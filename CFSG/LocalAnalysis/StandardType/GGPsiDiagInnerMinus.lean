module

public import CFSG.LocalAnalysis.StandardType.GGPsiDiagInnerMinusTorus
public import CFSG.LocalAnalysis.StandardType.GGPsiDiagInnerAssembly
public import CFSG.LocalAnalysis.StandardType.GGInnerDiagBridgeInner
public import CFSG.LocalAnalysis.SectionRank.EvenCover.SLTwo
public import CFSG.LieType.Universal.SpinOmega.Center
public import CFSG.RankThree.PartOne.CTP.SU4EvenBridge
public import CFSG.LargeExtraspecial.S4CEOmegaSpin
public import CFSG.Timmesfeld.Transvection.ModelSUFour
public import CFSG.CharacterTheory.Semidihedral.ElementStructure
public import CFSG.ClassicalInvolution.WeakCT.Main
public import CFSG.ClassicalInvolution.WeakCT.SpinMinus
public import CFSG.LargeExtraspecial.O62Model
public import CFSG.LargeExtraspecial.OrthoF2
public import CFSG.LargeExtraspecial.S2Basic
public import CFSG.LargeExtraspecial.S4SevenInput
public import CFSG.LocalAnalysis.SectionRank.ClassicalOdd
public import CFSG.LocalAnalysis.SectionRank.EvenCover.LinearStep
public import CFSG.LocalAnalysis.SectionRank.SporadicCover
public import CFSG.Sporadic.M23.M23Group
public import CFSG.Sporadic.Th.F2Spec

public section

namespace CFSG.StandardType

open CliffordAlgebra QuadraticMap CFSG.LieType.Universal CFSG.LieType.Universal.Spin
  CFSG.LieType.Universal.Spin.Twisted CFSG.LieType.RootSystem CFSG.LieType.Steinberg
  CFSG.LieType.CurtisTits CFSG.ClassicalGroups.Orthogonal

namespace PsiDiag

namespace SpinM

variable {n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2] {b c : K}
  (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)

include hirr in
theorem center_eq_bot (hn : 4 ≤ n) : Subgroup.center (spinGroup (quadMinus n K b c)) = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨-, hker, hZ⟩ := spinToStatedProj_quadMinus hn hirr
  rw [← hZ, hker, Subgroup.mem_comap, mem_statedScalars_iff, toLinEquiv_spinMatrix] at hx
  obtain ⟨r, hr⟩ := mem_scalars.mp hx
  obtain ⟨v, hv⟩ := exists_map_ne_zero_of_hypPair _ (minusPair K b c (⟨0, by omega⟩ : Fin (n - 1)))
  have h1 : r = 1 := by
    have h := map_spinAction (quadMinus n K b c) x v
    rw [hr, QuadraticMap.map_smul, smul_eq_mul] at h
    have h2 : r * r = 1 := by
      have h' : (r * r - 1) * quadMinus n K b c v = 0 := by rw [sub_mul, h, one_mul, sub_self]
      exact sub_eq_zero.mp ((mul_eq_zero.mp h').resolve_right hv)
    have h3 : (r - 1) ^ 2 = 0 := by
      linear_combination h2 + (1 - r) * CharTwo.two_eq_zero (R := K)
    exact sub_eq_zero.mp ((pow_eq_zero_iff two_ne_zero).mp h3)
  have hx1 : x ∈ (spinMatrix (quadMinus n K b c)).ker := by
    rw [ker_spinMatrix, MonoidHom.mem_ker]
    refine LinearEquiv.ext fun w => ?_
    rw [hr, h1, one_smul]
    rfl
  rw [ker_spinMatrix_quadMinus_eq_bot hirr CharTwo.two_eq_zero] at hx1
  exact hx1

omit [Finite K] [CharP K 2] in
theorem fieldCoord_injective : Function.Injective (fieldCoord (b := b) (c := c)) := by
  intro s s' h
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  simp only [fieldCoord, Matrix.cons_val_zero, Matrix.cons_val_one] at h0 h1
  exact QuadraticAlgebra.ext h0 h1

omit [Finite K] [CharP K 2] in
theorem starCoord_injective : Function.Injective (starCoord (b := b) (c := c)) := by
  intro s s' h
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  simp only [starCoord, Matrix.cons_val_zero, Matrix.cons_val_one] at h0 h1
  refine QuadraticAlgebra.ext ?_ h1
  rw [h1] at h0
  linear_combination -h0

private theorem exists_mem_centralizer_of_center_eq_bot
    (hZ : Subgroup.center (spinGroup (quadMinus n K b c)) = ⊥)
    (hct : IsCTGroupDatum (coxeterMatrix (minusDatum n hirr).isFiniteType).toCoxeterSystem
      (weylAction (minusDatum n hirr).isFiniteType) (minusDatum n hirr).roots
      (minusDatum n hirr).rootGroup (minusWeyl n hirr) (minusTorus n hirr))
    (hn : 2 ≤ n) {G : Type*} [Group G]
    (ψ : spinGroup (quadMinus n K b c) →* G)
    (hker : ψ.ker ≤ Subgroup.center (spinGroup (quadMinus n K b c))) {c₀ : G}
    (hc : GGPsiInnerDiag (minusDatum n hirr) ψ c₀) :
    ∃ g ∈ ψ.range, c₀ * g ∈ Subgroup.centralizer (ψ.range : Set G) := by
  haveI := fact_shortField hirr
  haveI : Finite (spinGroup (quadMinus n K b c)) :=
    Finite.of_injective _ ((MonoidHom.ker_eq_bot_iff _).mp
      (ker_spinMatrix_quadMinus_eq_bot (n := n) hirr CharTwo.two_eq_zero))
  have hψ : Function.Injective ψ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff, ← hZ]
    exact hker
  have hext := minusDatum_steinbergExtras n hirr
  obtain ⟨g, hg, hγ⟩ := hc
  obtain ⟨d, hd⟩ : ∃ d, d = c₀ * g := ⟨_, rfl⟩
  rw [← hd] at hγ
  obtain ⟨k, hkv⟩ : ∃ k : Fin (n - 1), k.val = n - 2 := ⟨⟨n - 2, by omega⟩, rfl⟩
  have hk : ¬ k.val + 1 < n - 1 := by omega
  have hlong : ∀ (i : Fin (n - 1)) (hi : i.val + 1 < n - 1), ∃ χ : Kˣ, ∀ a : K,
      d⁻¹ * ψ ((minusFrame n b c).longRoot (succ_ne_of_lt n hi) true false (.ofAdd a)) * d =
        ψ ((minusFrame n b c).longRoot (succ_ne_of_lt n hi) true false
          (.ofAdd ((χ : K) * a))) := by
    intro i hi
    have hX : (minusDatum n hirr).rootGroup (Pi.single i 1) =
        ((minusFrame n b c).longRoot (succ_ne_of_lt n hi) true false).range :=
      minusRootGroup_single_of_lt n hirr hi
    obtain ⟨h, hh, hz⟩ := hγ _ (single_mem_roots (D := minusDatum n hirr) i)
    obtain ⟨t, ht, htz⟩ := exists_torus_conj_of_mem_ggTorus hct hext i
      (fun y hy z hz => mul_comm_of_mem_range _ (hX ▸ hy) (hX ▸ hz)) hh
    obtain ⟨χ, hχ⟩ := torus_le_scalarAct_long hirr hi ht
    refine ⟨χ, fun a => ?_⟩
    have hmem : (minusFrame n b c).longRoot (succ_ne_of_lt n hi) true false (.ofAdd a) ∈
        (minusDatum n hirr).rootGroup (Pi.single i 1) := hX ▸ ⟨_, rfl⟩
    rw [hz _ hmem, htz _ hmem, hχ]
  have hshort : ∃ ν : (ShortField b c)ˣ, ∀ s : ShortField b c,
      d⁻¹ * ψ (shortX n hirr k s) * d = ψ (shortX n hirr k ((ν : ShortField b c) * s)) := by
    have hX : (minusDatum n hirr).rootGroup (Pi.single k 1) = (shortPosHom n hirr k).range :=
      minusRootGroup_single_of_not_lt n hirr hk
    obtain ⟨h, hh, hz⟩ := hγ _ (single_mem_roots (D := minusDatum n hirr) k)
    obtain ⟨t, ht, htz⟩ := exists_torus_conj_of_mem_ggTorus hct hext k
      (fun y hy z hz => mul_comm_of_mem_range _ (hX ▸ hy) (hX ▸ hz)) hh
    obtain ⟨ν, hν⟩ := torus_le_scalarAct_short hirr hk ht
    refine ⟨ν, fun s => ?_⟩
    have hmem : shortX n hirr k s ∈ (minusDatum n hirr).rootGroup (Pi.single k 1) :=
      hX ▸ ⟨_, rfl⟩
    rw [hz _ hmem, htz _ hmem, hν]
  choose χl hχl using hlong
  obtain ⟨ν, hν⟩ := hshort
  obtain ⟨t, ht, htl, hts⟩ := exists_torus_conj hirr hk
    (fun i => if hi : i.val + 1 < n - 1 then χl i hi else 1) ν
  obtain ⟨d', hd'⟩ : ∃ d', d' = d * ψ t := ⟨_, rfl⟩
  have hconj : ∀ z, d'⁻¹ * ψ z * d' = (ψ t)⁻¹ * (d⁻¹ * ψ z * d) * ψ t := fun z => by
    rw [hd']
    group
  have hfixL : ∀ (i : Fin (n - 1)) (hi : i.val + 1 < n - 1) (a : K),
      d'⁻¹ * ψ ((minusFrame n b c).longRoot (succ_ne_of_lt n hi) true false (.ofAdd a)) * d' =
        ψ ((minusFrame n b c).longRoot (succ_ne_of_lt n hi) true false (.ofAdd a)) := by
    intro i hi a
    have h1 := htl i hi a
    rw [dite_eq_left hi] at h1
    rw [hconj, hχl i hi a, ← h1, ← map_inv, ← map_mul, ← map_mul]
    congr 1
    group
  have hfixS : ∀ s, d'⁻¹ * ψ (shortX n hirr k s) * d' = ψ (shortX n hirr k s) := by
    intro s
    rw [hconj, hν s, ← hts s, ← map_inv, ← map_mul, ← map_mul]
    congr 1
    group
  have hpos : ∀ i : Fin (n - 1), ∀ z ∈ (minusDatum n hirr).rootGroup (Pi.single i 1),
      d'⁻¹ * ψ z * d' = ψ z := by
    intro i z hz
    by_cases hi : i.val + 1 < n - 1
    · have hX : (minusDatum n hirr).rootGroup (Pi.single i 1) =
          ((minusFrame n b c).longRoot (succ_ne_of_lt n hi) true false).range :=
        minusRootGroup_single_of_lt n hirr hi
      rw [hX] at hz
      obtain ⟨a, rfl⟩ := hz
      rw [← ofAdd_toAdd a]
      exact hfixL i hi _
    · have hik : i = k := Fin.ext (by have := i.isLt; omega)
      subst hik
      have hX : (minusDatum n hirr).rootGroup (Pi.single i 1) = (shortPosHom n hirr i).range :=
        minusRootGroup_single_of_not_lt n hirr hk
      rw [hX] at hz
      obtain ⟨p, rfl⟩ := hz
      obtain ⟨s, hs⟩ := exists_fieldCoord_eq (b := b) (c := c) (Multiplicative.toAdd p)
      have he : shortPosHom n hirr i p = shortX n hirr i s := by
        show _ = shortPosHom n hirr i (.ofAdd (fieldCoord s))
        rw [hs, ofAdd_toAdd]
      rw [he]
      exact hfixS s
  have hnorm : ∀ i : Fin (n - 1), ∀ z ∈ (minusDatum n hirr).rootGroup (-Pi.single i 1),
      ∃ z' ∈ (minusDatum n hirr).rootGroup (-Pi.single i 1), d'⁻¹ * ψ z * d' = ψ z' := by
    intro i
    obtain ⟨h, hh, hz⟩ := hγ _ (neg_single_mem_roots (D := minusDatum n hirr) i)
    have hN : h ∈ Subgroup.normalizer
        ((minusDatum n hirr).rootGroup (-Pi.single i 1) : Set (spinGroup (quadMinus n K b c))) := by
      simp only [ggTorus, Subgroup.mem_iInf] at hh
      exact hh _ (neg_single_mem_roots (D := minusDatum n hirr) i)
    have htN := iSup_le_normalizer_rootGroup hct (neg_single_mem_roots (D := minusDatum n hirr) i) ht
    intro z hzm
    refine ⟨t⁻¹ * (h * z * h⁻¹) * t, ?_, ?_⟩
    · have h1 := (Subgroup.mem_normalizer_iff.mp hN z).mp hzm
      have h2 := (Subgroup.mem_normalizer_iff.mp (inv_mem htN) _).mp h1
      rwa [inv_inv] at h2
    · rw [hconj, hz z hzm]
      simp only [map_mul, map_inv]
  have hneg : ∀ i : Fin (n - 1), ∀ z ∈ (minusDatum n hirr).rootGroup (-Pi.single i 1),
      d'⁻¹ * ψ z * d' = ψ z := by
    intro i
    by_cases hi : i.val + 1 < n - 1
    · have hXn : (minusDatum n hirr).rootGroup (-Pi.single i 1) =
          ((minusFrame n b c).longRoot (succ_ne_of_lt n hi).symm true false).range :=
        minusRootGroup_neg_single_of_lt n hirr hi
      let R := rankOneRelsMap (CFSG.SectionRank.EvenCover.sl2Rels K)
        (ψ.comp ((minusFrame n b c).longSL2 (succ_ne_of_lt n hi) true false))
      have hRx : ∀ a, R.x a =
          ψ ((minusFrame n b c).longRoot (succ_ne_of_lt n hi) true false (.ofAdd a)) :=
        fun a => congrArg ψ ((minusFrame n b c).longSL2_upperSL2 (succ_ne_of_lt n hi) true false a)
      have hRy : ∀ a, R.y a =
          ψ ((minusFrame n b c).longRoot (succ_ne_of_lt n hi).symm true false (.ofAdd a)) :=
        fun a => congrArg ψ ((minusFrame n b c).longSL2_lowerSL2 (succ_ne_of_lt n hi) true false a)
      have hyinj : Function.Injective R.y := fun a a' h => by
        rw [hRy, hRy] at h
        have h1 := (minusFrame n b c).longRoot_injective (succ_ne_of_lt n hi).symm true false (hψ h)
        simpa using congrArg Multiplicative.toAdd h1
      have hE7 : ∀ s, (∀ b', ∃ b'', R.x s * R.y b' * (R.x s)⁻¹ = R.y b'') → s = 0 := by
        intro s hs
        have hconjY : ∀ z ∈ (minusDatum n hirr).rootGroup (-Pi.single i 1),
            (minusFrame n b c).longRoot (succ_ne_of_lt n hi) true false (.ofAdd s) * z *
              ((minusFrame n b c).longRoot (succ_ne_of_lt n hi) true false (.ofAdd s))⁻¹ ∈
              (minusDatum n hirr).rootGroup (-Pi.single i 1) := by
          intro z hz
          rw [hXn] at hz ⊢
          obtain ⟨p, rfl⟩ := hz
          obtain ⟨b'', hb''⟩ := hs (Multiplicative.toAdd p)
          rw [hRx, hRy, hRy, ofAdd_toAdd, ← map_inv, ← map_mul, ← map_mul] at hb''
          exact ⟨_, (hψ hb'').symm⟩
        have h1 := minusDatum_eq_one_of_mem_normalizer n hirr i _
          (by rw [minusRootGroup_single_of_lt n hirr hi]; exact ⟨_, rfl⟩)
          (Subgroup.mem_normalizer_fintype hconjY)
        have h2 := (minusFrame n b c).longRoot_injective (succ_ne_of_lt n hi) true false
          (h1.trans (map_one _).symm)
        simpa using congrArg Multiplicative.toAdd h2
      have hu : ∀ a, d'⁻¹ * R.x a * d' = R.x a := fun a => by rw [hRx]; exact hfixL i hi a
      have hl : ∀ a, ∃ a', d'⁻¹ * R.y a * d' = R.y a' := by
        intro a
        have hmem : (minusFrame n b c).longRoot (succ_ne_of_lt n hi).symm true false (.ofAdd a) ∈
            (minusDatum n hirr).rootGroup (-Pi.single i 1) := by rw [hXn]; exact ⟨_, rfl⟩
        obtain ⟨z', hz', he⟩ := hnorm i _ hmem
        rw [hXn] at hz'
        obtain ⟨p, rfl⟩ := hz'
        exact ⟨Multiplicative.toAdd p, by rw [hRy, hRy, he, ofAdd_toAdd]⟩
      choose φ hφ using hl
      have hid := eq_of_conj_rankOneRels R hyinj hE7 hu hφ
      intro z hz
      rw [hXn] at hz
      obtain ⟨p, rfl⟩ := hz
      have h1 := hφ (Multiplicative.toAdd p)
      rw [hid, hRy, ofAdd_toAdd] at h1
      exact h1
    · have hik : i = k := Fin.ext (by have := i.isLt; omega)
      subst hik
      have hXn : (minusDatum n hirr).rootGroup (-Pi.single i 1) = (shortNegHom n hirr i).range :=
        minusRootGroup_neg_single_of_not_lt n hirr hk
      let R := rankOneRelsMap (shortRels n hirr i) ψ
      have hRx : ∀ s, R.x s = ψ (shortX n hirr i s) := fun s => rfl
      have hRy : ∀ s, R.y s = ψ (shortNegHom n hirr i (.ofAdd (starCoord s))) := fun s => rfl
      have hyinj : Function.Injective R.y := fun s s' h => by
        rw [hRy, hRy] at h
        have h1 := shortNegHom_injective n hirr i (hψ h)
        exact starCoord_injective (by simpa using congrArg Multiplicative.toAdd h1)
      have hE7 : ∀ s, (∀ b', ∃ b'', R.x s * R.y b' * (R.x s)⁻¹ = R.y b'') → s = 0 := by
        intro s hs
        have hconjY : ∀ z ∈ (minusDatum n hirr).rootGroup (-Pi.single i 1),
            shortX n hirr i s * z * (shortX n hirr i s)⁻¹ ∈
              (minusDatum n hirr).rootGroup (-Pi.single i 1) := by
          intro z hz
          rw [hXn] at hz ⊢
          obtain ⟨p, rfl⟩ := hz
          obtain ⟨s', hs'⟩ := exists_starCoord_eq (b := b) (c := c) (Multiplicative.toAdd p)
          obtain ⟨b'', hb''⟩ := hs s'
          rw [hRx, hRy, hRy, hs', ofAdd_toAdd, ← map_inv, ← map_mul, ← map_mul] at hb''
          exact ⟨_, (hψ hb'').symm⟩
        have h1 := minusDatum_eq_one_of_mem_normalizer n hirr i _
          (by rw [minusRootGroup_single_of_not_lt n hirr hk]; exact ⟨_, rfl⟩)
          (Subgroup.mem_normalizer_fintype hconjY)
        have h2 := shortPosHom_injective n hirr i (h1.trans (map_one _).symm)
        have h3 : fieldCoord s = fieldCoord (0 : ShortField b c) := by
          have h4 := congrArg Multiplicative.toAdd h2
          rw [toAdd_ofAdd, toAdd_one] at h4
          rw [h4]
          ext j
          fin_cases j <;> rfl
        exact fieldCoord_injective h3
      have hu : ∀ s, d'⁻¹ * R.x s * d' = R.x s := fun s => by rw [hRx]; exact hfixS s
      have hl : ∀ s, ∃ s', d'⁻¹ * R.y s * d' = R.y s' := by
        intro s
        have hmem : shortNegHom n hirr i (.ofAdd (starCoord s)) ∈
            (minusDatum n hirr).rootGroup (-Pi.single i 1) := by rw [hXn]; exact ⟨_, rfl⟩
        obtain ⟨z', hz', he⟩ := hnorm i _ hmem
        rw [hXn] at hz'
        obtain ⟨p, rfl⟩ := hz'
        obtain ⟨s', hs'⟩ := exists_starCoord_eq (b := b) (c := c) (Multiplicative.toAdd p)
        exact ⟨s', by rw [hRy, hRy, he, hs', ofAdd_toAdd]⟩
      choose φ hφ using hl
      have hid := eq_of_conj_rankOneRels R hyinj hE7 hu hφ
      intro z hz
      rw [hXn] at hz
      obtain ⟨p, rfl⟩ := hz
      obtain ⟨s, hs⟩ := exists_starCoord_eq (b := b) (c := c) (Multiplicative.toAdd p)
      have h1 := hφ s
      rw [hid, hRy, hs, ofAdd_toAdd] at h1
      exact h1
  have hcent := mem_centralizer_of_fix_simple hct rfl ψ hpos hneg
  exact ⟨g * ψ t, mul_mem hg ⟨t, rfl⟩, by rwa [← mul_assoc, ← hd, ← hd']⟩

theorem exists_mem_centralizer (hn : 4 ≤ n) {G : Type*} [Group G]
    (ψ : spinGroup (quadMinus n K b c) →* G)
    (hker : ψ.ker ≤ Subgroup.center (spinGroup (quadMinus n K b c))) {c₀ : G}
    (hc : GGPsiInnerDiag (minusDatum n hirr) ψ c₀) :
    ∃ g ∈ ψ.range, c₀ * g ∈ Subgroup.centralizer (ψ.range : Set G) :=
  exists_mem_centralizer_of_center_eq_bot (hirr := hirr)
    (center_eq_bot hirr hn) (minusDatum_isCTGroupDatum n hirr hn) (by omega) ψ hker hc

include hirr in
theorem center_eq_bot_three :
    Subgroup.center (spinGroup (quadMinus 3 K b c)) = ⊥ := by
  haveI := fact_shortField hirr
  haveI : Finite (ShortField b c) := finite_shortField (b := b) (c := c)
  haveI : CharP (ShortField b c) 2 :=
    charP_of_injective_algebraMap (algebraMap K (ShortField b c)).injective 2
  letI : Algebra (ZMod 2) K := ZMod.algebra K 2
  let f := Module.finrank (ZMod 2) K
  have hcardK : Nat.card K = 2 ^ f := (FiniteField.pow_finrank_eq_natCard 2 K).symm
  have hcardL : Nat.card (ShortField b c) = (2 ^ f) ^ 2 := by
    simpa [ShortField, Nat.card_prod, hcardK, pow_two] using
      Nat.card_congr (QuadraticAlgebra.equivProd (-c) b)
  obtain ⟨-, e, -⟩ := CFSG.RankThree.PartOne.CTP.SU4Even.exists_equiv_su_four_even
    (F := K) (K := ShortField b c) (f := f) hcardK hcardL hirr
  have hZSU : Subgroup.center (CFSG.LieType.Universal.Unitary.SU
      (CFSG.LieType.BorelTits.unitaryInvolution (ShortField b c) 2 f) 4) = ⊥ :=
    CFSG.Timmesfeld.Transvection.ModelRank.center_SU_four_eq_bot
      (F := ShortField b c)
      (σ := CFSG.LieType.BorelTits.unitaryInvolution (ShortField b c) 2 f)
      (CFSG.LieType.BorelTits.unitaryInvolution_involutive hcardL)
  refine (Subgroup.map_eq_bot_iff_of_injective
    (H := Subgroup.center (spinGroup (quadMinus 3 K b c)))
    (f := e.toMonoidHom) e.injective).mp ?_
  rw [CFSG.LieType.Universal.Unitary.map_center_mulEquiv e, hZSU]

theorem exists_mem_centralizer_three
    {G : Type*} [Group G]
    (ψ : spinGroup (quadMinus 3 K b c) →* G)
    (hker : ψ.ker ≤ Subgroup.center (spinGroup (quadMinus 3 K b c))) {c₀ : G}
    (hc : GGPsiInnerDiag (minusDatum 3 hirr) ψ c₀) :
    ∃ g ∈ ψ.range, c₀ * g ∈ Subgroup.centralizer (ψ.range : Set G) := by
  have hZ : Subgroup.center (spinGroup (quadMinus 3 K b c)) = ⊥ :=
    center_eq_bot_three (hirr := hirr)
  have hct := CFSG.LargeExtraspecial.S4.minusDatum_isCTGroupDatum_three_charTwo
    (F := K) hirr
  exact exists_mem_centralizer_of_center_eq_bot (hirr := hirr) hZ hct (by omega) ψ hker hc

end SpinM

end PsiDiag

section Genuine

theorem ggPsiDiagInner_POmegaMinus :
    ∀ (G : Type) [Group G] [Finite G] (n f : ℕ) (ψ : (ggU .POmegaMinus n f).K →* G)
      (G₀ : Subgroup G), GGPresentsG0 G₀ (ggU .POmegaMinus n f).D .POmegaMinus n f ψ →
        ∀ c ∈ Subgroup.normalizer (G₀ : Set G), GGPsiInnerDiag (ggU .POmegaMinus n f).D ψ c →
          ∃ g ∈ G₀, c * g ∈ Subgroup.centralizer (G₀ : Set G) := by
  intro G _ _ n f ψ G₀ hpres c _ hc
  obtain ⟨⟨hadm, -⟩, ⟨hrange, hker⟩, -, -⟩ := hpres
  subst hrange
  obtain ⟨-, -, hn⟩ := hadm
  exact PsiDiag.SpinM.exists_mem_centralizer (K := GaloisField 2 f) (minusCoeffs_irr 2 f) hn ψ
    hker hc

theorem ggPsiDiagInnerAt_POmegaMinus : GGPsiDiagInnerAt .POmegaMinus :=
  ggPsiDiagInner_POmegaMinus

end Genuine

section Inner

theorem ggPsiDiagInnerAt_of_ggInnerTag : ∀ t, GGInnerTag t → GGPsiDiagInnerAt t :=
  fun t ht => ggPsiDiagInner_of_POmegaMinus ggPsiDiagInner_POmegaMinus t ht

end Inner

end CFSG.StandardType
