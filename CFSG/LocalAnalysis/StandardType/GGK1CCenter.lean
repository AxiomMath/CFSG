module

public import CFSG.LocalAnalysis.StandardType.GGK1CDefs
public import CFSG.LocalAnalysis.StandardType.GGK1CLift
public import CFSG.RankThree.PartOne.KC.UnitaryPrimaryCentralizer
public import CFSG.RankThree.PartOne.KC.UnitaryGoodSpecial
public import CFSG.RankThree.Classical2.UnitarySplitPrimeRank
public import CFSG.LocalAnalysis.StandardType.GGTableBSymplecticLift
public import CFSG.LocalAnalysis.StandardType.GGSixAutKFinerChoiceTwoFrame

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Open Polynomial
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag (proj)
open CFSG.RankThree.Classical (spEnd spLin spSupported spForm reciprocalOrbits
  IsReciprocalTransversal SpPrimaryBlocks SpPairedBlock SpSelfDualBlock)
open CFSG.RankThree.PartOne.KCPrimary
open CFSG.RankThree.PartOne.KCUnitary
open CFSG.RankThree.PartOne.KCOrthogonal
open CFSG.StandardType.TableBSymp

private theorem ggK1CCe_charP_two {K : Type} [Field K] [Finite K] {nf : ℕ}
    (hnf : 1 ≤ nf) (hK : Nat.card K = 2 ^ nf) : CharP K 2 := by
  haveI := Fintype.ofFinite K
  exact charP_of_card_eq_prime_pow (p := 2) (f := nf) (by rw [Fintype.card_eq_nat_card, hK])

private theorem ggK1CCe_proj_injective {K : Type} [Field K] [Finite K] (r : ℕ)
    [NeZero r] [Fact (Nat.Prime 2)] (hchar : CharP K 2) :
    Function.Injective (proj r K) := by
  haveI : CharP K 2 := hchar
  exact (CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.proj_bijective_of_charTwo
    (r := r)).1

private theorem ggK1CCe_fixSub_conj {R : Type} [Group R] (a : R) :
    ggFixSub (MulAut.conj a) = Subgroup.centralizer ({a} : Set R) := by
  ext g
  rw [mem_ggFixSub, Subgroup.mem_centralizer_singleton_iff, MulAut.conj_apply]
  constructor
  · intro h
    calc g * a = (a * g * a⁻¹) * a := by rw [h]
      _ = a * g := by group
  · intro h
    calc a * g * a⁻¹ = (g * a) * a⁻¹ := by rw [h.symm]
      _ = g := by group

private noncomputable def ggK1CCe_scalarUnit (E M : Type) [Field E] [AddCommGroup M]
    [Module E M] (c : Eˣ) : (Module.End E M)ˣ where
  val := algebraMap E (Module.End E M) (c : E)
  inv := algebraMap E (Module.End E M) ((c⁻¹ : Eˣ) : E)
  val_inv := by
    rw [← (algebraMap E (Module.End E M)).map_mul, Units.mul_inv,
      (algebraMap E (Module.End E M)).map_one]
  inv_val := by
    rw [← (algebraMap E (Module.End E M)).map_mul, Units.inv_mul,
      (algebraMap E (Module.End E M)).map_one]

private theorem ggK1CCe_orderOf_scalarUnit {E M : Type} [Field E] [AddCommGroup M]
    [Module E M] [Nontrivial M] (c : Eˣ) :
    orderOf (ggK1CCe_scalarUnit E M c) = orderOf c := by
  have hinj : Function.Injective (algebraMap E (Module.End E M)) := by
    intro x y h
    obtain ⟨m, hm⟩ := exists_ne (0 : M)
    have h1 : x • m = y • m := by
      have := congrArg (fun f : Module.End E M => f m) h
      simpa [Algebra.algebraMap_eq_smul_one'] using this
    have h2 : (x - y) • m = 0 := by
      rw [sub_smul, sub_eq_zero]
      exact h1
    have hxy : x - y = 0 := (smul_eq_zero.mp h2).resolve_right hm
    exact sub_eq_zero.mp hxy
  let f : Eˣ →* (Module.End E M)ˣ := Units.map (algebraMap E (Module.End E M)).toMonoidHom
  have hf : Function.Injective f := by
    intro a b hab
    exact Units.ext (hinj (congrArg Units.val hab))
  have hfc : ggK1CCe_scalarUnit E M c = f c := by
    ext; rfl
  rw [hfc]
  exact orderOf_injective f hf c

private theorem ggK1CCe_scalarUnit_central {E M : Type} [Field E] [AddCommGroup M]
    [Module E M] (c : Eˣ) :
    ggK1CCe_scalarUnit E M c ∈
      Subgroup.center (LinearMap.GeneralLinearGroup E M) := by
  rw [Subgroup.mem_center_iff]
  intro g
  apply Units.ext
  ext v
  simp only [Units.val_mul, ggK1CCe_scalarUnit, Algebra.algebraMap_eq_smul_one',
    LinearMap.smul_apply, Module.End.mul_apply, Module.End.one_apply, map_smul]

private theorem ggK1CCe_scalarUnit_mem_unitary {E M : Type} [Field E] [AddCommGroup M]
    [Module E M] {σ : E →+* E} {B : M →ₛₗ[σ] M →ₗ[E] E}
    (c : Eˣ) (hc : σ (c : E) * (c : E) = 1) :
    (ggK1CCe_scalarUnit E M c : LinearMap.GeneralLinearGroup E M) ∈
      CFSG.LocalAnalysis.ComponentInitial.sesqUnitaryGroup B := by
  rw [CFSG.LocalAnalysis.ComponentInitial.mem_sesqUnitaryGroup]
  intro v w
  simp only [ggK1CCe_scalarUnit, Algebra.algebraMap_eq_smul_one', LinearMap.smul_apply,
    Module.End.one_apply]
  rw [map_smulₛₗ, map_smulₛₗ]
  simp only [RingHom.id_apply, smul_eq_mul]
  rw [show σ (c:E) = (c:E)⁻¹ from eq_inv_of_mul_eq_one_left hc]
  have hc0 : (c:E) ≠ 0 := Units.ne_zero c
  field_simp
  simp

private theorem ggK1CCe_paired_scalar {p nf r : ℕ} {K : Type} [Field K] [Finite K]
    {x : ↥(StatedSp r K)} {h : K[X]} (hp : p.Prime)
    (hsq : Squarefree (minpoly K (spEnd x)))
    (H : SpPrimaryBlocks 2 nf p x (proj r K x))
    (hh : h ∈ primaryFactors (spEnd x)) (hne : h ≠ reciprocalPolynomial h) :
    ∃ e ∈ spSupported x ({h, reciprocalPolynomial h} : Set K[X]),
      e ^ p = 1 ∧ orderOf e = p ∧
      ∀ g ∈ spSupported x ({h, reciprocalPolynomial h} : Set K[X]), Commute e g := by
  classical
  let i : primaryFactors (spEnd x) := ⟨h, hh⟩
  have hB : SpPairedBlock 2 nf p x i := H.paired i (by simpa using hne)
  obtain ⟨φ, -, -⟩ := hB.factor
  haveI : Fact (Irreducible (((⟨h, hh⟩ : primaryFactors (spEnd x)) : K[X]))) :=
      ⟨irreducible_of_mem_primaryFactors i.2⟩
  have hcard : Nat.card (AdjoinRoot (((⟨h, hh⟩ : primaryFactors (spEnd x)) : K[X]))) = (2 ^ nf) ^
      h.natDegree := hB.card_field
  haveI : Finite (AdjoinRoot (((⟨h, hh⟩ : primaryFactors (spEnd x)) : K[X]))) :=
      Nat.finite_of_card_ne_zero (by
    rw [hcard]
    exact (pow_pos (pow_pos (by norm_num) nf) h.natDegree).ne')
  haveI : Fintype (AdjoinRoot (((⟨h, hh⟩ : primaryFactors (spEnd x)) : K[X]))) := Fintype.ofFinite _
  haveI : Fintype (AdjoinRoot (((⟨h, hh⟩ : primaryFactors (spEnd x)) : K[X])))ˣ := Fintype.ofFinite
      _
  haveI : Nontrivial (primaryComponent (spEnd x) (((⟨h, hh⟩ : primaryFactors (spEnd x)) : K[X]))) :=
    Submodule.nontrivial_iff_ne_bot.mpr (primaryComponent_ne_bot hsq hh)
  have hdvd : p ∣ Nat.card (AdjoinRoot (((⟨h, hh⟩ : primaryFactors (spEnd x)) : K[X])))ˣ := by
    rw [Nat.card_units, hcard]
    exact hB.dvd
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨ζ, hζ⟩ := exists_prime_orderOf_dvd_card' (G := (AdjoinRoot (((⟨h, hh⟩ : primaryFactors
      (spEnd x)) : K[X])))ˣ) p hdvd
  let g : (Module.End (AdjoinRoot (((⟨h, hh⟩ : primaryFactors (spEnd x)) : K[X])))
      (primaryComponent (spEnd x) (((⟨h, hh⟩ : primaryFactors (spEnd x)) : K[X]))))ˣ :=
    ggK1CCe_scalarUnit (AdjoinRoot (((⟨h, hh⟩ : primaryFactors (spEnd x)) : K[X])))
        (primaryComponent (spEnd x) (((⟨h, hh⟩ : primaryFactors (spEnd x)) : K[X]))) ζ
  let e : ↥(StatedSp r K) := φ.symm g
  have hmem : e ∈ spSupported x ({h, reciprocalPolynomial h} : Set K[X]) := (φ.symm g).2
  have hord : orderOf e = p := by
    have h1 : orderOf g = p := by rw [ggK1CCe_orderOf_scalarUnit ζ, hζ]
    have h2 : orderOf (φ.symm g) = orderOf g :=
      orderOf_injective φ.symm.toMonoidHom φ.symm.injective g
    simpa [e] using h2.trans h1
  refine ⟨e, hmem, ?_, hord, ?_⟩
  · rw [← hord]; exact pow_orderOf_eq_one e
  · intro g' hg'
    change e * g' = g' * e
    have hsub : (⟨e, hmem⟩ : spSupported x ({h, reciprocalPolynomial h} : Set K[X])) *
        ⟨g', hg'⟩ = ⟨g', hg'⟩ * ⟨e, hmem⟩ := by
      apply φ.injective
      rw [map_mul, map_mul]
      have he : (⟨e, hmem⟩ : spSupported x ({h, reciprocalPolynomial h} : Set K[X])) =
          φ.symm g := rfl
      rw [he, φ.apply_symm_apply]
      have hc : g ∈ Subgroup.center (blockGL (spEnd x) (((⟨h, hh⟩ : primaryFactors (spEnd x)) :
          K[X]))) :=
        ggK1CCe_scalarUnit_central (E := AdjoinRoot (((⟨h, hh⟩ : primaryFactors (spEnd x)) : K[X])))
          (M := primaryComponent (spEnd x) (((⟨h, hh⟩ : primaryFactors (spEnd x)) : K[X]))) ζ
      exact (Subgroup.mem_center_iff.mp hc _).symm
    simpa [Subgroup.coe_mul] using congrArg Subtype.val hsub

private theorem ggK1CCe_selfDual_scalar {p nf r : ℕ} {K : Type} [Field K] [Finite K]
    {x : ↥(StatedSp r K)} {h : K[X]} (hp : p.Prime) (hpq : p ∣ 2 ^ nf + 1)
    (hsq : Squarefree (minpoly K (spEnd x)))
    (H : SpPrimaryBlocks 2 nf p x (proj r K x))
    (hh : h ∈ primaryFactors (spEnd x)) (hne : h ≠ X - 1)
    (hself : reciprocalPolynomial h = h) :
    ∃ e ∈ spSupported x ({h} : Set K[X]),
      e ^ p = 1 ∧ orderOf e = p ∧
      ∀ g ∈ spSupported x ({h} : Set K[X]), Commute e g := by
  classical
  let i : primaryFactors (spEnd x) := ⟨h, hh⟩
  have hB : SpSelfDualBlock 2 nf p x i := H.selfDual i (by simpa using hne) (by simpa using hself)
  haveI : Fact (Irreducible (((⟨h, hh⟩ : primaryFactors (spEnd x)) : K[X]))) :=
      ⟨irreducible_of_mem_primaryFactors i.2⟩
  haveI : Nontrivial (primaryComponent (spEnd x) (((⟨h, hh⟩ : primaryFactors (spEnd x)) : K[X]))) :=
    Submodule.nontrivial_iff_ne_bot.mpr (primaryComponent_ne_bot hsq hh)
  obtain ⟨d, hd, hpqd, σ, hσ, hσne, hσ2, hσroot, hσadj, hE, hbar, Hf, hHf, hHfsep,
    ⟨η, hη0, hηneg, hηtr⟩, ⟨eB, heB⟩, φ, hφ⟩ := hB.exists_half
  have hpq' : p ∣ 2 ^ (nf * d) + 1 := by
    simpa [pow_mul] using hpqd
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨ζ, hζord, hζnorm⟩ :=
    CFSG.RankThree.Classical2.exists_orderOf_eq_norm_one hE hp hpq'
  have hbarζ : hE.bar (ζ : AdjoinRoot (((⟨h, hh⟩ : primaryFactors (spEnd x)) : K[X]))) = (ζ :
      AdjoinRoot (((⟨h, hh⟩ : primaryFactors (spEnd x)) : K[X]))) ^ (2 ^ (nf * d)) := by
    rw [hbar, hσ, ← pow_mul]
  have hζnorm' : (ζ : AdjoinRoot (((⟨h, hh⟩ : primaryFactors (spEnd x)) : K[X]))) ^ (2 ^ (nf * d) +
      1) = 1 := by
    simpa using congrArg (fun u : (AdjoinRoot (((⟨h, hh⟩ : primaryFactors (spEnd x)) : K[X])))ˣ =>
        (u : AdjoinRoot (((⟨h, hh⟩ : primaryFactors (spEnd x)) : K[X])))) hζnorm
  have hnormζ : hE.bar (ζ : AdjoinRoot (((⟨h, hh⟩ : primaryFactors (spEnd x)) : K[X]))) * (ζ :
      AdjoinRoot (((⟨h, hh⟩ : primaryFactors (spEnd x)) : K[X]))) = 1 := by
    rw [hbarζ]
    simpa only [pow_succ] using hζnorm'
  let g : (Module.End (AdjoinRoot (((⟨h, hh⟩ : primaryFactors (spEnd x)) : K[X])))
      (primaryComponent (spEnd x) (((⟨h, hh⟩ : primaryFactors (spEnd x)) : K[X]))))ˣ :=
    ggK1CCe_scalarUnit (AdjoinRoot (((⟨h, hh⟩ : primaryFactors (spEnd x)) : K[X])))
        (primaryComponent (spEnd x) (((⟨h, hh⟩ : primaryFactors (spEnd x)) : K[X]))) ζ
  have hgunit : (g : LinearMap.GeneralLinearGroup (AdjoinRoot (((⟨h, hh⟩ : primaryFactors (spEnd
      x)) : K[X])))
      (primaryComponent (spEnd x) (((⟨h, hh⟩ : primaryFactors (spEnd x)) : K[X])))) ∈
      CFSG.LocalAnalysis.ComponentInitial.sesqUnitaryGroup Hf :=
    ggK1CCe_scalarUnit_mem_unitary ζ hnormζ
  let e : ↥(StatedSp r K) := φ.symm ⟨g, hgunit⟩
  have hmem : e ∈ spSupported x ({h} : Set K[X]) := (φ.symm ⟨g, hgunit⟩).2
  have hord : orderOf e = p := by
    have h1 : orderOf g = p := by rw [ggK1CCe_orderOf_scalarUnit ζ, hζord]
    have h2 : orderOf (φ.symm ⟨g, hgunit⟩) =
        orderOf (⟨g, hgunit⟩ : CFSG.LocalAnalysis.ComponentInitial.sesqUnitaryGroup Hf) :=
      orderOf_injective φ.symm.toMonoidHom φ.symm.injective
        (⟨g, hgunit⟩ : CFSG.LocalAnalysis.ComponentInitial.sesqUnitaryGroup Hf)
    have h3 : orderOf (⟨g, hgunit⟩ : CFSG.LocalAnalysis.ComponentInitial.sesqUnitaryGroup Hf) =
        orderOf g :=
      (orderOf_injective
        (Subgroup.subtype (CFSG.LocalAnalysis.ComponentInitial.sesqUnitaryGroup Hf))
        (Subgroup.subtype_injective _)
        (⟨g, hgunit⟩ : CFSG.LocalAnalysis.ComponentInitial.sesqUnitaryGroup Hf)).symm
    simpa [e] using h2.trans (h3.trans h1)
  refine ⟨e, hmem, ?_, hord, ?_⟩
  · rw [← hord]; exact pow_orderOf_eq_one e
  · intro g' hg'
    have hsub : (⟨e, hmem⟩ : spSupported x ({h} : Set K[X])) * ⟨g', hg'⟩ =
        ⟨g', hg'⟩ * ⟨e, hmem⟩ := by
      apply φ.injective
      rw [map_mul, map_mul]
      have he : (⟨e, hmem⟩ : spSupported x ({h} : Set K[X])) = φ.symm ⟨g, hgunit⟩ := rfl
      rw [he, φ.apply_symm_apply]
      apply Subtype.ext
      have hc : g ∈ Subgroup.center (blockGL (spEnd x) (((⟨h, hh⟩ : primaryFactors (spEnd x)) :
          K[X]))) :=
        ggK1CCe_scalarUnit_central (E := AdjoinRoot (((⟨h, hh⟩ : primaryFactors (spEnd x)) : K[X])))
          (M := primaryComponent (spEnd x) (((⟨h, hh⟩ : primaryFactors (spEnd x)) : K[X]))) ζ
      exact (Subgroup.mem_center_iff.mp hc _).symm
    change e * g' = g' * e
    simpa [Subgroup.coe_mul] using congrArg Subtype.val hsub

private theorem ggK1CCe_block_elemAbelian {p nf r : ℕ} {K : Type} [Field K] [Finite K]
    {x : ↥(StatedSp r K)} (hp : p.Prime)
    (H : SpPrimaryBlocks 2 nf p x (proj r K x))
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (f : ι → reciprocalOrbits (spEnd x)) (hne : ∀ i j, i ≠ j → f i ≠ f j)
    (e : ι → ↥(StatedSp r K))
    (hmem : ∀ i, e i ∈ spSupported x (f i : Set K[X]))
    (hp_pow : ∀ i, e i ^ p = 1)
    (hord : ∀ i, orderOf (e i) = p)
    (hcent : ∀ i, ∀ g ∈ spSupported x (f i : Set K[X]), Commute (e i) g) :
    ∃ E0 : Subgroup ↥(StatedSp r K), IsElemAbelian p E0 ∧
      Nat.card E0 = p ^ Fintype.card ι ∧
      E0 ≤ Subgroup.centralizer ({x} : Set ↥(StatedSp r K)) ∧
      (∀ z ∈ E0, ∀ g ∈ Subgroup.centralizer ({x} : Set ↥(StatedSp r K)), g * z = z * g) := by
  classical
  haveI : NeZero p := ⟨hp.ne_zero⟩
  let φ : (i : ι) → Multiplicative (ZMod p) →* ↥(StatedSp r K) :=
    fun i => zmodPowHom (hp_pow i)
  have hφmem : ∀ (i : ι) (a : Multiplicative (ZMod p)),
      φ i a ∈ spSupported x (f i : Set K[X]) := by
    intro i a
    have h : φ i a ∈ Subgroup.zpowers (e i) := by
      refine Subgroup.mem_zpowers_iff.mpr ?_
      exact ⟨(a : Multiplicative (ZMod p)).toAdd.val, by
        rw [zmodPowHom_apply]; rfl⟩
    exact Subgroup.zpowers_le.mpr (hmem i) h
  have hcomm : Pairwise fun i j => ∀ a b, Commute (φ i a) (φ j b) := by
    intro i j hij a b
    have hfi : (f i : Set K[X]) ∈ reciprocalOrbits (spEnd x) := (f i).2
    have hfj : (f j : Set K[X]) ∈ reciprocalOrbits (spEnd x) := (f j).2
    have hneij : (f i : Set K[X]) ≠ (f j : Set K[X]) :=
      fun h => hne i j hij (Subtype.ext h)
    exact H.directProduct.1 (f i : Set K[X]) hfi (f j : Set K[X]) hfj hneij
      (φ i a) (hφmem i a) (φ j b) (hφmem j b)
  let F : ((i : ι) → Multiplicative (ZMod p)) →* ↥(StatedSp r K) :=
    MonoidHom.noncommPiCoprod φ hcomm
  have hf : Function.Injective f := by
    intro i j hij
    by_contra h
    exact hne i j h hij
  have hind : iSupIndep fun i => (φ i).range :=
    iSupIndep.mono (H.directProduct.2.1.comp hf) (fun i => by
      rintro _ ⟨a, rfl⟩
      exact hφmem i a)
  have hφinj : ∀ i, Function.Injective (φ i) := by
    intro i
    rw [injective_iff_map_eq_one]
    intro a ha
    exact (zmodPowHom_eq_one_iff (hp_pow i) (hord i)).mp ha
  have hinjF : Function.Injective F :=
    MonoidHom.injective_noncommPiCoprod_of_iSupIndep φ hind hφinj
  let E0 : Subgroup ↥(StatedSp r K) := F.range
  have hcard : Nat.card E0 = p ^ Fintype.card ι := by
    calc Nat.card E0
        = Nat.card ((i : ι) → Multiplicative (ZMod p)) :=
          Nat.card_congr (MonoidHom.ofInjective hinjF).toEquiv.symm
      _ = ∏ i : ι, Nat.card (Multiplicative (ZMod p)) := Nat.card_pi
      _ = ∏ _i : ι, p := by
          refine Finset.prod_congr rfl fun i _ => ?_
          simp [Nat.card_eq_fintype_card, ZMod.card]
      _ = p ^ Fintype.card ι := by simp
  have hE0cent : ∀ z ∈ E0, ∀ g ∈ Subgroup.centralizer ({x} : Set ↥(StatedSp r K)),
      g * z = z * g := by
    intro z hz g hg
    have hz' : z ∈ Subgroup.centralizer
        (Subgroup.centralizer ({x} : Set ↥(StatedSp r K)) : Set ↥(StatedSp r K)) := by
      have hzF : z ∈ F.range := hz
      rw [MonoidHom.noncommPiCoprod_range] at hzF
      have hle : (⨆ i, (φ i).range) ≤ Subgroup.centralizer
          (Subgroup.centralizer ({x} : Set ↥(StatedSp r K)) : Set ↥(StatedSp r K)) := by
        refine iSup_le fun i => ?_
        rintro _ ⟨a, rfl⟩
        rw [Subgroup.mem_centralizer_iff]
        intro g' hg'
        have hg'' : g' ∈ ⨆ O : reciprocalOrbits (spEnd x), spSupported x (O : Set K[X]) := by
          rw [H.directProduct.2.2]; exact hg'
        have hcent_all : (⨆ O : reciprocalOrbits (spEnd x), spSupported x (O : Set K[X])) ≤
            Subgroup.centralizer ({φ i a} : Set ↥(StatedSp r K)) := by
          refine iSup_le fun O => ?_
          intro g'' hg''
          rw [Subgroup.mem_centralizer_singleton_iff]
          by_cases hO : O = f i
          · subst hO
            change g'' * φ i a = φ i a * g''
            rw [zmodPowHom_apply]
            exact (hcent i g'' hg'').symm.pow_right ((a : Multiplicative (ZMod p)).toAdd.val)
          · have hneO : (O : Set K[X]) ≠ (f i : Set K[X]) :=
              fun h => hO (Subtype.ext h)
            have hO' : (O : Set K[X]) ∈ reciprocalOrbits (spEnd x) := O.2
            have hfi' : (f i : Set K[X]) ∈ reciprocalOrbits (spEnd x) := (f i).2
            exact (H.directProduct.1 (O : Set K[X]) hO' (f i : Set K[X]) hfi' hneO
              g'' hg'' (φ i a) (hφmem i a))
        exact Subgroup.mem_centralizer_singleton_iff.mp (hcent_all hg'')
      exact hle hzF
    exact (Subgroup.mem_centralizer_iff.mp hz') g hg
  refine ⟨E0, ⟨?_, ?_⟩, hcard, ?_, ?_⟩
  · have hcomm : ∀ a b : E0, a * b = b * a := by
      intro a b
      apply Subtype.ext
      obtain ⟨x, hx⟩ := a.2
      obtain ⟨y, hy⟩ := b.2
      rw [Subgroup.coe_mul, Subgroup.coe_mul, ← hx, ← hy]
      exact (map_mul F x y).symm.trans
        ((congrArg F (mul_comm x y)).trans (map_mul F y x))
    exact IsMulCommutative.of_comm hcomm
  · intro z hz
    have hzF : z ∈ F.range := hz
    obtain ⟨a, ha⟩ := hzF
    rw [← ha, ← map_pow]
    have hap : a ^ p = 1 := by
      ext i
      simpa [Fintype.card_multiplicative, ZMod.card] using pow_card_eq_one (x := a i)
    rw [hap, map_one]
  · intro z hz
    exact Subgroup.mem_centralizer_singleton_iff.mpr
      (hE0cent z hz x
        (Subgroup.mem_centralizer_singleton_iff.mpr (Commute.refl x))).symm
  · intro z hz g hg
    exact hE0cent z hz g hg

private theorem ggK1CCe_eq_zero_of_sum_eq_zero {l : List ℕ} (h : l.sum = 0) :
    ∀ a ∈ l, a = 0 := by
  induction l with
  | nil => intro a ha; simp at ha
  | cons b t ih =>
      intro a ha
      simp only [List.sum_cons] at h
      simp only [List.mem_cons] at ha
      rcases ha with rfl | ha
      · omega
      · exact ih (by omega) a ha

private theorem ggK1CCe_range_succ_cons (n : ℕ) :
    List.range (n + 1) = 0 :: (List.range n).map Nat.succ := by
  induction n with
  | zero => simp
  | succ n ih =>
      conv_lhs => rw [List.range_succ, ih]
      rw [List.cons_append]
      simp [List.range_succ, List.map_append]

private theorem ggK1CCe_filter_range_getD_length (l : List ℕ) :
    ((List.range l.length).filter (fun k => decide (0 < l.getD k 0))).length =
      (l.filter (fun a => decide (a ≠ 0))).length := by
  induction l with
  | nil => simp
  | cons a t ih =>
      rw [List.length_cons, ggK1CCe_range_succ_cons t.length, List.filter_cons]
      have hmap : ((List.range t.length).map Nat.succ).filter
            (fun k => decide (0 < (a :: t).getD k 0))
          = ((List.range t.length).filter (fun j => decide (0 < t.getD j 0))).map Nat.succ := by
        rw [List.filter_map]
        apply congrArg (List.map Nat.succ)
        apply List.filter_congr
        intro j _
        simp [Function.comp_apply, List.getD_cons_succ]
      by_cases hp : 0 < a
      · have ha' : a ≠ 0 := Nat.pos_iff_ne_zero.mp hp
        rw [if_pos (by simpa using hp), List.length_cons, hmap, List.length_map, ih,
          List.filter_cons, if_pos (by simp [ha']), List.length_cons]
      · have ha : a = 0 := by omega
        rw [if_neg (by simpa using hp), hmap, List.length_map, ih,
          List.filter_cons, if_neg (by simp [ha])]

private theorem ggK1CCe_rZ_eq_tail (p : ℕ) (m : List ℕ) (H : ℕ)
    (hlen : m.length = H + 1) :
    ((List.range (H + 1)).filter
        (fun j => decide (1 ≤ j ∧ 0 < m.getD j 0))).length =
      (m.tail.filter (fun j => decide (j ≠ 0))).length := by
  rw [← hlen]
  cases m with
  | nil => simp
  | cons a t =>
      rw [List.length_cons, List.tail_cons]
      have h1 : (List.range (t.length + 1)).filter
            (fun j => decide (1 ≤ j ∧ 0 < (a :: t).getD j 0))
          = ((List.range t.length).filter (fun k => decide (0 < t.getD k 0))).map Nat.succ := by
        rw [ggK1CCe_range_succ_cons t.length]
        rw [List.filter_cons]
        rw [if_neg (by simp)]
        rw [List.filter_map]
        congr 1
      rw [h1, List.length_map, ggK1CCe_filter_range_getD_length t]

private theorem ggK1CCe_reciprocal_eq_self {p nf r : ℕ} {K : Type} [Field K] [Finite K]
    {x : ↥(StatedSp r K)} {h : K[X]} (hsq : Squarefree (minpoly K (spEnd x)))
    (hp : p.Prime) (hK : Nat.card K = 2 ^ nf) (hpq : p ∣ 2 ^ nf + 1)
    (hh : h ∈ primaryFactors (spEnd x)) (hne : h ≠ X - 1)
    (hord : orderOf (AdjoinRoot.root h) = p) :
    reciprocalPolynomial h = h := by
  classical
  have hmon : h.Monic := monic_of_mem_primaryFactors hh
  have hirr : Irreducible h := irreducible_of_mem_primaryFactors hh
  haveI : Fact (Irreducible h) := ⟨hirr⟩
  have h0 : h.coeff 0 ≠ 0 := coeff_zero_ne_zero_of_mem_primaryFactors hsq hh
  let E := AdjoinRoot h
  let lam : E := AdjoinRoot.root h
  have hroot : aeval lam h = 0 := by
    rw [AdjoinRoot.aeval_eq, AdjoinRoot.mk_self]
  have hqroot : aeval (lam ^ Nat.card K) h = 0 := by
    have := Fintype.ofFinite K
    rw [Nat.card_eq_fintype_card, ← expand_aeval, FiniteField.Polynomial.expand_card, map_pow,
      hroot, zero_pow Fintype.card_ne_zero]
  have hpqK : p ∣ Nat.card K + 1 := by rwa [hK]
  have hpow : lam ^ (Nat.card K + 1) = 1 := by
    rw [← orderOf_dvd_iff_pow_eq_one, hord]
    exact hpqK
  have hmul : lam ^ Nat.card K * lam = 1 := by
    rw [← pow_succ, hpow]
  have hinv : lam ^ Nat.card K = lam⁻¹ := eq_inv_of_mul_eq_one_left hmul
  have hrootinv : aeval (lam⁻¹) h = 0 := by
    rw [← hinv]
    exact hqroot
  let u : Eˣ := Units.mk0 lam (root_ne_zero h0)
  have hrec : aeval lam (reciprocalPolynomial h) = 0 := by
    have hu := aeval_reciprocalPolynomial_of_unit u h
    rw [show (u : E) = lam from rfl,
      show ((u⁻¹ : Eˣ) : E) = lam⁻¹ by rw [Units.val_inv_eq_inv_val]; rfl,
      hrootinv, mul_zero, smul_zero] at hu
    exact hu
  have hrec_monic : (reciprocalPolynomial h).Monic := monic_reciprocalPolynomial h0
  have hrec_irr : Irreducible (reciprocalPolynomial h) := irreducible_reciprocalPolynomial hirr h0
  have hmin : minpoly K lam = h := by
    rw [AdjoinRoot.minpoly_root hmon.ne_zero, hmon.leadingCoeff, inv_one, Polynomial.C_1,
      mul_one]
  have hdvd : h ∣ reciprocalPolynomial h := by
    nth_rewrite 1 [← hmin]
    rw [minpoly.dvd_iff]
    exact hrec
  exact eq_of_monic_of_associated hrec_monic hmon (hirr.associated_of_dvd hrec_irr hdvd).symm

private theorem ggK1CCe_conj_eq_one_iff {G : Type} [Group G] (u : G) :
    MulAut.conj u = 1 ↔ u ∈ Subgroup.center G := by
  constructor
  · intro h
    rw [Subgroup.mem_center_iff]
    intro g
    have hg := congrArg (fun f : MulAut G => f g) h
    simp only [MulAut.conj_apply, MulAut.one_apply] at hg
    calc g * u = (u * g * u⁻¹) * u := by rw [hg]
      _ = u * g := by group
  · intro h
    ext g
    rw [MulAut.conj_apply, ← Subgroup.mem_center_iff.mp h g, mul_assoc, mul_inv_cancel, mul_one]
    rfl

private theorem ggK1CCe_lift_commute {r : ℕ} {K : Type} [Field K]
    (hprojinj : Function.Injective (proj r K))
    (hcenterR : Subgroup.center (StatedProj (StatedSp r K)) = ⊥)
    {y x : ↥(StatedSp r K)}
    (hc : Commute (MulAut.conj (proj r K y)) (MulAut.conj (proj r K x))) :
    Commute y x := by
  classical
  let a : StatedProj (StatedSp r K) := proj r K y
  let b : StatedProj (StatedSp r K) := proj r K x
  have hconj_mul : ∀ u v : StatedProj (StatedSp r K),
      MulAut.conj (u * v) = MulAut.conj u * MulAut.conj v := by
    intro u v; ext g; simp [MulAut.conj_apply, mul_assoc]
  have hconj_inv : ∀ u : StatedProj (StatedSp r K),
      MulAut.conj u⁻¹ = (MulAut.conj u)⁻¹ := by
    intro u; ext g; simp [MulAut.conj_apply]
  have heq : MulAut.conj (a * b) = MulAut.conj (b * a) := by
    rw [hconj_mul, hconj_mul, hc.eq]
  let u : StatedProj (StatedSp r K) := (a * b) * (b * a)⁻¹
  have hu1 : MulAut.conj u = 1 := by
    rw [show u = (a * b) * (b * a)⁻¹ from rfl, hconj_mul, hconj_inv, heq, mul_inv_cancel]
  have huZ : u ∈ Subgroup.center (StatedProj (StatedSp r K)) :=
    (ggK1CCe_conj_eq_one_iff u).mp hu1
  have hu : u = 1 := by
    rw [hcenterR] at huZ
    exact Subgroup.mem_bot.mp huZ
  have hab : a * b = b * a := mul_inv_eq_one.mp hu
  apply hprojinj
  rw [map_mul, map_mul]
  exact hab

private theorem ggK1CCe_finish {p nf d r : ℕ} {K : Type} [Field K] [Finite K]
    {x : ↥(StatedSp r K)} {m : List ℕ} (hchar : CharP K 2)
    (hnf : 1 ≤ nf) (hK : Nat.card K = 2 ^ nf)
    (hprojinj : Function.Injective (proj r K))
    (H : SpPrimaryBlocks 2 nf p x (proj r K x))
    (hm : GGK1CMultOf p nf d r K x m) (n : ℕ)
    (E0 : Subgroup ↥(StatedSp r K)) (hE0ab : IsElemAbelian p E0)
    (hE0card : Nat.card E0 = p ^ n)
    (hE0C : E0 ≤ Subgroup.centralizer ({x} : Set ↥(StatedSp r K)))
    (hE0cent : ∀ z ∈ E0, ∀ g ∈ Subgroup.centralizer ({x} : Set ↥(StatedSp r K)),
      g * z = z * g)
    (hrZ : (ggMultDatumC p nf d m).rZ = n) :
    GGK1Center p (ggMultDatumC p nf d m) (StatedProj (StatedSp r K))
      (LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSpGroup K r)) (LargeEvenGSpSet K r))
      (MulAut.conj (proj r K x)) := by
  classical
  intro h2
  haveI : CharP K 2 := hchar
  let E : Subgroup (StatedProj (StatedSp r K)) := E0.map (proj r K)
  have hcenterS : Subgroup.center (StatedSp r K) = ⊥ := by
    rw [CFSG.LieType.Universal.Symplectic.center_eq,
      CFSG.Open.StatedAPI.statedScalars_subgroupOf_statedSp_eq_bot]
  have hprojsurj : Function.Surjective (proj r K) :=
    CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.proj_surjective
  let e : ↥(StatedSp r K) ≃* StatedProj (StatedSp r K) :=
    MulEquiv.ofBijective (proj r K) ⟨hprojinj, hprojsurj⟩
  have hcenterR : Subgroup.center (StatedProj (StatedSp r K)) = ⊥ := by
    have h := Subgroup.map_center_eq e
    rw [hcenterS, Subgroup.map_bot] at h
    exact h.symm
  refine ⟨E, ?_, ?_, ?_, ?_, ?_⟩
  · haveI : IsMulCommutative ↥E0 := hE0ab.1
    refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, ?_⟩
    · obtain ⟨a0, ha0, ha⟩ := a.2
      obtain ⟨b0, hb0, hb⟩ := b.2
      change a.1 * b.1 = b.1 * a.1
      rw [← ha, ← hb, ← map_mul, ← map_mul]
      exact congrArg (proj r K) (congrArg Subtype.val
        (hE0ab.1.is_comm.comm (⟨a0, ha0⟩ : E0) ⟨b0, hb0⟩))
    · intro z hz
      obtain ⟨z0, hz0, hz⟩ := hz
      rw [← hz, ← map_pow]
      exact congrArg (proj r K) (hE0ab.2 z0 hz0)
  · rw [Subgroup.card_map_of_injective hprojinj, hE0card, hrZ]
  · intro z hz
    obtain ⟨z0, hz0, hz⟩ := hz
    rw [← hz, ggK1CCe_fixSub_conj, H.centralizer_eq]
    exact Subgroup.mem_map_of_mem (proj r K) (hE0C hz0)
  · intro z hz g hg
    obtain ⟨z0, hz0, hz⟩ := hz
    rw [ggK1CCe_fixSub_conj, H.centralizer_eq] at hg
    obtain ⟨g0, hg0, hg⟩ := hg
    rw [← hz, ← hg, ← map_mul, ← map_mul]
    exact congrArg (proj r K) (hE0cent z0 hz0 g0 hg0)
  · intro ψ hψ hψp hcomm z hz
    obtain ⟨y, hyp, hyconj⟩ := ggK1C_exists_lift (p := p) (nf := nf) (r := r) (K := K)
      hnf hK ψ hψ hψp
    rw [← hyconj] at hcomm
    have hyx : Commute y x := ggK1CCe_lift_commute hprojinj hcenterR hcomm
    obtain ⟨z0, hz0, hz⟩ := hz
    have hyC : y ∈ Subgroup.centralizer ({x} : Set ↥(StatedSp r K)) :=
      Subgroup.mem_centralizer_singleton_iff.mpr hyx
    have hyz : y * z0 = z0 * y := hE0cent z0 hz0 y hyC
    rw [← hyconj, ← hz]
    change proj r K (y * z0 * y⁻¹) = proj r K z0
    rw [hyz]
    group

theorem ggK1C_core_center {p nf d r : ℕ} {K : Type} [Field K] [Finite K]
    (hp : p.Prime) (hp2 : p ≠ 2) (hdvd : p ∣ 2 ^ nf - 1 ∨ p ∣ 2 ^ nf + 1)
    (hnf : 1 ≤ nf) (hK : Nat.card K = 2 ^ nf) (hd : d = ggMultOrd p nf)
    {x : ↥(StatedSp r K)} {m : List ℕ} (hm : GGK1CMultOf p nf d r K x m)
    (hx : x ^ p = 1) :
    GGK1Center p (ggMultDatumC p nf d m) (StatedProj (StatedSp r K))
      (LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSpGroup K r)) (LargeEvenGSpSet K r))
      (MulAut.conj (proj r K x)) := by
  classical
  intro h2
  have hchar : CharP K 2 := ggK1CCe_charP_two hnf hK
  haveI : CharP K 2 := hchar
  have hpK : (p : K) ≠ 0 := by
    intro h0
    have h2p : 2 ∣ p := (CharP.cast_eq_zero_iff K 2 p).mp h0
    exact hp2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp h2p).symm
  have hd2 : d = 2 → p ∣ 2 ^ nf + 1 := by
    intro h
    subst hd
    unfold ggMultOrd at h
    by_cases h1 : p ∣ 2 ^ nf - 1
    · rw [if_pos h1] at h; omega
    · rw [if_neg h1] at h
      by_cases h2 : p ∣ 2 ^ nf + 1
      · exact h2
      · rw [if_neg h2] at h; omega
  by_cases hx1 : x = 1
  · subst hx1
    have hdim : Module.finrank K
        (primaryComponent (spEnd (1 : ↥(StatedSp r K))) (X - 1)) = 2 * r := by
      change Module.finrank K
        (primaryComponent (spEnd (1 : ↥(StatedSp r K))) (X - C (1 : K))) = 2 * r
      rw [primaryComponent_X_sub_C_one, CFSG.StandardType.ChoiceTwo.spEnd_one, sub_self,
        LinearMap.ker_zero, finrank_top,
        Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin]
      omega
    have hhead : m.headD 0 = r := by rw [hm.head_eq, hdim]; omega
    cases m with
    | nil =>
        have hlen := hm.length_eq
        simp at hlen
    | cons a t =>
        have ha : a = r := by simpa using hhead
        have hsum : a + t.sum = r := by simpa using hm.sum_eq
        have htsum : t.sum = 0 := by omega
        have htail : t.filter (fun j => decide (j ≠ 0)) = [] := by
          apply List.filter_eq_nil_iff.mpr
          intro b hb
          have hb0 := ggK1CCe_eq_zero_of_sum_eq_zero htsum b hb
          simp [hb0]
        have hzero : ((a :: t).tail.filter (fun j => decide (j ≠ 0))).length = 0 := by
          rw [List.tail_cons]
          exact congrArg List.length htail
        rcases hm.blocks_eq with ⟨-, P, hP, hmult⟩ | ⟨-, hmult⟩
        · have hP0 : P.card = 0 := by
            have hcard := congrArg Multiset.card hmult
            rw [Multiset.coe_card, hzero, Multiset.card_map] at hcard
            exact hcard.symm
          have := ggK1CCe_rZ_eq_tail p (a :: t) ((p - 1) / 2) hm.length_eq
          rw [hzero] at this
          rw [show (ggMultDatumC p nf d (a :: t)).rZ =
              ((List.range ((p - 1) / 2 + 1)).filter
                (fun j => decide (1 ≤ j ∧ 0 < (a :: t).getD j 0))).length from rfl, this] at h2
          omega
        · have hS0 : (ggK1CSelfDualFactors (1 : ↥(StatedSp r K))).card = 0 := by
            have hcard := congrArg Multiset.card hmult
            rw [Multiset.coe_card, hzero, Multiset.card_map] at hcard
            exact hcard.symm
          have := ggK1CCe_rZ_eq_tail p (a :: t) ((p - 1) / 2) hm.length_eq
          rw [hzero] at this
          rw [show (ggMultDatumC p nf d (a :: t)).rZ =
              ((List.range ((p - 1) / 2 + 1)).filter
                (fun j => decide (1 ≤ j ∧ 0 < (a :: t).getD j 0))).length from rfl, this] at h2
          omega
  · haveI : Fact p.Prime := ⟨hp⟩
    have hxord : orderOf x = p := orderOf_eq_prime hx hx1
    have hr : 1 ≤ r := by
      by_contra h
      have hr0 : r = 0 := by omega
      subst hr0
      haveI : Subsingleton ↥(StatedSp 0 K) := inferInstance
      exact hx1 (Subsingleton.elim x 1)
    haveI : NeZero r := ⟨by omega⟩
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hprojinj : Function.Injective (proj r K) := ggK1CCe_proj_injective r hchar
    have haord : orderOf (proj r K x) = p := by
      rw [← hxord]
      exact orderOf_injective (proj r K) hprojinj x
    have hsq : Squarefree (minpoly K (spEnd x)) := (CFSG.RankThree.Classical.altPrimaryData_spLin
        hpK hx).squarefree
    have H : SpPrimaryBlocks 2 nf p x (proj r K x) :=
      (CFSG.RankThree.Classical.symplectic_cross_prime_primary_centralizer_blocks
        (ℓ := 2) (f := nf) (p := p)
        Nat.prime_two hnf hK hp hp2 hp2 hr (proj r K x) haord).2 x rfl hxord
    rcases hm.blocks_eq with ⟨hd1, P, hP, hmult⟩ | ⟨hd2b, hmult⟩
    · let ι := {h : K[X] // h ∈ P}
      haveI : Fintype ι := inferInstance
      haveI : DecidableEq ι := inferInstance
      let f : ι → reciprocalOrbits (spEnd x) := fun i =>
        ⟨({i.1, reciprocalPolynomial i.1} : Set K[X]), ⟨i.1, (hP.1 i.1 i.2).1, rfl⟩⟩
      have hne : ∀ i j, i ≠ j → f i ≠ f j := by
        intro i j hij
        intro hfij
        have hmem : i.1 ∈ ({j.1, reciprocalPolynomial j.1} : Set K[X]) := by
          have hset := congrArg (fun O : reciprocalOrbits (spEnd x) => (O : Set K[X])) hfij
          change i.1 ∈ (f j : Set K[X])
          rw [← hset]
          exact Or.inl rfl
        rcases hmem with h | h
        · exact hij (Subtype.ext h)
        · exfalso
          have hji := hP.2.2 j.1 j.2
          rw [← h] at hji
          exact hji i.2
      have hex : ∀ i : ι, ∃ e ∈ spSupported x (f i : Set K[X]),
          e ^ p = 1 ∧ orderOf e = p ∧
          ∀ g ∈ spSupported x (f i : Set K[X]), Commute e g := by
        intro i
        exact ggK1CCe_paired_scalar hp hsq H (hP.1 i.1 i.2).1 (hP.1 i.1 i.2).2
      let e : ι → ↥(StatedSp r K) := fun i => Classical.choose (hex i)
      have hmem : ∀ i, e i ∈ spSupported x (f i : Set K[X]) :=
        fun i => (Classical.choose_spec (hex i)).1
      have hp_pow : ∀ i, e i ^ p = 1 :=
        fun i => (Classical.choose_spec (hex i)).2.1
      have hord : ∀ i, orderOf (e i) = p :=
        fun i => (Classical.choose_spec (hex i)).2.2.1
      have hcent : ∀ i, ∀ g ∈ spSupported x (f i : Set K[X]), Commute (e i) g :=
        fun i => (Classical.choose_spec (hex i)).2.2.2
      obtain ⟨E0, hE0ab, hE0card, hE0C, hE0cent⟩ :=
        ggK1CCe_block_elemAbelian hp H f hne e hmem hp_pow hord hcent
      have hrZ : (ggMultDatumC p nf d m).rZ = Fintype.card ι := by
        have hlen := ggK1CCe_rZ_eq_tail p m ((p - 1) / 2) hm.length_eq
        have hcard_mult : (m.tail.filter (fun j => decide (j ≠ 0))).length = P.card := by
          have := congrArg Multiset.card hmult
          simpa using this
        rw [show (ggMultDatumC p nf d m).rZ =
            ((List.range ((p - 1) / 2 + 1)).filter
              (fun j => decide (1 ≤ j ∧ 0 < m.getD j 0))).length from rfl,
          hlen, hcard_mult]
        simpa [ι] using (Finset.card_attach (s := P))
      exact (ggK1CCe_finish hchar hnf hK hprojinj H hm (Fintype.card ι) E0 hE0ab hE0card
        hE0C hE0cent hrZ) h2
    · let ι := {h : K[X] // h ∈ ggK1CSelfDualFactors x}
      haveI : Fintype ι := inferInstance
      haveI : DecidableEq ι := inferInstance
      have hsd : ∀ i : ι, reciprocalPolynomial i.1 = i.1 := by
        intro i
        have hi := Finset.mem_filter.mp i.2
        exact ggK1CCe_reciprocal_eq_self hsq hp hK (hd2 hd2b) hi.1 hi.2
          (H.nontrivial i.1 hi.1 hi.2)
      let f : ι → reciprocalOrbits (spEnd x) := fun i =>
        ⟨({i.1} : Set K[X]), by
          exact ⟨i.1, (Finset.mem_filter.mp i.2).1, by simp [hsd i]⟩⟩
      have hne : ∀ i j, i ≠ j → f i ≠ f j := by
        intro i j hij hfij
        have hmem : i.1 ∈ ({j.1} : Set K[X]) := by
          have hset := congrArg (fun O : reciprocalOrbits (spEnd x) => (O : Set K[X])) hfij
          change i.1 ∈ (f j : Set K[X])
          rw [← hset]
          exact rfl
        exact hij (Subtype.ext (by simpa using hmem))
      have hex : ∀ i : ι, ∃ e ∈ spSupported x (f i : Set K[X]),
          e ^ p = 1 ∧ orderOf e = p ∧
          ∀ g ∈ spSupported x (f i : Set K[X]), Commute e g := by
        intro i
        have hi := Finset.mem_filter.mp i.2
        exact ggK1CCe_selfDual_scalar hp (hd2 hd2b) hsq H hi.1 hi.2 (hsd i)
      let e : ι → ↥(StatedSp r K) := fun i => Classical.choose (hex i)
      have hmem : ∀ i, e i ∈ spSupported x (f i : Set K[X]) :=
        fun i => (Classical.choose_spec (hex i)).1
      have hp_pow : ∀ i, e i ^ p = 1 :=
        fun i => (Classical.choose_spec (hex i)).2.1
      have hord : ∀ i, orderOf (e i) = p :=
        fun i => (Classical.choose_spec (hex i)).2.2.1
      have hcent : ∀ i, ∀ g ∈ spSupported x (f i : Set K[X]), Commute (e i) g :=
        fun i => (Classical.choose_spec (hex i)).2.2.2
      obtain ⟨E0, hE0ab, hE0card, hE0C, hE0cent⟩ :=
        ggK1CCe_block_elemAbelian hp H f hne e hmem hp_pow hord hcent
      have hrZ : (ggMultDatumC p nf d m).rZ = Fintype.card ι := by
        have hlen := ggK1CCe_rZ_eq_tail p m ((p - 1) / 2) hm.length_eq
        have hcard_mult : (m.tail.filter (fun j => decide (j ≠ 0))).length =
            (ggK1CSelfDualFactors x).card := by
          have := congrArg Multiset.card hmult
          simpa using this
        rw [show (ggMultDatumC p nf d m).rZ =
            ((List.range ((p - 1) / 2 + 1)).filter
              (fun j => decide (1 ≤ j ∧ 0 < m.getD j 0))).length from rfl,
          hlen, hcard_mult]
        simpa [ι] using (Finset.card_attach (s := ggK1CSelfDualFactors x))
      exact (ggK1CCe_finish hchar hnf hK hprojinj H hm (Fintype.card ι) E0 hE0ab hE0card
        hE0C hE0cent hrZ) h2

end CFSG.StandardType

end
