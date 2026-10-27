module

public import CFSG.RankThree.PartTwo.Sec14.Ronan148BD4KF
public import CFSG.RankThree.PartTwo.Sec14.Ronan148BD4ThreeA
public import CFSG.RankThree.PartTwo.Sec14.Ronan148BD4Short
public import CFSG.RankThree.PartTwo.Sec11.KS11Lie6ProofBCent
import CFSG.RankThree.PartTwo.Sec14.Ronan148BD4Sig
import CFSG.RankThree.PartTwo.Sec4.Item417Res7ProofD4Odd
import CFSG.RankThree.PartTwo.Sec4.RonanK429RowHCore

public section

set_option linter.unusedSectionVars false

namespace CFSG.RankThree.PartTwo.Sec14.Ronan148B

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.LocalRank CFSG.GH74.GLS
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Chevalley
  CFSG.LocalAnalysis.ComponentInitial CFSG.RankThree.PartOne.KGD
  CFSG.RankThree.PartTwo.Sec11.KS11Lie5Proof CFSG.RankThree.PartTwo.Sec11.KS11Lie6Proof
open scoped commutatorElement

namespace Res148BD4

section Certs


variable {n : ℕ} {K : Type} [Field K] [Finite K] {σ : K ≃+* K}

theorem eq_bot_of_threeB (hn : 2 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 3)
    (hσ : ∀ c, σ c = c ^ 2 ^ n)
    {β : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)} (hβ3 : β ^ 3 = 1)
    (hβin : β ∉ (MulAut.conj : graphFixedRootGroup TwistTag.D4 K σ.toRingHom →*
      MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)).range)
    {z : graphFixedRootGroup TwistTag.D4 K σ.toRingHom}
    (hzS : z ∈ Subgroup.centralizer ((Sec11.KS11Lie4Proof.d4ShortSL2 K σ.toRingHom :
      Subgroup (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) :
        Set (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)))
    (hz3 : z ^ 3 = 1) (hz1 : z ≠ 1) (hβz : β z = z)
    {a : graphFixedRootGroup TwistTag.D4 K σ.toRingHom} (haz : a * z = z * a)
    {O : Subgroup (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)}
    (hOβ : ∀ x ∈ O, β x = x)
    (hOz : O ≤ Subgroup.centralizer ({z} : Set (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)))
    (hOn : ∀ y, β y = y → y * z = z * y → ∀ x ∈ O, y * x * y⁻¹ ∈ O)
    (hO3 : Nat.Coprime 3 (Nat.card O))
    {V : Subgroup (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)}
    (hVO : V ≤ O) (hV : V = ⁅V, Subgroup.zpowers a⁆) : V = ⊥ := by
  classical
  have hn1 : 1 ≤ n := by omega
  have hσ3 : σ ^ 3 = 1 := by
    ext c
    rw [ringEquiv_pow_three_apply]
    exact ringEquiv_cube_apply_eq hK hσ c
  have h3q : ¬ 3 ∣ 2 ^ n := by
    intro h
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).1
      (Nat.prime_three.dvd_of_dvd_pow h)
    omega
  set S := Sec11.KS11Lie4Proof.d4ShortSL2 K σ.toRingHom with hS
  set C := Subgroup.centralizer ({z} : Set (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) with hC
  obtain ⟨hD, -⟩ := d4ThreeBCent_holds K (2 ^ n) σ hK hσ h3q z hzS hz3 hz1
  have hCC : ⁅C, C⁆ ≤ S := by
    rw [Subgroup.commutator_le]
    intro x hx y hy
    rw [commutatorElement_def]
    exact hD x hx y hy
  have hK4 : 4 ≤ Nat.card K := by
    rw [hK]
    calc 4 ≤ 2 ^ 2 := le_rfl
      _ ≤ (2 ^ n) ^ 3 := by
        calc 2 ^ 2 ≤ 2 ^ (n * 3) := Nat.pow_le_pow_right (by norm_num) (by omega)
          _ = (2 ^ n) ^ 3 := by rw [pow_mul]
  have hSS : ⁅S, S⁆ = S := by
    obtain ⟨eS⟩ := nonempty_sl2_equiv_short hσ3
    have hP0 : Group.IsPerfect (Matrix.SpecialLinearGroup (Fin 2) K) :=
      CFSG.ClassicalInvolution.sl2_isPerfect hK4
    have hP : Group.IsPerfect S :=
      Group.IsPerfect.ofSurjective (f := eS.toMonoidHom) eS.surjective
    rw [Group.isPerfect_def] at hP
    rw [← Subgroup.map_subtype_commutator, hP, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  have hSC : S ≤ C := fun s hs => Subgroup.mem_centralizer_singleton_iff.2
    ((Subgroup.mem_centralizer_iff.1 hzS) s hs)
  have hCCS : ⁅C, C⁆ = S := le_antisymm hCC (hSS ▸ Subgroup.commutator_mono hSC hSC)
  have hβC : C.map β.toMonoidHom ≤ C := by
    rintro _ ⟨x, hx, rfl⟩
    have hx' : x * z = z * x := Subgroup.mem_centralizer_singleton_iff.1 hx
    refine Subgroup.mem_centralizer_singleton_iff.2 ?_
    rw [MulEquiv.coe_toMonoidHom, ← hβz, ← map_mul, ← map_mul, hx']
  have hβS : ∀ x ∈ S, β x ∈ S := by
    intro x hx
    rw [← hCCS] at hx ⊢
    have h1 : β x ∈ (⁅C, C⁆).map β.toMonoidHom := ⟨x, hx, rfl⟩
    rw [Subgroup.map_commutator] at h1
    exact Subgroup.commutator_mono hβC hβC h1
  have haC : a ∈ C := Subgroup.mem_centralizer_singleton_iff.2 haz
  have hVS : V ≤ S := by
    rw [hV, ← hCCS]
    exact Subgroup.commutator_mono (hVO.trans hOz) (Subgroup.zpowers_le.2 haC)
  have hbot := eq_bot_of_le_short_fixed hn hK hσ hβ3 hβin hβS (N := O ⊓ S) inf_le_right
    (fun x hx => hOβ x hx.1)
    (fun y hy hβy x hx => ⟨hOn y hβy (Subgroup.mem_centralizer_singleton_iff.1 (hSC hy)) x hx.1,
      S.mul_mem (S.mul_mem hy hx.2) (S.inv_mem hy)⟩)
    (Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le inf_le_left) hO3)
  exact eq_bot_iff.2 ((le_inf hVO hVS).trans hbot.le)

omit [Finite K] in
theorem map_conj_centralizer {G : Type*} [Group G] (c b : G) :
    (Subgroup.centralizer ({b} : Set G)).map (MulAut.conj c).toMonoidHom =
      Subgroup.centralizer ({c * b * c⁻¹} : Set G) := by
  ext y
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨w, hw, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff] at hw ⊢
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    calc c * w * c⁻¹ * (c * b * c⁻¹) = c * (w * b) * c⁻¹ := by group
      _ = c * (b * w) * c⁻¹ := by rw [hw]
      _ = c * b * c⁻¹ * (c * w * c⁻¹) := by group
  · intro hy
    refine ⟨c⁻¹ * y * c, ?_, ?_⟩
    · rw [Subgroup.mem_centralizer_singleton_iff] at hy ⊢
      calc c⁻¹ * y * c * b = c⁻¹ * (y * (c * b * c⁻¹)) * c := by group
        _ = c⁻¹ * (c * b * c⁻¹ * y) * c := by rw [hy]
        _ = b * (c⁻¹ * y * c) := by group
    · simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group

theorem mem_commutator_of_autFix (hn : 2 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 3)
    (hσ : ∀ c, σ c = c ^ 2 ^ n)
    {β : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)} (hβ3 : β ^ 3 = 1)
    (hβin : β ∉ (MulAut.conj : graphFixedRootGroup TwistTag.D4 K σ.toRingHom →*
      MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)).range)
    {b : graphFixedRootGroup TwistTag.D4 K σ.toRingHom} (hb3 : b ^ 3 = 1) (hb1 : b ≠ 1)
    (hβb : β b = b) {a : graphFixedRootGroup TwistTag.D4 K σ.toRingHom} (hab : a * b = b * a)
    {O : Subgroup (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)}
    (hOβ : ∀ x ∈ O, β x = x)
    (hOb : O ≤ Subgroup.centralizer ({b} : Set (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)))
    (hOn : ∀ y, β y = y → y * b = b * y → ∀ x ∈ O, y * x * y⁻¹ ∈ O)
    (hO3 : Nat.Coprime 3 (Nat.card O))
    {V : Subgroup (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)}
    (hVO : V ≤ O) (hV : V = ⁅V, Subgroup.zpowers a⁆) (hV1 : V ≠ ⊥) :
    b ∈ ⁅V, Subgroup.centralizer ({b} : Set (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))⁆ := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hn1 : 1 ≤ n := by omega
  have : CharP K 2 := by
    have : Fintype K := Fintype.ofFinite K
    exact charP_of_card_eq_prime_pow (f := n * 3)
      (by rw [← Nat.card_eq_fintype_card, hK, ← pow_mul])
  have : CharP (AlgebraicClosure K) 2 :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective 2
  have hq2 : 2 < 2 ^ n := by
    calc 2 < 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have hV3 : Nat.Coprime 3 (Nat.card V) :=
    Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le hVO) hO3
  have hb3' : (b : ModGL TwistTag.D4.tag K) ^ 3 = 1 := by
    rw [← Subgroup.coe_pow, hb3, Subgroup.coe_one]
  have hb1' : (b : ModGL TwistTag.D4.tag K) ≠ 1 := fun h => hb1 (Subtype.ext h)
  obtain ⟨ζ, x₀, hζ, hx₀, hcase⟩ := exists_conj_dA_or_dB (ℓ := 2) (f := n) hn1 (by norm_num) hK
    hσ (AlgebraicClosure K) (iterateFrobenius (AlgebraicClosure K) 2 n)
    (fun c => iterateFrobenius_def 2 n c) b.2 hb3' hb1'
  rcases hcase with hA | hB
  ·
    exact mem_commutator_of_conj_dA (ℓ := 2) (f := n) hn1 (by norm_num) hK hσ hq2 hζ hx₀ hA hab
      (hVO.trans hOb) hV hV3 hV1
  ·
    exfalso
    obtain ⟨k, hk, hkeq⟩ := exists_conj_d4T0 (algebraMap K (AlgebraicClosure K)) σ hζ
    obtain ⟨c, hc⟩ := exists_conj_of_triEmb_conj hn1 hK hσ (isPointIrreducible_gB hζ)
      (z := b) (s := ⟨d4T0 σ, d4T0_mem σ⟩) hx₀ hk hB hkeq
    set t₀ : graphFixedRootGroup TwistTag.D4 K σ.toRingHom := ⟨d4T0 σ, d4T0_mem σ⟩ with ht₀
    set θ := MulAut.conj c with hθ
    have hθb : θ b = t₀ := by rw [hθ, MulAut.conj_apply, hc]
    set β' := θ * β * θ⁻¹ with hβ'
    have hβ'app : ∀ y, β' y = θ (β (θ⁻¹ y)) := fun y => rfl
    have hβ'3 : β' ^ 3 = 1 := by
      rw [hβ', show θ * β * θ⁻¹ = θ * β * θ⁻¹ from rfl, conj_pow, hβ3, mul_one, mul_inv_cancel]
    have hβ'in : β' ∉ (MulAut.conj : graphFixedRootGroup TwistTag.D4 K σ.toRingHom →*
        MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)).range := by
      rintro ⟨d, hd⟩
      apply hβin
      refine ⟨c⁻¹ * d * c, ?_⟩
      have h1 : β = θ⁻¹ * β' * θ := by rw [hβ']; group
      rw [h1, ← hd, hθ, map_mul, map_mul, map_inv]
    have hβ't : β' t₀ = t₀ := by
      rw [hβ'app, ← hθb, MulAut.inv_apply, MulEquiv.symm_apply_apply, hβb]
    have hθinj : Function.Injective θ := θ.injective
    have ht₀3 : t₀ ^ 3 = 1 := by rw [← hθb, ← map_pow, hb3, map_one]
    have ht₀1 : t₀ ≠ 1 := by
      rw [← hθb]
      intro h
      exact hb1 (hθinj (h.trans (map_one θ).symm))
    have hVθ : V.map θ.toMonoidHom = ⁅V.map θ.toMonoidHom, Subgroup.zpowers (θ a)⁆ := by
      have hz : Subgroup.zpowers (θ a) = (Subgroup.zpowers a).map θ.toMonoidHom := by
        rw [MonoidHom.map_zpowers]
        rfl
      rw [hz, ← Subgroup.map_commutator, ← hV]
    have hbot := eq_bot_of_threeB hn hK hσ hβ'3 hβ'in (z := t₀) (d4T0_mem_centralizer σ) ht₀3
      ht₀1 hβ't (a := θ a) (by rw [← hθb, ← map_mul, ← map_mul, hab])
      (O := O.map θ.toMonoidHom)
      (by
        rintro _ ⟨x, hx, rfl⟩
        rw [MulEquiv.coe_toMonoidHom, hβ'app, MulAut.inv_apply, MulEquiv.symm_apply_apply,
          hOβ x hx])
      (by
        rw [← hθb, hθ, MulAut.conj_apply, ← map_conj_centralizer]
        exact Subgroup.map_mono hOb)
      (by
        intro y hy hyt x hx
        obtain ⟨x', hx', rfl⟩ := hx
        refine ⟨θ⁻¹ y * x' * (θ⁻¹ y)⁻¹, hOn (θ⁻¹ y) ?_ ?_ x' hx', ?_⟩
        · have h1 := congrArg (fun w => θ.symm w) hy
          simp only [hβ'app, MulAut.inv_apply, MulEquiv.symm_apply_apply] at h1
          rw [MulAut.inv_apply]
          exact h1
        · apply hθinj
          rw [map_mul, map_mul, MulAut.inv_apply, MulEquiv.apply_symm_apply, hθb]
          exact hyt
        · rw [MulEquiv.coe_toMonoidHom, map_mul, map_mul, map_inv, MulAut.inv_apply,
            MulEquiv.apply_symm_apply])
      (by rw [Subgroup.card_map_of_injective hθinj]; exact hO3)
      (V := V.map θ.toMonoidHom) (Subgroup.map_mono hVO) hVθ
    apply hV1
    rwa [Subgroup.map_eq_bot_iff_of_injective _ hθinj] at hbot

end Certs

end Res148BD4

open Res148BD4 in
theorem kF148D4Comm_holds :
    KF148D4Comm := by
  intro Γ _ _ S n hn hm ε hε3 hεout hK₀ b a hbS haS hab hb3 ha3 V hVO haV hVa hV1
  classical
  have hn2 : 2 ≤ n := by
    by_contra hlt
    have hn1 : n = 1 := by omega
    subst hn1
    obtain ⟨K₀, -, hperf, -, hiso⟩ := hK₀
    rcases hiso with ⟨h, -⟩ | ⟨-, ⟨e⟩⟩
    · norm_num at h
    · have : Group.IsPerfect K₀ := hperf
      have : Finite K₀ := inferInstance
      have hsub := Sec4.RonanK429H.subsingleton_of_mulEquiv_projSU_three_two e
      have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      have hc := KFacts.KS14.card_projSU_three_mul_gcd 2 1 le_rfl
      rw [← Nat.card_congr e.toEquiv, Nat.card_unique] at hc
      norm_num at hc
  obtain ⟨K, _, _, _, σ, hK, hσ, -, -, -, ⟨φ⟩⟩ :=
    Sec4.Res417Seven.exists_graphFixedRootGroup_of_trialityD4 hm
  set C₀ := graphFixedRootGroup TwistTag.D4 K σ.toRingHom with hC₀
  set f : C₀ →* Γ := S.subtype.comp φ.symm.toMonoidHom with hf
  have hfinj : Function.Injective f := fun x y h => φ.symm.injective (Subtype.ext h)
  have hfS : ∀ y, f y ∈ S := fun y => (φ.symm y).2
  have hfsurj : ∀ s ∈ S, ∃ y, f y = s := fun s hs => ⟨φ ⟨s, hs⟩, by simp [hf]⟩
  obtain ⟨hεN, hεnot⟩ := hεout
  have hεS : ∀ s ∈ S, ε * s * ε⁻¹ ∈ S := fun s hs => (Subgroup.mem_normalizer_iff.1 hεN s).1 hs
  set β : MulAut C₀ := MulAut.congr φ (S.normalizerMonoidHom ⟨ε, hεN⟩) with hβdef
  have hβf : ∀ y, f (β y) = ε * f y * ε⁻¹ := by
    intro y
    change ((φ.symm (φ (S.normalizerMonoidHom ⟨ε, hεN⟩ (φ.symm y))) : S) : Γ) = _
    rw [MulEquiv.symm_apply_apply, Subgroup.normalizerMonoidHom_apply_apply_coe]
    rfl
  have hβ3 : β ^ 3 = 1 := by
    refine MulEquiv.ext fun y => hfinj ?_
    rw [MulAut.one_apply, pow_three', MulAut.mul_apply, MulAut.mul_apply, hβf, hβf, hβf]
    calc ε * (ε * (ε * f y * ε⁻¹) * ε⁻¹) * ε⁻¹ = ε ^ 3 * f y * (ε ^ 3)⁻¹ := by
          simp only [pow_three, mul_inv_rev, mul_assoc]
      _ = f y := by rw [hε3]; group
  have hβin : β ∉ (MulAut.conj : C₀ →* MulAut C₀).range := by
    rintro ⟨d, hd⟩
    apply not_innerOn148_of_inducesOuterTheta ⟨hεN, hεnot⟩
    refine ⟨f d, hfS d, fun s hs => ?_⟩
    obtain ⟨y, rfl⟩ := hfsurj s hs
    rw [← hβf, ← hd, MulAut.conj_apply, map_mul, map_mul, map_inv]
  set b' := φ ⟨b, hbS.1⟩ with hb'
  set a' := φ ⟨a, haS.1⟩ with ha'
  have hfb : f b' = b := by simp [hf, hb']
  have hfa : f a' = a := by simp [hf, ha']
  have hεb : ε * b * ε⁻¹ = b := by
    have := Subgroup.mem_centralizer_singleton_iff.1 hbS.2
    rw [← this]; group
  have hεa : ε * a * ε⁻¹ = a := by
    have := Subgroup.mem_centralizer_singleton_iff.1 haS.2
    rw [← this]; group
  have hβb : β b' = b' := hfinj (by rw [hβf, hfb, hεb])
  have hab' : a' * b' = b' * a' := hfinj (by rw [map_mul, map_mul, hfa, hfb, hab])
  have hb'3 : b' ^ 3 = 1 := hfinj (by rw [map_pow, hfb, map_one, ← hb3, pow_orderOf_eq_one])
  have hb'1 : b' ≠ 1 := by
    intro h
    have h1 : b = 1 := by rw [← hfb, h, map_one]
    rw [h1, orderOf_one] at hb3
    omega
  set P := S ⊓ Subgroup.centralizer ({ε} : Set Γ) ⊓ Subgroup.centralizer ({b} : Set Γ) with hP
  set O := (pPrimeCoreOf 3 P).comap f with hO
  have hOP : pPrimeCoreOf 3 P ≤ P := pPrimeCoreOf_le 3 P
  have hOS : pPrimeCoreOf 3 P ≤ S := hOP.trans (inf_le_left.trans inf_le_left)
  have hmapO : O.map f = pPrimeCoreOf 3 P := by
    rw [hO, Subgroup.map_comap_eq, inf_eq_right]
    intro s hs
    obtain ⟨y, rfl⟩ := hfsurj s (hOS hs)
    exact ⟨y, rfl⟩
  have hOβ : ∀ x ∈ O, β x = x := by
    intro x hx
    apply hfinj
    rw [hβf]
    have hxε := (hOP hx).1.2
    have := Subgroup.mem_centralizer_singleton_iff.1 hxε
    rw [← this]; group
  have hOb : O ≤ Subgroup.centralizer ({b'} : Set C₀) := by
    intro x hx
    rw [Subgroup.mem_centralizer_singleton_iff]
    apply hfinj
    rw [map_mul, map_mul, hfb]
    exact Subgroup.mem_centralizer_singleton_iff.1 (hOP hx).2
  have hOn : ∀ y, β y = y → y * b' = b' * y → ∀ x ∈ O, y * x * y⁻¹ ∈ O := by
    intro y hy hyb x hx
    have hyP : f y ∈ P := by
      refine ⟨⟨hfS y, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩,
        Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
      · have h := congrArg f hy
        rw [hβf] at h
        calc f y * ε = ε * f y * ε⁻¹ * ε := by rw [h]
          _ = ε * f y := by group
      · rw [← hfb, ← map_mul, ← map_mul, hyb]
    change f (y * x * y⁻¹) ∈ pPrimeCoreOf 3 P
    rw [map_mul, map_mul, map_inv]
    exact (Subgroup.mem_normalizer_iff.1 (le_normalizer_pPrimeCoreOf 3 P hyP) (f x)).1 hx
  have hO3 : Nat.Coprime 3 (Nat.card O) := by
    rw [← Subgroup.card_map_of_injective hfinj, hmapO]
    exact coprime_card_pPrimeCoreOf 3 P
  have hVS : V ≤ S := hVO.trans hOS
  set V' := V.comap f with hV'
  have hmapV : V'.map f = V := by
    rw [hV', Subgroup.map_comap_eq, inf_eq_right]
    intro s hs
    obtain ⟨y, rfl⟩ := hfsurj s (hVS hs)
    exact ⟨y, rfl⟩
  have hV'O : V' ≤ O := fun x hx => hVO hx
  have hV'eq : V' = ⁅V', Subgroup.zpowers a'⁆ := by
    apply Subgroup.map_injective hfinj
    rw [Subgroup.map_commutator, hmapV, MonoidHom.map_zpowers, hfa]
    exact hVa
  have hV'1 : V' ≠ ⊥ := by
    intro h
    apply hV1
    rw [← hmapV, h, Subgroup.map_bot]
  have hmem := mem_commutator_of_autFix hn2 hK hσ hβ3 hβin hb'3 hb'1 hβb hab' hOβ hOb
    hOn hO3 hV'O hV'eq hV'1
  have h1 : f b' ∈ (⁅V', Subgroup.centralizer ({b'} : Set C₀)⁆).map f := ⟨b', hmem, rfl⟩
  rw [Subgroup.map_commutator, hmapV, hfb] at h1
  refine Subgroup.commutator_mono le_rfl ?_ h1
  rintro _ ⟨y, hy, rfl⟩
  refine ⟨hfS y, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
  rw [← hfb, ← map_mul, ← map_mul, Subgroup.mem_centralizer_singleton_iff.1 hy]

end CFSG.RankThree.PartTwo.Sec14.Ronan148B
