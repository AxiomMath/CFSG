module

public import CFSG.RankThree.PartTwo.Sec8.HeringU3nLift
public import CFSG.RankThree.PartTwo.Sec8.Item86ResProofOmega
public import CFSG.RankThree.PartTwo.Sec8.Standing
import CFSG.RankThree.PartTwo.Sec5.Tools
import CFSG.RankThree.PartTwo.Sec6.Item612Core
import CFSG.RankThree.PartTwo.KFacts.L34Sections
import CFSG.RankThree.PartTwo.KFacts.K71Borel
import CFSG.CGT.PushingUpLit.A78G0.Borel
import CFSG.LinearAlgebra.SL2MinimalFaithfulMatrix
import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels
import CFSG.RankThree.PartTwo.Sec8.Item87ProofTools

public section

namespace CFSG.RankThree.PartTwo.Sec8.HeringU3n

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec8.Item83Proof CFSG.RankThree.PartTwo.Sec8.Item86ResProof
open CFSG.Assembly.RankThreeEven (projSL)
open scoped MatrixGroups


theorem two_pow_three_mul_odd_mod {n : ℕ} (hn : Odd n) : 2 ^ (3 * n) ≡ 2 [MOD 3] := by
  obtain ⟨k, rfl⟩ := hn
  have : 2 ^ (3 * (2 * k + 1)) = 8 * 64 ^ k := by
    rw [show 3 * (2 * k + 1) = 3 + 6 * k by ring, pow_add, pow_mul]
    norm_num
  rw [this]
  have h64 : 64 ^ k ≡ 1 [MOD 3] := by
    have : (64 : ℕ) ≡ 1 [MOD 3] := by decide
    simpa using this.pow k
  calc 8 * 64 ^ k ≡ 8 * 1 [MOD 3] := Nat.ModEq.mul_left 8 h64
    _ ≡ 2 [MOD 3] := by decide

theorem exists_choice_of_sec8Std (h45 : Sec4.Item4_5) (hKB : KF83KBarTwo)
    {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L : Subgroup G} {a d : G} {n : ℕ}
    (h : Sec8Std G A c L a d n)
    (hK : Nonempty (imageModTheta L (inSubgroup perfectResidual
      (L ⊓ Subgroup.centralizer ({d} : Set G))) ≃* projSL 2 (GaloisField 2 (3 * n)))) :
    ∃ (S : Subgroup G) (s : G),
      S ≤ inSubgroup perfectResidual (L ⊓ Subgroup.centralizer ({d} : Set G)) ∧
      CFSG.Assembly.IsElemAbelian 2 S ∧ Nat.card S = 2 ^ (3 * n) ∧
      Subgroup.closure ({c, a, d} : Set G) ≤ Subgroup.normalizer (S : Set G) ∧
      s ∈ S ∧ s ≠ 1 ∧ Subgroup.closure ({c, a, d} : Set G) ≤ Subgroup.centralizer ({s} : Set G) ∧
      ∀ u ∈ S, u ≠ 1 → ∀ v ∈ S, v ≠ 1 →
        ∃ k ∈ Subgroup.normalizer (S : Set G), k * u * k⁻¹ = v := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hG : TheoremFourHyp G := h.toTheoremFourHyp
  have hd := h.data83
  have hn1 : 1 ≤ n := hd.odd.pos
  have hAe : CFSG.Assembly.IsElemAbelian 3 A := h.mem_partTwoF.1
  have hA81 : Nat.card A = 81 := hd.card_eq
  have hcomm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hAe.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  set K := inSubgroup perfectResidual (L ⊓ Subgroup.centralizer ({d} : Set G)) with hKdef
  set E := Subgroup.closure ({c, a, d} : Set G) with hEdef
  have hEA : E ≤ A := closure_le_of_sec8Std h
  have hE3 : IsPGroup 3 E := (Sec5.isPGroup_of_isElemAbelian hAe).to_le hEA
  have hKL : K ≤ L := (Item87Proof.residual_le _).trans inf_le_left
  have hAL : A ≤ Subgroup.normalizer (L : Set G) :=
    Sec6.le_normalizer_of_mem_thetaComponentsAt h45 hG hAe h.mem_A h.ne_one L
      h.mem_thetaComponentsAt
  have hdA : d ∈ A := hd.d_mem
  have hAK : A ≤ Subgroup.normalizer (K : Set G) := by
    intro x hx
    have hxC : x ∈ Subgroup.normalizer (Subgroup.centralizer ({d} : Set G) : Set G) :=
      Subgroup.le_normalizer (Subgroup.mem_centralizer_singleton_iff.mpr (hcomm x hx d hdA))
    have hxLd : x ∈ Subgroup.normalizer
        ((L ⊓ Subgroup.centralizer {d} : Subgroup G) : Set G) :=
      Subgroup.inf_normalizer_le_normalizer_inf ⟨hAL hx, hxC⟩
    exact CFSG.RankThree.GroupTheory.SteinbergBY.normalizer_le_normalizer_inSubgroup_perfectResidual
      _ hxLd
  set θL : Subgroup G := inSubgroup (aschbacherSolvableCore 3) L with hθL
  set N : Subgroup G := K ⊓ θL with hN
  have hAN : A ≤ Subgroup.normalizer (N : Set G) := fun x hx =>
    Subgroup.inf_normalizer_le_normalizer_inf
      ⟨hAK hx, Sec6.normalizer_le_normalizer_theta L (hAL hx)⟩
  have hN3 : ¬ 3 ∣ Nat.card N := by
    intro hdvd
    have h1 : Nat.card N ∣ Nat.card θL := Subgroup.card_dvd_of_le inf_le_right
    rw [hθL, inSubgroup, Subgroup.card_map_of_injective L.subtype_injective] at h1
    exact KFacts.not_three_dvd_card_aschbacherSolvableCore L (hdvd.trans h1)
  have hNodd : Odd (Nat.card N) :=
    odd_card_of_le_normalizer hG.localRank_three.le hAe hA81 hN3 hAN
  set F := GaloisField 2 (3 * n) with hF
  obtain ⟨e⟩ := hK
  let e₂ : projSL 2 F ≃* SL(2, F) :=
    (CFSG.RankThree.PartTwo.KFacts.L34.projSLEquivProjectiveSL 2 F).trans
      (CFSG.LocalAnalysis.ComponentInitial.LinearCover.projectiveSLTwoEquivSL F)
  let θ := aschbacherSolvableCore 3 L
  let φ₀ : K →* L ⧸ θ := (QuotientGroup.mk' θ).comp (Subgroup.inclusion hKL)
  have hφ₀mem : ∀ x : K, φ₀ x ∈ imageModTheta L K := fun x =>
    ⟨⟨x, hKL x.2⟩, Subgroup.mem_subgroupOf.mpr x.2, rfl⟩
  let φ₁ : K →* imageModTheta L K := φ₀.codRestrict _ hφ₀mem
  let φ : K →* SL(2, F) := (e₂.toMonoidHom.comp e.toMonoidHom).comp φ₁
  have hφ₁ : Function.Surjective φ₁ := by
    rintro ⟨y, ⟨z, hz, rfl⟩⟩
    exact ⟨⟨z, Subgroup.mem_subgroupOf.mp hz⟩, rfl⟩
  have hφ : Function.Surjective φ := (e₂.surjective.comp e.surjective).comp hφ₁
  have hNker : ∀ x : K, φ x = 1 ↔ (x : G) ∈ N := by
    intro x
    have h1 : φ x = 1 ↔ φ₁ x = 1 := by
      change e₂ (e (φ₁ x)) = 1 ↔ _
      rw [MulEquiv.map_eq_one_iff, MulEquiv.map_eq_one_iff]
    rw [h1]
    constructor
    · intro h1x
      have h2 : (QuotientGroup.mk' θ) (Subgroup.inclusion hKL x) = 1 := congrArg Subtype.val h1x
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h2
      exact ⟨x.2, ⟨_, h2, rfl⟩⟩
    · rintro ⟨-, ⟨y, hy, hyx⟩⟩
      apply Subtype.ext
      have : Subgroup.inclusion hKL x = y := Subtype.ext hyx.symm
      change (QuotientGroup.mk' θ) (Subgroup.inclusion hKL x) = 1
      rw [this, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      exact hy
  have hNK : N ≤ K := inf_le_left
  have hFcard : Nat.card F = 2 ^ (3 * n) := GaloisField.card 2 (3 * n) (by omega)
  have hr : Odd (Nat.card F ^ 2 - 1) := by
    have h2 : 2 ∣ Nat.card F ^ 2 := by
      rw [hFcard]
      exact dvd_pow (dvd_pow_self 2 (by omega)) two_ne_zero
    have h1 : 1 ≤ Nat.card F ^ 2 := Nat.one_le_pow _ _ (by rw [hFcard]; positivity)
    rw [Nat.odd_iff]
    omega
  have hH : Nat.card SL(2, F) = 2 ^ (3 * n) * (Nat.card F ^ 2 - 1) := by
    rw [CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two F, hFcard]
  have hsyl : ∀ U : Subgroup SL(2, F), Nat.card U = 2 ^ (3 * n) →
      CFSG.Assembly.IsElemAbelian 2 U ∧ ∀ u ∈ U, ∀ v ∈ U, u ≠ 1 → v ≠ 1 →
        ∃ g ∈ Subgroup.normalizer (U : Set SL(2, F)), g * u * g⁻¹ = v := by
    intro U hU
    have hfac : (Nat.card SL(2, F)).factorization 2 = 3 * n := by
      have := factorization_two_mul (a := 1) (b := Nat.card F ^ 2 - 1) (m := 3 * n) odd_one hr
      rw [hH]
      simpa using this
    obtain ⟨hE, -, hT⟩ := KFacts.sylow_two_sl2 (Sylow.ofCard U (by rw [hU, hfac]))
    exact ⟨hE, hT⟩
  have hTIsl : ∀ U U' : Subgroup SL(2, F), Nat.card U = 2 ^ (3 * n) → Nat.card U' = 2 ^ (3 * n) →
      ∀ x ∈ U, x ∈ U' → x ≠ 1 → U = U' := by
    intro U U' hU hU' x hx hx' hx1
    by_contra hne
    have hbot := CFSG.CGT.PushingUpLit.A78G0.inf_eq_bot_of_card_SL2 (e := 3 * n) (by omega) hU hU'
      hne
    have hmem : x ∈ U ⊓ U' := ⟨hx, hx'⟩
    rw [hbot, Subgroup.mem_bot] at hmem
    exact hx1 hmem
  obtain ⟨T, hT, hT1, hTK⟩ := exists_invariant_two_of_sec8Std hKB h
  have hT2 : IsPGroup 2 T := (isPiSubgroup_piOf_iff Nat.prime_two T).mp hT.2.1
  obtain ⟨S, hSK, hScard, hSelem, hES, htrans⟩ := exists_lift_sylow φ hφ hNker hNK hNodd hN3
    hr hH
    (fun U hU x hx y hy => ⟨congrArg Subtype.val ((hsyl U hU).1.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩),
      (hsyl U hU).1.2 x hx⟩)
    hTIsl (fun U hU u hu hu1 v hv hv1 => (hsyl U hU).2 u hu v hv hu1 hv1) hE3 (hEA.trans hAK)
    (hEA.trans hAN) hTK hT2 hT1 hT.2.2
  have hmod := Sec6.card_inf_centralizer_modEq (p := 3) hE3 hES
  have h2mod : Nat.card S ≡ 2 [MOD 3] := by
    rw [hScard]
    exact two_pow_three_mul_odd_mod hd.odd
  have hne : S ⊓ Subgroup.centralizer (E : Set G) ≠ ⊥ := by
    intro hb
    rw [hb, Subgroup.card_bot] at hmod
    exact absurd (hmod.trans h2mod) (by decide)
  obtain ⟨⟨s, hsS, hsC⟩, hs1'⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hne
  have hs1 : s ≠ 1 := fun h => hs1' (Subtype.ext h)
  refine ⟨S, s, hSK, hSelem, hScard, hES, hsS, hs1, fun x hx => ?_, htrans⟩
  rw [Subgroup.mem_centralizer_singleton_iff]
  exact Subgroup.mem_centralizer_iff.mp hsC x hx

end CFSG.RankThree.PartTwo.Sec8.HeringU3n
