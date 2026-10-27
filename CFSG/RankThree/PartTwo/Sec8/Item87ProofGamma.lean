module

public import CFSG.RankThree.PartTwo.Sec8.Item87Proof418
import CFSG.RankThree.PartTwo.KFacts.K71Coprime
import CFSG.RankThree.PartTwo.Sec21.Item229Pre
import CFSG.LocalAnalysis.SectionRank.OddCover.DegreeThree
import CFSG.GroupTheory.LocalCores.Layer.CentralExtension
import CFSG.LocalAnalysis.ComponentClassification.AssemblyBPredicates
public import CFSG.RankThree.PartTwo.Sec8.Item87ProofTools

public section

namespace CFSG.RankThree.PartTwo.Sec8

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projSL projSU projSp)
open CFSG.Assembly.LowTwoRank (StatedSU)

@[expose] def NoThetaNormal (Q : Type*) [Group Q] : Prop :=
  ∀ N : Subgroup Q, N.Normal → Group.IsSolvable N → ¬ 3 ∣ Nat.card N → N = ⊥

@[expose] def IsGammaTypeRee (X : Type) [Group X] (m : ℕ) : Prop :=
  ∃ (k : ℕ) (hk : (TauCeti.LieTypeIndex.reeF4 k).Valid), 2 * k + 1 = 3 * m ∧
    Nonempty (X ≃* (TauCeti.CFSGIndex.lie ⟨.reeF4 k, hk⟩).Group)

@[expose] def IsGammaTypeL2 (X : Type) [Group X] (m : ℕ) : Prop :=
  (∃ (q : TauCeti.PrimePower) (hq : (TauCeti.LieTypeIndex.trialityD4 q).Valid),
      q.p = 2 ∧ q.exponent = m ∧
        Nonempty (X ≃* (TauCeti.CFSGIndex.lie ⟨.trialityD4 q, hq⟩).Group)) ∨
    (∃ q : TauCeti.PrimePower, q.p = 2 ∧ q.exponent = 3 * m ∧ Sec4.IsoGTwo X q) ∨
    Nonempty (X ≃* projSU 3 2 (3 * m)) ∨ IsoSUThree X (2 ^ (3 * m)) ∨
    Nonempty (X ≃* projSp 2 (GaloisField 2 (3 * m)))

@[expose] def IsGammaType (X : Type) [Group X] (m : ℕ) : Prop :=
  IsGammaTypeRee X m ∨ IsGammaTypeL2 X m

namespace Item87Proof

variable {G : Type} [Group G] [Finite G]

theorem NoThetaNormal.of_mulEquiv {Q Q' : Type*} [Group Q] [Group Q'] (e : Q ≃* Q')
    (h : NoThetaNormal Q') : NoThetaNormal Q := by
  intro N hN hNs hN3
  have hM := h (N.map e.toMonoidHom) (hN.map _ e.surjective)
    (by
      have := hNs
      exact Group.isSolvable_of_surjective (e.toMonoidHom.subgroupMap_surjective N))
    (by
      rw [Nat.card_congr (N.equivMapOfInjective e.toMonoidHom e.injective).toEquiv.symm]
      exact hN3)
  rwa [Subgroup.map_eq_bot_iff_of_injective _ e.injective] at hM

theorem three_dvd_four_pow_sub_one (a : ℕ) : 3 ∣ 4 ^ a - 1 := by
  have h := Nat.pow_mod 4 a 3
  norm_num at h
  have h1 : 1 ≤ 4 ^ a := Nat.one_le_pow _ _ (by norm_num)
  omega

theorem three_dvd_card_projSL_two {a : ℕ} (ha : 1 ≤ a) :
    3 ∣ Nat.card (projSL 2 (GaloisField 2 a)) := by
  rw [Sec21.card_projSL_two a ha]
  refine Dvd.dvd.mul_left ?_ _
  have h4 : (2 ^ a) ^ 2 = 4 ^ a := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
  rw [h4]
  exact three_dvd_four_pow_sub_one a

theorem noThetaNormal_projSL_two {m : ℕ} (hm : 2 ≤ m) :
    NoThetaNormal (projSL 2 (GaloisField 2 m)) := by
  have := Sec21.isSimpleGroup_projSL_two hm
  intro N hN _ hN3
  rcases hN.eq_bot_or_eq_top with h | h
  · exact h
  · exfalso
    apply hN3
    rw [h, Subgroup.card_top]
    exact three_dvd_card_projSL_two (by omega)

theorem isQuasisimple_projSL_two {m : ℕ} (hm : 2 ≤ m) :
    IsQuasisimple (projSL 2 (GaloisField 2 m)) := by
  have := Sec21.isSimpleGroup_projSL_two hm
  refine (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup ?_).1
  by_contra hab
  push Not at hab
  let _ : CommGroup (projSL 2 (GaloisField 2 m)) :=
    { (inferInstance : Group _) with mul_comm := hab }
  have hp := IsSimpleGroup.prime_card (α := projSL 2 (GaloisField 2 m))
  rw [Sec21.card_projSL_two m (by omega)] at hp
  have h2 : 2 ∣ 2 ^ m * ((2 ^ m) ^ 2 - 1) := Dvd.dvd.mul_right (dvd_pow_self 2 (by omega)) _
  rcases (Nat.Prime.eq_one_or_self_of_dvd hp 2 h2) with h | h
  · omega
  · have h4 : 4 ≤ 2 ^ m := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
    have h15 : 15 ≤ (2 ^ m) ^ 2 - 1 := by
      have := Nat.pow_le_pow_left h4 2
      omega
    have : 4 * 15 ≤ 2 ^ m * ((2 ^ m) ^ 2 - 1) := Nat.mul_le_mul h4 h15
    omega

theorem isQuasisimple_statedSU_three {F : Type} [Field F] [Finite F] {f : ℕ}
    (hF : Nat.card F = (2 ^ f) ^ 2) (hf : 2 ≤ f) :
    IsQuasisimple (StatedSU 3 (2 ^ f) F) ∧
      Nat.card (Subgroup.center (StatedSU 3 (2 ^ f) F)) ∣ 3 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hnq : (3, 2 ^ f) ≠ (3, 2) := by
    intro h
    have h' : 2 ^ f = 2 := (Prod.mk.inj h).2
    have : 4 ≤ 2 ^ f := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
    omega
  obtain ⟨hq, hZ⟩ := CFSG.LieType.Universal.Unitary.isQuasisimple_statedSU_of_card hF le_rfl hnq
  refine ⟨hq, ?_⟩
  rw [hZ, (CFSG.LinearGroups.unitary_scalar_kernel Nat.prime_two hF (by norm_num)).2.2]
  exact Nat.gcd_dvd_left _ _

theorem three_dvd_card_statedSU_three {F : Type} [Field F] [Finite F] {f : ℕ}
    (hF : Nat.card F = (2 ^ f) ^ 2) :
    3 ∣ Nat.card (StatedSU 3 (2 ^ f) F) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := Fintype.ofFinite F
  have : CharP F 2 := charP_of_card_eq_prime_pow (f := 2 * f)
    (by rw [← Nat.card_eq_fintype_card, hF, ← pow_mul, mul_comm])
  rw [CFSG.SectionRank.OddCover.card_statedSU_three hF]
  refine Dvd.dvd.mul_right (Dvd.dvd.mul_left ?_ _) _
  have h4 : (2 ^ f) ^ 2 = 4 ^ f := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
  rw [h4]
  exact three_dvd_four_pow_sub_one f

theorem noThetaNormal_statedSU {F : Type} [Field F] [Finite F] {f : ℕ}
    (hF : Nat.card F = (2 ^ f) ^ 2) (hf : 2 ≤ f) : NoThetaNormal (StatedSU 3 (2 ^ f) F) := by
  obtain ⟨hq, hZ⟩ := isQuasisimple_statedSU_three hF hf
  intro N hN _ hN3
  have hqo := (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native _).mpr hq
  rcases CFSG.ComponentClassification.Quasisimple.normal_le_center_or_eq_top hqo N with h | h
  · have hdvd : Nat.card N ∣ 3 := (Subgroup.card_dvd_of_le h).trans hZ
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h3
    · exact Subgroup.eq_bot_of_card_eq N h1
    · exfalso
      apply hN3
      rw [h3]
  · exfalso
    apply hN3
    rw [h, Subgroup.card_top]
    exact three_dvd_card_statedSU_three hF

theorem isGammaIndex_cases {A Le : Subgroup G} {d : G} {m : ℕ} (h : IsGammaIndex A Le d m) :
    d ∈ A ∧ d ≠ 1 ∧ 1 ≤ m ∧
      ((IsGammaTypeRee (Le ⧸ aschbacherSolvableCore 3 Le) m ∧
          IsoSUThree (imageModTheta Le
            (inSubgroup perfectResidual (Le ⊓ Subgroup.centralizer ({d} : Set G))))
            (2 ^ (3 * m))) ∨
        (IsGammaTypeL2 (Le ⧸ aschbacherSolvableCore 3 Le) m ∧
          Nonempty (imageModTheta Le
            (inSubgroup perfectResidual (Le ⊓ Subgroup.centralizer ({d} : Set G))) ≃*
              projSL 2 (GaloisField 2 (3 * m))))) := by
  obtain ⟨hdA, hd1, hm, hcases⟩ := h
  refine ⟨hdA, hd1, hm, ?_⟩
  rcases hcases with ⟨k, hk, hkm, he, hSU⟩ | ⟨htype, hL2⟩
  · exact Or.inl ⟨⟨k, hk, hkm, he⟩, hSU⟩
  · exact Or.inr ⟨htype, hL2⟩

theorem isGammaType_of_isGammaIndex {A Le : Subgroup G} {d : G} {m : ℕ}
    (h : IsGammaIndex A Le d m) : IsGammaType (Le ⧸ aschbacherSolvableCore 3 Le) m := by
  obtain ⟨-, -, -, h | h⟩ := isGammaIndex_cases h
  · exact Or.inl h.1
  · exact Or.inr h.1

theorem residual_of_isGammaIndex {A Le : Subgroup G} {e d : G} {m : ℕ}
    (hLe : Le ∈ thetaComponentsAt 3 e) (h : IsGammaIndex A Le d m) :
    inSubgroup perfectResidual (Le ⊓ Subgroup.centralizer ({d} : Set G)) ∈
        thetaComponentsIn (Subgroup.centralizer {e} ⊓ Subgroup.centralizer {d}) ∧
      IsType418 (inSubgroup perfectResidual (Le ⊓ Subgroup.centralizer ({d} : Set G)) ⧸
        aschbacherSolvableCore 3
          (inSubgroup perfectResidual (Le ⊓ Subgroup.centralizer ({d} : Set G)))) m ∧
      inSubgroup perfectResidual (Le ⊓ Subgroup.centralizer ({d} : Set G)) ≠ ⊥ := by
  set K := inSubgroup perfectResidual (Le ⊓ Subgroup.centralizer ({d} : Set G)) with hK
  have hKL : K ≤ Le := (residual_le _).trans inf_le_left
  obtain ⟨-, -, hm, hcases⟩ := isGammaIndex_cases h
  have hm3 : 2 ≤ 3 * m := by omega
  rcases hcases with ⟨-, F, hF, hFf, hFc, ⟨φ⟩⟩ | ⟨-, ⟨φ⟩⟩
  · obtain ⟨hq, -⟩ := isQuasisimple_statedSU_three hFc hm3
    have hKq := isQuasisimple_quot_of_imageModTheta hKL
      (LocalCores.isQuasisimple_of_mulEquiv φ.symm hq)
    obtain ⟨ψ⟩ := nonempty_quot_mulEquiv_imageModTheta hKL
      (NoThetaNormal.of_mulEquiv φ (noThetaNormal_statedSU hFc hm3))
    refine ⟨mem_thetaComponentsIn_residual hLe hKq, Or.inl ⟨F, hF, hFf, hFc, ⟨ψ.trans φ⟩⟩, ?_⟩
    have : Nontrivial (StatedSU 3 (2 ^ (3 * m)) F) :=
      CFSG.LocalCores.isQuasisimple_nontrivial hq
    exact KFacts.ne_bot_of_imageModTheta_mulEquiv φ
  · have hq := isQuasisimple_projSL_two hm3
    have hKq := isQuasisimple_quot_of_imageModTheta hKL
      (LocalCores.isQuasisimple_of_mulEquiv φ.symm hq)
    obtain ⟨ψ⟩ := nonempty_quot_mulEquiv_imageModTheta hKL
      (NoThetaNormal.of_mulEquiv φ (noThetaNormal_projSL_two hm3))
    refine ⟨mem_thetaComponentsIn_residual hLe hKq, Or.inr (Or.inl ⟨ψ.trans φ⟩), ?_⟩
    have : Nontrivial (projSL 2 (GaloisField 2 (3 * m))) :=
      CFSG.LocalCores.isQuasisimple_nontrivial hq
    exact KFacts.ne_bot_of_imageModTheta_mulEquiv φ

end Item87Proof

end CFSG.RankThree.PartTwo.Sec8
