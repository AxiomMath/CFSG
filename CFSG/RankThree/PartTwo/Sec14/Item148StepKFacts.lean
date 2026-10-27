module

public import CFSG.RankThree.PartTwo.Sec14.Item148StepQuot
import CFSG.RankThree.PartTwo.KFacts.KS18A7M22Proof
import CFSG.RankThree.PartTwo.KFacts.KS18M12Proof
import CFSG.RankThree.PartTwo.KFacts.KS17J2AutOuter
import CFSG.LocalAnalysis.ComponentClassification.J2CoverAut
import CFSG.RankThree.PartTwo.Sec13.Item13Sporadic
import CFSG.RankThree.PartTwo.Sec13.Item13Models
import CFSG.RankThree.PartTwo.Sec19.Step1914Tri

public section

namespace CFSG.RankThree.PartTwo.Sec14

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.LocalRank

@[expose] def KF148Inner : Prop :=
  ∀ (X : Type) [Group X] [Finite X],
    (Nonempty (X ≃* CFSG.Blueprint.NativeSporadic.J2) ∨
      Nonempty (X ≃* alternatingGroup (Fin 7)) ∨
      Nonempty (X ≃* CFSG.Blueprint.NativeSporadic.M22) ∨
      Nonempty (X ≃* CFSG.Blueprint.NativeSporadic.M12) ∨
      Nonempty (X ≃* alternatingGroup (Fin 10))) →
    Subgroup.center X = ⊥ ∧ ∀ σ : MulAut X, σ ^ 3 = 1 → σ ∈ (MulAut.conj : X →* MulAut X).range

@[expose] def KF148PGL : Prop :=
  ∀ (Γ : Type) [Group Γ] [Finite Γ] (X E : Subgroup Γ),
    Group.IsPerfect ↥X →
    (IsLThreePi ↥X ∨ ∃ (p f : ℕ) (_ : Fact p.Prime), p ≠ 3 ∧ 1 ≤ f ∧ IsLThreeEpsAt ↥X p f) →
    E ≤ Subgroup.normalizer (X : Set Γ) → CFSG.Assembly.IsElemAbelian 3 E → Nat.card E = 27 →
    (∀ g ∈ Subgroup.centralizer (E : Set Γ), g ^ 3 = 1 → g ∈ E) →
    (∃ z : Γ, z ≠ 1 ∧ E ⊓ Subgroup.centralizer (X : Set Γ) = Subgroup.zpowers z) →
    (∃ a ∈ E, ¬ InnerOn148 X a) →
    ∃ (p f : ℕ), 1 ≤ f ∧ IsZ3PGLThreeAt ↥(X ⊔ E) p f

section Field


@[expose] def KF148Field : Prop :=
  ∀ (Γ : Type) [Group Γ] [Finite Γ] (X : Subgroup Γ) (n : ℕ) (x y : Γ), 1 ≤ n →
    Sec4.IsoLThreePi ↥X 2 (3 * n) → KFacts.InducesStdKind X x .field → x ^ 3 = 1 →
    y ∈ Subgroup.normalizer (X : Set Γ) → y ^ 3 = 1 → x * y = y * x →
    ∃ k : ℕ, InnerOn148 X (y * x ^ k)

end Field

theorem center_eq_bot_of_mulEquiv148 {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y)
    (hY : Subgroup.center Y = ⊥) : Subgroup.center X = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  have hex : e x ∈ Subgroup.center Y := by
    rw [Subgroup.mem_center_iff] at hx ⊢
    intro y
    obtain ⟨z, rfl⟩ := e.surjective y
    rw [← map_mul, ← map_mul, hx z]
  rw [hY, Subgroup.mem_bot] at hex
  rw [Subgroup.mem_bot]
  exact e.injective (hex.trans (map_one e).symm)

theorem center_eq_bot_of_isSimpleGroup148 {X : Type*} [Group X] [hS : IsSimpleGroup X]
    [hP : Group.IsPerfect X] : Subgroup.center X = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center X) with h | h
  · exact h
  · exfalso
    have hcomm : IsMulCommutative X := ⟨⟨fun a b => by
      have hb : b ∈ Subgroup.center X := h ▸ Subgroup.mem_top b
      exact (Subgroup.mem_center_iff.mp hb a)⟩⟩
    exact Group.IsPerfect.not_isMulCommutative X hcomm

theorem card_mulAut_alternatingGroup_ten :
    Nat.card (MulAut (alternatingGroup (Fin 10))) = 3628800 := by
  rw [← Nat.card_congr (MulEquiv.ofBijective _
    (CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 10 (by norm_num)
      (by norm_num))).toEquiv, Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
  rfl

theorem a10_facts148 (X : Type) [Group X] [Finite X]
    (hX : Nonempty (X ≃* alternatingGroup (Fin 10))) :
    Subgroup.center X = ⊥ ∧
      ∀ σ : MulAut X, σ ^ 3 = 1 → σ ∈ (MulAut.conj : X →* MulAut X).range := by
  obtain ⟨e⟩ := hX
  have h4 : 4 ≤ Nat.card (Fin 10) := by
    rw [Nat.card_eq_fintype_card, Fintype.card_fin]
    norm_num
  have hZ : Subgroup.center X = ⊥ :=
    center_eq_bot_of_mulEquiv148 e (alternatingGroup.center_eq_bot h4)
  refine ⟨hZ, fun σ hσ => ?_⟩
  have hXc : Nat.card X = 1814400 := by
    rw [Nat.card_congr e.toEquiv]
    exact KFacts.KS14.card_alternatingGroup_five_seven_ten.2.2
  have hAut : Nat.card (MulAut X) ≤ 2 * Nat.card X := by
    rw [Nat.card_congr (MulAut.congr e).toEquiv, card_mulAut_alternatingGroup_ten, hXc]
  obtain ⟨x, hx⟩ := KFacts.KS14.exists_conj_of_card_mulAut_le hZ hAut σ ⟨1, by rwa [pow_one]⟩
  exact ⟨x, hx.symm⟩

theorem kf148Inner :
    KF148Inner := by
  intro X _ _ hX
  have hpow : ∀ σ : MulAut X, σ ^ 3 = 1 → ∃ k : ℕ, σ ^ 3 ^ k = 1 :=
    fun σ hσ => ⟨1, by rwa [pow_one]⟩
  rcases hX with ⟨⟨e⟩⟩ | hA7 | hM22 | hM12 | hA10
  · refine ⟨center_eq_bot_of_mulEquiv148 e sporadicModels131.2.2.2, fun σ hσ => ?_⟩
    exact KFacts.ks17J2AutThree_of_outer
      CFSG.ComponentClassification.J2Cover.ctuc_j2_full_automorphism_permutation_model.2.2.2.2.2
      X ⟨e⟩ σ hσ
  · obtain ⟨-, hZ, hin, -⟩ := KFacts.KS14.ks18A7M22 X (Or.inl hA7)
    refine ⟨hZ, fun σ hσ => ?_⟩
    obtain ⟨x, hx⟩ := hin σ (hpow σ hσ)
    exact ⟨x, hx.symm⟩
  · obtain ⟨-, hZ, hin, -⟩ := KFacts.KS14.ks18A7M22 X (Or.inr hM22)
    refine ⟨hZ, fun σ hσ => ?_⟩
    obtain ⟨x, hx⟩ := hin σ (hpow σ hσ)
    exact ⟨x, hx.symm⟩
  · obtain ⟨-, hZ, hin, -⟩ := KFacts.ks18M12 X hM12
    refine ⟨hZ, fun σ hσ => ?_⟩
    obtain ⟨x, hx⟩ := hin σ (hpow σ hσ)
    exact ⟨x, hx.symm⟩
  · exact a10_facts148 X hA10

theorem kf148CenterL3 :
    ∀ (X : Type) [Group X] [Finite X], Group.IsPerfect X →
      (IsLThreePi X ∨ ∃ (p f : ℕ) (_ : Fact p.Prime), p ≠ 3 ∧ 1 ≤ f ∧ IsLThreeEpsAt X p f) →
      Subgroup.center X = ⊥ := by
  intro X _ _ hP hL
  by_cases hnt : Nontrivial X
  swap
  · rw [not_nontrivial_iff_subsingleton] at hnt
    exact Subsingleton.elim _ _
  have hU2 : ∀ (p e : ℕ) [Fact p.Prime], p ^ e = 2 →
      Nonempty (X ≃* CFSG.Assembly.RankThreeEven.projSU 3 p e) → False := by
    intro p e hp h2 ⟨φ⟩
    obtain ⟨rfl, rfl⟩ := eq_two_one_of_pow_eq_two hp.out h2
    have := isSolvable_projSU_two
    have hsol : Group.IsSolvable X :=
      Group.isSolvable_of_isSolvable_injective (f := φ.toMonoidHom) φ.injective
    exact Group.IsPerfect.not_isSolvable X hsol
  have hS : IsSimpleGroup X := by
    rcases hL with ⟨p, e, hp, he, hcase⟩ | ⟨p, f, hp, -, hf, hcase⟩
    · rcases hcase with ⟨-, ⟨φ⟩⟩ | ⟨-, ⟨φ⟩⟩
      · have := Sec19.Step1914TriProof.isSimpleGroup_projSL_three_of_field (GaloisField p e)
        exact φ.isSimpleGroup
      · by_cases h2 : p ^ e = 2
        · exact (hU2 p e h2 ⟨φ⟩).elim
        · have := Sec19.Step1914TriProof.isSimpleGroup_projSU_three_of_ne_two p e he h2
          exact φ.isSimpleGroup
    · rcases hcase with ⟨⟨φ⟩⟩ | ⟨hq2, ⟨φ⟩⟩
      · have := Sec19.Step1914TriProof.isSimpleGroup_projSL_three_of_field (GaloisField p f)
        exact φ.isSimpleGroup
      · have := Sec19.Step1914TriProof.isSimpleGroup_projSU_three_of_ne_two p f hf (by omega)
        exact φ.isSimpleGroup
  exact center_eq_bot_of_isSimpleGroup148

end CFSG.RankThree.PartTwo.Sec14
