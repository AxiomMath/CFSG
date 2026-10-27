module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC56Model
public import CFSG.LinearAlgebra.SL2MinimalFaithfulMatrix

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Open Subgroup
open scoped MatrixGroups

namespace OmegaModel

variable {W : Type} [CommGroup W] (S : OmegaModel W)

private theorem finite_W (S : OmegaModel W) : Finite W :=
  Finite.of_injective (S.e : W → Multiplicative (OmI → S.K)) S.e.injective

private theorem finite_mulAut (S : OmegaModel W) : Finite (MulAut W) := by
  haveI := finite_W S
  exact Finite.of_injective (fun g : MulAut W => (g : W → W)) DFunLike.coe_injective

theorem card_omega0_eq :
    Nat.card S.omega0 = (Nat.card S.K * (Nat.card S.K ^ 2 - 1)) ^ 2 := by
  have hSL : Nat.card (SL(2, S.K)) = Nat.card S.K * (Nat.card S.K ^ 2 - 1) :=
    CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two S.K
  change Nat.card (S.jHom.range) = (Nat.card S.K * (Nat.card S.K ^ 2 - 1)) ^ 2
  rw [Nat.card_congr (MonoidHom.ofInjective S.jHom_injective).toEquiv.symm, Nat.card_prod, hSL]
  exact (pow_two _).symm

theorem omega_eq_omega0_of_card
    (h : Nat.card S.omega = (Nat.card S.K * (Nat.card S.K ^ 2 - 1)) ^ 2) :
    S.omega = S.omega0 := by
  haveI := finite_mulAut S
  have hcard : Nat.card S.omega ≤ Nat.card S.omega0 := by
    rw [h, card_omega0_eq S]
  exact (Subgroup.eq_of_le_of_card_ge (H := S.omega0) (K := S.omega) (omega0_le_omega S)
    hcard).symm

@[expose] def factor : Fin 2 → Subgroup (MulAut W)
  | 0 => (S.jHom.comp (MonoidHom.inl _ _)).range
  | 1 => (S.jHom.comp (MonoidHom.inr _ _)).range

theorem factor_sup : S.factor 0 ⊔ S.factor 1 = S.omega0 := by
  apply le_antisymm
  · refine sup_le ?_ ?_
    · show (S.jHom.comp (MonoidHom.inl _ _)).range ≤ S.omega0
      rintro x ⟨a, rfl⟩
      exact (MonoidHom.mem_range (f := S.jHom)).mpr ⟨(a, 1), rfl⟩
    · show (S.jHom.comp (MonoidHom.inr _ _)).range ≤ S.omega0
      rintro x ⟨a, rfl⟩
      exact (MonoidHom.mem_range (f := S.jHom)).mpr ⟨(1, a), rfl⟩
  · rintro x ⟨p, rfl⟩
    have hp : p = (p.1, 1) * (1, p.2) := by ext <;> simp
    rw [hp, map_mul]
    refine Subgroup.mul_mem_sup ?_ ?_
    · exact (MonoidHom.mem_range (f := S.jHom.comp (MonoidHom.inl _ _))).mpr ⟨p.1, rfl⟩
    · exact (MonoidHom.mem_range (f := S.jHom.comp (MonoidHom.inr _ _))).mpr ⟨p.2, rfl⟩

theorem factor_commute {j l : Fin 2} (hjl : j ≠ l) :
    ∀ x ∈ S.factor j, ∀ y ∈ S.factor l, x * y = y * x := by
  fin_cases j <;> fin_cases l
  · exact (hjl rfl).elim
  · intro x hx y hy
    obtain ⟨a, rfl⟩ := MonoidHom.mem_range.mp hx
    obtain ⟨b, rfl⟩ := MonoidHom.mem_range.mp hy
    change S.jHom (a, 1) * S.jHom (1, b) = S.jHom (1, b) * S.jHom (a, 1)
    rw [← map_mul, ← map_mul]
    rw [show (a, 1) * (1, b) = (1, b) * (a, 1) by ext <;> simp]
  · intro x hx y hy
    obtain ⟨a, rfl⟩ := MonoidHom.mem_range.mp hx
    obtain ⟨b, rfl⟩ := MonoidHom.mem_range.mp hy
    change S.jHom (1, a) * S.jHom (b, 1) = S.jHom (b, 1) * S.jHom (1, a)
    rw [← map_mul, ← map_mul]
    rw [show (1, a) * (b, 1) = (b, 1) * (1, a) by ext <;> simp]
  · exact (hjl rfl).elim

theorem nonempty_mulEquiv_factor (j : Fin 2) : Nonempty (↥(S.factor j) ≃* SL(2, S.K)) := by
  fin_cases j
  · exact ⟨(MonoidHom.ofInjective (f := S.jHom.comp (MonoidHom.inl _ _))
      (S.jHom_injective.comp fun a b h => congrArg Prod.fst h)).symm⟩
  · exact ⟨(MonoidHom.ofInjective (f := S.jHom.comp (MonoidHom.inr _ _))
      (S.jHom_injective.comp fun a b h => congrArg Prod.snd h)).symm⟩

theorem card_factor (j : Fin 2) :
    Nat.card ↥(S.factor j) = Nat.card S.K * (Nat.card S.K ^ 2 - 1) := by
  obtain ⟨e⟩ := nonempty_mulEquiv_factor S j
  rw [Nat.card_congr e.toEquiv,
    CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two S.K]

private theorem center_specialLinearGroup_two_eq_bot (K : Type*) [Field K] [CharP K 2] :
    Subgroup.center (SL(2, K)) = ⊥ := by
  rw [eq_bot_iff]
  intro A hA
  obtain ⟨c, hc, hcA⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hA
  have hc1 : c = 1 := CharTwo.sq_injective (by simpa using hc)
  rw [Subgroup.mem_bot]
  ext i j
  rw [← hcA, hc1]
  simp [Matrix.one_apply]

private theorem isSimpleGroup_specialLinearGroup_two_of_charTwo
    (K : Type*) [Field K] [CharP K 2] (hK : 4 ≤ Nat.card K) :
    IsSimpleGroup (SL(2, K)) := by
  haveI : IsSimpleGroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) K) :=
    Matrix.ProjectiveSpecialLinearGroup.rank_two_simple hK
  have e : SL(2, K) ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) K :=
    QuotientGroup.quotientBot.symm.trans
      (QuotientGroup.quotientMulEquivOfEq (center_specialLinearGroup_two_eq_bot K).symm)
  exact e.isSimpleGroup

theorem isSimpleGroup_factor (j : Fin 2) : IsSimpleGroup ↥(S.factor j) := by
  haveI : IsSimpleGroup (SL(2, S.K)) :=
    isSimpleGroup_specialLinearGroup_two_of_charTwo S.K S.four_le
  obtain ⟨e⟩ := nonempty_mulEquiv_factor S j
  exact e.isSimpleGroup

theorem center_factor (j : Fin 2) : Subgroup.center ↥(S.factor j) = ⊥ := by
  obtain ⟨e⟩ := nonempty_mulEquiv_factor S j
  rw [eq_bot_iff]
  intro z hz
  rw [Subgroup.mem_bot]
  have hze : e z ∈ Subgroup.center (SL(2, S.K)) := by
    rw [Subgroup.mem_center_iff]
    intro w
    obtain ⟨y, rfl⟩ := e.surjective w
    rw [← map_mul, ← map_mul]
    rw [Subgroup.mem_center_iff.mp hz y]
  rw [center_specialLinearGroup_two_eq_bot, Subgroup.mem_bot] at hze
  exact e.injective (by simpa using hze)

theorem factor_inf_factor : S.factor 0 ⊓ S.factor 1 = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  rw [Subgroup.mem_inf] at hx
  rw [Subgroup.mem_bot]
  have hcent : (⟨x, hx.1⟩ : ↥(S.factor 0)) ∈ Subgroup.center ↥(S.factor 0) := by
    rw [Subgroup.mem_center_iff]
    intro y
    apply Subtype.ext
    exact (factor_commute S (j := 1) (l := 0) (by decide) x hx.2 y y.2).symm
  rw [center_factor S 0, Subgroup.mem_bot] at hcent
  simpa using congrArg Subtype.val hcent

theorem dvd_card_factor {m : ℕ} (hK : Nat.card S.K = 2 ^ m) (hm : m = 2 ∨ m = 3) (j : Fin 2) :
    3 ∣ Nat.card ↥(S.factor j) ∧ (2 ^ m - 1) ∣ Nat.card ↥(S.factor j) ∧
      ¬ (2 ^ m - 1) ^ 2 ∣ Nat.card ↥(S.factor j) := by
  rcases hm with rfl | rfl
  · rw [card_factor S j, hK]
    norm_num
  · rw [card_factor S j, hK]
    norm_num

end OmegaModel

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
