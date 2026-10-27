module

public import CFSG.RankThree.PartOne.KF.R56Final
public import CFSG.RankThree.PartOne.KF.U4Model
public import CFSG.LinearAlgebra.SL2MinimalFaithfulMatrix
public import CFSG.RankThree.SteinbergR3ECALinearSplitBlocks

public section

namespace CFSG.RankThree.PartOne.U4F

open Matrix CFSG CFSG.LieType.Universal.Unitary CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KFU
  CFSG.Assembly.LowTwoRank
open CFSG.LieType.BorelTits (unitaryInvolution unitaryInvolution_involutive)

theorem charP_two_of_card {L : Type} [Field L] [Finite L] {m : ℕ} (h : Nat.card L = 2 ^ m) :
    CharP L 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := Fintype.ofFinite L
  exact charP_of_card_eq_prime_pow (p := 2) (f := m) (by rwa [← Nat.card_eq_fintype_card])

variable {K : Type} [Field K] [Finite K] [CharP K 2] {f : ℕ}

theorem suQ_injective (hf : 1 ≤ f) (hK : Nat.card K = (2 ^ f) ^ 2) :
    Function.Injective (suQ (K := K) (f := f) 4 hK) := by
  rw [← MonoidHom.ker_eq_bot_iff]
  have hker : (suQ (K := K) (f := f) 4 hK).ker =
      ((StatedScalars (Fin 4) K).subgroupOf (StatedSU 4 (2 ^ f) K)).comap
        (equivStatedSU hK 4).toMonoidHom := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_comap]
    exact QuotientGroup.eq_one_iff _
  have hcard : Nat.card ((StatedScalars (Fin 4) K).subgroupOf (StatedSU 4 (2 ^ f) K)) = 1 := by
    rw [(CFSG.LinearGroups.unitary_scalar_kernel Nat.prime_two hK (by norm_num : 1 ≤ 4)).2.2]
    have hodd : Odd (2 ^ f + 1) := (Nat.even_pow.2 ⟨even_two, by omega⟩).add_one
    have h2 : Nat.Coprime 2 (2 ^ f + 1) := Nat.coprime_two_left.2 hodd
    simpa using Nat.Coprime.pow_left 2 h2
  have hbot : (StatedScalars (Fin 4) K).subgroupOf (StatedSU 4 (2 ^ f) K) = ⊥ :=
    Subgroup.eq_bot_of_card_eq _ hcard
  rw [hker, hbot, MonoidHom.comap_bot]
  exact (MonoidHom.ker_eq_bot_iff _).2 (equivStatedSU hK 4).injective

theorem suQ_surjective (hK : Nat.card K = (2 ^ f) ^ 2) :
    Function.Surjective (suQ (K := K) (f := f) 4 hK) :=
  (QuotientGroup.mk'_surjective _).comp (equivStatedSU hK 4).surjective

theorem exists_su_equiv {G : Type} [Group G] {U : Subgroup G} (hf : 1 ≤ f)
    (hU : StatedClassicalModel U .PSU 4 2 f) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K 2), Nat.card K = (2 ^ f) ^ 2 ∧
      Nonempty (↥U ≃* ↥(SU (unitaryInvolution K 2 f) 4)) := by
  obtain ⟨-, K, hKf, hKfin, hK, ⟨e⟩⟩ := hU
  have hchar : CharP K 2 := charP_two_of_card (m := 2 * f) (by rw [hK, ← pow_mul, mul_comm])
  refine ⟨K, hKf, hKfin, hchar, hK, ⟨?_⟩⟩
  exact e.trans (MulEquiv.ofBijective (suQ 4 hK) ⟨suQ_injective hf hK, suQ_surjective hK⟩).symm

theorem exists_equiv_SL2_of_model {X : Type} [Group X] {a : ℕ}
    (h : StatedClassicalModel X .PSL 2 2 a) :
    ∃ (L : Type) (_ : Field L) (_ : Finite L), Nat.card L = 2 ^ a ∧ 2 ≤ a ∧
      Nonempty (X ≃* SpecialLinearGroup (Fin 2) L) := by
  obtain ⟨hadm, L, hL, hLfin, hcard, ⟨e⟩⟩ := h
  obtain ⟨-, hf1, -, h22, -⟩ := hadm
  have ha2 : 2 ≤ a := by
    by_contra hlt
    have : a = 1 := by omega
    subst this
    exact h22 rfl
  have hchar : CharP L 2 := charP_two_of_card hcard
  obtain ⟨e'⟩ := nonempty_SL2_mulEquiv_statedProj (F := L)
  exact ⟨L, hL, hLfin, hcard, ha2, ⟨e.trans e'.symm⟩⟩

theorem perfect_card_of_equiv_SL2 {X : Type} [Group X] {L : Type} [Field L] [Finite L] {a : ℕ}
    (hL : Nat.card L = 2 ^ a) (ha : 2 ≤ a) (e : X ≃* SpecialLinearGroup (Fin 2) L) :
    Group.IsPerfect X ∧ Nat.card X = 2 ^ a * ((2 ^ a) ^ 2 - 1) := by
  have h4 : 4 ≤ Nat.card L := by
    rw [hL]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ a := Nat.pow_le_pow_right (by norm_num) ha
  refine ⟨?_, ?_⟩
  · have := (CFSG.RankThree.CALinearPlane.isQuasisimple_SL_of_two_le (k := L) (m := 2) le_rfl
      h4).1
    exact Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  · rw [Nat.card_congr e.toEquiv, CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two, hL]

theorem exists_mul_of_mem_sup {G : Type*} [Group G] {X Y F : Subgroup G} (hX : X ≤ F) (hY : Y ≤ F)
    (hF : ∀ a ∈ F, ∀ b ∈ F, a * b = b * a) {x : G} (hx : x ∈ X ⊔ Y) :
    ∃ c ∈ X, ∃ k ∈ Y, x = c * k := by
  rw [Subgroup.sup_eq_closure] at hx
  refine Subgroup.closure_induction (p := fun x _ => ∃ c ∈ X, ∃ k ∈ Y, x = c * k) ?_ ?_ ?_ ?_ hx
  · rintro y (hy | hy)
    · exact ⟨y, hy, 1, Y.one_mem, (mul_one y).symm⟩
    · exact ⟨1, X.one_mem, y, hy, (one_mul y).symm⟩
  · exact ⟨1, X.one_mem, 1, Y.one_mem, (mul_one 1).symm⟩
  · rintro _ _ _ _ ⟨c₁, hc₁, k₁, hk₁, rfl⟩ ⟨c₂, hc₂, k₂, hk₂, rfl⟩
    refine ⟨c₁ * c₂, X.mul_mem hc₁ hc₂, k₁ * k₂, Y.mul_mem hk₁ hk₂, ?_⟩
    have := hF k₁ (hY hk₁) c₂ (hX hc₂)
    calc c₁ * k₁ * (c₂ * k₂) = c₁ * (k₁ * c₂) * k₂ := by group
      _ = c₁ * (c₂ * k₁) * k₂ := by rw [this]
      _ = c₁ * c₂ * (k₁ * k₂) := by group
  · rintro _ _ ⟨c, hc, k, hk, rfl⟩
    refine ⟨c⁻¹, X.inv_mem hc, k⁻¹, Y.inv_mem hk, ?_⟩
    have := hF k (hY hk) c (hX hc)
    calc (c * k)⁻¹ = (k * c)⁻¹ := by rw [this]
      _ = c⁻¹ * k⁻¹ := _root_.mul_inv_rev k c

end CFSG.RankThree.PartOne.U4F
