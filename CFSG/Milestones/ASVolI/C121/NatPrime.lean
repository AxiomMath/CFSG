module

public import CFSG.Milestones.ASVolI.C121.J
public import CFSG.Quasithin.Background.B610

public section

namespace CFSG.ASVolI

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChC CFSG.LieType.BorelTits
open scoped MatrixGroups

variable {Ω : Type} [Group Ω]

theorem burnsideC121_conj_mul_inv_mem {Y W : Subgroup Ω} {k v : Ω} (hk : k ∈ Y) (hv : v ∈ W) :
    k * v * k⁻¹ * v⁻¹ ∈ ⁅W, Y⁆ := by
  rw [Subgroup.commutator_comm]
  exact Subgroup.commutator_mem_commutator hk hv

theorem burnsideC121_commutator_le {Y W : Subgroup Ω} (hYW : Y ≤ Subgroup.normalizer (W : Set Ω)) :
    ⁅W, Y⁆ ≤ W :=
  Subgroup.le_normalizer_iff_commutator_le_left.mp hYW

namespace burnsideC121_NatD

variable {Y W : Subgroup Ω} {n : ℕ} {F : Type} [Field F] [Fintype F]
  (D : burnsideC121_NatD Y W n F)

theorem beta_comm (hYW : Y ≤ Subgroup.normalizer (W : Set Ω)) (k : ↥Y) (v : ↥W) :
    Multiplicative.toAdd (D.β ⟨(k : Ω) * v * (k : Ω)⁻¹ * (v : Ω)⁻¹,
        burnsideC121_commutator_le hYW (burnsideC121_conj_mul_inv_mem k.2 v.2)⟩) =
      (D.α k : Matrix (Fin 2) (Fin 2) F).mulVec (Multiplicative.toAdd (D.β v)) -
        Multiplicative.toAdd (D.β v) := by
  have hkv : (k : Ω) * v * (k : Ω)⁻¹ ∈ W := (Subgroup.mem_normalizer_iff.mp (hYW k.2) v).mp v.2
  have e1 : (⟨(k : Ω) * v * (k : Ω)⁻¹ * (v : Ω)⁻¹,
      burnsideC121_commutator_le hYW (burnsideC121_conj_mul_inv_mem k.2 v.2)⟩ : ↥W) =
      ⟨_, hkv⟩ * v⁻¹ := rfl
  rw [e1, map_mul, map_inv, toAdd_mul, toAdd_inv, D.βe k v ⟨_, hkv⟩ rfl, sub_eq_add_neg]

theorem exists_commutator_beta (hYW : Y ≤ Subgroup.normalizer (W : Set Ω)) (hn : 2 ≤ n)
    (x : Fin 2 → F) :
    ∃ u : ↥W, (u : Ω) ∈ ⁅W, Y⁆ ∧ Multiplicative.toAdd (D.β u) = x := by
  have h4 : 4 ≤ Nat.card F := by
    rw [Nat.card_eq_fintype_card, D.card]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have hαs : Function.Surjective D.α := by
    rw [← MonoidHom.range_eq_top, D.αr, CFSG.Quasithin.C126.Nat.commutator_sl2_eq_top h4]
  obtain ⟨v₁, hv₁⟩ := D.βs (Multiplicative.ofAdd ![0, x 0])
  obtain ⟨v₂, hv₂⟩ := D.βs (Multiplicative.ofAdd ![x 1, 0])
  obtain ⟨a₁, ha₁⟩ := hαs (CFSG.Quasithin.SL2Model.e12 1)
  obtain ⟨a₂, ha₂⟩ := hαs (CFSG.Quasithin.SL2Model.e21 1)
  refine ⟨⟨_, burnsideC121_commutator_le hYW (burnsideC121_conj_mul_inv_mem a₁.2 v₁.2)⟩ *
    ⟨_, burnsideC121_commutator_le hYW (burnsideC121_conj_mul_inv_mem a₂.2 v₂.2)⟩, ?_, ?_⟩
  · exact Subgroup.mul_mem _ (burnsideC121_conj_mul_inv_mem a₁.2 v₁.2)
      (burnsideC121_conj_mul_inv_mem a₂.2 v₂.2)
  · rw [map_mul, toAdd_mul, D.beta_comm hYW, D.beta_comm hYW, hv₁, hv₂, ha₁, ha₂,
      CFSG.Quasithin.SL2Model.e12_coe, CFSG.Quasithin.SL2Model.e21_coe, toAdd_ofAdd, toAdd_ofAdd]
    funext i
    fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.vecHead, Matrix.vecTail]

end burnsideC121_NatD

namespace burnsideC121_YCtx

variable [Finite Ω] {X R T Y W : Subgroup Ω}
  (c : burnsideC121_YCtx X R T Y W) {n : ℕ} {F : Type} [Field F] [Fintype F]
  (D : burnsideC121_NatD Y W n F)

include c D

theorem isNaturalL2Prime (hn : 2 ≤ n) : IsNaturalL2Prime n Y W := by
  have h4 : 4 ≤ Nat.card F := by
    rw [Nat.card_eq_fintype_card, D.card]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have hαs : Function.Surjective D.α := by
    rw [← MonoidHom.range_eq_top, D.αr, CFSG.Quasithin.C126.Nat.commutator_sl2_eq_top h4]
  have hYW := c.Y_le_normalizer_W
  have hUW : ⁅W, Y⁆ ≤ W := burnsideC121_commutator_le hYW
  let ε := CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 2 F
  let α' : ↥Y →* ↥(StatedSL 2 F) := ε.toMonoidHom.comp D.α
  let ι : ↥⁅W, Y⁆ →* ↥W := Subgroup.inclusion hUW
  let β' : ↥⁅W, Y⁆ →* Multiplicative (Fin 2 → F) := D.β.comp ι
  refine Or.inl ⟨by omega, F, inferInstance, inferInstance, D.card,
    Subgroup.normalizer_commutator_ge_right W Y, α', ?_, ?_, β', ?_, ?_, ?_⟩
  · exact ε.surjective.comp hαs
  · ext k
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, c.inf_centralizer_W D]
    show ε (D.α k) = 1 ↔ _
    rw [MulEquiv.map_eq_one_iff, ← MonoidHom.mem_ker, D.αk, Subgroup.mem_subgroupOf]
  · intro x
    obtain ⟨u, hu, hβ⟩ := D.exists_commutator_beta hYW hn (Multiplicative.toAdd x)
    exact ⟨⟨u, hu⟩, hβ⟩
  · ext u
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    show D.β (ι u) = 1 ↔ _
    rw [← MonoidHom.mem_ker, D.βk, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    exact ⟨fun h => ⟨u.2, h.2⟩, fun h => ⟨hUW u.2, h.2⟩⟩
  · intro a u v huv
    exact D.βe a (ι u) (ι v) huv

end burnsideC121_YCtx

end CFSG.ASVolI
