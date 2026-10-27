module

public import CFSG.Quasithin.Recognition.St84.Gen.U4qAmalForm
public import CFSG.Quasithin.Recognition.St84.Gen.U4qAmalDefs
import CFSG.Quasithin.Recognition.St84.Gen.U4qAmalLocal

public section

namespace CFSG.Quasithin.F112R.St84

open Matrix CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {L1 L2 S : Subgroup G} {f : ℕ}

private theorem centerOf_eq_map_center_subtype (Q : Subgroup G) :
    centerOf Q = (Subgroup.center ↥Q).map Q.subtype := by
  ext z
  constructor
  · intro hz
    exact ⟨⟨z, hz.1⟩, Subgroup.mem_center_iff.mpr fun g =>
      Subtype.ext (Subgroup.mem_centralizer_iff.mp hz.2 g g.2), rfl⟩
  · rintro ⟨z', hz', rfl⟩
    exact ⟨z'.2, Subgroup.mem_centralizer_iff.mpr fun y hy =>
      congrArg Subtype.val (Subgroup.mem_center_iff.mp hz' ⟨y, hy⟩)⟩

private theorem U4qLocalData.card_centerOf_pCoreOf_left (hD : U4qLocalData L1 L2 S f) :
    Nat.card (centerOf (pCoreOf 2 L1)) = 2 ^ f := by
  rw [centerOf_eq_map_center_subtype,
    Subgroup.card_map_of_injective (pCoreOf 2 L1).subtype_injective]
  exact hD.special_left.2.2

private theorem U4qLocalData.commutator_eq_center_pCoreOf_left (hD : U4qLocalData L1 L2 S f) :
    commutator ↥(pCoreOf 2 L1) = Subgroup.center ↥(pCoreOf 2 L1) := by
  rcases hD.special_left.1.2 with ⟨hab, -⟩ | ⟨hc, -, -⟩
  · exfalso
    have hcen : Subgroup.center ↥(pCoreOf 2 L1) = ⊤ :=
      (Subgroup.eq_top_iff' _).mpr fun x =>
        Subgroup.mem_center_iff.mpr fun g => hab.is_comm.comm g x
    have hZ := hD.special_left.2.2
    rw [hcen, Subgroup.card_top, hD.special_left.2.1] at hZ
    have hf := hD.one_le
    have hlt : 2 ^ f < (2 ^ f) ^ (1 + 2 * 2) := by
      calc 2 ^ f = (2 ^ f) ^ 1 := (pow_one _).symm
        _ < (2 ^ f) ^ (1 + 2 * 2) :=
          Nat.pow_lt_pow_right (Nat.one_lt_two_pow (by omega)) (by norm_num)
    omega
  · exact hc

private theorem U4qLocalData.centerOf_le_commutator_left (hD : U4qLocalData L1 L2 S f) :
    centerOf (pCoreOf 2 L1) ≤ ⁅pCoreOf 2 L1, pCoreOf 2 L1⁆ := by
  intro z hz
  have hzc : (⟨z, hz.1⟩ : ↥(pCoreOf 2 L1)) ∈ commutator ↥(pCoreOf 2 L1) := by
    rw [hD.commutator_eq_center_pCoreOf_left]
    exact Subgroup.mem_center_iff.mpr fun y =>
      Subtype.ext (Subgroup.mem_centralizer_iff.mp hz.2 y y.2)
  have key : commutator ↥(pCoreOf 2 L1) ≤
      (⁅pCoreOf 2 L1, pCoreOf 2 L1⁆).comap (pCoreOf 2 L1).subtype := by
    rw [commutator_def, Subgroup.commutator_le]
    intro a _ b _
    exact Subgroup.commutator_mem_commutator a.2 b.2
  exact key hzc

private theorem U4qLocalData.mul_self_eq_one_of_mem_centerOf (hD : U4qLocalData L1 L2 S f) :
    ∀ z ∈ centerOf (pCoreOf 2 L1), z * z = 1 := by
  intro z hz
  have hz' : (⟨z, hz.1⟩ : ↥(pCoreOf 2 L1)) ∈ Subgroup.center ↥(pCoreOf 2 L1) :=
    Subgroup.mem_center_iff.mpr fun g =>
      Subtype.ext (Subgroup.mem_centralizer_iff.mp hz.2 g g.2)
  have h2 : (⟨z, hz.1⟩ : ↥(pCoreOf 2 L1)) ^ 2 = 1 := by
    rcases hD.special_left.1.2 with ⟨-, h⟩ | ⟨-, -, h⟩
    · exact h _
    · exact h _ hz'
  have h3 := congrArg Subtype.val h2
  simpa [pow_two] using h3

theorem U4qLocalData.exists_pointFormData (hD : U4qLocalData L1 L2 S f) {F : Type*} [Field F]
    [Finite F] [CharP F 2] (hFcard : Nat.card F = 2 ^ f)
    (α : L1 →* SpecialLinearGroup (Fin 2) F) (hα : Function.Surjective α)
    (β : ↥(pCoreOf 2 L1) →* Multiplicative (Matrix (Fin 2) (Fin 2) F))
    (hβ : Function.Surjective β)
    (hβker : β.ker = (centerOf (pCoreOf 2 L1)).subgroupOf (pCoreOf 2 L1))
    (hβconj : ∀ (ℓ : L1) (u v : ↥(pCoreOf 2 L1)), (v : G) = ℓ * u * ℓ⁻¹ →
      Multiplicative.toAdd (β v) = (α ℓ : Matrix (Fin 2) (Fin 2) F) * Multiplicative.toAdd (β u))
    (v₀ : Fin 2 → F) (hv₀ : v₀ ≠ 0)
    (hpure : ∀ u : ↥(pCoreOf 2 L1),
      (∃ m : Fin 2 → F, Multiplicative.toAdd (β u) = vecMulVec v₀ m) → (u : G) * u = 1) :
    ∃ D : PointFormData (pCoreOf 2 L1) (centerOf (pCoreOf 2 L1)) L1 F, D.α = α ∧ D.β = β := by
  have hZQ : centerOf (pCoreOf 2 L1) ≤ pCoreOf 2 L1 := inf_le_left
  have hZc : pCoreOf 2 L1 ≤ Subgroup.centralizer (centerOf (pCoreOf 2 L1) : Set G) :=
    Subgroup.le_centralizer_iff.mp inf_le_right
  obtain ⟨ζ, hζZ, hsq, hcomm⟩ := CFSG.Quasithin.F112R.St84.exists_sq_eq_det hZQ hZc
    hD.mul_self_eq_one_of_mem_centerOf (le_normalizer_pCoreOf 2 L1) hD.center_left α hα β hβ
    hβker hβconj v₀ hv₀ hpure
  obtain ⟨hinj, hrange⟩ := injective_and_range_eq_of_commutator_mem ζ hζZ
    (fun u v => ⟨_, (hcomm u v).symm⟩) hD.centerOf_le_commutator_left
    (by rw [hD.card_centerOf_pCoreOf_left, hFcard])
  exact ⟨⟨α, hα, β, hβ, hβker, hβconj, ζ, hinj, hrange, hsq, hcomm⟩, rfl, rfl⟩

end CFSG.Quasithin.F112R.St84

end
