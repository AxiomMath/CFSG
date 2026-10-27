module

public import CFSG.LocalAnalysis.QuasithinUnique.PushingUp.C1Blocks

public section

namespace CFSG.Quasithin.C124

open CFSG.QuasithinUnique CFSG.QuasithinUnique.C1 Subgroup
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem blockZ_eq_bot_of_surj (hL : IsShort2 L) {y : G} (hy : y ∈ L)
    (hc : ∀ l ∈ L, y * l * y⁻¹ * l⁻¹ ∈ blockQ L)
    (hs : ∀ u ∈ blockU L, ∃ u₁ ∈ blockU L, (y * u₁ * y⁻¹ * u₁⁻¹)⁻¹ * u ∈ blockZ L) :
    blockZ L = ⊥ := by
  have hyU : y ∈ normalizer (blockU L : Set G) := le_normalizer_blockU L hy
  have hUab := (elemAb2_blockU hL).1
  have hθ : ∀ v ∈ blockU L, y * v * y⁻¹ * v⁻¹ ∈ blockU L := fun v hv =>
    mul_mem ((mem_normalizer_iff.mp hyU v).mp hv) (inv_mem hv)
  have hZc : ∀ z ∈ blockZ L, ∀ l ∈ L, l * z = z * l := fun z hz l hl =>
    mem_centralizer_iff.mp hz.2 l hl
  let W : Subgroup G :=
    { carrier := {w | ∃ u ∈ blockU L, w = y * u * y⁻¹ * u⁻¹}
      mul_mem' := by
        rintro _ _ ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
        exact ⟨a * b, mul_mem ha hb, (commutator_mul_of_comm hUab hyU ha hb).symm⟩
      one_mem' := ⟨1, one_mem _, by simp⟩
      inv_mem' := by
        rintro _ ⟨a, ha, rfl⟩
        exact ⟨a⁻¹, inv_mem ha, (commutator_inv_of_comm hUab hyU ha).symm⟩ }
  have hWL : ∀ l ∈ L, ∀ w ∈ W, l * w * l⁻¹ ∈ W := by
    rintro l hl _ ⟨u, hu, rfl⟩
    refine ⟨l * u * l⁻¹, (mem_normalizer_iff.mp (le_normalizer_blockU L hl) u).mp hu, ?_⟩
    exact (commutator_conj_blockU hL hyU hl (hc l hl) hu).symm
  have hcomm : ⁅blockU L, L⁆ ≤ W := by
    rw [commutator_le]
    intro u hu l hl
    obtain ⟨u₁, hu₁, hz⟩ := hs u hu
    set w := y * u₁ * y⁻¹ * u₁⁻¹ with hw
    have hwW : w ∈ W := ⟨u₁, hu₁, rfl⟩
    have hzl : (w⁻¹ * u) * l * (w⁻¹ * u)⁻¹ = l := by
      rw [← hZc _ hz l hl]
      group
    have e : ⁅u, l⁆ = w * (l * w⁻¹ * l⁻¹) := by
      rw [commutatorElement_def]
      calc u * l * u⁻¹ * l⁻¹ = w * ((w⁻¹ * u) * l * (w⁻¹ * u)⁻¹) * w⁻¹ * l⁻¹ := by group
        _ = w * l * w⁻¹ * l⁻¹ := by rw [hzl]
        _ = w * (l * w⁻¹ * l⁻¹) := by group
    rw [e]
    exact mul_mem hwW (hWL l hl w⁻¹ (inv_mem hwW))
  have hUW : blockU L ≤ W := (commutator_blockU hL).ge.trans hcomm
  let f : ↥(blockU L) → ↥(blockU L) := fun u => ⟨y * u * y⁻¹ * u⁻¹, hθ u u.2⟩
  have hfs : Function.Surjective f := by
    rintro ⟨v, hv⟩
    obtain ⟨u, hu, rfl⟩ := hUW hv
    exact ⟨⟨u, hu⟩, rfl⟩
  have hfi : Function.Injective f := Finite.injective_iff_surjective.2 hfs
  refine (eq_bot_iff_forall _).2 fun z hz => ?_
  have hz1 : f ⟨z, hz.1⟩ = f 1 := by
    apply Subtype.ext
    show y * z * y⁻¹ * z⁻¹ = y * 1 * y⁻¹ * 1⁻¹
    rw [hZc z hz y hy]
    group
  exact congrArg Subtype.val (hfi hz1)

end CFSG.Quasithin.C124
