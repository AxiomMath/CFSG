module

public import CFSG.Quasithin.Background.B2FactorizationBridge

public section

namespace CFSG.Quasithin

open CFSG.Open

namespace ConvI

variable {G : Type*} [Group G] {V : Subgroup G} (hV : IsElemAbelian 2 V)

theorem convI_comm_iff {a b : G} (ha : a ∈ Subgroup.normalizer (V : Set G))
    (hb : b ∈ Subgroup.normalizer (V : Set G)) :
    convI hV ⟨a, ha⟩ * convI hV ⟨b, hb⟩ = convI hV ⟨b, hb⟩ * convI hV ⟨a, ha⟩ ↔
      a * b * a⁻¹ * b⁻¹ ∈ Subgroup.centralizer (V : Set G) := by
  rw [← convI_eq_one_iff hV ⟨a * b * a⁻¹ * b⁻¹, (Subgroup.normalizer (V : Set G)).mul_mem
    ((Subgroup.normalizer (V : Set G)).mul_mem ((Subgroup.normalizer (V : Set G)).mul_mem ha hb)
      ((Subgroup.normalizer (V : Set G)).inv_mem ha)) ((Subgroup.normalizer (V : Set G)).inv_mem hb)⟩]
  have e : (⟨a * b * a⁻¹ * b⁻¹, (Subgroup.normalizer (V : Set G)).mul_mem
    ((Subgroup.normalizer (V : Set G)).mul_mem ((Subgroup.normalizer (V : Set G)).mul_mem ha hb)
      ((Subgroup.normalizer (V : Set G)).inv_mem ha)) ((Subgroup.normalizer (V : Set G)).inv_mem hb)⟩ :
        ↥(Subgroup.normalizer (V : Set G))) =
      ⟨a, ha⟩ * ⟨b, hb⟩ * ⟨a, ha⟩⁻¹ * ⟨b, hb⟩⁻¹ := rfl
  rw [e, map_mul, map_mul, map_mul, map_inv, map_inv]
  constructor
  · intro h
    rw [h]; group
  · intro h
    have h1 := congrArg (fun x => x * (convI hV ⟨b, hb⟩ * convI hV ⟨a, ha⟩)) h
    simp only [one_mul] at h1
    calc convI hV ⟨a, ha⟩ * convI hV ⟨b, hb⟩
        = convI hV ⟨a, ha⟩ * convI hV ⟨b, hb⟩ * (convI hV ⟨a, ha⟩)⁻¹ * (convI hV ⟨b, hb⟩)⁻¹ *
            (convI hV ⟨b, hb⟩ * convI hV ⟨a, ha⟩) := by group
      _ = convI hV ⟨b, hb⟩ * convI hV ⟨a, ha⟩ := by rw [h, one_mul]

end ConvI

end CFSG.Quasithin
