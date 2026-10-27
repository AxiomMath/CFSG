module

public import CFSG.Quasithin.EmptyFaithful.ModEAut
public import CFSG.Quasithin.Background.F6GoldschmidtList
public import CFSG.Quasithin.Background.F6Basic

public section

namespace CFSG.Quasithin.ModE

open CFSG.Quasithin CFSG.Quasithin.F6 CFSG.Open CFSG.ComponentClassification.M12Cover

theorem four_of_autM12
    {D : Type} [Group D] [Finite D] (hD : IsAutM12 D) {G₁ G₂ : Subgroup D}
    (hGT : IsGoldschmidtTriple G₁ G₂) {z : D} {A : Subgroup D} (hz1 : z ≠ 1) (hz2 : z ^ 2 = 1)
    (hzG : z ∈ G₁ ⊓ G₂) (hzc : ∀ t ∈ G₁ ⊓ G₂, t * z = z * t)
    (hcent : G₂ ≤ Subgroup.centralizer ({z} : Set D)) (hAG : A ≤ G₂) (hAel : IsElemAbelian 2 A)
    (hAnorm : G₂ ≤ Subgroup.normalizer (A : Set D)) (hAcard : 2 ^ 4 ≤ Nat.card A) : False := by
  obtain ⟨e⟩ := hD
  let ψ : D ≃* autModel := e.trans autModelEquiv.symm
  let ι : D →* P24 := autModel.subtype.comp ψ.toMonoidHom
  have hι : Function.Injective ι := fun x y h => ψ.injective (Subtype.ext h)
  have hιmem : ∀ x, ι x ∈ autModel := fun x => (ψ x).2
  have hcardD : Nat.card D = 190080 := by
    rw [Nat.card_congr ψ.toEquiv, card_autModel]
  have hTcard : Nat.card (G₁ ⊓ G₂ : Subgroup D) = 128 := by
    obtain ⟨P, hP⟩ := hGT.sylow
    rw [← hP, Sylow.card_eq_multiplicity, hcardD, fac_190080]
    norm_num
  refine conc_four ((G₁ ⊓ G₂).map ι) (G₂.map ι) (A.map ι) (ι z) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · rintro _ ⟨t, _, rfl⟩
    exact hιmem t
  · rw [Subgroup.card_map_of_injective hι, hTcard]
  · rintro _ ⟨t, _, rfl⟩
    exact hιmem t
  · exact Subgroup.map_mono inf_le_right
  · rw [Subgroup.relIndex_map_map_of_injective _ _ hι]
    exact hGT.relIndex_inf_right
  · intro h
    exact hz1 (hι (h.trans (map_one ι).symm))
  · rw [← map_mul, ← pow_two, hz2, map_one]
  · exact Subgroup.mem_map_of_mem ι hzG
  · rintro _ ⟨t, ht, rfl⟩
    rw [← map_mul, ← map_mul, hzc t ht]
  · rintro _ ⟨g, hg, rfl⟩
    have := (Subgroup.mem_centralizer_iff.1 (hcent hg)) z rfl
    rw [← map_mul, ← map_mul, this]
  · exact Subgroup.map_mono hAG
  · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    have h := congrArg Subtype.val (hAel.1.is_comm.comm (⟨a, ha⟩ : A) ⟨b, hb⟩)
    rw [← map_mul, ← map_mul]
    exact congrArg ι h
  · rintro _ ⟨a, ha, rfl⟩
    rw [← map_mul, ← pow_two, hAel.2 a ha, map_one]
  · rintro _ ⟨g, hg, rfl⟩ _ ⟨a, ha, rfl⟩
    refine ⟨g * a * g⁻¹, ?_, ?_⟩
    · exact (Subgroup.mem_normalizer_iff.1 (hAnorm hg) a).1 ha
    · rw [map_mul, map_mul, map_inv]
  · rw [Subgroup.card_map_of_injective hι]
    exact hAcard.trans' (by norm_num)

end CFSG.Quasithin.ModE
