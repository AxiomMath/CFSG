module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.AppCStd
public import CFSG.Milestones.ASVolI.C61.PAppC54

public section

namespace CFSG.QuasithinUnique.burnsideC56_P.AppC

open CFSG.QuasithinUnique.AppC

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.A5.Delta5 Equiv

variable {G : Type} [Group G] [Finite G]

theorem a5_core_std {T M H S L : Subgroup G} (hcs : burnsideC56_CS G T M H S L)
    (hj : conjJoin S L = L) (P : A5Pi L) :
    ∃ P' : A5Pi L, P'.im (thompsonJ S) = Estd ∧ P'.im (baum S) = Estd ∧ P'.im S = Dstd ∧
      P'.im (L ⊔ baum S) = ⊤ := by
  obtain ⟨τ₁, τ₂, hτ₁, hτ₂, hdisj, hJeq, hBeq, hD8, -, htop, hJn, -⟩ := a5_core hcs hj P
  obtain ⟨ρ, hρ1, hρ2⟩ := swaps_conj τ₁ τ₂ hτ₁ hτ₂ hdisj
  have hcl : (Subgroup.closure ({τ₁, τ₂} : Set (Perm (Fin 5)))).map (MulAut.conj ρ).toMonoidHom =
      Estd := by
    rw [MonoidHom.map_closure, ← closure_swaps]
    congr 1
    ext g
    simp only [Set.mem_image, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨x, rfl | rfl, rfl⟩
      · exact Or.inl hρ1
      · exact Or.inr hρ2
    · rintro (rfl | rfl)
      · exact ⟨τ₁, Or.inl rfl, hρ1⟩
      · exact ⟨τ₂, Or.inr rfl, hρ2⟩
  have hJ' : (P.conj ρ).im (thompsonJ S) = Estd := by rw [A5Pi.im_conj, hJeq, hcl]
  have hB' : (P.conj ρ).im (baum S) = Estd := by rw [A5Pi.im_conj, hBeq, hcl]
  have hnorm' : ∀ d ∈ (P.conj ρ).im S, ∀ j ∈ (P.conj ρ).im (thompsonJ S),
      d * j * d⁻¹ ∈ (P.conj ρ).im (thompsonJ S) := by
    intro d hd j hj'
    rw [A5Pi.im_conj] at hd hj' ⊢
    obtain ⟨d₀, hd₀, rfl⟩ := Subgroup.mem_map.1 hd
    obtain ⟨j₀, hj₀, rfl⟩ := Subgroup.mem_map.1 hj'
    refine Subgroup.mem_map.2 ⟨d₀ * j₀ * d₀⁻¹, hJn d₀ hd₀ j₀ hj₀, ?_⟩
    simp [MulAut.conj_apply, mul_assoc]
  have hle : (P.conj ρ).im S ≤ Dstd := by
    intro d hd
    rw [mem_Dstd, mem_Dset]
    intro x hx
    have := hnorm' d hd x (by rw [hJ']; exact hx)
    rwa [hJ'] at this
  have hcard : Nat.card ((P.conj ρ).im S) = 8 := by
    rw [A5Pi.im_conj, Subgroup.card_map_of_injective (MulAut.conj ρ).injective, hD8]
  refine ⟨P.conj ρ, hJ', hB', ?_, ?_⟩
  · exact Subgroup.eq_of_le_of_card_ge hle (by rw [Dstd_card, hcard])
  · rw [A5Pi.im_conj, htop, Subgroup.map_top_of_surjective _ (MulAut.conj ρ).surjective]

end CFSG.QuasithinUnique.burnsideC56_P.AppC
