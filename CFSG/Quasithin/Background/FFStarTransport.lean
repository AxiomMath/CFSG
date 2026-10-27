module

public import CFSG.Quasithin.Background.FixVTransport

public section

namespace CFSG.Quasithin

variable {W W' : Type*} [CommGroup W] [CommGroup W']

theorem isFFStarOffender_map_congr_equiv_iff (φ : W ≃* W') {X A : Subgroup (MulAut W)} :
    IsFFStarOffender (X.map (MulAut.congr φ).toMonoidHom) (A.map (MulAut.congr φ).toMonoidHom) ↔
      IsFFStarOffender X A := by
  refine ⟨fun h => ?_, isFFStarOffender_map_congr_equiv φ⟩
  have hid : ((MulAut.congr φ.symm).toMonoidHom.comp (MulAut.congr φ).toMonoidHom) =
      MonoidHom.id (MulAut W) := by
    ext x w
    simp [MulAut.congr_apply]
  have := isFFStarOffender_map_congr_equiv φ.symm h
  rwa [Subgroup.map_map, Subgroup.map_map, hid, Subgroup.map_id, Subgroup.map_id] at this

theorem isFFStarOffender_map_conj {X A : Subgroup (MulAut W)} (h : IsFFStarOffender X A)
    {g : MulAut W} (hg : g ∈ X) : IsFFStarOffender X (A.map (MulAut.conj g).toMonoidHom) := by
  obtain ⟨hAX, hA1, ⟨hcomm, hsq⟩, hoff⟩ := h
  have hinj : Function.Injective (MulAut.conj g).toMonoidHom := (MulAut.conj g).injective
  have hcard : ∀ B : Subgroup (MulAut W), Nat.card (B.map (MulAut.conj g).toMonoidHom) *
      Nat.card (fixV (B.map (MulAut.conj g).toMonoidHom)) = Nat.card B * Nat.card (fixV B) :=
    fun B => by
      rw [fixV_map_conj_eq, Subgroup.card_map_of_injective hinj,
        Subgroup.card_map_of_injective g.injective]
  refine ⟨?_, fun h0 => hA1 ((Subgroup.map_eq_bot_iff_of_injective _ hinj).1 h0), ⟨?_, ?_⟩,
    fun B hB => ?_⟩
  · rintro _ ⟨a, ha, rfl⟩
    exact X.mul_mem (X.mul_mem hg (hAX ha)) (X.inv_mem hg)
  · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    rw [← map_mul, ← map_mul, hcomm a ha b hb]
  · rintro _ ⟨a, ha, rfl⟩
    rw [← map_pow, hsq a ha, map_one]
  · have hB' : (B.comap (MulAut.conj g).toMonoidHom).map (MulAut.conj g).toMonoidHom = B :=
      Subgroup.map_comap_eq_self_of_surjective (MulAut.conj g).surjective B
    rw [← hB', hcard, hcard]
    exact hoff _ fun x hx => by
      obtain ⟨a, ha, hax⟩ := Subgroup.mem_map.1 (hB (Subgroup.mem_comap.1 hx))
      exact hinj hax ▸ ha

end CFSG.Quasithin
