module

public import CFSG.Quasithin.Background.Module

public section

namespace CFSG.Quasithin

variable {W W' : Type*} [CommGroup W] [CommGroup W']

theorem mem_fixV_map_congr_equiv (φ : W ≃* W') (X : Subgroup (MulAut W)) (w : W') :
    w ∈ fixV (X.map (MulAut.congr φ).toMonoidHom) ↔ φ.symm w ∈ fixV X := by
  constructor
  · intro hw x hx
    have h1 : φ (x (φ.symm w)) = w := hw (MulAut.congr φ x) ⟨x, hx, rfl⟩
    calc x (φ.symm w) = φ.symm (φ (x (φ.symm w))) := (φ.symm_apply_apply _).symm
      _ = φ.symm w := by rw [h1]
  · rintro hv _ ⟨x, hx, rfl⟩
    show φ (x (φ.symm w)) = w
    rw [hv x hx, φ.apply_symm_apply]

theorem fixV_map_congr_equiv (φ : W ≃* W') (X : Subgroup (MulAut W)) :
    fixV (X.map (MulAut.congr φ).toMonoidHom) = (fixV X).map φ.toMonoidHom := by
  ext w
  rw [mem_fixV_map_congr_equiv, Subgroup.mem_map_equiv]

theorem fixV_map_conj_eq (X : Subgroup (MulAut W)) (g : MulAut W) :
    fixV (X.map (MulAut.conj g).toMonoidHom) = (fixV X).map g.toMonoidHom := by
  ext v
  rw [Subgroup.mem_map_equiv]
  constructor
  · intro hv x hx
    have h1 : g (x (g⁻¹ v)) = v := hv (g * x * g⁻¹) ⟨x, hx, rfl⟩
    calc x (g.symm v) = g.symm (g (x (g⁻¹ v))) := (g.symm_apply_apply _).symm
      _ = g.symm v := by rw [h1]
  · rintro hv _ ⟨x, hx, rfl⟩
    show g (x (g⁻¹ v)) = v
    rw [show g⁻¹ v = g.symm v from rfl, hv x hx, g.apply_symm_apply]

theorem commV_map_congr_equiv (φ : W ≃* W') (X : Subgroup (MulAut W)) :
    commV (X.map (MulAut.congr φ).toMonoidHom) = (commV X).map φ.toMonoidHom := by
  unfold commV
  rw [MonoidHom.map_closure]
  congr 1
  ext w'
  constructor
  · rintro ⟨x', hx', v', rfl⟩
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hx'
    refine ⟨x (φ.symm v') * (φ.symm v')⁻¹, ⟨x, hx, φ.symm v', rfl⟩, ?_⟩
    show φ (x (φ.symm v') * (φ.symm v')⁻¹) = (MulAut.congr φ x) v' * v'⁻¹
    rw [map_mul, map_inv, MulEquiv.apply_symm_apply]
    rfl
  · rintro ⟨_, ⟨x, hx, v, rfl⟩, rfl⟩
    refine ⟨MulAut.congr φ x, Subgroup.mem_map.mpr ⟨x, hx, rfl⟩, φ v, ?_⟩
    show (MulAut.congr φ x) (φ v) * (φ v)⁻¹ = φ (x v * v⁻¹)
    rw [map_mul, map_inv]
    show φ (x (φ.symm (φ v))) * (φ v)⁻¹ = φ (x v) * (φ v)⁻¹
    rw [MulEquiv.symm_apply_apply]

theorem isFFStarOffender_map_congr_equiv (φ : W ≃* W') {X A : Subgroup (MulAut W)}
    (h : IsFFStarOffender X A) :
    IsFFStarOffender (X.map (MulAut.congr φ).toMonoidHom)
      (A.map (MulAut.congr φ).toMonoidHom) := by
  obtain ⟨hAX, hA1, ⟨hcomm, hsq⟩, hoff⟩ := h
  have hinj : Function.Injective (MulAut.congr φ).toMonoidHom := (MulAut.congr φ).injective
  have hcard : ∀ B : Subgroup (MulAut W), Nat.card (B.map (MulAut.congr φ).toMonoidHom) *
      Nat.card (fixV (B.map (MulAut.congr φ).toMonoidHom)) = Nat.card B * Nat.card (fixV B) :=
    fun B => by
      rw [fixV_map_congr_equiv, Subgroup.card_map_of_injective hinj,
        Subgroup.card_map_of_injective φ.injective]
  refine ⟨Subgroup.map_mono hAX,
    fun h0 => hA1 ((Subgroup.map_eq_bot_iff_of_injective _ hinj).1 h0), ⟨?_, ?_⟩, fun B hB => ?_⟩
  · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    rw [← map_mul, ← map_mul, hcomm a ha b hb]
  · rintro _ ⟨a, ha, rfl⟩
    rw [← map_pow, hsq a ha, map_one]
  · have hB' : (B.comap (MulAut.congr φ).toMonoidHom).map (MulAut.congr φ).toMonoidHom = B :=
      Subgroup.map_comap_eq_self_of_surjective (MulAut.congr φ).surjective B
    rw [← hB', hcard, hcard]
    exact hoff _ fun x hx => by
      obtain ⟨a, ha, hax⟩ := Subgroup.mem_map.1 (hB (Subgroup.mem_comap.1 hx))
      exact hinj hax ▸ ha

end CFSG.Quasithin
