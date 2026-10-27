module

public import CFSG.RankThree.PartTwo.Sec21.Item224Res5ProofDefs

public section

namespace CFSG.RankThree.PartTwo.Sec21.Item224KFactsProof

open CFSG.RankThree.PartTwo.Sec21.Item224Res5Proof

variable {X Y : Type*} [Group X] [Group Y]

theorem mul_conj_mul_inv (α : MulAut X) (y : X) :
    α * MulAut.conj y * α⁻¹ = MulAut.conj (α y) := by
  ext m
  simp [MulAut.mul_apply, map_mul, map_inv]

theorem congr_conj (e : X ≃* Y) (y : X) :
    MulAut.congr e (MulAut.conj y) = MulAut.conj (e y) := by
  ext m
  simp [MulAut.congr_apply, map_mul, map_inv]

theorem fixed_map_congr_iff (e : X ≃* Y) (T : Subgroup (MulAut X)) (x : X) :
    (∀ t ∈ T.map (MulAut.congr e).toMonoidHom, t (e x) = e x) ↔ ∀ t ∈ T, t x = x := by
  constructor
  · intro h t ht
    have h1 := h _ ⟨t, ht, rfl⟩
    change e (t (e.symm (e x))) = e x at h1
    rw [MulEquiv.symm_apply_apply] at h1
    exact e.injective h1
  · rintro h _ ⟨t, ht, rfl⟩
    change e (t (e.symm (e x))) = e x
    rw [MulEquiv.symm_apply_apply, h t ht]

theorem oddFixed_map_congr (e : X ≃* Y) (T : Subgroup (MulAut X)) :
    oddFixed Y (T.map (MulAut.congr e).toMonoidHom) = (oddFixed X T).map e.toMonoidHom := by
  rw [oddFixed, oddFixed, MonoidHom.map_closure]
  congr 1
  ext y
  constructor
  · rintro ⟨hy, hodd⟩
    refine ⟨e.symm y, ⟨?_, ?_⟩, by simp⟩
    · rw [← fixed_map_congr_iff e T]
      simpa using hy
    · rwa [← MulEquiv.orderOf_eq e, MulEquiv.apply_symm_apply]
  · rintro ⟨x, ⟨hx, hodd⟩, rfl⟩
    refine ⟨(fixed_map_congr_iff e T x).mpr hx, ?_⟩
    change Odd (orderOf (e x))
    rwa [MulEquiv.orderOf_eq]

theorem autElliptic_map_congr (e : X ≃* Y) {T : Subgroup (MulAut X)} (h : AutElliptic X T) :
    AutElliptic Y (T.map (MulAut.congr e).toMonoidHom) := by
  intro P hP hPN
  set Φ := MulAut.congr e with hΦ
  set PX : Subgroup (MulAut X) := P.comap Φ.toMonoidHom with hPX
  have hPXmap : PX.map Φ.toMonoidHom = P := by
    rw [hPX, Subgroup.map_comap_eq, MonoidHom.range_eq_top_of_surjective _ Φ.surjective,
      inf_eq_right.mpr le_top]
  have hPX2 : IsPGroup 2 PX := hP.comap_of_injective Φ.toMonoidHom Φ.injective
  have hPXN : (oddFixed X T).map MulAut.conj ≤ Subgroup.normalizer (PX : Set (MulAut X)) := by
    rintro _ ⟨x, hx, rfl⟩
    have hex : e x ∈ oddFixed Y (T.map Φ.toMonoidHom) := by
      rw [oddFixed_map_congr]
      exact ⟨x, hx, rfl⟩
    have hN := hPN ⟨e x, hex, rfl⟩
    rw [Subgroup.mem_normalizer_iff] at hN ⊢
    intro p
    have hconj : Φ (MulAut.conj x * p * (MulAut.conj x)⁻¹) =
        MulAut.conj (e x) * Φ p * (MulAut.conj (e x))⁻¹ := by
      rw [map_mul, map_mul, map_inv, congr_conj]
    change Φ p ∈ P ↔ Φ (MulAut.conj x * p * (MulAut.conj x)⁻¹) ∈ P
    rw [hconj]
    exact hN (Φ p)
  obtain ⟨hfix, hcyc⟩ := h PX hPX2 hPXN
  refine ⟨?_, ?_⟩
  · intro q hq y hy
    rw [oddFixed_map_congr] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    have hq' : Φ.symm q ∈ PX := by
      change Φ (Φ.symm q) ∈ P
      rwa [MulEquiv.apply_symm_apply]
    have h1 := hfix _ hq' x hx
    have h2 : q = Φ (Φ.symm q) := (MulEquiv.apply_symm_apply Φ q).symm
    rw [h2]
    change e ((Φ.symm q) (e.symm (e x))) = e x
    rw [MulEquiv.symm_apply_apply, h1]
  · have hsurj : Function.Surjective
        ((Φ.toMonoidHom.comp PX.subtype).codRestrict P fun p => p.2) := by
      rintro ⟨q, hq⟩
      refine ⟨⟨Φ.symm q, ?_⟩, ?_⟩
      · change Φ (Φ.symm q) ∈ P
        rwa [MulEquiv.apply_symm_apply]
      · apply Subtype.ext
        change Φ (Φ.symm q) = q
        exact MulEquiv.apply_symm_apply Φ q
    exact isCyclic_of_surjective _ hsurj

theorem map_congr_symm_map_congr (e : X ≃* Y) (T : Subgroup (MulAut X)) :
    (T.map (MulAut.congr e).toMonoidHom).map (MulAut.congr e.symm).toMonoidHom = T := by
  rw [Subgroup.map_map]
  have hid : ((MulAut.congr e.symm).toMonoidHom.comp (MulAut.congr e).toMonoidHom) =
      MonoidHom.id (MulAut X) := by
    ext α x
    simp [MulAut.congr_apply]
  rw [hid, Subgroup.map_id]

theorem autElliptic_of_map_congr (e : X ≃* Y) {T : Subgroup (MulAut X)}
    (h : AutElliptic Y (T.map (MulAut.congr e).toMonoidHom)) : AutElliptic X T := by
  have h' := autElliptic_map_congr e.symm h
  rwa [map_congr_symm_map_congr] at h'

theorem mem_center_iff_of_mulEquiv (e : X ≃* Y) (x : X) :
    e x ∈ Subgroup.center Y ↔ x ∈ Subgroup.center X := by
  rw [Subgroup.mem_center_iff, Subgroup.mem_center_iff]
  constructor
  · intro h g
    apply e.injective
    rw [map_mul, map_mul, h (e g)]
  · intro h g
    obtain ⟨g, rfl⟩ := e.surjective g
    rw [← map_mul, ← map_mul, h g]

end CFSG.RankThree.PartTwo.Sec21.Item224KFactsProof
