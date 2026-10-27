module

public import CFSG.Quasithin.Vol2.Ch5Sec1L34QKq

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin

section Congr

variable {V V' : Type*} [CommGroup V] [CommGroup V']

theorem congrHom_symm_comp (e : V ≃* V') :
    (congrHom e.symm).comp (congrHom e) = MonoidHom.id (MulAut V) := by
  ext x v
  simp

theorem kq_map_congr [Finite V] [Finite V'] (e : V ≃* V') (X : Subgroup (MulAut V)) (k : ℕ) :
    kq (X.map (congrHom e)) k = kq X k := by
  refine le_antisymm (kq_map_congr_le e X k) ?_
  have h := kq_map_congr_le e.symm (X.map (congrHom e)) k
  rwa [Subgroup.map_map, congrHom_symm_comp, Subgroup.map_id] at h

end Congr

section Conj

variable {V : Type*} [CommGroup V]

theorem congrHom_eq_conj (g : MulAut V) (x : MulAut V) : congrHom g x = g * x * g⁻¹ := by
  ext v
  rfl

theorem map_congrHom_of_mem {X : Subgroup (MulAut V)} {g : MulAut V} (hg : g ∈ X) :
    X.map (congrHom g) = X := by
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    rw [congrHom_eq_conj]
    exact X.mul_mem (X.mul_mem hg hx) (X.inv_mem hg)
  · intro x hx
    refine ⟨g⁻¹ * x * g, X.mul_mem (X.mul_mem (X.inv_mem hg) hx) hg, ?_⟩
    rw [congrHom_eq_conj]
    group

theorem map_congrHom_mem_kRle {X B : Subgroup (MulAut V)} {g : MulAut V} (hg : g ∈ X) {k : ℕ}
    {r : ℚ} (hB : B ∈ kRle X k r) : B.map (congrHom g) ∈ kRle X k r := by
  obtain ⟨⟨hB2, hBr⟩, hBk⟩ := hB
  refine ⟨⟨?_, by rw [rAV_map_congr]; exact hBr⟩, ?_⟩
  · have := IsA2.map_congr g hB2
    rwa [map_congrHom_of_mem hg] at this
  · rw [commSeries_map_congr, hBk, Subgroup.map_bot]

theorem mem_QhatStar_map_conj [Finite V] {X A : Subgroup (MulAut V)} (hA : A ∈ QhatStar X)
    {g : MulAut V} (hg : g ∈ X) : A.map (congrHom g) ∈ QhatStar X := by
  obtain ⟨r, hr, hr2, hAk, hmin⟩ := hA
  refine ⟨r, hr, hr2, map_congrHom_mem_kRle hg hAk, fun B hB hBA => ?_⟩
  have hB' := map_congrHom_mem_kRle (X.inv_mem hg) hB
  have hle : B.map (congrHom g⁻¹) ≤ A := by
    rintro _ ⟨b, hb, rfl⟩
    obtain ⟨a, ha, hab⟩ := hBA hb
    rw [← hab, congrHom_eq_conj, congrHom_eq_conj]
    simpa [mul_assoc] using ha
  have heq := hmin _ hB' hle
  apply le_antisymm hBA
  rw [← heq]
  rintro _ ⟨_, ⟨b, hb, rfl⟩, rfl⟩
  rw [congrHom_eq_conj, congrHom_eq_conj]
  simpa [mul_assoc] using hb

theorem qhatOf_autSub_le_of_mem_QhatStar' [Finite V] (hV : ∀ v : V, v ^ 2 = 1)
    {X Y A : Subgroup (MulAut V)} {r : ℚ} (hr : qhatOf X = (r : WithTop ℚ))
    (hA : A ∈ QhatStar X) (hAY : A ≤ Y) {U : Subgroup V} (hU : A ≤ stabSub U)
    (hUA : commSub U A ≠ ⊥) : qhatOf (autSub Y U) ≤ (r : WithTop ℚ) := by
  obtain ⟨-, h7⟩ := D2_7 hV hr hA hU hUA
  obtain ⟨r', hr', -, ⟨⟨hA2, hAr⟩, hAk3⟩, -⟩ := hA
  have hrr : r' = r := WithTop.coe_injective (hr'.symm.trans hr)
  subst hrr
  rcases h7 with ⟨ε, hε, hεA⟩ | ⟨hB, hW⟩
  · obtain ⟨⟨hA2', hrle⟩, hk⟩ := hεA
    exact kq_le_iff.mpr ⟨autSub A U, ⟨autSub_mono hAY U, hA2'.2⟩, hk, by linarith⟩
  · have hA2U := hA2.autSub hU hUA
    refine kq_le_iff.mpr ⟨autSub A U, ⟨autSub_mono hAY U, hA2U.2⟩,
      commSeries_autSub_eq_bot hU hAk3, ?_⟩
    rw [rAV_autSub_eq_of_faithful hU hB hW]
    exact hAr

end Conj

end CFSG.Quasithin.H13
