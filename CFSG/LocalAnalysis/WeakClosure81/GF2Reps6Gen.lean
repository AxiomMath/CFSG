module

public import CFSG.Quasithin.Background.FixVLattice

public section

namespace CFSG.LocalAnalysis.WeakClosure81.Asch6

open CFSG.Quasithin Subgroup

@[expose] def quadY {P : Type*} [Group P] (G A : Subgroup P) (a : P) : Subgroup P :=
  ⨆ (x : P) (_ : x ∈ G) (_ : x * a = a * x), A.map (MulAut.conj x).toMonoidHom

variable {V : Type*} [CommGroup V]

theorem fixes_commV_map_conj {A : Subgroup (MulAut V)} (hA : IsQuadratic A) {a : MulAut V}
    (ha : a ∈ A) {x : MulAut V} (hx : x * a = a * x) :
    ∀ y ∈ A.map (MulAut.conj x).toMonoidHom, ∀ w ∈ commV (zpowers a), y w = w := by
  intro y hy w hw
  obtain ⟨c, hcA, rfl⟩ := Subgroup.mem_map.mp hy
  have hle : commV (Subgroup.zpowers a) ≤ commV A := by
    rw [FixVLat.commV_le_iff]
    intro g hg v
    exact Subgroup.subset_closure ⟨g, Subgroup.zpowers_le.mpr ha hg, v, rfl⟩
  have hnorm : ∀ z ∈ Subgroup.zpowers a, x⁻¹ * z * (x⁻¹)⁻¹ ∈ Subgroup.zpowers a := by
    intro z hz
    rcases Subgroup.mem_zpowers_iff.mp hz with ⟨n, rfl⟩
    have hconj : (MulAut.conj x⁻¹) a = a := by
      rw [MulAut.conj_apply, inv_inv, mul_assoc, ← hx]
      group
    have hzpow : (MulAut.conj x⁻¹) (a ^ n) = a ^ n := by
      rw [map_zpow, hconj]
    have hconj_zpow : x⁻¹ * a ^ n * (x⁻¹)⁻¹ = a ^ n := by
      simpa [MulAut.conj_apply] using hzpow
    rw [hconj_zpow]
    exact Subgroup.zpow_mem_zpowers a n
  have hxinv : x⁻¹ w ∈ commV (Subgroup.zpowers a) :=
    commV_apply_mem_of_normalizes hnorm hw
  have hc : c (x⁻¹ w) = x⁻¹ w := hA (hle hxinv) c hcA
  change ((MulAut.conj x) c) w = w
  rw [MulAut.conj_apply]
  change x (c (x⁻¹ w)) = w
  rw [hc]
  simp

theorem fixes_commV_quadY {G A : Subgroup (MulAut V)} (hA : IsQuadratic A) {a : MulAut V}
    (ha : a ∈ A) : ∀ y ∈ quadY G A a, ∀ w ∈ commV (zpowers a), y w = w := by
  intro y hy w hw
  have hle : quadY G A a ≤ centSub (commV (Subgroup.zpowers a)) := by
    refine iSup_le fun x => iSup_le fun _ => iSup_le fun hxa => ?_
    intro z hz
    exact mem_centSub.mpr (fixes_commV_map_conj hA ha hxa z hz)
  exact (mem_centSub.mp (hle hy)) w hw

theorem commV_inf_commV_conj_eq_bot {Y : Subgroup (MulAut V)} {a h : MulAut V}
    (hY : ∀ y ∈ Y, ∀ w ∈ commV (zpowers a), y w = w)
    (hgen : fixV (Y ⊔ Y.map (MulAut.conj h).toMonoidHom) = ⊥) :
    commV (zpowers a) ⊓ commV (zpowers (h * a * h⁻¹)) = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  intro w hw
  have hwA : w ∈ commV (Subgroup.zpowers a) := hw.1
  have hwmap : w ∈ (commV (Subgroup.zpowers a)).map h.toMonoidHom := by
    rw [← commV_zpowers_conj_eq a h]
    exact hw.2
  obtain ⟨u, hu, huw⟩ := hwmap
  have hYfix : w ∈ fixV Y := fun y hy => hY y hy w hwA
  have hYhfix : w ∈ fixV (Y.map (MulAut.conj h).toMonoidHom) := by
    intro y hy
    obtain ⟨c, hcY, rfl⟩ := Subgroup.mem_map.mp hy
    have hcu : c u = u := hY c hcY u hu
    rw [← huw]
    simp [MulAut.conj_apply, MulAut.mul_apply, hcu]
  have hwbot : w ∈ fixV (Y ⊔ Y.map (MulAut.conj h).toMonoidHom) :=
    FixVLat.mem_fixV_sup hYfix hYhfix
  rw [hgen] at hwbot
  simpa using hwbot

end CFSG.LocalAnalysis.WeakClosure81.Asch6

end
