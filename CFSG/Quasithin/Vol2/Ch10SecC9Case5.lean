module

public import CFSG.Quasithin.Vol2.Ch10SecC9Diag
public import CFSG.Quasithin.Vol2.Ch10SecC9B

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecC

open CFSG.Open CFSG.Quasithin.H13 CFSG.QuasithinUnique

variable {G : Type} [Group G] [Finite G] {L T P Y W W' : Subgroup G}

omit [Finite G] in
theorem le_of_inf_eq_bot (hc : ∀ a ∈ W, ∀ b ∈ W', a * b = b * a) (hYs : Y ≤ W ⊔ W')
    (hWY : W ≤ Y) (hYW' : Y ⊓ W' = ⊥) : Y ≤ W := by
  intro y hy
  obtain ⟨w, hw, w', hw', rfl⟩ := exists_mul_of_mem_sup hc (hYs hy)
  have h1 : w' ∈ Y ⊓ W' := ⟨by simpa using Y.mul_mem (Y.inv_mem (hWY hw)) hy, hw'⟩
  rw [hYW', Subgroup.mem_bot] at h1
  rw [h1, mul_one]
  exact hw

theorem le_of_case5 (hc : ∀ a ∈ W ⊔ W', ∀ b ∈ W ⊔ W', a * b = b * a) (hinf : W ⊓ W' = ⊥)
    (hLW : L ≤ Subgroup.normalizer (W : Set G)) (hLW' : L ≤ Subgroup.normalizer (W' : Set G))
    (hirr : IrrG L W) (hirr' : IrrG L W') (hni : ¬ IsXSectionIso L ⊥ W W')
    (hYs : Y ≤ W ⊔ W') (hLY : L ≤ Subgroup.normalizer (Y : Set G))
    (hTY : T ≤ Subgroup.normalizer (Y : Set G)) (hTL : T ≤ Subgroup.normalizer (L : Set G))
    (hTV : T ≤ Subgroup.normalizer ((W ⊔ W' : Subgroup G) : Set G)) (hP : IsPGroup 2 P)
    (hVP : W ⊔ W' ≤ P) (hTP : T ≤ P)
    (hfix : (W ⊔ W') ⊓ Subgroup.centralizer (T : Set G) ≤ Y) : W ⊔ W' ≤ Y := by
  have hcW : ∀ a ∈ W, ∀ b ∈ W', a * b = b * a := fun a ha b hb =>
    hc a (le_sup_left (a := W) ha) b (le_sup_right (b := W') hb)
  have hcW' : ∀ a ∈ W', ∀ b ∈ W, a * b = b * a := fun a ha b hb => (hcW b hb a ha).symm
  have hnd : ∀ D : Subgroup G, D ≤ W ⊔ W' → L ≤ Subgroup.normalizer (D : Set G) → D ⊓ W = ⊥ →
      D ⊓ W' = ⊥ → D = ⊥ := fun D hDs hLD h1 h2 =>
    eq_bot_of_disjoint hcW hirr hirr' hLW hLW' hni hDs hLD h1 h2
  have hnd' : ∀ D : Subgroup G, D ≤ W' ⊔ W → L ≤ Subgroup.normalizer (D : Set G) → D ⊓ W' = ⊥ →
      D ⊓ W = ⊥ → D = ⊥ := fun D hDs hLD h1 h2 => hnd D (sup_comm W' W ▸ hDs) hLD h2 h1
  have hfixU : ∀ U : Subgroup G, U ≤ W ⊔ W' → T ≤ Subgroup.normalizer (U : Set G) → U ≠ ⊥ →
      ∃ u ∈ U, u ≠ 1 ∧ u ∈ Y := fun U hU hTU hU1 => by
    obtain ⟨u, huU, hu1, huC⟩ := exists_mem_centralizer_ne_one hP (hU.trans hVP) hTP hTU hU1
    exact ⟨u, huU, hu1, hfix ⟨hU huU, huC⟩⟩
  have hV1 : W ⊔ W' ≠ ⊥ := fun h => hirr.1 (le_bot_iff.mp (h ▸ le_sup_left))
  have hYne : Y ≠ ⊥ := by
    obtain ⟨u, -, hu1, huY⟩ := hfixU _ le_rfl hTV hV1
    intro h
    rw [h, Subgroup.mem_bot] at huY
    exact hu1 huY
  have hLYW := fun l (hl : l ∈ L) => mem_normalizer_inf' (hLY hl) (hLW hl)
  have hLYW' := fun l (hl : l ∈ L) => mem_normalizer_inf' (hLY hl) (hLW' hl)
  rcases hirr.2 (Y ⊓ W) inf_le_right hLYW with hA | hA <;>
    rcases hirr'.2 (Y ⊓ W') inf_le_right hLYW' with hB | hB
  · exact absurd (hnd Y hYs hLY hA hB) hYne
  ·
    have hW'Y : W' ≤ Y := by rw [← hB]; exact inf_le_left
    have hYW' : Y ≤ W' := le_of_inf_eq_bot hcW' (sup_comm W W' ▸ hYs) hW'Y hA
    have hTW' : T ≤ Subgroup.normalizer (W' : Set G) := le_antisymm hYW' hW'Y ▸ hTY
    have hTW : T ≤ Subgroup.normalizer (W : Set G) := fun r hr =>
      mem_normalizer_of_noDiag (W := W') (W' := W) (inf_comm W W' ▸ hinf) hirr hLW hnd'
        (sup_comm W W' ▸ hTV hr) (hTL hr) (hTW' hr)
    obtain ⟨u, huW, hu1, huY⟩ := hfixU W le_sup_left hTW hirr.1
    have : u ∈ W ⊓ W' := ⟨huW, hYW' huY⟩
    rw [hinf, Subgroup.mem_bot] at this
    exact absurd this hu1
  ·
    have hWY : W ≤ Y := by rw [← hA]; exact inf_le_left
    have hYW : Y ≤ W := le_of_inf_eq_bot hcW hYs hWY hB
    have hTW : T ≤ Subgroup.normalizer (W : Set G) := le_antisymm hYW hWY ▸ hTY
    have hTW' : T ≤ Subgroup.normalizer (W' : Set G) := fun r hr =>
      mem_normalizer_of_noDiag hinf hirr' hLW' hnd (hTV hr) (hTL hr) (hTW hr)
    obtain ⟨u, huW', hu1, huY⟩ := hfixU W' le_sup_right hTW' hirr'.1
    have : u ∈ W ⊓ W' := ⟨hYW huY, huW'⟩
    rw [hinf, Subgroup.mem_bot] at this
    exact absurd this hu1
  · exact sup_le (by rw [← hA]; exact inf_le_left) (by rw [← hB]; exact inf_le_left)

omit [Finite G] in
theorem irrG_conjugate {s : G} (h : IrrG L W) (hs : s ∈ Subgroup.normalizer (L : Set G)) :
    IrrG L (CFSG.conjugate W s) := by
  have hback : ∀ X : Subgroup G, CFSG.conjugate (CFSG.conjugate X s⁻¹) s = X := fun X => by
    rw [SecA.conjugate_conjugate, inv_mul_cancel, SecA.conjugate_one]
  refine ⟨fun hW => h.1 ?_, fun X hX hLX => ?_⟩
  · have := congrArg (fun Y => CFSG.conjugate Y s⁻¹) hW
    simp only [SecA.conjugate_conjugate, mul_inv_cancel, SecA.conjugate_one] at this
    rw [this]
    simp [CFSG.conjugate]
  · have hX' : CFSG.conjugate X s⁻¹ ≤ W := by
      have := SecA.conjugate_mono hX s⁻¹
      rwa [SecA.conjugate_conjugate, mul_inv_cancel, SecA.conjugate_one] at this
    have hLX' : L ≤ Subgroup.normalizer ((CFSG.conjugate X s⁻¹ : Subgroup G) : Set G) :=
      fun l hl => by
        rw [Subgroup.mem_normalizer_iff]
        intro x
        rw [SecA.mem_conjugate_iff, SecA.mem_conjugate_iff, inv_inv]
        have hl' : s⁻¹ * l * s ∈ L := by
          have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hs) l).mp hl
          rwa [inv_inv] at this
        have e : s⁻¹ * (l * x * l⁻¹) * s = (s⁻¹ * l * s) * (s⁻¹ * x * s) * (s⁻¹ * l * s)⁻¹ := by
          group
        rw [e]
        exact Subgroup.mem_normalizer_iff.mp (hLX hl') _
    rcases h.2 _ hX' hLX' with h' | h'
    · left
      rw [← hback X, h']
      simp [CFSG.conjugate]
    · right
      rw [← hback X, h']

end CFSG.Quasithin.Vol2.Ch10.SecC
