module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3RowL3AAAA

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {W : Type} [CommGroup W]

private theorem s16h_autSec_le_normalizer {L Y : Subgroup (MulAut W)} {V C : Subgroup W}
    (hLV : L ≤ stabSub V) (hLC : L ≤ stabSub C) (hYV : Y ≤ stabSub V) (hYC : Y ≤ stabSub C)
    (hYL : Y ≤ normalizer (L : Set (MulAut W))) :
    autSec Y V C ≤ normalizer ((autSec L V C : Subgroup (MulAut (Sec V C))) :
      Set (MulAut (Sec V C))) := by
  set X' : Subgroup (MulAut W) := stabSub V ⊓ stabSub C with hX'def
  have hX'V : X' ≤ stabSub V := inf_le_left
  have hX'C : X' ≤ stabSub C := inf_le_right
  rw [← CFSG.Quasithin.B5.map_secHom_eq_autSec X' hX'V hX'C (le_inf hYV hYC),
    ← CFSG.Quasithin.B5.map_secHom_eq_autSec X' hX'V hX'C (le_inf hLV hLC)]
  refine le_trans (Subgroup.map_mono ?_) (Subgroup.le_normalizer_map _)
  intro y hy
  rw [Subgroup.mem_normalizer_iff]
  intro g
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
  exact Subgroup.mem_normalizer_iff.mp (hYL (Subgroup.mem_subgroupOf.mp hy)) (g : MulAut W)

public theorem s16h_twoNat_orbit_fix [Finite W] {L : Subgroup (MulAut W)} {U Z : Subgroup W}
    (hS : SumOfNat (fun H U Z => CFSG.Quasithin.BinaryNaturalSL H U Z 3 1) L U Z 2)
    (hLU : L ≤ stabSub U) (hLZ : L ≤ stabSub Z) (hLcard : Nat.card ↥L = 168)
    (E : Subgroup (MulAut W)) (hEN : E ≤ normalizer (L : Set (MulAut W)))
    (hEU : E ≤ stabSub U) (hEZ : E ≤ stabSub Z) (hEab : IsElemAbelian 3 E)
    (hEcard : 9 * Nat.card ↥(E ⊓ centSub U) ≤ Nat.card ↥E)
    (hErank : Nat.card ↥(autSub E U) ≤ 9) (hZcard : Nat.card ↥Z ≤ 2) :
    ∀ v : Sec U Z, v ≠ 1 → ∃ d : ↥(autSec E U Z), (d : MulAut (Sec U Z)) ≠ 1 ∧
      ∃ l : ↥L, (d : MulAut (Sec U Z))
        (CFSG.Quasithin.B5.secHom L hLU hLZ l v) =
        CFSG.Quasithin.B5.secHom L hLU hLZ l v := by
  intro v hv
  set G : Subgroup (MulAut (Sec U Z)) := autSec L U Z with hG
  set E' : Subgroup (MulAut (Sec U Z)) := autSec E U Z with hE'
  have hEN' : E' ≤ Subgroup.normalizer (G : Set (MulAut (Sec U Z))) := by
    rw [hE', hG]
    exact s16h_autSec_le_normalizer hLU hLZ hEU hEZ hEN
  have hE9 : Nat.card ↥E' = 9 := by
    rw [hE']
    exact s16h_twoNat_autSec_E_card hLU hLZ E hEU hEZ hEab hEcard hErank hZcard
  have hGdvd : Nat.card ↥G ∣ 168 := by
    rw [hG, ← CFSG.Quasithin.B5.range_secHom L hLU hLZ]
    exact hLcard ▸ Subgroup.card_range_dvd (CFSG.Quasithin.B5.secHom L hLU hLZ)
  have ha9 : ¬ 9 ∣ Nat.card (MulAction.orbit G v) := by
    intro h9
    have hOrbDvd : Nat.card (MulAction.orbit G v) ∣ Nat.card ↥G := by
      rw [Nat.card_coe_set_eq, ← MulAction.index_stabilizer]
      exact ⟨Nat.card ↥(MulAction.stabilizer G v), by
        rw [mul_comm, Subgroup.card_mul_index]⟩
    have hdvd : 9 ∣ 168 := dvd_trans h9 (dvd_trans hOrbDvd hGdvd)
    norm_num at hdvd
  obtain ⟨e, hene, x, hxO, hfix⟩ :=
    s16h_orbit_fix_count G E' hEN' hE9 v ha9
      (by simpa [hG] using s16h_twoNat_orbit_same_size hS hLU hLZ hLcard v hv)
      (fun h3 => by
        simpa [hG] using s16h_twoNat_orbit_same_size_three hS hLU hLZ hLcard v hv h3)
  rw [MulAction.mem_orbit_iff] at hxO
  obtain ⟨g, hgv⟩ := hxO
  have hgmem : (g : MulAut (Sec U Z)) ∈ (CFSG.Quasithin.B5.secHom L hLU hLZ).range := by
    rw [CFSG.Quasithin.B5.range_secHom L hLU hLZ]
    exact g.2
  obtain ⟨l, hl⟩ := MonoidHom.mem_range.mp hgmem
  have hx : x = CFSG.Quasithin.B5.secHom L hLU hLZ l v := by
    calc x = g • v := hgv.symm
      _ = (g : MulAut (Sec U Z)) v := rfl
      _ = (CFSG.Quasithin.B5.secHom L hLU hLZ l) v := by rw [hl]
  refine ⟨e, hene, l, ?_⟩
  rw [hx] at hfix
  exact hfix

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
