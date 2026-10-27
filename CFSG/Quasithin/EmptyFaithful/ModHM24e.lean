module

public import CFSG.Quasithin.EmptyFaithful.ModHM24d1
public import CFSG.Quasithin.EmptyFaithful.ModHM24d2
public import CFSG.Quasithin.EmptyFaithful.ModHM24d3
public import CFSG.Quasithin.EmptyFaithful.ModHSolv

public section

namespace CFSG.Quasithin.ModH.M24e

open CFSG.Quasithin.ModH.S24 CFSG.Quasithin.ModH.M24b CFSG.Quasithin.ModH.M24c CFSG.Blueprint CFSG.QuasithinUnique

theorem cross21 : ∀ k < 9, compn 24 M24d2.dat.cz (M24d1.dat.repCi.getD k 0) ∉ tK := by decide +kernel

theorem cross31 : ∀ k < 9, compn 24 M24d3.dat.cz (M24d1.dat.repCi.getD k 0) ∉ tK := by decide +kernel

theorem cross32 : ∀ k < 9, compn 24 M24d3.dat.cz (M24d2.dat.repCi.getD k 0) ∉ tK := by decide +kernel

theorem ne21 : M24d2.dat.Zg ≠ M24d1.dat.Zg := by
  intro h
  have hz : M24d2.dat.z ∈ M24d1.dat.Zg := h ▸ M24d2.facts.z_mem
  obtain ⟨k, hk, hmem⟩ := (M24d1.facts.mem _).1 hz
  rw [ZData.cd_z] at hmem
  exact cross21 k hk hmem

theorem ne31 : M24d3.dat.Zg ≠ M24d1.dat.Zg := by
  intro h
  have hz : M24d3.dat.z ∈ M24d1.dat.Zg := h ▸ M24d3.facts.z_mem
  obtain ⟨k, hk, hmem⟩ := (M24d1.facts.mem _).1 hz
  rw [ZData.cd_z] at hmem
  exact cross31 k hk hmem

theorem ne32 : M24d3.dat.Zg ≠ M24d2.dat.Zg := by
  intro h
  have hz : M24d3.dat.z ∈ M24d2.dat.Zg := h ▸ M24d3.facts.z_mem
  obtain ⟨k, hk, hmem⟩ := (M24d2.facts.mem _).1 hz
  rw [ZData.cd_z] at hmem
  exact cross32 k hk hmem

theorem contra_of_facts {Yb : Subgroup G} (hd : ConfigData G Sg Yb) (hsimple : IsSimpleGroup G)
    (hcard3 : 3 ∣ Nat.card G) (d : ZData) (hf : d.Facts) (hZ : Yb ⊔ Sg = d.Zg) : False := by
  have hnt : Subgroup.normalizer (d.Ng : Set G) ≠ ⊤ := by
    intro hT
    have hnormal : d.Ng.Normal := Subgroup.normalizer_eq_top_iff.1 hT
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal d.Ng with h | h
    · exact hf.ng_ne h
    · have hp := hf.ngp
      rw [h] at hp
      obtain ⟨n, hn⟩ := (IsPGroup.iff_card).1 hp
      rw [Subgroup.card_top] at hn
      rw [hn] at hcard3
      have h3 : 3 ∣ 2 := Nat.Prime.dvd_of_dvd_pow Nat.prime_three hcard3
      omega
  have hmax := hd.maximal d.Ng hf.ngp hf.ng_ne (by rw [hZ]; exact hf.normalizes) hnt
  have hwY : d.w ∈ Subgroup.normalizer (Yb : Set G) := hmax hf.w_norm
  have hyY : d.y ∈ Yb := by
    refine odd_mem_of_sup Sg_isPGroup hd.normalizes (by rw [hZ]; exact hf.y_mem) hf.y_odd
  have h1 : d.w * d.y * d.w⁻¹ ∈ Yb := (Subgroup.mem_normalizer_iff.1 hwY d.y).1 hyY
  apply hf.wy
  rw [← hZ]
  exact (le_sup_left : Yb ≤ Yb ⊔ Sg) h1


theorem not_configData_m24 (hns : ¬ Group.IsSolvable G) {Yb : Subgroup G} (hd : ConfigData G Sg Yb) :
    False := by
  have hsimple : IsSimpleGroup G := (CFSG.Sporadic.Mathieu.fam_m24_simplicity).2.2
  have hcard3 : 3 ∣ Nat.card G := by
    rw [show Nat.card G = Nat.card ↥NativeSporadic.M24 from rfl,
      CFSG.QuasithinUnique.Ch1.SporLat.M24.m24_card]
    norm_num
  have hZs : Group.IsSolvable ↥(Yb ⊔ Sg) :=
    isSolvable_sup_of_le_normalizer hd.solvable Sg_isPGroup hd.normalizes
  have h9 : 9 ∣ Nat.card ↥(Yb ⊔ Sg) := hd.nine.trans (Subgroup.card_dvd_of_le le_sup_left)
  have hc : Nat.card ↥(Yb ⊔ Sg) = 9216 :=
    M24a.card_nine_m24 hns Sg_sylow (le_sup_right : Sg ≤ Yb ⊔ Sg) hZs h9
  rcases eq_of_three M24d1.facts.sg_le M24d2.facts.sg_le M24d3.facts.sg_le M24d1.facts.card
    M24d2.facts.card M24d3.facts.card ne21.symm ne31.symm ne32.symm (le_sup_right : Sg ≤ Yb ⊔ Sg) hc with
    h | h | h
  · exact contra_of_facts hd hsimple hcard3 _ M24d1.facts h
  · exact contra_of_facts hd hsimple hcard3 _ M24d2.facts h
  · exact contra_of_facts hd hsimple hcard3 _ M24d3.facts h

end CFSG.Quasithin.ModH.M24e
