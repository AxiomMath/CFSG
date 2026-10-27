module

public import CFSG.Quasithin.Vol2.Ch10SecDVE2
public import CFSG.Quasithin.Vol2.Ch10SecD211A

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecD

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13 CFSG.QuasithinUnique

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G}

theorem le_of_component (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat)
    (h : Hyp10 G T L I) (h3 : Case10_1_1Three T L I) (hc : fsuCVM T L I = ⊥) {t : G}
    (ht : t ∈ T) (htn : t ∉ Subgroup.normalizer (L : Set G)) {v1 x : G}
    (hv1 : v1 ∈ fsuUL T L I) (hv11 : v1 ≠ 1) (hxL : x ∈ L) (hxo : Odd (orderOf x))
    (hxv1 : x * v1 * x⁻¹ = v1) (hxC : x ∉ Subgroup.centralizer (fsuUL T L I : Set G))
    {U : Subgroup G} (hxU : x ∈ Subgroup.normalizer (U : Set G)) (hv1U : v1 ∈ U)
    {u1 u2 : G} (hu : u1 * u2 ∈ U) (hu1 : u1 ∈ fsuUL T L I)
    (hu2 : u2 ∈ ⁅fsuVM T L I, CFSG.conjugate L t⁆) (hu11 : u1 ≠ 1) (hu1v : u1 ≠ v1) :
    fsuUL T L I ≤ U := by
  have hxN : x ∈ Subgroup.normalizer (fsuUL T L I : Set G) := L_le_normalizer_V1 hxL
  have hfpf := fun {u : G} (hu : u ∈ fsuUL T L I) hxu =>
    fpf_of_odd h h3 hc hv1 hv11 hxN hxo hxv1 hxC hu hxu
  have hV := SecA.isElemAbelian_fsuVM h
  have hcomm : ∀ a ∈ fsuUL T L I, ∀ b ∈ fsuUL T L I, a * b = b * a := fun a ha b hb =>
    B2F.isElemAbelian_comm hV (V1_le_V ha) (V1_le_V hb)
  have hsq : ∀ a ∈ fsuUL T L I, a * a = 1 := fun a ha => by
    rw [← pow_two]; exact hV.2 a (V1_le_V ha)
  have hxu2 : x * u2 * x⁻¹ = u2 := by
    rw [(Subgroup.mem_centralizer_iff.mp (V2_le_centralizer_L h37 h38 h ht htn hu2) x hxL)]
    group
  set w := x * u1 * x⁻¹ * u1⁻¹ with hw
  have hxu1V : x * u1 * x⁻¹ ∈ fsuUL T L I := (Subgroup.mem_normalizer_iff.mp hxN u1).mp hu1
  have hwV : w ∈ fsuUL T L I := (fsuUL T L I).mul_mem hxu1V ((fsuUL T L I).inv_mem hu1)
  have hwU : w ∈ U := by
    have h1 : x * (u1 * u2) * x⁻¹ * (u1 * u2)⁻¹ ∈ U :=
      U.mul_mem ((Subgroup.mem_normalizer_iff.mp hxU _).mp hu) (U.inv_mem hu)
    have e : x * (u1 * u2) * x⁻¹ * (u1 * u2)⁻¹ = w := by
      calc x * (u1 * u2) * x⁻¹ * (u1 * u2)⁻¹ =
            (x * u1 * x⁻¹) * (x * u2 * x⁻¹) * u2⁻¹ * u1⁻¹ := by group
        _ = w := by rw [hxu2, hw]; group
    rwa [e] at h1
  have hxu1 : x * u1 * x⁻¹ = w * u1 := by rw [hw]; group
  have hw1 : w ≠ 1 := fun h1 => by
    rcases hfpf hu1 (Or.inl (by rw [hxu1, h1, one_mul])) with h2 | h2
    · exact hu11 h2
    · exact hu1v h2
  have hwv : w ≠ v1 := fun h1 => by
    rcases hfpf hu1 (Or.inr (by rw [hxu1, h1, hcomm v1 hv1 u1 hu1])) with h2 | h2
    · exact hu11 h2
    · exact hu1v h2
  set y := x * w * x⁻¹ with hy
  have hyV : y ∈ fsuUL T L I := (Subgroup.mem_normalizer_iff.mp hxN w).mp hwV
  have hyU : y ∈ U := (Subgroup.mem_normalizer_iff.mp hxU w).mp hwU
  have hy1 : y ≠ 1 := fun h1 => hw1 (by
    calc w = x⁻¹ * y * x := by rw [hy]; group
      _ = 1 := by rw [h1]; group)
  have hyv : y ≠ v1 := fun h1 => hwv (by
    calc w = x⁻¹ * y * x := by rw [hy]; group
      _ = x⁻¹ * (x * v1 * x⁻¹) * x := by rw [h1, hxv1]
      _ = v1 := by group)
  have hyw : y ≠ w := fun h1 => by
    rcases hfpf hwV (Or.inl h1) with h2 | h2
    · exact hw1 h2
    · exact hwv h2
  have hywv : y ≠ v1 * w := fun h1 => by
    rcases hfpf hwV (Or.inr (by rw [← hy, h1, hcomm v1 hv1 w hwV])) with h2 | h2
    · exact hw1 h2
    · exact hwv h2
  have hvw1 : v1 * w ≠ 1 := fun h1 => hwv (by
    calc w = v1 * (v1 * w) := by rw [← mul_assoc, hsq v1 hv1, one_mul]
      _ = v1 := by rw [h1, mul_one])
  have hvwv : v1 * w ≠ v1 := fun h1 => hw1 (by
    calc w = v1 * (v1 * w) := by rw [← mul_assoc, hsq v1 hv1, one_mul]
      _ = v1 * v1 := by rw [h1]
      _ = 1 := hsq v1 hv1)
  have hvww : v1 * w ≠ w := fun h1 => hv11 (by
    calc v1 = v1 * w * w⁻¹ := by group
      _ = 1 := by rw [h1, mul_inv_cancel])
  set S := U ⊓ fsuUL T L I with hS
  have hsub : ({1, v1, w, v1 * w, y} : Set G) ⊆ (S : Set G) := by
    intro a ha
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl
    · exact S.one_mem
    · exact ⟨hv1U, hv1⟩
    · exact ⟨hwU, hwV⟩
    · exact ⟨U.mul_mem hv1U hwU, (fsuUL T L I).mul_mem hv1 hwV⟩
    · exact ⟨hyU, hyV⟩
  have h5 : ({1, v1, w, v1 * w, y} : Set G).ncard = 5 := by
    rw [Set.ncard_insert_of_notMem, Set.ncard_insert_of_notMem, Set.ncard_insert_of_notMem,
      Set.ncard_pair hywv.symm]
    · simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
      exact ⟨hvww.symm, hyw.symm⟩
    · simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
      exact ⟨hwv.symm, hvwv.symm, hyv.symm⟩
    · simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
      exact ⟨hv11.symm, hw1.symm, hvw1.symm, hy1.symm⟩
  have hS5 : 5 ≤ Nat.card S := by
    rw [show Nat.card S = (S : Set G).ncard from Nat.card_coe_set_eq (S : Set G), ← h5]
    exact Set.ncard_le_ncard hsub (Set.toFinite _)
  have hS8 : Nat.card S ∣ 8 := card_V1 h3 hc ▸ Subgroup.card_dvd_of_le inf_le_right
  have hSV : S = fsuUL T L I := Subgroup.eq_of_le_of_card_ge inf_le_right (by
    rw [card_V1 h3 hc]
    have : Nat.card S ≤ 8 := Nat.le_of_dvd (by norm_num) hS8
    interval_cases (Nat.card S) <;> omega)
  rw [← hSV]
  exact inf_le_left

end CFSG.Quasithin.Vol2.Ch10.SecD
