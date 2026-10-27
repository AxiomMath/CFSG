module

public import CFSG.Quasithin.Vol2.Ch10SecDXI4

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecD

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13 CFSG.QuasithinUnique

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G}

omit [Finite G] in
theorem mem_normalizer_kOf {W : Subgroup G} {v g : G} (hgN : g ∈ Subgroup.normalizer (W : Set G))
    (hgv : g * v = v * g) : g ∈ Subgroup.normalizer (kOf W v : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro k
  refine ⟨conj_mem_kOf hgN hgv, fun hk => ?_⟩
  have hv' : g⁻¹ * v = v * g⁻¹ := by
    calc g⁻¹ * v = g⁻¹ * (v * g) * g⁻¹ := by group
      _ = v * g⁻¹ := by rw [← hgv]; group
  have := conj_mem_kOf (Subgroup.inv_mem _ hgN) hv' hk
  simpa [mul_assoc] using this

theorem mem_centralizer_V2 (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat)
    (h : Hyp10 G T L I) {t : G} (ht : t ∈ T) (htn : t ∉ Subgroup.normalizer (L : Set G)) {l : G}
    (hl : l ∈ L) :
    l ∈ Subgroup.centralizer ((⁅fsuVM T L I, CFSG.conjugate L t⁆ : Subgroup G) : Set G) :=
  Subgroup.mem_centralizer_iff.mpr fun _ hw =>
    ((Subgroup.mem_centralizer_iff.mp (V2_le_centralizer_L h37 h38 h ht htn hw)) l hl).symm

theorem mem_of_pow_mul_mem
    (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat)
    (h : Hyp10 G T L I) (h3 : Case10_1_1Three T L I) (hc : fsuCVM T L I = ⊥) {t v₁ v₂ : G}
    (hd : IsData10_2_11 T L I t v₁ v₂) {x : G} (hxL : x ∈ L) (hxX : x ∈ Xz T L (v₁ * v₂))
    (hxo : Odd (orderOf x)) (hxC : x ∉ Subgroup.centralizer (fsuUL T L I : Set G))
    {Y : Subgroup G} (hQY : pCoreOf 2 (Xz T L (v₁ * v₂)) ≤ Y) (hYX : Y ≤ Xz T L (v₁ * v₂))
    (hTY : T ≤ Subgroup.normalizer (Y : Set G)) {y : G} (hyY : y ∈ Y) {i : ℕ} (hi3 : i % 3 ≠ 0)
    (hi : x ^ i * y ∈ kOf (fsuUL T L I) v₁) : x ∈ Y := by
  obtain ⟨s, hsTL, hs⟩ := exists_mul_conj_mem_kOf h37 h38 h h3 hc hd hxX hxo hxC
  have hd' := hd
  obtain ⟨ht, htn, hv1, -, hv2, -⟩ := hd'
  obtain ⟨hxN, hxv, -, -⟩ := mem_normalizer_V12_of_mem_Xz h37 h38 h hc hd hxX
  obtain ⟨-, -, hyN2, hyv2⟩ := mem_normalizer_V12_of_mem_Xz h37 h38 h hc hd (hYX hyY)
  have hsN : s ∈ Subgroup.normalizer (fsuUL T L I : Set G) := L_le_normalizer_V1 hsTL.2
  have hsv : s * v₁ = v₁ * s := (Subgroup.mem_centralizer_iff.mp hv1.2) s (inf_le_T1 hsTL)
  have hkey := pow_mul_mem_of (mem_normalizer_kOf hxN hxv) (mem_normalizer_kOf hsN hsv) hs hi
  have hsY : s * y * s⁻¹ ∈ Y := (Subgroup.mem_normalizer_iff.mp (hTY hsTL.1) y).mp hyY
  have hy'Y : y * (s * y * s⁻¹)⁻¹ ∈ Y := Y.mul_mem hyY (Y.inv_mem hsY)
  have hK2s := mem_kOf_of_mem_centralizer hv2.1 (mem_centralizer_V2 h37 h38 h ht htn hsTL.2)
  have hK2x := mem_kOf_of_mem_centralizer hv2.1 (mem_centralizer_V2 h37 h38 h ht htn hxL)
  have hy'2 : y * (s * y * s⁻¹)⁻¹ ∈ kOf ⁅fsuVM T L I, CFSG.conjugate L t⁆ v₂ := by
    have e : y * (s * y * s⁻¹)⁻¹ = (y * s * y⁻¹) * s⁻¹ := by group
    rw [e]
    exact Subgroup.mul_mem _ (conj_mem_kOf hyN2 hyv2 hK2s) (Subgroup.inv_mem _ hK2s)
  have hx2i : x ^ (2 * i) ∈ Y := by
    have h1 := hQY (kOf_inf_le_pCoreOf h37 h38 h hc hd
      ⟨⟨Subgroup.mul_mem _ (Subgroup.pow_mem _ hxX _) (hYX hy'Y), hkey⟩,
        Subgroup.mul_mem _ (Subgroup.pow_mem _ hK2x _) hy'2⟩)
    have := Y.mul_mem h1 (Y.inv_mem hy'Y)
    rwa [mul_inv_cancel_right] at this
  have hx3 : x ^ 3 = 1 := pow_three_eq_one_of_mem h37 h38 h h3 hc hd (oTwoUpper_le _ hxX) hxo
  have hmod : x ^ (2 * i) = x ^ (2 * (i % 3)) := by
    rw [show 2 * i = 2 * (i % 3) + 3 * (2 * (i / 3)) by omega, pow_add, pow_mul x 3, hx3,
      one_pow, mul_one]
  rw [hmod] at hx2i
  have h4 : x ^ 4 = x := by rw [show 4 = 3 + 1 by norm_num, pow_add, hx3, one_mul, pow_one]
  rcases (by omega : i % 3 = 1 ∨ i % 3 = 2) with h1 | h1
  · rw [h1] at hx2i
    rw [← h4, show 4 = 2 * 2 by norm_num, pow_mul]
    exact Y.pow_mem hx2i 2
  · rw [h1] at hx2i
    rwa [show 2 * 2 = 4 by norm_num, h4] at hx2i

end CFSG.Quasithin.Vol2.Ch10.SecD
