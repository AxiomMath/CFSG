
module

public import CFSG.Sporadic.J4.QT2LocCntProofBase

public import CFSG.Sporadic.J4.QT2LocProof
public import CFSG.Sporadic.J4.QT2LocZProof

public section

namespace CFSG.Sporadic.J4.QT2

open CFSG.Sporadic.J4 CFSG.Sporadic.J4.Native CFSG.Sporadic.J4.QT CFSG.Sporadic.Th Matrix
open scoped Classical

theorem Dlt_ncard {ℓ : ℕ} (hℓ : ℓ < 7) :
    (Dlt ℓ).ncard = [1, 32643072, 82575360, 54405120, 3400320, 15180, 28336].getD ℓ 0 := by
  rw [Dlt_eq_orbit_rep]
  exact Certificates.certificate4008.2 ℓ hℓ

theorem Dlt_five_card (_hF : J4Facts) : (Dlt 5).ncard ≤ 15180 :=
  (Dlt_ncard (ℓ := 5) (by norm_num)).le

theorem Omega_subset (hM : MatFacts) (hF : J4Facts) {z : J} :
    Omega z ⊆ {v | v ∈ Dlt 0 ∧ RIn v z} ∪ {v | v ∈ Dlt 1 ∧ RIn v z} ∪ {v | v ∈ Dlt 2 ∧ RIn v z} ∪
      {v | v ∈ Dlt 3 ∧ RIn v z} ∪ {v | v ∈ Dlt 4 ∧ RIn v z} ∪ {v | v ∈ Dlt 5 ∧ RIn v z} ∪
      {v | v ∈ Dlt 6 ∧ RIn v z} := by
  intro v hv
  obtain ⟨g, hg, hE⟩ := hv
  obtain ⟨ℓ, hℓ, h, hh, h', hh', rfl⟩ := exists_rep hF g
  have hvD : v ∈ Dlt ℓ := by
    refine ⟨h, hh, ?_⟩
    rw [← hg, mul_smul, mul_smul, smul_root_of_mem_Hj hM hh']
    rfl
  have hR : RIn v z := ⟨_, hg, hE⟩
  interval_cases ℓ
  · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl ⟨hvD, hR⟩)))))
  · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr ⟨hvD, hR⟩)))))
  · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr ⟨hvD, hR⟩))))
  · exact Or.inl (Or.inl (Or.inl (Or.inr ⟨hvD, hR⟩)))
  · exact Or.inl (Or.inl (Or.inr ⟨hvD, hR⟩))
  · exact Or.inl (Or.inr ⟨hvD, hR⟩)
  · exact Or.inr ⟨hvD, hR⟩

theorem card_Omega_le (hF : J4Facts) {z : J} (hz : z ∈ Zl) : (Omega z).ncard ≤ 77 := by
  have hM := hF.mat
  obtain ⟨c1, c2, c3, c4, c5, c6⟩ := cands_parts
  have hZ := card_Zl hM
  have b0 : {v | v ∈ Dlt 0 ∧ RIn v z}.ncard ≤ 1 := by
    have := dlt_filter_bound hM hF 0 (m := 1771) (dl := 1) (by
      rw [← hZ]; exact Finset.card_le_card (by unfold ZE; exact Finset.filter_subset _ _))
      (Dlt_zero_card hM) hz
    omega
  have bz : ∀ ℓ, ℓ < 7 → (candZ (locMats ()) (locInvs ()) ℓ).length ≤ 0 →
      {v | v ∈ Dlt ℓ ∧ RIn v z}.ncard = 0 := by
    intro ℓ hℓ hc
    have := dlt_filter_bound hM hF ℓ (m := 0) (dl := (Dlt ℓ).ncard)
      (ZE_card_le hM hℓ (pathInv_get hℓ) hc) le_rfl hz
    omega
  have b1 := bz 1 (by norm_num) c1.le
  have b2 := bz 2 (by norm_num) c2.le
  have b3 := bz 3 (by norm_num) c3.le
  have b4 := bz 4 (by norm_num) c4.le
  have b5 : {v | v ∈ Dlt 5 ∧ RIn v z}.ncard ≤ 60 := by
    have := dlt_filter_bound hM hF 5 (m := 7) (dl := 15180)
      (ZE_card_le hM (by norm_num) (pathInv_get (by norm_num)) c5.le) (Dlt_five_card hF) hz
    omega
  have b6 : {v | v ∈ Dlt 6 ∧ RIn v z}.ncard ≤ 16 := by
    have := dlt_filter_bound hM hF 6 (m := 1) (dl := 28336)
      (ZE_card_le hM (by norm_num) (pathInv_get (by norm_num)) c6.le) (Dlt_six_card hF) hz
    omega
  refine (Set.ncard_le_ncard (Omega_subset hM hF) (Set.toFinite _)).trans ?_
  refine (Set.ncard_union_le _ _).trans ?_
  have u1 := Set.ncard_union_le ({v | v ∈ Dlt 0 ∧ RIn v z} ∪ {v | v ∈ Dlt 1 ∧ RIn v z} ∪
    {v | v ∈ Dlt 2 ∧ RIn v z} ∪ {v | v ∈ Dlt 3 ∧ RIn v z} ∪ {v | v ∈ Dlt 4 ∧ RIn v z})
    {v | v ∈ Dlt 5 ∧ RIn v z}
  have u2 := Set.ncard_union_le ({v | v ∈ Dlt 0 ∧ RIn v z} ∪ {v | v ∈ Dlt 1 ∧ RIn v z} ∪
    {v | v ∈ Dlt 2 ∧ RIn v z} ∪ {v | v ∈ Dlt 3 ∧ RIn v z}) {v | v ∈ Dlt 4 ∧ RIn v z}
  have u3 := Set.ncard_union_le ({v | v ∈ Dlt 0 ∧ RIn v z} ∪ {v | v ∈ Dlt 1 ∧ RIn v z} ∪
    {v | v ∈ Dlt 2 ∧ RIn v z}) {v | v ∈ Dlt 3 ∧ RIn v z}
  have u4 := Set.ncard_union_le ({v | v ∈ Dlt 0 ∧ RIn v z} ∪ {v | v ∈ Dlt 1 ∧ RIn v z})
    {v | v ∈ Dlt 2 ∧ RIn v z}
  have u5 := Set.ncard_union_le {v | v ∈ Dlt 0 ∧ RIn v z} {v | v ∈ Dlt 1 ∧ RIn v z}
  omega

theorem card_centralizer_Zl (hF : J4Facts) {z : J} (hz : z ∈ Zl)
    (h7 : 7 ∣ Nat.card ↥(Subgroup.centralizer ({z} : Set J)))
    (h11 : 11 ∣ Nat.card ↥(Subgroup.centralizer ({z} : Set J))) :
    Nat.card ↥(Subgroup.centralizer ({z} : Set J)) = 21799895040 := by
  have hM := hF.mat
  have hKM := card_eq_orbit_mul_inf (Subgroup.centralizer ({z} : Set J)) Hj w₀
    (fun g => ⟨mem_Hj_of_smul_root hF, smul_root_of_mem_Hj hM⟩)
  have hHM := card_eq_card_mul_centralizer Hj z Zl hz (fun h hh x hx => (Zl_conj hM h hh).1 x hx)
    (fun x hx => Zl_trans hM z hz x hx)
  rw [card_Hj hF, card_Zl hM] at hHM
  have hMval : Nat.card ↥(Subgroup.centralizer ({z} : Set J) ⊓ Hj) = 283115520 := by omega
  have hm77 : Nat.card ↥(MulAction.orbit (Subgroup.centralizer ({z} : Set J)) w₀) ≤ 77 := by
    have hsub : MulAction.orbit (Subgroup.centralizer ({z} : Set J)) w₀ ⊆ Omega z := by
      refine orbit_subset_of _ w₀ _ fun q hq => ?_
      refine ⟨q, rfl, ?_⟩
      have hc := comm_of_mem_centralizer hq
      have : q⁻¹ * z * q = z := by
        rw [mul_assoc, ← hc, ← mul_assoc, inv_mul_cancel, one_mul]
      rw [this]
      exact mem_Eg_of_mem_Zl hz
    rw [Nat.card_coe_set_eq]
    exact (Set.ncard_le_ncard hsub (Set.toFinite _)).trans (card_Omega_le hF hz)
  have hmpos : 0 < Nat.card ↥(MulAction.orbit (Subgroup.centralizer ({z} : Set J)) w₀) := by
    rw [Nat.card_coe_set_eq, Set.ncard_pos (Set.toFinite _)]
    exact ⟨w₀, MulAction.mem_orbit_self w₀⟩
  have hfin := final_arith _ hm77 hmpos (by rw [← hMval, ← hKM]; exact h7)
    (by rw [← hMval, ← hKM]; exact h11)
  rw [hKM, hMval, hfin]

theorem card_centralizer_z0 (hF : J4Facts) :
    Nat.card ↥(Subgroup.centralizer ({eta uJ 11 1131} : Set J)) = 21799895040 :=
  card_centralizer_Zl hF z0_mem_Zl (seven_dvd_card_centralizer hF) (eleven_dvd_card_centralizer hF)

theorem card_centralizer_of_mem_Zl (hF : J4Facts) {x : J} (hx : x ∈ Zl) :
    Nat.card ↥(Subgroup.centralizer ({x} : Set J)) = 21799895040 := by
  obtain ⟨h, -, e⟩ := Zl_trans hF.mat _ z0_mem_Zl x hx
  rw [← e, card_centralizer_singleton_conj]
  exact card_centralizer_z0 hF

end CFSG.Sporadic.J4.QT2
