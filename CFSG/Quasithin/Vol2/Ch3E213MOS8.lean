module

public import CFSG.Quasithin.Vol2.Ch3E213MOS7
public import CFSG.GH74.GLS.IVK.L2.F1
public import CFSG.Quasithin.Vol2.Ch3E213MOS3

public section

namespace CFSG.Quasithin.Ch3E213M.OS

open CFSG.Open CFSG.GH74.GLS.IVK CFSG.GH74.GLS

theorem exists_inf_eq_and_hall {X : Type*} [Group X] {D T₀ V₀ : Subgroup X} (hDn : D.Normal)
    (hidx : D.index = 2) (hVn : T₀ ≤ Subgroup.normalizer (V₀ : Set X))
    (hV4 : 4 ≤ Nat.card V₀) (hle2 : Nat.card ↥(V₀ ⊓ D) ≤ 2) :
    ∃ w ∈ V₀ ⊓ D, orderOf w = 2 ∧ (∀ x ∈ V₀ ⊓ D, x = 1 ∨ x = w) ∧
      ∃ v ∈ V₀, v ∉ D ∧ ∀ g ∈ T₀, g * v * g⁻¹ = v ∨ g * v * g⁻¹ = w * v := by
  have := hDn
  have hrel : D.relIndex V₀ ≤ 2 := by
    have h := Subgroup.relIndex_dvd_index_of_normal D V₀
    rw [hidx] at h
    exact Nat.le_of_dvd two_pos h
  have hmul : D.relIndex V₀ * Nat.card ↥(V₀ ⊓ D) = Nat.card V₀ := by
    rw [inf_comm]
    exact Subgroup.relIndex_mul_card (H := D) (K := V₀)
  have h2 : Nat.card ↥(V₀ ⊓ D) = 2 := by
    have h4 : 4 ≤ D.relIndex V₀ * Nat.card ↥(V₀ ⊓ D) := by rw [hmul]; exact hV4
    have h5 : 4 ≤ 2 * Nat.card ↥(V₀ ⊓ D) := h4.trans (Nat.mul_le_mul_right _ hrel)
    omega
  obtain ⟨w, hw, hw2, hall⟩ := exists_eq_of_card_eq_two h2
  have hnle : ¬ V₀ ≤ D := by
    intro hle
    rw [Subgroup.relIndex_eq_one.mpr hle, one_mul, h2] at hmul
    omega
  obtain ⟨v, hv, hvD⟩ := IsConcreteLE.not_le_iff_exists.mp hnle
  refine ⟨w, hw, hw2, hall, v, hv, hvD, fun g hg => ?_⟩
  have hgv : g * v * g⁻¹ ∈ V₀ := (Subgroup.mem_normalizer_iff.mp (hVn hg) v).mp hv
  have hgvD : g * v * g⁻¹ ∉ D := fun h => hvD (by
    have := hDn.conj_mem _ h g⁻¹
    simpa [mul_assoc] using this)
  have hprod : g * v * g⁻¹ * v⁻¹ ∈ V₀ ⊓ D := by
    refine ⟨V₀.mul_mem hgv (V₀.inv_mem hv), ?_⟩
    show g * v * g⁻¹ * v⁻¹ ∈ D
    rw [Subgroup.mul_mem_iff_of_index_two hidx]
    exact ⟨fun h => absurd h hgvD, fun h => absurd (inv_mem_iff.mp h) hvD⟩
  rcases hall _ hprod with h | h
  · exact Or.inl (mul_inv_eq_one.mp h)
  · exact Or.inr (mul_inv_eq_iff_eq_mul.mp h)

theorem sq_facts {p : ℕ} (hp : p.Prime) (hp3 : 3 < p) :
    ((p ^ 2 : ℕ) : ℤ) ≡ 1 [ZMOD 4] ∧ 3 ∣ p ^ 2 - 1 := by
  obtain ⟨j, hj⟩ := hp.odd_of_ne_two (by omega)
  refine ⟨?_, ?_⟩
  · rw [Int.modEq_iff_dvd, hj]
    exact ⟨-((j : ℤ) ^ 2 + j), by push_cast; ring⟩
  · have h3 : p % 3 ≠ 0 := by
      intro h
      have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).mp (Nat.dvd_of_mod_eq_zero h)
      omega
    have hsq : p ^ 2 % 3 = 1 := by
      rw [Nat.pow_mod]
      have : p % 3 = 1 ∨ p % 3 = 2 := by omega
      rcases this with h | h <;> rw [h]
    have hp1 : 1 ≤ p ^ 2 := Nat.one_le_pow _ _ hp.pos
    omega

variable {F : Type} [Field F] [Finite F] {K : Type} [Group K] [Finite K]

theorem exists_fieldInv (hF : L2Field F) (e : K ≃* L2 F) (N : L2Notation e) {p : ℕ}
    (hp : p.Prime) (hq : Nat.card F = p ^ 2) :
    ∃ f₀ ∈ N.R, orderOf f₀ = 2 ∧ (∀ x ∈ fieldAutSub e, x = 1 ∨ x = f₀) ∧
      f₀ ∉ innDiagSub e ∧ ∀ x ∈ N.P, x * f₀ = f₀ * x := by
  have h2 : Nat.card (fieldAutSub e) = 2 := (ivk_1_2e F hF K e).2.2 p 2 hp hq
  obtain ⟨f₀, hf₀, hf₀2, hall⟩ := exists_eq_of_card_eq_two h2
  have hf₀R : f₀ ∈ N.R := ⟨fieldAutSub_le_T N h2 hf₀, hf₀⟩
  refine ⟨f₀, hf₀R, hf₀2, hall, fun hD => ?_, fun x hx => N.R_cent f₀ hf₀R hf₀2 x hx⟩
  have h1 : f₀ ∈ innDiagSub e ⊓ fieldAutSub e := ⟨hD, hf₀⟩
  rw [innDiagSub_inf_fieldAutSub e, Subgroup.mem_bot] at h1
  rw [h1, orderOf_one] at hf₀2
  exact absurd hf₀2 (by norm_num)

omit [Finite K] in
theorem index_innDiagSub {e : K ≃* L2 F} {f₀ : MulAut K} (hf₀2 : orderOf f₀ = 2)
    (hall : ∀ x ∈ fieldAutSub e, x = 1 ∨ x = f₀) (hf₀D : f₀ ∉ innDiagSub e) :
    (innDiagSub e).index = 2 :=
  Subgroup.index_eq_two_iff_exists_notMem_and.mpr
    ⟨f₀, hf₀D, fun b => (mem_innDiag_or hf₀2 hall b).symm⟩

theorem mem_of_comm (hF : L2Field F) {e : K ≃* L2 F} (N : L2Notation e) {n : ℕ}
    (hn : Nat.card N.P = 2 ^ n) (hn4 : 4 ≤ n) {w x : MulAut K} (hwP : w ∈ N.P) (hw1 : w ≠ 1)
    (hwc : ∀ y ∈ N.P, w * y = y * w) (hxP : x ∈ N.P) (hx2 : x * x = 1)
    (hcomm : ∀ g ∈ N.P, g * x * g⁻¹ = x ∨ g * x * g⁻¹ = w * x) : x = 1 ∨ x = w := by
  obtain ⟨k, hk, -, ⟨χ⟩⟩ := P_dihedral_model hF N n hn
  have h16 : 2 ^ 4 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn4
  have h4 : 4 ∣ 2 ^ n := by
    have := pow_dvd_pow 2 (show 2 ≤ n by omega)
    simpa using this
  have hke : Even k := ⟨k / 2, by omega⟩
  have hk5 : 5 ≤ k := by omega
  have hWZ : χ ⟨w, hwP⟩ ∈ Subgroup.center (DihedralGroup k) := by
    rw [Subgroup.mem_center_iff]
    intro d
    obtain ⟨d', rfl⟩ := χ.surjective d
    rw [← map_mul, ← map_mul]
    exact congrArg χ (Subtype.ext (hwc _ d'.2).symm)
  set g : ↥N.P := χ.symm (DihedralGroup.r 1) with hg
  have hc : DihedralGroup.r 1 * χ ⟨x, hxP⟩ * (DihedralGroup.r 1)⁻¹ * (χ ⟨x, hxP⟩)⁻¹ ∈
      Subgroup.center (DihedralGroup k) := by
    have e1 : DihedralGroup.r 1 * χ ⟨x, hxP⟩ * (DihedralGroup.r 1)⁻¹ * (χ ⟨x, hxP⟩)⁻¹ =
        χ (g * ⟨x, hxP⟩ * g⁻¹ * (⟨x, hxP⟩ : ↥N.P)⁻¹) := by
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, hg, MulEquiv.apply_symm_apply]
    rw [e1]
    rcases hcomm g g.2 with h | h
    · have h1 : g * ⟨x, hxP⟩ * g⁻¹ * (⟨x, hxP⟩ : ↥N.P)⁻¹ = 1 := by
        apply Subtype.ext
        show (g : MulAut K) * x * (g : MulAut K)⁻¹ * x⁻¹ = 1
        rw [h, mul_inv_cancel]
      rw [h1, map_one]
      exact Subgroup.one_mem _
    · have h1 : g * ⟨x, hxP⟩ * g⁻¹ * (⟨x, hxP⟩ : ↥N.P)⁻¹ = ⟨w, hwP⟩ := by
        apply Subtype.ext
        show (g : MulAut K) * x * (g : MulAut K)⁻¹ * x⁻¹ = w
        rw [h, mul_inv_cancel_right]
      rw [h1]
      exact hWZ
  have hXX : χ ⟨x, hxP⟩ * χ ⟨x, hxP⟩ = 1 := by
    rw [← map_mul]
    have h1 : (⟨x, hxP⟩ : ↥N.P) * ⟨x, hxP⟩ = 1 := Subtype.ext hx2
    rw [h1, map_one]
  have hXZ := Dih.mem_center_of_comm hke hk5 hXX hc
  have hxc : ∀ y ∈ N.P, x * y = y * x := by
    intro y hy
    have h1 := (Subgroup.mem_center_iff.mp hXZ) (χ ⟨y, hy⟩)
    rw [← map_mul, ← map_mul] at h1
    exact (congrArg Subtype.val (χ.injective h1)).symm
  by_cases hx1 : x = 1
  · exact Or.inl hx1
  · exact Or.inr (P_central_unique hF N n hn (by omega) hxP hwP hx1 hw1 hxc hwc)

omit [Finite K] in
theorem comm_of_inf_eq {e : K ≃* L2 F} (N : L2Notation e) {T₀ : Subgroup (MulAut K)}
    (hT : T₀ ≤ N.T) (hTP : T₀ ⊓ N.Pt = N.P) {f₀ : MulAut K} (hf₀2 : orderOf f₀ = 2)
    (hall : ∀ x ∈ fieldAutSub e, x = 1 ∨ x = f₀) (hf₀T : f₀ ∈ T₀)
    (hf₀P : ∀ x ∈ N.P, x * f₀ = f₀ * x) : ∀ g ∈ T₀, g * f₀ = f₀ * g := by
  intro g hg
  rcases mem_innDiag_or hf₀2 hall g with h | h
  · have hgPt : g ∈ T₀ ⊓ N.Pt := ⟨hg, hT hg, h⟩
    rw [hTP] at hgPt
    exact hf₀P g hgPt
  · have hgf : g * f₀ ∈ T₀ := T₀.mul_mem hg hf₀T
    have hgPt : g * f₀ ∈ T₀ ⊓ N.Pt := ⟨hgf, hT hgf, h⟩
    rw [hTP] at hgPt
    have h1 := hf₀P _ hgPt
    have h2 : g * f₀ * f₀ = f₀ * g * f₀ := by rw [h1, mul_assoc]
    exact mul_right_cancel h2

theorem false_of_Pt_le (hF : L2Field F) {e : K ≃* L2 F} (N : L2Notation e)
    (hn : Nat.card N.P = 2 ^ 3) {f₀ : MulAut K} (hf₀R : f₀ ∈ N.R) (hf₀2 : orderOf f₀ = 2)
    (hf₀P : ∀ y ∈ N.P, y * f₀ = f₀ * y) {w x : MulAut K} (hwP : w ∈ N.P) (hw1 : w ≠ 1)
    (hww : w * w = 1) (hwc : ∀ y ∈ N.P, w * y = y * w) (hxP : x ∈ N.P) (hx2 : x * x = 1)
    (hx1 : x ≠ 1) (hxw : x ≠ w)
    (hall : ∀ g ∈ N.Pt, g * (x * f₀) * g⁻¹ = x * f₀ ∨ g * (x * f₀) * g⁻¹ = w * (x * f₀)) :
    False := by
  obtain ⟨φ⟩ : Nonempty (↥N.Pt ≃* DihedralGroup 8) := Pt_dihedral_model hF N 3 hn
  have htw : N.t * w * N.t⁻¹ = w := t_comm_z hF N 3 hn le_rfl hwP hw1 hwc
  have hwcPt : ∀ g ∈ N.Pt, g * w = w * g := by
    intro g hg
    obtain ⟨-, -, hPt, -⟩ := ivk_1_2d F hF K e N
    have htn : Subgroup.zpowers N.t ≤ Subgroup.normalizer (N.P : Set (MulAut K)) :=
      (Subgroup.zpowers_le).mpr (le_normalizer_P N N.t_mem)
    have hg' : g ∈ N.P ⊔ Subgroup.zpowers N.t := by rw [hPt]; exact hg
    obtain ⟨a, ha, b, hb, rfl⟩ := E2P.exists_mul_of_mem_sup_of_le_normalizer' htn hg'
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
    have htc : Commute N.t w := by
      show N.t * w = w * N.t
      calc N.t * w = N.t * w * N.t⁻¹ * N.t := by group
        _ = w * N.t := by rw [htw]
    have h1 : Commute (N.t ^ j) w := htc.zpow_left j
    calc a * N.t ^ j * w = a * (N.t ^ j * w) := mul_assoc _ _ _
      _ = a * (w * N.t ^ j) := by rw [h1.eq]
      _ = a * w * N.t ^ j := (mul_assoc _ _ _).symm
      _ = w * a * N.t ^ j := by rw [hwc a ha]
      _ = w * (a * N.t ^ j) := mul_assoc _ _ _
  have hF1 := fInvNotCentPt F hF K e N f₀ hf₀R hf₀2
  have hxw' : w * x = x * w := hwc x hxP
  have hall' : ∀ g ∈ N.Pt, g * x * g⁻¹ = x ∨ g * x * g⁻¹ = w * x := by
    intro g hg
    by_cases hgP : g ∈ N.P
    · have hgf : f₀ * g⁻¹ = g⁻¹ * f₀ := (hf₀P _ (N.P.inv_mem hgP)).symm
      have h1 : g * (x * f₀) * g⁻¹ = g * x * g⁻¹ * f₀ := by
        calc g * (x * f₀) * g⁻¹ = g * x * (f₀ * g⁻¹) := by group
          _ = g * x * (g⁻¹ * f₀) := by rw [hgf]
          _ = g * x * g⁻¹ * f₀ := by group
      rcases hall g hg with h | h
      · rw [h1] at h
        exact Or.inl (mul_right_cancel h)
      · rw [h1, ← mul_assoc] at h
        exact Or.inr (mul_right_cancel h)
    · have hgi : g⁻¹ ∈ N.Pt := N.Pt.inv_mem hg
      have hgiP : g⁻¹ ∉ N.P := fun h => hgP (by simpa using N.P.inv_mem h)
      have hd := f_conj_d hF N 3 hn hf₀R hf₀2 hF1 hwP hw1 hwc hgi hgiP
      have hgf : f₀ * g⁻¹ = g⁻¹ * w * f₀ := by
        calc f₀ * g⁻¹ = f₀ * g⁻¹ * f₀⁻¹ * f₀ := by group
          _ = g⁻¹ * w * f₀ := by rw [hd]
      have h1 : g * (x * f₀) * g⁻¹ = g * x * g⁻¹ * w * f₀ := by
        calc g * (x * f₀) * g⁻¹ = g * x * (f₀ * g⁻¹) := by group
          _ = g * x * (g⁻¹ * w * f₀) := by rw [hgf]
          _ = g * x * g⁻¹ * w * f₀ := by group
      rcases hall g hg with h | h
      · rw [h1] at h
        have h2 : g * x * g⁻¹ * w = x := mul_right_cancel h
        right
        calc g * x * g⁻¹ = g * x * g⁻¹ * w * w := by rw [mul_assoc _ w w, hww, mul_one]
          _ = x * w := by rw [h2]
          _ = w * x := hxw'.symm
      · rw [h1, ← mul_assoc] at h
        have h2 : g * x * g⁻¹ * w = w * x := mul_right_cancel h
        left
        calc g * x * g⁻¹ = g * x * g⁻¹ * w * w := by rw [mul_assoc _ w w, hww, mul_one]
          _ = w * x * w := by rw [h2]
          _ = x * w * w := by rw [hxw']
          _ = x := by rw [mul_assoc, hww, mul_one]
  exact false_of_conj_mem φ (P_le_Pt N hxP) (P_le_Pt N hwP) hx2 hx1 hxw hw1 hwcPt hall'

end CFSG.Quasithin.Ch3E213M.OS
