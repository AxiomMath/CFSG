module

public import CFSG.RankThree.GF2n.Smith81.S81D6J4
public import CFSG.RankThree.GF2n.Smith81.S81YE4PairW
public import CFSG.RankThree.GF2n.Smith81.S81E7Conj

public section

namespace CFSG.RankThree.GF2n.Smith81.RootGenE4

open CFSG.LieType.Steinberg.Minuscule CFSG.Blueprint.Chevalley CFSG.RankThree.GF2n.Smith81
  CFSG.RankThree.GF2n.Smith81.E7Model CFSG.RankThree.GF2n.Smith81.D6Spin
  CFSG.RankThree.GF2n.Smith81.RootGen CFSG.RankThree.GF2n.Smith81.RootGenE5

variable
  {K : Type} [Field K]

private theorem range_xuWUnit_sub_one_le [CharP K 2] {β : Fin (Tag.rank .E7) → ℤ} (hβ : β ∈ Perp)
    (c : K) :
    LinearMap.range (((xuWUnit hβ c : (Module.End K (W K))ˣ) : Module.End K (W K)) - 1) ≤
      LinearMap.range (EW K β) := by
  rintro _ ⟨v, rfl⟩
  refine LinearMap.mem_range.mpr ⟨c • v, ?_⟩
  simp [xuWUnit_apply]

private theorem odd_dvd_four_eq_one {n : ℕ} (hodd : Odd n) (hdvd : n ∣ 4) : n = 1 := by
  rw [Nat.odd_iff] at hodd
  have hpos : 0 < n := Nat.pos_of_ne_zero (by rintro rfl; norm_num at hdvd)
  have hle : n ≤ 4 := Nat.le_of_dvd (by norm_num) hdvd
  interval_cases n <;> omega

theorem ranges_disjoint_theta4 [CharP K 2] (a b : K) :
    LinearMap.range (((xuWUnit theta4_mem_Perp a : (Module.End K (W K))ˣ) : Module.End K (W K)) - 1) ⊓
      LinearMap.range (((xuWUnit (neg_mem_Perp theta4_mem_Perp) b : (Module.End K (W K))ˣ) :
        Module.End K (W K)) - 1) = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro w hw
  obtain ⟨h1, h2⟩ := Submodule.mem_inf.1 hw
  have hA := range_xuWUnit_sub_one_le theta4_mem_Perp a h1
  have hB := range_xuWUnit_sub_one_le (neg_mem_Perp theta4_mem_Perp) b h2
  rw [range_EW theta4_mem_Perp, Finsupp.mem_supported'] at hA
  rw [range_EW (neg_mem_Perp theta4_mem_Perp), Finsupp.mem_supported'] at hB
  ext c
  rw [Finsupp.zero_apply]
  by_cases hc : pr (c : Fin e7Data.d) theta4 = 1
  · have hc' : ¬ pr (c : Fin e7Data.d) (-theta4) = 1 := by
      rw [pr_neg, hc]
      norm_num
    exact hB c hc'
  · exact hA c hc

theorem xuW_theta4_neg_ne_one [CharP K 2] {a b : K} (ha : a ≠ 0) (hb : b ≠ 0) :
    xuWUnit theta4_mem_Perp a * xuWUnit (neg_mem_Perp theta4_mem_Perp) b ≠ 1 := by
  intro h
  obtain ⟨b2, hb2⟩ : ∃ b2 : Idx0, pr (b2 : Fin e7Data.d) theta4 = -1 := by
    have hpos : 0 < (idx0.filter fun a => pr a theta4 = -1).card := by
      rw [(card_pr_perp theta4_mem_Perp).2.1]
      norm_num
    obtain ⟨a', ha'⟩ := Finset.card_pos.1 hpos
    exact ⟨⟨a', (Finset.mem_filter.1 ha').1⟩, (Finset.mem_filter.1 ha').2⟩
  have hb1 : pr ((shiftW theta4 b2 : Idx0) : Fin e7Data.d) theta4 = 1 := by
    rw [shiftW_val theta4_mem_Perp hb2]
    exact pr_shift_self isRoot_theta4 hb2
  have hne : b2 ≠ shiftW theta4 b2 := by
    intro h'
    rw [← h', hb2] at hb1
    norm_num at hb1
  have hn : ¬ pr (b2 : Fin e7Data.d) (-theta4) = -1 := by
    rw [pr_neg, hb2]
    norm_num
  have hY : (xuWUnit (neg_mem_Perp theta4_mem_Perp) b : Module.End K (W K))
      (Finsupp.single b2 1) = Finsupp.single b2 1 := by
    rw [xuWUnit_apply, EW_single (neg_mem_Perp theta4_mem_Perp), if_neg hn, smul_zero, add_zero]
  have hX : (xuWUnit theta4_mem_Perp a : Module.End K (W K)) (Finsupp.single b2 1) =
      Finsupp.single b2 1 + a • Finsupp.single (shiftW theta4 b2) 1 := by
    rw [xuWUnit_apply, EW_single theta4_mem_Perp, if_pos hb2]
  have hkey := congrArg (fun u : (Module.End K (W K))ˣ =>
    (u : Module.End K (W K)) (Finsupp.single b2 1)) h
  simp only [Units.val_mul, Module.End.mul_apply, Units.val_one, Module.End.one_apply] at hkey
  rw [hY, hX] at hkey
  have h3 := congrArg (fun f : W K => f (shiftW theta4 b2)) hkey
  simp [Finsupp.single_apply, hne] at h3
  exact ha h3

theorem xuW_theta4_neg_odd [Finite K] [CharP K 2] {a b : K} (ha : a ≠ 0) (hb : b ≠ 0) :
    Odd (orderOf (xuWUnit theta4_mem_Perp a * xuWUnit (neg_mem_Perp theta4_mem_Perp) b)) := by
  rw [xuWUnit_theta4, xuWUnit_neg_theta4, ← map_mul jHomW]
  have hodd : Odd (orderOf (MinData.Valid.slLower K a * MinData.Valid.slUpper K b)) := by
    refine sl2_orderOf_odd _ ?_ ?_
    · rw [slLower_mul_slUpper_apply_10]
      exact ha
    · have ht := trace_low_up a b
      rw [Matrix.trace_fin_two] at ht
      rw [ht]
      exact mul_ne_zero ha hb
  exact Odd.of_dvd_nat hodd (orderOf_map_dvd jHomW _)

theorem e4_odd_disj [CharP K 2] {r s : W K ≃ₗ[K] W K} (hr : IsRt4 r) (hs : IsRt4 s)
    (hodd : Odd (orderOf (r * s))) (hne : r * s ≠ 1) :
    LinearMap.range ((r : W K →ₗ[K] W K) - 1) ⊓ LinearMap.range ((s : W K →ₗ[K] W K) - 1) = ⊥ := by
  obtain ⟨E, a, b, δ, hδ, -, -, hEr, hEs, hpow⟩ := e4_pairNF_W hr hs
  have hδe : δ = -theta4 := by
    by_contra hne'
    have h4 : (r * s) ^ 4 = 1 := hpow hne'
    have hone : orderOf (r * s) = 1 := odd_dvd_four_eq_one hodd (orderOf_dvd_of_pow_eq_one h4)
    exact hne (orderOf_eq_one_iff.1 hone)
  subst hδe
  have hEs' : act4 E * s * (act4 E)⁻¹ = vAut0 K (xuWUnit (neg_mem_Perp theta4_mem_Perp) b) := hEs
  have hcr : act4 E * r = vAut0 K (xuWUnit theta4_mem_Perp a) * act4 E := by
    rw [← hEr, inv_mul_cancel_right]
  have hcs : act4 E * s = vAut0 K (xuWUnit (neg_mem_Perp theta4_mem_Perp) b) * act4 E := by
    rw [← hEs', inv_mul_cancel_right]
  have hpr : ∀ u : W K, act4 E (r u) =
      (xuWUnit theta4_mem_Perp a : Module.End K (W K)) (act4 E u) := by
    intro u
    have h := congrArg (fun f : W K ≃ₗ[K] W K => f u) hcr
    simpa only [LinearEquiv.mul_apply, vAut0_apply] using h
  have hps : ∀ u : W K, act4 E (s u) =
      (xuWUnit (neg_mem_Perp theta4_mem_Perp) b : Module.End K (W K)) (act4 E u) := by
    intro u
    have h := congrArg (fun f : W K ≃ₗ[K] W K => f u) hcs
    simpa only [LinearEquiv.mul_apply, vAut0_apply] using h
  have hkr : ∀ w ∈ LinearMap.range ((r : W K →ₗ[K] W K) - 1),
      act4 E w ∈ LinearMap.range ((xuWUnit theta4_mem_Perp a : Module.End K (W K)) - 1) := by
    rintro _ ⟨v, rfl⟩
    refine LinearMap.mem_range.mpr ⟨act4 E v, ?_⟩
    simp only [LinearMap.sub_apply, Module.End.one_apply, LinearEquiv.coe_coe, map_sub, hpr]
  have hks : ∀ w ∈ LinearMap.range ((s : W K →ₗ[K] W K) - 1),
      act4 E w ∈ LinearMap.range ((xuWUnit (neg_mem_Perp theta4_mem_Perp) b : Module.End K (W K)) - 1) := by
    rintro _ ⟨v, rfl⟩
    refine LinearMap.mem_range.mpr ⟨act4 E v, ?_⟩
    simp only [LinearMap.sub_apply, Module.End.one_apply, LinearEquiv.coe_coe, map_sub, hps]
  rw [Submodule.eq_bot_iff]
  intro w hw
  obtain ⟨h1, h2⟩ := Submodule.mem_inf.1 hw
  have hmem : act4 E w ∈ LinearMap.range ((xuWUnit theta4_mem_Perp a : Module.End K (W K)) - 1) ⊓
      LinearMap.range ((xuWUnit (neg_mem_Perp theta4_mem_Perp) b : Module.End K (W K)) - 1) :=
    Submodule.mem_inf.2 ⟨hkr w h1, hks w h2⟩
  rw [ranges_disjoint_theta4 a b, Submodule.mem_bot] at hmem
  exact (LinearEquiv.map_eq_zero_iff (act4 E)).1 hmem

end CFSG.RankThree.GF2n.Smith81.RootGenE4
