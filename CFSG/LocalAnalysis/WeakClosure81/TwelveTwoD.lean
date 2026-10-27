module

public import CFSG.LocalAnalysis.WeakClosure81.TwelveCartanRel
public import CFSG.LocalAnalysis.WeakClosure81.TwelvePartOne
public import CFSG.LocalAnalysis.WeakClosure81.TwelveTwoC

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.SignalizerFunctorTheorem.Quadratic CFSG.Quasithin.G11 CFSG.Open Subgroup
open CFSG.GH74.Uniqueness.Bender

section TwoD

variable {G : Type} [Group G] {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
  {n m : ℕ}

theorem Setting12One.m_le_n {ρ : G →* LGL 2 V} {B A : Subgroup G}
    {Z : Submodule (ZMod 2) V} (h : Setting12One ρ B Z A n m) : m ≤ n := by
  haveI : Finite G := rankOne_finite h.type
  obtain ⟨S, hSB⟩ := exists_sylow_of_isBorelIn h.borel
  have hAS : A ≤ (S : Subgroup G) :=
    le_sylow_of_le_normalizer (IsElemAbelian.isPGroup h.A_elem) (hSB ▸ h.A_le_B)
  have h1 := (rankOne_card_elemAbelian_le h.type hAS h.A_elem).1
  rw [h.A_card] at h1
  exact (Nat.pow_le_pow_iff_right (by norm_num)).1 h1

theorem eq_zero_of_mem_commSpace_of_inverted
    {ρ : G →* LGL 2 V} {B A : Subgroup G} {Z : Submodule (ZMod 2) V}
    (h : Setting12One ρ B Z A n m) (hmin : ∀ L : Subgroup G, A ≤ L → ¬ L ≤ B → L = ⊤)
    {t : G} {T : Subgroup G} (ht : t * t = 1) (hTinv : ∀ x ∈ T, t * x * t = x⁻¹)
    (hTodd : Odd (Nat.card T)) (W : Submodule (ZMod 2) V) {x : G} (hxT : x ∈ T) (hx1 : x ≠ 1)
    {y : V} (hy : y ∈ commSpace (T.map ρ) W) (hfix : ρ x y = y) : y = 0 := by
  haveI : Finite G := rankOne_finite h.type
  have hxodd : Odd (orderOf x) := odd_orderOf_of_odd_card hTodd hxT
  have hfm := twelveOne_fix_of_inverted h hmin ht (hTinv x hxT) hxodd hx1
  have hle : commSpace (T.map ρ) W ≤ commSub ρ.range := by
    rw [commSpace_le_iff]
    intro k hk u _
    exact Submodule.subset_span ⟨k, Subgroup.map_le_range ρ T hk, u, rfl⟩
  have hycomm : y ∈ commSub ρ.range := hle hy
  have hyfm : y ∈ fixMod (cE ρ.range) (ρ x) := by
    rw [mem_fixMod, hfix, sub_self]
    exact Submodule.zero_mem _
  have hycE : y ∈ cE ρ.range := hfm ⟨hyfm, hycomm⟩
  exact eq_zero_of_mem_commSpace_of_fixed ρ hTodd W hy
    (fun x' _ => (mem_cE.mp hycE).1 (ρ x') ⟨x', rfl⟩)

theorem twelveTwo_two_spec {ρ : G →* LGL 2 V} {B A : Subgroup G}
    {Z : Submodule (ZMod 2) V} (h : Setting12One ρ B Z A n m)
    (hmin : ∀ L : Subgroup G, A ≤ L → ¬ L ≤ B → L = ⊤)
    (hZ : Module.finrank (ZMod 2) Z ≤ m) :
    n = m ∧ Module.finrank (ZMod 2) Z = m ∧
      (∀ x ∈ B, Odd (orderOf x) → x ≠ 1 → ∀ z ∈ Z, ρ x z = z → z = 0) ∧
      ∃ (t : G) (T : Subgroup G), t * t = 1 ∧ t ∉ B ∧ T ≤ B ∧ IsCyclic T ∧
        Nat.card T = 2 ^ n - 1 ∧ (∀ x ∈ T, t * x * t = x⁻¹) ∧ RegularOnNonzero ρ T Z ∧
        commSpace (T.map ρ) Z = Z := by
  haveI : Finite G := rankOne_finite h.type
  obtain ⟨S, hSB⟩ := exists_sylow_of_isBorelIn h.borel
  obtain ⟨-, t, -, -, -, -, -, ht2, htS, -, -⟩ := rankOne_exists_cartan h.type S
  have hspec := rankOne_cartan_spec h.type S ht2 htS
  obtain ⟨hTle, -, -, hTcyc, hTcard, hTinv, hTfpf⟩ := hspec
  have hBST : ∀ b ∈ B, ∃ s ∈ (S : Subgroup G), ∃ x ∈ cartan (S : Subgroup G) t, b = s * x :=
    fun b hb => rankOne_borel_eq_mul h.type S ht2 htS (by rw [← hSB]; exact hb)
  have hTB : cartan (S : Subgroup G) t ≤ B := by rw [hSB]; exact hTle
  have htB : t ∉ B := by rw [hSB]; exact htS
  have hmn : m ≤ n := Setting12One.m_le_n h
  have hn1 : 1 < n := lt_of_lt_of_le h.one_lt_m hmn
  have hTodd : Odd (Nat.card (cartan (S : Subgroup G) t)) := by
    rw [hTcard]
    have h2 : 2 ^ n = 2 * 2 ^ (n - 1) := by
      rw [← pow_succ']
      congr 1
      omega
    have hpos : 0 < 2 ^ (n - 1) := pow_pos (by norm_num) _
    exact ⟨2 ^ (n - 1) - 1, by omega⟩
  have hT1 : cartan (S : Subgroup G) t ≠ ⊥ := by
    intro hbot
    have h1 : Nat.card (cartan (S : Subgroup G) t) = 1 := by
      rw [hbot]
      exact Subgroup.card_bot
    rw [hTcard] at h1
    have h4 : 4 ≤ 2 ^ n := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn1
    omega
  have hZinv : ∀ x ∈ cartan (S : Subgroup G) t, ∀ z ∈ Z, ρ x z ∈ Z :=
    fun x hx z hz => (h.stab x).mp (hTB hx) z hz
  obtain ⟨x₀, hx₀T, z₀, hz₀Z, hx₀z₀⟩ :=
    Setting12One.exists_nontrivial_of_cartan h hSB hT1 hTB hBST hTfpf
  have hY0 : commSpace ((cartan (S : Subgroup G) t).map ρ) Z ≠ ⊥ := by
    intro hbot
    rw [commSpace_eq_bot_iff] at hbot
    exact hx₀z₀ (hbot (ρ x₀) (Subgroup.mem_map_of_mem ρ hx₀T) z₀ hz₀Z)
  have hYZ : commSpace ((cartan (S : Subgroup G) t).map ρ) Z ≤ Z := by
    rw [commSpace_le_iff]
    intro k hk u hu
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hk
    exact Z.sub_mem (hZinv x hx u hu) hu
  have hYinv : ∀ x ∈ cartan (S : Subgroup G) t, ∀ y ∈ commSpace
      ((cartan (S : Subgroup G) t).map ρ) Z, ρ x y ∈ commSpace
      ((cartan (S : Subgroup G) t).map ρ) Z := fun x hx y hy =>
    map_mem_commSpace_map ρ hZinv hx hy
  have hfreeY : ∀ x ∈ cartan (S : Subgroup G) t, x ≠ 1 → ∀ y ∈ commSpace
      ((cartan (S : Subgroup G) t).map ρ) Z, ρ x y = y → y = 0 := fun x hx hx1 y hy hfix =>
    eq_zero_of_mem_commSpace_of_inverted h hmin ht2 hTinv hTodd Z hx hx1 hy hfix
  have hcard := card_add_one_le_card_of_free ρ hYinv hY0 hfreeY
  rw [hTcard, card_submodule_eq_two_pow_finrank] at hcard
  have hYdim : n ≤ Module.finrank (ZMod 2) (commSpace ((cartan (S : Subgroup G) t).map ρ) Z) := by
    have hpos : 1 ≤ 2 ^ n := Nat.one_le_two_pow
    have h2 : 2 ^ n ≤ 2 ^ Module.finrank (ZMod 2)
        (commSpace ((cartan (S : Subgroup G) t).map ρ) Z) := by omega
    exact (Nat.pow_le_pow_iff_right (by norm_num)).1 h2
  have hYZdim : Module.finrank (ZMod 2) (commSpace ((cartan (S : Subgroup G) t).map ρ) Z) ≤
      Module.finrank (ZMod 2) Z := Submodule.finrank_mono hYZ
  have hnm : n = m := le_antisymm (hYdim.trans (hYZdim.trans hZ)) hmn
  have hZn : Module.finrank (ZMod 2) Z = m := by omega
  have hYeq : commSpace ((cartan (S : Subgroup G) t).map ρ) Z = Z :=
    Submodule.eq_of_le_of_finrank_eq hYZ (by omega)
  have hZ0 : Z ≠ ⊥ := by
    intro hbot
    apply hY0
    rw [hYeq]
    exact hbot
  have hfreeZ : ∀ x ∈ cartan (S : Subgroup G) t, x ≠ 1 → ∀ z ∈ Z, ρ x z = z → z = 0 := by
    intro x hx hx1 z hz hfix
    refine hfreeY x hx hx1 z ?_ hfix
    rw [hYeq]
    exact hz
  have hcardZ : Nat.card (cartan (S : Subgroup G) t) + 1 = Nat.card Z := by
    rw [hTcard, card_submodule_eq_two_pow_finrank, hZn, ← hnm]
    have hpos : 1 ≤ 2 ^ n := Nat.one_le_two_pow
    omega
  have hreg : RegularOnNonzero ρ (cartan (S : Subgroup G) t) Z :=
    regularOnNonzero_of_card ρ hZinv hZ0 hfreeZ hcardZ
  have hSZ : ∀ s ∈ (S : Subgroup G), ∀ z ∈ Z, ρ s z ∈ Z := fun s hs z hz =>
    (h.stab s).mp (by rw [hSB]; exact Subgroup.le_normalizer hs) z hz
  have hSfix := sylow_trivial_of_regular ρ hTle hSZ hZ0 hreg
  refine ⟨hnm, hZn, ?_, t, cartan (S : Subgroup G) t, ht2, htB, hTB, hTcyc, hTcard, hTinv, hreg,
    hYeq⟩
  intro x hxB hodd hx1 z hz hfix
  exact eq_zero_of_fixed_of_odd_mem_borel ρ hTB (fun b hb z hz => (h.stab b).mp hb z hz) hBST
    hSfix hreg.1 hxB hodd hx1 hz hfix

end TwoD

theorem twelveTwo_two_top {G : Type} [Group G] {V : Type}
    [AddCommGroup V] [Module (ZMod 2) V] [Finite V] (ρ : G →* LGL 2 V) (B : Subgroup G)
    (Z : Submodule (ZMod 2) V) (A : Subgroup G) (n m : ℕ) (hS : Setting12One ρ B Z A n m)
    (hmin : ∀ L : Subgroup G, A ≤ L → ¬ L ≤ B → L = ⊤)
    (hZ : Module.finrank (ZMod 2) Z ≤ m) :
    n = m ∧ Module.finrank (ZMod 2) Z = m ∧
      ∀ x ∈ B, Odd (orderOf x) → x ≠ 1 → ∀ z ∈ Z, ρ x z = z → z = 0 := by
  obtain ⟨h1, h2, h3, -⟩ := twelveTwo_two_spec hS hmin hZ
  exact ⟨h1, h2, h3⟩

end CFSG.LocalAnalysis.WeakClosure81
