module

public import CFSG.LocalAnalysis.StandardType.GGHalfGlue

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.LieType.Universal.SpecialLinear Matrix GGHalf

namespace GGHalfCtx

private theorem zpow_eq_of_dvd_sub {H : Type*} [Group H] {g : H} {m n : ℤ}
    (hg : g ^ (3 : ℕ) = 1) (h : (3 : ℤ) ∣ m - n) : g ^ m = g ^ n := by
  rw [zpow_eq_zpow_emod' (x := g) m hg, zpow_eq_zpow_emod' (x := g) n hg]
  congr 1
  exact Int.ModEq.eq (Int.modEq_of_dvd h).symm

private theorem three_dvd_sq_sub_one_of_not_dvd {j : ℤ} (hj : ¬ (3 : ℤ) ∣ j) :
    (3 : ℤ) ∣ j * j - 1 := by
  refine (ZMod.intCast_zmod_eq_zero_iff_dvd (j * j - 1) 3).mp ?_
  push_cast
  have hsq : ∀ a : ZMod 3, a ≠ 0 → a * a = 1 := by decide
  have hj' : (j : ZMod 3) ≠ 0 :=
    fun h => hj ((ZMod.intCast_zmod_eq_zero_iff_dvd j 3).mp h)
  rw [hsq (j : ZMod 3) hj']
  ring

variable {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G}
  {L D J K : Subgroup G} {m : ℕ} {y : G}
  {φ₁ φ₂ : SpecialLinearGroup (Fin (m + 1 + 1 + 1)) F2 →* G}
  (h : GGHalfCtx p B Bs x L D J m y K φ₁ φ₂)

include h

theorem y_comm_J : ∀ j ∈ J, y * j = j * y := by
  obtain ⟨-, -, hDJ⟩ := h.cfg
  obtain ⟨-, -, -, -, hnbr, -, -⟩ := h.nbr
  obtain ⟨-, hNeighbor⟩ := hnbr
  obtain ⟨hD, -, -⟩ := hNeighbor
  obtain ⟨hPre, -⟩ := hDJ
  obtain ⟨-, -, -, -, -, -, hcent⟩ := hPre
  intro j hj
  have hyD : y ∈ D := by
    rw [hD]
    exact Subgroup.subset_closure (by simp)
  have hycent : y ∈ Subgroup.centralizer (J : Set G) := (le_of_eq hcent) hyD |>.2
  exact (Subgroup.mem_centralizer_iff.mp hycent j hj).symm

theorem w_comm_J : ∀ j ∈ J, wElt φ₂ * j = j * wElt φ₂ := by
  intro j hj
  have hJ : J = (φ₂.comp (slUpper2Hom m)).range := by
    rw [← h.coords.rangeJ, h.coords.agree]
  rw [hJ, MonoidHom.mem_range] at hj
  obtain ⟨s, hs⟩ := hj
  rw [← hs]
  show φ₂ (omegaBlock (m + 1 + 1) ⟨m + 1, by omega⟩) * φ₂ (slUpper2Hom m s) =
    φ₂ (slUpper2Hom m s) * φ₂ (omegaBlock (m + 1 + 1) ⟨m + 1, by omega⟩)
  have hS : slUpper2Hom m s ∈
      slOn (m + 1 + 1 + 1) {i : Fin (m + 1 + 1 + 1) | i.val ≤ m} := by
    rw [← range_slUpper2Hom m]
    exact ⟨s, rfl⟩
  have hk : (⟨m + 1, by omega⟩ : Fin (m + 1 + 1)).castSucc ∉
        {i : Fin (m + 1 + 1 + 1) | i.val ≤ m} ∧
      (⟨m + 1, by omega⟩ : Fin (m + 1 + 1)).succ ∉
        {i : Fin (m + 1 + 1 + 1) | i.val ≤ m} := by
    constructor <;>
      (simp only [Set.mem_setOf_eq, Fin.val_castSucc, Fin.val_succ]; omega)
  have hcomm := commute_omegaBlock_slOn
    (S := {i : Fin (m + 1 + 1 + 1) | i.val ≤ m})
    (k := (⟨m + 1, by omega⟩ : Fin (m + 1 + 1))) hk hS
  simp only [← map_mul]
  exact congrArg φ₂ hcomm

theorem not_dvd_of_y_eq {i j : ℤ} (hy : y = x ^ i * vElt φ₁ ^ j) : ¬ (3 : ℤ) ∣ j := by
  rcases h.basic with ⟨hBscomm, hBs3, hxBs, hyBs, hxne, hyne, hxL, hyK, hxK, hCBL⟩
  intro hj
  have hvBs : vElt φ₁ ∈ Bs := vElt_mem h
  have hv3 : vElt φ₁ ^ (3 : ℕ) = 1 := hBs3 _ hvBs
  have hx3 : x ^ (3 : ℕ) = 1 := hBs3 _ hxBs
  have hvj : vElt φ₁ ^ j = 1 := by
    have := zpow_eq_of_dvd_sub (g := vElt φ₁) hv3 (m := j) (n := 0) (by simpa using hj)
    simpa using this
  have hxy : y = x ^ i := by rw [hy, hvj, mul_one]
  have hycent : y ∈ Subgroup.centralizer (K : Set G) :=
    Subgroup.mem_centralizer_iff.mpr (fun k hk => (hyK k hk).symm)
  have hxord : orderOf x = 3 := by
    haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
    exact orderOf_eq_prime hx3 hxne
  have hyord : orderOf y = 3 := by
    haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
    exact orderOf_eq_prime (hBs3 y hyBs) hyne
  have hmem : y ∈ Subgroup.zpowers x := Subgroup.mem_zpowers_iff.mpr ⟨i, hxy.symm⟩
  have hle : Subgroup.zpowers y ≤ Subgroup.zpowers x := Subgroup.zpowers_le.mpr hmem
  have hcardx : Nat.card (Subgroup.zpowers x) = 3 := by rw [Nat.card_zpowers, hxord]
  have hcardy : Nat.card (Subgroup.zpowers y) = 3 := by rw [Nat.card_zpowers, hyord]
  have heq : Subgroup.zpowers y = Subgroup.zpowers x :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [hcardx, hcardy])
  have hxmem : x ∈ Subgroup.zpowers y := by
    rw [heq]
    exact Subgroup.mem_zpowers_iff.mpr ⟨1, by simp⟩
  have hxcent : x ∈ Subgroup.centralizer (K : Set G) :=
    Subgroup.zpowers_le.mpr hycent hxmem
  exact hxK (fun k hk => (Subgroup.mem_centralizer_iff.mp hxcent k hk).symm)

theorem not_dvd_det {i j a b : ℤ} (hy : y = x ^ i * vElt φ₁ ^ j)
    (hw : wElt φ₂ = x ^ a * vElt φ₁ ^ b) : ¬ (3 : ℤ) ∣ i * b - j * a := by
  rcases h.basic with ⟨hBscomm, hBs3, hxBs, hyBs, hxne, hyne, hxL, hyK, hxK, hCBL⟩
  intro hdiv
  have hj : ¬ (3 : ℤ) ∣ j := not_dvd_of_y_eq h hy
  have hsq : (3 : ℤ) ∣ j * j - 1 := three_dvd_sq_sub_one_of_not_dvd hj
  have h1 : (3 : ℤ) ∣ a - i * (b * j) := by
    obtain ⟨d, hd⟩ := hdiv
    obtain ⟨c, hc⟩ := hsq
    refine ⟨-a * c - d * j, ?_⟩
    have hkey : a - i * (b * j) = -(a * (j * j - 1)) - (i * b - j * a) * j := by ring
    rw [hkey, hc, hd]
    ring
  have h2 : (3 : ℤ) ∣ b - j * (b * j) := by
    obtain ⟨c, hc⟩ := hsq
    refine ⟨-b * c, ?_⟩
    have hkey : b - j * (b * j) = -(b * (j * j - 1)) := by ring
    rw [hkey, hc]
    ring
  have hvBs : vElt φ₁ ∈ Bs := vElt_mem h
  have hx3 : x ^ (3 : ℕ) = 1 := hBs3 _ hxBs
  have hv3 : vElt φ₁ ^ (3 : ℕ) = 1 := hBs3 _ hvBs
  have hxv : Commute x (vElt φ₁) := hBscomm x hxBs (vElt φ₁) hvBs
  have h_expand : y ^ (b * j) = x ^ (i * (b * j)) * vElt φ₁ ^ (j * (b * j)) := by
    rw [hy, (Commute.zpow_zpow hxv i j).mul_zpow (b * j)]
    simp only [← _root_.zpow_mul]
  have hw_eq : wElt φ₂ = y ^ (b * j) := by
    rw [hw, h_expand, zpow_eq_of_dvd_sub hx3 h1, zpow_eq_of_dvd_sub hv3 h2]
  have hw_mem : wElt φ₂ ∈ Subgroup.zpowers y := by
    rw [hw_eq]
    exact Subgroup.zpow_mem_zpowers y (b * j)
  have hycent : y ∈ Subgroup.centralizer (K : Set G) :=
    Subgroup.mem_centralizer_iff.mpr (fun k hk => (hyK k hk).symm)
  have hwcent : wElt φ₂ ∈ Subgroup.centralizer (K : Set G) :=
    Subgroup.zpowers_le.mpr hycent hw_mem
  have hcomm : ∀ t : SpecialLinearGroup (Fin (m + 1 + 1 + 1)) F2,
      φ₂ (omegaBlock (m + 1 + 1) ⟨m + 1, by omega⟩) * φ₂ t =
        φ₂ t * φ₂ (omegaBlock (m + 1 + 1) ⟨m + 1, by omega⟩) := by
    intro t
    have hmemK : φ₂ t ∈ K := by
      rw [← h.coords.range₂]
      exact ⟨t, rfl⟩
    have hthis := Subgroup.mem_centralizer_iff.mp hwcent (φ₂ t) hmemK
    simpa only [wElt] using hthis.symm
  have hone : omegaBlock (m + 1 + 1) ⟨m + 1, by omega⟩ = 1 :=
    eq_one_of_commute_range (s := omegaBlock (m + 1 + 1) ⟨m + 1, by omega⟩)
      h.coords.inj₂ hcomm
  exact omegaBlock_ne_one (m + 1 + 1) ⟨m + 1, by omega⟩ hone

end GGHalfCtx

end CFSG.StandardType

end
