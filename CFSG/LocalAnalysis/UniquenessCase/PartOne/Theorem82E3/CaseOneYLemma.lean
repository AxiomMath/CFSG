module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.CaseOneAbar
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.CaseOneMechanisms
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.CComponents
import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Diag.Fixed

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3

open CFSG.LocalAnalysis.UniquenessCase.UC22 (Data)

variable {G : Type} [Group G] [Finite G] {D : Data G}

namespace Case811Sylow

variable {c : Ctx82E3 D}

theorem exists_mem_centralizer_A_not_mem_L (h : Case811Sylow c) {p : ℕ} (hp : p ∈ D.sig)
    (hpA : ∀ g ∈ D.M ⊓ Subgroup.normalizer (h.A : Set G), IsPGroup p (Subgroup.zpowers g) →
      g ∈ Subgroup.centralizer (h.A : Set G))
    (hL2 : CFSG.Open.pRank p c.L ≤ 2)
    (hnot : ¬ p ∣ Nat.card (Subgroup.centralizer (h.Abar : Set c.Lbar))) :
    ∃ y ∈ D.M ⊓ Subgroup.centralizer (h.A : Set G), orderOf y = p ∧ y ∉ c.L := by
  have hp_prime : p.Prime := (D.sig_prime p hp).1
  have : Fact p.Prime := ⟨hp_prime⟩
  have hp2 : p ≠ 2 := by
    have := c.five_le_of_mem_sigma hp
    omega
  have hdvdM : p ∣ Nat.card (D.M ⊓ Subgroup.centralizer (h.A : Set G) : Subgroup G) := by
    by_contra hC
    have hML := h.pRank_M_le_pRank_L_of_not_dvd hpA hC
    have hM3 := c.pRank_eq_three_of_mem_sigma hp
    omega
  have hCA_dvd : p ∣ Nat.card (c.L ⊓ Subgroup.centralizer (h.A : Set G) : Subgroup G) ↔
      p ∣ Nat.card (Subgroup.centralizer (h.Abar : Set c.Lbar)) := by
    change p ∣ Nat.card (c.L ⊓ Subgroup.centralizer (h.A : Set G) : Subgroup G) ↔
      p ∣ Nat.card (Subgroup.centralizer (((h.A.subgroupOf c.L).map
        (QuotientGroup.mk' (CFSG.Open.pCore 2 ↥c.L))) : Set c.Lbar))
    exact Ctx82E3.dvd_card_centralizer_lbar_iff c (q := 3) (by norm_num) (p := p) hp2
      h.A_le_L h.elemAbelian.isPGroup
  obtain ⟨y₀, hy₀⟩ := exists_prime_orderOf_dvd_card'
    (G := ↥(D.M ⊓ Subgroup.centralizer (h.A : Set G))) p hdvdM
  have hyp : orderOf (y₀ : G) = p := by
    rw [Subgroup.orderOf_coe]
    exact hy₀
  refine ⟨y₀, y₀.2, hyp, fun hyL => hnot (hCA_dvd.mp ?_)⟩
  have hmem : (y₀ : G) ∈ c.L ⊓ Subgroup.centralizer (h.A : Set G) := ⟨hyL, y₀.2.2⟩
  have hz : p ∣ Nat.card (Subgroup.zpowers (y₀ : G)) := by
    rw [Nat.card_zpowers, hyp]
  exact hz.trans (Subgroup.card_dvd_of_le (Subgroup.zpowers_le.mpr hmem))

theorem exists_elemAbelian_sq_le_inf_normalizer (h : Case811Sylow c) {p : ℕ} (hp : p.Prime)
    {y : G} (hyM : y ∈ D.M) (hyA : y ∈ Subgroup.centralizer (h.A : Set G))
    (hyp : orderOf y = p) (hyL : y ∉ c.L) {X : Subgroup G} (hXA : X ≤ h.A)
    (hdvd : p ∣ Nat.card (c.L ⊓ Subgroup.centralizer (X : Set G) : Subgroup G)) :
    ∃ R : Subgroup G, CFSG.Open.IsElemAbelian p R ∧ Nat.card R = p ^ 2 ∧
      R ≤ D.M ⊓ Subgroup.normalizer (X : Set G) := by
  have : Fact p.Prime := ⟨hp⟩
  have hy_pow : y ^ p = 1 := by rw [← hyp]; exact pow_orderOf_eq_one y
  have hy_cent : y ∈ Subgroup.centralizer (X : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    exact Subgroup.mem_centralizer_iff.mp hyA x (hXA hx)
  let Y : Subgroup G := c.L ⊓ Subgroup.centralizer (X : Set G)
  have hyN : y ∈ Subgroup.normalizer (Y : Set G) := by
    have hyNL : y ∈ Subgroup.normalizer (c.L : Set G) := c.le_normalizer_L hyM
    have hyNC : y ∈ Subgroup.normalizer (Subgroup.centralizer (X : Set G) : Set G) :=
      Subgroup.le_normalizer hy_cent
    exact Subgroup.inf_normalizer_le_normalizer_inf ⟨hyNL, hyNC⟩
  obtain ⟨u, huY, huord, huCent⟩ :=
    CFSG.Quasithin.exists_orderOf_eq_of_isPGroup_normalizer
      (P := Subgroup.zpowers y) (H := Y)
      (CFSG.Open.isElemAbelian_zpowers hy_pow).isPGroup
      (Subgroup.zpowers_le.mpr hyN) hdvd
  have huy : u * y = y * u :=
    (Subgroup.mem_centralizer_iff.mp huCent y (Subgroup.mem_zpowers y)).symm
  have huL : u ∈ c.L := huY.1
  have huC : u ∈ Subgroup.centralizer (X : Set G) := huY.2
  have hu_not : u ∉ Subgroup.zpowers y := by
    intro hu
    have hEq : Subgroup.zpowers u = Subgroup.zpowers y := by
      refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hu) ?_
      rw [Nat.card_zpowers, Nat.card_zpowers, huord, hyp]
    have hy_mem : y ∈ Subgroup.zpowers u := by
      rw [hEq]
      exact Subgroup.mem_zpowers y
    exact hyL (Subgroup.zpowers_le.mpr huL hy_mem)
  have hu_pow : u ^ p = 1 := by rw [← huord]; exact pow_orderOf_eq_one u
  let R : Subgroup G := Subgroup.zpowers u ⊔ Subgroup.zpowers y
  have hcomm_uy : ∀ a ∈ Subgroup.zpowers u, ∀ b ∈ Subgroup.zpowers y, a * b = b * a := by
    intro a ha b hb
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
    exact ((show Commute u y from huy).zpow_zpow m n).eq
  have hR_elem : CFSG.Open.IsElemAbelian p R :=
    CFSG.Open.IsElemAbelian.sup_of_commute
      (CFSG.Open.isElemAbelian_zpowers hu_pow)
      (CFSG.Open.isElemAbelian_zpowers hy_pow) hcomm_uy
  have hinf : Subgroup.zpowers u ⊓ Subgroup.zpowers y = ⊥ :=
    CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Diag.zpowers_inf_eq_bot hp hu_pow hu_not
  have hR_card : Nat.card R = p ^ 2 := by
    obtain ⟨hcard, -⟩ :=
      CFSG.GroupTheory.card_sup_mul_card_inf_of_commute
        (Subgroup.zpowers u) (Subgroup.zpowers y) hcomm_uy
    rw [hinf, Nat.card_zpowers, Nat.card_zpowers, huord, hyp] at hcard
    simpa [pow_two] using hcard
  have hRM : R ≤ D.M :=
    sup_le (Subgroup.zpowers_le.mpr (c.hyp81.1 huL)) (Subgroup.zpowers_le.mpr hyM)
  have hRN : R ≤ Subgroup.normalizer (X : Set G) :=
    sup_le ((Subgroup.zpowers_le.mpr huC).trans (Subgroup.centralizer_le_normalizer (X : Set G)))
      ((Subgroup.zpowers_le.mpr hy_cent).trans (Subgroup.centralizer_le_normalizer (X : Set G)))
  exact ⟨R, hR_elem, hR_card, le_inf hRM hRN⟩

end Case811Sylow

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3
