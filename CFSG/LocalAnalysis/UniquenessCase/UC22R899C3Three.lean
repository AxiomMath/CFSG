module

public import CFSG.LocalAnalysis.UniquenessCase.UC22P2213e
import CFSG.LocalAnalysis.UniquenessCase.UC22R899C3Lift
import CFSG.LocalAnalysis.UniquenessCase.UC22R899C3W
import CFSG.LocalAnalysis.UniquenessCase.UC22S21r899Sp
import CFSG.LocalAnalysis.UniquenessCase.UC22S21r899Stab
import CFSG.LocalAnalysis.UniquenessCase.UC22R8100BBar
import CFSG.LocalAnalysis.UniquenessCase.UC22InE229Diag2
import CFSG.LocalAnalysis.UniquenessCase.UC22P2214c
import CFSG.LocalAnalysis.UniquenessCase.UC22P22a
import CFSG.LocalAnalysis.UniquenessCase.UC22P22l
import CFSG.LocalAnalysis.UniquenessCase.UC22P22rj
import CFSG.LocalAnalysis.UniquenessCase.UC22P22ry

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7 (Conclusion76)

variable {G : Type} [Group G] [Finite G]

theorem uc22r899c3_exists_lift_of_third {M K₁ K₂ K₃ : Subgroup G} (h₁ : K₁ ∈ calC M)
    (h₂ : K₂ ∈ calC M) (h₃ : K₃ ∈ calC M) (h13 : K₁ ≠ K₃) (h23 : K₂ ≠ K₃)
    (hZ : center (Bar2 K₃) = ⊥) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {b c : G} (hb : b ∈ K₃)
    (hbo : orderOf b = p) (hcM : c ∈ M) (hco : orderOf c = p)
    (hc₁ : ∀ k ∈ K₁, c * k * c⁻¹ * k⁻¹ ∈ pCoreOf 2 M)
    (hc₂ : ∀ k ∈ K₂, c * k * c⁻¹ * k⁻¹ ∈ pCoreOf 2 M)
    (hc₃ : ∀ k ∈ K₃, c * k * c⁻¹ * k⁻¹ ∈ pCoreOf 2 M) {a₁ a₂ : G} (ha₁ : a₁ ∈ K₁)
    (ha₂ : a₂ ∈ K₂) :
    ∃ A : Subgroup G, A ≤ M ∧ IsElemAbelian p A ∧ Nat.card A = p ^ 2 ∧
      ∀ e ∈ zpowers a₁ ⊔ zpowers a₂, ∀ a ∈ A, e * a * e⁻¹ * a⁻¹ ∈ pCoreOf 2 M := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hKM : ∀ {K : Subgroup G}, K ∈ calC M → K ≤ M := fun hK => uc22p22a_le_of_isSubnormal hK.1
  have hord : ∀ x : ↥M, orderOf (x : G) = p → orderOf (uc22p21cPi M x) = p := by
    intro x hx
    rw [Subgroup.orderOf_coe] at hx
    have hxp : x ^ p = 1 := by rw [← hx]; exact pow_orderOf_eq_one x
    refine orderOf_eq_prime (by rw [← map_pow, hxp, map_one]) fun h1 => ?_
    have h2 := uc22r8100b_eq_one_of_mem_pCore ((QuotientGroup.eq_one_iff _).1 h1)
      (hp.odd_of_ne_two hp2) hxp
    rw [h2, orderOf_one] at hx
    exact hp.one_lt.ne hx
  have hcomm : ∀ {K : Subgroup G}, (∀ k ∈ K, c * k * c⁻¹ * k⁻¹ ∈ pCoreOf 2 M) →
      ∀ y ∈ barImage M K, y * uc22p21cPi M ⟨c, hcM⟩ = uc22p21cPi M ⟨c, hcM⟩ * y := by
    intro K hc y hy
    obtain ⟨m, hm, rfl⟩ := uc22p21c_mem_barImage.1 hy
    have h1 : uc22p21cPi M (⟨c, hcM⟩ * m * ⟨c, hcM⟩⁻¹ * m⁻¹) = 1 :=
      (QuotientGroup.eq_one_iff _).2
        ((CFSG.mem_openPCoreOf_iff (⟨c, hcM⟩ * m * ⟨c, hcM⟩⁻¹ * m⁻¹ : ↥M)).1 (hc m hm))
    rw [map_mul, map_mul, map_mul, map_inv, map_inv] at h1
    exact (mul_inv_eq_iff_eq_mul.1 (mul_inv_eq_one.1 h1)).symm
  set x := uc22p21cPi M ⟨c, hcM⟩ with hx
  set y := uc22p21cPi M ⟨b, hKM h₃ hb⟩ with hy
  have hyK : y ∈ barImage M K₃ := uc22p21c_mem_barImage.2 ⟨_, hb, rfl⟩
  have hxo : orderOf x = p := hord _ hco
  have hyo : orderOf y = p := hord _ hbo
  have hyx : y ∉ zpowers x := by
    intro hyx
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hyx
    have hyc : ∀ z ∈ barImage M K₃, z * y = y * z := fun z hz => by
      rw [← hk]
      exact Commute.zpow_right (hcomm hc₃ z hz) k
    obtain ⟨e, -⟩ := uc22p22l_barImage_equiv h₃
    have hcen : e.symm ⟨y, hyK⟩ ∈ center (Bar2 K₃) := by
      rw [Subgroup.mem_center_iff]
      intro z
      apply e.injective
      rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
      exact Subtype.ext (hyc _ (e z).2)
    rw [hZ, Subgroup.mem_bot] at hcen
    have hy1 : y = 1 := by
      have h := congrArg (fun z => ((e z : ↥(barImage M K₃)) : Bar2 M)) hcen
      simpa using h
    rw [hy1, orderOf_one] at hyo
    exact hp.one_lt.ne hyo
  obtain ⟨hDel', hDc⟩ :=
    CFSG.ComponentClassification.UnbalancedGS.RankOneCenter.pair_isElementaryAbelian_card hxo hyo
      (hcomm hc₃ y hyK).symm hyx
  have hDel := (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian p _).1 hDel'
  have hcen : ∀ {K : Subgroup G} (hK : K ∈ calC M), K ≠ K₃ →
      (∀ k ∈ K, c * k * c⁻¹ * k⁻¹ ∈ pCoreOf 2 M) → ∀ {a : G} (ha : a ∈ K),
      ∀ d ∈ zpowers x ⊔ zpowers y,
        d * uc22p21cPi M ⟨a, hKM hK ha⟩ = uc22p21cPi M ⟨a, hKM hK ha⟩ * d := by
    intro K hK hne hc a ha d hd
    have haK : uc22p21cPi M ⟨a, hKM hK ha⟩ ∈ barImage M K :=
      uc22p21c_mem_barImage.2 ⟨_, ha, rfl⟩
    have hle : zpowers x ⊔ zpowers y ≤ centralizer {uc22p21cPi M ⟨a, hKM hK ha⟩} := by
      refine sup_le (zpowers_le.2 ?_) (zpowers_le.2 ?_)
      · refine Subgroup.mem_centralizer_iff.2 fun z hz => ?_
        rw [Set.mem_singleton_iff.1 hz]
        exact hcomm hc _ haK
      · refine Subgroup.mem_centralizer_iff.2 fun z hz => ?_
        rw [Set.mem_singleton_iff.1 hz]
        exact uc22p22l_barImage_commute hK h₃ hne _ haK _ hyK
    exact (Subgroup.mem_centralizer_iff.1 (hle hd) _ (Set.mem_singleton _)).symm
  exact uc22r899c3_exists_lift hp hp2 hDel hDc (hKM h₁ ha₁) (hKM h₂ ha₂) fun d hd =>
    ⟨hcen h₁ h13 hc₁ ha₁ d hd, hcen h₂ h23 hc₂ ha₂ d hd⟩

theorem uc22r899c3_exists_comm_of_not_dvd {M K₁ K₂ A₀ : Subgroup G} (h₁ : K₁ ∈ calC M)
    (h₂ : K₂ ∈ calC M) {n p : ℕ} (hL₁ : IsL2 (Bar2 K₁) n) (hL₂ : IsL2 (Bar2 K₂) n)
    (hp : p.Prime) (hp2 : p ≠ 2) (hpn : ¬ p ∣ n) (hA₀M : A₀ ≤ M) (hA₀ : IsElemAbelian p A₀)
    (hA₀c : Nat.card A₀ = p ^ 4) (hA₀N₁ : A₀ ≤ normalizer (K₁ : Set G))
    (hA₀N₂ : A₀ ≤ normalizer (K₂ : Set G)) :
    ∃ A : Subgroup G, A ≤ M ∧ IsElemAbelian p A ∧ Nat.card A = p ^ 2 ∧
      ∀ e ∈ K₁ ⊔ K₂, ∀ a ∈ A, e * a * e⁻¹ * a⁻¹ ∈ pCoreOf 2 M := by
  obtain ⟨B₁, hB₁, hB₁c, hB₁card⟩ := uc22p2213e_exists_centralizesBar hL₁ hp hp2 hpn hA₀ hA₀N₁
  obtain ⟨B₂, hB₂, hB₂c, hB₂card⟩ := uc22p2213e_exists_centralizesBar hL₂ hp hp2 hpn
    (hA₀.mono hB₁) (hB₁.trans hA₀N₂)
  have hB₂p : p ^ 2 ≤ Nat.card B₂ := by
    rw [hA₀c] at hB₁card
    have h4 : p ^ 2 * p ^ 2 ≤ p ^ 2 * Nat.card B₂ :=
      calc p ^ 2 * p ^ 2 = p ^ 4 := by ring
        _ ≤ p * Nat.card B₁ := hB₁card
        _ ≤ p * (p * Nat.card B₂) := Nat.mul_le_mul_left _ hB₂card
        _ = p ^ 2 * Nat.card B₂ := by ring
    exact Nat.le_of_mul_le_mul_left h4 (pow_pos hp.pos 2)
  obtain ⟨A, hAB, hAel, hAc⟩ := UC6S846.exists_card_p_sq hp (hA₀.mono (hB₂.trans hB₁)) hB₂p
  exact ⟨A, hAB.trans (hB₂.trans (hB₁.trans hA₀M)), hAel, hAc, fun e he a ha =>
    uc22p2213e_comm_mem_pCoreOf h₁ h₂ (hB₁c a (hB₂ (hAB ha))) (hB₂c a (hAB ha)) he⟩

theorem uc22r899c3_sp_of_moves {D : Data G}
    (hSg : UC6S846.SigmaStd D) (h614 : UC6.R6_14 D)
    (h76 : ∀ p ∈ D.sig, IsStronglyPEmbedded p D.M → Conclusion76 D.M p) {L : Subgroup G}
    (hL : L ∈ calC D.M) (hc3 : (conjSetOf D.M L).ncard = 3) {n : ℕ} (hL2 : IsL2 (Bar2 L) n)
    {s r : ℕ} (hs : Odd s) (hsn : s ∣ n) (hr : r.Prime) (hrs : r ∣ 2 ^ s - 1)
    (h3 : 3 ∈ D.sig) {A₀ : Subgroup G} (hA₀M : A₀ ≤ D.M) (hA₀ : IsElemAbelian 3 A₀)
    (hA₀c : Nat.card A₀ = 3 ^ 4) {w : G} (hw : w ∈ A₀) (hwL : w ∉ normalizer (L : Set G)) :
    IsStronglyPEmbedded r D.M := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hLm : L ∈ conjSetOf D.M L := ⟨1, D.M.one_mem, by ext x; simp⟩
  obtain ⟨A₁, hA₁, hA₁el, hA₁c, hA₁N⟩ :=
    uc22r899_exists_elemAbelian_stab Nat.prime_three (by norm_num) hc3 hA₀M hA₀ hA₀c
  obtain ⟨C, hCA₁, hCc, hCcard⟩ := uc22r899c3_exists_centralizesBar_sq hL2 Nat.prime_three
    (by norm_num) hA₁el (fun a ha => hA₁N a ha L hLm)
  have hC1 : 1 < Nat.card C := by
    rw [hA₁c] at hCcard
    norm_num at hCcard
    omega
  obtain ⟨⟨c, hcC⟩, hc1⟩ :=
    Subgroup.ne_bot_iff_exists_ne_one.1 ((Subgroup.one_lt_card_iff_ne_bot C).1 hC1)
  have hcA₀ : c ∈ A₀ := hA₁ (hCA₁ hcC)
  have hco : orderOf c = 3 :=
    orderOf_eq_prime (hA₀.2 c hcA₀) fun h => hc1 (Subtype.ext h)
  have hcL : ∀ l ∈ L, c * l * c⁻¹ * l⁻¹ ∈ pCoreOf 2 D.M := fun l hl =>
    uc22p22r_pCoreOf_le_of_isSubnormal hL.1 ((hCc c hcC).2 l hl)
  have hwc : w * c = c * w := by
    haveI := hA₀.1
    exact congrArg Subtype.val (mul_comm' (⟨w, hw⟩ : ↥A₀) ⟨c, hcA₀⟩)
  have hcK : ∀ K ∈ conjSetOf D.M L, ∀ k ∈ K, c * k * c⁻¹ * k⁻¹ ∈ pCoreOf 2 D.M := by
    intro K hK
    obtain ⟨j, rfl⟩ := uc22r899c3_exists_eq_map_conj hc3 (hA₀M hw) (hA₀.2 w hw) hwL hK
    exact uc22r899c3_comm_mem_pCoreOf_map_conj (D.M.pow_mem (hA₀M hw) j)
      (Commute.pow_left hwc j) hcL
  refine uc22r899c3_sp_of_lift hSg h614 h76 hL hc3 (Or.inl hL2) hs hsn hr hrs h3 ?_
  rintro K₁ h1S K₂ h2S - a₁ a₂ ha₁ ha₂ - -
  obtain ⟨K₃, h3S, h31, h32⟩ := uc22r899c3_exists_third (K₁ := K₁) (K₂ := K₂) hc3
  have h3K : 3 ∣ Nat.card K₃ := by
    have h4 : (2 ^ n) ^ 2 = 4 ^ n := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
    have h1 : 3 ∣ Nat.card (Bar2 K₃) := by
      rw [uc22p22r_L2_card (uc22s21r899_isL2_of_mem h3S hL2), h4]
      exact Dvd.dvd.mul_left (by simpa using Nat.sub_dvd_pow_sub_pow (x := 4) (y := 1) (n := n)) _
    exact h1.trans (Subgroup.card_quotient_dvd_card (CFSG.pCore 2 ↥K₃))
  obtain ⟨⟨b, hb⟩, hbo⟩ := exists_prime_orderOf_dvd_card' 3 h3K
  have hC := fun {K : Subgroup G} (hK : K ∈ conjSetOf D.M L) =>
    uc22p2214_calC_of_mem_conjSetOf hL hK
  exact uc22r899c3_exists_lift_of_third (hC h1S) (hC h2S) (hC h3S) h31.symm h32.symm
    (uc22s21r899_center_bot hL h3S (Or.inl hL2)) Nat.prime_three (by norm_num) hb
    ((Subgroup.orderOf_coe (⟨b, hb⟩ : ↥K₃)).trans hbo) (hA₀M hcA₀) hco (hcK K₁ h1S)
    (hcK K₂ h2S) (hcK K₃ h3S) ha₁ ha₂

private theorem uc22r899c3_moves_or_fixes {M L A₀ : Subgroup G}
    (hc3 : (conjSetOf M L).ncard = 3) (hA₀M : A₀ ≤ M) (hA₀ : IsElemAbelian 3 A₀) :
    (∃ w ∈ A₀, w ∉ normalizer (L : Set G)) ∨
      ∀ K ∈ conjSetOf M L, A₀ ≤ normalizer (K : Set G) := by
  by_cases hfix : A₀ ≤ normalizer (L : Set G)
  · refine Or.inr fun K hK a ha => uc22r899_mem_normalizer_of_fix hc3 (hA₀M ha) Nat.prime_three
      (by norm_num) (k := 1) (by rw [pow_one]; exact hA₀.2 a ha)
      (fun _ => ⟨L, ⟨1, M.one_mem, by ext x; simp⟩, hfix ha⟩) K hK
  · exact Or.inl (SetLike.not_le_iff_exists.1 hfix)

theorem uc22r899c3_sp_three_of_not_dvd {D : Data G}
    (hSg : UC6S846.SigmaStd D) (hfour : ∀ p ∈ D.sig, 4 ≤ CFSG.Open.pRank p D.M)
    (h614 : UC6.R6_14 D) (h76 : ∀ p ∈ D.sig, IsStronglyPEmbedded p D.M → Conclusion76 D.M p)
    {L : Subgroup G} (hL : L ∈ calC D.M) (hc3 : (conjSetOf D.M L).ncard = 3) {n : ℕ}
    (hL2 : IsL2 (Bar2 L) n) {s r : ℕ} (hs : Odd s) (hsn : s ∣ n) (hr : r.Prime)
    (hrs : r ∣ 2 ^ s - 1) (h3 : 3 ∈ D.sig) (h3n : ¬ 3 ∣ n) : IsStronglyPEmbedded r D.M := by
  obtain ⟨A₀, hA₀M, hA₀, hA₀c⟩ :=
    UC6S846.exists_elemAbelian_card_of_le_pRank Nat.prime_three (hfour 3 h3)
  rcases uc22r899c3_moves_or_fixes hc3 hA₀M hA₀ with ⟨w, hw, hwL⟩ | hA₀N
  · exact uc22r899c3_sp_of_moves hSg h614 h76 hL hc3 hL2 hs hsn hr hrs h3 hA₀M hA₀ hA₀c hw hwL
  refine uc22r899c3_sp_of_lift hSg h614 h76 hL hc3 (Or.inl hL2) hs hsn hr hrs h3 ?_
  rintro K₁ h1S K₂ h2S - a₁ a₂ ha₁ ha₂ - -
  obtain ⟨A, hAM, hAel, hAc, hA⟩ := uc22r899c3_exists_comm_of_not_dvd
    (uc22p2214_calC_of_mem_conjSetOf hL h1S) (uc22p2214_calC_of_mem_conjSetOf hL h2S)
    (uc22s21r899_isL2_of_mem h1S hL2) (uc22s21r899_isL2_of_mem h2S hL2) Nat.prime_three
    (by norm_num) h3n hA₀M hA₀ hA₀c (hA₀N K₁ h1S) (hA₀N K₂ h2S)
  exact ⟨A, hAM, hAel, hAc, fun e he =>
    hA e (sup_le_sup (zpowers_le.2 ha₁) (zpowers_le.2 ha₂) he)⟩

theorem uc22r899c3_sp_three_of_odd_factor {D : Data G}
    (hSg : UC6S846.SigmaStd D) (hfour : ∀ p ∈ D.sig, 4 ≤ CFSG.Open.pRank p D.M)
    (h614 : UC6.R6_14 D) (h76 : ∀ p ∈ D.sig, IsStronglyPEmbedded p D.M → Conclusion76 D.M p)
    {L : Subgroup G} (hL : L ∈ calC D.M) (hc3 : (conjSetOf D.M L).ncard = 3) {n m : ℕ}
    (hL2 : IsL2 (Bar2 L) n) {s r : ℕ} (hs : Odd s) (hsn : s ∣ n) (hr : r.Prime)
    (hrs : r ∣ 2 ^ s - 1) (h3 : 3 ∈ D.sig) (hn : n = 3 * m) (h3d : 3 ∣ 2 ^ n + 1)
    (hrm : r ∣ 2 ^ m - 1) : IsStronglyPEmbedded r D.M := by
  obtain ⟨A₀, hA₀M, hA₀, hA₀c⟩ :=
    UC6S846.exists_elemAbelian_card_of_le_pRank Nat.prime_three (hfour 3 h3)
  rcases uc22r899c3_moves_or_fixes hc3 hA₀M hA₀ with ⟨w, hw, hwL⟩ | hA₀N
  · exact uc22r899c3_sp_of_moves hSg h614 h76 hL hc3 hL2 hs hsn hr hrs h3 hA₀M hA₀ hA₀c hw hwL
  refine uc22r899c3_sp_of_lift hSg h614 h76 hL hc3 (Or.inl hL2) hs hsn hr hrs h3 ?_
  rintro K₁ h1S K₂ h2S hne a₁ a₂ ha₁ ha₂ ha₁o ha₂o
  exact uc22r8100b_exists_comm_lift (uc22p2214_calC_of_mem_conjSetOf hL h1S)
    (uc22p2214_calC_of_mem_conjSetOf hL h2S) hne (uc22s21r899_isL2_of_mem h1S hL2)
    (uc22s21r899_isL2_of_mem h2S hL2) hn Nat.prime_three (by norm_num) h3d hr
    (uc22ine229_ne_two hs hrs) hrm hA₀M hA₀ hA₀c (hA₀N K₁ h1S) (hA₀N K₂ h2S) ha₁ ha₂ ha₁o ha₂o

end CFSG.LocalAnalysis.UniquenessCase.UC22
