module

public import CFSG.RankThree.GF2n.Stroth80.Sec92SplitU
public import CFSG.RankThree.GF2n.Stroth80.Sec97FivePoint
import CFSG.RankThree.GF2n.Stroth80.HeringSec91CentreX
public import CFSG.RankThree.GF2n.Stroth80.Sec9NComm

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

namespace Split92

theorem mem_centre_of_comm_Wt (h34 : Stroth34Statement) (h311a : Stroth311aStatement)
    (h311bComm : Stroth311bCommStatement) (h311bCard : Stroth311bCardStatement)
    {hc : Ctx M Q Z B} {n : ℕ} {t : G} (hs : Sec9Hyp hc n t) {Z0 : Subgroup G}
    (hZ0 : IsCentrePre Z0 (Rt M (LB M Q B) t) Q) {y : G} (hy : y ∈ LB M Q B)
    (hyW : ∀ w ∈ Wt Q (Vt M (LB M Q B) B Z t), ⁅y, w⁆ ∈ Z) : y ∈ Z0 := by
  classical
  have hs5 := hs.toSec5
  have ht : t ∈ LB M Q B := hs5.mem
  obtain ⟨K, fK, finK, hchar, γ, M₀, h⟩ := stroth_globalModelData hc.hyp
  have hcard := stroth_3_5 h34 hc hs5.width hs5.n_gt hs5.noA2 hs5.gen
  have hZQB : Z ≤ QB B := hc.Z_le_QB.1
  have hZX : Z ≤ Q ⊓ QB B := le_inf hc.Z_le_Q hZQB
  have hVQ : Vt M (LB M Q B) B Z t ≤ Q := hc.Vt_le_Q t
  have hWQ : Wt Q (Vt M (LB M Q B) B Z t) ≤ Q := inf_le_left
  have hVW : Vt M (LB M Q B) B Z t ≤ Wt Q (Vt M (LB M Q B) B Z t) :=
    sec7ctr_Vt_le_Wt h34 hc hs5
  have hZW : Z ≤ Wt Q (Vt M (LB M Q B) B Z t) := sec39_Z_le_Vt.trans hVW
  obtain ⟨U, hU⟩ := hc.exists_submodule_inf_QB hs5.width hcard.2.2.2 h
  set Y : Subgroup G := QB B ⊓ Wt Q (Vt M (LB M Q B) B Z t) with hY
  have hZY : Z ≤ Y := le_inf hZQB hZW
  have hYQ : Y ≤ Q ⊓ QB B := fun x hx => ⟨hWQ hx.2, hx.1⟩
  have hBY : B ≤ Y := fun x hx => ⟨hc.B_le_QB hx, hVW (hc.B_le_Vt ht hx)⟩
  have hYsc : ∀ (c : K) (e : M₀.E), e ∈ M₀.img Y → c • e ∈ M₀.img Y := by
    intro c e he
    obtain ⟨y₀, hy₀, hy₀Q, rfl⟩ := he
    have h1 : c • M₀.π y₀ ∈ U := U.smul_mem c ((hU _).mpr (M₀.pi_mem_img (hYQ hy₀) hy₀Q))
    have h2 : c • M₀.π y₀ ∈ M₀.img (Wt Q (Vt M (LB M Q B) B Z t)) :=
      smul_mem_img_Wt M₀ h.reg hVQ c (M₀.pi_mem_img hy₀.2 hy₀Q)
    obtain ⟨y', hy'Q, hy'⟩ := M₀.π_surj (c • M₀.π y₀)
    rw [← hy'] at h1 h2
    have h1' : y' ∈ Q ⊓ QB B := (M₀.mem_img_iff hZX hy'Q).mp ((hU _).mp h1)
    have h2' : y' ∈ Wt Q (Vt M (LB M Q B) B Z t) := (M₀.mem_img_iff hZW hy'Q).mp h2
    exact ⟨y', ⟨h1'.2, h2'⟩, hy'Q, hy'⟩
  obtain ⟨b, hbY, hb0, hB, hel3, hel4, hcount⟩ := hc.elation_package hs5.width hs5.n_gt
    hs5.noA2 hcard.2.2.1 hcard.2.2.2 h hBY hYQ hYsc
  obtain ⟨T, hT⟩ := hc.exists_centSub (Y : Set G)
  have hcnt := hcount T hT
  have hYcard : Nat.card ↥Y = Nat.card Z ^ n :=
    (sec9_numerics h34 (step91OrderQB_of h34) (step91OrderVQB_of h34) hs).1
  have hKZ : Nat.card K = Nat.card Z := h.card
  have hK2 : 2 ≤ Nat.card K := by
    rw [hKZ]
    have := hc.hyp.q4
    omega
  have hYimg : Nat.card ↥Z * Nat.card (M₀.img Y) = Nat.card Z ^ n := by
    rw [← M₀.card_eq (hYQ.trans inf_le_left) hZY, hYcard]
  have hdim : Module.finrank K (imgSub M₀ Y hYsc) = n - 1 := by
    have h1 : Nat.card (imgSub M₀ Y hYsc) = Nat.card (M₀.img Y) :=
      Nat.card_congr (Equiv.subtypeEquivRight fun e => mem_imgSub)
    have e : Nat.card Z ^ n = Nat.card Z * Nat.card Z ^ (n - 1) := by
      rw [← pow_succ']
      congr 1
      have := hs5.n_gt
      omega
    have h2 : Nat.card Z * Nat.card (M₀.img Y) = Nat.card Z * Nat.card Z ^ (n - 1) := by
      rw [hYimg, e]
    have h3 := Nat.eq_of_mul_eq_mul_left Nat.card_pos h2
    have h4 : Nat.card K ^ Module.finrank K (imgSub M₀ Y hYsc) = Nat.card K ^ (n - 1) := by
      rw [← Module.natCard_eq_pow_finrank (K := K), h1, h3, hKZ]
    exact Nat.pow_right_injective hK2 h4
  rw [hdim, hcard.2.2.1, hKZ] at hcnt
  have hn3 : 3 ≤ n := hs5.n_gt
  have hTcard : Nat.card T = Nat.card Q * Nat.card Z := by
    have hpos : 0 < Nat.card Z ^ (n - 1 - 1) := pow_pos Nat.card_pos _
    refine Nat.eq_of_mul_eq_mul_right hpos ?_
    have e : Nat.card Z ^ (n - 1) = Nat.card Z ^ (n - 1 - 1) * Nat.card Z := by
      rw [← pow_succ]
      congr 1
      omega
    calc Nat.card T * Nat.card Z ^ (n - 1 - 1) = Nat.card Q * Nat.card Z ^ (n - 1) := hcnt.symm
      _ = Nat.card Q * Nat.card Z * Nat.card Z ^ (n - 1 - 1) := by rw [e]; ring
  have hNC : Sec9NCommStatement := sec9NComm_of_311b h34 h311bComm
  obtain ⟨r, hr⟩ := sec9AExists_of h34 h311a hNC G M Q Z B hc n t hs
  have h91b : Stroth91bStatement := stroth91b_of_steps h34 h311a hNC (step91OrderQB_of h34)
    (step91OrderVQB_of h34) (step91Inter_of h34) (step91MixedComm_of h34)
  obtain ⟨hZ0LN, hidx, -⟩ := step95Centre_of h34 h311a h311bComm h311bCard G M Q Z B hc n t hs
    Z0 hZ0
  have hQZ0 : Q ≤ Z0 := hc.Q_le_centre ht hZ0
  have hZ0card : Nat.card Z0 = Nat.card Q * Nat.card Z := by
    have h1 := Subgroup.relIndex_mul_card (H := Q) (K := Z0)
    rw [inf_of_le_left hQZ0, hidx] at h1
    rw [← h1, mul_comm]
  have hZ0T : Z0 ≤ T := by
    intro z hz
    exact (hT z).mpr ⟨(hZ0LN hz).1, fun y' hy' => HS9.comm_Wt_le_Z91 h34 h91b hs hr hZ0 hz y'
      hy'.2⟩
  have heq : Z0 = T := Subgroup.eq_of_le_of_card_ge hZ0T (by rw [hTcard, hZ0card])
  rw [heq]
  exact (hT y).mpr ⟨hy, fun y' hy' => hyW y' hy'.2⟩

theorem centre_conj_mem (hc : Ctx M Q Z B) {t : G} {Z0 : Subgroup G}
    (hZ0 : IsCentrePre Z0 (Rt M (LB M Q B) t) Q) {g z : G} (hg : g ∈ Rt M (LB M Q B) t)
    (hz : z ∈ Z0) : g * z * g⁻¹ ∈ Z0 := by
  have hzR := hZ0.le hz
  refine (hZ0 _).mpr ⟨(Rt M (LB M Q B) t).mul_mem ((Rt M (LB M Q B) t).mul_mem hg hzR)
    ((Rt M (LB M Q B) t).inv_mem hg), fun ρ hρ => ?_⟩
  have e : ⁅g * z * g⁻¹, ρ⁆ = g * ⁅z, g⁻¹ * ρ * g⁆ * g⁻¹ := by
    simp only [commutatorElement_def]; group
  rw [e]
  have h1 := hZ0.comm_mem hz ((Rt M (LB M Q B) t).mul_mem
    ((Rt M (LB M Q B) t).mul_mem ((Rt M (LB M Q B) t).inv_mem hg) hρ) hg)
  exact (Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 (hc.Rt_le_M t hg)) _).mp h1

theorem mem_centre_of_mem_N (h34 : Stroth34Statement) (h311a : Stroth311aStatement)
    (h311bComm : Stroth311bCommStatement) (h311bCard : Stroth311bCardStatement)
    {hc : Ctx M Q Z B} {n : ℕ} {t : G} (hs : Sec9Hyp hc n t) {r : G} (hr : Sec7A hc t r)
    {Z0 : Subgroup G} (hZ0 : IsCentrePre Z0 (Rt M (LB M Q B) t) Q)
    (hdec : ∀ m ∈ hc.CN t, (∀ w ∈ Wt Q (Vt M (LB M Q B) B Z t), ⁅m, w⁆ ∈ Z) →
      ∃ a ∈ LB M Q B ⊓ hc.CN t, (∀ w ∈ Wt Q (Vt M (LB M Q B) B Z t), ⁅a, w⁆ ∈ Z) ∧
        ∃ b ∈ LB M Q (conjSubgroup r B) ⊓ hc.CN t,
          (∀ w ∈ Wt Q (Vt M (LB M Q B) B Z t), ⁅b, w⁆ ∈ Z) ∧ m = a * b)
    {m : G} (hm : m ∈ hc.CN t) (hmW : ∀ w ∈ Wt Q (Vt M (LB M Q B) B Z t), ⁅m, w⁆ ∈ Z) :
    m ∈ Z0 := by
  have ht : t ∈ LB M Q B := hs.toSec5.mem
  have hrR : r ∈ Rt M (LB M Q B) t := hr.mem
  have hrM : r ∈ M := hc.Rt_le_M t hrR
  obtain ⟨a, ha, haW, b, hb, hbW, rfl⟩ := hdec m hm hmW
  have haZ := mem_centre_of_comm_Wt h34 h311a h311bComm h311bCard hs hZ0 ha.1 haW
  have hb' : r⁻¹ * b * r ∈ LB M Q B := by
    have h1 : b ∈ conjSubgroup r (LB M Q B) := hc.LB_conj hrM ▸ hb.1
    exact mem_conjSubgroup.mp h1
  have hbW' : ∀ w ∈ Wt Q (Vt M (LB M Q B) B Z t), ⁅r⁻¹ * b * r, w⁆ ∈ Z := by
    intro w hw
    have hw' : r * w * r⁻¹ ∈ Wt Q (Vt M (LB M Q B) B Z t) := sec9_conj_mem_Wt hc ht hrR hw
    have e : ⁅r⁻¹ * b * r, w⁆ = r⁻¹ * ⁅b, r * w * r⁻¹⁆ * r⁻¹⁻¹ := by
      simp only [commutatorElement_def]; group
    rw [e]
    exact (Subgroup.mem_normalizer_iff.mp (hc.hyp.Z_normal.2 (M.inv_mem hrM)) _).mp (hbW _ hw')
  have hbZ' := mem_centre_of_comm_Wt h34 h311a h311bComm h311bCard hs hZ0 hb' hbW'
  have hbZ : b ∈ Z0 := by
    have := centre_conj_mem hc hZ0 hrR hbZ'
    rwa [show r * (r⁻¹ * b * r) * r⁻¹ = b by group] at this
  exact Z0.mul_mem haZ hbZ

theorem exists_centralizing (h34 : Stroth34Statement) (h311a : Stroth311aStatement)
    (h311bComm : Stroth311bCommStatement) (h311bCard : Stroth311bCardStatement)
    {hc : Ctx M Q Z B} {n : ℕ} {t : G} (hs : Sec9Hyp hc n t) {x : G} (hxL : x ∈ LB M Q B)
    (hxN : x ∉ hc.CN t)
    (hxW : ∀ w ∈ Wt Q (Vt M (LB M Q B) B Z t), ⁅x, w⁆ ∈ Vt M (LB M Q B) B Z t)
    (hlt : Sec9R0 hc t x < Rt M (LB M Q B) t) :
    ∃ g₀ ∈ Rt M (LB M Q B) t, g₀ ∉ Sec9R0 hc t x ∧ ∀ a ∈ Sec9R0 hc t x, ⁅g₀, a⁆ ∈ Q := by
  classical
  have hs5 := hs.toSec5
  have ht : t ∈ LB M Q B := hs5.mem
  have hNC : Sec9NCommStatement := sec9NComm_of_311b h34 h311bComm
  obtain ⟨r, hr⟩ := sec9AExists_of h34 h311a hNC G M Q Z B hc n t hs
  obtain ⟨Z0, hZ0⟩ := hc.exists_centre ht
  obtain ⟨K, fK, finK, hch, hK, ψ, hψs, hψk, hψR₀⟩ := factor hc hs hxL hxN hlt
  obtain ⟨halpha, hdec⟩ := sec92_alpha h34 h311a h311bComm hs hr hxL hxN hxW hK ψ hψs hψk hψR₀
  have hRM : Rt M (LB M Q B) t ≤ M := hc.Rt_le_M t
  have hQR : Q ≤ Rt M (LB M Q B) t := hc.Q_le_Rt ht
  have hNR : hc.CN t ≤ Rt M (LB M Q B) t := sec9_CN_le_Rt hc t
  have hxR : x ∈ Rt M (LB M Q B) t := le_Rt (M := M) (LB M Q B) ht hxL
  have hmemN : ∀ m : ↥(Rt M (LB M Q B) t), ψ m = 1 ↔ (m : G) ∈ hc.CN t := fun m => by
    rw [← MonoidHom.mem_ker, hψk, Subgroup.mem_subgroupOf]
  have hNp : IsPGroup 2 ↥(hc.CN t) := Ctx.isPGroup_CN_of_311 h34 hc hs5
    (h311a G M Q Z B hc n hs5.width hs5.n_gt hs5.noA2 hs5.gen t ht hs5.notQ
      (sec9_Rt_ne_LB h34 hs))
  have h3 : 3 ∣ Nat.card ↥(StatedSL 2 K) := by
    rw [StatedAPI.card_statedSL_two]
    obtain ⟨jj, -, hZ2, -⟩ := hc.hyp.cp
    rw [hK, hZ2, ← pow_mul, pow_mul']
    have h1 : 4 - 1 ∣ 4 ^ jj - 1 ^ jj := Nat.sub_dvd_pow_sub_pow 4 1 jj
    rw [one_pow] at h1
    have h2 : (2 ^ 2) ^ jj = 4 ^ jj := by norm_num
    rw [h2]
    exact Dvd.dvd.mul_left h1 _
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨s₀, hs₀⟩ := exists_prime_orderOf_dvd_card' 3 h3
  obtain ⟨g₁, hg₁⟩ := hψs (1, s₀)
  obtain ⟨a₁, ha₁⟩ := exists_odd_pow g₁
  set h := g₁ ^ (2 ^ a₁) with hhdef
  have hψh : ψ h = (1, s₀ ^ (2 ^ a₁)) := by rw [hhdef, map_pow, hg₁]; simp
  have hs₀ne : s₀ ^ (2 ^ a₁) ≠ 1 := by
    intro h1
    have := orderOf_dvd_of_pow_eq_one h1
    rw [hs₀] at this
    have h2 : (3 : ℕ) ∣ 2 := (Nat.prime_three.dvd_of_dvd_pow this)
    omega
  have hhR₀ : (h : G) ∉ Sec9R0 hc t x := by
    rw [hψR₀, hψh]
    exact hs₀ne
  haveI hQn : (Q.subgroupOf (Rt M (LB M Q B) t)).Normal := ⟨fun a ha g => by
    rw [Subgroup.mem_subgroupOf] at ha ⊢
    exact (Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 (hRM g.2)) a).mp ha⟩
  let π : ↥(Rt M (LB M Q B) t) →* ↥(Rt M (LB M Q B) t) ⧸ Q.subgroupOf (Rt M (LB M Q B) t) :=
    QuotientGroup.mk' _
  have hπone : ∀ a : ↥(Rt M (LB M Q B) t), π a = 1 ↔ (a : G) ∈ Q := fun a => by
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
  have hodd : Odd (orderOf (π h)) := Odd.of_dvd_nat ha₁ (orderOf_map_dvd π h)
  have h2el : ∀ k : ↥(Rt M (LB M Q B) t), (k : G) ∈ hc.CN t → ∃ m : ℕ, π k ^ (2 ^ m) = 1 := by
    intro k hk
    obtain ⟨m, hm⟩ := hNp ⟨k, hk⟩
    refine ⟨m, ?_⟩
    rw [← map_pow, hπone]
    have := congrArg Subtype.val hm
    simp only [Subgroup.coe_pow, Subgroup.coe_one] at this
    rw [Subgroup.coe_pow, this]
    exact Q.one_mem
  have hcentral : ∀ z k : ↥(Rt M (LB M Q B) t), (z : G) ∈ Z0 → π k * π z * (π k)⁻¹ = π z := by
    intro z k hz
    have h1 : ((⁅z, k⁆ : ↥(Rt M (LB M Q B) t)) : G) ∈ Q := by
      simpa [commutatorElement_def] using hZ0.comm_mem hz k.2
    have h2 := (hπone _).mpr h1
    rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm] at h2
    rw [← h2]
    group
  have hN : ∀ m : ↥(Rt M (LB M Q B) t), (m : G) ∈ hc.CN t → π h * π m * (π h)⁻¹ = π m := by
    intro m hm
    set k : ↥(Rt M (LB M Q B) t) := h * m * h⁻¹ * m⁻¹ with hk
    have hkN : (k : G) ∈ hc.CN t := by
      have h1 : ψ k = 1 := by
        rw [hk, map_mul, map_mul, map_mul, map_inv, map_inv, (hmemN m).mpr hm]
        group
      exact (hmemN k).mp h1
    have hkW : ∀ w ∈ Wt Q (Vt M (LB M Q B) B Z t), ⁅(k : G), w⁆ ∈ Z := by
      intro w hw
      have := halpha h (by rw [hψh]) m hm w hw
      simpa [hk] using this
    have hkZ0 := mem_centre_of_mem_N h34 h311a h311bComm h311bCard hs hr hZ0 hdec hkN hkW
    obtain ⟨e, he⟩ := h2el k hkN
    have hconj : π h * π m * (π h)⁻¹ = π k * π m := by
      rw [hk]; simp only [map_mul, map_inv]; group
    have hk1 := eq_one_of_conj_eq_mul hodd hconj (hcentral k h hkZ0) he
    rw [hconj, hk1, one_mul]
  refine ⟨h, h.2, hhR₀, fun a ha => ?_⟩
  set aR : ↥(Rt M (LB M Q B) t) := ⟨a, Sec9R0_le_Rt hc hxR ha⟩ with haR
  set k : ↥(Rt M (LB M Q B) t) := h * aR * h⁻¹ * aR⁻¹ with hk
  have hkN : (k : G) ∈ hc.CN t := by
    have h1 : ψ k = 1 := by
      have ha2 : (ψ aR).2 = 1 := (hψR₀ aR).mp ha
      rw [hk, map_mul, map_mul, map_mul, map_inv, map_inv, hψh]
      refine Prod.ext ?_ ?_
      · simp
      · simp [ha2]
    exact (hmemN k).mp h1
  obtain ⟨e, he⟩ := h2el k hkN
  have hconj : π h * π aR * (π h)⁻¹ = π k * π aR := by
    rw [hk]; simp only [map_mul, map_inv]; group
  have hk1 := eq_one_of_conj_eq_mul hodd hconj (hN k hkN) he
  have h1 : ((⁅h, aR⁆ : ↥(Rt M (LB M Q B) t)) : G) ∈ Q := by
    rw [← hπone, map_commutatorElement, commutatorElement_def, show π h * π aR * (π h)⁻¹ * (π aR)⁻¹
      = π k by rw [hk]; simp only [map_mul, map_inv], hk1]
  simpa [commutatorElement_def, haR] using h1

end Split92

theorem sec9CentreMpr_of (h34 : Stroth34Statement) (h311a : Stroth311aStatement)
    (h311bComm : Stroth311bCommStatement) (h311bCard : Stroth311bCardStatement) :
    Sec9CentreMprStatement := by
  intro G _ _ M Q Z B hc n t hs Z0 hZ0 x hx hxW
  exact Split92.mem_centre_of_comm_Wt h34 h311a h311bComm h311bCard hs hZ0 hx hxW

theorem step92Split_of (h34 : Stroth34Statement) (h311a : Stroth311aStatement)
    (h311bComm : Stroth311bCommStatement) (h311bCard : Stroth311bCardStatement) :
    Step92SplitStatement := by
  intro G _ _ M Q Z B hc n t hs V W hV hW x hxL hxN hxW hlt _
  subst hV hW
  obtain ⟨g₀, hg₀R, hg₀, hg₀c⟩ :=
    Split92.exists_centralizing h34 h311a h311bComm h311bCard hs hxL hxN hxW hlt
  exact Split92.split_of_elem h34 h311a hs hxL hxN hlt hg₀R hg₀ hg₀c

end CFSG.RankThree.GF2n.Stroth80
