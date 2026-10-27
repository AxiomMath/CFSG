module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenTwentyOneM22
public import CFSG.Quasithin.H13.U3S1348J
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.M22CoverPoints
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenFortyOneProof

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

open Subgroup CFSG.Open CFSG.Quasithin CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]
variable {D : Data G} {V₀ V L : Subgroup G}

theorem exists_order_three_fix_of_M22
    (hV : Hyp125 D V₀ V)
    (hcard : Nat.card (Vtil V₀ V hV.isElemAbelian) = 2 ^ 10)
    (hSp : IsSpor ↥(barSub V₀ V hV.isElemAbelian L) .M22)
    (hirr : IsIrrOn (barSub V₀ V hV.isElemAbelian L) ⊤ ⊥)
    (hK : K_M22TenPointThree) :
    ∀ w : Vtil V₀ V hV.isElemAbelian, w ≠ 1 →
      ∃ g ∈ barSub V₀ V hV.isElemAbelian L, orderOf g = 3 ∧ g w = w := by
  intro w hw
  have hsq : ∀ x : Vtil V₀ V hV.isElemAbelian, x * x = 1 := fun x => by
    simpa [pow_two] using s15_Infra_vtil_sq_eq_one V₀ V hV.isElemAbelian x
  have hirr' : ∀ U : Subgroup (Vtil V₀ V hV.isElemAbelian),
      (∀ g ∈ barSub V₀ V hV.isElemAbelian L, ∀ u ∈ U, g u ∈ U) → U = ⊥ ∨ U = ⊤ := by
    intro U hU
    exact hirr.2.2.2 U hU bot_le le_top
  exact hK (Vtil V₀ V hV.isElemAbelian) hsq hcard
    (barSub V₀ V hV.isElemAbelian L) hSp hirr' w hw

private theorem exists_lift_order_three_of_M22_point
    (hV : Hyp125 D V₀ V) (c : Ctx17_17 D V₀ V L)
    (hc : Subgroup.center (Bar2 L) = ⊥)
    (hL1 : barSub V₀ V hV.isElemAbelian L ≠ ⊥)
    (hpt : ∀ w : Vtil V₀ V hV.isElemAbelian, w ≠ 1 →
      ∃ g ∈ barSub V₀ V hV.isElemAbelian L, orderOf g = 3 ∧ g w = w)
    {x : IntMod V hV.isElemAbelian} (hx0 : x.val ∉ V₀) :
    ∃ x₁ : G, x₁ ∈ L ∧ orderOf x₁ = 3 ∧
      x₁ ∈ F11.CElt D.M V₀ x.val ∧ x₁ ∉ F11.CTilde D.M V₀ V := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let w : Vtil V₀ V hV.isElemAbelian := mkTil V₀ V hV.isElemAbelian x
  have hw1 : w ≠ 1 := by
    intro h
    apply hx0
    have h' := (mkTil_eq_iff V₀ V hV.isElemAbelian x 1).1 (h.trans (map_one _).symm)
    simpa using h'
  obtain ⟨g, hgbar, hgord, hgw⟩ := hpt w hw1
  obtain ⟨g0s, hg0L, hg0act⟩ := (mem_barSub V₀ V hV.isElemAbelian L g).1 hgbar
  let z : stabTil V₀ V := g0s ^ 3
  have hzact : actTil V₀ V hV.isElemAbelian z = 1 := by
    change actTil V₀ V hV.isElemAbelian (g0s ^ 3) = 1
    rw [map_pow, hg0act]
    simpa [hgord] using pow_orderOf_eq_one g
  have hzL : (z : G) ∈ L := by
    change (g0s : G) ^ 3 ∈ L
    exact L.pow_mem hg0L 3
  have hzC : (z : G) ∈ F11.CTilde D.M V₀ V := by
    rw [mem_cTilde_iff hV.isElemAbelian hV.pairFacts.le_normalizer]
    refine ⟨c.mem_calC.1.le hzL, ⟨z.2, ?_⟩⟩
    simpa using hzact
  have hzO2 : (z : G) ∈ pCoreOf 2 L :=
    inf_cTilde_le_pCoreOf_of_center_eq_bot hV c.mem_calC hL1 hc ⟨hzL, hzC⟩
  have hNp : IsPGroup 2 ↥(pCoreOf 2 L) :=
    (CFSG.pCore_isPGroup (p := 2) (G := ↥L)).map L.subtype
  obtain ⟨k, hk⟩ := IsPGroup.exists_orderOf_eq_pow (p := 2) hNp ⟨(z : G), hzO2⟩
  have hzordG : orderOf (z : G) = 2 ^ k := by
    have h := hk
    rw [← Subgroup.orderOf_coe (H := pCoreOf 2 L) ⟨(z : G), hzO2⟩] at h
    exact h
  have hzord : orderOf z = 2 ^ k := by
    rw [← Subgroup.orderOf_coe (H := stabTil V₀ V) z, hzordG]
  let d : ℕ := 2 ^ k
  have hd : d = orderOf z := by
    rw [hzord]
  let x1s : stabTil V₀ V := g0s ^ d
  have hx1act : actTil V₀ V hV.isElemAbelian x1s = g ^ d := by
    change actTil V₀ V hV.isElemAbelian (g0s ^ d) = g ^ d
    rw [map_pow, hg0act]
  have h3d : ¬ 3 ∣ d := by
    intro h3
    have h32 : 3 ∣ 2 := Nat.Prime.dvd_of_dvd_pow Nat.prime_three (by simpa [d] using h3)
    norm_num at h32
  have hgpow_ne : g ^ d ≠ 1 := by
    intro h
    have hdvd : orderOf g ∣ d := orderOf_dvd_iff_pow_eq_one.mpr h
    rw [hgord] at hdvd
    exact h3d hdvd
  have hx1s_ne : x1s ≠ 1 := by
    intro h
    apply hgpow_ne
    rw [← hx1act, h, map_one]
  have hx1cubeS : x1s ^ 3 = 1 := by
    have h : x1s ^ 3 = z ^ d := by
      change (g0s ^ d) ^ 3 = (g0s ^ 3) ^ d
      rw [← pow_mul, mul_comm, pow_mul]
    rw [h, hd]
    exact pow_orderOf_eq_one z
  have hx1cube : ((x1s : G)) ^ 3 = 1 := by
    simpa using congrArg (fun q : stabTil V₀ V => (q : G)) hx1cubeS
  have hx1ne : (x1s : G) ≠ 1 := fun h => hx1s_ne (Subtype.ext h)
  have hx1ord : orderOf (x1s : G) = 3 := orderOf_eq_prime hx1cube hx1ne
  have hx1L : (x1s : G) ∈ L := by
    change (g0s : G) ^ d ∈ L
    exact L.pow_mem hg0L d
  have hx1notC : (x1s : G) ∉ F11.CTilde D.M V₀ V := by
    intro hC
    obtain ⟨-, hstab, hact⟩ :=
      (mem_cTilde_iff hV.isElemAbelian hV.pairFacts.le_normalizer).1 hC
    have h1 : actTil V₀ V hV.isElemAbelian x1s = 1 := by
      simpa using hact
    rw [hx1act] at h1
    exact hgpow_ne h1
  have hx1CE : (x1s : G) ∈ F11.CElt D.M V₀ x.val := by
    refine ⟨c.mem_calC.1.le hx1L, stabTil_le_normalizer₀ V₀ V x1s.2, ?_⟩
    have hfix : actTil V₀ V hV.isElemAbelian x1s w = w := by
      rw [hx1act]
      have hpow : ∀ n : ℕ, (g ^ n) w = w := by
        intro n
        induction n with
        | zero => simp
        | succ n ih => rw [pow_succ', MulAut.mul_apply, ih, hgw]
      exact hpow d
    have h2 : mkTil V₀ V hV.isElemAbelian
        (actStab V₀ V hV.isElemAbelian x1s x) = mkTil V₀ V hV.isElemAbelian x := by
      rw [← actTil_mk, hfix]
    have h3 : (actStab V₀ V hV.isElemAbelian x1s x).val * x.val⁻¹ ∈ V₀ :=
      (mkTil_eq_iff V₀ V hV.isElemAbelian _ _).1 h2
    rw [actStab_apply_val] at h3
    simpa [mul_assoc] using h3
  exact ⟨(x1s : G), hx1L, hx1ord, hx1CE, hx1notC⟩

theorem one_lt_pRank_cElt_of_M22
    (hV : Hyp125 D V₀ V) (hx : DataExt D) (h61 : UC6.R6_1 D) (h127 : R127 D)
    (c : Ctx17_17 D V₀ V L) (hN : (L.subgroupOf D.M).Normal)
    (hcard4 : Nat.card V₀ ≤ 4)
    (hsig : D.sig = {3})
    (hbar : CFSG.Open.pRank 3 (Mbar D.M V₀ V hV.isElemAbelian) ≤ 2)
    (hc : Subgroup.center (Bar2 L) = ⊥)
    (hL1 : barSub V₀ V hV.isElemAbelian L ≠ ⊥)
    (hpt : ∀ w : Vtil V₀ V hV.isElemAbelian, w ≠ 1 →
      ∃ g ∈ barSub V₀ V hV.isElemAbelian L, orderOf g = 3 ∧ g w = w)
    (x : IntMod V hV.isElemAbelian) (hx0 : x.val ∉ V₀) :
    1 < CFSG.Open.pRank 3 (F11.CElt D.M V₀ x.val) := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨x₁, hx1L, hx1ord, hx1CE, hx1notC⟩ :=
    exists_lift_order_three_of_M22_point hV c hc hL1 hpt hx0
  obtain ⟨-, -, hCTge1⟩ :=
    pRank_three_M_eq_three hV hx h61 h127 hcard4 hsig hbar
  obtain ⟨E, hEC, -, hEcard⟩ :=
    CFSG.SectionRank.exists_pRank (p := 3) (by norm_num) (F11.CTilde D.M V₀ V)
  have h3dvdE : 3 ∣ Nat.card E := by
    rw [hEcard]
    exact dvd_pow_self 3 (by omega)
  obtain ⟨yE, hyEord⟩ := exists_prime_orderOf_dvd_card' (G := E) 3 h3dvdE
  let y : G := (yE : E)
  have hyC : y ∈ F11.CTilde D.M V₀ V := hEC yE.2
  have hyord : orderOf y = 3 := by
    change orderOf (yE : G) = 3
    rw [Subgroup.orderOf_coe]
    exact hyEord
  have hyM : y ∈ D.M := uc22p22q_ctilde_le hyC
  let N : Subgroup G := pCoreOf 2 L
  let Q : Subgroup G := Subgroup.zpowers x₁ ⊔ Subgroup.zpowers y
  have hx1Q : x₁ ∈ Q := Subgroup.mem_sup_left (Subgroup.mem_zpowers x₁)
  have hyQ : y ∈ Q := Subgroup.mem_sup_right (Subgroup.mem_zpowers y)
  have hyCE : y ∈ F11.CElt D.M V₀ x.val := by
    obtain ⟨-, hyN₀, hycomm⟩ := uc22p22q_mem_ctilde.1 hyC
    exact ⟨hyM, hyN₀, hycomm x.val x.val_mem⟩
  have hQCE : Q ≤ F11.CElt D.M V₀ x.val :=
    sup_le (Subgroup.zpowers_le.mpr hx1CE) (Subgroup.zpowers_le.mpr hyCE)
  have hQM : Q ≤ D.M := fun q hq => (hQCE hq).1
  have hQstab : Q ≤ stabTil V₀ V := by
    intro q hq
    have hqCE := hQCE hq
    exact ⟨hV.pairFacts.le_normalizer hqCE.1, hqCE.2.1⟩
  have hNnormM : (N.subgroupOf D.M).Normal := by
    dsimp [N]
    exact CFSG.RankThreeEvenClassification.Helpers.pCoreOf_normal_subgroupOf 2 L D.M
      c.mem_calC.1.le hN
  have hNleM : N ≤ D.M :=
    (CFSG.LieType.BorelTits.pCoreOf_le 2 L).trans c.mem_calC.1.le
  have hNnormDM : D.M ≤ normalizer (N : Set G) := by
    have h := (Subgroup.normal_subgroupOf_iff_le_normalizer hNleM).1 hNnormM
    simpa using h
  have hNnormQ : (N.subgroupOf Q).Normal := by
    refine ⟨?_⟩
    intro n hn q
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    have hqM : (q : G) ∈ D.M := hQM q.2
    have hconj := (Subgroup.mem_normalizer_iff.1 (hNnormDM hqM) (n : G)).1 hn
    simpa using hconj
  have : (N.subgroupOf Q).Normal := hNnormQ
  have hNp : IsPGroup 2 ↥N := by
    dsimp [N]
    exact (CFSG.pCore_isPGroup (p := 2) (G := ↥L)).map L.subtype
  have hO2C : N ≤ F11.CTilde D.M V₀ V := by
    have hbarN : barSub V₀ V hV.isElemAbelian N = ⊥ := by
      dsimp [N]
      exact TwelveTwentyThree.barSub_pCoreOf_eq_bot_of_isSubnormal hV.isElemAbelian
        c.mem_calC.1 (barSub_pCoreOf_eq_bot_of_hyp125 hV)
    refine (CFSG.LocalAnalysis.WeakClosure81.barSub_eq_bot_iff hV.isElemAbelian
      hV.pairFacts.le_normalizer hV.pairFacts.le_normalizer₀ ?_).1 hbarN
    dsimp [N]
    exact (CFSG.LieType.BorelTits.pCoreOf_le 2 L).trans c.mem_calC.1.le
  have hyN : y ∉ N := by
    intro hyNmem
    obtain ⟨n, hn⟩ := IsPGroup.exists_orderOf_eq_pow (p := 2) hNp ⟨y, hyNmem⟩
    have hy2 : orderOf y = 2 ^ n := by
      have h := hn
      rw [← Subgroup.orderOf_coe (H := N) ⟨y, hyNmem⟩] at h
      exact h
    rw [hyord] at hy2
    have h3 : 3 ∣ 2 ^ n := by
      rw [← hy2]
    have h32 : 3 ∣ 2 := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3
    norm_num at h32
  let R := Q ⧸ N.subgroupOf Q
  let π : Q →* R := QuotientGroup.mk' (N.subgroupOf Q)
  let x1q : Q := ⟨x₁, hx1Q⟩
  let yq : Q := ⟨y, hyQ⟩
  have hx1q3Q : x1q ^ 3 = 1 := by
    refine Subtype.ext ?_
    change x₁ ^ 3 = 1
    rw [← hx1ord]
    exact pow_orderOf_eq_one x₁
  have hyq3Q : yq ^ 3 = 1 := by
    refine Subtype.ext ?_
    change y ^ 3 = 1
    rw [← hyord]
    exact pow_orderOf_eq_one y
  have hx1q3 : (π x1q) ^ 3 = 1 := by
    rw [← map_pow, hx1q3Q, map_one]
  have hyq3 : (π yq) ^ 3 = 1 := by
    rw [← map_pow, hyq3Q, map_one]
  have hx1q_ne : π x1q ≠ 1 := by
    intro h
    have hmem : x1q ∈ N.subgroupOf Q := (QuotientGroup.eq_one_iff (N := N.subgroupOf Q) x1q).mp h
    exact hx1notC (hO2C (Subgroup.mem_subgroupOf.mp hmem))
  have hx1q_ord : orderOf (π x1q) = 3 := orderOf_eq_prime hx1q3 hx1q_ne
  have hyq_ne : π yq ≠ 1 := by
    intro h
    have hmem : yq ∈ N.subgroupOf Q := (QuotientGroup.eq_one_iff (N := N.subgroupOf Q) yq).mp h
    exact hyN (Subgroup.mem_subgroupOf.mp hmem)
  have hx1M : x₁ ∈ D.M := c.mem_calC.1.le hx1L
  have hconjC : x₁ * y * x₁⁻¹ ∈ F11.CTilde D.M V₀ V :=
    uc22p22q_ctilde_conj_mem hV.pairFacts.le_normalizer hV.pairFacts.le_normalizer₀
      hx1M hyC
  have hcommC : ⁅x₁, y⁆ ∈ F11.CTilde D.M V₀ V := by
    rw [commutatorElement_def]
    exact (F11.CTilde D.M V₀ V).mul_mem hconjC ((F11.CTilde D.M V₀ V).inv_mem hyC)
  have hLMnorm : D.M ≤ normalizer (L : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer c.mem_calC.1.le).1 hN
  have hyconjL : y * x₁ * y⁻¹ ∈ L :=
    (Subgroup.mem_normalizer_iff.1 (hLMnorm hyM) x₁).1 hx1L
  have hcommL : ⁅x₁, y⁆ ∈ L := by
    rw [commutatorElement_def]
    have e : x₁ * y * x₁⁻¹ * y⁻¹ = x₁ * (y * x₁ * y⁻¹)⁻¹ := by group
    rw [e]
    exact L.mul_mem hx1L (L.inv_mem hyconjL)
  have hcommN : ⁅x₁, y⁆ ∈ N :=
    inf_cTilde_le_pCoreOf_of_center_eq_bot hV c.mem_calC hL1 hc ⟨hcommL, hcommC⟩
  have hcommQ : ⁅x1q, yq⁆ ∈ N.subgroupOf Q := by
    rw [Subgroup.mem_subgroupOf]
    change Q.subtype ⁅x1q, yq⁆ ∈ N
    rw [map_commutatorElement Q.subtype x1q yq]
    simpa [x1q, yq] using hcommN
  have hcommR : ⁅π x1q, π yq⁆ = 1 := by
    rw [← map_commutatorElement π x1q yq]
    exact (QuotientGroup.eq_one_iff (N := N.subgroupOf Q) ⁅x1q, yq⁆).mpr hcommQ
  have hcommπ : Commute (π x1q) (π yq) :=
    commutatorElement_eq_one_iff_mul_comm.mp hcommR
  let φ : Q →* MulAut (Vtil V₀ V hV.isElemAbelian) :=
    (actTil V₀ V hV.isElemAbelian).comp (Subgroup.inclusion hQstab)
  have hφ_eq_one_of_mem_C : ∀ q : Q, (q : G) ∈ F11.CTilde D.M V₀ V → φ q = 1 := by
    intro q hq
    obtain ⟨-, hstab, hact⟩ :=
      (mem_cTilde_iff hV.isElemAbelian hV.pairFacts.le_normalizer).1 hq
    have hsub : (⟨(q : G), hQstab q.2⟩ : stabTil V₀ V) = ⟨(q : G), hstab⟩ :=
      Subtype.ext rfl
    change actTil V₀ V hV.isElemAbelian ⟨(q : G), hQstab q.2⟩ = 1
    rw [hsub]
    exact hact
  have hφx1_ne : φ x1q ≠ 1 := by
    intro h
    apply hx1notC
    rw [mem_cTilde_iff hV.isElemAbelian hV.pairFacts.le_normalizer]
    have h' : actTil V₀ V hV.isElemAbelian ⟨x₁, hQstab hx1Q⟩ = 1 := by
      change φ x1q = 1
      exact h
    exact ⟨hx1M, ⟨hQstab hx1Q, h'⟩⟩
  have hφx1_3 : (φ x1q) ^ 3 = 1 := by
    rw [← map_pow, hx1q3Q, map_one]
  have hφx1_ord : orderOf (φ x1q) = 3 := orderOf_eq_prime hφx1_3 hφx1_ne
  have hy_not_mem_A : π yq ∉ Subgroup.zpowers (π x1q) := by
    intro hmem
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
    have hker : yq⁻¹ * x1q ^ k ∈ N.subgroupOf Q := by
      refine (QuotientGroup.eq_one_iff (N := N.subgroupOf Q) (yq⁻¹ * x1q ^ k)).mp ?_
      change π (yq⁻¹ * x1q ^ k) = 1
      rw [map_mul, map_zpow, hk]
      simp
    have hxC : x₁ ^ k ∈ F11.CTilde D.M V₀ V := by
      have h1 : ((yq⁻¹ * x1q ^ k : Q) : G) ∈ F11.CTilde D.M V₀ V :=
        hO2C (Subgroup.mem_subgroupOf.mp hker)
      have h1' : y⁻¹ * x₁ ^ k ∈ F11.CTilde D.M V₀ V := by
        simpa [yq, x1q] using h1
      have h2 := (F11.CTilde D.M V₀ V).mul_mem hyC h1'
      simpa [mul_assoc] using h2
    have hφpow : φ (x1q ^ k) = 1 :=
      hφ_eq_one_of_mem_C (x1q ^ k) (by simpa [x1q] using hxC)
    have hφpow' : (φ x1q) ^ k = 1 := by
      rw [← map_zpow]
      exact hφpow
    have h3k : (3 : ℤ) ∣ k := by
      have hdvd : (orderOf (φ x1q) : ℤ) ∣ k := orderOf_dvd_iff_zpow_eq_one.mpr hφpow'
      rwa [hφx1_ord] at hdvd
    have h3kQ : (orderOf x1q : ℤ) ∣ k := by
      rw [show orderOf x1q = 3 from ?_]
      · exact_mod_cast h3k
      · refine orderOf_eq_prime hx1q3Q ?_
        intro h
        exact hx1q_ne (by simpa [x1q] using congrArg π h)
    have hx1q_pow : x1q ^ k = 1 := orderOf_dvd_iff_zpow_eq_one.mp h3kQ
    have hyqinv : yq⁻¹ ∈ N.subgroupOf Q := by
      rw [hx1q_pow, mul_one] at hker
      exact hker
    have hyqmem : yq ∈ N.subgroupOf Q := by
      simpa using (N.subgroupOf Q).inv_mem hyqinv
    exact hyN (Subgroup.mem_subgroupOf.mp hyqmem)
  have hcommA : ∀ a ∈ Subgroup.zpowers (π x1q), a * π yq = π yq * a := by
    intro a ha
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    exact (hcommπ.zpow_left k).eq
  obtain ⟨hE9, hE9card⟩ := CFSG.Quasithin.H13.U3.elemAbelian_sup_zpowers
    (p := 3) (A := Subgroup.zpowers (π x1q)) (y := π yq)
    (CFSG.Open.isElemAbelian_zpowers hx1q3) hy_not_mem_A hyq3 hcommA
  have h2Rtop : 2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup R) := by
    refine CFSG.SectionRank.le_pRank (p := 3) (by norm_num) le_top hE9 ?_
    rw [hE9card, Nat.card_zpowers, hx1q_ord]
    norm_num
  have h2R : 2 ≤ CFSG.pRank 3 R := by
    rw [CFSG.SectionRank.pRank_eq_open_pRank_top 3 R]
    exact h2Rtop
  have hcardNq : Nat.card ↥(N.subgroupOf Q) ∣ Nat.card ↥N := by
    have hle : (N.subgroupOf Q).map Q.subtype ≤ N := by
      intro z hz
      obtain ⟨q, hq, rfl⟩ := Subgroup.mem_map.mp hz
      exact Subgroup.mem_subgroupOf.mp hq
    have hcard := Subgroup.card_dvd_of_le (H := (N.subgroupOf Q).map Q.subtype) (K := N) hle
    rwa [Subgroup.card_map_of_injective Q.subtype_injective] at hcard
  have h3N : ¬ 3 ∣ Nat.card ↥(N.subgroupOf Q) := by
    have h3N' : ¬ 3 ∣ Nat.card ↥N := by
      obtain ⟨n, hn⟩ := IsPGroup.exists_card_eq (p := 2) hNp
      rw [hn]
      intro h
      have h32 : 3 ∣ 2 := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h
      norm_num at h32
    exact fun h => h3N' (h.trans hcardNq)
  have hquot := CFSG.GroupTheory.PRankCoprimeQuotient.pRank_quotient_eq_of_not_dvd
    (p := 3) Nat.prime_three (N.subgroupOf Q) h3N
  have h2Q : 2 ≤ CFSG.Open.pRank 3 Q := by
    rw [← CFSG.SectionRank.pRank_coe_eq_openPRank 3 Q, ← hquot]
    exact h2R
  exact lt_of_lt_of_le (by norm_num : 1 < 2)
    (h2Q.trans (CFSG.SectionRank.pRank_mono (p := 3) (by norm_num) hQCE))

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17
