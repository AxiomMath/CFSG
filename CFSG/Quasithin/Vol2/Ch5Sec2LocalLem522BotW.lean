module

public import CFSG.Quasithin.Vol2.Ch5Sec1L34Lem519
public import CFSG.Quasithin.Vol2.Ch5Sec2LocalLem522Bot

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin
open scoped commutatorElement

section General

variable {A : Type} [Group A]

theorem le_centralizer_of_perfect_of_mem {R V Y : Subgroup A} (hR : ⁅R, R⁆ = R)
    (hYc : ∀ a ∈ Y, ∀ b ∈ Y, a * b = b * a) (hRY : R ≤ Subgroup.centralizer (Y : Set A))
    (h : ∀ r ∈ R, ∀ x ∈ V, x⁻¹ * r * x * r⁻¹ ∈ Y) :
    R ≤ Subgroup.centralizer (V : Set A) := by
  intro r hr
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  have hmul : ∀ a ∈ R, ∀ b ∈ R, x⁻¹ * (a * b) * x * (a * b)⁻¹ =
      (x⁻¹ * a * x * a⁻¹) * (x⁻¹ * b * x * b⁻¹) := by
    intro a ha b hb
    have hc := (Subgroup.mem_centralizer_iff.mp (hRY ha)) _ (h b hb x hx)
    calc x⁻¹ * (a * b) * x * (a * b)⁻¹ = (x⁻¹ * a * x * a⁻¹) * (a * (x⁻¹ * b * x * b⁻¹)) * a⁻¹ := by
          group
      _ = (x⁻¹ * a * x * a⁻¹) * ((x⁻¹ * b * x * b⁻¹) * a) * a⁻¹ := by rw [hc]
      _ = (x⁻¹ * a * x * a⁻¹) * (x⁻¹ * b * x * b⁻¹) := by group
  have hinv : ∀ a ∈ R, x⁻¹ * a⁻¹ * x * a⁻¹⁻¹ = (x⁻¹ * a * x * a⁻¹)⁻¹ := by
    intro a ha
    have h1 := hmul a ha a⁻¹ (R.inv_mem ha)
    rw [mul_inv_cancel] at h1
    have h2 : x⁻¹ * (1 : A) * x * (1 : A)⁻¹ = 1 := by group
    rw [h2] at h1
    exact (eq_inv_of_mul_eq_one_right h1.symm)
  have hcomm : ⁅R, R⁆ ≤ Subgroup.centralizer ({x} : Set A) := by
    rw [Subgroup.commutator_le]
    intro a ha b hb
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hab : x⁻¹ * ⁅a, b⁆ * x * ⁅a, b⁆⁻¹ = 1 := by
      rw [commutatorElement_def]
      have e1 := hmul (a * b * a⁻¹) (R.mul_mem (R.mul_mem ha hb) (R.inv_mem ha)) b⁻¹
        (R.inv_mem hb)
      have e2 := hmul (a * b) (R.mul_mem ha hb) a⁻¹ (R.inv_mem ha)
      have e3 := hmul a ha b hb
      rw [e1, e2, e3, hinv a ha, hinv b hb]
      have hya := h a ha x hx
      have hyb := h b hb x hx
      rw [hYc _ hya _ hyb]
      group
    have : x⁻¹ * ⁅a, b⁆ * x = ⁅a, b⁆ := by
      calc x⁻¹ * ⁅a, b⁆ * x = x⁻¹ * ⁅a, b⁆ * x * ⁅a, b⁆⁻¹ * ⁅a, b⁆ := by group
        _ = ⁅a, b⁆ := by rw [hab, one_mul]
    calc ⁅a, b⁆ * x = x * (x⁻¹ * ⁅a, b⁆ * x) := by group
      _ = x * ⁅a, b⁆ := by rw [this]
  rw [hR] at hcomm
  exact (Subgroup.mem_centralizer_singleton_iff.mp (hcomm hr)).symm

theorem false_of_orderOf_five_of_card_le {W : Type} [Group W] [Finite W] (hW : IsPGroup 2 W)
    (hcard : Nat.card W ≤ 8) {α : MulAut W} (hα : orderOf α = 5) : False := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set P := Subgroup.zpowers α with hPdef
  have hP : IsPGroup 5 ↥P := IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hα, pow_one])
  have hmod := hP.card_modEq_card_fixedPoints W
  let F : Subgroup W :=
    { carrier := {w | α w = w}
      one_mem' := map_one α
      mul_mem' := fun {a b} ha hb => by
        simp only [Set.mem_ofPred_eq] at ha hb ⊢
        rw [map_mul, ha, hb]
      inv_mem' := fun {a} ha => by
        simp only [Set.mem_ofPred_eq] at ha ⊢
        rw [map_inv, ha] }
  have hFP : MulAction.fixedPoints ↥P W = (F : Set W) := by
    ext w
    simp only [MulAction.mem_fixedPoints, SetLike.mem_coe]
    constructor
    · intro hw
      exact hw ⟨α, Subgroup.mem_zpowers α⟩
    · intro hw g
      have hst : α ∈ MulAction.stabilizer (MulAut W) w := hw
      have hg : (g : MulAut W) ∈ MulAction.stabilizer (MulAut W) w :=
        (Subgroup.zpowers_le.mpr hst) g.2
      exact hg
  rw [hFP] at hmod
  obtain ⟨a, ha⟩ := IsPGroup.iff_card.mp hW
  obtain ⟨b, hb⟩ := IsPGroup.iff_card.mp (hW.to_subgroup F)
  have hdvd : Nat.card F ∣ Nat.card W := Subgroup.card_subgroup_dvd_card F
  have ha3 : a ≤ 3 := by
    by_contra hcon
    have : 2 ^ 4 ≤ 2 ^ a := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hba : b ≤ a := by
    rw [ha, hb] at hdvd
    exact (Nat.pow_dvd_pow_iff_le_right (by norm_num)).mp hdvd
  have hmod' : 2 ^ a ≡ 2 ^ b [MOD 5] := by
    rw [← ha, ← hb]
    exact hmod
  have hab : a = b := by
    interval_cases a <;> interval_cases b <;> first | rfl | exact absurd hmod' (by decide)
  have hFtop : F = ⊤ := Subgroup.eq_top_of_card_eq F (by rw [hb, ha, hab])
  have hα1 : α = 1 := by
    ext w
    have hw : w ∈ F := by rw [hFtop]; exact Subgroup.mem_top w
    exact hw
  rw [hα1, orderOf_one] at hα
  omega

end General

namespace Hyp5_0_1

variable {G : Type} [Group G] [Finite G] {T M L V : Subgroup G} {n : ℕ}

theorem sixteen_le_card_commutator_of (h : Hyp5_0_1 G T M L n)
    (hLV : L ≤ Subgroup.normalizer (V : Set G)) (hVc : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a)
    (hV2 : ∀ x ∈ V, x * x = 1) (hVL : ⁅V, L⁆ ≠ ⊥) (hn : Even n) : 16 ≤ Nat.card ↥⁅V, L⁆ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hWV : ⁅V, L⁆ ≤ V := Subgroup.le_normalizer_iff_commutator_le_left.mp hLV
  have hLW : L ≤ Subgroup.normalizer ((⁅V, L⁆ : Subgroup G) : Set G) :=
    le_normalizer_commutator_of hLV Subgroup.le_normalizer
  have hWc : ∀ a ∈ ⁅V, L⁆, ∀ b ∈ ⁅V, L⁆, a * b = b * a := fun a ha b hb => hVc a (hWV ha) b (hWV hb)
  have hWL : ⁅⁅V, L⁆, L⁆ ≠ ⊥ := by
    intro h0
    have hLC : L ≤ Subgroup.centralizer ((⁅V, L⁆ : Subgroup G) : Set G) := by
      intro l hl
      rw [Subgroup.mem_centralizer_iff]
      intro w hw
      have h1 := Subgroup.commutator_mem_commutator hw hl
      rw [h0, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at h1
      exact h1
    have hLV' := le_centralizer_of_perfect_of_mem h.commutator_eq hWc hLC (fun l hl x hx => by
      have h1 := Subgroup.commutator_mem_commutator (V.inv_mem hx) hl
      rw [commutatorElement_def, inv_inv] at h1
      exact h1)
    apply hVL
    rw [eq_bot_iff, Subgroup.commutator_le]
    intro v hv l hl
    rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
    exact (Subgroup.mem_centralizer_iff.mp (hLV' hl)) v hv
  have h1 := h.card_quot_dvd_card_autOn hLW hWL
  rw [card_of_lieModel_L2 (by have := h.two_le; omega) h.lie] at h1
  have h5 : 5 ∣ Nat.card ↥(autOn L ⁅V, L⁆) := by
    refine dvd_trans ?_ h1
    obtain ⟨k, rfl⟩ := hn
    refine Dvd.dvd.mul_left ?_ _
    have e : 4 ^ (k + k) = 16 ^ k := by rw [← two_mul, pow_mul]; norm_num
    rw [e]
    have h15 : 16 - 1 ∣ 16 ^ k - 1 ^ k := Nat.sub_dvd_pow_sub_pow 16 1 k
    rw [one_pow] at h15
    exact dvd_trans (by norm_num) h15
  obtain ⟨α, hα⟩ := exists_prime_orderOf_dvd_card' 5 h5
  have hV2' : IsPGroup 2 ↥V := by
    intro v
    refine ⟨1, Subtype.ext ?_⟩
    simpa [pow_one, sq] using hV2 v v.2
  have hW2 : IsPGroup 2 ↥⁅V, L⁆ := hV2'.to_le hWV
  by_contra hlt
  have hle : Nat.card ↥⁅V, L⁆ ≤ 8 := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hW2
    rw [hk] at hlt ⊢
    have hk3 : k ≤ 3 := by
      by_contra hk4
      have : 2 ^ 4 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    calc 2 ^ k ≤ 2 ^ 3 := Nat.pow_le_pow_right (by norm_num) hk3
      _ = 8 := by norm_num
  refine false_of_orderOf_five_of_card_le hW2 hle (α := (α : MulAut ↥⁅V, L⁆)) ?_
  rw [Subgroup.orderOf_coe]
  exact hα

theorem sixteen_le_card_commutator (h : Hyp5_0_1 G T M L n) (hV : IsCh5Module T L V)
    (hn : Even n) : 16 ≤ Nat.card ↥⁅V, L⁆ := by
  have hred := hV.isTwoReducedIn
  exact h.sixteen_le_card_commutator_of (le_sup_left.trans hred.2.1)
    (fun a ha b hb => congrArg Subtype.val (hred.2.2.1.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩))
    (fun x hx => by simpa [sq] using hred.2.2.1.2 x hx) hV.2.2 hn

end Hyp5_0_1

namespace Hyp5_2_2p

variable {G : Type} [Group G] [Finite G] {T M L V H B D L₂ Dp : Subgroup G} {n p : ℕ}

theorem commutator_facts (hyp : Hyp5_2_2p G T M L V H B D L₂ Dp n p) (h510 : Stmt5_1_10)
    (h331 : Stmt3_3_1) (hR : L2RankOneSylowFact) :
    ⁅V, L⁆ ≤ sec52S M H ∧ (∀ x ∈ ⁅V, L⁆, x ^ 2 = 1) ∧
      (∀ a ∈ ⁅V, L⁆, ∀ b ∈ ⁅V, L⁆, a * b = b * a) ∧
      L ⊔ T ≤ Subgroup.normalizer ((⁅V, L⁆ : Subgroup G) : Set G) ∧
      16 ≤ Nat.card ↥⁅V, L⁆ := by
  have h := hyp.toHyp5_0_1
  have hV := hyp.ch5Module
  have hred := hV.isTwoReducedIn
  have hLV : L ≤ Subgroup.normalizer (V : Set G) := le_sup_left.trans hred.2.1
  have hWV : ⁅V, L⁆ ≤ V := Subgroup.le_normalizer_iff_commutator_le_left.mp hLV
  have hTL : T ≤ Subgroup.normalizer (L : Set G) := h.T_le.trans h.normal
  have hVL : V ≤ Subgroup.normalizer (L : Set G) :=
    hred.1.trans (sup_le Subgroup.le_normalizer hTL)
  have hWL : ⁅V, L⁆ ≤ L := Subgroup.le_normalizer_iff_commutator_le_right.mp hVL
  have hVT : V ≤ T := h.V_le_T hV
  obtain ⟨-, -, -, -, hSL, -, -, -⟩ := hyp.S_facts h510 h331 hR
  have hWS : ⁅V, L⁆ ≤ sec52S M H := by
    intro x hx
    have hxTL : x ∈ T ⊓ L := ⟨hVT (hWV hx), hWL hx⟩
    rw [← hSL] at hxTL
    exact hxTL.1
  have hn : Even n := by
    rcases hyp.n_cases with h2 | h4 | h8
    · exact ⟨1, by omega⟩
    · exact ⟨2, by omega⟩
    · exact ⟨4, by omega⟩
  refine ⟨hWS, fun x hx => hred.2.2.1.2 x (hWV hx), fun a ha b hb =>
    congrArg Subtype.val (hred.2.2.1.1.is_comm.comm ⟨a, hWV ha⟩ ⟨b, hWV hb⟩),
    le_normalizer_commutator_of hred.2.1 (sup_le Subgroup.le_normalizer hTL),
    h.sixteen_le_card_commutator hV hn⟩

theorem commutator_le_pCoreOf (hyp : Hyp5_2_2p G T M L V H B D L₂ Dp n p) (h510 : Stmt5_1_10)
    (h331 : Stmt3_3_1) (hR : L2RankOneSylowFact) :
    ⁅V, L⁆ ≤ pCoreOf 2 (Dp ⊔ sec52S M H) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hWS, hW2, -, hN, -⟩ := hyp.commutator_facts h510 h331 hR
  obtain ⟨hST, -, -, -, -, -, -, -⟩ := hyp.S_facts h510 h331 hR
  have hDpL : Dp ≤ L := hyp.Dp_le.trans (hyp.notation59.2.1.1.trans inf_le_left)
  refine le_pCoreOf_of_le_normalizer 2 (hWS.trans le_sup_right) ?_ ?_
  · exact sup_le (hDpL.trans (le_sup_left.trans hN)) (hST.trans (le_sup_right.trans hN))
  · intro w
    exact ⟨1, Subtype.ext (by simpa [pow_one] using hW2 w w.2)⟩

end Hyp5_2_2p

end CFSG.Quasithin.H13
