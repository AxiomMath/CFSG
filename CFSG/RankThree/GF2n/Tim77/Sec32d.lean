module

public import CFSG.RankThree.GF2n.Tim77.Sec3Basic
public import CFSG.CGT.Timmesfeld75.BenderInputs3
import all CFSG.Timmesfeld.RootInvolutions.RootInvolutionSetting
public import CFSG.Quasithin.Background.F1Models
public import CFSG.ThirdParty.BrauerInduction.Background.Group.Basic
public import CFSG.Timmesfeld.Bridge.OddTranspDefs

public section

namespace CFSG.RankThree.GF2n.Tim77

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open CFSG.RankThree.GF2n.Stroth80 CFSG.Timmesfeld.RootInvolutions
open Subgroup
open scoped commutatorElement

section Abstract

variable {H : Type} [Group H]

theorem sec32d_commutator_eq_top (D : Set H) (hgen : Subgroup.closure D = ⊤)
    (hsingle : ∃ d₀ ∈ D, ∀ d ∈ D, ∃ g : H, d = g * d₀ * g⁻¹)
    (huv : ∃ u ∈ D, ∃ v ∈ D, u * v ∈ D) : _root_.commutator H = ⊤ := by
  obtain ⟨d₀, hd₀, hcls⟩ := hsingle
  obtain ⟨u, hu, v, hv, huv'⟩ := huv
  have hcomm : ∀ d ∈ D, d * d₀⁻¹ ∈ _root_.commutator H := by
    intro d hd
    obtain ⟨g, rfl⟩ := hcls d hd
    have h := Subgroup.commutator_mem_commutator (Subgroup.mem_top g) (Subgroup.mem_top d₀)
    rw [commutatorElement_def] at h
    exact h
  have hd0 : d₀ ∈ _root_.commutator H := by
    have h1 := hcomm u hu
    have h2 := hcomm v hv
    have h3 := hcomm (u * v) huv'
    have key : d₀ * (v * d₀⁻¹) = (u * d₀⁻¹)⁻¹ * (u * v * d₀⁻¹) := by group
    have h4 : d₀ * (v * d₀⁻¹) ∈ _root_.commutator H := by
      rw [key]
      exact (_root_.commutator H).mul_mem ((_root_.commutator H).inv_mem h1) h3
    have h5 := (_root_.commutator H).mul_mem h4 ((_root_.commutator H).inv_mem h2)
    have h6 : d₀ * (v * d₀⁻¹) * (v * d₀⁻¹)⁻¹ = d₀ := by group
    rw [h6] at h5
    exact h5
  have hnorm : (_root_.commutator H).Normal := by
    unfold _root_.commutator
    infer_instance
  have hle : Subgroup.closure D ≤ _root_.commutator H := by
    refine (Subgroup.closure_le _).mpr fun d hd => ?_
    obtain ⟨g, rfl⟩ := hcls d hd
    exact hnorm.conj_mem d₀ hd0 g
  rw [hgen] at hle
  exact top_le_iff.mp hle

theorem sec32d_disconnected (D : Set H)
    (htrans : ∀ x ∈ D, ∀ y ∈ D, ∀ z ∈ D, Commute x y → Commute y z → Commute x z)
    {a b : H} (ha : a ∈ D) (hb : b ∈ D) (hab : ¬ Commute a b) :
    CFSG.Timmesfeld.Connectivity.Disconnected D := by
  unfold CFSG.Timmesfeld.Connectivity.Disconnected
  by_contra hcon
  have key : ∀ x ∈ D, ∀ y, Relation.ReflTransGen (CFSG.Timmesfeld.Connectivity.CommRel D) x y →
      y ∈ D → Commute x y := by
    intro x hx y hxy
    induction hxy with
    | refl => intro _; exact Commute.refl x
    | tail _ hbc ih =>
      intro hc
      obtain ⟨hb', hc', hbc'⟩ := hbc
      exact htrans x hx _ hb' _ hc (ih hb') hbc'
  apply hab
  refine key a ha b ?_ hb
  by_contra h
  exact hcon ⟨a, ha, b, hb, h⟩

theorem sec32d_zStar_le_center (hperf : _root_.commutator H = ⊤)
    (hO : ∀ z ∈ CFSG.pCore 2 H, ∀ g : H, g * z = z * g) :
    CFSG.Timmesfeld.Bridge.zStar H ≤ Subgroup.center H := by
  intro z hz
  have hzq : QuotientGroup.mk' (CFSG.pCore 2 H) z ∈ Subgroup.center (H ⧸ CFSG.pCore 2 H) := hz
  have hc : ∀ g : H, z * g * z⁻¹ * g⁻¹ ∈ CFSG.pCore 2 H := by
    intro g
    rw [← QuotientGroup.eq_one_iff]
    have h := Subgroup.mem_center_iff.mp hzq (QuotientGroup.mk g)
    simp only [QuotientGroup.mk'_apply] at h
    simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv]
    rw [← h]
    group
  obtain ⟨c, hcdef⟩ : ∃ c : H → H, ∀ g, c g = z * g * z⁻¹ * g⁻¹ :=
    ⟨fun g => z * g * z⁻¹ * g⁻¹, fun _ => rfl⟩
  have hmemP : ∀ g, c g ∈ CFSG.pCore 2 H := fun g => by
    rw [hcdef]
    exact hc g
  have hcen : ∀ g, c g ∈ Subgroup.center H := fun g =>
    Subgroup.mem_center_iff.mpr (hO (c g) (hmemP g))
  have hc1 : c 1 = 1 := by rw [hcdef]; group
  have hmul : ∀ x y, c (x * y) = c x * c y := by
    intro x y
    have hxy : x * c y = c y * x := Subgroup.mem_center_iff.mp (hcen y) x
    have e : c (x * y) = c x * (x * c y * x⁻¹) := by
      rw [hcdef, hcdef, hcdef]
      group
    rw [e]
    have e2 : x * c y * x⁻¹ = c y := by rw [hxy]; group
    rw [e2]
  have hinv : ∀ x, c x⁻¹ = (c x)⁻¹ := by
    intro x
    have h := hmul x x⁻¹
    rw [mul_inv_cancel, hc1] at h
    exact (inv_eq_of_mul_eq_one_right h.symm).symm
  have hcomm_c : ∀ x y, c (x * y * x⁻¹ * y⁻¹) = 1 := by
    intro x y
    rw [hmul, hmul, hmul, hinv, hinv]
    have hcy : c y * c x = c x * c y := Subgroup.mem_center_iff.mp (hcen x) (c y)
    rw [← hcy]
    group
  have hcz : ∀ x y : H, z * ⁅x, y⁆ = ⁅x, y⁆ * z := by
    intro x y
    have h := hcomm_c x y
    rw [hcdef] at h
    rw [commutatorElement_def]
    calc z * (x * y * x⁻¹ * y⁻¹)
        = z * (x * y * x⁻¹ * y⁻¹) * z⁻¹ * (x * y * x⁻¹ * y⁻¹)⁻¹ *
            ((x * y * x⁻¹ * y⁻¹) * z) := by group
      _ = (x * y * x⁻¹ * y⁻¹) * z := by rw [h, one_mul]
  have hle : _root_.commutator H ≤ Subgroup.centralizer ({z} : Set H) := by
    refine Subgroup.commutator_le.mpr ?_
    intro x _ y _
    rw [Subgroup.mem_centralizer_iff]
    intro g hg
    rw [Set.mem_singleton_iff.mp hg]
    exact hcz x y
  refine Subgroup.mem_center_iff.mpr (fun g => ?_)
  have hg : g ∈ _root_.commutator H := by
    rw [hperf]
    exact Subgroup.mem_top g
  exact (Subgroup.mem_centralizer_iff.mp (hle hg) z (Set.mem_singleton z)).symm

end Abstract

theorem sec32d_comm_of_isElemAbelian {G : Type} [Group G] {K : Subgroup G}
    (hK : IsElemAbelian 2 K) {x y : G} (hx : x ∈ K) (hy : y ∈ K) : x * y = y * x :=
  congrArg Subtype.val (hK.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)

theorem sec32d_commute_of_invol {H : Type} [Group H] {x y : H} (hx : x * x = 1) (hy : y * y = 1)
    (hxy : (x * y) ^ 2 = 1) : Commute x y := by
  have hx' : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx
  have hy' : y⁻¹ = y := inv_eq_of_mul_eq_one_right hy
  have h1 : x * y = (x * y)⁻¹ := eq_inv_of_mul_eq_one_left (by rw [← pow_two]; exact hxy)
  rw [mul_inv_rev, hx', hy'] at h1
  exact h1

theorem sec32d_mem_of_sq_mem_of_odd {H : Type} [Group H] {K : Subgroup H} {x : H}
    (hx : x ^ 2 ∈ K) (hodd : Odd (orderOf x)) : x ∈ K := by
  obtain ⟨k, hk⟩ := hodd
  have hpow : x ^ (2 * k + 1) = 1 := by
    rw [← hk]
    exact pow_orderOf_eq_one x
  have e : x = (x ^ 2) ^ (k + 1) := by
    rw [← pow_mul, show 2 * (k + 1) = (2 * k + 1) + 1 by ring, pow_succ, hpow, one_mul]
  rw [e]
  exact K.pow_mem hx _

theorem sec32d_beta_of_bender {X : Type} [Group X]
    (h : CFSG.BenderSuzuki.IsBenderGroup X) : Tim77Cor2BetaList X := by
  unfold Tim77Cor2BetaList
  rcases h with ⟨n, hn, e⟩ | ⟨n, hn, e⟩ | ⟨n, hn, e⟩
  · exact Or.inl ⟨n, by omega, statedClassicalModel_psl2_of_mulEquiv hn e⟩
  · exact Or.inr (Or.inr ⟨2 * n + 1, by omega, lieModel_twistedB2_of_mulEquiv_szModel hn e⟩)
  · exact Or.inr (Or.inl ⟨n, by omega, statedClassicalModel_psu3_of_mulEquiv hn e⟩)

section Config

variable {G : Type} [Group G] [Finite G] {A Abar S₀ B : Subgroup G} {s : G}

theorem sec32d_mem_D_iff {t : G} :
    t ∈ Section4.D A Abar s ↔
      ∃ z ∈ Section3.Y A Abar s, ∃ a ∈ A, a ∉ Section3.A0 A Abar ∧ t = z * a * z⁻¹ :=
  Iff.rfl

theorem sec32d_mem_centralizer (hC : Sec3Ctx A Abar S₀ B)
    (hs : Section3.IsSChoice A Abar S₀ B s) : s ∈ centralizer (A : Set G) := by
  obtain ⟨b, hb, -, hcase⟩ := hs
  rcases hcase with ⟨-, rfl⟩ | ⟨-, x, -, -, -, -, hsC, -⟩
  · exact hC.b_le_centralizer hb
  · exact hsC

theorem sec32d_mem_normalizer_of_centralizer {T : Subgroup G} {x : G}
    (h : x ∈ centralizer (T : Set G)) : x ∈ normalizer (T : Set G) :=
  Subgroup.centralizer_le_normalizer _ h

theorem sec32d_A_le_Y : A ≤ Section3.Y A Abar s := le_sup_left.trans le_sup_left

theorem sec32d_Abar_le_Y : Abar ≤ Section3.Y A Abar s := le_sup_right.trans le_sup_left

theorem sec32d_conj_le_Y : conjSubgroup s Abar ≤ Section3.Y A Abar s := le_sup_right

theorem sec32d_N_le_normalizer (hC : Sec3Ctx A Abar S₀ B) (hsC : s ∈ centralizer (A : Set G)) :
    Section3.N A Abar s ≤ normalizer (A : Set G) := by
  have hs' : s ∈ normalizer (A : Set G) := sec32d_mem_normalizer_of_centralizer hsC
  refine sup_le (sup_le ?_ ?_) ?_
  · rw [hC.a0_eq]
    exact inf_le_left.trans Subgroup.le_normalizer
  · rw [hC.abar0_eq]
    exact inf_le_right
  · intro x hx
    have hy : s⁻¹ * x * s ∈ Abar ⊓ normalizer (A : Set G) := by
      rw [← hC.abar0_eq]
      exact mem_conjSubgroup.mp hx
    have hy' : s⁻¹ * x * s ∈ normalizer (A : Set G) := hy.2
    have e : x = s * (s⁻¹ * x * s) * s⁻¹ := by group
    rw [e]
    exact mul_mem (mul_mem hs' hy') (inv_mem hs')

theorem sec32d_inf_N_le (hC : Sec3Ctx A Abar S₀ B)
    (hNab : IsElemAbelian 2 (Section3.N A Abar s)) :
    A ⊓ Section3.N A Abar s ≤ Section3.A0 A Abar := by
  intro c hc
  obtain ⟨a, haL, ha1⟩ := Subgroup.exists_mem_ne_one_of_ne_bot hC.setup.Lb_ne_bot
  have haN : a ∈ Section3.N A Abar s := by
    have h : Section3.Abar0 A Abar ≤ Section3.N A Abar s := le_sup_right.trans le_sup_left
    exact h haL
  have hca : c * a = a * c := sec32d_comm_of_isElemAbelian hNab hc.2 haN
  exact hC.setup.mem_L_of_commute hc.1 (hC.setup.Lb_le haL) ha1 hca

theorem sec32d_D_not_mem_N (hC : Sec3Ctx A Abar S₀ B)
    (hNab : IsElemAbelian 2 (Section3.N A Abar s))
    (hNnorm : ∀ y ∈ Section3.Y A Abar s, y ∈ normalizer (Section3.N A Abar s : Set G))
    {t : G} (ht : t ∈ Section4.D A Abar s) : t ∉ Section3.N A Abar s := by
  obtain ⟨y, hy, a, ha, ha0, rfl⟩ := sec32d_mem_D_iff.mp ht
  intro hN
  have haN : a ∈ Section3.N A Abar s :=
    (Subgroup.mem_normalizer_iff.mp (hNnorm y hy) a).mpr hN
  exact ha0 (sec32d_inf_N_le hC hNab ⟨ha, haN⟩)

theorem sec32d_inf_normalizer_conj (hsC : s ∈ centralizer (A : Set G)) :
    A ⊓ normalizer (conjSubgroup s Abar : Set G) = A ⊓ normalizer (Abar : Set G) := by
  ext x
  rw [Subgroup.mem_inf, Subgroup.mem_inf]
  refine and_congr_right fun hxA => ?_
  have hxs : x * s = s * x := Subgroup.mem_centralizer_iff.mp hsC x hxA
  rw [← conjSubgroup_eq_self_iff, ← conjSubgroup_eq_self_iff, ← conjSubgroup_mul, hxs,
    conjSubgroup_mul]
  constructor
  · intro h
    have h' := congrArg (conjSubgroup s⁻¹) h
    simpa only [← conjSubgroup_mul, inv_mul_cancel_left, inv_mul_cancel, conjSubgroup_one] using h'
  · intro h
    rw [h]

theorem sec32d_exists_conj_s (hC : Sec3Ctx A Abar S₀ B) (hsC : s ∈ centralizer (A : Set G)) :
    ∃ x ∈ A ⊔ conjSubgroup s Abar, conjSubgroup s Abar = conjSubgroup x A := by
  obtain ⟨g, hg⟩ := hC.exists_abar_eq
  have hid := sec32d_inf_normalizer_conj (Abar := Abar) hsC
  let S : Prop24Setup A (conjSubgroup s Abar) (Section3.A0 A Abar)
      (conjSubgroup s Abar ⊓ normalizer (A : Set G))
      (Section3.A0 A Abar ⊔ (conjSubgroup s Abar ⊓ normalizer (A : Set G))) :=
    { elem := hC.setup.elem
      ti := hC.setup.ti
      conj := ⟨s * g, by rw [hg, conjSubgroup_mul]⟩
      hL := by rw [hC.a0_eq, hid]
      hLb := rfl
      hM := rfl
      ne_bot := hC.a0_ne_bot
      ne := hC.a0_ne }
  exact S.exists_conj_eq

theorem sec32d_D_conj {y t : G} (hy : y ∈ Section3.Y A Abar s)
    (ht : t ∈ Section4.D A Abar s) : y * t * y⁻¹ ∈ Section4.D A Abar s := by
  obtain ⟨z, hz, a, ha, ha0, rfl⟩ := sec32d_mem_D_iff.mp ht
  exact sec32d_mem_D_iff.mpr ⟨y * z, mul_mem hy hz, a, ha, ha0, by group⟩

theorem sec32d_D_subset_Y : Section4.D A Abar s ⊆ Section3.Y A Abar s := by
  intro t ht
  obtain ⟨z, hz, a, ha, -, rfl⟩ := sec32d_mem_D_iff.mp ht
  exact mul_mem (mul_mem hz (sec32d_A_le_Y ha)) (inv_mem hz)

theorem sec32d_gen (hC : Sec3Ctx A Abar S₀ B) (hs : Section3.IsSChoice A Abar S₀ B s)
    (hNnorm : ∀ y ∈ Section3.Y A Abar s, y ∈ normalizer (Section3.N A Abar s : Set G)) :
    ∀ y ∈ Section3.Y A Abar s,
      y ∈ Subgroup.closure (Section4.D A Abar s ∪ (Section3.N A Abar s : Set G)) := by
  have hsC := sec32d_mem_centralizer hC hs
  have hA0N : Section3.A0 A Abar ≤ Section3.N A Abar s := le_sup_left.trans le_sup_left
  have hKconj : ∀ y ∈ Section3.Y A Abar s,
      ∀ k ∈ Subgroup.closure (Section4.D A Abar s ∪ (Section3.N A Abar s : Set G)),
        y * k * y⁻¹ ∈ Subgroup.closure (Section4.D A Abar s ∪ (Section3.N A Abar s : Set G)) := by
    intro y hy k hk
    induction hk using Subgroup.closure_induction with
    | mem w hw =>
      rcases hw with hw | hw
      · exact Subgroup.subset_closure (Or.inl (sec32d_D_conj hy hw))
      · exact Subgroup.subset_closure (Or.inr ((Subgroup.mem_normalizer_iff.mp (hNnorm y hy) w).mp
          hw))
    | one =>
      rw [mul_one, mul_inv_cancel]
      exact one_mem _
    | mul a b _ _ iha ihb =>
      have e : y * (a * b) * y⁻¹ = (y * a * y⁻¹) * (y * b * y⁻¹) := by group
      rw [e]
      exact mul_mem iha ihb
    | inv a _ iha =>
      have e : y * a⁻¹ * y⁻¹ = (y * a * y⁻¹)⁻¹ := by group
      rw [e]
      exact inv_mem iha
  have hAK : A ≤ Subgroup.closure (Section4.D A Abar s ∪ (Section3.N A Abar s : Set G)) := by
    intro a ha
    by_cases ha0 : a ∈ Section3.A0 A Abar
    · exact Subgroup.subset_closure (Or.inr (hA0N ha0))
    · exact Subgroup.subset_closure
        (Or.inl (sec32d_mem_D_iff.mpr ⟨1, one_mem _, a, ha, ha0, by simp⟩))
  have hYK : Section3.Y A Abar s ≤
      Subgroup.closure (Section4.D A Abar s ∪ (Section3.N A Abar s : Set G)) := by
    refine sup_le (sup_le hAK ?_) ?_
    · obtain ⟨x, hx, hxeq⟩ := hC.setup.exists_conj_eq
      intro b hb
      rw [hxeq] at hb
      have hbA : x⁻¹ * b * x ∈ A := mem_conjSubgroup.mp hb
      have hxY : x ∈ Section3.Y A Abar s := (sup_le sec32d_A_le_Y sec32d_Abar_le_Y) hx
      have h := hKconj x hxY _ (hAK hbA)
      have e : x * (x⁻¹ * b * x) * x⁻¹ = b := by group
      rwa [e] at h
    · obtain ⟨x, hx, hxeq⟩ := sec32d_exists_conj_s hC hsC
      intro b hb
      rw [hxeq] at hb
      have hbA : x⁻¹ * b * x ∈ A := mem_conjSubgroup.mp hb
      have hxY : x ∈ Section3.Y A Abar s := (sup_le sec32d_A_le_Y sec32d_conj_le_Y) hx
      have h := hKconj x hxY _ (hAK hbA)
      have e : x * (x⁻¹ * b * x) * x⁻¹ = b := by group
      rwa [e] at h
  exact fun y hy => hYK hy

theorem sec32d_exists_outside (hC : Sec3Ctx A Abar S₀ B) (hs : Section3.IsSChoice A Abar S₀ B s)
    (hNnorm : ∀ y ∈ Section3.Y A Abar s, y ∈ normalizer (Section3.N A Abar s : Set G)) :
    ∃ b ∈ Section4.D A Abar s, b ∉ normalizer (A : Set G) := by
  by_contra hcon
  push_neg at hcon
  have hsC := sec32d_mem_centralizer hC hs
  have hK : Subgroup.closure (Section4.D A Abar s ∪ (Section3.N A Abar s : Set G)) ≤
      normalizer (A : Set G) := by
    refine (Subgroup.closure_le _).mpr ?_
    rintro g (hg | hg)
    · exact hcon g hg
    · exact sec32d_N_le_normalizer hC hsC hg
  have hAbar : Abar ≤ normalizer (A : Set G) := fun b hb =>
    hK (sec32d_gen hC hs hNnorm b (sec32d_Abar_le_Y hb))
  obtain ⟨-, ⟨-, hne⟩, -⟩ := hC.nota.choice
  apply hne
  unfold normalizerIn
  ext b
  simp only [Subgroup.mem_inf]
  exact ⟨fun h => h.1, fun h => ⟨h, hAbar h⟩⟩

theorem sec32d_exists_noncomm (hC : Sec3Ctx A Abar S₀ B) {b : G}
    (hb : b ∉ normalizer (A : Set G)) :
    ∃ a ∈ A, a ∉ Section3.A0 A Abar ∧ ¬ Commute a b := by
  by_contra hcon
  push_neg at hcon
  apply hb
  have hA0le : Section3.A0 A Abar ≤ A := by
    rw [hC.a0_eq]
    exact inf_le_left
  have hcA : ∀ x ∈ A, x * b = b * x := by
    intro x hx
    by_cases hx0 : x ∈ Section3.A0 A Abar
    · obtain ⟨a₀, ha₀A, ha₀⟩ := SetLike.exists_of_lt (lt_of_le_of_ne hA0le hC.a0_ne)
      have hxa : x * a₀ ∉ Section3.A0 A Abar := fun h =>
        ha₀ (by simpa using mul_mem (inv_mem hx0) h)
      have h1 : Commute (x * a₀) b := hcon (x * a₀) (mul_mem hx ha₀A) hxa
      have h2 : Commute a₀ b := hcon a₀ ha₀A ha₀
      have key : x * b * a₀ = b * x * a₀ := by
        calc x * b * a₀ = x * (b * a₀) := by group
          _ = x * (a₀ * b) := by rw [h2.eq]
          _ = x * a₀ * b := by group
          _ = b * (x * a₀) := h1.eq
          _ = b * x * a₀ := by group
      exact mul_right_cancel key
    · exact hcon x hx hx0
  exact sec32d_mem_normalizer_of_centralizer (Subgroup.mem_centralizer_iff.mpr
    (fun x hx => hcA x hx))

theorem sec32d_exists_third (_hC : Sec3Ctx A Abar S₀ B) (hA : IsElemAbelian 2 A)
    (hq : 2 < (Section3.A0 A Abar).relIndex A) {a : G} (ha : a ∈ A)
    (ha0 : a ∉ Section3.A0 A Abar) :
    ∃ a' ∈ A, a' ∉ Section3.A0 A Abar ∧ a⁻¹ * a' ∉ Section3.A0 A Abar := by
  by_contra hcon
  push_neg at hcon
  have hainv : a⁻¹ = a := inv_eq_of_mul_eq_one_right (by rw [← pow_two]; exact hA.2 a ha)
  have h2 : (Section3.A0 A Abar).relIndex A = 2 := by
    rw [Subgroup.relIndex_eq_two_iff]
    refine ⟨a, ha, fun b hb => ?_⟩
    by_cases hb0 : b ∈ Section3.A0 A Abar
    · have hba : b * a ∉ Section3.A0 A Abar := by
        intro h
        apply ha0
        simpa using mul_mem (inv_mem hb0) h
      unfold Xor
      simp [hb0, hba]
    · have hba : b * a ∈ Section3.A0 A Abar := by
        have h := hcon b hb hb0
        have hc : b * a = a⁻¹ * b := by
          rw [hainv]
          exact sec32d_comm_of_isElemAbelian hA hb ha
        rw [hc]
        exact h
      unfold Xor
      simp [hb0, hba]
  omega

end Config

structure Sec32dData (Y₀ : Type) [Group Y₀] (N₀ : Subgroup Y₀) (D₀ : Set Y₀) : Prop where
  sq : ∀ n ∈ N₀, n ^ 2 = 1
  disj : ∀ t ∈ D₀, t ∉ N₀
  invol : ∀ t ∈ D₀, t ^ 2 = 1
  ord : ∀ t ∈ D₀, ∀ t' ∈ D₀, orderOf (t * t') ∣ 2 ∨ Odd (orderOf (t * t'))
  conjD : ∀ g : Y₀, ∀ t ∈ D₀, g * t * g⁻¹ ∈ D₀
  gen : ∀ y : Y₀, y ∈ Subgroup.closure (D₀ ∪ (N₀ : Set Y₀))
  cent : ∀ t ∈ D₀, ∀ x ∈ D₀, ∀ y ∈ D₀, Commute x t → Commute y t → Commute x y
  nonc : ∃ a ∈ D₀, ∃ b ∈ D₀, ¬ Commute a b ∧ a * b ∉ N₀
  idx : ∃ a ∈ D₀, ∃ a' ∈ D₀, a⁻¹ * a' ∉ N₀ ∧ Commute a a' ∧ a * a' ∈ D₀
  single : ∃ d₀ ∈ D₀, ∀ d ∈ D₀, ∃ g : Y₀, d = g * d₀ * g⁻¹
  O2 : ∀ z ∈ CFSG.pCore 2 Y₀, ∀ g : Y₀, ⁅z, g⁆ ∈ N₀

section Quotient

variable {Y₀ : Type} [Group Y₀] {N₀ : Subgroup Y₀} {D₀ : Set Y₀}

theorem sec32d_q_isOddTransp [N₀.Normal] (h : Sec32dData Y₀ N₀ D₀) :
    CFSG.Timmesfeld.Bridge.Asc72.IsOddTransp (QuotientGroup.mk' N₀ '' D₀) := by
  refine ⟨?_, ?_⟩
  · rintro x ⟨t, ht, rfl⟩
    have h1 : QuotientGroup.mk' N₀ t ≠ 1 := fun h1 =>
      h.disj t ht ((QuotientGroup.eq_one_iff t).mp h1)
    have h2 : QuotientGroup.mk' N₀ t ^ 2 = 1 := by
      rw [← map_pow, h.invol t ht, map_one]
    exact orderOf_eq_prime h2 h1
  · rintro x ⟨t, ht, rfl⟩ y ⟨t', ht', rfl⟩
    rw [← map_mul]
    have hd := orderOf_map_dvd (QuotientGroup.mk' N₀) (t * t')
    rcases h.ord t ht t' ht' with h2 | hodd
    · exact Or.inl (hd.trans h2)
    · exact Or.inr (Odd.of_dvd_nat hodd hd)

theorem sec32d_q_normal [N₀.Normal] (h : Sec32dData Y₀ N₀ D₀) :
    CFSG.Timmesfeld.Connectivity.IsNormalSet (QuotientGroup.mk' N₀ '' D₀) := by
  rintro g x ⟨t, ht, rfl⟩
  obtain ⟨g', rfl⟩ := QuotientGroup.mk_surjective g
  exact ⟨g' * t * g'⁻¹, h.conjD g' t ht, by simp⟩

theorem sec32d_q_closure [N₀.Normal] (h : Sec32dData Y₀ N₀ D₀) :
    Subgroup.closure (QuotientGroup.mk' N₀ '' D₀) = ⊤ := by
  rw [eq_top_iff]
  have key : ∀ z ∈ Subgroup.closure (D₀ ∪ (N₀ : Set Y₀)),
      QuotientGroup.mk' N₀ z ∈ Subgroup.closure (QuotientGroup.mk' N₀ '' D₀) := by
    intro z hz
    induction hz using Subgroup.closure_induction with
    | mem w hw =>
      rcases hw with hw | hw
      · exact Subgroup.subset_closure ⟨w, hw, rfl⟩
      · have e : QuotientGroup.mk' N₀ w = 1 := (QuotientGroup.eq_one_iff w).mpr hw
        rw [e]
        exact one_mem _
    | one => exact one_mem _
    | mul a b _ _ iha ihb =>
      rw [map_mul]
      exact mul_mem iha ihb
    | inv a _ iha =>
      rw [map_inv]
      exact inv_mem iha
  intro x _
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective x
  exact key y (h.gen y)

theorem sec32d_q_sq_mem [N₀.Normal] (h : Sec32dData Y₀ N₀ D₀) {t t' : Y₀} (ht : t ∈ D₀)
    (ht' : t' ∈ D₀) (hc : Commute (QuotientGroup.mk' N₀ t) (QuotientGroup.mk' N₀ t')) :
    (t * t') ^ 2 ∈ N₀ := by
  have hsq : (QuotientGroup.mk' N₀ t * QuotientGroup.mk' N₀ t') ^ 2 = 1 := by
    rw [hc.mul_pow 2, ← map_pow, ← map_pow, h.invol t ht, h.invol t' ht', map_one, mul_one]
  have : QuotientGroup.mk' N₀ ((t * t') ^ 2) = 1 := by
    rw [map_pow, map_mul]
    exact hsq
  exact (QuotientGroup.eq_one_iff _).mp this

theorem sec32d_q_commute_lift [N₀.Normal] (h : Sec32dData Y₀ N₀ D₀) {t t' : Y₀} (ht : t ∈ D₀)
    (ht' : t' ∈ D₀) (hne : QuotientGroup.mk' N₀ t ≠ QuotientGroup.mk' N₀ t')
    (hc : Commute (QuotientGroup.mk' N₀ t) (QuotientGroup.mk' N₀ t')) : Commute t t' := by
  have ht2 : t * t = 1 := by rw [← pow_two]; exact h.invol t ht
  have ht2' : t' * t' = 1 := by rw [← pow_two]; exact h.invol t' ht'
  rcases h.ord t ht t' ht' with h2 | hodd
  · exact sec32d_commute_of_invol ht2 ht2' (orderOf_dvd_iff_pow_eq_one.mp h2)
  · exfalso
    have hmem : t * t' ∈ N₀ := sec32d_mem_of_sq_mem_of_odd (sec32d_q_sq_mem h ht ht' hc) hodd
    have h1 : QuotientGroup.mk' N₀ t * QuotientGroup.mk' N₀ t' = 1 := by
      rw [← map_mul]
      exact (QuotientGroup.eq_one_iff _).mpr hmem
    have hsqt' : QuotientGroup.mk' N₀ t' * QuotientGroup.mk' N₀ t' = 1 := by
      rw [← map_mul, ht2', map_one]
    apply hne
    exact mul_right_cancel (h1.trans hsqt'.symm)

theorem sec32d_q_trans [N₀.Normal] (h : Sec32dData Y₀ N₀ D₀) :
    ∀ x ∈ QuotientGroup.mk' N₀ '' D₀, ∀ y ∈ QuotientGroup.mk' N₀ '' D₀,
      ∀ z ∈ QuotientGroup.mk' N₀ '' D₀, Commute x y → Commute y z → Commute x z := by
  rintro _ ⟨t₁, ht₁, rfl⟩ _ ⟨t₂, ht₂, rfl⟩ _ ⟨t₃, ht₃, rfl⟩ h12 h23
  by_cases e12 : QuotientGroup.mk' N₀ t₁ = QuotientGroup.mk' N₀ t₂
  · rw [e12]
    exact h23
  by_cases e23 : QuotientGroup.mk' N₀ t₂ = QuotientGroup.mk' N₀ t₃
  · rw [← e23]
    exact h12
  have c12 := sec32d_q_commute_lift h ht₁ ht₂ e12 h12
  have c23 := sec32d_q_commute_lift h ht₂ ht₃ e23 h23
  have c13 : Commute t₁ t₃ := h.cent t₂ ht₂ t₁ ht₁ t₃ ht₃ c12 c23.symm
  exact c13.map _

theorem sec32d_q_noncomm [N₀.Normal] (h : Sec32dData Y₀ N₀ D₀) :
    ∃ a ∈ QuotientGroup.mk' N₀ '' D₀, ∃ b ∈ QuotientGroup.mk' N₀ '' D₀, ¬ Commute a b := by
  obtain ⟨a, ha, b, hb, hab, habN⟩ := h.nonc
  refine ⟨QuotientGroup.mk' N₀ a, ⟨a, ha, rfl⟩, QuotientGroup.mk' N₀ b, ⟨b, hb, rfl⟩,
    fun hc => ?_⟩
  have ha2 : a * a = 1 := by
    rw [← pow_two]
    exact h.invol a ha
  have hb2 : b * b = 1 := by
    rw [← pow_two]
    exact h.invol b hb
  rcases h.ord a ha b hb with h2 | hodd
  · exact hab (sec32d_commute_of_invol ha2 hb2 (orderOf_dvd_iff_pow_eq_one.mp h2))
  · exact habN (sec32d_mem_of_sq_mem_of_odd (sec32d_q_sq_mem h ha hb hc) hodd)

theorem sec32d_q_disc [N₀.Normal] (h : Sec32dData Y₀ N₀ D₀) :
    CFSG.Timmesfeld.Connectivity.Disconnected (QuotientGroup.mk' N₀ '' D₀) := by
  obtain ⟨a, ha, b, hb, hab⟩ := sec32d_q_noncomm h
  exact sec32d_disconnected _ (sec32d_q_trans h) ha hb hab

theorem sec32d_q_uv [N₀.Normal] (h : Sec32dData Y₀ N₀ D₀) :
    ∃ u ∈ QuotientGroup.mk' N₀ '' D₀, ∃ v ∈ QuotientGroup.mk' N₀ '' D₀,
      u ≠ v ∧ Commute u v ∧ u * v ∈ QuotientGroup.mk' N₀ '' D₀ := by
  obtain ⟨a, ha, a', ha', hne, hc, haa⟩ := h.idx
  refine ⟨QuotientGroup.mk' N₀ a, ⟨a, ha, rfl⟩, QuotientGroup.mk' N₀ a', ⟨a', ha', rfl⟩,
    ?_, hc.map _, ⟨a * a', haa, by simp⟩⟩
  intro e
  have e' : (a : Y₀ ⧸ N₀) = a' := e
  exact hne (QuotientGroup.eq.mp e')

theorem sec32d_q_perfect [N₀.Normal] (h : Sec32dData Y₀ N₀ D₀) :
    _root_.commutator (Y₀ ⧸ N₀) = ⊤ := by
  obtain ⟨d₀, hd₀, hcls⟩ := h.single
  obtain ⟨u, hu, v, hv, -, -, huv⟩ := sec32d_q_uv h
  refine sec32d_commutator_eq_top _ (sec32d_q_closure h)
    ⟨QuotientGroup.mk' N₀ d₀, ⟨d₀, hd₀, rfl⟩, ?_⟩ ⟨u, hu, v, hv, huv⟩
  rintro _ ⟨d, hd, rfl⟩
  obtain ⟨g, hg⟩ := hcls d hd
  exact ⟨QuotientGroup.mk' N₀ g, by rw [hg]; simp⟩

theorem sec32d_q_O2 [N₀.Normal] (h : Sec32dData Y₀ N₀ D₀) :
    ∀ z ∈ CFSG.pCore 2 (Y₀ ⧸ N₀), ∀ g : Y₀ ⧸ N₀, g * z = z * g := by
  have hP : (CFSG.pCore 2 (Y₀ ⧸ N₀)).comap (QuotientGroup.mk' N₀) ≤ CFSG.pCore 2 Y₀ := by
    show _ ≤ sSup {K : Subgroup Y₀ | K.Normal ∧ IsPGroup 2 K}
    refine le_sSup ⟨inferInstance, ?_⟩
    intro x
    obtain ⟨n, hn⟩ := CFSG.pCore_isPGroup
      (⟨QuotientGroup.mk' N₀ x.1, x.2⟩ : CFSG.pCore 2 (Y₀ ⧸ N₀))
    have h1 : QuotientGroup.mk' N₀ (x.1 ^ 2 ^ n) = 1 := by
      rw [map_pow]
      have := congrArg Subtype.val hn
      simpa using this
    have hmem : x.1 ^ 2 ^ n ∈ N₀ := (QuotientGroup.eq_one_iff _).mp h1
    have hsq2 : (x.1 ^ 2 ^ n) ^ 2 = 1 := h.sq _ hmem
    refine ⟨n + 1, Subtype.ext ?_⟩
    simp only [SubgroupClass.coe_pow, OneMemClass.coe_one]
    rw [pow_succ, pow_mul]
    exact hsq2
  intro z hz g
  obtain ⟨t, rfl⟩ := QuotientGroup.mk_surjective z
  obtain ⟨s', rfl⟩ := QuotientGroup.mk_surjective g
  have ht : t ∈ CFSG.pCore 2 Y₀ := hP hz
  have hcomm := h.O2 t ht s'
  have h1 : QuotientGroup.mk' N₀ ⁅t, s'⁆ = 1 := (QuotientGroup.eq_one_iff _).mpr hcomm
  simp only [commutatorElement_def, map_mul, map_inv, QuotientGroup.mk'_apply] at h1
  have e : (t : Y₀ ⧸ N₀) * (s' : Y₀ ⧸ N₀) = (s' : Y₀ ⧸ N₀) * (t : Y₀ ⧸ N₀) := by
    calc (t : Y₀ ⧸ N₀) * (s' : Y₀ ⧸ N₀)
        = (t : Y₀ ⧸ N₀) * (s' : Y₀ ⧸ N₀) * (t : Y₀ ⧸ N₀)⁻¹ * (s' : Y₀ ⧸ N₀)⁻¹ *
            ((s' : Y₀ ⧸ N₀) * (t : Y₀ ⧸ N₀)) := by group
      _ = (s' : Y₀ ⧸ N₀) * (t : Y₀ ⧸ N₀) := by rw [h1, one_mul]
  exact e.symm

end Quotient

end CFSG.RankThree.GF2n.Tim77
