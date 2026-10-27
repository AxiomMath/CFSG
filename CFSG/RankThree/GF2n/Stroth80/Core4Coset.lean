module

public import CFSG.RankThree.GF2n.Stroth80.Core4Frame
public import CFSG.RankThree.GF2n.Stroth80.Core4Meet
public import CFSG.RankThree.GF2n.Stroth80.HeringSec93Rt
public import CFSG.RankThree.GF2n.Stroth80.Core4StepB
public import CFSG.RankThree.GF2n.Stroth80.HeringSec97F4A

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix Pointwise


@[expose] def Sec97CosetStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B) (n : ℕ) (t : G),
    Sec9Hyp hc n t → ∀ X Y : Subgroup G, HS9.Split95 M Q Z B t X Y →
      ∀ Z0 : Subgroup G, IsCentrePre Z0 (Rt M (LB M Q B) t) Q →
        ∀ x ∈ LB M Q B ⊓ hc.CN t, x ∉ Z0 → (∃ s ∈ Z0, ConjMod M Q s x) →
          ∀ c ∈ Z0, ∃ y ∈ hc.CN t, ⁅x, y⁆ * c⁻¹ ∈ Q

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

namespace HS9

theorem relIndex_kappa_ge (h34 : Stroth34Statement) (hc : Ctx M Q Z B) {n : ℕ} {t : G}
    (hs : Sec9Hyp hc n t) {X Y : Subgroup G} (hsplit : Split95 M Q Z B t X Y)
    (h4 : Sec4Concl M Q Z B X Y) (h2 : TwoConcl M Q B X) {h : G} (hh : h ∈ M)
    (hα : (Subgroup.normalizer (LB M Q (conjSubgroup h B) : Set G)).relIndex (LB M Q B) ≤
      Nat.card Z) :
    Nat.card Z ^ (n - 3) ≤ Q.relIndex ((LB M Q B ⊓ X) ⊓
      Subgroup.normalizer ((conjSubgroup h (LB M Q B ⊓ X) : Subgroup G) : Set G)) := by
  classical
  set L := LB M Q B with hL
  set E := L ⊓ X with hE
  set N := Subgroup.normalizer (LB M Q (conjSubgroup h B) : Set G) with hN
  set K := E ⊓ Subgroup.normalizer ((conjSubgroup h E : Subgroup G) : Set G) with hK
  have hLF : LB M Q (conjSubgroup h B) = conjSubgroup h L := hc.LB_conj hh
  have hQX : Q ≤ X := hsplit.1.1
  have hQL : Q ≤ L := le_sup_left
  have hQE : Q ≤ E := le_inf hQL hQX
  have hqq : 0 < Nat.card Z := Nat.card_pos
  have hn3 : 3 ≤ n := hs.toSec5.n_gt
  have hEL : E.relIndex L = Nat.card Z := relIndex_LB_inf_X hc hsplit h4
  have hLM : L ≤ M := hc.LB_le_M
  have hEN : E ⊓ N ≤ K := by
    intro x hx
    refine ⟨hx.1, ?_⟩
    have hxM : x ∈ M := hLM hx.1.1
    have hxN : conjSubgroup x (conjSubgroup h L) = conjSubgroup h L := by
      rw [← hLF]
      exact conjSubgroup_eq_self_iff.mpr hx.2
    have hn : conjSubgroup (h⁻¹ * x * h) L = L := by
      rw [conjSubgroup_mul, conjSubgroup_mul, hxN, conjSubgroup_inv_conj_self]
    have hnM : h⁻¹ * x * h ∈ M := M.mul_mem (M.mul_mem (M.inv_mem hh) hxM) hh
    have hEn := conj_E_eq_of_normalizes_LB h2 hnM hn
    refine conjSubgroup_eq_self_iff.mp ?_
    calc conjSubgroup x (conjSubgroup h E)
        = conjSubgroup (x * h) E := (conjSubgroup_mul _ _ _).symm
      _ = conjSubgroup (h * (h⁻¹ * x * h)) E := by rw [show h * (h⁻¹ * x * h) = x * h by group]
      _ = conjSubgroup h (conjSubgroup (h⁻¹ * x * h) E) := conjSubgroup_mul _ _ _
      _ = conjSubgroup h E := by rw [hEn]
  have hQLF : Q ≤ LB M Q (conjSubgroup h B) := le_sup_left
  have hQEN : Q ≤ E ⊓ N := le_inf hQE (hQLF.trans Subgroup.le_normalizer)
  have hEL' : E ⊓ N ≤ L := inf_le_left.trans inf_le_left
  have hdec : Q.relIndex (E ⊓ N) * (E ⊓ N).relIndex L = Nat.card Z ^ (n - 1) := by
    rw [Subgroup.relIndex_mul_relIndex Q (E ⊓ N) L hQEN hEL', relIndex_Q_LB h34 hc hs.toSec5]
  have hb : (E ⊓ N).relIndex L ≤ Nat.card Z * Nat.card Z := by
    refine (Subgroup.relIndex_inf_le (H := E) (K := N) (L := L)).trans ?_
    rw [hEL]
    exact Nat.mul_le_mul_left _ hα
  have hpow : Nat.card Z ^ (n - 1) = Nat.card Z ^ (n - 3) * (Nat.card Z * Nat.card Z) := by
    rw [← pow_two, ← pow_add]
    congr 1
    omega
  have ha : Nat.card Z ^ (n - 3) ≤ Q.relIndex (E ⊓ N) := by
    by_contra hlt
    push Not at hlt
    have h5 : Q.relIndex (E ⊓ N) * (E ⊓ N).relIndex L <
        Nat.card Z ^ (n - 3) * (Nat.card Z * Nat.card Z) :=
      lt_of_le_of_lt (Nat.mul_le_mul_left _ hb)
        (Nat.mul_lt_mul_of_pos_right hlt (Nat.mul_pos hqq hqq))
    rw [hdec, hpow] at h5
    exact lt_irrefl _ h5
  have hmul : Q.relIndex (E ⊓ N) * (E ⊓ N).relIndex K = Q.relIndex K :=
    Subgroup.relIndex_mul_relIndex Q (E ⊓ N) K hQEN hEN
  calc Nat.card Z ^ (n - 3) ≤ Q.relIndex (E ⊓ N) := ha
    _ ≤ Q.relIndex (E ⊓ N) * (E ⊓ N).relIndex K :=
        Nat.le_mul_of_pos_right _ (relIndex_pos' _ _)
    _ = Q.relIndex K := hmul

theorem exists_a2_in_kappa (h34 : Stroth34Statement) (h311a : Stroth311aStatement)
    (hc : Ctx M Q Z B) {n : ℕ} {t : G} (hs : Sec9Hyp hc n t) {X Y : Subgroup G}
    (hsplit : Split95 M Q Z B t X Y) (h4 : Sec4Concl M Q Z B X Y) (h2 : TwoConcl M Q B X)
    {Z0 : Subgroup G} (hZ0 : IsCentrePre Z0 (Rt M (LB M Q B) t) Q) (hcen : Centre95 hc t Z0)
    {h : G} (hh : h ∈ M) (hFB : conjSubgroup h B ≤ QB B)
    (hbad : ∃ s ∈ Z0, ∃ g ∈ M, g * s * g⁻¹ ∈ LB M Q B ⊓ hc.CN t ∧ g * s * g⁻¹ ∉ Z0)
    (hcoset : ∀ x ∈ LB M Q B ⊓ hc.CN t, x ∉ Z0 → (∃ s ∈ Z0, ConjMod M Q s x) →
      ∀ c ∈ Z0, ∃ y ∈ hc.CN t, ⁅x, y⁆ * c⁻¹ ∈ Q) :
    ∃ s ∈ Z0, s ∉ Q ∧ ∃ g ∈ M, ∃ e ∈ LB M Q B ⊓ X, e ∉ Q ∧
      e ∈ Subgroup.normalizer ((conjSubgroup h (LB M Q B ⊓ X) : Subgroup G) : Set G) ∧
      e * (g * s * g⁻¹)⁻¹ ∈ Q := by
  classical
  have hs5 := hs.toSec5
  have hQn : M ≤ Subgroup.normalizer (Q : Set G) := hc.hyp.Q_normal.2
  have hQZ0 : Q ≤ Z0 := hc.Q_le_centre hs5.mem hZ0
  have hNX : hc.CN t ≤ X := (sec97Head_of h34 h311a G M Q Z B hc n t hs X Y hsplit).1
  have hNR : hc.CN t ≤ Rt M (LB M Q B) t := fun x hx => (Ctx.mem_CN.mp hx).1
  have hLM : LB M Q B ≤ M := hc.LB_le_M
  have hZ0L : Z0 ≤ LB M Q B := fun z hz => (hcen.1 hz).1
  have hZ0E : Z0 ≤ LB M Q B ⊓ X := fun z hz => ⟨(hcen.1 hz).1, hNX (hcen.1 hz).2⟩
  set E := LB M Q B ⊓ X with hE
  set E1 := conjSubgroup h E with hE1
  set κ := E ⊓ Subgroup.normalizer (E1 : Set G) with hκ
  have hQL : Q ≤ LB M Q B := le_sup_left
  have hQX : Q ≤ X := hsplit.1.1
  have hQE : Q ≤ E := le_inf hQL hQX
  have hQh : conjSubgroup h Q = Q := hc.conj_Q_eq hh
  have hQE1 : Q ≤ E1 := by
    calc Q = conjSubgroup h Q := hQh.symm
      _ ≤ E1 := Subgroup.map_mono hQE
  have hQκ : Q ≤ κ := le_inf hQE (hQE1.trans Subgroup.le_normalizer)
  obtain ⟨s₀, hs₀, g₀, hg₀, hxT, hxZ⟩ := hbad
  have hs₀Q : s₀ ∉ Q := by
    intro hsQ
    apply hxZ
    exact hQZ0 ((Subgroup.mem_normalizer_iff.mp (hQn hg₀) s₀).mp hsQ)
  by_cases hA : ∃ u ∈ Z0 ⊓ κ, u ∉ Q
  · obtain ⟨u, hu, huQ⟩ := hA
    refine ⟨u, hu.1, huQ, 1, M.one_mem, u, hu.2.1, huQ, hu.2.2, ?_⟩
    rw [show u * (1 * u * 1⁻¹)⁻¹ = 1 by group]
    exact Q.one_mem
  push Not at hA
  have hconj : ∀ z ∈ Z0, ∀ k ∈ κ, z * k * z⁻¹ ∈ κ := by
    intro z hz k hk
    have hq : ⁅z, k⁆ ∈ Q := hc.commutator_LB_le_Q
      (Subgroup.commutator_mem_commutator (hZ0L hz) hk.1.1)
    have e : z * k * z⁻¹ = ⁅z, k⁆ * k := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact κ.mul_mem (hQκ hq) hk
  have hZ0N : Z0 ≤ Subgroup.normalizer (κ : Set G) := by
    intro z hz
    rw [Subgroup.mem_normalizer_iff]
    intro k
    constructor
    · exact hconj z hz k
    · intro hk
      have := hconj z⁻¹ (Z0.inv_mem hz) _ hk
      simpa [mul_assoc] using this
  have hκZ : κ ⊓ Z0 = Q := le_antisymm (fun u hu => hA u ⟨hu.2, hu.1⟩) (le_inf hQκ hQZ0)
  have hQcard : ∀ H : Subgroup G, Q ≤ H → Q.relIndex H * Nat.card Q = Nat.card H := by
    intro H hH
    have := Subgroup.relIndex_mul_card (H := Q) (K := H)
    rwa [inf_of_le_left hH] at this
  have hmulcard := card_sup_mul_card_inf_of_le_normalizer (L := κ) (E := Z0) hZ0N
  rw [hκZ] at hmulcard
  have hsupQ : Q ≤ κ ⊔ Z0 := hQκ.trans le_sup_left
  have hc1 := hQcard (κ ⊔ Z0) hsupQ
  have hc2 := hQcard κ hQκ
  have hc3 := hQcard Z0 hQZ0
  have hQpos : 0 < Nat.card Q := Nat.card_pos
  have hprod : Q.relIndex (κ ⊔ Z0) = Q.relIndex κ * Q.relIndex Z0 := by
    rw [← hc1, ← hc2, ← hc3] at hmulcard
    have h5 : Q.relIndex (κ ⊔ Z0) * Nat.card Q * Nat.card Q =
        Q.relIndex κ * Q.relIndex Z0 * Nat.card Q * Nat.card Q := by
      rw [hmulcard]
      ring
    exact Nat.eq_of_mul_eq_mul_right hQpos (Nat.eq_of_mul_eq_mul_right hQpos h5)
  have hn3 : 3 ≤ n := hs5.n_gt
  have hrelE : Q.relIndex E = Nat.card Z ^ (n - 2) := by
    have h1' := Subgroup.relIndex_mul_relIndex Q E (LB M Q B) hQE inf_le_left
    rw [relIndex_Ebar_eq h34 h311a hc hs hsplit, relIndex_Q_LB h34 hc hs5] at h1'
    have hpow : Nat.card Z ^ (n - 1) = Nat.card Z ^ (n - 2) * Nat.card Z := by
      rw [← pow_succ]
      congr 1
      omega
    exact Nat.eq_of_mul_eq_mul_right Nat.card_pos (by rw [h1', hpow])
  have hκge := relIndex_kappa_ge h34 hc hs hsplit h4 h2 hh (relIndex_normalizer_LB_le hc hh hFB)
  have hZ0rel : Q.relIndex Z0 = Nat.card Z := hcen.2.1
  have hcge : Q.relIndex E ≤ Q.relIndex (κ ⊔ Z0) := by
    rw [hprod, hZ0rel, hrelE]
    calc Nat.card Z ^ (n - 2) = Nat.card Z ^ (n - 3) * Nat.card Z := by
          rw [← pow_succ]
          congr 1
          omega
      _ ≤ Q.relIndex κ * Nat.card Z := Nat.mul_le_mul_right _ hκge
  have hsupE : κ ⊔ Z0 ≤ E := sup_le inf_le_left hZ0E
  have hrel1 : (κ ⊔ Z0).relIndex E = 1 := by
    have hm := Subgroup.relIndex_mul_relIndex Q (κ ⊔ Z0) E hsupQ hsupE
    have hpos : 0 < (κ ⊔ Z0).relIndex E := relIndex_pos' _ _
    have hEpos : 0 < Q.relIndex E := relIndex_pos' _ _
    have h6 : Q.relIndex (κ ⊔ Z0) * (κ ⊔ Z0).relIndex E ≤ Q.relIndex (κ ⊔ Z0) * 1 := by
      rw [mul_one, hm]
      exact hcge
    have h7 := Nat.le_of_mul_le_mul_left h6 (lt_of_lt_of_le hEpos hcge)
    omega
  have hEle : E ≤ κ ⊔ Z0 := Subgroup.relIndex_eq_one.mp hrel1
  have hset : ((κ ⊔ Z0 : Subgroup G) : Set G) = (κ : Set G) * (Z0 : Set G) :=
    Subgroup.coe_mul_of_right_le_normalizer_left κ Z0 hZ0N
  have hxmem : g₀ * s₀ * g₀⁻¹ ∈ ((κ ⊔ Z0 : Subgroup G) : Set G) := hEle ⟨hxT.1, hNX hxT.2⟩
  rw [hset] at hxmem
  obtain ⟨k, hk, z, hz, hkz⟩ := hxmem
  have hxM : g₀ * s₀ * g₀⁻¹ ∈ M := hLM hxT.1
  obtain ⟨y, hyN, hyc⟩ := hcoset _ hxT hxZ ⟨s₀, hs₀, hxM, g₀, hg₀, by
    rw [show g₀ * s₀ * g₀⁻¹ * (g₀ * s₀ * g₀⁻¹)⁻¹ = 1 by group]
    exact Q.one_mem⟩ z hz
  have hyM : y ∈ M := hc.Rt_le_M t (hNR hyN)
  have hzM : z ∈ M := hLM (hZ0L hz)
  have hkL : k ∈ LB M Q B := hk.1.1
  have hzL : z ∈ LB M Q B := hZ0L hz
  have hq₂ : z⁻¹ * (⁅g₀ * s₀ * g₀⁻¹, y⁆ * z⁻¹)⁻¹ * z ∈ Q := by
    have := (Subgroup.mem_normalizer_iff.mp (hQn (M.inv_mem hzM)) _).mp (Q.inv_mem hyc)
    simpa using this
  have hq₃ : ⁅k⁻¹, z⁻¹⁆ ∈ Q := hc.commutator_LB_le_Q
    (Subgroup.commutator_mem_commutator ((LB M Q B).inv_mem hkL) ((LB M Q B).inv_mem hzL))
  have he : y * (g₀ * s₀ * g₀⁻¹) * y⁻¹ =
      (z⁻¹ * (⁅g₀ * s₀ * g₀⁻¹, y⁆ * z⁻¹)⁻¹ * z) * k * ⁅k⁻¹, z⁻¹⁆ := by
    rw [← hkz]
    simp only [commutatorElement_def]
    group
  have heκ : y * (g₀ * s₀ * g₀⁻¹) * y⁻¹ ∈ κ := by
    rw [he]
    exact κ.mul_mem (κ.mul_mem (hQκ hq₂) hk) (hQκ hq₃)
  have heQ : y * (g₀ * s₀ * g₀⁻¹) * y⁻¹ ∉ Q := by
    intro hQe
    apply hxZ
    have := (Subgroup.mem_normalizer_iff.mp (hQn (M.inv_mem hyM)) _).mp hQe
    apply hQZ0
    simpa [mul_assoc] using this
  refine ⟨s₀, hs₀, hs₀Q, y * g₀, M.mul_mem hyM hg₀, y * (g₀ * s₀ * g₀⁻¹) * y⁻¹, heκ.1, heQ,
    heκ.2, ?_⟩
  rw [show y * (g₀ * s₀ * g₀⁻¹) * y⁻¹ * (y * g₀ * s₀ * (y * g₀)⁻¹)⁻¹ = 1 by group]
  exact Q.one_mem

end HS9

theorem core4_of_coset (h34 : Stroth34Statement) (h311a : Stroth311aStatement)
    (h311bComm : Stroth311bCommStatement) (h312b : Stroth312bStatement)
    (hA : Sec9AExistsStatement) (hn5 : Sec9NGeFiveStatement) (hS4 : Sec4Statement)
    (hCentre : Step95CentreStatement) (hG : Sec97CosetStatement) :
    Sec97FourCore94Statement := by
  intro G _ _ M Q Z B hc n t hs X Y hsplit h4 h1 h2 h3 Z0 hZ0 hbad h hh hFB hhard hline hTI
  have hcen := hCentre G M Q Z B hc n t hs Z0 hZ0
  have hcoset := hG G M Q Z B hc n t hs X Y hsplit Z0 hZ0
  have hex := HS9.exists_mem_E_not_Q h34 hc hs hsplit h4
  obtain ⟨s, hsZ0, hsQ, g, hg, e, heE, heQ, heN, hq⟩ :=
    HS9.exists_a2_in_kappa h34 h311a hc hs hsplit h4 h2 hZ0 hcen hh hFB hbad hcoset
  have hsM : s ∈ M := hc.LB_le_M (hcen.1 hsZ0).1
  obtain ⟨r, hr⟩ := hA G M Q Z B hc n t hs
  have hR : Rt M (LB M Q B) s = Rt M (LB M Q B) t :=
    HS9.Rt_eq_of_mem_Z091 h34 h311a h311bComm h312b hs hr hZ0 hsZ0 hsQ
  have hsE : s ∈ LB M Q B ⊓ X := ⟨(hcen.1 hsZ0).1,
    (sec97Head_of h34 h311a G M Q Z B hc n t hs X Y hsplit).1 (hcen.1 hsZ0).2⟩
  have hss : Sec9Hyp hc n s := HS9.sec9Hyp_of_card_le h34 hc hs hsplit h1 hsE hsQ (by rw [hR])
  have hV := HS9.Vt_eq_of_centre_mem h34 hc hs hcen hsZ0 hsQ hss
  obtain ⟨X₁, hsplit₁, hse, hEX⟩ :=
    HS9.exists_frame_of_conjMod h34 hS4 hc hs hsplit h4 h1 hg hsM hR hV heE heQ hq
  have h4₁ := hS4 G M Q Z B hc n e hse X₁ Y hsplit₁
  have h1₁ : HS9.OneConcl hc X₁ Y := by
    unfold HS9.OneConcl at h1 ⊢
    rw [hEX]
    exact h1
  have h2₁ : HS9.TwoConcl M Q B X₁ := by
    unfold HS9.TwoConcl at h2 ⊢
    rw [hEX]
    exact h2
  have hhard₁ : ∀ x ∈ LB M Q B ⊓ X₁, x ∉ Q →
      h * x * h⁻¹ ∉ LB M Q B ∧ x ∉ conjSubgroup h (LB M Q B) := by
    rw [hEX]
    exact hhard
  have hHK : ∀ k ∈ conjSubgroup h (LB M Q B ⊓ X₁) ⊓
      Subgroup.normalizer ((LB M Q B ⊓ X₁ : Subgroup G) : Set G),
      conjSubgroup k (LB M Q B ⊓ hc.CN e) = LB M Q B ⊓ hc.CN e := by
    rw [hEX]
    exact HS9.normalizes_CN_of_mem_kappa hc hh hFB hex (fun x hx hxQ => (hhard x hx hxQ).2) heE heN
  exact HS9.hard_false_of_normalizes_inf_CN h34 h311a hn5 hc hse hsplit₁ h4₁ h1₁ h2₁ hh hFB
    hhard₁ hHK

end CFSG.RankThree.GF2n.Stroth80
