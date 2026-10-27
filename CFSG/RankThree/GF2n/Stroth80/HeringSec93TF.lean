module

public import CFSG.RankThree.GF2n.Stroth80.HeringSec93TA
public import CFSG.RankThree.GF2n.Stroth80.HeringSec93TGrp
public import CFSG.RankThree.GF2n.Smith81.OrthE1B2
public import CFSG.RankThree.GF2n.Stroth80.HeringSec93FPGrp

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n.Smith81
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

namespace HS9

abbrev Xhat (M Q B : Subgroup G) (h : G) : Subgroup G :=
  LB M Q B ⊔ conjSubgroup h (LB M Q B)

abbrev Fhat (M Q B : Subgroup G) (h : G) : Subgroup G :=
  inSubgroup (pCore 2) (Xhat M Q B h)

theorem card_Z_facts (hc : Ctx M Q Z B) : (∃ e : ℕ, Nat.card Z = 2 ^ e) ∧ 4 ≤ Nat.card Z := by
  obtain ⟨e, -, he, -⟩ := hc.hyp.cp
  exact ⟨⟨e, he⟩, hc.hyp.q4⟩

theorem odd_sq_sub_one_of_two_pow {q : ℕ} (hq : ∃ e : ℕ, q = 2 ^ e) (h4 : 4 ≤ q) :
    Odd (q ^ 2 - 1) := by
  have h2 : 2 ∣ q := by
    obtain ⟨e, rfl⟩ := hq
    have he : e ≠ 0 := by
      rintro rfl
      simp at h4
    exact dvd_pow_self 2 he
  obtain ⟨c, rfl⟩ := h2
  have hc1 : 1 ≤ c := by omega
  have e : (2 * c) ^ 2 = 4 * (c * c) := by ring
  rw [e]
  have ht : 1 ≤ c * c := Nat.mul_pos hc1 hc1
  generalize c * c = u at ht
  exact ⟨2 * u - 1, by omega⟩

theorem pCoreIn_conj_LB_eq (h34 : Stroth34Statement) {hc : Ctx M Q Z B} {n : ℕ} {t : G}
    (hs : Sec5Hyp hc n t) {h : G} (hh : h ∈ M) {f : G} (hf : f ∈ Fhat M Q B h) :
    conjSubgroup f (LB M Q B) = LB M Q B ∧
      conjSubgroup f (conjSubgroup h (LB M Q B)) = conjSubgroup h (LB M Q B) := by
  have hc' : Ctx M Q Z (conjSubgroup h B) := hc.conj_of_mem hh
  have hLconj : LB M Q (conjSubgroup h B) = conjSubgroup h (LB M Q B) := hc.LB_conj hh
  have hLH : LB M Q B ≤ H0 M Z := hc.LB_le_H0
  have hL'H : conjSubgroup h (LB M Q B) ≤ H0 M Z := hLconj ▸ hc'.LB_le_H0
  have hXH : Xhat M Q B h ≤ H0 M Z := sup_le hLH hL'H
  have hfM : f ∈ M := (hXH (pCoreIn_le _ hf)).1
  have h1 := comm_mem_Z_of_pCoreIn h34 hc hs.width hs.n_gt hs.noA2 hs.gen
    (le_sup_left : LB M Q B ≤ Xhat M Q B h) hXH
  have h2 := comm_mem_Z_of_pCoreIn h34 hc' hs.width hs.n_gt (hc.noA2_conj hs.noA2 hh)
    (hs.gen.conj_of_mem hh) (hLconj ▸ le_sup_right : LB M Q (conjSubgroup h B) ≤ Xhat M Q B h) hXH
  refine ⟨conj_LB_eq_of_forall_comm_mem_Z hc hfM (h1 f hf), ?_⟩
  have := conj_LB_eq_of_forall_comm_mem_Z hc' hfM (h2 f hf)
  rwa [hLconj] at this

theorem card_Xhat (hc : Ctx M Q Z B) {h : G}
    (hq : QuotSat (Xhat M Q B h) (Fhat M Q B h) (IsSLModel 2 (Nat.card Z))) :
    Nat.card ↥(Xhat M Q B h) =
      Nat.card ↥(Fhat M Q B h) * (Nat.card Z * (Nat.card Z ^ 2 - 1)) := by
  obtain ⟨⟨e, he⟩, h4⟩ := card_Z_facts hc
  exact Smith81.Smith23E1.b2_sl_card (pCoreIn_le _) hq he h4

theorem isPGroup_LB_sup_pCoreIn (hc : Ctx M Q Z B) {X : Subgroup G} (hLX : LB M Q B ≤ X) :
    IsPGroup 2 ↥(LB M Q B ⊔ inSubgroup (pCore 2) X) := by
  have hLn : LB M Q B ≤ Subgroup.normalizer (inSubgroup (pCore 2) X : Set G) :=
    hLX.trans (le_normalizer_pCoreIn X)
  have := IsPGroup.to_sup_of_normal_left' (isPGroup_pCoreIn X) (isPGroup_LB_of_ctx hc) hLn
  rwa [sup_comm] at this

theorem card_LB_sup_Fhat_dvd (hc : Ctx M Q Z B) {h : G}
    (hq : QuotSat (Xhat M Q B h) (Fhat M Q B h) (IsSLModel 2 (Nat.card Z))) :
    Nat.card ↥(LB M Q B ⊔ Fhat M Q B h) ∣ Nat.card ↥(Fhat M Q B h) * Nat.card Z := by
  obtain ⟨hqe, h4⟩ := card_Z_facts hc
  exact card_dvd_of_isPGroup_of_odd (X := Xhat M Q B h) (F := Fhat M Q B h)
    (sup_le le_sup_left (pCoreIn_le _)) (isPGroup_LB_sup_pCoreIn hc le_sup_left)
    (isPGroup_pCoreIn _) hqe (odd_sq_sub_one_of_two_pow hqe h4) (card_Xhat hc hq)

theorem relIndex_Fhat_le (hc : Ctx M Q Z B) {h : G}
    (hq : QuotSat (Xhat M Q B h) (Fhat M Q B h) (IsSLModel 2 (Nat.card Z))) :
    (Fhat M Q B h).relIndex (LB M Q B) ≤ Nat.card Z := by
  have hLn : LB M Q B ≤ Subgroup.normalizer (Fhat M Q B h : Set G) :=
    (le_sup_left : LB M Q B ≤ Xhat M Q B h).trans (le_normalizer_pCoreIn _)
  have h1 := relIndex_mul_card_eq_card_sup hLn
  have h2 := card_LB_sup_Fhat_dvd hc hq
  rw [← h1] at h2
  have hpos : 0 < Nat.card ↥(Fhat M Q B h) := Nat.card_pos
  have h3 : (Fhat M Q B h).relIndex (LB M Q B) * Nat.card ↥(Fhat M Q B h) ≤
      Nat.card ↥(Fhat M Q B h) * Nat.card Z :=
    Nat.le_of_dvd (Nat.mul_pos hpos Nat.card_pos) h2
  nlinarith

theorem exists_conj_LB_eq (h34 : Stroth34Statement) {hc : Ctx M Q Z B} {n : ℕ} {t : G}
    (hs : Sec5Hyp hc n t) {h : G} (hh : h ∈ M)
    (hq : QuotSat (Xhat M Q B h) (Fhat M Q B h) (IsSLModel 2 (Nat.card Z)))
    (hsyl : Nat.card ↥(LB M Q B ⊔ Fhat M Q B h) = Nat.card ↥(Fhat M Q B h) * Nat.card Z) :
    ∃ g ∈ Xhat M Q B h, conjSubgroup h (LB M Q B) = conjSubgroup g (LB M Q B) := by
  classical
  obtain ⟨hqe, h4⟩ := card_Z_facts hc
  have hodd := odd_sq_sub_one_of_two_pow hqe h4
  have hc' : Ctx M Q Z (conjSubgroup h B) := hc.conj_of_mem hh
  have hLconj : LB M Q (conjSubgroup h B) = conjSubgroup h (LB M Q B) := hc.LB_conj hh
  have hLH : LB M Q B ≤ H0 M Z := hc.LB_le_H0
  have hL'H : conjSubgroup h (LB M Q B) ≤ H0 M Z := hLconj ▸ hc'.LB_le_H0
  have hXH : Xhat M Q B h ≤ H0 M Z := sup_le hLH hL'H
  have hXM : Xhat M Q B h ≤ M := fun x hx => (hXH hx).1
  have hLX : LB M Q B ≤ Xhat M Q B h := le_sup_left
  have hL'X : conjSubgroup h (LB M Q B) ≤ Xhat M Q B h := le_sup_right
  have hFX : Fhat M Q B h ≤ Xhat M Q B h := pCoreIn_le _
  have hFn : Xhat M Q B h ≤ Subgroup.normalizer (Fhat M Q B h : Set G) :=
    le_normalizer_pCoreIn _
  have hP2 : IsPGroup 2 ↥(LB M Q B ⊔ Fhat M Q B h) := isPGroup_LB_sup_pCoreIn hc hLX
  have hP'2 : IsPGroup 2 ↥(conjSubgroup h (LB M Q B) ⊔ Fhat M Q B h) := by
    have := isPGroup_LB_sup_pCoreIn hc' (X := Xhat M Q B h) (hLconj ▸ hL'X)
    rwa [hLconj] at this
  have hcard : Nat.card ↥(Xhat M Q B h) =
      Nat.card ↥(LB M Q B ⊔ Fhat M Q B h) * (Nat.card Z ^ 2 - 1) := by
    rw [card_Xhat hc hq, hsyl]
    ring
  obtain ⟨g, hgX, hg⟩ := exists_conj_mem_of_odd_index (sup_le hLX hFX) (sup_le hL'X hFX) hP2 hP'2
    hodd hcard
  have hgM : g ∈ M := hXM hgX
  have hcg : Ctx M Q Z (conjSubgroup g B) := hc.conj_of_mem hgM
  have hLg : LB M Q (conjSubgroup g B) = conjSubgroup g (LB M Q B) := hc.LB_conj hgM
  have hFg : ∀ f ∈ Fhat M Q B h, f ∈ Subgroup.normalizer
      (conjSubgroup g (LB M Q B) : Set G) := by
    intro f hf
    have hf' : g⁻¹ * f * g ∈ Fhat M Q B h := by
      have := (Subgroup.mem_normalizer_iff.mp (hFn ((Xhat M Q B h).inv_mem hgX)) f).mp hf
      simpa using this
    have h1 := (pCoreIn_conj_LB_eq h34 hs hh hf').1
    apply conjSubgroup_eq_self_iff.mp
    calc conjSubgroup f (conjSubgroup g (LB M Q B))
        = conjSubgroup g (conjSubgroup (g⁻¹ * f * g) (LB M Q B)) := by
          rw [← conjSubgroup_mul, ← conjSubgroup_mul]
          congr 1
          group
      _ = conjSubgroup g (LB M Q B) := by rw [h1]
  have hL'N : conjSubgroup h (LB M Q B) ≤
      Subgroup.normalizer (LB M Q (conjSubgroup g B) : Set G) := by
    rw [hLg]
    intro x hx
    have hx1 : g⁻¹ * x * g ∈ LB M Q B ⊔ Fhat M Q B h := hg x (Subgroup.mem_sup_left hx)
    have hLFn : LB M Q B ≤ Subgroup.normalizer (Fhat M Q B h : Set G) := hLX.trans hFn
    rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right _ _ hLFn] at hx1
    obtain ⟨l, hl, f, hf, hlf⟩ := hx1
    have e : x = (g * l * g⁻¹) * (g * f * g⁻¹) := by
      have : x = g * (g⁻¹ * x * g) * g⁻¹ := by group
      rw [this, ← hlf]
      group
    have h1 : g * l * g⁻¹ ∈ Subgroup.normalizer (conjSubgroup g (LB M Q B) : Set G) :=
      Subgroup.le_normalizer (mem_conjSubgroup.mpr (by simpa [mul_assoc] using hl))
    have h2 : g * f * g⁻¹ ∈ Subgroup.normalizer (conjSubgroup g (LB M Q B) : Set G) :=
      hFg _ ((Subgroup.mem_normalizer_iff.mp (hFn hgX) f).mp hf)
    rw [e]
    exact Subgroup.mul_mem _ h1 h2
  have he : conjSubgroup (h * g⁻¹) (LB M Q (conjSubgroup g B)) =
      conjSubgroup h (LB M Q B) := by
    rw [hLg, ← conjSubgroup_mul, inv_mul_cancel_right]
  have hwc := (stroth_3_5 h34 hcg hs.width hs.n_gt (hc.noA2_conj hs.noA2 hgM)
    (hs.gen.conj_of_mem hgM)).1 (h * g⁻¹) (M.mul_mem hh (M.inv_mem hgM)) (he ▸ hL'N)
  rw [he, hLg] at hwc
  exact ⟨g, hgX, hwc⟩

theorem inf_Fhat_le_conj (h34 : Stroth34Statement) {hc : Ctx M Q Z B} {n : ℕ} {t : G}
    (hs : Sec5Hyp hc n t) {h : G} (hh : h ∈ M)
    (hq : QuotSat (Xhat M Q B h) (Fhat M Q B h) (IsSLModel 2 (Nat.card Z)))
    (hsyl : Nat.card ↥(LB M Q B ⊔ Fhat M Q B h) = Nat.card ↥(Fhat M Q B h) * Nat.card Z)
    {Y : Subgroup G} (hYL : Y ≤ LB M Q B) (hLY : LB M Q B ≤ Y ⊔ Fhat M Q B h)
    (hYF : ∀ y ∈ Y, ∀ f ∈ Fhat M Q B h, ⁅f, y⁆ ∈ Q) :
    LB M Q B ⊓ Fhat M Q B h ≤ conjSubgroup h (LB M Q B) := by
  classical
  obtain ⟨g, hgX, hgL⟩ := exists_conj_LB_eq h34 hs hh hq hsyl
  have hc' : Ctx M Q Z (conjSubgroup h B) := hc.conj_of_mem hh
  have hLconj : LB M Q (conjSubgroup h B) = conjSubgroup h (LB M Q B) := hc.LB_conj hh
  have hLH : LB M Q B ≤ H0 M Z := hc.LB_le_H0
  have hL'H : conjSubgroup h (LB M Q B) ≤ H0 M Z := hLconj ▸ hc'.LB_le_H0
  have hXH : Xhat M Q B h ≤ H0 M Z := sup_le hLH hL'H
  have hXM : Xhat M Q B h ≤ M := fun x hx => (hXH hx).1
  have hLX : LB M Q B ≤ Xhat M Q B h := le_sup_left
  have hFn : Xhat M Q B h ≤ Subgroup.normalizer (Fhat M Q B h : Set G) :=
    le_normalizer_pCoreIn _
  have hgM : g ∈ M := hXM hgX
  have hQM : ∀ x ∈ M, ∀ y ∈ Q, x * y * x⁻¹ ∈ Q := fun x hx y hy =>
    (Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 hx) y).mp hy
  let C : Subgroup G :=
    { carrier := {x | x ∈ Xhat M Q B h ∧ ∀ f ∈ Fhat M Q B h, ⁅f, x⁆ ∈ Q}
      mul_mem' := by
        rintro a b ⟨haX, ha⟩ ⟨hbX, hb⟩
        refine ⟨(Xhat M Q B h).mul_mem haX hbX, fun f hf => ?_⟩
        have e : ⁅f, a * b⁆ = ⁅f, a⁆ * (a * ⁅f, b⁆ * a⁻¹) := by
          simp only [commutatorElement_def]
          group
        rw [e]
        exact Q.mul_mem (ha f hf) (hQM a (hXM haX) _ (hb f hf))
      one_mem' := ⟨(Xhat M Q B h).one_mem, fun f _ => by simp [commutatorElement_def]⟩
      inv_mem' := by
        rintro a ⟨haX, ha⟩
        refine ⟨(Xhat M Q B h).inv_mem haX, fun f hf => ?_⟩
        have e : ⁅f, a⁻¹⁆ = a⁻¹ * ⁅f, a⁆⁻¹ * a := by
          simp only [commutatorElement_def]
          group
        rw [e]
        have := hQM a⁻¹ (M.inv_mem (hXM haX)) _ (Q.inv_mem (ha f hf))
        simpa using this }
  have hYC : Y ≤ C := fun y hy => ⟨hLX (hYL hy), hYF y hy⟩
  have hFg : conjSubgroup g (Fhat M Q B h) = Fhat M Q B h :=
    conjSubgroup_eq_self_iff.mpr (hFn hgX)
  have hgYC : conjSubgroup g Y ≤ C := by
    intro w hw
    rw [mem_conjSubgroup] at hw
    refine ⟨?_, fun f hf => ?_⟩
    · have := (Xhat M Q B h).mul_mem ((Xhat M Q B h).mul_mem hgX (hLX (hYL hw)))
        ((Xhat M Q B h).inv_mem hgX)
      simpa [mul_assoc] using this
    · have hf' : g⁻¹ * f * g ∈ Fhat M Q B h := by
        have := (Subgroup.mem_normalizer_iff.mp (hFn ((Xhat M Q B h).inv_mem hgX)) f).mp hf
        simpa using this
      have e : ⁅f, w⁆ = g * ⁅g⁻¹ * f * g, g⁻¹ * w * g⁆ * g⁻¹ := by
        simp only [commutatorElement_def]
        group
      rw [e]
      exact hQM g hgM _ (hYF _ hw _ hf')
  have hL1 : LB M Q B ≤ C ⊔ Fhat M Q B h := hLY.trans (sup_le_sup_right hYC _)
  have hL2 : conjSubgroup g (LB M Q B) ≤ C ⊔ Fhat M Q B h := by
    calc conjSubgroup g (LB M Q B) ≤ conjSubgroup g (Y ⊔ Fhat M Q B h) :=
          Subgroup.map_mono hLY
      _ = conjSubgroup g Y ⊔ conjSubgroup g (Fhat M Q B h) := Subgroup.map_sup _ _ _
      _ ≤ C ⊔ Fhat M Q B h := by rw [hFg]; exact sup_le_sup_right hgYC _
  have hXCF : Xhat M Q B h ≤ C ⊔ Fhat M Q B h := sup_le hL1 (hgL ▸ hL2)
  have hCn : C ≤ Subgroup.normalizer (Fhat M Q B h : Set G) := fun c hc' => hFn hc'.1
  have hg' : g ∈ C ⊔ Fhat M Q B h := hXCF hgX
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right _ _ hCn] at hg'
  obtain ⟨c, hcC, f, hfF, rfl⟩ := hg'
  have hLc : conjSubgroup h (LB M Q B) = conjSubgroup c (LB M Q B) := by
    rw [hgL, conjSubgroup_mul, (pCoreIn_conj_LB_eq h34 hs hh hfF).1]
  have hQL' : Q ≤ conjSubgroup h (LB M Q B) :=
    calc Q = conjSubgroup h Q := (hc.conj_Q_eq hh).symm
      _ ≤ conjSubgroup h (LB M Q B) := Subgroup.map_mono sec39_Q_le_LB
  rintro φ ⟨hφL, hφF⟩
  have h1 : c * φ * c⁻¹ ∈ conjSubgroup h (LB M Q B) := by
    rw [hLc, mem_conjSubgroup]
    simpa [mul_assoc] using hφL
  have h2 : ⁅φ, c⁆ ∈ Q := hcC.2 φ hφF
  have e : φ = ⁅φ, c⁆ * (c * φ * c⁻¹) := by
    simp only [commutatorElement_def]
    group
  rw [e]
  exact (conjSubgroup h (LB M Q B)).mul_mem (hQL' h2) h1

theorem comm_Fhat_Z0_le_Q (h34 : Stroth34Statement) {hc : Ctx M Q Z B} {n : ℕ} {t : G}
    (hs : Sec5Hyp hc n t) {h : G} (hh : h ∈ M) {Z0 : Subgroup G} (hZ0L : Z0 ≤ LB M Q B)
    (hsc : StronglyClosedMod M Z0 (LB M Q B)) (hcase : Z0 ⊓ Fhat M Q B h ≤ Q) :
    ∀ y ∈ Z0, ∀ f ∈ Fhat M Q B h, ⁅f, y⁆ ∈ Q := by
  intro y hy f hf
  have hc' : Ctx M Q Z (conjSubgroup h B) := hc.conj_of_mem hh
  have hLconj : LB M Q (conjSubgroup h B) = conjSubgroup h (LB M Q B) := hc.LB_conj hh
  have hXH : Xhat M Q B h ≤ H0 M Z :=
    sup_le hc.LB_le_H0 (hLconj ▸ hc'.LB_le_H0)
  have hfM : f ∈ M := (hXH (pCoreIn_le _ hf)).1
  have hFn : Xhat M Q B h ≤ Subgroup.normalizer (Fhat M Q B h : Set G) :=
    le_normalizer_pCoreIn _
  have hfL : conjSubgroup f (LB M Q B) = LB M Q B := (pCoreIn_conj_LB_eq h34 hs hh hf).1
  have hyL : y ∈ LB M Q B := hZ0L hy
  have hfy : f * y * f⁻¹ ∈ LB M Q B := by
    have : f * y * f⁻¹ ∈ conjSubgroup f (LB M Q B) := by
      rw [mem_conjSubgroup]
      simpa [mul_assoc] using hyL
    rwa [hfL] at this
  have h1 : f * y * f⁻¹ ∈ Z0 := hsc y hy f hfM hfy
  have h2 : ⁅f, y⁆ ∈ Z0 := by
    have e : ⁅f, y⁆ = (f * y * f⁻¹) * y⁻¹ := by
      rw [commutatorElement_def]
    rw [e]
    exact Z0.mul_mem h1 (Z0.inv_mem hy)
  have h3 : ⁅f, y⁆ ∈ Fhat M Q B h := by
    have e : ⁅f, y⁆ = f * (y * f⁻¹ * y⁻¹) := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact (Fhat M Q B h).mul_mem hf
      ((Subgroup.mem_normalizer_iff.mp (hFn ((le_sup_left : LB M Q B ≤ Xhat M Q B h) hyL)) f⁻¹).mp
        ((Fhat M Q B h).inv_mem hf))
  exact hcase ⟨h2, h3⟩

theorem sup_Fhat_eq_of_inf_le (hc : Ctx M Q Z B) {h : G} (hh : h ∈ M) {Z0 : Subgroup G}
    (hZ0L : Z0 ≤ LB M Q B) (hQZ0 : Q ≤ Z0) (hcard : Q.relIndex Z0 = Nat.card Z)
    (hcase : Z0 ⊓ Fhat M Q B h ≤ Q)
    (hq : QuotSat (Xhat M Q B h) (Fhat M Q B h) (IsSLModel 2 (Nat.card Z))) :
    Z0 ⊔ Fhat M Q B h = LB M Q B ⊔ Fhat M Q B h ∧
      Nat.card ↥(LB M Q B ⊔ Fhat M Q B h) = Nat.card ↥(Fhat M Q B h) * Nat.card Z := by
  have hc' : Ctx M Q Z (conjSubgroup h B) := hc.conj_of_mem hh
  have hLconj : LB M Q (conjSubgroup h B) = conjSubgroup h (LB M Q B) := hc.LB_conj hh
  have hXH : Xhat M Q B h ≤ H0 M Z :=
    sup_le hc.LB_le_H0 (hLconj ▸ hc'.LB_le_H0)
  have hXM : Xhat M Q B h ≤ M := fun x hx => (hXH hx).1
  have hLX : LB M Q B ≤ Xhat M Q B h := le_sup_left
  have hFn : Xhat M Q B h ≤ Subgroup.normalizer (Fhat M Q B h : Set G) :=
    le_normalizer_pCoreIn _
  have hQF : Q ≤ Fhat M Q B h := Q_le_pCoreIn hc (sec39_Q_le_LB.trans hLX) hXM
  have hZF : Z0 ⊓ Fhat M Q B h = Q := le_antisymm hcase (le_inf hQZ0 hQF)
  have h1 := card_sup_mul_card_inf_of_le_normalizer (A := Z0) (F := Fhat M Q B h)
    (hZ0L.trans (hLX.trans hFn))
  rw [hZF] at h1
  have h2 : Q.relIndex Z0 * Nat.card ↥(Q ⊓ Z0) = Nat.card ↥Z0 := Subgroup.relIndex_mul_card Q Z0
  rw [inf_eq_left.mpr hQZ0, hcard] at h2
  have hQpos : 0 < Nat.card ↥Q := Nat.card_pos
  have h3 : Nat.card ↥(Z0 ⊔ Fhat M Q B h) = Nat.card ↥(Fhat M Q B h) * Nat.card Z := by
    have : Nat.card ↥(Z0 ⊔ Fhat M Q B h) * Nat.card ↥Q =
        (Nat.card ↥(Fhat M Q B h) * Nat.card Z) * Nat.card ↥Q := by
      rw [h1, ← h2]
      ring
    exact Nat.eq_of_mul_eq_mul_right hQpos this
  have hle : Z0 ⊔ Fhat M Q B h ≤ LB M Q B ⊔ Fhat M Q B h := sup_le_sup_right hZ0L _
  have hdvd := card_LB_sup_Fhat_dvd hc hq
  have hge : Nat.card ↥(LB M Q B ⊔ Fhat M Q B h) ≤ Nat.card ↥(Z0 ⊔ Fhat M Q B h) := by
    rw [h3]
    exact Nat.le_of_dvd (Nat.mul_pos Nat.card_pos Nat.card_pos) hdvd
  have heq : Z0 ⊔ Fhat M Q B h = LB M Q B ⊔ Fhat M Q B h :=
    Subgroup.eq_of_le_of_card_ge hle hge
  exact ⟨heq, by rw [← heq, h3]⟩

theorem inf_Fhat_le_conj_of_Z0 (h34 : Stroth34Statement) {hc : Ctx M Q Z B} {n : ℕ} {t : G}
    (hs : Sec5Hyp hc n t) {h : G} (hh : h ∈ M) {Z0 : Subgroup G} (hZ0L : Z0 ≤ LB M Q B)
    (hQZ0 : Q ≤ Z0) (hcard : Q.relIndex Z0 = Nat.card Z)
    (hsc : StronglyClosedMod M Z0 (LB M Q B)) (hcase : Z0 ⊓ Fhat M Q B h ≤ Q)
    (hq : QuotSat (Xhat M Q B h) (Fhat M Q B h) (IsSLModel 2 (Nat.card Z))) :
    LB M Q B ⊓ Fhat M Q B h ≤ LB M Q B ⊓ conjSubgroup h (LB M Q B) := by
  obtain ⟨heq, hsyl⟩ := sup_Fhat_eq_of_inf_le hc hh hZ0L hQZ0 hcard hcase hq
  refine le_inf inf_le_left (inf_Fhat_le_conj h34 hs hh hq hsyl hZ0L ?_
    (comm_Fhat_Z0_le_Q h34 hs hh hZ0L hsc hcase))
  exact le_sup_left.trans heq.ge

end HS9

end CFSG.RankThree.GF2n.Stroth80
