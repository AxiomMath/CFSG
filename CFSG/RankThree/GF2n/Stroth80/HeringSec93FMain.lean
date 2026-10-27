module

public import CFSG.RankThree.GF2n.Stroth80.HeringSec93FPGrp
public import CFSG.RankThree.GF2n.Stroth80.HeringSec93FHP
public import CFSG.RankThree.GF2n.Stroth80.HeringSec93One
public import CFSG.RankThree.GF2n.Stroth80.HeringSec91CentreX
public import CFSG.RankThree.GF2n.Stroth80.Sec715CentProof
public import CFSG.RankThree.GF2n.Stroth80.Sec123Order
public import CFSG.RankThree.GF2n.Stroth80.HeringSec93XH

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n.Smith81
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

namespace HS9

theorem conjB_le_Wt (h34 : Stroth34Statement) {hc : Ctx M Q Z B} {n : ℕ} {t : G}
    (hs : Sec9Hyp hc n t) {B' F : Subgroup G} (hB'Q : B' ≤ Q) (htF : t ∈ F)
    (hFB' : ∀ f ∈ F, ∀ b ∈ B', ⁅f, b⁆ ∈ Z) :
    B' ≤ Wt Q (Vt M (LB M Q B) B Z t) := by
  have hs5 := hs.toSec5
  have h35 := (stroth_3_5 h34 hc hs5.width hs5.n_gt hs5.noA2 hs5.gen).2.1
  obtain ⟨-, hW⟩ := hc.Vt_eq_Ut_and_Wt_eq_Q1_of_not_le_QB h35 hs5.mem hs5.notQ
    (sec9_notQB h34 hs)
  rw [hW]
  intro b hb
  exact ⟨hB'Q hb, fun s hs' => hFB' s (Subgroup.zpowers_le.mpr htF hs') b hb⟩

theorem comm_LB_conjB_mem_Vt (h34 : Stroth34Statement) {hc : Ctx M Q Z B} {n : ℕ} {t : G}
    (hs : Sec9Hyp hc n t) {B' F : Subgroup G} (hB'Q : B' ≤ Q)
    (hB'c : ∀ b ∈ B', ∀ y ∈ B, b * y = y * b) (hFB' : ∀ f ∈ F, ∀ b ∈ B', ⁅f, b⁆ ∈ Z)
    (hFN : LB M Q B ⊓ hc.CN t ≤ F) :
    ∀ x ∈ LB M Q B, ∀ b ∈ B', ⁅x, b⁆ ∈ Vt M (LB M Q B) B Z t := by
  intro x hx b hb
  have hbQ : b ∈ Q := hB'Q hb
  have hbc : b ∈ Subgroup.centralizer (B : Set G) :=
    Subgroup.mem_centralizer_iff.mpr fun y hy => (hB'c b hb y hy).symm
  have hxM : x ∈ M := hc.LB_le_M hx
  have hd : ⁅b, x⁆ ∈ Q ⊓ QB B := by
    have h1 := hc.comm_LB_mem_inf hx hbQ hbc
    rw [← commutatorElement_inv]
    exact (Q ⊓ QB B).inv_mem h1
  have hV : ⁅b, x⁆ ∈ Vt M (LB M Q B) B Z t := by
    refine centLam91 h34 hs _ hd fun l hl => ?_
    have hlL : l ∈ LB M Q B := le_sup_right (a := Q) ⟨hl.1.1, hl.1.2⟩
    have hlF : l ∈ F := hFN ⟨hlL, hl.2⟩
    have hlb : ⁅l, b⁆ ∈ Z := hFB' l hlF b hb
    refine hc.comm_comm_mem_Z_of_comm (R := LB M Q B) hc.LB_le_M hxM (fun ρ hρ => ?_) hlL hbQ ?_
    · exact hc.commutator_LB_le_Q
        (Subgroup.commutator_mem_commutator ((LB M Q B).inv_mem hρ) hx)
    · have h2 : x * ⁅l, b⁆⁻¹ * x⁻¹ ∈ Z :=
        (Subgroup.mem_normalizer_iff.mp (hc.hyp.Z_normal.2 hxM) _).mp (Z.inv_mem hlb)
      have e : ⁅⁅l, b⁆, x⁆ = ⁅l, b⁆ * (x * ⁅l, b⁆⁻¹ * x⁻¹) := by
        simp only [commutatorElement_def]
        group
      rw [e]
      exact Z.mul_mem hlb h2
  rw [← commutatorElement_inv]
  exact (Vt M (LB M Q B) B Z t).inv_mem hV

theorem conjB_le_Vt (h34 : Stroth34Statement) (h91b : Stroth91bStatement) {hc : Ctx M Q Z B}
    {n : ℕ} {t : G} (hs : Sec9Hyp hc n t) {r : G} (hr : Sec7A hc t r) {B' F : Subgroup G}
    (hB'Q : B' ≤ Q) (hB'c : ∀ b ∈ B', ∀ y ∈ B, b * y = y * b) (htF : t ∈ F)
    (hFB' : ∀ f ∈ F, ∀ b ∈ B', ⁅f, b⁆ ∈ Z) (hFN : LB M Q B ⊓ hc.CN t ≤ F) :
    B' ≤ Vt M (LB M Q B) B Z t := by
  obtain ⟨x₀, hx₀L, -, hx₀⟩ := exists_hp95 h34 h91b hs hr
  intro b hb
  have hbW : b ∈ Wt Q (Vt M (LB M Q B) B Z t) := conjB_le_Wt h34 hs hB'Q htF hFB' hb
  have hbA : b ∈ (QB B ⊓ Wt Q (Vt M (LB M Q B) B Z t)) ⊔ Vt M (LB M Q B) B Z t :=
    hx₀ b hbW (comm_LB_conjB_mem_Vt h34 hs hB'Q hB'c hFB' hFN x₀ hx₀L b hb)
  have hcomm : ∀ a ∈ QB B ⊓ Wt Q (Vt M (LB M Q B) B Z t), ∀ v ∈ Vt M (LB M Q B) B Z t,
      a * v = v * a := fun a ha v hv => (Subgroup.mem_centralizer_iff.mp ha.2.2 v hv).symm
  obtain ⟨a, ha, v, hv, rfl⟩ := exists_mul_of_mem_sup hcomm hbA
  have haQ : a ∈ Q := ha.2.1
  have haV : a ∈ Vt M (LB M Q B) B Z t := by
    refine centLam91 h34 hs a ⟨haQ, ha.1⟩ fun l hl => ?_
    have hlL : l ∈ LB M Q B := le_sup_right (a := Q) ⟨hl.1.1, hl.1.2⟩
    have hlF : l ∈ F := hFN ⟨hlL, hl.2⟩
    have hlb : ⁅l, a * v⁆ ∈ Z := hFB' l hlF (a * v) hb
    have hlv : ⁅l, v⁆ ∈ Z := (Ctx.mem_CN.mp hl.2).2 v hv
    have e : ⁅l, a⁆ = ⁅l, a * v⁆ * (a * ⁅l, v⁆ * a⁻¹)⁻¹ := by
      simp only [commutatorElement_def]
      group
    rw [e, hc.conj_Z_of_mem_Q haQ hlv]
    exact Z.mul_mem hlb (Z.inv_mem hlv)
  exact (Vt M (LB M Q B) B Z t).mul_mem haV hv

end HS9

theorem step93L2First_of (h34 : Stroth34Statement) (h311a : Stroth311aStatement)
    (h311bComm : Stroth311bCommStatement) (h311bCard : Stroth311bCardStatement)
    (h312b : Stroth312bStatement) : Step93L2FirstStatement := by
  classical
  intro G _ _ M Q Z B hc n t r Z0 h cfg _hq hLN
  obtain ⟨hs, hr, hZ0, hsc, hh, -, hK, -⟩ := cfg
  have hs5 := hs.toSec5
  have hNC : Sec9NCommStatement := sec9NComm_of_311b h34 h311bComm
  have h91b : Stroth91bStatement := stroth91b_of_steps h34 h311a hNC (step91OrderQB_of h34)
    (step91OrderVQB_of h34) (step91Inter_of h34) (step91MixedComm_of h34)
  have hCentre := step95Centre_of h34 h311a h311bComm h311bCard G M Q Z B hc n t hs Z0 hZ0
  have hc' : Ctx M Q Z (conjSubgroup h B) := hc.conj_of_mem hh
  have hLconj : LB M Q (conjSubgroup h B) = conjSubgroup h (LB M Q B) := hc.LB_conj hh
  have hLH : LB M Q B ≤ H0 M Z := hc.LB_le_H0
  have hL'H : conjSubgroup h (LB M Q B) ≤ H0 M Z := hLconj ▸ hc'.LB_le_H0
  set X : Subgroup G := LB M Q B ⊔ conjSubgroup h (LB M Q B) with hX
  have hFB' : ∀ f ∈ inSubgroup (pCore 2) X, ∀ b ∈ conjSubgroup h B, ⁅f, b⁆ ∈ Z :=
    HS9.comm_mem_Z_of_pCoreIn h34 hc' hs5.width hs5.n_gt (hc.noA2_conj hs5.noA2 hh)
      (hs5.gen.conj_of_mem hh) (hLconj ▸ le_sup_right) (sup_le hLH hL'H)
  have hZ0LN : Z0 ≤ LB M Q B ⊓ hc.CN t := hCentre.1
  have htF : t ∈ inSubgroup (pCore 2) X :=
    hLN (hZ0LN (IsCentrePre.mem_of_mem_LB (hc := hc) hs5.mem hZ0))
  have hB'V : conjSubgroup h B ≤ Vt M (LB M Q B) B Z t :=
    HS9.conjB_le_Vt h34 h91b hs hr hc'.le (step93L2_comm_B hc hh hK) htF hFB' hLN
  have hmV : conjSubgroup h B ⊔ Z ≤ Vt M (LB M Q B) B Z t := sup_le hB'V sec39_Z_le_Vt
  obtain ⟨ρ, hρR, hρ⟩ := step93One_of h34 h311a h311bComm h312b G M Q Z B hc n t hs r hr Z0 hZ0
    hsc h hh hmV
  have hρM : ρ ∈ M := hc.Rt_le_M t hρR
  have hLρ : conjSubgroup h (LB M Q B) = conjSubgroup ρ (LB M Q B) :=
    hc.conj_LB_eq_of_conj_BZ hh hρM hρ
  have hρnorm : ∀ ρ' ∈ Rt M (LB M Q B) t, ∀ y ∈ Q, ρ' * y * ρ'⁻¹ ∈ Q := fun ρ' hρ' y hy =>
    (Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 (hc.Rt_le_M t hρ')) y).mp hy
  intro z hz
  have hzL' : z ∈ conjSubgroup h (LB M Q B) := by
    rw [hLρ, mem_conjSubgroup]
    have hn1 := hZ0.mem_normalizer hρnorm ((Rt M (LB M Q B) t).inv_mem hρR)
    have hz' : ρ⁻¹ * z * ρ⁻¹⁻¹ ∈ Z0 := (Subgroup.mem_normalizer_iff.mp hn1 z).mp hz
    rw [inv_inv] at hz'
    exact (hZ0LN hz').1
  exact ⟨(hZ0LN hz).1, hzL'⟩

end CFSG.RankThree.GF2n.Stroth80
