module

public import CFSG.RankThree.GF2n.Stroth80.Sec93OmPfLinAlgGroup
public import CFSG.RankThree.GF2n.Stroth80.Sec93OmPfStep2
public import CFSG.RankThree.GF2n.Stroth80.Sec93OmPfStep3
public import CFSG.RankThree.GF2n.Stroth80.Sec93OmPfStep4
public import CFSG.RankThree.GF2n.Stroth80.Sec93OmPfStep5
public import CFSG.RankThree.GF2n.Stroth80.Sec93OmPfNormCN
public import CFSG.RankThree.GF2n.Stroth80.Sec93OmPfFrame
public import CFSG.RankThree.GF2n.Stroth80.CarterSec93Omega
public import CFSG.RankThree.GF2n.Stroth80.HeringSec93One
public import CFSG.RankThree.GF2n.Stroth80.HeringSec93XH

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix

namespace HS9

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem comm_CN_mem_Q_of_mem_inf (h34 : Stroth34Statement) (h311a : Stroth311aStatement)
    (h311bComm : Stroth311bCommStatement) (h311bCard : Stroth311bCardStatement)
    {hc : Ctx M Q Z B} {n : ℕ} {t r : G} {Z0 : Subgroup G} {h : G}
    (cfg : HS9.Cfg93c hc n t r Z0 h) {x : G}
    (hxK : x ∈ LB M Q B ⊓ conjSubgroup h (LB M Q B)) (hxQ : x ∉ Q) (hP4 : OmegaPlusNat hc x 2)
    {s : G} (hsZ : s ∈ Z0) (hsN : s ∈ hc.CN x) : ∀ b ∈ hc.CN x, ⁅s, b⁆ ∈ Q := by
  classical
  have hs := cfg.hs
  have hs5 := hs.toSec5
  have hxL : x ∈ LB M Q B := (Subgroup.mem_inf.mp hxK).1
  have hxL' : x ∈ conjSubgroup h (LB M Q B) := (Subgroup.mem_inf.mp hxK).2
  have hsx : Sec9Hyp hc n x :=
    ⟨⟨hs5.width, hs5.n_gt, hs5.noA2, hs5.gen, hxL, hxQ⟩, hP4, hs.large⟩
  have hsx5 := hsx.toSec5
  have hcen := step95Centre_of h34 h311a h311bComm h311bCard G M Q Z B hc n t hs Z0 cfg.hZ0
  have hZ0L : Z0 ≤ LB M Q B := hcen.1.trans inf_le_left
  obtain ⟨Z0x, hZ0x⟩ := exists_isCentrePre (Q := Q) (hc.Q_le_Rt hxL)
  have hcenx := step95Centre_of h34 h311a h311bComm h311bCard G M Q Z B hc n x hsx Z0x hZ0x
  have hZ0xL : Z0x ≤ LB M Q B := hcenx.1.trans inf_le_left
  have hZ0xL' : Z0x ≤ conjSubgroup h (LB M Q B) :=
    centre_le_conj_LB91 h34 h311a h311bComm h311bCard hsx hZ0x cfg.hh hxL'
  have hZ0xK : Z0x ≤ LB M Q B ⊓ conjSubgroup h (LB M Q B) := le_inf hZ0xL hZ0xL'
  have hT : ∀ a, a ∈ Z0x ↔ a ∈ LB M Q B ∧ ∀ r ∈ Rt M (LB M Q B) x, ⁅r, a⁆ ∈ Q := by
    intro a
    constructor
    · intro ha
      refine ⟨hZ0xL ha, fun ρ hρ => ?_⟩
      rw [← commutatorElement_inv]
      exact Q.inv_mem (hZ0x.comm_mem ha hρ)
    · rintro ⟨haL, haQ⟩
      refine hZ0x.mem_iff.mpr ⟨le_Rt (M := M) (LB M Q B) hxL haL, fun ρ hρ => ?_⟩
      rw [← commutatorElement_inv]
      exact Q.inv_mem (haQ ρ hρ)
  have hcommCN : ⁅hc.CN x, hc.CN x⁆ ≤ Z0x :=
    h311bComm G M Q Z B hc n hsx5.width hsx5.n_gt hsx5.noA2 hsx5.gen x hxL hsx5.notQ
      (sec9_Rt_ne_LB h34 hsx) (sec9_not_SLNat hsx) Z0x hT
  intro b hb
  have h1 := comm_mem_inf_CN hxL hZ0L cfg.hsc hsZ hb
  have h2 : ⁅s, b⁆ ∈ Z0x := hcommCN (Subgroup.commutator_mem_commutator hsN hb)
  have h3 : ⁅s, b⁆ ∈ Z0 ⊓ (LB M Q B ⊓ conjSubgroup h (LB M Q B)) :=
    Subgroup.mem_inf.mpr ⟨(Subgroup.mem_inf.mp h1).1, hZ0xK h2⟩
  rwa [cfg.hZQ] at h3

theorem Vt_le_of_not_inf_CN_le_Q (h34 : Stroth34Statement) (h311a : Stroth311aStatement)
    (h311bComm : Stroth311bCommStatement) (h311bCard : Stroth311bCardStatement)
    {hc : Ctx M Q Z B} {n : ℕ} {t r : G} {Z0 : Subgroup G} {h : G}
    (cfg : HS9.Cfg93c hc n t r Z0 h) {x : G}
    (hxK : x ∈ LB M Q B ⊓ conjSubgroup h (LB M Q B)) (hxQ : x ∉ Q) (hP4 : OmegaPlusNat hc x 2)
    (hA : ¬ Z0 ⊓ hc.CN x ≤ Q) :
    Vt M (LB M Q B) B Z t ≤ Vt M (LB M Q B) B Z x := by
  classical
  obtain ⟨s, hs0, hsQ⟩ := SetLike.not_le_iff_exists.mp hA
  obtain ⟨hsZ, hsN⟩ := Subgroup.mem_inf.mp hs0
  have hcommS := comm_CN_mem_Q_of_mem_inf h34 h311a h311bComm h311bCard cfg hxK hxQ hP4 hsZ hsN
  have hs := cfg.hs
  have hs5 := hs.toSec5
  have hxL : x ∈ LB M Q B := (Subgroup.mem_inf.mp hxK).1
  have hsx : Sec9Hyp hc n x :=
    ⟨⟨hs5.width, hs5.n_gt, hs5.noA2, hs5.gen, hxL, hxQ⟩, hP4, hs.large⟩
  have hsx5 := hsx.toSec5
  have hcen := step95Centre_of h34 h311a h311bComm h311bCard G M Q Z B hc n t hs Z0 cfg.hZ0
  have hZ0L : Z0 ≤ LB M Q B := hcen.1.trans inf_le_left
  have hNC : Sec9NCommStatement := sec9NComm_of_311b h34 h311bComm
  obtain ⟨r', hr'⟩ := sec9AExists_of h34 h311a hNC G M Q Z B hc n x hsx
  have h91b : Stroth91bStatement := stroth91b_of_steps h34 h311a hNC (step91OrderQB_of h34)
    (step91OrderVQB_of h34) (step91Inter_of h34) (step91MixedComm_of h34)
  have hchi := stroth91c_of_34 h34 G M Q Z B hc n x hsx (Rt M (LB M Q B) x)
    (Vt M (LB M Q B) B Z x) (Wt Q (Vt M (LB M Q B) B Z x)) rfl rfl rfl
  obtain ⟨hdsum, hNW⟩ := h91b G M Q Z B hc n x hsx r' hr' (Vt M (LB M Q B) B Z x)
    (Wt Q (Vt M (LB M Q B) B Z x)) rfl rfl
  have hdec : Wt Q (Vt M (LB M Q B) B Z x) ≤ (QB B ⊓ Wt Q (Vt M (LB M Q B) B Z x)) ⊔
      (QB (conjSubgroup r' B) ⊓ Wt Q (Vt M (LB M Q B) B Z x)) ⊔ Vt M (LB M Q B) B Z x := by
    obtain ⟨-, -, -, -, hsup, -⟩ := hdsum
    exact le_trans (le_of_eq hsup.symm) (sup_le
      (sup_le (le_sup_right.trans le_sup_left) le_sup_right)
      (sup_le (le_sup_left.trans le_sup_left) le_sup_right))
  obtain ⟨hVab, hWdef⟩ := n12Lemma2_of_chi h34 hc hsx5 hchi
  obtain ⟨g1, g2, g3, g4, g5, g6, g7⟩ := n12Lemma3_of_data h34 hc hsx5 hr' hchi hdec hNW
  obtain ⟨k0, k1, k2, k3, k4⟩ := n12Lemma4_of_notQB h34 hc hsx5 hr' (sec9_notQB h34 hsx)
  obtain ⟨f1, f2⟩ := n12Lemma5_of_faith hc hxL hr' (centLam91 h34 hsx)
  obtain ⟨hZQ, hZc, hcomm, hsq⟩ := n12Q_holds G M Q Z B hc
  obtain ⟨lam, hlam⟩ := n12Lam_holds G M Q Z B hc
  have hnd := n12Lemma1_holds G M Q Z B hc lam hlam
  have hZV : Z ≤ Vt M (LB M Q B) B Z x := sec39_Z_le_Vt
  have hstrong := propAGroup_strong Q Z (Vt M (LB M Q B) B Z x)
    (Wt Q (Vt M (LB M Q B) B Z x)) (QB B ⊓ Wt Q (Vt M (LB M Q B) B Z x))
    (QB (conjSubgroup r' B) ⊓ Wt Q (Vt M (LB M Q B) B Z x)) (B ⊔ Z)
    (Q ⊓ QB (conjSubgroup r' B)) lam (n12X hc x) (n12Y hc x r') hZQ hZc hcomm hsq hnd hZV
    (hc.Vt_le_Q x) inf_le_left hVab (hWdef lam hlam) g7 g5 g6 le_sup_right (le_inf hZQ k0)
    (sup_le hc.le hZQ) inf_le_left k4 g1 g2 g3 g4
    (fun g hg a ha => (Ctx.mem_CN.1 (by rcases hg with h | h <;> exact h.2)).2 a ha)
    k1 k2 k3 f1 f2
  have hsL : s ∈ LB M Q B := hZ0L hsZ
  obtain ⟨g, hgmem, q₀, hq₀, hsg⟩ := exists_mul_of_mem_sup_of_le_normalizer
    (H := QB B ⊓ M) (K := Q) (fun g hg => hc.hyp.Q_normal.2 hg.2)
    (show s ∈ (QB B ⊓ M) ⊔ Q by rw [sup_comm]; exact hsL)
  have hq₀CN : q₀ ∈ hc.CN x := sec8_Q_le_CN hc hxL hq₀
  have hgeq : g = s * q₀⁻¹ := by rw [← hsg]; group
  have hgCN : g ∈ hc.CN x := by
    rw [hgeq]
    exact (hc.CN x).mul_mem hsN ((hc.CN x).inv_mem hq₀CN)
  have hgX : g ∈ n12X hc x := ⟨hgmem, hgCN⟩
  have hsM : s ∈ M := hc.Rt_le_M x (Ctx.mem_CN.mp hsN).1
  have hgcomm : ∀ b ∈ hc.CN x, ⁅g, b⁆ ∈ Q := by
    intro b hb
    have hbM : b ∈ M := hc.Rt_le_M x (Ctx.mem_CN.mp hb).1
    have e : ⁅g, b⁆ = s * ⁅q₀⁻¹, b⁆ * s⁻¹ * ⁅s, b⁆ := by
      rw [hgeq]; simp only [commutatorElement_def]; group
    rw [e]
    have h1 : ⁅q₀⁻¹, b⁆ ∈ Q := by
      have e1 : ⁅q₀⁻¹, b⁆ = q₀⁻¹ * (b * q₀ * b⁻¹) := by
        simp only [commutatorElement_def]; group
      rw [e1]
      exact Q.mul_mem (Q.inv_mem hq₀)
        ((Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 hbM) q₀).mp hq₀)
    exact Q.mul_mem ((Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 hsM) _).mp h1)
      (hcommS b hb)
  have hfixSB : ∀ a ∈ QB B ⊓ Wt Q (Vt M (LB M Q B) B Z x), ⁅g, a⁆ ∈ Z := by
    intro a ha
    by_contra hna
    obtain ⟨y, hy, hyQ⟩ := hstrong.1 g hgX ⟨a, ha, hna⟩
    exact hyQ (hgcomm y hy.2)
  have hkey := hstrong.2 g hgX hfixSB (fun x' hx' => hgcomm x' hx'.2)
  have hnormV : s ∈ Subgroup.normalizer (Vt M (LB M Q B) B Z x : Set G) :=
    hc.Rt_normalizes_Vt hxL (Ctx.mem_CN.mp hsN).1
  have hsV : ∀ a ∈ Q, ⁅a, s⁆ ∈ Vt M (LB M Q B) B Z x := by
    intro a ha
    have hgM : g ∈ M := hgmem.2
    have e : ⁅s, a⁆ = g * ⁅q₀, a⁆ * g⁻¹ * ⁅g, a⁆ := by
      rw [← hsg]; simp only [commutatorElement_def]; group
    have h1 : ⁅q₀, a⁆ ∈ Z := hcomm q₀ hq₀ a ha
    have h2 : g * ⁅q₀, a⁆ * g⁻¹ ∈ Z :=
      (Subgroup.mem_normalizer_iff.mp (hc.hyp.Z_normal.2 hgM) _).mp h1
    have h3 : ⁅s, a⁆ ∈ Vt M (LB M Q B) B Z x := by
      rw [e]
      exact (Vt M (LB M Q B) B Z x).mul_mem (hZV h2) (hkey a ha)
    rw [← commutatorElement_inv]
    exact (Vt M (LB M Q B) B Z x).inv_mem h3
  have hUle : ⁅Q, Subgroup.zpowers s⁆ ≤ Vt M (LB M Q B) B Z x :=
    commutator_zpowers_le hnormV hsV
  rw [← hcen.2.2 s hsZ hsQ]
  exact sup_le hUle hZV

theorem false_of_not_inf_CN_le_Q_free (h34 : Stroth34Statement) (h311a : Stroth311aStatement)
    (h311bComm : Stroth311bCommStatement) (h311bCard : Stroth311bCardStatement)
    (h312b : Stroth312bStatement)
    {hc : Ctx M Q Z B} {n : ℕ} {t r : G} {Z0 : Subgroup G} {h : G}
    (cfg : HS9.Cfg93c hc n t r Z0 h) {x : G}
    (hxK : x ∈ LB M Q B ⊓ conjSubgroup h (LB M Q B)) (hxQ : x ∉ Q) (hP4 : OmegaPlusNat hc x 2)
    (hA : ¬ Z0 ⊓ hc.CN x ≤ Q) : False := by
  classical
  have hVle := Vt_le_of_not_inf_CN_le_Q h34 h311a h311bComm h311bCard cfg hxK hxQ hP4 hA
  have hs := cfg.hs
  have hs5 := hs.toSec5
  have hxL' : x ∈ conjSubgroup h (LB M Q B) := (Subgroup.mem_inf.mp hxK).2
  have hxL : x ∈ LB M Q B := (Subgroup.mem_inf.mp hxK).1
  have hsx : Sec9Hyp hc n x :=
    ⟨⟨hs5.width, hs5.n_gt, hs5.noA2, hs5.gen, hxL, hxQ⟩, hP4, hs.large⟩
  have hVeq : Vt M (LB M Q B) B Z t = Vt M (LB M Q B) B Z x :=
    Subgroup.eq_of_le_of_card_ge hVle (le_of_eq (hsx.card_V.trans hs.card_V.symm))
  have hBh : conjSubgroup h B ≤ Vt M (LB M Q B) B Z t := by
    rw [hVeq]
    exact sec39_conjB_le_Vt (M := M) (L := LB M Q B) (B := B) (Z := Z) (t := x) cfg.hh hxL'
  have hmV : conjSubgroup h B ⊔ Z ≤ Vt M (LB M Q B) B Z t := sup_le hBh sec39_Z_le_Vt
  obtain ⟨ρ, hρR, hρ⟩ := step93One_of h34 h311a h311bComm h312b G M Q Z B hc n t hs r cfg.hr Z0
    cfg.hZ0 cfg.hsc h cfg.hh hmV
  have hρM : ρ ∈ M := hc.Rt_le_M t hρR
  have hLρ : conjSubgroup h (LB M Q B) = conjSubgroup ρ (LB M Q B) :=
    hc.conj_LB_eq_of_conj_BZ cfg.hh hρM hρ
  have hρnorm : ∀ ρ' ∈ Rt M (LB M Q B) t, ∀ y ∈ Q, ρ' * y * ρ'⁻¹ ∈ Q := fun ρ' hρ' y hy =>
    (Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 (hc.Rt_le_M t hρ')) y).mp hy
  have hZ0LB : Z0 ≤ LB M Q B := sec93Omega_Z0_le_LB h34 h311a h311bComm hs cfg.hr cfg.hZ0
  have hZH : Z0 ≤ LB M Q B ⊓ conjSubgroup h (LB M Q B) := by
    intro z hz
    have hzL' : z ∈ conjSubgroup h (LB M Q B) := by
      rw [hLρ, mem_conjSubgroup]
      have hn1 := cfg.hZ0.mem_normalizer hρnorm ((Rt M (LB M Q B) t).inv_mem hρR)
      have hz' : ρ⁻¹ * z * ρ⁻¹⁻¹ ∈ Z0 := (Subgroup.mem_normalizer_iff.mp hn1 z).mp hz
      rw [inv_inv] at hz'
      exact hZ0LB hz'
    exact ⟨hZ0LB hz, hzL'⟩
  exact (sec93Omega_of_centre_le hs cfg.hZ0 hZH) cfg.hZQ

end HS9

end CFSG.RankThree.GF2n.Stroth80
