module

public import CFSG.RankThree.GF2n.Stroth80.Sec97FiveTrans
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.LocalAnalysis.AGLEmbedding.SeitzEqTwo.DescentE
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.Quasithin.H13.L32NSp4Over
public import CFSG.Quasithin.Vol2.Ch10SecKGA318
public import CFSG.RankThree.GF2n.Stroth80.Core4Line
public import CFSG.RankThree.PartTwo.KFacts.KS21Mult
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

namespace HS9

theorem conjSubgroup_Rt_of_conjMod (hc : Ctx M Q Z B) {g s e : G} (hg : g ∈ M) (hsM : s ∈ M)
    (hq : e * (g * s * g⁻¹)⁻¹ ∈ Q) :
    conjSubgroup g (Rt M (LB M Q B) s) = Rt M (LB M Q B) e := by
  have haM : g * s * g⁻¹ ∈ M := M.mul_mem (M.mul_mem hg hsM) (M.inv_mem hg)
  have hyQ : (g * s * g⁻¹)⁻¹ * (e * (g * s * g⁻¹)⁻¹) * (g * s * g⁻¹) ∈ Q := by
    have h := (Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 (M.inv_mem haM))
      (e * (g * s * g⁻¹)⁻¹)).mp hq
    simpa using h
  have h := Rt_mul_of_mem_Q hc (t := g * s * g⁻¹)
    (y := (g * s * g⁻¹)⁻¹ * (e * (g * s * g⁻¹)⁻¹) * (g * s * g⁻¹)) hyQ
  have e' : (g * s * g⁻¹) *
      ((g * s * g⁻¹)⁻¹ * (e * (g * s * g⁻¹)⁻¹) * (g * s * g⁻¹)) = e := by group
  rw [e'] at h
  rw [conjSubgroup_Rt_eq hg s]
  exact h.symm

theorem conjSubgroup_Vt_of_conjMod (hc : Ctx M Q Z B) {g s e : G} (hg : g ∈ M) (hsM : s ∈ M)
    (hq : e * (g * s * g⁻¹)⁻¹ ∈ Q) :
    conjSubgroup g (Vt M (LB M Q B) B Z s) = Vt M (LB M Q B) B Z e := by
  have haM : g * s * g⁻¹ ∈ M := M.mul_mem (M.mul_mem hg hsM) (M.inv_mem hg)
  have hyQ : (g * s * g⁻¹)⁻¹ * (e * (g * s * g⁻¹)⁻¹) * (g * s * g⁻¹) ∈ Q := by
    have h := (Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 (M.inv_mem haM))
      (e * (g * s * g⁻¹)⁻¹)).mp hq
    simpa using h
  have h := Vt_mul_of_mem_Q hc (t := g * s * g⁻¹)
    (y := (g * s * g⁻¹)⁻¹ * (e * (g * s * g⁻¹)⁻¹) * (g * s * g⁻¹)) hyQ
  have e' : (g * s * g⁻¹) *
      ((g * s * g⁻¹)⁻¹ * (e * (g * s * g⁻¹)⁻¹) * (g * s * g⁻¹)) = e := by group
  rw [e'] at h
  rw [conjSubgroup_Vt_eq hg (hc.conj_Z_eq hg) s]
  exact h.symm

theorem sec9Hyp_of_card_le (h34 : Stroth34Statement) (hc : Ctx M Q Z B) {n : ℕ} {t : G}
    (hs : Sec9Hyp hc n t) {X Y : Subgroup G} (hsplit : Split95 M Q Z B t X Y)
    (h1 : OneConcl hc X Y) {e : G} (heE : e ∈ LB M Q B ⊓ X) (heQ : e ∉ Q)
    (hcard : Nat.card ↥(Rt M (LB M Q B) t) ≤ Nat.card ↥(Rt M (LB M Q B) e)) :
    Sec9Hyp hc n e := by
  have hs5 := hs.toSec5
  have hOm : OmegaPlusNat hc e 2 := by
    obtain ⟨-, -, hcase, -⟩ := h1 e heE heQ
    rcases hcase with hR' | h
    · exfalso
      rw [hR'] at hcard
      exact absurd hcard (not_le.mpr (card_sup_lt_Rt h34 hc hs hsplit))
    · exact h
  exact ⟨⟨hs5.width, hs5.n_gt, hs5.noA2, hs5.gen, heE.1, heQ⟩, hOm, hs.large⟩

theorem Vt_eq_of_centre_mem (h34 : Stroth34Statement) (hc : Ctx M Q Z B) {n : ℕ} {t : G}
    (hs : Sec9Hyp hc n t) {Z0 : Subgroup G} (hcen : Centre95 hc t Z0) {s : G} (hs0 : s ∈ Z0)
    (hsQ : s ∉ Q) (hss : Sec9Hyp hc n s) :
    Vt M (LB M Q B) B Z s = Vt M (LB M Q B) B Z t := by
  have hs5 := hs.toSec5
  have h35 := (stroth_3_5 h34 hc hs5.width hs5.n_gt hs5.noA2 hs5.gen).2.1
  have hV := hc.Vt_eq_Ut_and_Wt_eq_Q1_of_not_le_QB h35 hss.toSec5.mem hss.toSec5.notQ
    (sec9_notQB h34 hss)
  rw [hV.1]
  simpa [Ut] using hcen.2.2 s hs0 hsQ

theorem exists_frame_of_conjMod (h34 : Stroth34Statement) (hS4 : Sec4Statement)
    (hc : Ctx M Q Z B) {n : ℕ} {t : G} (hs : Sec9Hyp hc n t) {X Y : Subgroup G}
    (hsplit : Split95 M Q Z B t X Y)
    (h4 : Sec4Concl M Q Z B X Y) (h1 : OneConcl hc X Y) {s g e : G} (hg : g ∈ M) (hsM : s ∈ M)
    (hR : Rt M (LB M Q B) s = Rt M (LB M Q B) t)
    (hV : Vt M (LB M Q B) B Z s = Vt M (LB M Q B) B Z t)
    (heE : e ∈ LB M Q B ⊓ X) (heQ : e ∉ Q) (hq : e * (g * s * g⁻¹)⁻¹ ∈ Q) :
    ∃ X₁ : Subgroup G, Split95 M Q Z B e X₁ Y ∧ Sec9Hyp hc n e ∧
      LB M Q B ⊓ X₁ = LB M Q B ⊓ X := by
  classical
  have hs5 := hs.toSec5
  have hQg : conjSubgroup g Q = Q := hc.conj_Q_eq hg
  have hQn : M ≤ Subgroup.normalizer (Q : Set G) := hc.hyp.Q_normal.2
  have hRe : Rt M (LB M Q B) e = conjSubgroup g (Rt M (LB M Q B) t) := by
    rw [← hR]
    exact (conjSubgroup_Rt_of_conjMod hc hg hsM hq).symm
  have hVe : Vt M (LB M Q B) B Z e = conjSubgroup g (Vt M (LB M Q B) B Z t) := by
    rw [← hV]
    exact (conjSubgroup_Vt_of_conjMod hc hg hsM hq).symm
  have hsplit0 := hsplit
  obtain ⟨⟨hQX, hXR, hQY, hYR, hXY, hXYQ, hcomm⟩, hYsl, hW⟩ := hsplit
  have hYn : ∀ ρ ∈ Rt M (LB M Q B) t, conjSubgroup ρ Y = Y :=
    hsplit0.conjSubgroup_eq_self_of_mem_Rt
  have hYg : conjSubgroup g Y = Y := by
    obtain ⟨-, -, -, huniq⟩ := h1 e heE heQ
    refine huniq (conjSubgroup g Y) ?_ ?_ ?_ ?_
    · rw [← hQg]
      exact Subgroup.map_mono hQY
    · rw [hRe]
      exact Subgroup.map_mono hYR
    · intro r hr
      have hr' : g⁻¹ * r * g ∈ Rt M (LB M Q B) t := by
        rw [hRe] at hr
        exact mem_conjSubgroup.mp hr
      calc conjSubgroup r (conjSubgroup g Y)
          = conjSubgroup g (conjSubgroup (g⁻¹ * r * g) Y) := by
            rw [← conjSubgroup_mul, ← conjSubgroup_mul]
            congr 1
            group
        _ = conjSubgroup g Y := by rw [hYn _ hr']
    · exact hQg ▸ QuotSat.conj (fun X Y _ _ e h => IsSLModel.congr e h) hYsl g
  have hmemY : ∀ y ∈ Y, g⁻¹ * y * g ∈ Y := by
    intro y hy
    have : y ∈ conjSubgroup g Y := by rwa [hYg]
    exact mem_conjSubgroup.mp this
  have hconjQ : ∀ c ∈ Q, g * c * g⁻¹ ∈ Q := by
    intro c hc'
    have : g * c * g⁻¹ ∈ conjSubgroup g Q := mem_conjSubgroup.mpr (by
      rw [show g⁻¹ * (g * c * g⁻¹) * g = c by group]
      exact hc')
    rwa [hQg] at this
  have hsplit1 : Split95 M Q Z B e (conjSubgroup g X) Y := by
    refine ⟨⟨?_, ?_, hQY, ?_, ?_, ?_, ?_⟩, hYsl, ?_⟩
    · rw [← hQg]
      exact Subgroup.map_mono hQX
    · rw [hRe]
      exact Subgroup.map_mono hXR
    · rw [hRe, ← hYg]
      exact Subgroup.map_mono hYR
    · calc conjSubgroup g X ⊔ Y = conjSubgroup g X ⊔ conjSubgroup g Y := by rw [hYg]
        _ = conjSubgroup g (X ⊔ Y) := (conjSubgroup_sup' _ _ _).symm
        _ = Rt M (LB M Q B) e := by rw [hXY, hRe]
    · calc conjSubgroup g X ⊓ Y = conjSubgroup g X ⊓ conjSubgroup g Y := by rw [hYg]
        _ = conjSubgroup g (X ⊓ Y) := (conjSubgroup_inf _ _ _).symm
        _ = Q := by rw [hXYQ, hQg]
    · intro a ha y hy
      have ha' : g⁻¹ * a * g ∈ X := mem_conjSubgroup.mp ha
      have hy' : g⁻¹ * y * g ∈ Y := hmemY y hy
      have e1 : ⁅a, y⁆ = g * ⁅g⁻¹ * a * g, g⁻¹ * y * g⁆ * g⁻¹ := by
        simp only [commutatorElement_def]
        group
      rw [e1]
      exact hconjQ _ (hcomm _ ha' _ hy')
    · intro x hx w hw
      obtain ⟨hwQ, hwC⟩ := hw
      have hx' : g⁻¹ * x * g ∈ X := mem_conjSubgroup.mp hx
      have hwQ' : g⁻¹ * w * g ∈ Q := by
        have := (Subgroup.mem_normalizer_iff.mp (hQn (M.inv_mem hg)) w).mp hwQ
        simpa using this
      have hwC' : g⁻¹ * w * g ∈ Subgroup.centralizer
          ((Vt M (LB M Q B) B Z t : Subgroup G) : Set G) := by
        refine Subgroup.mem_centralizer_iff.mpr fun v hv => ?_
        have hgv : g * v * g⁻¹ ∈ Vt M (LB M Q B) B Z e := by
          rw [hVe]
          exact ⟨v, hv, by simp [MulAut.conj_apply]⟩
        have h2 := Subgroup.mem_centralizer_iff.mp hwC _ hgv
        have e2 : v * (g⁻¹ * w * g) = g⁻¹ * ((g * v * g⁻¹) * w) * g := by group
        have e3 : (g⁻¹ * w * g) * v = g⁻¹ * (w * (g * v * g⁻¹)) * g := by group
        rw [e2, e3, h2]
      have h5 := hW _ hx' _ ⟨hwQ', hwC'⟩
      have e1 : g⁻¹ * ⁅x, w⁆ * g = ⁅g⁻¹ * x * g, g⁻¹ * w * g⁆ := by
        simp only [commutatorElement_def]
        group
      rw [hVe, mem_conjSubgroup, e1]
      exact h5
  have hse : Sec9Hyp hc n e := by
    refine sec9Hyp_of_card_le h34 hc hs hsplit0 h1 heE heQ ?_
    rw [hRe, card_conjSubgroup]
  refine ⟨conjSubgroup g X, hsplit1, hse, ?_⟩
  have h4₁ : Sec4Concl M Q Z B (conjSubgroup g X) Y := hS4 G M Q Z B hc n e hse _ Y hsplit1
  have hcomm1 : ∀ a ∈ conjSubgroup g X, ∀ y ∈ Y, ⁅a, y⁆ ∈ Q := hsplit1.1.2.2.2.2.2.2
  ext l
  constructor
  · rintro ⟨hlL, hlX⟩
    exact ⟨hlL, mem_X_of_comm_mem_Q hc hsplit0 h4 hlL (fun y hy => hcomm1 l hlX y hy)⟩
  · rintro ⟨hlL, hlX⟩
    exact ⟨hlL, mem_X_of_comm_mem_Q hc hsplit1 h4₁ hlL (fun y hy => hcomm l hlX y hy)⟩

theorem normalizes_CN_of_mem_kappa (hc : Ctx M Q Z B) {X : Subgroup G} {h : G} (hh : h ∈ M)
    (hFB : conjSubgroup h B ≤ QB B) (hex : ∃ x ∈ LB M Q B ⊓ X, x ∉ Q)
    (hhard : ∀ x ∈ LB M Q B ⊓ X, x ∉ Q → x ∉ conjSubgroup h (LB M Q B)) {e : G}
    (heE : e ∈ LB M Q B ⊓ X)
    (heN : e ∈ Subgroup.normalizer ((conjSubgroup h (LB M Q B ⊓ X) : Subgroup G) : Set G)) :
    ∀ k ∈ conjSubgroup h (LB M Q B ⊓ X) ⊓
      Subgroup.normalizer ((LB M Q B ⊓ X : Subgroup G) : Set G),
      conjSubgroup k (LB M Q B ⊓ hc.CN e) = LB M Q B ⊓ hc.CN e := by
  intro k hk
  have hLF : LB M Q (conjSubgroup h B) = conjSubgroup h (LB M Q B) := hc.LB_conj hh
  have hLFM : conjSubgroup h (LB M Q B) ≤ M := by
    rw [← hLF]
    exact (hc.conj_of_mem hh).LB_le_M
  have hkM : k ∈ M := hLFM (Subgroup.map_mono inf_le_left hk.1)
  have heM : e ∈ M := hc.LB_le_M heE.1
  have hkL : conjSubgroup k (LB M Q B) = LB M Q B :=
    conj_LB_eq_of_mem_kappaBar hc hh hFB hhard hex hk.1 (conjSubgroup_eq_self_iff.mpr hk.2)
  have hkE : conjSubgroup k (LB M Q B ⊓ X) = LB M Q B ⊓ X := conjSubgroup_eq_self_iff.mpr hk.2
  have heE1 : conjSubgroup e (conjSubgroup h (LB M Q B ⊓ X)) = conjSubgroup h (LB M Q B ⊓ X) :=
    conjSubgroup_eq_self_iff.mpr heN
  have hcomm : ⁅k, e⁆ ∈ Q := by
    have h1 : ⁅k, e⁆ ∈ LB M Q B ⊓ X := by
      have hmem : k * e * k⁻¹ ∈ conjSubgroup k (LB M Q B ⊓ X) :=
        ⟨e, heE, by simp [MulAut.conj_apply]⟩
      rw [hkE] at hmem
      have e1 : ⁅k, e⁆ = (k * e * k⁻¹) * e⁻¹ := by simp only [commutatorElement_def]
      rw [e1]
      exact (LB M Q B ⊓ X).mul_mem hmem ((LB M Q B ⊓ X).inv_mem heE)
    have h2 : ⁅k, e⁆ ∈ conjSubgroup h (LB M Q B ⊓ X) := by
      have hmem : e * k⁻¹ * e⁻¹ ∈ conjSubgroup e (conjSubgroup h (LB M Q B ⊓ X)) :=
        ⟨k⁻¹, (conjSubgroup h (LB M Q B ⊓ X)).inv_mem hk.1, by simp [MulAut.conj_apply]⟩
      rw [heE1] at hmem
      have e1 : ⁅k, e⁆ = k * (e * k⁻¹ * e⁻¹) := by
        simp only [commutatorElement_def]
        group
      rw [e1]
      exact (conjSubgroup h (LB M Q B ⊓ X)).mul_mem hk.1 hmem
    by_contra hnot
    exact hhard _ h1 hnot (Subgroup.map_mono inf_le_left h2)
  have hy : e⁻¹ * ⁅k, e⁆ * e ∈ Q := by
    have := (Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 (M.inv_mem heM)) ⁅k, e⁆).mp hcomm
    simpa using this
  have hCN : conjSubgroup k (hc.CN e) = hc.CN e := by
    rw [← hc.CN_conjM hkM e]
    have e1 : k * e * k⁻¹ = e * (e⁻¹ * ⁅k, e⁆ * e) := by
      simp only [commutatorElement_def]
      group
    rw [e1]
    exact hc.CN_mul_of_mem_Q hy
  exact conjSubgroup_inf_of_eq hkL hCN

end HS9

end CFSG.RankThree.GF2n.Stroth80
