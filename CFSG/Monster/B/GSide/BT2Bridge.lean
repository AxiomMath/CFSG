module

public import CFSG.Monster.B.GSide.BT2BridgeData
public import CFSG.Monster.B.GSide.BT2BridgeK1
public import CFSG.Monster.B.GSide.BT2PiModel
public import CFSG.Monster.B.GSide.BT2Generation
public import CFSG.Monster.B.TwoA.Amalgam.EightOrbitsPres
public meta import CFSG.Monster.B.GSide.MuFourOmega
public meta import Certificates.Data.CFSGNative.MonsterB.Co2Data
public meta import Certificates.Data.CFSGNative.MonsterB.Co2Matrix
public import Certificates.Certificate3131
public import Certificates.Certificate3057
public import Certificates.Certificate3058
public import Certificates.Certificate3060
public import Certificates.Certificate3061
public import Certificates.Certificate3130
public import Certificates.Certificate3178
public import Certificates.Certificate3179
public import Certificates.Certificate45
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate49
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate53
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate59
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate68
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate72
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate80
public import Certificates.Certificate81
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate117
public import Certificates.Certificate120
public import Certificates.Certificate3011
public import Certificates.Certificate3012
public import Certificates.Certificate3014
public import Certificates.Certificate3017
public import Certificates.Certificate3019
public import Certificates.Certificate3025
public import Certificates.Certificate3026
public import Certificates.Certificate3027
public import Certificates.Certificate3028
public import Certificates.Certificate3041
public import Certificates.Certificate3042
public import Certificates.Certificate3045
public import Certificates.Certificate3048
public import Certificates.Certificate3049
public import Certificates.Certificate3050
public import Certificates.Certificate3051
public import Certificates.Certificate3054
public import Certificates.Certificate3055
public import Certificates.Certificate3056
public import Certificates.Certificate3059
public import Certificates.Certificate3062
public import Certificates.Certificate3063
public import Certificates.Certificate3072
public import Certificates.Certificate3073
public import Certificates.Certificate3074
public import Certificates.Certificate3075
public import Certificates.Certificate3076
public import Certificates.Certificate3077
public import Certificates.Certificate3078
public import Certificates.Certificate3079
public import Certificates.Certificate3080
public import Certificates.Certificate3081
public import Certificates.Certificate3082
public import Certificates.Certificate3083
public import Certificates.Certificate3098
public import Certificates.Certificate3099
public import Certificates.Certificate3100
public import Certificates.Certificate3101
public import Certificates.Certificate3102
public import Certificates.Certificate3103
public import Certificates.Certificate3106
public import Certificates.Certificate3107
public import Certificates.Certificate3108
public import Certificates.Certificate3109
public import Certificates.Certificate3110
public import Certificates.Certificate3111
public import Certificates.Certificate3114
public import Certificates.Certificate3115
public import Certificates.Certificate3116
public import Certificates.Certificate3117
public import Certificates.Certificate3118
public import Certificates.Certificate3122
public import Certificates.Certificate3124
public import Certificates.Certificate3125
public import Certificates.Certificate3126
public import Certificates.Certificate3127
public import Certificates.Certificate3175
public import Certificates.Certificate16001
public import Certificates.Certificate16015
public import Certificates.Certificate16016
public import Certificates.Certificate16021
public import Certificates.Certificate16022
public import Certificates.Certificate16028
public import Certificates.Certificate16029
public import Certificates.Certificate16033
public import Certificates.Certificate16035
public import Certificates.Certificate16036
public import Certificates.Certificate16040
public import Certificates.Certificate3029
public import Certificates.Certificate3030
public import Certificates.Certificate3031
public import Certificates.Certificate3033
public import Certificates.Certificate3034
public import Certificates.Certificate3035
public import Certificates.Certificate3036
public import Certificates.Certificate3065
public import Certificates.Certificate16003
public import Certificates.Certificate16010
public import Certificates.Certificate16023
public import Certificates.Certificate16042
public import Certificates.Certificate16951
public import Certificates.Certificate1953
public import Certificates.Certificate1954
public import Certificates.Certificate3066
public import Certificates.Certificate3067
public import Certificates.Certificate3032
public import Certificates.Certificate3068
public import Certificates.Certificate3069
public import CFSG.Monster.B.GSide.BT2BridgeK1Inputs

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.GSide

open SimpleGraph CFSG.Monster CFSG.Monster.B CFSG.Monster.B.TwoA CFSG.Monster.B.TwoA.Sp8
  CFSG.Monster.B.TwoA.Amalgam
open CFSG.Monster.B.Co2 (v0 decW decW_xor decW_injective)
open CFSG.Monster.B.Short (Wv)

theorem vectors_all_lt :
    Co2.Native.vectors.all (fun x => decide (x < 2 ^ 22)) = true :=
  Certificates.certificate3131.1

theorem lt_of_contains {c : ℕ}
    (h : Co2.Native.vectors.contains c = true) : c < 2 ^ 22 :=
  of_decide_eq_true (Array.all_eq_true_iff_forall_mem.1 vectors_all_lt c
    (Array.contains_iff_mem.1 h))

theorem qPoly_eOne_e0 : qPoly (eOne + Pi.single 0 1) = 0 := by decide

theorem qPoly_eOnePlus_e0 : qPoly (eOnePlus + Pi.single 0 1) = 0 := by decide

theorem sigVert_mem_cPi0
    {v : Fin 8 → ZMod 2} (hv : qPoly v = 0)
    (hv' : qPoly (v + Pi.single 0 1) = 0) (hne : v ≠ v + Pi.single 0 1) : sigVert v ∈ cPi0 := by
  have hadj : cgraph.Adj (sigVert v) (sigVert (v + Pi.single 0 1)) :=
    cSigma_isClique (sigVert_mem hv) (sigVert_mem hv') ((sigVert_eq_iff hv hv').not.2 hne)
  refine mem_cPi0_of_clabel_mul_eq_xhat hadj ?_
  rw [clabel_sigVert hv, clabel_sigVert hv', Psi_add]
  have hc := commute_cQ_Psi v
  calc cQ * Psi v * (cQ * (Psi v * Psi (Pi.single 0 1))) =
        cQ * (Psi v * cQ) * (Psi v * Psi (Pi.single 0 1)) := by group
    _ = cQ * (cQ * Psi v) * (Psi v * Psi (Pi.single 0 1)) := by rw [← hc]
    _ = (cQ * cQ) * (Psi v * Psi v) * Psi (Pi.single 0 1) := by group
    _ = xhat := by
        rw [cQ_mul_self, ← Psi_add, ZModModule.add_self, Psi_zero', one_mul, one_mul, Psi_single]
        rfl

theorem eOne_ne : eOne ≠ eOne + Pi.single 0 1 := by decide

theorem eOnePlus_ne : eOnePlus ≠ eOnePlus + Pi.single 0 1 := by decide

theorem sigVert_eOne_mem :
    sigVert eOne ∈ cPi0 :=
  sigVert_mem_cPi0 qPoly_eOne qPoly_eOne_e0 eOne_ne

theorem sigVert_eOnePlus_mem :
    sigVert eOnePlus ∈ cPi0 :=
  sigVert_mem_cPi0 qPoly_eOnePlus qPoly_eOnePlus_e0 eOnePlus_ne

theorem cpsi_eq_of_clabel
    {y : CVert} (hy : y ∈ cPi0) {e : Ehat} (he : clabel y = e) :
    (cpsi ⟨y, hy⟩ : Wv v0) = psiW e := by
  rw [← psiW_clabel_cPi0]
  congr 1
  exact Subtype.ext he

theorem cpsi_cv0 :
    (cpsi ⟨cv0, cv0_mem_cPi0⟩ : Wv v0) = decW 6144 := by
  rw [cpsi_eq_of_clabel cv0_mem_cPi0 (e := cE) clabel_cv0, psiW_cE, Unitary.sigmaW_eq_decW]

theorem cpsi_sigVert_eOne :
    (cpsi ⟨sigVert eOne, sigVert_eOne_mem⟩ : Wv v0) = decW 6175 :=
    by
  have he : clabel (sigVert eOne) = ((cE * yhatE : Ehat) : Dfull) := by
    rw [clabel_sigVert qPoly_eOne, Psi_single]
    rfl
  rw [cpsi_eq_of_clabel sigVert_eOne_mem he, psiW_mul, psiW_cE, psiW_yhat8,
    Unitary.sigmaW_eq_decW, ← decW_xor]
  exact congrArg decW (by norm_num)

theorem cpsi_sigVert_eOnePlus :
    (cpsi ⟨sigVert eOnePlus, sigVert_eOnePlus_mem⟩ : Wv v0) = decW 24606 := by
  have hv : vPlus = Pi.single 6 1 := by decide
  have he : clabel (sigVert eOnePlus) = ((cE * yhatE * uhatE : Ehat) : Dfull) := by
    rw [clabel_sigVert qPoly_eOnePlus, Psi_add, hv, Psi_single, Psi_single]
    show cQ * (aT 1 * aT 6) = cQ * yhat * uhat
    rw [← mul_assoc]
    rfl
  rw [cpsi_eq_of_clabel sigVert_eOnePlus_mem he, psiW_mul, psiW_mul, psiW_cE, psiW_yhat8,
    psiW_uhat, Unitary.sigmaW_eq_decW, ← decW_xor, ← decW_xor]
  exact congrArg decW (by norm_num)

@[irreducible] def codeVert
    (c : ℕ) : CVert :=
  if c = 6144 then cv0 else if c = 6175 then sigVert eOne else if c = 24606 then
    sigVert eOnePlus else if h : Co2.Native.vectors.contains c = true then
      (piSec ⟨decW c, Unitary.decW_mem_OmegaW h⟩ : CVert) else cv0

theorem codeVert_6144 :
    codeVert 6144 = cv0 := by
  rw [codeVert]
  simp

theorem codeVert_6175 :
    codeVert 6175 = sigVert
    eOne := by
  rw [codeVert]
  simp

theorem codeVert_24606 :
    codeVert 24606 = sigVert
    eOnePlus := by
  rw [codeVert]
  simp

theorem codeVert_spec
    {c : ℕ}
    (h : Co2.Native.vectors.contains c = true) :
    ∃ hc : codeVert c ∈ cPi0, (cpsi ⟨codeVert c, hc⟩ : Wv v0) = decW c := by
  by_cases h1 : c = 6144
  · subst h1
    rw [codeVert_6144]
    exact ⟨cv0_mem_cPi0, cpsi_cv0⟩
  by_cases h2 : c = 6175
  · subst h2
    rw [codeVert_6175]
    exact ⟨sigVert_eOne_mem, cpsi_sigVert_eOne⟩
  by_cases h3 : c = 24606
  · subst h3
    rw [codeVert_24606]
    exact ⟨sigVert_eOnePlus_mem, cpsi_sigVert_eOnePlus⟩
  have e : codeVert c = (piSec ⟨decW c, Unitary.decW_mem_OmegaW h⟩ : CVert) := by
    rw [codeVert]
    simp only [h1, h2, h3, h, ↓reduceIte, ↓reduceDIte]
  rw [e]
  refine ⟨(piSec _).2, ?_⟩
  have := cpsi_piSec ⟨decW c, Unitary.decW_mem_OmegaW h⟩
  rw [show (⟨(piSec ⟨decW c, Unitary.decW_mem_OmegaW h⟩ : CVert), (piSec _).2⟩ : cPi0) =
    piSec ⟨decW c, Unitary.decW_mem_OmegaW h⟩ from rfl, this]

@[expose] def codeVertPi
    (c : ℕ)
    (h : Co2.Native.vectors.contains c = true) : cPi0 :=
  ⟨codeVert c, (codeVert_spec h).1⟩

theorem cpsi_codeVertPi
    {c : ℕ}
    (h : Co2.Native.vectors.contains c = true) :
    (cpsi (codeVertPi c h) : Wv v0) = decW c :=
  (codeVert_spec h).2

theorem codeVertPi_ne
    {a b : ℕ}
    (ha : Co2.Native.vectors.contains a = true)
    (hb : Co2.Native.vectors.contains b = true) (hab : a ≠ b) :
    cpsi (codeVertPi a ha) ≠ cpsi (codeVertPi b hb) := by
  intro e
  have e' := congrArg (fun z : Unitary.OmegaPt => (z : Wv v0)) e
  simp only [cpsi_codeVertPi] at e'
  exact hab (decW_injective (lt_of_contains ha) (lt_of_contains hb) e')

theorem adj_codeVert_iff
    {a b : ℕ}
    (ha : Co2.Native.vectors.contains a = true)
    (hb : Co2.Native.vectors.contains b = true) (hab : a ≠ b) :
    cgraph.Adj (codeVert a) (codeVert b) ↔ bWcode a b = 0 := by
  have hne : codeVertPi a ha ≠ codeVertPi b hb := fun e =>
    codeVertPi_ne ha hb hab (congrArg cpsi e)
  have h := cgraphPi_adj_iff hne
  have hψ := codeVertPi_ne ha hb hab
  change cgraph.Adj (codeVertPi a ha : CVert) (codeVertPi b hb) ↔ _
  refine (h.trans ⟨fun h' => h'.resolve_left hψ, Or.inr⟩).trans ?_
  rw [omegaGraph_adj_iff_bW, cpsi_codeVertPi, cpsi_codeVertPi, bW_decW]
  constructor
  · rintro ⟨-, h0⟩
    have hlt : bWcode a b < 2 := Nat.mod_lt _ (by norm_num)
    interval_cases hb' : bWcode a b
    · rfl
    · exact absurd h0 (by decide)
  · intro h0
    exact ⟨hψ, by rw [h0]; rfl⟩

@[expose] def codeHom :
    codeGraph →g cgraph where
  toFun := codeVert
  map_rel' {a b} h := by
    obtain ⟨hab, h0, -, ha, hb⟩ := codeGraph_adj_iff.1 h
    exact (adj_codeVert_iff ha hb hab).2 h0

theorem isType1782_codeVert :
    ∀
    a b c : ℕ, CodeT a b c →
    IsType1782 (codeHom a) (codeHom b) (codeHom c) := by
  intro a b c h
  obtain ⟨hab, hbc, hca, hs⟩ := h
  have hab' := codeHom.map_rel' (a := a) (b := b) hab
  have hbc' := codeHom.map_rel' (a := b) (b := c) hbc
  have hca' := codeHom.map_rel' (a := c) (b := a) hca
  obtain ⟨-, -, -, ha, hb⟩ := codeGraph_adj_iff.1 hab
  obtain ⟨-, -, -, -, hc⟩ := codeGraph_adj_iff.1 hbc
  have e := isType1782_of_cPi0 (u := codeVertPi a ha) (v := codeVertPi b hb)
    (w := codeVertPi c hc) hab' hca'.symm hbc' ?_
  · exact e
  rw [cpsi_codeVertPi, cpsi_codeVertPi, cpsi_codeVertPi, ← decW_xor, ← decW_xor]
  exact Unitary.decW_mem_OmegaW hs

theorem codeHom_apply
    (c : ℕ) : codeHom c = codeVert c := rfl

theorem codeHom_6144 :
    codeHom 6144 = cv0 := codeVert_6144

theorem codeHom_6175 :
    codeHom 6175 = sigVert eOne := codeVert_6175

theorem codeHom_24606 :
    codeHom 24606 = sigVert eOnePlus :=
    codeVert_24606

theorem triRel_tStar :
    TriRel cgraph IsType1782 cv0 (sigVert eOne) (sigVert eOnePlus) (codeHom 2652785) := by
  have e := TriRel.map codeHom isType1782_codeVert codeAdj_σ_w codeAdj_w_q₁ codeAdj_q₁_σ
    codeAdj_w_q₂ codeAdj_q₂_σ triRel_bridge
  rwa [codeHom_6144, codeHom_6175, codeHom_24606] at e

theorem contains_24606 : Co2.Native.vectors.contains 24606 = true :=
  Certificates.certificate3131.2.1

theorem contains_2652785 :
    Co2.Native.vectors.contains 2652785 = true :=
  Certificates.certificate3131.2.2.1

theorem bWcode_q₁_q₂ : bWcode 24606 2652785 ≠ 0 :=
  Certificates.certificate3131.2.2.2

theorem not_adj_tStar_q₂ :
    sigVert eOnePlus ≠ codeHom 2652785 ∧ ¬ cgraph.Adj (sigVert eOnePlus) (codeHom 2652785) := by
  rw [← codeHom_24606]
  have hne : (24606 : ℕ) ≠ 2652785 := by norm_num
  refine ⟨fun e => ?_, fun h => bWcode_q₁_q₂ ((adj_codeVert_iff contains_24606
    contains_2652785 hne).1 h)⟩
  have e' := codeVertPi_ne contains_24606 contains_2652785 hne
  apply e'
  congr 1
  exact Subtype.ext e

theorem exists_transport :
    ∃ s : Shat,
    cvMul cv0 s = cv0 ∧ cvMul (sigVert eOne) s = cw0 ∧
    ∀ v ∈ cSigma 1, cvMul v s ∈ cSigma 1 := by
  have h1 : cQ ∈ cOrbit := mem_cOrbit_iff.2 ⟨0, by decide, by rw [Psi_zero', mul_one]⟩
  have h2 : cQ * Psi eOne ∈ cOrbit := mem_cOrbit_iff.2 ⟨eOne, qPoly_eOne, rfl⟩
  have h4 : cQ * xhat ∈ cOrbit :=
    mem_cOrbit_iff.2 ⟨Pi.single 0 1, qPoly_e0, by rw [Psi_single]; rfl⟩
  have h12 : cQ ≠ cQ * Psi eOne := by
    intro e
    have e' := cPsi_injective (show cQ * Psi 0 = cQ * Psi eOne by rw [Psi_zero', mul_one]; exact e)
    exact absurd e' (by decide)
  have h34 : cQ ≠ cQ * xhat := by
    intro e
    have e' : cQ * Psi 0 = cQ * Psi (Pi.single 0 1) := by
      rw [Psi_zero', mul_one, Psi_single]
      exact e
    exact absurd (cPsi_injective e') (by decide)
  obtain ⟨x, hx, hx1, hx2⟩ := cOrbit_two_transitive h1 h2 h1 h4 h12 h34
  refine ⟨⟨x⁻¹, Xgrp_le_Shat (Xgrp.inv_mem hx)⟩, ?_, ?_, ?_⟩
  · refine clabel_injective_native ?_
    rw [clabel_cvMul, clabel_cv0]
    simpa only [inv_inv] using hx1
  · refine clabel_injective_native ?_
    rw [clabel_cvMul, clabel_sigVert qPoly_eOne, clabel_cw0]
    simpa only [inv_inv] using hx2
  · intro v hv
    obtain ⟨y, hy, rfl⟩ := mem_cSigma_one.1 hv
    exact mem_cSigma_one.2 ⟨_, Xgrp.mul_mem hy (Xgrp.inv_mem hx), cvMul_cvOf _ _⟩

theorem bt2C1 :
    BT2C1 := by
  let _ : MulAction Shat CVert := cvLeftAction
  have hsmul : ∀ (g : Shat) (v : CVert), g • v = cvMul v g⁻¹ := fun _ _ => rfl
  have hadj : ∀ (g : Shat) {u w : CVert}, cgraph.Adj u w → cgraph.Adj (g • u) (g • w) :=
    fun g u w h => by rw [hsmul, hsmul]; exact (cgraph_adj_cvMul _ _ _).2 h
  have hT : ∀ (g : Shat) {u w z : CVert}, IsType1782 u w z →
      IsType1782 (g • u) (g • w) (g • z) := fun g u w z h => by
    rw [hsmul, hsmul, hsmul]
    exact isType1782_cvMul _ h
  have hA : ∀ g ∈ cEdgeFix, g • cv0 = cv0 ∧ g • cw0 = cw0 := by
    intro g hg
    rw [hsmul, hsmul]
    exact ⟨(cEdgeFix.inv_mem hg).1, (cEdgeFix.inv_mem hg).2⟩
  obtain ⟨s, hs0, hs1, hsS⟩ := exists_transport
  set b₀ := cvMul (sigVert eOnePlus) s with hb₀def
  set c₁ := cvMul (codeHom 2652785) s with hc₁def
  have hT0 : IsCTriangle cv0 (sigVert eOne) (sigVert eOnePlus) := isCTriangle_tStar
  have hq₂ : cgraph.Adj cv0 (codeHom 2652785) ∧ cgraph.Adj (sigVert eOne) (codeHom 2652785) := by
    refine ⟨?_, ?_⟩
    · rw [← codeHom_6144]
      exact codeHom.map_rel' codeAdj_q₂_σ.symm
    · rw [← codeHom_6175]
      exact codeHom.map_rel' codeAdj_w_q₂
  have hb₀adj : cgraph.Adj cw0 b₀ ∧ cgraph.Adj b₀ cv0 := by
    rw [← hs0, ← hs1]
    exact ⟨(cgraph_adj_cvMul _ _ _).2 hT0.2.2, (cgraph_adj_cvMul _ _ _).2 hT0.2.1.symm⟩
  have hc₁adj : cgraph.Adj cw0 c₁ ∧ cgraph.Adj c₁ cv0 := by
    rw [← hs0, ← hs1]
    exact ⟨(cgraph_adj_cvMul _ _ _).2 hq₂.2, (cgraph_adj_cvMul _ _ _).2 hq₂.1.symm⟩
  have hb₀bad : ¬ IsType1782 cv0 cw0 b₀ := by
    rw [← hs0, ← hs1, hb₀def, ← isType1782_cvMul_iff]
    exact not_isType1782_tStar
  have hbridge : TriRel cgraph IsType1782 cv0 cw0 b₀ c₁ := by
    have e := TriRel.map (cvIso s).toHom (fun u w z h => isType1782_cvMul s h) hT0.1 hT0.2.2
      hT0.2.1.symm hq₂.2 hq₂.1.symm triRel_tStar
    change TriRel cgraph IsType1782 (cvMul cv0 s) (cvMul (sigVert eOne) s)
      (cvMul (sigVert eOnePlus) s) (cvMul (codeHom 2652785) s) at e
    rwa [hs0, hs1] at e
  have hb₀S : b₀ ∈ cSigma 1 := hsS _ (sigVert_mem qPoly_eOnePlus)
  have htrans : ∀ b, cgraph.Adj cw0 b → cgraph.Adj b cv0 → ¬ IsType1782 cv0 cw0 b →
      ∃ g ∈ cEdgeFix, g • b₀ = b := by
    intro b hb1 hb0 hb
    obtain ⟨M, -⟩ := exists_rootModel cv0
    have t1 : triType cv0 cw0 b = 44352 :=
      (triType_eq_or M ⟨cgraph_adj_cv0_cw0, hb0.symm, hb1⟩).resolve_left
        fun h => hb ⟨⟨cgraph_adj_cv0_cw0, hb0.symm, hb1⟩, h⟩
    have t0 : triType cv0 cw0 b₀ = 44352 :=
      (triType_eq_or M ⟨cgraph_adj_cv0_cw0, hb₀adj.2.symm, hb₀adj.1⟩).resolve_left
        fun h => hb₀bad ⟨⟨cgraph_adj_cv0_cw0, hb₀adj.2.symm, hb₀adj.1⟩, h⟩
    obtain ⟨t, ht0, ht1, htb⟩ := exists_cvMul_eq_of_triType_eq cgraph_adj_cv0_cw0
      hb₀adj.2.symm hb0.symm (t0.trans t1.symm)
    refine ⟨t⁻¹, ⟨?_, ?_⟩, ?_⟩
    · exact (vStab cv0).inv_mem ht0
    · exact (vStab cw0).inv_mem ht1
    · rw [hsmul, inv_inv]
      exact htb
  let M : Subgroup Shat := cEdgeFix ⊓ (Pc 3).comap Shat.subtype
  have hMA : M ≤ cEdgeFix := inf_le_left
  have hS3 : ∀ g : Shat, (g : Dfull) ∈ Pc 3 → ∀ v ∈ cSigma 1, g • v ∈ cSigma 1 := by
    intro g hg v hv
    rw [hsmul]
    obtain ⟨y, hy, rfl⟩ := mem_cSigma_one.1 hv
    have hgX : ((g⁻¹ : Shat) : Dfull) ∈ Xgrp := by
      rw [Subgroup.coe_inv]
      rw [Pc_three] at hg
      exact Xgrp.inv_mem hg.1
    exact mem_cSigma_one.2 ⟨_, Xgrp.mul_mem hy hgX, cvMul_cvOf _ _⟩
  have hK1 : ∀ g ∈ M, TriRel cgraph IsType1782 cv0 cw0 b₀ (g • b₀) := by
    intro g hg
    have hgA := hA g hg.1
    have h1 := hadj g hb₀adj.1
    have h0 := hadj g hb₀adj.2
    rw [hgA.2] at h1
    rw [hgA.1] at h0
    have hbad : ¬ IsType1782 cv0 cw0 (g • b₀) := by
      intro h
      apply hb₀bad
      have e := hT g⁻¹ h
      rwa [inv_smul_smul, ← hgA.1, ← hgA.2, inv_smul_smul, inv_smul_smul] at e
    exact triRel_of_mem_cSigma hb₀S (hS3 g hg.2 b₀ hb₀S) hb₀adj.2.symm hb₀adj.1 hb₀bad
      h0.symm h1 hbad
  have hmax : ∀ g ∈ cEdgeFix, g • b₀ ∉ cSigma 1 → cEdgeFix ≤ M ⊔ Subgroup.zpowers g := by
    intro g hg hgS
    have hg3 : (g : Dfull) ∉ Pc 3 := fun h3 => hgS (hS3 g h3 b₀ hb₀S)
    exact cEdgeFix_le_of_not_mem_Pc_three (fun g' hg' h3 => Subgroup.mem_sup_left ⟨hg', h3⟩) hg
      hg3 (Subgroup.mem_sup_right (Subgroup.mem_zpowers g))
  have hS₀ : ∀ v ∈ cSigma 1, v ≠ b₀ → cgraph.Adj b₀ v :=
    fun v hv hne => cSigma_isClique hb₀S hv hne.symm
  have hne : b₀ ≠ c₁ := fun e => not_adj_tStar_q₂.1 (cvMul_injective s e)
  have hnadj : ¬ cgraph.Adj b₀ c₁ := fun h =>
    not_adj_tStar_q₂.2 ((cgraph_adj_cvMul _ _ s).1 h)
  by_cases hc₁ : IsType1782 cv0 cw0 c₁
  · exact edgeConst_of_bridge_good hadj hT cEdgeFix hA ⟨hb₀adj.1, hb₀adj.2⟩ htrans
      ⟨hc₁adj.1, hc₁adj.2, hc₁⟩ hbridge
  · exact edgeConst_of_bridge hadj hT cEdgeFix M hA hMA ⟨hb₀adj.1, hb₀adj.2, hb₀bad⟩ htrans
      (cSigma 1) hS₀ hK1 hmax ⟨hb₀adj.1, hb₀adj.2, hb₀bad⟩ ⟨hc₁adj.1, hc₁adj.2, hc₁⟩ hne hnadj
      hbridge

end CFSG.Monster.B.GSide
