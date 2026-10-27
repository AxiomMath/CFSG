module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixI.proposition_1
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.Basic
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_3
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_4_b
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_5

namespace CFSG
end CFSG
open CFSG

/-!
# Chapter I, Section 2, Proposition 3: Appendix I input
-/

namespace CFSG.BenderSuzuki
namespace PFchapter1section2

open PFchapter1section1 PFAppendixIII

/-- The canonical Section 2 subgroup `W`, defined before `K` is known to be a
subgroup, has the centralizer description used in the proof of Proposition 2. -/
public theorem peterfalvi_chapter1_section2_canonical_W_eq_D_centralizer_involutions
    {G Ω : Type*} [Group G] [Finite G] [MulAction G Ω] [Finite Ω]
    (H D Q V W : Subgroup G) (t : G)
    (hA1 : HypothesisA1 G Ω H D Q t)
    (hV_eq : V = peterfalviV D t)
    (hW_eq : W = peterfalviW V (peterfalviKSet D t)) :
    W = D ⊓ Subgroup.centralizer ({x : G | x ∈ H ∧ IsInvolution x}) := by
  classical
  obtain ⟨p, hp, _hpuniq⟩ :=
    _root_.CFSG.BenderSuzuki.PFchapter1section1.proposition_4_b H D Q t hA1
  let s : G := p.1
  have hsStructure : ∃ r : G, r ∈ Q ∧ t * s * t = r⁻¹ * t * r :=
    ⟨p.2, hp.2.2.1, hp.2.2.2⟩
  have hW :=
    (_root_.CFSG.BenderSuzuki.PFchapter1section1.proposition_5 H D Q t s hA1
      hp.1 hp.2.1 hsStructure).2
  calc
    W = peterfalviW V (peterfalviKSet D t) := hW_eq
    _ = peterfalviW (peterfalviV D t) (peterfalviKSet D t) := by rw [hV_eq]
    _ = D ⊓ Subgroup.centralizer ({x : G | x ∈ H ∧ IsInvolution x}) := hW

/-- The canonical `W` is normal in `D`.  This does not require the anti-fixed
set to have been packaged as a subgroup. -/
public theorem peterfalvi_chapter1_section2_canonical_W_normal_D
    {G Ω : Type*} [Group G] [Finite G] [MulAction G Ω] [Finite Ω]
    (H D Q V W : Subgroup G) (t : G)
    (hA1 : HypothesisA1 G Ω H D Q t)
    (hV_eq : V = peterfalviV D t)
    (hW_eq : W = peterfalviW V (peterfalviKSet D t)) :
    (W.subgroupOf D).Normal := by
  classical
  let Iset : Set G := {x : G | x ∈ H ∧ IsInvolution x}
  have hW_eq_centralizer : W = D ⊓ Subgroup.centralizer Iset := by
    simpa [Iset] using
      peterfalvi_chapter1_section2_canonical_W_eq_D_centralizer_involutions
        H D Q V W t hA1 hV_eq hW_eq
  have hWleD : W ≤ D := by
    rw [hW_eq_centralizer]
    exact inf_le_left
  rw [Subgroup.normal_subgroupOf_iff hWleD]
  intro x d hxW hdD
  rw [hW_eq_centralizer] at hxW ⊢
  refine ⟨D.mul_mem (D.mul_mem hdD hxW.1) (D.inv_mem hdD), ?_⟩
  change d * x * d⁻¹ ∈ Subgroup.centralizer Iset
  rw [Subgroup.mem_centralizer_iff]
  intro y hyI
  have hdyH : rightConjugateElem y d ∈ Iset := by
    refine ⟨?_, isInvolution_rightConjugateElem hyI.2⟩
    exact H.mul_mem
      (H.mul_mem (H.inv_mem (hA1.D_le_H hdD)) hyI.1)
      (hA1.D_le_H hdD)
  have hcomm : rightConjugateElem y d * x = x * rightConjugateElem y d :=
    (Subgroup.mem_centralizer_iff.mp hxW.2) (rightConjugateElem y d) hdyH
  calc
    y * (d * x * d⁻¹) = d * (rightConjugateElem y d * x) * d⁻¹ := by
      simp [rightConjugateElem, mul_assoc]
    _ = d * (x * rightConjugateElem y d) * d⁻¹ := by rw [hcomm]
    _ = (d * x * d⁻¹) * y := by simp [rightConjugateElem, mul_assoc]

/-- Conjugation by `D/W` on `Q0`, with its representative formula.  The
centralizer description of `W` proves both well-definedness and faithfulness. -/
public theorem peterfalvi_chapter1_section2_canonical_quotient_conjugation_action
    {G : Type*} [Group G]
    (H D W Q0 : Subgroup G)
    (hDleH : D ≤ H)
    (hQ0_def : ∀ x : G, x ∈ Q0 ↔ x = 1 ∨ (x ∈ H ∧ IsInvolution x))
    (hW_eq :
      W = D ⊓ Subgroup.centralizer ({x : G | x ∈ H ∧ IsInvolution x}))
    (hWD : (W.subgroupOf D).Normal) :
    letI : (W.subgroupOf D).Normal := hWD
    ∃ rhoD : (D ⧸ W.subgroupOf D) →* MulAut Q0,
      Function.Injective rhoD ∧
        ∀ d : D, ∀ q : Q0,
          rhoD (QuotientGroup.mk d) q =
            ⟨rightConjugateElem (q : G) (d : G)⁻¹, by
              rw [hQ0_def]
              rcases (hQ0_def (q : G)).mp q.property with hq_one | hq
              · left
                simp [hq_one, rightConjugateElem]
              · right
                have hdH : (d : G) ∈ H := hDleH d.property
                refine ⟨?_, by
                  simpa [rightConjugateElem] using
                    (isInvolution_rightConjugateElem (g := (d : G)⁻¹) hq.2)⟩
                simpa [rightConjugateElem] using
                  H.mul_mem (H.mul_mem hdH hq.1) (H.inv_mem hdH)⟩ := by
  classical
  letI : (W.subgroupOf D).Normal := hWD
  have hclosed :
      ∀ d : G, d ∈ D → ∀ q : G, q ∈ Q0 → d * q * d⁻¹ ∈ Q0 := by
    intro d hdD q hqQ0
    apply (hQ0_def _).mpr
    rcases (hQ0_def q).mp hqQ0 with hq_one | hq
    · left
      simp [hq_one]
    · right
      have hdH : d ∈ H := hDleH hdD
      refine ⟨H.mul_mem (H.mul_mem hdH hq.1) (H.inv_mem hdH), ?_⟩
      simpa [rightConjugateElem] using
        (isInvolution_rightConjugateElem (g := d⁻¹) hq.2)
  have hDnorm : D ≤ Subgroup.normalizer (Q0 : Set G) := by
    intro d hdD
    rw [Subgroup.mem_normalizer_iff]
    intro q
    constructor
    · exact hclosed d hdD q
    · intro hq
      have hback := hclosed d⁻¹ (D.inv_mem hdD) (d * q * d⁻¹) hq
      simpa [mul_assoc] using hback
  letI : Subgroup.Normalizes D Q0 := ⟨hDnorm⟩
  let conjHom : D →* MulAut Q0 := MulDistribMulAction.toMulAut D Q0
  have hWker : W.subgroupOf D ≤ conjHom.ker := by
    intro w hwW
    change conjHom w = 1
    apply MulEquiv.ext
    intro q
    apply Subtype.ext
    change (w : G) * (q : G) * (w : G)⁻¹ = (q : G)
    have hwW' : (w : G) ∈ W := hwW
    rw [hW_eq] at hwW'
    rcases (hQ0_def (q : G)).mp q.property with hq_one | hq
    · simp [hq_one]
    · have hcomm : (w : G) * (q : G) = (q : G) * (w : G) :=
        ((Subgroup.mem_centralizer_iff.mp hwW'.2) (q : G) hq).symm
      rw [hcomm]
      simp
  have hker_le : conjHom.ker ≤ W.subgroupOf D := by
    intro d hd
    have hdInv : d⁻¹ ∈ conjHom.ker := conjHom.ker.inv_mem hd
    have hfix : ∀ x : G, x ∈ Q0 → rightConjugateElem x (d : G) = x := by
      intro x hxQ0
      let q : Q0 := ⟨x, hxQ0⟩
      have heq : conjHom d⁻¹ q = q := by
        have h := MonoidHom.mem_ker.mp hdInv
        exact congrArg (fun f : MulAut Q0 => f q) h
      have hcoe := congrArg Subtype.val heq
      simpa [conjHom, q, rightConjugateElem] using hcoe
    have hdW : (d : G) ∈ W := by
      rw [hW_eq]
      refine ⟨d.property, ?_⟩
      change (d : G) ∈
        Subgroup.centralizer ({x : G | x ∈ H ∧ IsInvolution x})
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      have hxQ0 : x ∈ Q0 := (hQ0_def x).mpr (Or.inr hx)
      have hxd := hfix x hxQ0
      calc
        x * (d : G) = (d : G) * rightConjugateElem x (d : G) := by
          simp [rightConjugateElem, mul_assoc]
        _ = (d : G) * x := by rw [hxd]
    exact hdW
  have hker : conjHom.ker = W.subgroupOf D := le_antisymm hker_le hWker
  let rhoD : (D ⧸ W.subgroupOf D) →* MulAut Q0 :=
    QuotientGroup.lift (W.subgroupOf D) conjHom hWker
  have hrho_ker : rhoD.ker = ⊥ := by
    change (QuotientGroup.lift (W.subgroupOf D) conjHom hWker).ker = ⊥
    rw [QuotientGroup.ker_lift, hker, QuotientGroup.map_mk'_self]
  refine ⟨rhoD, (MonoidHom.ker_eq_bot_iff rhoD).mp hrho_ker, ?_⟩
  intro d q
  change
    (QuotientGroup.lift (W.subgroupOf D) conjHom hWker)
      (QuotientGroup.mk d) q = _
  rw [QuotientGroup.lift_mk]
  apply Subtype.ext
  simp [conjHom, rightConjugateElem,
    Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe]

/-- The canonical `D/W` action is transitive on the nonidentity elements of
`Q0`; Section 1 Proposition 3 supplies the required element directly in `D`. -/
public theorem peterfalvi_chapter1_section2_canonical_quotient_transitive_on_Q0_nontrivial
    {G Ω : Type*} [Group G] [Finite G] [MulAction G Ω] [Finite Ω]
    (H D Q W Q0 : Subgroup G) (t : G)
    (hA1 : HypothesisA1 G Ω H D Q t)
    (hQ0_def : ∀ x : G, x ∈ Q0 ↔ x = 1 ∨ (x ∈ H ∧ IsInvolution x))
    (hWD : (W.subgroupOf D).Normal)
    (rhoD : (D ⧸ W.subgroupOf D) →* MulAut Q0)
    (hrhoD_coe : ∀ d : D, ∀ q : Q0,
      ((rhoD (QuotientGroup.mk d) q : Q0) : G) =
        rightConjugateElem (q : G) (d : G)⁻¹) :
    letI : (W.subgroupOf D).Normal := hWD
    letI : MulDistribMulAction (D ⧸ W.subgroupOf D) Q0 :=
      MulDistribMulAction.compHom Q0 rhoD
    ∀ x : Q0, x ≠ 1 → ∀ y : Q0, y ≠ 1 →
      ∃ d : D ⧸ W.subgroupOf D, d • x = y := by
  classical
  letI : (W.subgroupOf D).Normal := hWD
  letI : MulDistribMulAction (D ⧸ W.subgroupOf D) Q0 :=
    MulDistribMulAction.compHom Q0 rhoD
  intro x hx y hy
  have hxG : (x : G) ≠ 1 := fun h => hx (Subtype.ext h)
  have hyG : (y : G) ≠ 1 := fun h => hy (Subtype.ext h)
  have hxHI : (x : G) ∈ H ∧ IsInvolution (x : G) := by
    rcases (hQ0_def (x : G)).mp x.property with hx1 | hxHI
    · exact False.elim (hxG hx1)
    · exact hxHI
  have hyHI : (y : G) ∈ H ∧ IsInvolution (y : G) := by
    rcases (hQ0_def (y : G)).mp y.property with hy1 | hyHI
    · exact False.elim (hyG hy1)
    · exact hyHI
  rcases
      ((PFchapter1section1.proposition_3 H D Q t hA1).2
        (x : G) hxHI.1 hxHI.2 (y : G)).mp hyHI with
    ⟨k, hkD, hconj⟩
  let d : D := ⟨k⁻¹, D.inv_mem hkD.1⟩
  refine ⟨QuotientGroup.mk d, ?_⟩
  change rhoD (QuotientGroup.mk d) x = y
  apply Subtype.ext
  rw [hrhoD_coe d x]
  simpa [d] using hconj

/-- First sentence of the Proposition 3 proof, preliminary containment:
`KW` lies in `D`, so the quotient subgroup `KW/W` can be formed inside `D/W`
once the normality of `W` is available. -/
public theorem peterfalvi_chapter1_section2_proposition_3_appendixI_input_KW_le_D
    {G : Type*} [Group G]
    (D K V W : Subgroup G)
    (hKleD : K ≤ D)
    (hWleV : W ≤ V)
    (hVleD : V ≤ D) :
    K ⊔ W ≤ D := by
  exact sup_le hKleD (hWleV.trans hVleD)

/-- First sentence of the Proposition 3 proof, Section 1 Proposition 5
specialization: `W` is `D` intersected with the centralizer of all involutions
of `H`. This is the exact local use of Section 1, Proposition 5. -/
public theorem peterfalvi_chapter1_section2_proposition_3_appendixI_input_W_eq_D_centralizer_involutions
    {G Ω : Type*} [Group G] [Finite G] [MulAction G Ω] [Finite Ω]
    (H D Q K V W : Subgroup G) (t : G)
    (hA1 : HypothesisA1 G Ω H D Q t)
    (hK_def : ∀ x : G, x ∈ K ↔ x ∈ D ∧ rightConjugateElem x t = x⁻¹)
    (hV_eq : V = peterfalviV D t)
    (hW_eq : W = peterfalviW V (K : Set G)) :
    W = D ⊓ Subgroup.centralizer ({x : G | x ∈ H ∧ IsInvolution x}) := by
  classical
  obtain ⟨p, hp, _hpuniq⟩ := _root_.CFSG.BenderSuzuki.PFchapter1section1.proposition_4_b H D Q t hA1
  let s : G := p.1
  have hsH : s ∈ H := hp.1
  have hsI : IsInvolution s := hp.2.1
  have hsStructure : ∃ r : G, r ∈ Q ∧ t * s * t = r⁻¹ * t * r :=
    ⟨p.2, hp.2.2.1, hp.2.2.2⟩
  have hW :=
    (_root_.CFSG.BenderSuzuki.PFchapter1section1.proposition_5 H D Q t s hA1
      hsH hsI hsStructure).2
  calc
    W = peterfalviW V (K : Set G) := hW_eq
    _ = peterfalviW (peterfalviV D t) (K : Set G) := by rw [hV_eq]
    _ = peterfalviW (peterfalviV D t) (peterfalviKSet D t) := by
      congr 1
      ext x
      simp [peterfalviKSet, hK_def]
    _ = D ⊓ Subgroup.centralizer ({x : G | x ∈ H ∧ IsInvolution x}) := hW

/-- First sentence of the Proposition 3 proof: the preceding Section 1
centralizer description makes `W` normal in `D`. -/
public theorem peterfalvi_chapter1_section2_proposition_3_appendixI_input_W_normal_D
    {G Ω : Type*} [Group G] [Finite G] [MulAction G Ω] [Finite Ω]
    (H D Q K V W : Subgroup G) (t : G)
    (hA1 : HypothesisA1 G Ω H D Q t)
    (hK_def : ∀ x : G, x ∈ K ↔ x ∈ D ∧ rightConjugateElem x t = x⁻¹)
    (hV_eq : V = peterfalviV D t)
    (hWleV : W ≤ V)
    (hW_eq : W = peterfalviW V (K : Set G))
    (hVleD : V ≤ D) :
    (W.subgroupOf D).Normal := by
  classical
  let Iset : Set G := {x : G | x ∈ H ∧ IsInvolution x}
  have hW_eq_centralizer : W = D ⊓ Subgroup.centralizer Iset := by
    simpa [Iset] using
      peterfalvi_chapter1_section2_proposition_3_appendixI_input_W_eq_D_centralizer_involutions
        H D Q K V W t hA1 hK_def hV_eq hW_eq
  have hWleD : W ≤ D := hWleV.trans hVleD
  rw [Subgroup.normal_subgroupOf_iff hWleD]
  intro x d hxW hdD
  rw [hW_eq_centralizer] at hxW ⊢
  refine ⟨D.mul_mem (D.mul_mem hdD hxW.1) (D.inv_mem hdD), ?_⟩
  change d * x * d⁻¹ ∈ Subgroup.centralizer Iset
  rw [Subgroup.mem_centralizer_iff]
  intro y hyI
  have hdyH : rightConjugateElem y d ∈ Iset := by
    refine ⟨?_, isInvolution_rightConjugateElem hyI.2⟩
    exact
      H.mul_mem
        (H.mul_mem (H.inv_mem (hA1.D_le_H hdD)) hyI.1)
        (hA1.D_le_H hdD)
  have hcomm : rightConjugateElem y d * x = x * rightConjugateElem y d :=
    (Subgroup.mem_centralizer_iff.mp hxW.2) (rightConjugateElem y d) hdyH
  calc
    y * (d * x * d⁻¹) = d * (rightConjugateElem y d * x) * d⁻¹ := by
      simp [rightConjugateElem, mul_assoc]
    _ = d * (x * rightConjugateElem y d) * d⁻¹ := by
      rw [hcomm]
    _ = (d * x * d⁻¹) * y := by
      simp [rightConjugateElem, mul_assoc]

/-- First sentence of the Proposition 3 proof, faithful-action input for
Appendix I, Proposition 2: by Section 1, Proposition 5, an element of `D` that
centralizes every element of `Q0` is already in `W`; hence `D/W` acts faithfully
on `Q0`. -/
public theorem peterfalvi_chapter1_section2_proposition_3_appendixI_input_DmodW_faithful_on_Q0
    {G : Type*} [Group G]
    (H D W Q0 : Subgroup G)
    (hQ0_def : ∀ x : G, x ∈ Q0 ↔ x = 1 ∨ (x ∈ H ∧ IsInvolution x))
    (hW_eq_centralizer : W = D ⊓ Subgroup.centralizer ({x : G | x ∈ H ∧ IsInvolution x})) :
    ∀ d : D, (∀ x : G, x ∈ Q0 → rightConjugateElem x (d : G) = x) →
      (d : G) ∈ W := by
  classical
  intro d hfix
  let Iset : Set G := {x : G | x ∈ H ∧ IsInvolution x}
  have hW_eq : W = D ⊓ Subgroup.centralizer Iset := by
    simpa [Iset] using hW_eq_centralizer
  rw [hW_eq]
  refine ⟨d.property, ?_⟩
  change (d : G) ∈ Subgroup.centralizer Iset
  rw [Subgroup.mem_centralizer_iff]
  intro x hxI
  have hxQ0 : x ∈ Q0 := (hQ0_def x).mpr (Or.inr hxI)
  have hxd : rightConjugateElem x (d : G) = x := hfix x hxQ0
  calc
    x * (d : G) = (d : G) * rightConjugateElem x (d : G) := by
      simp [rightConjugateElem, mul_assoc]
    _ = (d : G) * x := by rw [hxd]

/-- First sentence of the Proposition 3 proof: the action on `Q0#` is
transitive. This is Section 1 Proposition 3, transported through the Section 2
definitions of `Q0` and `K`. -/
public theorem peterfalvi_chapter1_section2_proposition_3_appendixI_input_KW_transitive_Q0_nontrivial
    {G Ω : Type*} [Group G] [Finite G] [MulAction G Ω] [Finite Ω]
    (H D Q K W Q0 : Subgroup G) (t : G)
    (hA1 : HypothesisA1 G Ω H D Q t)
    (hK_def : ∀ x : G, x ∈ K ↔ x ∈ D ∧ rightConjugateElem x t = x⁻¹)
    (hQ0_def : ∀ x : G, x ∈ Q0 ↔ x = 1 ∨ (x ∈ H ∧ IsInvolution x)) :
    ∀ x : G, x ∈ Q0 → x ≠ 1 →
      ∀ y : G, y ∈ Q0 → y ≠ 1 →
        ∃ a : (K ⊔ W : Subgroup G), rightConjugateElem x (a : G) = y := by
  classical
  intro x hxQ0 hxne y hyQ0 hyne
  have hxHI : x ∈ H ∧ IsInvolution x := by
    rcases (hQ0_def x).mp hxQ0 with hx1 | hxHI
    · exact False.elim (hxne hx1)
    · exact hxHI
  have hyHI : y ∈ H ∧ IsInvolution y := by
    rcases (hQ0_def y).mp hyQ0 with hy1 | hyHI
    · exact False.elim (hyne hy1)
    · exact hyHI
  rcases ((PFchapter1section1.proposition_3 H D Q t hA1).2 x hxHI.1 hxHI.2 y).mp hyHI with
    ⟨k, hkKset, hconj⟩
  have hkK : k ∈ K := (hK_def k).mpr hkKset
  have hkKW : k ∈ K ⊔ W := (show K ≤ K ⊔ W from le_sup_left) hkK
  exact ⟨⟨k, hkKW⟩, hconj⟩

/-- First source-sentence quotient transfer: modulo `W`, the image of `KW`
agrees with the image of `K`. -/
public theorem peterfalvi_chapter1_section2_proposition_3_appendixI_input_KWmodW_eq_KmodW
    {G : Type*} [Group G]
    (D K V W : Subgroup G)
    (hKleD : K ≤ D)
    (hWleV : W ≤ V)
    (hVleD : V ≤ D)
    (hWnormalD : (W.subgroupOf D).Normal) :
    letI : (W.subgroupOf D).Normal := hWnormalD
    ((K ⊔ W).subgroupOf D).map (QuotientGroup.mk' (W.subgroupOf D)) =
      (K.subgroupOf D).map (QuotientGroup.mk' (W.subgroupOf D)) := by
  classical
  let N : Subgroup D := W.subgroupOf D
  letI : N.Normal := hWnormalD
  let π : D →* D ⧸ N := QuotientGroup.mk' N
  have hWleD : W ≤ D := hWleV.trans hVleD
  have hsubgroupOf_sup :
      (K ⊔ W).subgroupOf D = K.subgroupOf D ⊔ W.subgroupOf D := by
    exact Subgroup.subgroupOf_sup hKleD hWleD
  calc
    ((K ⊔ W).subgroupOf D).map (QuotientGroup.mk' (W.subgroupOf D)) =
        ((K ⊔ W).subgroupOf D).map π := rfl
    _ = (K.subgroupOf D ⊔ W.subgroupOf D).map π := by rw [hsubgroupOf_sup]
    _ = (K.subgroupOf D).map π ⊔ (W.subgroupOf D).map π := by rw [Subgroup.map_sup]
    _ = (K.subgroupOf D).map π ⊔ ⊥ := by
      rw [QuotientGroup.map_mk'_self (N := N)]
    _ = (K.subgroupOf D).map π := by simp
    _ = (K.subgroupOf D).map (QuotientGroup.mk' (W.subgroupOf D)) := rfl

/-- First source-sentence quotient transfer: Section 2 Proposition 2 cyclicity
of `K` makes `KW/W` cyclic. -/
public theorem peterfalvi_chapter1_section2_proposition_3_appendixI_input_KWmodW_cyclic_of_K_cyclic
    {G : Type*} [Group G]
    (D K V W : Subgroup G)
    (hKleD : K ≤ D)
    (hWleV : W ≤ V)
    (hVleD : V ≤ D)
    (hWnormalD : (W.subgroupOf D).Normal)
    (hKcyclic : IsCyclic K) :
    letI : (W.subgroupOf D).Normal := hWnormalD
    IsCyclic (((K ⊔ W).subgroupOf D).map
      (QuotientGroup.mk' (W.subgroupOf D))) := by
  classical
  let N : Subgroup D := W.subgroupOf D
  letI : N.Normal := hWnormalD
  let π : D →* D ⧸ N := QuotientGroup.mk' N
  have hKcyclic' : IsCyclic (K.subgroupOf D) := by
    have hKcyclic'' : IsCyclic K := by
      simpa [IsCyclic] using hKcyclic
    exact (Subgroup.subgroupOfEquivOfLe hKleD).isCyclic.mpr hKcyclic''
  have hKimage : IsCyclic ((K.subgroupOf D).map π) := by
    letI : IsCyclic (K.subgroupOf D) := hKcyclic'
    exact isCyclic_of_surjective (π.subgroupMap (K.subgroupOf D))
      (π.subgroupMap_surjective (K.subgroupOf D))
  have hKW_eq_K :=
    peterfalvi_chapter1_section2_proposition_3_appendixI_input_KWmodW_eq_KmodW
      D K V W hKleD hWleV hVleD hWnormalD
  rw [hKW_eq_K]
  exact hKimage

/-- First source-sentence quotient transfer: Section 2 Proposition 2 normality
of `K` in `D` makes `KW/W` normal in `D/W`. -/
public theorem peterfalvi_chapter1_section2_proposition_3_appendixI_input_KWmodW_normal_of_K_normal
    {G : Type*} [Group G]
    (D K V W : Subgroup G)
    (hKleD : K ≤ D)
    (hWleV : W ≤ V)
    (hVleD : V ≤ D)
    (hWnormalD : (W.subgroupOf D).Normal)
    (hKnormalD : (K.subgroupOf D).Normal) :
    letI : (W.subgroupOf D).Normal := hWnormalD
    (((K ⊔ W).subgroupOf D).map
      (QuotientGroup.mk' (W.subgroupOf D))).Normal := by
  classical
  let N : Subgroup D := W.subgroupOf D
  letI : N.Normal := hWnormalD
  let π : D →* D ⧸ N := QuotientGroup.mk' N
  have hKimage : ((K.subgroupOf D).map π).Normal :=
    Subgroup.Normal.map hKnormalD π (QuotientGroup.mk'_surjective N)
  have hKW_eq_K :=
    peterfalvi_chapter1_section2_proposition_3_appendixI_input_KWmodW_eq_KmodW
      D K V W hKleD hWleV hVleD hWnormalD
  rw [hKW_eq_K]
  exact hKimage

/-- The complete translation of the first sentence before Appendix I,
Proposition 2 is applied. The conclusion is deliberately written as explicit
facts, not as a bundled input structure. -/
public theorem peterfalvi_chapter1_section2_proposition_3_appendixI_input
    {G Ω : Type*} [Group G] [Finite G] [MulAction G Ω] [Finite Ω]
    (H D Q K V W Q0 : Subgroup G) (t : G)
    (hA1 : HypothesisA1 G Ω H D Q t)
    (hKleD : K ≤ D)
    (hK_def : ∀ x : G, x ∈ K ↔ x ∈ D ∧ rightConjugateElem x t = x⁻¹)
    (hV_eq : V = peterfalviV D t)
    (hWleV : W ≤ V)
    (hW_eq : W = peterfalviW V (K : Set G))
    (hQ0_def : ∀ x : G, x ∈ Q0 ↔ x = 1 ∨ (x ∈ H ∧ IsInvolution x))
    (hVleD : V ≤ D)
    (hKcyclic : IsCyclic K)
    (hKnormalD : (K.subgroupOf D).Normal) :
    ∃ hWnormalD : (W.subgroupOf D).Normal,
      (K ⊔ W ≤ D) ∧
        (letI : (W.subgroupOf D).Normal := hWnormalD;
          IsCyclic (((K ⊔ W).subgroupOf D).map
            (QuotientGroup.mk' (W.subgroupOf D)))) ∧
        (letI : (W.subgroupOf D).Normal := hWnormalD;
          (((K ⊔ W).subgroupOf D).map
            (QuotientGroup.mk' (W.subgroupOf D))).Normal) ∧
        (∀ d : D, (∀ x : G, x ∈ Q0 → rightConjugateElem x (d : G) = x) →
          (d : G) ∈ W) ∧
        (∀ x : G, x ∈ Q0 → x ≠ 1 →
          ∀ y : G, y ∈ Q0 → y ≠ 1 →
            ∃ a : (K ⊔ W : Subgroup G), rightConjugateElem x (a : G) = y) := by
  classical
  have hKWleD : K ⊔ W ≤ D :=
    peterfalvi_chapter1_section2_proposition_3_appendixI_input_KW_le_D D K V W hKleD hWleV hVleD
  have hWnormalD : (W.subgroupOf D).Normal :=
    peterfalvi_chapter1_section2_proposition_3_appendixI_input_W_normal_D
      H D Q K V W t hA1 hK_def hV_eq hWleV hW_eq hVleD
  have hW_eq_centralizer :
      W = D ⊓ Subgroup.centralizer ({x : G | x ∈ H ∧ IsInvolution x}) :=
    peterfalvi_chapter1_section2_proposition_3_appendixI_input_W_eq_D_centralizer_involutions
      H D Q K V W t hA1 hK_def hV_eq hW_eq
  refine ⟨hWnormalD, hKWleD, ?_, ?_, ?_, ?_⟩
  · simpa using
      peterfalvi_chapter1_section2_proposition_3_appendixI_input_KWmodW_cyclic_of_K_cyclic
        D K V W hKleD hWleV hVleD hWnormalD hKcyclic
  · simpa using
      peterfalvi_chapter1_section2_proposition_3_appendixI_input_KWmodW_normal_of_K_normal
        D K V W hKleD hWleV hVleD hWnormalD hKnormalD
  · exact peterfalvi_chapter1_section2_proposition_3_appendixI_input_DmodW_faithful_on_Q0
      H D W Q0 hQ0_def hW_eq_centralizer
  · exact peterfalvi_chapter1_section2_proposition_3_appendixI_input_KW_transitive_Q0_nontrivial
      H D Q K W Q0 t hA1 hK_def hQ0_def

/-- Proposition 3 proof, distinguished-coordinate sentence plus the Section 1
Proposition 5 input for Appendix I, Proposition 2(b): there is a distinguished
involution `s` in `Q0`, and Section 1, Proposition 5 identifies `V` with its
stabilizer in `D`. -/
public theorem peterfalvi_chapter1_section2_proposition_3_distinguished_involution
    {G Ω : Type*} [Group G] [Finite G] [MulAction G Ω] [Finite Ω]
    (H D Q V Q0 : Subgroup G) (t : G)
    (hA1 : HypothesisA1 G Ω H D Q t)
    (hV_eq : V = peterfalviV D t)
    (hQ0_def : ∀ x : G, x ∈ Q0 ↔ x = 1 ∨ (x ∈ H ∧ IsInvolution x)) :
    ∃ s : G, s ∈ H ∧ IsInvolution s ∧
      (∃ r : G, r ∈ Q ∧ t * s * t = r⁻¹ * t * r) ∧
        s ∈ Q0 ∧
          V = D ⊓ Subgroup.centralizer ({s} : Set G) ∧
            ∀ v : V, rightConjugateElem s (v : G) = s := by
  classical
  obtain ⟨p, hp, _hpuniq⟩ := _root_.CFSG.BenderSuzuki.PFchapter1section1.proposition_4_b H D Q t hA1
  let s : G := p.1
  have hsH : s ∈ H := hp.1
  have hsI : IsInvolution s := hp.2.1
  have hsStructure : ∃ r : G, r ∈ Q ∧ t * s * t = r⁻¹ * t * r :=
    ⟨p.2, hp.2.2.1, hp.2.2.2⟩
  have hsQ0 : s ∈ Q0 := (hQ0_def s).mpr (Or.inr ⟨hsH, hsI⟩)
  have hV_eq' :=
    (_root_.CFSG.BenderSuzuki.PFchapter1section1.proposition_5 H D Q t s hA1
      hsH hsI hsStructure).1
  refine ⟨s, hp.1, hp.2.1, ⟨p.2, hp.2.2.1, hp.2.2.2⟩, hsQ0, ?_, ?_⟩
  · calc
      V = peterfalviV D t := hV_eq
      _ = D ⊓ Subgroup.centralizer ({s} : Set G) := hV_eq'
  intro v
  have hvPeter : (v : G) ∈ peterfalviV D t := by
    rw [← hV_eq]
    exact v.property
  have hvDs : (v : G) ∈ D ⊓ Subgroup.centralizer ({s} : Set G) := by
    simpa [hV_eq'] using hvPeter
  have hcomm : (v : G) * s = s * (v : G) :=
    Subgroup.mem_centralizer_singleton_iff.mp hvDs.2
  calc
    rightConjugateElem s (v : G) = (v : G)⁻¹ * s * (v : G) := rfl
    _ = (v : G)⁻¹ * (s * (v : G)) := by rw [mul_assoc]
    _ = (v : G)⁻¹ * ((v : G) * s) := by rw [← hcomm]
    _ = ((v : G)⁻¹ * (v : G)) * s := by rw [← mul_assoc]
    _ = s := by simp

end PFchapter1section2
end CFSG.BenderSuzuki
