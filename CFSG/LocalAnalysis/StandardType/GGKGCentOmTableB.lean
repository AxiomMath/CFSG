module

public import CFSG.LocalAnalysis.StandardType.GGKGCentOmMinus
public import CFSG.LocalAnalysis.StandardType.GGSecFiveKGPosDefs
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyDichotomy
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.TorusM8POmegaMinus
import CFSG.LocalAnalysis.StandardType.GGSixRootCentralizerBasic
import Mathlib.Tactic.Group

public section

namespace CFSG.StandardType.KGCentOmMinus

open CFSG.LieType.Universal CFSG.LieType.Universal.Spin CFSG.LieType.Universal.Spin.Twisted
  CFSG.LieType.RootSystem CFSG.ClassicalGroups.Orthogonal QuadraticMap
open scoped Matrix

theorem exists_toStdB_weylAction_short {m : ℕ} {l : Fin m} (hl : ¬ l.val + 1 < m)
    (v : (coxeterMatrix (isFiniteType_cartanB m)).Group) :
    ∃ (i : Fin m) (s : Bool),
      toStdB m (weylAction (isFiniteType_cartanB m) v (Pi.single l 1)) =
        Pi.single i (boolSign s) := by
  induction v using (coxeterMatrix (isFiniteType_cartanB m)).toCoxeterSystem.simple_induction_left
    with
  | one =>
    exact ⟨l, true, by rw [map_one, Module.End.one_apply, toStdB_single_of_not_lt m hl,
      boolSign_true]⟩
  | mul_simple_left w k ih =>
    obtain ⟨i, s, h⟩ := ih
    rw [weylAction_mul_apply, weylAction_simple, toStdB_reflection, h]
    by_cases hk : k.val + 1 < m
    · refine ⟨Equiv.swap k ⟨k.val + 1, hk⟩ i, s, ?_⟩
      rw [stdReflB_of_lt m hk]
      funext a
      simp only [Function.comp_apply, Pi.single_apply, Equiv.swap_apply_eq_iff]
    · refine ⟨i, if i = k then !s else s, ?_⟩
      rw [stdReflB_of_not_lt m hk]
      funext a
      by_cases ha : a = i
      · subst ha
        by_cases hak : a = k
        · simp [hak]
        · simp [hak]
      · simp [ha]

variable {F : Type} [Field F] {b c : F}

theorem twShortRoot_mem_ggRootLevi (n : ℕ) (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0)
    {γ : Fin (n - 1) → ℤ} {i : Fin (n - 1)} {s : Bool}
    (h : toStdB (n - 1) γ = Pi.single i (boolSign s)) (s' : Bool) (P : Fin 2 → F) :
    twShortRoot n hirr i s' (.ofAdd P) ∈
      CFSG.StandardType.ggRootLevi (minusDatum n hirr) γ := by
  by_cases hs : s' = s
  · subst hs
    exact Subgroup.mem_sup_left (twShortRoot_mem_minusRootGroup n hirr i s' h P)
  · have hs' : s' = !s := by cases s <;> cases s' <;> simp_all
    have h' : toStdB (n - 1) (-γ) = Pi.single i (boolSign s') := by
      rw [toStdB_neg, h, hs', boolSign_not, Pi.single_neg]
    exact Subgroup.mem_sup_right (twShortRoot_mem_minusRootGroup n hirr i s' h' P)

theorem spinAction_fix_of_commute_twShortRoot [Finite F] [CharP F 2] {n : ℕ}
    (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) (hF : ∃ c' : F, c' ≠ 0 ∧ c' ≠ 1)
    {h : spinGroup (quadMinus n F b c)} (i : Fin (n - 1))
    (hcomm : ∀ (s : Bool) (P : Fin 2 → F),
      h * twShortRoot n hirr i s (.ofAdd P) = twShortRoot n hirr i s (.ofAdd P) * h) :
    spinAction _ h (eVec n i) = eVec n i ∧ spinAction _ h (fVec n i) = fVec n i ∧
      ∀ P : Fin 2 → F, spinAction _ h (planeVec n P) = planeVec n P := by
  have hc : ∀ (s : Bool) (P : Fin 2 → F) (v : Vm n F),
      eichler (quadMinus n F b c) (minusVec n i s) (planeVec n P)
          (((spinMatrix (quadMinus n F b c) h : GL _ F) : Matrix _ _ F) *ᵥ
            (fun k => (RingEquiv.refl F) (v k))) =
        ((spinMatrix (quadMinus n F b c) h : GL _ F) : Matrix _ _ F) *ᵥ
          (fun k => (RingEquiv.refl F)
            (eichler (quadMinus n F b c) (minusVec n i s) (planeVec n P) v k)) := by
    intro s P v
    have e1 : (fun k => (RingEquiv.refl F) (v k)) = v := rfl
    have e2 : (fun k => (RingEquiv.refl F)
        (eichler (quadMinus n F b c) (minusVec n i s) (planeVec n P) v k)) =
        eichler (quadMinus n F b c) (minusVec n i s) (planeVec n P) v := rfl
    rw [e1, e2, spinMatrix_mulVec, spinMatrix_mulVec, ← spinAction_twShortRoot_eq_eichler n hirr]
    have h1 := congrArg (fun u => spinAction (quadMinus n F b c) u v) (hcomm s P)
    simpa only [map_mul, LinearEquiv.mul_apply] using h1.symm
  obtain ⟨-, ν, -, hAe, hAf, hAp⟩ :=
    semi_eq_smul_of_commute_eichler_short hirr hF (spinMatrix (quadMinus n F b c) h)
      (RingEquiv.refl F) i hc
  rw [spinMatrix_mulVec] at hAe hAf
  have hν : ν = 1 := by
    have hp := polar_spinAction (quadMinus n F b c) h (eVec n i) (fVec n i)
    rw [hAe, hAf, polar_smul_left, polar_smul_right, polar_eVec_fVec, if_pos rfl] at hp
    have h2 : ν ^ 2 = 1 ^ 2 := by rw [one_pow, pow_two]; simpa [smul_eq_mul] using hp
    exact CharTwo.sq_injective h2
  subst hν
  refine ⟨by rw [hAe, one_smul], by rw [hAf, one_smul], fun P => ?_⟩
  have := hAp P
  rwa [spinMatrix_mulVec, one_smul] at this


theorem exists_weylAction_short_at (i : Fin 3) :
    ∃ (w : (coxeterMatrix (isFiniteType_cartanB 3)).Group) (s : Bool),
      toStdB 3 (weylAction (isFiniteType_cartanB 3) w (Pi.single 2 1)) =
        Pi.single i (boolSign s) := by
  have h2 : toStdB 3 (Pi.single (2 : Fin 3) 1) = Pi.single 2 1 :=
    toStdB_single_of_not_lt 3 (k := 2) (by decide)
  have hs : ∀ k : Fin 3, weylAction (isFiniteType_cartanB 3)
      ((coxeterMatrix (isFiniteType_cartanB 3)).toCoxeterSystem.simple k) =
        reflection (cartanB 3) k := weylAction_simple _
  fin_cases i
  · refine ⟨(coxeterMatrix (isFiniteType_cartanB 3)).toCoxeterSystem.simple 0 *
      (coxeterMatrix (isFiniteType_cartanB 3)).toCoxeterSystem.simple 1, true, ?_⟩
    rw [weylAction_mul_apply, hs, hs, toStdB_reflection, toStdB_reflection, h2,
      stdReflB_of_lt 3 (k := 1) (by decide), stdReflB_of_lt 3 (k := 0) (by decide)]
    funext a
    fin_cases a <;> rfl
  · refine ⟨(coxeterMatrix (isFiniteType_cartanB 3)).toCoxeterSystem.simple 1, true, ?_⟩
    rw [hs, toStdB_reflection, h2, stdReflB_of_lt 3 (k := 1) (by decide)]
    funext a
    fin_cases a <;> rfl
  · refine ⟨1, true, ?_⟩
    rw [map_one, Module.End.one_apply, h2, boolSign_true]
    rfl

private theorem fin3_other (k : Fin 3) :
    ∃ i j : Fin 3, i ≠ k ∧ j ≠ k ∧ i ≠ j ∧ ∀ l, l ≠ k → l = i ∨ l = j := by
  fin_cases k
  · exact ⟨1, 2, by decide, by decide, by decide, by decide⟩
  · exact ⟨0, 2, by decide, by decide, by decide, by decide⟩
  · exact ⟨0, 1, by decide, by decide, by decide, by decide⟩

theorem eq_one_of_spinAction_fix [Finite F] [CharP F 2] {n : ℕ} (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0)
    {h : spinGroup (quadMinus n F b c)}
    (he : ∀ j, spinAction _ h (eVec n j) = eVec n j) (hf : ∀ j, spinAction _ h (fVec n j) = fVec n j)
    (hp : ∀ P : Fin 2 → F, spinAction _ h (planeVec n P) = planeVec n P) : h = 1 := by
  apply CFSG.LargeExtraspecial.A2Mod.FrB.spinAction_injective n hirr (CharP.cast_eq_zero F 2)
  rw [map_one]
  apply LinearEquiv.toLinearMap_injective
  apply (Pi.basisFun F (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2)).ext
  intro q
  rw [Pi.basisFun_apply]
  rcases q with j | j | t
  · exact he j
  · exact hf j
  · have hpl : planeVec n (Pi.single t (1 : F)) =
        Pi.single (Sum.inr (Sum.inr t) : Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) 1 := by
      funext q
      rcases q with j | j | s <;> simp [planeVec, Pi.single_apply]
    have := hp (Pi.single t 1)
    rw [hpl] at this
    exact this

theorem exists_torus_coord [Finite F] [CharP F 2] {G : Type} [Group G] [Finite G] {p : ℕ}
    (hp : p.Prime) {Bs Y : Subgroup G}
    (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) (hF : ∃ c' : F, c' ≠ 0 ∧ c' ≠ 1)
    (ψ : spinGroup (quadMinus 4 F b c) →* G) (hψ : Function.Injective ψ) (hrange : ψ.range = Y)
    (ε : (coxeterMatrix (isFiniteType_cartanB 3)).Group ≃* ↥(ggAutomizer Y Bs))
    (hεr : ∀ i : Fin 3, GGIsReflection p
      ((ε ((coxeterMatrix (isFiniteType_cartanB 3)).simple i) : ↥(ggAutomizer Y Bs)) :
        MulAut ↥Bs))
    (hlev : ∀ (w : (coxeterMatrix (isFiniteType_cartanB 3)).Group) (i : Fin 3),
      ggRankOneIn Y Bs
        ((ε (w * (coxeterMatrix (isFiniteType_cartanB 3)).simple i * w⁻¹) :
          ↥(ggAutomizer Y Bs)) : MulAut ↥Bs) =
        (ggRootLevi (minusDatum 4 hirr)
          (weylAction (isFiniteType_cartanB 3) w (Pi.single i 1))).map ψ)
    (hTor : ∀ x ∈ Bs, ∃ h ∈ ggTorus (minusDatum 4 hirr), ∀ z, x * ψ z * x⁻¹ = ψ (h * z * h⁻¹))
    (hrank : p ^ 3 * Nat.card ↥(Bs ⊓ Subgroup.centralizer (Y : Set G)) ≤ Nat.card ↥Bs) :
    ∀ k : Fin (4 - 1), ∃ x ∈ Bs, ∃ h : spinGroup (quadMinus 4 F b c), ∃ ζ : F,
      ζ ^ 2 ≠ 1 ∧ (∀ u, x⁻¹ * ψ u * x = ψ (h * u * h⁻¹)) ∧
      spinAction _ h (eVec 4 k) = ζ • eVec 4 k ∧ spinAction _ h (fVec 4 k) = ζ⁻¹ • fVec 4 k ∧
      (∀ j, j ≠ k → spinAction _ h (eVec 4 j) = eVec 4 j ∧
        spinAction _ h (fVec 4 j) = fVec 4 j) ∧
      ∀ P, spinAction _ h (planeVec 4 P) = planeVec 4 P := by
  intro k
  have hrefl : ∀ i : Fin 3, ∃ r : MulAut ↥Bs, GGIsReflection p r ∧
      ∀ x ∈ ggHyperplane Bs r, ∀ (s : Bool) (P : Fin 2 → F),
        x * ψ (twShortRoot 4 hirr i s (.ofAdd P)) = ψ (twShortRoot 4 hirr i s (.ofAdd P)) * x := by
    intro i
    obtain ⟨w, si, hw⟩ := exists_weylAction_short_at i
    refine ⟨((ε (w * (coxeterMatrix (isFiniteType_cartanB 3)).simple 2 * w⁻¹) :
      ↥(ggAutomizer Y Bs)) : MulAut ↥Bs), ?_, ?_⟩
    · rw [map_mul, map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
      exact GGIsReflection.conj' (hεr 2) _
    · intro x hx s P
      have hmem : ψ (twShortRoot 4 hirr i s (.ofAdd P)) ∈ ggRankOneIn Y Bs
          ((ε (w * (coxeterMatrix (isFiniteType_cartanB 3)).simple 2 * w⁻¹) :
            ↥(ggAutomizer Y Bs)) : MulAut ↥Bs) := by
        rw [hlev w 2]
        exact Subgroup.mem_map_of_mem ψ (twShortRoot_mem_ggRootLevi 4 hirr hw s P)
      have hC := ((ggOTwoPrime_le _).trans inf_le_right) hmem
      exact Subgroup.mem_centralizer_iff.mp hC x hx
  obtain ⟨i, j, hik, hjk, hij, hcov⟩ := fin3_other k
  obtain ⟨ri, hri, hfi⟩ := hrefl i
  obtain ⟨rj, hrj, hfj⟩ := hrefl j
  obtain ⟨x, hxH, hxC⟩ : ∃ x ∈ ggHyperplane Bs ri ⊓ ggHyperplane Bs rj,
      x ∉ Bs ⊓ Subgroup.centralizer (Y : Set G) := by
    by_contra hne
    push Not at hne
    have hle : ggHyperplane Bs ri ⊓ ggHyperplane Bs rj ≤ Bs ⊓ Subgroup.centralizer (Y : Set G) :=
      fun x hx => hne x hx
    have hfix : ∀ r : MulAut ↥Bs, CFSG.StandardType.ggFixG Bs r = ggHyperplane Bs r := by
      intro r
      have h : CFSG.StandardType.ggFix r = MonoidHom.eqLocus (r : ↥Bs →* ↥Bs) (MonoidHom.id ↥Bs) := by
        ext; rfl
      rw [CFSG.StandardType.ggFixG, ggHyperplane, h]
    have hi := CFSG.StandardType.GGDichotomy.relIndex_ggFixG hri
    have hj := CFSG.StandardType.GGDichotomy.relIndex_ggFixG hrj
    rw [hfix] at hi hj
    have hinf : (ggHyperplane Bs ri ⊓ ggHyperplane Bs rj).relIndex Bs ≤
        (ggHyperplane Bs ri).relIndex Bs * (ggHyperplane Bs rj).relIndex Bs :=
      Subgroup.relIndex_inf_le
    rw [hi, hj] at hinf
    have hne0 : (ggHyperplane Bs ri ⊓ ggHyperplane Bs rj).relIndex Bs ≠ 0 := by
      show ((ggHyperplane Bs ri ⊓ ggHyperplane Bs rj).subgroupOf Bs).index ≠ 0
      exact Subgroup.FiniteIndex.index_ne_zero
    have hCle : (Bs ⊓ Subgroup.centralizer (Y : Set G)).relIndex Bs ≤
        (ggHyperplane Bs ri ⊓ ggHyperplane Bs rj).relIndex Bs :=
      Subgroup.relIndex_le_of_le_left hle hne0
    have hmul : (Bs ⊓ Subgroup.centralizer (Y : Set G)).relIndex Bs *
        Nat.card ↥((Bs ⊓ Subgroup.centralizer (Y : Set G)) ⊓ Bs) = Nat.card ↥Bs :=
      Subgroup.relIndex_mul_card _ _
    rw [show (Bs ⊓ Subgroup.centralizer (Y : Set G)) ⊓ Bs =
      Bs ⊓ Subgroup.centralizer (Y : Set G) from inf_le_left.antisymm (le_inf le_rfl inf_le_left)]
      at hmul
    have hpos : 0 < Nat.card ↥(Bs ⊓ Subgroup.centralizer (Y : Set G)) := Nat.card_pos
    have hp2 := hp.two_le
    have h1 : Nat.card ↥Bs ≤ p * p * Nat.card ↥(Bs ⊓ Subgroup.centralizer (Y : Set G)) := by
      rw [← hmul]
      exact Nat.mul_le_mul_right _ (hCle.trans hinf)
    have h2 : p * p * Nat.card ↥(Bs ⊓ Subgroup.centralizer (Y : Set G)) <
        p ^ 3 * Nat.card ↥(Bs ⊓ Subgroup.centralizer (Y : Set G)) := by
      apply Nat.mul_lt_mul_of_pos_right _ hpos
      calc p * p = p ^ 2 := by ring
        _ < p ^ 3 := Nat.pow_lt_pow_right hp.one_lt (by norm_num)
    omega
  have hxB : x ∈ Bs := (Subgroup.map_subtype_le _) (Subgroup.mem_inf.mp hxH).1
  have hxY : x ∉ Subgroup.centralizer (Y : Set G) := fun h => hxC ⟨hxB, h⟩
  obtain ⟨h, hhT, hh⟩ := hTor x hxB
  have hcomm : ∀ l ∈ ({i, j} : Set (Fin 3)), ∀ (s : Bool) (P : Fin 2 → F),
      h * twShortRoot 4 hirr l s (.ofAdd P) = twShortRoot 4 hirr l s (.ofAdd P) * h := by
    intro l hl s P
    have hx : x * ψ (twShortRoot 4 hirr l s (.ofAdd P)) * x⁻¹ =
        ψ (twShortRoot 4 hirr l s (.ofAdd P)) := by
      rcases hl with rfl | rfl
      · rw [hfi x (Subgroup.mem_inf.mp hxH).1 s P, mul_inv_cancel_right]
      · rw [hfj x (Subgroup.mem_inf.mp hxH).2 s P, mul_inv_cancel_right]
    rw [hh] at hx
    have := hψ hx
    calc h * twShortRoot 4 hirr l s (.ofAdd P)
        = h * twShortRoot 4 hirr l s (.ofAdd P) * h⁻¹ * h := by group
      _ = twShortRoot 4 hirr l s (.ofAdd P) * h := by rw [this]
  obtain ⟨hei, hfi', hpl⟩ := spinAction_fix_of_commute_twShortRoot (n := 4) hirr hF i (hcomm i (by simp))
  obtain ⟨hej, hfj', -⟩ := spinAction_fix_of_commute_twShortRoot (n := 4) hirr hF j (hcomm j (by simp))
  obtain ⟨μ, hμ⟩ := ClassicalPosition.exists_spinAction_minusVec_eq_smul_POmegaMinus 4 hirr hhT
    le_rfl k true
  obtain ⟨μ', hμ'⟩ := ClassicalPosition.exists_spinAction_minusVec_eq_smul_POmegaMinus 4 hirr hhT
    le_rfl k false
  rw [minusVec_true] at hμ
  rw [minusVec_false] at hμ'
  have hμμ : μ * μ' = 1 := by
    have hp' := polar_spinAction (quadMinus 4 F b c) h (eVec 4 k) (fVec 4 k)
    rw [hμ, hμ', polar_smul_left, polar_smul_right, polar_eVec_fVec, if_pos rfl] at hp'
    simpa [smul_eq_mul, mul_comm] using hp'
  have hother : ∀ l, l ≠ k → spinAction _ h (eVec 4 l) = eVec 4 l ∧
      spinAction _ h (fVec 4 l) = fVec 4 l := by
    intro l hl
    rcases hcov l hl with rfl | rfl
    · exact ⟨hei, hfi'⟩
    · exact ⟨hej, hfj'⟩
  have hμ1 : μ ≠ 1 := by
    rintro rfl
    have hμ'1 : μ' = 1 := by rwa [one_mul] at hμμ
    apply hxY
    have h1 : h = 1 := by
      refine eq_one_of_spinAction_fix (n := 4) hirr (fun l => ?_) (fun l => ?_) hpl
      · by_cases hl : l = k
        · subst hl; rw [hμ, one_smul]
        · exact (hother l hl).1
      · by_cases hl : l = k
        · subst hl; rw [hμ', hμ'1, one_smul]
        · exact (hother l hl).2
    rw [← hrange, Subgroup.mem_centralizer_iff]
    rintro _ ⟨z, rfl⟩
    have := hh z
    rw [h1, one_mul, inv_one, mul_one] at this
    calc ψ z * x = x * ψ z * x⁻¹ * x := by rw [this]
      _ = x * ψ z := by group
  refine ⟨x⁻¹, inv_mem hxB, h, μ, ?_, ?_, hμ, ?_, hother, hpl⟩
  · intro h2
    apply hμ1
    exact CharTwo.sq_injective (by simpa using h2)
  · intro u
    rw [inv_inv, hh u]
  · rw [hμ', eq_inv_of_mul_eq_one_right hμμ]


theorem mem_centralizer_of_tableBPos_short [Finite F] [CharP F 2] {f : ℕ} (hf : 1 ≤ f)
    (hcard : Nat.card F = 2 ^ f) (hF : ∃ c' : F, c' ≠ 0 ∧ c' ≠ 1)
    {G : Type} [Group G] [Finite G] {p : ℕ} (hp : p.Prime) {Bs Y : Subgroup G}
    (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0)
    (ψ : spinGroup (quadMinus 4 F b c) →* G) (hψ : Function.Injective ψ) (hrange : ψ.range = Y)
    (ε : (coxeterMatrix (isFiniteType_cartanB 3)).Group ≃* ↥(ggAutomizer Y Bs))
    (hεr : ∀ i : Fin 3, GGIsReflection p
      ((ε ((coxeterMatrix (isFiniteType_cartanB 3)).simple i) : ↥(ggAutomizer Y Bs)) :
        MulAut ↥Bs))
    (hlev : ∀ (w : (coxeterMatrix (isFiniteType_cartanB 3)).Group) (i : Fin 3),
      ggRankOneIn Y Bs
        ((ε (w * (coxeterMatrix (isFiniteType_cartanB 3)).simple i * w⁻¹) :
          ↥(ggAutomizer Y Bs)) : MulAut ↥Bs) =
        (ggRootLevi (minusDatum 4 hirr)
          (weylAction (isFiniteType_cartanB 3) w (Pi.single i 1))).map ψ)
    (hTor : ∀ x ∈ Bs, ∃ h ∈ ggTorus (minusDatum 4 hirr), ∀ z, x * ψ z * x⁻¹ = ψ (h * z * h⁻¹))
    (hrank : p ^ 3 * Nat.card ↥(Bs ⊓ Subgroup.centralizer (Y : Set G)) ≤ Nat.card ↥Bs)
    {t : G} (m : ℕ) (ht2 : t ^ (2 ^ m) = 1) (htB : ∀ x ∈ Bs, t * x = x * t)
    (htN : t ∈ Subgroup.normalizer (Y : Set G)) (v : (coxeterMatrix (isFiniteType_cartanB 3)).Group)
    (hcent : ∀ z ∈ ggRankOneIn Y Bs
      ((ε (v * (coxeterMatrix (isFiniteType_cartanB 3)).simple 2 * v⁻¹) :
        ↥(ggAutomizer Y Bs)) : MulAut ↥Bs), t * z = z * t) :
    t ∈ Subgroup.centralizer (Y : Set G) := by
  obtain ⟨i, s, hv⟩ := exists_toStdB_weylAction_short (m := 3) (l := 2) (by decide) v
  have hshort : ∀ (s' : Bool) (P : Fin 2 → F),
      t * ψ (twShortRoot 4 hirr i s' (.ofAdd P)) * t⁻¹ = ψ (twShortRoot 4 hirr i s' (.ofAdd P)) := by
    intro s' P
    have hmem : ψ (twShortRoot 4 hirr i s' (.ofAdd P)) ∈ ggRankOneIn Y Bs
        ((ε (v * (coxeterMatrix (isFiniteType_cartanB 3)).simple 2 * v⁻¹) :
          ↥(ggAutomizer Y Bs)) : MulAut ↥Bs) := by
      rw [hlev v 2]
      exact Subgroup.mem_map_of_mem ψ (twShortRoot_mem_ggRootLevi 4 hirr hv s' P)
    rw [hcent _ hmem, mul_inv_cancel_right]
  have htN' : t ∈ Subgroup.normalizer (ψ.range : Set G) := by rw [hrange]; exact htN
  have h := mem_centralizer_of_shortLevi_of_torus (n := 4) le_rfl hirr hF hf hcard ψ hψ Bs m ht2
    htB htN' i hshort (exists_torus_coord hp hirr hF ψ hψ hrange ε hεr hlev hTor hrank)
  rwa [hrange] at h

end CFSG.StandardType.KGCentOmMinus

end
