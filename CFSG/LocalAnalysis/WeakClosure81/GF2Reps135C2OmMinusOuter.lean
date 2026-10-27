module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2OmMinusData
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.SL2ModulesDensity
import CFSG.LieType.Steinberg.CentralExt.SpinMinusThree
import CFSG.LocalAnalysis.StandardType.GGOppositeRadicalOmegaMinusOpp
import CFSG.LocalAnalysis.RankThreeUC.GN15FFOPSL.Top.EndField
import CFSG.Blueprint.SourceClassicalTransport
import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
import CFSG.Monster.B.Fischer.Fi22Order
import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin.SmithCurtis CFSG.LieType.Universal.Spin CFSG.LieType.Universal.Spin.Twisted
open CFSG.QuasithinUnique.Setup.SL2Modules (EndRing)
open CFSG.StandardType.GGOppRadOmega
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_5.SmallO8mCurtis
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.RankThree.OrthogonalInvolutions
open scoped TensorProduct

variable {K : Type} [Field K] [Finite K] [CharP K 2] {b c : K}

private noncomputable instance ommOuter_invert :
    Invertible (quadMinus 4 K b c (planeVec 4 planeOne)) :=
  invertibleOfNonzero (by rw [quadMinus_planeVec]; simp [planeOne])

noncomputable def o8mPlaneRefl : Vm 4 K ≃ₗ[K] Vm 4 K :=
  TauCeti.QuadraticMap.reflection (quadMinus 4 K b c) (planeVec 4 planeOne)

omit [Finite K] [CharP K 2] in
theorem o8mPlaneRefl_eq_reflect :
    o8mPlaneRefl (b := b) (c := c) =
      CFSG.ClassicalGroups.Orthogonal.reflect (quadMinus 4 K b c) (planeVec 4 planeOne) :=
  CFSG.ClassicalGroups.Orthogonal.reflect_eq_reflection.symm

omit [Finite K] [CharP K 2] in
private theorem ommOuter_r0_mem :
    o8mPlaneRefl (b := b) (c := c) ∈ TauCeti.QuadraticMap.orthogonalGroup (quadMinus 4 K b c) :=
  TauCeti.QuadraticMap.reflection_mem_orthogonalGroup _ _

omit [Finite K] [CharP K 2] in
private theorem ommOuter_r0_eVec (i : Fin 3) :
    o8mPlaneRefl (b := b) (c := c) (eVec 4 i) = eVec 4 i := by
  rw [o8mPlaneRefl, TauCeti.QuadraticMap.reflection_apply_of_polar_eq_zero]
  exact polar_planeVec_eVec 4 b c planeOne i

omit [Finite K] [CharP K 2] in
private theorem ommOuter_r0_fVec (i : Fin 3) :
    o8mPlaneRefl (b := b) (c := c) (fVec 4 i) = fVec 4 i := by
  rw [o8mPlaneRefl, TauCeti.QuadraticMap.reflection_apply_of_polar_eq_zero]
  exact polar_planeVec_fVec 4 b c planeOne i

omit [Finite K] [CharP K 2] in
private theorem ommOuter_r0_planeVec (p : Fin 2 → K) :
    o8mPlaneRefl (b := b) (c := c) (planeVec 4 p) = planeVec 4 (planeRefl b c planeOne p) := by
  rw [o8mPlaneRefl, TauCeti.QuadraticMap.reflection_apply_eq_sub_div, quadMinus_planeVec',
    planeNorm_planeOne, div_one, polar_planeVec_planeVec, polarPlane_comm, planeRefl,
    planeNorm_planeOne, div_one, planeVec_sub, planeVec_smul]

variable (hirrQ : ∀ s : K, s ^ 2 + b * s + c ≠ 0)

noncomputable def o8mOuterAut : MulAut (spinGroup (quadMinus 4 K b c)) :=
  minusConj hirrQ (by norm_num) (ommOuter_r0_mem (b := b) (c := c))

theorem spinAction_o8mOuterAut (g : spinGroup (quadMinus 4 K b c)) :
    spinAction (quadMinus 4 K b c) (o8mOuterAut hirrQ g) =
      o8mPlaneRefl (b := b) (c := c) * spinAction (quadMinus 4 K b c) g *
        (o8mPlaneRefl (b := b) (c := c))⁻¹ :=
  spinAction_minusConj hirrQ (by norm_num) (ommOuter_r0_mem (b := b) (c := c)) g

variable {hirrQ}

private theorem ommOuter_c_twShortRoot (i : Fin 3) (s : Bool) (p : Fin 2 → K) :
    o8mOuterAut hirrQ (twShortRoot 4 hirrQ i s (.ofAdd p)) =
      twShortRoot 4 hirrQ i s (.ofAdd (planeRefl b c planeOne p)) := by
  apply CFSG.StandardType.RootCentOmega.spinAction_quadMinus_injective hirrQ
  rw [spinAction_o8mOuterAut hirrQ, spinAction_twShortRoot_eq_eichler,
    spinAction_twShortRoot_eq_eichler,
    CFSG.ClassicalGroups.Orthogonal.eichler_conj (ommOuter_r0_mem (b := b) (c := c))]
  congr 1
  · cases s
    · exact ommOuter_r0_fVec i
    · exact ommOuter_r0_eVec i
  · exact ommOuter_r0_planeVec (b := b) (c := c) p

private theorem ommOuter_c_longRoot (i j : Fin 3) (hij : i ≠ j) (s t : Bool) (a : K) :
    o8mOuterAut hirrQ ((minusFrame 4 b c).longRoot hij s t (.ofAdd a)) =
      (minusFrame 4 b c).longRoot hij s t (.ofAdd a) := by
  apply CFSG.StandardType.RootCentOmega.spinAction_quadMinus_injective hirrQ
  rw [spinAction_o8mOuterAut hirrQ, (minusFrame 4 b c).spinAction_longRoot_eq_eichler hij s t a,
    CFSG.ClassicalGroups.Orthogonal.eichler_conj (ommOuter_r0_mem (b := b) (c := c))]
  congr 1
  · cases t
    · exact ommOuter_r0_fVec j
    · exact ommOuter_r0_eVec j
  · rw [map_smul]
    congr 1
    cases s
    · exact ommOuter_r0_fVec i
    · exact ommOuter_r0_eVec i

private theorem ommOuter_eq_zero_or_one {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2)
    (x : K) : x = 0 ∨ x = 1 := by
  classical
  have : Fintype K := Fintype.ofFinite K
  have hcard : Fintype.card K = 2 := by rwa [Fintype.card_eq_nat_card]
  have huniv : ({0, 1} : Finset K) = Finset.univ := by
    apply Finset.eq_univ_of_card
    rw [hcard]; simp [zero_ne_one]
  have hx : x ∈ ({0, 1} : Finset K) := by rw [huniv]; exact Finset.mem_univ x
  simpa using hx

private theorem ommOuter_mul_self {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2) (x : K) :
    x * x = x := by
  rcases ommOuter_eq_zero_or_one hK x with h | h <;> simp [h]

private theorem ommOuter_negStar_eq_sq {K : Type} [Field K] [Finite K] [CharP K 2] {b c : K}
    (hirrQ : ∀ s : K, s ^ 2 + b * s + c ≠ 0) (hK : Nat.card K = 2) (t : ShortField b c) :
    CFSG.LieType.Steinberg.CentralExt.SpinMinusClosed.negStar t = t ^ 2 := by
  have hc : c = 1 := by
    rcases ommOuter_eq_zero_or_one hK c with h | h
    · exact absurd h (by simpa using hirrQ 0)
    · exact h
  have hb : b = 1 := by
    rcases ommOuter_eq_zero_or_one hK b with h | h
    · exfalso
      apply hirrQ 1
      rw [h, hc]
      simp only [pow_two, mul_one, add_zero]
      rw [one_add_one_eq_two]
      exact CharTwo.two_eq_zero
    · exact h
  ext <;>
    simp [CFSG.LieType.Steinberg.CentralExt.SpinMinusClosed.negStar, pow_two,
      QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul, hb, hc, ommOuter_mul_self hK,
      CharTwo.neg_eq, CharTwo.add_self_eq_zero, add_comm, mul_comm]

omit [Finite K] [CharP K 2] in
private theorem ommOuter_planeRefl_smul (r : K) (a p : Fin 2 → K) :
    planeRefl b c a (r • p) = r • planeRefl b c a p := by
  simp only [planeRefl, polarPlane_smul_left, smul_sub, smul_smul]
  module

omit [Finite K] [CharP K 2] in
private theorem ommOuter_planeNorm_planeRefl (a : Fin 2 → K) :
    planeNorm b c (planeRefl b c planeOne a) = planeNorm b c a := by
  have h := TauCeti.QuadraticMap.map_app_of_mem_orthogonalGroup
    (ommOuter_r0_mem (b := b) (c := c)) (planeVec 4 a)
  rw [ommOuter_r0_planeVec, quadMinus_planeVec', quadMinus_planeVec'] at h
  exact h

omit [Finite K] in
private theorem ommOuter_planeRefl_planeOne : planeRefl b c planeOne planeOne = planeOne := by
  simp [planeRefl, polarPlane_self, planeNorm_planeOne, CharTwo.two_eq_zero]

private theorem ommOuter_c_shortWeylElt (i : Fin 3) (a : Fin 2 → K) :
    o8mOuterAut hirrQ (shortWeylElt 4 hirrQ i a) =
      shortWeylElt 4 hirrQ i (planeRefl b c planeOne a) := by
  have hpos : shortPosHom 4 hirrQ i = twShortRoot 4 hirrQ i true := rfl
  have hneg : shortNegHom 4 hirrQ i = twShortRoot 4 hirrQ i false := rfl
  simp only [shortWeylElt, hpos, hneg, map_mul, ommOuter_c_twShortRoot, ommOuter_planeRefl_smul,
    ommOuter_planeNorm_planeRefl]

private theorem ommOuter_c_shortWeyl (i : Fin 3) :
    o8mOuterAut hirrQ (shortWeyl 4 hirrQ i) = shortWeyl 4 hirrQ i := by
  rw [shortWeyl, ommOuter_c_shortWeylElt, ommOuter_planeRefl_planeOne]

private theorem ommOuter_c_shortTorusElt (i : Fin 3) (a : Fin 2 → K) :
    o8mOuterAut hirrQ (shortTorusElt 4 hirrQ i a) =
      shortTorusElt 4 hirrQ i (planeRefl b c planeOne a) := by
  rw [shortTorusElt, shortTorusElt, map_mul, map_inv, ommOuter_c_shortWeylElt, ommOuter_c_shortWeyl]

private theorem ommOuter_c_shortTorusHom (hK : Nat.card K = 2) (i : Fin 3) (t : (ShortField b c)ˣ) :
    o8mOuterAut hirrQ (shortTorusHom 4 hirrQ i t) = shortTorusHom 4 hirrQ i (t ^ 2) := by
  rw [shortTorusHom_apply, shortTorusHom_apply, ommOuter_c_shortTorusElt,
    ← CFSG.LieType.Steinberg.CentralExt.SpinMinusClosed.fieldCoord_negStar (b := b) (c := c) t,
    Units.val_pow_eq_pow_val, ommOuter_negStar_eq_sq hirrQ hK t]

private theorem ommOuter_c_longWeyl (i j : Fin 3) (hij : i ≠ j) (s t : Bool) :
    o8mOuterAut hirrQ ((minusFrame 4 b c).longWeyl hij s t) =
      (minusFrame 4 b c).longWeyl hij s t := by
  rw [(minusFrame 4 b c).longWeyl_eq hij s t, map_mul, map_mul,
    ommOuter_c_longRoot i j hij s t 1, ommOuter_c_longRoot j i hij.symm (!t) (!s) (-1)]

private theorem ommOuter_c_longWeyl_succ (k : Fin 3) (hk : k.val + 1 < 3) :
    o8mOuterAut hirrQ ((minusFrame 4 b c).longWeyl (succ_ne_of_lt (n := 4) hk) true false) =
      (minusFrame 4 b c).longWeyl (succ_ne_of_lt (n := 4) hk) true false :=
  ommOuter_c_longWeyl (b := b) (c := c) k ⟨k.val + 1, hk⟩
    (succ_ne_of_lt (n := 4) hk) true false

private theorem ommOuter_c_minusWeyl (i : Fin 3) :
    o8mOuterAut hirrQ (minusWeyl 4 hirrQ i) = minusWeyl 4 hirrQ i := by
  rw [minusWeyl]
  split
  · exact ommOuter_c_longWeyl_succ (b := b) (c := c) i ‹_›
  · exact ommOuter_c_shortWeyl i

omit [Finite K] [CharP K 2] in
private theorem ommOuter_r0_mul_self :
    o8mPlaneRefl (b := b) (c := c) * o8mPlaneRefl (b := b) (c := c) = 1 :=
  TauCeti.QuadraticMap.reflection_mul_self _ _

theorem o8mOuterAut_apply_apply (g : spinGroup (quadMinus 4 K b c)) :
    o8mOuterAut hirrQ (o8mOuterAut hirrQ g) = g := by
  apply CFSG.StandardType.RootCentOmega.spinAction_quadMinus_injective hirrQ
  rw [spinAction_o8mOuterAut hirrQ, spinAction_o8mOuterAut hirrQ]
  have hinv : (o8mPlaneRefl (b := b) (c := c))⁻¹ = o8mPlaneRefl (b := b) (c := c) :=
    inv_eq_of_mul_eq_one_left (ommOuter_r0_mul_self (b := b) (c := c))
  rw [hinv,
    show o8mPlaneRefl (b := b) (c := c) *
        (o8mPlaneRefl (b := b) (c := c) * spinAction (quadMinus 4 K b c) g *
          o8mPlaneRefl (b := b) (c := c)) * o8mPlaneRefl (b := b) (c := c) =
      (o8mPlaneRefl (b := b) (c := c) * o8mPlaneRefl (b := b) (c := c)) *
        spinAction (quadMinus 4 K b c) g *
        (o8mPlaneRefl (b := b) (c := c) * o8mPlaneRefl (b := b) (c := c)) from by group]
  rw [ommOuter_r0_mul_self]
  group

private theorem ommOuter_c_o8mDatum_n (i : Fin 3) :
    o8mOuterAut hirrQ ((o8mDatum hirrQ).n i) = (o8mDatum hirrQ).n i := by
  rw [o8mDatum_n]
  exact ommOuter_c_minusWeyl i

private theorem ommOuter_c_mem_iff {S : Subgroup (spinGroup (quadMinus 4 K b c))}
    (hS : ∀ x ∈ S, o8mOuterAut hirrQ x ∈ S) (x : spinGroup (quadMinus 4 K b c)) :
    x ∈ S ↔ o8mOuterAut hirrQ x ∈ S := by
  refine ⟨hS x, fun hx => ?_⟩
  have := hS (o8mOuterAut hirrQ x) hx
  rwa [o8mOuterAut_apply_apply] at this

omit [Finite K] [CharP K 2] in
private theorem ommOuter_planeRefl_ne_zero {a : Fin 2 → K} (ha : a ≠ 0) :
    planeRefl b c planeOne a ≠ 0 := by
  intro h
  apply ha
  have := congrArg (planeRefl b c planeOne) h
  rwa [planeRefl_planeRefl planeNorm_planeOne_ne_zero, planeRefl_zero] at this

omit [CharP K 2] in
private theorem ommOuter_units_subsingleton (hK : Nat.card K = 2) : Subsingleton Kˣ := by
  refine ⟨fun u v => ?_⟩
  have hu : (u : K) = 1 := by
    rcases ommOuter_eq_zero_or_one hK (u : K) with h | h
    · exact absurd h u.ne_zero
    · exact h
  have hv : (v : K) = 1 := by
    rcases ommOuter_eq_zero_or_one hK (v : K) with h | h
    · exact absurd h v.ne_zero
    · exact h
  exact Units.ext (hu.trans hv.symm)

private theorem ommOuter_c_le_comap_longRootGroup (v : Fin 3 → ℤ) :
    (minusFrame 4 b c).longRootGroup v ≤
      ((minusFrame 4 b c).longRootGroup v).comap (o8mOuterAut hirrQ).toMonoidHom := by
  rw [HypFrame.longRootGroup]
  refine iSup_le fun i => iSup_le fun j => iSup_le fun hij => iSup_le fun s => iSup_le fun t =>
    iSup_le fun hv => ?_
  rintro x ⟨a, rfl⟩
  rw [Subgroup.mem_comap]
  change o8mOuterAut hirrQ ((minusFrame 4 b c).longRoot hij s t a) ∈ _
  rw [← ofAdd_toAdd a, ommOuter_c_longRoot]
  exact Subgroup.mem_iSup_of_mem i <| Subgroup.mem_iSup_of_mem j <| Subgroup.mem_iSup_of_mem hij <|
    Subgroup.mem_iSup_of_mem s <| Subgroup.mem_iSup_of_mem t <| Subgroup.mem_iSup_of_mem hv
      ⟨a, rfl⟩

private theorem ommOuter_c_le_comap_twShortRootGroup (v : Fin 3 → ℤ) :
    twShortRootGroup 4 hirrQ v ≤
      (twShortRootGroup 4 hirrQ v).comap (o8mOuterAut hirrQ).toMonoidHom := by
  rw [twShortRootGroup]
  refine iSup_le fun i => iSup_le fun s => iSup_le fun hv => ?_
  rintro x ⟨p, rfl⟩
  rw [Subgroup.mem_comap]
  change o8mOuterAut hirrQ ((twShortRoot 4 hirrQ i s) p) ∈ _
  rw [← ofAdd_toAdd p, ommOuter_c_twShortRoot]
  exact Subgroup.mem_iSup_of_mem i <| Subgroup.mem_iSup_of_mem s <|
    Subgroup.mem_iSup_of_mem hv ⟨planeRefl b c planeOne p, rfl⟩

private theorem ommOuter_c_map_minusRootGroup_le (γ : Fin 3 → ℤ) :
    (minusRootGroup 4 hirrQ γ).map (o8mOuterAut hirrQ).toMonoidHom ≤ minusRootGroup 4 hirrQ γ := by
  rw [minusRootGroup]
  refine (Subgroup.map_le_iff_le_comap).mpr (sup_le ?_ ?_)
  · exact (ommOuter_c_le_comap_longRootGroup (toStdB 3 γ)).trans (Subgroup.comap_mono le_sup_left)
  · exact (ommOuter_c_le_comap_twShortRootGroup (toStdB 3 γ)).trans
      (Subgroup.comap_mono le_sup_right)

private theorem ommOuter_c_mem_minusRootGroup (γ : Fin 3 → ℤ) {x : spinGroup (quadMinus 4 K b c)}
    (hx : x ∈ minusRootGroup 4 hirrQ γ) : o8mOuterAut hirrQ x ∈ minusRootGroup 4 hirrQ γ :=
  ommOuter_c_map_minusRootGroup_le γ (Subgroup.mem_map_of_mem _ hx)

private theorem ommOuter_c_o8mDatum_X (i : Fin 3) (x : spinGroup (quadMinus 4 K b c)) :
    x ∈ (o8mDatum hirrQ).X i ↔ o8mOuterAut hirrQ x ∈ (o8mDatum hirrQ).X i := by
  rw [o8mDatum_X]
  exact ommOuter_c_mem_iff (fun x hx => ommOuter_c_mem_minusRootGroup _ hx) x

private theorem ommOuter_c_le_comap_posUnipotent :
    CFSG.LieType.Steinberg.posUnipotent (minusDatum 4 hirrQ) ≤
      (CFSG.LieType.Steinberg.posUnipotent (minusDatum 4 hirrQ)).comap
        (o8mOuterAut hirrQ).toMonoidHom := by
  rw [CFSG.LieType.Steinberg.posUnipotent]
  refine iSup_le fun γ => iSup_le fun hγ => ?_
  rintro x hx
  rw [Subgroup.mem_comap]
  exact Subgroup.mem_iSup_of_mem γ <| Subgroup.mem_iSup_of_mem hγ
    (ommOuter_c_mem_minusRootGroup γ hx)

theorem mem_o8mDatum_U_iff_o8mOuterAut_mem (x : spinGroup (quadMinus 4 K b c)) :
    x ∈ (o8mDatum hirrQ).U ↔ o8mOuterAut hirrQ x ∈ (o8mDatum hirrQ).U := by
  change x ∈ CFSG.LieType.Steinberg.posUnipotent (minusDatum 4 hirrQ) ↔
    o8mOuterAut hirrQ x ∈ CFSG.LieType.Steinberg.posUnipotent (minusDatum 4 hirrQ)
  exact ommOuter_c_mem_iff
    (fun x hx => (Subgroup.mem_comap).mp (ommOuter_c_le_comap_posUnipotent hx)) x

private theorem ommOuter_c_mem_shortTorus (i : Fin 3) {x : spinGroup (quadMinus 4 K b c)}
    (hx : x ∈ shortTorus 4 hirrQ i) : o8mOuterAut hirrQ x ∈ shortTorus 4 hirrQ i := by
  rw [shortTorus] at hx ⊢
  refine Subgroup.closure_induction (p := fun y _ => o8mOuterAut hirrQ y ∈ shortTorus 4 hirrQ i)
    (fun y hy => ?_) (by rw [map_one]; exact Subgroup.one_mem _)
    (fun y z _ _ hy hz => by rw [map_mul]; exact Subgroup.mul_mem _ hy hz)
    (fun y _ hy => by rw [map_inv]; exact Subgroup.inv_mem _ hy) hx
  obtain ⟨a, ha, rfl⟩ := hy
  rw [ommOuter_c_shortTorusElt]
  exact Subgroup.subset_closure ⟨planeRefl b c planeOne a, ommOuter_planeRefl_ne_zero ha, rfl⟩

private theorem ommOuter_c_le_comap_minusTorus (hK : Nat.card K = 2) (i : Fin 3) :
    minusTorus 4 hirrQ i ≤ (minusTorus 4 hirrQ i).comap (o8mOuterAut hirrQ).toMonoidHom := by
  have : Subsingleton Kˣ := ommOuter_units_subsingleton hK
  intro x hx
  rw [Subgroup.mem_comap]
  match i with
  | ⟨0, h0⟩ =>
    rw [minusTorus_of_lt 4 hirrQ (k := ⟨0, h0⟩) (by norm_num)] at hx ⊢
    obtain ⟨τ, rfl⟩ := hx
    rw [Subsingleton.elim τ 1]
    simp
  | ⟨1, h1⟩ =>
    rw [minusTorus_of_lt 4 hirrQ (k := ⟨1, h1⟩) (by norm_num)] at hx ⊢
    obtain ⟨τ, rfl⟩ := hx
    rw [Subsingleton.elim τ 1]
    simp
  | ⟨2, h2⟩ =>
    rw [minusTorus_of_not_lt 4 hirrQ (k := ⟨2, h2⟩) (by norm_num)] at hx ⊢
    exact ommOuter_c_mem_shortTorus ⟨2, h2⟩ hx

private theorem ommOuter_c_o8mDatum_H (hK : Nat.card K = 2) (x : spinGroup (quadMinus 4 K b c)) :
    x ∈ (o8mDatum hirrQ).H ↔ o8mOuterAut hirrQ x ∈ (o8mDatum hirrQ).H := by
  have hle : (o8mDatum hirrQ).H ≤ ((o8mDatum hirrQ).H).comap (o8mOuterAut hirrQ).toMonoidHom := by
    change (⨆ i, minusTorus 4 hirrQ i) ≤
      ((⨆ i, minusTorus 4 hirrQ i)).comap (o8mOuterAut hirrQ).toMonoidHom
    refine iSup_le fun i => ?_
    exact (ommOuter_c_le_comap_minusTorus hK i).trans (Subgroup.comap_mono (le_iSup _ i))
  exact ommOuter_c_mem_iff (fun x hx => (Subgroup.mem_comap).mp (hle hx)) x

private theorem ommOuter_conj_involution {M : Type*} [Group M] {a r x : M} (ha : a * a = 1) :
    (r * a) * (a * x * a⁻¹) * (r * a)⁻¹ = r * x * r⁻¹ := by
  have hai : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha
  calc (r * a) * (a * x * a⁻¹) * (r * a)⁻¹
      = (r * a) * (a * x * a) * (r * a)⁻¹ := by rw [hai]
    _ = r * a * a * x * a * (a⁻¹ * r⁻¹) := by rw [mul_inv_rev]; group
    _ = r * (a * a) * x * (a * a) * r⁻¹ := by rw [hai]; group
    _ = r * x * r⁻¹ := by rw [ha]; group

private theorem ommOuter_not_mem_omegaGroup_of_outer
    (hirrQ : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (α : MulAut (spinGroup (quadMinus 4 K b c)))
    (houter : ∀ g₀ : spinGroup (quadMinus 4 K b c), α ≠ MulAut.conj g₀)
    {r : Vm 4 K ≃ₗ[K] Vm 4 K} (hnd : (quadMinus 4 K b c).polarBilin.Nondegenerate)
    (hconj : ∀ g, spinAction (quadMinus 4 K b c) (α g) =
      r * spinAction (quadMinus 4 K b c) g * r⁻¹) :
    r ∉ omegaGroup (quadMinus 4 K b c) hnd := by
  intro hr
  obtain ⟨h, hh⟩ :=
    exists_spinAction_eq_of_mem_omegaGroup_minus (hirr := hirrQ) (n := 4) (by norm_num) hr
  refine houter h (MulEquiv.ext fun g => ?_)
  apply CFSG.StandardType.RootCentOmega.spinAction_quadMinus_injective hirrQ
  rw [hconj g, MulAut.conj_apply, map_mul, map_mul, map_inv, hh]

private theorem ommOuter_exists_reflectionSpin (hirrQ : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (hK : Nat.card K = 2) (α : MulAut (spinGroup (quadMinus 4 K b c))) (hα2 : α * α = 1)
    (houter : ∀ g₀ : spinGroup (quadMinus 4 K b c), α ≠ MulAut.conj g₀) :
    ∃ (r : Vm 4 K ≃ₗ[K] Vm 4 K) (h : spinGroup (quadMinus 4 K b c)),
      (∀ g, spinAction (quadMinus 4 K b c) (α g) = r * spinAction (quadMinus 4 K b c) g * r⁻¹) ∧
      spinAction (quadMinus 4 K b c) h = r * o8mPlaneRefl (b := b) (c := c) := by
  classical
  have hnd : (quadMinus 4 K b c).polarBilin.Nondegenerate :=
    nondegenerate_polarBilin_quadMinus_of_finite 4 K hirrQ
  obtain ⟨sI, -, hsIconj⟩ :=
    exists_isometry_of_involutive_aut (b := b) (c := c) hirrQ (e := 1) (by norm_num)
      (by rw [hK]; norm_num) α hα2
  let E := coordinateMinusIsometry 4 K (by norm_num) b c
  let r : Vm 4 K ≃ₗ[K] Vm 4 K :=
    (E.toLinearEquiv.trans (matrixLinearIso sI.val)).trans E.symm.toLinearEquiv
  have hconj : ∀ g, spinAction (quadMinus 4 K b c) (α g) =
      r * spinAction (quadMinus 4 K b c) g * r⁻¹ := fun g =>
    spinAction_conj_of_coordinate hirrQ α sI hsIconj g
  have hS : ∀ w, coordinateQuadMinus 4 K (by norm_num) b c (matrixLinearIso sI.val w) =
      coordinateQuadMinus 4 K (by norm_num) b c w :=
    (mem_matrixIsometries_iff (coordinateQuadMinus 4 K (by norm_num) b c) sI.val).mp sI.2
  have hrO : r ∈ TauCeti.QuadraticMap.orthogonalGroup (quadMinus 4 K b c) := by
    rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff]
    intro v
    change quadMinus 4 K b c
      (E.symm.toLinearEquiv (matrixLinearIso sI.val (E.toLinearEquiv v))) = quadMinus 4 K b c v
    exact (E.symm.map_app (matrixLinearIso sI.val (E.toLinearEquiv v))).trans
      ((hS (E.toLinearEquiv v)).trans (E.map_app v))
  have hr_not : r ∉ omegaGroup (quadMinus 4 K b c) hnd :=
    ommOuter_not_mem_omegaGroup_of_outer hirrQ α houter hnd hconj
  have hOdd_r : Odd (Module.finrank K (commSpace r)) :=
    Nat.not_even_iff_odd.mp fun he => hr_not (mem_omegaGroup.mpr ⟨hrO, he⟩)
  have hfin_r0 : Module.finrank K (commSpace (o8mPlaneRefl (b := b) (c := c))) = 1 := by
    change Module.finrank K (commSpace
      (TauCeti.QuadraticMap.reflection (quadMinus 4 K b c) (planeVec 4 planeOne))) = 1
    exact finrank_commSpace_reflection hnd (planeVec 4 planeOne)
  have hOdd_r0 : Odd (Module.finrank K (commSpace (o8mPlaneRefl (b := b) (c := c)))) := by
    rw [hfin_r0]
    norm_num
  have hrr0 : r * o8mPlaneRefl (b := b) (c := c) ∈ omegaGroup (quadMinus 4 K b c) hnd := by
    refine mem_omegaGroup.mpr ⟨mul_mem hrO (ommOuter_r0_mem (b := b) (c := c)), ?_⟩
    rw [← ZMod.natCast_eq_zero_iff_even,
      natCast_finrank_commSpace_mul hnd hrO (ommOuter_r0_mem (b := b) (c := c)),
      hfin_r0,
      (ZMod.natCast_eq_one_iff_odd).mpr hOdd_r]
    exact CharTwo.add_self_eq_zero 1
  obtain ⟨h, hh⟩ :=
    exists_spinAction_eq_of_mem_omegaGroup_minus (hirr := hirrQ) (n := 4) (by norm_num) hrr0
  exact ⟨r, h, hconj, hh⟩

theorem exists_eq_conj_o8mOuterAut (hirrQ : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (hK : Nat.card K = 2) (α : MulAut (spinGroup (quadMinus 4 K b c))) (hα2 : α * α = 1)
    (houter : ∀ g₀ : spinGroup (quadMinus 4 K b c), α ≠ MulAut.conj g₀) :
    ∃ l : spinGroup (quadMinus 4 K b c), ∀ g, α g = l * o8mOuterAut hirrQ g * l⁻¹ := by
  obtain ⟨r, h, hconj, hh⟩ := ommOuter_exists_reflectionSpin hirrQ hK α hα2 houter
  have hr0sq : o8mPlaneRefl (b := b) (c := c) * o8mPlaneRefl (b := b) (c := c) = 1 :=
    TauCeti.QuadraticMap.reflection_mul_self (quadMinus 4 K b c) (planeVec 4 planeOne)
  refine ⟨h, fun g => ?_⟩
  apply CFSG.StandardType.RootCentOmega.spinAction_quadMinus_injective hirrQ
  rw [hconj g]
  symm
  calc spinAction (quadMinus 4 K b c) (h * o8mOuterAut hirrQ g * h⁻¹)
      = spinAction (quadMinus 4 K b c) h *
          spinAction (quadMinus 4 K b c) (o8mOuterAut hirrQ g) *
          (spinAction (quadMinus 4 K b c) h)⁻¹ := by rw [map_mul, map_mul, map_inv]
    _ = (r * o8mPlaneRefl (b := b) (c := c)) *
          (o8mPlaneRefl (b := b) (c := c) * spinAction (quadMinus 4 K b c) g *
            (o8mPlaneRefl (b := b) (c := c))⁻¹) *
          (r * o8mPlaneRefl (b := b) (c := c))⁻¹ := by
          rw [hh, spinAction_o8mOuterAut hirrQ]
    _ = r * spinAction (quadMinus 4 K b c) g * r⁻¹ := ommOuter_conj_involution hr0sq

private theorem ommOuter_twist_isCurtisType {G : Type*} [Group G] [Finite G] {B : Type*}
    {M : CoxeterMatrix B}
    {Weyl : Type*} [Group Weyl] {cs : CoxeterSystem M Weyl} {D : CurtisDatum G cs 2}
    {k V : Type*} [Field k] [CharP k 2] [AddCommGroup V] [Module k V]
    {ρ : Representation k G V} {y : V} {χ : G → k} {μ : B → k}
    (ht : D.IsCurtisType ρ y χ μ) (c : G ≃* G)
    (hU : ∀ u : G, u ∈ D.U ↔ c u ∈ D.U) (hH : ∀ h : G, h ∈ D.H ↔ c h ∈ D.H)
    (hX : ∀ s (x : G), x ∈ D.X s ↔ c x ∈ D.X s) (hn : ∀ s, c (D.n s) = D.n s)
    (T : V ≃ₗ[k] V) (hT : ∀ g v, T (ρ g v) = ρ (c g) (T v)) :
    D.IsCurtisType ρ (T y) (fun h => χ (c.symm h)) μ := by
  classical
  have : Fintype G := Fintype.ofFinite G
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hn' : ∀ s, c.symm (D.n s) = D.n s := fun s =>
    c.injective (by rw [MulEquiv.apply_symm_apply, hn s])
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro u hu
    have hu' : c.symm u ∈ D.U := (hU (c.symm u)).mpr (by simpa using hu)
    have h := hT (c.symm u) y
    rw [MulEquiv.apply_symm_apply] at h
    rw [← h, ht.1 _ hu']
  · intro h
    exact ht.2.1 (T.injective (h.trans (map_zero T).symm))
  · intro h hh
    have hh' : c.symm h ∈ D.H := (hH (c.symm h)).mpr (by simpa using hh)
    have h := hT (c.symm h) y
    rw [MulEquiv.apply_symm_apply] at h
    rw [← h, ht.2.2.1 _ hh', map_smul]
  · intro s
    rw [D.heckeT_apply ρ s (T y)]
    have hstep : ∀ x : D.X s, ρ ((x : G) * D.n s) (T y) =
        T (ρ (c.symm (x : G) * D.n s) y) := by
      intro x
      have h1 : c.symm ((x : G) * D.n s) = c.symm (x : G) * D.n s := by
        rw [map_mul, hn']
      have h := hT (c.symm ((x : G) * D.n s)) y
      rw [MulEquiv.apply_symm_apply, h1] at h
      exact h.symm
    let e : D.X s ≃ D.X s := (Equiv.subtypeEquiv c.toEquiv (hX s)).symm
    calc ∑ x : D.X s, ρ ((x : G) * D.n s) (T y)
        = ∑ x : D.X s, T (ρ (c.symm (x : G) * D.n s) y) :=
          Finset.sum_congr rfl fun x _ => hstep x
      _ = T (∑ x : D.X s, ρ (c.symm (x : G) * D.n s) y) := by rw [map_sum]
      _ = T (∑ x : D.X s, ρ (((e x : D.X s) : G) * D.n s) y) := rfl
      _ = T (∑ z : D.X s, ρ ((z : G) * D.n s) y) := by
          rw [Equiv.sum_comp e (fun z : D.X s => ρ ((z : G) * D.n s) y)]
      _ = T (μ s • y) := by rw [← D.heckeT_apply ρ s y, ht.2.2.2 s]
      _ = μ s • T y := map_smul T (μ s) y

private theorem ommOuter_twist_chi {G : Type*} [Group G] [Finite G] {B : Type*}
    {M : CoxeterMatrix B}
    {Weyl : Type*} [Group Weyl] {cs : CoxeterSystem M Weyl} {D : CurtisDatum G cs 2}
    {k V : Type*} [Field k] [CharP k 2] [AddCommGroup V] [Module k V]
    {ρ : Representation k G V} (hρ : IsSimpleRep ρ) {y : V} {χ : G → k} {μ : B → k}
    (ht : D.IsCurtisType ρ y χ μ) (c : G ≃* G)
    (hU : ∀ u : G, u ∈ D.U ↔ c u ∈ D.U) (hH : ∀ h : G, h ∈ D.H ↔ c h ∈ D.H)
    (hX : ∀ s (x : G), x ∈ D.X s ↔ c x ∈ D.X s) (hn : ∀ s, c (D.n s) = D.n s)
    (T : V ≃ₗ[k] V) (hT : ∀ g v, T (ρ g v) = ρ (c g) (T v)) :
    ∀ h ∈ D.H, χ (c h) = χ h := by
  classical
  have : Fintype G := Fintype.ofFinite G
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have ht' := ommOuter_twist_isCurtisType ht c hU hH hX hn T hT
  have huniq := CurtisDatum.IsCurtisType.unique hρ ht ht'
  intro h hh
  have h1 := huniq.1 (c h) ((hH h).mp hh)
  simp only [MulEquiv.symm_apply_apply] at h1
  exact h1

private theorem ommOuter_o8mDatum_H_eq (hirrQ : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (hK : Nat.card K = 2) : (o8mDatum hirrQ).H = shortTorus 4 hirrQ 2 := by
  have : Subsingleton Kˣ := ommOuter_units_subsingleton hK
  have h2 : minusTorus 4 hirrQ 2 = shortTorus 4 hirrQ 2 :=
    minusTorus_of_not_lt 4 hirrQ (k := 2) (by norm_num)
  change (⨆ i : Fin 3, minusTorus 4 hirrQ i) = shortTorus 4 hirrQ 2
  refine le_antisymm (iSup_le fun i => ?_) ?_
  · by_cases hi : i = 2
    · subst hi; rw [h2]
    · have hlt : i.val + 1 < 3 := by
        have hne : i.val ≠ 2 := fun hv => hi (Fin.ext hv)
        have := i.isLt
        omega
      rw [minusTorus_of_lt 4 hirrQ (k := i) hlt]
      have hbot : ((minusFrame 4 b c).longTorus (succ_ne_of_lt 4 hlt) true false).range = ⊥ := by
        rw [eq_bot_iff]
        rintro x ⟨τ, rfl⟩
        rw [Subsingleton.elim τ 1, map_one]
        exact Subgroup.one_mem _
      rw [hbot]
      exact bot_le
  · rw [← h2]
    exact le_iSup (fun i : Fin 3 => minusTorus 4 hirrQ i) 2

private theorem ommOuter_chi_eq_one (hirrQ : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (hK : Nat.card K = 2) {k : Type} [Field k] [CharP k 2]
    {V : Type} [AddCommGroup V] [Module k V]
    {ρ : Representation k (spinGroup (quadMinus 4 K b c)) V}
    {y : V} {χ : spinGroup (quadMinus 4 K b c) → k} {μ : Fin 3 → k}
    (ht : (o8mDatum hirrQ).IsCurtisType ρ y χ μ)
    (hchi : ∀ h ∈ (o8mDatum hirrQ).H, χ (o8mOuterAut hirrQ h) = χ h) :
    ∀ h ∈ (o8mDatum hirrQ).H, χ h = 1 := by
  intro h hh
  have hh' : h ∈ shortTorus 4 hirrQ 2 := by
    rwa [← ommOuter_o8mDatum_H_eq hirrQ hK]
  rw [← range_shortTorusHom 4 hirrQ 2] at hh'
  obtain ⟨t, rfl⟩ := hh'
  have hmem : shortTorusHom 4 hirrQ 2 t ∈ (o8mDatum hirrQ).H := by
    rw [ommOuter_o8mDatum_H_eq hirrQ hK, ← range_shortTorusHom 4 hirrQ 2]
    exact ⟨t, rfl⟩
  have h1 : χ (shortTorusHom 4 hirrQ 2 (t ^ 2)) = χ (shortTorusHom 4 hirrQ 2 t) := by
    have hc := hchi _ hmem
    rwa [ommOuter_c_shortTorusHom (hirrQ := hirrQ) hK 2 t] at hc
  have h2 : χ (shortTorusHom 4 hirrQ 2 (t ^ 2)) =
      (χ (shortTorusHom 4 hirrQ 2 t)) ^ 2 := by
    rw [map_pow (shortTorusHom 4 hirrQ 2) t 2]
    exact map_pow (CurtisDatum.IsCurtisType.chiHom ht)
      (⟨shortTorusHom 4 hirrQ 2 t, hmem⟩ : (o8mDatum hirrQ).H) 2
  have hne : χ (shortTorusHom 4 hirrQ 2 t) ≠ 0 := by
    intro h0
    have hmul := map_mul (CurtisDatum.IsCurtisType.chiHom ht)
      (⟨shortTorusHom 4 hirrQ 2 t, hmem⟩ : (o8mDatum hirrQ).H)
      (⟨shortTorusHom 4 hirrQ 2 t, hmem⟩ : (o8mDatum hirrQ).H)⁻¹
    rw [mul_inv_cancel, map_one, map_inv] at hmul
    rw [show (CurtisDatum.IsCurtisType.chiHom ht)
        (⟨shortTorusHom 4 hirrQ 2 t, hmem⟩ : (o8mDatum hirrQ).H) =
          χ (shortTorusHom 4 hirrQ 2 t) from rfl, h0, inv_zero, mul_zero] at hmul
    exact zero_ne_one hmul.symm
  have heq2 : χ (shortTorusHom 4 hirrQ 2 t) = (χ (shortTorusHom 4 hirrQ 2 t)) ^ 2 :=
    h1.symm.trans h2
  have hprod : χ (shortTorusHom 4 hirrQ 2 t) *
      (1 - χ (shortTorusHom 4 hirrQ 2 t)) = 0 := by
    rw [mul_sub, mul_one, sub_eq_zero]
    simpa [pow_two] using heq2
  rcases mul_eq_zero.mp hprod with h0 | h0
  · exact absurd h0 hne
  · rw [sub_eq_zero] at h0
    exact h0.symm

private theorem ommOuter_card_eq_two_of_le_bot {E k : Type*} [Field E] [Finite E] [Field k]
    [CharP k 2] [Algebra E k] (h : (algebraMap E k).fieldRange ≤ ⊥) : Nat.card E = 2 := by
  classical
  have : Fintype (⊥ : Subfield k) := Subfield.fintypeBot k 2
  have hinj : Function.Injective (algebraMap E k) := RingHom.injective _
  have hle : Nat.card E ≤ Nat.card (⊥ : Subfield k) := by
    refine Nat.card_le_card_of_injective
      (fun r : E => (⟨algebraMap E k r, h (RingHom.mem_fieldRange.mpr ⟨r, rfl⟩)⟩ :
        (⊥ : Subfield k))) ?_
    intro a b hab
    exact hinj (Subtype.ext_iff.mp hab)
  rw [Subfield.card_bot k 2] at hle
  have hgt : 1 < Nat.card E := Finite.one_lt_card
  omega

private theorem ommOuter_exists_twist {E k G M : Type*} [Field E] [Field k] [Algebra E k]
    [Group G] [AddCommGroup M] [Module E M] (σ : Representation E G M) (c : G ≃* G)
    (A : M ≃ₗ[E] M) (hA : ∀ g v, A (σ g v) = σ (c g) (A v)) :
    ∃ T : k ⊗[E] M ≃ₗ[k] k ⊗[E] M, ∀ g w,
      T (CFSG.Theory.Representation.extendScalars k σ g w) =
        CFSG.Theory.Representation.extendScalars k σ (c g) (T w) := by
  refine ⟨LinearEquiv.baseChange (R := E) (A := k) (M := M) (N := M) A, fun g w => ?_⟩
  rw [CFSG.Theory.Representation.extendScalars_apply,
    CFSG.Theory.Representation.extendScalars_apply]
  change (LinearMap.baseChange k (A : M →ₗ[E] M)) ((LinearMap.baseChange k (σ g)) w) =
    (LinearMap.baseChange k (σ (c g))) ((LinearMap.baseChange k (A : M →ₗ[E] M)) w)
  have h1 : (A : M →ₗ[E] M) ∘ₗ σ g = σ (c g) ∘ₗ A := by
    ext v
    exact hA g v
  have h2 := congrArg (fun f : M →ₗ[E] M => f.baseChange k) h1
  rw [LinearMap.baseChange_comp, LinearMap.baseChange_comp] at h2
  exact congrArg (fun f : k ⊗[E] M →ₗ[k] k ⊗[E] M => f w) h2

omit [Finite K] [CharP K 2] in
private theorem ommOuter_commute_of_endRing {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
    {ρ : Representation (ZMod 2) (spinGroup (quadMinus 4 K b c)) V} (s : V ≃ₗ[ZMod 2] V)
    (hcomm : ∀ d : EndRing ρ, ∀ v, s (d v) = d (s v)) :
    ∀ f : V →ₗ[ZMod 2] V, (∀ g, f ∘ₗ ρ g = ρ g ∘ₗ f) →
      s.toLinearMap ∘ₗ f = f ∘ₗ s.toLinearMap := by
  intro f hf
  obtain ⟨d, hd⟩ :=
    (CFSG.QuasithinUnique.Setup.SL2Modules.mem_endRing_iff ρ f).mpr fun g v => by
      have h := congrArg (fun m : V →ₗ[ZMod 2] V => m v) (hf g)
      simpa [LinearMap.comp_apply] using h
  ext v
  have h := hcomm d v
  rw [congrFun hd v, congrFun hd (s v)] at h
  simpa [LinearMap.comp_apply] using h

omit [Finite K] [CharP K 2] in
private theorem ommOuter_transportEnd_exists {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
    {ρ : Representation (ZMod 2) (spinGroup (quadMinus 4 K b c)) V} (s : V ≃ₗ[ZMod 2] V)
    (α : MulAut (spinGroup (quadMinus 4 K b c))) (hα : ∀ g v, s (ρ g (s.symm v)) = ρ (α g) v)
    (hcomm : ∀ d : EndRing ρ, ∀ v, s (d v) = d (s v)) :
    ∃ AE : ρ.asModule ≃ₗ[Module.End (MonoidAlgebra (ZMod 2) (spinGroup (quadMinus 4 K b c)))
        ρ.asModule] ρ.asModule,
      ∀ g x, AE (CFSG.endFieldRep ρ g x) = CFSG.endFieldRep ρ (α g) (AE x) := by
  classical
  let E := Module.End (MonoidAlgebra (ZMod 2) (spinGroup (quadMinus 4 K b c))) ρ.asModule
  have hα' : ∀ g v, s (ρ g v) = ρ (α g) (s v) := fun g v => by
    have h := hα g (s v)
    rwa [LinearEquiv.symm_apply_apply] at h
  let A : ρ.asModule ≃ₗ[ZMod 2] ρ.asModule :=
    ρ.asModuleEquiv.trans (s.trans ρ.asModuleEquiv.symm)
  have hAsmul : ∀ (c : E) (x : ρ.asModule), A (c • x) = c • A x := by
    intro c x
    change CFSG.LocalAnalysis.RankThreeUC.S15.GN15.FFO.PSL.transportEnd ρ s.toLinearMap
        (c • x) =
      c • CFSG.LocalAnalysis.RankThreeUC.S15.GN15.FFO.PSL.transportEnd ρ s.toLinearMap x
    exact CFSG.LocalAnalysis.RankThreeUC.S15.GN15.FFO.PSL.transportEnd_smul ρ s.toLinearMap
      (ommOuter_commute_of_endRing s hcomm) c x
  let AE : ρ.asModule ≃ₗ[E] ρ.asModule :=
    { toLinearMap := { toFun := A, map_add' := A.map_add, map_smul' := hAsmul }
      invFun := A.symm
      left_inv := A.left_inv
      right_inv := A.right_inv }
  refine ⟨AE, fun g x => ?_⟩
  change A (CFSG.endFieldRep ρ g x) = CFSG.endFieldRep ρ (α g) (A x)
  have hAx : A x = ρ.asModuleEquiv.symm (s (ρ.asModuleEquiv x)) := rfl
  rw [hAx]
  change ρ.asModuleEquiv.symm (s (ρ.asModuleEquiv (CFSG.endFieldRep ρ g x))) =
    ρ.asModuleEquiv.symm (ρ (α g) (s (ρ.asModuleEquiv x)))
  rw [CFSG.endFieldRep_apply', hα' g (ρ.asModuleEquiv x)]

private theorem ommOuter_exists_intertwiner {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
    {ρ : Representation (ZMod 2) (spinGroup (quadMinus 4 K b c)) V} (s : V ≃ₗ[ZMod 2] V)
    (α : MulAut (spinGroup (quadMinus 4 K b c))) (hα : ∀ g v, s (ρ g (s.symm v)) = ρ (α g) v)
    (hcomm : ∀ d : EndRing ρ, ∀ v, s (d v) = d (s v)) (l : spinGroup (quadMinus 4 K b c))
    (hl : ∀ g, α g = l * o8mOuterAut hirrQ g * l⁻¹) :
    ∃ A : ρ.asModule ≃ₗ[Module.End (MonoidAlgebra (ZMod 2) (spinGroup (quadMinus 4 K b c)))
        ρ.asModule] ρ.asModule,
      ∀ g v, A (CFSG.endFieldRep ρ g v) = CFSG.endFieldRep ρ (o8mOuterAut hirrQ g) (A v) := by
  classical
  let E := Module.End (MonoidAlgebra (ZMod 2) (spinGroup (quadMinus 4 K b c))) ρ.asModule
  obtain ⟨AE, hAint⟩ := ommOuter_transportEnd_exists s α hα hcomm
  let lE : ρ.asModule ≃ₗ[E] ρ.asModule :=
    { toLinearMap := CFSG.endFieldRep ρ l⁻¹
      invFun := CFSG.endFieldRep ρ l
      left_inv := fun x => by
        change CFSG.endFieldRep ρ l (CFSG.endFieldRep ρ l⁻¹ x) = x
        rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
      right_inv := fun y => by
        change CFSG.endFieldRep ρ l⁻¹ (CFSG.endFieldRep ρ l y) = y
        rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply] }
  let A' : ρ.asModule ≃ₗ[E] ρ.asModule := AE.trans lE
  have hiter : ∀ g, A' ∘ₗ CFSG.endFieldRep ρ g =
      CFSG.endFieldRep ρ (o8mOuterAut hirrQ g) ∘ₗ A' := by
    intro g
    ext x
    have hAintE : ρ.asModuleEquiv (AE (CFSG.endFieldRep ρ g x)) =
        ρ (α g) (ρ.asModuleEquiv (AE x)) := by
      rw [hAint g x, CFSG.endFieldRep_apply']
    have hρ : ∀ y : V, ρ l⁻¹ (ρ (α g) y) = ρ (o8mOuterAut hirrQ g) (ρ l⁻¹ y) := by
      intro y
      have heq : l⁻¹ * α g = o8mOuterAut hirrQ g * l⁻¹ := by
        rw [hl g]
        group
      simp only [← Module.End.mul_apply, ← map_mul, heq]
    apply ρ.asModuleEquiv.injective
    change ρ.asModuleEquiv (CFSG.endFieldRep ρ l⁻¹ (AE (CFSG.endFieldRep ρ g x))) =
      ρ.asModuleEquiv (CFSG.endFieldRep ρ (o8mOuterAut hirrQ g)
        (CFSG.endFieldRep ρ l⁻¹ (AE x)))
    simp only [CFSG.endFieldRep_apply']
    rw [hAintE]
    exact hρ (ρ.asModuleEquiv (AE x))
  refine ⟨A', fun g v => ?_⟩
  have h := congrArg (fun f : ρ.asModule →ₗ[E] ρ.asModule => f v) (hiter g)
  simpa [LinearMap.comp_apply] using h

theorem omMinus_two_card_endRing_eq_two_of_outer (hirrQ : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (hK : Nat.card K = 2) {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    {ρ : Representation (ZMod 2) (spinGroup (quadMinus 4 K b c)) V} (hρ : ρ.IsIrreducible)
    (s : V ≃ₗ[ZMod 2] V) (α : MulAut (spinGroup (quadMinus 4 K b c)))
    (hα : ∀ g v, s (ρ g (s.symm v)) = ρ (α g) v) (hα2 : α * α = 1)
    (houter : ∀ g₀ : spinGroup (quadMinus 4 K b c), α ≠ MulAut.conj g₀)
    (hcomm : ∀ d : EndRing ρ, ∀ v, s (d v) = d (s v)) :
    Nat.card (Module.End (MonoidAlgebra (ZMod 2) (spinGroup (quadMinus 4 K b c)))
      ρ.asModule) = 2 := by
  classical
  have : ρ.IsIrreducible := hρ
  let D := o8mDatum hirrQ
  have : Module.Finite (ZMod 2) V := Module.Finite.of_finite
  let E := Module.End (MonoidAlgebra (ZMod 2) (spinGroup (quadMinus 4 K b c))) ρ.asModule
  have : CharP E 2 := CFSG.HardMathSupport.GuralnickMalle.endField_charP ρ 2
  let k := AlgebraicClosure E
  have : Module.Finite E ρ.asModule :=
    CFSG.HardMathSupport.GuralnickMalle.finiteDimensional_endField ρ
  let τ := CFSG.Theory.Representation.extendScalars k (CFSG.endFieldRep ρ)
  have hτ : IsSimpleRep τ :=
    CFSG.HardMathSupport.Meierfrankenfeld.PSUScalar.isSimpleRep_extendScalars_endFieldRep ρ k
  have : Finite (CFSG.LieType.RootSystem.coxeterMatrix (isFiniteType_cartanB 3)).Group :=
    CFSG.LieType.RootSystem.finite_group (isFiniteType_cartanB 3)
  obtain ⟨z, χ, μ, ht⟩ := D.exists_isCurtisType
    (curtisDatum_splitOver (K := K) (k := k) hirrQ) hτ
  obtain ⟨l, hl⟩ := exists_eq_conj_o8mOuterAut hirrQ hK α hα2 houter
  obtain ⟨A, hA⟩ := ommOuter_exists_intertwiner (hirrQ := hirrQ) s α hα hcomm l hl
  obtain ⟨T, hT⟩ := ommOuter_exists_twist (k := k) (CFSG.endFieldRep ρ) (o8mOuterAut hirrQ) A hA
  have hchi := ommOuter_twist_chi (D := o8mDatum hirrQ) hτ ht (o8mOuterAut hirrQ)
    (mem_o8mDatum_U_iff_o8mOuterAut_mem) (ommOuter_c_o8mDatum_H hK) (ommOuter_c_o8mDatum_X)
    (ommOuter_c_o8mDatum_n) T hT
  have h1 := ommOuter_chi_eq_one hirrQ hK ht hchi
  have hfield :=
    CFSG.HardMathSupport.GuralnickMalle.isCurtisType_fieldRange_eq_closure ρ (o8mDatum hirrQ) k ht
  have hbot : (algebraMap E k).fieldRange ≤ ⊥ := by
    rw [hfield, Subfield.closure_le]
    rintro x ⟨h, hh, rfl⟩
    rw [h1 h hh]
    exact Subfield.one_mem ⊥
  exact ommOuter_card_eq_two_of_le_bot hbot

end CFSG.LocalAnalysis.WeakClosure81
