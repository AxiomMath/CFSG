
module

public import CFSG.Monster.B.TwoA.Unitary.WStabBase
public import CFSG.Monster.B.Classical.Derived22Coordinates
import all CFSG.Fischer.F4

public section

namespace CFSG.Monster.B.TwoA.Unitary.LinThree

open CFSG.Fischer CFSG.Monster.B.Classical.Plane CFSG.Monster.B.Classical.ThreePlane
  CFSG.LinearGroups CFSG.Monster.B.TwoA
open CFSG.Monster.Code (AutPerm)
open scoped LinearAlgebra.Projectivization MatrixGroups Matrix

@[expose] def jIdxN (n : ℕ) : Fin 21 := if h : n - 3 < 21 then jIdxTbl ⟨n - 3, h⟩ else 0

theorem jIdx_eq (i : NativeCoord) : jIdx i = jIdxN i := by
  rw [jIdxN, dite_eq_left (by omega)]
  rfl

theorem jIdxTbl_bijective : Function.Bijective jIdxTbl := by decide

@[expose] def coordEquiv : NativeCoord ≃ Fin 21 where
  toFun i := ⟨(i : ℕ) - 3, by omega⟩
  invFun t := ⟨⟨t + 3, by omega⟩, by simp⟩
  left_inv i := Subtype.ext (Fin.ext (by simp; omega))
  right_inv t := Fin.ext (by simp)

theorem jIdx_bijective : Function.Bijective jIdx :=
  jIdxTbl_bijective.comp coordEquiv.bijective

theorem j_bijective : Function.Bijective j := Ωproj.bijective.comp jIdx_bijective

@[expose] noncomputable def jEquiv : NativeCoord ≃ PlanePoint := Equiv.ofBijective j j_bijective

theorem jEquiv_apply (i : NativeCoord) : jEquiv i = j i := rfl

@[expose] def nlMask : Fin 21 → ℕ :=
  ![248, 3848, 61448, 15728648, 983048, 2392336, 1589776, 4331536, 8463376, 4276512, 8552992,
    2631712, 1315872, 8917376, 4465280, 1149056, 2245760, 1188160, 2167360, 8669248, 4752448]

theorem blockMasks_lines : ∀ bm ∈ CFSG.Monster.B.Classical.Mog22.blockMasks,
    2 ∈ (ofMask (bm + 3) : Finset (Fin 24)) → bm - 4 ∈ List.ofFn nlMask ∧
      (ofMask (bm + 3) : Finset (Fin 24)) \ {0, 1, 2} = ofMask (bm - 4) := by
  decide +kernel

theorem nlMask_blocks : ∀ b : Fin 21, nlMask b + 4 ∈ CFSG.Monster.B.Classical.Mog22.blockMasks ∧
    (({0, 1, 2} : Finset (Fin 24)) ⊆ ofMask (nlMask b + 4 + 3)) ∧
      (ofMask (nlMask b + 4 + 3) : Finset (Fin 24)) \ {0, 1, 2} = ofMask (nlMask b) := by
  decide +kernel

theorem nlMask_ge : ∀ b : Fin 21, ∀ i ∈ (ofMask (nlMask b) : Finset (Fin 24)), 3 ≤ (i : ℕ) := by
  decide +kernel

theorem nlMask_line : ∀ b t : Fin 21,
    (nlMask b).testBit (t + 3) = decide (∑ k, Ω b k * Ω (jIdxTbl t) k = 0) := by
  decide +kernel

theorem ofMask_nlMask_inj : ∀ a b : Fin 21,
    (ofMask (nlMask a) : Finset (Fin 24)) = ofMask (nlMask b) → a = b := by
  decide +kernel

theorem mem_nativeLines {d : Finset (Fin 24)} :
    d ∈ nativeLines ↔ ∃ b : Fin 21, d = ofMask (nlMask b) := by
  rw [nativeLines, Finset.mem_image]
  constructor
  · rintro ⟨O, hO, rfl⟩
    rw [Finset.mem_filter] at hO
    obtain ⟨hO, h012⟩ := hO
    have h0 : (0 : Fin 24) ∈ O := h012 (by simp)
    have h1 : (1 : Fin 24) ∈ O := h012 (by simp)
    have h2 : (2 : Fin 24) ∈ O := h012 (by simp)
    have hO' : O ∈ CFSG.Monster.B.Classical.Mog22.octads01 := by
      rw [CFSG.Monster.B.Classical.Mog22.octads01_eq, Finset.mem_filter]
      exact ⟨hO, h0, h1⟩
    simp only [CFSG.Monster.B.Classical.Mog22.octads01, List.mem_toFinset, List.mem_map] at hO'
    obtain ⟨bm, hbm, rfl⟩ := hO'
    obtain ⟨hmem, heq⟩ := blockMasks_lines bm hbm h2
    obtain ⟨b, hb⟩ := List.mem_ofFn.1 hmem
    exact ⟨b, heq.trans (by rw [← hb])⟩
  · rintro ⟨b, rfl⟩
    obtain ⟨hmem, hsub, heq⟩ := nlMask_blocks b
    refine ⟨ofMask (nlMask b + 4 + 3), Finset.mem_filter.2 ⟨?_, hsub⟩, heq⟩
    have h : (ofMask (nlMask b + 4 + 3) : Finset (Fin 24)) ∈
        CFSG.Monster.B.Classical.Mog22.octads01 := by
      simp only [CFSG.Monster.B.Classical.Mog22.octads01, List.mem_toFinset, List.mem_map]
      exact ⟨_, hmem, rfl⟩
    rw [CFSG.Monster.B.Classical.Mog22.octads01_eq, Finset.mem_filter] at h
    exact h.1

theorem nativeLines_eq :
    nativeLines = Finset.univ.image fun b => (ofMask (nlMask b) : Finset (Fin 24)) := by
  ext d
  rw [mem_nativeLines, Finset.mem_image]
  exact ⟨fun ⟨b, hb⟩ => ⟨b, Finset.mem_univ b, hb.symm⟩, fun ⟨b, _, hb⟩ => ⟨b, hb.symm⟩⟩

theorem card_nativeLines : nativeLines.card = 21 := by
  rw [nativeLines_eq, Finset.card_image_of_injective _ fun a b h => ofMask_nlMask_inj a b h,
    Finset.card_univ, Fintype.card_fin]

theorem nativeLines_ge {d : Finset (Fin 24)} (hd : d ∈ nativeLines) : ∀ i ∈ d, 3 ≤ (i : ℕ) := by
  obtain ⟨b, rfl⟩ := mem_nativeLines.1 hd
  exact nlMask_ge b

@[expose] noncomputable def lineSet (b : Fin 21) : Set PlanePoint := Ωproj '' ↑(projLine b)

theorem mem_ofMask_nlMask (b : Fin 21) (i : NativeCoord) :
    (i : Fin 24) ∈ (ofMask (nlMask b) : Finset (Fin 24)) ↔ jIdx i ∈ projLine b := by
  have h := nlMask_line b (coordEquiv i)
  have e : ((coordEquiv i : Fin 21) : ℕ) + 3 = ((i : Fin 24) : ℕ) := by
    change (i : ℕ) - 3 + 3 = _
    have := i.2
    omega
  rw [e] at h
  simp only [ofMask, Finset.mem_filter, Finset.mem_univ, true_and, projLine]
  rw [h, decide_eq_true_iff]
  rfl

theorem image_nlMask (b : Fin 21) :
    j '' {i : NativeCoord | (i : Fin 24) ∈ (ofMask (nlMask b) : Finset (Fin 24))} = lineSet b := by
  ext p
  constructor
  · rintro ⟨i, hi, rfl⟩
    exact ⟨jIdx i, (mem_ofMask_nlMask b i).1 hi, rfl⟩
  · rintro ⟨q, hq, rfl⟩
    obtain ⟨i, rfl⟩ := jIdx_bijective.2 q
    exact ⟨i, (mem_ofMask_nlMask b i).2 hq, rfl⟩

@[expose] noncomputable def dotForm (a : Fin 3 → F4) : Module.Dual F4 (Fin 3 → F4) :=
  ∑ k, a k • LinearMap.proj k

theorem dotForm_apply (a v : Fin 3 → F4) : dotForm a v = ∑ k, a k * v k := by
  simp [dotForm]

theorem dotForm_single (a : Fin 3 → F4) (k : Fin 3) : dotForm a (Pi.single k 1) = a k := by
  rw [dotForm_apply, Finset.sum_eq_single k]
  · simp
  · intro l _ hl
    simp [hl]
  · simp

theorem eq_dotForm (f : Module.Dual F4 (Fin 3 → F4)) :
    f = dotForm fun k => f (Pi.single k 1) := by
  refine LinearMap.pi_ext' fun k => LinearMap.ext_ring ?_
  rw [LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.coe_single, dotForm_single]

theorem dotForm_ne_zero {a : Fin 3 → F4} (ha : a ≠ 0) : dotForm a ≠ 0 := by
  intro h
  apply ha
  funext k
  rw [← dotForm_single a k, h, LinearMap.zero_apply, Pi.zero_apply]

theorem dotForm_smul (c : F4) (a : Fin 3 → F4) : dotForm (c • a) = c • dotForm a := by
  refine LinearMap.ext fun v => ?_
  simp only [dotForm_apply, LinearMap.smul_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum,
    mul_assoc]

theorem form_rep_eq_zero_iff (f : Module.Dual F4 (Fin 3 → F4)) (v : Fin 3 → F4) (hv : v ≠ 0) :
    f (Projectivization.mk F4 v hv).rep = 0 ↔ f v = 0 := by
  obtain ⟨a, ha⟩ := Projectivization.exists_smul_eq_mk_rep F4 v hv
  rw [← ha, Units.smul_def, map_smul, smul_eq_mul, mul_eq_zero, or_iff_right a.ne_zero]

theorem dotForm_eq_zero_iff (b : Fin 21) (v : Fin 3 → F4) (hv : v ≠ 0) :
    dotForm (Ω b) v = 0 ↔ normIdx v ∈ projLine b := by
  obtain ⟨c, hc, hv'⟩ := exists_smul_Ω_normIdx v hv
  simp only [projLine, Finset.mem_filter, Finset.mem_univ, true_and]
  conv_lhs => rw [hv']
  rw [map_smul, smul_eq_mul, mul_eq_zero, or_iff_right hc, dotForm_apply]

theorem lineSet_eq_kernel (b : Fin 21) :
    lineSet b = {p : PlanePoint | dotForm (Ω b) p.rep = 0} := by
  ext p
  induction p using Projectivization.ind with
  | h v hv =>
    rw [Set.mem_ofPred_eq, form_rep_eq_zero_iff, dotForm_eq_zero_iff b v hv, lineSet,
      Equiv.image_eq_preimage_symm, Set.mem_preimage, Ωproj_symm_mk, Finset.mem_coe]

theorem kernel_eq_lineSet (f : Module.Dual F4 (Fin 3 → F4)) (hf : f ≠ 0) :
    {p : PlanePoint | f p.rep = 0} = lineSet (normIdx fun k => f (Pi.single k 1)) := by
  set a : Fin 3 → F4 := fun k => f (Pi.single k 1) with ha_def
  have ha : a ≠ 0 := fun h => hf (by rw [eq_dotForm f, ← ha_def, h]; ext; simp [dotForm_apply])
  obtain ⟨c, hc, hac⟩ := exists_smul_Ω_normIdx a ha
  have hf' : f = c • dotForm (Ω (normIdx a)) := by
    calc f = dotForm a := eq_dotForm f
      _ = dotForm (c • Ω (normIdx a)) := congrArg dotForm hac
      _ = c • dotForm (Ω (normIdx a)) := dotForm_smul _ _
  rw [lineSet_eq_kernel]
  ext p
  rw [Set.mem_ofPred_eq, Set.mem_ofPred_eq]
  conv_lhs => rw [hf']
  rw [LinearMap.smul_apply, smul_eq_mul, mul_eq_zero, or_iff_right hc]

theorem image_nativeLines :
    (fun d : Finset (Fin 24) => j '' {i : NativeCoord | (i : Fin 24) ∈ d}) '' ↑nativeLines =
      {S | ∃ f : Module.Dual F4 (Fin 3 → F4), f ≠ 0 ∧ S = {p : PlanePoint | f p.rep = 0}} := by
  ext S
  constructor
  · rintro ⟨d, hd, rfl⟩
    obtain ⟨b, rfl⟩ := mem_nativeLines.1 hd
    exact ⟨dotForm (Ω b), dotForm_ne_zero (Ω_ne_zero b),
      (image_nlMask b).trans (lineSet_eq_kernel b)⟩
  · rintro ⟨f, hf, rfl⟩
    exact ⟨ofMask (nlMask (normIdx fun k => f (Pi.single k 1))), mem_nativeLines.2 ⟨_, rfl⟩,
      (image_nlMask _).trans (kernel_eq_lineSet f hf).symm⟩

theorem injOn_image_nativeLines :
    Set.InjOn (fun d : Finset (Fin 24) => j '' {i : NativeCoord | (i : Fin 24) ∈ d})
      ↑nativeLines := by
  intro d hd d' hd' h
  have h' : {i : NativeCoord | (i : Fin 24) ∈ d} = {i : NativeCoord | (i : Fin 24) ∈ d'} :=
    j_bijective.1.image_injective h
  ext x
  by_cases hx : 3 ≤ (x : ℕ)
  · exact iff_of_eq (congrArg (fun S : Set NativeCoord => (⟨x, hx⟩ : NativeCoord) ∈ S) h')
  · exact ⟨fun hm => absurd (nativeLines_ge hd x hm) hx,
      fun hm => absurd (nativeLines_ge hd' x hm) hx⟩

theorem image_pair_iff (p : Equiv.Perm (Fin 24)) :
    p '' {0, 1} = ({0, 1} : Set (Fin 24)) ↔ (p 0 = 0 ∧ p 1 = 1) ∨ (p 0 = 1 ∧ p 1 = 0) := by
  rw [Set.image_pair, Set.pair_eq_pair_iff]

theorem mem_P₂_iff (p : AutPerm) : (p : Equiv.Perm (Fin 24)) ∈ P₂ ↔ p ∈ P2 := by
  rw [mem_P₂, mem_P, mem_P2, mem_Ppair_iff, image_pair_iff]
  exact ⟨fun h => ⟨h.1.2, h.2⟩, fun h => ⟨⟨p.2, h.1⟩, h.2⟩⟩

theorem P₂_le_AutPerm : P₂ ≤ AutPerm := fun _ hp => (mem_P.1 (mem_P₂.1 hp).1).1

theorem P₂_eq_map : P₂ = P2.map AutPerm.subtype := by
  ext p
  constructor
  · intro hp
    exact ⟨⟨p, P₂_le_AutPerm hp⟩, (mem_P₂_iff _).1 hp, rfl⟩
  · rintro ⟨q, hq, rfl⟩
    exact (mem_P₂_iff q).2 hq

theorem natCard_P₂ : Nat.card P₂ = 40320 := by
  rw [P₂_eq_map, ← Nat.card_congr (P2.equivMapOfInjective AutPerm.subtype
    Subtype.val_injective).toEquiv, natCard_P2]

theorem nativeGenFn_check : ∀ (k : Fin 6) (i : Fin 24),
    (nativeGenFn k i : ℕ) = (n6PermArr[(k : ℕ)]!)[(i : ℕ)]! := by
  decide +kernel

theorem nativeGen_eq (k : Fin 6) : nativeGen k = (n6Aut k : Equiv.Perm (Fin 24)) :=
  Equiv.ext fun i => Fin.ext ((nativeGenFn_check k i).trans (n6Aut_apply k i).symm)

theorem nativeGen_mem (k : Fin 6) : nativeGen k ∈ P₂ := by
  rw [nativeGen_eq]
  exact (mem_P₂_iff (n6Aut k)).2 (n6Aut_mem_P2 k)

theorem mem_three_iff {p : Equiv.Perm (Fin 24)} (hp : p ∈ P₂) (i : Fin 24) :
    p i ∈ ({0, 1, 2} : Finset (Fin 24)) ↔ i ∈ ({0, 1, 2} : Finset (Fin 24)) := by
  obtain ⟨hP, h2⟩ := mem_P₂.1 hp
  have h01 := (image_pair_iff p).1 (mem_P.1 hP).2
  have hinj := p.injective
  simp only [Finset.mem_insert, Finset.mem_singleton]
  constructor
  · intro h
    rcases h01 with ⟨e0, e1⟩ | ⟨e0, e1⟩ <;> rcases h with h | h | h
    · exact .inl (hinj (h.trans e0.symm))
    · exact .inr (.inl (hinj (h.trans e1.symm)))
    · exact .inr (.inr (hinj (h.trans h2.symm)))
    · exact .inr (.inl (hinj (h.trans e1.symm)))
    · exact .inl (hinj (h.trans e0.symm))
    · exact .inr (.inr (hinj (h.trans h2.symm)))
  · rintro (rfl | rfl | rfl) <;> rcases h01 with ⟨e0, e1⟩ | ⟨e0, e1⟩ <;> simp [e0, e1, h2]

theorem three_le_iff : ∀ i : Fin 24, 3 ≤ (i : ℕ) ↔ i ∉ ({0, 1, 2} : Finset (Fin 24)) := by
  decide

theorem ge_three_iff {p : Equiv.Perm (Fin 24)} (hp : p ∈ P₂) (i : Fin 24) :
    3 ≤ (p i : ℕ) ↔ 3 ≤ (i : ℕ) := by
  rw [three_le_iff, three_le_iff, mem_three_iff hp]

@[expose] def restP : P₂ →* Equiv.Perm NativeCoord where
  toFun p := (p : Equiv.Perm (Fin 24)).subtypePerm fun i => ge_three_iff p.2 i
  map_one' := rfl
  map_mul' _ _ := rfl

theorem restP_apply (p : P₂) (i : NativeCoord) :
    (restP p i : Fin 24) = (p : Equiv.Perm (Fin 24)) i := rfl

attribute [local instance] restAction

theorem restP_injective : Function.Injective restP := by
  rw [injective_iff_map_eq_one]
  intro p hp
  have hfix : ∀ i : Fin 24, 3 ≤ (i : ℕ) → (p : Equiv.Perm (Fin 24)) i = i := fun i hi =>
    congrArg Subtype.val (Equiv.ext_iff.1 hp ⟨i, hi⟩)
  have hP2 : (⟨p, P₂_le_AutPerm p.2⟩ : AutPerm) ∈ P2 := (mem_P₂_iff _).1 p.2
  have hq : (⟨⟨p, P₂_le_AutPerm p.2⟩, (mem_P2.1 hP2).1⟩ : Ppair) = 1 :=
    eq_one_of_fix_rest fun i => Subtype.ext (by
      change (p : Equiv.Perm (Fin 24)) i = i
      by_cases h2 : (i : Fin 24) = 2
      · rw [h2]
        exact (mem_P2.1 hP2).2
      · have h0 : ((i : Fin 24) : ℕ) ≠ 0 := fun h => i.2.1 (Fin.ext h)
        have h1 : ((i : Fin 24) : ℕ) ≠ 1 := fun h => i.2.2 (Fin.ext h)
        have h2' : ((i : Fin 24) : ℕ) ≠ 2 := fun h => h2 (Fin.ext h)
        exact hfix i (by omega))
  exact Subtype.ext (congrArg (fun x : Ppair => ((x : AutPerm) : Equiv.Perm (Fin 24))) hq)

theorem sigma_smul_mk (A : SL(3, F4)) (ε : ZMod 2) (v : Fin 3 → F4) (hv : v ≠ 0) :
    (⟨(A : PSL(3, F4)), Multiplicative.ofAdd ε⟩ : SigmaL3) • Projectivization.mk F4 v hv =
      Projectivization.mk F4 (A • barPow ε v)
        ((smul_ne_zero_iff_ne A).mpr (barPow_ne_zero ε hv)) := by
  rw [CFSG.Monster.B.Classical.ThreePlane.smul_def, sigmaAct]
  change (A : PSL(3, F4)) • barPowP ε (Projectivization.mk F4 v hv) = _
  rw [barPowP_mk, Matrix.ProjectiveSpecialLinearGroup.smul_proj_mk, Projectivization.smul_mk]

theorem barPow_frame : ∀ (ε : ZMod 2) (k : Fin 3),
    barPow ε (Pi.single k 1) = Pi.single k 1 ∧ barPow ε 1 = 1 := by
  decide

theorem frame_ne_zero : ∀ k : Fin 3,
    (Pi.single k 1 : Fin 3 → F4) ≠ 0 ∧ (1 : Fin 3 → F4) ≠ 0 := by
  decide

theorem scalar_of_fix_frame (A : Matrix (Fin 3) (Fin 3) F4)
    (hk : ∀ k : Fin 3, ∃ c : F4, c • (Pi.single k 1 : Fin 3 → F4) = A *ᵥ Pi.single k 1)
    (h1 : ∃ c : F4, c • (1 : Fin 3 → F4) = A *ᵥ 1) : ∃ c : F4, A = c • 1 := by
  have hoff : ∀ i k : Fin 3, i ≠ k → A i k = 0 := by
    intro i k hik
    obtain ⟨c, hc⟩ := hk k
    have h := congrFun hc i
    rw [Matrix.mulVec_single_one, Matrix.col_apply, Pi.smul_apply, Pi.single_apply,
      ite_eq_right hik, smul_zero] at h
    exact h.symm
  obtain ⟨c, hc⟩ := h1
  have hdiag : ∀ i : Fin 3, A i i = c := by
    intro i
    have h := congrFun hc i
    simp only [Matrix.mulVec, dotProduct, Pi.one_apply, mul_one, Pi.smul_apply,
      smul_eq_mul] at h
    rw [Finset.sum_eq_single i (fun b _ hb => hoff i b (Ne.symm hb)) (by simp)] at h
    exact h.symm
  refine ⟨c, Matrix.ext fun i k => ?_⟩
  by_cases hik : i = k
  · subst hik
    rw [Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one, hdiag]
  · rw [Matrix.smul_apply, Matrix.one_apply_ne hik, smul_zero, hoff i k hik]

theorem det_ne_zero_of_scalar (A : SL(3, F4)) (c : F4)
    (hA : (A : Matrix (Fin 3) (Fin 3) F4) = c • 1) : c ≠ 0 := by
  rintro rfl
  have h := A.2
  rw [hA, zero_smul, Matrix.det_zero] at h
  exact zero_ne_one h

theorem mk_eq_one_of_scalar (A : SL(3, F4)) (c : F4)
    (hA : (A : Matrix (Fin 3) (Fin 3) F4) = c • 1) : (A : PSL(3, F4)) = 1 := by
  rw [QuotientGroup.eq_one_iff, ← scalarSL_eq_center]
  exact ⟨Units.mk0 c (det_ne_zero_of_scalar A c hA), hA⟩

theorem frob_moves : ∀ a c : F4, c ≠ 0 →
    a • (![1, F4.ω, 0] : Fin 3 → F4) ≠ c • fun i => (![1, F4.ω, 0] : Fin 3 → F4) i ^ 2 := by
  decide

theorem omega_vec_ne_zero : (![1, F4.ω, 0] : Fin 3 → F4) ≠ 0 := by decide

theorem eq_one_of_smul_eq (x : SigmaL3) (h : ∀ p : PlanePoint, x • p = p) : x = 1 := by
  obtain ⟨A, hA⟩ := QuotientGroup.mk_surjective x.left
  set ε : ZMod 2 := Multiplicative.toAdd x.right with hε
  have hx : x = ⟨(A : PSL(3, F4)), Multiplicative.ofAdd ε⟩ :=
    SemidirectProduct.ext hA.symm rfl
  have key : ∀ (v : Fin 3 → F4) (hv : v ≠ 0),
      ∃ c : F4, c • v = (A : Matrix (Fin 3) (Fin 3) F4) *ᵥ barPow ε v := by
    intro v hv
    have e := h (Projectivization.mk F4 v hv)
    rw [hx, sigma_smul_mk, Projectivization.mk_eq_mk_iff'] at e
    obtain ⟨c, hc⟩ := e
    exact ⟨c, by rw [hc, Matrix.SpecialLinearGroup.smul_def, Matrix.smul_eq_mulVec]⟩
  have hk : ∀ k : Fin 3, ∃ c : F4, c • (Pi.single k 1 : Fin 3 → F4) =
      (A : Matrix (Fin 3) (Fin 3) F4) *ᵥ Pi.single k 1 := by
    intro k
    have e := key _ (frame_ne_zero k).1
    rwa [(barPow_frame ε k).1] at e
  have h1 : ∃ c : F4, c • (1 : Fin 3 → F4) = (A : Matrix (Fin 3) (Fin 3) F4) *ᵥ 1 := by
    have e := key _ (frame_ne_zero 0).2
    rwa [(barPow_frame ε 0).2] at e
  obtain ⟨c, hc⟩ := scalar_of_fix_frame _ hk h1
  have hA1 : (A : PSL(3, F4)) = 1 := mk_eq_one_of_scalar A c hc
  have hε0 : ε = 0 := by
    rcases zmod2_cases ε with hε' | hε'
    · exact hε'
    · exfalso
      obtain ⟨a, ha⟩ := key _ omega_vec_ne_zero
      apply frob_moves a c (det_ne_zero_of_scalar A c hc)
      rw [ha, hc, Matrix.smul_mulVec, Matrix.one_mulVec, hε', barPow, ite_eq_right (by decide)]
  rw [hx, hA1, hε0]
  rfl

theorem card_F4 : Fintype.card F4 = 4 := F4.card

theorem natCard_GL3 : Nat.card (GL (Fin 3) F4) = 181440 := by
  rw [Matrix.card_GL_field, card_F4, Fin.prod_univ_three]
  rfl

theorem natCard_SL3 : Nat.card SL(3, F4) = 60480 := by
  rw [Matrix.card_SL_field, card_F4, Fin.prod_univ_three]
  rfl

theorem rootsOfUnity_eq_top : rootsOfUnity 3 F4 = ⊤ := by
  ext u
  simp only [mem_rootsOfUnity, Subgroup.mem_top, iff_true]
  have h := pow_card_eq_one (G := F4ˣ) (x := u)
  rwa [Fintype.card_units, card_F4] at h

theorem natCard_center : Nat.card (Subgroup.center SL(3, F4)) = 3 := by
  rw [Nat.card_congr (Matrix.SpecialLinearGroup.center_equiv_rootsOfUnity' (0 : Fin 3)).toEquiv]
  have e : Fintype.card (Fin 3) = 3 := Fintype.card_fin 3
  rw [e, rootsOfUnity_eq_top, Subgroup.card_top, Nat.card_eq_fintype_card, Fintype.card_units,
    card_F4]

theorem natCard_PSL3 : Nat.card PSL(3, F4) = 20160 := by
  have h := Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center SL(3, F4))
  rw [natCard_SL3, natCard_center] at h
  change Nat.card (SL(3, F4) ⧸ Subgroup.center SL(3, F4)) = 20160
  omega

theorem natCard_SigmaL3 : Nat.card SigmaL3 = 40320 := by
  rw [SemidirectProduct.card, natCard_PSL3, Nat.card_eq_fintype_card]
  rfl

theorem genMat_det (k : Fin 6) : (genMat k).det = 1 := by
  rw [Matrix.det_fin_three]
  revert k
  decide +kernel

@[expose] def genSL (k : Fin 6) : SL(3, F4) := ⟨genMat k, genMat_det k⟩

@[expose] noncomputable def genElt (k : Fin 6) : SigmaL3 := pairElt (genSL k) (genFrob k)

@[expose] def genP (k : Fin 6) : P₂ := ⟨nativeGen k, nativeGen_mem k⟩

theorem gen_check : ∀ (k : Fin 6) (i : Fin 24), 3 ≤ (i : ℕ) →
    normIdx (CFSG.Monster.B.Classical.ThreePlane.pairVec (genMat k) (genFrob k) (Ω (jIdxN i))) =
      jIdxN (nativeGenFn k i) := by
  decide +kernel

theorem normIdx_pairVec (k : Fin 6) (i : NativeCoord) :
    normIdx (CFSG.Monster.B.Classical.ThreePlane.pairVec (genMat k) (genFrob k) (jVec i)) =
      jIdx (restP (genP k) i) := by
  rw [jVec, jIdx_eq, jIdx_eq]
  exact gen_check k i i.2

theorem genElt_smul_j (k : Fin 6) (i : NativeCoord) : genElt k • j i = j (restP (genP k) i) := by
  rw [genElt, j, Ωproj_apply, pairElt_smul_mk]
  apply Ωproj.symm.injective
  rw [Ωproj_symm_mk, j, Equiv.symm_apply_apply]
  exact normIdx_pairVec k i

@[expose] noncomputable def rhoN : P₂ →* Equiv.Perm PlanePoint :=
  jEquiv.permCongrHom.toMonoidHom.comp restP

theorem rhoN_j (p : P₂) (i : NativeCoord) : rhoN p (j i) = j (restP p i) := by
  change jEquiv (restP p (jEquiv.symm (jEquiv i))) = jEquiv (restP p i)
  rw [Equiv.symm_apply_apply]

theorem rhoN_injective : Function.Injective rhoN :=
  jEquiv.permCongrHom.injective.comp restP_injective

@[expose] noncomputable def rhoS : SigmaL3 →* Equiv.Perm PlanePoint :=
  MulAction.toPermHom SigmaL3 PlanePoint

theorem rhoS_apply (x : SigmaL3) (p : PlanePoint) : rhoS x p = x • p := rfl

theorem rhoS_injective : Function.Injective rhoS := by
  rw [injective_iff_map_eq_one]
  intro x hx
  exact eq_one_of_smul_eq x fun p => congrArg (fun f : Equiv.Perm PlanePoint => f p) hx

theorem rhoN_genP (k : Fin 6) : rhoN (genP k) = rhoS (genElt k) := by
  ext p
  obtain ⟨i, rfl⟩ := j_bijective.2 p
  rw [rhoN_j, rhoS_apply, genElt_smul_j]

theorem natCard_range_rhoS : Nat.card rhoS.range = 40320 := by
  rw [← Nat.card_congr (MonoidHom.ofInjective rhoS_injective).toEquiv, natCard_SigmaL3]

theorem frob_smul (p : PlanePoint) :
    (⟨1, Multiplicative.ofAdd 1⟩ : SigmaL3) • p = frobP p := by
  rw [CFSG.Monster.B.Classical.ThreePlane.smul_def, sigmaAct]
  change (1 : PSL(3, F4)) • barPowP 1 p = frobP p
  rw [one_smul, barPowP, ite_eq_right (by decide)]

end CFSG.Monster.B.TwoA.Unitary.LinThree
