
module

public import CFSG.Sporadic.Co1
public import CFSG.Sporadic.Co1.Module.OrbitsInputs
public meta import Certificates.Data.CFSGNative.Co1.Data
public meta import Certificates.Data.CFSGNative.Perm.Chain
import CFSG.Perm.OrbitTree
import all CFSG.Blueprint.NativeSporadic
public import CFSG.Sporadic.Co1Base
public import CFSG.Sporadic.Th.F2Spec

public section

namespace CFSG.Sporadic.Co1.Module

open CFSG.Blueprint CFSG.Sporadic.SmallF2 CFSG.Sporadic.SmallF2.Native CFSG.Sporadic.Th
  CFSG.Sporadic.Th.Native CFSG.Perm.Native Matrix

abbrev Vec24 : Type := Fin 24 → ZMod 2

noncomputable abbrev Jmat : Subgroup (GL (Fin 24) (ZMod 2)) := SmallF2.J dat

noncomputable abbrev genA : Jmat := SmallF2.a dat

noncomputable abbrev genB : Jmat := SmallF2.b dat

@[expose] def matA : Matrix (Fin 24) (Fin 24) (ZMod 2) := rowsMatrix 24 dat.rowsA

@[expose] def matB : Matrix (Fin 24) (Fin 24) (ZMod 2) := rowsMatrix 24 dat.rowsB

@[expose] def v₂ : Vec24 := Pi.single 1 1

@[expose] def v₃ : Vec24 := Pi.single 12 1

@[expose] def v₄ : Vec24 := Pi.single 0 1

@[expose] def reps : Fin 3 → Vec24 := ![v₂, v₃, v₄]

theorem co1BaseFacts : BaseFacts dat := co1Facts.toBaseFacts

theorem genA_val :
    ((genA : GL (Fin 24) (ZMod 2)) : Matrix (Fin 24) (Fin 24) (ZMod 2)) = matA :=
  (a_val co1BaseFacts).trans (rowsMatrix_rowsA dat).symm

theorem genB_val :
    ((genB : GL (Fin 24) (ZMod 2)) : Matrix (Fin 24) (Fin 24) (ZMod 2)) = matB :=
  (b_val co1BaseFacts).trans (rowsMatrix_rowsB dat).symm

theorem matA_mul_self : matA * matA = 1 := by
  have h : mA dat ^ 2 = 1 := mA_pow co1BaseFacts
  rw [pow_two, ← rowsMatrix_rowsA] at h
  exact h

theorem matB_mul_mul : matB * (matB * matB) = 1 := by
  have h : mB dat ^ 3 = 1 := mB_pow co1BaseFacts
  rw [pow_succ', pow_two, ← rowsMatrix_rowsB] at h
  exact h

theorem smul_eq_mulVec {H : Subgroup (GL (Fin 24) (ZMod 2))} (g : H) (v : Vec24) :
    g • v = ((g : GL (Fin 24) (ZMod 2)) : Matrix (Fin 24) (Fin 24) (ZMod 2)) *ᵥ v := rfl

theorem toVecD_two_pow (i : Fin 24) : toVecD 24 (2 ^ (i : ℕ)) = Pi.single i 1 := by
  funext j
  rw [toVecD_apply, Nat.testBit_two_pow, Pi.single_apply]
  by_cases h : j = i
  · subst h; simp
  · have h' : (i : ℕ) ≠ j := fun e => h (Fin.ext e.symm)
    simp [h, h']

theorem toVecD_v₂ : toVecD 24 2 = v₂ := toVecD_two_pow 1

theorem toVecD_v₃ : toVecD 24 4096 = v₃ := toVecD_two_pow 12

theorem toVecD_v₄ : toVecD 24 1 = v₄ := toVecD_two_pow 0

@[expose] def orbitVec (v n i : ℕ) : Vec24 := toVecD 24 (orbitOf v n).pts[i]!

theorem a_smul_toVecD (x : ℕ) :
    genA • toVecD 24 x = toVecD 24 (vecMulN 24 dat.colsA x) := by
  have := SmallF2.smul_vec dat (SmallF2.a dat) (toVecD dat.d x)
  rw [a_val co1BaseFacts, ← rowsMatrix_rowsA, rowsMatrix_mulVec] at this
  exact this

theorem b_smul_toVecD (x : ℕ) :
    genB • toVecD 24 x = toVecD 24 (vecMulN 24 dat.colsB x) := by
  have := SmallF2.smul_vec dat (SmallF2.b dat) (toVecD dat.d x)
  rw [b_val co1BaseFacts, ← rowsMatrix_rowsB, rowsMatrix_mulVec] at this
  exact this

theorem vOrbitOK_facts {d n : ℕ} {cA cB : Array ℕ} {O : VOrbit}
    (h : vOrbitOK d n cA cB O = true) :
    O.pts.size = n ∧ ∀ i < n, O.pts[i]! < 2 ^ d ∧ ((posTable d O.pts)[O.pts[i]!]!).toNat = i ∧
      ap O.alpha i < n ∧ O.pts[ap O.alpha i]! = vecMulN d cA O.pts[i]! ∧
      ap O.beta i < n ∧ O.pts[ap O.beta i]! = vecMulN d cB O.pts[i]! := by
  unfold vOrbitOK at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  refine ⟨h1, fun i hi => ?_⟩
  have := (allIn_eq_true.1 h4) i (Nat.zero_le _) hi
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at this
  obtain ⟨⟨⟨⟨⟨h5, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩ := this
  exact ⟨h5, h6, h7, h8, h9, h10⟩

theorem treeOK_arith {n r : ℕ} {T : Tree} {letters : Array Table} {lv : Array ℕ}
    (h : Perm.Native.treeOK n r T letters lv = true) :
    0 < T.pts.size ∧ ap T.pts 0 = r ∧ ∀ k < T.pts.size, ap T.pts k < n ∧
      ap T.pos (ap T.pts k) = k ∧
      (∀ l ∈ lv, ap T.pos (ap letters[l]! (ap T.pts k)) < T.pts.size ∧
        ap T.pts (ap T.pos (ap letters[l]! (ap T.pts k))) = ap letters[l]! (ap T.pts k)) ∧
      (k = 0 ∨ (ap T.par k < k ∧ ap T.lab k ∈ lv ∧
        ap letters[ap T.lab k]! (ap T.pts (ap T.par k)) = ap T.pts k)) := by
  simp only [Perm.Native.treeOK, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  obtain ⟨⟨hm, h0⟩, hall⟩ := h
  refine ⟨hm, h0, fun k hk => ?_⟩
  have := (allIn_eq_true.1 hall) k (Nat.zero_le _) hk
  simp only [Perm.Native.treeAt, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq,
    Array.all_eq_true, Bool.or_eq_true, Array.contains_iff_mem] at this
  obtain ⟨⟨⟨hlt, hpos⟩, hcl⟩, hpar⟩ := this
  refine ⟨hlt, hpos, fun l hl => ?_, ?_⟩
  · obtain ⟨i, hi, rfl⟩ := Array.mem_iff_getElem.1 hl
    have := hcl i hi
    simpa using this
  · rcases hpar with h | ⟨⟨h1, h2⟩, h3⟩
    · exact Or.inl h
    · exact Or.inr ⟨h1, h2, h3⟩

theorem orbit_spec
    {v n : ℕ} {others : List ℕ} (h : orbitCheck v n others = true) :
    MulAction.orbit Jmat (toVecD 24 v) = orbitVec v n '' {i | i < n} ∧
      (∀ i < n, ∀ j < n, orbitVec v n i = orbitVec v n j → i = j) ∧
      (∀ w ∈ others, w < 2 ^ 24 → toVecD 24 w ∉ orbitVec v n '' {i | i < n}) := by
  classical
  unfold orbitCheck at h
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, Bool.not_eq_true'] at h
  obtain ⟨⟨⟨⟨hOK, h0⟩, hsz⟩, hTOK⟩, hoth⟩ := h
  set O := orbitOf v n with hO
  set ls : Array Table := #[O.alpha, O.beta] with hls
  set T := treeBFS n 0 ls #[0, 1] with hT
  obtain ⟨hsize, hO'⟩ := vOrbitOK_facts hOK
  obtain ⟨hpos, hroot, hTk⟩ := treeOK_arith hTOK
  have hn : 0 < n := hsz ▸ hpos
  have hTk' : ∀ k < n, _ := fun k hk => hTk k (by rw [hsz]; exact hk)
  have hinj : ∀ i < n, ∀ j < n, orbitVec v n i = orbitVec v n j → i = j := by
    intro i hi j hj e
    have e' := toVecD_injective (hO' i hi).1 (hO' j hj).1 e
    rw [← (hO' i hi).2.1, ← (hO' j hj).2.1, e']
  have hA : ∀ i < n, genA • orbitVec v n i = orbitVec v n (ap O.alpha i) := by
    intro i hi
    rw [orbitVec, a_smul_toVecD, orbitVec, ← (hO' i hi).2.2.2.1]
  have hB : ∀ i < n, genB • orbitVec v n i = orbitVec v n (ap O.beta i) := by
    intro i hi
    rw [orbitVec, b_smul_toVecD, orbitVec, ← (hO' i hi).2.2.2.2.2]
  have hQlt : ∀ k < n, ap T.pts k < n := fun k hk => (hTk' k hk).1
  have hinjT : ∀ j < n, ∀ k < n, ap T.pts j = ap T.pts k → j = k := by
    intro j hj k hk e
    rw [← (hTk' j hj).2.1, ← (hTk' k hk).2.1, e]
  have hsurj : ∀ i < n, ∃ k < n, ap T.pts k = i := by
    intro i hi
    let f : Fin n → Fin n := fun k => ⟨ap T.pts k, hQlt k k.isLt⟩
    have hf : Function.Injective f := by
      intro j k e
      apply Fin.ext
      exact hinjT j j.isLt k k.isLt (by simpa [f] using congrArg Fin.val e)
    obtain ⟨k, hk⟩ := Finite.injective_iff_surjective.1 hf ⟨i, hi⟩
    exact ⟨k, k.isLt, congrArg Fin.val hk⟩
  have himg : (fun k => orbitVec v n (ap T.pts k)) '' {k | k < n} =
      orbitVec v n '' {i | i < n} := by
    ext x
    constructor
    · rintro ⟨k, hk, rfl⟩
      exact ⟨ap T.pts k, hQlt k hk, rfl⟩
    · rintro ⟨i, hi, rfl⟩
      obtain ⟨k, hk, e⟩ := hsurj i hi
      exact ⟨k, hk, by show orbitVec v n (ap T.pts k) = _; rw [e]⟩
  have hroot' : orbitVec v n (ap T.pts 0) = toVecD 24 v := by
    rw [hroot, orbitVec, h0]
  have hl0 : ls[0]! = O.alpha := rfl
  have hl1 : ls[1]! = O.beta := rfl
  have hclosed : ∀ k < n, ∀ s ∈ ({genA, genB} : Set Jmat), ∃ j < n,
      orbitVec v n (ap T.pts j) = s • orbitVec v n (ap T.pts k) := by
    intro k hk s hs
    have hk' := hTk' k hk
    rcases hs with rfl | hs
    · have := hk'.2.2.1 0 (by simp)
      rw [hl0] at this
      refine ⟨_, hsz ▸ this.1, ?_⟩
      show orbitVec v n (ap T.pts (ap T.pos (ap O.alpha (ap T.pts k)))) = _
      rw [this.2, hA _ (hQlt k hk)]
    · rw [Set.mem_singleton_iff] at hs
      subst hs
      have := hk'.2.2.1 1 (by simp)
      rw [hl1] at this
      refine ⟨_, hsz ▸ this.1, ?_⟩
      show orbitVec v n (ap T.pts (ap T.pos (ap O.beta (ap T.pts k)))) = _
      rw [this.2, hB _ (hQlt k hk)]
  have hpar : ∀ k, 0 < k → k < n → ap T.par k < k := by
    intro k hk0 hk
    rcases (hTk' k hk).2.2.2 with h | h
    · omega
    · exact h.1
  have htree : ∀ k, 0 < k → k < n → orbitVec v n (ap T.pts k) =
      (if ap T.lab k = 0 then genA else genB) • orbitVec v n (ap T.pts (ap T.par k)) := by
    intro k hk0 hk
    rcases (hTk' k hk).2.2.2 with h | ⟨hp, hl, he⟩
    · omega
    · have hpk : ap T.par k < n := lt_trans hp hk
      have hlab : ap T.lab k = 0 ∨ ap T.lab k = 1 := by simpa using hl
      rcases hlab with hlab | hlab
      · rw [show (if ap T.lab k = 0 then genA else genB) = genA by simp [hlab]]
        rw [hlab, hl0] at he
        have he' : ap O.alpha (ap T.pts (ap T.par k)) = ap T.pts k := he
        rw [hA _ (hQlt _ hpk), he']
      · rw [show (if ap T.lab k = 0 then genA else genB) = genB by simp [hlab]]
        rw [hlab, hl1] at he
        have he' : ap O.beta (ap T.pts (ap T.par k)) = ap T.pts k := he
        rw [hB _ (hQlt _ hpk), he']
  have horb := CFSG.Perm.orbitTree_orbit_eq (G := Jmat) (S := ({genA, genB} : Set Jmat))
    (n := n) (P := fun k => orbitVec v n (ap T.pts k)) (par := fun k => ap T.par k)
    (lab := fun k => ap T.lab k) (ℓ := fun l => if l = 0 then genA else genB)
    (closure_ab dat) hn hclosed hpar htree
  have horb' : MulAction.orbit Jmat (toVecD 24 v) = orbitVec v n '' {i | i < n} := by
    rw [← hroot', ← himg]
    exact horb
  refine ⟨horb', hinj, ?_⟩
  rintro w hw hw24 ⟨i, hi, e⟩
  have hi' : i < n := hi
  have hw' : w = O.pts[i]! := toVecD_injective hw24 (hO' i hi').1 e.symm
  have hmem : O.pts[i]! ∈ O.pts := by
    rw [getElem!_pos O.pts i (by rw [hsize]; exact hi')]
    exact Array.getElem_mem _
  have := hoth w hw
  rw [hw'] at this
  have h2 := Array.contains_iff_mem.2 hmem
  rw [this] at h2
  exact absurd h2 (by decide)

theorem ncard_orbit_of_check
    {v n : ℕ} {others : List ℕ} (h : orbitCheck v n others = true) :
    (MulAction.orbit Jmat (toVecD 24 v)).ncard = n := by
  obtain ⟨h1, h2, -⟩ := orbit_spec h
  rw [h1, Set.InjOn.ncard_image (s := {i | i < n}) fun i hi j hj e => h2 i hi j hj e]
  exact Set.ncard_Iio_nat n

theorem not_mem_orbit_of_check
    {v n w : ℕ} {others : List ℕ} (h : orbitCheck v n others = true)
    (hw : w ∈ others) (hw24 : w < 2 ^ 24) : toVecD 24 w ∉ MulAction.orbit Jmat (toVecD 24 v) := by
  obtain ⟨h1, -, h3⟩ := orbit_spec h
  rw [h1]
  exact h3 w hw hw24

theorem disjoint_orbit {a b : Vec24} (h : a ∉ MulAction.orbit Jmat b) :
    Disjoint (MulAction.orbit Jmat a) (MulAction.orbit Jmat b) := by
  rw [Set.disjoint_left]
  intro x hxa hxb
  apply h
  have e1 : MulAction.orbit Jmat x = MulAction.orbit Jmat a := MulAction.orbit_eq_iff.2 hxa
  have e2 : MulAction.orbit Jmat x = MulAction.orbit Jmat b := MulAction.orbit_eq_iff.2 hxb
  rw [← e2, e1]
  exact MulAction.mem_orbit_self a

theorem zero_not_mem_orbit {v : Vec24} (hv : v ≠ 0) : (0 : Vec24) ∉ MulAction.orbit Jmat v := by
  rintro ⟨g, hg⟩
  apply hv
  have h0 : g • v = 0 := hg
  have : v = (g⁻¹ : Jmat) • (g • v) := (inv_smul_smul g v).symm
  rw [this, h0, smul_eq_mulVec, Matrix.mulVec_zero]

theorem v₂_ne_zero : v₂ ≠ 0 := by
  intro h
  have := congrFun h 1
  simp [v₂] at this

theorem v₃_ne_zero : v₃ ≠ 0 := by
  intro h
  have := congrFun h 12
  simp [v₃] at this

theorem v₄_ne_zero : v₄ ≠ 0 := by
  intro h
  have := congrFun h 0
  simp [v₄] at this

@[expose] def co1Act (g : NativeSporadic.Co1) (v : Vec24) : Vec24 :=
  (g.val.val : Matrix (Fin 24) (Fin 24) (ZMod 2)) *ᵥ v

section Generic

variable {D : VecData} (hB : BaseFacts D)
include hB

theorem seedMonoid_eq_closure :
    NativeSporadic.seedMonoid 2 D.d 1 D.seedA D.seedB =
      Submonoid.closure {((SmallF2.gA D : GL (Fin D.d) (ZMod 2)) :
        Matrix (Fin D.d) (Fin D.d) (ZMod 2)), ((SmallF2.gB D : GL (Fin D.d) (ZMod 2)) :
        Matrix (Fin D.d) (Fin D.d) (ZMod 2))} := by
  have h1 : ((SmallF2.gA D : GL (Fin D.d) (ZMod 2)) : Matrix (Fin D.d) (Fin D.d) (ZMod 2)) =
      mA D := a_val hB
  have h2 : ((SmallF2.gB D : GL (Fin D.d) (ZMod 2)) : Matrix (Fin D.d) (Fin D.d) (ZMod 2)) =
      mB D := b_val hB
  rw [h1, h2]
  rfl

end Generic

@[expose] noncomputable def unitsEquiv (D : VecData) (hB : BaseFacts D) :
    (NativeSporadic.seedMonoid 2 D.d 1 D.seedA D.seedB)ˣ ≃* SmallF2.J D :=
  (Units.mapEquiv (MulEquiv.submonoidCongr (seedMonoid_eq_closure hB))).trans
    (NativeSporadic.unitSeedEquiv (SmallF2.gA D) (SmallF2.gB D))

theorem unitsEquiv_val (D : VecData) (hB : BaseFacts D)
    (g : (NativeSporadic.seedMonoid 2 D.d 1 D.seedA D.seedB)ˣ) :
    (((unitsEquiv D hB g : SmallF2.J D) : GL (Fin D.d) (ZMod 2)) :
      Matrix (Fin D.d) (Fin D.d) (ZMod 2)) = g.val.val := rfl

theorem exists_unit_of_mem (D : VecData) (hB : BaseFacts D) (h : SmallF2.J D) :
    ∃ g : (NativeSporadic.seedMonoid 2 D.d 1 D.seedA D.seedB)ˣ,
      g.val.val = (((h : GL (Fin D.d) (ZMod 2)) : Matrix (Fin D.d) (Fin D.d) (ZMod 2))) := by
  refine ⟨(unitsEquiv D hB).symm h, ?_⟩
  have := unitsEquiv_val D hB ((unitsEquiv D hB).symm h)
  rw [MulEquiv.apply_symm_apply] at this
  exact this.symm

set_option maxRecDepth 4000 in
theorem exists_mem_Jmat (g : NativeSporadic.Co1) : ∃ h : Jmat,
    ((h : GL (Fin 24) (ZMod 2)) : Matrix (Fin 24) (Fin 24) (ZMod 2)) = g.val.val :=
  ⟨unitsEquiv dat co1BaseFacts g, unitsEquiv_val dat co1BaseFacts g⟩

set_option maxRecDepth 4000 in
theorem exists_co1_of_mem_Jmat (h : Jmat) : ∃ g : NativeSporadic.Co1,
    g.val.val = ((h : GL (Fin 24) (ZMod 2)) : Matrix (Fin 24) (Fin 24) (ZMod 2)) :=
  exists_unit_of_mem dat co1BaseFacts h

theorem exists_co1_matA :
    ∃ g : NativeSporadic.Co1, g.val.val = matA := by
  obtain ⟨g, hg⟩ := exists_co1_of_mem_Jmat genA
  exact ⟨g, hg.trans genA_val⟩

theorem exists_co1_matB :
    ∃ g : NativeSporadic.Co1, g.val.val = matB := by
  obtain ⟨g, hg⟩ := exists_co1_of_mem_Jmat genB
  exact ⟨g, hg.trans genB_val⟩

theorem range_co1Act (v : Vec24) :
    Set.range (fun g : NativeSporadic.Co1 => co1Act g v) = MulAction.orbit Jmat v := by
  ext x
  constructor
  · rintro ⟨g, rfl⟩
    obtain ⟨h, hh⟩ := exists_mem_Jmat g
    exact ⟨h, by show h • v = co1Act g v; rw [smul_eq_mulVec, hh]; rfl⟩
  · rintro ⟨h, rfl⟩
    obtain ⟨g, hg⟩ := exists_co1_of_mem_Jmat h
    exact ⟨g, by show co1Act g v = h • v; rw [smul_eq_mulVec, ← hg]; rfl⟩

end CFSG.Sporadic.Co1.Module
