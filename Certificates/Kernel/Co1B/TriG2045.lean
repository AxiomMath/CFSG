
module

public import Certificates.Kernel.Co1B.TriW2045B
public import Certificates.Kernel.Co1B.TriK2045
public import Certificates.Kernel.Co1B.Cent2045
public import CFSG.Certificates.Kernel.Co1BTriKSound
public import CFSG.Sporadic.Co1Block.TwoBTriBase
public import CFSG.Certificates.Kernel.Co1BTriSortSound

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCo1B.Tri2045

open CFSG.Sporadic.Co1Block CFSG.Sporadic.Co1Schreier CFSG.Sporadic.SmallF2 Matrix
  CFSG.KC.Co1T CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CertificateChecks.KernelSporSch.Co1Packed
  CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native

theorem twoBBray_len : twoBBray.length = 10 := rfl

theorem rows_getD {N : Nat} {M : Nat → Nat} {j : Nat} (hj : j < N) :
    ((List.range N).map fun i => unpack 24 24 (M i)).getD j CFSG.Sporadic.Co1Schreier.Native.one =
      unpack 24 24 (M j) := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hj]
  rfl

theorem bray_rows : twoBBm = (List.range 10).map fun i => unpack 24 24 (Cent2045.D2.M i) := by
  have e₁ : CFSG.Sporadic.Co1Block.Native.brayRows CFSG.Sporadic.Co1Schreier.Native.aR twoBD1 =
      ((List.range 43).map fun i => unpack 24 24 (Cent2045.D1.M i),
        (List.range 43).map fun i => unpack 24 24 (Cent2045.D1.MI i), true) :=
    CFSG.KS.SporSch.M24.dagIK_sound Cent2045.base_eq Cent2045.kD1
  have hj : ∀ j ∈ twoBBray, 3 < j ∧ j ≤ 43 := fun j hj => by
    simpa using List.all_eq_true.1 Cent2045.kI j hj
  have hbi : ∀ (i : Nat) (hi : i < twoBBray.length),
      Cent2045.D2.M i = Cent2045.D1.M (twoBBray[i] - 1) :=
    fun i hi => by simpa using CFSG.KS.SporSch.M24.bindFromK_sound (k := 0) Cent2045.kBind i hi
  apply List.ext_getElem (by simp [twoBBm, CFSG.Sporadic.Co1Block.Native.brayElts, twoBBray_len])
  intro i h₁ h₂
  have hi : i < twoBBray.length := by
    simpa [twoBBm, CFSG.Sporadic.Co1Block.Native.brayElts] using h₁
  simp only [twoBBm, CFSG.Sporadic.Co1Block.Native.brayElts, List.getElem_map,
    List.getElem_range, e₁]
  have hm := hj _ (List.getElem_mem hi)
  rw [rows_getD (by omega), hbi i hi]

theorem dag2_rows : (CFSG.Sporadic.Co1Schreier.Native.dag
    (CFSG.Sporadic.Co1Block.Native.brayElts
      (CFSG.Sporadic.Co1Block.Native.brayRows CFSG.Sporadic.Co1Schreier.Native.aR twoBD1)
      twoBBray) twoBD2).1 = (List.range 22).map fun i => unpack 24 24 (Cent2045.D2.M i) := by
  rw [CFSG.KS.SporSch.M24.dagIK_sound bray_rows Cent2045.kD2]

theorem matIdx_lt {m : Nat} (hm : m < 10) : matIdx m = m := by
  unfold matIdx
  rw [blt_of_lt hm]

theorem hTr {m : Nat} (hm : m < 12) :
    CFSG.KC.Co1F2.trK 24 (Cent2045.D2.M (matIdx m)) = TB.T m :=
  beq_of_true (TT.all m hm)

theorem kTA' : CFSG.KC.Co1F2.trK 24 PA = TB.T 12 := beq_of_true kTA

theorem kTZ' : CFSG.KC.Co1F2.trK 24 (mpowK (Cent2045.D2.M 2) 14) = TB.TZ := beq_of_true kTZ

theorem tris_len : twoBTris.length = 1365 := beq_of_true kLen

theorem kBase : ∀ k < 1365, baseOneK (TB.T 12) TB.PT TB.SV TB.SG TB.ST k = true :=
  slices_all (f := baseOneK (TB.T 12) TB.PT TB.SV TB.SG TB.ST) (L := 128) (NS := 11) B.all
    (by norm_num)

theorem kW {m : Nat} (hm : m < 12) : ∀ k < 1365, triOneK (TB.T m) TB.PT (TB.P m) k = true := by
  interval_cases m
  · exact slices_all (f := triOneK (TB.T 0) TB.PT (TB.P 0)) (L := 128) (NS := 11) W0.all (by norm_num)
  · exact slices_all (f := triOneK (TB.T 1) TB.PT (TB.P 1)) (L := 128) (NS := 11) W1.all (by norm_num)
  · exact slices_all (f := triOneK (TB.T 2) TB.PT (TB.P 2)) (L := 128) (NS := 11) W2.all (by norm_num)
  · exact slices_all (f := triOneK (TB.T 3) TB.PT (TB.P 3)) (L := 128) (NS := 11) W3.all (by norm_num)
  · exact slices_all (f := triOneK (TB.T 4) TB.PT (TB.P 4)) (L := 128) (NS := 11) W4.all (by norm_num)
  · exact slices_all (f := triOneK (TB.T 5) TB.PT (TB.P 5)) (L := 128) (NS := 11) W5.all (by norm_num)
  · exact slices_all (f := triOneK (TB.T 6) TB.PT (TB.P 6)) (L := 128) (NS := 11) W6.all (by norm_num)
  · exact slices_all (f := triOneK (TB.T 7) TB.PT (TB.P 7)) (L := 128) (NS := 11) W7.all (by norm_num)
  · exact slices_all (f := triOneK (TB.T 8) TB.PT (TB.P 8)) (L := 128) (NS := 11) W8.all (by norm_num)
  · exact slices_all (f := triOneK (TB.T 9) TB.PT (TB.P 9)) (L := 128) (NS := 11) W9.all (by norm_num)
  · exact slices_all (f := triOneK (TB.T 10) TB.PT (TB.P 10)) (L := 128) (NS := 11) W10.all
      (by norm_num)
  · exact slices_all (f := triOneK (TB.T 11) TB.PT (TB.P 11)) (L := 128) (NS := 11) W11.all
      (by norm_num)

theorem vecs : twoBTris = (List.range 1365).map (fun k => (tu TB.PT k, tv TB.PT k)) ∧
    (CFSG.Sporadic.Co1Block.Native.triVecs twoBTris).Nodup ∧
    ∀ y ∈ CFSG.Sporadic.Co1Block.Native.triVecs twoBTris, y < 2 ^ 24 ∧ y ≠ 0 ∧
      CFSG.KC.M1F2.vmF 24 (TB.T 12) y = y :=
  vecs_facts tris_len kTris kBase kSort

theorem tri_get {k : Nat} (hk : k < 1365) :
    twoBTris[k]'(by rw [tris_len]; exact hk) = (tu TB.PT k, tv TB.PT k) := by
  have := trisPK_sound kTris k (by rw [tris_len]; exact hk)
  simpa using this

theorem triP_eq {k : Nat} (hk : k < 1365) : triP k = (tu TB.PT k, tv TB.PT k) := by
  change twoBTris[k]! = _
  rw [getElem!_pos twoBTris k (by rw [tris_len]; exact hk), tri_get hk]

theorem inTriN_tri {k x : Nat} (hk : k < 1365) : inTriN (triP k) x = true ↔
    x ∈ [tu TB.PT k, tv TB.PT k, tu TB.PT k ^^^ tv TB.PT k] := by
  rw [inTriN_iff, triP_eq hk]
  simp

theorem vec_mem {k x : Nat} (hk : k < 1365)
    (hx : x ∈ [tu TB.PT k, tv TB.PT k, tu TB.PT k ^^^ tv TB.PT k]) :
    x ∈ CFSG.Sporadic.Co1Block.Native.triVecs twoBTris := by
  rw [CFSG.Sporadic.Co1Block.Native.triVecs, List.mem_flatMap]
  exact ⟨_, List.getElem_mem (by rw [tris_len]; exact hk), by rw [tri_get hk]; exact hx⟩

theorem tab_eq {k x : Nat} (hk : k < 1365)
    (hx : x ∈ [tu TB.PT k, tv TB.PT k, tu TB.PT k ^^^ tv TB.PT k]) :
    (CFSG.Sporadic.Co1Block.Native.triTable twoBTris)[x]! = k :=
  CFSG.KC.Co1B.triTable_get vecs.2.1 (fun y hy => (vecs.2.2 y hy).1)
    (by rw [tris_len]; exact hk) (by rw [tri_get hk]; exact hx)

theorem inTri_unique' {v : Vec24} {k k' : ℕ} (hk : k < 1365) (hk' : k' < 1365) (h : InTri v k)
    (h' : InTri v k') : k = k' := by
  obtain ⟨x, hx, rfl⟩ := h
  obtain ⟨x', hx', he⟩ := h'
  rw [inTriN_tri hk] at hx
  rw [inTriN_tri hk'] at hx'
  have hxx : x = x' :=
    toVecD_injective (vecs.2.2 x (vec_mem hk hx)).1 (vecs.2.2 x' (vec_mem hk' hx')).1 he
  subst hxx
  rw [← tab_eq hk hx, ← tab_eq hk' hx']

theorem tri_act {PM T P : Nat} (hT : CFSG.KC.Co1F2.trK 24 PM = T)
    (hW : ∀ k < 1365, triOneK T TB.PT P k = true) {k : Nat} (hk : k < 1365) :
    pg 11 (mask 11) P k < 1365 ∧ ∀ x ∈ [tu TB.PT k, tv TB.PT k, tu TB.PT k ^^^ tv TB.PT k],
      CFSG.Sporadic.Co1Schreier.Native.act (unpack 24 24 PM) x ∈
        [tu TB.PT (pg 11 (mask 11) P k), tv TB.PT (pg 11 (mask 11) P k),
          tu TB.PT (pg 11 (mask 11) P k) ^^^ tv TB.PT (pg 11 (mask 11) P k)] := by
  obtain ⟨h1, h2⟩ := triOneK_sound (hW k hk) hk
  exact ⟨h1, fun x hx => by rw [act_unpack hT]; exact h2 x hx⟩

theorem triPres_k {PM T P : Nat} {g : GL24} (hg : MRep (unpack 24 24 PM) g)
    (hT : CFSG.KC.Co1F2.trK 24 PM = T) (hW : ∀ k < 1365, triOneK T TB.PT P k = true)
    {k : Nat} (hk : k < 1365) : ∀ v, InTri v k →
      InTri (((g : GL24) : Matrix (Fin 24) (Fin 24) (ZMod 2)) *ᵥ v) (pg 11 (mask 11) P k) := by
  rintro v ⟨x, hx, rfl⟩
  obtain ⟨h1, h2⟩ := tri_act hT hW hk
  exact ⟨_, (inTriN_tri h1).2 (h2 x ((inTriN_tri hk).1 hx)), MRep.mulVec hg x⟩

theorem unpack_get' {n w P i : Nat} (hi : i < n) : (unpack n w P)[i]! = pg w (mask w) P i := by
  rw [getElem!_pos (unpack n w P) i (by simp [unpack, hi])]
  simp [unpack]

theorem triOK_of {PM T P : Nat} (hT : CFSG.KC.Co1F2.trK 24 PM = T)
    (hW : ∀ k < 1365, triOneK T TB.PT P k = true) :
    CFSG.Sporadic.Co1Block.Native.triOK (CFSG.Sporadic.Co1Block.Native.triTable twoBTris)
        twoBTris (unpack 24 24 PM) = true ∧
      CFSG.Sporadic.Co1Block.Native.triPerm (CFSG.Sporadic.Co1Block.Native.triTable twoBTris)
        twoBTris (unpack 24 24 PM) = unpack 1365 11 P := by
  have key : ∀ k (hk : k < 1365), ∀ x ∈ [tu TB.PT k, tv TB.PT k, tu TB.PT k ^^^ tv TB.PT k],
      (CFSG.Sporadic.Co1Block.Native.triTable twoBTris)[
        CFSG.Sporadic.Co1Schreier.Native.act (unpack 24 24 PM) x]! = pg 11 (mask 11) P k :=
    fun k hk x hx => tab_eq (tri_act hT hW hk).1 ((tri_act hT hW hk).2 x hx)
  constructor
  · unfold CFSG.Sporadic.Co1Block.Native.triOK
    rw [List.all_eq_true]
    intro p hp
    obtain ⟨k, hk', rfl⟩ := List.getElem_of_mem hp
    have hk : k < 1365 := by rwa [tris_len] at hk'
    rw [tri_get hk]
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq]
    rw [key k hk _ (by simp), key k hk _ (by simp), key k hk _ (by simp)]
    exact ⟨⟨(tri_act hT hW hk).1, rfl⟩, rfl⟩
  · unfold CFSG.Sporadic.Co1Block.Native.triPerm
    apply Array.ext
    · simp [tris_len, unpack]
    · intro i h1 h2
      have hi : i < 1365 := by simpa [tris_len] using h1
      simp only [List.getElem_toArray, List.getElem_map]
      rw [tri_get hi, key i hi _ (by simp)]
      simp [unpack]

theorem rep_co3Pow {n : Nat} {t : Array Nat} {g : Equiv.Perm (Fin n)} (ht : Rep n t g) :
    ∀ e, Rep n (CFSG.Sporadic.Schreier.Co3.co3PowA n t e) (g ^ e)
  | 0 => by
    simp only [CFSG.Sporadic.Schreier.Co3.co3PowA, pow_zero]
    exact rep_idA
  | e + 1 => by
    simp only [CFSG.Sporadic.Schreier.Co3.co3PowA, pow_succ']
    exact rep_compA ht (rep_co3Pow ht e)

theorem idA_eq : unpack 1365 11 (pidn 1365 11) = idA 1365 := CFSG.KS.Prim.idK_sound kId

theorem pow_eq_one_of {P e : Nat} {g : Equiv.Perm (Fin 1365)} (hg : Rep 1365 (unpack 1365 11 P) g)
    (h : CFSG.KS.Prim.powEqK 1365 11 (mask 11) (1365 * 11) (pidn 1365 11) P e (pidn 1365 11) =
      true) : g ^ e = 1 := by
  have := rep_co3Pow hg e
  rw [CFSG.KS.Prim.powEqK_sound h, idA_eq] at this
  exact this.unique rep_idA

theorem rep_mpow {X : Nat} {g : GL24} (hX : MRep (unpack 24 24 X) g) :
    ∀ e, MRep (unpack 24 24 (mpowK X e)) (g ^ (e + 1))
  | 0 => by
    have e0 : mpowK X 0 = X := rfl
    rw [e0, zero_add, pow_one]
    exact hX
  | e + 1 => by
    rw [← mpowK_unpack, pow_succ]
    exact (rep_mpow hX e).mul hX

theorem toVecD_act_inj {X : CFSG.Sporadic.Co1Schreier.Native.Rows} {v w : Nat} (hw : w < 2 ^ 24)
    (h : toVecD 24 (CFSG.Sporadic.Co1Schreier.Native.act X v) = toVecD 24 w) :
    CFSG.Sporadic.Co1Schreier.Native.act X v = w :=
  toVecD_injective (act_lt _ _) hw h

theorem act_ne {P T v : Nat} {g : GL24} (hg : MRep (unpack 24 24 P) g)
    (hT : CFSG.KC.Co1F2.trK 24 P = T) (hv : v < 2 ^ 24)
    (hne : CFSG.KC.M1F2.vmF 24 T v ≠ v) : g ≠ 1 := by
  rintro rfl
  have h := MRep.mulVec hg v
  rw [Units.val_one, one_mulVec] at h
  have := toVecD_act_inj hv h.symm
  rw [act_unpack hT] at this
  exact hne this

theorem act_ne2 {P P' T T' v : Nat} {g h : GL24} (hg : MRep (unpack 24 24 P) g)
    (hh : MRep (unpack 24 24 P') h) (hT : CFSG.KC.Co1F2.trK 24 P = T)
    (hT' : CFSG.KC.Co1F2.trK 24 P' = T')
    (hne : CFSG.KC.M1F2.vmF 24 T v ≠ CFSG.KC.M1F2.vmF 24 T' v) : g ≠ h := by
  rintro rfl
  have e := (MRep.mulVec hg v).symm.trans (MRep.mulVec hh v)
  have := toVecD_act_inj (act_lt _ _) e
  rw [act_unpack hT, act_unpack hT'] at this
  exact hne this

theorem act_ne12 {P P' T T' v : Nat} {g h : GL24} (hg : MRep (unpack 24 24 P) g)
    (hh : MRep (unpack 24 24 P') h) (hT : CFSG.KC.Co1F2.trK 24 P = T)
    (hT' : CFSG.KC.Co1F2.trK 24 P' = T') (hv : v < 2 ^ 24)
    (hne : CFSG.KC.M1F2.vmF 24 T (CFSG.KC.M1F2.vmF 24 T' v) ≠ v) : g * h ≠ 1 := by
  intro e
  have h1 := mulVec_mul' g h (toVecD 24 v)
  rw [e, Units.val_one, one_mulVec, MRep.mulVec hh, MRep.mulVec hg] at h1
  have := toVecD_act_inj hv h1.symm
  rw [act_unpack hT', act_unpack hT] at this
  exact hne this

section Grp

theorem gens_rep : List.Forall₂ MRep twoBBm (brayEltsG A₁ twoBD1 twoBBray) :=
  rep_brayElts rep_A₁ (centCheck_parts Cent2045.twoB_cent_check).1

abbrev bG (j : Nat) : GL24 := (brayEltsG A₁ twoBD1 twoBBray).getD j 1

theorem bG_mem (j : Nat) : bG j ∈ twoBE :=
  getD_mem_of_forall (fun _ hg => Subgroup.subset_closure hg) j

theorem bG_rep {j : Nat} (hj : j < 10) : MRep (unpack 24 24 (Cent2045.D2.M j)) (bG j) := by
  have := getD_rep gens_rep MRep.one j
  rwa [bray_rows, rows_getD hj] at this

abbrev dG (j : Nat) : GL24 := (strongDagG A₁ twoBD1 twoBBray twoBD2).getD j 1

theorem dG_mem (j : Nat) : dG j ∈ twoBE := getD_mem_of_forall strongDag_mem j

theorem dG_rep {j : Nat} (hj : j < 22) : MRep (unpack 24 24 (Cent2045.D2.M j)) (dG j) := by
  have := getD_rep (rep_strongDag rep_A₁ Cent2045.twoB_cent_check) MRep.one j
  rwa [dag2_rows, rows_getD hj] at this

theorem triPres_of {m : Nat} (hm : m < 12) {g : GL24}
    (hg : MRep (unpack 24 24 (Cent2045.D2.M (matIdx m))) g) : TriPres g := fun _ hk =>
  ⟨_, (tri_act (hTr hm) (kW hm) hk).1, triPres_k hg (hTr hm) (kW hm) hk⟩

theorem triPres_mem {g : GL24} (hg : g ∈ twoBE) : TriPres g := by
  have hg' : g ∈ (Subgroup.closure {g | g ∈ brayEltsG A₁ twoBD1 twoBBray}).toSubmonoid := hg
  rw [Subgroup.closure_toSubmonoid_of_finite] at hg'
  clear hg
  induction hg' using Submonoid.closure_induction with
  | mem x hx =>
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hx
    have hl : (brayEltsG A₁ twoBD1 twoBBray).length = 10 := by
      rw [← forall₂_length gens_rep, bray_rows]
      simp
    have hj' : j < 10 := by omega
    have h := bG_rep hj'
    rw [bG, List.getD_eq_getElem _ _ hj] at h
    exact triPres_of (m := j) (by omega) (by rw [matIdx_lt hj']; exact h)
  | one => exact triPres_one
  | mul x y _ _ hx hy => exact triPres_mul hx hy

theorem exists_triE (g : twoBE) (k : Fin 1365) : ∃ k' : Fin 1365, ∀ v, InTri v k →
    InTri ((((g : GL24) : GL24) : Matrix (Fin 24) (Fin 24) (ZMod 2)) *ᵥ v) k' := by
  obtain ⟨k', hk', h⟩ := triPres_mem g.2 k k.2
  exact ⟨⟨k', hk'⟩, h⟩

@[expose] def triActE (g : twoBE) (k : Fin 1365) : Fin 1365 := (exists_triE g k).choose

theorem triActE_spec (g : twoBE) (k : Fin 1365) : ∀ v, InTri v k →
    InTri ((((g : GL24) : GL24) : Matrix (Fin 24) (Fin 24) (ZMod 2)) *ᵥ v) (triActE g k) :=
  (exists_triE g k).choose_spec

theorem triActE_eq {g : twoBE} {k k' : Fin 1365}
    (h : InTri ((((g : GL24) : GL24) : Matrix (Fin 24) (Fin 24) (ZMod 2)) *ᵥ triV k) k') :
    triActE g k = k' :=
  Fin.ext (inTri_unique' (triActE g k).2 k'.2 (triActE_spec g k _ (triV_mem k)) h)

@[expose, instance_reducible] def triMulE : MulAction twoBE (Fin 1365) where
  smul := triActE
  one_smul k := triActE_eq (by
    change InTri (((1 : GL24) : Matrix (Fin 24) (Fin 24) (ZMod 2)) *ᵥ triV k) k
    rw [Units.val_one, one_mulVec]
    exact triV_mem k)
  mul_smul g h k := triActE_eq (by
    change InTri (((((g : GL24) * (h : GL24) : GL24)) : Matrix (Fin 24) (Fin 24) (ZMod 2)) *ᵥ
      triV k) (triActE g (triActE h k))
    rw [mulVec_mul']
    exact triActE_spec g _ _ (triActE_spec h k _ (triV_mem k)))

@[expose] def φE : twoBE →* Equiv.Perm (Fin 1365) :=
  @MulAction.toPermHom twoBE (Fin 1365) _ triMulE

theorem φE_apply (g : twoBE) (k : Fin 1365) : φE g k = triActE g k := rfl

theorem rep_φE {g : twoBE} {m : Nat} (hm : m < 12)
    (hg : MRep (unpack 24 24 (Cent2045.D2.M (matIdx m))) (g : GL24)) :
    Rep 1365 (unpack 1365 11 (TB.P m)) (φE g) := by
  intro k
  rw [φE_apply, triActE_eq (k' := ⟨_, (tri_act (hTr hm) (kW hm) k.2).1⟩)
    (triPres_k hg (hTr hm) (kW hm) k.2 _ (triV_mem k)), unpack_get' k.2]

theorem repA : MRep (unpack 24 24 PA) A₁ := aR_u ▸ rep_A₁

theorem bG3 : bG 3 = A₁ := by
  have h := bG_rep (j := 3) (by norm_num)
  rw [beq_of_true k3] at h
  exact h.eq repA

abbrev aE : twoBE := ⟨A₁, bG3 ▸ bG_mem 3⟩

abbrev bE (j : Nat) : twoBE := ⟨bG j, bG_mem j⟩

abbrev zE : twoBE := bE 2 ^ 15

theorem φE_a : φE aE = 1 := by
  refine Equiv.ext fun k => ?_
  rw [φE_apply, Equiv.Perm.one_apply]
  apply triActE_eq
  refine ⟨(triP k).1, by simp [inTriN], ?_⟩
  have hx : (triP k).1 ∈ CFSG.Sporadic.Co1Block.Native.triVecs twoBTris :=
    vec_mem k.2 (by rw [triP_eq k.2]; simp)
  change ((A₁ : GL24) : Matrix (Fin 24) (Fin 24) (ZMod 2)) *ᵥ toVecD 24 (triP k).1 =
    toVecD 24 (triP k).1
  rw [MRep.mulVec repA, act_unpack kTA', (vecs.2.2 _ hx).2.2]

theorem φE_z : φE zE = 1 := by
  rw [map_pow]
  have h := rep_φE (g := bE 2) (m := 2) (by norm_num) (bG_rep (j := 2) (by norm_num))
  exact pow_eq_one_of h kP15

end Grp

end CertificateChecks.KernelCo1B.Tri2045

end
