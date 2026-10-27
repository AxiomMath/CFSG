module

public import CFSG.Quasithin.Recognition.St84.HeisF4
public import CFSG.Assembly.Defs
public import CFSG.LocalAnalysis.ComponentClassification.J2CoverAutCheckInputs
public import CFSG.Sporadic.SmallOddCore.CentSpec
public import CFSG.Sporadic.SmallOddCore.LocalCheck

public section

namespace CFSG.Quasithin.F112R.St84.AutJ2Model

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.SmallOddCore
open CFSG.Sporadic.SmallOddCore.Native
open CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Native
open CFSG.ComponentClassification.J2Cover CFSG.Fischer
open CFSG.Quasithin.F112R.St84.Heis

@[expose] def sylT : List Table :=
  (sylowStrong.extract 0 3).toList.map fun t => t.map UInt32.ofNat

@[expose] def abuT : List Table :=
  [autStrong[0]!.map UInt32.ofNat, autStrong[1]!.map UInt32.ofNat, outerArr.map UInt32.ofNat]

@[expose] def gWT : Table :=
  wordTbl 315 abuT [2, 3, 1, 2, 2, 1, 3, 3, 3, 3, 3, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 3, 3, 1]

@[expose] def g1T : Table := wordTbl 315 abuT [2, 3, 2]

@[expose] def q2T : List Table :=
  [[2, 3, 1, 3, 3, 3], [1, 1, 3, 3, 3, 3], [2, 1, 2, 1], [2, 3, 3, 1]].map (wordTbl 315 sylT)

@[expose] def umT : Table := wordTbl 315 sylT [2]

@[expose] def vmT : Table := wordTbl 315 q2T [1, 1, 2]

@[expose] def e1RT : Table := wordTbl 315 sylT [3, 1, 3, 1, 3, 3]

@[expose] def e2RT : Table := wordTbl 315 sylT [1, 1, 1, 3, 2, 1]

@[expose] def f1RT : Table := wordTbl 315 sylT [2, 1, 3, 2, 1, 3]

@[expose] def f2RT : Table := wordTbl 315 sylT [1, 1, 1, 2, 3, 1]

@[expose] def tmRT : Table := wordTbl 315 sylT [1, 1, 3, 1, 2, 3]

@[expose] def gmRT : Table := wordTbl 315 sylT [1, 1, 1, 2, 1]

@[expose] def bmRT : Table := wordTbl 315 (sylT ++ [g1T]) [2, 4, 3, 4, 2, 3]

@[expose] def rmRT : Table := wordTbl 315 (sylT ++ [g1T]) [3, 4, 3, 4, 1, 4]

@[expose] def q1mOfCode (k : Nat) : Q1M :=
  ⟨⟨k % 4, Nat.mod_lt _ (by norm_num)⟩, ⟨(k / 4) % 4, Nat.mod_lt _ (by norm_num)⟩,
    ⟨(k / 16) % 4, Nat.mod_lt _ (by norm_num)⟩⟩

@[expose] def q1mList : List Q1M := List.ofFn fun i : Fin 64 => q1mOfCode i.val

@[expose] def q1mIdx (q : Q1M) : Fin 64 :=
  ⟨q.a.code.val + 4 * q.b.code.val + 16 * q.c.code.val, by
    have h1 := q.a.code.isLt
    have h2 := q.b.code.isLt
    have h3 := q.c.code.isLt
    omega⟩

theorem q1mOfCode_idx (q : Q1M) : q1mOfCode (q1mIdx q).val = q := by
  obtain ⟨⟨a, ha⟩, ⟨b, hb⟩, ⟨c, hc⟩⟩ := q
  simp only [q1mOfCode, q1mIdx, Nat.reduceMod]
  ext <;> simp <;> omega

theorem q1mList_length : q1mList.length = 64 := by
  simp [q1mList]

theorem mem_q1mList (q : Q1M) : q ∈ q1mList := by
  rw [q1mList, ← q1mOfCode_idx q]
  exact List.mem_ofFn.mpr ⟨q1mIdx q, rfl⟩

noncomputable abbrev E1R : Equiv.Perm (Fin 315) := tp 315 e1RT
noncomputable abbrev E2R : Equiv.Perm (Fin 315) := tp 315 e2RT
noncomputable abbrev F1R : Equiv.Perm (Fin 315) := tp 315 f1RT
noncomputable abbrev F2R : Equiv.Perm (Fin 315) := tp 315 f2RT
noncomputable abbrev rmR : Equiv.Perm (Fin 315) := tp 315 rmRT
noncomputable abbrev bmR : Equiv.Perm (Fin 315) := tp 315 bmRT
noncomputable abbrev tmR : Equiv.Perm (Fin 315) := tp 315 tmRT
noncomputable abbrev gmR : Equiv.Perm (Fin 315) := tp 315 gmRT
noncomputable abbrev umR : Equiv.Perm (Fin 315) := tp 315 umT
noncomputable abbrev vmR : Equiv.Perm (Fin 315) := tp 315 vmT

noncomputable def EmR (a : F4) : Equiv.Perm (Fin 315) :=
  E1R ^ (a.code.val % 2) * E2R ^ (a.code.val / 2)

noncomputable def FmR (b : F4) : Equiv.Perm (Fin 315) :=
  F1R ^ (b.code.val % 2) * F2R ^ (b.code.val / 2)

noncomputable def FmInvR (b : F4) : Equiv.Perm (Fin 315) :=
  (F2R⁻¹) ^ (b.code.val / 2) * (F1R⁻¹) ^ (b.code.val % 2)

noncomputable def κR (q : Q1M) : Equiv.Perm (Fin 315) :=
  EmR q.a * FmR q.b *
    (E1R * FmR (q.c + q.a * q.b) * E1R⁻¹ * (FmR (q.c + q.a * q.b))⁻¹)

@[expose] def EmT (a : F4) : Table :=
  compT 315 (powT 315 (a.code.val % 2) e1RT) (powT 315 (a.code.val / 2) e2RT)

@[expose] def FmT (b : F4) : Table :=
  compT 315 (powT 315 (b.code.val % 2) f1RT) (powT 315 (b.code.val / 2) f2RT)

@[expose] def FmInvT (b : F4) : Table :=
  compT 315 (powT 315 (b.code.val / 2) (invT 315 f2RT))
    (powT 315 (b.code.val % 2) (invT 315 f1RT))

@[expose] def κRT (q : Q1M) : Table :=
  let w := q.c + q.a * q.b
  compT 315 (compT 315 (EmT q.a) (FmT q.b))
    (compT 315 (compT 315 (compT 315 e1RT (FmT w)) (invT 315 e1RT)) (FmInvT w))

@[expose] def autJ2Tbls : List Table :=
  sylT ++ abuT ++ [gWT, g1T] ++ q2T ++
    [umT, vmT, e1RT, e2RT, f1RT, f2RT, tmRT, gmRT, bmRT, rmRT]

@[expose] def autJ2VtxC0 (_ : Unit := ()) : Bool :=
  autJ2Tbls.all (permOK 315) && autJ2Tbls.all fun t => invOK 315 t (invT 315 t)

@[expose] def autJ2VtxC1 (_ : Unit := ()) : Bool :=
  enumOK 315 300 256 sylT && enumOK 315 4000 3840 (sylT ++ [gWT]) &&
    enumOK 315 3000 2304 (sylT ++ [g1T])

@[expose] def autJ2VtxC2 (_ : Unit := ()) : Bool :=
  enumOK 315 100 32 q2T && normOK 315 100 q2T (sylT ++ [gWT])

@[expose] def autJ2VtxC3 (_ : Unit := ()) : Bool :=
  invoOK 315 umT && !(inP (natArr umT)) && invoOK 315 vmT &&
    !(commTT 315 vmT q2T[0]!) && commTT 315 umT vmT

@[expose] def κArr (_ : Unit := ()) : Array Table :=
  Array.ofFn (n := 64) fun i => κRT (q1mOfCode i.val)

theorem κArr_get (q : Q1M) : (κArr ())[(q1mIdx q).val]! = κRT q := by
  have h : (q1mIdx q).val < 64 := (q1mIdx q).isLt
  simp only [κArr]
  rw [getElem!_pos _ _ (by simpa using h), Array.getElem_ofFn, q1mOfCode_idx]

@[expose] def autJ2VtxC4Hom (_ : Unit := ()) : Bool :=
  let L := q1mList
  let K := κArr ()
  L.all fun x => L.all fun y =>
    tblEq 315 K[(q1mIdx (x * y)).val]! (compT 315 K[(q1mIdx x).val]! K[(q1mIdx y).val]!)

@[expose] def autJ2VtxC4Inj (_ : Unit := ()) : Bool :=
  let L := q1mList
  let K := κArr ()
  L.all fun x => x = 1 || !tblEq 315 K[(q1mIdx x).val]! (idT 315)

@[expose] def autJ2VtxC4 (_ : Unit := ()) : Bool := autJ2VtxC4Hom () && autJ2VtxC4Inj ()

@[expose] def conjGenOK (c : Table) (α : MulAut Q1M) : Bool :=
  [e1, e2, f1, f2].all fun g =>
    tblEq 315 (conjT 315 c (invT 315 c) (κRT g)) (κRT (α g))

@[expose] def autJ2VtxC5 (_ : Unit := ()) : Bool :=
  conjGenOK rmRT ρM && conjGenOK bmRT βM && conjGenOK tmRT τM && conjGenOK gmRT γM

@[expose] def autJ2VtxC6 (_ : Unit := ()) : Bool :=
  enumOK 315 100 36 [rmRT, bmRT, tmRT, gmRT] &&
    normOK 315 100 [e1RT, e2RT, f1RT, f2RT] (sylT ++ [g1T])

@[expose] def q1Gens : List Table := [e1RT, e2RT, f1RT, f2RT]

@[expose] def autJ2VtxC7 (_ : Unit := ()) : Bool :=
  enumOK 315 100 64 q1Gens

theorem autJ2VtxC0_perm (h : autJ2VtxC0 () = true) {t : Table} (ht : t ∈ autJ2Tbls) :
    permOK 315 t = true := by
  have h' := h
  simp only [autJ2VtxC0, Bool.and_eq_true, List.all_eq_true] at h'
  exact h'.1 t ht

theorem autJ2VtxC0_inv (h : autJ2VtxC0 () = true) {t : Table} (ht : t ∈ autJ2Tbls) :
    invOK 315 t (invT 315 t) = true := by
  have h' := h
  simp only [autJ2VtxC0, Bool.and_eq_true, List.all_eq_true] at h'
  exact h'.2 t ht

theorem autJ2VtxC3_spec (h : autJ2VtxC3 () = true) :
    invoOK 315 umT = true ∧ inP (natArr umT) = false ∧ invoOK 315 vmT = true ∧
      commTT 315 vmT q2T[0]! = false ∧ commTT 315 umT vmT = true := by
  have h' := h
  simp only [autJ2VtxC3, Bool.and_eq_true, Bool.not_eq_true'] at h'
  exact ⟨h'.1.1.1.1, h'.1.1.1.2, h'.1.1.2, h'.1.2, h'.2⟩

theorem rep_EmT (h0 : autJ2VtxC0 () = true) (a : F4) : Rep 315 (EmT a) (EmR a) := by
  have h1 := autJ2VtxC0_perm h0 (t := e1RT) (by simp [autJ2Tbls])
  have h2 := autJ2VtxC0_perm h0 (t := e2RT) (by simp [autJ2Tbls])
  rw [EmT, EmR]
  exact Rep.compT (Rep.powT (by norm_num) (rep_tp h1) _)
    (Rep.powT (by norm_num) (rep_tp h2) _)

theorem rep_FmT (h0 : autJ2VtxC0 () = true) (b : F4) : Rep 315 (FmT b) (FmR b) := by
  have h1 := autJ2VtxC0_perm h0 (t := f1RT) (by simp [autJ2Tbls])
  have h2 := autJ2VtxC0_perm h0 (t := f2RT) (by simp [autJ2Tbls])
  rw [FmT, FmR]
  exact Rep.compT (Rep.powT (by norm_num) (rep_tp h1) _)
    (Rep.powT (by norm_num) (rep_tp h2) _)

theorem rep_FmInvT (h0 : autJ2VtxC0 () = true) (b : F4) :
    Rep 315 (FmInvT b) (FmInvR b) := by
  have h1 := autJ2VtxC0_perm h0 (t := f1RT) (by simp [autJ2Tbls])
  have h2 := autJ2VtxC0_perm h0 (t := f2RT) (by simp [autJ2Tbls])
  have i1 := autJ2VtxC0_inv h0 (t := f1RT) (by simp [autJ2Tbls])
  have i2 := autJ2VtxC0_inv h0 (t := f2RT) (by simp [autJ2Tbls])
  rw [FmInvT, FmInvR]
  exact Rep.compT (Rep.powT (by norm_num) (rep_invT (rep_tp h2) i2) _)
    (Rep.powT (by norm_num) (rep_invT (rep_tp h1) i1) _)

theorem FmInvR_eq_inv (b : F4) : FmInvR b = (FmR b)⁻¹ := by
  rw [FmInvR, FmR, mul_inv_rev, inv_pow, inv_pow]

theorem rep_κRT (h0 : autJ2VtxC0 () = true) (q : Q1M) : Rep 315 (κRT q) (κR q) := by
  have h1 := autJ2VtxC0_perm h0 (t := e1RT) (by simp [autJ2Tbls])
  have hE1 : Rep 315 e1RT E1R := rep_tp h1
  have hE1i : Rep 315 (invT 315 e1RT) E1R⁻¹ :=
    rep_invT (rep_tp h1) (autJ2VtxC0_inv h0 (t := e1RT) (by simp [autJ2Tbls]))
  have hFinv : Rep 315 (FmInvT (q.c + q.a * q.b)) (FmR (q.c + q.a * q.b))⁻¹ := by
    rw [← FmInvR_eq_inv]
    exact rep_FmInvT h0 _
  simp only [κRT, κR]
  exact Rep.compT (Rep.compT (rep_EmT h0 q.a) (rep_FmT h0 q.b))
    (Rep.compT (Rep.compT (Rep.compT hE1 (rep_FmT h0 _)) hE1i) hFinv)

theorem autJ2VtxC4Hom_spec (h : autJ2VtxC4Hom () = true) (x y : Q1M) :
    tblEq 315 (κRT (x * y)) (compT 315 (κRT x) (κRT y)) = true := by
  have h' := h
  simp only [autJ2VtxC4Hom, List.all_eq_true] at h'
  have hxy := h' x (mem_q1mList x) y (mem_q1mList y)
  rwa [κArr_get x, κArr_get y, κArr_get (x * y)] at hxy

theorem autJ2VtxC4Inj_spec (h : autJ2VtxC4Inj () = true) {x : Q1M} (hx : x ≠ 1) :
    tblEq 315 (κRT x) (idT 315) = false := by
  have h' := h
  simp only [autJ2VtxC4Inj, List.all_eq_true, Bool.or_eq_true, decide_eq_true_eq] at h'
  have hx' := h' x (mem_q1mList x)
  rw [κArr_get x] at hx'
  rcases hx' with h1 | h1
  · exact absurd h1 hx
  · simpa using h1

theorem κR_one : κR 1 = 1 := by
  have h1 : (1 : Q1M) = ⟨0, 0, 0⟩ := rfl
  rw [h1]
  show EmR 0 * FmR 0 * (E1R * FmR (0 + 0 * 0) * E1R⁻¹ * (FmR (0 + 0 * 0))⁻¹) = 1
  have h0 : (0 : F4) = ⟨0⟩ := rfl
  rw [h0]
  have hz : (⟨0⟩ : F4) + ⟨0⟩ * ⟨0⟩ = ⟨0⟩ := rfl
  rw [hz]
  simp [EmR, FmR]

theorem κR_mul (h0 : autJ2VtxC0 () = true) (h4 : autJ2VtxC4 () = true) (x y : Q1M) :
    κR (x * y) = κR x * κR y := by
  have h4' := h4
  simp only [autJ2VtxC4, Bool.and_eq_true] at h4'
  have hhom : autJ2VtxC4Hom () = true := h4'.1
  exact (tblEq_iff_eq (rep_κRT h0 (x * y))
    (Rep.compT (rep_κRT h0 x) (rep_κRT h0 y))).1 (autJ2VtxC4Hom_spec hhom x y)

theorem κR_inv (h0 : autJ2VtxC0 () = true) (h4 : autJ2VtxC4 () = true) (y : Q1M) :
    κR y⁻¹ = (κR y)⁻¹ := by
  have h := κR_mul h0 h4 y y⁻¹
  rw [mul_inv_cancel, κR_one] at h
  calc κR y⁻¹ = 1 * κR y⁻¹ := (one_mul _).symm
    _ = ((κR y)⁻¹ * κR y) * κR y⁻¹ := by rw [inv_mul_cancel]
    _ = (κR y)⁻¹ * (κR y * κR y⁻¹) := by group
    _ = (κR y)⁻¹ * 1 := by rw [← h]
    _ = (κR y)⁻¹ := mul_one _

theorem κR_injective (h0 : autJ2VtxC0 () = true) (h4 : autJ2VtxC4 () = true) :
    Function.Injective κR := by
  intro x y hxy
  by_contra hne
  have hprod : x * y⁻¹ ≠ 1 := by
    intro h1
    apply hne
    calc x = x * y⁻¹ * y := by group
      _ = 1 * y := by rw [h1]
      _ = y := one_mul y
  have h4' := h4
  simp only [autJ2VtxC4, Bool.and_eq_true] at h4'
  have hinj : autJ2VtxC4Inj () = true := h4'.2
  have htab : tblEq 315 (κRT (x * y⁻¹)) (idT 315) = false :=
    autJ2VtxC4Inj_spec hinj hprod
  have hκ : κR (x * y⁻¹) = 1 := by
    rw [κR_mul h0 h4, hxy, κR_inv h0 h4, mul_inv_cancel]
  have htrue : tblEq 315 (κRT (x * y⁻¹)) (idT 315) = true :=
    (tblEq_iff_eq (rep_κRT h0 _) (Rep.idT (by norm_num))).2 hκ
  rw [htrue] at htab
  exact Bool.noConfusion htab

theorem conjGenOK_spec {c : Table} {α : MulAut Q1M} (h : conjGenOK c α = true)
    {g : Q1M} (hg : g ∈ [e1, e2, f1, f2]) :
    tblEq 315 (conjT 315 c (invT 315 c) (κRT g)) (κRT (α g)) = true := by
  have h' := h
  simp only [conjGenOK, List.all_eq_true] at h'
  exact h' g hg

theorem κR_conj_gen (h0 : autJ2VtxC0 () = true) {c : Table}
    {cR : Equiv.Perm (Fin 315)} {α : MulAut Q1M}
    (hc : Rep 315 c cR) (hci : Rep 315 (invT 315 c) cR⁻¹) (hall : conjGenOK c α = true)
    {g : Q1M} (hg : g ∈ [e1, e2, f1, f2]) :
    cR * κR g * cR⁻¹ = κR (α g) := by
  have hL : Rep 315 (conjT 315 c (invT 315 c) (κRT g)) (cR * κR g * cR⁻¹) :=
    rep_conjT hc hci (rep_κRT h0 g)
  have hR : Rep 315 (κRT (α g)) (κR (α g)) := rep_κRT h0 (α g)
  exact (tblEq_iff_eq hL hR).1 (conjGenOK_spec hall hg)

theorem κR_conj (h0 : autJ2VtxC0 () = true) (h4 : autJ2VtxC4 () = true) {c : Table}
    {cR : Equiv.Perm (Fin 315)} {α : MulAut Q1M}
    (hc : Rep 315 c cR) (hci : Rep 315 (invT 315 c) cR⁻¹) (hall : conjGenOK c α = true) :
    ∀ q : Q1M, cR * κR q * cR⁻¹ = κR (α q) := by
  let φ : Q1M →* Equiv.Perm (Fin 315) :=
    { toFun := fun q => cR * κR q * cR⁻¹
      map_one' := by simp [κR_one]
      map_mul' := by
        intro x y
        rw [κR_mul h0 h4]
        group }
  let ψ : Q1M →* Equiv.Perm (Fin 315) :=
    { toFun := fun q => κR (α q)
      map_one' := by rw [map_one, κR_one]
      map_mul' := by
        intro x y
        rw [map_mul, κR_mul h0 h4] }
  have hφψ : φ = ψ :=
    Heis.hom_ext (φ := φ) (ψ := ψ)
      (κR_conj_gen h0 hc hci hall (by simp))
      (κR_conj_gen h0 hc hci hall (by simp))
      (κR_conj_gen h0 hc hci hall (by simp))
      (κR_conj_gen h0 hc hci hall (by simp))
  intro q
  exact DFunLike.congr_fun hφψ q

theorem autJ2VtxC5_rm (h : autJ2VtxC5 () = true) : conjGenOK rmRT ρM = true := by
  have h' := h
  simp only [autJ2VtxC5, Bool.and_eq_true] at h'
  exact h'.1.1.1

theorem autJ2VtxC5_bm (h : autJ2VtxC5 () = true) : conjGenOK bmRT βM = true := by
  have h' := h
  simp only [autJ2VtxC5, Bool.and_eq_true] at h'
  exact h'.1.1.2

theorem autJ2VtxC5_tm (h : autJ2VtxC5 () = true) : conjGenOK tmRT τM = true := by
  have h' := h
  simp only [autJ2VtxC5, Bool.and_eq_true] at h'
  exact h'.1.2

theorem autJ2VtxC5_gm (h : autJ2VtxC5 () = true) : conjGenOK gmRT γM = true := by
  have h' := h
  simp only [autJ2VtxC5, Bool.and_eq_true] at h'
  exact h'.2

theorem κR_rm_conj (h0 : autJ2VtxC0 () = true) (h4 : autJ2VtxC4 () = true)
    (h5 : autJ2VtxC5 () = true) (q : Q1M) : rmR * κR q * rmR⁻¹ = κR (ρM q) := by
  have hrm := autJ2VtxC0_perm h0 (t := rmRT) (by simp [autJ2Tbls])
  exact κR_conj h0 h4 (rep_tp hrm)
    (rep_invT (rep_tp hrm) (autJ2VtxC0_inv h0 (t := rmRT) (by simp [autJ2Tbls])))
    (autJ2VtxC5_rm h5) q

theorem κR_bm_conj (h0 : autJ2VtxC0 () = true) (h4 : autJ2VtxC4 () = true)
    (h5 : autJ2VtxC5 () = true) (q : Q1M) : bmR * κR q * bmR⁻¹ = κR (βM q) := by
  have hbm := autJ2VtxC0_perm h0 (t := bmRT) (by simp [autJ2Tbls])
  exact κR_conj h0 h4 (rep_tp hbm)
    (rep_invT (rep_tp hbm) (autJ2VtxC0_inv h0 (t := bmRT) (by simp [autJ2Tbls])))
    (autJ2VtxC5_bm h5) q

theorem κR_tm_conj (h0 : autJ2VtxC0 () = true) (h4 : autJ2VtxC4 () = true)
    (h5 : autJ2VtxC5 () = true) (q : Q1M) : tmR * κR q * tmR⁻¹ = κR (τM q) := by
  have htm := autJ2VtxC0_perm h0 (t := tmRT) (by simp [autJ2Tbls])
  exact κR_conj h0 h4 (rep_tp htm)
    (rep_invT (rep_tp htm) (autJ2VtxC0_inv h0 (t := tmRT) (by simp [autJ2Tbls])))
    (autJ2VtxC5_tm h5) q

theorem κR_gm_conj (h0 : autJ2VtxC0 () = true) (h4 : autJ2VtxC4 () = true)
    (h5 : autJ2VtxC5 () = true) (q : Q1M) : gmR * κR q * gmR⁻¹ = κR (γM q) := by
  have hgm := autJ2VtxC0_perm h0 (t := gmRT) (by simp [autJ2Tbls])
  exact κR_conj h0 h4 (rep_tp hgm)
    (rep_invT (rep_tp hgm) (autJ2VtxC0_inv h0 (t := gmRT) (by simp [autJ2Tbls])))
    (autJ2VtxC5_gm h5) q

theorem autJ2VtxC1_syl (h : autJ2VtxC1 () = true) : enumOK 315 300 256 sylT = true := by
  have h' := h
  simp only [autJ2VtxC1, Bool.and_eq_true] at h'
  exact h'.1.1

theorem autJ2VtxC1_W (h : autJ2VtxC1 () = true) :
    enumOK 315 4000 3840 (sylT ++ [gWT]) = true := by
  have h' := h
  simp only [autJ2VtxC1, Bool.and_eq_true] at h'
  exact h'.1.2

theorem autJ2VtxC1_one (h : autJ2VtxC1 () = true) :
    enumOK 315 3000 2304 (sylT ++ [g1T]) = true := by
  have h' := h
  simp only [autJ2VtxC1, Bool.and_eq_true] at h'
  exact h'.2

theorem autJ2VtxC2_enum (h : autJ2VtxC2 () = true) : enumOK 315 100 32 q2T = true := by
  have h' := h
  simp only [autJ2VtxC2, Bool.and_eq_true] at h'
  exact h'.1

theorem autJ2VtxC2_norm (h : autJ2VtxC2 () = true) :
    normOK 315 100 q2T (sylT ++ [gWT]) = true := by
  have h' := h
  simp only [autJ2VtxC2, Bool.and_eq_true] at h'
  exact h'.2

theorem autJ2VtxC6_A (h : autJ2VtxC6 () = true) :
    enumOK 315 100 36 [rmRT, bmRT, tmRT, gmRT] = true := by
  have h' := h
  simp only [autJ2VtxC6, Bool.and_eq_true] at h'
  exact h'.1

theorem autJ2VtxC6_norm (h : autJ2VtxC6 () = true) :
    normOK 315 100 [e1RT, e2RT, f1RT, f2RT] (sylT ++ [g1T]) = true := by
  have h' := h
  simp only [autJ2VtxC6, Bool.and_eq_true] at h'
  exact h'.2

theorem autJ2VtxC7_spec (h : autJ2VtxC7 () = true) : enumOK 315 100 64 q1Gens = true := h

end CFSG.Quasithin.F112R.St84.AutJ2Model
