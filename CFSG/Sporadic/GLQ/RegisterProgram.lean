module

public import CFSG.LocalAnalysis.SectionRank.Sporadic.Elem3
public import CFSG.LocalAnalysis.SectionRank.Sporadic.LocalWitness
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.ElementaryAbelian
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedGSCRankOneCenter

public noncomputable section

namespace CFSG.Sporadic.GLQ

open CFSG.SectionRank CFSG.SectionRank.Native
open scoped Matrix

inductive Instr where
  | mu (i j k : ℕ)
  | iv (i k : ℕ)
  | pwr (e i k : ℕ)
deriving Inhabited

section Group

variable {G : Type*} [Group G]

@[expose] def initRegs (x y : G) : ℕ → G := fun r => if r = 1 then x else if r = 2 then y else 1

@[expose] def Instr.run (R : ℕ → G) : Instr → ℕ → G
  | .mu i j k => Function.update R k (R i * R j)
  | .iv i k => Function.update R k (R i)⁻¹
  | .pwr e i k => Function.update R k (R i ^ e)

@[expose] def runProg (R : ℕ → G) (prog : List Instr) : ℕ → G := prog.foldl Instr.run R

@[expose] def runStages (x y : G) (stages : List (List Instr)) : ℕ → G :=
  stages.foldl (fun R prog => runProg (initRegs (R 1) (R 2)) prog) (initRegs x y)

@[expose] def letter (x y : G) (l : ℤ) : G :=
  if l = 1 then x else if l = -1 then x⁻¹ else if l = 2 then y else if l = -2 then y⁻¹ else 1

@[expose] def signedWord (x y : G) (w : List ℤ) : G := (w.map (letter x y)).prod

theorem initRegs_mem (H : Subgroup G) {x y : G} (hx : x ∈ H) (hy : y ∈ H) (r : ℕ) :
    initRegs x y r ∈ H := by
  unfold initRegs
  split_ifs
  · exact hx
  · exact hy
  · exact H.one_mem

theorem run_mem (H : Subgroup G) {R : ℕ → G} (hR : ∀ r, R r ∈ H) (ins : Instr) (r : ℕ) :
    Instr.run R ins r ∈ H := by
  cases ins with
  | mu i j k =>
    simp only [Instr.run, Function.update_apply]
    split_ifs
    · exact H.mul_mem (hR i) (hR j)
    · exact hR r
  | iv i k =>
    simp only [Instr.run, Function.update_apply]
    split_ifs
    · exact H.inv_mem (hR i)
    · exact hR r
  | pwr e i k =>
    simp only [Instr.run, Function.update_apply]
    split_ifs
    · exact H.pow_mem (hR i) e
    · exact hR r

theorem runProg_mem (H : Subgroup G) (prog : List Instr) :
    ∀ {R : ℕ → G}, (∀ r, R r ∈ H) → ∀ r, runProg R prog r ∈ H := by
  induction prog with
  | nil => intro R hR r; exact hR r
  | cons ins prog ih =>
    intro R hR r
    exact ih (fun r => run_mem H hR ins r) r

theorem runStages_mem (H : Subgroup G) {x y : G} (hx : x ∈ H) (hy : y ∈ H)
    (stages : List (List Instr)) (r : ℕ) : runStages x y stages r ∈ H := by
  unfold runStages
  suffices h : ∀ (stages : List (List Instr)) {R : ℕ → G}, (∀ r, R r ∈ H) → ∀ r,
      stages.foldl (fun R prog => runProg (initRegs (R 1) (R 2)) prog) R r ∈ H by
    exact h stages (initRegs_mem H hx hy) r
  intro stages
  induction stages with
  | nil => intro R hR r; exact hR r
  | cons prog stages ih =>
    intro R hR r
    exact ih (runProg_mem H prog (initRegs_mem H (hR 1) (hR 2))) r

theorem signedWord_mem (H : Subgroup G) {x y : G} (hx : x ∈ H) (hy : y ∈ H) (w : List ℤ) :
    signedWord x y w ∈ H := by
  unfold signedWord
  refine H.list_prod_mem fun g hg => ?_
  obtain ⟨l, -, rfl⟩ := List.mem_map.mp hg
  unfold letter
  split_ifs
  · exact hx
  · exact H.inv_mem hx
  · exact hy
  · exact H.inv_mem hy
  · exact H.one_mem

end Group

section Native

variable {M V : Type} (O : Ops M V)

@[expose] def Instr.lt (n : ℕ) : Instr → Bool
  | .mu i j k => decide (i < n) && decide (j < n) && decide (k < n)
  | .iv i k => decide (i < n) && decide (k < n)
  | .pwr _ i k => decide (i < n) && decide (k < n)

@[expose] def initRegsN (n : ℕ) (x y : M × M) : Array (M × M) :=
  Array.ofFn (n := n) fun r => if r.val = 1 then x else if r.val = 2 then y else (O.one, O.one)

variable [Inhabited M]

@[expose] def Instr.runN (R : Array (M × M)) : Instr → Array (M × M)
  | .mu i j k => R.setIfInBounds k (O.mul R[i]!.1 R[j]!.1, O.mul R[j]!.2 R[i]!.2)
  | .iv i k => R.setIfInBounds k (R[i]!.2, R[i]!.1)
  | .pwr e i k => R.setIfInBounds k (O.pow R[i]!.1 e, O.pow R[i]!.2 e)

@[expose] def runProgN (R : Array (M × M)) (prog : List Instr) : Array (M × M) :=
  prog.foldl (Instr.runN O) R

@[expose] def runStagesN (n : ℕ) (x y : M × M) (stages : List (List Instr)) : Array (M × M) :=
  stages.foldl (fun R prog => runProgN O (initRegsN O n R[1]! R[2]!) prog) (initRegsN O n x y)

@[expose] def letterN (x y : M × M) (l : ℤ) : M :=
  if l = 1 then x.1 else if l = -1 then x.2 else if l = 2 then y.1 else if l = -2 then y.2
  else O.one

@[expose] def signedWordN (x y : M × M) : List ℤ → M
  | [] => O.one
  | l :: w => O.mul (letterN O x y l) (signedWordN x y w)

@[expose] def sqOK (X : M) : Bool := O.eq (O.mul X X) O.one

@[expose] def kerOK2 (xs : List M) (tests : List ℕ) : Bool :=
  (List.range (2 ^ xs.length - 1)).all fun n =>
    tests.any fun t => O.vne (O.appBase 2 xs (n + 1) (O.unit t)) (O.unit t)

@[expose] def elem2OK (xs : List M) (tests : List ℕ) : Bool :=
  xs.all (sqOK O) && O.commsOK xs && kerOK2 O xs tests

end Native

section Rep

variable {M V : Type} {O : Ops M V} {p d : ℕ} (Sp : OpsSpec O p d) {G : Type*} [Group G]
  (φ : G →* Matrix (Fin d) (Fin d) (ZMod p))

@[expose] def Rep (g : G) (X : M × M) : Prop :=
  Sp.WF X.1 ∧ Sp.WF X.2 ∧ Sp.toMat X.1 = φ g ∧ Sp.toMat X.2 = φ g⁻¹

@[expose] def RegsRep [Inhabited M] (n : ℕ) (R : ℕ → G) (Rn : Array (M × M)) : Prop :=
  Rn.size = n ∧ ∀ r < n, Rep Sp φ (R r) Rn[r]!

variable {Sp φ}

theorem rep_of {g : G} {X Y : M} (hX : Sp.WF X) (hY : Sp.WF Y) (h1 : Sp.toMat X = φ g)
    (h2 : Sp.toMat Y = φ g⁻¹) : Rep Sp φ g (X, Y) :=
  ⟨hX, hY, h1, h2⟩

theorem Rep.one : Rep Sp φ 1 (O.one, O.one) :=
  ⟨Sp.one_wf, Sp.one_wf, by rw [Sp.toMat_one, map_one], by rw [Sp.toMat_one, inv_one, map_one]⟩

theorem Rep.mul {g h : G} {X Y : M × M} (hg : Rep Sp φ g X) (hh : Rep Sp φ h Y) :
    Rep Sp φ (g * h) (O.mul X.1 Y.1, O.mul Y.2 X.2) :=
  ⟨Sp.mul_wf hg.1 hh.1, Sp.mul_wf hh.2.1 hg.2.1,
    by rw [Sp.toMat_mul hg.1 hh.1, hg.2.2.1, hh.2.2.1, map_mul],
    by rw [Sp.toMat_mul hh.2.1 hg.2.1, hg.2.2.2, hh.2.2.2, _root_.mul_inv_rev, map_mul]⟩

theorem Rep.inv {g : G} {X : M × M} (hg : Rep Sp φ g X) : Rep Sp φ g⁻¹ (X.2, X.1) :=
  ⟨hg.2.1, hg.1, hg.2.2.2, by rw [inv_inv]; exact hg.2.2.1⟩

theorem Rep.pow {g : G} {X : M × M} (hg : Rep Sp φ g X) (e : ℕ) :
    Rep Sp φ (g ^ e) (O.pow X.1 e, O.pow X.2 e) :=
  ⟨(Sp.pow_spec hg.1 e).1, (Sp.pow_spec hg.2.1 e).1,
    by rw [(Sp.pow_spec hg.1 e).2, hg.2.2.1, map_pow],
    by rw [(Sp.pow_spec hg.2.1 e).2, hg.2.2.2, ← map_pow, inv_pow]⟩

theorem getElem!_setIfInBounds_of_lt' [Inhabited M] {R : Array M} {k r : ℕ} (hr : r < R.size)
    (x : M) : (R.setIfInBounds k x)[r]! = if k = r then x else R[r]! := by
  rw [getElem!_pos _ r (by simpa using hr), Array.getElem_setIfInBounds,
    getElem!_pos R r hr]

theorem regsRep_initRegs [Inhabited M] {n : ℕ} {x y : G} {X Y : M × M} (hx : Rep Sp φ x X)
    (hy : Rep Sp φ y Y) : RegsRep Sp φ n (initRegs x y) (initRegsN O n X Y) := by
  have hs : (initRegsN O n X Y).size = n := by simp [initRegsN]
  refine ⟨hs, fun r hr => ?_⟩
  unfold initRegsN
  rw [getElem!_pos _ r (by simpa using hr), Array.getElem_ofFn]
  unfold initRegs
  split_ifs
  · exact hx
  · exact hy
  · exact Rep.one

theorem regsRep_run [Inhabited M] {n : ℕ} {R : ℕ → G} {Rn : Array (M × M)}
    (hR : RegsRep Sp φ n R Rn)
    {ins : Instr} (hins : ins.lt n = true) :
    RegsRep Sp φ n (Instr.run R ins) (Instr.runN O Rn ins) := by
  obtain ⟨hs, hR⟩ := hR
  cases ins with
  | mu i j k =>
    simp only [Instr.lt, Bool.and_eq_true, decide_eq_true_eq] at hins
    obtain ⟨⟨hi, hj⟩, -⟩ := hins
    refine ⟨by simp [Instr.runN, hs], fun r hr => ?_⟩
    simp only [Instr.run, Instr.runN]
    rw [getElem!_setIfInBounds_of_lt' (by rw [hs]; exact hr), Function.update_apply]
    by_cases hk : k = r
    · rw [ite_eq_left hk, ite_eq_left hk.symm]
      exact (hR i hi).mul (hR j hj)
    · rw [ite_eq_right hk, ite_eq_right (Ne.symm hk)]
      exact hR r hr
  | iv i k =>
    simp only [Instr.lt, Bool.and_eq_true, decide_eq_true_eq] at hins
    obtain ⟨hi, -⟩ := hins
    refine ⟨by simp [Instr.runN, hs], fun r hr => ?_⟩
    simp only [Instr.run, Instr.runN]
    rw [getElem!_setIfInBounds_of_lt' (by rw [hs]; exact hr), Function.update_apply]
    by_cases hk : k = r
    · rw [ite_eq_left hk, ite_eq_left hk.symm]
      exact (hR i hi).inv
    · rw [ite_eq_right hk, ite_eq_right (Ne.symm hk)]
      exact hR r hr
  | pwr e i k =>
    simp only [Instr.lt, Bool.and_eq_true, decide_eq_true_eq] at hins
    obtain ⟨hi, -⟩ := hins
    refine ⟨by simp [Instr.runN, hs], fun r hr => ?_⟩
    simp only [Instr.run, Instr.runN]
    rw [getElem!_setIfInBounds_of_lt' (by rw [hs]; exact hr), Function.update_apply]
    by_cases hk : k = r
    · rw [ite_eq_left hk, ite_eq_left hk.symm]
      exact (hR i hi).pow e
    · rw [ite_eq_right hk, ite_eq_right (Ne.symm hk)]
      exact hR r hr

theorem regsRep_runProg [Inhabited M] {n : ℕ} (prog : List Instr)
    (hprog : prog.all (Instr.lt n) = true) :
    ∀ {R : ℕ → G} {Rn : Array (M × M)}, RegsRep Sp φ n R Rn →
      RegsRep Sp φ n (runProg R prog) (runProgN O Rn prog) := by
  induction prog with
  | nil => intro R Rn hR; exact hR
  | cons ins prog ih =>
    intro R Rn hR
    rw [List.all_cons, Bool.and_eq_true] at hprog
    exact ih hprog.2 (regsRep_run hR hprog.1)

theorem regsRep_runStages [Inhabited M] {n : ℕ} (hn : 3 ≤ n) {x y : G} {X Y : M × M}
    (hx : Rep Sp φ x X) (hy : Rep Sp φ y Y) (stages : List (List Instr))
    (hst : stages.all (fun prog => prog.all (Instr.lt n)) = true) :
    RegsRep Sp φ n (runStages x y stages) (runStagesN O n X Y stages) := by
  unfold runStages runStagesN
  suffices h : ∀ (stages : List (List Instr)),
      stages.all (fun prog => prog.all (Instr.lt n)) = true →
      ∀ {R : ℕ → G} {Rn : Array (M × M)}, RegsRep Sp φ n R Rn →
        RegsRep Sp φ n (stages.foldl (fun R prog => runProg (initRegs (R 1) (R 2)) prog) R)
          (stages.foldl (fun R prog => runProgN O (initRegsN O n R[1]! R[2]!) prog) Rn) by
    exact h stages hst (regsRep_initRegs hx hy)
  intro stages
  induction stages with
  | nil => intro _ R Rn hR; exact hR
  | cons prog stages ih =>
    intro hst R Rn hR
    rw [List.all_cons, Bool.and_eq_true] at hst
    exact ih hst.2 (regsRep_runProg prog hst.1
      (regsRep_initRegs (hR.2 1 (by omega)) (hR.2 2 (by omega))))

theorem rep_letter {x y : G} {X Y : M × M} (hx : Rep Sp φ x X) (hy : Rep Sp φ y Y) (l : ℤ) :
    Sp.WF (letterN O X Y l) ∧ Sp.toMat (letterN O X Y l) = φ (letter x y l) := by
  unfold letterN letter
  split_ifs
  · exact ⟨hx.1, hx.2.2.1⟩
  · exact ⟨hx.2.1, hx.2.2.2⟩
  · exact ⟨hy.1, hy.2.2.1⟩
  · exact ⟨hy.2.1, hy.2.2.2⟩
  · exact ⟨Sp.one_wf, by rw [Sp.toMat_one, map_one]⟩

theorem rep_signedWord {x y : G} {X Y : M × M} (hx : Rep Sp φ x X) (hy : Rep Sp φ y Y) :
    ∀ w : List ℤ, Sp.WF (signedWordN O X Y w) ∧
      Sp.toMat (signedWordN O X Y w) = φ (signedWord x y w)
  | [] => ⟨Sp.one_wf, by rw [signedWordN, Sp.toMat_one, signedWord, List.map_nil,
      List.prod_nil, map_one]⟩
  | l :: w => by
    obtain ⟨hl, hl'⟩ := rep_letter hx hy l
    obtain ⟨hw, hw'⟩ := rep_signedWord hx hy w
    refine ⟨Sp.mul_wf hl hw, ?_⟩
    rw [signedWordN, Sp.toMat_mul hl hw, hl', hw']
    simp only [signedWord, List.map_cons, List.prod_cons, map_mul]

end Rep

theorem coe_inv_ofPowEqOne {M : Type*} [Monoid M] {a : M} {n : ℕ} (ha : a ^ n = 1)
    (hn : n ≠ 0) : (↑(Units.ofPowEqOne a n ha hn)⁻¹ : M) = a ^ (n - 1) :=
  Units.inv_eq_of_mul_eq_one_right (by
    rw [Units.val_ofPowEqOne, ← pow_succ', Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hn),
      ha])

@[expose] def enc2 : (r : ℕ) → (Fin r → Fin 2) → ℕ
  | 0, _ => 0
  | r + 1, a => (a 0 : ℕ) + 2 * enc2 r (Fin.tail a)

theorem enc2_lt : ∀ (r : ℕ) (a : Fin r → Fin 2), enc2 r a < 2 ^ r
  | 0, _ => by simp [enc2]
  | r + 1, a => by
    have := enc2_lt r (Fin.tail a)
    have := (a 0).isLt
    rw [enc2, pow_succ]
    omega

theorem eq_zero_of_enc2_eq_zero : ∀ (r : ℕ) (a : Fin r → Fin 2), enc2 r a = 0 → a = 0
  | 0, a, _ => funext fun i => i.elim0
  | r + 1, a, h => by
    rw [enc2] at h
    have h0 : (a 0 : ℕ) = 0 := by omega
    have ht := eq_zero_of_enc2_eq_zero r (Fin.tail a) (by omega)
    funext i
    refine Fin.cases (Fin.ext h0) (fun j => ?_) i
    exact congrFun ht j

namespace OpsSpecFacts

variable {M V : Type} {O : Ops M V} {p d : ℕ} (Sp : OpsSpec O p d)

theorem appBase2_spec : ∀ (xs : List M), (∀ X ∈ xs, Sp.WF X) →
    ∀ (a : Fin xs.length → Fin 2) {v : V}, Sp.VWF v →
      Sp.VWF (O.appBase 2 xs (enc2 _ a) v) ∧ Sp.toVec (O.appBase 2 xs (enc2 _ a) v) =
        Sp.toVec v ᵥ* (List.ofFn fun i => Sp.toMat xs[i] ^ (a i : ℕ)).prod
  | [], _, a, v, hv => ⟨hv, by simp [Ops.appBase]⟩
  | X :: xs, hxs, a, v, hv => by
    have hX := hxs X List.mem_cons_self
    have h0 := (a 0).isLt
    have hd : (enc2 (xs.length + 1) a) % 2 = (a 0 : ℕ) := by rw [enc2]; omega
    have hq : (enc2 (xs.length + 1) a) / 2 = enc2 xs.length (Fin.tail a) := by rw [enc2]; omega
    obtain ⟨w1, f1⟩ := Sp.app_spec hX (a 0 : ℕ) hv
    obtain ⟨w2, f2⟩ := appBase2_spec xs (fun Y hY => hxs Y (List.mem_cons_of_mem _ hY))
      (Fin.tail a) w1
    change Sp.VWF (O.appBase 2 xs (enc2 (xs.length + 1) a / 2)
        (O.app X (enc2 (xs.length + 1) a % 2) v)) ∧
      Sp.toVec (O.appBase 2 xs (enc2 (xs.length + 1) a / 2)
        (O.app X (enc2 (xs.length + 1) a % 2) v)) = _
    rw [hd, hq, List.ofFn_succ, List.prod_cons]
    refine ⟨w2, ?_⟩
    rw [f2, f1, Matrix.vecMul_vecMul]
    rfl

theorem ne_one_of_kerOK2 {xs : List M} (hxs : ∀ X ∈ xs, Sp.WF X) {tests : List ℕ}
    (h : kerOK2 O xs tests = true) (a : Fin xs.length → Fin 2) (ha : a ≠ 0) :
    (List.ofFn fun i => Sp.toMat xs[i] ^ (a i : ℕ)).prod ≠ 1 := by
  intro hone
  have hlt := enc2_lt _ a
  have hpos : enc2 _ a ≠ 0 := fun h0 => ha (eq_zero_of_enc2_eq_zero _ a h0)
  unfold kerOK2 at h
  rw [List.all_eq_true] at h
  obtain ⟨k, -, hk⟩ := List.any_eq_true.1 (h (enc2 _ a - 1) (List.mem_range.2 (by omega)))
  rw [show enc2 _ a - 1 + 1 = enc2 _ a by omega] at hk
  apply Sp.toVec_ne hk
  rw [(appBase2_spec Sp xs hxs a (Sp.unit_wf k)).2, hone, Matrix.vecMul_one]

end OpsSpecFacts

section Elem

variable {G : Type*} [Group G]

@[expose] noncomputable def elem2PowHom {C : Type*} [CommGroup C] {r : ℕ} (v : Fin r → C)
    (hv : ∀ i, v i ^ 2 = 1) : Multiplicative (Fin r → ZMod 2) →* C where
  toFun a := ∏ i, v i ^ (Multiplicative.toAdd a i).val
  map_one' := by simp
  map_mul' a b := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [toAdd_mul, Pi.add_apply, ZMod.val_add, ← pow_eq_pow_mod _ (hv i), pow_add]

open scoped IsMulCommutative in
theorem exists_elemAbelian_two {r : ℕ} (u : Fin r → G) (hsq : ∀ i, u i ^ 2 = 1)
    (hcomm : ∀ i j, Commute (u i) (u j))
    (hker : ∀ a : Fin r → Fin 2, a ≠ 0 → (List.ofFn fun i => u i ^ (a i : ℕ)).prod ≠ 1) :
    ∃ η : Multiplicative (Fin r → ZMod 2) →* G,
      (∀ a, η a = (List.ofFn fun i => u i ^ (Multiplicative.toAdd a i).val).prod) ∧
      Function.Injective η ∧ η.range = Subgroup.closure (Set.range u) ∧
      CFSG.IsElementaryAbelian 2 (Subgroup.closure (Set.range u)) ∧
      Nat.card (Subgroup.closure (Set.range u)) = 2 ^ r := by
  set C := Subgroup.closure (Set.range u)
  have hCc : IsMulCommutative C := Subgroup.isMulCommutative_closure (by
    rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩ _
    exact hcomm i j)
  let v : Fin r → C := fun i => ⟨u i, Subgroup.subset_closure ⟨i, rfl⟩⟩
  have hv : ∀ i, v i ^ 2 = 1 := fun i => Subtype.ext (by simpa [v] using hsq i)
  let φ : Multiplicative (Fin r → ZMod 2) →* G := C.subtype.comp (elem2PowHom v hv)
  have hφ : ∀ a, φ a = (List.ofFn fun i => u i ^ (Multiplicative.toAdd a i).val).prod := by
    intro a
    simp only [φ, MonoidHom.comp_apply, elem2PowHom, MonoidHom.coe_mk, OneHom.coe_mk]
    rw [← List.prod_ofFn, map_list_prod, List.map_ofFn]
    rfl
  have hinj : Function.Injective φ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro a ha
    rw [MonoidHom.mem_ker, hφ] at ha
    rw [Subgroup.mem_bot]
    by_contra hne
    refine hker (fun i => ⟨(Multiplicative.toAdd a i).val, ZMod.val_lt _⟩) (fun h0 => hne ?_) ha
    apply Multiplicative.toAdd.injective
    funext j
    have := congrFun h0 j
    simp only [Pi.zero_apply, Fin.ext_iff, Fin.val_zero] at this
    rw [toAdd_one, Pi.zero_apply]
    exact ZMod.val_injective _ (by rw [this, ZMod.val_zero])
  have hrange : φ.range = C := by
    apply le_antisymm
    · rintro _ ⟨a, rfl⟩
      exact (elem2PowHom v hv a).2
    · rw [Subgroup.closure_le]
      rintro _ ⟨i, rfl⟩
      have h1 : elem2PowHom v hv (Multiplicative.ofAdd (Pi.single i 1)) = v i := by
        simp only [elem2PowHom, MonoidHom.coe_mk, OneHom.coe_mk, toAdd_ofAdd]
        rw [Finset.prod_eq_single i]
        · rw [Pi.single_eq_same, show (1 : ZMod 2).val = 1 from rfl, pow_one]
        · intro j _ hj
          rw [Pi.single_eq_of_ne hj, ZMod.val_zero, pow_zero]
        · intro h
          exact absurd (Finset.mem_univ i) h
      exact ⟨_, congrArg Subtype.val h1⟩
  refine ⟨φ, hφ, hinj, hrange, ?_, ?_⟩
  · refine
      { toIsMulCommutative := hCc
        exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.2 fun x => ?_ }
    obtain ⟨a, ha⟩ : (x : G) ∈ φ.range := by rw [hrange]; exact x.2
    have h2 : a ^ 2 = 1 := by
      apply Multiplicative.toAdd.injective
      rw [toAdd_pow, toAdd_one]
      funext j
      rw [Pi.smul_apply, Pi.zero_apply]
      generalize Multiplicative.toAdd a j = z
      revert z
      decide
    apply Subtype.ext
    rw [SubgroupClass.coe_pow, ← ha, ← map_pow, h2, map_one, OneMemClass.coe_one]
  · rw [← hrange, ← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv]
    simp [Nat.card_eq_fintype_card]

theorem ne_one_of_ker {r : ℕ} (u : Fin r → G)
    (hker : ∀ a : Fin r → Fin 2, a ≠ 0 → (List.ofFn fun i => u i ^ (a i : ℕ)).prod ≠ 1)
    (j : Fin r) : u j ≠ 1 := by
  intro h1
  refine hker (Pi.single j 1) (fun h0 => by simpa using congrFun h0 j) ?_
  apply List.prod_eq_one
  intro g hg
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hg
  by_cases hij : i = j
  · subst hij
    rw [Pi.single_eq_same, h1, one_pow]
  · rw [Pi.single_eq_of_ne hij]
    simp

end Elem

namespace OpsSpecFacts

variable {M V : Type} {O : Ops M V} {p d : ℕ} (Sp : OpsSpec O p d)

theorem elem2_of_ok {G : Type*} [Group G] (φ : G →* Matrix (Fin d) (Fin d) (ZMod p))
    (hφ : Function.Injective φ) {r : ℕ} (u : Fin r → G) (X : Fin r → M)
    (hX : ∀ i, Sp.WF (X i) ∧ Sp.toMat (X i) = φ (u i)) {tests : List ℕ}
    (h : elem2OK O (List.ofFn X) tests = true) :
    (∀ i, u i ^ 2 = 1) ∧ (∀ i j, Commute (u i) (u j)) ∧
      ∀ a : Fin r → Fin 2, a ≠ 0 → (List.ofFn fun i => u i ^ (a i : ℕ)).prod ≠ 1 := by
  unfold elem2OK at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨hsq, hcomm⟩, hker⟩ := h
  have hw : ∀ Y ∈ List.ofFn X, Sp.WF Y := by
    intro Y hY
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hY
    exact (hX i).1
  refine ⟨fun i => ?_, fun i j => ?_, fun a ha hprod => ?_⟩
  · apply hφ
    have hXi := hX i
    have h1 := List.all_eq_true.1 hsq (X i) (List.mem_ofFn.mpr ⟨i, rfl⟩)
    have := Sp.toMat_eq (Sp.mul_wf hXi.1 hXi.1) Sp.one_wf h1
    rw [Sp.toMat_mul hXi.1 hXi.1, Sp.toMat_one, hXi.2] at this
    rw [map_pow, sq, this, map_one]
  · have hpair := Sp.pairwise_of_commsOK hw hcomm
    have key : ∀ i j : Fin r, i < j → Commute (u i) (u j) := by
      intro i j hij
      have hlen : (List.ofFn X).length = r := List.length_ofFn
      have := List.pairwise_iff_getElem.1 hpair i j (by rw [hlen]; exact i.isLt)
        (by rw [hlen]; exact j.isLt) hij
      simp only [List.getElem_ofFn] at this
      apply hφ
      rw [map_mul, map_mul, ← (hX i).2, ← (hX j).2]
      exact this
    rcases lt_trichotomy i j with hij | rfl | hij
    · exact key i j hij
    · exact Commute.refl _
    · exact (key j i hij).symm
  · have hlen : (List.ofFn X).length = r := List.length_ofFn
    let a' : Fin (List.ofFn X).length → Fin 2 := fun i => a (Fin.cast hlen i)
    have ha' : a' ≠ 0 := by
      intro h0
      apply ha
      funext i
      have := congrFun h0 (Fin.cast hlen.symm i)
      simpa [a'] using this
    apply ne_one_of_kerOK2 Sp hw hker a' ha'
    have h1 := congrArg φ hprod
    rw [map_list_prod, List.map_ofFn, map_one] at h1
    have h2 : (List.ofFn fun i : Fin r => Sp.toMat (List.ofFn X)[Fin.cast hlen.symm i] ^
        (a' (Fin.cast hlen.symm i) : ℕ)) = List.ofFn fun i => φ (u i ^ (a i : ℕ)) := by
      congr 1
      funext i
      rw [map_pow, ← (hX i).2]
      simp only [a', Fin.getElem_fin, List.getElem_ofFn, Fin.val_cast, Fin.eta, Fin.cast_cast,
        Fin.cast_eq_self]
    rw [List.ofFn_congr hlen, h2]
    exact h1

end OpsSpecFacts

theorem transport_elemAbelian_two {H K : Type*} [Group H] [Group K] [Finite K] (E : Subgroup H)
    (hE : CFSG.IsElementaryAbelian 2 E) {r : ℕ} (hcard : Nat.card E = 2 ^ r) (f : K ≃* H) :
    (∃ A : Subgroup K, CFSG.IsElementaryAbelian 2 A ∧ Nat.card A = 2 ^ r) ∧
      r ≤ CFSG.pRank 2 K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hA : CFSG.IsElementaryAbelian 2 (E.map f.symm.toMonoidHom) :=
    CFSG.IsElementaryAbelian.map _
  have hAc : Nat.card (E.map f.symm.toMonoidHom) = 2 ^ r := by
    rw [Subgroup.card_map_of_injective f.symm.injective, hcard]
  exact ⟨⟨_, hA, hAc⟩,
    CFSG.ComponentClassification.UnbalancedGS.RankOneCenter.le_pRank_of_subgroup hA hAc⟩

end CFSG.Sporadic.GLQ
