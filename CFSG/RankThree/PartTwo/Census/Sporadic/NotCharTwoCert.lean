module

public import CFSG.RankThree.PartTwo.Census.Sporadic.RankFourCert

public section

namespace CFSG.RankThree.PartTwo.Census

open CFSG.Assembly CFSG.Blueprint CFSG.SectionRank CFSG.SectionRank.Native
open scoped Matrix

structure NC2Data where
  base : Data
  inv : ℕ
  conj : ℕ
  conjInv : ℕ
  odd : ℕ
  oddExp : ℕ
  genExp : ℕ
  par : Array ℕ
  lab : Array ℕ
  edges : Array (Array ℕ)
  extra : List (ℕ × ℕ) := []

namespace NC2Data

variable {M V : Type} (O : Ops M V)

@[expose] def regs [Inhabited M] (D : NC2Data) : Array M :=
  O.run D.base.prog (O.initRegs (O.decode D.base.seedA) (O.decode D.base.seedB) D.base.nregs)

@[expose] def gensOf [Inhabited M] (D : NC2Data) (R : Array M) : Array M :=
  (D.base.outs.map fun r => R[r]!).toArray

@[expose] def buildPts [Inhabited M] (gens : Array M) (par lab : Array ℕ) (n : ℕ) : Array M :=
  (List.range n).foldl
    (fun acc i => acc.push (if i = 0 then O.one else O.mul acc[par[i]!]! gens[lab[i]!]!)) #[]

@[expose] def movesOK (tests : List ℕ) (X : M) : Bool :=
  tests.any fun k => O.vne (O.vmul (O.unit k) X) (O.unit k)

@[expose] def conjVec (G P Gi : M) (k : ℕ) : V := O.vmul (O.vmul (O.vmul (O.unit k) G) P) Gi

@[expose] def sig (tests : List ℕ) (X : M) : List V := tests.map fun k => O.vmul (O.unit k) X

@[expose] def vecsNe : List V → List V → Bool
  | u :: us, w :: ws => O.vne u w || vecsNe us ws
  | _, _ => false

@[expose] def progOK (D : NC2Data) : Bool :=
  decide (2 ≤ D.base.nregs) && D.base.prog.all (Op.lt D.base.nregs) &&
    D.base.outs.all (decide <| · < D.base.nregs) && decide (D.inv < D.base.nregs) &&
    decide (D.conj < D.base.nregs) && decide (D.conjInv < D.base.nregs) &&
    decide (D.odd < D.base.nregs)

@[expose] def relOK [Inhabited M] (D : NC2Data) (R : Array M) : Bool :=
  O.eq (O.mul R[D.inv]! R[D.inv]!) O.one && movesOK O D.base.tests R[D.inv]! &&
    D.base.outs.all (fun r => O.commOK R[r]! R[D.inv]!) && O.commOK R[D.conj]! R[D.inv]! &&
    O.commOK R[D.odd]! R[D.inv]! && decide (0 < D.genExp) &&
    D.base.outs.all (fun r => O.eq (O.pow R[r]! D.genExp) O.one) &&
    O.eq (O.mul R[D.conj]! R[D.conjInv]!) O.one && O.eq (O.pow R[D.odd]! D.oddExp) O.one &&
    decide (D.oddExp % 2 = 1) && movesOK O D.base.tests R[D.odd]!

@[expose] def extraOK [Inhabited M] (D : NC2Data) (R : Array M) : Bool :=
  D.extra.all fun rq => decide (rq.1 < D.base.nregs) && decide rq.2.Prime &&
    O.commOK R[rq.1]! R[D.inv]! && O.eq (O.pow R[rq.1]! rq.2) O.one &&
    movesOK O D.base.tests R[rq.1]!

@[expose] def treeOK (D : NC2Data) (ngens : ℕ) : Bool :=
  decide (0 < D.par.size) && decide (D.lab.size = D.par.size) &&
    decide (D.edges.size = D.par.size) &&
    (List.range D.par.size).all (fun i => decide (i = 0) ||
      (decide (D.par[i]! < i) && decide (D.lab[i]! < ngens)))

@[expose] def closedOK [Inhabited M] (gens pts : Array M) (edges : Array (Array ℕ)) (n : ℕ) :
    Bool :=
  (List.range n).all fun i => (List.range gens.size).all fun k =>
    decide ((edges[i]!)[k]! < n) && O.eq (O.mul pts[i]! gens[k]!) pts[(edges[i]!)[k]!]!

@[expose] def distinctOK (sigs : Array (List V)) (n : ℕ) : Bool :=
  (List.range n).all fun j => (List.range j).all fun i => vecsNe O sigs[i]! sigs[j]!

@[expose] def interOK [Inhabited M] (tests : List ℕ) (G Gi X : M) (pts : Array M)
    (sigs : Array (List V)) (n : ℕ) : Bool :=
  (List.range n).all fun i =>
    (let cv := tests.map (conjVec O G pts[i]! Gi)
     (List.range n).all fun j => vecsNe O cv sigs[j]!) ||
    O.commOK X (O.mul (O.mul G pts[i]!) Gi)

@[expose] def check [Inhabited M] (D : NC2Data) : Bool :=
  let R := regs O D
  let gens := gensOf D R
  let pts := buildPts O gens D.par D.lab D.par.size
  let sigs := pts.map (sig O D.base.tests)
  progOK D && relOK O D R && extraOK O D R && treeOK D gens.size &&
    closedOK O gens pts D.edges D.par.size &&
    distinctOK O sigs D.par.size &&
    interOK O D.base.tests R[D.conj]! R[D.conjInv]! R[D.odd]! pts sigs D.par.size

theorem buildPts_succ [Inhabited M] (gens : Array M) (par lab : Array ℕ) (n : ℕ) :
    buildPts O gens par lab (n + 1) = (buildPts O gens par lab n).push
      (if n = 0 then O.one else O.mul (buildPts O gens par lab n)[par[n]!]! gens[lab[n]!]!) := by
  simp only [buildPts, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]

theorem buildPts_size [Inhabited M] (gens : Array M) (par lab : Array ℕ) (n : ℕ) :
    (buildPts O gens par lab n).size = n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [buildPts_succ, Array.size_push, ih]

theorem buildPts_get [Inhabited M] (gens : Array M) (par lab : Array ℕ) {n : ℕ}
    (hpar : ∀ i < n, 0 < i → par[i]! < i) {i : ℕ} (hi : i < n) :
    (buildPts O gens par lab n)[i]! = if i = 0 then O.one else
      O.mul (buildPts O gens par lab n)[par[i]!]! gens[lab[i]!]! := by
  induction n with
  | zero => omega
  | succ n ih =>
    have hpar' : ∀ i < n, 0 < i → par[i]! < i := fun i hi h0 => hpar i (by omega) h0
    have hs := buildPts_size O gens par lab n
    have hget : ∀ j < n,
        (buildPts O gens par lab (n + 1))[j]! = (buildPts O gens par lab n)[j]! := by
      intro j hj
      rw [buildPts_succ, getElem!_pos _ j (by rw [Array.size_push, hs]; omega),
        getElem!_pos _ j (by rw [hs]; exact hj), Array.getElem_push_lt]
    rcases Nat.lt_or_ge i n with hin | hin
    · rw [hget i hin, ih hpar' hin]
      split
      · rfl
      · rw [hget _ (lt_of_lt_of_le (hpar' i hin (by omega)) hin.le)]
    · have hin' : i = n := by omega
      subst hin'
      rw [buildPts_succ, getElem!_pos _ i (by rw [Array.size_push, hs]; omega),
        Array.getElem_push, dite_eq_right (by rw [hs]; omega)]
      split
      · rfl
      · have hp := hpar i (by omega) (by omega)
        rw [getElem!_pos ((buildPts O gens par lab i).push _) (par[i]!)
            (by rw [Array.size_push, hs]; omega),
          Array.getElem_push_lt (by rw [hs]; exact hp),
          getElem!_pos _ (par[i]!) (by rw [hs]; exact hp)]

end NC2Data

theorem card_closure_of_tree {U : Type*} [Group U] [Finite U] {r N : ℕ} (σ : Fin r → U)
    (f : ℕ → U) (hN : 0 < N) (h0 : f 0 = 1)
    (hpar : ∀ i < N, 0 < i → ∃ j < i, ∃ k : Fin r, f i = f j * σ k)
    (hclo : ∀ i < N, ∀ k : Fin r, ∃ j < N, f i * σ k = f j)
    (hinj : ∀ i < N, ∀ j < N, f i = f j → i = j) :
    (∀ y, y ∈ Subgroup.closure (Set.range σ) ↔ ∃ i < N, f i = y) ∧
      Nat.card (Subgroup.closure (Set.range σ)) = N := by
  set S := Subgroup.closure (Set.range σ)
  have hmem : ∀ i < N, f i ∈ S := by
    intro i
    induction i using Nat.strong_induction_on with
    | _ i ih =>
      intro hi
      rcases Nat.eq_zero_or_pos i with rfl | hpos
      · rw [h0]; exact S.one_mem
      · obtain ⟨j, hj, k, e⟩ := hpar i hi hpos
        rw [e]
        exact S.mul_mem (ih j hj (hj.trans hi)) (Subgroup.subset_closure ⟨k, rfl⟩)
  have hpow : ∀ (k : Fin r) (m : ℕ), ∀ i < N, ∃ j < N, f i * σ k ^ m = f j := by
    intro k m
    induction m with
    | zero => intro i hi; exact ⟨i, hi, by rw [pow_zero, mul_one]⟩
    | succ m ih =>
      intro i hi
      obtain ⟨j, hj, e⟩ := ih i hi
      obtain ⟨l, hl, e'⟩ := hclo j hj k
      exact ⟨l, hl, by rw [pow_succ, ← mul_assoc, e, e']⟩
  have hsub : ∀ y ∈ S, ∃ i < N, f i = y := by
    intro y hy
    induction hy using Subgroup.closure_induction_right with
    | one => exact ⟨0, hN, h0⟩
    | mul_right x _ s hs ih =>
      obtain ⟨k, rfl⟩ := hs
      obtain ⟨i, hi, rfl⟩ := ih
      obtain ⟨j, hj, e⟩ := hclo i hi k
      exact ⟨j, hj, e.symm⟩
    | mul_inv_cancel x _ s hs ih =>
      obtain ⟨k, rfl⟩ := hs
      obtain ⟨i, hi, rfl⟩ := ih
      have hinv : (σ k)⁻¹ = σ k ^ (orderOf (σ k) - 1) := by
        rw [eq_comm, ← mul_eq_one_iff_eq_inv, ← pow_succ,
          Nat.sub_add_cancel (orderOf_pos (σ k)), pow_orderOf_eq_one]
      obtain ⟨j, hj, e⟩ := hpow k _ i hi
      exact ⟨j, hj, by rw [hinv, e]⟩
  refine ⟨fun y => ⟨hsub y, fun ⟨i, hi, e⟩ => e ▸ hmem i hi⟩, ?_⟩
  let F : Fin N → S := fun i => ⟨f i, hmem i i.isLt⟩
  have hF : Function.Bijective F := by
    refine ⟨fun a b hab => Fin.ext (hinj a a.isLt b b.isLt (congrArg Subtype.val hab)), ?_⟩
    rintro ⟨y, hy⟩
    obtain ⟨i, hi, rfl⟩ := hsub y hy
    exact ⟨⟨i, hi⟩, rfl⟩
  rw [← Nat.card_eq_of_bijective F hF, Nat.card_fin]

namespace OpsSpec

variable {M V : Type} {O : Ops M V} {p d : ℕ} (Sp : OpsSpec O p d)
include Sp

noncomputable def unitOfPow {S : Submonoid (Matrix (Fin d) (Fin d) (ZMod p))} {X : M}
    (hX : Sp.toMat X ∈ S) {e : ℕ} (he : Sp.toMat X ^ e = 1) (he0 : e ≠ 0) : Sˣ :=
  Units.ofPowEqOne ⟨Sp.toMat X, hX⟩ e (Subtype.ext (by rw [SubmonoidClass.coe_pow]; exact he))
    he0

omit Sp in
theorem units_ext {S : Submonoid (Matrix (Fin d) (Fin d) (ZMod p))} {u v : Sˣ}
    (h : ((u : S) : Matrix (Fin d) (Fin d) (ZMod p)) =
      ((v : S) : Matrix (Fin d) (Fin d) (ZMod p))) : u = v :=
  Units.ext (Subtype.ext h)

theorem toVec_unit_vmul {X : M} (hX : Sp.WF X) (k : ℕ) :
    Sp.toVec (O.vmul (O.unit k) X) = Sp.toVec (O.unit k) ᵥ* Sp.toMat X :=
  Sp.toVec_vmul (Sp.unit_wf k) hX

theorem toMat_ne_of_vecsNe {tests : List ℕ} {X Y : M} (hX : Sp.WF X) (hY : Sp.WF Y)
    (h : NC2Data.vecsNe O (NC2Data.sig O tests X) (NC2Data.sig O tests Y) = true) :
    Sp.toMat X ≠ Sp.toMat Y := by
  intro e
  induction tests with
  | nil => simp [NC2Data.sig, NC2Data.vecsNe] at h
  | cons k ks ih =>
    simp only [NC2Data.sig, List.map_cons, NC2Data.vecsNe, Bool.or_eq_true] at h
    rcases h with h | h
    · apply Sp.toVec_ne h
      rw [toVec_unit_vmul Sp hX, toVec_unit_vmul Sp hY, e]
    · exact ih h

theorem conj_ne_of_vecsNe {tests : List ℕ} {G P Gi Q : M} (hG : Sp.WF G) (hP : Sp.WF P)
    (hGi : Sp.WF Gi) (hQ : Sp.WF Q)
    (h : NC2Data.vecsNe O (tests.map (NC2Data.conjVec O G P Gi)) (NC2Data.sig O tests Q) = true) :
    Sp.toMat G * Sp.toMat P * Sp.toMat Gi ≠ Sp.toMat Q := by
  intro e
  induction tests with
  | nil => simp [NC2Data.sig, NC2Data.vecsNe] at h
  | cons k ks ih =>
    simp only [NC2Data.sig, List.map_cons, NC2Data.vecsNe, Bool.or_eq_true] at h
    rcases h with h | h
    · apply Sp.toVec_ne h
      rw [NC2Data.conjVec, Sp.toVec_vmul (Sp.vmul_wf (Sp.vmul_wf (Sp.unit_wf k) hG) hP) hGi,
        Sp.toVec_vmul (Sp.vmul_wf (Sp.unit_wf k) hG) hP, Sp.toVec_vmul (Sp.unit_wf k) hG,
        toVec_unit_vmul Sp hQ, ← e]
      simp only [Matrix.vecMul_vecMul, Matrix.mul_assoc]
    · exact ih h

theorem toMat_ne_one_of_movesOK {tests : List ℕ} {X : M} (hX : Sp.WF X)
    (h : NC2Data.movesOK O tests X = true) : Sp.toMat X ≠ 1 := by
  intro e
  obtain ⟨k, -, hk⟩ := List.any_eq_true.1 h
  apply Sp.toVec_ne hk
  rw [toVec_unit_vmul Sp hX, e, Matrix.vecMul_one]

theorem toMat_comm_of_commOK {X Y : M} (hX : Sp.WF X) (hY : Sp.WF Y)
    (h : O.commOK X Y = true) : Sp.toMat X * Sp.toMat Y = Sp.toMat Y * Sp.toMat X := by
  have := Sp.toMat_eq (Sp.mul_wf hX hY) (Sp.mul_wf hY hX) h
  rwa [Sp.toMat_mul hX hY, Sp.toMat_mul hY hX] at this

theorem exists_of_nc2Check [Inhabited M] (D : NC2Data) (h : NC2Data.check O D = true)
    [Finite (NativeSporadic.seedMonoid p d 1 D.base.seedA D.base.seedB)ˣ] :
    ∃ (t g x : (NativeSporadic.seedMonoid p d 1 D.base.seedA D.base.seedB)ˣ)
      (S : Subgroup (NativeSporadic.seedMonoid p d 1 D.base.seedA D.base.seedB)ˣ),
      orderOf t = 2 ∧ S ≤ Subgroup.centralizer {t} ∧ Nat.card S = D.par.size ∧
      g ∈ Subgroup.centralizer {t} ∧ x ∈ Subgroup.centralizer {t} ∧ x ≠ 1 ∧
      Odd (orderOf x) ∧ (∀ s ∈ S ⊓ S.map (MulAut.conj g).toMonoidHom, x * s = s * x) ∧
      ∀ rq ∈ D.extra, rq.2 ∣ Nat.card (Subgroup.centralizer ({t} : Set _)) := by
  classical
  set Sm := NativeSporadic.seedMonoid p d 1 D.base.seedA D.base.seedB
  set R := NC2Data.regs O D with hRdef
  set gens := NC2Data.gensOf D R with hgens
  set n := D.par.size with hn
  set pts := NC2Data.buildPts O gens D.par D.lab n with hpts
  unfold NC2Data.check at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨hprog, hrel⟩, hextra⟩, htree⟩, hclosed⟩, hdist⟩, hinter⟩ := h
  simp only [NC2Data.progOK, Bool.and_eq_true, decide_eq_true_eq] at hprog
  obtain ⟨⟨⟨⟨⟨⟨hn2, hp⟩, houts⟩, hinv⟩, hconj⟩, hconjInv⟩, hodd⟩ := hprog
  have hA : Sp.WF (O.decode D.base.seedA) ∧ Sp.toMat (O.decode D.base.seedA) ∈ Sm :=
    ⟨Sp.decode_wf _, by
      rw [Sp.toMat_decode]
      exact Submonoid.subset_closure (Set.mem_insert _ _)⟩
  have hB : Sp.WF (O.decode D.base.seedB) ∧ Sp.toMat (O.decode D.base.seedB) ∈ Sm :=
    ⟨Sp.decode_wf _, by
      rw [Sp.toMat_decode]
      exact Submonoid.subset_closure (Set.mem_insert_of_mem _ rfl)⟩
  obtain ⟨hs0, hok0⟩ := initRegs_regs Sp Sm hA hB D.base.nregs
  obtain ⟨hs, hok⟩ := run_regs Sp Sm D.base.prog hok0 (by rw [hs0]; exact hp)
  have hreg : ∀ r < D.base.nregs, Sp.WF R[r]! ∧ Sp.toMat R[r]! ∈ Sm := fun r hr =>
    hok r (by rw [hs, hs0]; exact hr)
  simp only [NC2Data.relOK, Bool.and_eq_true, decide_eq_true_eq] at hrel
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hT2, hT1⟩, hgT⟩, hGT⟩, hXT⟩, he0⟩, hge⟩, hGG⟩, hXm⟩, hmodd⟩, hX1⟩ := hrel
  set T := R[D.inv]!
  set G := R[D.conj]!
  set Gi := R[D.conjInv]!
  set X := R[D.odd]!
  obtain ⟨hTw, hTS⟩ := hreg _ hinv
  obtain ⟨hGw, hGS⟩ := hreg _ hconj
  obtain ⟨hGiw, hGiS⟩ := hreg _ hconjInv
  obtain ⟨hXw, hXS⟩ := hreg _ hodd
  have hTT : Sp.toMat T ^ 2 = 1 := by
    have := Sp.toMat_eq (Sp.mul_wf hTw hTw) Sp.one_wf hT2
    rwa [Sp.toMat_mul hTw hTw, Sp.toMat_one, ← sq] at this
  have hTne := toMat_ne_one_of_movesOK Sp hTw hT1
  have hXX : Sp.toMat X ^ D.oddExp = 1 := by
    have := Sp.toMat_eq (Sp.pow_spec hXw D.oddExp).1 Sp.one_wf hXm
    rwa [(Sp.pow_spec hXw D.oddExp).2, Sp.toMat_one] at this
  have hXne := toMat_ne_one_of_movesOK Sp hXw hX1
  have hGGi : Sp.toMat G * Sp.toMat Gi = 1 := by
    have := Sp.toMat_eq (Sp.mul_wf hGw hGiw) Sp.one_wf hGG
    rwa [Sp.toMat_mul hGw hGiw, Sp.toMat_one] at this
  have hGiG : Sp.toMat Gi * Sp.toMat G = 1 := mul_eq_one_comm.1 hGGi
  have hm0 : D.oddExp ≠ 0 := by omega
  let τ : Smˣ := unitOfPow Sp hTS hTT (by norm_num)
  let ξ : Smˣ := unitOfPow Sp hXS hXX hm0
  let γ : Smˣ := ⟨⟨Sp.toMat G, hGS⟩, ⟨Sp.toMat Gi, hGiS⟩, Subtype.ext hGGi, Subtype.ext hGiG⟩
  have hτm : ((τ : Sm) : Matrix (Fin d) (Fin d) (ZMod p)) = Sp.toMat T := rfl
  have hξm : ((ξ : Sm) : Matrix (Fin d) (Fin d) (ZMod p)) = Sp.toMat X := rfl
  have hγm : ((γ : Sm) : Matrix (Fin d) (Fin d) (ZMod p)) = Sp.toMat G := rfl
  have hγim : (((γ⁻¹ : Smˣ) : Sm) : Matrix (Fin d) (Fin d) (ZMod p)) = Sp.toMat Gi := rfl
  have hgsize : gens.size = D.base.outs.length := by simp [hgens, NC2Data.gensOf]
  have hgget : ∀ k < gens.size, gens[k]! = R[D.base.outs[k]!]! := by
    intro k hk
    rw [getElem!_pos gens k hk]
    simp only [hgens, NC2Data.gensOf, List.getElem_toArray, List.getElem_map]
    rw [getElem!_pos D.base.outs k (by rw [← hgsize]; exact hk)]
  have hgout : ∀ k < gens.size, D.base.outs[k]! ∈ D.base.outs := fun k hk => by
    rw [getElem!_pos D.base.outs k (by rw [← hgsize]; exact hk)]
    exact List.getElem_mem _
  have hgw : ∀ k < gens.size, Sp.WF gens[k]! ∧ Sp.toMat gens[k]! ∈ Sm := fun k hk => by
    rw [hgget k hk]
    exact hreg _ (of_decide_eq_true (List.all_eq_true.1 houts _ (hgout k hk)))
  have hge' : ∀ k < gens.size, Sp.toMat gens[k]! ^ D.genExp = 1 := fun k hk => by
    have hw := (hgw k hk).1
    have := Sp.toMat_eq (Sp.pow_spec hw D.genExp).1 Sp.one_wf
      (by rw [hgget k hk]; exact List.all_eq_true.1 hge _ (hgout k hk))
    rwa [(Sp.pow_spec hw D.genExp).2, Sp.toMat_one] at this
  have hgT' : ∀ k < gens.size, Sp.toMat gens[k]! * Sp.toMat T = Sp.toMat T * Sp.toMat gens[k]! :=
    fun k hk => toMat_comm_of_commOK Sp (hgw k hk).1 hTw
      (by rw [hgget k hk]; exact List.all_eq_true.1 hgT _ (hgout k hk))
  let σ : Fin gens.size → Smˣ := fun k => unitOfPow Sp (hgw k k.isLt).2 (hge' k k.isLt) (by omega)
  have hσm : ∀ k : Fin gens.size, ((σ k : Sm) : Matrix (Fin d) (Fin d) (ZMod p)) =
      Sp.toMat gens[(k : ℕ)]! := fun k => rfl
  simp only [NC2Data.treeOK, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    List.mem_range, Bool.or_eq_true] at htree
  obtain ⟨⟨⟨hn0, hlab⟩, hedges⟩, hpl⟩ := htree
  have hpar : ∀ i < n, 0 < i → D.par[i]! < i := fun i hi h0 =>
    ((hpl i hi).resolve_left (by omega)).1
  have hlabk : ∀ i < n, 0 < i → D.lab[i]! < gens.size := fun i hi h0 =>
    ((hpl i hi).resolve_left (by omega)).2
  have hptsz : pts.size = n := NC2Data.buildPts_size O gens D.par D.lab n
  have hptget := fun {i : ℕ} (hi : i < n) => NC2Data.buildPts_get O gens D.par D.lab hpar hi
  have hex : ∀ i < n, ∃ y : Smˣ, ((y : Sm) : Matrix (Fin d) (Fin d) (ZMod p)) =
      Sp.toMat pts[i]! ∧ Sp.WF pts[i]! := by
    intro i
    induction i using Nat.strong_induction_on with
    | _ i ih =>
      intro hi
      have e := hptget hi
      rcases Nat.eq_zero_or_pos i with rfl | hpos
      · rw [ite_eq_left (rfl : (0 : ℕ) = 0)] at e
        exact ⟨1, by rw [e, Sp.toMat_one]; rfl, by rw [e]; exact Sp.one_wf⟩
      · rw [ite_eq_right (by omega)] at e
        obtain ⟨y, hy, hyw⟩ := ih _ (hpar i hi hpos) ((hpar i hi hpos).trans hi)
        have hk := hlabk i hi hpos
        refine ⟨y * σ ⟨_, hk⟩, ?_, ?_⟩
        · rw [e, Sp.toMat_mul hyw (hgw _ hk).1, ← hy]
          rfl
        · rw [e]
          exact Sp.mul_wf hyw (hgw _ hk).1
  let f : ℕ → Smˣ := fun i => if hi : i < n then Classical.choose (hex i hi) else 1
  have hf : ∀ i < n, ((f i : Sm) : Matrix (Fin d) (Fin d) (ZMod p)) = Sp.toMat pts[i]! :=
    fun i hi => by
      simp only [f, hi, ↓reduceDIte]
      exact (Classical.choose_spec (hex i hi)).1
  have hfw : ∀ i < n, Sp.WF pts[i]! := fun i hi => (Classical.choose_spec (hex i hi)).2
  have hpt0 : pts[0]! = O.one := by
    have e := hptget hn0
    rwa [ite_eq_left (rfl : (0 : ℕ) = 0)] at e
  simp only [NC2Data.closedOK, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    List.mem_range] at hclosed
  simp only [NC2Data.distinctOK, List.all_eq_true, List.mem_range] at hdist
  have hsig : ∀ i < n, (pts.map (NC2Data.sig O D.base.tests))[i]! =
      NC2Data.sig O D.base.tests pts[i]! := fun i hi => by
    rw [getElem!_pos _ i (by rw [Array.size_map, hptsz]; exact hi), Array.getElem_map,
      getElem!_pos pts i (by rw [hptsz]; exact hi)]
  obtain ⟨hmemS, hcardS⟩ := card_closure_of_tree σ f hn0
    (units_ext (by rw [hf 0 hn0, hpt0, Sp.toMat_one]; rfl))
    (fun i hi h0 => ⟨D.par[i]!, hpar i hi h0, ⟨D.lab[i]!, hlabk i hi h0⟩, units_ext (by
      have e := hptget hi
      rw [ite_eq_right (by omega)] at e
      rw [hf i hi, e, Sp.toMat_mul (hfw _ ((hpar i hi h0).trans hi)) (hgw _ (hlabk i hi h0)).1,
        Units.val_mul, Submonoid.coe_mul, hf _ ((hpar i hi h0).trans hi)]
      rfl)⟩)
    (fun i hi k => ⟨(D.edges[i]!)[(k : ℕ)]!, (hclosed i hi k k.isLt).1, units_ext (by
      have := Sp.toMat_eq (Sp.mul_wf (hfw i hi) (hgw k k.isLt).1)
        (hfw _ (hclosed i hi k k.isLt).1) (hclosed i hi k k.isLt).2
      rw [Units.val_mul, Submonoid.coe_mul, hf i hi, hσm, hf _ (hclosed i hi k k.isLt).1, ← this,
        Sp.toMat_mul (hfw i hi) (hgw k k.isLt).1])⟩)
    (fun i hi j hj hij => by
      by_contra hne
      have hfij : ((f i : Sm) : Matrix (Fin d) (Fin d) (ZMod p)) =
          ((f j : Sm) : Matrix (Fin d) (Fin d) (ZMod p)) := by rw [hij]
      rw [hf i hi, hf j hj] at hfij
      rcases lt_or_gt_of_ne hne with hlt | hlt
      · have h := hdist j hj i hlt
        rw [hsig i hi, hsig j hj] at h
        exact toMat_ne_of_vecsNe Sp (hfw i hi) (hfw j hj) h hfij
      · have h := hdist i hi j hlt
        rw [hsig i hi, hsig j hj] at h
        exact toMat_ne_of_vecsNe Sp (hfw j hj) (hfw i hi) h hfij.symm)
  set S := Subgroup.closure (Set.range σ)
  refine ⟨τ, γ, ξ, S, ?_, ?_, hcardS, ?_, ?_, ?_, ?_, ?_, ?_⟩
  ·
    apply orderOf_eq_prime
    · exact Units.pow_ofPowEqOne _ _
    · intro h1
      exact hTne (by rw [← hτm, h1]; rfl)
  ·
    rw [Subgroup.closure_le]
    rintro _ ⟨k, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
    exact units_ext (by
      rw [Units.val_mul, Units.val_mul, Submonoid.coe_mul, Submonoid.coe_mul, hτm, hσm]
      exact hgT' k k.isLt)
  · rw [Subgroup.mem_centralizer_singleton_iff]
    exact units_ext (by
      rw [Units.val_mul, Units.val_mul, Submonoid.coe_mul, Submonoid.coe_mul, hτm, hγm]
      exact toMat_comm_of_commOK Sp hGw hTw hGT)
  · rw [Subgroup.mem_centralizer_singleton_iff]
    exact units_ext (by
      rw [Units.val_mul, Units.val_mul, Submonoid.coe_mul, Submonoid.coe_mul, hτm, hξm]
      exact toMat_comm_of_commOK Sp hXw hTw hXT)
  · intro h1
    exact hXne (by rw [← hξm, h1]; rfl)
  ·
    have hdvd : orderOf ξ ∣ D.oddExp := orderOf_dvd_of_pow_eq_one (Units.pow_ofPowEqOne _ _)
    exact Odd.of_dvd_nat (Nat.odd_iff.2 hmodd) hdvd
  ·
    rintro s ⟨hsS, ⟨y, hyS, rfl⟩⟩
    obtain ⟨i, hi, rfl⟩ := (hmemS y).1 hyS
    simp only [NC2Data.interOK, List.all_eq_true, List.mem_range, Bool.or_eq_true] at hinter
    have hconjm : (((MulAut.conj γ (f i) : Smˣ) : Sm) : Matrix (Fin d) (Fin d) (ZMod p)) =
        Sp.toMat G * Sp.toMat pts[i]! * Sp.toMat Gi := by
      rw [MulAut.conj_apply, Units.val_mul, Units.val_mul, Submonoid.coe_mul, Submonoid.coe_mul,
        hγm, hγim, hf i hi]
    rcases hinter i hi with hsep | hcomm
    · exfalso
      obtain ⟨j, hj, hjeq⟩ := (hmemS _).1 hsS
      have h := hsep j hj
      rw [hsig j hj] at h
      apply conj_ne_of_vecsNe Sp hGw (hfw i hi) hGiw (hfw j hj) h
      have hm : ((f j : Sm) : Matrix (Fin d) (Fin d) (ZMod p)) =
          (((MulAut.conj γ).toMonoidHom (f i) : Smˣ) : Sm) := by rw [hjeq]
      rw [hf j hj, MulEquiv.coe_toMonoidHom, hconjm] at hm
      exact hm.symm
    · have hcm := toMat_comm_of_commOK Sp hXw
        (Sp.mul_wf (Sp.mul_wf hGw (hfw i hi)) hGiw) hcomm
      rw [Sp.toMat_mul (Sp.mul_wf hGw (hfw i hi)) hGiw, Sp.toMat_mul hGw (hfw i hi)] at hcm
      apply units_ext
      rw [Units.val_mul, Units.val_mul, Submonoid.coe_mul, Submonoid.coe_mul, hξm,
        MulEquiv.coe_toMonoidHom, hconjm]
      exact hcm
  ·
    intro rq hrq
    simp only [NC2Data.extraOK, List.all_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hextra
    obtain ⟨⟨⟨⟨hr, hq⟩, hcT⟩, hpow⟩, hmv⟩ := hextra rq hrq
    obtain ⟨hYw, hYS⟩ := hreg _ hr
    have hYY : Sp.toMat R[rq.1]! ^ rq.2 = 1 := by
      have := Sp.toMat_eq (Sp.pow_spec hYw rq.2).1 Sp.one_wf hpow
      rwa [(Sp.pow_spec hYw rq.2).2, Sp.toMat_one] at this
    have hYne := toMat_ne_one_of_movesOK Sp hYw hmv
    let υ : Smˣ := unitOfPow Sp hYS hYY hq.ne_zero
    have hυC : υ ∈ Subgroup.centralizer ({τ} : Set Smˣ) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact units_ext (by
        rw [Units.val_mul, Units.val_mul, Submonoid.coe_mul, Submonoid.coe_mul, hτm]
        exact toMat_comm_of_commOK Sp hYw hTw hcT)
    have hυo : orderOf υ = rq.2 := by
      have : Fact rq.2.Prime := ⟨hq⟩
      apply orderOf_eq_prime (Units.pow_ofPowEqOne _ _)
      intro h1
      apply hYne
      exact congrArg (fun u : Smˣ => ((u : Sm) : Matrix (Fin d) (Fin d) (ZMod p))) h1
    have := Subgroup.orderOf_dvd_natCard (Subgroup.centralizer ({τ} : Set Smˣ)) hυC
    rwa [hυo] at this

theorem not_isCharTwoType_of_nc2Check [Inhabited M] (D : NC2Data) (h : NC2Data.check O D = true)
    [Finite (NativeSporadic.seedMonoid p d 1 D.base.seedA D.base.seedB)ˣ]
    (hN : D.par.size =
      2 ^ (Nat.card (NativeSporadic.seedMonoid p d 1 D.base.seedA D.base.seedB)ˣ).factorization 2) :
    ¬ IsCharTwoType (NativeSporadic.seedMonoid p d 1 D.base.seedA D.base.seedB)ˣ := by
  obtain ⟨t, g, x, S, ht, hSC, hcard, hg, hx, hx1, hxo, hxc, -⟩ := exists_of_nc2Check Sp D h
  set L := Subgroup.normalizer
    ((Subgroup.zpowers t : Subgroup (NativeSporadic.seedMonoid p d 1 D.base.seedA D.base.seedB)ˣ) :
      Set (NativeSporadic.seedMonoid p d 1 D.base.seedA D.base.seedB)ˣ)
  have ht1 : t ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at ht
    omega
  have hL : IsTwoLocal L := ⟨Subgroup.zpowers t, by rwa [Ne, Subgroup.zpowers_eq_bot],
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, ht, pow_one]), rfl⟩
  have hCL : Subgroup.centralizer ({t} : Set _) ≤ L := by
    intro y hy
    refine Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr ?_)
    rintro _ ⟨m, rfl⟩
    exact (Commute.zpow_left (Subgroup.mem_centralizer_singleton_iff.1 hy).symm m).eq
  set S₂ := S.map (MulAut.conj g).toMonoidHom
  have hS₂C : S₂ ≤ Subgroup.centralizer ({t} : Set _) := by
    rintro _ ⟨y, hy, rfl⟩
    rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hg (hSC hy)) (Subgroup.inv_mem _ hg)
  have hc₁ : Nat.card S = 2 ^ (Nat.card L).factorization 2 :=
    card_eq_two_pow_factorization_of_le (hSC.trans hCL) (hcard.trans hN)
  have hc₂ : Nat.card S₂ = 2 ^ (Nat.card L).factorization 2 := by
    rw [Subgroup.card_map_of_injective (MulAut.conj g).injective, hc₁]
  exact not_isCharTwoType_of_sylow_inf hL (hSC.trans hCL) (hS₂C.trans hCL) hc₁ hc₂ (hCL hx) hx1
    hxo hxc

omit Sp in
theorem normalizer_zpowers_eq_centralizer {U : Type*} [Group U] {t : U} (ht : orderOf t = 2) :
    Subgroup.normalizer ((Subgroup.zpowers t : Subgroup U) : Set U) =
      Subgroup.centralizer ({t} : Set U) := by
  apply le_antisymm
  · intro g hg
    have hmem := (Subgroup.mem_normalizer_iff.mp hg t).mp (Subgroup.mem_zpowers t)
    obtain ⟨k, e⟩ := Subgroup.mem_zpowers_iff.mp hmem
    rw [← zpow_mod_orderOf, ht] at e
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hk : k % ((2 : ℕ) : ℤ) = 0 ∨ k % ((2 : ℕ) : ℤ) = 1 := by omega
    rcases hk with hk | hk
    · exfalso
      rw [hk, zpow_zero, eq_comm, conj_eq_one_iff] at e
      rw [e, orderOf_one] at ht
      omega
    · rw [hk, zpow_one] at e
      calc g * t = g * t * g⁻¹ * g := by group
        _ = t * g := by rw [← e]
  · intro g hg
    refine Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr ?_)
    rintro _ ⟨m, rfl⟩
    exact (Commute.zpow_left (Subgroup.mem_centralizer_singleton_iff.1 hg).symm m).eq

theorem not_isCharTwoType_of_nc2Check' [Inhabited M] (D : NC2Data) (h : NC2Data.check O D = true)
    [Finite (NativeSporadic.seedMonoid p d 1 D.base.seedA D.base.seedB)ˣ]
    (hC : ∀ u : (NativeSporadic.seedMonoid p d 1 D.base.seedA D.base.seedB)ˣ, orderOf u = 2 →
      (∀ rq ∈ D.extra, rq.2 ∣ Nat.card (Subgroup.centralizer ({u} : Set _))) →
      D.par.size = 2 ^ (Nat.card (Subgroup.centralizer ({u} : Set _))).factorization 2) :
    ¬ IsCharTwoType (NativeSporadic.seedMonoid p d 1 D.base.seedA D.base.seedB)ˣ := by
  obtain ⟨t, g, x, S, ht, hSC, hcard, hg, hx, hx1, hxo, hxc, hext⟩ := exists_of_nc2Check Sp D h
  set L := Subgroup.normalizer
    ((Subgroup.zpowers t : Subgroup (NativeSporadic.seedMonoid p d 1 D.base.seedA D.base.seedB)ˣ) :
      Set (NativeSporadic.seedMonoid p d 1 D.base.seedA D.base.seedB)ˣ)
  have hLC : L = Subgroup.centralizer ({t} : Set _) := normalizer_zpowers_eq_centralizer ht
  have ht1 : t ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at ht
    omega
  have hL : IsTwoLocal L := ⟨Subgroup.zpowers t, by rwa [Ne, Subgroup.zpowers_eq_bot],
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, ht, pow_one]), rfl⟩
  set S₂ := S.map (MulAut.conj g).toMonoidHom
  have hS₂C : S₂ ≤ Subgroup.centralizer ({t} : Set _) := by
    rintro _ ⟨y, hy, rfl⟩
    rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hg (hSC hy)) (Subgroup.inv_mem _ hg)
  have hc₁ : Nat.card S = 2 ^ (Nat.card L).factorization 2 := by
    rw [hcard, hLC]
    exact hC t ht hext
  have hc₂ : Nat.card S₂ = 2 ^ (Nat.card L).factorization 2 := by
    rw [Subgroup.card_map_of_injective (MulAut.conj g).injective, hc₁]
  exact not_isCharTwoType_of_sylow_inf hL (hSC.trans hLC.ge) (hS₂C.trans hLC.ge) hc₁ hc₂
    (hLC.ge hx) hx1 hxo hxc

end OpsSpec

theorem factorization_two_of_eq {n a m : ℕ} (h : n = 2 ^ a * m) (hm : m % 2 = 1) :
    n.factorization 2 = a := by
  have hm0 : m ≠ 0 := by omega
  rw [h, Nat.factorization_mul (by positivity) hm0, Finsupp.add_apply,
    Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd (by omega), add_zero]

theorem excluded433_sporadic_of_not_isCharTwoType {s : TauCeti.SporadicName} {T : Type}
    [Group T] (e : IsSimpleGroup s.Group → Nonempty (s.Group ≃* T)) (hT : ¬ IsCharTwoType T) :
    Excluded433 (.sporadic s) :=
  excluded433_sporadic_of_equiv e fun _ _ _ hG eT => hG.false_of_not_isCharTwoType eT hT

end CFSG.RankThree.PartTwo.Census
