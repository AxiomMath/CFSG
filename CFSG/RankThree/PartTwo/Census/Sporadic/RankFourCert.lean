module

public import CFSG.LocalAnalysis.SectionRank.Sporadic.Elem3
public import CFSG.LocalAnalysis.SectionRank.PRank
public import CFSG.RankThree.PartTwo.Census.Sporadic.Common

public section

namespace CFSG.RankThree.PartTwo.Census

open CFSG.Blueprint CFSG.SectionRank CFSG.SectionRank.Native
open scoped Matrix

structure W4Data where
  base : Data
  inv : ℕ

namespace W4Data

variable {M V : Type} (O : Ops M V)

@[expose] def check [Inhabited M] (D : W4Data) : Bool :=
  let R := O.run D.base.prog
    (O.initRegs (O.decode D.base.seedA) (O.decode D.base.seedB) D.base.nregs)
  decide (2 ≤ D.base.nregs) && D.base.prog.all (Op.lt D.base.nregs) &&
    D.base.outs.all (decide <| · < D.base.nregs) && decide (D.inv < D.base.nregs) &&
    O.elemOK (D.base.outs.map fun r => R[r]!) D.base.tests &&
    O.eq (O.mul R[D.inv]! R[D.inv]!) O.one &&
    D.base.tests.any (fun k => O.vne (O.vmul (O.unit k) R[D.inv]!) (O.unit k)) &&
    D.base.outs.all (fun r => O.commOK R[r]! R[D.inv]!)

end W4Data

namespace OpsSpec

variable {M V : Type} {O : Ops M V} {p d : ℕ} (Sp : OpsSpec O p d)
include Sp

section Regs

variable [Inhabited M] (S : Submonoid (Matrix (Fin d) (Fin d) (ZMod p)))

theorem step_regs {R : Array M} (hR : ∀ r < R.size, Sp.WF R[r]! ∧ Sp.toMat R[r]! ∈ S) {op : Op}
    (hop : op.lt R.size = true) :
    (O.step R op).size = R.size ∧
      ∀ r < (O.step R op).size, Sp.WF (O.step R op)[r]! ∧ Sp.toMat (O.step R op)[r]! ∈ S := by
  cases op with
  | mul i j k =>
    simp only [Op.lt, Bool.and_eq_true, decide_eq_true_eq] at hop
    obtain ⟨⟨hi, hj⟩, hk⟩ := hop
    have hs : (O.step R (.mul i j k)).size = R.size := by
      simp [Ops.step, Array.set!]
    refine ⟨hs, fun r hr => ?_⟩
    rw [hs] at hr
    simp only [Ops.step, Array.set!]
    rw [CFSG.SectionRank.OpsSpec.getElem!_setIfInBounds_of_lt hr]
    split
    · obtain ⟨wi, mi⟩ := hR i hi
      obtain ⟨wj, mj⟩ := hR j hj
      exact ⟨Sp.mul_wf wi wj, by rw [Sp.toMat_mul wi wj]; exact S.mul_mem mi mj⟩
    · exact hR r hr
  | pow e i k =>
    simp only [Op.lt, Bool.and_eq_true, decide_eq_true_eq] at hop
    obtain ⟨hi, hk⟩ := hop
    have hs : (O.step R (.pow e i k)).size = R.size := by
      simp [Ops.step, Array.set!]
    refine ⟨hs, fun r hr => ?_⟩
    rw [hs] at hr
    simp only [Ops.step, Array.set!]
    rw [CFSG.SectionRank.OpsSpec.getElem!_setIfInBounds_of_lt hr]
    split
    · obtain ⟨wi, mi⟩ := hR i hi
      obtain ⟨w, m⟩ := Sp.pow_spec wi e
      exact ⟨w, by rw [m]; exact S.pow_mem mi e⟩
    · exact hR r hr

theorem run_regs (prog : List Op) {R : Array M}
    (hR : ∀ r < R.size, Sp.WF R[r]! ∧ Sp.toMat R[r]! ∈ S)
    (hprog : prog.all (Op.lt R.size) = true) :
    (O.run prog R).size = R.size ∧
      ∀ r < (O.run prog R).size, Sp.WF (O.run prog R)[r]! ∧ Sp.toMat (O.run prog R)[r]! ∈ S := by
  induction prog generalizing R with
  | nil => exact ⟨rfl, hR⟩
  | cons op prog ih =>
    rw [List.all_cons, Bool.and_eq_true] at hprog
    obtain ⟨hs, hok⟩ := step_regs Sp S hR hprog.1
    have := ih hok (by rw [hs]; exact hprog.2)
    simp only [Ops.run, List.foldl_cons] at this ⊢
    exact ⟨this.1.trans hs, this.2⟩

theorem initRegs_regs {A B : M} (hA : Sp.WF A ∧ Sp.toMat A ∈ S) (hB : Sp.WF B ∧ Sp.toMat B ∈ S)
    (n : ℕ) : (O.initRegs A B n).size = n ∧
      ∀ r < (O.initRegs A B n).size, Sp.WF (O.initRegs A B n)[r]! ∧
        Sp.toMat (O.initRegs A B n)[r]! ∈ S := by
  have hs : (O.initRegs A B n).size = n := by simp [Ops.initRegs]
  refine ⟨hs, fun r hr => ?_⟩
  rw [hs] at hr
  unfold Ops.initRegs
  rw [getElem!_pos _ r (by simpa using hr), Array.getElem_ofFn]
  split
  · exact hA
  split
  · exact hB
  · exact ⟨Sp.one_wf, by rw [Sp.toMat_one]; exact S.one_mem⟩

end Regs

theorem exists_of_w4Check [Inhabited M] (D : W4Data) (h : W4Data.check O D = true) :
    ∃ (t : (NativeSporadic.seedMonoid p d 1 D.base.seedA D.base.seedB)ˣ)
      (E : Subgroup (NativeSporadic.seedMonoid p d 1 D.base.seedA D.base.seedB)ˣ),
      orderOf t = 2 ∧ CFSG.Open.IsElemAbelian 3 E ∧ Nat.card E = 3 ^ D.base.outs.length ∧
        ∀ x ∈ E, x * t = t * x := by
  set S := NativeSporadic.seedMonoid p d 1 D.base.seedA D.base.seedB
  unfold W4Data.check at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨hn, hprog⟩, houts⟩, hinv⟩, hel⟩, hT2⟩, hT1⟩, hcomm⟩ := h
  have hA : Sp.WF (O.decode D.base.seedA) ∧ Sp.toMat (O.decode D.base.seedA) ∈ S :=
    ⟨Sp.decode_wf _, by
      rw [Sp.toMat_decode]
      exact Submonoid.subset_closure (Set.mem_insert _ _)⟩
  have hB : Sp.WF (O.decode D.base.seedB) ∧ Sp.toMat (O.decode D.base.seedB) ∈ S :=
    ⟨Sp.decode_wf _, by
      rw [Sp.toMat_decode]
      exact Submonoid.subset_closure (Set.mem_insert_of_mem _ rfl)⟩
  obtain ⟨hs0, hok0⟩ := initRegs_regs Sp S hA hB D.base.nregs
  obtain ⟨hs, hok⟩ := run_regs Sp S D.base.prog hok0 (by rw [hs0]; exact hprog)
  set R := O.run D.base.prog
    (O.initRegs (O.decode D.base.seedA) (O.decode D.base.seedB) D.base.nregs)
  rw [hs0] at hs
  obtain ⟨hTw, hTS⟩ := hok D.inv (by rw [hs]; exact hinv)
  set T := R[D.inv]!
  have hTT : Sp.toMat T * Sp.toMat T = 1 := by
    have := Sp.toMat_eq (Sp.mul_wf hTw hTw) Sp.one_wf hT2
    rwa [Sp.toMat_mul hTw hTw, Sp.toMat_one] at this
  have hTne : Sp.toMat T ≠ 1 := by
    intro h1
    obtain ⟨k, -, hk⟩ := List.any_eq_true.1 hT1
    apply Sp.toVec_ne hk
    rw [Sp.toVec_vmul (Sp.unit_wf k) hTw, h1, Matrix.vecMul_one]
  have hT2' : (⟨Sp.toMat T, hTS⟩ : S) ^ 2 = 1 := Subtype.ext (by
    rw [SubmonoidClass.coe_pow, sq]
    exact hTT)
  let τ : Sˣ := Units.ofPowEqOne _ 2 hT2' (by norm_num)
  have hτ : ((τ : S) : Matrix (Fin d) (Fin d) (ZMod p)) = Sp.toMat T := rfl
  have hτo : orderOf τ = 2 := by
    apply orderOf_eq_prime
    · exact Units.pow_ofPowEqOne _ _
    · intro h1
      apply hTne
      rw [← hτ, h1]
      rfl
  set xs := D.base.outs.map fun r => R[r]!
  have hxs : ∀ X ∈ xs, Sp.WF X ∧ Sp.toMat X ∈ S := by
    intro X hX
    obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hX
    exact hok r (by rw [hs]; exact of_decide_eq_true (List.all_eq_true.1 houts r hr))
  have hw : ∀ X ∈ xs, Sp.WF X := fun X hX => (hxs X hX).1
  unfold Ops.elemOK at hel
  simp only [Bool.and_eq_true] at hel
  obtain ⟨⟨hcube, hcomms⟩, hker⟩ := hel
  have hpair := Sp.pairwise_of_commsOK hw hcomms
  have hcubeM : ∀ i : Fin xs.length, Sp.toMat xs[i] ^ 3 = 1 := fun i => by
    have hX := hw _ (List.getElem_mem i.isLt)
    have := Sp.toMat_eq (Sp.mul_wf (Sp.mul_wf hX hX) hX) Sp.one_wf
      (List.all_eq_true.1 hcube _ (List.getElem_mem i.isLt))
    rwa [Sp.toMat_mul (Sp.mul_wf hX hX) hX, Sp.toMat_mul hX hX, Sp.toMat_one, ← pow_two,
      ← pow_succ] at this
  have hcommT : ∀ i : Fin xs.length, Sp.toMat xs[i] * Sp.toMat T = Sp.toMat T * Sp.toMat xs[i] :=
    fun i => by
      have hmem : xs[i] ∈ xs := List.getElem_mem i.isLt
      obtain ⟨r, hr, hrx⟩ := List.mem_map.1 hmem
      have hX := hw _ hmem
      have := Sp.toMat_eq (Sp.mul_wf hX hTw) (Sp.mul_wf hTw hX)
        (by rw [← hrx]; exact List.all_eq_true.1 hcomm r hr)
      rwa [Sp.toMat_mul hX hTw, Sp.toMat_mul hTw hX] at this
  set C := Subgroup.centralizer ({τ} : Set Sˣ)
  have h3 : ∀ i : Fin xs.length, (⟨Sp.toMat xs[i], (hxs _ (List.getElem_mem i.isLt)).2⟩ : S) ^ 3
      = 1 := fun i => Subtype.ext (by rw [SubmonoidClass.coe_pow]; exact hcubeM i)
  let w : Fin xs.length → Sˣ := fun i => Units.ofPowEqOne _ 3 (h3 i) (by norm_num)
  have hwC : ∀ i, w i ∈ C := fun i => by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact Units.ext (Subtype.ext (hcommT i))
  let u : Fin xs.length → C := fun i => ⟨w i, hwC i⟩
  let f : C →* Matrix (Fin d) (Fin d) (ZMod p) :=
    S.subtype.comp ((Units.coeHom S).comp C.subtype)
  have hf : ∀ i (n : ℕ), f (u i ^ n) = Sp.toMat xs[i] ^ n := fun i n => by
    rw [map_pow]
    rfl
  obtain ⟨E', hE', hE'c⟩ := exists_elemAbelian_of_commuting u
    (fun i => Subtype.ext (Units.pow_ofPowEqOne (h3 i) (by norm_num)))
    (fun i j => by
      apply Subtype.ext
      apply Units.ext
      apply Subtype.ext
      change Sp.toMat xs[i] * Sp.toMat xs[j] = Sp.toMat xs[j] * Sp.toMat xs[i]
      rcases lt_trichotomy i j with hij | rfl | hij
      · exact List.pairwise_iff_getElem.1 hpair i j i.isLt j.isLt hij
      · rfl
      · exact (List.pairwise_iff_getElem.1 hpair j i j.isLt i.isLt hij).symm)
    (fun a ha hprod => by
      refine Sp.ne_one_of_kerOK hw hker a ha ?_
      have := congrArg f hprod
      rwa [map_list_prod, List.map_ofFn, map_one, Function.comp_def,
        funext fun i => hf i _] at this)
  refine ⟨τ, E'.map C.subtype, hτo, CFSG.SectionRank.isElemAbelian_map hE' _, ?_, ?_⟩
  · rw [Subgroup.card_map_of_injective C.subtype_injective, hE'c, List.length_map]
  · rintro _ ⟨y, -, rfl⟩
    exact Subgroup.mem_centralizer_singleton_iff.1 y.2

theorem four_le_localRank_three_of_w4Check [Inhabited M] (D : W4Data)
    (h : W4Data.check O D = true) (h4 : D.base.outs.length = 4)
    [Finite (NativeSporadic.seedMonoid p d 1 D.base.seedA D.base.seedB)ˣ] :
    4 ≤ CFSG.Assembly.RankThreeEven.localRank 3
      (NativeSporadic.seedMonoid p d 1 D.base.seedA D.base.seedB)ˣ := by
  obtain ⟨t, E, ht, hE, hc, hEt⟩ := exists_of_w4Check Sp D h
  rw [h4] at hc
  exact le_localRank_of_commute_involution Nat.prime_three ht hE hc hEt

end OpsSpec

theorem excluded433_sporadic_of_four_le_localRank_three {s : TauCeti.SporadicName} {T : Type}
    [Group T] (e : IsSimpleGroup s.Group → Nonempty (s.Group ≃* T))
    (hT : ∀ [Finite T], 4 ≤ CFSG.Assembly.RankThreeEven.localRank 3 T) :
    Excluded433 (.sporadic s) :=
  excluded433_sporadic_of_equiv e fun G _ _ hG eT =>
    have : Finite T := Finite.of_equiv G eT.toEquiv
    hG.false_of_four_le_localRank eT Nat.prime_three (by norm_num) hT

end CFSG.RankThree.PartTwo.Census
