module

public import CFSG.GH74.Filter.Sporadic.He
import all CFSG.Blueprint.NativeSporadic
public import CFSG.LocalAnalysis.SectionRank.Sporadic.Elem3
import all CFSG.LocalAnalysis.SectionRank.Sporadic.Elem3

public section

namespace CFSG.RankThree.PartTwo.Sec21.Item21Early2Proof

open CFSG CFSG.Blueprint CFSG.SectionRank CFSG.SectionRank.Native


theorem elemAbelian_of_commuting_involutions {G : Type*} [Group G] {r : ℕ}
    (u : Fin r → G) (hsq : ∀ i, u i * u i = 1) (hcomm : ∀ i j, u i * u j = u j * u i)
    (hker : ∀ a : Fin r → Fin 2, a ≠ 0 → (List.ofFn fun i => u i ^ (a i : ℕ)).prod ≠ 1) :
    ∃ E : Subgroup G, Open.IsElemAbelian 2 E ∧ Nat.card E = 2 ^ r := by
  obtain ⟨f, hf⟩ := GH74.Filter.exists_injective_of_commuting_involutions u
    (fun i => by rw [sq]; exact hsq i) (fun i j => hcomm i j) hker
  refine exists_isElemAbelian_of_injective (p := 2) (A := Fin r → Multiplicative (ZMod 2))
    (fun a b => mul_comm a b) (fun a => ?_) (GH74.Filter.card_pi_zmod_two r) f hf
  funext i
  rw [Pi.pow_apply, Pi.one_apply]
  apply Multiplicative.toAdd.injective
  rw [toAdd_pow, toAdd_one]
  generalize Multiplicative.toAdd (a i) = z
  revert z
  decide

theorem elemAbelian_units_two {R' : Type*} [Monoid R'] (S : Submonoid R') {r : ℕ}
    (x : Fin r → R') (hxS : ∀ i, x i ∈ S) (hsq : ∀ i, x i * x i = 1)
    (hcomm : ∀ i j, x i * x j = x j * x i)
    (hker : ∀ a : Fin r → Fin 2, a ≠ 0 → (List.ofFn fun i => x i ^ (a i : ℕ)).prod ≠ 1) :
    ∃ E : Subgroup Sˣ, Open.IsElemAbelian 2 E ∧ Nat.card E = 2 ^ r := by
  have h2 : ∀ i, (⟨x i, hxS i⟩ : S) ^ 2 = 1 := fun i => Subtype.ext (by simpa [sq] using hsq i)
  let u : Fin r → Sˣ := fun i => Units.ofPowEqOne _ 2 (h2 i) (by norm_num)
  let f : Sˣ →* R' := S.subtype.comp (Units.coeHom S)
  have hf : ∀ i (n : ℕ), f (u i ^ n) = x i ^ n := fun i n => by
    rw [map_pow]
    rfl
  refine elemAbelian_of_commuting_involutions u (fun i => ?_)
    (fun i j => Units.ext (Subtype.ext (hcomm i j))) (fun a ha h => hker a ha ?_)
  · have := Units.pow_ofPowEqOne (h2 i) (by norm_num : 2 ≠ 0)
    rwa [sq] at this
  · have := congrArg f h
    rwa [map_list_prod, List.map_ofFn, map_one, Function.comp_def, funext fun i => hf i _] at this

@[expose] def secOpDst : Op → ℕ
  | .mul _ _ k => k
  | .pow _ _ k => k

section Regs

variable {M V : Type} {O : Ops M V} {p d : ℕ} [Inhabited M]

theorem secStep_getElem!_of_ne (O : Ops M V) (R : Array M) (op : Op) {k : ℕ} (hk : k < R.size)
    (hne : secOpDst op ≠ k) : (O.step R op)[k]! = R[k]! := by
  cases op with
  | mul i j l =>
    have hne' : l ≠ k := hne
    simp only [Ops.step, Array.set!]
    rw [OpsSpec.getElem!_setIfInBounds_of_lt hk]
    simp [hne']
  | pow e i l =>
    have hne' : l ≠ k := hne
    simp only [Ops.step, Array.set!]
    rw [OpsSpec.getElem!_setIfInBounds_of_lt hk]
    simp [hne']

theorem secStep_size (O : Ops M V) (R : Array M) (op : Op) : (O.step R op).size = R.size := by
  cases op <;> simp [Ops.step, Array.set!]

theorem secRun_getElem!_of_ne (O : Ops M V) (prog : List Op) : ∀ (R : Array M) {k : ℕ},
    k < R.size → (∀ op ∈ prog, secOpDst op ≠ k) → (O.run prog R)[k]! = R[k]! := by
  induction prog with
  | nil => intro R k _ _; rfl
  | cons op prog ih =>
    intro R k hk hne
    have h1 := ih (O.step R op) (by rw [secStep_size]; exact hk)
      (fun op' hop' => hne op' (List.mem_cons_of_mem _ hop'))
    simp only [Ops.run, List.foldl_cons] at h1 ⊢
    rw [h1, secStep_getElem!_of_ne O R op hk (hne op List.mem_cons_self)]

theorem secInitRegs_getElem!_of_ge (O : Ops M V) (A B : M) {n k : ℕ} (hk : k < n) (h2 : 2 ≤ k) :
    (O.initRegs A B n)[k]! = O.one := by
  unfold Ops.initRegs
  rw [getElem!_pos _ k (by simpa using hk), Array.getElem_ofFn]
  have h0 : k ≠ 0 := by omega
  have h1 : k ≠ 1 := by omega
  simp [h0, h1]

theorem elemAbelian_of_secCheck_one (Sp : OpsSpec O p d)
    (S : Submonoid (Matrix (Fin d) (Fin d) (ZMod p))) (D : SecData)
    (hA : Sp.WF (O.decode D.seedA) ∧ Sp.toMat (O.decode D.seedA) ∈ S)
    (hB : Sp.WF (O.decode D.seedB) ∧ Sp.toMat (O.decode D.seedB) ∈ S)
    (h : O.secCheck D = true) (h2 : 2 ≤ D.tReg) (hw : ∀ op ∈ D.prog, secOpDst op ≠ D.tReg) :
    ∃ E : Subgroup Sˣ, Open.IsElemAbelian 2 E ∧ Nat.card E = 2 ^ D.outs.length := by
  unfold Ops.secCheck at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨hn, hprog⟩, houts⟩, htreg⟩, hsec⟩ := h
  obtain ⟨hs0, hok0⟩ := Sp.initRegs_ok S hA hB D.nregs
  obtain ⟨hs, hok⟩ := Sp.run_ok S D.prog hok0 (by rw [hs0]; exact hprog)
  set R := O.run D.prog (O.initRegs (O.decode D.seedA) (O.decode D.seedB) D.nregs)
  rw [hs0] at hs
  set xs := D.outs.map fun r => R[r]! with hxsdef
  set T := R[D.tReg]! with hTdef
  have hTok : Sp.WF T ∧ Sp.toMat T ∈ S := hok D.tReg (by rw [hs]; exact htreg)
  have hT1 : Sp.toMat T = 1 := by
    have h1 := secRun_getElem!_of_ne O D.prog
      (O.initRegs (O.decode D.seedA) (O.decode D.seedB) D.nregs) (k := D.tReg)
      (by rw [hs0]; exact htreg) hw
    rw [secInitRegs_getElem!_of_ge O _ _ htreg h2] at h1
    rw [hTdef, h1, Sp.toMat_one]
  have hxs : ∀ X ∈ xs, Sp.WF X ∧ Sp.toMat X ∈ S := by
    intro X hX
    obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hX
    exact hok r (by rw [hs]; exact of_decide_eq_true (List.all_eq_true.1 houts r hr))
  have hw' : ∀ X ∈ xs, Sp.WF X := fun X hX => (hxs X hX).1
  unfold Ops.secOK at hsec
  simp only [Bool.and_eq_true] at hsec
  obtain ⟨⟨⟨htt, hxT⟩, hcomm⟩, hker⟩ := hsec
  have hpair := Sp.pairwise_of_commsModOK hTok.1 hw' hcomm
  have hsq : ∀ X ∈ xs, Sp.toMat X * Sp.toMat X = 1 := by
    intro X hX
    have h1 := List.all_eq_true.1 hxT X hX
    rw [Bool.and_eq_true] at h1
    have wX := hw' X hX
    have h2 := h1.2
    unfold Ops.inN at h2
    rw [Bool.or_eq_true] at h2
    rcases h2 with h2 | h2
    · have := Sp.toMat_eq (Sp.mul_wf wX wX) Sp.one_wf h2
      rwa [Sp.toMat_mul wX wX, Sp.toMat_one] at this
    · have := Sp.toMat_eq (Sp.mul_wf wX wX) hTok.1 h2
      rwa [Sp.toMat_mul wX wX, hT1] at this
  rw [← List.length_map (f := fun r => R[r]!)]
  refine elemAbelian_units_two S (fun i : Fin xs.length => Sp.toMat xs[i])
    (fun i => (hxs _ (List.getElem_mem i.isLt)).2)
    (fun i => hsq _ (List.getElem_mem i.isLt)) (fun i j => ?_)
    (fun a ha => (Sp.ne_of_kerModOK hTok.1 hw' hker a ha).1)
  rcases lt_trichotomy i j with hij | rfl | hij
  · rcases List.pairwise_iff_getElem.1 hpair i j i.isLt j.isLt hij with h | h
    · exact h
    · rwa [hT1, one_mul] at h
  · rfl
  · rcases List.pairwise_iff_getElem.1 hpair j i j.isLt i.isLt hij with h | h
    · exact h.symm
    · rw [hT1, one_mul] at h
      exact h.symm

theorem elemAbelian_of_secCheck_seed [NeZero p] (Sp : OpsSpec O p d) (D : SecData)
    (h : O.secCheck D = true) (h2 : 2 ≤ D.tReg) (hw : ∀ op ∈ D.prog, secOpDst op ≠ D.tReg) :
    ∃ E : Subgroup (NativeSporadic.seedMonoid p d 1 D.seedA D.seedB)ˣ,
      Open.IsElemAbelian 2 E ∧ Nat.card E = 2 ^ D.outs.length := by
  set S := NativeSporadic.seedMonoid p d 1 D.seedA D.seedB
  have hA : Sp.WF (O.decode D.seedA) ∧ Sp.toMat (O.decode D.seedA) ∈ S :=
    ⟨Sp.decode_wf _, by
      rw [Sp.toMat_decode]
      exact Submonoid.subset_closure (Set.mem_insert _ _)⟩
  have hB : Sp.WF (O.decode D.seedB) ∧ Sp.toMat (O.decode D.seedB) ∈ S :=
    ⟨Sp.decode_wf _, by
      rw [Sp.toMat_decode]
      exact Submonoid.subset_closure (Set.mem_insert_of_mem _ rfl)⟩
  exact elemAbelian_of_secCheck_one Sp S D hA hB h h2 hw

end Regs

theorem five_le_pRank_He :
    5 ≤ CFSG.Open.pRank 2 (⊤ : Subgroup NativeSporadic.He) := by
  obtain ⟨E, hE, hc⟩ := elemAbelian_of_secCheck_seed (specP 7 50) heSec
    CFSG.GH74.Filter.he_secCheck (by decide) (by decide)
  exact CFSG.SectionRank.le_pRank (by norm_num) le_top hE (hc.trans (by decide))

end CFSG.RankThree.PartTwo.Sec21.Item21Early2Proof
