module

public import CFSG.Sporadic.SuzOddCore.CTIBase
public import CFSG.Certificates.Kernel.TitsOver.Pair

public noncomputable section

namespace CFSG.Sporadic.SuzOddCore

open CFSG CFSG.Certificates CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.PSL3Four.Native
  CFSG.ComponentClassification.PSL3Four
open scoped commutatorElement

theorem invInnerGenArrs_size0 : (invInnerGenArrs 0).size = 22 := by
  simp [invInnerGenArrs, invInnerGenCounts]

theorem invInnerGenArrs_size1 : (invInnerGenArrs 1).size = 10 := by
  simp [invInnerGenArrs, invInnerGenCounts]

theorem dGens_size : dGens.size = 5 := by simp [dGens]

theorem qGens_size : qGens.size = 6 := by simp [qGens]

theorem tabRep_wordTab {m : ℕ} {gs : Array Tab} {f : ℕ → Equiv.Perm (Fin m)}
    (hgs : ∀ j < gs.size, TabRep gs[j]! (f j)) :
    ∀ w : List ℕ, (∀ j ∈ w, j < gs.size) → TabRep (wordTab m gs w) ((w.map f).prod)
  | [], _ => by simpa [wordTab] using (TabRep.idTab (n := m))
  | j :: w, hw => by
    have h1 : wordTab m gs (j :: w) = comp m gs[j]! (wordTab m gs w) := by
      simp only [wordTab, List.foldr_cons]
    rw [h1, List.map_cons, List.prod_cons]
    exact (hgs j (hw j (List.mem_cons_self))).comp
      (tabRep_wordTab hgs w fun i hi => hw i (List.mem_cons_of_mem _ hi))

theorem classWords_lt (l : ℕ) : ∀ j ∈ classWords.getD l [], j < dGens.size := by
  rw [dGens_size]
  intro j hj
  have : ∀ w ∈ classWords, ∀ j ∈ w, j < 5 := by decide
  rw [List.getD_eq_getElem?_getD] at hj
  cases hh : classWords[l]? with
  | none => simp [hh] at hj
  | some w => rw [hh, Option.getD_some] at hj; exact this w (List.mem_of_getElem? hh) j hj

theorem qWords_lt (j : ℕ) : ∀ k ∈ qWords.getD j [], k < 10 := by
  intro k hk
  have : ∀ w ∈ qWords, ∀ k ∈ w, k < 10 := by decide
  rw [List.getD_eq_getElem?_getD] at hk
  cases hh : qWords[j]? with
  | none => simp [hh] at hk
  | some w => rw [hh, Option.getD_some] at hk; exact this w (List.mem_of_getElem? hh) k hk


@[expose] def rho0Of (hm : (fixList 0).length = 42) : invE 0 →* Equiv.Perm (Fin 42) :=
  cRho (i := 0) (by norm_num) hm

@[expose] def kpermOf (hm : (fixList 0).length = 42) (k : ℕ) : Equiv.Perm (Fin 42) :=
  rho0Of hm (innerGenE (i := 0) (by norm_num) k)

theorem kpermOf_mem (hm : (fixList 0).length = 42) (k : ℕ) : kpermOf hm k ∈ (rho0Of hm).range :=
  ⟨_, rfl⟩

theorem tabRep_kpermOf (hm : (fixList 0).length = 42) {k : ℕ} (hk : k < 22) :
    TabRep (kGens 0)[k]! (kpermOf hm k) :=
  tabRep_kGens (i := 0) (by norm_num) hm (by rw [invInnerGenArrs_size0]; exact hk)

theorem tabRep_kpermOf_inv (hm : (fixList 0).length = 42) {k : ℕ} (hk : k < 22) :
    TabRep (kInvs 0)[k]! (kpermOf hm k)⁻¹ := by
  have hs : k < (kGens 0).size := by simpa [kGens, invInnerGenArrs_size0] using hk
  have e : (kInvs 0)[k]! = invTab 42 (kGens 0)[k]! := by
    rw [getElem!_pos (kInvs 0) k (by simpa [kInvs] using hs), getElem!_pos (kGens 0) k hs]
    simp [kInvs, hm]
  rw [e]
  exact CFSG.KS.TitsOver.tabRep_invTab (tabRep_kpermOf hm hk)

@[expose] def dpermOf (hm : (fixList 0).length = 42) (j : ℕ) : Equiv.Perm (Fin 42) :=
  ⁅kpermOf hm 1, kpermOf hm (j + 2)⁆

theorem tabRep_dpermOf (hm : (fixList 0).length = 42) {j : ℕ} (hj : j < 5) :
    TabRep dGens[j]! (dpermOf hm j) := by
  rw [dGens, getElem!_pos _ j (by simpa using hj), Array.getElem_ofFn]
  exact (tabRep_kpermOf hm (k := 1) (by norm_num)).commTab
    (tabRep_kpermOf hm (k := j + 2) (by omega)) (tabRep_kpermOf_inv hm (k := 1) (by norm_num))
    (tabRep_kpermOf_inv hm (k := j + 2) (by omega))

@[expose] def suzDOf (hm : (fixList 0).length = 42) : Subgroup (Equiv.Perm (Fin 42)) :=
  Subgroup.closure {g | ∃ j < 5, dpermOf hm j = g}

@[expose] def repPermOf (hm : (fixList 0).length = 42) (l : ℕ) : Equiv.Perm (Fin 42) :=
  ((classWords.getD l []).map (dpermOf hm)).prod

theorem tabRep_repPermOf (hm : (fixList 0).length = 42) (l : ℕ) :
    TabRep (classRep l) (repPermOf hm l) :=
  tabRep_wordTab (fun j hj => tabRep_dpermOf hm (by rw [dGens_size] at hj; exact hj)) _
    (classWords_lt l)

theorem repPermOf_mem (hm : (fixList 0).length = 42) (l : ℕ) : repPermOf hm l ∈ suzDOf hm := by
  refine (suzDOf hm).list_prod_mem fun x hx => ?_
  obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hx
  have := classWords_lt l j hj
  rw [dGens_size] at this
  exact Subgroup.subset_closure ⟨j, this, rfl⟩

@[expose] def classFunOf (hm : (fixList 0).length = 42) (l : Fin 10) : ConjClasses (suzDOf hm) :=
  ConjClasses.mk ⟨repPermOf hm l, repPermOf_mem hm l⟩

@[expose] def rho1Of (hm : (fixList 1).length = 54) : invE 1 →* Equiv.Perm (Fin 54) :=
  cRho (i := 1) (by norm_num) hm

@[expose] def kperm1Of (hm : (fixList 1).length = 54) (k : ℕ) : Equiv.Perm (Fin 54) :=
  rho1Of hm (innerGenE (i := 1) (by norm_num) k)

theorem tabRep_kperm1Of (hm : (fixList 1).length = 54) {k : ℕ} (hk : k < 10) :
    TabRep (kGens 1)[k]! (kperm1Of hm k) :=
  tabRep_kGens (i := 1) (by norm_num) hm (by rw [invInnerGenArrs_size1]; exact hk)

theorem tabRep_kperm1Of_inv (hm : (fixList 1).length = 54) {k : ℕ} (hk : k < 10) :
    TabRep (kInvs 1)[k]! (kperm1Of hm k)⁻¹ := by
  have hs : k < (kGens 1).size := by simpa [kGens, invInnerGenArrs_size1] using hk
  have e : (kInvs 1)[k]! = invTab 54 (kGens 1)[k]! := by
    rw [getElem!_pos (kInvs 1) k (by simpa [kInvs] using hs), getElem!_pos (kGens 1) k hs]
    simp [kInvs, hm]
  rw [e]
  exact CFSG.KS.TitsOver.tabRep_invTab (tabRep_kperm1Of hm hk)

@[expose] def qpermOf (hm : (fixList 1).length = 54) (j : ℕ) : Equiv.Perm (Fin 54) :=
  ((qWords.getD j []).map (kperm1Of hm)).prod

theorem tabRep_qpermOf (hm : (fixList 1).length = 54) {j : ℕ} (hj : j < 6) :
    TabRep qGens[j]! (qpermOf hm j) := by
  have hsz : (kGens 1).size = 10 := by simp [kGens, invInnerGenArrs_size1]
  rw [qGens, getElem!_pos _ j (by simpa using hj), Array.getElem_ofFn]
  exact tabRep_wordTab (fun k hk => tabRep_kperm1Of hm (by rw [hsz] at hk; exact hk)) _
    (fun k hk => by rw [hsz]; exact qWords_lt j k hk)

@[expose] def suzQbarOf (hm : (fixList 1).length = 54) : Subgroup (Equiv.Perm (Fin 54)) :=
  Subgroup.closure {g | ∃ j < 6, qpermOf hm j = g}

end CFSG.Sporadic.SuzOddCore
