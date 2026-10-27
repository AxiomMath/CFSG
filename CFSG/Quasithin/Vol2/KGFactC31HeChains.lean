module

public import CFSG.Quasithin.Vol2.KGFactC31Hat
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Quasithin.Vol2.KGFactC31HeCent
public import CFSG.Quasithin.Vol2.KGFactC31WordBasis

public section

namespace CFSG.Quasithin.KGC31.He

open CFSG.Open CFSG.QuasithinUnique CFSG.Blueprint CFSG.Quasithin.KGC31 CFSG.Sporadic.HeldB
  CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates CFSG.Certificates.Native
  CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.PairNative CFSG.Quasithin.KGC31.Native
  _root_.Certificates

theorem size_foldl_push (f : Array (Array ℕ) → List ℤ → Array ℕ) :
    ∀ (L : List (List ℤ)) (A₀ : Array (Array ℕ)),
      (L.foldl (fun S w => S.push (f S w)) A₀).size = A₀.size + L.length
  | [], A₀ => rfl
  | w :: L, A₀ => by
    rw [List.foldl_cons, size_foldl_push f L, Array.size_push, List.length_cons]
    omega

theorem getElem!_foldl_push (f : Array (Array ℕ) → List ℤ → Array ℕ) :
    ∀ (L : List (List ℤ)) (A₀ : Array (Array ℕ)) {i : ℕ}, i < A₀.size →
      (L.foldl (fun S w => S.push (f S w)) A₀)[i]! = A₀[i]!
  | [], A₀, i, _ => rfl
  | w :: L, A₀, i, hi => by
    rw [List.foldl_cons, getElem!_foldl_push f L _ (by rw [Array.size_push]; omega)]
    rw [getElem!_pos _ i (by rw [Array.size_push]; omega), getElem!_pos A₀ i hi,
      Array.getElem_push_lt]

theorem card_Ns : Nat.card nsGrp = 138240 := c_cardNs

theorem card_Ls : Nat.card lGrp = 69120 := c_cardLs

theorem card_N7 : Nat.card n7Grp = 21504 := c_cardN7

theorem letters_lsGenW : lsGenW.all (lettersOK 2) = true := by
  have h := c_letters
  simp only [List.all_append, Bool.and_eq_true] at h
  exact h.1.2

theorem letters_njW : njW.all (lettersOK 2) = true := by
  have h := c_letters
  simp only [List.all_append, Bool.and_eq_true] at h
  exact h.2

theorem closure_le_heP {W : List (List ℤ)}
    (hW : W.all (lettersOK 2) = true) : Subgroup.closure {g | ∃ w ∈ W, elt w = g} ≤ heP := by
  rw [Subgroup.closure_le]
  rintro _ ⟨w, hw, rfl⟩
  exact elt_mem_heP (List.all_eq_true.1 hW w hw)

theorem forall₂_Q :
    List.Forall₂ (Rep 8330) qA (List.ofFn vQ) := forall₂_vOf c_qLen letters_qW

theorem vE_mem (i : Fin 6) : vE i ∈ heP :=
  vOf_mem letters_eW i

theorem vQ_mem (i : Fin 4) : vQ i ∈ heP :=
  vOf_mem letters_qW i

theorem eSub_le_heP {k : ℕ} {v : Fin k → Equiv.Perm (Fin 8330)} (hv : EBasis v)
    (hvP : ∀ i, v i ∈ heP) : eSub hv ≤ heP := by
  rw [eSub_eq_closure, Subgroup.closure_le]
  rintro _ ⟨i, rfl⟩
  exact hvP i

theorem E_le_heP : eSub basis_E ≤ heP :=
  eSub_le_heP basis_E vE_mem

theorem Q_le_heP : eSub basis_Q ≤ heP :=
  eSub_le_heP basis_Q vQ_mem

theorem elt_mem_eNorm_Q {w : List ℤ}
    (hw : lettersOK 2 w = true) (h : normsW bs qA (wA w) (wAi w) = true) :
    elt w ∈ eNorm basis_Q :=
  mem_eNorm_of_normsW baseFaithful_heP hbs basis_Q forall₂_Q vQ_mem
    (rep_wA (lettersOK_mono (by norm_num) hw)) (rep_wAi (lettersOK_mono (by norm_num) hw))
    (elt_mem_heP hw) h

theorem Ns_le : nsGrp ≤ heP ⊓ eNorm basis_E := by
  have h := c_normNs
  rw [heE_eq] at h
  exact h

theorem N7_le : n7Grp ≤ heP ⊓ eNorm basis_Q := by
  have h := c_normN7
  rw [heQ_eq] at h
  exact h

theorem letters_y5W : lettersOK 2 y5W = true :=
  List.all_eq_true.1 letters_lsGenW _ (by rw [lsGenW]; exact List.mem_cons_self ..)

theorem Ls_eq : lGrp = Subgroup.closure {g | ∃ w ∈ lsGenW, elt w = g} := rfl

theorem mem_lsGenW {w : List ℤ} (hw : w ∈ lsGenW) :
    w = y5W ∨ ∃ n ∈ njW, w = n ++ y5W ++ invW n := by
  rw [lsGenW, List.mem_cons, List.mem_map] at hw
  rcases hw with rfl | ⟨n, hn, rfl⟩
  · exact Or.inl rfl
  · exact Or.inr ⟨n, hn, rfl⟩

theorem elt_lsGen {n : List ℤ} (hn : n ∈ njW) :
    elt (n ++ y5W ++ invW n) = elt n * elt y5W * (elt n)⁻¹ :=
  elt_conjW (lettersOK_mono (by norm_num) (List.all_eq_true.1 letters_njW n hn))
    (lettersOK_mono (by norm_num) letters_y5W)

theorem Ls_le :
    lGrp ≤ heP ⊓ eNorm basis_E := by
  have h := c_normL
  rw [heE_eq] at h
  exact le_inf (closure_le_heP letters_lsGenW) h

theorem y5_mem_Ls : elt y5W ∈ lGrp :=
  Subgroup.subset_closure ⟨y5W, by rw [lsGenW]; exact List.mem_cons_self .., rfl⟩

theorem nj_mem_eNorm {n : List ℤ} (hn : n ∈ njW) : elt n ∈ eNorm basis_E := by
  have h := c_normNj n hn
  rw [heE_eq] at h
  exact h

theorem E_le_Ls : eSub basis_E ≤ lGrp := by
  rw [← heE_eq]
  exact c_EL

theorem orderOf_y5 : orderOf (elt y5W) = 5 := c_y5

@[expose] def bPt (i : Fin 6) : Fin 8330 := ⟨bB.getD i 0 % 8330, Nat.mod_lt _ (by norm_num)⟩

theorem mem_bB : ∀ i, (bPt i : ℕ) ∈ bB := by decide

theorem exists_bPt : ∀ p ∈ bB, ∃ i, (bPt i : ℕ) = p := by decide

theorem bPt_inj : Function.Injective bPt := by decide

@[expose] def bBlk (i : Fin 6) : Finset (Fin 8330) := {bPt i}

theorem bBlk_inj : Function.Injective bBlk := fun _ _ h => bPt_inj (Finset.singleton_injective h)

@[expose] def bFix : Subgroup (Equiv.Perm (Fin 8330)) where
  carrier := {g | ∀ i, g (bPt i) = bPt i}
  one_mem' := fun _ => rfl
  mul_mem' := fun {a b} ha hb i => by rw [Equiv.Perm.mul_apply, hb i, ha i]
  inv_mem' := fun {a} ha i => by
    rw [Equiv.Perm.inv_eq_iff_eq]
    exact (ha i).symm

theorem mem_bFix {g : Equiv.Perm (Fin 8330)} : g ∈ bFix ↔ ∀ i, g (bPt i) = bPt i := Iff.rfl

theorem Ls_le_blockStab : lGrp ≤ blockStab bBlk bBlk_inj := by
  rw [Ls_eq, Subgroup.closure_le]
  rintro _ ⟨w, hw, rfl⟩
  intro i
  obtain ⟨j, hj⟩ := exists_bPt _ (c_LB w hw (bPt i) (mem_bB i))
  refine ⟨j, ?_⟩
  rw [bBlk, bBlk, Finset.image_singleton, Finset.singleton_inj]
  apply Fin.ext
  rw [hj]

theorem E_le_bFix : eSub basis_E ≤ bFix := by
  rw [eSub_eq_closure, Subgroup.closure_le]
  rintro _ ⟨i, rfl⟩
  intro j
  exact c_EB i (bPt j) (mem_bB j)

theorem card_fix_Ls :
    Nat.card {x : lGrp // (x : Equiv.Perm (Fin 8330)) ∈ bFix} = 192 := by
  rw [← c_ker]
  refine Nat.card_congr (Equiv.subtypeEquivRight fun x => ⟨fun h p hp => ?_, fun h i => ?_⟩)
  · obtain ⟨i, hi⟩ := exists_bPt p hp
    have hpi : bPt i = p := Fin.ext hi
    rw [← hpi]
    exact h i
  · exact h _ (mem_bB i)

end CFSG.Quasithin.KGC31.He

end
