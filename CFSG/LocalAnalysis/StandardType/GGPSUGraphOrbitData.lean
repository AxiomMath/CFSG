module

public import CFSG.LocalAnalysis.StandardType.GGPSUGraphPure
public import CFSG.LocalAnalysis.StandardType.GGPSUGraphOrbitInv
public import CFSG.LocalAnalysis.StandardType.GGPSLGraphPure
public import CFSG.LocalAnalysis.StandardType.GGBlockEmbed
public import CFSG.LocalAnalysis.StandardType.GGLocalFamilyCount

public section

namespace CFSG.StandardType

open CFSG.StandardType.ClassicalPosition Matrix
open CFSG.LocalAnalysis.ComponentInitial

private noncomputable def psuC3b_orbit {f n : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData 2 f K) (X : GL (Fin n) K)
    (e : Matrix (Fin n) (Fin n) K) : Finset (Matrix (Fin n) (Fin n) K) := by
  classical
  exact {e, psuDag h e, psuPsi h X e, psuDag h (psuPsi h X e)}

private lemma psuC3b_orbit_self {f n : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K)
    (X : GL (Fin n) K) (e : Matrix (Fin n) (Fin n) K) :
    e ∈ psuC3b_orbit h X e := by
  simp [psuC3b_orbit]

private lemma psuC3b_dag_psi {f n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    {h : UnitaryFieldData 2 f K} {X B : GL (Fin n) K} (S : PSUGraphSetting h n X B)
    (a : Matrix (Fin n) (Fin n) K) :
    psuDag h (psuPsi h X a) = psuPsi h X (psuDag h a) := by
  simp only [psuPsi]
  rw [← psuTheta_dag h X S.X_mem S.X_sq (psuDag h a), psuDag_dag]

private lemma psuC3b_dag_psi_dag_psi {f n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    {h : UnitaryFieldData 2 f K} {X B : GL (Fin n) K} (S : PSUGraphSetting h n X B)
    (a : Matrix (Fin n) (Fin n) K) :
    psuDag h (psuPsi h X (psuDag h (psuPsi h X a))) = a := by
  rw [psuC3b_dag_psi S (psuDag h (psuPsi h X a)), psuDag_dag,
    psuPsi_psi h X S.X_mem S.X_sq]

private lemma psuC3b_orbit_dag_mem {f n : ℕ} {K : Type} [Field K]
    {h : UnitaryFieldData 2 f K} {X : GL (Fin n) K}
    {e x : Matrix (Fin n) (Fin n) K} (hx : x ∈ psuC3b_orbit h X e) :
    psuDag h x ∈ psuC3b_orbit h X e := by
  simp only [psuC3b_orbit, Finset.mem_insert, Finset.mem_singleton] at hx ⊢
  rcases hx with rfl | rfl | rfl | rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inl (psuDag_dag h e)
  · exact Or.inr (Or.inr (Or.inr rfl))
  · exact Or.inr (Or.inr (Or.inl (psuDag_dag h (psuPsi h X e))))

private lemma psuC3b_orbit_psi_mem {f n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    {h : UnitaryFieldData 2 f K} {X B : GL (Fin n) K} (S : PSUGraphSetting h n X B)
    {e x : Matrix (Fin n) (Fin n) K} (hx : x ∈ psuC3b_orbit h X e) :
    psuPsi h X x ∈ psuC3b_orbit h X e := by
  simp only [psuC3b_orbit, Finset.mem_insert, Finset.mem_singleton] at hx ⊢
  rcases hx with rfl | rfl | rfl | rfl
  · exact Or.inr (Or.inr (Or.inl rfl))
  · exact Or.inr (Or.inr (Or.inr (psuC3b_dag_psi S e).symm))
  · exact Or.inl (psuPsi_psi h X S.X_mem S.X_sq e)
  · exact Or.inr (Or.inl (by
      rw [← psuC3b_dag_psi S (psuPsi h X e), psuPsi_psi h X S.X_mem S.X_sq]))

private lemma psuC3b_orbit_subset {f n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    {h : UnitaryFieldData 2 f K} {X B : GL (Fin n) K} (S : PSUGraphSetting h n X B)
    {e e' : Matrix (Fin n) (Fin n) K} (he' : e' ∈ psuC3b_orbit h X e) :
    psuC3b_orbit h X e' ⊆ psuC3b_orbit h X e := by
  intro x hx
  simp only [psuC3b_orbit, Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact he'
  · exact psuC3b_orbit_dag_mem he'
  · exact psuC3b_orbit_psi_mem S he'
  · exact psuC3b_orbit_dag_mem (psuC3b_orbit_psi_mem S he')

private lemma psuC3b_orbit_symm {f n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    {h : UnitaryFieldData 2 f K} {X B : GL (Fin n) K} (S : PSUGraphSetting h n X B)
    {e e' : Matrix (Fin n) (Fin n) K} (he' : e' ∈ psuC3b_orbit h X e) :
    e ∈ psuC3b_orbit h X e' := by
  simp only [psuC3b_orbit, Finset.mem_insert, Finset.mem_singleton] at he' ⊢
  rcases he' with rfl | rfl | rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr (Or.inl (psuDag_dag h e).symm)
  · exact Or.inr (Or.inr (Or.inl (psuPsi_psi h X S.X_mem S.X_sq e).symm))
  · exact Or.inr (Or.inr (Or.inr (psuC3b_dag_psi_dag_psi S e).symm))

private lemma psuC3b_orbit_eq {f n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    {h : UnitaryFieldData 2 f K} {X B : GL (Fin n) K} (S : PSUGraphSetting h n X B)
    {e e' : Matrix (Fin n) (Fin n) K} (he' : e' ∈ psuC3b_orbit h X e) :
    psuC3b_orbit h X e' = psuC3b_orbit h X e :=
  Finset.Subset.antisymm (psuC3b_orbit_subset S he')
    (psuC3b_orbit_subset S (psuC3b_orbit_symm S he'))

private theorem psuC3b_transversal {f n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    {h : UnitaryFieldData 2 f K} {X B : GL (Fin n) K} (S : PSUGraphSetting h n X B)
    (P : Finset (Matrix (Fin n) (Fin n) K))
    :
    ∃ R : Finset (Matrix (Fin n) (Fin n) K), R ⊆ P ∧
      ∀ e ∈ P, ∃! r, r ∈ R ∧
        (r = e ∨ r = psuDag h e ∨ r = psuPsi h X e ∨ r = psuDag h (psuPsi h X e)) := by
  classical
  let α := {e : Matrix (Fin n) (Fin n) K // e ∈ P}
  let rel : α → α → Prop := fun r s => s.1 ∈ psuC3b_orbit h X r.1
  have hrefl : ∀ a : α, rel a a := fun a => psuC3b_orbit_self h X a.1
  have hsymm : ∀ a b : α, rel a b → rel b a := fun a b hab => psuC3b_orbit_symm S hab
  have htrans : ∀ a b c : α, rel a b → rel b c → rel a c := by
    intro a b c hab hbc
    change b.1 ∈ psuC3b_orbit h X a.1 at hab
    change c.1 ∈ psuC3b_orbit h X b.1 at hbc
    change c.1 ∈ psuC3b_orbit h X a.1
    rw [← psuC3b_orbit_eq S hab]
    exact hbc
  letI inst : Setoid α :=
    { r := rel
      iseqv := ⟨hrefl, fun {a b} hab => hsymm a b hab,
        fun {a b c} hab hbc => htrans a b c hab hbc⟩ }
  let rep : α → Matrix (Fin n) (Fin n) K := fun e => (Quotient.out (Quotient.mk inst e)).1
  let R : Finset (Matrix (Fin n) (Fin n) K) := P.attach.image rep
  have hRsub : R ⊆ P := by
    intro r hr
    simp only [R, Finset.mem_image, Finset.mem_attach] at hr
    obtain ⟨e, -, rfl⟩ := hr
    exact (Quotient.out (Quotient.mk inst e)).2
  refine ⟨R, hRsub, ?_⟩
  intro e he
  let eA : α := ⟨e, he⟩
  let q := Quotient.mk inst eA
  let r : Matrix (Fin n) (Fin n) K := (Quotient.out q).1
  have hrR : r ∈ R := by
    simp only [R, Finset.mem_image, Finset.mem_attach]
    refine ⟨eA, ?_, rfl⟩
    exact Finset.mem_attach P eA
  have hrel : rel eA (Quotient.out q) := by
    have h1 : Quotient.mk inst (Quotient.out q) = Quotient.mk inst eA := by
      rw [Quotient.out_eq]
    exact hsymm _ _ (Quotient.exact h1)
  have hr_ex : r = e ∨ r = psuDag h e ∨ r = psuPsi h X e ∨
      r = psuDag h (psuPsi h X e) := by
    have hh := hrel
    change (Quotient.out q).1 ∈ psuC3b_orbit h X e at hh
    simp only [psuC3b_orbit, Finset.mem_insert, Finset.mem_singleton] at hh
    simpa [r] using hh
  refine ⟨r, ⟨hrR, hr_ex⟩, ?_⟩
  intro r' hr'
  obtain ⟨hr'R, hr'disj⟩ := hr'
  have hr'P : r' ∈ P := hRsub hr'R
  let r'A : α := ⟨r', hr'P⟩
  have hrel_e : rel eA r'A := by
    change r' ∈ psuC3b_orbit h X e
    simp only [psuC3b_orbit, Finset.mem_insert, Finset.mem_singleton]
    exact hr'disj
  have hmk0 : Quotient.mk inst eA = Quotient.mk inst r'A := Quotient.sound hrel_e
  have hmk : Quotient.mk inst r'A = Quotient.mk inst eA := hmk0.symm
  have hzmem : r' ∈ R := hr'R
  simp only [R, Finset.mem_image, Finset.mem_attach] at hzmem
  obtain ⟨z, -, hz⟩ := hzmem
  have hzr : (Quotient.out (Quotient.mk inst z)).1 = r' := hz
  have hzα : Quotient.out (Quotient.mk inst z) = r'A := by
    apply Subtype.ext
    exact hzr
  have hzeq : Quotient.mk inst z = Quotient.mk inst eA := by
    rw [← Quotient.out_eq (Quotient.mk inst z), hzα, hmk]
  have hout : Quotient.out (Quotient.mk inst z) = Quotient.out (Quotient.mk inst eA) := by
    rw [hzeq]
  calc r' = (Quotient.out (Quotient.mk inst z)).1 := hzr.symm
    _ = (Quotient.out (Quotient.mk inst eA)).1 := congrArg Subtype.val hout
    _ = r := rfl

private theorem psuC3b_orbit_size {f n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    {h : UnitaryFieldData 2 f K} {X B : GL (Fin n) K} (S : PSUGraphSetting h n X B)
    (e : Matrix (Fin n) (Fin n) K) :
    Nat.card {e' : Matrix (Fin n) (Fin n) K // e' = e ∨ e' = psuDag h e ∨
      e' = psuPsi h X e ∨ e' = psuDag h (psuPsi h X e)} = psuOrbSize (psuKind h X B e) := by
  classical
  haveI : Fintype K := Fintype.ofFinite K
  have hEq : Nat.card {e' : Matrix (Fin n) (Fin n) K // e' = e ∨ e' = psuDag h e ∨
      e' = psuPsi h X e ∨ e' = psuDag h (psuPsi h X e)} =
      (psuC3b_orbit h X e).card := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    congr 1
    ext x
    simp [psuC3b_orbit]
  rw [hEq]
  by_cases hd : psuDag h e = e
  · by_cases hp : psuPsi h X e = e
    · have hk : psuKind h X B e = 0 := by simp [psuKind, hd, hp]
      rw [hk]
      have horb : psuC3b_orbit h X e = {e} := by
        ext x; simp [psuC3b_orbit, hd, hp]
      rw [horb]
      simp [psuOrbSize]
    · have hk : psuKind h X B e = 1 := by simp [psuKind, hd, hp]
      rw [hk]
      have hdpsi : psuDag h (psuPsi h X e) = psuPsi h X e := by
        rw [psuC3b_dag_psi S e, hd]
      have horb : psuC3b_orbit h X e = {e, psuPsi h X e} := by
        ext x; simp [psuC3b_orbit, hd, hp, hdpsi]
      rw [horb, Finset.card_pair (Ne.symm hp)]
      simp [psuOrbSize]
  · by_cases hp : psuPsi h X e = e
    · by_cases ht : psuPsiTrivial h X B e
      · have hk : psuKind h X B e = 2 := by simp [psuKind, hd, hp, ht]
        rw [hk]
        have horb : psuC3b_orbit h X e = {e, psuDag h e} := by
          ext x; simp [psuC3b_orbit, hp]
        rw [horb, Finset.card_pair (Ne.symm hd)]
        simp [psuOrbSize]
      · have hk : psuKind h X B e = 3 := by simp [psuKind, hd, hp, ht]
        rw [hk]
        have horb : psuC3b_orbit h X e = {e, psuDag h e} := by
          ext x; simp [psuC3b_orbit, hp]
        rw [horb, Finset.card_pair (Ne.symm hd)]
        simp [psuOrbSize]
    · by_cases h4 : psuPsi h X e = psuDag h e
      · have hk : psuKind h X B e = 4 := by simp [psuKind, hd, hp, h4]
        rw [hk]
        have horb : psuC3b_orbit h X e = {e, psuDag h e} := by
          ext x; simp [psuC3b_orbit, h4, psuDag_dag, or_comm]
        rw [horb, Finset.card_pair (Ne.symm hd)]
        simp [psuOrbSize]
      · have hk : psuKind h X B e = 5 := by simp [psuKind, hd, hp, h4]
        rw [hk]
        have hdag_psi_ne : psuDag h (psuPsi h X e) ≠ e := by
          intro hh
          apply h4
          have hh' := congrArg (psuPsi h X) hh
          rw [show psuPsi h X (psuDag h (psuPsi h X e)) =
              psuDag h (psuPsi h X (psuPsi h X e)) from
            (psuC3b_dag_psi S (psuPsi h X e)).symm,
            psuPsi_psi h X S.X_mem S.X_sq] at hh'
          exact hh'.symm
        have hdag_dagpsi_ne : psuDag h (psuPsi h X e) ≠ psuDag h e := by
          intro hh
          apply hp
          have hh' : psuPsi h X e = e := by
            have h1 := congrArg (psuDag h) hh
            simp only [psuDag_dag] at h1
            exact h1
          exact hh'
        have hpsi_dagpsi_ne : psuDag h (psuPsi h X e) ≠ psuPsi h X e := by
          intro hh
          apply hd
          have hh' := congrArg (psuPsi h X) hh
          rw [show psuPsi h X (psuDag h (psuPsi h X e)) =
              psuDag h (psuPsi h X (psuPsi h X e)) from
            (psuC3b_dag_psi S (psuPsi h X e)).symm,
            psuPsi_psi h X S.X_mem S.X_sq] at hh'
          exact hh'
        have h1 : e ∉ ({psuDag h e, psuPsi h X e, psuDag h (psuPsi h X e)} :
            Finset (Matrix (Fin n) (Fin n) K)) := by
          simp only [Finset.mem_insert, Finset.mem_singleton]
          rintro (hx | hx | hx)
          · exact hd hx.symm
          · exact hp hx.symm
          · apply h4
            have hh' := congrArg (psuDag h) hx
            rw [psuDag_dag] at hh'
            exact hh'.symm
        have h2 : psuDag h e ∉ ({psuPsi h X e, psuDag h (psuPsi h X e)} :
            Finset (Matrix (Fin n) (Fin n) K)) := by
          simp only [Finset.mem_insert, Finset.mem_singleton]
          rintro (hx | hx)
          · exact h4 hx.symm
          · apply hp
            have hh' : psuPsi h X e = e := by
              have h1 := congrArg (psuDag h) hx
              simp only [psuDag_dag] at h1
              exact h1.symm
            exact hh'
        have h3 : psuPsi h X e ∉ ({psuDag h (psuPsi h X e)} :
            Finset (Matrix (Fin n) (Fin n) K)) := by
          simp only [Finset.mem_singleton]
          exact fun hx => hd (by
            have hh' := congrArg (fun x => psuDag h (psuPsi h X x)) hx
            rw [psuC3b_dag_psi_dag_psi S e] at hh'
            have h2 : psuDag h (psuPsi h X (psuPsi h X e)) = psuDag h e := by
              rw [psuPsi_psi h X S.X_mem S.X_sq]
            rw [h2] at hh'
            exact hh')
        have hc4 : (psuC3b_orbit h X e).card = 4 := by
          rw [show psuC3b_orbit h X e =
            {e, psuDag h e, psuPsi h X e, psuDag h (psuPsi h X e)} from rfl]
          rw [Finset.card_insert_of_notMem h1, Finset.card_insert_of_notMem h2,
            Finset.card_insert_of_notMem h3]
          simp
        rw [hc4]
        simp [psuOrbSize]

private lemma psuC3b_rank_add_idem {ι F : Type} [Fintype ι] [Field F]
    {e f : Matrix ι ι F} (he : IsIdempotentElem e) (hf : IsIdempotentElem f)
    (hef : e * f = 0) (hfe : f * e = 0) :
    Matrix.rank (e + f) = Matrix.rank e + Matrix.rank f := by
  have hee : e * e = e := he.eq
  have hff : f * f = f := hf.eq
  have hsup : LinearMap.range ((e + f).mulVecLin) =
      LinearMap.range e.mulVecLin ⊔ LinearMap.range f.mulVecLin := by
    apply le_antisymm
    · rintro w ⟨v, hv⟩
      rw [Matrix.mulVecLin_apply, Matrix.add_mulVec] at hv
      rw [← hv]
      exact Submodule.add_mem _
        (Submodule.mem_sup_left (LinearMap.mem_range.mpr ⟨v, Matrix.mulVecLin_apply e v⟩))
        (Submodule.mem_sup_right (LinearMap.mem_range.mpr ⟨v, Matrix.mulVecLin_apply f v⟩))
    · refine sup_le ?_ ?_
      · rintro w ⟨v, hv⟩
        refine LinearMap.mem_range.mpr ⟨e.mulVec v, ?_⟩
        rw [Matrix.mulVecLin_apply, Matrix.add_mulVec, Matrix.mulVec_mulVec,
          Matrix.mulVec_mulVec, hee, hfe, Matrix.zero_mulVec, add_zero]
        rw [Matrix.mulVecLin_apply] at hv
        exact hv
      · rintro w ⟨v, hv⟩
        refine LinearMap.mem_range.mpr ⟨f.mulVec v, ?_⟩
        rw [Matrix.mulVecLin_apply, Matrix.add_mulVec, Matrix.mulVec_mulVec,
          Matrix.mulVec_mulVec, hff, hef, Matrix.zero_mulVec, zero_add]
        rw [Matrix.mulVecLin_apply] at hv
        exact hv
  have hker : LinearMap.range f.mulVecLin ≤ LinearMap.ker e.mulVecLin := by
    rintro w ⟨v, hv⟩
    rw [← hv, LinearMap.mem_ker]
    simp only [Matrix.mulVecLin_apply]
    rw [Matrix.mulVec_mulVec, hef]
    simp
  have h_inf : LinearMap.range e.mulVecLin ⊓ LinearMap.range f.mulVecLin = ⊥ := by
    apply le_antisymm _ bot_le
    rintro w ⟨hwe, hwf⟩
    rw [Submodule.mem_bot]
    have hw0 : e.mulVec w = 0 := by
      have h := hker hwf
      simpa [LinearMap.mem_ker, Matrix.mulVecLin_apply] using h
    obtain ⟨v, hv⟩ := hwe
    have hweq : w = e.mulVec w := by
      rw [← hv]
      simp only [Matrix.mulVecLin_apply]
      rw [Matrix.mulVec_mulVec, hee]
    rw [hweq]
    exact hw0
  have hfin := Submodule.finrank_sup_add_finrank_inf_eq
    (LinearMap.range e.mulVecLin) (LinearMap.range f.mulVecLin)
  rw [h_inf, finrank_bot, add_zero] at hfin
  change Module.finrank F (LinearMap.range ((e + f).mulVecLin)) =
    Module.finrank F (LinearMap.range e.mulVecLin) +
      Module.finrank F (LinearMap.range f.mulVecLin)
  rw [hsup]
  exact hfin

private lemma psuC3b_rank_sum_idem {n : ℕ} {K : Type} [Field K]
    (P : Finset (Matrix (Fin n) (Fin n) K))
    (hidem : ∀ e ∈ P, IsIdempotentElem e)
    (horth : ∀ e ∈ P, ∀ e' ∈ P, e ≠ e' → e * e' = 0) :
    Matrix.rank (∑ e ∈ P, e) = ∑ e ∈ P, Matrix.rank e := by
  classical
  induction P using Finset.induction with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    have hidem_s : ∀ e ∈ s, IsIdempotentElem e :=
      fun e he => hidem e (Finset.mem_insert_of_mem he)
    have horth_s : ∀ e ∈ s, ∀ e' ∈ s, e ≠ e' → e * e' = 0 :=
      fun e he e' he' hne =>
        horth e (Finset.mem_insert_of_mem he) e' (Finset.mem_insert_of_mem he') hne
    have ih' := ih hidem_s horth_s
    have ha_idem : IsIdempotentElem a := hidem a (Finset.mem_insert_self a s)
    have hS_idem : IsIdempotentElem (∑ e ∈ s, e) := by
      rw [IsIdempotentElem, Finset.sum_mul_sum]
      apply Finset.sum_congr rfl
      intro e he
      rw [Finset.sum_eq_single e]
      · exact (hidem e (Finset.mem_insert_of_mem he)).eq
      · intro e' he' hne
        exact horth e (Finset.mem_insert_of_mem he) e' (Finset.mem_insert_of_mem he')
          (fun h => hne h.symm)
      · intro hnotin
        exact absurd he hnotin
    have haS : a * (∑ e ∈ s, e) = 0 := by
      rw [Finset.mul_sum]
      apply Finset.sum_eq_zero
      intro e he
      exact horth a (Finset.mem_insert_self a s) e (Finset.mem_insert_of_mem he)
        (fun h => ha (h ▸ he))
    have hSa : (∑ e ∈ s, e) * a = 0 := by
      rw [Finset.sum_mul]
      apply Finset.sum_eq_zero
      intro e he
      exact horth e (Finset.mem_insert_of_mem he) a (Finset.mem_insert_self a s)
        (fun h => ha (h.symm ▸ he))
    rw [psuC3b_rank_add_idem ha_idem hS_idem haS hSa, ih']

private theorem psuC3b_sum_rank {n : ℕ} {K : Type} [Field K]
    {B : GL (Fin n) K}
    (P : Finset (Matrix (Fin n) (Fin n) K)) (hP : PrimFamily (psuAlg B) P) :
    n = ∑ e ∈ P, Matrix.rank e := by
  classical
  rcases hP with ⟨hprim, horth, hsum⟩
  have hidem : ∀ e ∈ P, IsIdempotentElem e := fun e he => (hprim e).mp he |>.2.1
  have hrank := psuC3b_rank_sum_idem P hidem horth
  rw [hsum, Matrix.rank_one] at hrank
  simpa using hrank

private lemma psuC3b_orbit_subset_P {f n : ℕ} {K : Type} [Field K]
    {h : UnitaryFieldData 2 f K} {X : GL (Fin n) K}
    (P : Finset (Matrix (Fin n) (Fin n) K))
    (hstar : ∀ e ∈ P, psuDag h e ∈ P ∧ psuPsi h X e ∈ P)
    {e : Matrix (Fin n) (Fin n) K} (he : e ∈ P) :
    psuC3b_orbit h X e ⊆ P := by
  intro x hx
  simp only [psuC3b_orbit, Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact he
  · exact (hstar e he).1
  · exact (hstar e he).2
  · exact (hstar (psuPsi h X e) (hstar e he).2).1

private lemma psuC3b_alg_comm {n : ℕ} {K : Type} [Field K] (B : GL (Fin n) K) :
    ∀ a ∈ psuAlg B, ∀ b ∈ psuAlg B, a * b = b * a := by
  intro a ha b hb
  have hcommP : (Units.val '' ({B} : Set (GL (Fin n) K)) :
      Set (Matrix (Fin n) (Fin n) K)).Pairwise Commute := by
    rintro x ⟨s, hs, rfl⟩ y ⟨t, ht, rfl⟩ _
    rw [Set.mem_singleton_iff] at hs ht
    subst hs
    subst ht
    exact Commute.refl _
  letI : CommRing (psuAlg B) := Algebra.adjoinCommRingOfComm K hcommP
  exact congrArg Subtype.val (mul_comm (⟨a, ha⟩ : psuAlg B) (⟨b, hb⟩ : psuAlg B))

private lemma psuC3b_star_mem_of_primFamily {f n : ℕ} {K : Type} [Field K] [Finite K]
    [CharP K 2] {h : UnitaryFieldData 2 f K} {X B : GL (Fin n) K}
    (S : PSUGraphSetting h n X B) (P : Finset (Matrix (Fin n) (Fin n) K))
    (hP : PrimFamily (psuAlg B) P) :
    ∀ e ∈ P, psuDag h e ∈ P ∧ psuPsi h X e ∈ P := by
  intro e he
  refine ⟨?_, ?_⟩
  · exact primFamily_map_mem hP (psuDag h) (psuDag_add h) (psuDag_mul h)
      (fun a ha => (psuGraph_star_mem S a ha).1) (fun a _ => psuDag_dag h a)
      (psuC3b_alg_comm B) e he
  · exact primFamily_map_mem hP (psuPsi h X) (psuPsi_add h X) (psuPsi_mul h X)
      (fun a ha => (psuGraph_star_mem S a ha).2)
      (fun a _ => psuPsi_psi h X S.X_mem S.X_sq a) (psuC3b_alg_comm B) e he

private lemma psuC3b_orbit_card_eq_orbSize {f n : ℕ} {K : Type} [Field K] [Finite K]
    [CharP K 2] {h : UnitaryFieldData 2 f K} {X B : GL (Fin n) K}
    (S : PSUGraphSetting h n X B)
    (e : Matrix (Fin n) (Fin n) K) :
    (psuC3b_orbit h X e).card = psuOrbSize (psuKind h X B e) := by
  classical
  haveI : Fintype K := Fintype.ofFinite K
  have hEq : Nat.card {e' : Matrix (Fin n) (Fin n) K // e' = e ∨ e' = psuDag h e ∨
      e' = psuPsi h X e ∨ e' = psuDag h (psuPsi h X e)} =
      (psuC3b_orbit h X e).card := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    congr 1
    ext x
    simp [psuC3b_orbit]
  rw [← hEq]
  exact psuC3b_orbit_size S e

private lemma psuC3b_sum_over_orbits {f n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    {h : UnitaryFieldData 2 f K} {X B : GL (Fin n) K} (S : PSUGraphSetting h n X B)
    (P : Finset (Matrix (Fin n) (Fin n) K)) (hP : PrimFamily (psuAlg B) P)
    (R : Finset (Matrix (Fin n) (Fin n) K)) (hR : R ⊆ P)
    (hrep : ∀ e ∈ P, ∃! r, r ∈ R ∧
      (r = e ∨ r = psuDag h e ∨ r = psuPsi h X e ∨ r = psuDag h (psuPsi h X e)))
    (w : Matrix (Fin n) (Fin n) K → ℕ)
    (hw : ∀ r ∈ R, ∀ e ∈ psuC3b_orbit h X r, w e = w r) :
    ∑ e ∈ P, w e = ∑ r ∈ R, psuOrbSize (psuKind h X B r) * w r := by
  classical
  have hstar : ∀ e ∈ P, psuDag h e ∈ P ∧ psuPsi h X e ∈ P :=
    psuC3b_star_mem_of_primFamily S P hP
  have horb_sub : ∀ r ∈ R, psuC3b_orbit h X r ⊆ P := fun r hr =>
    psuC3b_orbit_subset_P P hstar (hR hr)
  have hUnion : P = R.biUnion (fun r => psuC3b_orbit h X r) := by
    apply Finset.Subset.antisymm
    · intro e he
      obtain ⟨r, ⟨hrR, hrdisj⟩, -⟩ := hrep e he
      have hre : r ∈ psuC3b_orbit h X e := by
        simpa [psuC3b_orbit] using hrdisj
      exact Finset.mem_biUnion.mpr ⟨r, hrR, psuC3b_orbit_symm S hre⟩
    · intro e he
      obtain ⟨r, hrR, her⟩ := Finset.mem_biUnion.mp he
      exact horb_sub r hrR her
  have hDisj : ∀ r1 ∈ R, ∀ r2 ∈ R, r1 ≠ r2 →
      Disjoint (psuC3b_orbit h X r1) (psuC3b_orbit h X r2) := by
    intro r1 hr1 r2 hr2 hne
    rw [Finset.disjoint_left]
    intro x hx1 hx2
    have hxr1 : r2 ∈ psuC3b_orbit h X r1 := by
      have h1 : psuC3b_orbit h X x = psuC3b_orbit h X r1 := psuC3b_orbit_eq S hx1
      have h2 : psuC3b_orbit h X x = psuC3b_orbit h X r2 := psuC3b_orbit_eq S hx2
      rw [← h1, h2]
      exact psuC3b_orbit_self h X r2
    have hdisj2 : r2 = r1 ∨ r2 = psuDag h r1 ∨ r2 = psuPsi h X r1 ∨
        r2 = psuDag h (psuPsi h X r1) := by
      simpa [psuC3b_orbit] using hxr1
    obtain ⟨r', ⟨-, hr'disj⟩, huniq⟩ := hrep r1 (hR hr1)
    have hcand : r2 ∈ R ∧ (r2 = r1 ∨ r2 = psuDag h r1 ∨ r2 = psuPsi h X r1 ∨
        r2 = psuDag h (psuPsi h X r1)) := ⟨hr2, hdisj2⟩
    have hcand1 : r1 ∈ R ∧ (r1 = r1 ∨ r1 = psuDag h r1 ∨ r1 = psuPsi h X r1 ∨
        r1 = psuDag h (psuPsi h X r1)) := ⟨hr1, Or.inl rfl⟩
    have e1 : r2 = r' := huniq r2 hcand
    have e2 : r1 = r' := huniq r1 hcand1
    exact hne (e1.trans e2.symm).symm
  have hstep : (∑ e ∈ R.biUnion (fun r => psuC3b_orbit h X r), w e) =
      ∑ r ∈ R, ∑ e ∈ psuC3b_orbit h X r, w e := by
    rw [Finset.sum_biUnion hDisj]
  calc ∑ e ∈ P, w e
      = ∑ e ∈ R.biUnion (fun r => psuC3b_orbit h X r), w e := by rw [hUnion]
    _ = ∑ r ∈ R, ∑ e ∈ psuC3b_orbit h X r, w e := hstep
    _ = ∑ r ∈ R, ∑ e ∈ psuC3b_orbit h X r, w r := by
        apply Finset.sum_congr rfl
        intro r hr
        apply Finset.sum_congr rfl
        intro e he
        exact hw r hr e he
    _ = ∑ r ∈ R, psuOrbSize (psuKind h X B r) * w r := by
        apply Finset.sum_congr rfl
        intro r hr
        rw [Finset.sum_const, smul_eq_mul,
          psuC3b_orbit_card_eq_orbSize S r]

private theorem psuC3b_dim_count {f n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    {h : UnitaryFieldData 2 f K} {X B : GL (Fin n) K} (S : PSUGraphSetting h n X B)
    (P : Finset (Matrix (Fin n) (Fin n) K)) (hP : PrimFamily (psuAlg B) P)
    (R : Finset (Matrix (Fin n) (Fin n) K)) (hR : R ⊆ P)
    (hrep : ∀ e ∈ P, ∃! r, r ∈ R ∧
      (r = e ∨ r = psuDag h e ∨ r = psuPsi h X e ∨ r = psuDag h (psuPsi h X e))) :
    n = ∑ r ∈ R, psuOrbSize (psuKind h X B r) * Matrix.rank r := by
  classical
  have hstar := psuC3b_star_mem_of_primFamily S P hP
  nth_rewrite 1 [psuC3b_sum_rank P hP]
  refine psuC3b_sum_over_orbits S P hP R hR hrep (fun e => Matrix.rank e) ?_
  intro r hr e he
  have heP : r ∈ P := hR hr
  have hinv := psuGraph_orbit_invariant S P hP r heP
  simp only [psuC3b_orbit, Finset.mem_insert, Finset.mem_singleton] at he
  rcases he with rfl | rfl | rfl | rfl
  · rfl
  · exact hinv.1.2.1
  · exact hinv.2.2.1
  · have h2 := psuGraph_orbit_invariant S P hP (psuPsi h X r) ((hstar r heP).2)
    rw [h2.1.2.1, hinv.2.2.1]

private lemma psuC3b_algHom_ext_B {f n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    {h : UnitaryFieldData 2 f K} {X B : GL (Fin n) K} (S : PSUGraphSetting h n X B)
    (κ κ' : psuAlg B →ₐ[K] K)
    (hB : κ ⟨(B : Matrix (Fin n) (Fin n) K), Algebra.subset_adjoin ⟨B, rfl, rfl⟩⟩ =
      κ' ⟨(B : Matrix (Fin n) (Fin n) K), Algebra.subset_adjoin ⟨B, rfl, rfl⟩⟩) :
    κ = κ' := by
  apply AlgHom.ext
  intro a
  have ha : (a : Matrix (Fin n) (Fin n) K) ∈
      Algebra.adjoin K (Units.val '' ({B} : Set (GL (Fin n) K))) := a.2
  refine Algebra.adjoin_induction (p := fun x hx => κ ⟨x, hx⟩ = κ' ⟨x, hx⟩) ?_ ?_ ?_ ?_ ha
  · rintro x ⟨s, hs, rfl⟩
    rw [Set.mem_singleton_iff] at hs
    subst hs
    exact hB
  · intro r
    simp
  · intro x y hx hy ihx ihy
    change κ (⟨x, hx⟩ + ⟨y, hy⟩) = κ' (⟨x, hx⟩ + ⟨y, hy⟩)
    rw [map_add, map_add, ihx, ihy]
  · intro x y hx hy ihx ihy
    change κ (⟨x, hx⟩ * ⟨y, hy⟩) = κ' (⟨x, hx⟩ * ⟨y, hy⟩)
    rw [map_mul, map_mul, ihx, ihy]

private lemma psuC3b_degree_one_exists_char {f n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    {h : UnitaryFieldData 2 f K} {X B : GL (Fin n) K} (S : PSUGraphSetting h n X B)
    (P : Finset (Matrix (Fin n) (Fin n) K)) (hP : PrimFamily (psuAlg B) P)
    (e : Matrix (Fin n) (Fin n) K) (he : e ∈ P) (hd : blockDegree (psuAlg B) e = 1) :
    ∃ (κ : psuAlg B →ₐ[K] K),
      κ ⟨(B : Matrix (Fin n) (Fin n) K), Algebra.subset_adjoin ⟨B, rfl, rfl⟩⟩ ≠ 0 ∧
      (∀ a : psuAlg B, κ a = 0 ↔ (a : Matrix (Fin n) (Fin n) K) * e = 0) := by
  classical
  have hePrim : IsPrimIdemIn (psuAlg B) e := (hP.1 e).mp he
  obtain ⟨F, hFld, hAlg, hFin, hChar, π, hM, hT, ψemb, hπ, hker, hdim, hcard, hact,
    hrank, hpos, hinj, hψact, hψone, hψcomm, hψB⟩ :=
    exists_blockEmbed (A := psuAlg B) S.odd rfl hePrim
  letI : Field F := hFld
  letI : Algebra K F := hAlg
  letI : Finite F := hFin
  letI : CharP F 2 := hChar
  have hfin1 : Module.finrank K F = 1 := by rw [hdim, hd]
  haveI : FiniteDimensional K F := FiniteDimensional.of_finrank_pos (by rw [hfin1]; norm_num)
  have hsurj : Function.Surjective (algebraMap K F) := by
    have htop : LinearMap.range (Algebra.linearMap K F) = ⊤ := by
      apply Submodule.eq_top_of_finrank_eq
      have h := LinearMap.finrank_range_add_finrank_ker (Algebra.linearMap K F)
      have hinj : Function.Injective (Algebra.linearMap K F) := (algebraMap K F).injective
      rw [LinearMap.ker_eq_bot_of_injective hinj, finrank_bot, add_zero,
        Module.finrank_self] at h
      rw [h, hfin1]
    intro y
    obtain ⟨x, hx⟩ := LinearMap.range_eq_top.mp htop y
    exact ⟨x, by simpa using hx⟩
  let eK : F ≃ₐ[K] K :=
    (AlgEquiv.ofBijective (Algebra.ofId K F)
      ⟨(algebraMap K F).injective, hsurj⟩).symm
  let κ : psuAlg B →ₐ[K] K := eK.toAlgHom.comp π
  have hκB : κ ⟨(B : Matrix (Fin n) (Fin n) K), Algebra.subset_adjoin ⟨B, rfl, rfl⟩⟩ ≠ 0 := by
    intro hzero
    have hpiB : π ⟨(B : Matrix (Fin n) (Fin n) K),
        Algebra.subset_adjoin ⟨B, rfl, rfl⟩⟩ = 0 := by
      apply eK.injective
      simpa [κ] using hzero
    haveI : Finite (LinearMap.range e.mulVecLin) :=
      Finite.of_injective (Subtype.val) Subtype.val_injective
    haveI : Module.Finite F (LinearMap.range e.mulVecLin) := Module.Finite.of_finite
    haveI : Module.IsTorsionFree F (LinearMap.range e.mulVecLin) := inferInstance
    obtain ⟨w, hwne⟩ := (Module.finrank_pos_iff_exists_ne_zero).mp hpos
    have hBw : (B : Matrix (Fin n) (Fin n) K) *ᵥ (w : Fin n → K) = 0 := by
      have h := hact ⟨(B : Matrix (Fin n) (Fin n) K),
        Algebra.subset_adjoin ⟨B, rfl, rfl⟩⟩ w
      rw [hpiB, zero_smul, Submodule.coe_zero] at h
      exact h.symm
    have hw0 : (w : Fin n → K) = 0 := by
      have h1 : ((B⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ
          ((B : Matrix (Fin n) (Fin n) K) *ᵥ (w : Fin n → K)) = 0 := by
        rw [hBw, Matrix.mulVec_zero]
      rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one,
        Matrix.one_mulVec] at h1
      exact h1
    exact hwne (Subtype.ext hw0)
  refine ⟨κ, hκB, ?_⟩
  intro a
  have hκa : κ a = eK (π a) := rfl
  rw [hκa]
  constructor
  · intro h
    exact (hker a).mp (eK.injective (by simpa using h))
  · intro h
    rw [(hker a).mpr h]
    exact map_zero eK

private theorem psuC3b_degree_one_idem_count {f n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    {h : UnitaryFieldData 2 f K} {X B : GL (Fin n) K} (S : PSUGraphSetting h n X B)
    (P : Finset (Matrix (Fin n) (Fin n) K)) (hP : PrimFamily (psuAlg B) P) :
    (P.filter (fun e => blockDegree (psuAlg B) e = 1)).card ≤ Nat.card Kˣ := by
  classical
  haveI : Fintype K := Fintype.ofFinite K
  let E := {e : Matrix (Fin n) (Fin n) K // e ∈ P ∧ blockDegree (psuAlg B) e = 1}
  have hcard : (P.filter (fun e => blockDegree (psuAlg B) e = 1)).card = Nat.card E := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    congr 1
    ext x
    simp [E, and_assoc, and_comm, and_left_comm]
  rw [hcard]
  let lam : E → Kˣ := fun e =>
    let κ := Classical.choose (psuC3b_degree_one_exists_char S P hP e.1 e.2.1 e.2.2)
    Units.mk0 (κ ⟨(B : Matrix (Fin n) (Fin n) K), Algebra.subset_adjoin ⟨B, rfl, rfl⟩⟩)
      ((Classical.choose_spec (psuC3b_degree_one_exists_char S P hP e.1 e.2.1 e.2.2)).1)
  have hlam_inj : Function.Injective lam := by
    intro e e' h
    let κe := Classical.choose (psuC3b_degree_one_exists_char S P hP e.1 e.2.1 e.2.2)
    let κe' := Classical.choose (psuC3b_degree_one_exists_char S P hP e'.1 e'.2.1 e'.2.2)
    have hspec_e :=
      Classical.choose_spec (psuC3b_degree_one_exists_char S P hP e.1 e.2.1 e.2.2)
    have hspec_e' :=
      Classical.choose_spec (psuC3b_degree_one_exists_char S P hP e'.1 e'.2.1 e'.2.2)
    have hB : κe ⟨(B : Matrix (Fin n) (Fin n) K), Algebra.subset_adjoin ⟨B, rfl, rfl⟩⟩ =
        κe' ⟨(B : Matrix (Fin n) (Fin n) K), Algebra.subset_adjoin ⟨B, rfl, rfl⟩⟩ := by
      have := congrArg (fun u : Kˣ => (u : K)) h
      simpa [lam, κe, κe'] using this
    have hκ : κe = κe' := psuC3b_algHom_ext_B S κe κe' hB
    have hker : ∀ a : psuAlg B, (a : Matrix (Fin n) (Fin n) K) * e.1 = 0 ↔
        (a : Matrix (Fin n) (Fin n) K) * e'.1 = 0 := by
      intro a
      have h1 : κe a = 0 ↔ (a : Matrix (Fin n) (Fin n) K) * e.1 = 0 := hspec_e.2 a
      have h2 : κe' a = 0 ↔ (a : Matrix (Fin n) (Fin n) K) * e'.1 = 0 := hspec_e'.2 a
      rw [← h1, ← h2, hκ]
    have hee : e.1 * e.1 = e.1 := ((hP.1 e.1).mp e.2.1).2.1.eq
    have heA : e.1 ∈ psuAlg B := ((hP.1 e.1).mp e.2.1).1
    have hsub : (1 - e.1) ∈ psuAlg B := Subalgebra.sub_mem _ (Subalgebra.one_mem _) heA
    have hzero : ((1 - e.1) * e.1) = 0 := by
      rw [Matrix.sub_mul, Matrix.one_mul, hee, sub_self]
    have hzero' : ((1 - e.1) * e'.1) = 0 := (hker ⟨1 - e.1, hsub⟩).mp hzero
    have hee' : e'.1 = e.1 * e'.1 := by
      rw [Matrix.sub_mul, Matrix.one_mul] at hzero'
      exact sub_eq_zero.mp hzero'
    by_cases hne : e.1 = e'.1
    · exact Subtype.ext hne
    · exfalso
      have horth := hP.2.1 e.1 e.2.1 e'.1 e'.2.1 hne
      rw [horth] at hee'
      have hne0 := ((hP.1 e'.1).mp e'.2.1).2.2.1
      exact hne0 hee'
  exact Nat.card_le_card_of_injective lam hlam_inj

private theorem psuC3b_card_units_K {f : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData 2 f K) : Nat.card Kˣ = (2 ^ f) ^ 2 - 1 := by
  rw [Nat.card_units, h.card_eq_sq]

private theorem psuC3b_degree_one_orbit_sum {f n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    {h : UnitaryFieldData 2 f K} {X B : GL (Fin n) K} (S : PSUGraphSetting h n X B)
    (P : Finset (Matrix (Fin n) (Fin n) K)) (hP : PrimFamily (psuAlg B) P)
    (R : Finset (Matrix (Fin n) (Fin n) K)) (hR : R ⊆ P)
    (hrep : ∀ e ∈ P, ∃! r, r ∈ R ∧
      (r = e ∨ r = psuDag h e ∨ r = psuPsi h X e ∨ r = psuDag h (psuPsi h X e))) :
    (∑ r ∈ R.filter (fun r => blockDegree (psuAlg B) r = 1), psuOrbSize (psuKind h X B r)) =
      (P.filter (fun e => blockDegree (psuAlg B) e = 1)).card := by
  classical
  have hmain := psuC3b_sum_over_orbits S P hP R hR hrep
    (fun e => if blockDegree (psuAlg B) e = 1 then 1 else 0) ?_
  · rw [Finset.card_filter, hmain, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro r hr
    by_cases hb : blockDegree (psuAlg B) r = 1
    · simp [hb]
    · simp [hb]
  · intro r hr e he
    have heP : r ∈ P := hR hr
    have hstar := psuC3b_star_mem_of_primFamily S P hP
    have hinv := psuGraph_orbit_invariant S P hP r heP
    simp only [psuC3b_orbit, Finset.mem_insert, Finset.mem_singleton] at he
    rcases he with rfl | rfl | rfl | rfl
    · rfl
    · rw [hinv.1.2.2]
    · rw [hinv.2.2.2]
    · have hinv2 := psuGraph_orbit_invariant S P hP (psuPsi h X r) ((hstar r heP).2)
      rw [hinv2.1.2.2, hinv.2.2.2]

private theorem psuC3b_degree_one_count {f n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    {h : UnitaryFieldData 2 f K} {X B : GL (Fin n) K} (S : PSUGraphSetting h n X B)
    (P : Finset (Matrix (Fin n) (Fin n) K)) (hP : PrimFamily (psuAlg B) P)
    (R : Finset (Matrix (Fin n) (Fin n) K)) (hR : R ⊆ P)
    (hrep : ∀ e ∈ P, ∃! r, r ∈ R ∧
      (r = e ∨ r = psuDag h e ∨ r = psuPsi h X e ∨ r = psuDag h (psuPsi h X e))) :
    (∑ r ∈ R.filter (fun r => blockDegree (psuAlg B) r = 1), psuOrbSize (psuKind h X B r)) ≤
      (2 ^ f) ^ 2 - 1 := by
  rw [psuC3b_degree_one_orbit_sum S P hP R hR hrep]
  have hle := psuC3b_degree_one_idem_count S P hP
  rwa [psuC3b_card_units_K h] at hle

private lemma psuC3b_psi_zero {f n : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K)
    (X : GL (Fin n) K) : psuPsi h X (0 : Matrix (Fin n) (Fin n) K) = 0 := by
  simp [psuPsi, psuTheta, psuDag, formAdj]

private lemma psuC3b_kind_three {f n : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K)
    (X B : GL (Fin n) K) (e : Matrix (Fin n) (Fin n) K)
    (hk : psuKind h X B e = 3) :
    psuDag h e ≠ e ∧ psuPsi h X e = e ∧ ¬ psuPsiTrivial h X B e := by
  unfold psuKind at hk
  by_cases hd : psuDag h e = e
  · rw [if_pos hd] at hk
    by_cases hp : psuPsi h X e = e
    · rw [if_pos hp] at hk
      omega
    · rw [if_neg hp] at hk
      omega
  · rw [if_neg hd] at hk
    by_cases hp : psuPsi h X e = e
    · rw [if_pos hp] at hk
      by_cases ht : psuPsiTrivial h X B e
      · rw [if_pos ht] at hk
        omega
      · rw [if_neg ht] at hk
        exact ⟨hd, hp, ht⟩
    · rw [if_neg hp] at hk
      by_cases h4 : psuPsi h X e = psuDag h e
      · rw [if_pos h4] at hk
        omega
      · rw [if_neg h4] at hk
        omega

private theorem psuC3b_degree_data {f n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    {h : UnitaryFieldData 2 f K} {X B : GL (Fin n) K} (S : PSUGraphSetting h n X B)
    (P : Finset (Matrix (Fin n) (Fin n) K)) (hP : PrimFamily (psuAlg B) P)
    (R : Finset (Matrix (Fin n) (Fin n) K)) (hR : R ⊆ P)
    :
    ∀ r ∈ R, 1 ≤ blockDegree (psuAlg B) r ∧
      (psuKind h X B r = 3 → Even (blockDegree (psuAlg B) r)) := by
  intro r hr
  have he : IsPrimIdemIn (psuAlg B) r := (hP.1 r).mp (hR hr)
  obtain ⟨F, hFld, hAlg, hFin, hChar, π, hM, hT, ψemb, hπ, hker, hdim, hcard, hact,
    hrank, hpos, hinj, hψact, hψone, hψcomm, hψB⟩ :=
    exists_blockEmbed S.odd rfl he
  letI : Field F := hFld
  letI : Algebra K F := hAlg
  letI : Finite F := hFin
  letI : CharP F 2 := hChar
  have hdpos : 0 < blockDegree (psuAlg B) r := by
    by_contra hcon
    have h0 : blockDegree (psuAlg B) r = 0 := by omega
    haveI : Fintype F := Fintype.ofFinite F
    rw [h0, pow_zero, Nat.card_eq_fintype_card] at hcard
    have h2 := Fintype.one_lt_card (α := F)
    omega
  refine ⟨by omega, ?_⟩
  intro hk3
  obtain ⟨hdne, hpse, hntriv⟩ := psuC3b_kind_three h X B r hk3
  let A : Subalgebra K (Matrix (Fin n) (Fin n) K) := psuAlg B
  have hcommP : (Units.val '' ({B} : Set (GL (Fin n) K)) :
      Set (Matrix (Fin n) (Fin n) K)).Pairwise Commute := by
    rintro a ⟨s, hs, rfl⟩ b ⟨s', hs', rfl⟩ _
    rw [Set.mem_singleton_iff] at hs hs'
    subst hs
    subst hs'
    exact Commute.refl _
  letI : CommRing A := Algebra.adjoinCommRingOfComm K hcommP
  let ψA : A →ₐ[K] A :=
    { toFun := fun a => ⟨psuPsi h X (a : Matrix (Fin n) (Fin n) K),
        (psuGraph_star_mem S a.1 a.2).2⟩
      map_one' := Subtype.ext (psuPsi_one h X)
      map_mul' := by
        intro a b
        apply Subtype.ext
        change psuPsi h X ((a : Matrix (Fin n) (Fin n) K) *
            (b : Matrix (Fin n) (Fin n) K)) =
          psuPsi h X (a : Matrix (Fin n) (Fin n) K) *
            psuPsi h X (b : Matrix (Fin n) (Fin n) K)
        rw [psuPsi_mul]
        exact congrArg Subtype.val (mul_comm
          (⟨psuPsi h X (b : Matrix (Fin n) (Fin n) K),
            (psuGraph_star_mem S b.1 b.2).2⟩ : A)
          (⟨psuPsi h X (a : Matrix (Fin n) (Fin n) K),
            (psuGraph_star_mem S a.1 a.2).2⟩ : A))
      map_zero' := Subtype.ext (psuC3b_psi_zero h X)
      map_add' := by
        intro a b
        apply Subtype.ext
        exact psuPsi_add h X (a : Matrix (Fin n) (Fin n) K)
          (b : Matrix (Fin n) (Fin n) K)
      commutes' := by
        intro c
        apply Subtype.ext
        change psuPsi h X (((algebraMap K A) c : A) : Matrix (Fin n) (Fin n) K) =
          (((algebraMap K A) c : A) : Matrix (Fin n) (Fin n) K)
        rw [Algebra.algebraMap_eq_smul_one]
        simp [psuPsi_smul, psuPsi_one] }
  have hker_psi : RingHom.ker π ≤ RingHom.ker (π.comp ψA) := by
    intro a ha
    rw [RingHom.mem_ker] at ha ⊢
    rw [AlgHom.comp_apply]
    rw [hker (ψA a), hker a] at *
    have hrA : r ∈ A := he.1
    have h1 : psuPsi h X ((a : Matrix (Fin n) (Fin n) K) * r) = 0 := by
      rw [ha, psuC3b_psi_zero h X]
    rw [psuPsi_mul, hpse] at h1
    have hcomm : (r : Matrix (Fin n) (Fin n) K) * psuPsi h X (a : Matrix (Fin n) (Fin n) K) =
        psuPsi h X (a : Matrix (Fin n) (Fin n) K) * r :=
      congrArg Subtype.val (mul_comm (⟨r, hrA⟩ : A) (ψA a))
    rw [hcomm] at h1
    change psuPsi h X (a : Matrix (Fin n) (Fin n) K) * r = 0
    exact h1
  let τ0 : F →ₐ[K] F := AlgHom.liftOfSurjective π hπ (π.comp ψA) hker_psi
  have hτ0_apply : ∀ a : A, τ0 (π a) = π (ψA a) := fun a =>
    AlgHom.liftOfSurjective_apply π hπ (π.comp ψA) hker_psi a
  have hψA2 : ∀ a : A, ψA (ψA a) = a := by
    intro a
    apply Subtype.ext
    change psuPsi h X (psuPsi h X (a : Matrix (Fin n) (Fin n) K)) =
      (a : Matrix (Fin n) (Fin n) K)
    exact psuPsi_psi h X S.X_mem S.X_sq _
  have hτ02 : τ0.comp τ0 = AlgHom.id K F := by
    apply AlgHom.ext
    intro x
    obtain ⟨a, rfl⟩ := hπ x
    rw [AlgHom.comp_apply, hτ0_apply, hτ0_apply, hψA2]
    rfl
  have hτ01 : τ0 ≠ AlgHom.id K F := by
    intro hid
    apply hntriv
    intro a ha
    let aA : A := ⟨a, ha⟩
    have h2 : τ0 (π aA) = π aA := by rw [hid]; rfl
    rw [hτ0_apply] at h2
    have h3 : π (ψA aA - aA) = 0 := by
      rw [map_sub, h2, sub_self]
    rw [hker] at h3
    change (((ψA aA - aA : A) : Matrix (Fin n) (Fin n) K) * r) = 0 at h3
    have h4 : (ψA aA : Matrix (Fin n) (Fin n) K) * r = a * r := by
      have h5 : ((ψA aA : Matrix (Fin n) (Fin n) K) -
          (aA : Matrix (Fin n) (Fin n) K)) * r = 0 := by simpa using h3
      rw [Matrix.sub_mul, sub_eq_zero] at h5
      exact h5
    have hrA : r ∈ A := he.1
    calc psuPsi h X (a * r) = psuPsi h X r * psuPsi h X a := psuPsi_mul h X a r
      _ = r * psuPsi h X a := by rw [hpse]
      _ = psuPsi h X a * r :=
        congrArg Subtype.val (mul_comm (⟨r, hrA⟩ : A) (ψA aA))
      _ = a * r := h4
  let τ : F ≃ₐ[K] F := AlgEquiv.ofAlgHom τ0 τ0 hτ02 hτ02
  have hτ2 : τ * τ = 1 := by
    ext x
    change τ0 (τ0 x) = x
    exact AlgHom.congr_fun hτ02 x
  have hτ1 : τ ≠ 1 := by
    intro h
    apply hτ01
    apply AlgHom.ext
    intro x
    have hx := congrArg (fun e : F ≃ₐ[K] F => e x) h
    change τ0 x = x
    exact hx
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have horder : orderOf τ = 2 :=
    orderOf_eq_prime (by simpa [pow_two] using hτ2) hτ1
  have hdvd1 : orderOf τ ∣ Nat.card (F ≃ₐ[K] F) := orderOf_dvd_natCard τ
  have hdvd2 : Nat.card (F ≃ₐ[K] F) ∣ Module.finrank K F :=
    TauCeti.natCard_algEquiv_dvd_finrank K F
  have h2dvd : 2 ∣ Module.finrank K F := by
    rw [← horder]
    exact dvd_trans hdvd1 hdvd2
  rw [← hdim]
  exact even_iff_two_dvd.mpr h2dvd

private def psuC3b_F1 {f n : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K)
    (B : GL (Fin n) K) : Type :=
  {t : psuAlg B //
    psuDag h (t : Matrix (Fin n) (Fin n) K) * (t : Matrix (Fin n) (Fin n) K) = 1}

private def psuC3b_U {f n : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K)
    (X B : GL (Fin n) K) : Type :=
  {t : psuC3b_F1 h B //
    psuPsi h X ((t.1 : psuAlg B) : Matrix (Fin n) (Fin n) K) *
      ((t.1 : psuAlg B) : Matrix (Fin n) (Fin n) K) = 1}

private def psuC3b_Nrange {f n : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K)
    (X B : GL (Fin n) K) : Type :=
  {m : Matrix (Fin n) (Fin n) K //
    ∃ t : psuC3b_F1 h B,
      m = psuPsi h X ((t.1 : psuAlg B) : Matrix (Fin n) (Fin n) K) *
        ((t.1 : psuAlg B) : Matrix (Fin n) (Fin n) K)}

private def psuC3b_F1O (q d k : ℕ) : ℕ :=
  if k = 0 then q ^ d + 1
  else if k = 1 then (q ^ d + 1) ^ 2
  else if k = 5 then (q ^ (2 * d) - 1) ^ 2
  else q ^ (2 * d) - 1

private def psuC3b_UO (q d k : ℕ) : ℕ :=
  if k = 0 ∨ k = 2 then 1
  else if k = 1 ∨ k = 3 then q ^ d + 1
  else if k = 4 then q ^ d - 1
  else q ^ (2 * d) - 1

private lemma psuC3b_kind_le {f n : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K)
    (X B : GL (Fin n) K) (e : Matrix (Fin n) (Fin n) K) : psuKind h X B e ≤ 5 := by
  unfold psuKind
  split_ifs <;> omega

private lemma psuC3bg4_self_dag_eq_one {f n : ℕ} {K : Type} [Field K]
    {h : UnitaryFieldData 2 f K} {B : GL (Fin n) K} (t : psuAlg B)
    (ht : psuDag h (t : Matrix (Fin n) (Fin n) K) * (t : Matrix (Fin n) (Fin n) K) = 1) :
    (t : Matrix (Fin n) (Fin n) K) * psuDag h (t : Matrix (Fin n) (Fin n) K) = 1 :=
  (Matrix.mul_eq_one_comm_of_card_eq (R := K) (m := Fin n) (n := Fin n)
    (A := psuDag h (t : Matrix (Fin n) (Fin n) K)) (B := (t : Matrix (Fin n) (Fin n) K))
    (by rfl)).mp ht

private noncomputable def psuC3bg4_dagA {f n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    {h : UnitaryFieldData 2 f K} {X B : GL (Fin n) K} (S : PSUGraphSetting h n X B)
    (t : psuAlg B) : psuAlg B :=
  ⟨psuDag h (t : Matrix (Fin n) (Fin n) K), (psuGraph_star_mem S t.1 t.2).1⟩

private noncomputable def psuC3bg4_psiA {f n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    {h : UnitaryFieldData 2 f K} {X B : GL (Fin n) K} (S : PSUGraphSetting h n X B)
    (t : psuAlg B) : psuAlg B :=
  ⟨psuPsi h X (t : Matrix (Fin n) (Fin n) K), (psuGraph_star_mem S t.1 t.2).2⟩

private lemma psuC3bg4_psiA_one {f n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    {h : UnitaryFieldData 2 f K} {X B : GL (Fin n) K} (S : PSUGraphSetting h n X B) :
    psuC3bg4_psiA S (1 : psuAlg B) = 1 := by
  apply Subtype.ext
  change psuPsi h X ((1 : psuAlg B) : Matrix (Fin n) (Fin n) K) =
    (1 : Matrix (Fin n) (Fin n) K)
  rw [Subalgebra.coe_one, psuPsi_one]

private lemma psuC3bg4_psiA_mul {f n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    {h : UnitaryFieldData 2 f K} {X B : GL (Fin n) K} (S : PSUGraphSetting h n X B)
    (s t : psuAlg B) :
    psuC3bg4_psiA S (s * t) = psuC3bg4_psiA S t * psuC3bg4_psiA S s := by
  apply Subtype.ext
  change psuPsi h X ((s * t : psuAlg B) : Matrix (Fin n) (Fin n) K) =
    psuPsi h X (t : Matrix (Fin n) (Fin n) K) *
      psuPsi h X (s : Matrix (Fin n) (Fin n) K)
  rw [Subalgebra.coe_mul, psuPsi_mul]

private lemma psuC3bg4_pow_two_mul (q d : ℕ) : q ^ (2 * d) = (q ^ d) ^ 2 := by
  rw [Nat.mul_comm 2 d, pow_mul]

private lemma psuC3bg4_sq_sub_one (a : ℕ) : a ^ 2 - 1 = (a + 1) * (a - 1) := by
  have h := Nat.sq_sub_sq a 1
  simpa using h

private lemma psuC3b_normImage_eq_Nrange {f n : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData 2 f K) (X B : GL (Fin n) K) :
    Nat.card (psuNormImage h X B) = Nat.card (psuC3b_Nrange h X B) := by
  classical
  refine Nat.card_congr (Equiv.subtypeEquivRight (fun m => ?_))
  constructor
  · rintro ⟨t, ht, rfl⟩
    exact ⟨⟨⟨t, ht.1⟩, ht.2⟩, rfl⟩
  · rintro ⟨t, rfl⟩
    exact ⟨(t.1 : Matrix (Fin n) (Fin n) K), ⟨t.1.2, t.2⟩, rfl⟩

private lemma psuC3b_first_iso {f n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    {h : UnitaryFieldData 2 f K} {X B : GL (Fin n) K} (S : PSUGraphSetting h n X B)
    (P : Finset (Matrix (Fin n) (Fin n) K)) (hP : PrimFamily (psuAlg B) P) :
    Nat.card (psuC3b_Nrange h X B) * Nat.card (psuC3b_U h X B) =
      Nat.card (psuC3b_F1 h B) := by
  classical
  have hcommP : (Units.val '' ({B} : Set (GL (Fin n) K)) :
      Set (Matrix (Fin n) (Fin n) K)).Pairwise Commute := by
    rintro a ⟨s, hs, rfl⟩ b ⟨t, ht, rfl⟩ _
    rw [Set.mem_singleton_iff] at hs ht
    subst hs
    subst ht
    exact Commute.refl _
  letI : CommRing (psuAlg B) := Algebra.adjoinCommRingOfComm K hcommP
  letI mulG : Mul (psuC3b_F1 h B) :=
    ⟨fun t u => ⟨t.1 * u.1, by
      show psuDag h (((t.1 * u.1 : psuAlg B) : Matrix (Fin n) (Fin n) K)) *
        ((t.1 * u.1 : psuAlg B) : Matrix (Fin n) (Fin n) K) = 1
      change psuDag h ((t.1 : Matrix (Fin n) (Fin n) K) *
          (u.1 : Matrix (Fin n) (Fin n) K)) *
          ((t.1 : Matrix (Fin n) (Fin n) K) *
            (u.1 : Matrix (Fin n) (Fin n) K)) = 1
      rw [psuDag_mul]
      rw [Matrix.mul_assoc,
        ← Matrix.mul_assoc (psuDag h (t.1 : Matrix (Fin n) (Fin n) K))
          (t.1 : Matrix (Fin n) (Fin n) K) (u.1 : Matrix (Fin n) (Fin n) K),
        t.2, Matrix.one_mul, u.2]⟩⟩
  letI oneG : One (psuC3b_F1 h B) :=
    ⟨⟨(1 : psuAlg B), by
      show psuDag h (((1 : psuAlg B) : Matrix (Fin n) (Fin n) K)) *
        ((1 : psuAlg B) : Matrix (Fin n) (Fin n) K) = 1
      rw [Subalgebra.coe_one, psuDag_one, Matrix.one_mul]⟩⟩
  letI invG : Inv (psuC3b_F1 h B) :=
    ⟨fun t => ⟨psuC3bg4_dagA S t.1, by
      show psuDag h (((psuC3bg4_dagA S t.1 : psuAlg B) : Matrix (Fin n) (Fin n) K)) *
        ((psuC3bg4_dagA S t.1 : psuAlg B) : Matrix (Fin n) (Fin n) K) = 1
      change psuDag h (psuDag h (t.1 : Matrix (Fin n) (Fin n) K)) *
        psuDag h (t.1 : Matrix (Fin n) (Fin n) K) = 1
      rw [psuDag_dag]
      exact psuC3bg4_self_dag_eq_one t.1 t.2⟩⟩
  letI grpG : Group (psuC3b_F1 h B) :=
    Group.ofLeftAxioms
      (fun a b c => Subtype.ext (by
        change (a.1 * b.1) * c.1 = a.1 * (b.1 * c.1)
        rw [mul_assoc]))
      (fun a => Subtype.ext (by
        change (1 : psuAlg B) * a.1 = a.1
        rw [one_mul]))
      (fun a => Subtype.ext (by
        change (psuC3bg4_dagA S a.1) * a.1 = 1
        exact Subtype.ext a.2))
  let N : psuC3b_F1 h B →* (psuAlg B)ˣ :=
    { toFun := fun t => Units.mk (psuC3bg4_psiA S t.1 * t.1)
        (psuC3bg4_dagA S t.1 * psuC3bg4_psiA S (psuC3bg4_dagA S t.1))
        (by
          have hψ : psuC3bg4_psiA S t.1 *
              psuC3bg4_psiA S (psuC3bg4_dagA S t.1) = 1 := by
            rw [← psuC3bg4_psiA_mul S (psuC3bg4_dagA S t.1) t.1]
            rw [show psuC3bg4_dagA S t.1 * t.1 = 1 from Subtype.ext t.2,
              psuC3bg4_psiA_one]
          have htd : t.1 * psuC3bg4_dagA S t.1 = 1 :=
            Subtype.ext (psuC3bg4_self_dag_eq_one t.1 t.2)
          calc (psuC3bg4_psiA S t.1 * t.1) *
                (psuC3bg4_dagA S t.1 * psuC3bg4_psiA S (psuC3bg4_dagA S t.1))
              = (psuC3bg4_psiA S t.1 *
                  psuC3bg4_psiA S (psuC3bg4_dagA S t.1)) *
                  (t.1 * psuC3bg4_dagA S t.1) := by ring
            _ = 1 * 1 := by rw [hψ, htd]
            _ = 1 := one_mul 1)
        (by
          have hψ' : psuC3bg4_psiA S (psuC3bg4_dagA S t.1) *
              psuC3bg4_psiA S t.1 = 1 := by
            rw [← psuC3bg4_psiA_mul S t.1 (psuC3bg4_dagA S t.1)]
            rw [show t.1 * psuC3bg4_dagA S t.1 = 1 from
              Subtype.ext (psuC3bg4_self_dag_eq_one t.1 t.2), psuC3bg4_psiA_one]
          have hdt : psuC3bg4_dagA S t.1 * t.1 = 1 := Subtype.ext t.2
          calc (psuC3bg4_dagA S t.1 * psuC3bg4_psiA S (psuC3bg4_dagA S t.1)) *
                (psuC3bg4_psiA S t.1 * t.1)
              = (psuC3bg4_psiA S (psuC3bg4_dagA S t.1) * psuC3bg4_psiA S t.1) *
                  (psuC3bg4_dagA S t.1 * t.1) := by ring
            _ = 1 * 1 := by rw [hψ', hdt]
            _ = 1 := one_mul 1)
      map_one' := by
        apply Units.ext
        change psuC3bg4_psiA S (1 : psuAlg B) * (1 : psuAlg B) = 1
        rw [psuC3bg4_psiA_one, one_mul]
      map_mul' := by
        intro s t
        apply Units.ext
        change psuC3bg4_psiA S (s.1 * t.1) * (s.1 * t.1) =
          (psuC3bg4_psiA S s.1 * s.1) * (psuC3bg4_psiA S t.1 * t.1)
        rw [psuC3bg4_psiA_mul S s.1 t.1]
        ring }
  have hcard := Subgroup.card_ker_mul_card_range N
  have hker : Nat.card N.ker = Nat.card (psuC3b_U h X B) := by
    have hiff : ∀ t : psuC3b_F1 h B, (N t = 1) ↔
        (psuPsi h X ((t.1 : psuAlg B) : Matrix (Fin n) (Fin n) K) *
          ((t.1 : psuAlg B) : Matrix (Fin n) (Fin n) K) = 1) := by
      intro t
      have hval : ((N t : (psuAlg B)ˣ) : psuAlg B) =
          psuC3bg4_psiA S t.1 * t.1 := rfl
      have hiff' : (N t = 1) ↔ (psuC3bg4_psiA S t.1 * t.1 : psuAlg B) = 1 := by
        rw [Units.ext_iff]
        simp [hval]
      exact hiff'.trans Subtype.ext_iff
    exact Nat.card_congr (Equiv.subtypeEquivRight hiff)
  let toNr : N.range → psuC3b_Nrange h X B := fun u =>
    ⟨((u.1 : psuAlg B) : Matrix (Fin n) (Fin n) K), by
      obtain ⟨t, ht⟩ := u.2
      exact ⟨t, by rw [← ht]; rfl⟩⟩
  let fromNr : psuC3b_Nrange h X B → N.range := fun m =>
    ⟨N (Classical.choose m.2), ⟨Classical.choose m.2, rfl⟩⟩
  have hrange : Nat.card N.range = Nat.card (psuC3b_Nrange h X B) := by
    refine Nat.card_congr
      { toFun := toNr, invFun := fromNr, left_inv := ?_, right_inv := ?_ }
    · intro u
      apply Subtype.ext
      apply Units.ext
      have h2 : (u.1 : psuAlg B) = psuC3bg4_psiA S (Classical.choose (toNr u).2).1 *
          (Classical.choose (toNr u).2).1 := by
        apply Subtype.ext
        simpa [psuC3bg4_psiA] using Classical.choose_spec (toNr u).2
      rw [show ((N (Classical.choose (toNr u).2) : (psuAlg B)ˣ) : psuAlg B) =
          psuC3bg4_psiA S (Classical.choose (toNr u).2).1 *
            (Classical.choose (toNr u).2).1 from rfl]
      exact h2.symm
    · intro m
      apply Subtype.ext
      exact (Classical.choose_spec m.2).symm
  rw [hker, hrange] at hcard
  simpa [Nat.mul_comm] using hcard

private lemma psuC3bg1_mem_span_one_sub {R : Type*} [CommRing R] {ε : R}
    (hε : IsIdempotentElem ε) (a : R) :
    a * ε = 0 ↔ a ∈ Ideal.span ({1 - ε} : Set R) := by
  constructor
  · intro h
    have ha : a = a * (1 - ε) := by rw [mul_sub, mul_one, h, sub_zero]
    rw [ha]
    exact Ideal.mul_mem_left _ a (Ideal.subset_span (Set.mem_singleton _))
  · intro ha
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton.mp ha
    rw [hc, mul_assoc, mul_comm c, ← mul_assoc, IsIdempotentElem.one_sub_mul_self hε,
      zero_mul]

private lemma psuC3bg1_quot_equiv {R F : Type*} [CommRing R] [Field F]
    (ε : R) (hε : IsIdempotentElem ε) (π : R →+* F) (hsurj : Function.Surjective π)
    (hker : ∀ a, π a = 0 ↔ a * ε = 0) :
    ∃ q : R ⧸ Ideal.span ({1 - ε} : Set R) ≃+* F,
      ∀ a, q (Ideal.Quotient.mk _ a) = π a := by
  classical
  let I : Ideal R := Ideal.span ({1 - ε} : Set R)
  have hzero : ∀ a ∈ I, π a = 0 := by
    intro a ha
    rw [hker a]
    exact (psuC3bg1_mem_span_one_sub hε a).mpr ha
  let f : R ⧸ I →+* F := Ideal.Quotient.lift I π hzero
  have hf : Function.Bijective f := by
    refine ⟨?_, ?_⟩
    · intro x y hxy
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
      obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective y
      rw [Ideal.Quotient.lift_mk, Ideal.Quotient.lift_mk] at hxy
      rw [Ideal.Quotient.eq]
      have h1 : π (a - b) = 0 := by rw [map_sub, hxy, sub_self]
      rw [hker] at h1
      exact (psuC3bg1_mem_span_one_sub hε (a - b)).mp h1
    · intro y
      obtain ⟨a, ha⟩ := hsurj y
      exact ⟨Ideal.Quotient.mk I a, by rw [Ideal.Quotient.lift_mk, ha]⟩
  refine ⟨RingEquiv.ofBijective f hf, ?_⟩
  intro a
  show f (Ideal.Quotient.mk I a) = π a
  rw [Ideal.Quotient.lift_mk]

private lemma psuC3bg1_pairwise_commute {n : ℕ} {K : Type} [Field K] (B : GL (Fin n) K) :
    (Units.val '' ({B} : Set (GL (Fin n) K)) : Set (Matrix (Fin n) (Fin n) K)).Pairwise
      Commute := by
  rintro x ⟨s, hs, rfl⟩ y ⟨t, ht, rfl⟩ _
  rw [Set.mem_singleton_iff] at hs ht
  subst hs
  subst ht
  exact Commute.refl _

@[instance_reducible]

private noncomputable def psuC3bg1_commRing {n : ℕ} {K : Type} [Field K]
    (B : GL (Fin n) K) : CommRing (psuAlg B) :=
  Algebra.adjoinCommRingOfComm K (psuC3bg1_pairwise_commute B)

private def psuC3bg1_idemFam {n : ℕ} {K : Type} [Field K] (B : GL (Fin n) K)
    (P : Finset (Matrix (Fin n) (Fin n) K)) (hP : PrimFamily (psuAlg B) P) :
    {e // e ∈ P} → psuAlg B :=
  fun i => ⟨i.1, ((hP.1 i.1).mp i.2).1⟩

private lemma psuC3bg1_orthIdem {n : ℕ} {K : Type} [Field K] (B : GL (Fin n) K)
    (P : Finset (Matrix (Fin n) (Fin n) K)) (hP : PrimFamily (psuAlg B) P) :
    OrthogonalIdempotents (psuC3bg1_idemFam B P hP) := by
  refine ⟨?_, ?_⟩
  · intro i
    apply Subtype.ext
    show (i.1 : Matrix (Fin n) (Fin n) K) * i.1 = i.1
    exact (((hP.1 i.1).mp i.2).2.1).eq
  · intro i j hij
    apply Subtype.ext
    show (i.1 : Matrix (Fin n) (Fin n) K) * j.1 = 0
    exact hP.2.1 i.1 i.2 j.1 j.2 (fun h => hij (Subtype.ext h))

private lemma psuC3bg1_dag_mul_eq_zero {f n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    {h : UnitaryFieldData 2 f K} {X B : GL (Fin n) K} (S : PSUGraphSetting h n X B)
    (a e : Matrix (Fin n) (Fin n) K) (ha : a ∈ psuAlg B) (he : e ∈ psuAlg B) :
    psuDag h a * e = 0 ↔ a * psuDag h e = 0 := by
  have hzero : psuDag h (0 : Matrix (Fin n) (Fin n) K) = 0 := by
    simp [psuDag, formAdj]
  constructor
  · intro hz
    have h1 : psuDag h (psuDag h a * e) = 0 := by rw [hz, hzero]
    rw [psuDag_mul, psuDag_dag] at h1
    rw [psuC3b_alg_comm B (psuDag h e) (psuGraph_star_mem S e he).1 a ha] at h1
    exact h1
  · intro hz
    have h1 : psuDag h (a * psuDag h e) = 0 := by rw [hz, hzero]
    rw [psuDag_mul, psuDag_dag] at h1
    rw [psuC3b_alg_comm B e he (psuDag h a) (psuGraph_star_mem S a ha).1] at h1
    exact h1

private lemma psuC3bg1_psi_mul_eq_zero {f n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    {h : UnitaryFieldData 2 f K} {X B : GL (Fin n) K} (S : PSUGraphSetting h n X B)
    (a e : Matrix (Fin n) (Fin n) K) (ha : a ∈ psuAlg B) (he : e ∈ psuAlg B) :
    psuPsi h X a * e = 0 ↔ a * psuPsi h X e = 0 := by
  constructor
  · intro hz
    have h1 : psuPsi h X (psuPsi h X a * e) = 0 := by rw [hz, psuC3b_psi_zero h X]
    rw [psuPsi_mul, psuPsi_psi h X S.X_mem S.X_sq] at h1
    rw [psuC3b_alg_comm B (psuPsi h X e) (psuGraph_star_mem S e he).2 a ha] at h1
    exact h1
  · intro hz
    have h1 : psuPsi h X (a * psuPsi h X e) = 0 := by rw [hz, psuC3b_psi_zero h X]
    rw [psuPsi_mul, psuPsi_psi h X S.X_mem S.X_sq] at h1
    rw [psuC3b_alg_comm B e he (psuPsi h X a) (psuGraph_star_mem S a ha).2] at h1
    exact h1

private noncomputable def psuC3bg1_dagHom {f n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    {h : UnitaryFieldData 2 f K} {X B : GL (Fin n) K} (S : PSUGraphSetting h n X B) : psuAlg B →+* psuAlg B where
  toFun a := ⟨psuDag h a.1, (psuGraph_star_mem S a.1 a.2).1⟩
  map_one' := Subtype.ext (psuDag_one h)
  map_mul' := by
    intro a b
    apply Subtype.ext
    show psuDag h (a.1 * b.1) = psuDag h a.1 * psuDag h b.1
    rw [psuDag_mul]
    exact psuC3b_alg_comm B (psuDag h b.1) (psuGraph_star_mem S b.1 b.2).1
      (psuDag h a.1) (psuGraph_star_mem S a.1 a.2).1
  map_zero' := by
    apply Subtype.ext
    show psuDag h (0 : Matrix (Fin n) (Fin n) K) = 0
    simp [psuDag, formAdj]
  map_add' := by
    intro a b
    apply Subtype.ext
    show psuDag h (a.1 + b.1) = psuDag h a.1 + psuDag h b.1
    rw [psuDag_add]

private noncomputable def psuC3bg1_psiHom {f n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    {h : UnitaryFieldData 2 f K} {X B : GL (Fin n) K} (S : PSUGraphSetting h n X B) : psuAlg B →+* psuAlg B where
  toFun a := ⟨psuPsi h X a.1, (psuGraph_star_mem S a.1 a.2).2⟩
  map_one' := Subtype.ext (psuPsi_one h X)
  map_mul' := by
    intro a b
    apply Subtype.ext
    show psuPsi h X (a.1 * b.1) = psuPsi h X a.1 * psuPsi h X b.1
    rw [psuPsi_mul]
    exact psuC3b_alg_comm B (psuPsi h X b.1) (psuGraph_star_mem S b.1 b.2).2
      (psuPsi h X a.1) (psuGraph_star_mem S a.1 a.2).2
  map_zero' := Subtype.ext (psuC3b_psi_zero h X)
  map_add' := by
    intro a b
    apply Subtype.ext
    show psuPsi h X (a.1 + b.1) = psuPsi h X a.1 + psuPsi h X b.1
    rw [psuPsi_add]

private lemma psuC3b_block_prod {f n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    {h : UnitaryFieldData 2 f K} {X B : GL (Fin n) K}
    (S : PSUGraphSetting h n X B) (P : Finset (Matrix (Fin n) (Fin n) K))
    (hP : PrimFamily (psuAlg B) P) :
    ∃ (F : {e // e ∈ P} → Type) (_ : ∀ e, Field (F e)) (_ : ∀ e, Algebra K (F e))
      (_ : ∀ e, Finite (F e)) (_ : ∀ e, CharP (F e) 2)
      (π : ∀ e, psuAlg B →ₐ[K] F e),
      (∀ e, Function.Surjective (π e)) ∧
      (∀ e (a : psuAlg B), π e a = 0 ↔ (a : Matrix (Fin n) (Fin n) K) * e.1 = 0) ∧
      (∀ e, Module.finrank K (F e) = blockDegree (psuAlg B) e.1) ∧
      (∀ e, Nat.card (F e) = Nat.card K ^ blockDegree (psuAlg B) e.1) ∧
      Function.Bijective (fun (a : psuAlg B) (e : {e // e ∈ P}) => π e a) := by
  classical
  letI : CommRing (psuAlg B) := psuC3bg1_commRing B
  have horth : OrthogonalIdempotents (psuC3bg1_idemFam B P hP) := psuC3bg1_orthIdem B P hP
  have hsum : (∑ i : {e // e ∈ P}, psuC3bg1_idemFam B P hP i) = 1 := by
    apply Subtype.ext
    show ((∑ i : {e // e ∈ P}, psuC3bg1_idemFam B P hP i : psuAlg B) :
      Matrix (Fin n) (Fin n) K) = (1 : Matrix (Fin n) (Fin n) K)
    have hcoe : ((∑ i : {e // e ∈ P}, psuC3bg1_idemFam B P hP i : psuAlg B) :
        Matrix (Fin n) (Fin n) K) = ∑ i : {e // e ∈ P}, i.1 := by
      change (Subalgebra.val (psuAlg B) (∑ i : {e // e ∈ P},
        psuC3bg1_idemFam B P hP i) : Matrix (Fin n) (Fin n) K) =
        ∑ i : {e // e ∈ P}, i.1
      rw [map_sum (Subalgebra.val (psuAlg B))]
      apply Finset.sum_congr rfl
      intro i _
      rw [Subalgebra.val_apply]
      rfl
    rw [hcoe]
    change (P.attach.sum (fun i : {e // e ∈ P} =>
      (i.1 : Matrix (Fin n) (Fin n) K))) = 1
    exact (Finset.sum_attach P (fun x => x)).trans hP.2.2
  have hCO : CompleteOrthogonalIdempotents (psuC3bg1_idemFam B P hP) :=
    CompleteOrthogonalIdempotents.mk horth hsum
  have key : ∀ e : {e // e ∈ P}, ∃ (F : Type) (_ : Field F) (_ : Algebra K F)
      (_ : Finite F) (_ : CharP F 2) (π : psuAlg B →ₐ[K] F),
      Function.Surjective π ∧
      (∀ a : psuAlg B, π a = 0 ↔ (a : Matrix (Fin n) (Fin n) K) * e.1 = 0) ∧
      Module.finrank K F = blockDegree (psuAlg B) e.1 ∧
      Nat.card F = Nat.card K ^ blockDegree (psuAlg B) e.1 := by
    intro e
    obtain ⟨F, hFld, hAlg, hFin, hChar, π, hM, hT, ψ, hπ, hker, hdim, hcard, _⟩ :=
      exists_blockEmbed (A := psuAlg B) S.odd rfl ((hP.1 e.1).mp e.2)
    exact ⟨F, hFld, hAlg, hFin, hChar, π, hπ, hker, hdim, hcard⟩
  choose F fieldF algF finF charF π hdata using key
  have hπ : ∀ e, Function.Surjective (π e) := fun e => (hdata e).1
  have hker : ∀ e (a : psuAlg B), π e a = 0 ↔ (a : Matrix (Fin n) (Fin n) K) * e.1 = 0 :=
    fun e => (hdata e).2.1
  have hdim : ∀ e, Module.finrank K (F e) = blockDegree (psuAlg B) e.1 :=
    fun e => (hdata e).2.2.1
  have hcard : ∀ e, Nat.card (F e) = Nat.card K ^ blockDegree (psuAlg B) e.1 :=
    fun e => (hdata e).2.2.2
  letI := fieldF
  letI := algF
  letI := finF
  letI := charF
  refine ⟨F, fieldF, algF, finF, charF, π, hπ, hker, hdim, hcard, ?_⟩
  have hker' : ∀ (e : {e // e ∈ P}) (a : psuAlg B),
      π e a = 0 ↔ a * psuC3bg1_idemFam B P hP e = 0 := by
    intro e a
    rw [hker e a]
    constructor
    · intro h
      exact Subtype.ext (by simpa [psuC3bg1_idemFam] using h)
    · intro h
      exact by simpa [psuC3bg1_idemFam] using congrArg Subtype.val h
  let q : ∀ e : {e // e ∈ P},
      psuAlg B ⧸ Ideal.span ({1 - psuC3bg1_idemFam B P hP e} : Set (psuAlg B)) ≃+* F e :=
    fun e => Classical.choose (psuC3bg1_quot_equiv (psuC3bg1_idemFam B P hP e)
      (horth.1 e) (π e).toRingHom (hπ e) (hker' e))
  have hq : ∀ e (a : psuAlg B),
      q e (Ideal.Quotient.mk _ a) = π e a :=
    fun e => Classical.choose_spec (psuC3bg1_quot_equiv (psuC3bg1_idemFam B P hP e)
      (horth.1 e) (π e).toRingHom (hπ e) (hker' e))
  have hbij : Function.Bijective (fun (a : psuAlg B) (e : {e // e ∈ P}) => π e a) := by
    have hcomp : (fun (a : psuAlg B) (e : {e // e ∈ P}) => π e a) =
        ⇑(RingEquiv.piCongrRight q) ∘
          ⇑(RingHom.pi (fun i : {e // e ∈ P} =>
            Ideal.Quotient.mk (Ideal.span ({1 - psuC3bg1_idemFam B P hP i} :
              Set (psuAlg B))))) := by
      funext a i
      change π i a = (RingEquiv.piCongrRight q
        ((RingHom.pi (fun i : {e // e ∈ P} =>
          Ideal.Quotient.mk (Ideal.span ({1 - psuC3bg1_idemFam B P hP i} :
            Set (psuAlg B))))) a)) i
      rw [RingEquiv.piCongrRight_apply, RingHom.pi_apply]
      exact (hq i a).symm
    rw [hcomp]
    have h1 : Function.Bijective (⇑(RingEquiv.piCongrRight q)) :=
      (RingEquiv.piCongrRight q).toEquiv.bijective
    exact Function.Bijective.comp h1 (CompleteOrthogonalIdempotents.bijective_pi hCO)
  exact hbij

private lemma psuC3b_star_transport {f n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    {h : UnitaryFieldData 2 f K} {X B : GL (Fin n) K}
    (S : PSUGraphSetting h n X B) (P : Finset (Matrix (Fin n) (Fin n) K))
    (hP : PrimFamily (psuAlg B) P)
    (F : {e // e ∈ P} → Type) [fieldF : ∀ e, Field (F e)]
    [algF : ∀ e, Algebra K (F e)] [finF : ∀ e, Finite (F e)] [charF : ∀ e, CharP (F e) 2]
    (π : ∀ e, psuAlg B →ₐ[K] F e) (hπ : ∀ e, Function.Surjective (π e))
    (hker : ∀ e (a : psuAlg B), π e a = 0 ↔ (a : Matrix (Fin n) (Fin n) K) * e.1 = 0) :
    ∃ (ι : ∀ e e' : {e // e ∈ P}, e'.1 = psuDag h e.1 → (F e' ≃+* F e))
      (Ψ : ∀ e e' : {e // e ∈ P}, e'.1 = psuPsi h X e.1 → (F e' ≃+* F e)),
      (∀ (a : psuAlg B) (e e' : {e // e ∈ P}) (he : e'.1 = psuDag h e.1),
        π e ⟨psuDag h (a : Matrix (Fin n) (Fin n) K), (psuGraph_star_mem S a.1 a.2).1⟩ =
          ι e e' he (π e' a)) ∧
      (∀ (a : psuAlg B) (e e' : {e // e ∈ P}) (he : e'.1 = psuPsi h X e.1),
        π e ⟨psuPsi h X (a : Matrix (Fin n) (Fin n) K), (psuGraph_star_mem S a.1 a.2).2⟩ =
          Ψ e e' he (π e' a)) := by
  classical
  letI : CommRing (psuAlg B) := psuC3bg1_commRing B
  have horth : OrthogonalIdempotents (psuC3bg1_idemFam B P hP) := psuC3bg1_orthIdem B P hP
  have hidem : ∀ e : {e // e ∈ P}, IsIdempotentElem (psuC3bg1_idemFam B P hP e) :=
    fun e => horth.1 e
  have hker' : ∀ (e : {e // e ∈ P}) (a : psuAlg B),
      π e a = 0 ↔ a * psuC3bg1_idemFam B P hP e = 0 := by
    intro e a
    rw [hker e a]
    constructor
    · intro h
      exact Subtype.ext (by simpa [psuC3bg1_idemFam] using h)
    · intro h
      exact by simpa [psuC3bg1_idemFam] using congrArg Subtype.val h
  let q : ∀ e' : {e // e ∈ P},
      psuAlg B ⧸ Ideal.span ({1 - psuC3bg1_idemFam B P hP e'} : Set (psuAlg B)) ≃+* F e' :=
    fun e' => Classical.choose (psuC3bg1_quot_equiv (psuC3bg1_idemFam B P hP e')
      (hidem e') (π e').toRingHom (hπ e') (hker' e'))
  have hq : ∀ e' (a : psuAlg B), q e' (Ideal.Quotient.mk _ a) = π e' a :=
    fun e' => Classical.choose_spec (psuC3bg1_quot_equiv (psuC3bg1_idemFam B P hP e')
      (hidem e') (π e').toRingHom (hπ e') (hker' e'))
  let σdag : (e : {e // e ∈ P}) → (psuAlg B →+* F e) :=
    fun e => (π e).toRingHom.comp (psuC3bg1_dagHom S)
  let σpsi : (e : {e // e ∈ P}) → (psuAlg B →+* F e) :=
    fun e => (π e).toRingHom.comp (psuC3bg1_psiHom S)
  have hsurj_dag : Function.Surjective (psuC3bg1_dagHom S : psuAlg B → psuAlg B) := by
    intro y
    refine ⟨⟨psuDag h y.1, (psuGraph_star_mem S y.1 y.2).1⟩, ?_⟩
    apply Subtype.ext
    show psuDag h (psuDag h y.1) = y.1
    rw [psuDag_dag]
  have hsurj_psi : Function.Surjective (psuC3bg1_psiHom S : psuAlg B → psuAlg B) := by
    intro y
    refine ⟨⟨psuPsi h X y.1, (psuGraph_star_mem S y.1 y.2).2⟩, ?_⟩
    apply Subtype.ext
    show psuPsi h X (psuPsi h X y.1) = y.1
    rw [psuPsi_psi h X S.X_mem S.X_sq]
  have hsurjdag : ∀ (e e' : {e // e ∈ P}) (he : e'.1 = psuDag h e.1),
      Function.Surjective (σdag e) := by
    intro e e' he
    show Function.Surjective (fun x : psuAlg B => π e ((psuC3bg1_dagHom S) x))
    exact Function.Surjective.comp (hπ e) hsurj_dag
  have hsurjpsi : ∀ (e e' : {e // e ∈ P}) (he : e'.1 = psuPsi h X e.1),
      Function.Surjective (σpsi e) := by
    intro e e' he
    show Function.Surjective (fun x : psuAlg B => π e ((psuC3bg1_psiHom S) x))
    exact Function.Surjective.comp (hπ e) hsurj_psi
  have hkerdag : ∀ (e e' : {e // e ∈ P}) (he : e'.1 = psuDag h e.1) (a : psuAlg B),
      σdag e a = 0 ↔ a * psuC3bg1_idemFam B P hP e' = 0 := by
    intro e e' he a
    have h1 : σdag e a =
        π e ⟨psuDag h a.1, (psuGraph_star_mem S a.1 a.2).1⟩ := rfl
    rw [h1, hker e ⟨psuDag h a.1, (psuGraph_star_mem S a.1 a.2).1⟩]
    have h2 : psuDag h a.1 * e.1 = 0 ↔ a.1 * psuDag h e.1 = 0 :=
      psuC3bg1_dag_mul_eq_zero S a.1 e.1 a.2 ((hP.1 e.1).mp e.2).1
    rw [h2, ← he]
    constructor
    · intro h
      exact Subtype.ext (by simpa [psuC3bg1_idemFam] using h)
    · intro h
      exact by simpa [psuC3bg1_idemFam] using congrArg Subtype.val h
  have hkerpsi : ∀ (e e' : {e // e ∈ P}) (he : e'.1 = psuPsi h X e.1) (a : psuAlg B),
      σpsi e a = 0 ↔ a * psuC3bg1_idemFam B P hP e' = 0 := by
    intro e e' he a
    have h1 : σpsi e a =
        π e ⟨psuPsi h X a.1, (psuGraph_star_mem S a.1 a.2).2⟩ := rfl
    rw [h1, hker e ⟨psuPsi h X a.1, (psuGraph_star_mem S a.1 a.2).2⟩]
    have h2 : psuPsi h X a.1 * e.1 = 0 ↔ a.1 * psuPsi h X e.1 = 0 :=
      psuC3bg1_psi_mul_eq_zero S a.1 e.1 a.2 ((hP.1 e.1).mp e.2).1
    rw [h2, ← he]
    constructor
    · intro h
      exact Subtype.ext (by simpa [psuC3bg1_idemFam] using h)
    · intro h
      exact by simpa [psuC3bg1_idemFam] using congrArg Subtype.val h
  let qdag : ∀ (e e' : {e // e ∈ P}) (he : e'.1 = psuDag h e.1),
      psuAlg B ⧸ Ideal.span ({1 - psuC3bg1_idemFam B P hP e'} : Set (psuAlg B)) ≃+* F e :=
    fun e e' he => Classical.choose (psuC3bg1_quot_equiv (psuC3bg1_idemFam B P hP e')
      (hidem e') (σdag e) (hsurjdag e e' he) (hkerdag e e' he))
  have hqdag : ∀ (e e' : {e // e ∈ P}) (he : e'.1 = psuDag h e.1) (a : psuAlg B),
      qdag e e' he (Ideal.Quotient.mk _ a) = σdag e a :=
    fun e e' he => Classical.choose_spec (psuC3bg1_quot_equiv (psuC3bg1_idemFam B P hP e')
      (hidem e') (σdag e) (hsurjdag e e' he) (hkerdag e e' he))
  let qpsi : ∀ (e e' : {e // e ∈ P}) (he : e'.1 = psuPsi h X e.1),
      psuAlg B ⧸ Ideal.span ({1 - psuC3bg1_idemFam B P hP e'} : Set (psuAlg B)) ≃+* F e :=
    fun e e' he => Classical.choose (psuC3bg1_quot_equiv (psuC3bg1_idemFam B P hP e')
      (hidem e') (σpsi e) (hsurjpsi e e' he) (hkerpsi e e' he))
  have hqpsi : ∀ (e e' : {e // e ∈ P}) (he : e'.1 = psuPsi h X e.1) (a : psuAlg B),
      qpsi e e' he (Ideal.Quotient.mk _ a) = σpsi e a :=
    fun e e' he => Classical.choose_spec (psuC3bg1_quot_equiv (psuC3bg1_idemFam B P hP e')
      (hidem e') (σpsi e) (hsurjpsi e e' he) (hkerpsi e e' he))
  let ι0 : ∀ e e' : {e // e ∈ P}, e'.1 = psuDag h e.1 → (F e' ≃+* F e) :=
    fun e e' he => (q e').symm.trans (qdag e e' he)
  let Ψ0 : ∀ e e' : {e // e ∈ P}, e'.1 = psuPsi h X e.1 → (F e' ≃+* F e) :=
    fun e e' he => (q e').symm.trans (qpsi e e' he)
  refine ⟨ι0, Ψ0, ?_, ?_⟩
  · intro a e e' he
    have h1 : (q e').symm (π e' a) = Ideal.Quotient.mk _ a := by
      rw [← hq e' a, RingEquiv.symm_apply_apply]
    have h2 : qdag e e' he (Ideal.Quotient.mk _ a) = σdag e a := hqdag e e' he a
    change π e ⟨psuDag h a.1, (psuGraph_star_mem S a.1 a.2).1⟩ =
      (qdag e e' he) ((q e').symm (π e' a))
    rw [h1, h2]
    rfl
  · intro a e e' he
    have h1 : (q e').symm (π e' a) = Ideal.Quotient.mk _ a := by
      rw [← hq e' a, RingEquiv.symm_apply_apply]
    have h2 : qpsi e e' he (Ideal.Quotient.mk _ a) = σpsi e a := hqpsi e e' he a
    change π e ⟨psuPsi h X a.1, (psuGraph_star_mem S a.1 a.2).2⟩ =
      (qpsi e e' he) ((q e').symm (π e' a))
    rw [h1, h2]
    rfl

private theorem psuC3b_field_unitary_card {E : Type} [Field E] [Finite E]
    (Y : E ≃+* E) (hY2 : ∀ t, Y (Y t) = t) (hY1 : ∃ t, Y t ≠ t) :
    Nat.card {t : E // Y t * t = 1} = Nat.sqrt (Nat.card E) + 1 := by
  classical
  have hY2' : Y * Y = 1 := by
    ext t
    exact hY2 t
  have hY1' : Y ≠ 1 := by
    obtain ⟨t, ht⟩ := hY1
    exact fun h => ht (by simpa using congrArg (fun e : E ≃+* E => e t) h)
  obtain ⟨Q, hQ, hRange⟩ := CFSG.StandardType.pslGraph_norm_card_II (F := E) Y hY2' hY1'
  let N : Eˣ →* Eˣ := Units.map Y.toMonoidHom * MonoidHom.id Eˣ
  have hNval : ∀ u : Eˣ, ((N u : Eˣ) : E) = Y (u : E) * (u : E) := by
    intro u
    simp only [N, MonoidHom.mul_apply, Units.val_mul, Units.coe_map, MonoidHom.id_apply]
    rfl
  have hRangeE : Nat.card (Set.range (fun u : Eˣ => ((N u : Eˣ) : E))) = Q - 1 := by
    rw [show (fun u : Eˣ => ((N u : Eˣ) : E)) = (fun u : Eˣ => Y (u : E) * (u : E))
      from funext hNval]
    exact hRange
  have himg : Set.range (fun u : Eˣ => ((N u : Eˣ) : E)) =
      (fun u : Eˣ => (u : E)) '' (Set.range (fun u : Eˣ => N u)) := by
    ext x
    constructor
    · rintro ⟨u, rfl⟩
      exact ⟨N u, ⟨u, rfl⟩, rfl⟩
    · rintro ⟨u, ⟨v, rfl⟩, rfl⟩
      exact ⟨v, rfl⟩
  rw [himg, Nat.card_image_of_injective (fun a b h => Units.ext h)] at hRangeE
  have hRangeKer : Nat.card N.range = Q - 1 := by
    have h := hRangeE
    rw [show (Set.range (fun u : Eˣ => N u)) = ((N.range : Subgroup Eˣ) : Set Eˣ) from
      (MonoidHom.coe_range N).symm] at h
    exact h
  have hQ2 : 2 ≤ Q := by
    have h2 : 2 ≤ Q * Q := by
      rw [← hQ]
      haveI : Fintype E := Fintype.ofFinite E
      rw [Nat.card_eq_fintype_card]
      exact Fintype.one_lt_card
    by_contra hcon
    have hle : Q ≤ 1 := by omega
    have hmul : Q * Q ≤ 1 := by simpa using Nat.mul_le_mul hle hle
    omega
  have hker : Nat.card N.ker = Q + 1 := by
    have h := Subgroup.card_mul_index N.ker
    rw [Subgroup.index_ker, hRangeKer, Nat.card_units, hQ] at h
    have hsq : Q * Q - 1 = (Q + 1) * (Q - 1) := by
      have h1 : 1 ≤ Q := by omega
      have h2 : 1 ≤ Q * Q := by nlinarith
      nlinarith [Nat.sub_add_cancel h1, Nat.sub_add_cancel h2]
    rw [hsq] at h
    exact Nat.eq_of_mul_eq_mul_right (by omega) h
  have hset : Nat.card {t : E // Y t * t = 1} = Nat.card N.ker := by
    have h1 : Nat.card {t : E // Y t * t = 1} = Nat.card {u : Eˣ // N u = 1} := by
      apply Nat.card_congr
      let ht0 : ∀ t : {t : E // Y t * t = 1}, t.1 ≠ 0 := fun t => by
        intro h0
        have ht : Y (0 : E) * (0 : E) = 1 := by simpa [h0] using t.2
        rw [map_zero, mul_zero] at ht
        exact zero_ne_one ht
      refine
        { toFun := fun t =>
            ⟨Units.mk0 t.1 (ht0 t), by
              apply Units.ext
              show ((N (Units.mk0 t.1 (ht0 t)) : Eˣ) : E) = (1 : E)
              rw [hNval]
              simpa using t.2⟩
          invFun := fun u =>
            ⟨(u.1 : E), by
              have h2 := congrArg (fun w : Eˣ => (w : E)) u.2
              rw [hNval] at h2
              exact h2⟩
          left_inv := fun t => Subtype.ext rfl
          right_inv := fun u => Subtype.ext (Units.ext rfl) }
    rw [h1]
    exact Nat.card_congr (Equiv.subtypeEquiv (Equiv.refl _)
      (fun u => (MonoidHom.mem_ker).symm))
  rw [hset, hker, hQ, Nat.sqrt_eq]

private theorem psuC3b_field_units_card {E : Type} [Field E] :
    Nat.card Eˣ = Nat.card E - 1 :=
  Nat.card_units E

private theorem psuC3b_field_fix_units_card {E : Type} [Field E] [Finite E]
    (Y : E ≃+* E) (hY2 : ∀ t, Y (Y t) = t) (hY1 : ∃ t, Y t ≠ t) :
    Nat.card {t : Eˣ // Y (t : E) = (t : E)} = Nat.sqrt (Nat.card E) - 1 := by
  classical
  have hY2' : Y * Y = 1 := by
    ext t
    exact hY2 t
  have hY1' : Y ≠ 1 := by
    obtain ⟨t, ht⟩ := hY1
    exact fun h => ht (by simpa using congrArg (fun e : E ≃+* E => e t) h)
  have horder : orderOf Y = 2 := by
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact orderOf_eq_prime (by simpa [pow_two] using hY2') hY1'
  let K : Subfield E := FixedPoints.subfield (Subgroup.zpowers Y) E
  let F : Subfield E := FixedBy.subfield E Y
  have hKF : K = F := by
    apply Subfield.ext
    intro x
    show x ∈ MulAction.fixedPoints (Subgroup.zpowers Y) E ↔ x ∈ F
    rw [MulAction.mem_fixedPoints]
    change (∀ m : ↥(Subgroup.zpowers Y), m • x = x) ↔ x ∈ MulAction.fixedBy E Y
    rw [MulAction.mem_fixedBy]
    constructor
    · intro hx
      simpa using hx ⟨Y, Subgroup.mem_zpowers Y⟩
    · intro hx m
      have hYmem : Y ∈ MulAction.stabilizer (E ≃+* E) x := by
        rw [MulAction.mem_stabilizer_iff]
        simpa using hx
      have hle : Subgroup.zpowers Y ≤ MulAction.stabilizer (E ≃+* E) x :=
        (Subgroup.zpowers_le).mpr hYmem
      have hm := hle m.2
      rwa [MulAction.mem_stabilizer_iff] at hm
  have hKcard : Nat.card E = Nat.card K ^ 2 := by
    have h := CFSG.GorensteinWalter.nat_card_eq_fixedSubfield_card_pow_orderOf E Y
    rw [horder] at h
    simpa [K] using h
  have hFcard : Nat.card F = Nat.sqrt (Nat.card E) := by
    rw [← hKF, hKcard, Nat.sqrt_eq']
  have hset : Nat.card {t : Eˣ // Y (t : E) = (t : E)} = Nat.card Fˣ := by
    apply Nat.card_congr
    refine
      { toFun := fun t => Units.mk0 ⟨(t.1 : E), ?_⟩ (by
            intro h
            exact t.1.ne_zero (congrArg Subtype.val h))
        invFun := fun u => ⟨Units.map F.subtype.toMonoidHom u, ?_⟩
        left_inv := ?_
        right_inv := ?_ }
    · change (t.1 : E) ∈ MulAction.fixedBy E Y
      rw [MulAction.mem_fixedBy]
      simpa using t.2
    · show Y ((↑(Units.map F.subtype.toMonoidHom u) : Eˣ) : E) =
        ((↑(Units.map F.subtype.toMonoidHom u) : Eˣ) : E)
      have hu : ((u : F) : E) ∈ F := u.1.2
      change ((u : F) : E) ∈ MulAction.fixedBy E Y at hu
      rw [MulAction.mem_fixedBy] at hu
      simpa using hu
    · intro t
      exact Subtype.ext (Units.ext rfl)
    · intro u
      exact Units.ext (Subtype.ext rfl)
  rw [hset, Nat.card_units, hFcard]

private noncomputable def psuC3bg2_D {f n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    {h : UnitaryFieldData 2 f K} {X B : GL (Fin n) K} (S : PSUGraphSetting h n X B)
    (P : Finset (Matrix (Fin n) (Fin n) K)) (hP : PrimFamily (psuAlg B) P) :
    {e // e ∈ P} → {e // e ∈ P} :=
  fun e => ⟨psuDag h e.1, (psuC3b_star_mem_of_primFamily S P hP e.1 e.2).1⟩

private noncomputable def psuC3bg2_ιA {f n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    {h : UnitaryFieldData 2 f K} {X B : GL (Fin n) K} (S : PSUGraphSetting h n X B)
    (P : Finset (Matrix (Fin n) (Fin n) K)) (hP : PrimFamily (psuAlg B) P)
    {F : {e // e ∈ P} → Type} [fieldF : ∀ e, Field (F e)]
    (ι : ∀ e e' : {e // e ∈ P}, e'.1 = psuDag h e.1 → (F e' ≃+* F e))
    (e : {e // e ∈ P}) : F (psuC3bg2_D S P hP e) ≃+* F e :=
  ι e (psuC3bg2_D S P hP e) rfl

private def psuC3bg2_W {f n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    {h : UnitaryFieldData 2 f K} {X B : GL (Fin n) K} (S : PSUGraphSetting h n X B)
    (P : Finset (Matrix (Fin n) (Fin n) K)) (hP : PrimFamily (psuAlg B) P)
    {F : {e // e ∈ P} → Type} [fieldF : ∀ e, Field (F e)]
    (ι : ∀ e e' : {e // e ∈ P}, e'.1 = psuDag h e.1 → (F e' ≃+* F e)) : Type :=
  {y : ∀ e : {e // e ∈ P}, F e //
    ∀ e : {e // e ∈ P},
      psuC3bg2_ιA S P hP ι e (y (psuC3bg2_D S P hP e)) * y e = 1}

private lemma psuC3bg2_cond_iff {f n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    {h : UnitaryFieldData 2 f K} {X B : GL (Fin n) K} (S : PSUGraphSetting h n X B)
    (P : Finset (Matrix (Fin n) (Fin n) K)) (hP : PrimFamily (psuAlg B) P)
    {F : {e // e ∈ P} → Type} [fieldF : ∀ e, Field (F e)]
    [algF : ∀ e, Algebra K (F e)]
    (π : ∀ e, psuAlg B →ₐ[K] F e)
    (ι : ∀ e e' : {e // e ∈ P}, e'.1 = psuDag h e.1 → (F e' ≃+* F e))
    (hι : ∀ (a : psuAlg B) (e e' : {e // e ∈ P}) (he : e'.1 = psuDag h e.1),
      π e ⟨psuDag h (a : Matrix (Fin n) (Fin n) K), (psuGraph_star_mem S a.1 a.2).1⟩ =
        ι e e' he (π e' a))
    (hbij : Function.Bijective (fun (a : psuAlg B) (e : {e // e ∈ P}) => π e a))
    (a : psuAlg B) :
    (psuDag h (a : Matrix (Fin n) (Fin n) K) * (a : Matrix (Fin n) (Fin n) K) = 1) ↔
      (∀ e : {e // e ∈ P},
        psuC3bg2_ιA S P hP ι e (π (psuC3bg2_D S P hP e) a) * π e a = 1) := by
  constructor
  · intro hmat e
    have hmem : (⟨psuDag h (a : Matrix (Fin n) (Fin n) K),
        (psuGraph_star_mem S a.1 a.2).1⟩ * a : psuAlg B) = 1 := by
      apply Subtype.ext
      simpa using hmat
    have hstep : psuC3bg2_ιA S P hP ι e (π (psuC3bg2_D S P hP e) a) =
        π e ⟨psuDag h (a : Matrix (Fin n) (Fin n) K),
          (psuGraph_star_mem S a.1 a.2).1⟩ := by
      rw [psuC3bg2_ιA]
      exact (hι a e (psuC3bg2_D S P hP e) rfl).symm
    calc psuC3bg2_ιA S P hP ι e (π (psuC3bg2_D S P hP e) a) * π e a
        = π e ⟨psuDag h (a : Matrix (Fin n) (Fin n) K),
            (psuGraph_star_mem S a.1 a.2).1⟩ * π e a := by rw [hstep]
      _ = π e (⟨psuDag h (a : Matrix (Fin n) (Fin n) K),
            (psuGraph_star_mem S a.1 a.2).1⟩ * a) := by rw [map_mul]
      _ = π e 1 := by rw [hmem]
      _ = 1 := map_one (π e)
  · intro H
    have hmem : ∀ e : {e // e ∈ P},
        π e (⟨psuDag h (a : Matrix (Fin n) (Fin n) K),
          (psuGraph_star_mem S a.1 a.2).1⟩ * a) = π e (1 : psuAlg B) := by
      intro e
      rw [map_mul, map_one]
      rw [show π e ⟨psuDag h (a : Matrix (Fin n) (Fin n) K),
          (psuGraph_star_mem S a.1 a.2).1⟩ =
          psuC3bg2_ιA S P hP ι e (π (psuC3bg2_D S P hP e) a) from by
        rw [psuC3bg2_ιA]
        exact hι a e (psuC3bg2_D S P hP e) rfl]
      exact H e
    have halg : (⟨psuDag h (a : Matrix (Fin n) (Fin n) K),
        (psuGraph_star_mem S a.1 a.2).1⟩ * a : psuAlg B) = 1 :=
      hbij.1 (funext hmem)
    simpa using congrArg Subtype.val halg

private lemma psuC3bg2_F1_card_bijection {f n : ℕ} {K : Type} [Field K] [Finite K]
    [CharP K 2] {h : UnitaryFieldData 2 f K} {X B : GL (Fin n) K}
    (S : PSUGraphSetting h n X B) (P : Finset (Matrix (Fin n) (Fin n) K))
    (hP : PrimFamily (psuAlg B) P) {F : {e // e ∈ P} → Type} [fieldF : ∀ e, Field (F e)]
    [algF : ∀ e, Algebra K (F e)]
    (π : ∀ e, psuAlg B →ₐ[K] F e)
    (ι : ∀ e e' : {e // e ∈ P}, e'.1 = psuDag h e.1 → (F e' ≃+* F e))
    (hι : ∀ (a : psuAlg B) (e e' : {e // e ∈ P}) (he : e'.1 = psuDag h e.1),
      π e ⟨psuDag h (a : Matrix (Fin n) (Fin n) K), (psuGraph_star_mem S a.1 a.2).1⟩ =
        ι e e' he (π e' a))
    (hbij : Function.Bijective (fun (a : psuAlg B) (e : {e // e ∈ P}) => π e a)) :
    Nat.card (psuC3b_F1 h B) = Nat.card (psuC3bg2_W S P hP ι) := by
  classical
  let eB : psuAlg B ≃ (∀ e : {e // e ∈ P}, F e) := Equiv.ofBijective _ hbij
  have h := Nat.card_congr (Equiv.subtypeEquiv eB
    (p := fun a : psuAlg B =>
      psuDag h (a : Matrix (Fin n) (Fin n) K) * (a : Matrix (Fin n) (Fin n) K) = 1)
    (q := fun y : ∀ e : {e // e ∈ P}, F e =>
      ∀ e : {e // e ∈ P}, psuC3bg2_ιA S P hP ι e (y (psuC3bg2_D S P hP e)) * y e = 1)
    (fun a => by
      simpa [eB, psuC3bg2_W] using psuC3bg2_cond_iff S P hP π ι hι hbij a))
  simpa [psuC3b_F1, psuC3bg2_W, eB] using h

private def psuC3bg2_fiber {f n : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData 2 f K) (X : GL (Fin n) K)
    (P : Finset (Matrix (Fin n) (Fin n) K)) (R : Finset (Matrix (Fin n) (Fin n) K))
    (r : {r // r ∈ R}) : Type :=
  {e : {e // e ∈ P} // e.1 ∈ psuC3b_orbit h X r.1}

private noncomputable def psuC3bg2_rep {f n : ℕ} {K : Type} [Field K]
    {h : UnitaryFieldData 2 f K} {X : GL (Fin n) K}
    (P : Finset (Matrix (Fin n) (Fin n) K)) (R : Finset (Matrix (Fin n) (Fin n) K))
    (hrep : ∀ e ∈ P, ∃! r, r ∈ R ∧
      (r = e ∨ r = psuDag h e ∨ r = psuPsi h X e ∨ r = psuDag h (psuPsi h X e)))
    (e : {e // e ∈ P}) : {r // r ∈ R} :=
  ⟨Classical.choose (hrep e.1 e.2), (Classical.choose_spec (hrep e.1 e.2)).1.1⟩

private lemma psuC3bg2_D_mem_orbit {f n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    {h : UnitaryFieldData 2 f K} {X B : GL (Fin n) K} (S : PSUGraphSetting h n X B)
    {r e : Matrix (Fin n) (Fin n) K}
    (he : e ∈ psuC3b_orbit h X r) : psuDag h e ∈ psuC3b_orbit h X r := by
  have hEq : psuC3b_orbit h X e = psuC3b_orbit h X r := psuC3b_orbit_eq S he
  have hmem : psuDag h e ∈ psuC3b_orbit h X e :=
    psuC3b_orbit_dag_mem (psuC3b_orbit_self h X e)
  rwa [hEq] at hmem

private lemma psuC3bg2_rep_mem_orbit {f n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    {h : UnitaryFieldData 2 f K} {X B : GL (Fin n) K} (S : PSUGraphSetting h n X B)
    (P : Finset (Matrix (Fin n) (Fin n) K)) (R : Finset (Matrix (Fin n) (Fin n) K))
    (hrep : ∀ e ∈ P, ∃! r, r ∈ R ∧
      (r = e ∨ r = psuDag h e ∨ r = psuPsi h X e ∨ r = psuDag h (psuPsi h X e)))
    (e : {e // e ∈ P}) :
    e.1 ∈ psuC3b_orbit h X (psuC3bg2_rep P R hrep e).1 := by
  have hdisj := (Classical.choose_spec (hrep e.1 e.2)).1.2
  have hmem : (psuC3bg2_rep P R hrep e).1 ∈ psuC3b_orbit h X e.1 := by
    simpa [psuC3bg2_rep, psuC3b_orbit] using hdisj
  exact psuC3b_orbit_symm S hmem

private lemma psuC3bg2_rep_eq {f n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    {h : UnitaryFieldData 2 f K} {X B : GL (Fin n) K} (S : PSUGraphSetting h n X B)
    (P : Finset (Matrix (Fin n) (Fin n) K)) (R : Finset (Matrix (Fin n) (Fin n) K))
    (hrep : ∀ e ∈ P, ∃! r, r ∈ R ∧
      (r = e ∨ r = psuDag h e ∨ r = psuPsi h X e ∨ r = psuDag h (psuPsi h X e)))
    (e : {e // e ∈ P}) (r : Matrix (Fin n) (Fin n) K) (hr : r ∈ R)
    (he : e.1 ∈ psuC3b_orbit h X r) : psuC3bg2_rep P R hrep e = ⟨r, hr⟩ := by
  apply Subtype.ext
  have hspec := (Classical.choose_spec (hrep e.1 e.2)).2
  have hmem : r ∈ psuC3b_orbit h X e.1 := psuC3b_orbit_symm S he
  have hdisj : r = e.1 ∨ r = psuDag h e.1 ∨ r = psuPsi h X e.1 ∨
      r = psuDag h (psuPsi h X e.1) := by
    simpa [psuC3b_orbit] using hmem
  exact (hspec r ⟨hr, hdisj⟩).symm

private lemma psuC3bg2_z_cast {f n : ℕ} {K : Type} [Field K]
    {h : UnitaryFieldData 2 f K} {X : GL (Fin n) K}
    (P : Finset (Matrix (Fin n) (Fin n) K)) (R : Finset (Matrix (Fin n) (Fin n) K))
    {F : {e // e ∈ P} → Type} {r r' : {r // r ∈ R}} (hr : r' = r)
    (z : (r : {r // r ∈ R}) → (e : psuC3bg2_fiber h X P R r) → F e.1)
    (e : psuC3bg2_fiber h X P R r) (mem' : e.1.1 ∈ psuC3b_orbit h X r'.1) :
    HEq (z r' ⟨e.1, mem'⟩) (z r e) := by
  cases hr
  rfl

private noncomputable def psuC3bg2_piEquiv {f n : ℕ} {K : Type} [Field K] [Finite K]
    [CharP K 2] {h : UnitaryFieldData 2 f K} {X B : GL (Fin n) K}
    (S : PSUGraphSetting h n X B) (P : Finset (Matrix (Fin n) (Fin n) K))
    (R : Finset (Matrix (Fin n) (Fin n) K))
    (hrep : ∀ e ∈ P, ∃! r, r ∈ R ∧
      (r = e ∨ r = psuDag h e ∨ r = psuPsi h X e ∨ r = psuDag h (psuPsi h X e)))
    (F : {e // e ∈ P} → Type) :
    ((e : {e // e ∈ P}) → F e) ≃
      ((r : {r // r ∈ R}) → (e : psuC3bg2_fiber h X P R r) → F e.1) where
  toFun y r e := y e.1
  invFun z e := z (psuC3bg2_rep P R hrep e)
    ⟨e, psuC3bg2_rep_mem_orbit S P R hrep e⟩
  left_inv y := by
    funext e
    rfl
  right_inv z := by
    funext r e
    have hrep_eq : psuC3bg2_rep P R hrep e.1 = r :=
      psuC3bg2_rep_eq S P R hrep e.1 r.1 r.2 e.2
    change z (psuC3bg2_rep P R hrep e.1)
      ⟨e.1, psuC3bg2_rep_mem_orbit S P R hrep e.1⟩ = z r e
    exact eq_of_heq (psuC3bg2_z_cast P R hrep_eq z e
      (psuC3bg2_rep_mem_orbit S P R hrep e.1))

private def psuC3bg2_LocalPred {f n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    {h : UnitaryFieldData 2 f K} {X B : GL (Fin n) K} (S : PSUGraphSetting h n X B)
    (P : Finset (Matrix (Fin n) (Fin n) K)) (R : Finset (Matrix (Fin n) (Fin n) K))
    (hP : PrimFamily (psuAlg B) P)
    {F : {e // e ∈ P} → Type} [fieldF : ∀ e, Field (F e)]
    (ι : ∀ e e' : {e // e ∈ P}, e'.1 = psuDag h e.1 → (F e' ≃+* F e))
    (r : {r // r ∈ R}) (z : (e : psuC3bg2_fiber h X P R r) → F e.1) : Prop :=
  ∀ e : psuC3bg2_fiber h X P R r,
    psuC3bg2_ιA S P hP ι e.1
      (z ⟨psuC3bg2_D S P hP e.1, psuC3bg2_D_mem_orbit S e.2⟩) * z e = 1

private def psuC3bg2_Local {f n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    {h : UnitaryFieldData 2 f K} {X B : GL (Fin n) K} (S : PSUGraphSetting h n X B)
    (P : Finset (Matrix (Fin n) (Fin n) K)) (R : Finset (Matrix (Fin n) (Fin n) K))
    (hP : PrimFamily (psuAlg B) P)
    {F : {e // e ∈ P} → Type} [fieldF : ∀ e, Field (F e)]
    (ι : ∀ e e' : {e // e ∈ P}, e'.1 = psuDag h e.1 → (F e' ≃+* F e))
    (r : {r // r ∈ R}) : Type :=
  {z : (e : psuC3bg2_fiber h X P R r) → F e.1 //
    psuC3bg2_LocalPred S P R hP ι r z}

private noncomputable def psuC3bg2_Dfib {f n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    {h : UnitaryFieldData 2 f K} {X B : GL (Fin n) K} (S : PSUGraphSetting h n X B)
    (P : Finset (Matrix (Fin n) (Fin n) K)) (hP : PrimFamily (psuAlg B) P)
    (R : Finset (Matrix (Fin n) (Fin n) K)) (r : {r // r ∈ R}) :
    psuC3bg2_fiber h X P R r → psuC3bg2_fiber h X P R r :=
  fun e => ⟨psuC3bg2_D S P hP e.1, psuC3bg2_D_mem_orbit S e.2⟩

private lemma psuC3bg2_iota_inv {f n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    {h : UnitaryFieldData 2 f K} {X B : GL (Fin n) K} (S : PSUGraphSetting h n X B)
    (P : Finset (Matrix (Fin n) (Fin n) K))
    {F : {e // e ∈ P} → Type} [fieldF : ∀ e, Field (F e)]
    [algF : ∀ e, Algebra K (F e)]
    (π : ∀ e, psuAlg B →ₐ[K] F e) (hπ : ∀ e, Function.Surjective (π e))
    (ι : ∀ e e' : {e // e ∈ P}, e'.1 = psuDag h e.1 → (F e' ≃+* F e))
    (hι : ∀ (a : psuAlg B) (e e' : {e // e ∈ P}) (he : e'.1 = psuDag h e.1),
      π e ⟨psuDag h (a : Matrix (Fin n) (Fin n) K), (psuGraph_star_mem S a.1 a.2).1⟩ =
        ι e e' he (π e' a))
    {e e' : {e // e ∈ P}} (he : e'.1 = psuDag h e.1)
    (he' : e.1 = psuDag h e'.1) :
    ι e' e he' = (ι e e' he).symm := by
  let f : F e' ≃+* F e := ι e e' he
  let g : F e ≃+* F e' := ι e' e he'
  have hfg : ∀ y : F e, f (g y) = y := by
    intro y
    obtain ⟨a, rfl⟩ := hπ e y
    let a' : psuAlg B := ⟨psuDag h (a : Matrix (Fin n) (Fin n) K),
      (psuGraph_star_mem S a.1 a.2).1⟩
    have h1 : g (π e a) = π e' a' := (hι a e' e he').symm
    have h2 : f (π e' a') = π e ⟨psuDag h (a' : Matrix (Fin n) (Fin n) K),
      (psuGraph_star_mem S a'.1 a'.2).1⟩ := (hι a' e e' he).symm
    have h3 : (⟨psuDag h (a' : Matrix (Fin n) (Fin n) K),
        (psuGraph_star_mem S a'.1 a'.2).1⟩ : psuAlg B) = a := by
      apply Subtype.ext
      exact psuDag_dag h (a : Matrix (Fin n) (Fin n) K)
    rw [h1, h2, h3]
  apply RingEquiv.ext
  intro x
  calc g x = f.symm (f (g x)) := (f.symm_apply_apply (g x)).symm
    _ = f.symm x := by rw [hfg x]

private abbrev psuC3bg2_LocalF {f n : ℕ} {K : Type} [Field K]
    {h : UnitaryFieldData 2 f K} (P : Finset (Matrix (Fin n) (Fin n) K))
    {F : {e // e ∈ P} → Type} [fieldF : ∀ e, Field (F e)]
    (ι : ∀ e e' : {e // e ∈ P}, e'.1 = psuDag h e.1 → (F e' ≃+* F e))
    (A : Type) (key : A → {e // e ∈ P}) : Type :=
  LocalFamilies (fun x y : {e // e ∈ P} => y.1 = psuDag h x.1) ι A key

private lemma psuC3bg2_Local_card_eq {f n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    {h : UnitaryFieldData 2 f K} {X B : GL (Fin n) K} (S : PSUGraphSetting h n X B)
    (P : Finset (Matrix (Fin n) (Fin n) K)) (hP : PrimFamily (psuAlg B) P)
    (R : Finset (Matrix (Fin n) (Fin n) K))
    {F : {e // e ∈ P} → Type} [fieldF : ∀ e, Field (F e)]
    (ι : ∀ e e' : {e // e ∈ P}, e'.1 = psuDag h e.1 → (F e' ≃+* F e))
    (r : {r // r ∈ R}) :
    Nat.card (psuC3bg2_Local S P R hP ι r) =
      Nat.card (psuC3bg2_LocalF P ι (psuC3bg2_fiber h X P R r) (fun x => x.1)) := by
  classical
  apply Nat.card_congr
  refine Equiv.subtypeEquiv (Equiv.refl _) ?_
  intro z
  constructor
  · intro hz x y he
    have hy : y = ⟨psuC3bg2_D S P hP x.1, psuC3bg2_D_mem_orbit S x.2⟩ := by
      apply Subtype.ext
      apply Subtype.ext
      exact he
    subst hy
    simpa [psuC3bg2_ιA, psuC3bg2_Dfib, psuC3bg2_LocalPred] using hz x
  · intro hz e
    have h := hz e ⟨psuC3bg2_D S P hP e.1, psuC3bg2_D_mem_orbit S e.2⟩ rfl
    simpa [psuC3bg2_ιA, psuC3bg2_Dfib, psuC3bg2_LocalPred] using h

private lemma psuC3bg2_LocalF_split {f n : ℕ} {K : Type} [Field K]
    {h : UnitaryFieldData 2 f K} (P : Finset (Matrix (Fin n) (Fin n) K))
    {F : {e // e ∈ P} → Type} [fieldF : ∀ e, Field (F e)]
    (ι : ∀ e e' : {e // e ∈ P}, e'.1 = psuDag h e.1 → (F e' ≃+* F e))
    (A : Type) (key : A → {e // e ∈ P}) (p : A → Prop) [DecidablePred p]
    (hp : ∀ x y : A, (key y).1 = psuDag h (key x).1 → (p x ↔ p y)) :
    Nat.card (psuC3bg2_LocalF P ι A key) =
      Nat.card (psuC3bg2_LocalF P ι {x // p x} (fun x => key x.1)) *
        Nat.card (psuC3bg2_LocalF P ι {x // ¬ p x} (fun x => key x.1)) :=
  card_localFamilies_split (fun x y : {e // e ∈ P} => y.1 = psuDag h x.1) ι A key p hp

private lemma psuC3bg2_LocalF_unique {f n : ℕ} {K : Type} [Field K]
    {h : UnitaryFieldData 2 f K} (P : Finset (Matrix (Fin n) (Fin n) K))
    {F : {e // e ∈ P} → Type} [fieldF : ∀ e, Field (F e)]
    (ι : ∀ e e' : {e // e ∈ P}, e'.1 = psuDag h e.1 → (F e' ≃+* F e))
    (A : Type) [Unique A] (key : A → {e // e ∈ P})
    (he : (key default).1 = psuDag h (key default).1) :
    Nat.card (psuC3bg2_LocalF P ι A key) =
      Nat.card {u : F (key default) // ι (key default) (key default) he u * u = 1} :=
  card_localFamilies_unique (fun x y : {e // e ∈ P} => y.1 = psuDag h x.1) ι A key he

private lemma psuC3bg2_LocalF_pair {f n : ℕ} {K : Type} [Field K]
    {h : UnitaryFieldData 2 f K} (P : Finset (Matrix (Fin n) (Fin n) K))
    {F : {e // e ∈ P} → Type} [fieldF : ∀ e, Field (F e)]
    (ι : ∀ e e' : {e // e ∈ P}, e'.1 = psuDag h e.1 → (F e' ≃+* F e))
    (A : Type) (key : A → {e // e ∈ P}) (a b : A) (hne : a ≠ b)
    (hcover : ∀ x : A, x = a ∨ x = b)
    (hab : (key b).1 = psuDag h (key a).1) (hba : (key a).1 = psuDag h (key b).1)
    (hinv : ∀ (x y : A) (hxy : (key y).1 = psuDag h (key x).1)
      (hyx : (key x).1 = psuDag h (key y).1),
      ι (key y) (key x) hyx = (ι (key x) (key y) hxy).symm)
    (hfix : ∀ x : A, (key x).1 ≠ psuDag h (key x).1) :
    Nat.card (psuC3bg2_LocalF P ι A key) = Nat.card (F (key a)) - 1 :=
  card_localFamilies_pair (fun x y : {e // e ∈ P} => y.1 = psuDag h x.1) ι A key a b hne hcover hab hba hinv hfix

private lemma psuC3g2g2_kind_zero {f n : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K)
    (X B : GL (Fin n) K) (e : Matrix (Fin n) (Fin n) K) (hk : psuKind h X B e = 0) :
    psuDag h e = e ∧ psuPsi h X e = e := by
  unfold psuKind at hk
  by_cases hd : psuDag h e = e
  · rw [if_pos hd] at hk
    by_cases hp : psuPsi h X e = e
    · exact ⟨hd, hp⟩
    · rw [if_neg hp] at hk; omega
  · rw [if_neg hd] at hk
    by_cases hp : psuPsi h X e = e
    · rw [if_pos hp] at hk
      by_cases ht : psuPsiTrivial h X B e
      · rw [if_pos ht] at hk; omega
      · rw [if_neg ht] at hk; omega
    · rw [if_neg hp] at hk
      by_cases h4 : psuPsi h X e = psuDag h e
      · rw [if_pos h4] at hk; omega
      · rw [if_neg h4] at hk; omega

private lemma psuC3g2g2_kind_one {f n : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K)
    (X B : GL (Fin n) K) (e : Matrix (Fin n) (Fin n) K) (hk : psuKind h X B e = 1) :
    psuDag h e = e ∧ psuPsi h X e ≠ e := by
  unfold psuKind at hk
  by_cases hd : psuDag h e = e
  · rw [if_pos hd] at hk
    by_cases hp : psuPsi h X e = e
    · rw [if_pos hp] at hk; omega
    · exact ⟨hd, hp⟩
  · rw [if_neg hd] at hk
    by_cases hp : psuPsi h X e = e
    · rw [if_pos hp] at hk
      by_cases ht : psuPsiTrivial h X B e
      · rw [if_pos ht] at hk; omega
      · rw [if_neg ht] at hk; omega
    · rw [if_neg hp] at hk
      by_cases h4 : psuPsi h X e = psuDag h e
      · rw [if_pos h4] at hk; omega
      · rw [if_neg h4] at hk; omega

private lemma psuC3g2g2_kind_ge_two_dag_ne {f n : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData 2 f K) (X B : GL (Fin n) K) (e : Matrix (Fin n) (Fin n) K)
    (hk : 2 ≤ psuKind h X B e) : psuDag h e ≠ e := by
  intro hcon
  unfold psuKind at hk
  rw [if_pos hcon] at hk
  split_ifs at hk <;> omega

private lemma psuC3g2g2_kind_le_four_psi {f n : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData 2 f K) (X B : GL (Fin n) K) (e : Matrix (Fin n) (Fin n) K)
    (hk2 : 2 ≤ psuKind h X B e) (hk4 : psuKind h X B e ≤ 4) :
    psuPsi h X e = e ∨ psuPsi h X e = psuDag h e := by
  unfold psuKind at hk2 hk4
  by_cases hd : psuDag h e = e
  · rw [if_pos hd] at hk2
    split_ifs at hk2 <;> omega
  · rw [if_neg hd] at hk2 hk4
    by_cases hp : psuPsi h X e = e
    · exact Or.inl hp
    · rw [if_neg hp] at hk2 hk4
      by_cases h4 : psuPsi h X e = psuDag h e
      · exact Or.inr h4
      · rw [if_neg h4] at hk4; omega

private lemma psuC3g2g2_kind_five {f n : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K)
    (X B : GL (Fin n) K) (e : Matrix (Fin n) (Fin n) K) (hk : psuKind h X B e = 5) :
    psuDag h e ≠ e ∧ psuPsi h X e ≠ e ∧ psuPsi h X e ≠ psuDag h e := by
  unfold psuKind at hk
  by_cases hd : psuDag h e = e
  · rw [if_pos hd] at hk
    split_ifs at hk <;> omega
  · rw [if_neg hd] at hk
    by_cases hp : psuPsi h X e = e
    · rw [if_pos hp] at hk
      split_ifs at hk <;> omega
    · rw [if_neg hp] at hk
      by_cases h4 : psuPsi h X e = psuDag h e
      · rw [if_pos h4] at hk; omega
      · rw [if_neg h4] at hk
        exact ⟨hd, hp, h4⟩

private lemma psuC3g2g2_sqrt_cardF {f n : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData 2 f K) {B : GL (Fin n) K}
    (P : Finset (Matrix (Fin n) (Fin n) K))
    {F : {e // e ∈ P} → Type}
    (hcard : ∀ e, Nat.card (F e) = Nat.card K ^ blockDegree (psuAlg B) e.1)
    (e : {e // e ∈ P}) :
    Nat.sqrt (Nat.card (F e)) = (2 ^ f) ^ blockDegree (psuAlg B) e.1 := by
  rw [hcard e, h.card]
  have hsq : (2 ^ (2 * f)) ^ blockDegree (psuAlg B) e.1 =
      ((2 ^ f) ^ blockDegree (psuAlg B) e.1) ^ 2 := by
    calc (2 ^ (2 * f)) ^ blockDegree (psuAlg B) e.1
        = 2 ^ ((2 * f) * blockDegree (psuAlg B) e.1) := (pow_mul 2 (2 * f) _).symm
      _ = 2 ^ (f * (2 * blockDegree (psuAlg B) e.1)) := by congr 1; ring
      _ = (2 ^ f) ^ (2 * blockDegree (psuAlg B) e.1) := pow_mul 2 f _
      _ = ((2 ^ f) ^ blockDegree (psuAlg B) e.1) ^ 2 := by
            rw [show 2 * blockDegree (psuAlg B) e.1 =
              blockDegree (psuAlg B) e.1 * 2 from by ring, pow_mul]
  rw [hsq, Nat.sqrt_eq']

private lemma psuC3g2g2_cardF {f n : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData 2 f K) {B : GL (Fin n) K}
    (P : Finset (Matrix (Fin n) (Fin n) K))
    {F : {e // e ∈ P} → Type}
    (hcard : ∀ e, Nat.card (F e) = Nat.card K ^ blockDegree (psuAlg B) e.1)
    (e : {e // e ∈ P}) :
    Nat.card (F e) = (2 ^ f) ^ (2 * blockDegree (psuAlg B) e.1) := by
  rw [hcard e, h.card, ← pow_mul, ← pow_mul]
  congr 1
  ring

private lemma psuC3g2g2_F1O_zero (q d : ℕ) : psuC3b_F1O q d 0 = q ^ d + 1 := by
  simp [psuC3b_F1O]

private lemma psuC3g2g2_F1O_one (q d : ℕ) : psuC3b_F1O q d 1 = (q ^ d + 1) ^ 2 := by
  simp [psuC3b_F1O]

private lemma psuC3g2g2_F1O_five (q d : ℕ) : psuC3b_F1O q d 5 = (q ^ (2 * d) - 1) ^ 2 := by
  simp [psuC3b_F1O]

private lemma psuC3g2g2_F1O_mid (q d k : ℕ) (h0 : k ≠ 0) (h1 : k ≠ 1) (h5 : k ≠ 5) :
    psuC3b_F1O q d k = q ^ (2 * d) - 1 := by
  simp [psuC3b_F1O, h0, h1, h5]

private lemma psuC3g2g2_LocalF_unique_at {f n : ℕ} {K : Type} [Field K]
    {h : UnitaryFieldData 2 f K} (P : Finset (Matrix (Fin n) (Fin n) K))
    {F : {e // e ∈ P} → Type} [fieldF : ∀ e, Field (F e)]
    (ι : ∀ e e' : {e // e ∈ P}, e'.1 = psuDag h e.1 → (F e' ≃+* F e))
    (A : Type) (star : A) (huniq : ∀ x : A, x = star)
    (key : A → {e // e ∈ P})
    (he : (key star).1 = psuDag h (key star).1) :
    Nat.card (psuC3bg2_LocalF P ι A key) =
      Nat.card {u : F (key star) // ι (key star) (key star) he u * u = 1} := by
  letI : Unique A := { default := star, uniq := huniq }
  exact psuC3bg2_LocalF_unique P ι A key he

private lemma psuC3g2g2_kind234_dag_ne {f n : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData 2 f K) (X : GL (Fin n) K) {r x : Matrix (Fin n) (Fin n) K}
    (hd : psuDag h r ≠ r) (hpsi : psuPsi h X r = r ∨ psuPsi h X r = psuDag h r)
    (hx : x ∈ psuC3b_orbit h X r) : psuDag h x ≠ x := by
  have hdr : r ≠ psuDag h r := fun hc => hd hc.symm
  simp only [psuC3b_orbit, Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx with h | h | h | h
  · rw [h]; exact hd
  · rw [h, psuDag_dag]; exact hdr
  · rcases hpsi with hp | hp
    · rw [h, hp]; exact hd
    · rw [h, hp, psuDag_dag]; exact hdr
  · rcases hpsi with hp | hp
    · rw [h, hp, psuDag_dag]; exact hdr
    · rw [h, hp]; exact fun hc => hd (by simpa [psuDag_dag] using hc)

private lemma psuC3bg2_tau_facts {f n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    {h : UnitaryFieldData 2 f K} {X B : GL (Fin n) K} (S : PSUGraphSetting h n X B)
    (P : Finset (Matrix (Fin n) (Fin n) K))
    {F : {e // e ∈ P} → Type} [fieldF : ∀ e, Field (F e)]
    [algF : ∀ e, Algebra K (F e)]
    (π : ∀ e, psuAlg B →ₐ[K] F e) (hπ : ∀ e, Function.Surjective (π e))
    (ι : ∀ e e' : {e // e ∈ P}, e'.1 = psuDag h e.1 → (F e' ≃+* F e))
    (hι : ∀ (a : psuAlg B) (e e' : {e // e ∈ P}) (he : e'.1 = psuDag h e.1),
      π e ⟨psuDag h (a : Matrix (Fin n) (Fin n) K), (psuGraph_star_mem S a.1 a.2).1⟩ =
        ι e e' he (π e' a))
    (e : {e // e ∈ P}) (he : e.1 = psuDag h e.1) :
    (∀ t, ι e e he (ι e e he t) = t) ∧ ∃ t, ι e e he t ≠ t := by
  constructor
  · intro t
    obtain ⟨a, rfl⟩ := hπ e t
    have h1 : ι e e he (π e a) = π e ⟨psuDag h (a : Matrix (Fin n) (Fin n) K),
        (psuGraph_star_mem S a.1 a.2).1⟩ := (hι a e e he).symm
    have h2 : ι e e he (π e ⟨psuDag h (a : Matrix (Fin n) (Fin n) K),
          (psuGraph_star_mem S a.1 a.2).1⟩) = π e a := by
      rw [← hι ⟨psuDag h (a : Matrix (Fin n) (Fin n) K),
        (psuGraph_star_mem S a.1 a.2).1⟩ e e he]
      congr 1
      apply Subtype.ext
      exact psuDag_dag h (a : Matrix (Fin n) (Fin n) K)
    rw [h1, h2]
  · obtain ⟨c, hc⟩ := h.exists_bar_ne
    let a0 : psuAlg B := algebraMap K (psuAlg B) c
    refine ⟨π e a0, fun hcon => hc ?_⟩
    have hdag_scalar : (⟨psuDag h ((a0 : psuAlg B) : Matrix (Fin n) (Fin n) K),
        (psuGraph_star_mem S a0.1 a0.2).1⟩ : psuAlg B) =
        algebraMap K (psuAlg B) (h.bar c) := by
      apply Subtype.ext
      change psuDag h ((a0 : psuAlg B) : Matrix (Fin n) (Fin n) K) =
        algebraMap K (Matrix (Fin n) (Fin n) K) (h.bar c)
      have ha0 : ((a0 : psuAlg B) : Matrix (Fin n) (Fin n) K) = c • 1 := by
        change algebraMap K (Matrix (Fin n) (Fin n) K) c = c • 1
        rw [Algebra.algebraMap_eq_smul_one]
      rw [ha0, psuDag_smul, psuDag_one, Algebra.algebraMap_eq_smul_one]
    rw [← hι a0 e e he] at hcon
    rw [hdag_scalar] at hcon
    rw [(π e).commutes (h.bar c), (π e).commutes c] at hcon
    exact (algebraMap K (F e)).injective hcon

private lemma psuC3bg2_local_kind0 {f n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    {h : UnitaryFieldData 2 f K} {X B : GL (Fin n) K} (S : PSUGraphSetting h n X B)
    (P : Finset (Matrix (Fin n) (Fin n) K)) (hP : PrimFamily (psuAlg B) P)
    (R : Finset (Matrix (Fin n) (Fin n) K)) (hR : R ⊆ P)
    {F : {e // e ∈ P} → Type} [fieldF : ∀ e, Field (F e)]
    [algF : ∀ e, Algebra K (F e)] [finF : ∀ e, Finite (F e)]
    (π : ∀ e, psuAlg B →ₐ[K] F e) (hπ : ∀ e, Function.Surjective (π e))
    (hcard : ∀ e, Nat.card (F e) = Nat.card K ^ blockDegree (psuAlg B) e.1)
    (ι : ∀ e e' : {e // e ∈ P}, e'.1 = psuDag h e.1 → (F e' ≃+* F e))
    (hι : ∀ (a : psuAlg B) (e e' : {e // e ∈ P}) (he : e'.1 = psuDag h e.1),
      π e ⟨psuDag h (a : Matrix (Fin n) (Fin n) K), (psuGraph_star_mem S a.1 a.2).1⟩ =
        ι e e' he (π e' a))
    (r : {r // r ∈ R}) (hk : psuKind h X B r.1 = 0) :
    Nat.card (psuC3bg2_Local S P R hP ι r) =
      psuC3b_F1O (2 ^ f) (blockDegree (psuAlg B) r.1) 0 := by
  classical
  obtain ⟨hdag, hpsi⟩ := psuC3g2g2_kind_zero h X B r.1 hk
  let e0 : {e // e ∈ P} := ⟨r.1, hR r.2⟩
  have he0 : e0.1 = psuDag h e0.1 := hdag.symm
  let star : psuC3bg2_fiber h X P R r := ⟨e0, psuC3b_orbit_self h X r.1⟩
  have huniq : ∀ x : psuC3bg2_fiber h X P R r, x = star := by
    intro x
    apply Subtype.ext
    apply Subtype.ext
    have hx : x.1.1 ∈ psuC3b_orbit h X r.1 := x.2
    simp only [psuC3b_orbit, Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with h | h | h | h
    · exact h
    · rw [h, hdag]
    · rw [h, hpsi]
    · rw [h, hpsi, hdag]
  rw [psuC3bg2_Local_card_eq S P hP R ι r,
    psuC3g2g2_LocalF_unique_at P ι (psuC3bg2_fiber h X P R r) star huniq (fun x => x.1) he0,
    psuC3b_field_unitary_card (ι e0 e0 he0)
      (psuC3bg2_tau_facts S P π hπ ι hι e0 he0).1
      (psuC3bg2_tau_facts S P π hπ ι hι e0 he0).2,
    psuC3g2g2_sqrt_cardF h P hcard e0]
  rw [psuC3g2g2_F1O_zero]

private lemma psuC3bg2_local_kind1 {f n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    {h : UnitaryFieldData 2 f K} {X B : GL (Fin n) K} (S : PSUGraphSetting h n X B)
    (P : Finset (Matrix (Fin n) (Fin n) K)) (hP : PrimFamily (psuAlg B) P)
    (R : Finset (Matrix (Fin n) (Fin n) K)) (hR : R ⊆ P)
    {F : {e // e ∈ P} → Type} [fieldF : ∀ e, Field (F e)]
    [algF : ∀ e, Algebra K (F e)] [finF : ∀ e, Finite (F e)]
    (π : ∀ e, psuAlg B →ₐ[K] F e) (hπ : ∀ e, Function.Surjective (π e))
    (hcard : ∀ e, Nat.card (F e) = Nat.card K ^ blockDegree (psuAlg B) e.1)
    (ι : ∀ e e' : {e // e ∈ P}, e'.1 = psuDag h e.1 → (F e' ≃+* F e))
    (hι : ∀ (a : psuAlg B) (e e' : {e // e ∈ P}) (he : e'.1 = psuDag h e.1),
      π e ⟨psuDag h (a : Matrix (Fin n) (Fin n) K), (psuGraph_star_mem S a.1 a.2).1⟩ =
        ι e e' he (π e' a))
    (r : {r // r ∈ R}) (hk : psuKind h X B r.1 = 1) :
    Nat.card (psuC3bg2_Local S P R hP ι r) =
      psuC3b_F1O (2 ^ f) (blockDegree (psuAlg B) r.1) 1 := by
  classical
  obtain ⟨hdag, hpsi_ne⟩ := psuC3g2g2_kind_one h X B r.1 hk
  have hdpsi : psuDag h (psuPsi h X r.1) = psuPsi h X r.1 := by
    rw [psuC3b_dag_psi S r.1, hdag]
  let A := psuC3bg2_fiber h X P R r
  let e0 : {e // e ∈ P} := ⟨r.1, hR r.2⟩
  let e1 : {e // e ∈ P} := ⟨psuPsi h X r.1,
    (psuC3b_star_mem_of_primFamily S P hP r.1 (hR r.2)).2⟩
  have he0 : e0.1 = psuDag h e0.1 := hdag.symm
  have he1 : e1.1 = psuDag h e1.1 := hdpsi.symm
  let p : A → Prop := fun x => x.1.1 = r.1
  have hdagfix : ∀ x : A, psuDag h x.1.1 = x.1.1 := by
    intro x
    have hx : x.1.1 ∈ psuC3b_orbit h X r.1 := x.2
    simp only [psuC3b_orbit, Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with h | h | h | h
    · rw [h, hdag]
    · rw [h, psuDag_dag, hdag]
    · rw [h, hdpsi]
    · rw [h, psuDag_dag, hdpsi]
  have hp : ∀ x y : A, ((fun z : A => z.1) y).1 = psuDag h ((fun z : A => z.1) x).1 →
      (p x ↔ p y) := by
    intro x y hxy
    rw [hdagfix x] at hxy
    change (x.1.1 = r.1) ↔ (y.1.1 = r.1)
    rw [hxy]
  let star0 : {x : A // p x} := ⟨⟨e0, psuC3b_orbit_self h X r.1⟩, rfl⟩
  let star1 : {x : A // ¬ p x} :=
    ⟨⟨e1, psuC3b_orbit_psi_mem S (psuC3b_orbit_self h X r.1)⟩, hpsi_ne⟩
  have huniq0 : ∀ x : {x : A // p x}, x = star0 := by
    intro x
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    exact x.2
  have huniq1 : ∀ x : {x : A // ¬ p x}, x = star1 := by
    intro x
    have hx : x.1.1.1 ∈ psuC3b_orbit h X r.1 := x.1.2
    have hnp : x.1.1.1 ≠ r.1 := x.2
    simp only [psuC3b_orbit, Finset.mem_insert, Finset.mem_singleton] at hx
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    rcases hx with h | h | h | h
    · exact (hnp h).elim
    · exact (hnp (by rw [h, hdag])).elim
    · exact h
    · rw [h, hdpsi]
  have hinv := psuGraph_orbit_invariant S P hP r.1 (hR r.2)
  rw [psuC3bg2_Local_card_eq S P hP R ι r,
    psuC3bg2_LocalF_split P ι A (fun z : A => z.1) p hp,
    psuC3g2g2_LocalF_unique_at P ι {x : A // p x} star0 huniq0
      (fun z : {x : A // p x} => z.1.1) he0,
    psuC3g2g2_LocalF_unique_at P ι {x : A // ¬ p x} star1 huniq1
      (fun z : {x : A // ¬ p x} => z.1.1) he1,
    psuC3b_field_unitary_card (ι e0 e0 he0)
      (psuC3bg2_tau_facts S P π hπ ι hι e0 he0).1
      (psuC3bg2_tau_facts S P π hπ ι hι e0 he0).2,
    psuC3b_field_unitary_card (ι e1 e1 he1)
      (psuC3bg2_tau_facts S P π hπ ι hι e1 he1).1
      (psuC3bg2_tau_facts S P π hπ ι hι e1 he1).2,
    psuC3g2g2_sqrt_cardF h P hcard e0,
    psuC3g2g2_sqrt_cardF h P hcard e1,
    show blockDegree (psuAlg B) e0.1 = blockDegree (psuAlg B) r.1 from rfl,
    show blockDegree (psuAlg B) e1.1 = blockDegree (psuAlg B) r.1 from hinv.2.2.2,
    psuC3g2g2_F1O_one]
  ring

private lemma psuC3bg2_local_kind234 {f n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    {h : UnitaryFieldData 2 f K} {X B : GL (Fin n) K} (S : PSUGraphSetting h n X B)
    (P : Finset (Matrix (Fin n) (Fin n) K)) (hP : PrimFamily (psuAlg B) P)
    (R : Finset (Matrix (Fin n) (Fin n) K)) (hR : R ⊆ P)
    {F : {e // e ∈ P} → Type} [fieldF : ∀ e, Field (F e)]
    [algF : ∀ e, Algebra K (F e)] [finF : ∀ e, Finite (F e)] [charF : ∀ e, CharP (F e) 2]
    (π : ∀ e, psuAlg B →ₐ[K] F e) (hπ : ∀ e, Function.Surjective (π e))
    (hcard : ∀ e, Nat.card (F e) = Nat.card K ^ blockDegree (psuAlg B) e.1)
    (ι : ∀ e e' : {e // e ∈ P}, e'.1 = psuDag h e.1 → (F e' ≃+* F e))
    (hι : ∀ (a : psuAlg B) (e e' : {e // e ∈ P}) (he : e'.1 = psuDag h e.1),
      π e ⟨psuDag h (a : Matrix (Fin n) (Fin n) K), (psuGraph_star_mem S a.1 a.2).1⟩ =
        ι e e' he (π e' a))
    (r : {r // r ∈ R}) (hk2 : 2 ≤ psuKind h X B r.1) (hk4 : psuKind h X B r.1 ≤ 4) :
    Nat.card (psuC3bg2_Local S P R hP ι r) =
      psuC3b_F1O (2 ^ f) (blockDegree (psuAlg B) r.1) (psuKind h X B r.1) := by
  classical
  have hd : psuDag h r.1 ≠ r.1 := psuC3g2g2_kind_ge_two_dag_ne h X B r.1 hk2
  have hpsi : psuPsi h X r.1 = r.1 ∨ psuPsi h X r.1 = psuDag h r.1 :=
    psuC3g2g2_kind_le_four_psi h X B r.1 hk2 hk4
  let A := psuC3bg2_fiber h X P R r
  let a : A := ⟨⟨r.1, hR r.2⟩, psuC3b_orbit_self h X r.1⟩
  let b : A := ⟨⟨psuDag h r.1, (psuC3b_star_mem_of_primFamily S P hP r.1 (hR r.2)).1⟩,
    psuC3b_orbit_dag_mem (psuC3b_orbit_self h X r.1)⟩
  have hne : a ≠ b := by
    intro hab
    have h1 : r.1 = psuDag h r.1 := by
      have h2 := congrArg (fun x : A => x.1.1) hab
      simpa [a, b] using h2
    exact hd h1.symm
  have hcover : ∀ x : A, x = a ∨ x = b := by
    intro x
    have hx : x.1.1 ∈ psuC3b_orbit h X r.1 := x.2
    simp only [psuC3b_orbit, Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with h | h | h | h
    · left; apply Subtype.ext; apply Subtype.ext; exact h
    · right; apply Subtype.ext; apply Subtype.ext; exact h
    · rcases hpsi with hp | hp
      · left; apply Subtype.ext; apply Subtype.ext; rw [h, hp]
      · right; apply Subtype.ext; apply Subtype.ext; rw [h, hp]
    · rcases hpsi with hp | hp
      · right; apply Subtype.ext; apply Subtype.ext; rw [h, hp]
      · left; apply Subtype.ext; apply Subtype.ext; rw [h, hp, psuDag_dag]
  have hab : ((fun z : A => z.1) b).1 = psuDag h ((fun z : A => z.1) a).1 := rfl
  have hba : ((fun z : A => z.1) a).1 = psuDag h ((fun z : A => z.1) b).1 := by
    change r.1 = psuDag h (psuDag h r.1)
    rw [psuDag_dag]
  have hinv : ∀ (x y : A)
      (hxy : ((fun z : A => z.1) y).1 = psuDag h ((fun z : A => z.1) x).1)
      (hyx : ((fun z : A => z.1) x).1 = psuDag h ((fun z : A => z.1) y).1),
      ι ((fun z : A => z.1) y) ((fun z : A => z.1) x) hyx =
        (ι ((fun z : A => z.1) x) ((fun z : A => z.1) y) hxy).symm :=
    fun x y hxy hyx => psuC3bg2_iota_inv S P π hπ ι hι hxy hyx
  have hfix : ∀ x : A, ((fun z : A => z.1) x).1 ≠ psuDag h (((fun z : A => z.1) x).1) :=
    fun x => (psuC3g2g2_kind234_dag_ne h X hd hpsi x.2).symm
  rw [psuC3bg2_Local_card_eq S P hP R ι r,
    psuC3bg2_LocalF_pair P ι A (fun z : A => z.1) a b hne hcover hab hba hinv hfix,
    psuC3g2g2_cardF h P hcard ((fun z : A => z.1) a)]
  have hk0 : psuKind h X B r.1 ≠ 0 := by omega
  have hk1 : psuKind h X B r.1 ≠ 1 := by omega
  have hk5 : psuKind h X B r.1 ≠ 5 := by omega
  rw [psuC3g2g2_F1O_mid (2 ^ f) (blockDegree (psuAlg B) r.1) (psuKind h X B r.1)
    hk0 hk1 hk5]

private lemma psuC3bg2_local_kind5 {f n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    {h : UnitaryFieldData 2 f K} {X B : GL (Fin n) K} (S : PSUGraphSetting h n X B)
    (P : Finset (Matrix (Fin n) (Fin n) K)) (hP : PrimFamily (psuAlg B) P)
    (R : Finset (Matrix (Fin n) (Fin n) K)) (hR : R ⊆ P)
    {F : {e // e ∈ P} → Type} [fieldF : ∀ e, Field (F e)]
    [algF : ∀ e, Algebra K (F e)] [finF : ∀ e, Finite (F e)] [charF : ∀ e, CharP (F e) 2]
    (π : ∀ e, psuAlg B →ₐ[K] F e) (hπ : ∀ e, Function.Surjective (π e))
    (hcard : ∀ e, Nat.card (F e) = Nat.card K ^ blockDegree (psuAlg B) e.1)
    (ι : ∀ e e' : {e // e ∈ P}, e'.1 = psuDag h e.1 → (F e' ≃+* F e))
    (hι : ∀ (a : psuAlg B) (e e' : {e // e ∈ P}) (he : e'.1 = psuDag h e.1),
      π e ⟨psuDag h (a : Matrix (Fin n) (Fin n) K), (psuGraph_star_mem S a.1 a.2).1⟩ =
        ι e e' he (π e' a))
    (r : {r // r ∈ R}) (hk : psuKind h X B r.1 = 5) :
    Nat.card (psuC3bg2_Local S P R hP ι r) =
      psuC3b_F1O (2 ^ f) (blockDegree (psuAlg B) r.1) 5 := by
  classical
  obtain ⟨hd, hp, h4⟩ := psuC3g2g2_kind_five h X B r.1 hk
  have hdag_psi : psuDag h (psuPsi h X r.1) = psuPsi h X (psuDag h r.1) :=
    psuC3b_dag_psi S r.1
  have ddn : psuDag h (psuPsi h X r.1) ≠ r.1 := by
    intro hc
    have h2 : psuPsi h X (psuDag h r.1) = r.1 := by rw [← hdag_psi]; exact hc
    have h3 := congrArg (psuPsi h X) h2
    rw [psuPsi_psi h X S.X_mem S.X_sq (psuDag h r.1)] at h3
    exact h4 h3.symm
  have ddm : psuDag h (psuPsi h X r.1) ≠ psuDag h r.1 := by
    intro hc
    have h3 := congrArg (psuDag h) hc
    rw [psuDag_dag, psuDag_dag] at h3
    exact hp h3
  have hne2' : psuPsi h X r.1 ≠ psuDag h (psuPsi h X r.1) := by
    intro h2
    rw [hdag_psi] at h2
    have h3 := congrArg (psuPsi h X) h2
    rw [psuPsi_psi h X S.X_mem S.X_sq r.1,
      psuPsi_psi h X S.X_mem S.X_sq (psuDag h r.1)] at h3
    exact hd h3.symm
  let A := psuC3bg2_fiber h X P R r
  let a : A := ⟨⟨r.1, hR r.2⟩, psuC3b_orbit_self h X r.1⟩
  let b : A := ⟨⟨psuDag h r.1, (psuC3b_star_mem_of_primFamily S P hP r.1 (hR r.2)).1⟩,
    psuC3b_orbit_dag_mem (psuC3b_orbit_self h X r.1)⟩
  let c : A := ⟨⟨psuPsi h X r.1, (psuC3b_star_mem_of_primFamily S P hP r.1 (hR r.2)).2⟩,
    psuC3b_orbit_psi_mem S (psuC3b_orbit_self h X r.1)⟩
  let d : A := ⟨⟨psuDag h (psuPsi h X r.1),
    (psuC3b_star_mem_of_primFamily S P hP (psuPsi h X r.1)
      ((psuC3b_star_mem_of_primFamily S P hP r.1 (hR r.2)).2)).1⟩,
    psuC3b_orbit_dag_mem (psuC3b_orbit_psi_mem S (psuC3b_orbit_self h X r.1))⟩
  let p : A → Prop := fun x => x.1.1 = r.1 ∨ x.1.1 = psuDag h r.1
  have notp_c : ¬ p c := by
    change ¬ (psuPsi h X r.1 = r.1 ∨ psuPsi h X r.1 = psuDag h r.1)
    exact not_or.mpr ⟨hp, h4⟩
  have notp_d : ¬ p d := by
    change ¬ (psuDag h (psuPsi h X r.1) = r.1 ∨
      psuDag h (psuPsi h X r.1) = psuDag h r.1)
    exact not_or.mpr ⟨ddn, ddm⟩
  have hp_inv : ∀ x y : A, ((fun z : A => z.1) y).1 = psuDag h ((fun z : A => z.1) x).1 →
      (p x ↔ p y) := by
    intro x y hxy
    have hx : x.1.1 ∈ psuC3b_orbit h X r.1 := x.2
    have hiff : (x.1.1 = r.1 ∨ x.1.1 = psuDag h r.1) ↔
        (psuDag h x.1.1 = r.1 ∨ psuDag h x.1.1 = psuDag h r.1) := by
      simp only [psuC3b_orbit, Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with hm | hm | hm | hm
      · rw [hm]; constructor
        · intro _; exact Or.inr rfl
        · intro _; exact Or.inl rfl
      · rw [hm]; constructor
        · intro _; exact Or.inl (psuDag_dag h r.1)
        · intro _; exact Or.inr rfl
      · rw [hm]; constructor
        · intro hh; exact hh.elim (fun hc => (hp hc).elim) (fun hc => (h4 hc).elim)
        · intro hh; exact hh.elim (fun hc => (ddn hc).elim) (fun hc => (ddm hc).elim)
      · rw [hm]
        simp only [psuDag_dag]
        constructor
        · intro hh; exact hh.elim (fun hc => (ddn hc).elim) (fun hc => (ddm hc).elim)
        · intro hh; exact hh.elim (fun hc => (hp hc).elim) (fun hc => (h4 hc).elim)
    change (x.1.1 = r.1 ∨ x.1.1 = psuDag h r.1) ↔
      (y.1.1 = r.1 ∨ y.1.1 = psuDag h r.1)
    rw [hxy]
    exact hiff
  let star1 : {x : A // p x} := ⟨a, Or.inl rfl⟩
  let star1b : {x : A // p x} := ⟨b, Or.inr rfl⟩
  let star2 : {x : A // ¬ p x} := ⟨c, notp_c⟩
  let star2b : {x : A // ¬ p x} := ⟨d, notp_d⟩
  have hne1 : star1 ≠ star1b := by
    intro hh
    have h2 := congrArg (fun z : {x : A // p x} => z.1.1.1) hh
    have h3 : r.1 = psuDag h r.1 := by simpa [star1, star1b, a, b] using h2
    exact hd h3.symm
  have hne2 : star2 ≠ star2b := by
    intro hh
    have h2 := congrArg (fun z : {x : A // ¬ p x} => z.1.1.1) hh
    exact hne2' (by simpa [star2, star2b, c, d] using h2)
  have hcover1 : ∀ x : {x : A // p x}, x = star1 ∨ x = star1b := by
    intro x
    rcases x.2 with h | h
    · left; apply Subtype.ext; apply Subtype.ext; apply Subtype.ext; exact h
    · right; apply Subtype.ext; apply Subtype.ext; apply Subtype.ext; exact h
  have hcover2 : ∀ x : {x : A // ¬ p x}, x = star2 ∨ x = star2b := by
    intro x
    have hx : x.1.1.1 ∈ psuC3b_orbit h X r.1 := x.1.2
    have hnp : ¬ (x.1.1.1 = r.1 ∨ x.1.1.1 = psuDag h r.1) := x.2
    simp only [psuC3b_orbit, Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with h | h | h | h
    · exact (hnp (Or.inl h)).elim
    · exact (hnp (Or.inr h)).elim
    · left; apply Subtype.ext; apply Subtype.ext; apply Subtype.ext; exact h
    · right; apply Subtype.ext; apply Subtype.ext; apply Subtype.ext; exact h
  have hab1 : ((fun z : {x : A // p x} => z.1.1) star1b).1 =
      psuDag h ((fun z : {x : A // p x} => z.1.1) star1).1 := rfl
  have hba1 : ((fun z : {x : A // p x} => z.1.1) star1).1 =
      psuDag h ((fun z : {x : A // p x} => z.1.1) star1b).1 := by
    change r.1 = psuDag h (psuDag h r.1)
    rw [psuDag_dag]
  have hinv1 : ∀ (x y : {x : A // p x})
      (hxy : ((fun z : {x : A // p x} => z.1.1) y).1 =
        psuDag h ((fun z : {x : A // p x} => z.1.1) x).1)
      (hyx : ((fun z : {x : A // p x} => z.1.1) x).1 =
        psuDag h ((fun z : {x : A // p x} => z.1.1) y).1),
      ι ((fun z : {x : A // p x} => z.1.1) y)
          ((fun z : {x : A // p x} => z.1.1) x) hyx =
        (ι ((fun z : {x : A // p x} => z.1.1) x)
          ((fun z : {x : A // p x} => z.1.1) y) hxy).symm :=
    fun x y hxy hyx => psuC3bg2_iota_inv S P π hπ ι hι hxy hyx
  have hfix1 : ∀ x : {x : A // p x},
      ((fun z : {x : A // p x} => z.1.1) x).1 ≠
        psuDag h (((fun z : {x : A // p x} => z.1.1) x).1) := by
    intro x
    rcases x.2 with h | h
    · rw [h]; exact fun hc => hd hc.symm
    · rw [h]; exact fun hc => hd (by simpa [psuDag_dag] using hc)
  have hab2 : ((fun z : {x : A // ¬ p x} => z.1.1) star2b).1 =
      psuDag h ((fun z : {x : A // ¬ p x} => z.1.1) star2).1 := rfl
  have hba2 : ((fun z : {x : A // ¬ p x} => z.1.1) star2).1 =
      psuDag h ((fun z : {x : A // ¬ p x} => z.1.1) star2b).1 := by
    change psuPsi h X r.1 = psuDag h (psuDag h (psuPsi h X r.1))
    rw [psuDag_dag]
  have hinv2 : ∀ (x y : {x : A // ¬ p x})
      (hxy : ((fun z : {x : A // ¬ p x} => z.1.1) y).1 =
        psuDag h ((fun z : {x : A // ¬ p x} => z.1.1) x).1)
      (hyx : ((fun z : {x : A // ¬ p x} => z.1.1) x).1 =
        psuDag h ((fun z : {x : A // ¬ p x} => z.1.1) y).1),
      ι ((fun z : {x : A // ¬ p x} => z.1.1) y)
          ((fun z : {x : A // ¬ p x} => z.1.1) x) hyx =
        (ι ((fun z : {x : A // ¬ p x} => z.1.1) x)
          ((fun z : {x : A // ¬ p x} => z.1.1) y) hxy).symm :=
    fun x y hxy hyx => psuC3bg2_iota_inv S P π hπ ι hι hxy hyx
  have hfix2 : ∀ x : {x : A // ¬ p x},
      ((fun z : {x : A // ¬ p x} => z.1.1) x).1 ≠
        psuDag h (((fun z : {x : A // ¬ p x} => z.1.1) x).1) := by
    intro x
    have hx : x.1.1.1 ∈ psuC3b_orbit h X r.1 := x.1.2
    have hnp : ¬ (x.1.1.1 = r.1 ∨ x.1.1.1 = psuDag h r.1) := x.2
    simp only [psuC3b_orbit, Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with h | h | h | h
    · exact (hnp (Or.inl h)).elim
    · exact (hnp (Or.inr h)).elim
    · rw [h]; exact hne2'
    · rw [h, psuDag_dag]; exact fun hc => hne2' hc.symm
  have hinv := psuGraph_orbit_invariant S P hP r.1 (hR r.2)
  rw [psuC3bg2_Local_card_eq S P hP R ι r,
    psuC3bg2_LocalF_split P ι A (fun z : A => z.1) p hp_inv,
    psuC3bg2_LocalF_pair P ι {x : A // p x} (fun z => z.1.1) star1 star1b hne1 hcover1
      hab1 hba1 hinv1 hfix1,
    psuC3bg2_LocalF_pair P ι {x : A // ¬ p x} (fun z => z.1.1) star2 star2b hne2 hcover2
      hab2 hba2 hinv2 hfix2,
    psuC3g2g2_cardF h P hcard star1.1.1,
    psuC3g2g2_cardF h P hcard star2.1.1,
    show blockDegree (psuAlg B) (star1.1.1).1 = blockDegree (psuAlg B) r.1 from rfl,
    show blockDegree (psuAlg B) (star2.1.1).1 = blockDegree (psuAlg B) r.1 from
      hinv.2.2.2,
    psuC3g2g2_F1O_five]
  ring

private lemma psuC3bg2_local_count {f n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    {h : UnitaryFieldData 2 f K} {X B : GL (Fin n) K} (S : PSUGraphSetting h n X B)
    (P : Finset (Matrix (Fin n) (Fin n) K)) (hP : PrimFamily (psuAlg B) P)
    (R : Finset (Matrix (Fin n) (Fin n) K)) (hR : R ⊆ P)
    {F : {e // e ∈ P} → Type} [fieldF : ∀ e, Field (F e)]
    [algF : ∀ e, Algebra K (F e)] [finF : ∀ e, Finite (F e)] [charF : ∀ e, CharP (F e) 2]
    (π : ∀ e, psuAlg B →ₐ[K] F e) (hπ : ∀ e, Function.Surjective (π e))
    (hcard : ∀ e, Nat.card (F e) = Nat.card K ^ blockDegree (psuAlg B) e.1)
    (ι : ∀ e e' : {e // e ∈ P}, e'.1 = psuDag h e.1 → (F e' ≃+* F e))
    (hι : ∀ (a : psuAlg B) (e e' : {e // e ∈ P}) (he : e'.1 = psuDag h e.1),
      π e ⟨psuDag h (a : Matrix (Fin n) (Fin n) K), (psuGraph_star_mem S a.1 a.2).1⟩ =
        ι e e' he (π e' a))
    (r : {r // r ∈ R}) :
    Nat.card (psuC3bg2_Local S P R hP ι r) =
      psuC3b_F1O (2 ^ f) (blockDegree (psuAlg B) r.1) (psuKind h X B r.1) := by
  have hle := psuC3b_kind_le h X B r.1
  rcases (by omega : psuKind h X B r.1 = 0 ∨ psuKind h X B r.1 = 1 ∨
      (2 ≤ psuKind h X B r.1 ∧ psuKind h X B r.1 ≤ 4) ∨ psuKind h X B r.1 = 5) with
    h0 | h1 | ⟨h2, h4⟩ | h5
  · rw [h0]; exact psuC3bg2_local_kind0 S P hP R hR π hπ hcard ι hι r h0
  · rw [h1]; exact psuC3bg2_local_kind1 S P hP R hR π hπ hcard ι hι r h1
  · exact psuC3bg2_local_kind234 S P hP R hR π hπ hcard ι hι r h2 h4
  · rw [h5]; exact psuC3bg2_local_kind5 S P hP R hR π hπ hcard ι hι r h5

private lemma psuC3bg2_W_card_split {f n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    {h : UnitaryFieldData 2 f K} {X B : GL (Fin n) K} (S : PSUGraphSetting h n X B)
    (P : Finset (Matrix (Fin n) (Fin n) K)) (hP : PrimFamily (psuAlg B) P)
    (R : Finset (Matrix (Fin n) (Fin n) K))
    (hrep : ∀ e ∈ P, ∃! r, r ∈ R ∧
      (r = e ∨ r = psuDag h e ∨ r = psuPsi h X e ∨ r = psuDag h (psuPsi h X e)))
    {F : {e // e ∈ P} → Type} [fieldF : ∀ e, Field (F e)]
    (ι : ∀ e e' : {e // e ∈ P}, e'.1 = psuDag h e.1 → (F e' ≃+* F e)) :
    Nat.card (psuC3bg2_W S P hP ι) =
      ∏ r : {r // r ∈ R}, Nat.card (psuC3bg2_Local S P R hP ι r) := by
  classical
  let ePi := psuC3bg2_piEquiv S P R hrep F
  have hpred : ∀ y : (e : {e // e ∈ P}) → F e,
      (∀ e : {e // e ∈ P}, psuC3bg2_ιA S P hP ι e (y (psuC3bg2_D S P hP e)) * y e = 1) ↔
        (∀ r : {r // r ∈ R}, psuC3bg2_LocalPred S P R hP ι r (ePi y r)) := by
    intro y
    constructor
    · intro h r e
      simpa [ePi, psuC3bg2_piEquiv, psuC3bg2_LocalPred] using h e.1
    · intro h e
      have h' := h (psuC3bg2_rep P R hrep e)
        ⟨e, psuC3bg2_rep_mem_orbit S P R hrep e⟩
      simpa [ePi, psuC3bg2_piEquiv, psuC3bg2_LocalPred] using h'
  let e1 : psuC3bg2_W S P hP ι ≃
      ((r : {r // r ∈ R}) →
        {z : (e : psuC3bg2_fiber h X P R r) → F e.1 //
          psuC3bg2_LocalPred S P R hP ι r z}) :=
    (Equiv.subtypeEquiv ePi hpred).trans
      (Equiv.subtypePiEquivPi (α := {r // r ∈ R})
        (β := fun r => (e : psuC3bg2_fiber h X P R r) → F e.1)
        (p := fun r z => psuC3bg2_LocalPred S P R hP ι r z))
  have hcard := Nat.card_congr e1
  rw [hcard]
  exact Nat.card_pi

private lemma psuC3b_F1_prod {f n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    {h : UnitaryFieldData 2 f K} {X B : GL (Fin n) K}
    (S : PSUGraphSetting h n X B) (P : Finset (Matrix (Fin n) (Fin n) K))
    (hP : PrimFamily (psuAlg B) P) (R : Finset (Matrix (Fin n) (Fin n) K)) (hR : R ⊆ P)
    (hrep : ∀ e ∈ P, ∃! r, r ∈ R ∧
      (r = e ∨ r = psuDag h e ∨ r = psuPsi h X e ∨ r = psuDag h (psuPsi h X e)))
    (F : {e // e ∈ P} → Type) [fieldF : ∀ e, Field (F e)]
    [algF : ∀ e, Algebra K (F e)] [finF : ∀ e, Finite (F e)] [charF : ∀ e, CharP (F e) 2]
    (π : ∀ e, psuAlg B →ₐ[K] F e) (hπ : ∀ e, Function.Surjective (π e))
    (hcard : ∀ e, Nat.card (F e) = Nat.card K ^ blockDegree (psuAlg B) e.1)
    (hbij : Function.Bijective (fun (a : psuAlg B) (e : {e // e ∈ P}) => π e a))
    (ι : ∀ e e' : {e // e ∈ P}, e'.1 = psuDag h e.1 → (F e' ≃+* F e))
    (hι : ∀ (a : psuAlg B) (e e' : {e // e ∈ P}) (he : e'.1 = psuDag h e.1),
      π e ⟨psuDag h (a : Matrix (Fin n) (Fin n) K), (psuGraph_star_mem S a.1 a.2).1⟩ =
        ι e e' he (π e' a)) :
    Nat.card (psuC3b_F1 h B) =
      ∏ r ∈ R, psuC3b_F1O (2 ^ f) (blockDegree (psuAlg B) r) (psuKind h X B r) := by
  classical
  rw [psuC3bg2_F1_card_bijection S P hP π ι hι hbij,
    psuC3bg2_W_card_split S P hP R hrep ι]
  rw [Finset.prod_subtype (s := R) (p := fun r => r ∈ R) (h := fun x => Iff.rfl)
    (f := fun r => psuC3b_F1O (2 ^ f) (blockDegree (psuAlg B) r) (psuKind h X B r))]
  apply Finset.prod_congr rfl
  intro r _
  exact psuC3bg2_local_count S P hP R hR π hπ hcard ι hι r

private noncomputable def psuC3bg3_dag {f n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    {h : UnitaryFieldData 2 f K} {X B : GL (Fin n) K} (S : PSUGraphSetting h n X B)
    (P : Finset (Matrix (Fin n) (Fin n) K)) (hP : PrimFamily (psuAlg B) P) :
    {e : Matrix (Fin n) (Fin n) K // e ∈ P} → {e : Matrix (Fin n) (Fin n) K // e ∈ P} :=
  fun e => ⟨psuDag h e.1, (psuC3b_star_mem_of_primFamily S P hP e.1 e.2).1⟩

private noncomputable def psuC3bg3_psi {f n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    {h : UnitaryFieldData 2 f K} {X B : GL (Fin n) K} (S : PSUGraphSetting h n X B)
    (P : Finset (Matrix (Fin n) (Fin n) K)) (hP : PrimFamily (psuAlg B) P) :
    {e : Matrix (Fin n) (Fin n) K // e ∈ P} → {e : Matrix (Fin n) (Fin n) K // e ∈ P} :=
  fun e => ⟨psuPsi h X e.1, (psuC3b_star_mem_of_primFamily S P hP e.1 e.2).2⟩

private noncomputable def psuC3bg3_dagA {f n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    {h : UnitaryFieldData 2 f K} {X B : GL (Fin n) K} (S : PSUGraphSetting h n X B)
    (t : psuAlg B) : psuAlg B :=
  ⟨psuDag h (t : Matrix (Fin n) (Fin n) K), (psuGraph_star_mem S t.1 t.2).1⟩

private noncomputable def psuC3bg3_psiA {f n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    {h : UnitaryFieldData 2 f K} {X B : GL (Fin n) K} (S : PSUGraphSetting h n X B)
    (t : psuAlg B) : psuAlg B :=
  ⟨psuPsi h X (t : Matrix (Fin n) (Fin n) K), (psuGraph_star_mem S t.1 t.2).2⟩

private lemma psuC3bg3_dagA_eq_one_iff {f n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    {h : UnitaryFieldData 2 f K} {X B : GL (Fin n) K} (S : PSUGraphSetting h n X B)
    (t : psuAlg B) :
    (psuC3bg3_dagA S t * t = 1) ↔
      (psuDag h (t : Matrix (Fin n) (Fin n) K) *
        (t : Matrix (Fin n) (Fin n) K) = 1) := by
  constructor
  · intro hh
    exact congrArg Subtype.val hh
  · intro hh
    exact Subtype.ext hh

private lemma psuC3bg3_psiA_eq_one_iff {f n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    {h : UnitaryFieldData 2 f K} {X B : GL (Fin n) K} (S : PSUGraphSetting h n X B)
    (t : psuAlg B) :
    (psuC3bg3_psiA S t * t = 1) ↔
      (psuPsi h X (t : Matrix (Fin n) (Fin n) K) *
        (t : Matrix (Fin n) (Fin n) K) = 1) := by
  constructor
  · intro hh
    exact congrArg Subtype.val hh
  · intro hh
    exact Subtype.ext hh

private lemma psuC3bg3_dag_eq_one_iff {f n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    {h : UnitaryFieldData 2 f K} {X B : GL (Fin n) K} (S : PSUGraphSetting h n X B)
    (P : Finset (Matrix (Fin n) (Fin n) K)) (hP : PrimFamily (psuAlg B) P)
    (F : {e : Matrix (Fin n) (Fin n) K // e ∈ P} → Type) [fieldF : ∀ e, Field (F e)]
    [algF : ∀ e, Algebra K (F e)]
    (π : ∀ e : {e : Matrix (Fin n) (Fin n) K // e ∈ P}, psuAlg B →ₐ[K] F e)
    (ι : ∀ e e' : {e : Matrix (Fin n) (Fin n) K // e ∈ P},
      e'.1 = psuDag h e.1 → (F e' ≃+* F e))
    (hι : ∀ (a : psuAlg B) (e e' : {e : Matrix (Fin n) (Fin n) K // e ∈ P})
      (he : e'.1 = psuDag h e.1),
      π e ⟨psuDag h (a : Matrix (Fin n) (Fin n) K), (psuGraph_star_mem S a.1 a.2).1⟩ =
        ι e e' he (π e' a))
    (hbij : Function.Bijective (fun (a : psuAlg B)
      (e : {e : Matrix (Fin n) (Fin n) K // e ∈ P}) => π e a)) (t : psuAlg B) :
    (psuC3bg3_dagA S t * t = 1) ↔
      ∀ e : {e : Matrix (Fin n) (Fin n) K // e ∈ P},
        ι e (psuC3bg3_dag S P hP e) rfl
          (π (psuC3bg3_dag S P hP e) t) * π e t = 1 := by
  constructor
  · intro hh e
    have hf : (fun e : {e : Matrix (Fin n) (Fin n) K // e ∈ P} =>
        π e (psuC3bg3_dagA S t * t)) = fun e => (1 : F e) := by
      have h1 := congrArg (fun a : psuAlg B =>
        fun e : {e : Matrix (Fin n) (Fin n) K // e ∈ P} => π e a) hh
      simpa using h1
    have he : π e (psuC3bg3_dagA S t * t) = 1 := congrFun hf e
    rw [map_mul] at he
    have hcoe : π e (psuC3bg3_dagA S t) =
        ι e (psuC3bg3_dag S P hP e) rfl (π (psuC3bg3_dag S P hP e) t) :=
      hι t e (psuC3bg3_dag S P hP e) rfl
    rw [hcoe] at he
    exact he
  · intro hh
    apply hbij.injective
    funext e
    change π e (psuC3bg3_dagA S t * t) = π e 1
    rw [map_mul]
    have hcoe : π e (psuC3bg3_dagA S t) =
        ι e (psuC3bg3_dag S P hP e) rfl (π (psuC3bg3_dag S P hP e) t) :=
      hι t e (psuC3bg3_dag S P hP e) rfl
    rw [hcoe, hh e, map_one]

private lemma psuC3bg3_psi_eq_one_iff {f n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    {h : UnitaryFieldData 2 f K} {X B : GL (Fin n) K} (S : PSUGraphSetting h n X B)
    (P : Finset (Matrix (Fin n) (Fin n) K)) (hP : PrimFamily (psuAlg B) P)
    (F : {e : Matrix (Fin n) (Fin n) K // e ∈ P} → Type) [fieldF : ∀ e, Field (F e)]
    [algF : ∀ e, Algebra K (F e)]
    (π : ∀ e : {e : Matrix (Fin n) (Fin n) K // e ∈ P}, psuAlg B →ₐ[K] F e)
    (Ψ : ∀ e e' : {e : Matrix (Fin n) (Fin n) K // e ∈ P},
      e'.1 = psuPsi h X e.1 → (F e' ≃+* F e))
    (hΨ : ∀ (a : psuAlg B) (e e' : {e : Matrix (Fin n) (Fin n) K // e ∈ P})
      (he : e'.1 = psuPsi h X e.1),
      π e ⟨psuPsi h X (a : Matrix (Fin n) (Fin n) K), (psuGraph_star_mem S a.1 a.2).2⟩ =
        Ψ e e' he (π e' a))
    (hbij : Function.Bijective (fun (a : psuAlg B)
      (e : {e : Matrix (Fin n) (Fin n) K // e ∈ P}) => π e a)) (t : psuAlg B) :
    (psuC3bg3_psiA S t * t = 1) ↔
      ∀ e : {e : Matrix (Fin n) (Fin n) K // e ∈ P},
        Ψ e (psuC3bg3_psi S P hP e) rfl
          (π (psuC3bg3_psi S P hP e) t) * π e t = 1 := by
  constructor
  · intro hh e
    have hf : (fun e : {e : Matrix (Fin n) (Fin n) K // e ∈ P} =>
        π e (psuC3bg3_psiA S t * t)) = fun e => (1 : F e) := by
      have h1 := congrArg (fun a : psuAlg B =>
        fun e : {e : Matrix (Fin n) (Fin n) K // e ∈ P} => π e a) hh
      simpa using h1
    have he : π e (psuC3bg3_psiA S t * t) = 1 := congrFun hf e
    rw [map_mul] at he
    have hcoe : π e (psuC3bg3_psiA S t) =
        Ψ e (psuC3bg3_psi S P hP e) rfl (π (psuC3bg3_psi S P hP e) t) :=
      hΨ t e (psuC3bg3_psi S P hP e) rfl
    rw [hcoe] at he
    exact he
  · intro hh
    apply hbij.injective
    funext e
    change π e (psuC3bg3_psiA S t * t) = π e 1
    rw [map_mul]
    have hcoe : π e (psuC3bg3_psiA S t) =
        Ψ e (psuC3bg3_psi S P hP e) rfl (π (psuC3bg3_psi S P hP e) t) :=
      hΨ t e (psuC3bg3_psi S P hP e) rfl
    rw [hcoe, hh e, map_one]

private def psuC3bg3_C1 {f n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    {h : UnitaryFieldData 2 f K} {X B : GL (Fin n) K} (S : PSUGraphSetting h n X B)
    (P : Finset (Matrix (Fin n) (Fin n) K)) (hP : PrimFamily (psuAlg B) P)
    (F : {e : Matrix (Fin n) (Fin n) K // e ∈ P} → Type) [fieldF : ∀ e, Field (F e)]
    (ι : ∀ e e' : {e : Matrix (Fin n) (Fin n) K // e ∈ P},
      e'.1 = psuDag h e.1 → (F e' ≃+* F e))
    (y : ∀ e : {e : Matrix (Fin n) (Fin n) K // e ∈ P}, F e) : Prop :=
  ∀ e : {e : Matrix (Fin n) (Fin n) K // e ∈ P},
    ι e (psuC3bg3_dag S P hP e) rfl (y (psuC3bg3_dag S P hP e)) * y e = 1

private def psuC3bg3_C2 {f n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    {h : UnitaryFieldData 2 f K} {X B : GL (Fin n) K} (S : PSUGraphSetting h n X B)
    (P : Finset (Matrix (Fin n) (Fin n) K)) (hP : PrimFamily (psuAlg B) P)
    (F : {e : Matrix (Fin n) (Fin n) K // e ∈ P} → Type) [fieldF : ∀ e, Field (F e)]
    (Ψ : ∀ e e' : {e : Matrix (Fin n) (Fin n) K // e ∈ P},
      e'.1 = psuPsi h X e.1 → (F e' ≃+* F e))
    (y : ∀ e : {e : Matrix (Fin n) (Fin n) K // e ∈ P}, F e) : Prop :=
  ∀ e : {e : Matrix (Fin n) (Fin n) K // e ∈ P},
    Ψ e (psuC3bg3_psi S P hP e) rfl (y (psuC3bg3_psi S P hP e)) * y e = 1

private lemma psuC3bg3_U_family_card {f n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    {h : UnitaryFieldData 2 f K} {X B : GL (Fin n) K} (S : PSUGraphSetting h n X B)
    (P : Finset (Matrix (Fin n) (Fin n) K)) (hP : PrimFamily (psuAlg B) P)
    (F : {e : Matrix (Fin n) (Fin n) K // e ∈ P} → Type) [fieldF : ∀ e, Field (F e)]
    [algF : ∀ e, Algebra K (F e)]
    (π : ∀ e : {e : Matrix (Fin n) (Fin n) K // e ∈ P}, psuAlg B →ₐ[K] F e)
    (hbij : Function.Bijective (fun (a : psuAlg B)
      (e : {e : Matrix (Fin n) (Fin n) K // e ∈ P}) => π e a))
    (ι : ∀ e e' : {e : Matrix (Fin n) (Fin n) K // e ∈ P},
      e'.1 = psuDag h e.1 → (F e' ≃+* F e))
    (hι : ∀ (a : psuAlg B) (e e' : {e : Matrix (Fin n) (Fin n) K // e ∈ P})
      (he : e'.1 = psuDag h e.1),
      π e ⟨psuDag h (a : Matrix (Fin n) (Fin n) K), (psuGraph_star_mem S a.1 a.2).1⟩ =
        ι e e' he (π e' a))
    (Ψ : ∀ e e' : {e : Matrix (Fin n) (Fin n) K // e ∈ P},
      e'.1 = psuPsi h X e.1 → (F e' ≃+* F e))
    (hΨ : ∀ (a : psuAlg B) (e e' : {e : Matrix (Fin n) (Fin n) K // e ∈ P})
      (he : e'.1 = psuPsi h X e.1),
      π e ⟨psuPsi h X (a : Matrix (Fin n) (Fin n) K), (psuGraph_star_mem S a.1 a.2).2⟩ =
        Ψ e e' he (π e' a)) :
    Nat.card (psuC3b_U h X B) =
      Nat.card {y : ∀ e : {e : Matrix (Fin n) (Fin n) K // e ∈ P}, F e //
        psuC3bg3_C1 S P hP F ι y ∧ psuC3bg3_C2 S P hP F Ψ y} := by
  classical
  let e0 : psuAlg B ≃ (∀ e : {e : Matrix (Fin n) (Fin n) K // e ∈ P}, F e) :=
    Equiv.ofBijective _ hbij
  have hdag : ∀ t : psuAlg B, psuC3bg3_dagA S t * t = 1 ↔
      ∀ e : {e : Matrix (Fin n) (Fin n) K // e ∈ P},
        ι e (psuC3bg3_dag S P hP e) rfl (e0 t (psuC3bg3_dag S P hP e)) * e0 t e = 1 := by
    intro t
    have ht : e0 t = (fun e => π e t) := rfl
    rw [ht]
    exact psuC3bg3_dag_eq_one_iff S P hP F π ι hι hbij t
  have hpsi : ∀ t : psuAlg B, psuC3bg3_psiA S t * t = 1 ↔
      ∀ e : {e : Matrix (Fin n) (Fin n) K // e ∈ P},
        Ψ e (psuC3bg3_psi S P hP e) rfl (e0 t (psuC3bg3_psi S P hP e)) * e0 t e = 1 := by
    intro t
    have ht : e0 t = (fun e => π e t) := rfl
    rw [ht]
    exact psuC3bg3_psi_eq_one_iff S P hP F π Ψ hΨ hbij t
  let ue : psuC3b_U h X B ≃
      {t : psuAlg B // psuC3bg3_dagA S t * t = 1 ∧ psuC3bg3_psiA S t * t = 1} :=
    { toFun := fun u => ⟨u.1.1, (psuC3bg3_dagA_eq_one_iff S u.1.1).mpr u.1.2,
        (psuC3bg3_psiA_eq_one_iff S u.1.1).mpr u.2⟩
      invFun := fun t => ⟨⟨t.1, (psuC3bg3_dagA_eq_one_iff S t.1).mp t.2.1⟩,
        (psuC3bg3_psiA_eq_one_iff S t.1).mp t.2.2⟩
      left_inv := fun u => by apply Subtype.ext; apply Subtype.ext; rfl
      right_inv := fun t => by apply Subtype.ext; apply Subtype.ext; rfl }
  rw [Nat.card_congr ue]
  apply Nat.card_congr
  refine Equiv.subtypeEquiv e0 ?_
  intro t
  exact and_congr (hdag t) (hpsi t)

private lemma psuC3bg3_orbit_mem_swap {f n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    {h : UnitaryFieldData 2 f K} {X B : GL (Fin n) K} (S : PSUGraphSetting h n X B)
    (e r : Matrix (Fin n) (Fin n) K) :
    e ∈ psuC3b_orbit h X r ↔
      (r = e ∨ r = psuDag h e ∨ r = psuPsi h X e ∨ r = psuDag h (psuPsi h X e)) := by
  simp only [psuC3b_orbit, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro (h1 | h1 | h1 | h1)
    · exact Or.inl h1.symm
    · exact Or.inr (Or.inl (by rw [h1, psuDag_dag]))
    · exact Or.inr (Or.inr (Or.inl (by rw [h1, psuPsi_psi h X S.X_mem S.X_sq])))
    · exact Or.inr (Or.inr (Or.inr (by rw [h1, psuC3b_dag_psi_dag_psi S])))
  · rintro (h1 | h1 | h1 | h1)
    · exact Or.inl h1.symm
    · exact Or.inr (Or.inl (by rw [h1, psuDag_dag]))
    · exact Or.inr (Or.inr (Or.inl (by rw [h1, psuPsi_psi h X S.X_mem S.X_sq])))
    · exact Or.inr (Or.inr (Or.inr (by rw [h1, psuC3b_dag_psi_dag_psi S])))

private lemma psuC3bg3_existsUnique_orbit {f n : ℕ} {K : Type} [Field K] [Finite K]
    [CharP K 2] {h : UnitaryFieldData 2 f K} {X B : GL (Fin n) K}
    (S : PSUGraphSetting h n X B) (P R : Finset (Matrix (Fin n) (Fin n) K))
    (hrep : ∀ e ∈ P, ∃! r, r ∈ R ∧
      (r = e ∨ r = psuDag h e ∨ r = psuPsi h X e ∨ r = psuDag h (psuPsi h X e)))
    (e : {e : Matrix (Fin n) (Fin n) K // e ∈ P}) :
    ∃! r : {r : Matrix (Fin n) (Fin n) K // r ∈ R}, e.1 ∈ psuC3b_orbit h X r.1 := by
  classical
  obtain ⟨r, ⟨hrR, hcond⟩, huniq⟩ := hrep e.1 e.2
  refine ⟨⟨r, hrR⟩, (psuC3bg3_orbit_mem_swap S e.1 r).mpr hcond, ?_⟩
  intro r' hr'
  apply Subtype.ext
  exact huniq r'.1 ⟨r'.2, (psuC3bg3_orbit_mem_swap S e.1 r'.1).mp hr'⟩

private noncomputable def psuC3bg3_rep {f n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    {h : UnitaryFieldData 2 f K} {X B : GL (Fin n) K} (S : PSUGraphSetting h n X B)
    (P R : Finset (Matrix (Fin n) (Fin n) K))
    (hrep : ∀ e ∈ P, ∃! r, r ∈ R ∧
      (r = e ∨ r = psuDag h e ∨ r = psuPsi h X e ∨ r = psuDag h (psuPsi h X e)))
    (e : {e : Matrix (Fin n) (Fin n) K // e ∈ P}) :
    {r : Matrix (Fin n) (Fin n) K // r ∈ R} :=
  Classical.choose (psuC3bg3_existsUnique_orbit S P R hrep e)

private lemma psuC3bg3_rep_spec {f n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    {h : UnitaryFieldData 2 f K} {X B : GL (Fin n) K} (S : PSUGraphSetting h n X B)
    (P R : Finset (Matrix (Fin n) (Fin n) K))
    (hrep : ∀ e ∈ P, ∃! r, r ∈ R ∧
      (r = e ∨ r = psuDag h e ∨ r = psuPsi h X e ∨ r = psuDag h (psuPsi h X e)))
    (e : {e : Matrix (Fin n) (Fin n) K // e ∈ P}) :
    e.1 ∈ psuC3b_orbit h X (psuC3bg3_rep S P R hrep e).1 :=
  (Classical.choose_spec (psuC3bg3_existsUnique_orbit S P R hrep e)).1

private def psuC3bg3_fiber {f n : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K)
    (X : GL (Fin n) K) (P R : Finset (Matrix (Fin n) (Fin n) K))
    (r : {r : Matrix (Fin n) (Fin n) K // r ∈ R}) : Type :=
  {e : {e : Matrix (Fin n) (Fin n) K // e ∈ P} // e.1 ∈ psuC3b_orbit h X r.1}

private def psuC3bg3_C1r {f n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    {h : UnitaryFieldData 2 f K} {X B : GL (Fin n) K} (S : PSUGraphSetting h n X B)
    (P R : Finset (Matrix (Fin n) (Fin n) K)) (hP : PrimFamily (psuAlg B) P)
    (F : {e : Matrix (Fin n) (Fin n) K // e ∈ P} → Type) [fieldF : ∀ e, Field (F e)]
    (ι : ∀ e e' : {e : Matrix (Fin n) (Fin n) K // e ∈ P},
      e'.1 = psuDag h e.1 → (F e' ≃+* F e))
    (r : {r : Matrix (Fin n) (Fin n) K // r ∈ R})
    (z : ∀ e : {e : {e : Matrix (Fin n) (Fin n) K // e ∈ P} //
        e.1 ∈ psuC3b_orbit h X r.1}, F e.1) : Prop :=
  ∀ e : {e : {e : Matrix (Fin n) (Fin n) K // e ∈ P} //
        e.1 ∈ psuC3b_orbit h X r.1},
    ι e.1 (psuC3bg3_dag S P hP e.1) rfl
      (z ⟨psuC3bg3_dag S P hP e.1, psuC3b_orbit_dag_mem e.2⟩) * z e = 1

private def psuC3bg3_C2r {f n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    {h : UnitaryFieldData 2 f K} {X B : GL (Fin n) K} (S : PSUGraphSetting h n X B)
    (P R : Finset (Matrix (Fin n) (Fin n) K)) (hP : PrimFamily (psuAlg B) P)
    (F : {e : Matrix (Fin n) (Fin n) K // e ∈ P} → Type) [fieldF : ∀ e, Field (F e)]
    (Ψ : ∀ e e' : {e : Matrix (Fin n) (Fin n) K // e ∈ P},
      e'.1 = psuPsi h X e.1 → (F e' ≃+* F e))
    (r : {r : Matrix (Fin n) (Fin n) K // r ∈ R})
    (z : ∀ e : {e : {e : Matrix (Fin n) (Fin n) K // e ∈ P} //
        e.1 ∈ psuC3b_orbit h X r.1}, F e.1) : Prop :=
  ∀ e : {e : {e : Matrix (Fin n) (Fin n) K // e ∈ P} //
        e.1 ∈ psuC3b_orbit h X r.1},
    Ψ e.1 (psuC3bg3_psi S P hP e.1) rfl
      (z ⟨psuC3bg3_psi S P hP e.1, psuC3b_orbit_psi_mem S e.2⟩) * z e = 1

private lemma psuC3bg3_C1_iff {f n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    {h : UnitaryFieldData 2 f K} {X B : GL (Fin n) K} (S : PSUGraphSetting h n X B)
    (P R : Finset (Matrix (Fin n) (Fin n) K)) (hP : PrimFamily (psuAlg B) P)
    (hrep : ∀ e ∈ P, ∃! r, r ∈ R ∧
      (r = e ∨ r = psuDag h e ∨ r = psuPsi h X e ∨ r = psuDag h (psuPsi h X e)))
    (F : {e : Matrix (Fin n) (Fin n) K // e ∈ P} → Type) [fieldF : ∀ e, Field (F e)]
    (ι : ∀ e e' : {e : Matrix (Fin n) (Fin n) K // e ∈ P},
      e'.1 = psuDag h e.1 → (F e' ≃+* F e))
    (y : ∀ e : {e : Matrix (Fin n) (Fin n) K // e ∈ P}, F e) :
    psuC3bg3_C1 S P hP F ι y ↔
      ∀ r : {r : Matrix (Fin n) (Fin n) K // r ∈ R},
        psuC3bg3_C1r S P R hP F ι r (fun e => y e.1) := by
  constructor
  · intro h r e
    exact h e.1
  · intro h e
    exact h (psuC3bg3_rep S P R hrep e) ⟨e, psuC3bg3_rep_spec S P R hrep e⟩

private lemma psuC3bg3_C2_iff {f n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    {h : UnitaryFieldData 2 f K} {X B : GL (Fin n) K} (S : PSUGraphSetting h n X B)
    (P R : Finset (Matrix (Fin n) (Fin n) K)) (hP : PrimFamily (psuAlg B) P)
    (hrep : ∀ e ∈ P, ∃! r, r ∈ R ∧
      (r = e ∨ r = psuDag h e ∨ r = psuPsi h X e ∨ r = psuDag h (psuPsi h X e)))
    (F : {e : Matrix (Fin n) (Fin n) K // e ∈ P} → Type) [fieldF : ∀ e, Field (F e)]
    (Ψ : ∀ e e' : {e : Matrix (Fin n) (Fin n) K // e ∈ P},
      e'.1 = psuPsi h X e.1 → (F e' ≃+* F e))
    (y : ∀ e : {e : Matrix (Fin n) (Fin n) K // e ∈ P}, F e) :
    psuC3bg3_C2 S P hP F Ψ y ↔
      ∀ r : {r : Matrix (Fin n) (Fin n) K // r ∈ R},
        psuC3bg3_C2r S P R hP F Ψ r (fun e => y e.1) := by
  constructor
  · intro h r e
    exact h e.1
  · intro h e
    exact h (psuC3bg3_rep S P R hrep e) ⟨e, psuC3bg3_rep_spec S P R hrep e⟩

private lemma psuC3bg3_rep_eq {f n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    {h : UnitaryFieldData 2 f K} {X B : GL (Fin n) K} (S : PSUGraphSetting h n X B)
    (P R : Finset (Matrix (Fin n) (Fin n) K))
    (hrep : ∀ e ∈ P, ∃! r, r ∈ R ∧
      (r = e ∨ r = psuDag h e ∨ r = psuPsi h X e ∨ r = psuDag h (psuPsi h X e)))
    (e : {e : Matrix (Fin n) (Fin n) K // e ∈ P})
    (r : Matrix (Fin n) (Fin n) K) (hr : r ∈ R) (he : e.1 ∈ psuC3b_orbit h X r) :
    psuC3bg3_rep S P R hrep e = ⟨r, hr⟩ := by
  apply Subtype.ext
  have hspec := (Classical.choose_spec (psuC3bg3_existsUnique_orbit S P R hrep e)).2
  exact congrArg Subtype.val (hspec ⟨r, hr⟩ he).symm

private lemma psuC3bg3_z_cast {f n : ℕ} {K : Type} [Field K]
    {h : UnitaryFieldData 2 f K} {X : GL (Fin n) K}
    (P R : Finset (Matrix (Fin n) (Fin n) K))
    {F : {e : Matrix (Fin n) (Fin n) K // e ∈ P} → Type}
    {r r' : {r : Matrix (Fin n) (Fin n) K // r ∈ R}} (hr : r' = r)
    (z : (r : {r : Matrix (Fin n) (Fin n) K // r ∈ R}) →
      (e : psuC3bg3_fiber h X P R r) → F e.1)
    (e : psuC3bg3_fiber h X P R r) (mem' : e.1.1 ∈ psuC3b_orbit h X r'.1) :
    HEq (z r' ⟨e.1, mem'⟩) (z r e) := by
  cases hr
  rfl

private noncomputable def psuC3bg3_piEquiv {f n : ℕ} {K : Type} [Field K] [Finite K]
    [CharP K 2] {h : UnitaryFieldData 2 f K} {X B : GL (Fin n) K}
    (S : PSUGraphSetting h n X B) (P R : Finset (Matrix (Fin n) (Fin n) K))
    (hrep : ∀ e ∈ P, ∃! r, r ∈ R ∧
      (r = e ∨ r = psuDag h e ∨ r = psuPsi h X e ∨ r = psuDag h (psuPsi h X e)))
    (F : {e : Matrix (Fin n) (Fin n) K // e ∈ P} → Type) :
    ((e : {e : Matrix (Fin n) (Fin n) K // e ∈ P}) → F e) ≃
      ((r : {r : Matrix (Fin n) (Fin n) K // r ∈ R}) →
        (e : psuC3bg3_fiber h X P R r) → F e.1) where
  toFun y r e := y e.1
  invFun z e := z (psuC3bg3_rep S P R hrep e)
    ⟨e, psuC3bg3_rep_spec S P R hrep e⟩
  left_inv y := by funext e; rfl
  right_inv z := by
    funext r e
    have hrep_eq : psuC3bg3_rep S P R hrep e.1 = r :=
      psuC3bg3_rep_eq S P R hrep e.1 r.1 r.2 e.2
    change z (psuC3bg3_rep S P R hrep e.1)
      ⟨e.1, psuC3bg3_rep_spec S P R hrep e.1⟩ = z r e
    exact eq_of_heq (psuC3bg3_z_cast P R hrep_eq z e
      (psuC3bg3_rep_spec S P R hrep e.1))

private lemma psuC3bg3_family_factor {f n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    {h : UnitaryFieldData 2 f K} {X B : GL (Fin n) K} (S : PSUGraphSetting h n X B)
    (P R : Finset (Matrix (Fin n) (Fin n) K)) (hP : PrimFamily (psuAlg B) P)
    (hrep : ∀ e ∈ P, ∃! r, r ∈ R ∧
      (r = e ∨ r = psuDag h e ∨ r = psuPsi h X e ∨ r = psuDag h (psuPsi h X e)))
    (F : {e : Matrix (Fin n) (Fin n) K // e ∈ P} → Type) [fieldF : ∀ e, Field (F e)]
    (ι : ∀ e e' : {e : Matrix (Fin n) (Fin n) K // e ∈ P},
      e'.1 = psuDag h e.1 → (F e' ≃+* F e))
    (Ψ : ∀ e e' : {e : Matrix (Fin n) (Fin n) K // e ∈ P},
      e'.1 = psuPsi h X e.1 → (F e' ≃+* F e)) :
    Nat.card {y : ∀ e : {e : Matrix (Fin n) (Fin n) K // e ∈ P}, F e //
        psuC3bg3_C1 S P hP F ι y ∧ psuC3bg3_C2 S P hP F Ψ y} =
      ∏ r : {r : Matrix (Fin n) (Fin n) K // r ∈ R},
        Nat.card {z : (e : psuC3bg3_fiber h X P R r) → F e.1 //
          psuC3bg3_C1r S P R hP F ι r z ∧ psuC3bg3_C2r S P R hP F Ψ r z} := by
  classical
  let ePi := psuC3bg3_piEquiv S P R hrep F
  have hpred : ∀ y : (e : {e : Matrix (Fin n) (Fin n) K // e ∈ P}) → F e,
      (psuC3bg3_C1 S P hP F ι y ∧ psuC3bg3_C2 S P hP F Ψ y) ↔
        ∀ r : {r : Matrix (Fin n) (Fin n) K // r ∈ R},
          (psuC3bg3_C1r S P R hP F ι r (ePi y r) ∧
            psuC3bg3_C2r S P R hP F Ψ r (ePi y r)) := by
    intro y
    have h1 : psuC3bg3_C1 S P hP F ι y ↔
        ∀ r : {r : Matrix (Fin n) (Fin n) K // r ∈ R},
          psuC3bg3_C1r S P R hP F ι r (ePi y r) := by
      exact psuC3bg3_C1_iff S P R hP hrep F ι y
    have h2 : psuC3bg3_C2 S P hP F Ψ y ↔
        ∀ r : {r : Matrix (Fin n) (Fin n) K // r ∈ R},
          psuC3bg3_C2r S P R hP F Ψ r (ePi y r) := by
      exact psuC3bg3_C2_iff S P R hP hrep F Ψ y
    constructor
    · intro h r
      exact ⟨h1.mp h.1 r, h2.mp h.2 r⟩
    · intro h
      exact ⟨h1.mpr (fun r => (h r).1), h2.mpr (fun r => (h r).2)⟩
  let ee : {y : ∀ e : {e : Matrix (Fin n) (Fin n) K // e ∈ P}, F e //
        psuC3bg3_C1 S P hP F ι y ∧ psuC3bg3_C2 S P hP F Ψ y} ≃
      ((r : {r : Matrix (Fin n) (Fin n) K // r ∈ R}) →
        {z : (e : psuC3bg3_fiber h X P R r) → F e.1 //
          psuC3bg3_C1r S P R hP F ι r z ∧ psuC3bg3_C2r S P R hP F Ψ r z}) :=
    (Equiv.subtypeEquiv ePi hpred).trans
      (Equiv.subtypePiEquivPi (α := {r : Matrix (Fin n) (Fin n) K // r ∈ R})
        (β := fun r => (e : psuC3bg3_fiber h X P R r) → F e.1)
        (p := fun r z => psuC3bg3_C1r S P R hP F ι r z ∧ psuC3bg3_C2r S P R hP F Ψ r z))
  rw [Nat.card_congr ee]
  exact Nat.card_pi

private def psuC3bg3_Local {f n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    {h : UnitaryFieldData 2 f K} {X B : GL (Fin n) K} (S : PSUGraphSetting h n X B)
    (P R : Finset (Matrix (Fin n) (Fin n) K)) (hP : PrimFamily (psuAlg B) P)
    (F : {e : Matrix (Fin n) (Fin n) K // e ∈ P} → Type) [fieldF : ∀ e, Field (F e)]
    (ι : ∀ e e' : {e : Matrix (Fin n) (Fin n) K // e ∈ P},
      e'.1 = psuDag h e.1 → (F e' ≃+* F e))
    (Ψ : ∀ e e' : {e : Matrix (Fin n) (Fin n) K // e ∈ P},
      e'.1 = psuPsi h X e.1 → (F e' ≃+* F e))
    (r : {r : Matrix (Fin n) (Fin n) K // r ∈ R}) : Type :=
  {z : (e : psuC3bg3_fiber h X P R r) → F e.1 //
    psuC3bg3_C1r S P R hP F ι r z ∧ psuC3bg3_C2r S P R hP F Ψ r z}

private lemma psuC3bg3_pi_self {n : ℕ} {K : Type} [Field K]
    {B : GL (Fin n) K}
    (P : Finset (Matrix (Fin n) (Fin n) K)) (hP : PrimFamily (psuAlg B) P)
    (F : {e : Matrix (Fin n) (Fin n) K // e ∈ P} → Type) [fieldF : ∀ e, Field (F e)]
    [algF : ∀ e, Algebra K (F e)]
    (π : ∀ e : {e : Matrix (Fin n) (Fin n) K // e ∈ P}, psuAlg B →ₐ[K] F e)
    (hker : ∀ e (a : psuAlg B), π e a = 0 ↔ (a : Matrix (Fin n) (Fin n) K) * e.1 = 0)
    (e : {e : Matrix (Fin n) (Fin n) K // e ∈ P}) :
    π e ⟨e.1, ((hP.1 e.1).mp e.2).1⟩ = 1 := by
  have hePrim : IsPrimIdemIn (psuAlg B) e.1 := (hP.1 e.1).mp e.2
  let eA : psuAlg B := ⟨e.1, hePrim.1⟩
  have heidem : e.1 * e.1 = e.1 := hePrim.2.1.eq
  have h1e : ((1 : Matrix (Fin n) (Fin n) K) - e.1) ∈ psuAlg B :=
    (psuAlg B).sub_mem ((psuAlg B).one_mem) eA.2
  have hzero : (((⟨(1 : Matrix (Fin n) (Fin n) K) - e.1, h1e⟩ : psuAlg B) :
      Matrix (Fin n) (Fin n) K) * e.1) = 0 := by
    change (1 - e.1) * e.1 = 0
    rw [Matrix.sub_mul, Matrix.one_mul, heidem, sub_self]
  have h0 := (hker e ⟨(1 : Matrix (Fin n) (Fin n) K) - e.1, h1e⟩).mpr hzero
  have hsplit : π e (⟨(1 : Matrix (Fin n) (Fin n) K) - e.1, h1e⟩ : psuAlg B) =
      1 - π e eA := by
    rw [show (⟨(1 : Matrix (Fin n) (Fin n) K) - e.1, h1e⟩ : psuAlg B) = 1 - eA from rfl,
      map_sub, map_one]
  rw [hsplit] at h0
  exact (sub_eq_zero.mp h0).symm

private lemma psuC3bg3_kind_two {f n : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K)
    (X B : GL (Fin n) K) (e : Matrix (Fin n) (Fin n) K) (hk : psuKind h X B e = 2) :
    psuDag h e ≠ e ∧ psuPsi h X e = e ∧ psuPsiTrivial h X B e := by
  unfold psuKind at hk
  by_cases hd : psuDag h e = e
  · rw [if_pos hd] at hk
    by_cases hp : psuPsi h X e = e
    · rw [if_pos hp] at hk; omega
    · rw [if_neg hp] at hk; omega
  · rw [if_neg hd] at hk
    by_cases hp : psuPsi h X e = e
    · rw [if_pos hp] at hk
      by_cases ht : psuPsiTrivial h X B e
      · rw [if_pos ht] at hk; exact ⟨hd, hp, ht⟩
      · rw [if_neg ht] at hk; omega
    · rw [if_neg hp] at hk
      by_cases h4 : psuPsi h X e = psuDag h e
      · rw [if_pos h4] at hk; omega
      · rw [if_neg h4] at hk; omega

private lemma psuC3bg3_Ψ_eq_of_idx_eq {f n : ℕ} {K : Type} [Field K]
    {h : UnitaryFieldData 2 f K} {X : GL (Fin n) K}
    (P : Finset (Matrix (Fin n) (Fin n) K))
    {F : {e : Matrix (Fin n) (Fin n) K // e ∈ P} → Type} [fieldF : ∀ e, Field (F e)]
    (Ψ : ∀ e e' : {e : Matrix (Fin n) (Fin n) K // e ∈ P},
      e'.1 = psuPsi h X e.1 → (F e' ≃+* F e))
    {rI e' : {e : Matrix (Fin n) (Fin n) K // e ∈ P}} (hidx : e' = rI)
    (he : e'.1 = psuPsi h X rI.1) (he' : rI.1 = psuPsi h X rI.1) (x : F e') :
    HEq (Ψ rI e' he x) (Ψ rI rI he' (cast (congrArg F hidx) x)) := by
  subst hidx
  rfl

private lemma psuC3bg3_ι_eq_of_idx_eq {f n : ℕ} {K : Type} [Field K]
    {h : UnitaryFieldData 2 f K}
    (P : Finset (Matrix (Fin n) (Fin n) K))
    {F : {e : Matrix (Fin n) (Fin n) K // e ∈ P} → Type} [fieldF : ∀ e, Field (F e)]
    (ι : ∀ e e' : {e : Matrix (Fin n) (Fin n) K // e ∈ P},
      e'.1 = psuDag h e.1 → (F e' ≃+* F e))
    {rI e' : {e : Matrix (Fin n) (Fin n) K // e ∈ P}} (hidx : e' = rI)
    (he : e'.1 = psuDag h rI.1) (he' : rI.1 = psuDag h rI.1) (x : F e') :
    HEq (ι rI e' he x) (ι rI rI he' (cast (congrArg F hidx) x)) := by
  subst hidx
  rfl

private lemma psuC3bg3_z_cast' {f n : ℕ} {K : Type} [Field K]
    {h : UnitaryFieldData 2 f K} {X : GL (Fin n) K}
    {P R : Finset (Matrix (Fin n) (Fin n) K)}
    {F : {e : Matrix (Fin n) (Fin n) K // e ∈ P} → Type}
    {r : {r : Matrix (Fin n) (Fin n) K // r ∈ R}}
    {z : (e : psuC3bg3_fiber h X P R r) → F e.1}
    {a b : psuC3bg3_fiber h X P R r} (hab : a = b) :
    cast (congrArg F (congrArg Subtype.val hab)) (z a) = z b := by
  subst hab
  rfl

private lemma psuC3bg3_sq_eq_one {E : Type} [Field E] [CharP E 2] {x : E}
    (hx : x * x = 1) : x = 1 := by
  have h0 : (x - 1) * (x + 1) = 0 := by
    rw [show (x - 1) * (x + 1) = x * x - 1 by ring, hx, sub_self]
  have hneg : (-1 : E) = 1 := by
    rw [neg_eq_iff_add_eq_zero]
    have h2 : (2 : E) = 0 := CharP.cast_eq_zero E 2
    rwa [show (2 : E) = 1 + 1 from by ring] at h2
  have hsub : x - 1 = x + 1 := by rw [sub_eq_add_neg, hneg]
  have h0' : (x - 1) * (x - 1) = 0 := by
    rw [← hsub] at h0
    exact h0
  exact sub_eq_zero.mp (mul_self_eq_zero.mp h0')

private lemma psuC3bg3_iota_inv {f n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    {h : UnitaryFieldData 2 f K} {X B : GL (Fin n) K} (S : PSUGraphSetting h n X B)
    (P : Finset (Matrix (Fin n) (Fin n) K))
    {F : {e : Matrix (Fin n) (Fin n) K // e ∈ P} → Type} [fieldF : ∀ e, Field (F e)]
    [algF : ∀ e, Algebra K (F e)]
    (π : ∀ e : {e : Matrix (Fin n) (Fin n) K // e ∈ P}, psuAlg B →ₐ[K] F e)
    (hπ : ∀ e, Function.Surjective (π e))
    (ι : ∀ e e' : {e : Matrix (Fin n) (Fin n) K // e ∈ P},
      e'.1 = psuDag h e.1 → (F e' ≃+* F e))
    (hι : ∀ (a : psuAlg B) (e e' : {e : Matrix (Fin n) (Fin n) K // e ∈ P})
      (he : e'.1 = psuDag h e.1),
      π e ⟨psuDag h (a : Matrix (Fin n) (Fin n) K), (psuGraph_star_mem S a.1 a.2).1⟩ =
        ι e e' he (π e' a))
    {e e' : {e : Matrix (Fin n) (Fin n) K // e ∈ P}} (he : e'.1 = psuDag h e.1)
    (he' : e.1 = psuDag h e'.1) :
    ι e' e he' = (ι e e' he).symm := by
  let f : F e' ≃+* F e := ι e e' he
  let g : F e ≃+* F e' := ι e' e he'
  have hfg : ∀ y : F e, f (g y) = y := by
    intro y
    obtain ⟨a, rfl⟩ := hπ e y
    let a' : psuAlg B := ⟨psuDag h (a : Matrix (Fin n) (Fin n) K),
      (psuGraph_star_mem S a.1 a.2).1⟩
    have h1 : g (π e a) = π e' a' := (hι a e' e he').symm
    have h2 : f (π e' a') = π e ⟨psuDag h (a' : Matrix (Fin n) (Fin n) K),
      (psuGraph_star_mem S a'.1 a'.2).1⟩ := (hι a' e e' he).symm
    have h3 : (⟨psuDag h (a' : Matrix (Fin n) (Fin n) K),
        (psuGraph_star_mem S a'.1 a'.2).1⟩ : psuAlg B) = a := by
      apply Subtype.ext
      exact psuDag_dag h (a : Matrix (Fin n) (Fin n) K)
    rw [h1, h2, h3]
  apply RingEquiv.ext
  intro x
  calc g x = f.symm (f (g x)) := (f.symm_apply_apply (g x)).symm
    _ = f.symm x := by rw [hfg x]

private lemma psuC3bg3_kind_one {f n : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K)
    (X B : GL (Fin n) K) (e : Matrix (Fin n) (Fin n) K) (hk : psuKind h X B e = 1) :
    psuDag h e = e ∧ psuPsi h X e ≠ e := by
  unfold psuKind at hk
  by_cases hd : psuDag h e = e
  · rw [if_pos hd] at hk
    by_cases hp : psuPsi h X e = e
    · rw [if_pos hp] at hk; omega
    · rw [if_neg hp] at hk; exact ⟨hd, hp⟩
  · rw [if_neg hd] at hk
    by_cases hp : psuPsi h X e = e
    · rw [if_pos hp] at hk; split_ifs at hk <;> omega
    · rw [if_neg hp] at hk; split_ifs at hk <;> omega

private lemma psuC3bg3_kind_zero {f n : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K)
    (X B : GL (Fin n) K) (e : Matrix (Fin n) (Fin n) K) (hk : psuKind h X B e = 0) :
    psuDag h e = e ∧ psuPsi h X e = e := by
  unfold psuKind at hk
  by_cases hd : psuDag h e = e
  · rw [if_pos hd] at hk
    by_cases hp : psuPsi h X e = e
    · rw [if_pos hp] at hk; exact ⟨hd, hp⟩
    · rw [if_neg hp] at hk; omega
  · rw [if_neg hd] at hk
    by_cases hp : psuPsi h X e = e
    · rw [if_pos hp] at hk; split_ifs at hk <;> omega
    · rw [if_neg hp] at hk; split_ifs at hk <;> omega

private lemma psuC3bg3_sqrt_sq (n : ℕ) : Nat.sqrt (n ^ 2) = n := by
  rw [pow_two]
  exact Nat.sqrt_eq n

private lemma psuC3bg3_unitary_fix_eq_one {E : Type} [Field E] [Finite E] [CharP E 2]
    (σ : E ≃+* E) (hσ2 : ∀ t, σ (σ t) = t) (hσ1 : ∃ t, σ t ≠ t)
    (Θ : E ≃+* E) (hΘ2 : ∀ t, Θ (Θ t) = t) (hΘ1 : ∃ t, Θ t ≠ t) :
    Nat.card {t : E // σ t * t = 1 ∧ (Θ * σ) t * t = 1} = 1 := by
  classical
  haveI : Fintype E := Fintype.ofFinite E
  let H1 : Subgroup Eˣ :=
    { carrier := {u | σ (u : E) * (u : E) = 1}
      one_mem' := by simp
      mul_mem' := by
        intro u v hu hv
        change σ ↑(u * v) * ↑(u * v) = 1
        rw [Units.val_mul, map_mul]
        calc σ ↑u * σ ↑v * (↑u * ↑v) = (σ ↑u * ↑u) * (σ ↑v * ↑v) := by ring
          _ = 1 := by rw [hu, hv, mul_one]
      inv_mem' := by
        intro u hu
        change σ ↑(u⁻¹) * ↑(u⁻¹) = 1
        have hu' : σ (u : E) * (u : E) = 1 := hu
        have hσu : σ (u : E) = ((u : E))⁻¹ := eq_inv_of_mul_eq_one_left hu'
        rw [Units.val_inv_eq_inv_val, ← hσu, hσ2, hσu, mul_inv_cancel₀ (Units.ne_zero u)] }
  let H2 : Subgroup Eˣ :=
    { carrier := {u | Θ (u : E) = (u : E)}
      one_mem' := by simp
      mul_mem' := by
        intro u v hu hv
        change Θ ↑(u * v) = ↑(u * v)
        rw [Units.val_mul, map_mul, hu, hv]
      inv_mem' := by
        intro u hu
        change Θ ↑(u⁻¹) = ↑(u⁻¹)
        rw [Units.val_inv_eq_inv_val, map_inv₀, hu] }
  have hcard1 : Nat.card H1 = Nat.sqrt (Nat.card E) + 1 := by
    rw [← psuC3b_field_unitary_card (E := E) σ hσ2 hσ1]
    apply Nat.card_congr
    refine { toFun := fun u => ⟨((u : Eˣ) : E), u.2⟩
             invFun := fun t => ⟨Units.mk0 t.1 (by
               intro h0
               have ht := t.2
               rw [h0, map_zero, zero_mul] at ht
               exact zero_ne_one ht), t.2⟩
             left_inv := fun u => Subtype.ext (Units.ext rfl)
             right_inv := fun t => Subtype.ext rfl }
  have hcard2 : Nat.card H2 = Nat.sqrt (Nat.card E) - 1 := by
    rw [show Nat.card H2 = Nat.card {u : Eˣ // Θ (u : E) = (u : E)} from rfl]
    exact psuC3b_field_fix_units_card (E := E) Θ hΘ2 hΘ1
  have hone : ∀ a : {t : E // σ t * t = 1 ∧ (Θ * σ) t * t = 1}, a.1 = 1 := by
    intro a
    by_contra hne
    have ha0 : a.1 ≠ 0 := by rintro h; simpa [h] using a.2.1
    let u : Eˣ := Units.mk0 a.1 ha0
    have hu1 : u ∈ H1 := by
      change σ (u : E) * (u : E) = 1
      exact a.2.1
    have hu2 : u ∈ H2 := by
      show Θ (u : E) = (u : E)
      change Θ a.1 = a.1
      have h1 : σ a.1 = a.1⁻¹ := eq_inv_of_mul_eq_one_left a.2.1
      have h2 : Θ (σ a.1) = a.1⁻¹ := eq_inv_of_mul_eq_one_left a.2.2
      rw [h1, map_inv₀] at h2
      exact _root_.inv_inj.mp h2
    have hd1 : orderOf u ∣ Nat.card H1 := by
      have := Subgroup.card_dvd_of_le (Subgroup.zpowers_le.mpr hu1)
      rwa [Nat.card_zpowers] at this
    have hd2 : orderOf u ∣ Nat.card H2 := by
      have := Subgroup.card_dvd_of_le (Subgroup.zpowers_le.mpr hu2)
      rwa [Nat.card_zpowers] at this
    have hn1 : 1 ≤ Nat.sqrt (Nat.card E) :=
      (Nat.sqrt_pos).mpr (Nat.card_pos (α := E))
    have hg2 : orderOf u ∣ 2 := by
      have h1 : orderOf u ∣ Nat.sqrt (Nat.card E) + 1 := hcard1 ▸ hd1
      have h2 : orderOf u ∣ Nat.sqrt (Nat.card E) - 1 := hcard2 ▸ hd2
      have hsub : Nat.sqrt (Nat.card E) + 1 - (Nat.sqrt (Nat.card E) - 1) = 2 := by omega
      have hd := Nat.dvd_sub h1 h2
      rwa [hsub] at hd
    rcases (Nat.dvd_prime Nat.prime_two).mp hg2 with h | h
    · have hu : u = 1 := orderOf_eq_one_iff.mp h
      have h1 : (u : E) = 1 := Units.val_eq_one.mpr hu
      exact hne (by rwa [show (u : E) = a.1 from rfl] at h1)
    · have hpow : u ^ 2 = 1 := by rw [← h]; exact pow_orderOf_eq_one u
      have h2 : (u : E) * (u : E) = 1 := by
        have := congrArg (fun v : Eˣ => (v : E)) hpow
        simpa only [pow_two, Units.val_mul, Units.val_one] using this
      have hu : u = 1 := Units.ext (psuC3bg3_sq_eq_one h2)
      have h1 : (u : E) = 1 := Units.val_eq_one.mpr hu
      exact hne (by rwa [show (u : E) = a.1 from rfl] at h1)
  rw [Nat.card_eq_one_iff_unique]
  exact ⟨⟨fun a b => Subtype.ext (by rw [hone a, hone b])⟩, ⟨⟨1, by simp⟩⟩⟩

private lemma psuC3bg3_unitary_fix_apply {E : Type} [Field E] [Finite E] [CharP E 2]
    (σ : E ≃+* E) (hσ2 : ∀ t, σ (σ t) = t) (hσ1 : ∃ t, σ t ≠ t)
    (Θ : E ≃+* E) (hΘ2 : ∀ t, Θ (Θ t) = t) (hΘ1 : ∃ t, Θ t ≠ t)
    (t : E) (h1 : σ t * t = 1) (h2 : (Θ * σ) t * t = 1) : t = 1 := by
  haveI : Subsingleton {t : E // σ t * t = 1 ∧ (Θ * σ) t * t = 1} :=
    (Nat.card_eq_one_iff_unique.mp
      (psuC3bg3_unitary_fix_eq_one σ hσ2 hσ1 Θ hΘ2 hΘ1)).1
  exact congrArg Subtype.val
    (Subsingleton.elim (⟨t, h1, h2⟩ : {t : E // σ t * t = 1 ∧ (Θ * σ) t * t = 1})
      ⟨1, by simp⟩)

private lemma psuC3bg3_local_kind0 {f n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    {h : UnitaryFieldData 2 f K} {X B : GL (Fin n) K} (S : PSUGraphSetting h n X B)
    (P R : Finset (Matrix (Fin n) (Fin n) K)) (hP : PrimFamily (psuAlg B) P)
    (F : {e : Matrix (Fin n) (Fin n) K // e ∈ P} → Type) [fieldF : ∀ e, Field (F e)]
    [algF : ∀ e, Algebra K (F e)] [charF : ∀ e, CharP (F e) 2] [finF : ∀ e, Finite (F e)]
    (π : ∀ e : {e : Matrix (Fin n) (Fin n) K // e ∈ P}, psuAlg B →ₐ[K] F e)
    (hπ : ∀ e, Function.Surjective (π e))
    (hR : R ⊆ P)
    (ι : ∀ e e' : {e : Matrix (Fin n) (Fin n) K // e ∈ P},
      e'.1 = psuDag h e.1 → (F e' ≃+* F e))
    (hι : ∀ (a : psuAlg B) (e e' : {e : Matrix (Fin n) (Fin n) K // e ∈ P})
      (he : e'.1 = psuDag h e.1),
      π e ⟨psuDag h (a : Matrix (Fin n) (Fin n) K), (psuGraph_star_mem S a.1 a.2).1⟩ =
        ι e e' he (π e' a))
    (Ψ : ∀ e e' : {e : Matrix (Fin n) (Fin n) K // e ∈ P},
      e'.1 = psuPsi h X e.1 → (F e' ≃+* F e))
    (hΨ : ∀ (a : psuAlg B) (e e' : {e : Matrix (Fin n) (Fin n) K // e ∈ P})
      (he : e'.1 = psuPsi h X e.1),
      π e ⟨psuPsi h X (a : Matrix (Fin n) (Fin n) K), (psuGraph_star_mem S a.1 a.2).2⟩ =
        Ψ e e' he (π e' a))
    (r : {r : Matrix (Fin n) (Fin n) K // r ∈ R}) (hk : psuKind h X B r.1 = 0) :
    Nat.card (psuC3bg3_Local S P R hP F ι Ψ r) =
      psuC3b_UO (2 ^ f) (blockDegree (psuAlg B) r.1) 0 := by
  obtain ⟨hp_dag, hp_psi⟩ := psuC3bg3_kind_zero h X B r.1 hk
  have hPr : r.1 ∈ P := hR r.2
  let rI : {e : Matrix (Fin n) (Fin n) K // e ∈ P} := ⟨r.1, hPr⟩
  let rf : psuC3bg3_fiber h X P R r := ⟨rI, psuC3b_orbit_self h X r.1⟩
  let ι0 : F rI ≃+* F rI := ι rI rI hp_dag.symm
  let Ψ0 : F rI ≃+* F rI := Ψ rI rI hp_psi.symm
  have hιK : ∀ c : K, ι0 (algebraMap K (F rI) c) = algebraMap K (F rI) (h.bar c) := by
    intro c
    let aK : psuAlg B := algebraMap K (psuAlg B) c
    have hh := hι aK rI rI hp_dag.symm
    have hsub : (⟨psuDag h (aK : Matrix (Fin n) (Fin n) K),
        (psuGraph_star_mem S aK.1 aK.2).1⟩ : psuAlg B) =
        algebraMap K (psuAlg B) (h.bar c) := by
      apply Subtype.ext
      simp [aK, Algebra.algebraMap_eq_smul_one, psuDag_smul, psuDag_one]
    rw [hsub] at hh
    rw [show (π rI) aK = algebraMap K (F rI) c from (π rI).commutes c,
      show (π rI) (algebraMap K (psuAlg B) (h.bar c)) = algebraMap K (F rI) (h.bar c) from
        (π rI).commutes (h.bar c)] at hh
    exact hh.symm
  have hΨK : ∀ c : K, Ψ0 (algebraMap K (F rI) c) = algebraMap K (F rI) c := by
    intro c
    let aK : psuAlg B := algebraMap K (psuAlg B) c
    have hh := hΨ aK rI rI hp_psi.symm
    have hsub : (⟨psuPsi h X (aK : Matrix (Fin n) (Fin n) K),
        (psuGraph_star_mem S aK.1 aK.2).2⟩ : psuAlg B) =
        algebraMap K (psuAlg B) c := by
      apply Subtype.ext
      simp [aK, Algebra.algebraMap_eq_smul_one, psuPsi_smul, psuPsi_one]
    rw [hsub] at hh
    rw [show (π rI) aK = algebraMap K (F rI) c from (π rI).commutes c] at hh
    exact hh.symm
  have hσ2 : ∀ t, ι0 (ι0 t) = t := by
    intro t
    obtain ⟨a, rfl⟩ := hπ rI t
    have h1 : ι0 (π rI a) = π rI ⟨psuDag h (a : Matrix (Fin n) (Fin n) K),
        (psuGraph_star_mem S a.1 a.2).1⟩ := (hι a rI rI hp_dag.symm).symm
    have h2 : ι0 (π rI ⟨psuDag h (a : Matrix (Fin n) (Fin n) K),
        (psuGraph_star_mem S a.1 a.2).1⟩) = π rI a := by
      have hh := (hι ⟨psuDag h (a : Matrix (Fin n) (Fin n) K),
        (psuGraph_star_mem S a.1 a.2).1⟩ rI rI hp_dag.symm).symm
      rwa [show (⟨psuDag h (psuDag h (a : Matrix (Fin n) (Fin n) K)), _⟩ : psuAlg B) = a
        from Subtype.ext (psuDag_dag h (a : Matrix (Fin n) (Fin n) K))] at hh
    rw [h1, h2]
  have hΨ2 : ∀ t, Ψ0 (Ψ0 t) = t := by
    intro t
    obtain ⟨a, rfl⟩ := hπ rI t
    have h1 : Ψ0 (π rI a) = π rI ⟨psuPsi h X (a : Matrix (Fin n) (Fin n) K),
        (psuGraph_star_mem S a.1 a.2).2⟩ := (hΨ a rI rI hp_psi.symm).symm
    have h2 : Ψ0 (π rI ⟨psuPsi h X (a : Matrix (Fin n) (Fin n) K),
        (psuGraph_star_mem S a.1 a.2).2⟩) = π rI a := by
      have hh := (hΨ ⟨psuPsi h X (a : Matrix (Fin n) (Fin n) K),
        (psuGraph_star_mem S a.1 a.2).2⟩ rI rI hp_psi.symm).symm
      rwa [show (⟨psuPsi h X (psuPsi h X (a : Matrix (Fin n) (Fin n) K)), _⟩ : psuAlg B) = a
        from Subtype.ext (psuPsi_psi h X S.X_mem S.X_sq (a : Matrix (Fin n) (Fin n) K))] at hh
    rw [h1, h2]
  have hcomm : ∀ x, ι0 (Ψ0 x) = Ψ0 (ι0 x) := by
    intro x
    obtain ⟨a, rfl⟩ := hπ rI x
    have h1 : Ψ0 (π rI a) = π rI ⟨psuPsi h X (a : Matrix (Fin n) (Fin n) K),
        (psuGraph_star_mem S a.1 a.2).2⟩ := (hΨ a rI rI hp_psi.symm).symm
    have h2 : ι0 (π rI ⟨psuPsi h X (a : Matrix (Fin n) (Fin n) K),
        (psuGraph_star_mem S a.1 a.2).2⟩) =
        π rI ⟨psuDag h (psuPsi h X (a : Matrix (Fin n) (Fin n) K)), _⟩ :=
      (hι ⟨psuPsi h X (a : Matrix (Fin n) (Fin n) K),
        (psuGraph_star_mem S a.1 a.2).2⟩ rI rI hp_dag.symm).symm
    have h3 : ι0 (π rI a) = π rI ⟨psuDag h (a : Matrix (Fin n) (Fin n) K),
        (psuGraph_star_mem S a.1 a.2).1⟩ := (hι a rI rI hp_dag.symm).symm
    have h4 : Ψ0 (π rI ⟨psuDag h (a : Matrix (Fin n) (Fin n) K),
        (psuGraph_star_mem S a.1 a.2).1⟩) =
        π rI ⟨psuPsi h X (psuDag h (a : Matrix (Fin n) (Fin n) K)), _⟩ :=
      (hΨ ⟨psuDag h (a : Matrix (Fin n) (Fin n) K),
        (psuGraph_star_mem S a.1 a.2).1⟩ rI rI hp_psi.symm).symm
    rw [h1, h2, h3, h4]
    exact congrArg (π rI) (Subtype.ext (psuC3b_dag_psi S a))
  have hΘ2 : ∀ t, (Ψ0 * ι0) ((Ψ0 * ι0) t) = t := by
    intro t
    change Ψ0 (ι0 (Ψ0 (ι0 t))) = t
    rw [hcomm (ι0 t), hΨ2 (ι0 (ι0 t)), hσ2 t]
  have hΘ1 : ∃ t, (Ψ0 * ι0) t ≠ t := by
    obtain ⟨c, hc⟩ := h.exists_bar_ne
    refine ⟨algebraMap K (F rI) c, ?_⟩
    change Ψ0 (ι0 (algebraMap K (F rI) c)) ≠ algebraMap K (F rI) c
    rw [hιK c, hΨK (h.bar c)]
    intro h
    exact hc ((algebraMap K (F rI)).injective h)
  have hσ1 : ∃ t, ι0 t ≠ t := by
    obtain ⟨c, hc⟩ := h.exists_bar_ne
    refine ⟨algebraMap K (F rI) c, ?_⟩
    rw [hιK c]
    intro h
    exact hc ((algebraMap K (F rI)).injective h)
  have hkey : ∀ z : psuC3bg3_Local S P R hP F ι Ψ r, z.1 rf = 1 := by
    intro z
    have hdag : psuC3bg3_dag S P hP rI = rI := Subtype.ext hp_dag
    have hpsi : psuC3bg3_psi S P hP rI = rI := Subtype.ext hp_psi
    have e1 : ι0 (z.1 rf) * z.1 rf = 1 := by
      have hh := psuC3bg3_ι_eq_of_idx_eq P ι hdag rfl hp_dag.symm
        (z.1 ⟨psuC3bg3_dag S P hP rI, psuC3b_orbit_dag_mem rf.2⟩)
      have hcast : cast (congrArg F hdag)
          (z.1 ⟨psuC3bg3_dag S P hP rI, psuC3b_orbit_dag_mem rf.2⟩) = z.1 rf := by
        have hfarm : (⟨psuC3bg3_dag S P hP rI, psuC3b_orbit_dag_mem rf.2⟩ :
            psuC3bg3_fiber h X P R r) = rf := Subtype.ext hdag
        have hzz := psuC3bg3_z_cast' (F := F) (z := z.1) hfarm
        rwa [Subsingleton.elim (congrArg Subtype.val hfarm) hdag] at hzz
      have hEq : ι rI (psuC3bg3_dag S P hP rI) rfl
          (z.1 ⟨psuC3bg3_dag S P hP rI, psuC3b_orbit_dag_mem rf.2⟩) = ι0 (z.1 rf) :=
        (eq_of_heq hh).trans (by rw [hcast])
      rw [← hEq]
      exact z.2.1 rf
    have e2 : Ψ0 (z.1 rf) * z.1 rf = 1 := by
      have hh := psuC3bg3_Ψ_eq_of_idx_eq (X := X) P Ψ hpsi rfl hp_psi.symm
        (z.1 ⟨psuC3bg3_psi S P hP rI, psuC3b_orbit_psi_mem S rf.2⟩)
      have hcast : cast (congrArg F hpsi)
          (z.1 ⟨psuC3bg3_psi S P hP rI, psuC3b_orbit_psi_mem S rf.2⟩) = z.1 rf := by
        have hfarm : (⟨psuC3bg3_psi S P hP rI, psuC3b_orbit_psi_mem S rf.2⟩ :
            psuC3bg3_fiber h X P R r) = rf := Subtype.ext hpsi
        have hzz := psuC3bg3_z_cast' (F := F) (z := z.1) hfarm
        rwa [Subsingleton.elim (congrArg Subtype.val hfarm) hpsi] at hzz
      have hEq : Ψ rI (psuC3bg3_psi S P hP rI) rfl
          (z.1 ⟨psuC3bg3_psi S P hP rI, psuC3b_orbit_psi_mem S rf.2⟩) = Ψ0 (z.1 rf) :=
        (eq_of_heq hh).trans (by rw [hcast])
      rw [← hEq]
      exact z.2.2 rf
    have e2' : ((Ψ0 * ι0) * ι0) (z.1 rf) * z.1 rf = 1 := by
      rw [show ((Ψ0 * ι0) * ι0) (z.1 rf) = Ψ0 (z.1 rf) from by
        change Ψ0 (ι0 (ι0 (z.1 rf))) = Ψ0 (z.1 rf)
        rw [hσ2]]
      exact e2
    exact psuC3bg3_unitary_fix_apply ι0 hσ2 hσ1 (Ψ0 * ι0) hΘ2 hΘ1 (z.1 rf) e1 e2'
  have hconst : ∀ (z : psuC3bg3_Local S P R hP F ι Ψ r)
      (e : psuC3bg3_fiber h X P R r), z.1 e = 1 := by
    intro z e
    have horb : e.1.1 = r.1 ∨ e.1.1 = psuDag h r.1 ∨ e.1.1 = psuPsi h X r.1 ∨
        e.1.1 = psuDag h (psuPsi h X r.1) := by simpa [psuC3b_orbit] using e.2
    have he1 : e.1.1 = r.1 := by
      rcases horb with hc | hc | hc | hc
      · exact hc
      · exact hc.trans hp_dag
      · exact hc.trans hp_psi
      · exact (hc.trans (congrArg (psuDag h) hp_psi)).trans hp_dag
    have he : e = rf := Subtype.ext (Subtype.ext he1)
    rw [he, hkey z]
  have hUO : psuC3b_UO (2 ^ f) (blockDegree (psuAlg B) r.1) 0 = 1 := by simp [psuC3b_UO]
  haveI : Subsingleton (psuC3bg3_Local S P R hP F ι Ψ r) :=
    ⟨fun z w => by
      apply Subtype.ext
      funext e
      rw [hconst z e, hconst w e]⟩
  have hne : Nonempty (psuC3bg3_Local S P R hP F ι Ψ r) :=
    ⟨⟨fun _ => 1, by constructor <;> intro e <;> simp [map_one]⟩⟩
  rw [hUO, Nat.card_eq_one_iff_unique]
  exact ⟨inferInstance, hne⟩

private def psuC3bg3_LocalFU {f n : ℕ} {K : Type} [Field K]
    {h : UnitaryFieldData 2 f K} {X : GL (Fin n) K}
    (P : Finset (Matrix (Fin n) (Fin n) K))
    {F : {e : Matrix (Fin n) (Fin n) K // e ∈ P} → Type} [fieldF : ∀ e, Field (F e)]
    (ι : ∀ e e' : {e : Matrix (Fin n) (Fin n) K // e ∈ P},
      e'.1 = psuDag h e.1 → (F e' ≃+* F e))
    (Ψ : ∀ e e' : {e : Matrix (Fin n) (Fin n) K // e ∈ P},
      e'.1 = psuPsi h X e.1 → (F e' ≃+* F e))
    (A : Type) (key : A → {e : Matrix (Fin n) (Fin n) K // e ∈ P}) : Type :=
  {z : (a : A) → F (key a) //
    (∀ (a b : A) (he : (key b).1 = psuDag h (key a).1),
      ι (key a) (key b) he (z b) * z a = 1) ∧
    (∀ (a b : A) (he : (key b).1 = psuPsi h X (key a).1),
      Ψ (key a) (key b) he (z b) * z a = 1)}

private def psuC3bg3_piTwo {β : Type} [DecidableEq β]
    (F : β → Type) (a b : β) (hab : ∀ e : β, e = a ∨ e = b) (hne : a ≠ b) :
    ((e : β) → F e) ≃ F a × F b where
  toFun z := (z a, z b)
  invFun p := fun e =>
    if h : e = a then h ▸ p.1 else (hab e).resolve_left h ▸ p.2
  left_inv z := by
    funext e
    rcases hab e with rfl | rfl
    · simp
    · simp [hne.symm]
  right_inv p := by
    simp [hne, hne.symm]

private lemma psuC3bg3_Local_card_eq {f n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    {h : UnitaryFieldData 2 f K} {X B : GL (Fin n) K} (S : PSUGraphSetting h n X B)
    (P R : Finset (Matrix (Fin n) (Fin n) K)) (hP : PrimFamily (psuAlg B) P)
    (F : {e : Matrix (Fin n) (Fin n) K // e ∈ P} → Type) [fieldF : ∀ e, Field (F e)]
    (ι : ∀ e e' : {e : Matrix (Fin n) (Fin n) K // e ∈ P},
      e'.1 = psuDag h e.1 → (F e' ≃+* F e))
    (Ψ : ∀ e e' : {e : Matrix (Fin n) (Fin n) K // e ∈ P},
      e'.1 = psuPsi h X e.1 → (F e' ≃+* F e))
    (r : {r : Matrix (Fin n) (Fin n) K // r ∈ R}) :
    Nat.card (psuC3bg3_Local S P R hP F ι Ψ r) =
      Nat.card (psuC3bg3_LocalFU (h := h) (X := X) P ι Ψ (psuC3bg3_fiber h X P R r)
        (fun x => x.1)) := by
  apply Nat.card_congr
  refine Equiv.subtypeEquiv (Equiv.refl _) ?_
  intro z
  constructor
  · intro hz
    refine ⟨?_, ?_⟩
    · intro a b he
      have hb : b = ⟨psuC3bg3_dag S P hP a.1, psuC3b_orbit_dag_mem a.2⟩ :=
        Subtype.ext (Subtype.ext he)
      subst hb
      exact hz.1 a
    · intro a b he
      have hb : b = ⟨psuC3bg3_psi S P hP a.1, psuC3b_orbit_psi_mem S a.2⟩ :=
        Subtype.ext (Subtype.ext he)
      subst hb
      exact hz.2 a
  · intro hz
    refine ⟨?_, ?_⟩
    · intro a
      exact hz.1 a ⟨psuC3bg3_dag S P hP a.1, psuC3b_orbit_dag_mem a.2⟩ rfl
    · intro a
      exact hz.2 a ⟨psuC3bg3_psi S P hP a.1, psuC3b_orbit_psi_mem S a.2⟩ rfl

private lemma psuC3bg3_Psi_inv
    {f n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    {h : UnitaryFieldData 2 f K} {X B : GL (Fin n) K} (S : PSUGraphSetting h n X B)
    (P : Finset (Matrix (Fin n) (Fin n) K))
    {F : {e : Matrix (Fin n) (Fin n) K // e ∈ P} → Type} [fieldF : ∀ e, Field (F e)]
    [algF : ∀ e, Algebra K (F e)]
    (π : ∀ e : {e : Matrix (Fin n) (Fin n) K // e ∈ P}, psuAlg B →ₐ[K] F e)
    (hπ : ∀ e, Function.Surjective (π e))
    (Ψ : ∀ e e' : {e : Matrix (Fin n) (Fin n) K // e ∈ P},
      e'.1 = psuPsi h X e.1 → (F e' ≃+* F e))
    (hΨ : ∀ (a : psuAlg B) (e e' : {e : Matrix (Fin n) (Fin n) K // e ∈ P})
      (he : e'.1 = psuPsi h X e.1),
      π e ⟨psuPsi h X (a : Matrix (Fin n) (Fin n) K), (psuGraph_star_mem S a.1 a.2).2⟩ =
        Ψ e e' he (π e' a))
    {e e' : {e : Matrix (Fin n) (Fin n) K // e ∈ P}} (he : e'.1 = psuPsi h X e.1)
    (he' : e.1 = psuPsi h X e'.1) :
    Ψ e' e he' = (Ψ e e' he).symm := by
  let f : F e' ≃+* F e := Ψ e e' he
  let g : F e ≃+* F e' := Ψ e' e he'
  have hfg : ∀ y : F e, f (g y) = y := by
    intro y
    obtain ⟨a, rfl⟩ := hπ e y
    let a' : psuAlg B := ⟨psuPsi h X (a : Matrix (Fin n) (Fin n) K),
      (psuGraph_star_mem S a.1 a.2).2⟩
    have h1 : g (π e a) = π e' a' := (hΨ a e' e he').symm
    have h2 : f (π e' a') = π e ⟨psuPsi h X (a' : Matrix (Fin n) (Fin n) K),
      (psuGraph_star_mem S a'.1 a'.2).2⟩ := (hΨ a' e e' he).symm
    have h3 : (⟨psuPsi h X (a' : Matrix (Fin n) (Fin n) K),
        (psuGraph_star_mem S a'.1 a'.2).2⟩ : psuAlg B) = a := by
      apply Subtype.ext
      exact psuPsi_psi h X S.X_mem S.X_sq (a : Matrix (Fin n) (Fin n) K)
    rw [h1, h2, h3]
  apply RingEquiv.ext
  intro x
  calc g x = f.symm (f (g x)) := (f.symm_apply_apply (g x)).symm
    _ = f.symm x := by rw [hfg x]

private lemma psuC3bg3_comm_dagSwap
    {f n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    {h : UnitaryFieldData 2 f K} {X B : GL (Fin n) K} (S : PSUGraphSetting h n X B)
    (P : Finset (Matrix (Fin n) (Fin n) K))
    {F : {e : Matrix (Fin n) (Fin n) K // e ∈ P} → Type} [fieldF : ∀ e, Field (F e)]
    [algF : ∀ e, Algebra K (F e)]
    (π : ∀ e : {e : Matrix (Fin n) (Fin n) K // e ∈ P}, psuAlg B →ₐ[K] F e)
    (hπ : ∀ e, Function.Surjective (π e))
    (ι : ∀ e e' : {e : Matrix (Fin n) (Fin n) K // e ∈ P},
      e'.1 = psuDag h e.1 → (F e' ≃+* F e))
    (hι : ∀ (a : psuAlg B) (e e' : {e : Matrix (Fin n) (Fin n) K // e ∈ P})
      (he : e'.1 = psuDag h e.1),
      π e ⟨psuDag h (a : Matrix (Fin n) (Fin n) K), (psuGraph_star_mem S a.1 a.2).1⟩ =
        ι e e' he (π e' a))
    (Ψ : ∀ e e' : {e : Matrix (Fin n) (Fin n) K // e ∈ P},
      e'.1 = psuPsi h X e.1 → (F e' ≃+* F e))
    (hΨ : ∀ (a : psuAlg B) (e e' : {e : Matrix (Fin n) (Fin n) K // e ∈ P})
      (he : e'.1 = psuPsi h X e.1),
      π e ⟨psuPsi h X (a : Matrix (Fin n) (Fin n) K), (psuGraph_star_mem S a.1 a.2).2⟩ =
        Ψ e e' he (π e' a))
    {e e' : {e : Matrix (Fin n) (Fin n) K // e ∈ P}} (he : e'.1 = psuDag h e.1)
    (hpe : e.1 = psuPsi h X e.1) (hpe' : e'.1 = psuPsi h X e'.1) (y : F e') :
    ι e e' he (Ψ e' e' hpe' y) = Ψ e e hpe (ι e e' he y) := by
  obtain ⟨a, rfl⟩ := hπ e' y
  have h1 : Ψ e' e' hpe' (π e' a) = π e' ⟨psuPsi h X (a : Matrix (Fin n) (Fin n) K),
      (psuGraph_star_mem S a.1 a.2).2⟩ := (hΨ a e' e' hpe').symm
  have h2 : ι e e' he (π e' ⟨psuPsi h X (a : Matrix (Fin n) (Fin n) K),
      (psuGraph_star_mem S a.1 a.2).2⟩) =
      π e ⟨psuDag h (psuPsi h X (a : Matrix (Fin n) (Fin n) K)), _⟩ :=
    (hι ⟨psuPsi h X (a : Matrix (Fin n) (Fin n) K), _⟩ e e' he).symm
  have h3 : ι e e' he (π e' a) = π e ⟨psuDag h (a : Matrix (Fin n) (Fin n) K),
      (psuGraph_star_mem S a.1 a.2).1⟩ := (hι a e e' he).symm
  have h4 : Ψ e e hpe (π e ⟨psuDag h (a : Matrix (Fin n) (Fin n) K),
      (psuGraph_star_mem S a.1 a.2).1⟩) =
      π e ⟨psuPsi h X (psuDag h (a : Matrix (Fin n) (Fin n) K)), _⟩ :=
    (hΨ ⟨psuDag h (a : Matrix (Fin n) (Fin n) K), _⟩ e e hpe).symm
  rw [h1, h2, h3, h4]
  exact congrArg (π e) (Subtype.ext (psuC3b_dag_psi S a))

private lemma psuC3bg3_comm_psiSwap
    {f n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    {h : UnitaryFieldData 2 f K} {X B : GL (Fin n) K} (S : PSUGraphSetting h n X B)
    (P : Finset (Matrix (Fin n) (Fin n) K))
    {F : {e : Matrix (Fin n) (Fin n) K // e ∈ P} → Type} [fieldF : ∀ e, Field (F e)]
    [algF : ∀ e, Algebra K (F e)]
    (π : ∀ e : {e : Matrix (Fin n) (Fin n) K // e ∈ P}, psuAlg B →ₐ[K] F e)
    (hπ : ∀ e, Function.Surjective (π e))
    (ι : ∀ e e' : {e : Matrix (Fin n) (Fin n) K // e ∈ P},
      e'.1 = psuDag h e.1 → (F e' ≃+* F e))
    (hι : ∀ (a : psuAlg B) (e e' : {e : Matrix (Fin n) (Fin n) K // e ∈ P})
      (he : e'.1 = psuDag h e.1),
      π e ⟨psuDag h (a : Matrix (Fin n) (Fin n) K), (psuGraph_star_mem S a.1 a.2).1⟩ =
        ι e e' he (π e' a))
    (Ψ : ∀ e e' : {e : Matrix (Fin n) (Fin n) K // e ∈ P},
      e'.1 = psuPsi h X e.1 → (F e' ≃+* F e))
    (hΨ : ∀ (a : psuAlg B) (e e' : {e : Matrix (Fin n) (Fin n) K // e ∈ P})
      (he : e'.1 = psuPsi h X e.1),
      π e ⟨psuPsi h X (a : Matrix (Fin n) (Fin n) K), (psuGraph_star_mem S a.1 a.2).2⟩ =
        Ψ e e' he (π e' a))
    {e e' : {e : Matrix (Fin n) (Fin n) K // e ∈ P}} (he : e'.1 = psuPsi h X e.1)
    (hde : e.1 = psuDag h e.1) (hde' : e'.1 = psuDag h e'.1) (y : F e') :
    Ψ e e' he (ι e' e' hde' y) = ι e e hde (Ψ e e' he y) := by
  obtain ⟨a, rfl⟩ := hπ e' y
  have h1 : ι e' e' hde' (π e' a) = π e' ⟨psuDag h (a : Matrix (Fin n) (Fin n) K),
      (psuGraph_star_mem S a.1 a.2).1⟩ := (hι a e' e' hde').symm
  have h2 : Ψ e e' he (π e' ⟨psuDag h (a : Matrix (Fin n) (Fin n) K),
      (psuGraph_star_mem S a.1 a.2).1⟩) =
      π e ⟨psuPsi h X (psuDag h (a : Matrix (Fin n) (Fin n) K)), _⟩ :=
    (hΨ ⟨psuDag h (a : Matrix (Fin n) (Fin n) K), _⟩ e e' he).symm
  have h3 : Ψ e e' he (π e' a) = π e ⟨psuPsi h X (a : Matrix (Fin n) (Fin n) K),
      (psuGraph_star_mem S a.1 a.2).2⟩ := (hΨ a e e' he).symm
  have h4 : ι e e hde (π e ⟨psuPsi h X (a : Matrix (Fin n) (Fin n) K),
      (psuGraph_star_mem S a.1 a.2).2⟩) =
      π e ⟨psuDag h (psuPsi h X (a : Matrix (Fin n) (Fin n) K)), _⟩ :=
    (hι ⟨psuPsi h X (a : Matrix (Fin n) (Fin n) K), _⟩ e e hde).symm
  rw [h1, h2, h3, h4]
  exact congrArg (π e) (Subtype.ext (psuC3b_dag_psi S a)).symm

private lemma psuC3bg3_two_point_count {E₁ E₂ : Type} [Field E₁] [Field E₂]
    (α : E₂ ≃+* E₁) (ρ₁ : E₁ ≃+* E₁) (ρ₂ : E₂ ≃+* E₂) (hcomm : ∀ y, α (ρ₂ y) = ρ₁ (α y)) :
    Nat.card {p : E₁ × E₂ // α p.2 * p.1 = 1 ∧ α.symm p.1 * p.2 = 1 ∧
      ρ₁ p.1 * p.1 = 1 ∧ ρ₂ p.2 * p.2 = 1} = Nat.card {x : E₁ // ρ₁ x * x = 1} := by
  apply Nat.card_congr
  have hx0 : ∀ x : {x : E₁ // ρ₁ x * x = 1}, x.1 ≠ 0 := by
    intro x h0
    have h2 := x.2
    rw [h0, mul_zero] at h2
    exact zero_ne_one h2
  refine { toFun := fun p => ⟨p.1.1, p.2.2.2.1⟩
           invFun := fun x => ⟨(x.1, α.symm (x.1)⁻¹), ?_⟩
           left_inv := ?_
           right_inv := ?_ }
  · refine ⟨?_, ?_, ?_, ?_⟩
    · show α (α.symm (x.1)⁻¹) * x.1 = 1
      rw [RingEquiv.apply_symm_apply]
      exact inv_mul_cancel₀ (hx0 x)
    · show α.symm x.1 * α.symm (x.1)⁻¹ = 1
      rw [← map_mul, mul_inv_cancel₀ (hx0 x), map_one]
    · exact x.2
    · have hh := hcomm (α.symm (x.1)⁻¹)
      rw [RingEquiv.apply_symm_apply] at hh
      have h1 : ρ₂ (α.symm (x.1)⁻¹) = α.symm (ρ₁ (x.1)⁻¹) := by
        have := congrArg α.symm hh
        rwa [RingEquiv.symm_apply_apply] at this
      have h2 : ρ₁ (x.1)⁻¹ = x.1 := by
        have h3 : ρ₁ x.1 = (x.1)⁻¹ := eq_inv_of_mul_eq_one_left x.2
        rw [map_inv₀, h3, inv_inv]
      rw [h1, h2]
      show α.symm x.1 * α.symm (x.1)⁻¹ = 1
      rw [← map_mul, mul_inv_cancel₀ (hx0 x), map_one]
  · intro p
    apply Subtype.ext
    refine Prod.ext rfl ?_
    exact (congrArg α.symm (eq_inv_of_mul_eq_one_left p.2.1)).symm.trans
      (RingEquiv.symm_apply_apply α p.1.2)
  · intro x
    apply Subtype.ext
    rfl

private lemma psuC3bg3_LocalFU_pattern3 {f n : ℕ} {K : Type} [Field K]
    {h : UnitaryFieldData 2 f K} {X : GL (Fin n) K}
    (P : Finset (Matrix (Fin n) (Fin n) K))
    {F : {e : Matrix (Fin n) (Fin n) K // e ∈ P} → Type} [fieldF : ∀ e, Field (F e)]
    (ι : ∀ e e' : {e : Matrix (Fin n) (Fin n) K // e ∈ P},
      e'.1 = psuDag h e.1 → (F e' ≃+* F e))
    (Ψ : ∀ e e' : {e : Matrix (Fin n) (Fin n) K // e ∈ P},
      e'.1 = psuPsi h X e.1 → (F e' ≃+* F e))
    (A : Type) (key : A → {e : Matrix (Fin n) (Fin n) K // e ∈ P}) (a b : A) (hne : a ≠ b)
    (hcover : ∀ x : A, x = a ∨ x = b)
    (hdab : (key b).1 = psuDag h (key a).1) (hdba : (key a).1 = psuDag h (key b).1)
    (hpa : (key a).1 = psuPsi h X (key a).1) (hpb : (key b).1 = psuPsi h X (key b).1)
    (hdaa : (key a).1 ≠ psuDag h (key a).1) (hdbb : (key b).1 ≠ psuDag h (key b).1)
    (hpab : (key b).1 ≠ psuPsi h X (key a).1) (hpba : (key a).1 ≠ psuPsi h X (key b).1) :
    Nat.card (psuC3bg3_LocalFU (h := h) (X := X) P ι Ψ A key) =
      Nat.card {p : F (key a) × F (key b) //
        ι (key a) (key b) hdab p.2 * p.1 = 1 ∧ ι (key b) (key a) hdba p.1 * p.2 = 1 ∧
        Ψ (key a) (key a) hpa p.1 * p.1 = 1 ∧ Ψ (key b) (key b) hpb p.2 * p.2 = 1} := by
  classical
  apply Nat.card_congr
  refine Equiv.subtypeEquiv
    (psuC3bg3_piTwo (fun x => F (key x)) a b hcover hne) ?_
  intro z
  constructor
  · intro hz
    exact ⟨hz.1 a b hdab, hz.1 b a hdba, hz.2 a a hpa, hz.2 b b hpb⟩
  · rintro ⟨h1, h2, h3, h4⟩
    refine ⟨?_, ?_⟩
    · intro x y h'
      rcases hcover x with hx | hx <;> rcases hcover y with hy | hy
      · subst x; subst y; exact absurd h' hdaa
      · subst x; subst y; rw [Subsingleton.elim h' hdab]; exact h1
      · subst x; subst y; rw [Subsingleton.elim h' hdba]; exact h2
      · subst x; subst y; exact absurd h' hdbb
    · intro x y h'
      rcases hcover x with hx | hx <;> rcases hcover y with hy | hy
      · subst x; subst y; rw [Subsingleton.elim h' hpa]; exact h3
      · subst x; subst y; exact absurd h' hpab
      · subst x; subst y; exact absurd h' hpba
      · subst x; subst y; rw [Subsingleton.elim h' hpb]; exact h4

private lemma psuC3bg3_LocalFU_pattern1 {f n : ℕ} {K : Type} [Field K]
    {h : UnitaryFieldData 2 f K} {X : GL (Fin n) K}
    (P : Finset (Matrix (Fin n) (Fin n) K))
    {F : {e : Matrix (Fin n) (Fin n) K // e ∈ P} → Type} [fieldF : ∀ e, Field (F e)]
    (ι : ∀ e e' : {e : Matrix (Fin n) (Fin n) K // e ∈ P},
      e'.1 = psuDag h e.1 → (F e' ≃+* F e))
    (Ψ : ∀ e e' : {e : Matrix (Fin n) (Fin n) K // e ∈ P},
      e'.1 = psuPsi h X e.1 → (F e' ≃+* F e))
    (A : Type) (key : A → {e : Matrix (Fin n) (Fin n) K // e ∈ P}) (a b : A) (hne : a ≠ b)
    (hcover : ∀ x : A, x = a ∨ x = b)
    (hda : (key a).1 = psuDag h (key a).1) (hdb : (key b).1 = psuDag h (key b).1)
    (hpab : (key b).1 = psuPsi h X (key a).1) (hpba : (key a).1 = psuPsi h X (key b).1)
    (hdab : (key b).1 ≠ psuDag h (key a).1) (hdba : (key a).1 ≠ psuDag h (key b).1)
    (hpaa : (key a).1 ≠ psuPsi h X (key a).1) (hpbb : (key b).1 ≠ psuPsi h X (key b).1) :
    Nat.card (psuC3bg3_LocalFU (h := h) (X := X) P ι Ψ A key) =
      Nat.card {p : F (key a) × F (key b) //
        ι (key a) (key a) hda p.1 * p.1 = 1 ∧ ι (key b) (key b) hdb p.2 * p.2 = 1 ∧
        Ψ (key a) (key b) hpab p.2 * p.1 = 1 ∧ Ψ (key b) (key a) hpba p.1 * p.2 = 1} := by
  classical
  apply Nat.card_congr
  refine Equiv.subtypeEquiv
    (psuC3bg3_piTwo (fun x => F (key x)) a b hcover hne) ?_
  intro z
  constructor
  · intro hz
    exact ⟨hz.1 a a hda, hz.1 b b hdb, hz.2 a b hpab, hz.2 b a hpba⟩
  · rintro ⟨h1, h2, h3, h4⟩
    refine ⟨?_, ?_⟩
    · intro x y h'
      rcases hcover x with hx | hx <;> rcases hcover y with hy | hy
      · subst x; subst y; rw [Subsingleton.elim h' hda]; exact h1
      · subst x; subst y; exact absurd h' hdab
      · subst x; subst y; exact absurd h' hdba
      · subst x; subst y; rw [Subsingleton.elim h' hdb]; exact h2
    · intro x y h'
      rcases hcover x with hx | hx <;> rcases hcover y with hy | hy
      · subst x; subst y; exact absurd h' hpaa
      · subst x; subst y; rw [Subsingleton.elim h' hpab]; exact h3
      · subst x; subst y; rw [Subsingleton.elim h' hpba]; exact h4
      · subst x; subst y; exact absurd h' hpbb

private lemma psuC3bg3_local_kind1 {f n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    {h : UnitaryFieldData 2 f K} {X B : GL (Fin n) K} (S : PSUGraphSetting h n X B)
    (P R : Finset (Matrix (Fin n) (Fin n) K)) (hP : PrimFamily (psuAlg B) P)
    (F : {e : Matrix (Fin n) (Fin n) K // e ∈ P} → Type) [fieldF : ∀ e, Field (F e)]
        [algF : ∀ e, Algebra K (F e)] [finF : ∀ e, Finite (F e)]
    (hcard : ∀ e, Nat.card (F e) = Nat.card K ^ blockDegree (psuAlg B) e.1)
    (π : ∀ e : {e : Matrix (Fin n) (Fin n) K // e ∈ P}, psuAlg B →ₐ[K] F e)
    (hπ : ∀ e, Function.Surjective (π e))
    (hR : R ⊆ P)
(ι : ∀ e e' : {e : Matrix (Fin n) (Fin n) K // e ∈ P},
      e'.1 = psuDag h e.1 → (F e' ≃+* F e))
    (hι : ∀ (a : psuAlg B) (e e' : {e : Matrix (Fin n) (Fin n) K // e ∈ P})
      (he : e'.1 = psuDag h e.1),
      π e ⟨psuDag h (a : Matrix (Fin n) (Fin n) K), (psuGraph_star_mem S a.1 a.2).1⟩ =
        ι e e' he (π e' a))
    (Ψ : ∀ e e' : {e : Matrix (Fin n) (Fin n) K // e ∈ P},
      e'.1 = psuPsi h X e.1 → (F e' ≃+* F e))
    (hΨ : ∀ (a : psuAlg B) (e e' : {e : Matrix (Fin n) (Fin n) K // e ∈ P})
      (he : e'.1 = psuPsi h X e.1),
      π e ⟨psuPsi h X (a : Matrix (Fin n) (Fin n) K), (psuGraph_star_mem S a.1 a.2).2⟩ =
        Ψ e e' he (π e' a))
    (r : {r : Matrix (Fin n) (Fin n) K // r ∈ R}) (hk : psuKind h X B r.1 = 1) :
    Nat.card (psuC3bg3_Local S P R hP F ι Ψ r) =
      psuC3b_UO (2 ^ f) (blockDegree (psuAlg B) r.1) 1 := by
  classical
  obtain ⟨hp_dag, hp_psi_ne⟩ := psuC3bg3_kind_one h X B r.1 hk
  have hPr : r.1 ∈ P := hR r.2
  let rI : {e : Matrix (Fin n) (Fin n) K // e ∈ P} := ⟨r.1, hPr⟩
  let sI : {e : Matrix (Fin n) (Fin n) K // e ∈ P} := psuC3bg3_psi S P hP rI
  let rf : psuC3bg3_fiber h X P R r := ⟨rI, psuC3b_orbit_self h X r.1⟩
  let sf : psuC3bg3_fiber h X P R r := ⟨sI, psuC3b_orbit_psi_mem S rf.2⟩
  have hdag_sI : psuC3bg3_dag S P hP sI = sI := by
    apply Subtype.ext
    show psuDag h (psuPsi h X rI.1) = psuPsi h X rI.1
    rw [psuC3b_dag_psi S rI.1, hp_dag]
  have hpsi_sI : psuC3bg3_psi S P hP sI = rI := by
    apply Subtype.ext
    exact psuPsi_psi h X S.X_mem S.X_sq rI.1
  have hne : rf ≠ sf := by
    intro hh
    exact hp_psi_ne (congrArg (fun e : psuC3bg3_fiber h X P R r => e.1.1) hh).symm
  have hcover : ∀ e : psuC3bg3_fiber h X P R r, e = rf ∨ e = sf := by
    intro e
    have horb : e.1.1 = r.1 ∨ e.1.1 = psuDag h r.1 ∨ e.1.1 = psuPsi h X r.1 ∨
        e.1.1 = psuDag h (psuPsi h X r.1) := by simpa [psuC3b_orbit] using e.2
    rcases horb with hc | hc | hc | hc
    · left; exact Subtype.ext (Subtype.ext hc)
    · left; exact Subtype.ext (Subtype.ext (hc.trans hp_dag))
    · right; exact Subtype.ext (Subtype.ext hc)
    · right
      apply Subtype.ext
      apply Subtype.ext
      show e.1.1 = psuPsi h X r.1
      rw [hc, psuC3b_dag_psi S r.1, hp_dag]
  have hda : rI.1 = psuDag h rI.1 := hp_dag.symm
  have hdb : sI.1 = psuDag h sI.1 := (congrArg Subtype.val hdag_sI).symm
  have hpab : sI.1 = psuPsi h X rI.1 := rfl
  have hpba : rI.1 = psuPsi h X sI.1 := (congrArg Subtype.val hpsi_sI).symm
  have hdab : sI.1 ≠ psuDag h rI.1 := fun hh => hp_psi_ne (hh.trans hp_dag)
  have hdba : rI.1 ≠ psuDag h sI.1 := fun hh =>
    hne (Subtype.ext (Subtype.ext (hh.trans (congrArg Subtype.val hdag_sI))))
  have hpaa : rI.1 ≠ psuPsi h X rI.1 := fun hh => hp_psi_ne hh.symm
  have hpbb : sI.1 ≠ psuPsi h X sI.1 := fun hh =>
    hne ((Subtype.ext (Subtype.ext (hh.trans (congrArg Subtype.val hpsi_sI)))).symm)
  have hσ2 : ∀ x : F rI, ι rI rI hda (ι rI rI hda x) = x := by
    intro x
    obtain ⟨a, rfl⟩ := hπ rI x
    have h1 : ι rI rI hda (π rI a) = π rI ⟨psuDag h (a : Matrix (Fin n) (Fin n) K),
        (psuGraph_star_mem S a.1 a.2).1⟩ := (hι a rI rI hda).symm
    have h2 : ι rI rI hda (π rI ⟨psuDag h (a : Matrix (Fin n) (Fin n) K),
        (psuGraph_star_mem S a.1 a.2).1⟩) = π rI a := by
      have hh := (hι ⟨psuDag h (a : Matrix (Fin n) (Fin n) K),
        (psuGraph_star_mem S a.1 a.2).1⟩ rI rI hda).symm
      rwa [show (⟨psuDag h (psuDag h (a : Matrix (Fin n) (Fin n) K)), _⟩ : psuAlg B) = a
        from Subtype.ext (psuDag_dag h (a : Matrix (Fin n) (Fin n) K))] at hh
    rw [h1, h2]
  have hσ1 : ∃ x : F rI, ι rI rI hda x ≠ x := by
    obtain ⟨c, hc⟩ := h.exists_bar_ne
    refine ⟨algebraMap K (F rI) c, ?_⟩
    have hιK : ι rI rI hda (algebraMap K (F rI) c) = algebraMap K (F rI) (h.bar c) := by
      let aK : psuAlg B := algebraMap K (psuAlg B) c
      have hh := hι aK rI rI hda
      have hsub : (⟨psuDag h (aK : Matrix (Fin n) (Fin n) K),
          (psuGraph_star_mem S aK.1 aK.2).1⟩ : psuAlg B) = algebraMap K (psuAlg B) (h.bar c) := by
        apply Subtype.ext
        simp [aK, Algebra.algebraMap_eq_smul_one, psuDag_smul, psuDag_one]
      rw [hsub] at hh
      rw [show (π rI) aK = algebraMap K (F rI) c from (π rI).commutes c,
        show (π rI) (algebraMap K (psuAlg B) (h.bar c)) = algebraMap K (F rI) (h.bar c) from
          (π rI).commutes (h.bar c)] at hh
      exact hh.symm
    rw [hιK]
    intro hcon
    exact hc ((algebraMap K (F rI)).injective hcon)
  rw [psuC3bg3_Local_card_eq]
  rw [psuC3bg3_LocalFU_pattern1 (h := h) (X := X) P ι Ψ
    (psuC3bg3_fiber h X P R r) (fun x => x.1) rf sf hne hcover
    hda hdb hpab hpba hdab hdba hpaa hpbb]
  rw [show (Ψ sI rI hpba) = (Ψ rI sI hpab).symm from
    psuC3bg3_Psi_inv S P π hπ Ψ hΨ hpab hpba]
  let ee : {p : F rI × F sI // ι rI rI hda p.1 * p.1 = 1 ∧
      ι sI sI hdb p.2 * p.2 = 1 ∧ Ψ rI sI hpab p.2 * p.1 = 1 ∧
      (Ψ rI sI hpab).symm p.1 * p.2 = 1} ≃
      {p : F rI × F sI // (Ψ rI sI hpab) p.2 * p.1 = 1 ∧
      (Ψ rI sI hpab).symm p.1 * p.2 = 1 ∧ ι rI rI hda p.1 * p.1 = 1 ∧
      ι sI sI hdb p.2 * p.2 = 1} :=
    Equiv.subtypeEquiv (Equiv.refl (F rI × F sI)) (fun p => by
      constructor
      · rintro ⟨h1, h2, h3, h4⟩; exact ⟨h3, h4, h1, h2⟩
      · rintro ⟨h1, h2, h3, h4⟩; exact ⟨h3, h4, h1, h2⟩)
  rw [Nat.card_congr ee]
  rw [psuC3bg3_two_point_count (Ψ rI sI hpab) (ι rI rI hda) (ι sI sI hdb)
    (psuC3bg3_comm_psiSwap S P π hπ ι hι Ψ hΨ hpab hda hdb)]
  rw [psuC3b_field_unitary_card (E := F rI) (ι rI rI hda) hσ2 hσ1]
  rw [show psuC3b_UO (2 ^ f) (blockDegree (psuAlg B) r.1) 1 =
      (2 ^ f) ^ blockDegree (psuAlg B) r.1 + 1 from by simp [psuC3b_UO]]
  congr 1
  rw [hcard rI, h.card_eq_sq]
  rw [show ((2 ^ f) ^ 2) ^ blockDegree (psuAlg B) r.1 =
      ((2 ^ f) ^ blockDegree (psuAlg B) r.1) ^ 2 from by ring]
  exact psuC3bg3_sqrt_sq _

private lemma psuC3bg3_local_kind2 {f n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    {h : UnitaryFieldData 2 f K} {X B : GL (Fin n) K} (S : PSUGraphSetting h n X B)
    (P R : Finset (Matrix (Fin n) (Fin n) K)) (hP : PrimFamily (psuAlg B) P)
    (F : {e : Matrix (Fin n) (Fin n) K // e ∈ P} → Type) [fieldF : ∀ e, Field (F e)]
        [algF : ∀ e, Algebra K (F e)] [charF : ∀ e, CharP (F e) 2]
    (π : ∀ e : {e : Matrix (Fin n) (Fin n) K // e ∈ P}, psuAlg B →ₐ[K] F e)
    (hπ : ∀ e, Function.Surjective (π e))
    (hker : ∀ e (a : psuAlg B), π e a = 0 ↔ (a : Matrix (Fin n) (Fin n) K) * e.1 = 0)
    (hR : R ⊆ P)
(ι : ∀ e e' : {e : Matrix (Fin n) (Fin n) K // e ∈ P},
      e'.1 = psuDag h e.1 → (F e' ≃+* F e))
    (Ψ : ∀ e e' : {e : Matrix (Fin n) (Fin n) K // e ∈ P},
      e'.1 = psuPsi h X e.1 → (F e' ≃+* F e))
    (hΨ : ∀ (a : psuAlg B) (e e' : {e : Matrix (Fin n) (Fin n) K // e ∈ P})
      (he : e'.1 = psuPsi h X e.1),
      π e ⟨psuPsi h X (a : Matrix (Fin n) (Fin n) K), (psuGraph_star_mem S a.1 a.2).2⟩ =
        Ψ e e' he (π e' a))
    (r : {r : Matrix (Fin n) (Fin n) K // r ∈ R}) (hk : psuKind h X B r.1 = 2) :
    Nat.card (psuC3bg3_Local S P R hP F ι Ψ r) =
      psuC3b_UO (2 ^ f) (blockDegree (psuAlg B) r.1) 2 := by
  obtain ⟨hd, hp, ht⟩ := psuC3bg3_kind_two h X B r.1 hk
  have hPr : r.1 ∈ P := hR r.2
  let rI : {e : Matrix (Fin n) (Fin n) K // e ∈ P} := ⟨r.1, hPr⟩
  let rIA : psuAlg B := ⟨r.1, ((hP.1 r.1).mp hPr).1⟩
  let rf : psuC3bg3_fiber h X P R r := ⟨rI, psuC3b_orbit_self h X r.1⟩
  let sf : psuC3bg3_fiber h X P R r :=
    ⟨psuC3bg3_dag S P hP rI, psuC3b_orbit_dag_mem (psuC3b_orbit_self h X r.1)⟩
  have hpsi : psuC3bg3_psi S P hP rI = rI := Subtype.ext hp
  have hPsi_id : ∀ y : F rI, Ψ rI rI hp.symm y = y := by
    intro y
    obtain ⟨a, ha⟩ := hπ rI y
    have hmemA : ((a * rIA : psuAlg B) : Matrix (Fin n) (Fin n) K) ∈ psuAlg B :=
      mul_mem a.2 rIA.2
    have hh := hΨ (a * rIA) rI rI hp.symm
    have ht' : psuPsi h X ((a * rIA : psuAlg B) : Matrix (Fin n) (Fin n) K) =
        ((a * rIA : psuAlg B) : Matrix (Fin n) (Fin n) K) := ht a a.2
    rw [show (⟨psuPsi h X ((a * rIA : psuAlg B) : Matrix (Fin n) (Fin n) K),
        (psuGraph_star_mem S (a * rIA).1 hmemA).2⟩ : psuAlg B) = a * rIA from
      Subtype.ext ht'] at hh
    rw [map_mul, psuC3bg3_pi_self P hP F π hker rI, mul_one] at hh
    rw [ha] at hh
    exact hh.symm
  have hbase : ∀ z : psuC3bg3_Local S P R hP F ι Ψ r, z.1 rf = 1 := by
    intro z
    have hC2 := z.2.2 rf
    have hψeq : Ψ rI (psuC3bg3_psi S P hP rI) rfl
        (z.1 ⟨psuC3bg3_psi S P hP rI, psuC3b_orbit_psi_mem S rf.2⟩) = z.1 rf := by
      have hh := psuC3bg3_Ψ_eq_of_idx_eq P Ψ hpsi rfl hp.symm
        (z.1 ⟨psuC3bg3_psi S P hP rI, psuC3b_orbit_psi_mem S rf.2⟩)
      have hcast : cast (congrArg F hpsi)
          (z.1 ⟨psuC3bg3_psi S P hP rI, psuC3b_orbit_psi_mem S rf.2⟩) = z.1 rf := by
        have hfarm : (⟨psuC3bg3_psi S P hP rI, psuC3b_orbit_psi_mem S rf.2⟩ :
            psuC3bg3_fiber h X P R r) = rf := Subtype.ext hpsi
        have hzz := psuC3bg3_z_cast' (F := F) (z := z.1) hfarm
        rwa [Subsingleton.elim (congrArg Subtype.val hfarm) hpsi] at hzz
      exact (eq_of_heq hh).trans ((hPsi_id _).trans hcast)
    rw [hψeq] at hC2
    exact psuC3bg3_sq_eq_one hC2
  have hsf : ∀ z : psuC3bg3_Local S P R hP F ι Ψ r, z.1 sf = 1 := by
    intro z
    have hC1 := z.2.1 rf
    rw [hbase z, mul_one] at hC1
    dsimp only [rf, sf] at hC1
    have h2 := congrArg (fun w => (ι rI (psuC3bg3_dag S P hP rI) rfl).symm w) hC1
    simpa using h2
  have hconst : ∀ z : psuC3bg3_Local S P R hP F ι Ψ r,
      ∀ e : psuC3bg3_fiber h X P R r, z.1 e = 1 := by
    intro z e
    have horb : e.1.1 = r.1 ∨ e.1.1 = psuDag h r.1 ∨ e.1.1 = psuPsi h X r.1 ∨
        e.1.1 = psuDag h (psuPsi h X r.1) := by
      simpa [psuC3b_orbit] using e.2
    rcases horb with hc | hc | hc | hc
    · have he : e = rf := Subtype.ext (Subtype.ext hc)
      rw [he, hbase z]
    · have he : e = sf := Subtype.ext (Subtype.ext hc)
      rw [he, hsf z]
    · have he : e = rf := Subtype.ext (Subtype.ext (hc.trans hp))
      rw [he, hbase z]
    · have he : e = sf := Subtype.ext (Subtype.ext (hc.trans (congrArg (psuDag h) hp)))
      rw [he, hsf z]
  have hUO : psuC3b_UO (2 ^ f) (blockDegree (psuAlg B) r.1) 2 = 1 := by simp [psuC3b_UO]
  haveI : Subsingleton (psuC3bg3_Local S P R hP F ι Ψ r) :=
    ⟨fun z w => by
      apply Subtype.ext
      funext e
      rw [hconst z e, hconst w e]⟩
  have hne : Nonempty (psuC3bg3_Local S P R hP F ι Ψ r) :=
    ⟨⟨fun _ => 1, by constructor <;> intro e <;> simp [map_one]⟩⟩
  rw [hUO, Nat.card_eq_one_iff_unique]
  exact ⟨inferInstance, hne⟩

private lemma psuC3bg3_local_kind3 {f n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    {h : UnitaryFieldData 2 f K} {X B : GL (Fin n) K} (S : PSUGraphSetting h n X B)
    (P R : Finset (Matrix (Fin n) (Fin n) K)) (hP : PrimFamily (psuAlg B) P)
    (F : {e : Matrix (Fin n) (Fin n) K // e ∈ P} → Type) [fieldF : ∀ e, Field (F e)]
    [algF : ∀ e, Algebra K (F e)] [finF : ∀ e, Finite (F e)]
    (hcard : ∀ e, Nat.card (F e) = Nat.card K ^ blockDegree (psuAlg B) e.1)
    (π : ∀ e : {e : Matrix (Fin n) (Fin n) K // e ∈ P}, psuAlg B →ₐ[K] F e)
    (hπ : ∀ e, Function.Surjective (π e))
    (hker : ∀ e (a : psuAlg B), π e a = 0 ↔ (a : Matrix (Fin n) (Fin n) K) * e.1 = 0)
    (hR : R ⊆ P)
    (ι : ∀ e e' : {e : Matrix (Fin n) (Fin n) K // e ∈ P},
      e'.1 = psuDag h e.1 → (F e' ≃+* F e))
    (hι : ∀ (a : psuAlg B) (e e' : {e : Matrix (Fin n) (Fin n) K // e ∈ P})
      (he : e'.1 = psuDag h e.1),
      π e ⟨psuDag h (a : Matrix (Fin n) (Fin n) K), (psuGraph_star_mem S a.1 a.2).1⟩ =
        ι e e' he (π e' a))
    (Ψ : ∀ e e' : {e : Matrix (Fin n) (Fin n) K // e ∈ P},
      e'.1 = psuPsi h X e.1 → (F e' ≃+* F e))
    (hΨ : ∀ (a : psuAlg B) (e e' : {e : Matrix (Fin n) (Fin n) K // e ∈ P})
      (he : e'.1 = psuPsi h X e.1),
      π e ⟨psuPsi h X (a : Matrix (Fin n) (Fin n) K), (psuGraph_star_mem S a.1 a.2).2⟩ =
        Ψ e e' he (π e' a))
    (r : {r : Matrix (Fin n) (Fin n) K // r ∈ R}) (hk : psuKind h X B r.1 = 3) :
    Nat.card (psuC3bg3_Local S P R hP F ι Ψ r) =
      psuC3b_UO (2 ^ f) (blockDegree (psuAlg B) r.1) 3 := by
  classical
  obtain ⟨hdag_ne, hp_psi, hntriv⟩ := psuC3b_kind_three h X B r.1 hk
  have hPr : r.1 ∈ P := hR r.2
  let rI : {e : Matrix (Fin n) (Fin n) K // e ∈ P} := ⟨r.1, hPr⟩
  let sI : {e : Matrix (Fin n) (Fin n) K // e ∈ P} := psuC3bg3_dag S P hP rI
  let rf : psuC3bg3_fiber h X P R r := ⟨rI, psuC3b_orbit_self h X r.1⟩
  let sf : psuC3bg3_fiber h X P R r := ⟨sI, psuC3b_orbit_dag_mem rf.2⟩
  have hdag_sI : psuC3bg3_dag S P hP sI = rI := by
    apply Subtype.ext
    exact psuDag_dag h rI.1
  have hpsi_sI : psuC3bg3_psi S P hP sI = sI := by
    apply Subtype.ext
    show psuPsi h X (psuDag h rI.1) = psuDag h rI.1
    rw [← psuC3b_dag_psi S rI.1, hp_psi]
  have hne : rf ≠ sf := by
    intro hh
    exact hdag_ne (congrArg (fun e : psuC3bg3_fiber h X P R r => e.1.1) hh).symm
  have hcover : ∀ e : psuC3bg3_fiber h X P R r, e = rf ∨ e = sf := by
    intro e
    have horb : e.1.1 = r.1 ∨ e.1.1 = psuDag h r.1 ∨ e.1.1 = psuPsi h X r.1 ∨
        e.1.1 = psuDag h (psuPsi h X r.1) := by simpa [psuC3b_orbit] using e.2
    rcases horb with hc | hc | hc | hc
    · left; exact Subtype.ext (Subtype.ext hc)
    · right; exact Subtype.ext (Subtype.ext hc)
    · left; exact Subtype.ext (Subtype.ext (hc.trans hp_psi))
    · right
      apply Subtype.ext
      apply Subtype.ext
      show e.1.1 = psuDag h r.1
      rw [hc, congrArg (psuDag h) hp_psi]
  let Ψ0 : F rI ≃+* F rI := Ψ rI rI hp_psi.symm
  have hhe_sr : rI.1 = psuDag h sI.1 := (psuDag_dag h rI.1).symm
  have hhe_ss : sI.1 = psuPsi h X sI.1 := (congrArg Subtype.val hpsi_sI).symm
  have hΨ2 : ∀ x : F rI, Ψ0 (Ψ0 x) = x := by
    intro x
    obtain ⟨a, rfl⟩ := hπ rI x
    have h1 : Ψ0 (π rI a) = π rI ⟨psuPsi h X (a : Matrix (Fin n) (Fin n) K),
        (psuGraph_star_mem S a.1 a.2).2⟩ := (hΨ a rI rI hp_psi.symm).symm
    have h2 : Ψ0 (π rI ⟨psuPsi h X (a : Matrix (Fin n) (Fin n) K),
        (psuGraph_star_mem S a.1 a.2).2⟩) = π rI a := by
      have hh := (hΨ ⟨psuPsi h X (a : Matrix (Fin n) (Fin n) K),
        (psuGraph_star_mem S a.1 a.2).2⟩ rI rI hp_psi.symm).symm
      rwa [show (⟨psuPsi h X (psuPsi h X (a : Matrix (Fin n) (Fin n) K)), _⟩ : psuAlg B) = a
        from Subtype.ext (psuPsi_psi h X S.X_mem S.X_sq (a : Matrix (Fin n) (Fin n) K))] at hh
    rw [h1, h2]
  have hΨ1 : ∃ x : F rI, Ψ0 x ≠ x := by
    have hntriv' : ∃ a : Matrix (Fin n) (Fin n) K, a ∈ psuAlg B ∧
        psuPsi h X (a * r.1) ≠ a * r.1 := by
      by_contra hc
      apply hntriv
      intro a ha
      by_contra hne'
      exact hc ⟨a, ha, hne'⟩
    obtain ⟨a, ha, hne'⟩ := hntriv'
    let aA : psuAlg B := ⟨a, ha⟩
    refine ⟨π rI aA, ?_⟩
    rw [← hΨ aA rI rI hp_psi.symm]
    intro hcon
    apply hne'
    have hrA : r.1 ∈ psuAlg B := ((hP.1 r.1).mp hPr).1
    have hψmul : psuPsi h X (a * r.1) = psuPsi h X a * r.1 := by
      rw [psuPsi_mul, hp_psi]
      exact psuC3b_alg_comm B r.1 hrA (psuPsi h X a) (psuGraph_star_mem S a ha).2
    have h1 : (psuPsi h X a - a) * r.1 = 0 := by
      have hh := (hker rI (⟨psuPsi h X a, (psuGraph_star_mem S a ha).2⟩ - aA)).mp ?_
      · simpa using hh
      · rw [map_sub, hcon, sub_self]
    rw [hψmul]
    rw [Matrix.sub_mul, sub_eq_zero] at h1
    exact h1
  have hdbb : sI.1 ≠ psuDag h sI.1 :=
    fun hh => hne ((Subtype.ext (Subtype.ext (hh.trans (congrArg Subtype.val hdag_sI)))).symm)
  rw [psuC3bg3_Local_card_eq]
  rw [psuC3bg3_LocalFU_pattern3 (h := h) (X := X) P ι Ψ
    (psuC3bg3_fiber h X P R r) (fun x => x.1) rf sf hne hcover
    rfl hhe_sr hp_psi.symm hhe_ss (fun hh => hdag_ne hh.symm) hdbb
    (fun hh => hne ((Subtype.ext (Subtype.ext (hh.trans hp_psi))).symm))
    (fun hh => hne (Subtype.ext (Subtype.ext (hh.trans (congrArg Subtype.val hpsi_sI)))))]
  rw [show (ι sI rI hhe_sr) = (ι rI sI rfl).symm from
    psuC3bg3_iota_inv S P π hπ ι hι rfl hhe_sr]
  rw [psuC3bg3_two_point_count (ι rI sI rfl) Ψ0 (Ψ sI sI hhe_ss)
    (psuC3bg3_comm_dagSwap S P π hπ ι hι Ψ hΨ rfl hp_psi.symm hhe_ss)]
  rw [psuC3b_field_unitary_card (E := F rI) Ψ0 hΨ2 hΨ1]
  rw [show psuC3b_UO (2 ^ f) (blockDegree (psuAlg B) r.1) 3 =
      (2 ^ f) ^ blockDegree (psuAlg B) r.1 + 1 from by simp [psuC3b_UO]]
  congr 1
  rw [hcard rI, h.card_eq_sq]
  rw [show ((2 ^ f) ^ 2) ^ blockDegree (psuAlg B) r.1 =
      ((2 ^ f) ^ blockDegree (psuAlg B) r.1) ^ 2 from by ring]
  exact psuC3bg3_sqrt_sq _

private lemma psuC3bg3b_card_F {f n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    {h : UnitaryFieldData 2 f K} {X B : GL (Fin n) K} (S : PSUGraphSetting h n X B)
    (P : Finset (Matrix (Fin n) (Fin n) K)) (hP : PrimFamily (psuAlg B) P)
    (F : {e : Matrix (Fin n) (Fin n) K // e ∈ P} → Type) [fieldF : ∀ e, Field (F e)]
        [algF : ∀ e, Algebra K (F e)] [charF : ∀ e, CharP (F e) 2] [finF : ∀ e, Finite (F e)]
    (π : ∀ e : {e : Matrix (Fin n) (Fin n) K // e ∈ P}, psuAlg B →ₐ[K] F e)
    (hπ : ∀ e, Function.Surjective (π e))
    (hker : ∀ e (a : psuAlg B), π e a = 0 ↔ (a : Matrix (Fin n) (Fin n) K) * e.1 = 0)
    (e : {e : Matrix (Fin n) (Fin n) K // e ∈ P}) :
    Nat.card (F e) = Nat.card K ^ blockDegree (psuAlg B) e.1 := by
  obtain ⟨F0, fieldF0, algF0, finF0, charF0, π0, hπ0, hker0, hdim0, hcard0, hbij0⟩ :=
    psuC3b_block_prod S P hP
  letI := fieldF0
  have hker_eq : RingHom.ker (π e : psuAlg B →+* F e) =
      RingHom.ker (π0 e : psuAlg B →+* F0 e) := by
    ext a
    exact (hker e a).trans (hker0 e a).symm
  calc Nat.card (F e)
      = Nat.card (psuAlg B ⧸ RingHom.ker (π e : psuAlg B →+* F e)) :=
        (Nat.card_congr (RingHom.quotientKerEquivOfSurjective
          (f := (π e : psuAlg B →+* F e)) (hπ e)).toEquiv).symm
    _ = Nat.card (psuAlg B ⧸ RingHom.ker (π0 e : psuAlg B →+* F0 e)) :=
        Nat.card_congr (Ideal.quotEquivOfEq hker_eq).toEquiv
    _ = Nat.card (F0 e) :=
        Nat.card_congr (RingHom.quotientKerEquivOfSurjective
          (f := (π0 e : psuAlg B →+* F0 e)) (hπ0 e)).toEquiv
    _ = Nat.card K ^ blockDegree (psuAlg B) e.1 := hcard0 e

private lemma psuC3bg3b_dagA_psiA {f n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    {h : UnitaryFieldData 2 f K} {X B : GL (Fin n) K} (S : PSUGraphSetting h n X B)
    (a : psuAlg B) :
    psuC3bg3_dagA S (psuC3bg3_psiA S a) = psuC3bg3_psiA S (psuC3bg3_dagA S a) := by
  apply Subtype.ext
  exact psuC3b_dag_psi S (a : Matrix (Fin n) (Fin n) K)

private lemma psuC3bg3b_dagA_dagA {f n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    {h : UnitaryFieldData 2 f K} {X B : GL (Fin n) K} (S : PSUGraphSetting h n X B)
    (a : psuAlg B) : psuC3bg3_dagA S (psuC3bg3_dagA S a) = a := by
  apply Subtype.ext
  exact psuDag_dag h (a : Matrix (Fin n) (Fin n) K)

private lemma psuC3bg3b_psiA_psiA {f n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    {h : UnitaryFieldData 2 f K} {X B : GL (Fin n) K} (S : PSUGraphSetting h n X B)
    (a : psuAlg B) : psuC3bg3_psiA S (psuC3bg3_psiA S a) = a := by
  apply Subtype.ext
  exact psuPsi_psi h X S.X_mem S.X_sq (a : Matrix (Fin n) (Fin n) K)

private lemma psuC3bg3b_Ψ_apply_idx_eq {f n : ℕ} {K : Type} [Field K]
    {h : UnitaryFieldData 2 f K} {X : GL (Fin n) K}
    (P : Finset (Matrix (Fin n) (Fin n) K))
    {F : {e : Matrix (Fin n) (Fin n) K // e ∈ P} → Type} [fieldF : ∀ e, Field (F e)]
    (Ψ : ∀ e e' : {e : Matrix (Fin n) (Fin n) K // e ∈ P},
      e'.1 = psuPsi h X e.1 → (F e' ≃+* F e))
    {e e₁ e₂ : {e : Matrix (Fin n) (Fin n) K // e ∈ P}} (hidx : e₁ = e₂)
    (he₁ : e₁.1 = psuPsi h X e.1) (he₂ : e₂.1 = psuPsi h X e.1) (x : F e₁) :
    Ψ e e₂ he₂ (cast (congrArg F hidx) x) = Ψ e e₁ he₁ x := by
  subst hidx
  simp only [cast_eq]

private lemma psuC3bg3b_sqrt_cardF {f n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    {h : UnitaryFieldData 2 f K} {X B : GL (Fin n) K} (S : PSUGraphSetting h n X B)
    (P : Finset (Matrix (Fin n) (Fin n) K)) (hP : PrimFamily (psuAlg B) P)
    (F : {e : Matrix (Fin n) (Fin n) K // e ∈ P} → Type) [fieldF : ∀ e, Field (F e)]
        [algF : ∀ e, Algebra K (F e)] [charF : ∀ e, CharP (F e) 2] [finF : ∀ e, Finite (F e)]
    (π : ∀ e : {e : Matrix (Fin n) (Fin n) K // e ∈ P}, psuAlg B →ₐ[K] F e)
    (hπ : ∀ e, Function.Surjective (π e))
    (hker : ∀ e (a : psuAlg B), π e a = 0 ↔ (a : Matrix (Fin n) (Fin n) K) * e.1 = 0)
    (e : {e : Matrix (Fin n) (Fin n) K // e ∈ P}) :
    Nat.sqrt (Nat.card (F e)) = (2 ^ f) ^ blockDegree (psuAlg B) e.1 := by
  rw [psuC3bg3b_card_F S P hP F π hπ hker e, h.card]
  have hsq : (2 ^ (2 * f)) ^ blockDegree (psuAlg B) e.1 =
      ((2 ^ f) ^ blockDegree (psuAlg B) e.1) ^ 2 := by
    calc (2 ^ (2 * f)) ^ blockDegree (psuAlg B) e.1
        = 2 ^ ((2 * f) * blockDegree (psuAlg B) e.1) := (pow_mul 2 (2 * f) _).symm
      _ = 2 ^ (f * (2 * blockDegree (psuAlg B) e.1)) := by congr 1; ring
      _ = (2 ^ f) ^ (2 * blockDegree (psuAlg B) e.1) := pow_mul 2 f _
      _ = ((2 ^ f) ^ blockDegree (psuAlg B) e.1) ^ 2 := by
            rw [show 2 * blockDegree (psuAlg B) e.1 =
              blockDegree (psuAlg B) e.1 * 2 from by ring, pow_mul]
  rw [hsq, Nat.sqrt_eq']

private def psuC3bg3b_piTwoEquiv {β : Type} [DecidableEq β]
    (F : β → Type) (a b : β) (hab : ∀ e : β, e = a ∨ e = b) (hne : a ≠ b) :
    ((e : β) → F e) ≃ F a × F b where
  toFun z := (z a, z b)
  invFun p := fun e =>
    if h : e = a then h ▸ p.1 else (hab e).resolve_left h ▸ p.2
  left_inv z := by
    funext e
    rcases hab e with rfl | rfl
    · simp
    · simp [hne.symm]
  right_inv p := by
    simp [hne, hne.symm]

private def psuC3bg3b_piFourEquiv {β : Type} [DecidableEq β]
    (F : β → Type) (a b c d : β)
    (hab : ∀ e : β, e = a ∨ e = b ∨ e = c ∨ e = d)
    (hne_ab : a ≠ b) (hne_ac : a ≠ c) (hne_ad : a ≠ d)
    (hne_bc : b ≠ c) (hne_bd : b ≠ d) (hne_cd : c ≠ d) :
    ((e : β) → F e) ≃ F a × F b × F c × F d where
  toFun z := (z a, z b, z c, z d)
  invFun p := fun e =>
    if h : e = a then h ▸ p.1
    else if h2 : e = b then h2 ▸ p.2.1
    else if h3 : e = c then h3 ▸ p.2.2.1
    else (((hab e).resolve_left h).resolve_left h2).resolve_left h3 ▸ p.2.2.2
  left_inv z := by
    funext e
    rcases hab e with rfl | rfl | rfl | rfl
    · simp
    · simp [hne_ab.symm]
    · simp [hne_ac.symm, hne_bc.symm]
    · simp [hne_ad.symm, hne_bd.symm, hne_cd.symm]
  right_inv p := by
    simp [hne_ab.symm, hne_ac.symm, hne_ad.symm, hne_bc.symm, hne_bd.symm, hne_cd.symm]

private lemma psuC3bg3b_iota_inv {f n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    {h : UnitaryFieldData 2 f K} {X B : GL (Fin n) K} (S : PSUGraphSetting h n X B)
    (P : Finset (Matrix (Fin n) (Fin n) K))
    {F : {e // e ∈ P} → Type} [fieldF : ∀ e, Field (F e)]
    [algF : ∀ e, Algebra K (F e)]
    (π : ∀ e, psuAlg B →ₐ[K] F e) (hπ : ∀ e, Function.Surjective (π e))
    (ι : ∀ e e' : {e // e ∈ P}, e'.1 = psuDag h e.1 → (F e' ≃+* F e))
    (hι : ∀ (a : psuAlg B) (e e' : {e // e ∈ P}) (he : e'.1 = psuDag h e.1),
      π e ⟨psuDag h (a : Matrix (Fin n) (Fin n) K), (psuGraph_star_mem S a.1 a.2).1⟩ =
        ι e e' he (π e' a))
    {e e' : {e // e ∈ P}} (he : e'.1 = psuDag h e.1) (he' : e.1 = psuDag h e'.1) :
    ι e' e he' = (ι e e' he).symm := by
  let f : F e' ≃+* F e := ι e e' he
  let g : F e ≃+* F e' := ι e' e he'
  have hfg : ∀ y : F e, f (g y) = y := by
    intro y
    obtain ⟨a, rfl⟩ := hπ e y
    let a' : psuAlg B := ⟨psuDag h (a : Matrix (Fin n) (Fin n) K),
      (psuGraph_star_mem S a.1 a.2).1⟩
    have h1 : g (π e a) = π e' a' := (hι a e' e he').symm
    have h2 : f (π e' a') = π e ⟨psuDag h (a' : Matrix (Fin n) (Fin n) K),
      (psuGraph_star_mem S a'.1 a'.2).1⟩ := (hι a' e e' he).symm
    have h3 : (⟨psuDag h (a' : Matrix (Fin n) (Fin n) K),
        (psuGraph_star_mem S a'.1 a'.2).1⟩ : psuAlg B) = a := by
      apply Subtype.ext
      exact psuDag_dag h (a : Matrix (Fin n) (Fin n) K)
    rw [h1, h2, h3]
  apply RingEquiv.ext
  intro x
  calc g x = f.symm (f (g x)) := (f.symm_apply_apply (g x)).symm
    _ = f.symm x := by rw [hfg x]

private lemma psuC3bg3b_Ψ_inv {f n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    {h : UnitaryFieldData 2 f K} {X B : GL (Fin n) K} (S : PSUGraphSetting h n X B)
    (P : Finset (Matrix (Fin n) (Fin n) K))
    {F : {e // e ∈ P} → Type} [fieldF : ∀ e, Field (F e)]
    [algF : ∀ e, Algebra K (F e)]
    (π : ∀ e, psuAlg B →ₐ[K] F e) (hπ : ∀ e, Function.Surjective (π e))
    (Ψ : ∀ e e' : {e // e ∈ P}, e'.1 = psuPsi h X e.1 → (F e' ≃+* F e))
    (hΨ : ∀ (a : psuAlg B) (e e' : {e // e ∈ P}) (he : e'.1 = psuPsi h X e.1),
      π e ⟨psuPsi h X (a : Matrix (Fin n) (Fin n) K), (psuGraph_star_mem S a.1 a.2).2⟩ =
        Ψ e e' he (π e' a))
    {e e' : {e // e ∈ P}} (he : e'.1 = psuPsi h X e.1) (he' : e.1 = psuPsi h X e'.1) :
    Ψ e' e he' = (Ψ e e' he).symm := by
  let f : F e' ≃+* F e := Ψ e e' he
  let g : F e ≃+* F e' := Ψ e' e he'
  have hfg : ∀ y : F e, f (g y) = y := by
    intro y
    obtain ⟨a, rfl⟩ := hπ e y
    let a' : psuAlg B := ⟨psuPsi h X (a : Matrix (Fin n) (Fin n) K),
      (psuGraph_star_mem S a.1 a.2).2⟩
    have h1 : g (π e a) = π e' a' := (hΨ a e' e he').symm
    have h2 : f (π e' a') = π e ⟨psuPsi h X (a' : Matrix (Fin n) (Fin n) K),
      (psuGraph_star_mem S a'.1 a'.2).2⟩ := (hΨ a' e e' he).symm
    have h3 : (⟨psuPsi h X (a' : Matrix (Fin n) (Fin n) K),
        (psuGraph_star_mem S a'.1 a'.2).2⟩ : psuAlg B) = a := by
      apply Subtype.ext
      exact psuPsi_psi h X S.X_mem S.X_sq (a : Matrix (Fin n) (Fin n) K)
    rw [h1, h2, h3]
  apply RingEquiv.ext
  intro x
  calc g x = f.symm (f (g x)) := (f.symm_apply_apply (g x)).symm
    _ = f.symm x := by rw [hfg x]

private lemma psuC3bg3b_ι_apply_idx_eq {f n : ℕ} {K : Type} [Field K]
    {h : UnitaryFieldData 2 f K}
    (P : Finset (Matrix (Fin n) (Fin n) K))
    {F : {e : Matrix (Fin n) (Fin n) K // e ∈ P} → Type} [fieldF : ∀ e, Field (F e)]
    (ι : ∀ e e' : {e : Matrix (Fin n) (Fin n) K // e ∈ P},
      e'.1 = psuDag h e.1 → (F e' ≃+* F e))
    {e e₁ e₂ : {e : Matrix (Fin n) (Fin n) K // e ∈ P}} (hidx : e₁ = e₂)
    (he₁ : e₁.1 = psuDag h e.1) (he₂ : e₂.1 = psuDag h e.1) (x : F e₁) :
    ι e e₂ he₂ (cast (congrArg F hidx) x) = ι e e₁ he₁ x := by
  subst hidx
  simp only [cast_eq]

private lemma psuC3bg3b_pair_lhs_inv {E E' : Type} [Field E] [Field E'] (ι0 : E ≃+* E')
    {x : E'} {y : E} (h1 : ι0 y * x = 1) : ι0.symm x * y = 1 := by
  have hx : x ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at h1
    exact zero_ne_one h1
  have h : ι0 y = x⁻¹ := eq_inv_of_mul_eq_one_left h1
  have hy : y = ι0.symm (x⁻¹) := by
    rw [← h, RingEquiv.symm_apply_apply]
  have hx' : ι0.symm x ≠ 0 := fun h0 =>
    hx (by rw [← RingEquiv.apply_symm_apply ι0 x, h0, map_zero])
  rw [hy, map_inv₀]
  exact mul_inv_cancel₀ hx'

private lemma psuC3bg3b_pair_rhs_inv {E E' : Type} [Field E] [Field E']
    (Ψ0 : E ≃+* E') {x : E'} {y : E} (h2 : Ψ0 y * x = 1) :
    Ψ0.symm x * y = 1 := by
  have hx : x ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at h2
    exact zero_ne_one h2
  have h2' : Ψ0 y = x⁻¹ := eq_inv_of_mul_eq_one_left h2
  have hyΨ : y = Ψ0.symm (x⁻¹) := by rw [← h2', RingEquiv.symm_apply_apply]
  have hx' : Ψ0.symm x ≠ 0 := fun h0 =>
    hx (by rw [← RingEquiv.apply_symm_apply Ψ0 x, h0, map_zero])
  rw [hyΨ, map_inv₀]
  exact mul_inv_cancel₀ hx'

private lemma psuC3bg3b_kind_four {f n : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K)
    (X B : GL (Fin n) K) (e : Matrix (Fin n) (Fin n) K) (hk : psuKind h X B e = 4) :
    psuDag h e ≠ e ∧ psuPsi h X e = psuDag h e ∧ psuPsi h X e ≠ e := by
  unfold psuKind at hk
  by_cases hdd : psuDag h e = e
  · rw [if_pos hdd] at hk; split_ifs at hk <;> omega
  · rw [if_neg hdd] at hk
    by_cases hpp : psuPsi h X e = e
    · rw [if_pos hpp] at hk; split_ifs at hk <;> omega
    · rw [if_neg hpp] at hk
      by_cases h4 : psuPsi h X e = psuDag h e
      · rw [if_pos h4] at hk
        exact ⟨hdd, h4, hpp⟩
      · rw [if_neg h4] at hk; omega

private lemma psuC3bg3b_kind_five {f n : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K)
    (X B : GL (Fin n) K) (e : Matrix (Fin n) (Fin n) K) (hk : psuKind h X B e = 5) :
    psuDag h e ≠ e ∧ psuPsi h X e ≠ e ∧ psuPsi h X e ≠ psuDag h e := by
  unfold psuKind at hk
  by_cases hdd : psuDag h e = e
  · rw [if_pos hdd] at hk; split_ifs at hk <;> omega
  · rw [if_neg hdd] at hk
    by_cases hpp : psuPsi h X e = e
    · rw [if_pos hpp] at hk; split_ifs at hk <;> omega
    · rw [if_neg hpp] at hk
      by_cases h4 : psuPsi h X e = psuDag h e
      · rw [if_pos h4] at hk; omega
      · rw [if_neg h4] at hk
        exact ⟨hdd, hpp, h4⟩

private lemma psuC3bg3_local_kind4 {f n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    {h : UnitaryFieldData 2 f K} {X B : GL (Fin n) K} (S : PSUGraphSetting h n X B)
    (P R : Finset (Matrix (Fin n) (Fin n) K)) (hP : PrimFamily (psuAlg B) P)
    (F : {e : Matrix (Fin n) (Fin n) K // e ∈ P} → Type) [fieldF : ∀ e, Field (F e)]
        [algF : ∀ e, Algebra K (F e)] [charF : ∀ e, CharP (F e) 2] [finF : ∀ e, Finite (F e)]
    (π : ∀ e : {e : Matrix (Fin n) (Fin n) K // e ∈ P}, psuAlg B →ₐ[K] F e)
    (hπ : ∀ e, Function.Surjective (π e))
    (hker : ∀ e (a : psuAlg B), π e a = 0 ↔ (a : Matrix (Fin n) (Fin n) K) * e.1 = 0)
    (hR : R ⊆ P)
(ι : ∀ e e' : {e : Matrix (Fin n) (Fin n) K // e ∈ P},
      e'.1 = psuDag h e.1 → (F e' ≃+* F e))
    (hι : ∀ (a : psuAlg B) (e e' : {e : Matrix (Fin n) (Fin n) K // e ∈ P})
      (he : e'.1 = psuDag h e.1),
      π e ⟨psuDag h (a : Matrix (Fin n) (Fin n) K), (psuGraph_star_mem S a.1 a.2).1⟩ =
        ι e e' he (π e' a))
    (Ψ : ∀ e e' : {e : Matrix (Fin n) (Fin n) K // e ∈ P},
      e'.1 = psuPsi h X e.1 → (F e' ≃+* F e))
    (hΨ : ∀ (a : psuAlg B) (e e' : {e : Matrix (Fin n) (Fin n) K // e ∈ P})
      (he : e'.1 = psuPsi h X e.1),
      π e ⟨psuPsi h X (a : Matrix (Fin n) (Fin n) K), (psuGraph_star_mem S a.1 a.2).2⟩ =
        Ψ e e' he (π e' a))
    (r : {r : Matrix (Fin n) (Fin n) K // r ∈ R}) (hk : psuKind h X B r.1 = 4) :
    Nat.card (psuC3bg3_Local S P R hP F ι Ψ r) =
      psuC3b_UO (2 ^ f) (blockDegree (psuAlg B) r.1) 4 := by
  classical
  obtain ⟨hd, hp4, hpn⟩ := psuC3bg3b_kind_four h X B r.1 hk
  have hPr : r.1 ∈ P := hR r.2
  let rI : {e : Matrix (Fin n) (Fin n) K // e ∈ P} := ⟨r.1, hPr⟩
  let dI : {e : Matrix (Fin n) (Fin n) K // e ∈ P} := psuC3bg3_dag S P hP rI
  let rf : psuC3bg3_fiber h X P R r := ⟨rI, psuC3b_orbit_self h X r.1⟩
  let sf : psuC3bg3_fiber h X P R r := ⟨dI, psuC3b_orbit_dag_mem rf.2⟩
  let pf : psuC3bg3_fiber h X P R r :=
    ⟨psuC3bg3_psi S P hP rI, psuC3b_orbit_psi_mem S rf.2⟩
  have hhpd : psuC3bg3_psi S P hP rI = dI := Subtype.ext hp4
  have hpsf : pf = sf := Subtype.ext hhpd
  let ι0 : F dI ≃+* F rI := ι rI dI rfl
  let Ψ0 : F dI ≃+* F rI := Ψ rI dI hp4.symm
  let Θ : F rI ≃+* F rI := (ι0.symm).trans Ψ0
  have hcover : ∀ e : psuC3bg3_fiber h X P R r, e = rf ∨ e = sf := by
    intro e
    have hx : e.1.1 ∈ psuC3b_orbit h X r.1 := e.2
    simp only [psuC3b_orbit, Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with h | h | h | h
    · left; exact Subtype.ext (Subtype.ext h)
    · right; exact Subtype.ext (Subtype.ext h)
    · right; exact Subtype.ext (Subtype.ext (h.trans hp4))
    · left; exact Subtype.ext (Subtype.ext (h.trans (by rw [hp4, psuDag_dag])))
  have hnes : rf ≠ sf := by
    intro hcon
    have h : r.1 = psuDag h r.1 := by
      have hh := congrArg (fun x : psuC3bg3_fiber h X P R r => x.1.1) hcon
      simpa [rf, sf, dI, rI, psuC3bg3_dag] using hh
    exact hd h.symm
  have hι0_symm : ∀ a : psuAlg B, ι0.symm (π rI a) = π dI (psuC3bg3_dagA S a) := by
    intro a
    rw [RingEquiv.symm_apply_eq]
    have h1 : π rI (psuC3bg3_dagA S (psuC3bg3_dagA S a)) =
        ι0 (π dI (psuC3bg3_dagA S a)) :=
      hι (psuC3bg3_dagA S a) rI dI rfl
    rwa [psuC3bg3b_dagA_dagA S a] at h1
  have hΨ0_apply : ∀ a : psuAlg B, Ψ0 (π dI a) = π rI (psuC3bg3_psiA S a) := by
    intro a
    exact (hΨ a rI dI hp4.symm).symm
  have hΘ_apply : ∀ a : psuAlg B,
      Θ (π rI a) = π rI (psuC3bg3_psiA S (psuC3bg3_dagA S a)) := by
    intro a
    change Ψ0 (ι0.symm (π rI a)) = _
    rw [hι0_symm a, hΨ0_apply (psuC3bg3_dagA S a)]
  have hΘ2 : ∀ t, Θ (Θ t) = t := by
    intro t
    obtain ⟨a, rfl⟩ := hπ rI t
    rw [hΘ_apply a, hΘ_apply (psuC3bg3_psiA S (psuC3bg3_dagA S a))]
    congr 1
    rw [psuC3bg3b_dagA_psiA S (psuC3bg3_dagA S a), psuC3bg3b_dagA_dagA S a,
      psuC3bg3b_psiA_psiA S a]
  have hΨK : ∀ c : K, Ψ0 (algebraMap K (F dI) c) = algebraMap K (F rI) c := by
    intro c
    let aK : psuAlg B := algebraMap K (psuAlg B) c
    have hh := hΨ aK rI dI hp4.symm
    have hsub : (⟨psuPsi h X (aK : Matrix (Fin n) (Fin n) K),
        (psuGraph_star_mem S aK.1 aK.2).2⟩ : psuAlg B) = algebraMap K (psuAlg B) c := by
      apply Subtype.ext
      simp [aK, Algebra.algebraMap_eq_smul_one, psuPsi_smul, psuPsi_one]
    rw [hsub] at hh
    rw [show (π rI) aK = algebraMap K (F rI) c from (π rI).commutes c] at hh
    rw [show (π dI) aK = algebraMap K (F dI) c from (π dI).commutes c] at hh
    exact hh.symm
  have hιK : ∀ c : K, ι0 (algebraMap K (F dI) c) = algebraMap K (F rI) (h.bar c) := by
    intro c
    let aK : psuAlg B := algebraMap K (psuAlg B) c
    have hh := hι aK rI dI rfl
    have hsub : (⟨psuDag h (aK : Matrix (Fin n) (Fin n) K),
        (psuGraph_star_mem S aK.1 aK.2).1⟩ : psuAlg B) = algebraMap K (psuAlg B) (h.bar c) := by
      apply Subtype.ext
      simp [aK, Algebra.algebraMap_eq_smul_one, psuDag_smul, psuDag_one]
    rw [hsub] at hh
    rw [show (π rI) (algebraMap K (psuAlg B) (h.bar c)) = algebraMap K (F rI) (h.bar c) from
        (π rI).commutes (h.bar c)] at hh
    rw [show (π dI) aK = algebraMap K (F dI) c from (π dI).commutes c] at hh
    exact hh.symm
  have hιsymmK : ∀ c : K, ι0.symm (algebraMap K (F rI) c) = algebraMap K (F dI) (h.bar c) := by
    intro c
    rw [RingEquiv.symm_apply_eq, hιK (h.bar c), h.bar_bar]
  have hΘ_alg : ∀ c : K, Θ (algebraMap K (F rI) c) = algebraMap K (F rI) (h.bar c) := by
    intro c
    change Ψ0 (ι0.symm (algebraMap K (F rI) c)) = _
    rw [hιsymmK c, hΨK (h.bar c)]
  have hΘ1 : ∃ t, Θ t ≠ t := by
    obtain ⟨c, hc⟩ := h.exists_bar_ne
    refine ⟨algebraMap K (F rI) c, ?_⟩
    rw [hΘ_alg c]
    intro h
    exact hc ((algebraMap K (F rI)).injective h)
  let ePi := psuC3bg3b_piTwoEquiv (fun e : psuC3bg3_fiber h X P R r => F e.1) rf sf hcover hnes
  have hpred : ∀ z : (e : psuC3bg3_fiber h X P R r) → F e.1,
      (psuC3bg3_C1r S P R hP F ι r z ∧ psuC3bg3_C2r S P R hP F Ψ r z) ↔
        (ι0 (ePi z).2 * (ePi z).1 = 1 ∧ Ψ0 (ePi z).2 * (ePi z).1 = 1) := by
    intro z
    constructor
    · intro hz
      obtain ⟨h1, h2⟩ := hz
      refine ⟨?_, ?_⟩
      · simpa [ePi, psuC3bg3b_piTwoEquiv, ι0, rf, sf, dI, rI] using h1 rf
      · have hcast : cast (congrArg F hhpd) (z pf) = z sf := by
          rw [show hhpd = congrArg Subtype.val hpsf from Subsingleton.elim _ _]
          exact psuC3bg3_z_cast' hpsf
        have hh := psuC3bg3b_Ψ_apply_idx_eq (X := X) P Ψ hhpd rfl hp4.symm (z pf)
        rw [hcast] at hh
        have hEq : Ψ0 (z sf) * z rf = 1 := by rw [hh]; exact h2 rf
        simpa [ePi, psuC3bg3b_piTwoEquiv, Ψ0, rf, sf, dI, rI] using hEq
    · intro hp
      obtain ⟨hp1, hp2⟩ := hp
      have hp1' : ι0 (z sf) * z rf = 1 := by
        simpa [ePi, psuC3bg3b_piTwoEquiv, rf, sf, dI, rI] using hp1
      have hp2' : Ψ0 (z sf) * z rf = 1 := by
        simpa [ePi, psuC3bg3b_piTwoEquiv, rf, sf, dI, rI] using hp2
      constructor
      · intro e
        rcases hcover e with rfl | rfl
        · simpa [ePi, psuC3bg3b_piTwoEquiv, ι0, rf, sf, dI, rI] using hp1
        · have hdag : psuC3bg3_dag S P hP dI = rI := Subtype.ext (psuDag_dag h rI.1)
          have hfib : (⟨psuC3bg3_dag S P hP dI, psuC3b_orbit_dag_mem sf.2⟩ :
              psuC3bg3_fiber h X P R r) = rf := Subtype.ext (Subtype.ext (psuDag_dag h rI.1))
          have hcast : cast (congrArg F hdag)
              (z ⟨psuC3bg3_dag S P hP dI, psuC3b_orbit_dag_mem sf.2⟩) = z rf := by
            rw [show hdag = congrArg Subtype.val hfib from Subsingleton.elim _ _]
            exact psuC3bg3_z_cast' hfib
          have hh := psuC3bg3b_ι_apply_idx_eq P ι hdag rfl (psuDag_dag h rI.1).symm
            (z ⟨psuC3bg3_dag S P hP dI, psuC3b_orbit_dag_mem sf.2⟩)
          rw [hcast] at hh
          have hinv := psuC3bg3b_iota_inv S P π hπ ι hι (e := rI) (e' := dI)
            rfl (psuDag_dag h rI.1).symm
          have hgoal : ι dI (psuC3bg3_dag S P hP dI) rfl
              (z ⟨psuC3bg3_dag S P hP dI, psuC3b_orbit_dag_mem sf.2⟩) * z sf = 1 := by
            rw [← hh, hinv]
            exact psuC3bg3b_pair_lhs_inv ι0 hp1'
          simpa using hgoal
      · intro e
        rcases hcover e with rfl | rfl
        · have hcast : cast (congrArg F hhpd) (z pf) = z sf := by
            rw [show hhpd = congrArg Subtype.val hpsf from Subsingleton.elim _ _]
            exact psuC3bg3_z_cast' hpsf
          have hh := psuC3bg3b_Ψ_apply_idx_eq (X := X) P Ψ hhpd rfl hp4.symm (z pf)
          rw [hcast] at hh
          have hgoal : Ψ rI (psuC3bg3_psi S P hP rI) rfl (z pf) * z rf = 1 := by
            rw [← hh]; exact hp2'
          simpa [ePi, psuC3bg3b_piTwoEquiv, rf, sf, dI, rI, pf] using hgoal
        · have hpsi_eq : psuC3bg3_psi S P hP dI = rI := by
            apply Subtype.ext
            show psuPsi h X (psuDag h rI.1) = rI.1
            rw [← psuC3b_dag_psi S rI.1, hp4, psuDag_dag]
          have hfib : (⟨psuC3bg3_psi S P hP dI, psuC3b_orbit_psi_mem S sf.2⟩ :
              psuC3bg3_fiber h X P R r) = rf := Subtype.ext hpsi_eq
          have hcast : cast (congrArg F hpsi_eq)
              (z ⟨psuC3bg3_psi S P hP dI, psuC3b_orbit_psi_mem S sf.2⟩) = z rf := by
            rw [show hpsi_eq = congrArg Subtype.val hfib from Subsingleton.elim _ _]
            exact psuC3bg3_z_cast' hfib
          have he₂ : rI.1 = psuPsi h X dI.1 := by
            show r.1 = psuPsi h X (psuDag h r.1)
            rw [← psuC3b_dag_psi S r.1, hp4, psuDag_dag]
          have hh := psuC3bg3b_Ψ_apply_idx_eq (X := X) P Ψ hpsi_eq rfl he₂
            (z ⟨psuC3bg3_psi S P hP dI, psuC3b_orbit_psi_mem S sf.2⟩)
          rw [hcast] at hh
          have hinv := psuC3bg3b_Ψ_inv S P π hπ Ψ hΨ (e := rI) (e' := dI) hp4.symm he₂
          have hgoal : Ψ dI (psuC3bg3_psi S P hP dI) rfl
              (z ⟨psuC3bg3_psi S P hP dI, psuC3b_orbit_psi_mem S sf.2⟩) * z sf = 1 := by
            rw [← hh, hinv]
            exact psuC3bg3b_pair_rhs_inv Ψ0 hp2'
          simpa using hgoal
  let eFix : {p : F rI × F dI // ι0 p.2 * p.1 = 1 ∧ Ψ0 p.2 * p.1 = 1} ≃
      {u : (F rI)ˣ // Θ (u : F rI) = (u : F rI)} :=
    { toFun := fun p => by
        have hx0 : p.1.1 ≠ 0 := by
          intro h0
          have hh := p.2.1
          rw [h0, mul_zero] at hh
          exact zero_ne_one hh
        refine ⟨Units.mk0 p.1.1 hx0, ?_⟩
        have h1' : ι0 p.1.2 = p.1.1⁻¹ := eq_inv_of_mul_eq_one_left p.2.1
        have h2' : Ψ0 p.1.2 = p.1.1⁻¹ := eq_inv_of_mul_eq_one_left p.2.2
        have hy : p.1.2 = (ι0.symm p.1.1)⁻¹ := by
          rw [← RingEquiv.symm_apply_apply ι0 p.1.2, h1', map_inv₀]
        change Ψ0 (ι0.symm p.1.1) = p.1.1
        apply inv_injective
        rw [← map_inv₀, ← hy, h2']
      invFun := fun u => ⟨((u.1 : F rI), (ι0.symm (u.1 : F rI))⁻¹), by
          show ι0 ((ι0.symm (u.1 : F rI))⁻¹) * (u.1 : F rI) = 1
          rw [map_inv₀, RingEquiv.apply_symm_apply]
          exact inv_mul_cancel₀ (Units.ne_zero u.1), by
          show Ψ0 ((ι0.symm (u.1 : F rI))⁻¹) * (u.1 : F rI) = 1
          rw [map_inv₀, show Ψ0 (ι0.symm (u.1 : F rI)) = (u.1 : F rI) from u.2]
          exact inv_mul_cancel₀ (Units.ne_zero u.1)⟩
      left_inv := fun p => by
        apply Subtype.ext
        apply Prod.ext
        · rfl
        · have h1' : ι0 p.1.2 = p.1.1⁻¹ := eq_inv_of_mul_eq_one_left p.2.1
          have hy : p.1.2 = (ι0.symm p.1.1)⁻¹ := by
            rw [← RingEquiv.symm_apply_apply ι0 p.1.2, h1', map_inv₀]
          exact hy.symm
      right_inv := fun u => Subtype.ext (Units.ext rfl) }
  have hcard : Nat.card (psuC3bg3_Local S P R hP F ι Ψ r) =
      Nat.card {u : (F rI)ˣ // Θ (u : F rI) = (u : F rI)} :=
    Nat.card_congr ((Equiv.subtypeEquiv ePi hpred).trans eFix)
  rw [hcard, psuC3b_field_fix_units_card Θ hΘ2 hΘ1,
    psuC3bg3b_sqrt_cardF S P hP F π hπ hker rI]
  rw [show psuC3b_UO (2 ^ f) (blockDegree (psuAlg B) r.1) 4 =
      (2 ^ f) ^ blockDegree (psuAlg B) r.1 - 1 from by simp [psuC3b_UO]]

private lemma psuC3bg3_local_kind5 {f n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    {h : UnitaryFieldData 2 f K} {X B : GL (Fin n) K} (S : PSUGraphSetting h n X B)
    (P R : Finset (Matrix (Fin n) (Fin n) K)) (hP : PrimFamily (psuAlg B) P)
    (F : {e : Matrix (Fin n) (Fin n) K // e ∈ P} → Type) [fieldF : ∀ e, Field (F e)]
        [algF : ∀ e, Algebra K (F e)] [charF : ∀ e, CharP (F e) 2] [finF : ∀ e, Finite (F e)]
    (π : ∀ e : {e : Matrix (Fin n) (Fin n) K // e ∈ P}, psuAlg B →ₐ[K] F e)
    (hπ : ∀ e, Function.Surjective (π e))
    (hker : ∀ e (a : psuAlg B), π e a = 0 ↔ (a : Matrix (Fin n) (Fin n) K) * e.1 = 0)
    (hR : R ⊆ P)
(ι : ∀ e e' : {e : Matrix (Fin n) (Fin n) K // e ∈ P},
      e'.1 = psuDag h e.1 → (F e' ≃+* F e))
    (hι : ∀ (a : psuAlg B) (e e' : {e : Matrix (Fin n) (Fin n) K // e ∈ P})
      (he : e'.1 = psuDag h e.1),
      π e ⟨psuDag h (a : Matrix (Fin n) (Fin n) K), (psuGraph_star_mem S a.1 a.2).1⟩ =
        ι e e' he (π e' a))
    (Ψ : ∀ e e' : {e : Matrix (Fin n) (Fin n) K // e ∈ P},
      e'.1 = psuPsi h X e.1 → (F e' ≃+* F e))
    (hΨ : ∀ (a : psuAlg B) (e e' : {e : Matrix (Fin n) (Fin n) K // e ∈ P})
      (he : e'.1 = psuPsi h X e.1),
      π e ⟨psuPsi h X (a : Matrix (Fin n) (Fin n) K), (psuGraph_star_mem S a.1 a.2).2⟩ =
        Ψ e e' he (π e' a))
    (r : {r : Matrix (Fin n) (Fin n) K // r ∈ R}) (hk : psuKind h X B r.1 = 5) :
    Nat.card (psuC3bg3_Local S P R hP F ι Ψ r) =
      psuC3b_UO (2 ^ f) (blockDegree (psuAlg B) r.1) 5 := by
  classical
  obtain ⟨hd, hp, h4⟩ := psuC3bg3b_kind_five h X B r.1 hk
  have hPr : r.1 ∈ P := hR r.2
  let rI : {e : Matrix (Fin n) (Fin n) K // e ∈ P} := ⟨r.1, hPr⟩
  let dI : {e : Matrix (Fin n) (Fin n) K // e ∈ P} := psuC3bg3_dag S P hP rI
  let cI : {e : Matrix (Fin n) (Fin n) K // e ∈ P} := psuC3bg3_psi S P hP rI
  let eI : {e : Matrix (Fin n) (Fin n) K // e ∈ P} := psuC3bg3_dag S P hP cI
  let rf : psuC3bg3_fiber h X P R r := ⟨rI, psuC3b_orbit_self h X r.1⟩
  let sf : psuC3bg3_fiber h X P R r := ⟨dI, psuC3b_orbit_dag_mem rf.2⟩
  let cf : psuC3bg3_fiber h X P R r := ⟨cI, psuC3b_orbit_psi_mem S rf.2⟩
  let df : psuC3bg3_fiber h X P R r := ⟨eI, psuC3b_orbit_dag_mem cf.2⟩
  have hne_ab : rf ≠ sf := by
    intro hcon
    have hx : r.1 = psuDag h r.1 := by
      have hh := congrArg (fun x : psuC3bg3_fiber h X P R r => x.1.1) hcon
      simpa [rf, sf, dI, rI, psuC3bg3_dag] using hh
    exact hd hx.symm
  have hne_ac : rf ≠ cf := by
    intro hcon
    have hx : r.1 = psuPsi h X r.1 := by
      have hh := congrArg (fun x : psuC3bg3_fiber h X P R r => x.1.1) hcon
      simpa [rf, cf, cI, rI, psuC3bg3_psi] using hh
    exact hp hx.symm
  have hne_ad : rf ≠ df := by
    intro hcon
    have hx : r.1 = psuDag h (psuPsi h X r.1) := by
      have hh := congrArg (fun x : psuC3bg3_fiber h X P R r => x.1.1) hcon
      simpa [rf, df, eI, cI, rI, psuC3bg3_dag, psuC3bg3_psi] using hh
    have h2 : psuPsi h X r.1 = psuDag h r.1 := by
      have h3 := congrArg (psuDag h) hx
      rw [psuDag_dag] at h3
      exact h3.symm
    exact h4 h2
  have hne_bc : sf ≠ cf := by
    intro hcon
    have hx : psuDag h r.1 = psuPsi h X r.1 := by
      have hh := congrArg (fun x : psuC3bg3_fiber h X P R r => x.1.1) hcon
      simpa [sf, cf, dI, cI, rI, psuC3bg3_dag, psuC3bg3_psi] using hh
    exact h4 hx.symm
  have hne_bd : sf ≠ df := by
    intro hcon
    have hx : psuDag h r.1 = psuDag h (psuPsi h X r.1) := by
      have hh := congrArg (fun x : psuC3bg3_fiber h X P R r => x.1.1) hcon
      simpa [sf, df, dI, eI, cI, rI, psuC3bg3_dag, psuC3bg3_psi] using hh
    have h2 : r.1 = psuPsi h X r.1 := by
      have h3 := congrArg (psuDag h) hx
      rw [psuDag_dag, psuDag_dag] at h3
      exact h3
    exact hp h2.symm
  have hne_cd : cf ≠ df := by
    intro hcon
    have hx : psuPsi h X r.1 = psuDag h (psuPsi h X r.1) := by
      have hh := congrArg (fun x : psuC3bg3_fiber h X P R r => x.1.1) hcon
      simpa [cf, df, cI, eI, rI, psuC3bg3_dag, psuC3bg3_psi] using hh
    have h2 : r.1 = psuDag h r.1 := by
      have h3 := congrArg (psuPsi h X) hx
      rw [psuPsi_psi h X S.X_mem S.X_sq, ← psuC3b_dag_psi S (psuPsi h X r.1),
        psuPsi_psi h X S.X_mem S.X_sq] at h3
      exact h3
    exact hd h2.symm
  have hcover4 : ∀ e : psuC3bg3_fiber h X P R r, e = rf ∨ e = sf ∨ e = cf ∨ e = df := by
    intro e
    have hx : e.1.1 ∈ psuC3b_orbit h X r.1 := e.2
    simp only [psuC3b_orbit, Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with h | h | h | h
    · left; exact Subtype.ext (Subtype.ext h)
    · right; left; exact Subtype.ext (Subtype.ext h)
    · right; right; left; exact Subtype.ext (Subtype.ext h)
    · right; right; right; exact Subtype.ext (Subtype.ext h)
  let ι0 : F dI ≃+* F rI := ι rI dI rfl
  let Ψ0 : F cI ≃+* F rI := Ψ rI cI rfl
  let ι1 : F eI ≃+* F cI := ι cI eI rfl
  let Ψ1 : F eI ≃+* F dI := Ψ dI eI (psuC3b_dag_psi S r.1)
  have hΨ0_symm : ∀ a : psuAlg B, Ψ0.symm (π rI a) = π cI (psuC3bg3_psiA S a) := by
    intro a
    rw [RingEquiv.symm_apply_eq]
    have h1 : π rI (psuC3bg3_psiA S (psuC3bg3_psiA S a)) =
        Ψ0 (π cI (psuC3bg3_psiA S a)) :=
      hΨ (psuC3bg3_psiA S a) rI cI rfl
    rwa [psuC3bg3b_psiA_psiA S a] at h1
  have hι0_symm : ∀ a : psuAlg B, ι0.symm (π rI a) = π dI (psuC3bg3_dagA S a) := by
    intro a
    rw [RingEquiv.symm_apply_eq]
    have h1 : π rI (psuC3bg3_dagA S (psuC3bg3_dagA S a)) =
        ι0 (π dI (psuC3bg3_dagA S a)) :=
      hι (psuC3bg3_dagA S a) rI dI rfl
    rwa [psuC3bg3b_dagA_dagA S a] at h1
  have hι1_symm : ∀ a : psuAlg B, ι1.symm (π cI a) = π eI (psuC3bg3_dagA S a) := by
    intro a
    rw [RingEquiv.symm_apply_eq]
    have h1 : π cI (psuC3bg3_dagA S (psuC3bg3_dagA S a)) =
        ι1 (π eI (psuC3bg3_dagA S a)) :=
      hι (psuC3bg3_dagA S a) cI eI rfl
    rwa [psuC3bg3b_dagA_dagA S a] at h1
  have hΨ1_symm : ∀ a : psuAlg B, Ψ1.symm (π dI a) = π eI (psuC3bg3_psiA S a) := by
    intro a
    rw [RingEquiv.symm_apply_eq]
    have h1 : π dI (psuC3bg3_psiA S (psuC3bg3_psiA S a)) =
        Ψ1 (π eI (psuC3bg3_psiA S a)) :=
      hΨ (psuC3bg3_psiA S a) dI eI (psuC3b_dag_psi S r.1)
    rwa [psuC3bg3b_psiA_psiA S a] at h1
  have hcomm : ∀ a : F rI, ι1.symm (Ψ0.symm a) = Ψ1.symm (ι0.symm a) := by
    intro a
    obtain ⟨b, rfl⟩ := hπ rI a
    rw [hΨ0_symm b, hι1_symm (psuC3bg3_psiA S b), hι0_symm b,
      hΨ1_symm (psuC3bg3_dagA S b)]
    rw [psuC3bg3b_dagA_psiA S b]
  let ePi := psuC3bg3b_piFourEquiv (fun e : psuC3bg3_fiber h X P R r => F e.1)
    rf sf cf df hcover4 hne_ab hne_ac hne_ad hne_bc hne_bd hne_cd
  have hpred : ∀ z : (e : psuC3bg3_fiber h X P R r) → F e.1,
      (psuC3bg3_C1r S P R hP F ι r z ∧ psuC3bg3_C2r S P R hP F Ψ r z) ↔
        (ι0 (ePi z).2.1 * (ePi z).1 = 1 ∧
         Ψ0 (ePi z).2.2.1 * (ePi z).1 = 1 ∧
         ι1 (ePi z).2.2.2 * (ePi z).2.2.1 = 1 ∧
         Ψ1 (ePi z).2.2.2 * (ePi z).2.1 = 1) := by
    intro z
    have hsimple : ∀ x : (e : psuC3bg3_fiber h X P R r) → F e.1,
        (ePi x).1 = x rf ∧ (ePi x).2.1 = x sf ∧
        (ePi x).2.2.1 = x cf ∧ (ePi x).2.2.2 = x df := by
      intro x
      exact ⟨rfl, rfl, rfl, rfl⟩
    constructor
    · intro hz
      obtain ⟨h1, h2⟩ := hz
      obtain ⟨e1, e2, e3, e4⟩ := hsimple z
      refine ⟨?_, ?_, ?_, ?_⟩
      · rw [e1, e2]; exact h1 rf
      · rw [e1, e3]; exact h2 rf
      · rw [e3, e4]; exact h1 cf
      · have hpsidf : psuC3bg3_psi S P hP dI = eI := Subtype.ext (psuC3b_dag_psi S r.1).symm
        have hfib : (⟨psuC3bg3_psi S P hP dI, psuC3b_orbit_psi_mem S sf.2⟩ :
            psuC3bg3_fiber h X P R r) = df := Subtype.ext hpsidf
        have hcast : cast (congrArg F hpsidf)
            (z ⟨psuC3bg3_psi S P hP dI, psuC3b_orbit_psi_mem S sf.2⟩) = z df := by
          rw [show hpsidf = congrArg Subtype.val hfib from Subsingleton.elim _ _]
          exact psuC3bg3_z_cast' hfib
        have hh := psuC3bg3b_Ψ_apply_idx_eq (X := X) P Ψ hpsidf rfl (psuC3b_dag_psi S r.1)
          (z ⟨psuC3bg3_psi S P hP dI, psuC3b_orbit_psi_mem S sf.2⟩)
        rw [hcast] at hh
        rw [e2, e4, hh]
        exact h2 sf
    · intro hq
      obtain ⟨hq1, hq2, hq3, hq4⟩ := hq
      obtain ⟨e1, e2, e3, e4⟩ := hsimple z
      have hq1' : ι0 (z sf) * z rf = 1 := by simpa [e1, e2] using hq1
      have hq2' : Ψ0 (z cf) * z rf = 1 := by simpa [e1, e3] using hq2
      have hq3' : ι1 (z df) * z cf = 1 := by simpa [e3, e4] using hq3
      have hq4' : Ψ1 (z df) * z sf = 1 := by simpa [e2, e4] using hq4
      constructor
      · intro e
        rcases hcover4 e with rfl | rfl | rfl | rfl
        · simpa [ι0, rf, sf, cf, df, dI, cI, eI, rI] using hq1'
        · have hdag : psuC3bg3_dag S P hP dI = rI := Subtype.ext (psuDag_dag h rI.1)
          have hfib : (⟨psuC3bg3_dag S P hP dI, psuC3b_orbit_dag_mem sf.2⟩ :
              psuC3bg3_fiber h X P R r) = rf := Subtype.ext (Subtype.ext (psuDag_dag h rI.1))
          have hcast : cast (congrArg F hdag)
              (z ⟨psuC3bg3_dag S P hP dI, psuC3b_orbit_dag_mem sf.2⟩) = z rf := by
            rw [show hdag = congrArg Subtype.val hfib from Subsingleton.elim _ _]
            exact psuC3bg3_z_cast' hfib
          have hh := psuC3bg3b_ι_apply_idx_eq P ι hdag rfl (psuDag_dag h rI.1).symm
            (z ⟨psuC3bg3_dag S P hP dI, psuC3b_orbit_dag_mem sf.2⟩)
          rw [hcast] at hh
          have hinv := psuC3bg3b_iota_inv S P π hπ ι hι (e := rI) (e' := dI)
            rfl (psuDag_dag h rI.1).symm
          have hgoal : ι dI (psuC3bg3_dag S P hP dI) rfl
              (z ⟨psuC3bg3_dag S P hP dI, psuC3b_orbit_dag_mem sf.2⟩) * z sf = 1 := by
            rw [← hh, hinv]
            exact psuC3bg3b_pair_lhs_inv ι0 hq1'
          simpa using hgoal
        · simpa [ι1, rf, sf, cf, df, dI, cI, eI, rI] using hq3'
        · have hdag : psuC3bg3_dag S P hP eI = cI := Subtype.ext (psuDag_dag h cI.1)
          have hfib : (⟨psuC3bg3_dag S P hP eI, psuC3b_orbit_dag_mem df.2⟩ :
              psuC3bg3_fiber h X P R r) = cf := Subtype.ext (Subtype.ext (psuDag_dag h cI.1))
          have hcast : cast (congrArg F hdag)
              (z ⟨psuC3bg3_dag S P hP eI, psuC3b_orbit_dag_mem df.2⟩) = z cf := by
            rw [show hdag = congrArg Subtype.val hfib from Subsingleton.elim _ _]
            exact psuC3bg3_z_cast' hfib
          have hh := psuC3bg3b_ι_apply_idx_eq P ι hdag rfl (psuDag_dag h cI.1).symm
            (z ⟨psuC3bg3_dag S P hP eI, psuC3b_orbit_dag_mem df.2⟩)
          rw [hcast] at hh
          have hinv := psuC3bg3b_iota_inv S P π hπ ι hι (e := cI) (e' := eI)
            rfl (psuDag_dag h cI.1).symm
          have hgoal : ι eI (psuC3bg3_dag S P hP eI) rfl
              (z ⟨psuC3bg3_dag S P hP eI, psuC3b_orbit_dag_mem df.2⟩) * z df = 1 := by
            rw [← hh, hinv]
            exact psuC3bg3b_pair_lhs_inv ι1 hq3'
          simpa using hgoal
      · intro e
        rcases hcover4 e with rfl | rfl | rfl | rfl
        · simpa [Ψ0, rf, sf, cf, df, dI, cI, eI, rI] using hq2'
        · have hpsidf : psuC3bg3_psi S P hP dI = eI := Subtype.ext (psuC3b_dag_psi S r.1).symm
          have hfib : (⟨psuC3bg3_psi S P hP dI, psuC3b_orbit_psi_mem S sf.2⟩ :
              psuC3bg3_fiber h X P R r) = df := Subtype.ext hpsidf
          have hcast : cast (congrArg F hpsidf)
              (z ⟨psuC3bg3_psi S P hP dI, psuC3b_orbit_psi_mem S sf.2⟩) = z df := by
            rw [show hpsidf = congrArg Subtype.val hfib from Subsingleton.elim _ _]
            exact psuC3bg3_z_cast' hfib
          have hh := psuC3bg3b_Ψ_apply_idx_eq (X := X) P Ψ hpsidf rfl (psuC3b_dag_psi S r.1)
            (z ⟨psuC3bg3_psi S P hP dI, psuC3b_orbit_psi_mem S sf.2⟩)
          rw [hcast] at hh
          have hgoal : Ψ dI (psuC3bg3_psi S P hP dI) rfl
              (z ⟨psuC3bg3_psi S P hP dI, psuC3b_orbit_psi_mem S sf.2⟩) * z sf = 1 := by
            rw [← hh]; exact hq4'
          simpa using hgoal
        · have hpsir : psuC3bg3_psi S P hP cI = rI := by
            apply Subtype.ext
            show psuPsi h X (psuPsi h X r.1) = r.1
            rw [psuPsi_psi h X S.X_mem S.X_sq]
          have hfib : (⟨psuC3bg3_psi S P hP cI, psuC3b_orbit_psi_mem S cf.2⟩ :
              psuC3bg3_fiber h X P R r) = rf := Subtype.ext hpsir
          have hcast : cast (congrArg F hpsir)
              (z ⟨psuC3bg3_psi S P hP cI, psuC3b_orbit_psi_mem S cf.2⟩) = z rf := by
            rw [show hpsir = congrArg Subtype.val hfib from Subsingleton.elim _ _]
            exact psuC3bg3_z_cast' hfib
          have he₂ : rI.1 = psuPsi h X cI.1 := by
            show r.1 = psuPsi h X (psuPsi h X r.1)
            rw [psuPsi_psi h X S.X_mem S.X_sq]
          have hh := psuC3bg3b_Ψ_apply_idx_eq (X := X) P Ψ hpsir rfl he₂
            (z ⟨psuC3bg3_psi S P hP cI, psuC3b_orbit_psi_mem S cf.2⟩)
          rw [hcast] at hh
          have hinv := psuC3bg3b_Ψ_inv S P π hπ Ψ hΨ (e := rI) (e' := cI) rfl he₂
          have hgoal : Ψ cI (psuC3bg3_psi S P hP cI) rfl
              (z ⟨psuC3bg3_psi S P hP cI, psuC3b_orbit_psi_mem S cf.2⟩) * z cf = 1 := by
            rw [← hh, hinv]
            exact psuC3bg3b_pair_lhs_inv Ψ0 hq2'
          simpa using hgoal
        · have hpsidf : psuC3bg3_psi S P hP eI = dI := by
            apply Subtype.ext
            show psuPsi h X (psuDag h (psuPsi h X r.1)) = psuDag h r.1
            rw [← psuC3b_dag_psi S (psuPsi h X r.1), psuPsi_psi h X S.X_mem S.X_sq]
          have hfib : (⟨psuC3bg3_psi S P hP eI, psuC3b_orbit_psi_mem S df.2⟩ :
              psuC3bg3_fiber h X P R r) = sf := Subtype.ext hpsidf
          have hcast : cast (congrArg F hpsidf)
              (z ⟨psuC3bg3_psi S P hP eI, psuC3b_orbit_psi_mem S df.2⟩) = z sf := by
            rw [show hpsidf = congrArg Subtype.val hfib from Subsingleton.elim _ _]
            exact psuC3bg3_z_cast' hfib
          have he₂ : dI.1 = psuPsi h X eI.1 := by
            show psuDag h r.1 = psuPsi h X (psuDag h (psuPsi h X r.1))
            rw [← psuC3b_dag_psi S (psuPsi h X r.1), psuPsi_psi h X S.X_mem S.X_sq]
          have hh := psuC3bg3b_Ψ_apply_idx_eq (X := X) P Ψ hpsidf rfl he₂
            (z ⟨psuC3bg3_psi S P hP eI, psuC3b_orbit_psi_mem S df.2⟩)
          rw [hcast] at hh
          have hinv := psuC3bg3b_Ψ_inv S P π hπ Ψ hΨ (e := dI) (e' := eI)
            (psuC3b_dag_psi S r.1) he₂
          have hgoal : Ψ eI (psuC3bg3_psi S P hP eI) rfl
              (z ⟨psuC3bg3_psi S P hP eI, psuC3b_orbit_psi_mem S df.2⟩) * z df = 1 := by
            rw [← hh, hinv]
            exact psuC3bg3b_pair_lhs_inv Ψ1 hq4'
          simpa using hgoal
  let eUnits : {p : F rI × F dI × F cI × F eI //
      (ι0 p.2.1 * p.1 = 1 ∧ Ψ0 p.2.2.1 * p.1 = 1 ∧
       ι1 p.2.2.2 * p.2.2.1 = 1 ∧ Ψ1 p.2.2.2 * p.2.1 = 1)} ≃ (F rI)ˣ :=
    { toFun := fun p => by
        have hx0 : p.1.1 ≠ 0 := by
          intro h0
          have hh := p.2.1
          rw [h0, mul_zero] at hh
          exact zero_ne_one hh
        exact Units.mk0 p.1.1 hx0
      invFun := fun u => by
        refine ⟨((u : F rI), ι0.symm (u : F rI)⁻¹, Ψ0.symm (u : F rI)⁻¹,
          (ι1.symm (Ψ0.symm (u : F rI)⁻¹))⁻¹), ?_, ?_, ?_, ?_⟩
        · show ι0 (ι0.symm (u : F rI)⁻¹) * (u : F rI) = 1
          rw [RingEquiv.apply_symm_apply]
          exact inv_mul_cancel₀ (Units.ne_zero u)
        · show Ψ0 (Ψ0.symm (u : F rI)⁻¹) * (u : F rI) = 1
          rw [RingEquiv.apply_symm_apply]
          exact inv_mul_cancel₀ (Units.ne_zero u)
        · show ι1 (ι1.symm (Ψ0.symm (u : F rI)⁻¹))⁻¹ * Ψ0.symm (u : F rI)⁻¹ = 1
          rw [map_inv₀, RingEquiv.apply_symm_apply]
          exact inv_mul_cancel₀ (fun h0 => inv_ne_zero (Units.ne_zero u) (by
            rw [← RingEquiv.apply_symm_apply Ψ0 ((u : F rI)⁻¹), h0, map_zero]))
        · have hv : (ι1.symm (Ψ0.symm (u : F rI)⁻¹))⁻¹ =
              (Ψ1.symm (ι0.symm (u : F rI)⁻¹))⁻¹ :=
            congrArg (fun x : F eI => x⁻¹) (hcomm (u : F rI)⁻¹)
          show Ψ1 ((ι1.symm (Ψ0.symm (u : F rI)⁻¹))⁻¹) * ι0.symm (u : F rI)⁻¹ = 1
          rw [hv, map_inv₀, RingEquiv.apply_symm_apply]
          exact inv_mul_cancel₀ (fun h0 => inv_ne_zero (Units.ne_zero u) (by
            rw [← RingEquiv.apply_symm_apply ι0 ((u : F rI)⁻¹), h0, map_zero]))
      left_inv := fun p => by
        apply Subtype.ext
        apply Prod.ext
        · rfl
        · apply Prod.ext
          · have h1' : ι0 p.1.2.1 = p.1.1⁻¹ := eq_inv_of_mul_eq_one_left p.2.1
            have hy : p.1.2.1 = ι0.symm (p.1.1⁻¹) := by
              rw [← RingEquiv.symm_apply_apply ι0 p.1.2.1, h1']
            exact hy.symm
          · apply Prod.ext
            · have h2' : Ψ0 p.1.2.2.1 = p.1.1⁻¹ := eq_inv_of_mul_eq_one_left p.2.2.1
              have hy : p.1.2.2.1 = Ψ0.symm (p.1.1⁻¹) := by
                rw [← RingEquiv.symm_apply_apply Ψ0 p.1.2.2.1, h2']
              exact hy.symm
            · have h2' : Ψ0 p.1.2.2.1 = p.1.1⁻¹ := eq_inv_of_mul_eq_one_left p.2.2.1
              have hy : p.1.2.2.1 = Ψ0.symm (p.1.1⁻¹) := by
                rw [← RingEquiv.symm_apply_apply Ψ0 p.1.2.2.1, h2']
              have h3' : ι1 p.1.2.2.2 = (p.1.2.2.1)⁻¹ := eq_inv_of_mul_eq_one_left p.2.2.2.1
              have hz : p.1.2.2.2 = (ι1.symm (Ψ0.symm (p.1.1⁻¹)))⁻¹ := by
                rw [← RingEquiv.symm_apply_apply ι1 p.1.2.2.2, h3', hy, map_inv₀]
              exact hz.symm
      right_inv := fun u => by
        apply Units.ext
        rfl }
  have hcard : Nat.card (psuC3bg3_Local S P R hP F ι Ψ r) = Nat.card ((F rI)ˣ) :=
    Nat.card_congr ((Equiv.subtypeEquiv ePi hpred).trans eUnits)
  have hcardF : Nat.card (F rI) = (2 ^ f) ^ (2 * blockDegree (psuAlg B) r.1) := by
    rw [psuC3bg3b_card_F S P hP F π hπ hker rI, h.card, ← pow_mul, ← pow_mul]
    congr 1
    ring
  rw [hcard, psuC3b_field_units_card (E := F rI), hcardF,
    show psuC3b_UO (2 ^ f) (blockDegree (psuAlg B) r.1) 5 =
        (2 ^ f) ^ (2 * blockDegree (psuAlg B) r.1) - 1 from by simp [psuC3b_UO]]

private lemma psuC3bg3_local_count {f n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    {h : UnitaryFieldData 2 f K} {X B : GL (Fin n) K} (S : PSUGraphSetting h n X B)
    (P R : Finset (Matrix (Fin n) (Fin n) K)) (hP : PrimFamily (psuAlg B) P)
    (F : {e : Matrix (Fin n) (Fin n) K // e ∈ P} → Type) [fieldF : ∀ e, Field (F e)]
        [algF : ∀ e, Algebra K (F e)] [charF : ∀ e, CharP (F e) 2] [finF : ∀ e, Finite (F e)]
    (hcard : ∀ e, Nat.card (F e) = Nat.card K ^ blockDegree (psuAlg B) e.1)
    (π : ∀ e : {e : Matrix (Fin n) (Fin n) K // e ∈ P}, psuAlg B →ₐ[K] F e)
    (hπ : ∀ e, Function.Surjective (π e))
    (hker : ∀ e (a : psuAlg B), π e a = 0 ↔ (a : Matrix (Fin n) (Fin n) K) * e.1 = 0)
    (hR : R ⊆ P)
(ι : ∀ e e' : {e : Matrix (Fin n) (Fin n) K // e ∈ P},
      e'.1 = psuDag h e.1 → (F e' ≃+* F e))
    (hι : ∀ (a : psuAlg B) (e e' : {e : Matrix (Fin n) (Fin n) K // e ∈ P})
      (he : e'.1 = psuDag h e.1),
      π e ⟨psuDag h (a : Matrix (Fin n) (Fin n) K), (psuGraph_star_mem S a.1 a.2).1⟩ =
        ι e e' he (π e' a))
    (Ψ : ∀ e e' : {e : Matrix (Fin n) (Fin n) K // e ∈ P},
      e'.1 = psuPsi h X e.1 → (F e' ≃+* F e))
    (hΨ : ∀ (a : psuAlg B) (e e' : {e : Matrix (Fin n) (Fin n) K // e ∈ P})
      (he : e'.1 = psuPsi h X e.1),
      π e ⟨psuPsi h X (a : Matrix (Fin n) (Fin n) K), (psuGraph_star_mem S a.1 a.2).2⟩ =
        Ψ e e' he (π e' a))
    (r : {r : Matrix (Fin n) (Fin n) K // r ∈ R}) :
    Nat.card (psuC3bg3_Local S P R hP F ι Ψ r) =
      psuC3b_UO (2 ^ f) (blockDegree (psuAlg B) r.1) (psuKind h X B r.1) := by
  have hle := psuC3b_kind_le h X B r.1
  rcases (by omega : psuKind h X B r.1 = 0 ∨ psuKind h X B r.1 = 1 ∨
      psuKind h X B r.1 = 2 ∨ psuKind h X B r.1 = 3 ∨ psuKind h X B r.1 = 4 ∨
      psuKind h X B r.1 = 5) with h | h | h | h | h | h
  · rw [h]; exact psuC3bg3_local_kind0 S P R hP F π hπ hR ι hι Ψ hΨ r h
  · rw [h]; exact psuC3bg3_local_kind1 S P R hP F hcard π hπ hR ι hι Ψ hΨ r h
  · rw [h]; exact psuC3bg3_local_kind2 S P R hP F π hπ hker hR ι Ψ hΨ r h
  · rw [h]; exact psuC3bg3_local_kind3 S P R hP F hcard π hπ hker hR ι hι Ψ hΨ r h
  · rw [h]; exact psuC3bg3_local_kind4 S P R hP F π hπ hker hR ι hι Ψ hΨ r h
  · rw [h]; exact psuC3bg3_local_kind5 S P R hP F π hπ hker hR ι hι Ψ hΨ r h

private lemma psuC3b_U_prod {f n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    {h : UnitaryFieldData 2 f K} {X B : GL (Fin n) K}
    (S : PSUGraphSetting h n X B) (P : Finset (Matrix (Fin n) (Fin n) K))
    (hP : PrimFamily (psuAlg B) P) (R : Finset (Matrix (Fin n) (Fin n) K)) (hR : R ⊆ P)
    (hrep : ∀ e ∈ P, ∃! r, r ∈ R ∧
      (r = e ∨ r = psuDag h e ∨ r = psuPsi h X e ∨ r = psuDag h (psuPsi h X e)))
    (F : {e // e ∈ P} → Type) [fieldF : ∀ e, Field (F e)]
    [algF : ∀ e, Algebra K (F e)] [finF : ∀ e, Finite (F e)] [charF : ∀ e, CharP (F e) 2]
    (π : ∀ e, psuAlg B →ₐ[K] F e) (hπ : ∀ e, Function.Surjective (π e))
    (hker : ∀ e (a : psuAlg B), π e a = 0 ↔ (a : Matrix (Fin n) (Fin n) K) * e.1 = 0)
    (hcard : ∀ e, Nat.card (F e) = Nat.card K ^ blockDegree (psuAlg B) e.1)
    (hbij : Function.Bijective (fun (a : psuAlg B) (e : {e // e ∈ P}) => π e a))
    (ι : ∀ e e' : {e // e ∈ P}, e'.1 = psuDag h e.1 → (F e' ≃+* F e))
    (hι : ∀ (a : psuAlg B) (e e' : {e // e ∈ P}) (he : e'.1 = psuDag h e.1),
      π e ⟨psuDag h (a : Matrix (Fin n) (Fin n) K), (psuGraph_star_mem S a.1 a.2).1⟩ =
        ι e e' he (π e' a))
    (Ψ : ∀ e e' : {e // e ∈ P}, e'.1 = psuPsi h X e.1 → (F e' ≃+* F e))
    (hΨ : ∀ (a : psuAlg B) (e e' : {e // e ∈ P}) (he : e'.1 = psuPsi h X e.1),
      π e ⟨psuPsi h X (a : Matrix (Fin n) (Fin n) K), (psuGraph_star_mem S a.1 a.2).2⟩ =
        Ψ e e' he (π e' a)) :
    Nat.card (psuC3b_U h X B) =
      ∏ r ∈ R, psuC3b_UO (2 ^ f) (blockDegree (psuAlg B) r) (psuKind h X B r) := by
  classical
  rw [psuC3bg3_U_family_card S P hP F π hbij ι hι Ψ hΨ]
  rw [psuC3bg3_family_factor S P R hP hrep F ι Ψ]
  rw [Finset.prod_subtype (s := R) (p := fun r => r ∈ R) (h := fun x => Iff.rfl)
    (f := fun r => psuC3b_UO (2 ^ f) (blockDegree (psuAlg B) r) (psuKind h X B r))]
  apply Finset.prod_congr rfl
  intro r hr
  exact psuC3bg3_local_count S P R hP F hcard π hπ hker hR ι hι Ψ hΨ r

private lemma psuC3b_F1_card {f n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    {h : UnitaryFieldData 2 f K} {X B : GL (Fin n) K} (S : PSUGraphSetting h n X B)
    (P : Finset (Matrix (Fin n) (Fin n) K)) (hP : PrimFamily (psuAlg B) P)
    (R : Finset (Matrix (Fin n) (Fin n) K)) (hR : R ⊆ P)
    (hrep : ∀ e ∈ P, ∃! r, r ∈ R ∧
      (r = e ∨ r = psuDag h e ∨ r = psuPsi h X e ∨ r = psuDag h (psuPsi h X e))) :
    Nat.card (psuC3b_F1 h B) =
      ∏ r ∈ R, psuC3b_F1O (2 ^ f) (blockDegree (psuAlg B) r) (psuKind h X B r) := by
  classical
  obtain ⟨F, fieldF, algF, finF, charF, π, hsurj, hker, hdim, hcard, hbij⟩ :=
    psuC3b_block_prod S P hP
  letI := fieldF
  letI := algF
  letI := finF
  letI := charF
  obtain ⟨ι, Ψ, hι, hΨ⟩ := psuC3b_star_transport S P hP F π hsurj hker
  exact psuC3b_F1_prod S P hP R hR hrep F π hsurj hcard hbij ι hι

private lemma psuC3b_U_card {f n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    {h : UnitaryFieldData 2 f K} {X B : GL (Fin n) K} (S : PSUGraphSetting h n X B)
    (P : Finset (Matrix (Fin n) (Fin n) K)) (hP : PrimFamily (psuAlg B) P)
    (R : Finset (Matrix (Fin n) (Fin n) K)) (hR : R ⊆ P)
    (hrep : ∀ e ∈ P, ∃! r, r ∈ R ∧
      (r = e ∨ r = psuDag h e ∨ r = psuPsi h X e ∨ r = psuDag h (psuPsi h X e))) :
    Nat.card (psuC3b_U h X B) =
      ∏ r ∈ R, psuC3b_UO (2 ^ f) (blockDegree (psuAlg B) r) (psuKind h X B r) := by
  classical
  obtain ⟨F, fieldF, algF, finF, charF, π, hsurj, hker, hdim, hcard, hbij⟩ :=
    psuC3b_block_prod S P hP
  letI := fieldF
  letI := algF
  letI := finF
  letI := charF
  obtain ⟨ι, Ψ, hι, hΨ⟩ := psuC3b_star_transport S P hP F π hsurj hker
  exact psuC3b_U_prod S P hP R hR hrep F π hsurj hker hcard hbij ι hι Ψ hΨ

private lemma psuC3b_rho_arith (q d k : ℕ) (hq : 2 ≤ q) (hd : 1 ≤ d) (hk : k ≤ 5)
    (heven : k = 3 → Even d) :
    psuC3b_UO q d k ∣ psuC3b_F1O q d k ∧
      psuC3b_F1O q d k / psuC3b_UO q d k = psuRho q d k ∧ 0 < psuC3b_UO q d k := by
  have hk6 : k < 6 := by omega
  interval_cases k
  · change 1 ∣ q ^ d + 1 ∧ (q ^ d + 1) / 1 = q ^ d + 1 ∧ 0 < 1
    simp
  · change (q ^ d + 1) ∣ (q ^ d + 1) ^ 2 ∧
      (q ^ d + 1) ^ 2 / (q ^ d + 1) = q ^ d + 1 ∧ 0 < q ^ d + 1
    refine ⟨?_, ?_, by positivity⟩
    · rw [pow_two]; exact dvd_mul_right _ _
    · rw [pow_two]; exact Nat.mul_div_right (q ^ d + 1) (by positivity)
  · change 1 ∣ q ^ (2 * d) - 1 ∧ (q ^ (2 * d) - 1) / 1 = q ^ (2 * d) - 1 ∧ 0 < 1
    simp
  · change (q ^ d + 1) ∣ q ^ (2 * d) - 1 ∧
      (q ^ (2 * d) - 1) / (q ^ d + 1) = q ^ d - 1 ∧ 0 < q ^ d + 1
    have hpow : q ^ (2 * d) = (q ^ d) ^ 2 := psuC3bg4_pow_two_mul q d
    have hsq : (q ^ d) ^ 2 - 1 = (q ^ d + 1) * (q ^ d - 1) :=
      psuC3bg4_sq_sub_one (q ^ d)
    rw [hpow, hsq]
    refine ⟨?_, ?_, by positivity⟩
    · exact dvd_mul_right _ _
    · exact Nat.mul_div_right (q ^ d - 1) (by positivity)
  · change (q ^ d - 1) ∣ q ^ (2 * d) - 1 ∧
      (q ^ (2 * d) - 1) / (q ^ d - 1) = q ^ d + 1 ∧ 0 < q ^ d - 1
    have hpow : q ^ (2 * d) = (q ^ d) ^ 2 := psuC3bg4_pow_two_mul q d
    have hsq : (q ^ d) ^ 2 - 1 = (q ^ d + 1) * (q ^ d - 1) :=
      psuC3bg4_sq_sub_one (q ^ d)
    have h1 : q ≤ q ^ d := by
      have h := Nat.pow_le_pow_right (by omega : 1 ≤ q) hd
      simpa using h
    have hposd : 0 < q ^ d - 1 := by omega
    rw [hpow, hsq, Nat.mul_comm (q ^ d + 1) (q ^ d - 1)]
    refine ⟨?_, ?_, hposd⟩
    · exact dvd_mul_right _ _
    · exact Nat.mul_div_right (q ^ d + 1) hposd
  · change (q ^ (2 * d) - 1) ∣ (q ^ (2 * d) - 1) ^ 2 ∧
      (q ^ (2 * d) - 1) ^ 2 / (q ^ (2 * d) - 1) = q ^ (2 * d) - 1 ∧
      0 < q ^ (2 * d) - 1
    have h1 : q ≤ q ^ (2 * d) := by
      have h := Nat.pow_le_pow_right (by omega : 1 ≤ q) (by omega : 1 ≤ 2 * d)
      simpa using h
    have hpos2 : 0 < q ^ (2 * d) - 1 := by omega
    refine ⟨?_, ?_, hpos2⟩
    · rw [pow_two]; exact dvd_mul_right _ _
    · rw [pow_two]; exact Nat.mul_div_right (q ^ (2 * d) - 1) hpos2

private lemma psuC3b_norm_card_arith {ι : Type} (N U : ℕ) (R : Finset ι) (F1O UO ρ : ι → ℕ)
    (hN : N * U = ∏ r ∈ R, F1O r) (hU : U = ∏ r ∈ R, UO r)
    (hdiv : ∀ r ∈ R, UO r ∣ F1O r ∧ F1O r / UO r = ρ r)
    (hpos : ∀ r ∈ R, 0 < UO r) :
    N = ∏ r ∈ R, ρ r := by
  have hfact : ∀ r ∈ R, F1O r = UO r * ρ r := by
    intro r hr
    calc F1O r = F1O r / UO r * UO r := (Nat.div_mul_cancel (hdiv r hr).1).symm
      _ = ρ r * UO r := by rw [(hdiv r hr).2]
      _ = UO r * ρ r := Nat.mul_comm _ _
  have hP : ∏ r ∈ R, F1O r = (∏ r ∈ R, UO r) * (∏ r ∈ R, ρ r) := by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl (fun r hr => hfact r hr)
  have hPpos : 0 < ∏ r ∈ R, UO r := Finset.prod_pos (fun r hr => hpos r hr)
  have hcancel : N * (∏ r ∈ R, UO r) = (∏ r ∈ R, UO r) * (∏ r ∈ R, ρ r) := by
    rw [show N * (∏ r ∈ R, UO r) = ∏ r ∈ R, F1O r from by rw [← hU]; exact hN]
    exact hP
  rw [mul_comm N (∏ r ∈ R, UO r)] at hcancel
  exact Nat.eq_of_mul_eq_mul_left hPpos hcancel

private theorem psuC3b_norm_card {f n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    {h : UnitaryFieldData 2 f K} {X B : GL (Fin n) K} (S : PSUGraphSetting h n X B)
    (P : Finset (Matrix (Fin n) (Fin n) K)) (hP : PrimFamily (psuAlg B) P)
    (R : Finset (Matrix (Fin n) (Fin n) K)) (hR : R ⊆ P)
    (hrep : ∀ e ∈ P, ∃! r, r ∈ R ∧
      (r = e ∨ r = psuDag h e ∨ r = psuPsi h X e ∨ r = psuDag h (psuPsi h X e))) :
    Nat.card (psuNormImage h X B) =
      ∏ r ∈ R, psuRho (2 ^ f) (blockDegree (psuAlg B) r) (psuKind h X B r) := by
  classical
  rw [psuC3b_normImage_eq_Nrange h X B]
  have hq : 2 ≤ 2 ^ f := by
    rw [show (2 : ℕ) = 2 ^ 1 from (pow_one 2).symm]
    exact Nat.pow_le_pow_right (by norm_num) h.one_le
  have hdata := psuC3b_degree_data S P hP R hR
  refine psuC3b_norm_card_arith (Nat.card (psuC3b_Nrange h X B))
    (Nat.card (psuC3b_U h X B)) R
    (fun r => psuC3b_F1O (2 ^ f) (blockDegree (psuAlg B) r) (psuKind h X B r))
    (fun r => psuC3b_UO (2 ^ f) (blockDegree (psuAlg B) r) (psuKind h X B r))
    (fun r => psuRho (2 ^ f) (blockDegree (psuAlg B) r) (psuKind h X B r))
    ?_ ?_ ?_ ?_
  · rw [psuC3b_first_iso S P hP, psuC3b_F1_card S P hP R hR hrep]
  · exact psuC3b_U_card S P hP R hR hrep
  · intro r hr
    have h := psuC3b_rho_arith (2 ^ f) (blockDegree (psuAlg B) r) (psuKind h X B r)
      hq (hdata r hr).1 (psuC3b_kind_le h X B r) (hdata r hr).2
    exact ⟨h.1, h.2.1⟩
  · intro r hr
    have h := psuC3b_rho_arith (2 ^ f) (blockDegree (psuAlg B) r) (psuKind h X B r)
      hq (hdata r hr).1 (psuC3b_kind_le h X B r) (hdata r hr).2
    exact h.2.2

theorem psuGraph_orbit_data {f n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    {h : UnitaryFieldData 2 f K} {X B : GL (Fin n) K} (S : PSUGraphSetting h n X B)
    (P : Finset (Matrix (Fin n) (Fin n) K)) (hP : PrimFamily (psuAlg B) P)
    :
    ∃ R : Finset (Matrix (Fin n) (Fin n) K), R ⊆ P ∧
      (∀ e ∈ P, ∃! r, r ∈ R ∧
        (r = e ∨ r = psuDag h e ∨ r = psuPsi h X e ∨ r = psuDag h (psuPsi h X e))) ∧
      Nat.card (psuNormImage h X B) =
        ∏ r ∈ R, psuRho (2 ^ f) (blockDegree (psuAlg B) r) (psuKind h X B r) ∧
      n = ∑ r ∈ R, psuOrbSize (psuKind h X B r) * Matrix.rank r ∧
      (∑ r ∈ R.filter (fun r => blockDegree (psuAlg B) r = 1), psuOrbSize (psuKind h X B r)) ≤
        (2 ^ f) ^ 2 - 1 ∧
      ∀ r ∈ R, 1 ≤ blockDegree (psuAlg B) r ∧
        (psuKind h X B r = 3 → Even (blockDegree (psuAlg B) r)) := by
  obtain ⟨R, hRsub, hRrep⟩ := psuC3b_transversal S P
  exact ⟨R, hRsub, hRrep, psuC3b_norm_card S P hP R hRsub hRrep,
    psuC3b_dim_count S P hP R hRsub hRrep,
    psuC3b_degree_one_count S P hP R hRsub hRrep,
    psuC3b_degree_data S P hP R hRsub⟩

end CFSG.StandardType
