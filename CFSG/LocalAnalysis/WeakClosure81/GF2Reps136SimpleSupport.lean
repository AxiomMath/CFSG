module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps136SimpleSchur
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs12d

public section

namespace CFSG.LocalAnalysis.WeakClosure81.GF2Reps136

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open scoped commutatorElement Pointwise Matrix

lemma w1369_ta_inv_equivariant' {Q : Type} [CommGroup Q] {Λ : Subgroup (MulAut Q)}
    {A B : Subgroup Q} (hA : StableUnder Λ A) (hB : StableUnder Λ B)
    (φ : A →* B) (hbij : Function.Bijective φ)
    (heq : ∀ g (hg : g ∈ Λ) (x : A),
      (φ ⟨g (x : Q), hA g hg (x : Q) x.2⟩ : Q) = g (φ x : Q)) :
    ∀ g (hg : g ∈ Λ) (y : B),
      (((MulEquiv.ofBijective φ hbij).symm ⟨g (y : Q), hB g hg (y : Q) y.2⟩ : A) : Q) =
        g (((MulEquiv.ofBijective φ hbij).symm y : A) : Q) := by
  intro g hg y
  let Φ : A ≃* B := MulEquiv.ofBijective φ hbij
  change ((Φ.symm ⟨g (y : Q), hB g hg (y : Q) y.2⟩ : A) : Q) = g ((Φ.symm y : A) : Q)
  rw [show g ((Φ.symm y : A) : Q) =
      ((⟨g ((Φ.symm y : A) : Q), hA g hg ((Φ.symm y : A) : Q) (Φ.symm y).2⟩ : A) : Q) from rfl]
  apply congrArg (fun z : A => (z : Q))
  apply hbij.1
  change Φ (Φ.symm ⟨g (y : Q), hB g hg (y : Q) y.2⟩) =
    Φ ⟨g ((Φ.symm y : A) : Q), hA g hg ((Φ.symm y : A) : Q) (Φ.symm y).2⟩
  rw [Φ.apply_symm_apply]
  apply Subtype.ext
  change (g (y : Q)) = ((φ ⟨g ((Φ.symm y : A) : Q),
    hA g hg ((Φ.symm y : A) : Q) (Φ.symm y).2⟩ : B) : Q)
  have h2 : φ (Φ.symm y) = y := Φ.apply_symm_apply y
  rw [heq g hg (Φ.symm y), h2]

lemma w1369_ta_SecIsoOn_of_mulEquiv {Q : Type} [CommGroup Q] {Λ : Subgroup (MulAut Q)}
    {A B : Subgroup Q} (hA : StableUnder Λ A) (hB : StableUnder Λ B) (e : A ≃* B)
    (he : ∀ g (hg : g ∈ Λ) (x : A),
      (e ⟨g (x : Q), hA g hg (x : Q) x.2⟩ : Q) = g (e x : Q)) :
    SecIsoOn Λ A ⊥ B ⊥ := by
  refine ⟨bot_le, bot_le, hA, ?_, hB, ?_, ?_⟩
  · intro g hg x hx
    simpa using hx
  · intro g hg x hx
    simpa using hx
  · refine ⟨(B).subtype.comp e.toMonoidHom, fun a => (e a).2, ?_, ?_, ?_⟩
    · intro a
      constructor
      · intro h
        have h1 : e a = 1 := Subtype.ext (by simpa using h)
        have h2 : (a : Q) = 1 :=
          congrArg Subtype.val (e.injective (h1.trans (map_one e).symm))
        show (a : Q) ∈ (⊥ : Subgroup Q)
        rw [Subgroup.mem_bot]
        exact h2
      · intro h
        have ha : a = 1 := by simpa using h
        show B.subtype (e a) ∈ (⊥ : Subgroup Q)
        rw [ha, map_one]
        rfl
    · intro b hb
      refine ⟨e.symm ⟨b, hb⟩, ?_⟩
      have h2 : (e (e.symm ⟨b, hb⟩) : Q) = b := congrArg Subtype.val (e.apply_symm_apply ⟨b, hb⟩)
      simp [h2]
    · intro g hg a a' ha'
      have ha'' : a' = ⟨g (a : Q), hA g hg (a : Q) a.2⟩ := Subtype.ext ha'
      rw [ha'']
      simp only [Subgroup.mem_bot, mul_inv_eq_one]
      exact he g hg a

@[expose] noncomputable def w1369_ta_projHom {Q : Type} [CommGroup Q] {Λ : Subgroup (MulAut Q)}
    {k : ℕ} {I : Fin k → Subgroup Q} (P : w1369_ta_Proj I Λ) (S : Subgroup Q) (i : Fin k) :
    S →* I i :=
  MonoidHom.codRestrict ((P.e i).comp S.subtype) (I i) (fun s => P.e_mem i (s : Q))

lemma w1369_ta_projHom_apply {Q : Type} [CommGroup Q] {Λ : Subgroup (MulAut Q)}
    {k : ℕ} {I : Fin k → Subgroup Q} (P : w1369_ta_Proj I Λ) (S : Subgroup Q) (i : Fin k)
    (x : S) : (w1369_ta_projHom P S i x : Q) = P.e i (x : Q) := rfl

lemma w1369_ta_projHom_equiv {Q : Type} [CommGroup Q] {Λ : Subgroup (MulAut Q)}
    {k : ℕ} {I : Fin k → Subgroup Q} (P : w1369_ta_Proj I Λ) {S : Subgroup Q}
    (hS : StableUnder Λ S) (i : Fin k) :
    ∀ g (hg : g ∈ Λ) (x : S),
      (w1369_ta_projHom P S i ⟨g (x : Q), hS g hg (x : Q) x.2⟩ : Q) =
        g ((w1369_ta_projHom P S i x : I i) : Q) := by
  intro g hg x
  rw [w1369_ta_projHom_apply, w1369_ta_projHom_apply]
  exact P.e_equiv i g hg (x : Q)

lemma w1369_ta_projHom_bij {Q : Type} [CommGroup Q] {Λ : Subgroup (MulAut Q)}
    {k : ℕ} {I : Fin k → Subgroup Q} (P : w1369_ta_Proj I Λ)
    (hsimple : ∀ i, w1369_ta_IsSimple Λ (I i))
    {S : Subgroup Q} (hS : w1369_ta_IsSimple Λ S) {i : Fin k}
    (hi : w1369_ta_projHom P S i ≠ 1) :
    Function.Bijective (w1369_ta_projHom P S i) :=
  w1369_ta_bijective_of_ne_one hS (hsimple i) (w1369_ta_projHom_equiv P hS.2.1 i) hi

@[expose] def w1369_ta_supp {Q : Type} [CommGroup Q] {Λ : Subgroup (MulAut Q)}
    {k : ℕ} {I : Fin k → Subgroup Q} (P : w1369_ta_Proj I Λ) (S : Subgroup Q) : Set (Fin k) :=
  {i | w1369_ta_projHom P S i ≠ 1}

lemma w1369_ta_supp_nonempty {Q : Type} [CommGroup Q] {Λ : Subgroup (MulAut Q)}
    {k : ℕ} {I : Fin k → Subgroup Q} (P : w1369_ta_Proj I Λ) {S : Subgroup Q}
    (hS : S ≠ ⊥) : (w1369_ta_supp P S).Nonempty := by
  obtain ⟨x, hx⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hS
  by_contra h
  rw [Set.not_nonempty_iff_eq_empty] at h
  have h' : ∀ i, w1369_ta_projHom P S i = 1 := fun i => by
    by_contra hne
    have hmem : i ∈ (∅ : Set (Fin k)) := by
      rw [← h]
      exact hne
    exact hmem
  have hx1 : x = 1 := by
    apply Subtype.ext
    show (x : Q) = 1
    rw [← P.e_prod (x : Q)]
    apply Finset.prod_eq_one
    intro i _
    have hval := congrArg (fun f : S →* I i => f x) (h' i)
    have hq := congrArg (fun z : I i => (z : Q)) hval
    rw [w1369_ta_projHom_apply] at hq
    simpa using hq
  exact hx hx1

lemma w1369_ta_SecIsoOn_of_proj {Q : Type} [CommGroup Q] {Λ : Subgroup (MulAut Q)}
    {k : ℕ} {I : Fin k → Subgroup Q} (P : w1369_ta_Proj I Λ)
    (hstab : ∀ i, StableUnder Λ (I i))
    (hsimple : ∀ i, w1369_ta_IsSimple Λ (I i))
    {S : Subgroup Q} (hS : w1369_ta_IsSimple Λ S) {i j : Fin k}
    (hi : w1369_ta_projHom P S i ≠ 1) (hj : w1369_ta_projHom P S j ≠ 1) :
    SecIsoOn Λ (I i) ⊥ (I j) ⊥ := by
  refine w1369_ta_SecIsoOn_of_mulEquiv (hstab i) (hstab j)
    ((MulEquiv.ofBijective (w1369_ta_projHom P S i)
      (w1369_ta_projHom_bij P hsimple hS hi)).symm.trans
      (MulEquiv.ofBijective (w1369_ta_projHom P S j)
        (w1369_ta_projHom_bij P hsimple hS hj))) ?_
  intro g hg x
  set Φi := MulEquiv.ofBijective (w1369_ta_projHom P S i)
    (w1369_ta_projHom_bij P hsimple hS hi)
  set Φj := MulEquiv.ofBijective (w1369_ta_projHom P S j)
    (w1369_ta_projHom_bij P hsimple hS hj)
  change (Φj (Φi.symm ⟨g (x : Q), hstab i g hg (x : Q) x.2⟩) : Q) =
    g ((Φj (Φi.symm x) : I j) : Q)
  have h1 : Φi.symm ⟨g (x : Q), hstab i g hg (x : Q) x.2⟩ =
      ⟨g ((Φi.symm x : S) : Q), hS.2.1 g hg ((Φi.symm x : S) : Q) (Φi.symm x).2⟩ :=
    Subtype.ext (w1369_ta_inv_equivariant' hS.2.1 (hstab i) (w1369_ta_projHom P S i) _
      (w1369_ta_projHom_equiv P hS.2.1 i) g hg x)
  rw [h1]
  exact w1369_ta_projHom_equiv P hS.2.1 j g hg (Φi.symm x)

lemma w1369_ta_simple_iso_some {Q : Type} [CommGroup Q] {Λ : Subgroup (MulAut Q)}
    {k : ℕ} {I : Fin k → Subgroup Q} (P : w1369_ta_Proj I Λ)
    (hstab : ∀ i, StableUnder Λ (I i))
    (hsimple : ∀ i, w1369_ta_IsSimple Λ (I i))
    {S : Subgroup Q} (hS : w1369_ta_IsSimple Λ S) :
    ∃ i, SecIsoOn Λ (I i) ⊥ S ⊥ := by
  obtain ⟨i, hi⟩ := w1369_ta_supp_nonempty P hS.1
  refine ⟨i, ?_⟩
  refine w1369_ta_SecIsoOn_of_mulEquiv (hstab i) hS.2.1
    (MulEquiv.ofBijective (w1369_ta_projHom P S i)
      (w1369_ta_projHom_bij P hsimple hS hi)).symm ?_
  intro g hg x
  exact w1369_ta_inv_equivariant' hS.2.1 (hstab i) (w1369_ta_projHom P S i) _
    (w1369_ta_projHom_equiv P hS.2.1 i) g hg x

end CFSG.LocalAnalysis.WeakClosure81.GF2Reps136
