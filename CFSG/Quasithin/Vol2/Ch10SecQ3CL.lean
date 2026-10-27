module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBGeneralLinearSmall
public import CFSG.Quasithin.Background.E2Three

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecB

namespace C11AmS

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

theorem isSolvable_of_isL2Natural_one {W : Type*} [CommGroup W] {K₀ : Subgroup (MulAut W)}
    {C : Subgroup W} (h : E2.IsL2Natural K₀ C 1) : Group.IsSolvable ↥K₀ := by
  obtain ⟨-, F, _, _, hF, e, -⟩ := h
  have hF2 : Nat.card F = 2 := by rw [Nat.card_eq_fintype_card, hF]; rfl
  have : Group.IsSolvable (Matrix.GeneralLinearGroup (Fin 2) F) :=
    CFSG.ComponentClassification.CatalogueBGeneralLinear.generalLinear_two_small_solvable F
      (Or.inl hF2)
  have : Group.IsSolvable (Matrix.SpecialLinearGroup (Fin 2) F) :=
    Group.isSolvable_of_isSolvable_injective Matrix.SpecialLinearGroup.toGL_injective
  exact Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective

theorem isSolvable_conjAut {W : Type*} [CommGroup W] {K₀ : Subgroup (MulAut W)}
    (h : Group.IsSolvable ↥K₀) (g : MulAut W) : Group.IsSolvable ↥(B1.conjAut g K₀) := by
  have he : B1.conjAut g K₀ = K₀.map (MulAut.conj g).toMonoidHom := by
    ext x
    rw [B1.mem_conjAut, Subgroup.mem_map_equiv, MulAut.conj_symm_apply]
  rw [he]
  exact Group.isSolvable_of_surjective (f := (MulAut.conj g).toMonoidHom.subgroupMap K₀)
    ((MulAut.conj g).toMonoidHom.subgroupMap_surjective K₀)

theorem isSolvable_sup {Y : Type*} [Group Y] {A B : Subgroup Y} (hA : Group.IsSolvable ↥A)
    (hB : Group.IsSolvable ↥B) (hc : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) :
    Group.IsSolvable ↥(A ⊔ B) := by
  have hcomm : ∀ (a : ↥A) (b : ↥B), Commute (A.subtype a) (B.subtype b) :=
    fun a b => hc a a.2 b b.2
  let f : ↥A × ↥B →* Y := MonoidHom.noncommCoprod A.subtype B.subtype hcomm
  have hrange : f.range = A ⊔ B := by
    refine le_antisymm ?_ (sup_le ?_ ?_)
    · rintro _ ⟨⟨a, b⟩, rfl⟩
      exact (A ⊔ B).mul_mem (Subgroup.mem_sup_left a.2) (Subgroup.mem_sup_right b.2)
    · intro a ha
      exact ⟨(⟨a, ha⟩, 1), by
        change A.subtype.noncommCoprod B.subtype hcomm (⟨a, ha⟩, 1) = a
        rw [MonoidHom.noncommCoprod_apply]; simp⟩
    · intro b hb
      exact ⟨(1, ⟨b, hb⟩), by
        change A.subtype.noncommCoprod B.subtype hcomm (1, ⟨b, hb⟩) = b
        rw [MonoidHom.noncommCoprod_apply]; simp⟩
  have : Group.IsSolvable ↥f.range :=
    Group.isSolvable_of_surjective (f := f.rangeRestrict) f.rangeRestrict_surjective
  rw [hrange] at this
  exact this

theorem isSolvable_iSup {Y : Type*} [Group Y] {I : Finset (Subgroup Y)}
    (hcard : I.card = 1 ∨ I.card = 2) (hsol : ∀ L ∈ I, Group.IsSolvable ↥L)
    (hcomm : ∀ L ∈ I, ∀ L' ∈ I, L ≠ L' → ∀ a ∈ L, ∀ b ∈ L', a * b = b * a) :
    Group.IsSolvable ↥(⨆ L ∈ I, L) := by
  classical
  rcases hcard with h1 | h2
  · obtain ⟨L, rfl⟩ := Finset.card_eq_one.mp h1
    rw [Finset.iSup_singleton]
    exact hsol L (Finset.mem_singleton_self L)
  · obtain ⟨A, B, hAB, rfl⟩ := Finset.card_eq_two.mp h2
    have he : (⨆ L ∈ ({A, B} : Finset (Subgroup Y)), L) = A ⊔ B := by
      rw [Finset.iSup_insert, Finset.iSup_singleton]
    rw [he]
    exact isSolvable_sup (hsol A (by simp)) (hsol B (by simp))
      (hcomm A (by simp) B (by simp) hAB)

theorem eq_bot_of_perfect_of_le {Y : Type*} [Group Y] {P S : Subgroup Y}
    (hS : Group.IsSolvable ↥S) (hPS : P ≤ S) (hP : ⁅P, P⁆ = P) : P = ⊥ := by
  by_contra hne
  have hP' : P.subgroupOf S ≠ ⊥ := by
    intro h
    exact hne (by
      rw [eq_bot_iff]
      intro x hx
      have : (⟨x, hPS hx⟩ : ↥S) ∈ P.subgroupOf S := hx
      rw [h, Subgroup.mem_bot] at this
      exact Subgroup.mem_bot.mpr (congrArg Subtype.val this))
  have hlt := Group.IsSolvable.commutator_lt_of_ne_bot hP'
  apply hlt.ne
  have hmap : (P.subgroupOf S).map S.subtype = P := Subgroup.map_subgroupOf_eq_of_le hPS
  refine Subgroup.map_injective S.subtype_injective ?_
  rw [Subgroup.map_commutator, hmap, hP]

end C11AmS

end CFSG.Quasithin.Vol2.Ch10.SecB
