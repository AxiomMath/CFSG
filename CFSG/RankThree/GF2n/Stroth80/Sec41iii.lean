module

public import CFSG.RankThree.GF2n.Stroth80.Sec44
public import CFSG.RankThree.GF2n.Stroth80.Sec4Quasi

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix

theorem center_statedSL_two_eq_bot {K : Type} [Field K] [Finite K] [CharP K 2] :
    Subgroup.center ↥(StatedSL 2 K) = ⊥ := by
  let e : Matrix.SpecialLinearGroup (Fin 2) K ≃* StatedSL 2 K :=
    (MonoidHom.ofInjective Matrix.SpecialLinearGroup.toGL_injective).trans
      (MulEquiv.subgroupCongr (CFSG.Open.StatedAPI.statedSL_eq_range_toGL 2 K).symm)
  have hroots : rootsOfUnity 2 K = ⊥ := by
    rw [eq_bot_iff]
    intro ζ hζ
    have h2 : ζ ^ 2 = 1 := (mem_rootsOfUnity 2 ζ).mp hζ
    rw [Subgroup.mem_bot]
    apply Units.ext
    have h3 : (ζ : K) * (ζ : K) = 1 := by
      have := congrArg Units.val h2
      simpa [sq] using this
    rcases mul_self_eq_one_iff.1 h3 with h1 | h1
    · rw [h1, Units.val_one]
    · rw [h1, CharTwo.neg_eq, Units.val_one]
  have hcard : Nat.card (Subgroup.center ↥(StatedSL 2 K)) = 1 := by
    rw [← Nat.card_congr (Subgroup.centerCongr e).toEquiv,
      Nat.card_congr (Matrix.SpecialLinearGroup.center_equiv_rootsOfUnity' (0 : Fin 2)).toEquiv,
      Fintype.card_fin, hroots]
    simp
  exact Subgroup.card_eq_one.mp hcard

theorem isSimpleGroup_statedSL_two {K : Type} [Field K] [Finite K] [CharP K 2]
    (hq : CFSG.IsQuasisimple ↥(StatedSL 2 K)) : IsSimpleGroup ↥(StatedSL 2 K) := by
  obtain ⟨-, hs, -⟩ := hq
  have e : (↥(StatedSL 2 K) ⧸ Subgroup.center ↥(StatedSL 2 K)) ≃* ↥(StatedSL 2 K) :=
    (QuotientGroup.quotientMulEquivOfEq center_statedSL_two_eq_bot).trans
      QuotientGroup.quotientBot
  exact (MulEquiv.isSimpleGroup_congr e).mp hs

theorem exists_equiv_top_bot (A B : Type*) [Group A] [Group B] :
    Nonempty (↥((⊤ : Subgroup A).prod (⊥ : Subgroup B)) ≃* A) := by
  refine ⟨MulEquiv.ofBijective ((MonoidHom.fst A B).comp (Subgroup.subtype _)) ⟨?_, ?_⟩⟩
  · intro p q hpq
    have h1 : p.1.1 = q.1.1 := hpq
    have hp2 : p.1.2 = 1 := Subgroup.mem_bot.mp (Subgroup.mem_prod.mp p.2).2
    have hq2 : q.1.2 = 1 := Subgroup.mem_bot.mp (Subgroup.mem_prod.mp q.2).2
    exact Subtype.ext (Prod.ext h1 (hp2.trans hq2.symm))
  · intro a
    exact ⟨⟨(a, 1), Subgroup.mem_prod.mpr ⟨Subgroup.mem_top a, Subgroup.mem_bot.mpr rfl⟩⟩, rfl⟩

theorem exists_equiv_bot_top (A B : Type*) [Group A] [Group B] :
    Nonempty (↥((⊥ : Subgroup A).prod (⊤ : Subgroup B)) ≃* B) := by
  refine ⟨MulEquiv.ofBijective ((MonoidHom.snd A B).comp (Subgroup.subtype _)) ⟨?_, ?_⟩⟩
  · intro p q hpq
    have h1 : p.1.2 = q.1.2 := hpq
    have hp2 : p.1.1 = 1 := Subgroup.mem_bot.mp (Subgroup.mem_prod.mp p.2).1
    have hq2 : q.1.1 = 1 := Subgroup.mem_bot.mp (Subgroup.mem_prod.mp q.2).1
    exact Subtype.ext (Prod.ext (hp2.trans hq2.symm) h1)
  · intro b
    exact ⟨⟨(1, b), Subgroup.mem_prod.mpr ⟨Subgroup.mem_bot.mpr rfl, Subgroup.mem_top b⟩⟩, rfl⟩

theorem sl2_of_commuting_normal_prod {K : Type} [Field K] [Finite K] [CharP K 2]
    (hq : CFSG.IsQuasisimple ↥(StatedSL 2 K)) {Γ : Type} [Group Γ]
    (e : Γ ≃* ↥(StatedSL 2 K) × ↥(StatedSL 2 K)) {F₁ F₂ : Subgroup Γ} [F₁.Normal] [F₂.Normal]
    (h1 : F₁ ≠ ⊥) (h2 : F₂ ≠ ⊥) (hc : ∀ x ∈ F₁, ∀ y ∈ F₂, x * y = y * x) :
    Nonempty (↥F₁ ≃* ↥(StatedSL 2 K)) ∧ Nonempty (↥F₂ ≃* ↥(StatedSL 2 K)) := by
  haveI : IsSimpleGroup ↥(StatedSL 2 K) := isSimpleGroup_statedSL_two hq
  have hA : ∃ a b : ↥(StatedSL 2 K), a * b ≠ b * a := by
    by_contra h
    push Not at h
    exact not_isSolvable_of_isQuasisimple hq (isSolvable_of_comm fun a b => h a b)
  haveI hN1 : (F₁.map e.toMonoidHom).Normal :=
    Subgroup.Normal.map ‹F₁.Normal› e.toMonoidHom e.surjective
  haveI hN2 : (F₂.map e.toMonoidHom).Normal :=
    Subgroup.Normal.map ‹F₂.Normal› e.toMonoidHom e.surjective
  have h1' : F₁.map e.toMonoidHom ≠ ⊥ := fun h =>
    h1 ((Subgroup.map_eq_bot_iff_of_injective F₁ e.injective).mp h)
  have h2' : F₂.map e.toMonoidHom ≠ ⊥ := fun h =>
    h2 ((Subgroup.map_eq_bot_iff_of_injective F₂ e.injective).mp h)
  have hc' : ∀ x ∈ F₁.map e.toMonoidHom, ∀ y ∈ F₂.map e.toMonoidHom, x * y = y * x := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    show e a * e b = e b * e a
    rw [← map_mul, ← map_mul, hc a ha b hb]
  have e1 : Nonempty (↥F₁ ≃* ↥(F₁.map e.toMonoidHom)) :=
    ⟨Subgroup.equivMapOfInjective F₁ e.toMonoidHom e.injective⟩
  have e2 : Nonempty (↥F₂ ≃* ↥(F₂.map e.toMonoidHom)) :=
    ⟨Subgroup.equivMapOfInjective F₂ e.toMonoidHom e.injective⟩
  obtain ⟨t1⟩ := exists_equiv_top_bot ↥(StatedSL 2 K) ↥(StatedSL 2 K)
  obtain ⟨b1⟩ := exists_equiv_bot_top ↥(StatedSL 2 K) ↥(StatedSL 2 K)
  obtain ⟨e1⟩ := e1
  obtain ⟨e2⟩ := e2
  rcases commuting_normal_ne_bot_prod hA hA h1' h2' hc' with ⟨hn1, hn2⟩ | ⟨hn1, hn2⟩
  · exact ⟨⟨e1.trans ((MulEquiv.subgroupCongr hn1).trans t1)⟩,
      ⟨e2.trans ((MulEquiv.subgroupCongr hn2).trans b1)⟩⟩
  · exact ⟨⟨e1.trans ((MulEquiv.subgroupCongr hn1).trans b1)⟩,
      ⟨e2.trans ((MulEquiv.subgroupCongr hn2).trans t1)⟩⟩

end CFSG.RankThree.GF2n.Stroth80
