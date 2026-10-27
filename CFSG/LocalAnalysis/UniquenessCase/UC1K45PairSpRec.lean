module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PCore
public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UCK.PairSpLem

open Subgroup

@[expose] def PairShape (Q : Type) [Group Q] : Prop :=
  (IsCyclic Q ∧ Nat.card Q = 3) ∨ (Nat.card Q = 9 ∧ IsMulCommutative Q) ∨
    Nonempty (Q ≃* alternatingGroup (Fin 5))

@[expose] def PairShapeHom (Y : Type) [Group Y] : Prop :=
  ∃ (Q : Type) (_ : Group Q) (f : Y →* Q), Function.Surjective f ∧ IsPGroup 2 f.ker ∧
    CFSG.pCore 2 Q = ⊥ ∧ PairShape Q

@[expose] def memA {G : Type*} [Group G] (a b : G) : ↥(Subgroup.closure ({a, b} : Set G)) :=
  ⟨a, Subgroup.subset_closure (Set.mem_insert _ _)⟩

@[expose] def memB {G : Type*} [Group G] (a b : G) : ↥(Subgroup.closure ({a, b} : Set G)) :=
  ⟨b, Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))⟩

theorem closure_pair_induction {G : Type*} [Group G] {a b : G}
    {p : ↥(Subgroup.closure ({a, b} : Set G)) → Prop} (ha : p (memA a b)) (hb : p (memB a b))
    (hone : p 1) (hmul : ∀ x y, p x → p y → p (x * y)) (hinv : ∀ x, p x → p x⁻¹) :
    ∀ x, p x := by
  rintro ⟨x, hx⟩
  induction hx using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with rfl | hx
    · exact ha
    · rw [Set.mem_singleton_iff] at hx
      subst hx
      exact hb
  | one => exact hone
  | mul x y hx hy ihx ihy => exact hmul ⟨x, hx⟩ ⟨y, hy⟩ ihx ihy
  | inv x hx ihx => exact hinv ⟨x, hx⟩ ihx

theorem isPGroup_two_ker_of_pow_four {Y Q : Type*} [Group Y] [Group Q] (f : Y →* Q)
    (h : ∀ y : Y, f y = 1 → y ^ 4 = 1) : IsPGroup 2 f.ker := by
  intro g
  refine ⟨2, Subtype.ext ?_⟩
  simpa using h g.1 g.2

theorem pCore_eq_bot_of_odd_card {Q : Type*} [Group Q] (h : Odd (Nat.card Q)) :
    CFSG.pCore 2 Q = ⊥ := by
  haveI : Finite Q := Nat.finite_of_card_ne_zero (by
    intro h0
    rw [h0] at h
    exact absurd h (by decide))
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp (CFSG.pCore_isPGroup (p := 2) (G := Q))
  have hdvd : Nat.card (CFSG.pCore 2 Q) ∣ Nat.card Q := Subgroup.card_subgroup_dvd_card _
  rw [hn] at hdvd
  have hn0 : n = 0 := by
    by_contra hne
    exact (Nat.not_even_iff_odd.mpr h) (even_iff_two_dvd.mpr ((dvd_pow_self 2 hne).trans hdvd))
  rw [hn0, pow_zero] at hn
  exact Subgroup.eq_bot_of_card_eq _ hn

theorem pCore_alt5_eq_bot : CFSG.pCore 2 ↥(alternatingGroup (Fin 5)) = ⊥ := by
  haveI : IsSimpleGroup (alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup (by simp)
  haveI : (CFSG.pCore 2 ↥(alternatingGroup (Fin 5))).Normal := CFSG.pCore_normal
  rcases Subgroup.Normal.eq_bot_or_eq_top (CFSG.pCore 2 ↥(alternatingGroup (Fin 5))) with h | h
  · exact h
  · exfalso
    have hp := CFSG.pCore_isPGroup (p := 2) (G := ↥(alternatingGroup (Fin 5)))
    rw [h] at hp
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hp
    rw [Subgroup.card_top, nat_card_alternatingGroup] at hn
    have h3 : 3 ∣ 2 ^ n := by
      rw [← hn, Nat.card_eq_fintype_card, Fintype.card_fin]
      decide
    have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3
    omega

theorem pCore_eq_ker {Y Q : Type*} [Group Y] [Group Q] (f : Y →* Q)
    (hf : Function.Surjective f) (hker : IsPGroup 2 f.ker) (hQ : CFSG.pCore 2 Q = ⊥) :
    CFSG.pCore 2 Y = f.ker := by
  apply le_antisymm
  · have hnorm : ((CFSG.pCore 2 Y).map f).Normal := (CFSG.pCore_normal (p := 2) (G := Y)).map f hf
    have hp : IsPGroup 2 ((CFSG.pCore 2 Y).map f) :=
      (CFSG.pCore_isPGroup (p := 2) (G := Y)).map f
    have hle : (CFSG.pCore 2 Y).map f ≤ CFSG.pCore 2 Q := le_sSup ⟨hnorm, hp⟩
    rw [hQ, le_bot_iff, Subgroup.map_eq_bot_iff] at hle
    exact hle
  · exact le_sSup ⟨inferInstance, hker⟩

theorem pairShapeHom_of_cyclic3 {Y Q : Type} [Group Y] [Group Q] (f : Y →* Q)
    (hf : Function.Surjective f) (hker : IsPGroup 2 f.ker) (hcyc : IsCyclic Q)
    (hcard : Nat.card Q = 3) : PairShapeHom Y :=
  ⟨Q, inferInstance, f, hf, hker, pCore_eq_bot_of_odd_card (by rw [hcard]; decide),
    Or.inl ⟨hcyc, hcard⟩⟩

theorem pairShapeHom_of_commutative9 {Y : Type} [Group Y] (hcomm : IsMulCommutative Y)
    (hcard : Nat.card Y = 9) : PairShapeHom Y :=
  ⟨Y, inferInstance, MonoidHom.id Y, Function.surjective_id,
    by rw [MonoidHom.ker_id]; exact IsPGroup.of_bot,
    pCore_eq_bot_of_odd_card (by rw [hcard]; decide), Or.inr (Or.inl ⟨hcard, hcomm⟩)⟩

theorem pairShapeHom_of_alt5 {Y : Type} [Group Y] (f : Y →* ↥(alternatingGroup (Fin 5)))
    (hf : Function.Surjective f) (hker : IsPGroup 2 f.ker) : PairShapeHom Y :=
  ⟨↥(alternatingGroup (Fin 5)), inferInstance, f, hf, hker, pCore_alt5_eq_bot,
    Or.inr (Or.inr ⟨MulEquiv.refl _⟩)⟩

end CFSG.LocalAnalysis.UniquenessCase.UCK.PairSpLem
