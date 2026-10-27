module

public import CFSG.RankThree.PartTwo.Sec21.Item21Statements
public import CFSG.RankThree.PartTwo.KFacts.KP14McLaughlin
public import CFSG.RankThree.PartTwo.Sec21.Item226Coord
import CFSG.RankThree.PartTwo.KFacts.K74Irreducible

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Blueprint
open scoped Matrix

@[expose] def Item217InL : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A E U : Subgroup G) (c : G) (L : Subgroup G),
    Sec21Pair G A E U c L → Nonempty (L ⧸ Subgroup.center L ≃* NativeSporadic.J3) → c ∈ L →
      Nat.card A = 3 ^ 4 ∧ IsIrreducibleOn (wStar A) ∧ (∃ t ∈ wStar A, IsTransvectionOn t) ∧
      (∃ P : Sylow 3 (wStar A), ∀ x ∈ (P : Subgroup (wStar A)), (x : MulAut A) ∈ starOf A L) ∧
      ∀ x ∈ starOf A L, ¬ IsTransvectionOn x

@[expose] def Item217NotInL : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A E U : Subgroup G) (c : G) (L : Subgroup G),
    Sec21Pair G A E U c L → Nonempty (L ⧸ Subgroup.center L ≃* NativeSporadic.J3) → c ∉ L →
      False

namespace Item21EarlyProof

variable {G : Type} [Group G] {A : Subgroup G}

theorem isIrreducibleOn_map_coordGL4 (f : Multiplicative (Fin 4 → ZMod 3) ≃* A)
    {S : Subgroup (MulAut A)} (hS : IsIrreducibleOn S) :
    CFSG.RankThree.SubgroupLists.IsIrreducibleOn (S.map (coordGL4 f)) := by
  intro W hW
  refine @KFacts.irreducible_coordHom (Fin 4 → ZMod 3) _ (Pi.Function.module _ _ _) G _ A f S hS
    W ?_
  rintro _ ⟨σ, hσ, rfl⟩ x hx
  have h := hW _ ⟨σ, hσ, rfl⟩ x hx
  rwa [coordGL4_mulVec] at h

theorem toAdd_symm_commutator (f : Multiplicative (Fin 4 → ZMod 3) ≃* A) (φ : MulAut A)
    (v : Fin 4 → ZMod 3) :
    Multiplicative.toAdd (f.symm ((f (Multiplicative.ofAdd v))⁻¹ * φ (f (Multiplicative.ofAdd v))))
      = (((coordGL4 f φ : GL (Fin 4) (ZMod 3)) : Matrix (Fin 4) (Fin 4) (ZMod 3)) - 1) *ᵥ v := by
  rw [Matrix.sub_mulVec, Matrix.one_mulVec, coordGL4_mulVec, coordLin4_apply, map_mul, map_inv,
    MulEquiv.symm_apply_apply, toAdd_mul, toAdd_inv, toAdd_ofAdd]
  abel

theorem toAdd_symm_apply (f : Multiplicative (Fin 4 → ZMod 3) ≃* A) (φ : MulAut A) (x : A) :
    Multiplicative.toAdd (f.symm (φ x)) =
      ((coordGL4 f φ : GL (Fin 4) (ZMod 3)) : Matrix (Fin 4) (Fin 4) (ZMod 3)) *ᵥ
        Multiplicative.toAdd (f.symm x) := by
  rw [coordGL4_mulVec, coordLin4_apply, ofAdd_toAdd, MulEquiv.apply_symm_apply]

theorem natCard_range_mulVecLin {k : Type*} [Field k] [Finite k] {d : ℕ}
    (N : Matrix (Fin d) (Fin d) k) :
    Nat.card (LinearMap.range N.mulVecLin) = Nat.card k ^ N.rank := by
  unfold Matrix.rank
  exact Module.natCard_eq_pow_finrank

theorem isTransvectionOn_iff_GL4 (hA : IsMulCommutative A)
    (f : Multiplicative (Fin 4 → ZMod 3) ≃* A) (φ : MulAut A) :
    IsTransvectionOn φ ↔ KFacts.KP14.IsTransvectionGL (coordGL4 f φ) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set M : Matrix (Fin 4) (Fin 4) (ZMod 3) :=
    ((coordGL4 f φ : GL (Fin 4) (ZMod 3)) : Matrix (Fin 4) (Fin 4) (ZMod 3)) with hM
  have hcard : Nat.card (commOf φ) = 3 ^ (M - 1).rank := by
    rw [card_commOf_eq_card_range4 hA f φ]
    have hset : (Set.range fun v : Fin 4 → ZMod 3 => (M - 1) *ᵥ v) =
        (LinearMap.range (M - 1).mulVecLin : Set (Fin 4 → ZMod 3)) := by
      ext w
      simp
    rw [hset]
    have h := natCard_range_mulVecLin (M - 1)
    rw [Nat.card_zmod] at h
    exact h
  have hfix : commOf φ ≤ fixedSubgroupOf φ ↔ (M - 1) * (M - 1) = 0 := by
    constructor
    · intro hle
      apply Matrix.mulVec_injective
      funext v
      rw [← Matrix.mulVec_mulVec, Matrix.zero_mulVec]
      set a : A := f (Multiplicative.ofAdd v)
      have hx : a⁻¹ * φ a ∈ commOf φ := mem_commOf φ a
      have hfx := hle hx
      rw [mem_fixedSubgroupOf] at hfx
      have h1 := toAdd_symm_apply f φ (a⁻¹ * φ a)
      rw [hfx, toAdd_symm_commutator f φ v] at h1
      rw [Matrix.sub_mulVec, Matrix.one_mulVec, ← h1, sub_self]
    · intro hsq x hx
      rw [mem_fixedSubgroupOf]
      obtain ⟨a, rfl⟩ := (mem_commOf_iff hA φ x).mp hx
      set v := Multiplicative.toAdd (f.symm a)
      have ha : a = f (Multiplicative.ofAdd v) := by simp [v]
      apply f.symm.injective
      apply Multiplicative.toAdd.injective
      rw [toAdd_symm_apply, ha, toAdd_symm_commutator f φ v]
      have h2 : (M - 1) *ᵥ ((M - 1) *ᵥ v) = 0 := by
        rw [Matrix.mulVec_mulVec, hsq, Matrix.zero_mulVec]
      rw [Matrix.sub_mulVec, Matrix.one_mulVec] at h2
      exact sub_eq_zero.mp h2
  constructor
  · rintro ⟨h3, hle⟩
    refine ⟨fun h1 => ?_, hfix.mp hle, ?_⟩
    · have hφ : φ = 1 := coordGL4_injective f (by rw [h1, map_one])
      rw [(commOf_eq_bot_iff φ).mpr hφ, Subgroup.card_bot] at h3
      omega
    · rw [hcard] at h3
      exact Nat.pow_right_injective (by norm_num : 2 ≤ 3) (by simpa using h3)
  · rintro ⟨-, hsq, hrk⟩
    exact ⟨by rw [hcard, hrk]; norm_num, hfix.mpr hsq⟩

end Item21EarlyProof

open Item21EarlyProof

theorem item217_of (hMcL : KFacts.KP14.SylowTransvectionGL43) (hIn : Item217InL)
    (hOut : Item217NotInL) : Item217 := by
  intro G _ _ A E U c L hpair
  refine ⟨fun e => ?_⟩
  by_cases hcL : c ∈ L
  · obtain ⟨hA81, hirr, ⟨t, htW, ht⟩, ⟨P, hPL⟩, hnoT⟩ := hIn G A E U c L hpair ⟨e⟩ hcL
    have hAe : CFSG.Assembly.IsElemAbelian 3 A := hpair.mem_S.1.1
    obtain ⟨f⟩ := Sec12.exists_coords hAe hA81
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    set W' := (wStar A).map (coordGL4 f) with hW'
    let eW : wStar A ≃* W' := (wStar A).equivMapOfInjective (coordGL4 f) (coordGL4_injective f)
    obtain ⟨x, hxP, hx⟩ := hMcL W' (isIrreducibleOn_map_coordGL4 f hirr)
      ⟨coordGL4 f t, ⟨t, htW, rfl⟩, (isTransvectionOn_iff_GL4 hAe.1 f t).mp ht⟩
      (P.mapSurjective (f := eW.toMonoidHom) fun y => eW.surjective y)
    have hxP' : x ∈ (P : Subgroup (wStar A)).map eW.toMonoidHom := hxP
    obtain ⟨y, hyP, rfl⟩ := hxP'
    exact hnoT _ (hPL y hyP) ((isTransvectionOn_iff_GL4 hAe.1 f _).mpr hx)
  · exact hOut G A E U c L hpair ⟨e⟩ hcL

end CFSG.RankThree.PartTwo.Sec21
