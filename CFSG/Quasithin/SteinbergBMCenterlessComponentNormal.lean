module

public import Mathlib.GroupTheory.NoncommCoprod
public import CFSG.GroupTheory.LocalCores.Components

public section

namespace CFSG.Quasithin.SteinbergBM

open Subgroup

variable {X : Type*} [Group X]

theorem bddAbove_pRank_set [Finite X] {p : ℕ} (hp : 1 < p) :
    BddAbove {r : ℕ | ∃ B : Subgroup X, CFSG.IsElementaryAbelian p B ∧ Nat.card B = p ^ r} := by
  refine ⟨Nat.card X, ?_⟩
  rintro r ⟨B, -, hB⟩
  have h := Subgroup.card_le_card_group B
  rw [hB] at h
  exact ((Nat.lt_pow_self hp).le).trans h

theorem exists_card_eq_pow_pRank [Finite X] {p : ℕ} (hp : 1 < p) :
    ∃ B : Subgroup X, CFSG.IsElementaryAbelian p B ∧ Nat.card B = p ^ CFSG.pRank p X := by
  have hbot : CFSG.IsElementaryAbelian p (⊥ : Subgroup X) :=
    { toIsMulCommutative := ⟨⟨fun a b => Subsingleton.elim _ _⟩⟩
      exponent_dvd_p :=
        Monoid.exponent_dvd_of_forall_pow_eq_one fun _ => Subsingleton.elim _ _ }
  have hne : {r : ℕ | ∃ B : Subgroup X, CFSG.IsElementaryAbelian p B ∧
      Nat.card B = p ^ r}.Nonempty := ⟨0, ⊥, hbot, by rw [card_bot, pow_zero]⟩
  exact Nat.sSup_mem hne (bddAbove_pRank_set hp)

theorem card_sup_of_commute {U U' : Subgroup X} (hcomm : U' ≤ centralizer (U : Set X))
    (hdisj : U ⊓ U' = ⊥) : Nat.card (U ⊔ U' : Subgroup X) = Nat.card U * Nat.card U' := by
  have hc : ∀ (m : U) (n : U'), Commute (U.subtype m) (U'.subtype n) := fun m n =>
    (mem_centralizer_iff.mp (hcomm n.2)) m m.2
  have hinj : Function.Injective (U.subtype.noncommCoprod U'.subtype hc) := by
    rw [MonoidHom.noncommCoprod_injective]
    refine ⟨U.subtype_injective, U'.subtype_injective, ?_⟩
    rw [range_subtype, range_subtype, disjoint_iff]
    exact hdisj
  have hrange : (U.subtype.noncommCoprod U'.subtype hc).range = U ⊔ U' := by
    rw [MonoidHom.noncommCoprod_range, range_subtype, range_subtype]
  rw [← hrange, ← Nat.card_prod]
  exact (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm

theorem centerless_component_rank_forces_normality [Finite X] {p : ℕ} (hp : p.Prime)
    {A : Subgroup X} (hA : CFSG.IsComponent A) (hZ : center A = ⊥)
    (hrank : CFSG.pRank p X < 2 * CFSG.pRank p A) : A.Normal := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨U, hU, hUcard⟩ := exists_card_eq_pow_pRank (X := A) hp.one_lt
  set r := CFSG.pRank p A
  set U₀ : Subgroup X := U.map A.subtype with hU₀
  have hU₀A : U₀ ≤ A := map_subtype_le U
  have hU₀card : Nat.card U₀ = p ^ r := by
    rw [hU₀, card_map_of_injective A.subtype_injective, hUcard]
  have hU₀e : CFSG.IsElementaryAbelian p U₀ := CFSG.IsElementaryAbelian.map_subtype
  refine ⟨fun a ha x => ?_⟩
  set A' : Subgroup X := A.map (MulAut.conj x).toMonoidHom with hA'
  have hA'c : CFSG.IsComponent A' := CFSG.LocalCores.isComponent_map_mulEquiv _ hA
  have hmem : x * a * x⁻¹ ∈ A' := ⟨a, ha, rfl⟩
  rcases CFSG.LocalCores.distinct_components_commute hA hA'c with h | h
  · exact h ▸ hmem
  exfalso
  have hA'C : A' ≤ centralizer (A : Set X) :=
    commutator_eq_bot_iff_le_centralizer.mp (by rw [commutator_comm]; exact h)
  have hAA' : A ⊓ A' = ⊥ := by
    rw [eq_bot_iff]
    intro y ⟨hyA, hyA'⟩
    have hyZ : (⟨y, hyA⟩ : A) ∈ center A := by
      rw [mem_center_iff]
      intro b
      exact Subtype.ext ((mem_centralizer_iff.mp (hA'C hyA')) b b.2)
    rw [hZ, mem_bot] at hyZ
    exact mem_bot.mpr (congrArg Subtype.val hyZ)
  set U₁ : Subgroup X := U₀.map (MulAut.conj x).toMonoidHom with hU₁
  have hU₁A' : U₁ ≤ A' := map_mono hU₀A
  have hU₁card : Nat.card U₁ = p ^ r := by
    rw [hU₁, card_map_of_injective (MulAut.conj x).injective, hU₀card]
  have hU₁e : CFSG.IsElementaryAbelian p U₁ := CFSG.IsElementaryAbelian.map _
  have hcomm : U₁ ≤ centralizer (U₀ : Set X) :=
    (hU₁A'.trans hA'C).trans (centralizer_le hU₀A)
  have hdisj : U₀ ⊓ U₁ = ⊥ := le_bot_iff.mp (hAA' ▸ inf_le_inf hU₀A hU₁A')
  have hWe : CFSG.IsElementaryAbelian p (U₀ ⊔ U₁ : Subgroup X) :=
    CFSG.IsElementaryAbelian.sup_of_le_centralizer hcomm
  have hWcard : Nat.card (U₀ ⊔ U₁ : Subgroup X) = p ^ (2 * r) := by
    rw [card_sup_of_commute hcomm hdisj, hU₀card, hU₁card, ← pow_add, two_mul]
  have hle : 2 * r ≤ CFSG.pRank p X :=
    le_csSup (bddAbove_pRank_set hp.one_lt) ⟨_, hWe, hWcard⟩
  omega

end CFSG.Quasithin.SteinbergBM
