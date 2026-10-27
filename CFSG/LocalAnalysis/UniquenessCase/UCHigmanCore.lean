module

public import CFSG.LocalAnalysis.UniquenessCase.UCHigmanDesc
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Blueprint.Catalog
public import CFSG.RankThree.FFModules.Offenders

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UCK.Higman

open Matrix CFSG.Open CFSG.Blueprint
open scoped MatrixGroups

section Final

theorem sl2_of_lieModel {G : Type} [Group G] {n : ℕ} (hL : LieModel G .PSL 2 2 n) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K 2), Nat.card K = 2 ^ n ∧
      Nonempty (G ≃* SL(2, K)) := by
  rcases hL with ⟨-, ⟨-, K, hKf, hKfin, hK, ⟨e⟩⟩⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩
  · have hK2 : 2 ≤ Nat.card K := Finite.one_lt_card
    have hn1 : 1 ≤ n := by
      by_contra hn0
      have : n = 0 := by omega
      rw [this, pow_zero] at hK
      omega
    haveI : Fintype K := Fintype.ofFinite K
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    haveI hchar : CharP K 2 := charP_of_card_eq_prime_pow (f := n)
      (by rw [← Nat.card_eq_fintype_card, hK])
    refine ⟨K, hKf, hKfin, hchar, hK, ⟨?_⟩⟩
    let e' : G ≃* StatedSL 2 K ⧸ (StatedScalars (Fin 2) K).subgroupOf (StatedSL 2 K) := e
    exact (e'.trans ((QuotientGroup.quotientMulEquivOfEq
      (CFSG.Open.StatedAPI.statedScalars_subgroupOf_statedSL_two_eq_bot (K := K))).trans
      QuotientGroup.quotientBot)).trans
      (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 2 K).symm
  · exact absurd h (by decide)
  · exact absurd h (by decide)
  · exact absurd h (by decide)

theorem simple_of_irreducible {G : Type} [Group G] {V : Type} [AddCommGroup V]
    [Module (ZMod 2) V] (ρ : Representation (ZMod 2) G V) (hirr : ρ.IsIrreducible) :
    Nontrivial V ∧ ∀ W : Submodule (ZMod 2) V, (∀ g : G, ∀ w ∈ W, ρ g w ∈ W) →
      W = ⊥ ∨ W = ⊤ := by
  refine ⟨?_, fun W hW => ?_⟩
  · by_contra hV
    rw [not_nontrivial_iff_subsingleton] at hV
    have h1 : (⊥ : Subrepresentation ρ) = ⊤ := by
      apply Subrepresentation.ext
      exact Subsingleton.elim _ _
    exact bot_ne_top h1
  · have := IsSimpleOrder.eq_bot_or_eq_top (⟨W, fun g v hv => hW g v hv⟩ : Subrepresentation ρ)
    rcases this with h | h
    · left; exact congrArg Subrepresentation.toSubmodule h
    · right; exact congrArg Subrepresentation.toSubmodule h

theorem twist_injective (K : Type) [Field K] [ExpChar K 2] (i : ℕ) :
    Function.Injective (Matrix.SpecialLinearGroup.map (iterateFrobenius K 2 i) :
      SL(2, K) →* SL(2, K)) := by
  intro a b h
  apply Subtype.ext
  ext x y
  have := congrFun (congrFun (congrArg (fun g : SL(2, K) => (g : Matrix (Fin 2) (Fin 2) K)) h) x) y
  exact (iterateFrobenius K 2 i).injective (by simpa using this)

@[expose] noncomputable def twistEquiv (K : Type) [Field K] [Finite K] [CharP K 2] (i : ℕ) :
    SL(2, K) ≃* SL(2, K) :=
  haveI : ExpChar K 2 := ExpChar.prime Nat.prime_two
  MulEquiv.ofBijective (Matrix.SpecialLinearGroup.map (iterateFrobenius K 2 i))
    ⟨twist_injective K i, Finite.surjective_of_injective (twist_injective K i)⟩

theorem exists_gen_of_card_three {G : Type} [Group G] (D : Subgroup G) (hD : Nat.card D = 3) :
    ∃ d : G, D = Subgroup.zpowers d ∧ d ^ 3 = 1 ∧ d ≠ 1 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : IsCyclic D := isCyclic_of_prime_card hD
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := D)
  refine ⟨(g : G), ?_, ?_, ?_⟩
  · apply le_antisymm
    · intro x hx
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 (hg ⟨x, hx⟩)
      exact Subgroup.mem_zpowers_iff.2 ⟨k, by simpa using congrArg Subtype.val hk⟩
    · rw [Subgroup.zpowers_le]
      exact g.2
  · have h := pow_card_eq_one' (G := D) (x := g)
    rw [hD] at h
    simpa using congrArg Subtype.val h
  · intro h1
    have hg1 : g = 1 := Subtype.ext h1
    haveI : Subsingleton D := ⟨fun a b => by
      obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.1 (hg a)
      obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.1 (hg b)
      rw [← hi, ← hj, hg1]
      simp⟩
    have := Nat.card_of_subsingleton (1 : D)
    omega

theorem fixed_of_zpowers {G : Type} [Group G] {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) G V) (d : G) (w : V) (hw : ρ d w = w) :
    ∀ a ∈ Subgroup.zpowers d, ρ a w = w := by
  let H : Subgroup G :=
    { carrier := {a | ρ a w = w}
      mul_mem' := fun {a b} ha hb => by
        change ρ (a * b) w = w
        change ρ a w = w at ha
        change ρ b w = w at hb
        rw [map_mul, Module.End.mul_apply, hb, ha]
      one_mem' := by
        change ρ 1 w = w
        simp
      inv_mem' := fun {a} ha => by
        change ρ a⁻¹ w = w
        change ρ a w = w at ha
        have h2 : ρ a⁻¹ (ρ a w) = w := by
          rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
        rwa [ha] at h2 }
  have hH : Subgroup.zpowers d ≤ H := (Subgroup.zpowers_le).2 hw
  intro a ha
  exact hH ha

end Final

open CFSG.RankThree.FFModules (fixSub mem_fixSub)

theorem exists_natural_of_fixSub_eq_bot {G : Type} [Group G] {n : ℕ} (hL : LieModel G .PSL 2 2 n)
    {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V] (ρ : Representation (ZMod 2) G V)
    (hirr : ρ.IsIrreducible) (D : Subgroup G) (hD : Nat.card D = 3) (hfix : fixSub ρ D = ⊥) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (φ : G ≃* SL(2, F)) (ψ : V ≃+ (Fin 2 → F)),
      Nat.card F = 2 ^ n ∧
        ∀ (g : G) (v : V), ψ (ρ g v) = ((φ g : Matrix (Fin 2) (Fin 2) F)).mulVec (ψ v) := by
  obtain ⟨K, hKf, hKfin, hchar, hn, ⟨θ⟩⟩ := sl2_of_lieModel hL
  obtain ⟨hnt, hsimple⟩ := simple_of_irreducible ρ hirr
  obtain ⟨d, hDd, hd3, hd1⟩ := exists_gen_of_card_three D hD
  have hdV : ∀ v : V, ρ d (ρ d v) + ρ d v + v = 0 := by
    intro v
    have h3 : ρ d (ρ d (ρ d v)) = v := by
      have h : ρ (d ^ 3) v = v := by rw [hd3]; simp
      rw [pow_succ, pow_two, map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply] at h
      exact h
    have hw : ρ d (ρ d (ρ d v) + ρ d v + v) = ρ d (ρ d v) + ρ d v + v := by
      rw [map_add, map_add, h3]
      abel
    have hmem : ρ d (ρ d v) + ρ d v + v ∈ fixSub ρ D := by
      rw [mem_fixSub]
      intro a ha
      rw [hDd] at ha
      exact fixed_of_zpowers ρ d _ hw a ha
    rw [hfix] at hmem
    exact (Submodule.mem_bot _).1 hmem
  let ρ' : Representation (ZMod 2) SL(2, K) V := MonoidHom.comp ρ θ.symm.toMonoidHom
  have hρ' : ∀ (g : G) (v : V), ρ' (θ g) v = ρ g v := by
    intro g v
    simp [ρ']
  have hsimple' : ∀ W : Submodule (ZMod 2) V,
      (∀ (g : SL(2, K)), ∀ w ∈ W, ρ' g w ∈ W) → W = ⊥ ∨ W = ⊤ := by
    intro W hW
    apply hsimple W
    intro g w hw
    have := hW (θ g) w hw
    rwa [hρ'] at this
  have hθd3 : (θ d) ^ 3 = 1 := by rw [← map_pow, hd3, map_one]
  have hθd1 : θ d ≠ 1 := fun h => hd1 (θ.injective (by rw [h, map_one]))
  have hdV' : ∀ v : V, ρ' (θ d) (ρ' (θ d) v) + ρ' (θ d) v + v = 0 := by
    intro v
    simp only [hρ']
    exact hdV v
  obtain ⟨i, -, ψ, hψ⟩ := descent_natural hn ρ' hsimple' (θ d) hθd3 hθd1 hdV'
  refine ⟨K, hKf, hKfin, θ.trans (twistEquiv K i), ψ, hn, fun g v => ?_⟩
  have h := hψ (θ g) v
  rw [hρ'] at h
  rw [h]
  rfl

end CFSG.LocalAnalysis.UniquenessCase.UCK.Higman
