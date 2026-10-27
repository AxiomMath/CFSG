module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtL2BlockArith
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtL2BlockBorel
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L238BridgeAlt57

public section

namespace CFSG.QuasithinUnique.Bridge

open CFSG.Quasithin CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement

namespace L2Block

variable {S : Type} [CommGroup S] [Finite S] {G L : Subgroup (MulAut S)} {n : ℕ}

structure Ctx (G L : Subgroup (MulAut S)) (n : ℕ) : Prop where
  three_le : 3 ≤ n
  psl : IsPSL 2 2 n ↥L
  hF : L = quasithinGenFitting G
  hsq : ∀ y ∈ G, y ^ 2 ∈ L

namespace Ctx

variable (C : Ctx G L n)

include C

theorem simple : IsSimpleGroup ↥L :=
  RankOneRecog.isSimpleGroup_of_fusionIsBenderGroup (A5.C25.fusionIsBenderGroup_of_isPSL C.psl)

omit [Finite S] in
theorem center_bot : Subgroup.center ↥L = ⊥ := GoldMLA.center_eq_bot_of_isPSL C.psl

omit [Finite S] in
theorem card_eq : Nat.card ↥L = 2 ^ n * (4 ^ n - 1) := by
  obtain ⟨K, hF, hfin, hchar, hcard, ⟨e⟩⟩ := S151S4.exists_equiv_sl2 C.psl
  rw [Nat.card_congr e.toEquiv, CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two K, hcard,
    ← pow_mul, mul_comm n 2, pow_mul]
  norm_num

omit [Finite S] in
theorem no4 : ∀ g : ↥L, g ^ 4 = 1 → g ^ 2 = 1 := by
  obtain ⟨K, hF, hfin, hchar, hcard, ⟨e⟩⟩ := S151S4.exists_equiv_sl2 C.psl
  intro g hg
  apply e.injective
  rw [map_pow, map_one]
  exact GoldL2.sl2_sq_eq_one_of_pow_four (e g) (by rw [← map_pow, hg, map_one])

omit [Finite S] in
theorem normal : ∀ g ∈ G, ∀ l ∈ L, g * l * g⁻¹ ∈ L :=
  FStarSimple.normal C.hF

theorem le_ffJ {A : Subgroup (MulAut S)} (hA : IsFFStarOffender G A) : L ≤ ffJ G :=
  FStarSimple.le_ffJ C.hF C.simple C.center_bot hA

omit [Finite S] in
theorem hnorm : (L.subgroupOf (ffJ G)).Normal := ⟨fun l hl g => by
  rw [Subgroup.mem_subgroupOf] at hl ⊢
  exact C.normal (g : MulAut S) (Alt57.ffJ_le G g.2) _ hl⟩

end Ctx

end L2Block

end CFSG.QuasithinUnique.Bridge
