module

public import CFSG.RankThree.PartOne.TAIL.KSideCen
public import CFSG.RankThree.PartOne.TAIL.KSideSing
public import CFSG.RankThree.PartOne.TAIL.KSideOutLin
public import CFSG.CharacterTheory.Semidihedral.SemilinearOuterQuotient

public section

namespace CFSG.RankThree.PartOne.TAIL

open Subgroup CFSG CFSG.Assembly CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.GroupTheory

theorem sylow_transport {G : Type} [Group G] {K : Subgroup G} {X : Type*} [Group X]
    (e : ↥K ≃* X) (hX : ∀ R : Subgroup X, IsPGroup 7 R → IsCyclic ↥R ∧ Nat.card ↥R ≤ 49) :
    ∀ R : Subgroup G, R ≤ K → IsPGroup 7 R → IsCyclic ↥R ∧ Nat.card ↥R ≤ 49 := by
  intro R hRK hR
  have hRK' : IsPGroup 7 (R.subgroupOf K) := hR.comap_subtype
  have hRX : IsPGroup 7 ((R.subgroupOf K).map e.toMonoidHom) := hRK'.map _
  obtain ⟨hcyc, hcard⟩ := hX _ hRX
  have e1 : ↥(R.subgroupOf K) ≃* ↥((R.subgroupOf K).map e.toMonoidHom) :=
    Subgroup.equivMapOfInjective _ e.toMonoidHom e.injective
  have e2 : ↥(R.subgroupOf K) ≃* ↥R := Subgroup.subgroupOfEquivOfLe hRK
  refine ⟨?_, ?_⟩
  · exact (e2.isCyclic).1 ((e1.isCyclic).2 hcyc)
  · rw [← Nat.card_congr e2.toEquiv, Nat.card_congr e1.toEquiv]
    exact hcard

theorem kData_of_model_lin {G : Type} [Group G] [Finite G] {K : Subgroup G} {c : G} {m : ℕ}
    {F : Type} [Field F] [Finite F] (hm : m = 3 ∨ m = 4) (hF : Nat.card F = 2 ^ 7)
    (e : ↥K ≃* Matrix.SpecialLinearGroup (Fin m) F) (hc7 : c ^ 7 = 1)
    (hc : InducesFieldAut 7 c K) : KData G K c := by
  have hg : Nat.gcd m (Nat.card F - 1) = 1 := by
    rw [hF]
    rcases hm with rfl | rfl <;> norm_num
  have hm0 : m ≠ 0 := by rcases hm with rfl | rfl <;> norm_num
  have hZ : K ⊓ Subgroup.centralizer (K : Set G) = ⊥ :=
    inf_centralizer_eq_bot_of_mulEquiv e (center_sl_eq_bot hm0 hg)
  have hS : ∀ R : Subgroup G, R ≤ K → IsPGroup 7 R → IsCyclic ↥R ∧ Nat.card ↥R ≤ 49 := by
    refine sylow_transport e ?_
    rcases hm with rfl | rfl
    · exact fun R hR => sylow_sl_three hF R hR
    · exact fun R hR => sylow_sl_four hF R hR
  have hAut : Nat.card (F ≃+* F) ∣ 21 := by
    rw [CFSG.Semidihedral.SemilinearOuterQuotient.fieldAut_card F Nat.prime_two hF]
    norm_num
  have hO : OutData ↥K := by
    refine OutData.of_mulEquiv e (outData_sl ?_ hg hAut)
    rcases hm with rfl | rfl <;> norm_num
  exact kData_of_parts hZ hS hO hc7 hc

end CFSG.RankThree.PartOne.TAIL
