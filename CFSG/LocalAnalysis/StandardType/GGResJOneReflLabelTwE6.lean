module

public import CFSG.LocalAnalysis.StandardType.GGTableBNoncyclic
public import CFSG.LocalAnalysis.StandardType.GGTwE6RecipeTransport
import CFSG.LocalAnalysis.StandardType.GGExcFieldRankTwE6
import CFSG.LocalAnalysis.StandardType.GGSixOrderPAutInnerExcSylowTorus

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

private theorem ggJORLEAux_notCyclic_of_elemAbelian {X : Type} [Group X] {A : Subgroup X}
    (hA : IsElemAbelian 3 A) (h : 9 ≤ Nat.card A) :
    IsPGroup 3 A ∧ ¬ IsCyclic A := by
  have hpow : ∀ x : A, x ^ 3 = 1 := fun x => Subtype.ext (by simpa using hA.2 x x.2)
  refine ⟨fun x => ⟨1, by simpa using hpow x⟩, ?_⟩
  intro hcyc
  have hexp : Monoid.exponent A ∣ 3 := Monoid.exponent_dvd_of_forall_pow_eq_one hpow
  rw [IsCyclic.exponent_eq_card] at hexp
  have hle : Nat.card A ≤ 3 := Nat.le_of_dvd (by norm_num) hexp
  omega

private theorem ggJORLEAux_degCountTw_two :
    CFSG.LieType.SeitzGeneration.degCountTw 2 = 6 := by
  rw [CFSG.LieType.SeitzGeneration.degCountTw,
    show CFSG.LieType.SeitzGeneration.ennola 2 = 1 from by decide]
  decide

theorem largeEvenLabelAll_noncyclic_three_twE6
    {l n : ℕ} (hn : 1 ≤ n) (h3 : 3 ∣ 2 ^ n + 1) :
    LargeEvenLabelAll ⟨.twE6, l, n⟩ fun R _ _ _ =>
      ∃ F : Subgroup R, IsPGroup 3 F ∧ ¬ IsCyclic F := by
  intro Q hQ
  dsimp only [CFSG.StandardType.LargeEvenRawDatum, LargeEvenRecipeTwisted] at hQ ⊢
  obtain ⟨K, _, _, hK, hq⟩ := hQ
  have : CharP K 2 := charP_two_of_card (m := n * 2) (by rw [hK, pow_mul])
  obtain ⟨σ, hσ, ε, -⟩ := TwE6Transport.exists_recipeConj hn hK
  have he : orderOf (((2 ^ n : ℕ)) : ZMod 3) = 2 :=
    OrdPInnerExc.orderOf_natCast_eq_two_of_dvd_add_one Nat.prime_three (by norm_num) h3
  obtain ⟨E, hEel, hEcard⟩ :=
    exists_twistedE6 Nat.prime_two hn K hK σ hσ (p := 3) (e := 2) Nat.prime_three
      (by norm_num) he
  let ψ : ↥(CFSG.LieType.Chevalley.twistedE6RootGroup K σ) →*
      LargeEvenCenterQuot (LargeEvenTwistedH (LargeEvenCartanE 6) K LargeEvenRhoE6 n) := ε
  let F : Subgroup
      (LargeEvenCenterQuot (LargeEvenTwistedH (LargeEvenCartanE 6) K LargeEvenRhoE6 n)) :=
    E.map ψ
  have hFel : IsElemAbelian 3 F := by
    change IsElemAbelian 3 (E.map ψ)
    exact hEel.map ψ
  have hψinj : Function.Injective ψ := ε.injective
  have hFcard : Nat.card F = Nat.card E := by
    change Nat.card (E.map ψ) = Nat.card E
    exact Subgroup.card_map_of_injective (f := ψ) hψinj
  have hE9 : 9 ≤ Nat.card E := by
    rw [ggJORLEAux_degCountTw_two] at hEcard
    norm_num at hEcard ⊢
    omega
  have hF9 : 9 ≤ Nat.card F := by rw [hFcard]; exact hE9
  refine ⟨K, inferInstance, inferInstance, hK, hq, F, ?_⟩
  exact ggJORLEAux_notCyclic_of_elemAbelian hFel hF9

end CFSG.StandardType

end
