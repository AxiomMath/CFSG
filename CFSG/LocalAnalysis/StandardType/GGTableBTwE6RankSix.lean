module

public import CFSG.LocalAnalysis.StandardType.GGTableBTwE6PerBstar
public import CFSG.LocalAnalysis.StandardType.GGTableBExcE6Basic

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

namespace TwE6Rank

theorem dvd_card_sub_one {n : ℕ} {K : Type} (hK : Nat.card K = (2 ^ n) ^ 2) {p : ℕ}
    (hpn : p ∣ 2 ^ n + 1) : p ∣ Nat.card K - 1 := by
  obtain ⟨m, hm⟩ : ∃ m, 2 ^ n = m + 1 := ⟨2 ^ n - 1, by have := Nat.one_le_two_pow (n := n); omega⟩
  have e : (2 ^ n) ^ 2 - 1 = (2 ^ n + 1) * m := by
    rw [hm, show (m + 1) ^ 2 = (m + 1 + 1) * m + 1 by ring, Nat.add_sub_cancel]
  rw [hK, e]
  exact Dvd.dvd.mul_right hpn m


variable {n : ℕ} {K : Type} [Field K] [Finite K]

theorem exists_injective_adjointGroup (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 2) :
    ∃ ψ : TwE6Delta.RecipeR K n →* adjointGroup TwistTag.E6.tag K, Function.Injective ψ := by
  have : CharP K 2 := charP_two_of_card (m := n * 2) (by rw [hK, pow_mul])
  obtain ⟨-, T, -, -⟩ := InnerDiagTwE6.exists_twistedTransport (K := K) n
    (iterateFrobenius K 2 n) (iterateFrobenius_def 2 n)
  have hZ := TwE6Delta.center_recipeH_eq_bot hn hK
  have hΓ : twistedFixedGroup .E6 K (iterateFrobenius K 2 n) ≤ adjointGroup TwistTag.E6.tag K :=
    inf_le_left
  have hle : ⁅twistedFixedGroup .E6 K (iterateFrobenius K 2 n),
      twistedFixedGroup .E6 K (iterateFrobenius K 2 n)⁆ ≤ adjointGroup TwistTag.E6.tag K := by
    refine Subgroup.commutator_le.2 fun a ha b hb => hΓ ?_
    rw [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem ha hb) (inv_mem ha)) (inv_mem hb)
  let e₁ : TwE6Delta.RecipeR K n ≃* TwE6Delta.RecipeH K n :=
    (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
  exact ⟨(Subgroup.inclusion hle).comp (T.symm.toMonoidHom.comp e₁.toMonoidHom),
    (Subgroup.inclusion_injective hle).comp (T.symm.injective.comp e₁.injective)⟩

theorem card_le_of_isElemAbelian (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 2) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3) (hpn : p ∣ 2 ^ n + 1)
    {A : Subgroup (TwE6Delta.RecipeR K n)} (hA : IsElemAbelian p A) : Nat.card A ≤ p ^ 6 := by
  obtain ⟨ψ, hψ⟩ := exists_injective_adjointGroup hn hK
  have hpq := dvd_card_sub_one hK hpn
  have hT : GGExcToralRankInput TwistTag.E6.tag K p :=
    TableBExc.ggExcToralRankInput_E6_of_ne_three hp hp2 hp3 hpq
  have hV : Nat.card (TableBExc.torusPow TwistTag.E6.tag K p) = p ^ TwistTag.E6.tag.rank :=
    TableBExc.card_torusPow_E6 hp hp3 hpq
  have hE : IsElemAbelian p (A.map ψ) :=
    ⟨IsMulCommutative.of_comm fun x y => by
      obtain ⟨a, ha, hax⟩ := Subgroup.mem_map.1 x.2
      obtain ⟨b, hb, hby⟩ := Subgroup.mem_map.1 y.2
      have hab : a * b = b * a :=
        congrArg (fun z : A => (z : TwE6Delta.RecipeR K n)) (hA.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
      apply Subtype.ext
      change (x : adjointGroup TwistTag.E6.tag K) * y = y * x
      rw [← hax, ← hby, ← map_mul, ← map_mul, hab],
    fun x hx => by
      obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.1 hx
      rw [← map_pow, hA.2 a ha, map_one]⟩
  calc Nat.card A = Nat.card (A.map ψ) := (Subgroup.card_map_of_injective hψ).symm
    _ ≤ p ^ TwistTag.E6.tag.rank := GGExcToralRankInput.card_le hT hV hE
    _ = p ^ 6 := rfl

end TwE6Rank

theorem ggTwE6RankSixInput_holds :
    GGTwE6RankSixInput := by
  intro K _ _ n p hn hK hp hpn hp3 A hA
  exact TwE6Rank.card_le_of_isElemAbelian hn hK hp (TableBU.ne_two_of_dvd_two_pow_add_one hn hpn)
    hp3 hpn hA

theorem ggTwE6BstarInput_of_dvd
    (hD : GGTwE6BstarDvdInput) :
    GGTwE6BstarInput :=
  ggTwE6BstarInput_of_rank ggTwE6RankSixInput_holds hD

end CFSG.StandardType
