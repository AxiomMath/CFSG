module

public import CFSG.LocalAnalysis.StandardType.GGNbrInnerWeylOpenLabels
public import CFSG.LocalAnalysis.StandardType.GGTableBTwE6Delta
public import CFSG.LocalAnalysis.StandardType.GGTableBTwE6Dvd
public import CFSG.LieType.SeitzGeneration.ExcHighThree.TwE6Two
public import CFSG.HardMathSupport.Lang.AnisoE6.FieldEmbed
public import CFSG.LocalAnalysis.StandardType.GGNbrInnerWeylClauseFive

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.SeitzGeneration.ExcHighThree

section Main

theorem exists_mulEquiv_recipeR_twistedE6RootGroup {K : Type} [Field K] [Finite K] {n : ℕ}
    (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 2) :
    ∃ σ : K ≃+* K, (∀ c, σ c = c ^ 2 ^ n) ∧
      Nonempty (TwE6Delta.RecipeR K n ≃* twistedE6RootGroup K σ) := by
  haveI : CharP K 2 := charP_two_of_card (m := n * 2) (by rw [hK, pow_mul])
  refine ⟨iterateFrobeniusEquiv K 2 n, ?_, ?_⟩
  · intro c
    rw [iterateFrobeniusEquiv_apply, iterateFrobenius_def]
  · set σ := iterateFrobeniusEquiv K 2 n with hσdef
    have hσ : ∀ c, σ.toRingHom c = c ^ 2 ^ n := fun c => by
      rw [RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, hσdef,
        iterateFrobeniusEquiv_apply, iterateFrobenius_def]
    obtain ⟨-, T, -, -⟩ := InnerDiagTwE6.exists_twistedTransport (K := K) n σ.toRingHom hσ
    have hZH := TwE6Delta.center_recipeH_eq_bot hn hK
    have hΓ := (finite_fixed_root_group_perfect TwistTag.E6 Nat.prime_two hn K hK
      σ.toRingHom hσ).2.2.1
    let e₁ : TwE6Delta.RecipeR K n ≃* TwE6Delta.RecipeH K n :=
      (QuotientGroup.quotientMulEquivOfEq hZH).trans QuotientGroup.quotientBot
    let e : TwE6Delta.RecipeR K n ≃* twistedE6RootGroup K σ :=
      (e₁.trans T.symm).trans (MulEquiv.subgroupCongr hΓ)
    exact ⟨e⟩

theorem exists_injective_f4_recipeR {K : Type} [Field K] [Finite K] {n : ℕ} (hn : 1 ≤ n)
    (hK : Nat.card K = (2 ^ n) ^ 2) :
    ∃ (k : Type) (_ : Field k) (_ : Finite k) (_ : CharP k 2)
      (ι : adjointGroup .F4 k →* TwE6Delta.RecipeR K n),
      Nat.card k = 2 ^ n ∧ Function.Injective ι := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI hK2 : CharP K 2 := charP_two_of_card (m := n * 2) (by rw [hK, pow_mul])
  obtain ⟨σ, hσ, ⟨e⟩⟩ := exists_mulEquiv_recipeR_twistedE6RootGroup (K := K) hn hK
  have hkcard : Nat.card (GaloisField 2 n) = 2 ^ n := GaloisField.card 2 n (by omega)
  obtain ⟨φ⟩ := CFSG.HardMathSupport.Lang.AnisoE6.nonempty_ringHom_of_card_sq
    (ℓ := 2) (f := n) (k := GaloisField 2 n) (K := K) hkcard hK
  letI : Algebra (GaloisField 2 n) K := φ.toAlgebra
  have hpow : ∀ c : GaloisField 2 n, c ^ 2 ^ n = c := by
    intro c
    letI : Fintype (GaloisField 2 n) := Fintype.ofFinite _
    have hq : Fintype.card (GaloisField 2 n) = 2 ^ n := by
      rw [← Nat.card_eq_fintype_card]; exact hkcard
    rw [← hq]
    exact FiniteField.pow_card c
  have hfix : ∀ c : GaloisField 2 n,
      σ (algebraMap (GaloisField 2 n) K c) = algebraMap (GaloisField 2 n) K c := by
    intro c
    have h1 : (algebraMap (GaloisField 2 n) K c) ^ 2 ^ n =
        algebraMap (GaloisField 2 n) K c := by
      rw [← map_pow, hpow c]
    rw [hσ (algebraMap (GaloisField 2 n) K c), h1]
  have hiota : Function.Injective (TwE6Two.iota σ hfix) := by
    intro g g' h
    have h1 : baseChangeGL (algebraMap (GaloisField 2 n) K)
        ((embE6F4 (GaloisField 2 n) g : adjointGroup .E6 (GaloisField 2 n)) :
          ModGL Tag.E6 (GaloisField 2 n)) =
        baseChangeGL (algebraMap (GaloisField 2 n) K)
        ((embE6F4 (GaloisField 2 n) g' : adjointGroup .E6 (GaloisField 2 n)) :
          ModGL Tag.E6 (GaloisField 2 n)) := by
      have hc := congrArg
        (fun x : twistedE6RootGroup K σ => (x : ModGL TwistTag.E6.tag K)) h
      rwa [TwE6Two.coe_iota σ hfix g, TwE6Two.coe_iota σ hfix g'] at hc
    have h2 : ((embE6F4 (GaloisField 2 n) g : adjointGroup .E6 (GaloisField 2 n)) :
          ModGL Tag.E6 (GaloisField 2 n)) =
        ((embE6F4 (GaloisField 2 n) g' : adjointGroup .E6 (GaloisField 2 n)) :
          ModGL Tag.E6 (GaloisField 2 n)) :=
      baseChangeGL_injective (algebraMap (GaloisField 2 n) K) h1
    have hemb : Function.Injective (embE6F4 (GaloisField 2 n)) :=
      Subtype.val_injective.comp (isoE6F4 (GaloisField 2 n)).injective
    exact hemb (Subtype.val_injective h2)
  let ι : adjointGroup .F4 (GaloisField 2 n) →* TwE6Delta.RecipeR K n :=
    e.symm.toMonoidHom.comp (TwE6Two.iota σ hfix)
  have hinj : Function.Injective ι := fun g g' h => hiota (e.symm.injective h)
  exact ⟨GaloisField 2 n, inferInstance, inferInstance, inferInstance, ι, hkcard, hinj⟩

end Main

end CFSG.StandardType

end
