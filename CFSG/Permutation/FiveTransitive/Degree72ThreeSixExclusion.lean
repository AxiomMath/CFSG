module

public import CFSG.Permutation.FiveTransitive.Degree72ThreeFivePower
public import CFSG.Permutation.FiveTransitive.ThreeGroupOrbitFiveFixed

public section

namespace CFSG

namespace FiveTransitive.Degree72ThreeSixExclusion

open MulAction SylowFixedActionCore

theorem fixed_ne_six
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 72)
    (h5 : IsMultiplyPretransitive P X 5)
    (hnotAlt : ¬ alternatingGroup X ≤ P)
    (s : Set X) (hs : s.ncard = 5) (S : Sylow 3 (fixingSubgroup P s)) :
    Nat.card (sylowFixedPoints X P s S) ≠ 6 := by
  classical
  intro hF
  let _ : Fact (Nat.Prime 3) := ⟨by decide⟩
  let _ : Fact (Nat.Prime 5) := ⟨by decide⟩
  let Q := sylowImage X P s S
  let N := sylowNormalizer X P s S
  let F := sylowFixedPoints X P s S
  let _ : Fintype F := Fintype.ofFinite F
  let rho : N →* Equiv.Perm F := toPermHom N F
  have hQ : IsPGroup 3 Q := S.isPGroup'.map (fixingSubgroup P s).subtype
  have hfixeq : (F : Set X) = fixedPoints Q X := FixedNormalizerAction.fixed_eq Q
  have hFfin : Fintype.card F = 6 := by rwa [← Nat.card_eq_fintype_card]
  have hexp : ∀ a b : Fin 5 → X, Function.Injective a → Function.Injective b →
      ∃ g : P, ∀ i, g • a i = b i := by
    intro a b ha hb
    obtain ⟨g,hg⟩ := h5.exists_smul_eq (⟨a,ha⟩ : Fin 5 ↪ X) ⟨b,hb⟩
    exact ⟨g,fun i => DFunLike.congr_fun hg i⟩
  have hN5 := sylowNormalizer_five_transitive_on_fixedPoints X P hexp s hs S
  have hAlt : alternatingGroup F ≤ rho.range := by
    apply SmallDegreeFixedAction.alternatingGroup_le_of_card_le_twentySeven_away_mathieu F rho.range
    · rw [hFfin]; norm_num
    · rw [hFfin]; norm_num
    · rw [hFfin]; norm_num
    · rw [hFfin]; norm_num
    · intro a b ha hb
      obtain ⟨g,hg⟩ := hN5 a b ha hb
      exact ⟨⟨rho g,⟨g,rfl⟩⟩,hg⟩
  have hdiv : 5 ∣ Nat.card N :=
    ((odd_prime_dvd_alternating_card F (by decide : Nat.Prime 5) (by norm_num)
      (by rw [hFfin]; norm_num)).trans (Subgroup.card_dvd_of_le hAlt)).trans
        (Subgroup.card_range_dvd rho)
  let T : Sylow 5 N := Sylow.nonempty.some
  have hdivI : 5 ∣ Nat.card rho.range :=
    (odd_prime_dvd_alternating_card F (by decide : Nat.Prime 5) (by decide)
      (by rw [hFfin]; decide)).trans (Subgroup.card_dvd_of_le hAlt)
  have hex : ∃ z : N, z ∈ (T : Subgroup N) ∧ rho z ≠ 1 := by
    by_contra hn
    push Not at hn
    exact prime_not_dvd_range_card_of_sylow_le_ker T rho (fun z hz => hn z hz) hdivI
  obtain ⟨z,hzT,hzne⟩ := hex
  obtain ⟨e,he⟩ := IsPGroup.iff_orderOf.mp T.isPGroup' (⟨z,hzT⟩ : T)
  have hzo : orderOf z.val = 5 ^ e := (Subgroup.orderOf_coe z).trans
    ((Subgroup.orderOf_coe (⟨z,hzT⟩ : T)).trans he)
  have hzpow : z ^ 5 = 1 := Subtype.ext
    (Degree72ThreeFivePower.pow_five_eq_one P hcard h5 hnotAlt z.val ⟨e,hzo⟩)
  have hz : orderOf z = 5 := orderOf_eq_prime hzpow (fun hh => hzne (by rw [hh,map_one]))
  have hzlocal : orderOf (rho z) = 5 := orderOf_eq_prime
    (by rw [← map_pow,hzpow,map_one]) hzne
  have hg := Degree72FiveActual.fixed_card_cases P hcard h5 hnotAlt z.val ((Subgroup.orderOf_coe z).trans hz)
  have hl : Nat.card (Function.fixedPoints (rho z)) = 1 := by
    obtain ⟨u,hu⟩ := Equiv.Perm.cycleType_prime_order (σ := rho z) (by rw [hzlocal]; decide)
    have hsum := (rho z).sum_cycleType
    rw [hu,Multiset.sum_replicate,nsmul_eq_mul,Nat.cast_id,hzlocal] at hsum
    have hb := Finset.card_le_univ (rho z).support
    rw [hFfin] at hb
    rw [Nat.card_eq_fintype_card,Equiv.Perm.card_fixedPoints,(rho z).sum_cycleType,hFfin]
    omega
  let E : {x : fixedPoints Q X // z.val.val x.val = x.val} ≃ Function.fixedPoints (rho z) :=
    { toFun := fun x => ⟨⟨x.val.val,by rw [hfixeq]; exact x.val.property⟩,Subtype.ext x.property⟩
      invFun := fun x => ⟨⟨x.val.val,by rw [← hfixeq]; exact x.val.property⟩,congrArg Subtype.val x.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have hsmall (x : X) : Nat.card (orbit Q x) < 81 := by
    have hh := Nat.card_le_card_of_injective (fun y : orbit Q x => y.val) Subtype.val_injective
    rw [Nat.card_eq_fintype_card (α := X),hcard] at hh
    omega
  have hc := ThreeGroupOrbitFiveFixed.fixed_congruence Q hQ hsmall z.val z.property
    (congrArg Subtype.val hzpow)
  change Nat.card (Function.fixedPoints z.val.val) ≡
    Nat.card {x : fixedPoints Q X // z.val.val x.val = x.val} [MOD 3] at hc
  rw [Nat.card_congr E] at hc
  change Nat.card (Function.fixedPoints z.val.val) % 3 =
    Nat.card (Function.fixedPoints (rho z)) % 3 at hc
  let i : Function.fixedPoints (rho z) → Function.fixedPoints z.val.val :=
    fun x => ⟨x.val.val,congrArg Subtype.val x.property⟩
  have hi : Function.Injective i := by
    intro a b hab
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun y : Function.fixedPoints z.val.val => y.val) hab
  have hle := Nat.card_le_card_of_injective i hi
  omega

end FiveTransitive.Degree72ThreeSixExclusion

end CFSG
