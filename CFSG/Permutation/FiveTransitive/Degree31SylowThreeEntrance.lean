module

public import CFSG.Permutation.FiveTransitive.Degree31SylowThreeFixed
public import CFSG.Permutation.FiveTransitive.Degree31ThreeGroupBound
public import CFSG.Permutation.FiveTransitive.Degree31SevenCentralizer
public import CFSG.Permutation.FiveTransitive.ThreeGroupSmallSevenAut

public section

namespace CFSG

namespace FiveTransitive.Degree31SylowThreeEntrance

open MulAction SylowFixedActionCore

theorem card_eq_three
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 31)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (s : Set X) (hs : s.ncard = 5)
    (S : Sylow 3 (fixingSubgroup P s)) (hS : Nat.card S ≠ 1) : Nat.card S = 3 := by
  classical
  let _ : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  let _ : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  let Q := sylowImage X P s S
  let N := sylowNormalizer X P s S
  let F := sylowFixedPoints X P s S
  let _ : Fintype F := Fintype.ofFinite F
  let rho : N →* Equiv.Perm F := toPermHom N F
  have hQcard : Nat.card Q = Nat.card S := Nat.card_congr
    ((S : Subgroup (fixingSubgroup P s)).equivMapOfInjective
      (fixingSubgroup P s).subtype Subtype.val_injective).toEquiv.symm
  have hQ : IsPGroup 3 Q := S.isPGroup'.map (fixingSubgroup P s).subtype
  have hfixeq : (F : Set X) = fixedPoints Q X := by
    ext x
    constructor
    · intro hx q
      exact hx (⟨⟨q.val,Q.le_normalizer q.property⟩,q.property⟩ : sylowInNormalizer X P s S)
    · intro hx q
      exact hx (⟨q.val.val,q.property⟩ : Q)
  have hF : Nat.card F = 7 := Degree31SylowThreeFixed.fixed_card_eq_seven P hcard h5 hnotAlt s hs S hS
  have hFfin : Fintype.card F = 7 := by rwa [Nat.card_eq_fintype_card] at hF
  have hQ81 : Nat.card Q ≤ 81 := Degree31ThreeGroupBound.card_le_eighty_one
    P hcard h5 hnotAlt Q hQ (by rw [← hfixeq,hF]; norm_num)
  have hexp : ∀ a b : Fin 5 → X, Function.Injective a → Function.Injective b →
      ∃ g : P, ∀ i, g • a i = b i := by
    intro a b ha hb
    obtain ⟨g,hg⟩ := h5.exists_smul_eq (⟨a,ha⟩ : Fin 5 ↪ X) ⟨b,hb⟩
    exact ⟨g,fun i => DFunLike.congr_fun hg i⟩
  have hN5 := sylowNormalizer_five_transitive_on_fixedPoints X P hexp s hs S
  have hAlt : alternatingGroup F ≤ rho.range := by
    apply SmallDegreeFixedAction.alternatingGroup_le_of_card_le_twentySeven_away_mathieu F rho.range
    · omega
    · omega
    · omega
    · omega
    · intro a b ha hb
      obtain ⟨g,hg⟩ := hN5 a b ha hb
      exact ⟨⟨rho g,⟨g,rfl⟩⟩,hg⟩
  have hseven : 7 ∣ Nat.card rho.range :=
    (odd_prime_dvd_alternating_card F (by norm_num : Nat.Prime 7) (by norm_num) (by omega)).trans
      (Subgroup.card_dvd_of_le hAlt)
  let T : Sylow 7 N := Sylow.nonempty.some
  have hex : ∃ z : N, z ∈ (T : Subgroup N) ∧ rho z ≠ 1 := by
    by_contra hn
    push Not at hn
    have hker : (T : Subgroup N) ≤ rho.ker := fun z hz => hn z hz
    exact prime_not_dvd_range_card_of_sylow_le_ker T rho hker hseven
  obtain ⟨z,hzT,hzrho⟩ := hex
  obtain ⟨e,he⟩ := IsPGroup.iff_orderOf.mp T.isPGroup' (⟨z,hzT⟩ : T)
  have hzpermorder : orderOf z.val.val = 7 ^ e := by
    rw [Subgroup.orderOf_coe z.val,Subgroup.orderOf_coe z]
    exact (Subgroup.orderOf_coe (⟨z,hzT⟩ : T)).trans he
  have hzperm7 : z.val.val ^ 7 = 1 :=
    Degree31SevenCentralizer.pow_seven_eq_one hcard z.val.val ⟨e,hzpermorder⟩
  have hz7 : z ^ 7 = 1 := Subtype.ext (Subtype.ext hzperm7)
  have hzP7 : orderOf z.val = 7 := orderOf_eq_prime (congrArg Subtype.val hz7) (by
    intro he
    have hz1 : z = 1 := Subtype.ext he
    exact hzrho (by rw [hz1,map_one]))
  have hauto : Q.normalizerMonoidHom z = 1 :=
    ThreeGroupSmallSevenAut.eq_one Q hQ hQ81 _ (by rw [← map_pow,hz7,map_one])
  have hcomm : ∀ q : Q, z.val * q.val = q.val * z.val := by
    intro q
    have he : z.val * q.val * z.val⁻¹ = q.val := congrArg Subtype.val (DFunLike.congr_fun hauto q)
    simpa only [mul_assoc,inv_mul_cancel,mul_one] using congrArg (fun p : P => p * z.val) he
  have hrho7 : orderOf (rho z) = 7 := orderOf_eq_prime (by rw [← map_pow,hz7,map_one]) hzrho
  have hnF : ∀ x : F, rho z x ≠ x := by
    have hp : Nat.Prime (orderOf (rho z)) := by rw [hrho7]; norm_num
    obtain ⟨m,hm⟩ := Equiv.Perm.cycleType_prime_order hp
    have hsum := (rho z).sum_cycleType
    rw [hm,Multiset.sum_replicate,nsmul_eq_mul,Nat.cast_id,hrho7] at hsum
    have hle := Finset.card_le_univ (rho z).support
    rw [hFfin] at hle
    have hsupp : (rho z).support.card = 7 := by omega
    have hzfixed : Fintype.card (Function.fixedPoints (rho z)) = 0 := by
      rw [Equiv.Perm.card_fixedPoints,(rho z).sum_cycleType,hFfin,hsupp]
    let _ : IsEmpty (Function.fixedPoints (rho z)) := Fintype.card_eq_zero_iff.mp hzfixed
    exact fun x hx => isEmptyElim (⟨x,hx⟩ : Function.fixedPoints (rho z))
  have hQ3 := Degree31SevenCentralizer.card_le_three P hcard h5 hnotAlt Q hQ z.val hzP7 hcomm
    (by
      intro x hx he
      have hxF : x ∈ (F : Set X) := hfixeq ▸ hx
      apply hnF ⟨x,hxF⟩
      exact Subtype.ext he)
  rw [hQcard] at hQ3
  obtain ⟨k,hk⟩ := IsPGroup.iff_card.mp S.isPGroup'
  have hk1 : k ≤ 1 := by
    by_contra hn
    have hh := Nat.pow_le_pow_right (by norm_num : 0 < 3) (by omega : 2 ≤ k)
    norm_num at hh
    omega
  interval_cases k
  · exact (hS (by simpa only [pow_zero] using hk)).elim
  · simpa only [pow_one] using hk

end FiveTransitive.Degree31SylowThreeEntrance

end CFSG
