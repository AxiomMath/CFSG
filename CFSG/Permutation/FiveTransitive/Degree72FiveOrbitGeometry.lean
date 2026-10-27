module

public import CFSG.Permutation.FiveTransitive.Degree72FiveImage
public import CFSG.Permutation.FiveTransitive.Degree72FiveElevenFixed
public import CFSG.Permutation.FiveTransitive.NormalizerOrbitFamily

public section

namespace CFSG

namespace FiveTransitive.Degree72FiveOrbitGeometry

open MulAction SylowFixedActionCore

theorem exists_eleven
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 72)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (s : Set X) (hs : s.ncard = 5) (S : Sylow 5 (fixingSubgroup P s)) (hF12 : Nat.card (sylowFixedPoints X P s S) = 12) :
    ∃ g : sylowNormalizer X P s S, orderOf g = 11 := by
  classical
  let _ : Fact (Nat.Prime 11) := ⟨by decide⟩
  let N := sylowNormalizer X P s S
  let F := sylowFixedPoints X P s S
  let _ : Fintype F := Fintype.ofFinite F
  let rho := toPermHom N F
  have hI := Degree72FiveImage.card_eq_95040 P hcard h5 hnotAlt s hs S hF12
  have hd : 11 ∣ Nat.card rho.range := by
    change 11 ∣ Nat.card (toPermHom (sylowNormalizer X P s S) (sylowFixedPoints X P s S)).range
    rw [hI]
    norm_num
  exact exists_prime_orderOf_dvd_card' (G := N) 11 (hd.trans (Subgroup.card_range_dvd rho))

theorem exterior_orbit_card_five
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 72)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (s : Set X) (hs : s.ncard = 5) (S : Sylow 5 (fixingSubgroup P s)) (hF12 : Nat.card (sylowFixedPoints X P s S) = 12) :
    ∀ x : X, x ∉ fixedPoints (sylowImage X P s S) X →
      Nat.card (orbit (sylowImage X P s S) x) = 5 := by
  classical
  let _ : Fact (Nat.Prime 5) := ⟨by decide⟩
  let _ : Fact (Nat.Prime 11) := ⟨by decide⟩
  let Q := sylowImage X P s S
  have hQ : IsPGroup 5 Q := S.isPGroup'.map (fixingSubgroup P s).subtype
  obtain ⟨g,hg⟩ := exists_eleven P hcard h5 hnotAlt s hs S hF12
  let B := NormalizerOrbitFamily.Family (X := X) Q 25
  let sigma := NormalizerOrbitFamily.toPermHom (X := X) Q 25
  have hB : Nat.card B ≤ 2 := by
    have hb := NormalizerOrbitFamily.card_mul_le (X := X) Q 25
    rw [Nat.card_eq_fintype_card (α := X),hcard] at hb
    change Nat.card B * 25 ≤ 72 at hb
    omega
  have hsigma : sigma g = 1 := by
    have hpow : sigma g ^ 11 = 1 := by rw [← map_pow,← hg,pow_orderOf_eq_one,map_one]
    by_contra hn
    have ho : orderOf (sigma g) = 11 := orderOf_eq_prime hpow hn
    have hd : 11 ∣ (Nat.card B).factorial := by
      have hd := orderOf_dvd_natCard (sigma g)
      rwa [ho,Nat.card_perm] at hd
    have hbad := hd.trans (Nat.factorial_dvd_factorial hB)
    norm_num [Nat.factorial] at hbad
  intro x hx
  change Nat.card (orbit Q x) = 5
  obtain ⟨e,he⟩ := hQ.card_orbit x
  have hb := Nat.card_le_card_of_injective (fun y : orbit Q x => y.val) Subtype.val_injective
  rw [Nat.card_eq_fintype_card (α := X),hcard,he] at hb
  have he2 : e ≤ 2 := by
    by_contra hn
    have hh := Nat.pow_le_pow_right (by decide : 0 < 5) (by omega : 3 ≤ e)
    norm_num at hh
    omega
  have hn1 : Nat.card (orbit Q x) ≠ 1 := by
    intro h
    exact hx (mem_fixedPoints_iff_card_orbit_eq_one.mpr (by rwa [← Nat.card_eq_fintype_card]))
  have hn25 : Nat.card (orbit Q x) ≠ 25 := by
    intro h25
    let O : B := ⟨Quotient.mk'' x,by rwa [orbitRel.Quotient.orbit_mk]⟩
    have hpres := congrArg Subtype.val (congrArg (fun a : Equiv.Perm B => a O) hsigma)
    have hgx : g.val • x ∈ orbit Q x := Quotient.exact hpres
    have hsub : orbit Q x ⊆ fixedBy X g.val := fun y hy =>
      Degree67FiveOrbitElevenFixed.fixes_preserved_orbit Q hQ g.val g.property
        (congrArg Subtype.val (hg ▸ pow_orderOf_eq_one g)) x (by omega) hgx y hy
    have hle := Set.ncard_le_ncard hsub
    rw [← Nat.card_coe_set_eq,← Nat.card_coe_set_eq,h25] at hle
    have hF : Nat.card (fixedPoints Q X) = 12 := by
      rw [← FixedNormalizerAction.fixed_eq Q]
      exact hF12
    have hfixed := Degree72FiveElevenFixed.fixed_le_seventeen P hcard h5 hnotAlt Q hQ hF g hg
    change Nat.card (fixedBy X g.val) ≤ 17 at hfixed
    omega
  rw [he] at hn1 hn25 ⊢
  interval_cases e <;> norm_num at *

end FiveTransitive.Degree72FiveOrbitGeometry

end CFSG
