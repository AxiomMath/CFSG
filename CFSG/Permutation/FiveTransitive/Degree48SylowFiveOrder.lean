module

public import CFSG.Permutation.FiveTransitive.Degree48FiveSylowData
public import CFSG.Permutation.FiveTransitive.Degree48FiveGroupBound
public import CFSG.Permutation.FiveTransitive.Degree48FiveCentralizer
public import CFSG.Permutation.FiveTransitive.FiveGroup3125SevenAutomorphism
public import CFSG.Permutation.FiveTransitive.FixedNormalizerAction

public section

namespace CFSG

namespace FiveTransitive.Degree48SylowFiveOrder

open MulAction Subgroup SylowFixedActionCore

private theorem sylow_card
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 48)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (s : Set X) (hs : s.ncard = 5)
    (S : Sylow 5 (fixingSubgroup P s)) (hS : Nat.card S ≠ 1) : Nat.card S = 5 := by
  classical
  let _ : Fact (Nat.Prime 5) := ⟨by decide⟩
  let _ : Fact (Nat.Prime 7) := ⟨by decide⟩
  let Q := sylowImage X P s S
  let N := sylowNormalizer X P s S
  let F := sylowFixedPoints X P s S
  let _ : Fintype F := Fintype.ofFinite _
  obtain ⟨hF,hAlt⟩ := Degree48FiveSylowData.five_fixed_card_and_image P hcard h5 hnotAlt s hs S hS
  change Nat.card F = 8 at hF
  have hQ : IsPGroup 5 Q := S.isPGroup'.map (fixingSubgroup P s).subtype
  have hfixeq : (F : Set X) = fixedPoints Q X := FixedNormalizerAction.fixed_eq Q
  have hfixed : Nat.card (fixedPoints Q X) = 8 := by rwa [← hfixeq]
  have hQcard := Degree48FiveGroupBound.card_le_three_thousand_one_hundred_twenty_five P hcard h5 hnotAlt Q hQ hfixed.ge
  let rho : N →* Equiv.Perm F := toPermHom N F
  have hd : 7 ∣ Nat.card rho.range :=
    (odd_prime_dvd_alternating_card F (by decide : Nat.Prime 7) (by decide)
      (by rw [← Nat.card_eq_fintype_card,hF]; decide)).trans (Subgroup.card_dvd_of_le hAlt)
  obtain ⟨g,hg⟩ := exists_prime_orderOf_dvd_card' (G := N) 7
    (hd.trans (Subgroup.card_range_dvd rho))
  have haut : Q.normalizerMonoidHom g = 1 :=
    FiveGroup3125SevenAutomorphism.eq_one hQ hQcard _
      (by rw [← map_pow,← hg,pow_orderOf_eq_one,map_one])
  have hcomm : ∀ q : Q, g.val * q.val = q.val * g.val := by
    intro q
    have hh : g.val * q.val * g.val⁻¹ = q.val :=
      congrArg Subtype.val (DFunLike.congr_fun haut q)
    simpa only [mul_assoc,inv_mul_cancel,mul_one] using
      congrArg (fun a : P => a * g.val) hh
  have hle := Degree48FiveCentralizer.card_le_five P hcard h5 hnotAlt Q hQ
    g.val ((Subgroup.orderOf_coe g).trans hg) hcomm
  have heq : Nat.card Q = Nat.card S := Subgroup.card_map_of_injective (fixingSubgroup P s).subtype_injective
  rw [heq] at hle
  obtain ⟨e,he⟩ := IsPGroup.iff_card.mp S.isPGroup'
  have hepos : 1 ≤ e := by
    by_contra hn
    exact hS (by rw [he,show e=0 by omega,pow_zero])
  have hge : 5 ≤ Nat.card S := by rw [he]; exact Nat.pow_le_pow_right (by decide : 0 < 5) hepos
  omega

private theorem fixed_card_eq_eight
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 48)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (g : P) (hg : orderOf g = 5) (hfixed : 5 ≤ Nat.card (Function.fixedPoints g.val)) :
    Nat.card (Function.fixedPoints g.val) = 8 := by
  classical
  let _ : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  let b : Fin 5 ↪ Function.fixedPoints g.val :=
    (Fin.castLEEmb hfixed).trans (Finite.equivFin (Function.fixedPoints g.val)).symm.toEmbedding
  let bX : Fin 5 ↪ X := b.trans (Function.Embedding.subtype _)
  let s : Set X := Set.range bX
  have hs : s.ncard = 5 := by
    simpa only [Nat.card_fin] using Set.ncard_range_of_injective bX.injective
  let H := fixingSubgroup P s
  have hgmem : g ∈ H := by
    apply (mem_fixingSubgroup_iff P).mpr
    rintro x ⟨i,rfl⟩
    exact (b i).property
  let u : H := ⟨g,hgmem⟩
  have hu : orderOf u = 5 := (Subgroup.orderOf_coe u).symm.trans hg
  have hZ : IsPGroup 5 (zpowers u) := by
    apply IsPGroup.of_card (n := 1)
    rw [Nat.card_zpowers,hu,pow_one]
  obtain ⟨S,hZS⟩ := hZ.exists_le_sylow
  have hSge : 5 ≤ Nat.card S := by
    have h := Subgroup.card_le_of_le hZS
    rwa [Nat.card_zpowers,hu] at h
  have hSne : Nat.card S ≠ 1 := by omega
  have hSfive : Nat.card S = 5 := sylow_card P hcard h5 hnotAlt s hs S hSne
  let Q := sylowImage X P s S
  have hQcard : Nat.card Q = 5 := by
    have hmap : Nat.card Q = Nat.card S := Subgroup.card_map_of_injective H.subtype_injective
    exact hmap.trans hSfive
  have hRQ : zpowers g = Q := by
    apply Subgroup.eq_of_le_of_card_ge
    · apply zpowers_le.mpr
      exact ⟨u,hZS (mem_zpowers u),rfl⟩
    · rw [Nat.card_zpowers,hg,hQcard]
  have hF := (Degree48FiveSylowData.five_fixed_card_and_image P hcard h5 hnotAlt s hs S hSne).1
  have hfixeq : (sylowFixedPoints X P s S : Set X) = fixedPoints Q X :=
    FixedNormalizerAction.fixed_eq Q
  rw [hfixeq] at hF
  have hcyclic : Function.fixedPoints g.val = fixedPoints (zpowers g) X := by
    ext x
    constructor
    · intro hx z
      have hz : zpowers g ≤ stabilizer P x := zpowers_le.mpr hx
      exact hz z.property
    · intro hx
      exact hx ⟨g,mem_zpowers g⟩
  rw [hcyclic,hRQ]
  exact hF

theorem twenty_five_not_dvd_five_fixer_card
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 48)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (s : Set X) (hs : s.ncard = 5) : ¬ 25 ∣ Nat.card (fixingSubgroup P s) := by
  let _ : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  intro hd
  let S : Sylow 5 (fixingSubgroup P s) := Sylow.nonempty.some
  have h25 : 25 ∣ Nat.card S := S.pow_dvd_card_of_pow_dvd_card (n := 2) hd
  by_cases hS : Nat.card S = 1
  · rw [hS] at h25
    norm_num at h25
  · rw [sylow_card P hcard h5 hnotAlt s hs S hS] at h25
    norm_num at h25

theorem fixed_card_three_or_eight
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 48)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (g : P) (hg : orderOf g = 5) :
    Nat.card (Function.fixedPoints g.val) = 3 ∨ Nat.card (Function.fixedPoints g.val) = 8 := by
  classical
  by_cases hfixed : 5 ≤ Nat.card (Function.fixedPoints g.val)
  · exact Or.inr (fixed_card_eq_eight P hcard h5 hnotAlt g hg hfixed)
  · let _ : Fact (Nat.Prime 5) := ⟨by decide⟩
    let f : Function.End X := g.val.toFun
    have hf : f ^ 5 = 1 := by
      funext x
      change (g ^ 5).val x = x
      rw [← hg,pow_orderOf_eq_one]
      rfl
    have hm := Equiv.Perm.card_fixedPoints_modEq (f := f) (p := 5) (n := 1)
      (by simpa only [pow_one] using hf)
    change Fintype.card X % 5 = Fintype.card (Function.fixedPoints g.val) % 5 at hm
    rw [hcard,← Nat.card_eq_fintype_card] at hm
    exact Or.inl (by omega)

end FiveTransitive.Degree48SylowFiveOrder

end CFSG
