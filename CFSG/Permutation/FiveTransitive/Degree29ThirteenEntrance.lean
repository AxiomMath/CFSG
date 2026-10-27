module

public import CFSG.Permutation.FiveTransitive.Degree29ThirteenSubgroup
public import CFSG.Permutation.FiveTransitive.Degree29ThirteenCentralizerExclusion
public import CFSG.Permutation.FiveTransitive.GenericSylowFixedAction

public section

namespace CFSG

namespace FiveTransitive.Degree29ThirteenEntrance

open MulAction Subgroup FixedNormalizerAction

private theorem sylow_fixed_image
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 29)
    (h5 : IsMultiplyPretransitive P X 5)
    (S : Sylow 13 P) (hfixed : Nat.card (fixedPoints S X) = 3) :
    Image (X := X) (S : Subgroup P) = ⊤ := by
  classical
  let _ : Fact (Nat.Prime 13) := ⟨by norm_num⟩
  let s : Set X := fixedPoints S X
  have hs : s.ncard = 3 := by rw [← Nat.card_coe_set_eq]; exact hfixed
  have hle : (S : Subgroup P) ≤ fixingSubgroup P s := by
    intro q hq
    apply (mem_fixingSubgroup_iff P).mpr
    intro x hx
    exact hx (⟨q,hq⟩ : S)
  let T : Sylow 13 (fixingSubgroup P s) := S.subtype hle
  have himage : GenericSylowFixedAction.sylowImage P X s T = (S : Subgroup P) := by
    ext q
    change q ∈ ((S : Subgroup P).subgroupOf (fixingSubgroup P s)).map
      (fixingSubgroup P s).subtype ↔ q ∈ S
    constructor
    · rintro ⟨w,hw,rfl⟩
      exact hw
    · intro hq
      exact ⟨⟨q,hle hq⟩,hq,rfl⟩
  have h3 : IsMultiplyPretransitive P X 3 := by
    let _ := h5
    exact isMultiplyPretransitive_of_le (G := P) (α := X) (n := 5)
      (by norm_num) (by rw [Nat.card_eq_fintype_card,hcard]; norm_num)
  have hexp : ∀ a b : Fin 3 → X, Function.Injective a → Function.Injective b →
      ∃ g : P, ∀ i, g • a i = b i := by
    intro a b ha hb
    obtain ⟨g,hg⟩ := h3.exists_smul_eq (⟨a,ha⟩ : Fin 3 ↪ X) ⟨b,hb⟩
    exact ⟨g,fun i => DFunLike.congr_fun hg i⟩
  have hlocal := GenericSylowFixedAction.sylowNormalizer_transitive_on_fixedPoints
    P X 3 hexp s hs T
  change ∀ a b : Fin 3 → Fixed (X := X) (GenericSylowFixedAction.sylowImage P X s T),
    Function.Injective a → Function.Injective b →
    ∃ g : Normalizer (GenericSylowFixedAction.sylowImage P X s T), ∀ i, g • a i = b i at hlocal
  rw [himage] at hlocal
  let F := Fixed (X := X) (S : Subgroup P)
  let J := Image (X := X) (S : Subgroup P)
  have hF : Nat.card F = 3 := by
    change Nat.card (Fixed (X := X) (S : Subgroup P)) = 3
    rw [fixed_eq]
    exact hfixed
  have hJ3 : IsMultiplyPretransitive J F 3 := by
    rw [isMultiplyPretransitive_iff]
    intro a b
    obtain ⟨g,hg⟩ := hlocal a b a.injective b.injective
    refine ⟨⟨toPermHom (Normalizer (S : Subgroup P)) F g,⟨g,rfl⟩⟩,?_⟩
    apply Function.Embedding.ext
    intro i
    exact hg i
  apply Equiv.Perm.eq_top_of_isMultiplyPretransitive
  change IsMultiplyPretransitive J F (Nat.card F - 1)
  rw [hF]
  let _ := hJ3
  exact isMultiplyPretransitive_of_le (G := J) (α := F) (n := 3) (by norm_num) (by rw [hF])

private theorem exists_generator
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 29)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P) :
    ∃ r : P, orderOf r = 13 ∧ r.val.cycleType = {13,13} ∧
      Nat.card (Fixed (X := X) (zpowers r)) = 3 ∧ Image (X := X) (zpowers r) = ⊤ := by
  classical
  let _ : Fact (Nat.Prime 13) := ⟨by norm_num⟩
  have hd := FiveTransitive.descFactorial_dvd_card_of_isMultiplyPretransitive P X 5 (by omega) h5
  rw [hcard] at hd
  have h13 : 13 ∣ Nat.card P := (by norm_num [Nat.descFactorial] : 13 ∣ (29 : ℕ).descFactorial 5).trans hd
  obtain ⟨r,hr⟩ := exists_prime_orderOf_dvd_card' (G := P) 13 h13
  have hR : IsPGroup 13 (zpowers r) := by
    apply IsPGroup.of_card
    rw [Nat.card_zpowers,hr,pow_one]
  obtain ⟨S,hRS⟩ := hR.exists_le_sylow
  have hSne : (S : Subgroup P) ≠ ⊥ := by
    intro he
    have hrS := hRS (mem_zpowers r)
    rw [he,mem_bot] at hrS
    rw [hrS,orderOf_one] at hr
    norm_num at hr
  have hScard := Degree29ThirteenSubgroup.card_eq_thirteen P hcard h5 hnotAlt
    (S : Subgroup P) S.isPGroup' hSne
  have hSfixed := Degree29ThirteenSubgroup.fixed_card_eq_three P hcard h5 hnotAlt
    (S : Subgroup P) S.isPGroup' hSne
  have heq : zpowers r = (S : Subgroup P) := Subgroup.eq_of_le_of_card_ge hRS (by
    rw [Nat.card_zpowers,hr,hScard])
  refine ⟨r,hr,Degree29ThirteenSubgroup.order_thirteen_cycle_type P hcard h5 hnotAlt r hr,?_,?_⟩
  · rw [heq,fixed_eq]
    exact hSfixed
  · rw [heq]
    exact sylow_fixed_image P hcard h5 S hSfixed

theorem excluded
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 29)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P) : False := by
  obtain ⟨r,_,htype,hfixed,himage⟩ := exists_generator P hcard h5 hnotAlt
  exact Degree29ThirteenCentralizerExclusion.excluded P hcard h5 hnotAlt r htype hfixed himage

end FiveTransitive.Degree29ThirteenEntrance

end CFSG
