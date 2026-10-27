module

public import CFSG.Permutation.FiveTransitive.Degree31MaximalPairFixer
public import CFSG.Permutation.FiveTransitive.Degree31Order4096FixedFive

public section

namespace CFSG

namespace FiveTransitive.Degree31BlockPairs

open MulAction

theorem block_data
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 31)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (s : Set X) (hs : s.ncard = 5) (hH : Nat.card (fixingSubgroup P s) = 4096)
    (b : Set X) (hb : b.ncard = 7) (hsb : s ⊆ b)
    (hK : Nat.card (fixingSubgroup P b) = 2048) :
    (b \ s).ncard = 2 ∧ Disjoint (b \ s) s ∧
      ∀ (h : fixingSubgroup P s) (x : X), x ∈ b \ s → h • x ∈ b \ s := by
  let H := fixingSubgroup P s
  let K := fixingSubgroup P b
  have hKH : K ≤ H := by
    intro k hk
    exact (mem_fixingSubgroup_iff P).mpr (fun x hx =>
      (mem_fixingSubgroup_iff P).mp hk x (hsb hx))
  have hbf : b ⊆ fixedPoints K X := by
    intro x hx k
    exact (mem_fixingSubgroup_iff P).mp k.property x hx
  have hKtwo : IsPGroup 2 K := IsPGroup.iff_card.mpr ⟨11,by change Nat.card (fixingSubgroup P b) = _; rw [hK]; norm_num⟩
  have hfix := (Degree31MaximalPairFixer.fixed_seven_image_top
    P hcard h5 hnotAlt s hs hH K hKtwo hK (by
      rw [Nat.card_coe_set_eq]
      have := Set.ncard_le_ncard hbf
      omega)).1
  have heq : fixedPoints K X = b := (Set.eq_of_subset_of_ncard_le hbf (by
    rw [← Nat.card_coe_set_eq,hfix,hb])).symm
  have hsubcard : Nat.card (K.subgroupOf H) = 2048 :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKH).toEquiv).trans hK
  have hindex : (K.subgroupOf H).index = 2 := by
    have hm := (K.subgroupOf H).index_mul_card
    rw [hsubcard] at hm
    change _ = Nat.card (fixingSubgroup P s) at hm
    rw [hH] at hm
    omega
  let _ : (K.subgroupOf H).Normal := Subgroup.normal_of_index_eq_two hindex
  have hn : H ≤ Subgroup.normalizer (K : Set P) :=
    Subgroup.le_normalizer_of_normal_subgroupOf hKH
  refine ⟨by rw [Set.ncard_sdiff hsb,hb,hs],Set.disjoint_sdiff_left,?_⟩
  intro h x hx
  refine ⟨?_,?_⟩
  · rw [← heq]
    exact FixedSetNormalizerPerm.smul_mem_fixedPoints P X K h.val (hn h.property)
      (heq.symm ▸ hx.1)
  · intro hxs
    have hf := (mem_fixingSubgroup_iff P).mp h⁻¹.property (h • x) hxs
    have hx' : x = h • x := by
      change (h : P)⁻¹ • ((h : P) • x) = h • x at hf
      simpa only [inv_smul_smul] using hf
    exact hx.2 (hx' ▸ hxs)

private theorem orbit_eq_pair
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 31)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (s : Set X) (hs : s.ncard = 5) (hH : Nat.card (fixingSubgroup P s) = 4096)
    (c : Set X) (hc : c.ncard = 2) (hcs : Disjoint c s)
    (hinv : ∀ (h : fixingSubgroup P s) (x : X), x ∈ c → h • x ∈ c)
    (x : X) (hx : x ∈ c) : orbit (fixingSubgroup P s) x = c := by
  have hsub : orbit (fixingSubgroup P s) x ⊆ c := by
    rintro y ⟨h,rfl⟩
    exact hinv h x hx
  have hxnot : x ∉ s := fun hh => Set.disjoint_left.mp hcs hx hh
  have hcases := Degree31Order4096FixedFive.orbit_card_cases P hcard h5 hnotAlt s hs hH x hxnot
  have hle := Set.ncard_le_ncard hsub
  rw [← Nat.card_coe_set_eq] at hle
  have hsize : (orbit (fixingSubgroup P s) x).ncard = 2 := by
    rw [← Nat.card_coe_set_eq]
    omega
  exact Set.eq_of_subset_of_ncard_le hsub (by omega)

theorem disjoint_pairs
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 31)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (s : Set X) (hs : s.ncard = 5) (hH : Nat.card (fixingSubgroup P s) = 4096)
    (b d : Set X) (hb : b.ncard = 7) (hd : d.ncard = 7) (hsb : s ⊆ b) (hsd : s ⊆ d)
    (hKb : Nat.card (fixingSubgroup P b) = 2048)
    (hKd : Nat.card (fixingSubgroup P d) = 2048) (hne : b ≠ d) :
    Disjoint (b \ s) (d \ s) := by
  obtain ⟨hb2,hbs,hbi⟩ := block_data P hcard h5 hnotAlt s hs hH b hb hsb hKb
  obtain ⟨hd2,hds,hdi⟩ := block_data P hcard h5 hnotAlt s hs hH d hd hsd hKd
  apply Set.disjoint_left.mpr
  intro x hxb hxd
  have he := (orbit_eq_pair P hcard h5 hnotAlt s hs hH _ hb2 hbs hbi x hxb).symm.trans
    (orbit_eq_pair P hcard h5 hnotAlt s hs hH _ hd2 hds hdi x hxd)
  apply hne
  apply Set.Subset.antisymm
  · intro y hy
    by_cases hys : y ∈ s
    · exact hsd hys
    · exact (he ▸ (show y ∈ b \ s from ⟨hy,hys⟩)).1
  · intro y hy
    by_cases hys : y ∈ s
    · exact hsb hys
    · exact (he.symm ▸ (show y ∈ d \ s from ⟨hy,hys⟩)).1

end FiveTransitive.Degree31BlockPairs

end CFSG
