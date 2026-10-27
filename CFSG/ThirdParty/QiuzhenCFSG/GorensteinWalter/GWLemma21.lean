module


public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.CPrime
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.DihedralAut
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.DihedralNormalSubgroup
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_3_4
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-!
# Gorenstein--Walter Part I, Lemma 2.1

This theorem-level module contains the Grün and dihedral infrastructure for
the three-case classification.  `GorensteinWalter.GW1965` retains only the
public statement wrapper and its downstream Proposition-9 consumers.
-/

noncomputable section

namespace CFSG.GorensteinWalter

open BenderSuzuki.External
open BenderSuzuki.PFchapter1section1
open scoped commutatorElement

universe u

/-! ## Normal-index consequences of the abelian quotient -/

/-- If a normal quotient is a `p`-group, its whole Sylow subgroup is the image
of any ambient Sylow `p`-subgroup.  Consequently the quotient index equals the
relative index of the normal subgroup in that Sylow subgroup. -/
public theorem normal_relIndex_sylow_eq_index_of_quotient_isPGroup
    {G : Type u} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] (S : Sylow p G)
    (N : Subgroup G) (hN : N.Normal)
    (hquot : IsPGroup p (G ⧸ N)) :
    N.relIndex (S : Subgroup G) = N.index := by
  let : N.Normal := hN
  let q : G →* G ⧸ N := QuotientGroup.mk' N
  let Sq : Sylow p (G ⧸ N) :=
    S.mapSurjective (f := q) (QuotientGroup.mk'_surjective N)
  have hSqtop : (Sq : Subgroup (G ⧸ N)) = ⊤ := by
    symm
    exact Sq.is_maximal' (hquot.to_subgroup ⊤) le_top
  calc
    N.relIndex (S : Subgroup G) = q.ker.relIndex (S : Subgroup G) := by
      rw [show q.ker = N by exact QuotientGroup.ker_mk' N]
    _ = Nat.card ((S : Subgroup G).map q) :=
      Subgroup.relIndex_ker (S : Subgroup G) q
    _ = Nat.card (Sq : Subgroup (G ⧸ N)) := by
      rw [Sylow.coe_mapSurjective]
    _ = Nat.card (⊤ : Subgroup (G ⧸ N)) := by rw [hSqtop]
    _ = Nat.card (G ⧸ N) := Subgroup.card_top
    _ = N.index := by rw [Subgroup.index_eq_card]

/-- A normal subgroup of index two contains the ambient commutator subgroup. -/
public theorem commutator_le_of_normal_index_two
    {G : Type u} [Group G] [Finite G]
    (N : Subgroup G) (hN : N.Normal) (hindex : N.index = 2) :
    commutator G ≤ N := by
  let : N.Normal := hN
  rw [← Subgroup.Normal.quotient_commutative_iff_commutator_le]
  exact (isCyclic_of_prime_card (p := 2) (by
    rw [← N.index_eq_card, hindex])).isMulCommutative

/-- A normal subgroup of index four contains the ambient commutator subgroup,
because every group of order four is commutative. -/
public theorem commutator_le_of_normal_index_four
    {G : Type u} [Group G] [Finite G]
    (N : Subgroup G) (hN : N.Normal) (hindex : N.index = 4) :
    commutator G ≤ N := by
  let : N.Normal := hN
  rw [← Subgroup.Normal.quotient_commutative_iff_commutator_le]
  apply IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 2)
  rw [← N.index_eq_card, hindex]
  norm_num

/-- An index-two normal subgroup forces two to divide the relative index of
`S ∩ G'` in a Sylow `2`-subgroup `S`. -/
public theorem normal_index_two_dvd_sylow_inf_commutator_relIndex
    {G : Type u} [Group G] [Finite G]
    (S : Sylow 2 G) (N : Subgroup G) (hN : N.Normal)
    (hindex : N.index = 2) :
    2 ∣ (((S : Subgroup G) ⊓ commutator G).relIndex (S : Subgroup G)) := by
  have hcomm : commutator G ≤ N :=
    commutator_le_of_normal_index_two N hN hindex
  have hle : (S : Subgroup G) ⊓ commutator G ≤ N :=
    fun _ hx => hcomm hx.2
  have hquot : IsPGroup 2 (G ⧸ N) := by
    let : N.Normal := hN
    apply IsPGroup.of_card (n := 1)
    rw [← N.index_eq_card, hindex]
    norm_num
  have hrel : N.relIndex (S : Subgroup G) = N.index :=
    normal_relIndex_sylow_eq_index_of_quotient_isPGroup S N hN hquot
  have hdvd : N.relIndex (S : Subgroup G) ∣
      ((S : Subgroup G) ⊓ commutator G).relIndex (S : Subgroup G) :=
    Subgroup.relIndex_dvd_of_le_left (S : Subgroup G) hle
  rwa [hrel, hindex] at hdvd

/-- An index-four normal subgroup forces four to divide the relative index of
`S ∩ G'` in a Sylow `2`-subgroup `S`. -/
public theorem normal_index_four_dvd_sylow_inf_commutator_relIndex
    {G : Type u} [Group G] [Finite G]
    (S : Sylow 2 G) (N : Subgroup G) (hN : N.Normal)
    (hindex : N.index = 4) :
    4 ∣ (((S : Subgroup G) ⊓ commutator G).relIndex (S : Subgroup G)) := by
  have hcomm : commutator G ≤ N :=
    commutator_le_of_normal_index_four N hN hindex
  have hle : (S : Subgroup G) ⊓ commutator G ≤ N :=
    fun _ hx => hcomm hx.2
  have hquot : IsPGroup 2 (G ⧸ N) := by
    let : N.Normal := hN
    apply IsPGroup.of_card (n := 2)
    rw [← N.index_eq_card, hindex]
    norm_num
  have hrel : N.relIndex (S : Subgroup G) = N.index :=
    normal_relIndex_sylow_eq_index_of_quotient_isPGroup S N hN hquot
  have hdvd : N.relIndex (S : Subgroup G) ∣
      ((S : Subgroup G) ⊓ commutator G).relIndex (S : Subgroup G) :=
    Subgroup.relIndex_dvd_of_le_left (S : Subgroup G) hle
  rwa [hrel, hindex] at hdvd

/-! ## The Grün transfer realizes the required normal factors -/

/-- The Grün transfer kernel is a normal subgroup whose index is exactly the
relative index of the Grün subgroup in the chosen Sylow subgroup. -/
public theorem exists_normal_subgroup_index_eq_grun_relIndex
    {G : Type u} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] (S : Sylow p G) :
    ∃ N : Subgroup G,
      N.Normal ∧
        N.index =
          (huppertIV34GrunKernelSubgroup (Q := G) (S : Subgroup G)).relIndex
            (S : Subgroup G) := by
  let V := huppertIV34GrunTransfer (Q := G) S
  refine ⟨V.ker, inferInstance, ?_⟩
  simpa [V] using huppertIV34GrunTransfer_ker_index (Q := G) S

/-- Relative index one for the Grün subgroup rules out normal subgroups of
index two. -/
public theorem no_normal_index_two_of_grun_relIndex_eq_one
    {G : Type u} [Group G] [Finite G]
    (S : Sylow 2 G)
    (hrel :
      (huppertIV34GrunKernelSubgroup (Q := G) (S : Subgroup G)).relIndex
        (S : Subgroup G) = 1) :
    ¬ ∃ N : Subgroup G, N.Normal ∧ N.index = 2 := by
  rintro ⟨N, hN, hindex⟩
  have hdvd := normal_index_two_dvd_sylow_inf_commutator_relIndex
    S N hN hindex
  rw [huppert_IV_3_4_first_grun (Q := G) (q := 2) S, hrel] at hdvd
  norm_num at hdvd

/-- Relative index two for the Grün subgroup produces a normal subgroup of
index two. -/
public theorem exists_normal_index_two_of_grun_relIndex_eq_two
    {G : Type u} [Group G] [Finite G]
    (S : Sylow 2 G)
    (hrel :
      (huppertIV34GrunKernelSubgroup (Q := G) (S : Subgroup G)).relIndex
        (S : Subgroup G) = 2) :
    ∃ N : Subgroup G, N.Normal ∧ N.index = 2 := by
  obtain ⟨N, hN, hindex⟩ := exists_normal_subgroup_index_eq_grun_relIndex S
  exact ⟨N, hN, hindex.trans hrel⟩

/-- Relative index two for the Grün subgroup rules out a normal subgroup of
index four. -/
public theorem no_normal_index_four_of_grun_relIndex_eq_two
    {G : Type u} [Group G] [Finite G]
    (S : Sylow 2 G)
    (hrel :
      (huppertIV34GrunKernelSubgroup (Q := G) (S : Subgroup G)).relIndex
        (S : Subgroup G) = 2) :
    ¬ ∃ N : Subgroup G, N.Normal ∧ N.index = 4 := by
  rintro ⟨N, hN, hindex⟩
  have hdvd := normal_index_four_dvd_sylow_inf_commutator_relIndex
    S N hN hindex
  rw [huppert_IV_3_4_first_grun (Q := G) (q := 2) S, hrel] at hdvd
  norm_num at hdvd

/-- Relative index four for the Grün subgroup produces a normal subgroup of
index four. -/
public theorem exists_normal_index_four_of_grun_relIndex_eq_four
    {G : Type u} [Group G] [Finite G]
    (S : Sylow 2 G)
    (hrel :
      (huppertIV34GrunKernelSubgroup (Q := G) (S : Subgroup G)).relIndex
        (S : Subgroup G) = 4) :
    ∃ N : Subgroup G, N.Normal ∧ N.index = 4 := by
  obtain ⟨N, hN, hindex⟩ := exists_normal_subgroup_index_eq_grun_relIndex S
  exact ⟨N, hN, hindex.trans hrel⟩

/-! ## Concrete dihedral subgroup coordinates -/

/-- Shifting the reflection parameter by an even amount does not change the
corresponding index-two subgroup. -/
public theorem dihedralIndexTwoSubgroup_eq_of_shift
    {m : ℕ} (hm : 1 ≤ m) (j j' : ZMod (2 ^ m)) (a : ℤ)
    (hshift : j = j' + (2 : ZMod (2 ^ m)) * (a : ZMod (2 ^ m))) :
    dihedralIndexTwoSubgroup m j = dihedralIndexTwoSubgroup m j' := by
  ext x
  rw [mem_dihedralIndexTwoSubgroup_iff hm,
    mem_dihedralIndexTwoSubgroup_iff hm]
  constructor
  · rintro (⟨k, hk⟩ | ⟨k, hk⟩)
    · exact Or.inl ⟨k, hk⟩
    · right
      refine ⟨a + k, ?_⟩
      rw [hk, hshift]
      congr 1
      push_cast
      ring
  · rintro (⟨k, hk⟩ | ⟨k, hk⟩)
    · exact Or.inl ⟨k, hk⟩
    · right
      refine ⟨k - a, ?_⟩
      rw [hk, hshift]
      congr 1
      push_cast
      ring

/-- The index-two subgroups containing the even rotations form exactly two
families, represented by reflection parameters zero and one. -/
public theorem dihedralIndexTwoSubgroup_eq_zero_or_one
    {m : ℕ} (hm : 1 ≤ m) (j : ZMod (2 ^ m)) :
    dihedralIndexTwoSubgroup m j = dihedralIndexTwoSubgroup m 0 ∨
      dihedralIndexTwoSubgroup m j = dihedralIndexTwoSubgroup m 1 := by
  rcases j.val.even_or_odd with ⟨k, hk⟩ | ⟨k, hk⟩
  · left
    apply dihedralIndexTwoSubgroup_eq_of_shift hm j 0 k
    rw [← ZMod.natCast_zmod_val j, hk]
    push_cast
    ring
  · right
    apply dihedralIndexTwoSubgroup_eq_of_shift hm j 1 k
    rw [← ZMod.natCast_zmod_val j, hk]
    push_cast
    ring

/-- Cardinality of the rotation subgroup generated by `r(2^k)`. -/
public theorem card_dihedralRotationSubgroup
    {m k : ℕ} (hk : k ≤ m) :
    Nat.card (↥(dihedralRotationSubgroup m k)) = 2 ^ (m - k) := by
  let : NeZero (2 ^ m) := ⟨pow_ne_zero m (by norm_num : 2 ≠ 0)⟩
  rw [dihedralRotationSubgroup_def, Nat.card_zpowers, DihedralGroup.orderOf_r]
  have hcast : (2 ^ k : ZMod (2 ^ m)) =
      ((2 ^ k : ℕ) : ZMod (2 ^ m)) := by norm_num
  have hval : (2 ^ k : ZMod (2 ^ m)).val = 2 ^ k % 2 ^ m := by
    rw [hcast]
    exact ZMod.val_natCast (2 ^ m) (2 ^ k)
  rw [hval]
  by_cases hkm : k = m
  · subst k
    simp
  · have hlt : k < m := lt_of_le_of_ne hk hkm
    have hp_lt : 2 ^ k < 2 ^ m :=
      (pow_lt_pow_iff_right₀ (by norm_num : 1 < 2)).2 hlt
    rw [Nat.mod_eq_of_lt hp_lt]
    have hgcd : Nat.gcd (2 ^ m) (2 ^ k) = 2 ^ k := by
      rw [Nat.gcd_eq_right_iff_dvd]
      exact pow_dvd_pow 2 hk
    rw [hgcd]
    have hpow : 2 ^ m = 2 ^ k * 2 ^ (m - k) := by
      calc
        2 ^ m = 2 ^ (k + (m - k)) := by congr 1; omega
        _ = 2 ^ k * 2 ^ (m - k) := by rw [pow_add]
    rw [hpow, Nat.mul_div_right _ (pow_pos (by norm_num : 0 < 2) k)]

/-- A rotation subgroup containing all even rotations is generated by `r 1`
or by `r 2`. -/
public theorem rotation_exponent_zero_or_one_of_even_rotations_le
    {m k : ℕ} (hm : 1 ≤ m) (hk : k ≤ m)
    (hle : Subgroup.zpowers (DihedralGroup.r (2 : ZMod (2 ^ m))) ≤
      dihedralRotationSubgroup m k) :
    k = 0 ∨ k = 1 := by
  have hcard_le := Subgroup.card_le_of_le hle
  have hcardB :
      Nat.card (↥(Subgroup.zpowers (DihedralGroup.r (2 : ZMod (2 ^ m))))) =
        2 ^ (m - 1) := by
    simpa [dihedralRotationSubgroup_def] using
      card_dihedralRotationSubgroup (m := m) (k := 1) hm
  rw [hcardB, card_dihedralRotationSubgroup hk] at hcard_le
  have hmk : m - 1 ≤ m - k :=
    (pow_le_pow_iff_right₀ (by norm_num : 1 < 2)).mp hcard_le
  omega

/-- A normal subgroup of a dihedral `2`-group containing the derived rotation
subgroup is one of five subgroups: the derived rotations, all rotations, either
reflection extension, or the whole group. -/
public theorem normal_subgroup_dihedral_above_derived_five_cases
    {m : ℕ} (hm : 1 ≤ m)
    (D : Subgroup (DihedralGroup (2 ^ m))) (hDnormal : D.Normal)
    (hB : dihedralRotationSubgroup m 1 ≤ D) :
    D = dihedralRotationSubgroup m 1 ∨
      D = dihedralRotationSubgroup m 0 ∨
      D = dihedralIndexTwoSubgroup m 0 ∨
      D = dihedralIndexTwoSubgroup m 1 ∨
      D = ⊤ := by
  rcases normal_subgroup_dihedral_two_pow hm D hDnormal with
      ⟨k, hk, hD⟩ | hD | ⟨j, hD⟩
  · have hcases : k = 0 ∨ k = 1 := by
      rw [hD] at hB
      apply rotation_exponent_zero_or_one_of_even_rotations_le hm hk
      simpa [dihedralRotationSubgroup_def] using hB
    rcases hcases with rfl | rfl
    · exact Or.inr (Or.inl hD)
    · exact Or.inl hD
  · exact Or.inr (Or.inr (Or.inr (Or.inr hD)))
  · rcases dihedralIndexTwoSubgroup_eq_zero_or_one hm j with hj | hj
    · exact Or.inr (Or.inr (Or.inl (hD.trans hj)))
    · exact Or.inr (Or.inr (Or.inr (Or.inl (hD.trans hj))))

/-- In `ZMod (2^m)`, with `m ≥ 1`, twice an element cannot be one. -/
public theorem zmod_two_mul_ne_one
    {m : ℕ} (hm : 1 ≤ m) (a : ZMod (2 ^ m)) :
    (2 : ZMod (2 ^ m)) * a ≠ 1 := by
  intro h
  have hdiv : 2 ∣ 2 ^ m := pow_dvd_pow 2 hm
  let f : ZMod (2 ^ m) →+* ZMod 2 := ZMod.castHom hdiv (ZMod 2)
  have hmap := congrArg f h
  have hf2 : f (2 : ZMod (2 ^ m)) = 0 := by
    rw [ZMod.castHom_apply]
    rw [show (2 : ZMod (2 ^ m)) = ((2 : ℕ) : ZMod (2 ^ m)) by norm_num]
    rw [ZMod.cast_natCast hdiv 2]
    simpa using ZMod.natCast_self 2
  have hzero : (0 : ZMod 2) = 1 := by
    calc
      0 = f 2 * f a := by rw [hf2, zero_mul]
      _ = f ((2 : ZMod (2 ^ m)) * a) := (map_mul f 2 a).symm
      _ = f 1 := hmap
      _ = 1 := map_one f
  norm_num at hzero

/-- The odd rotation `r 1` is absent from both reflection extensions of the
even rotation subgroup. -/
public theorem r_one_not_mem_dihedralIndexTwoSubgroup
    {m : ℕ} (hm : 1 ≤ m) (j : ZMod (2 ^ m)) :
    DihedralGroup.r 1 ∉ dihedralIndexTwoSubgroup m j := by
  rw [mem_dihedralIndexTwoSubgroup_iff hm]
  rintro (⟨k, hk⟩ | ⟨k, hk⟩)
  · have heq : (1 : ZMod (2 ^ m)) =
        (2 : ZMod (2 ^ m)) * (k : ZMod (2 ^ m)) :=
      DihedralGroup.r.inj hk
    exact zmod_two_mul_ne_one hm (k : ZMod (2 ^ m)) heq.symm
  · cases hk

/-- Each reflection extension of the even rotations has ambient index two. -/
public theorem dihedralIndexTwoSubgroup_index_eq_two
    {m : ℕ} (hm : 1 ≤ m) (j : ZMod (2 ^ m)) :
    (dihedralIndexTwoSubgroup m j).index = 2 := by
  have hdvd := dihedralIndexTwoSubgroup_index_dvd_two hm j
  have hne1 : (dihedralIndexTwoSubgroup m j).index ≠ 1 := by
    intro h
    have htop : dihedralIndexTwoSubgroup m j = ⊤ :=
      Subgroup.index_eq_one.mp h
    exact r_one_not_mem_dihedralIndexTwoSubgroup hm j (by rw [htop]; trivial)
  rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with hone | htwo
  · exact False.elim (hne1 hone)
  · exact htwo

private theorem r_two_mul_mem_even_rotations
    {m : ℕ} (a : ZMod (2 ^ m)) :
    DihedralGroup.r ((2 : ZMod (2 ^ m)) * a) ∈
      Subgroup.zpowers (DihedralGroup.r (2 : ZMod (2 ^ m))) := by
  rw [Subgroup.mem_zpowers_iff]
  refine ⟨(a.val : ℤ), ?_⟩
  rw [DihedralGroup.r_zpow]
  congr 1
  rw [Int.cast_natCast, ZMod.natCast_zmod_val]

/-- The derived subgroup of `DihedralGroup (2^m)` is the subgroup of even
rotations. -/
public theorem commutator_dihedral_two_pow
    {m : ℕ} :
    commutator (DihedralGroup (2 ^ m)) =
      Subgroup.zpowers (DihedralGroup.r (2 : ZMod (2 ^ m))) := by
  apply le_antisymm
  · change ⁅(⊤ : Subgroup (DihedralGroup (2 ^ m))), ⊤⁆ ≤
      Subgroup.zpowers (DihedralGroup.r (2 : ZMod (2 ^ m)))
    rw [Subgroup.commutator_le]
    intro a _ha b _hb
    rcases a with i | i <;> rcases b with j | j
    · simp [commutatorElement_def]
    · convert r_two_mul_mem_even_rotations (m := m) i using 1
      simp [commutatorElement_def, sub_eq_add_neg]
      ring
    · convert r_two_mul_mem_even_rotations (m := m) (-j) using 1
      simp [commutatorElement_def, sub_eq_add_neg]
      ring
    · convert r_two_mul_mem_even_rotations (m := m) (j - i) using 1
      simp [commutatorElement_def, sub_eq_add_neg]
      ring
  · rw [Subgroup.zpowers_le]
    have hmem : ⁅DihedralGroup.r (1 : ZMod (2 ^ m)), DihedralGroup.sr 0⁆ ∈
        commutator (DihedralGroup (2 ^ m)) :=
      Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)
    convert hmem using 1
    simp [commutatorElement_def]
    ring

/-! ## Excluding the full rotation subgroup from the Grün cases -/

/-- Transport the concrete commutator calculation through an equivalence with
a dihedral `2`-group. -/
public theorem commutator_eq_dihedral_even_rotations_comap
    {G : Type*} [Group G] (P : Subgroup G) {m : ℕ}
    (e : P ≃* DihedralGroup (2 ^ m)) :
    commutator P =
      (dihedralRotationSubgroup m 1).comap e.toMonoidHom := by
  apply Subgroup.map_injective (f := e.toMonoidHom) e.injective
  calc
    (commutator P).map e.toMonoidHom =
        commutator (DihedralGroup (2 ^ m)) := by
      simpa [commutator] using
        (Subgroup.map_commutator (⊤ : Subgroup P) (⊤ : Subgroup P)
          e.toMonoidHom)
    _ = dihedralRotationSubgroup m 1 := by
      simpa [dihedralRotationSubgroup_def] using
        commutator_dihedral_two_pow (m := m)
    _ = ((dihedralRotationSubgroup m 1).comap e.toMonoidHom).map
        e.toMonoidHom := by
      symm
      exact Subgroup.map_comap_eq_self_of_surjective e.surjective _

/-- Ambient-image form of the transported dihedral commutator calculation. -/
public theorem embedded_commutator_eq_even_rotations
    {G : Type*} [Group G] (P : Subgroup G) {m : ℕ}
    (e : P ≃* DihedralGroup (2 ^ m)) :
    (commutator P).map P.subtype =
      ((dihedralRotationSubgroup m 1).comap e.toMonoidHom).map P.subtype := by
  rw [commutator_eq_dihedral_even_rotations_comap P e]

/-- The ambient image of the derived subgroup is contained in the Grün
subgroup; these are the conjugate-derived generators with conjugator one. -/
public theorem embedded_commutator_le_grunKernelSubgroup
    {G : Type*} [Group G] (P : Subgroup G) :
    (commutator P).map P.subtype ≤
      huppertIV34GrunKernelSubgroup (Q := G) P := by
  classical
  intro x hx
  rw [huppertIV34GrunKernelSubgroup_def]
  apply Subgroup.subset_closure
  right
  rcases Subgroup.mem_map.mp hx with ⟨xP, hxPcomm, hxval⟩
  refine ⟨1, ?_, ?_⟩
  · rw [← hxval]
    exact xP.property
  · let Pder : Subgroup G := (commutator P).map P.subtype
    change x ∈ rightConjugate Pder 1
    simpa [Pder, rightConjugate, Subgroup.conjBy] using hx

/-- A rotation in `DihedralGroup (2^m)` whose order divides `2^(m-1)` is an
even rotation. -/
public theorem rotation_mem_even_of_orderOf_dvd
    {m : ℕ} (hm : 1 ≤ m) (x : DihedralGroup (2 ^ m))
    (hxA : x ∈ dihedralRotationSubgroup m 0)
    (horder : orderOf x ∣ 2 ^ (m - 1)) :
    x ∈ dihedralRotationSubgroup m 1 := by
  let X : Subgroup (DihedralGroup (2 ^ m)) := Subgroup.zpowers x
  have hXA : X ≤ dihedralRotationSubgroup m 0 := by
    rw [Subgroup.zpowers_le]
    exact hxA
  have hAeq : dihedralRotationSubgroup m 0 =
      Subgroup.zpowers (DihedralGroup.r (1 : ZMod (2 ^ m))) := by
    rw [dihedralRotationSubgroup_def]
    norm_num
  have hXR : X ≤ Subgroup.zpowers (DihedralGroup.r (1 : ZMod (2 ^ m))) := by
    simpa [hAeq] using hXA
  obtain ⟨k, hk, hX⟩ :=
    le_zpowers_r_one_eq_dihedralRotationSubgroup hm X hXR
  have hcardX : Nat.card X = orderOf x := Nat.card_zpowers x
  have hcard_le : Nat.card X ≤ 2 ^ (m - 1) := by
    rw [hcardX]
    exact Nat.le_of_dvd (pow_pos (by norm_num : 0 < 2) (m - 1)) horder
  have hpow_le : 2 ^ (m - k) ≤ 2 ^ (m - 1) := by
    rw [hX, card_dihedralRotationSubgroup hk] at hcard_le
    exact hcard_le
  have hmk : m - k ≤ m - 1 :=
    (pow_le_pow_iff_right₀ (by norm_num : 1 < 2)).mp hpow_le
  have hk1 : 1 ≤ k := by omega
  have hrot_le : dihedralRotationSubgroup m k ≤
      dihedralRotationSubgroup m 1 := by
    rw [dihedralRotationSubgroup_def, dihedralRotationSubgroup_def,
      show (2 ^ 1 : ZMod (2 ^ m)) = 2 by norm_num, Subgroup.zpowers_le]
    rw [show DihedralGroup.r (2 ^ k : ZMod (2 ^ m)) =
        (DihedralGroup.r (2 : ZMod (2 ^ m))) ^ (2 ^ (k - 1)) by
      rw [DihedralGroup.r_pow]
      congr 1
      push_cast
      rw [show k = 1 + (k - 1) by omega, pow_add]
      norm_num]
    exact Subgroup.pow_mem _ (Subgroup.mem_zpowers _) _
  apply hrot_le
  rw [← hX]
  exact Subgroup.mem_zpowers x

/-- In an ambient group, an element that is both a rotation of an embedded
dihedral subgroup and a conjugate of one of its even rotations is itself an
even rotation. -/
public theorem rotation_inter_conjugate_even
    {G : Type*} [Group G] [Finite G]
    (P : Subgroup G) {m : ℕ} (hm : 1 ≤ m)
    (e : P ≃* DihedralGroup (2 ^ m))
    (g x : G)
    (hxA : x ∈
      ((dihedralRotationSubgroup m 0).comap e.toMonoidHom).map P.subtype)
    (hxconj : x ∈ rightConjugate
      (((dihedralRotationSubgroup m 1).comap e.toMonoidHom).map P.subtype) g) :
    x ∈ ((dihedralRotationSubgroup m 1).comap e.toMonoidHom).map P.subtype := by
  rcases Subgroup.mem_map.mp hxA with ⟨xP, hxPA, hxval⟩
  rw [rightConjugate, Subgroup.conjBy, Subgroup.mem_map] at hxconj
  rcases hxconj with ⟨y, hyB, hyx⟩
  rcases Subgroup.mem_map.mp hyB with ⟨yP, hyPB, hypval⟩
  have hey_dvd : orderOf (e yP) ∣ 2 ^ (m - 1) := by
    rw [← card_dihedralRotationSubgroup (m := m) (k := 1) hm,
      ← Nat.card_zpowers]
    apply Subgroup.card_dvd_of_le
    rw [Subgroup.zpowers_le]
    exact hyPB
  have horders : orderOf (e xP) = orderOf (e yP) := by
    calc
      orderOf (e xP) = orderOf xP := e.orderOf_eq xP
      _ = orderOf x := by
        rw [← hxval]
        exact (orderOf_injective P.subtype P.subtype_injective xP).symm
      _ = orderOf y := by
        rw [← hyx]
        exact MulEquiv.orderOf_eq (MulAut.conj g⁻¹) y
      _ = orderOf yP := by
        rw [← hypval]
        exact orderOf_injective P.subtype P.subtype_injective yP
      _ = orderOf (e yP) := (e.orderOf_eq yP).symm
  have hex_dvd : orderOf (e xP) ∣ 2 ^ (m - 1) := horders ▸ hey_dvd
  refine Subgroup.mem_map.mpr ⟨xP, ?_, hxval⟩
  exact rotation_mem_even_of_orderOf_dvd hm (e xP) hxPA hex_dvd

/-- If the automorphism group of a Sylow `p`-subgroup is a `p`-group, every
element of its ambient normalizer is a product of a Sylow element and a
centralizer element. -/
public theorem normalizer_decomp_of_aut_isPGroup
    {G : Type u} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (S : Sylow p G) (hAut : IsPGroup p (MulAut S))
    {n : G} (hn : n ∈ Subgroup.normalizer ((S : Subgroup G) : Set G)) :
    ∃ s : G, s ∈ (S : Subgroup G) ∧
      ∃ c : G, c ∈ Subgroup.centralizer ((S : Subgroup G) : Set G) ∧
        n = s * c := by
  let N : Subgroup G := Subgroup.normalizer ((S : Subgroup G) : Set G)
  let phi : N →* MulAut S :=
    Subgroup.normalizerMonoidHom (H := (S : Subgroup G))
  let SN : Sylow p N := S.subtype Subgroup.le_normalizer
  let R : Subgroup (MulAut S) := phi.range
  let SR : Sylow p R := SN.mapSurjective (f := phi.rangeRestrict)
    phi.rangeRestrict_surjective
  have hRp : IsPGroup p R := hAut.to_subgroup R
  have hSRtop : (SR : Subgroup R) = ⊤ := by
    symm
    exact SR.is_maximal' (hRp.to_subgroup ⊤) le_top
  let nN : N := ⟨n, hn⟩
  let y : R := ⟨phi nN, ⟨nN, rfl⟩⟩
  have hySR : y ∈ (SR : Subgroup R) := by rw [hSRtop]; trivial
  rw [Sylow.coe_mapSurjective] at hySR
  rcases hySR with ⟨sN, hsSN, hphis⟩
  have hphi : phi sN = phi nN := congrArg Subtype.val hphis
  have hsS : (sN : G) ∈ (S : Subgroup G) := hsSN
  let cN : N := sN⁻¹ * nN
  have hcKer : cN ∈ phi.ker := by
    change phi cN = 1
    dsimp [cN]
    rw [map_mul, map_inv, hphi]
    simp
  have hker : phi.ker =
      (Subgroup.centralizer ((S : Subgroup G) : Set G)).subgroupOf N := by
    simpa [phi, N] using
      (Subgroup.normalizerMonoidHom_ker (H := (S : Subgroup G)))
  have hcC : (cN : G) ∈ Subgroup.centralizer ((S : Subgroup G) : Set G) := by
    rw [hker] at hcKer
    exact hcKer
  refine ⟨sN, hsS, cN, hcC, ?_⟩
  dsimp [cN, nN]
  simp

/-- A central element that is already known to be a rotation in a dihedral
`2`-group of order at least eight is an even rotation. -/
public theorem central_rotation_mem_even
    {m : ℕ} (hm : 2 ≤ m) (x : DihedralGroup (2 ^ m))
    (hxA : x ∈ dihedralRotationSubgroup m 0)
    (hxZ : x ∈ Subgroup.center (DihedralGroup (2 ^ m))) :
    x ∈ dihedralRotationSubgroup m 1 := by
  rcases dihedralGroup_cases x with ⟨i, rfl⟩ | ⟨i, rfl⟩
  · have hcomm :=
      Subgroup.mem_center_iff.mp hxZ (DihedralGroup.sr (0 : ZMod (2 ^ m)))
    have hneg : i = -i := by
      simpa [DihedralGroup.r_mul_sr, DihedralGroup.sr_mul_r] using hcomm
    have hsq : (DihedralGroup.r i : DihedralGroup (2 ^ m)) ^ 2 = 1 := by
      rw [pow_two, DihedralGroup.r_mul_r, DihedralGroup.one_def]
      congr 1
      calc
        i + i = i + -i := congrArg (fun z => i + z) hneg
        _ = 0 := by simp
    have hord2 : orderOf (DihedralGroup.r i : DihedralGroup (2 ^ m)) ∣ 2 :=
      orderOf_dvd_of_pow_eq_one hsq
    have h2pow : 2 ∣ 2 ^ (m - 1) := by
      change (2 : ℕ) ^ 1 ∣ 2 ^ (m - 1)
      exact pow_dvd_pow (2 : ℕ) (by omega : 1 ≤ m - 1)
    exact rotation_mem_even_of_orderOf_dvd (by omega) _ hxA
      (hord2.trans h2pow)
  · exfalso
    apply sr_not_mem_zpowers_r_one i
    simpa [dihedralRotationSubgroup_def] using hxA

/-- Inside the normalizer of a Sylow subgroup whose automorphism group is a
`p`-group, the derived subgroup is contained in the product of the Sylow
derived subgroup and the centralizer. -/
public theorem normalizer_commutator_le_sylow_commutator_sup_centralizer
    {G : Type u} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (S : Sylow p G) (hAut : IsPGroup p (MulAut S)) :
    let N : Subgroup G := Subgroup.normalizer ((S : Subgroup G) : Set G)
    let P : Subgroup N := (S : Subgroup G).subgroupOf N
    let B : Subgroup N := (commutator P).map P.subtype
    let C : Subgroup N :=
      (Subgroup.centralizer ((S : Subgroup G) : Set G)).subgroupOf N
    commutator N ≤ B ⊔ C := by
  classical
  let N : Subgroup G := Subgroup.normalizer ((S : Subgroup G) : Set G)
  let P : Subgroup N := (S : Subgroup G).subgroupOf N
  let B : Subgroup N := (commutator P).map P.subtype
  let C : Subgroup N :=
    (Subgroup.centralizer ((S : Subgroup G) : Set G)).subgroupOf N
  let K : Subgroup N := B ⊔ C
  have : P.Normal := by
    simpa [P, N] using
      (inferInstance : ((S : Subgroup G).subgroupOf
        (Subgroup.normalizer ((S : Subgroup G) : Set G))).Normal)
  have : B.Normal := by
    simpa [B] using
      (inferInstance : ((commutator P).map P.subtype).Normal)
  have : C.Normal := by
    simpa [C, N] using
      (Subgroup.normal_subgroupOf_centralizer_normalizer
        (((S : Subgroup G) : Subgroup G) : Set G))
  have : K.Normal := by
    dsimp [K]
    infer_instance
  have hcomm : IsMulCommutative (N ⧸ K) := by
    constructor
    constructor
    intro x y
    obtain ⟨n, rfl⟩ := QuotientGroup.mk'_surjective K x
    obtain ⟨n', rfl⟩ := QuotientGroup.mk'_surjective K y
    obtain ⟨s, hs, c, hc, hn⟩ :=
      normalizer_decomp_of_aut_isPGroup S hAut n.property
    obtain ⟨s', hs', c', hc', hn'⟩ :=
      normalizer_decomp_of_aut_isPGroup S hAut n'.property
    let sN : N := ⟨s, Subgroup.le_normalizer hs⟩
    let sN' : N := ⟨s', Subgroup.le_normalizer hs'⟩
    let cN : N := ⟨c, Subgroup.centralizer_le_normalizer _ hc⟩
    let cN' : N := ⟨c', Subgroup.centralizer_le_normalizer _ hc'⟩
    have hsP : sN ∈ P := hs
    have hsP' : sN' ∈ P := hs'
    have hcC : cN ∈ C := hc
    have hcC' : cN' ∈ C := hc'
    have hcK : cN ∈ K := (le_sup_right : C ≤ K) hcC
    have hcK' : cN' ∈ K := (le_sup_right : C ≤ K) hcC'
    have hqc : QuotientGroup.mk' K cN = 1 :=
      (QuotientGroup.eq_one_iff cN).2 hcK
    have hqc' : QuotientGroup.mk' K cN' = 1 :=
      (QuotientGroup.eq_one_iff cN').2 hcK'
    have hnN : n = sN * cN := by
      apply Subtype.ext
      exact hn
    have hnN' : n' = sN' * cN' := by
      apply Subtype.ext
      exact hn'
    have hqs : QuotientGroup.mk' K n = QuotientGroup.mk' K sN := by
      rw [hnN, map_mul, hqc, mul_one]
    have hqs' : QuotientGroup.mk' K n' = QuotientGroup.mk' K sN' := by
      rw [hnN', map_mul, hqc', mul_one]
    rw [hqs, hqs']
    rw [← commutatorElement_eq_one_iff_mul_comm,
      ← map_commutatorElement]
    apply (QuotientGroup.eq_one_iff (N := K) ⁅sN, sN'⁆).2
    apply (le_sup_left : B ≤ K)
    rw [Subgroup.mem_map]
    let sP : P := ⟨sN, hsP⟩
    let sP' : P := ⟨sN', hsP'⟩
    refine ⟨⁅sP, sP'⁆, Subgroup.commutator_mem_commutator
      (Subgroup.mem_top _) (Subgroup.mem_top _), ?_⟩
    rfl
  exact (Subgroup.Normal.quotient_commutative_iff_commutator_le
    (N := K)).mp hcomm

/-- An element of the normalizer-derived part of the Grün generating set
which is already known to be a rotation is necessarily an even rotation. -/
public theorem normalizer_derived_rotation_even
    {G : Type u} [Group G] [Finite G]
    (S : Sylow 2 G) {m : ℕ} (hm : 2 ≤ m)
    (e : S ≃* DihedralGroup (2 ^ m))
    (hAut : IsPGroup 2 (MulAut S)) {x : G}
    (hxA : x ∈
      ((dihedralRotationSubgroup m 0).comap e.toMonoidHom).map
        (S : Subgroup G).subtype)
    (hxderived : x ∈
      (commutator (Subgroup.normalizer ((S : Subgroup G) : Set G))).map
        (Subgroup.normalizer ((S : Subgroup G) : Set G)).subtype) :
    x ∈ ((dihedralRotationSubgroup m 1).comap e.toMonoidHom).map
      (S : Subgroup G).subtype := by
  classical
  let N : Subgroup G := Subgroup.normalizer ((S : Subgroup G) : Set G)
  let P : Subgroup N := (S : Subgroup G).subgroupOf N
  let B : Subgroup N := (commutator P).map P.subtype
  let C : Subgroup N :=
    (Subgroup.centralizer ((S : Subgroup G) : Set G)).subgroupOf N
  let Bamb : Subgroup G :=
    ((dihedralRotationSubgroup m 1).comap e.toMonoidHom).map
      (S : Subgroup G).subtype
  have : C.Normal := by
    simpa [C, N] using
      (Subgroup.normal_subgroupOf_centralizer_normalizer
        (((S : Subgroup G) : Subgroup G) : Set G))
  have hcomm_le : commutator N ≤ B ⊔ C := by
    simpa [N, P, B, C] using
      (normalizer_commutator_le_sylow_commutator_sup_centralizer S hAut)
  rcases Subgroup.mem_map.mp hxA with ⟨xS, hxSA, hxval⟩
  rcases Subgroup.mem_map.mp hxderived with ⟨xN, hxNcomm, hxNval⟩
  have hxNK : xN ∈ B ⊔ C := hcomm_le hxNcomm
  rcases (Subgroup.mem_sup_of_normal_right.mp hxNK) with
    ⟨b, hbB, c, hcC, hbc⟩
  rcases Subgroup.mem_map.mp hbB with ⟨bP, hbPcomm, hbval⟩
  let f : P ≃* S := Subgroup.subgroupOfEquivOfLe
    (show (S : Subgroup G) ≤ N from Subgroup.le_normalizer)
  let eP : P ≃* DihedralGroup (2 ^ m) := f.trans e
  have hmap_comm : (commutator P).map eP.toMonoidHom =
      commutator (DihedralGroup (2 ^ m)) := by
    simpa [commutator] using
      (Subgroup.map_commutator (⊤ : Subgroup P) (⊤ : Subgroup P)
        eP.toMonoidHom)
  have hebComm : eP bP ∈ commutator (DihedralGroup (2 ^ m)) := by
    rw [← hmap_comm]
    exact Subgroup.mem_map_of_mem eP.toMonoidHom hbPcomm
  have hebB : e (f bP) ∈ dihedralRotationSubgroup m 1 := by
    change eP bP ∈ dihedralRotationSubgroup m 1
    simpa [commutator_dihedral_two_pow, dihedralRotationSubgroup_def] using
      hebComm
  have hfbval : ((f bP : S) : G) = (b : G) := by
    have hbvalG := congrArg Subtype.val hbval
    simpa [f, P, N] using hbvalG
  have hbBamb : (b : G) ∈ Bamb := by
    refine Subgroup.mem_map.mpr ⟨f bP, hebB, ?_⟩
    exact hfbval
  have hbcG : (b : G) * (c : G) = x := by
    calc
      (b : G) * (c : G) = (xN : G) := congrArg Subtype.val hbc
      _ = x := hxNval
  have hcval : (c : G) = (b : G)⁻¹ * x := by
    calc
      (c : G) = (b : G)⁻¹ * ((b : G) * (c : G)) := by group
      _ = (b : G)⁻¹ * x := by rw [hbcG]
  let cS : S := ⟨c, by
    rw [hcval, ← hfbval, ← hxval]
    exact (S : Subgroup G).mul_mem ((S : Subgroup G).inv_mem (f bP).property)
      xS.property⟩
  have hcSeq : cS = (f bP)⁻¹ * xS := by
    apply Subtype.ext
    change (c : G) = ((f bP : S) : G)⁻¹ * (xS : G)
    rw [hcval, hfbval]
    congr 1
    exact hxval.symm
  have hBA : dihedralRotationSubgroup m 1 ≤
      dihedralRotationSubgroup m 0 := by
    rw [dihedralRotationSubgroup_def, dihedralRotationSubgroup_def,
      show (2 ^ 0 : ZMod (2 ^ m)) = 1 by norm_num, Subgroup.zpowers_le]
    simpa only [pow_one] using r_mem_zpowers_r_one 2
  have hecA : e cS ∈ dihedralRotationSubgroup m 0 := by
    rw [hcSeq, map_mul, map_inv]
    exact (dihedralRotationSubgroup m 0).mul_mem
      ((dihedralRotationSubgroup m 0).inv_mem (hBA hebB)) hxSA
  have hcCenter : cS ∈ Subgroup.center S := by
    apply Subgroup.mem_center_iff.mpr
    intro y
    apply Subtype.ext
    have hcCentAmb : (c : G) ∈
        Subgroup.centralizer ((S : Subgroup G) : Set G) := hcC
    exact Subgroup.mem_centralizer_iff.mp hcCentAmb y y.property
  have hecCenter : e cS ∈
      Subgroup.center (DihedralGroup (2 ^ m)) :=
    MulEquivClass.apply_mem_center e hcCenter
  have hecB : e cS ∈ dihedralRotationSubgroup m 1 :=
    central_rotation_mem_even hm (e cS) hecA hecCenter
  have hcBamb : (c : G) ∈ Bamb := by
    exact Subgroup.mem_map.mpr ⟨cS, hecB, rfl⟩
  have hprod : (b : G) * (c : G) ∈ Bamb := Bamb.mul_mem hbBamb hcBamb
  rw [hbcG] at hprod
  exact hprod

/-- If the Grün subgroup of a dihedral Sylow `2`-subgroup is contained in the
full rotation subgroup, then it is exactly the even-rotation subgroup. -/
public theorem grun_eq_even_rotations_of_le_rotations
    {G : Type u} [Group G] [Finite G]
    (S : Sylow 2 G) {m : ℕ} (hm : 2 ≤ m)
    (e : S ≃* DihedralGroup (2 ^ m))
    (hAut : IsPGroup 2 (MulAut S))
    (hDleA : huppertIV34GrunKernelSubgroup (Q := G) (S : Subgroup G) ≤
      ((dihedralRotationSubgroup m 0).comap e.toMonoidHom).map
        (S : Subgroup G).subtype) :
    huppertIV34GrunKernelSubgroup (Q := G) (S : Subgroup G) =
      ((dihedralRotationSubgroup m 1).comap e.toMonoidHom).map
        (S : Subgroup G).subtype := by
  classical
  let D : Subgroup G :=
    huppertIV34GrunKernelSubgroup (Q := G) (S : Subgroup G)
  let B : Subgroup G :=
    ((dihedralRotationSubgroup m 1).comap e.toMonoidHom).map
      (S : Subgroup G).subtype
  let Pder : Subgroup G := (commutator (S : Subgroup G)).map
    (S : Subgroup G).subtype
  have hPder : Pder = B := by
    simpa [Pder, B] using
      (embedded_commutator_eq_even_rotations (S : Subgroup G) e)
  apply le_antisymm
  · rw [huppertIV34GrunKernelSubgroup_def, Subgroup.closure_le]
    intro x hx
    have hxD : x ∈ D := by
      change x ∈ huppertIV34GrunKernelSubgroup (Q := G) (S : Subgroup G)
      rw [huppertIV34GrunKernelSubgroup_def]
      exact Subgroup.subset_closure hx
    have hxA := hDleA hxD
    rcases hx with hxN | hxC
    · exact normalizer_derived_rotation_even S hm e hAut hxA hxN.2
    · rcases hxC with ⟨g, _hxS, hxconj⟩
      change x ∈ rightConjugate Pder g at hxconj
      rw [hPder] at hxconj
      exact rotation_inter_conjugate_even (S : Subgroup G) (by omega) e
        g x hxA hxconj
  · intro x hxB
    apply embedded_commutator_le_grunKernelSubgroup (S : Subgroup G)
    change x ∈ Pder
    rwa [hPder]

/-- The Grün subgroup of a dihedral Sylow `2`-subgroup of order at least eight
is the even rotations, one of the two reflection extensions, or the whole
Sylow subgroup. -/
public theorem dihedral_grun_subgroup_four_cases
    {G : Type u} [Group G] [Finite G]
    (S : Sylow 2 G) {m : ℕ} (hm : 2 ≤ m)
    (e : S ≃* DihedralGroup (2 ^ m))
    (hAut : IsPGroup 2 (MulAut S)) :
    let D := huppertIV34GrunKernelSubgroup (Q := G) (S : Subgroup G)
    D = ((dihedralRotationSubgroup m 1).comap e.toMonoidHom).map
          (S : Subgroup G).subtype ∨
      D = ((dihedralIndexTwoSubgroup m 0).comap e.toMonoidHom).map
          (S : Subgroup G).subtype ∨
      D = ((dihedralIndexTwoSubgroup m 1).comap e.toMonoidHom).map
          (S : Subgroup G).subtype ∨
      D = (S : Subgroup G) := by
  classical
  let D : Subgroup G :=
    huppertIV34GrunKernelSubgroup (Q := G) (S : Subgroup G)
  let DS : Subgroup S := D.subgroupOf (S : Subgroup G)
  let De : Subgroup (DihedralGroup (2 ^ m)) := DS.map e.toMonoidHom
  have hDleS : D ≤ (S : Subgroup G) := by
    change huppertIV34GrunKernelSubgroup (Q := G) (S : Subgroup G) ≤
      (S : Subgroup G)
    rw [← huppert_IV_3_4_first_grun (Q := G) (q := 2) S]
    exact inf_le_left
  have : DS.Normal := by
    simpa [DS, D] using
      (inferInstance :
        ((huppertIV34GrunKernelSubgroup (Q := G) (S : Subgroup G)).subgroupOf
          (S : Subgroup G)).Normal)
  have hDeNormal : De.Normal := by
    exact (inferInstance : DS.Normal).map e.toMonoidHom e.surjective
  have hB : dihedralRotationSubgroup m 1 ≤ De := by
    intro y hy
    let yS : S := e.symm y
    have hycomm : yS ∈ commutator (S : Subgroup G) := by
      rw [commutator_eq_dihedral_even_rotations_comap (S : Subgroup G) e]
      change e yS ∈ dihedralRotationSubgroup m 1
      simpa [yS] using hy
    have hyD : (yS : G) ∈ D := by
      apply embedded_commutator_le_grunKernelSubgroup (S : Subgroup G)
      exact Subgroup.mem_map_of_mem (S : Subgroup G).subtype hycomm
    have hyDS : yS ∈ DS := hyD
    exact Subgroup.mem_map.mpr ⟨yS, hyDS, e.apply_symm_apply y⟩
  have htransport (H : Subgroup (DihedralGroup (2 ^ m))) (hDeH : De = H) :
      D = (H.comap e.toMonoidHom).map (S : Subgroup G).subtype := by
    have hDSH : DS = H.comap e.toMonoidHom := by
      apply Subgroup.map_injective (f := e.toMonoidHom) e.injective
      change De = (H.comap e.toMonoidHom).map e.toMonoidHom
      rw [hDeH]
      symm
      exact Subgroup.map_comap_eq_self_of_surjective e.surjective H
    calc
      D = DS.map (S : Subgroup G).subtype :=
        (Subgroup.map_subgroupOf_eq_of_le hDleS).symm
      _ = (H.comap e.toMonoidHom).map (S : Subgroup G).subtype := by
        rw [hDSH]
  rcases normal_subgroup_dihedral_above_derived_five_cases (by omega) De
      hDeNormal hB with hDB | hDA | hDE0 | hDE1 | hDtop
  · exact Or.inl (htransport _ hDB)
  · left
    apply grun_eq_even_rotations_of_le_rotations S hm e hAut
    exact le_of_eq (htransport _ hDA)
  · exact Or.inr (Or.inl (htransport _ hDE0))
  · exact Or.inr (Or.inr (Or.inl (htransport _ hDE1)))
  · right
    right
    right
    change D = (S : Subgroup G)
    have ht := htransport ⊤ hDtop
    rw [Subgroup.comap_top] at ht
    rw [← MonoidHom.range_eq_map, Subgroup.range_subtype] at ht
    exact ht

end CFSG.GorensteinWalter
