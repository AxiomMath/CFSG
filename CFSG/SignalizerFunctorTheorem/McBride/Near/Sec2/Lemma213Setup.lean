module

public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec2.Lemma213Aux
public import CFSG.SignalizerFunctorTheorem.McBride.Prelim.Semisimple
public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec2.Lemma212Aux
public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec2.Thm210g

public section

open CFSG.Open
open scoped Pointwise

namespace CFSG.SignalizerFunctorTheorem.McBride.Near.Lemma213

variable {Γ : Type*} [Group Γ] {p : ℕ} {A G W : Subgroup Γ}

structure Hyp (p : ℕ) (A G W : Subgroup Γ) : Prop where
  near : NearAsolvAction p A G
  sol_eq : sol G = ⊥
  ne_bot : G ≠ ⊥
  le : W ≤ kOf G
  admits : Admits (cenIn G A ⊔ A) W
  perfect : Group.IsPerfect ↥W

@[expose] def tOne (G W : Subgroup Γ) : Set (Subgroup Γ) :=
  {J | J ∈ lcal (kOf G) ∧ projIn (lcal (kOf G)) J W = ⊥}

@[expose] def tTwo (G W : Subgroup Γ) : Set (Subgroup Γ) :=
  {J | J ∈ lcal (kOf G) ∧ projIn (lcal (kOf G)) J W = J}

theorem tOne_subset (G W : Subgroup Γ) : tOne G W ⊆ lcal (kOf G) := fun _ hJ => hJ.1

theorem tTwo_subset (G W : Subgroup Γ) : tTwo G W ⊆ lcal (kOf G) := fun _ hJ => hJ.1

theorem simple_of_mem_lcal {X J : Subgroup Γ} (hJ : J ∈ lcal X) :
    IsSimpleGroup ↥J ∧ ¬ IsMulCommutative ↥J :=
  (mem_lcal_iff.1 hJ).2.2

theorem mem_normalizer_kOf [Finite Γ] {G : Subgroup Γ} (hsol : sol G = ⊥) {g : Γ}
    (hg : g ∈ Subgroup.normalizer (G : Set Γ)) : g ∈ Subgroup.normalizer (kOf G : Set Γ) := by
  have hK := isDirectProduct_lcal_kOf hsol
  have key : ∀ g ∈ Subgroup.normalizer (G : Set Γ), ∀ x ∈ kOf G, g * x * g⁻¹ ∈ kOf G :=
    fun g hg x hx => hK.conj_mem (fun J hJ => map_conj_mem_lcal hJ hg) hx
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨key g hg x, fun hx => ?_⟩
  have := key g⁻¹ (inv_mem hg) _ hx
  simpa [mul_assoc] using this

theorem kOf_ne_bot [Finite Γ] {G : Subgroup Γ} (hsol : sol G = ⊥) (hG : G ≠ ⊥) : kOf G ≠ ⊥ := by
  intro hK
  apply hG
  have h := centralizer_kOf_eq_bot hsol
  rwa [hK, centralizer_bot, inf_top_eq] at h

namespace Hyp

variable [Finite Γ] (H : Hyp p A G W)

include H

theorem admits_A_kOf : Admits A (kOf G) := fun _ ha =>
  mem_normalizer_kOf H.sol_eq (H.near.admits ha)

theorem admits_DA_kOf : Admits (cenIn G A ⊔ A) (kOf G) :=
  sup_le (fun _ hd =>
    mem_normalizer_kOf H.sol_eq (Subgroup.le_normalizer (Subgroup.mem_inf.1 hd).1)) H.admits_A_kOf

omit [Finite Γ] in
theorem admits_A_W : Admits A W := le_sup_right.trans H.admits

theorem semisimpleAction : SemisimpleAction p A (kOf G) where
  prime := H.near.prime
  odd := H.near.odd
  elemAbelian := H.near.elemAbelian
  admits := H.admits_A_kOf
  nearPSolvable := signalizerNearPSolvable_of_le (kOf_le G) H.near.nearPSolvable
  solvable_cen := by
    have : Group.IsSolvable ↥(G ⊓ Subgroup.centralizer (A : Set Γ)) := H.near.solvable_cen
    exact Group.isSolvable_of_isSolvable_injective
      (Subgroup.inclusion_injective (inf_le_inf_right _ (kOf_le G) :
        kOf G ⊓ Subgroup.centralizer (A : Set Γ) ≤ G ⊓ Subgroup.centralizer (A : Set Γ)))
  semisimple := isSemisimple_kOf H.sol_eq
  ne_bot := kOf_ne_bot H.sol_eq H.ne_bot

theorem hK : IsDirectProduct (lcal (kOf G)) (kOf G) :=
  H.semisimpleAction.isDirectProduct_lcal

omit [Finite Γ] in
theorem admits_cenK_W : Admits (cenIn (kOf G) A ⊔ A) W :=
  (sup_le_sup_right (inf_le_inf_right _ (kOf_le G)) A).trans H.admits

theorem dichotomy
    {J : Subgroup Γ} (hJ : J ∈ lcal (kOf G)) :
    projIn (lcal (kOf G)) J W = ⊥ ∨ (projIn (lcal (kOf G)) J W = J ∧ smear J A ≤ W) := by
  have := H.perfect
  rcases projIn_eq_bot_or_not_isSolvable H.hK hJ H.le with h | h
  · exact Or.inl h
  · exact Or.inr (thm210g H.semisimpleAction H.le H.admits_cenK_W hJ h)

theorem tTwo_eq_diff
    : tTwo G W = lcal (kOf G) \ tOne G W := by
  ext J
  constructor
  · rintro ⟨hJ, hJW⟩
    refine ⟨hJ, fun hJ1 => ne_bot_of_mem_lcal hJ ?_⟩
    rw [← hJW, hJ1.2]
  · rintro ⟨hJ, hJn⟩
    refine ⟨hJ, ?_⟩
    rcases H.dichotomy hJ with h | ⟨h, -⟩
    · exact absurd ⟨hJ, h⟩ hJn
    · exact h

theorem disjoint_tOne_tTwo
    : Disjoint (tOne G W) (tTwo G W) := by
  rw [H.tTwo_eq_diff]
  exact Set.disjoint_sdiff_right

theorem tOne_union_tTwo
    : tOne G W ∪ tTwo G W = lcal (kOf G) := by
  rw [H.tTwo_eq_diff]
  exact Set.union_sdiff_cancel (tOne_subset G W)

theorem smear_le_W
    {J : Subgroup Γ} (hJ : J ∈ tTwo G W) : smear J A ≤ W := by
  rcases H.dichotomy hJ.1 with h | ⟨-, h⟩
  · exact absurd (hJ.2.symm.trans h) (ne_bot_of_mem_lcal hJ.1)
  · exact h

theorem le_k1_of_mem_tOne {J : Subgroup Γ} (hJ : J ∈ tOne G W) : J ≤ k1 G W := by
  have hJL := hJ.1
  refine le_inf (H.hK.le hJL) fun j hj => ?_
  rw [Subgroup.mem_centralizer_iff]
  intro w hw
  have hwK : w ∈ kOf G := H.le hw
  have h1 : H.hK.coord hJL ⟨w, hwK⟩ = 1 := by
    have hmem : ((H.hK.coord hJL ⟨w, hwK⟩ : J) : Γ) ∈ projIn (lcal (kOf G)) J W :=
      (H.hK.mem_projIn_iff hJL).2 ⟨⟨w, hwK⟩, hw, rfl⟩
    rw [hJ.2, Subgroup.mem_bot] at hmem
    exact Subtype.ext hmem
  have h2 : w ∈ sSup (lcal (kOf G) \ {J}) := (H.hK.coord_eq_one_iff hJL ⟨w, hwK⟩).1 h1
  exact (H.hK.commute_sSup_diff hJL j hj w h2).eq.symm

theorem k1_le_sSup_tOne :
    k1 G W ≤ sSup (tOne G W) := by
  intro y hy
  obtain ⟨hyK, hyc⟩ := Subgroup.mem_inf.1 hy
  refine H.hK.mem_of_coord_mem hyK fun J hJ => ?_
  by_cases hJ1 : J ∈ tOne G W
  · exact le_sSup hJ1 (H.hK.coord hJ ⟨y, hyK⟩).2
  · have hJ2 : J ∈ tTwo G W := by
      rw [H.tTwo_eq_diff]
      exact ⟨hJ, hJ1⟩
    have h1 : H.hK.coord hJ ⟨y, hyK⟩ = 1 := by
      refine coord_eq_one_of_commute H.hK hJ (simple_of_mem_lcal hJ).1
        (simple_of_mem_lcal hJ).2 (P := W) hJ2.2.ge hyK fun w hw => ?_
      exact Subgroup.mem_centralizer_iff.1 hyc w hw
    rw [h1]
    exact one_mem _

theorem k1_eq :
    k1 G W = sSup (tOne G W) :=
  le_antisymm H.k1_le_sSup_tOne (sSup_le fun _ hJ => H.le_k1_of_mem_tOne hJ)

theorem k2_eq :
    k2 G W = sSup (tTwo G W) := by
  unfold k2
  rw [H.k1_eq, cenIn_sSup_eq H.hK (fun J hJ => simple_of_mem_lcal hJ) (tOne_subset G W),
    H.tTwo_eq_diff]

omit [Finite Γ] in
theorem le_k2 : W ≤ k2 G W := by
  refine le_inf H.le fun w hw => ?_
  rw [Subgroup.mem_centralizer_iff]
  intro k hk
  exact (Subgroup.mem_centralizer_iff.1 (Subgroup.mem_inf.1 hk).2 w hw).symm

theorem isDirectPair
    : IsDirectPair (k1 G W) (k2 G W) (kOf G) where
  commute := fun x hx y hy =>
    (Subgroup.mem_centralizer_iff.1 (Subgroup.mem_inf.1 hy).2 x hx : x * y = y * x)
  inf_eq_bot := by
    rw [H.k1_eq, H.k2_eq]
    exact disjoint_iff.1
      (Thm210.disjoint_sSup_sSup H.hK (tOne_subset G W) (tTwo_subset G W) H.disjoint_tOne_tTwo)
  sup_eq := by
    rw [H.k1_eq, H.k2_eq, ← sSup_union, H.tOne_union_tTwo]
    exact H.hK.sSup_eq

theorem admits_A_k1 : Admits A (k1 G W) := admits_cenIn H.admits_A_kOf H.admits_A_W

theorem admits_A_k2 : Admits A (k2 G W) := admits_cenIn H.admits_A_kOf H.admits_A_k1

theorem smear_le_k1 {J : Subgroup Γ} (hJ : J ∈ tOne G W) : smear J A ≤ k1 G W :=
  (smear_le_orbitClosure J A).trans
    (Lemma212.orbitClosure_le_of_normalizer (H.le_k1_of_mem_tOne hJ) H.admits_A_k1)

theorem cenIn_le_sup
    : cenIn (kOf G) (A : Set Γ) ≤ W ⊔ k1 G W := by
  rw [← H.semisimpleAction.isDirectProduct_smear.sSup_eq]
  refine sSup_le ?_
  rintro _ ⟨J, hJ, rfl⟩
  by_cases hJ1 : J ∈ tOne G W
  · exact (H.smear_le_k1 hJ1).trans le_sup_right
  · have hJ2 : J ∈ tTwo G W := by
      rw [H.tTwo_eq_diff]
      exact ⟨hJ, hJ1⟩
    exact (H.smear_le_W hJ2).trans le_sup_left

end Hyp

end CFSG.SignalizerFunctorTheorem.McBride.Near.Lemma213
