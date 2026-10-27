module

public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec3.IntrThm33aAux1
public import CFSG.GroupTheory.PerfectResidualNodes

public section

open CFSG.Open

universe u

namespace CFSG.SignalizerFunctorTheorem.McBride.Near.Thm33a

open CFSG.SignalizerFunctorTheorem.McBride.Nonsolv

variable {Γ : Type u} [Group Γ] {A X Y X₁ X₂ : Subgroup Γ}

theorem commutator_self_le (K : Subgroup Γ) : ⁅K, K⁆ ≤ K :=
  Subgroup.commutator_le.mpr fun x hx y hy => by
    rw [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem hx hy) (inv_mem hx)) (inv_mem hy)

theorem normalizer_le_normalizer_commutator (K : Subgroup Γ) :
    Subgroup.normalizer (K : Set Γ) ≤ Subgroup.normalizer (⁅K, K⁆ : Subgroup Γ) := by
  have := Thm211.normalizer_le_normalizer_map_subtype (commutator ↥K)
  rwa [Subgroup.map_subtype_commutator] at this

theorem qimg_commutator {R S₁ S₂ : Subgroup Γ} (h₁ : S₁ ≤ AChief.nrm R)
    (h₂ : S₂ ≤ AChief.nrm R) :
    AChief.qimg R ⁅S₁, S₂⁆ = ⁅AChief.qimg R S₁, AChief.qimg R S₂⁆ := by
  have hle : ⁅S₁, S₂⁆ ≤ AChief.nrm R :=
    (Subgroup.commutator_mono h₁ h₂).trans (commutator_self_le _)
  have key : ⁅S₁, S₂⁆.subgroupOf (AChief.nrm R) =
      ⁅S₁.subgroupOf (AChief.nrm R), S₂.subgroupOf (AChief.nrm R)⁆ := by
    apply Subgroup.map_injective (AChief.nrm R).subtype_injective
    rw [Subgroup.map_subgroupOf_eq_of_le hle, Subgroup.map_commutator,
      Subgroup.map_subgroupOf_eq_of_le h₁, Subgroup.map_subgroupOf_eq_of_le h₂]
  unfold AChief.qimg
  rw [key, Subgroup.map_commutator]

section Pair

variable (hP : (X₁, X₂) ∈ iPairsY A X Y)

include hP

theorem pair_le_nrm : X₁ ≤ AChief.nrm X₂ :=
  le_H.trans (pair_admits_H₂ hP)

theorem not_isSolvable_qimg_pair : ¬ Group.IsSolvable ↥(AChief.qimg X₂ X₁) := by
  intro hsol
  have hX₁ := pair_le_nrm hP
  have hcomm : Admits (X₁ ⊔ cenIn X (A : Set Γ) ⊔ A) ⁅X₁, X₁⁆ :=
    (pair_admits_H hP).trans (normalizer_le_normalizer_commutator X₁)
  rcases chief_dichotomy (pair_chief hP) hcomm (commutator_self_le X₁) with h | h
  · refine absurd (fun g hg => ?_ : X₁ ≤ X₂) (not_le_of_gt (pair_lt hP))
    have hg' : g ∈ secCenIn (X₁ ⊔ cenIn X (A : Set Γ)) X₁ X₂ := by
      refine Subgroup.mem_inf.mpr ⟨Subgroup.mem_sup_left hg, ?_⟩
      rw [mem_sectionCentralizer_iff]
      exact ⟨pair_admits_H₂ hP (le_H hg), pair_admits_H hP (le_H hg),
        fun y hy => h (Subgroup.commutator_mem_commutator hg hy)⟩
    rwa [pair_secCenIn hP] at hg'
  · have hT : AChief.qimg X₂ X₁ = ⁅AChief.qimg X₂ X₁, AChief.qimg X₂ X₁⁆ := by
      conv_lhs => rw [← h]
      rw [SolQuot.qimg_sup ((commutator_self_le X₁).trans hX₁) Subgroup.le_normalizer,
        SolQuot.qimg_self, sup_bot_eq, qimg_commutator hX₁ hX₁]
    have hperf : Group.IsPerfect ↥(AChief.qimg X₂ X₁) := Subgroup.isPerfect_iff.mpr hT.symm
    have hbot : AChief.qimg X₂ X₁ = ⊥ := by
      by_contra hne
      have : Nontrivial ↥(AChief.qimg X₂ X₁) := (Subgroup.nontrivial_iff_ne_bot _).mpr hne
      exact Group.IsPerfect.not_isSolvable _ hsol
    exact absurd ((SolQuot.qimg_eq_bot_iff hX₁).mp hbot) (not_le_of_gt (pair_lt hP))

theorem qimg_eq_of_sup_eq {N : Subgroup Γ} (hN : N ≤ X₁) (h : N ⊔ X₂ = X₁) :
    AChief.qimg X₂ X₁ = AChief.qimg X₂ N := by
  conv_lhs => rw [← h]
  rw [SolQuot.qimg_sup (hN.trans (pair_le_nrm hP)) Subgroup.le_normalizer, SolQuot.qimg_self,
    sup_bot_eq]

theorem le_of_solvable {N : Subgroup Γ} (hNX₁ : N ≤ X₁)
    (hN : Admits (X₁ ⊔ cenIn X (A : Set Γ) ⊔ A) N) (hs : Group.IsSolvable N) : N ≤ X₂ := by
  rcases chief_dichotomy (pair_chief hP) hN hNX₁ with h | h
  · exact h
  · exfalso
    apply not_isSolvable_qimg_pair hP
    rw [qimg_eq_of_sup_eq hP hNX₁ h]
    exact Group.isSolvable_of_surjective (SolQuot.qres_surjective (hNX₁.trans (pair_le_nrm hP)))

theorem not_perfRes_le [Finite Γ] {B : Subgroup Γ} (hBX₁ : B ≤ X₁) (h : B ⊔ X₂ = X₁)
    (hle : perfRes B ≤ X₂) : False := by
  apply not_isSolvable_qimg_pair hP
  have hBn : B ≤ AChief.nrm X₂ := hBX₁.trans (pair_le_nrm hP)
  rw [qimg_eq_of_sup_eq hP hBX₁ h]
  obtain ⟨n, hn, -⟩ := CFSG.exists_perfectResidual_eq_derivedSeries (G := ↥B)
  have hle' : derivedSeries ↥B n ≤ X₂.subgroupOf B := by
    rw [← hn]
    exact Subgroup.map_le_iff_le_comap.mp hle
  refine ⟨n, ?_⟩
  rw [← map_derivedSeries_eq (SolQuot.qres_surjective hBn) n, Subgroup.map_eq_bot_iff,
    SolQuot.ker_qres hBn]
  exact hle'

theorem false_of_commute {M W : Subgroup Γ} (hMX₁ : M ≤ X₁) (hWX₁ : W ≤ X₁)
    (hM : M ⊔ X₂ = X₁) (hW : W ⊔ X₂ = X₁) (hc : ∀ m ∈ M, ∀ w ∈ W, Commute m w) : False := by
  apply not_isSolvable_qimg_pair hP
  refine Group.isSolvable_of_comm ?_
  rintro ⟨a, ha⟩ ⟨b, hb⟩
  rw [qimg_eq_of_sup_eq hP hMX₁ hM] at ha
  rw [qimg_eq_of_sup_eq hP hWX₁ hW] at hb
  obtain ⟨m, hm, rfl⟩ := (AChief.mem_qimg_iff X₂ M a).mp ha
  obtain ⟨w, hw, rfl⟩ := (AChief.mem_qimg_iff X₂ W b).mp hb
  apply Subtype.ext
  show AChief.qmap X₂ m * AChief.qmap X₂ w = AChief.qmap X₂ w * AChief.qmap X₂ m
  rw [← map_mul, ← map_mul]
  exact congrArg _ (Subtype.ext (hc m hm w hw).eq)

end Pair

theorem not_isSolvable_qimg_of_mem_iPairs (hP : (X₁, X₂) ∈ iPairs A X) :
    ¬ Group.IsSolvable ↥(AChief.qimg X₂ X₁) :=
  not_isSolvable_qimg_pair (Y := X₂ ⊓ cenIn X (A : Set Γ)) ⟨hP, rfl⟩

theorem not_isSolvableSection_of_mem_iPairs (hP : (X₁, X₂) ∈ iPairs A X) :
    ¬ IsSolvableSection X₁ X₂ := by
  rintro ⟨n, hn⟩
  have hX₁ : X₁ ≤ AChief.nrm X₂ :=
    pair_le_nrm (Y := X₂ ⊓ cenIn X (A : Set Γ)) (⟨hP, rfl⟩ : (X₁, X₂) ∈ iPairsY A X _)
  refine not_isSolvable_qimg_of_mem_iPairs hP ⟨n, ?_⟩
  rw [← map_derivedSeries_eq (SolQuot.qres_surjective hX₁) n, Subgroup.map_eq_bot_iff,
    SolQuot.ker_qres hX₁]
  exact hn


end CFSG.SignalizerFunctorTheorem.McBride.Near.Thm33a
