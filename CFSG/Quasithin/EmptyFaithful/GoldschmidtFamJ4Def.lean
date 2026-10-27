module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtJ4LocTransport
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtFamJ4Red
public import CFSG.Quasithin.EmptyFaithful.ModHJ4Odd
public import CFSG.Quasithin.Background.A312SporGen

public section

namespace CFSG.Quasithin.J4Fam

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Blueprint
open CFSG.Sporadic.J4 CFSG.Sporadic.J4.QT CFSG.Quasithin.J4Loc

@[expose] def J4OvergroupLocal : Prop :=
  ∀ Y : Subgroup J, P0 ≤ Y → Y ≠ ⊤ → ¬ Group.IsSolvable ↥Y →
    Y ≤ Hj ∨ Y ≤ Subgroup.centralizer ({z0} : Set J) ∨ Y ≤ Subgroup.normalizer (V0 : Set J)

@[expose] def J4Case (M : Subgroup J) : Prop :=
  ∀ B : Subgroup J, B ∈ lFamily P0 → B ⊔ P0 ≤ M → J4Shape ↥B

section Certs


theorem overgroup_of_solvable {Y : Subgroup J} (hY : P0 ≤ Y) (hs : Group.IsSolvable ↥Y) :
    Y ≤ Hj ∨ Y ≤ Subgroup.centralizer ({z0} : Set J) ∨ Y ≤ Subgroup.normalizer (V0 : Set J) := by
  have hF : J4Facts := j4Facts
  have h := CFSG.Quasithin.ModH.J4.solvableOverSylow_j4 J
  have e : Nonempty (J ≃* NativeSporadic.Carrier .J4) := ⟨(seedEquiv hF.mat).symm⟩
  obtain ⟨N, hN, hne, hYN⟩ := h e P0 isSylowTwoOf_P0 Y hs hY
  have hNY : ∀ y ∈ Y, ∀ x ∈ N, y * x * y⁻¹ ∈ N := by
    intro y hy x hx
    have h1 := hYN hy
    rw [Subgroup.mem_normalizer_iff] at h1
    exact (h1 x).1 hx
  exact overgroup_of_normal_two_subgroup j4TwoLocalOvergroups hY hN hne hNY

theorem j4OvergroupLocal_of_normalizes
    (h : ∀ Y : Subgroup J, P0 ≤ Y → Y ≠ ⊤ → ¬ Group.IsSolvable ↥Y →
      ∃ N : Subgroup J, IsPGroup 2 ↥N ∧ N ≠ ⊥ ∧ ∀ y ∈ Y, ∀ x ∈ N, y * x * y⁻¹ ∈ N) :
    J4OvergroupLocal := by
  intro Y hY htop hns
  obtain ⟨N, hN, hne, hYN⟩ := h Y hY htop hns
  exact overgroup_of_normal_two_subgroup j4TwoLocalOvergroups hY hN hne hYN

end Certs

section Assembly

open CFSG.QuasithinUnique.Vol2Native.A312L


theorem sup_ne_top {B : Subgroup J} (hq : CFSG.IsQuasisimple J) (hB : B ∈ lFamily P0)
    (hBtop : B ≠ ⊤) : B ⊔ P0 ≠ ⊤ := by
  intro htop
  have hB' : B ∈ cComp (B ⊔ P0) := hB
  rw [htop] at hB'
  exact hBtop (A321.cComp_eq_top_of_quasisimple hq hB')

theorem a312Case_of_cases (hO : J4OvergroupLocal) (hHj : J4Case Hj)
    (hM2 : J4Case (Subgroup.centralizer ({z0} : Set J)))
    (hM3 : J4Case (Subgroup.normalizer (V0 : Set J))) (hq : CFSG.IsQuasisimple J)
    {B : Subgroup J} (hB : B ∈ lFamily P0) (hBtop : B ≠ ⊤) : A312Case B ⊤ := by
  have hF : J4Facts := j4Facts
  have hYtop := sup_ne_top hq hB hBtop
  have hns := A312S.not_isSolvable_sup hB
  have hshape : J4Shape ↥B := by
    rcases hO _ le_sup_right hYtop hns with h | h | h
    · exact hHj B hB h
    · exact hM2 B hB h
    · exact hM3 B hB h
  have hJ4 : IsSporadic .J4 ↥(⊤ : Subgroup J) :=
    ⟨Subgroup.topEquiv.trans (seedEquiv hF.mat).symm⟩
  iterate 15 right
  left
  exact ⟨hJ4, hshape⟩

theorem famJ4_of_cases (hO : J4OvergroupLocal) (hHj : J4Case Hj)
    (hM2 : J4Case (Subgroup.centralizer ({z0} : Set J)))
    (hM3 : J4Case (Subgroup.normalizer (V0 : Set J))) : FamJ4 := by
  intro X _ _ hq hX
  obtain ⟨e⟩ := hX
  have hF : J4Facts := j4Facts
  have e' : X ≃* J := e.trans (seedEquiv hF.mat)
  have hqJ : CFSG.IsQuasisimple J := CFSG.LocalCores.isQuasisimple_of_mulEquiv e' hq
  have hJ : A312For J := by
    refine A312For.of_sylow P0 isSylowTwoOf_P0 ?_
    intro B hB hBtop
    exact a312Case_of_cases hO hHj hM2 hM3 hqJ hB hBtop
  exact A312For.of_mulEquiv (X := X) (Y := J) e' hJ

end Assembly

end CFSG.Quasithin.J4Fam
