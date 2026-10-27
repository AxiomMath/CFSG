module

public import CFSG.RankThree.GF2n.Stroth80.Sec79OmegaFixed
public import CFSG.RankThree.GF2n.Stroth80.Sec79SplitOfFixed
public import CFSG.RankThree.GF2n.Stroth80.Sec5NatBridge

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG.ClassicalGroups.F2Fixed CFSG.ClassicalGroups.Orthogonal CFSG.CGT.Timmesfeld75
  QuadraticMap
open scoped commutatorElement Matrix

section Eichler

variable {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K] [Finite K] [CharP K 2]
  {Q : QuadraticForm K (ι → K)} {X : Subgroup (GL ι K)}

theorem exists_nonA2_of_map_Lom (E : ElemMatrixIso Q X) (hQ : (polarBilin Q).Nondegenerate)
    (h4 : 4 ≤ Fintype.card ι) {Y : Type*} [Group Y] (φ : Y →* GL ι K) {L : Subgroup Y}
    {u u' : ι → K} (hu' : Q u' = 0) (huu' : polar Q u u' ≠ 0)
    (hL : L.map φ = E.LomGL u') :
    ∃ y ∈ L, ∃ v : ι → K, polar Q v ((φ y : Matrix ι ι K) *ᵥ v) ≠ 0 := by
  have hu'0 : u' ≠ 0 := by
    rintro rfl
    exact huu' (by simp)
  obtain ⟨w, hw1, hw2⟩ := exists_nonsingular_perp hQ (by simpa using h4) hu'0
  set g : Gom Q := eichlerG Q u' w with hg
  set A : X := E.equiv.symm g with hA
  have hAapp : ∀ v : ι → K, ((A : GL ι K) : Matrix ι ι K) *ᵥ v = g.app v := by
    intro v
    rw [← E.app A v, hA, MulEquiv.apply_symm_apply]
  have hAmem : (A : GL ι K) ∈ E.LomGL u' := by
    unfold ElemMatrixIso.LomGL
    rw [mem_matrixOf_iff]
    refine ⟨A.2, ?_⟩
    have h1 : E.equiv ⟨(A : GL ι K), A.2⟩ = g := by
      rw [hA]
      exact MulEquiv.apply_symm_apply E.equiv g
    rw [h1]
    exact eichlerG_mem_Lom hw1
  rw [← hL] at hAmem
  obtain ⟨y, hy, hyA⟩ := Subgroup.mem_map.mp hAmem
  refine ⟨y, hy, u, ?_⟩
  rw [hyA, hAapp]
  have h2 : g.app u = eichler Q u' w u := rfl
  rw [h2, polar_apply_eichler_self hu' hw1, CharTwo.two_eq_zero, zero_mul, zero_sub]
  exact neg_ne_zero.mpr (mul_ne_zero hw2 (pow_ne_zero 2 huu'))

end Eichler

section Split

variable {G : Type} [Group G] [Finite G] {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
  [Finite K] [CharP K 2] {Q : QuadraticForm K (ι → K)} {X : Subgroup (GL ι K)}
  {R N P I L₁ L₂ A₁ A₂ A : Subgroup G}

theorem sec79_split_of_hom (E : ElemMatrixIso Q X) (hQ : (polarBilin Q).Nondegenerate)
    (h4 : 4 ≤ Fintype.card ι) (φ : ↥R →* GL ι K) (hφ : φ.range = X)
    (hNφ : φ.ker = N.subgroupOf R)
    (hP : ∀ r ∈ R, ∀ x ∈ P, r * x * r⁻¹ ∈ P) (hI : ∀ r ∈ R, ∀ x ∈ I, r * x * r⁻¹ ∈ I)
    (hN : ∀ n ∈ N, ∀ y ∈ P, ⁅n, y⁆ ∈ I) (hd : IsOppDecomp P I L₁ L₂ A₁ A₂) (h₁ : L₁ ≤ R)
    (h₂ : L₂ ≤ R) {u u' : ι → K} (hu : Q u = 0) (hu' : Q u' = 0) (huu' : polar Q u u' ≠ 0)
    (hL₁ : (L₁.subgroupOf R).map φ = E.LomGL u) (hL₂ : (L₂.subgroupOf R).map φ = E.LomGL u')
    (hIA : I ≤ A) (hAP : A ≤ P) (hA : ∀ r ∈ R, conjSubgroup r A = A) :
    A ≤ (A ⊓ A₁) ⊔ (A ⊓ A₂) := by
  classical
  have hsec := SecHyp.of_isOppDecomp hd hP hI
  obtain ⟨M, iM, iA, κ, hκ, hker⟩ := exists_sectionModule_ker hNφ hsec hN
  haveI : Finite M := hκ.finite
  have hdec := isCompl_fixedSub_of_isOppDecomp hP hκ hd h₁ h₂
  have hdec' := hdec.symm
  have huu'' : polar Q u' u ≠ 0 := by rwa [polar_comm]
  obtain ⟨y, hy, hny⟩ := exists_nonA2_of_map_Lom E hQ h4 φ hu' huu' hL₂
  obtain ⟨x, hx, hnx⟩ := exists_nonA2_of_map_Lom E hQ h4 φ hu huu'' hL₁
  obtain ⟨hy1, hy2, -⟩ := stroth_2_1_ii_omega_fixed_of_hom E φ hφ hQ hκ.two hker hu hu' huu' hL₁
    hL₂ hdec h4 hy hny
  obtain ⟨hx1, hx2, -⟩ := stroth_2_1_ii_omega_fixed_of_hom E φ hφ hQ hκ.two hker hu' hu huu'' hL₂
    hL₁ hdec' h4 hx hnx
  set C₁ := fixedSub M ((L₁.subgroupOf R : Subgroup ↥R) : Set ↥R) with hC₁
  set C₂ := fixedSub M ((L₂.subgroupOf R : Subgroup ↥R) : Set ↥R) with hC₂
  have hinv : ∀ r : ↥R, ∀ a ∈ secSub κ A, r • a ∈ secSub κ A := by
    intro r a ha
    have h1 := secSub_conjSubgroup hP hκ r A
    rw [hA r r.2] at h1
    rw [h1]
    exact AddSubgroup.mem_map.mpr ⟨a, ha, rfl⟩
  have hsplit := splitOfFixed_holds M C₁ C₂ (secSub κ A) hdec (comm M x) (comm M y)
    (by rw [ker_comm]; exact hx1) hx2 (by rw [ker_comm]; exact hy1) hy2 (by
      intro a ha
      refine ⟨?_, ?_⟩
      · rw [comm_apply]
        exact AddSubgroup.sub_mem _ (hinv x a ha) ha
      · rw [comm_apply]
        exact AddSubgroup.sub_mem _ (hinv y a ha) ha)
  obtain ⟨e₁, e₂⟩ := fixedSub_eq_secSub_of_isOppDecomp hP hκ hd h₁ h₂
  obtain ⟨hIA₁, hA₁P, hIA₂, hA₂P, -⟩ := hd
  have hsplit' : secSub κ A = secSub κ ((A ⊓ A₁) ⊔ (A ⊓ A₂)) := by
    rw [secSub_sup (inf_le_left.trans hAP) (inf_le_left.trans hAP), secSub_inf hκ hIA,
      secSub_inf hκ hIA]
    rw [hC₁, hC₂, e₁, e₂] at hsplit
    exact hsplit
  have hIV : I ≤ (A ⊓ A₁) ⊔ (A ⊓ A₂) := le_sup_of_le_left (le_inf hIA hIA₁)
  exact (secSub_le_secSub_iff hκ hAP hIV).mp hsplit'.le

end Split

end CFSG.RankThree.GF2n.Stroth80
