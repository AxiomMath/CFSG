module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive.Invol.ExcTwistRoot
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive.Invol.ExcTwistTheta

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.LieType.Chevalley.ToralSign
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  (rootChar rootChar_nsmul_single rootDiagUnit)

private def i0 : Fin TwistTag.E6.tag.rank := ⟨0, by decide⟩
private def i1 : Fin TwistTag.E6.tag.rank := ⟨1, by decide⟩
private def i2 : Fin TwistTag.E6.tag.rank := ⟨2, by decide⟩
private def i3 : Fin TwistTag.E6.tag.rank := ⟨3, by decide⟩
private def i4 : Fin TwistTag.E6.tag.rank := ⟨4, by decide⟩
private def i5 : Fin TwistTag.E6.tag.rank := ⟨5, by decide⟩

private abbrev e6 (i : Fin TwistTag.E6.tag.rank) : Fin TwistTag.E6.tag.rank → ℤ := Pi.single i 1


private theorem pinnedX_commute_E6 {k : Type} [Field k] {γ δ : Fin TwistTag.E6.tag.rank → ℤ}
    (hγ : IsRoot TwistTag.E6.tag γ) (hδ : IsRoot TwistTag.E6.tag δ) (hne : γ ≠ δ) (hne' : γ ≠ -δ)
    (h : ¬ IsRoot TwistTag.E6.tag (γ + δ)) (c d : k) :
    Commute (pinnedX TwistTag.E6.tag k γ c) (pinnedX TwistTag.E6.tag k δ d) :=
  (simply_laced_root_commutator_unit TwistTag.E6.tag (Or.inr (Or.inl rfl))
    hγ hδ hne hne').2 h k (pinnedX TwistTag.E6.tag k γ c) (Subgroup.subset_closure ⟨c, rfl⟩)
    (pinnedX TwistTag.E6.tag k δ d) (Subgroup.subset_closure ⟨d, rfl⟩)

private lemma pinnedX_mul_eq_one_left {k : Type} [Field k] {γ δ : Fin TwistTag.E6.tag.rank → ℤ}
    (hγ : IsRoot TwistTag.E6.tag γ) (hδ : IsRoot TwistTag.E6.tag δ) (hne : γ ≠ δ)
    (hposγ : 0 < height γ) (hposδ : 0 < height δ) (n n' : ℤ) (hn : (n : k) ≠ 0) (c d : k)
    (hcd : pinnedX TwistTag.E6.tag k γ ((n : k) * c) *
      pinnedX TwistTag.E6.tag k δ ((n' : k) * d) = 1) : c = 0 := by
  have hL : [γ, δ].Nodup := by simp [hne]
  have hroots : ∀ ρ ∈ [γ, δ], IsRoot TwistTag.E6.tag ρ ∧ 0 < height ρ := by
    intro ρ hρ
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hρ
    rcases hρ with rfl | rfl
    · exact ⟨hγ, hposγ⟩
    · exact ⟨hδ, hposδ⟩
  have heq : ([γ, δ].map fun ρ =>
        pinnedX TwistTag.E6.tag k ρ (if ρ = γ then (n : k) * c else (n' : k) * d)).prod =
      ([γ, δ].map fun ρ => pinnedX TwistTag.E6.tag k ρ (0 : k)).prod := by
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
      if_neg (Ne.symm hne), pinnedX_zero, mul_one]
    exact hcd
  have hkey := pinnedX_list_prod_injective (τ := TwistTag.E6.tag) (R := k) [γ, δ] hL hroots
    (fun ρ => if ρ = γ then (n : k) * c else (n' : k) * d) (fun _ => 0) heq
  have hnc : (n : k) * c = 0 := by simpa using hkey γ (by simp)
  exact (mul_eq_zero.1 hnc).resolve_left hn

theorem exists_inv_good_E6tw_graph {K k : Type} [Field K] [Finite K] [Field k] [IsAlgClosed k]
    (ι : K →+* k) {p e : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) [CharP K p] [CharP k p]
    (hK : Nat.card K = p ^ e) (h3 : 3 < p ^ e) :
    ∃ u : fixedPointsIn (adjointGroup TwistTag.E6.tag k)
        (frobTwistGL TwistTag.E6.tag k p e (diagramMap TwistTag.E6 k)),
      orderOf u = p ∧ IsSpecialGood p u ∧
      diagramMap TwistTag.E6 k * (u : ModGL TwistTag.E6.tag k) * (diagramMap TwistTag.E6 k)⁻¹ =
        (u : ModGL TwistTag.E6.tag k)⁻¹ := by
  classical
  have hp : p.Prime := Fact.out
  have hQ0c : ∀ c : k, diagramMap TwistTag.E6 k * pinnedX TwistTag.E6.tag k (e6 i0) c *
      (diagramMap TwistTag.E6 k)⁻¹ = pinnedX TwistTag.E6.tag k (e6 i5) c := by
    intro c
    have h := diagramMap_conj_pinnedX_single TwistTag.E6 i0 c
    rw [show TwistTag.E6.perm i0 = i5 from by decide] at h
    simpa using h
  have hQ5c : ∀ c : k, diagramMap TwistTag.E6 k * pinnedX TwistTag.E6.tag k (e6 i5) c *
      (diagramMap TwistTag.E6 k)⁻¹ = pinnedX TwistTag.E6.tag k (e6 i0) c := by
    intro c
    have h := diagramMap_conj_pinnedX_single TwistTag.E6 i5 c
    rw [show TwistTag.E6.perm i5 = i0 from by decide] at h
    simpa using h
  have hQ2c : ∀ c : k, diagramMap TwistTag.E6 k * pinnedX TwistTag.E6.tag k (e6 i2) c *
      (diagramMap TwistTag.E6 k)⁻¹ = pinnedX TwistTag.E6.tag k (e6 i4) c := by
    intro c
    have h := diagramMap_conj_pinnedX_single TwistTag.E6 i2 c
    rw [show TwistTag.E6.perm i2 = i4 from by decide] at h
    simpa using h
  have hQ4c : ∀ c : k, diagramMap TwistTag.E6 k * pinnedX TwistTag.E6.tag k (e6 i4) c *
      (diagramMap TwistTag.E6 k)⁻¹ = pinnedX TwistTag.E6.tag k (e6 i2) c := by
    intro c
    have h := diagramMap_conj_pinnedX_single TwistTag.E6 i4 c
    rw [show TwistTag.E6.perm i4 = i2 from by decide] at h
    simpa using h
  have hQ0 : ∀ c : k, diagramMap TwistTag.E6 k * pinnedX TwistTag.E6.tag k (e6 i0) c *
      (diagramMap TwistTag.E6 k)⁻¹ = pinnedX TwistTag.E6.tag k (e6 i5) (1 * c) :=
    fun c => by simpa using hQ0c c
  have hQ5 : ∀ c : k, diagramMap TwistTag.E6 k * pinnedX TwistTag.E6.tag k (e6 i5) c *
      (diagramMap TwistTag.E6 k)⁻¹ = pinnedX TwistTag.E6.tag k (e6 i0) (1 * c) :=
    fun c => by simpa using hQ5c c
  have hQ2 : ∀ c : k, diagramMap TwistTag.E6 k * pinnedX TwistTag.E6.tag k (e6 i2) c *
      (diagramMap TwistTag.E6 k)⁻¹ = pinnedX TwistTag.E6.tag k (e6 i4) (1 * c) :=
    fun c => by simpa using hQ2c c
  have hQ4 : ∀ c : k, diagramMap TwistTag.E6 k * pinnedX TwistTag.E6.tag k (e6 i4) c *
      (diagramMap TwistTag.E6 k)⁻¹ = pinnedX TwistTag.E6.tag k (e6 i2) (1 * c) :=
    fun c => by simpa using hQ4c c
  have hpos : 0 < p ^ e - 1 := by omega
  obtain ⟨mu, hmu⟩ := IsAlgClosed.exists_pow_nat_eq (-1 : k) hpos
  have hmu0 : mu ≠ 0 := by
    rintro rfl
    rw [zero_pow hpos.ne'] at hmu
    exact one_ne_zero (neg_eq_zero.mp hmu.symm)
  have hq_odd : Odd (p ^ e) := (hp.odd_of_ne_two hp2).pow
  have hmu_q : mu ^ p ^ e = -mu := by
    rw [show p ^ e = (p ^ e - 1) + 1 by omega, pow_succ, hmu]
    ring
  have hmu_qq : (mu ^ p ^ e) ^ p ^ e = mu * (1 * 1) := by
    rw [hmu_q, hq_odd.neg_pow, hmu_q, neg_neg]
    ring
  have h2 : IsRoot TwistTag.E6.tag (e6 i2) := isRoot_iff_mem_artifactRoots.2 (by decide)
  have h0 : IsRoot TwistTag.E6.tag (e6 i0) := isRoot_iff_mem_artifactRoots.2 (by decide)
  have h4 : IsRoot TwistTag.E6.tag (e6 i4) := isRoot_iff_mem_artifactRoots.2 (by decide)
  have h5 : IsRoot TwistTag.E6.tag (e6 i5) := isRoot_iff_mem_artifactRoots.2 (by decide)
  have h20 : e6 i2 ≠ e6 i0 ∧ e6 i2 ≠ -e6 i0 ∧ IsRoot TwistTag.E6.tag (e6 i2 + e6 i0) :=
    ⟨by decide, by decide, isRoot_iff_mem_artifactRoots.2 (by decide)⟩
  have h45 : e6 i4 ≠ e6 i5 ∧ e6 i4 ≠ -e6 i5 ∧ IsRoot TwistTag.E6.tag (e6 i4 + e6 i5) :=
    ⟨by decide, by decide, isRoot_iff_mem_artifactRoots.2 (by decide)⟩
  have hcf := (simply_laced_root_commutator_unit TwistTag.E6.tag (Or.inr (Or.inl rfl))
    h2 h0 h20.1 h20.2.1).1 h20.2.2
  have hcf' := (simply_laced_root_commutator_unit TwistTag.E6.tag (Or.inr (Or.inl rfl))
    h4 h5 h45.1 h45.2.1).1 h45.2.2
  have hAA' : RootsCommute TwistTag.E6.tag (e6 i2) (e6 i4) :=
    rootsCommute_of_list (by decide) (by decide) (by decide)
  have hBB' : RootsCommute TwistTag.E6.tag (e6 i0) (e6 i5) :=
    rootsCommute_of_list (by decide) (by decide) (by decide)
  have hAB' : RootsCommute TwistTag.E6.tag (e6 i2) (e6 i5) :=
    rootsCommute_of_list (by decide) (by decide) (by decide)
  have hA'B : RootsCommute TwistTag.E6.tag (e6 i4) (e6 i0) :=
    rootsCommute_of_list (by decide) (by decide) (by decide)
  have hzz : RootsCommute TwistTag.E6.tag (e6 i2 + e6 i0) (e6 i4 + e6 i5) :=
    rootsCommute_of_list (by decide) (by decide) (by decide)
  have hzA : RootsCommute TwistTag.E6.tag (e6 i2 + e6 i0) (e6 i2) :=
    rootsCommute_of_list (by decide) (by decide) (by decide)
  have hzA' : RootsCommute TwistTag.E6.tag (e6 i2 + e6 i0) (e6 i4) :=
    rootsCommute_of_list (by decide) (by decide) (by decide)
  have hzB : RootsCommute TwistTag.E6.tag (e6 i2 + e6 i0) (e6 i0) :=
    rootsCommute_of_list (by decide) (by decide) (by decide)
  have hzB' : RootsCommute TwistTag.E6.tag (e6 i2 + e6 i0) (e6 i5) :=
    rootsCommute_of_list (by decide) (by decide) (by decide)
  have hzA2 : RootsCommute TwistTag.E6.tag (e6 i4 + e6 i5) (e6 i2) :=
    rootsCommute_of_list (by decide) (by decide) (by decide)
  have hzA2' : RootsCommute TwistTag.E6.tag (e6 i4 + e6 i5) (e6 i4) :=
    rootsCommute_of_list (by decide) (by decide) (by decide)
  have hzB2 : RootsCommute TwistTag.E6.tag (e6 i4 + e6 i5) (e6 i0) :=
    rootsCommute_of_list (by decide) (by decide) (by decide)
  have hzB2' : RootsCommute TwistTag.E6.tag (e6 i4 + e6 i5) (e6 i5) :=
    rootsCommute_of_list (by decide) (by decide) (by decide)
  have hposh : 0 < height (e6 i2 + e6 i0) ∧ 0 < height (e6 i4 + e6 i5) :=
    ⟨by decide, by decide⟩
  have hCinj : ∀ c d : k,
      (fun r => pinnedX TwistTag.E6.tag k (e6 i2 + e6 i0)
        ((commConst TwistTag.E6.tag (e6 i2) (e6 i0) (1, 1) : k) * r)) c *
      (fun r => pinnedX TwistTag.E6.tag k (e6 i4 + e6 i5)
        ((commConst TwistTag.E6.tag (e6 i4) (e6 i5) (1, 1) : k) * r)) d = 1 →
      c = 0 := by
    intro c d hcd
    have hn0 : (commConst TwistTag.E6.tag (e6 i2) (e6 i0) (1, 1) : k) ≠ 0 := by
      rcases hcf.1 with h | h <;> simp [h]
    exact pinnedX_mul_eq_one_left h20.2.2 h45.2.2 hzz.1 hposh.1 hposh.2
      (commConst TwistTag.E6.tag (e6 i2) (e6 i0) (1, 1))
      (commConst TwistTag.E6.tag (e6 i4) (e6 i5) (1, 1)) hn0 c d hcd
  obtain ⟨u, huval, huord, hugood⟩ :=
    exists_pair_heis_good_of_mu (adjointGroup TwistTag.E6.tag k)
      (frobTwistGL TwistTag.E6.tag k p e (diagramMap TwistTag.E6 k)) ι hp hp2 hK h3
      (A := fun c => pinnedX TwistTag.E6.tag k (e6 i2) c)
      (A' := fun c => pinnedX TwistTag.E6.tag k (e6 i4) c)
      (B := fun c => pinnedX TwistTag.E6.tag k (e6 i0) c)
      (B' := fun c => pinnedX TwistTag.E6.tag k (e6 i5) c)
      (C := fun r => pinnedX TwistTag.E6.tag k (e6 i2 + e6 i0)
        ((commConst TwistTag.E6.tag (e6 i2) (e6 i0) (1, 1) : k) * r))
      (C' := fun r => pinnedX TwistTag.E6.tag k (e6 i4 + e6 i5)
        ((commConst TwistTag.E6.tag (e6 i4) (e6 i5) (1, 1) : k) * r))
      (hA := pinnedX_add TwistTag.E6.tag k (e6 i2))
      (hA' := pinnedX_add TwistTag.E6.tag k (e6 i4))
      (hB := pinnedX_add TwistTag.E6.tag k (e6 i0))
      (hB' := pinnedX_add TwistTag.E6.tag k (e6 i5))
      (hC := fun c d => by rw [mul_add, pinnedX_add])
      (hC' := fun c d => by rw [mul_add, pinnedX_add])
      (hAX := fun c => pinnedX_mem_adjointGroup (e6 i2) c)
      (hA'X := fun c => pinnedX_mem_adjointGroup (e6 i4) c)
      (hBX := fun c => pinnedX_mem_adjointGroup (e6 i0) c)
      (hB'X := fun c => pinnedX_mem_adjointGroup (e6 i5) c)
      (sa := 1) (sa' := 1) (sb := 1) (sb' := 1)
      (hsa := one_mul 1) (hsa' := one_mul 1) (hsb := one_mul 1) (hsb' := one_mul 1)
      (hSA := fun c => frobTwistGL_pinnedX p e (diagramMap TwistTag.E6 k) hQ2 c)
      (hSA' := fun c => frobTwistGL_pinnedX p e (diagramMap TwistTag.E6 k) hQ4 c)
      (hSB := fun c => frobTwistGL_pinnedX p e (diagramMap TwistTag.E6 k) hQ0 c)
      (hSB' := fun c => frobTwistGL_pinnedX p e (diagramMap TwistTag.E6 k) hQ5 c)
      (hAA' := fun c d => pinnedX_commute_E6 h2 h4 hAA'.1 hAA'.2.1 hAA'.2.2 c d)
      (hBB' := fun c d => pinnedX_commute_E6 h0 h5 hBB'.1 hBB'.2.1 hBB'.2.2 c d)
      (hAB' := fun c d => pinnedX_commute_E6 h2 h5 hAB'.1 hAB'.2.1 hAB'.2.2 c d)
      (hA'B := fun c d => pinnedX_commute_E6 h4 h0 hA'B.1 hA'B.2.1 hA'B.2.2 c d)
      (hAB := fun c d => by rw [hcf.2 k c d, mul_assoc])
      (hA'B' := fun c d => by rw [hcf'.2 k c d, mul_assoc])
      (hCA := fun c d => pinnedX_commute_E6 h20.2.2 h2 hzA.1 hzA.2.1 hzA.2.2
        ((commConst TwistTag.E6.tag (e6 i2) (e6 i0) (1, 1) : k) * c) d)
      (hCA' := fun c d => pinnedX_commute_E6 h20.2.2 h4 hzA'.1 hzA'.2.1 hzA'.2.2
        ((commConst TwistTag.E6.tag (e6 i2) (e6 i0) (1, 1) : k) * c) d)
      (hCB := fun c d => pinnedX_commute_E6 h20.2.2 h0 hzB.1 hzB.2.1 hzB.2.2
        ((commConst TwistTag.E6.tag (e6 i2) (e6 i0) (1, 1) : k) * c) d)
      (hCB' := fun c d => pinnedX_commute_E6 h20.2.2 h5 hzB'.1 hzB'.2.1 hzB'.2.2
        ((commConst TwistTag.E6.tag (e6 i2) (e6 i0) (1, 1) : k) * c) d)
      (hC'A := fun c d => pinnedX_commute_E6 h45.2.2 h2 hzA2.1 hzA2.2.1 hzA2.2.2
        ((commConst TwistTag.E6.tag (e6 i4) (e6 i5) (1, 1) : k) * c) d)
      (hC'A' := fun c d => pinnedX_commute_E6 h45.2.2 h4 hzA2'.1 hzA2'.2.1 hzA2'.2.2
        ((commConst TwistTag.E6.tag (e6 i4) (e6 i5) (1, 1) : k) * c) d)
      (hC'B := fun c d => pinnedX_commute_E6 h45.2.2 h0 hzB2.1 hzB2.2.1 hzB2.2.2
        ((commConst TwistTag.E6.tag (e6 i4) (e6 i5) (1, 1) : k) * c) d)
      (hC'B' := fun c d => pinnedX_commute_E6 h45.2.2 h5 hzB2'.1 hzB2'.2.1 hzB2'.2.2
        ((commConst TwistTag.E6.tag (e6 i4) (e6 i5) (1, 1) : k) * c) d)
      (hCC' := fun c d => pinnedX_commute_E6 h20.2.2 h45.2.2 hzz.1 hzz.2.1 hzz.2.2
        ((commConst TwistTag.E6.tag (e6 i2) (e6 i0) (1, 1) : k) * c)
        ((commConst TwistTag.E6.tag (e6 i4) (e6 i5) (1, 1) : k) * d))
      (hCinj := hCinj) (hmu0 := hmu0) (hmu := hmu_qq)
  refine ⟨u, huord, hugood, ?_⟩
  have huval' : (u : ModGL TwistTag.E6.tag k) =
      pinnedX TwistTag.E6.tag k (e6 i0) mu * pinnedX TwistTag.E6.tag k (e6 i5) (-mu) := by
    rw [huval, hmu_q, one_mul]
  rw [huval']
  calc diagramMap TwistTag.E6 k *
        (pinnedX TwistTag.E6.tag k (e6 i0) mu * pinnedX TwistTag.E6.tag k (e6 i5) (-mu)) *
        (diagramMap TwistTag.E6 k)⁻¹
      = (diagramMap TwistTag.E6 k * pinnedX TwistTag.E6.tag k (e6 i0) mu *
            (diagramMap TwistTag.E6 k)⁻¹) *
          (diagramMap TwistTag.E6 k * pinnedX TwistTag.E6.tag k (e6 i5) (-mu) *
            (diagramMap TwistTag.E6 k)⁻¹) := by group
    _ = pinnedX TwistTag.E6.tag k (e6 i5) mu * pinnedX TwistTag.E6.tag k (e6 i0) (-mu) := by
        rw [hQ0c mu, hQ5c (-mu)]
    _ = (pinnedX TwistTag.E6.tag k (e6 i0) mu *
          pinnedX TwistTag.E6.tag k (e6 i5) (-mu))⁻¹ := by
        rw [mul_inv_rev, pinnedX_neg, pinnedX_neg, neg_neg]

theorem exists_inv_good_E6tw_graph_diag {K k : Type} [Field K] [Finite K] [Field k]
    [IsAlgClosed k] (ι : K →+* k) {p e : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) [CharP K p] [CharP k p]
    (hK : Nat.card K = p ^ e) (h3 : 3 < p ^ e) :
    ∃ u : fixedPointsIn (adjointGroup TwistTag.E6.tag k)
        (frobTwistGL TwistTag.E6.tag k p e (diagramMap TwistTag.E6 k)),
      orderOf u = p ∧ IsSpecialGood p u ∧
      (rootDiagUnit TwistTag.E6.tag ![1, -1, 1, 1, 1, 1] * diagramMap TwistTag.E6 k) *
          (u : ModGL TwistTag.E6.tag k) *
          (rootDiagUnit TwistTag.E6.tag ![1, -1, 1, 1, 1, 1] * diagramMap TwistTag.E6 k)⁻¹ =
        (u : ModGL TwistTag.E6.tag k)⁻¹ := by
  classical
  have hp : p.Prime := Fact.out
  have hα : IsRoot TwistTag.E6.tag (e6 i3) := isRoot_iff_mem_artifactRoots.2 (by decide)
  have hβ : IsRoot TwistTag.E6.tag (e6 i1) := isRoot_iff_mem_artifactRoots.2 (by decide)
  have hαβ : e6 i3 ≠ e6 i1 ∧ e6 i3 ≠ -e6 i1 ∧
      IsRoot TwistTag.E6.tag (e6 i3 + e6 i1) :=
    ⟨by decide, by decide, isRoot_iff_mem_artifactRoots.2 (by decide)⟩
  have hzα : RootsCommute TwistTag.E6.tag (e6 i3 + e6 i1) (e6 i3) :=
    rootsCommute_of_list (by decide) (by decide) (by decide)
  have hzβ : RootsCommute TwistTag.E6.tag (e6 i3 + e6 i1) (e6 i1) :=
    rootsCommute_of_list (by decide) (by decide) (by decide)
  have hQα : ∃ s : k, s * s = 1 ∧ ∀ c : k,
      diagramMap TwistTag.E6 k * pinnedX TwistTag.E6.tag k (e6 i3) c *
        (diagramMap TwistTag.E6 k)⁻¹ = pinnedX TwistTag.E6.tag k (e6 i3) (s * c) := by
    refine ⟨1, one_mul 1, fun c => ?_⟩
    rw [one_mul]
    have h := diagramMap_conj_pinnedX_single TwistTag.E6 i3 c
    rw [show TwistTag.E6.perm i3 = i3 from by decide] at h
    simpa using h
  have hQβ : ∃ s : k, s * s = 1 ∧ ∀ c : k,
      diagramMap TwistTag.E6 k * pinnedX TwistTag.E6.tag k (e6 i1) c *
        (diagramMap TwistTag.E6 k)⁻¹ = pinnedX TwistTag.E6.tag k (e6 i1) (s * c) := by
    refine ⟨1, one_mul 1, fun c => ?_⟩
    rw [one_mul]
    have h := diagramMap_conj_pinnedX_single TwistTag.E6 i1 c
    rw [show TwistTag.E6.perm i1 = i1 from by decide] at h
    simpa using h
  have htB : ∀ c : k,
      (rootDiagUnit TwistTag.E6.tag ![1, -1, 1, 1, 1, 1] * diagramMap TwistTag.E6 k) *
          pinnedX TwistTag.E6.tag k (e6 i1) c *
          (rootDiagUnit TwistTag.E6.tag ![1, -1, 1, 1, 1, 1] * diagramMap TwistTag.E6 k)⁻¹ =
        pinnedX TwistTag.E6.tag k (e6 i1) (-c) := by
    intro c
    have hP : diagramMap TwistTag.E6 k * pinnedX TwistTag.E6.tag k (e6 i1) c *
        (diagramMap TwistTag.E6 k)⁻¹ = pinnedX TwistTag.E6.tag k (e6 i1) c := by
      have h := diagramMap_conj_pinnedX_single TwistTag.E6 i1 c
      rw [show TwistTag.E6.perm i1 = i1 from by decide] at h
      simpa using h
    have hb : rootChar (τ := TwistTag.E6.tag)
        (![1, -1, 1, 1, 1, 1] : Fin TwistTag.E6.tag.rank → kˣ) (e6 i1) = -1 := by
      have h := rootChar_nsmul_single (τ := TwistTag.E6.tag) (K := k)
        (![1, -1, 1, 1, 1, 1] : Fin TwistTag.E6.tag.rank → kˣ) i1 1
      simp only [one_smul, pow_one] at h
      rw [h]
      rfl
    calc (rootDiagUnit TwistTag.E6.tag ![1, -1, 1, 1, 1, 1] * diagramMap TwistTag.E6 k) *
          pinnedX TwistTag.E6.tag k (e6 i1) c *
          (rootDiagUnit TwistTag.E6.tag ![1, -1, 1, 1, 1, 1] * diagramMap TwistTag.E6 k)⁻¹
        = rootDiagUnit TwistTag.E6.tag ![1, -1, 1, 1, 1, 1] *
            (diagramMap TwistTag.E6 k * pinnedX TwistTag.E6.tag k (e6 i1) c *
              (diagramMap TwistTag.E6 k)⁻¹) *
            (rootDiagUnit TwistTag.E6.tag ![1, -1, 1, 1, 1, 1])⁻¹ := by group
      _ = rootDiagUnit TwistTag.E6.tag ![1, -1, 1, 1, 1, 1] *
            pinnedX TwistTag.E6.tag k (e6 i1) c *
            (rootDiagUnit TwistTag.E6.tag ![1, -1, 1, 1, 1, 1])⁻¹ := by rw [hP]
      _ = pinnedX TwistTag.E6.tag k (e6 i1)
            ((rootChar (τ := TwistTag.E6.tag)
              (![1, -1, 1, 1, 1, 1] : Fin TwistTag.E6.tag.rank → kˣ) (e6 i1) : k) * c) :=
          rootDiagUnit_conj_pinnedX _ hβ c
      _ = pinnedX TwistTag.E6.tag k (e6 i1) (-c) := by
          rw [hb]
          simp
  obtain ⟨u, huord, hugood, hinv⟩ :=
    exists_twist_fixed_inv_good (τ := .E6) (hτ := Or.inr (Or.inl rfl)) (K := K) (k := k)
      (ι := ι) (p := p) (e := e) (hp2 := hp2) (hK := hK) (h3 := h3)
      (Q := diagramMap TwistTag.E6 k) (α := e6 i3) (β := e6 i1)
      hα hβ hQα hQβ hαβ hzα hzβ
      (t := rootDiagUnit TwistTag.E6.tag ![1, -1, 1, 1, 1, 1] * diagramMap TwistTag.E6 k) htB
  exact ⟨u, huord, hugood, hinv⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive
