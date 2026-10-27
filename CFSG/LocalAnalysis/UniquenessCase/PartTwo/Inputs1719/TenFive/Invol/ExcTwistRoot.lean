module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive.Invol.ExcPairHeis
public import CFSG.LieType.AlgebraicGroups.ToralTwistPinningFrobenius
public import CFSG.Blueprint.ChevalleyRootArtifact

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley (rootChar rootDiagUnit)

abbrev RootsCommute (τ : Tag) (α β : Fin τ.rank → ℤ) : Prop :=
  α ≠ β ∧ α ≠ -β ∧ ¬IsRoot τ (α + β)

theorem rootsCommute_of_list {τ : Tag} {α β : Fin τ.rank → ℤ}
    (h1 : List.ofFn α ≠ List.ofFn β) (h2 : List.ofFn α ≠ List.ofFn (-β))
    (h3 : List.ofFn (α + β) ∉ τ.artifactRoots) : RootsCommute τ α β :=
  ⟨fun e => h1 (by rw [e]), fun e => h2 (by rw [e]),
    fun h => h3 (isRoot_iff_mem_artifactRoots.1 h)⟩

theorem frobTwistGL_pinnedX
    {τ : Tag} {k : Type} [Field k] (p : ℕ) [Fact p.Prime]
    [CharP k p] (e : ℕ) (Q : ModGL τ k) {γ γ' : Fin τ.rank → ℤ} {s : k}
    (hQ : ∀ c, Q * pinnedX τ k γ c * Q⁻¹ = pinnedX τ k γ' (s * c)) (c : k) :
    frobTwistGL τ k p e Q (pinnedX τ k γ c) = pinnedX τ k γ' (s * c ^ p ^ e) := by
  rw [frobTwistGL_apply, entrywiseFrobGL_pinnedX, iterateFrobenius_def, hQ]


open scoped commutatorElement in
theorem pinnedX_commute {τ : Tag} (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    {k : Type} [Field k] {γ δ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ) (hδ : IsRoot τ δ)
    (hne : γ ≠ δ) (hne' : γ ≠ -δ) (h : ¬IsRoot τ (γ + δ)) (c d : k) :
    Commute (pinnedX τ k γ c) (pinnedX τ k δ d) :=
  (simply_laced_root_commutator_unit τ hτ hγ hδ hne hne').2 h k
    (pinnedX τ k γ c) (Subgroup.subset_closure ⟨c, rfl⟩)
    (pinnedX τ k δ d) (Subgroup.subset_closure ⟨d, rfl⟩)

theorem pinnedX_commute_of_rootsCommute {τ : Tag}
    (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {k : Type} [Field k]
    {γ δ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ) (hδ : IsRoot τ δ)
    (h : RootsCommute τ γ δ) (c d : k) :
    Commute (pinnedX τ k γ c) (pinnedX τ k δ d) :=
  pinnedX_commute hτ hγ hδ h.1 h.2.1 h.2.2 c d

theorem exists_twist_pair_inv_good {τ : Tag} (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    {K k : Type} [Field K] [Finite K] [Field k] [IsAlgClosed k] (ι : K →+* k) {p e : ℕ}
    [Fact p.Prime] (hp2 : p ≠ 2) [CharP K p] [CharP k p] (hK : Nat.card K = p ^ e)
    (h3 : 3 < p ^ e) (Q : ModGL τ k) (θ : (Fin τ.rank → ℤ) → Fin τ.rank → ℤ)
    (hQ : ∀ γ, IsRoot τ γ → ∃ s : k, s * s = 1 ∧
      ∀ c, Q * pinnedX τ k γ c * Q⁻¹ = pinnedX τ k (θ γ) (s * c))
    (a : Fin τ.rank → kˣ) {α β : Fin τ.rank → ℤ}
    (hα : IsRoot τ α) (hβ : IsRoot τ β) (hθα : IsRoot τ (θ α)) (hθβ : IsRoot τ (θ β))
    (hθθα : θ (θ α) = α) (hθθβ : θ (θ β) = β)
    (hαθα : RootsCommute τ α (θ α)) (hβθβ : RootsCommute τ β (θ β))
    (hαθβ : RootsCommute τ α (θ β)) (hθαβ : RootsCommute τ (θ α) β)
    (hαβ : α ≠ β ∧ α ≠ -β ∧ IsRoot τ (α + β))
    (hθαθβ : θ α ≠ θ β ∧ θ α ≠ -θ β ∧ IsRoot τ (θ α + θ β))
    (hz : ∀ γ ∈ [α, θ α, β, θ β],
      RootsCommute τ (α + β) γ ∧ RootsCommute τ (θ α + θ β) γ)
    (hzz : RootsCommute τ (α + β) (θ α + θ β))
    (hpos : 0 < height (α + β) ∧ 0 < height (θ α + θ β))
    (hχ : rootChar a β = -1) (hχ' : rootChar a (θ β) = -1) :
    ∃ u : fixedPointsIn (adjointGroup τ k) (frobTwistGL τ k p e Q), orderOf u = p ∧
      IsSpecialGood p u ∧
      rootDiagUnit τ a * (u : ModGL τ k) * (rootDiagUnit τ a)⁻¹ = (u : ModGL τ k)⁻¹ := by
  classical
  obtain ⟨sa, hsa, hQa⟩ := hQ α hα
  obtain ⟨sa', hsa', hQa'⟩ := hQ (θ α) hθα
  obtain ⟨sb, hsb, hQb⟩ := hQ β hβ
  obtain ⟨sb', hsb', hQb'⟩ := hQ (θ β) hθβ
  have hQaθ : ∀ c, Q * pinnedX τ k (θ α) c * Q⁻¹ = pinnedX τ k α (sa' * c) := by
    intro c
    rw [hQa' c, hθθα]
  have hQbθ : ∀ c, Q * pinnedX τ k (θ β) c * Q⁻¹ = pinnedX τ k β (sb' * c) := by
    intro c
    rw [hQb' c, hθθβ]
  have hcf := (simply_laced_root_commutator_unit τ hτ hα hβ hαβ.1 hαβ.2.1).1 hαβ.2.2
  have hcf' :=
    (simply_laced_root_commutator_unit τ hτ hθα hθβ hθαθβ.1 hθαθβ.2.1).1 hθαθβ.2.2
  have hzα := hz α (by simp)
  have hzθα := hz (θ α) (by simp)
  have hzβ := hz β (by simp)
  have hzθβ := hz (θ β) (by simp)
  have hCinj : ∀ c d : k,
      (fun r => pinnedX τ k (α + β) ((commConst τ α β (1, 1) : k) * r)) c *
        (fun r => pinnedX τ k (θ α + θ β) ((commConst τ (θ α) (θ β) (1, 1) : k) * r)) d = 1 →
      c = 0 := by
    intro c d hcd
    have hL : [α + β, θ α + θ β].Nodup := by simp [hzz.1]
    have hroots : ∀ γ ∈ [α + β, θ α + θ β], IsRoot τ γ ∧ 0 < height γ := by
      intro γ hγ
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hγ
      rcases hγ with rfl | rfl
      · exact ⟨hαβ.2.2, hpos.1⟩
      · exact ⟨hθαθβ.2.2, hpos.2⟩
    have heq : ([α + β, θ α + θ β].map fun γ =>
          pinnedX τ k γ (if γ = α + β then (commConst τ α β (1, 1) : k) * c
            else (commConst τ (θ α) (θ β) (1, 1) : k) * d)).prod =
        ([α + β, θ α + θ β].map fun γ => pinnedX τ k γ (0 : k)).prod := by
      simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
        if_neg (Ne.symm hzz.1), pinnedX_zero, mul_one]
      exact hcd
    have hkey := pinnedX_list_prod_injective (τ := τ) (R := k) [α + β, θ α + θ β] hL hroots
      (fun γ => if γ = α + β then (commConst τ α β (1, 1) : k) * c
        else (commConst τ (θ α) (θ β) (1, 1) : k) * d) (fun _ => 0) heq
    have hnc : (commConst τ α β (1, 1) : k) * c = 0 := by
      simpa using hkey (α + β) (by simp)
    have hn0 : (commConst τ α β (1, 1) : k) ≠ 0 := by
      rcases hcf.1 with h | h <;> simp [h]
    exact (mul_eq_zero.1 hnc).resolve_left hn0
  refine exists_pair_heis_inv_good (adjointGroup τ k) (frobTwistGL τ k p e Q) ι (Fact.out) hp2
    hK h3 (A := fun c => pinnedX τ k α c) (A' := fun c => pinnedX τ k (θ α) c)
    (B := fun c => pinnedX τ k β c) (B' := fun c => pinnedX τ k (θ β) c)
    (C := fun r => pinnedX τ k (α + β) ((commConst τ α β (1, 1) : k) * r))
    (C' := fun r => pinnedX τ k (θ α + θ β) ((commConst τ (θ α) (θ β) (1, 1) : k) * r))
    (hA := pinnedX_add τ k α) (hA' := pinnedX_add τ k (θ α)) (hB := pinnedX_add τ k β)
    (hB' := pinnedX_add τ k (θ β))
    (hC := fun c d => by rw [mul_add, pinnedX_add])
    (hC' := fun c d => by rw [mul_add, pinnedX_add])
    (hAX := fun c => pinnedX_mem_adjointGroup α c)
    (hA'X := fun c => pinnedX_mem_adjointGroup (θ α) c)
    (hBX := fun c => pinnedX_mem_adjointGroup β c)
    (hB'X := fun c => pinnedX_mem_adjointGroup (θ β) c)
    (sa := sa) (sa' := sa') (sb := sb) (sb' := sb') (hsa := hsa) (hsa' := hsa')
    (hsb := hsb) (hsb' := hsb')
    (hSA := fun c => frobTwistGL_pinnedX p e Q hQa c)
    (hSA' := fun c => frobTwistGL_pinnedX p e Q hQaθ c)
    (hSB := fun c => frobTwistGL_pinnedX p e Q hQb c)
    (hSB' := fun c => frobTwistGL_pinnedX p e Q hQbθ c)
    (hAA' := fun c d => pinnedX_commute hτ hα hθα hαθα.1 hαθα.2.1 hαθα.2.2 c d)
    (hBB' := fun c d => pinnedX_commute hτ hβ hθβ hβθβ.1 hβθβ.2.1 hβθβ.2.2 c d)
    (hAB' := fun c d => pinnedX_commute hτ hα hθβ hαθβ.1 hαθβ.2.1 hαθβ.2.2 c d)
    (hA'B := fun c d => pinnedX_commute hτ hθα hβ hθαβ.1 hθαβ.2.1 hθαβ.2.2 c d)
    (hAB := fun c d => by rw [hcf.2 k c d, mul_assoc])
    (hA'B' := fun c d => by rw [hcf'.2 k c d, mul_assoc])
    (hCA := fun c d => pinnedX_commute hτ hαβ.2.2 hα hzα.1.1 hzα.1.2.1 hzα.1.2.2 _ d)
    (hCA' := fun c d => pinnedX_commute hτ hαβ.2.2 hθα hzθα.1.1 hzθα.1.2.1 hzθα.1.2.2 _ d)
    (hCB := fun c d => pinnedX_commute hτ hαβ.2.2 hβ hzβ.1.1 hzβ.1.2.1 hzβ.1.2.2 _ d)
    (hCB' := fun c d => pinnedX_commute hτ hαβ.2.2 hθβ hzθβ.1.1 hzθβ.1.2.1 hzθβ.1.2.2 _ d)
    (hC'A := fun c d => pinnedX_commute hτ hθαθβ.2.2 hα hzα.2.1 hzα.2.2.1 hzα.2.2.2 _ d)
    (hC'A' := fun c d => pinnedX_commute hτ hθαθβ.2.2 hθα hzθα.2.1 hzθα.2.2.1 hzθα.2.2.2 _ d)
    (hC'B := fun c d => pinnedX_commute hτ hθαθβ.2.2 hβ hzβ.2.1 hzβ.2.2.1 hzβ.2.2.2 _ d)
    (hC'B' := fun c d => pinnedX_commute hτ hθαθβ.2.2 hθβ hzθβ.2.1 hzθβ.2.2.1 hzθβ.2.2.2 _ d)
    (hCC' := fun c d => pinnedX_commute hτ hαβ.2.2 hθαθβ.2.2 hzz.1 hzz.2.1 hzz.2.2 _ _)
    (hCinj := hCinj) (t := rootDiagUnit τ a)
    (htB := fun c => by
      rw [rootDiagUnit_conj_pinnedX a hβ c, hχ, Units.val_neg, Units.val_one, neg_one_mul])
    (htB' := fun c => by
      rw [rootDiagUnit_conj_pinnedX a hθβ c, hχ', Units.val_neg, Units.val_one, neg_one_mul])

theorem exists_twist_fixed_inv_good {τ : Tag} (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    {K k : Type} [Field K] [Finite K] [Field k] [IsAlgClosed k] (ι : K →+* k) {p e : ℕ}
    [Fact p.Prime] (hp2 : p ≠ 2) [CharP K p] [CharP k p] (hK : Nat.card K = p ^ e)
    (h3 : 3 < p ^ e) (Q : ModGL τ k) {α β : Fin τ.rank → ℤ} (hα : IsRoot τ α)
    (hβ : IsRoot τ β)
    (hQα : ∃ s : k, s * s = 1 ∧ ∀ c, Q * pinnedX τ k α c * Q⁻¹ = pinnedX τ k α (s * c))
    (hQβ : ∃ s : k, s * s = 1 ∧ ∀ c, Q * pinnedX τ k β c * Q⁻¹ = pinnedX τ k β (s * c))
    (hαβ : α ≠ β ∧ α ≠ -β ∧ IsRoot τ (α + β))
    (hzα : RootsCommute τ (α + β) α) (hzβ : RootsCommute τ (α + β) β) {t : ModGL τ k}
    (htB : ∀ c, t * pinnedX τ k β c * t⁻¹ = pinnedX τ k β (-c)) :
    ∃ u : fixedPointsIn (adjointGroup τ k) (frobTwistGL τ k p e Q), orderOf u = p ∧
      IsSpecialGood p u ∧ t * (u : ModGL τ k) * t⁻¹ = (u : ModGL τ k)⁻¹ := by
  classical
  obtain ⟨sa, hsa, hQa⟩ := hQα
  obtain ⟨sb, hsb, hQb⟩ := hQβ
  have hcf := (simply_laced_root_commutator_unit τ hτ hα hβ hαβ.1 hαβ.2.1).1 hαβ.2.2
  have hCinj : ∀ c : k,
      pinnedX τ k (α + β) ((commConst τ α β (1, 1) : k) * c) = 1 → c = 0 := by
    intro c hc
    have h0 : pinnedX τ k (α + β) ((commConst τ α β (1, 1) : k) * c) =
        pinnedX τ k (α + β) 0 := by rw [hc, pinnedX_zero]
    have hnc : (commConst τ α β (1, 1) : k) * c = 0 :=
      pinnedX_injective (τ := τ) (R := k) (α + β) h0
    have hn0 : (commConst τ α β (1, 1) : k) ≠ 0 := by
      rcases hcf.1 with h | h <;> simp [h]
    exact (mul_eq_zero.1 hnc).resolve_left hn0
  refine exists_fixed_heis_inv_good (adjointGroup τ k) (frobTwistGL τ k p e Q) ι (Fact.out)
    hp2 hK h3 (A := fun c => pinnedX τ k α c) (B := fun c => pinnedX τ k β c)
    (C := fun r => pinnedX τ k (α + β) ((commConst τ α β (1, 1) : k) * r))
    (hA := pinnedX_add τ k α) (hB := pinnedX_add τ k β)
    (hC := fun c d => by rw [mul_add, pinnedX_add])
    (hAX := fun c => pinnedX_mem_adjointGroup α c)
    (hBX := fun c => pinnedX_mem_adjointGroup β c)
    (sa := sa) (sb := sb) (hsa := hsa) (hsb := hsb)
    (hSA := fun c => frobTwistGL_pinnedX p e Q hQa c)
    (hSB := fun c => frobTwistGL_pinnedX p e Q hQb c)
    (hAB := fun c d => by rw [hcf.2 k c d, mul_assoc])
    (hCA := fun c d => pinnedX_commute hτ hαβ.2.2 hα hzα.1 hzα.2.1 hzα.2.2 _ d)
    (hCB := fun c d => pinnedX_commute hτ hαβ.2.2 hβ hzβ.1 hzβ.2.1 hzβ.2.2 _ d)
    (hCinj := hCinj) (t := t) (htB := htB)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive
