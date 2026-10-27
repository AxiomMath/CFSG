module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps86Ind
import CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive.ToolRestrict
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenThirteenAltTenPerm

public section

namespace CFSG.LocalAnalysis.WeakClosure81.GF2Reps86

open CFSG.Quasithin CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive Equiv Equiv.Perm

private theorem exists_stable_finset {n : ℕ} (hn : 10 ≤ n) {τ : Perm (Fin n)}
    (hτ : ∀ x, τ (τ x) = x) (hf : ∀ i, τ i ≠ i) :
    ∃ Δ : Finset (Fin n), Δ.card = 10 ∧ ∀ x, x ∈ Δ → τ x ∈ Δ := by
  classical
  set S : Finset (Fin n) := Finset.univ.filter fun x => x < τ x with hS
  have hmem : ∀ x, x ∈ S ↔ x < τ x := fun x => by simp [hS]
  have hdisj : Disjoint S (S.image τ) := by
    rw [Finset.disjoint_left]
    intro x hx hx'
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 hx'
    have h1 := (hmem y).1 hy
    have h2 := (hmem (τ y)).1 hx
    rw [hτ] at h2
    exact lt_asymm h1 h2
  have hunion : S ∪ S.image τ = Finset.univ := by
    refine Finset.eq_univ_of_forall fun x => ?_
    rcases lt_or_gt_of_ne (hf x).symm with h | h
    · exact Finset.mem_union_left _ ((hmem x).2 h)
    · refine Finset.mem_union_right _ (Finset.mem_image.2 ⟨τ x, (hmem _).2 ?_, hτ x⟩)
      rw [hτ]
      exact h
  have hcard : S.card + S.card = n := by
    have h := Finset.card_union_of_disjoint hdisj
    rw [hunion, Finset.card_univ, Fintype.card_fin,
      Finset.card_image_of_injective _ τ.injective] at h
    omega
  obtain ⟨R, hRS, hR⟩ := Finset.exists_subset_card_eq (show 5 ≤ S.card by omega)
  refine ⟨R ∪ R.image τ, ?_, fun x hx => ?_⟩
  · rw [Finset.card_union_of_disjoint (hdisj.mono hRS (Finset.image_subset_image hRS)),
      Finset.card_image_of_injective _ τ.injective, hR]
  · rcases Finset.mem_union.1 hx with h | h
    · exact Finset.mem_union_right _ (Finset.mem_image_of_mem τ h)
    · obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 h
      rw [hτ]
      exact Finset.mem_union_left _ hy

private theorem exists_embedding_stable {n : ℕ} (hn : 10 ≤ n) {τ : Perm (Fin n)}
    (hτ : ∀ x, τ (τ x) = x) (hf : ∀ i, τ i ≠ i) :
    ∃ ι : Fin 10 ↪ Fin n, τ ∈ permSetStab (Set.range ι) := by
  obtain ⟨Δ, hΔ, hstab⟩ := exists_stable_finset hn hτ hf
  refine ⟨(Δ.orderEmbOfFin hΔ).toEmbedding, fun x => ?_⟩
  have hr : Set.range (Δ.orderEmbOfFin hΔ).toEmbedding = (Δ : Set (Fin n)) :=
    Finset.range_orderEmbOfFin Δ hΔ
  rw [hr, Finset.mem_coe, Finset.mem_coe]
  refine ⟨fun h => ?_, hstab x⟩
  have h1 := hstab _ h
  rwa [hτ] at h1

private theorem sign_restrictPerm_eq_neg_one {n : ℕ} {ι : Fin 10 ↪ Fin n} {τ : Perm (Fin n)}
    (hτ : τ ∈ permSetStab (Set.range ι)) (h2 : τ ^ 2 = 1) (hf : ∀ i, τ i ≠ i) :
    sign (restrictPerm ι ⟨τ, hτ⟩) = -1 := by
  refine CFSG.LocalAnalysis.RankThreeTheoremC.TenThirteen.AltTen.sign_eq_neg_one_of_involution
    ?_ fun i hi => ?_
  · rw [← map_pow]
    have h : (⟨τ, hτ⟩ : ↥(permSetStab (Set.range ι))) ^ 2 = 1 := Subtype.ext h2
    rw [h, map_one]
  · have h := restrictPerm_apply_apply ι ⟨τ, hτ⟩ i
    rw [hi] at h
    exact hf (ι i) h.symm

private def twistSub {m n : ℕ} (ι : Fin m ↪ Fin n) (τ : Perm (Fin n)) (hτ : ∀ x, τ (τ x) = x) :
    Subgroup ↥(permSetStab (Set.range ι)) where
  carrier := {g | ∀ x, x ∉ Set.range ι →
    (g : Perm (Fin n)) x = if sign (restrictPerm ι g) = 1 then x else τ x}
  one_mem' := fun x _ => by simp
  mul_mem' := fun {g h} hg hh x hx => by
    have hhx : (h : Perm (Fin n)) x ∉ Set.range ι := fun hmem => hx ((h.2 x).1 hmem)
    have e1 := hh x hx
    have e2 := hg _ hhx
    show (g : Perm (Fin n)) ((h : Perm (Fin n)) x) = _
    rw [e2, e1, map_mul, map_mul]
    rcases Int.units_eq_one_or (sign (restrictPerm ι g)) with hεg | hεg <;>
      rcases Int.units_eq_one_or (sign (restrictPerm ι h)) with hεh | hεh <;>
      simp [hεg, hεh, hτ]
  inv_mem' := fun {g} hg x hx => by
    have hgx : ((g⁻¹ : ↥(permSetStab (Set.range ι))) : Perm (Fin n)) x ∉ Set.range ι :=
      fun hmem => hx ((g⁻¹.2 x).1 hmem)
    have e := hg _ hgx
    have e0 : (g : Perm (Fin n)) (((g⁻¹ : ↥(permSetStab (Set.range ι))) : Perm (Fin n)) x) = x := by
      simp
    rw [e0] at e
    simp only [map_inv, inv_eq_one]
    split_ifs at e ⊢ with h
    · exact e.symm
    · calc ((g⁻¹ : ↥(permSetStab (Set.range ι))) : Perm (Fin n)) x
          = τ (τ (((g⁻¹ : ↥(permSetStab (Set.range ι))) : Perm (Fin n)) x)) := (hτ _).symm
        _ = τ x := by rw [← e]

private theorem mem_twistSub {m n : ℕ} {ι : Fin m ↪ Fin n} {τ : Perm (Fin n)}
    {hτ : ∀ x, τ (τ x) = x} {g : ↥(permSetStab (Set.range ι))} :
    g ∈ twistSub ι τ hτ ↔ ∀ x, x ∉ Set.range ι →
      (g : Perm (Fin n)) x = if sign (restrictPerm ι g) = 1 then x else τ x :=
  Iff.rfl

private theorem exists_subgroup_lift_twist {m n : ℕ} (ι : Fin m ↪ Fin n) {τ : Perm (Fin n)}
    (hτ : τ ∈ permSetStab (Set.range ι)) (hτ2 : ∀ x, τ (τ x) = x)
    (hs : sign (restrictPerm ι ⟨τ, hτ⟩) = -1) :
    ∃ J : Subgroup (Perm (Fin n)), J ≤ permSetStab (Set.range ι) ∧ τ ∈ J ∧
      (∀ σ : alternatingGroup (Fin m), (altLift ι σ : Perm (Fin n)) ∈ J) ∧
      ∀ g ∈ J, (∀ i, g (ι i) = ι i) → g = 1 := by
  refine ⟨(twistSub ι τ hτ2).map (permSetStab (Set.range ι)).subtype,
    Subgroup.map_subtype_le _, ?_, fun σ => ?_, fun g hg hfix => ?_⟩
  · refine Subgroup.mem_map.2 ⟨⟨τ, hτ⟩, mem_twistSub.2 fun x _ => ?_, rfl⟩
    rw [hs, if_neg (by decide)]
  · have hσ : restrictPerm ι ⟨altLift ι σ, altLift_mem_permSetStab ι σ⟩ = (σ : Perm (Fin m)) :=
      Equiv.ext fun i => ι.injective
        ((restrictPerm_apply_apply ι _ i).trans (altLift_apply_apply ι σ i))
    refine Subgroup.mem_map.2 ⟨⟨altLift ι σ, altLift_mem_permSetStab ι σ⟩,
      mem_twistSub.2 fun x hx => ?_, rfl⟩
    rw [hσ, mem_alternatingGroup.1 σ.2, if_pos rfl]
    exact altLift_apply_of_notMem ι σ hx
  · obtain ⟨g₀, hg₀, rfl⟩ := Subgroup.mem_map.1 hg
    have h1 : restrictPerm ι g₀ = 1 :=
      Equiv.ext fun i => ι.injective ((restrictPerm_apply_apply ι g₀ i).trans (hfix i))
    refine Equiv.ext fun x => ?_
    by_cases hx : x ∈ Set.range ι
    · obtain ⟨i, rfl⟩ := hx
      exact hfix i
    · have h2 := mem_twistSub.1 hg₀ x hx
      rw [h1, map_one, if_pos rfl] at h2
      exact h2

theorem noFpf_of_ten_le (h10 : NoFpf 10) {n : ℕ} (hn : 10 ≤ n) : NoFpf n := by
  intro V _ _ hV H ψ hψ hA t ht hfpf hidx
  have hτ2 : (ψ t) ^ 2 = 1 := by rw [← map_pow, ht, map_one]
  have hτ : ∀ x, ψ t (ψ t x) = x := fun x => by
    simpa [pow_two] using congrArg (fun g : Perm (Fin n) => g x) hτ2
  obtain ⟨ι, hτS⟩ := exists_embedding_stable hn hτ hfpf
  obtain ⟨J, hJS, hτJ, hlift, hker⟩ := exists_subgroup_lift_twist ι hτS hτ
    (sign_restrictPerm_eq_neg_one hτS hτ2 hfpf)
  have hKS : preSub ψ J ≤ preSub ψ (permSetStab (Set.range ι)) := preSub_mono hJS
  have htK : (t : MulAut V) ∈ preSub ψ J := coe_mem_preSub.2 hτJ
  refine h10 V hV (preSub ψ J) (restrictHom ψ ι (preSub ψ J) hKS) ?_ ?_ ⟨(t : MulAut V), htK⟩
    ?_ ?_ ?_
  · refine restrictHom_injective hψ fun k hk => hker _ ?_ hk
    exact (coe_mem_preSub (ψ := ψ) (x := Subgroup.inclusion (hKS.trans preSub_le) k)).1 k.2
  · intro σ hσ
    obtain ⟨h, hh⟩ := hA (altLift ι ⟨σ, hσ⟩).2
    have hhJ : (h : MulAut V) ∈ preSub ψ J := coe_mem_preSub.2 (hh ▸ hlift _)
    exact ⟨⟨h, hhJ⟩, restrictHom_eq_of_eq_altLift (hK := hKS) (σ := ⟨σ, hσ⟩) hh⟩
  · exact Subtype.ext (by
      simpa only [SubgroupClass.coe_pow, OneMemClass.coe_one] using
        congrArg (fun x : ↥H => (x : MulAut V)) ht)
  · intro i hi
    have h := restrictHom_apply_apply (hK := hKS) ⟨(t : MulAut V), htK⟩ i
    rw [hi] at h
    exact hfpf (ι i) h.symm
  · exact hidx

end CFSG.LocalAnalysis.WeakClosure81.GF2Reps86

end
