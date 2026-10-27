module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven3TenCore
public import CFSG.Adapters.GeneralizedFitting
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenInfra
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenDefs2

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

private theorem s16c167_map_commSub_conj {W : Type} [CommGroup W] (X : Subgroup (MulAut W))
    (g : MulAut W) :
    (commSub (⊤ : Subgroup W) X).map g.toMonoidHom =
      commSub (⊤ : Subgroup W) (X.map (MulAut.conj g).toMonoidHom) := by
  unfold commSub
  rw [MonoidHom.map_closure]
  congr 1
  ext c
  constructor
  · rintro ⟨c', ⟨x, hx, w, -, rfl⟩, rfl⟩
    refine ⟨g * x * g⁻¹, Subgroup.mem_map.2 ⟨x, hx, rfl⟩, g w, Subgroup.mem_top _, ?_⟩
    simp [MulAut.mul_apply, MulAut.inv_apply]
  · rintro ⟨y, hy, w, -, rfl⟩
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.1 hy
    refine ⟨x (g⁻¹ w) * (g⁻¹ w)⁻¹, ⟨x, hx, g⁻¹ w, Subgroup.mem_top _, rfl⟩, ?_⟩
    simp [MulAut.mul_apply, MulAut.inv_apply]

theorem s16c167_card_vtil_le_of_case168_10 (D : Data G) {V L : Subgroup G}
    (hV : IsElemAbelian 2 V) (hc : Counterex16 D ⊥ V L hV) (h10 : Case168_10At D ⊥ V hV L 7) :
    Nat.card (Vtil ⊥ V hV) ≤ 2 ^ 12 := by
  obtain ⟨-, hrk, hs, -, -⟩ := h10
  obtain ⟨t, -, -, -, -, hsup, -⟩ := hc.conc
  have hd : dParam 7 = 3 := by
    unfold dParam
    haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
    exact orderOf_eq_prime (p := 3) (by decide) (by decide)
  rw [hd] at hrk
  let Ts : Set (Subgroup (MulAut (Vtil ⊥ V hV))) :=
    {X | ∃ φ ∈ Mbar D.M ⊥ V hV, X = (lBar ⊥ V hV L).map (MulAut.conj φ).toMonoidHom}
  let S : Set (Subgroup (Vtil ⊥ V hV)) :=
    conjSubs (Mbar D.M ⊥ V hV) (commSub ⊤ (lBar ⊥ V hV L))
  have hTs : Ts.ncard = 2 := hs
  have hTfin : Ts.Finite := Set.finite_of_ncard_ne_zero (by rw [hTs]; norm_num)
  have hSsub : S ⊆ (fun X => commSub (⊤ : Subgroup (Vtil ⊥ V hV)) X) '' Ts := by
    rintro Y ⟨g, hg, rfl⟩
    exact ⟨_, ⟨g, hg, rfl⟩, (s16c167_map_commSub_conj _ g).symm⟩
  have hSfin : S.Finite := (hTfin.image _).subset hSsub
  have hSle : S.ncard ≤ 2 := by
    calc S.ncard ≤ ((fun X => commSub (⊤ : Subgroup (Vtil ⊥ V hV)) X) '' Ts).ncard :=
          Set.ncard_le_ncard hSsub (hTfin.image _)
      _ ≤ Ts.ncard := Set.ncard_image_le hTfin
      _ = 2 := hTs
  have hX₀ : commSub ⊤ (lBar ⊥ V hV L) ∈ S := by
    refine ⟨1, (Mbar D.M ⊥ V hV).one_mem, ?_⟩
    ext x
    simp [Subgroup.mem_map]
  have hrkS : ∀ Y ∈ S, rk ↥Y = 6 := by
    rintro Y ⟨g, -, rfl⟩
    rw [rk_map_aut_eq]
    exact hrk
  obtain ⟨X₁, hX₁, hcover⟩ : ∃ X₁ ∈ S, ∀ Y ∈ S,
      Y = commSub ⊤ (lBar ⊥ V hV L) ∨ Y = X₁ := by
    by_cases h : ∃ X₁ ∈ S, X₁ ≠ commSub ⊤ (lBar ⊥ V hV L)
    · obtain ⟨X₁, hX₁, hne⟩ := h
      have hsub : ({commSub ⊤ (lBar ⊥ V hV L), X₁} : Set (Subgroup (Vtil ⊥ V hV))) ⊆ S := by
        intro Y hY
        rcases hY with rfl | rfl
        · exact hX₀
        · exact hX₁
      have hpair : ({commSub ⊤ (lBar ⊥ V hV L), X₁} : Set (Subgroup (Vtil ⊥ V hV))).ncard = 2 :=
        Set.ncard_pair hne.symm
      have heq := Set.eq_of_subset_of_ncard_le hsub (by rw [hpair]; exact hSle) hSfin
      refine ⟨X₁, hX₁, fun Y hY => ?_⟩
      rw [← heq] at hY
      exact hY
    · exact ⟨_, hX₀, fun Y hY => Or.inl (by_contra fun hne => h ⟨Y, hY, hne⟩)⟩
  have htop : commSub ⊤ (lBar ⊥ V hV L) ⊔ X₁ = ⊤ := by
    refine eq_top_iff.2 ?_
    calc (⊤ : Subgroup (Vtil ⊥ V hV)) = ⨆ Y ∈ S, Y := hsup.symm
      _ ≤ commSub ⊤ (lBar ⊥ V hV L) ⊔ X₁ := by
        refine iSup₂_le fun Y hY => ?_
        rcases hcover Y hY with h | h
        · rw [h]
          exact le_sup_left
        · rw [h]
          exact le_sup_right
  have hsq : ∀ v : Vtil ⊥ V hV, v ^ 2 = 1 := fun v => s15_Infra_vtil_sq_eq_one ⊥ V hV v
  have hp : IsPGroup 2 (Vtil ⊥ V hV) := isPGroup_two_of_sq_eq_one hsq
  have hr1 := rk_sup_add_rk_inf (commSub ⊤ (lBar ⊥ V hV L)) X₁
  rw [htop, rk_top, hrkS _ hX₀, hrkS _ hX₁] at hr1
  rw [card_eq_two_pow_of_isPGroup hp]
  exact Nat.pow_le_pow_right (by norm_num) (by omega)

theorem s16c167_rk_le_two_of_case168_10_seven (D : Data G) {V L : Subgroup G}
    (hV : IsElemAbelian 2 V) (hc : Counterex16 D ⊥ V L hV) (h10 : Case168_10At D ⊥ V hV L 7)
    {X : Subgroup (MulAut (Vtil ⊥ V hV))} (hXM : X ≤ Mbar D.M ⊥ V hV)
    (hX : IsElemAbelian2 X) : rk ↥X ≤ 2 := by
  have hsq : ∀ w : Vtil ⊥ V hV, w * w = 1 := fun w => by
    have := s15_Infra_vtil_sq_eq_one ⊥ V hV w
    rwa [pow_two] at this
  have hcard := s16c167_card_vtil_le_of_case168_10 D hV hc h10
  have hTn : ∀ g ∈ Mbar D.M ⊥ V hV, ∀ t ∈ fstarBar D.M ⊥ V hV,
      g * t * g⁻¹ ∈ fstarBar D.M ⊥ V hV := by
    intro g hg t ht
    have ht' : t ∈ (genFittingFStar ↥(Mbar D.M ⊥ V hV)).map (Mbar D.M ⊥ V hV).subtype := ht
    obtain ⟨t', ht'F, rfl⟩ := Subgroup.mem_map.1 ht'
    have hn : (genFittingFStar ↥(Mbar D.M ⊥ V hV)).Normal :=
      CFSG.ComponentClassification.GeneralizedFitting.normal _
    exact Subgroup.mem_map.2 ⟨⟨g, hg⟩ * t' * ⟨g, hg⟩⁻¹, hn.conj_mem t' ht'F ⟨g, hg⟩, rfl⟩
  have hTc : ∀ x ∈ Mbar D.M ⊥ V hV, (∀ t ∈ fstarBar D.M ⊥ V hV, x * t = t * x) →
      x ∈ fstarBar D.M ⊥ V hV := by
    intro x hx hcomm
    have hcent : (⟨x, hx⟩ : ↥(Mbar D.M ⊥ V hV)) ∈
        Subgroup.centralizer (genFittingFStar ↥(Mbar D.M ⊥ V hV) :
          Set ↥(Mbar D.M ⊥ V hV)) := by
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      apply Subtype.ext
      exact (hcomm (h : MulAut (Vtil ⊥ V hV)) (Subgroup.mem_map.2 ⟨h, hh, rfl⟩)).symm
    exact Subgroup.mem_map.2
      ⟨⟨x, hx⟩, CFSG.Adapters.generalized_fitting_self_centralizing _ hcent, rfl⟩
  have hle := s16c167_card_le_four_of_ten hsq hcard hTn hTc h10.2.2.2.2 hXM hX
  have hp : IsPGroup 2 ↥X := by
    intro x
    refine ⟨1, Subtype.ext ?_⟩
    simpa using hX.2 (x : MulAut (Vtil ⊥ V hV)) x.2
  rw [card_eq_two_pow_of_isPGroup hp] at hle
  by_contra hlt
  have h8 : 2 ^ 3 ≤ 2 ^ rk ↥X := Nat.pow_le_pow_right (by norm_num) (by omega)
  omega

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
