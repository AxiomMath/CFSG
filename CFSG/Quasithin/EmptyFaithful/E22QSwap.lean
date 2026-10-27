module

public import CFSG.Quasithin.EmptyFaithful.E22QWr
public import CFSG.Quasithin.Background.E1Sec4

public section

namespace CFSG.Quasithin.E2.E22N

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.A1b

variable {G : Type} [Group G] [Finite G] {p : ℕ} {T M J₁ J₂ : Subgroup G} {z₁ : G}

theorem swapw_isComponent₁ (h : Wr p T M J₁ J₂ z₁) : CFSG.IsComponent J₁ := by
  have := h.simple₁
  have := h.normal_X
  exact ⟨(CFSG.LocalCores.isQuasisimple_of_isSimpleGroup h.nonab₁).1,
    A3.isSubnormal_of_subnormal (A3.subnormal_of_normal le_sup_left h.J₁_normal_in_X)
      (Subgroup.Normal.isSubnormal inferInstance)⟩

theorem swapw_isComponent₂ (h : Wr p T M J₁ J₂ z₁) : CFSG.IsComponent J₂ := by
  have := h.simple₂
  have := h.normal_X
  exact ⟨(CFSG.LocalCores.isQuasisimple_of_isSimpleGroup h.nonab₂).1,
    A3.isSubnormal_of_subnormal (A3.subnormal_of_normal le_sup_right h.J₂_normal_in_X)
      (Subgroup.Normal.isSubnormal inferInstance)⟩

omit [Finite G] in
theorem swapw_eq_bot_of_commutator (h : Wr p T M J₁ J₂ z₁) {K : Subgroup G} (h₁ : ⁅J₁, K⁆ = ⊥)
    (h₂ : ⁅J₂, K⁆ = ⊥) : K = ⊥ := by
  have hK : J₁ ⊔ J₂ ≤ Subgroup.centralizer (K : Set G) :=
    sup_le (Subgroup.commutator_eq_bot_iff_le_centralizer.mp h₁)
      (Subgroup.commutator_eq_bot_iff_le_centralizer.mp h₂)
  have := Subgroup.le_centralizer_iff.mp hK
  rw [h.cent] at this
  exact le_bot_iff.mp this

theorem swapw_radical_eq_bot (h : Wr p T M J₁ J₂ z₁) : CFSG.solvableRadical G = ⊥ := by
  have key : ∀ K : Subgroup G, CFSG.IsComponent K → ⁅K, CFSG.solvableRadical G⁆ = ⊥ := fun K hK =>
    (CFSG.LocalCores.component_solvable_centralizer
      (A3.solvableRadical_isSolvable (G := G)) (Subgroup.Normal.isSubnormal inferInstance)).1 K hK
  exact swapw_eq_bot_of_commutator h (key _ (swapw_isComponent₁ h))
    (key _ (swapw_isComponent₂ h))

theorem swapw_cCompSpan_le (h : Wr p T M J₁ J₂ z₁) : cCompSpan (⊤ : Subgroup G) ≤ J₁ ⊔ J₂ := by
  have hR := swapw_radical_eq_bot h
  refine sSup_le fun K hK => ?_
  have hKc : CFSG.IsComponent K := isComponent_of_mem_cComp_top hR hK
  rcases CFSG.LocalCores.distinct_components_commute hKc (swapw_isComponent₁ h) with h1 | h1
  · exact h1.le.trans le_sup_left
  rcases CFSG.LocalCores.distinct_components_commute hKc (swapw_isComponent₂ h) with h2 | h2
  · exact h2.le.trans le_sup_right
  · exfalso
    rw [Subgroup.commutator_comm] at h1 h2
    exact ne_bot_of_mem_cComp hK (swapw_eq_bot_of_commutator h h1 h2)

theorem swapw_isComponent_map {J : Subgroup G} (hJ : CFSG.IsComponent J) :
    CFSG.IsComponent (J.map (QuotientGroup.mk' (CFSG.solvableRadical G))) := by
  have hker : Group.IsSolvable (QuotientGroup.mk' (CFSG.solvableRadical G)).ker := by
    rw [QuotientGroup.ker_mk']
    exact A3.solvableRadical_isSolvable
  exact isComponent_of_mem_cComp_top (A3.solvableRadical_quotient_eq_bot G)
    (map_mem_cComp_top _ (QuotientGroup.mk'_surjective _) hker (mem_cComp_top_of_isComponent hJ))

omit [Finite G] in
theorem swapw_mk'_injective (hR : CFSG.solvableRadical G = ⊥) :
    Function.Injective (QuotientGroup.mk' (CFSG.solvableRadical G)) :=
  (MonoidHom.ker_eq_bot_iff _).mp (by rw [QuotientGroup.ker_mk', hR])

theorem swapw_layer_eq (h : Wr p T M J₁ J₂ z₁) :
    CFSG.layer (G ⧸ CFSG.solvableRadical G) =
      (J₁ ⊔ J₂).map (QuotientGroup.mk' (CFSG.solvableRadical G)) := by
  refine le_antisymm ?_ ?_
  · rw [← map_cCompSpan_eq_layer]
    exact Subgroup.map_mono (swapw_cCompSpan_le h)
  · rw [Subgroup.map_sup]
    exact sup_le
      (CFSG.LocalCores.component_le_layer (swapw_isComponent_map (swapw_isComponent₁ h)))
      (CFSG.LocalCores.component_le_layer (swapw_isComponent_map (swapw_isComponent₂ h)))

omit [Finite G] in
theorem swapw_biSup_conj {Q : Type*} [Group Q] (h : Wr p T M J₁ J₂ z₁) (π : G →* Q)
    {τ : Subgroup G} (hτ : τ ≤ T) {c : G} (hcτ : c ∈ τ) (hc : conjSub c J₁ = J₂) :
    (⨆ t ∈ τ.map π, conjSub t (J₁.map π)) = (J₁ ⊔ J₂).map π := by
  apply le_antisymm
  · refine iSup₂_le fun t' ht' => ?_
    obtain ⟨t, ht, rfl⟩ := ht'
    rw [← E1.map_conjSub]
    rcases h.perm t (hτ ht) with e | e
    · rw [e]
      exact Subgroup.map_mono le_sup_left
    · rw [e]
      exact Subgroup.map_mono le_sup_right
  · rw [Subgroup.map_sup]
    refine sup_le ?_ ?_
    · refine le_iSup₂_of_le (π 1) (Subgroup.mem_map_of_mem π τ.one_mem) ?_
      rw [map_one, conjSub_one]
    · refine le_iSup₂_of_le (π c) (Subgroup.mem_map_of_mem π hcτ) ?_
      rw [← E1.map_conjSub, hc]

theorem swapw_X_perfect (h : Wr p T M J₁ J₂ z₁) : ⁅J₁ ⊔ J₂, J₁ ⊔ J₂⁆ = J₁ ⊔ J₂ := by
  refine le_antisymm (A3.commutator_self_le _) (sup_le ?_ ?_)
  · have h1 : ⁅J₁, J₁⁆ = J₁ := Subgroup.isPerfect_iff.mp (swapw_isComponent₁ h).1.1
    exact h1.symm.le.trans (Subgroup.commutator_mono le_sup_left le_sup_left)
  · have h2 : ⁅J₂, J₂⁆ = J₂ := Subgroup.isPerfect_iff.mp (swapw_isComponent₂ h).1.1
    exact h2.symm.le.trans (Subgroup.commutator_mono le_sup_right le_sup_right)

omit [Finite G] in
theorem swapw_centralizes_J₂ {A : Subgroup G} {c : G} (hcA : c ∈ Subgroup.centralizer (A : Set G))
    (hc : conjSub c J₁ = J₂) (hA : A ≤ Subgroup.centralizer (J₁ : Set G)) :
    A ≤ Subgroup.centralizer (J₂ : Set G) := by
  intro x hx
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  obtain ⟨y', hy', rfl⟩ : y ∈ conjSub c J₁ := hc ▸ hy
  have hxc : Commute x c := Subgroup.mem_centralizer_iff.mp hcA x hx
  have hxy : Commute x y' := (Subgroup.mem_centralizer_iff.mp (hA hx) y' hy').symm
  have := ((hxc.mul_right hxy).mul_right hxc.inv_right).eq
  simpa [MulAut.conj_apply] using this.symm

theorem swapw_commutator_eq (h : Wr p T M J₁ J₂ z₁) {A : Subgroup G} (hAbot : A ≠ ⊥) {c : G}
    (hcA : c ∈ Subgroup.centralizer (A : Set G)) (hc : conjSub c J₁ = J₂)
    (hAN : A ≤ Subgroup.normalizer (J₁ : Set G)) : ⁅J₁, A⁆ = J₁ := by
  have hJ₁ := mem_cComp_top_of_isComponent (swapw_isComponent₁ h)
  rcases cComp_commutator_dichotomy hJ₁ A with ⟨h1, -⟩ | h1
  · exfalso
    rw [swapw_radical_eq_bot h, le_bot_iff] at h1
    have hAJ₁ : A ≤ Subgroup.centralizer (J₁ : Set G) :=
      Subgroup.le_centralizer_iff.mp (Subgroup.commutator_eq_bot_iff_le_centralizer.mp h1)
    have hAJ₂ := swapw_centralizes_J₂ hcA hc hAJ₁
    refine hAbot (swapw_eq_bot_of_commutator h h1 ?_)
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.mpr (Subgroup.le_centralizer_iff.mp hAJ₂)
  · rw [h1]
    exact le_antisymm (conjClosure_le fun a ha z hz =>
      (Subgroup.mem_normalizer_iff.mp (hAN ha) z).mp hz) (le_conjClosure J₁ A)

theorem swapw_eTwo (h : Wr p T M J₁ J₂ z₁) {A : Subgroup G} (hA2 : Nat.card A = 2)
    (hc : ¬ T ⊓ Subgroup.centralizer (A : Set G) ≤ Subgroup.normalizer (J₁ : Set G)) :
    E1.ETwo G T A := by
  have hAbot : A ≠ ⊥ := by
    rintro rfl
    simp at hA2
  have hR : CFSG.solvableRadical G = ⊥ := swapw_radical_eq_bot h
  obtain ⟨c, hcmem, hcN⟩ := IsConcreteLE.not_le_iff_exists.mp hc
  have hcT : c ∈ T := (Subgroup.mem_inf.mp hcmem).1
  have hcA : c ∈ Subgroup.centralizer (A : Set G) := (Subgroup.mem_inf.mp hcmem).2
  have hcJ : conjSub c J₁ = J₂ := by
    rcases h.perm c hcT with e | e
    · exact absurd (conjSub_eq_iff_mem_normalizer.mp e) hcN
    · exact e
  have := h.normal_X
  have hnormtop : ∀ g : G, g ∈ Subgroup.normalizer ((J₁ ⊔ J₂ : Subgroup G) : Set G) := fun g => by
    rw [Subgroup.normalizer_eq_top_iff.mpr inferInstance]
    exact Subgroup.mem_top g
  have h2 : ∀ x : G, ∃ k : ℕ, x ^ 2 ^ k ∈ J₁ ⊔ J₂ := fun x =>
    B6.isTwoQuotient_of_sup_eq h.sylow.isPGroup (D := ⊤) (C := J₁ ⊔ J₂) (fun g _ => hnormtop g)
      (by rw [sup_comm]; exact h.gen) x (Subgroup.mem_top x)
  have hJ₁c := mem_cComp_top_of_isComponent (swapw_isComponent₁ h)
  have hJ₂c := mem_cComp_top_of_isComponent (swapw_isComponent₂ h)
  have hπinj := swapw_mk'_injective hR
  refine ⟨?_, ?_, ?_, J₁.map (QuotientGroup.mk' (CFSG.solvableRadical G)),
    swapw_isComponent_map (swapw_isComponent₁ h), ?_, ?_⟩
  · rw [hR]
    refine ⟨⊥, ⟨le_rfl, IsPGroup.of_bot, ?_⟩, Subgroup.Normal.subgroupOf inferInstance _⟩
    rw [Subgroup.relIndex_self]
    omega
  · rw [E1.pCore_two_quotient_eq_top_iff]
    intro x
    obtain ⟨k, hk⟩ := h2 x
    refine ⟨k, ?_⟩
    have hLO : J₁ ⊔ J₂ ≤ oInftyE G := by
      rw [E1.oInftyE_eq_cCompSpan_sup G]
      exact (sup_le (le_cCompSpan hJ₁c) (le_cCompSpan hJ₂c)).trans le_sup_left
    exact hLO hk
  · have h1 : twoResidual (⊤ : Subgroup G) ≤ J₁ ⊔ J₂ :=
      twoResidual_le_of_isTwoQuotient le_top (fun g _ => hnormtop g) fun y _ => h2 y
    have h3 : perfectCore (⊤ : Subgroup G) ≤ twoResidual (⊤ : Subgroup G) :=
      perfectCore_le_of_sup_solvable (twoResidual_le ⊤)
        (Subgroup.Normal.subgroupOf
          (Subgroup.normalizer_eq_top_iff.mp (top_le_iff.mp (le_normalizer_twoResidual ⊤))) _)
        (by rw [sup_comm]; exact (sup_twoResidual_eq h.sylow).symm)
        (E1.isSolvable_of_isPGroup_two h.sylow.isPGroup)
    exact le_antisymm (h1.trans (le_perfectCore_of_perfect le_top (swapw_X_perfect h))) h3
  · rw [swapw_layer_eq h, swapw_biSup_conj h _ (E1.tauOf_le ⊤ T A) (c := c)
      (by rw [h.tau_eq]; exact hcmem) hcJ]
  · by_cases hAN : A ≤ Subgroup.normalizer (J₁ : Set G)
    · left
      show J₁.map (QuotientGroup.mk' (CFSG.solvableRadical G)) =
        ⁅J₁.map (QuotientGroup.mk' (CFSG.solvableRadical G)),
          A.map (QuotientGroup.mk' (CFSG.solvableRadical G))⁆
      rw [← Subgroup.map_commutator, swapw_commutator_eq h hAbot hcA hcJ hAN]
    · right
      refine ⟨fun hle => hAN fun a ha => ?_, ?_⟩
      · have h3 := Subgroup.mem_normalizer_iff.mp
          (hle (Subgroup.mem_map_of_mem (QuotientGroup.mk' (CFSG.solvableRadical G)) ha))
        rw [Subgroup.mem_normalizer_iff]
        intro z
        have h4 := h3 (QuotientGroup.mk' (CFSG.solvableRadical G) z)
        rwa [← map_inv, ← map_mul, ← map_mul, Subgroup.mem_map_iff_mem hπinj,
          Subgroup.mem_map_iff_mem hπinj] at h4
      · show Nat.card (A.map (QuotientGroup.mk' (CFSG.solvableRadical G))) = 2
        rw [Subgroup.card_map_of_injective hπinj]
        exact hA2

set_option linter.unusedVariables false in
theorem swap_witness {G : Type} [Group G] [Finite G] {p : ℕ} {T M J₁ J₂ : Subgroup G} {z₁ : G}
    (h : Wr p T M J₁ J₂ z₁) {A : Subgroup G} (hAT : A ≤ T) (hA2 : Nat.card A = 2)
    (hc : ¬ T ⊓ Subgroup.centralizer (A : Set G) ≤ Subgroup.normalizer (J₁ : Set G)) :
    E1.IsE 1 ⊤ T A ⊤ := by
  have hR : CFSG.solvableRadical G = ⊥ := swapw_radical_eq_bot h
  have he : (Subgroup.topEquiv (G := G)).toMonoidHom = (⊤ : Subgroup G).subtype := rfl
  have hS : ((T ⊓ ⊤).subgroupOf (⊤ : Subgroup G)).map
      (Subgroup.topEquiv (G := G)).toMonoidHom = T := by
    rw [he, inf_top_eq]
    exact Subgroup.map_subgroupOf_eq_of_le le_top
  have hB : (A.subgroupOf (⊤ : Subgroup G)).map (Subgroup.topEquiv (G := G)).toMonoidHom = A := by
    rw [he]
    exact Subgroup.map_subgroupOf_eq_of_le le_top
  refine ⟨le_rfl, (E1.tauOf_le ⊤ T A).trans (by rw [inf_top_eq]),
    by rw [inf_top_eq]; exact h.sylow, Or.inr ⟨?_, ?_⟩⟩
  · rw [E1.eTwo_map (Subgroup.topEquiv (G := G)), hS, hB]
    exact swapw_eTwo h hA2 hc
  · have h1 := E1.card_barRad_map (Subgroup.topEquiv (G := G)) (A.subgroupOf (⊤ : Subgroup G))
    rw [hB] at h1
    rw [← h1]
    have : Nat.card (E1.barRad G A) = Nat.card A :=
      Subgroup.card_map_of_injective (swapw_mk'_injective hR)
    rw [this, hA2]
    norm_num

end CFSG.Quasithin.E2.E22N
