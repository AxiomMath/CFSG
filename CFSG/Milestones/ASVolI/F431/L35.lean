module

public import CFSG.Milestones.ASVolI.F431.AInvSpAll
public import CFSG.Milestones.ASVolI.F431.Odd

public section

namespace CFSG.ASVolI

open CFSG.Open CFSG.ASVolI.ChF CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.H13.F431
  CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion

section Fusion

set_option linter.unusedSectionVars false


variable {κ : GLKind} {f : ℕ} {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E}

theorem burnsideF4m_long_conj_inv (hyp : HypF_4_4 κ 2 f Gp M₁ M₂) {x : E}
    (hx : ∃ g ∈ Gp, g * x * g⁻¹ ∈ ctr (pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)))) (e : E) :
    ∃ g ∈ Gp, g * (e * x * e⁻¹) * g⁻¹ ∈ ctr (pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂))) := by
  haveI := hyp.normal
  obtain ⟨g, hg, hgx⟩ := hx
  obtain ⟨n, hn, h, hh, rfl⟩ := hyp.split e
  have hhN : h ∈ Subgroup.normalizer
      ((ctr (pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂))) : Subgroup E) : Set E) :=
    burnsideF4j_mem_normalizer_ctr (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 _
      (burnsideF4j_le_normalizer_inf hyp.normal (M₁ ⊓ M₂) hh))
  refine ⟨h * g * h⁻¹ * n⁻¹, Gp.mul_mem (hyp.normal.conj_mem g hg h) (Gp.inv_mem hn), ?_⟩
  have e1 : h * g * h⁻¹ * n⁻¹ * (n * h * x * (n * h)⁻¹) * (h * g * h⁻¹ * n⁻¹)⁻¹ =
      h * (g * x * g⁻¹) * h⁻¹ := by group
  rw [e1]
  exact (Subgroup.mem_normalizer_iff.mp hhN _).mp hgx

theorem burnsideF4m_isConj_Gp_of_two (hyp : HypF_4_4 κ 2 f Gp M₁ M₂) (hL3 : κ ≠ .L3)
    (hSp : κ ≠ .Sp4) (hG2d : κ ≠ .G2d) {i j : E} (hi : i ∈ Gp) (hj : j ∈ Gp) (hi1 : i ≠ 1)
    (hi2 : i * i = 1) (hij : IsConj i j) : ∃ g ∈ Gp, g * i * g⁻¹ = j := by
  haveI := hyp.finite
  have hyp' := burnsideF4j_restrict ChF.nativeChartCompatibility hyp
  have h27 := as_F_4_27 κ f ↥Gp ⊤ _ _ hyp' rfl
  dsimp only at h27
  obtain ⟨-, -, -, h3, -, -⟩ := h27
  obtain ⟨hcard, ⟨C, ⟨hCI, hCm⟩, hCu⟩, -, -, -⟩ := h3 ⟨hL3, hSp, hG2d⟩
  have hS : ctr (pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂))) =
      (ctr (pCoreOf 2 ((Gp ⊓ M₁).subgroupOf Gp ⊓ (Gp ⊓ M₂).subgroupOf Gp))).map
        Gp.subtype := by
    rw [burnsideF4j_inf_inf_eq_map, burnsideF4j_pCoreOf_map _ Gp.subtype_injective,
      burnsideF4j_ctr_map _ Gp.subtype_injective]
  obtain ⟨e, he⟩ := isConj_iff.mp hij
  have hj1 : j ≠ 1 := by
    rintro rfl
    apply hi1
    calc i = e⁻¹ * (e * i * e⁻¹) * e := by group
      _ = 1 := by rw [he]; group
  have hj2 : j * j = 1 := by
    rw [← he]
    calc e * i * e⁻¹ * (e * i * e⁻¹) = e * (i * i) * e⁻¹ := by group
      _ = 1 := by rw [hi2]; group
  have hmemI : ∀ (x : E) (hx : x ∈ Gp), x ≠ 1 → x * x = 1 →
      ConjClasses.mk (⟨x, hx⟩ : ↥Gp) ∈ InvClasses ↥Gp := fun x hx hx1 hx2 =>
    ⟨⟨x, hx⟩, ConjClasses.mem_carrier_mk, fun h => hx1 (congrArg Subtype.val h),
      Subtype.ext hx2⟩
  have hLC : ∀ (x : E) (hx : x ∈ Gp), x ≠ 1 → x * x = 1 →
      ((∃ g ∈ Gp, g * x * g⁻¹ ∈ ctr (pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)))) ↔
        ConjClasses.mk (⟨x, hx⟩ : ↥Gp) = C) := by
    intro x hx hx1 hx2
    constructor
    · rintro ⟨g, hg, hgx⟩
      rw [hS] at hgx
      obtain ⟨w, hw, hwx⟩ := hgx
      refine hCu _ ⟨hmemI x hx hx1 hx2, w, ?_, hw⟩
      rw [ConjClasses.mem_carrier_iff_mk_eq, ConjClasses.mk_eq_mk_iff_isConj]
      refine isConj_iff.mpr ⟨⟨g, hg⟩⁻¹, Subtype.ext ?_⟩
      show g⁻¹ * (w : E) * g⁻¹⁻¹ = x
      have hwx' : (w : E) = g * x * g⁻¹ := hwx
      rw [hwx']
      group
    · intro hxC
      obtain ⟨w, hwC, hwS⟩ := hCm
      rw [← hxC, ConjClasses.mem_carrier_iff_mk_eq, ConjClasses.mk_eq_mk_iff_isConj] at hwC
      obtain ⟨c, hc⟩ := isConj_iff.mp hwC.symm
      refine ⟨(c : E), c.2, ?_⟩
      rw [hS]
      exact ⟨w, hwS, (congrArg Subtype.val hc).symm⟩
  have hiI := hmemI i hi hi1 hi2
  have hjI := hmemI j hj hj1 hj2
  have hconj : ConjClasses.mk (⟨i, hi⟩ : ↥Gp) = ConjClasses.mk (⟨j, hj⟩ : ↥Gp) := by
    by_cases hL : ∃ g ∈ Gp, g * i * g⁻¹ ∈ ctr (pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)))
    · have hLj : ∃ g ∈ Gp, g * j * g⁻¹ ∈ ctr (pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂))) := by
        rw [← he]
        exact burnsideF4m_long_conj_inv hyp hL e
      rw [(hLC i hi hi1 hi2).mp hL, (hLC j hj hj1 hj2).mp hLj]
    · have hLj : ¬ ∃ g ∈ Gp, g * j * g⁻¹ ∈ ctr (pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂))) := by
        intro hLj
        apply hL
        have := burnsideF4m_long_conj_inv hyp hLj e⁻¹
        rwa [← he, show e⁻¹ * (e * i * e⁻¹) * e⁻¹⁻¹ = i by group] at this
      have hiC : ConjClasses.mk (⟨i, hi⟩ : ↥Gp) ≠ C := fun h => hL ((hLC i hi hi1 hi2).mpr h)
      have hjC : ConjClasses.mk (⟨j, hj⟩ : ↥Gp) ≠ C := fun h => hLj ((hLC j hj hj1 hj2).mpr h)
      by_contra hne
      have hsub : ({C, ConjClasses.mk (⟨i, hi⟩ : ↥Gp), ConjClasses.mk (⟨j, hj⟩ : ↥Gp)} :
          Set (ConjClasses ↥Gp)) ⊆ InvClasses ↥Gp := by
        intro D hD
        rcases hD with rfl | rfl | hD
        · exact hCI
        · exact hiI
        · rw [Set.mem_singleton_iff] at hD
          rw [hD]
          exact hjI
      have h3 : Set.ncard ({C, ConjClasses.mk (⟨i, hi⟩ : ↥Gp),
          ConjClasses.mk (⟨j, hj⟩ : ↥Gp)} : Set (ConjClasses ↥Gp)) = 3 := by
        rw [Set.ncard_insert_of_notMem, Set.ncard_pair hne]
        rintro (h | h)
        · exact hiC h.symm
        · exact hjC (Set.mem_singleton_iff.mp h).symm
      have hle := Set.ncard_le_ncard hsub (Set.toFinite _)
      omega
  obtain ⟨c, hc⟩ := isConj_iff.mp (ConjClasses.mk_eq_mk_iff_isConj.mp hconj)
  exact ⟨(c : E), c.2, congrArg Subtype.val hc⟩

variable {Y : Type} [Group Y] {β : Cpl M₁ M₂ Y} {M : Type} [Group M] {ε : Y →* M} {z : M}

theorem burnsideF4m_theta_S_le {K' : Type} [Group K'] [Finite E]
    (hyp : HypF_4_4 κ 2 f Gp M₁ M₂) (θ : E ≃* K') {N1 N2 : Subgroup K'}
    (h1 : ∀ e, θ e ∈ N1 ↔ e ∈ M₁) (h2 : ∀ e, θ e ∈ N2 ↔ e ∈ M₂) {T : Subgroup K'}
    (hT : IsSylowTwoOf T ⊤) (hT1 : T ≤ N1) (hT2 : T ≤ N2) {s : E}
    (hs : s ∈ pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂))) : θ s ∈ T := by
  have hT' := burnsideF4m_isSylowTwoOf_map_inj θ.symm.toMonoidHom θ.symm.injective hT
  have htop : (⊤ : Subgroup K').map θ.symm.toMonoidHom = ⊤ := by
    rw [← MonoidHom.range_eq_map]
    exact MonoidHom.range_eq_top.mpr θ.symm.surjective
  rw [htop] at hT'
  have hle : T.map θ.symm.toMonoidHom ≤ M₁ ⊓ M₂ := by
    rintro _ ⟨t, ht, rfl⟩
    refine ⟨(h1 _).mp ?_, (h2 _).mp ?_⟩
    · show θ (θ.symm t) ∈ N1
      rw [MulEquiv.apply_symm_apply]
      exact hT1 ht
    · show θ (θ.symm t) ∈ N2
      rw [MulEquiv.apply_symm_apply]
      exact hT2 ht
  have hS := burnsideF4j_S_le_sylow hyp (F7.isSylowTwoOf_mono_right hT' hle le_top) hs
  obtain ⟨t, ht, hts⟩ := hS
  have : t = θ s := by
    rw [← hts]
    simp
  rw [← this]
  exact ht

theorem burnsideF4m_F_4_35_of_lieK {K' : Type} [Group K'] [Finite K']
    (hyp : HypF_4_31 κ f Gp M₁ M₂ β ε z) (hL3 : κ ≠ .L3) (hSp : κ ≠ .Sp4)
    (θ : E ≃* K') {N1 N2 : Subgroup K'} (h1 : ∀ e, θ e ∈ N1 ↔ e ∈ M₁)
    (h2 : ∀ e, θ e ∈ N2 ↔ e ∈ M₂) {T : Subgroup K'} {I : Finset K'} {z₀ : K'}
    (L : F431LieK T N1 N2 I z₀)
    (hnf : ∀ i ∈ I, ∀ j ∈ I, i ≠ j →
      ¬ IsConj (amalgamMap ((burnsideF4d_bOne β ε).comp (burnsideF4m_psi θ h1))
          ((burnsideF4d_bTwo β ε).comp (burnsideF4m_psi θ h2)) i)
        (amalgamMap ((burnsideF4d_bOne β ε).comp (burnsideF4m_psi θ h1))
          ((burnsideF4d_bTwo β ε).comp (burnsideF4m_psi θ h2)) j))
    (i j : ↥(M₁ ⊓ M₂)) (hi : (i : E) ∈ pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)))
    (hj : (j : E) ∈ pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂))) (hi1 : i ≠ 1) (hi2 : i * i = 1)
    (hj1 : j ≠ 1) (hj2 : j * j = 1) :
    ((∃ g ∈ Gp, g * (i : E) * g⁻¹ = (j : E)) ↔ IsConj (bM β ε i) (bM β ε j)) := by
  haveI := hyp.amalgam.finite
  refine ⟨burnsideF4j_F_4_35_forward hyp i j hi hj, fun h => ?_⟩
  obtain ⟨hC, -, -, -⟩ := burnsideF4m_comp_data hyp θ h1 h2
  have hiT := burnsideF4m_theta_S_le hyp.amalgam θ h1 h2 L.sylow L.T_le₁ L.T_le₂ hi
  have hjT := burnsideF4m_theta_S_le hyp.amalgam θ h1 h2 L.sylow L.T_le₁ L.T_le₂ hj
  have hord : ∀ x : ↥(M₁ ⊓ M₂), x ≠ 1 → x * x = 1 → orderOf (θ (x : E)) = 2 := by
    intro x hx1 hx2
    refine orderOf_eq_prime ?_ ?_
    · rw [pow_two, ← map_mul]
      have : (x : E) * x = 1 := congrArg Subtype.val hx2
      rw [this, map_one]
    · intro h0
      apply hx1
      apply Subtype.ext
      exact θ.injective (h0.trans (map_one θ).symm)
  have hφ : ∀ (x : ↥(M₁ ⊓ M₂)) (hx : θ (x : E) ∈ N1),
      amalgamMap ((burnsideF4d_bOne β ε).comp (burnsideF4m_psi θ h1))
        ((burnsideF4d_bTwo β ε).comp (burnsideF4m_psi θ h2)) (θ (x : E)) = bM β ε x := by
    intro x hx
    rw [amalgamMap_of_mem₁ _ _ hx]
    show burnsideF4d_bOne β ε (burnsideF4m_psi θ h1 ⟨θ x, hx⟩) =
      burnsideF4d_bOne β ε ⟨x, x.2.1⟩
    congr 1
    exact Subtype.ext (by rw [burnsideF4m_psi_apply]; simp)
  have hK := (L.lemma_F435 hC hnf hiT hjT (hord i hi1 hi2) (hord j hj1 hj2)).mpr (by
    rw [hφ i (L.T_le₁ hiT), hφ j (L.T_le₁ hjT)]
    exact h)
  have hE : IsConj (i : E) (j : E) := by
    obtain ⟨c, hc⟩ := isConj_iff.mp hK
    refine isConj_iff.mpr ⟨θ.symm c, θ.injective ?_⟩
    simp only [map_mul, map_inv, MulEquiv.apply_symm_apply]
    exact hc
  have hiG : (i : E) ∈ Gp := (CFSG.LieType.BorelTits.pCoreOf_le 2 _ hi).1
  have hjG : (j : E) ∈ Gp := (CFSG.LieType.BorelTits.pCoreOf_le 2 _ hj).1
  exact burnsideF4m_isConj_Gp_of_two hyp.amalgam hL3 hSp hyp.not_G2d hiG hjG
    (fun h0 => hi1 (Subtype.ext h0)) (congrArg Subtype.val hi2) hE

end Fusion

end CFSG.ASVolI
