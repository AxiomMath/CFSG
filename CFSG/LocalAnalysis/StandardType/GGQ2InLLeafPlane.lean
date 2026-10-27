module

public import CFSG.LocalAnalysis.StandardType.GGQ2InLCoverFrame
public import CFSG.LocalAnalysis.StandardType.GGQ2ClassicalCatalogueU
public import CFSG.LocalAnalysis.StandardType.GGQ2PlaneChain
import CFSG.LocalAnalysis.StandardType.GGQ2PlaneChainProofs

public section

namespace CFSG.StandardType.GGQ2Frame

open CFSG CFSG.Assembly Module

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private theorem ilp_leafModelOn_congr {t : ℕ}
    {Na Nb : Subgroup (PlaneRaw.V t ≃ₗ[PlaneRaw.F] PlaneRaw.V t)} {vx vx' z z' : PlaneRaw.V t}
    (hv : Submodule.span PlaneRaw.F {vx} = Submodule.span PlaneRaw.F {vx'})
    (hz : Submodule.span PlaneRaw.F {z} = Submodule.span PlaneRaw.F {z'}) :
    PlaneRaw.LeafModelOn t Na Nb vx z ↔ PlaneRaw.LeafModelOn t Na Nb vx' z' := by
  simp only [PlaneRaw.LeafModelOn, hv, hz]

private lemma ilp_sq_eq_one (a : PlaneRaw.F) (ha : a ≠ 0) : a * a = 1 := by
  revert a
  decide

private lemma ilp_eq_one_or_neg_one (a : PlaneRaw.F) (ha : a ≠ 0) : a = 1 ∨ a = -1 := by
  revert a
  decide

private lemma ilp_add_eq_of_ne_zero {x y : PlaneRaw.F} (hx : x ≠ 0) (hy : y ≠ 0)
    (hxy : x + y ≠ 0) : x = y := by
  revert x y
  decide

private lemma ilp_orientEquiv_neg_apply {t : ℕ} {e : PlaneRaw.V t} (he : ∀ i, e i ≠ 0)
    (v : PlaneRaw.V t) :
    PlaneRaw.orientEquiv t (-e) v = - PlaneRaw.orientEquiv t e v := by
  funext i
  rcases ilp_eq_one_or_neg_one (e i) (he i) with h | h
  · have h' : -e i = -1 := by rw [h]
    have h'' : ¬ (e i = -1) := by rw [h]; decide
    simp only [PlaneRaw.orientEquiv, LinearEquiv.piCongrRight_apply, Pi.neg_apply]
    rw [if_pos h', if_neg h'']
    simp
  · have h' : ¬ (-e i = -1) := by rw [h]; decide
    have h'' : e i = -1 := h
    simp only [PlaneRaw.orientEquiv, LinearEquiv.piCongrRight_apply, Pi.neg_apply]
    rw [if_neg h', if_pos h'']
    simp

private lemma ilp_orientEquiv_neg_symm_apply {t : ℕ} {e : PlaneRaw.V t} (he : ∀ i, e i ≠ 0)
    (w : PlaneRaw.V t) :
    (PlaneRaw.orientEquiv t (-e))⁻¹ w = - (PlaneRaw.orientEquiv t e)⁻¹ w := by
  change (PlaneRaw.orientEquiv t (-e)).symm w = - (PlaneRaw.orientEquiv t e).symm w
  apply (PlaneRaw.orientEquiv t (-e)).injective
  rw [LinearEquiv.apply_symm_apply, ilp_orientEquiv_neg_apply he]
  simp

private lemma ilp_swapTwist_neg {t : ℕ} {e : PlaneRaw.V t} (he : ∀ i, e i ≠ 0) (i j : Fin t) :
    PlaneRaw.swapTwist t (-e) i j = PlaneRaw.swapTwist t e i j := by
  apply LinearEquiv.ext
  intro v
  rw [PlaneRaw.swapTwist, PlaneRaw.swapTwist, LinearEquiv.mul_apply, LinearEquiv.mul_apply,
    LinearEquiv.mul_apply, LinearEquiv.mul_apply]
  rw [ilp_orientEquiv_neg_apply he, map_neg, map_neg, ilp_orientEquiv_neg_symm_apply he]
  simp

private lemma ilp_twistedPermGroupOn_smul {t : ℕ} {e : PlaneRaw.V t} (he : ∀ i, e i ≠ 0)
    {c : PlaneRaw.F} (hc : c ≠ 0) :
    PlaneRaw.twistedPermGroupOn t (c • e) = PlaneRaw.twistedPermGroupOn t e := by
  rcases ilp_eq_one_or_neg_one c hc with rfl | hc
  · simp
  · rw [hc, neg_one_smul]
    unfold PlaneRaw.twistedPermGroupOn
    congr 1
    ext T
    simp only [Set.mem_setOf_eq]
    constructor
    · rintro ⟨i, j, hi, hj, rfl⟩
      exact ⟨i, j, by simpa using hi, by simpa using hj, ilp_swapTwist_neg he i j⟩
    · rintro ⟨i, j, hi, hj, rfl⟩
      exact ⟨i, j, by simpa using hi, by simpa using hj, (ilp_swapTwist_neg he i j).symm⟩

private lemma ilp_span_singleton_eq_of_mem {t : ℕ} {v w : PlaneRaw.V t} (hv : v ≠ 0)
    (hw : w ∈ Submodule.span PlaneRaw.F {v}) (hw0 : w ≠ 0) :
    Submodule.span PlaneRaw.F {v} = Submodule.span PlaneRaw.F {w} :=
  eq_span_singleton_of_mem_of_finrank_eq_one (by rw [finrank_span_singleton hv]) hw hw0

private lemma ilp_zero_cent {t : ℕ} {k : PlaneRaw.PlaneKind} {S : Finset (Fin t)}
    {z : PlaneRaw.V t} (hz : z ≠ 0)
    (h : PlaneRaw.cent k (PlaneRaw.Code.zero S) = Submodule.span PlaneRaw.F {z}) :
    ∃ i₁ : Fin t, S = Finset.univ.erase i₁ ∧
      Submodule.span PlaneRaw.F {z} =
        Submodule.span PlaneRaw.F {Pi.single i₁ (1 : PlaneRaw.F)} := by
  have hdelta : ∀ i, i ∉ S → Pi.single i (1 : PlaneRaw.F) ∈ Submodule.span PlaneRaw.F {z} := by
    intro i hi
    rw [← h, PlaneRaw.mem_cent_zero]
    intro j hj
    exact Pi.single_eq_of_ne (fun hji : j = i => hi (hji ▸ hj)) 1
  have hex : ∃ i, i ∉ S := by
    by_contra hall
    have hall' : ∀ i, i ∈ S := by
      intro i
      by_contra hmem
      exact hall ⟨i, hmem⟩
    have hSup : S = Finset.univ := Finset.eq_univ_of_forall hall'
    have hzmem : z ∈ PlaneRaw.cent k (PlaneRaw.Code.zero S) := by
      rw [h]
      exact Submodule.mem_span_singleton_self z
    have hzero : ∀ i ∈ S, z i = 0 := (PlaneRaw.mem_cent_zero k S z).mp hzmem
    refine hz (funext fun i => ?_)
    exact hzero i (by simp [hSup])
  obtain ⟨i₁, hi₁⟩ := hex
  have huniq : ∀ i, i ∉ S → i = i₁ := by
    intro i hi
    by_contra hne
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp (hdelta i hi)
    obtain ⟨b, hb⟩ := Submodule.mem_span_singleton.mp (hdelta i₁ hi₁)
    have hai : a * z i = 1 := by
      have hh := congrFun ha i
      simpa [Pi.single_eq_same] using hh
    have ha1 : a * z i₁ = 0 := by
      have hh := congrFun ha i₁
      rw [Pi.single_eq_of_ne (Ne.symm hne) 1] at hh
      simpa using hh
    have hb1 : b * z i₁ = 1 := by
      have hh := congrFun hb i₁
      simpa [Pi.single_eq_same] using hh
    have hz1 : z i₁ ≠ 0 := by
      intro h0
      rw [h0, mul_zero] at hb1
      exact zero_ne_one hb1
    rcases mul_eq_zero.mp ha1 with h0 | h0
    · rw [h0, zero_mul] at hai
      exact zero_ne_one hai
    · exact hz1 h0
  refine ⟨i₁, ?_, ?_⟩
  · ext i
    rw [Finset.mem_erase]
    simp only [Finset.mem_univ, and_true]
    constructor
    · intro hi
      exact fun h => hi₁ (h ▸ hi)
    · intro hi
      by_contra hmem
      exact hi (huniq i hmem)
  · apply eq_span_singleton_of_mem_of_finrank_eq_one
      (by rw [finrank_span_singleton hz]) (hdelta i₁ hi₁)
    intro hzero
    have := congrFun hzero i₁
    simp at this

private lemma ilp_update_eq_add_single {t : ℕ} (e : PlaneRaw.V t) (i₀ : Fin t) :
    Function.update e i₀ (-e i₀) = e + (e i₀) • Pi.single i₀ (1 : PlaneRaw.F) := by
  funext i
  by_cases hi : i = i₀
  · subst hi
    rw [Function.update_apply, if_pos rfl, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      Pi.single_eq_same]
    have h2 : (2 : ZMod 3) = -1 := by decide
    rw [show e i + e i * 1 = -e i from by
      calc e i + e i * 1 = 2 * e i := by ring
        _ = -1 * e i := by rw [h2]
        _ = -e i := by ring]
  · rw [Function.update_apply, if_neg hi, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      Pi.single_eq_of_ne hi, mul_zero, add_zero]

private theorem ilp_planeEntry_raw {k : PlaneRaw.PlaneKind} {t : ℕ}
    (hZ : 4 ≤ t → ∀ e : PlaneRaw.V t, (∀ i, e i ≠ 0) → ∀ i₁ : Fin t,
      PlaneRaw.LeafModelOn t (PlaneRaw.twistedPermGroupOn t e)
        (PlaneRaw.normalizerOf k t (.zero (Finset.univ.erase i₁))) e (Pi.single i₁ 1)) :
    ∀ vx : PlaneRaw.V t, vx ≠ 0 →
    ∀ ℓ : PlaneRaw.Code t, 4 ≤ t ∧ PlaneRaw.admissible k ℓ →
      (∃ lab : LargeEvenLabel, GGLabQTwo 3 lab ∧ GGLabelIso lab (PlaneRaw.label k ℓ)) →
      PlaneRaw.occurs (Submodule.span PlaneRaw.F {vx}) ℓ →
      PlaneRaw.cent k ℓ = Submodule.span PlaneRaw.F {vx} → vx ∈ PlaneRaw.inside k ℓ →
    ∀ U : Submodule PlaneRaw.F (PlaneRaw.V t), finrank PlaneRaw.F U = 2 → vx ∈ U →
    ∀ j : PlaneRaw.Code t, 4 ≤ t ∧ PlaneRaw.admissible k j →
      PlaneRaw.occurs U j → PlaneRaw.cent k j = U → PlaneRaw.inside k j ≤ PlaneRaw.inside k ℓ →
      PlaneRaw.normalizerOf k t j ≤ PlaneRaw.normalizerOf k t ℓ →
    ∀ z ∈ U, z ∉ Submodule.span PlaneRaw.F {vx} →
    ∀ c : PlaneRaw.Code t,
      (4 ≤ t ∧ PlaneRaw.admissible k c) ∧
        PlaneRaw.occurs (Submodule.span PlaneRaw.F {z}) c ∧
        PlaneRaw.cent k c = Submodule.span PlaneRaw.F {z} ∧
        PlaneRaw.normalizerOf k t j ≤ PlaneRaw.normalizerOf k t c ∧
        vx ∉ PlaneRaw.cent k c →
      PlaneRaw.inside k j ≤ PlaneRaw.inside k c →
      PlaneRaw.LeafModelOn t (PlaneRaw.normalizerOf k t ℓ) (PlaneRaw.normalizerOf k t c) vx z := by
  intro vx hvx ℓ hℓ _ _ hcent hin U hU hvxU j hj _ hcentj _ _ z hzU hz c hc _
  obtain ⟨h4t, hℓadm⟩ := hℓ
  have hz0 : z ≠ 0 := by
    intro h
    apply hz
    rw [h]
    exact Submodule.zero_mem _
  cases ℓ with
  | zero S =>
      exfalso
      have hvcent : vx ∈ PlaneRaw.cent k (PlaneRaw.Code.zero S) := by
        rw [hcent]
        exact Submodule.mem_span_singleton_self vx
      have hvzero : ∀ i ∈ S, vx i = 0 := (PlaneRaw.mem_cent_zero k S vx).mp hvcent
      have hsupp : PlaneRaw.vSupport vx ⊆ S := (PlaneRaw.mem_inside_zero k S vx).mp hin
      have hne : ∃ i, vx i ≠ 0 := by
        by_contra h
        apply hvx
        funext i
        by_contra hi
        exact h ⟨i, hi⟩
      obtain ⟨i, hi⟩ := hne
      have hiS : i ∈ PlaneRaw.vSupport vx := by simpa [PlaneRaw.vSupport] using hi
      exact hi (hvzero i (hsupp hiS))
  | extension e =>
      have he : e ≠ 0 := hℓadm.1
      have hcard : (PlaneRaw.Code.extSupport e).card = t := by
        have hfr := PlaneRaw.finrank_cent_extension k e he
        rw [hcent, finrank_span_singleton hvx] at hfr
        have hle : (PlaneRaw.Code.extSupport e).card ≤ t := by
          simpa using Finset.card_le_univ (PlaneRaw.Code.extSupport e)
        omega
      have hsupp_univ : PlaneRaw.Code.extSupport e = Finset.univ :=
        Finset.eq_univ_of_card _ (by simpa using hcard)
      have hei : ∀ i, e i ≠ 0 := by
        intro i
        have hi : i ∈ PlaneRaw.Code.extSupport e := by
          rw [hsupp_univ]
          exact Finset.mem_univ i
        simpa using hi
      have he_cent : e ∈ PlaneRaw.cent k (PlaneRaw.Code.extension e) := by
        rw [PlaneRaw.mem_cent_extension]
        intro i _ j _
        rw [ilp_sq_eq_one (e i) (hei i), ilp_sq_eq_one (e j) (hei j)]
      have he_mem : e ∈ Submodule.span PlaneRaw.F {vx} := by
        rw [← hcent]
        exact he_cent
      have hspan_vx_e : Submodule.span PlaneRaw.F {vx} = Submodule.span PlaneRaw.F {e} :=
        ilp_span_singleton_eq_of_mem hvx he_mem he
      have hz_not_e : z ∉ Submodule.span PlaneRaw.F {e} := by
        rw [← hspan_vx_e]
        exact hz
      have he_U : e ∈ U := by
        have hle : Submodule.span PlaneRaw.F {vx} ≤ U :=
          Submodule.span_le.mpr (by rintro w rfl; exact hvxU)
        exact hle he_mem
      obtain ⟨hcadm, -, hccent, -, -⟩ := hc
      show PlaneRaw.LeafModelOn t (PlaneRaw.twistedPermGroupOn t e)
        (PlaneRaw.normalizerOf k t c) vx z
      cases c with
      | zero S'' =>
          obtain ⟨i₁, hS'', hspan_z⟩ := ilp_zero_cent hz0 hccent
          rw [hS'']
          exact (ilp_leafModelOn_congr hspan_vx_e hspan_z).mpr (hZ h4t e hei i₁)
      | extension e'' =>
          have he'' : e'' ≠ 0 := hcadm.2.1
          show PlaneRaw.LeafModelOn t (PlaneRaw.twistedPermGroupOn t e)
            (PlaneRaw.twistedPermGroupOn t e'') vx z
          have hcard'' : (PlaneRaw.Code.extSupport e'').card = t := by
            have hfr := PlaneRaw.finrank_cent_extension k e'' he''
            rw [hccent, finrank_span_singleton hz0] at hfr
            have hle : (PlaneRaw.Code.extSupport e'').card ≤ t := by
              simpa using Finset.card_le_univ (PlaneRaw.Code.extSupport e'')
            omega
          have hsupp'' : PlaneRaw.Code.extSupport e'' = Finset.univ :=
            Finset.eq_univ_of_card _ (by simpa using hcard'')
          have hei'' : ∀ i, e'' i ≠ 0 := by
            intro i
            have hi : i ∈ PlaneRaw.Code.extSupport e'' := by
              rw [hsupp'']
              exact Finset.mem_univ i
            simpa using hi
          have he''_cent : e'' ∈ PlaneRaw.cent k (PlaneRaw.Code.extension e'') := by
            rw [PlaneRaw.mem_cent_extension]
            intro i _ j _
            rw [ilp_sq_eq_one (e'' i) (hei'' i), ilp_sq_eq_one (e'' j) (hei'' j)]
          have he''_mem : e'' ∈ Submodule.span PlaneRaw.F {z} := by
            rw [← hccent]
            exact he''_cent
          have hspan_z_e'' : Submodule.span PlaneRaw.F {z} = Submodule.span PlaneRaw.F {e''} :=
            ilp_span_singleton_eq_of_mem hz0 he''_mem he''
          have hzfull : ∀ i, z i ≠ 0 := by
            have hzmem : z ∈ Submodule.span PlaneRaw.F {e''} := by
              rw [← hspan_z_e'']
              exact Submodule.mem_span_singleton_self z
            obtain ⟨ν, hν⟩ := Submodule.mem_span_singleton.mp hzmem
            have hν0 : ν ≠ 0 := by
              intro h0
              apply hz0
              rw [← hν, h0, zero_smul]
            intro i
            have hzi : z i = ν * e'' i := by
              have hh := congrFun hν i
              simpa using hh.symm
            rw [hzi]
            exact mul_ne_zero hν0 (hei'' i)
          cases j with
          | zero S' =>
              exfalso
              have he_cent' : e ∈ PlaneRaw.cent k (PlaneRaw.Code.zero S') := by
                rw [hcentj]
                exact he_U
              have hS' : S' = ∅ := by
                apply Finset.eq_empty_iff_forall_notMem.mpr
                intro i hi
                exact hei i ((PlaneRaw.mem_cent_zero k S' e).mp he_cent' i hi)
              have hUtop : U = ⊤ := by
                rw [← hcentj, hS', Submodule.eq_top_iff']
                intro v
                rw [PlaneRaw.mem_cent_zero]
                intro i hi
                exact absurd hi (by simp)
              have hdt : finrank PlaneRaw.F U = t := by
                rw [hUtop, finrank_top]
                simp
              rw [hdt] at hU
              omega
          | extension e' =>
              have he' : e' ≠ 0 := hj.2.1
              have hcard' : (PlaneRaw.Code.extSupport e').card = t - 1 := by
                have hfr := PlaneRaw.finrank_cent_extension k e' he'
                rw [hcentj, hU] at hfr
                have hle : (PlaneRaw.Code.extSupport e').card ≤ t := by
                  simpa using Finset.card_le_univ (PlaneRaw.Code.extSupport e')
                omega
              have hcompl : (PlaneRaw.Code.extSupport e')ᶜ.card = 1 := by
                rw [Finset.card_compl, Fintype.card_fin, hcard']
                omega
              obtain ⟨i₀, hi₀⟩ := Finset.card_eq_one.mp hcompl
              have hi₀T : i₀ ∉ PlaneRaw.Code.extSupport e' := by
                have h : i₀ ∈ (PlaneRaw.Code.extSupport e')ᶜ := by rw [hi₀]; simp
                simpa using h
              have hT : PlaneRaw.Code.extSupport e' = Finset.univ.erase i₀ := by
                ext i
                rw [Finset.mem_erase]
                constructor
                · intro hi
                  exact ⟨fun h => hi₀T (h ▸ hi), Finset.mem_univ i⟩
                · rintro ⟨hne, -⟩
                  by_contra hmem
                  have h : i ∈ (PlaneRaw.Code.extSupport e')ᶜ := by simpa using hmem
                  rw [hi₀] at h
                  exact hne (by simpa using h)
              have hTpos : 0 < (PlaneRaw.Code.extSupport e').card := by omega
              obtain ⟨i₁, hi₁T⟩ := Finset.card_pos.mp hTpos
              have he'_cent : e ∈ PlaneRaw.cent k (PlaneRaw.Code.extension e') := by
                rw [hcentj]
                exact he_U
              have hz_cent : z ∈ PlaneRaw.cent k (PlaneRaw.Code.extension e') := by
                rw [hcentj]
                exact hzU
              have hcent_e : ∀ i ∈ PlaneRaw.Code.extSupport e', ∀ j ∈ PlaneRaw.Code.extSupport e',
                  e' i * e i = e' j * e j :=
                (PlaneRaw.mem_cent_extension k e' e).mp he'_cent
              have hcent_z : ∀ i ∈ PlaneRaw.Code.extSupport e', ∀ j ∈ PlaneRaw.Code.extSupport e',
                  e' i * z i = e' j * z j :=
                (PlaneRaw.mem_cent_extension k e' z).mp hz_cent
              obtain ⟨α, hα⟩ : ∃ α : PlaneRaw.F, α = z i₁ / e i₁ := ⟨_, rfl⟩
              have hei₁ : e i₁ ≠ 0 := hei i₁
              have hα_e : z i₁ = α * e i₁ := by
                rw [hα]
                exact (div_mul_cancel₀ (z i₁) hei₁).symm
              have he'i₁ : e' i₁ ≠ 0 := by simpa using hi₁T
              have hαj : ∀ j, j ∈ PlaneRaw.Code.extSupport e' → z j = α * e j := by
                intro j hj
                have he'j : e' j ≠ 0 := by simpa using hj
                have hzeq : e' j * z j = e' j * (α * e j) := by
                  calc e' j * z j = e' i₁ * z i₁ := (hcent_z i₁ hi₁T j hj).symm
                    _ = e' i₁ * (α * e i₁) := by rw [hα_e]
                    _ = α * (e' i₁ * e i₁) := by ring
                    _ = α * (e' j * e j) := by rw [hcent_e i₁ hi₁T j hj]
                    _ = e' j * (α * e j) := by ring
                exact mul_left_cancel₀ he'j hzeq
              obtain ⟨β, hβ⟩ : ∃ β : PlaneRaw.F, β = z i₀ - α * e i₀ := ⟨_, rfl⟩
              have hzrep : z = α • e + β • Pi.single i₀ (1 : PlaneRaw.F) := by
                funext i
                by_cases hi : i = i₀
                · subst hi
                  rw [hβ, Pi.add_apply, Pi.smul_apply, Pi.smul_apply, smul_eq_mul,
                    smul_eq_mul, Pi.single_eq_same, mul_one]
                  ring
                · have hiT : i ∈ PlaneRaw.Code.extSupport e' := by
                    rw [hT, Finset.mem_erase]
                    exact ⟨hi, Finset.mem_univ i⟩
                  rw [hαj i hiT, Pi.add_apply, Pi.smul_apply, Pi.smul_apply, smul_eq_mul,
                    smul_eq_mul, Pi.single_eq_of_ne hi, mul_zero, add_zero]
              have hβ0 : β ≠ 0 := by
                intro h0
                apply hz_not_e
                rw [hzrep, h0, zero_smul, add_zero]
                exact Submodule.smul_mem _ α (Submodule.subset_span (Set.mem_singleton e))
              have hα0 : α ≠ 0 := by
                intro h0
                have hzi : z i₁ = 0 := by rw [hα_e, h0, zero_mul]
                exact hzfull i₁ hzi
              have hαe0 : α * e i₀ ≠ 0 := mul_ne_zero hα0 (hei i₀)
              have hsum : α * e i₀ + β ≠ 0 := by
                have hzi₀ : z i₀ = α * e i₀ + β := by
                  have hh := congrFun hzrep i₀
                  simpa [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.single_eq_same] using hh
                rw [← hzi₀]
                exact hzfull i₀
              have hβeq : β = α * e i₀ := by
                apply ilp_add_eq_of_ne_zero hβ0 hαe0
                rwa [add_comm]
              have hzeq : z = α • Function.update e i₀ (-e i₀) := by
                rw [hzrep, ilp_update_eq_add_single, smul_add, hβeq, smul_smul]
              have hestar : ∀ i, Function.update e i₀ (-e i₀) i ≠ 0 := by
                intro i
                by_cases hi : i = i₀
                · subst hi
                  simpa [Function.update_apply] using neg_ne_zero.mpr (hei i)
                · simpa [Function.update_apply, hi] using hei i
              have hestar0 : Function.update e i₀ (-e i₀) ≠ 0 := by
                intro h0
                exact hestar i₀ (congrFun h0 i₀)
              have hspan_z_estar : Submodule.span PlaneRaw.F {z}
                  = Submodule.span PlaneRaw.F {Function.update e i₀ (-e i₀)} := by
                apply eq_span_singleton_of_mem_of_finrank_eq_one
                  (by rw [finrank_span_singleton hz0]) ?_ hestar0
                rw [Submodule.mem_span_singleton]
                exact ⟨α⁻¹, by rw [hzeq, smul_smul, inv_mul_cancel₀ hα0, one_smul]⟩
              have he''_mem2 : e'' ∈ Submodule.span PlaneRaw.F
                  {Function.update e i₀ (-e i₀)} := by
                rw [← hspan_z_estar, hspan_z_e'']
                exact Submodule.mem_span_singleton_self e''
              obtain ⟨ν, hν⟩ := Submodule.mem_span_singleton.mp he''_mem2
              have hν0 : ν ≠ 0 := by
                intro h0
                apply he''
                rw [← hν, h0, zero_smul]
              have hgroup : PlaneRaw.twistedPermGroupOn t e''
                  = PlaneRaw.twistedPermGroupOn t (Function.update e i₀ (-e i₀)) := by
                rw [← hν]
                exact ilp_twistedPermGroupOn_smul hestar hν0
              rw [hgroup]
              exact (ilp_leafModelOn_congr hspan_vx_e hspan_z_estar).mpr
                (PlaneRaw.leafModelFlip_holds _ h4t _ hei i₀)

theorem inLLeafCases_planeEntry {k : PlaneRaw.PlaneKind} {t : ℕ}
    (hZ : 4 ≤ t → ∀ e : PlaneRaw.V t, (∀ i, e i ≠ 0) → ∀ i₁ : Fin t,
      PlaneRaw.LeafModelOn t (PlaneRaw.twistedPermGroupOn t e)
        (PlaneRaw.normalizerOf k t (.zero (Finset.univ.erase i₁))) e (Pi.single i₁ 1)) :
    InLLeafCases (planeEntry k t) := by
  intro vx hvx ℓ hℓ hlab hocc hcent hin U hU hvxU j hj hoccj hcentj hinj hNj z hzU hz c hc hinc
  exact ilp_planeEntry_raw hZ vx hvx ℓ hℓ hlab hocc hcent hin U hU hvxU j hj hoccj hcentj hinj
    hNj z hzU hz c hc hinc

theorem inLLeafCases_symp (t : ℕ) : InLLeafCases (classicalCatalogue (.symp t)) := by
  change InLLeafCases (planeEntry .symplectic t)
  refine inLLeafCases_planeEntry (k := .symplectic) (t := t) ?_
  intro ht e he i₁
  have hcard : (Finset.univ.erase i₁ : Finset (Fin t)).card = t - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ i₁), Finset.card_univ, Fintype.card_fin]
  have hne : (Finset.univ.erase i₁ : Finset (Fin t)).card ≠ 2 := by
    rw [hcard]
    omega
  have hnorm : PlaneRaw.normalizerOf .symplectic t (.zero (Finset.univ.erase i₁))
      = PlaneRaw.signedPermGroupOn t (Finset.univ.erase i₁) := by
    simp only [PlaneRaw.normalizerOf]
    rw [if_neg hne]
  rw [hnorm]
  exact PlaneRaw.leafModelSigned_holds _ ht _ he i₁

theorem inLLeafCases_orth (t : ℕ) (δ : Fin 2) : InLLeafCases (classicalCatalogue (.orth t δ)) := by
  change InLLeafCases (planeEntry (.orthogonal δ) t)
  refine inLLeafCases_planeEntry (k := .orthogonal δ) (t := t) ?_
  intro ht e he i₁
  have hnorm : PlaneRaw.normalizerOf (.orthogonal δ) t (.zero (Finset.univ.erase i₁))
      = if δ.val = 0 then PlaneRaw.evenSignedPermGroupOn t (Finset.univ.erase i₁)
        else PlaneRaw.signedPermGroupOn t (Finset.univ.erase i₁) := by
    simp only [PlaneRaw.normalizerOf]
  rw [hnorm]
  by_cases hδ : δ.val = 0
  · rw [if_pos hδ]
    exact PlaneRaw.leafModelEvenSigned_holds _ ht _ he i₁
  · rw [if_neg hδ]
    exact PlaneRaw.leafModelSigned_holds _ ht _ he i₁

end CFSG.StandardType.GGQ2Frame

end
