module

public import CFSG.RankThree.GF2n.Smith81.S81ZModelId
public import CFSG.RankThree.GF2n.Smith81.S81VGenBridge
public import CFSG.RankThree.GF2n.Smith81.S81XE7Geom

public noncomputable section

namespace CFSG.RankThree.GF2n.Smith81.S81Z

open CFSG.LieType.Steinberg.Minuscule CFSG.Blueprint.Chevalley CFSG.LieType.Steinberg
  CFSG.LieType.Universal CFSG.LieType.RootSystem CFSG.LieType.CurtisTits
  CFSG.RankThree.GF2n.Smith81.XOps CFSG.RankThree.GF2n.Smith81.E7Model
  CFSG.RankThree.GF2n.Smith81.E7X CFSG.RankThree.GF2n.Smith81.Gen76


variable {K : Type} [Field K] [CharP K 2]

section Weights

theorem weight_eq_orbit (c : Fin e7Data.d) : ∃ n : Gp K, endoE n (w0 : V K) = Finsupp.single c 1 := by
  obtain ⟨n, σ, ρ, hm, hσ⟩ := exists_isMon_of_weight (K := K) c
  refine ⟨n, ?_⟩
  have := hm.weight ⟨0, by decide⟩
  rw [hσ] at this
  exact this

theorem spanM_top : Submodule.span K (Set.range fun g : Gp K => endoE g (w0 : V K)) = ⊤ := by
  rw [eq_top_iff, ← (Finsupp.basisSingleOne (R := K) (ι := Fin e7Data.d)).span_eq]
  refine Submodule.span_mono ?_
  rintro _ ⟨c, rfl⟩
  obtain ⟨n, hn⟩ := weight_eq_orbit (K := K) c
  exact ⟨n, by
    show endoE n (w0 : V K) = _
    rw [hn]
    simp [Finsupp.coe_basisSingleOne]⟩

theorem finrank_V56 : Module.finrank K (V K) = 56 := by
  rw [Module.finrank_finsupp_self, Fintype.card_fin]
  rfl

end Weights

section Plane

@[expose] def planeP (K : Type) [Field K] : Submodule K (V K) := Submodule.span K {(w0 : V K), sw0 K}

theorem w0_mem_planeP : (w0 : V K) ∈ planeP K := Submodule.subset_span (by simp)

theorem sw0_mem_planeP : sw0 K ∈ planeP K := Submodule.subset_span (by simp)

theorem mem_planeP {v : V K} : v ∈ planeP K ↔ ∃ a b : K, v = a • sw0 K + b • (w0 : V K) := by
  constructor
  · intro hv
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hv
    · rintro x (rfl | rfl)
      · exact ⟨0, 1, by simp⟩
      · exact ⟨1, 0, by simp⟩
    · exact ⟨0, 0, by simp⟩
    · rintro x y - - ⟨a, b, rfl⟩ ⟨a', b', rfl⟩
      exact ⟨a + a', b + b', by rw [add_smul, add_smul]; abel⟩
    · rintro c x - ⟨a, b, rfl⟩
      exact ⟨c * a, c * b, by rw [smul_add, smul_smul, smul_smul]⟩
  · rintro ⟨a, b, rfl⟩
    exact Submodule.add_mem _ (Submodule.smul_mem _ _ sw0_mem_planeP)
      (Submodule.smul_mem _ _ w0_mem_planeP)

@[expose] def Hsl (K : Type) [Field K] : Subgroup (Gp K) :=
  Subgroup.closure ({g | ∃ t : K, g = xE alpha7 t} ∪ {sN K})

theorem xE_mem_Hsl (t : K) : xE alpha7 t ∈ Hsl K :=
  Subgroup.subset_closure (Or.inl ⟨t, rfl⟩)

theorem sN_mem_Hsl : sN K ∈ Hsl K := Subgroup.subset_closure (Or.inr rfl)

theorem endoE_xE_alpha7_comb (t a b : K) :
    endoE (xE alpha7 t) (a • sw0 K + b • (w0 : V K)) = a • sw0 K + (b + a * t) • (w0 : V K) := by
  rw [map_add, map_smul, map_smul, endoE_xE_alpha7_sw0, endoE_xE_alpha7_w0, smul_add, add_smul,
    smul_smul]
  abel

theorem endoE_sN_comb (a b : K) :
    endoE (sN K) (a • sw0 K + b • (w0 : V K)) = b • sw0 K + a • (w0 : V K) := by
  rw [map_add, map_smul, map_smul, endoE_sN_sw0]
  show a • (w0 : V K) + b • sw0 K = _
  rw [add_comm]

theorem plane_stable {g : Gp K} (hg : g ∈ Hsl K) :
    (∀ v ∈ planeP K, endoE g v ∈ planeP K) ∧ ∀ v ∈ planeP K, endoE g⁻¹ v ∈ planeP K := by
  refine Subgroup.closure_induction (p := fun g _ => (∀ v ∈ planeP K, endoE g v ∈ planeP K) ∧
    ∀ v ∈ planeP K, endoE g⁻¹ v ∈ planeP K) ?_ ?_ ?_ ?_ hg
  · rintro g (⟨t, rfl⟩ | rfl)
    · have key : ∀ v ∈ planeP K, endoE (xE alpha7 t) v ∈ planeP K := by
        intro v hv
        obtain ⟨a, b, rfl⟩ := mem_planeP.1 hv
        rw [endoE_xE_alpha7_comb]
        exact mem_planeP.2 ⟨a, b + a * t, rfl⟩
      have hinv : endoE (xE alpha7 t)⁻¹ = endoE (xE alpha7 t) :=
        LinearMap.ext fun v => endoE_inv_xE t v
      refine ⟨key, fun v hv => ?_⟩
      rw [hinv]
      exact key v hv
    · have key : ∀ v ∈ planeP K, endoE (sN K) v ∈ planeP K := by
        intro v hv
        obtain ⟨a, b, rfl⟩ := mem_planeP.1 hv
        rw [endoE_sN_comb]
        exact mem_planeP.2 ⟨b, a, rfl⟩
      refine ⟨key, fun v hv => ?_⟩
      rw [sN_inv]
      exact key v hv
  · exact ⟨fun v hv => by rw [endoE_one, Module.End.one_apply]; exact hv,
      fun v hv => by rw [inv_one, endoE_one, Module.End.one_apply]; exact hv⟩
  · rintro x y - - ⟨hx1, hx2⟩ ⟨hy1, hy2⟩
    refine ⟨fun v hv => ?_, fun v hv => ?_⟩
    · rw [endoE_mul, Module.End.mul_apply]
      exact hx1 _ (hy1 v hv)
    · rw [mul_inv_rev, endoE_mul, Module.End.mul_apply]
      exact hy2 _ (hx2 v hv)
  · rintro x - ⟨hx1, hx2⟩
    refine ⟨fun v hv => ?_, fun v hv => ?_⟩
    · exact hx2 v hv
    · rw [inv_inv]
      exact hx1 v hv

end Plane

section Lines

abbrev L0E (K : Type) [Field K] : Set (Submodule K (V K)) :=
  rootLine (K := K) (e7Data_valid.sRefl node7 topIdx) topIdx

theorem single_sRefl_eq_sw0 :
    (Finsupp.single (e7Data_valid.sRefl node7 topIdx) (1 : K) : V K) = sw0 K := by
  rw [sw0_eq]

theorem mem_L0E {u : Submodule K (V K)} :
    u ∈ L0E K ↔ u = K ∙ (w0 : V K) ∨ ∃ t : K, u = K ∙ (sw0 K + t • (w0 : V K)) := by
  unfold L0E rootLine
  simp only [Set.mem_insert_iff, Set.mem_range]
  rw [single_sRefl_eq_sw0]
  constructor
  · rintro (h | ⟨t, rfl⟩)
    · exact Or.inl h
    · exact Or.inr ⟨t, rfl⟩
  · rintro (h | ⟨t, rfl⟩)
    · exact Or.inl h
    · exact Or.inr ⟨t, rfl⟩

theorem exists_vec_of_mem_L0E {z : Submodule K (V K)} (hz : z ∈ L0E K) :
    ∃ v ∈ planeP K, v ≠ 0 ∧ z = K ∙ v := by
  rcases mem_L0E.1 hz with rfl | ⟨t, rfl⟩
  · exact ⟨w0, w0_mem_planeP, w0_ne_zero, rfl⟩
  · refine ⟨sw0 K + t • (w0 : V K), mem_planeP.2 ⟨1, t, by rw [one_smul]⟩, ?_, rfl⟩
    intro h0
    apply sw0_notin_span (K := K)
    have : sw0 K = (-t) • (w0 : V K) := by
      have := congrArg (fun v => v - t • (w0 : V K)) h0
      simp only [add_sub_cancel_right, zero_sub] at this
      rw [this, neg_smul]
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)

variable (K) in
@[expose] def ptsE : Set (Submodule K (V K)) := Set.range fun g : Gp K => K ∙ endoE g (w0 : V K)

@[expose] def ptE (g : Gp K) : ↥(ptsE K) := ⟨K ∙ endoE g (w0 : V K), g, rfl⟩

theorem ptE_surjective : Function.Surjective (ptE (K := K)) := by
  rintro ⟨_, g, rfl⟩
  exact ⟨g, rfl⟩

theorem ptE_val (g : Gp K) : ((ptE g : ↥(ptsE K)) : Submodule K (V K)) = K ∙ endoE g (w0 : V K) := rfl

@[expose] def ColE (x y z : ↥(ptsE K)) : Prop :=
  ∃ 𝓛, IsLine (EGrp K) (L0E K) 𝓛 ∧ (x : Submodule K (V K)) ∈ 𝓛 ∧ (y : Submodule K (V K)) ∈ 𝓛 ∧
    (z : Submodule K (V K)) ∈ 𝓛

set_option maxRecDepth 20000 in
theorem endoE_xE_sN_w0 (t : K) : endoE (xE alpha7 t * sN K) (w0 : V K) = sw0 K + t • (w0 : V K) := by
  rw [endoE_mul, Module.End.mul_apply]
  exact endoE_xE_alpha7_sw0 t

theorem exists_g0 {u₁ u₂ : Submodule K (V K)} (h₁ : u₁ ∈ L0E K) (h₂ : u₂ ∈ L0E K) (hne : u₁ ≠ u₂) :
    ∃ g₀ ∈ Hsl K, K ∙ endoE g₀ (w0 : V K) = u₁ ∧ K ∙ endoE (g₀ * sN K) (w0 : V K) = u₂ := by
  rcases mem_L0E.1 h₁ with rfl | ⟨t, rfl⟩ <;> rcases mem_L0E.1 h₂ with rfl | ⟨u, rfl⟩
  · exact absurd rfl hne
  · refine ⟨xE alpha7 u, xE_mem_Hsl u, ?_, ?_⟩
    · rw [endoE_xE_alpha7_w0]
    · rw [endoE_xE_sN_w0]
  · refine ⟨xE alpha7 t * sN K, (Hsl K).mul_mem (xE_mem_Hsl t) sN_mem_Hsl, ?_, ?_⟩
    · rw [endoE_xE_sN_w0]
    · rw [mul_assoc, sN_sq, mul_one, endoE_xE_alpha7_w0]
  · have htu : t ≠ u := fun h => hne (by rw [h])
    have hc : (t + u) ≠ 0 := fun h => htu (by
      have : t = -u := eq_neg_of_add_eq_zero_left h
      rw [this, CharTwo.neg_eq])
    set c : K := (t + u)⁻¹ with hcdef
    have hc0 : c ≠ 0 := inv_ne_zero hc
    have hct : c * (t + u) = 1 := inv_mul_cancel₀ hc
    have h4 : (1 + c * t : K) = c * u := by
      have h5 : c * u + c * t = 1 := by rw [← mul_add, add_comm, hct]
      calc (1 + c * t : K) = 1 - c * t := (CharTwo.sub_eq_add 1 (c * t)).symm
        _ = c * u := (eq_sub_of_add_eq h5).symm
    refine ⟨xE alpha7 t * sN K * xE alpha7 c, (Hsl K).mul_mem ((Hsl K).mul_mem (xE_mem_Hsl t)
      sN_mem_Hsl) (xE_mem_Hsl c), ?_, ?_⟩
    · rw [endoE_mul (xE alpha7 t * sN K) (xE alpha7 c), Module.End.mul_apply, endoE_xE_alpha7_w0,
        endoE_xE_sN_w0]
    · have hv : endoE (xE alpha7 t * sN K * xE alpha7 c * sN K) (w0 : V K) =
          c • (sw0 K + u • (w0 : V K)) := by
        have e1 : xE alpha7 t * sN K * xE alpha7 c * sN K =
            (xE alpha7 t * sN K) * (xE alpha7 c * sN K) := by group
        rw [e1, endoE_mul, Module.End.mul_apply, endoE_xE_sN_w0 c, endoE_mul, Module.End.mul_apply]
        have h3 : sw0 K + c • (w0 : V K) = (1 : K) • sw0 K + c • (w0 : V K) := by rw [one_smul]
        rw [h3, endoE_sN_comb, endoE_xE_alpha7_comb, h4, smul_add, smul_smul]
      rw [hv]
      exact Submodule.span_singleton_smul_eq (isUnit_iff_ne_zero.2 hc0) _

theorem line_points {g₀ : Gp K} (hg₀ : g₀ ∈ Hsl K) {z : Submodule K (V K)} (hz : z ∈ L0E K) :
    z = K ∙ endoE g₀ (w0 : V K) ∨ ∃ t : K, z = K ∙ endoE (g₀ * xE alpha7 t * sN K) (w0 : V K) := by
  obtain ⟨v, hvP, hv0, rfl⟩ := exists_vec_of_mem_L0E hz
  have hv' : endoE g₀⁻¹ v ∈ planeP K := (plane_stable hg₀).2 v hvP
  obtain ⟨a, b, hab⟩ := mem_planeP.1 hv'
  have hv : v = a • endoE g₀ (sw0 K) + b • endoE g₀ (w0 : V K) := by
    have := congrArg (fun x => endoE g₀ x) hab
    simp only [endoE_endoE_inv, map_add, map_smul] at this
    exact this
  by_cases ha : a = 0
  · left
    have hb : b ≠ 0 := by
      rintro rfl
      apply hv0
      rw [hv, ha]
      simp
    rw [hv, ha, zero_smul, zero_add]
    exact Submodule.span_singleton_smul_eq (isUnit_iff_ne_zero.2 hb) _
  · right
    refine ⟨b / a, ?_⟩
    have h1 : endoE (g₀ * xE alpha7 (b / a) * sN K) (w0 : V K) =
        endoE g₀ (sw0 K) + (b / a) • endoE g₀ (w0 : V K) := by
      rw [mul_assoc, endoE_mul, Module.End.mul_apply, endoE_xE_sN_w0, map_add, map_smul]
    rw [h1, hv]
    have h2 : a • endoE g₀ (sw0 K) + b • endoE g₀ (w0 : V K) =
        a • (endoE g₀ (sw0 K) + (b / a) • endoE g₀ (w0 : V K)) := by
      rw [smul_add, smul_smul, mul_div_cancel₀ _ ha]
    rw [h2]
    exact Submodule.span_singleton_smul_eq (isUnit_iff_ne_zero.2 ha) _

theorem hline_E7 : ∀ x y z : ↥(ptsE K), ColE x y z → x ≠ y →
    ∃ (g : Gp K) (t : K), ptE g = x ∧ ptE (g * sN K) = y ∧
      (z = x ∨ z = ptE (g * xE alpha7 t * sN K)) := by
  rintro x y z ⟨𝓛, ⟨h, hh, rfl⟩, hx, hy, hz⟩ hxy
  obtain ⟨x', hx', hxe⟩ := hx
  obtain ⟨y', hy', hye⟩ := hy
  obtain ⟨z', hz', hze⟩ := hz
  have hne : x' ≠ y' := by
    intro h'
    apply hxy
    apply Subtype.ext
    rw [← hxe, ← hye, h']
  obtain ⟨g₀, hg₀, hg₁, hg₂⟩ := exists_g0 hx' hy' hne
  let h' : Gp K := ⟨h, hh⟩
  have hact : ∀ g : Gp K, act h (K ∙ endoE g (w0 : V K)) = K ∙ endoE (h' * g) (w0 : V K) := by
    intro g
    rw [act_span_singleton, endoE_mul]
    rfl
  have hxp : ((ptE (h' * g₀) : ↥(ptsE K)) : Submodule K (V K)) = (x : Submodule K (V K)) := by
    rw [ptE_val, ← hxe, ← hg₁, hact]
  have hyp : ((ptE (h' * g₀ * sN K) : ↥(ptsE K)) : Submodule K (V K)) = (y : Submodule K (V K)) := by
    rw [ptE_val, ← hye, ← hg₂, hact, mul_assoc]
  rcases line_points hg₀ hz' with hz1 | ⟨t, hz2⟩
  · refine ⟨h' * g₀, 0, Subtype.ext hxp, Subtype.ext hyp, Or.inl ?_⟩
    apply Subtype.ext
    rw [← hze, ← hxe, hz1.trans hg₁]
  · refine ⟨h' * g₀, t, Subtype.ext hxp, Subtype.ext hyp, Or.inr ?_⟩
    apply Subtype.ext
    rw [ptE_val, ← hze, hz2, hact]
    simp only [mul_assoc]

end Lines

section Generation

@[expose] def ptW (c : Fin e7Data.d) : ↥(ptsE K) :=
  ⟨K ∙ (Finsupp.single c 1 : V K), by
    obtain ⟨n, hn⟩ := weight_eq_orbit (K := K) c
    exact ⟨n, by
      show K ∙ endoE n (w0 : V K) = _
      rw [hn]⟩⟩

@[expose] def PiE (K : Type) [Field K] [CharP K 2] : Finset ↥(ptsE K) :=
  Finset.univ.image fun c : Fin e7Data.d => ptW c

theorem card_PiE_le : (PiE K).card ≤ 56 := by
  refine (Finset.card_image_le).trans ?_
  rw [Finset.card_univ, Fintype.card_fin]
  exact le_of_eq rfl

theorem hlines_E7 : ∀ 𝓛, IsLine (EGrp K) (L0E K) 𝓛 → 𝓛 ⊆ ptsE K := by
  rintro 𝓛 ⟨h, hh, rfl⟩ _ ⟨x', hx', rfl⟩
  let h' : Gp K := ⟨h, hh⟩
  have hact : ∀ g : Gp K, act h (K ∙ endoE g (w0 : V K)) = K ∙ endoE (h' * g) (w0 : V K) := by
    intro g
    rw [act_span_singleton, endoE_mul]
    rfl
  rcases mem_L0E.1 hx' with rfl | ⟨t, rfl⟩
  · exact ⟨h', by
      show K ∙ endoE h' (w0 : V K) = _
      rw [act_span_singleton]⟩
  · refine ⟨h' * (xE alpha7 t * sN K), ?_⟩
    show K ∙ endoE (h' * (xE alpha7 t * sN K)) (w0 : V K) = act h (K ∙ (sw0 K + t • (w0 : V K)))
    rw [← endoE_xE_sN_w0, ← hact]

theorem hgen_E7 : ∀ S : Set (Submodule K (V K)), IsLineClosed (EGrp K) (L0E K) S →
    (∀ P ∈ PiE K, (P : Submodule K (V K)) ∈ S) → ptsE K ⊆ S := by
  intro S hS hP
  rintro _ ⟨g, rfl⟩
  have hW : ∀ c : Fin e7Data.d, (K ∙ (Finsupp.single c 1 : V K)) ∈ S :=
    fun c => hP (ptW c) (Finset.mem_image.2 ⟨c, Finset.mem_univ _, rfl⟩)
  exact weightPoints_generate hS hW g.2 topIdx

theorem hGen_E7 : ∀ Q : ↥(ptsE K) → Prop, (∀ x ∈ PiE K, Q x) →
    (∀ x y z : ↥(ptsE K), Q x → Q y → x ≠ y → ColE x y z → Q z) → ∀ x, Q x :=
  S81V.hGen_of_isLineClosed (Γ := EGrp K) (𝓛₀ := L0E K) (Pts := ptsE K) (Pi := PiE K)
    hlines_E7 hgen_E7

end Generation

end CFSG.RankThree.GF2n.Smith81.S81Z
