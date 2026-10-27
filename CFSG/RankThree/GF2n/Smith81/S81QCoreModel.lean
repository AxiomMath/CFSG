module

public import CFSG.RankThree.GF2n.Smith81.S81QRDLink
public import CFSG.RankThree.GF2n.Smith81.S81VGenBridge

public noncomputable section

namespace CFSG.RankThree.GF2n.Smith81.D6Spin

open CFSG.LieType.Steinberg.Minuscule CFSG.Blueprint.Chevalley CFSG.LieType.Steinberg
  CFSG.LieType.Universal CFSG.LieType.RootSystem CFSG.LieType.CurtisTits
  CFSG.RankThree.GF2n.Smith81.XOps CFSG.RankThree.GF2n.Smith81.E7Model
  CFSG.RankThree.GF2n.Smith81.E7X CFSG.RankThree.GF2n.Smith81.S81Z CFSG.RankThree.GF2n.Smith81.D6X
  CFSG.RankThree.GF2n.Smith81.S81V CFSG.RankThree.GF2n.Smith81.Gen76


variable {K : Type} [Field K] [CharP K 2] [Finite K]

section Weights

theorem weight_eq_orbit0 (c : Idx0) :
    ∃ n : ↥(EAut0 K), (n : W K ≃ₗ[K] W K) (p0 K) = Finsupp.single c 1 := by
  obtain ⟨n, σ, ρ, hn, hm, hσ⟩ := exists_isMonL_of_weight (K := K) (c : Fin e7Data.d) (mem_idx0.1 c.2)
  refine ⟨lamGEquivEAut0 K ⟨n, hn⟩, ?_⟩
  apply emb_injective
  have h1 := lamGHom_induces (K := K) ⟨n, hn⟩ (p0 K)
  have h2 := hm.weight (a0 : Fin e7Data.d)
  have h3 : σ (a0 : Fin e7Data.d) = (c : Fin e7Data.d) := hσ
  rw [h3] at h2
  show emb K (lamGHom K ⟨n, hn⟩ (p0 K)) = emb K (Finsupp.single c 1)
  rw [h1, p0, emb_single, emb_single]
  exact h2

theorem spanW_top0 :
    Submodule.span K (Set.range fun g : ↥(EAut0 K) => (g : W K ≃ₗ[K] W K) (p0 K)) = ⊤ := by
  rw [eq_top_iff, ← (Finsupp.basisSingleOne (R := K) (ι := Idx0)).span_eq]
  refine Submodule.span_mono ?_
  rintro _ ⟨c, rfl⟩
  obtain ⟨n, hn⟩ := weight_eq_orbit0 (K := K) c
  exact ⟨n, by
    show (n : W K ≃ₗ[K] W K) (p0 K) = _
    rw [hn]
    simp [Finsupp.coe_basisSingleOne]⟩

theorem card_Idx0 : Fintype.card Idx0 = 32 := (Fintype.card_coe idx0).trans card_idx0

theorem finrank_W32 : Module.finrank K (W K) = 32 := by
  rw [Module.finrank_finsupp_self, card_Idx0]

end Weights

section Plane

@[expose] def xt (t : K) : ↥(EAut0 K) := (d6RootDatum K).u (t • (d6RootDatum K).n₁)

theorem coe_xt (t : K) :
    ((xt t : ↥(EAut0 K)) : W K ≃ₗ[K] W K) = vAut0 K (xuWUnit alphaA2_mem_Perp t) :=
  d6_u_smul_n1 t

theorem xt_zero : xt (0 : K) = 1 := by
  have h := (d6RootDatum K).u_add 0 0
  rw [add_zero] at h
  have h0 : (d6RootDatum K).u 0 = 1 := mul_left_cancel (a := (d6RootDatum K).u 0) (by rw [mul_one]; exact h.symm)
  unfold xt
  rw [zero_smul]
  exact h0

theorem xt_add (t u : K) : xt (t + u) = xt t * xt u := by
  unfold xt
  rw [add_smul]
  exact (d6RootDatum K).u_add _ _

theorem xt_mul_self (t : K) : xt t * xt t = 1 := by
  rw [← xt_add, CharTwo.add_self_eq_zero, xt_zero]

theorem xt_inv (t : K) : (xt t)⁻¹ = xt t := inv_eq_of_mul_eq_one_right (xt_mul_self t)

theorem s_mul_s0 : (d6RootDatum K).s * (d6RootDatum K).s = 1 := (d6RootDatum K).s_sq

theorem s_inv0 : ((d6RootDatum K).s)⁻¹ = (d6RootDatum K).s := inv_eq_of_mul_eq_one_right s_mul_s0

@[expose] def sp0 (K : Type) [Field K] [CharP K 2] [Finite K] : W K :=
  (((d6RootDatum K).s : ↥(EAut0 K)) : W K ≃ₗ[K] W K) (p0 K)

theorem sp0_eq : sp0 K = Finsupp.single a1W 1 := d6_s_apply_single a0

set_option maxRecDepth 20000 in
theorem pr_a1W : pr (a1W : Fin e7Data.d) alphaA2 = -1 := by
  have h : pr (e7Data_valid.sRefl nodeA2 (⟨8, by decide⟩ : Fin e7Data.d)) alphaA2 = -1 := by
    unfold pr
    rw [e7Data_valid.sRefl_val]
    have : e7Data.wt (e7Data.weyl (8 : ℕ) nodeA2) ⬝ᵥ alphaA2 = -1 := by
      unfold alphaA2 nodeA2
      decide +kernel
    exact this
  exact h

set_option maxRecDepth 20000 in
theorem shift_a1W : shift alphaA2 (a1W : Fin e7Data.d) = (a0 : Fin e7Data.d) := by
  have h : shift alphaA2 (e7Data_valid.sRefl nodeA2 (⟨8, by decide⟩ : Fin e7Data.d)) = ⟨8, by decide⟩ := by
    apply shift_eq
    rw [e7Data_valid.sRefl_val]
    have : e7Data.wt (8 : ℕ) = e7Data.wt (e7Data.weyl (8 : ℕ) nodeA2) + MinData.toWeight alphaA2 := by
      unfold alphaA2 nodeA2
      decide +kernel
    exact this
  exact h

theorem shiftW_a1W : shiftW alphaA2 a1W = a0 :=
  Subtype.ext ((shiftW_val alphaA2_mem_Perp pr_a1W).trans shift_a1W)

theorem a1W_ne_a0 : a1W ≠ a0 := by
  intro h
  have h1 := pr_a1W
  rw [h] at h1
  have h2 : pr (a0 : Fin e7Data.d) alphaA2 = 1 := pr_alphaA2
  rw [h2] at h1
  norm_num at h1

theorem xt_p0 (t : K) : ((xt t : ↥(EAut0 K)) : W K ≃ₗ[K] W K) (p0 K) = p0 K :=
  rootRad0_fix_p0 (u_mem_rootRad0 (t • (d6RootDatum K).n₁))

theorem xt_sp0 (t : K) :
    ((xt t : ↥(EAut0 K)) : W K ≃ₗ[K] W K) (sp0 K) = sp0 K + t • p0 K := by
  rw [coe_xt, vAut0_apply, sp0_eq, xuWUnit_apply, EW_single alphaA2_mem_Perp, if_pos pr_a1W,
    shiftW_a1W]
  rfl

theorem s_sp0 : (((d6RootDatum K).s : ↥(EAut0 K)) : W K ≃ₗ[K] W K) (sp0 K) = p0 K := by
  have h : (((d6RootDatum K).s * (d6RootDatum K).s : ↥(EAut0 K)) : W K ≃ₗ[K] W K) = 1 :=
    congrArg Subtype.val s_mul_s0
  unfold sp0
  rw [← LinearEquiv.mul_apply]
  have h' : (((d6RootDatum K).s : ↥(EAut0 K)) : W K ≃ₗ[K] W K) *
      (((d6RootDatum K).s : ↥(EAut0 K)) : W K ≃ₗ[K] W K) = 1 := h
  rw [h']
  rfl

theorem xt_s_p0 (t : K) :
    ((xt t * (d6RootDatum K).s : ↥(EAut0 K)) : W K ≃ₗ[K] W K) (p0 K) = sp0 K + t • p0 K := by
  show ((xt t : ↥(EAut0 K)) : W K ≃ₗ[K] W K) ((((d6RootDatum K).s : ↥(EAut0 K)) : W K ≃ₗ[K] W K) (p0 K)) = _
  exact xt_sp0 t

@[expose] def plane0 (K : Type) [Field K] [CharP K 2] [Finite K] : Submodule K (W K) :=
  Submodule.span K {p0 K, sp0 K}

theorem p0_mem_plane0 : p0 K ∈ plane0 K := Submodule.subset_span (by simp)

theorem sp0_mem_plane0 : sp0 K ∈ plane0 K := Submodule.subset_span (by simp)

theorem mem_plane0 {v : W K} : v ∈ plane0 K ↔ ∃ a b : K, v = a • sp0 K + b • p0 K := by
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
    exact Submodule.add_mem _ (Submodule.smul_mem _ _ sp0_mem_plane0)
      (Submodule.smul_mem _ _ p0_mem_plane0)

@[expose] def Hsl0 (K : Type) [Field K] [CharP K 2] [Finite K] : Subgroup ↥(EAut0 K) :=
  Subgroup.closure ({g | ∃ t : K, g = xt t} ∪ {(d6RootDatum K).s})

theorem xt_mem_Hsl0 (t : K) : xt t ∈ Hsl0 K :=
  Subgroup.subset_closure (Or.inl ⟨t, rfl⟩)

theorem s_mem_Hsl0 : (d6RootDatum K).s ∈ Hsl0 K := Subgroup.subset_closure (Or.inr rfl)

theorem xt_comb (t a b : K) :
    ((xt t : ↥(EAut0 K)) : W K ≃ₗ[K] W K) (a • sp0 K + b • p0 K) = a • sp0 K + (b + a * t) • p0 K := by
  rw [map_add, map_smul, map_smul, xt_sp0, xt_p0, smul_add, add_smul, smul_smul]
  abel

theorem s_comb (a b : K) :
    (((d6RootDatum K).s : ↥(EAut0 K)) : W K ≃ₗ[K] W K) (a • sp0 K + b • p0 K) =
      b • sp0 K + a • p0 K := by
  rw [map_add, map_smul, map_smul, s_sp0]
  show a • p0 K + b • sp0 K = _
  rw [add_comm]

theorem plane_stable0 {g : ↥(EAut0 K)} (hg : g ∈ Hsl0 K) :
    (∀ v ∈ plane0 K, (g : W K ≃ₗ[K] W K) v ∈ plane0 K) ∧
      ∀ v ∈ plane0 K, ((g⁻¹ : ↥(EAut0 K)) : W K ≃ₗ[K] W K) v ∈ plane0 K := by
  refine Subgroup.closure_induction (p := fun (g : ↥(EAut0 K)) _ => (∀ v ∈ plane0 K, (g : W K ≃ₗ[K] W K) v ∈ plane0 K) ∧
    ∀ v ∈ plane0 K, ((g⁻¹ : ↥(EAut0 K)) : W K ≃ₗ[K] W K) v ∈ plane0 K) ?_ ?_ ?_ ?_ hg
  · rintro g (⟨t, rfl⟩ | rfl)
    · have key : ∀ v ∈ plane0 K, ((xt t : ↥(EAut0 K)) : W K ≃ₗ[K] W K) v ∈ plane0 K := by
        intro v hv
        obtain ⟨a, b, rfl⟩ := mem_plane0.1 hv
        rw [xt_comb]
        exact mem_plane0.2 ⟨a, b + a * t, rfl⟩
      refine ⟨key, fun v hv => ?_⟩
      rw [xt_inv]
      exact key v hv
    · have key : ∀ v ∈ plane0 K,
          (((d6RootDatum K).s : ↥(EAut0 K)) : W K ≃ₗ[K] W K) v ∈ plane0 K := by
        intro v hv
        obtain ⟨a, b, rfl⟩ := mem_plane0.1 hv
        rw [s_comb]
        exact mem_plane0.2 ⟨b, a, rfl⟩
      refine ⟨key, fun v hv => ?_⟩
      rw [s_inv0]
      exact key v hv
  · exact ⟨fun v hv => hv, fun v hv => by rw [inv_one]; exact hv⟩
  · rintro x y - - ⟨hx1, hx2⟩ ⟨hy1, hy2⟩
    refine ⟨fun v hv => ?_, fun v hv => ?_⟩
    · show (x : W K ≃ₗ[K] W K) ((y : W K ≃ₗ[K] W K) v) ∈ _
      exact hx1 _ (hy1 v hv)
    · rw [mul_inv_rev]
      show ((y⁻¹ : ↥(EAut0 K)) : W K ≃ₗ[K] W K) (((x⁻¹ : ↥(EAut0 K)) : W K ≃ₗ[K] W K) v) ∈ _
      exact hy2 _ (hx2 v hv)
  · rintro x - ⟨hx1, hx2⟩
    refine ⟨fun v hv => ?_, fun v hv => ?_⟩
    · exact hx2 v hv
    · rw [inv_inv]
      exact hx1 v hv

end Plane

section Lines

abbrev L0W (K : Type) [Field K] : Set (Submodule K (W K)) := rootLine (K := K) a1W a0

theorem mem_L0W {u : Submodule K (W K)} :
    u ∈ L0W K ↔ u = K ∙ p0 K ∨ ∃ t : K, u = K ∙ (sp0 K + t • p0 K) := by
  unfold L0W rootLine
  simp only [Set.mem_insert_iff, Set.mem_range]
  have hp : (Finsupp.single a0 (1 : K) : W K) = p0 K := rfl
  rw [hp, ← sp0_eq]
  constructor
  · rintro (h | ⟨t, rfl⟩)
    · exact Or.inl h
    · exact Or.inr ⟨t, rfl⟩
  · rintro (h | ⟨t, rfl⟩)
    · exact Or.inl h
    · exact Or.inr ⟨t, rfl⟩

theorem sp0_notin_span : sp0 K ∉ Submodule.span K {p0 K} := by
  intro h
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 h
  have h1 := congrArg (fun w : W K => w a1W) hc
  simp only [Finsupp.smul_apply, smul_eq_mul, sp0_eq, p0] at h1
  rw [Finsupp.single_eq_same, Finsupp.single_eq_of_ne a1W_ne_a0] at h1
  simp at h1

theorem exists_vec_of_mem_L0W {z : Submodule K (W K)} (hz : z ∈ L0W K) :
    ∃ v ∈ plane0 K, v ≠ 0 ∧ z = K ∙ v := by
  rcases mem_L0W.1 hz with rfl | ⟨t, rfl⟩
  · exact ⟨p0 K, p0_mem_plane0, p0_ne_zero, rfl⟩
  · refine ⟨sp0 K + t • p0 K, mem_plane0.2 ⟨1, t, by rw [one_smul]⟩, ?_, rfl⟩
    intro h0
    apply sp0_notin_span (K := K)
    have : sp0 K = (-t) • p0 K := by
      have := congrArg (fun v => v - t • p0 K) h0
      simp only [add_sub_cancel_right, zero_sub] at this
      rw [this, neg_smul]
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)

variable (K) in
@[expose] def ptsW : Set (Submodule K (W K)) :=
  Set.range fun g : ↥(EAut0 K) => K ∙ (g : W K ≃ₗ[K] W K) (p0 K)

@[expose] def ptW0 (g : ↥(EAut0 K)) : ↥(ptsW K) := ⟨K ∙ (g : W K ≃ₗ[K] W K) (p0 K), g, rfl⟩

theorem ptW0_surjective : Function.Surjective (ptW0 (K := K)) := by
  rintro ⟨_, g, rfl⟩
  exact ⟨g, rfl⟩

theorem ptW0_val (g : ↥(EAut0 K)) :
    ((ptW0 g : ↥(ptsW K)) : Submodule K (W K)) = K ∙ (g : W K ≃ₗ[K] W K) (p0 K) := rfl

@[expose] def ColW (x y z : ↥(ptsW K)) : Prop :=
  ∃ 𝓛, IsLine (LamW K) (L0W K) 𝓛 ∧ (x : Submodule K (W K)) ∈ 𝓛 ∧ (y : Submodule K (W K)) ∈ 𝓛 ∧
    (z : Submodule K (W K)) ∈ 𝓛

theorem exists_g0 {u₁ u₂ : Submodule K (W K)} (h₁ : u₁ ∈ L0W K) (h₂ : u₂ ∈ L0W K) (hne : u₁ ≠ u₂) :
    ∃ g₀ ∈ Hsl0 K, K ∙ (g₀ : W K ≃ₗ[K] W K) (p0 K) = u₁ ∧
      K ∙ ((g₀ * (d6RootDatum K).s : ↥(EAut0 K)) : W K ≃ₗ[K] W K) (p0 K) = u₂ := by
  rcases mem_L0W.1 h₁ with rfl | ⟨t, rfl⟩ <;> rcases mem_L0W.1 h₂ with rfl | ⟨u, rfl⟩
  · exact absurd rfl hne
  · refine ⟨xt u, xt_mem_Hsl0 u, ?_, ?_⟩
    · rw [xt_p0]
    · rw [xt_s_p0]
  · refine ⟨xt t * (d6RootDatum K).s, mul_mem (xt_mem_Hsl0 t) s_mem_Hsl0, ?_, ?_⟩
    · rw [xt_s_p0]
    · rw [mul_assoc, s_mul_s0, mul_one, xt_p0]
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
    refine ⟨xt t * (d6RootDatum K).s * xt c,
      mul_mem (mul_mem (xt_mem_Hsl0 t) s_mem_Hsl0) (xt_mem_Hsl0 c), ?_, ?_⟩
    · show K ∙ ((xt t * (d6RootDatum K).s : ↥(EAut0 K)) : W K ≃ₗ[K] W K)
        (((xt c : ↥(EAut0 K)) : W K ≃ₗ[K] W K) (p0 K)) = _
      rw [xt_p0, xt_s_p0]
    · have hv : ((xt t * (d6RootDatum K).s * xt c * (d6RootDatum K).s : ↥(EAut0 K)) :
          W K ≃ₗ[K] W K) (p0 K) = c • (sp0 K + u • p0 K) := by
        have e1 : xt t * (d6RootDatum K).s * xt c * (d6RootDatum K).s =
            (xt t * (d6RootDatum K).s) * (xt c * (d6RootDatum K).s) := by group
        rw [e1]
        show ((xt t * (d6RootDatum K).s : ↥(EAut0 K)) : W K ≃ₗ[K] W K)
          (((xt c * (d6RootDatum K).s : ↥(EAut0 K)) : W K ≃ₗ[K] W K) (p0 K)) = _
        rw [xt_s_p0 c]
        have h3 : sp0 K + c • p0 K = (1 : K) • sp0 K + c • p0 K := by rw [one_smul]
        rw [h3]
        show ((xt t : ↥(EAut0 K)) : W K ≃ₗ[K] W K) ((((d6RootDatum K).s : ↥(EAut0 K)) :
          W K ≃ₗ[K] W K) ((1 : K) • sp0 K + c • p0 K)) = _
        rw [s_comb, xt_comb, h4, smul_add, smul_smul]
      rw [hv]
      exact Submodule.span_singleton_smul_eq (isUnit_iff_ne_zero.2 hc0) _

theorem apply_inv_apply0 (g : ↥(EAut0 K)) (v : W K) :
    (g : W K ≃ₗ[K] W K) (((g⁻¹ : ↥(EAut0 K)) : W K ≃ₗ[K] W K) v) = v :=
  LinearEquiv.apply_symm_apply _ _

theorem line_points {g₀ : ↥(EAut0 K)} (hg₀ : g₀ ∈ Hsl0 K) {z : Submodule K (W K)} (hz : z ∈ L0W K) :
    z = K ∙ (g₀ : W K ≃ₗ[K] W K) (p0 K) ∨
      ∃ t : K, z = K ∙ ((g₀ * xt t * (d6RootDatum K).s : ↥(EAut0 K)) : W K ≃ₗ[K] W K) (p0 K) := by
  obtain ⟨v, hvP, hv0, rfl⟩ := exists_vec_of_mem_L0W hz
  have hv' : ((g₀⁻¹ : ↥(EAut0 K)) : W K ≃ₗ[K] W K) v ∈ plane0 K := (plane_stable0 hg₀).2 v hvP
  obtain ⟨a, b, hab⟩ := mem_plane0.1 hv'
  have hv : v = a • (g₀ : W K ≃ₗ[K] W K) (sp0 K) + b • (g₀ : W K ≃ₗ[K] W K) (p0 K) := by
    have := congrArg (fun x => (g₀ : W K ≃ₗ[K] W K) x) hab
    simp only [apply_inv_apply0, map_add, map_smul] at this
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
    have h1 : ((g₀ * xt (b / a) * (d6RootDatum K).s : ↥(EAut0 K)) : W K ≃ₗ[K] W K) (p0 K) =
        (g₀ : W K ≃ₗ[K] W K) (sp0 K) + (b / a) • (g₀ : W K ≃ₗ[K] W K) (p0 K) := by
      rw [mul_assoc]
      show (g₀ : W K ≃ₗ[K] W K) (((xt (b / a) * (d6RootDatum K).s : ↥(EAut0 K)) : W K ≃ₗ[K] W K) (p0 K)) = _
      rw [xt_s_p0, map_add, map_smul]
    rw [h1, hv]
    have h2 : a • (g₀ : W K ≃ₗ[K] W K) (sp0 K) + b • (g₀ : W K ≃ₗ[K] W K) (p0 K) =
        a • ((g₀ : W K ≃ₗ[K] W K) (sp0 K) + (b / a) • (g₀ : W K ≃ₗ[K] W K) (p0 K)) := by
      rw [smul_add, smul_smul, mul_div_cancel₀ _ ha]
    rw [h2]
    exact Submodule.span_singleton_smul_eq (isUnit_iff_ne_zero.2 ha) _

@[expose] def hEq (h : (Module.End K (W K))ˣ) (hh : h ∈ LamW K) : ↥(EAut0 K) :=
  ⟨vAut0 K h, h, hh, rfl⟩

theorem act_ptW (h : (Module.End K (W K))ˣ) (hh : h ∈ LamW K) (g : ↥(EAut0 K)) :
    act h (K ∙ (g : W K ≃ₗ[K] W K) (p0 K)) =
      K ∙ ((hEq h hh * g : ↥(EAut0 K)) : W K ≃ₗ[K] W K) (p0 K) := by
  rw [act_span_singleton]
  rfl

theorem hline_E4 : ∀ x y z : ↥(ptsW K), ColW x y z → x ≠ y →
    ∃ (g : ↥(EAut0 K)) (t : K), ptW0 g = x ∧ ptW0 (g * (d6RootDatum K).s) = y ∧
      (z = x ∨ z = ptW0 (g * xt t * (d6RootDatum K).s)) := by
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
  have hxp : ((ptW0 (hEq h hh * g₀) : ↥(ptsW K)) : Submodule K (W K)) = (x : Submodule K (W K)) := by
    rw [ptW0_val, ← hxe, ← hg₁, act_ptW]
  have hyp : ((ptW0 (hEq h hh * g₀ * (d6RootDatum K).s) : ↥(ptsW K)) : Submodule K (W K)) =
      (y : Submodule K (W K)) := by
    rw [ptW0_val, ← hye, ← hg₂, act_ptW, mul_assoc]
  rcases line_points hg₀ hz' with hz1 | ⟨t, hz2⟩
  · refine ⟨hEq h hh * g₀, 0, Subtype.ext hxp, Subtype.ext hyp, Or.inl ?_⟩
    apply Subtype.ext
    rw [← hze, ← hxe, hz1.trans hg₁]
  · refine ⟨hEq h hh * g₀, t, Subtype.ext hxp, Subtype.ext hyp, Or.inr ?_⟩
    apply Subtype.ext
    rw [ptW0_val, ← hze, hz2, act_ptW h hh]
    simp only [mul_assoc]

end Lines

section Generation

@[expose] def ptW (c : Idx0) : ↥(ptsW K) :=
  ⟨K ∙ (Finsupp.single c 1 : W K), by
    obtain ⟨n, hn⟩ := weight_eq_orbit0 (K := K) c
    exact ⟨n, by
      show K ∙ (n : W K ≃ₗ[K] W K) (p0 K) = _
      rw [hn]⟩⟩

@[expose] def PiW (K : Type) [Field K] [CharP K 2] [Finite K] : Finset ↥(ptsW K) :=
  Finset.univ.image fun c : Idx0 => ptW c

theorem card_PiW_le : (PiW K).card ≤ 32 := by
  refine (Finset.card_image_le).trans ?_
  rw [Finset.card_univ, card_Idx0]

theorem hlines_E4 : ∀ 𝓛, IsLine (LamW K) (L0W K) 𝓛 → 𝓛 ⊆ ptsW K := by
  rintro 𝓛 ⟨h, hh, rfl⟩ _ ⟨x', hx', rfl⟩
  rcases mem_L0W.1 hx' with rfl | ⟨t, rfl⟩
  · exact ⟨hEq h hh, by
      show K ∙ ((hEq h hh : ↥(EAut0 K)) : W K ≃ₗ[K] W K) (p0 K) = _
      rw [act_span_singleton]
      rfl⟩
  · refine ⟨hEq h hh * (xt t * (d6RootDatum K).s), ?_⟩
    show K ∙ ((hEq h hh * (xt t * (d6RootDatum K).s) : ↥(EAut0 K)) : W K ≃ₗ[K] W K) (p0 K) =
      act h (K ∙ (sp0 K + t • p0 K))
    rw [← xt_s_p0, ← act_ptW]

theorem hgen_E4 : ∀ S : Set (Submodule K (W K)), IsLineClosed (LamW K) (L0W K) S →
    (∀ P ∈ PiW K, (P : Submodule K (W K)) ∈ S) → ptsW K ⊆ S := by
  intro S hS hP
  rintro _ ⟨g, rfl⟩
  have hW : ∀ c : Idx0, (K ∙ (Finsupp.single c 1 : W K)) ∈ S :=
    fun c => hP (ptW c) (Finset.mem_image.2 ⟨c, Finset.mem_univ _, rfl⟩)
  obtain ⟨g', hg', hgg⟩ := g.2
  have h := weightPointsW_generate hS hW hg' a0
  have e : (g : W K ≃ₗ[K] W K) (p0 K) = (g' : Module.End K (W K)) (Finsupp.single a0 1) := by
    rw [← hgg]
    rfl
  show K ∙ (g : W K ≃ₗ[K] W K) (p0 K) ∈ S
  rw [e]
  exact h

theorem hGen_E4 : ∀ Q : ↥(ptsW K) → Prop, (∀ x ∈ PiW K, Q x) →
    (∀ x y z : ↥(ptsW K), Q x → Q y → x ≠ y → ColW x y z → Q z) → ∀ x, Q x :=
  S81V.hGen_of_isLineClosed (Γ := LamW K) (𝓛₀ := L0W K) (Pts := ptsW K) (Pi := PiW K)
    hlines_E4 hgen_E4

end Generation

end CFSG.RankThree.GF2n.Smith81.D6Spin
