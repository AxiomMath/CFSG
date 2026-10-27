module

public import CFSG.RankThree.GF2n.Smith81.S81YE4Def
public import CFSG.RankThree.GF2n.Smith81.S81D6Bruhat
public import CFSG.RankThree.GF2n.Smith81.S81E7Fe7

public section

namespace CFSG.RankThree.GF2n.Smith81.RootGenE4

open CFSG.LieType.Steinberg.Minuscule CFSG.Blueprint.Chevalley CFSG.RankThree.GF2n.Smith81
  CFSG.RankThree.GF2n.Smith81.E7Model CFSG.RankThree.GF2n.Smith81.D6Spin
  CFSG.RankThree.GF2n.Smith81.RootGen CFSG.RankThree.GF2n.Smith81.RootGenE5

variable
  {K : Type} [Field K]

theorem b4_check : ∀ k : Fin 126,
    MinData.toWeight ((Tag.rootCertificate .E7).root k) ⬝ᵥ theta = 0 →
    0 < CFSG.Blueprint.Chevalley.height (τ := .E7) ((Tag.rootCertificate .E7).root k) →
    pr (⟨8, by decide⟩ : Fin e7Data.d) ((Tag.rootCertificate .E7).root k) ≠ -1 := by
  decide +kernel

theorem pr_a0_ne_neg_one {β : Fin (Tag.rank .E7) → ℤ} (hβ : IsRoot .E7 β)
    (hzero : MinData.toWeight β ⬝ᵥ theta = 0)
    (hpos : 0 < CFSG.Blueprint.Chevalley.height (τ := .E7) β) :
    pr (a0 : Fin e7Data.d) β ≠ -1 := by
  have h := (forall_isRoot_iff (fun γ => MinData.toWeight γ ⬝ᵥ theta = 0 →
    0 < CFSG.Blueprint.Chevalley.height (τ := .E7) γ → pr (a0 : Fin e7Data.d) γ ≠ -1)).2 b4_check
  exact h β hβ hzero hpos

theorem UL_fix_a0 [CharP K 2] {u : (Module.End K (V K))ˣ} (hu : u ∈ UL K) :
    (u : Module.End K (V K)) (Finsupp.single (a0 : Fin e7Data.d) 1) =
      Finsupp.single (a0 : Fin e7Data.d) 1 := by
  rw [UL] at hu
  induction hu using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨β, hβ, hzero, hpos, c, rfl⟩ := hx
    rw [e7Data_valid.xu_apply, rootOp_single (K := K) hβ,
      if_neg (pr_a0_ne_neg_one hβ hzero hpos), smul_zero, add_zero]
  | one => rw [Units.val_one, Module.End.one_apply]
  | mul x y _ _ hx hy => rw [Units.val_mul, Module.End.mul_apply, hy, hx]
  | inv x _ hx =>
    calc ((x⁻¹ : (Module.End K (V K))ˣ) : Module.End K (V K)) (Finsupp.single (a0 : Fin e7Data.d) 1)
        = ((x⁻¹ : (Module.End K (V K))ˣ) : Module.End K (V K))
            (((x : (Module.End K (V K))ˣ) : Module.End K (V K)) (Finsupp.single (a0 : Fin e7Data.d) 1)) := by
          rw [hx]
      _ = Finsupp.single (a0 : Fin e7Data.d) 1 := by
          rw [← Module.End.mul_apply, Units.inv_mul, Module.End.one_apply]

theorem act7_mul_apply (g h : G7 K) (v : V K) : act7 (g * h) v = act7 g (act7 h v) := by
  rw [act7_mul]
  rfl

theorem act7_one_apply (v : V K) : act7 (1 : G7 K) v = v := by
  rw [act7_apply, e7Data_valid.endo_one, Module.End.one_apply]

theorem act7_mem_V0_of_mem_LG [CharP K 2] {g : G7 K} (hg : g ∈ LG K) {v : V K} (hv : v ∈ V0 K) :
    act7 g v ∈ V0 K := by
  rw [act7_apply]
  exact Lam_stabilizes_V0 (mem_LG.1 hg) hv

theorem endo_borL_a0 [CharP K 2] {b : G7 K} (hb : b ∈ BorL K) :
    ∃ c : K, c ≠ 0 ∧ act7 b (Finsupp.single (a0 : Fin e7Data.d) 1) =
      c • Finsupp.single (a0 : Fin e7Data.d) 1 := by
  obtain ⟨u, hu, t, ht, rfl⟩ := mem_BorL_iff.1 hb
  have hu' : (u : (Module.End K (V K))ˣ) ∈ UL K := Subgroup.mem_comap.1 hu
  obtain ⟨c, hc⟩ := endo_tor_single (K := K) ht (a0 : Fin e7Data.d)
  have hact : act7 t (Finsupp.single (a0 : Fin e7Data.d) 1) =
      c • Finsupp.single (a0 : Fin e7Data.d) 1 := by
    rw [act7_apply]
    exact hc
  have hfix : act7 u (Finsupp.single (a0 : Fin e7Data.d) 1) =
      Finsupp.single (a0 : Fin e7Data.d) 1 := by
    rw [act7_apply]
    exact UL_fix_a0 hu'
  refine ⟨c, ?_, ?_⟩
  · rintro rfl
    apply (Finsupp.single_ne_zero.2 one_ne_zero : (Finsupp.single (a0 : Fin e7Data.d) 1 : V K) ≠ 0)
    have h1 : act7 t (Finsupp.single (a0 : Fin e7Data.d) 1) = 0 := by
      rw [hact, zero_smul]
    exact (act7 t).map_eq_zero_iff.1 h1
  · rw [act7_mul_apply, hact, map_smul, hfix]

theorem e4V_lineNF [CharP K 2] {g : G7 K} (hg : g ∈ LG K) {c : K} (hc : c ≠ 0) :
    ∃ (u : G7 K) (μ : Fin e7Data.d) (c₀ : K), u ∈ LG K ∧
      (∀ a : K, u * e7Data_valid.xm K theta4 a = e7Data_valid.xm K theta4 a * u) ∧ μ ∈ idx0 ∧
      c₀ ≠ 0 ∧ c • act7 g (Finsupp.single (a0 : Fin e7Data.d) 1) =
        c₀ • act7 u (Finsupp.single μ 1) := by
  obtain ⟨w, b₁, hb₁, b₂, hb₂, rfl⟩ := Lam_bruhat (mem_LG.1 hg)
  obtain ⟨c₂, hc₂0, hc₂⟩ := endo_borL_a0 hb₂
  obtain ⟨μ, hμ⟩ := endo_nW_single (K := K) w (a0 : Fin e7Data.d)
  obtain ⟨u, hu, t, ht, rfl⟩ := mem_BorL_iff.1 hb₁
  obtain ⟨c₃, hc₃⟩ := endo_tor_single (K := K) ht μ
  have hu' : (u : (Module.End K (V K))ˣ) ∈ UL K := Subgroup.mem_comap.1 hu
  have huLG : u ∈ LG K := mem_LG.2 (UL_le_Lam hu')
  have hnw : act7 (nW K w) (Finsupp.single (a0 : Fin e7Data.d) 1) = Finsupp.single μ 1 := by
    rw [act7_apply]
    exact hμ
  have ht3 : act7 t (Finsupp.single μ 1) = c₃ • Finsupp.single μ 1 := by
    rw [act7_apply]
    exact hc₃
  have hμne : (Finsupp.single μ 1 : V K) ≠ 0 := Finsupp.single_ne_zero.2 one_ne_zero
  have hc₃0 : c₃ ≠ 0 := by
    rintro rfl
    apply hμne
    have h1 : act7 t (Finsupp.single μ 1) = 0 := by
      rw [ht3, zero_smul]
    exact (act7 t).map_eq_zero_iff.1 h1
  have hc₀ : c * c₂ * c₃ ≠ 0 := mul_ne_zero (mul_ne_zero hc hc₂0) hc₃0
  have key : act7 (u * t * nW K w * b₂) (Finsupp.single (a0 : Fin e7Data.d) 1) =
      (c₂ * c₃) • act7 u (Finsupp.single μ 1) := by
    simp only [act7_mul_apply, hc₂, map_smul, hnw, ht3, smul_smul]
  have heq : c • act7 (u * t * nW K w * b₂) (Finsupp.single (a0 : Fin e7Data.d) 1) =
      (c * c₂ * c₃) • act7 u (Finsupp.single μ 1) := by
    rw [key, smul_smul, mul_assoc]
  have hv0 : (Finsupp.single (a0 : Fin e7Data.d) 1 : V K) ∈ V0 K := by
    rw [mem_V0]
    intro b hb
    rw [Finsupp.single_apply, if_neg]
    intro h
    exact hb (h ▸ a0.2)
  have hgV0 : act7 (u * t * nW K w * b₂) (Finsupp.single (a0 : Fin e7Data.d) 1) ∈ V0 K :=
    act7_mem_V0_of_mem_LG hg hv0
  have huV0 : act7 u (Finsupp.single μ 1) ∈ V0 K := by
    have h1 : (c * c₂ * c₃) • act7 u (Finsupp.single μ 1) ∈ V0 K := by
      rw [← heq]
      exact Submodule.smul_mem _ c hgV0
    have h2 := Submodule.smul_mem _ (c * c₂ * c₃)⁻¹ h1
    rwa [smul_smul, inv_mul_cancel₀ hc₀, one_smul] at h2
  have hsing : (Finsupp.single μ 1 : V K) ∈ V0 K := by
    have h3 := act7_mem_V0_of_mem_LG (inv_mem huLG) huV0
    rwa [← act7_mul_apply, inv_mul_cancel, act7_one_apply] at h3
  refine ⟨u, μ, c * c₂ * c₃, huLG, ?_, ?_, hc₀, heq⟩
  · intro a
    apply Subtype.ext
    exact UL_comm_xu_theta4 hu' a
  · by_contra hμ'
    have h4 := (mem_V0.1 hsing) μ hμ'
    rw [Finsupp.single_eq_same] at h4
    exact one_ne_zero h4

end CFSG.RankThree.GF2n.Smith81.RootGenE4
