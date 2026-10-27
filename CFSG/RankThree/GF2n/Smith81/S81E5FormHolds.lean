module

public import CFSG.RankThree.GF2n.Smith81.S81E5Tr
public import CFSG.RankThree.GF2n.Smith81.S81WGeomE7
public import CFSG.RankThree.GF2n.Smith81.S81WIrrE7
public import CFSG.RankThree.GF2n.Smith81.S81TLineGen

public section


namespace CFSG.RankThree.GF2n.Smith81.E7Model

open CFSG.LieType.Steinberg.Minuscule CFSG.Blueprint.Chevalley

private theorem exists_root_lower_index : ∀ b : Fin e7Data.d, b ≠ i7 →
    ∃ k : Fin 126, pr i7 ((Tag.rootCertificate .E7).root k) = 1 ∧
      pr b ((Tag.rootCertificate .E7).root k) = -1 := by
  unfold pr
  decide +kernel

theorem exists_root_lower {b : Fin e7Data.d} (hb : b ≠ i7) :
    ∃ γ : Fin (Tag.rank .E7) → ℤ, IsRoot .E7 γ ∧ pr i7 γ = 1 ∧ pr b γ = -1 := by
  obtain ⟨k, h1, h2⟩ := exists_root_lower_index b hb
  have hlen : (Tag.rootCertificate .E7).roots.length = 126 := Tag.rootCertificate_length .E7
  exact ⟨_, RootCertificate.isRoot_root (Tag.rootCertificate_check .E7) k (by omega), h1, h2⟩

variable {K : Type} [Field K] [CharP K 2]

theorem mem_span_w0_of_fix {v : V K} (hv : ∀ s ∈ rootSet7 K, s v = v) :
    v ∈ Submodule.span K {(w0 : V K)} := by
  have hzero : ∀ b, b ≠ i7 → v b = 0 := by
    intro b hb
    obtain ⟨γ, hγ, h1, h2⟩ := exists_root_lower hb
    have hfix := congrArg (fun f : V K => f (shift γ b))
      (hv (vAut K (e7Data_valid.xu K γ 1)) ⟨γ, hγ, h1, 1, rfl⟩)
    simp only [vAut_apply] at hfix
    rw [xu_apply_coord hγ (1 : K) v (shift γ b), if_pos (pr_shift_self hγ h2),
      shift_neg_shift hγ h2, one_mul] at hfix
    exact add_eq_left.mp hfix
  rw [Submodule.mem_span_singleton]
  refine ⟨v i7, ?_⟩
  ext b
  by_cases hb : b = i7
  · subst hb
    simp
  · simp [Finsupp.single_apply, Ne.symm hb, hzero b hb]

theorem beta_EAut {g : V K ≃ₗ[K] V K} (hg : g ∈ EAut K) (x y : V K) :
    beta (g x) (g y) = beta x y := by
  obtain ⟨g₀, hg₀, rfl⟩ := Subgroup.mem_map.mp hg
  exact E_isometry hg₀ x y

theorem span_orbit_w0 :
    Submodule.span K (Set.range fun g : EAut K => (g : V K ≃ₗ[K] V K) (w0 : V K)) = ⊤ := by
  set S := Submodule.span K (Set.range fun g : EAut K => (g : V K ≃ₗ[K] V K) (w0 : V K)) with hS
  have hmap : ∀ g ∈ EAut K, S.map (g : V K →ₗ[K] V K) ≤ S := by
    intro g hg
    rw [hS, Submodule.map_span, Submodule.span_le]
    rintro _ ⟨_, ⟨h, rfl⟩, rfl⟩
    exact Submodule.subset_span ⟨⟨g * h, (EAut K).mul_mem hg h.2⟩, rfl⟩
  have hinv : ∀ g ∈ EAut K, ∀ s ∈ S.toAddSubgroup, g s ∈ S.toAddSubgroup :=
    fun g hg s hs => hmap g hg ⟨s, hs, rfl⟩
  have hw : (w0 : V K) ∈ S := Submodule.subset_span ⟨⟨1, (EAut K).one_mem⟩, rfl⟩
  rcases EAut_irreducible_V S.toAddSubgroup hinv with h | h
  · exfalso
    have hw' : (w0 : V K) ∈ S.toAddSubgroup := hw
    rw [h, AddSubgroup.mem_bot] at hw'
    exact Finsupp.single_ne_zero.2 one_ne_zero hw'
  · rw [eq_top_iff]
    intro v _
    have hv : v ∈ S.toAddSubgroup := by
      rw [h]
      exact AddSubgroup.mem_top v
    exact hv

theorem eq_of_beta_eq {y z : V K} (h : ∀ x : V K, beta x y = beta x z) : y = z := by
  ext a
  have h1 := h (Finsupp.single (opp a) 1)
  rwa [MinuscT.beta_single_left, MinuscT.beta_single_left, opp_opp] at h1

@[expose] noncomputable def betaRep (B' : V K →ₗ[K] V K →ₗ[K] K) : V K →ₗ[K] V K :=
  (Finsupp.linearEquivFunOnFinite K K (Fin e7Data.d)).symm.toLinearMap ∘ₗ
    LinearMap.pi fun a => B' (Finsupp.single (opp a) 1)

theorem betaRep_apply (B' : V K →ₗ[K] V K →ₗ[K] K) (v : V K) (a : Fin e7Data.d) :
    betaRep B' v a = B' (Finsupp.single (opp a) 1) v := rfl

theorem beta_betaRep (B' : V K →ₗ[K] V K →ₗ[K] K) (u v : V K) :
    beta u (betaRep B' v) = B' u v := by
  induction u using Finsupp.induction_linear with
  | zero =>
    have h := beta_add_left (0 : V K) 0 (betaRep B' v)
    rw [add_zero] at h
    rw [map_zero, LinearMap.zero_apply]
    exact left_eq_add.mp h
  | add x y hx hy => rw [beta_add_left, hx, hy, map_add, LinearMap.add_apply]
  | single a c =>
    have hs : (Finsupp.single a c : V K) = c • Finsupp.single a 1 := by
      rw [Finsupp.smul_single, smul_eq_mul, mul_one]
    rw [hs, beta_smul_left, MinuscT.beta_single_left, betaRep_apply, opp_opp, map_smul,
      LinearMap.smul_apply, smul_eq_mul]

theorem betaRep_comm {B' : V K →ₗ[K] V K →ₗ[K] K}
    (hinv : ∀ g ∈ EAut K, ∀ u v : V K, B' (g u) (g v) = B' u v)
    {g : V K ≃ₗ[K] V K} (hg : g ∈ EAut K) (v : V K) :
    betaRep B' (g v) = g (betaRep B' v) := by
  refine eq_of_beta_eq fun u => ?_
  obtain ⟨u', rfl⟩ : ∃ u', u = g u' := ⟨g.symm u, (g.apply_symm_apply u).symm⟩
  rw [beta_betaRep, hinv g hg, beta_EAut hg, beta_betaRep]

theorem schur_V {T : V K →ₗ[K] V K} (hT : ∀ g ∈ EAut K, ∀ v : V K, T (g v) = g (T v)) :
    ∃ c : K, ∀ v : V K, T v = c • v := by
  have hfix : ∀ s ∈ rootSet7 K, s (T w0) = T w0 := fun s hs => by
    rw [← hT s (rootSet7_subset hs), rootSet7_fix s hs]
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp (mem_span_w0_of_fix hfix)
  have hall : T = c • LinearMap.id := by
    apply LinearMap.ext_on_range span_orbit_w0
    intro g
    rw [hT g g.2, ← hc, LinearMap.smul_apply, LinearMap.id_apply, map_smul]
  exact ⟨c, fun v => LinearMap.congr_fun hall v⟩

theorem invariant_bilinear_eq_smul_beta (B' : V K →ₗ[K] V K →ₗ[K] K)
    (hinv : ∀ g ∈ EAut K, ∀ u v : V K, B' (g u) (g v) = B' u v) :
    ∃ c : K, ∀ u v : V K, B' u v = c * beta u v := by
  obtain ⟨c, hc⟩ := schur_V fun g hg v => betaRep_comm hinv hg v
  exact ⟨c, fun u v => by rw [← beta_betaRep, hc, beta_smul_right]⟩

end CFSG.RankThree.GF2n.Smith81.E7Model

namespace CFSG.RankThree.GF2n.Smith81

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Stroth80 CFSG.RankThree.GF2n.Smith81.EGeom
  CFSG.LieType.Steinberg.Minuscule CFSG.RankThree.GF2n.Smith81.E7Model

theorem smith24E5Form_holds : Smith24E5FormStatement := by
  intro G _ _ M Q Z B IH hc h5 K _ _ γ M₀ hg ψ φ d
  have hctx : Ctx M Q Z B := hc.ctx
  haveI : CharP K 2 := by
    obtain ⟨m, -, hZm, -⟩ := hctx.hyp.cp
    exact charP_two_of_natCard_pow_two (hg.card.trans hZm)
  let B' : V K →ₗ[K] V K →ₗ[K] K :=
    M₀.B.compl₁₂ (ψ.symm : V K →ₗ[K] M₀.E) (ψ.symm : V K →ₗ[K] M₀.E)
  have hB' : ∀ u v, B' u v = M₀.B (ψ.symm u) (ψ.symm v) := fun u v => rfl
  have hinv : ∀ g ∈ EAut K, ∀ u v : V K, B' (g u) (g v) = B' u v := by
    intro g hg u v
    rw [← d.range] at hg
    obtain ⟨s, rfl⟩ := hg
    obtain ⟨hsM, hsC⟩ := Subgroup.mem_inf.mp (Lgen_le_H0 hctx s.2)
    have hcz : ∀ z ∈ Z, (s : G) * z * (s : G)⁻¹ = z := fun z hz => by
      rw [mul_inv_eq_iff_eq_mul]
      exact (Subgroup.mem_centralizer_iff.mp hsC z hz).symm
    obtain ⟨T, hTπ, -, hTB⟩ := hg.linear_of_centralizes hsM hcz
    have hφ : ∀ w : V K, ψ.symm (φ s w) = T (ψ.symm w) := by
      intro w
      obtain ⟨x, hx, hxw⟩ := M₀.π_surj (ψ.symm w)
      have hw : w = ψ (M₀.π x) := by rw [hxw, LinearEquiv.apply_symm_apply]
      rw [hw, ← d.equivariant s x hx, LinearEquiv.symm_apply_apply,
        LinearEquiv.symm_apply_apply, hTπ x hx]
    rw [hB', hB', hφ, hφ, hTB]
  obtain ⟨lam, hlam⟩ := E7Model.invariant_bilinear_eq_smul_beta B' hinv
  refine ⟨lam, ?_, fun e f => ?_⟩
  · intro h0
    have hzero : ∀ e f, M₀.B e f = 0 := fun e f => by
      have h1 := hlam (ψ e) (ψ f)
      rw [hB', h0, zero_mul, LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply] at h1
      exact h1
    have hne : ψ.symm (w0 : V K) ≠ 0 := by
      intro h
      have h2 : (w0 : V K) = 0 := by simpa using congrArg ψ h
      exact Finsupp.single_ne_zero.2 one_ne_zero h2
    exact hne (M₀.nondeg _ fun f => hzero _ f)
  · have h1 := hlam (ψ e) (ψ f)
    rwa [hB', LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply] at h1

end CFSG.RankThree.GF2n.Smith81
