module

public import CFSG.GroupTheory.WeirSylow.OrthogonalModels
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.UCTenSeven.OddSmallOrthogonalBase
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.UCTenSeven.OddSmallOrthogonalFour
import CFSG.ClassicalGroups.Orthogonal.ThreeDimensionalPlaneSylow
import CFSG.ClassicalInvolution.SmallOrth.Orth3Block

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.UCTenSeven

open Subgroup Module QuadraticMap

variable {K W : Type} [Field K] [Finite K] [AddCommGroup W] [Module K W] [FiniteDimensional K W]

private lemma two_ne_zero_of_odd_card (hodd : Odd (Nat.card K)) : (2 : K) ≠ 0 := by
  let fintypeK : Fintype K := Fintype.ofFinite K
  have h2 : Nat.card K % 2 = 1 := Nat.odd_iff.mp hodd
  rw [@Nat.card_eq_fintype_card K fintypeK] at h2
  exact @CFSG.RankThree.Classical.two_ne_zero_of_card_odd K _ fintypeK h2

private lemma finrank_ker_polarBilin (hodd : Odd (Nat.card K)) {Q : QuadraticForm K W}
    {u : W} (hu : Q u ≠ 0) :
    finrank K (LinearMap.ker (polarBilin Q u)) + 1 = finrank K W := by
  have h2 : (2 : K) ≠ 0 := two_ne_zero_of_odd_card hodd
  have hne : polarBilin Q u ≠ 0 := by
    intro h
    have hself : polarBilin Q u u = 0 := by rw [h]; rfl
    rw [polarBilin_apply_apply, polar_self] at hself
    have h2u : (2 : K) * Q u = 0 := by simpa [two_mul] using hself
    exact hu (mul_eq_zero.mp h2u |>.resolve_left h2)
  exact Module.Dual.finrank_ker_add_one_of_ne_zero hne

omit [FiniteDimensional K W] in
private lemma nondegenerate_comp_ker_polarBilin (hodd : Odd (Nat.card K))
    {Q : QuadraticForm K W} (hQ : (polarBilin Q).Nondegenerate) {u : W} (hu : Q u ≠ 0) :
    (polarBilin (Q.comp (LinearMap.ker (polarBilin Q u)).subtype)).Nondegenerate := by
  have h2 : (2 : K) ≠ 0 := two_ne_zero_of_odd_card hodd
  have hfu : polarBilin Q u u ≠ 0 := by
    rw [polarBilin_apply_apply, polar_self]
    have : (2 : K) * Q u ≠ 0 := mul_ne_zero h2 hu
    simpa [two_mul] using this
  have hcompl : IsCompl (LinearMap.ker (polarBilin Q u)) (K ∙ u) := by
    refine ⟨?_, ?_⟩
    · rw [Submodule.disjoint_def]
      intro x hx hx''
      have hx0 : polarBilin Q u x = 0 := LinearMap.mem_ker.mp hx
      rw [Submodule.mem_span_singleton] at hx''
      obtain ⟨a, rfl⟩ := hx''
      rw [polarBilin_apply_apply, polar_smul_right] at hx0
      have hx0' : a * polarBilin Q u u = 0 := by
        rwa [smul_eq_mul] at hx0
      have ha : a = 0 := (mul_eq_zero.mp hx0').resolve_right hfu
      rw [ha, zero_smul]
    · rw [codisjoint_iff, sup_comm]
      exact LinearMap.span_singleton_sup_ker_eq_top (polarBilin Q u) hfu
  have horth : ∀ x ∈ LinearMap.ker (polarBilin Q u), ∀ y ∈ K ∙ u, polar Q x y = 0 := by
    intro x hx y hy
    rw [Submodule.mem_span_singleton] at hy
    obtain ⟨a, rfl⟩ := hy
    have hx0 : polar Q u x = 0 := by
      rw [← polarBilin_apply_apply]
      exact LinearMap.mem_ker.mp hx
    rw [polar_smul_right, polar_comm, hx0, smul_zero]
  exact CFSG.ClassicalGroups.Orthogonal.Small.nondegenerate_comp_subtype hQ hcompl horth

private lemma odd_order_of_pow_eq_one {G : Type*} [Group G] {g : G} {p j : ℕ}
    (hp : p.Prime) (hp5 : 5 ≤ p) (hg : g ^ p ^ j = 1) : Odd (orderOf g) := by
  have hp_odd : Odd p := hp.odd_of_ne_two (by omega)
  have hpj_odd : Odd (p ^ j) := hp_odd.pow
  have hdvd : orderOf g ∣ p ^ j := orderOf_dvd_iff_pow_eq_one.mpr hg
  exact Odd.of_dvd_nat hpj_odd hdvd


omit [Finite K] [FiniteDimensional K W] in
private lemma nondegenerate_restrict_span_singleton {B : LinearMap.BilinForm K W} {x : W}
    (hx : B x x ≠ 0) : (B.restrict (K ∙ x)).Nondegenerate := by
  constructor
  · intro y hy
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp y.2
    have h := hy y
    change B (y : W) (y : W) = 0 at h
    rw [← ha] at h
    rw [map_smul, map_smul] at h
    have h' : a * (a * B x x) = 0 := by
      simpa [smul_eq_mul, mul_assoc] using h
    have ha0 : a = 0 := by
      rcases mul_eq_zero.mp h' with h1 | h2
      · exact h1
      · rcases mul_eq_zero.mp h2 with h3 | h4
        · exact h3
        · exact absurd h4 hx
    apply Subtype.ext
    rw [← ha, ha0, zero_smul]
    rfl
  · intro y hy
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp y.2
    have h := hy y
    change B (y : W) (y : W) = 0 at h
    rw [← ha] at h
    rw [map_smul, map_smul] at h
    have h' : a * (a * B x x) = 0 := by
      simpa [smul_eq_mul, mul_assoc] using h
    have ha0 : a = 0 := by
      rcases mul_eq_zero.mp h' with h1 | h2
      · exact h1
      · rcases mul_eq_zero.mp h2 with h3 | h4
        · exact h3
        · exact absurd h4 hx
    apply Subtype.ext
    rw [← ha, ha0, zero_smul]
    rfl

omit [Finite K] [FiniteDimensional K W] in
private lemma nondegenerate_restrict_sup_of_orthogonal {B : LinearMap.BilinForm K W}
    {V₁ V₂ : Submodule K W}
    (h1 : (B.restrict V₁).Nondegenerate) (h2 : (B.restrict V₂).Nondegenerate)
    (horth : ∀ u ∈ V₁, ∀ v ∈ V₂, B u v = 0) (horth' : ∀ v ∈ V₂, ∀ u ∈ V₁, B v u = 0) :
    (B.restrict (V₁ ⊔ V₂)).Nondegenerate := by
  constructor
  · intro y hy
    obtain ⟨y₁, hy₁, y₂, hy₂, hsum⟩ := Submodule.mem_sup.mp y.2
    have e1 : y₁ = 0 := by
      have := h1.1 ⟨y₁, hy₁⟩ (fun z => by
        have h := hy ⟨z, Submodule.mem_sup_left z.2⟩
        change B (y : W) (z : W) = 0 at h
        change B y₁ (z : W) = 0
        rw [← hsum, map_add, LinearMap.add_apply, horth' y₂ hy₂ z z.2, add_zero] at h
        exact h)
      exact congrArg Subtype.val this
    have e2 : y₂ = 0 := by
      have := h2.1 ⟨y₂, hy₂⟩ (fun z => by
        have h := hy ⟨z, Submodule.mem_sup_right z.2⟩
        change B (y : W) (z : W) = 0 at h
        change B y₂ (z : W) = 0
        rw [← hsum, map_add, LinearMap.add_apply, horth y₁ hy₁ z z.2, zero_add] at h
        exact h)
      exact congrArg Subtype.val this
    exact Subtype.ext (by rw [← hsum, e1, e2, add_zero]; rfl)
  · intro y hy
    obtain ⟨y₁, hy₁, y₂, hy₂, hsum⟩ := Submodule.mem_sup.mp y.2
    have e1 : y₁ = 0 := by
      have := h1.2 ⟨y₁, hy₁⟩ (fun z => by
        have h := hy ⟨z, Submodule.mem_sup_left z.2⟩
        change B (z : W) (y : W) = 0 at h
        change B (z : W) y₁ = 0
        rw [← hsum, map_add, horth z z.2 y₂ hy₂, add_zero] at h
        exact h)
      exact congrArg Subtype.val this
    have e2 : y₂ = 0 := by
      have := h2.2 ⟨y₂, hy₂⟩ (fun z => by
        have h := hy ⟨z, Submodule.mem_sup_right z.2⟩
        change B (z : W) (y : W) = 0 at h
        change B (z : W) y₂ = 0
        rw [← hsum, map_add, horth' z z.2 y₁ hy₁, zero_add] at h
        exact h)
      exact congrArg Subtype.val this
    exact Subtype.ext (by rw [← hsum, e1, e2, add_zero]; rfl)

theorem eq_one_of_mem_normalizer_sylow_of_finrank_eq_three (hodd : Odd (Nat.card K))
    {Q : QuadraticForm K W} (hQ : (polarBilin Q).Nondegenerate) (hdim : finrank K W = 3)
    (T : Sylow 2 (TauCeti.QuadraticMap.orthogonalGroup Q))
    {g : TauCeti.QuadraticMap.orthogonalGroup Q} {p j : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hg : g ^ p ^ j = 1)
    (hgT : g ∈ normalizer
      ((T : Subgroup (TauCeti.QuadraticMap.orthogonalGroup Q)) :
        Set (TauCeti.QuadraticMap.orthogonalGroup Q))) :
    g = 1 := by
  classical
  open CFSG.ClassicalGroups.Orthogonal.ThreeDimensionalPlaneSylow in
  obtain ⟨b, hbT, hbc, hb2, hb1, u, v, hu, hv, huv, hbu, hbv, hfix⟩ :=
    exists_central_plane_negation_of_sylow Q hodd hQ hdim T
  let n : TauCeti.QuadraticMap.orthogonalGroup Q := QuadraticMap.negOrthogonal Q
  have hn_central : ∀ x : TauCeti.QuadraticMap.orthogonalGroup Q, x * n = n * x := by
    intro x
    apply Subtype.ext
    change (x : W ≃ₗ[K] W) * (n : W ≃ₗ[K] W) = (n : W ≃ₗ[K] W) * (x : W ≃ₗ[K] W)
    rw [show (n : W ≃ₗ[K] W) = LinearEquiv.neg K from QuadraticMap.coe_negOrthogonal Q]
    ext w
    simp [LinearEquiv.neg_apply, LinearEquiv.mul_apply]
  have hnT : n ∈ (T : Subgroup (TauCeti.QuadraticMap.orthogonalGroup Q)) := by
    have hn_pgroup : IsPGroup 2 (Subgroup.zpowers n) := by
      have hord : orderOf n = 2 := by
        apply orderOf_eq_prime _ (by
          intro h
          have hcoe : (n : W ≃ₗ[K] W) = 1 := by rw [h]; rfl
          rw [show (n : W ≃ₗ[K] W) = LinearEquiv.neg K from
            QuadraticMap.coe_negOrthogonal Q] at hcoe
          have hpos : 0 < finrank K W := by omega
          have htop : (⊤ : Submodule K W) ≠ ⊥ := by
            intro hbot
            have h0 : finrank K (⊤ : Submodule K W) = finrank K (⊥ : Submodule K W) := by rw [hbot]
            rw [finrank_top, finrank_bot] at h0
            omega
          obtain ⟨w, _, hw⟩ := Submodule.exists_mem_ne_zero_of_ne_bot htop
          have hw' := congrArg (fun (f : W ≃ₗ[K] W) => f w) hcoe
          simp at hw'
          have h2w : (2 : K) • w = 0 := by
            rw [two_smul]
            nth_rewrite 2 [← hw']
            exact add_neg_cancel w
          exact hw (smul_eq_zero.mp h2w |>.resolve_left (two_ne_zero_of_odd_card hodd)))
        rw [pow_two]
        exact QuadraticMap.negOrthogonal_mul_self Q
      exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hord]; norm_num)
    have hT2 : IsPGroup 2 ((T : Subgroup (TauCeti.QuadraticMap.orthogonalGroup Q))) :=
      Sylow.isPGroup' T
    have hnorm : (T : Subgroup (TauCeti.QuadraticMap.orthogonalGroup Q)) ≤
        Subgroup.normalizer
          ((Subgroup.zpowers n) : Set (TauCeti.QuadraticMap.orthogonalGroup Q)) := by
      rw [Subgroup.le_set_normalizer_iff]
      intro x hx y hy
      rcases Subgroup.mem_zpowers_iff.mp hy with ⟨k, rfl⟩
      have hk : x * n ^ k = n ^ k * x := (Commute.zpow_right (hn_central x) k).eq
      rw [hk, mul_assoc, mul_inv_cancel, mul_one]
      exact Subgroup.mem_zpowers_iff.mpr ⟨k, rfl⟩
    have hsup : IsPGroup 2
        ↥(((T : Subgroup (TauCeti.QuadraticMap.orthogonalGroup Q)) ⊔ Subgroup.zpowers n)) :=
      IsPGroup.to_sup_of_normal_right' hT2 hn_pgroup hnorm
    have hmax := Sylow.is_maximal' T hsup le_sup_left
    rw [← hmax]
    exact Subgroup.mem_sup_right (Subgroup.mem_zpowers n)
  have hu_ne : u ≠ 0 := by
    intro h; rw [h, map_zero] at hu; exact one_ne_zero hu.symm
  have hv_ne : v ≠ 0 := by
    intro h; rw [h, map_zero] at hv; exact one_ne_zero hv.symm
  have hbuu : polarBilin Q u u ≠ 0 := by
    rw [polarBilin_apply_apply, polar_self, hu]
    simpa using two_ne_zero_of_odd_card hodd
  have hbvv : polarBilin Q v v ≠ 0 := by
    rw [polarBilin_apply_apply, polar_self, hv]
    simpa using two_ne_zero_of_odd_card hodd
  have hline_u : (LinearMap.BilinForm.restrict (polarBilin Q) (K ∙ u)).Nondegenerate :=
    nondegenerate_restrict_span_singleton hbuu
  have hline_v : (LinearMap.BilinForm.restrict (polarBilin Q) (K ∙ v)).Nondegenerate :=
    nondegenerate_restrict_span_singleton hbvv
  have horth_uv : ∀ x ∈ K ∙ u, ∀ y ∈ K ∙ v, polarBilin Q x y = 0 := by
    intro x hx y hy
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hx
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hy
    rw [← ha, ← hc]
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul, huv, mul_zero]
  have horth_vu : ∀ y ∈ K ∙ v, ∀ x ∈ K ∙ u, polarBilin Q y x = 0 := by
    intro y hy x hx
    rw [polarBilin_apply_apply, polar_comm, ← polarBilin_apply_apply]
    exact horth_uv x hx y hy
  let P : Submodule K W := K ∙ u ⊔ K ∙ v
  have hP_nd : (LinearMap.BilinForm.restrict (polarBilin Q) P).Nondegenerate :=
    nondegenerate_restrict_sup_of_orthogonal hline_u hline_v horth_uv horth_vu
  have hLI : LinearIndependent K ![u, v] := by
    rw [LinearIndependent.pair_iff' hu_ne]
    intro a ha
    apply hv_ne
    have h : polarBilin Q u (a • u) = 0 := by
      rw [ha, huv]
    rw [polarBilin_apply_apply, polar_smul_right] at h
    have h' : a * polarBilin Q u u = 0 := by
      rwa [smul_eq_mul] at h
    have ha0 : a = 0 := (mul_eq_zero.mp h').resolve_right hbuu
    rw [← ha, ha0, zero_smul]
  have hP_fin : finrank K P = 2 := by
    have hfin_u : finrank K (K ∙ u) = 1 := finrank_span_singleton hu_ne
    have hfin_v : finrank K (K ∙ v) = 1 := finrank_span_singleton hv_ne
    have hdisj : K ∙ u ⊓ K ∙ v = ⊥ := by
      rw [Submodule.eq_bot_iff]
      intro x hx
      rw [Submodule.mem_inf] at hx
      obtain ⟨hxu, hxv⟩ := hx
      obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hxu
      obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hxv
      have h1 : polarBilin Q (c • v) v = 0 := by
        have hcv : c • v = a • u := hc.trans ha.symm
        rw [hcv, map_smul, LinearMap.smul_apply, huv, smul_zero]
      rw [LinearMap.map_smul, LinearMap.smul_apply, polarBilin_apply_apply, polar_self] at h1
      have h' : c * (2 * Q v) = 0 := by
        simpa [smul_eq_mul] using h1
      have hc0 : c = 0 := by
        rcases mul_eq_zero.mp h' with hc' | h2v
        · exact hc'
        · rcases mul_eq_zero.mp h2v with h2' | hv'
          · exact absurd h2' (two_ne_zero_of_odd_card hodd)
          · exact absurd hv' (by rw [hv]; exact one_ne_zero)
      rw [← hc, hc0, zero_smul]
    have h := Submodule.finrank_sup_add_finrank_inf_eq (K ∙ u) (K ∙ v)
    rw [hdisj, finrank_bot, hfin_u, hfin_v] at h
    dsimp [P]
    omega
  have hrefl : (polarBilin Q).IsRefl := (QuadraticMap.isSymm_polarBilin Q).isRefl
  have hcompl : IsCompl P (LinearMap.BilinForm.orthogonal (polarBilin Q) P) :=
    LinearMap.BilinForm.isCompl_orthogonal_of_restrict_nondegenerate hrefl hP_nd
  have horth_fin : finrank K (LinearMap.BilinForm.orthogonal (polarBilin Q) P) = 1 := by
    rw [LinearMap.BilinForm.finrank_orthogonal hQ P, hP_fin, hdim]
  have hne_bot : LinearMap.BilinForm.orthogonal (polarBilin Q) P ≠ ⊥ := by
    intro h
    have h0 : finrank K (LinearMap.BilinForm.orthogonal (polarBilin Q) P) = 0 := by
      rw [h, finrank_bot]
    omega
  obtain ⟨w, hw_mem, hw_ne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne_bot
  have hspan_w : LinearMap.BilinForm.orthogonal (polarBilin Q) P = K ∙ w := by
    have hle : K ∙ w ≤ LinearMap.BilinForm.orthogonal (polarBilin Q) P :=
      (Submodule.span_singleton_le_iff_mem w
        (LinearMap.BilinForm.orthogonal (polarBilin Q) P)).mpr hw_mem
    have hfin_w : finrank K (K ∙ w) = 1 := finrank_span_singleton hw_ne
    have heq : finrank K (K ∙ w) = finrank K (LinearMap.BilinForm.orthogonal (polarBilin Q) P) := by
      rw [hfin_w, horth_fin]
    exact (Submodule.eq_of_le_of_finrank_eq hle heq).symm
  have hQw : Q w ≠ 0 := by
    intro hQw
    have hw_rad : w ∈ LinearMap.BilinForm.orthogonal (polarBilin Q) (⊤ : Submodule K W) := by
      rw [LinearMap.BilinForm.mem_orthogonal_iff]
      intro x _
      obtain ⟨p, q, hx_eq⟩ :=
        CFSG.LocalAnalysis.ComponentInitial.exists_add_of_isCompl hcompl x
      rw [hx_eq, map_add, LinearMap.add_apply]
      have h1 : polarBilin Q (p : W) w = 0 :=
        (LinearMap.BilinForm.mem_orthogonal_iff.mp hw_mem) (p : W) p.2
      have h2 : polarBilin Q q w = 0 := by
        have hq' : (q : W) ∈ K ∙ w := by
          rw [← hspan_w]
          exact q.2
        obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hq'
        rw [← hc, LinearMap.map_smul, LinearMap.smul_apply, polarBilin_apply_apply, polar_self, hQw]
        simp
      rw [h1, h2, add_zero]
    have hw0 : w = 0 := hQ.1 w (fun y => by
      have h := (LinearMap.BilinForm.mem_orthogonal_iff.mp hw_rad) y
        (Submodule.mem_top : y ∈ (⊤ : Submodule K W))
      rw [polarBilin_apply_apply] at h ⊢
      rw [polar_comm]
      exact h)
    exact hw_ne hw0
  have instW : Invertible (Q w) := invertibleOfNonzero hQw
  have hbP : ∀ p ∈ P, (b : W ≃ₗ[K] W) p = -p := by
    intro p hp
    rw [Submodule.mem_sup] at hp
    obtain ⟨y, hy, z, hz, rfl⟩ := hp
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hy
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hz
    rw [map_add, map_smul, map_smul, hbu, hbv, smul_neg, smul_neg]
    abel
  have hbPperp : ∀ q ∈ LinearMap.BilinForm.orthogonal (polarBilin Q) P,
      (b : W ≃ₗ[K] W) q = q := by
    intro q hq
    apply hfix
    · exact (LinearMap.BilinForm.mem_orthogonal_iff.mp hq) u
        (Submodule.mem_sup_left (Submodule.mem_span_singleton_self u))
    · exact (LinearMap.BilinForm.mem_orthogonal_iff.mp hq) v
        (Submodule.mem_sup_right (Submodule.mem_span_singleton_self v))
  have hn_apply : ∀ x : W, (n : W ≃ₗ[K] W) x = -x := by
    intro x
    rw [show (n : W ≃ₗ[K] W) = LinearEquiv.neg K from QuadraticMap.coe_negOrthogonal Q]
    rfl
  have hrefP : ∀ p ∈ P,
      (@TauCeti.QuadraticMap.reflectionOrthogonal K W _ _ _ Q w instW : W ≃ₗ[K] W) p = p := by
    intro p hp
    have horth : QuadraticMap.IsOrtho Q w p :=
      QuadraticMap.isOrtho_polarBilin.mp (by
        rw [polarBilin_apply_apply, polar_comm]
        exact (LinearMap.BilinForm.mem_orthogonal_iff.mp hw_mem) p hp)
    rw [TauCeti.QuadraticMap.coe_reflectionOrthogonal]
    exact @TauCeti.QuadraticMap.reflection_apply_of_isOrtho K W _ _ _ Q w instW p horth
  have hrefPperp : ∀ q ∈ LinearMap.BilinForm.orthogonal (polarBilin Q) P,
      (@TauCeti.QuadraticMap.reflectionOrthogonal K W _ _ _ Q w instW : W ≃ₗ[K] W) q = -q := by
    intro q hq
    have hq' : q ∈ K ∙ w := by
      rw [← hspan_w]
      exact hq
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hq'
    rw [map_smul]
    have hww : (@TauCeti.QuadraticMap.reflectionOrthogonal K W _ _ _ Q w instW : W ≃ₗ[K] W) w =
        -w := by
      rw [TauCeti.QuadraticMap.coe_reflectionOrthogonal]
      exact @TauCeti.QuadraticMap.reflection_apply_self K W _ _ _ Q w instW
    rw [hww, smul_neg]
  have hnegb_eq : n * b = @TauCeti.QuadraticMap.reflectionOrthogonal K W _ _ _ Q w instW := by
    apply Subtype.ext
    apply LinearEquiv.ext
    intro x
    obtain ⟨p, q, hx_eq⟩ := CFSG.LocalAnalysis.ComponentInitial.exists_add_of_isCompl hcompl x
    rw [hx_eq]
    change (n : W ≃ₗ[K] W) ((b : W ≃ₗ[K] W) ((p : W) + (q : W))) =
      (@TauCeti.QuadraticMap.reflectionOrthogonal K W _ _ _ Q w instW : W ≃ₗ[K] W)
        ((p : W) + (q : W))
    calc (n : W ≃ₗ[K] W) ((b : W ≃ₗ[K] W) ((p : W) + (q : W)))
        = (n : W ≃ₗ[K] W) ((b : W ≃ₗ[K] W) (p : W) + (b : W ≃ₗ[K] W) (q : W)) := by
          rw [map_add]
      _ = (n : W ≃ₗ[K] W) (-(p : W) + (q : W)) := by rw [hbP p p.2, hbPperp q q.2]
      _ = (n : W ≃ₗ[K] W) (-(p : W)) + (n : W ≃ₗ[K] W) (q : W) := by rw [map_add]
      _ = -(-(p : W)) + -(q : W) := by rw [hn_apply, hn_apply]
      _ = (@TauCeti.QuadraticMap.reflectionOrthogonal K W _ _ _ Q w instW : W ≃ₗ[K] W)
          ((p : W) + (q : W)) := by
        rw [map_add, hrefP p p.2, hrefPperp q q.2]
        abel
  have href_mem : @TauCeti.QuadraticMap.reflectionOrthogonal K W _ _ _ Q w instW ∈
      (T : Subgroup (TauCeti.QuadraticMap.orthogonalGroup Q)) := by
    rw [← hnegb_eq]
    exact mul_mem hnT hbT
  have href_central : ∀ t ∈ (T : Subgroup (TauCeti.QuadraticMap.orthogonalGroup Q)),
      t * @TauCeti.QuadraticMap.reflectionOrthogonal K W _ _ _ Q w instW =
        @TauCeti.QuadraticMap.reflectionOrthogonal K W _ _ _ Q w instW * t := by
    intro t ht
    rw [← hnegb_eq]
    calc t * (n * b) = (t * n) * b := by group
      _ = (n * t) * b := by rw [hn_central t]
      _ = n * (t * b) := by group
      _ = n * (b * t) := by rw [hbc t ht]
      _ = (n * b) * t := by group
  have hgw : (g : W ≃ₗ[K] W) w = w :=
    @apply_eq_self_of_central_reflection K W _ _ _ _ _ hodd Q (by omega)
      (T : Subgroup (TauCeti.QuadraticMap.orthogonalGroup Q)) w instW
      href_mem href_central g p j hp hp5 hg hgT
  have hQ' : (polarBilin (Q.comp (LinearMap.ker (polarBilin Q w)).subtype)).Nondegenerate :=
    nondegenerate_comp_ker_polarBilin hodd hQ hQw
  have hfin' : finrank K (LinearMap.ker (polarBilin Q w)) + 1 = finrank K W :=
    finrank_ker_polarBilin hodd hQw
  have hdim' : finrank K (LinearMap.ker (polarBilin Q w)) ≤ 2 := by omega
  exact @eq_one_of_central_reflection K W _ _ _ _ _ hodd Q hQ T w instW
      href_mem href_central g (p ^ j) hg hgT hgw
    (fun T' g' hg' hg'T' =>
      eq_one_of_mem_normalizer_sylow_of_finrank_le_two hodd hQ' hdim' T'
        (odd_order_of_pow_eq_one hp hp5 hg') hg'T')

theorem eq_one_of_mem_normalizer_sylow_small (hodd : Odd (Nat.card K))
    {Q : QuadraticForm K W} (hQ : (polarBilin Q).Nondegenerate) (hdim : finrank K W ≤ 4)
    (hminus : finrank K W = 4 → ¬ CFSG.GroupTheory.WeirSylow.IsPlusType Q)
    (T : Sylow 2 (TauCeti.QuadraticMap.orthogonalGroup Q))
    {g : TauCeti.QuadraticMap.orthogonalGroup Q} {p j : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hg : g ^ p ^ j = 1)
    (hgT : g ∈ normalizer
      ((T : Subgroup (TauCeti.QuadraticMap.orthogonalGroup Q)) :
        Set (TauCeti.QuadraticMap.orthogonalGroup Q))) :
    g = 1 := by
  rcases Nat.lt_or_ge 2 (finrank K W) with h2 | h2
  · have h3 : finrank K W = 3 ∨ finrank K W = 4 := by omega
    rcases h3 with h3 | h4
    · exact eq_one_of_mem_normalizer_sylow_of_finrank_eq_three hodd hQ h3 T hp hp5 hg hgT
    · obtain ⟨u, hu_inv, hu_mem, hu_central⟩ :=
        exists_central_reflection_of_finrank_eq_four hodd hQ h4 (hminus h4) T
      have hQu : Q u ≠ 0 := by
        intro h
        have := isUnit_of_invertible (Q u)
        exact this.ne_zero h
      have hgu : (g : W ≃ₗ[K] W) u = u :=
        @apply_eq_self_of_central_reflection K W _ _ _ _ _ hodd Q (by omega)
          (T : Subgroup (TauCeti.QuadraticMap.orthogonalGroup Q)) u hu_inv
          hu_mem hu_central g p j hp hp5 hg hgT
      have hQ' : (polarBilin (Q.comp (LinearMap.ker (polarBilin Q u)).subtype)).Nondegenerate :=
        nondegenerate_comp_ker_polarBilin hodd hQ hQu
      have hfin' : finrank K (LinearMap.ker (polarBilin Q u)) + 1 = finrank K W :=
        finrank_ker_polarBilin hodd hQu
      have hdim3 : finrank K (LinearMap.ker (polarBilin Q u)) = 3 := by omega
      exact @eq_one_of_central_reflection K W _ _ _ _ _ hodd Q hQ T u hu_inv
          hu_mem hu_central g (p ^ j) hg hgT hgu
        (fun T' g' hg' hg'T' =>
          eq_one_of_mem_normalizer_sylow_of_finrank_eq_three hodd hQ' hdim3 T' hp hp5 hg' hg'T')
  · exact eq_one_of_mem_normalizer_sylow_of_finrank_le_two hodd hQ h2 T
      (odd_order_of_pow_eq_one hp hp5 hg) hgT

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.UCTenSeven
