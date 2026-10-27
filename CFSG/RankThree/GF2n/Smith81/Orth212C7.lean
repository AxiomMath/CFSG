module

public import CFSG.RankThree.GF2n.Smith81.Orth28Route

public section

namespace CFSG.RankThree.GF2n.Smith81

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Stroth80
open scoped commutatorElement

variable {G : Type} [Group G]

theorem orth212C7_theta_zero [Finite G]
    (h4 : Orth212C4CondStatement) (h28 : Smith28OrthStatement)
    {M Q Z B X : Subgroup G} (hcfg : SmithOrthCfg M Q Z B) {x : G} (hs : Sit M Q Z X x)
    {c : G} (hcx : ⁅c, x⁆ ∈ Z) : ⁅c, x⁆ = 1 := by
  have hcomm : x * ⁅c, x⁆ = ⁅c, x⁆ * x := by
    have h := hs.x_cent (smith_1_12 hs) _ hcx
    rw [mul_inv_eq_iff_eq_mul] at h
    exact h
  have hconj : IsConj x (x * ⁅c, x⁆) := by
    refine isConj_iff.mpr ⟨c, ?_⟩
    rw [hcomm, commutatorElement_def]
    group
  exact h4 G M Q Z B hcfg X x hs (smith28aOrth_of_28 h28 G M Q Z B hcfg X x hs) _ hcx hconj

theorem orth212C7_sit_conj {M Q Z X : Subgroup G} {x h : G} (hs : Sit M Q Z X x)
    (hyM : h * x * h⁻¹ ∈ M) (hyQ : h * x * h⁻¹ ∉ Q) :
    Sit M Q Z (conjSubgroup h X) (h * x * h⁻¹) := by
  obtain ⟨g, hg⟩ := hs.conj
  refine ⟨hs.hyp, ⟨h * g, ?_⟩, ?_, ?_, hyM, hyQ⟩
  · rw [hg, conjSubgroup_mul]
  · rw [mem_conjSubgroup]
    have e : h⁻¹ * (h * x * h⁻¹) * h = x := by group
    rw [e]
    exact hs.mem
  · intro h1
    apply hs.ne_one
    calc x = h⁻¹ * (h * x * h⁻¹) * h := by group
      _ = 1 := by rw [h1]; group

theorem orth212C7_nondegenerate_of_alt {K E : Type} [Field K] [AddCommGroup E] [Module K E]
    {B : LinearMap.BilinForm K E} (halt : ∀ e, B e e = 0)
    (hl : ∀ e, (∀ f, B e f = 0) → e = 0) : B.Nondegenerate := by
  have hanti : ∀ e f, B e f + B f e = 0 := by
    intro e f
    have h := halt (e + f)
    simpa [map_add, halt, add_comm] using h
  refine And.intro hl fun f hf => hl f fun e => ?_
  have h1 := hanti f e
  rw [hf e, add_zero] at h1
  exact h1

theorem orth212C7_perp_ker_eq_range {K E : Type} [Field K] [AddCommGroup E] [Module K E]
    [FiniteDimensional K E] {B : LinearMap.BilinForm K E} (hB : B.Nondegenerate)
    (T : E →ₗ[K] E) (hT : ∀ e f, B (T e) (T f) = B e f) :
    B.orthogonal (LinearMap.ker (T - LinearMap.id)) = LinearMap.range (T - LinearMap.id) := by
  have hle : LinearMap.range (T - LinearMap.id) ≤
      B.orthogonal (LinearMap.ker (T - LinearMap.id)) := by
    rintro _ ⟨w, rfl⟩
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    intro n hn
    rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero] at hn
    have h1 : B n (T w) = B n w := by
      have h := hT n w
      rw [hn] at h
      exact h
    rw [LinearMap.sub_apply, LinearMap.id_apply, map_sub, h1, sub_self]
  have hd : Module.finrank K (LinearMap.range (T - LinearMap.id)) =
      Module.finrank K (B.orthogonal (LinearMap.ker (T - LinearMap.id))) := by
    have h1 := LinearMap.finrank_range_add_finrank_ker (T - LinearMap.id)
    have h2 := LinearMap.BilinForm.finrank_orthogonal hB (LinearMap.ker (T - LinearMap.id))
    omega
  exact (Submodule.eq_of_le_of_finrank_eq hle hd).symm

theorem orth212C7Cond_of_C4 (h4 : Orth212C4CondStatement)
    (h28 : Smith28OrthStatement) : Orth212C7CondStatement := by
  intro G _ _ M Q Z B hcfg X x hs _ h q hq hhx
  have H := hs.hyp
  have hxM : x ∈ M := hs.memM
  have hx2 : x * x = 1 := hs.x_sq
  have hxinv : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx2
  have hxc : ∀ z ∈ Z, x * z * x⁻¹ = z := hs.x_cent (smith_1_12 hs)
  have hqM : q ∈ M := H.Q_normal.1 hq
  obtain ⟨k, γ, M₀, -, hD⟩ := stroth_globalModelDataGF H
  obtain ⟨T, hTπ, -, hTB⟩ := hD.linear_of_centralizes hxM hxc
  have hB : M₀.B.Nondegenerate := orth212C7_nondegenerate_of_alt M₀.alt M₀.nondeg
  have hperp := orth212C7_perp_ker_eq_range hB T.toLinearMap hTB
  have hπ1 : M₀.π 1 = 0 := by
    have h := M₀.π_mul 1 Q.one_mem 1 Q.one_mem
    rw [mul_one] at h
    exact left_eq_add.mp h
  have hπinv : ∀ a ∈ Q, M₀.π a⁻¹ = -M₀.π a := by
    intro a ha
    have h := M₀.π_mul a ha a⁻¹ (Q.inv_mem ha)
    rw [mul_inv_cancel, hπ1] at h
    exact eq_neg_of_add_eq_zero_right h.symm
  have hmemq : M₀.π q ∈ M₀.B.orthogonal (LinearMap.ker (T.toLinearMap - LinearMap.id)) := by
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    intro e he
    have hTe : T e = e := by simpa [sub_eq_zero] using he
    obtain ⟨w, hw, hwe⟩ := M₀.π_surj e
    have hwxQ : ⁅w, x⁆ ∈ Q := comm_mem_Q H hxM hw
    have hxwQ : x * w * x⁻¹ ∈ Q := conj_mem_Q H hxM hw
    have hπwx : M₀.π ⁅w, x⁆ = 0 := by
      have e1 : ⁅w, x⁆ = w * (x * w * x⁻¹)⁻¹ := by
        simp only [commutatorElement_def]; group
      rw [e1, M₀.π_mul w hw _ (Q.inv_mem hxwQ), hπinv _ hxwQ, hTπ w hw, hwe, hTe,
        add_neg_cancel]
    have hwxZ : ⁅w, x⁆ ∈ Z := (M₀.π_ker ⁅w, x⁆ hwxQ).mp hπwx
    have hθ : ⁅w, x⁆ = 1 := orth212C7_theta_zero h4 h28 hcfg hs hwxZ
    have hyM : h * x * h⁻¹ ∈ M := by
      rw [hhx]; exact M.mul_mem hxM hqM
    have hyQ : h * x * h⁻¹ ∉ Q := by
      rw [hhx]
      intro hxq
      apply hs.notQ
      have e2 : x = x * q * q⁻¹ := by group
      rw [e2]
      exact Q.mul_mem hxq (Q.inv_mem hq)
    have hsy := orth212C7_sit_conj hs hyM hyQ
    have hwq : ⁅w, q⁆ = 1 := by
      have hc : ⁅w, h * x * h⁻¹⁆ = ⁅w, q⁆ := by
        rw [hhx]
        have e3 : ⁅w, x * q⁆ = ⁅w, x⁆ * (x * ⁅w, q⁆ * x⁻¹) := by
          simp only [commutatorElement_def]; group
        rw [e3, hθ, one_mul, hxc _ (comm_mem_Z H hw hq)]
      have hZ : ⁅w, h * x * h⁻¹⁆ ∈ Z := by
        rw [hc]; exact comm_mem_Z H hw hq
      rw [← hc]
      exact orth212C7_theta_zero h4 h28 hcfg hsy hZ
    have h0 := (GM.comm_eq_one_iff hD hw hq).mp hwq
    rw [hwe] at h0
    exact h0
  have hmem : M₀.π q ∈ LinearMap.range (T.toLinearMap - LinearMap.id) := by
    rw [← hperp]; exact hmemq
  obtain ⟨e', he'⟩ := LinearMap.mem_range.mp hmem
  have hTe' : T e' - e' = M₀.π q := by simpa using he'
  obtain ⟨q₀, hq₀, hq₀e⟩ := M₀.π_surj e'
  have hxq₀ : x * q₀ * x⁻¹ ∈ Q := conj_mem_Q H hxM hq₀
  have e2 : ⁅x, q₀⁆ = (x * q₀ * x⁻¹) * q₀⁻¹ := by
    simp only [commutatorElement_def]
  have hcQ : ⁅x, q₀⁆ ∈ Q := by
    rw [e2]; exact Q.mul_mem hxq₀ (Q.inv_mem hq₀)
  have hπc : M₀.π ⁅x, q₀⁆ = M₀.π q := by
    rw [e2, M₀.π_mul _ hxq₀ _ (Q.inv_mem hq₀), hπinv _ hq₀, hTπ q₀ hq₀, hq₀e,
      ← sub_eq_add_neg, hTe']
  obtain ⟨z₀, hz₀⟩ : ∃ z₀ : G, z₀ = ⁅x, q₀⁆⁻¹ * q := ⟨_, rfl⟩
  have hz₀Q : z₀ ∈ Q := by
    rw [hz₀]; exact Q.mul_mem (Q.inv_mem hcQ) hq
  have hq_eq : q = ⁅x, q₀⁆ * z₀ := by
    rw [hz₀, mul_inv_cancel_left]
  have hz₀π : M₀.π z₀ = 0 := by
    rw [hz₀, M₀.π_mul _ (Q.inv_mem hcQ) _ hq, hπinv _ hcQ, hπc, neg_add_cancel]
  have hz₀Z : z₀ ∈ Z := (M₀.π_ker z₀ hz₀Q).mp hz₀π
  have hyx : h * x * h⁻¹ = q₀ * x * q₀⁻¹ * z₀ := by
    rw [hhx, hq_eq, commutatorElement_def, hxinv]
    calc x * (x * q₀ * x * q₀⁻¹ * z₀) = (x * x) * q₀ * x * q₀⁻¹ * z₀ := by group
      _ = q₀ * x * q₀⁻¹ * z₀ := by rw [hx2, one_mul]
  have hx₁M : q₀ * x * q₀⁻¹ ∈ M :=
    M.mul_mem (M.mul_mem (H.Q_normal.1 hq₀) hxM) (M.inv_mem (H.Q_normal.1 hq₀))
  have hx₁Q : q₀ * x * q₀⁻¹ ∉ Q := by
    intro h1
    apply hs.notQ
    have e4 : x = q₀⁻¹ * (q₀ * x * q₀⁻¹) * q₀⁻¹⁻¹ := by group
    rw [e4]
    exact conj_mem_Q H (M.inv_mem (H.Q_normal.1 hq₀)) h1
  have hs₁ := orth212C7_sit_conj hs hx₁M hx₁Q
  have hconj₁ : IsConj (q₀ * x * q₀⁻¹) (q₀ * x * q₀⁻¹ * z₀) := by
    rw [← hyx]
    exact (show IsConj (q₀ * x * q₀⁻¹) x from isConj_iff.mpr ⟨q₀⁻¹, by group⟩).trans
      (show IsConj x (h * x * h⁻¹) from isConj_iff.mpr ⟨h, rfl⟩)
  have hz₁ : z₀ = 1 :=
    h4 G M Q Z B hcfg _ _ hs₁ (smith28aOrth_of_28 h28 G M Q Z B hcfg _ _ hs₁) z₀ hz₀Z hconj₁
  refine ⟨q₀, hq₀, ?_⟩
  rw [hyx, hz₁, mul_one]

end CFSG.RankThree.GF2n.Smith81
