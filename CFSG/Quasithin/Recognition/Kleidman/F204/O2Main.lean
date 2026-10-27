module

public import CFSG.Quasithin.Recognition.Kleidman.F204.O2Pi

public section

namespace CFSG.Quasithin.Kleidman.F204

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin CFSG.Quasithin.F7
  CFSG.Quasithin.FA5 CFSG.OrderReductions.FrattiniAutomorphisms CFSG
  CFSG.QuasithinUnique.A5.Delta5

open scoped IsMulCommutative commutatorElement

set_option linter.unusedSectionVars false

variable {G : Type} [Group G] [Finite G] {L1 L2 S D X Z : Subgroup G}

theorem Z2_le_Q1 (F : Frame L1 L2 S D X) (hZ : ZData L1 L2 S Z) :
    Frame.Z2 L1 L2 S Z ≤ Q1 L1 L2 S := by
  by_contra hZ2
  obtain ⟨a, ha, haQ⟩ : ∃ a ∈ Frame.Z2 L1 L2 S Z, a ∉ Q1 L1 L2 S := by
    by_contra h
    push Not at h
    exact hZ2 (fun a ha => h a ha)
  obtain ⟨x0, hx0, hx05, hx01, -⟩ := F.exists_gen
  obtain ⟨d, hd, hd1⟩ := F.exists_ne_one_D
  have haS : a ∈ S := F.Q2_le_S (F.Z2_le_Q2 hZ ha)
  have haa : a * a = 1 := F.Z2_sq hZ a ha
  have haP : a ∈ P1 L1 L2 S := F.mem_P1_of_mem_S haS
  have hx0P : x0 ∈ P1 L1 L2 S := F.mem_P1_of_mem_X hx0
  have hdB : d ∈ bigB L1 L2 S := F.D_le_B hd
  have hdP : d ∈ P1 L1 L2 S := (le_sup_right : bigB L1 L2 S ≤ P1 L1 L2 S) hdB
  obtain ⟨hx5, htt, htx⟩ := theta_rel F hx0 hx05 haS haa haQ
  obtain ⟨hd3, hdx⟩ := theta_D_rel F (x0 := x0) hx0 hd
  have hrk := finrank_range_theta_le F hZ ha
  have hne := theta_x_ne F hx0 hx05 hx01
  have hdnt := theta_d_nontrivial F hZ ha haQ hx0 hx05 hx01 hd hd1
  obtain ⟨y0, hy0Z, hy0Q, hy0⟩ := exists_y0 F hZ ha haQ hx0 hx05 hx01
  set y := x0⁻¹ * y0 * x0 with hy
  have hyQ : y ∈ Q1 L1 L2 S := by
    have := (Subgroup.mem_normalizer_iff.mp (P1_le_normalizer_Q1 L1 L2 S
      ((P1 L1 L2 S).inv_mem hx0P)) y0).mp hy0Q
    simpa using this
  have hyQ2 : y ∉ Q2 L1 L2 S := hy0
  have hyT : y ∈ Tsub L1 L2 S Z x0 := Subgroup.subset_closure ⟨hyQ, -1, by
    have : (x0 ^ (-1 : ℤ))⁻¹ * y * x0 ^ (-1 : ℤ) = y0 := by rw [hy]; group
    rw [this]; exact hy0Z⟩
  obtain ⟨q, hqQ, hqQ2, hyq, hyq'⟩ := exists_third F hyQ hyQ2
  have hqP : q ∈ P2 L1 L2 S := Q1_mem_P2 F hqQ
  have hwZ : q * a * q⁻¹ * a⁻¹ ∈ Frame.Z2 L1 L2 S Z :=
    (Frame.Z2 L1 L2 S Z).mul_mem (Z2_norm hqP ha) ((Frame.Z2 L1 L2 S Z).inv_mem ha)
  have hwQ : q * a * q⁻¹ * a⁻¹ ∈ Q1 L1 L2 S := by
    have h1 : a * q⁻¹ * a⁻¹ ∈ Q1 L1 L2 S :=
      (Subgroup.mem_normalizer_iff.mp (P1_le_normalizer_Q1 L1 L2 S haP) q⁻¹).mp
        ((Q1 L1 L2 S).inv_mem hqQ)
    have := (Q1 L1 L2 S).mul_mem hqQ h1
    simpa [mul_assoc] using this
  have hwT : q * a * q⁻¹ * a⁻¹ ∈ Tsub L1 L2 S Z x0 :=
    Subgroup.subset_closure ⟨hwQ, 0, by simpa using hwZ⟩
  set c : CC L1 L2 S Z x0 := cmT (⟨y, hyT⟩ : TT L1 L2 S Z x0) ⟨q * a * q⁻¹ * a⁻¹, hwT⟩ with hc
  have hcG : (((c : CC L1 L2 S Z x0) : TT L1 L2 S Z x0) : G) = kc y q a := rfl
  set cd := cdC F hx0 hZ ha haQ hx05 hx01 hd with hcd
  set h0 : CC L1 L2 S Z x0 := c * cd c * cd (cd c) with hh0
  have hcc : ∀ c1 c2 : CC L1 L2 S Z x0, c1 * c2 = c2 * c1 := fun c1 c2 =>
    Subtype.ext (CC_central F hx0 hZ ha haQ hx05 hx01 c1 c2)
  have hh0ne : h0 ≠ 1 := by
    intro h1
    have h2 : (((h0 : CC L1 L2 S Z x0) : TT L1 L2 S Z x0) : G) = 1 := by rw [h1]; rfl
    have hd3' : d * d * d = 1 := by rw [← pow_three']; exact pow_three_of_mem_D F hd
    have e : (((h0 : CC L1 L2 S Z x0) : TT L1 L2 S Z x0) : G) =
        kc y q a * (d * kc y q a * d⁻¹) * (d⁻¹ * kc y q a * d) := by
      show kc y q a * (d * kc y q a * d⁻¹) * (d * (d * kc y q a * d⁻¹) * d⁻¹) = _
      have : d * (d * kc y q a * d⁻¹) * d⁻¹ = d⁻¹ * kc y q a * d := by
        have hdd : d * d = d⁻¹ := by
          have := congrArg (· * d⁻¹) hd3'
          simpa [mul_assoc] using this
        calc d * (d * kc y q a * d⁻¹) * d⁻¹ = (d * d) * kc y q a * (d * d)⁻¹ := by group
          _ = d⁻¹ * kc y q a * d := by rw [hdd]; group
      rw [this]
    rw [e] at h2
    exact kc_avg_ne_one F hZ hZ2 ha haQ hyQ hqQ hyQ2 hqQ2 hyq hyq' hd h2
  have hfix : cd h0 = h0 := by
    have hcube := cdC_cube F hx0 hZ ha haQ hx05 hx01 hd c
    rw [hh0, map_mul, map_mul, hcube]
    rw [show cd c * cd (cd c) * c = c * cd c * cd (cd c) by
      rw [hcc (cd c * cd (cd c)) c, mul_assoc]]
  obtain ⟨π, hπ0, hπinv⟩ := exists_pi F hx0 hZ ha haQ hx05 hx01 hd h0 hh0ne hfix
  have hψs := psiT_surjective hZ ha haQ hx0 hx05 hx01 F hyT hyQ2
  have hcent := psiT_ker_central hZ ha haQ hx0 hx05 hx01 F
  obtain ⟨B, hB⟩ := exists_bilin (psiT (Z := Z) F hx0) hψs hcent π
  set xθ := theta L1 L2 S ⟨x0, hx0P⟩ with hxθ
  set tθ := theta L1 L2 S ⟨a, haP⟩ with htθ
  set dθ := theta L1 L2 S ⟨d, hdP⟩ with hdθ
  have hvec : ∀ v : VV F hx0, ∃ τ : TT L1 L2 S Z x0,
      Multiplicative.toAdd (psiT (Z := Z) F hx0 τ) = v := by
    intro v
    obtain ⟨τ, hτ⟩ := hψs (Multiplicative.ofAdd v)
    exact ⟨τ, by rw [hτ]; rfl⟩
  have hpsi : ∀ τ : TT L1 L2 S Z x0, Multiplicative.toAdd (psiT (Z := Z) F hx0 τ) =
      Submodule.Quotient.mk (mu (⟨τ, Tsub_le_Q1 τ.2⟩ : ↥(Q1 L1 L2 S))) := fun τ => rfl
  have hxB : ∀ v w, B (O2Alg.xq xθ tθ hx5 htt htx v) (O2Alg.xq xθ tθ hx5 htt htx w) = B v w := by
    intro v w
    obtain ⟨τ, rfl⟩ := hvec v
    obtain ⟨σ, rfl⟩ := hvec w
    have hxq : ∀ τ : TT L1 L2 S Z x0, O2Alg.xq xθ tθ hx5 htt htx
        (Multiplicative.toAdd (psiT (Z := Z) F hx0 τ)) =
        Multiplicative.toAdd (psiT (Z := Z) F hx0 ⟨x0 * τ * x0⁻¹, x0_conj_Tsub F hx0 τ.2⟩) := by
      intro τ
      rw [hpsi, hpsi, O2Alg.xq_mk]
      exact congrArg Submodule.Quotient.mk (theta_apply ⟨x0, hx0P⟩ _)
    rw [hxq τ, hxq σ, hB, hB]
    congr 2
    apply Subtype.ext
    apply Subtype.ext
    show ⁅x0 * (τ : G) * x0⁻¹, x0 * (σ : G) * x0⁻¹⁆ = ⁅(τ : G), (σ : G)⁆
    have h1 : ⁅x0 * (τ : G) * x0⁻¹, x0 * (σ : G) * x0⁻¹⁆ =
        x0 * ⁅(τ : G), (σ : G)⁆ * x0⁻¹ := by
      simp only [commutatorElement_def]; group
    rw [h1]
    exact x0_centralizes_CC F hx0 hZ ha haQ hx05 hx01 (cmT τ σ)
  have hdB' : ∀ v w, B (O2Alg.dq xθ tθ hx5 htt htx dθ hd3 hdx v)
      (O2Alg.dq xθ tθ hx5 htt htx dθ hd3 hdx w) = B v w := by
    intro v w
    obtain ⟨τ, rfl⟩ := hvec v
    obtain ⟨σ, rfl⟩ := hvec w
    have hdq : ∀ τ : TT L1 L2 S Z x0, O2Alg.dq xθ tθ hx5 htt htx dθ hd3 hdx
        (Multiplicative.toAdd (psiT (Z := Z) F hx0 τ)) =
        Multiplicative.toAdd (psiT (Z := Z) F hx0 ⟨d * τ * d⁻¹, d_conj_Tsub F hx0 hZ hd τ.2⟩) := by
      intro τ
      rw [hpsi, hpsi, O2Alg.dq_mk]
      exact congrArg Submodule.Quotient.mk (theta_apply ⟨d, hdP⟩ _)
    rw [hdq τ, hdq σ, hB, hB]
    have hcm : cmT (⟨d * (τ : G) * d⁻¹, d_conj_Tsub F hx0 hZ hd τ.2⟩ : TT L1 L2 S Z x0)
        ⟨d * (σ : G) * d⁻¹, d_conj_Tsub F hx0 hZ hd σ.2⟩ = cd (cmT τ σ) := by
      apply Subtype.ext
      apply Subtype.ext
      show ⁅d * (τ : G) * d⁻¹, d * (σ : G) * d⁻¹⁆ = d * ⁅(τ : G), (σ : G)⁆ * d⁻¹
      simp only [commutatorElement_def]; group
    rw [hcm, hπinv]
  have hπc : π c ≠ 1 := by
    intro h1
    apply hπ0
    have h2 : π (cd c) = π c := hπinv c
    have h3 : π (cd (cd c)) = π c := by rw [hπinv, hπinv]
    rw [hh0, map_mul, map_mul, h2, h3, h1]
    simp
  have hBne : ∃ v w, B v w ≠ 0 := by
    refine ⟨Multiplicative.toAdd (psiT (Z := Z) F hx0 ⟨y, hyT⟩),
      Multiplicative.toAdd (psiT (Z := Z) F hx0 ⟨q * a * q⁻¹ * a⁻¹, hwT⟩), ?_⟩
    rw [hB]
    intro h
    apply hπc
    exact Multiplicative.toAdd.injective h
  exact O2Alg.no_form xθ tθ hx5 htt htx dθ hd3 hdx hrk hne hdnt B hxB hdB' hBne

end CFSG.Quasithin.Kleidman.F204
