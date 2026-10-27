module

public import CFSG.LocalAnalysis.StandardType.GGQTwoThmB
public import Mathlib.LinearAlgebra.SesquilinearForm.Basic
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.LinearAlgebra.Matrix.DotProduct

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly Module QTwoLin

private def ggQ2x_fixSet {K V : Type*} [CommRing K] [AddCommGroup V] [Module K V]
    (S : Set V) : Subgroup (V ≃ₗ[K] V) where
  carrier := {g | ∀ v ∈ S, g v = v}
  mul_mem' := by
    intro a b ha hb v hv
    rw [LinearEquiv.mul_apply]
    have hbv : b v ∈ S := by rw [hb v hv]; exact hv
    rw [ha (b v) hbv, hb v hv]
  one_mem' := by intro v _; rfl
  inv_mem' := by
    intro a ha v hv
    have h : a (a⁻¹ v) = a v := by
      show a (a.symm v) = a v
      rw [LinearEquiv.apply_symm_apply, ha v hv]
    exact LinearEquiv.injective a h

private lemma ggQ2xDg_conj_reflection {K V : Type*} [CommRing K] [AddCommGroup V] [Module K V]
    (a : V ≃ₗ[K] V) {ψ : Dual K V} {cc : V} (h : ψ cc = 2) :
    a * Module.reflection h * a.symm =
      Module.reflection (show (ψ.comp (a.symm : V →ₗ[K] V)) (a cc) = 2 by
        simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
        exact h) := by
  ext w
  rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply,
    Module.reflection_apply (a.symm w) h, Module.reflection_apply w]
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
  rw [map_sub, map_smul, LinearEquiv.apply_symm_apply]

private lemma ggQ2xDg_isReflLin_conj {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    (a t : V ≃ₗ[ZMod 3] V) (ht : IsReflLin t) : IsReflLin (a * t * a⁻¹) := by
  obtain ⟨cc, ψ, hψ, rfl⟩ := ht
  refine ⟨a cc, ψ.comp (a.symm : V →ₗ[ZMod 3] V), ?_, ?_⟩
  · simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
    exact hψ
  · rw [show a⁻¹ = a.symm from rfl]
    exact ggQ2xDg_conj_reflection a hψ

private lemma ggQ2xDg_rootPair_self (D : GGQ2Lin 3) (γ : ↥D.rootPairs) :
    γ.1.1 γ.1.2 = 2 := by
  obtain ⟨k, w, _, hq2, hq1⟩ := γ.2
  rw [hq2, hq1]
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
  rw [LinearEquiv.symm_apply_apply, D.root_coroot_self]

private lemma ggQ2xDg_simplePair_mem (D : GGQ2Lin 3) (k : D.ι) :
    (D.root k, D.coroot k) ∈ D.rootPairs :=
  ⟨k, 1, D.weyl.one_mem, rfl, by
    change D.root k = (D.root k).comp (LinearMap.id : D.V →ₗ[ZMod 3] D.V)
    rw [LinearMap.comp_id]⟩

private lemma ggQ2xDg_simpleRefl_mem_weyl (D : GGQ2Lin 3) (k : D.ι) :
    D.simpleRefl k ∈ D.weyl :=
  Subgroup.subset_closure ⟨k, trivial, rfl⟩

private lemma ggQ2xDg_rootRefl_mem_weyl (D : GGQ2Lin 3) (γ : ↥D.rootPairs) :
    Module.reflection (ggQ2xDg_rootPair_self D γ) ∈ D.weyl := by
  obtain ⟨k, w, hw, hq2, hq1⟩ := γ.2
  have heq : Module.reflection (ggQ2xDg_rootPair_self D γ) = w * D.simpleRefl k * w.symm := by
    ext v
    rw [Module.reflection_apply v (ggQ2xDg_rootPair_self D γ),
      LinearEquiv.mul_apply, LinearEquiv.mul_apply]
    rw [show D.simpleRefl k = Module.reflection (D.root_coroot_self k) from rfl,
      Module.reflection_apply (w.symm v) (D.root_coroot_self k)]
    rw [map_sub, map_smul, LinearEquiv.apply_symm_apply]
    rw [hq1, hq2]
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
  rw [heq]
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hw (ggQ2xDg_simpleRefl_mem_weyl D k))
    (Subgroup.inv_mem _ hw)

theorem ggQ2_degenerate_lin {p : ℕ} [Fact p.Prime] (hp : p = 3) (D : GGQ2Lin p) (hbas : D.Basis)
    (hdeg : (D.cartan.det : ZMod p) = 0) (h4 : 4 ≤ Fintype.card D.ι) (x : D.V)
    (hx : ∀ v, (∀ g ∈ D.parab {k | k ≠ D.a}, g v = v) ↔ v ∈ Submodule.span (ZMod p) {x})
    (A : Subgroup (D.V ≃ₗ[ZMod p] D.V)) (hW : D.weyl ≤ A) (hTF : TransvectionFree A) :
    ∀ φ ∈ A, φ x ∈ Submodule.span (ZMod p) {x} := by
  subst hp
  obtain ⟨β, d, hβsymm, hd, hβh⟩ := ggQ2_exists_invariantForm (p := 3) rfl D hbas h4
  have hβsymm' : LinearMap.IsSymm β := ⟨fun u w => hβsymm.eq u w⟩
  let Rad : Submodule (ZMod 3) D.V := ⨅ u, LinearMap.ker (β u)
  have hmemRad : ∀ v, v ∈ Rad ↔ ∀ u, β u v = 0 := by
    intro v
    simp only [Rad, Submodule.mem_iInf, LinearMap.mem_ker]
  haveI : Nonempty D.ι := Fintype.card_pos_iff.mp (by omega)
  have hspan : Submodule.span (ZMod 3) (Set.range D.coroot) = ⊤ :=
    hbas.1.span_eq_top_of_card_eq_finrank hbas.2
  let sp : D.ι → ↥D.rootPairs := fun k => ⟨(D.root k, D.coroot k), ggQ2xDg_simplePair_mem D k⟩
  have hsp1 : ∀ k, (sp k).1.1 = D.root k := fun _ => rfl
  have hsp2 : ∀ k, (sp k).1.2 = D.coroot k := fun _ => rfl
  have hdet : (D.cartan.map (Int.castRingHom (ZMod 3))).det = 0 := by
    change (D.cartan.map (fun x : ℤ => (x : ZMod 3))).det = 0
    rw [← Int.cast_det]
    exact hdeg
  obtain ⟨b, hbne, hbker⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  let v : D.V := ∑ j, b j • D.coroot j
  have hv_ne : v ≠ 0 := by
    intro hv0
    apply hbne
    have hli := hbas.1
    rw [Fintype.linearIndependent_iffₛ] at hli
    have hsum : (∑ j, b j • D.coroot j) = 0 := by simpa only [v] using hv0
    have h := hli b 0 (by simpa using hsum)
    ext i
    simpa using h i
  have hRad_of_coroot : ∀ w, (∀ i, β (D.coroot i) w = 0) → w ∈ Rad := by
    intro w hw
    rw [hmemRad]
    intro u
    have hL : β w = 0 := by
      apply LinearMap.ext_on_range hspan
      intro i
      rw [← hβsymm.eq (D.coroot i) w]
      exact hw i
    rw [hβsymm.eq u w, hL]
    rfl
  have hcoroot_rad : ∀ i, β (D.coroot i) v = 0 := by
    intro i
    have h1 : β (D.coroot i) v = d (sp i) * (D.root i) v := by
      simpa only [hsp1, hsp2] using hβh (sp i) v
    have hsum : (D.root i) v = ∑ j, b j * (D.cartan i j : ZMod 3) := by
      simp only [v, map_sum, map_smul, smul_eq_mul, D.pairing]
    have hbi := congrArg (fun w : D.ι → ZMod 3 => w i) hbker
    rw [Matrix.mulVec_apply_eq_sum, Pi.zero_apply] at hbi
    have hbi' : ∑ j, ((Int.castRingHom (ZMod 3)) (D.cartan i j)) * b j = 0 := by
      simpa only [Matrix.map_apply] using hbi
    have hroot : (D.root i) v = 0 := by
      rw [hsum]
      have hcomm : ∑ j, b j * (D.cartan i j : ZMod 3) =
          ∑ j, ((Int.castRingHom (ZMod 3)) (D.cartan i j)) * b j := by
        refine Finset.sum_congr rfl fun j _ => ?_
        exact mul_comm _ _
      rw [hcomm, hbi']
    rw [h1, hroot, mul_zero]
  have hv_rad : v ∈ Rad := hRad_of_coroot v hcoroot_rad
  have hRad_ne_bot : Rad ≠ ⊥ := by
    intro hbot
    have : v ∈ (⊥ : Submodule (ZMod 3) D.V) := hbot ▸ hv_rad
    rw [Submodule.mem_bot] at this
    exact hv_ne this
  have hRad_le : Rad ≤ Submodule.span (ZMod 3) ({x} : Set D.V) := by
    intro w hw
    refine (hx w).mp ?_
    intro g hg
    have hfix : ∀ k, k ≠ D.a → D.simpleRefl k w = w := by
      intro k _
      rw [show D.simpleRefl k = Module.reflection (D.root_coroot_self k) from rfl,
        Module.reflection_apply w (D.root_coroot_self k)]
      have hβk : β (D.coroot k) w = 0 := (hmemRad w).mp hw (D.coroot k)
      have h1 : β (D.coroot k) w = d (sp k) * (D.root k) w := by
        simpa only [hsp1, hsp2] using hβh (sp k) w
      have hroot : (D.root k) w = 0 := by
        have h2 : d (sp k) * (D.root k) w = 0 := by rw [← h1, hβk]
        exact (mul_eq_zero.mp h2).resolve_left (hd (sp k))
      rw [hroot, zero_smul, sub_zero]
    have hle : D.parab {k | k ≠ D.a} ≤ ggQ2x_fixSet ({w} : Set D.V) := by
      rw [GGQ2Lin.parab, Subgroup.closure_le]
      rintro g ⟨k, hk, rfl⟩
      intro z hz
      rw [Set.mem_singleton_iff] at hz
      rw [hz]
      exact hfix k hk
    exact hle hg w rfl
  have hx_mem : x ∈ Rad := by
    have hw : v ∈ Submodule.span (ZMod 3) ({x} : Set D.V) := hRad_le hv_rad
    obtain ⟨cc, hcc⟩ := Submodule.mem_span_singleton.mp hw
    have hcc_ne : cc ≠ 0 := by
      intro h0
      rw [h0, zero_smul] at hcc
      exact hv_ne hcc.symm
    have hx_eq : x = cc⁻¹ • v := by
      rw [← hcc, smul_smul, inv_mul_cancel₀ hcc_ne, one_smul]
    rw [hx_eq]
    exact Submodule.smul_mem _ _ hv_rad
  have hrefl_fix : ∀ t ∈ A, IsReflLin t → t ∈ ggQ2x_fixSet (Rad : Set D.V) := by
    intro t htA ht
    obtain ⟨c, φ, hφ, rfl⟩ := ht
    intro w hw
    by_cases hc : ∃ γ : ↥D.rootPairs, c ∈ Submodule.span (ZMod 3) ({γ.1.2} : Set D.V)
    ·
      obtain ⟨γ, hcγ⟩ := hc
      obtain ⟨k, hk⟩ := Submodule.mem_span_singleton.mp hcγ
      have hc0 : c ≠ 0 := by
        intro h0
        rw [h0, map_zero] at hφ
        exact two_ne_zero_of_charP_three (K := ZMod 3) hφ.symm
      have hk0 : k ≠ 0 := by
        intro h0
        exact hc0 (by rw [← hk, h0, zero_smul])
      have hα : γ.1.1 γ.1.2 = 2 := ggQ2xDg_rootPair_self D γ
      have hφ' : (k⁻¹ • γ.1.1) c = 2 := by
        rw [← hk, LinearMap.smul_apply, smul_eq_mul, map_smul, smul_eq_mul, hα,
          ← mul_assoc, inv_mul_cancel₀ hk0, one_mul]
      by_cases hphi : φ = k⁻¹ • γ.1.1
      ·
        subst hphi
        rw [Module.reflection_apply w hφ]
        have hγ : γ.1.1 w = 0 := by
          have hβγ : β (γ.1.2) w = 0 := (hmemRad w).mp hw (γ.1.2)
          have h1 : β (γ.1.2) w = d γ * γ.1.1 w := hβh γ w
          have h2 : d γ * γ.1.1 w = 0 := by rw [← h1, hβγ]
          exact (mul_eq_zero.mp h2).resolve_left (hd γ)
        rw [LinearMap.smul_apply, smul_eq_mul, hγ, mul_zero, zero_smul, sub_zero]
      ·
        exfalso
        have hφ'_mem : Module.reflection hφ' ∈ A := by
          have heq : Module.reflection hφ' = Module.reflection (ggQ2xDg_rootPair_self D γ) := by
            ext z
            rw [Module.reflection_apply z hφ',
              Module.reflection_apply z (ggQ2xDg_rootPair_self D γ)]
            rw [← hk, LinearMap.smul_apply, smul_eq_mul, smul_smul]
            have hs : (k⁻¹ * γ.1.1 z) * k = γ.1.1 z := by
              rw [mul_assoc, mul_comm (γ.1.1 z) k, ← mul_assoc, inv_mul_cancel₀ hk0, one_mul]
            rw [hs]
          rw [heq]
          exact hW (ggQ2xDg_rootRefl_mem_weyl D γ)
        have htv : IsTransvectionLin (Module.reflection hφ' * Module.reflection hφ) :=
          transvection_of_same_centre hφ hφ' hphi
        exact hTF _ (Subgroup.mul_mem _ hφ'_mem htA) htv
    ·
      push Not at hc
      have hspan' : Submodule.span (ZMod 3) (Set.range (fun γ : ↥D.rootPairs => γ.1.2)) = ⊤ := by
        rw [eq_top_iff, ← hspan]
        refine Submodule.span_mono ?_
        rintro z ⟨i, rfl⟩
        exact ⟨sp i, rfl⟩
      obtain ⟨ε, _, hεv⟩ :=
        refl_eq_orthogonal (V := D.V) (ι := ↥D.rootPairs)
          (fun γ : ↥D.rootPairs => γ.1.2) (fun γ : ↥D.rootPairs => γ.1.1)
          (fun γ => ggQ2xDg_rootPair_self D γ) β hβsymm' d hd hβh hspan'
          A hTF (fun γ => hW (ggQ2xDg_rootRefl_mem_weyl D γ))
          hφ htA hc (ggQ2_connectivity (p := 3) rfl D hbas h4 c)
      rw [Module.reflection_apply w hφ, hεv w, (hmemRad w).mp hw c, mul_zero, zero_smul,
        sub_zero]
  have hR_fix : reflGp A ≤ ggQ2x_fixSet (Rad : Set D.V) := by
    rw [reflGp, Subgroup.closure_le]
    rintro t ⟨htA, ht⟩
    exact hrefl_fix t htA ht
  have hW_le_R : D.weyl ≤ reflGp A := by
    change Subgroup.closure (D.simpleRefl '' Set.univ) ≤ reflGp A
    rw [Subgroup.closure_le]
    rintro t ⟨k, -, rfl⟩
    exact Subgroup.mem_closure_of_mem
      ⟨hW (ggQ2xDg_simpleRefl_mem_weyl D k), D.coroot k, D.root k, D.root_coroot_self k, rfl⟩
  have hparab_le_weyl : D.parab {k | k ≠ D.a} ≤ D.weyl := by
    change Subgroup.closure (D.simpleRefl '' {k | k ≠ D.a}) ≤
      Subgroup.closure (D.simpleRefl '' Set.univ)
    refine Subgroup.closure_mono ?_
    rintro t ⟨k, _, rfl⟩
    exact ⟨k, trivial, rfl⟩
  have hnormal : ∀ a ∈ A, ∀ r ∈ reflGp A, a * r * a.symm ∈ reflGp A := by
    intro a ha r hr
    have hmap : (MulAut.conj a) '' ({t : D.V ≃ₗ[ZMod 3] D.V | t ∈ A ∧ IsReflLin t} : Set _) ⊆
        ({t : D.V ≃ₗ[ZMod 3] D.V | t ∈ A ∧ IsReflLin t} : Set _) := by
      rintro _ ⟨t, ⟨htA, htR⟩, rfl⟩
      rw [MulAut.conj_apply]
      exact ⟨Subgroup.mul_mem _ (Subgroup.mul_mem _ ha htA) (Subgroup.inv_mem _ ha),
        ggQ2xDg_isReflLin_conj a t htR⟩
    have hle : Subgroup.map (MulAut.conj a) (reflGp A) ≤ reflGp A := by
      rw [reflGp, MonoidHom.map_closure]
      exact Subgroup.closure_mono hmap
    have hm : MulAut.conj a r ∈ Subgroup.map (MulAut.conj a) (reflGp A) := ⟨r, hr, rfl⟩
    have h := hle hm
    rw [MulAut.conj_apply] at h
    exact h
  intro φ hφA
  have hfixR : ∀ r ∈ reflGp A, r (φ x) = φ x := by
    intro r hr
    have hconj : φ.symm * r * φ ∈ reflGp A := by
      simpa only [LinearEquiv.symm_symm] using hnormal φ.symm (Subgroup.inv_mem _ hφA) r hr
    have hxfix : (φ.symm * r * φ) x = x := hR_fix hconj x hx_mem
    calc r (φ x) = φ ((φ.symm * r * φ) x) := by
          rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, LinearEquiv.apply_symm_apply]
      _ = φ x := by rw [hxfix]
  exact (hx (φ x)).mp fun g hg => hfixR g (hW_le_R (hparab_le_weyl hg))

end CFSG.StandardType

end
