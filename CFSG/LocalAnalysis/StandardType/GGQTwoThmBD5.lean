module

public import CFSG.LocalAnalysis.StandardType.GGQTwoDWeyl
public import CFSG.LocalAnalysis.StandardType.GGQTwoDCoord
public import CFSG.LocalAnalysis.StandardType.GGQTwoS1Transport
public import CFSG.LocalAnalysis.StandardType.GGQTwoQuandleE
public import CFSG.LocalAnalysis.StandardType.GGQTwoBCZ1
public import CFSG.LocalAnalysis.StandardType.GGQTwoInnerDefs

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly Module QTwoLin

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private theorem ggQ2xD5_cartan_symm (D : GGQ2Lin 3) (e : Fin 5 ≃ D.ι)
    (hD : D.coxeter = (ggCoxeterMatrixD 5).reindex e) :
    ∀ i j, D.cartan i j = D.cartan j i :=
  ggQ2xQ_cartan_symm_of_reindex (ggCoxeterMatrixD 5)
    (by intro a b; rw [ggCoxeterMatrixD_apply]; split_ifs <;> omega) D e hD

private def ggQ2xD5_dotForm : LinearMap.BilinForm (ZMod 3) (GGBCV 5) :=
  LinearMap.mk₂ (ZMod 3) (fun u v => ∑ i, u i * v i)
    (by intro u₁ u₂ v
        simp only [Pi.add_apply]
        rw [← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl (fun i _ => by rw [add_mul]))
    (by intro a u v
        simp only [Pi.smul_apply, smul_eq_mul]
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun i _ => by rw [mul_assoc]))
    (by intro u v₁ v₂
        simp only [Pi.add_apply]
        rw [← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl (fun i _ => by rw [mul_add]))
    (by intro a u v
        simp only [Pi.smul_apply, smul_eq_mul]
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun i _ => by rw [mul_left_comm]))

private lemma ggQ2xD5_dotForm_apply (u v : GGBCV 5) :
    ggQ2xD5_dotForm u v = ∑ i, u i * v i := by
  rw [ggQ2xD5_dotForm, LinearMap.mk₂_apply]

private theorem ggQ2xD5_S1 (D : GGQ2Lin 3) (hbas : D.Basis) (e : Fin 5 ≃ D.ι)
    (hD : D.coxeter = (ggCoxeterMatrixD 5).reindex e)
    (A : Subgroup (D.V ≃ₗ[ZMod 3] D.V)) (hW : D.weyl ≤ A) (hTF : TransvectionFree A)
    (τ : D.V ≃ₗ[ZMod 3] GGBCV 5)
    (hcor : ∀ i, τ (D.coroot (e i)) = ggDSimple 3 5 i)
    (hroot : ∀ i v, D.root (e i) v = ∑ j, ggDSimple 3 5 i j * τ v j) :
    ∀ (c : GGBCV 5) (φ : Module.Dual (ZMod 3) (GGBCV 5)) (h : φ c = 2),
      Module.reflection h ∈ A.map (ggLinConj τ).toMonoidHom →
      ∃ ε : ZMod 3, (ε = 1 ∨ ε = -1) ∧ ∀ v, φ v = ε * (c ⬝ᵥ v) := by
  intro c φ h ht
  have h4 : 4 ≤ Fintype.card D.ι := by
    rw [← Fintype.card_congr e, Fintype.card_fin]; omega
  have hsym : ∀ i j, D.cartan i j = D.cartan j i := ggQ2xD5_cartan_symm D e hD
  have hB' : ∀ i j : D.ι,
      ggQ2xD5_dotForm (τ (D.coroot i)) (τ (D.coroot j)) = (D.cartan i j : ZMod 3) := by
    intro i j
    obtain ⟨a, rfl⟩ := e.surjective i
    obtain ⟨b, rfl⟩ := e.surjective j
    rw [ggQ2xD5_dotForm_apply, hcor a, hcor b]
    have h1 := hroot a (D.coroot (e b))
    rw [D.pairing] at h1
    rw [hcor b] at h1
    exact h1.symm
  obtain ⟨ε, hε, hφ⟩ :=
    ggQ2_S1_transport D hbas h4 hsym τ ggQ2xD5_dotForm hB' A hW hTF h ht
  refine ⟨ε, hε, fun v => ?_⟩
  have hdot : ggQ2xD5_dotForm c v = c ⬝ᵥ v := by
    rw [ggQ2xD5_dotForm_apply]
    rfl
  exact (hφ v).trans (congrArg (fun x => ε * x) hdot)

private theorem ggQ2xD5a_simpleRefl_apply (D : GGQ2Lin 3) (k : D.ι) (v : D.V) :
    D.simpleRefl k v = v - D.root k v • D.coroot k := by
  rw [show D.simpleRefl k = Module.reflection (D.root_coroot_self k) from rfl]
  exact Module.reflection_apply v (D.root_coroot_self k)

private lemma ggQ2xD5a_coroot_ne_zero (D : GGQ2Lin 3) (k : D.ι) : D.coroot k ≠ 0 := by
  intro h
  have h2 : D.root k (D.coroot k) = 2 := D.root_coroot_self k
  rw [h, map_zero] at h2
  exact (by decide : (2 : ZMod 3) ≠ 0) h2.symm

private lemma ggQ2xD5a_fixed_iff (D : GGQ2Lin 3) (k : D.ι) (w : D.V) :
    D.simpleRefl k w = w ↔ D.root k w = 0 := by
  rw [ggQ2xD5a_simpleRefl_apply]
  constructor
  · intro h
    rcases smul_eq_zero.mp (sub_eq_self.mp h) with h0 | h0
    · exact h0
    · exact absurd h0 (ggQ2xD5a_coroot_ne_zero D k)
  · intro h
    rw [h, zero_smul, sub_zero]

private lemma ggQ2xD5a_parab_fixed_iff (D : GGQ2Lin 3) (e : Fin 5 ≃ D.ι)
    (ha : D.a = e 0) (w : D.V) :
    (∀ g ∈ D.parab {k | k ≠ D.a}, g w = w) ↔
      (∀ i : Fin 5, i ≠ 0 → D.root (e i) w = 0) := by
  constructor
  · intro hw i hi
    have hmem : D.simpleRefl (e i) ∈ D.parab {k | k ≠ D.a} := by
      rw [GGQ2Lin.parab]
      refine Subgroup.subset_closure ⟨e i, ?_, rfl⟩
      intro h
      exact hi (e.injective (h.trans ha))
    exact (ggQ2xD5a_fixed_iff D (e i) w).mp (hw (D.simpleRefl (e i)) hmem)
  · intro hw g hg
    have hg' : g ∈ Subgroup.closure (D.simpleRefl '' {k | k ≠ D.a}) := by
      simpa only [GGQ2Lin.parab] using hg
    refine Subgroup.closure_induction (p := fun x _ => x w = w) ?_ ?_ ?_ ?_ hg'
    · rintro x ⟨k, hk, rfl⟩
      obtain ⟨i, rfl⟩ := e.surjective k
      have hi : i ≠ 0 := by
        intro h0
        exact hk (by rw [ha, h0])
      exact (ggQ2xD5a_fixed_iff D (e i) w).mpr (hw i hi)
    · rfl
    · intro x y _ _ hx' hy'
      rw [LinearEquiv.mul_apply, hy', hx']
    · intro x _ hx'
      apply x.injective
      rw [hx']
      exact x.apply_symm_apply w

private lemma ggQ2xD5a_sum_single (i : Fin 5) :
    (∑ j, ggDSimple 3 5 i j * (Pi.single (0 : Fin 5) (1 : ZMod 3) : GGBCV 5) j) =
      ggDSimple 3 5 i (0 : Fin 5) := by
  rw [Finset.sum_eq_single (0 : Fin 5)]
  · simp
  · intro b _ hb
    rw [Pi.single_eq_of_ne (M := fun _ => ZMod 3) hb, mul_zero]
  · intro h
    exact absurd (Finset.mem_univ _) h

private lemma ggQ2xD5a_dsimple_zero (i : Fin 5) (hi : i ≠ 0) :
    ggDSimple 3 5 i (0 : Fin 5) = 0 := by
  rcases lt_or_ge ((i : ℕ) + 1) 5 with hlt | hge
  · have h1 : ¬ ((0 : Fin 5) : ℕ) = (i : ℕ) := by
      intro h
      exact hi (Fin.ext h.symm)
    have h2 : ¬ ((0 : Fin 5) : ℕ) = (i : ℕ) + 1 := by
      intro h
      omega
    rw [ggQ2_DW_eval_chain 3 5 i hlt (0 : Fin 5), if_neg h1, if_neg h2, add_zero]
  · rw [ggQ2_DW_eval_fork 3 5 i (Nat.not_lt.mpr hge) (0 : Fin 5)]
    simp

private theorem ggQ2xD5_tau_x (D : GGQ2Lin 3) (e : Fin 5 ≃ D.ι)
    (hD : D.coxeter = (ggCoxeterMatrixD 5).reindex e) (ha : D.a = e 0) (x : D.V)
    (hx : ∀ v, (∀ g ∈ D.parab {k | k ≠ D.a}, g v = v) ↔ v ∈ Submodule.span (ZMod 3) {x})
    (τ : D.V ≃ₗ[ZMod 3] GGBCV 5)
    (hcor : ∀ i, τ (D.coroot (e i)) = ggDSimple 3 5 i)
    (hroot : ∀ i v, D.root (e i) v = ∑ j, ggDSimple 3 5 i j * τ v j) :
    Submodule.span (ZMod 3) {τ x} = Submodule.span (ZMod 3) {(Pi.single 0 1 : GGBCV 5)} := by
  have hxroot : ∀ i : Fin 5, i ≠ 0 → D.root (e i) x = 0 :=
    (ggQ2xD5a_parab_fixed_iff D e ha x).mp
      ((hx x).mpr (Submodule.mem_span_singleton_self x))
  have heq1 : (τ x) (⟨1, by decide⟩ : Fin 5) = (τ x) (⟨2, by decide⟩ : Fin 5) := by
    have h := hxroot (⟨1, by decide⟩ : Fin 5) (by decide)
    rw [hroot (⟨1, by decide⟩ : Fin 5) x,
      ggQ2_DW_sum_ggDSimple 3 5 (⟨1, by decide⟩ : Fin 5) (by decide) (τ x)] at h
    exact sub_eq_zero.mp h
  have heq2 : (τ x) (⟨2, by decide⟩ : Fin 5) = (τ x) (⟨3, by decide⟩ : Fin 5) := by
    have h := hxroot (⟨2, by decide⟩ : Fin 5) (by decide)
    rw [hroot (⟨2, by decide⟩ : Fin 5) x,
      ggQ2_DW_sum_ggDSimple 3 5 (⟨2, by decide⟩ : Fin 5) (by decide) (τ x)] at h
    exact sub_eq_zero.mp h
  have heq3 : (τ x) (⟨3, by decide⟩ : Fin 5) = (τ x) (⟨4, by decide⟩ : Fin 5) := by
    have h := hxroot (⟨3, by decide⟩ : Fin 5) (by decide)
    rw [hroot (⟨3, by decide⟩ : Fin 5) x,
      ggQ2_DW_sum_ggDSimple 3 5 (⟨3, by decide⟩ : Fin 5) (by decide) (τ x)] at h
    exact sub_eq_zero.mp h
  have heq4 : (τ x) (⟨3, by decide⟩ : Fin 5) = -(τ x) (⟨4, by decide⟩ : Fin 5) := by
    have h := hxroot (⟨4, by decide⟩ : Fin 5) (by decide)
    rw [hroot (⟨4, by decide⟩ : Fin 5) x,
      ggQ2_DW_sum_ggDSimple_fork 3 5 (by omega) (⟨4, by decide⟩ : Fin 5) (by decide)
        (τ x)] at h
    exact eq_neg_of_add_eq_zero_left h
  have h4z : (τ x) (⟨4, by decide⟩ : Fin 5) = 0 := by
    have h : (τ x) (⟨4, by decide⟩ : Fin 5) = -(τ x) (⟨4, by decide⟩ : Fin 5) :=
      heq3.symm.trans heq4
    have hsum : (τ x) (⟨4, by decide⟩ : Fin 5) + (τ x) (⟨4, by decide⟩ : Fin 5) = 0 := by
      nth_rewrite 2 [h]; exact add_neg_cancel _
    have h2 : (2 : ZMod 3) * (τ x) (⟨4, by decide⟩ : Fin 5) = 0 := by
      rw [two_mul]; exact hsum
    exact (mul_eq_zero.mp h2).resolve_left (by decide)
  have h3z : (τ x) (⟨3, by decide⟩ : Fin 5) = 0 := heq3.trans h4z
  have h2z : (τ x) (⟨2, by decide⟩ : Fin 5) = 0 := heq2.trans h3z
  have h1z : (τ x) (⟨1, by decide⟩ : Fin 5) = 0 := heq1.trans h2z
  have hux : τ x ∈ Submodule.span (ZMod 3) {(Pi.single 0 1 : GGBCV 5)} := by
    rw [Submodule.mem_span_singleton]
    refine ⟨(τ x) (0 : Fin 5), ?_⟩
    funext j
    fin_cases j
    · simp
    · rw [h1z]; simp
    · rw [h2z]; simp
    · rw [h3z]; simp
    · rw [h4z]; simp
  have hfixf0 : ∀ g ∈ D.parab {k | k ≠ D.a},
      g (τ.symm (Pi.single 0 1 : GGBCV 5)) = τ.symm (Pi.single 0 1 : GGBCV 5) :=
    (ggQ2xD5a_parab_fixed_iff D e ha (τ.symm (Pi.single 0 1 : GGBCV 5))).mpr (by
      intro i hi
      rw [hroot i (τ.symm (Pi.single 0 1 : GGBCV 5)), LinearEquiv.apply_symm_apply,
        ggQ2xD5a_sum_single i, ggQ2xD5a_dsimple_zero i hi])
  have hf0 : (Pi.single 0 1 : GGBCV 5) ∈ Submodule.span (ZMod 3) {τ x} := by
    have hpre : τ.symm (Pi.single 0 1 : GGBCV 5) ∈ Submodule.span (ZMod 3) {x} :=
      (hx _).mp hfixf0
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hpre
    rw [Submodule.mem_span_singleton]
    refine ⟨c, ?_⟩
    have h := congrArg τ hc
    rw [map_smul, LinearEquiv.apply_symm_apply] at h
    exact h
  refine le_antisymm ?_ ?_
  · rw [Submodule.span_le, Set.singleton_subset_iff]
    exact hux
  · rw [Submodule.span_le, Set.singleton_subset_iff]
    exact hf0

private def ggQ2xD5_Z (A : Subgroup (GGBCV 5 ≃ₗ[ZMod 3] GGBCV 5)) : Set (GGBCV 5) :=
  {z | ∃ hz : z ⬝ᵥ z ≠ 0, ggBCRefl z hz ∈ A}

private theorem ggQ2xD5_Z0 (A : Subgroup (GGBCV 5 ≃ₗ[ZMod 3] GGBCV 5)) :
    ∀ z ∈ ggQ2xD5_Z A, z ⬝ᵥ z ≠ 0 := by
  rintro z ⟨hz, -⟩
  exact hz

private theorem ggQ2xD5_Zroots (A : Subgroup (GGBCV 5 ≃ₗ[ZMod 3] GGBCV 5))
    (hW : ggBCReflGp (ggDRoots 5) ≤ A) : ggDRoots 5 ⊆ ggQ2xD5_Z A := by
  intro z hz
  have hz0 : z ⬝ᵥ z ≠ 0 := by
    rw [ggQ2x_dot_self_eq_wt, hz]
    decide
  exact ⟨hz0, hW (Subgroup.subset_closure ⟨z, hz, hz0, rfl⟩)⟩

private lemma ggQ2xD5b_conj_reflection {K V : Type*} [CommRing K] [AddCommGroup V] [Module K V]
    (a : V ≃ₗ[K] V) {ψ : Module.Dual K V} {cc : V} (h : ψ cc = 2) :
    a * Module.reflection h * a.symm =
      Module.reflection (show (ψ.comp (a.symm : V →ₗ[K] V)) (a cc) = 2 by
        simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
        exact h) := by
  ext w
  rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply,
    Module.reflection_apply (a.symm w) h, Module.reflection_apply w]
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
  rw [map_sub, map_smul, LinearEquiv.apply_symm_apply]

private lemma ggQ2xD5b_refl_eq_bc {n : ℕ} {c : GGBCV n}
    {φ : Module.Dual (ZMod 3) (GGBCV n)} (hφ : φ c = 2) (ε : ZMod 3)
    (hφv : ∀ v, φ v = ε * (c ⬝ᵥ v)) :
    ∃ hc : c ⬝ᵥ c ≠ 0, Module.reflection hφ = ggBCRefl c hc := by
  have hc : c ⬝ᵥ c ≠ 0 := by
    intro h0
    have h := hφv c
    rw [hφ, h0, mul_zero] at h
    exact two_ne_zero_of_charP_three h
  refine ⟨hc, ?_⟩
  have he : ε = 2 / (c ⬝ᵥ c) := by
    have h : ε * (c ⬝ᵥ c) = 2 := by rw [← hφv c, hφ]
    field_simp
    exact h
  let ψ : Module.Dual (ZMod 3) (GGBCV n) := (2 / (c ⬝ᵥ c)) • ggBCDot c
  have hf : φ = ψ := by
    apply LinearMap.ext
    intro v
    rw [hφv v, LinearMap.smul_apply, ggQ2x_ggBCDot_apply, he, smul_eq_mul]
  subst φ
  rfl

private theorem ggQ2xD5_perm (A : Subgroup (GGBCV 5 ≃ₗ[ZMod 3] GGBCV 5))
    (hS1 : ∀ (c : GGBCV 5) (φ : Module.Dual (ZMod 3) (GGBCV 5)) (h : φ c = 2),
      Module.reflection h ∈ A → ∃ ε : ZMod 3, (ε = 1 ∨ ε = -1) ∧ ∀ v, φ v = ε * (c ⬝ᵥ v))
    (a : GGBCV 5 ≃ₗ[ZMod 3] GGBCV 5) (ha : a ∈ A) (z : GGBCV 5) (hz : z ∈ ggQ2xD5_Z A) :
    a z ∈ ggQ2xD5_Z A := by
  obtain ⟨hz0, hzA⟩ := hz
  let ψ : Module.Dual (ZMod 3) (GGBCV 5) := (2 / (z ⬝ᵥ z)) • ggBCDot z
  have hψ : ψ z = 2 := by
    change (2 / (z ⬝ᵥ z)) * (ggBCDot z z) = 2
    rw [ggQ2x_ggBCDot_apply]
    field_simp
  have hψeq : Module.reflection hψ = ggBCRefl z hz0 := rfl
  have hreflA : Module.reflection hψ ∈ A := hψeq ▸ hzA
  let φ : Module.Dual (ZMod 3) (GGBCV 5) := ψ.comp (a.symm : GGBCV 5 →ₗ[ZMod 3] GGBCV 5)
  have hφ : φ (a z) = 2 := by
    change ψ (a.symm (a z)) = 2
    rw [LinearEquiv.symm_apply_apply]
    exact hψ
  have hconj : a * Module.reflection hψ * a.symm = Module.reflection hφ :=
    ggQ2xD5b_conj_reflection a hψ
  have htA : a * Module.reflection hψ * a.symm ∈ A :=
    A.mul_mem (A.mul_mem ha hreflA) (A.inv_mem ha)
  have hreflA' : Module.reflection hφ ∈ A := by
    rw [← hconj]
    exact htA
  obtain ⟨ε, -, hφv⟩ := hS1 (a z) φ hφ hreflA'
  obtain ⟨hc, heq⟩ := ggQ2xD5b_refl_eq_bc hφ ε hφv
  refine ⟨hc, ?_⟩
  rw [← heq]
  exact hreflA'

private lemma ggQ2xD5b_scalar_of_refl
    (A : Subgroup (GGBCV 5 ≃ₗ[ZMod 3] GGBCV 5))
    (hS1 : ∀ (c : GGBCV 5) (φ : Module.Dual (ZMod 3) (GGBCV 5)) (h : φ c = 2),
      Module.reflection h ∈ A → ∃ ε : ZMod 3, (ε = 1 ∨ ε = -1) ∧ ∀ v, φ v = ε * (c ⬝ᵥ v))
    (a : GGBCV 5 ≃ₗ[ZMod 3] GGBCV 5) (ha : a ∈ A)
    (c : GGBCV 5) (hc : c ⬝ᵥ c ≠ 0) (hcA : ggBCRefl c hc ∈ A) :
    ∃ κ : ZMod 3, ∀ w, (a c) ⬝ᵥ (a w) = κ * (c ⬝ᵥ w) := by
  let ψ : Module.Dual (ZMod 3) (GGBCV 5) := (2 / (c ⬝ᵥ c)) • ggBCDot c
  have hψ : ψ c = 2 := by
    change (2 / (c ⬝ᵥ c)) * (ggBCDot c c) = 2
    rw [ggQ2x_ggBCDot_apply]
    field_simp
  have hψeq : Module.reflection hψ = ggBCRefl c hc := rfl
  have hreflA : Module.reflection hψ ∈ A := hψeq ▸ hcA
  let φ : Module.Dual (ZMod 3) (GGBCV 5) := ψ.comp (a.symm : GGBCV 5 →ₗ[ZMod 3] GGBCV 5)
  have hφ : φ (a c) = 2 := by
    change ψ (a.symm (a c)) = 2
    rw [LinearEquiv.symm_apply_apply]
    exact hψ
  have hconj : a * Module.reflection hψ * a.symm = Module.reflection hφ :=
    ggQ2xD5b_conj_reflection a hψ
  have htA : a * Module.reflection hψ * a.symm ∈ A :=
    A.mul_mem (A.mul_mem ha hreflA) (A.inv_mem ha)
  have hreflA' : Module.reflection hφ ∈ A := by
    rw [← hconj]
    exact htA
  obtain ⟨ε, hε, hφv⟩ := hS1 (a c) φ hφ hreflA'
  refine ⟨ε * (2 / (c ⬝ᵥ c)), fun w => ?_⟩
  have h1 : ε * ((a c) ⬝ᵥ (a w)) = φ (a w) := by
    rw [hφv (a w)]
  have h2 : φ (a w) = (2 / (c ⬝ᵥ c)) * (c ⬝ᵥ w) := by
    change ψ (a.symm (a w)) = _
    rw [LinearEquiv.symm_apply_apply]
    change (2 / (c ⬝ᵥ c)) * (ggBCDot c w) = _
    rw [ggQ2x_ggBCDot_apply]
  have hX : ε * ((a c) ⬝ᵥ (a w)) = (2 / (c ⬝ᵥ c)) * (c ⬝ᵥ w) := h1.trans h2
  have hε2 : ε * ε = 1 := by rcases hε with h | h <;> rw [h] <;> decide
  calc (a c) ⬝ᵥ (a w) = (ε * ε) * ((a c) ⬝ᵥ (a w)) := by rw [hε2, one_mul]
    _ = ε * (ε * ((a c) ⬝ᵥ (a w))) := by ring
    _ = ε * ((2 / (c ⬝ᵥ c)) * (c ⬝ᵥ w)) := by rw [hX]
    _ = (ε * (2 / (c ⬝ᵥ c))) * (c ⬝ᵥ w) := by ring

private lemma ggQ2xD5b_root_scalar
    (A : Subgroup (GGBCV 5 ≃ₗ[ZMod 3] GGBCV 5))
    (hW : ggBCReflGp (ggDRoots 5) ≤ A)
    (hS1 : ∀ (c : GGBCV 5) (φ : Module.Dual (ZMod 3) (GGBCV 5)) (h : φ c = 2),
      Module.reflection h ∈ A → ∃ ε : ZMod 3, (ε = 1 ∨ ε = -1) ∧ ∀ v, φ v = ε * (c ⬝ᵥ v))
    (a : GGBCV 5 ≃ₗ[ZMod 3] GGBCV 5) (ha : a ∈ A) {c : GGBCV 5}
    (hc : c ∈ ggDRoots 5) :
    ∃ κ : ZMod 3, ∀ w, (a c) ⬝ᵥ (a w) = κ * (c ⬝ᵥ w) := by
  have hc0 : c ⬝ᵥ c ≠ 0 := by
    rw [ggQ2x_dot_self_eq_wt, hc]
    decide
  exact ggQ2xD5b_scalar_of_refl A hS1 a ha c hc0
    (hW (Subgroup.subset_closure ⟨c, hc, hc0, rfl⟩))

private lemma ggQ2xD5b_scalar_const {a : GGBCV 5 ≃ₗ[ZMod 3] GGBCV 5} {c c' : GGBCV 5}
    (hcc' : c ⬝ᵥ c' ≠ 0) {κ κ' : ZMod 3}
    (hκ : ∀ w, (a c) ⬝ᵥ (a w) = κ * (c ⬝ᵥ w))
    (hκ' : ∀ w, (a c') ⬝ᵥ (a w) = κ' * (c' ⬝ᵥ w)) : κ = κ' := by
  have h : κ * (c ⬝ᵥ c') = κ' * (c ⬝ᵥ c') := by
    rw [← hκ c', dotProduct_comm (a c) (a c'), hκ' c, dotProduct_comm c' c]
  exact mul_right_cancel₀ hcc' h

private lemma ggQ2xD5b_connectivity :
    ∀ c c' : GGBCV 5, ggBCWt c = 2 → ggBCWt c' = 2 →
      ∃ c'' : GGBCV 5, ggBCWt c'' = 2 ∧ c ⬝ᵥ c'' ≠ 0 ∧ c' ⬝ᵥ c'' ≠ 0 := by
  set_option synthInstance.maxSize 2048 in
  decide +kernel

private lemma ggQ2xD5b_global_scalar
    (A : Subgroup (GGBCV 5 ≃ₗ[ZMod 3] GGBCV 5))
    (hW : ggBCReflGp (ggDRoots 5) ≤ A)
    (hS1 : ∀ (c : GGBCV 5) (φ : Module.Dual (ZMod 3) (GGBCV 5)) (h : φ c = 2),
      Module.reflection h ∈ A → ∃ ε : ZMod 3, (ε = 1 ∨ ε = -1) ∧ ∀ v, φ v = ε * (c ⬝ᵥ v))
    (a : GGBCV 5 ≃ₗ[ZMod 3] GGBCV 5) (ha : a ∈ A) :
    ∃ κ : ZMod 3, ∀ c ∈ ggDRoots 5, ∀ w, (a c) ⬝ᵥ (a w) = κ * (c ⬝ᵥ w) := by
  let c0 : GGBCV 5 := Pi.single 0 1 + Pi.single 1 1
  have hc0 : c0 ∈ ggDRoots 5 := by
    show ggBCWt c0 = 2
    exact ggQ2x_wt_single_add_single 0 1 (by decide) 1 1 (by decide) (by decide)
  obtain ⟨κ0, hκ0⟩ := ggQ2xD5b_root_scalar A hW hS1 a ha hc0
  refine ⟨κ0, fun c hc => ?_⟩
  obtain ⟨κc, hκc⟩ := ggQ2xD5b_root_scalar A hW hS1 a ha hc
  obtain ⟨c'', hc''w, h1, h2⟩ := ggQ2xD5b_connectivity c c0 hc hc0
  have hc'' : c'' ∈ ggDRoots 5 := hc''w
  obtain ⟨κ'', hκ''⟩ := ggQ2xD5b_root_scalar A hW hS1 a ha hc''
  have e1 : κc = κ'' := ggQ2xD5b_scalar_const h1 hκc hκ''
  have e2 : κ0 = κ'' := ggQ2xD5b_scalar_const h2 hκ0 hκ''
  have hκ0c : κ0 = κc := by rw [e2, ← e1]
  intro w
  rw [hκ0c]
  exact hκc w

private lemma ggQ2xD5b_exists_ne (i : Fin 5) : ∃ j : Fin 5, j ≠ i := by
  fin_cases i <;> first | exact ⟨1, by decide⟩ | exact ⟨0, by decide⟩

private lemma ggQ2xD5b_linearize (a : GGBCV 5 ≃ₗ[ZMod 3] GGBCV 5) {κ : ZMod 3}
    (hκ : ∀ c ∈ ggDRoots 5, ∀ w, (a c) ⬝ᵥ (a w) = κ * (c ⬝ᵥ w)) :
    ∀ u w, (a u) ⬝ᵥ (a w) = κ * (u ⬝ᵥ w) := by
  intro u w
  let F : GGBCV 5 →ₗ[ZMod 3] ZMod 3 :=
    (ggBCDot (a w)).comp a.toLinearMap - κ • ggBCDot w
  have hFroot : ∀ c ∈ ggDRoots 5, F c = 0 := by
    intro c hc
    change (ggBCDot (a w)) (a c) - (κ • ggBCDot w) c = 0
    rw [LinearMap.smul_apply, smul_eq_mul, ggQ2x_ggBCDot_apply, ggQ2x_ggBCDot_apply]
    rw [dotProduct_comm (a w) (a c), dotProduct_comm w c, hκ c hc w, sub_self]
  have hsingle : ∀ i : Fin 5, F (Pi.single i 1) = 0 := by
    intro i
    obtain ⟨j, hji⟩ := ggQ2xD5b_exists_ne i
    have hc1 : (Pi.single i 1 - Pi.single j 1 : GGBCV 5) ∈ ggDRoots 5 := by
      show ggBCWt (Pi.single i 1 - Pi.single j 1) = 2
      exact ggQ2x_wt_sub_single i j (Ne.symm hji)
    have hc2 : (Pi.single i 1 + Pi.single j 1 : GGBCV 5) ∈ ggDRoots 5 := by
      show ggBCWt (Pi.single i 1 + Pi.single j 1) = 2
      exact ggQ2x_wt_single_add_single i j (Ne.symm hji) 1 1 (by decide) (by decide)
    have hsum : (Pi.single i 1 - Pi.single j 1) + (Pi.single i 1 + Pi.single j 1)
        = (2 : ZMod 3) • (Pi.single i 1 : GGBCV 5) := by
      rw [two_smul]
      abel
    have hdecomp : (Pi.single i 1 : GGBCV 5) = (2 : ZMod 3) •
        ((Pi.single i 1 - Pi.single j 1) + (Pi.single i 1 + Pi.single j 1)) := by
      rw [hsum, smul_smul, show (2 : ZMod 3) * 2 = 1 by decide, one_smul]
    rw [hdecomp, map_smul, map_add, hFroot _ hc1, hFroot _ hc2, add_zero, smul_zero]
  have hF0 : F = 0 := by
    apply (Pi.basisFun (ZMod 3) (Fin 5)).ext
    intro i
    simpa using hsingle i
  have hu : (ggBCDot (a w)) (a u) - κ * (ggBCDot w u) = 0 := by
    have h := congrArg (fun g : GGBCV 5 →ₗ[ZMod 3] ZMod 3 => g u) hF0
    simpa [F, LinearMap.smul_apply, smul_eq_mul] using h
  rw [ggQ2x_ggBCDot_apply, ggQ2x_ggBCDot_apply] at hu
  have hwu : (a w) ⬝ᵥ (a u) = κ * (w ⬝ᵥ u) := sub_eq_zero.mp hu
  rw [dotProduct_comm (a u) (a w), dotProduct_comm u w]
  exact hwu

private lemma ggQ2xD5b_kappa_one (a : GGBCV 5 ≃ₗ[ZMod 3] GGBCV 5) {κ : ZMod 3}
    (hκ : ∀ u w, (a u) ⬝ᵥ (a w) = κ * (u ⬝ᵥ w)) : κ = 1 := by
  let M : Matrix (Fin 5) (Fin 5) (ZMod 3) := LinearMap.toMatrix' a.toLinearMap
  have hMtM : M.transpose * M = κ • (1 : Matrix (Fin 5) (Fin 5) (ZMod 3)) := by
    ext j k
    rw [Matrix.mul_apply]
    have hsum : (∑ i, M.transpose j i * M i k) =
        (a (Pi.single j 1)) ⬝ᵥ (a (Pi.single k 1)) := by
      rw [dotProduct]
      apply Finset.sum_congr rfl
      intro i _
      rw [Matrix.transpose_apply]
      change LinearMap.toMatrix' a.toLinearMap i j * LinearMap.toMatrix' a.toLinearMap i k =
        a (Pi.single j 1) i * a (Pi.single k 1) i
      rw [LinearMap.toMatrix'_apply, LinearMap.toMatrix'_apply]
      rfl
    rw [hsum, hκ, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
    congr 1
    rw [single_one_dotProduct]
    by_cases hjk : j = k
    · subst hjk; simp
    · rw [Pi.single_eq_of_ne (M := fun _ => ZMod 3) hjk]
      simp [hjk]
  have hdet : M.det ≠ 0 := by
    let M' : Matrix (Fin 5) (Fin 5) (ZMod 3) := LinearMap.toMatrix' a.symm.toLinearMap
    have hcomp : a.toLinearMap.comp a.symm.toLinearMap = 1 := by ext x; simp
    have hMM' : M * M' = 1 := by
      show LinearMap.toMatrix' a.toLinearMap * LinearMap.toMatrix' a.symm.toLinearMap = 1
      rw [← LinearMap.toMatrix'_comp, hcomp, LinearMap.toMatrix'_one]
    intro h0
    have h := congrArg Matrix.det hMM'
    rw [Matrix.det_mul, h0, zero_mul, Matrix.det_one] at h
    exact zero_ne_one h
  have hdet2 : M.det * M.det = κ ^ 5 := by
    have h := congrArg Matrix.det hMtM
    rw [Matrix.det_mul, Matrix.det_transpose, Matrix.det_smul, Matrix.det_one,
      Fintype.card_fin, mul_one] at h
    exact h
  have hd : M.det * M.det = 1 := by
    have h : ∀ d : ZMod 3, d ≠ 0 → d * d = 1 := by decide
    exact h _ hdet
  have hpow : ∀ x : ZMod 3, x ^ 5 = x := by decide
  have h1 : κ ^ 5 = 1 := by rw [← hdet2, hd]
  rwa [hpow κ] at h1

private theorem ggQ2xD5_isometry (A : Subgroup (GGBCV 5 ≃ₗ[ZMod 3] GGBCV 5))
    (hW : ggBCReflGp (ggDRoots 5) ≤ A)
    (hS1 : ∀ (c : GGBCV 5) (φ : Module.Dual (ZMod 3) (GGBCV 5)) (h : φ c = 2),
      Module.reflection h ∈ A → ∃ ε : ZMod 3, (ε = 1 ∨ ε = -1) ∧ ∀ v, φ v = ε * (c ⬝ᵥ v))
    (a : GGBCV 5 ≃ₗ[ZMod 3] GGBCV 5) (ha : a ∈ A) (u v : GGBCV 5) :
    (a u) ⬝ᵥ (a v) = u ⬝ᵥ v := by
  obtain ⟨κ, hκ⟩ := ggQ2xD5b_global_scalar A hW hS1 a ha
  have hκall := ggQ2xD5b_linearize a hκ
  have hκ1 : κ = 1 := ggQ2xD5b_kappa_one a hκall
  rw [hκall u v, hκ1, one_mul]

private def ggQ2xD5z_phi : List (List ℕ) :=
  [[0, 0, 0, 1, 1], [0, 0, 0, 1, 2], [0, 0, 0, 2, 1], [0, 0, 0, 2, 2], [0, 0, 1, 0, 1],
   [0, 0, 1, 0, 2], [0, 0, 1, 1, 0], [0, 0, 1, 2, 0], [0, 0, 2, 0, 1], [0, 0, 2, 0, 2],
   [0, 0, 2, 1, 0], [0, 0, 2, 2, 0], [0, 1, 0, 0, 1], [0, 1, 0, 0, 2], [0, 1, 0, 1, 0],
   [0, 1, 0, 2, 0], [0, 1, 1, 0, 0], [0, 1, 2, 0, 0], [0, 2, 0, 0, 1], [0, 2, 0, 0, 2],
   [0, 2, 0, 1, 0], [0, 2, 0, 2, 0], [0, 2, 1, 0, 0], [0, 2, 2, 0, 0], [1, 0, 0, 0, 1],
   [1, 0, 0, 0, 2], [1, 0, 0, 1, 0], [1, 0, 0, 2, 0], [1, 0, 1, 0, 0], [1, 0, 2, 0, 0],
   [1, 1, 0, 0, 0], [1, 2, 0, 0, 0], [2, 0, 0, 0, 1], [2, 0, 0, 0, 2], [2, 0, 0, 1, 0],
   [2, 0, 0, 2, 0], [2, 0, 1, 0, 0], [2, 0, 2, 0, 0], [2, 1, 0, 0, 0], [2, 2, 0, 0, 0]]

private def ggQ2xD5z_toRep1 : List (List ℕ × List (List ℕ)) :=
  [([0, 0, 0, 0, 1], [[1, 0, 0, 0, 2]]), ([0, 0, 0, 0, 2], [[1, 0, 0, 0, 1]]),
   ([0, 0, 0, 1, 0], [[1, 0, 0, 2, 0]]), ([0, 0, 0, 2, 0], [[1, 0, 0, 1, 0]]),
   ([0, 0, 1, 0, 0], [[1, 0, 2, 0, 0]]), ([0, 0, 2, 0, 0], [[1, 0, 1, 0, 0]]),
   ([0, 1, 0, 0, 0], [[1, 2, 0, 0, 0]]), ([0, 2, 0, 0, 0], [[1, 1, 0, 0, 0]]),
   ([1, 0, 0, 0, 0], []), ([2, 0, 0, 0, 0], [[1, 0, 0, 0, 2], [1, 0, 0, 0, 1]])]

private def ggQ2xD5z_toRep4 : List (List ℕ × List (List ℕ)) :=
  [([0, 1, 1, 1, 1], [[1, 0, 0, 0, 2]]), ([0, 1, 1, 1, 2], [[1, 0, 0, 0, 1]]),
   ([0, 1, 1, 2, 1], [[1, 0, 0, 1, 0], [0, 0, 0, 1, 2]]),
   ([0, 1, 1, 2, 2], [[1, 0, 0, 1, 0], [0, 0, 0, 1, 1]]),
   ([0, 1, 2, 1, 1], [[1, 0, 1, 0, 0], [0, 0, 1, 0, 2]]),
   ([0, 1, 2, 1, 2], [[1, 0, 1, 0, 0], [0, 0, 1, 0, 1]]),
   ([0, 1, 2, 2, 1], [[1, 0, 0, 0, 2], [0, 0, 1, 1, 0]]),
   ([0, 1, 2, 2, 2], [[1, 0, 0, 0, 1], [0, 0, 1, 1, 0]]),
   ([0, 2, 1, 1, 1], [[1, 1, 0, 0, 0], [0, 1, 0, 0, 2]]),
   ([0, 2, 1, 1, 2], [[1, 1, 0, 0, 0], [0, 1, 0, 0, 1]]),
   ([0, 2, 1, 2, 1], [[1, 0, 0, 0, 2], [0, 1, 0, 1, 0]]),
   ([0, 2, 1, 2, 2], [[1, 0, 0, 0, 1], [0, 1, 0, 1, 0]]),
   ([0, 2, 2, 1, 1], [[1, 0, 0, 0, 2], [0, 1, 1, 0, 0]]),
   ([0, 2, 2, 1, 2], [[1, 0, 0, 0, 1], [0, 1, 1, 0, 0]]),
   ([0, 2, 2, 2, 1], [[1, 0, 0, 1, 0], [0, 1, 1, 0, 0], [0, 0, 0, 1, 2]]),
   ([0, 2, 2, 2, 2], [[1, 0, 0, 1, 0], [0, 1, 1, 0, 0], [0, 0, 0, 1, 1]]),
   ([1, 0, 1, 1, 1], [[0, 1, 0, 0, 2]]), ([1, 0, 1, 1, 2], [[0, 1, 0, 0, 1]]),
   ([1, 0, 1, 2, 1], [[0, 1, 0, 1, 0], [0, 0, 0, 1, 2]]),
   ([1, 0, 1, 2, 2], [[0, 1, 0, 1, 0], [0, 0, 0, 1, 1]]),
   ([1, 0, 2, 1, 1], [[0, 1, 1, 0, 0], [0, 0, 1, 0, 2]]),
   ([1, 0, 2, 1, 2], [[0, 1, 1, 0, 0], [0, 0, 1, 0, 1]]),
   ([1, 0, 2, 2, 1], [[0, 1, 0, 0, 2], [0, 0, 1, 1, 0]]),
   ([1, 0, 2, 2, 2], [[0, 1, 0, 0, 1], [0, 0, 1, 1, 0]]), ([1, 1, 0, 1, 1], [[0, 0, 1, 0, 2]]),
   ([1, 1, 0, 1, 2], [[0, 0, 1, 0, 1]]), ([1, 1, 0, 2, 1], [[0, 0, 1, 1, 0], [0, 0, 0, 1, 2]]),
   ([1, 1, 0, 2, 2], [[0, 0, 1, 1, 0], [0, 0, 0, 1, 1]]), ([1, 1, 1, 0, 1], [[0, 0, 0, 1, 2]]),
   ([1, 1, 1, 0, 2], [[0, 0, 0, 1, 1]]), ([1, 1, 1, 1, 0], []),
   ([1, 1, 1, 2, 0], [[0, 0, 0, 1, 2], [0, 0, 0, 1, 1]]),
   ([1, 1, 2, 0, 1], [[0, 0, 1, 0, 2], [0, 0, 0, 1, 1]]),
   ([1, 1, 2, 0, 2], [[0, 0, 1, 0, 1], [0, 0, 0, 1, 2]]),
   ([1, 1, 2, 1, 0], [[0, 0, 1, 0, 2], [0, 0, 1, 0, 1]]), ([1, 1, 2, 2, 0], [[0, 0, 1, 1, 0]]),
   ([1, 2, 0, 1, 1], [[0, 1, 0, 0, 2], [0, 0, 1, 0, 1]]),
   ([1, 2, 0, 1, 2], [[0, 1, 0, 0, 1], [0, 0, 1, 0, 2]]),
   ([1, 2, 0, 2, 1], [[0, 1, 0, 1, 0], [0, 0, 1, 0, 2]]),
   ([1, 2, 0, 2, 2], [[0, 1, 0, 1, 0], [0, 0, 1, 0, 1]]),
   ([1, 2, 1, 0, 1], [[0, 1, 0, 0, 2], [0, 0, 0, 1, 1]]),
   ([1, 2, 1, 0, 2], [[0, 1, 0, 0, 1], [0, 0, 0, 1, 2]]),
   ([1, 2, 1, 1, 0], [[0, 1, 0, 0, 2], [0, 1, 0, 0, 1]]), ([1, 2, 1, 2, 0], [[0, 1, 0, 1, 0]]),
   ([1, 2, 2, 0, 1], [[0, 1, 1, 0, 0], [0, 0, 0, 1, 2]]),
   ([1, 2, 2, 0, 2], [[0, 1, 1, 0, 0], [0, 0, 0, 1, 1]]), ([1, 2, 2, 1, 0], [[0, 1, 1, 0, 0]]),
   ([1, 2, 2, 2, 0], [[0, 1, 1, 0, 0], [0, 0, 0, 1, 2], [0, 0, 0, 1, 1]]),
   ([2, 0, 1, 1, 1], [[1, 0, 0, 0, 2], [0, 1, 0, 0, 1]]),
   ([2, 0, 1, 1, 2], [[1, 0, 0, 0, 1], [0, 1, 0, 0, 2]]),
   ([2, 0, 1, 2, 1], [[1, 0, 0, 1, 0], [0, 1, 0, 0, 2]]),
   ([2, 0, 1, 2, 2], [[1, 0, 0, 1, 0], [0, 1, 0, 0, 1]]),
   ([2, 0, 2, 1, 1], [[1, 0, 1, 0, 0], [0, 1, 0, 0, 2]]),
   ([2, 0, 2, 1, 2], [[1, 0, 1, 0, 0], [0, 1, 0, 0, 1]]),
   ([2, 0, 2, 2, 1], [[1, 0, 1, 0, 0], [0, 1, 0, 1, 0], [0, 0, 0, 1, 2]]),
   ([2, 0, 2, 2, 2], [[1, 0, 1, 0, 0], [0, 1, 0, 1, 0], [0, 0, 0, 1, 1]]),
   ([2, 1, 0, 1, 1], [[1, 0, 0, 0, 2], [0, 0, 1, 0, 1]]),
   ([2, 1, 0, 1, 2], [[1, 0, 0, 0, 1], [0, 0, 1, 0, 2]]),
   ([2, 1, 0, 2, 1], [[1, 0, 0, 1, 0], [0, 0, 1, 0, 2]]),
   ([2, 1, 0, 2, 2], [[1, 0, 0, 1, 0], [0, 0, 1, 0, 1]]),
   ([2, 1, 1, 0, 1], [[1, 0, 0, 0, 2], [0, 0, 0, 1, 1]]),
   ([2, 1, 1, 0, 2], [[1, 0, 0, 0, 1], [0, 0, 0, 1, 2]]),
   ([2, 1, 1, 1, 0], [[1, 0, 0, 0, 2], [1, 0, 0, 0, 1]]), ([2, 1, 1, 2, 0], [[1, 0, 0, 1, 0]]),
   ([2, 1, 2, 0, 1], [[1, 0, 1, 0, 0], [0, 0, 0, 1, 2]]),
   ([2, 1, 2, 0, 2], [[1, 0, 1, 0, 0], [0, 0, 0, 1, 1]]), ([2, 1, 2, 1, 0], [[1, 0, 1, 0, 0]]),
   ([2, 1, 2, 2, 0], [[1, 0, 1, 0, 0], [0, 0, 0, 1, 2], [0, 0, 0, 1, 1]]),
   ([2, 2, 0, 1, 1], [[1, 1, 0, 0, 0], [0, 0, 1, 0, 2]]),
   ([2, 2, 0, 1, 2], [[1, 1, 0, 0, 0], [0, 0, 1, 0, 1]]),
   ([2, 2, 0, 2, 1], [[1, 1, 0, 0, 0], [0, 0, 1, 1, 0], [0, 0, 0, 1, 2]]),
   ([2, 2, 0, 2, 2], [[1, 1, 0, 0, 0], [0, 0, 1, 1, 0], [0, 0, 0, 1, 1]]),
   ([2, 2, 1, 0, 1], [[1, 1, 0, 0, 0], [0, 0, 0, 1, 2]]),
   ([2, 2, 1, 0, 2], [[1, 1, 0, 0, 0], [0, 0, 0, 1, 1]]), ([2, 2, 1, 1, 0], [[1, 1, 0, 0, 0]]),
   ([2, 2, 1, 2, 0], [[1, 1, 0, 0, 0], [0, 0, 0, 1, 2], [0, 0, 0, 1, 1]]),
   ([2, 2, 2, 0, 1], [[1, 1, 0, 0, 0], [0, 0, 1, 0, 2], [0, 0, 0, 1, 1]]),
   ([2, 2, 2, 0, 2], [[1, 1, 0, 0, 0], [0, 0, 1, 0, 1], [0, 0, 0, 1, 2]]),
   ([2, 2, 2, 1, 0], [[1, 1, 0, 0, 0], [0, 0, 1, 0, 2], [0, 0, 1, 0, 1]]),
   ([2, 2, 2, 2, 0], [[1, 1, 0, 0, 0], [0, 0, 1, 1, 0]])]

private def ggQ2xD5z_toRep5 : List (List ℕ × List (List ℕ)) :=
  [([1, 1, 1, 1, 1], []), ([1, 1, 1, 1, 2], [[1, 1, 0, 0, 0], [0, 0, 1, 1, 0]]),
   ([1, 1, 1, 2, 1], [[1, 1, 0, 0, 0], [0, 0, 1, 0, 1]]), ([1, 1, 1, 2, 2], [[0, 0, 0, 1, 1]]),
   ([1, 1, 2, 1, 1], [[1, 1, 0, 0, 0], [0, 0, 0, 1, 1]]), ([1, 1, 2, 1, 2], [[0, 0, 1, 0, 1]]),
   ([1, 1, 2, 2, 1], [[0, 0, 1, 1, 0]]), ([1, 1, 2, 2, 2], [[1, 1, 0, 0, 0]]),
   ([1, 2, 1, 1, 1], [[1, 0, 1, 0, 0], [0, 0, 0, 1, 1]]), ([1, 2, 1, 1, 2], [[0, 1, 0, 0, 1]]),
   ([1, 2, 1, 2, 1], [[0, 1, 0, 1, 0]]), ([1, 2, 1, 2, 2], [[1, 0, 1, 0, 0]]),
   ([1, 2, 2, 1, 1], [[0, 1, 1, 0, 0]]), ([1, 2, 2, 1, 2], [[1, 0, 0, 1, 0]]),
   ([1, 2, 2, 2, 1], [[1, 0, 0, 0, 1]]), ([1, 2, 2, 2, 2], [[0, 1, 1, 0, 0], [0, 0, 0, 1, 1]]),
   ([2, 1, 1, 1, 1], [[0, 1, 1, 0, 0], [0, 0, 0, 1, 1]]), ([2, 1, 1, 1, 2], [[1, 0, 0, 0, 1]]),
   ([2, 1, 1, 2, 1], [[1, 0, 0, 1, 0]]), ([2, 1, 1, 2, 2], [[0, 1, 1, 0, 0]]),
   ([2, 1, 2, 1, 1], [[1, 0, 1, 0, 0]]), ([2, 1, 2, 1, 2], [[0, 1, 0, 1, 0]]),
   ([2, 1, 2, 2, 1], [[0, 1, 0, 0, 1]]), ([2, 1, 2, 2, 2], [[1, 0, 1, 0, 0], [0, 0, 0, 1, 1]]),
   ([2, 2, 1, 1, 1], [[1, 1, 0, 0, 0]]), ([2, 2, 1, 1, 2], [[0, 0, 1, 1, 0]]),
   ([2, 2, 1, 2, 1], [[0, 0, 1, 0, 1]]), ([2, 2, 1, 2, 2], [[1, 1, 0, 0, 0], [0, 0, 0, 1, 1]]),
   ([2, 2, 2, 1, 1], [[0, 0, 0, 1, 1]]), ([2, 2, 2, 1, 2], [[1, 1, 0, 0, 0], [0, 0, 1, 0, 1]]),
   ([2, 2, 2, 2, 1], [[1, 1, 0, 0, 0], [0, 0, 1, 1, 0]]), ([2, 2, 2, 2, 2], [])]

private def ggQ2xD5z_der1 : List (ℕ × ℕ × List ℕ) :=
  [(24, 40, [0, 0, 0, 0, 2]), (25, 40, [0, 0, 0, 0, 1]), (26, 40, [0, 0, 0, 2, 0]),
   (27, 40, [0, 0, 0, 1, 0]), (28, 40, [0, 0, 2, 0, 0]), (29, 40, [0, 0, 1, 0, 0]),
   (30, 40, [0, 2, 0, 0, 0]), (31, 40, [0, 1, 0, 0, 0]), (40, 40, [2, 0, 0, 0, 0])]

private def ggQ2xD5z_der4 : List (ℕ × ℕ × List ℕ) :=
  [(0, 40, [1, 1, 1, 0, 2]), (1, 40, [1, 1, 1, 0, 1]), (4, 40, [1, 1, 0, 1, 2]),
   (5, 40, [1, 1, 0, 1, 1]), (6, 40, [1, 1, 2, 2, 0]), (12, 40, [1, 0, 1, 1, 2]),
   (13, 40, [1, 0, 1, 1, 1]), (14, 40, [1, 2, 1, 2, 0]), (16, 40, [1, 2, 2, 1, 0]),
   (24, 40, [0, 1, 1, 1, 2]), (25, 40, [0, 1, 1, 1, 1]), (26, 40, [2, 1, 1, 2, 0]),
   (28, 40, [2, 1, 2, 1, 0]), (30, 40, [2, 2, 1, 1, 0]), (40, 0, [1, 1, 1, 2, 1]),
   (40, 1, [1, 1, 1, 2, 2]), (40, 2, [2, 2, 2, 1, 1]), (40, 3, [2, 2, 2, 1, 2]),
   (40, 4, [1, 1, 2, 1, 1]), (40, 5, [1, 1, 2, 1, 2]), (40, 8, [2, 2, 1, 2, 1]),
   (40, 9, [2, 2, 1, 2, 2]), (40, 12, [1, 2, 1, 1, 1]), (40, 13, [1, 2, 1, 1, 2]),
   (40, 18, [2, 1, 2, 2, 1]), (40, 19, [2, 1, 2, 2, 2]), (40, 24, [2, 1, 1, 1, 1]),
   (40, 25, [2, 1, 1, 1, 2]), (40, 32, [1, 2, 2, 2, 1]), (40, 33, [1, 2, 2, 2, 2]),
   (40, 40, [2, 2, 2, 2, 0]), (0, 42, [1, 1, 1, 2, 0]), (0, 44, [1, 1, 0, 2, 2]),
   (0, 45, [1, 1, 2, 0, 1]), (0, 47, [1, 0, 1, 2, 2]), (0, 48, [1, 2, 1, 0, 1]),
   (0, 49, [1, 2, 2, 0, 2]), (0, 51, [0, 1, 1, 2, 2]), (0, 52, [2, 1, 1, 0, 1]),
   (0, 53, [2, 1, 2, 0, 2]), (0, 54, [2, 2, 1, 0, 2]), (0, 56, [1, 1, 1, 1, 1]),
   (0, 57, [2, 2, 2, 2, 2]), (0, 59, [1, 1, 2, 2, 2]), (0, 62, [2, 2, 1, 1, 1]),
   (0, 63, [1, 2, 1, 2, 2]), (0, 66, [2, 1, 2, 1, 1]), (0, 67, [2, 1, 1, 2, 2]),
   (0, 70, [1, 2, 2, 1, 1]), (0, 71, [2, 2, 2, 0, 1]), (1, 43, [1, 1, 0, 2, 1]),
   (1, 45, [1, 1, 2, 0, 2]), (1, 46, [1, 0, 1, 2, 1]), (1, 48, [1, 2, 1, 0, 2]),
   (1, 49, [1, 2, 2, 0, 1]), (1, 50, [0, 1, 1, 2, 1]), (1, 52, [2, 1, 1, 0, 2]),
   (1, 53, [2, 1, 2, 0, 1]), (1, 54, [2, 2, 1, 0, 1]), (1, 55, [1, 1, 1, 1, 2]),
   (1, 58, [2, 2, 2, 2, 1]), (1, 60, [1, 1, 2, 2, 1]), (1, 61, [2, 2, 1, 1, 2]),
   (1, 64, [1, 2, 1, 2, 1]), (1, 65, [2, 1, 2, 1, 2]), (1, 68, [2, 1, 1, 2, 1]),
   (1, 69, [1, 2, 2, 1, 2]), (1, 71, [2, 2, 2, 0, 2]), (4, 44, [1, 1, 2, 1, 0]),
   (4, 47, [1, 0, 2, 1, 2]), (4, 48, [1, 2, 0, 2, 2]), (4, 49, [1, 2, 0, 1, 1]),
   (4, 51, [0, 1, 2, 1, 2]), (4, 52, [2, 1, 0, 2, 2]), (4, 53, [2, 1, 0, 1, 1]),
   (4, 54, [2, 2, 0, 1, 2]), (4, 71, [2, 2, 0, 2, 1]), (5, 46, [1, 0, 2, 1, 1]),
   (5, 48, [1, 2, 0, 2, 1]), (5, 49, [1, 2, 0, 1, 2]), (5, 50, [0, 1, 2, 1, 1]),
   (5, 52, [2, 1, 0, 2, 1]), (5, 53, [2, 1, 0, 1, 2]), (5, 54, [2, 2, 0, 1, 1]),
   (5, 71, [2, 2, 0, 2, 2]), (6, 46, [1, 0, 2, 2, 2]), (6, 47, [1, 0, 2, 2, 1]),
   (6, 50, [0, 1, 2, 2, 2]), (6, 51, [0, 1, 2, 2, 1]), (12, 47, [1, 2, 1, 1, 0]),
   (12, 51, [0, 2, 1, 1, 2]), (12, 52, [2, 0, 1, 2, 2]), (12, 53, [2, 0, 2, 1, 2]),
   (12, 54, [2, 0, 1, 1, 1]), (12, 71, [2, 0, 2, 2, 1]), (13, 50, [0, 2, 1, 1, 1]),
   (13, 52, [2, 0, 1, 2, 1]), (13, 53, [2, 0, 2, 1, 1]), (13, 54, [2, 0, 1, 1, 2]),
   (13, 71, [2, 0, 2, 2, 2]), (14, 50, [0, 2, 1, 2, 2]), (14, 51, [0, 2, 1, 2, 1]),
   (16, 50, [0, 2, 2, 1, 2]), (16, 51, [0, 2, 2, 1, 1]), (24, 51, [2, 1, 1, 1, 0]),
   (24, 71, [0, 2, 2, 2, 1]), (25, 71, [0, 2, 2, 2, 2]), (41, 42, [0, 0, 0, 0, 2]),
   (42, 41, [0, 0, 0, 0, 1]), (55, 42, [0, 0, 0, 1, 0]), (59, 44, [0, 0, 1, 0, 0]),
   (63, 47, [0, 1, 0, 0, 0]), (67, 51, [1, 0, 0, 0, 0]), (0, 95, [1, 2, 2, 2, 0]),
   (0, 98, [2, 1, 2, 2, 0]), (0, 99, [2, 2, 1, 2, 0]), (0, 108, [2, 2, 2, 1, 0]),
   (0, 149, [0, 0, 0, 2, 0]), (4, 149, [0, 0, 2, 0, 0]), (12, 149, [0, 2, 0, 0, 0]),
   (24, 149, [2, 0, 0, 0, 0])]

private def ggQ2xD5z_der5 : List (ℕ × ℕ × List ℕ) :=
  [(0, 40, [1, 1, 1, 2, 2]), (4, 40, [1, 1, 2, 1, 2]), (6, 40, [1, 1, 2, 2, 1]),
   (12, 40, [1, 2, 1, 1, 2]), (14, 40, [1, 2, 1, 2, 1]), (16, 40, [1, 2, 2, 1, 1]),
   (24, 40, [2, 1, 1, 1, 2]), (26, 40, [2, 1, 1, 2, 1]), (28, 40, [2, 1, 2, 1, 1]),
   (30, 40, [2, 2, 1, 1, 1]), (40, 3, [2, 2, 2, 1, 1]), (40, 9, [2, 2, 1, 2, 1]),
   (40, 11, [2, 2, 1, 1, 2]), (40, 19, [2, 1, 2, 2, 1]), (40, 21, [2, 1, 2, 1, 2]),
   (40, 23, [2, 1, 1, 2, 2]), (40, 33, [1, 2, 2, 2, 1]), (40, 35, [1, 2, 2, 1, 2]),
   (40, 37, [1, 2, 1, 2, 2]), (40, 39, [1, 1, 2, 2, 2]), (40, 40, [2, 2, 2, 2, 2]),
   (0, 46, [1, 2, 2, 2, 2]), (0, 49, [2, 1, 2, 2, 2]), (0, 50, [2, 2, 1, 2, 2]),
   (0, 56, [2, 1, 1, 1, 1]), (0, 59, [1, 2, 1, 1, 1]), (0, 60, [1, 1, 2, 1, 1]),
   (4, 50, [2, 2, 2, 1, 2]), (4, 60, [1, 1, 1, 2, 1]), (6, 50, [2, 2, 2, 2, 1]),
   (6, 60, [1, 1, 1, 1, 2])]

private def ggQ2xD5z_vec (l : List ℕ) : GGBCV 5 :=
  fun i => ((l.getD (i : ℕ) 0 : ℕ) : ZMod 3)

private def ggQ2xD5z_digits (v : GGBCV 5) : List ℕ :=
  [(v 0).val, (v 1).val, (v 2).val, (v 3).val, (v 4).val]

private theorem ggQ2xD5z_vec_digits (v : GGBCV 5) : ggQ2xD5z_vec (ggQ2xD5z_digits v) = v := by
  funext i
  fin_cases i <;> simp [ggQ2xD5z_vec, ggQ2xD5z_digits]

private def ggQ2xD5z_rf (z w : GGBCV 5) : GGBCV 5 :=
  w + ((z ⬝ᵥ w) * (z ⬝ᵥ z)) • z

private def ggQ2xD5z_third (e : ℕ × ℕ × List ℕ) : List ℕ := e.2.2

private def ggQ2xD5z_applyRoots : List (List ℕ) → GGBCV 5 → GGBCV 5
  | [], w => w
  | ρ :: l, w => ggQ2xD5z_applyRoots l (ggQ2xD5z_rf (ggQ2xD5z_vec ρ) w)

private def ggQ2xD5z_step (S : List (GGBCV 5)) (e : ℕ × ℕ × List ℕ) : Option (List (GGBCV 5)) :=
  (S[e.1]?).bind fun z =>
    (S[e.2.1]?).bind fun w =>
      if z ⬝ᵥ z = 0 then none
      else if ggQ2xD5z_rf z w = ggQ2xD5z_vec e.2.2 then some (S ++ [ggQ2xD5z_vec e.2.2]) else none

private def ggQ2xD5z_deriveAll : List (GGBCV 5) → List (ℕ × ℕ × List ℕ) → Option (List (GGBCV 5))
  | S, [] => some S
  | S, e :: es => (ggQ2xD5z_step S e).bind (fun S' => ggQ2xD5z_deriveAll S' es)

private def ggQ2xD5z_T1 : List (GGBCV 5) :=
  (ggQ2xD5z_phi ++ [[1, 0, 0, 0, 0]] ++ ggQ2xD5z_der1.map ggQ2xD5z_third).map ggQ2xD5z_vec

private def ggQ2xD5z_T4 : List (GGBCV 5) :=
  (ggQ2xD5z_phi ++ [[1, 1, 1, 1, 0]] ++ ggQ2xD5z_der4.map ggQ2xD5z_third).map ggQ2xD5z_vec

private def ggQ2xD5z_T5 : List (GGBCV 5) :=
  (ggQ2xD5z_phi ++ [[1, 1, 1, 1, 1]] ++ ggQ2xD5z_der5.map ggQ2xD5z_third).map ggQ2xD5z_vec

private theorem ggQ2xD5z_der1_eq :
    ggQ2xD5z_deriveAll ((ggQ2xD5z_phi ++ [[1, 0, 0, 0, 0]]).map ggQ2xD5z_vec)
      ggQ2xD5z_der1 = some ggQ2xD5z_T1 := by
  decide +kernel

private theorem ggQ2xD5z_der4_eq :
    ggQ2xD5z_deriveAll ((ggQ2xD5z_phi ++ [[1, 1, 1, 1, 0]]).map ggQ2xD5z_vec)
      ggQ2xD5z_der4 = some ggQ2xD5z_T4 := by
  decide +kernel

private theorem ggQ2xD5z_der5_eq :
    ggQ2xD5z_deriveAll ((ggQ2xD5z_phi ++ [[1, 1, 1, 1, 1]]).map ggQ2xD5z_vec)
      ggQ2xD5z_der5 = some ggQ2xD5z_T5 := by
  decide +kernel

private theorem ggQ2xD5z_der1_cov :
    ∀ v : GGBCV 5, ggBCWt v = 1 ∨ ggBCWt v = 2 → v ∈ ggQ2xD5z_T1 := by
  decide +kernel

private theorem ggQ2xD5z_der4_cov : ∀ v : GGBCV 5, v ⬝ᵥ v ≠ 0 → v ∈ ggQ2xD5z_T4 := by decide +kernel

private theorem ggQ2xD5z_der5_cov :
    ∀ v : GGBCV 5, ggBCWt v = 2 ∨ ggBCWt v = 5 → v ∈ ggQ2xD5z_T5 := by
  decide +kernel

private theorem ggQ2xD5z_toRep1_cov : ∀ v : GGBCV 5, ggBCWt v = 1 →
    ∃ p ∈ ggQ2xD5z_toRep1, ggQ2xD5z_digits v = p.1 := by decide +kernel

private theorem ggQ2xD5z_toRep4_cov : ∀ v : GGBCV 5, ggBCWt v = 4 →
    ∃ p ∈ ggQ2xD5z_toRep4, ggQ2xD5z_digits v = p.1 := by decide +kernel

private theorem ggQ2xD5z_toRep5_cov : ∀ v : GGBCV 5, ggBCWt v = 5 →
    ∃ p ∈ ggQ2xD5z_toRep5, ggQ2xD5z_digits v = p.1 := by decide +kernel

private theorem ggQ2xD5z_toRep1_good : ∀ p ∈ ggQ2xD5z_toRep1,
    ggQ2xD5z_applyRoots p.2 (ggQ2xD5z_vec p.1) = ggQ2xD5z_vec [1, 0, 0, 0, 0] ∧
      ∀ ρ ∈ p.2, ggBCWt (ggQ2xD5z_vec ρ) = 2 := by decide +kernel

private theorem ggQ2xD5z_toRep4_good : ∀ p ∈ ggQ2xD5z_toRep4,
    ggQ2xD5z_applyRoots p.2 (ggQ2xD5z_vec p.1) = ggQ2xD5z_vec [1, 1, 1, 1, 0] ∧
      ∀ ρ ∈ p.2, ggBCWt (ggQ2xD5z_vec ρ) = 2 := by decide +kernel

private theorem ggQ2xD5z_toRep5_good : ∀ p ∈ ggQ2xD5z_toRep5,
    (ggQ2xD5z_applyRoots p.2 (ggQ2xD5z_vec p.1) = ggQ2xD5z_vec [1, 1, 1, 1, 1] ∨
      ggQ2xD5z_applyRoots p.2 (ggQ2xD5z_vec p.1) = ggQ2xD5z_vec [2, 2, 2, 2, 2]) ∧
      ∀ ρ ∈ p.2, ggBCWt (ggQ2xD5z_vec ρ) = 2 := by decide +kernel

private theorem ggQ2xD5z_rf_eq (z w : GGBCV 5) (hz : z ⬝ᵥ z ≠ 0) :
    ggQ2xD5z_rf z w = ggBCRefl z hz w := by
  rw [ggQ2xD5z_rf, ggQ2x_ggBCRefl_apply]

private theorem ggQ2xD5z_wt_class (v : GGBCV 5) (hv : v ⬝ᵥ v ≠ 0) :
    ggBCWt v = 1 ∨ ggBCWt v = 2 ∨ ggBCWt v = 4 ∨ ggBCWt v = 5 := by
  have hle : ggBCWt v ≤ 5 := by
    unfold ggBCWt
    calc (Finset.univ.filter fun i => v i ≠ 0).card
        ≤ (Finset.univ : Finset (Fin 5)).card := Finset.card_filter_le _ _
      _ = 5 := by simp
  rw [ggQ2x_dot_self_eq_wt] at hv
  revert hv
  interval_cases h : ggBCWt v <;> decide

private theorem ggQ2xD5z_neg_mem (Z : Set (GGBCV 5)) (hZ0 : ∀ z ∈ Z, z ⬝ᵥ z ≠ 0)
    (hZcl : ∀ z ∈ Z, ∀ w ∈ Z, ∀ hz : z ⬝ᵥ z ≠ 0, ggBCRefl z hz w ∈ Z)
    {w : GGBCV 5} (hw : w ∈ Z) : -w ∈ Z := by
  have hz := hZ0 w hw
  have hcl := hZcl w hw w hw hz
  have hsp : (w ⬝ᵥ w) * (w ⬝ᵥ w) = 1 :=
    (by decide : ∀ x : ZMod 3, x ≠ 0 → x * x = 1) (w ⬝ᵥ w) hz
  have heq : ggBCRefl w hz w = -w := by
    rw [ggQ2x_ggBCRefl_apply, hsp, one_smul]
    rw [← two_smul (ZMod 3) w]
    rw [show (2 : ZMod 3) = -1 by decide, neg_smul, one_smul]
  rwa [heq] at hcl

private theorem ggQ2xD5z_applyRoots_mem (Z : Set (GGBCV 5))
    (hZ0 : ∀ z ∈ Z, z ⬝ᵥ z ≠ 0)
    (hZcl : ∀ z ∈ Z, ∀ w ∈ Z, ∀ hz : z ⬝ᵥ z ≠ 0, ggBCRefl z hz w ∈ Z) :
    ∀ (word : List (List ℕ)), (∀ ρ ∈ word, ggQ2xD5z_vec ρ ∈ Z) →
      ∀ w ∈ Z, ggQ2xD5z_applyRoots word w ∈ Z := by
  intro word
  induction word with
  | nil => intro _ w hw; simpa [ggQ2xD5z_applyRoots] using hw
  | cons ρ l ih =>
      intro hroots w hw
      have hρ : ggQ2xD5z_vec ρ ∈ Z := hroots ρ (by simp)
      have hz : ggQ2xD5z_vec ρ ⬝ᵥ ggQ2xD5z_vec ρ ≠ 0 := hZ0 _ hρ
      have hroots' : ∀ σ ∈ l, ggQ2xD5z_vec σ ∈ Z := fun σ hσ => hroots σ (by simp [hσ])
      show ggQ2xD5z_applyRoots l (ggQ2xD5z_rf (ggQ2xD5z_vec ρ) w) ∈ Z
      refine ih hroots' _ ?_
      rw [ggQ2xD5z_rf_eq (ggQ2xD5z_vec ρ) w hz]
      exact hZcl _ hρ w hw hz

private theorem ggQ2xD5z_step_sound (Z : Set (GGBCV 5))
    (hZcl : ∀ z ∈ Z, ∀ w ∈ Z, ∀ hz : z ⬝ᵥ z ≠ 0, ggBCRefl z hz w ∈ Z)
    {S : List (GGBCV 5)} (hS : ∀ x ∈ S, x ∈ Z) {e : ℕ × ℕ × List ℕ}
    {S' : List (GGBCV 5)} (h : ggQ2xD5z_step S e = some S') :
    ∀ x ∈ S', x ∈ Z := by
  intro x hx
  unfold ggQ2xD5z_step at h
  cases h1 : S[e.1]? with
  | none => rw [h1, Option.bind_none] at h; exact absurd h (by simp)
  | some z =>
    rw [h1, Option.bind_some] at h
    cases h2 : S[e.2.1]? with
    | none => rw [h2, Option.bind_none] at h; exact absurd h (by simp)
    | some w =>
      rw [h2, Option.bind_some] at h
      by_cases hz : z ⬝ᵥ z = 0
      · rw [if_pos hz] at h; exact absurd h (by simp)
      · rw [if_neg hz] at h
        by_cases hr : ggQ2xD5z_rf z w = ggQ2xD5z_vec e.2.2
        · rw [if_pos hr] at h
          have hSeq : S ++ [ggQ2xD5z_vec e.2.2] = S' := Option.some.inj h
          rw [← hSeq] at hx
          rcases List.mem_append.mp hx with hxS | hx1
          · exact hS x hxS
          · have hx1' : x = ggQ2xD5z_vec e.2.2 := List.mem_singleton.mp hx1
            have hzmem : z ∈ S := (List.mem_iff_getElem?).mpr ⟨_, h1⟩
            have hwmem : w ∈ S := (List.mem_iff_getElem?).mpr ⟨_, h2⟩
            have hplayer : ggQ2xD5z_vec e.2.2 ∈ Z := by
              rw [← hr, ggQ2xD5z_rf_eq z w (by simpa using hz)]
              exact hZcl z (hS z hzmem) w (hS w hwmem) (by simpa using hz)
            rw [← hx1'] at hplayer
            exact hplayer
        · rw [if_neg hr] at h; exact absurd h (by simp)

private theorem ggQ2xD5z_deriveAll_sound (Z : Set (GGBCV 5))
    (hZcl : ∀ z ∈ Z, ∀ w ∈ Z, ∀ hz : z ⬝ᵥ z ≠ 0, ggBCRefl z hz w ∈ Z) :
    ∀ (d : List (ℕ × ℕ × List ℕ)) (S T : List (GGBCV 5)),
      ggQ2xD5z_deriveAll S d = some T → (∀ x ∈ S, x ∈ Z) → ∀ x ∈ T, x ∈ Z := by
  intro d
  induction d with
  | nil =>
      intro S T h hS x hx
      simp only [ggQ2xD5z_deriveAll, Option.some.injEq] at h
      rw [← h] at hx
      exact hS x hx
  | cons e es ih =>
      intro S T h hS x hx
      simp only [ggQ2xD5z_deriveAll] at h
      cases hst : ggQ2xD5z_step S e with
      | none => rw [hst] at h; exact absurd h (by simp)
      | some S' =>
          rw [hst] at h
          exact ih S' T h (ggQ2xD5z_step_sound Z hZcl hS hst) x hx

private theorem ggQ2xD5z_phi_mem :
    ∀ p ∈ ggQ2xD5z_phi, ggBCWt (ggQ2xD5z_vec p) = 2 := by
  decide +kernel

private theorem ggQ2xD5z_toRep_sound (Z : Set (GGBCV 5))
    (hZ0 : ∀ z ∈ Z, z ⬝ᵥ z ≠ 0)
    (hZcl : ∀ z ∈ Z, ∀ w ∈ Z, ∀ hz : z ⬝ᵥ z ≠ 0, ggBCRefl z hz w ∈ Z)
    (hZroots : ggDRoots 5 ⊆ Z)
    (l : List (List ℕ × List (List ℕ))) (rep : GGBCV 5)
    (hgood : ∀ p ∈ l, ggQ2xD5z_applyRoots p.2 (ggQ2xD5z_vec p.1) = rep ∧
      ∀ ρ ∈ p.2, ggBCWt (ggQ2xD5z_vec ρ) = 2)
    {v : List ℕ} {word : List (List ℕ)} (hmem : (v, word) ∈ l)
    (hv : ggQ2xD5z_vec v ∈ Z) : rep ∈ Z := by
  have hg := hgood (v, word) hmem
  have hroots : ∀ ρ ∈ word, ggQ2xD5z_vec ρ ∈ Z := fun ρ hρ => hZroots (hg.2 ρ hρ)
  have hz := ggQ2xD5z_applyRoots_mem Z hZ0 hZcl word hroots (ggQ2xD5z_vec v) hv
  rw [hg.1] at hz
  exact hz

private theorem ggQ2xD5z_of_der (Z : Set (GGBCV 5))
    (hZcl : ∀ z ∈ Z, ∀ w ∈ Z, ∀ hz : z ⬝ᵥ z ≠ 0, ggBCRefl z hz w ∈ Z)
    (hZroots : ggDRoots 5 ⊆ Z)
    (rep : List ℕ) (hrep : ggQ2xD5z_vec rep ∈ Z)
    (d : List (ℕ × ℕ × List ℕ)) (T : List (GGBCV 5))
    (hT : ggQ2xD5z_deriveAll ((ggQ2xD5z_phi ++ [rep]).map ggQ2xD5z_vec) d = some T) :
    ∀ x ∈ T, x ∈ Z := by
  refine ggQ2xD5z_deriveAll_sound Z hZcl d ((ggQ2xD5z_phi ++ [rep]).map ggQ2xD5z_vec) T hT ?_
  intro x hx
  rw [List.map_append] at hx
  rcases List.mem_append.mp hx with hx' | hx'
  · obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hx'
    exact hZroots (ggQ2xD5z_phi_mem p hp)
  · simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hx'
    rw [hx']; exact hrep

private theorem ggQ2xD5z_rep1_mem (Z : Set (GGBCV 5))
    (hZ0 : ∀ z ∈ Z, z ⬝ᵥ z ≠ 0) (hZroots : ggDRoots 5 ⊆ Z)
    (hZcl : ∀ z ∈ Z, ∀ w ∈ Z, ∀ hz : z ⬝ᵥ z ≠ 0, ggBCRefl z hz w ∈ Z)
    (h1 : ∃ v ∈ Z, ggBCWt v = 1) : ggQ2xD5z_vec [1, 0, 0, 0, 0] ∈ Z := by
  obtain ⟨v, hvZ, hvwt⟩ := h1
  obtain ⟨p, hpmem, hpd⟩ := ggQ2xD5z_toRep1_cov v hvwt
  obtain ⟨pl, word⟩ := p
  simp only [Prod.fst, Prod.snd] at hpd
  have hmem : (ggQ2xD5z_digits v, word) ∈ ggQ2xD5z_toRep1 := by rw [hpd]; exact hpmem
  have hvZ' : ggQ2xD5z_vec (ggQ2xD5z_digits v) ∈ Z := by rwa [ggQ2xD5z_vec_digits]
  exact ggQ2xD5z_toRep_sound Z hZ0 hZcl hZroots _ _ ggQ2xD5z_toRep1_good hmem hvZ'

private theorem ggQ2xD5z_rep4_mem (Z : Set (GGBCV 5))
    (hZ0 : ∀ z ∈ Z, z ⬝ᵥ z ≠ 0) (hZroots : ggDRoots 5 ⊆ Z)
    (hZcl : ∀ z ∈ Z, ∀ w ∈ Z, ∀ hz : z ⬝ᵥ z ≠ 0, ggBCRefl z hz w ∈ Z)
    (h4 : ∃ v ∈ Z, ggBCWt v = 4) : ggQ2xD5z_vec [1, 1, 1, 1, 0] ∈ Z := by
  obtain ⟨v, hvZ, hvwt⟩ := h4
  obtain ⟨p, hpmem, hpd⟩ := ggQ2xD5z_toRep4_cov v hvwt
  obtain ⟨pl, word⟩ := p
  simp only [Prod.fst, Prod.snd] at hpd
  have hmem : (ggQ2xD5z_digits v, word) ∈ ggQ2xD5z_toRep4 := by rw [hpd]; exact hpmem
  have hvZ' : ggQ2xD5z_vec (ggQ2xD5z_digits v) ∈ Z := by rwa [ggQ2xD5z_vec_digits]
  exact ggQ2xD5z_toRep_sound Z hZ0 hZcl hZroots _ _ ggQ2xD5z_toRep4_good hmem hvZ'

private theorem ggQ2xD5z_rep5_mem (Z : Set (GGBCV 5))
    (hZ0 : ∀ z ∈ Z, z ⬝ᵥ z ≠ 0) (hZroots : ggDRoots 5 ⊆ Z)
    (hZcl : ∀ z ∈ Z, ∀ w ∈ Z, ∀ hz : z ⬝ᵥ z ≠ 0, ggBCRefl z hz w ∈ Z)
    (h5 : ∃ v ∈ Z, ggBCWt v = 5) : ggQ2xD5z_vec [1, 1, 1, 1, 1] ∈ Z := by
  obtain ⟨v, hvZ, hvwt⟩ := h5
  obtain ⟨p, hpmem, hpd⟩ := ggQ2xD5z_toRep5_cov v hvwt
  obtain ⟨pl, word⟩ := p
  simp only [Prod.fst, Prod.snd] at hpd
  have hmem : (ggQ2xD5z_digits v, word) ∈ ggQ2xD5z_toRep5 := by rw [hpd]; exact hpmem
  have hvZ' : ggQ2xD5z_vec (ggQ2xD5z_digits v) ∈ Z := by rwa [ggQ2xD5z_vec_digits]
  have hg := ggQ2xD5z_toRep5_good (ggQ2xD5z_digits v, word) hmem
  have hroots : ∀ ρ ∈ word, ggQ2xD5z_vec ρ ∈ Z := fun ρ hρ => hZroots (hg.2 ρ hρ)
  have hz := ggQ2xD5z_applyRoots_mem Z hZ0 hZcl word hroots (ggQ2xD5z_vec (ggQ2xD5z_digits v)) hvZ'
  rcases hg.1 with h | h
  · rw [h] at hz; exact hz
  · have hneg : ggQ2xD5z_vec [1, 1, 1, 1, 1] =
        -ggQ2xD5z_applyRoots word (ggQ2xD5z_vec (ggQ2xD5z_digits v)) := by rw [h]; decide
    rw [hneg]
    exact ggQ2xD5z_neg_mem Z hZ0 hZcl hz

private theorem ggQ2xD5_Z_cases (Z : Set (GGBCV 5)) (hZ0 : ∀ z ∈ Z, z ⬝ᵥ z ≠ 0)
    (hZroots : ggDRoots 5 ⊆ Z)
    (hZcl : ∀ z ∈ Z, ∀ w ∈ Z, ∀ hz : z ⬝ᵥ z ≠ 0, ggBCRefl z hz w ∈ Z) :
    Z = ggDRoots 5 ∨ Z = ggBCRoots 5 ∨ Z = ggDRoots 5 ∪ {z | ggBCWt z = 5} ∨
      Z = {z | z ⬝ᵥ z ≠ 0} := by
  by_cases h4 : ∃ v ∈ Z, ggBCWt v = 4
  · right; right; right
    apply Set.ext; intro z; constructor
    · intro hz; exact hZ0 z hz
    · intro hz
      have hrep : ggQ2xD5z_vec [1, 1, 1, 1, 0] ∈ Z := ggQ2xD5z_rep4_mem Z hZ0 hZroots hZcl h4
      have hT := ggQ2xD5z_of_der Z hZcl hZroots [1, 1, 1, 1, 0] hrep
        ggQ2xD5z_der4 ggQ2xD5z_T4 ggQ2xD5z_der4_eq
      exact hT z (ggQ2xD5z_der4_cov z hz)
  · by_cases h1 : ∃ v ∈ Z, ggBCWt v = 1
    · by_cases h5 : ∃ v ∈ Z, ggBCWt v = 5
      · exfalso
        have hrep1 : ggQ2xD5z_vec [1, 0, 0, 0, 0] ∈ Z := ggQ2xD5z_rep1_mem Z hZ0 hZroots hZcl h1
        have hrep5 : ggQ2xD5z_vec [1, 1, 1, 1, 1] ∈ Z := ggQ2xD5z_rep5_mem Z hZ0 hZroots hZcl h5
        have hz5 : ggQ2xD5z_vec [1, 1, 1, 1, 1] ⬝ᵥ ggQ2xD5z_vec [1, 1, 1, 1, 1] ≠ 0 := hZ0 _ hrep5
        have hwZ : ggQ2xD5z_rf (ggQ2xD5z_vec [1, 1, 1, 1, 1])
            (ggQ2xD5z_vec [1, 0, 0, 0, 0]) ∈ Z := by
          rw [ggQ2xD5z_rf_eq _ _ hz5]
          exact hZcl _ hrep5 _ hrep1 hz5
        apply h4
        refine ⟨_, hwZ, ?_⟩
        rw [show ggQ2xD5z_rf (ggQ2xD5z_vec [1, 1, 1, 1, 1]) (ggQ2xD5z_vec [1, 0, 0, 0, 0]) =
            ggQ2xD5z_vec [0, 2, 2, 2, 2] by decide]
        decide
      · right; left
        apply Set.ext; intro z; constructor
        · intro hz
          rcases ggQ2xD5z_wt_class z (hZ0 z hz) with h | h | h | h
          · show 1 ≤ ggBCWt z ∧ ggBCWt z ≤ 2
            omega
          · show 1 ≤ ggBCWt z ∧ ggBCWt z ≤ 2
            omega
          · exact absurd ⟨z, hz, h⟩ h4
          · exact absurd ⟨z, hz, h⟩ h5
        · intro hz
          have hwt : ggBCWt z = 1 ∨ ggBCWt z = 2 := by
            have hz' : 1 ≤ ggBCWt z ∧ ggBCWt z ≤ 2 := hz
            omega
          have hrep : ggQ2xD5z_vec [1, 0, 0, 0, 0] ∈ Z := ggQ2xD5z_rep1_mem Z hZ0 hZroots hZcl h1
          have hT := ggQ2xD5z_of_der Z hZcl hZroots [1, 0, 0, 0, 0] hrep
            ggQ2xD5z_der1 ggQ2xD5z_T1 ggQ2xD5z_der1_eq
          exact hT z (ggQ2xD5z_der1_cov z hwt)
    · by_cases h5 : ∃ v ∈ Z, ggBCWt v = 5
      · right; right; left
        apply Set.ext; intro z; constructor
        · intro hz
          rcases ggQ2xD5z_wt_class z (hZ0 z hz) with h | h | h | h
          · exact absurd ⟨z, hz, h⟩ h1
          · exact Or.inl h
          · exact absurd ⟨z, hz, h⟩ h4
          · exact Or.inr h
        · intro hz
          rcases hz with hz | hz
          · exact hZroots hz
          · have hrep : ggQ2xD5z_vec [1, 1, 1, 1, 1] ∈ Z := ggQ2xD5z_rep5_mem Z hZ0 hZroots hZcl h5
            have hT := ggQ2xD5z_of_der Z hZcl hZroots [1, 1, 1, 1, 1] hrep
              ggQ2xD5z_der5 ggQ2xD5z_T5 ggQ2xD5z_der5_eq
            exact hT z (ggQ2xD5z_der5_cov z (Or.inr hz))
      · left
        apply Set.ext; intro z; constructor
        · intro hz
          rcases ggQ2xD5z_wt_class z (hZ0 z hz) with h | h | h | h
          · exact absurd ⟨z, hz, h⟩ h1
          · exact h
          · exact absurd ⟨z, hz, h⟩ h4
          · exact absurd ⟨z, hz, h⟩ h5
        · intro hz; exact hZroots hz

private lemma ggQ2xD5c_isReflLin_bc {n : ℕ} (c : GGBCV n) (hc : c ⬝ᵥ c ≠ 0) :
    IsReflLin (ggBCRefl c hc) := by
  refine ⟨c, (2 / (c ⬝ᵥ c)) • (ggBCDot c : ggQ2_DW_Dualc n), ?_, ?_⟩
  · change (2 / (c ⬝ᵥ c)) * ((ggBCDot c : ggQ2_DW_Dualc n) c) = 2
    rw [ggQ2_DW_dot_apply_c]
    field_simp
  · rfl

private lemma ggQ2xD5c_wt_one {v : GGBCV 5} (h : ggBCWt v = 1) :
    ∃ a : Fin 5, ∃ c : ZMod 3, c ≠ 0 ∧ v = c • Pi.single a 1 := by
  unfold ggBCWt at h
  obtain ⟨a, ha⟩ := Finset.card_eq_one.mp h
  refine ⟨a, v a, ?_, ?_⟩
  · have hm : a ∈ Finset.univ.filter (fun i => v i ≠ 0) := by rw [ha]; simp
    simpa using hm
  · funext i
    by_cases hia : i = a
    · subst hia; simp
    · have hm : i ∉ Finset.univ.filter (fun i => v i ≠ 0) := by rw [ha]; simp [hia]
      have hvi : v i = 0 := by simpa using hm
      simp [Pi.single_eq_of_ne hia, hvi]

private lemma ggQ2xD5c_single_dot (a : Fin 5) (v : GGBCV 5) :
    (Pi.single a (1 : ZMod 3) : GGBCV 5) ⬝ᵥ v = v a := by
  simpa [ggQ2_DW_fvec, ggQ2_DW_dotLin] using ggQ2_DW_dotLin_fvec_left 3 5 a v

private lemma ggQ2xD5c_span_smul (x : GGBCV 5) (c : ZMod 3) (hc : c ≠ 0) :
    Submodule.span (ZMod 3) {c • x} = Submodule.span (ZMod 3) {x} := by
  apply le_antisymm
  · rw [Submodule.span_singleton_le_iff_mem, Submodule.mem_span_singleton]
    exact ⟨c, rfl⟩
  · rw [Submodule.span_singleton_le_iff_mem, Submodule.mem_span_singleton]
    exact ⟨c⁻¹, by rw [smul_smul, inv_mul_cancel₀ hc, one_smul]⟩

private lemma ggQ2xD5c_root_refl_mem (A : Subgroup (GGBCV 5 ≃ₗ[ZMod 3] GGBCV 5))
    (hW : ggBCReflGp (ggDRoots 5) ≤ A) (c : GGBCV 5) (hc : c ∈ ggDRoots 5)
    (hc0 : c ⬝ᵥ c ≠ 0) : ggBCRefl c hc0 ∈ reflGp A :=
  Subgroup.subset_closure
    ⟨hW (Subgroup.subset_closure ⟨c, hc, hc0, rfl⟩), ggQ2xD5c_isReflLin_bc c hc0⟩

private lemma ggQ2xD5c_refl_sub_gen (j : Fin 5) (hj : j ≠ 0) (c : GGBCV 5)
    (hc : c = (Pi.single 0 (1 : ZMod 3) - Pi.single j 1 : GGBCV 5))
    (h : c ⬝ᵥ c ≠ 0) :
    ggBCRefl c h (Pi.single 0 1 : GGBCV 5) = Pi.single j 1 := by
  rw [ggQ2x_ggBCRefl_apply]
  have hdot : c ⬝ᵥ (Pi.single 0 (1 : ZMod 3) : GGBCV 5) = 1 := by
    rw [hc, sub_dotProduct, ggQ2xD5c_single_dot 0 (Pi.single 0 (1 : ZMod 3)),
      Pi.single_eq_same, dotProduct_comm (Pi.single j (1 : ZMod 3)) (Pi.single 0 1),
      ggQ2xD5c_single_dot 0 (Pi.single j (1 : ZMod 3)),
      Pi.single_eq_of_ne (M := fun _ => ZMod 3) (Ne.symm hj), sub_zero]
  have hnorm : c ⬝ᵥ c = 2 := by rw [hc, ggQ2_DW_sub_norm 0 j (Ne.symm hj)]
  rw [hdot, hnorm, hc]
  funext i
  fin_cases j <;> fin_cases i <;> decide

private lemma ggQ2xD5c_refl_add_gen (j : Fin 5) (hj : j ≠ 0) (c : GGBCV 5)
    (hc : c = (Pi.single 0 (1 : ZMod 3) + Pi.single j 1 : GGBCV 5))
    (h : c ⬝ᵥ c ≠ 0) :
    ggBCRefl c h (Pi.single 0 1 : GGBCV 5) = -Pi.single j 1 := by
  rw [ggQ2x_ggBCRefl_apply]
  have hdot : c ⬝ᵥ (Pi.single 0 (1 : ZMod 3) : GGBCV 5) = 1 := by
    rw [hc, add_dotProduct, ggQ2xD5c_single_dot 0 (Pi.single 0 (1 : ZMod 3)),
      Pi.single_eq_same, dotProduct_comm (Pi.single j (1 : ZMod 3)) (Pi.single 0 1),
      ggQ2xD5c_single_dot 0 (Pi.single j (1 : ZMod 3)),
      Pi.single_eq_of_ne (M := fun _ => ZMod 3) (Ne.symm hj), add_zero]
  have hnorm : c ⬝ᵥ c = 2 := by rw [hc, ggQ2_DW_add_norm 0 j (Ne.symm hj)]
  rw [hdot, hnorm, hc]
  funext i
  fin_cases j <;> fin_cases i <;> decide

private lemma ggQ2xD5c_wt_cases (v : GGBCV 5) (hv : (ggBCWt v : ZMod 3) = 1) :
    ggBCWt v = 1 ∨ ggBCWt v = 4 := by
  have hle : ggBCWt v ≤ 5 := by
    simpa [ggBCWt] using Finset.card_le_univ (Finset.univ.filter fun i => v i ≠ 0)
  have h : ∀ n : Fin 6, ((n : ℕ) : ZMod 3) = 1 → (n : ℕ) = 1 ∨ (n : ℕ) = 4 := by
    decide +kernel
  exact h ⟨ggBCWt v, by omega⟩ (by simpa using hv)

private def ggQ2xD5c_N (y : GGBCV 5) : ℕ :=
  (Finset.univ.filter fun ρ : GGBCV 5 => ggBCWt ρ = 2 ∧ ρ ⬝ᵥ y = 0).card

private lemma ggQ2xD5c_N_f0 :
    ggQ2xD5c_N (Pi.single 0 (1 : ZMod 3) : GGBCV 5) = 24 := by
  decide +kernel

private lemma ggQ2xD5c_N_wt4 (y : GGBCV 5) (hy : ggBCWt y = 4) : ggQ2xD5c_N y = 12 := by
  revert y; decide +kernel

private lemma ggQ2xD5c_N_perm (A : Subgroup (GGBCV 5 ≃ₗ[ZMod 3] GGBCV 5))
    (hW : ggBCReflGp (ggDRoots 5) ≤ A)
    (hS1 : ∀ (c : GGBCV 5) (φ : Module.Dual (ZMod 3) (GGBCV 5)) (h : φ c = 2),
      Module.reflection h ∈ A → ∃ ε : ZMod 3, (ε = 1 ∨ ε = -1) ∧ ∀ v, φ v = ε * (c ⬝ᵥ v))
    (hZ : ggQ2xD5_Z A = ggDRoots 5)
    (a : GGBCV 5 ≃ₗ[ZMod 3] GGBCV 5) (ha : a ∈ A) (y : GGBCV 5) :
    ggQ2xD5c_N (a y) = ggQ2xD5c_N y := by
  apply le_antisymm
  · have hmem : a⁻¹ ∈ A := A.inv_mem ha
    have hmap : Set.MapsTo (fun ρ => a⁻¹ ρ)
        (↑(Finset.univ.filter fun ρ : GGBCV 5 => ggBCWt ρ = 2 ∧ ρ ⬝ᵥ (a y) = 0))
        (↑(Finset.univ.filter fun ρ : GGBCV 5 => ggBCWt ρ = 2 ∧ ρ ⬝ᵥ y = 0)) := by
      intro ρ hρ
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hρ ⊢
      obtain ⟨hρ2, hρ0⟩ := hρ
      refine ⟨?_, ?_⟩
      · have hz : ρ ∈ ggQ2xD5_Z A := by rw [hZ]; exact hρ2
        have hmem2 := ggQ2xD5_perm A hS1 a⁻¹ hmem ρ hz
        rwa [hZ] at hmem2
      · have hiso := ggQ2xD5_isometry A hW hS1 a⁻¹ hmem ρ (a y)
        have hy : a⁻¹ (a y) = y := by simp
        rw [hy] at hiso
        rw [hiso, hρ0]
    have hcard := Finset.card_le_card_of_injOn (fun ρ => a⁻¹ ρ) hmap
      (fun x _ z _ h => (a⁻¹).injective h)
    simpa [ggQ2xD5c_N] using hcard
  · have hmap : Set.MapsTo (fun ρ => a ρ)
        (↑(Finset.univ.filter fun ρ : GGBCV 5 => ggBCWt ρ = 2 ∧ ρ ⬝ᵥ y = 0))
        (↑(Finset.univ.filter fun ρ : GGBCV 5 => ggBCWt ρ = 2 ∧ ρ ⬝ᵥ (a y) = 0)) := by
      intro ρ hρ
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hρ ⊢
      obtain ⟨hρ2, hρ0⟩ := hρ
      refine ⟨?_, ?_⟩
      · have hz : ρ ∈ ggQ2xD5_Z A := by rw [hZ]; exact hρ2
        have hmem2 := ggQ2xD5_perm A hS1 a ha ρ hz
        rwa [hZ] at hmem2
      · rw [ggQ2xD5_isometry A hW hS1 a ha ρ y, hρ0]
    have hcard := Finset.card_le_card_of_injOn (fun ρ => a ρ) hmap
      (fun x _ z _ h => a.injective h)
    simpa [ggQ2xD5c_N] using hcard

private theorem ggQ2xD5_wt1 (A : Subgroup (GGBCV 5 ≃ₗ[ZMod 3] GGBCV 5))
    (hW : ggBCReflGp (ggDRoots 5) ≤ A) (v : GGBCV 5) (hv : ggBCWt v = 1) :
    ∃ r ∈ reflGp A, Submodule.span (ZMod 3) {v} =
      Submodule.span (ZMod 3) {r (Pi.single 0 1 : GGBCV 5)} := by
  obtain ⟨j, c, hc, rfl⟩ := ggQ2xD5c_wt_one hv
  have hspan : Submodule.span (ZMod 3) {c • Pi.single j (1 : ZMod 3)} =
      Submodule.span (ZMod 3) {(Pi.single j 1 : GGBCV 5)} := ggQ2xD5c_span_smul _ c hc
  by_cases hj : j = 0
  · subst hj
    refine ⟨1, Subgroup.one_mem _, ?_⟩
    rw [hspan]
    simp
  · rcases ggQ2_DW_eq_one_or_neg_one c hc with hc1 | hcm1
    · subst hc1
      have hnorm : (Pi.single 0 (1 : ZMod 3) - Pi.single j 1 : GGBCV 5) ⬝ᵥ
          (Pi.single 0 1 - Pi.single j 1) ≠ 0 := by
        rw [ggQ2_DW_sub_norm 0 j (Ne.symm hj)]; decide
      refine ⟨ggBCRefl _ hnorm,
        ggQ2xD5c_root_refl_mem A hW _ (ggQ2_DW_Wt_sub_single 0 j (Ne.symm hj)) hnorm, ?_⟩
      rw [hspan, ggQ2xD5c_refl_sub_gen j hj _ rfl hnorm]
    · subst hcm1
      have hnorm : (Pi.single 0 (1 : ZMod 3) + Pi.single j 1 : GGBCV 5) ⬝ᵥ
          (Pi.single 0 1 + Pi.single j 1) ≠ 0 := by
        rw [ggQ2_DW_add_norm 0 j (Ne.symm hj)]; decide
      refine ⟨ggBCRefl _ hnorm,
        ggQ2xD5c_root_refl_mem A hW _ (ggQ2_DW_Wt_add_single 0 j (Ne.symm hj)) hnorm, ?_⟩
      rw [hspan, ggQ2xD5c_refl_add_gen j hj _ rfl hnorm]
      rw [Submodule.span_singleton_eq_span_singleton]
      exact ⟨-1, by simp⟩

private theorem ggQ2xD5_case_Phi (A : Subgroup (GGBCV 5 ≃ₗ[ZMod 3] GGBCV 5))
    (hW : ggBCReflGp (ggDRoots 5) ≤ A)
    (hS1 : ∀ (c : GGBCV 5) (φ : Module.Dual (ZMod 3) (GGBCV 5)) (h : φ c = 2),
      Module.reflection h ∈ A → ∃ ε : ZMod 3, (ε = 1 ∨ ε = -1) ∧ ∀ v, φ v = ε * (c ⬝ᵥ v))
    (hZ : ggQ2xD5_Z A = ggDRoots 5) :
    ∀ a ∈ A, ∃ r ∈ reflGp A, Submodule.span (ZMod 3) {a (Pi.single 0 1 : GGBCV 5)} =
      Submodule.span (ZMod 3) {r (Pi.single 0 1 : GGBCV 5)} := by
  intro a ha
  have hnorm : (a (Pi.single 0 (1 : ZMod 3))) ⬝ᵥ (a (Pi.single 0 1)) = 1 := by
    rw [ggQ2xD5_isometry A hW hS1 a ha, ggQ2xD5c_single_dot 0 (Pi.single 0 1),
      Pi.single_eq_same]
  have hwt : (ggBCWt (a (Pi.single 0 (1 : ZMod 3))) : ZMod 3) = 1 := by
    rw [← ggQ2x_dot_self_eq_wt]; exact hnorm
  rcases ggQ2xD5c_wt_cases _ hwt with h1 | h4
  · exact ggQ2xD5_wt1 A hW _ h1
  · exfalso
    have hN : ggQ2xD5c_N (a (Pi.single 0 (1 : ZMod 3))) =
        ggQ2xD5c_N (Pi.single 0 (1 : ZMod 3)) :=
      ggQ2xD5c_N_perm A hW hS1 hZ a ha (Pi.single 0 1)
    have h12 : ggQ2xD5c_N (a (Pi.single 0 (1 : ZMod 3))) = 12 := ggQ2xD5c_N_wt4 _ h4
    have h24 : ggQ2xD5c_N (Pi.single 0 (1 : ZMod 3)) = 24 := ggQ2xD5c_N_f0
    omega
private theorem ggQ2xD5_case_B (A : Subgroup (GGBCV 5 ≃ₗ[ZMod 3] GGBCV 5))
    (hW : ggBCReflGp (ggDRoots 5) ≤ A)
    (hS1 : ∀ (c : GGBCV 5) (φ : Module.Dual (ZMod 3) (GGBCV 5)) (h : φ c = 2),
      Module.reflection h ∈ A → ∃ ε : ZMod 3, (ε = 1 ∨ ε = -1) ∧ ∀ v, φ v = ε * (c ⬝ᵥ v))
    (hZ : ggQ2xD5_Z A = ggBCRoots 5) :
    ∀ a ∈ A, ∃ r ∈ reflGp A, Submodule.span (ZMod 3) {a (Pi.single 0 1 : GGBCV 5)} =
      Submodule.span (ZMod 3) {r (Pi.single 0 1 : GGBCV 5)} := by
  intro a ha
  have hf0Z : (Pi.single 0 (1 : ZMod 3) : GGBCV 5) ∈ ggQ2xD5_Z A := by
    rw [hZ]
    have hw : ggBCWt (Pi.single 0 (1 : ZMod 3) : GGBCV 5) = 1 := ggQ2x_wt_single 0
    show 1 ≤ ggBCWt (Pi.single 0 (1 : ZMod 3) : GGBCV 5) ∧
      ggBCWt (Pi.single 0 (1 : ZMod 3) : GGBCV 5) ≤ 2
    omega
  have hvZ : a (Pi.single 0 (1 : ZMod 3)) ∈ ggQ2xD5_Z A :=
    ggQ2xD5_perm A hS1 a ha _ hf0Z
  have hle : ggBCWt (a (Pi.single 0 (1 : ZMod 3))) ≤ 2 := by
    have h := hvZ
    rw [hZ] at h
    exact h.2
  have hnorm : (a (Pi.single 0 (1 : ZMod 3))) ⬝ᵥ (a (Pi.single 0 1)) = 1 := by
    rw [ggQ2xD5_isometry A hW hS1 a ha, ggQ2xD5c_single_dot 0 (Pi.single 0 1),
      Pi.single_eq_same]
  have hwt : (ggBCWt (a (Pi.single 0 (1 : ZMod 3))) : ZMod 3) = 1 := by
    rw [← ggQ2x_dot_self_eq_wt]; exact hnorm
  rcases ggQ2xD5c_wt_cases _ hwt with h1 | h4
  · exact ggQ2xD5_wt1 A hW _ h1
  · omega

private lemma ggQ2xD5c_fac1 (x : ZMod 3) (hx : 2 - 2 * x ≠ 0) :
    (1 - x) * (2 - 2 * x) = 2 := by
  revert hx; revert x; decide +kernel

private lemma ggQ2xD5c_fac2 (x : ZMod 3) (hx : 2 + 2 * x ≠ 0) :
    (1 + x) * (2 + 2 * x) = 2 := by
  revert hx; revert x; decide +kernel

private lemma ggQ2xD5c_notboth (x : ZMod 3) : 2 - 2 * x ≠ 0 ∨ 2 + 2 * x ≠ 0 := by
  revert x; decide +kernel

private lemma ggQ2xD5c_sub_dot_f0 (v : GGBCV 5) :
    (Pi.single 0 (1 : ZMod 3) - v : GGBCV 5) ⬝ᵥ Pi.single 0 1 = 1 - v 0 := by
  rw [sub_dotProduct, ggQ2xD5c_single_dot 0 (Pi.single 0 (1 : ZMod 3)), Pi.single_eq_same,
    dotProduct_comm v (Pi.single 0 1), ggQ2xD5c_single_dot 0 v]

private lemma ggQ2xD5c_add_dot_f0 (v : GGBCV 5) :
    (Pi.single 0 (1 : ZMod 3) + v : GGBCV 5) ⬝ᵥ Pi.single 0 1 = 1 + v 0 := by
  rw [add_dotProduct, ggQ2xD5c_single_dot 0 (Pi.single 0 (1 : ZMod 3)), Pi.single_eq_same,
    dotProduct_comm v (Pi.single 0 1), ggQ2xD5c_single_dot 0 v]

private lemma ggQ2xD5c_sub_self_dot (v : GGBCV 5) (hv : v ⬝ᵥ v = 1) :
    (Pi.single 0 (1 : ZMod 3) - v : GGBCV 5) ⬝ᵥ (Pi.single 0 1 - v) =
      2 - 2 * (v 0) := by
  rw [sub_dotProduct, dotProduct_sub, dotProduct_sub,
    ggQ2xD5c_single_dot 0 (Pi.single 0 (1 : ZMod 3)), Pi.single_eq_same,
    ggQ2xD5c_single_dot 0 v, dotProduct_comm v (Pi.single 0 (1 : ZMod 3)),
    ggQ2xD5c_single_dot 0 v, hv]
  ring

private lemma ggQ2xD5c_add_self_dot (v : GGBCV 5) (hv : v ⬝ᵥ v = 1) :
    (Pi.single 0 (1 : ZMod 3) + v : GGBCV 5) ⬝ᵥ (Pi.single 0 1 + v) =
      2 + 2 * (v 0) := by
  rw [add_dotProduct, dotProduct_add, dotProduct_add,
    ggQ2xD5c_single_dot 0 (Pi.single 0 (1 : ZMod 3)), Pi.single_eq_same,
    ggQ2xD5c_single_dot 0 v, dotProduct_comm v (Pi.single 0 (1 : ZMod 3)),
    ggQ2xD5c_single_dot 0 v, hv]
  ring

private lemma ggQ2xD5c_vec_sub (v : GGBCV 5) :
    (Pi.single 0 (1 : ZMod 3) : GGBCV 5) + (2 : ZMod 3) •
      ((Pi.single 0 1 : GGBCV 5) - v) = v := by
  revert v; decide +kernel

private lemma ggQ2xD5c_vec_add (v : GGBCV 5) :
    (Pi.single 0 (1 : ZMod 3) : GGBCV 5) + (2 : ZMod 3) •
      ((Pi.single 0 1 : GGBCV 5) + v) = -v := by
  revert v; decide +kernel

private lemma ggQ2xD5c_span_neg (x : GGBCV 5) :
    Submodule.span (ZMod 3) {x} = Submodule.span (ZMod 3) {-x} := by
  rw [Submodule.span_singleton_eq_span_singleton]
  exact ⟨-1, by simp⟩

private lemma ggQ2xD5c_refl_sub_all (v : GGBCV 5) (hv : v ⬝ᵥ v = 1) (c : GGBCV 5)
    (hc : c = (Pi.single 0 (1 : ZMod 3) - v : GGBCV 5)) (h : c ⬝ᵥ c ≠ 0) :
    ggBCRefl c h (Pi.single 0 1 : GGBCV 5) = v := by
  rw [ggQ2x_ggBCRefl_apply]
  have hdot : c ⬝ᵥ (Pi.single 0 (1 : ZMod 3) : GGBCV 5) = 1 - v 0 := by
    rw [hc, ggQ2xD5c_sub_dot_f0]
  have hnorm : c ⬝ᵥ c = 2 - 2 * (v 0) := by rw [hc, ggQ2xD5c_sub_self_dot v hv]
  have hne : 2 - 2 * (v 0) ≠ 0 := by rwa [hnorm] at h
  have hfac : (1 - v 0) * (2 - 2 * (v 0)) = 2 := ggQ2xD5c_fac1 (v 0) hne
  rw [hdot, hnorm, hfac, hc]
  exact ggQ2xD5c_vec_sub v

private lemma ggQ2xD5c_refl_add_all (v : GGBCV 5) (hv : v ⬝ᵥ v = 1) (c : GGBCV 5)
    (hc : c = (Pi.single 0 (1 : ZMod 3) + v : GGBCV 5)) (h : c ⬝ᵥ c ≠ 0) :
    ggBCRefl c h (Pi.single 0 1 : GGBCV 5) = -v := by
  rw [ggQ2x_ggBCRefl_apply]
  have hdot : c ⬝ᵥ (Pi.single 0 (1 : ZMod 3) : GGBCV 5) = 1 + v 0 := by
    rw [hc, ggQ2xD5c_add_dot_f0]
  have hnorm : c ⬝ᵥ c = 2 + 2 * (v 0) := by rw [hc, ggQ2xD5c_add_self_dot v hv]
  have hne : 2 + 2 * (v 0) ≠ 0 := by rwa [hnorm] at h
  have hfac : (1 + v 0) * (2 + 2 * (v 0)) = 2 := ggQ2xD5c_fac2 (v 0) hne
  rw [hdot, hnorm, hfac, hc]
  exact ggQ2xD5c_vec_add v

private theorem ggQ2xD5_case_all (A : Subgroup (GGBCV 5 ≃ₗ[ZMod 3] GGBCV 5))
    (hW : ggBCReflGp (ggDRoots 5) ≤ A)
    (hS1 : ∀ (c : GGBCV 5) (φ : Module.Dual (ZMod 3) (GGBCV 5)) (h : φ c = 2),
      Module.reflection h ∈ A → ∃ ε : ZMod 3, (ε = 1 ∨ ε = -1) ∧ ∀ v, φ v = ε * (c ⬝ᵥ v))
    (hZ : ggQ2xD5_Z A = {z | z ⬝ᵥ z ≠ 0}) :
    ∀ a ∈ A, ∃ r ∈ reflGp A, Submodule.span (ZMod 3) {a (Pi.single 0 1 : GGBCV 5)} =
      Submodule.span (ZMod 3) {r (Pi.single 0 1 : GGBCV 5)} := by
  intro a ha
  let v : GGBCV 5 := a (Pi.single 0 (1 : ZMod 3))
  have hv : v ⬝ᵥ v = 1 := by
    dsimp only [v]
    rw [ggQ2xD5_isometry A hW hS1 a ha, ggQ2xD5c_single_dot 0 (Pi.single 0 1),
      Pi.single_eq_same]
  rcases ggQ2xD5c_notboth (v 0) with h1 | h2
  · have hz : (Pi.single 0 (1 : ZMod 3) - v : GGBCV 5) ∈ ggQ2xD5_Z A := by
      rw [hZ]
      show (Pi.single 0 (1 : ZMod 3) - v : GGBCV 5) ⬝ᵥ (Pi.single 0 1 - v) ≠ 0
      rw [ggQ2xD5c_sub_self_dot v hv]
      exact h1
    obtain ⟨hz0, hzA⟩ := hz
    refine ⟨ggBCRefl _ hz0, Subgroup.subset_closure
      ⟨hzA, ggQ2xD5c_isReflLin_bc _ hz0⟩, ?_⟩
    rw [ggQ2xD5c_refl_sub_all v hv _ rfl hz0]
  · have hz : (Pi.single 0 (1 : ZMod 3) + v : GGBCV 5) ∈ ggQ2xD5_Z A := by
      rw [hZ]
      show (Pi.single 0 (1 : ZMod 3) + v : GGBCV 5) ⬝ᵥ (Pi.single 0 1 + v) ≠ 0
      rw [ggQ2xD5c_add_self_dot v hv]
      exact h2
    obtain ⟨hz0, hzA⟩ := hz
    refine ⟨ggBCRefl _ hz0, Subgroup.subset_closure
      ⟨hzA, ggQ2xD5c_isReflLin_bc _ hz0⟩, ?_⟩
    rw [ggQ2xD5c_refl_add_all v hv _ rfl hz0]
    exact ggQ2xD5c_span_neg v

private def ggQ2xD5e_vec (l : List ℕ) : GGBCV 5 := fun i => (l.getD i 0 : ZMod 3)

private def ggQ2xD5e_rf (z w : GGBCV 5) : GGBCV 5 :=
  w + ((z ⬝ᵥ w) * (z ⬝ᵥ z)) • z

private def ggQ2xD5e_applyWord : List (List ℕ) → GGBCV 5 → GGBCV 5
  | [], w => w
  | z :: zs, w => ggQ2xD5e_applyWord zs (ggQ2xD5e_rf (ggQ2xD5e_vec z) w)

private def ggQ2xD5e_words : List (List ℕ × List (List ℕ)) :=
  [([0, 1, 1, 1, 1], [[1, 2, 2, 2, 2]]), ([0, 1, 1, 1, 2], [[1, 2, 2, 2, 1]]),
   ([0, 1, 1, 2, 1], [[1, 2, 2, 1, 2]]), ([0, 1, 1, 2, 2], [[1, 2, 2, 1, 1]]),
   ([0, 1, 2, 1, 1], [[1, 2, 1, 2, 2]]), ([0, 1, 2, 1, 2], [[1, 2, 1, 2, 1]]),
   ([0, 1, 2, 2, 1], [[1, 2, 1, 1, 2]]), ([0, 1, 2, 2, 2], [[1, 2, 1, 1, 1]]),
   ([0, 2, 1, 1, 1], [[1, 1, 2, 2, 2]]), ([0, 2, 1, 1, 2], [[1, 1, 2, 2, 1]]),
   ([0, 2, 1, 2, 1], [[1, 1, 2, 1, 2]]), ([0, 2, 1, 2, 2], [[1, 1, 2, 1, 1]]),
   ([0, 2, 2, 1, 1], [[1, 1, 1, 2, 2]]), ([0, 2, 2, 1, 2], [[1, 1, 1, 2, 1]]),
   ([0, 2, 2, 2, 1], [[1, 1, 1, 1, 2]]), ([0, 2, 2, 2, 2], [[1, 1, 1, 1, 1]]),
   ([1, 0, 1, 1, 1], [[1, 1, 0, 0, 0], [1, 1, 1, 1, 1]]),
   ([1, 0, 1, 1, 2], [[1, 1, 0, 0, 0], [1, 1, 1, 1, 2]]),
   ([1, 0, 1, 2, 1], [[1, 1, 0, 0, 0], [1, 1, 1, 2, 1]]),
   ([1, 0, 1, 2, 2], [[1, 1, 0, 0, 0], [1, 1, 1, 2, 2]]),
   ([1, 0, 2, 1, 1], [[1, 1, 0, 0, 0], [1, 1, 2, 1, 1]]),
   ([1, 0, 2, 1, 2], [[1, 1, 0, 0, 0], [1, 1, 2, 1, 2]]),
   ([1, 0, 2, 2, 1], [[1, 1, 0, 0, 0], [1, 1, 2, 2, 1]]),
   ([1, 0, 2, 2, 2], [[1, 1, 0, 0, 0], [1, 1, 2, 2, 2]]),
   ([1, 1, 0, 1, 1], [[1, 0, 1, 0, 0], [1, 1, 1, 1, 1]]),
   ([1, 1, 0, 1, 2], [[1, 0, 1, 0, 0], [1, 1, 1, 1, 2]]),
   ([1, 1, 0, 2, 1], [[1, 0, 1, 0, 0], [1, 1, 1, 2, 1]]),
   ([1, 1, 0, 2, 2], [[1, 0, 1, 0, 0], [1, 1, 1, 2, 2]]),
   ([1, 1, 1, 0, 1], [[1, 0, 0, 1, 0], [1, 1, 1, 1, 1]]),
   ([1, 1, 1, 0, 2], [[1, 0, 0, 1, 0], [1, 1, 1, 1, 2]]),
   ([1, 1, 1, 1, 0], [[1, 0, 0, 0, 1], [1, 1, 1, 1, 1]]),
   ([1, 1, 1, 2, 0], [[1, 0, 0, 0, 1], [1, 1, 1, 2, 1]]),
   ([1, 1, 2, 0, 1], [[1, 0, 0, 1, 0], [1, 1, 2, 1, 1]]),
   ([1, 1, 2, 0, 2], [[1, 0, 0, 1, 0], [1, 1, 2, 1, 2]]),
   ([1, 1, 2, 1, 0], [[1, 0, 0, 0, 1], [1, 1, 2, 1, 1]]),
   ([1, 1, 2, 2, 0], [[1, 0, 0, 0, 1], [1, 1, 2, 2, 1]]),
   ([1, 2, 0, 1, 1], [[1, 0, 1, 0, 0], [1, 2, 1, 1, 1]]),
   ([1, 2, 0, 1, 2], [[1, 0, 1, 0, 0], [1, 2, 1, 1, 2]]),
   ([1, 2, 0, 2, 1], [[1, 0, 1, 0, 0], [1, 2, 1, 2, 1]]),
   ([1, 2, 0, 2, 2], [[1, 0, 1, 0, 0], [1, 2, 1, 2, 2]]),
   ([1, 2, 1, 0, 1], [[1, 0, 0, 1, 0], [1, 2, 1, 1, 1]]),
   ([1, 2, 1, 0, 2], [[1, 0, 0, 1, 0], [1, 2, 1, 1, 2]]),
   ([1, 2, 1, 1, 0], [[1, 0, 0, 0, 1], [1, 2, 1, 1, 1]]),
   ([1, 2, 1, 2, 0], [[1, 0, 0, 0, 1], [1, 2, 1, 2, 1]]),
   ([1, 2, 2, 0, 1], [[1, 0, 0, 1, 0], [1, 2, 2, 1, 1]]),
   ([1, 2, 2, 0, 2], [[1, 0, 0, 1, 0], [1, 2, 2, 1, 2]]),
   ([1, 2, 2, 1, 0], [[1, 0, 0, 0, 1], [1, 2, 2, 1, 1]]),
   ([1, 2, 2, 2, 0], [[1, 0, 0, 0, 1], [1, 2, 2, 2, 1]]),
   ([2, 0, 1, 1, 1], [[1, 1, 0, 0, 0], [1, 2, 2, 2, 2]]),
   ([2, 0, 1, 1, 2], [[1, 1, 0, 0, 0], [1, 2, 2, 2, 1]]),
   ([2, 0, 1, 2, 1], [[1, 1, 0, 0, 0], [1, 2, 2, 1, 2]]),
   ([2, 0, 1, 2, 2], [[1, 1, 0, 0, 0], [1, 2, 2, 1, 1]]),
   ([2, 0, 2, 1, 1], [[1, 1, 0, 0, 0], [1, 2, 1, 2, 2]]),
   ([2, 0, 2, 1, 2], [[1, 1, 0, 0, 0], [1, 2, 1, 2, 1]]),
   ([2, 0, 2, 2, 1], [[1, 1, 0, 0, 0], [1, 2, 1, 1, 2]]),
   ([2, 0, 2, 2, 2], [[1, 1, 0, 0, 0], [1, 2, 1, 1, 1]]),
   ([2, 1, 0, 1, 1], [[1, 0, 1, 0, 0], [1, 2, 2, 2, 2]]),
   ([2, 1, 0, 1, 2], [[1, 0, 1, 0, 0], [1, 2, 2, 2, 1]]),
   ([2, 1, 0, 2, 1], [[1, 0, 1, 0, 0], [1, 2, 2, 1, 2]]),
   ([2, 1, 0, 2, 2], [[1, 0, 1, 0, 0], [1, 2, 2, 1, 1]]),
   ([2, 1, 1, 0, 1], [[1, 0, 0, 1, 0], [1, 2, 2, 2, 2]]),
   ([2, 1, 1, 0, 2], [[1, 0, 0, 1, 0], [1, 2, 2, 2, 1]]),
   ([2, 1, 1, 1, 0], [[1, 0, 0, 0, 1], [1, 2, 2, 2, 2]]),
   ([2, 1, 1, 2, 0], [[1, 0, 0, 0, 1], [1, 2, 2, 1, 2]]),
   ([2, 1, 2, 0, 1], [[1, 0, 0, 1, 0], [1, 2, 1, 2, 2]]),
   ([2, 1, 2, 0, 2], [[1, 0, 0, 1, 0], [1, 2, 1, 2, 1]]),
   ([2, 1, 2, 1, 0], [[1, 0, 0, 0, 1], [1, 2, 1, 2, 2]]),
   ([2, 1, 2, 2, 0], [[1, 0, 0, 0, 1], [1, 2, 1, 1, 2]]),
   ([2, 2, 0, 1, 1], [[1, 0, 1, 0, 0], [1, 1, 2, 2, 2]]),
   ([2, 2, 0, 1, 2], [[1, 0, 1, 0, 0], [1, 1, 2, 2, 1]]),
   ([2, 2, 0, 2, 1], [[1, 0, 1, 0, 0], [1, 1, 2, 1, 2]]),
   ([2, 2, 0, 2, 2], [[1, 0, 1, 0, 0], [1, 1, 2, 1, 1]]),
   ([2, 2, 1, 0, 1], [[1, 0, 0, 1, 0], [1, 1, 2, 2, 2]]),
   ([2, 2, 1, 0, 2], [[1, 0, 0, 1, 0], [1, 1, 2, 2, 1]]),
   ([2, 2, 1, 1, 0], [[1, 0, 0, 0, 1], [1, 1, 2, 2, 2]]),
   ([2, 2, 1, 2, 0], [[1, 0, 0, 0, 1], [1, 1, 2, 1, 2]]),
   ([2, 2, 2, 0, 1], [[1, 0, 0, 1, 0], [1, 1, 1, 2, 2]]),
   ([2, 2, 2, 0, 2], [[1, 0, 0, 1, 0], [1, 1, 1, 2, 1]]),
   ([2, 2, 2, 1, 0], [[1, 0, 0, 0, 1], [1, 1, 1, 2, 2]]),
   ([2, 2, 2, 2, 0], [[1, 0, 0, 0, 1], [1, 1, 1, 1, 2]])]

private lemma ggQ2xD5e_table :
    ∀ t : GGBCV 5, ggBCWt t = 4 →
      ∃ row ∈ ggQ2xD5e_words, ggQ2xD5e_vec row.1 = t ∧
        (∀ z ∈ row.2, ggBCWt (ggQ2xD5e_vec z) = 2 ∨ ggBCWt (ggQ2xD5e_vec z) = 5) ∧
        (ggQ2xD5e_applyWord row.2 (Pi.single 0 1 : GGBCV 5) = t ∨
          ggQ2xD5e_applyWord row.2 (Pi.single 0 1 : GGBCV 5) = -t) := by
  decide +kernel

private lemma ggQ2xD5e_wt_eq_one_or_four {n : ℕ} (hle : n ≤ 5) (h : (n : ZMod 3) = 1) :
    n = 1 ∨ n = 4 := by
  have hcases : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd h (by decide)
  · exact Or.inl rfl
  · exact absurd h (by decide)
  · exact absurd h (by decide)
  · exact Or.inr rfl
  · exact absurd h (by decide)

private abbrev ggQ2xD5e_Dualc (n : ℕ) : Type :=
  @Module.Dual (ZMod 3) (GGBCV n) _ _ (ggBCModule n)

private lemma ggQ2xD5e_isReflLin_bc {n : ℕ} (c : GGBCV n) (hc : c ⬝ᵥ c ≠ 0) :
    IsReflLin (ggBCRefl c hc) := by
  refine ⟨c, (2 / (c ⬝ᵥ c)) • (ggBCDot c : ggQ2xD5e_Dualc n), ?_, ?_⟩
  · change (2 / (c ⬝ᵥ c)) * ((ggBCDot c : ggQ2xD5e_Dualc n) c) = 2
    rw [ggQ2x_ggBCDot_apply]
    field_simp
  · rfl

private lemma ggQ2xD5e_exists_prod_applyWord
    (A : Subgroup (GGBCV 5 ≃ₗ[ZMod 3] GGBCV 5)) (word : List (List ℕ))
    (hcent : ∀ z ∈ word, ggQ2xD5e_vec z ∈ ggQ2xD5_Z A) :
    ∃ r ∈ reflGp A, ∀ w, r w = ggQ2xD5e_applyWord word w := by
  induction word with
  | nil => exact ⟨1, Subgroup.one_mem _, fun w => rfl⟩
  | cons z zs ih =>
      have hz : ggQ2xD5e_vec z ∈ ggQ2xD5_Z A := hcent z (by simp)
      obtain ⟨hzn, hzA⟩ := hz
      obtain ⟨r', hr', hr'w⟩ := ih (fun y hy => hcent y (by simp [hy]))
      have hsR : IsReflLin (ggBCRefl (ggQ2xD5e_vec z) hzn) := ggQ2xD5e_isReflLin_bc _ hzn
      have hs : ggBCRefl (ggQ2xD5e_vec z) hzn ∈ reflGp A :=
        Subgroup.subset_closure ⟨hzA, hsR⟩
      refine ⟨r' * ggBCRefl (ggQ2xD5e_vec z) hzn, mul_mem hr' hs, fun w => ?_⟩
      rw [LinearEquiv.mul_apply, hr'w (ggBCRefl (ggQ2xD5e_vec z) hzn w),
        ggQ2x_ggBCRefl_apply]
      rfl

private theorem ggQ2xD5_case_E6 (A : Subgroup (GGBCV 5 ≃ₗ[ZMod 3] GGBCV 5))
    (hW : ggBCReflGp (ggDRoots 5) ≤ A)
    (hS1 : ∀ (c : GGBCV 5) (φ : Module.Dual (ZMod 3) (GGBCV 5)) (h : φ c = 2),
      Module.reflection h ∈ A → ∃ ε : ZMod 3, (ε = 1 ∨ ε = -1) ∧ ∀ v, φ v = ε * (c ⬝ᵥ v))
    (hZ : ggQ2xD5_Z A = ggDRoots 5 ∪ {z | ggBCWt z = 5}) :
    ∀ a ∈ A, ∃ r ∈ reflGp A, Submodule.span (ZMod 3) {a (Pi.single 0 1 : GGBCV 5)} =
      Submodule.span (ZMod 3) {r (Pi.single 0 1 : GGBCV 5)} := by
  intro a ha
  have hnorm : (a (Pi.single 0 1 : GGBCV 5)) ⬝ᵥ (a (Pi.single 0 1 : GGBCV 5)) = 1 := by
    rw [ggQ2xD5_isometry A hW hS1 a ha (Pi.single 0 1) (Pi.single 0 1),
      ggQ2x_dot_self_eq_wt, ggQ2x_wt_single, Nat.cast_one]
  have hwt3 : (ggBCWt (a (Pi.single 0 1 : GGBCV 5)) : ZMod 3) = 1 := by
    rw [← ggQ2x_dot_self_eq_wt]
    exact hnorm
  have hwtle : ggBCWt (a (Pi.single 0 1 : GGBCV 5)) ≤ 5 := by
    unfold ggBCWt
    calc (Finset.univ.filter fun i => (a (Pi.single 0 1 : GGBCV 5)) i ≠ 0).card
        ≤ (Finset.univ : Finset (Fin 5)).card := Finset.card_filter_le _ _
      _ = 5 := by simp
  rcases ggQ2xD5e_wt_eq_one_or_four hwtle hwt3 with hwt1 | hwt4
  · exact ggQ2xD5_wt1 A hW (a (Pi.single 0 1)) hwt1
  · obtain ⟨row, -, -, hrow2, hrow3⟩ := ggQ2xD5e_table (a (Pi.single 0 1)) hwt4
    have hcent : ∀ z ∈ row.2, ggQ2xD5e_vec z ∈ ggQ2xD5_Z A := by
      intro z hz
      rcases hrow2 z hz with h2 | h5
      · rw [hZ]; exact Or.inl h2
      · rw [hZ]; exact Or.inr h5
    obtain ⟨r, hr, hrw⟩ := ggQ2xD5e_exists_prod_applyWord A row.2 hcent
    refine ⟨r, hr, ?_⟩
    rw [hrw (Pi.single 0 1)]
    rcases hrow3 with happ | happ
    · rw [happ]
    · rw [happ]
      have hneg : Submodule.span (ZMod 3)
          ({- (a (Pi.single 0 1 : GGBCV 5))} : Set (GGBCV 5)) =
          Submodule.span (ZMod 3) {a (Pi.single 0 1 : GGBCV 5)} := by
        simpa using Submodule.span_neg ({a (Pi.single 0 1 : GGBCV 5)} : Set (GGBCV 5))
      exact hneg.symm

private theorem ggQ2xD5_core (A : Subgroup (GGBCV 5 ≃ₗ[ZMod 3] GGBCV 5))
    (hW : ggBCReflGp (ggDRoots 5) ≤ A)
    (hS1 : ∀ (c : GGBCV 5) (φ : Module.Dual (ZMod 3) (GGBCV 5)) (h : φ c = 2),
      Module.reflection h ∈ A → ∃ ε : ZMod 3, (ε = 1 ∨ ε = -1) ∧ ∀ v, φ v = ε * (c ⬝ᵥ v)) :
    ∀ a ∈ A, ∃ r ∈ reflGp A, Submodule.span (ZMod 3) {a (Pi.single 0 1 : GGBCV 5)} =
      Submodule.span (ZMod 3) {r (Pi.single 0 1 : GGBCV 5)} := by
  have hZ0 := ggQ2xD5_Z0 A
  have hZroots := ggQ2xD5_Zroots A hW
  have hZcl : ∀ z ∈ ggQ2xD5_Z A, ∀ w ∈ ggQ2xD5_Z A, ∀ hz : z ⬝ᵥ z ≠ 0,
      ggBCRefl z hz w ∈ ggQ2xD5_Z A := by
    intro z hz w hw hz0
    have hzA : ggBCRefl z hz0 ∈ A := by
      obtain ⟨hz1, hzA⟩ := hz
      rwa [show ggBCRefl z hz0 = ggBCRefl z hz1 from rfl]
    exact ggQ2xD5_perm A hS1 _ hzA w hw
  rcases ggQ2xD5_Z_cases _ hZ0 hZroots hZcl with hZ | hZ | hZ | hZ
  · exact ggQ2xD5_case_Phi A hW hS1 hZ
  · exact ggQ2xD5_case_B A hW hS1 hZ
  · exact ggQ2xD5_case_E6 A hW hS1 hZ
  · exact ggQ2xD5_case_all A hW hS1 hZ

theorem ggQ2_thmB_D5 (D : GGQ2Lin 3) (hbas : D.Basis) (e : Fin 5 ≃ D.ι)
    (hD : D.coxeter = (ggCoxeterMatrixD 5).reindex e) (ha : D.a = e 0) (x : D.V)
    (hx : ∀ v, (∀ g ∈ D.parab {k | k ≠ D.a}, g v = v) ↔ v ∈ Submodule.span (ZMod 3) {x})
    (A : Subgroup (D.V ≃ₗ[ZMod 3] D.V)) (hW : D.weyl ≤ A) (hTF : TransvectionFree A) :
    ∀ φ ∈ A, ∃ r ∈ reflGp A,
      Submodule.span (ZMod 3) {φ x} = Submodule.span (ZMod 3) {r x} := by
  obtain ⟨τ, hτ, hroot⟩ := ggQ2_D_coordinates (p := 3) (by decide) D hbas (by omega) e hD
  have hW' : ggBCReflGp (ggDRoots 5) ≤ A.map (ggLinConj τ).toMonoidHom :=
    ggQ2_DW_Droots_le_map D hbas (by omega) e hD τ hτ hroot A hW
  have hS1 := ggQ2xD5_S1 D hbas e hD A hW hTF τ hτ hroot
  have hx' := ggQ2xD5_tau_x D e hD ha x hx τ hτ hroot
  have hcore := ggQ2xD5_core _ hW' hS1
  refine (ggLinConj_P3 τ A x).mp ?_
  intro φ' hφ'
  obtain ⟨r', hr', hspan⟩ := hcore φ' hφ'
  refine ⟨r', hr', ?_⟩
  have key : ∀ g : GGBCV 5 ≃ₗ[ZMod 3] GGBCV 5, Submodule.span (ZMod 3) {g (τ x)} =
      Submodule.span (ZMod 3) {g (Pi.single 0 1 : GGBCV 5)} := by
    intro g
    have h := congrArg (Submodule.map (g : GGBCV 5 →ₗ[ZMod 3] GGBCV 5)) hx'
    simpa [Submodule.map_span, Set.image_singleton] using h
  rw [key φ', key r']
  exact hspan

end CFSG.StandardType

end
