module

public import CFSG.LieType.SeitzGeneration.UnitaryCenters
public import CFSG.LocalAnalysis.WeakClosure81.Asc80BOddPSUOuterAntiFrame

public section

namespace CFSG.LocalAnalysis.WeakClosure81.UOuter

open Matrix CFSG.LieType.Universal.Unitary CFSG.ClassicalGroups.Unitary
  CFSG.LieType.SeitzGeneration.Centers

variable {K : Type} [Field K] {σ : K ≃+* K}

private noncomputable def eich (hσ : IsUnitaryInvolution σ) {e y : Fin 4 → K}
    (he : herm σ e e = 0) (hy : herm σ y y = 0) (hey : herm σ e y = 0) : SUid σ 4 :=
  eichler hσ.invol he hey (by rw [zero_add, map_zero, hy, neg_zero])

private theorem eich_smul (hσ : IsUnitaryInvolution σ) {e y : Fin 4 → K}
    (he : herm σ e e = 0) (hy : herm σ y y = 0) (hey : herm σ e y = 0) (x : Fin 4 → K) :
    eich hσ he hy hey • x = x + herm σ e x • y - herm σ y x • e := by
  simpa [eich] using
    eichler_smul (c := 0) hσ.invol he hey (by rw [zero_add, map_zero, hy, neg_zero]) x

private theorem eich_mem {A : Matrix (Fin 4) (Fin 4) K} {H : Subgroup (SUid σ 4)} {l ε : K}
    (hσ : IsUnitaryInvolution σ) (hl : σ l * l = -1) (hε : ε = l ∨ ε = -l)
    (hAu : (A.map σ)ᵀ * A = 1)
    (hin : ∀ g : SUid σ 4, A * ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
      ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) * A → g ∈ H)
    {e y : Fin 4 → K} (he : herm σ e e = 0) (hy : herm σ y y = 0)
    (hey : herm σ e y = 0) (heig : A *ᵥ e = ε • e) (hyeig : A *ᵥ y = (-ε) • y) :
    eich hσ he hy hey ∈ H := by
  refine hin _ ?_
  have h := eichlerMat_comm_of_eigen hσ.invol hl hε hAu he heig hyeig
  simpa [eich, eichler, mkSU] using h

private theorem mulVec_smul_eigen {A : Matrix (Fin 4) (Fin 4) K} {v : Fin 4 → K} {μ : K}
    (c : K) (h : A *ᵥ v = μ • v) : A *ᵥ (c • v) = μ • (c • v) := by
  rw [Matrix.mulVec_smul, h]
  exact smul_comm c μ v

theorem eq_top_of_antiFrame (hσ : IsUnitaryInvolution σ) {H : Subgroup (SUid σ 4)}
    {A A' : Matrix (Fin 4) (Fin 4) K} {l : K} (hl : σ l * l = -1)
    (hAu : (A.map σ)ᵀ * A = 1) (hA'u : (A'.map σ)ᵀ * A' = 1) {f₁ f₂ g₁ g₂ : Fin 4 → K}
    (F : AntiFrame σ A A' l f₁ f₂ g₁ g₂)
    (hH : ∀ g : SUid σ 4,
      (A * ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) = (g : GL (Fin 4) K) * A ∨
        A' * ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) = (g : GL (Fin 4) K) * A') →
      g ∈ H)
    (hf₁ : IsCenter H f₁) :
    H = ⊤ := by
  classical
  have hg1f1 : herm σ g₁ f₁ = 1 := by
    rw [herm_conj σ hσ.invol f₁ g₁, F.f₁g₁, map_one]
  have hg2f2 : herm σ g₂ f₂ = 1 := by
    rw [herm_conj σ hσ.invol f₂ g₂, F.f₂g₂, map_one]
  have hf2f1 : herm σ f₂ f₁ = 0 := herm_eq_zero_comm σ hσ.invol F.f₁f₂
  have hg2f1 : herm σ g₂ f₁ = 0 := herm_eq_zero_comm σ hσ.invol F.f₁g₂
  have hg1f2 : herm σ g₁ f₂ = 0 := herm_eq_zero_comm σ hσ.invol F.f₂g₁
  have hg2g1 : herm σ g₂ g₁ = 0 := herm_eq_zero_comm σ hσ.invol F.g₁g₂
  have hinA : ∀ g : SUid σ 4, A * ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
      ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) * A → g ∈ H :=
    fun g hg => hH g (Or.inl hg)
  have hinA' : ∀ g : SUid σ 4, A' * ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
      ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) * A' → g ∈ H :=
    fun g hg => hH g (Or.inr hg)
  have hmA (c : K) :
      eich hσ F.f₂f₂ (y := c • g₁) (by simp [F.g₁g₁]) (by simp [F.f₂g₁]) ∈ H :=
    eich_mem (H := H) (y := c • g₁) hσ hl (Or.inl rfl) hAu hinA F.f₂f₂
      (by simp [F.g₁g₁]) (by simp [F.f₂g₁]) F.af₂ (mulVec_smul_eigen c F.ag₁)
  have hactA (c : K) :
      eich hσ F.f₂f₂ (y := c • g₁) (by simp [F.g₁g₁]) (by simp [F.f₂g₁]) • f₁
        = f₁ - σ c • f₂ := by
    rw [eich_smul (y := c • g₁) hσ F.f₂f₂ (by simp [F.g₁g₁]) (by simp [F.f₂g₁]) f₁]
    simp [hf2f1, hg1f1]
  have hmB (c : K) :
      eich hσ F.f₁f₁ (y := c • g₂) (by simp [F.g₂g₂]) (by simp [F.f₁g₂]) ∈ H :=
    eich_mem (H := H) (y := c • g₂) hσ hl (Or.inl rfl) hAu hinA F.f₁f₁
      (by simp [F.g₂g₂]) (by simp [F.f₁g₂]) F.af₁ (mulVec_smul_eigen c F.ag₂)
  have hactB1 (c : K) :
      eich hσ F.f₁f₁ (y := c • g₂) (by simp [F.g₂g₂]) (by simp [F.f₁g₂]) • f₁ = f₁ := by
    rw [eich_smul (y := c • g₂) hσ F.f₁f₁ (by simp [F.g₂g₂]) (by simp [F.f₁g₂]) f₁]
    simp [F.f₁f₁, hg2f1]
  have hactB2 (c : K) :
      eich hσ F.f₁f₁ (y := c • g₂) (by simp [F.g₂g₂]) (by simp [F.f₁g₂]) • f₂
        = f₂ - σ c • f₁ := by
    rw [eich_smul (y := c • g₂) hσ F.f₁f₁ (by simp [F.g₂g₂]) (by simp [F.f₁g₂]) f₂]
    simp [F.f₁f₂, hg2f2]
  have hmC (c : K) :
      eich hσ F.g₂g₂ (y := c • g₁) (by simp [F.g₁g₁]) (by simp [hg2g1]) ∈ H :=
    eich_mem (H := H) (y := c • g₁) hσ hl (Or.inl rfl) hA'u hinA' F.g₂g₂
      (by simp [F.g₁g₁]) (by simp [hg2g1]) F.bg₂ (mulVec_smul_eigen c F.bg₁)
  have hactC (c : K) :
      eich hσ F.g₂g₂ (y := c • g₁) (by simp [F.g₁g₁]) (by simp [hg2g1]) • f₁
        = f₁ - σ c • g₂ := by
    rw [eich_smul (y := c • g₁) hσ F.g₂g₂ (by simp [F.g₁g₁]) (by simp [hg2g1]) f₁]
    simp [hg2f1, hg1f1]
  have hmD (c : K) :
      eich hσ F.f₁f₁ (y := c • f₂) (by simp [F.f₂f₂]) (by simp [F.f₁f₂]) ∈ H :=
    eich_mem (H := H) (y := c • f₂) hσ hl (Or.inl rfl) hA'u hinA' F.f₁f₁
      (by simp [F.f₂f₂]) (by simp [F.f₁f₂]) F.bf₁ (mulVec_smul_eigen c F.bf₂)
  have hactD1 (c : K) :
      eich hσ F.f₁f₁ (y := c • f₂) (by simp [F.f₂f₂]) (by simp [F.f₁f₂]) • f₁ = f₁ := by
    rw [eich_smul (y := c • f₂) hσ F.f₁f₁ (by simp [F.f₂f₂]) (by simp [F.f₁f₂]) f₁]
    simp [F.f₁f₁, hf2f1]
  have hactD2 (c : K) :
      eich hσ F.f₁f₁ (y := c • f₂) (by simp [F.f₂f₂]) (by simp [F.f₁f₂]) • g₂
        = g₂ - σ c • f₁ := by
    rw [eich_smul (y := c • f₂) hσ F.f₁f₁ (by simp [F.f₂f₂]) (by simp [F.f₁f₂]) g₂]
    simp [F.f₁g₂, F.f₂g₂]
  have hmE (c : K) :
      eich hσ F.g₁g₁ (y := c • f₂) (by simp [F.f₂f₂]) (by simp [hg1f2]) ∈ H :=
    eich_mem (H := H) (y := c • f₂) hσ hl (Or.inr rfl) hAu hinA F.g₁g₁
      (by simp [F.f₂f₂]) (by simp [hg1f2]) F.ag₁ (by simpa using mulVec_smul_eigen c F.af₂)
  have hactE (c : K) :
      eich hσ F.g₁g₁ (y := c • f₂) (by simp [F.f₂f₂]) (by simp [hg1f2]) • g₂
        = g₂ - σ c • g₁ := by
    rw [eich_smul (y := c • f₂) hσ F.g₁g₁ (by simp [F.f₂f₂]) (by simp [hg1f2]) g₂]
    simp [F.g₁g₂, F.f₂g₂]
  have hmF (c : K) :
      eich hσ F.g₂g₂ (y := c • f₁) (by simp [F.f₁f₁]) (by simp [hg2f1]) ∈ H :=
    eich_mem (H := H) (y := c • f₁) hσ hl (Or.inr rfl) hAu hinA F.g₂g₂
      (by simp [F.f₁f₁]) (by simp [hg2f1]) F.ag₂ (by simpa using mulVec_smul_eigen c F.af₁)
  have hactF1 (c : K) :
      eich hσ F.g₂g₂ (y := c • f₁) (by simp [F.f₁f₁]) (by simp [hg2f1]) • g₂ = g₂ := by
    rw [eich_smul (y := c • f₁) hσ F.g₂g₂ (by simp [F.f₁f₁]) (by simp [hg2f1]) g₂]
    simp [F.g₂g₂, F.f₁g₂]
  have hactF2 (c : K) :
      eich hσ F.g₂g₂ (y := c • f₁) (by simp [F.f₁f₁]) (by simp [hg2f1]) • g₁
        = g₁ - σ c • g₂ := by
    rw [eich_smul (y := c • f₁) hσ F.g₂g₂ (by simp [F.f₁f₁]) (by simp [hg2f1]) g₁]
    simp [hg2g1, F.f₁g₁]
  have hf12 : IsCenter H (f₁ + f₂) := by
    have h := hf₁.map (hmA (-1))
    rw [hactA (-1)] at h
    simpa using h
  have hf2 : IsCenter H f₂ := by
    have h := hf12.map (hmB 1)
    rw [smul_add, hactB1 1, hactB2 1] at h
    have hv : f₁ + (f₂ - σ (1 : K) • f₁) = f₂ := by
      rw [map_one]
      module
    rwa [hv] at h
  have hfg2 : IsCenter H (f₁ + g₂) := by
    have h := hf₁.map (hmC (-1))
    rw [hactC (-1)] at h
    simpa using h
  have hg2 : IsCenter H g₂ := by
    have h := hfg2.map (hmD 1)
    rw [smul_add, hactD1 1, hactD2 1] at h
    have hv : f₁ + (g₂ - σ (1 : K) • f₁) = g₂ := by
      rw [map_one]
      module
    rwa [hv] at h
  have hg21 : IsCenter H (g₂ + g₁) := by
    have h := hg2.map (hmE (-1))
    rw [hactE (-1)] at h
    simpa using h
  have hg1 : IsCenter H g₁ := by
    have h := hg21.map (hmF 1)
    rw [smul_add, hactF1 1, hactF2 1] at h
    have hv : g₂ + (g₁ - σ (1 : K) • g₂) = g₁ := by
      rw [map_one]
      module
    rwa [hv] at h
  have hplus : ∀ β : K, IsCenter H (f₁ + β • f₂) := by
    intro β
    have h := hf₁.map (hmA (-(σ β)))
    rw [hactA (-(σ β))] at h
    have hs : σ (-(σ β)) = -β := by rw [map_neg, hσ.invol]
    rw [hs] at h
    simpa using h
  have hshift : ∀ β : K, IsCenter H (g₂ + β • g₁) := by
    intro β
    have h := hg2.map (hmE (-(σ β)))
    rw [hactE (-(σ β))] at h
    have hs : σ (-(σ β)) = -β := by rw [map_neg, hσ.invol]
    rw [hs] at h
    simpa using h
  have hvf : ∀ a b : K, IsCenter H (a • f₁ + b • f₂) := by
    intro a b
    by_cases ha : a = 0
    · rw [ha, zero_smul, zero_add]
      simpa using IsCenter.smul hσ.invol hf2 b
    · have h := IsCenter.smul hσ.invol (hplus (a⁻¹ * b)) a
      have hv : a • (f₁ + (a⁻¹ * b) • f₂) = a • f₁ + b • f₂ := by
        rw [smul_add, smul_smul, ← mul_assoc, mul_inv_cancel₀ ha, one_mul]
      rwa [hv] at h
  have hvg : ∀ a b : K, IsCenter H (a • g₁ + b • g₂) := by
    intro a b
    by_cases hb : b = 0
    · rw [hb, zero_smul, add_zero]
      simpa using IsCenter.smul hσ.invol hg1 a
    · have h := IsCenter.smul hσ.invol (hshift (b⁻¹ * a)) b
      have hv : b • (g₂ + (b⁻¹ * a) • g₁) = a • g₁ + b • g₂ := by
        rw [smul_add, smul_smul, ← mul_assoc, mul_inv_cancel₀ hb, one_mul, add_comm]
      rwa [hv] at h
  refine eq_top_of_forall_isCenter hσ (by norm_num) (fun h => absurd h (by norm_num)) ?_
  intro v hvv
  obtain ⟨a, b, c, d, hvdecomp⟩ := F.span v
  set vp : Fin 4 → K := a • f₁ + b • f₂ with hvp
  set vm : Fin 4 → K := c • g₁ + d • g₂ with hvm
  have hvsum : v = vp + vm := by
    rw [hvdecomp, hvp, hvm]
    module
  have hvp_center : IsCenter H vp := by rw [hvp]; exact hvf a b
  have hvm_center : IsCenter H vm := by rw [hvm]; exact hvg c d
  by_cases hvm0 : vm = 0
  · have hv_eq : v = vp := by rw [hvsum, hvm0, add_zero]
    rw [hv_eq]
    exact hvp_center
  · by_cases hvp0 : vp = 0
    · have hv_eq : v = vm := by rw [hvsum, hvp0, zero_add]
      rw [hv_eq]
      exact hvm_center
    · by_cases hzero : herm σ vm vp = 0
      ·
        have hpick : herm σ f₁ vm ≠ 0 ∨ herm σ f₂ vm ≠ 0 := by
          by_contra h
          push Not at h
          have h1 : herm σ f₁ vm = c := by
            rw [hvm]
            simp [F.f₁g₁, F.f₁g₂]
          have h2 : herm σ f₂ vm = d := by
            rw [hvm]
            simp [F.f₂g₁, F.f₂g₂]
          have hc0 : c = 0 := by rw [← h1]; exact h.1
          have hd0 : d = 0 := by rw [← h2]; exact h.2
          exact hvm0 (by rw [hvm, hc0, hd0, zero_smul, zero_smul, add_zero])
        obtain ⟨e, hee, hX⟩ : ∃ e : Fin 4 → K,
            (e = f₁ ∨ e = f₂) ∧ herm σ e vm ≠ 0 := by
          rcases hpick with h | h
          · exact ⟨f₁, Or.inl rfl, h⟩
          · exact ⟨f₂, Or.inr rfl, h⟩
        obtain ⟨τ, hτ0, hτ⟩ := hσ.exists_traceZero
        have hτ' : σ τ = -τ := by linear_combination hτ
        have h_e_vp : herm σ e vp = 0 := by
          rcases hee with h | h
          · rw [h, hvp]; simp [F.f₁f₁, F.f₁f₂]
          · rw [h, hvp]; simp [hf2f1, F.f₂f₂]
        have he_iso : herm σ e e = 0 := by
          rcases hee with h | h
          · rw [h]; simp [F.f₁f₁]
          · rw [h]; simp [F.f₂f₂]
        have hev : herm σ e v = herm σ e vm := by
          rw [hvsum, herm_add_right, h_e_vp, zero_add]
        set wp : Fin 4 → K := vp + (τ * herm σ e vm) • e with hwp
        set w : Fin 4 → K := v + (τ * herm σ e v) • e with hw
        have hw_eq : w = wp + vm := by
          rw [hw, hwp, ← hev, hvsum]
          module
        have hwp_center : IsCenter H wp := by
          rcases hee with h | h
          · have hwp' : wp = (a + τ * herm σ f₁ vm) • f₁ + b • f₂ := by
              rw [hwp, h, hvp]
              module
            rw [hwp']
            exact hvf _ _
          · have hwp' : wp = a • f₁ + (b + τ * herm σ f₂ vm) • f₂ := by
              rw [hwp, h, hvp]
              module
            rw [hwp']
            exact hvf _ _
        have hne' : herm σ vm wp ≠ 0 := by
          rw [hwp, herm_add_right, hzero, zero_add, herm_smul_right,
            herm_conj σ hσ.invol e vm]
          exact mul_ne_zero (mul_ne_zero hτ0 hX) ((map_ne_zero σ).mpr hX)
        have hw_iso : herm σ w w = 0 := by
          have hwtv : w = tv hσ.invol he_iso hτ • v := by
            rw [hw, tv_smul]
          rw [hwtv, herm_smul_smul, hvv]
        have hw_center : IsCenter H w := by
          have hiso : herm σ (wp + vm) (wp + vm) = 0 := by
            rw [← hw_eq]
            exact hw_iso
          have h := IsCenter.add hσ.invol hwp_center hvm_center hiso hne'
          rwa [← hw_eq] at h
        have hcenter : IsCenter H (w + ((-τ) * herm σ e w) • e) := by
          refine IsCenter.move ?_ hw_center ?_
          · rcases hee with h | h
            · rw [h]; exact hf₁
            · rw [h]; exact hf2
          · rw [map_neg, hτ']
            ring
        have hEq : w + ((-τ) * herm σ e w) • e = v := by
          have hew : herm σ e w = herm σ e v := by
            rw [hw, herm_add_right, herm_smul_right]
            simp [he_iso]
          rw [hew, hw, add_assoc, ← add_smul,
            show τ * herm σ e v + (-τ) * herm σ e v = 0 by ring, zero_smul, add_zero]
        rw [hEq] at hcenter
        exact hcenter
      · rw [hvsum]
        refine IsCenter.add hσ.invol hvp_center hvm_center ?_ hzero
        rw [← hvsum]
        exact hvv

end CFSG.LocalAnalysis.WeakClosure81.UOuter
