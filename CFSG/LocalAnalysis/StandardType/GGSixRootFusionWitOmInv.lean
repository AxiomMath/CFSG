module

public import CFSG.LocalAnalysis.StandardType.GGTableBOrthogonalDiag
public import CFSG.RankThree.OrthogonalInvolutions.Dickson
public import CFSG.LieType.SeitzGeneration.OrthEvenSingular
public import CFSG.RankThree.PartOne.S11d.OrthDicksonOmega

public section

namespace CFSG.StandardType

namespace WitOm

open Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions TableBOrth

variable {K : Type} [Field K] [CharP K 2] {V : Type} [AddCommGroup V] [Module K V]
  {Q : QuadraticForm K V} {t : V ≃ₗ[K] V}

section Moving

theorem apply_sub_eq (htt : t * t = 1) (x : V) : t (t x - x) = t x - x :=
  mem_fixSpace.mp (commSpace_le_fixSpace htt (sub_mem_commSpace t x))

theorem wallForm_sub_right (htt : t * t = 1) (x z : V) : wallForm Q t x (t z - z) = 0 := by
  rw [wallForm_apply, apply_sub_eq htt, sub_self, polar_zero_right]

theorem wallForm_sub_left (hO : t ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (htt : t * t = 1)
    (x z : V) : wallForm Q t (t z - z) x = 0 := by
  rw [wallForm_symm hO htt, wallForm_sub_right htt]

theorem map_add_sub (hO : t ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (x z : V) :
    Q (x + (t z - z)) = Q x + wallForm Q t z z + wallForm Q t x z := by
  rw [map_add_eq, wallForm_self hO, wallForm_apply]

theorem wallForm_add_sub (hO : t ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (htt : t * t = 1)
    (x y z w : V) : wallForm Q t (x + (t z - z)) (y + (t w - w)) = wallForm Q t x y := by
  simp only [map_add, LinearMap.add_apply, wallForm_sub_right htt, wallForm_sub_left hO htt,
    add_zero]

theorem exists_hypFamily_of_wall (hO : t ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    (htt : t * t = 1) {f₁ f₂ : V} (h₁ : wallForm Q t f₁ f₁ = 0) (h₂ : wallForm Q t f₂ f₂ = 0)
    (h₁₂ : wallForm Q t f₁ f₂ = 1) :
    ∃ e f : Fin 2 → V, IsHypFamily Q e f ∧ t (e 0) = e 0 ∧ t (e 1) = e 1 + e 0 ∧
      t (f 0) = f 0 + f 1 ∧ t (f 1) = f 1 := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have h₂₁ : wallForm Q t f₂ f₁ = 1 := by rw [wallForm_symm hO htt, h₁₂]
  set z₁ : V := Q f₁ • f₂ + polar Q f₁ f₂ • f₁ with hz₁
  set z₂ : V := Q f₂ • f₁ with hz₂
  set g₁ : V := f₁ + (t z₁ - z₁) with hg₁
  set g₂ : V := f₂ + (t z₂ - z₂) with hg₂
  have hβz₁ : wallForm Q t z₁ z₁ = 0 := by
    simp only [hz₁, map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
      h₁, h₂, h₁₂, h₂₁]
    linear_combination (Q f₁ * polar Q f₁ f₂) * h2
  have hβz₂ : wallForm Q t z₂ z₂ = 0 := by
    simp only [hz₂, map_smul, LinearMap.smul_apply, smul_eq_mul, h₁, mul_zero]
  have hQg₁ : Q g₁ = 0 := by
    rw [hg₁, map_add_sub hO, hβz₁, hz₁]
    simp only [map_add, map_smul, smul_eq_mul, h₁, h₁₂]
    linear_combination Q f₁ * h2
  have hQg₂ : Q g₂ = 0 := by
    rw [hg₂, map_add_sub hO, hβz₂, hz₂]
    simp only [map_smul, smul_eq_mul, h₂₁]
    linear_combination Q f₂ * h2
  have hpg : polar Q g₁ g₂ = 0 := by
    rw [hg₁, hg₂, polar_add_left, polar_add_right, polar_add_right,
      polar_commSpace_eq_zero hO htt (sub_mem_commSpace t z₁) (sub_mem_commSpace t z₂),
      polar_comm Q (t z₁ - z₁) f₂, ← wallForm_apply, ← wallForm_apply, hz₁, hz₂]
    simp only [map_add, map_smul, smul_eq_mul, h₁, h₂, h₂₁]
    linear_combination polar Q f₁ f₂ * h2
  have hβ₁ : wallForm Q t g₁ g₁ = 0 := by rw [hg₁, wallForm_add_sub hO htt, h₁]
  have hβ₂ : wallForm Q t g₂ g₂ = 0 := by rw [hg₂, wallForm_add_sub hO htt, h₂]
  have hβ₁₂ : wallForm Q t g₁ g₂ = 1 := by rw [hg₁, hg₂, wallForm_add_sub hO htt, h₁₂]
  have hβ₂₁ : wallForm Q t g₂ g₁ = 1 := by rw [wallForm_symm hO htt, hβ₁₂]
  refine ⟨![t g₂ - g₂, g₂], ![g₁, t g₁ - g₁], ⟨fun k => ?_, fun k => ?_, fun i j => ?_,
    fun i j => ?_, fun i j => ?_⟩, ?_, ?_, ?_, ?_⟩
  · fin_cases k
    · simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero]
      rw [← wallForm_self hO, hβ₂]
    · exact hQg₂
  · fin_cases k
    · exact hQg₁
    · simp only [Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_zero]
      rw [← wallForm_self hO, hβ₁]
  · fin_cases i <;> fin_cases j <;>
      simp only [Fin.zero_eta, Fin.mk_one, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one]
    · exact polar_commSpace_eq_zero hO htt (sub_mem_commSpace t g₂) (sub_mem_commSpace t g₂)
    · rw [polar_comm, ← wallForm_apply, hβ₂]
    · rw [← wallForm_apply, hβ₂]
    · exact polar_self_eq_zero Q g₂
  · fin_cases i <;> fin_cases j <;>
      simp only [Fin.zero_eta, Fin.mk_one, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one]
    · exact polar_self_eq_zero Q g₁
    · rw [← wallForm_apply, hβ₁]
    · rw [polar_comm, ← wallForm_apply, hβ₁]
    · exact polar_commSpace_eq_zero hO htt (sub_mem_commSpace t g₁) (sub_mem_commSpace t g₁)
  · fin_cases i <;> fin_cases j <;>
      simp only [Fin.zero_eta, Fin.mk_one, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one,
        ite_true, Fin.reduceEq, ite_false]
    · rw [polar_comm, ← wallForm_apply, hβ₁₂]
    · exact polar_commSpace_eq_zero hO htt (sub_mem_commSpace t g₂) (sub_mem_commSpace t g₁)
    · rw [polar_comm, hpg]
    · rw [← wallForm_apply, hβ₂₁]
  · exact apply_sub_eq htt g₂
  · simp only [Matrix.cons_val_one, Matrix.cons_val_zero]
    abel
  · simp only [Matrix.cons_val_one, Matrix.cons_val_zero]
    abel
  · exact apply_sub_eq htt g₁

end Moving

section Pair

omit [CharP K 2] in
theorem exists_wall_pair_of_alt (hQ : Q.polarBilin.Nondegenerate)
    (hO : t ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (htt : t * t = 1) (ht1 : t ≠ 1)
    (halt : ∀ x, wallForm Q t x x = 0) :
    ∃ f₁ f₂ : V, wallForm Q t f₁ f₁ = 0 ∧ wallForm Q t f₂ f₂ = 0 ∧ wallForm Q t f₁ f₂ = 1 := by
  obtain ⟨x, y, hxy⟩ : ∃ x y, wallForm Q t x y ≠ 0 := by
    by_contra h
    push Not at h
    apply ht1
    refine LinearEquiv.ext fun y => ?_
    rw [mem_fixSpace.mp (mem_fixSpace_of_wallForm hQ hO htt (h y)), LinearEquiv.coe_one, id]
  refine ⟨x, (wallForm Q t x y)⁻¹ • y, halt x, halt _, ?_⟩
  rw [map_smul, smul_eq_mul, inv_mul_cancel₀ hxy]

theorem wallForm_add_add (hO : t ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (htt : t * t = 1)
    (x y : V) : wallForm Q t (x + y) (x + y) = wallForm Q t x x + wallForm Q t y y := by
  simp only [map_add, LinearMap.add_apply]
  rw [wallForm_symm hO htt y x]
  linear_combination (wallForm Q t x y) * (CharTwo.two_eq_zero : (2 : K) = 0)

theorem exists_wall_pair_of_three [FiniteDimensional K V] [Finite K]
    (hQ : Q.polarBilin.Nondegenerate) (hO : t ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    (htt : t * t = 1) {x₀ : V} (hx₀ : wallForm Q t x₀ x₀ ≠ 0)
    (h3 : 3 ≤ finrank K (commSpace t)) :
    ∃ f₁ f₂ : V, wallForm Q t f₁ f₁ = 0 ∧ wallForm Q t f₂ f₂ = 0 ∧ wallForm Q t f₁ f₂ = 1 := by
  let H : Submodule K V :=
    { carrier := {x | wallForm Q t x x = 0}
      add_mem' := fun {x y} hx hy => by
        simp only [Set.mem_ofPred_eq] at hx hy ⊢
        rw [wallForm_add_add hO htt, hx, hy, add_zero]
      zero_mem' := by simp
      smul_mem' := fun c x hx => by
        simp only [Set.mem_ofPred_eq] at hx ⊢
        simp only [map_smul, LinearMap.smul_apply, smul_eq_mul, hx, mul_zero] }
  have hH : ∀ x, x ∈ H ↔ wallForm Q t x x = 0 := fun x => Iff.rfl
  by_contra hcon
  have hzero : ∀ x ∈ H, ∀ y ∈ H, wallForm Q t x y = 0 := by
    intro x hx y hy
    by_contra hxy
    refine hcon ⟨x, (wallForm Q t x y)⁻¹ • y, (hH x).mp hx, ?_, ?_⟩
    · exact (hH _).mp (H.smul_mem _ hy)
    · rw [map_smul, smul_eq_mul, inv_mul_cancel₀ hxy]
  have hsup : H ⊔ Submodule.span K {x₀} = ⊤ := by
    rw [eq_top_iff]
    intro x _
    obtain ⟨c, hc⟩ := isSquare_of_charTwo' (wallForm Q t x x / wallForm Q t x₀ x₀)
    have hmem : x + c • x₀ ∈ H := by
      rw [hH, wallForm_add_add hO htt]
      simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
      rw [← mul_assoc, ← hc, div_mul_cancel₀ _ hx₀]
      linear_combination (wallForm Q t x x) * (CharTwo.two_eq_zero : (2 : K) = 0)
    refine Submodule.mem_sup.mpr ⟨x + c • x₀, hmem, (-c) • x₀,
      Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self x₀), ?_⟩
    rw [neg_smul, add_neg_cancel_right]
  have hspan : finrank K (Submodule.span K {x₀}) ≤ 1 := by
    have := finrank_span_finset_le_card (R := K) ({x₀} : Finset V)
    rwa [Finset.coe_singleton, Finset.card_singleton] at this
  have hVH : finrank K V ≤ finrank K H + 1 := by
    have h1 := Submodule.finrank_add_le_finrank_add_finrank H (Submodule.span K {x₀})
    rw [hsup, finrank_top] at h1
    omega
  set N : V →ₗ[K] V := (t : V →ₗ[K] V) - 1 with hN
  have hNH : H.map N ≤ LinearMap.BilinForm.orthogonal Q.polarBilin H := by
    rintro _ ⟨z, hz, rfl⟩
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    intro y hy
    change polar Q y (t z - z) = 0
    rw [← wallForm_apply]
    exact hzero y hy z hz
  have h1 := Submodule.finrank_mono hNH
  rw [LinearMap.BilinForm.finrank_orthogonal hQ] at h1
  have hcomm : commSpace t ≤ H.map N ⊔ (Submodule.span K {x₀}).map N := by
    rw [← Submodule.map_sup, hsup, Submodule.map_top]
  have h2 := (Submodule.finrank_mono hcomm).trans
    (Submodule.finrank_add_le_finrank_add_finrank _ _)
  have h3' := Submodule.finrank_map_le N (Submodule.span K {x₀})
  have h4 := Submodule.finrank_le H
  omega

end Pair

section Fixed

theorem partner_spec {x y : V} (hx : Q x = 0) (hxy : polar Q x y ≠ 0) :
    Q ((polar Q x y)⁻¹ • y + Q ((polar Q x y)⁻¹ • y) • x) = 0 ∧
      polar Q x ((polar Q x y)⁻¹ • y + Q ((polar Q x y)⁻¹ • y) • x) = 1 := by
  have hxu : polar Q x ((polar Q x y)⁻¹ • y) = 1 := by
    rw [polar_smul_right, smul_eq_mul, inv_mul_cancel₀ hxy]
  generalize (polar Q x y)⁻¹ • y = u at hxu ⊢
  have hsm : Q (Q u • x) = 0 := by rw [QuadraticMap.map_smul, hx, smul_zero]
  constructor
  · rw [map_add_eq, hsm, add_zero, polar_smul_right, polar_comm, hxu, smul_eq_mul, mul_one]
    exact CharTwo.add_self_eq_zero _
  · rw [polar_add_right, hxu, polar_smul_right, polar_self_eq_zero, smul_zero, add_zero]

omit [CharP K 2] in
theorem finrank_le_finrank_inf_ker_add_one [FiniteDimensional K V] (A : Submodule K V)
    (φ : V →ₗ[K] K) : finrank K A ≤ finrank K ↥(A ⊓ LinearMap.ker φ) + 1 := by
  have h1 := Submodule.finrank_sup_add_finrank_inf_eq A (LinearMap.ker φ)
  have h2 := Submodule.finrank_le (A ⊔ LinearMap.ker φ)
  have h3 := LinearMap.finrank_range_add_finrank_ker φ
  have h4 : finrank K (LinearMap.range φ) ≤ 1 := by
    have := Submodule.finrank_le (LinearMap.range φ)
    rwa [Module.finrank_self] at this
  omega

theorem exists_hypFamily_fixed [FiniteDimensional K V] [Finite K]
    (hQ : Q.polarBilin.Nondegenerate) (hO : t ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    (htt : t * t = 1) {w₀ : V} (hw₀ : w₀ ∈ commSpace t) (hQw₀ : Q w₀ ≠ 0)
    (hl : finrank K (commSpace t) ≤ 2) (h8 : 8 ≤ finrank K V) :
    ∃ e f : Fin 2 → V, IsHypFamily Q e f ∧ ∀ i, t (e i) = e i ∧ t (f i) = f i := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  set W := commSpace t with hW
  set C := fixSpace t with hC
  have hWC : W ≤ C := commSpace_le_fixSpace htt
  have hCW : C = LinearMap.BilinForm.orthogonal Q.polarBilin W :=
    fixSpace_eq_orthogonal_commSpace hQ hO htt
  have hrefl : (Q.polarBilin).IsRefl := fun x y h => by
    rw [polarBilin_apply_apply] at h ⊢
    rw [polar_comm]
    exact h
  have hWCp : ∀ w ∈ W, ∀ c ∈ C, polar Q w c = 0 := by
    intro w hw c hc
    rw [hCW, LinearMap.BilinForm.mem_orthogonal_iff] at hc
    exact hc w hw
  have hperp : ∀ x, (∀ c ∈ C, polar Q x c = 0) → x ∈ W := by
    intro x hx
    have hmem : x ∈ LinearMap.BilinForm.orthogonal Q.polarBilin C := by
      rw [LinearMap.BilinForm.mem_orthogonal_iff]
      intro c hc
      change polar Q c x = 0
      rw [polar_comm]
      exact hx c hc
    rwa [hCW, LinearMap.BilinForm.orthogonal_orthogonal hQ hrefl] at hmem
  have hdim : finrank K W + finrank K C = finrank K V := finrank_commSpace_add_finrank_fixSpace t
  obtain ⟨S, hS⟩ := W.exists_isCompl
  have hSdim : finrank K W + finrank K S = finrank K V := Submodule.finrank_add_eq_of_isCompl hS
  have hS₀dim : 4 ≤ finrank K ↥(S ⊓ C) := by
    have h1 := Submodule.finrank_sup_add_finrank_inf_eq S C
    have h1' := Submodule.finrank_le (S ⊔ C)
    omega
  have hS₀W : ∀ x ∈ S ⊓ C, x ∈ W → x = 0 := fun x hx hxW =>
    (Submodule.disjoint_def.mp hS.disjoint) x hxW hx.1
  have hpartner : ∀ {x : V} {D : Submodule K V}, x ∈ D → Q x = 0 →
      (∃ y ∈ D, polar Q x y ≠ 0) → ∃ y ∈ D, Q y = 0 ∧ polar Q x y = 1 := by
    rintro x D hxD hQx ⟨y, hyD, hxy⟩
    obtain ⟨h1, h2⟩ := partner_spec hQx hxy
    exact ⟨_, D.add_mem (D.smul_mem _ hyD) (D.smul_mem _ hxD), h1, h2⟩
  obtain ⟨x₁, hx₁S, hx₁0, hQx₁⟩ :=
    CFSG.LieType.SeitzGeneration.OrthBlk.exists_singular_of_three_le_charTwo (Q := Q) h2
      (le_trans (by norm_num : 3 ≤ 4) hS₀dim)
  have hx₁C : x₁ ∈ C := hx₁S.2
  have hx₁W : x₁ ∉ W := fun h => hx₁0 (hS₀W x₁ hx₁S h)
  obtain ⟨y₁, hy₁C, hQy₁, hxy₁⟩ := hpartner hx₁C hQx₁ (by
    by_contra h
    push Not at h
    exact hx₁W (hperp x₁ h))
  have hyx₁ : polar Q y₁ x₁ = 1 := by rw [polar_comm, hxy₁]
  set D := C ⊓ LinearMap.ker (Q.polarBilin x₁) ⊓ LinearMap.ker (Q.polarBilin y₁) with hD
  have hmemD : ∀ z, z ∈ D ↔ z ∈ C ∧ polar Q x₁ z = 0 ∧ polar Q y₁ z = 0 := by
    intro z
    simp only [hD, Submodule.mem_inf, LinearMap.mem_ker, polarBilin_apply_apply, and_assoc]
  have hS₂dim : 2 ≤ finrank K ↥(S ⊓ C ⊓ LinearMap.ker (Q.polarBilin x₁) ⊓
      LinearMap.ker (Q.polarBilin y₁)) := by
    have h1 : finrank K ↥(S ⊓ C) ≤ finrank K ↥(S ⊓ C ⊓ LinearMap.ker (Q.polarBilin x₁)) + 1 :=
      finrank_le_finrank_inf_ker_add_one _ _
    have h1' : finrank K ↥(S ⊓ C ⊓ LinearMap.ker (Q.polarBilin x₁)) ≤
        finrank K ↥(S ⊓ C ⊓ LinearMap.ker (Q.polarBilin x₁) ⊓
          LinearMap.ker (Q.polarBilin y₁)) + 1 :=
      finrank_le_finrank_inf_ker_add_one _ _
    omega
  obtain ⟨s, hsS₂, hs0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
    (p := S ⊓ C ⊓ LinearMap.ker (Q.polarBilin x₁) ⊓ LinearMap.ker (Q.polarBilin y₁)) fun h => by
      rw [h, finrank_bot] at hS₂dim
      omega
  have hsS : s ∈ S ⊓ C := hsS₂.1.1
  have hsC : s ∈ C := hsS.2
  have hsx₁ : polar Q x₁ s = 0 := by
    have := hsS₂.1.2
    simpa only [SetLike.mem_coe, LinearMap.mem_ker, polarBilin_apply_apply] using this
  have hsy₁ : polar Q y₁ s = 0 := by
    have := hsS₂.2
    simpa only [SetLike.mem_coe, LinearMap.mem_ker, polarBilin_apply_apply] using this
  obtain ⟨c, hc⟩ := isSquare_of_charTwo' (Q s / Q w₀)
  have hwW : c • w₀ ∈ W := W.smul_mem c hw₀
  set x₂ := s + c • w₀ with hx₂
  have hQx₂ : Q x₂ = 0 := by
    rw [hx₂, map_add_eq, QuadraticMap.map_smul, smul_eq_mul, ← hc, div_mul_cancel₀ _ hQw₀,
      polar_comm, hWCp _ hwW s hsC, add_zero]
    exact CharTwo.add_self_eq_zero _
  have hx₂C : x₂ ∈ C := C.add_mem hsC (hWC hwW)
  have hx₂W : x₂ ∉ W := fun h => hs0 (hS₀W s hsS (by
    have := W.sub_mem h hwW
    rwa [hx₂, add_sub_cancel_right] at this))
  have hx₁x₂ : polar Q x₁ x₂ = 0 := by
    rw [hx₂, polar_add_right, hsx₁, polar_comm, hWCp _ hwW x₁ hx₁C, add_zero]
  have hy₁x₂ : polar Q y₁ x₂ = 0 := by
    rw [hx₂, polar_add_right, hsy₁, polar_comm, hWCp _ hwW y₁ hy₁C, add_zero]
  have hx₂D : x₂ ∈ D := (hmemD x₂).mpr ⟨hx₂C, hx₁x₂, hy₁x₂⟩
  obtain ⟨y₂, hy₂D, hQy₂, hxy₂⟩ := hpartner hx₂D hQx₂ (by
    by_contra h
    push Not at h
    refine hx₂W (hperp x₂ fun z hz => ?_)
    have hz' : z + polar Q z y₁ • x₁ + polar Q z x₁ • y₁ ∈ D := by
      refine (hmemD _).mpr ⟨C.add_mem (C.add_mem hz (C.smul_mem _ hx₁C)) (C.smul_mem _ hy₁C),
        ?_, ?_⟩
      · rw [polar_add_right, polar_add_right, polar_smul_right, polar_smul_right,
          polar_self_eq_zero, hxy₁, smul_zero, add_zero, smul_eq_mul, mul_one, polar_comm]
        exact CharTwo.add_self_eq_zero _
      · rw [polar_add_right, polar_add_right, polar_smul_right, polar_smul_right,
          polar_self_eq_zero, hyx₁, smul_zero, add_zero, smul_eq_mul, mul_one, polar_comm]
        exact CharTwo.add_self_eq_zero _
    have := h _ hz'
    rwa [polar_add_right, polar_add_right, polar_smul_right, polar_smul_right, polar_comm Q x₂ x₁,
      hx₁x₂, polar_comm Q x₂ y₁, hy₁x₂, smul_zero, smul_zero, add_zero, add_zero] at this)
  obtain ⟨hy₂C, hx₁y₂, hy₁y₂⟩ := (hmemD y₂).mp hy₂D
  refine ⟨![x₁, x₂], ![y₁, y₂], ⟨fun k => ?_, fun k => ?_, fun i j => ?_, fun i j => ?_,
    fun i j => ?_⟩, fun i => ?_⟩
  · fin_cases k
    · exact hQx₁
    · exact hQx₂
  · fin_cases k
    · exact hQy₁
    · exact hQy₂
  · fin_cases i <;> fin_cases j <;>
      simp only [Fin.zero_eta, Fin.mk_one, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one]
    · exact polar_self_eq_zero Q x₁
    · exact hx₁x₂
    · rw [polar_comm]
      exact hx₁x₂
    · exact polar_self_eq_zero Q x₂
  · fin_cases i <;> fin_cases j <;>
      simp only [Fin.zero_eta, Fin.mk_one, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one]
    · exact polar_self_eq_zero Q y₁
    · exact hy₁y₂
    · rw [polar_comm]
      exact hy₁y₂
    · exact polar_self_eq_zero Q y₂
  · fin_cases i <;> fin_cases j <;>
      simp only [Fin.zero_eta, Fin.mk_one, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one,
        ite_true, Fin.reduceEq, ite_false]
    · exact hxy₁
    · exact hx₁y₂
    · rw [polar_comm]
      exact hy₁x₂
    · exact hxy₂
  · fin_cases i
    · exact ⟨mem_fixSpace.mp hx₁C, mem_fixSpace.mp hy₁C⟩
    · exact ⟨mem_fixSpace.mp hx₂C, mem_fixSpace.mp hy₂C⟩

end Fixed

section Main

theorem exists_hypFamily_stable [FiniteDimensional K V] [Finite K]
    (hQ : Q.polarBilin.Nondegenerate) (hO : t ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    (htt : t * t = 1) (ht1 : t ≠ 1) (h8 : 8 ≤ finrank K V) :
    ∃ e f : Fin 2 → V, IsHypFamily Q e f ∧
      (∀ i, t (e i) ∈ Submodule.span K (Set.range e)) ∧
      ∀ i, t (f i) ∈ Submodule.span K (Set.range f) := by
  have hmem : ∀ (u : Fin 2 → V) i, u i ∈ Submodule.span K (Set.range u) :=
    fun u i => Submodule.subset_span ⟨i, rfl⟩
  have hmoving : ∀ {f₁ f₂ : V}, wallForm Q t f₁ f₁ = 0 → wallForm Q t f₂ f₂ = 0 →
      wallForm Q t f₁ f₂ = 1 → ∃ e f : Fin 2 → V, IsHypFamily Q e f ∧
        (∀ i, t (e i) ∈ Submodule.span K (Set.range e)) ∧
        ∀ i, t (f i) ∈ Submodule.span K (Set.range f) := by
    intro f₁ f₂ h₁ h₂ h₁₂
    obtain ⟨e, f, hef, he0, he1, hf0, hf1⟩ := exists_hypFamily_of_wall hO htt h₁ h₂ h₁₂
    refine ⟨e, f, hef, fun i => ?_, fun i => ?_⟩
    · fin_cases i
      · show t (e 0) ∈ _
        rw [he0]
        exact hmem e 0
      · show t (e 1) ∈ _
        rw [he1]
        exact add_mem (hmem e 1) (hmem e 0)
    · fin_cases i
      · show t (f 0) ∈ _
        rw [hf0]
        exact add_mem (hmem f 0) (hmem f 1)
      · show t (f 1) ∈ _
        rw [hf1]
        exact hmem f 1
  by_cases halt : ∀ x, wallForm Q t x x = 0
  · obtain ⟨f₁, f₂, h₁, h₂, h₁₂⟩ := exists_wall_pair_of_alt hQ hO htt ht1 halt
    exact hmoving h₁ h₂ h₁₂
  push Not at halt
  obtain ⟨x₀, hx₀⟩ := halt
  by_cases h3 : 3 ≤ finrank K (commSpace t)
  · obtain ⟨f₁, f₂, h₁, h₂, h₁₂⟩ := exists_wall_pair_of_three hQ hO htt hx₀ h3
    exact hmoving h₁ h₂ h₁₂
  · obtain ⟨e, f, hef, hfix⟩ := exists_hypFamily_fixed hQ hO htt (sub_mem_commSpace t x₀)
      (by rwa [← wallForm_self hO]) (by omega) h8
    exact ⟨e, f, hef, fun i => by rw [(hfix i).1]; exact hmem e i,
      fun i => by rw [(hfix i).2]; exact hmem f i⟩

theorem exists_orthDerived_apply_eq [FiniteDimensional K V] [Finite K]
    (hQ : Q.polarBilin.Nondegenerate)
    (hT : ∃ T : Submodule K V, finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0)
    {e f e' f' : Fin 2 → V} (h : IsHypFamily Q e f) (h' : IsHypFamily Q e' f')
    {w : V} (hw : Q w ≠ 0) (hwe : ∀ i, polar Q w (e i) = 0) (hwf : ∀ i, polar Q w (f i) = 0) :
    ∃ g ∈ CFSG.RankThree.Classical2.orthDerived Q, ∀ i, g (e i) = e' i ∧ g (f i) = f' i := by
  obtain ⟨g, hgO, hg⟩ := exists_orth_apply_eq hQ (Sum.elim e f) (Sum.elim e' f')
    h.linearIndependent h'.linearIndependent (fun i => by
      rcases i with i | i
      · rw [Sum.elim_inl, Sum.elim_inl, h.map_e, h'.map_e]
      · rw [Sum.elim_inr, Sum.elim_inr, h.map_f, h'.map_f])
    (fun i j => by
      rcases i with i | i <;> rcases j with j | j <;>
        simp only [Sum.elim_inl, Sum.elim_inr]
      · rw [h.polar_ee, h'.polar_ee]
      · rw [h.polar_ef, h'.polar_ef]
      · rw [polar_comm, h'.polar_ef, polar_comm, h.polar_ef]
      · rw [h.polar_ff, h'.polar_ff])
  have hgo : ∀ i, g (e i) = e' i ∧ g (f i) = f' i := fun i => ⟨hg (Sum.inl i), hg (Sum.inr i)⟩
  let _ : Invertible (Q w) := invertibleOfNonzero hw
  have hrO := TauCeti.QuadraticMap.reflection_mem_orthogonalGroup Q w
  have hr1 : finrank K (commSpace (TauCeti.QuadraticMap.reflection Q w)) = 1 :=
    finrank_commSpace_reflection hQ w
  have hΩ := CFSG.RankThree.PartOne.FieldFix.omegaGroup_le_orthDerived hQ hT
  by_cases hev : Even (finrank K (commSpace g))
  · exact ⟨g, hΩ ⟨hgO, hev⟩, hgo⟩
  · refine ⟨g * TauCeti.QuadraticMap.reflection Q w, hΩ ⟨mul_mem hgO hrO, ?_⟩, fun i => ?_⟩
    · obtain ⟨k, hk⟩ := Nat.not_even_iff_odd.mp hev
      rw [← ZMod.natCast_eq_zero_iff_even, natCast_finrank_commSpace_mul hQ hgO hrO, hr1, hk]
      push_cast
      rw [show (2 : ZMod 2) = 0 from rfl, zero_mul, zero_add]
      rfl
    · rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply,
        TauCeti.QuadraticMap.reflection_apply_of_polar_eq_zero _ _ (hwe i),
        TauCeti.QuadraticMap.reflection_apply_of_polar_eq_zero _ _ (hwf i)]
      exact hgo i

end Main

end WitOm

end CFSG.StandardType
