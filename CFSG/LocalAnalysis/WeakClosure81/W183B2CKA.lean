module

public import CFSG.LocalAnalysis.WeakClosure81.W183B2CKOuter
public import CFSG.LocalAnalysis.WeakClosure81.W183B2CKHeart
public import CFSG.LocalAnalysis.WeakClosure81.W183B2Fin
public import CFSG.LocalAnalysis.WeakClosure81.W183B2CKAAux1
import CFSG.LocalAnalysis.WeakClosure81.W183K3Quasi
import CFSG.LocalAnalysis.ComponentClassification.Quasisimple

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open scoped TensorProduct
open CFSG.Quasithin CFSG.Open Subgroup
open CFSG.LocalAnalysis.UniquenessCase.UC22 (IsL3 IsAlt IsSp4)
open CFSG.LocalAnalysis.ComponentInitial.PairedTensorOrbits

theorem w183b2_core_k_caseA_of_abs {G : Type} [Group G] [Finite G] {Q : Type} [AddCommGroup Q]
    [Module (AlgebraicClosure (ZMod 2)) Q] [FiniteDimensional (AlgebraicClosure (ZMod 2)) Q]
    {ρ : Representation (AlgebraicClosure (ZMod 2)) G Q} {A₁ A₂ Δ : Subgroup G}
    (h : CoreSetting ρ A₁ A₂ Δ) (hAbs : AbsIrrOverF4 ↥A₁)
    (hsimple : ∀ U : Submodule (AlgebraicClosure (ZMod 2)) Q,
      w183b2InvSub ρ (A₁ ⊔ A₂) U → U = ⊥ ∨ U = ⊤) :
    Nat.card ↥Δ ≤ 4 := by
  obtain ⟨U₁, U₂, _, _, _, _, _, _, ρ₁, ρ₂, E, hirr₁, hirr₂, hE₁, hE₂⟩ :=
    w183b2_outer_decomp h hsimple
  haveI hnt₁ : Nontrivial U₁ := ((isIrreducible_iff ρ₁).1 hirr₁).1
  haveI hnt₂ : Nontrivial U₂ := ((isIrreducible_iff ρ₂).1 hirr₂).1
  haveI hfinΔ : Finite ↥Δ := Finite.of_injective (Subtype.val : ↥Δ → G) Subtype.val_injective
  have hend₁ : ∀ f : U₁ →ₗ[AlgebraicClosure (ZMod 2)] U₁,
      (∀ a x, f (ρ₁ a x) = ρ₁ a (f x)) → ∃ c : AlgebraicClosure (ZMod 2), f = c • 1 := by
    intro f hf
    obtain ⟨c, hc⟩ := Module.End.exists_eigenvalue f
    have hEinv : IsInv ρ₁ (Module.End.eigenspace f c) := by
      intro a x hx
      rw [Module.End.mem_eigenspace_iff] at hx ⊢
      rw [hf a x, hx, map_smul]
    rcases ((isIrreducible_iff ρ₁).1 hirr₁).2 _ hEinv with hbot | htop
    · exact absurd hbot hc
    · refine ⟨c, ?_⟩
      ext x
      have hx : x ∈ Module.End.eigenspace f c := by rw [htop]; trivial
      rw [Module.End.mem_eigenspace_iff] at hx
      simpa using hx
  have hend₂ : ∀ f : U₂ →ₗ[AlgebraicClosure (ZMod 2)] U₂,
      (∀ b x, f (ρ₂ b x) = ρ₂ b (f x)) → ∃ c : AlgebraicClosure (ZMod 2), f = c • 1 := by
    intro f hf
    obtain ⟨c, hc⟩ := Module.End.exists_eigenvalue f
    have hEinv : IsInv ρ₂ (Module.End.eigenspace f c) := by
      intro b x hx
      rw [Module.End.mem_eigenspace_iff] at hx ⊢
      rw [hf b x, hx, map_smul]
    rcases ((isIrreducible_iff ρ₂).1 hirr₂).2 _ hEinv with hbot | htop
    · exact absurd hbot hc
    · refine ⟨c, ?_⟩
      ext x
      have hx : x ∈ Module.End.eigenspace f c := by rw [htop]; trivial
      rw [Module.End.mem_eigenspace_iff] at hx
      simpa using hx
  have hAbs₁ : AbsIrr ρ₁ := AbsIrr.of_isIrreducible hirr₁ hend₁
  have hAbs₂ : AbsIrr ρ₂ := AbsIrr.of_isIrreducible hirr₂ hend₂
  have hconj₁ : ∀ a : ↥A₁, (E.conjAlgEquiv (AlgebraicClosure (ZMod 2))) (ρ (a : G)) =
      TensorProduct.map (ρ₁ a) (LinearMap.id : Module.End (AlgebraicClosure (ZMod 2)) U₂) := by
    intro a
    apply LinearMap.ext
    intro q
    simp only [LinearEquiv.conjAlgEquiv_apply, LinearMap.coe_comp, LinearEquiv.coe_coe,
      Function.comp_apply]
    rw [hE₁ a (E.symm q), E.apply_symm_apply]
  have hconj₂ : ∀ b : ↥A₂, (E.conjAlgEquiv (AlgebraicClosure (ZMod 2))) (ρ (b : G)) =
      TensorProduct.map (LinearMap.id : Module.End (AlgebraicClosure (ZMod 2)) U₁) (ρ₂ b) := by
    intro b
    apply LinearMap.ext
    intro q
    simp only [LinearEquiv.conjAlgEquiv_apply, LinearMap.coe_comp, LinearEquiv.coe_coe,
      Function.comp_apply]
    rw [hE₂ b (E.symm q), E.apply_symm_apply]
  have hker₁ : ∀ x : ↥A₁, ρ₁ x = 1 → x ∈ Subgroup.center ↥A₁ := by
    have hne : MonoidHom.ker ρ₁ ≠ ⊤ := by
      intro htop
      obtain ⟨a, ha, q, hq⟩ := h.nontriv₁
      have hker : (⟨a, ha⟩ : ↥A₁) ∈ MonoidHom.ker ρ₁ := by rw [htop]; trivial
      have h1 : ρ₁ (⟨a, ha⟩ : ↥A₁) = 1 := hker
      have hEρ : (E.conjAlgEquiv (AlgebraicClosure (ZMod 2))) (ρ a) = 1 := by
        rw [hconj₁ ⟨a, ha⟩, h1]
        exact TensorProduct.map_one
      have hρ : ρ a = 1 := by
        have := congrArg (fun F => (E.conjAlgEquiv (AlgebraicClosure (ZMod 2))).symm F) hEρ
        simpa using this
      rw [hρ] at hq
      exact hq rfl
    intro x hx
    exact CFSG.ComponentClassification.Quasisimple.normal_le_center_of_ne_top h.quasi₁
      (MonoidHom.ker ρ₁) hne (MonoidHom.mem_ker.mpr hx)
  have hker₂ : ∀ x : ↥A₂, ρ₂ x = 1 → x ∈ Subgroup.center ↥A₂ := by
    have hne : MonoidHom.ker ρ₂ ≠ ⊤ := by
      intro htop
      obtain ⟨b, hb, q, hq⟩ := h.nontriv₂
      have hker : (⟨b, hb⟩ : ↥A₂) ∈ MonoidHom.ker ρ₂ := by rw [htop]; trivial
      have h1 : ρ₂ (⟨b, hb⟩ : ↥A₂) = 1 := hker
      have hEρ : (E.conjAlgEquiv (AlgebraicClosure (ZMod 2))) (ρ b) = 1 := by
        rw [hconj₂ ⟨b, hb⟩, h1]
        exact TensorProduct.map_one
      have hρ : ρ b = 1 := by
        have := congrArg (fun F => (E.conjAlgEquiv (AlgebraicClosure (ZMod 2))).symm F) hEρ
        simpa using this
      rw [hρ] at hq
      exact hq rfl
    intro x hx
    exact CFSG.ComponentClassification.Quasisimple.normal_le_center_of_ne_top h.quasi₂
      (MonoidHom.ker ρ₂) hne (MonoidHom.mem_ker.mpr hx)
  let T : ↥Δ →* Module.End (AlgebraicClosure (ZMod 2)) (U₁ ⊗[AlgebraicClosure (ZMod 2)] U₂) :=
    (E.conjAlgEquiv (AlgebraicClosure (ZMod 2))).toMonoidHom.comp (ρ.comp Δ.subtype)
  have hT : ∀ d : ↥Δ, T d = (E.conjAlgEquiv (AlgebraicClosure (ZMod 2))) (ρ (d : G)) :=
    fun d => rfl
  have hΔ : ∀ d : ↥Δ, d * d = 1 := by
    intro d
    apply Subtype.ext
    have hd2 : (d : G) ^ 2 = 1 := h.elem.2 (d : G) d.2
    simpa [pow_two] using hd2
  have hTunit : ∀ d : ↥Δ, IsUnit (T d) := by
    intro d
    refine ⟨⟨T d, T d, ?_, ?_⟩, rfl⟩ <;> rw [← map_mul, hΔ d, map_one]
  have hinj : ∀ d : ↥Δ, T d = 1 → d = 1 := by
    intro d hd
    apply Subtype.ext
    apply w183b2_faithful_kernel h d.2
    have hρd : ρ (d : G) = 1 := by
      have := congrArg (fun F => (E.conjAlgEquiv (AlgebraicClosure (ZMod 2))).symm F) hd
      simpa [T] using this
    exact hρd
  have hquad : ∀ d e : ↥Δ, (T d - 1) * (T e - 1) = 0 := by
    intro d e
    have hq := w183b2_quadratic_operator h d.2 e.2
    have h1 : (1 : Module.End (AlgebraicClosure (ZMod 2))
        (U₁ ⊗[AlgebraicClosure (ZMod 2)] U₂)) =
        (E.conjAlgEquiv (AlgebraicClosure (ZMod 2))) 1 := (map_one _).symm
    rw [hT d, hT e, h1, ← map_sub, ← map_sub, ← map_mul, hq, map_zero]
  have hgen₁ : ∀ (d : ↥Δ) (a : ↥A₁),
      T d * TensorProduct.map (ρ₁ a) LinearMap.id =
        TensorProduct.map (ρ₁ ⟨(d : G) * (a : G) * (d : G)⁻¹,
          h.norm₁ (d : G) d.2 (a : G) a.2⟩) LinearMap.id * T d := by
    intro d a
    rw [hT d, ← hconj₁ a, ← hconj₁ ⟨(d : G) * (a : G) * (d : G)⁻¹,
      h.norm₁ (d : G) d.2 (a : G) a.2⟩]
    rw [← map_mul, ← map_mul]
    congr 1
    rw [← map_mul, ← map_mul]
    congr 1
    group
  have hgen₂ : ∀ (d : ↥Δ) (b : ↥A₂),
      T d * TensorProduct.map LinearMap.id (ρ₂ b) =
        TensorProduct.map LinearMap.id (ρ₂ ⟨(d : G) * (b : G) * (d : G)⁻¹,
          h.norm₂ (d : G) d.2 (b : G) b.2⟩) * T d := by
    intro d b
    rw [hT d, ← hconj₂ b, ← hconj₂ ⟨(d : G) * (b : G) * (d : G)⁻¹,
      h.norm₂ (d : G) d.2 (b : G) b.2⟩]
    rw [← map_mul, ← map_mul]
    congr 1
    rw [← map_mul, ← map_mul]
    congr 1
    group
  have hn₁ : ∀ (d : ↥Δ) (X : Module.End (AlgebraicClosure (ZMod 2)) U₁),
      ∃ X' : Module.End (AlgebraicClosure (ZMod 2)) U₁,
        T d * TensorProduct.map X LinearMap.id = TensorProduct.map X' LinearMap.id * T d := by
    intro d X
    have hmem : X ∈ Submodule.span (AlgebraicClosure (ZMod 2)) (Set.range ρ₁) := by
      rw [hAbs₁.2]; trivial
    induction hmem using Submodule.span_induction with
    | mem X hX => obtain ⟨a, rfl⟩ := hX; exact ⟨_, hgen₁ d a⟩
    | zero => exact ⟨0, by simp⟩
    | add X Y _ _ hX hY =>
        obtain ⟨X', hX'⟩ := hX
        obtain ⟨Y', hY'⟩ := hY
        refine ⟨X' + Y', ?_⟩
        calc T d * TensorProduct.map (X + Y) LinearMap.id
            = T d * (TensorProduct.map X LinearMap.id +
                TensorProduct.map Y LinearMap.id) := by rw [TensorProduct.map_add_left]
          _ = T d * TensorProduct.map X LinearMap.id +
                T d * TensorProduct.map Y LinearMap.id := by rw [mul_add]
          _ = TensorProduct.map X' LinearMap.id * T d +
                TensorProduct.map Y' LinearMap.id * T d := by rw [hX', hY']
          _ = (TensorProduct.map X' LinearMap.id +
                TensorProduct.map Y' LinearMap.id) * T d := by rw [add_mul]
          _ = TensorProduct.map (X' + Y') LinearMap.id * T d := by
                rw [TensorProduct.map_add_left]
    | smul c X _ hX =>
        obtain ⟨X', hX'⟩ := hX
        refine ⟨c • X', ?_⟩
        calc T d * TensorProduct.map (c • X) LinearMap.id
            = T d * (c • TensorProduct.map X LinearMap.id) := by
                rw [TensorProduct.map_smul_left]
          _ = c • (T d * TensorProduct.map X LinearMap.id) := by rw [mul_smul_comm]
          _ = c • (TensorProduct.map X' LinearMap.id * T d) := by rw [hX']
          _ = (c • TensorProduct.map X' LinearMap.id) * T d := by rw [smul_mul_assoc]
          _ = TensorProduct.map (c • X') LinearMap.id * T d := by
                rw [TensorProduct.map_smul_left]
  have hn₂ : ∀ (d : ↥Δ) (Y : Module.End (AlgebraicClosure (ZMod 2)) U₂),
      ∃ Y' : Module.End (AlgebraicClosure (ZMod 2)) U₂,
        T d * TensorProduct.map LinearMap.id Y = TensorProduct.map LinearMap.id Y' * T d := by
    intro d Y
    have hmem : Y ∈ Submodule.span (AlgebraicClosure (ZMod 2)) (Set.range ρ₂) := by
      rw [hAbs₂.2]; trivial
    induction hmem using Submodule.span_induction with
    | mem Y hY => obtain ⟨b, rfl⟩ := hY; exact ⟨_, hgen₂ d b⟩
    | zero => exact ⟨0, by simp⟩
    | add X Y _ _ hX hY =>
        obtain ⟨X', hX'⟩ := hX
        obtain ⟨Y', hY'⟩ := hY
        refine ⟨X' + Y', ?_⟩
        calc T d * TensorProduct.map LinearMap.id (X + Y)
            = T d * (TensorProduct.map LinearMap.id X +
                TensorProduct.map LinearMap.id Y) := by rw [TensorProduct.map_add_right]
          _ = T d * TensorProduct.map LinearMap.id X +
                T d * TensorProduct.map LinearMap.id Y := by rw [mul_add]
          _ = TensorProduct.map LinearMap.id X' * T d +
                TensorProduct.map LinearMap.id Y' * T d := by rw [hX', hY']
          _ = (TensorProduct.map LinearMap.id X' +
                TensorProduct.map LinearMap.id Y') * T d := by rw [add_mul]
          _ = TensorProduct.map LinearMap.id (X' + Y') * T d := by
                rw [TensorProduct.map_add_right]
    | smul c X _ hX =>
        obtain ⟨X', hX'⟩ := hX
        refine ⟨c • X', ?_⟩
        calc T d * TensorProduct.map LinearMap.id (c • X)
            = T d * (c • TensorProduct.map LinearMap.id X) := by
                rw [TensorProduct.map_smul_right]
          _ = c • (T d * TensorProduct.map LinearMap.id X) := by rw [mul_smul_comm]
          _ = c • (TensorProduct.map LinearMap.id X' * T d) := by rw [hX']
          _ = (c • TensorProduct.map LinearMap.id X') * T d := by rw [smul_mul_assoc]
          _ = TensorProduct.map LinearMap.id (c • X') * T d := by
                rw [TensorProduct.map_smul_right]
  have hc₁ : ∃ e : ↥Δ, ∃ X : Module.End (AlgebraicClosure (ZMod 2)) U₁,
      T e * TensorProduct.map X LinearMap.id ≠ TensorProduct.map X LinearMap.id * T e := by
    by_contra hcon
    have hall : ∀ (e : ↥Δ) (X : Module.End (AlgebraicClosure (ZMod 2)) U₁),
        T e * TensorProduct.map X LinearMap.id = TensorProduct.map X LinearMap.id * T e :=
      fun e X => not_not.mp fun hne => hcon ⟨e, X, hne⟩
    have hcent : ∀ d ∈ Δ, ∀ y ∈ A₁, d * y * d⁻¹ * y⁻¹ ∈ W183K3.quasiCentre A₁ := by
      intro d hd y hyA
      have hcomm := hall ⟨d, hd⟩ (ρ₁ ⟨y, hyA⟩)
      have hgen := hgen₁ ⟨d, hd⟩ ⟨y, hyA⟩
      have h1 : TensorProduct.map (ρ₁ ⟨d * y * d⁻¹,
          h.norm₁ d hd y hyA⟩) LinearMap.id * T ⟨d, hd⟩ =
          TensorProduct.map (ρ₁ ⟨y, hyA⟩) LinearMap.id * T ⟨d, hd⟩ := by
        rw [← hgen, hcomm]
      have h2 : TensorProduct.map (ρ₁ ⟨d * y * d⁻¹,
          h.norm₁ d hd y hyA⟩) LinearMap.id =
          TensorProduct.map (ρ₁ ⟨y, hyA⟩) LinearMap.id :=
        (hTunit ⟨d, hd⟩).mul_right_cancel h1
      have h3 : ρ₁ ⟨d * y * d⁻¹, h.norm₁ d hd y hyA⟩ = ρ₁ ⟨y, hyA⟩ :=
        w183b2_tensor_map_one_injective h2
      have h4 : ρ₁ (⟨d * y * d⁻¹, h.norm₁ d hd y hyA⟩ * (⟨y, hyA⟩ : ↥A₁)⁻¹) = 1 := by
        rw [map_mul, h3, ← map_mul, mul_inv_cancel, map_one]
      exact Subgroup.mem_map.mpr ⟨_, hker₁ _ h4, rfl⟩
    apply h.two₂
    intro d hd
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact (W183K3.quasi_comm_of_comm_mod_centre h.quasi₁ (fun l hl => h.norm₁ d hd l hl)
      (hcent d hd) y hy).symm
  have hc₂ : ∃ e : ↥Δ, ∃ Y : Module.End (AlgebraicClosure (ZMod 2)) U₂,
      T e * TensorProduct.map LinearMap.id Y ≠ TensorProduct.map LinearMap.id Y * T e := by
    by_contra hcon
    have hall : ∀ (e : ↥Δ) (Y : Module.End (AlgebraicClosure (ZMod 2)) U₂),
        T e * TensorProduct.map LinearMap.id Y = TensorProduct.map LinearMap.id Y * T e :=
      fun e Y => not_not.mp fun hne => hcon ⟨e, Y, hne⟩
    have hcent : ∀ d ∈ Δ, ∀ y ∈ A₂, d * y * d⁻¹ * y⁻¹ ∈ W183K3.quasiCentre A₂ := by
      intro d hd y hyA
      have hcomm := hall ⟨d, hd⟩ (ρ₂ ⟨y, hyA⟩)
      have hgen := hgen₂ ⟨d, hd⟩ ⟨y, hyA⟩
      have h1 : TensorProduct.map LinearMap.id (ρ₂ ⟨d * y * d⁻¹,
          h.norm₂ d hd y hyA⟩) * T ⟨d, hd⟩ =
          TensorProduct.map LinearMap.id (ρ₂ ⟨y, hyA⟩) * T ⟨d, hd⟩ := by
        rw [← hgen, hcomm]
      have h2 : TensorProduct.map LinearMap.id (ρ₂ ⟨d * y * d⁻¹,
          h.norm₂ d hd y hyA⟩) =
          TensorProduct.map LinearMap.id (ρ₂ ⟨y, hyA⟩) :=
        (hTunit ⟨d, hd⟩).mul_right_cancel h1
      have h3 : ρ₂ ⟨d * y * d⁻¹, h.norm₂ d hd y hyA⟩ = ρ₂ ⟨y, hyA⟩ :=
        w183b2_tensor_map_one_injective_right h2
      have h4 : ρ₂ (⟨d * y * d⁻¹, h.norm₂ d hd y hyA⟩ * (⟨y, hyA⟩ : ↥A₂)⁻¹) = 1 := by
        rw [map_mul, h3, ← map_mul, mul_inv_cancel, map_one]
      exact Subgroup.mem_map.mpr ⟨_, hker₂ _ h4, rfl⟩
    apply h.two₁
    intro d hd
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact (W183K3.quasi_comm_of_comm_mod_centre h.quasi₂ (fun l hl => h.norm₂ d hd l hl)
      (hcent d hd) y hy).symm
  have hF : ∃ (n : ℕ) (b : Module.Basis (Fin n) (AlgebraicClosure (ZMod 2)) U₁)
      (F : Subfield (AlgebraicClosure (ZMod 2)))
      (S : Set (Module.End (AlgebraicClosure (ZMod 2)) U₁)),
      Finite F ∧ Nat.card F ≤ 4 ∧
      Submodule.span (AlgebraicClosure (ZMod 2)) S = ⊤ ∧
      (∀ s ∈ S, ∀ i j, LinearMap.toMatrix b b s i j ∈ F) ∧
      ∀ d, ∀ s ∈ S, ∃ s' ∈ S,
        T d * TensorProduct.map s LinearMap.id = TensorProduct.map s' LinearMap.id * T d := by
    let n : ℕ := Module.finrank (AlgebraicClosure (ZMod 2)) U₁
    let b₀ : Module.Basis (Fin n) (AlgebraicClosure (ZMod 2)) U₁ :=
      Module.finBasis (AlgebraicClosure (ZMod 2)) U₁
    let ρ₁mat : ↥A₁ →* Matrix.GeneralLinearGroup (Fin n) (AlgebraicClosure (ZMod 2)) :=
      (Units.mapEquiv (LinearMap.toMatrixAlgEquiv b₀).toMulEquiv).toMonoidHom.comp ρ₁.toHomUnits
    have hρ₁mat : ∀ a : ↥A₁, ((ρ₁mat a : Matrix.GeneralLinearGroup (Fin n)
        (AlgebraicClosure (ZMod 2))) : Matrix (Fin n) (Fin n) (AlgebraicClosure (ZMod 2))) =
        LinearMap.toMatrix b₀ b₀ (ρ₁ a) := by
      intro a
      rfl
    have hirr₁mat : ∀ W : Submodule (AlgebraicClosure (ZMod 2))
        (Fin n → AlgebraicClosure (ZMod 2)),
        (∀ x : ↥A₁, ∀ w ∈ W, ((ρ₁mat x : Matrix.GeneralLinearGroup (Fin n)
          (AlgebraicClosure (ZMod 2))) : Matrix (Fin n) (Fin n)
            (AlgebraicClosure (ZMod 2))).mulVec w ∈ W) → W = ⊥ ∨ W = ⊤ := by
      intro W hW
      let W' : Submodule (AlgebraicClosure (ZMod 2)) U₁ := W.comap b₀.equivFun.toLinearMap
      have hW'inv : IsInv ρ₁ W' := by
        intro a u hu
        have hu' : b₀.equivFun u ∈ W := hu
        have hmem : (LinearMap.toMatrix b₀ b₀ (ρ₁ a)).mulVec (b₀.equivFun u) ∈ W := by
          have := hW a (b₀.equivFun u) hu'
          rwa [hρ₁mat a] at this
        have heq : b₀.equivFun (ρ₁ a u) =
            (LinearMap.toMatrix b₀ b₀ (ρ₁ a)).mulVec (b₀.equivFun u) := by
          rw [Module.Basis.equivFun_apply, Module.Basis.equivFun_apply]
          exact (LinearMap.toMatrix_mulVec_repr b₀ b₀ (ρ₁ a) u).symm
        change b₀.equivFun ((ρ₁ a) u) ∈ W
        rw [heq]
        exact hmem
      have hmap : W'.map b₀.equivFun.toLinearMap = W :=
        Submodule.map_comap_eq_self
          (by rw [LinearMap.range_eq_top.mpr b₀.equivFun.surjective]; exact le_top)
      rcases ((isIrreducible_iff ρ₁).1 hirr₁).2 W' hW'inv with h | h
      · left
        rw [← hmap, h, Submodule.map_bot]
      · right
        rw [← hmap, h, Submodule.map_top,
          LinearMap.range_eq_top.mpr b₀.equivFun.surjective]
    obtain ⟨F, P, hFfin, hFcard, hPent⟩ := hAbs n ρ₁mat hirr₁mat
    let u : (U₁ →ₗ[AlgebraicClosure (ZMod 2)] U₁)ˣ :=
      Units.map (Matrix.toLinAlgEquiv b₀).toMonoidHom P⁻¹
    let φ : U₁ ≃ₗ[AlgebraicClosure (ZMod 2)] U₁ := LinearMap.GeneralLinearGroup.toLinearEquiv u
    have hφ : LinearMap.toMatrix b₀ b₀ (φ : U₁ →ₗ[AlgebraicClosure (ZMod 2)] U₁) =
        ((P⁻¹ : Matrix.GeneralLinearGroup (Fin n) (AlgebraicClosure (ZMod 2))) :
          Matrix (Fin n) (Fin n) (AlgebraicClosure (ZMod 2))) := by
      change LinearMap.toMatrixAlgEquiv b₀ (φ : U₁ →ₗ[AlgebraicClosure (ZMod 2)] U₁) = _
      rw [show (φ : U₁ →ₗ[AlgebraicClosure (ZMod 2)] U₁) =
          (Matrix.toLinAlgEquiv b₀) ((P⁻¹ : Matrix.GeneralLinearGroup (Fin n)
            (AlgebraicClosure (ZMod 2))) : Matrix (Fin n) (Fin n) (AlgebraicClosure (ZMod 2))) by
        rfl]
      rw [LinearMap.toMatrixAlgEquiv_toLinAlgEquiv]
    refine ⟨n, b₀.map φ, F, Set.range ρ₁, hFfin, hFcard, hAbs₁.2, ?_, ?_⟩
    · rintro s ⟨a, rfl⟩ i j
      rw [w183b2_toMatrix_map_map b₀ φ P hφ (ρ₁ a)]
      have h := hPent a i j
      rwa [show ((P * ρ₁mat a * P⁻¹ : Matrix.GeneralLinearGroup (Fin n)
          (AlgebraicClosure (ZMod 2))) : Matrix (Fin n) (Fin n) (AlgebraicClosure (ZMod 2))) =
          ((P : Matrix.GeneralLinearGroup (Fin n) (AlgebraicClosure (ZMod 2))) :
            Matrix (Fin n) (Fin n) (AlgebraicClosure (ZMod 2))) *
          LinearMap.toMatrix b₀ b₀ (ρ₁ a) *
          ((P⁻¹ : Matrix.GeneralLinearGroup (Fin n) (AlgebraicClosure (ZMod 2))) :
            Matrix (Fin n) (Fin n) (AlgebraicClosure (ZMod 2))) by
        rw [Units.val_mul, Units.val_mul, hρ₁mat a]] at h
    · rintro d s ⟨a, rfl⟩
      exact ⟨ρ₁ ⟨(d : G) * (a : G) * (d : G)⁻¹,
        h.norm₁ (d : G) d.2 (a : G) a.2⟩, ⟨_, rfl⟩, hgen₁ d a⟩
  exact w183b2_core_tensor hΔ T hinj hquad hn₁ hn₂ hc₁ hc₂ hF

end CFSG.LocalAnalysis.WeakClosure81

end
