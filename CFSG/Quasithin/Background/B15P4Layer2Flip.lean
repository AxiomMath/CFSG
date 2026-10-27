module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.OffenderTransitive

public section

namespace CFSG.Quasithin.B15P4

open TensorProduct Module CFSG.QuasithinUnique.Setup.Offender

universe u

section Core

variable {F : Type u} [Field F] {P : Type u} [AddCommGroup P] [Module F P]
  {W : Type u} [AddCommGroup W] [Module F W]

theorem flip_core_false [Finite F] [CharP F 2] [Module.Finite F P]
    (hD : 2 ≤ Module.finrank F P) (Φ : W ≃ₗ[F] P ⊗[F] P)
    (B : Subgroup (W ≃ₗ[F] W)) (hB0 : B ≠ ⊥) (hB2 : ∀ b ∈ B, b * b = 1)
    (a₀ : W ≃ₗ[F] W) (ha₀2 : a₀ * a₀ = 1) (hBa₀ : ∀ b ∈ B, b * a₀ = a₀ * b)
    (hblock : ∀ b ∈ B, ∃ x y : P ≃ₗ[F] P, ∀ p q,
      Φ (b (Φ.symm (p ⊗ₜ[F] q))) = x p ⊗ₜ[F] y q)
    (hswap : ∃ α β : P ≃ₗ[F] P, ∀ p q, Φ (a₀ (Φ.symm (p ⊗ₜ[F] q))) = α q ⊗ₜ[F] β p)
    (hq : ∀ b ∈ B, ∀ w, b (a₀ w - w) = a₀ w - w)
    (hoff : Nat.card W ≤ Nat.card B * Nat.card (fixGL B)) : False := by
  classical
  have hnt : Nontrivial P := Module.nontrivial_of_finrank_pos (R := F) (M := P) (by omega)
  obtain ⟨α, β, hαβ⟩ := hswap
  let Ψ : (P ⊗[F] P) ≃ₗ[F] (P ⊗[F] P) := TensorProduct.congr (LinearEquiv.refl F P) α
  let Θ : W ≃ₗ[F] P ⊗[F] P := Φ.trans Ψ
  let cj : (W ≃ₗ[F] W) →* ((P ⊗[F] P) ≃ₗ[F] (P ⊗[F] P)) := conjHom Θ
  have hΘsymm : ∀ p q : P, Θ.symm (p ⊗ₜ[F] q) = Φ.symm (p ⊗ₜ[F] α.symm q) := by
    intro p q
    simp [Θ, Ψ]
  have hcj_a₀ : ∀ p q : P, cj a₀ (p ⊗ₜ[F] q) = q ⊗ₜ[F] α (β p) := by
    intro p q
    show Θ (a₀ (Θ.symm (p ⊗ₜ[F] q))) = _
    rw [hΘsymm]
    show Ψ (Φ (a₀ (Φ.symm (p ⊗ₜ[F] α.symm q)))) = _
    rw [hαβ]
    simp [Ψ]
  have hw1 : β.trans α = 1 := by
    apply eq_of_tensor_square_eq
    intro u v
    have h2 := congrArg (fun f : W ≃ₗ[F] W => cj f (u ⊗ₜ[F] v)) ha₀2
    simp only [map_mul, map_one, LinearEquiv.mul_apply, hcj_a₀] at h2
    exact h2
  have hcj_flip : ∀ z, cj a₀ z = TensorProduct.comm F P P z := by
    intro z
    refine LinearMap.congr_fun (f := (cj a₀).toLinearMap)
      (g := (TensorProduct.comm F P P).toLinearMap) (TensorProduct.ext' fun p q => ?_) z
    simp only [LinearEquiv.coe_coe, hcj_a₀, TensorProduct.comm_tmul]
    rw [show α (β p) = p from LinearEquiv.congr_fun hw1 p]
  have hcj_b : ∀ b ∈ B, ∃ x y : P ≃ₗ[F] P, ∀ p q, cj b (p ⊗ₜ[F] q) = x p ⊗ₜ[F] y q := by
    intro b hb
    obtain ⟨x, y, hxy⟩ := hblock b hb
    refine ⟨x, α.symm.trans (y.trans α), fun p q => ?_⟩
    show Θ (b (Θ.symm (p ⊗ₜ[F] q))) = _
    rw [hΘsymm]
    show Ψ (Φ (b (Φ.symm (p ⊗ₜ[F] α.symm q)))) = _
    rw [hxy]
    simp [Ψ]
  let B'' : Subgroup ((P ⊗[F] P) ≃ₗ[F] (P ⊗[F] P)) := B.map cj
  have hform : ∀ b ∈ B'', ∃ x y : P ≃ₗ[F] P, ∀ u v, b (u ⊗ₜ[F] v) = x u ⊗ₜ[F] y v := by
    intro b hb
    obtain ⟨b₀, hb₀, rfl⟩ := Subgroup.mem_map.1 hb
    exact hcj_b b₀ hb₀
  have hcomm : ∀ b ∈ B'', ∀ w, b (TensorProduct.comm F P P w) =
      TensorProduct.comm F P P (b w) := by
    intro b hb w
    obtain ⟨b₀, hb₀, rfl⟩ := Subgroup.mem_map.1 hb
    rw [← hcj_flip, ← LinearEquiv.mul_apply, ← map_mul, hBa₀ b₀ hb₀, map_mul,
      LinearEquiv.mul_apply]
    exact hcj_flip _
  have hfix : ∀ b ∈ B'', ∀ w, b (TensorProduct.comm F P P w - w) =
      TensorProduct.comm F P P w - w := by
    intro b hb w
    obtain ⟨b₀, hb₀, rfl⟩ := Subgroup.mem_map.1 hb
    have h1 : cj a₀ w - w = Θ (a₀ (Θ.symm w) - Θ.symm w) := by
      rw [map_sub, LinearEquiv.apply_symm_apply]; rfl
    rw [← hcj_flip, h1]
    show Θ (b₀ (Θ.symm (Θ (a₀ (Θ.symm w) - Θ.symm w)))) = _
    rw [LinearEquiv.symm_apply_apply, hq b₀ hb₀]
  have hP2 : IsPGroup 2 B'' := fun g => ⟨1, by
    obtain ⟨g, hg⟩ := g
    obtain ⟨b₀, hb₀, rfl⟩ := Subgroup.mem_map.1 hg
    apply Subtype.ext
    show (cj b₀) ^ (2 ^ 1) = 1
    rw [pow_one, pow_two, ← map_mul, hB2 b₀ hb₀, map_one]⟩
  obtain ⟨γ, hγ1, hγ2, hγ3, hγ4, hγ5, hγ6, hγ7⟩ :=
    quadratic_tensor_flip_factor_kernel hD B'' hform hcomm hfix
  have hB''ne : B'' ≠ ⊥ := by
    intro h
    apply hB0
    exact (Subgroup.map_eq_bot_iff_of_injective B (conjHom_injective Θ)).1 h
  by_cases hD3 : 3 ≤ Module.finrank F P
  · exact hB''ne (hγ4 hD3)
  · have hD2 : Module.finrank F P = 2 := by omega
    obtain ⟨hle, himp⟩ := hγ6 hD2 hP2
    have hdim : Module.finrank F (fixGL B'') ≤ 2 := himp hB''ne
    have hWfin : Module.Finite F W := Module.Finite.equiv Θ.symm
    have hB''card : Nat.card B'' = Nat.card B :=
      Subgroup.card_map_of_injective (conjHom_injective Θ)
    have hWcard : Nat.card W = Nat.card F ^ (Module.finrank F P * Module.finrank F P) := by
      rw [Nat.card_congr Θ.toEquiv, Module.natCard_eq_pow_finrank (K := F),
        Module.finrank_tensorProduct]
    have hfB : Nat.card (fixGL B) = Nat.card F ^ Module.finrank F (fixGL B) :=
      Module.natCard_eq_pow_finrank (K := F)
    have hYfix : (fixGL B).map Θ.toLinearMap ≤ fixGL B'' := by
      rintro _ ⟨w, hw, rfl⟩
      rw [mem_fixGL]
      intro b hb
      obtain ⟨b₀, hb₀, rfl⟩ := Subgroup.mem_map.1 hb
      show Θ (b₀ (Θ.symm (Θ w))) = Θ w
      rw [LinearEquiv.symm_apply_apply, mem_fixGL.1 hw b₀ hb₀]
    have hf2 : Module.finrank F (fixGL B) ≤ 2 := by
      have h1 : Module.finrank F ((fixGL B).map Θ.toLinearMap) = Module.finrank F (fixGL B) :=
        LinearEquiv.finrank_map_eq Θ _
      have h2 := Submodule.finrank_mono hYfix
      omega
    have hq2 : 2 ≤ Nat.card F := by
      have := Finite.one_lt_card (α := F)
      omega
    rw [hWcard, hD2, hfB, ← hB''card] at hoff
    have h3 : Nat.card F ^ (2 * 2) ≤ Nat.card F * Nat.card F ^ 2 :=
      hoff.trans (Nat.mul_le_mul hle (Nat.pow_le_pow_right (by omega) hf2))
    have h4 : Nat.card F ^ 3 < Nat.card F ^ (2 * 2) :=
      Nat.pow_lt_pow_right (by omega) (by norm_num)
    have h5 : Nat.card F * Nat.card F ^ 2 = Nat.card F ^ 3 := by ring
    omega

end Core

section Tensor

variable {F : Type u} [Field F] {U : Type u} [AddCommGroup U] [Module F U]

theorem false_of_diagonal_tensor [Finite F] [CharP F 2] [Module.Finite F U]
    (hd : 2 ≤ Module.finrank F U) {s : ℕ} (hs : 2 ≤ s)
    (A : Subgroup ((⨂[F] _ : Fin s, U) ≃ₗ[F] ⨂[F] _ : Fin s, U)) [CFSG.IsElementaryAbelian 2 A]
    (hperm : ∀ a ∈ A, ∀ i, ∃ j, (factorAlg i).map (a.conjAlgEquiv F).toAlgHom = factorAlg j)
    (htrans : ∀ i j, ∃ a ∈ A, (factorAlg i).map (a.conjAlgEquiv F).toAlgHom = factorAlg j)
    (B : Subgroup ((⨂[F] _ : Fin s, U) ≃ₗ[F] ⨂[F] _ : Fin s, U)) (hBA : B ≤ A) (hB0 : B ≠ ⊥)
    (hBfix : ∀ b ∈ B, ∀ i,
      (factorAlg i).map (b.conjAlgEquiv F).toAlgHom = factorAlg i)
    (hBq : ∀ a ∈ A, ∀ b ∈ B, ∀ w, b (a w - w) = a w - w)
    (hoffB : Nat.card (⨂[F] _ : Fin s, U) ≤ Nat.card B * Nat.card (fixGL B)) : False := by
  classical
  have hmfW : Module.Finite F (⨂[F] _ : Fin s, U) :=
    Module.Finite.of_basis (Basis.piTensorProduct (fun _ : Fin s => Module.finBasis F U))
  have hWfin : Finite (⨂[F] _ : Fin s, U) := Module.finite_of_finite F
  have hAfin : Finite A :=
    Finite.of_injective (fun a : A => ((a : (⨂[F] _ : Fin s, U) ≃ₗ[F] ⨂[F] _ : Fin s, U) :
      (⨂[F] _ : Fin s, U) → ⨂[F] _ : Fin s, U))
      (fun a b h => Subtype.ext (LinearEquiv.ext fun w => congrFun h w))
  obtain ⟨π, hπ⟩ := exists_perm_hom hd A hperm
  have hinj := factorAlg_index_injective (F := F) (U := U) hd (s := s)
  have htr : ∀ i j, ∃ a : A, π a i = j := by
    intro i j
    obtain ⟨a, ha, hmap⟩ := htrans i j
    refine ⟨⟨a, ha⟩, ?_⟩
    apply hinj
    show factorAlg (F := F) (V := fun _ : Fin s => U) (π ⟨a, ha⟩ i) =
      factorAlg (F := F) (V := fun _ : Fin s => U) j
    rw [← hπ ⟨a, ha⟩ i]
    exact hmap
  obtain ⟨a₀, A₁, S, ha₀1, hdich, hS1, hS2, hi₀⟩ := exists_halving hs A π htr
  have hsq : ∀ a : A, a * a = 1 := fun a => by
    have := Monoid.exponent_dvd_iff_forall_pow_eq_one.1
      (CFSG.IsElementaryAbelian.exponent_dvd_p 2 A) a
    rwa [pow_two] at this
  have hcomm : ∀ a b : A, a * b = b * a := fun a b =>
    (IsMulCommutative.is_comm (M := A)).comm a b
  have hτ2 : ∀ i, π a₀ (π a₀ i) = i := by
    intro i
    rw [← Equiv.Perm.mul_apply, ← map_mul, hsq, map_one]
    rfl
  obtain ⟨E, hE1, hE2, hE3⟩ := exists_regroup S (π a₀) (hS2 a₀ ha₀1) hτ2
  have : Fintype {i : Fin s // i ∈ S} := Fintype.ofFinite _
  have hmfP : Module.Finite F (⨂[F] _ : {i : Fin s // i ∈ S}, U) :=
    Module.Finite.of_basis (Basis.piTensorProduct (fun _ : {i : Fin s // i ∈ S} =>
      Module.finBasis F U))
  let Φ : (⨂[F] _ : Fin s, U) ≃ₗ[F] (⨂[F] _ : {i : Fin s // i ∈ S}, U) ⊗[F]
      (⨂[F] _ : {i : Fin s // i ∈ S}, U) := phiEquiv E
  have hblockA : ∀ b ∈ A₁.map A.subtype, ∃ x y : (⨂[F] _ : {i : Fin s // i ∈ S}, U) ≃ₗ[F]
      (⨂[F] _ : {i : Fin s // i ∈ S}, U), ∀ p q, Φ (b (Φ.symm (p ⊗ₜ[F] q))) = x p ⊗ₜ[F] y q := by
    intro b hb
    obtain ⟨b₀, hb₀, rfl⟩ := Subgroup.mem_map.1 hb
    obtain ⟨g, hg⟩ := full_matrix_tensor_factor_normalizer hd hs (π b₀) b₀.1 (hπ b₀)
    obtain ⟨ν₁, ν₂, h1, h2⟩ := hE3 (π b₀) (hS1 b₀ hb₀)
    refine ⟨opT ν₁ (fun l => g (E.symm (Sum.inl l))),
      opT ν₂ (fun l => g (E.symm (Sum.inr l))), fun p q => ?_⟩
    have hg' : (b₀ : (⨂[F] _ : Fin s, U) ≃ₗ[F] ⨂[F] _ : Fin s, U) = opT (π b₀) g := hg
    show Φ (b₀.1 (Φ.symm (p ⊗ₜ[F] q))) = _
    rw [hg', ← TensorProduct.congr_tmul]
    exact phi_conj_block E (π b₀) g ν₁ ν₂ h1 h2 (p ⊗ₜ[F] q)
  have hswap : ∃ α β : (⨂[F] _ : {i : Fin s // i ∈ S}, U) ≃ₗ[F]
      (⨂[F] _ : {i : Fin s // i ∈ S}, U), ∀ p q,
      Φ (a₀.1 (Φ.symm (p ⊗ₜ[F] q))) = α q ⊗ₜ[F] β p := by
    obtain ⟨g, hg⟩ := full_matrix_tensor_factor_normalizer hd hs (π a₀) a₀.1 (hπ a₀)
    refine ⟨PiTensorProduct.congr (fun l => g (E.symm (Sum.inl l))),
      PiTensorProduct.congr (fun l => g (E.symm (Sum.inr l))), fun p q => ?_⟩
    have hg' : (a₀ : (⨂[F] _ : Fin s, U) ≃ₗ[F] ⨂[F] _ : Fin s, U) = opT (π a₀) g := hg
    show Φ (a₀.1 (Φ.symm (p ⊗ₜ[F] q))) = _
    rw [hg', phi_conj_swap E (π a₀) g hE1 hE2, TensorProduct.comm_tmul, TensorProduct.congr_tmul]
  have hcard : 1 ≤ Fintype.card {i : Fin s // i ∈ S} :=
    Fintype.card_pos_iff.2 ⟨⟨_, hi₀⟩⟩
  have hfinrank := finrank_piTensor_const (F := F) (U := U) {i : Fin s // i ∈ S}
  have hD : 2 ≤ Module.finrank F (⨂[F] _ : {i : Fin s // i ∈ S}, U) := by
    rw [hfinrank]
    calc 2 ≤ Module.finrank F U := hd
      _ = Module.finrank F U ^ 1 := (pow_one _).symm
      _ ≤ Module.finrank F U ^ Fintype.card {i : Fin s // i ∈ S} :=
        Nat.pow_le_pow_right (by omega) hcard
  have hBA₁ : ∀ b ∈ B, b ∈ A₁.map A.subtype := by
    intro b hb
    have hπb : π ⟨b, hBA hb⟩ = 1 := by
      refine Equiv.ext fun i => ?_
      show π ⟨b, hBA hb⟩ i = i
      apply hinj
      show factorAlg (F := F) (V := fun _ : Fin s => U) (π ⟨b, hBA hb⟩ i) =
        factorAlg (F := F) (V := fun _ : Fin s => U) i
      rw [← hπ ⟨b, hBA hb⟩ i]
      exact hBfix b hb i
    refine Subgroup.mem_map.2 ⟨⟨b, hBA hb⟩, ?_, rfl⟩
    by_contra hnot
    have h2 := hS2 ⟨b, hBA hb⟩ hnot ⟨0, by omega⟩
    rw [hπb] at h2
    exact (h2.1 hi₀) hi₀
  have hAab : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hcomm ⟨a, ha⟩ ⟨b, hb⟩)
  have hA2 : ∀ a ∈ A, a * a = 1 := fun a ha => congrArg Subtype.val (hsq ⟨a, ha⟩)
  exact flip_core_false hD Φ B hB0 (fun b hb => hA2 b (hBA hb)) a₀.1 (hA2 a₀.1 a₀.2)
    (fun b hb => hAab b (hBA hb) a₀.1 a₀.2) (fun b hb => hblockA b (hBA₁ b hb)) hswap
    (fun b hb w => hBq a₀.1 a₀.2 b hb w) hoffB

end Tensor

end CFSG.Quasithin.B15P4
