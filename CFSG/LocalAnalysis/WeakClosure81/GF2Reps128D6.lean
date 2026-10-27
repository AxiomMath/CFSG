module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps128D5

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.PartTwo Subgroup
open scoped Matrix MatrixGroups
open CFSG.Quasithin.H13.H11P

theorem mem_sup_zpowers_of_swap {W : Type} [CommGroup W] {L : Subgroup (MulAut W)}
    {t : MulAut W} (hW : ∀ w : W, w ^ 2 = 1) (ht2 : orderOf t = 2) {K : Type} [Field K]
    [Finite K] {n : ℕ} (hK : Nat.card K = 2 ^ n) (hn : 2 ≤ n)
    (hT : IsMatTensor2 L (L.map (MulAut.conj t).toMonoidHom) K)
    (hrk : rkIdx (fixV (Subgroup.zpowers t)) = n) {s : MulAut W} (hs2 : s * s = 1)
    (hLs : L.map (MulAut.conj s).toMonoidHom = L.map (MulAut.conj t).toMonoidHom)
    (hrks : rkIdx (fixV (Subgroup.zpowers s)) = n) :
    s ∈ L ⊔ L.map (MulAut.conj t).toMonoidHom ⊔ Subgroup.zpowers t := by
  classical
  set L' := L.map (MulAut.conj t).toMonoidHom with hL'
  obtain ⟨φ₁, φ₂, ψ, h₁, h₂⟩ := hT
  have h2 : (2 : K) = 0 := by
    have h1 := congrArg (fun w => Multiplicative.toAdd (ψ w))
      (hW (ψ.symm (Multiplicative.ofAdd (1 : Mat K))))
    simp only [map_pow, MulEquiv.apply_symm_apply, toAdd_pow, toAdd_ofAdd, map_one,
      toAdd_one] at h1
    have h3 := congrFun (congrFun h1 0) 0
    simpa using h3
  have : CharP K 2 := CharTwo.of_one_ne_zero_of_two_eq_zero one_ne_zero h2
  have ht : t * t = 1 := by rw [← sq, ← ht2, pow_orderOf_eq_one]
  have hΦapp : ∀ (a : MulAut W) (v : VM K), MulAut.congr ψ a v = ψ (a (ψ.symm v)) := fun a v => by
    rw [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.trans_apply]
  have hΦ₁ : ∀ (x : MulAut W) (hx : x ∈ L), MulAut.congr ψ x = rho (φ₁ ⟨x, hx⟩, 1) := by
    intro x hx
    refine eq_of_addMap fun X => ?_
    rw [addMap_rho, Matrix.SpecialLinearGroup.coe_one, Matrix.transpose_one, Matrix.mul_one,
      addMap_apply, hΦapp]
    have := h₁ ⟨x, hx⟩ (ψ.symm (Multiplicative.ofAdd X))
    rwa [MulEquiv.apply_symm_apply, toAdd_ofAdd] at this
  have hΦ₂ : ∀ (y : MulAut W) (hy : y ∈ L'), MulAut.congr ψ y = rho (1, φ₂ ⟨y, hy⟩) := by
    intro y hy
    refine eq_of_addMap fun X => ?_
    rw [addMap_rho, Matrix.SpecialLinearGroup.coe_one, Matrix.one_mul, addMap_apply, hΦapp]
    have := h₂ ⟨y, hy⟩ (ψ.symm (Multiplicative.ofAdd X))
    rwa [MulEquiv.apply_symm_apply, toAdd_ofAdd] at this
  have hΦ₁' : ∀ g, MulAut.congr ψ (φ₁.symm g : MulAut W) = rho (g, 1) := fun g => by
    rw [hΦ₁ _ (φ₁.symm g).2, Subtype.coe_eta, MulEquiv.apply_symm_apply]
  have hΦ₂' : ∀ h, MulAut.congr ψ (φ₂.symm h : MulAut W) = rho (1, h) := fun h => by
    rw [hΦ₂ _ (φ₂.symm h).2, Subtype.coe_eta, MulEquiv.apply_symm_apply]
  have hmapLL : (L ⊔ L').map (MulAut.congr ψ).toMonoidHom = Lm K := by
    rw [Subgroup.map_sup]
    refine le_antisymm (sup_le ?_ ?_) ?_
    · rintro _ ⟨x, hx, rfl⟩
      exact ⟨_, (hΦ₁ x hx).symm⟩
    · rintro _ ⟨y, hy, rfl⟩
      exact ⟨_, (hΦ₂ y hy).symm⟩
    · rintro _ ⟨p, rfl⟩
      have hp : rho p = rho (p.1, 1) * rho (1, p.2) := by rw [rho_mul_mk, mul_one, one_mul]
      rw [hp, ← hΦ₁', ← hΦ₂']
      exact mul_mem (Subgroup.mem_sup_left (Subgroup.mem_map_of_mem _ (φ₁.symm p.1).2))
        (Subgroup.mem_sup_right (Subgroup.mem_map_of_mem _ (φ₂.symm p.2).2))
  have key : ∀ x : MulAut W, x * x = 1 → L.map (MulAut.conj x).toMonoidHom = L' →
      rkIdx (fixV (Subgroup.zpowers x)) = n →
      ∃ P Q : SL(2, K), ∀ X, addMap (MulAut.congr ψ x) X = (P : Mat K) * Xᵀ * (Q : Mat K)ᵀ := by
    intro x hx hLx hrkx
    have hxinv : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx
    have h2nd : L'.map (MulAut.conj x).toMonoidHom ≤ L := by
      rw [← hLx]
      rintro _ ⟨_, ⟨y, hy, rfl⟩, rfl⟩
      have e : (MulAut.conj x).toMonoidHom ((MulAut.conj x).toMonoidHom y) = y := by
        rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, MulAut.conj_apply, hxinv]
        calc x * (x * y * x) * x = (x * x) * y * (x * x) := by group
          _ = y := by rw [hx, one_mul, mul_one]
      rw [e]
      exact hy
    have hconj : ∀ y ∈ L ⊔ L', x * y * x⁻¹ ∈ L ⊔ L' := by
      have hle : (L ⊔ L').map (MulAut.conj x).toMonoidHom ≤ L ⊔ L' := by
        rw [Subgroup.map_sup, hLx]
        exact sup_le le_sup_right (h2nd.trans le_sup_left)
      intro y hy
      exact hle ⟨y, hy, rfl⟩
    set x' := MulAut.congr ψ x with hx'
    have hx'x' : x' * x' = 1 := by rw [hx', ← map_mul, hx, map_one]
    have hfwd : ∀ h ∈ Lm K, x' * h * x'⁻¹ ∈ Lm K := by
      intro h hh
      rw [← hmapLL] at hh ⊢
      obtain ⟨y, hy, rfl⟩ := hh
      refine ⟨x * y * x⁻¹, hconj y hy, ?_⟩
      simp only [MulEquiv.coe_toMonoidHom, map_mul, map_inv, hx']
    have hN : x' ∈ NLm K := by
      rw [Subgroup.mem_normalizer_iff]
      intro h
      refine ⟨hfwd h, fun hh => ?_⟩
      have e : x' * (x' * h * x'⁻¹) * x'⁻¹ = h := by
        calc x' * (x' * h * x'⁻¹) * x'⁻¹ = (x' * x') * h * (x' * x')⁻¹ := by group
          _ = h := by rw [hx'x', one_mul, inv_one, mul_one]
      rw [← e]
      exact hfwd _ hh
    have hnot : x' ∉ Lm K := by
      rintro ⟨⟨P₀, Q₀⟩, hPQ⟩
      have hg : uu (1 : K) ≠ 1 := fun h => one_ne_zero (uu_injective (h.trans uu_zero.symm))
      have hmem : (MulAut.conj x).toMonoidHom (φ₁.symm (uu 1) : MulAut W) ∈ L' :=
        hLx ▸ Subgroup.mem_map_of_mem (MulAut.conj x).toMonoidHom (φ₁.symm (uu 1)).2
      have e1 := hΦ₂ _ hmem
      have e2 : MulAut.congr ψ ((MulAut.conj x).toMonoidHom (φ₁.symm (uu 1) : MulAut W)) =
          rho (P₀ * uu 1 * P₀⁻¹, Q₀ * 1 * Q₀⁻¹) := by
        rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, map_mul, map_mul, map_inv, ← hx', ← hPQ,
          hΦ₁', ← map_inv, rho_mul_mk, Prod.inv_mk, rho_mul_mk]
      have e3 := rho_injective (e2.symm.trans e1)
      have e4 : P₀ * uu 1 * P₀⁻¹ = 1 := congrArg Prod.fst e3
      apply hg
      calc uu (1 : K) = P₀⁻¹ * (P₀ * uu 1 * P₀⁻¹) * P₀ := by group
        _ = 1 := by rw [e4, mul_one, inv_mul_cancel]
    have hzp : Subgroup.zpowers x' = (Subgroup.zpowers x).map (MulAut.congr ψ).toMonoidHom := by
      rw [MonoidHom.map_zpowers]
      rfl
    have hrk' : rkIdx (fixV (Subgroup.zpowers x')) = n := by
      rw [← hrkx]
      unfold rkIdx
      rw [hzp, fixV_map_congr_equiv, Subgroup.index_map_of_bijective ψ.bijective]
    exact w4t_o4_swap_form hK hn hN hx'x' hnot hrk'
  obtain ⟨P, Q, hPQ⟩ := key t ht rfl hrk
  obtain ⟨P', Q', hP'Q'⟩ := key s hs2 hLs hrks
  have hRmap : (L ⊔ L' ⊔ Subgroup.zpowers t).map (MulAut.congr ψ).toMonoidHom =
      Lm K ⊔ Subgroup.zpowers (MulAut.congr ψ t) := by
    rw [Subgroup.map_sup, hmapLL, MonoidHom.map_zpowers]
    rfl
  have hs' : MulAut.congr ψ s ∈ Lm K ⊔ Subgroup.zpowers (MulAut.congr ψ t) := by
    rw [w4t_o4_mem_sup_iff hPQ]
    exact (w4t_o4_mem_sup_iff hP'Q' _).mp
      ((le_sup_right : _ ≤ Lm K ⊔ _) (Subgroup.mem_zpowers _))
  rw [← hRmap, Subgroup.mem_map_equiv, MulEquiv.symm_apply_apply] at hs'
  exact hs'

end CFSG.LocalAnalysis.WeakClosure81
