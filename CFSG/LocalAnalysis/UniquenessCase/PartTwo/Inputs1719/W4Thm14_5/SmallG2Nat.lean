module

public import CFSG.Quasithin.Background.SmithB42G2TenQ
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7bOffender
public import CFSG.Quasithin.Vol2.Ch11SecBK5Base11
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15RankTwoPerOffenderSemi
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15RankTwoPerOffenderG2Std
import CFSG.LocalAnalysis.RankThreeUC.AGL81U4FFDescent
import CFSG.Quasithin.Background.SmithB42G2FRank

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_5

open CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall CFSG.QuasithinUnique.Setup.X7b
open CFSG.Quasithin.Vol2.Ch11.SecB.K5 CFSG.Quasithin.B42G2Ten CFSG.LocalAnalysis.RankThreeUC.S15
open scoped Matrix

@[expose] def toSix (K : Type) [AddCommGroup K] : (Ix3 → K) ≃+ (Fin 6 → K) where
  toFun w i := w (e6.symm i)
  invFun u k := u (e6 k)
  left_inv w := funext fun k => by simp
  right_inv u := funext fun i => by simp
  map_add' _ _ := rfl

theorem g2Six_mulVec_toSix {K : Type} [Field K] [CharP K 2] (g : ↥(cayleyGroup K))
    (w : Ix3 → K) :
    ((g2Six g : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) *ᵥ toSix K w = toSix K (g2Act g w) := by
  have hM : ((g2Six g : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) =
      ((g2Mat g : GL Ix3 K) : Matrix Ix3 Ix3 K).submatrix e6.symm e6.symm := rfl
  rw [hM, Matrix.submatrix_mulVec_equiv]
  funext i
  have hw : toSix K w ∘ e6.symm.symm = w := by
    funext k
    simp [toSix]
  simp only [Function.comp_apply]
  rw [hw]
  exact congrFun (g2Mat_mulVec g w) (e6.symm i)

variable {K : Type} [Field K] [Finite K] [CharP K 2] {f : ℕ}
  {M : Type} [AddCommGroup M] [Module (ZMod 2) M] [Finite M]

theorem nontrivial_cayleyGroup (hq : 1 < Nat.card K) : Nontrivial ↥(cayleyGroup K) := by
  have h1 : 1 < Nat.card ↥(cayleyGroup K) := by
    rw [CFSG.Quasithin.Vol2.KGNat.card_cayleyGroup]
    have h6 : 1 < Nat.card K ^ 6 := Nat.one_lt_pow (by norm_num) hq
    have h2 : 1 < Nat.card K ^ 2 := Nat.one_lt_pow (by norm_num) hq
    calc 1 < Nat.card K ^ 6 := h6
      _ ≤ Nat.card K ^ 6 * ((Nat.card K ^ 6 - 1) * (Nat.card K ^ 2 - 1)) :=
        Nat.le_mul_of_pos_right _ (Nat.mul_pos (by omega) (by omega))
  have : Finite ↥(cayleyGroup K) := Nat.finite_of_card_ne_zero (by omega)
  exact Finite.one_lt_card_iff_nontrivial.mp h1

private theorem natCard_eq_two_pow_finrank (V : Type) [AddCommGroup V] [Module (ZMod 2) V]
    [Module.Finite (ZMod 2) V] : Nat.card V = 2 ^ Module.finrank (ZMod 2) V := by
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2) (V := V), Nat.card_zmod]

omit [Finite K] in
theorem dispRank_eq_mul_rank_of_natural (hK : Nat.card K = 2 ^ f)
    (π : ↥(cayleyGroup K) →* (M ≃ₗ[ZMod 2] M)) (φ : M ≃+ (Ix3 → K))
    (hφ : ∀ g w, φ (π g w) = g2Act g (φ w)) (z : ↥(cayleyGroup K)) :
    dispRank (π z) = f * (repQ z - 1).rank := by
  classical
  have : Module.Finite (ZMod 2) M := Module.Finite.of_finite
  set N : (Ix3 → K) →ₗ[K] (Ix3 → K) := (repQ z - 1).mulVecLin with hN
  set R := LinearMap.range ((π z).toLinearMap - 1) with hR
  have hφR : ∀ w : M, φ (((π z).toLinearMap - 1) w) = N (φ w) := fun w => by
    rw [LinearMap.sub_apply, Module.End.one_apply, map_sub, LinearEquiv.coe_coe, hφ, hN,
      Matrix.mulVecLin_apply, Matrix.sub_mulVec, Matrix.one_mulVec, repQ_mulVec]
  have hcard : Nat.card R = Nat.card (LinearMap.range N) := by
    refine Nat.card_congr
      { toFun := fun r => ⟨φ r, ?_⟩
        invFun := fun s => ⟨φ.symm s, ?_⟩
        left_inv := fun r => Subtype.ext (φ.symm_apply_apply _)
        right_inv := fun s => Subtype.ext (φ.apply_symm_apply _) }
    · obtain ⟨w, hw⟩ := r.2
      exact ⟨φ w, by rw [← hφR, hw]⟩
    · obtain ⟨u, hu⟩ := s.2
      refine ⟨φ.symm u, φ.injective ?_⟩
      rw [hφR, φ.apply_symm_apply, hu, φ.apply_symm_apply]
  have h1 : Nat.card R = 2 ^ dispRank (π z) := natCard_eq_two_pow_finrank R
  have h2 : Nat.card (LinearMap.range N) = 2 ^ (f * (repQ z - 1).rank) := by
    rw [Module.natCard_eq_pow_finrank (K := K), hK, ← pow_mul]
    rfl
  rw [hcard, h2] at h1
  exact (Nat.pow_right_injective le_rfl h1).symm

omit [Finite K] [CharP K 2] [Finite M] in
private theorem fixed_eq_zero_of_irr (π : ↥(cayleyGroup K) →* (M ≃ₗ[ZMod 2] M))
    (hπ : Function.Injective π)
    (hirr : ∀ U : Submodule (ZMod 2) M, (∀ g, ∀ u ∈ U, π g u ∈ U) → U = ⊥ ∨ U = ⊤)
    (hnt : ∃ g : ↥(cayleyGroup K), g ≠ 1) {v : M} (hv : ∀ g, π g v = v) : v = 0 := by
  let U : Submodule (ZMod 2) M :=
    { carrier := {w | ∀ g, π g w = w}
      add_mem' := fun {x y} hx hy g => by rw [map_add, hx g, hy g]
      zero_mem' := fun g => map_zero _
      smul_mem' := fun c x hx g => by rw [map_smul, hx g] }
  have hU : ∀ g, ∀ u ∈ U, π g u ∈ U := fun g u hu h => by
    have := hu (g⁻¹ * h * g)
    calc π h (π g u) = π g (π (g⁻¹ * h * g) u) := by
          simp only [map_mul, LinearEquiv.mul_apply]
          rw [← LinearEquiv.mul_apply (π g) (π g⁻¹), ← map_mul, mul_inv_cancel, map_one]
          rfl
      _ = π g u := by rw [this]
  rcases hirr U hU with h | h
  · have : v ∈ U := hv
    rw [h] at this
    exact this
  · exfalso
    obtain ⟨g, hg⟩ := hnt
    apply hg
    apply hπ
    refine LinearEquiv.ext fun w => ?_
    have hw : w ∈ U := h ▸ Submodule.mem_top
    rw [map_one]
    exact hw g

omit [Finite K] [CharP K 2] [Finite M] in
private theorem span_comm_eq_top (π : ↥(cayleyGroup K) →* (M ≃ₗ[ZMod 2] M))
    (hπ : Function.Injective π)
    (hirr : ∀ U : Submodule (ZMod 2) M, (∀ g, ∀ u ∈ U, π g u ∈ U) → U = ⊥ ∨ U = ⊤)
    (hnt : ∃ g : ↥(cayleyGroup K), g ≠ 1) :
    Submodule.span (ZMod 2) {w | ∃ l ∈ π.range, ∃ x ∈ (⊤ : Submodule (ZMod 2) M),
      w = (l : M ≃ₗ[ZMod 2] M) x - x} = ⊤ := by
  set C := Submodule.span (ZMod 2) {w | ∃ l ∈ π.range, ∃ x ∈ (⊤ : Submodule (ZMod 2) M),
      w = (l : M ≃ₗ[ZMod 2] M) x - x} with hC
  have hCinv : ∀ g, ∀ u ∈ C, π g u ∈ C := by
    intro g u hu
    refine Submodule.span_induction (p := fun u _ => π g u ∈ C) ?_ ?_ ?_ ?_ hu
    · rintro _ ⟨l, ⟨h, rfl⟩, x, -, rfl⟩
      refine Submodule.subset_span ⟨π (g * h * g⁻¹), ⟨_, rfl⟩, π g x, Submodule.mem_top, ?_⟩
      simp only [map_sub, map_mul, map_inv, LinearEquiv.mul_apply]
      rw [← LinearEquiv.mul_apply (π g)⁻¹ (π g), inv_mul_cancel]
      rfl
    · simp only [map_zero]
      exact C.zero_mem
    · intro x y _ _ hx hy
      rw [map_add]
      exact C.add_mem hx hy
    · intro c x _ hx
      rw [map_smul]
      exact C.smul_mem c hx
  rcases hirr C hCinv with h | h
  · exfalso
    obtain ⟨g, hg⟩ := hnt
    apply hg
    apply hπ
    refine LinearEquiv.ext fun w => ?_
    have hw : π g w - w ∈ C := Submodule.subset_span ⟨π g, ⟨g, rfl⟩, w, Submodule.mem_top, rfl⟩
    rw [h, Submodule.mem_bot, sub_eq_zero] at hw
    rw [map_one]
    exact hw
  · exact h

theorem two_mul_le_dispRank_of_natural
    (hK : Nat.card K = 2 ^ f) (hf : 2 ≤ f)
    (π : ↥(cayleyGroup K) →* (M ≃ₗ[ZMod 2] M)) (hπ : Function.Injective π)
    (hirr : ∀ U : Submodule (ZMod 2) M, (∀ g, ∀ u ∈ U, π g u ∈ U) → U = ⊥ ∨ U = ⊤)
    (φ : M ≃+ (Ix3 → K)) (hφ : ∀ g w, φ (π g w) = g2Act g (φ w))
    (a : M ≃ₗ[ZMod 2] M) (ha2 : a * a = 1) (ha1 : a ≠ 1)
    (hnorm : ∀ x, ∃ y, a * π x * a⁻¹ = π y) :
    2 * f ≤ dispRank a := by
  classical
  have : Module.Finite (ZMod 2) M := Module.Finite.of_finite
  have hq : 1 < Nat.card K := by
    rw [hK]
    exact Nat.one_lt_two_pow (by omega)
  have hnt : ∃ g : ↥(cayleyGroup K), g ≠ 1 := by
    have := nontrivial_cayleyGroup hq
    exact exists_ne 1
  set L : Subgroup (M ≃ₗ[ZMod 2] M) := π.range with hLdef
  let eL : ↥(cayleyGroup K) ≃* ↥L := MonoidHom.ofInjective hπ
  have heL : ∀ l : ↥L, (l : M ≃ₗ[ZMod 2] M) = π (eL.symm l) := fun l => by
    conv_lhs => rw [← eL.apply_symm_apply l]
    rfl
  let ρ : Representation (ZMod 2) (M ≃ₗ[ZMod 2] M) M :=
    LinearEquiv.automorphismGroup.toLinearMapMonoidHom
  have hρ : ∀ g v, ρ g v = g v := fun _ _ => rfl
  let ψ₆ : M ≃+ (Fin 6 → K) := φ.trans (toSix K)
  have hψ₆ : ∀ g w, ψ₆ (π g w) =
      ((g2Six g : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) *ᵥ ψ₆ w := fun g w => by
    show toSix K (φ (π g w)) = _
    rw [hφ, ← g2Six_mulVec_toSix]
    rfl
  let N : NatQuot ρ L K 6 :=
    { Mat := g2Six.comp eL.symm.toMonoidHom
      mat_inj := g2Six_injective.comp eL.symm.injective
      I := ⊤
      inv := fun _ _ _ _ => Submodule.mem_top
      π := ψ₆.toAddMonoidHom.comp (⊤ : Submodule (ZMod 2) M).subtype.toAddMonoidHom
      surj := fun u => ⟨⟨ψ₆.symm u, Submodule.mem_top⟩, ψ₆.apply_symm_apply u⟩
      equiv := fun l v => by
        show ψ₆ (ρ l v) = _
        rw [hρ, heL l, hψ₆]
        rfl
      ker_iff := fun v => by
        constructor
        · intro h l _
          have hv : (v : M) = 0 := ψ₆.injective (h.trans (map_zero ψ₆).symm)
          rw [hv, map_zero]
        · intro h
          have hv : (v : M) = 0 :=
            fixed_eq_zero_of_irr π hπ hirr hnt fun g => h (π g) ⟨g, rfl⟩
          show ψ₆ (v : M) = 0
          rw [hv, map_zero] }
  have hS : NatSchur N.Mat := fun c hc => natSchur_g2Six c fun g u => by
    have h := hc (eL g) u
    simpa [N, MulEquiv.symm_apply_apply] using h
  have hO : NatOut N.Mat := fun Mx hMx hnormM => by
    obtain ⟨g₀, hg₀⟩ := natOut_g2Six hf hK Mx hMx fun g => by
      obtain ⟨l', hl'⟩ := hnormM (eL g)
      exact ⟨eL.symm l', by simpa [N] using hl'⟩
    exact ⟨eL g₀, by simpa [N] using hg₀⟩
  have hIcomm : ∀ v ∈ N.I, v ∈ Submodule.span (ZMod 2)
      {w | ∃ l ∈ L, ∃ x ∈ N.I, w = ρ l x - x} := by
    intro v _
    have h := span_comm_eq_top π hπ hirr hnt
    have he : {w | ∃ l ∈ L, ∃ x ∈ N.I, w = ρ l x - x} = {w | ∃ l ∈ π.range,
        ∃ x ∈ (⊤ : Submodule (ZMod 2) M), w = (l : M ≃ₗ[ZMod 2] M) x - x} := rfl
    rw [he, h]
    exact Submodule.mem_top
  have hainv : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha2
  have hgN : ∀ l ∈ L, a * l * a⁻¹ ∈ L := by
    rintro _ ⟨x, rfl⟩
    obtain ⟨y, hy⟩ := hnorm x
    exact ⟨y, hy.symm⟩
  have hgN' : ∀ l ∈ L, a⁻¹ * l * a ∈ L := by
    intro l hl
    have h := hgN l hl
    rw [hainv] at h ⊢
    exact h
  have hg2 : ∀ v ∈ N.I, ρ a (ρ a v) = v := fun v _ => by
    rw [hρ, hρ, ← LinearEquiv.mul_apply, ha2]
    rfl
  obtain ⟨T, σ, hTπ, hT2, hTs⟩ :=
    N.exists_semilinear_psi hS hgN hgN' (fun v _ => Submodule.mem_top) hg2
  have hTa : ∀ v : M, ψ₆ (a v) = T (ψ₆ v) := fun v => hTπ ⟨v, Submodule.mem_top⟩
  by_cases hσ : ∀ c, σ c = c
  ·
    obtain ⟨l₀, hl₀, hal, -⟩ := N.acts_as_L_of_linear hO hIcomm hgN
      (fun v _ => Submodule.mem_top) hg2 T hTπ (fun c u => by rw [hTs, hσ])
    obtain ⟨z, rfl⟩ := hl₀
    have haz : a = π z := LinearEquiv.ext fun v => hal v Submodule.mem_top
    have hz2 : z * z = 1 := hπ (by rw [map_mul, ← haz, ha2, map_one])
    have hz1 : z ≠ 1 := fun h => ha1 (by rw [haz, h, map_one])
    rw [haz, dispRank_eq_mul_rank_of_natural hK π φ hφ z]
    have h2 := CFSG.Quasithin.B42G2F.two_le_rank_repQ hz2 hz1
    calc 2 * f = f * 2 := mul_comm 2 f
      _ ≤ f * (repQ z - 1).rank := Nat.mul_le_mul_left f h2
  ·
    push Not at hσ
    have hu0 : (Pi.single 0 1 : Fin 6 → K) ≠ 0 := by
      intro h
      have := congrFun h 0
      simp at this
    have hσσ : ∀ c, σ (σ c) = c := fun c => by
      have h := hT2 (c • Pi.single 0 1)
      rw [hTs, hTs, hT2] at h
      exact smul_left_injective K hu0 h
    have hfix := CFSG.LocalAnalysis.RankThreeUC.card_fix_sq_of_semilinear_involution
      σ.toRingHom hσσ hσ T (fun c u => hTs c u) hT2
    have hCa : Nat.card ↥(LinearMap.ker (a.toLinearMap - 1)) = Nat.card {u // T u = u} := by
      refine Nat.card_congr
        { toFun := fun v => ⟨ψ₆ v, ?_⟩
          invFun := fun u => ⟨ψ₆.symm u, ?_⟩
          left_inv := fun v => Subtype.ext (ψ₆.symm_apply_apply _)
          right_inv := fun u => Subtype.ext (ψ₆.apply_symm_apply _) }
      · have hv := v.2
        rw [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero] at hv
        rw [← hTa]
        exact congrArg ψ₆ hv
      · rw [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero]
        apply ψ₆.injective
        change ψ₆ (a (ψ₆.symm u)) = ψ₆ (ψ₆.symm u)
        rw [hTa, ψ₆.apply_symm_apply, u.2]
    have hM6 : Nat.card M = 2 ^ (6 * f) := by
      rw [Nat.card_congr ψ₆.toEquiv, Nat.card_fun, Nat.card_fin, hK, ← pow_mul, mul_comm]
    have hdimM : Module.finrank (ZMod 2) M = 6 * f := by
      rw [natCard_eq_two_pow_finrank M] at hM6
      exact Nat.pow_right_injective le_rfl hM6
    have hdimK : Module.finrank (ZMod 2) ↥(LinearMap.ker (a.toLinearMap - 1)) = 3 * f := by
      have h1 := natCard_eq_two_pow_finrank ↥(LinearMap.ker (a.toLinearMap - 1))
      rw [hCa] at h1
      rw [h1, Nat.card_fun, Nat.card_fin, hK, ← pow_mul, ← pow_mul] at hfix
      have h2 := Nat.pow_right_injective le_rfl hfix
      omega
    have hrn := LinearMap.finrank_range_add_finrank_ker (a.toLinearMap - 1)
    change 2 * f ≤ Module.finrank (ZMod 2) ↥(LinearMap.range (a.toLinearMap - 1))
    omega

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_5
