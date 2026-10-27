module

public import CFSG.LocalAnalysis.StandardType.GGSixLayerCXNonsplitKGClLift
public import CFSG.LocalAnalysis.StandardType.GGSixLayerFactsOmegaFree

public section

namespace CFSG.StandardType

namespace OmNonsplit

open Matrix QuadraticMap CFSG.ClassicalGroups.Orthogonal LayerCores

section Adj

variable {K : Type} [Field K] [Finite K] [CharP K 2] {ι : Type} [Fintype ι] [DecidableEq ι]
  {adj : Matrix ι ι K → Matrix ι ι K} (hadj : IsInvol adj)

theorem exists_coreFamily_adjCent_dvd {A : GL ι K} (hAu : A ∈ unitaryOf hadj) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hAp : A ^ p = 1) (hfree : IsUnit ((A : Matrix ι ι K) - 1))
    (hsymd : ∃ Y : Matrix ι ι K, Y * (A : Matrix ι ι K) = (A : Matrix ι ι K) * Y ∧
      Y + adj Y = 1) :
    ∃ (β : Type) (S : β → Subgroup (GL ι K)),
      IsCoreFamily (adjCent (Subgroup.zpowers A) hadj) S ∧ ∀ c, p ∣ Nat.card (S c) := by
  classical
  obtain ⟨Y, hYA, hY⟩ := hsymd
  obtain ⟨r, D, d, _, _, _, _, _, Φ, τ, hτ, π, hπ, Sf, hΦ, -, -, himg, hy, hSle, hSn, hder,
    hq⟩ := ClNonsplit.exists_coreData hadj (ClNonsplit.natCast_card_zpowers_ne_zero hp hp2 hAp)
      (ClNonsplit.adj_stab_zpowers hadj hAu)
      ⟨Y, fun _ hg => ClNonsplit.commute_of_mem_zpowers hYA hg, hY⟩
  have hΦu : Function.Injective (Units.map Φ.toMonoidHom) :=
    Units.map_injective (f := Φ.toMonoidHom) hΦ
  have hF : IsCoreFamily (adjCent (Subgroup.zpowers A) hadj)
      (fun c : {b : Fin r // b ≤ π b ∧ Sf b ≠ ⊥} =>
        (coreOf π hτ Sf c.1).map (Units.map Φ.toMonoidHom)) := by
    have h := (ClNonsplit.isCoreFamily_coreOf hτ hπ hSle hSn hder hq).map _ hΦu
    rwa [himg] at h
  refine ⟨_, _, hF, fun c => ?_⟩
  by_contra hpc
  obtain ⟨b, hbπ, hSb⟩ := c
  have hpS : ¬ p ∣ Nat.card (Sf b) := by
    intro h
    apply hpc
    show p ∣ Nat.card ((coreOf π hτ Sf b).map (Units.map Φ.toMonoidHom))
    rw [Subgroup.card_map_of_injective hΦu,
      Nat.card_congr (Equiv.ofBijective _ (bijective_coreOf hτ hπ hSle b))]
    exact h
  have hMB := ClNonsplit.fix_of_not_dvd hadj hΦ hτ hπ himg hy hSle hder
    ((hq b).resolve_left hSb).1 hp hp2 hpS hAu hAp rfl
  have h1 : ∀ M ∈ (coreOf π hτ Sf b).map (Units.map Φ.toMonoidHom), M = 1 := by
    intro M hM
    apply Units.ext
    rw [Units.val_one]
    exact hfree.mul_left_inj.mp ((hMB M hM).2.trans (Matrix.one_mul _).symm)
  obtain ⟨u, u', huu⟩ := LayerFacts.exists_mul_ne_of_isQuasisimple (hF.2.2.1 ⟨b, hbπ, hSb⟩)
  have hu : u = 1 := Subtype.ext (h1 u u.2)
  have hu' : u' = 1 := Subtype.ext (h1 u' u'.2)
  exact huu (by rw [hu, hu'])

end Adj

section Orth

variable {K : Type} [Field K] [Finite K] [CharP K 2] {W : Type} [AddCommGroup W] [Module K W]
  [FiniteDimensional K W] {Q : QuadraticForm K W}

theorem exists_coreFamily_orthFree_dvd (hQ : (polarBilin Q).Nondegenerate) {a : W ≃ₗ[K] W}
    (haO : a ∈ TauCeti.QuadraticMap.orthogonalGroup Q) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hap : a ^ p = 1) (hfree : ∀ w : W, a w = w → w = 0) :
    ∃ (β : Type) (S : β → Subgroup (W ≃ₗ[K] W)),
      IsCoreFamily (Subgroup.centralizer (Subgroup.zpowers a : Set (W ≃ₗ[K] W)) ⊓
        TauCeti.QuadraticMap.orthogonalGroup Q) S ∧ ∀ c, p ∣ Nat.card (S c) := by
  classical
  have := finite_linearEquiv (K := K) (V := W)
  set A := Subgroup.zpowers a with hAdef
  have : Fintype A := Fintype.ofFinite A
  have hodd : Odd (Nat.card A) := by
    rw [hAdef, Nat.card_zpowers]
    exact Odd.of_dvd_nat (hp.odd_of_ne_two hp2) (orderOf_dvd_of_pow_eq_one hap)
  have hA : (Fintype.card A : K) ≠ 0 := by
    rw [← Nat.card_eq_fintype_card]
    exact natCast_card_ne_zero_of_odd hodd
  have hAO : A ≤ TauCeti.QuadraticMap.orthogonalGroup Q := Subgroup.zpowers_le.mpr haO
  have hfreeA : ∀ w : W, (∀ g ∈ A, g w = w) → w = 0 :=
    fun w hw => hfree w (hw a (Subgroup.mem_zpowers a))
  set b := Module.finBasis K W with hb
  set M := LinearMap.BilinForm.toMatrix b (polarBilin Q) with hM
  have hMt : Mᵀ = M := by
    ext i j
    rw [Matrix.transpose_apply, hM, LinearMap.BilinForm.toMatrix_apply,
      LinearMap.BilinForm.toMatrix_apply, polarBilin_apply_apply, polarBilin_apply_apply,
      polar_comm]
  have hd : ∀ i, M i i = 0 := fun i => by
    rw [hM, LinearMap.BilinForm.toMatrix_apply, polarBilin_apply_apply, polar_self, two_nsmul,
      CharTwo.add_self_eq_zero]
  have hMd : IsUnit M.det :=
    isUnit_iff_ne_zero.mpr ((LinearMap.BilinForm.nondegenerate_iff_det_ne_zero b).mp hQ)
  have hadj := isInvol_gramAdj hMd hMt
  have hU := mem_unitaryOf_gramAdj_iff b hM hMd hMt
  set A₀ := matEquiv b a with hA₀
  have hA₀U : A₀ ∈ unitaryOf hadj := (hU a).mpr (polar_map_of_mem haO)
  have hA₀p : A₀ ^ p = 1 := by rw [hA₀, ← map_pow, hap, map_one]
  have hA' : A.map (matEquiv b).toMonoidHom = Subgroup.zpowers A₀ := by
    rw [hAdef, MonoidHom.map_zpowers]
    rfl
  obtain ⟨Y₀, hY₀⟩ := exists_add_gramAdj_eq_one hMd hMt hd
  obtain ⟨Y, hYc, hY⟩ := exists_avg_add_eq_one hadj (gramAdj_smul M)
    (A := Subgroup.zpowers A₀) (Subgroup.zpowers_le.mpr hA₀U)
    (ClNonsplit.natCast_card_zpowers_ne_zero hp hp2 hA₀p) hY₀
  have hunit : IsUnit ((A₀ : Matrix (Fin (Module.finrank K W)) (Fin (Module.finrank K W)) K) -
      1) := by
    rw [← Matrix.mulVec_injective_iff_isUnit]
    intro v v' hvv'
    have h0 : ((A₀ : Matrix (Fin (Module.finrank K W)) (Fin (Module.finrank K W)) K) - 1) *ᵥ
        (v - v') = 0 := by
      rw [Matrix.mulVec_sub, hvv', sub_self]
    set w := b.equivFun.symm (v - v') with hw
    have hrep : b.equivFun w = v - v' := by rw [hw, LinearEquiv.apply_symm_apply]
    have h5 : (A₀ : Matrix (Fin (Module.finrank K W)) (Fin (Module.finrank K W)) K) *ᵥ
        b.equivFun w = b.equivFun w := by
      rw [hrep]
      rw [Matrix.sub_mulVec, Matrix.one_mulVec, sub_eq_zero] at h0
      exact h0
    have h2 : b.equivFun (a w) = b.equivFun w := by
      rw [← h5, hA₀, coe_matEquiv, Module.Basis.equivFun_apply, Module.Basis.equivFun_apply,
        LinearMap.toMatrix_mulVec_repr]
      rfl
    have h3 : a w = w := b.equivFun.injective h2
    have h4 : w = 0 := hfree w h3
    rw [← sub_eq_zero, ← hrep, h4, map_zero]
  obtain ⟨β, S, hS, hSp⟩ := exists_coreFamily_adjCent_dvd hadj hA₀U hp hp2 hA₀p hunit
    ⟨Y, hYc A₀ (Subgroup.mem_zpowers A₀), hY⟩
  have hsurj : ∀ T : Subgroup (GL (Fin (Module.finrank K W)) K),
      T ≤ ((matEquiv b).toMonoidHom).range := fun _ g _ =>
    ⟨(matEquiv b).symm g, (matEquiv b).apply_symm_apply g⟩
  have h := hS.comap (matEquiv b).toMonoidHom (matEquiv b).injective (hsurj _)
  have hC : (adjCent (Subgroup.zpowers A₀) hadj).comap (matEquiv b).toMonoidHom =
      Subgroup.centralizer (A : Set (W ≃ₗ[K] W)) ⊓ TauCeti.QuadraticMap.orthogonalGroup Q := by
    rw [← hA']
    ext g
    rw [Subgroup.mem_comap, adjCent, Subgroup.mem_inf, Subgroup.mem_inf]
    have hcent : (matEquiv b).toMonoidHom g ∈
        Subgroup.centralizer ((A.map (matEquiv b).toMonoidHom : Subgroup _) :
          Set (GL (Fin _) K)) ↔ g ∈ Subgroup.centralizer (A : Set (W ≃ₗ[K] W)) := by
      rw [Subgroup.mem_centralizer_iff, Subgroup.mem_centralizer_iff]
      constructor
      · intro h a ha
        exact (matEquiv b).injective (by
          rw [map_mul, map_mul]
          exact h _ ⟨a, ha, rfl⟩)
      · rintro h _ ⟨a, ha, rfl⟩
        show (matEquiv b) a * (matEquiv b) g = (matEquiv b) g * (matEquiv b) a
        rw [← map_mul, ← map_mul, h a ha]
    rw [hcent]
    constructor
    · rintro ⟨hgc, hgu⟩
      exact ⟨hgc, isometry_of_polar hAO hA hfreeA hgc ((hU g).mp hgu)⟩
    · rintro ⟨hgc, hgO⟩
      exact ⟨hgc, (hU g).mpr (polar_map_of_mem hgO)⟩
  rw [hC] at h
  refine ⟨β, _, h, fun c => ?_⟩
  rw [← Subgroup.card_map_of_injective (f := (matEquiv b).toMonoidHom) (matEquiv b).injective,
    Subgroup.map_comap_eq_self (hsurj _)]
  exact hSp c

end Orth

end OmNonsplit

end CFSG.StandardType
