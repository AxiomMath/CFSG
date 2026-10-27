module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.K328.Rows
import CFSG.Adapters.StatedQuasisimple
import CFSG.Open.StatedCenterThree
import CFSG.Open.StatedZModTwo

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.K328

open CFSG.Open
open scoped commutatorElement

private theorem k328r4p_model (F : Type) [Field F] [Fintype F] [DecidableEq F]
    (hF : Fintype.card F = 2) :
    ∃ (L : Type) (_ : Field L) (ℓ : L →+* Matrix (Fin 2) (Fin 2) F) (ω : L),
      Nat.card L = 4 ∧ ℓ ω = rhoOmega F ∧
      ∀ g : Matrix (Fin 2) (Fin 2) F, rhoOmega F * g = g * rhoOmega F → ∃ a : L, ℓ a = g := by
  have hsq : ∀ r : F, r ^ 2 = r := fun r => by
    have := FiniteField.pow_card r
    rwa [hF] at this
  have : Fact (∀ r : F, r ^ 2 ≠ 1 + 1 * r) := ⟨fun r hr => by
    have h := hsq r
    exact one_ne_zero (by linear_combination h - hr)⟩
  have hM : rhoOmega F * rhoOmega F =
      (1 : F) • (1 : Matrix (Fin 2) (Fin 2) F) + (1 : F) • rhoOmega F := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [rhoOmega, Matrix.mul_apply, Fin.sum_univ_two]
  let ℓ : QuadraticAlgebra F 1 1 →ₐ[F] Matrix (Fin 2) (Fin 2) F :=
    QuadraticAlgebra.lift ⟨rhoOmega F, hM⟩
  refine ⟨QuadraticAlgebra F 1 1, inferInstance, ℓ.toRingHom, QuadraticAlgebra.omega, ?_, ?_, ?_⟩
  · rw [Nat.card_congr (QuadraticAlgebra.equivProd 1 1), Nat.card_prod, Nat.card_eq_fintype_card,
      hF]
  · simp [ℓ]
  · intro g hg
    refine ⟨⟨g 0 0, g 0 1⟩, ?_⟩
    have e00 := congrFun (congrFun hg 0) 0
    have e01 := congrFun (congrFun hg 0) 1
    simp [rhoOmega, Matrix.mul_apply, Fin.sum_univ_two] at e00 e01
    ext i j
    fin_cases i <;> fin_cases j <;> simp [ℓ, rhoOmega, QuadraticAlgebra.lift_apply_apply, e00, e01]

private def k328r4p_Phi (F : Type) [Field F] :
    Matrix (Fin 6) (Fin 6) F ≃+* Matrix (Fin 3) (Fin 3) (Matrix (Fin 2) (Fin 2) F) :=
  (Matrix.reindexRingEquiv F finProdFinEquiv.symm).trans
    (Matrix.compRingEquiv (Fin 3) (Fin 2) F).symm

private theorem k328r4p_Phi_apply {F : Type} [Field F] (g : Matrix (Fin 6) (Fin 6) F)
    (i j : Fin 3) (r s : Fin 2) :
    k328r4p_Phi F g i j r s = g (finProdFinEquiv (i, r)) (finProdFinEquiv (j, s)) := by
  simp [k328r4p_Phi]

private theorem k328r4p_Phi_blockDiag3 {F : Type} [Field F] [Fintype F] [DecidableEq F]
    (A₀ A₁ A₂ : Matrix (Fin 2) (Fin 2) F) :
    k328r4p_Phi F (blockDiag3 F 6 A₀ A₁ A₂) = Matrix.diagonal ![A₀, A₁, A₂] := by
  ext i j r s
  rw [k328r4p_Phi_apply]
  fin_cases i <;> fin_cases j <;> fin_cases r <;> fin_cases s <;>
    simp [blockDiag3, finProdFinEquiv, Matrix.diagonal]

private def k328r4p_rho {F L : Type} [Field F] [Field L] (ℓ : L →+* Matrix (Fin 2) (Fin 2) F) :
    Matrix (Fin 3) (Fin 3) L →+* Matrix (Fin 6) (Fin 6) F :=
  (k328r4p_Phi F).symm.toRingHom.comp ℓ.mapMatrix

private theorem k328r4p_Phi_rho {F L : Type} [Field F] [Field L]
    (ℓ : L →+* Matrix (Fin 2) (Fin 2) F) (A : Matrix (Fin 3) (Fin 3) L) :
    k328r4p_Phi F (k328r4p_rho ℓ A) = ℓ.mapMatrix A := by
  simp [k328r4p_rho]

private theorem k328r4p_rho_injective {F L : Type} [Field F] [Field L]
    (ℓ : L →+* Matrix (Fin 2) (Fin 2) F) : Function.Injective (k328r4p_rho ℓ) := by
  intro A B h
  have h1 := congrArg (k328r4p_Phi F) h
  rw [k328r4p_Phi_rho, k328r4p_Phi_rho] at h1
  exact Matrix.map_injective ℓ.injective h1

private theorem k328r4p_rho_scalar {F L : Type} [Field F] [Fintype F] [DecidableEq F] [Field L]
    (ℓ : L →+* Matrix (Fin 2) (Fin 2) F) (ω : L) (hω : ℓ ω = rhoOmega F) :
    k328r4p_rho ℓ (Matrix.scalar (Fin 3) ω) =
      blockDiag3 F 6 (rhoOmega F) (rhoOmega F) (rhoOmega F) := by
  apply (k328r4p_Phi F).injective
  rw [k328r4p_Phi_rho, k328r4p_Phi_blockDiag3, RingHom.mapMatrix_apply, Matrix.scalar_apply,
    Matrix.diagonal_map (map_zero ℓ), hω]
  congr 1
  funext i
  fin_cases i <;> rfl

private theorem k328r4p_exists_rho {F L : Type} [Field F] [Fintype F] [DecidableEq F] [Field L]
    (ℓ : L →+* Matrix (Fin 2) (Fin 2) F)
    (hsurj : ∀ g : Matrix (Fin 2) (Fin 2) F, rhoOmega F * g = g * rhoOmega F → ∃ a : L, ℓ a = g)
    (g : Matrix (Fin 6) (Fin 6) F)
    (hg : blockDiag3 F 6 (rhoOmega F) (rhoOmega F) (rhoOmega F) * g =
      g * blockDiag3 F 6 (rhoOmega F) (rhoOmega F) (rhoOmega F)) :
    ∃ A : Matrix (Fin 3) (Fin 3) L, k328r4p_rho ℓ A = g := by
  have h1 := congrArg (k328r4p_Phi F) hg
  rw [map_mul, map_mul, k328r4p_Phi_blockDiag3] at h1
  have hb : ∀ i j, rhoOmega F * k328r4p_Phi F g i j = k328r4p_Phi F g i j * rhoOmega F := by
    intro i j
    have := congrFun (congrFun h1 i) j
    rw [Matrix.diagonal_mul, Matrix.mul_diagonal] at this
    fin_cases i <;> fin_cases j <;> simpa using this
  choose a ha using fun i j => hsurj _ (hb i j)
  refine ⟨Matrix.of a, (k328r4p_Phi F).injective ?_⟩
  rw [k328r4p_Phi_rho]
  refine Matrix.ext fun i j => ?_
  exact ha i j

private def k328r4p_rhoG {F L : Type} [Field F] [Field L] (ℓ : L →+* Matrix (Fin 2) (Fin 2) F) :
    GL (Fin 3) L →* GL (Fin 6) F :=
  Units.map (k328r4p_rho ℓ).toMonoidHom

private theorem k328r4p_rhoG_val {F L : Type} [Field F] [Field L]
    (ℓ : L →+* Matrix (Fin 2) (Fin 2) F) (a : GL (Fin 3) L) :
    ((k328r4p_rhoG ℓ a : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F) =
      k328r4p_rho ℓ (a : Matrix (Fin 3) (Fin 3) L) := rfl

private theorem k328r4p_rhoG_injective {F L : Type} [Field F] [Field L]
    (ℓ : L →+* Matrix (Fin 2) (Fin 2) F) : Function.Injective (k328r4p_rhoG ℓ) := by
  intro a b h
  apply Units.ext
  apply k328r4p_rho_injective ℓ
  have := congrArg (fun u : GL (Fin 6) F => (u : Matrix (Fin 6) (Fin 6) F)) h
  simpa [k328r4p_rhoG_val] using this

private theorem k328r4p_exists_rhoG {F L : Type} [Field F] [Fintype F] [DecidableEq F] [Field L]
    (ℓ : L →+* Matrix (Fin 2) (Fin 2) F)
    (hsurj : ∀ g : Matrix (Fin 2) (Fin 2) F, rhoOmega F * g = g * rhoOmega F → ∃ a : L, ℓ a = g)
    (z₀ : GL (Fin 6) F)
    (hz : (z₀ : Matrix (Fin 6) (Fin 6) F) =
      blockDiag3 F 6 (rhoOmega F) (rhoOmega F) (rhoOmega F))
    (g : GL (Fin 6) F) (hg : z₀ * g = g * z₀) : ∃ a : GL (Fin 3) L, k328r4p_rhoG ℓ a = g := by
  have hc : Commute z₀ g := hg
  have hmat : ∀ h : GL (Fin 6) F, Commute z₀ h →
      (z₀ : Matrix (Fin 6) (Fin 6) F) * h = (h : Matrix (Fin 6) (Fin 6) F) * z₀ := by
    intro h hh
    have := congrArg (fun u : GL (Fin 6) F => (u : Matrix (Fin 6) (Fin 6) F)) hh.eq
    simpa using this
  obtain ⟨A, hA⟩ := k328r4p_exists_rho ℓ hsurj (g : Matrix (Fin 6) (Fin 6) F)
    (by rw [← hz]; exact hmat g hc)
  obtain ⟨B, hB⟩ := k328r4p_exists_rho ℓ hsurj ((g⁻¹ : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F)
    (by rw [← hz]; exact hmat g⁻¹ hc.inv_right)
  have hAB : A * B = 1 := by
    apply k328r4p_rho_injective ℓ
    rw [map_mul, hA, hB, map_one]
    exact g.mul_inv
  have hBA : B * A = 1 := by
    apply k328r4p_rho_injective ℓ
    rw [map_mul, hA, hB, map_one]
    exact g.inv_mul
  exact ⟨⟨A, B, hAB, hBA⟩, Units.ext hA⟩

private theorem k328r4p_rhoG_commute {F L : Type} [Field F] [Fintype F] [DecidableEq F] [Field L]
    (ℓ : L →+* Matrix (Fin 2) (Fin 2) F) (ω : L) (hω : ℓ ω = rhoOmega F) (z₀ : GL (Fin 6) F)
    (hz : (z₀ : Matrix (Fin 6) (Fin 6) F) =
      blockDiag3 F 6 (rhoOmega F) (rhoOmega F) (rhoOmega F))
    (a : GL (Fin 3) L) : z₀ * k328r4p_rhoG ℓ a = k328r4p_rhoG ℓ a * z₀ := by
  apply Units.ext
  simp only [Units.val_mul, k328r4p_rhoG_val, hz]
  rw [← k328r4p_rho_scalar ℓ ω hω, ← map_mul, ← map_mul]
  congr 1
  exact (Matrix.scalar_commute ω (fun r => Commute.all _ _) _).eq

private theorem k328r4p_stdComp_eq {F L : Type} [Field F] [Fintype F] [DecidableEq F] [Field L]
    (hF : Fintype.card F = 2) (ℓ : L →+* Matrix (Fin 2) (Fin 2) F) (ω : L)
    (hω : ℓ ω = rhoOmega F)
    (hsurj : ∀ g : Matrix (Fin 2) (Fin 2) F, rhoOmega F * g = g * rhoOmega F → ∃ a : L, ℓ a = g)
    (z₀ : GL (Fin 6) F)
    (hz : (z₀ : Matrix (Fin 6) (Fin 6) F) =
      blockDiag3 F 6 (rhoOmega F) (rhoOmega F) (rhoOmega F)) :
    stdComp (StatedSL 6 F) z₀ = (StatedSL 3 L).map (k328r4p_rhoG ℓ) := by
  have hcard : Nat.card F = 2 := by rw [Nat.card_eq_fintype_card]; exact hF
  have hC : StatedSL 6 F ⊓ Subgroup.centralizer {z₀} = Subgroup.centralizer {z₀} := by
    rw [CFSG.Open.StatedAPI.statedSL_eq_top_of_card_two hcard 6, top_inf_eq]
  have hYC : (StatedSL 3 L).map (k328r4p_rhoG ℓ) ≤ Subgroup.centralizer {z₀} := by
    rintro _ ⟨a, -, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    rw [hh]
    exact k328r4p_rhoG_commute ℓ ω hω z₀ hz a
  apply le_antisymm
  · unfold stdComp
    rw [hC, Subgroup.commutator_le]
    intro g₁ hg₁ g₂ hg₂
    obtain ⟨a, rfl⟩ := k328r4p_exists_rhoG ℓ hsurj z₀ hz g₁
      (Subgroup.mem_centralizer_iff.1 hg₁ z₀ rfl)
    obtain ⟨b, rfl⟩ := k328r4p_exists_rhoG ℓ hsurj z₀ hz g₂
      (Subgroup.mem_centralizer_iff.1 hg₂ z₀ rfl)
    refine ⟨⁅a, b⁆, ?_, map_commutatorElement _ _ _⟩
    show ⁅a, b⁆ ∈ StatedSL 3 L
    rw [CFSG.Open.StatedAPI.statedSL_eq_ker_det, MonoidHom.mem_ker, map_commutatorElement]
    exact commutatorElement_eq_one_iff_mul_comm.2 (mul_comm _ _)
  · have : Group.IsPerfect ↥(StatedSL 3 L) :=
      (CFSG.Open.StatedAPI.isQuasisimple_statedSL_of_two_le (m := 2) le_rfl L).1
    have hperf : ⁅StatedSL 3 L, StatedSL 3 L⁆ = StatedSL 3 L := Subgroup.commutator_eq_self
    have hY : (StatedSL 3 L).map (k328r4p_rhoG ℓ) =
        ⁅(StatedSL 3 L).map (k328r4p_rhoG ℓ), (StatedSL 3 L).map (k328r4p_rhoG ℓ)⁆ := by
      rw [← Subgroup.map_commutator, hperf]
    unfold stdComp
    rw [hC]
    exact hY.le.trans (Subgroup.commutator_mono hYC hYC)

private theorem k328r4p_centralizer_zpowers_eq {G : Type} [Group G] (H : Subgroup G) (z₀ : G)
    (hz₀ : z₀ ∈ H) :
    Subgroup.centralizer ((Subgroup.zpowers (⟨z₀, hz₀⟩ : H) : Subgroup H) : Set H) =
      (H ⊓ Subgroup.centralizer {z₀}).subgroupOf H := by
  ext x
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf, Subgroup.mem_centralizer_iff,
    Subgroup.mem_centralizer_iff]
  constructor
  · intro h
    refine ⟨x.2, fun y hy => ?_⟩
    rw [Set.mem_singleton_iff] at hy
    subst hy
    exact congrArg Subtype.val (h _ (Subgroup.mem_zpowers _))
  · rintro ⟨-, h⟩ y hy
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
    have hc : Commute (⟨z₀, hz₀⟩ : H) x := Subtype.ext (h z₀ rfl)
    exact (hc.zpow_left k).eq

private theorem k328r4p_subgroupOf_commutator_self {A : Type} [Group A] (K : Subgroup A) :
    ⁅K, K⁆.subgroupOf K = commutator K := by
  rw [← Subgroup.map_subtype_commutator K]
  exact Subgroup.comap_map_eq_self_of_injective K.subtype_injective _

private theorem k328r4p_pos_of_equiv {G : Type} [Group G] [Finite G] (H : Subgroup G) (z₀ : G)
    (hz₀ : z₀ ∈ H) (hz : z₀ ∈ stdComp H z₀) (ho : orderOf z₀ = 3) {L : Type} [Field L]
    (hL : Nat.card L = 4) (e : ↥(stdComp H z₀) ≃* ↥(StatedSL 3 L)) :
    Pos ↥H (Subgroup.zpowers (⟨z₀, hz₀⟩ : H)) ((stdComp H z₀).subgroupOf H) := by
  have hfin : Finite L := Nat.finite_of_card_ne_zero (by omega)
  have hSC : stdComp H z₀ ≤ H ⊓ Subgroup.centralizer {z₀} :=
    Subgroup.commutator_le_self (H ⊓ Subgroup.centralizer {z₀})
  let eX : ↥((stdComp H z₀).subgroupOf H) ≃* ↥(StatedSL 3 L) :=
    (Subgroup.subgroupOfEquivOfLe (stdComp_le H z₀)).trans e
  have hcen : Subgroup.center ↥(StatedSL 3 L) =
      (StatedScalars (Fin 3) L).subgroupOf (StatedSL 3 L) := by
    rw [← CFSG.Assembly.LowTwoRank.map_center_eq_statedScalars 3 L,
      Subgroup.map_center_eq (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 3 L)]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Nat.card_zpowers, ← Subgroup.orderOf_coe]
    exact ho
  · rw [Subgroup.zpowers_le]
    exact hz
  · rw [k328r4p_centralizer_zpowers_eq]
    exact fun x hx => Subgroup.mem_subgroupOf.2 (hSC (Subgroup.mem_subgroupOf.1 hx))
  · rw [k328r4p_centralizer_zpowers_eq]
    have h1 : (stdComp H z₀).subgroupOf H =
        ⁅(H ⊓ Subgroup.centralizer {z₀}).subgroupOf H,
          (H ⊓ Subgroup.centralizer {z₀}).subgroupOf H⁆ := by
      apply Subgroup.map_injective H.subtype_injective
      rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le inf_le_left,
        Subgroup.map_subgroupOf_eq_of_le (hSC.trans inf_le_left)]
      rfl
    rw [h1, k328r4p_subgroupOf_commutator_self]
    exact Subgroup.Normal.isSubnormal inferInstance
  · have hq := CFSG.Open.StatedAPI.isQuasisimple_statedSL_of_two_le (m := 2) le_rfl L
    exact isQuasisimple_of_mulEquiv' eX.symm ⟨hq.1.1, hq.2.1⟩
  · have h3 : 3 ∣ Nat.card L - 1 := by rw [hL]
    rw [← CFSG.Open.StatedCenterThree.card_center_statedSL_three h3]
    exact Nat.card_congr (Subgroup.centerCongr eX).toEquiv
  · let f : ↥((stdComp H z₀).subgroupOf H) ⧸ Subgroup.center ↥((stdComp H z₀).subgroupOf H) ≃*
        StatedProj (StatedSL 3 L) :=
      QuotientGroup.congr _ ((StatedScalars (Fin 3) L).subgroupOf (StatedSL 3 L)) eX
        ((Subgroup.map_center_eq eX).trans hcen)
    refine Or.inl (CFSG.Blueprint.LieModel.of_mulEquiv f.symm ?_)
    exact Or.inl ⟨by decide, ⟨Nat.prime_two, by norm_num, by norm_num, by decide, by decide⟩, L,
      inferInstance, inferInstance, by rw [hL]; norm_num, ⟨MulEquiv.refl _⟩⟩

theorem row4_pos (F : Type) [Field F] [Fintype F] [DecidableEq F]
    (hF : Fintype.card F = 2) (z₀ t₀ : GL (Fin 6) F)
    (hz : (z₀ : Matrix (Fin 6) (Fin 6) F) =
      blockDiag3 F 6 (rhoOmega F) (rhoOmega F) (rhoOmega F))
    (ht : (t₀ : Matrix (Fin 6) (Fin 6) F) =
      blockDiag3 F 6 (rhoOmega F) (rhoOmega F ^ 2) 1) :
    PosLeaf (StatedSL 6 F) z₀ := by
  have _ := ht
  intro hz₀
  obtain ⟨L, _, ℓ, ω, hL, hω, hsurj⟩ := k328r4p_model F hF
  have hS := k328r4p_stdComp_eq hF ℓ ω hω hsurj z₀ hz
  have hfin : Finite L := Nat.finite_of_card_ne_zero (by omega)
  have hω0 : ω ≠ 0 := fun h => by
    have h1 := congrFun (congrFun (hω ▸ congrArg ℓ h) 0) 1
    simp [rhoOmega] at h1
  have hu : (Units.mk0 ω hω0) ^ 3 = 1 := by
    have h := pow_card_eq_one' (G := Lˣ) (x := Units.mk0 ω hω0)
    rwa [Nat.card_units, hL] at h
  have hω3 : ω ^ 3 = 1 := by simpa using congrArg Units.val hu
  set a₀ : GL (Fin 3) L := Matrix.GeneralLinearGroup.scalar (Fin 3) (Units.mk0 ω hω0) with ha₀
  have ha₀z : k328r4p_rhoG ℓ a₀ = z₀ :=
    Units.ext (by rw [k328r4p_rhoG_val, ha₀, Matrix.GeneralLinearGroup.coe_scalar, Units.val_mk0,
      k328r4p_rho_scalar ℓ ω hω, hz])
  have ha₀S : a₀ ∈ StatedSL 3 L := by
    rw [CFSG.Open.StatedAPI.mem_statedSL_iff, ha₀, Matrix.GeneralLinearGroup.coe_scalar,
      Units.val_mk0, Matrix.scalar_apply, Matrix.det_diagonal, Finset.prod_const,
      Finset.card_univ, Fintype.card_fin]
    exact hω3
  have hz3 : z₀ ^ 3 = 1 := by
    rw [← ha₀z, ← map_pow, ha₀, ← map_pow, hu, map_one, map_one]
  have hz1 : z₀ ≠ 1 := fun h => by
    have h1 := congrFun (congrFun
      (congrArg (fun u : GL (Fin 6) F => (u : Matrix (Fin 6) (Fin 6) F)) h) 0) 0
    simp [hz, blockDiag3, rhoOmega] at h1
  have ho : orderOf z₀ = 3 := orderOf_eq_prime hz3 hz1
  have hzS : z₀ ∈ stdComp (StatedSL 6 F) z₀ := by
    rw [hS]
    exact ⟨a₀, ha₀S, ha₀z⟩
  let e : ↥(stdComp (StatedSL 6 F) z₀) ≃* ↥(StatedSL 3 L) :=
    (MulEquiv.subgroupCongr hS).trans
      (Subgroup.equivMapOfInjective (StatedSL 3 L) (k328r4p_rhoG ℓ)
        (k328r4p_rhoG_injective ℓ)).symm
  exact k328r4p_pos_of_equiv (StatedSL 6 F) z₀ hz₀ hzS ho hL e

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.K328
