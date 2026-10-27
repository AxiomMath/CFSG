module

public import CFSG.Quasithin.Background.H11Defs
import CFSG.Quasithin.Vol2.Ch9H11Holds
import CFSG.Quasithin.Background.P3OrthoOm4
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Quasithin.Background.A3ComponentsBasic
public import CFSG.Quasithin.Background.D2Params
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalGroup.Basic

public section

namespace CFSG.Quasithin.H11Proof

open CFSG.Quasithin

section PlusBridge

open scoped Matrix

open CFSG.ComponentClassification.CatalogueBOrthogonalFourSplit
  (DeterminantIsometries determinantForm determinantForm_apply specialRho specialRho_apply)
open CFSG.Quasithin.G11.P3Ortho.Om4 (rho' commutator_eq_range)
open CFSG.Quasithin.H13.H11P (Lm VM rho)
open CFSG.Quasithin.H13
open CFSG.RankThree.PartOne.KCRootAxis (SL₂)

variable {F : Type} [Field F]

private def thetaPlus (F : Type) [Field F] : (Fin 4 → F) ≃ₗ[F] Matrix (Fin 2) (Fin 2) F where
  toFun x := !![x 0, x 2; x 3, x 1]
  invFun X := ![X 0 0, X 1 1, X 0 1, X 1 0]
  map_add' x y := by
    ext i j; fin_cases i <;> fin_cases j <;> rfl
  map_smul' c x := by
    ext i j; fin_cases i <;> fin_cases j <;> rfl
  left_inv x := by
    funext i; fin_cases i <;> rfl
  right_inv X := by
    ext i j; fin_cases i <;> fin_cases j <;> rfl

private theorem det_thetaPlus [CharP F 2] (x : Fin 4 → F) :
    (thetaPlus F x).det = H11Proof.orthPlus F x := by
  simp [thetaPlus, H11Proof.orthPlus, Matrix.det_fin_two, sub_eq_add_neg, CharTwo.neg_eq]

private def cjL {V W : Type} [AddCommGroup V] [Module F V] [AddCommGroup W] [Module F W]
    (Θ : V ≃ₗ[F] W) (g : V ≃ₗ[F] V) : W ≃ₗ[F] W :=
  Θ.symm.trans (g.trans Θ)

private theorem cjL_apply {V W : Type} [AddCommGroup V] [Module F V] [AddCommGroup W]
    [Module F W] (Θ : V ≃ₗ[F] W) (g : V ≃ₗ[F] V) (X : W) :
    cjL Θ g X = Θ (g (Θ.symm X)) := rfl

private def cjHom {V W : Type} [AddCommGroup V] [Module F V] [AddCommGroup W] [Module F W]
    (Θ : V ≃ₗ[F] W) : (V ≃ₗ[F] V) →* (W ≃ₗ[F] W) where
  toFun := cjL Θ
  map_one' := LinearEquiv.ext fun X => by simp [cjL_apply]
  map_mul' g h := LinearEquiv.ext fun X => by simp [cjL_apply]

private theorem congr_linToMulAut (Θ : (Fin 4 → F) ≃ₗ[F] Matrix (Fin 2) (Fin 2) F)
    (g : (Fin 4 → F) ≃ₗ[F] (Fin 4 → F)) :
    MulAut.congr (AddEquiv.toMultiplicative Θ.toAddEquiv) (H11Proof.linToMulAut F (Fin 4 → F) g) =
      H11Proof.linToMulAut F (Matrix (Fin 2) (Fin 2) F) (cjL Θ g) := by
  refine MulEquiv.ext fun X => ?_
  rfl

private theorem map_isometry_plus [CharP F 2] :
    Subgroup.map (cjHom (thetaPlus F))
      (H11Proof.isometryGroup F (H11Proof.orthPlus F)) =
      TauCeti.QuadraticMap.orthogonalGroup (determinantForm F) := by
  ext y
  constructor
  · rintro ⟨g, hg, rfl⟩
    rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff]
    intro X
    rw [determinantForm_apply, determinantForm_apply]
    change (cjL (thetaPlus F) g X).det = X.det
    rw [cjL_apply, det_thetaPlus, hg ((thetaPlus F).symm X), ← det_thetaPlus,
      LinearEquiv.apply_symm_apply]
  · intro hy
    refine ⟨(thetaPlus F).trans (y.trans (thetaPlus F).symm), ?_, ?_⟩
    · intro x
      have h := (TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp hy) (thetaPlus F x)
      rw [determinantForm_apply, determinantForm_apply] at h
      show H11Proof.orthPlus F ((thetaPlus F).trans (y.trans (thetaPlus F).symm) x) =
        H11Proof.orthPlus F x
      rw [← det_thetaPlus, ← det_thetaPlus]
      simp only [LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply]
      exact h
    · refine LinearEquiv.ext fun X => ?_
      change cjL (thetaPlus F) ((thetaPlus F).trans (y.trans (thetaPlus F).symm)) X = y X
      rw [cjL_apply]
      simp

private def transSL (g : Matrix.SpecialLinearGroup (Fin 2) F) :
    Matrix.SpecialLinearGroup (Fin 2) F :=
  ⟨(g : Matrix (Fin 2) (Fin 2) F)ᵀ, by simp [Matrix.det_transpose]⟩

private theorem transSL_transSL (g : Matrix.SpecialLinearGroup (Fin 2) F) :
    transSL (transSL g) = g :=
  Subtype.ext (by simp [transSL])

private theorem coe_transSL (g : Matrix.SpecialLinearGroup (Fin 2) F) :
    ((transSL g : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
      (g : Matrix (Fin 2) (Fin 2) F)ᵀ := rfl

private theorem linToMulAut_rho' (z : Matrix.SpecialLinearGroup (Fin 2) F ×
    Matrix.SpecialLinearGroup (Fin 2) F) :
    H11Proof.linToMulAut F (Matrix (Fin 2) (Fin 2) F) (rho' F z) =
      rho (K := F) (z.1, transSL (z.2⁻¹)) := by
  refine MulEquiv.ext fun X => ?_
  change Multiplicative.ofAdd ((rho' F z) (Multiplicative.toAdd X)) = _
  change Multiplicative.ofAdd (((specialRho z).val : _ → _) (Multiplicative.toAdd X)) = _
  rw [specialRho_apply]
  change Multiplicative.ofAdd ((z.1 : Matrix (Fin 2) (Fin 2) F) * Multiplicative.toAdd X *
      (((z.2⁻¹ : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F))) =
    Multiplicative.ofAdd ((z.1 : Matrix (Fin 2) (Fin 2) F) * Multiplicative.toAdd X *
      ((transSL (z.2⁻¹) : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)ᵀ)
  rw [coe_transSL, Matrix.transpose_transpose]

private theorem map_rho'_range_eq_Lm :
    ((rho' F).range).map (H11Proof.linToMulAut F (Matrix (Fin 2) (Fin 2) F)) = Lm F := by
  ext x
  constructor
  · rintro ⟨_, ⟨z, rfl⟩, rfl⟩
    exact ⟨(z.1, transSL (z.2⁻¹)), (linToMulAut_rho' z).symm⟩
  · rintro ⟨p, rfl⟩
    refine ⟨rho' F (p.1, (transSL p.2)⁻¹), ⟨_, rfl⟩, ?_⟩
    rw [linToMulAut_rho']
    congr 2
    simp [transSL_transSL]

private theorem omega_plus_map [Finite F] [CharP F 2] (h4 : 4 ≤ Nat.card F) :
    (H11Proof.omegaFour F (H11Proof.orthPlus F)).map
      (MulAut.congr (AddEquiv.toMultiplicative (thetaPlus F).toAddEquiv)).toMonoidHom = Lm F := by
  unfold H11Proof.omegaFour
  rw [Subgroup.map_map]
  have hcomp : (MulAut.congr (AddEquiv.toMultiplicative (thetaPlus F).toAddEquiv)).toMonoidHom.comp
      (H11Proof.linToMulAut F (Fin 4 → F)) =
      (H11Proof.linToMulAut F (Matrix (Fin 2) (Fin 2) F)).comp (cjHom (thetaPlus F)) :=
    MonoidHom.ext fun g => congr_linToMulAut (thetaPlus F) g
  rw [hcomp, ← Subgroup.map_map, Subgroup.map_commutator, map_isometry_plus,
    commutator_eq_range h4, map_rho'_range_eq_Lm]

private theorem realizesMod_plus {V : Type} [CommGroup V] {L : Subgroup (MulAut V)}
    (e : V ≃* Multiplicative (Matrix (Fin 2) (Fin 2) F))
    (h : L.map (MulAut.congr e).toMonoidHom = Lm F) :
    FFModel.RealizesMod (V := V) (CFSG.Quasithin.H13.tensorPairModel
      (CFSG.Assembly.LowTwoRank.StatedSL 2 F) (CFSG.Assembly.LowTwoRank.StatedSL 2 F)) L := by
  classical
  have hmem : ∀ p : SL₂ F × SL₂ F, (MulAut.congr e).symm (H11P.rho p) ∈ L := by
    intro p
    have hp : H11P.rho p ∈ L.map (MulAut.congr e).toMonoidHom := by
      rw [h]; exact ⟨p, rfl⟩
    obtain ⟨x, hx, hxp⟩ := hp
    have hxe : x = (MulAut.congr e).symm (H11P.rho p) := by
      rw [MulEquiv.eq_symm_apply]; exact hxp
    rw [← hxe]; exact hx
  let π₀ : (CFSG.Assembly.LowTwoRank.StatedSL 2 F × CFSG.Assembly.LowTwoRank.StatedSL 2 F) →*
      MulAut V :=
    (MulAut.congr e).symm.toMonoidHom.comp
      ((H11P.rho (K := F)).comp ((H11P.slE F).toMonoidHom.prodMap (H11P.slE F).toMonoidHom))
  have hπ₀ : ∀ γ, π₀ γ ∈ L := fun γ => hmem _
  let π : (CFSG.Assembly.LowTwoRank.StatedSL 2 F × CFSG.Assembly.LowTwoRank.StatedSL 2 F) →*
      ↥L := π₀.codRestrict L hπ₀
  have hπγ : ∀ γ, ((π γ : ↥L) : MulAut V) = (MulAut.congr e).symm
      (H11P.rho (H11P.slE F γ.1, H11P.slE F γ.2)) := fun γ => rfl
  have key : ∀ (γ : CFSG.Assembly.LowTwoRank.StatedSL 2 F × CFSG.Assembly.LowTwoRank.StatedSL 2 F)
      (u : V), e (((π γ : ↥L) : MulAut V) u) =
        H11P.rho (H11P.slE F γ.1, H11P.slE F γ.2) (e u) := by
    intro γ u
    rw [hπγ]
    have hf : MulAut.congr e ((MulAut.congr e).symm
        (H11P.rho (H11P.slE F γ.1, H11P.slE F γ.2))) =
        H11P.rho (H11P.slE F γ.1, H11P.slE F γ.2) :=
      MulEquiv.apply_symm_apply _ _
    have h2 := congrArg (fun g : MulAut (Multiplicative (Matrix (Fin 2) (Fin 2) F)) => g (e u)) hf
    simp only [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply] at h2
    exact h2
  let φ : (⊤ : Subgroup V) →* (⊤ : Subgroup (Multiplicative (Matrix (Fin 2) (Fin 2) F))) :=
    { toFun := fun u => ⟨e u, Subgroup.mem_top _⟩
      map_one' := Subtype.ext (map_one e)
      map_mul' := fun u v => Subtype.ext (map_mul e _ _) }
  let β := (QuotientGroup.mk' ((⊥ : Subgroup (Multiplicative (Matrix (Fin 2) (Fin 2) F))).subgroupOf
    (⊤ : Subgroup (Multiplicative (Matrix (Fin 2) (Fin 2) F))))).comp φ
  refine ⟨π, ?_, bot_le, bot_le, fun _ _ _ => Subgroup.mem_top _, ?_,
    fun _ _ _ => Subgroup.mem_top _, ?_, β, ?_, ?_, ?_⟩
  ·
    intro x
    have hx : (MulAut.congr e).toMonoidHom (x : MulAut V) ∈
        L.map (MulAut.congr e).toMonoidHom := Subgroup.mem_map_of_mem _ x.2
    rw [h] at hx
    obtain ⟨⟨y1, y2⟩, hy⟩ := hx
    refine ⟨((H11P.slE F).symm y1, (H11P.slE F).symm y2), Subtype.ext ?_⟩
    refine (hπγ _).trans ?_
    simp only [MulEquiv.apply_symm_apply]
    rw [hy]
    exact MulEquiv.symm_apply_apply _ _
  · intro h' z hz
    have hz1 : z = 1 := (Subgroup.mem_bot (G := V)).mp hz
    subst hz1
    rw [map_one]
    exact Subgroup.one_mem _
  · intro γ m hm
    have hm1 : m = 1 := (Subgroup.mem_bot (G := Multiplicative (Matrix (Fin 2) (Fin 2) F))).mp hm
    subst hm1
    have h1 : (CFSG.Quasithin.H13.tensorPairModel (CFSG.Assembly.LowTwoRank.StatedSL 2 F)
        (CFSG.Assembly.LowTwoRank.StatedSL 2 F)).act γ 1 = 1 := by
      show Multiplicative.ofAdd (_ * (0 : Matrix (Fin 2) (Fin 2) F) * _) =
        (1 : Multiplicative (Matrix (Fin 2) (Fin 2) F))
      rw [mul_zero, zero_mul]
      rfl
    rw [h1]
    exact Subgroup.one_mem _
  · intro q
    obtain ⟨m, rfl⟩ := QuotientGroup.mk_surjective q
    refine ⟨⟨e.symm m.1, Subgroup.mem_top _⟩, ?_⟩
    change (QuotientGroup.mk (⟨e (e.symm m.1), Subgroup.mem_top _⟩ :
      ↥(⊤ : Subgroup (Multiplicative (Matrix (Fin 2) (Fin 2) F)))) :
      _ ⧸ _) = QuotientGroup.mk m
    congr 1
    exact Subtype.ext (MulEquiv.apply_symm_apply e m.1)
  · intro u
    change (QuotientGroup.mk (⟨e u, Subgroup.mem_top _⟩ :
      ↥(⊤ : Subgroup (Multiplicative (Matrix (Fin 2) (Fin 2) F)))) : _ ⧸ _) = 1 ↔
      (u : V) ∈ (⊥ : Subgroup V)
    refine (QuotientGroup.eq_one_iff _).trans ?_
    rw [Subgroup.mem_subgroupOf]
    simp only [Subgroup.mem_bot]
    exact e.map_eq_one_iff
  · intro γ u m hu hm hβu
    let mv : Multiplicative (Matrix (Fin 2) (Fin 2) F) := m.1
    have h0 : (QuotientGroup.mk (φ u) : _ ⧸ _) = QuotientGroup.mk
        (⟨mv, Subgroup.mem_top _⟩ : ↥(⊤ : Subgroup (Multiplicative (Matrix (Fin 2) (Fin 2) F)))) :=
      hβu
    have h1 := Subgroup.mem_subgroupOf.mp (QuotientGroup.eq.mp h0)
    have h2 : ((φ u : ↥(⊤ : Subgroup (Multiplicative (Matrix (Fin 2) (Fin 2) F)))) :
        Multiplicative (Matrix (Fin 2) (Fin 2) F))⁻¹ * mv = 1 := by
      have h3 := Subgroup.mem_bot.mp h1
      simpa using h3
    have h3 : mv = e u := (inv_mul_eq_one.mp h2).symm
    show (QuotientGroup.mk (φ ⟨((π γ : ↥L) : MulAut V) u, hu⟩) :
      _ ⧸ _) = QuotientGroup.mk ⟨_, hm⟩
    refine congrArg QuotientGroup.mk (Subtype.ext ?_)
    show e (((π γ : ↥L) : MulAut V) u) = (CFSG.Quasithin.H13.tensorPairModel
      (CFSG.Assembly.LowTwoRank.StatedSL 2 F) (CFSG.Assembly.LowTwoRank.StatedSL 2 F)).act γ mv
    rw [congrArg (fun x : Multiplicative (Matrix (Fin 2) (Fin 2) F) =>
      (CFSG.Quasithin.H13.tensorPairModel (CFSG.Assembly.LowTwoRank.StatedSL 2 F)
        (CFSG.Assembly.LowTwoRank.StatedSL 2 F)).act γ x) h3]
    exact (key γ u).trans (H11P.act_eq_rho γ (e u)).symm


private theorem natCard_mat_two [Finite F] (hF : Nat.card F = 4) :
    Nat.card (Matrix (Fin 2) (Fin 2) F) = 2 ^ 8 := by
  rw [Module.natCard_eq_pow_finrank (K := F), hF, Module.finrank_matrix, Fintype.card_fin]
  norm_num

theorem card_mul_pow_of_rkIdx {G : Type} [Group G] [Finite G] (H : Subgroup G)
    (hG : Nat.card G = 2 ^ 8) : Nat.card H * 2 ^ rkIdx H = 2 ^ 8 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hdvd : H.index ∣ 2 ^ 8 := hG ▸ H.index_dvd_card
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
  have hk : rkIdx H = j := by rw [rkIdx, hj, padicValNat.prime_pow]
  rw [hk, ← hG, ← H.index_mul_card, hj, mul_comm]

private def linEquivOne {t : MulAut (Multiplicative (Matrix (Fin 2) (Fin 2) F))}
    (ht : CFSG.Quasithin.H13.H11P.IsSemi t 1) :
    Matrix (Fin 2) (Fin 2) F ≃ₗ[F] Matrix (Fin 2) (Fin 2) F where
  toFun X := CFSG.Quasithin.H13.H11P.addMap t X
  invFun X := CFSG.Quasithin.H13.H11P.addMap t⁻¹ X
  map_add' X Y := map_add (CFSG.Quasithin.H13.H11P.addMap t) X Y
  map_smul' c X := by
    simpa using ht c X
  left_inv X := by
    show CFSG.Quasithin.H13.H11P.addMap t⁻¹ (CFSG.Quasithin.H13.H11P.addMap t X) = X
    rw [← CFSG.Quasithin.H13.H11P.addMap_mul, inv_mul_cancel, CFSG.Quasithin.H13.H11P.addMap_one]
  right_inv X := by
    show CFSG.Quasithin.H13.H11P.addMap t (CFSG.Quasithin.H13.H11P.addMap t⁻¹ X) = X
    rw [← CFSG.Quasithin.H13.H11P.addMap_mul, mul_inv_cancel, CFSG.Quasithin.H13.H11P.addMap_one]


private theorem mat_transvection [CharP F 2] [Finite F] (hF : Nat.card F = 4)
    {V : Type} [CommGroup V] [Finite V] {L M : Subgroup (MulAut V)}
    (e' : V ≃* Multiplicative (Matrix (Fin 2) (Fin 2) F))
    (hL : L.map (MulAut.congr e').toMonoidHom = Lm F)
    (hMN : M ≤ Subgroup.normalizer (L : Set (MulAut V)))
    {t : MulAut V} (htM : t ∈ M) (ht2 : t * t = 1)
    (hV : Nat.card V = 2 ^ 8) (hrk : rkIdx (fixV (Subgroup.zpowers t)) = 2) :
    ∃ g : Matrix (Fin 2) (Fin 2) F ≃ₗ[F] Matrix (Fin 2) (Fin 2) F,
      H11Proof.linToMulAut F (Matrix (Fin 2) (Fin 2) F) g = MulAut.congr e' t ∧
      Module.finrank F (LinearMap.range (g.toLinearMap - LinearMap.id)) = 1 ∧
      (g.toLinearMap - LinearMap.id) ∘ₗ (g.toLinearMap - LinearMap.id) = 0 := by
  classical
  have h4 : 4 ≤ Nat.card F := by rw [hF]
  have hH := card_mul_pow_of_rkIdx (fixV (Subgroup.zpowers t)) hV
  rw [hrk] at hH
  have hHcard : Nat.card (fixV (Subgroup.zpowers t)) = 64 := by omega
  have hfix' : fixV (Subgroup.zpowers (MulAut.congr e' t)) =
      (fixV (Subgroup.zpowers t)).map e'.toMonoidHom := by
    have := CFSG.Quasithin.fixV_map_congr_equiv e' (Subgroup.zpowers t)
    rw [MonoidHom.map_zpowers] at this
    exact this
  have hcard' : Nat.card (fixV (Subgroup.zpowers (MulAut.congr e' t))) = 64 := by
    rw [hfix', Subgroup.card_map_of_injective e'.injective, hHcard]
  have ht'2 : MulAut.congr e' t * MulAut.congr e' t = 1 := by
    rw [← map_mul, ht2, map_one]
  have hnorm : MulAut.congr e' t ∈
      Subgroup.normalizer (Lm F : Set (MulAut (Multiplicative (Matrix (Fin 2) (Fin 2) F)))) := by
    have h1 : MulAut.congr e' t ∈
        (Subgroup.normalizer (L : Set (MulAut V))).map (MulAut.congr e').toMonoidHom :=
      Subgroup.mem_map_of_mem _ (hMN htM)
    rw [Subgroup.map_equiv_normalizer_eq, hL] at h1
    exact h1
  obtain ⟨c, -, P, Q, σ, hform⟩ := CFSG.Quasithin.H13.H11P.normal_form h4 hnorm
  have hsemi := CFSG.Quasithin.H13.H11P.isSemi_of_form hform
  by_cases hσ1 : σ = 1
  swap
  ·
    exfalso
    have hcf := CFSG.Quasithin.H13.H11P.card_fix_sq
      (Y := (⊤ : Subgroup (Multiplicative (Matrix (Fin 2) (Fin 2) F))))
      (fun _ _ _ => Subgroup.mem_top _) hsemi hσ1 ht'2 (fun X _ => Subgroup.mem_top _)
    have hTop : Nat.card {X : Matrix (Fin 2) (Fin 2) F //
        CFSG.Quasithin.H13.H11P.MemM (⊤ : Subgroup (Multiplicative (Matrix (Fin 2) (Fin 2) F)))
          X} = 2 ^ 8 := by
      rw [← natCard_mat_two hF]
      exact Nat.card_congr (Equiv.subtypeUnivEquiv fun X => Subgroup.mem_top _)
    have hsub : Nat.card {X : Matrix (Fin 2) (Fin 2) F //
        CFSG.Quasithin.H13.H11P.MemM (⊤ : Subgroup (Multiplicative (Matrix (Fin 2) (Fin 2) F)))
          X ∧ CFSG.Quasithin.H13.H11P.addMap (MulAut.congr e' t) X = X} =
        Nat.card (fixV (Subgroup.zpowers (MulAut.congr e' t))) := by
      refine Nat.card_congr
        { toFun := fun X => ⟨Multiplicative.ofAdd X.1,
            CFSG.Quasithin.H13.H11P.memM_fixV_zpowers.mpr X.2.2⟩
          invFun := fun Y => ⟨Multiplicative.toAdd Y.1,
            ⟨Subgroup.mem_top _, CFSG.Quasithin.H13.H11P.memM_fixV_zpowers.mp Y.2⟩⟩
          left_inv := fun X => rfl
          right_inv := fun Y => rfl }
    rw [hsub, hTop, hcard'] at hcf
    norm_num at hcf
  subst hσ1
  set t' := MulAut.congr e' t with ht'def
  set g := linEquivOne hsemi with hgdef
  have hgX : ∀ X, g X = CFSG.Quasithin.H13.H11P.addMap t' X := fun X => rfl
  have hgg : ∀ X, g (g X) = X := by
    intro X
    rw [hgX, hgX, ← CFSG.Quasithin.H13.H11P.addMap_mul, ht'2,
      CFSG.Quasithin.H13.H11P.addMap_one]
  set N := g.toLinearMap - LinearMap.id with hN
  have hNX : ∀ Z, N Z = g Z - Z := fun Z => rfl
  refine ⟨g, rfl, ?_, ?_⟩
  · show Module.finrank F (LinearMap.range N) = 1
    have hrn := LinearMap.finrank_range_add_finrank_ker N
    have hmat : Module.finrank F (Matrix (Fin 2) (Fin 2) F) = 4 := by
      rw [Module.finrank_matrix, Fintype.card_fin, Module.finrank_self]
    have hker_iff : ∀ X : Matrix (Fin 2) (Fin 2) F,
        X ∈ LinearMap.ker N ↔ CFSG.Quasithin.H13.H11P.addMap t' X = X := by
      intro X
      rw [LinearMap.mem_ker, hN, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero]
      rfl
    have hkerNat : Nat.card (LinearMap.ker N) = 64 := by
      rw [← hcard']
      refine Nat.card_congr
        { toFun := fun X => ⟨Multiplicative.ofAdd (X : Matrix (Fin 2) (Fin 2) F),
            CFSG.Quasithin.H13.H11P.memM_fixV_zpowers.mpr ((hker_iff _).mp X.2)⟩
          invFun := fun Y => ⟨Multiplicative.toAdd (Y : Multiplicative (Matrix (Fin 2) (Fin 2) F)),
            (hker_iff _).mpr (CFSG.Quasithin.H13.H11P.memM_fixV_zpowers.mp Y.2)⟩
          left_inv := fun X => rfl
          right_inv := fun Y => rfl }
    have hkerf : Module.finrank F (LinearMap.ker N) = 3 := by
      have h := Module.natCard_eq_pow_finrank (K := F) (V := LinearMap.ker N)
      rw [hkerNat, hF] at h
      have h' : (4 : ℕ) ^ Module.finrank F (LinearMap.ker N) = 4 ^ 3 := by
        rw [← h]
        norm_num
      exact Nat.pow_right_injective (by norm_num) h'
    rw [hmat, hkerf] at hrn
    omega
  · show N ∘ₗ N = 0
    apply LinearMap.ext
    intro X
    have h2 : ∀ Y : Matrix (Fin 2) (Fin 2) F, Y + Y = 0 := fun Y => CharTwo.add_self_eq_zero Y
    rw [LinearMap.comp_apply, LinearMap.zero_apply, hNX (N X), hNX X, map_sub, hgg]
    have h3 : X - g X - (g X - X) = (X + X) - (g X + g X) := by abel
    rw [h3, h2 X, h2 (g X), sub_self]


private theorem isFTransvection_of_mat (g : Matrix (Fin 2) (Fin 2) F ≃ₗ[F] Matrix (Fin 2) (Fin 2) F)
    (T : MulAut (Multiplicative (Fin 4 → F)))
    (hT : H11Proof.linToMulAut F (Matrix (Fin 2) (Fin 2) F) g =
      MulAut.congr (AddEquiv.toMultiplicative (thetaPlus F).toAddEquiv) T)
    (hr : Module.finrank F (LinearMap.range (g.toLinearMap - LinearMap.id)) = 1)
    (hn : (g.toLinearMap - LinearMap.id) ∘ₗ (g.toLinearMap - LinearMap.id) = 0) :
    H11Proof.IsFTransvection F (Fin 4) T := by
  classical
  unfold H11Proof.IsFTransvection
  set Θ := thetaPlus F with hΘ
  set h : (Fin 4 → F) ≃ₗ[F] (Fin 4 → F) := Θ.trans (g.trans Θ.symm) with hh
  have hcj : cjL Θ h = g := LinearEquiv.ext fun X => by
    rw [cjL_apply, hh]
    simp
  have hEx : ∀ x : Fin 4 → F,
      (h.toLinearMap - LinearMap.id : (Fin 4 → F) →ₗ[F] (Fin 4 → F)) x =
        Θ.symm ((g.toLinearMap - LinearMap.id : Matrix (Fin 2) (Fin 2) F →ₗ[F]
          Matrix (Fin 2) (Fin 2) F) (Θ x)) := by
    intro x
    simp [hh, map_sub]
  refine ⟨h, ?_, ?_, ?_⟩
  · apply MulEquiv.injective (MulAut.congr (AddEquiv.toMultiplicative Θ.toAddEquiv))
    rw [congr_linToMulAut Θ h, hcj, hT]
  · have hrange : LinearMap.range (h.toLinearMap - LinearMap.id) =
        (LinearMap.range (g.toLinearMap - LinearMap.id)).map
          (Θ.symm : Matrix (Fin 2) (Fin 2) F →ₗ[F] (Fin 4 → F)) := by
      ext y
      constructor
      · rintro ⟨x, rfl⟩
        exact ⟨(g.toLinearMap - LinearMap.id : Matrix (Fin 2) (Fin 2) F →ₗ[F]
          Matrix (Fin 2) (Fin 2) F) (Θ x), LinearMap.mem_range_self _ _, (hEx x).symm⟩
      · rintro ⟨z, ⟨w, rfl⟩, rfl⟩
        exact ⟨Θ.symm w, by rw [hEx, LinearEquiv.apply_symm_apply]; rfl⟩
    rw [hrange, LinearEquiv.finrank_map_eq]
    exact hr
  · apply LinearMap.ext
    intro x
    have hnn : (g.toLinearMap - LinearMap.id : Matrix (Fin 2) (Fin 2) F →ₗ[F]
        Matrix (Fin 2) (Fin 2) F) ((g.toLinearMap - LinearMap.id : Matrix (Fin 2) (Fin 2) F →ₗ[F]
        Matrix (Fin 2) (Fin 2) F) (Θ x)) = 0 := by
      have := LinearMap.congr_fun hn (Θ x)
      simpa using this
    rw [LinearMap.comp_apply, LinearMap.zero_apply, hEx, hEx, LinearEquiv.apply_symm_apply, hnn,
      map_zero]

theorem natCard_fin4_fun [Finite F] (hF : Nat.card F = 4) :
    Nat.card (Fin 4 → F) = 2 ^ 8 := by
  rw [Nat.card_fun, Nat.card_fin, hF]
  norm_num

theorem h11_plus {V : Type} [CommGroup V] [Finite V] (hV2 : ∀ v : V, v ^ 2 = 1)
    [Finite F] [CharP F 2] {n : ℕ} (hn : 2 ≤ n) (hF : Nat.card F = 2 ^ n)
    (M : Subgroup (MulAut V)) (e : V ≃* Multiplicative (Fin 4 → F))
    (hO : (perfectCore M).map (MulAut.congr e).toMonoidHom =
      H11Proof.omegaFour F (H11Proof.orthPlus F))
    (A : Subgroup (MulAut V)) (hA : IsA2 M A) :
    rk ↥A + n ≤ rkIdx (fixV A) + 1 ∧
      (rk ↥A + 2 ≤ rkIdx (fixV A) ∨
        (n = 2 ∧ ∃ t ∈ A, H11Proof.IsFTransvection F (Fin 4) (MulAut.congr e t))) ∧
      (A ≤ perfectCore M → rk ↥A + n ≤ rkIdx (fixV A)) := by
  classical
  set Θ' : Multiplicative (Fin 4 → F) ≃* Multiplicative (Matrix (Fin 2) (Fin 2) F) :=
    AddEquiv.toMultiplicative (thetaPlus F).toAddEquiv with hΘ'
  set e' : V ≃* Multiplicative (Matrix (Fin 2) (Fin 2) F) := e.trans Θ' with he'
  have h4 : 4 ≤ Nat.card F := by
    rw [hF]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have hcomp : (MulAut.congr e').toMonoidHom =
      (MulAut.congr Θ').toMonoidHom.comp (MulAut.congr e).toMonoidHom :=
    MonoidHom.ext fun x => MulEquiv.ext fun y => by
      simp [he', MulAut.congr_apply, MulEquiv.trans_apply]
  have hcomp' : ∀ x, MulAut.congr e' x = MulAut.congr Θ' (MulAut.congr e x) :=
    fun x => DFunLike.congr_fun hcomp x
  have hL' : (perfectCore M).map (MulAut.congr e').toMonoidHom = Lm F := by
    rw [hcomp, ← Subgroup.map_map, hO]
    exact omega_plus_map h4
  have hreal := realizesMod_plus e' hL'
  have hLM : perfectCore M ≤ M := perfectCore_le M
  have hMN : M ≤ Subgroup.normalizer (perfectCore M : Set (MulAut V)) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (perfectCore_le M)).mp (perfectCore_normal M)
  obtain ⟨c1, c2, c3⟩ := ch9InH11Plus_holds V (perfectCore M) M n hV2 (by omega) hLM hMN
    ⟨F, inferInstance, inferInstance, hF, hreal⟩ A hA.1 hA.2.1 hA.2.2
  refine ⟨c1, ?_, c3⟩
  rcases c2 with c2 | ⟨hn2, t, htA, hrk⟩
  · exact Or.inl c2
  · refine Or.inr ⟨hn2, t, htA, ?_⟩
    have hF4 : Nat.card F = 4 := by rw [hF, hn2]; norm_num
    have htM : t ∈ M := hA.1 htA
    have ht2 : t * t = 1 := by
      rw [← sq]
      exact hA.2.2.2 t htA
    have hV : Nat.card V = 2 ^ 8 := by
      have hm : Nat.card (Multiplicative (Fin 4 → F)) = Nat.card (Fin 4 → F) := rfl
      rw [Nat.card_congr e.toEquiv, hm, natCard_fin4_fun hF4]
    have hrk2 : rkIdx (fixV (Subgroup.zpowers t)) = 2 := by rw [hrk, hn2]
    obtain ⟨g, hg, hr, hn'⟩ := mat_transvection hF4 e' hL' hMN htM ht2 hV hrk2
    refine isFTransvection_of_mat g (MulAut.congr e t) ?_ hr hn'
    rw [hg]
    exact hcomp' t

end PlusBridge

end CFSG.Quasithin.H11Proof
