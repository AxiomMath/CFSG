module

public import CFSG.Quasithin.Vol2.Ch5Sec1L34B45Herm
public import CFSG.Quasithin.Vol2.Ch5Sec1L34E9
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.Background.SmithB45SL3Excl
public import CFSG.Quasithin.Background.SmithB45SL3Herm

public section

namespace CFSG.Quasithin.H13.B45L34

open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup.Layer.Actor
  CFSG.QuasithinUnique.Setup.Layer CFSG.QuasithinUnique.Setup.X7a
  CFSG.LocalAnalysis.ComponentInitial CFSG.Quasithin CFSG.Quasithin.B45SL3 CFSG.Quasithin.H
open CFSG.Quasithin.H.L3Nine (HMod rho mat mat_injective mat_rho)
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag (proj scalars mem_scalars scalars_eq_center)
open scoped MatrixGroups Matrix

theorem mem_center_of_involutive {M : Type*} [Group M] {ψ : M →* M} (hψ : ∀ g, ψ (ψ g) = g)
    {z : M} (hz : z ∈ Subgroup.center M) : ψ z ∈ Subgroup.center M := by
  rw [Subgroup.mem_center_iff] at hz ⊢
  intro y
  rw [← hψ y, ← map_mul, ← map_mul, hz (ψ y)]

theorem exists_herm_model
    {V : Type} [CommGroup V] [Finite V] (hV : ∀ v : V, v ^ 2 = 1)
    {G L : Subgroup (MulAut V)} (hHyp : B4Hyp G L) (hZ : Subgroup.center ↥L = ⊥)
    (hmodel : StatedClassicalModel (↥L ⧸ Subgroup.center ↥L) .PSL 3 2 2)
    (hq : qhatOf G ≤ ((2 : ℚ) : WithTop ℚ)) :
    ∃ (F : Type) (_ : Field F) (_ : Fintype F) (_ : CharP F 2) (hK : Nat.card F = (2 ^ 1) ^ 2)
      (e : LinearFlag.projectiveSL 3 F ≃* ↥L) (Φ : V ≃* HMod 1 F),
      ∀ x v, Φ (((e x : ↥L) : MulAut V) v) = rhoP hK x (Φ v) := by
  classical
  obtain ⟨-, F, _, _, φ₀, hFcard, hcov⟩ := B42SL3.exists_cover hV hHyp (by norm_num) hmodel
  have : Fintype F := Fintype.ofFinite F
  have hF : Fintype.card F = 2 ^ 2 := by rw [Fintype.card_eq_nat_card]; exact hFcard
  have hchar : CharP F 2 := finite_field_prime_power_characteristic Nat.prime_two (by omega) hFcard
  have hV' : ∀ v : V, v * v = 1 := fun v => by rw [← pow_two]; exact hV v
  obtain ⟨W, _, _, _, ⟨θ⟩⟩ := exists_binModel_of_binary hV'
  have hirrV := Bridge.TypeList.irr_of_isIrrSec hHyp.2.2.2
  have hntW : Nontrivial W := by
    obtain ⟨v, -, hv⟩ := IsConcreteLE.exists_of_lt hHyp.2.2.2.1
    replace hv : v ≠ 1 := fun h => hv (h ▸ Subgroup.one_mem _)
    refine ⟨⟨Multiplicative.toAdd (θ v), 0, fun h => hv ?_⟩⟩
    have h1 : θ v = 1 := Multiplicative.toAdd.injective (by simpa using h)
    simpa using congrArg θ.symm h1
  set ρ := B42SL3.repOf θ φ₀ with hρ
  have hker := B42SL3.repOf_ker θ hcov
  have hirr := B42SL3.repOf_irreducible θ hirrV hcov.surjective
  have hnt : ∃ x, ρ x ≠ 1 := ⟨up3 0 0 1, fun h => by
    obtain ⟨c, -, hc⟩ := hker _ h
    exact not_scalar_up3 (F := F) ⟨(c : F), hc⟩⟩
  have hGN : G ≤ Subgroup.normalizer (L : Set (MulAut V)) := B42L2.le_normalizer_of_b4Hyp hHyp
  let bas := Module.finBasis (ZMod 2) W
  obtain ⟨a, b, Wj, hne, hWirr, heq, -, hO, -⟩ := exists_label_pkg hF (by omega) ρ bas hirr hnt
  obtain ⟨e₀⟩ := heq 0
  obtain ⟨A, hA2, -, hAr⟩ := kq_le_iff.1 hq
  have hAWel : CFSG.IsElementaryAbelian 2 ↥(A.map (binPsi θ).toMonoidHom) :=
    (isElemAbelian2_iff_map θ A).1 hA2.2.2
  have hAWne : A.map (binPsi θ).toMonoidHom ≠ ⊥ := by
    rw [Ne, Subgroup.map_eq_bot_iff_of_injective A (binPsi θ).injective]
    exact hA2.2.1
  have hAWn := B42SL3.intertwines_map θ hcov.surjective (hA2.1.trans hGN)
  have h2F : Nat.card W ≤ Nat.card ↥(A.map (binPsi θ).toMonoidHom) ^ 2 *
      Nat.card {w : W // ∀ x ∈ A.map (binPsi θ).toMonoidHom, x w = w} := by
    rw [B42SL3.card_fix_map, Subgroup.card_map_of_injective (binPsi θ).injective, ← natCard_eq θ]
    exact (rAV_le_two_iff hV hA2).1 hAr
  have hk4 : Nat.card F = 4 := by rw [hFcard]; norm_num
  obtain ⟨ω, hω3, hω2⟩ := KGL34P.exists_primitive_cube_root hk4
  rcases natural_or_row ρ hker _ hAWn (by omega) hF hirr hAWne h2F bas hne (Wj 0) (hWirr 0) e₀
    hO with hnat | ⟨hS, hH, hlt⟩
  ·
    exfalso
    obtain ⟨ψ, hψ, E, hE⟩ :=
      B42SL3.exists_natural_of_single hF ρ bas hirr hnat.1 hnat.2 (Wj 0) e₀
    set z := KGL34P.scalarW2 hω3 with hz
    have hzc : z ∈ Subgroup.center (SL(3, F)) := by
      rw [← scalars_eq_center]
      exact KGL34P.scalarW2_mem hω3
    have hψz : ψ z ∈ scalars 3 F := by
      rw [scalars_eq_center]
      exact mem_center_of_involutive hψ hzc
    have hφ : φ₀ (ψ z) = 1 := by
      have h1 : φ₀ (ψ z) ∈ Subgroup.center ↥L := by
        rw [← hcov.map_scalars]
        exact ⟨_, hψz, rfl⟩
      rw [hZ] at h1
      exact h1
    have hρz : ρ (ψ z) = 1 := by
      refine LinearMap.ext fun w => ?_
      rw [hρ, B42SL3.repOf_apply, hφ, OneMemClass.coe_one, map_one]
      rfl
    have hω21 : ω ^ 2 ≠ 1 := by
      intro h
      have h1 : ω = 1 := by
        have := hω3
        rw [pow_succ, h, one_mul] at this
        exact this
      rw [h1] at hω2
      have : (3 : F) = 0 := by linear_combination hω2
      have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
      have : (1 : F) = 0 := by linear_combination this - h2
      exact one_ne_zero this
    obtain ⟨w, hw⟩ := exists_ne (0 : W)
    have hEw : E w = (ω ^ 2) • E w := by
      have h1 := hE (ψ z) w
      rw [hρz, Module.End.one_apply, hψ, hz] at h1
      refine h1.trans ?_
      ext i
      rw [KGL34P.scalarW2, LinearFlag.coe_scalarElement, Matrix.scalar_apply,
        Matrix.mulVec_diagonal, Pi.smul_apply, smul_eq_mul, Units.val_mk0]
    have h0 : E w = 0 := by
      have h1 : (ω ^ 2 - 1) • E w = 0 := by rw [sub_smul, ← hEw, one_smul, sub_self]
      rcases smul_eq_zero.mp h1 with h | h
      · exact absurd (sub_eq_zero.mp h) hω21
      · exact h
    exact hw (E.injective (h0.trans E.map_zero.symm))
  ·
    obtain ⟨m, hm, hfm, hK, ψ, hψ, E, hE⟩ := exists_herm_of_row hF ρ bas hirr hS hH hlt (Wj 0) e₀
    have hm1 : m = 1 := by omega
    subst hm1
    set κ := φ₀.comp ψ with hκ
    have hκs : Function.Surjective κ := fun l => by
      obtain ⟨g, hg⟩ := hcov.surjective l
      exact ⟨ψ g, by rw [hκ, MonoidHom.comp_apply, hψ, hg]⟩
    have hκk : κ.ker = scalars 3 F := by
      ext g
      rw [MonoidHom.mem_ker]
      constructor
      · intro hg
        have h1 : ψ g ∈ scalars 3 F := hcov.ker_le _ hg
        rw [scalars_eq_center] at h1 ⊢
        have := mem_center_of_involutive hψ h1
        rwa [hψ] at this
      · intro hg
        rw [scalars_eq_center] at hg
        have h1 : ψ g ∈ scalars 3 F := by
          rw [scalars_eq_center]
          exact mem_center_of_involutive hψ hg
        have h2 : φ₀ (ψ g) ∈ Subgroup.center ↥L := by
          rw [← hcov.map_scalars]
          exact ⟨_, h1, rfl⟩
        rw [hZ] at h2
        exact h2
    let e : LinearFlag.projectiveSL 3 F ≃* ↥L :=
      (QuotientGroup.quotientMulEquivOfEq hκk.symm).trans
        (QuotientGroup.quotientKerEquivOfSurjective κ hκs)
    have he : ∀ g, e (proj 3 F g) = κ g := fun g => rfl
    refine ⟨F, inferInstance, inferInstance, hchar, hK, e, θ.trans E, fun x v => ?_⟩
    obtain ⟨g, rfl⟩ := LinearFlag.proj_surjective 3 F x
    rw [he, rhoP_proj]
    have h1 : ρ (ψ g) (Multiplicative.toAdd (θ v)) =
        Multiplicative.toAdd (θ (((φ₀ (ψ g) : ↥L) : MulAut V) v)) :=
      B42SL3.repOf_toAdd θ φ₀ (ψ g) v
    have h2 := hE (ψ g) (Multiplicative.toAdd (θ v))
    rw [hψ, h1] at h2
    rw [MulEquiv.trans_apply, MulEquiv.trans_apply, hκ, MonoidHom.comp_apply]
    simpa using h2

end CFSG.Quasithin.H13.B45L34
