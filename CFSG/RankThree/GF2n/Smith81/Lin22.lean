module

public import CFSG.RankThree.GF2n.Smith81.LinStmt
public import CFSG.RankThree.GF2n.Smith81.Lin31TwoModel
import CFSG.RankThree.GF2n.Smith81.Lin22Model
import CFSG.RankThree.GF2n.Smith81.Lin22Gamma
import CFSG.RankThree.GF2n.Smith81.Lin22Root
import CFSG.RankThree.GF2n.Smith81.Lin22SL2
import CFSG.RankThree.GF2n.Smith81.Lin31Two

public section

namespace CFSG.RankThree.GF2n.Smith81

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Stroth80
open scoped commutatorElement Matrix MatrixGroups

section CardGamma

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

namespace TensorModel

theorem card_Gamma_inf_SL_dvd (TM : TensorModel M Q Z B) (hc : Ctx M Q Z B)
    (hw : Width Q Z 2) :
    Nat.card ↥(TM.Gamma ⊓ StatedSL 2 TM.F) ∣ 2 * (Nat.card TM.F - 1) := by
  have h4 : 4 ≤ Nat.card TM.F := by
    rw [TM.card_F]
    exact hc.hyp.q4
  obtain ⟨u₀, hu₀, hBu₀⟩ := exists_plane_of_ctx (TM := TM) hc
  obtain ⟨H, μ, hHΓ, -, -, hHμ, hHdet, hHrel⟩ :=
    torus_lemma_full (TM := TM) hc hw hc hu₀ hBu₀
  obtain ⟨r, h, hr0, hcoe, hord⟩ :=
    SL2Torus.exists_smul_mem_orderOf (F := TM.F) h4 hu₀ hHμ hHdet hHrel
  let Γ₁ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) TM.F) :=
    TM.Gamma.comap (Matrix.SpecialLinearGroup.toGL :
      Matrix.SpecialLinearGroup (Fin 2) TM.F →* GL (Fin 2) TM.F)
  have htoGL : (Matrix.SpecialLinearGroup.toGL h : GL (Fin 2) TM.F) =
      Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.mk0 r hr0) * H := by
    apply Units.ext
    change (h : Matrix (Fin 2) (Fin 2) TM.F) =
      (Matrix.scalar (Fin 2) (Units.mk0 r hr0 : TM.F)) *
        (H : Matrix (Fin 2) (Fin 2) TM.F)
    rw [hcoe, Matrix.smul_eq_diagonal_mul]
    simp [Matrix.scalar_apply]
  have hconj : ∀ X : Matrix.SpecialLinearGroup (Fin 2) TM.F,
      Matrix.SpecialLinearGroup.toGL (h * X * h⁻¹) =
        H * Matrix.SpecialLinearGroup.toGL X * H⁻¹ := by
    intro X
    rw [map_mul, map_mul, map_inv, htoGL, mul_inv_rev]
    set C : GL (Fin 2) TM.F :=
      Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.mk0 r hr0)
    calc C * H * Matrix.SpecialLinearGroup.toGL X * (H⁻¹ * C⁻¹)
        = C * (H * Matrix.SpecialLinearGroup.toGL X * H⁻¹) * C⁻¹ := by group
      _ = (H * Matrix.SpecialLinearGroup.toGL X * H⁻¹) * C * C⁻¹ := by
        rw [Matrix.GeneralLinearGroup.scalar_commute]
      _ = H * Matrix.SpecialLinearGroup.toGL X * H⁻¹ := by group
  have hN : h ∈ Subgroup.normalizer (Γ₁ : Set (Matrix.SpecialLinearGroup (Fin 2) TM.F)) := by
    rw [Subgroup.mem_normalizer_iff]
    intro X
    constructor
    · intro hX
      change Matrix.SpecialLinearGroup.toGL (h * X * h⁻¹) ∈ TM.Gamma
      rw [hconj X]
      exact TM.Gamma.mul_mem (TM.Gamma.mul_mem hHΓ hX) (TM.Gamma.inv_mem hHΓ)
    · intro hX
      change Matrix.SpecialLinearGroup.toGL (h * X * h⁻¹) ∈ TM.Gamma at hX
      rw [hconj X] at hX
      change Matrix.SpecialLinearGroup.toGL X ∈ TM.Gamma
      have e : Matrix.SpecialLinearGroup.toGL X =
          H⁻¹ * (H * Matrix.SpecialLinearGroup.toGL X * H⁻¹) * H := by group
      rw [e]
      exact TM.Gamma.mul_mem (TM.Gamma.mul_mem (TM.Gamma.inv_mem hHΓ) hX) hHΓ
  have htop : Γ₁ ≠ ⊤ := by
    intro hΓ
    apply not_statedSL_le_Gamma (TM := TM) hc
    intro A hA
    rw [CFSG.Open.StatedAPI.statedSL_eq_range_toGL] at hA
    obtain ⟨X, rfl⟩ := hA
    have hX : X ∈ Γ₁ := by rw [hΓ]; exact Subgroup.mem_top X
    change Matrix.SpecialLinearGroup.toGL X ∈ TM.Gamma at hX
    exact hX
  have hO : ∀ P : Subgroup (Matrix.SpecialLinearGroup (Fin 2) TM.F), P ≤ Γ₁ →
      Γ₁ ≤ Subgroup.normalizer (P : Set (Matrix.SpecialLinearGroup (Fin 2) TM.F)) →
      IsPGroup 2 P → P = ⊥ :=
    fun P hP hNP h2 => eq_bot_of_isPGroup_two (TM := TM) hc hP hNP h2
  have hdvd := SL2Torus.card_dvd_of_mem_normalizer (F := TM.F) h4 hord hN hO htop
  rwa [show Nat.card Γ₁ = Nat.card ↥(TM.Gamma ⊓ StatedSL 2 TM.F) from
    TensorModel.card_comap_Gamma (TM := TM)] at hdvd

end TensorModel

end CardGamma

theorem lin22Statement_holds : Lin22Statement := by
  intro G _ _ M Q Z B hc hD2 hno
  obtain ⟨TM⟩ := exists_tensorModel_of_not_noA2 hc hD2 hno
  have hw : Width Q Z 2 := by
    have := hD2.1
    unfold Width
    simpa using this
  have hdvd : Nat.card ↥(TM.Gamma ⊓ StatedSL 2 TM.F) ∣ 2 * (Nat.card TM.F - 1) :=
    TM.card_Gamma_inf_SL_dvd hc hw
  have hCD : CentDvdN 2 M Q Z (Lgen M (LB M Q B)) :=
    TM.centDvdN_two_of_card_dvd hc hdvd
  obtain ⟨W₁, W₂, hLS, -, -⟩ := exists_two_planes_of_model hc TM hw hCD
  exact ⟨W₁, W₂, hLS⟩

end CFSG.RankThree.GF2n.Smith81
