module

public import CFSG.LocalAnalysis.StandardType.GGQ2S08RoNFullDiagonal
public import CFSG.LocalAnalysis.StandardType.GGQ2S08RoNMono
public import CFSG.LocalAnalysis.StandardType.GGRemTableBLLineUAct

public section

namespace CFSG.StandardType.E6QTwo

open CFSG.Assembly CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.RankThree.PartOne.KCUnitaryModel (idGram)
open CFSG.SectionRank.OddCover (diagHom coe_diagHom)
open InndiagSU
open CFSG.StandardType.LineU

variable {G : Type} [Group G] {K : Type} [Field K] {n : ℕ}
variable {Bs L : Subgroup G} {x : G}

@[expose] noncomputable def e6QTwoNPermGLSU (hK : Nat.card K = 4)
    (ρ : Equiv.Perm (Fin (n + 1))) :
      ↥(ClassicalGroups.UnitaryFlag.unitarySU 2 1 K (n + 1)) :=
  SeitzReduction.UnitaryPilot.permSU (USixTwo.fieldDataFour hK) ρ⁻¹

theorem e6QTwoNCoePermGLSU (hK : Nat.card K = 4) (ρ : Equiv.Perm (Fin (n + 1))) :
    (e6QTwoNPermGLSU (K := K) hK ρ : GL (Fin (n + 1)) K) =
      TauCeti.permutationGL (k := K) ρ := by
  rw [e6QTwoNPermGLSU, USixTwo.coe_permSU_eq_permutationGL, inv_inv]

@[expose] noncomputable def e6QTwoNFramePerm (hK : Nat.card K = 4) {Q : GL (Fin (n + 1)) K}
    (hQ : Q ∈ primeFormUnitary (USixTwo.fieldDataFour hK) (idGram K (n + 1)))
    (τ : Equiv.Perm (Fin (n + 1))) : MulAut (LargeEvenProj (LargeEvenSUGroup (Fin (n + 1)) K (2 ^
      1))) :=
  MulAut.conj (frameMk (USixTwo.fieldDataFour hK) Q hQ (e6QTwoNPermGLSU hK τ))

theorem e6QTwoNFrameAct_perm (hK : Nat.card K = 4) {Q : GL (Fin (n + 1)) K}
    {hQ : Q ∈ primeFormUnitary (USixTwo.fieldDataFour hK) (idGram K (n + 1))}
    {e : MulAut (LargeEvenProj (LargeEvenSUGroup (Fin (n + 1)) K (2 ^ 1)))} {σ : Fin (n + 1) → Kˣ}
    (he : TableBUD.FrameAct (USixTwo.fieldDataFour hK) Q hQ e σ) (τ : Equiv.Perm (Fin (n + 1))) :
    TableBUD.FrameAct (USixTwo.fieldDataFour hK) Q hQ
      (e6QTwoNFramePerm hK hQ τ * e * (e6QTwoNFramePerm hK hQ τ)⁻¹)
      (σ ∘ ⇑τ.symm) := by
  have : Finite K := USixTwo.finite_of_card_eq_four hK
  have hσn : ∀ k, ((σ k : Kˣ) : K) ^ (2 ^ 1 + 1) = 1 := fun k => by
    rw [show 2 ^ 1 + 1 = 3 by norm_num, ← Units.val_pow_eq_pow_val,
      USixTwo.cube_unit_eq_one hK (σ k), Units.val_one]
  have hmatGL : (e6QTwoNPermGLSU hK τ : GL (Fin (n + 1)) K) * (diagHom (n + 1) σ : GL
    (Fin (n + 1)) K) *
      ((e6QTwoNPermGLSU hK τ : GL (Fin (n + 1)) K))⁻¹ =
        (diagHom (n + 1) (σ ∘ ⇑τ.symm) : GL (Fin (n + 1)) K) := by
    have hcoe : (e6QTwoNPermGLSU hK τ : GL (Fin (n + 1)) K) =
        TauCeti.permutationGL (k := K) τ := e6QTwoNCoePermGLSU hK τ
    have hdiag : (diagHom (n + 1) σ : GL (Fin (n + 1)) K) = TauCeti.diagGL σ := Units.ext (by
      rw [coe_diagHom, TauCeti.diagGL_coe])
    have hdiag' : (diagHom (n + 1) (σ ∘ ⇑τ.symm) : GL (Fin (n + 1)) K) =
        TauCeti.diagGL (σ ∘ ⇑τ.symm) := Units.ext (by rw [coe_diagHom, TauCeti.diagGL_coe])
    rw [hcoe, hdiag, hdiag']
    rw [TauCeti.mul_diagGL_of_coe_eq_permMatrix (TauCeti.permutationGL (k := K) τ) τ.symm
      (TauCeti.permutationGL_coe τ) σ]
    group
  have hmat : (e6QTwoNPermGLSU hK τ : ↥(ClassicalGroups.UnitaryFlag.unitarySU 2 1 K (n + 1))) *
      diagHom (n + 1) σ * (e6QTwoNPermGLSU hK τ)⁻¹ = diagHom (n + 1) (σ ∘ ⇑τ.symm) := by
    simpa using hmatGL
  have hP : (e6QTwoNPermGLSU hK τ : GL (Fin (n + 1)) K) ∈
      primeFormUnitary (USixTwo.fieldDataFour hK) (idGram K (n + 1)) :=
    TableBUE.unitarySU_le_primeFormUnitary (USixTwo.fieldDataFour hK)
      (e6QTwoNPermGLSU hK τ).2
  have hconj := GGQ2S08RoN.e6QTwoNIsSemilin_conj_frameMk (USixTwo.fieldDataFour hK) (Q := Q) hQ
    (e6QTwoNPermGLSU hK τ)
  have hinv := TableBUD.IsSemilin.inv hconj
  have h1 := hconj.mul (USixTwo.fieldDataFour hK) he
    (TableBUD.diagHom_mem_primeFormUnitary (USixTwo.fieldDataFour hK) hσn)
  have h2 := h1.mul (USixTwo.fieldDataFour hK) hinv (Subgroup.inv_mem _ hP)
  rw [show (1 : K ≃+* K) * 1 * 1⁻¹ = 1 from by group] at h2
  simp only [map_one, MulAut.one_apply, inv_one, mul_one] at h2
  rw [hmatGL] at h2
  exact h2


noncomputable def e6QTwoNPermPre (hK : Nat.card K = 4) {Q : GL (Fin (n + 1)) K}
    (hQ : Q ∈ primeFormUnitary (USixTwo.fieldDataFour hK) (idGram K (n + 1)))
    (θ : L ⧸ Subgroup.center L ≃*
      LargeEvenProj (LargeEvenSUGroup (Fin (n + 1)) K (2 ^ 1)))
    (τ : Equiv.Perm (Fin (n + 1))) : ↥L :=
  Classical.choose (QuotientGroup.mk'_surjective (Subgroup.center ↥L)
    (θ.symm (frameMk (USixTwo.fieldDataFour hK) Q hQ
      (e6QTwoNPermGLSU hK τ))))

theorem e6QTwoNPermPre_spec (hK : Nat.card K = 4) {Q : GL (Fin (n + 1)) K}
    (hQ : Q ∈ primeFormUnitary (USixTwo.fieldDataFour hK) (idGram K (n + 1)))
    (θ : L ⧸ Subgroup.center L ≃*
      LargeEvenProj (LargeEvenSUGroup (Fin (n + 1)) K (2 ^ 1)))
    (τ : Equiv.Perm (Fin (n + 1))) :
    θ (QuotientGroup.mk' (Subgroup.center L) (e6QTwoNPermPre hK hQ θ τ)) =
      frameMk (USixTwo.fieldDataFour hK) Q hQ (e6QTwoNPermGLSU hK τ) := by
  classical
  rw [show QuotientGroup.mk' (Subgroup.center L) (e6QTwoNPermPre hK hQ θ τ) =
      θ.symm (frameMk (USixTwo.fieldDataFour hK) Q hQ
        (e6QTwoNPermGLSU hK τ)) from
    Classical.choose_spec (QuotientGroup.mk'_surjective (Subgroup.center ↥L)
      (θ.symm (frameMk (USixTwo.fieldDataFour hK) Q hQ
        (e6QTwoNPermGLSU hK τ)))),
    MulEquiv.apply_symm_apply]

theorem e6QTwoNConjOnQuot_permPre (hK : Nat.card K = 4) {Q : GL (Fin (n + 1)) K}
    (hQ : Q ∈ primeFormUnitary (USixTwo.fieldDataFour hK) (idGram K (n + 1)))
    (θ : L ⧸ Subgroup.center L ≃*
      LargeEvenProj (LargeEvenSUGroup (Fin (n + 1)) K (2 ^ 1)))
    (τ : Equiv.Perm (Fin (n + 1))) :
    e6QTwoNConjOnQuot θ (e6QTwoNPermPre hK hQ θ τ) =
      e6QTwoNFramePerm hK hQ τ := by
  simp only [e6QTwoNConjOnQuot]
  rw [e6QTwoQuotCenterAutHom_conj,
    ← e6QTwoMulAutConjCongr θ
      (QuotientGroup.mk' (Subgroup.center L) (e6QTwoNPermPre hK hQ θ τ)),
    e6QTwoNPermPre_spec hK hQ θ τ]
  rfl


end CFSG.StandardType.E6QTwo

end
