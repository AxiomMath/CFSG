module

public import CFSG.LocalAnalysis.StandardType.GGQ2S08RoNSU
public import CFSG.LocalAnalysis.StandardType.GGQ2S08RoNDiag
public import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylE6QTwoSixPermAux
public import CFSG.LocalAnalysis.StandardType.GGBstarDeltaUnitarySemi

public section

namespace CFSG.StandardType.E6QTwo

open CFSG CFSG.Assembly
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.SectionRank.OddCover (diagHom coe_diagHom)
open InndiagSU
open CFSG.RankThree.PartOne.KCUnitaryModel (idGram)

variable {G : Type} [Group G] [Finite G] {Bs L : Subgroup G} {x : G} {n : ℕ}
variable {K : Type} [Field K] [Finite K]

@[expose] noncomputable def e6QTwoNConjOnQuot
    (θ : L ⧸ Subgroup.center L ≃* LargeEvenProj (LargeEvenSUGroup (Fin (n + 1)) K (2 ^ 1)))
    (g : ↥L) : MulAut (LargeEvenProj (LargeEvenSUGroup (Fin (n + 1)) K (2 ^ 1))) :=
  (MulAut.congr θ) (e6QTwoQuotCenterAutHom ↥L (MulAut.conj g))

omit [Finite G] [Finite K]
  in
theorem e6QTwoNConjOnQuot_mk
    (θ : L ⧸ Subgroup.center L ≃* LargeEvenProj (LargeEvenSUGroup (Fin (n + 1)) K (2 ^ 1)))
    (g l : ↥L) :
    e6QTwoNConjOnQuot θ g (θ (QuotientGroup.mk' (Subgroup.center L) l)) =
      θ (QuotientGroup.mk' (Subgroup.center L) (g * l * g⁻¹)) := by
  rw [e6QTwoNConjOnQuot, e6QTwoMulAutCongrApply, e6QTwoQuotCenterAutHom_mk,
    MulAut.conj_apply]

namespace GGQ2S08RoN

theorem conjOnQuot_eq (c : GGQ2S08RoN n Bs L x) (ν : ↥L) :
    e6QTwoNConjOnQuot c.θ ν =
      MulAut.conj (c.θ (QuotientGroup.mk' (Subgroup.center ↥L) ν)) := by
  ext r
  obtain ⟨q, rfl⟩ := c.θ.surjective r
  obtain ⟨l, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center ↥L) q
  rw [e6QTwoNConjOnQuot_mk, MulAut.conj_apply, map_mul, map_mul, map_inv, map_mul, map_mul,
    map_inv]

omit [Finite K]
  in
theorem e6QTwoNIsSemilin_conj_frameMk (h : UnitaryFieldData 2 1 K) {Q : GL (Fin (n + 1)) K}
    (hQ : Q ∈ primeFormUnitary h (idGram K (n + 1)))
    (P : ↥(ClassicalGroups.UnitaryFlag.unitarySU 2 1 K (n + 1))) :
    IsSemilin (frameMk h Q hQ) (MulAut.conj (frameMk h Q hQ P)) (P : GL (Fin (n + 1)) K) 1 := by
  intro u v huv
  have hu : P * u * P⁻¹ = v := by
    refine Subtype.ext ?_
    simpa using huv.symm
  have hmul : frameMk h Q hQ P * frameMk h Q hQ u * (frameMk h Q hQ P)⁻¹ =
      frameMk h Q hQ (P * u * P⁻¹) := by
    rw [map_mul, map_mul, map_inv]
  rw [MulAut.conj_apply, hmul, hu]

omit [Finite G] [Finite K]
  in
theorem e6QTwoNFrameAction_conj
    (θ : L ⧸ Subgroup.center L ≃* LargeEvenProj (LargeEvenSUGroup (Fin (n + 1)) K (2 ^ 1)))
    (hNL : Bs ≤ Subgroup.normalizer (L : Set G)) {g : G} (hgL : g ∈ L)
    {b : ↥Bs} (hb : g * (b : G) * g⁻¹ ∈ Bs) :
    e6QTwoNFrameAction hNL θ ⟨g * (b : G) * g⁻¹, hb⟩ =
      e6QTwoNConjOnQuot θ ⟨g, hgL⟩ * e6QTwoNFrameAction hNL θ b *
        (e6QTwoNConjOnQuot θ ⟨g, hgL⟩)⁻¹ := by
  let Φ : MulAut ↥L →* MulAut (LargeEvenProj (LargeEvenSUGroup (Fin (n + 1)) K (2 ^ 1))) :=
    (MulAut.congr θ).toMonoidHom.comp (e6QTwoQuotCenterAutHom ↥L)
  have hconj : e6QTwoBstarConjAction hNL ⟨g * (b : G) * g⁻¹, hb⟩ =
      MulAut.conj (⟨g, hgL⟩ : ↥L) * e6QTwoBstarConjAction hNL b *
        (MulAut.conj (⟨g, hgL⟩ : ↥L))⁻¹ := by
    ext l
    rw [e6QTwoBstarConjAction_apply]
    simp only [MulAut.mul_apply, MulAut.conj_apply, MulAut.conj_inv_apply, Subgroup.coe_mul,
      Subgroup.coe_inv]
    rw [e6QTwoBstarConjAction_apply]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    group
  have hβ : e6QTwoNFrameAction hNL θ ⟨g * (b : G) * g⁻¹, hb⟩ =
      Φ (e6QTwoBstarConjAction hNL ⟨g * (b : G) * g⁻¹, hb⟩) := rfl
  have hβb : e6QTwoNFrameAction hNL θ b = Φ (e6QTwoBstarConjAction hNL b) := rfl
  have hw : e6QTwoNConjOnQuot θ ⟨g, hgL⟩ = Φ (MulAut.conj (⟨g, hgL⟩ : ↥L)) := rfl
  rw [hβ, hβb, hw, hconj, map_mul, map_mul, map_inv]

theorem exists_monomial_of_mem_normalizer (c : GGQ2S08RoN n Bs L x) {ν : G} (hnL : ν ∈ L)
    (hnN : ν ∈ Subgroup.normalizer (Bs : Set G)) :
    ∃ (g : ↥(ClassicalGroups.UnitaryFlag.unitarySU 2 1 c.K (n + 1))) (τ : Equiv.Perm (Fin (n + 1)))
      (u : Fin (n + 1) → c.Kˣ),
      InndiagSU.frameMk (USixTwo.fieldDataFour c.hK) c.Q c.hQ g =
        c.θ (QuotientGroup.mk' (Subgroup.center ↥L) ⟨ν, hnL⟩) ∧
      (g : GL (Fin (n + 1)) c.K) = CFSG.RankThree.Classical.permGL τ * diagHom (n + 1) u ∧
      ∀ (b : Bs) (hb : ν * (b : G) * ν⁻¹ ∈ Bs),
        ∃ μ : c.Kˣ, ∀ k, c.diag ⟨ν * (b : G) * ν⁻¹, hb⟩ k = μ * c.diag b (τ.symm k) := by
  classical
  set hU := USixTwo.fieldDataFour c.hK with hhU
  have hK' : Nat.card c.K = (2 ^ 1) ^ 2 := by rw [c.hK]; norm_num
  set r := c.θ (QuotientGroup.mk' (Subgroup.center ↥L) ⟨ν, hnL⟩) with hr
  obtain ⟨g, hgr⟩ := InndiagSU.frameMk_surjective hU c.Q c.hQ r
  have hgU : (g : GL (Fin (n + 1)) c.K) ∈ primeFormUnitary hU
      (CFSG.RankThree.PartOne.KCUnitaryModel.idGram c.K (n + 1)) :=
    TableBUE.unitarySU_le_primeFormUnitary hU g.2
  have hginvU : (g : GL (Fin (n + 1)) c.K)⁻¹ ∈ primeFormUnitary hU
      (CFSG.RankThree.PartOne.KCUnitaryModel.idGram c.K (n + 1)) := Subgroup.inv_mem _ hgU
  have hdiagU : ∀ σ : Fin (n + 1) → c.Kˣ, diagHom (n + 1) σ ∈ primeFormUnitary hU
      (CFSG.RankThree.PartOne.KCUnitaryModel.idGram c.K (n + 1)) := fun σ =>
    TableBUD.diagHom_mem_primeFormUnitary hU (c.norm_one σ)
  have key : ∀ (b : Bs) (hb : ν * (b : G) * ν⁻¹ ∈ Bs), ∃ μ : c.Kˣ,
      (g : GL (Fin (n + 1)) c.K) * diagHom (n + 1) (c.diag b) * (g : GL (Fin (n + 1)) c.K)⁻¹ =
        Matrix.GeneralLinearGroup.scalar (Fin (n + 1)) μ * diagHom (n + 1) (c.diag ⟨ν * (b : G) *
          ν⁻¹, hb⟩) := by
    intro b hb
    have hact : c.act ⟨ν * (b : G) * ν⁻¹, hb⟩ = MulAut.conj r * c.act b * (MulAut.conj r)⁻¹ := by
      change e6QTwoNFrameAction c.hNL c.θ ⟨ν * (b : G) * ν⁻¹, hb⟩ = _
      rw [e6QTwoNFrameAction_conj c.θ c.hNL hnL hb, c.conjOnQuot_eq]
    have h1 : InndiagSU.IsSemilin (InndiagSU.frameMk hU c.Q c.hQ) (MulAut.conj r)
        (g : GL (Fin (n + 1)) c.K) 1 := by
      have h := e6QTwoNIsSemilin_conj_frameMk hU c.hQ g
      rwa [hgr] at h
    have hgl : ∀ X : GL (Fin (n + 1)) c.K, glAut (1 : c.K ≃+* c.K) X = X := fun X => by
      rw [map_one, MulAut.one_apply]
    have h3 := TableBUD.IsSemilin.inv h1
    rw [inv_one, hgl] at h3
    have h12 := h1.mul hU (c.frameDiag_diag b) (hdiagU _)
    rw [hgl, one_mul] at h12
    have h123 := h12.mul hU h3 hginvU
    rw [hgl, one_mul, ← hact] at h123
    obtain ⟨μ, hμ⟩ := TableBUD.IsSemilin.eq_smul hU hK' (by have := c.hn; omega)
      (by have := c.hn; simp; omega) (p := 3)
      (by norm_num) (by norm_num) c.hQ
      (Subgroup.mul_mem _ (Subgroup.mul_mem _ hgU (hdiagU _)) hginvU) (hdiagU _) h123
      (c.frameDiag_diag ⟨ν * (b : G) * ν⁻¹, hb⟩)
    exact ⟨μ, hμ⟩
  have hscal : ∀ (μ : c.Kˣ) (σ : Fin (n + 1) → c.Kˣ),
      Matrix.GeneralLinearGroup.scalar (Fin (n + 1)) μ * diagHom (n + 1) σ = diagHom (n + 1) (fun
        k => μ * σ k) := by
    intro μ σ
    apply Units.ext
    rw [Units.val_mul, coe_diagHom, coe_diagHom, Matrix.GeneralLinearGroup.coe_scalar,
      Matrix.scalar_apply, Matrix.diagonal_mul_diagonal]
    rfl
  have hmono : ∀ t : Fin (n + 1) → c.Kˣ, ∏ i, t i = 1 →
      ∃ t' : Fin (n + 1) → c.Kˣ,
        (g : GL (Fin (n + 1)) c.K) * diagHom (n + 1) t * (g : GL (Fin (n + 1)) c.K)⁻¹ =
        diagHom (n + 1) t' := by
    intro t _
    obtain ⟨b, hb⟩ := c.exists_diag_eq (fun k => (t (0 : Fin (n + 1)))⁻¹ * t k) (by simp)
    have hb' : ν * (b : G) * ν⁻¹ ∈ Bs := (Subgroup.mem_normalizer_iff.mp hnN (b : G)).mp b.2
    obtain ⟨μ, hμ⟩ := key b hb'
    refine ⟨fun k => t (0 : Fin (n + 1)) * (μ * c.diag ⟨ν * (b : G) * ν⁻¹, hb'⟩ k), ?_⟩
    have ht : diagHom (n + 1) t =
        Matrix.GeneralLinearGroup.scalar (Fin (n + 1)) (t (0 : Fin (n + 1))) * diagHom (n + 1)
          (c.diag b) := by
      rw [hscal, hb]
      congr 1
      funext k
      rw [mul_inv_cancel_left]
    rw [ht, ← hscal, ← hscal, ← hμ]
    have hc := TypeA.PGLTor.scalar_mul_comm (t (0 : Fin (n + 1))) (g : GL (Fin (n + 1)) c.K)
    calc (g : GL (Fin (n + 1)) c.K) *
          (Matrix.GeneralLinearGroup.scalar (Fin (n + 1)) (t (0 : Fin (n + 1))) * diagHom (n + 1)
            (c.diag b)) *
          (g : GL (Fin (n + 1)) c.K)⁻¹
        = ((g : GL (Fin (n + 1)) c.K) * Matrix.GeneralLinearGroup.scalar (Fin (n + 1)) (t (0 : Fin
          (n + 1)))) *
            diagHom (n + 1) (c.diag b) * (g : GL (Fin (n + 1)) c.K)⁻¹ := by group
      _ = _ := by rw [← hc]; group
  obtain ⟨τ, u, hgτ⟩ := ggQ2s08rN_exists_monomial c.hK hmono
  refine ⟨g, τ, u, hgr, hgτ, fun b hb => ?_⟩
  obtain ⟨μ, hμ⟩ := key b hb
  have hconj : (g : GL (Fin (n + 1)) c.K) * diagHom (n + 1) (c.diag b) * (g : GL (Fin (n + 1))
    c.K)⁻¹ =
      diagHom (n + 1) (c.diag b ∘ ⇑τ.symm) := by
    rw [hgτ, mul_inv_rev, ← CFSG.RankThree.Classical2.permGL_mul_diagHom_mul_inv τ (c.diag b)]
    have hcomm : diagHom (n + 1) u * diagHom (n + 1) (c.diag b) * (diagHom (n + 1) u)⁻¹ = diagHom
      (n + 1) (c.diag b) := by
      rw [← map_inv, ← map_mul, ← map_mul, mul_comm u, mul_inv_cancel_right]
    calc CFSG.RankThree.Classical.permGL τ * diagHom (n + 1) u * diagHom (n + 1) (c.diag b) *
          ((diagHom (n + 1) u)⁻¹ * (CFSG.RankThree.Classical.permGL τ)⁻¹)
        = CFSG.RankThree.Classical.permGL τ *
            (diagHom (n + 1) u * diagHom (n + 1) (c.diag b) * (diagHom (n + 1) u)⁻¹) *
            (CFSG.RankThree.Classical.permGL τ)⁻¹ := by group
      _ = _ := by rw [hcomm]
  rw [hconj, hscal] at hμ
  have hfun := (CFSG.SectionRank.OddCover.diagHom_injective (n := n + 1) (K := c.K)) hμ
  refine ⟨μ⁻¹, fun k => ?_⟩
  have hk := congrFun hfun k
  simp only [Function.comp_apply] at hk
  rw [hk, inv_mul_cancel_left]



theorem exists_perm_of_mem_normalizer (c : GGQ2S08RoN n Bs L x) {ν : G} (hnL : ν ∈ L)
    (hnN : ν ∈ Subgroup.normalizer (Bs : Set G)) :
    ∃ τ : Equiv.Perm (Fin (n + 1)), ∀ (b : Bs) (hb : ν * (b : G) * ν⁻¹ ∈ Bs),
      ∃ μ : c.Kˣ, ∀ k, c.diag ⟨ν * (b : G) * ν⁻¹, hb⟩ k = μ * c.diag b (τ.symm k) := by
  obtain ⟨-, τ, -, -, -, h⟩ := c.exists_monomial_of_mem_normalizer hnL hnN
  exact ⟨τ, h⟩

end GGQ2S08RoN

end CFSG.StandardType.E6QTwo

end
