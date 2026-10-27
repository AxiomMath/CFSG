module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylE6QTwoSixPermAux7
public import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylE6QTwoSixFrameAux2
public import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylE6QTwoSixCenter
public import CFSG.LocalAnalysis.StandardType.GGQ2S08RoCloseDefs
public import CFSG.LocalAnalysis.StandardType.GGHdRo7SULCoordModelA
public import CFSG.LocalAnalysis.StandardType.GGQ2S08RoSixSU

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly E6QTwo
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.SectionRank.OddCover (diagHom coe_diagHom)

structure GGQ2S08RoSix {G : Type} [Group G] [Finite G] (Bs L : Subgroup G) (x : G) where
  K : Type
  instField : Field K
  instFinite : Finite K
  hK : Nat.card K = 4
  θ : L ⧸ Subgroup.center L ≃* LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1))
  Q : GL (Fin 6) K
  hQ : Q ∈ primeFormUnitary (USixTwo.fieldDataFour hK)
    (CFSG.RankThree.PartOne.KCUnitaryModel.idGram K 6)
  hperf : commutator ↥L = ⊤
  hBs : IsElemAbelian 3 Bs
  hcard : Nat.card Bs = 3 ^ 6
  hx : x ∈ Bs
  hxL : x ∈ L
  hx1 : x ≠ 1
  hBL : Bs ⊓ Subgroup.centralizer (L : Set G) = Subgroup.zpowers x
  hstar : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ 3 = 1 → g ∈ Bs
  hNL : Bs ≤ Subgroup.normalizer (L : Set G)
  hI : ∀ b ∈ Bs, ∃ ψ ∈ LargeEvenMatConjImage
      (LargeEvenProjMk (LargeEvenSUGroup (Fin 6) K (2 ^ 1))) (LargeEvenGUSet (Fin 6) K (2 ^ 1)),
    LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) ψ
  hLx : L ≤ Subgroup.centralizer {x}
  hLsn : IsSubnormal L (Subgroup.centralizer {x})
  hfull : ∀ σ : Fin 6 → Kˣ, σ (0 : Fin 6) = 1 → (∀ k, σ k ^ 3 = 1) →
    ∃ b : Bs, TableBUD.FrameAct (USixTwo.fieldDataFour hK) Q hQ
      (e6QTwoSixFrameAction hNL θ b) σ
  hrange5 : Nat.card ↥(e6QTwoSixFrameAction hNL θ).range = 3 ^ 5

attribute [instance] GGQ2S08RoSix.instField GGQ2S08RoSix.instFinite

namespace GGQ2S08RoSix

variable {G : Type} [Group G] [Finite G] {Bs L : Subgroup G} {x : G}

noncomputable abbrev act (c : GGQ2S08RoSix Bs L x) :
    Bs →* MulAut (LargeEvenProj (LargeEvenSUGroup (Fin 6) c.K (2 ^ 1))) :=
  e6QTwoSixFrameAction c.hNL c.θ

abbrev FrameDiag (c : GGQ2S08RoSix Bs L x) (b : Bs) (σ : Fin 6 → c.Kˣ) : Prop :=
  TableBUD.FrameAct (USixTwo.fieldDataFour c.hK) c.Q c.hQ (c.act b) σ

theorem exists_frameDiag (c : GGQ2S08RoSix Bs L x) (b : Bs) :
    ∃ σ : Fin 6 → c.Kˣ, σ (0 : Fin 6) = 1 ∧ c.FrameDiag b σ := by
  obtain ⟨σ, h0, -, h⟩ := e6QTwoSixFrameAct_of_mem_range c.hK c.hNL c.θ c.hfull c.hrange5
    (MonoidHom.mem_range.mpr ⟨b, rfl⟩)
  exact ⟨σ, h0, h⟩

@[expose] noncomputable def diag (c : GGQ2S08RoSix Bs L x) (b : Bs) : Fin 6 → c.Kˣ :=
  (c.exists_frameDiag b).choose

theorem diag_zero (c : GGQ2S08RoSix Bs L x) (b : Bs) : c.diag b (0 : Fin 6) = 1 :=
  (c.exists_frameDiag b).choose_spec.1

theorem frameDiag_diag (c : GGQ2S08RoSix Bs L x) (b : Bs) : c.FrameDiag b (c.diag b) :=
  (c.exists_frameDiag b).choose_spec.2


theorem cube (c : GGQ2S08RoSix Bs L x) (t : c.Kˣ) : t ^ 3 = 1 :=
  USixTwo.cube_unit_eq_one c.hK t

theorem norm_one (c : GGQ2S08RoSix Bs L x) (σ : Fin 6 → c.Kˣ) (k : Fin 6) :
    ((σ k : c.Kˣ) : c.K) ^ (2 ^ 1 + 1) = 1 := by
  rw [show (2 : ℕ) ^ 1 + 1 = 3 by norm_num, ← Units.val_pow_eq_pow_val, c.cube, Units.val_one]

theorem frameDiag_eq_smul (c : GGQ2S08RoSix Bs L x) {b : Bs} {σ σ' : Fin 6 → c.Kˣ}
    (h : c.FrameDiag b σ) (h' : c.FrameDiag b σ') : ∃ μ : c.Kˣ, ∀ k, σ' k = μ * σ k :=
  TableBUD.FrameAct.eq_smul (n := 1) (h := USixTwo.fieldDataFour c.hK)
    (by rw [c.hK]; norm_num) (by norm_num : 3 ≤ 6) (by norm_num : (6, 2 ^ 1) ≠ (3, 2))
    (p := 3) (by norm_num) (by norm_num : 3 ∣ 2 ^ 1 + 1) (c.norm_one σ) (c.norm_one σ') h h'

theorem diag_eq_of_frameDiag (c : GGQ2S08RoSix Bs L x) {b : Bs} {σ : Fin 6 → c.Kˣ}
    (h0 : σ (0 : Fin 6) = 1) (h : c.FrameDiag b σ) : c.diag b = σ :=
  e6QTwoSixFrameAct_inj c.hK (c.diag_zero b) h0 (fun k => c.cube _) (fun k => c.cube _)
    (c.frameDiag_diag b) h

theorem exists_eq_smul_diag (c : GGQ2S08RoSix Bs L x) {b : Bs} {σ : Fin 6 → c.Kˣ}
    (h : c.FrameDiag b σ) : ∃ μ : c.Kˣ, ∀ k, σ k = μ * c.diag b k :=
  c.frameDiag_eq_smul (c.frameDiag_diag b) h

theorem diag_mul (c : GGQ2S08RoSix Bs L x) (b b' : Bs) :
    c.diag (b * b') = c.diag b * c.diag b' := by
  refine c.diag_eq_of_frameDiag ?_ ?_
  · rw [Pi.mul_apply, c.diag_zero, c.diag_zero, mul_one]
  · have h := TableBUD.FrameAct.mul (c.frameDiag_diag b) (c.frameDiag_diag b')
      (c.norm_one (c.diag b'))
    rwa [← map_mul] at h

theorem diag_one (c : GGQ2S08RoSix Bs L x) : c.diag 1 = 1 := by
  refine c.diag_eq_of_frameDiag rfl ?_
  rw [FrameDiag, map_one]
  exact TableBUD.frameAct_one

theorem diag_eq_one_iff (c : GGQ2S08RoSix Bs L x) (b : Bs) :
    c.diag b = 1 ↔ (b : G) ∈ Subgroup.zpowers x := by
  have hker := e6QTwoSixFrameAction_ker_eq c.θ c.hNL c.hperf c.hBL
  constructor
  · intro h
    have h1 : c.act b = 1 := by
      have hb := c.frameDiag_diag b
      rw [h] at hb
      exact TableBUD.FrameAct.unique (h := USixTwo.fieldDataFour c.hK) (Q := c.Q) (hQ := c.hQ)
        (hσ := c.norm_one 1) hb TableBUD.frameAct_one
    have hb : b ∈ (c.act).ker := h1
    rw [show (c.act).ker = (e6QTwoSixFrameAction c.hNL c.θ).ker from rfl, hker,
      Subgroup.mem_subgroupOf] at hb
    exact hb
  · intro h
    have hb : b ∈ (e6QTwoSixFrameAction c.hNL c.θ).ker := by
      rw [hker, Subgroup.mem_subgroupOf]
      exact h
    refine c.diag_eq_of_frameDiag rfl ?_
    rw [FrameDiag, show c.act b = 1 from hb]
    exact TableBUD.frameAct_one

theorem exists_diag_eq (c : GGQ2S08RoSix Bs L x) (σ : Fin 6 → c.Kˣ) (h0 : σ (0 : Fin 6) = 1) :
    ∃ b : Bs, c.diag b = σ := by
  obtain ⟨b, hb⟩ := c.hfull σ h0 (fun k => c.cube _)
  exact ⟨b, c.diag_eq_of_frameDiag h0 hb⟩


theorem conjOnQuot_eq (c : GGQ2S08RoSix Bs L x) (n : ↥L) :
    e6QTwoSixConjOnQuot c.θ n = MulAut.conj (c.θ (QuotientGroup.mk' (Subgroup.center ↥L) n)) := by
  ext r
  obtain ⟨q, rfl⟩ := c.θ.surjective r
  obtain ⟨l, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center ↥L) q
  rw [e6QTwoSixConjOnQuot_mk, MulAut.conj_apply, map_mul, map_mul, map_inv, map_mul, map_mul,
    map_inv]

theorem exists_monomial_of_mem_normalizer (c : GGQ2S08RoSix Bs L x) {n : G} (hnL : n ∈ L)
    (hnN : n ∈ Subgroup.normalizer (Bs : Set G)) :
    ∃ (g : ↥(ClassicalGroups.UnitaryFlag.unitarySU 2 1 c.K 6)) (τ : Equiv.Perm (Fin 6))
      (u : Fin 6 → c.Kˣ),
      InndiagSU.frameMk (USixTwo.fieldDataFour c.hK) c.Q c.hQ g =
        c.θ (QuotientGroup.mk' (Subgroup.center ↥L) ⟨n, hnL⟩) ∧
      (g : GL (Fin 6) c.K) = CFSG.RankThree.Classical.permGL τ * diagHom 6 u ∧
      ∀ (b : Bs) (hb : n * (b : G) * n⁻¹ ∈ Bs),
        ∃ μ : c.Kˣ, ∀ k, c.diag ⟨n * (b : G) * n⁻¹, hb⟩ k = μ * c.diag b (τ.symm k) := by
  classical
  set hU := USixTwo.fieldDataFour c.hK with hhU
  have hK' : Nat.card c.K = (2 ^ 1) ^ 2 := by rw [c.hK]; norm_num
  set r := c.θ (QuotientGroup.mk' (Subgroup.center ↥L) ⟨n, hnL⟩) with hr
  obtain ⟨g, hgr⟩ := InndiagSU.frameMk_surjective hU c.Q c.hQ r
  have hgU : (g : GL (Fin 6) c.K) ∈ primeFormUnitary hU
      (CFSG.RankThree.PartOne.KCUnitaryModel.idGram c.K 6) :=
    TableBUE.unitarySU_le_primeFormUnitary hU g.2
  have hginvU : (g : GL (Fin 6) c.K)⁻¹ ∈ primeFormUnitary hU
      (CFSG.RankThree.PartOne.KCUnitaryModel.idGram c.K 6) := Subgroup.inv_mem _ hgU
  have hdiagU : ∀ σ : Fin 6 → c.Kˣ, diagHom 6 σ ∈ primeFormUnitary hU
      (CFSG.RankThree.PartOne.KCUnitaryModel.idGram c.K 6) := fun σ =>
    TableBUD.diagHom_mem_primeFormUnitary hU (c.norm_one σ)
  have key : ∀ (b : Bs) (hb : n * (b : G) * n⁻¹ ∈ Bs), ∃ μ : c.Kˣ,
      (g : GL (Fin 6) c.K) * diagHom 6 (c.diag b) * (g : GL (Fin 6) c.K)⁻¹ =
        Matrix.GeneralLinearGroup.scalar (Fin 6) μ * diagHom 6 (c.diag ⟨n * (b : G) * n⁻¹, hb⟩) := by
    intro b hb
    have hact : c.act ⟨n * (b : G) * n⁻¹, hb⟩ = MulAut.conj r * c.act b * (MulAut.conj r)⁻¹ := by
      change e6QTwoSixFrameAction c.hNL c.θ ⟨n * (b : G) * n⁻¹, hb⟩ = _
      rw [e6QTwoSixFrameAction_conj c.θ c.hNL hnL hb, c.conjOnQuot_eq]
    have h1 : InndiagSU.IsSemilin (InndiagSU.frameMk hU c.Q c.hQ) (MulAut.conj r)
        (g : GL (Fin 6) c.K) 1 := by
      have h := e6QTwoSixIsSemilin_conj_frameMk hU c.hQ g
      rwa [hgr] at h
    have hgl : ∀ X : GL (Fin 6) c.K, glAut (1 : c.K ≃+* c.K) X = X := fun X => by
      rw [map_one, MulAut.one_apply]
    have h3 := TableBUD.IsSemilin.inv h1
    rw [inv_one, hgl] at h3
    have h12 := h1.mul hU (c.frameDiag_diag b) (hdiagU _)
    rw [hgl, one_mul] at h12
    have h123 := h12.mul hU h3 hginvU
    rw [hgl, one_mul, ← hact] at h123
    obtain ⟨μ, hμ⟩ := TableBUD.IsSemilin.eq_smul hU hK' (by norm_num) (by norm_num) (p := 3)
      (by norm_num) (by norm_num) c.hQ
      (Subgroup.mul_mem _ (Subgroup.mul_mem _ hgU (hdiagU _)) hginvU) (hdiagU _) h123
      (c.frameDiag_diag ⟨n * (b : G) * n⁻¹, hb⟩)
    exact ⟨μ, hμ⟩
  have hscal : ∀ (μ : c.Kˣ) (σ : Fin 6 → c.Kˣ),
      Matrix.GeneralLinearGroup.scalar (Fin 6) μ * diagHom 6 σ = diagHom 6 (fun k => μ * σ k) := by
    intro μ σ
    apply Units.ext
    rw [Units.val_mul, coe_diagHom, coe_diagHom, Matrix.GeneralLinearGroup.coe_scalar,
      Matrix.scalar_apply, Matrix.diagonal_mul_diagonal]
    rfl
  have hmono : ∀ t : Fin 6 → c.Kˣ, ∏ i, t i = 1 →
      ∃ t' : Fin 6 → c.Kˣ, (g : GL (Fin 6) c.K) * diagHom 6 t * (g : GL (Fin 6) c.K)⁻¹ =
        diagHom 6 t' := by
    intro t _
    obtain ⟨b, hb⟩ := c.exists_diag_eq (fun k => (t (0 : Fin 6))⁻¹ * t k) (by simp)
    have hb' : n * (b : G) * n⁻¹ ∈ Bs := (Subgroup.mem_normalizer_iff.mp hnN (b : G)).mp b.2
    obtain ⟨μ, hμ⟩ := key b hb'
    refine ⟨fun k => t (0 : Fin 6) * (μ * c.diag ⟨n * (b : G) * n⁻¹, hb'⟩ k), ?_⟩
    have ht : diagHom 6 t =
        Matrix.GeneralLinearGroup.scalar (Fin 6) (t (0 : Fin 6)) * diagHom 6 (c.diag b) := by
      rw [hscal, hb]
      congr 1
      funext k
      rw [mul_inv_cancel_left]
    rw [ht, ← hscal, ← hscal, ← hμ]
    have hc := TypeA.PGLTor.scalar_mul_comm (t (0 : Fin 6)) (g : GL (Fin 6) c.K)
    calc (g : GL (Fin 6) c.K) *
          (Matrix.GeneralLinearGroup.scalar (Fin 6) (t (0 : Fin 6)) * diagHom 6 (c.diag b)) *
          (g : GL (Fin 6) c.K)⁻¹
        = ((g : GL (Fin 6) c.K) * Matrix.GeneralLinearGroup.scalar (Fin 6) (t (0 : Fin 6))) *
            diagHom 6 (c.diag b) * (g : GL (Fin 6) c.K)⁻¹ := by group
      _ = _ := by rw [← hc]; group
  obtain ⟨τ, u, hgτ⟩ := ggQ2s08r6_exists_monomial c.hK hmono
  refine ⟨g, τ, u, hgr, hgτ, fun b hb => ?_⟩
  obtain ⟨μ, hμ⟩ := key b hb
  have hconj : (g : GL (Fin 6) c.K) * diagHom 6 (c.diag b) * (g : GL (Fin 6) c.K)⁻¹ =
      diagHom 6 (c.diag b ∘ ⇑τ.symm) := by
    rw [hgτ, mul_inv_rev, ← CFSG.RankThree.Classical2.permGL_mul_diagHom_mul_inv τ (c.diag b)]
    have hcomm : diagHom 6 u * diagHom 6 (c.diag b) * (diagHom 6 u)⁻¹ = diagHom 6 (c.diag b) := by
      rw [← map_inv, ← map_mul, ← map_mul, mul_comm u, mul_inv_cancel_right]
    calc CFSG.RankThree.Classical.permGL τ * diagHom 6 u * diagHom 6 (c.diag b) *
          ((diagHom 6 u)⁻¹ * (CFSG.RankThree.Classical.permGL τ)⁻¹)
        = CFSG.RankThree.Classical.permGL τ *
            (diagHom 6 u * diagHom 6 (c.diag b) * (diagHom 6 u)⁻¹) *
            (CFSG.RankThree.Classical.permGL τ)⁻¹ := by group
      _ = _ := by rw [hcomm]
  rw [hconj, hscal] at hμ
  have hfun := (CFSG.SectionRank.OddCover.diagHom_injective (n := 6) (K := c.K)) hμ
  refine ⟨μ⁻¹, fun k => ?_⟩
  have hk := congrFun hfun k
  simp only [Function.comp_apply] at hk
  rw [hk, inv_mul_cancel_left]


theorem exists_perm_of_mem_normalizer (c : GGQ2S08RoSix Bs L x) {n : G} (hnL : n ∈ L)
    (hnN : n ∈ Subgroup.normalizer (Bs : Set G)) :
    ∃ τ : Equiv.Perm (Fin 6), ∀ (b : Bs) (hb : n * (b : G) * n⁻¹ ∈ Bs),
      ∃ μ : c.Kˣ, ∀ k, c.diag ⟨n * (b : G) * n⁻¹, hb⟩ k = μ * c.diag b (τ.symm k) := by
  obtain ⟨-, τ, -, -, -, h⟩ := c.exists_monomial_of_mem_normalizer hnL hnN
  exact ⟨τ, h⟩

end GGQ2S08RoSix

end CFSG.StandardType

end
