module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylE6QTwoSixFrameAux2

public section

namespace CFSG.StandardType.E6QTwo

open CFSG.Assembly CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {K : Type} [Field K] [Finite K]

private theorem e6QTwoSixFrameAction_normalizer_eq {Bs L : Subgroup G}
    (hNL : Bs ≤ Subgroup.normalizer (L : Set G))
    (θ : L ⧸ Subgroup.center L ≃* LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1)))
    (b : Bs) :
    e6QTwoSixFrameAction (le_rfl : Subgroup.normalizer (L : Set G) ≤
        Subgroup.normalizer (L : Set G)) θ ⟨b, hNL b.2⟩ =
      e6QTwoSixFrameAction hNL θ b := by
  ext r
  obtain ⟨q, rfl⟩ := θ.surjective r
  obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective (s := Subgroup.center L) q
  rw [← QuotientGroup.mk'_apply (N := Subgroup.center L) l]
  rw [e6QTwoSixFrameAction_apply (le_rfl : Subgroup.normalizer (L : Set G) ≤
      Subgroup.normalizer (L : Set G)) θ ⟨b, hNL b.2⟩ l]
  rw [e6QTwoSixFrameAction_apply hNL θ b l]

private theorem e6QTwoSixXMemCentralizer {Bs L : Subgroup G} {x : G}
    (hx : x ∈ Bs)
    (hBL : Bs ⊓ Subgroup.centralizer (L : Set G) = Subgroup.zpowers x) :
    x ∈ Subgroup.centralizer (L : Set G) := by
  have hx' : x ∈ Bs ⊓ Subgroup.centralizer (L : Set G) := by
    rw [hBL]
    exact Subgroup.mem_zpowers x
  exact hx'.2

private theorem e6QTwoSixGamma_comm (hK : Nat.card K = 4) {Bs L : Subgroup G} {x g : G}
    (θ : L ⧸ Subgroup.center L ≃* LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1)))
    (hperf : commutator ↥L = ⊤) (hx : x ∈ Bs)
    (hBL : Bs ⊓ Subgroup.centralizer (L : Set G) = Subgroup.zpowers x)
    (hNL : Bs ≤ Subgroup.normalizer (L : Set G))
    (hgBs : g ∈ Subgroup.normalizer (Bs : Set G))
    (hgN : g ∈ Subgroup.normalizer (L : Set G))
    (hgB : ∀ y ∈ Bs, g * y * g⁻¹ * y⁻¹ ∈ Subgroup.zpowers x)
    (y : Bs) :
    e6QTwoSixFrameAction (le_rfl : Subgroup.normalizer (L : Set G) ≤
        Subgroup.normalizer (L : Set G)) θ ⟨g, hgN⟩ *
      e6QTwoSixFrameAction hNL θ y =
    e6QTwoSixFrameAction hNL θ y *
      e6QTwoSixFrameAction (le_rfl : Subgroup.normalizer (L : Set G) ≤
        Subgroup.normalizer (L : Set G)) θ ⟨g, hgN⟩ := by
  let N := Subgroup.normalizer (L : Set G)
  let βN := e6QTwoSixFrameAction (le_rfl : N ≤ N) θ
  let β := e6QTwoSixFrameAction hNL θ
  have hxN : x ∈ N := Subgroup.centralizer_le_normalizer (L : Set G)
    (e6QTwoSixXMemCentralizer hx hBL)
  have hxβ : βN ⟨x, hxN⟩ = 1 := by
    rw [← MonoidHom.mem_ker, e6QTwoSixFrameAction_ker (le_rfl : N ≤ N) θ hperf]
    exact Subgroup.mem_subgroupOf.mpr
      ⟨hxN, e6QTwoSixXMemCentralizer hx hBL⟩
  have hgyBs : g * y * g⁻¹ ∈ Bs :=
    (Subgroup.mem_normalizer_iff.mp hgBs (y : G)).mp y.2
  have hgyN : g * y * g⁻¹ ∈ N := hNL hgyBs
  have hz_mem : g * y * g⁻¹ * y⁻¹ ∈ Subgroup.zpowers x := hgB y y.2
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hz_mem
  have hgy_eq : g * y * g⁻¹ = x ^ k * y := by
    conv_rhs => rw [hk]
    simp
  have hz_bs : x ^ k * y ∈ Bs := by
    refine Bs.mul_mem ?_ y.2
    exact Subgroup.zpowers_le.mpr hx
      (Subgroup.zpow_mem (K := Subgroup.zpowers x) (Subgroup.mem_zpowers x) k)
  have hβN_z : βN ⟨x ^ k * y, hNL hz_bs⟩ = βN ⟨y, hNL y.2⟩ := by
    have hxpow : βN ⟨x ^ k * y, hNL hz_bs⟩ =
        βN ⟨x, hxN⟩ ^ k * βN ⟨y, hNL y.2⟩ := by
      have h1 : (⟨x ^ k * y, hNL hz_bs⟩ : N) = ⟨x, hxN⟩ ^ k * ⟨y, hNL y.2⟩ := by
        apply Subtype.ext
        simp only [Subgroup.coe_mul, Subgroup.coe_zpow]
      rw [h1, map_mul, map_zpow]
    simpa [hxpow, hxβ]
  have hconj : βN ⟨g, hgN⟩ * βN ⟨y, hNL y.2⟩ * (βN ⟨g, hgN⟩)⁻¹ =
      βN ⟨g * y * g⁻¹, hgyN⟩ := by
    have h1 : (⟨g * y * g⁻¹, hgyN⟩ : N) =
        ⟨g, hgN⟩ * ⟨y, hNL y.2⟩ * ⟨g, hgN⟩⁻¹ := by
      apply Subtype.ext
      rw [Subgroup.coe_mul, Subgroup.coe_inv]
      rfl
    rw [h1]
    simp only [map_mul, map_inv]
  have hβ_gy : βN ⟨g * y * g⁻¹, hgyN⟩ = βN ⟨y, hNL y.2⟩ := by
    rw [show (⟨g * y * g⁻¹, hgyN⟩ : N) = ⟨x ^ k * y, hNL hz_bs⟩ from by
      apply Subtype.ext
      exact hgy_eq]
    exact hβN_z
  have hconv : βN ⟨y, hNL y.2⟩ = e6QTwoSixFrameAction hNL θ y :=
    e6QTwoSixFrameAction_normalizer_eq hNL θ y
  have hγ : e6QTwoSixFrameAction (le_rfl : N ≤ N) θ ⟨g, hgN⟩ =
      βN ⟨g, hgN⟩ := rfl
  rw [hγ, ← hconv]
  calc βN ⟨g, hgN⟩ * βN ⟨y, hNL y.2⟩
      = (βN ⟨g, hgN⟩ * βN ⟨y, hNL y.2⟩ * (βN ⟨g, hgN⟩)⁻¹) * βN ⟨g, hgN⟩ := by group
    _ = βN ⟨g * y * g⁻¹, hgyN⟩ * βN ⟨g, hgN⟩ := by rw [hconj]
    _ = βN ⟨y, hNL y.2⟩ * βN ⟨g, hgN⟩ := by rw [hβ_gy]
private noncomputable def frameChange (hK : Nat.card K = 4) (Q : GL (Fin 6) K)
    (hQ : Q ∈ primeFormUnitary (USixTwo.fieldDataFour hK)
      (RankThree.PartOne.KCUnitaryModel.idGram K 6)) :
    LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1)) ≃*
      LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1)) :=
  TableBUE.conjProj (USixTwo.fieldDataFour hK) Q hQ

private theorem frameChange_mk (hK : Nat.card K = 4) (Q : GL (Fin 6) K)
    (hQ : Q ∈ primeFormUnitary (USixTwo.fieldDataFour hK)
      (RankThree.PartOne.KCUnitaryModel.idGram K 6))
    (x : ↥(ClassicalGroups.UnitaryFlag.unitarySU 2 1 K 6)) :
    frameChange hK Q hQ (InndiagSU.projU 1 6 K x) =
      InndiagSU.projU 1 6 K (TableBUE.conjSU (USixTwo.fieldDataFour hK) Q hQ x) :=
  TableBUE.conjProj_mk (USixTwo.fieldDataFour hK) Q hQ x

private theorem frameMk_one_eq (hK : Nat.card K = 4) :
    InndiagSU.frameMk (USixTwo.fieldDataFour hK) (1 : GL (Fin 6) K)
      (Subgroup.one_mem _) = InndiagSU.projU 1 6 K := by
  ext u
  rw [InndiagSU.frameMk_apply]
  congr 1
  apply (TableBUE.conjSU (USixTwo.fieldDataFour hK) (1 : GL (Fin 6) K)
    (Subgroup.one_mem _)).injective
  rw [MulEquiv.apply_symm_apply]
  apply Subtype.ext
  rw [TableBUE.coe_conjSU]
  simp

private theorem conjProj_symm_projU (hK : Nat.card K = 4) (Q : GL (Fin 6) K)
    (hQ : Q ∈ primeFormUnitary (USixTwo.fieldDataFour hK)
      (RankThree.PartOne.KCUnitaryModel.idGram K 6))
    (u : ↥(ClassicalGroups.UnitaryFlag.unitarySU 2 1 K 6)) :
    (frameChange hK Q hQ).symm (InndiagSU.projU 1 6 K u) =
      InndiagSU.frameMk (USixTwo.fieldDataFour hK) Q hQ u := by
  apply (frameChange hK Q hQ).injective
  rw [MulEquiv.apply_symm_apply, InndiagSU.frameMk_apply, frameChange_mk,
    MulEquiv.apply_symm_apply]

private theorem frameAct_conjProj (hK : Nat.card K = 4) (Q : GL (Fin 6) K)
    (hQ : Q ∈ primeFormUnitary (USixTwo.fieldDataFour hK)
      (RankThree.PartOne.KCUnitaryModel.idGram K 6))
    {e : MulAut (LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1)))}
    {σ : Fin 6 → Kˣ}
    (hfr : TableBUD.FrameAct (USixTwo.fieldDataFour hK) Q hQ e σ) :
    TableBUD.FrameAct (USixTwo.fieldDataFour hK) (1 : GL (Fin 6) K) (Subgroup.one_mem _)
      ((MulAut.congr (frameChange hK Q hQ)) e) σ := by
  intro u v huv
  rw [frameMk_one_eq hK]
  change (frameChange hK Q hQ)
      (e ((frameChange hK Q hQ).symm (InndiagSU.projU 1 6 K u))) =
    InndiagSU.projU 1 6 K v
  rw [conjProj_symm_projU hK Q hQ u]
  rw [hfr.apply u v huv]
  rw [← conjProj_symm_projU hK Q hQ v]
  rw [MulEquiv.apply_symm_apply]

theorem e6QTwoSixGamma3 (hK : Nat.card K = 4) {Bs L : Subgroup G} {x : G}
    (θ : L ⧸ Subgroup.center L ≃* LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1)))
    (hperf : commutator ↥L = ⊤) (hBs : IsElemAbelian 3 Bs) (hcard : Nat.card Bs = 3 ^ 6)
    (hx : x ∈ Bs)
    (hBL : Bs ⊓ Subgroup.centralizer (L : Set G) = Subgroup.zpowers x)
    (hNL : Bs ≤ Subgroup.normalizer (L : Set G))
    (hI : ∀ b ∈ Bs, ∃ ψ ∈ LargeEvenMatConjImage
        (LargeEvenProjMk (LargeEvenSUGroup (Fin 6) K (2 ^ 1))) (LargeEvenGUSet (Fin 6) K (2 ^ 1)),
      LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) ψ)
    {g : G} (hgN : g ∈ Subgroup.normalizer (L : Set G))
    (hgBs : g ∈ Subgroup.normalizer (Bs : Set G))
    (hgB : ∀ y ∈ Bs, g * y * g⁻¹ * y⁻¹ ∈ Subgroup.zpowers x) :
    (e6QTwoSixFrameAction (le_rfl : Subgroup.normalizer (L : Set G) ≤
        Subgroup.normalizer (L : Set G)) θ ⟨g, hgN⟩) ^ 3 = 1 := by
  classical
  let N := Subgroup.normalizer (L : Set G)
  let βN := e6QTwoSixFrameAction (le_rfl : N ≤ N) θ
  let γ := βN ⟨g, hgN⟩
  obtain ⟨-, -, Q, hQ, hfull⟩ :=
    e6QTwoSixFrameFullDiagonal hK θ hperf hBs hcard hx hBL hNL hI
  have hconj_mem : ∀ σ : e6QTwoTorParamSubgroup (K := K),
      ∃ b : Bs, MulAut.conj ((e6QTwoFrameTorusHom hK Q hQ) σ) =
        e6QTwoSixFrameAction hNL θ b := by
    intro σ
    have hσ3 : ∀ k, σ.1 k ^ 3 = 1 := fun k => USixTwo.cube_unit_eq_one hK (σ.1 k)
    let c : Kˣ := (σ.1 (0 : Fin 6))⁻¹
    have hc3 : c ^ 3 = 1 := USixTwo.cube_unit_eq_one hK c
    let τ : Fin 6 → Kˣ := fun k => c * σ.1 k
    have hτ0 : τ (0 : Fin 6) = 1 := by
      show c * σ.1 0 = 1
      exact inv_mul_cancel _
    have hτ3 : ∀ k, τ k ^ 3 = 1 := by
      intro k
      rw [show τ k = c * σ.1 k from rfl, mul_pow, hc3, hσ3 k, one_mul]
    have hτn : ∀ k, ((τ k : Kˣ) : K) ^ (2 ^ 1 + 1) = 1 := by
      intro k
      rw [show 2 ^ 1 + 1 = 3 by norm_num, ← Units.val_pow_eq_pow_val, hτ3 k, Units.val_one]
    obtain ⟨b, hb⟩ := hfull τ hτ0 hτ3
    have hfr : TableBUD.FrameAct (USixTwo.fieldDataFour hK) Q hQ
        (MulAut.conj (e6QTwoFrameTorusHom hK Q hQ σ)) τ :=
      TableBUD.FrameAct.smul (e6QTwoFrameActFrameTorusHom hK Q hQ σ) c
    have hEq : e6QTwoSixFrameAction hNL θ b =
        MulAut.conj (e6QTwoFrameTorusHom hK Q hQ σ) :=
      TableBUD.FrameAct.unique (h := USixTwo.fieldDataFour hK) (Q := Q) (hQ := hQ)
        (hσ := hτn) hb hfr
    exact ⟨b, hEq.symm⟩
  have hfix_frame : ∀ σ : e6QTwoTorParamSubgroup (K := K),
      γ ((e6QTwoFrameTorusHom hK Q hQ) σ) = (e6QTwoFrameTorusHom hK Q hQ) σ := by
    intro σ
    obtain ⟨b, hb⟩ := hconj_mem σ
    have hcomm := e6QTwoSixGamma_comm hK θ hperf hx hBL hNL hgBs hgN hgB b
    have hconj_eq : MulAut.conj (γ ((e6QTwoFrameTorusHom hK Q hQ) σ)) =
        MulAut.conj ((e6QTwoFrameTorusHom hK Q hQ) σ) := by
      rw [e6QTwoMulAutConjCongr γ ((e6QTwoFrameTorusHom hK Q hQ) σ), hb]
      ext x
      rw [MulAut.congr_apply]
      simp only [MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
      calc (e6QTwoSixFrameAction (le_rfl : N ≤ N) θ ⟨g, hgN⟩)
            ((e6QTwoSixFrameAction hNL θ b)
              ((e6QTwoSixFrameAction (le_rfl : N ≤ N) θ ⟨g, hgN⟩).symm x)) =
          ((e6QTwoSixFrameAction (le_rfl : N ≤ N) θ ⟨g, hgN⟩) *
            (e6QTwoSixFrameAction hNL θ b))
              ((e6QTwoSixFrameAction (le_rfl : N ≤ N) θ ⟨g, hgN⟩).symm x) := rfl
        _ = ((e6QTwoSixFrameAction hNL θ b) *
            (e6QTwoSixFrameAction (le_rfl : N ≤ N) θ ⟨g, hgN⟩))
            ((e6QTwoSixFrameAction (le_rfl : N ≤ N) θ ⟨g, hgN⟩).symm x) := by rw [hcomm]
        _ = (e6QTwoSixFrameAction hNL θ b) x := by simp
    exact CFSG.StandardType.mulAut_conj_injective
      (TableBUE.center_proj_eq_bot (by rw [hK]; norm_num) (by norm_num : 3 ≤ 6)
        (by norm_num : (6, 2 ^ 1) ≠ (3, 2))) hconj_eq
  let c := frameChange hK Q hQ
  have hmap_le : (e6QTwoFrameTorusHom hK Q hQ).range.map c.toMonoidHom ≤
      USixTwo.torU K := by
    rintro _ ⟨r, hr, rfl⟩
    obtain ⟨σ, rfl⟩ := hr
    have hfrQ : TableBUD.FrameAct (USixTwo.fieldDataFour hK) Q hQ
        (MulAut.conj (e6QTwoFrameTorusHom hK Q hQ σ)) σ.1 :=
      e6QTwoFrameActFrameTorusHom hK Q hQ σ
    have hσn : ∀ k, ((σ.1 k : Kˣ) : K) ^ (2 ^ 1 + 1) = 1 := by
      intro k
      rw [show 2 ^ 1 + 1 = 3 by norm_num, ← Units.val_pow_eq_pow_val,
        USixTwo.cube_unit_eq_one hK, Units.val_one]
    have hfr1 : TableBUD.FrameAct (USixTwo.fieldDataFour hK) (1 : GL (Fin 6) K)
        (Subgroup.one_mem _) ((MulAut.congr c) (MulAut.conj
          (e6QTwoFrameTorusHom hK Q hQ σ))) σ.1 :=
      frameAct_conjProj hK Q hQ hfrQ
    have hconj_eq : MulAut.conj (c (e6QTwoFrameTorusHom hK Q hQ σ)) =
        (MulAut.congr c) (MulAut.conj (e6QTwoFrameTorusHom hK Q hQ σ)) :=
      (e6QTwoMulAutConjCongr c _)
    rw [← hconj_eq] at hfr1
    obtain ⟨u, hu⟩ := InndiagSU.projU_surjective (n := 1) (d := 6) (K := K)
      (c (e6QTwoFrameTorusHom hK Q hQ σ))
    have hinner : InndiagSU.IsSemilin
        (InndiagSU.frameMk (USixTwo.fieldDataFour hK) (1 : GL (Fin 6) K) (Subgroup.one_mem _))
        (MulAut.conj (c (e6QTwoFrameTorusHom hK Q hQ σ))) u 1 := by
      intro a b hab
      rw [frameMk_one_eq hK]
      rw [MulAut.conj_apply, ← hu, ← map_mul, ← map_inv, ← map_mul]
      exact congrArg (InndiagSU.projU 1 6 K) (Subtype.ext hab.symm)
    have hσu : SectionRank.OddCover.diagHom 6 σ.1 ∈
        primeFormUnitary (USixTwo.fieldDataFour hK)
          (RankThree.PartOne.KCUnitaryModel.idGram K 6) :=
      TableBUD.diagHom_mem_primeFormUnitary (USixTwo.fieldDataFour hK) hσn
    have hxu : (u : GL (Fin 6) K) ∈ primeFormUnitary (USixTwo.fieldDataFour hK)
        (RankThree.PartOne.KCUnitaryModel.idGram K 6) :=
      TableBUE.unitarySU_le_primeFormUnitary (USixTwo.fieldDataFour hK) u.2
    have hK' : Nat.card K = (2 ^ 1) ^ 2 := by rw [hK]; norm_num
    obtain ⟨cc, hcc⟩ := TableBUD.IsSemilin.eq_smul
      (h := USixTwo.fieldDataFour hK) hK' (by norm_num : 3 ≤ 6)
      (by norm_num : (6, 2 ^ 1) ≠ (3, 2)) (by norm_num : Nat.Prime 3)
      (by norm_num : 3 ∣ 2 ^ 1 + 1) (Q := (1 : GL (Fin 6) K)) (Subgroup.one_mem _) hxu hσu
      hinner hfr1
    have hconst : SectionRank.OddCover.diagHom 6 (fun _ : Fin 6 => cc) =
        Matrix.GeneralLinearGroup.scalar (Fin 6) cc := by
      apply Units.ext
      rw [SectionRank.OddCover.coe_diagHom, Matrix.GeneralLinearGroup.coe_scalar,
        Matrix.scalar_apply]
    have hdiagmul : SectionRank.OddCover.diagHom 6 (fun k => cc * σ.1 k) =
        Matrix.GeneralLinearGroup.scalar (Fin 6) cc *
          SectionRank.OddCover.diagHom 6 σ.1 := by
      rw [show (fun k => cc * σ.1 k) = (fun _ : Fin 6 => cc) * σ.1 from rfl,
        map_mul, hconst]
    let u' : ↥(LargeEvenSUGroup (Fin 6) K (2 ^ 1)) := ⟨(u : GL (Fin 6) K), u.2⟩
    have hu_torSU : u' ∈ USixTwo.torSU K := by
      rw [USixTwo.torSU, Subgroup.mem_comap]
      refine TauCeti.mem_diagonalTorus_iff.mpr ?_
      have hmat : ((u' : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) =
          Matrix.diagonal (fun k => ((cc * σ.1 k : Kˣ) : K)) := by
        rw [show ((u' : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) =
            ((Matrix.GeneralLinearGroup.scalar (Fin 6) cc *
              SectionRank.OddCover.diagHom 6 σ.1 : GL (Fin 6) K) :
              Matrix (Fin 6) (Fin 6) K) from by rw [hcc]]
        rw [← congrArg (fun g : GL (Fin 6) K => (g : Matrix (Fin 6) (Fin 6) K)) hdiagmul,
          SectionRank.OddCover.coe_diagHom]
      change ((u' : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K).IsDiag
      rw [hmat]
      exact Matrix.isDiag_diagonal _
    have hproj : InndiagSU.projU 1 6 K u ∈ USixTwo.torU K := by
      rw [USixTwo.torU]
      exact Subgroup.mem_map.mpr ⟨u', hu_torSU, rfl⟩
    change c ((e6QTwoFrameTorusHom hK Q hQ) σ) ∈ USixTwo.torU K
    rw [← hu]
    exact hproj
  have hmap_eq : (e6QTwoFrameTorusHom hK Q hQ).range.map c.toMonoidHom = USixTwo.torU K := by
    refine Subgroup.eq_of_le_of_card_ge hmap_le ?_
    have hcard : Nat.card ↥((e6QTwoFrameTorusHom hK Q hQ).range.map c.toMonoidHom) =
        Nat.card ↥(e6QTwoFrameTorusHom hK Q hQ).range :=
      Subgroup.card_map_of_injective (f := c.toMonoidHom) c.injective
    rw [hcard, e6QTwoCardRangeFrameTorusHom hK Q hQ, USixTwo.card_torU hK]
  have hfix_torU : ∀ u ∈ USixTwo.torU K,
      ((MulAut.congr c) γ) u = u := by
    intro u hu
    have hmem : u ∈ (e6QTwoFrameTorusHom hK Q hQ).range.map c.toMonoidHom := by
      rw [hmap_eq]; exact hu
    obtain ⟨r, hr, hcr⟩ := Subgroup.mem_map.mp hmem
    obtain ⟨σ, rfl⟩ := hr
    have hγr : γ ((e6QTwoFrameTorusHom hK Q hQ) σ) = (e6QTwoFrameTorusHom hK Q hQ) σ :=
      hfix_frame σ
    rw [← hcr]
    change ((MulAut.congr c) γ) (c ((e6QTwoFrameTorusHom hK Q hQ) σ)) =
      c ((e6QTwoFrameTorusHom hK Q hQ) σ)
    rw [e6QTwoMulAutCongrApply c γ ((e6QTwoFrameTorusHom hK Q hQ) σ), hγr]
  have h3 := USixTwo.pow_three_eq_one_of_forall_fix_torU hK ((MulAut.congr c) γ) hfix_torU
  have hmap_pow : ((MulAut.congr c) γ) ^ 3 = (MulAut.congr c) (γ ^ 3) :=
    (map_pow (MulAut.congr c).toMonoidHom γ 3).symm
  rw [hmap_pow] at h3
  exact (MulAut.congr c).injective (by rw [h3, map_one])

end CFSG.StandardType.E6QTwo

end
