module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermOmKFrameDefs
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyAut
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentySpCoord
public import CFSG.ClassicalGroups.Orthogonal.UnitaryOmega.Blocks
public import Mathlib.GroupTheory.Perm.ViaEmbedding
import CFSG.Permutation.Embedding
public import CFSG.ClassicalGroups.Orthogonal.RootGroupNormalizer
public import CFSG.HardMathSupport.Dickson.Bal207.OrthD4Loc
public import CFSG.Holt.Fixed
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S172CCentLayer
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10FBaseIso
public import CFSG.LocalAnalysis.GLTheoremA.S10.Lemma106107
public import CFSG.LocalAnalysis.GLTheoremA.Sec5Setup
public import CFSG.RankThree.PartOne.FOC.CompCommutator
public import CFSG.RankThree.PartOne.KC.OrthogonalAnchoredGeneration
public import CFSG.RankThree.PartOne.S15K.FixedWitt
public import CFSG.RankThree.PartOne.S15K.LayerModel

public section

namespace CFSG.StandardType

open CFSG.ClassicalGroups.Orthogonal.UnitaryOmega CFSG.ClassicalInvolution.Models.OrthogonalPairs
open CFSG.LieType.BorelTits

section Recalibration

variable {F K : Type} [Field F] [Field K] [Algebra F K] [Finite K] [CharP K 2] {f p : ℕ}
  {E : QuadExt F K (unitaryInvolution K 2 f)} {G : Type} [Group G] {Bs X : Subgroup G} {n m : ℕ}
  {eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p))} {π : Fin (m + 1) ≃ Fin n}
  {κ : normOmega E m →* G} {χ : Multiplicative (ZMod p) →* Kˣ}

theorem GGSecFiveBPermOmKFrame.comp_normOmegaConj
    (hframe : GGSecFiveBPermOmKFrame E Bs X eta π κ χ)
    {g : ((F × F) × (Fin m → K)) ≃ₗ[F] ((F × F) × (Fin m → K))}
    (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup (normHypForm E m))
    (hgT : ∀ (a : Fin m → Multiplicative (ZMod p)) (v : (F × F) × (Fin m → K)),
      g (v.1, fun i => (χ (a i) : K) * v.2 i) = ((g v).1, fun i => (χ (a i) : K) * (g v).2 i)) :
    GGSecFiveBPermOmKFrame E Bs X eta π (κ.comp (normOmegaConj E hg).toMonoidHom) χ := by
  obtain ⟨hinj, hrange, hχ, hact⟩ := hframe
  refine ⟨hinj.comp (normOmegaConj E hg).injective, ?_, hχ, fun b => ?_⟩
  · rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr (MulEquiv.surjective _),
      ← MonoidHom.range_eq_map, hrange]
  obtain ⟨T, hT, hbT⟩ := hact b
  have hcomm : g * (T : ((F × F) × (Fin m → K)) ≃ₗ[F] ((F × F) × (Fin m → K))) =
      (T : ((F × F) × (Fin m → K)) ≃ₗ[F] ((F × F) × (Fin m → K))) * g := by
    apply LinearEquiv.ext
    intro v
    rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, hT v,
      hgT (fun i => eta b (π i.castSucc)) v, hT (g v)]
  have hTfix : normOmegaConj E hg T = T := by
    apply Subtype.ext
    rw [normOmegaConj_apply, hcomm, mul_assoc, mul_inv_cancel, mul_one]
  refine ⟨T, hT, fun s => ?_⟩
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
  rw [hbT (normOmegaConj E hg s)]
  congr 1
  calc T * normOmegaConj E hg s * T⁻¹
      = normOmegaConj E hg T * normOmegaConj E hg s * (normOmegaConj E hg T)⁻¹ := by
          rw [hTfix]
    _ = normOmegaConj E hg (T * s * T⁻¹) := by
          simp only [map_mul, map_inv]

theorem GGSecFiveBPermOmKFrame.conj_transporter
    (hframe : GGSecFiveBPermOmKFrame E Bs X eta π κ χ) {g : G}
    (hg : g ∈ Subgroup.normalizer (Bs : Set G)) {τ : Equiv.Perm (Fin n)}
    (hτ : MulAut.congr eta (ggConjAut Bs hg) = SpCoord.permAut τ) :
    GGSecFiveBPermOmKFrame E Bs (X.map (MulAut.conj g).toMonoidHom) eta (π.trans τ)
      ((MulAut.conj g).toMonoidHom.comp κ) χ := by
  obtain ⟨hinj, hrange, hχ, hT⟩ := hframe
  refine ⟨(MulAut.conj g).injective.comp hinj, ?_, hχ, fun b => ?_⟩
  · rw [MonoidHom.range_comp, hrange]
  ·
    let b' : ↥Bs := (ggConjAut Bs hg).symm b
    have hb' : ((b' : ↥Bs) : G) = g⁻¹ * b * g := rfl
    have hcoord : ∀ c, eta b' c = eta b (τ c) := by
      intro c
      have h := congrArg (fun φ : MulAut (Fin n → Multiplicative (ZMod p)) => φ (eta b')) hτ
      have hb : ggConjAut Bs hg b' = b := MulEquiv.apply_symm_apply _ b
      simp only [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply, hb] at h
      have h' := congrFun h (τ c)
      rw [SpCoord.permAut_apply] at h'
      simpa using h'.symm
    obtain ⟨T, hTv, hTc⟩ := hT b'
    refine ⟨T, fun v => ?_, fun s => ?_⟩
    · rw [hTv v]
      simp only [Equiv.trans_apply, hcoord]
    · have h := hTc s
      rw [hb'] at h
      simp only [MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom, Function.comp_apply,
        MulAut.conj_apply]
      rw [← h]
      group

end Recalibration

private theorem oaJ_castRestr_planeDiag {F K : Type} [Monoid K] {p : ℕ} {r r' : ℕ}
    (h : r ≤ r') (χ : Multiplicative (ZMod p) →* Kˣ)
    (a : Fin r' → Multiplicative (ZMod p)) (v : (F × F) × (Fin r' → K)) :
    castRestr h (v.1, fun i => (χ (a i) : K) * v.2 i) =
      ((castRestr h v).1,
        fun i => (χ (a (Fin.castLE h i)) : K) * (castRestr h v).2 i) := rfl

section Cast

variable {F K : Type} [Field F] [Field K] [Algebra F K] [Finite K] [CharP K 2] {f p : ℕ}
  (E : QuadExt F K (unitaryInvolution K 2 f))

theorem normOmegaCast_normPlaneTorus {r r' : ℕ} (h : r ≤ r') (hr : 2 ≤ r) (hr' : 2 ≤ r')
    (hpq : p ∣ 2 ^ f + 1) (χ : Multiplicative (ZMod p) →* Kˣ)
    (u : Fin r → Multiplicative (ZMod p)) :
    normOmegaCast E h (normPlaneTorus E hr hpq χ u) =
      normPlaneTorus E hr' hpq χ (fun j => if hj : (j : ℕ) < r then u ⟨j, hj⟩ else 1) := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro v
  simp only [normOmegaCast_apply, castEquiv_apply, castLin_apply,
    LinearEquiv.coe_toLinearMap]
  rw [normPlaneTorus_apply E hr hpq χ u,
    normPlaneTorus_apply E hr' hpq χ
      (fun j => if hj : (j : ℕ) < r then u ⟨j, hj⟩ else 1)]
  refine Prod.ext rfl (funext fun j => ?_)
  dsimp only
  by_cases hj : (j : ℕ) < r
  · simp only [dif_pos hj]
    rfl
  · simp only [dif_neg hj]
    rw [map_one, Units.val_one, one_mul]

theorem castEquiv_planeDiag_comm {r r' : ℕ} (h : r ≤ r') (χ : Multiplicative (ZMod p) →* Kˣ)
    {g : ((F × F) × (Fin r → K)) ≃ₗ[F] ((F × F) × (Fin r → K))}
    (hg : ∀ (a : Fin r → Multiplicative (ZMod p)) (v : (F × F) × (Fin r → K)),
      g (v.1, fun i => (χ (a i) : K) * v.2 i) = ((g v).1, fun i => (χ (a i) : K) * (g v).2 i))
    (a : Fin r' → Multiplicative (ZMod p)) (v : (F × F) × (Fin r' → K)) :
    castEquiv h g (v.1, fun i => (χ (a i) : K) * v.2 i) =
      ((castEquiv h g v).1, fun i => (χ (a i) : K) * (castEquiv h g v).2 i) := by
  have hg' := hg (fun i => a (Fin.castLE h i)) (castRestr h v)
  simp only [castEquiv_apply, castLin_apply, LinearEquiv.coe_toLinearMap]
  refine Prod.ext ?_ (funext fun j => ?_)
  · dsimp only
    rw [oaJ_castRestr_planeDiag, hg']
  · dsimp only
    by_cases hj : (j : ℕ) < r
    · simp only [dif_pos hj]
      rw [oaJ_castRestr_planeDiag, hg']
      rfl
    · simp only [dif_neg hj]

theorem normOmegaConj_castEquiv_normOmegaCast {r r' : ℕ} (h : r ≤ r')
    {g : ((F × F) × (Fin r → K)) ≃ₗ[F] ((F × F) × (Fin r → K))}
    (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup (normHypForm E r)) (y : normOmega E r) :
    normOmegaConj E (castEquiv_mem_orthogonalGroup E h hg) (normOmegaCast E h y) =
      normOmegaCast E h (normOmegaConj E hg y) := by
  apply Subtype.ext
  rw [normOmegaConj_apply, normOmegaCast_apply, normOmegaCast_apply, normOmegaConj_apply]
  have hmul : castEquiv h (g * (y : ((F × F) × (Fin r → K)) ≃ₗ[F]
      ((F × F) × (Fin r → K))) * g⁻¹) =
      castEquiv h g * castEquiv h (y : ((F × F) × (Fin r → K)) ≃ₗ[F]
        ((F × F) × (Fin r → K))) * (castEquiv h g)⁻¹ := by
    change castHom h (g * (y : ((F × F) × (Fin r → K)) ≃ₗ[F]
        ((F × F) × (Fin r → K))) * g⁻¹) =
      castHom h g * castHom h (y : ((F × F) × (Fin r → K)) ≃ₗ[F]
        ((F × F) × (Fin r → K))) * (castHom h g)⁻¹
    simp only [map_mul, map_inv]
  rw [hmul]

end Cast

private theorem oaJ_finRotate_castSucc {n : ℕ} (i : Fin n) :
    finRotate (n + 1) (Fin.castSucc i) = Fin.succ i := by
  exact finRotate_of_lt (n := n) i.2

theorem viaEmbeddingHom_succEmb_eq_conj (n : ℕ) (σ : Equiv.Perm (Fin n)) :
    Equiv.Perm.viaEmbeddingHom (Fin.succEmb n) σ =
      finRotate (n + 1) * Equiv.Perm.viaEmbeddingHom (Fin.castSuccEmb : Fin n ↪ Fin (n + 1)) σ *
        (finRotate (n + 1))⁻¹ := by
  have h0 : (0 : Fin (n + 1)) ∉ Set.range (Fin.succEmb n) := by
    rintro ⟨i, hi⟩
    rw [Fin.coe_succEmb] at hi
    exact Fin.succ_ne_zero i hi
  have hlast : Fin.last n ∉ Set.range (Fin.castSuccEmb : Fin n ↪ Fin (n + 1)) := by
    rintro ⟨i, hi⟩
    rw [Fin.coe_castSuccEmb] at hi
    exact Fin.castSucc_ne_last i hi
  have hsymm0 : (finRotate (n + 1)).symm 0 = Fin.last n := by
    rw [Equiv.symm_apply_eq]
    simp
  have hsymm : ∀ i : Fin n,
      (finRotate (n + 1)).symm (Fin.succ i) = Fin.castSucc i := by
    intro i
    rw [Equiv.symm_apply_eq]
    exact (oaJ_finRotate_castSucc i).symm
  have hviaS : Equiv.Perm.viaEmbeddingHom (Fin.succEmb n) σ =
      σ.viaEmbedding (Fin.succEmb n) := rfl
  have hviaC : Equiv.Perm.viaEmbeddingHom (Fin.castSuccEmb : Fin n ↪ Fin (n + 1)) σ =
      σ.viaEmbedding (Fin.castSuccEmb : Fin n ↪ Fin (n + 1)) := rfl
  have hL : ∀ i : Fin n, (σ.viaEmbedding (Fin.succEmb n)) (Fin.succ i) = Fin.succ (σ i) := by
    intro i
    have h := Equiv.Perm.viaEmbedding_apply σ (Fin.succEmb n) i
    simpa [Fin.coe_succEmb] using h
  have hC : ∀ i : Fin n,
      (σ.viaEmbedding (Fin.castSuccEmb : Fin n ↪ Fin (n + 1))) (Fin.castSucc i) =
        Fin.castSucc (σ i) := by
    intro i
    have h := Equiv.Perm.viaEmbedding_apply σ (Fin.castSuccEmb : Fin n ↪ Fin (n + 1)) i
    simpa [Fin.coe_castSuccEmb] using h
  ext x
  rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, Equiv.Perm.inv_def, hviaS, hviaC]
  refine Fin.cases ?_ ?_ x
  · rw [Equiv.Perm.viaEmbedding_apply_of_notMem σ (Fin.succEmb n) 0 h0, hsymm0,
      Equiv.Perm.viaEmbedding_apply_of_notMem σ (Fin.castSuccEmb : Fin n ↪ Fin (n + 1))
        (Fin.last n) hlast]
    have hfr : finRotate (n + 1) (Fin.last n) = (0 : Fin (n + 1)) := by
      simpa [Fin.last] using (finRotate_last' (n := n))
    rw [hfr]
  · intro i
    rw [hL i, hsymm i, hC i, oaJ_finRotate_castSucc]

theorem viaEmbeddingHom_trans_equiv {α β γ : Type*} (ι : α ↪ β) (e : β ≃ γ)
    (σ : Equiv.Perm α) :
    Equiv.Perm.viaEmbeddingHom (ι.trans e.toEmbedding) σ =
      e.permCongr (Equiv.Perm.viaEmbeddingHom ι σ) :=
  CFSG.Permutation.viaEmbeddingHom_trans_equiv ι e σ

theorem castSuccEmb_trans_finRotate (n : ℕ) :
    (Fin.castSuccEmb : Fin n ↪ Fin (n + 1)).trans (finRotate (n + 1)).toEmbedding =
      Fin.succEmb n := by
  refine Function.Embedding.ext fun i => ?_
  rw [Function.Embedding.trans_apply, Equiv.coe_toEmbedding, Fin.coe_castSuccEmb,
    Fin.coe_succEmb]
  exact oaJ_finRotate_castSucc i

theorem viaEmbeddingHom_castSuccEmb_finRotate_trans {γ : Type*} (n : ℕ) (π : Fin (n + 1) ≃ γ)
    (σ : Equiv.Perm (Fin n)) :
    Equiv.Perm.viaEmbeddingHom ((Fin.castSuccEmb : Fin n ↪ Fin (n + 1)).trans
      ((finRotate (n + 1)).trans π).toEmbedding) σ =
      π.permCongr (Equiv.Perm.viaEmbeddingHom (Fin.succEmb n) σ) := by
  rw [← viaEmbeddingHom_trans_equiv, ← castSuccEmb_trans_finRotate n, Equiv.trans_toEmbedding]
  rfl

end CFSG.StandardType

end
