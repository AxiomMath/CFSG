module

public import CFSG.RankThree.GF2n.Stroth80.HeringSec9RStmt
public import CFSG.RankThree.GF2n.Stroth80.HeringSec9Line
import CFSG.RankThree.GF2n.Stroth80.Sec715IrrALin
import CFSG.LinearAlgebra.SL2LineStabilizer

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open CFSG.Quasithin.G11.P3Ortho.Om4
open CFSG.Open.StatedAPI
open scoped commutatorElement Matrix

namespace HS9

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem sec97_factor_pair (h34 : Stroth34Statement) (h311a : Stroth311aStatement)
    (hc : Ctx M Q Z B) {n : ℕ} {t : G} (hs : Sec9Hyp hc n t)
    {X Y : Subgroup G} (hsplit : Split95 M Q Z B t X Y)
    {K : Type} [Field K] [Finite K] [CharP K 2] (hK : Nat.card K = Nat.card Z)
    (φ : ↥(Rt M (LB M Q B) t) →* GL (Fin 2 ⊕ Fin 2) K)
    (hrange : ((Ψ K).toMonoidHom.comp φ).range = (rho' K).range)
    (hker : φ.ker = (hc.CN t).subgroupOf (Rt M (LB M Q B) t)) :
    ((Y.subgroupOf (Rt M (LB M Q B) t)).map ((Ψ K).toMonoidHom.comp φ) = leftF K ∧
      (X.subgroupOf (Rt M (LB M Q B) t)).map ((Ψ K).toMonoidHom.comp φ) = rightF K) ∨
    ((Y.subgroupOf (Rt M (LB M Q B) t)).map ((Ψ K).toMonoidHom.comp φ) = rightF K ∧
      (X.subgroupOf (Rt M (LB M Q B) t)).map ((Ψ K).toMonoidHom.comp φ) = leftF K) := by
  classical
  have hs5 := hs.toSec5
  have ht : t ∈ LB M Q B := hs5.mem
  have hq4 : 4 ≤ Nat.card K := hK ▸ hc.hyp.q4
  have hhead := (sec97Head_of h34 h311a G M Q Z B hc n t hs X Y hsplit).1
  obtain ⟨⟨hQX, hXR, hQY, hYR, hXY, hXYQ, hcomm⟩, hYsl, -⟩ := hsplit
  have hq4Z : 4 ≤ Nat.card Z := hc.hyp.q4
  have hq2 : ∃ s : ℕ, Nat.card Z = 2 ^ s := by
    obtain ⟨e, -, he, -⟩ := hc.hyp.cp
    exact ⟨e, he⟩
  obtain ⟨hYQnorm, hYmod⟩ := hYsl
  obtain ⟨hYcard, -⟩ := HS9.isSLModel_two_data hq4Z hq2 hYmod
  have hQY_idx : Q.relIndex Y = Nat.card Z * (Nat.card Z ^ 2 - 1) := hYcard
  have hYX : Y ≤ Subgroup.normalizer (X : Set G) := HS9.normalizer_of_commutator_le hQX hcomm
  have hXY' : X ≤ Subgroup.normalizer (Y : Set G) :=
    HS9.normalizer_of_commutator_le (X := Y) (Y := X) hQY (fun a ha y hy => by
      have := Q.inv_mem (hcomm y hy a ha)
      rwa [commutatorElement_inv] at this)
  have hRX : Rt M (LB M Q B) t ≤ Subgroup.normalizer (X : Set G) :=
    calc Rt M (LB M Q B) t = X ⊔ Y := hXY.symm
      _ ≤ _ := sup_le Subgroup.le_normalizer hYX
  have hRY : Rt M (LB M Q B) t ≤ Subgroup.normalizer (Y : Set G) :=
    calc Rt M (LB M Q B) t = X ⊔ Y := hXY.symm
      _ ≤ _ := sup_le hXY' Subgroup.le_normalizer
  have hdec : ∀ r ∈ Rt M (LB M Q B) t, ∃ x ∈ X, ∃ y ∈ Y, x * y = r := by
    intro r hr
    have hr' : r ∈ (↑(X ⊔ Y) : Set G) := by rw [hXY]; exact hr
    rw [Subgroup.coe_mul_of_left_le_normalizer_right X Y hXY'] at hr'
    obtain ⟨x, hx, y, hy, hxy⟩ := Set.mem_mul.mp hr'
    exact ⟨x, hx, y, hy, hxy⟩
  let φ'' : ↥(Rt M (LB M Q B) t) →*
      (Matrix (Fin 2) (Fin 2) K ≃ₗ[K] Matrix (Fin 2) (Fin 2) K) := (Ψ K).toMonoidHom.comp φ
  have hφ''1 : ∀ s : ↥(Rt M (LB M Q B) t), φ'' s = 1 ↔ (s : G) ∈ hc.CN t := by
    intro s
    show Ψ K (φ s) = 1 ↔ _
    rw [MulEquiv.map_eq_one_iff, ← MonoidHom.mem_ker, hker, Subgroup.mem_subgroupOf]
  have hcardSL : Nat.card (Matrix.SpecialLinearGroup (Fin 2) K) =
      Nat.card K * (Nat.card K ^ 2 - 1) :=
    (card_statedSL 2 K).symm.trans (card_statedSL_two K)
  have hcardRange : Nat.card (rho' K).range =
      Nat.card K * (Nat.card K ^ 2 - 1) * (Nat.card K * (Nat.card K ^ 2 - 1)) := by
    rw [← Nat.card_congr (MonoidHom.ofInjective (rho'_injective (K := K))).toEquiv,
      Nat.card_prod, hcardSL]
  have hQY_idxK : Q.relIndex Y = Nat.card K * (Nat.card K ^ 2 - 1) := by
    rw [hQY_idx, hK]
  have hHYne : (Y.subgroupOf (Rt M (LB M Q B) t)).map φ'' ≠ ⊥ :=
    sec97_HY_ne_bot φ'' hYR hhead hXYQ hQY_idx hq4Z hφ''1
  have hcardHY : Nat.card ↥((Y.subgroupOf (Rt M (LB M Q B) t)).map φ'') ≤
      Nat.card K * (Nat.card K ^ 2 - 1) :=
    sec97_HY_card_le φ'' hYR (hc.Q_le_CN ht) hφ''1 hQY_idxK
  have hHXne : (X.subgroupOf (Rt M (LB M Q B) t)).map φ'' ≠ ⊥ :=
    sec97_HX_ne_bot φ'' hrange hdec hXR hYR hcardRange hcardHY hq4
  have hnc := sec97_normal_comm φ'' hrange hRX hRY (hc.Q_le_CN ht) hcomm hφ''1
  have hcls := eq_leftF_or_rightF hq4 hnc.2.1 hnc.1
    (hrange ▸ Subgroup.map_le_range φ'' (X.subgroupOf (Rt M (LB M Q B) t)))
    (hrange ▸ Subgroup.map_le_range φ'' (Y.subgroupOf (Rt M (LB M Q B) t)))
    hHXne hHYne hnc.2.2
  rcases hcls with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Or.inr ⟨h2, h1⟩
  · exact Or.inl ⟨h2, h1⟩

theorem sec97_line_data_of (h34 : Stroth34Statement) (h311a : Stroth311aStatement)
    (hc : Ctx M Q Z B) {n : ℕ} {t : G} (hs : Sec9Hyp hc n t)
    {X Y : Subgroup G} (hsplit : Split95 M Q Z B t X Y) {S : Subgroup G}
    (hS : S = X ∨ S = Y) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K 2)
      (_ : (Z.subgroupOf (Vt M (LB M Q B) B Z t)).Normal)
      (φ : ↥(Rt M (LB M Q B) t) →* GL (Fin 2 ⊕ Fin 2) K)
      (ψ : ↥(Vt M (LB M Q B) B Z t) ⧸ Z.subgroupOf (Vt M (LB M Q B) B Z t) ≃*
        Multiplicative (Fin 2 ⊕ Fin 2 → K))
      (u : Fin 2 ⊕ Fin 2 → K)
      (H : Subgroup (Matrix (Fin 2) (Fin 2) K ≃ₗ[K] Matrix (Fin 2) (Fin 2) K))
      (Φ : (Fin 2 → K) →ₗ[K] Matrix (Fin 2) (Fin 2) K) (w₀ : Fin 2 → K),
      Nat.card K = Nat.card Z ∧
      (∀ (s : ↥(Rt M (LB M Q B) t)) (v w : ↥(Vt M (LB M Q B) B Z t)),
        (w : G) = (s : G) * v * (s : G)⁻¹ →
        Multiplicative.toAdd (ψ (QuotientGroup.mk w)) =
          (φ s : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ
            Multiplicative.toAdd (ψ (QuotientGroup.mk v))) ∧
      Rt M (LB M Q B) t ≤ Subgroup.normalizer (Vt M (LB M Q B) B Z t : Set G) ∧
      (∀ x : Fin 2 ⊕ Fin 2 → K,
        (∃ b : ↥(Vt M (LB M Q B) B Z t), (b : G) ∈ B ∧ secVec ψ b = x) ↔
          ∃ c : K, x = c • u) ∧
      (∀ h, h ∈ H ↔ ∃ s : ↥(Rt M (LB M Q B) t), (s : G) ∈ S ∧ Ψ K (φ s) = h) ∧
      ActsNat H Φ ∧ w₀ ≠ 0 ∧ toMat K u = Φ w₀ ∧
      (H = leftF K ∨ H = rightF K) ∧ (toMat K u).det = 0 := by
  classical
  obtain ⟨K, fK, finK, chK, hn, φ, ψ, u, hK, hrange, hker, hnorm, hψ, hBiff, hW, hdet, hu0⟩ :=
    sec9_coord h34 hc hs
  haveI := hn
  haveI : CharP K 2 := chK
  let φ'' : ↥(Rt M (LB M Q B) t) →*
      (Matrix (Fin 2) (Fin 2) K ≃ₗ[K] Matrix (Fin 2) (Fin 2) K) := (Ψ K).toMonoidHom.comp φ
  have hfac := sec97_factor_pair h34 h311a hc hs hsplit hK φ hrange hker
  rcases hS with rfl | rfl
  · rcases hfac with ⟨-, hX⟩ | ⟨hY, hX⟩
    · obtain ⟨Φ, w₀, hA, hw₀, hu⟩ :=
        natural_module_data (H := rightF K) (Or.inr rfl) hdet hu0
      refine ⟨K, fK, finK, chK, hn, φ, ψ, u, rightF K, Φ, w₀, hK, hψ, hnorm, hBiff, ?_,
        hA, hw₀, hu, Or.inr rfl, hdet⟩
      intro h
      rw [← hX]
      simp only [Subgroup.mem_map, Subgroup.mem_subgroupOf]
      exact Iff.rfl
    · obtain ⟨Φ, w₀, hA, hw₀, hu⟩ :=
        natural_module_data (H := leftF K) (Or.inl rfl) hdet hu0
      refine ⟨K, fK, finK, chK, hn, φ, ψ, u, leftF K, Φ, w₀, hK, hψ, hnorm, hBiff, ?_,
        hA, hw₀, hu, Or.inl rfl, hdet⟩
      intro h
      rw [← hX]
      simp only [Subgroup.mem_map, Subgroup.mem_subgroupOf]
      exact Iff.rfl
  · rcases hfac with ⟨hY, -⟩ | ⟨hY, -⟩
    · obtain ⟨Φ, w₀, hA, hw₀, hu⟩ :=
        natural_module_data (H := leftF K) (Or.inl rfl) hdet hu0
      refine ⟨K, fK, finK, chK, hn, φ, ψ, u, leftF K, Φ, w₀, hK, hψ, hnorm, hBiff, ?_,
        hA, hw₀, hu, Or.inl rfl, hdet⟩
      intro h
      rw [← hY]
      simp only [Subgroup.mem_map, Subgroup.mem_subgroupOf]
      exact Iff.rfl
    · obtain ⟨Φ, w₀, hA, hw₀, hu⟩ :=
        natural_module_data (H := rightF K) (Or.inr rfl) hdet hu0
      refine ⟨K, fK, finK, chK, hn, φ, ψ, u, rightF K, Φ, w₀, hK, hψ, hnorm, hBiff, ?_,
        hA, hw₀, hu, Or.inr rfl, hdet⟩
      intro h
      rw [← hY]
      simp only [Subgroup.mem_map, Subgroup.mem_subgroupOf]
      exact Iff.rfl

theorem ulineX_data (h34 : Stroth34Statement) (h311a : Stroth311aStatement)
    (hc : Ctx M Q Z B) {n : ℕ} {t : G} (hs : Sec9Hyp hc n t) {X Y : Subgroup G}
    (hsplit : Split95 M Q Z B t X Y) :
    Nat.card ↥(Uline Z B X) = Nat.card Z ^ 3 ∧ IsIrredModule X (Uline Z B X) Z ∧
      (∀ v ∈ Uline Z B X, ∃ x ∈ X, v ∈ (conjSubgroup x B ⊔ Z : Subgroup G)) ∧
      Uline Z B X ≤ Vt M (LB M Q B) B Z t := by
  obtain ⟨K, fK, finK, chK, hn, φ, ψ, u, H, Φ, w₀, hK, hψ, hnorm, hBiff, hH, hA, hw₀, hu, -, -⟩ :=
    sec97_line_data_of h34 h311a hc hs hsplit (Or.inl rfl)
  haveI := hn
  haveI : CharP K 2 := chK
  obtain ⟨⟨hQX, hXR, hQY, hYR, hXY, hXYQ, hcomm⟩, -, -⟩ := hsplit
  have ht : t ∈ LB M Q B := hs.toSec5.mem
  have hZV : Z ≤ Vt M (LB M Q B) B Z t := sec39_Z_le_Vt
  have hBV : B ≤ Vt M (LB M Q B) B Z t := hc.B_le_Vt ht
  have hmem := uline_mem_iff ψ φ hψ hnorm hXR hZV hBV u hBiff hH hA hw₀ hu
  have hUV : Uline Z B X ≤ Vt M (LB M Q B) B Z t := fun x hx => ((hmem x).mp hx).1
  have hu0 : toMat K u ≠ 0 := by
    rw [hu]
    exact fun h => hw₀ (hA.inj (by rw [h, map_zero]))
  have hbnz : ∃ b ∈ B, b ∉ Z := by
    obtain ⟨b, hbB, hbu⟩ := (hBiff u).mpr ⟨1, (one_smul K u).symm⟩
    refine ⟨(b : G), hbB, fun hbZ => hu0 ?_⟩
    rw [← hbu, (secVec_eq_zero_iff ψ b).mpr hbZ, map_zero]
  refine ⟨?_, uline_irred ψ φ hψ hnorm hXR hZV hBV u hBiff hH hA hw₀ hu hbnz,
    uline_cover ψ φ hψ hnorm hXR hZV hBV u hBiff hH hA hw₀ hu, hUV⟩
  rw [uline_card ψ φ hψ hnorm hXR hZV hBV u hBiff hH hA hw₀ hu, hK]
  ring

section MatrixAlgebra

variable {K : Type} [Field K]

private theorem eq_vecMulVec_of_mul_eq_self {A : Matrix.SpecialLinearGroup (Fin 2) K}
    (hA : A ≠ 1) {a : Fin 2 → K} (ha : a ≠ 0)
    (hAa : (A : Matrix (Fin 2) (Fin 2) K) *ᵥ a = a)
    {M : Matrix (Fin 2) (Fin 2) K} (hAM : (A : Matrix (Fin 2) (Fin 2) K) * M = M) :
    ∃ w : Fin 2 → K, M = Matrix.vecMulVec a w := by
  have hcol : ∀ j, (A : Matrix (Fin 2) (Fin 2) K) *ᵥ (fun i => M i j) = (fun i => M i j) := by
    intro j
    funext i
    have h := congrFun (congrFun hAM i) j
    rw [Matrix.mul_apply] at h
    simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two] using h
  choose w hw using fun j =>
    CFSG.LinearAlgebra.exists_eq_smul_of_mulVec_eq_self A hA ha hAa (hcol j)
  refine ⟨w, ?_⟩
  ext i j
  have h := congrFun (hw j) i
  simpa [Matrix.vecMulVec_apply, mul_comm] using h

theorem exists_vecMulVec_one_sub_of_vecMul_eq_self [CharP K 2]
    {C : Matrix (Fin 2) (Fin 2) K} (hdet : C.det = 1)
    {b : Fin 2 → K} (hb : b ≠ 0) (hCb : b ᵥ* C = b) (hCne : C ≠ 1) :
    ∃ u : Fin 2 → K, u ≠ 0 ∧ 1 - C = Matrix.vecMulVec u b := by
  let A := Cᵀ
  have hAdet : A.det = 1 := by
    dsimp [A]
    rw [Matrix.det_transpose, hdet]
  have hAb : A *ᵥ b = b := by
    rw [Matrix.mulVec_transpose]
    exact hCb
  have hAne : A ≠ 1 := by
    intro hA1
    apply hCne
    have hC : C = Aᵀ := by
      dsimp [A]
      rw [Matrix.transpose_transpose]
    rw [hC, hA1, Matrix.transpose_one]
  have hdetA1 : (A - 1).det = 0 := by
    refine Matrix.exists_mulVec_eq_zero_iff.mp ⟨b, hb, ?_⟩
    rw [Matrix.sub_mulVec, hAb, Matrix.one_mulVec, sub_self]
  have htr : A.trace = 0 := by
    have h1 : A 0 0 * A 1 1 - A 0 1 * A 1 0 = 1 := by
      simpa [Matrix.det_fin_two] using hAdet
    have h2 : (A 0 0 - 1) * (A 1 1 - 1) - A 0 1 * A 1 0 = 0 := by
      simpa [Matrix.det_fin_two, Matrix.sub_apply] using hdetA1
    have h3 : -(A 0 0 + A 1 1) + (2 : K) = 0 := by
      linear_combination h2 - h1
    have h20 : (2 : K) = 0 := CharP.cast_eq_zero K 2
    have h4 : -(A 0 0 + A 1 1) = 0 := by simpa [h20] using h3
    rw [Matrix.trace_fin_two]
    exact neg_eq_zero.mp h4
  have hA2 : A ^ 2 = 1 := by
    have hCH : A ^ 2 - A.trace • A + A.det • 1 = 0 := by
      have h := Matrix.aeval_self_charpoly A
      rw [Matrix.charpoly_fin_two] at h
      simpa [map_add, map_sub, map_mul, map_pow, Polynomial.aeval_X,
        Algebra.algebraMap_eq_smul_one, Matrix.smul_mul, Matrix.one_mul] using h
    rw [htr, hAdet] at hCH
    have hCH' : A ^ 2 + 1 = 0 := by simpa using hCH
    exact CharTwo.add_eq_zero.mp hCH'
  have hsq : (1 - A) * (1 - A) = 0 := by
    have hAA : A * A = 1 := by rw [← pow_two]; exact hA2
    rw [sub_mul, one_mul, mul_sub, mul_one, hAA]
    rw [CharTwo.sub_eq_add, CharTwo.sub_eq_add]
    simp [CharTwo.add_self_eq_zero, add_assoc, add_comm, add_left_comm]
  have hD : 1 - C = (1 - A)ᵀ := by
    dsimp [A]
    rw [Matrix.transpose_sub, Matrix.transpose_one, Matrix.transpose_transpose]
  have hD2 : (1 - C) * (1 - C) = 0 := by
    rw [hD, ← Matrix.transpose_mul, hsq, Matrix.transpose_zero]
  have hbD : b ᵥ* (1 - C) = 0 := by
    rw [Matrix.vecMul_sub, hCb, Matrix.vecMul_one, sub_self]
  have hDdet : (1 - C).det = 0 :=
    (Matrix.exists_vecMul_eq_zero_iff).mp ⟨b, hb, hbD⟩
  have hDne : 1 - C ≠ 0 := by
    intro h
    exact hCne (sub_eq_zero.mp h).symm
  obtain ⟨p, q, hp, hq, hDpq⟩ := exists_vecMulVec_of_det_eq_zero hDdet hDne
  have hbp : b ⬝ᵥ p = 0 := by
    have h := hbD
    rw [hDpq, Matrix.vecMul_vecMulVec] at h
    exact (smul_eq_zero.mp h).resolve_right hq
  have hqp : q ⬝ᵥ p = 0 := by
    have h := hD2
    rw [hDpq, Matrix.vecMulVec_mul_vecMulVec] at h
    have h' : (q ⬝ᵥ p) • q = 0 := by
      by_contra hne
      exact (Matrix.vecMulVec_ne_zero hp hne) h
    exact (smul_eq_zero.mp h').resolve_right hq
  obtain ⟨c, hcq⟩ := S715L.exists_eq_smul_of_dotProduct_eq_zero hp hb
    (by rwa [dotProduct_comm] at hbp) (by rwa [dotProduct_comm] at hqp)
  have hcne : c ≠ 0 := by
    intro hc0
    exact hq (by rw [hcq, hc0, zero_smul])
  refine ⟨c • p, smul_ne_zero hcne hp, ?_⟩
  rw [hDpq, hcq, Matrix.smul_vecMulVec, Matrix.vecMulVec_smul]

end MatrixAlgebra

theorem cmat_comm_eq {V Z R : Subgroup G} [(Z.subgroupOf V).Normal]
    {K : Type} [Field K]
    (φ : ↥R →* GL (Fin 2 ⊕ Fin 2) K)
    (ψ : ↥V ⧸ Z.subgroupOf V ≃* Multiplicative (Fin 2 ⊕ Fin 2 → K))
    (hψ : ∀ (s : ↥R) (v w : ↥V), (w : G) = (s : G) * v * (s : G)⁻¹ →
      Multiplicative.toAdd (ψ (QuotientGroup.mk w)) =
        (φ s : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ
          Multiplicative.toAdd (ψ (QuotientGroup.mk v)))
    (hnorm : R ≤ Subgroup.normalizer (V : Set G)) (s : ↥R) (v : ↥V) :
    cmat ψ ⟨⁅(s : G), (v : G)⁆, comm_mem_of_le_normalizer hnorm s v⟩ =
      Ψ K (φ s) (cmat ψ v) - cmat ψ v := by
  unfold cmat
  rw [secVec_comm φ ψ hψ hnorm s v, map_sub]
  congr 1
  rw [Ψ_apply, LinearEquiv.symm_apply_apply]

theorem apply_toMat_u_eq {V Z R : Subgroup G} [(Z.subgroupOf V).Normal]
    {K : Type} [Field K]
    (hc : Ctx M Q Z B)
    (φ : ↥R →* GL (Fin 2 ⊕ Fin 2) K)
    (ψ : ↥V ⧸ Z.subgroupOf V ≃* Multiplicative (Fin 2 ⊕ Fin 2 → K))
    (hψ : ∀ (s : ↥R) (v w : ↥V), (w : G) = (s : G) * v * (s : G)⁻¹ →
      Multiplicative.toAdd (ψ (QuotientGroup.mk w)) =
        (φ s : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ
          Multiplicative.toAdd (ψ (QuotientGroup.mk v)))
    (hnorm : R ≤ Subgroup.normalizer (V : Set G))
    (u : Fin 2 ⊕ Fin 2 → K)
    (hBiff : ∀ x : Fin 2 ⊕ Fin 2 → K,
      (∃ b : ↥V, (b : G) ∈ B ∧ secVec ψ b = x) ↔ ∃ c : K, x = c • u)
    {y : G} (hyL : y ∈ LB M Q B) (hyR : y ∈ R) :
    Ψ K (φ ⟨y, hyR⟩) (toMat K u) = toMat K u := by
  obtain ⟨b, hbB, hbu⟩ := (hBiff u).mpr ⟨1, (one_smul K u).symm⟩
  have hbZ : ⁅y, (b : G)⁆ ∈ Z := hc.comm_B_mem_Z hyL hbB
  have h0 : cmat ψ ⟨⁅y, (b : G)⁆, comm_mem_of_le_normalizer hnorm ⟨y, hyR⟩ b⟩ = 0 :=
    (cmat_eq_zero_iff ψ _).mpr hbZ
  rw [cmat_comm_eq φ ψ hψ hnorm ⟨y, hyR⟩ b] at h0
  have hfix : Ψ K (φ ⟨y, hyR⟩) (cmat ψ b) = cmat ψ b := sub_eq_zero.mp h0
  have hcb : cmat ψ b = toMat K u := by
    unfold cmat
    rw [hbu]
  rwa [hcb] at hfix

private theorem exists_mem_inf_not_mem_CN (h34 : Stroth34Statement) (h311a : Stroth311aStatement)
    (hc : Ctx M Q Z B) {n : ℕ} {t : G} (hs : Sec9Hyp hc n t) {X Y : Subgroup G}
    (hsplit : Split95 M Q Z B t X Y) (h4 : Sec4Concl M Q Z B X Y) :
    ∃ y ∈ LB M Q B ⊓ Y, y ∉ hc.CN t := by
  by_contra hno
  push Not at hno
  have hhead := (sec97Head_of h34 h311a G M Q Z B hc n t hs X Y hsplit).1
  obtain ⟨⟨-, -, -, -, -, hXYQ, -⟩, -, -⟩ := hsplit
  have hleQ : LB M Q B ⊓ Y ≤ Q := by
    intro y hy
    rw [← hXYQ]
    exact ⟨hhead (hno y hy), hy.2⟩
  have h1 : Q.relIndex (LB M Q B ⊓ Y) = 1 := Subgroup.relIndex_eq_one.mpr hleQ
  rw [h4.2.1] at h1
  have := hc.hyp.q4
  omega

theorem actsNat_leftF_outerL {K : Type} [Field K] [Finite K] [CharP K 2]
    {b : Fin 2 → K} (hb : b ≠ 0) : ActsNat (leftF K) (outerL b) := by
  refine ⟨outerL_injective hb, ?_, ?_⟩
  · rintro _ ⟨A, rfl⟩
    refine ⟨A, fun w => ?_⟩
    show rho' K (A, 1) (Matrix.vecMulVec w b) = Matrix.vecMulVec _ b
    rw [rho'_inl_apply, Matrix.mul_vecMulVec]
  · intro g
    refine ⟨rho' K (g, 1), ⟨g, rfl⟩, fun w => ?_⟩
    show rho' K (g, 1) (Matrix.vecMulVec w b) = Matrix.vecMulVec _ b
    rw [rho'_inl_apply, Matrix.mul_vecMulVec]

theorem actsNat_rightF_outerR {K : Type} [Field K] [Finite K] [CharP K 2]
    {a : Fin 2 → K} (ha : a ≠ 0) : ActsNat (rightF K) (outerR a) := by
  refine ⟨outerR_injective ha, ?_, ?_⟩
  · rintro _ ⟨B, rfl⟩
    refine ⟨(B⁻¹).transpose, fun w => ?_⟩
    show rho' K (1, B) (Matrix.vecMulVec a w) = Matrix.vecMulVec a _
    rw [rho'_inr_apply, Matrix.vecMulVec_mul, Matrix.SpecialLinearGroup.coe_transpose,
      Matrix.mulVec_transpose]
  · intro g
    refine ⟨rho' K (1, (g.transpose)⁻¹), ⟨_, rfl⟩, fun w => ?_⟩
    show rho' K (1, (g.transpose)⁻¹) (Matrix.vecMulVec a w) = Matrix.vecMulVec a _
    have e : (((g.transpose)⁻¹)⁻¹).transpose = g := by
      rw [inv_inv]
      exact Subtype.ext (Matrix.transpose_transpose _)
    rw [rho'_inr_apply, Matrix.vecMulVec_mul, ← Matrix.mulVec_transpose,
      ← Matrix.SpecialLinearGroup.coe_transpose, e]

private theorem left_matrix_of_y (hc : Ctx M Q Z B) {t : G}
    {X Y : Subgroup G} (hsplit : Split95 M Q Z B t X Y)
    {K : Type} [Field K] [Finite K] [CharP K 2]
    [(Z.subgroupOf (Vt M (LB M Q B) B Z t)).Normal]
    {φ : ↥(Rt M (LB M Q B) t) →* GL (Fin 2 ⊕ Fin 2) K}
    {ψ : ↥(Vt M (LB M Q B) B Z t) ⧸ Z.subgroupOf (Vt M (LB M Q B) B Z t) ≃*
      Multiplicative (Fin 2 ⊕ Fin 2 → K)}
    {u : Fin 2 ⊕ Fin 2 → K}
    (hψ : ∀ (s : ↥(Rt M (LB M Q B) t)) (v w : ↥(Vt M (LB M Q B) B Z t)),
      (w : G) = (s : G) * v * (s : G)⁻¹ →
      Multiplicative.toAdd (ψ (QuotientGroup.mk w)) =
        (φ s : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ
          Multiplicative.toAdd (ψ (QuotientGroup.mk v)))
    (hnorm : Rt M (LB M Q B) t ≤ Subgroup.normalizer (Vt M (LB M Q B) B Z t : Set G))
    (hBiff : ∀ x : Fin 2 ⊕ Fin 2 → K,
      (∃ b : ↥(Vt M (LB M Q B) B Z t), (b : G) ∈ B ∧ secVec ψ b = x) ↔
        ∃ c : K, x = c • u)
    (hker : φ.ker = (hc.CN t).subgroupOf (Rt M (LB M Q B) t))
    {a b : Fin 2 → K} (hb : b ≠ 0) (hu : toMat K u = Matrix.vecMulVec a b)
    (hYeq : (Y.subgroupOf (Rt M (LB M Q B) t)).map ((Ψ K).toMonoidHom.comp φ) = leftF K)
    {y : G} (hy : y ∈ LB M Q B ⊓ Y) (hyR : y ∈ Rt M (LB M Q B) t)
    (hyN : y ∉ hc.CN t) :
    ∃ A : Matrix.SpecialLinearGroup (Fin 2) K,
      rho' K (A, 1) = Ψ K (φ ⟨y, hyR⟩) ∧
      (A : Matrix (Fin 2) (Fin 2) K) ≠ 1 ∧
      (A : Matrix (Fin 2) (Fin 2) K) *ᵥ a = a := by
  classical
  obtain ⟨⟨-, hXR, -, hYR, -, -, -⟩, -, -⟩ := hsplit
  have hHY : ∀ h, h ∈ leftF K ↔
      ∃ s : ↥(Rt M (LB M Q B) t), (s : G) ∈ Y ∧ Ψ K (φ s) = h := by
    intro h
    rw [← hYeq]
    simp only [Subgroup.mem_map, Subgroup.mem_subgroupOf]
    exact Iff.rfl
  have hyMem : Ψ K (φ ⟨y, hyR⟩) ∈ leftF K :=
    (hHY _).mpr ⟨⟨y, hyR⟩, hy.2, rfl⟩
  obtain ⟨A, hA0⟩ := hyMem
  have hA : rho' K (A, 1) = Ψ K (φ ⟨y, hyR⟩) := by simpa using hA0
  have hφne : φ ⟨y, hyR⟩ ≠ 1 := by
    intro h1
    apply hyN
    have hmem : (⟨y, hyR⟩ : ↥(Rt M (LB M Q B) t)) ∈ φ.ker := h1
    rwa [hker, Subgroup.mem_subgroupOf] at hmem
  have hAne : (A : Matrix (Fin 2) (Fin 2) K) ≠ 1 := by
    intro hA1
    apply hφne
    apply (Ψ K).injective
    have hrho1 : rho' K (A, 1) = 1 := by
      have hA1' : A = 1 := Subtype.ext hA1
      rw [hA1']
      exact map_one (rho' K)
    rw [← hA, hrho1]
    exact (map_one (Ψ K)).symm
  have hfix_u : Ψ K (φ ⟨y, hyR⟩) (toMat K u) = toMat K u :=
    apply_toMat_u_eq hc φ ψ hψ hnorm u hBiff hy.1 hyR
  have hAu : (A : Matrix (Fin 2) (Fin 2) K) * toMat K u = toMat K u := by
    rw [← rho'_inl_apply, hA]
    exact hfix_u
  have hAa : (A : Matrix (Fin 2) (Fin 2) K) *ᵥ a = a := by
    have h := hAu
    rw [hu, Matrix.mul_vecMulVec] at h
    obtain ⟨j, hj⟩ : ∃ j, b j ≠ 0 := by
      by_contra hcon
      push Not at hcon
      exact hb (funext hcon)
    funext i
    have h' := congrFun (congrFun h i) j
    simp only [Matrix.vecMulVec_apply] at h'
    exact mul_right_cancel₀ hj h'
  exact ⟨A, hA, hAne, hAa⟩

private theorem left_fixed_A (h34 : Stroth34Statement) (h311a : Stroth311aStatement)
    (hc : Ctx M Q Z B) {n : ℕ} {t : G} (hs : Sec9Hyp hc n t)
    {X Y : Subgroup G} (hsplit : Split95 M Q Z B t X Y)
    (h4 : Sec4Concl M Q Z B X Y)
    {K : Type} [Field K] [Finite K] [CharP K 2]
    [(Z.subgroupOf (Vt M (LB M Q B) B Z t)).Normal]
    {φ : ↥(Rt M (LB M Q B) t) →* GL (Fin 2 ⊕ Fin 2) K}
    {ψ : ↥(Vt M (LB M Q B) B Z t) ⧸ Z.subgroupOf (Vt M (LB M Q B) B Z t) ≃*
      Multiplicative (Fin 2 ⊕ Fin 2 → K)}
    {u : Fin 2 ⊕ Fin 2 → K}
    (hψ : ∀ (s : ↥(Rt M (LB M Q B) t)) (v w : ↥(Vt M (LB M Q B) B Z t)),
      (w : G) = (s : G) * v * (s : G)⁻¹ →
      Multiplicative.toAdd (ψ (QuotientGroup.mk w)) =
        (φ s : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ
          Multiplicative.toAdd (ψ (QuotientGroup.mk v)))
    (hnorm : Rt M (LB M Q B) t ≤ Subgroup.normalizer (Vt M (LB M Q B) B Z t : Set G))
    (hBiff : ∀ x : Fin 2 ⊕ Fin 2 → K,
      (∃ b : ↥(Vt M (LB M Q B) B Z t), (b : G) ∈ B ∧ secVec ψ b = x) ↔
        ∃ c : K, x = c • u)
    (hker : φ.ker = (hc.CN t).subgroupOf (Rt M (LB M Q B) t))
    {a b : Fin 2 → K} (hb : b ≠ 0) (hu : toMat K u = Matrix.vecMulVec a b)
    (hYeq : (Y.subgroupOf (Rt M (LB M Q B) t)).map ((Ψ K).toMonoidHom.comp φ) = leftF K)
    {v : G} (hv : v ∈ Vt M (LB M Q B) B Z t)
    (hfix : ∀ y ∈ LB M Q B ⊓ Y, ⁅y, v⁆ ∈ Z) :
    ∃ A : Matrix.SpecialLinearGroup (Fin 2) K,
      (A : Matrix (Fin 2) (Fin 2) K) ≠ 1 ∧
      (A : Matrix (Fin 2) (Fin 2) K) *ᵥ a = a ∧
      (A : Matrix (Fin 2) (Fin 2) K) * cmat ψ ⟨v, hv⟩ = cmat ψ ⟨v, hv⟩ := by
  classical
  obtain ⟨y, hy, hyN⟩ := exists_mem_inf_not_mem_CN h34 h311a hc hs hsplit h4
  have hyR : y ∈ Rt M (LB M Q B) t := by
    obtain ⟨⟨-, -, -, hYR, -, -, -⟩, -, -⟩ := hsplit
    exact hYR hy.2
  obtain ⟨A, hA, hAne, hAa⟩ :=
    left_matrix_of_y hc hsplit hψ hnorm hBiff hker hb hu hYeq hy hyR hyN
  have h0 : cmat ψ ⟨⁅y, v⁆, comm_mem_of_le_normalizer hnorm ⟨y, hyR⟩ ⟨v, hv⟩⟩ = 0 :=
    (cmat_eq_zero_iff ψ _).mpr (hfix y hy)
  rw [cmat_comm_eq φ ψ hψ hnorm ⟨y, hyR⟩ ⟨v, hv⟩] at h0
  have hfix_eq : Ψ K (φ ⟨y, hyR⟩) (cmat ψ ⟨v, hv⟩) = cmat ψ ⟨v, hv⟩ := sub_eq_zero.mp h0
  have hAM : (A : Matrix (Fin 2) (Fin 2) K) * cmat ψ ⟨v, hv⟩ = cmat ψ ⟨v, hv⟩ := by
    rw [← rho'_inl_apply, hA]
    exact hfix_eq
  exact ⟨A, hAne, hAa, hAM⟩

private theorem mem_ulineX_of_fix_left (h34 : Stroth34Statement) (h311a : Stroth311aStatement)
    (hc : Ctx M Q Z B) {n : ℕ} {t : G} (hs : Sec9Hyp hc n t)
    {X Y : Subgroup G} (hsplit : Split95 M Q Z B t X Y)
    (h4 : Sec4Concl M Q Z B X Y)
    {K : Type} [Field K] [Finite K] [CharP K 2]
    [(Z.subgroupOf (Vt M (LB M Q B) B Z t)).Normal]
    {φ : ↥(Rt M (LB M Q B) t) →* GL (Fin 2 ⊕ Fin 2) K}
    {ψ : ↥(Vt M (LB M Q B) B Z t) ⧸ Z.subgroupOf (Vt M (LB M Q B) B Z t) ≃*
      Multiplicative (Fin 2 ⊕ Fin 2 → K)}
    {u : Fin 2 ⊕ Fin 2 → K}
    (hψ : ∀ (s : ↥(Rt M (LB M Q B) t)) (v w : ↥(Vt M (LB M Q B) B Z t)),
      (w : G) = (s : G) * v * (s : G)⁻¹ →
      Multiplicative.toAdd (ψ (QuotientGroup.mk w)) =
        (φ s : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ
          Multiplicative.toAdd (ψ (QuotientGroup.mk v)))
    (hnorm : Rt M (LB M Q B) t ≤ Subgroup.normalizer (Vt M (LB M Q B) B Z t : Set G))
    (hBiff : ∀ x : Fin 2 ⊕ Fin 2 → K,
      (∃ b : ↥(Vt M (LB M Q B) B Z t), (b : G) ∈ B ∧ secVec ψ b = x) ↔
        ∃ c : K, x = c • u)
    (hker : φ.ker = (hc.CN t).subgroupOf (Rt M (LB M Q B) t))
    {a b : Fin 2 → K} (ha : a ≠ 0) (hb : b ≠ 0) (hu : toMat K u = Matrix.vecMulVec a b)
    (hYeq : (Y.subgroupOf (Rt M (LB M Q B) t)).map ((Ψ K).toMonoidHom.comp φ) = leftF K)
    (hXeq : (X.subgroupOf (Rt M (LB M Q B) t)).map ((Ψ K).toMonoidHom.comp φ) = rightF K)
    {v : G} (hv : v ∈ Vt M (LB M Q B) B Z t)
    (hfix : ∀ y ∈ LB M Q B ⊓ Y, ⁅y, v⁆ ∈ Z) :
    v ∈ Uline Z B X := by
  classical
  have ht : t ∈ LB M Q B := hs.toSec5.mem
  have hZV : Z ≤ Vt M (LB M Q B) B Z t := sec39_Z_le_Vt
  have hBV : B ≤ Vt M (LB M Q B) B Z t := hc.B_le_Vt ht
  obtain ⟨A, hAne, hAa, hAM⟩ :=
    left_fixed_A h34 h311a hc hs hsplit h4 hψ hnorm hBiff hker hb hu hYeq hv hfix
  obtain ⟨⟨-, hXR, -, hYR, -, -, -⟩, -, -⟩ := hsplit
  have hAne' : A ≠ 1 := fun h => hAne (by
    rw [h]
    rfl)
  obtain ⟨w, hw⟩ := eq_vecMulVec_of_mul_eq_self hAne' ha hAa hAM
  have hHX : ∀ h, h ∈ rightF K ↔
      ∃ s : ↥(Rt M (LB M Q B) t), (s : G) ∈ X ∧ Ψ K (φ s) = h := by
    intro h
    rw [← hXeq]
    simp only [Subgroup.mem_map, Subgroup.mem_subgroupOf]
    exact Iff.rfl
  refine (uline_mem_iff ψ φ hψ hnorm hXR hZV hBV u hBiff hHX
    (actsNat_rightF_outerR (a := a) ha) hb hu v).mpr ⟨hv, ?_⟩
  exact ⟨w, by rw [hw]; rfl⟩

private theorem right_action_of_y (hc : Ctx M Q Z B) {t : G} {Y : Subgroup G}
    {K : Type} [Field K] [Finite K] [CharP K 2]
    [(Z.subgroupOf (Vt M (LB M Q B) B Z t)).Normal]
    {φ : ↥(Rt M (LB M Q B) t) →* GL (Fin 2 ⊕ Fin 2) K}
    {ψ : ↥(Vt M (LB M Q B) B Z t) ⧸ Z.subgroupOf (Vt M (LB M Q B) B Z t) ≃*
      Multiplicative (Fin 2 ⊕ Fin 2 → K)}
    {u : Fin 2 ⊕ Fin 2 → K}
    (hψ : ∀ (s : ↥(Rt M (LB M Q B) t)) (v w : ↥(Vt M (LB M Q B) B Z t)),
      (w : G) = (s : G) * v * (s : G)⁻¹ →
      Multiplicative.toAdd (ψ (QuotientGroup.mk w)) =
        (φ s : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ
          Multiplicative.toAdd (ψ (QuotientGroup.mk v)))
    (hnorm : Rt M (LB M Q B) t ≤ Subgroup.normalizer (Vt M (LB M Q B) B Z t : Set G))
    (hBiff : ∀ x : Fin 2 ⊕ Fin 2 → K,
      (∃ b : ↥(Vt M (LB M Q B) B Z t), (b : G) ∈ B ∧ secVec ψ b = x) ↔
        ∃ c : K, x = c • u)
    (hker : φ.ker = (hc.CN t).subgroupOf (Rt M (LB M Q B) t))
    {a b : Fin 2 → K} (ha : a ≠ 0) (hu : toMat K u = Matrix.vecMulVec a b)
    (hYeq : (Y.subgroupOf (Rt M (LB M Q B) t)).map ((Ψ K).toMonoidHom.comp φ) = rightF K)
    {y : G} (hy : y ∈ LB M Q B ⊓ Y) (hyR : y ∈ Rt M (LB M Q B) t)
    (hyN : y ∉ hc.CN t) :
    ∃ (Bmat : Matrix.SpecialLinearGroup (Fin 2) K) (C : Matrix (Fin 2) (Fin 2) K),
      rho' K (1, Bmat) = Ψ K (φ ⟨y, hyR⟩) ∧
      C = ((Bmat⁻¹ : Matrix.SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) ∧
      C ≠ 1 ∧ b ᵥ* C = b := by
  classical
  have hHY : ∀ h, h ∈ rightF K ↔
      ∃ s : ↥(Rt M (LB M Q B) t), (s : G) ∈ Y ∧ Ψ K (φ s) = h := by
    intro h
    rw [← hYeq]
    simp only [Subgroup.mem_map, Subgroup.mem_subgroupOf]
    exact Iff.rfl
  have hyMem : Ψ K (φ ⟨y, hyR⟩) ∈ rightF K :=
    (hHY _).mpr ⟨⟨y, hyR⟩, hy.2, rfl⟩
  obtain ⟨Bmat, hB0⟩ := hyMem
  have hB : rho' K (1, Bmat) = Ψ K (φ ⟨y, hyR⟩) := by simpa using hB0
  have hfix_u : Ψ K (φ ⟨y, hyR⟩) (toMat K u) = toMat K u :=
    apply_toMat_u_eq hc φ ψ hψ hnorm u hBiff hy.1 hyR
  have hMu : toMat K u * (((Bmat⁻¹ : Matrix.SpecialLinearGroup (Fin 2) K) :
      Matrix (Fin 2) (Fin 2) K)) = toMat K u := by
    rw [← rho'_inr_apply, hB]
    exact hfix_u
  have hbC : b ᵥ* (((Bmat⁻¹ : Matrix.SpecialLinearGroup (Fin 2) K) :
      Matrix (Fin 2) (Fin 2) K)) = b := by
    have h := hMu
    rw [hu, Matrix.vecMulVec_mul] at h
    obtain ⟨i, hi⟩ : ∃ i, a i ≠ 0 := by
      by_contra hcon
      push Not at hcon
      exact ha (funext hcon)
    funext j
    have h' := congrFun (congrFun h i) j
    simp only [Matrix.vecMulVec_apply] at h'
    exact mul_left_cancel₀ hi h'
  let C : Matrix (Fin 2) (Fin 2) K := ((Bmat⁻¹ : Matrix.SpecialLinearGroup (Fin 2) K) :
    Matrix (Fin 2) (Fin 2) K)
  have hCne : C ≠ 1 := by
    intro hC1
    have hC1' : Bmat⁻¹ = 1 := Subtype.ext hC1
    have hB1 : Bmat = 1 := inv_eq_one.mp hC1'
    apply hyN
    have h1 : φ ⟨y, hyR⟩ = 1 := by
      apply (Ψ K).injective
      rw [← hB]
      have hrho1 : rho' K (1, Bmat) = 1 := by
        rw [hB1]
        exact map_one (rho' K)
      rw [hrho1]
      exact (map_one (Ψ K)).symm
    have hmem : (⟨y, hyR⟩ : ↥(Rt M (LB M Q B) t)) ∈ φ.ker := h1
    rwa [hker, Subgroup.mem_subgroupOf] at hmem
  exact ⟨Bmat, C, hB, rfl, hCne, hbC⟩

private theorem right_fixed_A (h34 : Stroth34Statement) (h311a : Stroth311aStatement)
    (hc : Ctx M Q Z B) {n : ℕ} {t : G} (hs : Sec9Hyp hc n t)
    {X Y : Subgroup G} (hsplit : Split95 M Q Z B t X Y)
    (h4 : Sec4Concl M Q Z B X Y)
    {K : Type} [Field K] [Finite K] [CharP K 2]
    [(Z.subgroupOf (Vt M (LB M Q B) B Z t)).Normal]
    {φ : ↥(Rt M (LB M Q B) t) →* GL (Fin 2 ⊕ Fin 2) K}
    {ψ : ↥(Vt M (LB M Q B) B Z t) ⧸ Z.subgroupOf (Vt M (LB M Q B) B Z t) ≃*
      Multiplicative (Fin 2 ⊕ Fin 2 → K)}
    {u : Fin 2 ⊕ Fin 2 → K}
    (hψ : ∀ (s : ↥(Rt M (LB M Q B) t)) (v w : ↥(Vt M (LB M Q B) B Z t)),
      (w : G) = (s : G) * v * (s : G)⁻¹ →
      Multiplicative.toAdd (ψ (QuotientGroup.mk w)) =
        (φ s : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ
          Multiplicative.toAdd (ψ (QuotientGroup.mk v)))
    (hnorm : Rt M (LB M Q B) t ≤ Subgroup.normalizer (Vt M (LB M Q B) B Z t : Set G))
    (hBiff : ∀ x : Fin 2 ⊕ Fin 2 → K,
      (∃ b : ↥(Vt M (LB M Q B) B Z t), (b : G) ∈ B ∧ secVec ψ b = x) ↔
        ∃ c : K, x = c • u)
    (hker : φ.ker = (hc.CN t).subgroupOf (Rt M (LB M Q B) t))
    {a b : Fin 2 → K} (ha : a ≠ 0) (hu : toMat K u = Matrix.vecMulVec a b)
    (hYeq : (Y.subgroupOf (Rt M (LB M Q B) t)).map ((Ψ K).toMonoidHom.comp φ) = rightF K)
    {v : G} (hv : v ∈ Vt M (LB M Q B) B Z t)
    (hfix : ∀ y ∈ LB M Q B ⊓ Y, ⁅y, v⁆ ∈ Z) :
    ∃ A : Matrix.SpecialLinearGroup (Fin 2) K,
      A ≠ 1 ∧ (A : Matrix (Fin 2) (Fin 2) K) *ᵥ b = b ∧
        (A : Matrix (Fin 2) (Fin 2) K) * (cmat ψ ⟨v, hv⟩)ᵀ = (cmat ψ ⟨v, hv⟩)ᵀ := by
  classical
  obtain ⟨y, hy, hyN⟩ := exists_mem_inf_not_mem_CN h34 h311a hc hs hsplit h4
  have hyR : y ∈ Rt M (LB M Q B) t := by
    obtain ⟨⟨-, -, -, hYR, -, -, -⟩, -, -⟩ := hsplit
    exact hYR hy.2
  obtain ⟨Bmat, C, hB, hCdef, hCne, hbC⟩ :=
    right_action_of_y hc hψ hnorm hBiff hker ha hu hYeq hy hyR hyN
  have hAne : Cᵀ ≠ 1 := by
    intro hA1
    apply hCne
    have h := congrArg Matrix.transpose hA1
    simpa using h
  have hAb : Cᵀ *ᵥ b = b := by
    rw [Matrix.mulVec_transpose]
    exact hbC
  have h0 : cmat ψ ⟨⁅y, v⁆, comm_mem_of_le_normalizer hnorm ⟨y, hyR⟩ ⟨v, hv⟩⟩ = 0 :=
    (cmat_eq_zero_iff ψ _).mpr (hfix y hy)
  rw [cmat_comm_eq φ ψ hψ hnorm ⟨y, hyR⟩ ⟨v, hv⟩] at h0
  have hfix_eq : Ψ K (φ ⟨y, hyR⟩) (cmat ψ ⟨v, hv⟩) = cmat ψ ⟨v, hv⟩ := sub_eq_zero.mp h0
  have hMC : cmat ψ ⟨v, hv⟩ * C = cmat ψ ⟨v, hv⟩ := by
    rw [hCdef, ← rho'_inr_apply, hB]
    exact hfix_eq
  have htrans : Cᵀ * (cmat ψ ⟨v, hv⟩)ᵀ = (cmat ψ ⟨v, hv⟩)ᵀ := by
    have h := congrArg Matrix.transpose hMC
    rwa [Matrix.transpose_mul] at h
  let Amat : Matrix.SpecialLinearGroup (Fin 2) K := (Bmat⁻¹).transpose
  have hAmat : (Amat : Matrix (Fin 2) (Fin 2) K) = Cᵀ := by
    change (((Bmat⁻¹ : Matrix.SpecialLinearGroup (Fin 2) K) :
      Matrix (Fin 2) (Fin 2) K))ᵀ = Cᵀ
    rw [← hCdef]
  have hAne' : Amat ≠ 1 := by
    intro h
    apply hAne
    have h1 : (Amat : Matrix (Fin 2) (Fin 2) K) = 1 := by rw [h]; rfl
    rwa [hAmat] at h1
  have hAb' : (Amat : Matrix (Fin 2) (Fin 2) K) *ᵥ b = b := by
    rw [hAmat]
    exact hAb
  have htrans' : (Amat : Matrix (Fin 2) (Fin 2) K) * (cmat ψ ⟨v, hv⟩)ᵀ =
      (cmat ψ ⟨v, hv⟩)ᵀ := by
    rw [hAmat]
    exact htrans
  exact ⟨Amat, hAne', hAb', htrans'⟩

private theorem mem_ulineX_of_fix_right (h34 : Stroth34Statement) (h311a : Stroth311aStatement)
    (hc : Ctx M Q Z B) {n : ℕ} {t : G} (hs : Sec9Hyp hc n t)
    {X Y : Subgroup G} (hsplit : Split95 M Q Z B t X Y)
    (h4 : Sec4Concl M Q Z B X Y)
    {K : Type} [Field K] [Finite K] [CharP K 2]
    [(Z.subgroupOf (Vt M (LB M Q B) B Z t)).Normal]
    {φ : ↥(Rt M (LB M Q B) t) →* GL (Fin 2 ⊕ Fin 2) K}
    {ψ : ↥(Vt M (LB M Q B) B Z t) ⧸ Z.subgroupOf (Vt M (LB M Q B) B Z t) ≃*
      Multiplicative (Fin 2 ⊕ Fin 2 → K)}
    {u : Fin 2 ⊕ Fin 2 → K}
    (hψ : ∀ (s : ↥(Rt M (LB M Q B) t)) (v w : ↥(Vt M (LB M Q B) B Z t)),
      (w : G) = (s : G) * v * (s : G)⁻¹ →
      Multiplicative.toAdd (ψ (QuotientGroup.mk w)) =
        (φ s : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ
          Multiplicative.toAdd (ψ (QuotientGroup.mk v)))
    (hnorm : Rt M (LB M Q B) t ≤ Subgroup.normalizer (Vt M (LB M Q B) B Z t : Set G))
    (hBiff : ∀ x : Fin 2 ⊕ Fin 2 → K,
      (∃ b : ↥(Vt M (LB M Q B) B Z t), (b : G) ∈ B ∧ secVec ψ b = x) ↔
        ∃ c : K, x = c • u)
    (hker : φ.ker = (hc.CN t).subgroupOf (Rt M (LB M Q B) t))
    {a b : Fin 2 → K} (ha : a ≠ 0) (hb : b ≠ 0) (hu : toMat K u = Matrix.vecMulVec a b)
    (hYeq : (Y.subgroupOf (Rt M (LB M Q B) t)).map ((Ψ K).toMonoidHom.comp φ) = rightF K)
    (hXeq : (X.subgroupOf (Rt M (LB M Q B) t)).map ((Ψ K).toMonoidHom.comp φ) = leftF K)
    {v : G} (hv : v ∈ Vt M (LB M Q B) B Z t)
    (hfix : ∀ y ∈ LB M Q B ⊓ Y, ⁅y, v⁆ ∈ Z) :
    v ∈ Uline Z B X := by
  classical
  have ht : t ∈ LB M Q B := hs.toSec5.mem
  have hZV : Z ≤ Vt M (LB M Q B) B Z t := sec39_Z_le_Vt
  have hBV : B ≤ Vt M (LB M Q B) B Z t := hc.B_le_Vt ht
  obtain ⟨A, hAne, hAb, htrans⟩ :=
    right_fixed_A h34 h311a hc hs hsplit h4 hψ hnorm hBiff hker ha hu hYeq hv hfix
  obtain ⟨⟨-, hXR, -, hYR, -, -, -⟩, -, -⟩ := hsplit
  obtain ⟨w, hw⟩ := eq_vecMulVec_of_mul_eq_self hAne hb hAb htrans
  have hMw : cmat ψ ⟨v, hv⟩ = Matrix.vecMulVec w b := by
    have h2 : cmat ψ ⟨v, hv⟩ = (Matrix.vecMulVec b w)ᵀ := by
      rw [← hw, Matrix.transpose_transpose]
    rwa [Matrix.transpose_vecMulVec] at h2
  have hHX : ∀ h, h ∈ leftF K ↔
      ∃ s : ↥(Rt M (LB M Q B) t), (s : G) ∈ X ∧ Ψ K (φ s) = h := by
    intro h
    rw [← hXeq]
    simp only [Subgroup.mem_map, Subgroup.mem_subgroupOf]
    exact Iff.rfl
  refine (uline_mem_iff ψ φ hψ hnorm hXR hZV hBV u hBiff hHX
    (actsNat_leftF_outerL (b := b) hb) ha hu v).mpr ⟨hv, ?_⟩
  exact ⟨w, by rw [hMw]; rfl⟩

theorem mem_ulineX_of_fix (h34 : Stroth34Statement) (h311a : Stroth311aStatement)
    (hc : Ctx M Q Z B) {n : ℕ} {t : G} (hs : Sec9Hyp hc n t) {X Y : Subgroup G}
    (hsplit : Split95 M Q Z B t X Y) (h4 : Sec4Concl M Q Z B X Y) {v : G}
    (hv : v ∈ Vt M (LB M Q B) B Z t) (hfix : ∀ y ∈ LB M Q B ⊓ Y, ⁅y, v⁆ ∈ Z) :
    v ∈ Uline Z B X := by
  classical
  obtain ⟨K, fK, finK, chK, hn, φ, ψ, u, hK, hrange, hker, hnorm, hψ, hBiff, hW, hdet, hu0⟩ :=
    sec9_coord h34 hc hs
  haveI := hn
  haveI : CharP K 2 := chK
  obtain ⟨a, b, ha, hb, hu⟩ := exists_vecMulVec_of_det_eq_zero hdet hu0
  have hfac := sec97_factor_pair h34 h311a hc hs hsplit hK φ hrange hker
  rcases hfac with ⟨hYeq, hXeq⟩ | ⟨hYeq, hXeq⟩
  · exact mem_ulineX_of_fix_left h34 h311a hc hs hsplit h4 hψ hnorm hBiff hker
      ha hb hu hYeq hXeq hv hfix
  · exact mem_ulineX_of_fix_right h34 h311a hc hs hsplit h4 hψ hnorm hBiff hker
      ha hb hu hYeq hXeq hv hfix

end HS9

end CFSG.RankThree.GF2n.Stroth80
