module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotCentralizerA2
public import CFSG.HardMathSupport.Cooperstein.Coordinator.LieInput.SpCent
public import CFSG.RankThree.GF2n.Tim81.Sec7.Defs

public section

namespace CFSG.RankThree.GF2n.Tim81

open CFSG CFSG.Timmesfeld.ARS CFSG.Assembly.LowTwoRank
open scoped Matrix
open CFSG.LieType.Universal.Symplectic CFSG.LieType.Universal.Symplectic.SpExtras
open CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.HardMathSupport.Cooperstein.Coordinator.LieInput

namespace SpRootRad

variable {k : ℕ} {F : Type} [Field F]

private def emb (k : ℕ) : Fin k ⊕ Fin k → Fin (k + 1) ⊕ Fin (k + 1) :=
  Sum.map Fin.castSucc Fin.castSucc

private theorem emb_injective : Function.Injective (emb k) :=
  Sum.map_injective.2 ⟨Fin.castSucc_injective k, Fin.castSucc_injective k⟩

private theorem emb_ne_inl (a : Fin k ⊕ Fin k) : emb k a ≠ Sum.inl (Fin.last k) := by
  rcases a with j | j
  · simp [emb, (Fin.castSucc_lt_last j).ne]
  · simp [emb]

private theorem emb_ne_inr (a : Fin k ⊕ Fin k) : emb k a ≠ Sum.inr (Fin.last k) := by
  rcases a with j | j
  · simp [emb]
  · simp [emb, (Fin.castSucc_lt_last j).ne]

private theorem inl_last_not_mem :
    (Sum.inl (Fin.last k) : Fin (k + 1) ⊕ Fin (k + 1)) ∉ Set.range (emb k) :=
  fun ⟨a, ha⟩ => emb_ne_inl a ha

private theorem inr_last_not_mem :
    (Sum.inr (Fin.last k) : Fin (k + 1) ⊕ Fin (k + 1)) ∉ Set.range (emb k) :=
  fun ⟨a, ha⟩ => emb_ne_inr a ha

private theorem sum_split {M : Type*} [AddCommMonoid M] (f : Fin (k + 1) ⊕ Fin (k + 1) → M) :
    ∑ c, f c = ∑ d, f (emb k d) + f (Sum.inl (Fin.last k)) + f (Sum.inr (Fin.last k)) := by
  rw [Fintype.sum_sum_type, Fintype.sum_sum_type, Fin.sum_univ_castSucc, Fin.sum_univ_castSucc]
  simp only [emb, Sum.map_inl, Sum.map_inr]
  abel

private noncomputable abbrev longT (k : ℕ) (F : Type) [Field F] : Subgroup (StatedSp (k + 1) F) :=
  rootGroup (k + 1) F (Pi.single (Fin.last k) 1)

private theorem stdVec_long :
    stdVec (.positiveLong (Fin.last k)) = toStd (k + 1) (Pi.single (Fin.last k) (1 : ℤ)) := by
  rw [toStd_single_of_not_lt' (by simp)]
  rfl

private abbrev IsRC (M : Matrix (Fin (k + 1) ⊕ Fin (k + 1)) (Fin (k + 1) ⊕ Fin (k + 1)) F) : Prop :=
  (∀ x, M x (Sum.inl (Fin.last k)) = if x = Sum.inl (Fin.last k) then 1 else 0) ∧
    ∀ y, M (Sum.inr (Fin.last k)) y = if y = Sum.inr (Fin.last k) then 1 else 0

private theorem isRC_of_mem [CharP F 2] {g : StatedSp (k + 1) F}
    (hg : g ∈ Subgroup.centralizer (longT k F : Set (StatedSp (k + 1) F))) :
    IsRC (mat (k + 1) F g) := by
  have h1 : elt (.positiveLong (Fin.last k)) (1 : F) ∈ longT k F :=
    (mem_rootGroup_iff stdVec_long).2 ⟨1, rfl⟩
  have hc := Subgroup.mem_centralizer_iff.1 hg _ h1
  exact col_row_of_comm_long (Fin.last k) (comm_mat_of_comm _ hc.symm)

private theorem mem_of_isRC {g : StatedSp (k + 1) F} (h : IsRC (mat (k + 1) F g)) :
    g ∈ Subgroup.centralizer (longT k F : Set (StatedSp (k + 1) F)) := by
  rw [Subgroup.mem_centralizer_iff]
  intro t ht
  obtain ⟨c, rfl⟩ := (mem_rootGroup_iff stdVec_long).1 ht
  apply mat_injective
  have hE : E F (.positiveLong (Fin.last k)) * mat (k + 1) F g =
      mat (k + 1) F g * E F (.positiveLong (Fin.last k)) := by
    ext x y
    rw [Emul_long, mulE_long]
    by_cases hx : x = Sum.inl (Fin.last k) <;> by_cases hy : y = Sum.inr (Fin.last k) <;>
      simp [hx, hy, h.1, h.2]
  rw [map_mul, map_mul, mat_elt, Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one,
    Matrix.smul_mul, Matrix.mul_smul, hE]

private theorem submatrix_mul
    {G H : Matrix (Fin (k + 1) ⊕ Fin (k + 1)) (Fin (k + 1) ⊕ Fin (k + 1)) F}
    (hG : IsRC G) (hH : IsRC H) :
    (G * H).submatrix (emb k) (emb k) =
      G.submatrix (emb k) (emb k) * H.submatrix (emb k) (emb k) := by
  ext a b
  simp only [Matrix.submatrix_apply, Matrix.mul_apply]
  rw [sum_split, hG.1, hH.2, if_neg (emb_ne_inl a), if_neg (emb_ne_inr b)]
  simp

private theorem gram_form_t {n : ℕ} (M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F)
    (x y : Fin n ⊕ Fin n) :
    (Mᵀ * gram F n * M) x y =
      ∑ i, (M (Sum.inl i) x * M (Sum.inr i) y - M (Sum.inr i) x * M (Sum.inl i) y) := by
  have h := gram_form Mᵀ x y
  simp only [Matrix.transpose_transpose, Matrix.transpose_apply] at h
  exact h

private theorem gram_emb (a b : Fin k ⊕ Fin k) :
    gram F (k + 1) (emb k a) (emb k b) = gram F k a b := by
  rcases a with i | i <;> rcases b with j | j <;>
    simp [emb, gram, Matrix.one_apply, Fin.castSucc_inj]

private theorem submatrix_symplectic
    {G : Matrix (Fin (k + 1) ⊕ Fin (k + 1)) (Fin (k + 1) ⊕ Fin (k + 1)) F} (hG : IsRC G)
    (hJ : Gᵀ * gram F (k + 1) * G = gram F (k + 1)) :
    (G.submatrix (emb k) (emb k))ᵀ * gram F k * G.submatrix (emb k) (emb k) = gram F k := by
  ext a b
  have h := congrFun (congrFun hJ (emb k a)) (emb k b)
  rw [gram_form_t, Fin.sum_univ_castSucc, hG.2 (emb k a), hG.2 (emb k b),
    if_neg (emb_ne_inr a), if_neg (emb_ne_inr b), gram_emb] at h
  rw [gram_form_t, ← h]
  simp [emb]

variable (k F) in
private noncomputable def piC [CharP F 2] :
    Subgroup.centralizer (longT k F : Set (StatedSp (k + 1) F)) →* StatedSp k F where
  toFun g := ofSymplecticMat ((mat (k + 1) F g).submatrix (emb k) (emb k))
    (submatrix_symplectic (isRC_of_mem g.2) (mat_transpose_mul_gram_mul g.1))
  map_one' := by
    apply mat_injective
    rw [mat_ofSymplecticMat, OneMemClass.coe_one, map_one, map_one]
    exact Matrix.submatrix_one _ emb_injective
  map_mul' g h := by
    apply mat_injective
    rw [mat_ofSymplecticMat, map_mul, mat_ofSymplecticMat, mat_ofSymplecticMat, Subgroup.coe_mul,
      map_mul]
    exact submatrix_mul (isRC_of_mem g.2) (isRC_of_mem h.2)

private theorem mat_piC [CharP F 2]
    (g : Subgroup.centralizer (longT k F : Set (StatedSp (k + 1) F))) :
    mat k F (piC k F g) = (mat (k + 1) F g).submatrix (emb k) (emb k) :=
  rfl

private theorem piC_surjective [CharP F 2] : Function.Surjective (piC k F) := by
  intro A
  set g := spEmbed (K := F) (Fin.castSucc : Fin k → Fin (k + 1)) (Fin.castSucc_injective k) A
  have hg : IsRC (mat (k + 1) F g) := by
    rw [mat_spEmbed]
    refine ⟨fun x => ?_, fun y => ?_⟩
    · rw [spEmbedMat_apply_of_not_mem _ (fun h => inl_last_not_mem h.2), Matrix.one_apply]
    · rw [spEmbedMat_apply_of_not_mem _ (fun h => inr_last_not_mem h.1), Matrix.one_apply]
      simp only [eq_comm]
  refine ⟨⟨g, mem_of_isRC hg⟩, mat_injective ?_⟩
  rw [mat_piC]
  ext a b
  rw [Matrix.submatrix_apply]
  exact spEmbedMat_apply_image (Fin.castSucc_injective k) _ a b

private theorem col_last_eq [CharP F 2]
    {G : Matrix (Fin (k + 1) ⊕ Fin (k + 1)) (Fin (k + 1) ⊕ Fin (k + 1)) F} (hG : IsRC G)
    (hGs : ∀ a b, G (emb k a) (emb k b) = if a = b then 1 else 0)
    (hJ : G * gram F (k + 1) * Gᵀ = gram F (k + 1)) (b : Fin k ⊕ Fin k) :
    G (emb k b) (Sum.inr (Fin.last k)) = G (Sum.inl (Fin.last k)) (emb k b.swap) := by
  have h := congrFun (congrFun hJ (emb k b)) (Sum.inl (Fin.last k))
  rw [show G * gram F (k + 1) * Gᵀ = G * Jmat (k + 1) F * Gᵀ from rfl, gram_form,
    Fin.sum_univ_castSucc, hG.1 (emb k b), if_neg (emb_ne_inl b), hG.1 (Sum.inl (Fin.last k)),
    if_pos rfl] at h
  have hgram : gram F (k + 1) (emb k b) (Sum.inl (Fin.last k)) = 0 := by
    rcases b with j | j <;> simp [emb, gram, Matrix.one_apply, (Fin.castSucc_lt_last j).ne]
  rw [hgram] at h
  have hl : ∀ j : Fin k, G (emb k b) (Sum.inl j.castSucc) = if b = Sum.inl j then 1 else 0 :=
    fun j => hGs b (Sum.inl j)
  have hr : ∀ j : Fin k, G (emb k b) (Sum.inr j.castSucc) = if b = Sum.inr j then 1 else 0 :=
    fun j => hGs b (Sum.inr j)
  simp only [hl, hr, ite_mul, one_mul, zero_mul, zero_sub, mul_one] at h
  rcases b with j₀ | j₀
  · simp only [Sum.inl.injEq, reduceCtorEq, if_false, sub_zero, Finset.sum_ite_eq,
      Finset.mem_univ, if_true] at h
    rw [CharTwo.neg_eq, add_eq_zero_iff_eq_neg, CharTwo.neg_eq] at h
    exact h.symm
  · simp only [Sum.inr.injEq, reduceCtorEq, if_false, zero_sub, Finset.sum_neg_distrib,
      Finset.sum_ite_eq, Finset.mem_univ, if_true] at h
    rw [CharTwo.neg_eq, CharTwo.neg_eq, add_eq_zero_iff_eq_neg, CharTwo.neg_eq] at h
    exact h.symm

private theorem coord_cases (x : Fin (k + 1) ⊕ Fin (k + 1)) :
    (∃ a, x = emb k a) ∨ x = Sum.inl (Fin.last k) ∨ x = Sum.inr (Fin.last k) := by
  rcases x with i | i <;> rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
  · exact Or.inl ⟨Sum.inl j, rfl⟩
  · exact Or.inr (Or.inl rfl)
  · exact Or.inl ⟨Sum.inr j, rfl⟩
  · exact Or.inr (Or.inr rfl)

private theorem sum_ite_mul {α : Type*} [Fintype α] [DecidableEq α] (a : α) (f : α → F) :
    ∑ d, (if a = d then (1 : F) else 0) * f d = f a := by
  simp [ite_mul]

private theorem sum_mul_ite {α : Type*} [Fintype α] [DecidableEq α] (b : α) (f : α → F) :
    ∑ d, f d * (if d = b then (1 : F) else 0) = f b := by
  simp [mul_ite]

private theorem mul_apply_rc
    {G H : Matrix (Fin (k + 1) ⊕ Fin (k + 1)) (Fin (k + 1) ⊕ Fin (k + 1)) F}
    (hG : IsRC G) (hH : IsRC H) (x z : Fin (k + 1) ⊕ Fin (k + 1)) :
    (G * H) x z = ∑ d, G x (emb k d) * H (emb k d) z +
      (if x = Sum.inl (Fin.last k) then 1 else 0) * H (Sum.inl (Fin.last k)) z +
        G x (Sum.inr (Fin.last k)) * (if z = Sum.inr (Fin.last k) then 1 else 0) := by
  rw [Matrix.mul_apply, sum_split, hG.1 x, hH.2 z]

private theorem commute_of_mem_ker [CharP F 2]
    {g h : Subgroup.centralizer (longT k F : Set (StatedSp (k + 1) F))}
    (hg : g ∈ (piC k F).ker) (hh : h ∈ (piC k F).ker) : g * h = h * g := by
  have hsub : ∀ u : Subgroup.centralizer (longT k F : Set (StatedSp (k + 1) F)),
      u ∈ (piC k F).ker → ∀ a b, mat (k + 1) F u (emb k a) (emb k b) = if a = b then 1 else 0 := by
    intro u hu a b
    have h1 := congrFun (congrFun (congrArg (mat k F) (MonoidHom.mem_ker.1 hu)) a) b
    rw [mat_piC, map_one, Matrix.submatrix_apply, Matrix.one_apply] at h1
    exact h1
  set G := mat (k + 1) F g with hGdef
  set H := mat (k + 1) F h with hHdef
  have hG : IsRC G := isRC_of_mem g.2
  have hH : IsRC H := isRC_of_mem h.2
  have hGs : ∀ a b, G (emb k a) (emb k b) = if a = b then 1 else 0 := hsub g hg
  have hHs : ∀ a b, H (emb k a) (emb k b) = if a = b then 1 else 0 := hsub h hh
  have hGc := col_last_eq hG hGs (mat_mul_gram_mul_transpose g.1)
  have hHc := col_last_eq hH hHs (mat_mul_gram_mul_transpose h.1)
  have key : G * H = H * G := by
    ext x z
    rw [mul_apply_rc hG hH, mul_apply_rc hH hG]
    rcases coord_cases x with ⟨a, rfl⟩ | rfl | rfl
    · simp only [hGs, hHs, sum_ite_mul, if_neg (emb_ne_inl a), zero_mul, add_zero]
      rcases coord_cases z with ⟨b, rfl⟩ | rfl | rfl
      · rw [hGs, hHs, if_neg (emb_ne_inr b), mul_zero, mul_zero]
      · simp only [hG.1, hH.1, if_neg (emb_ne_inl a), reduceCtorEq, if_false, mul_zero]
      · rw [if_pos rfl, mul_one, mul_one, add_comm]
    · simp only [if_true, one_mul]
      rcases coord_cases z with ⟨b, rfl⟩ | rfl | rfl
      · simp only [hGs, hHs, sum_mul_ite, if_neg (emb_ne_inr b), mul_zero, add_zero]
        exact add_comm _ _
      · simp only [hG.1, hH.1, if_neg (emb_ne_inl _), if_true, mul_zero,
          Finset.sum_const_zero, zero_add, reduceCtorEq, if_false]
      · simp only [hGc, hHc, if_true, mul_one]
        have hswap : ∑ d, H (Sum.inl (Fin.last k)) (emb k d) *
              G (Sum.inl (Fin.last k)) (emb k d.swap) =
            ∑ d, G (Sum.inl (Fin.last k)) (emb k d) * H (Sum.inl (Fin.last k)) (emb k d.swap) := by
          rw [← (Equiv.sumComm (Fin k) (Fin k)).sum_comp]
          simp only [Equiv.sumComm_apply, Sum.swap_swap]
          exact Finset.sum_congr rfl fun d _ => mul_comm _ _
        rw [hswap]
        abel
    · simp only [hG.2, hH.2, if_neg (emb_ne_inr _), zero_mul, Finset.sum_const_zero, zero_add,
        reduceCtorEq, if_false, if_true, one_mul]
  refine Subtype.ext (mat_injective ?_)
  rw [Subgroup.coe_mul, Subgroup.coe_mul, map_mul, map_mul]
  exact key

private theorem commute_of_normal [Finite F] [CharP F 2] (hF : 4 ≤ Nat.card F) (hk : 1 ≤ k)
    (N : Subgroup (Subgroup.centralizer (longT k F : Set (StatedSp (k + 1) F)))) (hN : N.Normal)
    (h2 : IsPGroup 2 N) {a b : Subgroup.centralizer (longT k F : Set (StatedSp (k + 1) F))}
    (ha : a ∈ N) (hb : b ∈ N) : a * b = b * a := by
  haveI : (N.map (piC k F)).Normal := hN.map (piC k F) piC_surjective
  have hbot := CFSG.SeitzReduction.SymplecticPilot.eq_bot_of_normal_of_isPGroup_statedSp hF hk
    (N.map (piC k F)) (h2.map (piC k F))
  have hker : ∀ c ∈ N, c ∈ (piC k F).ker := fun c hc => by
    rw [MonoidHom.mem_ker, ← Subgroup.mem_bot, ← hbot]
    exact Subgroup.mem_map_of_mem _ hc
  exact commute_of_mem_ker (hker a ha) (hker b hb)

end SpRootRad

open SpRootRad in
theorem symplecticRootRadicalAbelian :
    ∀ (K : Type) [Group K] [Finite K] (X₀ : Subgroup K) (Δ : Set (Subgroup K)) (f m : ℕ)
      (hm : 2 ≤ m), 2 ≤ f → IsSpImage X₀ Δ f m (by omega) → ∀ T ∈ Δ,
        inSubgroup (pCore 2) (X₀ ⊓ cenOf T) ≤ cenOf (inSubgroup (pCore 2) (X₀ ⊓ cenOf T)) := by
  intro K _ _ X₀ Δ f m hm hf hX T hT
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  obtain ⟨Φ, hΦ, hrange, hΔ⟩ := hX
  obtain ⟨x, rfl⟩ := (hΔ T).1 hT
  have hlast : (⟨k + 1 - 1, by omega⟩ : Fin (k + 1)) = Fin.last k := Fin.ext (by simp)
  have hT0 : (CFSG.LieType.Universal.Symplectic.rootDatum (k + 1) (GaloisField 2 f)).rootGroup
      (Pi.single (⟨k + 1 - 1, by omega⟩ : Fin (k + 1)) 1) = longT k (GaloisField 2 f) := by
    rw [hlast]
    rfl
  rw [hT0]
  set ψ : StatedSp (k + 1) (GaloisField 2 f) →* K := Φ.comp (MulAut.conj x).toMonoidHom with hψdef
  have hψ : Function.Injective ψ := hΦ.comp (MulAut.conj x).injective
  have hTψ : (conjSub (longT k (GaloisField 2 f)) x).map Φ = (longT k (GaloisField 2 f)).map ψ := by
    rw [conjSub, Subgroup.map_map]
  have hrange' : ψ.range = X₀ := by
    rw [← hrange]
    ext y
    constructor
    · rintro ⟨g, rfl⟩
      exact ⟨_, rfl⟩
    · rintro ⟨g, rfl⟩
      exact ⟨x⁻¹ * g * x, by simp [hψdef, mul_assoc]⟩
  have hH : X₀ ⊓ cenOf ((longT k (GaloisField 2 f)).map ψ) =
      (Subgroup.centralizer (longT k (GaloisField 2 f) : Set _)).map ψ := by
    ext y
    rw [Subgroup.mem_inf, Subgroup.mem_map]
    constructor
    · rintro ⟨hy0, hyc⟩
      rw [← hrange'] at hy0
      obtain ⟨g, rfl⟩ := hy0
      refine ⟨g, ?_, rfl⟩
      rw [Subgroup.mem_centralizer_iff] at hyc ⊢
      intro t ht
      apply hψ
      rw [map_mul, map_mul]
      exact hyc (ψ t) (Subgroup.mem_map_of_mem ψ ht)
    · rintro ⟨g, hg, rfl⟩
      refine ⟨hrange' ▸ ⟨g, rfl⟩, ?_⟩
      rw [Subgroup.mem_centralizer_iff] at hg ⊢
      intro t' ht'
      obtain ⟨t, ht, rfl⟩ := Subgroup.mem_map.1 ht'
      rw [← map_mul, ← map_mul, hg t ht]
  rw [hTψ, hH]
  have hk : 1 ≤ k := by omega
  have hF : 4 ≤ Nat.card (GaloisField 2 f) := by
    rw [GaloisField.card 2 f (by omega)]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  set C := Subgroup.centralizer
    (longT k (GaloisField 2 f) : Set (StatedSp (k + 1) (GaloisField 2 f)))
  set H' := C.map ψ
  let e : C ≃* H' := Subgroup.equivMapOfInjective C ψ hψ
  intro a ha
  rw [Subgroup.mem_centralizer_iff]
  intro b hb
  simp only [inSubgroup] at ha hb
  obtain ⟨u, hu, rfl⟩ := ha
  obtain ⟨v, hv, rfl⟩ := hb
  rw [← map_mul, ← map_mul]
  congr 1
  have hN : ((CFSG.pCore 2 H').map e.symm.toMonoidHom).Normal :=
    CFSG.pCore_normal.map _ e.symm.surjective
  have h2 : IsPGroup 2 ((CFSG.pCore 2 H').map e.symm.toMonoidHom) :=
    CFSG.pCore_isPGroup.map _
  have hc := commute_of_normal hF hk _ hN h2 (Subgroup.mem_map_of_mem _ hv)
    (Subgroup.mem_map_of_mem _ hu)
  apply e.symm.injective
  rw [map_mul, map_mul]
  exact hc

end CFSG.RankThree.GF2n.Tim81
