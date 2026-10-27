module

public import CFSG.Quasithin.EmptyFaithful.T1515C4Mod
public import CFSG.Quasithin.Vol2.Ch6Sec2Lem7W2

public section

namespace CFSG.Quasithin.H13

open CFSG.Open hiding StatedSL StatedClassicalModel StatedProj StatedLieTag StatedLieAdmissible
open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank

section Transvection

variable {K : Type} [Field K]

@[expose] def tvec627 (f : (Fin 3 → K) →ₗ[K] K) (w : Fin 3 → K) : Matrix (Fin 3) (Fin 3) K :=
  1 + Matrix.vecMulVec w (fun j => f (Pi.single j 1))

theorem dotProduct_form627 (f : (Fin 3 → K) →ₗ[K] K) (v : Fin 3 → K) :
    (fun j => f (Pi.single j 1)) ⬝ᵥ v = f v := by
  conv_rhs => rw [← Finset.univ_sum_single v]
  rw [map_sum]
  simp only [dotProduct]
  refine Finset.sum_congr rfl fun j _ => ?_
  have e : Pi.single j (v j) = v j • Pi.single j (1 : K) := by
    funext k
    by_cases h : k = j
    · subst h
      simp
    · simp [h]
  rw [e, map_smul, smul_eq_mul, mul_comm]

theorem tvec627_mulVec (f : (Fin 3 → K) →ₗ[K] K) (w v : Fin 3 → K) :
    (tvec627 f w).mulVec v = v + f v • w := by
  rw [tvec627, Matrix.add_mulVec, Matrix.one_mulVec, Matrix.vecMulVec_mulVec, op_smul_eq_smul,
    dotProduct_form627]

theorem det_tvec627 (f : (Fin 3 → K) →ₗ[K] K) (w : Fin 3 → K) :
    (tvec627 f w).det = 1 + f w := by
  rw [tvec627, Matrix.vecMulVec_eq Unit, Matrix.det_one_add_replicateCol_mul_replicateRow,
    dotProduct_form627]

@[expose] noncomputable def tvecSL627 (f : (Fin 3 → K) →ₗ[K] K) (w : Fin 3 → K) (hw : f w = 0) :
    ↥(StatedSL 3 K) :=
  specialLinearGroupEquivStatedSL 3 K ⟨tvec627 f w, by rw [det_tvec627, hw, add_zero]⟩

theorem tvecSL627_coe (f : (Fin 3 → K) →ₗ[K] K) (w : Fin 3 → K) (hw : f w = 0) :
    (((tvecSL627 f w hw : ↥(StatedSL 3 K)) : Matrix.GeneralLinearGroup (Fin 3) K) :
      Matrix (Fin 3) (Fin 3) K) = tvec627 f w := rfl

end Transvection

variable {Q : Type} [CommGroup Q]

theorem card_le_mul_fixV_inf627 [Finite Q] (A : Subgroup (MulAut Q)) (U : Subgroup Q) :
    Nat.card U ≤ (fixV A).index * Nat.card ↥(fixV A ⊓ U) := by
  have h1 := Subgroup.relIndex_mul_card (fixV A) U
  have h2 : (fixV A).relIndex U ≤ (fixV A).index :=
    (Subgroup.relIndex_le_of_le_right le_top (by
      rw [Subgroup.relIndex_top_right]; exact Subgroup.index_ne_zero_of_finite)).trans_eq
      (Subgroup.relIndex_top_right _)
  rw [inf_comm] at h1
  calc Nat.card U = (fixV A).relIndex U * Nat.card ↥(fixV A ⊓ U) := by rw [inf_comm, h1]
    _ ≤ (fixV A).index * Nat.card ↥(fixV A ⊓ U) := Nat.mul_le_mul_right _ h2

theorem isFFStarOffenderOn627 [Finite Q] {G A : Subgroup (MulAut Q)} (hAG : A ≤ G) (hA1 : A ≠ ⊥)
    (hAab : IsElemAbelian2 A) (hfix : ∀ a ∈ A, a ≠ 1 → fixV (Subgroup.zpowers a) = fixV A)
    (hidx : (fixV A).index ≤ Nat.card A) (U : Subgroup Q) : IsFFStarOffenderOn G A U := by
  refine ⟨hAG, hA1, hAab, fun B hBA => ?_⟩
  by_cases hB : B = ⊥
  · subst hB
    have hfix0 : fixV (⊥ : Subgroup (MulAut Q)) = ⊤ := by
      ext v
      simp only [mem_fixV, Subgroup.mem_bot, Subgroup.mem_top, iff_true]
      rintro x rfl
      rfl
    rw [Subgroup.card_bot, one_mul, hfix0, top_inf_eq]
    exact (card_le_mul_fixV_inf627 A U).trans (Nat.mul_le_mul_right _ hidx)
  · obtain ⟨⟨b, hbB⟩, hb1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hB
    have hb1' : b ≠ 1 := fun h => hb1 (Subtype.ext h)
    have hfB : fixV B = fixV A := by
      refine le_antisymm ?_ (fun v hv x hx => hv x (hBA hx))
      rw [← hfix b (hBA hbB) hb1']
      exact fun v hv x hx => hv x (Subgroup.zpowers_le.mpr hbB hx)
    rw [hfB]
    exact Nat.mul_le_mul_right _ (Subgroup.card_le_of_le hBA)

theorem false_of_case1ii627 [Finite Q] {J L A : Subgroup (MulAut Q)} (hii : B51Case1ii J L)
    (hAJ : A ≤ J) (hA1 : A ≠ ⊥) (hAab : IsElemAbelian2 A)
    (hfix : ∀ a ∈ A, a ≠ 1 → fixV (Subgroup.zpowers a) = fixV A)
    (hidx : (fixV A).index ≤ Nat.card A) (hcomm : Nat.card (commV A) ≤ 4) : False := by
  classical
  obtain ⟨-, n, K, _, _, -, I, π, hind, -, hreal, hoff, -⟩ := hii
  obtain ⟨-, W, hW2, hWT⟩ := (hoff A).mp (isFFStarOffenderOn627 hAJ hA1 hAab hfix hidx _)
  have hWlt : W < ⊤ := by
    refine lt_top_iff_ne_top.mpr fun h => ?_
    have h3 : Module.finrank K ↥W = 3 := by
      rw [h, finrank_top, Module.finrank_fin_fun]
    omega
  obtain ⟨f, hf0, hWf⟩ := W.exists_le_ker_of_lt_top hWlt
  obtain ⟨v₁, hv₁⟩ : ∃ v, f v ≠ 0 := by
    by_contra h
    push Not at h
    exact hf0 (LinearMap.ext h)
  set v₀ : Fin 3 → K := (f v₁)⁻¹ • v₁ with hv₀
  have hfv₀ : f v₀ = 1 := by rw [hv₀, map_smul, smul_eq_mul, inv_mul_cancel₀ hv₁]
  have hfW : ∀ w ∈ W, f w = 0 := fun w hw => LinearMap.mem_ker.mp (hWf hw)
  have hgA : ∀ w : ↥W, ((π (tvecSL627 f w (hfW w w.2)) : ↥L) : MulAut Q) ∈ A := by
    intro w
    have h1 := (hWT (tvecSL627 f w (hfW w w.2))).mpr ⟨fun w' hw' => ?_, fun v => ?_⟩
    · exact Subgroup.mem_subgroupOf.mp h1
    · rw [tvecSL627_coe, tvec627_mulVec, hfW w' hw', zero_smul, add_zero]
    · rw [tvecSL627_coe, tvec627_mulVec, add_sub_cancel_left]
      exact W.smul_mem _ w.2
  have hcI : ∀ i : Fin 2, ∃ c : ↥W → ↥(commV A), (∀ w, ((c w : ↥(commV A)) : Q) ∈ I i) ∧
      Function.Injective c := by
    intro i
    obtain ⟨-, hUinv, β, hβs, -, hβe⟩ := natReal627 (hreal i)
    obtain ⟨u₀, hu₀⟩ := hβs (Multiplicative.ofAdd v₀)
    have hmem : ∀ w : ↥W, ((π (tvecSL627 f w (hfW w w.2)) : ↥L) : MulAut Q) (u₀ : Q) ∈ I i :=
      fun w => hUinv _ _ u₀.2
    refine ⟨fun w => ⟨((π (tvecSL627 f w (hfW w w.2)) : ↥L) : MulAut Q) (u₀ : Q) * (u₀ : Q)⁻¹,
      Subgroup.subset_closure ⟨_, hgA w, u₀, rfl⟩⟩, fun w => (I i).mul_mem (hmem w)
        ((I i).inv_mem u₀.2), fun w w' hww => ?_⟩
    have hβc : ∀ w : ↥W, Multiplicative.toAdd (β (⟨_, hmem w⟩ * u₀⁻¹)) = (w : Fin 3 → K) := by
      intro w
      rw [map_mul, map_inv, toAdd_mul, toAdd_inv, hβe _ u₀ (hmem w), hu₀, toAdd_ofAdd,
        tvecSL627_coe, tvec627_mulVec, hfv₀, one_smul]
      abel
    have h0 : ((π (tvecSL627 f w (hfW w w.2)) : ↥L) : MulAut Q) (u₀ : Q) * (u₀ : Q)⁻¹ =
        ((π (tvecSL627 f w' (hfW w' w'.2)) : ↥L) : MulAut Q) (u₀ : Q) * (u₀ : Q)⁻¹ := by
      simpa using congrArg Subtype.val hww
    have h1 : (⟨_, hmem w⟩ * u₀⁻¹ : ↥(I i)) = ⟨_, hmem w'⟩ * u₀⁻¹ :=
      Subtype.ext (by simpa using h0)
    apply Subtype.ext
    rw [← hβc w, ← hβc w', h1]
  obtain ⟨c₀, hc₀I, hc₀⟩ := hcI 0
  obtain ⟨c₁, hc₁I, hc₁⟩ := hcI 1
  have hdisj : I 0 ⊓ I 1 = ⊥ := disjoint_iff.mp (hind.pairwiseDisjoint (by decide))
  have hinj : Function.Injective fun p : ↥W × ↥W => c₀ p.1 * c₁ p.2 := by
    rintro ⟨w₁, w₂⟩ ⟨x₁, x₂⟩ h
    set a := ((c₀ w₁ : ↥(commV A)) : Q) with ha
    set a' := ((c₀ x₁ : ↥(commV A)) : Q) with ha'
    set b := ((c₁ w₂ : ↥(commV A)) : Q) with hb
    set b' := ((c₁ x₂ : ↥(commV A)) : Q) with hb'
    have h1 : a * b = a' * b' := congrArg Subtype.val h
    have h2 : a * a'⁻¹ = b' * b⁻¹ := by
      calc a * a'⁻¹ = (a * b) * (a'⁻¹ * b⁻¹) := by rw [mul_mul_mul_comm, mul_inv_cancel, mul_one]
        _ = (a' * b') * (a'⁻¹ * b⁻¹) := by rw [h1]
        _ = b' * b⁻¹ := by rw [mul_mul_mul_comm, mul_inv_cancel, one_mul]
    have h3 : a * a'⁻¹ ∈ I 0 ⊓ I 1 :=
      ⟨(I 0).mul_mem (hc₀I w₁) ((I 0).inv_mem (hc₀I x₁)),
        h2 ▸ (I 1).mul_mem (hc₁I x₂) ((I 1).inv_mem (hc₁I w₂))⟩
    rw [hdisj, Subgroup.mem_bot] at h3
    have h4 : w₁ = x₁ := hc₀ (Subtype.ext (mul_inv_eq_one.mp h3))
    have h5 : b' * b⁻¹ = 1 := h2 ▸ h3
    have h6 : x₂ = w₂ := hc₁ (Subtype.ext (mul_inv_eq_one.mp h5))
    rw [h4, h6]
  have : Fintype K := Fintype.ofFinite K
  have hW4 : 4 ≤ Nat.card ↥W := by
    have : Fintype ↥W := Fintype.ofFinite _
    rw [Nat.card_eq_fintype_card, Module.card_eq_pow_finrank (K := K), hW2]
    have : 2 ≤ Fintype.card K := Fintype.one_lt_card
    nlinarith
  have h16 := Nat.card_le_card_of_injective _ hinj
  rw [Nat.card_prod] at h16
  nlinarith

end CFSG.Quasithin.H13
