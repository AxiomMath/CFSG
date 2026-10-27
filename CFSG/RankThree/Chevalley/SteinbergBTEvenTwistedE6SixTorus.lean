module

public import CFSG.LieType.Chevalley.GraphFixedFinitePerfect
public import CFSG.LieType.Chevalley.GraphFixedHighestRoot
public import CFSG.LieType.Chevalley.E6ToralGraphInvolution

public noncomputable section

namespace CFSG.RankThree.Chevalley

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley Matrix
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open scoped Pointwise commutatorElement

section CharTwo

variable {K : Type} [Field K]

theorem sixTorus_neg_eq (h2 : (2 : K) = 0) (c : K) : -c = c := by
  rw [neg_eq_iff_add_eq_zero, ← two_mul, h2, zero_mul]

theorem sixTorus_units_neg_one (h2 : (2 : K) = 0) : (-1 : Kˣ) = 1 :=
  Units.ext (by rw [Units.val_neg, Units.val_one, sixTorus_neg_eq h2])

theorem sixTorus_weylElt_inv {τ : Tag} (h2 : (2 : K) = 0) (i : Fin τ.rank) :
    (weylElt τ K i 1)⁻¹ = weylElt τ K i 1 := by
  rw [weylElt_inv, sixTorus_units_neg_one h2]

theorem sixTorus_list_prod_inv {τ : Tag} (h2 : (2 : K) = 0) (ω : List (Fin τ.rank)) :
    ((ω.map fun i => weylElt τ K i 1).prod)⁻¹ = (ω.reverse.map fun i => weylElt τ K i 1).prod := by
  have e : ((fun x => x⁻¹) ∘ fun i => weylElt τ K i 1) = fun i : Fin τ.rank => weylElt τ K i 1 :=
    funext fun i => sixTorus_weylElt_inv h2 i
  rw [List.prod_inv_reverse, List.map_map, e, List.map_reverse]

theorem sixTorus_conj_word {τ : Tag} (h2 : (2 : K) = 0) (ω : List (Fin τ.rank))
    {α : Fin τ.rank → ℤ} (hα : IsRoot τ α) (c : K) :
    (ω.map fun i => weylElt τ K i 1).prod * pinnedX τ K α c *
        ((ω.map fun i => weylElt τ K i 1).prod)⁻¹ =
      pinnedX τ K (ω.foldr (reflect τ) α) c := by
  obtain ⟨ε, hε, h⟩ := exists_prod_weylElt_mul_pinnedX_mul_inv K ω hα
  rw [h, eq_one_of_mul_self_eq_one_of_two_eq_zero h2 hε, one_mul, wordProd_smul]

theorem sixTorus_isRoot_foldr {τ : Tag} (ω : List (Fin τ.rank)) {α : Fin τ.rank → ℤ}
    (hα : IsRoot τ α) : IsRoot τ (ω.foldr (reflect τ) α) := by
  induction ω with
  | nil => exact hα
  | cons i ω ih => exact IsRoot.reflect i ih

end CharTwo

section SL2

variable {K : Type} [Field K]

theorem sixTorus_hom_ext {G : Type*} [Group G] {φ ψ : SL2 K →* G}
    (hu : ∀ c, φ (uSL c) = ψ (uSL c)) (hv : ∀ c, φ (vSL c) = ψ (vSL c)) : φ = ψ := by
  apply MonoidHom.eq_of_eqOn_dense
    (CFSG.LocalAnalysis.ComponentInitial.sl2_closure_upper_lower (K := K))
  rintro _ (⟨c, rfl⟩ | ⟨c, rfl⟩)
  · exact hu c
  · exact hv c

theorem sixTorus_commute_of_gen {G : Type*} [Group G] (φ ψ : SL2 K →* G)
    (h : ∀ x ∈ Set.range (uSL (K := K)) ∪ Set.range (vSL (K := K)),
      ∀ y ∈ Set.range (uSL (K := K)) ∪ Set.range (vSL (K := K)), Commute (φ x) (ψ y))
    (A B : SL2 K) : Commute (φ A) (ψ B) := by
  have hS : Subgroup.closure (Set.range (uSL (K := K)) ∪ Set.range (vSL (K := K))) = ⊤ :=
    CFSG.LocalAnalysis.ComponentInitial.sl2_closure_upper_lower (K := K)
  have h1 : ∀ y ∈ Set.range (uSL (K := K)) ∪ Set.range (vSL (K := K)), ∀ A : SL2 K,
      Commute (φ A) (ψ y) := by
    intro y hy A
    have hle : Subgroup.closure (Set.range (uSL (K := K)) ∪ Set.range (vSL (K := K))) ≤
        (Subgroup.centralizer {ψ y}).comap φ :=
      (Subgroup.closure_le _).2 fun x hx =>
        Subgroup.mem_centralizer_singleton_iff.2 (h x hx y hy).eq
    exact Subgroup.mem_centralizer_singleton_iff.1
      (Subgroup.mem_comap.1 (hle (hS ▸ Subgroup.mem_top A)))
  have hle : Subgroup.closure (Set.range (uSL (K := K)) ∪ Set.range (vSL (K := K))) ≤
      (Subgroup.centralizer {φ A}).comap ψ :=
    (Subgroup.closure_le _).2 fun y hy =>
      Subgroup.mem_centralizer_singleton_iff.2 (h1 y hy A).symm.eq
  exact (Subgroup.mem_centralizer_singleton_iff.1
    (Subgroup.mem_comap.1 (hle (hS ▸ Subgroup.mem_top B)))).symm

theorem sixTorus_WSL_eq : (WSL : SL2 K) = uSL 1 * vSL (-1) * uSL 1 :=
  SL2_ext (by simp [coe_WSL, coe_uSL, coe_vSL, Matrix.mul_apply, Fin.sum_univ_two])
    (by simp [coe_WSL, coe_uSL, coe_vSL, Matrix.mul_apply, Fin.sum_univ_two])
    (by simp [coe_WSL, coe_uSL, coe_vSL, Matrix.mul_apply, Fin.sum_univ_two])
    (by simp [coe_WSL, coe_uSL, coe_vSL, Matrix.mul_apply, Fin.sum_univ_two])

variable [CharP K 2]

theorem sixTorus_two : (2 : K) = 0 := CharP.cast_eq_zero K 2

@[expose] def sixTorusS : SL2 K :=
  ⟨!![0, 1; 1, 0], by rw [Matrix.det_fin_two_of, mul_zero, mul_one, zero_sub,
    sixTorus_neg_eq sixTorus_two]⟩

@[expose] def sixTorusP (ω : K) : SL2 K :=
  ⟨!![ω, ω + 1; 1, 1], by rw [Matrix.det_fin_two_of, mul_one, mul_one, sub_add_cancel_left,
    sixTorus_neg_eq sixTorus_two]⟩

theorem coe_sixTorusS : ((sixTorusS : SL2 K) : Matrix (Fin 2) (Fin 2) K) = !![0, 1; 1, 0] := rfl

theorem coe_sixTorusP (ω : K) :
    ((sixTorusP ω : SL2 K) : Matrix (Fin 2) (Fin 2) K) = !![ω, ω + 1; 1, 1] := rfl

theorem sixTorusS_eq_WSL : (sixTorusS : SL2 K) = WSL :=
  SL2_ext rfl rfl (by rw [coe_sixTorusS, coe_WSL]; simp [sixTorus_neg_eq sixTorus_two]) rfl

theorem sixTorusS_mul_self : (sixTorusS : SL2 K) * sixTorusS = 1 :=
  SL2_ext (by simp [coe_sixTorusS, Matrix.mul_apply, Fin.sum_univ_two])
    (by simp [coe_sixTorusS, Matrix.mul_apply, Fin.sum_univ_two])
    (by simp [coe_sixTorusS, Matrix.mul_apply, Fin.sum_univ_two])
    (by simp [coe_sixTorusS, Matrix.mul_apply, Fin.sum_univ_two])

theorem sixTorusS_inv : (sixTorusS : SL2 K)⁻¹ = sixTorusS :=
  inv_eq_of_mul_eq_one_right sixTorusS_mul_self

theorem sixTorusS_conj_uSL (c : K) : sixTorusS * uSL c * sixTorusS⁻¹ = vSL c := by
  rw [sixTorusS_inv]
  exact SL2_ext (by simp [coe_sixTorusS, coe_uSL, coe_vSL, Matrix.mul_apply, Fin.sum_univ_two])
    (by simp [coe_sixTorusS, coe_uSL, coe_vSL, Matrix.mul_apply, Fin.sum_univ_two])
    (by simp [coe_sixTorusS, coe_uSL, coe_vSL, Matrix.mul_apply, Fin.sum_univ_two])
    (by simp [coe_sixTorusS, coe_uSL, coe_vSL, Matrix.mul_apply, Fin.sum_univ_two])

theorem sixTorusS_conj_vSL (c : K) : sixTorusS * vSL c * sixTorusS⁻¹ = uSL c := by
  rw [sixTorusS_inv]
  exact SL2_ext (by simp [coe_sixTorusS, coe_uSL, coe_vSL, Matrix.mul_apply, Fin.sum_univ_two])
    (by simp [coe_sixTorusS, coe_uSL, coe_vSL, Matrix.mul_apply, Fin.sum_univ_two])
    (by simp [coe_sixTorusS, coe_uSL, coe_vSL, Matrix.mul_apply, Fin.sum_univ_two])
    (by simp [coe_sixTorusS, coe_uSL, coe_vSL, Matrix.mul_apply, Fin.sum_univ_two])

theorem sixTorusS_conj_HSL (t : Kˣ) : sixTorusS * HSL t * sixTorusS⁻¹ = HSL t⁻¹ := by
  rw [sixTorusS_inv]
  exact SL2_ext (by simp [coe_sixTorusS, coe_HSL, Matrix.mul_apply, Fin.sum_univ_two])
    (by simp [coe_sixTorusS, coe_HSL, Matrix.mul_apply, Fin.sum_univ_two])
    (by simp [coe_sixTorusS, coe_HSL, Matrix.mul_apply, Fin.sum_univ_two])
    (by simp [coe_sixTorusS, coe_HSL, Matrix.mul_apply, Fin.sum_univ_two])

theorem map_sixTorusP (σ : K →+* K) {ω : K} (hω : ω + σ ω = 1) :
    Matrix.SpecialLinearGroup.map σ (sixTorusP ω) = sixTorusP ω * sixTorusS := by
  have h2 : (2 : K) = 0 := sixTorus_two
  have hσω : σ ω = ω + 1 := by linear_combination hω - ω * h2
  refine SL2_ext ?_ ?_ ?_ ?_
  · simp [coe_sixTorusP, coe_sixTorusS, Matrix.mul_apply, Fin.sum_univ_two, hσω]
  · simp only [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply,
      Matrix.SpecialLinearGroup.coe_mul, coe_sixTorusP, coe_sixTorusS, Matrix.map_apply,
      Matrix.mul_apply, Fin.sum_univ_two]
    simp [hσω]
    linear_combination h2
  · simp [coe_sixTorusP, coe_sixTorusS, Matrix.mul_apply, Fin.sum_univ_two]
  · simp [coe_sixTorusP, coe_sixTorusS, Matrix.mul_apply, Fin.sum_univ_two]

end SL2

section Words

variable (K : Type) [Field K]

@[expose] def sixTorusM : Fin 4 → ModGL TwistTag.E6.tag K :=
  ![weylElt TwistTag.E6.tag K ⟨0, by decide⟩ 1 * weylElt TwistTag.E6.tag K ⟨5, by decide⟩ 1,
    weylElt TwistTag.E6.tag K ⟨2, by decide⟩ 1 * weylElt TwistTag.E6.tag K ⟨4, by decide⟩ 1,
    weylElt TwistTag.E6.tag K ⟨3, by decide⟩ 1, weylElt TwistTag.E6.tag K ⟨1, by decide⟩ 1]

@[expose] def sixTorusH : Fin 4 → ModGL TwistTag.E6.tag K :=
  ![1, sixTorusM K 1, sixTorusM K 0 * sixTorusM K 1,
    sixTorusM K 3 * sixTorusM K 2 * sixTorusM K 1 * sixTorusM K 2 * sixTorusM K 3 *
      sixTorusM K 0 * sixTorusM K 1]

@[expose] def sixTorusWord : Fin 4 → List (Fin TwistTag.E6.tag.rank) :=
  ![[], [⟨2, by decide⟩, ⟨4, by decide⟩],
    [⟨0, by decide⟩, ⟨5, by decide⟩, ⟨2, by decide⟩, ⟨4, by decide⟩],
    [⟨1, by decide⟩, ⟨3, by decide⟩, ⟨2, by decide⟩, ⟨4, by decide⟩, ⟨3, by decide⟩,
      ⟨1, by decide⟩, ⟨0, by decide⟩, ⟨5, by decide⟩, ⟨2, by decide⟩, ⟨4, by decide⟩]]

theorem sixTorusH_eq (j : Fin 4) :
    sixTorusH K j = ((sixTorusWord j).map fun i => weylElt TwistTag.E6.tag K i 1).prod := by
  fin_cases j <;> simp [sixTorusH, sixTorusM, sixTorusWord, mul_assoc]

@[expose] def sixTorusRoot : Fin 4 → Fin TwistTag.E6.tag.rank → ℤ :=
  ![Pi.single ⟨3, by decide⟩ 1, ![0, 0, 1, 1, 1, 0], ![1, 0, 1, 1, 1, 1], ![1, 2, 2, 3, 2, 1]]

theorem sixTorus_foldr_root : ∀ j : Fin 4,
    (sixTorusWord j).foldr (reflect TwistTag.E6.tag) (Pi.single ⟨3, by decide⟩ 1) =
        sixTorusRoot j ∧
      (sixTorusWord j).foldr (reflect TwistTag.E6.tag) (-Pi.single ⟨3, by decide⟩ 1) =
        -sixTorusRoot j := by
  decide +kernel

theorem sixTorus_isRoot (j : Fin 4) : IsRoot TwistTag.E6.tag (sixTorusRoot j) := by
  rw [← (sixTorus_foldr_root j).1]
  exact sixTorus_isRoot_foldr _ (isRoot_single _ _)

theorem sixTorus_orth : ∀ i j : Fin 4, i ≠ j →
    sixTorusRoot i ⬝ᵥ (TwistTag.E6.tag.symmetrizedCartan *ᵥ sixTorusRoot j) = 0 := by
  decide +kernel

@[expose] def sixTorusZWord : List (Fin TwistTag.E6.tag.rank) :=
  (sixTorusWord 0 ++ [⟨3, by decide⟩] ++ (sixTorusWord 0).reverse) ++
    (sixTorusWord 1 ++ [⟨3, by decide⟩] ++ (sixTorusWord 1).reverse) ++
    (sixTorusWord 2 ++ [⟨3, by decide⟩] ++ (sixTorusWord 2).reverse) ++
    (sixTorusWord 3 ++ [⟨3, by decide⟩] ++ (sixTorusWord 3).reverse)

theorem sixTorus_foldr_z : ∀ k : Fin TwistTag.E6.tag.rank,
    sixTorusZWord.foldr (reflect TwistTag.E6.tag) (Pi.single k 1) =
        -Pi.single (TwistTag.E6.perm k) 1 ∧
      sixTorusZWord.foldr (reflect TwistTag.E6.tag) (-Pi.single k 1) =
        Pi.single (TwistTag.E6.perm k) 1 := by
  decide +kernel

theorem sixTorus_perm_perm : ∀ k : Fin TwistTag.E6.tag.rank,
    TwistTag.E6.perm (TwistTag.E6.perm k) = k := by
  decide

variable {K}

@[expose] def sixTorusIota (ρ : SL2 K →* ModGL TwistTag.E6.tag K) (j : Fin 4) :
    SL2 K →* ModGL TwistTag.E6.tag K :=
  (MulAut.conj (sixTorusH K j)).toMonoidHom.comp ρ

theorem sixTorusIota_apply (ρ : SL2 K →* ModGL TwistTag.E6.tag K) (j : Fin 4) (B : SL2 K) :
    sixTorusIota ρ j B = sixTorusH K j * ρ B * (sixTorusH K j)⁻¹ :=
  rfl

@[expose] def sixTorusProd (ρ : SL2 K →* ModGL TwistTag.E6.tag K) (B : SL2 K) :
    ModGL TwistTag.E6.tag K :=
  sixTorusIota ρ 0 B * sixTorusIota ρ 1 B * sixTorusIota ρ 2 B * sixTorusIota ρ 3 B

theorem twistHom_sixTorusM (σ : K →+* K) (k : Fin 4) :
    twistHom TwistTag.E6 K σ (sixTorusM K k) = sixTorusM K k := by
  have h05 : Commute (weylElt TwistTag.E6.tag K ⟨5, by decide⟩ 1)
      (weylElt TwistTag.E6.tag K ⟨0, by decide⟩ 1) :=
    commute_weylElt_weylElt (a := ⟨0, by decide⟩) K (by decide) (by decide) (by decide) 1 1
  have h42 : Commute (weylElt TwistTag.E6.tag K ⟨4, by decide⟩ 1)
      (weylElt TwistTag.E6.tag K ⟨2, by decide⟩ 1) :=
    commute_weylElt_weylElt (a := ⟨1, by decide⟩) K (by decide) (by decide) (by decide) 1 1
  have p0 : TwistTag.E6.perm ⟨0, by decide⟩ = ⟨5, by decide⟩ := by decide
  have p5 : TwistTag.E6.perm ⟨5, by decide⟩ = ⟨0, by decide⟩ := by decide
  have p2 : TwistTag.E6.perm ⟨2, by decide⟩ = ⟨4, by decide⟩ := by decide
  have p4 : TwistTag.E6.perm ⟨4, by decide⟩ = ⟨2, by decide⟩ := by decide
  have p3 : TwistTag.E6.perm ⟨3, by decide⟩ = ⟨3, by decide⟩ := by decide
  have p1 : TwistTag.E6.perm ⟨1, by decide⟩ = ⟨1, by decide⟩ := by decide
  fin_cases k
  · change twistHom TwistTag.E6 K σ (weylElt TwistTag.E6.tag K ⟨0, by decide⟩ 1 *
      weylElt TwistTag.E6.tag K ⟨5, by decide⟩ 1) = _
    rw [map_mul, twistHom_weylElt_one, twistHom_weylElt_one, p0, p5]
    exact h05.eq
  · change twistHom TwistTag.E6 K σ (weylElt TwistTag.E6.tag K ⟨2, by decide⟩ 1 *
      weylElt TwistTag.E6.tag K ⟨4, by decide⟩ 1) = _
    rw [map_mul, twistHom_weylElt_one, twistHom_weylElt_one, p2, p4]
    exact h42.eq
  · change twistHom TwistTag.E6 K σ (weylElt TwistTag.E6.tag K ⟨3, by decide⟩ 1) = _
    rw [twistHom_weylElt_one, p3]
    rfl
  · change twistHom TwistTag.E6 K σ (weylElt TwistTag.E6.tag K ⟨1, by decide⟩ 1) = _
    rw [twistHom_weylElt_one, p1]
    rfl

theorem sixTorusH_zero : sixTorusH K 0 = 1 := by
  rw [sixTorusH, Matrix.cons_val_zero]

theorem sixTorusH_one : sixTorusH K 1 = sixTorusM K 1 := by
  rw [sixTorusH, Matrix.cons_val_one, Matrix.cons_val_zero]

theorem sixTorusH_two : sixTorusH K 2 = sixTorusM K 0 * sixTorusM K 1 := by
  rw [sixTorusH, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]

theorem sixTorusH_three : sixTorusH K 3 = sixTorusM K 3 * sixTorusM K 2 * sixTorusM K 1 *
    sixTorusM K 2 * sixTorusM K 3 * sixTorusM K 0 * sixTorusM K 1 := by
  rw [sixTorusH, Matrix.cons_val_three, Matrix.tail_cons, Matrix.tail_cons, Matrix.head_cons]

theorem twistHom_sixTorusH (σ : K →+* K) (j : Fin 4) :
    twistHom TwistTag.E6 K σ (sixTorusH K j) = sixTorusH K j := by
  fin_cases j
  · exact (show twistHom TwistTag.E6 K σ (sixTorusH K 0) = sixTorusH K 0 by
      rw [sixTorusH_zero, map_one])
  · exact (show twistHom TwistTag.E6 K σ (sixTorusH K 1) = sixTorusH K 1 by
      rw [sixTorusH_one, twistHom_sixTorusM])
  · exact (show twistHom TwistTag.E6 K σ (sixTorusH K 2) = sixTorusH K 2 by
      rw [sixTorusH_two, map_mul, twistHom_sixTorusM, twistHom_sixTorusM])
  · exact (show twistHom TwistTag.E6 K σ (sixTorusH K 3) = sixTorusH K 3 by
      rw [sixTorusH_three]
      simp only [map_mul, twistHom_sixTorusM])

end Words

section Iota

variable {K : Type} [Field K] [CharP K 2] {ρ : SL2 K →* ModGL TwistTag.E6.tag K}

theorem sixTorusIota_uSL (hρu : ∀ c, ρ (uSL c) = xUnit TwistTag.E6.tag K ⟨3, by decide⟩ c)
    (j : Fin 4) (c : K) :
    sixTorusIota ρ j (uSL c) = pinnedX TwistTag.E6.tag K (sixTorusRoot j) c := by
  rw [sixTorusIota_apply, hρu, ← pinnedX_single, sixTorusH_eq,
    sixTorus_conj_word sixTorus_two _ (isRoot_single _ _), (sixTorus_foldr_root j).1]

theorem sixTorusIota_vSL (hρv : ∀ c, ρ (vSL c) = yUnit TwistTag.E6.tag K ⟨3, by decide⟩ c)
    (j : Fin 4) (c : K) :
    sixTorusIota ρ j (vSL c) = pinnedX TwistTag.E6.tag K (-sixTorusRoot j) c := by
  rw [sixTorusIota_apply, hρv, ← pinnedX_neg_single, sixTorusH_eq,
    sixTorus_conj_word sixTorus_two _ (isRoot_neg_single _ _), (sixTorus_foldr_root j).2]

variable (hρu : ∀ c, ρ (uSL c) = xUnit TwistTag.E6.tag K ⟨3, by decide⟩ c)
  (hρv : ∀ c, ρ (vSL c) = yUnit TwistTag.E6.tag K ⟨3, by decide⟩ c)

include hρu hρv in
theorem commute_sixTorusIota {i j : Fin 4} (hij : i ≠ j) (A B : SL2 K) :
    Commute (sixTorusIota ρ i A) (sixTorusIota ρ j B) := by
  have horth := sixTorus_orth i j hij
  refine sixTorus_commute_of_gen _ _ ?_ A B
  rintro _ (⟨c, rfl⟩ | ⟨c, rfl⟩) _ (⟨d, rfl⟩ | ⟨d, rfl⟩)
  · rw [sixTorusIota_uSL hρu, sixTorusIota_uSL hρu]
    exact commute_pinnedX_of_rootForm_eq_zero K (sixTorus_isRoot i) (sixTorus_isRoot j) horth c d
  · rw [sixTorusIota_uSL hρu, sixTorusIota_vSL hρv]
    exact commute_pinnedX_of_rootForm_eq_zero K (sixTorus_isRoot i) (IsRoot.neg (sixTorus_isRoot j))
      (by rw [mulVec_neg, dotProduct_neg, horth, neg_zero]) c d
  · rw [sixTorusIota_vSL hρv, sixTorusIota_uSL hρu]
    exact commute_pinnedX_of_rootForm_eq_zero K (IsRoot.neg (sixTorus_isRoot i)) (sixTorus_isRoot j)
      (by rw [neg_dotProduct, horth, neg_zero]) c d
  · rw [sixTorusIota_vSL hρv, sixTorusIota_vSL hρv]
    exact commute_pinnedX_of_rootForm_eq_zero K (IsRoot.neg (sixTorus_isRoot i))
      (IsRoot.neg (sixTorus_isRoot j))
      (by rw [neg_dotProduct, mulVec_neg, dotProduct_neg, horth, neg_neg]) c d

include hρu hρv in
theorem sixTorusProd_mul (A B : SL2 K) :
    sixTorusProd ρ (A * B) = sixTorusProd ρ A * sixTorusProd ρ B := by
  have hc : ∀ i j : Fin 4, i ≠ j → ∀ A B : SL2 K,
      Commute (sixTorusIota ρ i A) (sixTorusIota ρ j B) :=
    fun i j h => commute_sixTorusIota hρu hρv h
  simp only [sixTorusProd, map_mul, mul_assoc]
  rw [(hc 0 1 (by decide) B A).left_comm, (hc 1 2 (by decide) B A).left_comm,
    (hc 0 2 (by decide) B A).left_comm, (hc 2 3 (by decide) B A).left_comm,
    (hc 1 3 (by decide) B A).left_comm, (hc 0 3 (by decide) B A).left_comm]

omit [CharP K 2] in
include hρu hρv in
theorem twistHom_comp_rho (σ : K →+* K) :
    (twistHom TwistTag.E6 K σ).comp ρ = ρ.comp (Matrix.SpecialLinearGroup.map σ) := by
  have hp : TwistTag.E6.perm ⟨3, by decide⟩ = ⟨3, by decide⟩ := by decide
  refine sixTorus_hom_ext (fun c => ?_) (fun c => ?_)
  · rw [MonoidHom.comp_apply, MonoidHom.comp_apply, hρu, twistHom_xUnit, map_uSL, hρu, hp]
  · rw [MonoidHom.comp_apply, MonoidHom.comp_apply, hρv, twistHom_yUnit, map_vSL, hρv, hp]

omit [CharP K 2] in
include hρu hρv in
theorem twistHom_sixTorusProd (σ : K →+* K) (B : SL2 K) :
    twistHom TwistTag.E6 K σ (sixTorusProd ρ B) =
      sixTorusProd ρ (Matrix.SpecialLinearGroup.map σ B) := by
  have h : ∀ j, twistHom TwistTag.E6 K σ (sixTorusIota ρ j B) =
      sixTorusIota ρ j (Matrix.SpecialLinearGroup.map σ B) := fun j => by
    rw [sixTorusIota_apply, sixTorusIota_apply, map_mul, map_mul, map_inv, twistHom_sixTorusH,
      ← MonoidHom.comp_apply (twistHom TwistTag.E6 K σ) ρ, twistHom_comp_rho hρu hρv σ,
      MonoidHom.comp_apply]
  simp only [sixTorusProd, map_mul, h]

omit [CharP K 2] in
include hρu hρv in
theorem sixTorus_rho_WSL : ρ WSL = weylElt TwistTag.E6.tag K ⟨3, by decide⟩ 1 := by
  rw [sixTorus_WSL_eq, map_mul, map_mul, hρu, hρv, CFSG.Blueprint.Chevalley.weylElt_eq_xUnit_mul]
  simp only [inv_one, Units.val_one]

include hρu hρv in
theorem sixTorusZ_eq :
    sixTorusProd ρ sixTorusS = (sixTorusZWord.map fun i => weylElt TwistTag.E6.tag K i 1).prod := by
  have h : ∀ j, sixTorusIota ρ j sixTorusS =
      ((sixTorusWord j).map fun i => weylElt TwistTag.E6.tag K i 1).prod *
        weylElt TwistTag.E6.tag K ⟨3, by decide⟩ 1 *
          ((sixTorusWord j).reverse.map fun i => weylElt TwistTag.E6.tag K i 1).prod := fun j => by
    rw [sixTorusIota_apply, sixTorusS_eq_WSL, sixTorus_rho_WSL hρu hρv, sixTorusH_eq,
      sixTorus_list_prod_inv sixTorus_two]
  rw [sixTorusProd, h, h, h, h, sixTorusZWord]
  simp only [List.map_append, List.prod_append, List.map_cons, List.map_nil, List.prod_cons,
    List.prod_nil, mul_one, mul_assoc]

include hρu hρv in
theorem sixTorusZ_conj_twistHom_xUnit (σ : K →+* K) (k : Fin TwistTag.E6.tag.rank) (c : K) :
    sixTorusProd ρ sixTorusS * twistHom TwistTag.E6 K σ (xUnit TwistTag.E6.tag K k c) *
        (sixTorusProd ρ sixTorusS)⁻¹ = yUnit TwistTag.E6.tag K k (σ c) := by
  rw [twistHom_xUnit, sixTorusZ_eq hρu hρv, ← pinnedX_single,
    sixTorus_conj_word sixTorus_two _ (isRoot_single _ _), (sixTorus_foldr_z _).1,
    sixTorus_perm_perm, pinnedX_neg_single]

include hρu hρv in
theorem sixTorusZ_conj_twistHom_yUnit (σ : K →+* K) (k : Fin TwistTag.E6.tag.rank) (c : K) :
    sixTorusProd ρ sixTorusS * twistHom TwistTag.E6 K σ (yUnit TwistTag.E6.tag K k c) *
        (sixTorusProd ρ sixTorusS)⁻¹ = xUnit TwistTag.E6.tag K k (σ c) := by
  rw [twistHom_yUnit, sixTorusZ_eq hρu hρv, ← pinnedX_neg_single,
    sixTorus_conj_word sixTorus_two _ (isRoot_neg_single _ _), (sixTorus_foldr_z _).2,
    sixTorus_perm_perm, pinnedX_single]

include hρu hρv in
theorem sixTorusZ_conj_twistHom_rankOneHom (σ : K →+* K) (k : Fin TwistTag.E6.tag.rank)
    (B : SL2 K) :
    sixTorusProd ρ sixTorusS * twistHom TwistTag.E6 K σ (rankOneHom TwistTag.E6 K k B) *
        (sixTorusProd ρ sixTorusS)⁻¹ =
      rankOneHom TwistTag.E6 K k (sixTorusS * Matrix.SpecialLinearGroup.map σ B * sixTorusS⁻¹) := by
  set z := sixTorusProd ρ sixTorusS
  have h : (MulAut.conj z).toMonoidHom.comp
      ((twistHom TwistTag.E6 K σ).comp (rankOneHom TwistTag.E6 K k)) =
      (rankOneHom TwistTag.E6 K k).comp ((MulAut.conj sixTorusS).toMonoidHom.comp
        (Matrix.SpecialLinearGroup.map σ)) := by
    refine sixTorus_hom_ext (fun c => ?_) (fun c => ?_)
    · change z * twistHom TwistTag.E6 K σ (rankOneHom TwistTag.E6 K k (uSL c)) * z⁻¹ =
        rankOneHom TwistTag.E6 K k (sixTorusS * Matrix.SpecialLinearGroup.map σ (uSL c) *
          sixTorusS⁻¹)
      rw [rankOneHom_uSL, sixTorusZ_conj_twistHom_xUnit hρu hρv, map_uSL, sixTorusS_conj_uSL,
        rankOneHom_vSL]
    · change z * twistHom TwistTag.E6 K σ (rankOneHom TwistTag.E6 K k (vSL c)) * z⁻¹ =
        rankOneHom TwistTag.E6 K k (sixTorusS * Matrix.SpecialLinearGroup.map σ (vSL c) *
          sixTorusS⁻¹)
      rw [rankOneHom_vSL, sixTorusZ_conj_twistHom_yUnit hρu hρv, map_vSL, sixTorusS_conj_vSL,
        rankOneHom_uSL]
  exact DFunLike.congr_fun h B

include hρu hρv in
theorem sixTorusZ_conj_twistHom_torusElt (σ : K →+* K) (k : Fin TwistTag.E6.tag.rank) (t : Kˣ) :
    sixTorusProd ρ sixTorusS * twistHom TwistTag.E6 K σ (torusElt TwistTag.E6.tag K k t) *
        (sixTorusProd ρ sixTorusS)⁻¹ =
      torusElt TwistTag.E6.tag K k (Units.map σ.toMonoidHom t)⁻¹ := by
  rw [← rankOneHom_HSL (t := TwistTag.E6), sixTorusZ_conj_twistHom_rankOneHom hρu hρv, map_HSL,
    sixTorusS_conj_HSL, rankOneHom_HSL]

include hρu hρv in
theorem sixTorusZ_conj_twistHom_weylElt (σ : K →+* K) (k : Fin TwistTag.E6.tag.rank) :
    sixTorusProd ρ sixTorusS * twistHom TwistTag.E6 K σ (weylElt TwistTag.E6.tag K k 1) *
        (sixTorusProd ρ sixTorusS)⁻¹ = weylElt TwistTag.E6.tag K k 1 := by
  rw [← rankOneHom_WSL (t := TwistTag.E6), sixTorusZ_conj_twistHom_rankOneHom hρu hρv, map_WSL,
    ← sixTorusS_eq_WSL, mul_inv_cancel_right]

end Iota

section Fixed

variable {K : Type} [Field K] [CharP K 2] {ρ : SL2 K →* ModGL TwistTag.E6.tag K}
  (hρu : ∀ c, ρ (uSL c) = xUnit TwistTag.E6.tag K ⟨3, by decide⟩ c)
  (hρv : ∀ c, ρ (vSL c) = yUnit TwistTag.E6.tag K ⟨3, by decide⟩ c)

omit [CharP K 2] in
include hρu hρv in
theorem sixTorus_rho_mem (B : SL2 K) : ρ B ∈ adjointGroup TwistTag.E6.tag K := by
  have hle : Subgroup.closure (Set.range (uSL (K := K)) ∪ Set.range (vSL (K := K))) ≤
      (adjointGroup TwistTag.E6.tag K).comap ρ := by
    refine (Subgroup.closure_le _).2 ?_
    rintro _ (⟨c, rfl⟩ | ⟨c, rfl⟩)
    · show ρ (uSL c) ∈ adjointGroup TwistTag.E6.tag K
      rw [hρu]
      exact xUnit_mem_adjointGroup _ _
    · show ρ (vSL c) ∈ adjointGroup TwistTag.E6.tag K
      rw [hρv]
      exact yUnit_mem_adjointGroup _ _
  have hS : Subgroup.closure (Set.range (uSL (K := K)) ∪ Set.range (vSL (K := K))) = ⊤ :=
    CFSG.LocalAnalysis.ComponentInitial.sl2_closure_upper_lower (K := K)
  exact hle (hS ▸ Subgroup.mem_top B)

omit [CharP K 2] in
theorem sixTorus_word_mem (ω : List (Fin TwistTag.E6.tag.rank)) :
    (ω.map fun i => weylElt TwistTag.E6.tag K i 1).prod ∈ adjointGroup TwistTag.E6.tag K :=
  list_prod_mem fun x hx => by
    obtain ⟨i, -, rfl⟩ := List.mem_map.1 hx
    exact weylElt_mem_adjointGroup i 1

omit [CharP K 2] in
include hρu hρv in
theorem sixTorusProd_mem (B : SL2 K) :
    sixTorusProd ρ B ∈ adjointGroup TwistTag.E6.tag K := by
  have h : ∀ j, sixTorusIota ρ j B ∈ adjointGroup TwistTag.E6.tag K := fun j => by
    rw [sixTorusIota_apply, sixTorusH_eq]
    exact mul_mem (mul_mem (sixTorus_word_mem _) (sixTorus_rho_mem hρu hρv B))
      (inv_mem (sixTorus_word_mem _))
  exact mul_mem (mul_mem (mul_mem (h 0) (h 1)) (h 2)) (h 3)

include hρu hρv in
theorem sixTorus_z_eq (σ : K →+* K) {ω : K} (hω : ω + σ ω = 1) :
    sixTorusProd ρ sixTorusS = sixTorusProd ρ (sixTorusP ω)⁻¹ *
      (twistHom TwistTag.E6 K σ (sixTorusProd ρ (sixTorusP ω)⁻¹))⁻¹ := by
  let Φ : SL2 K →* ModGL TwistTag.E6.tag K :=
    MonoidHom.mk' (sixTorusProd ρ) (sixTorusProd_mul hρu hρv)
  have hΦ : ∀ B, sixTorusProd ρ B = Φ B := fun B => rfl
  rw [twistHom_sixTorusProd hρu hρv, map_inv, map_sixTorusP σ hω, hΦ, hΦ, hΦ, ← map_inv,
    ← map_mul, inv_inv, ← mul_assoc, inv_mul_cancel, one_mul]

include hρu hρv in
theorem sixTorus_mem_fix_iff (σ : K →+* K) {ω : K} (hω : ω + σ ω = 1)
    (x : ModGL TwistTag.E6.tag K) :
    (x ∈ adjointGroup TwistTag.E6.tag K ∧ sixTorusProd ρ sixTorusS *
        twistHom TwistTag.E6 K σ x * (sixTorusProd ρ sixTorusS)⁻¹ = x) ↔
      x ∈ (twistedFixedGroup TwistTag.E6 K σ).map
        (MulAut.conj (sixTorusProd ρ (sixTorusP ω)⁻¹)).toMonoidHom := by
  set g := sixTorusProd ρ (sixTorusP ω)⁻¹ with hgdef
  have hg : g ∈ adjointGroup TwistTag.E6.tag K := sixTorusProd_mem hρu hρv _
  rw [sixTorus_z_eq hρu hρv σ hω, ← hgdef]
  constructor
  · rintro ⟨hx, hfx⟩
    refine ⟨g⁻¹ * x * g, (mem_twistedFixedGroup_iff_twistHom _ _ _).2
      ⟨mul_mem (mul_mem (inv_mem hg) hx) hg, ?_⟩, ?_⟩
    · rw [map_mul, map_mul, map_inv]
      calc (twistHom TwistTag.E6 K σ g)⁻¹ * twistHom TwistTag.E6 K σ x *
            twistHom TwistTag.E6 K σ g =
          g⁻¹ * (g * (twistHom TwistTag.E6 K σ g)⁻¹ * twistHom TwistTag.E6 K σ x *
            (g * (twistHom TwistTag.E6 K σ g)⁻¹)⁻¹) * g := by group
        _ = g⁻¹ * x * g := by rw [hfx]
    · change g * (g⁻¹ * x * g) * g⁻¹ = x
      group
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨hyC, hFy⟩ := (mem_twistedFixedGroup_iff_twistHom _ _ _).1 hy
    refine ⟨?_, ?_⟩
    · show g * y * g⁻¹ ∈ adjointGroup TwistTag.E6.tag K
      exact mul_mem (mul_mem hg hyC) (inv_mem hg)
    · show g * (twistHom TwistTag.E6 K σ g)⁻¹ * twistHom TwistTag.E6 K σ (g * y * g⁻¹) *
        (g * (twistHom TwistTag.E6 K σ g)⁻¹)⁻¹ = g * y * g⁻¹
      rw [map_mul, map_mul, map_inv, hFy]
      group

end Fixed

section Torus

variable {K : Type} [Field K] {p : ℕ} [Fact p.Prime]

theorem sixTorus_prod_zpow {G : Type*} [CommGroup G] (a : G) {ι : Type*} [Fintype ι]
    (f : ι → ℤ) : ∏ i, a ^ f i = a ^ ∑ i, f i := by
  classical
  have h : ∀ s : Finset ι, ∏ i ∈ s, a ^ f i = a ^ ∑ i ∈ s, f i := fun s => by
    induction s using Finset.induction_on with
    | empty => simp
    | insert x s hx ih => rw [Finset.prod_insert hx, Finset.sum_insert hx, ih, _root_.zpow_add]
  exact h Finset.univ

theorem sixTorus_zpow_eq_iff {G : Type*} [Group G] {ζ : G} (hζ : orderOf ζ = p) (m n : ℤ) :
    ζ ^ m = ζ ^ n ↔ (m : ZMod p) = n := by
  rw [zpow_eq_zpow_iff_modEq, hζ, ZMod.intCast_eq_intCast_iff]

theorem sixTorus_sum_identity {n : ℕ} {R : Type*} [CommRing R] (a : Fin n → Fin n → R)
    (v : Fin n → R) (i l : Fin n) :
    ∑ j, v j * a j l + (∑ j, v j * a j i) * -a i l =
      ∑ j, (v - (∑ k, a k i * v k) • (Pi.single i 1 : Fin n → R)) j * a j l := by
  simp only [Pi.sub_apply, Pi.smul_apply, Pi.single_apply, smul_eq_mul, mul_ite, mul_one,
    mul_zero, sub_mul, ite_mul, zero_mul]
  rw [Finset.sum_sub_distrib, Finset.sum_ite_eq']
  simp only [Finset.mem_univ, ↓reduceIte]
  have hs : ∑ j, a j i * v j = ∑ j, v j * a j i := Finset.sum_congr rfl fun j _ => mul_comm _ _
  rw [hs]
  ring

@[expose] def sixTorusExp (v : Fin TwistTag.E6.tag.rank → ZMod p) (l : Fin TwistTag.E6.tag.rank) :
    ℤ :=
  ∑ j, ((v j).val : ℤ) * TwistTag.E6.tag.cartan j l

theorem sixTorusExp_cast (v : Fin TwistTag.E6.tag.rank → ZMod p) (l : Fin TwistTag.E6.tag.rank) :
    ((sixTorusExp v l : ℤ) : ZMod p) = ∑ j, v j * (TwistTag.E6.tag.cartan j l : ZMod p) := by
  simp only [sixTorusExp, Int.cast_sum, Int.cast_mul, Int.cast_natCast, ZMod.natCast_zmod_val]

@[expose] def sixTorusTheta (ζ : Kˣ) (v : Fin TwistTag.E6.tag.rank → ZMod p) :
    ModGL TwistTag.E6.tag K :=
  rootDiagUnit TwistTag.E6.tag fun l => ζ ^ sixTorusExp v l

omit [Fact p.Prime] in
theorem sixTorusTheta_eq (ζ : Kˣ) (v : Fin TwistTag.E6.tag.rank → ZMod p) :
    sixTorusTheta ζ v = ((List.finRange TwistTag.E6.tag.rank).map fun j =>
      torusElt TwistTag.E6.tag K j (ζ ^ (v j).val)).prod := by
  rw [list_prod_torusElt_eq_rootDiagUnit, sixTorusTheta]
  congr 1
  funext l
  simp only [cartanChar, sixTorusExp]
  rw [← sixTorus_prod_zpow]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [← zpow_natCast, ← _root_.zpow_mul]

variable {ζ : Kˣ} (hζ : orderOf ζ = p)
include hζ

theorem sixTorusTheta_add (v w : Fin TwistTag.E6.tag.rank → ZMod p) :
    sixTorusTheta ζ (v + w) = sixTorusTheta ζ v * sixTorusTheta ζ w := by
  rw [sixTorusTheta, sixTorusTheta, sixTorusTheta, ← rootDiagUnit_mul]
  congr 1
  funext l
  rw [Pi.mul_apply, ← _root_.zpow_add, sixTorus_zpow_eq_iff hζ, Int.cast_add, sixTorusExp_cast,
    sixTorusExp_cast, sixTorusExp_cast, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun j _ => by rw [Pi.add_apply, add_mul]

theorem sixTorusTheta_zero : sixTorusTheta ζ (0 : Fin TwistTag.E6.tag.rank → ZMod p) = 1 := by
  rw [sixTorusTheta, ← rootDiagUnit_one]
  congr 1
  funext l
  rw [Pi.one_apply, ← zpow_zero ζ, sixTorus_zpow_eq_iff hζ, sixTorusExp_cast]
  simp

theorem sixTorusTheta_single (k : Fin TwistTag.E6.tag.rank) :
    sixTorusTheta ζ (Pi.single k (1 : ZMod p)) = torusElt TwistTag.E6.tag K k ζ := by
  rw [sixTorusTheta, torusElt_eq_rootDiagUnit]
  congr 1
  funext l
  rw [sixTorus_zpow_eq_iff hζ, sixTorusExp_cast]
  simp [Pi.single_apply]

theorem sixTorusTheta_eq_one (hp3 : 3 < p) {v : Fin TwistTag.E6.tag.rank → ZMod p}
    (h : sixTorusTheta ζ v = 1) : v = 0 := by
  have h1 : (fun l => ζ ^ sixTorusExp v l) = 1 :=
    rootDiagUnit_injective (h.trans rootDiagUnit_one.symm)
  have h3 : v ᵥ* (TwistTag.E6.tag.cartan.map (Int.cast : ℤ → ZMod p)) = 0 := funext fun l => by
    have h2 := congrFun h1 l
    rw [Pi.one_apply, ← zpow_zero ζ, sixTorus_zpow_eq_iff hζ, Int.cast_zero,
      sixTorusExp_cast] at h2
    simpa [Matrix.vecMul, dotProduct] using h2
  refine Matrix.eq_zero_of_vecMul_eq_zero ?_ h3
  have hdet : (TwistTag.E6.tag.cartan.map (Int.cast : ℤ → ZMod p)).det = ((3 : ℕ) : ZMod p) := by
    have h4 := (Int.castRingHom (ZMod p)).map_det TwistTag.E6.tag.cartan
    rw [RingHom.mapMatrix_apply, Int.coe_castRingHom] at h4
    rw [← h4, show TwistTag.E6.tag.cartan.det = 3 from det_cartan_E6]
    simp
  rw [hdet, Ne, ZMod.natCast_eq_zero_iff]
  intro h5
  have := Nat.le_of_dvd (by norm_num) h5
  omega

theorem weylElt_conj_sixTorusTheta (i : Fin TwistTag.E6.tag.rank)
    (v : Fin TwistTag.E6.tag.rank → ZMod p) :
    weylElt TwistTag.E6.tag K i 1 * sixTorusTheta ζ v * (weylElt TwistTag.E6.tag K i 1)⁻¹ =
      sixTorusTheta ζ (v - (∑ j, (TwistTag.E6.tag.cartan j i : ZMod p) * v j) • Pi.single i 1) := by
  rw [sixTorusTheta, weylElt_conj_rootDiagUnit, sixTorusTheta]
  congr 1
  funext l
  rw [← _root_.zpow_mul, ← _root_.zpow_add, sixTorus_zpow_eq_iff hζ]
  push_cast
  rw [sixTorusExp_cast, sixTorusExp_cast, sixTorusExp_cast]
  exact sixTorus_sum_identity (fun j l => (TwistTag.E6.tag.cartan j l : ZMod p)) v i l

end Torus

section Reflections

variable {K : Type} [Field K]

theorem sixTorus_torusElt_pow {τ : Tag} (j : Fin τ.rank) (t : Kˣ) (n : ℕ) :
    torusElt τ K j (t ^ n) = torusElt τ K j t ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, torusElt_one]
  | succ n ih => rw [pow_succ, pow_succ, torusElt_mul, ih]

theorem sixTorus_weylElt_ne_one {τ : Tag} (k : Fin τ.rank) : weylElt τ K k 1 ≠ 1 := by
  intro h
  have h1 := weylElt_rootVec_single (τ := τ) (R := K) k 1
  rw [h, Units.val_one, Module.End.one_apply, inv_one, Units.val_one, one_pow, one_smul,
    rootVec_eq_single_of_isRoot (isRoot_single _ k),
    rootVec_eq_single_of_isRoot (isRoot_neg_single _ k)] at h1
  have h2 := congrArg Subtype.val (Sum.inr.inj ((Finsupp.single_left_inj one_ne_zero).1 h1))
  have h3 := congrFun h2 k
  simp at h3

theorem sixTorus_mem_of_involution {f : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = (2 ^ f) ^ 2)
    {σ : K →+* K} (hsurj : Function.Surjective σ) (g : ModGL TwistTag.E6.tag K)
    {x : ModGL TwistTag.E6.tag K}
    (hx : x ∈ (twistedFixedGroup TwistTag.E6 K σ).map (MulAut.conj g).toMonoidHom)
    (hx2 : x * x = 1) :
    x ∈ (graphFixedRootGroup TwistTag.E6 K σ).map (MulAut.conj g).toMonoidHom := by
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; positivity)
  obtain ⟨γ, hγ, rfl⟩ := Subgroup.mem_map.1 hx
  have hγ2 : γ * γ = 1 := by
    have h : (MulAut.conj g).toMonoidHom (γ * γ) = (MulAut.conj g).toMonoidHom 1 := by
      rw [map_mul, hx2, map_one]
    exact (MulAut.conj g).injective h
  have hmem : γ ∈ (graphFixedTorus TwistTag.E6 K σ : Set (ModGL TwistTag.E6.tag K)) *
      (graphFixedRootGroup TwistTag.E6 K σ : Set (ModGL TwistTag.E6.tag K)) := by
    rw [← coe_twistedFixedGroup_eq_mul hsurj]
    exact hγ
  obtain ⟨h, hh, c, hc, rfl⟩ := Set.mem_mul.1 hmem
  obtain ⟨hhT, hhΓ⟩ := Subgroup.mem_inf.1 hh
  have hN := graphFixedRootGroup_subgroupOf_normal (t := TwistTag.E6) hsurj
  have hnorm : ∀ a ∈ twistedFixedGroup TwistTag.E6 K σ, ∀ b ∈ graphFixedRootGroup TwistTag.E6 K σ,
      a * b * a⁻¹ ∈ graphFixedRootGroup TwistTag.E6 K σ := fun a ha b hb =>
    Subgroup.mem_subgroupOf.1 (hN.conj_mem ⟨b, graphFixedRootGroup_le _ _ _ hb⟩
      (Subgroup.mem_subgroupOf.2 hb) ⟨a, ha⟩)
  have hh2 : h * h ∈ graphFixedRootGroup TwistTag.E6 K σ := by
    have e : h * h = (h * c * h⁻¹)⁻¹ * (h * c * (h * c)) * c⁻¹ := by group
    rw [e, hγ2, mul_one]
    exact mul_mem (inv_mem (hnorm h hhΓ c hc)) (inv_mem hc)
  obtain ⟨l, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hhT
  have hpow : rootDiagUnit TwistTag.E6.tag l ^ Nat.card K = rootDiagUnit TwistTag.E6.tag l := by
    have h1 : rootDiagUnit TwistTag.E6.tag l ^ (Nat.card K - 1) = 1 := by
      have e : rootDiagUnit TwistTag.E6.tag l ^ (Nat.card K - 1) =
          rootDiagUnitHom TwistTag.E6.tag K (l ^ (Nat.card K - 1)) :=
        (map_pow (rootDiagUnitHom TwistTag.E6.tag K) l (Nat.card K - 1)).symm
      have hl : l ^ (Nat.card K - 1) = 1 := funext fun i => by
        rw [Pi.pow_apply, Pi.one_apply, ← Nat.card_units]
        exact pow_card_eq_one'
      rw [e, hl, map_one]
    have hc1 : 1 ≤ Nat.card K := Nat.card_pos
    rw [show Nat.card K = Nat.card K - 1 + 1 by omega, pow_succ, h1, one_mul]
  obtain ⟨M, hM⟩ : Even (Nat.card K) := by
    rw [hK]
    exact Nat.even_pow.2 ⟨Nat.even_pow.2 ⟨even_two, by omega⟩, by norm_num⟩
  have hhC : rootDiagUnit TwistTag.E6.tag l ∈ graphFixedRootGroup TwistTag.E6 K σ := by
    rw [← hpow, hM, ← two_mul, pow_mul, sq]
    exact pow_mem hh2 M
  exact Subgroup.mem_map_of_mem _ (mul_mem hhC hc)

theorem sixTorus_exists_zeta {f p : ℕ} (hK : Nat.card K = (2 ^ f) ^ 2) (hp : p.Prime)
    (hpq : p ∣ 2 ^ f + 1) : ∃ ζ : Kˣ, orderOf ζ = p := by
  have : Fact p.Prime := ⟨hp⟩
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; positivity)
  refine exists_prime_orderOf_dvd_card' p ?_
  rw [Nat.card_units, hK]
  have e := Nat.sq_sub_sq (2 ^ f) 1
  rw [one_pow] at e
  rw [e]
  exact Dvd.dvd.mul_right hpq _

theorem sixTorus_sigma_sigma {f : ℕ} (hK : Nat.card K = (2 ^ f) ^ 2) {σ : K →+* K}
    (hσ : ∀ a, σ a = a ^ 2 ^ f) (c : K) : σ (σ c) = c := by
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; positivity)
  have : Fintype K := Fintype.ofFinite K
  rw [hσ, hσ, ← pow_mul, show 2 ^ f * 2 ^ f = Fintype.card K by
    rw [Fintype.card_eq_nat_card, hK, sq], FiniteField.pow_card]

theorem sixTorus_exists_omega [CharP K 2] {f : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = (2 ^ f) ^ 2)
    {σ : K →+* K} (hσ : ∀ a, σ a = a ^ 2 ^ f) : ∃ ω : K, ω + σ ω = 1 := by
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; positivity)
  have h2 : (2 : K) = 0 := sixTorus_two
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Kˣ)
  have hord : orderOf g = (2 ^ f) ^ 2 - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_units, hK]
  have hq : 2 ≤ 2 ^ f := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  have hξ : σ (g : K) ≠ g := by
    intro h
    rw [hσ] at h
    have h1 : g ^ (2 ^ f) = g := Units.ext (by rw [Units.val_pow_eq_pow_val]; exact h)
    have h3 : g ^ (2 ^ f - 1) = 1 := by
      have h4 : g ^ (2 ^ f - 1) * g = 1 * g := by
        rw [← pow_succ, Nat.sub_add_cancel (by omega), h1, one_mul]
      exact mul_right_cancel h4
    have h5 := Nat.le_of_dvd (by omega) (hord ▸ orderOf_dvd_of_pow_eq_one h3)
    have h6 : 2 * 2 ^ f ≤ 2 ^ f * 2 ^ f := Nat.mul_le_mul_right _ hq
    rw [sq] at h5
    omega
  set ξ : K := (g : K)
  have hsum : ξ + σ ξ ≠ 0 := fun h => hξ (by
    rw [add_eq_zero_iff_eq_neg, sixTorus_neg_eq h2] at h
    exact h.symm)
  refine ⟨ξ / (ξ + σ ξ), ?_⟩
  rw [map_div₀, map_add, sixTorus_sigma_sigma hK hσ, add_comm (σ ξ) ξ, ← add_div,
    div_self hsum]

end Reflections

theorem even_twisted_E6_nonsplit_six_torus_and_rational_reflections {f p : ℕ} (hf : 1 ≤ f)
    (K : Type) [Field K] [CharP K 2] (hK : Nat.card K = (2 ^ f) ^ 2) (σ : K →+* K)
    (hσ : ∀ a, σ a = a ^ 2 ^ f) (hp : p.Prime) (hp3 : 3 < p) (hpq : p ∣ 2 ^ f + 1)
    (ρ : SL2 K →* ModGL TwistTag.E6.tag K)
    (hρu : ∀ c, ρ (uSL c) = xUnit TwistTag.E6.tag K ⟨3, by decide⟩ c)
    (hρv : ∀ c, ρ (vSL c) = yUnit TwistTag.E6.tag K ⟨3, by decide⟩ c) :
    (∃ ζ : Kˣ, orderOf ζ = p) ∧ (∃ ω : K, ω + σ ω = 1) ∧
    ∀ ζ : Kˣ, orderOf ζ = p → ∀ ω : K, ω + σ ω = 1 →
      let g := sixTorusProd ρ (sixTorusP ω)⁻¹
      let z := sixTorusProd ρ sixTorusS
      let Γs := (twistedFixedGroup TwistTag.E6 K σ).map (MulAut.conj g).toMonoidHom
      let Cs := (graphFixedRootGroup TwistTag.E6 K σ).map (MulAut.conj g).toMonoidHom
      let D := Subgroup.closure (Set.range fun j => torusElt TwistTag.E6.tag K j ζ)
      z = g * (twistHom TwistTag.E6 K σ g)⁻¹ ∧
      (∀ x, (x ∈ adjointGroup TwistTag.E6.tag K ∧ z * twistHom TwistTag.E6 K σ x * z⁻¹ = x) ↔
        x ∈ Γs) ∧
      ⁅Γs, Γs⁆ = Cs ∧ D ≤ Cs ∧
      ∃ θ : Multiplicative (Fin TwistTag.E6.tag.rank → ZMod p) ≃* D,
        (∀ v, (θ (Multiplicative.ofAdd v) : ModGL TwistTag.E6.tag K) =
          ((List.finRange TwistTag.E6.tag.rank).map fun j =>
            torusElt TwistTag.E6.tag K j (ζ ^ (v j).val)).prod) ∧
        ∀ i, weylElt TwistTag.E6.tag K i 1 ∈ Cs ∧ orderOf (weylElt TwistTag.E6.tag K i 1) = 2 ∧
          (∀ x ∈ D, weylElt TwistTag.E6.tag K i 1 * x * (weylElt TwistTag.E6.tag K i 1)⁻¹ ∈ D) ∧
          ∀ v, weylElt TwistTag.E6.tag K i 1 * (θ (Multiplicative.ofAdd v) :
              ModGL TwistTag.E6.tag K) * (weylElt TwistTag.E6.tag K i 1)⁻¹ =
            (θ (Multiplicative.ofAdd
              (v - (∑ j, (TwistTag.E6.tag.cartan j i : ZMod p) * v j) •
                (Pi.single i 1 : Fin TwistTag.E6.tag.rank → ZMod p))) :
              ModGL TwistTag.E6.tag K) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have h2 : (2 : K) = 0 := sixTorus_two
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; positivity)
  have hsurj : Function.Surjective σ := Finite.surjective_of_injective σ.injective
  refine ⟨sixTorus_exists_zeta hK hp hpq, sixTorus_exists_omega hf hK hσ, fun ζ hζ ω hω => ?_⟩
  intro g z Γs Cs D
  have hfix : ∀ x, (x ∈ adjointGroup TwistTag.E6.tag K ∧
      z * twistHom TwistTag.E6 K σ x * z⁻¹ = x) ↔ x ∈ Γs :=
    sixTorus_mem_fix_iff hρu hρv σ hω
  have hder : ⁅Γs, Γs⁆ = Cs := by
    rw [← Subgroup.map_commutator,
      (finite_fixed_root_group_perfect TwistTag.E6 Nat.prime_two hf K hK σ hσ).2.2.1]
  have hσt : ∀ t : Kˣ, t ^ p = 1 → Units.map σ.toMonoidHom t = t⁻¹ := fun t ht => by
    obtain ⟨m, hm⟩ := hpq
    have h1 : t ^ (2 ^ f) * t = 1 := by rw [← pow_succ, hm, pow_mul, ht, one_pow]
    refine Units.ext ?_
    change σ (t : K) = ((t⁻¹ : Kˣ) : K)
    rw [hσ, ← Units.val_pow_eq_pow_val, eq_inv_of_mul_eq_one_left h1]
  have hdΓ : ∀ k (t : Kˣ), t ^ p = 1 → torusElt TwistTag.E6.tag K k t ∈ Γs := fun k t ht =>
    (hfix _).1 ⟨torusElt_mem_adjointGroup k t,
      (sixTorusZ_conj_twistHom_torusElt hρu hρv σ k t).trans (by rw [hσt t ht, inv_inv])⟩
  have hnΓ : ∀ k, weylElt TwistTag.E6.tag K k 1 ∈ Γs := fun k =>
    (hfix _).1 ⟨weylElt_mem_adjointGroup k 1, sixTorusZ_conj_twistHom_weylElt hρu hρv σ k⟩
  have hζp : ζ ^ p = 1 := by
    rw [← hζ]
    exact pow_orderOf_eq_one ζ
  have hdC : ∀ k, torusElt TwistTag.E6.tag K k ζ ∈ Cs := by
    intro k
    obtain ⟨m, hm⟩ : Even (p + 1) := (hp.odd_of_ne_two (by omega)).add_one
    set s := ζ ^ m
    have hs2 : s * s = ζ := by rw [← pow_add, ← hm, pow_succ, hζp, one_mul]
    have hsp : s⁻¹ ^ p = 1 := by
      rw [inv_pow, ← pow_mul, mul_comm, pow_mul, hζp, one_pow, inv_one]
    have hcomm := Subgroup.commutator_mem_commutator (hnΓ k) (hdΓ k s⁻¹ hsp)
    rw [hder] at hcomm
    have hc : ⁅weylElt TwistTag.E6.tag K k 1, torusElt TwistTag.E6.tag K k s⁻¹⁆ =
        torusElt TwistTag.E6.tag K k ζ := by
      rw [commutatorElement_def, weylElt_one_mul_torusElt_mul_inv, Tag.cartan_self,
        torusElt_mul_comm k k s⁻¹, mul_inv_cancel_right, _root_.inv_zpow', neg_neg, zpow_ofNat,
        sq, hs2]
    rw [← hc]
    exact hcomm
  have hDC : D ≤ Cs := (Subgroup.closure_le _).2 (by rintro _ ⟨k, rfl⟩; exact hdC k)
  let Θ : Multiplicative (Fin TwistTag.E6.tag.rank → ZMod p) →* ModGL TwistTag.E6.tag K :=
    { toFun := fun v => sixTorusTheta ζ v.toAdd
      map_one' := sixTorusTheta_zero hζ
      map_mul' := fun v w => sixTorusTheta_add hζ v.toAdd w.toAdd }
  have hΘ : ∀ v, Θ (Multiplicative.ofAdd v) = sixTorusTheta ζ v := fun v => rfl
  have hΘinj : Function.Injective Θ := (injective_iff_map_eq_one Θ).2 fun v hv =>
    toAdd_eq_zero.1 (sixTorusTheta_eq_one hζ hp3 hv)
  have hΘrange : Θ.range = D := by
    refine le_antisymm ?_ ((Subgroup.closure_le _).2 ?_)
    · rintro _ ⟨v, rfl⟩
      change sixTorusTheta ζ v.toAdd ∈ D
      rw [sixTorusTheta_eq]
      refine list_prod_mem fun x hx => ?_
      obtain ⟨j, -, rfl⟩ := List.mem_map.1 hx
      rw [sixTorus_torusElt_pow]
      exact pow_mem (Subgroup.subset_closure
        (Set.mem_range_self (f := fun j => torusElt TwistTag.E6.tag K j ζ) j)) _
    · rintro _ ⟨j, rfl⟩
      exact MonoidHom.mem_range.2 ⟨Multiplicative.ofAdd
        (Pi.single j 1 : Fin TwistTag.E6.tag.rank → ZMod p), sixTorusTheta_single hζ j⟩
  let θ : Multiplicative (Fin TwistTag.E6.tag.rank → ZMod p) ≃* D :=
    (MonoidHom.ofInjective hΘinj).trans (MulEquiv.subgroupCongr hΘrange)
  have hθ : ∀ v, (θ v : ModGL TwistTag.E6.tag K) = Θ v := fun v => rfl
  refine ⟨sixTorus_z_eq hρu hρv σ hω, hfix, hder, hDC, θ, fun v => ?_, fun i => ?_⟩
  · rw [hθ, hΘ, sixTorusTheta_eq]
  refine ⟨sixTorus_mem_of_involution hf hK hsurj g (hnΓ i) ?_, ?_, ?_, fun v => ?_⟩
  · rw [weylElt_one_mul_self, sixTorus_units_neg_one h2, torusElt_one]
  · refine orderOf_eq_prime (p := 2) ?_ (sixTorus_weylElt_ne_one i)
    rw [sq, weylElt_one_mul_self, sixTorus_units_neg_one h2, torusElt_one]
  · intro x hx
    rw [← hΘrange] at hx ⊢
    obtain ⟨v, rfl⟩ := hx
    refine ⟨Multiplicative.ofAdd (v.toAdd - (∑ j, (TwistTag.E6.tag.cartan j i : ZMod p) *
      v.toAdd j) • (Pi.single i 1 : Fin TwistTag.E6.tag.rank → ZMod p)), ?_⟩
    exact (weylElt_conj_sixTorusTheta hζ i v.toAdd).symm
  · rw [hθ, hθ, hΘ, hΘ]
    exact weylElt_conj_sixTorusTheta hζ i v

end CFSG.RankThree.Chevalley
