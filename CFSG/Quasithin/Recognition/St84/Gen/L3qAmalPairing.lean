module

public import CFSG.Quasithin.Recognition.St84.Gen.L3qAmalLocal
public import CFSG.Quasithin.Recognition.St84.Gen.L3qAmalCoord

import CFSG.Quasithin.Recognition.St84.Gen.SL2Semilinear
import CFSG.ClassicalGroups.PCoreSection

public section

namespace CFSG.Quasithin.F112R.St84

open Matrix CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits

variable {G : Type} [Group G] [Finite G] {L1 L2 S : Subgroup G} {f : ℕ}

private def uMat {F : Type*} [Field F] (t : F) : Matrix (Fin 2) (Fin 2) F := !![1, t; 0, 1]

private lemma uMat_det {F : Type*} [Field F] (t : F) : (uMat t).det = 1 := by
  simp [uMat, Matrix.det_fin_two]

private def uSL {F : Type*} [Field F] (t : F) : Matrix.SpecialLinearGroup (Fin 2) F :=
  ⟨uMat t, uMat_det t⟩

private lemma coe_uSL {F : Type*} [Field F] (t : F) :
    (uSL t : Matrix (Fin 2) (Fin 2) F) = uMat t := rfl

private lemma uSL_injective {F : Type*} [Field F] : Function.Injective (uSL (F := F)) := by
  intro s t h
  have h' : uMat s = uMat t := congrArg Subtype.val h
  have := congrFun (congrFun h' 0) 1
  simpa [uMat] using this

private lemma uSL_mul {F : Type*} [Field F] (s t : F) : uSL s * uSL t = uSL (s + t) := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, coe_uSL, coe_uSL, coe_uSL]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [uMat, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

private lemma uSL_zero {F : Type*} [Field F] : uSL (0 : F) = 1 := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [uSL, uMat]

private lemma uMat_mulVec {F : Type*} [Field F] (t : F) (v : Fin 2 → F) :
    (uMat t).mulVec v = ![v 0 + t * v 1, v 1] := by
  funext i
  fin_cases i <;> simp [vecHead, vecTail, uMat, Matrix.mulVec, Fin.sum_univ_two]

private def fixedLine (F : Type*) [AddGroup F] : AddSubgroup (Fin 2 → F) where
  carrier := {v | v 1 = 0}
  zero_mem' := by simp
  add_mem' := by
    intro a b ha hb
    change a 1 = 0 at ha
    change b 1 = 0 at hb
    simp [ha, hb]
  neg_mem' := by
    intro a ha
    change a 1 = 0 at ha
    simp [ha]

private lemma card_fixedLine {F : Type*} [Field F] :
    Nat.card ↥(fixedLine F) = Nat.card F := by
  refine Nat.card_congr ?_
  refine
    { toFun := fun v => (v : Fin 2 → F) 0
      invFun := fun z => ⟨Pi.single (M := fun _ : Fin 2 => F) 0 z, ?_⟩
      left_inv := ?_
      right_inv := ?_ }
  · show Pi.single (M := fun _ : Fin 2 => F) 0 z 1 = 0
    simp
  · intro v
    apply Subtype.ext
    funext i
    fin_cases i
    · simp
    · show Pi.single (M := fun _ : Fin 2 => F) 0 ((v : Fin 2 → F) 0) 1 = (v : Fin 2 → F) 1
      rw [Pi.single_eq_of_ne (by decide : (1 : Fin 2) ≠ 0)]
      exact v.2.symm
  · intro z
    simp

private lemma eq_fixedLine_of_uInvariant {F : Type*} [Field F] [Finite F]
    (W : AddSubgroup (Fin 2 → F)) (hcard : Nat.card ↥W = Nat.card F)
    (hU : ∀ (t : F) (w : Fin 2 → F), w ∈ W → (uMat t).mulVec w ∈ W) :
    W = fixedLine F := by
  have hline_card : Nat.card ↥(fixedLine F) = Nat.card F := card_fixedLine
  have hsub : ∀ (t : F) (w : Fin 2 → F), w ∈ W → (uMat t).mulVec w - w ∈ W :=
    fun t w hw => W.sub_mem (hU t w hw) hw
  rcases em (∃ w ∈ W, w 1 ≠ 0) with ⟨w, hw, hw1⟩ | hnone
  · have hline_le : fixedLine F ≤ W := by
      intro v hv
      have hv1 : (v : Fin 2 → F) 1 = 0 := hv
      have hmem : (fun i : Fin 2 => if i = 0 then (v : Fin 2 → F) 0 else 0) ∈ W := by
        have h := hsub ((v : Fin 2 → F) 0 / w 1) w hw
        have heq : (uMat ((v : Fin 2 → F) 0 / w 1)).mulVec w - w =
            fun i : Fin 2 => if i = 0 then (v : Fin 2 → F) 0 else 0 := by
          funext i
          rw [uMat_mulVec]
          fin_cases i <;> simp [div_mul_cancel₀ _ hw1] <;> ring
        rwa [heq] at h
      have hv_eq : (v : Fin 2 → F) =
          fun i : Fin 2 => if i = 0 then (v : Fin 2 → F) 0 else 0 := by
        funext i
        fin_cases i <;> simp [hv1]
      rwa [hv_eq]
    have hEq : fixedLine F = W := by
      apply AddSubgroup.eq_of_le_of_card_ge hline_le
      rw [hcard, hline_card]
    have hwline : w ∈ fixedLine F := by rw [hEq]; exact hw
    exact absurd hwline hw1
  · have hle : W ≤ fixedLine F := by
      intro v hv
      by_contra hv1
      exact hnone ⟨v, hv, hv1⟩
    have hEq : W = fixedLine F := by
      apply AddSubgroup.eq_of_le_of_card_ge hle
      rw [hcard, hline_card]
    exact hEq

theorem L3qLocalData.map_pCoreOf_left_alpha_surjective (hH : Hyp111 L1 L2 S)
    (hD : L3qLocalData L1 L2 S f) (c₂ : VertexCoord L2 S (GaloisField 2 f))
    (t : GaloisField 2 f) :
    ∃ x : ↥(pCoreOf 2 L1),
      (c₂.α (Subgroup.inclusion (hH.pCoreOf_le_left.trans (hD.le_right hH)) x) :
        Matrix (Fin 2) (Fin 2) (GaloisField 2 f)) = !![1, t; 0, 1] := by
  classical
  let F := GaloisField 2 f
  have hf0 : f ≠ 0 := by have := hD.one_le; omega
  have hcardF : Nat.card F = 2 ^ f := GaloisField.card 2 f hf0
  let hQ : pCoreOf 2 L1 ≤ L2 := hH.pCoreOf_le_left.trans (hD.le_right hH)
  let ψ : ↥(pCoreOf 2 L1) →* Matrix.SpecialLinearGroup (Fin 2) F :=
    c₂.α.comp (Subgroup.inclusion hQ)
  have hker : ψ.ker = (pCoreOf 2 L1 ⊓ pCoreOf 2 L2).subgroupOf (pCoreOf 2 L1) := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    change c₂.α (Subgroup.inclusion hQ x) = 1 ↔ _
    rw [c₂.eq_one_iff, Subgroup.coe_inclusion]
    exact ⟨fun h => ⟨x.2, h⟩, fun h => h.2⟩
  have hkercard : Nat.card ψ.ker = 2 ^ f := by
    rw [hker]
    calc Nat.card ↥((pCoreOf 2 L1 ⊓ pCoreOf 2 L2).subgroupOf (pCoreOf 2 L1))
        = Nat.card ↥(pCoreOf 2 L1 ⊓ pCoreOf 2 L2) :=
          Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
      _ = 2 ^ f := hD.card_inf
  have hrangecard : Nat.card ψ.range = 2 ^ f := by
    have h := Subgroup.card_ker_mul_card_range ψ
    rw [hkercard, hD.card_left] at h
    have hpow : 2 ^ (2 * f) = 2 ^ f * 2 ^ f := by rw [← pow_add]; congr 1; omega
    rw [hpow] at h
    exact Nat.eq_of_mul_eq_mul_left (by positivity) h
  have hsub : (ψ.range : Set (Matrix.SpecialLinearGroup (Fin 2) F)) ⊆
      Set.range (uSL (F := F)) := by
    rintro A ⟨x, rfl⟩
    obtain ⟨s, hs⟩ := (c₂.mem_iff (Subgroup.inclusion hQ x)).mp
      (by simpa using hH.pCoreOf_le_left x.2)
    exact ⟨s, Subtype.ext (by
      show (uMat s : Matrix (Fin 2) (Fin 2) F) =
        ((c₂.α (Subgroup.inclusion hQ x)) : Matrix (Fin 2) (Fin 2) F)
      exact hs.symm)⟩
  have hrangecard' : Nat.card ↥(Set.range (uSL (F := F))) = 2 ^ f := by
    rw [Nat.card_coe_set_eq, Set.ncard_range_of_injective (uSL_injective (F := F)), hcardF]
  have heq : (ψ.range : Set (Matrix.SpecialLinearGroup (Fin 2) F)) =
      Set.range (uSL (F := F)) := by
    apply Set.eq_of_subset_of_ncard_le hsub
    · have h2 : (Set.range (uSL (F := F))).ncard =
          (ψ.range : Set (Matrix.SpecialLinearGroup (Fin 2) F)).ncard := by
        rw [Set.ncard_range_of_injective (uSL_injective (F := F)), hcardF]
        exact hrangecard.symm
      exact le_of_eq h2
  have hmem : uSL t ∈ ψ.range := by
    have h : uSL t ∈ (Set.range (uSL (F := F))) := Set.mem_range_self t
    rwa [← heq] at h
  obtain ⟨x, hx⟩ := hmem
  exact ⟨x, congrArg Subtype.val hx⟩

theorem L3qLocalData.map_pCoreOf_right_alpha (hH : Hyp111 L1 L2 S)
    (hD : L3qLocalData L1 L2 S f) (c₁ : VertexCoord L1 S (GaloisField 2 f))
    (y : ↥(pCoreOf 2 L2)) :
    ∃ t : GaloisField 2 f,
      (c₁.α (Subgroup.inclusion (hH.pCoreOf_le_right.trans (hD.le_left hH)) y) :
        Matrix (Fin 2) (Fin 2) (GaloisField 2 f)) = !![1, t; 0, 1] := by
  exact (c₁.mem_iff _).mp (by simpa using hH.pCoreOf_le_right y.2)

theorem L3qLocalData.mem_inf_iff_second_coord_right (hH : Hyp111 L1 L2 S)
    (hD : L3qLocalData L1 L2 S f) (c₂ : VertexCoord L2 S (GaloisField 2 f)) :
    ∀ y : ↥(pCoreOf 2 L2), (y : G) ∈ (pCoreOf 2 L1 ⊓ pCoreOf 2 L2) ↔
      Multiplicative.toAdd (c₂.β y) 1 = 0 := by
  classical
  let F := GaloisField 2 f
  have hf0 : f ≠ 0 := by have := hD.one_le; omega
  have hcardF : Nat.card F = 2 ^ f := GaloisField.card 2 f hf0
  let hQ : pCoreOf 2 L1 ≤ L2 := hH.pCoreOf_le_left.trans (hD.le_right hH)
  let W : AddSubgroup (Fin 2 → F) :=
    { carrier := {v | ∃ y : ↥(pCoreOf 2 L2),
        (y : G) ∈ (pCoreOf 2 L1 ⊓ pCoreOf 2 L2) ∧ Multiplicative.toAdd (c₂.β y) = v}
      zero_mem' := by
        refine ⟨1, ?_, ?_⟩
        · simp
        · simp
      add_mem' := by
        rintro a b ⟨y, hy, rfl⟩ ⟨z, hz, rfl⟩
        refine ⟨y * z, ?_, ?_⟩
        · simpa using Subgroup.mul_mem (pCoreOf 2 L1 ⊓ pCoreOf 2 L2) hy hz
        · rw [map_mul, toAdd_mul]
      neg_mem' := by
        rintro a ⟨y, hy, rfl⟩
        refine ⟨y⁻¹, ?_, ?_⟩
        · simpa using Subgroup.inv_mem (pCoreOf 2 L1 ⊓ pCoreOf 2 L2) hy
        · rw [map_inv, toAdd_inv] }
  have hWcard : Nat.card ↥W = 2 ^ f := by
    have himg : (W : Set (Fin 2 → F)) =
        (fun y : ↥(pCoreOf 2 L2) => Multiplicative.toAdd (c₂.β y)) ''
          (((pCoreOf 2 L1 ⊓ pCoreOf 2 L2).subgroupOf (pCoreOf 2 L2) :
            Subgroup ↥(pCoreOf 2 L2)) : Set ↥(pCoreOf 2 L2)) := by
      ext v
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact ⟨y, hy, rfl⟩
      · rintro ⟨y, hy, rfl⟩
        exact ⟨y, hy, rfl⟩
    have hinj : Function.Injective
        (fun y : ↥(pCoreOf 2 L2) => Multiplicative.toAdd (c₂.β y)) := by
      intro a b h
      exact c₂.β.injective (Multiplicative.toAdd.injective h)
    have h1 : (W : Set (Fin 2 → F)).ncard = 2 ^ f := by
      rw [himg, Set.ncard_image_of_injective _ hinj, ← Nat.card_coe_set_eq]
      calc Nat.card ↥((pCoreOf 2 L1 ⊓ pCoreOf 2 L2).subgroupOf (pCoreOf 2 L2))
          = Nat.card ↥(pCoreOf 2 L1 ⊓ pCoreOf 2 L2) :=
            Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv
        _ = 2 ^ f := hD.card_inf
    have h2 : Nat.card ↥W = (W : Set (Fin 2 → F)).ncard := rfl
    rw [h2]
    exact h1
  have hWinv : ∀ (t : F) (w : Fin 2 → F), w ∈ W → (uMat t).mulVec w ∈ W := by
    intro t w hw
    obtain ⟨y, hy, rfl⟩ := hw
    obtain ⟨x, hx⟩ := L3qLocalData.map_pCoreOf_left_alpha_surjective hH hD c₂ t
    let xL : ↥L2 := Subgroup.inclusion hQ x
    let v : ↥(pCoreOf 2 L2) :=
      ⟨(xL : G) * (y : G) * (xL : G)⁻¹,
        CFSG.ClassicalGroups.PCoreSection.conj_mem_pCoreOf xL.2 y.2⟩
    have hvQ1 : (v : G) ∈ pCoreOf 2 L1 :=
      Subgroup.mul_mem _ (Subgroup.mul_mem _ x.2 hy.1) (Subgroup.inv_mem _ x.2)
    have hvℓ : (v : G) ∈ (pCoreOf 2 L1 ⊓ pCoreOf 2 L2) := ⟨hvQ1, v.2⟩
    have hspec : c₂.α xL = uSL t := by
      apply Subtype.ext
      rw [coe_uSL]
      exact hx
    have heq : Multiplicative.toAdd (c₂.β v) =
        (uMat t).mulVec (Multiplicative.toAdd (c₂.β y)) := by
      have h := c₂.equivariant xL y v (by rfl)
      rwa [hspec] at h
    exact ⟨v, hvℓ, heq⟩
  have hWline : W = fixedLine F :=
    eq_fixedLine_of_uInvariant W (hWcard.trans hcardF.symm) hWinv
  intro y
  constructor
  · intro hy
    have hmem : Multiplicative.toAdd (c₂.β y) ∈ W := ⟨y, hy, rfl⟩
    rw [hWline] at hmem
    exact hmem
  · intro h0
    have hmem : Multiplicative.toAdd (c₂.β y) ∈ W := by
      rw [hWline]
      exact h0
    obtain ⟨z, hz, hzeq⟩ := hmem
    have hzy : z = y := by
      apply c₂.β.injective
      apply Multiplicative.toAdd.injective
      exact hzeq
    rwa [hzy] at hz

theorem L3qLocalData.mem_inf_iff_second_coord_left (hH : Hyp111 L1 L2 S)
    (hD : L3qLocalData L1 L2 S f) (c₁ : VertexCoord L1 S (GaloisField 2 f))
    (c₂ : VertexCoord L2 S (GaloisField 2 f)) :
    ∀ x : ↥(pCoreOf 2 L1), (x : G) ∈ (pCoreOf 2 L1 ⊓ pCoreOf 2 L2) ↔
      Multiplicative.toAdd (c₁.β x) 1 = 0 := by
  classical
  let F := GaloisField 2 f
  have hf0 : f ≠ 0 := by have := hD.one_le; omega
  have hcardF : Nat.card F = 2 ^ f := GaloisField.card 2 f hf0
  have hline₂ := L3qLocalData.mem_inf_iff_second_coord_right hH hD c₂
  have hcent₂ : ∀ z : ↥(pCoreOf 2 L2), (z : G) ∈ (pCoreOf 2 L1 ⊓ pCoreOf 2 L2) ↔
      ∀ s ∈ S, s * (z : G) = (z : G) * s := by
    intro z
    rw [hline₂ z]
    exact (c₂.mem_centralizer_iff (hD.le_right hH) z).symm
  let C : Subgroup ↥(pCoreOf 2 L1) :=
    { carrier := {x | Multiplicative.toAdd (c₁.β x) 1 = 0}
      one_mem' := by simp
      mul_mem' := by
        intro a b ha hb
        change Multiplicative.toAdd (c₁.β (a * b)) 1 = 0
        rw [map_mul, toAdd_mul, Pi.add_apply]
        rw [show Multiplicative.toAdd (c₁.β a) 1 = 0 from ha,
          show Multiplicative.toAdd (c₁.β b) 1 = 0 from hb, add_zero]
      inv_mem' := by
        intro a ha
        change Multiplicative.toAdd (c₁.β a⁻¹) 1 = 0
        rw [map_inv, toAdd_inv, Pi.neg_apply]
        rw [show Multiplicative.toAdd (c₁.β a) 1 = 0 from ha, neg_zero] }
  have hCcard : Nat.card ↥C = 2 ^ f := by
    have h1 : Nat.card ↥C = Nat.card ↥(fixedLine F) := by
      refine Nat.card_congr ?_
      refine
        { toFun := fun x => ⟨Multiplicative.toAdd (c₁.β x.1), x.2⟩
          invFun := fun v => ⟨c₁.β.symm (Multiplicative.ofAdd (v : Fin 2 → F)), ?_⟩
          left_inv := ?_
          right_inv := ?_ }
      · show Multiplicative.toAdd
          (c₁.β (c₁.β.symm (Multiplicative.ofAdd (v : Fin 2 → F)))) 1 = 0
        rw [MulEquiv.apply_symm_apply]
        exact v.2
      · intro x
        apply Subtype.ext
        simp
      · intro v
        apply Subtype.ext
        simp
    rw [h1, card_fixedLine, hcardF]
  have hℓle : (pCoreOf 2 L1 ⊓ pCoreOf 2 L2).subgroupOf (pCoreOf 2 L1) ≤ C := by
    intro x hx
    have hxℓ : (x : G) ∈ (pCoreOf 2 L1 ⊓ pCoreOf 2 L2) := hx
    have hcent : ∀ s ∈ S, s * (x : G) = (x : G) * s :=
      (hcent₂ ⟨(x : G), hxℓ.2⟩).mp hxℓ
    exact (c₁.mem_centralizer_iff (hD.le_left hH) x).mp hcent
  have hℓcard : Nat.card ↥((pCoreOf 2 L1 ⊓ pCoreOf 2 L2).subgroupOf (pCoreOf 2 L1)) =
      2 ^ f := by
    calc Nat.card ↥((pCoreOf 2 L1 ⊓ pCoreOf 2 L2).subgroupOf (pCoreOf 2 L1))
        = Nat.card ↥(pCoreOf 2 L1 ⊓ pCoreOf 2 L2) :=
          Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
      _ = 2 ^ f := hD.card_inf
  have heq : (pCoreOf 2 L1 ⊓ pCoreOf 2 L2).subgroupOf (pCoreOf 2 L1) = C := by
    apply Subgroup.eq_of_le_of_card_ge hℓle
    rw [hℓcard, hCcard]
  intro x
  have hx : (x : G) ∈ (pCoreOf 2 L1 ⊓ pCoreOf 2 L2) ↔ x ∈ C := by
    rw [← heq, Subgroup.mem_subgroupOf]
  exact hx

theorem L3qLocalData.commutator_mem_inf (hH : Hyp111 L1 L2 S)
    (hD : L3qLocalData L1 L2 S f) (x : ↥(pCoreOf 2 L1)) (y : ↥(pCoreOf 2 L2)) :
    (x : G) * (y : G) * (x : G)⁻¹ * (y : G)⁻¹ ∈ (pCoreOf 2 L1 ⊓ pCoreOf 2 L2) ∧
      (y : G) * (x : G) * (y : G)⁻¹ * (x : G)⁻¹ ∈
        (pCoreOf 2 L1 ⊓ pCoreOf 2 L2) ∧
      (x : G) * (y : G) * (x : G)⁻¹ * (y : G)⁻¹ =
        (y : G) * (x : G) * (y : G)⁻¹ * (x : G)⁻¹ := by
  have hQ1L2 : pCoreOf 2 L1 ≤ L2 := hH.pCoreOf_le_left.trans (hD.le_right hH)
  have hQ2L1 : pCoreOf 2 L2 ≤ L1 := hH.pCoreOf_le_right.trans (hD.le_left hH)
  have hz₂Q₂ : (x : G) * (y : G) * (x : G)⁻¹ * (y : G)⁻¹ ∈ pCoreOf 2 L2 := by
    have h1 : (x : G) * (y : G) * (x : G)⁻¹ ∈ pCoreOf 2 L2 :=
      (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 L2 (hQ1L2 x.2)) (y : G)).mp y.2
    exact Subgroup.mul_mem _ h1 (Subgroup.inv_mem _ y.2)
  have hz₁Q₁ : (y : G) * (x : G) * (y : G)⁻¹ * (x : G)⁻¹ ∈ pCoreOf 2 L1 := by
    have h1 : (y : G) * (x : G) * (y : G)⁻¹ ∈ pCoreOf 2 L1 :=
      (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 L1 (hQ2L1 y.2)) (x : G)).mp x.2
    exact Subgroup.mul_mem _ h1 (Subgroup.inv_mem _ x.2)
  have hinv : (x : G) * (y : G) * (x : G)⁻¹ * (y : G)⁻¹ =
      ((y : G) * (x : G) * (y : G)⁻¹ * (x : G)⁻¹)⁻¹ := by group
  refine ⟨⟨?_, hz₂Q₂⟩, ⟨hz₁Q₁, ?_⟩, ?_⟩
  · rw [hinv]; exact Subgroup.inv_mem _ hz₁Q₁
  · have h₂ : ((x : G) * (y : G) * (x : G)⁻¹ * (y : G)⁻¹)⁻¹ ∈ pCoreOf 2 L2 :=
      Subgroup.inv_mem _ hz₂Q₂
    rwa [hinv, inv_inv] at h₂
  · rw [hinv]
    exact inv_eq_of_mul_eq_one_right
      (by simpa [pow_two] using hD.isElemAbelian_left.2 _ hz₁Q₁)

theorem L3qLocalData.commutator_coord (hH : Hyp111 L1 L2 S)
    (hD : L3qLocalData L1 L2 S f) (c₁ : VertexCoord L1 S (GaloisField 2 f))
    (c₂ : VertexCoord L2 S (GaloisField 2 f))
    {x : ↥(pCoreOf 2 L1)} {y : ↥(pCoreOf 2 L2)}
    {σ τ : GaloisField 2 f}
    (hx : (c₂.α (Subgroup.inclusion (hH.pCoreOf_le_left.trans (hD.le_right hH)) x) :
      Matrix (Fin 2) (Fin 2) (GaloisField 2 f)) = !![1, σ; 0, 1])
    (hy : (c₁.α (Subgroup.inclusion (hH.pCoreOf_le_right.trans (hD.le_left hH)) y) :
      Matrix (Fin 2) (Fin 2) (GaloisField 2 f)) = !![1, τ; 0, 1])
    (z₁ : ↥(pCoreOf 2 L1)) (z₂ : ↥(pCoreOf 2 L2))
    (hz₁ : (z₁ : G) = (y : G) * (x : G) * (y : G)⁻¹ * (x : G)⁻¹)
    (hz₂ : (z₂ : G) = (x : G) * (y : G) * (x : G)⁻¹ * (y : G)⁻¹) :
    Multiplicative.toAdd (c₁.β z₁) =
        ![τ * (Multiplicative.toAdd (c₁.β x)) 1, 0] ∧
      Multiplicative.toAdd (c₂.β z₂) =
        ![σ * (Multiplicative.toAdd (c₂.β y)) 1, 0] ∧
      (z₁ : G) = (z₂ : G) := by
  have hQ1L2 : pCoreOf 2 L1 ≤ L2 := hH.pCoreOf_le_left.trans (hD.le_right hH)
  have hQ2L1 : pCoreOf 2 L2 ≤ L1 := hH.pCoreOf_le_right.trans (hD.le_left hH)
  refine ⟨?_, ?_, ?_⟩
  · exact c₁.commutator (s := Subgroup.inclusion hQ2L1 y) (x := x) (v := z₁) hy hz₁
  · exact c₂.commutator (s := Subgroup.inclusion hQ1L2 x) (x := y) (v := z₂) hx hz₂
  · have hmem := L3qLocalData.commutator_mem_inf hH hD x y
    rw [hz₁, hz₂]
    exact hmem.2.2.symm

private lemma inclQ1L2 (hH : Hyp111 L1 L2 S) (hD : L3qLocalData L1 L2 S f) :
    pCoreOf 2 L1 ≤ L2 :=
  hH.pCoreOf_le_left.trans (hD.le_right hH)

private lemma inclQ2L1 (hH : Hyp111 L1 L2 S) (hD : L3qLocalData L1 L2 S f) :
    pCoreOf 2 L2 ≤ L1 :=
  hH.pCoreOf_le_right.trans (hD.le_left hH)

private noncomputable def pairingLineElem (hH : Hyp111 L1 L2 S)
    (hD : L3qLocalData L1 L2 S f) (c₂ : VertexCoord L2 S (GaloisField 2 f))
    (w : GaloisField 2 f) : ↥(pCoreOf 2 L1 ⊓ pCoreOf 2 L2) :=
  ⟨(c₂.β.symm (Multiplicative.ofAdd ![w, 0]) : G), by
    refine (L3qLocalData.mem_inf_iff_second_coord_right hH hD c₂
      (c₂.β.symm (Multiplicative.ofAdd ![w, 0]))).mpr ?_
    simp⟩

private lemma pairingLineElem_coe (hH : Hyp111 L1 L2 S)
    (hD : L3qLocalData L1 L2 S f) (c₂ : VertexCoord L2 S (GaloisField 2 f))
    (w : GaloisField 2 f) :
    (⟨(pairingLineElem hH hD c₂ w : G), (pairingLineElem hH hD c₂ w).2.2⟩ :
      ↥(pCoreOf 2 L2)) = c₂.β.symm (Multiplicative.ofAdd ![w, 0]) :=
  Subtype.ext rfl

private lemma pairingLineElem_beta (hH : Hyp111 L1 L2 S)
    (hD : L3qLocalData L1 L2 S f) (c₂ : VertexCoord L2 S (GaloisField 2 f))
    (w : GaloisField 2 f) :
    c₂.β ⟨(pairingLineElem hH hD c₂ w : G), (pairingLineElem hH hD c₂ w).2.2⟩ =
      Multiplicative.ofAdd ![w, 0] := by
  rw [pairingLineElem_coe]
  simp

private lemma pairingLineElem_eq_of_coord (hH : Hyp111 L1 L2 S)
    (hD : L3qLocalData L1 L2 S f) (c₂ : VertexCoord L2 S (GaloisField 2 f))
    {w : GaloisField 2 f} {z : ↥(pCoreOf 2 L1 ⊓ pCoreOf 2 L2)}
    (hz : Multiplicative.toAdd
      (c₂.β ⟨(z : G), z.2.2⟩) = ![w, 0]) :
    pairingLineElem hH hD c₂ w = z := by
  have hz' : c₂.β ⟨(z : G), z.2.2⟩ = Multiplicative.ofAdd ![w, 0] := by
    simpa using congrArg Multiplicative.ofAdd hz
  apply Subtype.ext
  have h1 : (⟨(pairingLineElem hH hD c₂ w : G),
      (pairingLineElem hH hD c₂ w).2.2⟩ : ↥(pCoreOf 2 L2)) =
      ⟨(z : G), z.2.2⟩ := by
    apply c₂.β.injective
    rw [pairingLineElem_beta, hz']
  exact congrArg (fun q : ↥(pCoreOf 2 L2) => (q : G)) h1

private lemma pairingLineElem_zero (hH : Hyp111 L1 L2 S)
    (hD : L3qLocalData L1 L2 S f) (c₂ : VertexCoord L2 S (GaloisField 2 f)) :
    pairingLineElem hH hD c₂ 0 = 1 := by
  apply pairingLineElem_eq_of_coord (z := 1)
  have h : (⟨((1 : ↥(pCoreOf 2 L1 ⊓ pCoreOf 2 L2)) : G),
      (1 : ↥(pCoreOf 2 L1 ⊓ pCoreOf 2 L2)).2.2⟩ : ↥(pCoreOf 2 L2)) = 1 :=
    Subtype.ext rfl
  rw [h, map_one]
  funext i
  fin_cases i <;> simp

private lemma pairingLineElem_add (hH : Hyp111 L1 L2 S)
    (hD : L3qLocalData L1 L2 S f) (c₂ : VertexCoord L2 S (GaloisField 2 f))
    (a b : GaloisField 2 f) :
    pairingLineElem hH hD c₂ (a + b) =
      pairingLineElem hH hD c₂ a * pairingLineElem hH hD c₂ b := by
  apply pairingLineElem_eq_of_coord
  have h1 : (⟨(((pairingLineElem hH hD c₂ a * pairingLineElem hH hD c₂ b :
        ↥(pCoreOf 2 L1 ⊓ pCoreOf 2 L2)) : G)),
      (pairingLineElem hH hD c₂ a * pairingLineElem hH hD c₂ b).2.2⟩ :
        ↥(pCoreOf 2 L2)) =
      ⟨(pairingLineElem hH hD c₂ a : G), (pairingLineElem hH hD c₂ a).2.2⟩ *
        ⟨(pairingLineElem hH hD c₂ b : G), (pairingLineElem hH hD c₂ b).2.2⟩ :=
    Subtype.ext rfl
  rw [h1, map_mul, pairingLineElem_beta, pairingLineElem_beta, ← ofAdd_add]
  ext i
  fin_cases i <;> simp

private noncomputable def pairingL (hH : Hyp111 L1 L2 S)
    (hD : L3qLocalData L1 L2 S f) (c₁ : VertexCoord L1 S (GaloisField 2 f))
    (c₂ : VertexCoord L2 S (GaloisField 2 f)) :
    GaloisField 2 f →+ GaloisField 2 f where
  toFun w :=
    Multiplicative.toAdd (c₁.β ⟨(pairingLineElem hH hD c₂ w : G),
      (pairingLineElem hH hD c₂ w).2.1⟩) 0
  map_zero' := by
    rw [pairingLineElem_zero]
    have h : (⟨((1 : ↥(pCoreOf 2 L1 ⊓ pCoreOf 2 L2)) : G),
        (1 : ↥(pCoreOf 2 L1 ⊓ pCoreOf 2 L2)).2.1⟩ : ↥(pCoreOf 2 L1)) = 1 :=
      Subtype.ext rfl
    rw [h, map_one]
    simp
  map_add' a b := by
    rw [pairingLineElem_add]
    have hmul : (⟨(((pairingLineElem hH hD c₂ a * pairingLineElem hH hD c₂ b :
          ↥(pCoreOf 2 L1 ⊓ pCoreOf 2 L2)) : G)),
        (pairingLineElem hH hD c₂ a * pairingLineElem hH hD c₂ b).2.1⟩ :
          ↥(pCoreOf 2 L1)) =
        ⟨(pairingLineElem hH hD c₂ a : G), (pairingLineElem hH hD c₂ a).2.1⟩ *
          ⟨(pairingLineElem hH hD c₂ b : G), (pairingLineElem hH hD c₂ b).2.1⟩ :=
      Subtype.ext rfl
    rw [hmul, map_mul, toAdd_mul]
    simp

private lemma pairingL_bijective (hH : Hyp111 L1 L2 S)
    (hD : L3qLocalData L1 L2 S f) (c₁ : VertexCoord L1 S (GaloisField 2 f))
    (c₂ : VertexCoord L2 S (GaloisField 2 f)) :
    Function.Bijective (pairingL hH hD c₁ c₂) := by
  have hline₁ := L3qLocalData.mem_inf_iff_second_coord_left hH hD c₁ c₂
  have hline₂ := L3qLocalData.mem_inf_iff_second_coord_right hH hD c₂
  have hlineElem_inj : Function.Injective (pairingLineElem hH hD c₂) := by
    intro a b h
    have h' : Multiplicative.toAdd (c₂.β ⟨(pairingLineElem hH hD c₂ a : G),
        (pairingLineElem hH hD c₂ a).2.2⟩) 0 =
        Multiplicative.toAdd (c₂.β ⟨(pairingLineElem hH hD c₂ b : G),
          (pairingLineElem hH hD c₂ b).2.2⟩) 0 := by rw [h]
    rw [pairingLineElem_beta, pairingLineElem_beta] at h'
    simpa using h'
  constructor
  · intro a b hab
    have h0 : Multiplicative.toAdd (c₁.β ⟨(pairingLineElem hH hD c₂ a : G),
        (pairingLineElem hH hD c₂ a).2.1⟩) 0 =
        Multiplicative.toAdd (c₁.β ⟨(pairingLineElem hH hD c₂ b : G),
          (pairingLineElem hH hD c₂ b).2.1⟩) 0 := hab
    have ha1 : Multiplicative.toAdd (c₁.β ⟨(pairingLineElem hH hD c₂ a : G),
        (pairingLineElem hH hD c₂ a).2.1⟩) 1 = 0 :=
      (hline₁ _).mp (pairingLineElem hH hD c₂ a).2
    have hb1 : Multiplicative.toAdd (c₁.β ⟨(pairingLineElem hH hD c₂ b : G),
        (pairingLineElem hH hD c₂ b).2.1⟩) 1 = 0 :=
      (hline₁ _).mp (pairingLineElem hH hD c₂ b).2
    have hβ : c₁.β ⟨(pairingLineElem hH hD c₂ a : G),
        (pairingLineElem hH hD c₂ a).2.1⟩ =
        c₁.β ⟨(pairingLineElem hH hD c₂ b : G),
          (pairingLineElem hH hD c₂ b).2.1⟩ := by
      funext i
      fin_cases i
      · exact h0
      · show Multiplicative.toAdd (c₁.β ⟨(pairingLineElem hH hD c₂ a : G),
          (pairingLineElem hH hD c₂ a).2.1⟩) 1 =
          Multiplicative.toAdd (c₁.β ⟨(pairingLineElem hH hD c₂ b : G),
            (pairingLineElem hH hD c₂ b).2.1⟩) 1
        rw [ha1, hb1]
    have h1 : (⟨(pairingLineElem hH hD c₂ a : G),
        (pairingLineElem hH hD c₂ a).2.1⟩ : ↥(pCoreOf 2 L1)) =
        ⟨(pairingLineElem hH hD c₂ b : G),
          (pairingLineElem hH hD c₂ b).2.1⟩ := c₁.β.injective hβ
    apply hlineElem_inj
    exact Subtype.ext (congrArg (fun z : ↥(pCoreOf 2 L1) => (z : G)) h1)
  · intro y
    let w₁ : ↥(pCoreOf 2 L1) := c₁.β.symm (Multiplicative.ofAdd ![y, 0])
    have hw₁β : c₁.β w₁ = Multiplicative.ofAdd ![y, 0] := by
      simp [w₁]
    have hw₁ : (w₁ : G) ∈ (pCoreOf 2 L1 ⊓ pCoreOf 2 L2) := by
      rw [hline₁ w₁]
      rw [show Multiplicative.toAdd (c₁.β w₁) 1 = 0 by rw [hw₁β]; simp]
    let z : ↥(pCoreOf 2 L1 ⊓ pCoreOf 2 L2) := ⟨(w₁ : G), hw₁⟩
    have hz : Multiplicative.toAdd (c₂.β ⟨(z : G), z.2.2⟩) =
        ![Multiplicative.toAdd (c₂.β ⟨(z : G), z.2.2⟩) 0, 0] := by
      funext i
      fin_cases i
      · rfl
      · exact (hline₂ ⟨(z : G), z.2.2⟩).mp z.2
    let w : GaloisField 2 f := Multiplicative.toAdd (c₂.β ⟨(z : G), z.2.2⟩) 0
    have hline : pairingLineElem hH hD c₂ w = z :=
      pairingLineElem_eq_of_coord hH hD c₂ hz
    refine ⟨w, ?_⟩
    have hzw : (⟨(pairingLineElem hH hD c₂ w : G),
        (pairingLineElem hH hD c₂ w).2.1⟩ : ↥(pCoreOf 2 L1)) = w₁ := by
      rw [hline]
    show Multiplicative.toAdd (c₁.β ⟨(pairingLineElem hH hD c₂ w : G),
      (pairingLineElem hH hD c₂ w).2.1⟩) 0 = y
    rw [hzw, hw₁β]
    simp

private noncomputable def pairingY (hH : Hyp111 L1 L2 S)
    (hD : L3qLocalData L1 L2 S f) (c₂ : VertexCoord L2 S (GaloisField 2 f))
    (τ : GaloisField 2 f) : ↥(pCoreOf 2 L2) :=
  c₂.β.symm (Multiplicative.ofAdd ![0, τ])

private lemma pairingY_beta (hH : Hyp111 L1 L2 S)
    (hD : L3qLocalData L1 L2 S f) (c₂ : VertexCoord L2 S (GaloisField 2 f))
    (τ : GaloisField 2 f) :
    c₂.β (pairingY hH hD c₂ τ) = Multiplicative.ofAdd ![0, τ] := by
  simp [pairingY]

private noncomputable def pairingC (hH : Hyp111 L1 L2 S)
    (hD : L3qLocalData L1 L2 S f) (c₁ : VertexCoord L1 S (GaloisField 2 f))
    (c₂ : VertexCoord L2 S (GaloisField 2 f)) :
    GaloisField 2 f →+ GaloisField 2 f where
  toFun τ :=
    (c₁.α (Subgroup.inclusion (inclQ2L1 hH hD) (pairingY hH hD c₂ τ)) :
      Matrix (Fin 2) (Fin 2) (GaloisField 2 f)) 0 1
  map_zero' := by
    have h : pairingY hH hD c₂ 0 = 1 := by
      apply c₂.β.injective
      rw [pairingY_beta]
      simp
    rw [h, map_one]
    simp
  map_add' s t := by
    have hy : pairingY hH hD c₂ (s + t) =
        pairingY hH hD c₂ s * pairingY hH hD c₂ t := by
      apply c₂.β.injective
      rw [pairingY_beta, map_mul, pairingY_beta, pairingY_beta, ← ofAdd_add]
      ext i
      fin_cases i <;> simp
    obtain ⟨a, ha⟩ := L3qLocalData.map_pCoreOf_right_alpha hH hD c₁ (pairingY hH hD c₂ s)
    obtain ⟨b, hb⟩ := L3qLocalData.map_pCoreOf_right_alpha hH hD c₁ (pairingY hH hD c₂ t)
    show (c₁.α (Subgroup.inclusion (inclQ2L1 hH hD) (pairingY hH hD c₂ (s + t))) :
      Matrix (Fin 2) (Fin 2) (GaloisField 2 f)) 0 1 =
      (c₁.α (Subgroup.inclusion (inclQ2L1 hH hD) (pairingY hH hD c₂ s)) :
        Matrix (Fin 2) (Fin 2) (GaloisField 2 f)) 0 1 +
      (c₁.α (Subgroup.inclusion (inclQ2L1 hH hD) (pairingY hH hD c₂ t)) :
        Matrix (Fin 2) (Fin 2) (GaloisField 2 f)) 0 1
    have hinc : Subgroup.inclusion (inclQ2L1 hH hD)
          (pairingY hH hD c₂ s * pairingY hH hD c₂ t) =
        Subgroup.inclusion (inclQ2L1 hH hD) (pairingY hH hD c₂ s) *
          Subgroup.inclusion (inclQ2L1 hH hD) (pairingY hH hD c₂ t) :=
      map_mul _ _ _
    have hprod : (c₁.α (Subgroup.inclusion (inclQ2L1 hH hD)
          (pairingY hH hD c₂ s * pairingY hH hD c₂ t)) :
        Matrix (Fin 2) (Fin 2) (GaloisField 2 f)) =
        (c₁.α (Subgroup.inclusion (inclQ2L1 hH hD) (pairingY hH hD c₂ s)) :
          Matrix (Fin 2) (Fin 2) (GaloisField 2 f)) *
        (c₁.α (Subgroup.inclusion (inclQ2L1 hH hD) (pairingY hH hD c₂ t)) :
          Matrix (Fin 2) (Fin 2) (GaloisField 2 f)) := by
      rw [hinc, map_mul]
      rfl
    rw [hy, hprod, ha, hb]
    simp [Matrix.mul_apply, Fin.sum_univ_two]
    ring

private lemma pairingC_spec (hH : Hyp111 L1 L2 S)
    (hD : L3qLocalData L1 L2 S f) (c₁ : VertexCoord L1 S (GaloisField 2 f))
    (c₂ : VertexCoord L2 S (GaloisField 2 f)) (τ : GaloisField 2 f) :
    c₁.α (Subgroup.inclusion (inclQ2L1 hH hD) (pairingY hH hD c₂ τ)) =
      uSL (pairingC hH hD c₁ c₂ τ) := by
  obtain ⟨t, ht⟩ := L3qLocalData.map_pCoreOf_right_alpha hH hD c₁ (pairingY hH hD c₂ τ)
  apply Subtype.ext
  rw [coe_uSL]
  change (c₁.α (Subgroup.inclusion (inclQ2L1 hH hD) (pairingY hH hD c₂ τ)) :
    Matrix (Fin 2) (Fin 2) (GaloisField 2 f)) = uMat (pairingC hH hD c₁ c₂ τ)
  have hC : pairingC hH hD c₁ c₂ τ = t := by
    simp [pairingC, ht]
  rw [ht, uMat, hC]

private noncomputable def pairingSection (hH : Hyp111 L1 L2 S)
    (hD : L3qLocalData L1 L2 S f) (c₂ : VertexCoord L2 S (GaloisField 2 f))
    (t : GaloisField 2 f) : ↥(pCoreOf 2 L1) :=
  Classical.choose (L3qLocalData.map_pCoreOf_left_alpha_surjective hH hD c₂ t)

private lemma pairingSection_spec (hH : Hyp111 L1 L2 S)
    (hD : L3qLocalData L1 L2 S f) (c₂ : VertexCoord L2 S (GaloisField 2 f))
    (t : GaloisField 2 f) :
    c₂.α (Subgroup.inclusion (inclQ1L2 hH hD) (pairingSection hH hD c₂ t)) = uSL t := by
  apply Subtype.ext
  rw [coe_uSL]
  exact Classical.choose_spec
    (L3qLocalData.map_pCoreOf_left_alpha_surjective hH hD c₂ t)

private lemma pairingSection_coord_eq (hH : Hyp111 L1 L2 S)
    (hD : L3qLocalData L1 L2 S f) (c₁ : VertexCoord L1 S (GaloisField 2 f))
    (c₂ : VertexCoord L2 S (GaloisField 2 f)) {x y : ↥(pCoreOf 2 L1)}
    (hxy : c₂.α (Subgroup.inclusion (inclQ1L2 hH hD) x) =
      c₂.α (Subgroup.inclusion (inclQ1L2 hH hD) y)) :
    Multiplicative.toAdd (c₁.β x) 1 = Multiplicative.toAdd (c₁.β y) 1 := by
  have hline₁ := L3qLocalData.mem_inf_iff_second_coord_left hH hD c₁ c₂
  let k : ↥(pCoreOf 2 L1) := x * y⁻¹
  have hk1 : c₂.α (Subgroup.inclusion (inclQ1L2 hH hD) k) = 1 := by
    have hk : Subgroup.inclusion (inclQ1L2 hH hD) k =
        Subgroup.inclusion (inclQ1L2 hH hD) x * (Subgroup.inclusion (inclQ1L2 hH hD) y)⁻¹ := by
      rw [show k = x * y⁻¹ from rfl, map_mul, map_inv]
    rw [hk, map_mul, map_inv, hxy, mul_inv_cancel]
  have hkℓ : (k : G) ∈ (pCoreOf 2 L1 ⊓ pCoreOf 2 L2) :=
    ⟨k.2, by
      have h := (c₂.eq_one_iff (Subgroup.inclusion (inclQ1L2 hH hD) k)).mp hk1
      simpa using h⟩
  have hβk : Multiplicative.toAdd (c₁.β k) 1 = 0 := (hline₁ k).mp hkℓ
  have hβ : Multiplicative.toAdd (c₁.β k) =
      Multiplicative.toAdd (c₁.β x) - Multiplicative.toAdd (c₁.β y) := by
    rw [show k = x * y⁻¹ from rfl, map_mul, map_inv, toAdd_mul, toAdd_inv]
    simp [sub_eq_add_neg]
  have h := congrFun hβ 1
  rw [hβk] at h
  have h' : Multiplicative.toAdd (c₁.β x) 1 - Multiplicative.toAdd (c₁.β y) 1 = 0 := by
    simpa using h.symm
  exact sub_eq_zero.mp h'

private noncomputable def pairingA (hH : Hyp111 L1 L2 S)
    (hD : L3qLocalData L1 L2 S f) (c₁ : VertexCoord L1 S (GaloisField 2 f))
    (c₂ : VertexCoord L2 S (GaloisField 2 f)) :
    GaloisField 2 f →+ GaloisField 2 f where
  toFun σ := Multiplicative.toAdd (c₁.β (pairingSection hH hD c₂ σ)) 1
  map_zero' := by
    have h1 : c₂.α (Subgroup.inclusion (inclQ1L2 hH hD)
        (pairingSection hH hD c₂ 0)) = 1 := by
      rw [pairingSection_spec]
      exact uSL_zero
    have hℓ : (pairingSection hH hD c₂ 0 : G) ∈
        (pCoreOf 2 L1 ⊓ pCoreOf 2 L2) :=
      ⟨(pairingSection hH hD c₂ 0).2, by
        have h := (c₂.eq_one_iff (Subgroup.inclusion (inclQ1L2 hH hD)
          (pairingSection hH hD c₂ 0))).mp h1
        simpa using h⟩
    exact (L3qLocalData.mem_inf_iff_second_coord_left hH hD c₁ c₂ _).mp hℓ
  map_add' s t := by
    have h1 : c₂.α (Subgroup.inclusion (inclQ1L2 hH hD)
          (pairingSection hH hD c₂ (s + t))) =
        c₂.α (Subgroup.inclusion (inclQ1L2 hH hD)
          (pairingSection hH hD c₂ s * pairingSection hH hD c₂ t)) := by
      rw [pairingSection_spec,
        show Subgroup.inclusion (inclQ1L2 hH hD)
            (pairingSection hH hD c₂ s * pairingSection hH hD c₂ t) =
          Subgroup.inclusion (inclQ1L2 hH hD) (pairingSection hH hD c₂ s) *
            Subgroup.inclusion (inclQ1L2 hH hD) (pairingSection hH hD c₂ t)
          from map_mul _ _ _,
        map_mul, pairingSection_spec, pairingSection_spec, uSL_mul]
    have h2 := pairingSection_coord_eq hH hD c₁ c₂ h1
    rw [h2, map_mul, toAdd_mul]
    simp

private lemma pairingL_mul (hH : Hyp111 L1 L2 S)
    (hD : L3qLocalData L1 L2 S f) (c₁ : VertexCoord L1 S (GaloisField 2 f))
    (c₂ : VertexCoord L2 S (GaloisField 2 f)) (σ τ : GaloisField 2 f) :
    pairingL hH hD c₁ c₂ (σ * τ) =
      Multiplicative.toAdd (c₁.β (pairingSection hH hD c₂ σ)) 1 *
        pairingC hH hD c₁ c₂ τ := by
  classical
  let F := GaloisField 2 f
  haveI : CharP F 2 := by
    have hf0 : f ≠ 0 := by have := hD.one_le; omega
    haveI : Fintype F := Fintype.ofFinite F
    have hcard : Fintype.card F = 2 ^ f := by
      rw [Fintype.card_eq_nat_card]
      exact GaloisField.card 2 f hf0
    exact charP_of_card_eq_prime_pow hcard
  have hline₂ := L3qLocalData.mem_inf_iff_second_coord_right hH hD c₂
  let x := pairingSection hH hD c₂ σ
  let y := pairingY hH hD c₂ τ
  let z₁ : ↥(pCoreOf 2 L1) :=
    ⟨(y : G) * (x : G) * (y : G)⁻¹ * (x : G)⁻¹, by
      have hQ2L1 : pCoreOf 2 L2 ≤ L1 := inclQ2L1 hH hD
      have h1 : (y : G) * (x : G) * (y : G)⁻¹ ∈ pCoreOf 2 L1 :=
        (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 L1 (hQ2L1 y.2))
          (x : G)).mp x.2
      exact Subgroup.mul_mem _ h1 (Subgroup.inv_mem _ x.2)⟩
  let z₂ : ↥(pCoreOf 2 L2) :=
    ⟨(x : G) * (y : G) * (x : G)⁻¹ * (y : G)⁻¹, by
      have hQ1L2 : pCoreOf 2 L1 ≤ L2 := inclQ1L2 hH hD
      have h1 : (x : G) * (y : G) * (x : G)⁻¹ ∈ pCoreOf 2 L2 :=
        (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 L2 (hQ1L2 x.2))
          (y : G)).mp y.2
      exact Subgroup.mul_mem _ h1 (Subgroup.inv_mem _ y.2)⟩
  have hxα : (c₂.α (Subgroup.inclusion (inclQ1L2 hH hD) x) :
      Matrix (Fin 2) (Fin 2) F) = !![1, σ; 0, 1] := by
    have h := congrArg Subtype.val (pairingSection_spec hH hD c₂ σ)
    simpa [coe_uSL, uMat] using h
  have hyα : (c₁.α (Subgroup.inclusion (inclQ2L1 hH hD) y) :
      Matrix (Fin 2) (Fin 2) F) = !![1, pairingC hH hD c₁ c₂ τ; 0, 1] := by
    have h := congrArg Subtype.val (pairingC_spec hH hD c₁ c₂ τ)
    simpa [coe_uSL, uMat] using h
  have hcomm := L3qLocalData.commutator_coord hH hD c₁ c₂ hxα hyα z₁ z₂ rfl rfl
  have hβ₂z₂ : Multiplicative.toAdd (c₂.β z₂) = ![σ * τ, 0] := by
    rw [hcomm.2.1]
    have hτ : Multiplicative.toAdd (c₂.β y) 1 = τ := by rw [pairingY_beta]; simp
    rw [hτ]
  have hz₂ℓ : (z₂ : G) ∈ (pCoreOf 2 L1 ⊓ pCoreOf 2 L2) := by
    refine ⟨?_, z₂.2⟩
    have h : (z₂ : G) = (z₁ : G) := hcomm.2.2.symm
    rw [h]
    exact z₁.2
  have hline : pairingLineElem hH hD c₂ (σ * τ) = ⟨(z₂ : G), hz₂ℓ⟩ :=
    pairingLineElem_eq_of_coord hH hD c₂ hβ₂z₂
  have hl : pairingL hH hD c₁ c₂ (σ * τ) =
      Multiplicative.toAdd (c₁.β ⟨(z₂ : G), hz₂ℓ.1⟩) 0 := by
    change Multiplicative.toAdd (c₁.β ⟨(pairingLineElem hH hD c₂ (σ * τ) : G),
      (pairingLineElem hH hD c₂ (σ * τ)).2.1⟩) 0 = _
    rw [hline]
  have hz₁ : (⟨(z₂ : G), hz₂ℓ.1⟩ : ↥(pCoreOf 2 L1)) = z₁ :=
    Subtype.ext hcomm.2.2.symm
  have hfin : pairingL hH hD c₁ c₂ (σ * τ) =
      Multiplicative.toAdd (c₁.β x) 1 * pairingC hH hD c₁ c₂ τ := by
    rw [hl, hz₁, hcomm.1]
    simp [mul_comm]
  rw [hfin]

private lemma pairingL_mul_eq (hH : Hyp111 L1 L2 S)
    (hD : L3qLocalData L1 L2 S f) (c₁ : VertexCoord L1 S (GaloisField 2 f))
    (c₂ : VertexCoord L2 S (GaloisField 2 f)) :
    ∀ y t : GaloisField 2 f,
      pairingL hH hD c₁ c₂ (y * t) = pairingA hH hD c₁ c₂ y * pairingC hH hD c₁ c₂ t := by
  intro y t
  rw [pairingL_mul]
  rfl

theorem L3qLocalData.exists_ringEquiv_pairing (hH : Hyp111 L1 L2 S)
    (hD : L3qLocalData L1 L2 S f)
    (c₁ : VertexCoord L1 S (GaloisField 2 f)) (c₂ : VertexCoord L2 S (GaloisField 2 f)) :
    ∃ (ρ : GaloisField 2 f ≃+* GaloisField 2 f) (e₁ e₂ : (GaloisField 2 f)ˣ),
      (∀ (z₁ : ↥(pCoreOf 2 L1)) (z₂ : ↥(pCoreOf 2 L2)), (z₁ : G) = z₂ →
        Multiplicative.toAdd (c₁.β z₁) 1 = 0 ∧ Multiplicative.toAdd (c₂.β z₂) 1 = 0 ∧
        Multiplicative.toAdd (c₁.β z₁) 0 = e₁ * ρ (Multiplicative.toAdd (c₂.β z₂) 0)) ∧
      (∀ (x : ↥(pCoreOf 2 L1)) (x' : ↥L2) (t : GaloisField 2 f), (x : G) = x' →
        (c₂.α x' : Matrix (Fin 2) (Fin 2) (GaloisField 2 f)) = !![1, t; 0, 1] →
          Multiplicative.toAdd (c₁.β x) 1 = e₂ * ρ t) := by
  classical
  let F := GaloisField 2 f
  have hline₁ := L3qLocalData.mem_inf_iff_second_coord_left hH hD c₁ c₂
  have hline₂ := L3qLocalData.mem_inf_iff_second_coord_right hH hD c₂
  obtain ⟨ρ, hl, ha, hc⟩ :=
    exists_ringEquiv_of_map_mul (pairingL hH hD c₁ c₂) (pairingA hH hD c₁ c₂)
      (pairingC hH hD c₁ c₂) (pairingL_bijective hH hD c₁ c₂)
      (pairingL_mul_eq hH hD c₁ c₂)
  have h11 : pairingL hH hD c₁ c₂ 1 =
      pairingA hH hD c₁ c₂ 1 * pairingC hH hD c₁ c₂ 1 := by
    rw [← pairingL_mul_eq hH hD c₁ c₂ 1 1, mul_one]
  have hl1 : pairingL hH hD c₁ c₂ 1 ≠ 0 := by
    intro h0
    have h1 : (1 : F) = 0 := (pairingL_bijective hH hD c₁ c₂).1 (by rw [h0, map_zero])
    exact one_ne_zero h1
  have ha1 : pairingA hH hD c₁ c₂ 1 ≠ 0 := by
    intro h0
    exact hl1 (by rw [h11, h0, zero_mul])
  let e₁ : Fˣ := Units.mk0 (pairingL hH hD c₁ c₂ 1) hl1
  let e₂ : Fˣ := Units.mk0 (pairingA hH hD c₁ c₂ 1) ha1
  refine ⟨ρ, e₁, e₂, ?_, ?_⟩
  · intro z₁ z₂ hz
    have hz₁ℓ : (z₁ : G) ∈ (pCoreOf 2 L1 ⊓ pCoreOf 2 L2) :=
      ⟨z₁.2, by rw [hz]; exact z₂.2⟩
    have hz₂ℓ : (z₂ : G) ∈ (pCoreOf 2 L1 ⊓ pCoreOf 2 L2) := by
      rw [← hz]
      exact hz₁ℓ
    refine ⟨(hline₁ z₁).mp hz₁ℓ, (hline₂ z₂).mp hz₂ℓ, ?_⟩
    have hzℓ : (⟨(z₂ : G), hz₂ℓ⟩ : ↥(pCoreOf 2 L1 ⊓ pCoreOf 2 L2)) =
        ⟨(z₁ : G), hz₁ℓ⟩ := Subtype.ext hz.symm
    have hcoord : Multiplicative.toAdd (c₂.β ⟨(z₂ : G), hz₂ℓ.2⟩) =
        ![Multiplicative.toAdd (c₂.β z₂) 0, 0] := by
      funext i
      fin_cases i
      · rfl
      · simpa using (hline₂ z₂).mp hz₂ℓ
    have hline : pairingLineElem hH hD c₂ (Multiplicative.toAdd (c₂.β z₂) 0) =
        ⟨(z₂ : G), hz₂ℓ⟩ :=
      pairingLineElem_eq_of_coord hH hD c₂ hcoord
    have hlw : pairingL hH hD c₁ c₂ (Multiplicative.toAdd (c₂.β z₂) 0) =
        Multiplicative.toAdd (c₁.β z₁) 0 := by
      change Multiplicative.toAdd (c₁.β ⟨(pairingLineElem hH hD c₂
        (Multiplicative.toAdd (c₂.β z₂) 0) : G),
        (pairingLineElem hH hD c₂ (Multiplicative.toAdd (c₂.β z₂) 0)).2.1⟩) 0 =
        Multiplicative.toAdd (c₁.β z₁) 0
      rw [hline, hzℓ]
    rw [← hlw, hl]
    rfl
  · intro x x' t hx hx'
    have hx₂ : (Subgroup.inclusion (inclQ1L2 hH hD) x : ↥L2) = x' := Subtype.ext hx
    have hα : (c₂.α (Subgroup.inclusion (inclQ1L2 hH hD) x) :
        Matrix (Fin 2) (Fin 2) F) = !![1, t; 0, 1] := by
      rw [hx₂]
      exact hx'
    have hα' : c₂.α (Subgroup.inclusion (inclQ1L2 hH hD) x) =
        c₂.α (Subgroup.inclusion (inclQ1L2 hH hD) (pairingSection hH hD c₂ t)) := by
      apply Subtype.ext
      rw [pairingSection_spec, coe_uSL]
      exact hα
    have hcoord := pairingSection_coord_eq hH hD c₁ c₂ hα'
    have hspec : pairingA hH hD c₁ c₂ t =
        Multiplicative.toAdd (c₁.β (pairingSection hH hD c₂ t)) 1 := rfl
    rw [hcoord, ← hspec, ha]
    rfl

end CFSG.Quasithin.F112R.St84
