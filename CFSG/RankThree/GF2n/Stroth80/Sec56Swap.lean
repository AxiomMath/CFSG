module

public import CFSG.RankThree.GF2n.Stroth80.Sec56Frame
public import CFSG.RankThree.GF2n.Stroth80.Sec3Defs
public import CFSG.RankThree.GF2n.Stroth80.Sec56CentIndex
public import CFSG.RankThree.GF2n.Stroth80.Sec56SL2Model

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Timmesfeld CFSG.Timmesfeld.RankOne
open scoped commutatorElement Matrix

section SL2

variable (F : Type*) [Field F]

theorem upperElt_mulVec_zero (t : F) (v : Fin 2 → F) :
    ((upperElt F t : Matrix (Fin 2) (Fin 2) F) *ᵥ v) 0 = v 0 + t * v 1 := by
  simp [upperElt, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

theorem lowerElt_mulVec_zero (t : F) (v : Fin 2 → F) :
    ((lowerElt F t : Matrix (Fin 2) (Fin 2) F) *ᵥ v) 0 = v 0 := by
  simp [lowerElt, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

theorem lowerElt_mulVec_one (t : F) (v : Fin 2 → F) :
    ((lowerElt F t : Matrix (Fin 2) (Fin 2) F) *ᵥ v) 1 = t * v 0 + v 1 := by
  simp [lowerElt, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

theorem lowerElt_inv (t : F) : (lowerElt F t)⁻¹ = lowerElt F (-t) := by
  rw [inv_eq_iff_mul_eq_one, lowerElt_mul, add_neg_cancel, lowerElt_zero]

end SL2

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem Ctx.exists_QB_cent_swap (hc : Ctx M Q Z B) {C : Subgroup G}
    (hC : Ctx M Q Z C) (hCQ : C ≤ QB B) (hCB : ¬ C ≤ B ⊔ Z) (hBC : ¬ B ≤ C ⊔ Z) :
    (B ⊔ C) ⊓ Z = ⊥ ∧ ∃ D : Subgroup G, Ctx M Q Z D ∧ D ≤ B ⊔ C ∧ D ⊓ B = ⊥ ∧
      ∃ y ∈ QB D, y ∈ Subgroup.centralizer (Z : Set G) ∧ ∀ b ∈ B, y * b * y⁻¹ ∈ C := by
  obtain ⟨h, hh⟩ := hc.conj
  obtain ⟨c, hcC⟩ := hC.conj
  have hCB' : C ≠ B := fun e => hCB (e ▸ le_sup_left)
  have hBC' : B ≠ C := fun e => hCB' e.symm
  have hQBh : QB B = conjSubgroup h Q := (Ctx.QB_eq hc hh).2
  have hQCc : QB C = conjSubgroup c Q := (Ctx.QB_eq hC hcC).2
  have hBCx := hc.frame hh hcC hCQ hCB'
  have hBQC : B ≤ QB C := (Ctx.Z_le_QB hBCx).1
  have hCBx := hC.frame hcC hh hBQC hBC'
  have hZQB : Z ≤ QB B := (Ctx.Z_le_QB hc).1
  have hZQC : Z ≤ QB C := (Ctx.Z_le_QB hC).1
  have hidxB := hBCx.hyp.card_cent_inf (E := Z) (F := C) (gE := h⁻¹) (gF := c * h⁻¹)
    (by rw [hh, ← conjSubgroup_mul, inv_mul_cancel, conjSubgroup_one])
    (by rw [hcC, hh, ← conjSubgroup_mul, inv_mul_cancel_right])
    (by rw [← hQBh]; exact hZQB) (by rw [← hQBh]; exact hCQ) hc.ne.symm hCB'
    (by rwa [sup_comm] at hCB)
  have hidxC := hCBx.hyp.card_cent_inf (E := Z) (F := B) (gE := c⁻¹) (gF := h * c⁻¹)
    (by rw [hcC, ← conjSubgroup_mul, inv_mul_cancel, conjSubgroup_one])
    (by rw [hh, hcC, ← conjSubgroup_mul, inv_mul_cancel_right])
    (by rw [← hQCc]; exact hZQC) (by rw [← hQCc]; exact hBQC) hC.ne.symm hBC'
    (by rwa [sup_comm] at hBC)
  rw [← hQBh] at hidxB
  rw [← hQCc] at hidxC
  obtain ⟨n, hn2, hBn, φ, ψ, -, hφker, hcompat, hφU, hφL, hψB⟩ := hBCx.sl2Model
  have hQBH : QB B ≤ conjSubgroup h Q ⊔ QB C := by
    rw [hQBh]
    exact le_sup_left
  have hQCH : QB C ≤ conjSubgroup h Q ⊔ QB C := le_sup_right
  have hKn : Nat.card (GaloisField 2 n) = Nat.card B := by
    rw [GaloisField.card 2 n (by omega), hBn]
  have hcardC : Nat.card C = Nat.card B := by
    rw [hcC, hh, card_conjSubgroup, card_conjSubgroup]
  have hT₁ : ((QB B ⊓ Subgroup.centralizer (Z : Set G)).subgroupOf
      (conjSubgroup h Q ⊔ QB C)).map φ = upperUnipotent (GaloisField 2 n) := by
    refine map_eq_of_card_eq φ (P := (conjSubgroup h Q).subgroupOf (conjSubgroup h Q ⊔ QB C))
      ?_ hφU ?_
    · intro x hx
      rw [Subgroup.mem_subgroupOf] at hx ⊢
      have hx1 := hx.1
      rw [hQBh] at hx1
      exact hx1
    · rw [card_subgroupOf_of_le (inf_le_left.trans hQBH), hφker,
        card_subgroupOf_inf_subgroupOf (inf_le_left.trans hQBH), card_upperUnipotent, hKn]
      have e : QB B ⊓ Subgroup.centralizer (Z : Set G) ⊓
          Subgroup.centralizer ((B ⊔ C : Subgroup G) : Set G) =
          QB B ⊓ Subgroup.centralizer (Z : Set G) ⊓ Subgroup.centralizer (C : Set G) := by
        apply le_antisymm
        · exact inf_le_inf_left _
            (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr le_sup_right))
        · intro x hx
          refine ⟨hx.1, mem_centralizer_sup ?_ hx.2⟩
          exact Subgroup.mem_centralizer_iff.mpr fun b hb => (hc.QB_comm hx.1.1 hb).symm
      rw [e]
      exact hidxB
  have hT₂ : ((QB C ⊓ Subgroup.centralizer (Z : Set G)).subgroupOf
      (conjSubgroup h Q ⊔ QB C)).map φ = lowerUnipotent (GaloisField 2 n) := by
    refine map_eq_of_card_eq φ (P := (QB C).subgroupOf (conjSubgroup h Q ⊔ QB C)) ?_ hφL ?_
    · intro x hx
      rw [Subgroup.mem_subgroupOf] at hx ⊢
      exact hx.1
    · rw [card_subgroupOf_of_le (inf_le_left.trans hQCH), hφker,
        card_subgroupOf_inf_subgroupOf (inf_le_left.trans hQCH), card_lowerUnipotent, hKn,
        ← hcardC]
      have e : QB C ⊓ Subgroup.centralizer (Z : Set G) ⊓
          Subgroup.centralizer ((B ⊔ C : Subgroup G) : Set G) =
          QB C ⊓ Subgroup.centralizer (Z : Set G) ⊓ Subgroup.centralizer (B : Set G) := by
        apply le_antisymm
        · exact inf_le_inf_left _ (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr le_sup_left))
        · intro x hx
          refine ⟨hx.1, mem_centralizer_sup hx.2 ?_⟩
          exact Subgroup.mem_centralizer_iff.mpr fun c hc' => (hC.QB_comm hx.1.1 hc').symm
      rw [e]
      exact hidxC
  obtain ⟨x₁, hx₁T, hx₁⟩ : ∃ x₁ ∈ (QB B ⊓ Subgroup.centralizer (Z : Set G)).subgroupOf
      (conjSubgroup h Q ⊔ QB C), φ x₁ = upperElt (GaloisField 2 n) 1 := by
    have hu : upperElt (GaloisField 2 n) 1 ∈ upperUnipotent (GaloisField 2 n) :=
      (mem_upperUnipotent_iff _).mpr ⟨1, rfl⟩
    rw [← hT₁] at hu
    exact Subgroup.mem_map.mp hu
  obtain ⟨x₂, hx₂T, hx₂⟩ : ∃ x₂ ∈ (QB C ⊓ Subgroup.centralizer (Z : Set G)).subgroupOf
      (conjSubgroup h Q ⊔ QB C), φ x₂ = lowerElt (GaloisField 2 n) 1 := by
    have hu : lowerElt (GaloisField 2 n) 1 ∈ lowerUnipotent (GaloisField 2 n) :=
      (mem_lowerUnipotent_iff _).mpr ⟨1, rfl⟩
    rw [← hT₂] at hu
    exact Subgroup.mem_map.mp hu
  have hx₁G := Subgroup.mem_subgroupOf.mp hx₁T
  have hx₂G := Subgroup.mem_subgroupOf.mp hx₂T
  have hx₂M : (x₂ : G) ∈ M := by
    rw [← hc.hyp.normalizer_Z.1]
    exact Subgroup.centralizer_le_normalizer _ hx₂G.2
  have hψC : ∀ w : ↥(B ⊔ C), (w : G) ∈ C → Multiplicative.toAdd (ψ w) 0 = 0 := by
    intro w hw
    have h1 := hcompat x₂ w w (by rw [hC.QB_comm hx₂G.1 hw, mul_inv_cancel_right])
    rw [hx₂] at h1
    have h2 := congrFun h1 1
    rw [lowerElt_mulVec_one, one_mul] at h2
    have h3 : Multiplicative.toAdd (ψ w) 0 + Multiplicative.toAdd (ψ w) 1 =
        0 + Multiplicative.toAdd (ψ w) 1 := by rw [zero_add]; exact h2.symm
    exact add_right_cancel h3
  have hCmem : ∀ w : ↥(B ⊔ C), Multiplicative.toAdd (ψ w) 0 = 0 → (w : G) ∈ C := by
    intro w hw
    have hcardCW : Nat.card ↥(C.subgroupOf (B ⊔ C)) = Nat.card (GaloisField 2 n) := by
      rw [card_subgroupOf_of_le le_sup_right, hcardC, hKn]
    exact Subgroup.mem_subgroupOf.mp (mem_of_coord_zero (i := 0) (j := 1) (by decide) ψ hcardCW
      (fun w' hw' => hψC w' (Subgroup.mem_subgroupOf.mp hw')) hw)
  have hWnorm : ∀ z : ↥(conjSubgroup h Q ⊔ QB C), (z : G) ∈ QB B ∨ (z : G) ∈ QB C →
      ∀ w ∈ B ⊔ C, (z : G) * w * (z : G)⁻¹ ∈ B ⊔ C := by
    rintro z (hz | hz) w hw
    · exact hc.conj_mem_sup hCQ hz hw
    · rw [sup_comm] at hw ⊢
      exact hC.conj_mem_sup hBQC hz hw
  refine ⟨?_, conjSubgroup (x₂ : G) B, hc.conj_of_mem hx₂M, ?_, ?_,
    (x₂ : G) * x₁ * (x₂ : G)⁻¹, ?_, ?_, ?_⟩
  ·
    rw [eq_bot_iff]
    intro z hz
    obtain ⟨hzW, hzZ⟩ := Subgroup.mem_inf.mp hz
    have k1 := hcompat x₁ ⟨z, hzW⟩ ⟨z, hzW⟩ (by
      show z = (x₁ : G) * z * (x₁ : G)⁻¹
      rw [← (Subgroup.mem_centralizer_iff.mp hx₁G.2 z hzZ), mul_inv_cancel_right])
    have k2 := hcompat x₂ ⟨z, hzW⟩ ⟨z, hzW⟩ (by
      show z = (x₂ : G) * z * (x₂ : G)⁻¹
      rw [← (Subgroup.mem_centralizer_iff.mp hx₂G.2 z hzZ), mul_inv_cancel_right])
    rw [hx₁] at k1
    rw [hx₂] at k2
    have e1 := congrFun k1 0
    have e2 := congrFun k2 1
    rw [upperElt_mulVec_zero, one_mul] at e1
    rw [lowerElt_mulVec_one, one_mul] at e2
    have z1 : Multiplicative.toAdd (ψ ⟨z, hzW⟩) 1 = 0 := by
      have := e1
      linear_combination -this
    have z0 : Multiplicative.toAdd (ψ ⟨z, hzW⟩) 0 = 0 := by
      have := e2
      linear_combination -this
    have hz0 : Multiplicative.toAdd (ψ ⟨z, hzW⟩) = 0 := by
      funext i
      fin_cases i
      · exact z0
      · exact z1
    have hz1 : (⟨z, hzW⟩ : ↥(B ⊔ C)) = 1 := by
      apply ψ.injective
      rw [map_one]
      exact Multiplicative.toAdd.injective hz0
    rw [Subgroup.mem_bot]
    exact congrArg Subtype.val hz1
  · intro d hd
    have hb := mem_conjSubgroup.mp hd
    have e : d = (x₂ : G) * ((x₂ : G)⁻¹ * d * x₂) * (x₂ : G)⁻¹ := by group
    rw [e]
    exact hWnorm x₂ (Or.inr hx₂G.1) _ (Subgroup.mem_sup_left hb)
  · rw [eq_bot_iff]
    intro d hd
    obtain ⟨hdD, hdB⟩ := Subgroup.mem_inf.mp hd
    have hb := mem_conjSubgroup.mp hdD
    set b := (x₂ : G)⁻¹ * d * x₂ with hbdef
    have h1 := hcompat x₂ ⟨b, Subgroup.mem_sup_left hb⟩ ⟨d, Subgroup.mem_sup_left hdB⟩
      (by simp only [hbdef]; group)
    rw [hx₂] at h1
    have h2 := congrFun h1 1
    rw [lowerElt_mulVec_one, one_mul,
      (hψB ⟨d, Subgroup.mem_sup_left hdB⟩).mp hdB,
      (hψB ⟨b, Subgroup.mem_sup_left hb⟩).mp hb, add_zero] at h2
    have hb0 : Multiplicative.toAdd (ψ ⟨b, Subgroup.mem_sup_left hb⟩) = 0 := by
      funext i
      fin_cases i
      · exact h2.symm
      · exact (hψB ⟨b, Subgroup.mem_sup_left hb⟩).mp hb
    have hb1 : (⟨b, Subgroup.mem_sup_left hb⟩ : ↥(B ⊔ C)) = 1 := by
      apply ψ.injective
      rw [map_one]
      exact Multiplicative.toAdd.injective hb0
    have hb1' : b = 1 := congrArg Subtype.val hb1
    rw [Subgroup.mem_bot]
    have e : d = (x₂ : G) * b * (x₂ : G)⁻¹ := by simp only [hbdef]; group
    rw [e, hb1', mul_one, mul_inv_cancel]
  · rw [QB_conj, mem_conjSubgroup]
    have e : (x₂ : G)⁻¹ * ((x₂ : G) * x₁ * (x₂ : G)⁻¹) * x₂ = x₁ := by group
    rw [e]
    exact hx₁G.1
  · exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hx₂G.2 hx₁G.2) (Subgroup.inv_mem _ hx₂G.2)
  · intro b hb
    have hbW : b ∈ B ⊔ C := Subgroup.mem_sup_left hb
    have hb1 : (x₂ : G)⁻¹ * b * (x₂ : G)⁻¹⁻¹ ∈ B ⊔ C :=
      hWnorm x₂⁻¹ (Or.inr (Subgroup.inv_mem _ hx₂G.1)) b hbW
    have hb2 : (x₁ : G) * ((x₂ : G)⁻¹ * b * (x₂ : G)⁻¹⁻¹) * (x₁ : G)⁻¹ ∈ B ⊔ C :=
      hWnorm x₁ (Or.inl hx₁G.1) _ hb1
    have hb3 : (x₂ : G) * ((x₁ : G) * ((x₂ : G)⁻¹ * b * (x₂ : G)⁻¹⁻¹) * (x₁ : G)⁻¹) *
        (x₂ : G)⁻¹ ∈ B ⊔ C := hWnorm x₂ (Or.inr hx₂G.1) _ hb2
    have e : (x₂ : G) * x₁ * (x₂ : G)⁻¹ * b * ((x₂ : G) * x₁ * (x₂ : G)⁻¹)⁻¹ =
        (x₂ : G) * ((x₁ : G) * ((x₂ : G)⁻¹ * b * (x₂ : G)⁻¹⁻¹) * (x₁ : G)⁻¹) * (x₂ : G)⁻¹ := by
      group
    rw [e]
    have c1 := hcompat x₂⁻¹ ⟨b, hbW⟩ ⟨_, hb1⟩ (by simp)
    have c2 := hcompat x₁ ⟨_, hb1⟩ ⟨_, hb2⟩ rfl
    have c3 := hcompat x₂ ⟨_, hb2⟩ ⟨_, hb3⟩ rfl
    rw [map_inv, hx₂, lowerElt_inv] at c1
    rw [hx₁] at c2
    rw [hx₂] at c3
    refine hCmem ⟨_, hb3⟩ ?_
    rw [c3, lowerElt_mulVec_zero, c2, upperElt_mulVec_zero, c1,
      lowerElt_mulVec_zero, lowerElt_mulVec_one, (hψB ⟨b, hbW⟩).mp hb]
    ring
end CFSG.RankThree.GF2n.Stroth80
