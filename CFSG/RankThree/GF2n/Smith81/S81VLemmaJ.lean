module

public import CFSG.RankThree.GF2n.Smith81.S81VPtStab
public import CFSG.RankThree.GF2n.Smith81.S81VNilpDim
public import CFSG.RankThree.GF2n.Smith81.S81VSchurFlag

public section

namespace CFSG.RankThree.GF2n.Smith81.S81V

open CFSG CFSG.Open CFSG.LieType.Universal.Unitary CFSG.ClassicalGroups.Unitary Module
  CFSG.RankThree.GF2n.Smith81 CFSG.RankThree.GF2n.Smith81.U6Cube

variable {F : Type} [Field F] {σ : F ≃+* F}

private theorem lemmaJ_isElemAbelian_map {E : Subgroup (SUid σ 6)} (hE : IsElemAbelian 2 E) :
    IsElemAbelian 2 (E.map (SUid σ 6).subtype) := by
  refine ⟨isMulCommutative_iff.mpr ?_, fun x hx => ?_⟩
  · rintro ⟨a, ha⟩ ⟨b, hb⟩
    obtain ⟨a₀, ha₀, rfl⟩ := Subgroup.mem_map.mp ha
    obtain ⟨b₀, hb₀, rfl⟩ := Subgroup.mem_map.mp hb
    have hab : (⟨a₀, ha₀⟩ : E) * ⟨b₀, hb₀⟩ = ⟨b₀, hb₀⟩ * ⟨a₀, ha₀⟩ :=
      isMulCommutative_iff.mp hE.1 ⟨a₀, ha₀⟩ ⟨b₀, hb₀⟩
    have h2 : ((a₀ : SUid σ 6) : GL (Fin 6) F) * ((b₀ : SUid σ 6) : GL (Fin 6) F) =
        ((b₀ : SUid σ 6) : GL (Fin 6) F) * ((a₀ : SUid σ 6) : GL (Fin 6) F) :=
      congrArg (fun z : E => ((z : SUid σ 6) : GL (Fin 6) F)) hab
    exact Subtype.ext h2
  · obtain ⟨x₀, hx₀, rfl⟩ := Subgroup.mem_map.mp hx
    have h2 : ((x₀ : SUid σ 6) : GL (Fin 6) F) ^ 2 = 1 := by
      rw [← Subgroup.coe_pow, hE.2 x₀ hx₀, Subgroup.coe_one]
    exact h2

private theorem lemmaJ_herm_smul_sub_self {e : SUid σ 6} (he : e ^ 2 = 1) (v y : Fin 6 → F)
    (hey : e • y = y) : herm σ (e • v - v) y = 0 := by
  have hee : ∀ z : Fin 6 → F, e • (e • z) = z := fun z => by
    rw [smul_smul, ← pow_two, he, one_smul]
  have h1 : herm σ (e • v) y = herm σ v (e • y) :=
    calc herm σ (e • v) y = herm σ (e • v) (e • (e • y)) := by rw [hee]
      _ = herm σ v (e • y) := herm_smul_smul σ e v (e • y)
  rw [herm_sub_left, h1, hey, sub_self]

theorem lemmaJU [Finite F] [CharP F 2] (hσ : IsUnitaryInvolution σ) {E : Subgroup (SUid σ 6)}
    (hE : IsElemAbelian 2 E) (h : Nat.card (Fσ σ) ^ 9 ≤ Nat.card E) :
    ∃ W : Submodule F (Fin 6 → F), IsTotIso σ W ∧ finrank F W = 3 ∧ E = PtStab σ W := by
  have hE' := lemmaJ_isElemAbelian_map hE
  have hle' : E.map (SUid σ 6).subtype ≤ SUid σ 6 := by
    intro x hx
    obtain ⟨g, -, rfl⟩ := Subgroup.mem_map.mp hx
    exact g.2
  have hcard' : Nat.card (Fσ σ) ^ 9 ≤ Nat.card (E.map (SUid σ 6).subtype) := by
    rw [Subgroup.card_map_of_injective (f := (SUid σ 6).subtype) Subtype.val_injective]
    exact h
  have h9 := nine_le_finrank_nilpSpan hσ hE' hle' hcard'
  obtain ⟨W, h3, -, hfixW, hspanW⟩ := exists_schur_space hE' h9
  have hsp : ∀ y ∈ W, ∀ x ∈ Submodule.span F {u : Fin 6 → F | ∃ e ∈ E.map (SUid σ 6).subtype,
      ∃ v : Fin 6 → F, u = ((e : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F).mulVec v - v},
      herm σ x y = 0 := by
    intro y hy x hx
    induction hx using Submodule.span_induction with
    | mem u hu =>
      obtain ⟨e, he, v, rfl⟩ := hu
      obtain ⟨e₀, he₀, rfl⟩ := Subgroup.mem_map.mp he
      exact lemmaJ_herm_smul_sub_self (hE.2 e₀ he₀) v y
        (hfixW ((SUid σ 6).subtype e₀) (Subgroup.mem_map_of_mem (SUid σ 6).subtype he₀) y hy)
    | zero => exact herm_zero_left σ y
    | add a b _ _ ha hb => rw [herm_add_left, ha, hb, add_zero]
    | smul c a _ ha => rw [herm_smul_left, ha, mul_zero]
  have hti : IsTotIso σ W := by
    intro x hx y hy
    exact hsp y hy x (hspanW hx)
  refine ⟨W, hti, h3, ?_⟩
  have hEP : E ≤ PtStab σ W := by
    intro e he w hw
    exact hfixW ((SUid σ 6).subtype e) (Subgroup.mem_map_of_mem (SUid σ 6).subtype he) w hw
  exact Subgroup.eq_of_le_of_card_ge hEP ((card_ptStab_le hσ hti h3).trans h)

end CFSG.RankThree.GF2n.Smith81.S81V
