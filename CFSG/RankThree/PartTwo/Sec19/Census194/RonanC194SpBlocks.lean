module

public import CFSG.Open.StatedAPI
public import CFSG.LocalAnalysis.SectionRank.PRank

public section

namespace CFSG.RankThree.PartTwo.Sec19.Census194.RonanC194

open Matrix CFSG.Open

section Blocks

variable {K : Type*} [CommRing K] {n : ℕ}

@[expose] def spBlock (A : Fin n → Matrix (Fin 2) (Fin 2) K) :
    Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K :=
  fromBlocks (diagonal fun i => A i 0 0) (diagonal fun i => A i 0 1)
    (diagonal fun i => A i 1 0) (diagonal fun i => A i 1 1)

theorem spBlock_mul (A B : Fin n → Matrix (Fin 2) (Fin 2) K) :
    spBlock A * spBlock B = spBlock (fun i => A i * B i) := by
  unfold spBlock
  rw [fromBlocks_multiply]
  simp only [diagonal_mul_diagonal, diagonal_add, mul_apply, Fin.sum_univ_two]

theorem spBlock_one : spBlock (fun _ : Fin n => (1 : Matrix (Fin 2) (Fin 2) K)) = 1 := by
  unfold spBlock
  rw [← fromBlocks_one]
  simp [one_apply]

theorem spBlock_symp (A : Fin n → Matrix (Fin 2) (Fin 2) K) (hA : ∀ i, (A i).det = 1) :
    (spBlock A)ᵀ * fromBlocks 0 1 (-1) 0 * spBlock A = fromBlocks 0 1 (-1) 0 := by
  unfold spBlock
  rw [fromBlocks_transpose, fromBlocks_multiply, fromBlocks_multiply]
  simp only [diagonal_transpose, transpose_zero, transpose_one, Matrix.mul_zero, Matrix.mul_one,
    Matrix.zero_mul, zero_add, add_zero, Matrix.mul_neg, Matrix.neg_mul, diagonal_mul_diagonal]
  have h : ∀ i, A i 0 0 * A i 1 1 - A i 0 1 * A i 1 0 = 1 := fun i => by
    rw [← det_fin_two]; exact hA i
  simp only [diagonal_neg, diagonal_add]
  rw [fromBlocks_inj]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← diagonal_zero]; congr 1; funext i; ring
  · rw [← diagonal_one]; congr 1; funext i; linear_combination h i
  · rw [show (-1 : Matrix (Fin n) (Fin n) K) = diagonal fun _ => -1 by
      rw [← diagonal_neg, diagonal_one]]
    congr 1; funext i; linear_combination (-1 : K) * h i
  · rw [← diagonal_zero]; congr 1; funext i; ring

theorem spBlock_injective :
    Function.Injective (spBlock : (Fin n → Matrix (Fin 2) (Fin 2) K) → _) := by
  intro A B h
  unfold spBlock at h
  rw [fromBlocks_inj] at h
  obtain ⟨h00, h01, h10, h11⟩ := h
  funext i
  ext a b
  fin_cases a <;> fin_cases b
  · exact congrFun (diagonal_injective h00) i
  · exact congrFun (diagonal_injective h01) i
  · exact congrFun (diagonal_injective h10) i
  · exact congrFun (diagonal_injective h11) i

end Blocks

section Hom

variable (K : Type) [Field K] (n : ℕ)

@[expose] noncomputable def spBlockHom :
    (Fin n → Matrix.SpecialLinearGroup (Fin 2) K) →* StatedSp n K :=
  let Φ : (Fin n → Matrix.SpecialLinearGroup (Fin 2) K) →*
      Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K :=
    { toFun := fun A => spBlock fun i => (A i : Matrix (Fin 2) (Fin 2) K)
      map_one' := spBlock_one
      map_mul' := fun A B => (spBlock_mul _ _).symm }
  (MonoidHom.toHomUnits Φ).codRestrict (StatedSp n K) fun A =>
    StatedAPI.mem_statedSp_iff.2 (spBlock_symp _ fun i => (A i).2)

theorem coe_spBlockHom (A : Fin n → Matrix.SpecialLinearGroup (Fin 2) K) :
    (((spBlockHom K n A : StatedSp n K) : GL (Fin n ⊕ Fin n) K) :
      Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) =
        spBlock fun i => (A i : Matrix (Fin 2) (Fin 2) K) :=
  rfl

theorem spBlockHom_injective : Function.Injective (spBlockHom K n) := by
  intro A B h
  have h1 := congrArg (fun x : StatedSp n K =>
    (((x : GL (Fin n ⊕ Fin n) K) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K))) h
  simp only [coe_spBlockHom] at h1
  have h2 := spBlock_injective h1
  funext i
  exact Subtype.ext (congrFun h2 i)

end Hom

section Rank

variable {K : Type} [Field K] [Finite K] {n r : ℕ}

theorem le_pRank_statedSp (hr : r.Prime) (hdvd : r ∣ Nat.card K ^ 2 - 1) :
    n ≤ CFSG.Open.pRank r (⊤ : Subgroup (StatedSp n K)) := by
  haveI : Fact r.Prime := ⟨hr⟩
  obtain ⟨g, hg⟩ : ∃ g : Matrix.SpecialLinearGroup (Fin 2) K, orderOf g = r := by
    refine exists_prime_orderOf_dvd_card' r ?_
    rw [← StatedAPI.card_statedSL, StatedAPI.card_statedSL_two]
    exact Dvd.dvd.mul_left hdvd _
  have hcard : Nat.card (Fin n → Subgroup.zpowers g) = r ^ n := by
    rw [Nat.card_pi]
    simp [Nat.card_zpowers, hg]
  refine CFSG.SectionRank.le_pRank_of_injective hr.one_lt (fun a b => ?_) (fun a => ?_) hcard
    ((spBlockHom K n).comp (MonoidHom.compLeft (Subgroup.zpowers g).subtype (Fin n))) ?_ le_top
  · funext i
    exact mul_comm' (a i) (b i)
  · funext i
    rw [Pi.pow_apply, Pi.one_apply]
    have := pow_card_eq_one' (G := Subgroup.zpowers g) (x := a i)
    rwa [Nat.card_zpowers, hg] at this
  · exact (spBlockHom_injective K n).comp
      (fun a b h => funext fun i => Subtype.ext (congrFun h i))

@[expose] noncomputable def statedProjEquivSp [CharP K 2] :
    StatedProj (StatedSp n K) ≃* StatedSp n K :=
  (QuotientGroup.quotientMulEquivOfEq
    (StatedAPI.statedScalars_subgroupOf_statedSp_eq_bot (n := n) (K := K))).trans
    QuotientGroup.quotientBot

theorem le_pRank_statedProj_sp [CharP K 2] (hr : r.Prime) (hdvd : r ∣ Nat.card K ^ 2 - 1) :
    n ≤ CFSG.Open.pRank r (⊤ : Subgroup (StatedProj (StatedSp n K))) := by
  rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv hr.one_lt statedProjEquivSp]
  exact le_pRank_statedSp hr hdvd

end Rank

end CFSG.RankThree.PartTwo.Sec19.Census194.RonanC194
