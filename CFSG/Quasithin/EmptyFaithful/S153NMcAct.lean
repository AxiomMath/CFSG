module

public import CFSG.Quasithin.Background.Module

public section

namespace CFSG.Quasithin.S153N

section Action

variable {W : Type} [CommGroup W]

instance quotAct (J : Subgroup (MulAut W)) : MulAction ↥J (W ⧸ fixV J) where
  smul g := QuotientGroup.map (fixV J) (fixV J) ((g : MulAut W) : W →* W) (fun c hc => by
    rw [Subgroup.mem_comap]
    show (g : MulAut W) c ∈ fixV J
    rw [hc g g.2]
    exact hc)
  one_smul q := by
    induction q using QuotientGroup.induction_on with
    | _ z => rfl
  mul_smul g h q := by
    induction q using QuotientGroup.induction_on with
    | _ z => rfl

theorem quotAct_smul_mk (J : Subgroup (MulAut W)) (g : ↥J) (x : W) :
    g • (QuotientGroup.mk x : W ⧸ fixV J) = QuotientGroup.mk ((g : MulAut W) x) := rfl

@[expose] def stabQ (J : Subgroup (MulAut W)) (w : W) : Subgroup ↥J :=
  MulAction.stabilizer ↥J (QuotientGroup.mk w : W ⧸ fixV J)

theorem mem_stabQ {J : Subgroup (MulAut W)} {w : W} {g : ↥J} :
    g ∈ stabQ J w ↔ (g : MulAut W) w * w⁻¹ ∈ fixV J := by
  rw [stabQ, MulAction.mem_stabilizer_iff, quotAct_smul_mk, QuotientGroup.eq_iff_div_mem,
    div_eq_mul_inv]

theorem index_stabQ_add_one_le [Finite W] (J : Subgroup (MulAut W)) {w : W} (hw : w ∉ fixV J) :
    (stabQ J w).index + 1 ≤ Nat.card (W ⧸ fixV J) := by
  have hnot : (1 : W ⧸ fixV J) ∉ MulAction.orbit ↥J (QuotientGroup.mk w : W ⧸ fixV J) := by
    rintro ⟨g, hg⟩
    have hc : (g : MulAut W) w ∈ fixV J :=
      (QuotientGroup.eq_one_iff _).1 (by rw [← quotAct_smul_mk]; exact hg)
    have hgg : (g : MulAut W) ((g : MulAut W) w) = (g : MulAut W) w := hc g g.2
    exact hw (by rwa [(g : MulAut W).injective hgg] at hc)
  rw [stabQ, MulAction.index_stabilizer, ← Set.ncard_insert_of_notMem hnot]
  exact Set.ncard_le_card _

theorem card_quot_fixV [Finite W] {J : Subgroup (MulAut W)}
    (hcard : Nat.card W = 2 ^ 4 * Nat.card ↥(fixV J)) : Nat.card (W ⧸ fixV J) = 16 := by
  have h := Subgroup.card_eq_card_quotient_mul_card_subgroup (fixV J)
  have hpos : 0 < Nat.card ↥(fixV J) := Nat.card_pos
  rw [hcard] at h
  have := Nat.eq_of_mul_eq_mul_right hpos h.symm
  omega

end Action

end CFSG.Quasithin.S153N
