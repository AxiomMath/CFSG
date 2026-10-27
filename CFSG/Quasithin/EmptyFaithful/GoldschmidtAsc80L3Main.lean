module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtAsc80L3Sd
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtAsc80L3WrNorm
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtAsc80Hyp

public section

namespace CFSG.Quasithin.E2P.Asc80

open Matrix CFSG.Quasithin.A38c15 CFSG.Quasithin.B6 CFSG.QuasithinUnique
open scoped MatrixGroups

variable {p : ℕ} [Fact p.Prime]

theorem exists_equiv_psl3 {H : Type} [Group H] {K : Subgroup H} (h : IsPSL 3 p 1 ↥K) :
    Nonempty (↥K ≃* PSL3 p) := by
  obtain ⟨-, F, hF, hFin, hcard, ⟨eK⟩⟩ := h
  let _ : Fintype F := Fintype.ofFinite F
  let _ : Fintype (ZMod p) := Fintype.ofFinite (ZMod p)
  have hc : Fintype.card F = Fintype.card (ZMod p) := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hcard, pow_one, Nat.card_zmod]
  exact ⟨eK.trans
    ((CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 3 F).symm.trans
      (CFSG.ClassicalModels.projectiveSpecialLinearFieldEquiv
        (FiniteField.ringEquivOfCardEq hc) (Fin 3)))⟩

theorem exists_noncomm_psl3 (hp2 : p ≠ 2) : ∃ a b : PSL3 p, a * b ≠ b * a :=
  ⟨piL p (w13 p), zc p, fun h => piL_w13_not_mem_leviC (mem_leviC_of_commute_z hp2 h)⟩

theorem asc80L3 (hirr : SL3OddIrr) (hp2 : p ≠ 2) {H : Type}
    [Group H] [Finite H] {K T M : Subgroup H} (hK : K.Normal) (hs : IsSimpleGroup ↥K)
    (hmodel : IsPSL 3 p 1 ↥K) (hc : Subgroup.centralizer (K : Set H) = ⊥)
    (hT : IsSylowTwoOf T ⊤) (hsup : K ⊔ T = ⊤) (hM : IsUniqueMaxOver ⊤ T M) :
    M ⊓ K = K ⊓ Subgroup.centralizer (zOf (T ⊓ K) : Set H) ∧ p % 4 = 3 ∧
      E2.InducesOuter T K := by
  obtain ⟨e⟩ := exists_equiv_psl3 hmodel
  have hnabC := exists_noncomm_psl3 (p := p) hp2
  have hnab : ∃ a b : ↥K, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hnabC
    exact ⟨e.symm a, e.symm b, fun h => hab (by simpa using congrArg e h)⟩
  have hX := asHyp_of_uniqueMax hK hs hnab hc hT hsup hM
  obtain ⟨hMK, hTK⟩ := inf_M_eq_of_l3 hirr hp2 hX e
  refine ⟨hMK, ?_, inducesOuter_of_not_le hK hc hTK⟩
  by_contra hp4
  have hodd : p % 2 = 1 := ((Fact.out : p.Prime).eq_two_or_odd).resolve_left hp2
  have hp1 : p % 4 = 1 := by omega
  obtain ⟨U, hU, hUB, hbot, hcomm, hnot⟩ := exists_wreathed_normalizer (p := p) hp1
  have : IsSimpleGroup ↥K := hs
  have : IsSimpleGroup (PSL3 p) := e.symm.isSimpleGroup
  have hN := normalizer_centralizer_ne_top hnabC hbot hcomm
  have hle := hX.normalizer_centralizer_commutator_le_levi e hU hN hMK
  rw [centralizer_zOf_eq_leviC hp2 hU hUB] at hle
  exact hnot hle

end CFSG.Quasithin.E2P.Asc80
