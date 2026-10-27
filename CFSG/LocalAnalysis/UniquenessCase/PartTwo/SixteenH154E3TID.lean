module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154LemmaMc
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3MixedSL8UAB
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC56R37B
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3TIDA

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
variable {G : Type} [Group G] [Finite G]

theorem s16h_e3_v1_card_ge_eight (D : Data G) {V L : Subgroup G} (h : Setting16 D ⊥ V L)
    (hs2 : s15 D.M ⊥ V h.hyp151.isElemAbelian L = 2)
    {x : G} (hxM : x ∈ D.M) (hxn : x ∉ nBar D.M ⊥ V h.hyp151.isElemAbelian L)
    (hZ4 : 2 < Nat.card ↥(commSub ⊤ (lBar ⊥ V h.hyp151.isElemAbelian L) ⊓
      fixV (lBar ⊥ V h.hyp151.isElemAbelian L)))
    (hZ0 : wSub ⊥ V h.hyp151.isElemAbelian L ⊓
      conjSubgroup (wSub ⊥ V h.hyp151.isElemAbelian L) x = ⊥) :
    8 ≤ Nat.card ↥(v1Sub D.M ⊥ V h.hyp151.isElemAbelian L) := by
  have hV := h.hyp151.isElemAbelian
  rw [s16h_e3_v1Sub_eq_sup_zx D h hs2 hxM hxn]
  set Z : Subgroup G := wSub ⊥ V hV L ⊓ Subgroup.centralizer (L : Set G) with hZdef
  have hcardZ : Nat.card ↥Z =
      Nat.card ↥(commSub ⊤ (lBar ⊥ V hV L) ⊓ fixV (lBar ⊥ V hV L)) := by
    rw [hZdef, s16h_wSub_inf_centralizer_eq_preTil D h]
    rw [card_preTil (V₀ := ⊥) (V := V) hV bot_le, Subgroup.card_bot, one_mul]
  have hpow : Nat.card ↥(commSub ⊤ (lBar ⊥ V hV L) ⊓ fixV (lBar ⊥ V hV L)) =
      2 ^ rk ↥(commSub ⊤ (lBar ⊥ V hV L) ⊓ fixV (lBar ⊥ V hV L)) :=
    CFSG.Quasithin.card_eq_two_pow (s15_Infra_vtil_sq_eq_one ⊥ V hV) _
  have hZge : 4 ≤ Nat.card ↥Z := by
    rw [hcardZ, hpow]
    have hrk : 2 ≤ rk ↥(commSub ⊤ (lBar ⊥ V hV L) ⊓ fixV (lBar ⊥ V hV L)) := by
      by_contra hrk
      have hle : rk ↥(commSub ⊤ (lBar ⊥ V hV L) ⊓ fixV (lBar ⊥ V hV L)) ≤ 1 := by
        omega
      have hle' : 2 ^ rk ↥(commSub ⊤ (lBar ⊥ V hV L) ⊓ fixV (lBar ⊥ V hV L)) ≤ 2 := by
        simpa using Nat.pow_le_pow_right (show 0 < 2 by norm_num) hle
      have h4 := hZ4
      rw [hpow] at h4
      omega
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ rk ↥(commSub ⊤ (lBar ⊥ V hV L) ⊓ fixV (lBar ⊥ V hV L)) :=
          Nat.pow_le_pow_right (show 0 < 2 by norm_num) hrk
  have hcardZx : Nat.card ↥(conjSubgroup Z x) = Nat.card ↥Z := by
    change Nat.card ↥(Z.map (MulAut.conj x⁻¹).toMonoidHom) = Nat.card ↥Z
    exact Subgroup.card_map_of_injective (MulAut.conj x⁻¹).injective
  have hZinf : Z ⊓ conjSubgroup Z x = ⊥ := by
    apply le_bot_iff.1
    have h1 : Z ≤ wSub ⊥ V hV L := by
      rw [hZdef]
      exact inf_le_left
    have h2 : conjSubgroup Z x ≤ conjSubgroup (wSub ⊥ V hV L) x :=
      E3.conjSubgroup_mono_left x h1
    exact (le_inf (inf_le_left.trans h1) (inf_le_right.trans h2)).trans (le_of_eq hZ0)
  have hZx_ne : conjSubgroup Z x ≠ ⊥ := by
    intro hbot
    have hc : Nat.card ↥(conjSubgroup Z x) = 1 := by rw [hbot, Subgroup.card_bot]
    omega
  have hlt : Z < Z ⊔ conjSubgroup Z x := by
    refine lt_of_le_of_ne le_sup_left ?_
    intro heq
    apply hZx_ne
    have hle : conjSubgroup Z x ≤ Z := by
      have h := le_sup_right (a := Z) (b := conjSubgroup Z x)
      rwa [← heq] at h
    have hsub : conjSubgroup Z x ≤ Z ⊓ conjSubgroup Z x := le_inf hle le_rfl
    rw [hZinf] at hsub
    exact le_bot_iff.1 hsub
  have hkey := s16h_e3_two_mul_card_le_card_sup hlt
  omega

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
