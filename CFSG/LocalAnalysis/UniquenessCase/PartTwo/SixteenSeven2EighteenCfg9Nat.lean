module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenDefs
public import CFSG.Quasithin.EmptyFaithful.F918C14

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup

variable {W : Type} [CommGroup W]

@[expose] def NatSum3 (L : Subgroup (MulAut W)) (J : Subgroup W) : Prop :=
  ∃ I₀ I₁ I₂ : Subgroup W, XMod.IsIrr ↥L I₀ ∧ XMod.IsIrr ↥L I₁ ∧ XMod.IsIrr ↥L I₂ ∧
    Nat.card ↥I₀ = 8 ∧ Nat.card ↥I₁ = 8 ∧ Nat.card ↥I₂ = 8 ∧
    I₀ ⊓ I₁ = ⊥ ∧ (I₀ ⊔ I₁) ⊓ I₂ = ⊥ ∧ I₀ ⊔ I₁ ⊔ I₂ = J

private lemma s16c167_isIrr_of_binaryNatSummand {L : Subgroup (MulAut W)} {I : Subgroup W}
    (h : BinaryNaturalSL L I ⊥ 3 1) : XMod.IsIrr ↥L I := by
  obtain ⟨K, _, _, _, _, hπ⟩ := h
  exact CFSG.Quasithin.B5.isIrr_of_realizes (n := 3) (by norm_num) hπ

private lemma s16c167_card_of_binaryNatSummand {L : Subgroup (MulAut W)} {I : Subgroup W}
    (h : BinaryNaturalSL L I ⊥ 3 1) : Nat.card ↥I = 8 := by
  obtain ⟨K, _, _, hKcard, _, hπ⟩ := h
  haveI : Fintype K := Fintype.ofFinite K
  obtain ⟨e, -⟩ := CFSG.Quasithin.B5.exists_linModel hπ
  rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, Fintype.card_multiplicative,
    Fintype.card_fun, Fintype.card_fin, ← Nat.card_eq_fintype_card, hKcard]
  norm_num

theorem s16c167_natSum3_of_sumOfNat {L : Subgroup (MulAut W)} {J : Subgroup W}
    (h : SumOfNat (fun H U Z => BinaryNaturalSL H U Z 3 1) L J ⊥ 3) : NatSum3 L J := by
  obtain ⟨I, -, hind, hsup, hnat⟩ := h
  have hindep : iSupIndep I := by
    rw [iSupIndep_def]
    intro i
    rw [disjoint_iff]
    exact le_bot_iff.mp (by simpa [bot_sup_eq] using hind i)
  obtain ⟨hd0, -, hd2⟩ := iSupIndep_fin_three.mp hindep
  have h01 : I 0 ⊓ I 1 = ⊥ := by
    rw [← le_bot_iff]
    exact (le_inf inf_le_left (le_trans inf_le_right le_sup_left)).trans hd0.le_bot
  have h012 : (I 0 ⊔ I 1) ⊓ I 2 = ⊥ := by
    rw [inf_comm]
    exact le_bot_iff.mp hd2.le_bot
  have hsum : I 0 ⊔ I 1 ⊔ I 2 = J := by
    rw [← hsup, bot_sup_eq, iSup_fin_three]
  exact ⟨I 0, I 1, I 2, s16c167_isIrr_of_binaryNatSummand (hnat 0),
    s16c167_isIrr_of_binaryNatSummand (hnat 1), s16c167_isIrr_of_binaryNatSummand (hnat 2),
    s16c167_card_of_binaryNatSummand (hnat 0), s16c167_card_of_binaryNatSummand (hnat 1),
    s16c167_card_of_binaryNatSummand (hnat 2), h01, h012, hsum⟩

variable [Finite W]

theorem s16c167_rk_natSum3 {L : Subgroup (MulAut W)} {J : Subgroup W} (h : NatSum3 L J) :
    rk ↥J = 9 := by
  obtain ⟨I₀, I₁, I₂, -, -, -, hc₀, hc₁, hc₂, h01, h012, hsum⟩ := h
  rw [← hsum]
  have hI₀ : rk ↥I₀ = 3 := by
    show padicValNat 2 (Nat.card ↥I₀) = 3
    rw [hc₀, show (8 : ℕ) = 2 ^ 3 by norm_num, padicValNat.prime_pow]
  have hI₁ : rk ↥I₁ = 3 := by
    show padicValNat 2 (Nat.card ↥I₁) = 3
    rw [hc₁, show (8 : ℕ) = 2 ^ 3 by norm_num, padicValNat.prime_pow]
  have hI₂ : rk ↥I₂ = 3 := by
    show padicValNat 2 (Nat.card ↥I₂) = 3
    rw [hc₂, show (8 : ℕ) = 2 ^ 3 by norm_num, padicValNat.prime_pow]
  have hsup₁ : rk ↥(I₀ ⊔ I₁) = 6 := by
    have h := rk_sup_add_rk_inf I₀ I₁
    rw [h01, rk_bot, hI₀, hI₁] at h
    omega
  have hfin : rk ↥(I₀ ⊔ I₁ ⊔ I₂) = 9 := by
    have h := rk_sup_add_rk_inf (I₀ ⊔ I₁) I₂
    rw [h012, rk_bot, hsup₁, hI₂] at h
    omega
  exact hfin

theorem s16c167_natSum3_conj {L : Subgroup (MulAut W)} {J : Subgroup W} (h : NatSum3 L J)
    (φ : MulAut W) :
    NatSum3 (L.map (MulAut.conj φ).toMonoidHom) (J.map φ.toMonoidHom) := by
  obtain ⟨I₀, I₁, I₂, hi₀, hi₁, hi₂, hc₀, hc₁, hc₂, h01, h012, hsum⟩ := h
  refine ⟨I₀.map φ.toMonoidHom, I₁.map φ.toMonoidHom, I₂.map φ.toMonoidHom,
    CFSG.Quasithin.isIrr_map_conj φ hi₀, CFSG.Quasithin.isIrr_map_conj φ hi₁,
    CFSG.Quasithin.isIrr_map_conj φ hi₂, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Subgroup.card_map_of_injective (f := φ.toMonoidHom) φ.injective, hc₀]
  · rw [Subgroup.card_map_of_injective (f := φ.toMonoidHom) φ.injective, hc₁]
  · rw [Subgroup.card_map_of_injective (f := φ.toMonoidHom) φ.injective, hc₂]
  · rw [← Subgroup.map_inf I₀ I₁ φ.toMonoidHom φ.injective, h01, Subgroup.map_bot]
  · rw [← Subgroup.map_sup I₀ I₁ φ.toMonoidHom,
      ← Subgroup.map_inf (I₀ ⊔ I₁) I₂ φ.toMonoidHom φ.injective, h012, Subgroup.map_bot]
  · rw [← Subgroup.map_sup I₀ I₁ φ.toMonoidHom,
      ← Subgroup.map_sup (I₀ ⊔ I₁) I₂ φ.toMonoidHom, hsum]

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
