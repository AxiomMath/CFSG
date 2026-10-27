module

public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Sec6.T614.M3b
public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Sec6.T614.GenSemi

public section

open CFSG.Open

universe u

namespace CFSG.SignalizerFunctorTheorem.McBride.Nonsolv

namespace Counterexample

variable {p : ℕ} {G : Type u} [Group G] [Finite G] {A : Subgroup G} {θ : G → Subgroup G}
  {E : Subgroup G}

theorem wTilde_properties
    (h : Counterexample p A θ) (S : Setting614 p A θ E)
    {B : Subgroup G} (hB : B ∈ signalizerFunctorEk p 2 A) (hEB : E ⊓ B = ⊥) :
    (∀ b ∈ B, b ≠ 1 →
      wTilde θ E B ⊓ Subgroup.centralizer {b} = kOf (θ b) ⊓ thetaOf θ E) ∧
    (∀ J ∈ lcal (thetaOf θ E), wTilde θ E B ⊓ jTilde (thetaOf θ E) J =
      projIn (jTilde (thetaOf θ E) '' lcal (thetaOf θ E)) (jTilde (thetaOf θ E) J)
        (kOf (thetaOf θ B) ⊓ thetaOf θ E)) ∧
    IsDirectProduct {Y | ∃ J ∈ lcal (thetaOf θ E), Y = wTilde θ E B ⊓ jTilde (thetaOf θ E) J}
      (wTilde θ E B) := by
  classical
  have hBA : B ≤ A := hB.1
  have hE0 : E ≠ ⊥ := h.ne_bot_of_mem_E1 S.mem
  have hBel : IsElemAbelian p B := h.isElemAbelian_of_le hBA
  have hBN : B ≤ Subgroup.normalizer (thetaOf θ E : Set G) :=
    hBA.trans (h.isFunctor.normalizes_thetaOf S.mem.1)
  have hsolE : sol (thetaOf θ E) = ⊥ := h.sol_thetaOf S.mem.1 hE0
  have hHE := h.normalizes_of_mem_lcal_thetaOf S.mem.1 hE0
  obtain ⟨hreg1, hreg2⟩ := h.regular_lcal_thetaOf S hB hEB
  have hfree : ∀ b ∈ B, b ≠ 1 → ∀ J ∈ lcal (thetaOf θ E),
      J.map (MulAut.conj b).toMonoidHom ≠ J := fun b hb hb1 J hJ => hreg2 J hJ b hb hb1
  have hne : (lcal (thetaOf θ E)).Nonempty := h.lcal_thetaOf_nonempty S.mem.1 hE0
  have hsolH : sol (thetaOf θ E ⊔ B) = ⊥ := T614.sol_sup_eq_bot hBN hsolE hHE hfree hne
  have hlcal : lcal (thetaOf θ E ⊔ B) = lcal (thetaOf θ E) := T614.lcal_sup_eq hBel.1 hBN
  have hkOf : kOf (thetaOf θ E ⊔ B) = kOf (thetaOf θ E) :=
    T614.kOf_sup_eq hBel.1 hBN hsolE hsolH
  have hfun := h.isFunctor_thetaTilde S hB hEB
  have hle : ∀ g, thetaTilde θ E g ≤ θ g := fun g => inf_le_left.trans (kOf_le _)
  have hC : ∀ b ∈ B, b ≠ 1 → signalizerMcBrideHypothesisB p (thetaTilde θ E b) :=
    fun b hb hb1 => hypB_mono (hle b) (h.hypC b (hBA hb) hb1)
  obtain ⟨W, hWg, hproj, hdp⟩ := theorem_5_17 h.prime hBel hB.2 le_sup_right hsolH
    (fun J hJ J' hJ' => hreg1 J (hlcal ▸ hJ) J' (hlcal ▸ hJ'))
    (fun J hJ b hb hb1 => hreg2 J (hlcal ▸ hJ) b hb hb1)
    hfun (fun b hb hb1 => inf_le_right.trans le_sup_left) hC
    (fun b hb hb1 => by
      rw [hkOf]
      exact h.kOf_thetaOf_inf_centralizer_le S hB hEB hb hb1)
    (fun b hb hb1 => h.nonempty_pi_mulEquiv_thetaTilde S hB hEB hb hb1)
  have hWeq : W = wTilde θ E B :=
    eq_thetaSup_of_forall_le h.prime hBel hB.2.ge hfun hC hWg.1 fun X hX => hWg.2 hX
  have hjT : ∀ J ∈ lcal (thetaOf θ E),
      jTilde (thetaOf θ E ⊔ B) J = jTilde (thetaOf θ E) J := by
    intro J hJ
    have h2 : 1 < Nat.card (lcal (thetaOf θ E)) := by
      rw [S.card_E]
      exact Nat.one_lt_pow two_ne_zero h.prime.one_lt
    have := Finite.one_lt_card_iff_nontrivial.mp h2
    obtain ⟨⟨J', hJ'⟩, hne'⟩ := exists_ne (⟨J, hJ⟩ : ↥(lcal (thetaOf θ E)))
    exact T614.jTilde_sup_eq hBN hsolE hHE hfree hsolH hBel.1 hJ
      ⟨J', hJ', fun e => hne' (Subtype.ext e)⟩
  have himg : jTilde (thetaOf θ E ⊔ B) '' lcal (thetaOf θ E ⊔ B) =
      jTilde (thetaOf θ E) '' lcal (thetaOf θ E) := by
    rw [hlcal]
    exact Set.image_congr hjT
  rw [← hWeq]
  refine ⟨fun b hb hb1 => le_antisymm (hWg.1.2.2.1 b hb hb1) (le_inf ?_ ?_), fun J hJ => ?_, ?_⟩
  · have : thetaTilde θ E b ≤ wTilde θ E B := le_thetaSup hb hb1
    rw [← hWeq] at this
    exact this
  · exact (hle b).trans (h.isFunctor.le_centralizer b (hBA hb) hb1)
  · have := hproj J (hlcal ▸ hJ)
    rw [hjT J hJ, himg, h.thetaOf_thetaTilde S hB hEB] at this
    exact this
  · have hset : {Y | ∃ J ∈ lcal (thetaOf θ E ⊔ B), Y = W ⊓ jTilde (thetaOf θ E ⊔ B) J} =
        {Y | ∃ J ∈ lcal (thetaOf θ E), Y = W ⊓ jTilde (thetaOf θ E) J} := by
      ext Y
      constructor
      · rintro ⟨J, hJ, rfl⟩
        exact ⟨J, hlcal ▸ hJ, by rw [hjT J (hlcal ▸ hJ)]⟩
      · rintro ⟨J, hJ, rfl⟩
        exact ⟨J, hlcal ▸ hJ, by rw [hjT J hJ]⟩
    rw [hset] at hdp
    exact hdp

end Counterexample

end CFSG.SignalizerFunctorTheorem.McBride.Nonsolv
