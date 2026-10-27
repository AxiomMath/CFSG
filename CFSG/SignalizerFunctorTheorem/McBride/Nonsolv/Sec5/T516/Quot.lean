module

public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Sec5.T516.NS
public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.SolQuot.Basic

public section

open CFSG.Open

universe u

namespace CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.T516

open AChief SolQuot

variable {Γ : Type u} [Group Γ] [Finite Γ] {p : ℕ} {A G N Y : Subgroup Γ}

theorem coprime_card_of_le (h : KSetting p A G) (hY : Y ≤ G) : Nat.Coprime p (Nat.card Y) :=
  h.hypB.2.1.coprime_dvd_right (Subgroup.card_dvd_of_le hY)

omit [Finite Γ] in
theorem isSolvable_qimg_of_isSolvable {S : Subgroup Γ} (hS : S ≤ nrm N)
    (h : Group.IsSolvable S) : Group.IsSolvable (qimg N S) :=
  have := h
  Group.isSolvable_of_surjective (f := qres N S hS) (qres_surjective hS)

theorem card_qimg_lt (hNG : N ≤ G) (hG : G ≤ nrm N) (hne : N ≠ ⊥) :
    Nat.card (qimg N G) < Nat.card G := by
  have h1 := card_qimg_mul_card hNG hG
  have h2 : 1 < Nat.card N := (Subgroup.one_lt_card_iff_ne_bot N).mpr hne
  rw [← h1]
  exact lt_mul_of_one_lt_right Nat.card_pos h2

theorem qimg_mem_nsSet (h : KSetting p A G) (hG : G ≤ nrm N) (hA : A ≤ nrm N)
    (hY : Y ∈ nsSet p A G) : qimg N Y ∈ nsSet p (qimg N A) (qimg N G) := by
  have hYG : Y ≤ G := hY.1
  have hYN : Y ≤ nrm N := hYG.trans hG
  refine ⟨qimg_mono hYG, ?_, qimg_le_normalizer hY.2.2.1, isElemAbelian_qimg h.elemAbelian,
    hypB_qimg hYN hY.2.2.2.2.1, ?_⟩
  · rw [← AChief.qimg_inf_centralizer h.prime h.elemAbelian h.normalizes hA hG h.hypB.2.1]
    exact qimg_le_normalizer hY.2.1
  · rw [← AChief.qimg_inf_centralizer h.prime h.elemAbelian hY.2.2.1 hA hYN
      (coprime_card_of_le h hYG)]
    exact isSolvable_qimg_of_isSolvable (inf_le_left.trans hYN) hY.2.2.2.2.2

theorem exists_mem_nsSet_qimg_eq (h : KSetting p A G) (hG : G ≤ nrm N) (hA : A ≤ nrm N)
    (hN : N ∈ nsSet p A G) {Y' : Subgroup (QG N)}
    (hY' : Y' ∈ nsSet p (qimg N A) (qimg N G)) : ∃ Y ∈ nsSet p A G, qimg N Y = Y' := by
  set Y := G ⊓ qpre N Y' with hYdef
  have hYG : Y ≤ G := inf_le_left
  have hYN : Y ≤ nrm N := hYG.trans hG
  have hNY : N ≤ Y := le_inf hN.1 (le_qpre Y')
  have himg : qimg N Y = Y' := by
    rw [hYdef, qimg_inf_of_le (qpre_le_nrm Y') (le_qpre Y'), qimg_qpre]
    exact inf_eq_right.mpr hY'.1
  have hE : G ⊔ A ≤ nrm N := sup_le hG hA
  have hnorm : ∀ g : Γ, ∀ hg : g ∈ G ⊔ A, qmap N ⟨g, hE hg⟩ ∈ Subgroup.normalizer (Y' : Set _) →
      g ∈ Subgroup.normalizer (Y : Set Γ) := fun g hg hq =>
    (mem_normalizer_qimg_iff (hYG.trans le_sup_left) (inf_le_right.trans hNY) hE hg).mp
      (himg ▸ hq)
  have hAY : A ≤ Subgroup.normalizer (Y : Set Γ) := fun a ha =>
    hnorm a ((le_sup_right : A ≤ G ⊔ A) ha)
      (hY'.2.2.1 ((mem_qimg_iff N A _).mpr ⟨⟨a, hA ha⟩, ha, rfl⟩))
  have hDY : G ⊓ Subgroup.centralizer (A : Set Γ) ≤ Subgroup.normalizer (Y : Set Γ) := by
    intro d hd
    refine hnorm d ((le_sup_left : G ≤ G ⊔ A) hd.1) (hY'.2.1 ?_)
    rw [← AChief.qimg_inf_centralizer h.prime h.elemAbelian h.normalizes hA hG h.hypB.2.1]
    exact (mem_qimg_iff N _ _).mpr ⟨⟨d, hG hd.1⟩, hd, rfl⟩
  refine ⟨Y, mem_nsSet_of_isDAInvariant h.elemAbelian
    (CFSG.SignalizerFunctor.Helpers.mcBrideHypothesisB_of_le p hYG h.hypB) ⟨hYG, hDY, hAY⟩ ?_,
    himg⟩
  have hsolq : Group.IsSolvable (qimg N (Y ⊓ Subgroup.centralizer (A : Set Γ))) := by
    rw [AChief.qimg_inf_centralizer h.prime h.elemAbelian hAY hA hYN (coprime_card_of_le h hYG),
      himg]
    exact hY'.2.2.2.2.2
  have hk : Group.IsSolvable ↥((Y ⊓ Subgroup.centralizer (A : Set Γ)) ⊓ N) :=
    isSolvable_of_le (fun x hx => Subgroup.mem_inf.mpr ⟨hx.2, hx.1.2⟩) hN.2.2.2.2.2
  exact (isSolvable_qimg_iff_of_inf hk (inf_le_left.trans hYN)).mp hsolq

theorem nsOf_qimg (h : KSetting p A G) (hG : G ≤ nrm N) (hA : A ≤ nrm N)
    (hN : N ∈ nsSet p A G) : qimg N (nsOf p A G) = nsOf p (qimg N A) (qimg N G) := by
  apply le_antisymm
  · show qimg N (⨆ Y ∈ nsSet p A G, Y) ≤ _
    rw [qimg_biSup (S := fun Y => Y) fun Y hY => hY.1.trans hG]
    exact iSup₂_le fun Y hY => le_nsOf (qimg_mem_nsSet h hG hA hY)
  · refine iSup₂_le fun Y' hY' => ?_
    obtain ⟨Y, hY, rfl⟩ := exists_mem_nsSet_qimg_eq h hG hA hN hY'
    exact qimg_mono (le_nsOf hY)

end CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.T516
