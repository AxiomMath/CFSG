module

public import CFSG.Quasithin.Background.S1549CBasic
public import CFSG.Quasithin.EmptyFaithful.S153D26

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.S1417
open scoped commutatorElement Pointwise

namespace S1549C

variable {G : Type} [Group G] [Finite G] {T Mc M : Subgroup G}

omit [Finite G] in
theorem le_conjClosure_self (L T : Subgroup G) : L ≤ conjClosure L T := fun x hx => by
  have := mem_conjClosure (Z := L) (H := T) T.one_mem hx
  simpa using this

omit [Finite G] in
theorem conjClosure_le_of_le {L T H : Subgroup G} (hL : L ≤ H) (hT : T ≤ H) :
    conjClosure L T ≤ H :=
  conjClosure_le fun _ hk _ hz => H.mul_mem (H.mul_mem (hT hk) (hL hz)) (H.inv_mem (hT hk))

theorem eq_sup_of_minimal (h11 : StageLemma14111) (h113 : StageLemma14113) (h : Hyp153 G T Mc M)
    {H : Subgroup G} (hH : Adm T Mc M H)
    (hmin : ∀ H' : Subgroup G, Adm T Mc M H' → H' ≤ H → H' = H)
    (hb : Y0 T Mc M = thetaOf (M ⊓ H)) {L : Subgroup G} (hLH : L ≤ H) (hL1 : L ≠ ⊥)
    (hLp : ⁅L, L⁆ = L) (hLY : L = ⁅L, Y0 T Mc M⁆) :
    H = conjClosure L T ⊔ Y0 T Mc M ⊔ T := by
  have hTH : T ≤ H := le_sup_right.trans hH.hY0
  have hY0H : Y0 T Mc M ≤ H := le_sup_left.trans hH.hY0
  have hHMc : H ≤ Mc := C1Pack153.le_mc_of_isHTM153 h11 h hH.hH
  set H' : Subgroup G := conjClosure L T ⊔ Y0 T Mc M ⊔ T with hH'
  have hH'H : H' ≤ H := sup_le (sup_le (conjClosure_le_of_le hLH hTH) hY0H) hTH
  have hTH' : T ≤ H' := le_sup_right
  have hY0T : Y0 T Mc M ⊔ T ≤ H' := sup_le (le_sup_right.trans le_sup_left) le_sup_right
  have hLH' : L ≤ H' := (le_conjClosure_self L T).trans (le_sup_left.trans le_sup_left)
  have hZT : quasithinOmegaOneCenter T ≤ T := (le_conjClosure _ _).trans h.VZ_le_T
  have hZc : H' ≤ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) :=
    (hH'H.trans hHMc).trans (h.lemma_15_3_4 h11).le
  have hZH' : quasithinOmegaOneCenter T ≤ pCoreOf 2 H' :=
    le_pCoreOf_of_le_normalizer 2 (hZT.trans hTH')
      (fun g hg => (Subgroup.centralizer_le_normalizer _) (hZc hg))
      ((h.qtfe.sylow.1).to_le hZT)
  have hZne : quasithinOmegaOneCenter T ≠ ⊥ := by
    intro hbot
    have := h.lemma_15_3_2_two.2
    rw [hbot, Subgroup.card_bot] at this
    omega
  have hO2 : pCoreOf 2 H' ≠ ⊥ := fun hbot => hZne (le_bot_iff.mp (hbot ▸ hZH'))
  have hnM : ¬ H' ≤ M := by
    intro hHM
    have hLMH : L ≤ M ⊓ H := le_inf (hLH'.trans hHM) hLH
    have hnorm : L ≤ Subgroup.normalizer (Y0 T Mc M : Set G) := by
      rw [hb]
      exact fun x hx => S153D.normalizer_le_normalizer_thetaOf (M ⊓ H)
        (Subgroup.le_normalizer (hLMH hx))
    have hcomm : ⁅L, Y0 T Mc M⁆ ≤ Y0 T Mc M := by
      refine Subgroup.commutator_le.mpr fun l hl y hy => ?_
      have h1 := (Subgroup.mem_normalizer_iff.mp (hnorm hl) y).mp hy
      rw [commutatorElement_def]
      exact Subgroup.mul_mem _ h1 (Subgroup.inv_mem _ hy)
    have hLY0 : L ≤ Y0 T Mc M := hLY ▸ hcomm
    have hsolv : Group.IsSolvable ↥L :=
      S153D.isSolvable_of_le_Y153 h113 h (hLY0.trans ((Y0_le T Mc M).trans inf_le_left))
    have h1 := (isSolvable_iff_perfectCore_eq_bot L).mp hsolv
    rw [perfectCore_eq_self_of_perfect hLp] at h1
    exact hL1 h1
  exact (hmin H' ⟨⟨⟨hTH', hO2⟩, hnM⟩, hY0T⟩ hH'H).symm

end S1549C

end CFSG.Quasithin
