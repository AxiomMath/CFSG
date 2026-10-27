module

public import CFSG.Quasithin.Background.B15P4Layer2Trans
public import CFSG.Quasithin.Background.B15P4Layer2Moved

public section

namespace CFSG.Quasithin.B15P4

open CFSG.Open

variable {V : Type} [CommGroup V] [Finite V]

theorem false_of_A2_ne_bot (hV : ∀ v : V, v ^ 2 = 1) {A K : Subgroup (MulAut V)}
    (hA : IsFFStarOffender (Kspan A K ⊔ A) A) (hK : IsComponentOf K (Kspan A K ⊔ A))
    (hex : ∃ a ∈ A, a ∉ Subgroup.normalizer (K : Set (MulAut V)))
    (hcomm : commV (Kspan A K) = ⊤)
    (hmin : ∀ W : Subgroup V, W ≠ ⊤ → (∀ a ∈ A, ∀ w ∈ W, a w ∈ W) →
      (∀ e ∈ Kspan A K, ∀ w ∈ W, e w ∈ W) → commSub W A ≠ ⊥ → ¬ K ≤ centSub W → False)
    (hB : A2sub A ≠ ⊥) : False := by
  classical
  obtain ⟨a₀, ha₀, hn⟩ := hex
  have hAG : A ≤ Kspan A K ⊔ A := hA.1
  have hEA : ⁅Kspan A K, A⁆ = Kspan A K := commutator_Kspan_eq hK hAG ha₀ hn
  by_cases hmoved : ∃ I ∈ IrrPlus (Kspan A K) (⊤ : Subgroup V), ∃ a ∈ A, I.map a.toMonoidHom ≠ I
  · obtain ⟨I, hI, a, ha, hmove⟩ := hmoved
    obtain ⟨b, hb1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hB
    exact false_of_moved hV hA hK ha₀ hn hcomm hmin b.2 (fun h => hb1 (Subtype.ext h)) hI ha hmove
  · have hfix : ∀ g ∈ A, ∀ J ∈ IrrPlus (Kspan A K) (⊤ : Subgroup V),
        J.map g.toMonoidHom = J := by
      intro g hg J hJ
      by_contra hne
      exact hmoved ⟨J, hJ, g, hg, hne⟩
    have htop := top_mem_irrPlus_of_fixed hK hAG hEA hmin hfix
    exact false_of_top_irr hV hA hK ha₀ hn hcomm htop hB

theorem false_of_centSub_ne_bot (hV : ∀ v : V, v ^ 2 = 1) {A K : Subgroup (MulAut V)}
    (hA : IsFFStarOffender (Kspan A K ⊔ A) A) (hK : IsComponentOf K (Kspan A K ⊔ A))
    (hex : ∃ a ∈ A, a ∉ Subgroup.normalizer (K : Set (MulAut V)))
    (hcomm : commV (Kspan A K) = ⊤)
    (hmin : ∀ W : Subgroup V, W ≠ ⊤ → (∀ a ∈ A, ∀ w ∈ W, a w ∈ W) →
      (∀ e ∈ Kspan A K, ∀ w ∈ W, e w ∈ W) → commSub W A ≠ ⊥ → ¬ K ≤ centSub W → False)
    (hB : A ⊓ centSub (commV A) ≠ ⊥) : False :=
  false_of_A2_ne_bot hV hA hK hex hcomm hmin (by rwa [A2sub_eq_inf_centSub hA.2.2.1.1])

end CFSG.Quasithin.B15P4
