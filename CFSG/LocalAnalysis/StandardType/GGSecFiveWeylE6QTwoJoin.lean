module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylE6QTwoDefs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylE6QTwoBridgeDefs
public import CFSG.LocalAnalysis.StandardType.GGSkeleton
public import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylE6QTwoRowE
public import CFSG.Blueprint.Catalog

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal

section Cfg

variable {G : Type} [Group G] [Finite G]

theorem GGSecFiveE6QTwoCfg.weylAt_E6
    {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hC : GGSecFiveE6QTwoCfg p B Bs x L D J)
    (hE : GGSecFiveWeylAt p B Bs x L D J CoxeterMatrix.E₆ ∨
      GGSecFiveWeylAt p B Bs x L D J CoxeterMatrix.E₇ ∨
      GGSecFiveWeylAt p B Bs x L D J CoxeterMatrix.E₈) :
    GGSecFiveWeylAt p B Bs x L D J CoxeterMatrix.E₆ :=
  hE.resolve_right fun h => h.elim hC.not_weylAt_E7 hC.not_weylAt_E8

end Cfg

section MaxEleven

variable {X : Type} [Group X] [Finite X]

theorem eq_top_of_maxEleven
    (hmax : ∀ M : Subgroup X, IsCoatom M → 11 ∣ Nat.card M → GGTwistedE6MaxElevenProp M)
    {H L K E : Subgroup X} {x : X} (hLH : L ≤ H) (hKH : K ≤ H) (hEH : E ≤ H) (hxH : x ∈ H)
    (hL : Nat.card L = 9196830720) (hLp : ⁅L, L⁆ = L) (hKp : ⁅K, K⁆ = K) (hKL : ¬ K ≤ L)
    (hE : IsElemAbelian 3 E) (hEc : Nat.card E = 3 ^ 5) (hx : orderOf x = 3)
    (hxL : L ≤ Subgroup.centralizer {x}) (hxnL : x ∉ L) : H = ⊤ := by
  classical
  by_contra hH
  obtain ⟨M, hMcoat, hHM⟩ :=
    (@IsCoatomic.eq_top_or_exists_le_coatom (Subgroup X) _ _ (Finite.to_isCoatomic)
      H).resolve_left hH
  have hLM : L ≤ M := hLH.trans hHM
  have hKM : K ≤ M := hKH.trans hHM
  have hEM : E ≤ M := hEH.trans hHM
  have hxM : x ∈ M := hHM hxH
  have h11L : 11 ∣ Nat.card L := by rw [hL]; norm_num
  have h11M : 11 ∣ Nat.card M := h11L.trans (Subgroup.card_dvd_of_le hLM)
  rcases hmax M hMcoat h11M with hsmall | ⟨N, hNM, hNcard, hNP⟩ | hcent | hnot3
  · have hle := hsmall E hEM hE
    rw [hEc] at hle
    norm_num at hle
  · have hLN : L ≤ N := hNP L hLM hLp
    have hNLeq : Nat.card N = Nat.card L := by rw [hNcard, hL]
    have hLeqN : L = N := Subgroup.eq_of_le_of_card_ge hLN (le_of_eq hNLeq)
    have hKN : K ≤ N := hNP K hKM hKp
    exact hKL (by rw [hLeqN]; exact hKN)
  · have h11c : 11 ∣ Nat.card (M ⊓ Subgroup.centralizer ({x} : Set X) : Subgroup X) := by
      refine h11L.trans (Subgroup.card_dvd_of_le ?_)
      exact le_inf hLM hxL
    exact hcent x hxM hx h11c
  · apply hnot3
    have hcomm : ∀ a ∈ Subgroup.zpowers x, ∀ b ∈ L, Commute a b := by
      intro a ha b hb
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
      exact Commute.zpow_left ((Subgroup.mem_centralizer_singleton_iff.mp (hxL hb)).symm) k
    have hdisj : Subgroup.zpowers x ⊓ L = ⊥ := by
      have hdvd : Nat.card (Subgroup.zpowers x ⊓ L : Subgroup X) ∣ 3 := by
        have hle : Nat.card (Subgroup.zpowers x ⊓ L : Subgroup X) ∣
            Nat.card (Subgroup.zpowers x : Subgroup X) := Subgroup.card_dvd_of_le inf_le_left
        rwa [Nat.card_zpowers, hx] at hle
      rcases (Nat.dvd_prime (by norm_num : Nat.Prime 3)).mp hdvd with h1 | h3
      · exact Subgroup.eq_bot_of_card_eq (Subgroup.zpowers x ⊓ L) h1
      · exfalso
        have heq : Subgroup.zpowers x ⊓ L = Subgroup.zpowers x :=
          Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [h3, Nat.card_zpowers, hx])
        exact hxnL ((Subgroup.mem_inf.mp (heq ▸ Subgroup.mem_zpowers x)).2)
    have hcard : Nat.card (Subgroup.zpowers x ⊔ L : Subgroup X) = 3 * 9196830720 := by
      rw [CFSG.card_sup_eq_mul_of_commute _ _ hcomm hdisj, Nat.card_zpowers, hx, hL]
    have hdvd : 3 ^ 7 ∣ Nat.card (Subgroup.zpowers x ⊔ L : Subgroup X) := by
      rw [hcard]
      exact ⟨12615680, by norm_num⟩
    have hle : Subgroup.zpowers x ⊔ L ≤ M :=
      sup_le (Subgroup.zpowers_le.mpr hxM) hLM
    exact hdvd.trans (Subgroup.card_dvd_of_le hle)

end MaxEleven

section Join

variable {G : Type} [Group G] [Finite G]

theorem ggG0_eq_top_of_nbr
    (hWil : ∀ (X : Type) [Group X] [Finite X], ChevalleyExceptionalModel X .twistedE6 2 1 →
      KProper InCatalog X →
      ∀ M : Subgroup X, IsCoatom M → 11 ∣ Nat.card M → GGTwistedE6MaxElevenProp M)
    (hG : ChevalleyExceptionalModel G .twistedE6 2 1) (hK : KProper InCatalog G) {p : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hnbr : GGNbr p B x D J y K)
    (hL : Nat.card L = 9196830720) (hLp : ⁅L, L⁆ = L) (hKp : ⁅K, K⁆ = K) (hKL : ¬ K ≤ L)
    (hBs : IsElemAbelian 3 Bs) (hBsc : Nat.card Bs = 3 ^ 5) (hBsLK : Bs ≤ L ⊔ K)
    (hxBs : x ∈ Bs) (hx : orderOf x = 3) (hxL : L ≤ Subgroup.centralizer {x}) (hxnL : x ∉ L) :
    ggG0 p B x L D J = ⊤ := by
  have hmaxG : ∀ M : Subgroup G, IsCoatom M → 11 ∣ Nat.card M →
      GGTwistedE6MaxElevenProp M := hWil G hG hK
  have hL0 : L ≤ ggG0 p B x L D J := le_ggG0_left p B x L D J
  have hK0 : K ≤ ggG0 p B x L D J := le_ggG0_of_ggNbr hnbr
  have hBs0 : Bs ≤ ggG0 p B x L D J := hBsLK.trans (sup_le hL0 hK0)
  exact @eq_top_of_maxEleven G _ _ hmaxG (ggG0 p B x L D J) L K Bs x
    hL0 hK0 hBs0 (hBs0 hxBs) hL hLp hKp hKL hBs hBsc hx hxL hxnL

end Join

end CFSG.StandardType

end
