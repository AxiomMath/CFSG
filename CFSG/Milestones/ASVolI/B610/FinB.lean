module

public import CFSG.Milestones.ASVolI.B610.FinA
public import CFSG.Milestones.ASVolI.B610.CompA
public import CFSG.Milestones.ASVolI.B610.Targets
public import CFSG.Milestones.ASVolI.B610.FamG

public section

namespace CFSG.Quasithin.B610T.Fin

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem burnsideB610_le_of_subnormal {A B : Subgroup G} (h : IsSubnormal A B) : A ≤ B := by
  induction h with
  | refl A => exact le_rfl
  | @step A M B hAM _ _ ih => exact hAM.trans ih

omit [Finite G] in
theorem burnsideB610_convI_mem_normalizer {V Y : Subgroup G} (hV : IsElemAbelian 2 V) {g : G}
    (hg : g ∈ Subgroup.normalizer (V : Set G)) (hgY : g ∈ Subgroup.normalizer (Y : Set G)) :
    convI hV ⟨g, hg⟩ ∈ Subgroup.normalizer (autI hV Y : Set (MulAut (IntMod V hV))) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  refine (autI_cjSub hV hg Y).trans ?_
  rw [B2F.mem_normalizer_iff_cjSub_eq.mp hgY]

omit [Finite G] in
theorem burnsideB610_autI_sup_cent {H V L : Subgroup G} (hV : IsElemAbelian 2 V)
    (hHN : H ≤ Subgroup.normalizer (V : Set G)) (hLN : L ≤ Subgroup.normalizer (V : Set G)) :
    autI hV (L ⊔ (H ⊓ Subgroup.centralizer (V : Set G))) = autI hV L := by
  rw [autI_sup hV hLN (inf_le_left.trans hHN),
    autI_eq_bot_of_le_centralizer hV (inf_le_right : H ⊓ Subgroup.centralizer (V : Set G) ≤ _),
    sup_bot_eq]

theorem burnsideB610_case_ge_two (hcomp : burnsideB610_CompFamTarget) {H T M V L : Subgroup G}
    {n : ℕ} (hV : IsElemAbelian 2 V) (hMP : MinParabolic H T M) (hred : IsTwoReducedIn H V)
    (hL : IsSubnormal L H) (hJ : ¬ thompsonJ T ≤ Subgroup.centralizer (V : Set G)) (hn : 2 ≤ n)
    (hnat : IsNaturalL2Prime n L V) :
    (∀ s ∈ baum T, ∀ hs : s ∈ Subgroup.normalizer (V : Set G),
        convI hV ⟨s, hs⟩ ∈ Subgroup.normalizer ((autI hV L : Subgroup (MulAut (IntMod V hV))) :
          Set (MulAut (IntMod V hV)))) ∧
      IsSylowTwoOf (baum T) (⨆ l ∈ L, (baum T).map (MulAut.conj l).toMonoidHom) ∧
      (twoResidual L = L →
        omegaOneCenterOf (thompsonJ T) =
          (⁅V, L⁆ ⊓ Subgroup.centralizer (thompsonJ T : Set G)) ⊔
            (omegaOneCenterOf (thompsonJ T) ⊓ Subgroup.centralizer (L : Set G))) := by
  classical
  have hHN : H ≤ Subgroup.normalizer (V : Set G) := hred.2.1
  have hT := hMP.isSylow
  have hLH : L ≤ H := burnsideB610_le_of_subnormal hL
  have hLN : L ≤ Subgroup.normalizer (V : Set G) := hLH.trans hHN
  obtain ⟨F, _, _, hFc, ⟨D⟩⟩ := exists_natData hn hnat
  haveI : CharP F 2 := charP_of_card_eq_prime_pow hFc
  have hF : Nat.card F = 2 ^ n := by rw [Nat.card_eq_fintype_card, hFc]
  have h4 : ∃ s : Finset F, s.card = 4 := by
    have h4le : 4 ≤ (Finset.univ : Finset F).card := by
      rw [Finset.card_univ, hFc]
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
    obtain ⟨s, -, hs⟩ := Finset.exists_subset_card_eq h4le
    exact ⟨s, hs⟩
  obtain ⟨ι, S, X, DX, hFam, i₀, hi₀, hX₀⟩ := hcomp G H T M V L F n hMP hred hJ hL hn hFc D
  obtain ⟨hR1, hR2, hR3, hR4⟩ := hFam.main (by omega) hF hMP hred hJ
  have hLC : L ≤ Subgroup.normalizer
      ((H ⊓ Subgroup.centralizer (V : Set G) : Subgroup G) : Set G) := fun g hg =>
    Subgroup.inf_normalizer_le_normalizer_inf
      ⟨Subgroup.le_normalizer (hLH hg), B6.le_normalizer_centralizer hHN (hLH hg)⟩
  have hX₀aut : autI hV (X i₀) = autI hV L := by
    rw [hX₀]
    exact burnsideB610_autI_sup_cent hV hHN hLN
  have hLX : L ≤ X i₀ := by
    rw [hX₀]
    exact le_sup_left
  have hcomm : ⁅V, X i₀⁆ = ⁅V, L⁆ := by
    rw [hX₀]
    exact burnsideB610_commutator_sup_centralizing inf_le_right hLC
  have hnorm : ∀ (g : G) (hg : g ∈ Subgroup.normalizer (V : Set G)),
      g ∈ Subgroup.normalizer (X i₀ : Set G) →
      convI hV ⟨g, hg⟩ ∈ Subgroup.normalizer ((autI hV L : Subgroup (MulAut (IntMod V hV))) :
        Set (MulAut (IntMod V hV))) := by
    intro g hg hgX
    have h1 := burnsideB610_convI_mem_normalizer hV hg hgX
    rwa [hX₀aut] at h1
  have hLres : L ≤ twoResidual L ⊔ (H ⊓ Subgroup.centralizer (V : Set G)) :=
    (burnsideB610_le_twoResidual_sup D h4).trans (sup_le_sup_left (inf_le_inf_right _ hLH) _)
  have hsyl : IsSylowTwoOf (autI hV (baum T) ⊓ autI hV L) (autI hV L) := by
    obtain ⟨B, hBJ, hBX, hBc⟩ := hR3 i₀ hi₀
    have hST : baum T ≤ T := inf_le_left
    have hSN : baum T ≤ Subgroup.normalizer (V : Set G) := hST.trans (hT.1.trans hHN)
    have hY2 : IsPGroup 2 ↥(autI hV (baum T) ⊓ autI hV L) :=
      (B2F.isPGroup_autI hV (hT.2.1.to_le hST) hSN).to_le inf_le_left
    have hYL : autI hV (baum T) ⊓ autI hV L ≤ autI hV L := inf_le_right
    have hBY : autI hV B ≤ autI hV (baum T) ⊓ autI hV L :=
      le_inf (autI_mono hV (hBJ.trans (B2F.thompsonJ_le_baum T)))
        ((autI_mono hV hBX).trans hX₀aut.le)
    have hle := D.card_le_of_isPGroup hV hLN hYL hY2
    have hge : Nat.card F ≤ Nat.card ↥(autI hV (baum T) ⊓ autI hV L) := by
      rw [hF, ← hBc]
      exact Subgroup.card_le_of_le hBY
    exact D.isSylowTwoOf_of_card hV hLN hYL hY2 (le_antisymm hle hge)
  exact burnsideB610_concl hV hMP hred hJ hLH hLX hcomm hnorm hR1 (hR2 i₀ hi₀) (hR4 i₀ hi₀)
    hLres hsyl

end CFSG.Quasithin.B610T.Fin
