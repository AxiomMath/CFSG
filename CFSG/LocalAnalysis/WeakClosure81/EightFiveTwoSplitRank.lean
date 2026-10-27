module

public import CFSG.LocalAnalysis.WeakClosure81.EightFiveTwoSplitDefs
public import CFSG.LocalAnalysis.WeakClosure81.SevenThirteen

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.CGT.Timmesfeld75 Subgroup
open CFSG.LocalAnalysis.WeakClosure81.SevenK
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem rk_subgroupOf_eq {V H : Subgroup G} (hVH : V ≤ H) : rk ↥(V.subgroupOf H) = rk ↥V := by
  unfold rk
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hVH).toEquiv]

theorem seven_thirteen_l2 (hRank : L2RootCommutatorRank) {V H E : Subgroup G}
    (h : Hyp711 V H E) {X : Type} [Group X] {φ : ↥(kSub V H E) →* X}
    (hφ : IsBarMap (kSub V H E) (pCoreOf 2 (kSub V H E)) φ) {n : ℕ}
    (hX : IsL2Gp (X ⧸ Subgroup.center X) n) : n + 1 ≤ rk ↥V := by
  have hnle : ¬ V ≤ pCoreOf 2 (kSub V H E) := not_le_pCoreOf_kSub h
  obtain ⟨v, hvV, hvJ⟩ := Set.not_subset.1 hnle
  have hVK : V ≤ kSub V H E := le_kSub h.mem
  have hvK : v ∈ kSub V H E := hVK hvV
  have hIab : IsElemAbelian 2 (iSub V H E) :=
    seven_two_iSub_isElemAbelian_uncond h.elemAbelian h.ti h.abelian h.omega_le
  have hKH : kSub V H E ≤ H := kSub_le_of_forall_le h.omega_le
  have hIleH : iSub V H E ≤ H := by
    refine iSup_le fun U => iSup_le fun _ => ?_
    exact inf_le_right.trans (CFSG.LieType.BorelTits.pCoreOf_le 2 H)
  have hHN : H ≤ Subgroup.normalizer (iSub V H E : Set G) :=
    le_normalizer_of_subgroupOf_normal hIleH (iSub_subgroupOf_normal h.le h.normal)
  have hKN : kSub V H E ≤ Subgroup.normalizer (iSub V H E : Set G) := hKH.trans hHN
  have hcent := kSub_inf_centralizer_iSub_le_pCoreOf h
  have hvv : v * v = 1 := elemAbelian_mul_self h.elemAbelian hvV
  have hne1 : φ ⟨v, hvK⟩ ≠ 1 := fun h1 => hvJ ((hφ.ker_iff _).mp h1)
  have hrank := hRank G (kSub V H E) (iSub V H E) n hIab hKN hcent X φ hφ hX
    ⟨v, hvK⟩ hvv hne1
  have hle := commutator_iSub_zpowers_le_inf_iSub h hvV
  have h2 : n ≤ rk ↥(V ⊓ iSub V H E) := hrank.trans (rk_mono hle)
  have h3 : V ⊓ iSub V H E < V := by
    rw [← inf_pCoreOf_kSub_eq_inf_iSub h]
    exact inf_lt_left.2 hnle
  have h4 := rk_add_one_le_of_lt h.elemAbelian h3
  omega

theorem rank_unitary_of_hyp83_at3 (hRank : UnitaryRootCommutatorRankAt 3) {V H T : Subgroup G}
    (h : Hyp83 V H T) (hKT : H = kGenIn V H ⊔ T) {X : Type} [Group X]
    {φ : ↥(ambK V H T) →* X} (hφ : IsBarMap (ambK V H T) (pCoreOf 2 (ambK V H T)) φ) (n : ℕ)
    (hX : IsPSUGp (X ⧸ Subgroup.center X) 3 n)
    (hroot : ∀ s ∈ barSub (ambK V H T) φ (ambV V H), s ≠ 1 → IsUnitaryTransvection X 3 n s) :
    2 * n + 1 ≤ rk ↥V := by
  have h13 := seven_thirteen_at hRank (AmbientH.hyp711 h hKT) hφ (m := 3) hX
    (fun k hkV hkJ => hroot (φ k) (mem_barSub.mpr ⟨k, hkV, rfl⟩)
      (fun h1 => hkJ ((hφ.ker_iff k).mp h1)))
  rw [← rk_subgroupOf_eq h.le_H]
  exact h13.1

theorem rank_l2_of_hyp83 (hRank : L2RootCommutatorRank) {V H T : Subgroup G}
    (h : Hyp83 V H T) (hKT : H = kGenIn V H ⊔ T) {X : Type} [Group X]
    {φ : ↥(ambK V H T) →* X} (hφ : IsBarMap (ambK V H T) (pCoreOf 2 (ambK V H T)) φ) (n : ℕ)
    (hX : IsL2Gp (X ⧸ Subgroup.center X) n) : n + 1 ≤ rk ↥V := by
  have h13 := seven_thirteen_l2 hRank (AmbientH.hyp711 h hKT) hφ hX
  rw [← rk_subgroupOf_eq h.le_H]
  exact h13

end CFSG.LocalAnalysis.WeakClosure81

end
