module

public import CFSG.LocalAnalysis.WeakClosure81.EightSixDefs
public import CFSG.LocalAnalysis.WeakClosure81.EightSixLast

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

@[expose] def W3Lem83In (G : Type) [Group G] [Finite G] : Prop :=
  ∀ V H T : Subgroup G, Hyp7 V → IsCalH V H → ¬ IsCalH0 V H →
    IsSylowIn 2 T (H ⊓ Subgroup.normalizer (V : Set G)) →
      (∀ k ∈ conjClosure V H, ∃ a ∈ kGenIn V H, conjSubgroup V k = conjSubgroup V a) ∧
      (H : Set G) = (kGenIn V H : Set G) *
        ((H ⊓ Subgroup.normalizer (V : Set G) : Subgroup G) : Set G) *
        ((H ⊓ Subgroup.normalizer (E3.wClos V 0 T : Set G) : Subgroup G) : Set G)

theorem conjClosure_le_of_le_H {V H : Subgroup G} (hVH : V ≤ H) : conjClosure V H ≤ H :=
  conjClosure_le fun h hh _ hz => H.mul_mem (H.mul_mem hh (hVH hz)) (H.inv_mem hh)

theorem conjSubgroup_le_kGenIn {V H : Subgroup G} {k : G} (hk : k ∈ conjClosure V H) :
    conjSubgroup V k ≤ kGenIn V H :=
  le_iSup₂_of_le k hk le_rfl

theorem le_kGenIn_self (V H : Subgroup G) : V ≤ kGenIn V H := by
  simpa only [conjSubgroup_one] using conjSubgroup_le_kGenIn (V := V) (H := H) (one_mem _)

theorem kGenIn_le_H {V H : Subgroup G} (hVH : V ≤ H) : kGenIn V H ≤ H :=
  iSup₂_le fun _ hk => conjSubgroup_le_of_le hVH (conjClosure_le_of_le_H hVH hk)

theorem kGenIn_le_conjClosure (V H : Subgroup G) : kGenIn V H ≤ conjClosure V H :=
  iSup₂_le fun _ hk => conjSubgroup_le_of_le (le_conjClosure V H) hk

theorem conjClosure_le_normalizer_kGenIn (V H : Subgroup G) :
    conjClosure V H ≤ Subgroup.normalizer (kGenIn V H : Set G) := by
  intro x hx
  have h1 : conjSubgroup (kGenIn V H) x ≤ kGenIn V H := by
    have hmap : conjSubgroup (kGenIn V H) x =
        ⨆ k ∈ conjClosure V H, conjSubgroup V (k * x) := by
      rw [show conjSubgroup (kGenIn V H) x =
          (kGenIn V H).map (MulAut.conj x⁻¹).toMonoidHom from rfl]
      unfold kGenIn
      rw [Subgroup.map_iSup]
      refine iSup_congr fun k => ?_
      rw [Subgroup.map_iSup]
      refine iSup_congr fun hk => ?_
      exact conjSubgroup_conjSubgroup V k x
    rw [hmap]
    exact iSup₂_le fun k hk => conjSubgroup_le_kGenIn ((conjClosure V H).mul_mem hk hx)
  exact conjSubgroup_eq_iff_mem_normalizer.mp
    (Subgroup.eq_of_le_of_card_ge h1 (E3.card_conjSubgroup (kGenIn V H) x).ge)

theorem pCoreOf_conjClosure_le_pCoreOf {V H : Subgroup G} (hVH : V ≤ H) :
    pCoreOf 2 (conjClosure V H) ≤ pCoreOf 2 H := by
  refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
    ((CFSG.LieType.BorelTits.pCoreOf_le (r := 2) (conjClosure V H)).trans
      (conjClosure_le_of_le_H hVH)) ?_
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup (r := 2) (conjClosure V H))
  exact (le_normalizer_conjClosure V H).trans
    (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 _)

theorem pCoreOf_kGenIn_le {V H : Subgroup G} (hVH : V ≤ H) :
    pCoreOf 2 (kGenIn V H) ≤ pCoreOf 2 H := by
  refine le_trans ?_ (pCoreOf_conjClosure_le_pCoreOf hVH)
  refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
    ((CFSG.LieType.BorelTits.pCoreOf_le (r := 2) (kGenIn V H)).trans
      (kGenIn_le_conjClosure V H)) ?_
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup (r := 2) (kGenIn V H))
  exact (conjClosure_le_normalizer_kGenIn V H).trans
    (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 _)

theorem not_kGenIn_le_normalizer {V H T : Subgroup G} (hV : IsElemAbelian 2 V) (hH : IsCalH V H)
    (hH0 : ¬ IsCalH0 V H) (hTM : T ≤ Subgroup.normalizer (V : Set G))
    (hKT : H = kGenIn V H ⊔ T) : ¬ kGenIn V H ≤ Subgroup.normalizer (V : Set G) :=
  fun hKM => hH0 (isCalH0_of_le_normalizer hV hH (hKT.le.trans (sup_le hKM hTM)))

theorem eight_six_step_three_in {V H T : Subgroup G} (hV : IsElemAbelian 2 V) (hH : IsCalH V H)
    (hT : IsSylowIn 2 T (H ⊓ Subgroup.normalizer (V : Set G)))
    (hW : E3.wClos V 0 T ≠ V) (hKM : ¬ kGenIn V H ≤ Subgroup.normalizer (V : Set G))
    (hweak : ∀ h ∈ H, conjSubgroup V h ≤ T → conjSubgroup V h = V)
    (halt : ∀ U : Subgroup G, (∃ g : G, U = conjSubgroup V g) → U ≤ H →
      U ∈ omegaHIn V H ∨ ∀ W ∈ omegaHIn V H, ∀ u ∈ U, ∀ w ∈ W, u * w = w * u) :
    ¬ CentralizersInM V H T ∧ ¬ NormalizersInMTwo V H (E3.wClos V 0 T) := by
  have hKX : ∀ g : G, conjSubgroup V g ≤ T → conjSubgroup V g ≠ V →
      conjSubgroup V g ≤ Subgroup.centralizer (kGenIn V H : Set G) := by
    intro g hgT hgne
    have hgH : conjSubgroup V g ≤ H := hgT.trans (hT.le.trans inf_le_left)
    rcases halt (conjSubgroup V g) ⟨g, rfl⟩ hgH with ⟨h, hh, hgh⟩ | hcomm
    · exact absurd (hgh.trans (hweak h hh (hgh ▸ hgT))) hgne
    · have hK : kGenIn V H ≤ Subgroup.centralizer (conjSubgroup V g : Set G) := by
        refine iSup₂_le fun k hk => ?_
        intro w hw
        refine Subgroup.mem_centralizer_iff.mpr fun u hu => ?_
        exact hcomm (conjSubgroup V k) ⟨k, conjClosure_le_of_le_H hH.1 hk, rfl⟩ u hu w hw
      exact Subgroup.le_centralizer_iff.mpr hK
  exact not_centralizersInM_and_not_normalizersInMTwo hV hH hT hW (kGenIn_le_H hH.1) hKM hKX

end CFSG.LocalAnalysis.WeakClosure81

end
