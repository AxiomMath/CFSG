module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtNoE9Z4P4USyl2
public import CFSG.Quasithin.EmptyFaithful.S146F23
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtNoE9Z4P4Rec
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtNoE9Z4P4UMod

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7 CFSG.Quasithin.C1Pack
  CFSG.Quasithin.CosetGeom CFSG.Quasithin.S1417
open scoped commutatorElement

section InvU

variable {G : Type} [Group G] [Finite G] {T M H PQ : Subgroup G} {p : ℕ} {R₁ R₂ : Subgroup G}
  {s : G}

theorem e9z4_isInvU (h35 : Lemma1435) (h5 : Stage1461Five) (S : Setting146 G T M)
    (hred : IsRedCE T M H PQ p) (hmax : PMaximal T M p) (hshape : IsE9Z4Shape T H p)
    (hdat : IsE9Dat T M H PQ R₁ R₂ s) (hF : oTwoUpper H ≤ oTwoFstarIn (mcOf T))
    (h16 : Subgroup.normalizer ((T ⊓ Subgroup.normalizer (R₁ : Set G) : Subgroup G) : Set G) ⊓
      mcOf T = T)
    {u : G} (hu : u ∈ uHi T M H R₁ ∨ u ∈ uHi T M H R₂) (huZ : u ∉ quasithinOmegaOneCenter T)
    (huT : T ⊓ Subgroup.normalizer (R₁ : Set G) ≤ tZero T u) : IsInvU T M H u := by
  classical
  have _hmax : PMaximal T M p := hmax
  obtain ⟨h98, hsplit, Q₁, Q₂, hstr, hpp, hR₁, hR₂⟩ := hdat.setup h35 S hred hshape
  subst hR₁ hR₂
  have hH : IsHTM T M H := hred.isHTM
  have hTH : T ≤ H := hH.1.1
  have hsw := inf_normalizer_HLb_swap h98.toHypF91 hTH rfl hstr hpp
  suffices key : ∀ {Qa Qb : Subgroup (MulAut ↥(kOf (rhoH h98.toHypF91)))},
      PlanePair ((T.subgroupOf H).map (resBeta (rhoH h98.toHypF91)))
        ((PQ.subgroupOf H).map (resBeta (rhoH h98.toHypF91))) Qa Qb →
      T ⊓ Subgroup.normalizer (HLb (resBeta (rhoH h98.toHypF91)) Qa : Set G) =
        T ⊓ Subgroup.normalizer (HLb (resBeta (rhoH h98.toHypF91)) Q₁ : Set G) →
      u ∈ uHi T M H (HLb (resBeta (rhoH h98.toHypF91)) Qa) → IsInvU T M H u by
    rcases hu with hu | hu
    · exact key hpp rfl hu
    · exact key hpp.symm hsw hu
  intro Qa Qb hp hQ hu
  have hidx : (T ⊓ Subgroup.normalizer (HLb (resBeta (rhoH h98.toHypF91)) Qa : Set G)).relIndex
      T = 2 := by
    rw [hQ]
    exact hdat.indexT
  have huT' : T ⊓ Subgroup.normalizer (HLb (resBeta (rhoH h98.toHypF91)) Qa : Set G) ≤
      tZero T u := by
    rw [hQ]
    exact huT
  have hT0 := tZero_eq_of_plane h98.toHypF91 hsplit rfl hstr hp hidx hu huZ huT'
  have hUu : u ∈ conjClosure (VZ T M) H := uHi_le_conjClosure (HLb_le _) hu
  refine ⟨hUu, isSylowTwoOf_tU_of_plane S hH h98.toHypF91 hsplit hstr hp hshape.2 hidx hu huZ hT0,
    ?_, ?_, ?_, ?_⟩
  · rw [hT0]
    exact hidx
  · obtain ⟨x, hx, hxu⟩ := exists_moves_self h98.toHypF91 hsplit hstr hp hu huZ
    exact not_mem_centralizer_pCoreOf_of_mem_oTwoFstarIn S h5 hH hUu
      (hF ((oTwoUpper_mono (HLb_le _)) hx)) hxu
  · intro t htT htn
    have htH : t ∈ H := hTH htT
    have hn : t ∉ Subgroup.normalizer
        (HLb (resBeta (rhoH h98.toHypF91)) Qa : Set G) := fun hn => htn (by
      rw [hT0]
      exact ⟨htT, hn⟩)
    have hyT : resBeta (rhoH h98.toHypF91) ⟨t, htH⟩ ∈
        (T.subgroupOf H).map (resBeta (rhoH h98.toHypF91)) :=
      Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr htT)
    have hyn : resBeta (rhoH h98.toHypF91) ⟨t, htH⟩ ∉
        Subgroup.normalizer (Qa : Set (MulAut ↥(kOf (rhoH h98.toHypF91)))) := fun hyn =>
      hn ((mem_normalizer_HLb_iff h98.toHypF91 (hp.1.trans hstr.P_le_X)).mpr hyn)
    have htc := hstr.conjBy_eq_of_not_mem_normalizer hp hyT hyn
    obtain ⟨x, hx, hxv⟩ := exists_moves_mul_conj h98.toHypF91 hsplit hstr hp hu huZ htH htc
    exact not_mem_centralizer_pCoreOf_of_mem_oTwoFstarIn S h5 hH
      ((conjClosure (VZ T M) H).mul_mem hUu (conj_mem_UH htH hUu))
      (hF ((oTwoUpper_mono (HLb_le _)) hx)) hxv
  · rw [hT0, hQ]
    exact h16

end InvU

end CFSG.Quasithin
