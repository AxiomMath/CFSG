module

public import CFSG.LocalAnalysis.WeakClosure81.EightTwelveDefs

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique Subgroup
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

theorem isElemAbelian_eGrp_of_isCalH {V H T : Subgroup G} (hH : IsCalH V H)
    (hT : IsSylowIn 2 T (H ⊓ normalizer (V : Set G))) : IsElemAbelian 2 (eGrp H T) := by
  have hTH : IsSylowIn 2 T H := isSylowIn_of_isCalH hH hT
  have hO2T : pCoreOf 2 H ≤ T := pCoreOf_le_of_isCalH hH hT
  have hC : omegaOneCenterOf T ≤ omegaOneCenterOf (pCoreOf 2 H) := by
    intro c hc
    have hcT : c ∈ T := omegaOneCenterOf_le T hc
    have hcC : ∀ y ∈ T, y * c = c * y := fun y hy =>
      mem_centralizer_of_mem_omegaOneCenterOf hc hy
    have hcCen : c ∈ centralizer (pCoreOf 2 H : Set G) :=
      Subgroup.mem_centralizer_iff.mpr fun y hy => hcC y (hO2T hy)
    have hcO2 : c ∈ pCoreOf 2 H := hH.2.1 ⟨hTH.le hcT, hcCen⟩
    exact mem_omegaOneCenterOf hcO2 (fun y hy => hcC y (hO2T hy))
      ((B2F.isElemAbelian_omegaOneCenterOf T).2 c hc)
  have hEO : eGrp H T ≤ omegaOneCenterOf (pCoreOf 2 H) := by
    unfold eGrp
    refine conjClosure_le fun h hh c hc => ?_
    have hHnorm : H ≤ Subgroup.normalizer (omegaOneCenterOf (pCoreOf 2 H) : Set G) :=
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf (r := 2) H).trans
        (normalizer_le_normalizer_omegaOneCenterOf (pCoreOf 2 H))
    exact (Subgroup.mem_normalizer_iff.mp (hHnorm hh) c).1 (hC hc)
  exact CFSG.Open.IsElemAbelian.mono (B2F.isElemAbelian_omegaOneCenterOf (pCoreOf 2 H)) hEO

private theorem not_isCyclic_of_isElemAbelian_of_two_lt_card {A : Subgroup G}
    (hA : IsElemAbelian 2 A) (hcard : 2 < Nat.card A) : ¬ IsCyclic A := by
  intro hcyc
  obtain ⟨g, hg⟩ := hcyc.exists_generator
  have hg2 : g ^ 2 = 1 := Subtype.ext (by simpa using hA.2 g g.2)
  have hord : orderOf g = Nat.card A := orderOf_eq_card_of_forall_mem_zpowers hg
  have hle : orderOf g ≤ 2 := Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one hg2)
  omega

end CFSG.LocalAnalysis.WeakClosure81

end
