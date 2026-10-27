module

public import CFSG.Quasithin.EmptyFaithful.S151XF

public section

namespace CFSG.Quasithin.S151S9U

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Assembly.LowTwoRank
open CFSG.LieType.BorelTits

variable {G : Type} [Group G] [Finite G]

theorem inH_mZ_sup {T Mc M Z₁ Z₂ V₁ V₂ L : Subgroup G} (hc : Ctx15120 T Mc M Z₁ Z₂ V₁ V₂ L) :
    InH T (mZ1516 Mc Z₁ ⊔ T) := by
  refine ⟨le_sup_right, ?_⟩
  have hQne : q1_1516 Mc Z₁ ≠ ⊥ := hc.h18.five.2.2.radical.2.1
  have hQH : q1_1516 Mc Z₁ ≤ mZ1516 Mc Z₁ ⊔ T := (q1_1516_le Mc Z₁).trans le_sup_left
  have hHN : mZ1516 Mc Z₁ ⊔ T ≤ Subgroup.normalizer (q1_1516 Mc Z₁ : Set G) :=
    sup_le (le_normalizer_pCoreOf 2 _) hc.h18.three
  have hle : q1_1516 Mc Z₁ ≤ pCoreOf 2 (mZ1516 Mc Z₁ ⊔ T) :=
    le_pCoreOf_of_le_normalizer 2 hQH hHN (pCoreOf_isPGroup 2 _)
  intro h
  exact hQne (le_bot_iff.mp (h ▸ hle))

theorem false_of_block_not_centralizing {T Mc M Z₁ Z₂ V₁ V₂ L : Subgroup G}
    (hc : Ctx15120 T Mc M Z₁ Z₂ V₁ V₂ L) (hTMz : T ≤ Subgroup.normalizer (mZ1516 Mc Z₁ : Set G))
    {K : Subgroup G} (hK : K ∈ cComp K)
    (hKM : K ≤ mZ1516 Mc Z₁) (hKn : (K.subgroupOf (mZ1516 Mc Z₁)).Normal) {z : G}
    (hz : z ∈ quasithinOmegaOneCenter T) (hKz : ¬ K ≤ Subgroup.centralizer ({z} : Set G)) :
    False := by
  have hq := hc.ctx.qtfe
  obtain ⟨S₂, hS₂⟩ := hq.exists_sylow
  subst hS₂
  have hEven : quasithinEvenCharacteristic G := hq.qtke.2.1
  have hH : InH (S₂ : Subgroup G) (mZ1516 Mc Z₁ ⊔ (S₂ : Subgroup G)) := inH_mZ_sup hc
  have hmZH : IsSubnormal (mZ1516 Mc Z₁) (mZ1516 Mc Z₁ ⊔ (S₂ : Subgroup G)) :=
    A3.subnormal_of_normal le_sup_left
      ((Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).mpr
        (sup_le Subgroup.le_normalizer hTMz))
  have hKH : IsSubnormal K (mZ1516 Mc Z₁ ⊔ (S₂ : Subgroup G)) :=
    A3.subnormal_trans (A3.subnormal_of_normal hKM hKn) hmZH
  have hKc : K ∈ cComp (mZ1516 Mc Z₁ ⊔ (S₂ : Subgroup G)) := cComp_mem_of_subnormal hKH hK
  have hzZ : Subgroup.zpowers z ≤ quasithinOmegaOneCenter (S₂ : Subgroup G) :=
    (Subgroup.zpowers_le).mpr hz
  have hV : IsTwoReducedIn (mZ1516 Mc Z₁ ⊔ (S₂ : Subgroup G))
      (conjClosure (Subgroup.zpowers z) (mZ1516 Mc Z₁ ⊔ (S₂ : Subgroup G))) :=
    isTwoReducedIn_conjClosure (mZ1516 Mc Z₁ ⊔ (S₂ : Subgroup G)) S₂ le_sup_right
      (charTwo_of_inH hEven S₂ hH) hzZ
  have hne : ⁅conjClosure (Subgroup.zpowers z) (mZ1516 Mc Z₁ ⊔ (S₂ : Subgroup G)), K⁆ ≠ ⊥ := by
    intro h0
    apply hKz
    have hzV : z ∈ conjClosure (Subgroup.zpowers z) (mZ1516 Mc Z₁ ⊔ (S₂ : Subgroup G)) :=
      le_conjClosure _ _ (Subgroup.mem_zpowers z)
    have hle : conjClosure (Subgroup.zpowers z) (mZ1516 Mc Z₁ ⊔ (S₂ : Subgroup G)) ≤
        Subgroup.centralizer (K : Set G) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mp h0
    intro k hk
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (Subgroup.mem_centralizer_iff.mp (hle hzV) k hk)
  exact hq.faithful_empty K (isFaithfulLocal_of_commutator_ne_bot hEven S₂ hH hKc hV hne)

end CFSG.Quasithin.S151S9U
