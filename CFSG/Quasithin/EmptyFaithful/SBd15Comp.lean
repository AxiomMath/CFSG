module

public import CFSG.Quasithin.EmptyFaithful.S153R33
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public section

namespace CFSG.Quasithin.SBd15

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped commutatorElement

theorem le_centralizer_of_isPerfect_of_card_le_four {G : Type} [Group G] [Finite G] {V K : Subgroup G}
    (hV : Nat.card ↥V ≤ 4) (hKN : K ≤ Subgroup.normalizer (V : Set G)) (hK : ⁅K, K⁆ = K) :
    K ≤ Subgroup.centralizer (V : Set G) := by
  classical
  have hperf : Group.IsPerfect ↥K := Subgroup.isPerfect_iff.mpr hK
  let ψ : ↥K →* MulAut ↥V := V.normalizerMonoidHom.comp (Subgroup.inclusion hKN)
  have hsolv : Group.IsSolvable (MulAut ↥V) := by
    have h1 : Group.IsSolvable (Equiv.Perm ↥V) := Equiv.Perm.isSolvable hV
    exact Group.isSolvable_of_isSolvable_injective (f := MulAut.toPerm ↥V)
      (fun a b h => MulEquiv.ext fun x => congrArg (fun p => p x) h)
  have h2 : Group.IsPerfect ↥ψ.range := Group.IsPerfect.range ψ
  have h3 : Group.IsSolvable ↥ψ.range := inferInstance
  have h4 : ∀ k : ↥K, ψ k = 1 := fun k =>
    congrArg Subtype.val (S153D.eq_one_of_isPerfect_of_isSolvable (⟨ψ k, ⟨k, rfl⟩⟩ : ↥ψ.range))
  intro k hk
  have h5 : (⟨k, hKN hk⟩ : ↥(Subgroup.normalizer (V : Set G))) ∈ V.normalizerMonoidHom.ker :=
    MonoidHom.mem_ker.mpr (h4 ⟨k, hk⟩)
  rw [Subgroup.normalizerMonoidHom_ker] at h5
  exact Subgroup.mem_subgroupOf.mp h5

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ Yp I : Subgroup G} {t : G}

theorem charTwo_sup_of_le (h113 : StageLemma14113) (c : CtxComp T Mc M V₁ V₂ Yp I t) {K : Subgroup G}
    (hKI : K ≤ I) (hN : Yp ⊔ Sgp153 T V₁ ≤ Subgroup.normalizer (K : Set G)) (hcK : CharTwo K)
    (hnot : ¬ K ≤ M ⊓ I) : CharTwo (K ⊔ (Yp ⊔ Sgp153 T V₁)) := by
  have hXn : K ⊔ (Yp ⊔ Sgp153 T V₁) ≤ Subgroup.normalizer (K : Set G) :=
    sup_le Subgroup.le_normalizer hN
  have hKne : K ≠ ⊥ := fun hb => hnot (hb ▸ bot_le)
  have hO₂ : pCoreOf 2 K ≠ ⊥ := by
    intro hb
    apply hKne
    have h1 : K ⊓ Subgroup.centralizer (pCoreOf 2 K : Set G) ≤ pCoreOf 2 K := hcK
    rw [hb] at h1
    rw [eq_bot_iff]
    intro x hx
    refine Subgroup.mem_bot.mpr (Subgroup.mem_bot.mp (h1 ⟨hx, Subgroup.mem_centralizer_iff.2 fun y hy => ?_⟩))
    rw [show (y : G) = 1 from by simpa using hy, mul_one, one_mul]
  have hO₂X : pCoreOf 2 K ≤ pCoreOf 2 (K ⊔ (Yp ⊔ Sgp153 T V₁)) :=
    le_pCoreOf_of_le_normalizer 2 ((pCoreOf_le 2 K).trans le_sup_left)
      (hXn.trans (normalizer_le_normalizer_pCoreOf 2 K)) (pCoreOf_isPGroup 2 K)
  have hX : IsHPlus Yp (Sgp153 T V₁) M (K ⊔ (Yp ⊔ Sgp153 T V₁)) :=
    ⟨⟨le_sup_right, fun hb => hO₂ (le_bot_iff.mp (hO₂X.trans hb.le))⟩,
      fun hXM => hnot (le_inf (le_sup_left.trans hXM) hKI)⟩
  have hodd : oddCoreIn (K ⊔ (Yp ⊔ Sgp153 T V₁)) = ⊥ :=
    S153D.input15311Eight_of_stages h113 G T Mc M V₁ V₂ Yp t c.hyp _ hX
  have hsolv : Group.IsSolvable ↥(Yp ⊔ Sgp153 T V₁) := S153D.isSolvable_Yp_sup' h113 c.hyp
  refine DoubleA3.charTwo_of_no_component (fun K' hK' => ?_) hodd
  have hperf : Group.IsPerfect ↥K' := (BenderBranch.isQuasisimple_of_isComponentIn hK').1
  have hK'K : K' ≤ K := S153R.le_of_isPerfect_of_le_sup_solvable hN hK'.1
  exact DoubleA3.not_isComponentIn_of_charTwo hcK K'
    (BenderBranch.isComponentIn_of_le hK' hK'K le_sup_left)

theorem le_M_of_charTwo (h113 : StageLemma14113) (h25 : Stage15325)
    (c : CtxComp T Mc M V₁ V₂ Yp I t) {K : Subgroup G} (hKI : K ≤ I)
    (hN : Yp ⊔ Sgp153 T V₁ ≤ Subgroup.normalizer (K : Set G)) (hcK : CharTwo K) : K ≤ M ⊓ I := by
  by_contra hnle
  have hCX := charTwo_sup_of_le h113 c hKI hN hcK hnle
  have hV₁ne : ∃ v ∈ V₁, v ≠ 1 := by
    have hV₁b : V₁ ≠ ⊥ := by
      intro hb
      have := c.hyp.decomp.card₁
      rw [hb, Subgroup.card_bot] at this
      omega
    obtain ⟨⟨v, hv⟩, hv1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hV₁b
    exact ⟨v, hv, fun h1 => hv1 (Subtype.ext h1)⟩
  have hV₁S : V₁ ≤ Sgp153 T V₁ :=
    le_inf (c.hyp.decomp.le₁.trans c.hyp.hyp.VZ_le_T) Subgroup.le_normalizer
  have hX : IsHPlus Yp (Sgp153 T V₁) M (K ⊔ (Yp ⊔ Sgp153 T V₁)) := by
    refine ⟨⟨le_sup_right, ?_⟩, fun hXM => hnle (le_inf (le_sup_left.trans hXM) hKI)⟩
    intro hb
    obtain ⟨v, hv, hv1⟩ := hV₁ne
    have hvX : v ∈ K ⊔ (Yp ⊔ Sgp153 T V₁) :=
      Subgroup.mem_sup_right (Subgroup.mem_sup_right (hV₁S hv))
    have h1 : (K ⊔ (Yp ⊔ Sgp153 T V₁)) ⊓
        Subgroup.centralizer (pCoreOf 2 (K ⊔ (Yp ⊔ Sgp153 T V₁)) : Set G) ≤
        pCoreOf 2 (K ⊔ (Yp ⊔ Sgp153 T V₁)) := hCX
    rw [hb] at h1
    refine hv1 (Subgroup.mem_bot.mp (h1 ⟨hvX, Subgroup.mem_centralizer_iff.2 fun y hy => ?_⟩))
    rw [show (y : G) = 1 from by simpa using hy, mul_one, one_mul]
  exact h25 G T Mc M V₁ V₂ Yp t c.hyp _ hX hCX

theorem concl15333_of_isComponentIn (h11 : StageLemma14111) (h113 : StageLemma14113)
    (h25 : Stage15325) (c : CtxComp T Mc M V₁ V₂ Yp I t) {L : Subgroup G} (hL : IsComponentIn L I) :
    Concl15333 T M V₁ Yp I L := by
  have hq : CFSG.IsQuasisimple ↥L := BenderBranch.isQuasisimple_of_isComponentIn hL
  obtain ⟨z, hz, hz1, hZ⟩ := S153H.exists_generator_Z c.hyp.hyp
  have h115 := S153H.lemma115Hyp_of_ctx h11 h113 c hz hz1 hZ
  have hSI : Sgp153 T V₁ ≤ I := le_sup_right.trans c.inH.1.1
  refine
    { mem := Id2519.mem_cComp_of_isComponentIn hL
      quasisimple := hq
      center_eq := S153H.centerOf_eq_pCoreOf_of_isComponentIn c.oddCore hL
      not_le := S153H.not_le_M_of_isComponentIn c hL
      inv_le := ?_
      comp_prop := ?_ }
  · intro L₁ hL₁ hN hchar
    have hL₁I : L₁ ≤ I := hL₁.trans (conjClosure_le fun s hs l hl =>
      I.mul_mem (I.mul_mem (hSI hs) (hL.1 hl)) (I.inv_mem (hSI hs)))
    exact le_M_of_charTwo h113 h25 c hL₁I hN hchar
  · intro K hKc
    obtain ⟨-, hcomm, -, hchar⟩ := h115.component_action hKc
    have hcent : Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) =
        Subgroup.centralizer {z} := by
      rw [hZ]
      exact S153H.centralizer_zpowers_eq z
    refine ⟨S153H.not_le_M_of_isComponentIn c hKc, ?_, ?_, ?_⟩
    · rw [hZ]
      exact hcomm
    · exact le_bot_iff.mp ((S153H.oddCoreIn_le_of_isComponentIn hKc).trans c.oddCore.le)
    · rw [hcent]
      exact hchar

end CFSG.Quasithin.SBd15
