module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.TwelveTen
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.TwelveSevenP
import CFSG.LocalAnalysis.QuasithinUnique.CharTwoTransport
import CFSG.Quasithin.Background.A4V

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
  CFSG.LocalAnalysis.WeakClosure81

variable {G : Type} [Group G] [Finite G]

namespace TwelveEleven

theorem fstar_eq_pCoreOf_of_charTwo {H : Subgroup G} (hH : CFSG.QuasithinUnique.CharTwo H) :
    Fstar H = pCoreOf 2 H := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := (CFSG.isCharacteristicP_iff_generalizedFitting_eq_pCore ↥H 2).1
    (CFSG.QuasithinUnique.charTwo_iff_isCharacteristicP.1 hH)
  unfold Fstar pCoreOf
  rw [CFSG.Adapters.genFittingFStar_eq_foundations, h]

theorem fstar_sup_eq_pCoreOf (D : Data G) {X : Subgroup G} (hXM : X ≤ D.M) :
    Fstar (X ⊔ D.T) = pCoreOf 2 (X ⊔ D.T) := by
  have hTM : IsSylowIn 2 D.T D.M := TwelveShort.isSylowIn_of_le D D.sylowM.le
  have hOM := CFSG.LieType.BorelTits.pCoreOf_le 2 D.M
  have hOT : pCoreOf 2 D.M ≤ D.T :=
    IsSylowIn.le_of_normal hTM hOM
      ((Subgroup.normal_subgroupOf_iff_le_normalizer hOM).2
        (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 D.M))
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 D.M)
  exact fstar_eq_pCoreOf_of_charTwo (CFSG.QuasithinUnique.CharTwo.of_pCoreOf_le
    (D.standing.charTwo D.M D.maxLocal.1) (sup_le hXM D.sylowM.le) (hOT.trans le_sup_right))

theorem rankThreeGamma_centerOf_le (D : Data G) (hcu : CentralizersUnique D.M D.T) :
    rankThreeGamma 1 2 (centerOf D.T) ≤ D.M := by
  refine rankThreeGamma_le_of_normalizer_le (fun A hA hA1 => ?_) le_rfl
  obtain ⟨⟨z, hzA⟩, hz1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hA1
  have hz1' : z ≠ 1 := fun h => hz1 (Subtype.ext h)
  intro x hx
  have hzZ : z ∈ centerOf D.T := hA hzA
  have hw : x * z * x⁻¹ ∈ centerOf D.T := hA ((Subgroup.mem_normalizer_iff.1 hx z).1 hzA)
  have hw1 : x * z * x⁻¹ ≠ 1 := by
    intro h1
    apply hz1'
    calc z = x⁻¹ * (x * z * x⁻¹) * x := by group
      _ = 1 := by rw [h1]; group
  have hcomm : ∀ y ∈ centerOf D.T, ∀ t ∈ D.T, y * t = t * y := fun y hy t ht =>
    (Subgroup.mem_centralizer_iff.1 hy.2 t ht).symm
  have hCw := (hcu _ hw.1 (hcomm _ hw) hw1).1
  have hz2 := (hcu z hzZ.1 (hcomm z hzZ) hz1').2
  by_contra hxM
  apply hz2 x⁻¹ (fun h => hxM (by simpa using D.M.inv_mem h))
  intro c hc
  refine ⟨x * c * x⁻¹, hCw ?_, ?_⟩
  · rw [Subgroup.mem_centralizer_singleton_iff] at hc ⊢
    calc x * c * x⁻¹ * (x * z * x⁻¹) = x * (c * z) * x⁻¹ := by group
      _ = x * (z * c) * x⁻¹ := by rw [hc]
      _ = x * z * x⁻¹ * (x * c * x⁻¹) := by group
  · simp [MulAut.conj_apply, mul_assoc]

end TwelveEleven

open TwelveShort

theorem twelve_eleven_one (D : Data G) (hx : DataExt D) (h61 : UC6.R6_1 D) (h63 : UC6.R6_3 D)
    (h66 : UC6.R6_6 D) (h127 : R127 D) (h1114 : R1114 D) (h183 : W3Thm183 G)
    (h193 : W3Thm193 G) {V₀ V : Subgroup G} (h : Hyp125 D V₀ V)
    (hP : ∃ X : Subgroup G, F11.InP11 D X) (hV₀ : V₀ ≠ ⊥) :
    ¬ MBarGT D.M V₀ V (D.k + 1) := by
  intro hm
  obtain ⟨X, hX⟩ := hP
  have hs := weakClosureSetting_of_hyp125 D hx h61 h127 h1114 h hV₀
  obtain ⟨h0, hcu, -⟩ : InCalV0 D.M V₀ V ∧ CentralizersUnique D.M D.T ∧
      ∀ W : Subgroup G, ¬ InCalW D.M D.T W := by
    rcases h.1 with ⟨-, h0⟩ | h2
    · exact absurd h0 hV₀
    · exact h2
  obtain ⟨p, hp, hp2, hXM, hXp, hexp, hXnc, hperm, hΓX, -⟩ := id hX
  have hm2 : MBarGT D.M V₀ V 2 := mBarGT_mono hm (by have := one_le_k D; omega)
  rcases h193 D V₀ V hs hV₀ p X hp hp2 hXp hXnc hexp
      (fun g hg hg0 => TwelveSeven.inf_conjSubgroup_eq_bot D h63 hX h0.1 hg hg0)
      (inCalU_of_inP11 D h63 hp hp2 hXM hXp hexp hΓX) hperm
      (sup_le hXM D.sylowM.le) (TwelveEleven.fstar_sup_eq_pCoreOf D hXM) hm2
      (TwelveEleven.rankThreeGamma_centerOf_le D hcu) with h1 | h2
  · exact twelve_ten_one_zero D hx h61 h66 h127 h1114 h183 h hV₀ hm2 h1
  · exact twelve_ten_one D hx h61 h66 h127 h1114 h183 h hV₀ hm
      ((CFSG.Quasithin.A4.normalizer_le_normalizer_omegaOneCenterOf _).trans h2)

theorem twelve_eleven_two (D : Data G) (h63 : UC6.R6_3 D) (h126 : R126 D) (h111 : W3Thm111 G)
    {V₀ V : Subgroup G} (h : Hyp125 D V₀ V) (hP : ∃ X : Subgroup G, F11.InP11 D X)
    (hV₀ : V₀ = ⊥) : ¬ MBarGT D.M V₀ V (D.k + 2) := by
  subst hV₀
  intro hm
  obtain ⟨X, hX⟩ := hP
  rcases h.1 with ⟨hW, -⟩ | ⟨h0, -, -⟩
  · have hV1 : InCalV1 D.M D.T V := hW.1.1
    have hVV : InCalV D.M V := hV1.1
    have hV' : IsElemAbelian 2 V := hVV.2.2.2
    have hm2 : MBarGT D.M ⊥ V 2 := mBarGT_mono hm (by omega)
    have hgt : D.k + 2 < E3.sParam hV' := lt_sParam_of_mBarGT D h111 hV1 hm2 hm
    obtain ⟨H₀, hmin⟩ := h.exists_hyp124Min
    have hS : IsSylowIn 2 D.T H₀ := isSylowIn_of_le D hmin.1.1
    have hE : E1.InE D.k H₀ := h126 H₀ hmin
    have hW0 : E3.wClos V 0 D.T ≠ ⊥ := wClos_zero_ne_bot D hVV
    obtain ⟨p, hp, hp2, hXM, hXp, hexp, hnc, hperm, hΓ, -⟩ := hX
    exact hmin.1.2.1 (six_sixteen_two_uncond hV' D.maxLocal hS (one_le_k D) hE hW0 hgt hp hp2
      hXM hnc hexp hperm (inCalU_of_inP11 D h63 hp hp2 hXM hXp hexp hΓ))
  · exact absurd rfl h0.1.1

theorem r1211_1_of_twelve_eleven (D : Data G) (hx : DataExt D) (h61 : UC6.R6_1 D)
    (h63 : UC6.R6_3 D) (h66 : UC6.R6_6 D) (h127 : R127 D) (h1114 : R1114 D)
    (h183 : W3Thm183 G) (h193 : W3Thm193 G) : R1211_1 D :=
  fun _ _ h hP hV₀ => twelve_eleven_one D hx h61 h63 h66 h127 h1114 h183 h193 h hP hV₀

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
