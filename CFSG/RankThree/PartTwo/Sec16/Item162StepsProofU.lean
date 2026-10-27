module

public import CFSG.RankThree.PartTwo.Sec17.RouteWire16
public import CFSG.RankThree.PartTwo.Sec16.Item163ProofR
public import CFSG.RankThree.PartTwo.Sec17.RouteForms
import CFSG.RankThree.PartTwo.Sec16.Item162StepsProofTools
import CFSG.CGT.PushingUp.TwoLocals
import CFSG.RankThree.PartTwo.Sec14.Item147

public section

namespace CFSG.RankThree.PartTwo.Sec16

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15
  CFSG.GH74.GLS

@[expose] def Step162UJ : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec15R G A c L → ∀ Y₁ Y₂ S₁ S₂ : Subgroup G, MaxCE162 A (lB A) Y₁ Y₂ S₁ S₂ →
      ¬ S₁ ≤ S₂ → ¬ S₂ ≤ S₁ →
      ¬ TransOn A (lB A) (xA A)
          (delta A (lB A) (Subgroup.normalizer ((S₁ ⊓ S₂ : Subgroup G) : Set G))) →
      ∃ J ∈ scriptY0 A (lB A),
        J ≤ delta A (lB A) (Subgroup.normalizer ((S₁ ⊓ S₂ : Subgroup G) : Set G)) ∧ omg155 A J

namespace Proof162

variable {G : Type} [Group G] [Finite G] {A : Subgroup G}

theorem card_lt_and_mem_of_lt {Y S U : Subgroup G} (hS : S ∈ scriptQPi A (lB A) Y (piOf 2))
    (hAU : A ≤ Subgroup.normalizer (U : Set G)) (hUS : U ≤ S) (hne : U ≠ S) :
    Nat.card U < Nat.card (S ⊓ Subgroup.normalizer (U : Set G) : Subgroup G) ∧
      S ⊓ Subgroup.normalizer (U : Set G) ∈
        scriptQPi A (lB A) (delta A (lB A) (Subgroup.normalizer (U : Set G))) (piOf 2) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hS2 : IsPGroup 2 S := isPGroup_of_mem_scriptQPi Nat.prime_two hS
  obtain ⟨x, hxS, hxU, hxN⟩ := Late.exists_mem_normalizer_not_mem_of_lt hS2 (lt_of_le_of_ne hUS hne)
  have hlt : U < S ⊓ Subgroup.normalizer (U : Set G) := by
    refine lt_of_le_of_ne (le_inf hUS Subgroup.le_normalizer) fun heq => hxU ?_
    rw [heq]
    exact ⟨hxS, hxN⟩
  have hAT : A ≤ Subgroup.normalizer ((S ⊓ Subgroup.normalizer (U : Set G) : Subgroup G) : Set G) :=
    Late.le_normalizer_inf hS.1.1.1.2.2 (hAU.trans (Sec6.normalizer_le_normalizer_normalizer U))
  have hTQ : S ⊓ Subgroup.normalizer (U : Set G) ∈ scriptQ A (lB A) :=
    mem_scriptQ_of_le hS.1.1 inf_le_left hAT
  refine ⟨Subgroup.card_lt_of_lt hlt, ⟨hTQ, le_delta hTQ inf_le_right⟩, fun q hq => ?_⟩
  exact hS.2 q (hq.trans (Subgroup.card_dvd_of_le inf_le_left))

theorem delta_normalizer_le_of_omg155 (h155 : Item155 A (lB A)) {U : Subgroup G}
    (hU2 : IsPGroup 2 U) (hU1 : U ≠ ⊥) (hAU : A ≤ Subgroup.normalizer (U : Set G))
    {J I : Subgroup G} (hJ : J ∈ scriptY0 A (lB A))
    (hJK : J ≤ delta A (lB A) (Subgroup.normalizer (U : Set G))) (hΩ : omg155 A J)
    (hI : I ∈ scriptY0Star A (lB A)) (hJI : J ≤ I) :
    delta A (lB A) (Subgroup.normalizer (U : Set G)) ≤ Subgroup.normalizer (I : Set G) := by
  obtain ⟨M, hNM, hM⟩ := CFSG.CGT.PushingUp.exists_isMaximalTwoLocal_ge
    (CFSG.CGT.PushingUp.isPLocal_normalizer_of_isPGroup hU2 hU1)
  have hJ3 : J = oPrimeResidualOf 3 J := hJ.1.2.1
  have hJY3 : J ∈ scriptY3 A (lB A) := ⟨hJ.2, hJ.1.2.2.1⟩
  have hX4 : oPrimeResidualOf 3 J ∈ scriptY4 A (lB A) := by
    rw [← hJ3]
    exact hJ.1
  have hcov : J = oPrimeResidualOf 3 J ⊔ CFSG.Open.pCoreOf 2 J := by
    rw [← hJ3]
    exact (sup_eq_left.mpr (CFSG.LieType.BorelTits.pCoreOf_le 2 J)).symm
  have hIΓ : I ∈ gam155 A (lB A) J (oPrimeResidualOf 3 J) := by
    rw [← hJ3]
    exact ⟨hI, hJI, hJI.trans Subgroup.le_normalizer⟩
  have hMm : M ∈ CFSG.maximalTwoLocalsContaining ((A ⊔ J : Subgroup G) : Set G) :=
    ⟨hM, fun x hx => hNM (sup_le hAU (hJK.trans (delta_le _)) hx)⟩
  have hΩ' : omg155 A (oPrimeResidualOf 3 J) := by
    rw [← hJ3]
    exact hΩ
  exact (delta_mono hNM).trans ((h155 J hJY3 hX4 hcov).2 I hIΓ (Or.inl hΩ') M hMm)

theorem le_of_maxCE162 (h153 : Item153Main A (lB A)) (hobs : Claim153Obs A (lB A))
    (h1411 : Item1411_1 A (lB A)) (h155 : Item155 A (lB A)) {Y₁ Y₂ S₁ S₂ : Subgroup G}
    (hmax : MaxCE162 A (lB A) Y₁ Y₂ S₁ S₂)
    (hJ : ¬ S₁ ≤ S₂ → ¬ S₂ ≤ S₁ →
      ¬ TransOn A (lB A) (xA A)
          (delta A (lB A) (Subgroup.normalizer ((S₁ ⊓ S₂ : Subgroup G) : Set G))) →
      ∃ J ∈ scriptY0 A (lB A),
        J ≤ delta A (lB A) (Subgroup.normalizer ((S₁ ⊓ S₂ : Subgroup G) : Set G)) ∧
          omg155 A J) :
    S₁ ≤ S₂ := by
  by_contra h12
  obtain ⟨hY₁, hY₂, hS₁, hS₂, -, hnc⟩ := hmax.1
  have hS₁G := mem_qStarTop_of_mem_qStarN h153 hobs hY₁ hS₁
  have hS₂G := mem_qStarTop_of_mem_qStarN h153 hobs hY₂ hS₂
  have h21 : ¬ S₂ ≤ S₁ := fun h21 =>
    h12 (hS₂G.2 (⟨⟨hS₁.prop.1.1, le_top⟩, hS₁.prop.2⟩ : S₁ ∈ scriptQPi A (lB A) ⊤ (piOf 2)) h21)
  have hAU : A ≤ Subgroup.normalizer ((S₁ ⊓ S₂ : Subgroup G) : Set G) :=
    Late.le_normalizer_inf hS₁.prop.1.1.1.2.2 hS₂.prop.1.1.1.2.2
  obtain ⟨hlt₁, hT₁⟩ := card_lt_and_mem_of_lt hS₁.prop hAU inf_le_left fun h => h12 (by
    rw [← h]
    exact inf_le_right)
  obtain ⟨hlt₂, hT₂⟩ := card_lt_and_mem_of_lt hS₂.prop hAU inf_le_right fun h => h21 (by
    rw [← h]
    exact inf_le_left)
  set U := S₁ ⊓ S₂ with hU
  set K := delta A (lB A) (Subgroup.normalizer (U : Set G)) with hKdef
  have hnt : ¬ TransOn A (lB A) (xA A) K := by
    intro htr
    obtain ⟨T₁', hT₁T₁', hT₁'⟩ :=
      Finite.exists_le_maximal (p := (· ∈ scriptQPi A (lB A) K (piOf 2))) hT₁
    obtain ⟨T₂', hT₂T₂', hT₂'⟩ :=
      Finite.exists_le_maximal (p := (· ∈ scriptQPi A (lB A) K (piOf 2))) hT₂
    obtain ⟨x, hx, hxT⟩ := htr T₁' hT₁' T₂' hT₂'
    have hxX : x ∈ xA A := (Subgroup.mem_inf.mp hx).1
    have hxW : x ∈ Subgroup.normalizer (A : Set G) := xA_le_normalizer A hxX
    obtain ⟨V, hT₁'V, hV⟩ := Finite.exists_le_maximal
      (p := (· ∈ scriptQPi A (lB A) ⊤ (piOf 2)))
      (⟨⟨hT₁'.prop.1.1, le_top⟩, hT₁'.prop.2⟩ : T₁' ∈ scriptQPi A (lB A) ⊤ (piOf 2))
    obtain ⟨w, hw, hVeq⟩ := h1411 S₁ hS₁G V hV
    have hwW : w ∈ Subgroup.normalizer (A : Set G) := (Subgroup.mem_inf.mp hw).1
    have hVN : V ∈ scriptQPiStar A (lB A)
        (Subgroup.normalizer ((Y₁.map (MulAut.conj w).toMonoidHom : Subgroup G) : Set G))
        (piOf 2) := by
      have h1 := Sec17.HeadProof.map_conj_mem_scriptQPiStar hwW hS₁
      rwa [Subgroup.map_equiv_normalizer_eq, ← hVeq] at h1
    have hY₁w := map_conj_mem_scriptY0Star hwW hY₁
    have hc1 := conj_of_card_lt hmax hY₁ hY₁w hS₁ hVN (lt_of_lt_of_le hlt₁
      (Subgroup.card_le_of_le (le_inf inf_le_left (hT₁T₁'.trans hT₁'V))))
    have hY₂x := map_conj_mem_scriptY0Star (inv_mem hxW) hY₂
    have hS₂x : S₂.map (MulAut.conj x⁻¹).toMonoidHom ∈ scriptQPiStar A (lB A)
        (Subgroup.normalizer ((Y₂.map (MulAut.conj x⁻¹).toMonoidHom : Subgroup G) : Set G))
        (piOf 2) := by
      have h1 := Sec17.HeadProof.map_conj_mem_scriptQPiStar (inv_mem hxW) hS₂
      rwa [Subgroup.map_equiv_normalizer_eq] at h1
    have hT₂le : (S₂ ⊓ Subgroup.normalizer (U : Set G)).map (MulAut.conj x⁻¹).toMonoidHom ≤
        V ⊓ S₂.map (MulAut.conj x⁻¹).toMonoidHom := by
      refine le_inf ?_ (Subgroup.map_mono inf_le_left)
      calc (S₂ ⊓ Subgroup.normalizer (U : Set G)).map (MulAut.conj x⁻¹).toMonoidHom
          ≤ T₂'.map (MulAut.conj x⁻¹).toMonoidHom := Subgroup.map_mono hT₂T₂'
        _ = T₁' := by rw [hxT, Late.map_conj_map_conj, inv_mul_cancel, Late.map_conj_one]
        _ ≤ V := hT₁'V
    have hcard₂ : Nat.card ((S₂ ⊓ Subgroup.normalizer (U : Set G)).map
        (MulAut.conj x⁻¹).toMonoidHom : Subgroup G) =
        Nat.card (S₂ ⊓ Subgroup.normalizer (U : Set G) : Subgroup G) :=
      Subgroup.card_map_of_injective (MulAut.conj x⁻¹).injective
    have hc2 := conj_of_card_lt hmax hY₁w hY₂x hVN hS₂x (lt_of_lt_of_le hlt₂
      (hcard₂ ▸ Subgroup.card_le_of_le hT₂le))
    obtain ⟨x₁, hx₁, h₁⟩ := hc1
    obtain ⟨x₂, hx₂, h₂⟩ := hc2
    obtain ⟨z, hz, hzY⟩ := conj_trans hx₁ hx₂ h₁ h₂
    exact hnc (conj_trans hz (inv_mem hxX) hzY rfl)
  obtain ⟨J, hJ0, hJK, hJΩ⟩ := hJ h12 h21 hnt
  obtain ⟨I, hJI, hI⟩ := Finite.exists_le_maximal (p := (· ∈ scriptY0 A (lB A))) hJ0
  have hU2 : IsPGroup 2 U :=
    (isPGroup_of_mem_scriptQPi Nat.prime_two hS₁.prop).to_le inf_le_left
  have hKI : K ≤ Subgroup.normalizer (I : Set G) :=
    delta_normalizer_le_of_omg155 h155 hU2 hmax.1.ne_bot hAU hJ0 hJK hJΩ hI hJI
  have conjI : ∀ {Yi Si : Subgroup G}, Yi ∈ scriptY0Star A (lB A) →
      Si ∈ scriptQPiStar A (lB A) (Subgroup.normalizer (Yi : Set G)) (piOf 2) →
      Si ⊓ Subgroup.normalizer (U : Set G) ∈ scriptQPi A (lB A) K (piOf 2) →
      Nat.card U < Nat.card (Si ⊓ Subgroup.normalizer (U : Set G) : Subgroup G) →
      ∃ x ∈ xA A, Yi = I.map (MulAut.conj x).toMonoidHom := by
    intro Yi Si hYi hSi hT hlt
    obtain ⟨SI, hTSI, hSI⟩ := Finite.exists_le_maximal
      (p := (· ∈ scriptQPi A (lB A) (Subgroup.normalizer (I : Set G)) (piOf 2)))
      (⟨⟨hT.1.1, hT.1.2.trans hKI⟩, hT.2⟩ :
        Si ⊓ Subgroup.normalizer (U : Set G) ∈
          scriptQPi A (lB A) (Subgroup.normalizer (I : Set G)) (piOf 2))
    exact conj_of_card_lt hmax hYi hI hSi hSI
      (lt_of_lt_of_le hlt (Subgroup.card_le_of_le (le_inf inf_le_left hTSI)))
  obtain ⟨x₁, hx₁, h₁⟩ := conjI hY₁ hS₁ hT₁ hlt₁
  obtain ⟨x₂, hx₂, h₂⟩ := conjI hY₂ hS₂ hT₂ hlt₂
  obtain ⟨y₂, hy₂, h₂'⟩ := conj_symm hx₂ h₂
  exact hnc (conj_trans hx₁ hy₂ h₁ h₂')

end Proof162

theorem step162UR_of (h153 : Item153MainR) (hobs : Claim153ObsR) (h1411 : Item1411_1R)
    (h155 : Item155R) (hJ : Step162UJ) : Step162UR := by
  intro G _ _ A c₀ L₀ _ c L hR Y₁ Y₂ S₁ S₂ hmax
  exact Proof162.le_of_maxCE162 (h153 G A c L hR) (hobs G A c L hR) (h1411 G A c L hR)
    (h155 G A c L hR) hmax (hJ G A c L hR Y₁ Y₂ S₁ S₂ hmax)

end CFSG.RankThree.PartTwo.Sec16
