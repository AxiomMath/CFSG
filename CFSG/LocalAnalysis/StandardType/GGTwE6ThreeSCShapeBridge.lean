module

public import CFSG.LocalAnalysis.StandardType.GGTwE6ThreeFrameDescent
public import CFSG.LocalAnalysis.StandardType.GGSixBstarE6ThreeAutFrame
public import CFSG.LocalAnalysis.StandardType.GGSixBstarE6ThreeVAdNotInner
public import CFSG.LocalAnalysis.StandardType.GGSixBstarTwE6ThreeNine
public import CFSG.LocalAnalysis.StandardType.GGTwE6ToralInner
public import CFSG.Quasithin.SteinbergCDCentralThreeA6Centralizer
public import CFSG.Quasithin.H13.A7SharedCubicSylow

public section

namespace CFSG.StandardType.NoOffTwE6Three

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Exceptional CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.Open CFSG.StandardType.TwE6Toral CFSG.StandardType.NoOffE6Three
  CFSG.StandardType.TableBExc.E6Three

private theorem nine_dvd_add_one_of_nine_dvd_sq_sub_one (q : ℕ) (h3 : 3 ∣ q + 1)
    (h9 : 9 ∣ q ^ 2 - 1) : 9 ∣ q + 1 := by
  have hq0 : 0 < q := by omega
  have h1 : 1 ≤ q ^ 2 := Nat.one_le_pow 2 q hq0
  have h9z : (9 : ℤ) ∣ (q : ℤ) * (q : ℤ) - 1 := by
    have hcast : ((q ^ 2 - 1 : ℕ) : ℤ) = (q : ℤ) * (q : ℤ) - 1 := by
      rw [Nat.cast_sub h1]
      push_cast
      ring
    rw [← hcast]
    exact_mod_cast h9
  rcases CFSG.Quasithin.SteinbergCD.dvd_sub_one_or_dvd_add_one_of_dvd_mul_self_sub_one h9z
    with h | h
  · exfalso
    have h3z : (3 : ℤ) ∣ (q : ℤ) + 1 := by exact_mod_cast h3
    have h3z' : (3 : ℤ) ∣ (q : ℤ) - 1 :=
      dvd_trans (by norm_num : (3 : ℤ) ∣ 9) h
    have h2 : (3 : ℤ) ∣ 2 := by
      have := Int.dvd_sub h3z h3z'
      ring_nf at this
      simpa using this
    omega
  · exact_mod_cast h

@[expose] def GGTwE6ThreeRankFiveInput : Prop :=
  ∀ {f : ℕ}, 1 ≤ f → 3 ∣ 2 ^ f + 1 →
    ∀ {S : Subgroup (MulAut ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f))
      (frobQ 2 f)))},
      IsElemAbelian 3 S → S ≤ LayerSixE.twInndiagAut f → 3 ^ 5 ≤ Nat.card S →
      ∃ Y : Subgroup (MulAut ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f))
          (frobQ 2 f))),
        Y ≤ LayerSixE.twInndiagAut f ∧ S ≤ Y ∧ IsElemAbelian 3 Y ∧ Nat.card Y = 3 ^ 6 ∧
        (9 ∣ 2 ^ f + 1 → Y ≤ (MulAut.conj : ↥(graphFixedRootGroup TwistTag.E6
          (GaloisField 2 (2 * f)) (frobQ 2 f)) →*
          MulAut ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f)) (frobQ 2 f))).range)

theorem ggTwE6ThreeSCShapeInput_of_rankFive (h : GGTwE6ThreeRankFiveInput) :
    GGTwE6ThreeSCShapeInput := by
  intro f hf h3 M' S hSM hInnM hSel hSI h5 hSC
  classical
  let K := GaloisField 2 (2 * f)
  let C := ↥(graphFixedRootGroup TwistTag.E6 K (frobQ 2 f))
  let I : Subgroup (MulAut C) := (MulAut.conj : C →* MulAut C).range
  let Innd : Subgroup (MulAut C) := LayerSixE.twInndiagAut f
  haveI : Fintype K := Fintype.ofFinite K
  have hsplit : Innd ≤ M' ∨ M' ⊓ Innd ≤ I := by
    by_cases hle : Innd ≤ M'
    · exact Or.inl hle
    · refine Or.inr ?_
      intro t ht
      by_contra htI
      exact hle ((twInndiagAut_le_sup_zpowers hf ht.2 htI).trans
        (sup_le hInnM (Subgroup.zpowers_le.mpr ht.1)))
  have hKcard : Nat.card K = (2 ^ f) ^ 2 := card_galoisField_two_mul f hf
  have h3K : 3 ∣ Nat.card K - 1 := by
    rw [hKcard]
    have hfac : (2 ^ f) ^ 2 - 1 = (2 ^ f + 1) * (2 ^ f - 1) := by
      simpa using Nat.sq_sub_sq (2 ^ f) 1
    rw [hfac]
    exact dvd_mul_of_dvd_left h3 _
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨ζ, hζo⟩ := TableBSymp.exists_orderOf_eq_of_dvd (K := K) h3K
  have hζ : ζ ^ 3 = 1 := by
    rw [← hζo]
    exact pow_orderOf_eq_one ζ
  obtain ⟨Y, hYInnd, hSY, hYel, hYcard, hYnine⟩ := h hf h3 hSel hSI h5
  by_cases hYM : Y ≤ M'
  ·
    have hYleS : Y ≤ S := by
      intro y hy
      refine hSC y (hYM hy) (fun s hs => ?_) (hYel.2 y hy)
      haveI : IsMulCommutative ↥Y := hYel.1
      exact congrArg Subtype.val (mul_comm' (⟨y, hy⟩ : Y) (⟨s, hSY hs⟩ : Y))
    have hYeq : S = Y := le_antisymm hSY hYleS
    have hScard : Nat.card S = 3 ^ 6 := by rw [hYeq, hYcard]
    have hcardLift : Nat.card (twLift hf S) = 3 ^ 6 := by
      rw [card_twLift hf hSI, hScard]
    obtain ⟨γ, -, hγ⟩ := exists_conj_eq_vAd (K := K) h3K hζo hζ
      (isElemAbelian_twLift hf hSI hSel) (twLift_le_hatAut_range hf S) hcardLift.ge
    have hframeV : GGBstarModelFrame (TableBExc.E6Three.adPerm .E6 3) 3
        (⊤ : Subgroup (MulAut (adjointGroup Tag.E6 K))) (vAd ζ hζ) :=
      ggBstarModelFrame_vAd hζo hζ ⊤
    have htop : (⊤ : Subgroup (MulAut (adjointGroup Tag.E6 K))).map
        (MulAut.conj γ).toMonoidHom = ⊤ :=
      Subgroup.map_top_of_surjective _ (MulAut.conj γ).surjective
    have hframeLift : GGBstarModelFrame (TableBExc.E6Three.adPerm .E6 3) 3
        (⊤ : Subgroup (MulAut (adjointGroup Tag.E6 K))) (twLift hf S) := by
      refine GGBstarModelFrame.of_conj (M := ⊤) (Bs := twLift hf S) γ ?_
      rw [htop, hγ]
      exact hframeV
    exact Or.inl (ggBstarModelFrame_of_twLift hf hSI hframeLift)
  ·
    have hMI : M' ⊓ Innd ≤ I := by
      rcases hsplit with hID | hMI
      · exact absurd (hYInnd.trans hID) hYM
      · exact hMI
    have hSInn : S ≤ I := (le_inf hSM hSI).trans hMI
    have hnine : ¬ 9 ∣ 2 ^ f + 1 := fun h9 => hYM ((hYnine h9).trans hInnM)
    have hnot9 : ¬ 9 ∣ Nat.card K - 1 := by
      rw [hKcard]
      intro hd
      exact hnine (nine_dvd_add_one_of_nine_dvd_sq_sub_one (2 ^ f) h3 hd)
    have hnot : ¬ vAd ζ hζ ≤
        (MulAut.conj : (adjointGroup Tag.E6 K) →*
          MulAut (adjointGroup Tag.E6 K)).range :=
      vAd_not_le_innerAut hnot9 hζo hζ
    have hinner : twLift hf S ≤
        (MulAut.conj : (adjointGroup Tag.E6 K) →*
          MulAut (adjointGroup Tag.E6 K)).range :=
      twLift_le_innerAut hf hSInn
    have h5Lift : 3 ^ 5 ≤ Nat.card (twLift hf S) := by
      rw [card_twLift hf hSI]
      exact h5
    obtain ⟨γ, -, hγ⟩ := exists_conj_eq_vHyp (K := K) h3K hζo hζ hnot
      (isElemAbelian_twLift hf hSI hSel) hinner h5Lift
    have hframeH : GGBstarModelFrame NoOffRest.hypPerm 3
        (⊤ : Subgroup (MulAut (adjointGroup Tag.E6 K))) (vHyp ζ hζ) :=
      ggBstarModelFrame_vHyp hζo hζ ⊤
    have htop : (⊤ : Subgroup (MulAut (adjointGroup Tag.E6 K))).map
        (MulAut.conj γ).toMonoidHom = ⊤ :=
      Subgroup.map_top_of_surjective _ (MulAut.conj γ).surjective
    have hframeLift : GGBstarModelFrame NoOffRest.hypPerm 3
        (⊤ : Subgroup (MulAut (adjointGroup Tag.E6 K))) (twLift hf S) := by
      refine GGBstarModelFrame.of_conj (M := ⊤) (Bs := twLift hf S) γ ?_
      rw [htop, hγ]
      exact hframeH
    exact Or.inr (ggBstarModelFrame_of_twLift hf hSI hframeLift)

end CFSG.StandardType.NoOffTwE6Three
