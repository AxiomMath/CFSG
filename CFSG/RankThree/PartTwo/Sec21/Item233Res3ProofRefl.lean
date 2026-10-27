module

public import CFSG.RankThree.PartTwo.Sec21.Item233Res3ProofSmallSp64
public import CFSG.RankThree.PartTwo.Sec21.Item233Res3ProofU54Lines
public import CFSG.RankThree.PartTwo.Sec21.Item233Res3ProofSp4
public import CFSG.RankThree.PartTwo.Sec21.Item233Res3ProofSL3
public import CFSG.RankThree.PartTwo.Sec21.Item221ResProofZ
import CFSG.RankThree.PartTwo.Sec4.T444.Item434SmallTwoOtherSp44
public import CFSG.RankThree.PartTwo.Sec21.Item221ProofZGen

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.KFacts.KP14
open CFSG.Assembly (IsElemAbelian)
open CFSG.Assembly.RankThreeEven (projSL projSU projSp)
open CFSG.Assembly.LowTwoRank (StatedSp)
open URoots (V3)
open Matrix
open CFSG.RankThree.PartOne.KFU (card_center_mulEquiv)

namespace Item233Res3Proof

variable {G : Type} [Group G]

theorem not_twentySeven_dvd_card_U44 : ¬ 27 ∣ Nat.card (projSU 4 2 2) := by
  rw [card_U44]
  norm_num

theorem center_U44 : Subgroup.center (projSU 4 2 2) = ⊥ := by
  have : IsSimpleGroup (projSU 4 2 2) := isSimpleGroup_projSU le_rfl (by norm_num)
  exact Sec4.Item434Spor.center_eq_bot_of_simple (by rw [card_U44]; norm_num)

theorem cubeInner_U44 : Sec4.CubeInner (projSU 4 2 2) := by
  apply Sec4.cubeInner_of_not_three_dvd_card_outer
  intro h3
  have := h3.trans (Sec4.card_outer_projSU_dvd 4 2 2 (by norm_num) (by norm_num) (by norm_num))
  norm_num at this

theorem exists_fourGroup_of_inner [Finite G] {A Z : Subgroup G}
    (hA : Maximal (fun B : Subgroup G => IsElemAbelian 3 B) A) (hA27 : Nat.card A = 3 ^ 3)
    (hAN : A ≤ Subgroup.normalizer (Z : Set G))
    (hC3 : Nat.card (A ⊓ Subgroup.centralizer (Z : Set G) : Subgroup G) = 3)
    (hZc : Subgroup.center Z = ⊥) (hCI : Sec4.CubeInner Z) (h27 : ¬ 27 ∣ Nat.card Z)
    (hlines : ∀ ℓ : Subgroup G, ℓ ≤ A ⊓ Z → Nat.card ℓ = 3 → ∃ V : Subgroup G, V ≤ Z ∧
      IsElemAbelian 2 V ∧ Nat.card V = 4 ∧ A ⊓ Z ≤ Subgroup.normalizer (V : Set G) ∧
      (A ⊓ Z) ⊓ Subgroup.centralizer (V : Set G) = ℓ)
    {ρ : MulAut A} (hρZ : ρ ∈ starOf A Z) (hρ : IsReflectionOn ρ) :
    ∃ V ∈ fourGroups A, A ⊓ Subgroup.centralizer (V : Set G) ≤ fixedInG A ρ := by
  have hF9 := card_inf_eq_nine hA hA27 hAN hZc hCI hC3 h27
  have hAZ := inf_sup_inf_centralizer_eq hA27 hZc hF9 hC3
  exact exists_fourGroup_of_lines hA.prop hA27 hZc hAZ hC3 hlines hρZ hρ

theorem reflRootFourGroupFour :
    ∀ (G : Type) [Group G] [Finite G] (A Z : Subgroup G),
      Maximal (fun B : Subgroup G => IsElemAbelian 3 B) A → Nat.card A = 3 ^ 3 →
      A ≤ Subgroup.normalizer (Z : Set G) →
      Nat.card (A ⊓ Subgroup.centralizer (Z : Set G) : Subgroup G) = 3 →
      (Nonempty (Z ≃* SL3 2) ∨ Nonempty (Z ≃* projSp 2 (GaloisField 2 2)) ∨
        Nonempty (Z ≃* projSU 4 2 2) ∨ Nonempty (Z ≃* projSU 5 2 2)) →
      ∀ ρ ∈ starOf A Z, IsReflectionOn ρ →
        ∃ V ∈ fourGroups A, A ⊓ Subgroup.centralizer (V : Set G) ≤ fixedInG A ρ := by
  intro G _ _ A Z hA hA27 hAN hC3 hZ ρ hρZ hρ
  have hAe : IsElemAbelian 3 A := hA.prop
  have hFe : IsElemAbelian 3 (A ⊓ Z) := isElemAbelian_of_le hAe inf_le_left
  rcases hZ with hZ | hZ | hZ | hZ <;> obtain ⟨eZ⟩ := hZ
  · exact exists_fourGroup_SL34 hAe hAN eZ hρZ hρ
  ·
    set e := eZ.trans Sec4.Item434SmallTwoOther.sp44Equiv
    have hZc : Subgroup.center Z = ⊥ := by
      have h := card_center_mulEquiv e
      rw [Sec4.Item434SmallTwoOther.center_sp44, Subgroup.card_bot] at h
      exact Subgroup.eq_bot_of_card_eq _ h
    have hCI : Sec4.CubeInner Z := by
      have hS : Sec4.CubeInner (StatedSp 2 (GaloisField 2 2)) := fun τ h3 =>
        Sec4.Item434SmallTwoOther.mem_range_conj_of_pow_three_sp44 τ h3
      exact hS.of_mulEquiv e
    have h27 : ¬ 27 ∣ Nat.card Z := by
      rw [Nat.card_congr e.toEquiv, Sec4.Item434SmallTwoOther.card_sp44]
      norm_num
    refine exists_fourGroup_of_inner hA hA27 hAN hC3 hZc hCI h27 ?_ hρZ hρ
    intro ℓ hℓ hℓ3
    exact sp4FourGroupLines (b := 2) (by norm_num) even_two G Z ⟨eZ⟩ (A ⊓ Z) ℓ inf_le_right hFe
      hℓ hℓ3
  ·
    have hZc : Subgroup.center Z = ⊥ := by
      have h := card_center_mulEquiv eZ
      rw [center_U44, Subgroup.card_bot] at h
      exact Subgroup.eq_bot_of_card_eq _ h
    have h27 : ¬ 27 ∣ Nat.card Z := by
      rw [Nat.card_congr eZ.toEquiv]
      exact not_twentySeven_dvd_card_U44
    refine exists_fourGroup_of_inner hA hA27 hAN hC3 hZc (cubeInner_U44.of_mulEquiv eZ) h27 ?_
      hρZ hρ
    intro ℓ hℓ hℓ3
    exact U4FourLines.u4FourGroupLines (by norm_num) even_two G Z ⟨eZ⟩ (A ⊓ Z) ℓ inf_le_right hFe
      hℓ hℓ3
  ·
    obtain ⟨hZc, hF9, ε, -, hT2⟩ := exists_model_U54 hA hA27 hAN hC3 eZ
    have hAZ := inf_sup_inf_centralizer_eq hA27 hZc hF9 hC3
    exact exists_fourGroup_of_lines hAe hA27 hZc hAZ hC3 (lines_U54 hAe ε hT2) hρZ hρ

theorem eq_two_of_kOf [Finite G] (h2130 : Item2130) (h222 : Item222) (hKW : KOfWellDefinedAll)
    {A E U L : Subgroup G} {c : G} (hpair : Sec21Pair G A E U c L) (hconc : Item231Concl A)
    (hA27 : Nat.card A = 3 ^ 3) {φ : MulAut A} (hφ : φ ∈ dStar A) {m : ℕ} (hm0 : 0 < m)
    (hme : Even m) (eK : kOf A φ ≃* projSL 2 (GaloisField 2 m)) : m = 2 := by
  have hK := hKW G A E U c L hpair
  have hAF := hpair.mem_S.1
  have hAe : IsElemAbelian 3 A := hAF.1
  have hAc : ∀ a b : A, a * b = b * a := hAe.1.is_comm.comm
  have hm2 : 2 ≤ m := by
    obtain ⟨k, hk⟩ := hme
    omega
  have hKI : kOf A φ ≤ iGroup A := kOf_le_iGroup hφ
  have hKC : kOf A φ ≤ Subgroup.centralizer (fixedInG A φ : Set G) :=
    (kOf_le_kZero hK hφ).trans (kZero_le_centralizer A φ)
  have hKp : Group.IsPerfect (kOf A φ) := isPerfect_of_mulEquiv_projSL hm2 eK
  have hAI : A ≤ iGroup A := le_iGroup h2130 h222 hpair hK
  have hBA : fixedInG A φ ≤ A := Subgroup.map_subtype_le _
  have hB9 := Item228ResProof.card_fixedInG_eq_nine hAc hA27 hφ.1
  have hI : Nonempty (iGroup A ≃* projSL 4 (GaloisField 2 2)) ∨
      Nonempty (iGroup A ≃* projSp 3 (GaloisField 2 2)) := by
    rcases hconc with ⟨-, -, h81⟩ | ⟨hI, -, -⟩ | ⟨hI, -, -⟩
    · rw [hA27] at h81
      norm_num at h81
    · exact Or.inl hI
    · exact Or.inr hI
  have h60 := terminalRootSmall G (iGroup A) A (fixedInG A φ) (kOf A φ) hAI hAe hA27 hI hBA hB9
    hKI hKC hKp
  rw [Nat.card_congr eK.toEquiv, card_projSL_two m (by omega)] at h60
  by_contra hne
  have hm4 : 4 ≤ m := by
    obtain ⟨k, hk⟩ := hme
    omega
  have h1 : 16 ≤ 2 ^ m := by
    calc 16 = 2 ^ 4 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm4
  have h2 : 255 ≤ (2 ^ m) ^ 2 - 1 := by
    have : 256 ≤ (2 ^ m) ^ 2 := by nlinarith
    omega
  have h3 := Nat.mul_le_mul h1 h2
  omega

theorem reflDStar_three' [Finite G] (h45 : Sec4.Item4_5) (h66 : Sec6.Item6_6) (h222 : Item222)
    (h2131 : Item2131One) (h612 : Item612Sec21) (h2130 : Item2130) (hKW : KOfWellDefinedAll)
    {A E U L : Subgroup G} {c : G} (hpair : Sec21Pair G A E U c L) (hconc : Item231Concl A)
    (hA27 : Nat.card A = 3 ^ 3) {φ : MulAut A} (hφ : φ ∈ dStar A) {Z : Subgroup G}
    (hZ : Z ∈ lStar A) (h3 : ∀ ψ ∈ dStar A, ψ ≠ φ → Item228OneConcl A φ Z) :
    ∀ ρ ∈ starOf A Z, IsReflectionOn ρ → ρ ∈ dStar A := by
  intro ρ hρZ hρ
  have hAF := hpair.mem_S.1
  have hAe : IsElemAbelian 3 A := hAF.1
  have hAc : IsMulCommutative A := hAe.1
  have hAmax : Maximal (fun B : Subgroup G => IsElemAbelian 3 B) A :=
    ⟨hAe, fun B hB hAB => (hAF.2.1 B hB hAB).le⟩
  obtain ⟨f, hWf, hcase⟩ := exists_coord_image_dStar h2131 h222 hpair hA27
  have hρm : coordGL f ρ ∈ monomial := hWf ⟨ρ, starOf_le_wStar A Z hρZ, rfl⟩
  have hρmono : coordGL f ρ ∈ monoRefl :=
    mem_monoRefl_of_isReflection hρm ((isReflectionOn_iff hAc f ρ).mp hρ)
  have hmem : coordGL f ρ ∈ coordGL f '' dStar A → ρ ∈ dStar A := by
    rintro ⟨d, hd, hdρ⟩
    rwa [← coordGL_injective f hdρ]
  rcases hcase with hD | hD
  · by_cases hs : coordGL f ρ ∈ swapRefl
    · exact hmem (hD ▸ hs)
    · exfalso
      have hdiag : coordGL f ρ ∈ diagRefl := by
        rcases hρmono with h | h
        · exact h
        · exact absurd h hs
      obtain ⟨ψ, hψ, hψφ⟩ := Item221ResProof.exists_ne_of_image_eq_swapRefl f hD φ
      obtain ⟨m, hm0, hme, ⟨eK⟩, hZtype⟩ := h3 ψ hψ hψφ
      have hm2 : m = 2 := eq_two_of_kOf h2130 h222 hKW hpair hconc hA27 hφ hm0 hme eK
      subst hm2
      have hZtype' : Nonempty (Z ≃* SL3 2) ∨ Nonempty (Z ≃* projSp 2 (GaloisField 2 2)) ∨
          Nonempty (Z ≃* projSU 4 2 2) ∨ Nonempty (Z ≃* projSU 5 2 2) := by
        rcases hZtype with h | h | h | ⟨h4, -⟩ | ⟨-, h⟩
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr (Or.inl h))
        · norm_num at h4
        · exact Or.inr (Or.inr (Or.inr h))
      obtain ⟨a, haA, ha1, hZa⟩ := mem_thetaComponentFamily_iff.mp hZ.1
      have hAN : A ≤ Subgroup.normalizer (Z : Set G) :=
        Sec6.le_normalizer_of_mem_thetaComponentsAt h45 hpair.standing.toTheoremFourHyp hAe haA
          ha1 Z hZa
      have hC3 := Item221ResProof.card_inf_centralizer_eq_three h66 hpair.standing hpair.mem_S hZ
      obtain ⟨V, hV, hVC⟩ := reflRootFourGroupFour G A Z hAmax hA27 hAN hC3 hZtype' ρ hρZ hρ
      obtain ⟨b, hbV, hbd⟩ := exists_bodyDiag_of_fourGroup h612 h222 hpair hA27 f hD hV
      obtain ⟨b', hb'ρ, hb'b⟩ := hVC ⟨b.2, hbV⟩
      have hb'eq : b' = b := Subtype.ext hb'b
      rw [hb'eq, SetLike.mem_coe, mem_fixedSubgroupOf] at hb'ρ
      have hfix : ((coordGL f ρ : GL (Fin 3) (ZMod 3)) : Mat3) *ᵥ
          Multiplicative.toAdd (f.symm b) = Multiplicative.toAdd (f.symm b) := by
        rw [coordGL_mulVec, coordLin3_apply, ofAdd_toAdd, MulEquiv.apply_symm_apply, hb'ρ]
      obtain ⟨h0, h1, h2⟩ := Item221ResProof.diagRefl_not_fix_bodyDiag _ hbd
      simp only [diagRefl, Set.mem_insert_iff, Set.mem_singleton_iff] at hdiag
      rcases hdiag with h | h | h <;> rw [h] at hfix
      · exact h0 hfix
      · exact h1 hfix
      · exact h2 hfix
  · exact hmem (hD ▸ hρmono)

end Item233Res3Proof

theorem item233ZReflDStar_of' (h45 : Sec4.Item4_5) (h66 : Sec6.Item6_6) (h222 : Item222)
    (hKW : KOfWellDefinedAll) (h2131 : Item2131One) (h612 : Item612Sec21) (h2130 : Item2130) :
    Item233ZReflDStar := by
  intro G _ _ A E U c L hpair hconc φ hφ Z hZ hKZ h4 h3
  have hconc' := hconc
  rcases hconc with ⟨-, -, hA⟩ | ⟨-, -, hA⟩ | ⟨-, -, hA⟩
  · exact Item221ResProof.reflDStar_four h222 hKW hpair hA hφ hKZ (h4 hA)
  · exact Item233Res3Proof.reflDStar_three' h45 h66 h222 h2131 h612 h2130 hKW hpair hconc' hA hφ
      hZ (h3 hA)
  · exact Item233Res3Proof.reflDStar_three' h45 h66 h222 h2131 h612 h2130 hKW hpair hconc' hA hφ
      hZ (h3 hA)

theorem item233ZGen_of_res'' (h45 : Sec4.Item4_5) (h66 : Sec6.Item6_6) (h2130 : Item2130)
    (h222 : Item222) (hKW : KOfWellDefinedAll) (hInner : Item223OneInner)
    (h2131 : Item2131One) (h612 : Item612Sec21) (hN : Item233ZRootGenThreeNotU54) :
    Item233ZGen :=
  item233ZGen_of h222 hKW hInner (item233ZReflDStar_of' h45 h66 h222 hKW h2131 h612 h2130)
    (item233ZRootGen_of h222 hKW (item233ZRootGenThree_of_notU54 hN
      (item233ZNotU54_of h45 h66 h2130 h222 hKW u54LongRoot terminalRootSmall)))

end CFSG.RankThree.PartTwo.Sec21
