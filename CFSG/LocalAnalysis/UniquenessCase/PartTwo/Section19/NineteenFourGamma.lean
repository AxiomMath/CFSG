module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section19.NineteenFourP
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section19.NineteenThreeHigh
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section19.NineteenSix
public import CFSG.LocalAnalysis.WeakClosure81.FiveTenMaxU

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S19

open CFSG.Open Subgroup CFSG.Quasithin CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.WeakClosure81
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

theorem exists_gammaZero_19 (hTim : CFSG.CGT.Timmesfeld75.NodeStatement)
    (hcat : ¬ CFSG.Blueprint.Catalog G) (D : Data G) (h61 : UC6.R6_1 D) (h86 : W3Lem86_1 G)
    (h126 : R126 D) {V₀ V : Subgroup G} {p : ℕ} {L K : Subgroup G}
    (h : Ctx19_1 D V₀ V p L K) (hm : 4 < mSub V₀) :
    ∃ A ∈ E3.gammaSet V₀ 0 D.T, ∃ J : Subgroup G, JChoice19 D L K J ∧
      IsSylowIn 2 (D.T ⊓ centralizer (A : Set G)) (D.M ⊓ centralizer (A : Set G)) ∧
      ¬ ⁅J, A⁆ ≤ pCoreOf 2 D.M := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hne : V₀ ≠ ⊥ := ne_bot_of_one_lt_mSub h.hyp.big
  have hV : InCalV D.M V₀ := S17.hyp125_inCalV h.hyp.hyp125 hne
  have hTI := S17.hyp125_isTI h.hyp.hyp125 hne
  have h8 : 8 ≤ Nat.card V₀ := by
    have hcardV0 : Nat.card V₀ = 2 ^ mSub V₀ :=
      card_eq_two_pow_mSub h.hyp.hyp125.pairFacts.elemAbelian₀.isPGroup
    rw [hcardV0]
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ mSub V₀ := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h5 : 5 ∈ D.sig := h.p_eq ▸ h.hyp.hp
  have hLM : L ≤ D.M := CFSG.Quasithin.A3.subnormal_le h.hyp.hL.1.1
  have hKM : K ≤ D.M := CFSG.Quasithin.A3.subnormal_le h.hK.1
  have h5L : 5 ∣ Nat.card L := (h.p_eq ▸ h.hyp.hL.2 : 5 ∈ piSet L).2
  have h5K : 5 ∣ Nat.card K := UC22.InS3.UC49.five_dvd_card_of_isAlt h.hKshape
  have hLK : ⁅L, K⁆ ≤ pCoreOf 2 D.M :=
    ((calC_commutator_le_of_ne h.hyp.hL.1 h.hK h.hne.symm).trans inf_le_left).trans
      (uc22p22r_pCoreOf_le_of_isSubnormal h.hyp.hL.1.1)
  have hex : ∃ A₀ ∈ E3.gammaSet V₀ 0 D.T,
      ¬ ⁅L, A₀⁆ ≤ pCoreOf 2 D.M ∨ ¬ ⁅K, A₀⁆ ≤ pCoreOf 2 D.M := by
    by_contra hcon
    have hcon' : ∀ A ∈ E3.gammaSet V₀ 0 D.T,
        ⁅L, A⁆ ≤ pCoreOf 2 D.M ∧ ⁅K, A⁆ ≤ pCoreOf 2 D.M := by
      intro A hA
      have h1 : ¬ (¬ ⁅L, A⁆ ≤ pCoreOf 2 D.M ∨ ¬ ⁅K, A⁆ ≤ pCoreOf 2 D.M) :=
        fun hh => hcon ⟨A, hA, hh⟩
      constructor
      · by_contra hp
        exact h1 (Or.inl hp)
      · by_contra hq
        exact h1 (Or.inr hq)
    have hLN : L ≤ normalizer (E3.wClos V₀ 0 D.T : Set G) :=
      le_normalizer_wClos_zero_of_forall_commutator_le D fun A hA => (hcon' A hA).1
    have hKN : K ≤ normalizer (E3.wClos V₀ 0 D.T : Set G) :=
      le_normalizer_wClos_zero_of_forall_commutator_le D fun A hA => (hcon' A hA).2
    have hU : UniqueMax D.M (D.M ⊓ normalizer (E3.wClos V₀ 0 D.T : Set G)) :=
      uniqueMax_of_commutator_le_pCoreOf D h61 h5
        (H := D.M ⊓ normalizer (E3.wClos V₀ 0 D.T : Set G)) (Y := L) (J := K)
        inf_le_left (le_inf hLM hLN) (le_inf hKM hKN) hLK h.hK.2.1 h5K h5L
    exact twelve_seven_one hTim hcat D h86 h126 h.hyp.hyp125.2 hV hTI h8 hU
  obtain ⟨A₀, hA₀, hA₀nle⟩ := hex
  have hA₀el : IsElemAbelian 2 A₀ := by
    obtain ⟨g, hAg, -⟩ := hA₀.2
    exact (E3.isElemAbelian_conjSubgroup hV.2.2.2 g).mono hAg
  have hA₀C : A₀ ≤ centralizer (A₀ : Set G) := by
    intro a ha
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    exact CFSG.Open.IsElemAbelian.comm hA₀el hb ha
  have hCTle : D.T ⊓ centralizer (A₀ : Set G) ≤ D.M ⊓ centralizer (A₀ : Set G) :=
    le_inf (inf_le_left.trans D.sylowM.le) inf_le_right
  have hCTp : IsPGroup 2 (D.T ⊓ centralizer (A₀ : Set G) : Subgroup G) :=
    D.sylowM.isPGroup.to_le inf_le_left
  obtain ⟨P, hP, hQTP⟩ := exists_isSylowIn_ge 2 hCTle hCTp
  have hPM : P ≤ D.M := hP.le.trans inf_le_left
  obtain ⟨k, hkM, hkP⟩ := UC6.exists_conj_le_of_isSylowOf D.sylowM hPM hP.isPGroup
  obtain ⟨A, hAdef⟩ : ∃ A : Subgroup G, A = conjSubgroup A₀ k := ⟨_, rfl⟩
  have hA₀P : A₀ ≤ P := (le_inf hA₀.1 hA₀C).trans hQTP
  have hAT : A ≤ D.T := by
    intro x hx
    rw [hAdef] at hx
    rw [mem_conjSubgroup_iff] at hx
    have hxP : k * x * k⁻¹ ∈ P := hA₀P hx
    have h := hkP (k * x * k⁻¹) hxP
    simpa [mul_assoc] using h
  have hAgamma : A ∈ E3.gammaSet V₀ 0 D.T := by
    refine ⟨hAT, ?_⟩
    rw [hAdef]
    exact E3.gammaMember_conj (V := V₀) (A := A₀) (i := 0) k hA₀.2
  have hH₀ : conjSubgroup (D.M ⊓ centralizer (A₀ : Set G)) k =
      D.M ⊓ centralizer (A : Set G) := by
    rw [E3.conjSubgroup_inf, E3.conjSubgroup_centralizer, hAdef]
    rw [conjSubgroup_eq_iff_mem_normalizer.2 (Subgroup.le_normalizer hkM)]
  have hP'syl : IsSylowIn 2 (conjSubgroup P k) (D.M ⊓ centralizer (A : Set G)) := by
    rw [← hH₀]
    refine isSylowIn_of_card_eq (E3.conjSubgroup_mono_left k hP.le) ?_
    rw [E3.card_conjSubgroup, E3.card_conjSubgroup, hP.card_eq]
  have hP'T : conjSubgroup P k ≤ D.T := by
    intro x hx
    rw [mem_conjSubgroup_iff] at hx
    have h := hkP (k * x * k⁻¹) hx
    simpa [mul_assoc] using h
  have hP'C : conjSubgroup P k ≤ centralizer (A : Set G) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    rw [hAdef] at ha
    change a ∈ conjSubgroup A₀ k at ha
    rw [mem_conjSubgroup_iff] at hx ha
    have hxP : k * x * k⁻¹ ∈ P := hx
    have haA₀ : k * a * k⁻¹ ∈ A₀ := ha
    have hxcent : k * x * k⁻¹ ∈ Subgroup.centralizer (A₀ : Set G) :=
      (Subgroup.mem_inf.mp (hP.le hxP)).2
    have hcomm : (k * a * k⁻¹) * (k * x * k⁻¹) = (k * x * k⁻¹) * (k * a * k⁻¹) :=
      (Subgroup.mem_centralizer_iff.mp hxcent) (k * a * k⁻¹) haA₀
    calc a * x = k⁻¹ * ((k * a * k⁻¹) * (k * x * k⁻¹)) * k := by group
      _ = k⁻¹ * ((k * x * k⁻¹) * (k * a * k⁻¹)) * k := by rw [hcomm]
      _ = x * a := by group
  have hSsyl : IsSylowIn 2 (D.T ⊓ centralizer (A : Set G))
      (D.M ⊓ centralizer (A : Set G)) :=
    isSylowIn_of_le_of_isPGroup hP'syl (le_inf hP'T hP'C)
      (le_inf (inf_le_left.trans D.sylowM.le) inf_le_right)
      (D.sylowM.isPGroup.to_le inf_le_left)
  have hperm : PermutesPair D.M L K := permutesPair_of_ctx19_one h
  obtain ⟨J, hJchoice, hJN, hJA₀⟩ : ∃ J : Subgroup G, JChoice19 D L K J ∧
      D.M ≤ normalizer (J : Set G) ∧ ¬ ⁅J, A₀⁆ ≤ pCoreOf 2 D.M := by
    by_cases hLn : (L.subgroupOf D.M).Normal
    · have hMLn : D.M ≤ normalizer (L : Set G) :=
        (Subgroup.normal_subgroupOf_iff_le_normalizer hLM).1 hLn
      have hKn : D.M ≤ normalizer (K : Set G) := by
        intro m hm
        rcases hperm m hm with ⟨-, h2⟩ | ⟨h1, -⟩
        · exact UC6S846.mem_normalizer_iff_map_conj.2 h2
        · have hLm : L.map (MulAut.conj m).toMonoidHom = L :=
            UC6S846.mem_normalizer_iff_map_conj.1 (hMLn hm)
          exact absurd (hLm.symm.trans h1) h.hne.symm
      rcases hA₀nle with hL | hK
      · exact ⟨L, Or.inl ⟨Or.inl rfl, hLn⟩, hMLn, hL⟩
      · exact ⟨K, Or.inl ⟨Or.inr rfl, hLn⟩, hKn, hK⟩
    · have hsupN : D.M ≤ normalizer ((L ⊔ K : Subgroup G) : Set G) := by
        intro m hm
        rw [UC6S846.mem_normalizer_iff_map_conj, Subgroup.map_sup]
        rcases hperm m hm with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · rw [h1, h2]
        · rw [h1, h2]
          exact sup_comm _ _
      refine ⟨L ⊔ K, Or.inr ⟨rfl, hLn⟩, hsupN, ?_⟩
      intro hle
      rcases hA₀nle with hL | hK
      · exact hL ((Subgroup.commutator_mono le_sup_left le_rfl).trans hle)
      · exact hK ((Subgroup.commutator_mono le_sup_right le_rfl).trans hle)
  have hJk : conjSubgroup J k = J :=
    conjSubgroup_eq_iff_mem_normalizer.2 (hJN hkM)
  have hOk : conjSubgroup (pCoreOf 2 D.M) k⁻¹ = pCoreOf 2 D.M :=
    conjSubgroup_eq_iff_mem_normalizer.2
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf (r := 2) D.M (D.M.inv_mem hkM))
  have hJAnle : ¬ ⁅J, A⁆ ≤ pCoreOf 2 D.M := by
    intro hle
    apply hJA₀
    have h1 : conjSubgroup ⁅J, A⁆ k⁻¹ ≤ conjSubgroup (pCoreOf 2 D.M) k⁻¹ :=
      E3.conjSubgroup_mono_left k⁻¹ hle
    have hJAeq : ⁅J, A⁆ = conjSubgroup ⁅J, A₀⁆ k := by
      rw [hAdef, E3.conjSubgroup_commutator, hJk]
    rw [hJAeq, E3.conjSubgroup_conj_inv, hOk] at h1
    exact h1
  exact ⟨A, hAgamma, J, hJchoice, hSsyl, hJAnle⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S19
