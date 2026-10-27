module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section19.NineteenTen
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section19.NineteenTwentyTwoVZero
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.OutL2U3Product
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section18.EighteenSevenFinal
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenFiftyEightLemmas
public import CFSG.GroupTheory.PerfectLeOfPGroupQuotient
public import CFSG.Mathlib.Arithmetic.TwoPowModThree

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S19

open Subgroup CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17
open CFSG.Blueprint (LieModel)

variable {G : Type} [Group G] [Finite G]

section Certificates


theorem jM_four_structure (D : Data G) {V₀ V : Subgroup G} {p : ℕ} {L : Subgroup G}
    (h : Hyp19 D V₀ V p L) (h1 : R19_1At D V₀ V p L h) (h42 : S17.R17_42At D V₀ V)
    (h641 : S17.R17_64_1At D V₀ V) (h642 : S17.R17_64_2At D V₀ V)
    (h643 : S17.R17_64_3At D V₀ V) (hj : S17.jM D p = 4) :
    ∃ K₁ K₂ : Subgroup G, K₁ ∈ calC D.M ∧ K₂ ∈ calC D.M ∧ K₁ ≠ K₂ ∧
      IOf D p L = K₁ ⊔ K₂ ∧ IsL2 (Bar2 K₁) (S17.nOf L) ∧
      (IsL2 (Bar2 K₂) (S17.nOf L) ∨ IsU3 (Bar2 K₂) (S17.nOf L)) ∧
      IsPowTwo (S17.nOf L) ∧ 2 < S17.nOf L ∧
      (S17.IsL2U3Product (Bar2 (IOf D p L)) (S17.nOf L) ∨
        IsL2Square (Bar2 (IOf D p L)) (S17.nOf L)) ∧
      (2 : ℤ) ^ S17.nOf L ≡ -1 [ZMOD (p : ℤ)] := by
  classical
  have h54 : S17.Hyp1754 D p := hyp1754_of_jM_eq_four D h h42 hj
  have hH : Hinf D.M = Lp D p := h641 p h54
  obtain ⟨n', hn'⟩ := h642 p h54
  obtain ⟨hn'pow, hn'cong⟩ := h643 p h54 n' hn'
  have hX4 : conjClosure D.M L ∈ S17.calL4Star D p := by
    have hX0 : conjClosure D.M L ∈ S17.calL0Star D p := h.hX
    rw [S17.calL0Star, hj] at hX0
    simpa [S17.calLjStar] using hX0
  rw [S17.mem_calL4Star] at hX4
  obtain ⟨-, ⟨a, hXshape⟩, -⟩ := hX4
  have hsX : IsSimpleGroup (Bar2 (conjClosure D.M L)) := by
    rcases hXshape with hL2 | hU3
    · exact LieModel.isSimpleGroup_of_mem_classicalTags (by decide) hL2
    · exact LieModel.isSimpleGroup_of_mem_classicalTags (by decide) hU3
  have hXL : conjClosure D.M L = L :=
    conjClosure_eq_self_of_isSimpleGroup_bar2 h.hL.1 hsX
  have hLM : L ≤ D.M := h.hL.1.1.le
  have hMnX : D.M ≤ normalizer (conjClosure D.M L : Set G) :=
    (conjSetOf_subset_calC_conjClosure h.hL.1).2.1
  have hMnL : D.M ≤ normalizer (L : Set G) := by rwa [hXL] at hMnX
  have hLnM : (L.subgroupOf D.M).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hLM).2 hMnL
  have hLleHinf : L ≤ Hinf D.M := uc22p21c_le_Hinf h.hL.1.1.le h.hL.1.2.1
  have hLleLp : L ≤ Lp D p := by rw [← hH]; exact hLleHinf
  have hbar2L' : IsL2 (Bar2 L) n' ∨ IsU3 (Bar2 L) n' :=
    S17.bar2_isL2_or_isU3_of_p1642 h.hL.1 hLnM hLleLp hn'
  have hn'eq : n' = S17.nOf L := by
    rcases hbar2L' with hL2 | hU3
    · exact (S17.nOf_eq_of_isL2 hL2).symm
    · exact (S18.nOf_eq_of_isU3 hU3).symm
  subst n'
  have hbar2L : IsL2 (Bar2 L) (S17.nOf L) ∨ IsU3 (Bar2 L) (S17.nOf L) := hbar2L'
  have hnpow : IsPowTwo (S17.nOf L) := hn'pow
  have hncong : (2 : ℤ) ^ S17.nOf L ≡ -1 [ZMOD (p : ℤ)] := hn'cong
  have hn_pos : 1 ≤ S17.nOf L := by
    rcases hbar2L with hL2 | hU3
    · have hadm := hL2.admissible
      simp only [CFSG.Open.StatedLieAdmissible] at hadm
      exact hadm.2.1
    · have hadm := hU3.admissible
      simp only [CFSG.Open.StatedLieAdmissible] at hadm
      exact hadm.2.1
  have hn1 : S17.nOf L ≠ 1 := by
    rcases hbar2L with hL2 | hU3
    · intro hn
      have hadm := hL2.admissible
      simp only [CFSG.Open.StatedLieAdmissible] at hadm
      exact hadm.2.2.2.1 (by rw [hn]; norm_num)
    · intro hn
      have hadm := hU3.admissible
      simp only [CFSG.Open.StatedLieAdmissible] at hadm
      exact hadm.2.2.2 (by rw [hn]; norm_num)
  have hn2 : S17.nOf L ≠ 2 := by
    intro hn
    rcases hbar2L with hL2 | hU3
    · rw [hn] at hL2
      exact h1.1 hL2
    · rw [hn] at hU3
      exact h1.2 hU3
  have hn_gt2 : 2 < S17.nOf L := by omega
  have hnEven : Even (S17.nOf L) := by
    obtain ⟨k, hk⟩ := hnpow
    have hk2 : 2 ≤ k := by
      by_contra h
      have hk1 : k ≤ 1 := by omega
      interval_cases k
      · norm_num at hk
        omega
      · norm_num at hk
        exact hn2 hk
    rw [hk]
    exact Nat.even_pow.mpr ⟨even_two, by omega⟩
  have hp : p.Prime := (D.sig_prime p h.hp).1
  have hpn : p ∣ 2 ^ S17.nOf L + 1 :=
    CFSG.LocalAnalysis.UniquenessCase.UC22.P2214R.dvd_of_cong hncong
  have hpdvd : p ∣ 2 ^ (2 * S17.nOf L) - 1 :=
    CFSG.RankThree.PartOne.K1320.dvd_two_pow_double_sub_one hpn
  have hnot3 : ¬ 3 ∣ 2 ^ S17.nOf L + 1 := by
    intro hd
    have h0 : (2 ^ S17.nOf L + 1) % 3 = 0 := Nat.mod_eq_zero_of_dvd hd
    rw [Nat.add_mod, CFSG.two_pow_mod_three_of_even hnEven] at h0
    norm_num at h0
  have hI_le_Lp : IOf D p L ≤ Lp D p := by
    rw [IOf, if_pos hj]
    refine iSup₂_le fun K hK => ?_
    exact (uc22p21c_le_Hinf hK.1.1.le hK.1.2.1).trans hH.le
  have key : ∀ {A B : Type} [Group A] [Group B] (e : Bar2 (Lp D p) ≃* A × B)
      (hA : IsL2 A (S17.nOf L)) (hB : IsL2 B (S17.nOf L) ∨ IsU3 B (S17.nOf L)),
      ∃ K₁ K₂ : Subgroup G, K₁ ∈ calC D.M ∧ K₂ ∈ calC D.M ∧ K₁ ≠ K₂ ∧
        IOf D p L = K₁ ⊔ K₂ ∧ IsL2 (Bar2 K₁) (S17.nOf L) ∧
        (IsL2 (Bar2 K₂) (S17.nOf L) ∨ IsU3 (Bar2 K₂) (S17.nOf L)) ∧
        K₁ ⊔ K₂ = Lp D p := by
    intro A B _ _ e hA hB
    classical
    let πA : Bar2 (Lp D p) →* A := (MonoidHom.fst A B).comp e.toMonoidHom
    let πB : Bar2 (Lp D p) →* B := (MonoidHom.snd A B).comp e.toMonoidHom
    let CA : Subgroup (Bar2 (Lp D p)) := πB.ker
    let CB : Subgroup (Bar2 (Lp D p)) := πA.ker
    have hCAn : CA.Normal := inferInstance
    have hCBn : CB.Normal := inferInstance
    let fA : CA →* A := πA.comp CA.subtype
    have hfA_inj : Function.Injective fA := by
      intro x y hxy
      have h1 : (e (x : Bar2 (Lp D p))).1 = (e (y : Bar2 (Lp D p))).1 := by
        simpa [fA, πA] using hxy
      have hx : (e (x : Bar2 (Lp D p))).2 = 1 := by
        simpa [πB] using MonoidHom.mem_ker.mp x.2
      have hy : (e (y : Bar2 (Lp D p))).2 = 1 := by
        simpa [πB] using MonoidHom.mem_ker.mp y.2
      apply Subtype.ext
      apply e.injective
      exact Prod.ext h1 (by rw [hx, hy])
    have hfA_surj : Function.Surjective fA := by
      intro a
      refine ⟨⟨e.symm (a, 1), ?_⟩, ?_⟩
      · show πB (e.symm (a, 1)) = 1
        simp [πB]
      · show fA ⟨e.symm (a, 1), _⟩ = a
        simp [fA, πA]
    let eCA : CA ≃* A := MulEquiv.ofBijective fA ⟨hfA_inj, hfA_surj⟩
    let fB : CB →* B := πB.comp CB.subtype
    have hfB_inj : Function.Injective fB := by
      intro x y hxy
      have h1 : (e (x : Bar2 (Lp D p))).2 = (e (y : Bar2 (Lp D p))).2 := by
        simpa [fB, πB] using hxy
      have hx : (e (x : Bar2 (Lp D p))).1 = 1 := by
        simpa [πA] using MonoidHom.mem_ker.mp x.2
      have hy : (e (y : Bar2 (Lp D p))).1 = 1 := by
        simpa [πA] using MonoidHom.mem_ker.mp y.2
      apply Subtype.ext
      apply e.injective
      exact Prod.ext (by rw [hx, hy]) h1
    have hfB_surj : Function.Surjective fB := by
      intro b
      refine ⟨⟨e.symm (1, b), ?_⟩, ?_⟩
      · show πA (e.symm (1, b)) = 1
        simp [πA]
      · show fB ⟨e.symm (1, b), _⟩ = b
        simp [fB, πB]
    let eCB : CB ≃* B := MulEquiv.ofBijective fB ⟨hfB_inj, hfB_surj⟩
    have hAsimp : IsSimpleGroup A :=
      LieModel.isSimpleGroup_of_mem_classicalTags (by decide) hA
    have hAnon : ∃ a b : A, a * b ≠ b * a :=
      CFSG.ComponentClassification.HarrisLit.nonabelian_of_lieModel_psl2 hA
    have hCAq : CFSG.IsQuasisimple CA :=
      CFSG.IsQuasisimple.of_mulEquiv eCA
        (@CFSG.LocalCores.isQuasisimple_of_isSimpleGroup A _ hAsimp hAnon).1
    have hCAcomp : CFSG.IsComponent CA := ⟨hCAq, hCAn.isSubnormal⟩
    have hBq : CFSG.IsQuasisimple B := by
      rcases hB with hB2 | hB3
      · have hBsimp : IsSimpleGroup B :=
          LieModel.isSimpleGroup_of_mem_classicalTags (by decide) hB2
        exact (@CFSG.LocalCores.isQuasisimple_of_isSimpleGroup B _ hBsimp
          (CFSG.ComponentClassification.HarrisLit.nonabelian_of_lieModel_psl2 hB2)).1
      · have hBsimp : IsSimpleGroup B :=
          LieModel.isSimpleGroup_of_mem_classicalTags (by decide) hB3
        exact (@CFSG.LocalCores.isQuasisimple_of_isSimpleGroup B _ hBsimp
          (CFSG.LocalAnalysis.EvenBN.GMSK.exists_mul_ne_of_lieModel_PSU3 hB3)).1
    have hCBq : CFSG.IsQuasisimple CB := CFSG.IsQuasisimple.of_mulEquiv eCB hBq
    have hCBcomp : CFSG.IsComponent CB := ⟨hCBq, hCBn.isSubnormal⟩
    obtain ⟨K₁, hK₁calLp, hbarK₁⟩ := s13_exists_calC_of_component (Lp D p) hCAcomp
    obtain ⟨K₂, hK₂calLp, hbarK₂⟩ := s13_exists_calC_of_component (Lp D p) hCBcomp
    have hK₁calM : K₁ ∈ calC D.M := calC_of_calC_Lp D hK₁calLp
    have hK₂calM : K₂ ∈ calC D.M := calC_of_calC_Lp D hK₂calLp
    have hK₁leLp : K₁ ≤ Lp D p := hK₁calLp.1.le
    have hK₂leLp : K₂ ≤ Lp D p := hK₂calLp.1.le
    have hK₁normM : (K₁.subgroupOf D.M).Normal := (h54.2 K₁ hK₁calM).1
    have hK₂normM : (K₂.subgroupOf D.M).Normal := (h54.2 K₂ hK₂calM).1
    have hK₁normLp : (K₁.subgroupOf (Lp D p)).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hK₁leLp).2
        ((Lp_le_M D p).trans
          ((Subgroup.normal_subgroupOf_iff_le_normalizer hK₁calM.1.le).1 hK₁normM))
    have hK₂normLp : (K₂.subgroupOf (Lp D p)).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hK₂leLp).2
        ((Lp_le_M D p).trans
          ((Subgroup.normal_subgroupOf_iff_le_normalizer hK₂calM.1.le).1 hK₂normM))
    have hCAsup : CA ⊔ CB = ⊤ := by
      rw [eq_top_iff]
      intro x _
      have hx : x = e.symm ((e x).1, 1) * e.symm (1, (e x).2) := by
        rw [← map_mul]
        simp
      rw [hx]
      refine Subgroup.mul_mem_sup ?_ ?_
      · show πB (e.symm ((e x).1, 1)) = 1
        simp [πB]
      · show πA (e.symm (1, (e x).2)) = 1
        simp [πA]
    have hCAneCB : CA ≠ CB := by
      intro hEq
      obtain ⟨a, ha⟩ := exists_ne (1 : A)
      have hmemCA : e.symm (a, 1) ∈ CA := by
        show πB (e.symm (a, 1)) = 1
        simp [πB]
      have hmemCB : e.symm (a, 1) ∈ CB := hEq ▸ hmemCA
      have h1 : (e (e.symm (a, 1))).1 = 1 := by
        simpa [πA] using MonoidHom.mem_ker.mp hmemCB
      exact ha (by simpa using h1)
    have hK₁neK₂ : K₁ ≠ K₂ := by
      intro hEq
      apply hCAneCB
      rw [← hbarK₁, ← hbarK₂, hEq]
    have hK₁L2 : IsL2 (Bar2 K₁) (S17.nOf L) := by
      obtain ⟨e1⟩ := s13_bar_equiv hK₁calLp
      exact LieModel.of_mulEquiv
        ((e1.trans (MulEquiv.subgroupCongr hbarK₁)).trans eCA).symm hA
    have hK₂shape : IsL2 (Bar2 K₂) (S17.nOf L) ∨ IsU3 (Bar2 K₂) (S17.nOf L) := by
      obtain ⟨e2⟩ := s13_bar_equiv hK₂calLp
      have e2' : Bar2 K₂ ≃* B := (e2.trans (MulEquiv.subgroupCongr hbarK₂)).trans eCB
      rcases hB with hB2 | hB3
      · exact Or.inl (LieModel.of_mulEquiv e2'.symm hB2)
      · exact Or.inr (LieModel.of_mulEquiv e2'.symm hB3)
    have hpK₁ : p ∣ Nat.card K₁ := by
      have h := S17.dvd_card_bar2_of_isL2 hK₁L2 hpn
      rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (CFSG.pCore 2 ↥K₁)]
      exact h.mul_right _
    have hpK₂ : p ∣ Nat.card K₂ := by
      rcases hK₂shape with hK₂L2 | hK₂U3
      · have h := S17.dvd_card_bar2_of_isL2 hK₂L2 hpn
        rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (CFSG.pCore 2 ↥K₂)]
        exact h.mul_right _
      · have hcard := S17.card_mul_gcd_of_isU3 hK₂U3
        have hgcd : Nat.gcd 3 (2 ^ S17.nOf L + 1) = 1 := by
          have hc : Nat.Coprime 3 (2 ^ S17.nOf L + 1) :=
            (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hnot3
          simpa using hc
        rw [hgcd, mul_one] at hcard
        have hpbar : p ∣ Nat.card (Bar2 K₂) := by
          rw [hcard]
          have h1 : p ∣ (2 ^ (2 * S17.nOf L) - 1) * (2 ^ (3 * S17.nOf L) + 1) :=
            dvd_mul_of_dvd_left hpdvd _
          have h2 : p ∣ (2 ^ (2 * S17.nOf L) - 1) * (2 ^ (3 * S17.nOf L) + 1) *
              2 ^ (3 * S17.nOf L) := dvd_mul_of_dvd_left h1 _
          simpa [mul_comm, mul_left_comm, mul_assoc] using h2
        rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (CFSG.pCore 2 ↥K₂)]
        exact hpbar.mul_right _
    have hK₁p : K₁ ∈ S17.calLp D p := ⟨hK₁calM, hp, hpK₁⟩
    have hK₂p : K₂ ∈ S17.calLp D p := ⟨hK₂calM, hp, hpK₂⟩
    let Dsub : Subgroup G := K₁ ⊔ K₂
    have hDle : Dsub ≤ Lp D p := sup_le hK₁leLp hK₂leLp
    have hDsubNorm : (Dsub.subgroupOf (Lp D p)).Normal := by
      rw [show Dsub.subgroupOf (Lp D p) =
        K₁.subgroupOf (Lp D p) ⊔ K₂.subgroupOf (Lp D p) from
        Subgroup.subgroupOf_sup hK₁leLp hK₂leLp]
      exact @Subgroup.sup_normal ↥(Lp D p) _
        (K₁.subgroupOf (Lp D p)) (K₂.subgroupOf (Lp D p)) hK₁normLp hK₂normLp
    have hDnorm : Lp D p ≤ normalizer (Dsub : Set G) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hDle).1 hDsubNorm
    have hDbar : barImage (Lp D p) Dsub = ⊤ := by
      rw [show Dsub = K₁ ⊔ K₂ from rfl, s13_barImage_sup hK₁leLp hK₂leLp,
        hbarK₁, hbarK₂, hCAsup]
    have hDN : Dsub ⊔ pCoreOf 2 (Lp D p) = Lp D p := by
      have hpre := barPreimage_barImage_eq_sup_pCore (M := Lp D p) (H := Dsub) hDle
      rw [hDbar] at hpre
      have htop : barPreimage (Lp D p) (⊤ : Subgroup (Bar2 (Lp D p))) = Lp D p := by
        refine le_antisymm (uc22p21c_barPreimage_le _ _) fun x hx => ?_
        exact uc22p21c_mem_barPreimage.2 ⟨hx, Subgroup.mem_top _⟩
      rw [htop] at hpre
      simpa [CFSG.Open.pCoreOf] using hpre.symm
    have hdvd : Dsub.relIndex (Lp D p) ∣ Nat.card (pCoreOf 2 (Lp D p)) := by
      have hrelsup : (Dsub.subgroupOf (Lp D p)) ⊔
          ((pCoreOf 2 (Lp D p)).subgroupOf (Lp D p)) = ⊤ := by
        rw [← Subgroup.subgroupOf_sup hDle
          (CFSG.LieType.BorelTits.pCoreOf_le 2 (Lp D p)), hDN, Subgroup.subgroupOf_self]
      have hrel1 : (Dsub.subgroupOf (Lp D p)).relIndex ⊤ =
          (Dsub.subgroupOf (Lp D p)).relIndex
            ((pCoreOf 2 (Lp D p)).subgroupOf (Lp D p)) := by
        rw [← hrelsup]
        exact @Subgroup.relIndex_sup_left ↥(Lp D p) _
          ((pCoreOf 2 (Lp D p)).subgroupOf (Lp D p))
          (Dsub.subgroupOf (Lp D p)) hDsubNorm
      have hrelD : Dsub.relIndex (Lp D p) =
          (Dsub.subgroupOf (Lp D p)).relIndex ⊤ := by
        rw [Subgroup.relIndex_top_right]
        rfl
      have hdvd' : (Dsub.subgroupOf (Lp D p)).relIndex ⊤ ∣
          Nat.card ((pCoreOf 2 (Lp D p)).subgroupOf (Lp D p)) := by
        rw [hrel1]
        have h := Subgroup.relIndex_mul_card (Dsub.subgroupOf (Lp D p))
          ((pCoreOf 2 (Lp D p)).subgroupOf (Lp D p))
        rw [← h]
        exact dvd_mul_right _ _
      have hcardN : Nat.card ((pCoreOf 2 (Lp D p)).subgroupOf (Lp D p)) =
          Nat.card (pCoreOf 2 (Lp D p)) :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe
          (CFSG.LieType.BorelTits.pCoreOf_le 2 (Lp D p))).toEquiv
      rw [hcardN] at hdvd'
      rw [hrelD]
      exact hdvd'
    obtain ⟨k, hk⟩ :=
      IsPGroup.iff_card.mp (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (Lp D p))
    have hdvd' : Dsub.relIndex (Lp D p) ∣ 2 ^ k := by rwa [hk] at hdvd
    obtain ⟨j, -, hj'⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd'
    have hperf : ⁅Lp D p, Lp D p⁆ = Lp D p := by
      rw [← hH]
      exact uc22p21c_Hinf_perfect D.M
    have hLp_le_D : Lp D p ≤ Dsub :=
      Subgroup.le_of_commutator_eq_self_of_relIndex_eq_prime_pow Nat.prime_two
        hDle hDnorm hj' le_rfl hperf
    have hD_eq : Dsub = Lp D p := le_antisymm hDle hLp_le_D
    have hI_eq_D : IOf D p L = Dsub := by
      refine le_antisymm ?_ ?_
      · rw [hD_eq]
        exact hI_le_Lp
      · exact sup_le (le_IOf_of_mem_calLp hj hK₁p) (le_IOf_of_mem_calLp hj hK₂p)
    exact ⟨K₁, K₂, hK₁calM, hK₂calM, hK₁neK₂, hI_eq_D, hK₁L2, hK₂shape,
      show K₁ ⊔ K₂ = Lp D p from hD_eq⟩
  have hmain : ∃ K₁ K₂ : Subgroup G, K₁ ∈ calC D.M ∧ K₂ ∈ calC D.M ∧ K₁ ≠ K₂ ∧
      IOf D p L = K₁ ⊔ K₂ ∧ IsL2 (Bar2 K₁) (S17.nOf L) ∧
      (IsL2 (Bar2 K₂) (S17.nOf L) ∨ IsU3 (Bar2 K₂) (S17.nOf L)) ∧
      K₁ ⊔ K₂ = Lp D p := by
    rcases hn' with ⟨⟨A, B, gA, gB, ⟨e⟩, hA, hB⟩, -⟩ |
      ⟨⟨A, B, gA, gB, ⟨e⟩, hA, hB⟩, -⟩
    · exact @key A B gA gB e hA (Or.inl hB)
    · exact @key A B gA gB e hA (Or.inr hB)
  obtain ⟨K₁, K₂, hK₁calM, hK₂calM, hK₁neK₂, hI_eq, hK₁L2, hK₂shape, hsupLp⟩ := hmain
  have hI_eq_Lp : IOf D p L = Lp D p := by rw [hI_eq, hsupLp]
  have he : Nonempty (Bar2 (IOf D p L) ≃* Bar2 (Lp D p)) := by
    rw [hI_eq_Lp]
    exact ⟨MulEquiv.refl _⟩
  exact ⟨K₁, K₂, hK₁calM, hK₂calM, hK₁neK₂, hI_eq, hK₁L2, hK₂shape,
    hnpow, hn_gt2, isL2U3Product_or_isL2Square_of_bar2_equiv hn' he, hncong⟩

theorem setting1910_of_jM_four (D : Data G) {V₀ V : Subgroup G} {p : ℕ} {L : Subgroup G}
    (h : Hyp19 D V₀ V p L) (h1 : R19_1At D V₀ V p L h) (h42 : S17.R17_42At D V₀ V)
    (h641 : S17.R17_64_1At D V₀ V) (h642 : S17.R17_64_2At D V₀ V)
    (h643 : S17.R17_64_3At D V₀ V) (h57 : S17.R17_57At D V₀ V)
    (hSg : CFSG.LocalAnalysis.UniquenessCase.UC6S846.SigmaStd D) (hDE : DataExt D)
    (hj : S17.jM D p = 4) : Setting1910 D V₀ V p L := by
  obtain ⟨K₁, K₂, -, -, -, hI_eq, -, -, hnpow, hn_gt2, hprod, hcong⟩ :=
    jM_four_structure D h h1 h42 h641 h642 h643 hj
  have h54 : S17.Hyp1754 D p := hyp1754_of_jM_eq_four D h h42 hj
  obtain ⟨n, hn⟩ := h642 p h54
  have hpow : IsPowTwo n := (h643 p h54 n hn).1
  have hrank : CFSG.Open.pRank p D.M = 3 :=
    S17.pRank_eq_three_of_P17_64_2 hSg h57 S17.k_OutL2U3Product_holds h54 hn hpow
  have he : evenRank G = 3 := by
    have h3 : 3 ≤ evenRank G := D.standing.rank
    by_contra hne
    have hgt : 3 < evenRank G := by omega
    have h4 := hDE.four_le hgt p h.hp
    omega
  simp only [Setting1910]
  exact ⟨he, Or.inr (Or.inr ⟨hprod, hn_gt2, hnpow, hcong⟩)⟩

theorem nineteen_ten_of (D : Data G) {V₀ V : Subgroup G} {p : ℕ} {L : Subgroup G}
    (h : Hyp19 D V₀ V p L) (h1 : R19_1At D V₀ V p L h) (h9 : R19_9At D V₀ V p L h)
    (h67 : S17.R17_67At D V₀ V) (h42 : S17.R17_42At D V₀ V)
    (h641 : S17.R17_64_1At D V₀ V) (h642 : S17.R17_64_2At D V₀ V)
    (h643 : S17.R17_64_3At D V₀ V) (h57 : S17.R17_57At D V₀ V)
    (hSg : CFSG.LocalAnalysis.UniquenessCase.UC6S846.SigmaStd D) (hDE : DataExt D) :
    R19_10At D V₀ V p L h := by
  by_cases hj : S17.jM D p = 4
  · exact setting1910_of_jM_four D h h1 h42 h641 h642 h643 h57 hSg hDE hj
  · exact setting1910_of_jM_ne_four D h h1 h9 h67 h42 hj

end Certificates

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S19
