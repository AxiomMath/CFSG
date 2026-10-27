module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenThirtySixAN3C
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.InP11OfStrongly
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.ComponentTorus

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

open Subgroup CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.UC6S846
open CFSG.QuasithinUnique (IsSylowTwoOf)
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem conjClosure_eq_of_ncard_le_one {M L : Subgroup G}
    (h : (conjSetOf M L).ncard ≤ 1) : L = conjClosure M L := by
  classical
  have hsub : (conjSetOf M L).Subsingleton := Set.ncard_le_one_iff_subsingleton.1 h
  have hmem : ∀ g : G, g ∈ M → L.map (MulAut.conj g).toMonoidHom = L := by
    intro g hg
    have h1 : L.map (MulAut.conj g).toMonoidHom ∈ conjSetOf M L := ⟨g, hg, rfl⟩
    have h2 : L ∈ conjSetOf M L :=
      ⟨1, Subgroup.one_mem M, by rw [map_one MulAut.conj]; exact (Subgroup.map_id L).symm⟩
    exact hsub h1 h2
  have hle : conjClosure M L ≤ L := by
    refine iSup₂_le fun K hK => ?_
    obtain ⟨g, hg, rfl⟩ := hK
    exact (hmem g hg).le
  exact (le_antisymm hle (TwelveTwentyThree.le_conjClosure M L)).symm

theorem exists_three_mem_conjSetOf {M L : Subgroup G}
    (h : 3 ≤ (conjSetOf M L).ncard) :
    ∃ K₁ K₂ K₃ : Subgroup G,
      K₁ ∈ conjSetOf M L ∧ K₂ ∈ conjSetOf M L ∧ K₃ ∈ conjSetOf M L ∧
        K₁ ≠ K₂ ∧ K₁ ≠ K₃ ∧ K₂ ≠ K₃ := by
  classical
  let F : Finset (Subgroup G) := (Set.toFinite (conjSetOf M L)).toFinset
  have hF : 2 < F.card := by
    have hcard : F.card = (conjSetOf M L).ncard := by
      change (Set.toFinite (conjSetOf M L)).toFinset.card = (conjSetOf M L).ncard
      exact (Set.ncard_eq_toFinset_card (conjSetOf M L) (Set.toFinite _)).symm
    omega
  have hmem : ∀ K : Subgroup G, K ∈ F ↔ K ∈ conjSetOf M L := by
    intro K
    simp [F]
  obtain ⟨K₁, hK₁, K₂, hK₂, K₃, hK₃, h₁₂, h₁₃, h₂₃⟩ := Finset.two_lt_card.mp hF
  exact ⟨K₁, K₂, K₃, (hmem K₁).1 hK₁, (hmem K₂).1 hK₂, (hmem K₃).1 hK₃, h₁₂, h₁₃, h₂₃⟩

@[expose] def Gap17_36a_n3_three_torus (D : Data G) (V₀ V L : Subgroup G) (n : ℕ) : Prop :=
  Ctx17_33 D V₀ V L n → V₀ ≠ ⊥ → n = 3 →
    3 ∣ Nat.card (Subgroup.center (Bar2 L)) → 3 ≤ (conjSetOf D.M L).ncard →
      ∃ E : Subgroup G, E ≤ conjClosure D.M L ∧ IsElemAbelian 3 E ∧
        Permutes E D.T ∧ 2 ≤ CFSG.Open.pRank 3 E

@[expose] def Gap17_36a_n3_two_p (D : Data G) (V₀ V L : Subgroup G) (n : ℕ) : Prop :=
  Ctx17_33 D V₀ V L n → V₀ ≠ ⊥ → n = 3 →
    3 ∣ Nat.card (Subgroup.center (Bar2 L)) → (conjSetOf D.M L).ncard = 2 →
      ∃ X : Subgroup G, F11.InP11 D X

theorem seventeen_thirtysix_a_n3_three
    (D : Data G) (V₀ V L : Subgroup G) (n : ℕ) (c : Ctx17_33 D V₀ V L n)
    (h1 : ∀ (hV : Hyp125 D V₀ V), R17_1At D V₀ V hV)
    (hSg : SigmaStd D)
    (hCen : UCK.U3Center)
    (hTorus : Gap17_36a_n3_three_torus D V₀ V L n)
    (hV0 : V₀ ≠ ⊥) (hn : n = 3)
    (hZ : 3 ∣ Nat.card (Subgroup.center (Bar2 L)))
    (hcard : 3 ≤ (conjSetOf D.M L).ncard) :
    L = conjClosure D.M L := by
  classical
  obtain ⟨K₁, K₂, K₃, hK₁, hK₂, hK₃, h₁₂, h₁₃, h₂₃⟩ := exists_three_mem_conjSetOf hcard
  have hZcard : Nat.card (Subgroup.center (Bar2 L)) = 3 :=
    Nat.dvd_antisymm (hCen (Bar2 L) n c.shape) hZ
  have h4 : 4 ≤ CFSG.Open.pRank 3 D.M :=
    four_le_pRank_three_of_three_conj c.mem_calC c.shape hn hZcard hK₁ hK₂ hK₃ h₁₂ h₁₃ h₂₃
  have hsig : 3 ∈ D.sig := hSg.four_mem 3 Nat.prime_three (by norm_num) h4
  have hstr : CFSG.RankThree.PartOne.IsStronglyPEmbedded 3 D.M :=
    sp_of_mem_sig hSg (not_solvable_of_mem_calC c.mem_calC) hsig
  obtain ⟨E, hEL₀, hEel, hEperm, hErank⟩ := hTorus c hV0 hn hZ hcard
  have hEM : E ≤ D.M := hEL₀.trans (TwelveTwentyThree.conjClosure_le c.mem_calC.1.le)
  have hEnc : ¬ IsCyclic ↥E := by
    intro hcyc
    have h2 : CFSG.Open.pRank 3 E ≤ 1 :=
      CFSG.SectionRank.pRank_le_one_of_isCyclic Nat.prime_three hcyc
    omega
  exact absurd ((h1 c.hyp125).2
    ⟨E, inP11_of_strongly Nat.prime_three (by norm_num) hstr hEM hEel.isPGroup hEel.2
      hEnc hEperm⟩).1 hV0

theorem seventeen_thirtysix_a_n3_two
    (D : Data G) (V₀ V L : Subgroup G) (n : ℕ) (c : Ctx17_33 D V₀ V L n)
    (h1 : ∀ (hV : Hyp125 D V₀ V), R17_1At D V₀ V hV)
    (hP : Gap17_36a_n3_two_p D V₀ V L n)
    (hV0 : V₀ ≠ ⊥) (hn : n = 3)
    (hZ : 3 ∣ Nat.card (Subgroup.center (Bar2 L)))
    (hcard : (conjSetOf D.M L).ncard = 2) :
    L = conjClosure D.M L :=
  absurd ((h1 c.hyp125).2 (hP c hV0 hn hZ hcard)).1 hV0

theorem seventeen_thirtysix_a_n3
    (D : Data G) (V₀ V L : Subgroup G) (n : ℕ) (c : Ctx17_33 D V₀ V L n)
    (h1 : ∀ (hV : Hyp125 D V₀ V), R17_1At D V₀ V hV)
    (hSg : SigmaStd D)
    (hCen : UCK.U3Center)
    (hTwo : Gap17_36a_n3_two_p D V₀ V L n)
    (hThree : Gap17_36a_n3_three_torus D V₀ V L n)
    (hV0 : V₀ ≠ ⊥) (hn : n = 3)
    (hZ : 3 ∣ Nat.card (Subgroup.center (Bar2 L))) :
    L = conjClosure D.M L := by
  have hself : L ∈ conjSetOf D.M L :=
    ⟨1, Subgroup.one_mem D.M, by rw [map_one MulAut.conj]; exact (Subgroup.map_id L).symm⟩
  have hpos : 0 < (conjSetOf D.M L).ncard :=
    Set.ncard_pos (Set.toFinite _) |>.2 ⟨L, hself⟩
  rcases lt_or_ge (conjSetOf D.M L).ncard 2 with h | h
  · exact conjClosure_eq_of_ncard_le_one (by omega)
  · rcases lt_or_eq_of_le h with h2 | h2
    · exact seventeen_thirtysix_a_n3_three D V₀ V L n c h1 hSg hCen hThree hV0 hn hZ h2
    · exact seventeen_thirtysix_a_n3_two D V₀ V L n c h1 hTwo hV0 hn hZ h2.symm

theorem seventeen_thirtysix_a_of_subgaps
    (D : Data G) (V₀ V : Subgroup G)
    (h352 : R17_35_2At D V₀ V)
    (h1 : ∀ (hV : Hyp125 D V₀ V), R17_1At D V₀ V hV)
    (hSg : SigmaStd D)
    (hK3 : CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.K_BorelTorusAbelian)
    (hCen : UCK.U3Center) (hSyl : UCK.U3Syl)
    (hBorel : K_U3CartanRank)
    (hTwo : ∀ (L : Subgroup G) (n : ℕ), Gap17_36a_n3_two_p D V₀ V L n)
    (hThree : ∀ (L : Subgroup G) (n : ℕ), Gap17_36a_n3_three_torus D V₀ V L n) :
    R17_36aAt D V₀ V := by
  intro L n c
  by_contra hne
  have hV0 : V₀ ≠ ⊥ := by
    intro h0
    exact hne ((h352 L n c h0).2.2.2)
  have hn2 : 2 ≤ n := CFSG.LocalAnalysis.UniquenessCase.PartTwo.s13_two_le_of_isU3 c.shape.2
  have hL : L ∈ calC D.M := c.mem_calC
  have hnn : ¬ (L.subgroupOf D.M).Normal := by
    intro hN
    apply hne
    have hNM : D.M ≤ Subgroup.normalizer (L : Set G) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer c.mem_calC.1.le).1 hN
    have hcl : UC22.conjClosure D.M L ≤ L := by
      refine iSup₂_le fun K hK => ?_
      obtain ⟨g, hg, rfl⟩ := hK
      rintro x ⟨y, hy, rfl⟩
      exact (Subgroup.mem_normalizer_iff.mp (hNM hg) y).1 hy
    exact le_antisymm (uc22p22v_le_conjClosure D.M L) hcl
  have hnn' : ¬ D.M ≤ Subgroup.normalizer (L : Set G) := by
    intro h
    exact hnn ((Subgroup.normal_subgroupOf_iff_le_normalizer hL.1.le).2 h)
  have hchev : CIsChevOver (BarInf L) n := by
    obtain ⟨e⟩ := UC22.uc22p21k_barInf_equiv_of_calC c.mem_calC
    have hLie : CFSG.Blueprint.LieModel (BarInf L) .PSU 3 2 n :=
      CFSG.Blueprint.LieModel.of_mulEquiv e.symm c.shape.2
    exact ⟨.PSU, 3, hLie.admissible, hLie⟩
  obtain ⟨S, hS⟩ := CFSG.GroupTheory.PermSylowTwo.exists_isSylowTwoOf_top (Bar2 L)
  have key : ∀ (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (hcond : 3 < p ∨ n = 3)
      (hpdvd : p ∣ 2 ^ n + 1) (hZ : ¬ p ∣ Nat.card (Subgroup.center (Bar2 L)))
      (h4 : 4 ≤ CFSG.Open.pRank p D.M), False := by
    intro p hp hp2 hcond hpdvd hZ h4
    have hpsig : p ∈ D.sig := hSg.four_mem p hp hp2 h4
    have hstr : CFSG.RankThree.PartOne.IsStronglyPEmbedded p D.M :=
      sp_of_mem_sig hSg (not_solvable_of_mem_calC hL) hpsig
    have hrank : 1 ≤ CFSG.Open.pRank p
        (⊤ : Subgroup (TauCeti.Subgroup.normalizerQuotient S)) :=
      hBorel (Bar2 L) n p c.shape hp hpdvd hcond S hS
    obtain ⟨E, hEB, hEel, hperm, hErank⟩ :=
      exists_permuting_elemAbelian_noncyclic_of_calC (D := D) (L := L)
        (X := conjClosure D.M L) (n := n) (r := p) hL rfl hchev hK3 hnn hZ S hS hrank hp hp2
    have hEM : E ≤ D.M :=
      (hEB.trans inf_le_left).trans
        (CFSG.LocalAnalysis.UniquenessCase.PartTwo.TwelveTwentyThree.conjClosure_le hL.1.le)
    have hEnc : ¬ IsCyclic ↥E := by
      intro hcyc
      have h2 : CFSG.Open.pRank p E ≤ 1 :=
        CFSG.SectionRank.pRank_le_one_of_isCyclic hp hcyc
      omega
    exact hV0 ((h1 c.hyp125).2
      ⟨E, inP11_of_strongly hp hp2 hstr hEM hEel.isPGroup hEel.2 hEnc hperm⟩).1
  by_cases hn3 : n = 3
  ·
    subst hn3
    by_cases hZ3 : 3 ∣ Nat.card (Subgroup.center (Bar2 L))
    · exact hne (seventeen_thirtysix_a_n3 D V₀ V L 3 c h1 hSg hCen (hTwo L 3)
        (hThree L 3) hV0 rfl hZ3)
    · have h3rank : 2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup (Bar2 L)) :=
        UC22.two_le_pRank_three_of_isSU3 c.shape ⟨1, rfl⟩
      obtain ⟨E0, hE0L, hE0el, a, ha2, hE0card⟩ :=
        exists_elemAbelian_sq_lift_of_isSU3 (L := L) (q := 3) Nat.prime_three
          (by norm_num) h3rank
      have h4 : 4 ≤ CFSG.Open.pRank 3 D.M := by
        have h := calCRankTwice D.M L hL hnn' 3 Nat.prime_three (by norm_num) hZ3 E0 hE0L
          hE0el a hE0card
        omega
      exact key 3 Nat.prime_three (by norm_num) (Or.inr rfl) (by norm_num) hZ3 h4
  ·
    obtain ⟨p, hp, hp3, hpdvd⟩ := uc2_17_36a_exists_prime_gt_three hn2 hn3
    have hp2 : p ≠ 2 := by omega
    have hZ : ¬ p ∣ Nat.card (Subgroup.center (Bar2 L)) := by
      intro hdvd
      have h3 : Nat.card (Subgroup.center (Bar2 L)) ∣ 3 := hCen (Bar2 L) n c.shape
      have hle := Nat.le_of_dvd (by norm_num) (hdvd.trans h3)
      omega
    obtain ⟨E0, hE0L, hE0el, hE0card⟩ :=
      exists_elemAbelian_sq_of_isSU3 hSyl c.shape hp hp3 hpdvd
    have h4 : 4 ≤ CFSG.Open.pRank p D.M := by
      have h := calCRankTwice D.M L hL hnn' p hp hp2 hZ E0 hE0L hE0el 2 hE0card
      omega
    exact key p hp hp2 (Or.inl hp3) hpdvd hZ h4

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17
