module

public import CFSG.Quasithin.EmptyFaithful.S152He12A
public import CFSG.Quasithin.EmptyFaithful.S152He8Cases
public import CFSG.Quasithin.EmptyFaithful.S152He2Cases
public import CFSG.Quasithin.EmptyFaithful.S152QA
public import CFSG.Quasithin.EmptyFaithful.S152N2Glue
public import CFSG.Quasithin.EmptyFaithful.S152N2L14
public import CFSG.Quasithin.Background.C1PackS15212C
public import CFSG.Quasithin.EmptyFaithful.S151cStmt2
public import CFSG.Quasithin.EmptyFaithful.S152N2L14D

public section

namespace CFSG.Quasithin

namespace He12

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.S152N CFSG.Quasithin.S152N2
open CFSG.Quasithin.C1Pack12
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

structure Lemma15212ConclW (T Mc M H B : Subgroup G) : Prop where
  xi : IsXi T (oTwoUpper H)
  cases : conjClosure (oTwoUpper H) Mc = oTwoUpper H ∨
    Case15212ii T Mc (conjClosure (oTwoUpper H) Mc) ∨
    Case15212iii T Mc (conjClosure (oTwoUpper H) Mc) ∨
    Case15212He T Mc (conjClosure (oTwoUpper H) Mc)
  unique : IsUniqueM H Mc
  normal : H ≤ Subgroup.normalizer ((⁅V154 T Mc M, B⁆ : Subgroup G) : Set G)
  normalizer_le : Subgroup.normalizer ((⁅V154 T Mc M, B⁆ : Subgroup G) : Set G) ≤ Mc
  eq_oThreePrime_of_ne : conjClosure (oTwoUpper H) Mc ≠ oTwoUpper H →
    conjClosure (oTwoUpper H) Mc = oPrimeResidualOf 3 Mc
  three_centralizes : ∀ x ∈ Mc, (∃ k : ℕ, orderOf x = 3 ^ k) →
    x ∈ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G)
  le_centralizer : conjClosure (oTwoUpper H) Mc ≤
    Subgroup.centralizer (quasithinOmegaOneCenter T : Set G)
  not_six : ¬ Case1512Six T Mc M
  eq_VZ : V154 T Mc M = VZ T M

@[expose] def StageLemma15212W : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M : Subgroup G), Setting152 T Mc M →
    ∀ H : Subgroup G, IsHStar T M H → ∀ B ∈ sigmaPrime T H (V154 T Mc M),
      Lemma15212ConclW T Mc M H B

structure Core15212W (T Mc M H : Subgroup G) : Prop where
  cases : conjClosure (oTwoUpper H) Mc = oTwoUpper H ∨
    Case15212ii T Mc (conjClosure (oTwoUpper H) Mc) ∨
    Case15212iii T Mc (conjClosure (oTwoUpper H) Mc) ∨
    Case15212He T Mc (conjClosure (oTwoUpper H) Mc)
  eq_oThreePrime_of_ne : conjClosure (oTwoUpper H) Mc ≠ oTwoUpper H →
    conjClosure (oTwoUpper H) Mc = oPrimeResidualOf 3 Mc
  three_centralizes : ∀ x ∈ Mc, (∃ k : ℕ, orderOf x = 3 ^ k) →
    x ∈ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G)

@[expose] def Input15212CoreW : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M : Subgroup G), Setting152 T Mc M →
    ∀ H : Subgroup G, IsHStar T M H → Core15212W T Mc M H

theorem stageLemma15212W_of_core_ce (h1416 : StageLemma1416) (h1515 : StageLemma1515CE)
    (h15201 : StageLemma15201) (h5 : StageLemma15205)
    (h1519 : StageLemma1519) (h15208 : StageLemma15208) (h15209 : StageNotation15209)
    (h15211 : StageLemma15211) (core : Input15212CoreW) : StageLemma15212W := by
  intro G _ _ T Mc M hs H hH B hB
  have s := St12.of_stages h5 h1519 h15208 h15209 h15211 hs hH hB
  have c := core G T Mc M hs H hH
  have hle := le_centralizer_of_cases hs h1416 s.c19 hH c.cases
  have hd : S152Y.Data T Mc M :=
    ⟨hs.qtfe, hs.mf, h1515 G T Mc M hs.qtfe hs.mf hs.ce, h15201 G T Mc M hs⟩
  have hsix : ¬ Case1512Six T Mc M := not_case1512Six_of_threeElements hd c.three_centralizes
  exact ⟨s.xi, c.cases, s.unique, s.H_le_normalizer, s.normalizer_le, c.eq_oThreePrime_of_ne,
    c.three_centralizes, hle, hsix, V154_eq_VZ hsix⟩

theorem oPrimeResidualOf_le_conjClosure_of_ne
    (hA3 : ∀ (G : Type) [Group G] [Finite G], A3Orbits G) (h122 : Lemma122A) (hF : A318Facts)
    (h36 : A36ForSQTK) (h38 : A38ForSQTK) (hK : KnownFacts15122Types)
    {T Mc M H : Subgroup G} (hs : Setting152 T Mc M)
    (hcases : conjClosure (oTwoUpper H) Mc = oTwoUpper H ∨
      Case15212ii T Mc (conjClosure (oTwoUpper H) Mc) ∨
      Case15212iii T Mc (conjClosure (oTwoUpper H) Mc) ∨
      Case15212He T Mc (conjClosure (oTwoUpper H) Mc))
    (hne : conjClosure (oTwoUpper H) Mc ≠ oTwoUpper H) :
    oPrimeResidualOf 3 Mc ≤ conjClosure (oTwoUpper H) Mc := by
  have hTMc : T ≤ Mc := hs.qtfe.t_le_mc
  have hPMc : pCoreOf 2 Mc ≠ ⊥ := pCoreOf_ne_bot_of_isTwoLocal hs.qtfe.mc_max.1
  have hSQ : SQTKGroup ↥Mc :=
    sqtkGroup_of_pCoreOf_ne_bot hs.qtfe.qtke hs.qtfe.simple hs.qtfe.nonabelian hPMc
  have hTKc : T ≤ Subgroup.normalizer ((conjClosure (oTwoUpper H) Mc : Subgroup G) : Set G) :=
    fun t ht => le_normalizer_conjClosure _ _ (hTMc ht)
  rcases hcases with h | h | h | h
  · exact absurd h hne
  · exact (He8.eq_of_caseii hF h36 h38 hK hSQ hTKc h).ge
  · exact He8.le_of_caseiii (hA3 G) h122 hs h
  · exact (He8.eq_of_caseHe hF h36 h38 hK hSQ h).ge

theorem input15212CoreW_of_prop134He
    (h134 : EmptyFaithfulMultiple.Prop134E9He)
    (hA3 : ∀ (G : Type) [Group G] [Finite G], A3Orbits G) (h1416 : StageLemma1416)
    (h15208 : StageLemma15208) (h15209 : StageNotation15209) (insp : Insp15212)
    (h1519 : StageLemma1519) (h122 : Lemma122A) (hF : A318Facts) (h36 : A36ForSQTK)
    (h38 : A38ForSQTK) (hK : KnownFacts15122Types) : Input15212CoreW := by
  intro G _ _ T Mc M hs H hH
  have hcases := cases15212_of_prop134He h134 hA3 h1416 h15208 h15209 insp G T Mc M hs H hH
  obtain ⟨φ⟩ := h15208 G T Mc M hs H hH
  have hHMc : H ≤ Mc := (h15209 G T Mc M hs H hH).le_mc
  have hle : conjClosure (oTwoUpper H) Mc ≤ oPrimeResidualOf 3 Mc :=
    conjClosure_oTwoUpper_le_oPrimeResidualOf_three hHMc φ
  have c19 := h1519 G T Mc M hs.qtfe hs.mf hs.ce
  have heq : conjClosure (oTwoUpper H) Mc ≠ oTwoUpper H →
      conjClosure (oTwoUpper H) Mc = oPrimeResidualOf 3 Mc := fun hne =>
    le_antisymm hle (oPrimeResidualOf_le_conjClosure_of_ne hA3 h122 hF h36 h38 hK hs hcases hne)
  refine ⟨hcases, heq, ?_⟩
  intro x hx hk
  obtain ⟨k, hk⟩ := hk
  by_cases hI : conjClosure (oTwoUpper H) Mc = oTwoUpper H
  · exact mem_centralizer_Z_of_threePower h15208 h15209 h1519 hs hH hI hx hk
  · have h4 := heq hI
    have hxK : x ∈ conjClosure (oTwoUpper H) Mc := by
      rw [h4]
      exact Subgroup.subset_closure ⟨hx, k, hk⟩
    exact le_centralizer_of_cases hs h1416 c19 hH hcases hxK

theorem bdata_15213W (h15210 : StageLemma15210) (h15211 : StageLemma15211)
    (h15212 : StageLemma15212W) {T Mc M H : Subgroup G} (hs : Setting152 T Mc M)
    (hH : IsHStar T M H) (c209 : Notation15209Concl T Mc M H) (hVcard : Nat.card (V154 T Mc M) = 16)
    {B : Subgroup G} (hB : B ∈ sigmaPrime T H (V154 T Mc M)) :
    B ≤ T ∧ Nat.card (autOn B (V154 T Mc M)) = 2 ∧ autOn B (V154 T Mc M) ≤ mBar0 T Mc M ∧
      Nat.card (⁅V154 T Mc M, B⁆ : Subgroup G) = 4 ∧
      T ≤ Subgroup.normalizer ((⁅V154 T Mc M, B⁆ : Subgroup G) : Set G) ∧
      ∀ y ∈ autOn M (V154 T Mc M), y ^ 3 = 1 →
        (∀ b ∈ autOn B (V154 T Mc M), b * y = y * b) → y = 1 := by
  have hqtfe := hs.qtfe
  have hMT : InM T M := hs.mf.1.1
  have hTM : T ≤ M := hMT.2
  have hMV : M ≤ Subgroup.normalizer (V154 T Mc M : Set G) := le_normalizer_V154 T Mc M
  have hVE : IsElemAbelian 2 (V154 T Mc M) :=
    isElemAbelian_mono151 (V154_le_VZ T Mc M) (isElemAbelian_VZ hqtfe hMT)
  have hVT : V154 T Mc M ≤ T := (V154_le_VZ T Mc M).trans (isTwoReducedIn_VZ hqtfe hMT).2
  have hTH : T ≤ H := by rw [c209.eq_inf]; exact inf_le_right
  have hBT : B ≤ T := le_T_of_mem_sigmaSet hqtfe.sylow hTH hB.1
  have c211 := h15211 G T Mc M hs H hH B hB
  have hQT : autOn B (V154 T Mc M) ∈ QsetOn T (V154 T Mc M) :=
    mem_qsetOn_of_le c211.quad (A4.autOn_mono hBT)
  have c210 := h15210 G T Mc M hs _ hQT
  have hWeq : ⁅V154 T Mc M, preOn T (V154 T Mc M) (autOn B (V154 T Mc M))⁆ =
      ⁅V154 T Mc M, B⁆ := commutator_preOn_eq hVE hBT hTM hMV
  have hWcard : Nat.card (⁅V154 T Mc M, B⁆ : Subgroup G) = 4 := c211.card
  have hTW : T ≤ Subgroup.normalizer ((⁅V154 T Mc M, B⁆ : Subgroup G) : Set G) := by
    rw [← hWeq]; exact c210.2.2.2
  have c212 := h15212 G T Mc M hs H hH B hB
  have hW1 : (⁅V154 T Mc M, B⁆ : Subgroup G) ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hWcard
    omega
  have hWV : (⁅V154 T Mc M, B⁆ : Subgroup G) ≤ V154 T Mc M := by
    rw [Subgroup.commutator_le]
    intro v hv b hb
    have hbN : b ∈ Subgroup.normalizer (V154 T Mc M : Set G) := hMV (hTM (hBT hb))
    have h1 : b * v⁻¹ * b⁻¹ ∈ V154 T Mc M :=
      (Subgroup.mem_normalizer_iff.mp hbN _).mp ((V154 T Mc M).inv_mem hv)
    have : ⁅v, b⁆ = v * (b * v⁻¹ * b⁻¹) := by simp only [commutatorElement_def]; group
    rw [this]
    exact (V154 T Mc M).mul_mem hv h1
  obtain ⟨w₀, hw₀W, hw₀1, hw₀Z⟩ := exists_w₀ hqtfe.sylow.1 hWV hVT hVE hTW hW1
  have hcen : ∀ g ∈ Mc, (∃ a : ℕ, g ^ (3 ^ a) = 1) → g * w₀ = w₀ * g := by
    rintro g hgMc ⟨a, ha⟩
    have hord : orderOf g ∣ 3 ^ a := orderOf_dvd_of_pow_eq_one ha
    obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hord
    have hgC := c212.three_centralizes g hgMc ⟨k, hk⟩
    exact (Subgroup.mem_centralizer_iff.mp hgC w₀ hw₀Z).symm
  have hstar := star_lemma hVE hVcard hMV (hBT.trans hTM) c210.2.1 hWcard c212.normalizer_le
    hw₀W hw₀1 hcen
  exact ⟨hBT, c210.2.1, c210.1, hWcard, hTW, hstar⟩

theorem stageLemma15213W_of (h15201 : StageLemma15201) (h15209 : StageNotation15209)
    (h15210 : StageLemma15210) (h15211 : StageLemma15211) (h15212 : StageLemma15212W)
    (hΩ : Omega4PlusIsS3xS3) (hFr : Frobenius20IsSz2) : StageLemma15213 := by
  intro G _ _ T Mc M hs H hH
  have hqtfe := hs.qtfe
  have hMT : InM T M := hs.mf.1.1
  have hTM : T ≤ M := hMT.2
  have hMV : M ≤ Subgroup.normalizer (V154 T Mc M : Set G) := le_normalizer_V154 T Mc M
  have hVE : IsElemAbelian 2 (V154 T Mc M) :=
    isElemAbelian_mono151 (V154_le_VZ T Mc M) (isElemAbelian_VZ hqtfe hMT)
  have c201 := h15201 G T Mc M hs
  have hVcard : Nat.card (V154 T Mc M) = 16 := c201.card
  have c209 := h15209 G T Mc M hs H hH
  let _ : CommGroup ↥(V154 T Mc M) := commGroupOfElemAbelian hVE
  have hV2 : ∀ v : ↥(V154 T Mc M), v ^ 2 = 1 := fun v =>
    Subtype.ext (by simpa [sq] using hVE.2 v v.2)
  have hsyl : IsSylowTwoOf (autOn T (V154 T Mc M)) (autOn M (V154 T Mc M)) :=
    B2F.isSylowTwoOf_autI hVE hMV (isSylowTwoOf_of_le151 hqtfe.sylow hTM)
  have hdata := fun (B : Subgroup G) (hB : B ∈ sigmaPrime T H (V154 T Mc M)) =>
    bdata_15213W h15210 h15211 h15212 hs hH c209 hVcard hB
  set Bs : Set (Subgroup (MulAut (V154 T Mc M))) :=
    {B' | ∃ B ∈ sigmaPrime T H (V154 T Mc M), B' = autOn B (V154 T Mc M)} with hBsdef
  have hmemBs : ∀ B ∈ sigmaPrime T H (V154 T Mc M), autOn B (V154 T Mc M) ∈ Bs :=
    fun B hB => ⟨B, hB, rfl⟩
  have hBsT : ∀ B' ∈ Bs, B' ≤ autOn T (V154 T Mc M) ∧ Nat.card B' = 2 := by
    rintro _ ⟨B, hB, rfl⟩
    obtain ⟨hBT, hB2, -⟩ := hdata B hB
    exact ⟨A4.autOn_mono hBT, hB2⟩
  have hBsstar : ∀ B' ∈ Bs, ∀ y ∈ autOn M (V154 T Mc M), y ^ 3 = 1 →
      (∀ b ∈ B', b * y = y * b) → y = 1 := by
    rintro _ ⟨B, hB, rfl⟩
    exact (hdata B hB).2.2.2.2.2
  have hcomm4 : ∀ B ∈ sigmaPrime T H (V154 T Mc M),
      Nat.card (commV (autOn B (V154 T Mc M))) = 4 := by
    intro B hB
    obtain ⟨hBT, -, -, hWcard, -⟩ := hdata B hB
    have := commutator_eq_map_commV hVE (hBT.trans (hTM.trans hMV))
    rw [this, Subgroup.card_map_of_injective (V154 T Mc M).subtype_injective] at hWcard
    exact hWcard
  have hX₀le : mBar0 T Mc M ≤ autOn M (V154 T Mc M) := by
    have : mBar0 T Mc M = JhatOn M (V154 T Mc M) := rfl
    rw [this, JhatOn_eq hVE]
    exact @Jhat_le ↥(V154 T Mc M) (commGroupOfElemAbelian hVE) inferInstance _
  have hX₀n : autOn M (V154 T Mc M) ≤ Subgroup.normalizer (mBar0 T Mc M : Set _) := by
    intro g hg
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · exact fun hy => JhatOn_normalized hg hy
    · intro hy
      have := JhatOn_normalized ((autOn M (V154 T Mc M)).inv_mem hg) hy
      have e : g⁻¹ * (g * y * g⁻¹) * g⁻¹⁻¹ = y := by group
      rwa [e] at this
  have key : (Case15213i T Mc M ∨ Case15213ii T Mc M H) ∧
      ShapeConcl (autOn M (V154 T Mc M)) (autOn T (V154 T Mc M)) Bs := by
    rcases c201.cases with hOne | hTwo | hThree | hFive
    · have hOne' := hOne
      obtain ⟨-, hXA, ⟨e⟩⟩ := hOne
      have hX : Nonempty (↥(autOn M (V154 T Mc M)) ≃* DihedralGroup 3) :=
        ⟨(MulEquiv.subgroupCongr hXA).trans e⟩
      obtain ⟨hsmall, hconcl⟩ := case_one hsyl hX Bs hBsT
      exact ⟨Or.inl ⟨Or.inl hOne', hsmall⟩, hconcl⟩
    · exfalso
      obtain ⟨B₁, hB₁⟩ := c209.sigmaPrime_nonempty
      obtain ⟨-, -, ⟨e⟩⟩ := hTwo
      exact case_two_false e (A4.autOn_mono ((hdata B₁ hB₁).1.trans hTM))
        ((hdata B₁ hB₁).2.2.2.2.2)
    · have hThree' := hThree
      obtain ⟨-, -, hV', hΩ'⟩ := hThree
      obtain ⟨e⟩ : Nonempty (↥(autOn M (V154 T Mc M)) ≃* DihedralGroup 3 × DihedralGroup 3) :=
        @hΩ ↥(V154 T Mc M) (commGroupOfElemAbelian hV') inferInstance _ hΩ'
      have hconcl := shapeConcl_of_s3s3 hsyl e Bs
        (fun B' hB' => ⟨(hBsT B' hB').1, (hBsT B' hB').2, hBsstar B' hB'⟩)
      exact ⟨Or.inr ⟨hThree', fun B hB => hconcl.isB0 _ (hmemBs B hB)⟩, hconcl⟩
    · have hFive' := hFive
      obtain ⟨-, hD5, -, hF⟩ := hFive
      rcases hF with hFeq | hZ15
      · have hF' : ∀ K : Subgroup (MulAut (V154 T Mc M)), K ≤ autOn M (V154 T Mc M) →
            autOn M (V154 T Mc M) ≤ Subgroup.normalizer (K : Set _) →
            (∀ a ∈ K, ∀ b ∈ K, a * b = b * a) → K ≤ mBar0 T Mc M := by
          intro K hKX hKn hKc
          have h1 := le_fittingIn_of_comm hKX hKn hKc
          rw [hFeq] at h1
          exact h1.trans (fittingIn_le _)
        obtain ⟨hsmall, hconcl⟩ := case_five_small hFr hV2 hVcard hsyl hX₀le hX₀n hD5 hF' Bs hBsT
        exact ⟨Or.inl ⟨Or.inr hFive', hsmall⟩, hconcl⟩
      · exfalso
        obtain ⟨B₁, hB₁⟩ := c209.sigmaPrime_nonempty
        obtain ⟨hB₁T, hB₁2, -, -, -, hB₁star⟩ := hdata B₁ hB₁
        exact case_five_z15 hV2 hVcard (F := fittingIn (autOn M (V154 T Mc M)))
          (fittingIn_le _) (le_normalizer_map_subtype' _ _) hZ15
          (A4.autOn_mono (hB₁T.trans hTM)) hB₁2 (hcomm4 B₁ hB₁) hB₁star
  obtain ⟨hcases, hconcl⟩ := key
  obtain ⟨B₁, hB₁⟩ := c209.sigmaPrime_nonempty
  have hunique : ∀ B ∈ sigmaPrime T H (V154 T Mc M),
      autOn B (V154 T Mc M) = autOn B₁ (V154 T Mc M) :=
    fun B hB => hconcl.uniq _ _ (hBsT _ (hmemBs B hB)).1 (hBsT _ (hmemBs B₁ hB₁)).1
      (hBsT _ (hmemBs B hB)).2 (hBsT _ (hmemBs B₁ hB₁)).2 (hconcl.isB0 _ (hmemBs B hB))
      (hconcl.isB0 _ (hmemBs B₁ hB₁))
  refine ⟨hcases, autOn B₁ (V154 T Mc M), ⟨(hBsT _ (hmemBs B₁ hB₁)).1,
    (hBsT _ (hmemBs B₁ hB₁)).2, hconcl.isB0 _ (hmemBs B₁ hB₁)⟩, ?_, ?_⟩
  · intro B₀' hB₀'
    exact hconcl.uniq B₀' _ hB₀'.1 (hBsT _ (hmemBs B₁ hB₁)).1 hB₀'.2.1
      (hBsT _ (hmemBs B₁ hB₁)).2 hB₀'.2.2 (hconcl.isB0 _ (hmemBs B₁ hB₁))
  · intro B hB
    have hEq := hunique B hB
    have hBT := (hdata B hB).1
    have hBN : B ≤ Subgroup.normalizer (V154 T Mc M : Set G) := hBT.trans (hTM.trans hMV)
    have hfc : fixV (autOn B (V154 T Mc M)) = commV (autOn B (V154 T Mc M)) :=
      fixV_eq_commV_of_card_two hV2 hVcard (hBsT _ (hmemBs B hB)).2 (hcomm4 B hB)
    refine ⟨hEq, ?_, ?_, ?_⟩
    · rw [commutator_eq_map_commV hVE hBN, ← map_fixV_autOn hVE hBN, hfc]
    · rw [← hEq, commutator_preOn_eq hVE hBT hTM hMV]
    · rw [← hEq]
      have hPN : preOn T (V154 T Mc M) (autOn B (V154 T Mc M)) ≤
          Subgroup.normalizer (V154 T Mc M : Set G) := (preOn_le T _ _).trans (hTM.trans hMV)
      rw [commutator_eq_map_commV hVE hPN, ← map_fixV_autOn hVE hPN,
        autOn_preOn (A4.autOn_mono hBT), hfc]

theorem stageLemma15214W_of_ce (h15201 : StageLemma15201) (h1515 : StageLemma1515CE)
    (h1518 : StageLemma1518) (h1519 : StageLemma1519) (h15209 : StageNotation15209)
    (h15211 : StageLemma15211) (h15212 : StageLemma15212W) (h15213 : StageLemma15213)
    (hΩ : Omega4PlusIsS3xS3) (hOm : Om4Z152) : StageLemma15214 := by
  intro G _ _ T Mc M hs B₀ hB₀
  have hqtfe := hs.qtfe
  have hMT : InM T M := hs.mf.1.1
  have hTM : T ≤ M := hMT.2
  have hMV : M ≤ Subgroup.normalizer (V154 T Mc M : Set G) := le_normalizer_V154 T Mc M
  have hVE : IsElemAbelian 2 (V154 T Mc M) := S152N.isElemAbelian_V154 hs
  obtain ⟨H, hH⟩ := exists_isHStar hqtfe.inM_mc hMT hs.mf.2.1.symm
  have c209 := h15209 G T Mc M hs H hH
  obtain ⟨B, hB⟩ := c209.sigmaPrime_nonempty
  have c211 := h15211 G T Mc M hs H hH B hB
  have c212 := h15212 G T Mc M hs H hH B hB
  have c213 := h15213 G T Mc M hs H hH
  have c1515 := h1515 G T Mc M hqtfe hs.mf hs.ce
  have c1519 := h1519 G T Mc M hqtfe hs.mf hs.ce
  have c1518 := h1518 G T Mc M hqtfe hs.mf hs.ce
  have c201 := h15201 G T Mc M hs
  obtain ⟨B₀', hB₀', huniq, hforall⟩ := c213.exists_B0
  have hBB : B₀ = B₀' := huniq B₀ hB₀
  obtain ⟨-, -, hW1, hW2⟩ := hforall B hB
  subst hBB
  have hZV : quasithinOmegaOneCenter T ≤ V154 T Mc M := by
    calc quasithinOmegaOneCenter T ≤ conjClosure (quasithinOmegaOneCenter T) M :=
          le_conjClosure _ _
      _ = VZ T M := rfl
      _ = V154 T Mc M := c212.eq_VZ.symm
  have hzS : zSOf T Mc M B₀ = V154 T Mc M ⊓ Subgroup.centralizer
      (preOn T (V154 T Mc M) B₀ : Set G) := hW2
  have hD : Data14 T Mc M B₀ :=
    { pgroup := hqtfe.sylow.1
      elemAbelian := hVE
      card_V := c201.card
      V_le_T := S152N.V154_le_T hs
      T_le_M := hTM
      M_le_normalizer := hMV
      Z_le_V := hZV
      zS_eq := hzS
      card_zS := by
        have : zSOf T Mc M B₀ = ⁅V154 T Mc M, B⁆ := hW1.symm
        rw [this]
        exact c211.card
      normal_zS := by
        have : zSOf T Mc M B₀ = ⁅V154 T Mc M, B⁆ := hW1.symm
        rw [this]
        exact c211.normal
      isB0 := hB₀
      T_le_Mc := hqtfe.t_le_mc
      sylow_bar := by
        let _ : CommGroup ↥(V154 T Mc M) := commGroupOfElemAbelian hVE
        exact B2F.isSylowTwoOf_autI hVE hMV (isSylowTwoOf_of_le151 hqtfe.sylow hTM)
      centralizer_V_le := c1515.centralizer_le
      not_M_le := fun h =>
        hs.mf.2.1 ((hMT.1.2 Mc hqtfe.mc_max.1 h).symm)
      ord := c1519.two.2 Mc hqtfe.inM_mc
      baum_eq := c1519.one_baum
      three_centralizes := by
        intro g hgMc ⟨a, ha⟩
        obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp (orderOf_dvd_of_pow_eq_one ha)
        exact c212.three_centralizes g hgMc ⟨k, hk⟩
      centralizer_Z_le := hqtfe.centralizer_le_mc
      shape := by
        rcases c213.cases with h | h
        · exact Or.inl h
        · exact Or.inr h.1.2.2
      q_eq := fun hV => qOf_eq_two_of_lemma1518 hV c1518 }
  have hinf := inf_eq14 hD hΩ hOm
  exact ⟨mc_eq14 hD hinf.1, Z_le_zS hD, cases14 hD, baum_le14 hD, zS_eq14 hD, hinf,
    params14 hD hΩ, barT14 hD hOm⟩

end He12

end CFSG.Quasithin
