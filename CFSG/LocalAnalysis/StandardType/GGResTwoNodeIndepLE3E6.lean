module

public import CFSG.LocalAnalysis.StandardType.GGResTwoNodeIndep
public import CFSG.LocalAnalysis.StandardType.GGResLeviLE3Count
public import CFSG.LocalAnalysis.StandardType.GGTwoNodeKFixLineDefs
public import CFSG.LocalAnalysis.StandardType.GGTBFixDefs
public import CFSG.LocalAnalysis.StandardType.GGTwoNodeA5Consumer

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem GGResLeviSideDatumLE3.reflGenerated {G : Type} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] {Bs X J : Subgroup G}
    (hD : GGResLeviSideDatumLE3 p Bs X J) : GGReflGenerated p (ggAutomizer X Bs) := by
  obtain ⟨Λ, iF, iD, S, M, C, MJ, V, iA, iM, ι, φ, h, α, -, -, -, -, -, -, -, hrefl,
    -, -, hcl, -, -, -⟩ := hD
  exact ggIndep_reflGenerated_of_closure hrefl hcl

theorem ggResTwoNodeIndepLE3E6_of_ten (hTen : GGResTwoNodeIndepLE3TenInput)
    (hAll : LR6A5All) (hOrb : GGResCentBoundInput) (hOrbK : GGResCentBoundNbrInput)
    (hFix : GGTBFixInput) (hFixK : GGTBFixNbrInput) (hKFix : GGTwoNodeKFixLineInput)
    (hD : GGTwoNodeIndepDatum) : GGResTwoNodeIndepLE3E6Input := by
  intro G _ _ p B Bs x L D J y K hH _ hF hS hE hP
  rcases hP with ⟨hrow, hp3, hxL, -, -, -⟩ | ⟨hrow, hp3, hyK, -, hL, -⟩ | hTenP
  · exact ggResTwoNodeIndepA5L hAll hOrb hFix hFixK hD hp3 hH hrow hxL
  · exact ggResTwoNodeIndepA5K_of_reflGenerated hAll hOrbK hFix hKFix hD hp3 hH hF hS hE
      hrow hyK hL.reflGenerated
  · exact hTen G p B Bs x L D J y K hH hF hS hE hTenP

private lemma le3e6_smallA_arith {p N : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hdvd : p ∣ N) (h4 : 4 ≤ N) (hlt : N < (if p = 3 then 9 else 10)) :
    5 ≤ N ∧ p ∣ N ∧ N ≤ 10 ∧ ¬ p ^ 2 ∣ N := by
  have hNlt10 : N < 10 := by
    by_cases hp3 : p = 3
    · rw [if_pos hp3] at hlt; omega
    · rw [if_neg hp3] at hlt; omega
  have h5 : 5 ≤ N := by
    by_contra hcon
    have hN4 : N = 4 := by omega
    have hp4 : p ∣ 4 := by rw [← hN4]; exact hdvd
    have hp_le : p ≤ 4 := Nat.le_of_dvd (by norm_num) hp4
    interval_cases p
    · norm_num at hp
    · norm_num at hp
    · exact hp2 rfl
    · norm_num at hp4
    · norm_num at hp
  refine ⟨h5, hdvd, by omega, ?_⟩
  intro h2
  have hle : p ^ 2 ≤ N := Nat.le_of_dvd (by omega) h2
  by_cases hp3 : p = 3
  · rw [if_pos hp3] at hlt
    have hp9 : p ^ 2 = 9 := by rw [hp3]; norm_num
    omega
  · rw [if_neg hp3] at hlt
    have hp_lt4 : p < 4 := by
      by_contra hcon
      have h4' : 4 ≤ p := by omega
      have h16 : 16 ≤ p ^ 2 := by nlinarith
      omega
    interval_cases p
    · norm_num at hp
    · norm_num at hp
    · exact hp2 rfl
    · exact hp3 rfl

private lemma le3e6_smallA_facts {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {labJ labX : LargeEvenLabel} (hJΛ : LargeEvenInLambda2 labJ)
    (h : ggRowTwoNodeSmallA p labJ labX) :
    5 ≤ labX.rank + 1 ∧ p ∣ labX.rank + 1 ∧ labX.rank + 1 ≤ 10 ∧
      ¬ p ^ 2 ∣ labX.rank + 1 := by
  obtain ⟨⟨hr, hsmall⟩, htag⟩ := h
  rcases hr with ⟨hJtag, -, hN, hX⟩ | ⟨hJtag, -, hN, hX⟩ | ⟨-, -, -, hX⟩ | ⟨-, -, -, hX⟩
  · have hJrank : 1 ≤ labJ.rank := by
      have h := hJΛ.2; rw [hJtag] at h; exact h.1
    have hXrank : labX.rank = labJ.rank + 2 := by rw [hX]
    have hdvd : p ∣ labX.rank + 1 := by rw [hXrank]; simpa [Nat.add_assoc] using hN
    have h4 : 4 ≤ labX.rank + 1 := by omega
    have hlt : labX.rank + 1 < (if p = 3 then 9 else 10) := by
      by_cases hp3 : p = 3
      · rw [if_pos hp3] at hsmall ⊢; omega
      · rw [if_neg hp3] at hsmall ⊢; omega
    exact le3e6_smallA_arith hp hp2 hdvd h4 hlt
  · have hJrank : 1 ≤ labJ.rank := by
      have h := hJΛ.2; rw [hJtag] at h; omega
    have hXrank : labX.rank = labJ.rank + 2 := by rw [hX]
    have hdvd : p ∣ labX.rank + 1 := by rw [hXrank]; simpa [Nat.add_assoc] using hN
    have h4 : 4 ≤ labX.rank + 1 := by omega
    have hlt : labX.rank + 1 < (if p = 3 then 9 else 10) := by
      by_cases hp3 : p = 3
      · rw [if_pos hp3] at hsmall ⊢; omega
      · rw [if_neg hp3] at hsmall ⊢; omega
    exact le3e6_smallA_arith hp hp2 hdvd h4 hlt
  · exfalso
    have hE : labX.tag = .E6 := by rw [hX]
    rcases htag with h | h <;> rw [hE] at h <;> exact absurd h (by decide)
  · exfalso
    have hE : labX.tag = .twE6 := by rw [hX]
    rcases htag with h | h <;> rw [hE] at h <;> exact absurd h (by decide)

private lemma le3e6_nine_tag {p : ℕ} {labJ labX : LargeEvenLabel}
    (hr : ggRowTwoNode p labJ labX) (h8 : labX.rank = 8) :
    labX.tag = .A ∨ labX.tag = .twA := by
  rcases hr with ⟨-, -, -, hX⟩ | ⟨-, -, -, hX⟩ | ⟨-, -, -, hX⟩ | ⟨-, -, -, hX⟩
  · exact Or.inl (by rw [hX])
  · exact Or.inr (by rw [hX])
  · exfalso
    have : labX.rank = 0 := by rw [hX]
    omega
  · exfalso
    have : labX.rank = 0 := by rw [hX]
    omega

private theorem le3e6_xdatum_of_A {G : Type} [Group G] [Finite G] {p n : ℕ} [Fact p.Prime]
    {Bs X : Subgroup G} (h : GGResXDatumA p Bs X n) : GGResXDatum p Bs X := by
  obtain ⟨Λ, i1, i2, M, C, V, i3, i4, ι, φ, h, α, e, hM, hW, hC, hlin, hrefl, hpair, hf, hcl⟩ := h
  exact ⟨Λ, i1, i2, M, C, V, i3, i4, ι, φ, h, α, hW, hC, hlin, hrefl, hpair, hf, hcl⟩

private theorem le3e6_xdatumA {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hD : GGTwoNodeIndepDatum) (hH : GGResHyp p B Bs x L D J y K)
    (X : Subgroup G) (z : G) (hXz : (X = L ∧ z = x) ∨ (X = K ∧ z = y)) (hz : z ∈ X)
    {labJ labX : LargeEvenLabel} (hJΛ : LargeEvenInLambda2 labJ) (hXΛ : LargeEvenInLambda2 labX)
    (hJl : GGHasLabel labJ (↥J ⧸ Subgroup.center ↥J))
    (hXl : GGHasLabel labX (↥X ⧸ Subgroup.center ↥X))
    (hr : ggRowTwoNode p labJ labX) (htag : labX.tag = .A ∨ labX.tag = .twA) :
    GGResXDatumA p Bs X labX.rank := by
  rcases (hD G p B Bs x L D J y K hH X z hXz labJ labX hJΛ hXΛ hJl hXl hr hz)
    with ⟨-, hA⟩ | ⟨hE, -⟩
  · rcases hA with hAx | ⟨-, hXA⟩
    · obtain ⟨Λ, iF, iD, M, C, V, iAC, iM, ι, φ, h, α, e, hMeq, hW, hC, hφ, hrefl, hpair,
        hf, hAL, -⟩ := hAx
      exact ⟨Λ, iF, iD, M, C, V, iAC, iM, ι, φ, h, α, e, hMeq, hW, hC, hφ, hrefl, hpair,
        hf, hAL⟩
    · exact hXA
  · exfalso
    rcases hE with h | h <;> rcases htag with h' | h' <;>
      exact absurd (h.symm.trans h') (by decide)

private theorem le3e6_xdatumAIndep_K {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hD : GGTwoNodeIndepDatum) (hH : GGResHyp p B Bs x L D J y K)
    {labJ labX : LargeEvenLabel} (hJΛ : LargeEvenInLambda2 labJ) (hXΛ : LargeEvenInLambda2 labX)
    (hJl : GGHasLabel labJ (↥J ⧸ Subgroup.center ↥J))
    (hXl : GGHasLabel labX (↥K ⧸ Subgroup.center ↥K))
    (hr : ggRowTwoNode p labJ labX) (hyK : y ∈ K)
    (hsmall : ggRowTwoNodeSmallA p labJ labX) (htag : labX.tag = .A ∨ labX.tag = .twA) :
    GGResXDatumAIndep p Bs K labX.rank := by
  have hp2 : p ≠ 2 := hH.1.1.2.2.2.2.2.1.2.1
  rcases (hD G p B Bs x L D J y K hH K y (Or.inr ⟨rfl, rfl⟩) labJ labX hJΛ hXΛ hJl hXl hr hyK)
    with ⟨-, hA⟩ | ⟨hE, -⟩
  · rcases hA with hAx | ⟨hpg, hXA⟩
    · obtain ⟨Λ, iF, iD, M, C, V, iAC, iM, ι, φ, h, α, e, hMeq, hW, hC, hφ, hrefl, hpair,
        hf, hAL, hind⟩ := hAx
      exact ⟨Λ, iF, iD, M, C, V, iAC, iM, ι, φ, h, α, e, hMeq, hW, hC, hφ, hrefl, hpair,
        hf, hAL, hind hyK⟩
    · exfalso
      have h1 : p ^ 2 ∣ labX.rank + 1 := dvd_trans hpg (Nat.gcd_dvd_left _ _)
      exact (le3e6_smallA_facts (Fact.out) hp2 hJΛ hsmall).2.2.2 h1
  · exfalso
    rcases hE with h | h <;> rcases htag with h' | h' <;>
      exact absurd (h.symm.trans h') (by decide)

theorem ggResTwoNodeIndepLE3Rest_of_E6 (hE6 : GGResTwoNodeIndepLE3E6Input)
    (hTwo : GGResTwoNodeIndepSmallTwoInput) (hTwoNine : GGResTwoNodeNineDepTwoInput)
    (hFix : GGTBFixInput) (hKFix : GGTwoNodeKFixLineInput) (hD : GGTwoNodeIndepDatum)
    (hJ2 : GGTBJTwoNodeInput) : GGResTwoNodeIndepLE3RestInput := by
  intro G _ _ p B Bs x L D J y K hH _ hF hS hE hP
  have hp2 : p ≠ 2 := hH.1.1.2.2.2.2.2.1.2.1
  have hBs : IsElemAbelian p Bs := hH.1.tableB_facts.2.1
  have hxBs : x ∈ Bs := hH.1.tableB_facts.2.2.1
  have hLx : L ≤ Subgroup.centralizer ({x} : Set G) := hH.1.tableB_facts.2.2.2.1
  have hx1 : x ≠ 1 := by
    intro h1
    have h := hH.1.orderOf_x
    rw [h1, orderOf_one] at h
    exact (Fact.out : p.Prime).one_lt.ne' h.symm
  have hxp : x ^ p = 1 := hBs.2 x hxBs
  have hyD : y ∈ D := by
    rw [hH.2.2.2.2.1.2.1]
    exact Subgroup.subset_closure (by simp)
  have hyBs : y ∈ Bs := hH.1.2.1.1 (hH.1.2.2.1.1 hyD)
  have hKy : K ≤ Subgroup.centralizer ({y} : Set G) := hH.2.2.2.2.1.1.2.2.2.1
  have hy1 : y ≠ 1 := ggRC_y_ne_one hH
  have hyp : y ^ p = 1 := hBs.2 y hyBs
  have hfixL := hFix G p B Bs x L D J hH.1 hH.2.1 hH.2.2.1 hH.2.2.2.1 y K
    hH.2.2.2.2.1 hH.2.2.2.2.2.1 hH.2.2.2.2.2.2
  have hfixx := ggRC_automizer_fixes_y hxBs hLx
  have hfixy := ggRC_automizer_fixes_y hyBs hKy
  rcases hP with hP1 | hP2 | hP3 | hP4
  · obtain ⟨hrowL, hxL, hK3⟩ := hP1
    have hrowL0 := hrowL
    obtain ⟨labJ, labX, hJΛ, hXΛ, hJlab, hXlab, hr⟩ := hrowL
    obtain ⟨hN5, hpN, hN10, -⟩ := le3e6_smallA_facts (Fact.out) hp2 hJΛ hr
    have hrow2 : GGResRowAt ggRowTwoNode p J L :=
      ⟨labJ, labX, hJΛ, hXΛ, hJlab, hXlab, hr.1.1⟩
    have hXdA : GGResXDatumA p Bs L labX.rank :=
      le3e6_xdatumA hD hH L x (Or.inl ⟨rfl, rfl⟩) hxL hJΛ hXΛ hJlab hXlab hr.1.1 hr.2
    by_cases hK2 : GGResTwoNodeSideDatum p Bs K J
    · exact hTwo G p B Bs x L D J y K hH hF hS hE (Or.inr (Or.inr (Or.inl ⟨hrowL0, hxL, hK2⟩)))
    · have hXs : GGResTwoNodeSideDatum p Bs L J :=
        (hJ2 G p B Bs x L D J y K hH).1 (le3e6_xdatum_of_A hXdA) hrow2
      have hle : Nat.card Bs ≤ p ^ (labX.rank + 1) :=
        ggLE3_card_le_of_fix (N := labX.rank + 1) (by omega)
          (by simpa [Nat.add_sub_cancel] using hXdA) hxp hfixL
      have h3card := ggLE3_three_card hp2 hBs hN5 hpN
        (by simpa [Nat.add_sub_cancel] using hXdA) hXs hK3 hK2 hyBs hy1 hfixy
      rcases h3card with ⟨hp3, -, hcard⟩ | hbound
      · refine hE6 G p B Bs x L D J y K hH hF hS hE ?_
        exact Or.inl ⟨hrowL0, hp3, hxL, hcard, hK3, hK2⟩
      · exfalso
        have hlt : p ^ (labX.rank + 1) < p ^ (labX.rank + 1 + 1) :=
          Nat.pow_lt_pow_right (Fact.out : p.Prime).one_lt (by omega)
        omega
  · obtain ⟨hrowK, hyK, hL3⟩ := hP2
    have hrowK0 := hrowK
    obtain ⟨labJ, labX, hJΛ, hXΛ, hJlab, hXlab, hr⟩ := hrowK
    obtain ⟨hN5, hpN, hN10, -⟩ := le3e6_smallA_facts (Fact.out) hp2 hJΛ hr
    have hrow2 : GGResRowAt ggRowTwoNode p J K :=
      ⟨labJ, labX, hJΛ, hXΛ, hJlab, hXlab, hr.1.1⟩
    have hXdK : GGResXDatumA p Bs K labX.rank :=
      le3e6_xdatumA hD hH K y (Or.inr ⟨rfl, rfl⟩) hyK hJΛ hXΛ hJlab hXlab hr.1.1 hr.2
    by_cases hL2 : GGResTwoNodeSideDatum p Bs L J
    · exact hTwo G p B Bs x L D J y K hH hF hS hE (Or.inr (Or.inr (Or.inr ⟨hrowK0, hyK, hL2⟩)))
    · have hXs : GGResTwoNodeSideDatum p Bs K J :=
        (hJ2 G p B Bs x L D J y K hH).2 (le3e6_xdatum_of_A hXdK) hrow2
      have hXI : GGResXDatumAIndep p Bs K labX.rank :=
        le3e6_xdatumAIndep_K hD hH hJΛ hXΛ hJlab hXlab hr.1.1 hyK hr hr.2
      have hrowN : GGResRowAt (fun p labJ labK => ggRowTwoNode p labJ labK ∧
          labK.rank + 1 = labX.rank + 1) p J K :=
        ⟨labJ, labX, hJΛ, hXΛ, hJlab, hXlab, ⟨hr.1.1, rfl⟩⟩
      have hstrong : ∀ b : ↥Bs, (∀ ψ ∈ ggAutomizer K Bs, ψ b = b) → (b : G) ∈ Subgroup.zpowers y :=
        fun b hb => (hKFix G p B Bs x L D J y K (labX.rank + 1) hH hF hS hE hrowN hp2
          hN5 hN10 hpN hyK hXI b).mp hb
      have hle : Nat.card Bs ≤ p ^ (labX.rank + 1) :=
        ggLE3_card_le_of_fix (N := labX.rank + 1) (by omega)
          (by simpa [Nat.add_sub_cancel] using hXdK) hyp hstrong
      have h3card := ggLE3_three_card hp2 hBs hN5 hpN
        (by simpa [Nat.add_sub_cancel] using hXdK) hXs hL3 hL2 hxBs hx1 hfixx
      rcases h3card with ⟨hp3, -, hcard⟩ | hbound
      · refine hE6 G p B Bs x L D J y K hH hF hS hE ?_
        exact Or.inr (Or.inl ⟨hrowK0, hp3, hyK, hcard, hL3, hL2⟩)
      · exfalso
        have hlt : p ^ (labX.rank + 1) < p ^ (labX.rank + 1 + 1) :=
          Nat.pow_lt_pow_right (Fact.out : p.Prime).one_lt (by omega)
        omega
  · obtain ⟨hrowL9, hxL9, hncL, hK3n⟩ := hP3
    have hrowL90 := hrowL9
    obtain ⟨labJ, labX, hJΛ, hXΛ, hJlab, hXlab, hr⟩ := hrowL9
    obtain ⟨hrNN, hp3, hrank8⟩ := hr
    have htag : labX.tag = .A ∨ labX.tag = .twA := le3e6_nine_tag hrNN hrank8
    have hrow2 : GGResRowAt ggRowTwoNode p J L :=
      ⟨labJ, labX, hJΛ, hXΛ, hJlab, hXlab, hrNN⟩
    have hXdA : GGResXDatumA p Bs L labX.rank :=
      le3e6_xdatumA hD hH L x (Or.inl ⟨rfl, rfl⟩) hxL9 hJΛ hXΛ hJlab hXlab hrNN htag
    by_cases hK2 : GGResTwoNodeSideDatum p Bs K J
    · exact hTwoNine G p B Bs x L D J y K hH hF hS hE (Or.inl ⟨hrowL90, hxL9, hncL, hK2⟩)
    · exfalso
      have hN : labX.rank + 1 = 9 := by omega
      have hN5 : 5 ≤ labX.rank + 1 := by omega
      have hpN : p ∣ labX.rank + 1 := by rw [hN, hp3]; norm_num
      have hXs : GGResTwoNodeSideDatum p Bs L J :=
        (hJ2 G p B Bs x L D J y K hH).1 (le3e6_xdatum_of_A hXdA) hrow2
      have hle : Nat.card Bs ≤ p ^ (labX.rank + 1) :=
        ggLE3_card_le_of_fix (N := labX.rank + 1) (by omega)
          (by simpa [Nat.add_sub_cancel] using hXdA) hxp hfixL
      have h3card := ggLE3_three_card hp2 hBs hN5 hpN
        (by simpa [Nat.add_sub_cancel] using hXdA) hXs hK3n hK2 hyBs hy1 hfixy
      rcases h3card with ⟨-, hN6, -⟩ | hbound
      · omega
      · have hlt : p ^ (labX.rank + 1) < p ^ (labX.rank + 1 + 1) :=
          Nat.pow_lt_pow_right (Fact.out : p.Prime).one_lt (by omega)
        omega
  · obtain ⟨hrowK9, hyK9, hncK, hL3n⟩ := hP4
    have hrowK90 := hrowK9
    obtain ⟨labJ, labX, hJΛ, hXΛ, hJlab, hXlab, hr⟩ := hrowK9
    obtain ⟨hrNN, hp3, hrank8⟩ := hr
    have htag : labX.tag = .A ∨ labX.tag = .twA := le3e6_nine_tag hrNN hrank8
    have hrow2 : GGResRowAt ggRowTwoNode p J K :=
      ⟨labJ, labX, hJΛ, hXΛ, hJlab, hXlab, hrNN⟩
    have hXdK : GGResXDatumA p Bs K labX.rank :=
      le3e6_xdatumA hD hH K y (Or.inr ⟨rfl, rfl⟩) hyK9 hJΛ hXΛ hJlab hXlab hrNN htag
    by_cases hL2 : GGResTwoNodeSideDatum p Bs L J
    · exact hTwoNine G p B Bs x L D J y K hH hF hS hE (Or.inr ⟨hrowK90, hyK9, hncK, hL2⟩)
    · have hN : labX.rank + 1 = 9 := by omega
      have hN5 : 5 ≤ labX.rank + 1 := by omega
      have hpN : p ∣ labX.rank + 1 := by rw [hN, hp3]; norm_num
      have hXs : GGResTwoNodeSideDatum p Bs K J :=
        (hJ2 G p B Bs x L D J y K hH).2 (le3e6_xdatum_of_A hXdK) hrow2
      have h3card := ggLE3_three_card_fixY hp2 hBs hN5 hpN
        (by simpa [Nat.add_sub_cancel] using hXdK) hXs hL3n hL2 hxBs hx1 hxp hfixx hfixL
      rcases h3card with ⟨-, hN6, -⟩ | hcard
      · omega
      · refine hE6 G p B Bs x L D J y K hH hF hS hE ?_
        refine Or.inr (Or.inr ⟨hrowK90, hyK9, hncK, ?_, hL3n, hL2⟩)
        rw [hcard, hp3, hN]

end CFSG.StandardType

end
