module

public import CFSG.LocalAnalysis.StandardType.GGTwoNodeDepAssembly
public import CFSG.LocalAnalysis.StandardType.GGTWRowData
public import CFSG.LocalAnalysis.StandardType.GGTWRowDataL
public import CFSG.LocalAnalysis.StandardType.GGResXDatumAHLK
public import CFSG.LocalAnalysis.StandardType.GGHLNbrInput
public import CFSG.LocalAnalysis.StandardType.GGTWRowGenDefs
public import CFSG.LocalAnalysis.StandardType.GGResXDatumARankFrom
public import CFSG.LocalAnalysis.StandardType.GGResXDatumAHLFrom
public import CFSG.LocalAnalysis.StandardType.GGTWTwA5Defs
public import CFSG.LocalAnalysis.StandardType.GGTWTwA5Datum

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private theorem l05nQK_iso_eq_of_tag {lab lab' : LargeEvenLabel} (hiso : GGLabelIso lab lab')
    (hlab : lab.tag = .A ∨ lab.tag = .twA) (hlab' : lab'.tag = .A ∨ lab'.tag = .twA) :
    lab = lab' := by
  rcases hiso with h | ⟨h1, -, -, -⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ |
    ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact h
  · rcases hlab with ht | ht <;> rw [ht] at h1 <;> exact absurd h1 (by decide)
  · have htD : lab.tag = .D := by rw [h1]
    rcases hlab with ht | ht <;> rw [htD] at ht <;> exact absurd ht (by decide)
  · have htD : lab'.tag = .D := by rw [h2]
    rcases hlab' with ht | ht <;> rw [htD] at ht <;> exact absurd ht (by decide)
  · have htD : lab.tag = .twD := by rw [h1]
    rcases hlab with ht | ht <;> rw [htD] at ht <;> exact absurd ht (by decide)
  · have htD : lab'.tag = .twD := by rw [h2]
    rcases hlab' with ht | ht <;> rw [htD] at ht <;> exact absurd ht (by decide)
  · have htD : lab.tag = .twD := by rw [h1]
    rcases hlab with ht | ht <;> rw [htD] at ht <;> exact absurd ht (by decide)
  · have htD : lab'.tag = .twD := by rw [h1]
    rcases hlab' with ht | ht <;> rw [htD] at ht <;> exact absurd ht (by decide)

private lemma l05nQK_not_dvd_enn {p n : ℕ} (h1 : p ∣ 2 ^ n - 1) :
    ¬ (p = 3 ∧ p ∣ 2 ^ n + 1) := by
  rintro ⟨hp3, h2⟩
  have hsub : p ∣ (2 ^ n + 1) - (2 ^ n - 1) := Nat.dvd_sub h2 h1
  have h2eq : (2 ^ n + 1) - (2 ^ n - 1) = 2 := by
    have hA : 0 < 2 ^ n := by positivity
    omega
  rw [h2eq] at hsub
  rw [hp3] at hsub
  exact absurd hsub (by decide)

theorem l05nQK_innerDiagOnLabel_K (hRig : GGLabelRigidInput) {G : Type} [Group G]
    [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G}
    {K : Subgroup G} (hH : GGResHyp p B Bs x L D J y K) {r₀ : ℕ} {labX : LargeEvenLabel}
    (hXΛ : LargeEvenInLambda2 labX) (hXlab : GGHasLabel labX (↥K ⧸ Subgroup.center ↥K))
    (hPred : GGTWRowPred r₀ p labX) (h4 : 4 ≤ labX.rank) :
    GGInnerDiagOnLabel (GGTWRowPred r₀) p Bs K := by
  obtain ⟨hcomm, labK, hlabK, hraw⟩ :=
    (hH.2.2.1.2 y K hH.2.2.2.2.1 : GGInnerDiagOn Bs K)
  have hlabKHas : GGHasLabel labK (↥K ⧸ Subgroup.center ↥K) := by
    refine largeEvenRawDatum_mono ?_ hraw
    rintro R _ I F ⟨hs, hna, θ, hP⟩
    exact ⟨θ⟩
  have hiso : GGLabelIso labX labK :=
    hRig labX labK (↥K ⧸ Subgroup.center ↥K) hXΛ hlabK hXlab hlabKHas
  have hEq : labX = labK := ggTWR_iso_eq_fst' hiso hPred.1 h4
  refine ⟨hcomm, labK, hlabK, ?_⟩
  refine largeEvenRawDatum_mono ?_ hraw
  rintro R _ I F ⟨hs, hna, θ, hP⟩
  refine ⟨hs, hna, θ, ?_, hP⟩
  rw [← hEq]
  exact hPred

private theorem l05nQK_datum_of_pred {r₀ : ℕ} (hr₀ : 4 ≤ r₀) (hT : GGTBTorAFrom r₀)
    (hLift : GGTBTorLiftAFrom r₀) (hRig : GGLabelRigidInput)
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {y : G} {K : Subgroup G} (hH : GGResHyp p B Bs x L D J y K)
    {N : ℕ} {labK : LargeEvenLabel} (hKΛ : LargeEvenInLambda2 labK)
    (hKl : GGHasLabel labK (↥K ⧸ Subgroup.center ↥K))
    (hPred : GGTWRowPred r₀ p labK) (h4 : 4 ≤ labK.rank) (hKrank : labK.rank = N - 1) :
    GGResXDatumA p Bs K (N - 1) := by
  have hInner := l05nQK_innerDiagOnLabel_K hRig hH hKΛ hKl hPred h4
  obtain ⟨lab, hlabΛ, hlabHas, hlabPred, hdatumLab⟩ :=
    ggResXDatumA_of_tbTor_from_K hr₀ hT hLift hH hInner
  have hiso : GGLabelIso lab labK := hRig lab labK _ hlabΛ hKΛ hlabHas hKl
  have hEq : lab = labK := ggTWR_iso_eq hiso hPred.1 h4
  rw [hEq] at hdatumLab
  rw [hKrank] at hdatumLab
  exact hdatumLab

theorem ggTWSmall_rowdata_K
    {r₀ : ℕ} (hr₀ : 4 ≤ r₀) (hRig : GGLabelRigidInput)
    (hT : GGTBTorAFrom r₀) (hLift : GGTBTorLiftAFrom r₀) (hR : r₀ ≤ 5 → GGTBXDatumResInput)
    (hTw : r₀ ≤ 5 → GGTWTwA5Open)
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {y : G} {K : Subgroup G} (hH : GGResHyp p B Bs x L D J y K) {N : ℕ}
    (hN : N = 5 ∨ N = 6 ∨ N = 7 ∨ N = 9 ∨ N = 10) (hrN : r₀ + 1 ≤ N)
    {labJ : LargeEvenLabel} (hJΛ : LargeEvenInLambda2 labJ)
    (hJl : GGHasLabel labJ (↥J ⧸ Subgroup.center ↥J)) (hJtag : labJ.tag = .A ∨ labJ.tag = .twA)
    (hJr : labJ.rank + 3 = N) (hrowK : GGResRowAt ggRowTwoNode p J K) :
    GGResXDatumA p Bs K (N - 1) := by
  obtain ⟨labJ', labK, hJ'Λ, hKΛ, hJ'l, hKl, hRowK⟩ := hrowK
  have hisoJ : GGLabelIso labJ' labJ := hRig labJ' labJ _ hJ'Λ hJΛ hJ'l hJl
  rcases hRowK with hAc | htwAc | hD4c | htwD4c
  · obtain ⟨hJtagA, hqdvd, hrdvd, hXeq⟩ := hAc
    subst hXeq
    have hEqJ : labJ' = labJ := l05nQK_iso_eq_of_tag hisoJ (Or.inl hJtagA) hJtag
    have hKtag : (⟨.A, labJ'.rank + 2, labJ'.n⟩ : LargeEvenLabel).tag = .A ∨
        (⟨.A, labJ'.rank + 2, labJ'.n⟩ : LargeEvenLabel).tag = .twA := Or.inl rfl
    have hKrank : (⟨.A, labJ'.rank + 2, labJ'.n⟩ : LargeEvenLabel).rank = N - 1 := by
      change labJ'.rank + 2 = N - 1
      rw [hEqJ]; omega
    have hdvdK : p ∣ (⟨.A, labJ'.rank + 2, labJ'.n⟩ : LargeEvenLabel).rank + 1 := by
      simpa using hrdvd
    have hMXK : p ∣ ggTorM (⟨.A, labJ'.rank + 2, labJ'.n⟩ : LargeEvenLabel) := by
      rw [ggTWR_ggTorM_A]; exact hqdvd
    have h4K : 4 ≤ (⟨.A, labJ'.rank + 2, labJ'.n⟩ : LargeEvenLabel).rank := by
      rw [hKrank]; omega
    have hnotEnn : ¬ (p = 3 ∧ (⟨.A, labJ'.rank + 2, labJ'.n⟩ : LargeEvenLabel).rank = 5 ∧
        p ∣ 2 ^ (⟨.A, labJ'.rank + 2, labJ'.n⟩ : LargeEvenLabel).n + 1) := by
      rintro ⟨hp3, -, hdiv⟩
      exact l05nQK_not_dvd_enn hqdvd ⟨hp3, hdiv⟩
    have hPred : GGTWRowPred r₀ p (⟨.A, labJ'.rank + 2, labJ'.n⟩ : LargeEvenLabel) :=
      ⟨hKtag, by rw [hKrank]; omega, hdvdK, hMXK, hnotEnn⟩
    exact l05nQK_datum_of_pred hr₀ hT hLift hRig hH hKΛ hKl hPred h4K hKrank
  · obtain ⟨hJtagT, hqdvd, hrdvd, hXeq⟩ := htwAc
    subst hXeq
    have hEqJ : labJ' = labJ := l05nQK_iso_eq_of_tag hisoJ (Or.inr hJtagT) hJtag
    have hKtag : (⟨.twA, labJ'.rank + 2, labJ'.n⟩ : LargeEvenLabel).tag = .A ∨
        (⟨.twA, labJ'.rank + 2, labJ'.n⟩ : LargeEvenLabel).tag = .twA := Or.inr rfl
    have hKrank : (⟨.twA, labJ'.rank + 2, labJ'.n⟩ : LargeEvenLabel).rank = N - 1 := by
      change labJ'.rank + 2 = N - 1
      rw [hEqJ]; omega
    have hdvdK : p ∣ (⟨.twA, labJ'.rank + 2, labJ'.n⟩ : LargeEvenLabel).rank + 1 := by
      simpa using hrdvd
    have hMXK : p ∣ ggTorM (⟨.twA, labJ'.rank + 2, labJ'.n⟩ : LargeEvenLabel) := by
      rw [ggTWR_ggTorM_twA]; exact hqdvd
    have h4K : 4 ≤ (⟨.twA, labJ'.rank + 2, labJ'.n⟩ : LargeEvenLabel).rank := by
      rw [hKrank]; omega
    by_cases hEnn : p = 3 ∧ (⟨.twA, labJ'.rank + 2, labJ'.n⟩ : LargeEvenLabel).rank = 5 ∧
        p ∣ 2 ^ (⟨.twA, labJ'.rank + 2, labJ'.n⟩ : LargeEvenLabel).n + 1
    · have hR5 : GGTBXDatumResInput := hR (by omega)
      have hTw5 : GGTWTwA5Open := hTw (by omega)
      have htw : (⟨.twA, labJ'.rank + 2, labJ'.n⟩ : LargeEvenLabel).tag = .twA ∧
          (⟨.twA, labJ'.rank + 2, labJ'.n⟩ : LargeEvenLabel).rank = 5 ∧
          3 ∣ 2 ^ (⟨.twA, labJ'.rank + 2, labJ'.n⟩ : LargeEvenLabel).n + 1 :=
        ⟨rfl, hEnn.2.1, by simpa [hEnn.1] using hEnn.2.2⟩
      have hd := (ggTWTwA5_datum hRig hR5 hTw5 hH (X := K) (z := y) (Or.inr ⟨rfl, rfl⟩)
        hEnn.1 hKΛ hKl htw).1
      have hN1 : N - 1 = 5 := by omega
      rw [hN1]; exact hd
    · have hPred : GGTWRowPred r₀ p (⟨.twA, labJ'.rank + 2, labJ'.n⟩ : LargeEvenLabel) :=
        ⟨hKtag, by rw [hKrank]; omega, hdvdK, hMXK, hEnn⟩
      exact l05nQK_datum_of_pred hr₀ hT hLift hRig hH hKΛ hKl hPred h4K hKrank
  · obtain ⟨hJrow, -, -, -⟩ := hD4c
    have hEqJ : labJ' = labJ := ggTWR_iso_eq_D4 hisoJ hJrow
    have htagD : labJ.tag = .D := by
      rw [← hEqJ]
      simpa using congrArg LargeEvenLabel.tag hJrow
    rcases hJtag with hA | hA
    · rw [htagD] at hA; exact absurd hA (by decide)
    · rw [htagD] at hA; exact absurd hA (by decide)
  · obtain ⟨hJrow, -, -, -⟩ := htwD4c
    have hEqJ : labJ' = labJ := ggTWR_iso_eq_D4 hisoJ hJrow
    have htagD : labJ.tag = .D := by
      rw [← hEqJ]
      simpa using congrArg LargeEvenLabel.tag hJrow
    rcases hJtag with hA | hA
    · rw [htagD] at hA; exact absurd hA (by decide)
    · rw [htagD] at hA; exact absurd hA (by decide)

end CFSG.StandardType

end
