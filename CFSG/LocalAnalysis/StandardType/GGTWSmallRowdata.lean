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

lemma l05nQD_row_facts {p : ℕ} {J X : LargeEvenLabel}
    (h : ggRowTwoNode p J X) (h4 : 4 ≤ X.rank) :
    (J.tag = .A ∨ J.tag = .twA) ∧ (X.tag = .A ∨ X.tag = .twA) ∧ X.rank = J.rank + 2 ∧
      p ∣ X.rank + 1 ∧ p ∣ ggTorM X := by
  rcases h with ⟨hJ, hp, hdvd, hX⟩ | ⟨hJ, hp, hdvd, hX⟩ | ⟨-, -, -, hX⟩ | ⟨-, -, -, hX⟩
  · subst hX
    refine ⟨Or.inl hJ, Or.inl rfl, rfl, ?_, ?_⟩
    · have he : (J.rank + 2) + 1 = J.rank + 3 := by omega
      rw [he]; exact hdvd
    · rw [ggTWR_ggTorM_A]; exact hp
  · subst hX
    refine ⟨Or.inr hJ, Or.inr rfl, rfl, ?_, ?_⟩
    · have he : (J.rank + 2) + 1 = J.rank + 3 := by omega
      rw [he]; exact hdvd
    · rw [ggTWR_ggTorM_twA]; exact hp
  · subst hX
    have h0 : (⟨.E6, 0, J.n⟩ : LargeEvenLabel).rank = 0 := rfl
    rw [h0] at h4; omega
  · subst hX
    have h0 : (⟨.twE6, 0, J.n⟩ : LargeEvenLabel).rank = 0 := rfl
    rw [h0] at h4; omega

lemma l05nQD_cell {r p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (h4 : 4 ≤ r) (h9 : r ≤ 9)
    (hdvd : p ∣ r + 1) :
    (p = 5 ∧ r + 1 = 5) ∨ (p = 3 ∧ r + 1 = 6) ∨ (p = 7 ∧ r + 1 = 7) ∨
      (p = 3 ∧ r + 1 = 9) ∨ (p = 5 ∧ r + 1 = 10) := by
  interval_cases r
  · exact Or.inl ⟨(Nat.prime_dvd_prime_iff_eq hp (by norm_num)).1 (by simpa using hdvd), rfl⟩
  · have hd : p ∣ 2 * 3 := by rw [show (2 : ℕ) * 3 = 6 by norm_num]; exact hdvd
    rcases (Nat.Prime.dvd_mul hp).1 hd with h | h
    · exact absurd ((Nat.prime_dvd_prime_iff_eq hp (by norm_num)).1 h) hp2
    · exact Or.inr (Or.inl ⟨(Nat.prime_dvd_prime_iff_eq hp (by norm_num)).1 h, rfl⟩)
  · exact Or.inr (Or.inr (Or.inl
      ⟨(Nat.prime_dvd_prime_iff_eq hp (by norm_num)).1 (by simpa using hdvd), rfl⟩))
  · have hpow : p ∣ 2 ^ 3 := by rw [show (2 : ℕ) ^ 3 = 8 by norm_num]; exact hdvd
    have h2dvd : p ∣ 2 := hp.dvd_of_dvd_pow hpow
    exact absurd ((Nat.prime_dvd_prime_iff_eq hp (by norm_num)).1 h2dvd) hp2
  · have hpow : p ∣ 3 ^ 2 := by rw [show (3 : ℕ) ^ 2 = 9 by norm_num]; exact hdvd
    have h3dvd : p ∣ 3 := hp.dvd_of_dvd_pow hpow
    exact Or.inr (Or.inr (Or.inr (Or.inl
      ⟨(Nat.prime_dvd_prime_iff_eq hp (by norm_num)).1 h3dvd, rfl⟩)))
  · have hd : p ∣ 2 * 5 := by rw [show (2 : ℕ) * 5 = 10 by norm_num]; exact hdvd
    rcases (Nat.Prime.dvd_mul hp).1 hd with h | h
    · exact absurd ((Nat.prime_dvd_prime_iff_eq hp (by norm_num)).1 h) hp2
    · exact Or.inr (Or.inr (Or.inr (Or.inr
        ⟨(Nat.prime_dvd_prime_iff_eq hp (by norm_num)).1 h, rfl⟩)))

private lemma l05nQD_twA_of_ennola {p : ℕ} {lab : LargeEvenLabel} (hp : p.Prime) (hp2 : p ≠ 2)
    (htag : lab.tag = .A ∨ lab.tag = .twA) (hdvdM : p ∣ ggTorM lab)
    (h : p = 3 ∧ lab.rank = 5 ∧ p ∣ 2 ^ lab.n + 1) : lab.tag = .twA := by
  rcases htag with hA | htw
  · exfalso
    have hM : ggTorM lab = 2 ^ lab.n - 1 := by
      unfold ggTorM
      rw [hA]
      rw [if_neg (by decide : ¬ ((.A : LargeEvenLieTag) = .twA ∨
        (.A : LargeEvenLieTag) = .twE6))]
    have hdiv2 : p ∣ 2 ^ lab.n - 1 := by rw [← hM]; exact hdvdM
    have h2 : p ∣ 2 := by
      have hsub := Nat.dvd_sub h.2.2 hdiv2
      have h1 : 1 ≤ 2 ^ lab.n := Nat.one_le_two_pow
      have heq : 2 ^ lab.n + 1 - (2 ^ lab.n - 1) = 2 := by omega
      rwa [heq] at hsub
    exact absurd ((Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 2)).1 h2) hp2
  · exact htw

theorem ggTWSmall_rowdata {r₀ : ℕ}
    (hr₀ : 4 ≤ r₀) (hRig : GGLabelRigidInput) (hT : GGTBTorAFrom r₀) (hLift : GGTBTorLiftAFrom r₀)
    (hW : GGTBWNormLabelInput) (hR : r₀ ≤ 5 → GGTBXDatumResInput)
    (hTw : r₀ ≤ 5 → GGTWTwA5Open) {G : Type} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G}
    {K : Subgroup G} (hH : GGResHyp p B Bs x L D J y K)
    (hrow : GGResRowAt (fun p J X => ggRowTwoNode p J X ∧ r₀ ≤ X.rank ∧ X.rank ≤ 9) p J L)
    (hxL : x ∉ L) :
    ∃ (N : ℕ) (labJ labX : LargeEvenLabel),
      ((p = 5 ∧ N = 5) ∨ (p = 3 ∧ N = 6) ∨ (p = 7 ∧ N = 7) ∨ (p = 3 ∧ N = 9) ∨
        (p = 5 ∧ N = 10)) ∧
      LargeEvenInLambda2 labJ ∧ LargeEvenInLambda2 labX ∧
      GGHasLabel labJ (↥J ⧸ Subgroup.center ↥J) ∧ GGHasLabel labX (↥L ⧸ Subgroup.center ↥L) ∧
      ggRowTwoNodeSmall p labJ labX ∧ (labX.tag = .A ∨ labX.tag = .twA) ∧
      (labJ.tag = .A ∨ labJ.tag = .twA) ∧ labX.rank + 1 = N ∧ labJ.rank + 3 = N ∧
      GGResXDatumA p Bs L (N - 1) ∧ GGTWHLAt p Bs L x := by
  obtain ⟨labJ, labX, hJΛ, hXΛ, hJl, hXl, hRow⟩ := hrow
  obtain ⟨hRow2, hlow, hhigh⟩ := hRow
  have h4X : 4 ≤ labX.rank := le_trans hr₀ hlow
  obtain ⟨htagJ, htagX, hrankJ, hdvdX, hMX⟩ := l05nQD_row_facts hRow2 h4X
  have hp2 : p ≠ 2 := hH.1.1.2.2.2.2.2.1.2.1
  have hcell : (p = 5 ∧ labX.rank + 1 = 5) ∨ (p = 3 ∧ labX.rank + 1 = 6) ∨
      (p = 7 ∧ labX.rank + 1 = 7) ∨ (p = 3 ∧ labX.rank + 1 = 9) ∨
      (p = 5 ∧ labX.rank + 1 = 10) :=
    l05nQD_cell Fact.out hp2 h4X hhigh hdvdX
  by_cases hEnn : p = 3 ∧ labX.rank = 5 ∧ p ∣ 2 ^ labX.n + 1
  ·
    have hR5 : r₀ ≤ 5 := by omega
    have htwA : labX.tag = .twA := l05nQD_twA_of_ennola Fact.out hp2 htagX hMX hEnn
    have h3 : 3 ∣ 2 ^ labX.n + 1 := hEnn.1 ▸ hEnn.2.2
    obtain ⟨hDat5, hHL5, -⟩ :=
      ggTWTwA5_datum (X := L) (z := x) hRig (hR hR5) (hTw hR5) hH
        (Or.inl ⟨rfl, rfl⟩) hEnn.1 hXΛ hXl ⟨htwA, hEnn.2.1, h3⟩
    have hHLx : GGTWHLAt p Bs L x := hHL5 ⟨rfl, rfl⟩
    have hdat : GGResXDatumA p Bs L (labX.rank + 1 - 1) := by
      rw [Nat.add_sub_cancel, hEnn.2.1]; exact hDat5
    exact ⟨labX.rank + 1, labJ, labX, hcell, hJΛ, hXΛ, hJl, hXl, ⟨hRow2, hhigh⟩, htagX, htagJ,
      rfl, by omega, hdat, hHLx⟩
  ·
    have hInner : GGInnerDiagOn Bs L := hH.2.2.1.1
    obtain ⟨hperf, lab0, hlab0, hraw0⟩ := hInner
    have hhas0 : GGHasLabel lab0 (↥L ⧸ Subgroup.center ↥L) := by
      unfold GGHasLabel
      refine largeEvenRawDatum_mono ?_ hraw0
      rintro R _ I F ⟨-, -, θ, -⟩
      exact ⟨θ⟩
    have hlab0X : lab0 = labX :=
      ggTWR_iso_eq (hRig lab0 labX _ hlab0 hXΛ hhas0 hXl) htagX h4X
    have hInnerLabel : GGInnerDiagOnLabel (GGTWRowPred r₀) p Bs L := by
      refine ⟨hperf, lab0, hlab0, ?_⟩
      refine largeEvenRawDatum_mono ?_ hraw0
      rintro R _ I F ⟨hs, hna, θ, hP0⟩
      exact ⟨hs, hna, θ, ⟨by rw [hlab0X]; exact ⟨htagX, hlow, hdvdX, hMX, hEnn⟩, hP0⟩⟩
    have hxB : x ∈ Bs := hH.1.tableB_facts.2.2.1
    obtain ⟨lab, hlabΛ, hlab, hP, hdat⟩ :=
      ggResXDatumA_compat_from hr₀ hRig hT hLift hW hH hInnerLabel hxB
    obtain ⟨Λ, iF, iD, M, C, V, iVadd, iVmod, ι, φ, hvec, α, e, hMeq, hMw, hMC, hlin, hrefl,
      hpair, hIso, hgen, S, hN, hWn, hMi, hnc, ψ, hcompat, hA⟩ := hdat
    have hiso : GGLabelIso lab labX := hRig lab labX _ hlabΛ hXΛ hlab hXl
    have hEq : lab = labX := ggTWR_iso_eq hiso htagX h4X
    subst lab
    have hdatumX : GGResXDatumA p Bs L labX.rank :=
      ⟨Λ, iF, iD, M, C, V, iVadd, iVmod, ι, φ, hvec, α, e, hMeq, hMw, hMC, hlin, hrefl,
        hpair, hIso, hgen⟩
    have hHL : GGTWHLAt p Bs L x := by
      refine ⟨hxB, ?_⟩
      intro Λ₂ iF₂ iD₂ M₂ C₂ hMw₂ hMC₂ V₂ iV₂add iV₂mod ι₂ φ₂ h₂ α₂ hlin₂ hrefl₂ hpair₂ hgen₂
        t ht htr htx
      exact ggHL_lines_of_automizer hWn hH.1 hMi hnc hN hxB φ ψ hcompat hA hgen hMw₂ hMC₂
        ι₂ φ₂ h₂ α₂ hlin₂ hrefl₂ hpair₂ hgen₂ t ht htr htx
    have hdat : GGResXDatumA p Bs L (labX.rank + 1 - 1) := by
      rw [Nat.add_sub_cancel]; exact hdatumX
    exact ⟨labX.rank + 1, labJ, labX, hcell, hJΛ, hXΛ, hJl, hXl, ⟨hRow2, hhigh⟩, htagX, htagJ,
      rfl, by omega, hdat, hHL⟩

end CFSG.StandardType

end
