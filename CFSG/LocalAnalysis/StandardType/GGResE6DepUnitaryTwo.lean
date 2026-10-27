module

public import CFSG.LocalAnalysis.StandardType.GGResE6DepUnitary
public import CFSG.LocalAnalysis.StandardType.GGUSixTwoSetup
public import CFSG.LocalAnalysis.StandardType.GGUSixTwoDescent
public import CFSG.LocalAnalysis.StandardType.GGF4AutWeyl
public import CFSG.LocalAnalysis.StandardType.GGCoxeterFaithfulTypeA
public import CFSG.LocalAnalysis.StandardType.GGNbrCenterPCyclicHolds
public import CFSG.LocalAnalysis.StandardType.GGUSixThreeWeylHolds
public import CFSG.LocalAnalysis.StandardType.GGTableBUnit63Main

public section

namespace CFSG.StandardType

open CFSG.Assembly
open CFSG.StandardType.USixTwo

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem psu6_two_inner_card
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = (2 ^ 1) ^ 2)
    {L' : Type} [Group L'] [Finite L'] {ψ : L' →* UnitaryR K 1 6}
    (hψ : Function.Surjective ψ) (hker : ψ.ker ≤ Subgroup.center L')
    (hperf : commutator L' = ⊤) {A : Subgroup (MulAut L')}
    (hA : CFSG.Open.IsElemAbelian 3 A)
    (hAI : ∀ a ∈ A, ∃ x ∈ UnitaryI K 1 6, ∀ l : L', x (ψ l) = ψ (a l))
    (hcard : 3 ^ 4 ≤ Nat.card A) (hsc : GGTorusSelfCent 3 A) :
    Nat.card ↥(ggAutomizer (MulAut.conj : L' →* MulAut L').range A) = 720 := by
  have hA3 : IsPGroup 3 A := CFSG.StandardType.Line63.H5.isPGroup_three_of_isElemAbelian hA
  obtain ⟨ψb, hψbmk, hψbs, hkerb, hperfb, hoddb, hAb, hcardAb, hAIb⟩ :=
    six_package hK hψ hker hperf hA hAI
  let Ab : Subgroup (MulAut (Qt L')) := A.map (qAutHom L')
  have hcardAb' : Nat.card Ab = Nat.card A := hcardAb
  obtain ⟨φ, hM, hdiag⟩ := exists_diagModel_odd hK hψbs hkerb hperfb hoddb hAb hAIb
    (by rw [hcardAb']; exact hcard)
  have hscAb : GGTorusSelfCent 3 Ab := ggTorusSelfCent_descent hA3 hsc
  have hTor : GGTorusTorData (2 ^ 1 + 1) 5 (CartanMatrix.A 5) (CoxeterMatrix.A 5)
      (Qt L') Ab :=
    ggTorusTorData_of_model_U hK Nat.prime_three (by norm_num) (by norm_num)
      (by norm_num : 3 ≤ 5) hM hAb hscAb hdiag
  obtain ⟨w, hw⟩ := hTor
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, he⟩ := hw
  obtain ⟨e, he⟩ := he
  have hInnerAb : Nat.card ↥(ggAutomizer
      (MulAut.conj : Qt L' →* MulAut (Qt L')).range Ab) = 720 := by
    rw [← Nat.card_congr e.toEquiv, l05nK3a_card_coxeterA 5]
    norm_num
  let H : Subgroup (MulAut L') := (MulAut.conj : L' →* MulAut L').range
  let Hb : Subgroup (MulAut (Qt L')) :=
    (MulAut.conj : Qt L' →* MulAut (Qt L')).range
  have hHmap : H.map (qAutHom L') = Hb := by
    ext x
    constructor
    · rintro ⟨h, hh, rfl⟩
      obtain ⟨l, rfl⟩ := hh
      exact ⟨qmk L' l, by rw [qAutHom_conj]⟩
    · rintro ⟨q, hq⟩
      obtain ⟨l, rfl⟩ := qmk_surjective q
      exact ⟨MulAut.conj l, ⟨l, rfl⟩, by rw [qAutHom_conj, hq]⟩
  have hmap := F4AutWeyl.ggAutomizer_map_eq (f := qAutHom L')
    (qAutHom_injective hperf) H A (by rfl)
  rw [hHmap] at hmap
  rw [hmap] at hInnerAb
  rw [Subgroup.card_map_of_injective (MulAut.congr _).injective] at hInnerAb
  simpa [H, Hb, Ab] using hInnerAb

theorem original_unitSix_card720
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K)
    (hp : p = 3)
    (hMark : GGInnerDiagOnLabel (fun _ lab => lab = ⟨.twA, 5, 1⟩) p Bs L) :
    Nat.card ↥(ggAutomizer L Bs) = 720 := by
  subst hp
  have hM63 : GGInnerDiagOnLab GGUnitDvd63Label 3 Bs L := by
    refine largeEvenMarking_mono (fun lab R _ I F θ hP => ⟨?_, ?_, hP.2.1, hP.2.2⟩) hMark
    · rw [hP.1]
      norm_num [GGUnitDvd63Label, GGUnitDvdLabel]
    · rw [hP.1]
      exact Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩))
  obtain ⟨hperfL, lab, hlab, hraw⟩ := hMark
  obtain ⟨-, -, -, -, -, -, -, hEq, -, -⟩ := largeEvenRawDatum_exists hraw
  subst hEq
  have hAll : LargeEvenLabelAll ⟨.twA, 5, 1⟩
      (fun R _ I _ => GGTorusReflGenW 3 4 R I) := by
    intro Q hQ
    obtain ⟨K, hKfield, hKfinite, hK, hQ'⟩ := hQ
    letI : Field K := hKfield
    letI : Finite K := hKfinite
    exact ⟨K, hKfield, hKfinite, hK,
      ⟨hQ', ggTorusReflGenW_unitSixThree (n := 1) (K := K) (by simpa using hK) le_rfl
        (by norm_num)⟩⟩
  obtain ⟨K, _, _, hK, hrawK⟩ := hAll _ hraw
  obtain ⟨⟨hs, hna, θ, -, hN, hind⟩, hRefl⟩ := hrawK
  obtain ⟨h4, h3⟩ := card_range_ggGamma_unitDvd63 hH.1 hM63 hN
  let A : Subgroup (MulAut L) := (ggGamma L hN).range
  have hTB : GGTorusTBGroup 3 4 (UnitaryR K 1 6) (UnitaryI K 1 6) L (ggQuotHom θ) A :=
    ggTorusTBGroup_of_marking (p := 3) (r := 4) Nat.prime_three
      hH.1.2.1.2.1 hH.1.2.1.2.2.2 hperfL θ hN
      (fun _ hb => ggLAut_mem_of_induces L θ hN hind hb) h4 h3
  have hA : IsElemAbelian 3 A := hTB.2.2.2.1
  have hAI : ∀ a ∈ A, ∃ x ∈ UnitaryI K 1 6,
      ∀ l : L, x (ggQuotHom θ l) = ggQuotHom θ (a l) := hTB.2.2.2.2.1
  have hsc : GGTorusSelfCent 3 A := hTB.2.2.2.2.2.2.2
  have hInner : Nat.card ↥(ggAutomizer (MulAut.conj : L →* MulAut L).range A) = 720 :=
    psu6_two_inner_card (by simpa using hK) (ggQuotHom_surjective θ)
      (by rw [ker_ggQuotHom]) hperfL hA hAI h4 hsc
  have hZ : Nat.card ↥(Bs ⊓ L ⊓ Subgroup.centralizer (L : Set G)) ≤ 3 := by
    have hle : Bs ⊓ L ⊓ Subgroup.centralizer (L : Set G) ≤
        Bs ⊓ Subgroup.centralizer (L : Set G) := by
      intro z hz
      exact ⟨hz.1.1, hz.2⟩
    have h := Subgroup.card_le_of_le hle
    rwa [hH.1.card_bstar_inf_centralizer_L] at h
  have hW : ggAutomizer (MulAut.conj : L →* MulAut L).range A ≤
      Subgroup.closure (ggTorusReflSet 3 A) := hRefl L (ggQuotHom θ) A hTB
  have hcardEq := card_ggAutomizer_eq_gamma_of_weylReflSet Nat.prime_three (by norm_num)
    hH.1.2.1.2.1 hH.1.2.1.2.2.2 hH.2.2.2.1 hN hZ hW
  rw [hcardEq, hInner]

theorem original_unitSix_not_typeE6
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K)
    (hp : p = 3)
    (hMark : GGInnerDiagOnLabel (fun _ lab => lab = ⟨.twA, 5, 1⟩) p Bs L)
    {Λ : Type} {M : CoxeterMatrix Λ} (hM : GGIsTypeE6 M)
    (f : M.Group ≃* ↥(ggAutomizer L Bs)) : False := by
  have h720 : Nat.card ↥(ggAutomizer L Bs) = 720 :=
    original_unitSix_card720 hH hp hMark
  have h51840 : Nat.card ↥(ggAutomizer L Bs) = 51840 :=
    card_ggAutomizer_of_typeE6 hM f
  rw [h720] at h51840
  norm_num at h51840

theorem original_unitSix_not_exactThree_E6_L
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K) (hp : p = 3)
    (hMark : GGInnerDiagOnLabel (fun _ lab => lab = ⟨.twA, 5, 1⟩) p Bs L) :
    ¬ GGResLeviDatumExact3 p Bs L J K ggSelAny ggTypLE6 := by
  intro hD
  obtain ⟨Λ, i1, i2, S, Λa, i3, i4, ML, CL, MK, CK, V, i5, i6, ι, φ, h, α,
    hS, hA1, hA3, hWML, hCLL, hWMK, hCKK, htyp, hlin, hrefl, hpairL, hpairK, hsel,
    ⟨fL, hfL⟩, hK, hclosL, hclosK, hdel, hclosJ⟩ := hD
  exact original_unitSix_not_typeE6 hH hp hMark htyp fL

section Certs

theorem GGResHyp.not_unitarySixTwo_of_card_automizer_E6
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {y : G} {K X : Subgroup G}
    (hH : GGResHyp 3 B Bs x L D J y K) (hX : X = L ∨ X = K)
    (h5 : ∀ (hN : Bs ≤ Subgroup.normalizer (X : Set G)),
      3 ^ 5 ≤ Nat.card ↥(ggGamma X hN).range)
    (hcard : Nat.card ↥(ggAutomizer X Bs) = 51840)
    (hMark : GGInnerDiagOnLabel (fun _ lab => lab = ⟨.twA, 5, 1⟩) 3 Bs X) :
    False := by
  have hInnX : GGInnerDiagOn Bs X :=
    largeEvenMarking_mono (fun _ _ _ _ _ _ h => ⟨h.2.1, h.2.2⟩) hMark
  obtain ⟨hperf, lab, hΛ, hraw⟩ := hMark
  obtain ⟨R₀, _, I₀, F₀, _, _, _, hEq, _, _⟩ := largeEvenRawDatum_exists hraw
  subst hEq
  obtain ⟨K, _, _, hK, hrawK⟩ := hraw
  obtain ⟨hs, hna, θ, -, hN, hind⟩ := hrawK
  have hBs : IsElemAbelian 3 Bs := hH.1.2.1.2.1
  have hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ 3 = 1 → g ∈ Bs :=
    hH.1.2.1.2.2.2
  have hBsI : ∀ (b : G) (hb : b ∈ Bs), ggLAut X θ ⟨b, hN hb⟩ ∈ UnitaryI K 1 6 :=
    fun b hb => ggLAut_mem_of_induces X θ hN hind hb
  have h3 := hH.pow_three_le_card_range hX hN
  have h5' := h5 hN
  have hTB := ggTorusTBGroup_of_marking (r := 3) Nat.prime_three hBs hSC hperf θ hN hBsI h3 h3
  let A : Subgroup (MulAut X) := (ggGamma X hN).range
  have hA : CFSG.Open.IsElemAbelian 3 A := hTB.2.2.2.1
  have hAI : ∀ a ∈ A, ∃ x ∈ UnitaryI K 1 6, ∀ l : X, x (ggQuotHom θ l) = ggQuotHom θ (a l) :=
    hTB.2.2.2.2.1
  have hsc : GGTorusSelfCent 3 A := hTB.2.2.2.2.2.2.2
  have h4 : 3 ^ 4 ≤ Nat.card A :=
    (Nat.pow_le_pow_right (by norm_num) (by norm_num : 4 ≤ 5)).trans h5'
  have hInner : Nat.card ↥(ggAutomizer (MulAut.conj : X →* MulAut X).range A) = 720 :=
    psu6_two_inner_card (by simpa using hK)
      (ggQuotHom_surjective θ) (by rw [ker_ggQuotHom]) hperf hA hAI h4 hsc
  have hActual : Nat.card ↥(ggAutomizer X Bs) = 51840 := hcard
  have hCP : GGLabelCenterPCyclicInput := ggLabelCenterPCyclicInput_holds
  have hZ : Nat.card ↥(Bs ⊓ X ⊓ Subgroup.centralizer (X : Set G)) ≤ 3 := by
    rcases hX with hXL | hXK
    · rw [hXL]
      have hle : Bs ⊓ L ⊓ Subgroup.centralizer (L : Set G) ≤
          Bs ⊓ Subgroup.centralizer (L : Set G) := by
        intro z hz
        exact ⟨hz.1.1, hz.2⟩
      have h := Subgroup.card_le_of_le hle
      rwa [hH.1.card_bstar_inf_centralizer_L] at h
    · rw [hXK] at hInnX ⊢
      exact ggNbr_card_center_le_of_centerPCyclic hCP hH.1 hInnX
  have hdvd := card_ggAutomizer_dvd_gamma Nat.prime_three hBs hH.2.2.2.1 hN hZ
  rw [hActual, hInner] at hdvd
  norm_num at hdvd

end Certs

end CFSG.StandardType
