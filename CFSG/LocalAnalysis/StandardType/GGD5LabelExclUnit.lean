module

public import CFSG.LocalAnalysis.StandardType.GGD5LabelGlue
import CFSG.LocalAnalysis.StandardType.GGStdUFourExcl
import CFSG.LocalAnalysis.StandardType.GGResE6DepUnitaryTwo
import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyUDefs
import CFSG.LocalAnalysis.StandardType.GGNbrReflGenCore
import CFSG.LocalAnalysis.StandardType.GGForkJrPumpLattice
import CFSG.LocalAnalysis.StandardType.GGTypeANbrKappaBase

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly Module

theorem lup10eU_labelAll_twA4_autCard :
    LargeEvenLabelAll ⟨.twA, 4, 1⟩ fun R _ I _ => GGTorusAutCardSC 3 R I 4 120 := by
  intro Q hQ
  dsimp only [LargeEvenRawDatum] at hQ ⊢
  obtain ⟨K, hKfield, hKfinite, hK, hQ⟩ := hQ
  refine ⟨K, hKfield, hKfinite, hK, hQ, ?_⟩
  have hdq : (5, 2 ^ 1) ≠ (3, 2) := by norm_num
  have hZ := TableBUE.center_proj_eq_bot (K := K) (n := 1) (d := 5) hK (by norm_num) hdq
  have hIp : ∀ φ ∈ LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSUGroup (Fin 5) K (2 ^ 1)))
      (LargeEvenGUSet (Fin 5) K (2 ^ 1)), φ ^ 3 = 1 →
        φ ∈ Set.range (MulAut.conj : LargeEvenProj (LargeEvenSUGroup (Fin 5) K (2 ^ 1)) →*
          MulAut (LargeEvenProj (LargeEvenSUGroup (Fin 5) K (2 ^ 1)))) :=
    fun φ hφ hφp => InndiagSU.ggOutdiagPrime_unitary hK le_rfl (by norm_num) hdq
      Nat.prime_three (by norm_num) (by norm_num) φ hφ hφp
  have hcp := StdSubRestU.ggCenterPrime_unitary (K := K) (n := 1) (d := 5) (p := 3)
    hK le_rfl (by norm_num) hdq Nat.prime_three (by norm_num) (by norm_num)
  have hT := UModel.ggTorusPermEltSC_unitary (K := K) (n := 1) (d := 5) (p := 3)
    hK le_rfl (by norm_num) Nat.prime_three (by norm_num) (by norm_num) (by norm_num)
  have h := ggTorusAutCardSC_of_permEltSC Nat.prime_three (by norm_num) (d := 5) (by norm_num)
    hZ hIp hcp hT
  have h5 : 5 - 1 = 4 := rfl
  have hf : Nat.factorial 5 = 120 := by decide
  simpa [h5, hf] using h

private theorem lup10eU_twA4_false
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} (hS : GGQTwoSetting 3 B Bs x L D J) (hxL : x ∉ L) {y : G}
    {H : Subgroup G} (M : GGQTwoAmbModel 3 Bs x y L H) (e : Fin 5 ≃ M.ι)
    (hecart : ∀ i j, M.cartan (e i) (e j) = CartanMatrix.D 5 i j) (he0 : M.a = e 0)
    (hbas : M.toLin.Basis)
    (hMark : GGInnerDiagOnLabel (fun _ lab => lab = ⟨.twA, 4, 1⟩) 3 Bs L) : False := by
  have h192 : Nat.card (ggAutomizer L Bs) = 192 := lup10c_card_automizer M e hecart he0 hbas
  obtain ⟨hperf, lab, hlab, hraw⟩ := hMark
  obtain ⟨-, -, -, -, -, -, -, hEq, -, -⟩ := largeEvenRawDatum_exists hraw
  obtain rfl := hEq
  obtain ⟨R, iR, I, F, hconj⟩ :=
    largeEvenRawDatum_exists (lup10eU_labelAll_twA4_autCard _ hraw)
  obtain ⟨⟨-, -, θ, -, hN, hind⟩, hSC⟩ := hconj
  have hBs : IsElemAbelian 3 Bs := hS.1.1.2.1.2.1
  have hSC' : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ 3 = 1 → g ∈ Bs :=
    hS.1.1.2.1.2.2.2
  have hBsI : ∀ (b : G) (hb : b ∈ Bs), ggLAut L θ ⟨b, hN hb⟩ ∈ I :=
    fun b hb => ggLAut_mem_of_induces L θ hN hind hb
  have hcardγ : Nat.card (ggGamma L hN).range = 3 ^ 4 :=
    lup10c_card_range_ggGamma hS hxL M e hbas hN
  have hTB : GGTorusTBGroup 3 4 R I L (ggQuotHom θ) (ggGamma L hN).range :=
    ggTorusTBGroup_of_marking Nat.prime_three hBs hSC' hperf θ hN hBsI
      (le_of_eq hcardγ.symm) (by rw [hcardγ]; norm_num)
  obtain ⟨hsurj, hker, hcomm, hA, hAI, -, h3, hSelf⟩ := hTB
  have hinner : Nat.card (ggAutomizer (MulAut.conj : ↥L →* MulAut ↥L).range
      (ggGamma L hN).range) = 120 :=
    (hSC L (ggQuotHom θ) hsurj hker hcomm (ggGamma L hN).range hA hAI h3 hSelf).2
  have hZ : Nat.card ↥(Bs ⊓ L ⊓ Subgroup.centralizer (L : Set G)) ≤ 3 := by
    have hle : Bs ⊓ L ⊓ Subgroup.centralizer (L : Set G) ≤
        Bs ⊓ Subgroup.centralizer (L : Set G) := by
      intro z hz
      exact ⟨hz.1.1, hz.2⟩
    have h := Subgroup.card_le_of_le hle
    rwa [hS.1.1.card_bstar_inf_centralizer_L] at h
  have hdvd := card_ggAutomizer_dvd_gamma Nat.prime_three hBs hS.1.2.2.2.1 hN hZ
  rw [h192, hinner] at hdvd
  exact absurd hdvd (by norm_num)

@[expose] def lup10eU_UC6InnerCard (R : Type) [Group R] (I : Set (MulAut R)) : Prop :=
  ∀ (L' : Type) [Group L'] [Finite L'] (ψ : L' →* R), Function.Surjective ψ →
    ψ.ker ≤ Subgroup.center L' → commutator L' = ⊤ →
    ∀ A : Subgroup (MulAut L'), IsElemAbelian 3 A →
      (∀ a ∈ A, ∃ φ ∈ I, ∀ l : L', φ (ψ l) = ψ (a l)) →
      3 ^ 4 ≤ Nat.card A → GGTorusSelfCent 3 A →
      Nat.card (ggAutomizer (MulAut.conj : L' →* MulAut L').range A) = 720

theorem lup10eU_labelAll_twA5_inner :
    LargeEvenLabelAll ⟨.twA, 5, 1⟩ fun R _ I _ => lup10eU_UC6InnerCard R I := by
  intro Q hQ
  dsimp only [LargeEvenRawDatum] at hQ ⊢
  obtain ⟨K, hKfield, hKfinite, hK, hQ⟩ := hQ
  refine ⟨K, hKfield, hKfinite, hK, hQ, ?_⟩
  intro L' _ _ ψ hψ hker hperf A hA hAI hcard hsc
  exact psu6_two_inner_card (K := K) (by simpa using hK) hψ hker hperf hA hAI hcard hsc

private theorem lup10eU_twA5_false
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} (hS : GGQTwoSetting 3 B Bs x L D J) (hxL : x ∉ L) {y : G}
    {H : Subgroup G} (M : GGQTwoAmbModel 3 Bs x y L H) (e : Fin 5 ≃ M.ι)
    (hecart : ∀ i j, M.cartan (e i) (e j) = CartanMatrix.D 5 i j) (he0 : M.a = e 0)
    (hbas : M.toLin.Basis)
    (hMark : GGInnerDiagOnLabel (fun _ lab => lab = ⟨.twA, 5, 1⟩) 3 Bs L) : False := by
  have h192 : Nat.card (ggAutomizer L Bs) = 192 := lup10c_card_automizer M e hecart he0 hbas
  obtain ⟨hperf, lab, hlab, hraw⟩ := hMark
  obtain ⟨-, -, -, -, -, -, -, hEq, -, -⟩ := largeEvenRawDatum_exists hraw
  obtain rfl := hEq
  obtain ⟨R, iR, I, F, hconj⟩ :=
    largeEvenRawDatum_exists (lup10eU_labelAll_twA5_inner _ hraw)
  obtain ⟨⟨-, -, θ, -, hN, hind⟩, hInnerCard⟩ := hconj
  have hBs : IsElemAbelian 3 Bs := hS.1.1.2.1.2.1
  have hSC' : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ 3 = 1 → g ∈ Bs :=
    hS.1.1.2.1.2.2.2
  have hBsI : ∀ (b : G) (hb : b ∈ Bs), ggLAut L θ ⟨b, hN hb⟩ ∈ I :=
    fun b hb => ggLAut_mem_of_induces L θ hN hind hb
  have hcardγ : Nat.card (ggGamma L hN).range = 3 ^ 4 :=
    lup10c_card_range_ggGamma hS hxL M e hbas hN
  have hTB : GGTorusTBGroup 3 4 R I L (ggQuotHom θ) (ggGamma L hN).range :=
    ggTorusTBGroup_of_marking Nat.prime_three hBs hSC' hperf θ hN hBsI
      (le_of_eq hcardγ.symm) (by rw [hcardγ]; norm_num)
  obtain ⟨hsurj, hker, hcomm, hA, hAI, -, h3, hSelf⟩ := hTB
  have hinner : Nat.card (ggAutomizer (MulAut.conj : ↥L →* MulAut ↥L).range
      (ggGamma L hN).range) = 720 :=
    hInnerCard L (ggQuotHom θ) hsurj hker hcomm (ggGamma L hN).range hA hAI
      (le_of_eq hcardγ.symm) hSelf
  have hZ : Nat.card ↥(Bs ⊓ L ⊓ Subgroup.centralizer (L : Set G)) ≤ 3 := by
    have hle : Bs ⊓ L ⊓ Subgroup.centralizer (L : Set G) ≤
        Bs ⊓ Subgroup.centralizer (L : Set G) := by
      intro z hz
      exact ⟨hz.1.1, hz.2⟩
    have h := Subgroup.card_le_of_le hle
    rwa [hS.1.1.card_bstar_inf_centralizer_L] at h
  have hdvd := card_ggAutomizer_dvd_gamma Nat.prime_three hBs hS.1.2.2.2.1 hN hZ
  rw [h192, hinner] at hdvd
  exact absurd hdvd (by norm_num)

private theorem lup10eU_twA_ge_six
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} (hS : GGQTwoSetting 3 B Bs x L D J) {y : G} {H : Subgroup G}
    (M : GGQTwoAmbModel 3 Bs x y L H) (e : Fin 5 ≃ M.ι) (hbas : M.toLin.Basis) {l : ℕ}
    (hl : 6 ≤ l)
    (hMark : GGInnerDiagOnLabel (fun _ lab => lab = ⟨.twA, l, 1⟩) 3 Bs L) : False := by
  obtain ⟨hperf, lab, hlab, hraw⟩ := hMark
  obtain ⟨-, -, -, -, -, -, -, hEq, -, -⟩ := largeEvenRawDatum_exists hraw
  obtain rfl := hEq
  have hAll := largeEvenLabelAll_torusLift_twA (p := 3) hlab rfl Nat.prime_three
    (by norm_num : 3 ∣ 2 ^ 1 + 1)
  obtain ⟨R, iR, I, F, hconj⟩ := largeEvenRawDatum_exists (hAll _ hraw)
  obtain ⟨⟨-, -, θ, -, -, -⟩, hlift⟩ := hconj
  have hr : 5 ≤ ggUnitaryTorusRank 3 (l + 1) := by
    unfold ggUnitaryTorusRank
    split_ifs <;> omega
  exact lup10c_not_torusLift hS M e hbas θ hr hlift

theorem lup10e_not_unit
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} (hS : GGQTwoSetting 3 B Bs x L D J) (hxL : x ∉ L) {y : G}
    {H : Subgroup G} (M : GGQTwoAmbModel 3 Bs x y L H) (e : Fin 5 ≃ M.ι)
    (hecart : ∀ i j, M.cartan (e i) (e j) = CartanMatrix.D 5 i j) (he0 : M.a = e 0)
    (hbas : M.toLin.Basis) :
    ¬ GGInnerDiagOnLabel (fun _ lab =>
        (lab.tag = .twA ∨ (lab.tag = .twD ∧ lab.rank = 3)) ∧ lab.n = 1) 3 Bs L := by
  intro hq
  have hq' : GGInnerDiagOnLabel (fun _ lab =>
      (lab.tag = .twA ∧ lab.n = 1) ∨ (lab.tag = .twD ∧ lab.rank = 3 ∧ lab.n = 1)) 3 Bs L := by
    refine largeEvenMarking_mono (fun lab R _ I F θ hP => ?_) hq
    obtain ⟨⟨hAB, hn⟩, hN, hind⟩ := hP
    rcases hAB with ht | ⟨ht, hr⟩
    · exact ⟨Or.inl ⟨ht, hn⟩, hN, hind⟩
    · exact ⟨Or.inr ⟨ht, hr, hn⟩, hN, hind⟩
  rcases GGInnerDiagOnLabel.elim_or hq' with hA | hD
  ·
    obtain ⟨hperf, lab, hlab, hraw⟩ := hA
    obtain ⟨t, l, n⟩ := lab
    obtain ⟨-, -, -, -, -, -, -, ⟨ht, hn⟩, -, -⟩ := largeEvenRawDatum_exists hraw
    obtain rfl := ht
    obtain rfl := hn
    have hlab' : 2 ≤ l ∧ (l = 2 → 2 ≤ 1) := hlab.2
    have hfix : ∀ S : ℕ → LargeEvenLabel → Prop, S 3 ⟨.twA, l, 1⟩ →
        GGInnerDiagOnLabel S 3 Bs L := fun S hS' =>
      ⟨hperf, ⟨.twA, l, 1⟩, hlab, largeEvenRawDatum_mono (lab := ⟨.twA, l, 1⟩)
        (fun R _ I F hQ => by
          obtain ⟨hs, hna, θ, -, hN, hind⟩ := hQ
          exact ⟨hs, hna, θ, hS', hN, hind⟩) hraw⟩
    rcases (show l = 2 ∨ l = 3 ∨ l = 4 ∨ l = 5 ∨ 6 ≤ l by omega) with rfl | rfl | rfl | rfl | hl6
    · have h21 : 2 ≤ 1 := hlab'.2 rfl
      omega
    · exact (not_ggInnerDiagOnLabel_u4 hS.1.1 (hfix _ ⟨Or.inl rfl, rfl, rfl⟩)).elim
    · exact lup10eU_twA4_false hS hxL M e hecart he0 hbas (hfix _ rfl)
    · exact lup10eU_twA5_false hS hxL M e hecart he0 hbas (hfix _ rfl)
    · exact lup10eU_twA_ge_six hS M e hbas hl6 (hfix _ rfl)
  ·
    obtain ⟨hperf, lab, hlab, hraw⟩ := hD
    obtain ⟨t, l, n⟩ := lab
    obtain ⟨-, -, -, -, -, -, -, ⟨ht, hr, hn⟩, -, -⟩ := largeEvenRawDatum_exists hraw
    obtain rfl := ht
    obtain rfl := hr
    obtain rfl := hn
    have hfix : ∀ S : ℕ → LargeEvenLabel → Prop, S 3 ⟨.twD, 3, 1⟩ →
        GGInnerDiagOnLabel S 3 Bs L := fun S hS' =>
      ⟨hperf, ⟨.twD, 3, 1⟩, hlab, largeEvenRawDatum_mono (lab := ⟨.twD, 3, 1⟩)
        (fun R _ I F hQ => by
          obtain ⟨hs, hna, θ, -, hN, hind⟩ := hQ
          exact ⟨hs, hna, θ, hS', hN, hind⟩) hraw⟩
    exact (not_ggInnerDiagOnLabel_u4 hS.1.1 (hfix _ ⟨Or.inr rfl, rfl, rfl⟩)).elim

end CFSG.StandardType

end
