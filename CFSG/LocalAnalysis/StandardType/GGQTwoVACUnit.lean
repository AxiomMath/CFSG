module

public import CFSG.LocalAnalysis.StandardType.GGQTwoVACSymp
public import CFSG.LocalAnalysis.StandardType.GGPZTrivUAll
public import CFSG.LocalAnalysis.StandardType.GGTBRowPermFrameAux
public import CFSG.LocalAnalysis.StandardType.GGTwE6WeylTorusTransferCore

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

theorem ggQ2Unit_gamma_card
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G}
    {x : G} {L D J : Subgroup G} (hS : GGQTwoSetting 3 B Bs x L D J)
    {K : Type} [Field K] [Finite K] {n d : ℕ} (hK : Nat.card K = (2 ^ n) ^ 2)
    (hn : 1 ≤ n) (hd : 3 ≤ d) (hpq : 3 ∣ 2 ^ n + 1) (hpd : ¬ 3 ∣ d)
    {θ : L ⧸ Subgroup.center L ≃* LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n))}
    (hperf : commutator L = ⊤) (hBsN : Bs ≤ Subgroup.normalizer (L : Set G))
    (hBsI0 : ∀ b ∈ Bs, ∃ φ ∈ LargeEvenMatConjImage
      (LargeEvenProjMk (LargeEvenSUGroup (Fin d) K (2 ^ n)))
      (LargeEvenGUSet (Fin d) K (2 ^ n)),
      LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) φ) :
    Nat.card (ggGamma L hBsN).range = 3 ^ (d - 1) := by
  have hp : (3 : ℕ).Prime := Nat.prime_three
  have hp2 : 3 ≠ 2 := by norm_num
  have hdq : (d, 2 ^ n) ≠ (3, 2) := by
    rintro h
    have h1 : d = 3 := congrArg Prod.fst h
    exact hpd (h1.symm ▸ dvd_refl 3)
  have hcfg : GGConfig 3 B Bs x L D J := hS.1.1
  obtain ⟨-, hBsE, -, -, -⟩ := hcfg.tableB_facts
  have hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ 3 = 1 → g ∈ Bs := hcfg.2.1.2.2.2
  have hBsI : ∀ (b : G) (hb : b ∈ Bs), ggLAut L θ ⟨b, hBsN hb⟩ ∈ LargeEvenMatConjImage
      (LargeEvenProjMk (LargeEvenSUGroup (Fin d) K (2 ^ n)))
      (LargeEvenGUSet (Fin d) K (2 ^ n)) :=
    fun b hb => ggLAut_mem_of_induces L θ hBsN hBsI0 hb
  have hAe : IsElemAbelian 3 (ggGamma L hBsN).range :=
    isElemAbelian_range (fun a b => Subtype.ext (TableB.IsElemAbelian.comm hBsE a.2 b.2))
      (fun a => Subtype.ext (by simpa using hBsE.2 a a.2)) (ggGamma L hBsN)
  have hAI : ∀ a ∈ (ggGamma L hBsN).range, ∃ φ ∈ LargeEvenMatConjImage
      (LargeEvenProjMk (LargeEvenSUGroup (Fin d) K (2 ^ n)))
      (LargeEvenGUSet (Fin d) K (2 ^ n)), ∀ l : L, φ (ggQuotHom θ l) = ggQuotHom θ (a l) := by
    rintro _ ⟨b, rfl⟩
    exact ⟨ggBeta L θ hBsN b, hBsI b b.2, fun l => ggBeta_ggQuotHom L hBsN θ b l⟩
  have hself : GGTorusSelfCent 3 (ggGamma L hBsN).range :=
    ggTorusSelfCent_ggGamma hBsN hSC
  have hIp := InndiagSU.ggOutdiagPrime_unitary hK hn hd hdq hp hpq hpd
  have hcp := StdSubRestU.ggCenterPrime_unitary hK hn hd hdq hp hp2 hpd
  obtain ⟨Λ, -, hΛinj, -, -, hEab, hEcard, hEsc⟩ :=
    TwE6TB.exists_innerModel (p := 3) hp
      (TableBUE.center_proj_eq_bot hK hd hdq) hIp hcp (ggQuotHom θ)
      (ggQuotHom_surjective θ) (by rw [ker_ggQuotHom]) hperf hAe hAI hself
  obtain ⟨τ, hτinj, hτrange, -, -⟩ :=
    UModel.ggTorusPermEltSCAll_unitary (K := K) (n := n) (d := d) (p := 3) hK hn
      (by omega : 1 ≤ d)
      hp hp2 hpq hpd ((ggGamma L hBsN).range.comap Λ) hEab hEsc
  have hcardE : Nat.card ((ggGamma L hBsN).range.comap Λ) = 3 ^ (d - 1) := by
    rw [← hτrange, Nat.card_congr (MonoidHom.ofInjective hτinj).toEquiv.symm,
      ggTBRowPerm_card_sumZero' d 3]
  rw [← hEcard]
  exact hcardE

theorem ggQ2TBFull_of_unit_of_not_dvd
    {G : Type} [Group G] [Finite G]
    {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hS : GGQTwoSetting p B Bs x L D J) (hp : p = 3)
    (hL : GGInnerDiagOnLabel (fun p lab => GGQ2VACLabUnit p lab ∧ ¬ 3 ∣ lab.rank + 1) p Bs L) :
    GGQ2TBFull p Bs L := by
  subst hp
  obtain ⟨hperf, lab, hlab, hraw⟩ := hL
  obtain ⟨tag, rank, n⟩ := lab
  obtain ⟨R, _, I, F, hQ⟩ := largeEvenRawDatum_exists hraw
  obtain ⟨-, -, θ, hP⟩ := hQ
  dsimp only [GGQ2VACLabUnit] at hP
  obtain ⟨⟨⟨hq, htag⟩, hndvd⟩, hBsN, hBsI0⟩ := hP
  subst htag
  have hn1 : n = 1 := by
    have h1 : 1 ≤ n := hlab.1
    have h2 : n < 2 := hq
    omega
  have hrank3 : 3 ≤ rank := by
    have h2 : 2 ≤ rank := hlab.2.1
    by_contra h3
    have hre : rank = 2 := by omega
    have hn2 : 2 ≤ n := hlab.2.2 hre
    omega
  subst hn1
  dsimp only [LargeEvenRawDatum] at hraw
  obtain ⟨K, _, _, hK, hQ₂⟩ := hraw
  obtain ⟨hsimple, hnab, θ₂, hP₂⟩ := hQ₂
  obtain ⟨-, hBsN₂, hBsI0₂⟩ := hP₂
  refine ⟨⟨.twA, rank, 1⟩, ?_, ?_, ?_⟩
  · simp [GGLabQTwo]
  · refine ⟨hperf, ⟨.twA, rank, 1⟩, hlab, ?_⟩
    dsimp only [CFSG.Assembly.LargeEvenRawDatumLegacy, CFSG.Assembly.LargeEvenRecipeUnitary]
    exact ⟨K, inferInstance, inferInstance, hK, hsimple, hnab, θ₂, rfl⟩
  · rw [← QTwoCav.gamma_card hBsN₂,
      ggQ2Unit_gamma_card (K := K) (n := 1) (d := rank + 1) hS hK (by norm_num)
        (by omega) (by norm_num) hndvd (θ := θ₂) hperf hBsN₂ hBsI0₂]
    simp [GGQ2LieRank]

@[expose] def GGQ2VACLabUnitCoprime (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  GGQ2VACLabUnit p lab ∧ ¬ 3 ∣ lab.rank + 1

theorem ggQTwoGuardFailsOn_unit_of_not_dvd
    (hCav : GGQ2CavOfTBFull) :
    GGQTwoGuardFailsOn GGQ2VACLabUnitCoprime :=
  ggQTwoGuardFailsOn_of_cavFull hCav fun hS hp hL =>
    ggQ2TBFull_of_unit_of_not_dvd hS hp hL


end CFSG.StandardType

end
