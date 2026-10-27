module

public import CFSG.LocalAnalysis.StandardType.GGResSingularAExactTwo
public import CFSG.LocalAnalysis.StandardType.GGTBJSpPlus
public import CFSG.LocalAnalysis.StandardType.GGResSpSplitThree
public import CFSG.LocalAnalysis.StandardType.GGResExcSplitExactTwoL

public import CFSG.LocalAnalysis.StandardType.GGResHigherFieldI1
public import CFSG.LocalAnalysis.StandardType.GGResCentBoundNbrHolds
public import CFSG.LocalAnalysis.StandardType.GGNbrU63
public import CFSG.LocalAnalysis.StandardType.GGQTwoVACUnitDvd
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyReflDom
public import CFSG.LocalAnalysis.StandardType.GGTorusGenRkTransport
public import CFSG.LocalAnalysis.StandardType.GGTableBUnitaryDvdCodimTwoLift
public import CFSG.LocalAnalysis.StandardType.GGUSixTwoModel
public import CFSG.LocalAnalysis.StandardType.GGTBJTwoNodeUnitarySixOriginal
public import CFSG.LocalAnalysis.StandardType.GGTBJLinearMinusFrame
public import CFSG.LocalAnalysis.StandardType.GGResE6Module
public import CFSG.LocalAnalysis.StandardType.GGStdSubIOneProperRestOrth
public import CFSG.LocalAnalysis.StandardType.GGStdSubIOneProperMoreOrth
public import CFSG.LocalAnalysis.GL83PartI.I713.Chain

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.StandardType.LineU TableB

theorem exists_unitaryModel_of_cover
    {G : Type} [Group G] [Finite G] {F : Type} [Field F] [Finite F]
    {p n d : ℕ} [Fact p.Prime] {Bs X : Subgroup G}
    (hF : Nat.card F = (2 ^ n) ^ 2) (hn : 1 ≤ n) (hd : 5 ≤ d)
    (hpq : p ∣ 2 ^ n + 1) (h63 : ¬ (d = 6 ∧ p = 3))
    (hXperf : commutator X = ⊤)
    (hN : Bs ≤ Subgroup.normalizer (X : Set G))
    {ψ : ↥X →* LargeEvenProj (unitarySU 2 n F d)}
    (hψ : Function.Surjective ψ)
    (hker : ψ.ker ≤ Subgroup.center ↥X)
    (hA : IsElemAbelian p (ggGamma X hN).range)
    (hAI : ∀ a ∈ (ggGamma X hN).range,
      ∃ φ ∈ LargeEvenMatConjImage (LargeEvenProjMk (unitarySU 2 n F d))
        (LargeEvenGUSet (Fin d) F (2 ^ n)),
      ∀ l : ↥X, φ (ψ l) = ψ (a l))
    (hr : p ^ (d - 3) ≤ Nat.card (ggGamma X hN).range)
    (h3 : p ^ 3 ≤ Nat.card (ggGamma X hN).range) :
    ∃ ψ : ↥(unitarySU 2 n F d) →* ↥X, UnitTB.Model ψ ∧
      ∀ a ∈ (ggGamma X hN).range, ∃ t : Fin d → F, ActsDiagU ψ a t := by
  have hp : p.Prime := Fact.out
  have hp2 : p ≠ 2 := TableBU.ne_two_of_dvd_two_pow_add_one hn hpq
  have hdq : (d, 2 ^ n) ≠ (3, 2) := by
    intro h
    have := congrArg Prod.fst h
    omega
  have h61 : (d, n) ≠ (6, 1) := by
    rintro h
    have hd6 : d = 6 := congrArg Prod.fst h
    have hn1 : n = 1 := congrArg Prod.snd h
    have hp3 : p = 3 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp
      (by simpa [hn1] using hpq)
    exact h63 ⟨hd6, hp3⟩
  have hcov := LineU.unitaryUniversalCover_holds n d F hF hd h61
  by_cases hpd : p ∣ d
  · have hcard := LineU.card_ge_of_dvd hp hp2 hd hpd h63 hr h3
    obtain ⟨ψ, hψs, hψker, hdiag⟩ :=
      LineU.exists_diagModel hF hn hd hp hpq hpd hcov hψ hker hXperf hA hAI hcard
    exact ⟨ψ, ⟨TableBU.unitaryFieldData_of_card hF hn, hψs, hψker⟩, hdiag⟩
  · obtain ⟨ψ, hψs, hψker, hdiag⟩ :=
      LineU.exists_diagModel_coprime hF hn (by omega : 3 ≤ d) hp hpq hpd hcov
        hψ hker hXperf hA hAI
    exact ⟨ψ, ⟨TableBU.unitaryFieldData_of_card hF hn, hψs, hψker⟩, hdiag⟩

end CFSG.StandardType

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.StandardType.LineU TableB

theorem GGResHyp.exists_unitaryModel_K_of_marking_data
    {G : Type} [Group G] [Finite G] {F : Type} [Field F] [Finite F]
    {n d p : ℕ} [Fact p.Prime] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K)
    (hF : Nat.card F = (2 ^ n) ^ 2) (hn : 1 ≤ n) (hd : 5 ≤ d)
    (hpq : p ∣ 2 ^ n + 1) (h63 : ¬ (d = 6 ∧ p = 3))
    (θ : ↥K ⧸ Subgroup.center ↥K ≃* LargeEvenProj (unitarySU 2 n F d))
    (hN : Bs ≤ Subgroup.normalizer (K : Set G))
    (hact : ∀ b ∈ Bs, ∃ a ∈ LargeEvenMatConjImage (LargeEvenProjMk (unitarySU 2 n F d))
      (LargeEvenGUSet (Fin d) F (2 ^ n)),
      LargeEvenInduces θ (fun l l' : ↥K => (l' : G) = b⁻¹ * l * b) a) :
    ∃ ψ : ↥(unitarySU 2 n F d) →* ↥K, UnitTB.Model ψ ∧
      ∀ a ∈ (ggGamma K hN).range, ∃ t : Fin d → F, ActsDiagU ψ a t := by
  have hp : p.Prime := Fact.out
  have hnb : GGNbr p B x D J y K := hH.2.2.2.2.1
  have hKmark : GGInnerDiagOn Bs K := hH.2.2.1.2 y K hnb
  have hperf : commutator ↥K = ⊤ := hKmark.1
  have hBs : IsElemAbelian p Bs := hH.1.tableB_facts.2.1
  have hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs :=
    hH.1.2.1.2.2.2
  have hdq : (d, 2 ^ n) ≠ (3, 2) := by
    intro h
    have := congrArg Prod.fst h
    omega
  have hlift := ggTorusLift_unitary hF hn (by omega : 3 ≤ d) hdq hp hpq
  have hr := pow_le_card_range_ggGamma_bstar_of_torusLift hH.1 hnb hperf θ hN hlift
  have h3 := pow_three_le_card_range_ggGamma_bstar hH.1 hnb hN
  have hTB : GGTorusTBGroup p (ggUnitaryTorusRank p d)
      (LargeEvenProj (unitarySU 2 n F d))
      (LargeEvenMatConjImage (LargeEvenProjMk (unitarySU 2 n F d))
        (LargeEvenGUSet (Fin d) F (2 ^ n))) K (ggQuotHom θ) (ggGamma K hN).range :=
    ggTorusTBGroup_of_marking hp hBs hSC hperf θ hN
      (fun b hb => ggLAut_mem_of_induces (B := Bs) (L := K)
        (R := LargeEvenProj (unitarySU 2 n F d)) (θ := θ)
        (I := LargeEvenMatConjImage (LargeEvenProjMk (unitarySU 2 n F d))
          (LargeEvenGUSet (Fin d) F (2 ^ n))) hN hact hb) hr h3
  obtain ⟨hψ, hker, _, hA, hAI, -, -, _⟩ := hTB
  have hr' : p ^ (d - 3) ≤ Nat.card (ggGamma K hN).range := by
    by_cases hpd : p ∣ d
    · simpa [ggUnitaryTorusRank, hpd] using hr
    · exact (Nat.pow_le_pow_right hp.pos (by omega : d - 3 ≤ d - 2)).trans
        (by simpa [ggUnitaryTorusRank, hpd] using hr)
  exact exists_unitaryModel_of_cover hF hn hd hpq h63 hperf hN hψ hker hA hAI hr' h3

end CFSG.StandardType

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.StandardType.LineU TableB

theorem GGResHyp.exists_unitaryModel_K_of_marking_not_six_three
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K)
    (hU : GGInnerDiagOnLabel
      (fun p lab => lab.tag = .twA ∧ 4 ≤ lab.rank ∧ p ∣ 2 ^ lab.n + 1 ∧
        ¬ (lab.rank + 1 = 6 ∧ p = 3)) p Bs K)
    (hN : Bs ≤ Subgroup.normalizer (K : Set G)) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (n d : ℕ)
      (θ : ↥K ⧸ Subgroup.center ↥K ≃* LargeEvenProj (unitarySU 2 n F d))
      (ψ : ↥(unitarySU 2 n F d) →* ↥K),
      UnitTB.Model ψ ∧
        ∀ a ∈ (ggGamma K hN).range, ∃ t : Fin d → F, ActsDiagU ψ a t := by
  classical
  obtain ⟨hperf, lab, hΛ, hraw⟩ := hU
  obtain ⟨R₀, iR₀, I₀, F₀, hQ₀⟩ := largeEvenRawDatum_exists hraw
  obtain ⟨-, -, θ₀, hP₀⟩ := hQ₀
  dsimp only at hP₀
  obtain ⟨⟨htag, hr4, hpq, hnot⟩, hN₀, hact₀⟩ := hP₀
  obtain ⟨tag, rank, n⟩ := lab
  change tag = .twA at htag
  change 4 ≤ rank at hr4
  change p ∣ 2 ^ n + 1 at hpq
  change ¬ (rank + 1 = 6 ∧ p = 3) at hnot
  subst tag
  dsimp only [LargeEvenRawDatumLegacy] at hraw
  obtain ⟨F, hField, hFinite, hFK, hQ⟩ := hraw
  letI : Field F := hField
  letI : Finite F := hFinite
  obtain ⟨-, -, θ, hP⟩ := hQ
  obtain ⟨⟨-, -, -, -⟩, hN', hact⟩ := hP
  have hn : 1 ≤ n := hΛ.1
  have hd : 5 ≤ rank + 1 := by omega
  have h63 : ¬ (rank + 1 = 6 ∧ p = 3) := hnot
  obtain ⟨ψ, hM, hdiag⟩ :=
    hH.exists_unitaryModel_K_of_marking_data hFK hn hd hpq h63 θ hN hact
  exact ⟨F, hField, hFinite, n, rank + 1, θ, ψ, hM, hdiag⟩

end CFSG.StandardType

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.StandardType.LineU TableB

theorem GGResHyp.exists_unitaryModel_K_six_three_of_gamma
    {G : Type} [Group G] [Finite G] {F : Type} [Field F] [Finite F]
    {n : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp 3 B Bs x L D J y K)
    (hF : Nat.card F = (2 ^ n) ^ 2) (hn : n = 1)
    (hpq : 3 ∣ 2 ^ n + 1)
    (θ : ↥K ⧸ Subgroup.center ↥K ≃* LargeEvenProj (unitarySU 2 n F 6))
    (hN : Bs ≤ Subgroup.normalizer (K : Set G))
    (hact : ∀ b ∈ Bs, ∃ a ∈ LargeEvenMatConjImage (LargeEvenProjMk (unitarySU 2 n F 6))
      (LargeEvenGUSet (Fin 6) F (2 ^ n)),
      LargeEvenInduces θ (fun l l' : ↥K => (l' : G) = b⁻¹ * l * b) a)
    (hodd : Odd (Nat.card (ggQuotHom θ).ker))
    (hγ : 3 ^ 4 ≤ Nat.card (ggGamma K hN).range) :
    ∃ ψ : ↥(unitarySU 2 n F 6) →* ↥K, UnitTB.Model ψ ∧
      ∀ a ∈ (ggGamma K hN).range, ∃ t : Fin 6 → F, ActsDiagU ψ a t := by
  subst hn
  have hp : Nat.Prime 3 := Nat.prime_three
  have hnb : GGNbr 3 B x D J y K := hH.2.2.2.2.1
  have hKmark : GGInnerDiagOn Bs K := hH.2.2.1.2 y K hnb
  have hperf : commutator ↥K = ⊤ := hKmark.1
  have hBs : IsElemAbelian 3 Bs := hH.1.tableB_facts.2.1
  have hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ 3 = 1 → g ∈ Bs :=
    hH.1.2.1.2.2.2
  have hdq : (6, 2 ^ 1) ≠ (3, 2) := by norm_num
  have hlift := ggTorusLift_unitary hF (by norm_num : 1 ≤ 1) (by norm_num : 3 ≤ 6)
    hdq hp hpq
  have hr := pow_le_card_range_ggGamma_bstar_of_torusLift hH.1 hnb hperf θ hN hlift
  have h3 := pow_three_le_card_range_ggGamma_bstar hH.1 hnb hN
  have hTB : GGTorusTBGroup 3 (ggUnitaryTorusRank 3 6)
      (LargeEvenProj (unitarySU 2 1 F 6))
      (LargeEvenMatConjImage (LargeEvenProjMk (unitarySU 2 1 F 6))
        (LargeEvenGUSet (Fin 6) F (2 ^ 1))) K (ggQuotHom θ) (ggGamma K hN).range :=
    ggTorusTBGroup_of_marking hp hBs hSC hperf θ hN
      (fun b hb => ggLAut_mem_of_induces (B := Bs) (L := K)
        (R := LargeEvenProj (unitarySU 2 1 F 6)) (θ := θ)
        (I := LargeEvenMatConjImage (LargeEvenProjMk (unitarySU 2 1 F 6))
          (LargeEvenGUSet (Fin 6) F (2 ^ 1))) hN hact hb) hr h3
  obtain ⟨hψ, hker, _, hA, hAI, -, -, _⟩ := hTB
  obtain ⟨ψ, hM, hdiag⟩ :=
    CFSG.StandardType.USixTwo.exists_diagModel_odd hF hψ hker hperf hodd hA hAI
      (by simpa using hγ)
  exact ⟨ψ, hM, hdiag⟩



theorem GGResHyp.exists_unitaryModel_K_six_three_qGeFour_of_gamma
    {G : Type} [Group G] [Finite G] {F : Type} [Field F] [Finite F]
    {n : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp 3 B Bs x L D J y K)
    (hF : Nat.card F = (2 ^ n) ^ 2) (hn : 2 ≤ n)
    (hpq : 3 ∣ 2 ^ n + 1)
    (θ : ↥K ⧸ Subgroup.center ↥K ≃* LargeEvenProj (unitarySU 2 n F 6))
    (hN : Bs ≤ Subgroup.normalizer (K : Set G))
    (hact : ∀ b ∈ Bs, ∃ a ∈ LargeEvenMatConjImage (LargeEvenProjMk (unitarySU 2 n F 6))
      (LargeEvenGUSet (Fin 6) F (2 ^ n)),
      LargeEvenInduces θ (fun l l' : ↥K => (l' : G) = b⁻¹ * l * b) a)
    (hγ : 3 ^ 4 ≤ Nat.card (ggGamma K hN).range) :
    ∃ ψ : ↥(unitarySU 2 n F 6) →* ↥K, UnitTB.Model ψ ∧
      ∀ a ∈ (ggGamma K hN).range, ∃ t : Fin 6 → F, ActsDiagU ψ a t := by
  have hp : Nat.Prime 3 := Nat.prime_three
  have hnb : GGNbr 3 B x D J y K := hH.2.2.2.2.1
  have hKmark : GGInnerDiagOn Bs K := hH.2.2.1.2 y K hnb
  have hperf : commutator ↥K = ⊤ := hKmark.1
  have hBs : IsElemAbelian 3 Bs := hH.1.tableB_facts.2.1
  have hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ 3 = 1 → g ∈ Bs :=
    hH.1.2.1.2.2.2
  have hdq : (6, 2 ^ n) ≠ (3, 2) := by
    intro h
    have := congrArg Prod.fst h
    omega
  have hlift := ggTorusLift_unitary hF (by omega : 1 ≤ n) (by norm_num : 3 ≤ 6)
    hdq hp hpq
  have hr := pow_le_card_range_ggGamma_bstar_of_torusLift hH.1 hnb hperf θ hN hlift
  have h3 := pow_three_le_card_range_ggGamma_bstar hH.1 hnb hN
  have hTB : GGTorusTBGroup 3 (ggUnitaryTorusRank 3 6)
      (LargeEvenProj (unitarySU 2 n F 6))
      (LargeEvenMatConjImage (LargeEvenProjMk (unitarySU 2 n F 6))
        (LargeEvenGUSet (Fin 6) F (2 ^ n))) K (ggQuotHom θ) (ggGamma K hN).range :=
    ggTorusTBGroup_of_marking hp hBs hSC hperf θ hN
      (fun b hb => ggLAut_mem_of_induces (B := Bs) (L := K)
        (R := LargeEvenProj (unitarySU 2 n F 6)) (θ := θ)
        (I := LargeEvenMatConjImage (LargeEvenProjMk (unitarySU 2 n F 6))
          (LargeEvenGUSet (Fin 6) F (2 ^ n))) hN hact hb) hr h3
  obtain ⟨hψ, hker, _, hA, hAI, -, -, _⟩ := hTB
  have hcov := LineU.unitaryUniversalCover_holds n 6 F hF (by norm_num)
    (by rintro ⟨-, h⟩; omega)
  obtain ⟨ψ, hψs, hψker, hdiag⟩ :=
    LineU.exists_diagModel hF (by omega : 1 ≤ n) (by norm_num) hp hpq (by norm_num : 3 ∣ 6)
      hcov hψ hker hperf hA hAI (by simpa using hγ)
  exact ⟨ψ, ⟨TableBU.unitaryFieldData_of_card hF (by omega), hψs, hψker⟩, hdiag⟩


theorem GGResHyp.exists_unitaryModel_K_qTwo_of_marking_rank
    {G : Type} [Group G] [Finite G] {p r : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K)
    (hU : GGInnerDiagOnLabel
      (fun p lab => lab.tag = .twA ∧ lab.rank = r ∧ lab.n = 1 ∧
        p ∣ 2 ^ lab.n + 1) p Bs K)
    (hr4 : 4 ≤ r) (hr5 : r ≠ 5) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F)
      (ψ : ↥(unitarySU 2 1 F (r + 1)) →* ↥K),
      UnitTB.Model ψ ∧
        ∀ a ∈ (ggGamma K (hH.2.2.1.2 y K hH.2.2.2.2.1).le_normalizer).range,
          ∃ t : Fin (r + 1) → F, ActsDiagU ψ a t := by
  classical
  unfold GGInnerDiagOnLabel at hU
  obtain ⟨hperf, lab, hΛ, hraw⟩ := hU
  obtain ⟨R₀, iR₀, I₀, F₀, hQ₀⟩ := largeEvenRawDatum_exists hraw
  obtain ⟨-, -, θ₀, hP₀⟩ := hQ₀
  dsimp only at hP₀
  obtain ⟨⟨htag, hrank, hn1, hpq⟩, hN₀, hact₀⟩ := hP₀
  obtain ⟨tag, rank, n⟩ := lab
  change tag = .twA at htag
  change rank = r at hrank
  change n = 1 at hn1
  change p ∣ 2 ^ n + 1 at hpq
  subst tag
  subst n
  subst rank
  dsimp only [LargeEvenRawDatumLegacy] at hraw
  obtain ⟨F, hField, hFinite, hFK, hQ⟩ := hraw
  letI : Field F := hField
  letI : Finite F := hFinite
  obtain ⟨-, -, θ, hP⟩ := hQ
  obtain ⟨⟨-, -, -, -⟩, hN, hact⟩ := hP
  have hd : 5 ≤ r + 1 := by omega
  have h63 : ¬ (r + 1 = 6 ∧ p = 3) := by
    rintro ⟨h6, -⟩
    exact hr5 (by omega)
  have hpq3 : p ∣ 2 ^ 1 + 1 := by simpa using hpq
  obtain ⟨ψ, hM, hdiag⟩ :=
    hH.exists_unitaryModel_K_of_marking_data (n := 1) (d := r + 1)
      hFK (by omega) hd hpq3 h63 θ hN hact
  exact ⟨F, hField, hFinite, ψ, hM, hdiag⟩

theorem GGResHyp.gamma_four_of_unitary_six_two_K
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hLB : GGLBalanceInput) (hP : GGStdSubPrimeInput)
    (hH : GGResHyp p B Bs x L D J y K)
    (hN : Bs ≤ Subgroup.normalizer (K : Set G)) (hp3 : p = 3)
    (hU63 : GGInnerDiagOnLabel GGNbrInner937U63Label p Bs K) :
    3 ^ 4 ≤ Nat.card (ggGamma K hN).range := by
  subst hp3
  exact ggUnitDvd63NbrRankInput_holds hLB hP G 3 B Bs x L D J hH.1 y K
    hH.2.2.2.2.1 hN hU63

theorem GGResHyp.u63_marking_of_cell
    {G : Type} [Group G] {p : ℕ} {Bs K : Subgroup G}
    (hcell : GGInnerDiagOnLabel
      (fun p lab => lab.tag = .twA ∧ lab.rank = 5 ∧ lab.n = 1 ∧ p = 3) p Bs K) :
    GGInnerDiagOnLabel GGNbrInner937U63Label p Bs K :=
  GGInnerDiagOnLabel.mono_label (fun lab h => by
    refine ⟨⟨h.1, by omega, ?_, ?_⟩, h.2.1, h.2.2.2⟩
    · rw [h.2.2.1, h.2.2.2]
      norm_num
    · rw [h.2.1, h.2.2.2]
      norm_num) hcell

theorem GGResHyp.unitary_six_two_K_marking_data
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp 3 B Bs x L D J y K)
    (hcell : GGInnerDiagOnLabel
      (fun _ lab => lab.tag = .twA ∧ lab.rank = 5 ∧ lab.n = 1) 3 Bs K) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F),
      Nat.card F = 4 ∧
      ∃ θ : ↥K ⧸ Subgroup.center ↥K ≃*
          LargeEvenProj (unitarySU 2 1 F 6),
        Bs ≤ Subgroup.normalizer (K : Set G) ∧
        ∀ b ∈ Bs, ∃ a ∈ LargeEvenMatConjImage
          (LargeEvenProjMk (unitarySU 2 1 F 6))
          (LargeEvenGUSet (Fin 6) F (2 ^ 1)),
          LargeEvenInduces θ (fun l l' : ↥K => (l' : G) = b⁻¹ * l * b) a := by
  classical
  unfold GGInnerDiagOnLabel at hcell
  obtain ⟨hperf, lab, hΛ, hraw⟩ := hcell
  obtain ⟨R0, _, I0, F0, _, _, _, hP0⟩ := largeEvenRawDatum_exists hraw
  obtain ⟨hS, -, -⟩ := hP0
  rcases lab with ⟨tag, rank, n⟩
  simp only at hS
  obtain ⟨htag, hrank, hn⟩ := hS
  subst tag
  subst rank
  subst n
  dsimp only [LargeEvenRawDatum] at hraw
  obtain ⟨F, hField, hFinite, hFK, hQ⟩ := hraw
  letI : Field F := hField
  letI : Finite F := hFinite
  obtain ⟨-, -, θ, hP⟩ := hQ
  obtain ⟨-, hN, hact⟩ := hP
  have hF4 : Nat.card F = 4 := by simpa using hFK
  refine ⟨F, hField, hFinite, hF4, θ, hN, ?_⟩
  change ∀ b ∈ Bs, ∃ a ∈ LargeEvenMatConjImage
      (LargeEvenProjMk (unitarySU 2 1 F 6))
      (LargeEvenGUSet (Fin 6) F (2 ^ 1)),
      LargeEvenInduces θ (fun l l' : ↥K => (l' : G) = b⁻¹ * l * b) a at hact
  exact hact

section GammaCert


theorem ggU63Label_le_qplus (p : ℕ) (lab : LargeEvenLabel)
    (h : GGNbrInner937U63Label p lab) :
    lab.tag = .twA ∧ 4 ≤ lab.rank ∧ p ∣ 2 ^ lab.n + 1 := by
  obtain ⟨⟨htag, h3, hpq, -⟩, hrank, -⟩ := h
  exact ⟨htag, by omega, hpq⟩

theorem ggGammaSuppliers_proved : GGLBalanceInput ∧ GGStdSubPrimeInput := by
  have h01 : CFSG.Yardstones.M3f9567aba59d.GGRemainderStdSubTableB :=
    ggRemainderStdSubTableB_proved
  obtain ⟨hTE6L, -, hsR, -⟩ := h01
  have hTE6 := ggTableBTwE6Round12_of_lang hTE6L
  have hP : GGStdSubPrimeInput :=
    ggStdSubPrimeInput_of_round12 hTE6 TwF4SUThree.ggTwF4ThreeRankInput_holds hsR
  have hLB : GGLBalanceInput :=
    ggLBalanceInput_of_catalogueSchreier
      CFSG.RankThree.PartOne.TCB.schreierFor_inCatalog_holds
  exact ⟨hLB, hP⟩


theorem GGResHyp.gamma_four_of_unitary_six_two_K_original
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K)
    (hN : Bs ≤ Subgroup.normalizer (K : Set G)) (hp3 : p = 3)
    (hU63 : GGInnerDiagOnLabel GGNbrInner937U63Label p Bs K) :
    3 ^ 4 ≤ Nat.card (ggGamma K hN).range := by
  obtain ⟨hLB, hP⟩ := ggGammaSuppliers_proved
  exact GGResHyp.gamma_four_of_unitary_six_two_K hLB hP hH hN hp3 hU63

theorem GGResHyp.exists_unitaryModel_K_six_two_of_marking_gamma_original
    {G : Type} [Group G] [Finite G] {F : Type} [Field F] [Finite F]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp 3 B Bs x L D J y K)
    (hF : Nat.card F = 4)
    (hU63 : GGInnerDiagOnLabel GGNbrInner937U63Label 3 Bs K)
    (θ : ↥K ⧸ Subgroup.center ↥K ≃* LargeEvenProj (unitarySU 2 1 F 6))
    (hodd : Odd (Nat.card (ggQuotHom θ).ker))
    (hN : Bs ≤ Subgroup.normalizer (K : Set G))
    (hact : ∀ b ∈ Bs, ∃ a ∈ LargeEvenMatConjImage (LargeEvenProjMk (unitarySU 2 1 F 6))
      (LargeEvenGUSet (Fin 6) F 2),
      LargeEvenInduces θ (fun l l' : ↥K => (l' : G) = b⁻¹ * l * b) a) :
    ∃ ψ : ↥(unitarySU 2 1 F 6) →* ↥K, UnitTB.Model ψ ∧
      ∀ a ∈ (ggGamma K hN).range, ∃ t : Fin 6 → F, ActsDiagU ψ a t := by
  have hγ : 3 ^ 4 ≤ Nat.card (ggGamma K hN).range :=
    GGResHyp.gamma_four_of_unitary_six_two_K_original hH hN rfl hU63
  exact GGResHyp.exists_unitaryModel_K_six_three_of_gamma hH
    (by simpa using hF) rfl (by norm_num : 3 ∣ 2 ^ 1 + 1) θ hN hact hodd hγ



theorem GGResHyp.beta_four_of_unitary_six_two_K_original
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K)
    (hN : Bs ≤ Subgroup.normalizer (K : Set G)) (hp3 : p = 3)
    (hU63 : GGInnerDiagOnLabel GGNbrInner937U63Label p Bs K)
    {R : Type} [Group R] (θ : ↥K ⧸ Subgroup.center ↥K ≃* R) :
    3 ^ 4 ≤ Nat.card (ggBeta K θ hN).range := by
  have hKmark : GGInnerDiagOn Bs K := hH.2.2.1.2 y K hH.2.2.2.2.1
  have hγ : 3 ^ 4 ≤ Nat.card (ggGamma K hN).range :=
    GGResHyp.gamma_four_of_unitary_six_two_K_original hH hN hp3 hU63
  exact ggQ2UnitDvd_beta_card_bound (n := 3 ^ 4) θ hN hKmark.1 hγ

theorem GGResHyp.beta_image_of_unitary_six_two_K_original
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K)
    (hN : Bs ≤ Subgroup.normalizer (K : Set G)) (hp3 : p = 3)
    (hU63 : GGInnerDiagOnLabel GGNbrInner937U63Label p Bs K)
    {R : Type} [Group R] (I : Set (MulAut R))
    (θ : ↥K ⧸ Subgroup.center ↥K ≃* R)
    (hI : ∀ b ∈ Bs, ∃ φ ∈ I, LargeEvenInduces θ
      (fun l l' : ↥K => (l' : G) = b⁻¹ * l * b) φ) :
    IsElemAbelian p (ggBeta K θ hN).range ∧
      ((ggBeta K θ hN).range : Set (MulAut R)) ⊆ I ∧
      3 ^ 3 ≤ Nat.card (ggBeta K θ hN).range := by
  have hKmark : GGInnerDiagOn Bs K := hH.2.2.1.2 y K hH.2.2.2.2.1
  have h := ggBeta_range_rank_three_of_innerDiag hH.1
    (Or.inr ⟨y, hH.2.2.2.2.1⟩) I θ hN hKmark.1 hI
  simpa [hp3] using h


theorem GGResHyp.gamma_four_of_unitary_cell
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K)
    (hN : Bs ≤ Subgroup.normalizer (K : Set G)) (hp3 : p = 3)
    (hcell : GGInnerDiagOnLabel
      (fun p lab => lab.tag = .twA ∧ lab.rank = 5 ∧ lab.n = 1 ∧ p = 3) p Bs K) :
    3 ^ 4 ≤ Nat.card (ggGamma K hN).range :=
  GGResHyp.gamma_four_of_unitary_six_two_K_original hH hN hp3
    (GGResHyp.u63_marking_of_cell hcell)



theorem GGResHyp.exists_unitaryModel_K_six_two_of_cell_B_lt_Bs
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp 3 B Bs x L D J y K)
    (hlt : B < Bs)
    (hcell : GGInnerDiagOnLabel
      (fun _ lab => lab.tag = .twA ∧ lab.rank = 5 ∧ lab.n = 1) 3 Bs K) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F)
      (ψ : ↥(unitarySU 2 1 F 6) →* ↥K),
      Nat.card F = 4 ∧ UnitTB.Model ψ ∧
      ∀ a ∈ (ggGamma K
        (GGInnerDiagOn.le_normalizer (hH.2.2.1.2 y K hH.2.2.2.2.1))).range,
        ∃ t : Fin 6 → F, LineU.ActsDiagU ψ a t := by
  obtain ⟨F, hField, hFinite, hF4, θ, hN, hact⟩ :=
    GGResHyp.unitary_six_two_K_marking_data hH hcell
  letI : Field F := hField
  letI : Finite F := hFinite
  have hcell' : GGInnerDiagOnLabel
      (fun p lab => lab.tag = .twA ∧ lab.rank = 5 ∧ lab.n = 1 ∧ p = 3) 3 Bs K :=
    GGInnerDiagOnLabel.mono_label (fun lab h => ⟨h.1, h.2.1, h.2.2, rfl⟩) hcell
  have hU63 : GGInnerDiagOnLabel GGNbrInner937U63Label 3 Bs K :=
    GGResHyp.u63_marking_of_cell hcell'
  have hodd : Odd (Nat.card (ggQuotHom θ).ker) := by
    rw [ker_ggQuotHom]
    exact hH.1.odd_card_center_of_B_lt_Bs hlt hN
  obtain ⟨ψ, hM, hdiag⟩ :=
    GGResHyp.exists_unitaryModel_K_six_two_of_marking_gamma_original
      hH hF4 hU63 θ hodd hN hact
  refine ⟨F, hField, hFinite, ψ, hF4, hM, ?_⟩
  simpa only [GGInnerDiagOn.le_normalizer] using hdiag

theorem GGResHyp.not_exactThree_K_of_six_two_cell_B_lt_Bs
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp 3 B Bs x L D J y K)
    (hlt : B < Bs)
    (hcell : GGInnerDiagOnLabel
      (fun _ lab => lab.tag = .twA ∧ lab.rank = 5 ∧ lab.n = 1) 3 Bs K) :
    ¬ GGResLeviDatumExact3 3 Bs K J L ggSelAny ggTypAny := by
  rintro h3
  obtain ⟨F, hField, hFinite, ψ, hF4, hM, hdiag⟩ :=
    GGResHyp.exists_unitaryModel_K_six_two_of_cell_B_lt_Bs hH hlt hcell
  letI : Field F := hField
  letI : Finite F := hFinite
  have hLB : GGLBalanceInput := ggGammaSuppliers_proved.1
  obtain ⟨hp3, hdiv, hd9, δ, hδ, hδdiag⟩ :=
    hH.unitary_exactThree_J_model_qTwo_of_K hLB hM
      (by norm_num : 3 ∣ 2 ^ 1 + 1) (by norm_num : 5 ≤ 6) hdiag h3
  have hJcomp : CFSG.Assembly.IsComponentOf J
      (L ⊓ Subgroup.centralizer (D : Set G)) :=
    hH.1.2.2.1.2.2.2.2.2.1
  have hJq : CFSG.Assembly.IsQuasisimple ↥J := hJcomp.2.2
  have hJqNat : CFSG.IsQuasisimple ↥J :=
    (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native ↥J).mp hJq
  haveI hsolSU : Group.IsSolvable ↥(unitarySU 2 1 F (6 - 3)) :=
    SmallU.isSolvable_unitarySU_small hδ.field (by norm_num) (by norm_num)
  have hsolJ : Group.IsSolvable ↥J :=
    solvable_of_surjective (f := δ) hδ.surj
  exact not_isSolvable_of_isQuasisimple hJqNat hsolJ


theorem GGResHyp.unitary_six_two_K_fix_mem_centralizer_noOdd
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp 3 B Bs x L D J y K)
    (hcell : GGInnerDiagOnLabel
      (fun _ lab => lab.tag = .twA ∧ lab.rank = 5 ∧ lab.n = 1) 3 Bs K) :
    ∀ b : ↥Bs, (∀ φ ∈ ggAutomizer J Bs, φ b = b) →
      (b : G) ∈ Subgroup.centralizer (J : Set G) := by
  classical
  open CFSG.StandardType.Line63.H5 CFSG.StandardType.SCFourCover in
  obtain ⟨F, hField, hFinite, hF4, θ, hN, hact⟩ :=
    GGResHyp.unitary_six_two_K_marking_data hH hcell
  letI : Field F := hField
  letI : Finite F := hFinite
  have hcell' : GGInnerDiagOnLabel
      (fun p lab => lab.tag = .twA ∧ lab.rank = 5 ∧ lab.n = 1 ∧ p = 3) 3 Bs K :=
    GGInnerDiagOnLabel.mono_label (fun lab h => ⟨h.1, h.2.1, h.2.2, rfl⟩) hcell
  have hγ : 3 ^ 4 ≤ Nat.card (ggGamma K hN).range :=
    GGResHyp.gamma_four_of_unitary_cell hH hN rfl hcell'
  have hxBs : x ∈ Bs := hH.1.tableB_facts.2.2.1
  have hKmark : GGInnerDiagOn Bs K := hH.2.2.1.2 y K hH.2.2.2.2.1
  have hKperf : commutator ↥K = ⊤ := hKmark.1
  have hBs : IsElemAbelian 3 Bs := hH.1.tableB_facts.2.1
  have hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ 3 = 1 → g ∈ Bs :=
    hH.1.2.1.2.2.2
  have hCharF : CharP F 2 :=
    charP_two_of_card (by simpa using hF4 : Nat.card F = 2 ^ 2)
  letI : CharP F 2 := hCharF
  obtain ⟨hNbar, φQ, hMQ, hdiagQ⟩ :=
    exists_diagonal_cover_of_unitary_six_two_red hF4 hKperf θ hN hBs hact hγ
  let NX : Subgroup G := Subgroup.normalizer (K : Set G)
  let Xbar : Subgroup (RedGrp K) := (redMkL K).range
  let Bbar : Subgroup (RedGrp K) := (redMkB hN).range
  let Jbar : Subgroup (RedGrp K) := (J.subgroupOf NX).map (redMk K)
  let JbarK : Subgroup (RedGrp K) := (J.subgroupOf K).map (redMkL K)
  have hJX : J ≤ K := GGResHyp.J_le_K_of_original hH
  have hJcompL : IsComponentOf J (L ⊓ Subgroup.centralizer (D : Set G)) :=
    hH.1.2.2.1.2.2.2.2.2.1
  have hJperf : commutator ↥J = ⊤ := hJcompL.2.2.1
  have hNJ : Bs ≤ Subgroup.normalizer (J : Set G) := GGResHyp.Bs_le_normalizer_J hH
  have hJbarK_eq : JbarK = Jbar := by
    ext x
    constructor
    · rintro ⟨j, hj, rfl⟩
      exact ⟨⟨(j : G), K.le_normalizer (hJX (Subgroup.mem_subgroupOf.mp hj))⟩,
        Subgroup.mem_subgroupOf.mp hj, rfl⟩
    · rintro ⟨jN, hjN, rfl⟩
      exact ⟨⟨(jN : G), hJX (Subgroup.mem_subgroupOf.mp hjN)⟩,
        Subgroup.mem_subgroupOf.mpr (Subgroup.mem_subgroupOf.mp hjN), rfl⟩
  have hJbar_le_Xbar : Jbar ≤ Xbar := by
    rintro _ ⟨jN, hjN, rfl⟩
    exact ⟨⟨(jN : G), hJX (Subgroup.mem_subgroupOf.mp hjN)⟩, rfl⟩
  have hψsurj : Function.Surjective ((redMkL K).rangeRestrict) :=
    MonoidHom.rangeRestrict_surjective _
  have hψker : ((redMkL K).rangeRestrict).ker ≤ Subgroup.center ↥K := by
    rw [redMkL_rangeRestrict_ker]
    exact USixTwo.zTwo_le_center
  let xBs : ↥Bs := ⟨x, hxBs⟩
  let xbar : ↥Bbar := ⟨redMkB hN xBs⁻¹, ⟨xBs⁻¹, rfl⟩⟩
  have hcompat : ∀ l : ↥K,
      ggGamma Xbar hNbar xbar (((redMkL K).rangeRestrict) l) =
        ((redMkL K).rangeRestrict) (ggGamma K hN (xBs⁻¹) l) := by
    intro l
    apply Subtype.ext
    change redMk K (Subgroup.inclusion hN (xBs⁻¹)) * redMkL K l *
        (redMk K (Subgroup.inclusion hN (xBs⁻¹)))⁻¹ =
      redMkL K (K.normalizerMonoidHom
        (Subgroup.inclusion hN (xBs⁻¹)) l)
    exact redMk_conj (L := K) (Subgroup.inclusion hN (xBs⁻¹)) l
  have hfixeq : ggFix (H := ↥K) (ggGamma K hN (xBs⁻¹)) =
      ggAutFixedSubgroup (K.normalizerMonoidHom
        ⟨x⁻¹, inv_mem (GGInnerDiagOn.le_normalizer hKmark hxBs)⟩) := by
    ext g
    rfl
  have hJcompK : IsComponentOf (J.subgroupOf K)
      (ggFix (H := ↥K) (ggGamma K hN (xBs⁻¹))) := by
    rw [hfixeq]
    exact GGResHyp.J_component_CK_of_original hH
  let JbarX : Subgroup Xbar := (J.subgroupOf K).map ((redMkL K).rangeRestrict)
  have hJbarcompX : IsComponentOf JbarX
      (ggFix (H := ↥Xbar) (ggGamma Xbar hNbar xbar)) := by
    have h := (SCFourCover.isComponentOf_map_iff hψsurj hψker hcompat
      (J := J.subgroupOf K) (Subgroup.isPerfect_iff.1 ⟨hJcompK.2.2.1⟩)).mp hJcompK
    simpa [JbarX] using h
  have hmap_sub : JbarK.subgroupOf Xbar =
      (J.subgroupOf K).map ((redMkL K).rangeRestrict) := by
    ext x
    constructor
    · intro hx
      rw [Subgroup.mem_subgroupOf] at hx
      obtain ⟨k, hk, hkx⟩ := hx
      exact ⟨k, hk, Subtype.ext hkx⟩
    · rintro ⟨k, hk, rfl⟩
      exact ⟨k, hk, rfl⟩
  have hJbarXeq : JbarX = JbarK.subgroupOf Xbar := hmap_sub.symm
  have hcompSub : IsComponentOf (Jbar.subgroupOf Xbar)
      (ggFix (H := ↥Xbar) (ggGamma Xbar hNbar xbar)) := by
    rw [← hJbarK_eq, ← hJbarXeq]
    exact hJbarcompX
  have hJbarq : CFSG.Assembly.IsQuasisimple ↥Jbar :=
    CFSG.Assembly.IsQuasisimple.of_mulEquiv
      (Subgroup.subgroupOfEquivOfLe hJbar_le_Xbar).symm hcompSub.2.2
  have hconj_mem : ∀ (c : ↥Bs) (g : RedGrp K), g ∈ Jbar →
      redMkB hN c * g * (redMkB hN c)⁻¹ ∈ Jbar := by
    intro c g hg
    obtain ⟨jN, hjN, rfl⟩ := hg
    change redMk K (Subgroup.inclusion hN c) * redMk K jN *
        (redMk K (Subgroup.inclusion hN c))⁻¹ ∈ Jbar
    simp only [← map_mul, ← map_inv]
    refine ⟨Subgroup.inclusion hN c * jN * (Subgroup.inclusion hN c)⁻¹, ?_, rfl⟩
    exact Subgroup.mem_subgroupOf.mpr
      ((Subgroup.mem_normalizer_iff.mp (hNJ c.2) (jN : G)).mp
        (Subgroup.mem_subgroupOf.mp hjN))
  have hNJbar : Bbar ≤ Subgroup.normalizer (Jbar : Set (RedGrp K)) := by
    rintro _ ⟨b, rfl⟩
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    apply le_antisymm
    · rintro _ ⟨x, hx, rfl⟩
      exact hconj_mem b x hx
    · intro y hy
      refine ⟨redMkB hN b⁻¹ * y * redMkB hN b, ?_, ?_⟩
      · simpa [map_inv] using hconj_mem b⁻¹ y hy
      · simp [MulAut.conj_apply, map_mul, map_inv]
        group
  obtain ⟨m, hm2, ψJ, hMJ, hdiagJ⟩ :=
    exists_unitaryModel_of_component_gamma hNbar hNJbar hJbar_le_Xbar hMQ hdiagQ xbar hcompSub
  have hm3 : 3 ≤ m := by
    by_contra hlt
    have hm1 : 1 ≤ m := by omega
    have hmle : m ≤ 2 := by omega
    haveI : Group.IsSolvable ↥(unitarySU 2 1 F m) :=
      WitSU.isSolvable_unitarySU_two_one hMQ.field hm1 (by omega)
    haveI : Group.IsSolvable ↥Jbar := Group.isSolvable_of_surjective hMJ.surj
    have hJbarqNat : CFSG.IsQuasisimple ↥Jbar :=
      (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native ↥Jbar).mp hJbarq
    exact not_isSolvable_of_isQuasisimple hJbarqNat inferInstance
  have hBsbar : IsElemAbelian 3 Bbar := isElemAbelian_redB hN hBs
  have hSCbar : ∀ g ∈ Subgroup.centralizer (Bbar : Set (RedGrp K)),
      g ^ 3 = 1 → g ∈ Bbar := redSC hN hBs hSC
  let eBs : ↥Bs ≃* ↥Bbar := MonoidHom.ofInjective (redMkB_injective hN hBs)
  have hJaut : ggAutomizer Jbar Bbar =
      (ggAutomizer J Bs).map (MulAut.congr eBs).toMonoidHom := by
    have h := ggAutomizer_redMk_eq hBs hN (hJX.trans Subgroup.le_normalizer) hNJ
    simpa [Jbar, Bbar, eBs] using h
  intro b hb
  let bbar : ↥Bbar := ⟨redMkB hN b, ⟨b, rfl⟩⟩
  have hfixbar : ∀ ψ ∈ ggAutomizer Jbar Bbar, ψ bbar = bbar := by
    intro ψ hψ
    rw [hJaut] at hψ
    obtain ⟨φ, hφ, rfl⟩ := hψ
    change (MulAut.congr eBs) φ bbar = bbar
    have hsymm : eBs.symm bbar = b := by
      apply eBs.injective
      rw [MulEquiv.apply_symm_apply]
      rfl
    change eBs (φ (eBs.symm bbar)) = bbar
    rw [hsymm, hb φ hφ]
    rfl
  have hcenbar : (bbar : RedGrp K) ∈
      Subgroup.centralizer (Jbar : Set (RedGrp K)) :=
    ggUnitaryModel_fix_mem_centralizer hNJbar hBsbar hSCbar hMJ hm3 hdiagJ bbar hfixbar
  letI : Group.IsPerfect ↥J := Group.isPerfect_def.mpr hJperf
  let bJ : ↥(Subgroup.normalizer (J : Set G)) := ⟨(b : G), hNJ b.2⟩
  let α : MulAut ↥J := J.normalizerMonoidHom bJ
  have hαcoe : ∀ jj : ↥J, ((α jj : ↥J) : G) =
      (b : G) * (jj : G) * (b : G)⁻¹ := by
    intro jj
    exact Subgroup.normalizerMonoidHom_apply_apply_coe J bJ jj
  have hcentral : ∀ jj : ↥J, jj⁻¹ * α jj ∈ Subgroup.center ↥J := by
    intro jj
    let bN : NX := ⟨(b : G), hN b.2⟩
    let jN : NX := ⟨(jj : G), hJX.trans Subgroup.le_normalizer jj.2⟩
    have hjbar : redMk K jN ∈ Jbar :=
      Subgroup.mem_map.mpr ⟨jN, Subgroup.mem_subgroupOf.mpr jj.2, rfl⟩
    have hcomm := (Subgroup.mem_centralizer_iff.mp hcenbar) (redMk K jN) hjbar
    have hbred : redMk K (jN⁻¹ * (bN * jN * bN⁻¹)) = 1 := by
      have hbN : redMk K bN = (bbar : RedGrp K) := rfl
      simp only [map_mul, map_inv, hbN]
      rw [← hcomm]
      group
    have hz : ((jN⁻¹ * (bN * jN * bN⁻¹) : NX) : G) ∈ twoCenter K :=
      (redMk_eq_one_iff K (jN⁻¹ * (bN * jN * bN⁻¹))).mp hbred
    rw [Subgroup.mem_center_iff]
    intro j'
    apply Subtype.ext
    have hzval : ((jj⁻¹ * α jj : ↥J) : G) =
        ((jN⁻¹ * (bN * jN * bN⁻¹) : NX) : G) := by
      rw [Subgroup.coe_mul, Subgroup.coe_inv, hαcoe]
      rfl
    change (j' : G) * ((jj⁻¹ * α jj : ↥J) : G) =
      ((jj⁻¹ * α jj : ↥J) : G) * (j' : G)
    rw [hzval]
    exact (hz.2.1 (j' : G) (hJX j'.2)).symm
  have hαone : α = 1 := by
    have h :=
      CFSG.ComponentClassification.PerfectAutomorphisms.hom_eq_id_of_central_displacement
        α.toMonoidHom hcentral
    have hpoint : ∀ jj : ↥J, α jj = (1 : MulAut ↥J) jj := by
      intro jj
      simpa using congrArg (fun f : ↥J →* ↥J => f jj) h
    exact MulEquiv.ext hpoint
  rw [Subgroup.mem_centralizer_iff]
  intro j hj
  have hαj : α ⟨j, hj⟩ = ⟨j, hj⟩ := by
    have := congrArg (fun f : MulAut ↥J => f ⟨j, hj⟩) hαone
    simpa using this
  have hval : (b : G) * (j : G) * (b : G)⁻¹ = (j : G) := by
    have h1 := congrArg (fun x : ↥J => (x : G)) hαj
    rw [hαcoe] at h1
    exact h1
  calc (j : G) * (b : G) = (b : G) * (j : G) * (b : G)⁻¹ * (b : G) := by rw [hval]
    _ = (b : G) * (j : G) := by group


theorem GGResHyp.not_exactThree_K_of_six_two_cell_B_eq_Bs
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp 3 B Bs x L D J y K)
    (hEq : B = Bs)
    (hcell : GGInnerDiagOnLabel
      (fun _ lab => lab.tag = .twA ∧ lab.rank = 5 ∧ lab.n = 1) 3 Bs K) :
    ¬ GGResLeviDatumExact3 3 Bs K J L ggSelAny ggTypAny := by
  intro h3
  obtain ⟨Λ, i1, i2, S, Λa, i3, i4, ML, CL, MK, CK, V, i5, i6, ι, φ, h, α,
    hS3, hA1, hA3, hWML, hCLL, hWMK, hCKK, htyp, hlin, hrefl, hpairL, hpairK, hsel,
    hfLx, hfKx, hclosL, hclosK, hdel, hclosJ⟩ := h3
  let := i1
  let := i2
  let := i3
  let := i4
  let := i5
  let := i6
  have hp2 : (3 : ℕ) ≠ 2 := by norm_num
  have hSHat : LargeEvenSHat 3 B y K := hH.2.2.2.2.1.1
  have hyBs : y ∈ Bs := hH.1.2.1.1 hSHat.2.1
  obtain ⟨v, hv, hvα⟩ := exists_root_kernel_of_centralizing hp2
    (fun i w => hlin (Sum.inl i) w) hpairL hCLL.1 hclosL
    hyBs hSHat.2.2.1 hSHat.2.2.2.1
  have haxis : Matrix.rank (CL.map (Int.castRingHom (ZMod 3))) + 1 ≤
      Module.finrank (ZMod 3) V :=
    ggResK_rank_core_add_one hH (fun i w => hlin (Sum.inl i) w) hpairL hCLL.1 hclosL
  have hfwd : ∀ b : ↥Bs, (∀ φ ∈ ggAutomizer J Bs, φ b = b) →
      (b : G) ∈ Subgroup.centralizer (J : Set G) :=
    GGResHyp.unitary_six_two_K_fix_mem_centralizer_noOdd hH hcell
  obtain ⟨-, -, -, -, hcent, hlt⟩ :=
    ggRes_exactThree_singular_chart_of_axis_bound hH.1 ι
      (fun i => φ (Sum.inl i)) (fun i => h (Sum.inl i)) (fun i => α (Sum.inl i))
      hWML hCLL (fun i w => hlin (Sum.inl i) w) (fun i => hrefl (Sum.inl i)) hpairL
      haxis S hS3 hclosJ hfwd
  rw [hEq] at hlt
  exact (lt_irrefl Bs) hlt


theorem GGResHyp.not_exactThree_K_of_six_two_cell
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp 3 B Bs x L D J y K)
    (hcell : GGInnerDiagOnLabel
      (fun _ lab => lab.tag = .twA ∧ lab.rank = 5 ∧ lab.n = 1) 3 Bs K) :
    ¬ GGResLeviDatumExact3 3 Bs K J L ggSelAny ggTypAny := by
  by_cases hEq : B = Bs
  · exact GGResHyp.not_exactThree_K_of_six_two_cell_B_eq_Bs hH hEq hcell
  · exact GGResHyp.not_exactThree_K_of_six_two_cell_B_lt_Bs hH
      (lt_of_le_of_ne hH.1.2.1.1 hEq) hcell

theorem GGResHyp.exists_unitaryModel_K_of_label_qGeFour
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K)
    (hU : GGInnerDiagOnLabel
      (fun p lab => lab.tag = .twA ∧ 4 ≤ lab.rank ∧ 2 ≤ lab.n ∧
        p ∣ 2 ^ lab.n + 1) p Bs K)
    (hN : Bs ≤ Subgroup.normalizer (K : Set G)) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (n d : ℕ)
      (θ : ↥K ⧸ Subgroup.center ↥K ≃* LargeEvenProj (unitarySU 2 n F d))
      (ψ : ↥(unitarySU 2 n F d) →* ↥K),
      2 ≤ n ∧ 5 ≤ d ∧ p ∣ 2 ^ n + 1 ∧ UnitTB.Model ψ ∧
        ∀ a ∈ (ggGamma K hN).range, ∃ t : Fin d → F, ActsDiagU ψ a t := by
  classical
  unfold GGInnerDiagOnLabel at hU
  obtain ⟨hperf, lab, hΛ, hraw⟩ := hU
  obtain ⟨R₀, iR₀, I₀, F₀, hQ₀⟩ := largeEvenRawDatum_exists hraw
  obtain ⟨-, -, θ₀, hP₀⟩ := hQ₀
  dsimp only at hP₀
  obtain ⟨⟨htag, hr4, hn2, hpq⟩, hN₀, hact₀⟩ := hP₀
  obtain ⟨tag, rank, n⟩ := lab
  change tag = .twA at htag
  change 4 ≤ rank at hr4
  change 2 ≤ n at hn2
  change p ∣ 2 ^ n + 1 at hpq
  subst tag
  dsimp only [LargeEvenRawDatumLegacy] at hraw
  obtain ⟨F, hField, hFinite, hFK, hQ⟩ := hraw
  letI : Field F := hField
  letI : Finite F := hFinite
  obtain ⟨hSimple, hNonAb, θ, hP⟩ := hQ
  obtain ⟨hlabel, hN', hact⟩ := hP
  have hd : 5 ≤ rank + 1 := by omega
  by_cases h63 : ¬ (rank + 1 = 6 ∧ p = 3)
  · obtain ⟨ψ, hM, hdiag⟩ :=
      GGResHyp.exists_unitaryModel_K_of_marking_data hH hFK (by omega : 1 ≤ n) hd hpq h63 θ hN hact
    exact ⟨F, hField, hFinite, n, rank + 1, θ, ψ, hn2, hd, hpq, hM, hdiag⟩
  · push Not at h63
    obtain ⟨hr6, hp3⟩ := h63
    have hrank5 : rank = 5 := by omega
    subst rank
    have hU63 : GGInnerDiagOnLabel GGNbrInner937U63Label p Bs K := by
      refine ⟨hperf, ⟨.twA, 5, n⟩, hΛ, ?_⟩
      dsimp only [CFSG.Assembly.LargeEvenRawDatumLegacy]
      refine ⟨F, hField, hFinite, hFK, ?_⟩
      exact ⟨hSimple, hNonAb, θ, ⟨⟨⟨rfl, by norm_num, hpq, by rw [hp3]; norm_num⟩, by norm_num, hp3⟩, hN', hact⟩⟩
    have hγ : 3 ^ 4 ≤ Nat.card (ggGamma K hN).range :=
      GGResHyp.gamma_four_of_unitary_six_two_K_original hH hN hp3 hU63
    have hH3 : GGResHyp 3 B Bs x L D J y K := by simpa [hp3] using hH
    obtain ⟨ψ, hM, hdiag⟩ :=
      GGResHyp.exists_unitaryModel_K_six_three_qGeFour_of_gamma hH3
        (by simpa using hFK : Nat.card F = (2 ^ n) ^ 2) hn2
        (by simpa [hp3] using hpq) θ hN hact hγ
    exact ⟨F, hField, hFinite, n, 6, θ, ψ, hn2, by norm_num, hpq, hM, hdiag⟩

theorem GGResHyp.not_exactThree_K_of_iOne_qGeFour
    (hLB : GGLBalanceInput)
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K)
    (hI : Bs ⊓ Subgroup.centralizer (J : Set G) = D)
    (hU : GGInnerDiagOnLabel
      (fun p lab => lab.tag = .twA ∧ 4 ≤ lab.rank ∧ 2 ≤ lab.n ∧
        p ∣ 2 ^ lab.n + 1) p Bs K) :
    ¬ GGResLeviDatumExact3 p Bs K J L ggSelAny ggTypAny := by
  intro h3
  have hN := (hH.2.2.1.2 y K hH.2.2.2.2.1).le_normalizer
  obtain ⟨F, hField, hFinite, n, d, θ, ψ, hn2, hd, hpq, hM, hdiag⟩ :=
    hH.exists_unitaryModel_K_of_label_qGeFour hU hN
  obtain ⟨r, hd_eq, hpd, hXD, hcardBs, hcardJ, hBlt, hAut⟩ :=
    hH.unitary_exactThree_typeA_card_J_of_K hLB hM hpq hd hdiag h3
  exact (hH.iOne_iff_card_ne_p3.mp hI) hcardJ

theorem GGResHyp.not_exactThree_K_of_linear_split_L_qGeFour
    (hLB : GGLBalanceInput)
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {y : G} {K : Subgroup G} (hH : GGResHyp p B Bs x L D J y K)
    (hL : GGInnerDiagOnLabel
      (fun _ lab => lab.tag = .A ∧ p ∣ 2 ^ lab.n - 1) p Bs L)
    (hU : GGInnerDiagOnLabel
      (fun p lab => lab.tag = .twA ∧ 4 ≤ lab.rank ∧ 2 ≤ lab.n ∧
        p ∣ 2 ^ lab.n + 1) p Bs K) :
    ¬ GGResLeviDatumExact3 p Bs K J L ggSelAny ggTypAny :=
  hH.not_exactThree_K_of_iOne_qGeFour hLB
    (hH.iOne_of_rootTwo (hH.rootTwo_of_large_linear_L_marking hL)) hU

theorem GGResHyp.not_exactThree_K_of_B_eq_Bs_qGeFour
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K) (hEq : B = Bs)
    (hU : GGInnerDiagOnLabel
      (fun p lab => lab.tag = .twA ∧ 4 ≤ lab.rank ∧ 2 ≤ lab.n ∧
        p ∣ 2 ^ lab.n + 1) p Bs K) :
    ¬ GGResLeviDatumExact3 p Bs K J L ggSelAny ggTypAny := by
  intro h3
  have hN := (hH.2.2.1.2 y K hH.2.2.2.2.1).le_normalizer
  obtain ⟨F, hField, hFinite, n, d, θ, ψ, hn2, hd, hpq, hM, hdiag⟩ :=
    hH.exists_unitaryModel_K_of_label_qGeFour hU hN
  have hLB : GGLBalanceInput := ggGammaSuppliers_proved.1
  obtain ⟨r, hd_eq, hpd, hXD, hcardBs, hcardJ, hBlt, hAut⟩ :=
    hH.unitary_exactThree_typeA_card_J_of_K hLB hM hpq hd hdiag h3
  have hBlt' : Bs < Bs := by simpa [hEq] using hBlt
  exact lt_irrefl Bs hBlt'

theorem GGResHyp.not_exactThree_K_of_spPlus_L_qGeFour
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K)
    (hL : GGInnerDiagOnLabel ggTBJSpPlusLabel p Bs L)
    (hU : GGInnerDiagOnLabel
      (fun p lab => lab.tag = .twA ∧ 4 ≤ lab.rank ∧ 2 ≤ lab.n ∧
        p ∣ 2 ^ lab.n + 1) p Bs K) :
    ¬ GGResLeviDatumExact3 p Bs K J L ggSelAny ggTypAny :=
  hH.not_exactThree_K_of_B_eq_Bs_qGeFour (hH.bstar_eq_of_spPlus_L hL) hU

theorem GGResHyp.not_exactThree_K_of_spSplit_three_L_qGeFour
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K)
    (hL : GGInnerDiagOnLabel (fun p lab =>
      (lab.tag = .B ∨ lab.tag = .C) ∧ lab.rank = 3 ∧ p ∣ 2 ^ lab.n - 1) p Bs L)
    (hU : GGInnerDiagOnLabel
      (fun p lab => lab.tag = .twA ∧ 4 ≤ lab.rank ∧ 2 ≤ lab.n ∧
        p ∣ 2 ^ lab.n + 1) p Bs K) :
    ¬ GGResLeviDatumExact3 p Bs K J L ggSelAny ggTypAny :=
  hH.not_exactThree_K_of_B_eq_Bs_qGeFour
    (hH.bstar_eq_of_spSplit_three_L hL) hU

theorem GGResHyp.not_exactThree_K_of_excSplit_L_qGeFour
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K)
    (hL : GGInnerDiagOnLabel GGExcLSplitLabel p Bs L)
    (hU : GGInnerDiagOnLabel
      (fun p lab => lab.tag = .twA ∧ 4 ≤ lab.rank ∧ 2 ≤ lab.n ∧
        p ∣ 2 ^ lab.n + 1) p Bs K) :
    ¬ GGResLeviDatumExact3 p Bs K J L ggSelAny ggTypAny :=
  hH.not_exactThree_K_of_B_eq_Bs_qGeFour
    (hH.bstar_eq_of_excLSplit (Fact.out : p.Prime) hL) hU

theorem GGResHyp.not_exactThree_K_of_original_L_marking_qGeFour
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K)
    (hL : (∃ r f : ℕ, p ∣ 2 ^ f + 1 ∧
      GGInnerDiagOnLabel (fun _ lab => lab = ⟨.A, r, f⟩) p Bs L) ∨
      GGInnerDiagOnLabel (fun _ lab => lab.tag = .E6 ∧ p ∣ 2 ^ lab.n - 1) p Bs L)
    (hU : GGInnerDiagOnLabel
      (fun p lab => lab.tag = .twA ∧ 4 ≤ lab.rank ∧ 2 ≤ lab.n ∧
        p ∣ 2 ^ lab.n + 1) p Bs K)
    (hN : Bs ≤ Subgroup.normalizer (K : Set G)) :
    ¬ GGResLeviDatumExact3 p Bs K J L ggSelAny ggTypAny := by
  have hBs : B = Bs := by
    rcases hL with ⟨r, f, hpq, hmarkA⟩ | hmarkE6
    · exact (hH.bstar_eq_of_linMinus_side (Or.inl rfl) hpq hmarkA).symm
    · exact hH.bstar_eq_of_splitE6_all Fact.out hmarkE6
  exact hH.not_exactThree_K_of_B_eq_Bs_qGeFour hBs hU

theorem GGResHyp.bstar_eq_of_orthogonal_split_L
    {G : Type} [Group G] [Finite G] {p : ℕ}
    {B Bs L D J K : Subgroup G} {x y : G}
    (hH : GGResHyp p B Bs x L D J y K)
    (hM : GGInnerDiagOnLabel GGCorFourTwoOrthSplitLabel p Bs L) :
    B = Bs := by
  obtain ⟨-, -, -, -, -, hβ, -, -⟩ := hH.1.1
  have hp : p.Prime := hβ.1
  have hM' := largeEvenMarking_and_labelAll
    (S := GGCorFourTwoOrthSplitLabel p)
    (P' := fun R _ I _ => ∃ r, GGTorusLift p r R ∧ GGIRankLe p r R I)
    (hall := fun lab hΛ hs => IOneRest.largeEvenLabelAll_iRank_orthSplit (p := p) hp hΛ hs)
    (hS := fun lab R _ I F θ hP => hP.1)
    hM
  obtain ⟨hL, lab, -, hraw⟩ := hM'
  obtain ⟨R, _, I, F, -, -, θ, ⟨⟨-, hBN, h3⟩, hr⟩⟩ := largeEvenRawDatum_exists hraw
  obtain ⟨r, hlift, hrank⟩ := hr
  exact bstar_eq_of_inner_rank hH.1.1 hH.1.2.1
    (ggLNoncyclicInput_holds G p B x L hH.1.1) hL θ
    (hH.1.2.1.1.trans hBN) h3 hlift hrank


theorem GGResHyp.not_exactThree_K_of_orthogonal_split_L_qGeFour
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K)
    (hL : GGInnerDiagOnLabel GGCorFourTwoOrthSplitLabel p Bs L)
    (hU : GGInnerDiagOnLabel
      (fun p lab => lab.tag = .twA ∧ 4 ≤ lab.rank ∧ 2 ≤ lab.n ∧
        p ∣ 2 ^ lab.n + 1) p Bs K) :
    ¬ GGResLeviDatumExact3 p Bs K J L ggSelAny ggTypAny :=
  hH.not_exactThree_K_of_B_eq_Bs_qGeFour (hH.bstar_eq_of_orthogonal_split_L hL) hU

theorem GGResHyp.bstar_eq_of_orthogonal_minus_even_L
    {G : Type} [Group G] [Finite G] {p : ℕ}
    {B Bs L D J K : Subgroup G} {x y : G}
    (hH : GGResHyp p B Bs x L D J y K)
    (hM : GGInnerDiagOnLabel
      (fun p lab => lab.tag = .twD ∧ 4 ≤ lab.rank ∧ Even lab.rank ∧
        p ∣ 2 ^ lab.n + 1) p Bs L) :
    B = Bs := by
  obtain ⟨-, -, -, -, -, hβ, -, -⟩ := hH.1.1
  have hp : p.Prime := hβ.1
  have hM' := largeEvenMarking_and_labelAll
    (S := fun lab => lab.tag = .twD ∧ 4 ≤ lab.rank ∧ Even lab.rank ∧
      p ∣ 2 ^ lab.n + 1)
    (P' := fun R _ I _ => ∃ r, GGTorusLift p r R ∧ GGIRankLe p r R I)
    (hall := fun lab hΛ hs =>
      largeEvenLabelAll_iRank_orthMinus_even_nonsplit (p := p) hp hΛ hs)
    (hS := fun lab R _ I F θ hP => hP.1)
    hM
  obtain ⟨hL, lab, -, hraw⟩ := hM'
  obtain ⟨R, _, I, F, -, -, θ, ⟨⟨-, hBN, h3⟩, hr⟩⟩ := largeEvenRawDatum_exists hraw
  obtain ⟨r, hlift, hrank⟩ := hr
  exact bstar_eq_of_inner_rank hH.1.1 hH.1.2.1
    (ggLNoncyclicInput_holds G p B x L hH.1.1) hL θ
    (hH.1.2.1.1.trans hBN) h3 hlift hrank

theorem GGResHyp.not_exactThree_K_of_orthogonal_minus_even_L_qGeFour
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K)
    (hL : GGInnerDiagOnLabel
      (fun p lab => lab.tag = .twD ∧ 4 ≤ lab.rank ∧ Even lab.rank ∧
        p ∣ 2 ^ lab.n + 1) p Bs L)
    (hU : GGInnerDiagOnLabel
      (fun p lab => lab.tag = .twA ∧ 4 ≤ lab.rank ∧ 2 ≤ lab.n ∧
        p ∣ 2 ^ lab.n + 1) p Bs K) :
    ¬ GGResLeviDatumExact3 p Bs K J L ggSelAny ggTypAny :=
  hH.not_exactThree_K_of_B_eq_Bs_qGeFour (hH.bstar_eq_of_orthogonal_minus_even_L hL) hU

theorem GGResHyp.centralizer_J_eq_D_of_B_eq_Bs
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K) (hEq : B = Bs) :
    Bs ⊓ Subgroup.centralizer (J : Set G) = D :=
  GGResHyp.iOne_of_eq_bstar hH hEq

theorem GGResHyp.card_centralizer_J_eq_nine_of_B_eq_Bs
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp 3 B Bs x L D J y K) (hEq : B = Bs) :
    Nat.card ↥(Bs ⊓ Subgroup.centralizer (J : Set G)) = 9 := by
  have h := GGResHyp.centralizer_J_eq_D_of_B_eq_Bs hH hEq
  have hD : Nat.card ↥D = 3 ^ 2 := hH.1.2.2.1.2.2.1
  rw [h, hD]
  norm_num

theorem GGResHyp.card_centralizer_K_le_nine_of_B_eq_Bs
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp 3 B Bs x L D J y K) (hEq : B = Bs) :
    Nat.card ↥(Bs ⊓ Subgroup.centralizer (K : Set G)) ≤ 9 := by
  have hJK : J ≤ K := GGResHyp.J_le_K_of_original hH
  have hle : Bs ⊓ Subgroup.centralizer (K : Set G) ≤
      Bs ⊓ Subgroup.centralizer (J : Set G) :=
    inf_le_inf_left Bs (Subgroup.centralizer_le hJK)
  have hcard := Subgroup.card_le_of_le hle
  rw [GGResHyp.card_centralizer_J_eq_nine_of_B_eq_Bs hH hEq] at hcard
  exact hcard


theorem GGResHyp.six_two_cell_centralizer_or_no_exactThree
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp 3 B Bs x L D J y K)
    (hcell : GGInnerDiagOnLabel
      (fun _ lab => lab.tag = .twA ∧ lab.rank = 5 ∧ lab.n = 1) 3 Bs K) :
    (B = Bs ∧ Nat.card ↥(Bs ⊓ Subgroup.centralizer (J : Set G)) = 9) ∨
      (B < Bs ∧ ¬ GGResLeviDatumExact3 3 Bs K J L ggSelAny ggTypAny) := by
  by_cases hEq : B = Bs
  · exact Or.inl ⟨hEq, GGResHyp.card_centralizer_J_eq_nine_of_B_eq_Bs hH hEq⟩
  · exact Or.inr ⟨lt_of_le_of_ne hH.1.2.1.1 hEq,
      GGResHyp.not_exactThree_K_of_six_two_cell_B_lt_Bs hH
        (lt_of_le_of_ne hH.1.2.1.1 hEq) hcell⟩


theorem GGResHyp.not_exactThree_K_of_qTwo_highrank
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K)
    (hU : GGInnerDiagOnLabel
      (fun p lab => lab.tag = .twA ∧ 4 ≤ lab.rank ∧ lab.n = 1 ∧
        p ∣ 2 ^ lab.n + 1) p Bs K)
    (hNoRow : ¬ GGResRowAt ggRowSUCorank3 p J K) :
    ¬ GGResLeviDatumExact3 p Bs K J L ggSelAny ggTypAny := by
  classical
  obtain ⟨hperf, lab, hΛ, hraw⟩ := hU
  obtain ⟨R₀, iR₀, I₀, F₀, hQ₀⟩ := largeEvenRawDatum_exists hraw
  obtain ⟨-, -, θ₀, hP₀⟩ := hQ₀
  dsimp only at hP₀
  obtain ⟨⟨htag, hr4, hn1, hpq⟩, hN₀, hact₀⟩ := hP₀
  obtain ⟨tag, rank, n⟩ := lab
  change tag = .twA at htag
  change 4 ≤ rank at hr4
  change n = 1 at hn1
  change p ∣ 2 ^ n + 1 at hpq
  subst tag
  have hp3 : p = 3 := by
    exact (Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) Nat.prime_three).mp
      (by simpa [hn1] using hpq)
  by_cases hrank5 : rank = 5
  · have hcell : GGInnerDiagOnLabel
        (fun _ lab => lab.tag = .twA ∧ lab.rank = 5 ∧ lab.n = 1) p Bs K := by
      refine ⟨hperf, ⟨.twA, rank, n⟩, hΛ, ?_⟩
      dsimp only [LargeEvenRawDatumLegacy, LargeEvenRecipeUnitary] at hraw ⊢
      obtain ⟨K', hField', hFinite', hFK', hQ'⟩ := hraw
      obtain ⟨hSimple', hNonab', θ', hP'⟩ := hQ'
      obtain ⟨hs, hN', hact'⟩ := hP'
      exact ⟨K', hField', hFinite', hFK', hSimple', hNonab', θ',
        ⟨⟨hs.1, hrank5, hs.2.2.1⟩, hN', hact'⟩⟩
    have hcell3 : GGInnerDiagOnLabel
        (fun _ lab => lab.tag = .twA ∧ lab.rank = 5 ∧ lab.n = 1) 3 Bs K := by
      simpa [hp3] using hcell
    have hH3 : GGResHyp 3 B Bs x L D J y K := by
      simpa [hp3] using hH
    simpa [hp3] using GGResHyp.not_exactThree_K_of_six_two_cell hH3 hcell3
  · have hU' : GGInnerDiagOnLabel
        (fun p lab => lab.tag = .twA ∧ lab.rank = rank ∧ lab.n = 1 ∧
          p ∣ 2 ^ lab.n + 1) p Bs K := by
      refine ⟨hperf, ⟨.twA, rank, n⟩, hΛ, ?_⟩
      dsimp only [LargeEvenRawDatumLegacy, LargeEvenRecipeUnitary] at hraw ⊢
      obtain ⟨K', hField', hFinite', hFK', hQ'⟩ := hraw
      obtain ⟨hSimple', hNonab', θ', hP'⟩ := hQ'
      obtain ⟨hs, hN', hact'⟩ := hP'
      exact ⟨K', hField', hFinite', hFK', hSimple', hNonab', θ',
        ⟨⟨hs.1, rfl, hs.2.2.1, hs.2.2.2⟩, hN', hact'⟩⟩
    obtain ⟨F, hField, hFinite, ψ, hM, hdiag⟩ :=
      GGResHyp.exists_unitaryModel_K_qTwo_of_marking_rank hH hU' hr4 hrank5
    intro h3
    apply hNoRow
    have hLB : GGLBalanceInput := ggGammaSuppliers_proved.1
    exact hH.unitary_exactThree_reserved_row_qTwo_of_K hLB hM
      (by simpa [hn1] using hpq) (by omega : 5 ≤ rank + 1) hdiag h3
theorem GGResHyp.exists_unitaryModel_K_of_label_qGeFour_literal_of_selector
    (S : ℕ → LargeEvenLabel → Prop)
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K)
    (hU : GGInnerDiagOnLabel
      (fun p lab => S p lab ∧ lab.tag = .twA ∧ 4 ≤ lab.rank ∧ 2 ≤ lab.n ∧
        p ∣ 2 ^ lab.n + 1) p Bs K)
    (hN : Bs ≤ Subgroup.normalizer (K : Set G)) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (n rank d : ℕ)
      (θ : ↥K ⧸ Subgroup.center ↥K ≃* LargeEvenProj (unitarySU 2 n F d))
      (ψ : ↥(unitarySU 2 n F d) →* ↥K),
      4 ≤ rank ∧ 2 ≤ n ∧ 5 ≤ d ∧ d = rank + 1 ∧ Nat.card F = (2 ^ n) ^ 2 ∧
        p ∣ 2 ^ n + 1 ∧ UnitTB.Model ψ ∧
          (∀ a ∈ (ggGamma K hN).range, ∃ t : Fin d → F, ActsDiagU ψ a t) ∧
          S p ⟨.twA, rank, n⟩ := by
  classical
  unfold GGInnerDiagOnLabel at hU
  obtain ⟨hperf, lab, hΛ, hraw⟩ := hU
  obtain ⟨R₀, iR₀, I₀, F₀, hQ₀⟩ := largeEvenRawDatum_exists hraw
  obtain ⟨-, -, θ₀, hP₀⟩ := hQ₀
  dsimp only at hP₀
  obtain ⟨⟨hS, htag, hr4, hn2, hpq⟩, hN₀, hact₀⟩ := hP₀
  obtain ⟨tag, rank, n⟩ := lab
  change tag = .twA at htag
  change 4 ≤ rank at hr4
  change 2 ≤ n at hn2
  change p ∣ 2 ^ n + 1 at hpq
  change S p ⟨tag, rank, n⟩ at hS
  subst tag
  dsimp only [LargeEvenRawDatumLegacy] at hraw
  obtain ⟨F, hField, hFinite, hFK, hQ⟩ := hraw
  letI : Field F := hField
  letI : Finite F := hFinite
  obtain ⟨hSimple, hNonAb, θ, hP⟩ := hQ
  obtain ⟨hlabel, hN', hact⟩ := hP
  have hd : 5 ≤ rank + 1 := by omega
  by_cases h63 : ¬ (rank + 1 = 6 ∧ p = 3)
  · obtain ⟨ψ, hM, hdiag⟩ :=
      GGResHyp.exists_unitaryModel_K_of_marking_data hH hFK (by omega : 1 ≤ n) hd hpq h63 θ hN hact
    exact ⟨F, hField, hFinite, n, rank, rank + 1, θ, ψ,
      hr4, hn2, hd, rfl, hFK, hpq, hM, hdiag, hS⟩
  · push Not at h63
    obtain ⟨hr6, hp3⟩ := h63
    have hrank5 : rank = 5 := by omega
    subst rank
    have hU63 : GGInnerDiagOnLabel GGNbrInner937U63Label p Bs K := by
      refine ⟨hperf, ⟨.twA, 5, n⟩, hΛ, ?_⟩
      dsimp only [CFSG.Assembly.LargeEvenRawDatumLegacy]
      refine ⟨F, hField, hFinite, hFK, ?_⟩
      exact ⟨hSimple, hNonAb, θ, ⟨⟨⟨rfl, by norm_num, hpq, by rw [hp3]; norm_num⟩, by norm_num, hp3⟩, hN', hact⟩⟩
    have hγ : 3 ^ 4 ≤ Nat.card (ggGamma K hN).range :=
      GGResHyp.gamma_four_of_unitary_six_two_K_original hH hN hp3 hU63
    have hH3 : GGResHyp 3 B Bs x L D J y K := by simpa [hp3] using hH
    obtain ⟨ψ, hM, hdiag⟩ :=
      GGResHyp.exists_unitaryModel_K_six_three_qGeFour_of_gamma hH3
        (by simpa using hFK : Nat.card F = (2 ^ n) ^ 2) hn2
        (by simpa [hp3] using hpq) θ hN hact hγ
    exact ⟨F, hField, hFinite, n, 5, 6, θ, ψ,
      by norm_num, hn2, by norm_num, by norm_num, hFK, hpq, hM, hdiag, hS⟩

theorem GGResHyp.exists_unitaryModel_K_of_label_qGeFour_literal
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K)
    (hU : GGInnerDiagOnLabel
      (fun p lab => lab.tag = .twA ∧ 4 ≤ lab.rank ∧ 2 ≤ lab.n ∧
        p ∣ 2 ^ lab.n + 1) p Bs K)
    (hN : Bs ≤ Subgroup.normalizer (K : Set G)) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (n rank d : ℕ)
      (θ : ↥K ⧸ Subgroup.center ↥K ≃* LargeEvenProj (unitarySU 2 n F d))
      (ψ : ↥(unitarySU 2 n F d) →* ↥K),
      4 ≤ rank ∧ 2 ≤ n ∧ 5 ≤ d ∧ d = rank + 1 ∧ Nat.card F = (2 ^ n) ^ 2 ∧
        p ∣ 2 ^ n + 1 ∧ UnitTB.Model ψ ∧
          ∀ a ∈ (ggGamma K hN).range, ∃ t : Fin d → F, ActsDiagU ψ a t := by
  obtain ⟨F, hField, hFinite, n, rank, d, θ, ψ,
    hr4, hn2, hd, hd_eq, hFK, hpq, hM, hdiag, -⟩ :=
    hH.exists_unitaryModel_K_of_label_qGeFour_literal_of_selector
      (S := fun _ _ => True) (by simpa using hU) hN
  exact ⟨F, hField, hFinite, n, rank, d, θ, ψ,
    hr4, hn2, hd, hd_eq, hFK, hpq, hM, hdiag⟩

theorem GGResHyp.rankFiveK3_original_facts
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K)
    (hU : GGInnerDiagOnLabel
      (fun p lab => lab.tag = .twA ∧ lab.rank = 5 ∧ 2 ≤ lab.n ∧
        p ∣ 2 ^ lab.n + 1) p Bs K)
    (h3 : GGResLeviDatumExact3 p Bs K J L ggSelAny ggTypAny) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (n : ℕ)
      (θK : ↥K ⧸ Subgroup.center ↥K ≃* LargeEvenProj (unitarySU 2 n F 6))
      (ψK : ↥(unitarySU 2 n F 6) →* ↥K)
      (δ : ↥(unitarySU 2 n F 3) →* ↥J),
      Nat.card F = (2 ^ n) ^ 2 ∧
        UnitTB.Model ψK ∧
        (∀ a ∈ (ggGamma K (hH.2.2.1.2 y K hH.2.2.2.2.1).le_normalizer).range,
          ∃ t : Fin 6 → F, LineU.ActsDiagU ψK a t) ∧
        UnitTB.Model δ ∧
        (∀ a ∈ (ggGamma J hH.Bs_le_normalizer_J).range,
          ∃ t : Fin 3 → F, LineU.ActsDiagU δ a t) ∧
        p = 3 ∧ Odd n ∧ 3 ≤ n ∧ p ∣ 2 ^ n + 1 ∧
        Nat.card Bs = 3 ^ 5 ∧
        Nat.card ↥(Bs ⊓ Subgroup.centralizer (J : Set G)) = 3 ^ 3 ∧
        Nat.card (ggAutomizer J Bs) = 6 ∧ B < Bs := by
  classical
  have hN : Bs ≤ Subgroup.normalizer (K : Set G) :=
    (hH.2.2.1.2 y K hH.2.2.2.2.1).le_normalizer
  have hU5 : GGInnerDiagOnLabel
      (fun p lab => lab.rank = 5 ∧ lab.tag = .twA ∧ 4 ≤ lab.rank ∧ 2 ≤ lab.n ∧
        p ∣ 2 ^ lab.n + 1) p Bs K :=
    GGInnerDiagOnLabel.mono_label (fun lab h => by
      obtain ⟨htag, hr5, hn2, hpq⟩ := h
      exact ⟨hr5, htag, by omega, hn2, hpq⟩) hU
  obtain ⟨F, hField, hFinite, n, rank, d, θK, ψK,
    -, hn2, -, hd_eq, hFK, hpq, hM, hdiag, hRank5⟩ :=
    hH.exists_unitaryModel_K_of_label_qGeFour_literal_of_selector
      (S := fun _ lab => lab.rank = 5) hU5 hN
  have hRank5' : rank = 5 := by simpa using hRank5
  have hd6 : d = 6 := by omega
  cases hd6
  have hLB : GGLBalanceInput := ggGammaSuppliers_proved.1
  obtain ⟨r, hdr, hpd6, -, hcardBs, hcardJ, hBlt, hAJ⟩ :=
    hH.unitary_exactThree_typeA_card_J_of_K hLB hM hpq (by norm_num) hdiag h3
  have hp2 : p ≠ 2 := hH.1.1.2.2.2.2.2.1.2.1
  have hp3 : p = 3 := by
    have hdiv : p ∣ 6 := by simpa using hpd6
    have h23 : p ∣ 2 * 3 := by simpa using hdiv
    rcases (Fact.out : p.Prime).dvd_mul.mp h23 with h2 | h3
    · exact (hp2 ((Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime)
        Nat.prime_two).mp h2)).elim
    · exact (Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) Nat.prime_three).mp h3
  obtain ⟨-, δ, hδM, hδdiag⟩ :=
    hH.unitary_exactThree_J_model_three_of_K hLB hM hpq hdiag h3
  have hr : r = 5 := by omega
  have hBs : Nat.card Bs = 3 ^ 5 := by
    simpa [hcardBs, hr, hp3]
  have hJ : Nat.card ↥(Bs ⊓ Subgroup.centralizer (J : Set G)) = 3 ^ 3 := by
    rw [hcardJ]
    rw [hp3]
  have hAJ6 : Nat.card (ggAutomizer J Bs) = 6 := by
    rw [hAJ, hr]
    norm_num
  have hnodd : Odd n :=
    CFSG.RankThree.PartTwo.Census.odd_of_three_dvd_two_pow_add_one
      (by simpa [hp3] using hpq)
  have hn3 : 3 ≤ n := by
    by_contra h
    have hn2' : n = 2 := by omega
    subst hn2'
    obtain ⟨k, hk⟩ := hnodd
    omega
  exact ⟨F, hField, hFinite, n, θK, ψK, δ, hFK, hM, hdiag, hδM, hδdiag,
    hp3, hnodd, hn3, hpq, hBs, hJ, hAJ6, hBlt⟩

theorem GGResHyp.rankFiveK3_line
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K)
    (hU : GGInnerDiagOnLabel
      (fun p lab => lab.tag = .twA ∧ lab.rank = 5 ∧ 2 ≤ lab.n ∧
        p ∣ 2 ^ lab.n + 1) p Bs K)
    (h3 : GGResLeviDatumExact3 p Bs K J L ggSelAny ggTypAny) :
    GGResLineJDatum 3 Bs J .A2 := by
  obtain ⟨F, hField, hFinite, n, θK, ψK, δ,
    hFK, hM, hdiag, hδM, hδdiag, hp3, hnodd, hn3, hpq, hBs, hJ, hAJ6, hBlt⟩ :=
    hH.rankFiveK3_original_facts hU h3
  have hLB : GGLBalanceInput := ggGammaSuppliers_proved.1
  obtain ⟨r, hdr, hpd6, hXD, hcardBs, hcardJ, hBlt', hAJ⟩ :=
    hH.unitary_exactThree_typeA_card_J_of_K hLB hM hpq (by norm_num) hdiag h3
  have hr : r = 5 := by omega
  have hcardK : Nat.card ↥(ggAutomizer K Bs) = 720 := by
    have h := hXD.card_automizer
    rw [hr] at h
    norm_num at h
    exact h
  have hH3 : GGResHyp 3 B Bs x L D J y K := by simpa [hp3] using hH
  have h33 : GGResLeviDatumExact3 3 Bs K J L ggSelAny ggTypAny := by simpa [hp3] using h3
  exact hH3.exactThree_A2_line_of_rankFive h33 hcardK hAJ6

theorem GGResHyp.not_exactThree_K_of_unitary_rank_four_qGeFour
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K)
    (hU : GGInnerDiagOnLabel
      (fun p lab => lab.tag = .twA ∧ lab.rank = 4 ∧ 2 ≤ lab.n ∧
        p ∣ 2 ^ lab.n + 1) p Bs K) :
    ¬ GGResLeviDatumExact3 p Bs K J L ggSelAny ggTypAny := by
  intro h3
  unfold GGInnerDiagOnLabel at hU
  obtain ⟨hperf, lab, hΛ, hraw⟩ := hU
  obtain ⟨R₀, iR₀, I₀, F₀, hQ₀⟩ := largeEvenRawDatum_exists hraw
  obtain ⟨-, -, θ₀, hP₀⟩ := hQ₀
  dsimp only at hP₀
  obtain ⟨⟨htag, hrank4, hn2, hpq⟩, hN₀, hact₀⟩ := hP₀
  obtain ⟨tag, rank, n⟩ := lab
  change tag = .twA at htag
  change rank = 4 at hrank4
  change 2 ≤ n at hn2
  change p ∣ 2 ^ n + 1 at hpq
  subst tag
  subst rank
  dsimp only [LargeEvenRawDatumLegacy] at hraw
  obtain ⟨F, hField, hFinite, hFK, hQ⟩ := hraw
  letI : Field F := hField
  letI : Finite F := hFinite
  obtain ⟨hSimple, hNonAb, θ, hP⟩ := hQ
  obtain ⟨hlabel, hN', hact⟩ := hP
  have hn1 : 1 ≤ n := by omega
  have hd5 : 5 ≤ 5 := by norm_num
  have h63 : ¬ (5 = 6 ∧ p = 3) := by norm_num
  let hN : Bs ≤ Subgroup.normalizer (K : Set G) :=
    (hH.2.2.1.2 y K hH.2.2.2.2.1).le_normalizer
  obtain ⟨ψ, hM, hdiag⟩ :=
    GGResHyp.exists_unitaryModel_K_of_marking_data hH hFK hn1 hd5 hpq h63 θ hN hact
  have hLB : GGLBalanceInput := ggGammaSuppliers_proved.1
  exact GGResHyp.not_exactThree_K_of_unitaryModel_degree_five hLB hH hM hpq hdiag h3

end GammaCert

end CFSG.StandardType

end
