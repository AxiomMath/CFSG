module

public import CFSG.LocalAnalysis.StandardType.GGTBTorDNsHolds
public import CFSG.LocalAnalysis.StandardType.GGTBXDatumOfTor
public import CFSG.LocalAnalysis.StandardType.GGTwE6WeylTorusTransferCore
public import CFSG.LocalAnalysis.StandardType.GGQTwoVACSymp
public import CFSG.LocalAnalysis.StandardType.GGRootGenSmallRankQFour
public import CFSG.LocalAnalysis.StandardType.GGCorFourTwoOpenOrth
public import CFSG.LocalAnalysis.StandardType.GGSecFiveSplitNbrSmallRank
public import CFSG.LocalAnalysis.StandardType.GGFieldCaseL48TBVac
public import CFSG.LocalAnalysis.StandardType.GGStdSubSmallRestThreeVac

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly
open CFSG.RankThree.Classical2 (orthDerived)

theorem ggQ2Orth_three_le_card_gamma {G : Type} [Group G] [Finite G] {B Bs : Subgroup G}
    {x : G} {L D J : Subgroup G} (hS : GGQTwoSetting 3 B Bs x L D J)
    (hBsN : Bs ≤ Subgroup.normalizer (L : Set G)) :
    3 ^ 3 ≤ Nat.card (ggGamma L hBsN).range := by
  have hcfg : GGConfig 3 B Bs x L D J := hS.1.1
  obtain ⟨-, -, hxB, -, h34⟩ := hcfg.tableB_facts
  have hkerγ : (ggGamma L hBsN).ker = (Subgroup.zpowers x).subgroupOf Bs := by
    ext b
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, ggGamma_eq_one_iff]
    constructor
    · intro hb
      have hmem : (b : G) ∈ Bs ⊓ Subgroup.centralizer (L : Set G) := ⟨b.2, hb⟩
      simpa [hcfg.bstar_inf_centralizer_L] using hmem
    · intro hb
      have hmem : (b : G) ∈ Bs ⊓ Subgroup.centralizer (L : Set G) := by
        simpa [hcfg.bstar_inf_centralizer_L] using hb
      exact hmem.2
  have hcard : Nat.card (ggGamma L hBsN).range * 3 = Nat.card Bs := by
    have h1 := Subgroup.card_ker_mul_card_range (ggGamma L hBsN)
    rw [hkerγ, Nat.card_congr
      (Subgroup.subgroupOfEquivOfLe (Subgroup.zpowers_le.mpr hxB)).toEquiv,
      Nat.card_zpowers, hcfg.orderOf_x] at h1
    simpa [mul_comm] using h1
  have h4 : 3 ^ 4 ≤ Nat.card (ggGamma L hBsN).range * 3 := by
    rw [hcard]; exact h34
  rw [pow_succ] at h4
  exact Nat.le_of_mul_le_mul_right h4 (by norm_num)

theorem ggQ2OrthPlus_gamma_upper
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G}
    {x : G} {L D J : Subgroup G} (hS : GGQTwoSetting 3 B Bs x L D J)
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2) {m : ℕ} (hm : 4 ≤ m)
    (heven : Even m)
    {θ : L ⧸ Subgroup.center L ≃* LargeEvenProj (LargeEvenOmega (LargeEvenQPlus K m))}
    (hperf : commutator L = ⊤) (hBsN : Bs ≤ Subgroup.normalizer (L : Set G))
    (hBsI0 : ∀ b ∈ Bs, ∃ φ ∈ LargeEvenInnSet (LargeEvenProj
      (LargeEvenOmega (LargeEvenQPlus K m))),
      LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) φ) :
    Nat.card (ggGamma L hBsN).range ≤ 3 ^ m := by
  classical
  haveI : CharP K 2 := charP_two_of_card (m := 1) (by rw [hK, pow_one])
  let R := LargeEvenProj (LargeEvenOmega (LargeEvenQPlus K m))
  let A : Subgroup (MulAut ↥L) := (ggGamma L hBsN).range
  have hcfg : GGConfig 3 B Bs x L D J := hS.1.1
  obtain ⟨-, hBsE, hxB, -, h34⟩ := hcfg.tableB_facts
  have hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ 3 = 1 → g ∈ Bs := hcfg.2.1.2.2.2
  have hAe : IsElemAbelian 3 A := (QTwoCav.gamma_hyps hS hBsN).1
  have hAsc : GGTorusSelfCent 3 A := (QTwoCav.gamma_hyps hS hBsN).2
  have hAI : ∀ a ∈ A, ∃ φ ∈ LargeEvenInnSet R, ∀ l : L,
      φ (ggQuotHom θ l) = ggQuotHom θ (a l) := by
    rintro _ ⟨b, rfl⟩
    exact ⟨ggBeta L θ hBsN b, ggBeta_mem L θ hBsN hBsI0 b,
      fun l => ggBeta_ggQuotHom L hBsN θ b l⟩
  have hker : (ggQuotHom θ).ker ≤ Subgroup.center L := by
    rw [ker_ggQuotHom]
  have h3A : 3 ^ 3 ≤ Nat.card A := by
    simpa [A] using ggQ2Orth_three_le_card_gamma hS hBsN
  have hTB : GGTorusTBGroup 3 3 R (LargeEvenInnSet R) ↥L (ggQuotHom θ) A :=
    ⟨ggQuotHom_surjective θ, hker, hperf, hAe, hAI, h3A, h3A, hAsc⟩
  have hpq : 3 ∣ Nat.card K + 1 := by rw [hK]
  have hTor := ggTorusTorW_omegaPlus_nonsplit (K := K) (p := 3) (N := m)
    Nat.prime_three (by norm_num) hpq hm heven (r := 3) ↥L (ggQuotHom θ) A hTB
  have h3eq : Nat.card K + 1 = 3 := by rw [hK]
  rw [h3eq] at hTor
  obtain ⟨w, hw⟩ := hTor
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact ggTD_card_range_le_pow (p := 3) (m := 3) (N := m)
    (C := CartanMatrix.D m) (M := ggCoxeterMatrixD m) (by norm_num) (by norm_num)
    hBsE hSC hBsN w hw

theorem ggQ2Orth_card_of_charSum {K : Type} [Field K] [Finite K] [CharP K 2]
    {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    {Q : QuadraticForm K V} (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hpq : 3 ∣ Nat.card K - 1 ∨ 3 ∣ Nat.card K + 1) {m : ℕ}
    (hV : Module.finrank K V = 2 * m)
    (hT : ∃ T : Submodule K V, Module.finrank K T = 3 ∧ ∀ v ∈ T, Q v = 0)
    (hchar : OrdPNsOm.charSum Q ⊤ ≡ 1 [ZMOD 3])
    {E : Subgroup ↥(orthDerived Q)} (hE : IsElemAbelian 3 E)
    (h3 : 3 ^ 3 ≤ Nat.card E)
    (hsc : ∀ g : ↥(orthDerived Q), (∀ z ∈ E, g * z = z * g) → g ^ 3 = 1 → g ∈ E) :
    Nat.card E = 3 ^ m := by
  classical
  have hne : ∃ b ∈ E, b ≠ 1 := by
    by_contra h
    push Not at h
    have hE1 : E = ⊥ := (Subgroup.eq_bot_iff_forall E).mpr h
    rw [hE1, Subgroup.card_bot] at h3
    omega
  obtain ⟨r, τ, hτinj, hrange, -, -, -, hW⟩ :=
    OrthTorus.exists_torus_orthDerived_of_ne (p := 3) Nat.prime_three (by norm_num)
      hpq hQ hT E hE hne hsc
  have hr : r = m := by
    rcases hW with ⟨-, hfin⟩ | ⟨hneg, -⟩
    · omega
    · exact absurd (hchar.symm.trans hneg)
        (OrthTorus.one_not_modEq_neg_one Nat.prime_three (by norm_num))
  have h1 : Nat.card (Fin r → Multiplicative (ZMod 3)) = 3 ^ r := by
    rw [Nat.card_congr (Equiv.piCongrRight fun _ => Multiplicative.toAdd),
      Nat.card_fun, Nat.card_zmod, Nat.card_fin]
  have h2 : Nat.card (MonoidHom.range τ) = Nat.card (Fin r → Multiplicative (ZMod 3)) :=
    Nat.card_congr (MonoidHom.ofInjective hτinj).toEquiv.symm
  rw [hrange] at h2
  rw [h2, h1, hr]

theorem ggQ2Orth_gamma_innerModel {G : Type} [Group G] [Finite G] {B Bs : Subgroup G}
    {x : G} {L D J : Subgroup G} (hS : GGQTwoSetting 3 B Bs x L D J)
    (hperf : commutator L = ⊤) (hBsN : Bs ≤ Subgroup.normalizer (L : Set G))
    {R : Type} [Group R] (hZ : Subgroup.center R = ⊥)
    (hIp : GGOutdiagPrime 3 R (LargeEvenInnSet R)) (hcp : GGCenterPrime 3 R)
    {K : Type} [Field K] [Finite K] [CharP K 2]
    {V : Type} [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}
    {θ : L ⧸ Subgroup.center L ≃* R} (e : R ≃* ↥(orthDerived Q))
    (hAI : ∀ a ∈ (ggGamma L hBsN).range, ∃ φ ∈ LargeEvenInnSet R, ∀ l : L,
      φ (ggQuotHom θ l) = ggQuotHom θ (a l)) :
    ∃ EΩ : Subgroup ↥(orthDerived Q), IsElemAbelian 3 EΩ ∧
      (∀ g : ↥(orthDerived Q), (∀ z ∈ EΩ, g * z = z * g) → g ^ 3 = 1 → g ∈ EΩ) ∧
      3 ^ 3 ≤ Nat.card EΩ ∧ Nat.card EΩ = Nat.card (ggGamma L hBsN).range := by
  classical
  let A : Subgroup (MulAut ↥L) := (ggGamma L hBsN).range
  have hAe : IsElemAbelian 3 A := (QTwoCav.gamma_hyps hS hBsN).1
  have hAsc : GGTorusSelfCent 3 A := (QTwoCav.gamma_hyps hS hBsN).2
  obtain ⟨Λ, -, -, -, -, hEab, hEcard, hEsc⟩ :=
    TwE6TB.exists_innerModel Nat.prime_three hZ hIp hcp (ggQuotHom θ)
      (ggQuotHom_surjective θ) (by rw [ker_ggQuotHom]) hperf hAe hAI hAsc
  let E : Subgroup R := A.comap Λ
  let EΩ : Subgroup ↥(orthDerived Q) := E.map e.toMonoidHom
  have hEΩab : IsElemAbelian 3 EΩ := TableB.isElemAbelian_map hEab e.toMonoidHom
  have hEΩcard : Nat.card EΩ = Nat.card A := by
    rw [Subgroup.card_map_of_injective (f := e.toMonoidHom) e.injective, hEcard]
  have h3A : 3 ^ 3 ≤ Nat.card A := by
    simpa [A] using ggQ2Orth_three_le_card_gamma hS hBsN
  have h3EΩ : 3 ^ 3 ≤ Nat.card EΩ := by rw [hEΩcard]; exact h3A
  have hEΩsc : ∀ g : ↥(orthDerived Q),
      (∀ z ∈ EΩ, g * z = z * g) → g ^ 3 = 1 → g ∈ EΩ := by
    intro g hg hg3
    obtain ⟨r, rfl⟩ := e.surjective g
    refine Subgroup.mem_map.mpr ⟨r, ?_, rfl⟩
    refine hEsc r ?_ ?_
    · intro z hz
      exact e.injective (by simpa [map_mul] using hg (e z) (Subgroup.mem_map_of_mem _ hz))
    · exact e.injective (by simpa [map_pow] using hg3)
  exact ⟨EΩ, hEΩab, hEΩsc, h3EΩ, hEΩcard⟩

theorem ggQ2OrthPlus_gamma_lower
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G}
    {x : G} {L D J : Subgroup G} (hS : GGQTwoSetting 3 B Bs x L D J)
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2) {m : ℕ} (hm : 4 ≤ m)
    (heven : Even m)
    {θ : L ⧸ Subgroup.center L ≃* LargeEvenProj (LargeEvenOmega (LargeEvenQPlus K m))}
    (hperf : commutator L = ⊤) (hBsN : Bs ≤ Subgroup.normalizer (L : Set G))
    (hBsI0 : ∀ b ∈ Bs, ∃ φ ∈ LargeEvenInnSet (LargeEvenProj
      (LargeEvenOmega (LargeEvenQPlus K m))),
      LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) φ) :
    3 ^ m ≤ Nat.card (ggGamma L hBsN).range := by
  classical
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  haveI : CharP K 2 := charP_two_of_card (m := 1) (by rw [hK, pow_one])
  let R := LargeEvenProj (LargeEvenOmega (LargeEvenQPlus K (m' + 1)))
  have hAI : ∀ a ∈ (ggGamma L hBsN).range, ∃ φ ∈ LargeEvenInnSet R, ∀ l : L,
      φ (ggQuotHom θ l) = ggQuotHom θ (a l) := by
    rintro _ ⟨b, rfl⟩
    exact ⟨ggBeta L θ hBsN b, ggBeta_mem L θ hBsN hBsI0 b,
      fun l => ggBeta_ggQuotHom L hBsN θ b l⟩
  obtain ⟨hZR, hcp⟩ := OrthNs.center_data_omegaPlus (K := K) (p := 3) (m := m' + 1)
    Nat.prime_three (by norm_num) (by omega : 3 ≤ m' + 1)
  have hIp : GGOutdiagPrime 3 R (LargeEvenInnSet R) := fun φ hφ _ => hφ
  obtain ⟨EΩ, hEΩab, hEΩsc, h3EΩ, hEΩcardA⟩ :=
    ggQ2Orth_gamma_innerModel hS hperf hBsN hZR hIp hcp
      (OrthTorus.rPlusEquiv K (by omega)) hAI
  obtain ⟨T, hTdim, hTsing⟩ :=
    OrthTorus.exists_totallySingular_qPlusForm (K := K) (n := m') (by omega)
  have hT : ∃ T : Submodule K (Fin (m' + 1) ⊕ Fin (m' + 1) → K),
      Module.finrank K T = 3 ∧ ∀ v ∈ T, TableBOrth.qPlusForm K (m' + 1) v = 0 :=
    ⟨T, hTdim, hTsing⟩
  have hcharSum : OrdPNsOm.charSum (TableBOrth.qPlusForm K (m' + 1)) ⊤ ≡ 1 [ZMOD 3] := by
    have h := OrthTorus.charSum_qPlusForm (K := K) (n := m')
    rw [h, hK]
    have h2 : (2 : ℤ) ≡ -1 [ZMOD 3] := by
      rw [Int.modEq_iff_dvd]
      norm_num
    have hp := h2.pow (m' + 1)
    rwa [Even.neg_one_pow heven] at hp
  have hVdim : Module.finrank K (Fin (m' + 1) ⊕ Fin (m' + 1) → K) = 2 * (m' + 1) := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin]
    ring
  have hcardEΩ : Nat.card EΩ = 3 ^ (m' + 1) :=
    ggQ2Orth_card_of_charSum (K := K) (V := Fin (m' + 1) ⊕ Fin (m' + 1) → K)
      (Q := TableBOrth.qPlusForm K (m' + 1))
      (TableBOrth.nondegenerate_qPlusForm (m' + 1))
      (Or.inr (by rw [hK])) hVdim hT hcharSum hEΩab h3EΩ hEΩsc
  rw [← hEΩcardA, hcardEΩ]

theorem ggQ2OrthPlus_gamma_card
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G}
    {x : G} {L D J : Subgroup G} (hS : GGQTwoSetting 3 B Bs x L D J)
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2) {m : ℕ} (hm : 4 ≤ m)
    (heven : Even m)
    {θ : L ⧸ Subgroup.center L ≃* LargeEvenProj (LargeEvenOmega (LargeEvenQPlus K m))}
    (hperf : commutator L = ⊤) (hBsN : Bs ≤ Subgroup.normalizer (L : Set G))
    (hBsI0 : ∀ b ∈ Bs, ∃ φ ∈ LargeEvenInnSet (LargeEvenProj
      (LargeEvenOmega (LargeEvenQPlus K m))),
      LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) φ) :
    Nat.card (ggGamma L hBsN).range = 3 ^ m :=
  le_antisymm (ggQ2OrthPlus_gamma_upper hS hK hm heven hperf hBsN hBsI0)
    (ggQ2OrthPlus_gamma_lower hS hK hm heven hperf hBsN hBsI0)

theorem ggQ2OrthMinus_gamma_upper
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G}
    {x : G} {L D J : Subgroup G} (hS : GGQTwoSetting 3 B Bs x L D J)
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2) {m : ℕ} (hm : 4 ≤ m)
    (hodd : Odd m) {b c : K} (hbc : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    {θ : L ⧸ Subgroup.center L ≃*
      LargeEvenProj (LargeEvenOmega (LargeEvenQMinus (m - 1) b c))}
    (hperf : commutator L = ⊤) (hBsN : Bs ≤ Subgroup.normalizer (L : Set G))
    (hBsI0 : ∀ b' ∈ Bs, ∃ φ ∈ LargeEvenInnSet (LargeEvenProj
      (LargeEvenOmega (LargeEvenQMinus (m - 1) b c))),
      LargeEvenInduces θ (fun l l' => (l' : G) = b'⁻¹ * l * b') φ) :
    Nat.card (ggGamma L hBsN).range ≤ 3 ^ m := by
  classical
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  haveI : CharP K 2 := charP_two_of_card (m := 1) (by rw [hK, pow_one])
  let R := LargeEvenProj (LargeEvenOmega (LargeEvenQMinus m' b c))
  let A : Subgroup (MulAut ↥L) := (ggGamma L hBsN).range
  have hcfg : GGConfig 3 B Bs x L D J := hS.1.1
  obtain ⟨-, hBsE, -, -, h34⟩ := hcfg.tableB_facts
  have hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ 3 = 1 → g ∈ Bs := hcfg.2.1.2.2.2
  have hAe : IsElemAbelian 3 A := (QTwoCav.gamma_hyps hS hBsN).1
  have hAsc : GGTorusSelfCent 3 A := (QTwoCav.gamma_hyps hS hBsN).2
  have hAI : ∀ a ∈ A, ∃ φ ∈ LargeEvenInnSet R, ∀ l : L,
      φ (ggQuotHom θ l) = ggQuotHom θ (a l) := by
    rintro _ ⟨b', rfl⟩
    exact ⟨ggBeta L θ hBsN b', ggBeta_mem L θ hBsN hBsI0 b',
      fun l => ggBeta_ggQuotHom L hBsN θ b' l⟩
  have h3A : 3 ^ 3 ≤ Nat.card A := by
    simpa [A] using ggQ2Orth_three_le_card_gamma hS hBsN
  have hTB : GGTorusTBGroup 3 3 R (LargeEvenInnSet R) ↥L (ggQuotHom θ) A :=
    ⟨ggQuotHom_surjective θ, by rw [ker_ggQuotHom], hperf, hAe, hAI, h3A, h3A, hAsc⟩
  have hpq : 3 ∣ Nat.card K + 1 := by rw [hK]
  have hTor := ggTorusTorW_omegaMinus_nonsplit (K := K) (p := 3) (N := m' + 1)
    Nat.prime_three (by norm_num) hpq (by omega) (hodd) hbc
    (r := 3) ↥L (ggQuotHom θ) A hTB
  have h3eq : Nat.card K + 1 = 3 := by rw [hK]
  rw [h3eq] at hTor
  obtain ⟨w, hw⟩ := hTor
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact ggTD_card_range_le_pow (p := 3) (m := 3) (N := m' + 1)
    (C := CartanMatrix.D (m' + 1)) (M := ggCoxeterMatrixD (m' + 1))
    (by norm_num) (by norm_num) hBsE hSC hBsN w hw

theorem ggQ2OrthMinus_gamma_lower
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G}
    {x : G} {L D J : Subgroup G} (hS : GGQTwoSetting 3 B Bs x L D J)
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2) {m : ℕ} (hm : 4 ≤ m)
    (hodd : Odd m) {b c : K} (hbc : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    {θ : L ⧸ Subgroup.center L ≃*
      LargeEvenProj (LargeEvenOmega (LargeEvenQMinus (m - 1) b c))}
    (hperf : commutator L = ⊤) (hBsN : Bs ≤ Subgroup.normalizer (L : Set G))
    (hBsI0 : ∀ b' ∈ Bs, ∃ φ ∈ LargeEvenInnSet (LargeEvenProj
      (LargeEvenOmega (LargeEvenQMinus (m - 1) b c))),
      LargeEvenInduces θ (fun l l' => (l' : G) = b'⁻¹ * l * b') φ) :
    3 ^ m ≤ Nat.card (ggGamma L hBsN).range := by
  classical
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  haveI : CharP K 2 := charP_two_of_card (m := 1) (by rw [hK, pow_one])
  let R := LargeEvenProj (LargeEvenOmega (LargeEvenQMinus m' b c))
  have hAI : ∀ a ∈ (ggGamma L hBsN).range, ∃ φ ∈ LargeEvenInnSet R, ∀ l : L,
      φ (ggQuotHom θ l) = ggQuotHom θ (a l) := by
    rintro _ ⟨b', rfl⟩
    exact ⟨ggBeta L θ hBsN b', ggBeta_mem L θ hBsN hBsI0 b',
      fun l => ggBeta_ggQuotHom L hBsN θ b' l⟩
  obtain ⟨hZR, hcp⟩ := OrthExc.center_data_omegaMinus (K := K) (p := 3) (m := m')
    Nat.prime_three (by norm_num) (by omega : 3 ≤ m') hbc
  have hIp : GGOutdiagPrime 3 R (LargeEvenInnSet R) := fun φ hφ _ => hφ
  obtain ⟨EΩ, hEΩab, hEΩsc, h3EΩ, hEΩcardA⟩ :=
    ggQ2Orth_gamma_innerModel hS hperf hBsN hZR hIp hcp
      (OrthTorus.rMinusEquiv K m' b c) hAI
  obtain ⟨-, hTfun⟩ := OrthTorus.charSum_qMinusForm (K := K) (m := m') hbc
  have hT : ∃ T : Submodule K (LargeEvenMinusIdx m' → K),
      Module.finrank K T = 3 ∧ ∀ v ∈ T, TableBOrth.qMinusForm K m' b c v = 0 :=
    hTfun (by omega)
  have hcharSum : OrdPNsOm.charSum (TableBOrth.qMinusForm K m' b c) ⊤ ≡ 1 [ZMOD 3] := by
    obtain ⟨h, -⟩ := OrthTorus.charSum_qMinusForm (K := K) (m := m') hbc
    rw [h, hK]
    have h2 : (2 : ℤ) ≡ -1 [ZMOD 3] := by
      rw [Int.modEq_iff_dvd]
      norm_num
    have hp := h2.pow (m' + 1)
    rw [Odd.neg_one_pow hodd] at hp
    simpa using hp.neg
  have hVdim : Module.finrank K (LargeEvenMinusIdx m' → K) = 2 * (m' + 1) := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_sum,
      Fintype.card_fin, Fintype.card_fin]
    ring
  have hcardEΩ : Nat.card EΩ = 3 ^ (m' + 1) :=
    ggQ2Orth_card_of_charSum (K := K) (V := LargeEvenMinusIdx m' → K)
      (Q := TableBOrth.qMinusForm K m' b c)
      (TableBOrth.nondegenerate_qMinusForm m' hbc)
      (Or.inr (by rw [hK])) hVdim hT hcharSum hEΩab h3EΩ hEΩsc
  rw [← hEΩcardA, hcardEΩ]

theorem ggQ2OrthMinus_gamma_card
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G}
    {x : G} {L D J : Subgroup G} (hS : GGQTwoSetting 3 B Bs x L D J)
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2) {m : ℕ} (hm : 4 ≤ m)
    (hodd : Odd m) {b c : K} (hbc : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    {θ : L ⧸ Subgroup.center L ≃*
      LargeEvenProj (LargeEvenOmega (LargeEvenQMinus (m - 1) b c))}
    (hperf : commutator L = ⊤) (hBsN : Bs ≤ Subgroup.normalizer (L : Set G))
    (hBsI0 : ∀ b' ∈ Bs, ∃ φ ∈ LargeEvenInnSet (LargeEvenProj
      (LargeEvenOmega (LargeEvenQMinus (m - 1) b c))),
      LargeEvenInduces θ (fun l l' => (l' : G) = b'⁻¹ * l * b') φ) :
    Nat.card (ggGamma L hBsN).range = 3 ^ m :=
  le_antisymm (ggQ2OrthMinus_gamma_upper hS hK hm hodd hbc hperf hBsN hBsI0)
    (ggQ2OrthMinus_gamma_lower hS hK hm hodd hbc hperf hBsN hBsI0)

theorem ggQ2TBFull_of_orthLabel {G : Type} [Group G] {p : ℕ} {Bs L : Subgroup G}
    {lab : LargeEvenLabel} (hgl : GGLabQTwo p lab)
    (hmark : LargeEvenMarking L (fun lab' _ _ _ _ _ => lab' = lab))
    (hBsN : Bs ≤ Subgroup.normalizer (L : Set G))
    (hcard : Nat.card (ggGamma L hBsN).range = p ^ GGQ2LieRank lab) :
    GGQ2TBFull p Bs L :=
  ⟨lab, hgl, hmark, by rwa [← QTwoCav.gamma_card hBsN]⟩

theorem ggQ2TBFull_of_orthFull
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G}
    {x : G} {L D J : Subgroup G} (hS : GGQTwoSetting p B Bs x L D J) (hp : p = 3)
    (hL : GGInnerDiagOnLabel (fun p lab => GGQ2VACLabOrth p lab ∧ 4 ≤ lab.rank ∧
      ((lab.tag = .D ∧ Even lab.rank) ∨ (lab.tag = .twD ∧ ¬ Even lab.rank))) p Bs L) :
    GGQ2TBFull p Bs L := by
  subst hp
  obtain ⟨hperf, lab, hlab, hraw⟩ := hL
  obtain ⟨R, hR, I, F, hQ⟩ := largeEvenRawDatum_exists hraw
  obtain ⟨-, -, θ, hP⟩ := hQ
  obtain ⟨horth, hrank, hpar⟩ := hP.1
  obtain ⟨tag, rank, n⟩ := lab
  have hn1 : n = 1 := by
    have h1 : 1 ≤ n := hlab.1; have h2 : n < 2 := horth.1; omega
  have hmark : LargeEvenMarking L (fun lab' _ _ _ _ _ => lab' = ⟨tag, rank, n⟩) :=
    ⟨hperf, ⟨tag, rank, n⟩, hlab,
      largeEvenRawDatum_mono (fun R _ I F ⟨hs, hna, θ, _⟩ => ⟨hs, hna, θ, rfl⟩) hraw⟩
  rcases hpar with ⟨htag, heven⟩ | ⟨htag, hodd⟩
  · subst htag
    dsimp only [CFSG.Assembly.LargeEvenRawDatumLegacy] at hraw
    have hrankD : 4 ≤ (⟨.D, rank, n⟩ : LargeEvenLabel).rank := by simpa using hrank
    have hrk3 : (⟨.D, rank, n⟩ : LargeEvenLabel).rank ≠ 3 := by omega
    rw [if_neg hrk3, hn1] at hraw
    obtain ⟨K, i1, i2, hK, hQ⟩ := hraw
    obtain ⟨-, -, θ, hQ⟩ := hQ
    obtain ⟨-, hBsN, hBsI0⟩ := hQ
    have hK2 : Nat.card K = 2 := by simpa using hK
    refine ggQ2TBFull_of_orthLabel ?_ hmark hBsN ?_
    · simpa [hn1] using horth.1
    · rw [ggQ2OrthPlus_gamma_card hS hK2 hrank heven hperf hBsN hBsI0]
      simp [GGQ2LieRank]
  · subst htag
    dsimp only [CFSG.Assembly.LargeEvenRawDatumLegacy] at hraw
    have hrankTwD : 4 ≤ (⟨.twD, rank, n⟩ : LargeEvenLabel).rank := by simpa using hrank
    have hrk2 : (⟨.twD, rank, n⟩ : LargeEvenLabel).rank ≠ 2 := by omega
    have hrk3 : (⟨.twD, rank, n⟩ : LargeEvenLabel).rank ≠ 3 := by omega
    rw [if_neg hrk2, if_neg hrk3, hn1] at hraw
    obtain ⟨K, i1, i2, hK, b, c, hbc, hQ⟩ := hraw
    obtain ⟨-, -, θ, hQ⟩ := hQ
    obtain ⟨-, hBsN, hBsI0⟩ := hQ
    have hK2 : Nat.card K = 2 := by simpa using hK
    have hodd' : Odd rank := Nat.not_even_iff_odd.mp hodd
    refine ggQ2TBFull_of_orthLabel ?_ hmark hBsN ?_
    · simpa [hn1] using horth.1
    · rw [ggQ2OrthMinus_gamma_card hS hK2 hrank hodd' hbc hperf hBsN hBsI0]
      simp [GGQ2LieRank]

theorem ggQTwoGuardFailsOn_orthSmall :
    GGQTwoGuardFailsOn (fun p lab => GGQ2VACLabOrth p lab ∧
      ((lab.tag = .D ∧ lab.rank = 3) ∨ (lab.tag = .twD ∧ lab.rank = 2))) := by
  intro G _ _ p B Bs x L D J hS hp hL
  subst hp
  have hmark := ggInnerDiagOnLabel_L_pRank_ge_three hS.1.1 hL
  have hbound : ¬ LargeEvenMarking ↥L (fun lab R _ I _ _ =>
      (GGQ2VACLabOrth 3 lab ∧
        ((lab.tag = .D ∧ lab.rank = 3) ∨ (lab.tag = .twD ∧ lab.rank = 2))) ∧
      ∃ E : Subgroup (MulAut R), (E : Set (MulAut R)) ⊆ I ∧ IsElemAbelian 3 E ∧
        3 ^ 3 ≤ Nat.card E) := by
    refine not_largeEvenMarking_of_labelAll_card_lt (p := 3)
      (S := fun lab => GGQ2VACLabOrth 3 lab ∧
        ((lab.tag = .D ∧ lab.rank = 3) ∨ (lab.tag = .twD ∧ lab.rank = 2))) ?_
    intro lab hlab hS
    rcases hS with ⟨horth, hD3 | htwD2⟩
    · have hn1 : lab.n = 1 := by
        have h1 : 1 ≤ lab.n := hlab.1
        have h2 : lab.n < 2 := horth.1
        omega
      exact (StdSubRestThree.largeEvenLabelAll_card_lt_twoThreeSmall (p := 3) (lab := lab)
        ⟨rfl, hn1, Or.inr ⟨hD3.1, hD3.2⟩⟩).mono
        fun _ _ _ _ h' _ _ => h'
    · exact (largeEvenLabelAll_card_lt_linearTwo (p := 3) Nat.prime_three (by norm_num)
        hlab (Or.inr ⟨htwD2.1, htwD2.2⟩)).mono fun _ _ _ _ h' _ _ => h'
  exact absurd hmark hbound

end CFSG.StandardType

end
