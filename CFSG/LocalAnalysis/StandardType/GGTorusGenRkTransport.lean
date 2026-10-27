module

public import CFSG.LocalAnalysis.StandardType.GGFieldCaseL48TBPosition
public import CFSG.LocalAnalysis.StandardType.GGTableBStdSub
public import CFSG.LocalAnalysis.GLTheoremA.S12.CanonInnBridge
public import CFSG.LocalAnalysis.StandardType.GGTorusGenRkComp
public import CFSG.LocalAnalysis.StandardType.GGResLeaf
public import CFSG.LocalAnalysis.StandardType.GGNbrTwE6Prop87
public import CFSG.LocalAnalysis.StandardType.GGTDModelU
public import CFSG.LocalAnalysis.StandardType.GGResE6DepOrder
public import CFSG.LocalAnalysis.StandardType.GGStdSubSmallUnitDvdSmall
public import CFSG.LocalAnalysis.StandardType.GGResLeviLE3BridgeA2
public import CFSG.LocalAnalysis.StandardType.GGResLeviLE3Bridge
public import CFSG.LocalAnalysis.StandardType.GGSpJoinNbrModel
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentySplitRefl
public import CFSG.LocalAnalysis.StandardType.GGRemTableBLLineUModelCoprime
public import CFSG.LocalAnalysis.StandardType.GGTableBUnit63Main
public import CFSG.LocalAnalysis.StandardType.GGTBJTwoNodeUnitaryDatum
public import CFSG.LocalAnalysis.StandardType.GGNbrReflGenCore

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly TableB

private theorem inf_centralizer_eq {M : Type} [Group M] {L' E E₁ D' : Subgroup M} {d : M}
    (hdec : ∀ x ∈ E, ∃ e₁ ∈ E₁, ∃ z ∈ E ⊓ Subgroup.centralizer (L' : Set M), x = e₁ * z)
    (hD'E : D' ≤ E) (hCD' : E ⊓ Subgroup.centralizer (L' : Set M) ≤ D')
    (hD'E₁ : D' ⊓ E₁ = Subgroup.zpowers d) :
    L' ⊓ Subgroup.centralizer (D' : Set M) = L' ⊓ Subgroup.centralizer ({d} : Set M) := by
  have hdD' : d ∈ D' := by
    have hd : d ∈ D' ⊓ E₁ := by
      rw [hD'E₁]
      exact Subgroup.mem_zpowers d
    exact hd.1
  apply le_antisymm
  · exact le_inf inf_le_left
      (inf_le_right.trans (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hdD')))
  · rintro l ⟨hlL, hld⟩
    refine ⟨hlL, ?_⟩
    refine Subgroup.mem_centralizer_iff.mpr ?_
    intro x hx
    obtain ⟨e₁, he₁E₁, z, hz, hxz⟩ := hdec x (hD'E hx)
    have hzD' : z ∈ D' := hCD' hz
    have hlz : l * z = z * l :=
      Subgroup.mem_centralizer_iff.mp hz.2 l hlL
    have he₁_eq : e₁ = x * z⁻¹ := by rw [hxz]; group
    have he₁D' : e₁ ∈ D' := by
      rw [he₁_eq]
      exact D'.mul_mem hx (D'.inv_mem hzD')
    have he₁zp : e₁ ∈ Subgroup.zpowers d := by
      rw [← hD'E₁]
      exact ⟨he₁D', he₁E₁⟩
    have hdle : d ∈ Subgroup.centralizer ({l} : Set M) := by
      refine Subgroup.mem_centralizer_iff.mpr ?_
      intro h hh
      rw [Set.mem_singleton_iff] at hh
      subst hh
      exact (Subgroup.mem_centralizer_iff.mp hld d (Set.mem_singleton d)).symm
    have he₁l : l * e₁ = e₁ * l :=
      Subgroup.mem_centralizer_iff.mp ((Subgroup.zpowers_le.mpr hdle) he₁zp) l (Set.mem_singleton l)
    rw [hxz]
    calc (e₁ * z) * l = e₁ * (z * l) := by group
      _ = e₁ * (l * z) := by rw [hlz]
      _ = (e₁ * l) * z := by group
      _ = (l * e₁) * z := by rw [he₁l]
      _ = l * (e₁ * z) := by group

private theorem fixSubgroup_conjAut_eq_ggFix {M : Type} [Group M] (L : Subgroup M) {d : M}
    (hd : d ∈ Subgroup.normalizer (L : Set M)) :
    CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup
        (CFSG.LocalAnalysis.GLTheoremA.Y10F.conjAut L d hd) =
      ggFix (L.normalizerMonoidHom ⟨d, hd⟩) := by
  ext l
  rw [CFSG.HardMathSupport.Solomon.Coordinator.mem_fixSubgroup, mem_ggFix]
  constructor
  · intro h
    apply Subtype.ext
    change d * (l : M) * d⁻¹ = (l : M)
    have h' := congrArg (fun x : L => (x : M)) h
    rw [CFSG.LocalAnalysis.GLTheoremA.Y10F.coe_conjAut] at h'
    calc d * (l : M) * d⁻¹ = d * (d⁻¹ * (l : M) * d) * d⁻¹ := by rw [h']
      _ = (l : M) := by group
  · intro h
    apply Subtype.ext
    rw [CFSG.LocalAnalysis.GLTheoremA.Y10F.coe_conjAut]
    have h' := congrArg (fun x : L => (x : M)) h
    change d * (l : M) * d⁻¹ = (l : M) at h'
    calc d⁻¹ * (l : M) * d = d⁻¹ * (d * (l : M) * d⁻¹) * d := by rw [h']
      _ = (l : M) := by group

theorem isComponentOf_subgroupOf_ggFix_of_decomp
    {M : Type} [Group M] [Finite M] {L' E E₁ D' J' : Subgroup M} {d : M}
    (hE : E ≤ Subgroup.normalizer (L' : Set M)) (hdE : d ∈ E)
    (hdec : ∀ x ∈ E, ∃ e₁ ∈ E₁, ∃ z ∈ E ⊓ Subgroup.centralizer (L' : Set M), x = e₁ * z)
    (hD'E : D' ≤ E) (hCD' : E ⊓ Subgroup.centralizer (L' : Set M) ≤ D')
    (hD'E₁ : D' ⊓ E₁ = Subgroup.zpowers d)
    (hJ : IsComponentOf J' (L' ⊓ Subgroup.centralizer (D' : Set M))) :
    IsComponentOf (J'.subgroupOf L')
      (ggFix (L'.normalizerMonoidHom ⟨d, hE hdE⟩)) := by
  have hCD : L' ⊓ Subgroup.centralizer (D' : Set M) =
      L' ⊓ Subgroup.centralizer ({d} : Set M) :=
    inf_centralizer_eq hdec hD'E hCD' hD'E₁
  have hK : IsComponentOf J' (L' ⊓ Subgroup.centralizer ({d} : Set M)) := hCD ▸ hJ
  have hKopen : CFSG.Open.IsComponentOf J' (L' ⊓ Subgroup.centralizer ({d} : Set M)) :=
    isComponentOf_iff_open.mp hK
  have hmain : CFSG.Open.IsComponentOf (J'.subgroupOf L')
      (CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup
        (CFSG.LocalAnalysis.GLTheoremA.Y10F.conjAut L' d (hE hdE))) :=
    CFSG.LocalAnalysis.GLTheoremA.CanonInn.isComponentOf_fixSubgroup_conjAut L' (hE hdE) hKopen
  rw [fixSubgroup_conjAut_eq_ggFix L' (hE hdE)] at hmain
  exact isComponentOf_iff_open.mpr hmain

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.StandardType.LineU

theorem GGResHyp.exists_unitaryModel_L_of_marking
    {G : Type} [Group G] [Finite G] {F : Type} [Field F] [Finite F]
    {n d p : ℕ} [Fact p.Prime] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K)
    (hF : Nat.card F = (2 ^ n) ^ 2) (hn : 1 ≤ n) (hd : 5 ≤ d)
    (hpq : p ∣ 2 ^ n + 1) (h63 : ¬ (d = 6 ∧ p = 3))
    (θ : ↥L ⧸ Subgroup.center ↥L ≃* LargeEvenProj (unitarySU 2 n F d))
    (hact : ∀ b ∈ Bs, ∃ a ∈ LargeEvenMatConjImage (LargeEvenProjMk (unitarySU 2 n F d))
      (LargeEvenGUSet (Fin d) F (2 ^ n)),
      LargeEvenInduces θ (fun l l' : ↥L => (l' : G) = b⁻¹ * l * b) a) :
    ∃ ψ : ↥(unitarySU 2 n F d) →* ↥L, UnitTB.Model ψ ∧
      ∀ a ∈ (ggGamma L hH.2.2.1.1.le_normalizer).range,
        ∃ t : Fin d → F, ActsDiagU ψ a t := by
  have hp : p.Prime := Fact.out
  have hp2 : p ≠ 2 := hH.1.1.2.2.2.2.2.1.2.1
  have hN := hH.2.2.1.1.le_normalizer
  have hperf : commutator ↥L = ⊤ := hH.2.2.1.1.1
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
  have hlift := ggTorusLift_unitary hF hn (by omega : 3 ≤ d) hdq hp hpq
  have hTB := ggTorusTBGroup_of_L hH.1 hperf θ hN
    (fun b hb => ggLAut_mem_of_induces L θ hN hact hb) hlift
  obtain ⟨hψ, hker, _, hA, hAI, hr, h3, _⟩ := hTB
  by_cases hpd : p ∣ d
  · have hr' : p ^ (d - 3) ≤ Nat.card (ggGamma L hN).range := by
      simpa [ggUnitaryTorusRank, hpd] using hr
    have hcard := LineU.card_ge_of_dvd hp hp2 hd hpd h63 hr' h3
    obtain ⟨ψ, hψs, hψker, hdiag⟩ :=
      LineU.exists_diagModel hF hn hd hp hpq hpd hcov hψ hker hperf hA hAI hcard
    exact ⟨ψ, ⟨TableBU.unitaryFieldData_of_card hF hn, hψs, hψker⟩, hdiag⟩
  · obtain ⟨ψ, hψs, hψker, hdiag⟩ :=
      LineU.exists_diagModel_coprime hF hn (by omega : 3 ≤ d) hp hpq hpd hcov
        hψ hker hperf hA hAI
    exact ⟨ψ, ⟨TableBU.unitaryFieldData_of_card hF hn, hψs, hψker⟩, hdiag⟩

theorem GGResHyp.exists_unitaryModel_L_of_marking_qGeFour
    {G : Type} [Group G] [Finite G] {F : Type} [Field F] [Finite F]
    {n d p : ℕ} [Fact p.Prime] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K)
    (hF : Nat.card F = (2 ^ n) ^ 2) (hn : 2 ≤ n) (hd : 5 ≤ d)
    (hpq : p ∣ 2 ^ n + 1)
    (θ : ↥L ⧸ Subgroup.center ↥L ≃* LargeEvenProj (unitarySU 2 n F d))
    (hact : ∀ b ∈ Bs, ∃ a ∈ LargeEvenMatConjImage (LargeEvenProjMk (unitarySU 2 n F d))
      (LargeEvenGUSet (Fin d) F (2 ^ n)),
      LargeEvenInduces θ (fun l l' : ↥L => (l' : G) = b⁻¹ * l * b) a) :
    ∃ ψ : ↥(unitarySU 2 n F d) →* ↥L, UnitTB.Model ψ ∧
      ∀ a ∈ (ggGamma L hH.2.2.1.1.le_normalizer).range,
        ∃ t : Fin d → F, ActsDiagU ψ a t := by
  by_cases h63 : ¬ (d = 6 ∧ p = 3)
  · exact hH.exists_unitaryModel_L_of_marking hF (by omega) hd hpq h63 θ hact
  push Not at h63
  obtain ⟨rfl, rfl⟩ := h63
  have hN := hH.2.2.1.1.le_normalizer
  have hperf : commutator ↥L = ⊤ := hH.2.2.1.1.1
  obtain ⟨_, lab, _, hraw⟩ := hH.2.2.1.1
  obtain ⟨R, iR, I, Fim, hsR, hnabR, η, _⟩ := largeEvenRawDatum_exists hraw
  let := iR
  have : IsSimpleGroup R := hsR
  have hs : IsSimpleGroup (LargeEvenProj (unitarySU 2 n F 6)) :=
    (θ.symm.trans η).isSimpleGroup
  have hnab : ∃ a b : LargeEvenProj (unitarySU 2 n F 6), a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hnabR
    let e := η.symm.trans θ
    refine ⟨e a, e b, fun he => hab (e.injective ?_)⟩
    simpa only [map_mul] using he
  have hmark : GGInnerDiagOnLab GGUnitDvd63Label 3 Bs L := by
    refine ⟨hperf, (⟨.twA, 5, n⟩ : LargeEvenLabel), ?_, ?_⟩
    · change 1 ≤ n ∧ 2 ≤ 5 ∧ (5 = 2 → 2 ≤ n)
      omega
    dsimp only [CFSG.Assembly.LargeEvenRawDatumLegacy]
    change LargeEvenRecipeUnitary 6 (2 ^ n) _
    refine ⟨F, inferInstance, inferInstance, hF, hs, hnab, θ, ?_⟩
    refine ⟨⟨⟨rfl, by norm_num, hpq, by norm_num⟩, rfl, rfl⟩, ?_, hN, hact⟩
    exact Or.inr (Or.inl ⟨by simp [LargeEvenUntwisted],
      by change LargeEvenLieTag.twA ≠ .triD4; decide, hpq⟩)
  have hcard := card_range_ggGamma_unitDvd63 hH.1 hmark hN
  have hcov := LineU.unitaryUniversalCover_holds n 6 F hF (by norm_num)
    (by intro h; have : n = 1 := congrArg Prod.snd h; omega)
  have hlift := ggTorusLift_unitary hF (by omega : 1 ≤ n) (by norm_num : 3 ≤ 6)
    (by intro h; have : (6 : ℕ) = 3 := congrArg Prod.fst h; omega)
    Nat.prime_three hpq
  obtain ⟨hψ, hker, _, hA, hAI, _, _, _⟩ :=
    ggTorusTBGroup_of_L hH.1 hperf θ hN
      (fun b hb => ggLAut_mem_of_induces L θ hN hact hb) hlift
  obtain ⟨ψ, hψs, hψker, hdiag⟩ := LineU.exists_diagModel hF (by omega) (by norm_num)
    Nat.prime_three hpq (by norm_num) hcov hψ hker hperf hA hAI
    (by simpa using hcard.1)
  exact ⟨ψ, ⟨TableBU.unitaryFieldData_of_card hF (by omega), hψs, hψker⟩, hdiag⟩

theorem exists_unitaryModel_of_component_gamma
    {G : Type} [Group G] [Finite G] {F : Type} [Field F] [Finite F] {n d : ℕ}
    {Bs X J : Subgroup G} (hNX : Bs ≤ Subgroup.normalizer (X : Set G))
    (hNJ : Bs ≤ Subgroup.normalizer (J : Set G)) (hJX : J ≤ X)
    {φ : ↥(unitarySU 2 n F d) →* ↥X} (hM : UnitTB.Model φ)
    (hdiag : ∀ a ∈ (ggGamma X hNX).range, ∃ t : Fin d → F, ActsDiagU φ a t)
    (z : Bs) (hcomp : IsComponentOf (J.subgroupOf X) (ggFix (ggGamma X hNX z))) :
    ∃ m, 2 ≤ m ∧ ∃ ψ : ↥(unitarySU 2 n F m) →* ↥J,
      UnitTB.Model ψ ∧
        ∀ a ∈ (ggGamma J hNJ).range, ∃ t : Fin m → F, ActsDiagU ψ a t := by
  classical
  obtain ⟨tz, htz⟩ := hdiag (ggGamma X hNX z) ⟨z, rfl⟩
  obtain ⟨i₀, hcard, ψ₀, hM₀, hψ₀, hact₀⟩ :=
    exists_model_of_isComponentOf_ggFix hM htz hcomp
  let S := Finset.univ.filter fun i => tz i = tz i₀
  let e : ↥(J.subgroupOf X) ≃* ↥J := Subgroup.subgroupOfEquivOfLe hJX
  let ψ : ↥(unitarySU 2 n F S.card) →* ↥J := e.toMonoidHom.comp ψ₀
  have hψM : UnitTB.Model ψ := by
    refine ⟨hM₀.field, e.surjective.comp hM₀.surj, ?_⟩
    intro u hu
    have hu₀ : ψ₀ u = 1 := e.injective (by simpa [ψ] using hu)
    exact hM₀.ker u hu₀
  refine ⟨S.card, hcard, ψ, hψM, ?_⟩
  rintro a ⟨b, rfl⟩
  obtain ⟨t, ht⟩ := hdiag (ggGamma X hNX b) ⟨b, rfl⟩
  let b₀ : MulAut ↥(J.subgroupOf X) := (e.trans (ggGamma J hNJ b)).trans e.symm
  have hres : ∀ u : J.subgroupOf X, (b₀ u : X) = ggGamma X hNX b u := by
    intro u
    apply Subtype.ext
    rfl
  have ht₀ := hact₀ (ggGamma X hNX b) t ht b₀ hres
  obtain ⟨D, hD, hDt, hDa⟩ := ht₀
  refine ⟨fun i => t (S.equivFin.symm i), D, hD, hDt, fun u => ?_⟩
  have hu := congrArg e (hDa u)
  simpa [ψ, b₀, MulEquiv.trans_apply] using hu

theorem GGResHyp.exists_unitaryModel_J_of_L
    {G : Type} [Group G] [Finite G] {F : Type} [Field F] [Finite F] {n d p : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K)
    {φ : ↥(unitarySU 2 n F d) →* ↥L} (hM : UnitTB.Model φ)
    (hdiag : ∀ a ∈ (ggGamma L hH.2.2.1.1.le_normalizer).range,
      ∃ t : Fin d → F, ActsDiagU φ a t) :
    ∃ m, 2 ≤ m ∧ ∃ ψ : ↥(unitarySU 2 n F m) →* ↥J,
      UnitTB.Model ψ ∧
        ∀ a ∈ (ggGamma J hH.Bs_le_normalizer_J).range,
          ∃ t : Fin m → F, ActsDiagU ψ a t := by
  have hnb := hH.2.2.2.2.1
  have hyBs : y ∈ Bs := hH.1.2.1.1 hnb.1.2.1
  have hJL : J ≤ L := hH.1.2.2.1.2.2.2.2.2.1.1.trans inf_le_left
  exact exists_unitaryModel_of_component_gamma hH.2.2.1.1.le_normalizer
    hH.Bs_le_normalizer_J hJL hM hdiag ⟨y, hyBs⟩
    (isComponentOf_subgroupOf_ggFix_ggGamma_y hH.1 hnb hH.2.2.1.1.le_normalizer hyBs)

theorem GGResHyp.exists_unitaryModel_J_of_K
    (hLB : GGLBalanceInput) (hSP : GGStdSubPrimeInput)
    {G : Type} [Group G] [Finite G] {F : Type} [Field F] [Finite F] {n d p : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K)
    {φ : ↥(unitarySU 2 n F d) →* ↥K} (hM : UnitTB.Model φ)
    (hdiag : ∀ a ∈ (ggGamma K (hH.2.2.1.2 y K hH.2.2.2.2.1).le_normalizer).range,
      ∃ t : Fin d → F, ActsDiagU φ a t) :
    ∃ m, 2 ≤ m ∧ ∃ ψ : ↥(unitarySU 2 n F m) →* ↥J,
      UnitTB.Model ψ ∧
        ∀ a ∈ (ggGamma J hH.Bs_le_normalizer_J).range,
          ∃ t : Fin m → F, ActsDiagU ψ a t := by
  have hnb := hH.2.2.2.2.1
  have hNK := (hH.2.2.1.2 y K hnb).le_normalizer
  have hxBs : x ∈ Bs := hH.1.tableB_facts.2.2.1
  obtain ⟨hJK, hcomp⟩ := isComponentOf_comap_ggFix_ggGamma_x hLB hSP hH.1 hnb hNK hxBs
  exact exists_unitaryModel_of_component_gamma hNK hH.Bs_le_normalizer_J hJK hM hdiag
    ⟨x, hxBs⟩ hcomp

theorem GGResHyp.unitaryModel_J_degree_ge_three
    {G : Type} [Group G] [Finite G] {F : Type} [Field F] [Finite F] {n m p : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K) (hm : 2 ≤ m)
    {ψ : ↥(unitarySU 2 n F m) →* ↥J} (hM : UnitTB.Model ψ)
    (hdiag : ∀ a ∈ (ggGamma J hH.Bs_le_normalizer_J).range,
      ∃ t : Fin m → F, ActsDiagU ψ a t) : 3 ≤ m := by
  by_contra hn
  have hm2 : m = 2 := by omega
  subst m
  have hp : p.Prime := hH.1.tableB_facts.1
  have hBs : CFSG.Open.IsElemAbelian p Bs := hH.1.2.1.2.1
  have hAp : ∀ a ∈ (ggGamma J hH.Bs_le_normalizer_J).range, a ^ p = 1 := by
    rintro a ⟨b, rfl⟩
    have hb : b ^ p = 1 := Subtype.ext (hBs.2 (b : G) b.2)
    rw [← map_pow, hb, map_one]
  have hupper := UnitTB.card_diagonal_two_le hM hp hAp hdiag
  have hbad : p ^ 2 ≤ p := hH.sq_le_card_gamma_J.trans hupper
  have hp2 := hp.two_le
  simp only [pow_two] at hbad
  nlinarith

theorem GGResHyp.unitaryModel_J_degree_ge_four_qTwo
    {G : Type} [Group G] [Finite G] {F : Type} [Field F] [Finite F] {m p : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K) (hm : 2 ≤ m)
    {ψ : ↥(unitarySU 2 1 F m) →* ↥J} (hM : UnitTB.Model ψ) : 4 ≤ m := by
  by_contra hn
  have : Group.IsSolvable ↥(unitarySU 2 1 F m) :=
    SmallU.isSolvable_unitarySU_small hM.field (by omega) (by omega)
  have hsolv : Group.IsSolvable ↥J := Group.isSolvable_of_surjective hM.surj
  have hpre : LargeEvenStdSubPre p B x L D J := hH.1.2.2.1
  exact SmallU.not_isComponentOf_of_solvable hpre.2.2.2.2.2.1 hsolv

theorem GGResHyp.unitary_J_fix_mem_centralizer_of_L
    {G : Type} [Group G] [Finite G] {F : Type} [Field F] [Finite F] {n d p : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K)
    {φ : ↥(unitarySU 2 n F d) →* ↥L} (hM : UnitTB.Model φ)
    (hdiag : ∀ a ∈ (ggGamma L hH.2.2.1.1.le_normalizer).range,
      ∃ t : Fin d → F, ActsDiagU φ a t)
    (b : Bs) (hb : ∀ a ∈ ggAutomizer J Bs, a b = b) :
    (b : G) ∈ Subgroup.centralizer (J : Set G) := by
  obtain ⟨m, hm, ψ, hψ, hδ⟩ := hH.exists_unitaryModel_J_of_L hM hdiag
  exact ggUnitaryModel_fix_mem_centralizer hH.Bs_le_normalizer_J hH.1.2.1.2.1
    hH.1.2.1.2.2.2 hψ (hH.unitaryModel_J_degree_ge_three hm hψ hδ) hδ b hb

theorem GGResHyp.unitary_J_fix_mem_centralizer_of_K
    (hLB : GGLBalanceInput) (hSP : GGStdSubPrimeInput)
    {G : Type} [Group G] [Finite G] {F : Type} [Field F] [Finite F] {n d p : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K)
    {φ : ↥(unitarySU 2 n F d) →* ↥K} (hM : UnitTB.Model φ)
    (hdiag : ∀ a ∈ (ggGamma K (hH.2.2.1.2 y K hH.2.2.2.2.1).le_normalizer).range,
      ∃ t : Fin d → F, ActsDiagU φ a t)
    (b : Bs) (hb : ∀ a ∈ ggAutomizer J Bs, a b = b) :
    (b : G) ∈ Subgroup.centralizer (J : Set G) := by
  obtain ⟨m, hm, ψ, hψ, hδ⟩ := hH.exists_unitaryModel_J_of_K hLB hSP hM hdiag
  exact ggUnitaryModel_fix_mem_centralizer hH.Bs_le_normalizer_J hH.1.2.1.2.1
    hH.1.2.1.2.2.2 hψ (hH.unitaryModel_J_degree_ge_three hm hψ hδ) hδ b hb

open Matrix CFSG.ClassicalGroups.UnitaryFlag in
open CFSG.LocalAnalysis.ComponentInitial CFSG.StandardType.LineU in
theorem GGResHyp.prime_dvd_J_of_unitary_K_exactThree
    {G : Type} [Group G] [Finite G] {F : Type} [Field F] [Finite F]
    {n d p : ℕ} [Fact p.Prime] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K)
    {ψ : ↥(unitarySU 2 n F d) →* ↥K} (hM : UnitTB.Model ψ)
    (hpq : p ∣ 2 ^ n + 1) (hd : 5 ≤ d)
    (hdiag : ∀ a ∈ (ggGamma K (hH.2.2.1.2 y K hH.2.2.2.2.1).le_normalizer).range,
      ∃ t : Fin d → F, LineU.ActsDiagU ψ a t)
    (h3 : GGResLeviDatumExact3 p Bs K J L ggSelAny ggTypAny) :
    p ∣ Nat.card J := by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : d ≠ 0)
  letI : CharP F 2 := CFSG.ClassicalGroups.Unitary.charP_of_card_sq
    (p := 2) (f := n) hM.field.card_eq_sq
  have hp2 : p ≠ 2 := hH.1.1.2.2.2.2.2.1.2.1
  have hN := (hH.2.2.1.2 y K hH.2.2.2.2.1).le_normalizer
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, ⟨eK, -⟩, -⟩ :=
    exists_weyl_datum_of_diagonal_unitary_cover hM.field.card_eq_sq
      hM.field.one_le hp2 hpq (by omega : 3 ≤ r) hH.1.2.1.2.1
      hH.1.2.1.2.2.2 hN hM hdiag
  have hWK : GGWeylTypeData r (Nat.card ↥(ggAutomizer K Bs))
      (Nat.card ↥(Subgroup.center ↥(ggAutomizer K Bs))) := by
    have h0 := ggWeylTypeData_of_isWeylMatrix
      (ggHLT_weyl_A (n := r) (by omega))
    have hc := Nat.card_congr eK.toEquiv
    have hz := Nat.card_congr (Subgroup.centerCongr eK).toEquiv
    simpa [hc, hz] using h0
  exact (ggResLeviDatumCard_survivor_dvd_and_ne h3 ⟨_, hWK⟩
    (by omega : 3 < r) hH.Bs_le_normalizer_J hp2
    (fun b hb => hH.1.2.1.2.1.2 b hb)).1

open Matrix CFSG.ClassicalGroups.UnitaryFlag in
open CFSG.LocalAnalysis.ComponentInitial CFSG.StandardType.LineU in
theorem GGResHyp.unitary_J_fix_mem_centralizer_of_K_exactThree
    (hLB : GGLBalanceInput)
    {G : Type} [Group G] [Finite G] {F : Type} [Field F] [Finite F]
    {n d p : ℕ} [Fact p.Prime] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K)
    {ψ : ↥(unitarySU 2 n F d) →* ↥K} (hM : UnitTB.Model ψ)
    (hpq : p ∣ 2 ^ n + 1) (hd : 5 ≤ d)
    (hdiag : ∀ a ∈ (ggGamma K (hH.2.2.1.2 y K hH.2.2.2.2.1).le_normalizer).range,
      ∃ t : Fin d → F, LineU.ActsDiagU ψ a t)
    (h3 : GGResLeviDatumExact3 p Bs K J L ggSelAny ggTypAny)
    (b : Bs) (hb : ∀ a ∈ ggAutomizer J Bs, a b = b) :
    (b : G) ∈ Subgroup.centralizer (J : Set G) := by
  have hpJ := hH.prime_dvd_J_of_unitary_K_exactThree hM hpq hd hdiag h3
  have hnb := hH.2.2.2.2.1
  have hNK := (hH.2.2.1.2 y K hnb).le_normalizer
  have hxBs : x ∈ Bs := hH.1.tableB_facts.2.2.1
  obtain ⟨hJK, hcomp⟩ :=
    isComponentOf_comap_ggFix_ggGamma_x_of_dvd hLB hH.1 hpJ hnb hNK hxBs
  obtain ⟨m, hm, φJ, hJ, hδ⟩ :=
    exists_unitaryModel_of_component_gamma hNK hH.Bs_le_normalizer_J hJK hM hdiag
      ⟨x, hxBs⟩ hcomp
  exact ggUnitaryModel_fix_mem_centralizer hH.Bs_le_normalizer_J hH.1.2.1.2.1
    hH.1.2.1.2.2.2 hJ (hH.unitaryModel_J_degree_ge_three hm hJ hδ) hδ b hb


theorem exists_root_kernel_of_centralizing
    {G : Type} [Group G] {p : ℕ} [Fact p.Prime]
    {Bs X : Subgroup G} {Λ : Type} {C : Matrix Λ Λ ℤ}
    {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    {ι : Additive ↥Bs ≃+ V} {φ : Λ → MulAut ↥Bs} {h : Λ → V}
    {α : Λ → Module.Dual (ZMod p) V}
    (hp2 : p ≠ 2)
    (hlin : ∀ i w, ggLin (p := p) ι (φ i) w = w - α i w • h i)
    (hpair : ∀ i j, α i (h j) = (C i j : ZMod p))
    (hdiag : ∀ i, C i i = 2)
    (hgen : ggAutomizer X Bs = Subgroup.closure (Set.range φ))
    {g : G} (hgBs : g ∈ Bs) (hg1 : g ≠ 1)
    (hgX : X ≤ Subgroup.centralizer ({g} : Set G)) :
    ∃ v : V, v ≠ 0 ∧ ∀ i, α i v = 0 := by
  classical
  let v : V := ι (Additive.ofMul (⟨g, hgBs⟩ : ↥Bs))
  have hv : v ≠ 0 := by
    intro h0
    have h1 : (⟨g, hgBs⟩ : ↥Bs) = 1 := by
      apply Additive.ofMul.injective
      exact ι.injective (by simpa [v] using h0)
    exact hg1 (by simpa using congrArg Subtype.val h1)
  have hαv : ∀ i, α i v = 0 := by
    intro i
    have hmem : φ i ∈ ggAutomizer X Bs := by
      rw [hgen]
      exact Subgroup.subset_closure ⟨i, rfl⟩
    have hfix : φ i ⟨g, hgBs⟩ = ⟨g, hgBs⟩ :=
      ggResI_automizer_fix hgBs hgX (φ i) hmem
    have hfixlin : ggLin (p := p) ι (φ i) v = v := by
      dsimp only [v]
      exact (ggLin_fix_iff (p := p) ι (φ i) ⟨g, hgBs⟩).mp hfix
    refine ggResI_alpha_eq_zero (p := p) hp2 (hlin i) ?_ hfixlin
    rw [hpair i i, hdiag i]
    norm_num
  exact ⟨v, hv, hαv⟩

theorem GGResHyp.unitary_exactThree_singular_chart_of_L
    {G : Type} [Group G] [Finite G] {F : Type} [Field F] [Finite F] {n d p : ℕ}
    [Fact p.Prime] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K)
    {φU : ↥(unitarySU 2 n F d) →* ↥L} (hM : UnitTB.Model φU)
    (hdiag : ∀ a ∈ (ggGamma L hH.2.2.1.1.le_normalizer).range,
      ∃ t : Fin d → F, ActsDiagU φU a t)
    {Λ : Type} [Fintype Λ] [DecidableEq Λ] {M : CoxeterMatrix Λ} {C : Matrix Λ Λ ℤ}
    {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    (ι : Additive ↥Bs ≃+ V) (φ : Λ → MulAut ↥Bs) (h : Λ → V)
    (α : Λ → Module.Dual (ZMod p) V) (hWM : GGIsWeylMatrix M) (hC : GGIntCartan M C)
    (hlin : ∀ i w, ggLin (p := p) ι (φ i) w = w - α i w • h i)
    (hrefl : ∀ i, GGIsReflection p (φ i))
    (hpair : ∀ i j, α i (h j) = (C i j : ZMod p))
    (hCdiag : ∀ i, C i i = 2)
    (hgenX : ggAutomizer L Bs = Subgroup.closure (Set.range φ))
    (S : Finset Λ) (hS : S.card = 3)
    (hgenJ : ggAutomizer J Bs =
      Subgroup.closure (Set.range fun i : {i : Λ // i ∉ S} => φ i.1)) :
    Module.finrank (ZMod p) V = Fintype.card Λ ∧
      Matrix.rank (C.map (Int.castRingHom (ZMod p))) + 1 = Fintype.card Λ ∧
      Module.finrank (ZMod p)
        (LinearMap.ker (LinearMap.pi fun i : {i : Λ // i ∉ S} => α i.1)) = 3 ∧
      ((GGIsTypeA M ∧ p ∣ Fintype.card Λ + 1) ∨ (p = 3 ∧ GGIsTypeE6 M)) ∧
      Nat.card ↥(Bs ⊓ Subgroup.centralizer (J : Set G)) = p ^ 3 ∧ B < Bs := by
  have hp2 : p ≠ 2 := hH.1.1.2.2.2.2.2.1.2.1
  have hSstar : LargeEvenSStar p B x L := hH.1.1.2.2.2.2.2.2.1
  have hxBs : x ∈ Bs := hH.1.2.1.1 hSstar.2.1
  have hx1 : x ≠ 1 := hSstar.2.2.1
  have hxL : L ≤ Subgroup.centralizer ({x} : Set G) := hSstar.2.2.2.1.1
  obtain ⟨v, hv, hvα⟩ :=
    exists_root_kernel_of_centralizing (p := p) hp2 hlin hpair hCdiag hgenX hxBs hx1 hxL
  exact ggRes_exactThree_singular_chart hH.1 ι φ h α hWM hC hlin hrefl hpair hv hvα S hS
    hgenJ (hH.unitary_J_fix_mem_centralizer_of_L hM hdiag)

theorem GGResHyp.unitary_exactThree_singular_chart_of_K
    (hLB : GGLBalanceInput) (hSP : GGStdSubPrimeInput)
    {G : Type} [Group G] [Finite G] {F : Type} [Field F] [Finite F] {n d p : ℕ}
    [Fact p.Prime] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K)
    {φU : ↥(unitarySU 2 n F d) →* ↥K} (hM : UnitTB.Model φU)
    (hdiag : ∀ a ∈ (ggGamma K (hH.2.2.1.2 y K hH.2.2.2.2.1).le_normalizer).range,
      ∃ t : Fin d → F, ActsDiagU φU a t)
    {Λ : Type} [Fintype Λ] [DecidableEq Λ] {M : CoxeterMatrix Λ} {C : Matrix Λ Λ ℤ}
    {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    (ι : Additive ↥Bs ≃+ V) (φ : Λ → MulAut ↥Bs) (h : Λ → V)
    (α : Λ → Module.Dual (ZMod p) V) (hWM : GGIsWeylMatrix M) (hC : GGIntCartan M C)
    (hlin : ∀ i w, ggLin (p := p) ι (φ i) w = w - α i w • h i)
    (hrefl : ∀ i, GGIsReflection p (φ i))
    (hpair : ∀ i j, α i (h j) = (C i j : ZMod p))
    (hCdiag : ∀ i, C i i = 2)
    (hgenX : ggAutomizer K Bs = Subgroup.closure (Set.range φ))
    (S : Finset Λ) (hS : S.card = 3)
    (hgenJ : ggAutomizer J Bs =
      Subgroup.closure (Set.range fun i : {i : Λ // i ∉ S} => φ i.1)) :
    Module.finrank (ZMod p) V = Fintype.card Λ ∧
      Matrix.rank (C.map (Int.castRingHom (ZMod p))) + 1 = Fintype.card Λ ∧
      Module.finrank (ZMod p)
        (LinearMap.ker (LinearMap.pi fun i : {i : Λ // i ∉ S} => α i.1)) = 3 ∧
      ((GGIsTypeA M ∧ p ∣ Fintype.card Λ + 1) ∨ (p = 3 ∧ GGIsTypeE6 M)) ∧
      Nat.card ↥(Bs ⊓ Subgroup.centralizer (J : Set G)) = p ^ 3 ∧ B < Bs := by
  have hp2 : p ≠ 2 := hH.1.1.2.2.2.2.2.1.2.1
  have hSHat : LargeEvenSHat p B y K := hH.2.2.2.2.1.1
  have hyBs : y ∈ Bs := hH.1.2.1.1 hSHat.2.1
  have hy1 : y ≠ 1 := hSHat.2.2.1
  have hyK : K ≤ Subgroup.centralizer ({y} : Set G) := hSHat.2.2.2.1
  obtain ⟨v, hv, hvα⟩ :=
    exists_root_kernel_of_centralizing (p := p) hp2 hlin hpair hCdiag hgenX hyBs hy1 hyK
  exact ggRes_exactThree_singular_chart hH.1 ι φ h α hWM hC hlin hrefl hpair hv hvα S hS
    hgenJ (hH.unitary_J_fix_mem_centralizer_of_K hLB hSP hM hdiag)

theorem card_ggAutomizer_eq_factorial_of_unitaryModel
    {G : Type} [Group G] [Finite G] {F : Type} [Field F] [Finite F]
    {n d p : ℕ} [Fact p.Prime] {Bs X : Subgroup G}
    (hBs : IsElemAbelian p Bs)
    (hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs)
    (hN : Bs ≤ Subgroup.normalizer (X : Set G))
    {ψ : ↥(unitarySU 2 n F d) →* ↥X} (hM : UnitTB.Model ψ)
    (hF : Nat.card F = (2 ^ n) ^ 2) (hp2 : p ≠ 2) (hpq : p ∣ 2 ^ n + 1)
    (hd : 4 ≤ d)
    (hdiag : ∀ a ∈ (ggGamma X hN).range, ∃ t : Fin d → F, LineU.ActsDiagU ψ a t) :
    Nat.card (ggAutomizer X Bs) = d.factorial := by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : d ≠ 0)
  have hA : IsElemAbelian p (ggGamma X hN).range := isElemAbelian_range
    (fun a b : Bs => hBs.1.is_comm.comm a b)
    (fun b : Bs => Subtype.ext (by simpa using hBs.2 b b.2)) (ggGamma X hN)
  have hTor := ggTorusTorData_of_model_U hF (Fact.out : p.Prime) hp2 hpq (by omega : 3 ≤ r)
    hM hA (ggTorusSelfCent_ggGamma hN hSC) hdiag
  have hodd : Odd (2 ^ n + 1) := by
    have hn : n ≠ 0 := by
      intro he
      rw [he] at hpq
      exact hp2 ((Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) Nat.prime_two).mp (by simpa using hpq))
    obtain ⟨f, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
    rw [pow_succ]
    exact ⟨2 ^ f, by omega⟩
  obtain ⟨φ, e, -, -⟩ := ggTBWeyl_of_torW hp2 hodd hpq hBs hSC hN hTor
  obtain ⟨eP, -⟩ := ggCoxeterA_mulEquivPerm r
  rw [← Nat.card_congr e.toEquiv, Nat.card_congr eP.toEquiv, Nat.card_perm, Nat.card_fin]

theorem factorial_le_card_ggAutomizer_of_unitaryModel_coprime
    {G : Type} [Group G] [Finite G] {F : Type} [Field F] [Finite F]
    {n d p : ℕ} [Fact p.Prime] {Bs X : Subgroup G}
    (hBs : IsElemAbelian p Bs)
    (hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs)
    (hN : Bs ≤ Subgroup.normalizer (X : Set G))
    {ψ : ↥(unitarySU 2 n F d) →* ↥X} (hM : UnitTB.Model ψ)
    (hp2 : p ≠ 2) (hpq : p ∣ 2 ^ n + 1) (hd : 3 ≤ d) (hcp : Nat.Coprime d p)
    (hdiag : ∀ a ∈ (ggGamma X hN).range,
      ∃ t : Fin d → F, LineU.ActsDiagU ψ a t) :
    d.factorial ≤ Nat.card (ggAutomizer X Bs) := by
  classical
  let A := (ggGamma X hN).range
  have hp : p.Prime := Fact.out
  have hA : IsElemAbelian p A := isElemAbelian_range
    (fun a b : Bs => hBs.1.is_comm.comm a b)
    (fun b : Bs => Subtype.ext (by simpa using hBs.2 b b.2)) (ggGamma X hN)
  have hsc : GGTorusSelfCent p A := ggTorusSelfCent_ggGamma hN hSC
  have hn : ∀ σ : Equiv.Perm (Fin d),
      MulAut.conj (ψ (LineU.permSU hM.field σ)) ∈
        Subgroup.normalizer (A : Set (MulAut X)) :=
    fun σ => unitDvd_conj_perm_mem_normalizer hM hp hpq hd hA.2 hsc hdiag σ
  let ρ : Equiv.Perm (Fin d) →* MulAut ↥A :=
    { toFun := fun σ => ggConjAut A (hn σ)
      map_one' := by
        refine MulEquiv.ext fun b => Subtype.ext ?_
        simp [ggConjAut_apply, UnitAct.permSU_one]
      map_mul' := by
        intro σ τ
        refine MulEquiv.ext fun b => Subtype.ext ?_
        simp only [ggConjAut_apply, MulAut.mul_apply, UnitAct.permSU_mul, map_mul]
        group }
  have hρ : Function.Injective ρ := by
    refine (injective_iff_map_eq_one ρ).mpr fun σ hσ => ?_
    refine UnitTB.permSU_eq_one_of_conj_comm_of_coprime hM hp hp2 hpq hd hcp
      hsc hdiag fun b hb => ?_
    have h := congrArg (fun f : MulAut ↥A => ((f ⟨b, hb⟩ : ↥A) : MulAut X)) hσ
    simpa [ρ, ggConjAut_apply] using h
  let g : ggAutomizer X Bs →* MulAut ↥A :=
    (ggAutomizer (MulAut.conj : X →* MulAut X).range A).subtype.comp
      (ggAutomizerGammaHom hN)
  have hlift : ∀ σ : Equiv.Perm (Fin d), ∃ c : ggAutomizer X Bs, g c = ρ σ := by
    intro σ
    have hw : ρ σ ∈ ggTorusWeylAut p A :=
      ⟨ψ (LineU.permSU hM.field σ), hn σ,
        LineU.weyl_W_prop hM.field hd hM.ker hA.2 hdiag _ ⟨σ, rfl⟩, rfl⟩
    rw [← ggAutomizerGammaHom_range hBs hSC hN] at hw
    obtain ⟨c, hc, he⟩ := Subgroup.mem_map.mp hw
    obtain ⟨b, rfl⟩ := hc
    exact ⟨b, he⟩
  let f : Equiv.Perm (Fin d) → ggAutomizer X Bs := fun σ => Classical.choose (hlift σ)
  have hf : Function.Injective f := by
    intro σ τ he
    apply hρ
    rw [← Classical.choose_spec (hlift σ), ← Classical.choose_spec (hlift τ)]
    exact congrArg g he
  have hc := Nat.card_le_card_of_injective f hf
  rw [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin] at hc
  exact hc

theorem GGResXDatumA.unitary_degree_eq
    {G : Type} [Group G] [Finite G] {F : Type} [Field F] [Finite F]
    {n d p r : ℕ} [Fact p.Prime] {Bs X : Subgroup G}
    (hBs : IsElemAbelian p Bs)
    (hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs)
    (hN : Bs ≤ Subgroup.normalizer (X : Set G))
    {ψ : ↥(unitarySU 2 n F d) →* ↥X} (hM : UnitTB.Model ψ)
    (hF : Nat.card F = (2 ^ n) ^ 2) (hp2 : p ≠ 2) (hpq : p ∣ 2 ^ n + 1)
    (hd : 5 ≤ d)
    (hdiag : ∀ a ∈ (ggGamma X hN).range, ∃ t : Fin d → F, LineU.ActsDiagU ψ a t)
    (hD : GGResXDatumA p Bs X r) : d = r + 1 := by
  have hc : d.factorial = (r + 1).factorial :=
    (card_ggAutomizer_eq_factorial_of_unitaryModel hBs hSC hN hM hF hp2 hpq (by omega) hdiag).symm.trans
      hD.card_automizer
  exact (Nat.factorial_inj (by omega : 1 < d)).mp hc

theorem not_typeE6_of_unitaryModel
    {G : Type} [Group G] [Finite G] {F : Type} [Field F] [Finite F]
    {n d p : ℕ} [Fact p.Prime] {Bs X : Subgroup G}
    (hBs : IsElemAbelian p Bs)
    (hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs)
    (hN : Bs ≤ Subgroup.normalizer (X : Set G))
    {ψ : ↥(unitarySU 2 n F d) →* ↥X} (hM : UnitTB.Model ψ)
    (hF : Nat.card F = (2 ^ n) ^ 2) (hp2 : p ≠ 2) (hpq : p ∣ 2 ^ n + 1)
    (hd : 5 ≤ d)
    (hdiag : ∀ a ∈ (ggGamma X hN).range, ∃ t : Fin d → F, LineU.ActsDiagU ψ a t)
    {Λ : Type} {M : CoxeterMatrix Λ}
    (f : M.Group ≃* ↥(ggAutomizer X Bs)) : ¬ GGIsTypeE6 M := by
  intro hE
  have hc : d.factorial = 51840 :=
    (card_ggAutomizer_eq_factorial_of_unitaryModel hBs hSC hN hM hF hp2 hpq (by omega) hdiag).symm.trans
      (card_ggAutomizer_of_typeE6 hE f)
  by_cases hd8 : d ≤ 8
  · have hh := Nat.factorial_le hd8
    norm_num at hh
    omega
  · have hh := Nat.factorial_le (show 9 ≤ d by omega)
    norm_num at hh
    omega

theorem GGResHyp.unitary_exactThree_typeA_card_J_of_L
    {G : Type} [Group G] [Finite G] {F : Type} [Field F] [Finite F]
    {n d p : ℕ} [Fact p.Prime] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K)
    {ψ : ↥(unitarySU 2 n F d) →* ↥L} (hM : UnitTB.Model ψ)
    (hpq : p ∣ 2 ^ n + 1) (hd : 5 ≤ d)
    (hdiag : ∀ a ∈ (ggGamma L hH.2.2.1.1.le_normalizer).range,
      ∃ t : Fin d → F, LineU.ActsDiagU ψ a t)
    (h3 : GGResLeviDatumExact3 p Bs L J K ggSelAny ggTypAny) :
    ∃ r : ℕ, d = r + 1 ∧ p ∣ d ∧ GGResXDatumA p Bs L r ∧
      Nat.card Bs = p ^ r ∧
      Nat.card ↥(Bs ⊓ Subgroup.centralizer (J : Set G)) = p ^ 3 ∧ B < Bs ∧
      Nat.card (ggAutomizer J Bs) = (r - 2).factorial := by
  classical
  obtain ⟨Λ, i1, i2, S, Λa, i3, i4, ML, CL, MK, CK, V, i5, i6, ι, φ, h, α,
    hS3, hA1, hA3, hWML, hCLL, hWMK, hCKK, htyp, hlin, hrefl, hpairL, hpairK, hsel,
    hfLx, hfKx, hclosL, hclosK, hdel, hclosJ⟩ := h3
  let := i1
  let := i2
  let := i3
  let := i4
  let := i5
  let := i6
  obtain ⟨fL, hfL⟩ := hfLx
  have hp2 : p ≠ 2 := hH.1.1.2.2.2.2.2.1.2.1
  have hBs := hH.1.2.1.2.1
  have hSC := hH.1.2.1.2.2.2
  have hN := hH.2.2.1.1.le_normalizer
  obtain ⟨hdim, hrank, hker, hsing, hcent, hlt⟩ :=
    hH.unitary_exactThree_singular_chart_of_L hM hdiag ι
      (fun i => φ (Sum.inl i)) (fun i => h (Sum.inl i)) (fun i => α (Sum.inl i))
      hWML hCLL (fun i => hlin (Sum.inl i)) (fun i => hrefl (Sum.inl i))
      hpairL hCLL.1 hclosL S hS3 hclosJ
  have hne : ¬ GGIsTypeE6 ML :=
    not_typeE6_of_unitaryModel hBs hSC hN hM hM.field.card_eq_sq hp2 hpq hd hdiag fL
  have hA : GGIsTypeA ML ∧ p ∣ Fintype.card Λ + 1 := by
    rcases hsing with hA | hE
    · exact hA
    · exact (hne hE.2).elim
  obtain ⟨r, e, hr, he⟩ := hA.1
  have hD : GGResXDatumA p Bs L r :=
    ⟨Λ, i1, i2, ML, CL, V, i5, i6, ι, (fun i => φ (Sum.inl i)),
      (fun i => h (Sum.inl i)), (fun i => α (Sum.inl i)), e, he, hWML, hCLL,
      (fun i => hlin (Sum.inl i)), (fun i => hrefl (Sum.inl i)), hpairL, ⟨fL, hfL⟩, hclosL⟩
  have hdegree : d = r + 1 := hD.unitary_degree_eq hBs hSC hN hM hM.field.card_eq_sq hp2 hpq hd hdiag
  have hΛ : Fintype.card Λ = r := by
    have hc := Nat.card_congr e
    simpa using hc.symm
  have hp : p ∣ d := by simpa [hΛ, hdegree] using hA.2
  have : Finite V := Finite.of_equiv (Additive ↥Bs) ι.toEquiv
  have hcard : Nat.card Bs = p ^ r := by
    rw [card_eq_of_ggLin ι, ← FiniteField.pow_finrank_eq_natCard p V, hdim, hΛ]
  have hr3 : 3 < r := by omega
  let fA : ((CoxeterMatrix.A r).reindex e).Group ≃* ggAutomizer L Bs := he ▸ fL
  have hfA : ∀ i, (fA (((CoxeterMatrix.A r).reindex e).simple i) : MulAut Bs) =
      φ (Sum.inl i) := by
    cases he
    simpa only [fA] using hfL
  have hconn : GGDeletedConnectedS ((CoxeterMatrix.A r).reindex e) S := he ▸ hdel
  have hc := ggRes_typeA_deletedS_card_automizer hr3 e S hS3 hconn
    (fun i => φ (Sum.inl i)) fA hfA hclosJ
  have hc' : Nat.card (ggAutomizer J Bs) = (r - 2).factorial := by
    convert hc using 1
    congr 1
    omega
  exact ⟨r, hdegree, hp, hD, hcard, hcent, hlt, hc'⟩


theorem GGResHyp.unitary_exactThree_typeA_of_L
    {G : Type} [Group G] [Finite G] {F : Type} [Field F] [Finite F]
    {n d p : ℕ} [Fact p.Prime] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K)
    {ψ : ↥(unitarySU 2 n F d) →* ↥L} (hM : UnitTB.Model ψ)
    (hpq : p ∣ 2 ^ n + 1) (hd : 5 ≤ d)
    (hdiag : ∀ a ∈ (ggGamma L hH.2.2.1.1.le_normalizer).range,
      ∃ t : Fin d → F, LineU.ActsDiagU ψ a t)
    (h3 : GGResLeviDatumExact3 p Bs L J K ggSelAny ggTypAny) :
    ∃ r : ℕ, d = r + 1 ∧ p ∣ d ∧ GGResXDatumA p Bs L r ∧
      Nat.card Bs = p ^ r ∧
      Nat.card ↥(Bs ⊓ Subgroup.centralizer (J : Set G)) = p ^ 3 ∧ B < Bs := by
  obtain ⟨r, hd, hp, hD, hcard, hcent, hlt, _⟩ :=
    hH.unitary_exactThree_typeA_card_J_of_L hM hpq hd hdiag h3
  exact ⟨r, hd, hp, hD, hcard, hcent, hlt⟩

theorem GGResHyp.unitary_exactThree_J_degree_qTwo_of_L
    {G : Type} [Group G] [Finite G] {F : Type} [Field F] [Finite F]
    {d m p r : ℕ} [Fact p.Prime] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K)
    {ψ : ↥(unitarySU 2 1 F d) →* ↥L} (hM : UnitTB.Model ψ)
    (hpq : p ∣ 2 ^ 1 + 1) (hd : 5 ≤ d)
    (hdiag : ∀ a ∈ (ggGamma L hH.2.2.1.1.le_normalizer).range,
      ∃ t : Fin d → F, LineU.ActsDiagU ψ a t)
    {δ : ↥(unitarySU 2 1 F m) →* ↥J} (hm : 2 ≤ m) (hδ : UnitTB.Model δ)
    (hδdiag : ∀ a ∈ (ggGamma J hH.Bs_le_normalizer_J).range,
      ∃ t : Fin m → F, LineU.ActsDiagU δ a t)
    {Λ : Type} [Fintype Λ] [DecidableEq Λ] (e : Fin r ≃ Λ)
    (S : Finset Λ) (hS : S.card = 3) (hr : 3 < r)
    (hconn : GGDeletedConnectedS ((CoxeterMatrix.A r).reindex e) S)
    (φ : Λ → MulAut Bs)
    (f : ((CoxeterMatrix.A r).reindex e).Group ≃* ggAutomizer L Bs)
    (hf : ∀ i, (f (((CoxeterMatrix.A r).reindex e).simple i) : MulAut Bs) = φ i)
    (hclosJ : ggAutomizer J Bs = Subgroup.closure
      (Set.range fun i : {i : Λ // i ∉ S} => φ i.val)) : m = d - 3 := by
  have hp2 : p ≠ 2 := hH.1.1.2.2.2.2.2.1.2.1
  have hcardL := card_ggAutomizer_eq_factorial_of_unitaryModel hH.1.2.1.2.1
    hH.1.2.1.2.2.2 hH.2.2.1.1.le_normalizer hM hM.field.card_eq_sq hp2 hpq (by omega) hdiag
  have hcardA : Nat.card (ggAutomizer L Bs) = (r + 1).factorial := by
    rw [← Nat.card_congr f.toEquiv]
    rw [Nat.card_congr
      (CoxeterMatrix.reindexGroupEquiv (CoxeterMatrix.A r) e).toEquiv]
    exact l05nK3a_card_coxeterA r
  have hdEq : d = r + 1 :=
    (Nat.factorial_inj (by omega : 1 < d)).mp (hcardL.symm.trans hcardA)
  have hm4 := hH.unitaryModel_J_degree_ge_four_qTwo hm hδ
  have hcardJ := card_ggAutomizer_eq_factorial_of_unitaryModel hH.1.2.1.2.1
    hH.1.2.1.2.2.2 hH.Bs_le_normalizer_J hδ hδ.field.card_eq_sq hp2 hpq hm4 hδdiag
  have hc := ggRes_typeA_deletedS_card_automizer hr e S hS hconn φ f hf hclosJ
  have hmEq : m = r - 3 + 1 :=
    (Nat.factorial_inj (by omega : 1 < m)).mp (hcardJ.symm.trans hc)
  omega

theorem GGResHyp.unitary_exactThree_J_model_qTwo_of_L
    {G : Type} [Group G] [Finite G] {F : Type} [Field F] [Finite F]
    {d p : ℕ} [Fact p.Prime] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K)
    {ψ : ↥(unitarySU 2 1 F d) →* ↥L} (hM : UnitTB.Model ψ)
    (hpq : p ∣ 2 ^ 1 + 1) (hd : 5 ≤ d)
    (hdiag : ∀ a ∈ (ggGamma L hH.2.2.1.1.le_normalizer).range,
      ∃ t : Fin d → F, LineU.ActsDiagU ψ a t)
    (h3 : GGResLeviDatumExact3 p Bs L J K ggSelAny ggTypAny) :
    p = 3 ∧ 3 ∣ d ∧ 9 ≤ d ∧
      ∃ δ : ↥(unitarySU 2 1 F (d - 3)) →* ↥J, UnitTB.Model δ ∧
        ∀ a ∈ (ggGamma J hH.Bs_le_normalizer_J).range,
          ∃ t : Fin (d - 3) → F, LineU.ActsDiagU δ a t := by
  obtain ⟨r, hdegree, hpd, _, _, _, _, hAJ⟩ :=
    hH.unitary_exactThree_typeA_card_J_of_L hM hpq hd hdiag h3
  have hp3 : p = 3 := (Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) Nat.prime_three).mp
    (by simpa using hpq)
  obtain ⟨m, hm, δ, hδ, hδdiag⟩ := hH.exists_unitaryModel_J_of_L hM hdiag
  have hm4 := hH.unitaryModel_J_degree_ge_four_qTwo hm hδ
  have hp2 : p ≠ 2 := hH.1.1.2.2.2.2.2.1.2.1
  have hc := card_ggAutomizer_eq_factorial_of_unitaryModel hH.1.2.1.2.1
    hH.1.2.1.2.2.2 hH.Bs_le_normalizer_J hδ hδ.field.card_eq_sq hp2 hpq hm4 hδdiag
  have hmEq : m = r - 2 :=
    (Nat.factorial_inj (by omega : 1 < m)).mp (hc.symm.trans hAJ)
  have hmdeg : m = d - 3 := by omega
  have hdiv : 3 ∣ d := hp3 ▸ hpd
  have hd9 : 9 ≤ d := by
    obtain ⟨t, ht⟩ := hdiv
    omega
  cases hmdeg
  exact ⟨hp3, hdiv, hd9, δ, hδ, hδdiag⟩

theorem GGResHyp.unitary_exactThree_reserved_row_qTwo_of_L
    {G : Type} [Group G] [Finite G] {F : Type} [Field F] [Finite F]
    {d p : ℕ} [Fact p.Prime] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K)
    {ψ : ↥(unitarySU 2 1 F d) →* ↥L} (hM : UnitTB.Model ψ)
    (hpq : p ∣ 2 ^ 1 + 1) (hd : 5 ≤ d)
    (hdiag : ∀ a ∈ (ggGamma L hH.2.2.1.1.le_normalizer).range,
      ∃ t : Fin d → F, LineU.ActsDiagU ψ a t)
    (h3 : GGResLeviDatumExact3 p Bs L J K ggSelAny ggTypAny) :
    GGResRowAt ggRowSUCorank3 p J L := by
  obtain ⟨hp3, hdiv, hd9, δ, hδ, _⟩ :=
    hH.unitary_exactThree_J_model_qTwo_of_L hM hpq hd hdiag h3
  have hJLabel := ggHasLabel_of_unitaryModel hδ (by omega : 3 ≤ d - 3)
    (by
      intro h
      have hfst := congrArg Prod.fst h
      omega)
  have hLLabel := ggHasLabel_of_unitaryModel hM (by omega : 3 ≤ d)
    (by
      intro h
      have hfst := congrArg Prod.fst h
      omega)
  refine ⟨⟨.twA, d - 3 - 1, 1⟩, ⟨.twA, d - 1, 1⟩, ?_, ?_, hJLabel, hLLabel, ?_⟩
  · exact ⟨by norm_num, by change 2 ≤ d - 3 - 1; omega,
      by change d - 3 - 1 = 2 → 2 ≤ 1; intro h; omega⟩
  · exact ⟨by norm_num, by change 2 ≤ d - 1; omega,
      by change d - 1 = 2 → 2 ≤ 1; intro h; omega⟩
  · change p = 3 ∧ LargeEvenLieTag.twA = .twA ∧ 1 = 1 ∧
      LargeEvenLieTag.twA = .twA ∧ 1 = 1 ∧
      d - 1 = d - 3 - 1 + 3 ∧ 8 ≤ d - 1 ∧ 3 ∣ d - 1 + 1
    exact ⟨hp3, rfl, rfl, rfl, rfl, by omega, by omega,
      by simpa [Nat.sub_add_cancel (by omega : 1 ≤ d)] using hdiv⟩

theorem GGResHyp.unitary_exactThree_typeA_card_J_of_K
    (hLB : GGLBalanceInput)
    {G : Type} [Group G] [Finite G] {F : Type} [Field F] [Finite F]
    {n d p : ℕ} [Fact p.Prime] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K)
    {ψ : ↥(unitarySU 2 n F d) →* ↥K} (hM : UnitTB.Model ψ)
    (hpq : p ∣ 2 ^ n + 1) (hd : 5 ≤ d)
    (hdiag : ∀ a ∈ (ggGamma K (hH.2.2.1.2 y K hH.2.2.2.2.1).le_normalizer).range,
      ∃ t : Fin d → F, LineU.ActsDiagU ψ a t)
    (h3 : GGResLeviDatumExact3 p Bs K J L ggSelAny ggTypAny) :
    ∃ r : ℕ, d = r + 1 ∧ p ∣ d ∧ GGResXDatumA p Bs K r ∧
      Nat.card Bs = p ^ r ∧
      Nat.card ↥(Bs ⊓ Subgroup.centralizer (J : Set G)) = p ^ 3 ∧ B < Bs ∧
      Nat.card (ggAutomizer J Bs) = (r - 2).factorial := by
  classical
  have hfwd := hH.unitary_J_fix_mem_centralizer_of_K_exactThree hLB hM hpq hd hdiag h3
  obtain ⟨Λ, i1, i2, S, Λa, i3, i4, ML, CL, MK, CK, V, i5, i6, ι, φ, h, α,
    hS3, hA1, hA3, hWML, hCLL, hWMK, hCKK, htyp, hlin, hrefl, hpairL, hpairK, hsel,
    hfLx, hfKx, hclosL, hclosK, hdel, hclosJ⟩ := h3
  let := i1
  let := i2
  let := i3
  let := i4
  let := i5
  let := i6
  obtain ⟨fL, hfL⟩ := hfLx
  have hp2 : p ≠ 2 := hH.1.1.2.2.2.2.2.1.2.1
  have hBs := hH.1.2.1.2.1
  have hSC := hH.1.2.1.2.2.2
  have hN := (hH.2.2.1.2 y K hH.2.2.2.2.1).le_normalizer
  obtain ⟨hdim, hrank, hker, hsing, hcent, hlt⟩ :=
    ggRes_exactThree_singular_chart_of_axis_bound hH.1 ι
      (fun i => φ (Sum.inl i)) (fun i => h (Sum.inl i)) (fun i => α (Sum.inl i))
      hWML hCLL (fun i => hlin (Sum.inl i)) (fun i => hrefl (Sum.inl i))
      hpairL (ggResK_rank_core_add_one hH (fun i => hlin (Sum.inl i))
        hpairL hCLL.1 hclosL) S hS3 hclosJ hfwd
  have hne : ¬ GGIsTypeE6 ML :=
    not_typeE6_of_unitaryModel hBs hSC hN hM hM.field.card_eq_sq hp2 hpq hd hdiag fL
  have hA : GGIsTypeA ML ∧ p ∣ Fintype.card Λ + 1 := by
    rcases hsing with hA | hE
    · exact hA
    · exact (hne hE.2).elim
  obtain ⟨r, e, hr, he⟩ := hA.1
  have hD : GGResXDatumA p Bs K r :=
    ⟨Λ, i1, i2, ML, CL, V, i5, i6, ι, (fun i => φ (Sum.inl i)),
      (fun i => h (Sum.inl i)), (fun i => α (Sum.inl i)), e, he, hWML, hCLL,
      (fun i => hlin (Sum.inl i)), (fun i => hrefl (Sum.inl i)), hpairL, ⟨fL, hfL⟩, hclosL⟩
  have hdegree : d = r + 1 := hD.unitary_degree_eq hBs hSC hN hM hM.field.card_eq_sq hp2 hpq hd hdiag
  have hΛ : Fintype.card Λ = r := by
    have hc := Nat.card_congr e
    simpa using hc.symm
  have hp : p ∣ d := by simpa [hΛ, hdegree] using hA.2
  have : Finite V := Finite.of_equiv (Additive ↥Bs) ι.toEquiv
  have hcard : Nat.card Bs = p ^ r := by
    rw [card_eq_of_ggLin ι, ← FiniteField.pow_finrank_eq_natCard p V, hdim, hΛ]
  have hr3 : 3 < r := by omega
  let fA : ((CoxeterMatrix.A r).reindex e).Group ≃* ggAutomizer K Bs := he ▸ fL
  have hfA : ∀ i, (fA (((CoxeterMatrix.A r).reindex e).simple i) : MulAut Bs) =
      φ (Sum.inl i) := by
    cases he
    simpa only [fA] using hfL
  have hconn : GGDeletedConnectedS ((CoxeterMatrix.A r).reindex e) S := he ▸ hdel
  have hc := ggRes_typeA_deletedS_card_automizer hr3 e S hS3 hconn
    (fun i => φ (Sum.inl i)) fA hfA hclosJ
  have hc' : Nat.card (ggAutomizer J Bs) = (r - 2).factorial := by
    convert hc using 1
    congr 1
    omega
  exact ⟨r, hdegree, hp, hD, hcard, hcent, hlt, hc'⟩



theorem GGResHyp.unitary_exactThree_typeA_of_K
    (hLB : GGLBalanceInput)
    {G : Type} [Group G] [Finite G] {F : Type} [Field F] [Finite F]
    {n d p : ℕ} [Fact p.Prime] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K)
    {ψ : ↥(unitarySU 2 n F d) →* ↥K} (hM : UnitTB.Model ψ)
    (hpq : p ∣ 2 ^ n + 1) (hd : 5 ≤ d)
    (hdiag : ∀ a ∈ (ggGamma K (hH.2.2.1.2 y K hH.2.2.2.2.1).le_normalizer).range,
      ∃ t : Fin d → F, LineU.ActsDiagU ψ a t)
    (h3 : GGResLeviDatumExact3 p Bs K J L ggSelAny ggTypAny) :
    ∃ r : ℕ, d = r + 1 ∧ p ∣ d ∧ GGResXDatumA p Bs K r ∧
      Nat.card Bs = p ^ r ∧
      Nat.card ↥(Bs ⊓ Subgroup.centralizer (J : Set G)) = p ^ 3 ∧ B < Bs := by
  obtain ⟨r, hdegree, hp, hD, hcard, hcent, hlt, _⟩ :=
    hH.unitary_exactThree_typeA_card_J_of_K hLB hM hpq hd hdiag h3
  exact ⟨r, hdegree, hp, hD, hcard, hcent, hlt⟩

theorem GGResHyp.not_exactThree_K_of_unitaryModel_degree_five
    (hLB : GGLBalanceInput)
    {G : Type} [Group G] [Finite G] {F : Type} [Field F] [Finite F]
    {n p : ℕ} [Fact p.Prime] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K)
    {ψ : ↥(unitarySU 2 n F 5) →* ↥K} (hM : UnitTB.Model ψ)
    (hpq : p ∣ 2 ^ n + 1)
    (hdiag : ∀ a ∈ (ggGamma K (hH.2.2.1.2 y K hH.2.2.2.2.1).le_normalizer).range,
      ∃ t : Fin 5 → F, LineU.ActsDiagU ψ a t) :
    ¬ GGResLeviDatumExact3 p Bs K J L ggSelAny ggTypAny := by
  intro h3
  obtain ⟨r, hdegree, hpd, _, _, _, _, hAJ⟩ :=
    hH.unitary_exactThree_typeA_card_J_of_K hLB hM hpq (by norm_num) hdiag h3
  have hr : r = 4 := by omega
  have hp5 : p = 5 := (Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime)
    (by norm_num : Nat.Prime 5)).mp hpd
  have hAJtwo : Nat.card (ggAutomizer J Bs) = 2 := by
    norm_num [hr] at hAJ
    exact hAJ
  have hpJ := hH.prime_dvd_J_of_unitary_K_exactThree hM hpq (by norm_num) hdiag h3
  have hN := (hH.2.2.1.2 y K hH.2.2.2.2.1).le_normalizer
  obtain ⟨hJK, hcomp⟩ := isComponentOf_comap_ggFix_ggGamma_x_of_dvd
    hLB hH.1 hpJ hH.2.2.2.2.1 hN hH.1.tableB_facts.2.2.1
  obtain ⟨m, hm, δ, hδ, hδdiag⟩ := exists_unitaryModel_of_component_gamma
    hN hH.Bs_le_normalizer_J hJK hM hdiag ⟨x, hH.1.tableB_facts.2.2.1⟩ hcomp
  have hm3 := hH.unitaryModel_J_degree_ge_three hm hδ hδdiag
  have hp2 : p ≠ 2 := hH.1.1.2.2.2.2.2.1.2.1
  by_cases hm4 : 4 ≤ m
  · have hc := card_ggAutomizer_eq_factorial_of_unitaryModel hH.1.2.1.2.1
      hH.1.2.1.2.2.2 hH.Bs_le_normalizer_J hδ hδ.field.card_eq_sq hp2 hpq hm4 hδdiag
    have h24 : 24 ≤ m.factorial := by
      calc 24 = Nat.factorial 4 := by norm_num
        _ ≤ m.factorial := Nat.factorial_le hm4
    omega
  · have hmEq : m = 3 := by omega
    have hcp : Nat.Coprime m p := by rw [hmEq, hp5]; norm_num
    have hc := factorial_le_card_ggAutomizer_of_unitaryModel_coprime hH.1.2.1.2.1
      hH.1.2.1.2.2.2 hH.Bs_le_normalizer_J hδ hp2 hpq hm3 hcp hδdiag
    norm_num [hmEq, hAJtwo] at hc

theorem GGResHyp.unitary_exactThree_J_model_three_of_K
    (hLB : GGLBalanceInput)
    {G : Type} [Group G] [Finite G] {F : Type} [Field F] [Finite F]
    {n p : ℕ} [Fact p.Prime] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K)
    {ψ : ↥(unitarySU 2 n F 6) →* ↥K} (hM : UnitTB.Model ψ)
    (hpq : p ∣ 2 ^ n + 1)
    (hdiag : ∀ a ∈ (ggGamma K (hH.2.2.1.2 y K hH.2.2.2.2.1).le_normalizer).range,
      ∃ t : Fin 6 → F, LineU.ActsDiagU ψ a t)
    (h3 : GGResLeviDatumExact3 p Bs K J L ggSelAny ggTypAny) :
    p = 3 ∧ ∃ δ : ↥(unitarySU 2 n F 3) →* ↥J, UnitTB.Model δ ∧
      ∀ a ∈ (ggGamma J hH.Bs_le_normalizer_J).range,
        ∃ t : Fin 3 → F, LineU.ActsDiagU δ a t := by
  obtain ⟨r, hdegree, hpd, _, _, _, _, hAJ⟩ :=
    hH.unitary_exactThree_typeA_card_J_of_K hLB hM hpq (by norm_num) hdiag h3
  have hr : r = 5 := by omega
  have hAJsix : Nat.card (ggAutomizer J Bs) = 6 := by
    norm_num [hr] at hAJ
    exact hAJ
  have hp2 : p ≠ 2 := hH.1.1.2.2.2.2.2.1.2.1
  have hp3 : p = 3 := by
    have hdiv : p ∣ 2 * 3 := by simpa using hpd
    rcases (Fact.out : p.Prime).dvd_mul.mp hdiv with h2 | h3
    · exact (hp2 ((Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime)
        Nat.prime_two).mp h2)).elim
    · exact (Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) Nat.prime_three).mp h3
  have hpJ := hH.prime_dvd_J_of_unitary_K_exactThree hM hpq (by norm_num) hdiag h3
  have hN := (hH.2.2.1.2 y K hH.2.2.2.2.1).le_normalizer
  obtain ⟨hJK, hcomp⟩ := isComponentOf_comap_ggFix_ggGamma_x_of_dvd
    hLB hH.1 hpJ hH.2.2.2.2.1 hN hH.1.tableB_facts.2.2.1
  obtain ⟨m, hm, δ, hδ, hδdiag⟩ := exists_unitaryModel_of_component_gamma
    hN hH.Bs_le_normalizer_J hJK hM hdiag ⟨x, hH.1.tableB_facts.2.2.1⟩ hcomp
  have hm3 := hH.unitaryModel_J_degree_ge_three hm hδ hδdiag
  have hm4 : ¬ 4 ≤ m := by
    intro h4
    have hc := card_ggAutomizer_eq_factorial_of_unitaryModel hH.1.2.1.2.1
      hH.1.2.1.2.2.2 hH.Bs_le_normalizer_J hδ hδ.field.card_eq_sq hp2 hpq h4 hδdiag
    have h24 : 24 ≤ m.factorial := by
      calc 24 = Nat.factorial 4 := by norm_num
           _ ≤ m.factorial := Nat.factorial_le h4
    omega
  have hmEq : m = 3 := by omega
  subst m
  exact ⟨hp3, δ, hδ, hδdiag⟩

theorem GGResHyp.unitary_exactThree_J_model_qTwo_of_K
    (hLB : GGLBalanceInput)
    {G : Type} [Group G] [Finite G] {F : Type} [Field F] [Finite F]
    {d p : ℕ} [Fact p.Prime] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K)
    {ψ : ↥(unitarySU 2 1 F d) →* ↥K} (hM : UnitTB.Model ψ)
    (hpq : p ∣ 2 ^ 1 + 1) (hd : 5 ≤ d)
    (hdiag : ∀ a ∈ (ggGamma K (hH.2.2.1.2 y K hH.2.2.2.2.1).le_normalizer).range,
      ∃ t : Fin d → F, LineU.ActsDiagU ψ a t)
    (h3 : GGResLeviDatumExact3 p Bs K J L ggSelAny ggTypAny) :
    p = 3 ∧ 3 ∣ d ∧ 9 ≤ d ∧
      ∃ δ : ↥(unitarySU 2 1 F (d - 3)) →* ↥J, UnitTB.Model δ ∧
        ∀ a ∈ (ggGamma J hH.Bs_le_normalizer_J).range,
          ∃ t : Fin (d - 3) → F, LineU.ActsDiagU δ a t := by
  obtain ⟨r, hdegree, hpd, _, _, _, _, hAJ⟩ :=
    hH.unitary_exactThree_typeA_card_J_of_K hLB hM hpq hd hdiag h3
  have hp3 : p = 3 := (Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) Nat.prime_three).mp
    (by simpa using hpq)
  have hpJ := hH.prime_dvd_J_of_unitary_K_exactThree hM hpq hd hdiag h3
  have hN := (hH.2.2.1.2 y K hH.2.2.2.2.1).le_normalizer
  obtain ⟨hJK, hcomp⟩ := isComponentOf_comap_ggFix_ggGamma_x_of_dvd
    hLB hH.1 hpJ hH.2.2.2.2.1 hN hH.1.tableB_facts.2.2.1
  obtain ⟨m, hm, δ, hδ, hδdiag⟩ := exists_unitaryModel_of_component_gamma
    hN hH.Bs_le_normalizer_J hJK hM hdiag ⟨x, hH.1.tableB_facts.2.2.1⟩ hcomp
  have hm4 := hH.unitaryModel_J_degree_ge_four_qTwo hm hδ
  have hp2 : p ≠ 2 := hH.1.1.2.2.2.2.2.1.2.1
  have hc := card_ggAutomizer_eq_factorial_of_unitaryModel hH.1.2.1.2.1
    hH.1.2.1.2.2.2 hH.Bs_le_normalizer_J hδ hδ.field.card_eq_sq hp2 hpq hm4 hδdiag
  have hmEq : m = r - 2 :=
    (Nat.factorial_inj (by omega : 1 < m)).mp (hc.symm.trans hAJ)
  have hmdeg : m = d - 3 := by omega
  have hdiv : 3 ∣ d := hp3 ▸ hpd
  have hd9 : 9 ≤ d := by
    obtain ⟨t, ht⟩ := hdiv
    omega
  cases hmdeg
  exact ⟨hp3, hdiv, hd9, δ, hδ, hδdiag⟩


theorem GGResHyp.unitary_exactThree_reserved_row_qTwo_of_K
    (hLB : GGLBalanceInput)
    {G : Type} [Group G] [Finite G] {F : Type} [Field F] [Finite F]
    {d p : ℕ} [Fact p.Prime] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K)
    {ψ : ↥(unitarySU 2 1 F d) →* ↥K} (hM : UnitTB.Model ψ)
    (hpq : p ∣ 2 ^ 1 + 1) (hd : 5 ≤ d)
    (hdiag : ∀ a ∈ (ggGamma K (hH.2.2.1.2 y K hH.2.2.2.2.1).le_normalizer).range,
      ∃ t : Fin d → F, LineU.ActsDiagU ψ a t)
    (h3 : GGResLeviDatumExact3 p Bs K J L ggSelAny ggTypAny) :
    GGResRowAt ggRowSUCorank3 p J K := by
  obtain ⟨hp3, hdiv, hd9, δ, hδ, _⟩ :=
    hH.unitary_exactThree_J_model_qTwo_of_K hLB hM hpq hd hdiag h3
  have hJLabel := ggHasLabel_of_unitaryModel hδ (by omega : 3 ≤ d - 3)
    (by
      intro h
      have hfst := congrArg Prod.fst h
      omega)
  have hKLabel := ggHasLabel_of_unitaryModel hM (by omega : 3 ≤ d)
    (by
      intro h
      have hfst := congrArg Prod.fst h
      omega)
  refine ⟨⟨.twA, d - 3 - 1, 1⟩, ⟨.twA, d - 1, 1⟩, ?_, ?_, hJLabel, hKLabel, ?_⟩
  · exact ⟨by norm_num, by change 2 ≤ d - 3 - 1; omega,
      by change d - 3 - 1 = 2 → 2 ≤ 1; intro h; omega⟩
  · exact ⟨by norm_num, by change 2 ≤ d - 1; omega,
      by change d - 1 = 2 → 2 ≤ 1; intro h; omega⟩
  · change p = 3 ∧ LargeEvenLieTag.twA = .twA ∧ 1 = 1 ∧
      LargeEvenLieTag.twA = .twA ∧ 1 = 1 ∧
      d - 1 = d - 3 - 1 + 3 ∧ 8 ≤ d - 1 ∧ 3 ∣ d - 1 + 1
    exact ⟨hp3, rfl, rfl, rfl, rfl, by omega, by omega,
      by simpa [Nat.sub_add_cancel (by omega : 1 ≤ d)] using hdiv⟩

theorem GGResHyp.unitary_exactThree_J_model_of_K
    (hLB : GGLBalanceInput)
    {G : Type} [Group G] [Finite G] {F : Type} [Field F] [Finite F]
    {n d p : ℕ} [Fact p.Prime] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K)
    {ψ : ↥(unitarySU 2 n F d) →* ↥K} (hM : UnitTB.Model ψ)
    (hpq : p ∣ 2 ^ n + 1) (hd : 7 ≤ d)
    (hdiag : ∀ a ∈ (ggGamma K (hH.2.2.1.2 y K hH.2.2.2.2.1).le_normalizer).range,
      ∃ t : Fin d → F, LineU.ActsDiagU ψ a t)
    (h3 : GGResLeviDatumExact3 p Bs K J L ggSelAny ggTypAny) :
    ∃ δ : ↥(unitarySU 2 n F (d - 3)) →* ↥J, UnitTB.Model δ ∧
      ∀ a ∈ (ggGamma J hH.Bs_le_normalizer_J).range,
        ∃ t : Fin (d - 3) → F, LineU.ActsDiagU δ a t := by
  obtain ⟨r, hdegree, _, _, hcard, hcent, _, hAJ⟩ :=
    hH.unitary_exactThree_typeA_card_J_of_K hLB hM hpq (by omega : 5 ≤ d) hdiag h3
  have hp : p.Prime := Fact.out
  have hpJ := hH.prime_dvd_J_of_unitary_K_exactThree hM hpq (by omega : 5 ≤ d) hdiag h3
  have hN := (hH.2.2.1.2 y K hH.2.2.2.2.1).le_normalizer
  obtain ⟨hJK, hcomp⟩ := isComponentOf_comap_ggFix_ggGamma_x_of_dvd
    hLB hH.1 hpJ hH.2.2.2.2.1 hN hH.1.tableB_facts.2.2.1
  obtain ⟨m, hm, δ, hδ, hδdiag⟩ := exists_unitaryModel_of_component_gamma
    hN hH.Bs_le_normalizer_J hJK hM hdiag ⟨x, hH.1.tableB_facts.2.2.1⟩ hcomp
  have hm3 := hH.unitaryModel_J_degree_ge_three hm hδ hδdiag
  have hm_ne_three : m ≠ 3 := by
    intro hm3eq
    have hAp : ∀ a ∈ (ggGamma J hH.Bs_le_normalizer_J).range, a ^ p = 1 := by
      rintro a ⟨b, rfl⟩
      have hb : b ^ p = 1 := Subtype.ext (hH.1.2.1.2.1.2 (b : G) b.2)
      rw [← map_pow, hb, map_one]
    have hbound : Nat.card (ggGamma J hH.Bs_le_normalizer_J).range ≤ p ^ (m - 1) :=
      UnitTB.card_diagonal_pow_le hδ (by omega : 3 ≤ m) hp hAp hδdiag
    have hbound2 : Nat.card (ggGamma J hH.Bs_le_normalizer_J).range ≤ p ^ 2 := by
      simpa [hm3eq] using hbound
    have hker : (ggGamma J hH.Bs_le_normalizer_J).ker =
        (Subgroup.centralizer (J : Set G)).subgroupOf Bs := by
      ext b
      rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, ggGamma_eq_one_iff]
    have he : Nat.card ↥((Subgroup.centralizer (J : Set G)).subgroupOf Bs) =
        Nat.card ↥(Bs ⊓ Subgroup.centralizer (J : Set G)) := by
      rw [← Subgroup.inf_subgroupOf_left]
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
    have hmul := TableB.card_range_mul_card_ker (ggGamma J hH.Bs_le_normalizer_J)
    rw [hker, he] at hmul
    have hBsle : Nat.card Bs ≤ p ^ 5 := by
      calc Nat.card Bs = Nat.card (ggGamma J hH.Bs_le_normalizer_J).range *
            Nat.card ↥(Bs ⊓ Subgroup.centralizer (J : Set G)) := hmul.symm
        _ ≤ p ^ 2 * p ^ 3 := Nat.mul_le_mul hbound2 (le_of_eq hcent)
        _ = p ^ 5 := by ring
    have hr6 : 6 ≤ r := by omega
    have hlt : p ^ 5 < p ^ r := Nat.pow_lt_pow_right hp.one_lt hr6
    have hle : p ^ r ≤ p ^ 5 := by simpa [hcard] using hBsle
    exact (not_le_of_gt hlt hle).elim
  have hm4 : 4 ≤ m := by omega
  have hp2 : p ≠ 2 := hH.1.1.2.2.2.2.2.1.2.1
  have hc := card_ggAutomizer_eq_factorial_of_unitaryModel hH.1.2.1.2.1
    hH.1.2.1.2.2.2 hH.Bs_le_normalizer_J hδ hδ.field.card_eq_sq hp2 hpq hm4 hδdiag
  have hmEq : m = r - 2 :=
    (Nat.factorial_inj (by omega : 1 < m)).mp (hc.symm.trans hAJ)
  have hmdeg : m = d - 3 := by omega
  cases hmdeg
  exact ⟨δ, hδ, hδdiag⟩

theorem GGResHyp.unitary_exactThree_J_model_six_of_K
    (hLB : GGLBalanceInput)
    {G : Type} [Group G] [Finite G] {F : Type} [Field F] [Finite F]
    {n p : ℕ} [Fact p.Prime] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K)
    {ψ : ↥(unitarySU 2 n F 9) →* ↥K} (hM : UnitTB.Model ψ)
    (hpq : p ∣ 2 ^ n + 1)
    (hdiag : ∀ a ∈ (ggGamma K (hH.2.2.1.2 y K hH.2.2.2.2.1).le_normalizer).range,
      ∃ t : Fin 9 → F, LineU.ActsDiagU ψ a t)
    (h3 : GGResLeviDatumExact3 p Bs K J L ggSelAny ggTypAny) :
    ∃ δ : ↥(unitarySU 2 n F 6) →* ↥J, UnitTB.Model δ ∧
      ∀ a ∈ (ggGamma J hH.Bs_le_normalizer_J).range,
        ∃ t : Fin 6 → F, LineU.ActsDiagU δ a t := by
  simpa using hH.unitary_exactThree_J_model_of_K hLB hM hpq (by omega : 7 ≤ 9) hdiag h3

private theorem qTwo_K_singular_chart_of_L
    {G : Type} [Group G] [Finite G] {F : Type} [Field F] [Finite F]
    {d p : ℕ} [Fact p.Prime] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K)
    {ψ : ↥(unitarySU 2 1 F d) →* ↥L} (hM : UnitTB.Model ψ)
    (hpq : p ∣ 2 ^ 1 + 1) (hd : 5 ≤ d)
    (hdiag : ∀ a ∈ (ggGamma L hH.2.2.1.1.le_normalizer).range,
      ∃ t : Fin d → F, LineU.ActsDiagU ψ a t)
    {Λ : Type} [Fintype Λ] [DecidableEq Λ] {ML : CoxeterMatrix Λ} {CL : Matrix Λ Λ ℤ}
    {S : Finset Λ} {Λa : Type}
    {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    (ι : Additive ↥Bs ≃+ V) (φ : Λ ⊕ Λa → MulAut ↥Bs) (h : Λ ⊕ Λa → V)
    (α : Λ ⊕ Λa → Module.Dual (ZMod p) V)
    (hS : S.card = 3)
    (hWML : GGIsWeylMatrix ML) (hCLL : GGIntCartan ML CL)
    (hlin : ∀ o w, ggLin (p := p) ι (φ o) w = w - α o w • h o)
    (hrefl : ∀ o, GGIsReflection p (φ o))
    (hpairL : ∀ i j : Λ, α (Sum.inl i) (h (Sum.inl j)) = (CL i j : ZMod p))
    (hclosL : ggAutomizer K Bs = Subgroup.closure (Set.range fun i : Λ => φ (Sum.inl i)))
    (hclosJ : ggAutomizer J Bs = Subgroup.closure
      (Set.range fun i : {i : Λ // i ∉ S} => φ (Sum.inl i))) :
    p = 3 ∧ Module.finrank (ZMod p) V = Fintype.card Λ ∧
      Matrix.rank (CL.map (Int.castRingHom (ZMod p))) + 1 = Fintype.card Λ ∧
      Module.finrank (ZMod p)
        (LinearMap.ker (LinearMap.pi fun i : {i : Λ // i ∉ S} => α (Sum.inl i))) = 3 ∧
      ((GGIsTypeA ML ∧ p ∣ Fintype.card Λ + 1) ∨ (p = 3 ∧ GGIsTypeE6 ML)) ∧
      Nat.card ↥(Bs ⊓ Subgroup.centralizer (J : Set G)) = p ^ 3 ∧ B < Bs := by
  classical
  have hp3 : p = 3 :=
    (Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) Nat.prime_three).mp (by simpa using hpq)
  have hp2 : p ≠ 2 := hH.1.1.2.2.2.2.2.1.2.1
  have hSHat : LargeEvenSHat p B y K := hH.2.2.2.2.1.1
  have hyBs : y ∈ Bs := hH.1.2.1.1 hSHat.2.1
  obtain ⟨v, hv, hvα⟩ := exists_root_kernel_of_centralizing (p := p) hp2
    (fun i => hlin (Sum.inl i)) hpairL hCLL.1 hclosL
    hyBs hSHat.2.2.1 hSHat.2.2.2.1
  obtain ⟨hdim, hrank, hker, hsing, hcent, hlt⟩ :=
    ggRes_exactThree_singular_chart hH.1 ι (fun i => φ (Sum.inl i))
      (fun i => h (Sum.inl i)) (fun i => α (Sum.inl i)) hWML hCLL
      (fun i => hlin (Sum.inl i)) (fun i => hrefl (Sum.inl i)) hpairL hv hvα S hS hclosJ
      (hH.unitary_J_fix_mem_centralizer_of_L hM hdiag)
  exact ⟨hp3, hdim, hrank, hker, hsing, hcent, hlt⟩

private theorem qTwo_L_chart_rank
    {G : Type} [Group G] [Finite G] {F : Type} [Field F] [Finite F]
    {d p : ℕ} [Fact p.Prime] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K)
    {ψ : ↥(unitarySU 2 1 F d) →* ↥L} (hM : UnitTB.Model ψ)
    (hpq : p ∣ 2 ^ 1 + 1) (hd : 5 ≤ d)
    (hdiag : ∀ a ∈ (ggGamma L hH.2.2.1.1.le_normalizer).range,
      ∃ t : Fin d → F, LineU.ActsDiagU ψ a t)
    {Λ : Type} [Fintype Λ] [DecidableEq Λ] {S : Finset Λ}
    {Λa : Type} [Fintype Λa] [DecidableEq Λa]
    {MK : CoxeterMatrix ({i : Λ // i ∉ S} ⊕ Λa)}
    (hWMK : GGIsWeylMatrix MK)
    (fK : MK.Group ≃* ↥(ggAutomizer L Bs)) :
    Fintype.card ({i : Λ // i ∉ S} ⊕ Λa) = d - 1 := by
  classical
  have hp2 : p ≠ 2 := hH.1.1.2.2.2.2.2.1.2.1
  have hBs := hH.1.2.1.2.1
  have hSC := hH.1.2.1.2.2.2
  have hN := hH.2.2.1.1.le_normalizer
  have hF : Nat.card F = (2 ^ 1) ^ 2 := hM.field.card_eq_sq
  have hcardL := card_ggAutomizer_eq_factorial_of_unitaryModel hBs hSC hN hM hF hp2 hpq
    (by omega : 4 ≤ d) hdiag
  have hcardMK : Nat.card MK.Group = d.factorial :=
    (Nat.card_congr fK.toEquiv).trans hcardL
  have hdataMK := ggWeylTypeData_of_isWeylMatrix hWMK
  have hdataA : GGWeylTypeData (d - 1) (Nat.card MK.Group) (if d - 1 = 1 then 2 else 1) := by
    refine Or.inl ⟨by omega, ?_, rfl⟩
    simpa [show d - 1 + 1 = d by omega] using hcardMK
  have hrank := ggWeylTypeData_rank_eq hdataMK hdataA
  simpa using hrank

private theorem qTwo_row_SU2_of_added_two
    {G : Type} [Group G] [Finite G] {F : Type} [Field F] [Finite F]
    {d m p : ℕ} [Fact p.Prime] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K)
    {ψ : ↥(unitarySU 2 1 F d) →* ↥L} (hM : UnitTB.Model ψ)
    (hpq : p ∣ 2 ^ 1 + 1) (hd : 5 ≤ d)
    {δ : ↥(unitarySU 2 1 F m) →* ↥J} (hδ : UnitTB.Model δ) (hm4 : 4 ≤ m)
    (hm : m + 2 = d) (hd7 : 7 ≤ d) (hndvd : ¬ 3 ∣ d) :
    GGResRowAt ggRowSUCorank2 p J L := by
  classical
  have hp3 : p = 3 :=
    (Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) Nat.prime_three).mp (by simpa using hpq)
  have hJlab := ggHasLabel_of_unitaryModel hδ (by omega : 3 ≤ m)
    (by intro h; have hfst := congrArg Prod.fst h; omega)
  have hLlab := ggHasLabel_of_unitaryModel hM (by omega : 3 ≤ d)
    (by intro h; have hfst := congrArg Prod.fst h; omega)
  refine ⟨⟨.twA, m - 1, 1⟩, ⟨.twA, d - 1, 1⟩, ?_, ?_, hJlab, hLlab, ?_⟩
  · unfold LargeEvenInLambda2
    change 1 ≤ 1 ∧ 2 ≤ m - 1 ∧ (m - 1 = 2 → 2 ≤ 1)
    exact ⟨by norm_num, by omega, by intro h; omega⟩
  · unfold LargeEvenInLambda2
    change 1 ≤ 1 ∧ 2 ≤ d - 1 ∧ (d - 1 = 2 → 2 ≤ 1)
    exact ⟨by norm_num, by omega, by intro h; omega⟩
  · change p = 3 ∧ LargeEvenLieTag.twA = LargeEvenLieTag.twA ∧ 1 = 1 ∧
      LargeEvenLieTag.twA = LargeEvenLieTag.twA ∧ 1 = 1 ∧
      d - 1 = m - 1 + 2 ∧ 6 ≤ d - 1 ∧ ¬ 3 ∣ d - 1 + 1
    refine ⟨hp3, rfl, rfl, rfl, rfl, by omega, by omega, ?_⟩
    have hd1 : d - 1 + 1 = d := by omega
    rwa [hd1]

private theorem qTwo_row_SU3_of_added_three
    {G : Type} [Group G] [Finite G] {F : Type} [Field F] [Finite F]
    {d m p : ℕ} [Fact p.Prime] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K)
    {ψ : ↥(unitarySU 2 1 F d) →* ↥L} (hM : UnitTB.Model ψ)
    (hpq : p ∣ 2 ^ 1 + 1) (hd : 5 ≤ d)
    {δ : ↥(unitarySU 2 1 F m) →* ↥J} (hδ : UnitTB.Model δ) (hm4 : 4 ≤ m)
    (hm : m + 3 = d) (hd9 : 9 ≤ d) (h3d : 3 ∣ d) :
    GGResRowAt ggRowSUCorank3 p J L := by
  classical
  have hp3 : p = 3 :=
    (Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) Nat.prime_three).mp (by simpa using hpq)
  have hJlab := ggHasLabel_of_unitaryModel hδ (by omega : 3 ≤ m)
    (by intro h; have hfst := congrArg Prod.fst h; omega)
  have hLlab := ggHasLabel_of_unitaryModel hM (by omega : 3 ≤ d)
    (by intro h; have hfst := congrArg Prod.fst h; omega)
  refine ⟨⟨.twA, m - 1, 1⟩, ⟨.twA, d - 1, 1⟩, ?_, ?_, hJlab, hLlab, ?_⟩
  · unfold LargeEvenInLambda2
    change 1 ≤ 1 ∧ 2 ≤ m - 1 ∧ (m - 1 = 2 → 2 ≤ 1)
    exact ⟨by norm_num, by omega, by intro h; omega⟩
  · unfold LargeEvenInLambda2
    change 1 ≤ 1 ∧ 2 ≤ d - 1 ∧ (d - 1 = 2 → 2 ≤ 1)
    exact ⟨by norm_num, by omega, by intro h; omega⟩
  · change p = 3 ∧ LargeEvenLieTag.twA = LargeEvenLieTag.twA ∧ 1 = 1 ∧
      LargeEvenLieTag.twA = LargeEvenLieTag.twA ∧ 1 = 1 ∧
      d - 1 = m - 1 + 3 ∧ 8 ≤ d - 1 ∧ 3 ∣ d - 1 + 1
    refine ⟨hp3, rfl, rfl, rfl, rfl, by omega, by omega, ?_⟩
    have hd1 : d - 1 + 1 = d := by omega
    rwa [hd1]


private theorem qTwo_survivor_nonempty {Λ : Type} [Fintype Λ] [DecidableEq Λ] {ML : CoxeterMatrix Λ}
    {S : Finset Λ} (hS : S.card = 3)
    (hAorE : (GGIsTypeA ML ∧ 3 ∣ Fintype.card Λ + 1) ∨ GGIsTypeE6 ML) :
    Nonempty {i : Λ // i ∉ S} := by
  have hcomp : Fintype.card {i : Λ // i ∉ S} = Fintype.card Λ - S.card := by
    rw [Fintype.card_subtype_compl (fun i : Λ => i ∈ S)]
    have hsub : Fintype.card {i : Λ // i ∈ S} = S.card := by
      rw [Fintype.card_subtype]
      simp
    rw [hsub]
  have hpos : 0 < Fintype.card {i : Λ // i ∉ S} := by
    rcases hAorE with ⟨hA, h3⟩ | hE
    · obtain ⟨n, e, hn1, -⟩ := hA
      have hcard : Fintype.card Λ = n := by
        simpa using (Fintype.card_congr e).symm
      have hSle : S.card ≤ Fintype.card Λ := Finset.card_le_univ S
      rw [hcomp, hS, hcard]
      have hn3 : 3 ≤ n := by omega
      have h3' : 3 ∣ n + 1 := by simpa [hcard] using h3
      have hn5 : 5 ≤ n := by
        by_contra h
        have hn4 : n ≤ 4 := by omega
        interval_cases n <;> norm_num at h3'
      omega
    · obtain ⟨e, -⟩ := hE
      have hcard : Fintype.card Λ = 6 := by
        simpa using (Fintype.card_congr e).symm
      rw [hcomp, hS, hcard]
      norm_num
  exact Fintype.card_pos_iff.mp hpos

private theorem qTwo_J_degree
    {G : Type} [Group G] [Finite G] {F : Type} [Field F] [Finite F]
    {d p : ℕ} [Fact p.Prime] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K)
    {ψ : ↥(unitarySU 2 1 F d) →* ↥L} (hM : UnitTB.Model ψ)
    (hpq : p ∣ 2 ^ 1 + 1) (hd : 5 ≤ d)
    (hdiag : ∀ a ∈ (ggGamma L hH.2.2.1.1.le_normalizer).range,
      ∃ t : Fin d → F, LineU.ActsDiagU ψ a t)
    {Λ : Type} [Fintype Λ] [DecidableEq Λ] {ML : CoxeterMatrix Λ} {CL : Matrix Λ Λ ℤ}
    {S : Finset Λ} (hS : S.card = 3)
    (hWML : GGIsWeylMatrix ML) (hCLL : GGIntCartan ML CL)
    (hdel : GGDeletedConnectedS ML S)
    (φ : Λ → MulAut ↥Bs)
    (fL : ML.Group ≃* ↥(ggAutomizer K Bs))
    (hfL : ∀ i, (fL (ML.simple i) : MulAut ↥Bs) = φ i)
    (hclosJ : ggAutomizer J Bs = Subgroup.closure
      (Set.range fun i : {i : Λ // i ∉ S} => φ i.val))
    (hAorE : (GGIsTypeA ML ∧ 3 ∣ Fintype.card Λ + 1) ∨ GGIsTypeE6 ML) :
    ∃ m, 4 ≤ m ∧ ∃ δ : ↥(unitarySU 2 1 F m) →* ↥J,
      UnitTB.Model δ ∧
        (∀ a ∈ (ggGamma J hH.Bs_le_normalizer_J).range,
          ∃ t : Fin m → F, LineU.ActsDiagU δ a t) ∧
        m + 2 = Fintype.card Λ := by
  classical
  have hne : Nonempty {i : Λ // i ∉ S} := qTwo_survivor_nonempty hS hAorE
  obtain ⟨m, hm2, δ, hδ, hδdiag⟩ := hH.exists_unitaryModel_J_of_L hM hdiag
  have hm4 := hH.unitaryModel_J_degree_ge_four_qTwo hm2 hδ
  have hp2 : p ≠ 2 := hH.1.1.2.2.2.2.2.1.2.1
  have hBs := hH.1.2.1.2.1
  have hSC := hH.1.2.1.2.2.2
  have hF : Nat.card F = (2 ^ 1) ^ 2 := hM.field.card_eq_sq
  have hcardJ := card_ggAutomizer_eq_factorial_of_unitaryModel hBs hSC
    hH.Bs_le_normalizer_J hδ hF hp2 hpq hm4 hδdiag
  have hWcomp : GGIsWeylMatrix (CFSG.Monster.B.Geometry.parMatrix ML {i : Λ | i ∉ S}) :=
    l05nBL_ggIsWeylMatrix_parMatrix_of_deletedConnected S ML CL hWML hCLL hdel hne
  have eSurv : (CFSG.Monster.B.Geometry.parMatrix ML {i : Λ | i ∉ S}).Group ≃* ↥(ggAutomizer J Bs) :=
    ggParabolic_equiv_of_generator_equiv ML {i : Λ | i ∉ S} φ fL hfL hclosJ
  have hcardComp : Nat.card (CFSG.Monster.B.Geometry.parMatrix ML {i : Λ | i ∉ S}).Group = m.factorial :=
    (Nat.card_congr eSurv.toEquiv).trans hcardJ
  have hdataComp := ggWeylTypeData_of_isWeylMatrix hWcomp
  have hdataA : GGWeylTypeData (m - 1) (Nat.card (CFSG.Monster.B.Geometry.parMatrix ML {i : Λ | i ∉ S}).Group)
      (if m - 1 = 1 then 2 else 1) := by
    refine Or.inl ⟨by omega, ?_, rfl⟩
    simpa [show m - 1 + 1 = m by omega] using hcardComp
  have hrank := ggWeylTypeData_rank_eq hdataComp hdataA
  have hcomp : Fintype.card {i : Λ // i ∉ S} = Fintype.card Λ - S.card := by
    rw [Fintype.card_subtype_compl (fun i : Λ => i ∈ S)]
    have hsub : Fintype.card {i : Λ // i ∈ S} = S.card := by
      rw [Fintype.card_subtype]
      simp
    rw [hsub]
  rw [hS] at hcomp
  have hrank' : Fintype.card {i : Λ // i ∉ S} = m - 1 := hrank
  have hmEq : m + 2 = Fintype.card Λ := by omega
  exact ⟨m, hm4, δ, hδ, hδdiag, hmEq⟩

private theorem qTwo_added_degree_eq {Λ : Type} [Fintype Λ] [DecidableEq Λ] (S : Finset Λ)
    {Λa : Type} [Fintype Λa] {d m k : ℕ}
    (hS : S.card = 3) (ha : Fintype.card Λa = k)
    (hMK : Fintype.card ({i : Λ // i ∉ S} ⊕ Λa) + 1 = d)
    (hm : m + 2 = Fintype.card Λ) : m + k = d := by
  have hcomp : Fintype.card {i : Λ // i ∉ S} + S.card = Fintype.card Λ := by
    rw [Fintype.card_subtype_compl (fun i : Λ => i ∈ S)]
    have hsub : Fintype.card {i : Λ // i ∈ S} = S.card := by
      rw [Fintype.card_subtype]
      simp
    rw [hsub, Nat.sub_add_cancel (Finset.card_le_univ S)]
  have hsum : Fintype.card ({i : Λ // i ∉ S} ⊕ Λa) =
      Fintype.card {i : Λ // i ∉ S} + Fintype.card Λa := Fintype.card_sum
  rw [hsum, ha] at hMK
  have hcomp1 : Fintype.card {i : Λ // i ∉ S} + 1 = m := by
    rw [hS] at hcomp
    omega
  omega

private theorem qTwo_row_twoNode_of_added_two
    {G : Type} [Group G] [Finite G] {F : Type} [Field F] [Finite F]
    {d m p : ℕ} [Fact p.Prime] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K)
    {ψ : ↥(unitarySU 2 1 F d) →* ↥L} (hM : UnitTB.Model ψ)
    (hpq : p ∣ 2 ^ 1 + 1) (hd : 5 ≤ d)
    {δ : ↥(unitarySU 2 1 F m) →* ↥J} (hδ : UnitTB.Model δ) (hm4 : 4 ≤ m)
    (hm : m + 2 = d) (h3d : 3 ∣ d) :
    GGResRowAt ggRowTwoNode p J L := by
  classical
  have hp3 : p = 3 :=
    (Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) Nat.prime_three).mp (by simpa using hpq)
  have hJlab := ggHasLabel_of_unitaryModel hδ (by omega : 3 ≤ m)
    (by intro h; have hfst := congrArg Prod.fst h; omega)
  have hLlab := ggHasLabel_of_unitaryModel hM (by omega : 3 ≤ d)
    (by intro h; have hfst := congrArg Prod.fst h; omega)
  refine ⟨⟨.twA, m - 1, 1⟩, ⟨.twA, d - 1, 1⟩, ?_, ?_, hJlab, hLlab, ?_⟩
  · unfold LargeEvenInLambda2
    change 1 ≤ 1 ∧ 2 ≤ m - 1 ∧ (m - 1 = 2 → 2 ≤ 1)
    exact ⟨by norm_num, by omega, by intro h; omega⟩
  · unfold LargeEvenInLambda2
    change 1 ≤ 1 ∧ 2 ≤ d - 1 ∧ (d - 1 = 2 → 2 ≤ 1)
    exact ⟨by norm_num, by omega, by intro h; omega⟩
  · refine Or.inr (Or.inl ?_)
    change LargeEvenLieTag.twA = .twA ∧ p ∣ 2 ^ 1 + 1 ∧ p ∣ (m - 1) + 3 ∧
      (⟨.twA, d - 1, 1⟩ : LargeEvenLabel) = ⟨.twA, m - 1 + 2, 1⟩
    refine ⟨rfl, hpq, ?_, ?_⟩
    · have hmd' : (m - 1) + 3 = d := by omega
      simpa [hp3, hmd'] using h3d
    · congr 1
      omega

theorem GGResHyp.unitary_exactThree_K_rows_qTwo_of_L
    {G : Type} [Group G] [Finite G] {F : Type} [Field F] [Finite F]
    {d p : ℕ} [Fact p.Prime] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K)
    {ψ : ↥(unitarySU 2 1 F d) →* ↥L} (hM : UnitTB.Model ψ)
    (hpq : p ∣ 2 ^ 1 + 1) (hd : 5 ≤ d)
    (hdiag : ∀ a ∈ (ggGamma L hH.2.2.1.1.le_normalizer).range,
      ∃ t : Fin d → F, LineU.ActsDiagU ψ a t)
    (h3 : GGResLeviDatumExact3 p Bs K J L ggSelAny ggTypAny) :
    GGResRowAt ggRowTwoNode p J L ∨ GGResRowAt ggRowSUCorank2 p J L ∨
      GGResRowAt ggRowSUCorank3 p J L := by
  classical
  obtain ⟨Λ, i1, i2, S, Λa, i3, i4, ML, CL, MK, CK, V, i5, i6, ι, φ, h, α,
    hS3, hA1, hA3, hWML, hCLL, hWMK, hCKK, htyp, hlin, hrefl, hpairL, hpairK, hsel,
    hfLx, hfKx, hclosL, hclosK, hdel, hclosJ⟩ := h3
  let := i1
  let := i2
  let := i3
  let := i4
  let := i5
  let := i6
  obtain ⟨fL, hfL⟩ := hfLx
  obtain ⟨fK, hfK⟩ := hfKx
  haveI : Finite V := Finite.of_equiv (Additive Bs) ι.toEquiv
  haveI : Module.Finite (ZMod p) V := Module.Finite.of_finite
  obtain ⟨hp3, hdim, hrank, hker, hsing, hcent, hlt⟩ :=
    qTwo_K_singular_chart_of_L hH hM hpq hd hdiag ι φ h α hS3 hWML hCLL
      hlin hrefl hpairL hclosL hclosJ
  have hAE : (GGIsTypeA ML ∧ 3 ∣ Fintype.card Λ + 1) ∨ GGIsTypeE6 ML := by
    rcases hsing with hA | hE
    · exact Or.inl ⟨hA.1, by simpa [hp3] using hA.2⟩
    · exact Or.inr hE.2
  obtain ⟨m, hm4, δ, hδ, hδdiag, hmΛ⟩ :=
    qTwo_J_degree hH hM hpq hd hdiag hS3 hWML hCLL hdel
      (fun i => φ (Sum.inl i)) fL hfL hclosJ hAE
  have hLrank := qTwo_L_chart_rank hH hM hpq hd hdiag hWMK fK
  have hmd : m + Nat.card Λa = d := qTwo_added_degree_eq S hS3
    Nat.card_eq_fintype_card.symm (by omega) hmΛ
  have hp : p.Prime := Fact.out
  have hp2 : p ≠ 2 := hH.1.1.2.2.2.2.2.1.2.1
  have hBs := hH.1.2.1.2.1
  have hSC := hH.1.2.1.2.2.2
  have hN := hH.2.2.1.1.le_normalizer
  rcases (by omega : Nat.card Λa = 1 ∨ Nat.card Λa = 2 ∨ Nat.card Λa = 3) with ha | ha | ha
  · have hnodes : Fintype.card Λ = d + 1 := by omega
    have hcard : Nat.card Bs = p ^ (d + 1) := by
      rw [card_eq_of_ggLin ι, ← FiniteField.pow_finrank_eq_natCard p V, hdim, hnodes]
    obtain ⟨_, _, hxBs, hLx, _⟩ := hH.1.tableB_facts
    have hS := hH.1.1.2.2.2.2.2.2.1
    have hmul := card_range_ggGamma_mul_of hp hBs hxBs hS.2.2.1 hLx hS.2.2.2.2 hN
    have hAp : ∀ a ∈ (ggGamma L hN).range, a ^ p = 1 := by
      rintro a ⟨b, rfl⟩
      have hb : b ^ p = 1 := Subtype.ext (hBs.2 (b : G) b.2)
      rw [← map_pow, hb, map_one]
    have hbound := UnitTB.card_diagonal_pow_le hM (by omega) hp hAp hdiag
    have hbad : p ^ (d + 1) ≤ p ^ d := by
      rw [← hcard, ← hmul]
      have hh := Nat.mul_le_mul_right p hbound
      simpa [← pow_succ, Nat.sub_add_cancel (by omega : 1 ≤ d)] using hh
    have hstrict := (Nat.pow_lt_pow_iff_right hp.one_lt).mpr (by omega : d < d + 1)
    exact (not_le_of_gt hstrict hbad).elim
  · have hm : m + 2 = d := by omega
    by_cases h3d : 3 ∣ d
    · exact Or.inl (qTwo_row_twoNode_of_added_two hH hM hpq hd hδ hm4 hm h3d)
    · have hd7 : 7 ≤ d := by
        by_contra hbad
        have hd6 : d = 6 := by omega
        exact h3d (by rw [hd6]; norm_num)
      exact Or.inr (Or.inl (qTwo_row_SU2_of_added_two hH hM hpq hd hδ hm4 hm hd7 h3d))
  · have hm : m + 3 = d := by omega
    rcases hAE with ⟨hA, hdiv⟩ | hE
    · have h3d : 3 ∣ d := by
        have heq : Fintype.card Λ + 1 = d := by omega
        rwa [heq] at hdiv
      have hd9 : 9 ≤ d := by
        have hd7 : 7 ≤ d := by omega
        by_contra hbad
        have h78 : d = 7 ∨ d = 8 := by omega
        rcases h78 with rfl | rfl <;> norm_num at h3d
      exact Or.inr (Or.inr (qTwo_row_SU3_of_added_three hH hM hpq hd hδ hm4 hm hd9 h3d))
    · obtain ⟨eE, _⟩ := hE
      have hnodes : Fintype.card Λ = 6 := by
        simpa using (Fintype.card_congr eE).symm
      have hd7 : d = 7 := by omega
      let j : ({i : Λ // i ∉ S} ⊕ Λa) → Λ ⊕ Λa := fun o => o.map Subtype.val id
      have hKgen : ggAutomizer L Bs = Subgroup.closure (Set.range fun o => φ (j o)) := by
        rw [hclosK]
        congr 1
        ext a
        simp only [Set.mem_range, Set.mem_union]
        constructor
        · rintro (⟨i, rfl⟩ | ⟨i, rfl⟩)
          · exact ⟨Sum.inl i, rfl⟩
          · exact ⟨Sum.inr i, rfl⟩
        · rintro ⟨o, rfl⟩
          cases o with
          | inl i => exact Or.inl ⟨i, rfl⟩
          | inr i => exact Or.inr ⟨i, rfl⟩
      obtain ⟨_, _, hxBs, hLx, _⟩ := hH.1.tableB_facts
      have hS := hH.1.1.2.2.2.2.2.2.1
      obtain ⟨v, hv, hvα⟩ := exists_root_kernel_of_centralizing (p := p) hp2
        (fun o => hlin (j o)) hpairK hCKK.1 hKgen hxBs hS.2.2.1 hLx
      haveI : Finite V := Finite.of_equiv (Additive Bs) ι.toEquiv
      haveI : Module.Finite (ZMod p) V := Module.Finite.of_finite
      have hdet := ggRC_det_cast_eq_zero_of_common_kernel_of_finrank_eq_card (fun o => h (j o)) (fun o => α (j o))
        hpairK hv hvα (by omega : Module.finrank (ZMod p) V =
          Fintype.card ({i : Λ // i ∉ S} ⊕ Λa))
      rcases ggRC_singular_typeA_or_E6 hp hp2 hWMK hCKK hdet with hA | hE
      · have hdiv : 3 ∣ 7 := by simpa [hp3, hLrank, hd7] using hA.2
        norm_num at hdiv
      · exact (not_typeE6_of_unitaryModel hBs hSC hN hM hM.field.card_eq_sq
          hp2 hpq hd hdiag fK hE.2).elim
theorem GGResHyp.not_exactThree_either_of_unitaryModel_qTwo
    {G : Type} [Group G] [Finite G] {F : Type} [Field F] [Finite F]
    {d p : ℕ} [Fact p.Prime] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K)
    {ψ : ↥(unitarySU 2 1 F d) →* ↥L} (hM : UnitTB.Model ψ)
    (hpq : p ∣ 2 ^ 1 + 1) (hd : 5 ≤ d)
    (hdiag : ∀ a ∈ (ggGamma L hH.2.2.1.1.le_normalizer).range,
      ∃ t : Fin d → F, LineU.ActsDiagU ψ a t)
    (hntwo : ¬ GGResRowAt ggRowTwoNode p J L)
    (hnSU2 : ¬ GGResRowAt ggRowSUCorank2 p J L)
    (hnSU3 : ¬ GGResRowAt ggRowSUCorank3 p J L) :
    ¬ (GGResLeviDatumExact3 p Bs L J K ggSelAny ggTypAny ∨
      GGResLeviDatumExact3 p Bs K J L ggSelAny ggTypAny) := by
  rintro (h3 | h3)
  · exact hnSU3 (hH.unitary_exactThree_reserved_row_qTwo_of_L hM hpq hd hdiag h3)
  · rcases hH.unitary_exactThree_K_rows_qTwo_of_L hM hpq hd hdiag h3 with h | h | h
    · exact hntwo h
    · exact hnSU2 h
    · exact hnSU3 h

theorem GGResHyp.not_exactThree_either_of_unitary_marking_qTwo
    {G : Type} [Group G] [Finite G] {F : Type} [Field F] [Finite F]
    {d p : ℕ} [Fact p.Prime] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K)
    (hF : Nat.card F = (2 ^ 1) ^ 2) (hd : 5 ≤ d) (hd6 : d ≠ 6)
    (hpq : p ∣ 2 ^ 1 + 1)
    (θ : ↥L ⧸ Subgroup.center ↥L ≃* LargeEvenProj (unitarySU 2 1 F d))
    (hact : ∀ b ∈ Bs, ∃ a ∈ LargeEvenMatConjImage (LargeEvenProjMk (unitarySU 2 1 F d))
      (LargeEvenGUSet (Fin d) F (2 ^ 1)),
      LargeEvenInduces θ (fun l l' : ↥L => (l' : G) = b⁻¹ * l * b) a)
    (hntwo : ¬ GGResRowAt ggRowTwoNode p J L)
    (hnSU2 : ¬ GGResRowAt ggRowSUCorank2 p J L)
    (hnSU3 : ¬ GGResRowAt ggRowSUCorank3 p J L) :
    ¬ (GGResLeviDatumExact3 p Bs L J K ggSelAny ggTypAny ∨
      GGResLeviDatumExact3 p Bs K J L ggSelAny ggTypAny) := by
  obtain ⟨ψ, hM, hdiag⟩ := hH.exists_unitaryModel_L_of_marking hF (by norm_num) hd hpq
    (fun h => hd6 h.1) θ hact
  exact hH.not_exactThree_either_of_unitaryModel_qTwo hM hpq hd hdiag hntwo hnSU2 hnSU3

theorem GGResHyp.not_exactThree_either_of_unitary_label_qTwo
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K)
    (hU : GGInnerDiagOnLabel
      (fun p lab => lab.tag = .twA ∧ 4 ≤ lab.rank ∧ lab.n = 1 ∧
        lab.rank ≠ 5 ∧ p ∣ 2 ^ lab.n + 1) p Bs L)
    (hntwo : ¬ GGResRowAt ggRowTwoNode p J L)
    (hnSU2 : ¬ GGResRowAt ggRowSUCorank2 p J L)
    (hnSU3 : ¬ GGResRowAt ggRowSUCorank3 p J L) :
    ¬ (GGResLeviDatumExact3 p Bs L J K ggSelAny ggTypAny ∨
      GGResLeviDatumExact3 p Bs K J L ggSelAny ggTypAny) := by
  obtain ⟨_, ⟨t, r, n⟩, _, hraw⟩ := hU
  have htag : t = .twA := by
    obtain ⟨R, _, I, F, _, _, θ, hθ⟩ := largeEvenRawDatum_exists hraw
    exact hθ.1.1
  subst t
  dsimp only [CFSG.Assembly.LargeEvenRawDatumLegacy] at hraw
  obtain ⟨F, iF, iFin, hF, _, _, θ, hpred, _, hact⟩ := hraw
  let := iF
  let := iFin
  have hn1 : n = 1 := hpred.2.2.1
  subst n
  exact hH.not_exactThree_either_of_unitary_marking_qTwo hF (by have := hpred.2.1; omega)
    (by have := hpred.2.2.2.1; omega) hpred.2.2.2.2 θ hact hntwo hnSU2 hnSU3

theorem linearIndependent_coroots_or_eq_of_A2
    {G : Type} [Group G] {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    {Bs J : Subgroup G} (ι : Additive ↥Bs ≃+ V)
    {r : Fin 2 → MulAut ↥Bs} {h : Fin 2 → V} {α : Fin 2 → Module.Dual (ZMod 3) V}
    (hform : ∀ j w, ggLin (p := 3) ι (r j) w = w - α j w • h j)
    (hpair : ∀ i j, α i (h j) = (CartanMatrix.A 2 i j : ZMod 3))
    (hmem : ∀ j, r j ∈ ggAutomizer J Bs)
    (hNoTr : GGNoTransvection 3 Bs) :
    LinearIndependent (ZMod 3) h ∨ r 0 = r 1 := by
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have h2ne : (2 : ZMod 3) ≠ 0 := by
    intro h
    have hdvd : 3 ∣ 2 := (ZMod.natCast_eq_zero_iff 2 3).mp h
    norm_num at hdvd
  have hα : ∀ i : Fin 2, α i (h i) = (2 : ZMod 3) := by
    intro i
    have hi : CartanMatrix.A 2 i i = 2 := by fin_cases i <;> decide
    rw [hpair i i, hi]
    norm_num
  have h01 : α 0 (h 1) = (2 : ZMod 3) := by
    have h01' : CartanMatrix.A 2 0 1 = -1 := by decide
    rw [hpair 0 1, h01']
    show ((-1 : ℤ) : ZMod 3) = ((2 : ℤ) : ZMod 3)
    rw [ZMod.intCast_eq_intCast_iff']
    norm_num
  have h10 : α 1 (h 0) = (2 : ZMod 3) := by
    have h10' : CartanMatrix.A 2 1 0 = -1 := by decide
    rw [hpair 1 0, h10']
    show ((-1 : ℤ) : ZMod 3) = ((2 : ℤ) : ZMod 3)
    rw [ZMod.intCast_eq_intCast_iff']
    norm_num
  by_cases hind : LinearIndependent (ZMod 3) h
  · exact Or.inl hind
  right
  have hh1 : h 1 ≠ 0 := by
    intro hz
    have h1 := hα 1
    rw [hz, map_zero] at h1
    exact h2ne h1.symm
  rw [linearIndependent_fin2] at hind
  push Not at hind
  obtain ⟨c, hc⟩ := hind hh1
  have hc1 : c = 1 := by
    have hc' := congrArg (α 1) hc
    rw [map_smul, hα 1, h10, smul_eq_mul] at hc'
    exact mul_right_cancel₀ h2ne (by rw [hc', one_mul])
  rw [hc1, one_smul] at hc
  by_contra hne
  have hf0 : α 1 - α 0 ≠ 0 := by
    intro hf
    apply hne
    have hαeq : α 1 = α 0 := sub_eq_zero.mp hf
    apply ggLin_injective (p := 3) ι
    ext w
    rw [hform 0 w, hform 1 w, hαeq, hc]
  have hw : h 0 ≠ 0 := by rwa [← hc]
  have hfw : (α 1 - α 0) (h 0) = 0 := by
    rw [LinearMap.sub_apply, h10, hα 0, sub_self]
  have happ : ∀ v, ggLin (p := 3) ι (r 0 * r 1) v = v + (α 1 - α 0) v • h 0 := by
    intro v
    rw [map_mul, LinearEquiv.mul_apply, hform 1 v, hform 0, hc, map_sub, map_smul,
      hα 0, smul_eq_mul, LinearMap.sub_apply]
    module
  have hmemprod : r 0 * r 1 ∈ ggInduced ⊤ Bs :=
    mul_mem_ggInduced (mem_ggInduced_top_of_mem_ggAutomizer (hmem 0))
      (mem_ggInduced_top_of_mem_ggAutomizer (hmem 1))
  exact (hNoTr (r 0 * r 1) hmemprod) (ggIsTransvection_of_apply (p := 3) ι hw hf0 hfw happ)

theorem coxeterMatrixA_reindex_le_three {ι : Type} {n : ℕ} (e : Fin n ≃ ι) (i j : ι) :
    ((CoxeterMatrix.A n).reindex e).M i j ≤ 3 := by
  rw [CoxeterMatrix.reindex_apply]
  show (if e.symm i = e.symm j then 1 else
    if ((e.symm j : Fin n) : ℕ) + 1 = e.symm i ∨ ((e.symm i : Fin n) : ℕ) + 1 = e.symm j then 3
      else 2) ≤ 3
  split_ifs <;> omega

section ExactThreeUnitaryExclusion


theorem GGResHyp.not_exactThree_of_unitaryModel_L
    {G : Type} [Group G] [Finite G] {F : Type} [Field F] [Finite F]
    {n d p : ℕ} [Fact p.Prime] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K)
    {ψ : ↥(unitarySU 2 n F d) →* ↥L} (hM : UnitTB.Model ψ)
    (hn : 2 ≤ n) (hpq : p ∣ 2 ^ n + 1) (hd : 5 ≤ d)
    (hdiag : ∀ a ∈ (ggGamma L hH.2.2.1.1.le_normalizer).range,
      ∃ t : Fin d → F, LineU.ActsDiagU ψ a t) :
    ¬ GGResLeviDatumExact3 p Bs L J K ggSelAny ggTypAny := by
  intro h3
  obtain ⟨r, -, -, -, -, hcent, hlt⟩ :=
    hH.unitary_exactThree_typeA_of_L hM hpq hd hdiag h3
  exact hH.centralizer_J_card_ne_p3_of_unitary hM hdiag hn hd hpq hlt hcent

theorem GGResHyp.not_exactThree_K_of_unitaryModel_L
    {G : Type} [Group G] [Finite G] {F : Type} [Field F] [Finite F]
    {n d p : ℕ} [Fact p.Prime] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K)
    {ψ : ↥(unitarySU 2 n F d) →* ↥L} (hM : UnitTB.Model ψ)
    (hn : 2 ≤ n) (hd : 5 ≤ d) (hpq : p ∣ 2 ^ n + 1)
    (hdiag : ∀ a ∈ (ggGamma L hH.2.2.1.1.le_normalizer).range,
      ∃ t : Fin d → F, LineU.ActsDiagU ψ a t) :
    ¬ GGResLeviDatumExact3 p Bs K J L ggSelAny ggTypAny := by
  intro h3
  obtain ⟨Λ, i1, i2, S, Λa, i3, i4, ML, CL, MK, CK, V, i5, i6, ι, φ, h, α,
    hS3, hA1, hA3, hWML, hCLL, hWMK, hCKK, htyp, hlin, hrefl, hpairL, hpairK, hsel,
    hfLx, hfKx, hclosL, hclosK, hdel, hclosJ⟩ := h3
  let := i1
  let := i2
  let := i5
  let := i6
  have hp2 : p ≠ 2 := hH.1.1.2.2.2.2.2.1.2.1
  have hSHat : LargeEvenSHat p B y K := hH.2.2.2.2.1.1
  have hyBs : y ∈ Bs := hH.1.2.1.1 hSHat.2.1
  obtain ⟨v, hv, hvα⟩ := exists_root_kernel_of_centralizing (p := p) hp2
    (fun i => hlin (Sum.inl i)) hpairL hCLL.1 hclosL
    hyBs hSHat.2.2.1 hSHat.2.2.2.1
  obtain ⟨_, _, _, _, hcent, hlt⟩ := ggRes_exactThree_singular_chart hH.1 ι
    (fun i => φ (Sum.inl i)) (fun i => h (Sum.inl i)) (fun i => α (Sum.inl i))
    hWML hCLL (fun i => hlin (Sum.inl i)) (fun i => hrefl (Sum.inl i))
    hpairL hv hvα S hS3 hclosJ (hH.unitary_J_fix_mem_centralizer_of_L hM hdiag)
  exact hH.centralizer_J_card_ne_p3_of_unitary hM hdiag hn hd hpq hlt hcent

theorem GGResHyp.not_exactThree_either_of_unitary_marking_qGeFour
    {G : Type} [Group G] [Finite G] {F : Type} [Field F] [Finite F]
    {n d p : ℕ} [Fact p.Prime] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K)
    (hF : Nat.card F = (2 ^ n) ^ 2) (hn : 2 ≤ n) (hd : 5 ≤ d)
    (hpq : p ∣ 2 ^ n + 1)
    (θ : ↥L ⧸ Subgroup.center ↥L ≃* LargeEvenProj (unitarySU 2 n F d))
    (hact : ∀ b ∈ Bs, ∃ a ∈ LargeEvenMatConjImage (LargeEvenProjMk (unitarySU 2 n F d))
      (LargeEvenGUSet (Fin d) F (2 ^ n)),
      LargeEvenInduces θ (fun l l' : ↥L => (l' : G) = b⁻¹ * l * b) a) :
    ¬ (GGResLeviDatumExact3 p Bs L J K ggSelAny ggTypAny ∨
      GGResLeviDatumExact3 p Bs K J L ggSelAny ggTypAny) := by
  obtain ⟨ψ, hM, hdiag⟩ :=
    hH.exists_unitaryModel_L_of_marking_qGeFour hF hn hd hpq θ hact
  exact not_or.mpr ⟨hH.not_exactThree_of_unitaryModel_L hM hn hpq hd hdiag,
    hH.not_exactThree_K_of_unitaryModel_L hM hn hd hpq hdiag⟩

theorem GGResHyp.not_exactThree_either_of_unitary_label_qGeFour
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K)
    (hU : GGInnerDiagOnLabel
      (fun p lab => lab.tag = .twA ∧ 4 ≤ lab.rank ∧ 2 ≤ lab.n ∧ p ∣ 2 ^ lab.n + 1)
      p Bs L) :
    ¬ (GGResLeviDatumExact3 p Bs L J K ggSelAny ggTypAny ∨
      GGResLeviDatumExact3 p Bs K J L ggSelAny ggTypAny) := by
  obtain ⟨_, lab, _, hraw⟩ := hU
  have htag : lab.tag = .twA := by
    obtain ⟨R, _, I, F, _, _, θ, hθ⟩ := largeEvenRawDatum_exists hraw
    exact hθ.1.1
  dsimp only [CFSG.Assembly.LargeEvenRawDatumLegacy] at hraw
  rw [htag] at hraw
  obtain ⟨F, iF, iFin, hF, _, _, θ, hpred, _, hact⟩ := hraw
  let := iF
  let := iFin
  exact hH.not_exactThree_either_of_unitary_marking_qGeFour hF hpred.2.2.1
    (by omega : 5 ≤ lab.rank + 1) hpred.2.2.2 θ hact

theorem GGResHyp.exactThree_A2_line_of_rankFive
    {G : Type} [Group G] [Finite G]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp 3 B Bs x L D J y K)
    (h3 : GGResLeviDatumExact3 3 Bs K J L ggSelAny ggTypAny)
    (hcardK : Nat.card ↥(ggAutomizer K Bs) = 720)
    (hAJ6 : Nat.card ↥(ggAutomizer J Bs) = 6) :
    GGResLineJDatum 3 Bs J .A2 := by
  classical
  obtain ⟨Λ, i1, i2, Sdel, Λa, i3, i4, ML, CL, MK, CK, V, i5, i6, ι, φ, h, α,
    hS3, hA1, hA3, hML, hCL, hMK, hCK, htyp, hlin, hrefl, hpairL, hpairK, hsel,
    ⟨fL, hfL⟩, ⟨fK, hfK⟩, hclosL, hclosK, hdel, hclosJ⟩ := h3
  let _ := i1
  let _ := i2
  let _ := i3
  let _ := i4
  let _ := i5
  let _ := i6
  have hcardML : Nat.card ML.Group = 720 :=
    (Nat.card_congr fL.toEquiv).trans hcardK
  have hW : GGWeylOfType 3 ML (ggAutomizer K Bs) :=
    ⟨fL, fun i => by rw [hfL i]; exact hrefl (Sum.inl i)⟩
  obtain ⟨eA, hMA⟩ := l05nQW_A5_of_weyl ML hML hW hcardK
  have h5 : Fintype.card Λ = 5 := by
    simpa using (Fintype.card_congr eA).symm
  have hcompl : Nat.card {i : Λ // i ∉ Sdel} = 2 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype_compl, Fintype.card_coe, h5, hS3]
  obtain ⟨u, v, huv, huniv⟩ := Nat.card_eq_two_iff.mp hcompl
  have hcover : ∀ w : {i : Λ // i ∉ Sdel}, w = u ∨ w = v := by
    intro w
    have hw : w ∈ ({u, v} : Set {i : Λ // i ∉ Sdel}) := by
      rw [huniv]
      exact Set.mem_univ w
    simpa using hw
  have hadj : ML.M u v ≠ 2 := by
    rcases Relation.ReflTransGen.cases_head (hdel u v) with huv' | ⟨c, ⟨huc, hc2⟩, -⟩
    · exact absurd huv' huv
    · rcases hcover c with rfl | rfl
      · exact absurd rfl huc
      · exact hc2
  have huv1 : u.1 ≠ v.1 := fun h' => huv (Subtype.ext h')
  have hle3 : ML.M u.1 v.1 ≤ 3 := by
    rw [hMA]
    exact coxeterMatrixA_reindex_le_three eA _ _
  have hCuv : CL u.1 v.1 = -1 ∧ CL v.1 u.1 = -1 := by
    rcases hCL.2 u.1 v.1 huv1 with ⟨h2, -, -⟩ | ⟨-, hc1, hc2⟩ | ⟨h4', -⟩ | ⟨h6', -⟩
    · exact absurd h2 hadj
    · exact ⟨hc1, hc2⟩
    · change ML.M u.1 v.1 = 4 at h4'
      omega
    · change ML.M u.1 v.1 = 6 at h6'
      omega
  let pr : Fin 2 → Λ := ![u.1, v.1]
  let r : Fin 2 → MulAut ↥Bs := fun k => φ (Sum.inl (pr k))
  let hv : Fin 2 → V := fun k => h (Sum.inl (pr k))
  let αv : Fin 2 → Module.Dual (ZMod 3) V := fun k => α (Sum.inl (pr k))
  have hform : ∀ k w, ggLin (p := 3) ι (r k) w = w - αv k w • hv k :=
    fun k w => hlin (Sum.inl (pr k)) w
  have hCLA : ∀ i j, CL (pr i) (pr j) = CartanMatrix.A 2 i j := by
    intro i j
    fin_cases i <;> fin_cases j
    · show CL u.1 u.1 = CartanMatrix.A 2 0 0
      rw [hCL.1]
      decide
    · show CL u.1 v.1 = CartanMatrix.A 2 0 1
      rw [hCuv.1]
      decide
    · show CL v.1 u.1 = CartanMatrix.A 2 1 0
      rw [hCuv.2]
      decide
    · show CL v.1 v.1 = CartanMatrix.A 2 1 1
      rw [hCL.1]
      decide
  have hpairv : ∀ i j, αv i (hv j) = (CartanMatrix.A 2 i j : ZMod 3) := by
    intro i j
    rw [← hCLA i j]
    exact hpairL (pr i) (pr j)
  have hrange : Set.range r = Set.range fun j : {j : Λ // j ∉ Sdel} => φ (Sum.inl j) := by
    ext ψ
    constructor
    · rintro ⟨k, rfl⟩
      fin_cases k
      · exact ⟨u, rfl⟩
      · exact ⟨v, rfl⟩
    · rintro ⟨j, rfl⟩
      rcases hcover j with rfl | rfl
      · exact ⟨0, rfl⟩
      · exact ⟨1, rfl⟩
  have hmem : ∀ k, r k ∈ ggAutomizer J Bs := by
    intro k
    fin_cases k
    · rw [hclosJ]
      exact Subgroup.subset_closure ⟨u, rfl⟩
    · rw [hclosJ]
      exact Subgroup.subset_closure ⟨v, rfl⟩
  rcases linearIndependent_coroots_or_eq_of_A2 ι hform hpairv hmem hH.2.2.2.1 with hind | heq
  · exact ⟨V, inferInstance, inferInstance, ι, r, hv, αv, hform, fun k => hrefl _,
      hpairv, hind, hclosJ.trans (congrArg Subgroup.closure hrange.symm)⟩
  · have hr1 : Set.range r = {r 0} := by
      ext ψ
      constructor
      · rintro ⟨k, rfl⟩
        fin_cases k
        · rfl
        · exact heq.symm
      · rintro rfl
        exact ⟨0, rfl⟩
    have hAJ : ggAutomizer J Bs = Subgroup.zpowers (r 0) := by
      rw [hclosJ, ← hrange, hr1, Subgroup.zpowers_eq_closure]
    have hAJle : Nat.card ↥(ggAutomizer J Bs) ≤ 2 := by
      rw [hAJ, Nat.card_zpowers]
      exact Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one (hrefl _).1)
    omega

end ExactThreeUnitaryExclusion

end CFSG.StandardType
