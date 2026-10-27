module

public import CFSG.LocalAnalysis.StandardType.GGQTwoVACUnit
public import CFSG.LocalAnalysis.StandardType.GGQTwoCavHeartReduction
public import CFSG.LocalAnalysis.StandardType.GGTableBUnit63Main
public import CFSG.LocalAnalysis.StandardType.GGTableBUnitaryTorus
public import CFSG.LocalAnalysis.StandardType.GGTableBLinUnitLCx
public import CFSG.LocalAnalysis.StandardType.GGNbrLangQ1TorUniTor
public import CFSG.LocalAnalysis.StandardType.GGBstarDeltaUDvdBound
public import CFSG.LocalAnalysis.StandardType.GGQTwoUnitaryRealization
public import CFSG.LocalAnalysis.StandardType.GGTPNPCompQuasi

public section

namespace CFSG.StandardType

noncomputable local instance fintypeUnitsOfFinite (K : Type) [Field K] [Finite K] :
    Fintype Kˣ :=
  Fintype.ofFinite Kˣ

open CFSG CFSG.Assembly CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.SectionRank.OddCover
open CFSG.ClassicalGroups.UnitaryFlag

theorem ggQ2UnitDvd_gamma_ge_of_torusLift {G : Type} [Group G] [Finite G]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} (hS : GGQTwoSetting 3 B Bs x L D J)
    {R : Type} [Group R] (θ : L ⧸ Subgroup.center L ≃* R)
    (hN : Bs ≤ Subgroup.normalizer (L : Set G)) {r : ℕ} (hlift : GGTorusLift 3 r R) :
    3 ^ r ≤ Nat.card (ggGamma L hN).range :=
  (card_range_ggGamma_bstar_ge hS.1.1 hS.2.1.1 θ hN hlift).1

theorem ggQ2UnitDvd_label_arith {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab)
    (hq2 : GGLabQTwo 3 lab) (htag : lab.tag = .twA) (h3d : 3 ∣ lab.rank + 1) :
    lab.n = 1 ∧ 6 ≤ lab.rank + 1 ∧ 3 ∣ lab.rank + 1 := by
  obtain ⟨t, r, n⟩ := lab
  dsimp only at htag hq2 h3d hlab
  subst htag
  have hn : 1 ≤ n := hlab.1
  have hq : n < 2 := hq2
  have hn1 : n = 1 := by omega
  subst hn1
  have hr2 : 2 ≤ r := hlab.2.1
  have hd6 : 6 ≤ r + 1 := by
    have h3 : r + 1 ≠ 3 := by
      intro h
      have hr2 : r = 2 := by omega
      have hn2 : 2 ≤ 1 := hlab.2.2 hr2
      omega
    have h3' : 3 ≤ r + 1 := by omega
    have h3d' : 3 ∣ r + 1 := h3d
    obtain ⟨k, hk⟩ := h3d'
    have hk2 : 2 ≤ k := by
      by_contra h
      have hk1 : k = 1 := by omega
      subst hk1
      omega
    omega
  exact ⟨rfl, hd6, h3d⟩

theorem ggQ2UnitDvd_gamma_ge_at_nine
    {G : Type} [Group G]
    [Finite G] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hS : GGQTwoSetting 3 B Bs x L D J) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = (2 ^ 1) ^ 2) {rank : ℕ} (hd6 : 6 ≤ rank + 1)
    (h3d : 3 ∣ rank + 1) (h6 : ¬ rank + 1 = 6)
    {θ : L ⧸ Subgroup.center L ≃*
      LargeEvenProj (LargeEvenSUGroup (Fin (rank + 1)) K (2 ^ 1))}
    (hN : Bs ≤ Subgroup.normalizer (L : Set G)) :
    3 ^ ((rank + 1) / 3 + 2) ≤ Nat.card (ggGamma L hN).range := by
  obtain ⟨k, hk⟩ := h3d
  have h9 : 9 ≤ rank + 1 := by
    have hk2 : 2 ≤ k := by
      rw [hk] at hd6
      omega
    have hk3 : 3 ≤ k := by
      by_contra h
      have hk_eq : k = 2 := by omega
      apply h6
      rw [hk, hk_eq]
    omega
  have h3d' : 3 ∣ rank + 1 := ⟨k, hk⟩
  have hdq : ((rank + 1), 2 ^ 1) ≠ (3, 2) := by
    intro h
    have := congrArg Prod.fst h
    omega
  have hlift : GGTorusLift 3 (ggUnitaryTorusRank 3 (rank + 1))
      (LargeEvenProj (LargeEvenSUGroup (Fin (rank + 1)) K (2 ^ 1))) :=
    ggTorusLift_unitary (K := K) (n := 1) (d := rank + 1) (p := 3) hK
      (by norm_num) (by omega) hdq Nat.prime_three (by norm_num)
  have hrank : ggUnitaryTorusRank 3 (rank + 1) = rank - 2 := by
    simp [ggUnitaryTorusRank, h3d']
  rw [hrank] at hlift
  have hbig := ggQ2UnitDvd_gamma_ge_of_torusLift hS (θ := θ) hN hlift
  refine le_trans ?_ hbig
  have hdiv : (rank + 1) / 3 = k := by
    rw [hk, Nat.mul_div_cancel_left _ (by norm_num : 0 < 3)]
  have hrank2 : rank - 2 = 3 * k - 3 := by omega
  rw [hdiv, hrank2]
  apply Nat.pow_le_pow_right (by norm_num)
  omega

theorem ggQ2UnitDvd_gamma_ge_at
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} (hS : GGQTwoSetting 3 B Bs x L D J)
    {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab) (hq : GGLabQTwo 3 lab)
    (htag : lab.tag = .twA) (h3d : 3 ∣ lab.rank + 1)
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = (2 ^ lab.n) ^ 2)
    (hsimple : IsSimpleGroup
      (LargeEvenProj (LargeEvenSUGroup (Fin (lab.rank + 1)) K (2 ^ lab.n))))
    (hnab : ∃ a b : LargeEvenProj (LargeEvenSUGroup (Fin (lab.rank + 1)) K (2 ^ lab.n)),
      a * b ≠ b * a)
    {θ : L ⧸ Subgroup.center L ≃*
      LargeEvenProj (LargeEvenSUGroup (Fin (lab.rank + 1)) K (2 ^ lab.n))}
    (hN : Bs ≤ Subgroup.normalizer (L : Set G))
    (hBsI0 : ∀ b ∈ Bs, ∃ φ ∈ LargeEvenMatConjImage
      (LargeEvenProjMk (LargeEvenSUGroup (Fin (lab.rank + 1)) K (2 ^ lab.n)))
      (LargeEvenGUSet (Fin (lab.rank + 1)) K (2 ^ lab.n)),
      LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) φ)
    (hperf : commutator L = ⊤) :
    3 ^ ((lab.rank + 1) / 3 + 2) ≤ Nat.card (ggGamma L hN).range := by
  obtain ⟨tag, rank, n⟩ := lab
  subst htag
  obtain ⟨hn1, hd6, -⟩ := ggQ2UnitDvd_label_arith hlab hq rfl h3d
  subst hn1
  by_cases h6 : rank + 1 = 6
  · have hlab63 : GGUnitDvd63Label 3 ⟨.twA, rank, 1⟩ := by
      have hrank5 : rank = 5 := by omega
      have h3r : 3 ≤ rank := by omega
      exact ⟨⟨rfl, h3r, by norm_num, h3d⟩, hrank5, rfl⟩
    have hsplit : LargeEvenSplit 3 ⟨.twA, rank, 1⟩ := by
      refine Or.inr (Or.inl ⟨by simp [LargeEvenUntwisted], by simp, by norm_num⟩)
    have hM : GGInnerDiagOnLab GGUnitDvd63Label 3 Bs L := by
      refine ⟨hperf, ⟨.twA, rank, 1⟩, hlab, ?_⟩
      dsimp only [LargeEvenRawDatum]
      exact ⟨K, inferInstance, inferInstance, hK, hsimple, hnab, θ, hlab63, hsplit,
        hN, hBsI0⟩
    have h4 := (card_range_ggGamma_unitDvd63 hS.1.1 hM hN).1
    have hdiv : (rank + 1) / 3 + 2 = 4 := by rw [h6]
    rw [hdiv]
    exact h4
  · exact ggQ2UnitDvd_gamma_ge_at_nine (θ := θ) hS hK hd6 h3d h6 hN

theorem range_ggBeta_eq_map_ggGamma {G : Type} [Group G] {L Bs : Subgroup G} {R : Type}
    [Group R] (θ : L ⧸ Subgroup.center L ≃* R)
    (hN : Bs ≤ Subgroup.normalizer (L : Set G)) :
    (ggBeta L θ hN).range = Subgroup.map (ggInducedAut θ) (ggGamma L hN).range := by
  ext x
  constructor
  · rintro ⟨b, rfl⟩
    refine ⟨ggGamma L hN b, ⟨b, rfl⟩, ?_⟩
    rw [ggBeta_eq, ggLAut_eq_ggInducedAut]
    rfl
  · rintro ⟨y, ⟨b, rfl⟩, rfl⟩
    refine ⟨b, ?_⟩
    rw [ggBeta_eq, ggLAut_eq_ggInducedAut]
    rfl

theorem ggQ2UnitDvd_frame_heart
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} (hS : GGQTwoSetting 3 B Bs x L D J)
    {K : Type} [Field K] [Finite K] {n d : ℕ} (hK : Nat.card K = (2 ^ n) ^ 2) (hn : 1 ≤ n)
    (hd : 3 ≤ d) (hdq : ¬(d = 3 ∧ 2 ^ n = 2)) (hpq : 3 ∣ 2 ^ n + 1)
    {θ : L ⧸ Subgroup.center L ≃* LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n))}
    (hN : Bs ≤ Subgroup.normalizer (L : Set G))
    {Q : GL (Fin d) K}
    (hQ : Q ∈ CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.primeFormUnitary
      (TableBU.unitaryFieldData_of_card hK hn)
      (CFSG.RankThree.PartOne.KCUnitaryModel.idGram K d))
    (hfr : ∀ a ∈ (ggBeta L θ hN).range, ∃ σ : Fin d → Kˣ,
      σ ⟨0, by omega⟩ = 1 ∧ (∀ k, σ k ^ 3 = 1) ∧
      (∀ k, ((σ k : Kˣ) : K) ^ (2 ^ n + 1) = 1) ∧
      TableBUD.FrameAct (TableBU.unitaryFieldData_of_card hK hn) Q hQ a σ) :
    ∀ τ : Fin d → Kˣ, τ ⟨0, by omega⟩ = 1 → (∀ k, τ k ^ 3 = 1) → ∏ k, τ k = 1 →
      ∃ a ∈ (ggBeta L θ hN).range,
        TableBUD.FrameAct (TableBU.unitaryFieldData_of_card hK hn) Q hQ a τ := by
  classical
  intro τ hτ0 hτ hprod
  let hU : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 2 n K :=
    TableBU.unitaryFieldData_of_card hK hn
  have hperf : commutator L = ⊤ := hS.2.1.1
  have hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ 3 = 1 → g ∈ Bs :=
    hS.1.1.2.1.2.2.2
  let s : ↥(unitarySU 2 n K d) :=
    ⟨diagHom d τ, TableBUDL.diagHom_mem_unitarySU hU hpq hτ hprod⟩
  have hsp : s ^ 3 = 1 := Subtype.ext (by
    show ((diagHom d τ : GL (Fin d) K) ^ 3) = 1
    exact TableBUDL.diagHom_pow_eq_one hτ)
  have hdq' : (d, 2 ^ n) ≠ (3, 2) := by
    rintro h
    exact hdq ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩
  obtain ⟨e, he3, hψe, hfix⟩ := TableBUDL.exists_lift_fix (p := 3) hU hK hn hd hdq'
    Nat.prime_three (by norm_num) (ggQuotHom_surjective θ) (by rw [ker_ggQuotHom]) hperf
    Q hQ s hsp
  have hself := ggTorusSelfCent_ggGamma (p := 3) hN hSC
  have heA : MulAut.conj e ∈ (ggGamma L hN).range := by
    refine hself e ?_ he3
    intro a ha
    obtain ⟨b, rfl⟩ := ha
    obtain ⟨σ, -, -, hσn, hfrσ⟩ := hfr (ggBeta L θ hN b) ⟨b, rfl⟩
    refine hfix (ggGamma L hN b) (ggBeta L θ hN b) (diagHom d σ) ?_ ?_ hfrσ ?_
    · exact TableBUD.diagHom_mem_primeFormUnitary hU hσn
    · intro l
      exact ggBeta_ggQuotHom L hN θ b l
    · rw [← map_mul, ← map_mul, mul_comm]
  refine ⟨ggInducedAut θ (MulAut.conj e), ?_, ?_⟩
  · rw [range_ggBeta_eq_map_ggGamma]
    exact ⟨MulAut.conj e, heA, rfl⟩
  · rw [tpq_ggInducedAut_conj]
    rw [show θ (QuotientGroup.mk e : ↥L ⧸ Subgroup.center L) = InndiagSU.frameMk hU Q hQ s from hψe]
    exact TableBUDL.frameAct_conj_frameMk (s := s) (τ := τ) rfl

@[expose] def ggQ2UnitDvdNormalizedTorus (d : ℕ) (K : Type) [Field K] (hd : 2 ≤ d) :
    Subgroup (Fin d → Kˣ) where
  carrier := {σ | σ ⟨0, by omega⟩ = 1}
  one_mem' := rfl
  mul_mem' := by
    intro a b ha hb
    show (a * b) ⟨0, by omega⟩ = 1
    rw [Pi.mul_apply, ha, hb, one_mul]
  inv_mem' := by
    intro a ha
    show (a⁻¹) ⟨0, by omega⟩ = 1
    rw [Pi.inv_apply, ha, inv_one]

@[expose] def ggQ2UnitDvdProd (d : ℕ) (K : Type) [Field K] (hd : 2 ≤ d) :
    ggQ2UnitDvdNormalizedTorus d K hd →* Kˣ where
  toFun σ := ∏ k, (σ : Fin d → Kˣ) k
  map_one' := by simp
  map_mul' := by
    intro a b
    simp only [Subgroup.coe_mul, Pi.mul_apply]
    rw [Finset.prod_mul_distrib]

theorem ggQ2UnitDvdNormalizedTorus_card {d : ℕ} {K : Type} [Field K] [Finite K]
    (hd : 2 ≤ d) (hK : Nat.card K = (2 ^ 1) ^ 2) :
    Nat.card (ggQ2UnitDvdNormalizedTorus d K hd) = 3 ^ (d - 1) := by
  change Nat.card {σ : Fin d → Kˣ // σ ⟨0, by omega⟩ = 1} = 3 ^ (d - 1)
  exact QTwoUnitary.card_normalized_weights hK (by omega)

theorem ggQ2UnitDvdProd_surjective {d : ℕ} {K : Type} [Field K] [Finite K]
    (hd : 2 ≤ d) :
    Function.Surjective (ggQ2UnitDvdProd d K hd) := by
  intro c
  let σ : Fin d → Kˣ := fun k => if k = (⟨1, by omega⟩ : Fin d) then c else 1
  have hσ0 : σ ⟨0, by omega⟩ = 1 := by
    show (if (⟨0, by omega⟩ : Fin d) = ⟨1, by omega⟩ then c else 1) = 1
    rw [if_neg]
    exact Fin.ext_iff.not.mpr (by norm_num)
  refine ⟨⟨σ, hσ0⟩, ?_⟩
  change (∏ k, (σ : Fin d → Kˣ) k) = c
  rw [show σ = (fun k => if k = (⟨1, by omega⟩ : Fin d) then c else 1) from rfl]
  rw [Finset.prod_eq_single (⟨1, by omega⟩ : Fin d)]
  · simp
  · intro b _ hb
    simp [hb]
  · intro h
    exact absurd (Finset.mem_univ (⟨1, by omega⟩ : Fin d)) h

theorem ggQ2UnitDvdDetOneCard {d : ℕ} {K : Type} [Field K] [Finite K]
    (hd : 2 ≤ d) (hK : Nat.card K = (2 ^ 1) ^ 2) :
    Nat.card (ggQ2UnitDvdProd d K hd).ker = 3 ^ (d - 2) := by
  have hsurj := ggQ2UnitDvdProd_surjective (d := d) (K := K) hd
  have hAd := ggQ2UnitDvdNormalizedTorus_card (d := d) (K := K) hd hK
  have h1 := Subgroup.card_ker_mul_card_range (ggQ2UnitDvdProd d K hd)
  rw [MonoidHom.range_eq_top.mpr hsurj, Subgroup.card_top, hAd] at h1
  have hK3 : Nat.card Kˣ = 3 := by rw [Nat.card_units, hK]; norm_num
  rw [hK3] at h1
  have hpow : 3 ^ (d - 1) = 3 ^ (d - 2) * 3 := by
    rw [← pow_succ]
    congr 1
    omega
  rw [hpow] at h1
  exact Nat.eq_of_mul_eq_mul_right (by norm_num) h1

theorem ggQ2UnitDvdDetOneLeFrameWeights
    {G : Type} [Group G]
    [Finite G] {Bs L : Subgroup G}
    {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = (2 ^ 1) ^ 2) {d : ℕ} (hd : 2 ≤ d) (hd3 : 3 ∣ d)
    {θ : L ⧸ Subgroup.center L ≃*
      LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ 1))}
    (hN : Bs ≤ Subgroup.normalizer (L : Set G))
    {Q : GL (Fin d) K}
    (hQ : Q ∈ CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.primeFormUnitary
      (TableBU.unitaryFieldData_of_card hK (by norm_num))
      (CFSG.RankThree.PartOne.KCUnitaryModel.idGram K d))
    (hheart : ∀ τ : Fin d → Kˣ, τ ⟨0, by omega⟩ = 1 → (∀ k, τ k ^ 3 = 1) →
      ∏ k, τ k = 1 → ∃ a ∈ (ggBeta L θ hN).range,
        TableBUD.FrameAct (TableBU.unitaryFieldData_of_card hK (by norm_num)) Q hQ a τ) :
    (ggQ2UnitDvdProd d K (by omega)).ker.map
        (ggQ2UnitDvdNormalizedTorus d K (by omega)).subtype ≤
      TableBUD.frameWeights (TableBU.unitaryFieldData_of_card hK (by norm_num)) Q hQ
        (by omega) 3 (ggBeta L θ hN).range := by
  rintro _ ⟨σ₀, hσ₀, rfl⟩
  have hprod : ∏ k, (σ₀ : Fin d → Kˣ) k = 1 := by
    change ggQ2UnitDvdProd d K (by omega) σ₀ = 1 at hσ₀
    change (∏ k, (σ₀ : Fin d → Kˣ) k) = 1 at hσ₀
    exact hσ₀
  have hcube : ∀ k, (σ₀ : Fin d → Kˣ) k ^ 3 = 1 := by
    intro k
    have h := pow_card_eq_one (x := (σ₀ : Fin d → Kˣ) k)
    rw [show Fintype.card Kˣ = 3 by
      rw [← Nat.card_eq_fintype_card, Nat.card_units, hK]
      norm_num] at h
    exact h
  obtain ⟨a, haA, hfrτ⟩ := hheart (σ₀ : Fin d → Kˣ) σ₀.2 hcube hprod
  exact ⟨σ₀.2, hcube, (by
    intro k
    have h := hcube k
    rw [show (2 ^ 1 + 1 : ℕ) = 3 by norm_num]
    simpa using congrArg (fun x : Kˣ => (x : K)) h), a, haA, hfrτ⟩

theorem ggQ2UnitDvd_exists_frame
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G}
    {x : G} {L D J : Subgroup G} (hS : GGQTwoSetting 3 B Bs x L D J)
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = (2 ^ 1) ^ 2) {d : ℕ}
    (hd : 6 ≤ d) (hd3 : 3 ∣ d)
    {θ : L ⧸ Subgroup.center L ≃* LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ 1))}
    (hN : Bs ≤ Subgroup.normalizer (L : Set G))
    (hBsI0 : ∀ b ∈ Bs, ∃ φ ∈ LargeEvenMatConjImage
      (LargeEvenProjMk (LargeEvenSUGroup (Fin d) K (2 ^ 1)))
      (LargeEvenGUSet (Fin d) K (2 ^ 1)),
      LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) φ)
    (hcard : 3 ^ (d / 3 + 2) ≤ Nat.card (ggBeta L θ hN).range) :
    ∃ (Q : GL (Fin d) K),
      ∃ (hQ : Q ∈ CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.primeFormUnitary
        (TableBU.unitaryFieldData_of_card hK (by norm_num))
        (CFSG.RankThree.PartOne.KCUnitaryModel.idGram K d)),
      (∀ a ∈ (ggBeta L θ hN).range, ∃ σ : Fin d → Kˣ,
        σ ⟨0, by omega⟩ = 1 ∧ (∀ k, σ k ^ 3 = 1) ∧
        (∀ k, ((σ k : Kˣ) : K) ^ (2 ^ 1 + 1) = 1) ∧
        TableBUD.FrameAct (TableBU.unitaryFieldData_of_card hK (by norm_num)) Q hQ a σ) ∧
      (∀ τ : Fin d → Kˣ, τ ⟨0, by omega⟩ = 1 → (∀ k, τ k ^ 3 = 1) →
        ∏ k, τ k = 1 → ∃ a ∈ (ggBeta L θ hN).range,
          TableBUD.FrameAct (TableBU.unitaryFieldData_of_card hK (by norm_num)) Q hQ a τ) := by
  classical
  let hU : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 2 1 K :=
    TableBU.unitaryFieldData_of_card hK (by norm_num)
  let A := (ggBeta L θ hN).range
  have hBsE : IsElemAbelian 3 Bs := (hS.1.1.tableB_facts).2.1
  have hEA : IsElemAbelian 3 A := isElemAbelian_range_ggBeta θ hBsE hN
  have h3D : ∀ b ∈ Bs, ∃ φ ∈ InndiagSU.inndiagU hU (by omega),
      LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) φ := by
    intro b hb
    obtain ⟨φ, hφI, hind⟩ := hBsI0 b hb
    exact ⟨φ, (InndiagSU.mem_inndiagU (h := hU) (hd := by omega)).mpr
      (InndiagSU.congr_mem_primeFormD hU (by omega) hK hφI), hind⟩
  have hAR : A ≤ InndiagSU.inndiagU hU (by omega) :=
    QTwoUnitary.range_ggBeta_le_inndiagU_of_induces hU (by omega) θ hN h3D
  have hdq : (d, 2 ^ 1) ≠ (3, 2) := by
    intro h
    have := congrArg Prod.fst h
    omega
  have hdq' : ¬(d = 3 ∧ 2 ^ 1 = 2) := by
    intro h
    exact hdq (Prod.ext h.1 h.2)
  have hbig : 3 ^ (d / 3 + 1) < Nat.card A := by
    have h3 : d / 3 + 1 < d / 3 + 2 := by omega
    exact (Nat.pow_lt_pow_right (by norm_num : 1 < 3) h3).trans_le hcard
  obtain ⟨Q, hQ, hfr⟩ := TableBUD.exists_frame_inndiag (h := hU) hK (by omega) hdq hdq'
    Nat.prime_three (by norm_num) hEA hAR hbig
  have hheart := ggQ2UnitDvd_frame_heart (n := 1) hS hK (by norm_num) (by omega) hdq'
    (by norm_num) hN hQ hfr
  exact ⟨Q, hQ, hfr, hheart⟩

theorem ggQ2UnitDvd_index_dichotomy
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G}
    {x : G} {L D J : Subgroup G} (hS : GGQTwoSetting 3 B Bs x L D J)
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = (2 ^ 1) ^ 2) {d : ℕ}
    (hd : 6 ≤ d) (hd3 : 3 ∣ d)
    {θ : L ⧸ Subgroup.center L ≃* LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ 1))}
    (hN : Bs ≤ Subgroup.normalizer (L : Set G))
    (hBsI0 : ∀ b ∈ Bs, ∃ φ ∈ LargeEvenMatConjImage
      (LargeEvenProjMk (LargeEvenSUGroup (Fin d) K (2 ^ 1)))
      (LargeEvenGUSet (Fin d) K (2 ^ 1)),
      LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) φ)
    (hcard : 3 ^ (d / 3 + 2) ≤ Nat.card (ggBeta L θ hN).range) :
    Nat.card (ggBeta L θ hN).range = 3 ^ (d - 1) ∨
      Nat.card (ggBeta L θ hN).range = 3 ^ (d - 2) := by
  classical
  let hU : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 2 1 K :=
    TableBU.unitaryFieldData_of_card hK (by norm_num)
  let A := (ggBeta L θ hN).range
  have hdq : (d, 2 ^ 1) ≠ (3, 2) := by
    intro h
    have := congrArg Prod.fst h
    omega
  obtain ⟨Q, hQ, hfr, hheart⟩ :=
    ggQ2UnitDvd_exists_frame (θ := θ) hS hK hd hd3 hN hBsI0 hcard
  let W := TableBUD.frameWeights hU Q hQ (by omega) 3 A
  have hWcard : Nat.card W = Nat.card A :=
    TableBUD.card_frameWeights (h := hU) (Q := Q) (hQ := hQ) hK (by omega) hdq
      Nat.prime_three (by norm_num) hfr
  let Dd : Subgroup (Fin d → Kˣ) :=
    (ggQ2UnitDvdProd d K (by omega)).ker.map
      (ggQ2UnitDvdNormalizedTorus d K (by omega)).subtype
  have hDcard : Nat.card Dd = 3 ^ (d - 2) := by
    change Nat.card ((ggQ2UnitDvdProd d K (by omega)).ker.map
      (ggQ2UnitDvdNormalizedTorus d K (by omega)).subtype) = 3 ^ (d - 2)
    rw [Subgroup.card_map_of_injective
      (ggQ2UnitDvdNormalizedTorus d K (by omega)).subtype_injective,
      ggQ2UnitDvdDetOneCard (by omega) hK]
  have hDdW : Dd ≤ W :=
    ggQ2UnitDvdDetOneLeFrameWeights (θ := θ) hK (by omega) hd3 hN hQ hheart
  have hWA : W ≤ ggQ2UnitDvdNormalizedTorus d K (by omega) := fun σ hσ => hσ.1
  have hWdvd : Nat.card W ∣ Nat.card (ggQ2UnitDvdNormalizedTorus d K (by omega)) :=
    Subgroup.card_dvd_of_le hWA
  rw [ggQ2UnitDvdNormalizedTorus_card (by omega) hK] at hWdvd
  obtain ⟨k, hk_le, hWk⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hWdvd
  have hDle : 3 ^ (d - 2) ≤ Nat.card W := by
    rw [← hDcard]
    exact Subgroup.card_le_of_le hDdW
  have hk_ge : d - 2 ≤ k := by
    rw [hWk] at hDle
    exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 3)).mp hDle
  have hk : k = d - 2 ∨ k = d - 1 := by omega
  rcases hk with rfl | rfl
  · right
    rw [← hWcard, hWk]
  · left
    rw [← hWcard, hWk]

theorem ggQ2UnitDvd_frame_weight_prod
    {G : Type} [Group G] [Finite G] {Bs L : Subgroup G}
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = (2 ^ 1) ^ 2) {d : ℕ}
    (hd : 6 ≤ d) (hdq : (d, 2 ^ 1) ≠ (3, 2)) (hd3 : 3 ∣ d)
    {θ : L ⧸ Subgroup.center L ≃* LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ 1))}
    (hN : Bs ≤ Subgroup.normalizer (L : Set G))
    (hcard : Nat.card (ggBeta L θ hN).range = 3 ^ (d - 2))
    {Q : GL (Fin d) K}
    (hQ : Q ∈ CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.primeFormUnitary
      (TableBU.unitaryFieldData_of_card hK (by norm_num))
      (CFSG.RankThree.PartOne.KCUnitaryModel.idGram K d))
    (hfr : ∀ a ∈ (ggBeta L θ hN).range, ∃ σ : Fin d → Kˣ,
      σ ⟨0, by omega⟩ = 1 ∧ (∀ k, σ k ^ 3 = 1) ∧
      (∀ k, ((σ k : Kˣ) : K) ^ (2 ^ 1 + 1) = 1) ∧
      TableBUD.FrameAct (TableBU.unitaryFieldData_of_card hK (by norm_num)) Q hQ a σ)
    (hheart : ∀ τ : Fin d → Kˣ, τ ⟨0, by omega⟩ = 1 → (∀ k, τ k ^ 3 = 1) →
      ∏ k, τ k = 1 → ∃ a ∈ (ggBeta L θ hN).range,
        TableBUD.FrameAct (TableBU.unitaryFieldData_of_card hK (by norm_num)) Q hQ a τ) :
    ∀ σ ∈ TableBUD.frameWeights (TableBU.unitaryFieldData_of_card hK (by norm_num))
      Q hQ (by omega) 3 (ggBeta L θ hN).range, ∏ k, (σ : Fin d → Kˣ) k = 1 := by
  classical
  let hU : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 2 1 K :=
    TableBU.unitaryFieldData_of_card hK (by norm_num)
  let A := (ggBeta L θ hN).range
  let W := TableBUD.frameWeights hU Q hQ (by omega) 3 A
  have hWcard : Nat.card W = 3 ^ (d - 2) := by
    rw [TableBUD.card_frameWeights (h := hU) (Q := Q) (hQ := hQ) hK (by omega : 3 ≤ d) hdq
      Nat.prime_three (by norm_num) hfr, hcard]
  let Dd : Subgroup (Fin d → Kˣ) :=
    (ggQ2UnitDvdProd d K (by omega)).ker.map
      (ggQ2UnitDvdNormalizedTorus d K (by omega)).subtype
  have hDcard : Nat.card Dd = 3 ^ (d - 2) := by
    change Nat.card ((ggQ2UnitDvdProd d K (by omega)).ker.map
      (ggQ2UnitDvdNormalizedTorus d K (by omega)).subtype) = 3 ^ (d - 2)
    rw [Subgroup.card_map_of_injective
      (ggQ2UnitDvdNormalizedTorus d K (by omega)).subtype_injective,
      ggQ2UnitDvdDetOneCard (by omega) hK]
  have hDdW : Dd ≤ W :=
    ggQ2UnitDvdDetOneLeFrameWeights (θ := θ) hK (by omega) hd3 hN hQ hheart
  have hWeq : W = Dd := by
    symm
    apply Subgroup.eq_of_le_of_card_ge hDdW
    rw [hWcard, hDcard]
  intro σ hσ
  change σ ∈ W at hσ
  rw [hWeq] at hσ
  obtain ⟨σ₀, hσ₀, hσθ⟩ := hσ
  rw [← hσθ]
  change ggQ2UnitDvdProd d K (by omega) σ₀ = 1 at hσ₀
  change (∏ k, (σ₀ : Fin d → Kˣ) k) = 1 at hσ₀
  exact hσ₀

theorem ggQ2UnitDvd_actor_lift
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G}
    {x : G} {L D J : Subgroup G} (hS : GGQTwoSetting 3 B Bs x L D J)
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = (2 ^ 1) ^ 2) {d : ℕ}
    (hd : 6 ≤ d) (hdq : (d, 2 ^ 1) ≠ (3, 2)) (hd3 : 3 ∣ d)
    {θ : L ⧸ Subgroup.center L ≃* LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ 1))}
    (hN : Bs ≤ Subgroup.normalizer (L : Set G))
    {Q : GL (Fin d) K}
    (hQ : Q ∈ CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.primeFormUnitary
      (TableBU.unitaryFieldData_of_card hK (by norm_num))
      (CFSG.RankThree.PartOne.KCUnitaryModel.idGram K d))
    (hfr : ∀ a ∈ (ggBeta L θ hN).range, ∃ σ : Fin d → Kˣ,
      σ ⟨0, by omega⟩ = 1 ∧ (∀ k, σ k ^ 3 = 1) ∧
      (∀ k, ((σ k : Kˣ) : K) ^ (2 ^ 1 + 1) = 1) ∧
      TableBUD.FrameAct (TableBU.unitaryFieldData_of_card hK (by norm_num)) Q hQ a σ)
    (hprodW : ∀ σ ∈ TableBUD.frameWeights (TableBU.unitaryFieldData_of_card hK (by norm_num))
      Q hQ (by omega) 3 (ggBeta L θ hN).range, ∏ k, (σ : Fin d → Kˣ) k = 1)
    {b : G} (hb : b ∈ Bs) :
    ∃ l : ↥L, l ^ 3 = 1 ∧
      ggBeta L θ hN ⟨b, hb⟩ = ggInducedAut θ (MulAut.conj l) := by
  have hperf : commutator L = ⊤ := hS.2.1.1
  obtain ⟨σ, hσ0, hσp, hσn, hfrσ⟩ := hfr (ggBeta L θ hN ⟨b, hb⟩) ⟨⟨b, hb⟩, rfl⟩
  have hprodσ : ∏ k, σ k = 1 :=
    hprodW σ ⟨hσ0, hσp, hσn, ⟨ggBeta L θ hN ⟨b, hb⟩, ⟨⟨b, hb⟩, rfl⟩, hfrσ⟩⟩
  have hσ3 : ∀ k, σ k ^ 3 = 1 := hσp
  let s : ↥(unitarySU 2 1 K d) :=
    ⟨diagHom d σ, TableBUDL.diagHom_mem_unitarySU (TableBU.unitaryFieldData_of_card hK
      (by norm_num)) (by norm_num) hσ3 hprodσ⟩
  have hsp : s ^ 3 = 1 := Subtype.ext (by
    show ((diagHom d σ : GL (Fin d) K) ^ 3) = 1
    exact TableBUDL.diagHom_pow_eq_one hσ3)
  obtain ⟨l, hl3, hψl, hfix⟩ := TableBUDL.exists_lift_fix (p := 3)
    (TableBU.unitaryFieldData_of_card hK (by norm_num)) hK (by norm_num)
    (by omega : 3 ≤ d) hdq Nat.prime_three (by norm_num) (ggQuotHom_surjective θ)
    (by rw [ker_ggQuotHom]) hperf Q hQ s hsp
  refine ⟨l, hl3, ?_⟩
  rw [tpq_ggInducedAut_conj]
  rw [show θ (QuotientGroup.mk l : ↥L ⧸ Subgroup.center L) = InndiagSU.frameMk
    (TableBU.unitaryFieldData_of_card hK (by norm_num)) Q hQ s from hψl]
  exact TableBUD.FrameAct.unique hσn hfrσ
    (TableBUDL.frameAct_conj_frameMk (s := s) (τ := σ) rfl)

theorem ggQ2UnitDvd_centralizer_comm {G : Type} [Group G] {Bs L : Subgroup G} {b : G}
    (hb : b ∈ Bs)
    (hN : Bs ≤ Subgroup.normalizer (L : Set G)) {l : ↥L}
    (hgamma : ggGamma L hN ⟨b, hb⟩ = MulAut.conj l) :
    ((l : G)⁻¹ * b) ∈ Subgroup.centralizer (L : Set G) ∧ Commute b (l : G) := by
  let c : G := (l : G)⁻¹ * b
  have hc_cent : c ∈ Subgroup.centralizer (L : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have h1 : (b * y * b⁻¹ : G) = (l : G) * y * (l : G)⁻¹ := by
      have := congrArg (fun z : ↥L => (z : G))
        (congrArg (fun f : MulAut ↥L => f ⟨y, hy⟩) hgamma)
      simpa [ggGamma_coe, MulAut.conj_apply] using this
    have hconj : c * y * c⁻¹ = y := by
      calc c * y * c⁻¹ = (l : G)⁻¹ * (b * y * b⁻¹) * (l : G) := by
            simp only [c]
            group
        _ = (l : G)⁻¹ * ((l : G) * y * (l : G)⁻¹) * (l : G) := by rw [h1]
        _ = y := by group
    have h2 : c * y = y * c := by
      have := congrArg (fun z => z * c) hconj
      simpa only [mul_assoc, inv_mul_cancel, mul_one] using this
    exact h2.symm
  have hbl : Commute b (l : G) := by
    have hcl : c * (l : G) = (l : G) * c :=
      ((Subgroup.mem_centralizer_iff.mp hc_cent) (l : G) l.2).symm
    have h1 : (l : G)⁻¹ * b * (l : G) = b := by
      have h := hcl
      simp only [c] at h
      rw [h]
      group
    calc b * (l : G) = (l : G) * ((l : G)⁻¹ * b * (l : G)) := by group
      _ = (l : G) * b := by rw [h1]
  exact ⟨by simpa only [c] using hc_cent, hbl⟩

theorem ggQ2UnitDvd_cube_commute {G : Type} [Group G] {L : Subgroup G} {b x : G} {l : ↥L}
    (hb3 : b ^ 3 = 1) (hl3 : l ^ 3 = 1) (hbl : Commute b (l : G))
    (hbx : b * x = x * b) (hlx : (l : G) * x = x * (l : G)) :
    ((l : G)⁻¹ * b) ^ 3 = 1 ∧ Commute ((l : G)⁻¹ * b) x := by
  let c : G := (l : G)⁻¹ * b
  have hc3 : c ^ 3 = 1 := by
    have hl3' : (l : G) ^ 3 = 1 := by simpa using congrArg (fun z : ↥L => (z : G)) hl3
    have hcomm : Commute ((l : G)⁻¹) b := hbl.symm.inv_left
    rw [show c = (l : G)⁻¹ * b from rfl, hcomm.mul_pow]
    simp [inv_pow, hl3', hb3]
  have hcx : Commute c x := by
    have hlx' : (l : G)⁻¹ * x = x * (l : G)⁻¹ :=
      Commute.inv_left (show Commute (l : G) x from hlx)
    show c * x = x * c
    calc c * x = (l : G)⁻¹ * (b * x) := by
          rw [show c = (l : G)⁻¹ * b from rfl]
          group
      _ = (l : G)⁻¹ * (x * b) := by rw [hbx]
      _ = ((l : G)⁻¹ * x) * b := by group
      _ = (x * (l : G)⁻¹) * b := by rw [hlx']
      _ = x * ((l : G)⁻¹ * b) := by group
      _ = x * c := by rw [show c = (l : G)⁻¹ * b from rfl]
  exact ⟨by simpa only [c] using hc3, by simpa only [c] using hcx⟩

theorem ggQ2UnitDvd_sup_zpowers_data {G : Type} [Group G] [Finite G] {L : Subgroup G}
    {x c : G} (hcyc : ∀ P : Subgroup G, P ≤ Subgroup.centralizer (L : Set G) →
      IsPGroup 3 P → IsCyclic P)
    (hxC : x ∈ Subgroup.centralizer (L : Set G))
    (hc_cent : c ∈ Subgroup.centralizer (L : Set G)) (hx3 : x ^ 3 = 1) (hx1 : x ≠ 1)
    (hc3 : c ^ 3 = 1) (hcx : Commute c x) :
    Nat.card ↥(Subgroup.zpowers x ⊔ Subgroup.zpowers c) ≤ 3 ∧
      Subgroup.zpowers x ⊔ Subgroup.zpowers c = Subgroup.zpowers x := by
  have hxEA : CFSG.Open.IsElemAbelian 3 (Subgroup.zpowers x) :=
    CFSG.Open.isElemAbelian_zpowers hx3
  have hcEA : CFSG.Open.IsElemAbelian 3 (Subgroup.zpowers c) :=
    CFSG.Open.isElemAbelian_zpowers hc3
  have hcomm_xc : ∀ a ∈ Subgroup.zpowers x, ∀ d' ∈ Subgroup.zpowers c, a * d' = d' * a := by
    intro a ha d' hd'
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hd'
    exact ((hcx.symm.zpow_left m).zpow_right n).eq
  have hsupEA := CFSG.Open.IsElemAbelian.sup_of_commute hxEA hcEA hcomm_xc
  have hsup_mem : Subgroup.zpowers x ⊔ Subgroup.zpowers c ≤
      Subgroup.centralizer (L : Set G) :=
    sup_le (Subgroup.zpowers_le.mpr hxC) (Subgroup.zpowers_le.mpr hc_cent)
  have hxP : IsPGroup 3 (Subgroup.zpowers x) := by
    refine IsPGroup.of_card (p := 3) (n := 1) ?_
    rw [Nat.card_zpowers, orderOf_eq_prime hx3 hx1]
    norm_num
  have hcP : IsPGroup 3 (Subgroup.zpowers c) := by
    by_cases hc1 : c = 1
    · rw [hc1, Subgroup.zpowers_one_eq_bot]
      exact IsPGroup.of_card (p := 3) (n := 0) (by simp)
    · refine IsPGroup.of_card (p := 3) (n := 1) ?_
      rw [Nat.card_zpowers, orderOf_eq_prime hc3 hc1]
      norm_num
  have hcentc : Subgroup.zpowers x ≤ Subgroup.centralizer (Subgroup.zpowers c : Set G) := by
    intro a ha
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact (hcomm_xc a ha y hy).symm
  have hnormc : Subgroup.zpowers x ≤ Subgroup.normalizer (Subgroup.zpowers c : Set G) :=
    hcentc.trans (Subgroup.centralizer_le_normalizer _)
  have hsupP : IsPGroup 3 ↥(Subgroup.zpowers x ⊔ Subgroup.zpowers c) :=
    IsPGroup.to_sup_of_normal_right' hxP hcP hnormc
  have hcyc_sup : IsCyclic ↥(Subgroup.zpowers x ⊔ Subgroup.zpowers c) :=
    hcyc _ hsup_mem hsupP
  have hcardx : Nat.card (Subgroup.zpowers x) = 3 := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime hx3 hx1
  have hsup_card : Nat.card ↥(Subgroup.zpowers x ⊔ Subgroup.zpowers c) ≤ 3 :=
    TableB.card_le_of_isCyclic (by norm_num) hcyc_sup (fun y hy => hsupEA.2 y hy)
  have hsup_eq' : Subgroup.zpowers x = Subgroup.zpowers x ⊔ Subgroup.zpowers c :=
    Subgroup.eq_of_le_of_card_ge (H := Subgroup.zpowers x) (K := _) le_sup_left
      (by rw [hcardx]; exact hsup_card)
  exact ⟨hsup_card, hsup_eq'.symm⟩

theorem ggQ2UnitDvd_mem_zpowers_of_three {G : Type} [Group G] {x c : G}
    (hsup : Subgroup.zpowers x ⊔ Subgroup.zpowers c = Subgroup.zpowers x) :
    c ∈ Subgroup.zpowers x := by
  rw [← hsup]
  exact (le_sup_right : Subgroup.zpowers c ≤ _) (Subgroup.mem_zpowers c)

theorem ggQ2UnitDvd_bstar_le_sup_zpowers
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G}
    {x : G} {L D J : Subgroup G} (hS : GGQTwoSetting 3 B Bs x L D J)
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = (2 ^ 1) ^ 2) {d : ℕ}
    (hd : 6 ≤ d) (hd3 : 3 ∣ d)
    {θ : L ⧸ Subgroup.center L ≃* LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ 1))}
    (hN : Bs ≤ Subgroup.normalizer (L : Set G))
    (hBsI0 : ∀ b ∈ Bs, ∃ φ ∈ LargeEvenMatConjImage
      (LargeEvenProjMk (LargeEvenSUGroup (Fin d) K (2 ^ 1)))
      (LargeEvenGUSet (Fin d) K (2 ^ 1)),
      LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) φ)
    (hcard : Nat.card (ggBeta L θ hN).range = 3 ^ (d - 2)) :
    Bs ≤ L ⊔ Subgroup.zpowers x := by
  classical
  let hU : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 2 1 K :=
    TableBU.unitaryFieldData_of_card hK (by norm_num)
  let A := (ggBeta L θ hN).range
  have hBsE : IsElemAbelian 3 Bs := (hS.1.1.tableB_facts).2.1
  have hdq : (d, 2 ^ 1) ≠ (3, 2) := by
    intro h
    have := congrArg Prod.fst h
    omega
  have hcard_le : 3 ^ (d / 3 + 2) ≤ Nat.card A := by
    change 3 ^ (d / 3 + 2) ≤ Nat.card (ggBeta L θ hN).range
    rw [hcard]
    apply Nat.pow_le_pow_right (by norm_num)
    omega
  obtain ⟨Q, hQ, hfr, hheart⟩ :=
    ggQ2UnitDvd_exists_frame (θ := θ) hS hK hd hd3 hN hBsI0 hcard_le
  have hprodW : ∀ σ ∈ TableBUD.frameWeights hU Q hQ (by omega) 3 A,
      ∏ k, (σ : Fin d → Kˣ) k = 1 :=
    ggQ2UnitDvd_frame_weight_prod (θ := θ) hK hd hdq hd3 hN hcard hQ hfr hheart
  have hSstar : LargeEvenSStar 3 B x L := hS.1.1.1.2.2.2.2.2.2.1
  obtain ⟨-, hxB, hx1, hComp, hcyc⟩ := hSstar
  have hxC : x ∈ Subgroup.centralizer (L : Set G) :=
    mem_centralizer_of_le_centralizer hComp.1
  intro b hb
  have hb3 : b ^ 3 = 1 := by simpa using hBsE.2 b hb
  obtain ⟨l, hl3, hact⟩ :=
    ggQ2UnitDvd_actor_lift (θ := θ) hS hK hd hdq hd3 hN hQ hfr hprodW hb
  have hgamma : ggGamma L hN ⟨b, hb⟩ = MulAut.conj l := by
    apply ggInducedAut_injective_of_perfect hS.2.1.1 θ
    have h1 : ggInducedAut θ (ggGamma L hN ⟨b, hb⟩) = ggBeta L θ hN ⟨b, hb⟩ := by
      rw [ggBeta_eq, ggLAut_eq_ggInducedAut]
      rfl
    rw [h1, hact]
  have hcent_bl := ggQ2UnitDvd_centralizer_comm hb hN hgamma
  have hcc := ggQ2UnitDvd_cube_commute hb3 hl3 hcent_bl.2
    (TableB.IsElemAbelian.comm hBsE hb (hS.1.1.2.1.1 hxB)) (hxC (l : G) l.2)
  have hsup := ggQ2UnitDvd_sup_zpowers_data hcyc hxC hcent_bl.1
    (by simpa using hBsE.2 x (hS.1.1.2.1.1 hxB)) hx1 hcc.1 hcc.2
  have hc_mem : ((l : G)⁻¹ * b) ∈ Subgroup.zpowers x :=
    ggQ2UnitDvd_mem_zpowers_of_three hsup.2
  have hb_eq : b = (l : G) * ((l : G)⁻¹ * b) := by group
  rw [hb_eq]
  exact Subgroup.mul_mem_sup l.2 ((Subgroup.zpowers_le.mpr hc_mem) (Subgroup.mem_zpowers _))
theorem ggQ2UnitDvd_beta_card_bound {G : Type} [Group G] {L Bs : Subgroup G} {R : Type}
    [Group R] (θ : L ⧸ Subgroup.center L ≃* R)
    (hN : Bs ≤ Subgroup.normalizer (L : Set G)) (hperf : commutator L = ⊤) {n : ℕ}
    (hcardγ : n ≤ Nat.card (ggGamma L hN).range) :
    n ≤ Nat.card (ggBeta L θ hN).range := by
  rw [QTwoCav.beta_card hperf θ hN, ← QTwoCav.gamma_card hN]
  exact hcardγ

theorem ggQ2UnitDvd_marking_twA {G : Type} [Group G] [Finite G] {L : Subgroup G}
    (hperf : commutator L = ⊤) (rank : ℕ)
    (hlab : LargeEvenInLambda2 ⟨.twA, rank, 1⟩) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = (2 ^ 1) ^ 2)
    (hsimple : IsSimpleGroup
      (LargeEvenProj (LargeEvenSUGroup (Fin (rank + 1)) K (2 ^ 1))))
    (hnab : ∃ a b : LargeEvenProj (LargeEvenSUGroup (Fin (rank + 1)) K (2 ^ 1)),
      a * b ≠ b * a)
    (θ : L ⧸ Subgroup.center L ≃*
      LargeEvenProj (LargeEvenSUGroup (Fin (rank + 1)) K (2 ^ 1))) :
    LargeEvenMarking L (fun lab' _ _ _ _ _ => lab' = ⟨.twA, rank, 1⟩) := by
  refine ⟨hperf, ⟨.twA, rank, 1⟩, hlab, ?_⟩
  dsimp only [CFSG.Assembly.LargeEvenRawDatumLegacy, CFSG.Assembly.LargeEvenRecipeUnitary]
  exact ⟨K, inferInstance, inferInstance, by simpa using hK, hsimple, hnab, θ, rfl⟩

theorem ggQ2TBFullOrHeart_of_unit_dvd
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hS : GGQTwoSetting p B Bs x L D J) (hp : p = 3)
    (hL : GGInnerDiagOnLabel (fun p lab => GGQ2VACLabUnit p lab ∧ 3 ∣ lab.rank + 1) p Bs L) :
    GGQ2TBFull p Bs L ∨ (GGQ2TBHeart p Bs L ∧ Bs ≤ L ⊔ Subgroup.zpowers x) := by
  subst hp
  obtain ⟨hperf, lab, hlab, hraw⟩ := hL
  obtain ⟨tag, rank, n⟩ := lab
  obtain ⟨R, _, I, F, hQ⟩ := largeEvenRawDatum_exists hraw
  obtain ⟨hsimple, hnab, θ, hP⟩ := hQ
  dsimp only [GGQ2VACLabUnit] at hP
  obtain ⟨⟨⟨hq, htag⟩, h3d⟩, hBsN, hBsI0⟩ := hP
  subst htag
  obtain ⟨hn1, hd6, -⟩ := ggQ2UnitDvd_label_arith hlab hq rfl h3d
  subst hn1
  have hraw_orig := hraw
  dsimp only [LargeEvenRawDatum] at hraw
  obtain ⟨K, hfield, hfin, hK, hsimple₂, hnab₂, θ₂, hP₂⟩ := hraw
  let _ : Field K := hfield
  let _ : Finite K := hfin
  dsimp only [GGQ2VACLabUnit] at hP₂
  obtain ⟨⟨⟨hq₂, htag₂⟩, h3d₂⟩, hBsN₂, hBsI0₂⟩ := hP₂
  have hk1 : Nat.card K = (2 ^ 1) ^ 2 := by simpa using hK
  have hcardγ : 3 ^ ((rank + 1) / 3 + 2) ≤ Nat.card (ggGamma L hBsN₂).range :=
    ggQ2UnitDvd_gamma_ge_at (θ := θ₂) hS hlab hq rfl h3d hK hsimple₂ hnab₂ hBsN₂ hBsI0₂ hperf
  have hcardβ : 3 ^ ((rank + 1) / 3 + 2) ≤ Nat.card (ggBeta L θ₂ hBsN₂).range :=
    ggQ2UnitDvd_beta_card_bound θ₂ hBsN₂ hperf hcardγ
  have hdich := ggQ2UnitDvd_index_dichotomy (θ := θ₂) hS hk1 hd6 h3d hBsN₂ hBsI0₂ hcardβ
  have hmark : LargeEvenMarking L (fun lab' _ _ _ _ _ => lab' = ⟨.twA, rank, 1⟩) :=
    ggQ2UnitDvd_marking_twA hperf rank hlab hK hsimple₂ hnab₂ θ₂
  have hidx : ((Subgroup.centralizer (L : Set G)).subgroupOf Bs).index =
      Nat.card (ggBeta L θ₂ hBsN₂).range :=
    (QTwoCav.beta_card hperf θ₂ hBsN₂).symm
  rcases hdich with hfull | hheart
  · left
    refine ⟨⟨.twA, rank, 1⟩, ?_, hmark, ?_⟩
    · simp [GGLabQTwo]
    · rw [hidx, hfull]
      simp [GGQ2LieRank]
  · right
    have hTB : GGQ2TBHeart 3 Bs L := by
      refine ⟨⟨.twA, rank, 1⟩, ?_, hmark, ?_, ?_⟩
      · simp [GGLabQTwo]
      · exact Or.inl ⟨rfl, h3d⟩
      · rw [hidx, hheart]
        simp [GGQ2LieRank]
    have hle := ggQ2UnitDvd_bstar_le_sup_zpowers (d := rank + 1) hS hk1 hd6 h3d
      (θ := θ₂) hBsN₂ hBsI0₂ hheart
    exact ⟨hTB, hle⟩

theorem ggQTwoGuardFailsOn_unit
    (hCav : GGQ2CavOfTBFull) :
    GGQTwoGuardFailsOn GGQ2VACLabUnit := by
  intro G _ _ p B Bs x L D J hS hp hL
  subst hp
  have hN : Bs ≤ Subgroup.normalizer (L : Set G) := by
    obtain ⟨-, lab, hlab, hraw⟩ := hL
    obtain ⟨R, _, I, F, hQ⟩ := largeEvenRawDatum_exists hraw
    obtain ⟨-, -, θ, hP⟩ := hQ
    exact hP.2.1
  have hPP' : ∀ (lab : LargeEvenLabel) (R : Type) [Group R] (I F : Set (MulAut R))
      (θ : L ⧸ Subgroup.center L ≃* R),
      (GGQ2VACLabUnit 3 lab ∧ Bs ≤ Subgroup.normalizer (L : Set G) ∧
        ∀ b ∈ Bs, ∃ φ ∈ I, LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) φ) →
      (((fun p lab => GGQ2VACLabUnit p lab ∧ 3 ∣ lab.rank + 1) 3 lab) ∨
       ((fun p lab => GGQ2VACLabUnit p lab ∧ ¬ 3 ∣ lab.rank + 1) 3 lab)) ∧
        Bs ≤ Subgroup.normalizer (L : Set G) ∧
        ∀ b ∈ Bs, ∃ φ ∈ I, LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) φ := by
    intro lab R _ I F θ h
    by_cases h3 : 3 ∣ lab.rank + 1
    · exact ⟨Or.inl ⟨h.1, h3⟩, h.2.1, h.2.2⟩
    · exact ⟨Or.inr ⟨h.1, h3⟩, h.2.1, h.2.2⟩
  have hL' : GGInnerDiagOnLabel (fun p lab =>
      ((fun p lab => GGQ2VACLabUnit p lab ∧ 3 ∣ lab.rank + 1) p lab) ∨
      ((fun p lab => GGQ2VACLabUnit p lab ∧ ¬ 3 ∣ lab.rank + 1) p lab)) 3 Bs L :=
    largeEvenMarking_mono hPP' hL
  rcases hL'.elim_or with hLdvd | hLcop
  · rcases ggQ2TBFullOrHeart_of_unit_dvd hS rfl hLdvd with hF | ⟨hH, hle⟩
    · exact hCav hS rfl hF
    · by_cases hJ : CFSG.AGLEmbedding.IsAltTwoP 3 J
      · rw [QTwoB2Cav.card_automizer_original_of_setting hS rfl hN hJ]
      · have h4 := ggQ2_cavOfTBHeartInner_holds hS rfl hH hle hJ hN
        rwa [QTwoCav.card_automizer_inner_image_eq_of_setting hS Nat.prime_three
          (by norm_num) hN] at h4
  · exact ggQTwoGuardFailsOn_unit_of_not_dvd hCav G 3 B Bs x L D J hS rfl hLcop

end CFSG.StandardType

end
