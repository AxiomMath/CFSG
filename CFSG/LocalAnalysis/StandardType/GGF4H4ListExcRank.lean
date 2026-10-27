module

public import CFSG.LocalAnalysis.StandardType.GGF4ThreeNbrRank
public import CFSG.LocalAnalysis.StandardType.GGTBTorF4NonsplitFrame
import CFSG.LocalAnalysis.StandardType.GGNbrU63Setup
import CFSG.LocalAnalysis.StandardType.GGTableBF4Basic

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Open CFSG.Blueprint.Chevalley TableB
open CFSG.LieType.Chevalley CFSG.RankThree.Chevalley

theorem false_of_nbr_torusLift_ge_four {G : Type} [Group G] [Finite G] {p : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hcfg : GGConfig p B Bs x L D J) (hcard : Nat.card Bs = p ^ 4) {y : G} {K : Subgroup G}
    (hnb : GGNbr p B x D J y K) {S : ℕ → LargeEvenLabel → Prop}
    (hM : GGInnerDiagOnLabel S p Bs K)
    (hlift : ∀ lab : LargeEvenLabel, LargeEvenInLambda2 lab → S p lab →
      LargeEvenLabelAll lab fun R _ _ _ => ∃ r, 4 ≤ r ∧ GGTorusLift p r R) :
    False := by
  obtain ⟨hp, -, -, -, -⟩ := hcfg.tableB_facts
  have hS : LargeEvenSHat p B y K := hnb.1
  have hKy : K ≤ Subgroup.centralizer ({y} : Set G) := hS.2.2.2.1
  obtain ⟨hperf, lab, hlab, hraw⟩ := hM
  obtain ⟨_, _, _, _, hQ₀⟩ := largeEvenRawDatum_exists hraw
  obtain ⟨_, _, _, hP₀⟩ := hQ₀
  obtain ⟨hSlab, -, -⟩ := hP₀
  obtain ⟨R, _, _, _, hQ, hliftR⟩ :=
    largeEvenRawDatum_exists (hlift lab hlab hSlab _ hraw)
  obtain ⟨-, -, θ, _⟩ := hQ
  obtain ⟨r, hr4, hlift'⟩ := hliftR
  have hrank := succ_le_twoLocalRank_of_torusLift hp hKy (hS.1.1.2 y hS.2.1) hS.2.2.1
    hperf θ hlift'
  have hcardB : Nat.card B ≤ Nat.card Bs := Subgroup.card_le_of_le hcfg.2.1.1
  rw [hcard, hS.1.2.1] at hcardB
  have hpow : p ^ (r + 1) ≤ p ^ 4 :=
    (Nat.pow_le_pow_right hp.pos hrank).trans hcardB
  have hr : r + 1 ≤ 4 := (pow_le_pow_iff_right₀ hp.one_lt).mp hpow
  omega

theorem false_of_nbr_gamma_ge_four {G : Type} [Group G] [Finite G] {p : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hcfg : GGConfig p B Bs x L D J) (hcard : Nat.card Bs = p ^ 4) {y : G} {K : Subgroup G}
    (hnb : GGNbr p B x D J y K) (hN : Bs ≤ Subgroup.normalizer (K : Set G))
    (hge : p ^ 4 ≤ Nat.card (ggGamma K hN).range) : False := by
  obtain ⟨hp, -, -, -, -⟩ := hcfg.tableB_facts
  have hS : LargeEvenSHat p B y K := hnb.1
  have hyB : y ∈ B := hS.2.1
  have hy1 : y ≠ 1 := hS.2.2.1
  have hKy : K ≤ Subgroup.centralizer ({y} : Set G) := hS.2.2.2.1
  have hyBs : y ∈ Bs := hcfg.2.1.1 hyB
  have hyC : y ∈ Subgroup.centralizer (K : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    exact Subgroup.mem_centralizer_singleton_iff.mp (hKy hk)
  have hy : y ∈ Bs ⊓ Subgroup.centralizer (K : Set G) := ⟨hyBs, hyC⟩
  have hHne : Bs ⊓ Subgroup.centralizer (K : Set G) ≠ ⊥ := by
    intro hbot
    have hybot : y ∈ (⊥ : Subgroup G) := hbot ▸ hy
    exact hy1 (Subgroup.mem_bot.mp hybot)
  have hH : 1 < Nat.card ↥(Bs ⊓ Subgroup.centralizer (K : Set G)) :=
    (Subgroup.one_lt_card_iff_ne_bot (Bs ⊓ Subgroup.centralizer (K : Set G))).mpr hHne
  have hmul := NbrU63.card_range_ggGamma_mul_card_inf hN
  have h2 : p ^ 4 * 2 ≤ Nat.card Bs := by
    calc
      p ^ 4 * 2 ≤ Nat.card (ggGamma K hN).range *
          Nat.card ↥(Bs ⊓ Subgroup.centralizer (K : Set G)) :=
        Nat.mul_le_mul hge (Nat.succ_le_of_lt hH)
      _ = Nat.card Bs := hmul
  rw [hcard] at h2
  have hp4 : 0 < p ^ 4 := pow_pos hp.pos 4
  omega

theorem exists_F4_quotient_of_marking
    {G : Type} [Group G] [Finite G] {p : ℕ}
    {S : ℕ → LargeEvenLabel → Prop} (hS : ∀ lab, S p lab → lab.tag = .F4) {Bs X : Subgroup G}
    (hmk : GGInnerDiagOnLabel S p Bs X) :
    ∃ lab : LargeEvenLabel, S p lab ∧
      ∃ (K₀ : Type) (_ : Field K₀) (_ : Finite K₀) (_ : CharP K₀ 2), Nat.card K₀ = 2 ^ lab.n ∧
        ∃ η : ↥X →* ↥(adjointGroup .F4 K₀), Function.Surjective η ∧
          (∀ x : ↥X, η x = 1 → (x : G) ∈ Subgroup.centralizer (X : Set G)) ∧
          (∀ z ∈ X, z ∈ Subgroup.centralizer (X : Set G) → z ^ 2 = 1) ∧
          Bs ≤ Subgroup.normalizer (X : Set G) ∧
          ∀ b ∈ Bs, ∃ x ∈ X, ∀ l ∈ X, b * l * b⁻¹ = x * l * x⁻¹ := by
  obtain ⟨hX, lab, hlab, hraw⟩ := hmk
  obtain ⟨_, _, _, _, hQ₀⟩ := largeEvenRawDatum_exists hraw
  obtain ⟨_, _, _, hP₀⟩ := hQ₀
  obtain ⟨hSlab, -, -⟩ := hP₀
  obtain ⟨t, l, n⟩ := lab
  obtain rfl : t = .F4 := by
    have h := hS ⟨t, l, n⟩ hSlab
    simpa using h
  obtain ⟨K, _, _, hK, -, -, θ, -, hBsN, hind⟩ := hraw
  have : CharP K 2 := charP_two_of_card hK
  set η : ↥X →* ↥(adjointGroup .F4 K) := (TableBF4.recipeEquiv K).toMonoidHom.comp (ggQuotHom θ)
  have hηs : Function.Surjective η :=
    (TableBF4.recipeEquiv K).surjective.comp (ggQuotHom_surjective θ)
  have hηk : η.ker = Subgroup.center ↥X := by
    rw [MonoidHom.ker_comp_of_injective _ _ (TableBF4.recipeEquiv K).injective, ker_ggQuotHom]
  have hZ := F4AutRefl.card_ker_dvd_two_of_adjointF4 hlab.1 hK hX η hηs hηk.le
  rw [hηk] at hZ
  have hZ2 : ∀ z ∈ X, z ∈ Subgroup.centralizer (X : Set G) → z ^ 2 = 1 := by
    intro z hzX hzC
    have hz : (⟨z, hzX⟩ : ↥X) ∈ Subgroup.center ↥X := Subgroup.mem_center_iff.mpr fun w =>
      Subtype.ext (Subgroup.mem_centralizer_iff.mp hzC w w.2)
    exact congrArg Subtype.val
      (orderOf_dvd_iff_pow_eq_one.mp ((Subgroup.orderOf_dvd_natCard _ hz).trans hZ))
  have hker : ∀ x : ↥X, η x = 1 → (x : G) ∈ Subgroup.centralizer (X : Set G) := by
    intro x hx
    have hx' : x ∈ Subgroup.center ↥X := hηk ▸ hx
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hx' ⟨h, hh⟩)
  refine ⟨⟨.F4, l, n⟩, hSlab, K, inferInstance, inferInstance, inferInstance, hK, η, hηs, hker,
    hZ2, hBsN, F4AutRefl.exists_conj_of_inn hX θ (TableBF4.idImage_subset_inn K) hBsN hind⟩

theorem ggF4Plus_rank_of_marking
    {G : Type} [Group G] [Finite G] {p : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} (hcfg : GGConfig p B Bs x L D J)
    (hp5 : 5 ≤ p) (hT : GGNoTransvection p Bs) {X : Subgroup G}
    (hM : GGInnerDiagOnLabel (fun q lab => lab.tag = .F4 ∧ q ∣ 2 ^ lab.n + 1) p Bs X)
    (hN : Bs ≤ Subgroup.normalizer (X : Set G)) :
    p ^ 4 ≤ Nat.card (ggGamma X hN).range := by
  obtain ⟨hp, -, -, -, -⟩ := hcfg.tableB_facts
  have hodd : Odd p := hp.odd_of_ne_two (by omega)
  obtain ⟨lab, ⟨htag, hpq⟩, K₀, _, _, _, hK₀, η, hηs, hker, hZ2, -, hinner⟩ :=
    exists_F4_quotient_of_marking (fun _ h => h.1) hM
  have hpq' : p ∣ Nat.card K₀ + 1 := hK₀ ▸ hpq
  have hcore : ∀ E : Subgroup (adjointGroup .F4 K₀), IsElemAbelian p E → Nat.card E ≤ p ^ 3 →
      (∀ g ∈ Subgroup.centralizer (E : Set (adjointGroup .F4 K₀)), g ^ p = 1 → g ∈ E) →
        ∃ φ ∈ ggInduced ⊤ E, GGIsTransvection p φ := by
    intro E hE hle hSC
    have : Fact p.Prime := ⟨hp⟩
    have : NeZero p := ⟨hp.ne_zero⟩
    obtain ⟨_, _, _, _, _, _, _, ι, _, _, _, _, _, _, _, hι, hrange, _, _⟩ :=
      F4NonsplitFrame.exists_nonsplit_frame_data hp5 hpq' hE hSC
    have hcardE : Nat.card E = p ^ 4 := by
      rw [← hrange, ← Nat.card_congr (MonoidHom.ofInjective hι).toEquiv]
      rw [Nat.card_congr Multiplicative.toAdd, Nat.card_fun, Nat.card_zmod, Nat.card_fin]
      rfl
    have h43 : 4 ≤ 3 := by
      have hle' : p ^ 4 ≤ p ^ 3 := by rwa [hcardE] at hle
      exact (pow_le_pow_iff_right₀ hp.one_lt).mp hle'
    omega
  have hlow := F4AutRefl.ggRankLower_of_quotient hp hodd hcfg.2.1.2.1
    hcfg.2.1.2.2.2 hinner hZ2 η hηs hker hT hcore
  rw [← NbrU63.card_range_ggGamma_mul_card_inf hN] at hlow
  exact Nat.le_of_mul_le_mul_right hlow Nat.card_pos

end CFSG.StandardType
