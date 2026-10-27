module

public import CFSG.LocalAnalysis.StandardType.GGNbrInnerWeylComp
public import CFSG.LocalAnalysis.StandardType.GGTableBNbrInnerNineSCr
public import CFSG.LocalAnalysis.StandardType.GGTableBUnit63Nbr
public import CFSG.LocalAnalysis.StandardType.GGTableBNbrInnerSCrCompDefs

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly TableB NbrInnerRest

section Config

variable {G : Type} [Group G] [Finite G]

theorem ggTableBNbrInner_of_ggTorusNbrSCrComp (hL : GGLBalanceInput) (hPJ : GGStdSubPrimeInput)
    {p r : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} (hcfg : GGConfig p B Bs x L D J) {y : G} {K : Subgroup G}
    (hnb : GGNbr p B x D J y K) (hK : commutator K = ⊤) {R : Type} [Group R]
    (θ : K ⧸ Subgroup.center K ≃* R) {I : Set (MulAut R)}
    (hN : Bs ≤ Subgroup.normalizer (K : Set G))
    (hBsI : ∀ (b : G) (hb : b ∈ Bs), ggLAut K θ ⟨b, hN hb⟩ ∈ I)
    (hlift : GGTorusLift p r R) (hT : GGTorusNbrSCrComp p r R I) {Y : Subgroup G}
    (hYN : Y ≤ Subgroup.normalizer (Bs : Set G)) (hYK : Y ≤ Subgroup.normalizer (K : Set G))
    (hYn : ∀ n ∈ Subgroup.normalizer (Bs : Set G) ⊓ Subgroup.centralizer ({y} : Set G),
      ∀ g ∈ Y, n * g * n⁻¹ ∈ Y)
    (hYp : ∀ g ∈ Y, ∃ k : ℕ, g ^ p ^ k ∈ Subgroup.centralizer (Bs : Set G)) :
    ∀ g ∈ Y, ∀ b ∈ Bs, g * b * g⁻¹ * b⁻¹ ∈ Subgroup.centralizer (K : Set G) := by
  classical
  obtain ⟨hp, hBs, hxBs, -, -⟩ := hcfg.tableB_facts
  have := Fact.mk hp
  have hS : LargeEvenSHat p B y K := hnb.1
  have hBBs : B ≤ Bs := hcfg.2.1.1
  have hBN : B ≤ Subgroup.normalizer (K : Set G) := hBBs.trans hN
  have hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs := hcfg.2.1.2.2.2
  have hKy : K ≤ Subgroup.centralizer ({y} : Set G) := hS.2.2.2.1
  set γ := ggGamma K hN with hγ
  have hBp : ∀ b : Bs, b ^ p = 1 := fun b => Subtype.ext (by simpa using hBs.2 b b.2)
  have hBc : ∀ a b : Bs, a * b = b * a := fun a b =>
    Subtype.ext (IsElemAbelian.comm hBs a.2 b.2)
  have hA : IsElemAbelian p γ.range := isElemAbelian_range hBc hBp γ
  have hAI : ∀ a ∈ γ.range, ∃ φ ∈ I, ∀ l : K, φ (ggQuotHom θ l) = ggQuotHom θ (a l) := by
    rintro _ ⟨b, rfl⟩
    exact ⟨ggBeta K θ hN b, hBsI b b.2, fun l => ggBeta_ggQuotHom K hN θ b l⟩
  have hcA := card_range_ggGamma_mul_of_sHat hp hS hBN
  have hle : Nat.card (ggGamma K hBN).range ≤ Nat.card γ.range := by
    refine Subgroup.card_le_of_le ?_
    rintro _ ⟨b, rfl⟩
    exact ⟨⟨b, hBBs b.2⟩, rfl⟩
  have hr : p ^ r ≤ Nat.card γ.range := by
    have h1 := succ_le_twoLocalRank_of_torusLift hp hKy (hS.1.1.2 y hS.2.1) hS.2.2.1 hK θ hlift
    have h2 : p ^ (r + 1) ≤ Nat.card (ggGamma K hBN).range * p := by
      rw [hcA, hS.1.2.1]
      exact Nat.pow_le_pow_right hp.pos h1
    rw [pow_succ] at h2
    exact (Nat.le_of_mul_le_mul_right h2 hp.pos).trans hle
  have h3 : p ^ 3 ≤ Nat.card γ.range := by
    have h4 := pow_four_le_card_of_bmax hp hS.1 hcfg.1.2.2.2.2.2.1.2.2.2
    rw [← hcA, pow_succ] at h4
    exact (Nat.le_of_mul_le_mul_right h4 hp.pos).trans hle
  have hx1 : γ ⟨x, hxBs⟩ ≠ 1 := by
    intro h
    rw [hγ, ggGamma_eq_one_iff] at h
    refine hnb.2.2.2 (le_trans ?_ bot_le)
    rw [le_bot_iff, Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro k hk
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
    exact Commute.zpow_left (Subgroup.mem_centralizer_iff.mp h k hk).symm n
  have hline : ∃ a₀ ∈ γ.range, a₀ ≠ 1 ∧ GGFixCompCyclic p a₀ :=
    ⟨γ ⟨x, hxBs⟩, ⟨_, rfl⟩, hx1, ggFixCompCyclic_ggGamma_x hL hcfg
      (hPJ _ _ _ _ _ _ _ hcfg.1 hcfg.2.2) hnb hN hxBs⟩
  obtain ⟨W, hW1, hW2⟩ := hT K (ggQuotHom θ) (ggQuotHom_surjective θ) (by rw [ker_ggQuotHom])
    hK γ.range hA hAI hr h3 (ggTorusSelfCent_ggGamma hN hSC) hline
  exact ggTableBNbrInner_of_weyl hcfg hnb hN hW1 hW2 hYN hYK hYn hYp

theorem ggTableBNbrInner_of_card {p r : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} (hcfg : GGConfig p B Bs x L D J) {y : G} {K : Subgroup G}
    (hnb : GGNbr p B x D J y K) (hK : commutator K = ⊤) {R : Type} [Group R]
    (θ : K ⧸ Subgroup.center K ≃* R) {I : Set (MulAut R)}
    (hN : Bs ≤ Subgroup.normalizer (K : Set G))
    (hBsI : ∀ (b : G) (hb : b ∈ Bs), ggLAut K θ ⟨b, hN hb⟩ ∈ I)
    (hr : p ^ r ≤ Nat.card (ggGamma K hN).range) (h3 : p ^ 3 ≤ Nat.card (ggGamma K hN).range)
    (hT : U63TB.GGTorusNbrSCrK p r R I) {Y : Subgroup G}
    (hYN : Y ≤ Subgroup.normalizer (Bs : Set G)) (hYK : Y ≤ Subgroup.normalizer (K : Set G))
    (hYn : ∀ n ∈ Subgroup.normalizer (Bs : Set G) ⊓ Subgroup.centralizer ({y} : Set G),
      ∀ g ∈ Y, n * g * n⁻¹ ∈ Y)
    (hYp : ∀ g ∈ Y, ∃ k : ℕ, g ^ p ^ k ∈ Subgroup.centralizer (Bs : Set G)) :
    ∀ g ∈ Y, ∀ b ∈ Bs, g * b * g⁻¹ * b⁻¹ ∈ Subgroup.centralizer (K : Set G) := by
  classical
  obtain ⟨hp, hBs, -, -, -⟩ := hcfg.tableB_facts
  have := Fact.mk hp
  have hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs := hcfg.2.1.2.2.2
  set γ := ggGamma K hN with hγ
  have hBp : ∀ b : Bs, b ^ p = 1 := fun b => Subtype.ext (by simpa using hBs.2 b b.2)
  have hBc : ∀ a b : Bs, a * b = b * a := fun a b =>
    Subtype.ext (IsElemAbelian.comm hBs a.2 b.2)
  have hA : IsElemAbelian p γ.range := isElemAbelian_range hBc hBp γ
  have hAI : ∀ a ∈ γ.range, ∃ φ ∈ I, ∀ l : K, φ (ggQuotHom θ l) = ggQuotHom θ (a l) := by
    rintro _ ⟨b, rfl⟩
    exact ⟨ggBeta K θ hN b, hBsI b b.2, fun l => ggBeta_ggQuotHom K hN θ b l⟩
  have hker : (ggQuotHom θ).ker = Subgroup.center K := ker_ggQuotHom θ
  obtain ⟨W, hW1, hW2⟩ := hT K (ggQuotHom θ) (ggQuotHom_surjective θ) hker.le
    hK γ.range hA hAI hr h3 (ggTorusSelfCent_ggGamma hN hSC)
  refine ggTableBNbrInner_of_weyl hcfg hnb hN hW1 (fun Y' hWA hWY hYA hYp' => ?_) hYN hYK hYn hYp
  refine hW2 Y' (fun f _ z hz => ?_) hWA hWY hYA hYp'
  rw [hker] at hz ⊢
  rw [Subgroup.mem_center_iff] at hz ⊢
  intro g
  obtain ⟨g', rfl⟩ := f.surjective g
  rw [← map_mul, ← map_mul, hz g']

end Config

theorem ggTableBNbrInnerInputOn_of_labelsSCrComp (hL : GGLBalanceInput)
    (hPJ : GGStdSubPrimeInput) {S : ℕ → LargeEvenLabel → Prop}
    (h : ∀ (p : ℕ) (lab : LargeEvenLabel), p.Prime → LargeEvenInLambda2 lab → S p lab →
      LargeEvenLabelAll lab fun R _ I _ => ∃ r, GGTorusLift p r R ∧ GGTorusNbrSCrComp p r R I) :
    GGTableBNbrInnerInputOn S := by
  intro G _ _ p B Bs x L D J hcfg y K hnb hN P hP
  have hp : p.Prime := hcfg.1.2.2.2.2.2.1.1
  obtain ⟨hK, lab, hlab, hraw⟩ := hP
  by_cases hSl : S p lab
  · refine ⟨hK, lab, hlab, largeEvenRawDatum_mono ?_ (h p lab hp hlab hSl _ hraw)⟩
    rintro R _ I F ⟨⟨hs, hna, θ, hPθ⟩, r, hlift, hT⟩
    exact ⟨hs, hna, θ, hPθ, fun _ hBsI Y _ hYN hYK _ hYn hYp =>
      ggTableBNbrInner_of_ggTorusNbrSCrComp hL hPJ hcfg hnb hK θ hN hBsI hlift hT hYN hYK hYn
        hYp⟩
  · refine ⟨hK, lab, hlab, largeEvenRawDatum_mono ?_ hraw⟩
    rintro R _ I F ⟨hs, hna, θ, hPθ⟩
    exact ⟨hs, hna, θ, hPθ, fun hS => absurd hS hSl⟩

end CFSG.StandardType

end
