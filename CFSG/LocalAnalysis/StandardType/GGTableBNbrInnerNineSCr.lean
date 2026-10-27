module

public import CFSG.LocalAnalysis.StandardType.GGTableBNbrInnerNine

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly TableB NbrInnerRest

@[expose] def GGTorusNbrSCr (p r : ℕ) (R : Type) [Group R] (I : Set (MulAut R)) : Prop :=
  ∀ (L' : Type) [Group L'] [Finite L'] (ψ : L' →* R), Function.Surjective ψ →
    ψ.ker ≤ Subgroup.center L' → commutator L' = ⊤ →
    ∀ A : Subgroup (MulAut L'), IsElemAbelian p A →
      (∀ a ∈ A, ∃ φ ∈ I, ∀ l : L', φ (ψ l) = ψ (a l)) →
      p ^ r ≤ Nat.card A → p ^ 3 ≤ Nat.card A → GGTorusSelfCent p A →
      ∃ W : Set L',
        (∀ n ∈ W, ∀ a ∈ A, (n * (a n)⁻¹) ^ p = 1 ∧ ∀ a' ∈ A, a' (n * (a n)⁻¹) = n * (a n)⁻¹) ∧
        ∀ Y : Subgroup (MulAut L'),
          (∀ n ∈ W, ∀ a ∈ A, MulAut.conj n * a * (MulAut.conj n)⁻¹ ∈ A) →
          (∀ n ∈ W, ∀ φ ∈ Y, MulAut.conj n * φ * (MulAut.conj n)⁻¹ ∈ Y) →
          (∀ φ ∈ Y, ∀ a ∈ A, φ * a * φ⁻¹ ∈ A) →
          (∀ φ ∈ Y, ∃ k : ℕ, ∀ a ∈ A, φ ^ p ^ k * a = a * φ ^ p ^ k) →
          ∀ φ ∈ Y, ∀ a ∈ A, φ * a = a * φ

theorem ggTorusNbrSCr_of_ggTorusNbr {p r : ℕ} {R : Type} [Group R] {I : Set (MulAut R)}
    (h : GGTorusNbr p r R I) : GGTorusNbrSCr p r R I :=
  fun L' _ _ ψ hψ hker hperf A hA hAI hr h3 _ => h L' ψ hψ hker hperf A hA hAI hr h3

theorem ggTorusNbrSCr_of_ggTorusNbrSC {p r : ℕ} {R : Type} [Group R] {I : Set (MulAut R)}
    (h : GGTorusNbrSC p R I) : GGTorusNbrSCr p r R I :=
  fun L' _ _ ψ hψ hker hperf A hA hAI _ h3 hsc => h L' ψ hψ hker hperf A hA hAI h3 hsc

theorem ggTorusNbrSCr_of_mulEquiv {p r : ℕ} {R R' : Type} [Group R] [Group R'] (e : R ≃* R')
    {I : Set (MulAut R)} {I' : Set (MulAut R')} (hI : ∀ φ ∈ I, MulAut.congr e φ ∈ I')
    (h : GGTorusNbrSCr p r R' I') : GGTorusNbrSCr p r R I := by
  intro L' _ _ ψ hψ hker hperf A hA hAI hr h3 hsc
  refine h L' (e.toMonoidHom.comp ψ) (e.surjective.comp hψ) ?_ hperf A hA ?_ hr h3 hsc
  · intro l hl
    exact hker (by simpa [MonoidHom.mem_ker] using hl)
  · intro a ha
    obtain ⟨φ, hφ, hφa⟩ := hAI a ha
    refine ⟨MulAut.congr e φ, hI φ hφ, fun l => ?_⟩
    simp [MulAut.congr_apply, hφa l]

section Config

variable {G : Type} [Group G] [Finite G]

theorem ggTableBNbrInner_of_ggTorusNbrSCr {p r : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} (hcfg : GGConfig p B Bs x L D J) {y : G} {K : Subgroup G}
    (hnb : GGNbr p B x D J y K) (hK : commutator K = ⊤) {R : Type} [Group R]
    (θ : K ⧸ Subgroup.center K ≃* R) {I : Set (MulAut R)}
    (hN : Bs ≤ Subgroup.normalizer (K : Set G))
    (hBsI : ∀ (b : G) (hb : b ∈ Bs), ggLAut K θ ⟨b, hN hb⟩ ∈ I)
    (hlift : GGTorusLift p r R) (hT : GGTorusNbrSCr p r R I) {Y : Subgroup G}
    (hYN : Y ≤ Subgroup.normalizer (Bs : Set G)) (hYK : Y ≤ Subgroup.normalizer (K : Set G))
    (hYn : ∀ n ∈ Subgroup.normalizer (Bs : Set G) ⊓ Subgroup.centralizer ({y} : Set G),
      ∀ g ∈ Y, n * g * n⁻¹ ∈ Y)
    (hYp : ∀ g ∈ Y, ∃ k : ℕ, g ^ p ^ k ∈ Subgroup.centralizer (Bs : Set G)) :
    ∀ g ∈ Y, ∀ b ∈ Bs, g * b * g⁻¹ * b⁻¹ ∈ Subgroup.centralizer (K : Set G) := by
  classical
  obtain ⟨hp, hBs, -, -, -⟩ := hcfg.tableB_facts
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
  obtain ⟨W, hW1, hW2⟩ := hT K (ggQuotHom θ) (ggQuotHom_surjective θ) (by rw [ker_ggQuotHom])
    hK γ.range hA hAI hr h3 (ggTorusSelfCent_ggGamma hN hSC)
  exact ggTableBNbrInner_of_weyl hcfg hnb hN hW1 hW2 hYN hYK hYn hYp

end Config

theorem ggTableBNbrInnerInputOn_of_labelsSCr {S : ℕ → LargeEvenLabel → Prop}
    (h : ∀ (p : ℕ) (lab : LargeEvenLabel), p.Prime → LargeEvenInLambda2 lab → S p lab →
      LargeEvenLabelAll lab fun R _ I _ => ∃ r, GGTorusLift p r R ∧ GGTorusNbrSCr p r R I) :
    GGTableBNbrInnerInputOn S := by
  intro G _ _ p B Bs x L D J hcfg y K hnb hN P hP
  have hp : p.Prime := hcfg.1.2.2.2.2.2.1.1
  obtain ⟨hK, lab, hlab, hraw⟩ := hP
  by_cases hSl : S p lab
  · refine ⟨hK, lab, hlab, largeEvenRawDatum_mono ?_ (h p lab hp hlab hSl _ hraw)⟩
    rintro R _ I F ⟨⟨hs, hna, θ, hPθ⟩, r, hlift, hT⟩
    exact ⟨hs, hna, θ, hPθ, fun _ hBsI Y _ hYN hYK _ hYn hYp =>
      ggTableBNbrInner_of_ggTorusNbrSCr hcfg hnb hK θ hN hBsI hlift hT hYN hYK hYn hYp⟩
  · refine ⟨hK, lab, hlab, largeEvenRawDatum_mono ?_ hraw⟩
    rintro R _ I F ⟨hs, hna, θ, hPθ⟩
    exact ⟨hs, hna, θ, hPθ, fun hS => absurd hS hSl⟩

open LocalAnalysis.ComponentInitial.LinearFlag in
@[expose] def GGTypeADvdNbrSCrInput : Prop :=
  ∀ (K : Type) [Field K] [Finite K] [CharP K 2] (d p : ℕ), 5 ≤ d → p.Prime →
    p ∣ Nat.card K - 1 → p ∣ d →
      GGTorusNbrSCr p (d - 2) (projectiveSL d K) (Set.range (conjAut d K))

@[expose] def GGTableBNbrInnerTypeADvdLabel (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  lab.tag = .A ∧ 4 ≤ lab.rank ∧ p ∣ 2 ^ lab.n - 1 ∧ p ∣ lab.rank + 1

theorem ggTableBNbrInnerInputOn_typeADvd
    (hA : GGTypeADvdNbrSCrInput) :
    GGTableBNbrInnerInputOn GGTableBNbrInnerTypeADvdLabel := by
  refine ggTableBNbrInnerInputOn_of_labelsSCr fun p lab hp _ h => ?_
  obtain ⟨t, l, n⟩ := lab
  obtain ⟨ht, hl, hpn, hpd⟩ := h
  dsimp only at ht hl hpn hpd
  subst ht
  intro Q hQ
  dsimp only [LargeEvenRawDatum] at hQ ⊢
  obtain ⟨K, _, _, hK, hQ'⟩ := hQ
  have : CharP K 2 := charP_two_of_card hK
  have hpK : p ∣ Nat.card K - 1 := by rw [hK]; exact hpn
  refine ⟨K, inferInstance, inferInstance, hK, hQ', l + 1 - 2,
    TypeA.ggTorusLift_of_mulEquiv (TypeA.recipeEquiv (l + 1) K)
      (TypeA.ggTorusLift_sub_two hp hpK (by omega) (TypeA.slHasSections_of_five_le (by omega))),
    ggTorusNbrSCr_of_mulEquiv (TypeA.recipeEquiv (l + 1) K)
      (fun _ hφ => TypeA.congr_recipeEquiv_mem hφ) (hA K (l + 1) p (by omega) hp hpK hpd)⟩

section Drop


theorem ggTableBNbrInnerInputOn_round10_of_typeADvd (hA : GGTypeADvdNbrSCrInput)
    (h : GGTableBNbrInnerInputOn fun p lab =>
      GGTableBNbrInnerRound10Label p lab ∧ ¬ GGTableBNbrInnerTypeADvdLabel p lab) :
    GGTableBNbrInnerInputOn GGTableBNbrInnerRound10Label :=
  ((ggTableBNbrInnerInputOn_typeADvd hA).or h).mono fun p lab h10 => by
    by_cases hd : GGTableBNbrInnerTypeADvdLabel p lab
    · exact Or.inl hd
    · exact Or.inr ⟨h10, hd⟩

theorem ggTableBNbrInnerInput_of_typeADvd (hA : GGTypeADvdNbrSCrInput)
    (h : GGTableBNbrInnerInputOn fun p lab =>
      GGTableBNbrInnerRound10Label p lab ∧ ¬ GGTableBNbrInnerTypeADvdLabel p lab) :
    GGTableBNbrInnerInput :=
  ggTableBNbrInnerInput_of_round10 (ggTableBNbrInnerInputOn_round10_of_typeADvd hA h)

end Drop

end CFSG.StandardType

end
