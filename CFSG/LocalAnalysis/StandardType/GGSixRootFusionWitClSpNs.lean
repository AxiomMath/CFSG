module

public import CFSG.LocalAnalysis.StandardType.GGSixRootFusionWitClSp

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank CFSG.RankThree.PartTwo.Sec21
open scoped MatrixGroups

@[expose] def GGSixBstarWit {G : Type} [Group G] (p : ℕ) (Bs G₀ : Subgroup G) (t : StatedLieTag)
    (f : ℕ) (b : G) : Prop :=
  b ∈ Bs ∧ b ≠ 1 ∧ ∃ L₁ : Subgroup G, IsComponentOf L₁ (G₀ ⊓ Subgroup.centralizer {b}) ∧
    (Nat.card (Bs ⊓ Subgroup.centralizer (L₁ : Set G) : Subgroup G) ≤ p ^ 2 ∨
      ¬ GGSixSeventeenExcluded p t f L₁)

theorem GGSixBstarWit.fusionWitness {G : Type} [Group G] {p : ℕ} {Bs D E G₀ : Subgroup G}
    {t : StatedLieTag} {f : ℕ} {b : G} (h : GGSixBstarWit p Bs G₀ t f b) :
    GGSixFusionWitness p Bs D E G₀ t f b :=
  ⟨h.2.1, Or.inr (Or.inr ⟨h.1, h.2.2⟩)⟩

namespace WitClSp

theorem conj_frame_witness {U G : Type*} [Group U] [Group G] (φ : U →* G) {A₀ w g X : U}
    (hX : Commute X (g * (A₀⁻¹ * w * A₀) * g⁻¹)) :
    φ (A₀ * (g⁻¹ * X * g) * A₀⁻¹) * φ w = φ w * φ (A₀ * (g⁻¹ * X * g) * A₀⁻¹) ∧
      φ (A₀ * g * A₀⁻¹) * φ (A₀ * (g⁻¹ * X * g) * A₀⁻¹) * (φ (A₀ * g * A₀⁻¹))⁻¹ =
        φ (A₀ * X * A₀⁻¹) := by
  constructor
  · rw [← map_mul, ← map_mul]
    congr 1
    calc A₀ * (g⁻¹ * X * g) * A₀⁻¹ * w =
        A₀ * g⁻¹ * (X * (g * (A₀⁻¹ * w * A₀) * g⁻¹)) * g * A₀⁻¹ := by group
      _ = A₀ * g⁻¹ * (g * (A₀⁻¹ * w * A₀) * g⁻¹ * X) * g * A₀⁻¹ := by rw [hX.eq]
      _ = w * (A₀ * (g⁻¹ * X * g) * A₀⁻¹) := by group
  · rw [← map_inv, ← map_mul, ← map_mul]
    congr 1
    group

end WitClSp

section Inputs

open CFSG.ClassicalInvolution.Models.SymplecticPairs in
@[expose] def GGSpPlaneWitnessInputOn (P : ℕ → ℕ → ℕ → Prop) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (n f : ℕ) (ψ : (ggU .PSp n f).K →* G), P n f p →
    GGSixCtxV2 p B Bs x L D J (ggU .PSp n f).D .PSp n f ψ → GGSixStepOne p B Bs x L D J →
      3 ≤ n ∧ ∃ (A₀ : StatedSp n (GaloisField 2 f)) (T : SL(2, GaloisField 2 f)),
        (∀ i : Fin n, GGSixBstarWit p Bs (ggG0 p B x L D J) .PSp f
          (ψ (A₀ * longBlock (GaloisField 2 f) n i T * A₀⁻¹))) ∧
        ∀ i j : Fin n, i ≠ j → GGSixBstarWit p Bs (ggG0 p B x L D J) .PSp f
          (ψ (A₀ * (longBlock (GaloisField 2 f) n i T * longBlock (GaloisField 2 f) n j T) *
            A₀⁻¹))

open WitClSp CFSG.ClassicalInvolution.Models.SymplecticPairs in
theorem ggSixRootFusionWitnessOn_PSp_of_planeWitness {P : ℕ → ℕ → ℕ → Prop}
    (hin : GGSpPlaneWitnessInputOn P) :
    GGSixRootFusionWitnessOn fun t n f p => t = .PSp ∧ P n f p := by
  intro G _ _ p B Bs x L D J t n f ψ hP hctx s1 _ E r _ _ _ s hs hs2
  obtain ⟨rfl, hPn⟩ := hP
  obtain ⟨hn3, A₀, T, h₁, h₂⟩ := hin G p B Bs x L D J n f ψ hPn hctx s1
  have hn2 : 2 ≤ n := hctx.2.2.2.1.1.2.2.1
  obtain ⟨hrange, hker⟩ := hctx.2.2.2.2.1
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hψ : Function.Injective ψ := by
    rw [injective_iff_map_eq_one]
    intro a ha
    have hz : a ∈ Subgroup.center (StatedSp n (GaloisField 2 f)) := hker ha
    rw [CFSG.LieType.Universal.Symplectic.center_eq,
      CFSG.LieType.SteinbergBR.EvenSp.statedScalars_subgroupOf_statedSp (by omega)] at hz
    exact Subgroup.mem_bot.mp hz
  obtain ⟨ψS, hψS⟩ : ∃ ψS : StatedSp n (GaloisField 2 f) →* G, ∀ a, ψS a = ψ a :=
    ⟨ψ, fun _ => rfl⟩
  have hψS' : Function.Injective ψS := fun a c h => hψ (by rw [← hψS, ← hψS]; exact h)
  have hrangeS : ψS.range = ggG0 p B x L D J := by
    rw [← hrange]
    ext y
    constructor
    · rintro ⟨a, rfl⟩
      exact ⟨a, (hψS a).symm⟩
    · rintro ⟨a, rfl⟩
      exact ⟨a, hψS a⟩
  rw [← hrangeS] at hs
  obtain ⟨w, rfl⟩ := hs
  have hw : w * w = 1 := by
    have h2 := pow_orderOf_eq_one (ψS w)
    rw [hs2, pow_two, ← map_mul] at h2
    exact hψS' (by rw [h2, map_one])
  have hv : (A₀⁻¹ * w * A₀) * (A₀⁻¹ * w * A₀) = 1 := by
    rw [show (A₀⁻¹ * w * A₀) * (A₀⁻¹ * w * A₀) = A₀⁻¹ * (w * w) * A₀ by group, hw, mul_one,
      inv_mul_cancel]
  have hM : ∀ g, ψS g ∈ ggM p B x L D J := fun g =>
    Subgroup.le_normalizer (hrangeS ▸ ⟨g, rfl⟩)
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 + 1 + 1 := ⟨n - 3, by omega⟩
  have h01 : (0 : Fin (m + 1 + 1 + 1)) ≠ 1 := by simp
  obtain ⟨g, ⟨hc₁, hc₂⟩ | ⟨hc₁, hc₂, hc₃, hc₄⟩⟩ := exists_conj_fix_or_swap _ hv
  · obtain ⟨hcomm, hconj⟩ := conj_frame_witness ψS (commute_longBlock_of_fix hc₁ hc₂ T)
    refine Or.inr (Or.inl ⟨_, hcomm, ψS (A₀ * g * A₀⁻¹), hM _, ?_⟩)
    rw [hconj, hψS]
    exact (h₁ 0).fusionWitness
  · obtain ⟨hcomm, hconj⟩ := conj_frame_witness ψS
      (commute_longBlock_two_of_swap h01 hc₁ hc₂ hc₃ hc₄ T)
    refine Or.inr (Or.inl ⟨_, hcomm, ψS (A₀ * g * A₀⁻¹), hM _, ?_⟩)
    rw [hconj, hψS]
    exact (h₂ 0 1 h01).fusionWitness

theorem ggSixRootFusionWitnessOn_PSpNonsplit_of_plane
    (hpl : GGSpPlaneWitnessInputOn fun _ f p => p ∣ 2 ^ f + 1)
    (hrest : GGSixRootFusionWitnessOn fun t _ f p =>
      t = .PSp ∧ ¬ p ∣ 2 ^ f - 1 ∧ ¬ p ∣ 2 ^ f + 1) :
    GGSixRootFusionWitnessOn GGPSpNonsplit := by
  intro G _ _ p B Bs x L D J t n f ψ hP
  by_cases hq : p ∣ 2 ^ f + 1
  · exact ggSixRootFusionWitnessOn_PSp_of_planeWitness hpl G p B Bs x L D J t n f ψ ⟨hP.1, hq⟩
  · exact hrest G p B Bs x L D J t n f ψ ⟨hP.1, hP.2, hq⟩

open WitSp WitClSp CFSG.ClassicalInvolution.Models.SymplecticPairs
  CFSG.SeitzReduction.SymplecticPilot in
theorem ggSpPlaneWitnessInputOn_split : GGSpPlaneWitnessInputOn fun _ f p => p ∣ 2 ^ f - 1 := by
  intro G _ _ p B Bs x L D J n f ψ hpq hctx s1
  obtain ⟨A₀, φ₀, hφ₀a, hφinj, hφrange, hframe₀, hn4, h4, hpF, hp, hBs, ζu, hζu1, hζup⟩ :=
    exists_spSplit_frame hctx s1 hpq
  have hT : ∀ i : Fin n, longBlock (GaloisField 2 f) n i (mkSL _ (det_diag_units ζu)) =
      diagSp (GaloisField 2 f) n (Pi.mulSingle i ζu) := fun i => by
    rw [← rootTorusHom_eq_longBlock, rootTorusHom_apply]
  refine ⟨by omega, A₀, mkSL _ (det_diag_units ζu), fun i => ?_, fun i j hij => ?_⟩
  · obtain ⟨k₀, hk₀⟩ := SLRep.exists_ne_fin (by omega : 2 ≤ n) i
    obtain ⟨heB, he1, L₂, hL₂, hcard⟩ := witness_of_diag h4 hp hpF hBs hφinj hφrange hframe₀
      (s := Pi.mulSingle i ζu) (mulSingle_pow_eq_one hζup i) (j₁ := i) (j₂ := i)
      (by rw [Pi.mulSingle_eq_same]; exact hζu1)
      (fun k hk _ => by rw [Pi.mulSingle_eq_of_ne hk]) (k₀ := k₀) hk₀ hk₀
    rw [hT, ← hφ₀a]
    exact ⟨heB, he1, L₂, hL₂, Or.inl hcard⟩
  · obtain ⟨k₀, hk₀⟩ : ∃ k₀ : Fin n, k₀ ∉ ({i, j} : Finset (Fin n)) := by
      by_contra hall
      simp only [not_exists, not_not] at hall
      have h := Finset.card_le_card (fun k _ => hall k : (Finset.univ : Finset (Fin n)) ⊆ _)
      rw [Finset.card_univ, Fintype.card_fin] at h
      have h2 := Finset.card_le_two (a := i) (b := j)
      omega
    have hk₀1 : k₀ ≠ i := fun h => hk₀ (by simp [h])
    have hk₀2 : k₀ ≠ j := fun h => hk₀ (by simp [h])
    obtain ⟨heB, he1, L₂, hL₂, hcard⟩ := witness_of_diag h4 hp hpF hBs hφinj hφrange hframe₀
      (s := Pi.mulSingle i ζu * Pi.mulSingle j ζu)
      (fun k => by rw [Pi.mul_apply, mul_pow, mulSingle_pow_eq_one hζup i k,
        mulSingle_pow_eq_one hζup j k, one_mul]) (j₁ := i) (j₂ := j)
      (by rw [Pi.mul_apply, Pi.mulSingle_eq_same, Pi.mulSingle_eq_of_ne hij, mul_one]
          exact hζu1)
      (fun k hk₁ hk₂ => by rw [Pi.mul_apply, Pi.mulSingle_eq_of_ne hk₁,
        Pi.mulSingle_eq_of_ne hk₂, mul_one]) (k₀ := k₀) hk₀1 hk₀2
    rw [hT, hT, ← map_mul, ← hφ₀a]
    exact ⟨heB, he1, L₂, hL₂, Or.inl hcard⟩

end Inputs

end CFSG.StandardType
