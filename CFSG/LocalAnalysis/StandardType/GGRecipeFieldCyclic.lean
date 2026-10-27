module

public import CFSG.LocalAnalysis.StandardType.GGRecipeFieldDefs
public import CFSG.LocalAnalysis.StandardType.GGFieldCaseL46J

public section

namespace CFSG.StandardType

open CFSG.Assembly

theorem exists_le_zpowers_sup_of_cyclic {G M : Type*} [Group G] [Group M] {U U₁ : Subgroup G}
    (ρ : U →* M) {J S : Subgroup M} (hN : (J.subgroupOf S).Normal)
    (hcyc : ∃ g ∈ S, ∀ s ∈ S, ∃ k : ℤ, g ^ k * s ∈ J) (hρS : ∀ u, ρ u ∈ S)
    (hmem : ∀ u : U, (u : G) ∈ U₁ ↔ ρ u ∈ J) :
    ∃ g ∈ U, U ≤ Subgroup.zpowers g ⊔ U₁ := by
  obtain ⟨g₀, hg₀, hgen⟩ := hcyc
  have := hN
  have hQ : IsCyclic (S ⧸ J.subgroupOf S) := by
    refine ⟨⟨(QuotientGroup.mk (⟨g₀, hg₀⟩ : S) : S ⧸ J.subgroupOf S), fun x => ?_⟩⟩
    induction x using QuotientGroup.induction_on with
    | H s =>
      obtain ⟨k, hk⟩ := hgen s s.2
      have h1 : (QuotientGroup.mk ((⟨g₀, hg₀⟩ : S) ^ k * s) : S ⧸ J.subgroupOf S) = 1 := by
        rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
        simpa using hk
      rw [QuotientGroup.mk_mul, QuotientGroup.mk_zpow] at h1
      refine ⟨-k, ?_⟩
      change (QuotientGroup.mk (⟨g₀, hg₀⟩ : S) : S ⧸ J.subgroupOf S) ^ (-k) = _
      rw [zpow_neg]
      exact inv_eq_of_mul_eq_one_right h1
  let ρ' : U →* S := ρ.codRestrict S hρS
  let ψ : U →* S ⧸ J.subgroupOf S := (QuotientGroup.mk' (J.subgroupOf S)).comp ρ'
  have : IsCyclic ψ.range := Subgroup.isCyclic _
  obtain ⟨⟨_, g, rfl⟩, hg⟩ := IsCyclic.exists_generator (α := ψ.range)
  refine ⟨g, g.2, fun u hu => ?_⟩
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hg ⟨ψ ⟨u, hu⟩, ⟨u, hu⟩, rfl⟩)
  have hk' : ψ (g ^ k) = ψ ⟨u, hu⟩ := by
    rw [map_zpow]
    exact congrArg Subtype.val hk
  have h1 : ψ (⟨u, hu⟩ * (g ^ k)⁻¹) = 1 := by rw [map_mul, map_inv, hk', mul_inv_cancel]
  have h2 : ρ (⟨u, hu⟩ * (g ^ k)⁻¹) ∈ J := by
    have h : (ρ' (⟨u, hu⟩ * (g ^ k)⁻¹) : S ⧸ J.subgroupOf S) = 1 := h1
    rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at h
    exact h
  have h3 := (hmem _).mpr h2
  have e : u = (u * ((g : G) ^ k)⁻¹) * (g : G) ^ k := by group
  rw [e]
  refine Subgroup.mul_mem _ (Subgroup.mem_sup_right ?_)
    (Subgroup.mem_sup_left (Subgroup.zpow_mem_zpowers _ _))
  simpa using h3

@[expose] def GGRawPCyclic (p : ℕ) : LargeEvenRawCont :=
  fun R _ I _ => IsSimpleGroup R → (∃ a b : R, a * b ≠ b * a) →
    ∃ J S : Subgroup (MulAut R), (J : Set (MulAut R)) = I ∧ J ≤ S ∧ (J.subgroupOf S).Normal ∧
      (∃ g ∈ S, ∀ s ∈ S, ∃ k : ℤ, g ^ k * s ∈ J) ∧
      ∀ α : MulAut R, (∃ k : ℕ, α ^ p ^ k = 1) → α ∈ S

@[expose] def GGRawPCyclicOn (S : ℕ → LargeEvenLabel → Prop) : Prop :=
  ∀ p : ℕ, p.Prime → p ≠ 2 → ∀ lab : LargeEvenLabel, LargeEvenInLambda2 lab → S p lab →
    LargeEvenLabelAll lab (GGRawPCyclic p)

theorem GGRawPCyclicOn.mono {S S' : ℕ → LargeEvenLabel → Prop}
    (hS : ∀ p lab, S' p lab → S p lab) (h : GGRawPCyclicOn S) : GGRawPCyclicOn S' :=
  fun p hp hp2 lab hlab hS' => h p hp hp2 lab hlab (hS p lab hS')

theorem GGRawPCyclicOn.or {S S' : ℕ → LargeEvenLabel → Prop} (h : GGRawPCyclicOn S)
    (h' : GGRawPCyclicOn S') : GGRawPCyclicOn fun p lab => S p lab ∨ S' p lab := by
  rintro p hp hp2 lab hlab (hS | hS)
  · exact h p hp hp2 lab hlab hS
  · exact h' p hp hp2 lab hlab hS

@[expose] def GGNotD4Three (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  ¬ (lab.tag = .D ∧ lab.rank = 4 ∧ p = 3)

@[expose] def GGL46CyclicD4Input : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G)
    (L D J X B₂ : Subgroup G) (d y : G) (K U U₁ : Subgroup G),
    GGFieldCaseSetup p B Bs x L D J X B₂ d y K U U₁ → p = 3 →
    LargeEvenMarking K (fun lab _ _ I _ θ => lab.tag = .D ∧ lab.rank = 4 ∧
      ∀ u ∈ U, u ∈ U₁ ↔ ∃ φ ∈ I, LargeEvenInduces θ (fun k k' => (k' : G) = u⁻¹ * k * u) φ) →
    ∃ g ∈ U, U ≤ Subgroup.zpowers g ⊔ U₁

theorem ggL46CyclicInput_of_raw (h : GGRawPCyclicOn GGNotD4Three) (hD4 : GGL46CyclicD4Input) :
    GGL46CyclicInput := by
  intro G _ _ p B Bs x L D J X B₂ d y K U U₁ hS
  have hcfg := hS.1.1
  have hp : p.Prime := hcfg.1.2.2.2.2.2.1.1
  have hp2 : p ≠ 2 := hcfg.1.2.2.2.2.2.1.2.1
  obtain ⟨-, hUp, -, -⟩ := hS.2.2.2.2.2.2.1
  obtain ⟨hUN, -, hmk⟩ := hS.2.2.2.2.2.2.2.1
  obtain ⟨hK, lab, hlab, hraw⟩ := hmk
  by_cases hD : lab.tag = .D ∧ lab.rank = 4 ∧ p = 3
  · obtain ⟨ht, hr, hp3⟩ := hD
    refine hD4 G p B Bs x L D J X B₂ d y K U U₁ hS hp3 ⟨hK, lab, hlab, ?_⟩
    refine largeEvenRawDatum_mono ?_ hraw
    rintro R _ I F ⟨hs, hna, θ, hθ⟩
    exact ⟨hs, hna, θ, ht, hr, hθ⟩
  · have hraw' := h p hp hp2 lab hlab hD _ hraw
    obtain ⟨R, _, I, F, ⟨hs, hna, θ, hθ⟩, hcyc⟩ := largeEvenRawDatum_exists hraw'
    obtain ⟨J', S, hJ', -, hN, hgen, hpS⟩ := hcyc hs hna
    let ρ : U →* MulAut R := (ggLAut K θ).comp (Subgroup.inclusion hUN)
    have hρ : ∀ u : U, ρ u = ggLAut K θ ⟨u, hUN u.2⟩ := fun _ => rfl
    have hρS : ∀ u : U, ρ u ∈ S := fun u => by
      obtain ⟨k, hk⟩ := hUp u
      exact hpS _ ⟨k, by rw [← map_pow, hk, map_one]⟩
    refine exists_le_zpowers_sup_of_cyclic ρ hN hgen hρS (fun u => ?_)
    · rw [hθ u u.2, hρ]
      constructor
      · rintro ⟨φ, hφ, hind⟩
        rw [eq_ggLAut_of_induces K θ (hUN u.2) hind, ← hJ'] at hφ
        have := J'.inv_mem hφ
        rw [← map_inv] at this
        convert this using 2
        exact Subtype.ext (by simp)
      · intro hmem
        refine ⟨ggLAut K θ ⟨(u : G)⁻¹, inv_mem (hUN u.2)⟩, ?_,
          largeEvenInduces_ggLAut_inv K θ (inv_mem (hUN u.2))⟩
        rw [← hJ']
        have := J'.inv_mem hmem
        rw [← map_inv] at this
        convert this using 2

end CFSG.StandardType

end
