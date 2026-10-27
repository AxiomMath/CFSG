module

public import CFSG.LocalAnalysis.SectionRank.EvenCover.CoverMap

public section

namespace CFSG.ShultStronglyClosedTI.PerfectOddCover

open CFSG.SectionRank.EvenCover

universe u v w

variable {S : Type u} {P : Type w} {L : Type v} [Group S] [Group P] [Group L]

theorem lift_surjective_ker [Group.IsPerfect L] {π : S →* P} (hπ : Function.Surjective π)
    {η : L →* P} (hcen : η.ker ≤ Subgroup.center L) {φ : S →* L} (hφ : η.comp φ = π) :
    Function.Surjective φ ∧ φ.ker ≤ π.ker ∧ π.ker.map φ = η.ker := by
  have hφ' : ∀ s, η (φ s) = π s := fun s => DFunLike.congr_fun hφ s
  have hsurj : Function.Surjective φ := by
    rw [← MonoidHom.range_eq_top]
    refine eq_top_of_forall_mul_center fun x => ?_
    obtain ⟨s, hs⟩ := hπ (η x)
    refine ⟨φ s, ⟨s, rfl⟩, hcen ?_⟩
    rw [MonoidHom.mem_ker, map_mul, map_inv, hφ', hs, inv_mul_cancel]
  refine ⟨hsurj, fun s hs => ?_, ?_⟩
  · rw [MonoidHom.mem_ker] at hs ⊢
    rw [← hφ', hs, map_one]
  · ext c
    constructor
    · rintro ⟨s, hs, rfl⟩
      rw [MonoidHom.mem_ker, hφ']
      exact hs
    · intro hc
      obtain ⟨s, rfl⟩ := hsurj c
      refine ⟨s, ?_, rfl⟩
      change π s = 1
      rw [← hφ']
      exact hc

theorem existsUnique_lift [Finite S] [Finite L]
    (hsplit : ∀ (E : Type (max u v)) [Group E] [Finite E] (ρ : E →* S),
      Function.Surjective ρ → ρ.ker ≤ Subgroup.center E → Odd (Nat.card ρ.ker) →
        ∃! σ : S →* E, ∀ s, ρ (σ s) = s)
    (π : S →* P) {η : L →* P} (hη : Function.Surjective η) (hcen : η.ker ≤ Subgroup.center L)
    (hodd : Odd (Nat.card η.ker)) :
    ∃! φ : S →* L, η.comp φ = π := by
  obtain ⟨σ, hσ, huniq⟩ := hsplit (pullback η π) (pullbackFst η π)
    (pullbackFst_surjective hη π) (pullbackFst_ker_le_center hcen π)
    (Odd.of_dvd_nat hodd (card_pullbackFst_ker_dvd η π))
  refine ⟨(MonoidHom.snd S L).comp ((pullback η π).subtype.comp σ), comp_snd_section σ hσ, ?_⟩
  intro ψ hψ
  let τ : S →* pullback η π :=
    { toFun := fun s => ⟨(s, ψ s), (DFunLike.congr_fun hψ s).symm⟩
      map_one' := Subtype.ext (Prod.ext rfl (map_one ψ))
      map_mul' := fun a b => Subtype.ext (Prod.ext rfl (map_mul ψ a b)) }
  have hτ : τ = σ := huniq τ fun _ => rfl
  ext s
  change ((τ s : pullback η π) : S × L).2 = _
  rw [hτ]
  rfl

theorem map_isCyclic_card_dvd (φ : S →* L) (Z : Subgroup S) [IsCyclic Z] {d : ℕ}
    (hZ : Nat.card Z ∣ d) :
    IsCyclic (Z.map φ) ∧ Nat.card (Z.map φ) = φ.ker.relIndex Z ∧ Nat.card (Z.map φ) ∣ d := by
  have hcard : Nat.card (Z.map φ) = φ.ker.relIndex Z := (Subgroup.relIndex_ker Z φ).symm
  exact ⟨isCyclic_of_surjective (φ.subgroupMap Z) (φ.subgroupMap_surjective Z), hcard,
    hcard ▸ (Subgroup.relIndex_dvd_card _ _).trans hZ⟩

theorem perfect_odd_cover_of_split [Finite S] [Finite L] [Group.IsPerfect L]
    (hsplit : ∀ (E : Type (max u v)) [Group E] [Finite E] (ρ : E →* S),
      Function.Surjective ρ → ρ.ker ≤ Subgroup.center E → Odd (Nat.card ρ.ker) →
        ∃! σ : S →* E, ∀ s, ρ (σ s) = s)
    {π : S →* P} (hπ : Function.Surjective π) [IsCyclic π.ker] {d : ℕ}
    (hZ : Nat.card π.ker ∣ d) {η : L →* P} (hη : Function.Surjective η)
    (hcen : η.ker ≤ Subgroup.center L) (hodd : Odd (Nat.card η.ker)) :
    ∃ φ : S →* L, η.comp φ = π ∧ (∀ ψ : S →* L, η.comp ψ = π → ψ = φ) ∧
      Function.Surjective φ ∧ φ.ker ≤ π.ker ∧ π.ker.map φ = η.ker ∧
      (∃ e : S ⧸ φ.ker ≃* L, ∀ s, e (QuotientGroup.mk s) = φ s ∧
        η (e (QuotientGroup.mk s)) = π s) ∧
      IsCyclic η.ker ∧ Nat.card η.ker = φ.ker.relIndex π.ker ∧ Nat.card η.ker ∣ d := by
  obtain ⟨φ, hφ, huniq⟩ := existsUnique_lift hsplit π hη hcen hodd
  obtain ⟨hsurj, hker, hmap⟩ := lift_surjective_ker hπ hcen hφ
  obtain ⟨hcyc, hcard, hdvd⟩ := map_isCyclic_card_dvd φ π.ker hZ
  rw [hmap] at hcyc hcard hdvd
  exact ⟨φ, hφ, huniq, hsurj, hker, hmap, ⟨QuotientGroup.quotientKerEquivOfSurjective φ hsurj,
    fun s => ⟨rfl, DFunLike.congr_fun hφ s⟩⟩, hcyc, hcard, hdvd⟩

end CFSG.ShultStronglyClosedTI.PerfectOddCover
