module

public import CFSG.LocalAnalysis.StandardType.GGFrameRoutePortRankLift

public section

namespace CFSG.StandardType.FrameRoute

open scoped commutatorElement

@[expose] def Rank3SymGens (M : Type*) [Group M] (r : ℕ) : Prop :=
  ∃ e : Fin r → M, (∀ i, e i ^ 3 = 1) ∧ (∀ i j, Commute (e i) (e j)) ∧
    Nat.card (Subgroup.closure (Set.range e)) = 3 ^ r ∧
    Subgroup.closure (Set.range e) ⊓ Subgroup.center M = ⊥ ∧
    (∃ t : M, (∃ k : ℕ, t ^ 2 ^ k = 1) ∧ t ∉ Subgroup.center M ∧ ∀ i, Commute t (e i)) ∧
    (∀ i, ∃ s : M, (∃ k : ℕ, s ^ 2 ^ k = 1) ∧ s * e i * s⁻¹ = (e i)⁻¹) ∧
    ∀ i j, i ≠ j → ∃ s : M, (∃ k : ℕ, s ^ 2 ^ k = 1) ∧
      ((s * e i * s⁻¹ = e i ∧ s * e j * s⁻¹ = (e j)⁻¹) ∨
        (s * e i * s⁻¹ = (e i)⁻¹ ∧ s * e j * s⁻¹ = e j))

theorem Rank3SymGens.of_mulEquiv {M M' : Type*} [Group M] [Group M'] (φ : M ≃* M') {r : ℕ}
    (h : Rank3SymGens M r) : Rank3SymGens M' r := by
  obtain ⟨e, he3, hcomm, hcard, hZ, ⟨t, ht2, htZ, ht⟩, hinv, hpair⟩ := h
  have hmap : Subgroup.closure (Set.range fun i => φ (e i)) =
      (Subgroup.closure (Set.range e)).map (φ : M →* M') := by
    rw [MonoidHom.map_closure, Set.range_comp']
    rfl
  refine ⟨fun i => φ (e i), ?_, ?_, ?_, ?_, ⟨φ t, ?_, ?_, ?_⟩, ?_, ?_⟩
  · intro i
    rw [← map_pow, he3 i, map_one]
  · intro i j
    exact (hcomm i j).map φ
  · rw [hmap, Subgroup.card_map_of_injective φ.injective, hcard]
  · rw [hmap, ← Subgroup.map_center_eq φ,
      ← Subgroup.map_inf (H := Subgroup.closure (Set.range e)) (K := Subgroup.center M)
        (f := (φ : M →* M')) φ.injective, hZ]
    simp
  · obtain ⟨k, hk⟩ := ht2
    exact ⟨k, by rw [← map_pow, hk, map_one]⟩
  · intro htc
    obtain ⟨z, hz, hzφ⟩ :=
      Subgroup.mem_map.mp (by rw [Subgroup.map_center_eq φ]; exact htc)
    rw [φ.injective hzφ] at hz
    exact htZ hz
  · intro i
    exact (ht i).map φ
  · intro i
    obtain ⟨s, hs2, hs⟩ := hinv i
    refine ⟨φ s, ?_, ?_⟩
    · obtain ⟨k, hk⟩ := hs2
      exact ⟨k, by rw [← map_pow, hk, map_one]⟩
    · simpa only [map_mul, map_inv] using congrArg φ hs
  · intro i j hij
    obtain ⟨s, hs2, hcase⟩ := hpair i j hij
    refine ⟨φ s, ?_, ?_⟩
    · obtain ⟨k, hk⟩ := hs2
      exact ⟨k, by rw [← map_pow, hk, map_one]⟩
    · rcases hcase with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · left
        exact ⟨by simpa only [map_mul, map_inv] using congrArg φ h1,
          by simpa only [map_mul, map_inv] using congrArg φ h2⟩
      · right
        exact ⟨by simpa only [map_mul, map_inv] using congrArg φ h1,
          by simpa only [map_mul, map_inv] using congrArg φ h2⟩

theorem Rank3Witness.of_rank3SymGens {J M : Type*} [Group J] [Group M] [Finite J] (π : J →* M)
    (hπ : Function.Surjective π) (hker : π.ker ≤ Subgroup.center J) {r : ℕ}
    (h : Rank3SymGens M r) : Rank3Witness J r := by
  obtain ⟨e, he3, hcomm, hcard, hZ, ⟨t, ht2, htZ, ht⟩, hinv, hpair⟩ := h
  exact Rank3Witness.of_surjective (t := t) π hπ hker e he3 hcomm hcard hZ ht2 htZ ht hinv hpair

private theorem centerQuot_commutatorHom_ker {J J₁ : Type*} [Group J] [Group J₁]
    (π : J₁ →* J) (hker : π.ker ≤ Subgroup.center J₁) {n : J₁}
    (hπn : π n ∈ Subgroup.center J) :
    ∃ g : J₁ →* Subgroup.center J₁, (∀ j, (g j : J₁) = ⁅n, j⁆) ∧
      π.ker ≤ g.ker ∧ commutator J₁ ≤ g.ker := by
  have hcent : ∀ j : J₁, ⁅n, j⁆ ∈ Subgroup.center J₁ := by
    intro j
    apply hker
    rw [MonoidHom.mem_ker, map_commutatorElement]
    exact commutatorElement_eq_one_iff_mul_comm.mpr
      ((Subgroup.mem_center_iff.mp hπn (π j)).symm)
  let g : J₁ →* Subgroup.center J₁ :=
    { toFun := fun j => ⟨⁅n, j⁆, hcent j⟩
      map_one' := by ext; simp [commutatorElement_def]
      map_mul' := fun x y => by
        apply Subtype.ext
        have hxy : x * ⁅n, y⁆ * x⁻¹ = ⁅n, y⁆ := by
          rw [Subgroup.mem_center_iff.mp (hcent y) x, mul_assoc, mul_inv_cancel, mul_one]
        show ⁅n, x * y⁆ = ⁅n, x⁆ * ⁅n, y⁆
        rw [commutatorElement_mul_right_eq_mul_conj]
        calc ⁅n, x⁆ * x * ⁅n, y⁆ * x⁻¹ = ⁅n, x⁆ * (x * ⁅n, y⁆ * x⁻¹) := by group
          _ = ⁅n, x⁆ * ⁅n, y⁆ := by rw [hxy] }
  refine ⟨g, ?_, ?_, ?_⟩
  · intro j
    rfl
  · intro k hk
    rw [MonoidHom.mem_ker]
    apply Subtype.ext
    show ⁅n, k⁆ = 1
    rw [commutatorElement_eq_one_iff_mul_comm]
    exact Subgroup.mem_center_iff.mp (hker hk) n
  · rw [commutator_def, Subgroup.commutator_le]
    intro x _ y _
    rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact (Subgroup.center.isMulCommutative (G := J₁)).is_comm.comm (g x) (g y)

private theorem ker_centerQuot_le_center {J : Type*} [Group J] (hperf : commutator J = ⊤)
    {J₁ : Type*} [Group J₁] (π : J₁ →* J) (hπ : Function.Surjective π)
    (hker : π.ker ≤ Subgroup.center J₁) :
    ((QuotientGroup.mk' (Subgroup.center J)).comp π).ker ≤ Subgroup.center J₁ := by
  intro n hn
  have hn1 : ((QuotientGroup.mk' (Subgroup.center J)).comp π) n = 1 := by
    simpa only [MonoidHom.mem_ker] using hn
  have hπn : π n ∈ Subgroup.center J := (QuotientGroup.eq_one_iff _).mp hn1
  obtain ⟨g, hg, hK, hcomm⟩ := centerQuot_commutatorHom_ker π hker hπn
  have hsup : commutator J₁ ⊔ π.ker = ⊤ := by
    have hmap : (commutator J₁).map π = ⊤ := by
      rw [commutator_def, Subgroup.map_commutator, Subgroup.map_top_of_surjective π hπ,
        ← commutator_def, hperf]
    rw [← Subgroup.comap_map_eq, hmap, Subgroup.comap_top]
  have htop : g.ker = ⊤ := eq_top_iff.mpr (hsup ▸ sup_le hcomm hK)
  rw [Subgroup.mem_center_iff]
  intro j
  have hj : g j = 1 := by
    have hmem : j ∈ g.ker := htop ▸ Subgroup.mem_top j
    simpa only [MonoidHom.mem_ker] using hmem
  have h1 : ⁅n, j⁆ = 1 := by
    rw [← hg j]
    simpa using congrArg Subtype.val hj
  exact (commutatorElement_eq_one_iff_mul_comm.mp h1).symm

theorem Rank3Witness.of_cover_centerQuot {J M : Type*} [Group J] [Group M]
    (hperf : commutator J = ⊤) (θ : J ⧸ Subgroup.center J ≃* M) {r : ℕ}
    (h : Rank3SymGens M r) (J₁ : Type*) [Group J₁] [Finite J₁] (π : J₁ →* J)
    (hπ : Function.Surjective π) (hker : π.ker ≤ Subgroup.center J₁) : Rank3Witness J₁ r := by
  let ρ : J₁ →* M :=
    θ.toMonoidHom.comp ((QuotientGroup.mk' (Subgroup.center J)).comp π)
  have hρ : Function.Surjective ρ :=
    θ.surjective.comp ((QuotientGroup.mk'_surjective _).comp hπ)
  have hρker : ρ.ker ≤ Subgroup.center J₁ := by
    intro n hn
    have hn1 : ρ n = 1 := by simpa only [MonoidHom.mem_ker] using hn
    refine ker_centerQuot_le_center hperf π hπ hker ?_
    rw [MonoidHom.mem_ker]
    exact θ.injective (by simpa [ρ] using hn1)
  exact Rank3Witness.of_rank3SymGens ρ hρ hρker h

end CFSG.StandardType.FrameRoute

end
