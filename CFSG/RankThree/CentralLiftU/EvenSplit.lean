module

public import CFSG.RankThree.CentralLiftU.UnitaryThreeEven
public import CFSG.RankThree.CentralLiftU.EvenTorus
public import CFSG.LocalAnalysis.SectionRank.EvenCover.Unitary
public import CFSG.ClassicalGroups.UnitaryFlag.ModelTransport
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate117

public section

namespace CFSG.RankThree.CentralLiftU

open CFSG.LieType.Steinberg CFSG.LieType.CentralExt CFSG.LieType.BorelTits
  CFSG.LieType.Universal.Unitary CFSG.LocalAnalysis.ComponentInitial
  CFSG.ClassicalGroups.UnitaryFlag
open CFSG.Assembly.LowTwoRank (StatedSU)

section Split

variable {f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K) [Finite K]
  [Fact (Nat.Prime 2)] [CharP K 2]

local notation "σ₀" => unitaryInvolution K 2 f

include h in
theorem nonempty_SU_three_mulEquiv_statedSU :
    Nonempty (SU σ₀ 3 ≃* StatedSU 3 (2 ^ f) K) := by
  have hK := card_eq_sq_of_unitaryFieldData h
  obtain ⟨P, hP⟩ := exists_wittMatrix hK 3
  exact ⟨(conjEquiv P hP).trans (MulEquiv.subgroupCongr (SUid_eq_statedSU hK 3))⟩

include h in
theorem exists_lift_SU_three_two {p : ℕ} (hp : p.Prime) (hp3 : 3 < p) {E G : Type*} [Group E]
    [Group G] [Finite E] {π : E →* G} (hπ : Function.Surjective π)
    (hcen : π.ker ≤ Subgroup.center E) (hpk : IsPGroup p π.ker) (α : SU σ₀ 3 →* G) :
    ∃ β : SU σ₀ 3 →* E, π.comp β = α := by
  obtain ⟨e⟩ := nonempty_SU_three_mulEquiv_statedSU h (f := f)
  have hsplit := (statedSU_three_even_lift_facts.{_, 0, 0} h hp hp3).1
  have : Finite (StatedSU 3 (2 ^ f) K) := inferInstance
  have : Finite (SU σ₀ 3) := Finite.of_equiv _ e.symm.toEquiv
  exact exists_lift_of_forall_section_prime (fun R _ _ ρ hρ hcen' hpk' =>
    forall_section_of_mulEquiv e (fun ρ' hρ' hcen'' hp'' => hsplit R ρ' hρ' hcen'' hp'')
      ρ hρ hcen' hpk') hπ hcen hpk α

theorem exists_rankOne_section_SU_odd_two {p : ℕ} (hp : p.Prime) (hp3 : 3 < p) {n : ℕ}
    (hn : 3 ≤ n) (ho : ¬Even n) {E : Type*} [Group E] [Finite E] {π : E →* SU σ₀ n}
    (hπ : Function.Surjective π) (hcen : π.ker ≤ Subgroup.center E) (hpk : IsPGroup p π.ker)
    (k : Fin (n / 2)) :
    ∃ φ : ↥(CFSG.LieType.CurtisTits.rankOne (rootGroup σ₀
      (unitaryInvolution_involutive (card_eq_sq_of_unitaryFieldData h)) n) k) →* E,
      ∀ g, π (φ g) = g := by
  have hF := card_eq_sq_of_unitaryFieldData h
  have hC := CFSG.SectionRank.EvenCover.not_two_dvd_of_odd (Gen.odd_card_ker hp hp3 hpk)
  by_cases hk : k.val + 1 < n / 2
  · set e := rankOneShortEquiv (hσ := unitaryInvolution_involutive hF) hk
    obtain ⟨ρ, hρ, -⟩ := CFSG.SectionRank.EvenCover.sl2_existsUnique_lift hπ hcen hC
      ((Subgroup.subtype _).comp e.symm.toMonoidHom)
    refine ⟨ρ.comp e.toMonoidHom, fun g => ?_⟩
    have h1 := DFunLike.congr_fun hρ (e g)
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply,
      Subgroup.coe_subtype] at h1
    exact h1
  · obtain ⟨e⟩ := nonempty_rankOne_last_odd_mulEquiv hF ho hn hk
    obtain ⟨ρ, hρ⟩ := exists_lift_SU_three_two h hp hp3 hπ hcen hpk
      ((Subgroup.subtype _).comp e.symm.toMonoidHom)
    refine ⟨ρ.comp e.toMonoidHom, fun g => ?_⟩
    have h1 := DFunLike.congr_fun hρ (e g)
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply,
      Subgroup.coe_subtype] at h1
    exact h1

include h in
theorem su_odd_central_large_prime_extension_splitting_two {p : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    {n : ℕ} (hn : 3 ≤ n) (ho : ¬Even n) {E : Type*} [Group E] [Finite E] {π : E →* SU σ₀ n}
    (hπ : Function.Surjective π) (hcen : π.ker ≤ Subgroup.center E) (hpk : IsPGroup p π.ker) :
    ∃ s : SU σ₀ n →* E, (∀ x, π (s x) = x) ∧ (∀ τ : SU σ₀ n →* E, (∀ x, π (τ x) = x) → τ = s) ∧
      ∃ e : π.ker × s.range ≃* E, ∀ a, e a = (a.1 : E) * a.2 := by
  have hF := card_eq_sq_of_unitaryFieldData h
  obtain ⟨ζ, hζ⟩ := exists_traceZero_ne_zero hF
  have hC := CFSG.SectionRank.EvenCover.not_two_dvd_of_odd (Gen.odd_card_ker hp hp3 hpk)
  have : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  exact exists_section_mulEquiv_of_existsUnique hcen (existsUnique_section_of_rankOne_lift
    (D := rootDatum hF n) (isCTGroupDatum hF n (by omega) ζ hζ)
    (steinbergExtras hF n (by omega) ζ hζ)
    (fun γ hγ => isPGroup_rootGroup (unitaryInvolution_involutive hF)
      (SUExtras.toStd_ne_zero_of_mem_roots hγ)) hπ hcen hC
    (exists_rankOne_section_SU_odd_two h hp hp3 hn ho hπ hcen hpk))

end Split

theorem nonempty_hypSU_mulEquiv_SU {f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K)
    [Finite K] [Fact (Nat.Prime 2)] [CharP K 2] (r : ℕ) :
    Nonempty (hypSU h r 1 ≃* SU (unitaryInvolution K 2 f) (2 * r + 1)) := by
  have hF := card_eq_sq_of_unitaryFieldData h
  obtain ⟨R0, hR0⟩ := exists_isHypTransport h (r := r) (ε := 1)
  obtain ⟨P, hP⟩ := exists_wittMatrix hF (2 * r + 1)
  exact ⟨((hypTransport h hR0).trans
    (MulEquiv.subgroupCongr (SUid_eq_statedSU hF (2 * r + 1)).symm)).trans (conjEquiv P hP).symm⟩

theorem odd_dimensional_even_unitary_central_large_prime_extension_splitting {f : ℕ} {K : Type}
    [Field K] (h : UnitaryFieldData 2 f K) {r : ℕ} (hr : 2 ≤ r) {E : Type*} [Group E] [Finite E]
    (π : E →* hypSU h r 1) (hπ : Function.Surjective π) (hcen : π.ker ≤ Subgroup.center E)
    {p : ℕ} (hp : p.Prime) (hp3 : 3 < p) (hpk : IsPGroup p π.ker) :
    ∃ s : hypSU h r 1 →* E, (∀ x, π (s x) = x) ∧
      (∀ t : hypSU h r 1 →* E, (∀ x, π (t x) = x) → t = s) ∧
      ∃ e : π.ker × s.range ≃* E, ∀ a, e a = (a.1 : E) * a.2 := by
  have := h.finite
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := h.charP
  obtain ⟨Φ⟩ := nonempty_hypSU_mulEquiv_SU h r
  have hker : (Φ.toMonoidHom.comp π).ker = π.ker := by
    ext x
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      map_eq_one_iff _ Φ.injective]
  have ho : ¬Even (2 * r + 1) := fun he => by
    obtain ⟨m, hm⟩ := he
    omega
  obtain ⟨s, hs, huniq, -⟩ := su_odd_central_large_prime_extension_splitting_two h hp hp3
    (n := 2 * r + 1) (by omega) ho (π := Φ.toMonoidHom.comp π) (Φ.surjective.comp hπ)
    (hker ▸ hcen) (hker ▸ hpk)
  have hs' : ∀ x, π (s.comp Φ.toMonoidHom x) = x := fun x => Φ.injective (hs (Φ x))
  refine exists_section_mulEquiv_of_existsUnique hcen ⟨s.comp Φ.toMonoidHom, hs',
    fun t ht => ?_⟩
  have h1 := huniq (t.comp Φ.symm.toMonoidHom) (fun x => by
    change Φ (π (t (Φ.symm x))) = x
    rw [ht, MulEquiv.apply_symm_apply])
  ext x
  have := DFunLike.congr_fun h1 (Φ x)
  simpa using this

end CFSG.RankThree.CentralLiftU
