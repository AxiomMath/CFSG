module

public import CFSG.Permutation.SylowTwoNormalizer.Basic
public import Mathlib.GroupTheory.GroupAction.SubMulAction.OfStabilizer

public section

namespace CFSG.Permutation.SylowTwoNormalizer

open Equiv MulAction Subgroup
open scoped Pointwise

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

@[expose] noncomputable def restrictHom (s : Set Ω) : stabilizer (Perm Ω) s →* Perm s :=
  MulAction.toPermHom (stabilizer (Perm Ω) s) s

theorem restrictHom_apply (s : Set Ω) (g : stabilizer (Perm Ω) s) (x : s) :
    ((restrictHom s g x : s) : Ω) = (g : Perm Ω) x := rfl

@[expose] noncomputable def restr (R : Subgroup (Perm Ω)) (s : Set Ω) : Subgroup (Perm s) :=
  (R.subgroupOf (stabilizer (Perm Ω) s)).map (restrictHom s)

theorem mem_restr {R : Subgroup (Perm Ω)} {s : Set Ω} {τ : Perm s} :
    τ ∈ restr R s ↔ ∃ g : stabilizer (Perm Ω) s, (g : Perm Ω) ∈ R ∧ restrictHom s g = τ := by
  rw [restr, Subgroup.mem_map]
  exact ⟨fun ⟨g, hg, h⟩ => ⟨g, Subgroup.mem_subgroupOf.mp hg, h⟩,
    fun ⟨g, hg, h⟩ => ⟨g, Subgroup.mem_subgroupOf.mpr hg, h⟩⟩

theorem isPGroup_restr {R : Subgroup (Perm Ω)} (hR : IsPGroup 2 R) (s : Set Ω) :
    IsPGroup 2 (restr R s) :=
  (IsPGroup.comap_subtype hR).map (restrictHom s)

theorem eq_one_of_restrictHom_eq_one {s : Set Ω} {g : Perm Ω} (hg : g ∈ stabilizer (Perm Ω) s)
    (hg' : g ∈ stabilizer (Perm Ω) sᶜ) (h1 : restrictHom s ⟨g, hg⟩ = 1)
    (h2 : restrictHom sᶜ ⟨g, hg'⟩ = 1) : g = 1 := by
  ext x
  by_cases hx : x ∈ s
  · have h := congrArg (fun p : Perm s => ((p ⟨x, hx⟩ : s) : Ω)) h1
    simpa [restrictHom_apply] using h
  · have hx' : x ∈ sᶜ := by simpa using hx
    have h := congrArg (fun p : Perm ↥sᶜ => ((p ⟨x, hx'⟩ : ↥sᶜ) : Ω)) h2
    simpa [restrictHom_apply] using h

@[expose] noncomputable def restrOfMem {R : Subgroup (Perm Ω)} {s : Set Ω}
    (hRs : R ≤ stabilizer (Perm Ω) s) (g : R) : restr R s :=
  ⟨restrictHom s ⟨g, hRs g.2⟩, mem_restr.mpr ⟨⟨g, hRs g.2⟩, g.2, rfl⟩⟩

theorem le_stabilizer_compl {R : Subgroup (Perm Ω)} {s : Set Ω}
    (hRs : R ≤ stabilizer (Perm Ω) s) : R ≤ stabilizer (Perm Ω) sᶜ :=
  hRs.trans (le_of_eq (stabilizer_compl (G := Perm Ω) (α := Ω) (s := s)).symm)

@[expose] noncomputable def restrProdHom {R : Subgroup (Perm Ω)} {s : Set Ω}
    (hRs : R ≤ stabilizer (Perm Ω) s) : R →* restr R s × restr R sᶜ where
  toFun g := (restrOfMem hRs g, restrOfMem (le_stabilizer_compl hRs) g)
  map_one' := by
    change (restrOfMem hRs 1, restrOfMem (le_stabilizer_compl hRs) 1) = (1, 1)
    exact Prod.ext (Subtype.ext (map_one (restrictHom s)))
      (Subtype.ext (map_one (restrictHom sᶜ)))
  map_mul' a b := by
    change (restrOfMem hRs (a * b), restrOfMem (le_stabilizer_compl hRs) (a * b)) =
      (restrOfMem hRs a * restrOfMem hRs b,
        restrOfMem (le_stabilizer_compl hRs) a * restrOfMem (le_stabilizer_compl hRs) b)
    refine Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)
    · simp only [restrOfMem, Subgroup.coe_mul]
      rw [← map_mul]
      congr 1
    · simp only [restrOfMem, Subgroup.coe_mul]
      rw [← map_mul]
      congr 1

@[simp] theorem restrProdHom_apply {R : Subgroup (Perm Ω)} {s : Set Ω}
    (hRs : R ≤ stabilizer (Perm Ω) s) (g : R) :
    restrProdHom hRs g = (restrOfMem hRs g, restrOfMem (le_stabilizer_compl hRs) g) := rfl

theorem restrProdHom_injective {R : Subgroup (Perm Ω)} {s : Set Ω}
    (hRs : R ≤ stabilizer (Perm Ω) s) : Function.Injective (restrProdHom hRs) := by
  have hRs' := le_stabilizer_compl hRs
  intro a b hab
  have h1 : restrProdHom hRs (a * b⁻¹) = 1 := by rw [map_mul, map_inv, hab, mul_inv_cancel]
  have h1s : restrictHom s ⟨↑(a * b⁻¹), hRs (a * b⁻¹).2⟩ = 1 := by
    have := congrArg (fun x : restr R s × restr R sᶜ => ((x.1 : restr R s) : Perm s)) h1
    simpa [restrOfMem] using this
  have h2s : restrictHom sᶜ ⟨↑(a * b⁻¹), hRs' (a * b⁻¹).2⟩ = 1 := by
    have := congrArg (fun x : restr R s × restr R sᶜ => ((x.2 : restr R sᶜ) : Perm ↥sᶜ)) h1
    simpa [restrOfMem] using this
  have hg : (↑(a * b⁻¹) : Perm Ω) = 1 :=
    eq_one_of_restrictHom_eq_one (hRs (a * b⁻¹).2) (hRs' (a * b⁻¹).2) h1s h2s
  have h : a * b⁻¹ = 1 := Subtype.ext (by simpa using hg)
  exact mul_inv_eq_one.mp h

theorem card_dvd_card_restr_mul {R : Subgroup (Perm Ω)} {s : Set Ω}
    (hRs : R ≤ stabilizer (Perm Ω) s) :
    Nat.card R ∣ Nat.card (restr R s) * Nat.card (restr R sᶜ) := by
  have h := Subgroup.card_dvd_of_injective (restrProdHom hRs) (restrProdHom_injective hRs)
  rwa [Nat.card_prod] at h

theorem mem_normalizer_subgroupOf {R : Subgroup (Perm Ω)} {s : Set Ω} {σ : Perm Ω}
    (hσ : σ ∈ stabilizer (Perm Ω) s) (hσR : σ ∈ normalizer (R : Set (Perm Ω))) :
    (⟨σ, hσ⟩ : stabilizer (Perm Ω) s) ∈
      normalizer (R.subgroupOf (stabilizer (Perm Ω) s) : Subgroup (stabilizer (Perm Ω) s)) := by
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · intro hh
    refine Subgroup.mem_subgroupOf.mpr ?_
    simpa using (Subgroup.mem_normalizer_iff.mp hσR (↑h : Perm Ω)).mp
      (Subgroup.mem_subgroupOf.mp hh)
  · intro hh
    refine (Subgroup.mem_normalizer_iff.mp hσR (↑h : Perm Ω)).mpr ?_
    simpa using Subgroup.mem_subgroupOf.mp hh

theorem restrictHom_mem_normalizer {R : Subgroup (Perm Ω)} {s : Set Ω} {σ : Perm Ω}
    (hσ : σ ∈ stabilizer (Perm Ω) s) (hσR : σ ∈ normalizer (R : Set (Perm Ω))) :
    restrictHom s ⟨σ, hσ⟩ ∈ normalizer ((restr R s : Subgroup (Perm s)) : Set (Perm s)) := by
  have hmem := mem_normalizer_subgroupOf hσ hσR
  have hle := Subgroup.le_normalizer_map (H := R.subgroupOf (stabilizer (Perm Ω) s)) (restrictHom s)
  exact hle (Subgroup.mem_map.mpr ⟨⟨σ, hσ⟩, hmem, rfl⟩)

theorem odd_orderOf_restrictHom {s : Set Ω} {σ : Perm Ω} (hσ : σ ∈ stabilizer (Perm Ω) s)
    (ho : Odd (orderOf σ)) : Odd (orderOf (restrictHom s ⟨σ, hσ⟩)) := by
  have h1 : orderOf (restrictHom s ⟨σ, hσ⟩) ∣ orderOf (⟨σ, hσ⟩ : stabilizer (Perm Ω) s) :=
    orderOf_map_dvd (restrictHom s) ⟨σ, hσ⟩
  have h2 : orderOf (⟨σ, hσ⟩ : stabilizer (Perm Ω) s) = orderOf σ :=
    (Subgroup.orderOf_coe ⟨σ, hσ⟩).symm
  rw [h2] at h1
  exact Odd.of_dvd_nat ho h1

theorem not_two_dvd_index_restr {R : Subgroup (Perm Ω)} {s : Set Ω} (hR : IsPGroup 2 R)
    (hRs : R ≤ stabilizer (Perm Ω) s)
    (hc : 2 ^ (padicValNat 2 (Nat.card s).factorial + padicValNat 2 (Nat.card ↥sᶜ).factorial) ∣
      Nat.card R) :
    ¬ 2 ∣ (restr R s).index ∧ ¬ 2 ∣ (restr R sᶜ).index := by
  classical
  haveI : Fintype ↥s := Fintype.ofFinite _
  haveI : Fintype ↥sᶜ := Fintype.ofFinite _
  have h1 : Nat.card (restr R s) ∣ 2 ^ padicValNat 2 (Nat.card ↥s).factorial :=
    card_dvd_of_isPGroup (isPGroup_restr hR s)
  have h2 : Nat.card (restr R sᶜ) ∣ 2 ^ padicValNat 2 (Nat.card ↥sᶜ).factorial :=
    card_dvd_of_isPGroup (isPGroup_restr hR sᶜ)
  obtain ⟨i, hi, hie⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h1
  obtain ⟨j, hj, hje⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h2
  have h3 : Nat.card R ∣ Nat.card (restr R s) * Nat.card (restr R sᶜ) :=
    card_dvd_card_restr_mul hRs
  have h4 : 2 ^ (padicValNat 2 (Nat.card ↥s).factorial +
      padicValNat 2 (Nat.card ↥sᶜ).factorial) ∣ 2 ^ i * 2 ^ j := by
    have h := dvd_trans hc h3
    rwa [hie, hje] at h
  have h5 : padicValNat 2 (Nat.card ↥s).factorial +
      padicValNat 2 (Nat.card ↥sᶜ).factorial ≤ i + j := by
    refine (Nat.pow_dvd_pow_iff_le_right (by norm_num : 1 < 2)).mp ?_
    simpa [pow_add] using h4
  have hia : i = padicValNat 2 (Nat.card ↥s).factorial := by omega
  have hjb : j = padicValNat 2 (Nat.card ↥sᶜ).factorial := by omega
  constructor
  · refine not_two_dvd_index_of_dvd_card (isPGroup_restr hR s) ?_
    rw [hie, hia]
  · refine not_two_dvd_index_of_dvd_card (isPGroup_restr hR sᶜ) ?_
    rw [hje, hjb]

theorem exists_not_mem_alternatingGroup_of_not_two_dvd_index {α : Type*} [Fintype α]
    [DecidableEq α] {H : Subgroup (Perm α)} (hH : IsPGroup 2 H) (h2 : 2 ≤ Nat.card α)
    (hi : ¬ 2 ∣ H.index) : ∃ τ ∈ H, τ ∉ alternatingGroup α := by
  by_contra h
  have hHA : H ≤ alternatingGroup α := fun τ hτ => by
    by_contra hτA
    exact h ⟨τ, hτ, hτA⟩
  have hdvd : 2 * Nat.card H ∣ 2 ^ padicValNat 2 (Nat.card α).factorial :=
    two_mul_card_dvd_of_le_alternatingGroup h2 hHA hH
  have heq : Nat.card H = 2 ^ padicValNat 2 (Nat.card α).factorial :=
    card_eq_of_not_two_dvd_index hH hi
  rw [heq] at hdvd
  have hpos : 0 < 2 ^ padicValNat 2 (Nat.card α).factorial := pow_pos (by norm_num) _
  have hle := Nat.le_of_dvd hpos hdvd
  omega

theorem false_of_card_eq_mul {R : Subgroup (Perm Ω)} {s : Set Ω} (hRA : R ≤ alternatingGroup Ω)
    (hR : IsPGroup 2 R) (hRs : R ≤ stabilizer (Perm Ω) s) (h2 : 2 ≤ Nat.card ↥sᶜ)
    (hsyl : ¬ 2 ∣ (restr R sᶜ).index)
    (hcard : Nat.card R = Nat.card (restr R s) * Nat.card (restr R sᶜ)) : False := by
  classical
  haveI : Fintype ↥sᶜ := Fintype.ofFinite _
  obtain ⟨τ, hτ, hτA⟩ :=
    exists_not_mem_alternatingGroup_of_not_two_dvd_index (isPGroup_restr hR sᶜ) h2 hsyl
  have hτsign : Equiv.Perm.sign τ = -1 := by
    rcases Int.units_eq_one_or (Equiv.Perm.sign τ) with h | h
    · exact absurd (Equiv.Perm.mem_alternatingGroup.mpr h) hτA
    · exact h
  have hbij : Function.Bijective (restrProdHom hRs) := by
    refine Function.Injective.bijective_of_nat_card_le (restrProdHom_injective hRs) ?_
    rw [Nat.card_prod, ← hcard]
  obtain ⟨g, hg⟩ := hbij.2 (1, ⟨τ, hτ⟩)
  have hRs' := le_stabilizer_compl hRs
  have hg1 : restrictHom s ⟨(g : Perm Ω), hRs g.2⟩ = 1 := by
    have h := congrArg (fun x : restr R s × restr R sᶜ => ((x.1 : restr R s) : Perm s)) hg
    simpa [restrOfMem] using h
  have hg2 : restrictHom sᶜ ⟨(g : Perm Ω), hRs' g.2⟩ = τ := by
    have h := congrArg (fun x : restr R s × restr R sᶜ => ((x.2 : restr R sᶜ) : Perm ↥sᶜ)) hg
    simpa [restrOfMem] using h
  have hgeq : (g : Perm Ω) = Equiv.Perm.ofSubtype (p := (· ∈ sᶜ)) τ := by
    ext x
    by_cases hx : x ∈ s
    · have hx' : x ∉ sᶜ := by simpa using hx
      rw [Equiv.Perm.ofSubtype_apply_of_not_mem _ hx']
      have h := congrArg (fun p : Perm s => ((p ⟨x, hx⟩ : s) : Ω)) hg1
      simpa [restrictHom_apply] using h
    · have hx' : x ∈ sᶜ := by simpa using hx
      rw [Equiv.Perm.ofSubtype_apply_of_mem _ hx']
      have h := congrArg (fun p : Perm ↥sᶜ => ((p ⟨x, hx'⟩ : ↥sᶜ) : Ω)) hg2
      simpa [restrictHom_apply] using h
  have hsign_g : Equiv.Perm.sign (g : Perm Ω) = 1 := by
    have h := hRA g.2
    rwa [Equiv.Perm.mem_alternatingGroup] at h
  have hsign_eq : Equiv.Perm.sign (g : Perm Ω) = Equiv.Perm.sign τ := by
    rw [hgeq]
    exact Equiv.Perm.sign_ofSubtype τ
  rw [hsign_g] at hsign_eq
  exact absurd (Units.ext_iff.mp (hsign_eq.trans hτsign)) (by norm_num)

theorem false_of_card_eq_mul' {R : Subgroup (Perm Ω)} {s : Set Ω} (hRA : R ≤ alternatingGroup Ω)
    (hR : IsPGroup 2 R) (hRs : R ≤ stabilizer (Perm Ω) s) (h2 : 2 ≤ Nat.card s)
    (hsyl : ¬ 2 ∣ (restr R s).index)
    (hcard : Nat.card R = Nat.card (restr R s) * Nat.card (restr R sᶜ)) : False := by
  refine false_of_card_eq_mul (s := sᶜ) hRA hR (le_stabilizer_compl hRs) ?_ ?_ ?_
  · simpa using h2
  · rw [compl_compl]
    exact hsyl
  · rw [compl_compl, mul_comm]
    exact hcard

theorem restr_le_alternatingGroup {R : Subgroup (Perm Ω)} {s : Set Ω} [DecidablePred (· ∈ s)]
    (hRA : R ≤ alternatingGroup Ω) (hRs : R ≤ stabilizer (Perm Ω) s) (h1 : Nat.card ↥sᶜ ≤ 1) :
    restr R s ≤ alternatingGroup s := by
  classical
  intro τ hτ
  obtain ⟨g, hgR, rfl⟩ := mem_restr.mp hτ
  rw [Equiv.Perm.mem_alternatingGroup]
  have hg_smul : (g : Perm Ω) • s = s := MulAction.mem_stabilizer_iff.mp g.2
  have hgs : ∀ x : Ω, x ∈ s ↔ (g : Perm Ω) x ∈ s := by
    intro x
    constructor
    · intro hx
      have h : (g : Perm Ω) x ∈ (g : Perm Ω) • s := Set.mem_smul_set.mpr ⟨x, hx, rfl⟩
      rwa [hg_smul] at h
    · intro hx
      have h : (g : Perm Ω) x ∈ (g : Perm Ω) • s := by rwa [hg_smul]
      obtain ⟨y, hy, hgy⟩ := Set.mem_smul_set.mp h
      have hyx : y = x := (g : Perm Ω).injective hgy
      rwa [hyx] at hy
  haveI hsub : Subsingleton ↥sᶜ := by
    haveI : Fintype ↥sᶜ := Fintype.ofFinite _
    exact Finite.card_le_one_iff_subsingleton.mp h1
  have hfix : ∀ x : Ω, x ∉ s → (g : Perm Ω) x = x := by
    intro x hx
    have hx' : x ∈ sᶜ := by simpa using hx
    have hgx' : (g : Perm Ω) x ∈ sᶜ := by
      simp only [Set.mem_compl_iff]
      exact fun h => hx ((hgs x).mpr h)
    exact congrArg Subtype.val
      (Subsingleton.elim (⟨(g : Perm Ω) x, hgx'⟩ : ↥sᶜ) ⟨x, hx'⟩)
  have hgeq : (g : Perm Ω) = Equiv.Perm.ofSubtype (p := (· ∈ s)) (restrictHom s g) := by
    ext x
    by_cases hx : x ∈ s
    · rw [Equiv.Perm.ofSubtype_apply_of_mem _ hx, restrictHom_apply]
    · rw [Equiv.Perm.ofSubtype_apply_of_not_mem _ hx]
      exact hfix x hx
  have hsign : Equiv.Perm.sign (g : Perm Ω) = Equiv.Perm.sign (restrictHom s g) := by
    rw [hgeq]
    exact Equiv.Perm.sign_ofSubtype (restrictHom s g)
  have hgA : Equiv.Perm.sign (g : Perm Ω) = 1 := by
    have h := hRA hgR
    rwa [Equiv.Perm.mem_alternatingGroup] at h
  rw [hgA] at hsign
  exact hsign.symm

end CFSG.Permutation.SylowTwoNormalizer
