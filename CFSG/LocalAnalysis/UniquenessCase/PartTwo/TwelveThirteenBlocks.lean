module

public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.TwelveThirteen

open Equiv Equiv.Perm MulAction Subgroup
open scoped Pointwise

variable {Ω : Type} [Fintype Ω] [DecidableEq Ω]

@[expose] def fibreStab {ι : Type} (β : Ω → ι) : Subgroup (Perm Ω) where
  carrier := {g | ∀ x, β (g x) = β x}
  one_mem' := fun _ => rfl
  mul_mem' := fun {a b} ha hb x => by
    change β (a (b x)) = β x
    rw [ha (b x), hb x]
  inv_mem' := fun {g} hg x => by
    simpa using (hg (g⁻¹ x)).symm

theorem le_normalizer_fibreStab {ι : Type} {β : Ω → ι} {Q : Subgroup (Perm Ω)}
    (hQ : ∀ q ∈ Q, ∀ x y, β (q x) = β (q y) ↔ β x = β y) :
    Q ≤ normalizer (fibreStab β : Set (Perm Ω)) := by
  have key : ∀ q ∈ Q, ∀ h ∈ fibreStab β, q * h * q⁻¹ ∈ fibreStab β := by
    intro q hq h hh x
    have := (hQ q hq (h (q⁻¹ x)) (q⁻¹ x)).2 (hh (q⁻¹ x))
    simpa [Perm.mul_apply] using this
  intro q hq
  rw [mem_normalizer_iff]
  intro h
  refine ⟨key q hq h, fun hh => ?_⟩
  have := key q⁻¹ (Q.inv_mem hq) _ hh
  simpa [mul_assoc] using this

theorem exists_blocks {Q : Subgroup (Perm Ω)} (hQ : IsPGroup 2 Q) :
    ∃ β : Ω → Set Ω, (∀ x y, y ∈ β x ↔ β y = β x) ∧ (∀ x, β x ⊆ orbit Q x) ∧
      (∀ x, Nat.card (orbit Q x) < 4 → β x = orbit Q x) ∧
      (∀ x, 4 ≤ Nat.card (orbit Q x) → (β x).ncard = 4) ∧
      ∀ q ∈ Q, ∀ x, β (q x) = q '' β x := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let rep : Ω → Ω := fun x => (Quotient.mk (MulAction.orbitRel Q Ω) x).out
  have rep_mem : ∀ x, rep x ∈ orbit Q x := by
    intro x
    simpa [rep] using MulAction.orbitRel_apply.mp
      (Quotient.mk_out (s := MulAction.orbitRel Q Ω) x)
  have rep_same : ∀ x y, y ∈ orbit Q x → rep y = rep x := by
    intro x y hy
    have hrel : MulAction.orbitRel Q Ω y x := MulAction.orbitRel_apply.mpr hy
    have hs : Quotient.mk (MulAction.orbitRel Q Ω) y
        = Quotient.mk (MulAction.orbitRel Q Ω) x := Quotient.sound hrel
    simpa [rep] using congrArg
      (fun q : Quotient (MulAction.orbitRel Q Ω) => q.out) hs
  have self_mem_orbit_rep : ∀ x, x ∈ orbit Q (rep x) := by
    intro x
    rw [MulAction.orbit_eq_iff.mpr (rep_mem x)]
    exact MulAction.mem_orbit_self x
  have hexists : ∀ z : Ω, ∃ R : Subgroup ↥Q,
      stabilizer Q z ≤ R ∧ (Nat.card (orbit Q z) < 4 → R = ⊤) ∧
        (4 ≤ Nat.card (orbit Q z) → (orbit ↥R z).ncard = 4) := by
    intro z
    by_cases hsmall : Nat.card (orbit Q z) < 4
    · exact ⟨⊤, le_top, fun _ => rfl, fun h => absurd h (not_le.2 hsmall)⟩
    · have h4 : 4 ≤ Nat.card (orbit Q z) := not_lt.1 hsmall
      obtain ⟨k, hk⟩ := (IsPGroup.iff_card (p := 2)).mp
        (IsPGroup.to_subgroup hQ (stabilizer Q z))
      obtain ⟨a, ha⟩ := IsPGroup.card_orbit hQ z
      have ha2 : 2 ≤ a := by
        have h4' : 2 ^ 2 ≤ 2 ^ a := by
          rw [ha] at h4
          norm_num at h4 ⊢
          exact h4
        exact (Nat.pow_le_pow_iff_right (by norm_num : (1 : ℕ) < 2)).mp h4'
      have hcard : Nat.card ↥Q = 2 ^ k * 2 ^ a := by
        have h1 := Subgroup.card_mul_index (H := stabilizer Q z)
        rw [hk, MulAction.index_stabilizer, ← Nat.card_coe_set_eq, ha] at h1
        exact h1.symm
      have hH : Nat.card (stabilizer Q z) ∣ 2 ^ (k + 2) := by
        rw [hk]
        exact pow_dvd_pow 2 (by omega)
      have hL : 2 ^ (k + 2) ∣ Nat.card (⊤ : Subgroup ↥Q) := by
        rw [Subgroup.card_top, hcard, ← pow_add]
        exact pow_dvd_pow 2 (by omega)
      obtain ⟨K, hKcard, hleK, -⟩ :=
        Sylow.exists_subgroup_card_pow_prime_le_le Nat.prime_two
          (n := k + 2) (H := stabilizer Q z) (L := (⊤ : Subgroup ↥Q)) hH hL le_top
      have h1 : (orbit ↥K z).ncard = (stabilizer Q z).relIndex K := by
        rw [← MulAction.index_stabilizer, ← MulAction.stabilizer_subgroupOf]
        rfl
      have hmul := Subgroup.relIndex_mul_card (H := stabilizer Q z) (K := K)
      rw [inf_eq_left.mpr hleK, hk, hKcard, pow_add] at hmul
      norm_num at hmul
      rw [← h1] at hmul
      have hrel : (orbit ↥K z).ncard = 4 :=
        Nat.mul_right_cancel (pow_pos (by norm_num) k) (hmul.trans (mul_comm _ _))
      exact ⟨K, hleK, fun h => absurd h hsmall, fun _ => hrel⟩
  choose R hR using hexists
  let B : Ω → Set Ω := fun z => orbit ↥(R z) z
  let β : Ω → Set Ω := fun x =>
    {y | ∃ q : ↥Q, q • rep x = x ∧ q⁻¹ • y ∈ B (rep x)}
  have smul_B : ∀ (z : Ω) (g : ↥(R z)), g • B z = B z := by
    intro z g
    simp only [B]
    exact MulAction.smul_orbit g z
  have smul_B_mem : ∀ (z : Ω) (g : ↥(R z)) (w : Ω), g • w ∈ B z ↔ w ∈ B z := by
    intro z g w
    constructor
    · intro h
      rw [← smul_B z g] at h
      rwa [Set.smul_mem_smul_set_iff] at h
    · intro h
      have h' := Set.smul_mem_smul_set (a := g) h
      rwa [smul_B z g] at h'
  have key : ∀ (x : Ω) (q : ↥Q), q • rep x = x →
      β x = (fun y => q • y) '' B (rep x) := by
    intro x q hq
    ext y
    constructor
    · rintro ⟨q', hq', hy'⟩
      have hstab : q⁻¹ * q' ∈ stabilizer Q (rep x) := by
        rw [MulAction.mem_stabilizer_iff]
        calc (q⁻¹ * q') • rep x = q⁻¹ • (q' • rep x) := by rw [mul_smul]
          _ = q⁻¹ • x := by rw [hq']
          _ = q⁻¹ • (q • rep x) := by rw [hq]
          _ = rep x := by rw [inv_smul_smul]
      have hRmem : q⁻¹ * q' ∈ R (rep x) := (hR (rep x)).1 hstab
      have hmem : (q⁻¹ * q') • (q'⁻¹ • y) ∈ B (rep x) := by
        have h' := Set.smul_mem_smul_set
          (a := (⟨q⁻¹ * q', hRmem⟩ : ↥(R (rep x)))) hy'
        rwa [smul_B (rep x) (⟨q⁻¹ * q', hRmem⟩ : ↥(R (rep x)))] at h'
      have hcomp : (q⁻¹ * q') • (q'⁻¹ • y) = q⁻¹ • y := by
        rw [mul_smul, smul_inv_smul]
      refine ⟨(q⁻¹ * q') • (q'⁻¹ • y), hmem, ?_⟩
      simp only [hcomp, smul_inv_smul]
    · rintro ⟨v, hv, rfl⟩
      exact ⟨q, hq, by rw [inv_smul_smul]; exact hv⟩
  have mem_image_key : ∀ (x : Ω) (q : ↥Q), q • rep x = x → ∀ y,
      y ∈ β x ↔ q⁻¹ • y ∈ B (rep x) := by
    intro x q hq y
    rw [key x q hq, Set.mem_image]
    constructor
    · rintro ⟨v, hv, hvy⟩
      rw [← hvy, inv_smul_smul]
      exact hv
    · intro hv
      exact ⟨q⁻¹ • y, hv, by rw [smul_inv_smul]⟩
  have mem_self : ∀ x, x ∈ β x := by
    intro x
    obtain ⟨q, hq⟩ := MulAction.mem_orbit_iff.mp (self_mem_orbit_rep x)
    refine ⟨q, hq, ?_⟩
    have hx : q⁻¹ • x = rep x := by
      calc q⁻¹ • x = q⁻¹ • (q • rep x) := by rw [hq]
        _ = rep x := by rw [inv_smul_smul]
    rw [hx]
    simp only [B]
    exact MulAction.mem_orbit_self (rep x)
  have hsub : ∀ x, β x ⊆ orbit Q x := by
    intro x y hy
    rcases hy with ⟨q, hq, hqy⟩
    have hBsub : B (rep x) ⊆ orbit Q (rep x) := by
      intro w hw
      simp only [B] at hw
      obtain ⟨r, rfl⟩ := MulAction.mem_orbit_iff.mp hw
      exact MulAction.mem_orbit (rep x) (r : ↥Q)
    have hmem : q⁻¹ • y ∈ orbit Q (rep x) := hBsub hqy
    have hqy2 : q • (q⁻¹ • y) ∈ orbit Q (rep x) := by
      obtain ⟨q₀, hq₀⟩ := MulAction.mem_orbit_iff.mp hmem
      rw [← hq₀]
      simpa [mul_smul] using MulAction.mem_orbit (rep x) (q * q₀)
    have hqeq : q • (q⁻¹ • y) = y := by rw [smul_inv_smul]
    rw [hqeq] at hqy2
    rwa [MulAction.orbit_eq_iff.mpr (rep_mem x)] at hqy2
  have hprop1 : ∀ x y, y ∈ β x ↔ β y = β x := by
    intro x y
    constructor
    · intro hy
      rcases hy with ⟨q, hq, hqy⟩
      have hmem : y ∈ orbit Q x := hsub x ⟨q, hq, hqy⟩
      have hrep : rep y = rep x := rep_same x y hmem
      obtain ⟨r, hr⟩ := MulAction.mem_orbit_iff.mp (by simpa only [B] using hqy)
      have hqr : (q * (r : ↥Q)) • rep x = y := by
        rw [mul_smul]
        change q • (r • rep x) = y
        rw [hr, smul_inv_smul]
      apply Set.ext
      intro w
      rw [mem_image_key y (q * (r : ↥Q)) (by rwa [hrep]) w,
        mem_image_key x q hq w, hrep]
      have hcoord : (q * (r : ↥Q))⁻¹ • w = (r⁻¹ : ↥(R (rep x))) • (q⁻¹ • w) := by
        rw [mul_inv_rev, mul_smul]
        rfl
      rw [hcoord]
      exact smul_B_mem (rep x) r⁻¹ (q⁻¹ • w)
    · intro heq
      rw [← heq]
      exact mem_self y
  have B_top : ∀ z : Ω, R z = ⊤ → B z = orbit Q z := by
    intro z hz
    ext w
    constructor
    · intro hw
      simp only [B] at hw
      rw [hz] at hw
      obtain ⟨g, rfl⟩ := MulAction.mem_orbit_iff.mp hw
      simpa [Subgroup.smul_def] using MulAction.mem_orbit z (g : ↥Q)
    · intro hw
      obtain ⟨g, rfl⟩ := MulAction.mem_orbit_iff.mp hw
      change g • z ∈ orbit ↥(R z) z
      rw [hz]
      simpa [Subgroup.smul_def] using
        MulAction.mem_orbit z (⟨g, Subgroup.mem_top g⟩ : ↥(⊤ : Subgroup ↥Q))
  have hsmall_eq : ∀ x, Nat.card (orbit Q x) < 4 → β x = orbit Q x := by
    intro x hx
    have horb : orbit Q (rep x) = orbit Q x := MulAction.orbit_eq_iff.mpr (rep_mem x)
    have hRtop : R (rep x) = ⊤ := (hR (rep x)).2.1 (by rwa [horb])
    obtain ⟨q, hq⟩ := MulAction.mem_orbit_iff.mp (self_mem_orbit_rep x)
    apply Set.Subset.antisymm (hsub x)
    intro y hy
    have hy' : y ∈ orbit Q (rep x) := by rwa [horb]
    have hyB : q⁻¹ • y ∈ B (rep x) := by
      rw [B_top (rep x) hRtop]
      obtain ⟨q₀, hq₀⟩ := MulAction.mem_orbit_iff.mp hy'
      rw [← hq₀]
      simpa [mul_smul] using MulAction.mem_orbit (rep x) (q⁻¹ * q₀)
    exact (mem_image_key x q hq y).mpr hyB
  have hfour : ∀ x, 4 ≤ Nat.card (orbit Q x) → (β x).ncard = 4 := by
    intro x hx
    have horb : orbit Q (rep x) = orbit Q x := MulAction.orbit_eq_iff.mpr (rep_mem x)
    have hR4 : (orbit ↥(R (rep x)) (rep x)).ncard = 4 :=
      (hR (rep x)).2.2 (by rwa [horb])
    obtain ⟨q, hq⟩ := MulAction.mem_orbit_iff.mp (self_mem_orbit_rep x)
    rw [key x q hq, Set.ncard_image_of_injective (B (rep x)) (MulAction.injective q)]
    exact hR4
  have hinv : ∀ q ∈ Q, ∀ x, β (q x) = q '' β x := by
    intro q hq x
    have hmem : q x ∈ orbit Q x := by
      simpa [Subgroup.smul_def] using MulAction.mem_orbit x (⟨q, hq⟩ : ↥Q)
    have hrep : rep (q x) = rep x := rep_same x (q x) hmem
    obtain ⟨p, hp⟩ := MulAction.mem_orbit_iff.mp (self_mem_orbit_rep x)
    have hqp : ((⟨q, hq⟩ : ↥Q) * p) • rep x = q x := by
      rw [mul_smul]
      change (⟨q, hq⟩ : ↥Q) • (p • rep x) = q x
      rw [hp]
      rfl
    have h1 := key (q x) ((⟨q, hq⟩ : ↥Q) * p) (by rwa [hrep])
    rw [hrep] at h1
    have h2 := key x p hp
    rw [h1, h2, Set.image_image]
    congr 1
  exact ⟨β, hprop1, hsub, hsmall_eq, hfour, hinv⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.TwelveThirteen