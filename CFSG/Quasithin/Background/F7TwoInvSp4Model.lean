module

public import CFSG.Quasithin.Background.F7TwoInvAutWrap
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticEvenAllInvolutionFourGroup
public import CFSG.ClassicalGroups.Symplectic.ProjectivePerfect

public section

namespace CFSG.Quasithin.F7Two

open CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
open CFSG.ComponentClassification.UnbalancedCatalog
open CFSG.ComponentClassification.UnbalancedCatalog.SpChain
open CFSG.ComponentClassification.OuterAutomorphisms (inner)

@[expose] def InvAutGenSp4OddEta : Prop :=
  ∀ (m : ℕ) (K : Type) [Field K] [Finite K] [CharP K 2], 1 ≤ m →
    Nat.card K = 2 ^ (2 * m + 1) → InvAutGen (antiSp K) (minorAut K ^ (2 * m + 1))

theorem invAutGen_congr_iff {A B : Type*} [Group A] [Group B] (e : A ≃* B) (φ : MulAut A) :
    InvAutGen B (MulAut.congr e φ) ↔ InvAutGen A φ := by
  constructor
  · intro h
    have h2 := InvAutGen.congr e.symm h
    have h3 : (e.symm.symm.trans (MulAut.congr e φ)).trans e.symm = φ :=
      MulEquiv.ext fun x => by simp [MulAut.congr_apply]
    rwa [h3] at h2
  · intro h
    have h1 : MulAut.congr e φ = (e.symm.trans φ).trans e := MulEquiv.ext fun _ => rfl
    rw [h1]
    exact InvAutGen.congr e h

theorem congr_conj_apply {A B : Type*} [Group A] [Group B] (e : A ≃* B) (x : A) :
    MulAut.congr e (MulAut.conj x) = MulAut.conj (e x) :=
  MulEquiv.ext fun y => by simp [MulAut.congr_apply, MulAut.conj_apply]

variable {K : Type} [Field K]

theorem fieldAut_eq_congr [CharP K 2] (σ : K ≃+* K) :
    fieldAut 2 K σ = MulAut.congr (projSpEquiv K) (fieldSp 2 K σ) := by
  refine MulEquiv.ext fun x => ?_
  obtain ⟨g, rfl⟩ := proj_surjective x
  rw [MulAut.congr_apply]
  change _ = projSpEquiv K (fieldSp 2 K σ ((projSpEquiv K).symm (projSpEquiv K g)))
  rw [MulEquiv.symm_apply_apply, fieldAut_proj]
  rfl

theorem isSimpleGroup_sp4_proj (hK : 4 ≤ Nat.card K) :
    IsSimpleGroup (StatedProj (StatedSp 2 K)) :=
  CFSG.ClassicalGroups.Symplectic.isSimpleGroup_statedProj_statedSp K 2 (by norm_num)
    (Or.inl (Or.inr hK))

theorem sp4_proj_nonabelian [Finite K] (hK : 4 ≤ Nat.card K) :
    ∃ x y : StatedProj (StatedSp 2 K), x * y ≠ y * x := by
  have hperf : Group.IsPerfect (StatedProj (StatedSp 2 K)) := by
    refine CFSG.ClassicalGroups.Symplectic.symplectic_projective_perfect 2 K (Or.inl ?_)
    have : Fintype K := Fintype.ofFinite K
    obtain ⟨s, -, hs⟩ := Finset.exists_subset_card_eq (s := (Finset.univ : Finset K)) (n := 4)
      (by rwa [Finset.card_univ, ← Nat.card_eq_fintype_card])
    exact ⟨s, hs⟩
  have := isSimpleGroup_sp4_proj hK
  by_contra hcomm
  push Not at hcomm
  let _ : CommGroup (StatedProj (StatedSp 2 K)) :=
    { (inferInstance : Group (StatedProj (StatedSp 2 K))) with mul_comm := hcomm }
  have hker : (⊤ : Subgroup (StatedProj (StatedSp 2 K))) ≤
      (MonoidHom.id (StatedProj (StatedSp 2 K))).ker := by
    rw [← hperf.commutator_eq_top]
    exact Abelianization.commutator_subset_ker _
  obtain ⟨a, b, hab⟩ := exists_pair_ne (StatedProj (StatedSp 2 K))
  exact hab ((MonoidHom.mem_ker.mp (hker (Subgroup.mem_top a))).trans
    (MonoidHom.mem_ker.mp (hker (Subgroup.mem_top b))).symm)

theorem exists_inner_involution [CharP K 2] (hs : IsSimpleGroup (StatedProj (StatedSp 2 K)))
    (hnonab : ∃ x y : StatedProj (StatedSp 2 K), x * y ≠ y * x)
    {β : MulAut (StatedProj (StatedSp 2 K))} (hβ2 : β * β = 1) (hβ1 : β ≠ 1)
    (hβi : β ∈ inner (StatedProj (StatedSp 2 K))) :
    ∃ g : StatedSp 2 K, g * g = 1 ∧ g ≠ 1 ∧
      β = MulAut.congr (projSpEquiv K) (MulAut.conj g) := by
  obtain ⟨p, rfl⟩ := hβi
  set g := (projSpEquiv K).symm p with hg
  have hβg : MulAut.conj p = MulAut.congr (projSpEquiv K) (MulAut.conj g) := by
    rw [congr_conj_apply, hg, MulEquiv.apply_symm_apply]
  have hpp : p * p = 1 := by
    have hc : p * p ∈ Subgroup.center (StatedProj (StatedSp 2 K)) := by
      rw [Subgroup.mem_center_iff]
      intro y
      have h1 := congrArg (fun φ : MulAut (StatedProj (StatedSp 2 K)) => φ y) hβ2
      simp only [MulAut.mul_apply, MulAut.conj_apply, MulAut.one_apply] at h1
      calc y * (p * p) = (p * (p * y * p⁻¹) * p⁻¹) * (p * p) := by rw [h1]
        _ = p * p * y := by group
    rw [center_eq_bot_of_isSimpleGroup hs hnonab, Subgroup.mem_bot] at hc
    exact hc
  refine ⟨g, ?_, ?_, hβg⟩
  · apply (projSpEquiv K).injective
    rw [map_mul, map_one, hg, MulEquiv.apply_symm_apply, hpp]
  · intro h1
    apply hβ1
    rw [hβg, h1, map_one, map_one]

theorem exists_field_involution [Finite K] [CharP K 2] {f : ℕ} (hf : 1 ≤ f)
    (hK : Nat.card K = 2 ^ f) (hfe : Even f)
    {β : MulAut (StatedProj (StatedSp 2 K))} (hβ2 : β * β = 1)
    (hβo : β ∉ inner (StatedProj (StatedSp 2 K))) :
    ∃ (σ : K ≃+* K) (h : StatedSp 2 K), σ ≠ 1 ∧ σ * σ = 1 ∧
      β = spInner 2 K h * fieldAut 2 K σ * (spInner 2 K h)⁻¹ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hord : orderOf β = 2 := orderOf_eq_prime (by rw [sq]; exact hβ2)
    fun h => hβo (h ▸ Subgroup.one_mem _)
  obtain ⟨-, -, -, -, -, hγ⟩ := even_symplectic_two_exterior_square_automorphism hf hK
  obtain ⟨-, -, -, -, -, -, -, -, -, -, heven, -⟩ := hγ (exceptionalAut K) exceptionalAut_proj
  obtain ⟨g, σ, hgσ⟩ := exists_eq_spInner_mul_fieldAut (heven hfe β hord)
  have hσ : σ ≠ 1 := by
    rintro rfl
    apply hβo
    rw [hgσ, map_one, mul_one]
    exact spInner_mem_inner g
  have hσσ : σ * σ = 1 := by
    have hsq := hβ2
    rw [hgσ, spInner_mul_fieldAut_mul, show (1 : MulAut (StatedProj (StatedSp 2 K))) =
      spInner 2 K 1 * fieldAut 2 K 1 by rw [map_one, map_one, one_mul]] at hsq
    exact (spInner_mul_fieldAut_inj hsq).2
  obtain ⟨-, -, -, -, -, -, -, -, -, -, h, hh⟩ :=
    even_symplectic_quadratic_involution_descent (by omega) hf hK hβ2 g σ
      (by rw [hgσ, spInner_apply]) hσ
  refine ⟨σ, h, hσ, hσσ, ?_⟩
  rw [hh, spInner_apply]

theorem invAutGen_of_odd_outer [Finite K] [CharP K 2] (hodd : InvAutGenSp4OddEta) {m : ℕ}
    (hm : 1 ≤ m)
    (hK : Nat.card K = 2 ^ (2 * m + 1))
    (hZ : Subgroup.center (StatedProj (StatedSp 2 K)) = ⊥)
    {β : MulAut (StatedProj (StatedSp 2 K))} (hβ2 : β ^ 2 = 1)
    (hβo : β ∉ inner (StatedProj (StatedSp 2 K))) :
    InvAutGen (StatedProj (StatedSp 2 K)) β := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, -, -, -, -, hγ⟩ := even_symplectic_two_exterior_square_automorphism (by omega) hK
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hodd'⟩ := hγ (exceptionalAut K) exceptionalAut_proj
  have hord : orderOf β = 2 := orderOf_eq_prime hβ2 fun h => hβo (h ▸ Subgroup.one_mem _)
  obtain ⟨g, hg⟩ := hodd' ⟨m, rfl⟩ β hord hβo
  set j : antiSp K ≃* StatedProj (StatedSp 2 K) := (antiSpEquiv K).trans (projSpEquiv K)
    with hjdef
  have hγj : exceptionalAut K = MulAut.congr j (minorAut K) := MulEquiv.ext fun _ => rfl
  have hj : j ((antiSpEquiv K).symm g) = proj 2 K g := by
    change projSpEquiv K (antiSpEquiv K ((antiSpEquiv K).symm g)) = proj 2 K g
    rw [MulEquiv.apply_symm_apply]
    rfl
  set g' := (antiSpEquiv K).symm g with hg'
  have hB : MulAut.congr j.symm β = MulAut.conj g' * minorAut K ^ (2 * m + 1) := by
    refine MulEquiv.ext fun x => ?_
    have hpow : ∀ n : ℕ, (exceptionalAut K ^ n) (j x) = j ((minorAut K ^ n) x) := by
      intro n
      rw [hγj, ← map_pow]
      change j ((minorAut K ^ n) (j.symm (j x))) = _
      rw [MulEquiv.symm_apply_apply]
    change j.symm (β (j x)) = g' * (minorAut K ^ (2 * m + 1)) x * g'⁻¹
    rw [hg, MulAut.mul_apply, hpow, spInner_eq_conj, MulAut.conj_apply, ← hj, ← map_inv,
      ← map_mul, ← map_mul, MulEquiv.symm_apply_apply]
  have hZG : Subgroup.center (antiSp K) = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    have hjz : j z ∈ Subgroup.center (StatedProj (StatedSp 2 K)) := by
      rw [Subgroup.mem_center_iff] at hz ⊢
      intro y
      obtain ⟨w, rfl⟩ := j.surjective y
      rw [← map_mul, ← map_mul, hz w]
    rw [hZ, Subgroup.mem_bot, ← map_one j] at hjz
    exact j.injective hjz
  have hB2 : (MulAut.conj g' * minorAut K ^ (2 * m + 1)) ^ 2 = 1 := by
    rw [← hB, ← map_pow, hβ2, map_one]
  obtain ⟨h, hh⟩ := exists_conj_eq_minorAut_pow hK hZG g' hB2
  have h1 : InvAutGen (antiSp K) (MulAut.conj g' * minorAut K ^ (2 * m + 1)) :=
    (InvAutGen.conj_iff (MulAut.conj h) _).2 (by rw [hh]; exact hodd m K hm hK)
  rw [← hB] at h1
  exact (invAutGen_congr_iff j.symm β).1 h1

end CFSG.Quasithin.F7Two
