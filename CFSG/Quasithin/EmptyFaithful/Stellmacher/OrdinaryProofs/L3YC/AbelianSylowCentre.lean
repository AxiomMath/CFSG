module

public import Mathlib.GroupTheory.Focal

public section

open IsMulCommutative

namespace CFSG.Quasithin.EmptyFaithful.Stellmacher.OrdinaryProofs.L3YC.AbelianSylowCentre

section Averaging

variable {Q : Type*} [CommGroup Q]

variable (A : Subgroup (MulAut Q)) [Fintype A]

@[expose] def avgHom : Q →* Q where
  toFun y := ∏ α : A, ((α : MulAut Q) y)
  map_one' := by simp
  map_mul' y z := by
    simp [map_mul, Finset.prod_mul_distrib]

variable {A}

theorem avgHom_apply (y : Q) : avgHom A y = ∏ α : A, ((α : MulAut Q) y) := rfl

theorem avgHom_smul (β : MulAut Q) (hβ : β ∈ A) (y : Q) :
    avgHom A (β y) = avgHom A y := by
  rw [avgHom_apply, avgHom_apply]
  refine Fintype.prod_equiv (Equiv.mulRight (⟨β, hβ⟩ : A)) _ _ (fun α => ?_)
  simp [Subgroup.coe_mul]

theorem avgHom_fixed (c : Q) (hc : ∀ α : A, (α : MulAut Q) c = c) :
    avgHom A c = c ^ Fintype.card A := by
  rw [avgHom_apply]
  simp [hc, Finset.prod_const, Finset.card_univ]

theorem eq_one_of_fixed (hco : Nat.Coprime (Nat.card Q) (Nat.card A))
    (hgen : ∀ y : Q, y ∈ Subgroup.closure {z : Q | ∃ x : Q, ∃ β ∈ A, z = x⁻¹ * β x})
    (c : Q) (hfix : ∀ β ∈ A, β c = c) : c = 1 := by
  have hker : ∀ y : Q, avgHom A y = 1 := by
    have hcl : Subgroup.closure {z : Q | ∃ x : Q, ∃ β ∈ A, z = x⁻¹ * β x} ≤ (avgHom A).ker := by
      apply (Subgroup.closure_le _).mpr
      rintro z ⟨x, β, hβ, rfl⟩
      rw [SetLike.mem_coe, MonoidHom.mem_ker, map_mul, map_inv, avgHom_smul β hβ, inv_mul_cancel]
    intro y
    exact MonoidHom.mem_ker.1 (hcl (hgen y))
  have hA : Nat.card A = Fintype.card A := Nat.card_eq_fintype_card
  rw [hA] at hco
  have hpow : c ^ Fintype.card A = 1 := by
    rw [← avgHom_fixed c (fun α => hfix _ α.2), hker c]
  have h1 : orderOf c = 1 :=
    Nat.eq_one_of_dvd_coprimes hco (orderOf_dvd_natCard c) (orderOf_dvd_of_pow_eq_one hpow)
  exact orderOf_eq_one_iff.mp h1

end Averaging

section Application

open Subgroup
open scoped commutatorElement

variable {G : Type*} [Group G] {p : ℕ} [Fact p.Prime]

theorem eq_one_of_normalizer_fixed [Finite G] (hG : _root_.commutator G = ⊤)
    (P : Sylow p G) [IsMulCommutative P] (c : G) (hc : c ∈ P)
    (hfix : ∀ n ∈ normalizer (P : Set G), n⁻¹ * c * n = c) : c = 1 := by
  let ν := (P : Subgroup G).normalizerMonoidHom
  let A : Subgroup (MulAut (P : Subgroup G)) := ν.range
  have : Finite (MulAut (P : Subgroup G)) := inferInstance
  have : Finite A := Subtype.finite
  letI : Fintype A := Fintype.ofFinite A
  have hcomm : ∀ a b : (P : Subgroup G), (a : G) * b = b * a :=
    fun a b => congrArg Subtype.val (mul_comm a b)
  have hval : ∀ (x : normalizer (P : Set G)) (a : (P : Subgroup G)),
      ((ν x a : (P : Subgroup G)) : G) = (x : G) * a * (x : G)⁻¹ :=
    fun _ _ => rfl
  have hco : Nat.Coprime (Nat.card (P : Subgroup G)) (Nat.card A) := by
    have hle : (P : Subgroup G).subgroupOf (normalizer (P : Set G)) ≤ ν.ker := by
      intro x hx
      rw [MonoidHom.mem_ker]
      refine MulEquiv.ext fun y => Subtype.ext ?_
      rw [mem_subgroupOf] at hx
      have hxy : (x : G) * y = y * x := hcomm ⟨x, hx⟩ y
      show ((ν x y : (P : Subgroup G)) : G) = (y : G)
      rw [hval, hxy, mul_inv_cancel_right]
    have hk : ν.ker.index = Nat.card A := Subgroup.index_ker ν
    have hdvd1 : ν.ker.index ∣ ((P : Subgroup G).subgroupOf (normalizer (P : Set G))).index :=
      Subgroup.index_dvd_of_le hle
    have hrel : ((P : Subgroup G).subgroupOf (normalizer (P : Set G))).index ∣ (P : Subgroup G).index :=
      ⟨_, (relIndex_mul_index (le_normalizer)).symm⟩
    have hA : Nat.card A ∣ (P : Subgroup G).index := by
      rw [← hk]
      exact hdvd1.trans hrel
    exact Nat.Coprime.coprime_dvd_right hA (Sylow.card_coprime_index P)
  have hgen : ∀ y : (P : Subgroup G), y ∈ Subgroup.closure
      {z : (P : Subgroup G) | ∃ x : (P : Subgroup G), ∃ β ∈ A, z = x⁻¹ * β x} := by
    have hfoc : (P : Subgroup G).focalSubgroup ≤
        (Subgroup.closure {z : (P : Subgroup G) | ∃ x : (P : Subgroup G), ∃ β ∈ A, z = x⁻¹ * β x}).map
          (P : Subgroup G).subtype := by
      rw [focalSubgroup_def]
      apply (Subgroup.closure_le _).mpr
      rintro g ⟨hgP, x, hxP, u, rfl⟩
      have e1 : u * x⁻¹ * u⁻¹ = x⁻¹ * ⁅x, u⁆ := by
        rw [commutatorElement_def]; group
      have hy : (u⁻¹)⁻¹ * x⁻¹ * u⁻¹ ∈ (P : Subgroup G) := by
        rw [inv_inv, e1]; exact mul_mem (inv_mem hxP) hgP
      obtain ⟨n, hn, hnx⟩ := Sylow.conj_eq_normalizer_conj_of_mem P x⁻¹ u⁻¹ (inv_mem hxP) hy
      rw [inv_inv] at hnx
      have hn' : n⁻¹ ∈ normalizer (P : Set G) := inv_mem hn
      have hmem : ν ⟨n⁻¹, hn'⟩ ∈ A := MonoidHom.mem_range.2 ⟨⟨n⁻¹, hn'⟩, rfl⟩
      have hval' : ((ν ⟨n⁻¹, hn'⟩ (⟨x, hxP⟩⁻¹ : (P : Subgroup G)) : (P : Subgroup G)) : G)
          = n⁻¹ * x⁻¹ * n := by
        rw [hval]; simp
      have hinv : (((⟨x, hxP⟩ : (P : Subgroup G))⁻¹)⁻¹ : (P : Subgroup G)) = x := by simp
      refine Subgroup.mem_map.2 ⟨((⟨x, hxP⟩ : (P : Subgroup G))⁻¹)⁻¹ * ν ⟨n⁻¹, hn'⟩
        (⟨x, hxP⟩⁻¹ : (P : Subgroup G)), Subgroup.subset_closure
          (by exact ⟨(⟨x, hxP⟩ : (P : Subgroup G))⁻¹, ν ⟨n⁻¹, hn'⟩, hmem, rfl⟩), ?_⟩
      show ((((⟨x, hxP⟩ : (P : Subgroup G))⁻¹)⁻¹ * ν ⟨n⁻¹, hn'⟩
        (⟨x, hxP⟩⁻¹ : (P : Subgroup G)) : (P : Subgroup G)) : G) = _
      rw [Subgroup.coe_mul, hinv, hval', ← hnx, commutatorElement_def]
      group
    intro y
    have htop : (P : Subgroup G) ≤ (P : Subgroup G).focalSubgroup := by
      have h := Subgroup.commutator_inf_eq_focalSubgroup (G := G) (p := p) P
      rw [hG, top_inf_eq] at h
      exact h.le
    obtain ⟨t, ht, hty⟩ := Subgroup.mem_map.1 (hfoc (htop y.2))
    have hty' : t = y := Subtype.ext hty
    rw [← hty']
    exact ht
  have hfixA : ∀ β ∈ A, β ⟨c, hc⟩ = ⟨c, hc⟩ := by
    intro β hβ
    obtain ⟨m, rfl⟩ := MonoidHom.mem_range.1 hβ
    apply Subtype.ext
    have h := hfix (m : G)⁻¹ (inv_mem m.2)
    rw [inv_inv] at h
    rw [hval]
    exact h
  have key := eq_one_of_fixed hco hgen ⟨c, hc⟩ hfixA
  simpa using congrArg Subtype.val key

end Application

end CFSG.Quasithin.EmptyFaithful.Stellmacher.OrdinaryProofs.L3YC.AbelianSylowCentre

end
