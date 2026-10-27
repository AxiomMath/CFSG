module

public import CFSG.Quasithin.EmptyFaithful.S146zHOfour
public import CFSG.Quasithin.EmptyFaithful.S146zIAlg
public import CFSG.Quasithin.EmptyFaithful.S146zIGen

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7 CFSG.Quasithin.C1Pack
  CFSG.Quasithin.CosetGeom
open scoped commutatorElement Pointwise

section Dih

theorem two_ne_zero_zmod {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) : (2 : ZMod p) ≠ 0 := by
  intro h
  have h' : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
  rw [ZMod.natCast_eq_zero_iff] at h'
  exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h')

theorem dih_comm_invol {p : ℕ} [Fact p.Prime] (hp2 : (2 : ZMod p) ≠ 0) {a b : DihedralGroup p}
    (ha : a * a = 1) (hb : b * b = 1) (hab : a * b = b * a) : a = 1 ∨ b = 1 ∨ a = b := by
  have key : ∀ i : ZMod p, DihedralGroup.r i * DihedralGroup.r i = 1 → i = 0 := by
    intro i h1
    have h2 : DihedralGroup.r (i + i) = DihedralGroup.r 0 := by
      rw [← DihedralGroup.r_mul_r]
      exact h1.trans DihedralGroup.one_def
    have h3 := DihedralGroup.r.inj h2
    have h4 : (2 : ZMod p) * i = 0 := by rw [two_mul]; exact h3
    exact (mul_eq_zero.mp h4).resolve_left hp2
  cases a with
  | r i =>
    left
    rw [key i ha]
    rfl
  | sr i =>
    cases b with
    | r j =>
      right; left
      rw [key j hb]
      rfl
    | sr j =>
      right; right
      have h1 : DihedralGroup.r (j - i) = DihedralGroup.r (i - j) := by
        rw [← DihedralGroup.sr_mul_sr, ← DihedralGroup.sr_mul_sr]
        exact hab
      have h2 := DihedralGroup.r.inj h1
      have h3 : (2 : ZMod p) * (j - i) = 0 := by
        calc (2 : ZMod p) * (j - i) = (j - i) + (j - i) := by rw [two_mul]
          _ = (i - j) + (j - i) := by rw [← h2]
          _ = 0 := by ring
      have h4 : j - i = 0 := (mul_eq_zero.mp h3).resolve_left hp2
      have h5 : j = i := sub_eq_zero.mp h4
      rw [h5]

end Dih

section Num

variable {G : Type} [Group G] [Finite G] {T M H : Subgroup G} {p : ℕ} {H₀ H₁ H₂ : Subgroup G} {t : G}

theorem IsDecP.card_Wsub_of_mIdx_eight (S : Setting146 G T M) {PQ : Subgroup G}
    (hred : IsRedCE T M H PQ p) (h : IsDecP T M H p H₀ H₁ H₂ t)
    (h91 : HypF91 T (VZ T M) (yOfL22 T M) (quasithinOmegaOneCenter T) (VZ T M) H)
    (h8 : mIdx (uK T M H ⊔ quasithinOmegaOneCenter T) (quasithinOmegaOneCenter T) = 8) :
    Nat.card (Wsub h91 (uHi T M H H₁)) = 16 := by
  have hH : IsHTM T M H := hred.isHTM
  have hr₁ : mIdx (uHi T M H H₁) (quasithinOmegaOneCenter T) = 4 := by
    have := h.mIdx_uK_sup_eq S hred
    omega
  have hH₁H : H₁ ≤ H := h.le₁.trans h.le
  have hi₁ : uHi T M H H₁ ≤ conjClosure (VZ T M) H := uHi_le_conjClosure hH₁H
  have hUZ : conjClosure (VZ T M) H ≤ Subgroup.normalizer (quasithinOmegaOneCenter T : Set G) :=
    S.conjClosure_le_normalizer_Z hH
  have hUp : IsPGroup 2 (conjClosure (VZ T M) H) :=
    isPGroup_of_isElemAbelian (S.lemma_14_5_15_two hH)
  rw [card_Wsub h91 hi₁, card_tildeOf_eq_relIndex (Z_le_uHi T M H H₁) (hi₁.trans hUZ),
    HypF98.relIndex_eq_two_pow_mIdx (hUp.to_le hi₁), hr₁]
  norm_num

theorem IsDecP.relIndex_inf_pCore_le_two (h : IsDecP T M H p H₀ H₁ H₂ t) (hp : p.Prime)
    (hp2 : p ≠ 2) {B : Subgroup G} (hBH₁ : B ≤ H₁) (hBab : IsElemAbelian 2 B) :
    (B ⊓ pCoreOf 2 H).relIndex B ≤ 2 := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨φ, -, hker⟩ := h.exists_phi_gen
  have h2 : (2 : ZMod p) ≠ 0 := two_ne_zero_zmod hp hp2
  by_cases hB : B ≤ pCoreOf 2 H
  · rw [inf_eq_left.mpr hB, Subgroup.relIndex_self]
    norm_num
  · obtain ⟨y, hyB, hyQ⟩ := IsConcreteLE.not_le_iff_exists.mp hB
    unfold Subgroup.relIndex
    refine index_le_two_of_forall _ (⟨y, hyB⟩ : ↥B) fun z => ?_
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    have hyz : (y : G) * z = z * y := isElemAbelian_comm hBab hyB z.2
    have hy₁ : y ∈ H₁ := hBH₁ hyB
    have hz₁ : (z : G) ∈ H₁ := hBH₁ z.2
    let ψ : ↥B →* DihedralGroup p := φ.comp (Subgroup.inclusion hBH₁)
    have hψ : ∀ w : ↥B, ψ w = φ ⟨(w : G), hBH₁ w.2⟩ := fun w => rfl
    have hsq : ∀ w : ↥B, ψ w * ψ w = 1 := by
      intro w
      rw [← map_mul]
      have : w * w = 1 := Subtype.ext (by
        have := isElemAbelian_pow_eq_one hBab w.2
        simpa [pow_two] using this)
      rw [this, map_one]
    have hcomm : ψ ⟨y, hyB⟩ * ψ z = ψ z * ψ ⟨y, hyB⟩ := by
      rw [← map_mul, ← map_mul]
      exact congrArg ψ (Subtype.ext hyz)
    rcases dih_comm_invol h2 (hsq ⟨y, hyB⟩) (hsq z) hcomm with h1 | h1 | h1
    · exfalso
      apply hyQ
      exact (hker ⟨y, hy₁⟩).mp (by exact h1)
    · left
      refine ⟨z.2, ?_⟩
      exact (hker ⟨(z : G), hz₁⟩).mp (by exact h1)
    · right
      refine ⟨B.mul_mem (B.inv_mem hyB) z.2, ?_⟩
      have h3 : ψ ((⟨y, hyB⟩ : ↥B)⁻¹ * z) = 1 := by
        rw [map_mul, map_inv, h1, inv_mul_cancel]
      have := (hker ⟨(y : G)⁻¹ * z, H₁.mul_mem (H₁.inv_mem hy₁) hz₁⟩).mp (by exact h3)
      simpa using this

end Num

end CFSG.Quasithin
