module

public import CFSG.Quasithin.Background.A318PL3Core

public section

namespace CFSG.Quasithin

namespace A318P

open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)

structure InnFrame (Y : Type) [Group Y] (C : Type) [Group C] where
  fld : C →* MulAut Y
  fld_inter : ∀ c : C, fld c ∈ inner Y → c = 1
  three_mem : ∀ (α : MulAut Y) (k : ℕ), orderOf α = 3 ^ k →
    ∃ i ∈ inner Y, ∃ c : C, α = i * fld c
  nine : ∀ c : C, orderOf c = 3 → ∃ E : Subgroup Y, Nat.card E = 9 ∧
    CFSG.Open.IsElemAbelian 3 E ∧ ∀ y ∈ E, fld c y = y

@[expose] def InnFrame.transport {Y Y' : Type} [Group Y] [Group Y'] {C : Type} [Group C]
    (F : InnFrame Y' C) (Φ : MulAut Y ≃* MulAut Y') (ψ : Y ≃* Y')
    (hin : (inner Y).map Φ.toMonoidHom = inner Y')
    (hact : ∀ (α : MulAut Y) (y : Y), Φ α (ψ y) = ψ (α y)) : InnFrame Y C where
  fld := Φ.symm.toMonoidHom.comp F.fld
  fld_inter := by
    intro c hc
    apply F.fld_inter
    have h1 : Φ (Φ.symm (F.fld c)) ∈ inner Y' := by
      rw [← hin]
      exact ⟨_, hc, rfl⟩
    rwa [Φ.apply_symm_apply] at h1
  three_mem := by
    intro α k hα
    have hα' : orderOf (Φ α) = 3 ^ k := by rw [MulEquiv.orderOf_eq]; exact hα
    obtain ⟨i, hi, c, h⟩ := F.three_mem _ k hα'
    refine ⟨Φ.symm i, ?_, c, ?_⟩
    · rw [← hin] at hi
      obtain ⟨j, hj, hji⟩ := hi
      have : Φ.symm i = j := by rw [← hji]; exact Φ.symm_apply_apply j
      rw [this]
      exact hj
    · apply Φ.injective
      change Φ α = Φ (Φ.symm i * Φ.symm (F.fld c))
      rw [map_mul, Φ.apply_symm_apply, Φ.apply_symm_apply]
      exact h
  nine := by
    intro c hc
    obtain ⟨E, hE9, hEel, hEfix⟩ := F.nine c hc
    refine ⟨E.map ψ.symm.toMonoidHom, ?_, ?_, ?_⟩
    · rw [Subgroup.card_map_of_injective ψ.symm.injective, hE9]
    · exact CFSG.SectionRank.isElemAbelian_map hEel ψ.symm.toMonoidHom
    · rintro _ ⟨e, he, rfl⟩
      have h1 : ψ ((Φ.symm (F.fld c)) (ψ.symm e)) = F.fld c e := by
        rw [← hact, Φ.apply_symm_apply, MulEquiv.apply_symm_apply]
      have h2 := hEfix e he
      change (Φ.symm (F.fld c)) (ψ.symm e) = ψ.symm e
      apply ψ.injective
      rw [h1, h2, MulEquiv.apply_symm_apply]

@[expose] def InnFrame.ofMulEquiv {Y Y' : Type} [Group Y] [Group Y'] {C : Type} [Group C]
    (F : InnFrame Y' C) (ψ : Y ≃* Y') : InnFrame Y C :=
  F.transport (MulAut.congr ψ) ψ
    (CFSG.ComponentClassification.OuterAutomorphisms.inner_map_congr ψ)
    (fun α y => by simp [MulAut.congr_apply])

section Core

variable {X : Type} [Group X] [Finite X] {S : Subgroup X} [S.Normal]
  {C : Type} [Group C]

omit [Finite X] [S.Normal] in
theorem exists_pow_not_mem_cube_mem {x : X} (hxS : x ∉ S) {k : ℕ} (hk : orderOf x = 3 ^ k) :
    ∃ y : X, y ∉ S ∧ y ^ 3 ∈ S ∧ ∃ j : ℕ, orderOf y = 3 ^ j := by
  induction k using Nat.strong_induction_on generalizing x with
  | _ k ih =>
    by_cases h3 : x ^ 3 ∈ S
    · exact ⟨x, hxS, h3, k, hk⟩
    · have hk1 : k ≠ 0 := by
        rintro rfl
        rw [pow_zero, orderOf_eq_one_iff] at hk
        exact hxS (hk ▸ S.one_mem)
      obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
      have hord : orderOf (x ^ 3) = 3 ^ k' := by
        rw [orderOf_pow' _ (by norm_num : (3 : ℕ) ≠ 0), hk]
        have : Nat.gcd (3 ^ (k' + 1)) 3 = 3 := by
          rw [pow_succ]
          exact Nat.gcd_eq_right (Dvd.intro_left _ rfl)
        rw [this, pow_succ, Nat.mul_div_cancel _ (by norm_num)]
      exact ih k' (by omega) h3 hord

theorem innFrame_core (hC : ∀ c : X, (∀ s ∈ S, c * s = s * c) → c = 1) (F : InnFrame ↥S C)
    (hX : CFSG.Open.pRank 3 (⊤ : Subgroup X) ≤ 2) :
    ∀ x : X, (∃ k : ℕ, orderOf x = 3 ^ k) → x ∈ S := by
  intro x ⟨k, hk⟩
  by_contra hxS
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set θ : X →* MulAut ↥S := MulAut.conjNormal with hθ
  have hinj : Function.Injective θ := conjNormal_injective hC
  obtain ⟨y, hyS, hy3, j, hj⟩ := exists_pow_not_mem_cube_mem hxS hk
  obtain ⟨i, hi, c, hic⟩ := F.three_mem (θ y) j (by rw [orderOf_injective θ hinj y]; exact hj)
  have hmapθ : S.map θ = inner ↥S := map_conjNormal_eq_inner
  have hc1 : c ≠ 1 := by
    rintro rfl
    apply hyS
    apply mem_of_conjNormal_inner hC
    rw [map_one, mul_one] at hic
    exact hic ▸ hi
  have hc3 : c ^ 3 = 1 := by
    have h1 : θ (y ^ 3) ∈ inner ↥S := by
      rw [← hmapθ]
      exact ⟨_, hy3, rfl⟩
    rw [map_pow, hic, L3Frame.mul_pow_three] at h1
    have hN : (inner ↥S : Subgroup (MulAut ↥S)).Normal := inferInstance
    have hN1 : i * (F.fld c * i * (F.fld c)⁻¹) * (F.fld c ^ 2 * i * (F.fld c ^ 2)⁻¹) ∈
        inner ↥S := by
      refine mul_mem (mul_mem hi ?_) ?_
      · have := hN.conj_mem i hi (F.fld c)
        simpa using this
      · have := hN.conj_mem i hi (F.fld c ^ 2)
        simpa using this
    apply F.fld_inter
    have h2 : F.fld c ^ 3 ∈ (inner ↥S : Subgroup (MulAut ↥S)) := by
      have := mul_mem (inv_mem hN1) h1
      rwa [inv_mul_cancel_left] at this
    rwa [map_pow]
  have hcord : orderOf c = 3 := orderOf_eq_prime hc3 hc1
  obtain ⟨s, hs, hsi⟩ : i ∈ S.map θ := by rw [hmapθ]; exact hi
  set z : X := s⁻¹ * y with hz
  have hθz : θ z = F.fld c := by
    rw [hz, map_mul, map_inv, hsi, hic]
    group
  have hz3 : z ^ 3 = 1 := by
    apply hinj
    rw [map_pow, hθz, ← map_pow, hc3, map_one, map_one]
  have hzS : z ∉ S := by
    intro hzS
    have : F.fld c ∈ (inner ↥S : Subgroup (MulAut ↥S)) := by
      rw [← hmapθ, ← hθz]
      exact ⟨z, hzS, rfl⟩
    exact hc1 (F.fld_inter c this)
  have hz1 : z ≠ 1 := fun h => hzS (h ▸ S.one_mem)
  have hzord : orderOf z = 3 := orderOf_eq_prime hz3 hz1
  obtain ⟨E, hE9, hEel, hEfix⟩ := F.nine c hcord
  have hES : E.map S.subtype ≤ S := by
    rintro _ ⟨e, -, rfl⟩
    exact e.2
  have hEel' : CFSG.Open.IsElemAbelian 3 (E.map S.subtype) :=
    CFSG.SectionRank.isElemAbelian_map hEel S.subtype
  have hEcard : Nat.card (E.map S.subtype) = 3 ^ 2 := by
    rw [Subgroup.card_map_of_injective S.subtype_injective, hE9]
    norm_num
  have hcomm : ∀ e ∈ E.map S.subtype, z * e = e * z := by
    rintro _ ⟨e, he, rfl⟩
    have h1 := hEfix e he
    have h2 := congrArg (fun a : ↥S => (a : X)) (hθz ▸ rfl : θ z e = F.fld c e)
    simp only [hθ, MulAut.conjNormal_apply] at h2
    rw [h1] at h2
    calc z * (e : X) = z * e * z⁻¹ * z := by group
      _ = e * z := by rw [h2]
  have h3 := three_le_pRank_of_centralizes (hp := ⟨Nat.prime_three⟩) hzord hzS hES hEel' hEcard hcomm
  omega

end Core

end A318P

end CFSG.Quasithin
