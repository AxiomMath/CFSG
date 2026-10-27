module

public import CFSG.Quasithin.Background.A318PL3Core

public section

namespace CFSG.Quasithin

namespace R3c18

open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)
open CFSG.Quasithin.A318P

structure PFrame (p : ℕ) (Y : Type) [Group Y] (C : Type) [Group C] where
  fld : C →* MulAut Y
  fld_inter : ∀ c : C, fld c ∈ inner Y → c = 1
  conj_mem : ∀ (α : MulAut Y) (k : ℕ), orderOf α = p ^ k →
    ∃ g : MulAut Y, ∃ i ∈ inner Y, ∃ c : C, g * α * g⁻¹ = i * fld c
  sq : 2 ≤ CFSG.pRank p Y → ∀ c : C, orderOf c = p → ∃ E : Subgroup Y, Nat.card E = p ^ 2 ∧
    CFSG.Open.IsElemAbelian p E ∧ ∀ y ∈ E, fld c y = y

section Transport

theorem pRank_congr {p : ℕ} (hp : 1 < p) {Y Y' : Type} [Group Y] [Finite Y] [Group Y'] [Finite Y']
    (e : Y ≃* Y') : CFSG.pRank p Y = CFSG.pRank p Y' := by
  rw [CFSG.SectionRank.pRank_eq_open_pRank_top, CFSG.SectionRank.pRank_eq_open_pRank_top]
  exact CFSG.SectionRank.pRank_top_eq_of_mulEquiv hp e

@[expose] def PFrame.transport {p : ℕ} (hp : 1 < p) {Y Y' : Type} [Group Y] [Finite Y] [Group Y']
    [Finite Y'] {C : Type} [Group C]
    (F : PFrame p Y' C) (Φ : MulAut Y ≃* MulAut Y') (ψ : Y ≃* Y')
    (hin : (inner Y).map Φ.toMonoidHom = inner Y')
    (hact : ∀ (α : MulAut Y) (y : Y), Φ α (ψ y) = ψ (α y)) : PFrame p Y C where
  fld := Φ.symm.toMonoidHom.comp F.fld
  fld_inter := by
    intro c hc
    apply F.fld_inter
    have h1 : Φ (Φ.symm (F.fld c)) ∈ inner Y' := by
      rw [← hin]
      exact ⟨_, hc, rfl⟩
    rwa [Φ.apply_symm_apply] at h1
  conj_mem := by
    intro α k hα
    have hα' : orderOf (Φ α) = p ^ k := by rw [MulEquiv.orderOf_eq]; exact hα
    obtain ⟨g', i, hi, c, h⟩ := F.conj_mem _ k hα'
    refine ⟨Φ.symm g', Φ.symm i, ?_, c, ?_⟩
    · rw [← hin] at hi
      obtain ⟨j, hj, hji⟩ := hi
      have : Φ.symm i = j := by rw [← hji]; exact Φ.symm_apply_apply j
      rw [this]
      exact hj
    · apply Φ.injective
      change Φ (Φ.symm g' * α * (Φ.symm g')⁻¹) = Φ (Φ.symm i * Φ.symm (F.fld c))
      rw [map_mul, map_mul, map_mul, map_inv, Φ.apply_symm_apply, Φ.apply_symm_apply,
        Φ.apply_symm_apply]
      exact h
  sq := by
    intro h2 c hc
    have h2' : 2 ≤ CFSG.pRank p Y' := by
      rw [← pRank_congr hp ψ]
      exact h2
    obtain ⟨E, hE9, hEel, hEfix⟩ := F.sq h2' c hc
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

@[expose] def PFrame.ofMulEquiv {p : ℕ} (hp : 1 < p) {Y Y' : Type} [Group Y] [Finite Y] [Group Y']
    [Finite Y'] {C : Type} [Group C] (F : PFrame p Y' C) (ψ : Y ≃* Y') : PFrame p Y C :=
  F.transport hp (MulAut.congr ψ) ψ
    (CFSG.ComponentClassification.OuterAutomorphisms.inner_map_congr ψ)
    (fun α y => by simp [MulAut.congr_apply])

end Transport

section Basic

theorem mul_pow_mem_mul_pow {G : Type*} [Group G] (N : Subgroup G) [N.Normal] {i : G} (hi : i ∈ N)
    (f : G) (n : ℕ) : ∃ j ∈ N, (i * f) ^ n = j * f ^ n := by
  induction n with
  | zero => exact ⟨1, N.one_mem, by simp⟩
  | succ n ih =>
    obtain ⟨j, hj, h⟩ := ih
    refine ⟨j * (f ^ n * i * (f ^ n)⁻¹), mul_mem hj (Subgroup.Normal.conj_mem inferInstance i hi _),
      ?_⟩
    rw [pow_succ, h, pow_succ f n]
    group

theorem exists_pow_not_mem_pow_mem {X : Type} [Group X] {S : Subgroup X} {p : ℕ} (hp : p.Prime)
    {x : X} (hxS : x ∉ S) {k : ℕ} (hk : orderOf x = p ^ k) :
    ∃ y : X, y ∉ S ∧ y ^ p ∈ S ∧ ∃ j : ℕ, orderOf y = p ^ j := by
  induction k using Nat.strong_induction_on generalizing x with
  | _ k ih =>
    by_cases h3 : x ^ p ∈ S
    · exact ⟨x, hxS, h3, k, hk⟩
    · have hk1 : k ≠ 0 := by
        rintro rfl
        rw [pow_zero, orderOf_eq_one_iff] at hk
        exact hxS (hk ▸ S.one_mem)
      obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
      have hord : orderOf (x ^ p) = p ^ k' := by
        rw [orderOf_pow' _ hp.ne_zero, hk]
        have : Nat.gcd (p ^ (k' + 1)) p = p := by
          rw [pow_succ]
          exact Nat.gcd_eq_right (Dvd.intro_left _ rfl)
        rw [this, pow_succ, Nat.mul_div_cancel _ hp.pos]
      exact ih k' (by omega) h3 hord

end Basic

section Core

variable {X : Type} [Group X] [Finite X] {S : Subgroup X} [S.Normal] {C : Type} [Group C]

theorem pframe_core {p : ℕ} [hp : Fact p.Prime]
    (hC : ∀ c : X, (∀ s ∈ S, c * s = s * c) → c = 1) (F : PFrame p ↥S C)
    (hS : 1 < CFSG.Open.pRank p S) (hX : CFSG.Open.pRank p (⊤ : Subgroup X) ≤ 2) :
    ∀ x : X, (∃ k : ℕ, orderOf x = p ^ k) → x ∈ S := by
  intro x ⟨k, hk⟩
  by_contra hxS
  set θ : X →* MulAut ↥S := MulAut.conjNormal with hθ
  have hinj : Function.Injective θ := conjNormal_injective hC
  have hmapθ : S.map θ = inner ↥S := map_conjNormal_eq_inner
  have hN : (inner ↥S : Subgroup (MulAut ↥S)).Normal := inferInstance
  obtain ⟨y, hyS, hyp, j, hj⟩ := exists_pow_not_mem_pow_mem hp.out hxS hk
  obtain ⟨g, i, hi, c, hgic⟩ := F.conj_mem (θ y) j (by rw [orderOf_injective θ hinj y]; exact hj)
  have hi' : g⁻¹ * i * g ∈ (inner ↥S : Subgroup (MulAut ↥S)) := by
    have := hN.conj_mem i hi g⁻¹
    simpa using this
  obtain ⟨s, hs, hsi⟩ : g⁻¹ * i * g ∈ S.map θ := by rw [hmapθ]; exact hi'
  set z : X := s⁻¹ * y with hz
  have hθy : θ y = g⁻¹ * (i * F.fld c) * g := by rw [← hgic]; group
  have hθz : θ z = g⁻¹ * F.fld c * g := by
    rw [hz, map_mul, map_inv, hsi, hθy]
    group
  have hc1 : c ≠ 1 := by
    rintro rfl
    apply hyS
    have h1 : θ z = 1 := by rw [hθz, map_one]; group
    have h2 : z = 1 := hinj (by rw [h1, map_one])
    have h3 : s = y := inv_mul_eq_one.mp h2
    rw [← h3]
    exact hs
  have hcp : c ^ p = 1 := by
    have h1 : θ (y ^ p) ∈ inner ↥S := by
      rw [← hmapθ]
      exact ⟨_, hyp, rfl⟩
    have h2 : g * θ (y ^ p) * g⁻¹ ∈ inner ↥S := hN.conj_mem _ h1 g
    have h3 : g * θ (y ^ p) * g⁻¹ = (i * F.fld c) ^ p := by
      rw [map_pow, ← conj_pow, hgic]
    obtain ⟨j', hj', hpow⟩ := mul_pow_mem_mul_pow (inner ↥S) hi (F.fld c) p
    have h4 : F.fld c ^ p ∈ inner ↥S := by
      have : F.fld c ^ p = j'⁻¹ * (g * θ (y ^ p) * g⁻¹) := by
        rw [h3, hpow]
        group
      rw [this]
      exact mul_mem (inv_mem hj') h2
    apply F.fld_inter
    rwa [map_pow]
  have hcord : orderOf c = p := orderOf_eq_prime hcp hc1
  have hz_p : z ^ p = 1 := by
    apply hinj
    rw [map_pow, hθz, map_one]
    have : (g⁻¹ * F.fld c * g) ^ p = g⁻¹ * F.fld c ^ p * g := by
      simpa using conj_pow (a := g⁻¹) (b := F.fld c) (i := p)
    rw [this, ← map_pow, hcp, map_one]
    group
  have hz1 : z ≠ 1 := fun h => hc1 (by
    have h1 : g⁻¹ * F.fld c * g = 1 := by rw [← hθz, h, map_one]
    have h2 : F.fld c = 1 := by
      have := congrArg (fun w => g * w * g⁻¹) h1
      simpa [mul_assoc] using this
    exact F.fld_inter c (by rw [h2]; exact (inner ↥S).one_mem))
  have hzord : orderOf z = p := orderOf_eq_prime hz_p hz1
  have hzS : z ∉ S := by
    intro hzS
    have h1 : θ z ∈ inner ↥S := by
      rw [← hmapθ]
      exact ⟨z, hzS, rfl⟩
    rw [hθz] at h1
    have h2 : F.fld c ∈ inner ↥S := by
      have := hN.conj_mem _ h1 g
      simpa [mul_assoc] using this
    exact hc1 (F.fld_inter c h2)
  have hS2 : 2 ≤ CFSG.pRank p ↥S := by
    rw [CFSG.SectionRank.pRank_eq_open_pRank_top, ← CFSG.SectionRank.pRank_eq_pRank_top_subgroup]
    exact hS
  obtain ⟨E, hE9, hEel, hEfix⟩ := F.sq hS2 c hcord
  set E₁ : Subgroup ↥S := E.map (g⁻¹ : MulAut ↥S).toMonoidHom with hE₁def
  set E₂ : Subgroup X := E₁.map S.subtype with hE₂def
  have hE₁ : Nat.card E₁ = p ^ 2 := by
    rw [hE₁def, Subgroup.card_map_of_injective (g⁻¹ : MulAut ↥S).injective, hE9]
  have hE₁el : CFSG.Open.IsElemAbelian p E₁ := CFSG.SectionRank.isElemAbelian_map hEel _
  have hE₂ : Nat.card E₂ = p ^ 2 := by
    rw [hE₂def, Subgroup.card_map_of_injective S.subtype_injective, hE₁]
  have hE₂el : CFSG.Open.IsElemAbelian p E₂ := CFSG.SectionRank.isElemAbelian_map hE₁el _
  have hES : E₂ ≤ S := by
    rintro _ ⟨e, -, rfl⟩
    exact e.2
  have hcomm : ∀ e ∈ E₂, z * e = e * z := by
    rintro _ ⟨e₁, he₁, rfl⟩
    obtain ⟨e, he, rfl⟩ := Subgroup.mem_map.1 he₁
    have h1 : (θ z) ((g⁻¹ : MulAut ↥S) e) = (g⁻¹ : MulAut ↥S) e := by
      rw [hθz]
      simp [MulAut.mul_apply, hEfix e he]
    have h2 := congrArg (fun a : ↥S => (a : X)) h1
    simp only [hθ, MulAut.conjNormal_apply] at h2
    calc z * ((S.subtype ((g⁻¹ : MulAut ↥S).toMonoidHom e)) : X)
        = z * (S.subtype ((g⁻¹ : MulAut ↥S).toMonoidHom e)) * z⁻¹ * z := by group
      _ = (S.subtype ((g⁻¹ : MulAut ↥S).toMonoidHom e)) * z := by
        rw [show z * (S.subtype ((g⁻¹ : MulAut ↥S).toMonoidHom e)) * z⁻¹ =
          (S.subtype ((g⁻¹ : MulAut ↥S).toMonoidHom e)) from h2]
  have h3 := three_le_pRank_of_centralizes (hp := hp) hzord hzS hES hE₂el hE₂ hcomm
  omega

end Core

end R3c18

end CFSG.Quasithin
