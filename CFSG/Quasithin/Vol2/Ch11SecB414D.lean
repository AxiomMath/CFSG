module

public import CFSG.Quasithin.Vol2.Ch11SecB414B

public section

namespace CFSG.Quasithin.H13.Ch4.B414

open CFSG.QuasithinUnique.Setup.X7a CFSG.Semidihedral.Principal
open CFSG.QuasithinUnique.Setup.X7 (matRep matRep_apply matMap matMap_apply)
open CFSG.QuasithinUnique.Setup.X7b (toMatRep)
open scoped MatrixGroups Matrix

variable {F : Type} [Field F] [CharP F 2] {U : Type} [AddCommGroup U] [Module (ZMod 2) U]

section General

theorem addSubgroup_eq_bot_or_top {Gr : Type*} [Monoid Gr] {ρ : Representation (ZMod 2) Gr U}
    (hirr : ρ.IsIrreducible) (A : AddSubgroup U) (hA : ∀ g, ∀ u ∈ A, ρ g u ∈ A) :
    A = ⊥ ∨ A = ⊤ := by
  rcases ((CFSG.QuasithinUnique.Setup.X7.isIrreducible_iff ρ).mp hirr).2
    (AddSubgroup.toZModSubmodule 2 A) (fun g u hu => hA g u hu) with h | h
  · left
    rw [eq_bot_iff]
    intro u hu
    have h1 : u ∈ AddSubgroup.toZModSubmodule 2 A := hu
    rw [h, Submodule.mem_bot] at h1
    exact (AddSubgroup.mem_bot).mpr h1
  · right
    rw [eq_top_iff]
    intro u _
    have h1 : u ∈ AddSubgroup.toZModSubmodule 2 A := by
      rw [h]
      exact Submodule.mem_top
    exact h1

theorem eq_one_of_sub {n : ℕ} (ρ : Representation (ZMod 2) SL(3, F) U)
    (bas : Module.Basis (Fin n) (ZMod 2) U) (W₀ : Subrepresentation (matRep (PFrep ρ bas)))
    {κ : Type} [Fintype κ] [DecidableEq κ] {R : SL(3, F) →* Matrix κ κ F}
    (e₀ : W₀.toRepresentation.Equiv (matRep R)) {g : SL(3, F)} (hg : ρ g = 1) : R g = 1 := by
  have hPF : PFrep ρ bas g = 1 := by
    have h1 : toMatRep ρ bas g = 1 := by
      show LinearMap.toMatrix bas bas (ρ g) = 1
      rw [hg, LinearMap.toMatrix_one]
    rw [PFrep, matMap_apply, h1, Matrix.map_one _ (map_zero _) (map_one _)]
  have hv : ∀ v : κ → F, R g *ᵥ v = v := by
    intro v
    have h1 := Representation.IntertwiningMap.isIntertwining _ _ e₀.toIntertwiningMap g
      (e₀.symm v)
    have h2 : W₀.toRepresentation g (e₀.symm v) = e₀.symm v := by
      apply Subtype.ext
      show PFrep ρ bas g *ᵥ ((e₀.symm v : W₀.toSubmodule) : Fin n → F) = _
      rw [hPF, Matrix.one_mulVec]
    have h4 : matRep R g (e₀ (e₀.symm v)) = e₀ (e₀.symm v) := by
      have h5 : e₀ (W₀.toRepresentation g (e₀.symm v)) = e₀ (e₀.symm v) := by rw [h2]
      exact h1.symm.trans h5
    rwa [Representation.Equiv.apply_symm_apply, matRep_apply] at h4
  ext i j
  have := congrFun (hv (Pi.single j 1)) i
  simpa [Matrix.mulVec_single_one, Matrix.one_apply, Pi.single_apply, eq_comm] using this

end General

section Four

variable [Fintype F]

omit [CharP F 2] in
theorem exists_ne_zero_ne_one (hF : Fintype.card F = 4) : ∃ ω : F, ω ≠ 0 ∧ ω ≠ 1 := by
  classical
  by_contra h
  push Not at h
  have hsub : (Finset.univ : Finset F) ⊆ {0, 1} := fun c _ => by
    by_cases hc : c = 0
    · simp [hc]
    · simp [h c hc]
  have h2 := Finset.card_le_card hsub
  rw [Finset.card_univ, hF] at h2
  have h3 := Finset.card_le_two (a := (0 : F)) (b := 1)
  omega

theorem mem_four (hF : Fintype.card F = 4) {ω : F} (h0 : ω ≠ 0) (h1 : ω ≠ 1) (c : F) :
    c = 0 ∨ c = 1 ∨ c = ω ∨ c = ω + 1 := by
  classical
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  have hne : ω + 1 ≠ 0 := fun h => h1 (by linear_combination h - h2)
  have h1ω : (1 : F) ≠ ω + 1 := fun h => h0 (by linear_combination -h)
  have hωω : ω ≠ ω + 1 := fun h => one_ne_zero (α := F) (by linear_combination -h)
  by_contra hc
  push Not at hc
  obtain ⟨hc0, hc1, hcω, hcω1⟩ := hc
  have h5 : ({c, 0, 1, ω, ω + 1} : Finset F).card = 5 := by
    rw [Finset.card_insert_of_notMem (by simp [hc0, hc1, hcω, hcω1]),
      Finset.card_insert_of_notMem (by simp [h0.symm, hne.symm]),
      Finset.card_insert_of_notMem (by simp [Ne.symm h1, h1ω]),
      Finset.card_pair_eq_two_iff.mpr hωω]
  have h6 := Finset.card_le_univ ({c, 0, 1, ω, ω + 1} : Finset F)
  omega

theorem sq_eq_add_one (hF : Fintype.card F = 4) {ω : F} (h0 : ω ≠ 0) (h1 : ω ≠ 1) :
    ω * ω = ω + 1 := by
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  rcases mem_four hF h0 h1 (ω * ω) with h | h | h | h
  · exact absurd (mul_self_eq_zero.mp h) h0
  · exfalso
    have h3 : (ω + 1) * (ω + 1) = 0 := by linear_combination h + (ω + 1) * h2
    exact h1 (by linear_combination mul_self_eq_zero.mp h3 - h2)
  · exfalso
    have h3 : ω * (ω - 1) = 0 := by linear_combination h
    rcases mul_eq_zero.mp h3 with h4 | h4
    · exact h0 h4
    · exact h1 (sub_eq_zero.mp h4)
  · exact h

end Four

section Kernel

variable [Fintype F] {κ : Type} [Fintype κ] [DecidableEq κ]

theorem card_of_not_injective (hF : Fintype.card F = 4) [Finite U] [Nontrivial U]
    {ρ : Representation (ZMod 2) SL(3, F) U} {R : SL(3, F) →* Matrix κ κ F}
    (hR : (matRep R).IsIrreducible) {H : (κ → F) →+ U}
    (hH : ∀ g v, H (R g *ᵥ v) = ρ g (H v)) (hsurj : Function.Surjective H)
    (hinj : ¬ Function.Injective H) (g₀ : SL(3, F)) :
    Nat.card U = 2 ^ Fintype.card κ ∧
      Nat.card {u // ρ g₀ u = u} ^ 2 = Nat.card {v : κ → F // R g₀ *ᵥ v = v} := by
  classical
  obtain ⟨ω, hω0, hω1⟩ := exists_ne_zero_ne_one hF
  have hωω := sq_eq_add_one hF hω0 hω1
  set K := H.ker with hKdef
  have hK : ∀ g, ∀ v ∈ K, R g *ᵥ v ∈ K := fun g v hv => by
    rw [AddMonoidHom.mem_ker, hH, AddMonoidHom.mem_ker.mp hv, map_zero]
  have hKne : K ≠ ⊥ := fun h => hinj ((AddMonoidHom.ker_eq_bot_iff H).mp h)
  have hS : ∀ x ∈ K, ω • x ∈ K → x = 0 := by
    let S : Submodule F (κ → F) :=
      { carrier := {x | x ∈ K ∧ ω • x ∈ K}
        add_mem' := fun {x y} hx hy =>
          ⟨K.add_mem hx.1 hy.1, by rw [smul_add]; exact K.add_mem hx.2 hy.2⟩
        zero_mem' := ⟨K.zero_mem, by rw [smul_zero]; exact K.zero_mem⟩
        smul_mem' := by
          intro c x hx
          have hωx : ω • x ∈ K ∧ ω • (ω • x) ∈ K := ⟨hx.2, by
            rw [smul_smul, hωω, add_smul, one_smul]
            exact K.add_mem hx.2 hx.1⟩
          rcases mem_four hF hω0 hω1 c with rfl | rfl | rfl | rfl
          · rw [zero_smul]
            exact ⟨K.zero_mem, by rw [smul_zero]; exact K.zero_mem⟩
          · rw [one_smul]
            exact hx
          · exact hωx
          · rw [add_smul, one_smul]
            exact ⟨K.add_mem hωx.1 hx.1, by rw [smul_add]; exact K.add_mem hωx.2 hx.2⟩ }
    have hSR : ∀ g, ∀ x ∈ S, matRep R g x ∈ S := by
      intro g x hx
      rw [matRep_apply]
      refine ⟨hK g x hx.1, ?_⟩
      rw [← Matrix.mulVec_smul]
      exact hK g _ hx.2
    rcases ((CFSG.QuasithinUnique.Setup.X7.isIrreducible_iff _).mp hR).2 S hSR with h0 | h1
    · intro x hx hωx
      have : x ∈ S := ⟨hx, hωx⟩
      rwa [h0, Submodule.mem_bot] at this
    · exfalso
      obtain ⟨u, hu⟩ := exists_ne (0 : U)
      obtain ⟨v, rfl⟩ := hsurj u
      have : v ∈ S := by
        rw [h1]
        exact Submodule.mem_top
      exact hu (AddMonoidHom.mem_ker.mp this.1)
  let φ : K × K → (κ → F) := fun p => (p.1 : κ → F) + ω • (p.2 : κ → F)
  have hφinj : Function.Injective φ := by
    rintro ⟨k₁, k₂⟩ ⟨k₁', k₂'⟩ h
    have h0 : (k₁ : κ → F) + ω • (k₂ : κ → F) = k₁' + ω • (k₂' : κ → F) := h
    have h1 : (k₂ : κ → F) - k₂' = 0 := by
      apply hS _ (K.sub_mem k₂.2 k₂'.2)
      have : ω • ((k₂ : κ → F) - k₂') = (k₁' : κ → F) - k₁ := by
        rw [smul_sub, sub_eq_sub_iff_add_eq_add, add_comm (ω • _)]
        exact h0
      rw [this]
      exact K.sub_mem k₁'.2 k₁.2
    have h2 : (k₂ : κ → F) = k₂' := sub_eq_zero.mp h1
    rw [h2] at h0
    exact Prod.ext (Subtype.ext (add_right_cancel h0)) (Subtype.ext h2)
  have hcardT : Nat.card (κ → F) = 4 ^ Fintype.card κ := by
    rw [Nat.card_fun, Nat.card_eq_fintype_card (α := F), hF, Nat.card_eq_fintype_card]
  have h4 : (4 : ℕ) ^ Fintype.card κ = 2 ^ Fintype.card κ * 2 ^ Fintype.card κ := by
    rw [← mul_pow]
    norm_num
  have hKc : Nat.card K = 2 ^ Fintype.card κ := by
    have hK2 : Nat.card K * Nat.card K ≤ 4 ^ Fintype.card κ := by
      rw [← hcardT, ← Nat.card_prod]
      exact Nat.card_le_card_of_injective φ hφinj
    have hK1 := two_pow_le_card_of_stable hR K hK hKne
    rw [h4] at hK2
    refine le_antisymm ?_ hK1
    by_contra hlt
    push Not at hlt
    have := Nat.mul_lt_mul'' hlt hlt
    omega
  have hφsurj : Function.Surjective φ := by
    have hc : Nat.card (κ → F) ≤ Nat.card (K × K) := by
      rw [Nat.card_prod, hKc, hcardT, h4]
    exact (hφinj.bijective_of_nat_card_le hc).2
  have hU : Nat.card U = 2 ^ Fintype.card κ := by
    have h2 := AddSubgroup.card_ker_mul_card_range H
    rw [AddMonoidHom.range_eq_top.mpr hsurj, AddSubgroup.card_top, ← hKdef, hKc, hcardT,
      h4] at h2
    exact Nat.eq_of_mul_eq_mul_left (Nat.two_pow_pos _) h2
  have hRK : ∀ k : K, R g₀ *ᵥ (k : κ → F) ∈ K := fun k => hK g₀ k k.2
  let ψ : {k : K // R g₀ *ᵥ (k : κ → F) = k} × {k : K // R g₀ *ᵥ (k : κ → F) = k} →
      {v : κ → F // R g₀ *ᵥ v = v} := fun p =>
    ⟨φ (p.1.1, p.2.1), by
      show R g₀ *ᵥ ((p.1.1 : κ → F) + ω • (p.2.1 : κ → F)) = _ + ω • _
      rw [Matrix.mulVec_add, Matrix.mulVec_smul, p.1.2, p.2.2]⟩
  have hψ : Function.Bijective ψ := by
    constructor
    · rintro ⟨a₁, a₂⟩ ⟨b₁, b₂⟩ h
      have h1 := hφinj (congrArg Subtype.val h)
      simp only [Prod.mk.injEq] at h1
      exact Prod.ext (Subtype.ext h1.1) (Subtype.ext h1.2)
    · rintro ⟨v, hv⟩
      obtain ⟨⟨k₁, k₂⟩, hk⟩ := hφsurj v
      have hfix : φ (⟨_, hRK k₁⟩, ⟨_, hRK k₂⟩) = φ (k₁, k₂) := by
        show R g₀ *ᵥ (k₁ : κ → F) + ω • R g₀ *ᵥ (k₂ : κ → F) = φ (k₁, k₂)
        rw [← Matrix.mulVec_smul, ← Matrix.mulVec_add]
        exact (congrArg (R g₀ *ᵥ ·) hk).trans (hv.trans hk.symm)
      have h1 := hφinj hfix
      simp only [Prod.mk.injEq] at h1
      exact ⟨(⟨k₁, congrArg Subtype.val h1.1⟩, ⟨k₂, congrArg Subtype.val h1.2⟩),
        Subtype.ext hk⟩
  let χ : {k : K // R g₀ *ᵥ (k : κ → F) = k} → {u // ρ g₀ u = u} := fun k =>
    ⟨H (ω • (k.1 : κ → F)), by rw [← hH, Matrix.mulVec_smul, k.2]⟩
  have hχ : Function.Bijective χ := by
    constructor
    · intro a b h
      have h1 : H (ω • ((a.1 : κ → F) - b.1)) = 0 := by
        rw [smul_sub, map_sub]
        exact sub_eq_zero.mpr (congrArg Subtype.val h)
      have h2 := hS _ (K.sub_mem a.1.2 b.1.2) (AddMonoidHom.mem_ker.mpr h1)
      exact Subtype.ext (Subtype.ext (sub_eq_zero.mp h2))
    · rintro ⟨u, hu⟩
      obtain ⟨v, rfl⟩ := hsurj u
      obtain ⟨⟨k₁, k₂⟩, hk⟩ := hφsurj v
      have hHv : H v = H (ω • (k₂ : κ → F)) := by
        rw [← hk]
        show H ((k₁ : κ → F) + ω • (k₂ : κ → F)) = _
        rw [map_add, AddMonoidHom.mem_ker.mp k₁.2, zero_add]
      have hk₂ : R g₀ *ᵥ (k₂ : κ → F) = k₂ := by
        have h1 : H (ω • (R g₀ *ᵥ (k₂ : κ → F) - k₂)) = 0 := by
          rw [smul_sub, map_sub, ← Matrix.mulVec_smul, hH, ← hHv, hu, sub_self]
        exact sub_eq_zero.mp (hS _ (K.sub_mem (hRK k₂) k₂.2) (AddMonoidHom.mem_ker.mpr h1))
      exact ⟨⟨k₂, hk₂⟩, Subtype.ext hHv.symm⟩
  refine ⟨hU, ?_⟩
  rw [← Nat.card_eq_of_bijective χ hχ, ← Nat.card_eq_of_bijective ψ hψ, Nat.card_prod, sq]

end Kernel

end CFSG.Quasithin.H13.Ch4.B414
