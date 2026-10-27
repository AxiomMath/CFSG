module

public import CFSG.Quasithin.EmptyFaithful.SzN31SmallStmt
public import CFSG.Quasithin.EmptyFaithful.SzN31Basic

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.SzN31

open CFSG.Quasithin.G11

namespace SmD2

theorem card_nonzero_of_card_four {V : Type} [AddCommGroup V] [Finite V] (h : Nat.card V = 4) :
    Nat.card {v : V // v ≠ 0} = 3 := by
  have h1 : Nat.card {v : V // v ≠ 0} = (({0} : Set V)ᶜ).ncard := by
    rw [← Nat.card_coe_set_eq]
    rfl
  rw [h1, Set.ncard_compl, Set.ncard_singleton, h]

section Action

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V]

@[expose] def permNonzero (g : GLV V) : Equiv.Perm {v : V // v ≠ 0} :=
  Equiv.subtypeEquiv g.toEquiv fun v => by simp

variable (V) in
@[expose] def permNonzeroHom : GLV V →* Equiv.Perm {v : V // v ≠ 0} where
  toFun := permNonzero
  map_one' := by
    ext v
    rfl
  map_mul' g h := by
    ext v
    rfl

theorem permNonzeroHom_injective : Function.Injective (permNonzeroHom V) := by
  rw [injective_iff_map_eq_one]
  intro g hg
  ext v
  by_cases hv : v = 0
  · simp [hv]
  · have := congrArg
      (fun σ : Equiv.Perm {v : V // v ≠ 0} => ((σ ⟨v, hv⟩ : {v : V // v ≠ 0}) : V)) hg
    simpa [permNonzeroHom, permNonzero] using this

end Action

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]

theorem not_isPGroup_two_of_isIrr {Γ : Subgroup (GLV V)} (hirr : IsIrr Γ ⊤)
    (hd : 2 ≤ Module.finrank (ZMod 2) V) : ¬ IsPGroup 2 ↥Γ := by
  intro hP
  have : Nontrivial V := Module.nontrivial_of_finrank_pos (R := ZMod 2) (by omega)
  obtain ⟨v, hv0, hv⟩ := exists_ne_zero_fixed_of_isPGroup hP
  have hinv : Invariant Γ (Submodule.span (ZMod 2) {v}) := by
    intro k hk u hu
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hu
    rw [map_smul, hv k hk]
    exact Submodule.smul_mem _ c (Submodule.mem_span_singleton_self v)
  rcases hirr.eq_bot_or_eq hinv le_top with h | h
  · have hv' : v ∈ (⊥ : Submodule (ZMod 2) V) := h ▸ Submodule.mem_span_singleton_self v
    exact hv0 (by simpa using hv')
  · have h1 := finrank_span_singleton (K := ZMod 2) hv0
    rw [h, finrank_top] at h1
    omega

end SmD2

open SmD2

theorem smallCase2 : SmallCase 2 := by
  intro V _ _ _ Γ A m hyp _ _ _ hd
  have hV : Nat.card V = 4 := by
    have : Module.Finite (ZMod 2) V := Module.Finite.of_finite
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod, hd]
    norm_num
  have hN : Nat.card {v : V // v ≠ 0} = 3 := card_nonzero_of_card_four hV
  set φ : ↥Γ →* Equiv.Perm {v : V // v ≠ 0} := (permNonzeroHom V).comp Γ.subtype with hφdef
  have hφ : Function.Injective φ := permNonzeroHom_injective.comp Γ.subtype_injective
  have hperm : Nat.card (Equiv.Perm {v : V // v ≠ 0}) = 6 := by
    rw [Nat.card_perm, hN]
    rfl
  have hdvd : Nat.card ↥Γ ∣ 6 := hperm ▸ Subgroup.card_dvd_of_injective φ hφ
  have hA : Nat.card A ∣ Nat.card ↥Γ := Subgroup.card_dvd_of_le hyp.A_le
  rw [hyp.A_card] at hA
  have h2 : 2 ∣ Nat.card ↥Γ := (dvd_pow_self 2 (by have := hyp.A_ne; omega)).trans hA
  have hne2 : Nat.card ↥Γ ≠ 2 := by
    intro h
    exact not_isPGroup_two_of_isIrr hyp.irreducible (by omega)
      (IsPGroup.of_card (n := 1) (by rw [h]; rfl))
  have h6 : Nat.card ↥Γ = 6 := by
    have hle : Nat.card ↥Γ ≤ 6 := Nat.le_of_dvd (by norm_num) hdvd
    have hpos : 0 < Nat.card ↥Γ := Nat.card_pos
    generalize Nat.card ↥Γ = n at *
    interval_cases n <;> omega
  have hm1 : m = 1 := by
    by_contra hne
    have hm2 : 2 ≤ m := by have := hyp.A_ne; omega
    have h4 : 2 ^ 2 ∣ 2 ^ m := pow_dvd_pow 2 hm2
    have h46 : 2 ^ 2 ∣ 6 := (h4.trans hA).trans hdvd
    norm_num at h46
  have hbij : Function.Bijective φ := hφ.bijective_of_nat_card_le (by rw [h6, hperm])
  exact Or.inl ⟨hm1, hd, ⟨(MulEquiv.ofBijective φ hbij).trans
    (Finite.equivFinOfCardEq hN).permCongrHom⟩⟩

end CFSG.Quasithin.SzN31
