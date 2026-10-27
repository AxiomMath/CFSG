module

public import CFSG.LocalAnalysis.QuasithinUnique.Defs

public section

namespace CFSG.Quasithin.H13.L619

open Equiv
open scoped Pointwise

theorem exists_perm3_of_relIndex_three {X : Type*} [Group X] [Finite X] {U Q : Subgroup X}
    (hUQ : U ≤ Q) (hU : IsPGroup 2 U) (hidx : U.relIndex Q = 3)
    (hnn : ¬ Q ≤ Subgroup.normalizer (U : Set X)) :
    ∃ ρ : ↥Q →* Perm (Fin 3), Function.Surjective ρ ∧ IsPGroup 2 ρ.ker := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set S : Subgroup ↥Q := U.subgroupOf Q with hS
  have hSidx : S.index = 3 := hidx
  have hcard : Nat.card (↥Q ⧸ S) = 3 := by rw [← Subgroup.index_eq_card]; exact hSidx
  let eqv : (↥Q ⧸ S) ≃ Fin 3 := (Finite.equivFin _).trans (finCongr hcard)
  let ρ : ↥Q →* Perm (Fin 3) :=
    (eqv.permCongrHom).toMonoidHom.comp (MulAction.toPermHom ↥Q (↥Q ⧸ S))
  have hker : ρ.ker = S.normalCore := by
    rw [Subgroup.normalCore_eq_ker]
    ext x
    simp only [MonoidHom.mem_ker, ρ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.map_eq_one_iff]
  have hS2 : IsPGroup 2 S := hU.of_equiv (Subgroup.subgroupOfEquivOfLe hUQ).symm
  have hle : ρ.ker ≤ S := by rw [hker]; exact Subgroup.normalCore_le S
  refine ⟨ρ, ?_, hS2.to_le hle⟩
  have hlt : ρ.ker ≠ S := by
    intro he
    have hnorm : S.Normal := by rw [← he]; exact MonoidHom.normal_ker ρ
    apply hnn
    intro q hq
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      have := hnorm.conj_mem ⟨x, hUQ hx⟩ (Subgroup.mem_subgroupOf.mpr hx) ⟨q, hq⟩
      exact Subgroup.mem_subgroupOf.mp this
    · intro hx
      have hxQ : x ∈ Q := by
        have e : x = q⁻¹ * (q * x * q⁻¹) * q := by group
        rw [e]
        exact Q.mul_mem (Q.mul_mem (Q.inv_mem hq) (hUQ hx)) hq
      have := hnorm.conj_mem ⟨q * x * q⁻¹, hUQ hx⟩ (Subgroup.mem_subgroupOf.mpr hx) ⟨q, hq⟩⁻¹
      have e : (⟨q, hq⟩⁻¹ * ⟨q * x * q⁻¹, hUQ hx⟩ * (⟨q, hq⟩⁻¹)⁻¹ : ↥Q) = ⟨x, hxQ⟩ :=
        Subtype.ext (by simp only [Subgroup.coe_mul, Subgroup.coe_inv, inv_inv]; group)
      rw [e] at this
      exact Subgroup.mem_subgroupOf.mp this
  have h1 := Subgroup.card_ker_mul_card_range ρ
  have h2 := Subgroup.card_mul_index S
  rw [hSidx] at h2
  have h3 := Subgroup.card_mul_index (ρ.ker.subgroupOf S)
  have h4 : Nat.card ↥(ρ.ker.subgroupOf S) = Nat.card ρ.ker :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv
  rw [h4] at h3
  have hi : (ρ.ker.subgroupOf S).index ≠ 1 := by
    intro h
    rw [Subgroup.index_eq_one, Subgroup.subgroupOf_eq_top] at h
    exact hlt (le_antisymm hle h)
  have hm : (ρ.ker.subgroupOf S).index ≠ 0 := Subgroup.index_ne_zero_of_finite
  have hn : 0 < Nat.card ρ.ker := Nat.card_pos
  have hr : Nat.card ρ.range = 3 * (ρ.ker.subgroupOf S).index := by
    refine Nat.eq_of_mul_eq_mul_left hn ?_
    rw [h1, ← h2, ← h3]
    ring
  have h6 : Nat.card (Perm (Fin 3)) = 6 := by rw [Nat.card_perm, Nat.card_fin]; rfl
  have hdvd : Nat.card ρ.range ∣ 6 := h6 ▸ Subgroup.card_subgroup_dvd_card ρ.range
  have hr6 : Nat.card ρ.range = 6 := by
    have := Nat.le_of_dvd (by norm_num) hdvd
    omega
  have htop : ρ.range = ⊤ := Subgroup.eq_top_of_card_eq _ (by rw [hr6, h6])
  exact MonoidHom.range_eq_top.mp htop

@[expose] def r4 : Perm (Fin 5) := swap 0 1 * swap 1 2 * swap 2 3

@[expose] def d8List : List (Perm (Fin 5)) :=
  [1, r4, r4 ^ 2, r4 ^ 3, swap 0 2, r4 * swap 0 2, r4 ^ 2 * swap 0 2, r4 ^ 3 * swap 0 2]

theorem d8List_one : (1 : Perm (Fin 5)) ∈ d8List := by decide

theorem d8List_mul : ∀ a ∈ d8List, ∀ b ∈ d8List, a * b ∈ d8List := by decide +kernel

theorem d8List_inv : ∀ a ∈ d8List, a⁻¹ ∈ d8List := by decide +kernel

@[expose] def d8 : Subgroup (Perm (Fin 5)) where
  carrier := {σ | σ ∈ d8List}
  one_mem' := d8List_one
  mul_mem' ha hb := d8List_mul _ ha _ hb
  inv_mem' ha := d8List_inv _ ha

theorem mem_d8 {σ : Perm (Fin 5)} : σ ∈ d8 ↔ σ ∈ d8List := Iff.rfl

theorem card_d8 : Nat.card d8 = 8 := by
  have e : (d8 : Set (Perm (Fin 5))) = ↑d8List.toFinset := by
    ext σ
    simp [mem_d8]
  rw [← SetLike.coe_sort_coe, e, Nat.card_coe_set_eq, Set.ncard_coe_finset]
  decide

@[expose] def stab4 : Subgroup (Perm (Fin 5)) := MulAction.stabilizer (Perm (Fin 5)) (4 : Fin 5)

theorem mem_stab4 {σ : Perm (Fin 5)} : σ ∈ stab4 ↔ σ 4 = 4 := by
  rw [stab4, MulAction.mem_stabilizer_iff, Perm.smul_def]

theorem card_perm_five : Nat.card (Perm (Fin 5)) = 120 := by
  rw [Nat.card_perm, Nat.card_fin]
  rfl

theorem card_stab4 : Nat.card stab4 = 24 := by
  have h := Subgroup.card_mul_index stab4
  rw [stab4, MulAction.index_stabilizer_of_transitive, card_perm_five, Nat.card_fin] at h
  rw [stab4]
  omega

theorem d8_le_stab4 : d8 ≤ stab4 := fun σ hσ => by
  rw [mem_stab4]
  revert σ
  show ∀ σ ∈ d8List, σ 4 = 4
  decide +kernel

theorem isSylowTwoOf_d8 : CFSG.QuasithinUnique.IsSylowTwoOf d8 ⊤ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine ⟨le_top, IsPGroup.of_card (n := 3) (by rw [card_d8]; norm_num), ?_⟩
  rw [show (d8.subgroupOf ⊤).index = d8.index from Subgroup.relIndex_top_right d8]
  have h := Subgroup.card_mul_index d8
  rw [card_d8, card_perm_five] at h
  have : d8.index = 15 := by omega
  rw [this]
  decide

theorem r4_mem_d8 : r4 ∈ d8 := by rw [mem_d8]; decide

theorem swap02_mem_d8 : swap (0 : Fin 5) 2 ∈ d8 := by rw [mem_d8]; decide

theorem swap13_mem_d8 : swap (1 : Fin 5) 3 ∈ d8 := by rw [mem_d8]; decide

theorem swap_aux : ∀ σ : Perm (Fin 5), σ 4 ≠ 4 → ∃ x : Fin 5, x ≠ 4 ∧
    (σ * swap 0 2 * σ⁻¹ = swap 4 x ∨ σ * swap 1 3 * σ⁻¹ = swap 4 x) := by decide +kernel

theorem swap40_aux : ∀ x : Fin 5, x ≠ 4 → ∃ k : Fin 4,
    r4 ^ (k : ℕ) * swap 4 x * (r4 ^ (k : ℕ))⁻¹ = swap 4 0 := by decide +kernel

theorem swap4_aux : ∀ y : Fin 5, y ≠ 4 → ∃ k : Fin 4,
    r4 ^ (k : ℕ) * swap 4 0 * (r4 ^ (k : ℕ))⁻¹ = swap 4 y := by decide +kernel

theorem swap_eq_aux : ∀ a b : Fin 5, a ≠ b → a ≠ 4 → b ≠ 4 →
    swap a b = swap 4 a * swap 4 b * swap 4 a := by decide +kernel

theorem le_stab4_or_eq_top {R : Subgroup (Perm (Fin 5))} (hR : d8 ≤ R) :
    R ≤ stab4 ∨ R = ⊤ := by
  by_cases h : R ≤ stab4
  · exact Or.inl h
  · right
    obtain ⟨σ, hσR, hσ⟩ := Set.not_subset.mp h
    rw [SetLike.mem_coe, mem_stab4] at hσ
    obtain ⟨x, hx4, hx⟩ := swap_aux σ hσ
    have hxR : swap 4 x ∈ R := by
      rcases hx with hx | hx
      · rw [← hx]
        exact R.mul_mem (R.mul_mem hσR (hR swap02_mem_d8)) (R.inv_mem hσR)
      · rw [← hx]
        exact R.mul_mem (R.mul_mem hσR (hR swap13_mem_d8)) (R.inv_mem hσR)
    have hr : r4 ∈ R := hR r4_mem_d8
    have hconj : ∀ (k : ℕ) {τ : Perm (Fin 5)}, τ ∈ R → r4 ^ k * τ * (r4 ^ k)⁻¹ ∈ R :=
      fun k τ hτ => R.mul_mem (R.mul_mem (R.pow_mem hr k) hτ) (R.inv_mem (R.pow_mem hr k))
    obtain ⟨k, hk⟩ := swap40_aux x hx4
    have h40 : swap 4 0 ∈ R := hk ▸ hconj k hxR
    have hall : ∀ y : Fin 5, y ≠ 4 → swap 4 y ∈ R := fun y hy => by
      obtain ⟨j, hj⟩ := swap4_aux y hy
      exact hj ▸ hconj j h40
    rw [eq_top_iff, ← Perm.closure_isSwap, Subgroup.closure_le]
    rintro τ ⟨a, b, hab, rfl⟩
    by_cases ha : a = 4
    · subst ha
      exact hall b (Ne.symm hab)
    by_cases hb : b = 4
    · subst hb
      rw [swap_comm]
      exact hall a ha
    rw [SetLike.mem_coe, swap_eq_aux a b hab ha hb]
    exact R.mul_mem (R.mul_mem (hall a ha) (hall b hb)) (hall a ha)

theorem swap01_conj_not_mem : swap (0 : Fin 5) 1 * swap 0 2 * (swap 0 1)⁻¹ ∉ d8 := by
  rw [mem_d8]
  decide

theorem eq_bot_of_normal_two_perm5 {N : Subgroup (Perm (Fin 5))} [N.Normal]
    (hN : IsPGroup 2 N) : N = ⊥ := by
  by_contra hne
  have : Nontrivial N := (Subgroup.nontrivial_iff_ne_bot N).mpr hne
  have hle := Perm.alternatingGroup_le_of_normal (by simp) this
  have h60 : Nat.card (alternatingGroup (Fin 5)) = 60 := by
    rw [Nat.card_eq_fintype_card, card_alternatingGroup, Fintype.card_fin]
    rfl
  have hdvd : 60 ∣ Nat.card N := h60 ▸ Subgroup.card_dvd_of_le hle
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card).mp hN
  rw [hk] at hdvd
  have h3 : 3 ∣ 2 ^ k := (show 3 ∣ 60 by norm_num).trans hdvd
  have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3
  omega

theorem center_aux : ∀ σ : Perm (Fin 5), σ * swap 0 1 = swap 0 1 * σ →
    σ * swap 1 2 = swap 1 2 * σ → σ * swap 2 3 = swap 2 3 * σ → σ * swap 3 4 = swap 3 4 * σ →
    σ = 1 := by decide +kernel

theorem center_perm5 : Subgroup.center (Perm (Fin 5)) = ⊥ := by
  rw [eq_bot_iff]
  intro σ hσ
  rw [Subgroup.mem_center_iff] at hσ
  exact center_aux σ (hσ _).symm (hσ _).symm (hσ _).symm (hσ _).symm

theorem s5_parabolics_of {X : Type*} [Group X] [Finite X] (f : X ≃* Perm (Fin 5))
    {U : Subgroup X} (hmem : ∀ x, x ∈ U ↔ f x ∈ d8) :
    ∃ Q : Subgroup X, U ≤ Q ∧ (∀ R : Subgroup X, U ≤ R → R ≤ Q ∨ R = ⊤) ∧
      ∃ ρ : ↥Q →* Perm (Fin 3), Function.Surjective ρ ∧ IsPGroup 2 ρ.ker := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Q := stab4.comap f.toMonoidHom with hQ
  have hUQ : U ≤ Q := fun x hx => d8_le_stab4 ((hmem x).mp hx)
  refine ⟨Q, hUQ, fun R hR => ?_, ?_⟩
  · have hR' : d8 ≤ R.map f.toMonoidHom := by
      intro σ hσ
      refine ⟨f.symm σ, hR ((hmem _).mpr (by simpa using hσ)), by simp⟩
    rcases le_stab4_or_eq_top hR' with h | h
    · left
      intro x hx
      exact h ⟨x, hx, rfl⟩
    · right
      rw [eq_top_iff]
      intro x _
      have : f x ∈ R.map f.toMonoidHom := h ▸ Subgroup.mem_top _
      obtain ⟨y, hy, hyx⟩ := this
      rw [show y = x from f.injective hyx] at hy
      exact hy
  ·
    have hUm : U.map f.toMonoidHom = d8 := by
      ext σ
      constructor
      · rintro ⟨x, hx, rfl⟩
        exact (hmem x).mp hx
      · intro hσ
        exact ⟨f.symm σ, (hmem _).mpr (by simpa using hσ), by simp⟩
    have hQm : Q.map f.toMonoidHom = stab4 := by
      ext σ
      constructor
      · rintro ⟨x, hx, rfl⟩
        exact hx
      · intro hσ
        exact ⟨f.symm σ, show f (f.symm σ) ∈ stab4 by simpa using hσ, by simp⟩
    have hcU : Nat.card U = 8 := by
      rw [← card_d8, ← hUm, Subgroup.card_map_of_injective f.injective]
    have hcQ : Nat.card Q = 24 := by
      rw [← card_stab4, ← hQm, Subgroup.card_map_of_injective f.injective]
    refine exists_perm3_of_relIndex_three hUQ (IsPGroup.of_card (n := 3) (by rw [hcU]; norm_num))
      ?_ ?_
    · have h := Subgroup.relIndex_mul_card U Q
      rw [inf_of_le_left hUQ, hcU, hcQ] at h
      omega
    · intro hle
      have hx : f.symm (swap 0 1) ∈ Q := by
        show f (f.symm (swap 0 1)) ∈ stab4
        rw [MulEquiv.apply_symm_apply, mem_stab4]
        decide
      have hu : f.symm (swap 0 2) ∈ U := (hmem _).mpr (by simpa using swap02_mem_d8)
      have := (Subgroup.mem_normalizer_iff.mp (hle hx) _).mp hu
      rw [hmem, map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply,
        MulEquiv.apply_symm_apply] at this
      exact swap01_conj_not_mem this

theorem s5_parabolics {X : Type*} [Group X] [Finite X] (e : X ≃* Perm (Fin 5)) {U : Subgroup X}
    (hU : CFSG.QuasithinUnique.IsSylowTwoOf U ⊤) :
    ∃ Q : Subgroup X, U ≤ Q ∧ (∀ R : Subgroup X, U ≤ R → R ≤ Q ∨ R = ⊤) ∧
      ∃ ρ : ↥Q →* Perm (Fin 3), Function.Surjective ρ ∧ IsPGroup 2 ρ.ker := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hU2 : IsPGroup 2 (U.map e.toMonoidHom) := hU.2.1.map _
  have hidx : ¬ 2 ∣ (U.map e.toMonoidHom).index := by
    rw [MulEquiv.toMonoidHom_eq_coe, Subgroup.index_map_equiv]
    have := hU.2.2
    rwa [show (U.subgroupOf ⊤).index = U.index from Subgroup.relIndex_top_right U] at this
  have hd2 : IsPGroup 2 d8 := isSylowTwoOf_d8.2.1
  have hdidx : ¬ 2 ∣ d8.index := by
    have := isSylowTwoOf_d8.2.2
    rwa [show (d8.subgroupOf ⊤).index = d8.index from Subgroup.relIndex_top_right d8] at this
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (Perm (Fin 5)) (hd2.toSylow hdidx)
    (hU2.toSylow hidx)
  have hg' : U.map e.toMonoidHom = MulAut.conj g • d8 := by
    have := congrArg (fun P : Sylow 2 (Perm (Fin 5)) => (P : Subgroup (Perm (Fin 5)))) hg
    simp only [Sylow.coe_subgroup_smul, IsPGroup.toSylow_coe] at this
    exact this.symm
  refine s5_parabolics_of (e.trans (MulAut.conj g⁻¹)) fun x => ?_
  have h1 : x ∈ U ↔ e x ∈ U.map e.toMonoidHom := by
    rw [Subgroup.mem_map_equiv, MulEquiv.symm_apply_apply]
  rw [h1, hg', Subgroup.mem_pointwise_smul_iff_inv_smul_mem, MulAut.smul_def,
    MulAut.conj_inv_apply]
  simp

end CFSG.Quasithin.H13.L619
