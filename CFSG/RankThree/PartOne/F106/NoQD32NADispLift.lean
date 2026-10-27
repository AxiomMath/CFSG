module

public import CFSG.RankThree.PartOne.N143X.WeylMatrix

public section

namespace CFSG.RankThree.PartOne.F106

open Subgroup CFSG CFSG.Assembly.LowTwoRank CFSG.RankThree.PartOne.N143X
open scoped commutatorElement

section Center

theorem card_quotient_center_congr {G H : Type*} [Group G] [Group H] (e : G ≃* H) :
    Nat.card (G ⧸ center G) = Nat.card (H ⧸ center H) := by
  have hc : (center G).map e.toMonoidHom = center H := by
    refine le_antisymm ?_ ?_
    · rintro _ ⟨z, hz, rfl⟩
      refine mem_center_iff.2 fun h => ?_
      obtain ⟨g, rfl⟩ := e.surjective h
      simp only [MulEquiv.coe_toMonoidHom, ← map_mul, mem_center_iff.1 hz g]
    · intro w hw
      refine ⟨e.symm w, mem_center_iff.2 fun g => ?_, e.apply_symm_apply w⟩
      apply e.injective
      rw [map_mul, map_mul, e.apply_symm_apply]
      exact mem_center_iff.1 hw (e g)
  rw [← index_eq_card, ← index_eq_card, ← hc]
  exact (index_map_of_bijective e.bijective _).symm

theorem card_quotient_center_le_of_surjective {G H : Type*} [Group G] [Group H] [Finite G]
    (f : G →* H) (hf : Function.Surjective f) :
    Nat.card (H ⧸ center H) ≤ Nat.card (G ⧸ center G) := by
  have hle : (center G).map f ≤ center H := by
    rintro _ ⟨z, hz, rfl⟩
    refine mem_center_iff.2 fun h => ?_
    obtain ⟨g, rfl⟩ := hf h
    rw [← map_mul, ← map_mul, mem_center_iff.1 hz g]
  have h1 : (center H).index ∣ ((center G).map f).index := index_dvd_of_le hle
  have h2 : ((center G).map f).index ∣ (center G).index := index_map_dvd _ hf
  rw [← index_eq_card, ← index_eq_card]
  exact Nat.le_of_dvd (Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite) (h1.trans h2)

theorem pow_five_dvd_card {q : ℕ} (hq : q.Prime) {F : Type*} [Group F] [Finite F]
    (hF : ∀ x : F, x ^ q = 1) (h4 : q ^ 4 ≤ Nat.card (F ⧸ center F)) : q ^ 5 ∣ Nat.card F := by
  have : Fact q.Prime := ⟨hq⟩
  have hp : IsPGroup q F := fun x => ⟨1, by simpa using hF x⟩
  have hq4 : 1 < q ^ 4 := Nat.one_lt_pow (by norm_num) hq.one_lt
  have : Nontrivial F := by
    rw [← not_subsingleton_iff_nontrivial]
    intro hs
    have : Nat.card (F ⧸ center F) = 1 := Nat.card_unique
    omega
  have hz : Nontrivial (center F) := hp.center_nontrivial
  have hz2 : 1 < Nat.card (center F) := Finite.one_lt_card
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card).mp hp
  have hmul := Subgroup.card_eq_card_quotient_mul_card_subgroup (center F)
  have hlt : q ^ 4 < q ^ k := by
    rw [← hk, hmul]
    nlinarith
  have hk5 : 5 ≤ k := by
    by_contra hk5
    have := Nat.pow_le_pow_right hq.pos (by omega : k ≤ 4)
    omega
  rw [hk]
  exact pow_dvd_pow q hk5

end Center

section Transport

variable {G H : Type*} [Group G] [Group H]

theorem pow_eq_one_of_equiv (ε : G ≃* H) {q : ℕ} (h : ∀ y : H, y ^ q = 1) (x : G) :
    x ^ q = 1 := by
  apply ε.injective
  rw [map_pow, h, map_one]

theorem commutator_eq_one_of_equiv (ε : G ≃* H) (h : ∀ a b c : H, ⁅⁅a, b⁆, c⁆ = 1) (a b c : G) :
    ⁅⁅a, b⁆, c⁆ = 1 := by
  apply ε.injective
  rw [map_commutatorElement, map_commutatorElement, h, map_one]

theorem subgroup_data {T : Type*} [Group T] {Y : Subgroup T} {q : ℕ}
    (hexp : ∀ y ∈ Y, y ^ q = 1) (hcl : ∀ a ∈ Y, ∀ b ∈ Y, ∀ c ∈ Y, ⁅⁅a, b⁆, c⁆ = 1) :
    (∀ y : ↥Y, y ^ q = 1) ∧ (∀ a b c : ↥Y, ⁅⁅a, b⁆, c⁆ = 1) := by
  refine ⟨fun y => Subtype.ext (by simpa using hexp y y.2), fun a b c => Subtype.ext ?_⟩
  simpa [commutatorElement_def] using hcl a a.2 b b.2 c c.2

theorem data_of_subgroup {T : Type*} [Group T] {F : Subgroup T} {q : ℕ}
    (hexp : ∀ y : ↥F, y ^ q = 1) (hcl : ∀ a b c : ↥F, ⁅⁅a, b⁆, c⁆ = 1) :
    (∀ y ∈ F, y ^ q = 1) ∧ (∀ a ∈ F, ∀ b ∈ F, ∀ c ∈ F, ⁅⁅a, b⁆, c⁆ = 1) := by
  refine ⟨fun y hy => ?_, fun a ha b hb c hc => ?_⟩
  · simpa using congrArg Subtype.val (hexp ⟨y, hy⟩)
  · simpa [commutatorElement_def] using congrArg Subtype.val (hcl ⟨a, ha⟩ ⟨b, hb⟩ ⟨c, hc⟩)

end Transport

section Lift

theorem exists_lift_nonab {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K] [Finite K]
    (M : Subgroup (GL ι K)) {T : Type} [Group T] (e : T ≃* StatedProj M) {q : ℕ} (hq : q.Prime)
    {d : ℕ} (hd : ∀ c : Kˣ, Matrix.GeneralLinearGroup.scalar ι c ∈ M → c ^ d = 1)
    (hqd : ¬ q ∣ d) {Y : Subgroup T} (hexp : ∀ y ∈ Y, y ^ q = 1)
    (hcl : ∀ a ∈ Y, ∀ b ∈ Y, ∀ c ∈ Y, ⁅⁅a, b⁆, c⁆ = 1) :
    ∃ F : Subgroup (GL ι K), F ≤ M ∧ (∀ x ∈ F, x ^ q = 1) ∧
      (∀ a ∈ F, ∀ b ∈ F, ∀ c ∈ F, ⁅⁅a, b⁆, c⁆ = 1) ∧
      Nat.card (↥F ⧸ center ↥F) = Nat.card (↥Y ⧸ center ↥Y) := by
  classical
  have : Fact q.Prime := ⟨hq⟩
  let N : Subgroup M := (StatedScalars ι K).subgroupOf M
  let π : M →* T := e.symm.toMonoidHom.comp (QuotientGroup.mk' N)
  have hπ : Function.Surjective π :=
    e.symm.surjective.comp (QuotientGroup.mk'_surjective N)
  have hπker : π.ker = N := by
    ext x
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.map_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  have hker : π.ker ≤ Subgroup.center M := by
    rw [hπker]
    intro x hx
    obtain ⟨c, hc⟩ := Subgroup.mem_subgroupOf.1 hx
    have hcen : Matrix.GeneralLinearGroup.scalar ι c ∈ Subgroup.center (GL ι K) := by
      rw [Matrix.GeneralLinearGroup.center_eq_range_scalar]
      exact ⟨c, rfl⟩
    rw [Subgroup.mem_center_iff]
    intro y
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, ← hc]
    exact Subgroup.mem_center_iff.1 hcen (y : GL ι K)
  have hpk : ¬ q ∣ Nat.card π.ker := by
    rw [hπker]
    exact not_dvd_card_scalarKernel' M hq hqd hd
  have hYp : IsPGroup q Y := fun y => ⟨1, Subtype.ext (by simpa using hexp y y.2)⟩
  obtain ⟨F₀, -, hF₀map, hF₀inj, -⟩ := exists_pSubgroup_lift_normalizer π hπ hker hpk hYp
  let eF : F₀ ≃* Y := (MonoidHom.ofInjective hF₀inj).trans (MulEquiv.subgroupCongr (by
    rw [MonoidHom.range_comp, Subgroup.range_subtype, hF₀map]))
  let ε : (F₀.map M.subtype) ≃* Y :=
    ((F₀.equivMapOfInjective M.subtype M.subtype_injective).symm).trans eF
  obtain ⟨hY1, hY2⟩ := subgroup_data hexp hcl
  obtain ⟨hF1, hF2⟩ := data_of_subgroup (pow_eq_one_of_equiv ε hY1)
    (commutator_eq_one_of_equiv ε hY2)
  refine ⟨F₀.map M.subtype, ?_, hF1, hF2, card_quotient_center_congr ε⟩
  rintro _ ⟨x, -, rfl⟩
  exact x.2

theorem exists_embed_nonab {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K] {T : Type}
    [Group T] (ψ : T →* GL ι K) (hψ : Function.Injective ψ) {q : ℕ} {Y : Subgroup T}
    (hexp : ∀ y ∈ Y, y ^ q = 1) (hcl : ∀ a ∈ Y, ∀ b ∈ Y, ∀ c ∈ Y, ⁅⁅a, b⁆, c⁆ = 1) :
    ∃ F : Subgroup (GL ι K), (∀ x ∈ F, x ^ q = 1) ∧
      (∀ a ∈ F, ∀ b ∈ F, ∀ c ∈ F, ⁅⁅a, b⁆, c⁆ = 1) ∧
      Nat.card (↥F ⧸ center ↥F) = Nat.card (↥Y ⧸ center ↥Y) := by
  let ε : (Y.map ψ) ≃* Y := (Y.equivMapOfInjective ψ hψ).symm
  obtain ⟨hY1, hY2⟩ := subgroup_data hexp hcl
  obtain ⟨hF1, hF2⟩ := data_of_subgroup (pow_eq_one_of_equiv ε hY1)
    (commutator_eq_one_of_equiv ε hY2)
  exact ⟨Y.map ψ, hF1, hF2, card_quotient_center_congr ε⟩

end Lift

end CFSG.RankThree.PartOne.F106
