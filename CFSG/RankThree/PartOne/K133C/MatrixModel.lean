module

public import CFSG.RankThree.PartOne.K133C.InnerPlane
public import CFSG.RankThree.PartOne.N143X.WeylMatrix

public section

namespace CFSG.RankThree.PartOne.K133C

open CFSG CFSG.Assembly.LowTwoRank CFSG.RankThree.PartOne.N143X

theorem unit_eq_one_of_pow_two {K : Type*} [Field K] [CharP K 2] {c : Kˣ} {k : ℕ}
    (h : c ^ (2 ^ k) = 1) : c = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h1 : (c : K) ^ (2 ^ k) = 1 := by
    have := congrArg Units.val h
    simpa using this
  have h2 : ((c : K) - 1) ^ (2 ^ k) = 0 := by
    rw [sub_pow_char_pow (p := 2), h1, one_pow, sub_self]
  exact Units.ext (sub_eq_zero.1 ((pow_eq_zero_iff (pow_ne_zero k two_ne_zero)).1 h2))

theorem scalar_unit_injective {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι] {K : Type}
    [Field K] : Function.Injective (Matrix.GeneralLinearGroup.scalar ι : Kˣ →* GL ι K) := by
  intro c d h
  obtain ⟨i⟩ := ‹Nonempty ι›
  have := congrArg (fun g : GL ι K => (g : Matrix ι ι K) i i) h
  apply Units.ext
  simpa using this

theorem movingPlane_of_matrix_model {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι] {K : Type} [Field K]
    [Finite K] [CharP K 2] (M : Subgroup (GL ι K)) {T : Type} [Group T] (e : T ≃* StatedProj M)
    {p : ℕ} (hp : p.Prime) {d : ℕ}
    (hd : ∀ c : Kˣ, Matrix.GeneralLinearGroup.scalar ι c ∈ M → c ^ d = 1) (hpd : ¬ p ∣ d)
    (hM : ∀ F : Subgroup (GL ι K), F ≤ M → IsElementaryAbelian p F → Nat.card F = p ^ 2 →
      ∃ S : Subgroup (GL ι K), S ≤ M ∧ IsPGroup 2 S ∧ (∀ h ∈ F, ∀ s ∈ S, h * s * h⁻¹ ∈ S) ∧
        ∃ h ∈ F, ∃ s ∈ S, h * s * h⁻¹ ≠ s)
    {E : Subgroup T} (hE : IsElementaryAbelian p E) (hc : Nat.card E = p ^ 2) :
    MovingPlane T E := by
  classical
  have : Fact p.Prime := ⟨hp⟩
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
  have hpk : ¬ p ∣ Nat.card π.ker := by
    rw [hπker]
    exact not_dvd_card_scalarKernel' M hp hpd hd
  have hEp : IsPGroup p E := by
    have := hE
    exact IsElementaryAbelian.isPGroup p E
  have hker2 : ∀ x ∈ π.ker, ∀ k : ℕ, x ^ (2 ^ k) = 1 → x = 1 := by
    intro x hx k hxk
    rw [hπker] at hx
    obtain ⟨c, hc⟩ := Subgroup.mem_subgroupOf.1 hx
    have hck : c ^ (2 ^ k) = 1 := by
      have h1 := congrArg (fun y : M => ((y : GL ι K))) hxk
      simp only [Subgroup.coe_pow, Subgroup.coe_one] at h1
      rw [← hc, ← map_pow] at h1
      exact scalar_unit_injective (by rw [h1, map_one])
    have hc1 : c = 1 := unit_eq_one_of_pow_two hck
    apply Subtype.ext
    rw [← hc, hc1, map_one, Subgroup.coe_one]
  obtain ⟨F₀, hF₀p, hF₀map, hF₀inj, hF₀norm⟩ :=
    exists_pSubgroup_lift_normalizer π hπ hker hpk hEp
  let eF : F₀ ≃* E := (MonoidHom.ofInjective hF₀inj).trans (MulEquiv.subgroupCongr (by
    rw [MonoidHom.range_comp, Subgroup.range_subtype, hF₀map]))
  have hF₀el : IsElementaryAbelian p F₀ := isElementaryAbelian_of_equiv eF.symm hE
  have hF₀c : Nat.card F₀ = p ^ 2 := by rw [Nat.card_congr eF.toEquiv, hc]
  have hFel : IsElementaryAbelian p (F₀.map M.subtype) := IsElementaryAbelian.map_subtype
  have hFc : Nat.card (F₀.map M.subtype) = p ^ 2 := by
    rw [Subgroup.card_map_of_injective M.subtype_injective, hF₀c]
  have hFle : F₀.map M.subtype ≤ M := fun x ⟨y, _, hy⟩ => hy ▸ y.2
  obtain ⟨S, hSM, hS2, hSst, h, hh, s, hs, hmv⟩ := hM _ hFle hFel hFc
  let S₀ : Subgroup M := S.comap M.subtype
  have hS₀2 : IsPGroup 2 S₀ := by
    intro g
    obtain ⟨k, hk⟩ := hS2 ⟨(g : M), g.2⟩
    refine ⟨k, Subtype.ext (Subtype.ext ?_)⟩
    have := congrArg (fun y : S => ((y : GL ι K))) hk
    simpa using this
  refine ⟨S₀.map π, hS₀2.map π, ?_, ?_⟩
  · intro t ht u hu
    rw [← hF₀map] at ht
    obtain ⟨f, hf, rfl⟩ := Subgroup.mem_map.1 ht
    obtain ⟨s', hs', rfl⟩ := Subgroup.mem_map.1 hu
    refine Subgroup.mem_map.2 ⟨f * s' * f⁻¹, ?_, by simp⟩
    show ((f * s' * f⁻¹ : M) : GL ι K) ∈ S
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
    exact hSst _ (Subgroup.mem_map_of_mem _ hf) _ hs'
  · obtain ⟨f, hf, rfl⟩ := Subgroup.mem_map.1 hh
    have hsM : s ∈ M := hSM hs
    have hfE : π f ∈ E := by rw [← hF₀map]; exact Subgroup.mem_map_of_mem _ hf
    refine ⟨π f, hfE, π ⟨s, hsM⟩, Subgroup.mem_map_of_mem _ hs, ?_⟩
    intro heq
    set c : M := f * ⟨s, hsM⟩ * f⁻¹ * ⟨s, hsM⟩⁻¹ with hcdef
    have hcS : c ∈ S₀ := by
      show ((c : M) : GL ι K) ∈ S
      rw [hcdef, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv,
        Subgroup.coe_inv]
      exact S.mul_mem (hSst _ (Subgroup.mem_map_of_mem _ hf) _ hs) (S.inv_mem hs)
    have hcker : c ∈ π.ker := by
      rw [MonoidHom.mem_ker, hcdef, map_mul, map_mul, map_mul, map_inv, map_inv, heq]
      group
    obtain ⟨k, hk⟩ := hS₀2 ⟨c, hcS⟩
    have hk' : c ^ (2 ^ k) = 1 := congrArg Subtype.val hk
    have hc1 : c = 1 := hker2 c hcker k hk'
    apply hmv
    have h1 : f * ⟨s, hsM⟩ * f⁻¹ = ⟨s, hsM⟩ := by
      have := congrArg (fun y => y * ⟨s, hsM⟩) hc1
      simpa [hcdef, mul_assoc] using this
    have h2 := congrArg (fun y : M => ((y : GL ι K))) h1
    simpa [Subgroup.coe_mul, Subgroup.coe_inv] using h2

end CFSG.RankThree.PartOne.K133C
