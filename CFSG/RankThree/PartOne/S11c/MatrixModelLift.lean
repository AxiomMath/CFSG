module

public import CFSG.RankThree.PartOne.S11c.PlaneLift

public section

namespace CFSG.RankThree.PartOne

open CFSG CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.OuterAutomorphisms (inner Outer)

theorem center_eq_bot_of_isQuasisimple {X : Type*} [Group X] (hX : CFSG.IsQuasisimple X) :
    Subgroup.center (X ⧸ Subgroup.center X) = ⊥ := by
  obtain ⟨-, hsimple, a, b, hab⟩ := hX
  rcases hsimple.eq_bot_or_eq_top_of_normal (Subgroup.center (X ⧸ Subgroup.center X)) with h | h
  · exact h
  · exact absurd ((Subgroup.mem_center_iff.1 (h ▸ Subgroup.mem_top b)) a) hab

theorem le_inner_of_not_dvd_outer {T : Type} [Group T] [Finite T] {p : ℕ} (hp : p.Prime)
    {m : ℕ} (hout : Nat.card (Outer T) ∣ m) (hpm : ¬ p ∣ m) {E : Subgroup (MulAut T)}
    (hE : IsPGroup p E) : E ≤ inner T := by
  intro β hβ
  obtain ⟨k, hk⟩ := hE ⟨β, hβ⟩
  have hβk : β ^ p ^ k = 1 := congrArg Subtype.val hk
  set π := QuotientGroup.mk' (inner T)
  have h1 : orderOf (π β) ∣ p ^ k := orderOf_dvd_of_pow_eq_one (by rw [← map_pow, hβk, map_one])
  have h2 : orderOf (π β) ∣ m := (orderOf_dvd_natCard (π β)).trans hout
  have hcop : Nat.Coprime (p ^ k) m :=
    Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd hp).2 hpm)
  have h3 : orderOf (π β) = 1 := (Nat.Coprime.coprime_dvd_left h1 hcop).eq_one_of_dvd h2
  rw [orderOf_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h3
  exact h3

theorem not_dvd_card_scalarKernel {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]
    (M : Subgroup (GL ι K)) [Finite M] {d p : ℕ} (hp : p.Prime) (hpd : ¬ p ∣ d)
    (hd : ∀ c : Kˣ, Matrix.GeneralLinearGroup.scalar ι c ∈ M → c ^ d = 1) :
    ¬ p ∣ Nat.card ((StatedScalars ι K).subgroupOf M) :=
  CFSG.Open.StatedAPI.not_dvd_card_statedScalars_subgroupOf M hp hpd hd

theorem planeCentralizes_of_matrix_model {T : Type} [Group T] [Finite T]
    (hZ : Subgroup.center T = ⊥) {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]
    [Finite K] (M : Subgroup (GL ι K)) (e : T ≃* StatedProj M) {p : ℕ}
    {E : Subgroup (MulAut T)} {U : Subgroup T} (hplane : PlaneOn p E U)
    (hE : E ≤ (MulAut.conj : T →* MulAut T).range) {d : ℕ}
    (hd : ∀ c : Kˣ, Matrix.GeneralLinearGroup.scalar ι c ∈ M → c ^ d = 1) (hpd : ¬ p ∣ d)
    (hmat : ∀ F V : Subgroup (GL ι K), F ≤ M → IsElementaryAbelian p F →
      Nat.card F = p ^ 2 → IsPGroup 2 V → F ≤ Subgroup.normalizer (V : Set (GL ι K)) →
        ∀ x ∈ F, ∀ u ∈ V, x * u = u * x) :
    PlaneCentralizes E U := by
  classical
  have hp := hplane.prime
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
    exact not_dvd_card_scalarKernel M hp hpd hd
  refine planeCentralizes_of_central_lift hZ hplane hE π hπ hker hpk ?_
  intro F' U' hF'el hF'card hU'2 hnorm
  have hF''el : IsElementaryAbelian p (F'.map M.subtype) :=
    IsElementaryAbelian.map_subtype (H := F')
  have hF''card : Nat.card (F'.map M.subtype) = p ^ 2 := by
    rw [Subgroup.card_map_of_injective M.subtype_injective]
    exact hF'card
  have hU''2 : IsPGroup 2 (U'.map M.subtype) := hU'2.map M.subtype
  have hnorm' : F'.map M.subtype ≤ Subgroup.normalizer ((U'.map M.subtype : Subgroup (GL ι K)) :
      Set (GL ι K)) := by
    rintro _ ⟨x, hx, rfl⟩
    rw [Subgroup.mem_normalizer_iff]
    intro w
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact ⟨x * u * x⁻¹, hnorm x hx u hu, by simp⟩
    · rintro ⟨u, hu, hwu⟩
      refine ⟨x⁻¹ * u * x, ?_, ?_⟩
      · simpa using hnorm x⁻¹ (F'.inv_mem hx) u hu
      · have h1 : (x : GL ι K) * w * (x : GL ι K)⁻¹ = u := hwu.symm
        have h2 : w = (x : GL ι K)⁻¹ * u * x := by rw [← h1]; group
        simp [h2]
  intro x hx u hu
  have := hmat (F'.map M.subtype) (U'.map M.subtype) (by rintro _ ⟨y, -, rfl⟩; exact y.2) hF''el
    hF''card hU''2 hnorm' x ⟨x, hx, rfl⟩ u ⟨u, hu, rfl⟩
  exact Subtype.ext this

end CFSG.RankThree.PartOne
