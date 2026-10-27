module

public import Mathlib.GroupTheory.PGroup

public section

namespace CFSG.RankThree.PartTwo.Sec13.RonanStep131b.L3

theorem exists_conj_mem_of_isPGroup {A : Type*} [Group A] {N : Subgroup A} {p : ℕ} [Fact p.Prime]
    (hN : ¬ p ∣ N.index) {P : Subgroup A} (hP : IsPGroup p P) :
    ∃ a : A, ∀ x ∈ P, a⁻¹ * x * a ∈ N := by
  obtain ⟨q, hq⟩ := hP.nonempty_fixed_point_of_prime_not_dvd_card (A ⧸ N) hN
  induction q using QuotientGroup.induction_on with
  | H a =>
    refine ⟨a, fun x hx => ?_⟩
    have h1 : (⟨x, hx⟩ : P) • (a : A ⧸ N) = (a : A ⧸ N) := MulAction.mem_fixedPoints.mp hq ⟨x, hx⟩
    have h2 : ((x * a : A) : A ⧸ N) = (a : A ⧸ N) := h1
    have h3 := QuotientGroup.eq.mp h2.symm
    simpa [mul_assoc] using h3

theorem exists_stable_conj {H X : Type*} [Group H] [Finite H] [Group X] (φ : H →* MulAut X)
    {N : Subgroup H} (hN : ¬ 3 ∣ N.index) {P : Subgroup (MulAut X)} (hP : IsPGroup 3 P)
    (hPφ : P ≤ φ.range) :
    ∃ h : H, ∀ σ ∈ P, ∃ n ∈ N, φ h * φ n * (φ h)⁻¹ = σ := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hψ : Function.Surjective φ.rangeRestrict := φ.rangeRestrict_surjective
  have hN' : ¬ 3 ∣ (N.map φ.rangeRestrict).index := fun hd =>
    hN (hd.trans (Subgroup.index_map_dvd N hψ))
  have hP' : IsPGroup 3 (P.subgroupOf φ.range) :=
    IsPGroup.comap_of_injective hP φ.range.subtype φ.range.subtype_injective
  obtain ⟨a, ha⟩ := exists_conj_mem_of_isPGroup hN' hP'
  obtain ⟨h, rfl⟩ := hψ a
  refine ⟨h, fun σ hσ => ?_⟩
  have hmem := ha ⟨σ, hPφ hσ⟩ (Subgroup.mem_subgroupOf.mpr hσ)
  obtain ⟨n, hn, hnσ⟩ := Subgroup.mem_map.mp hmem
  refine ⟨n, hn, ?_⟩
  have h1 : φ n = (φ h)⁻¹ * σ * φ h := congrArg Subtype.val hnσ
  rw [h1]
  group

theorem exists_stable_subgroup {H X : Type*} [Group H] [Finite H] [Group X] (φ : H →* MulAut X)
    {N : Subgroup H} (hN : ¬ 3 ∣ N.index) {V₀ : Subgroup X} (hV₀ : V₀ ≠ ⊥) (hV₀2 : IsPGroup 2 V₀)
    (hstab : ∀ n ∈ N, ∀ x ∈ V₀, φ n x ∈ V₀) {P : Subgroup (MulAut X)} (hP : IsPGroup 3 P)
    (hPφ : P ≤ φ.range) :
    ∃ V : Subgroup X, V ≠ ⊥ ∧ IsPGroup 2 V ∧ ∀ σ ∈ P, V.map σ.toMonoidHom = V := by
  obtain ⟨h, hh⟩ := exists_stable_conj φ hN hP hPφ
  have hiff : ∀ n ∈ N, ∀ x, (φ n).symm x ∈ V₀ ↔ x ∈ V₀ := fun n hn x => by
    refine ⟨fun hx => ?_, fun hx => ?_⟩
    · have := hstab n hn _ hx
      simpa using this
    · have := hstab n⁻¹ (inv_mem hn) x hx
      rwa [map_inv] at this
  refine ⟨V₀.map (φ h).toMonoidHom, ?_, hV₀2.map _, fun σ hσ => ?_⟩
  · intro hbot
    exact hV₀ ((Subgroup.map_eq_bot_iff_of_injective V₀ (φ h).injective).mp hbot)
  · obtain ⟨n, hn, rfl⟩ := hh σ hσ
    ext x
    simp only [Subgroup.mem_map_equiv]
    have e : (φ h).symm ((φ h * φ n * (φ h)⁻¹).symm x) = (φ n).symm ((φ h).symm x) := by
      simp only [← MulAut.inv_def, mul_inv_rev, inv_inv, MulAut.mul_apply, MulAut.inv_apply_self]
    rw [e]
    exact hiff n hn _

theorem map_eq_of_forall_mem_iff {G : Type*} [Group G] (K : Subgroup G) (τ : G ≃* G)
    (h : ∀ x, τ x ∈ K ↔ x ∈ K) : K.map τ.toMonoidHom = K := by
  ext x
  constructor
  · intro hx
    obtain ⟨k, hk, rfl⟩ := Subgroup.mem_map.mp hx
    exact (h k).mpr hk
  · intro hx
    refine Subgroup.mem_map.mpr ⟨τ.symm x, ?_, by simp⟩
    exact (h (τ.symm x)).mp (by simpa using hx)

theorem mem_iff_of_map_eq {G : Type*} [Group G] {K : Subgroup G} {τ : G ≃* G}
    (h : K.map τ.toMonoidHom = K) (x : G) : τ x ∈ K ↔ x ∈ K := by
  constructor
  · intro hx
    rw [← h] at hx
    obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hx
    exact τ.injective hyx ▸ hy
  · intro hx
    rw [← h]
    exact Subgroup.mem_map_of_mem τ.toMonoidHom hx

theorem exists_stable_of_mulEquiv {X Y : Type*} [Group X] [Group Y] (ι : X ≃* Y)
    {P : Subgroup (MulAut X)}
    (h : ∃ V : Subgroup Y, V ≠ ⊥ ∧ IsPGroup 2 V ∧
      ∀ τ ∈ P.map (MulAut.congr ι).toMonoidHom, V.map τ.toMonoidHom = V) :
    ∃ V : Subgroup X, V ≠ ⊥ ∧ IsPGroup 2 V ∧ ∀ σ ∈ P, V.map σ.toMonoidHom = V := by
  obtain ⟨V', hV'ne, hV'2, hV'inv⟩ := h
  refine ⟨V'.comap ι.toMonoidHom, ?_, IsPGroup.comap_of_injective hV'2 ι.toMonoidHom ι.injective,
    fun σ hσ => ?_⟩
  · obtain ⟨y, hy⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hV'ne
    intro hbot
    have hmem : ι.symm (y : Y) ∈ V'.comap ι.toMonoidHom := by
      rw [Subgroup.mem_comap]
      simpa using y.2
    rw [hbot, Subgroup.mem_bot] at hmem
    apply hy
    apply Subtype.ext
    simpa using congrArg ι hmem
  · apply map_eq_of_forall_mem_iff
    intro x
    have hτ : (MulAut.congr ι) σ ∈ P.map (MulAut.congr ι).toMonoidHom :=
      Subgroup.mem_map_of_mem _ hσ
    have key := mem_iff_of_map_eq (hV'inv _ hτ) (ι x)
    have hcongr : (MulAut.congr ι) σ (ι x) = ι (σ x) := by
      simp [MulAut.congr_apply]
    rw [hcongr] at key
    rw [Subgroup.mem_comap, Subgroup.mem_comap]
    exact key

end CFSG.RankThree.PartTwo.Sec13.RonanStep131b.L3
