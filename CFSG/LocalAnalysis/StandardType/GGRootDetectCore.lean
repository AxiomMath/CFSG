module

public import CFSG.LocalAnalysis.StandardType.GGHypSixTypeA

public section

namespace CFSG.StandardType

open CFSG.LieType.Universal

namespace RootDetect

section Quotient

variable {S G : Type*} [Group S] [Group G] {N : Subgroup S} [N.Normal] {ψ : S →* G}

omit [N.Normal] in
theorem mk_eq_of_psi_eq (hN : Subgroup.center S ≤ N) (hker : ψ.ker ≤ Subgroup.center S)
    {y₁ y₂ : S} (h : ψ y₁ = ψ y₂) : (y₁ : S ⧸ N) = y₂ := by
  rw [QuotientGroup.eq]
  apply hN
  apply hker
  rw [MonoidHom.mem_ker, map_mul, map_inv, h, inv_mul_cancel]

theorem exists_conj_preimage {c : G} (hc : c ∈ Subgroup.normalizer (ψ.range : Set G)) (y : S) :
    ∃ y', ψ y' = c⁻¹ * ψ y * c := by
  have h := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hc) (ψ y)).mp ⟨y, rfl⟩
  rw [inv_inv] at h
  exact h

theorem exists_quotAut [Finite S] (hN : N = Subgroup.center S)
    (hperf : ⁅(⊤ : Subgroup S), (⊤ : Subgroup S)⁆ = ⊤) (hker : ψ.ker ≤ Subgroup.center S)
    {c : G} (hc : c ∈ Subgroup.normalizer (ψ.range : Set G)) :
    ∃ α : MulAut (S ⧸ N), ∀ y y' : S, ψ y' = c⁻¹ * ψ y * c → α (y : S ⧸ N) = (y' : S ⧸ N) := by
  have hNc : Subgroup.center S ≤ N := hN.ge
  choose ρ hρ using exists_conj_preimage (ψ := ψ) hc
  have hmul : ∀ a b, ((ρ (a * b) : S) : S ⧸ N) = (ρ a : S ⧸ N) * (ρ b : S ⧸ N) := by
    intro a b
    rw [← QuotientGroup.mk_mul]
    apply mk_eq_of_psi_eq hNc hker
    rw [hρ, map_mul, map_mul, hρ, hρ]
    group
  let ρh : S →* S ⧸ N := MonoidHom.mk' (fun y => ((ρ y : S) : S ⧸ N)) hmul
  have hρh : ∀ y, ρh y = ((ρ y : S) : S ⧸ N) := fun _ => rfl
  have hrange : ∀ k ∈ ψ.range, ∃ w, k = c⁻¹ * ψ w * c := by
    intro k hk
    obtain ⟨w, hw⟩ := (Subgroup.mem_normalizer_iff.mp hc k).mp hk
    exact ⟨w, by rw [hw]; group⟩
  have hle : N ≤ ρh.ker := by
    intro z hz
    rw [hN] at hz
    rw [MonoidHom.mem_ker, hρh, QuotientGroup.eq_one_iff, hN]
    have hcomm : ∀ y, ψ y * ψ (ρ z) = ψ (ρ z) * ψ y := by
      intro y
      obtain ⟨w, hw⟩ := hrange (ψ y) ⟨y, rfl⟩
      have hzw := Subgroup.mem_center_iff.mp hz w
      rw [hw, hρ]
      calc c⁻¹ * ψ w * c * (c⁻¹ * ψ z * c) = c⁻¹ * ψ (w * z) * c := by rw [map_mul]; group
        _ = c⁻¹ * ψ (z * w) * c := by rw [hzw]
        _ = _ := by rw [map_mul]; group
    refine HypSixTypeA.mem_center_of_comm_mem_center hperf fun y => hker ?_
    rw [MonoidHom.mem_ker, map_mul, map_mul, map_mul, map_inv, map_inv, ← hcomm y]
    group
  let ρbar : S ⧸ N →* S ⧸ N := QuotientGroup.lift N ρh hle
  have hρbar : ∀ y : S, ρbar (y : S ⧸ N) = ((ρ y : S) : S ⧸ N) := fun y => by
    change QuotientGroup.lift N ρh hle (QuotientGroup.mk y) = _
    rw [QuotientGroup.lift_mk, hρh]
  have hsurj : Function.Surjective ρbar := by
    intro x
    obtain ⟨y', rfl⟩ := QuotientGroup.mk_surjective x
    obtain ⟨y, hy⟩ := (Subgroup.mem_normalizer_iff.mp hc (ψ y')).mp ⟨y', rfl⟩
    refine ⟨(y : S ⧸ N), ?_⟩
    rw [hρbar]
    apply mk_eq_of_psi_eq hNc hker
    rw [hρ, hy]
    group
  have : Finite (S ⧸ N) := Finite.of_surjective _ QuotientGroup.mk_surjective
  have hinj : Function.Injective ρbar := Finite.injective_iff_surjective.mpr hsurj
  refine ⟨MulEquiv.ofBijective ρbar ⟨hinj, hsurj⟩, fun y y' h => ?_⟩
  change ρbar (y : S ⧸ N) = _
  rw [hρbar]
  exact mk_eq_of_psi_eq hNc hker ((hρ y).trans h.symm)

theorem quotAut_pow_apply (hN : Subgroup.center S ≤ N) (hker : ψ.ker ≤ Subgroup.center S)
    {c : G} (hc : c ∈ Subgroup.normalizer (ψ.range : Set G)) {α : MulAut (S ⧸ N)}
    (hα : ∀ y y' : S, ψ y' = c⁻¹ * ψ y * c → α (y : S ⧸ N) = (y' : S ⧸ N)) :
    ∀ k : ℕ, ∀ y y' : S, ψ y' = (c ^ k)⁻¹ * ψ y * c ^ k → (α ^ k) (y : S ⧸ N) = (y' : S ⧸ N)
  | 0 => fun y y' h => by
      rw [pow_zero, MulAut.one_apply]
      exact mk_eq_of_psi_eq hN hker (by rw [h]; group)
  | k + 1 => fun y y' h => by
      obtain ⟨y'', hy''⟩ := exists_conj_preimage (Subgroup.pow_mem _ hc k) y
      rw [pow_succ', MulAut.mul_apply, quotAut_pow_apply hN hker hc hα k y y'' hy'']
      apply hα
      rw [h, hy'', pow_succ]
      group

theorem quotAut_pow_eq_one (hN : Subgroup.center S ≤ N) (hker : ψ.ker ≤ Subgroup.center S)
    {c : G} (hc : c ∈ Subgroup.normalizer (ψ.range : Set G)) {α : MulAut (S ⧸ N)}
    (hα : ∀ y y' : S, ψ y' = c⁻¹ * ψ y * c → α (y : S ⧸ N) = (y' : S ⧸ N)) {p : ℕ}
    (hcp : c ^ p ∈ Subgroup.centralizer (ψ.range : Set G)) : α ^ p = 1 := by
  ext x
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective x
  rw [MulAut.one_apply]
  apply quotAut_pow_apply hN hker hc hα p y y
  have hcomm := Subgroup.mem_centralizer_iff.mp hcp (ψ y) ⟨y, rfl⟩
  rw [mul_assoc, hcomm, inv_mul_cancel_left]

theorem centralizes_of_quotAut_conj (hN : N = Subgroup.center S)
    (hperf : ⁅(⊤ : Subgroup S), (⊤ : Subgroup S)⁆ = ⊤) {c : G} (hc : c ∈ Subgroup.normalizer (ψ.range : Set G)) {α : MulAut (S ⧸ N)}
    (hα : ∀ y y' : S, ψ y' = c⁻¹ * ψ y * c → α (y : S ⧸ N) = (y' : S ⧸ N)) {a : S}
    (ha : ∀ y : S, α (y : S ⧸ N) = ((a * y * a⁻¹ : S) : S ⧸ N)) (y : S) :
    (c * ψ a)⁻¹ * ψ y * (c * ψ a) = ψ y := by
  have hratio : ∀ w, ∃ s ∈ Subgroup.center S, (ψ w)⁻¹ * ((c * ψ a)⁻¹ * ψ w * (c * ψ a)) = ψ s := by
    intro w
    obtain ⟨w', hw'⟩ := exists_conj_preimage hc w
    have hq : ((a * w * a⁻¹ : S) : S ⧸ N) = (w' : S ⧸ N) := by
      rw [← ha w]
      exact hα w w' hw'
    have hs : (a * w * a⁻¹)⁻¹ * w' ∈ Subgroup.center S := by
      rw [← hN]
      exact QuotientGroup.eq.mp hq
    obtain ⟨s, hsdef⟩ : ∃ s, s = (a * w * a⁻¹)⁻¹ * w' := ⟨_, rfl⟩
    rw [← hsdef] at hs
    have hw's : w' = a * w * a⁻¹ * s := by rw [hsdef]; group
    have hs' : a⁻¹ * s * a = s := by
      rw [mul_assoc, ← Subgroup.mem_center_iff.mp hs a, inv_mul_cancel_left]
    refine ⟨s, hs, ?_⟩
    calc (ψ w)⁻¹ * ((c * ψ a)⁻¹ * ψ w * (c * ψ a)) =
        (ψ w)⁻¹ * ((ψ a)⁻¹ * (c⁻¹ * ψ w * c) * ψ a) := by group
      _ = ψ (w⁻¹ * (a⁻¹ * w' * a)) := by
        rw [← hw', map_mul, map_mul, map_mul, map_inv, map_inv]
      _ = ψ s := by
        rw [hw's]
        congr 1
        calc w⁻¹ * (a⁻¹ * (a * w * a⁻¹ * s) * a) = a⁻¹ * s * a := by group
          _ = s := hs'
  have heq := HypSixTypeA.eq_of_inv_mul_comm hperf (H := ψ.range) ψ
    ((MulAut.conj (c * ψ a)⁻¹).toMonoidHom.comp ψ) (fun w => ⟨w, rfl⟩)
    (fun w => by
      obtain ⟨w', hw'⟩ := exists_conj_preimage hc w
      refine ⟨a⁻¹ * w' * a, ?_⟩
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
      rw [map_mul, map_mul, map_inv, hw']
      group)
    (fun w k hk => by
      obtain ⟨s, hs, hsw⟩ := hratio w
      obtain ⟨v, rfl⟩ := hk
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
      rw [hsw, ← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hs v])
  have h1 := congrArg (fun φ : S →* G => φ y) heq
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv] at h1
  exact h1.symm

end Quotient

section InnerDiag

variable {U G : Type*} [Group U] [Group G]

theorem ggPsiInnerDiag_of_centralizes (Δ : UniversalRootDatum U) {ψ : U →* G} {c : G} {a : U}
    (h : ∀ y, (c * ψ a)⁻¹ * ψ y * (c * ψ a) = ψ y) : GGPsiInnerDiag Δ ψ c :=
  ⟨ψ a, ⟨a, rfl⟩, fun _ _ => ⟨1, Subgroup.one_mem _, fun z _ => by
    rw [h z, one_mul, inv_one, mul_one]⟩⟩

theorem exists_conj_of_torusOnRoot (Δ : UniversalRootDatum U) {ψ : U →* G} {c : G}
    {γ : Fin Δ.rank → ℤ} {u : U} (hT : GGTorusOnRoot Δ ψ c γ u) :
    ∃ W : U, ∀ z ∈ Δ.rootGroup γ, ψ (W * z * W⁻¹) = c⁻¹ * ψ (u * z * u⁻¹) * c := by
  obtain ⟨g, ⟨g₀, rfl⟩, h, -, hz⟩ := hT
  refine ⟨g₀ * u * h, fun z hz' => ?_⟩
  have hzt := hz z hz'
  calc ψ (g₀ * u * h * z * (g₀ * u * h)⁻¹) =
      ψ g₀ * ψ (u * (h * z * h⁻¹) * u⁻¹) * (ψ g₀)⁻¹ := by
        simp only [map_mul, map_inv]
        group
    _ = ψ g₀ * ((c * ψ g₀)⁻¹ * ψ (u * z * u⁻¹) * (c * ψ g₀)) * (ψ g₀)⁻¹ := by rw [hzt]
    _ = _ := by group

end InnerDiag

section Field

variable {ι K : Type*} [Fintype ι] [DecidableEq ι] [Field K]

theorem ringEquiv_eq_one_of_mul_conj {E M M' : Matrix ι ι K} (hE : E ≠ 0) (hMM' : M * M' = 1)
    {σ : K ≃+* K} (h : ∀ t : K, (1 + t • E) * M = M * (1 + σ t • E)) : σ = 1 := by
  have hs : ∀ t : K, t • (E * M) = σ t • (M * E) := by
    intro t
    have h1 := h t
    rw [Matrix.add_mul, Matrix.one_mul, Matrix.mul_add, Matrix.mul_one, Matrix.smul_mul,
      Matrix.mul_smul] at h1
    exact add_left_cancel h1
  have hc : E * M = M * E := by simpa using hs 1
  have hEM : E * M ≠ 0 := by
    intro h0
    apply hE
    calc E = E * M * M' := by rw [Matrix.mul_assoc, hMM', Matrix.mul_one]
      _ = 0 := by rw [h0, Matrix.zero_mul]
  refine RingEquiv.ext fun t => ?_
  show σ t = t
  have h3 : (t - σ t) • (E * M) = 0 := by rw [sub_smul, hs t, hc, sub_self]
  rcases smul_eq_zero.mp h3 with h4 | h4
  · exact (sub_eq_zero.mp h4).symm
  · exact absurd h4 hEM

theorem mul_self_eq_one_of_charTwo [CharP K 2] {M : Type*} [Monoid M] {x : K → M}
    (hadd : ∀ s t, x (s + t) = x s * x t) (h0 : x 0 = 1) (t : K) : x t * x t = 1 := by
  rw [← hadd, CharTwo.add_self_eq_zero, h0]

end Field

end RootDetect

end CFSG.StandardType
