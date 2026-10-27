module

public import CFSG.ClassicalGroups.Orthogonal.Transitive
public import CFSG.RankThree.GF2n.Stroth80.Satz5Hyperbolic

public section

namespace CFSG.RankThree.GF2n.Stroth80

private theorem stroth80_inv_mul_of_mul_eq {G : Type} [Group G] {z z' b b' : G}
    (h : z * b = z' * b') : z'⁻¹ * z = b' * b⁻¹ := by
  calc z'⁻¹ * z = z'⁻¹ * (z * b) * b⁻¹ := by simp [mul_assoc]
    _ = z'⁻¹ * (z' * b') * b⁻¹ := by rw [h]
    _ = b' * b⁻¹ := by simp [mul_assoc]

private theorem stroth80_mulMap_injective {G : Type} [Group G] {Z B D : Subgroup G}
    (hZ : Z ≤ D) (hB : B ≤ D) (hinf : Z ⊓ B = ⊥) :
    Function.Injective (fun p : ↥Z × ↥B =>
      (⟨(p.1 : G) * (p.2 : G), D.mul_mem (hZ p.1.2) (hB p.2.2)⟩ : ↥D)) := by
  rintro ⟨z, b⟩ ⟨z', b'⟩ h
  have h' : (z : G) * (b : G) = (z' : G) * (b' : G) := congrArg Subtype.val h
  have hmem : (z' : G)⁻¹ * (z : G) ∈ Z ⊓ B :=
    Subgroup.mem_inf.2 ⟨Z.mul_mem (Z.inv_mem z'.2) z.2, by
      rw [stroth80_inv_mul_of_mul_eq h']
      exact B.mul_mem b'.2 (B.inv_mem b.2)⟩
  rw [hinf, Subgroup.mem_bot, inv_mul_eq_one] at hmem
  have hzz : (z : G) = (z' : G) := hmem.symm
  have hbb : (b : G) = (b' : G) := by
    rw [hzz] at h'
    exact mul_left_cancel h'
  exact Prod.ext (Subtype.ext hzz) (Subtype.ext hbb)

theorem card_mul_le_of_inf_eq_bot {G : Type} [Group G] [Finite G] {Z B D : Subgroup G}
    (hZ : Z ≤ D) (hB : B ≤ D) (hinf : Z ⊓ B = ⊥) :
    Nat.card Z * Nat.card B ≤ Nat.card D := by
  rw [← Nat.card_prod]
  exact Nat.card_le_card_of_injective _ (stroth80_mulMap_injective hZ hB hinf)

theorem exists_mul_of_card_eq {G : Type} [Group G] [Finite G] {Z B D : Subgroup G}
    (hZ : Z ≤ D) (hB : B ≤ D) (hinf : Z ⊓ B = ⊥)
    (hcard : Nat.card D = Nat.card Z * Nat.card B) :
    ∀ d ∈ D, ∃ z ∈ Z, ∃ b ∈ B, d = z * b := by
  intro d hd
  have hinj := stroth80_mulMap_injective hZ hB hinf
  have hcard' : Nat.card (↥Z × ↥B) = Nat.card ↥D := by
    rw [Nat.card_prod, hcard]
  have hbij := (Nat.bijective_iff_injective_and_card _).2 ⟨hinj, hcard'⟩
  obtain ⟨⟨z, b⟩, hzb⟩ := hbij.2 ⟨d, hd⟩
  exact ⟨(z : G), z.2, (b : G), b.2, (congrArg Subtype.val hzb).symm⟩

theorem card_dvd_of_free_action {H X : Type} [Group H] [Finite H] [Finite X] [MulAction H X]
    (hfree : ∀ (h : H) (x : X), h • x = x → h = 1) : Nat.card H ∣ Nat.card X := by
  classical
  haveI : Fintype (MulAction.orbitRel.Quotient H X) := Fintype.ofFinite _
  have horb : ∀ ω : MulAction.orbitRel.Quotient H X, Nat.card ω.orbit = Nat.card H := by
    intro ω
    have hstab : MulAction.stabilizer H ω.out = ⊥ := by
      rw [Subgroup.eq_bot_iff_forall]
      intro h hh
      exact hfree h ω.out (MulAction.mem_stabilizer_iff.mp hh)
    rw [MulAction.orbitRel.Quotient.orbit_eq_orbit_out ω Quotient.out_eq',
      Nat.card_congr (MulAction.orbitEquivQuotientStabilizer H ω.out), hstab]
    exact Subgroup.index_bot
  rw [Nat.card_congr (MulAction.selfEquivSigmaOrbits' H X), Nat.card_sigma]
  exact Finset.dvd_sum fun ω _ => dvd_of_eq (horb ω).symm

theorem two_pow_sub_one_dvd {r k : ℕ} (hr : 0 < r) (h : 2 ^ r - 1 ∣ 2 ^ k - 1) : r ∣ k := by
  have hg := Nat.pow_sub_one_gcd_pow_sub_one 2 r k
  rw [Nat.gcd_eq_left h] at hg
  have hp1 : 0 < 2 ^ r := pow_pos (by norm_num) r
  have hp2 : 0 < 2 ^ Nat.gcd r k := pow_pos (by norm_num) _
  have h2 : 2 ^ r = 2 ^ Nat.gcd r k := by omega
  have hr' : r = Nat.gcd r k := Nat.pow_right_injective (le_refl 2) h2
  have hd := Nat.gcd_dvd_right r k
  rw [← hr'] at hd
  exact hd

theorem eq_of_two_pow_bounds {r k : ℕ} (hr : 0 < r) (hdvd : 2 ^ r - 1 ∣ 2 ^ k - 1)
    (h1 : 2 ^ r ≤ 2 ^ k) (h2 : 2 ^ k < 2 ^ (2 * r)) : k = r := by
  obtain ⟨s, hs⟩ := two_pow_sub_one_dvd hr hdvd
  have hk1 : r ≤ k := (Nat.pow_le_pow_iff_right (by norm_num)).mp h1
  have hk2 : k < 2 * r := (Nat.pow_lt_pow_iff_right (by norm_num)).mp h2
  subst hs
  have hs2 : s < 2 := by
    by_contra hc
    have hc' : 2 ≤ s := not_lt.mp hc
    have h3 : r * 2 ≤ r * s := Nat.mul_le_mul_left r hc'
    omega
  interval_cases s <;> omega

theorem card_conj_free_dvd {G : Type} [Group G] [Finite G] {Q L : Subgroup G} (hQL : Q ≤ L)
    {τ : G} (hτL : ∀ l ∈ L, τ * l * τ⁻¹ ∈ L) (hτQ : ∀ x ∈ Q, τ * x * τ⁻¹ ∈ Q)
    (hfree : ∀ i : ℕ, 0 < i → i < orderOf τ → ∀ l ∈ L,
      τ ^ i * l * (τ ^ i)⁻¹ * l⁻¹ ∈ Q → l ∈ Q) :
    orderOf τ ∣ Nat.card L - Nat.card Q := by
  classical
  have hn : 0 < orderOf τ := orderOf_pos τ
  have hpow : ∀ S : Subgroup G, (∀ x ∈ S, τ * x * τ⁻¹ ∈ S) →
      ∀ i : ℕ, ∀ x ∈ S, τ ^ i * x * (τ ^ i)⁻¹ ∈ S := by
    intro S hS i
    induction i with
    | zero => intro x hx; simpa using hx
    | succ k ih =>
      intro x hx
      have e : τ ^ (k + 1) * x * (τ ^ (k + 1))⁻¹ = τ * (τ ^ k * x * (τ ^ k)⁻¹) * τ⁻¹ := by
        simp only [pow_succ', mul_inv_rev, mul_assoc]
      rw [e]
      exact hS _ (ih x hx)
  have hinv : ∀ i : ℕ, ∀ l : G, τ ^ i * l * (τ ^ i)⁻¹ ∈ Q → l ∈ Q := by
    intro i l hy
    obtain ⟨m, hm⟩ : ∃ m : ℕ, m + i = orderOf τ * i :=
      ⟨orderOf τ * i - i, by
        have : i ≤ orderOf τ * i := Nat.le_mul_of_pos_left i hn
        omega⟩
    have hmi : τ ^ m * τ ^ i = 1 := by
      rw [← pow_add, hm, pow_mul, pow_orderOf_eq_one, one_pow]
    have h2 := hpow Q hτQ m _ hy
    have e : τ ^ m * (τ ^ i * l * (τ ^ i)⁻¹) * (τ ^ m)⁻¹ = l := by
      have hm' : τ ^ m = (τ ^ i)⁻¹ := eq_inv_of_mul_eq_one_left hmi
      rw [hm', inv_inv]
      group
    rw [e] at h2
    exact h2
  have hgX : ∀ g ∈ Subgroup.zpowers τ, ∀ l ∈ (L : Set G) \ (Q : Set G),
      g * l * g⁻¹ ∈ (L : Set G) \ (Q : Set G) := by
    intro g hg l hl
    obtain ⟨i, rfl⟩ := (Submonoid.mem_powers_iff _ _).mp (mem_powers_iff_mem_zpowers.mpr hg)
    exact ⟨hpow L hτL i l hl.1, fun hy => hl.2 (hinv i l hy)⟩
  letI act : MulAction (Subgroup.zpowers τ) ↥((L : Set G) \ (Q : Set G)) :=
    { smul := fun g x => ⟨g.1 * x.1 * g.1⁻¹, hgX g.1 g.2 x.1 x.2⟩
      one_smul := fun x => by
        apply Subtype.ext
        show (1 : G) * x.1 * (1 : G)⁻¹ = x.1
        simp
      mul_smul := fun g h x => by
        apply Subtype.ext
        show g.1 * h.1 * x.1 * (g.1 * h.1)⁻¹ = g.1 * (h.1 * x.1 * h.1⁻¹) * g.1⁻¹
        simp only [mul_inv_rev, mul_assoc] }
  have hfreeX : ∀ (h : ↥(Subgroup.zpowers τ)) (x : ↥((L : Set G) \ (Q : Set G))),
      h • x = x → h = 1 := by
    intro h x hx
    have hconj : h.1 * x.1 * h.1⁻¹ = x.1 := congrArg Subtype.val hx
    obtain ⟨i, hi⟩ := (Submonoid.mem_powers_iff _ _).mp (mem_powers_iff_mem_zpowers.mpr h.2)
    have hτh : τ ^ (i % orderOf τ) = h.1 := (pow_mod_orderOf τ i).trans hi
    rcases Nat.eq_zero_or_pos (i % orderOf τ) with h0 | hpos
    · apply Subtype.ext
      rw [← hτh, h0, pow_zero, Subgroup.coe_one]
    · exfalso
      have hlt : i % orderOf τ < orderOf τ := Nat.mod_lt _ hn
      have hc : τ ^ (i % orderOf τ) * x.1 * (τ ^ (i % orderOf τ))⁻¹ * x.1⁻¹ = 1 := by
        rw [hτh, hconj, mul_inv_cancel]
      have hmemQ := hfree (i % orderOf τ) hpos hlt x.1 x.2.1 (by rw [hc]; exact Q.one_mem)
      exact x.2.2 hmemQ
  have hcardH : Nat.card (Subgroup.zpowers τ) = orderOf τ := Nat.card_zpowers τ
  have hsub : (Q : Set G) ⊆ (L : Set G) := SetLike.coe_subset_coe.mpr hQL
  have hcardX : Nat.card ↥((L : Set G) \ (Q : Set G)) = Nat.card L - Nat.card Q := by
    have h3 := Set.ncard_sdiff_add_ncard_of_subset hsub
    have hL : Nat.card L = (L : Set G).ncard := Nat.card_coe_set_eq _
    have hQ' : Nat.card Q = (Q : Set G).ncard := Nat.card_coe_set_eq _
    rw [Nat.card_coe_set_eq, hL, hQ']
    omega
  have hdvd := card_dvd_of_free_action (H := ↥(Subgroup.zpowers τ))
    (X := ↥((L : Set G) \ (Q : Set G))) hfreeX
  rw [hcardH, hcardX] at hdvd
  exact hdvd

end CFSG.RankThree.GF2n.Stroth80

namespace CFSG.ClassicalGroups.Orthogonal

open QuadraticMap

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

theorem mem_rootGroup_of_formula (h2 : (2 : K) = 0) {b v : V} (hbs : Q b = 0)
    (hv : polar Q b v = 0) (T : V ≃ₗ[K] V)
    (hT : ∀ y, T y = y + polar Q y b • v + polar Q y v • b + (Q v * polar Q y b) • b) :
    T ∈ rootGroup Q b := by
  have hneg : ∀ c : K, -c = c := fun c =>
    neg_eq_of_add_eq_zero_left (by rw [← two_mul, h2, zero_mul])
  rw [mem_rootGroup]
  refine ⟨v, hv, LinearEquiv.ext fun y => ?_⟩
  rw [eichler_apply hbs hv y, hT y, sub_eq_add_neg, ← neg_smul, hneg, add_smul]
  abel

end CFSG.ClassicalGroups.Orthogonal

namespace CFSG.RankThree.GF2n.Stroth80.Satz5

open CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Tim79 CFSG.ClassicalGroups.Orthogonal

variable {G : Type} [Group G] {P Z : Subgroup G} {K : Type} [Field K] {γ : G → K}

theorem exists_hyperbolic_triple_of_singular (M₀ : Tim79.QuadModel P Z K γ)
    {S₁ S₂ : Submodule K M₀.E} (hS : IsCompl S₁ S₂) (hS₁ : ∀ x ∈ S₁, M₀.Qf x = 0)
    (hS₂ : ∀ x ∈ S₂, M₀.Qf x = 0) (hdim : 4 ≤ Module.finrank K M₀.E) {b : M₀.E}
    (hb0 : b ≠ 0) (hbs : M₀.Qf b = 0) :
    ∃ v₁ w₁ w₂ : M₀.E, M₀.Qf v₁ = 0 ∧ M₀.Qf w₁ = 0 ∧ M₀.Qf w₂ = 0 ∧
      M₀.B v₁ w₁ = 1 ∧ M₀.B b w₂ = 1 ∧ M₀.B v₁ w₂ = 0 ∧ M₀.B b w₁ = 0 ∧
      M₀.B v₁ b = 0 ∧ M₀.B w₁ w₂ = 0 := by
  obtain ⟨v₁, v₂, w₁, w₂, hv₁, hv₂, hw₁, hw₂, hv₁w₁, hv₂w₂, hv₁w₂, hv₂w₁, hv₁v₂, hw₁w₂⟩ :=
    exists_hyperbolic_quadruple M₀ hS hS₁ hS₂ hdim
  have hQ : ∀ x : M₀.E, M₀.toQuadraticForm x = M₀.Qf x := fun x => rfl
  have hpol : ∀ x y : M₀.E, QuadraticMap.polar M₀.toQuadraticForm x y = M₀.B x y :=
    fun x y => Tim79.QuadModel.polar_toQuadraticForm M₀ x y
  have hBeq : QuadraticMap.polarBilin M₀.toQuadraticForm = M₀.B := by
    refine LinearMap.ext fun x => LinearMap.ext fun y => ?_
    rw [QuadraticMap.polarBilin_apply_apply, hpol]
  have hnd : M₀.B.Nondegenerate := by
    refine ⟨fun x hx => M₀.nondeg x hx, fun y hy => M₀.nondeg y fun f => ?_⟩
    rw [Tim79.QuadModel.B_comm (M₀ := M₀) y f, hy f, neg_zero]
  have hnd' : (QuadraticMap.polarBilin M₀.toQuadraticForm).Nondegenerate := by
    rw [hBeq]
    exact hnd
  obtain ⟨H₁, hH₁e, hH₁f⟩ :
      ∃ H : CFSG.ClassicalGroups.Orthogonal.HypPair M₀.toQuadraticForm,
        H.e = v₁ ∧ H.f = w₁ :=
    ⟨⟨v₁, w₁, (hQ v₁).trans hv₁, (hQ w₁).trans hw₁, (hpol v₁ w₁).trans hv₁w₁⟩, rfl, rfl⟩
  obtain ⟨H₂, hH₂e, hH₂f⟩ :
      ∃ H : CFSG.ClassicalGroups.Orthogonal.HypPair M₀.toQuadraticForm,
        H.e = v₂ ∧ H.f = w₂ :=
    ⟨⟨v₂, w₂, (hQ v₂).trans hv₂, (hQ w₂).trans hw₂, (hpol v₂ w₂).trans hv₂w₂⟩, rfl, rfl⟩
  have hee : QuadraticMap.polar M₀.toQuadraticForm v₁ v₂ = 0 := (hpol v₁ v₂).trans hv₁v₂
  have hef : QuadraticMap.polar M₀.toQuadraticForm v₁ w₂ = 0 := (hpol v₁ w₂).trans hv₁w₂
  have hfe : QuadraticMap.polar M₀.toQuadraticForm w₁ v₂ = 0 := by
    rw [hpol, Tim79.QuadModel.B_comm (M₀ := M₀) w₁ v₂, hv₂w₁, neg_zero]
  have hff : QuadraticMap.polar M₀.toQuadraticForm w₁ w₂ = 0 := (hpol w₁ w₂).trans hw₁w₂
  have hO : H₁.Orth H₂ := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [hH₁e, hH₂e]
      exact hee
    · rw [hH₁e, hH₂f]
      exact hef
    · rw [hH₁f, hH₂e]
      exact hfe
    · rw [hH₁f, hH₂f]
      exact hff
  have hxy : M₀.toQuadraticForm v₂ = M₀.toQuadraticForm b :=
    (hQ v₂).trans ((hv₂.trans hbs.symm).trans (hQ b).symm)
  have hv₂0 : v₂ ≠ 0 := fun h => by
    rw [h, map_zero, LinearMap.zero_apply] at hv₂w₂
    exact zero_ne_one hv₂w₂
  obtain ⟨g, hg, hgv⟩ :=
    CFSG.ClassicalGroups.Orthogonal.exists_mem_elementaryGroup_apply_eq hnd' hO hv₂0 hb0 hxy
  have hg' := CFSG.ClassicalGroups.Orthogonal.elementaryGroup_le_orthogonalGroup
    M₀.toQuadraticForm hg
  have hgQ : ∀ x : M₀.E, M₀.Qf (g x) = M₀.Qf x := fun x =>
    CFSG.ClassicalGroups.Orthogonal.map_of_mem hg' x
  have hgB : ∀ x y : M₀.E, M₀.B (g x) (g y) = M₀.B x y := fun x y =>
    (hpol (g x) (g y)).symm.trans
      ((CFSG.ClassicalGroups.Orthogonal.polar_map_of_mem hg' x y).trans (hpol x y))
  refine ⟨g v₁, g w₁, g w₂, (hgQ v₁).trans hv₁, (hgQ w₁).trans hw₁, (hgQ w₂).trans hw₂,
    (hgB v₁ w₁).trans hv₁w₁, ?_, (hgB v₁ w₂).trans hv₁w₂, ?_, ?_, (hgB w₁ w₂).trans hw₁w₂⟩
  · rw [← hgv]
    exact (hgB v₂ w₂).trans hv₂w₂
  · rw [← hgv]
    exact (hgB v₂ w₁).trans hv₂w₁
  · rw [← hgv]
    exact (hgB v₁ v₂).trans hv₁v₂

end CFSG.RankThree.GF2n.Stroth80.Satz5
