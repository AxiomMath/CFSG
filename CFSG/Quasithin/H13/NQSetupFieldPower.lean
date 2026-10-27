module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.ElementaryAbelian
public import CFSG.LocalAnalysis.ComponentInitial.FieldFiniteAutomorphism

public section

namespace CFSG.Quasithin.H13.NQSetup

open Subgroup
open scoped Pointwise

variable {G : Type*} [Group G]

theorem borel_power_action {B T U A : Subgroup G} (hTB : T ≤ B) (hUB : U ≤ B)
    (hUn : ∀ b ∈ B, ∀ u ∈ U, b * u * b⁻¹ ∈ U) (hT : ∀ t ∈ T, ∀ t' ∈ T, t * t' = t' * t)
    (hBTU : ∀ b ∈ B, ∃ t ∈ T, ∃ u ∈ U, b = t * u) (hAB : A ≤ B) (hAU : A ⊓ U = ⊥) :
    (∀ a ∈ A, ∀ a' ∈ A, a * a' = a' * a) ∧
      ∀ (δ : G →* G) (n : ℕ), (∀ u ∈ U, δ u ∈ U) → (∀ t ∈ T, δ t = t ^ n) →
        ∀ g ∈ B, (∀ a ∈ A, g * δ a * g⁻¹ ∈ A) → ∀ a ∈ A, g * δ a * g⁻¹ = a ^ n := by
  have hN : (U.subgroupOf B).Normal := ⟨fun u hu b => by
    rw [mem_subgroupOf] at hu ⊢
    simpa using hUn b b.2 u hu⟩
  have hAinj : ∀ x ∈ A, ∀ y ∈ A, x⁻¹ * y ∈ U → x = y := by
    intro x hx y hy hxy
    have h1 : x⁻¹ * y ∈ A ⊓ U := mem_inf.2 ⟨mul_mem (inv_mem hx) hy, hxy⟩
    rw [hAU, mem_bot] at h1
    exact inv_mul_eq_one.1 h1
  have hcoset : ∀ x : B, ∃ t : B, (t : G) ∈ T ∧
      (QuotientGroup.mk x : B ⧸ U.subgroupOf B) = QuotientGroup.mk t := by
    intro x
    obtain ⟨t, ht, u, hu, hx⟩ := hBTU x x.2
    refine ⟨⟨t, hTB ht⟩, ht, ?_⟩
    rw [QuotientGroup.eq, mem_subgroupOf]
    simp only [coe_mul, coe_inv, hx, mul_inv_rev, inv_mul_cancel_right]
    exact inv_mem hu
  have hcomm : ∀ x y : B, (QuotientGroup.mk x : B ⧸ U.subgroupOf B) * QuotientGroup.mk y =
      QuotientGroup.mk y * QuotientGroup.mk x := by
    intro x y
    obtain ⟨t, ht, hxt⟩ := hcoset x
    obtain ⟨t', ht', hyt⟩ := hcoset y
    rw [hxt, hyt, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    congr 1
    exact Subtype.ext (hT _ ht _ ht')
  have hmodU : ∀ x y : B, (QuotientGroup.mk x : B ⧸ U.subgroupOf B) = QuotientGroup.mk y →
      ((x : G))⁻¹ * y ∈ U := by
    intro x y h
    have := QuotientGroup.eq.1 h
    rw [mem_subgroupOf] at this
    simpa using this
  refine ⟨fun a ha a' ha' => ?_, fun δ n hδU hδT g hg hgA a ha => ?_⟩
  · have h1 := hcomm ⟨a, hAB ha⟩ ⟨a', hAB ha'⟩
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul] at h1
    have h2 := hmodU _ _ h1
    simp only [coe_mul] at h2
    exact hAinj _ (mul_mem ha ha') _ (mul_mem ha' ha) h2
  · obtain ⟨t, ht, u, hu, hau⟩ := hBTU a (hAB ha)
    have hδa : δ a = t ^ n * δ u := by rw [hau, map_mul, hδT t ht]
    have hδaB : δ a ∈ B := by
      rw [hδa]
      exact mul_mem (pow_mem (hTB ht) n) (hUB (hδU u hu))
    have hx := hgA a ha
    have h1 : (QuotientGroup.mk (⟨δ a, hδaB⟩ : B) : B ⧸ U.subgroupOf B) =
        QuotientGroup.mk (⟨a ^ n, pow_mem (hAB ha) n⟩ : B) := by
      have e1 : (QuotientGroup.mk (⟨δ a, hδaB⟩ : B) : B ⧸ U.subgroupOf B) =
          QuotientGroup.mk (⟨t ^ n, pow_mem (hTB ht) n⟩ : B) := by
        rw [QuotientGroup.eq, mem_subgroupOf]
        simp only [coe_mul, coe_inv, hδa, mul_inv_rev, inv_mul_cancel_right]
        exact inv_mem (hδU u hu)
      have e2 : (QuotientGroup.mk (⟨a, hAB ha⟩ : B) : B ⧸ U.subgroupOf B) =
          QuotientGroup.mk (⟨t, hTB ht⟩ : B) := by
        rw [QuotientGroup.eq, mem_subgroupOf]
        simp only [coe_mul, coe_inv, hau, mul_inv_rev, inv_mul_cancel_right]
        exact inv_mem hu
      have e3 : (⟨t ^ n, pow_mem (hTB ht) n⟩ : B) = (⟨t, hTB ht⟩ : B) ^ n := Subtype.ext (by simp)
      have e4 : (⟨a ^ n, pow_mem (hAB ha) n⟩ : B) = (⟨a, hAB ha⟩ : B) ^ n := Subtype.ext (by simp)
      rw [e1, e3, QuotientGroup.mk_pow, e4, QuotientGroup.mk_pow, e2]
    have h2 : (QuotientGroup.mk (⟨g * δ a * g⁻¹, hAB hx⟩ : B) : B ⧸ U.subgroupOf B) =
        QuotientGroup.mk (⟨δ a, hδaB⟩ : B) := by
      have e : (⟨g * δ a * g⁻¹, hAB hx⟩ : B) = ⟨g, hg⟩ * ⟨δ a, hδaB⟩ * (⟨g, hg⟩ : B)⁻¹ :=
        Subtype.ext (by simp)
      rw [e, QuotientGroup.mk_mul, QuotientGroup.mk_mul, hcomm, QuotientGroup.mk_inv,
        mul_inv_cancel_right]
    exact hAinj _ hx _ (pow_mem ha n) (hmodU _ _ (h2.trans h1))

theorem exists_pow_two_pow_of_ringEquiv {k : Type} [Field k] {f : ℕ} (hf : 1 ≤ f)
    (hk : Nat.card k = 2 ^ f) (δ : k ≃+* k) : ∃ i < f, ∀ c, δ c = c ^ 2 ^ i := by
  obtain ⟨σ, hσ, hord, hz, -⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_automorphism_fixed_field_cardinality
      Nat.prime_two hf hk
  have : Finite (k ≃+* k) := by
    have : Finite k := Nat.finite_of_card_ne_zero (by rw [hk]; positivity)
    exact Finite.of_injective (fun e : k ≃+* k => (e : k → k)) DFunLike.coe_injective
  have hmem : δ ∈ Submonoid.powers σ := by
    rw [mem_powers_iff_mem_zpowers, hz]
    exact mem_top δ
  obtain ⟨m, rfl⟩ := hmem
  have hpow : ∀ (j : ℕ) (c : k), (σ ^ j) c = c ^ 2 ^ j := by
    intro j
    induction j with
    | zero => intro c; simp
    | succ j ih =>
      intro c
      rw [pow_succ]
      change (σ ^ j) (σ c) = _
      rw [hσ, ih, ← pow_mul, ← pow_succ']
  refine ⟨m % f, Nat.mod_lt m (by omega), fun c => ?_⟩
  change (σ ^ m) c = _
  rw [← pow_mod_orderOf σ m, hord, hpow]

theorem exists_subgroup_mul_eq {X : Type*} [Group X] (A U : Subgroup X)
    (h : (A : Set X) * (U : Set X) = (U : Set X) * (A : Set X)) (hd : Disjoint A U) :
    ∃ D : Subgroup X, A ≤ D ∧ U ≤ D ∧ Nat.card D = Nat.card A * Nat.card U := by
  let D : Subgroup X :=
    { carrier := (A : Set X) * (U : Set X)
      mul_mem' := by
        rintro _ _ ⟨a, ha, u, hu, rfl⟩ ⟨a', ha', u', hu', rfl⟩
        have h1 : u * a' ∈ (A : Set X) * (U : Set X) := h ▸ Set.mul_mem_mul hu ha'
        obtain ⟨a'', ha'', u'', hu'', he⟩ := h1
        refine ⟨a * a'', mul_mem ha ha'', u'' * u', mul_mem hu'' hu', ?_⟩
        rw [show a * u * (a' * u') = a * (u * a') * u' by group, ← he]
        group
      one_mem' := ⟨1, one_mem A, 1, one_mem U, mul_one 1⟩
      inv_mem' := by
        rintro _ ⟨a, ha, u, hu, rfl⟩
        have h1 : u⁻¹ * a⁻¹ ∈ (A : Set X) * (U : Set X) :=
          h ▸ Set.mul_mem_mul (inv_mem hu) (inv_mem ha)
        rwa [mul_inv_rev] }
  have hD : ∀ x, x ∈ D ↔ x ∈ (A : Set X) * (U : Set X) := fun x => Iff.rfl
  refine ⟨D, fun a ha => (hD a).2 ⟨a, ha, 1, one_mem U, mul_one a⟩,
    fun u hu => (hD u).2 ⟨1, one_mem A, u, hu, one_mul u⟩, ?_⟩
  let e : A × U → D := fun p => ⟨p.1 * p.2, (hD _).2 (Set.mul_mem_mul p.1.2 p.2.2)⟩
  have he : Function.Bijective e := by
    refine ⟨fun p q hpq => Subgroup.mul_injective_of_disjoint hd (congrArg Subtype.val hpq), ?_⟩
    rintro ⟨x, hx⟩
    obtain ⟨a, ha, u, hu, rfl⟩ := (hD x).1 hx
    exact ⟨(⟨a, ha⟩, ⟨u, hu⟩), rfl⟩
  rw [← Nat.card_prod, Nat.card_congr (Equiv.ofBijective e he)]

theorem map_inv_mul_mul_eq {X : Type*} [Group X] (κ β : MulAut X) {H : Subgroup X}
    (hH : H.map β.toMonoidHom = H) :
    (H.map κ⁻¹.toMonoidHom).map (κ⁻¹ * β * κ).toMonoidHom = H.map κ⁻¹.toMonoidHom := by
  rw [Subgroup.map_map]
  have e : (κ⁻¹ * β * κ).toMonoidHom.comp κ⁻¹.toMonoidHom =
      κ⁻¹.toMonoidHom.comp β.toMonoidHom := by
    ext x
    simp
  rw [e, ← Subgroup.map_map, hH]


theorem field_power_of_sylow {X : Type*} [Group X] [Finite X] (U₀ : Subgroup X) (P : Sylow 2 X)
    (hP : (P : Subgroup X) = U₀) (n : ℕ)
    (H : ∀ A : Subgroup X, Odd (Nat.card A) → ¬ 3 ∣ Nat.card A →
      (A : Set X) * (U₀ : Set X) = (U₀ : Set X) * (A : Set X) →
      (∀ a ∈ A, ∀ b ∈ A, a * b = b * a) ∧
        ∀ α : MulAut X, A.map α.toMonoidHom = A → U₀.map α.toMonoidHom = U₀ →
          ∃ i < n, ∀ a ∈ A, α a = a ^ 2 ^ i)
    (U : Sylow 2 X) (A : Subgroup X) (hAodd : Odd (Nat.card A)) (hA3 : ¬ 3 ∣ Nat.card A)
    (hAU : (A : Set X) * ((U : Subgroup X) : Set X) = ((U : Subgroup X) : Set X) * (A : Set X)) :
    (∀ a ∈ A, ∀ b ∈ A, a * b = b * a) ∧
      (∀ α : MulAut X, A.map α.toMonoidHom = A → (U : Subgroup X).map α.toMonoidHom = U →
        ∃ i < n, ∀ a ∈ A, α a = a ^ 2 ^ i) ∧
      ∀ α : MulAut X, A.map α.toMonoidHom = A → (U : Subgroup X).map α.toMonoidHom = U →
        ∀ p : ℕ, p.Prime → ∀ (N : Subgroup A) [N.Characteristic],
          CFSG.IsElementaryAbelian p (A ⧸ N) →
          ∃ c : ZMod p, ∀ a b : A, (b : X) = α a → (b : A ⧸ N) = (a : A ⧸ N) ^ c.val := by
  classical
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq X P U
  set κ : MulAut X := MulAut.conj c with hκ
  have hUκ : (U : Subgroup X) = U₀.map κ.toMonoidHom := by
    rw [← hc, Sylow.coe_subgroup_smul, hP]
    rfl
  set A₀ := A.map κ⁻¹.toMonoidHom with hA₀
  have hA₀card : Nat.card A₀ = Nat.card A := Subgroup.card_map_of_injective κ⁻¹.injective
  have hU₀ : U₀ = (U : Subgroup X).map κ⁻¹.toMonoidHom := by
    rw [hUκ, Subgroup.map_map]
    have e : κ⁻¹.toMonoidHom.comp κ.toMonoidHom = MonoidHom.id _ := by
      ext x
      simp
    rw [e, Subgroup.map_id]
  have hA₀U : (A₀ : Set X) * (U₀ : Set X) = (U₀ : Set X) * (A₀ : Set X) := by
    rw [hU₀, hA₀, Subgroup.coe_map, Subgroup.coe_map, ← Set.image_mul, hAU, Set.image_mul]
  obtain ⟨hcomm₀, hpow₀⟩ := H A₀ (hA₀card ▸ hAodd) (hA₀card ▸ hA3) hA₀U
  have hfield : ∀ α : MulAut X, A.map α.toMonoidHom = A →
      (U : Subgroup X).map α.toMonoidHom = U → ∃ i < n, ∀ a ∈ A, α a = a ^ 2 ^ i := by
    intro α hαA hαU
    obtain ⟨i, hi, hα₀⟩ := hpow₀ (κ⁻¹ * α * κ) (map_inv_mul_mul_eq κ α hαA)
      (by rw [hU₀]; exact map_inv_mul_mul_eq κ α hαU)
    refine ⟨i, hi, fun a ha => ?_⟩
    have h1 := hα₀ (κ⁻¹ a) ⟨a, ha, rfl⟩
    rw [MulAut.mul_apply, MulAut.mul_apply, MulAut.apply_inv_self, ← map_pow] at h1
    exact κ⁻¹.injective h1
  refine ⟨fun a ha b hb => ?_, hfield, fun α hαA hαU p _ N _ hN => ?_⟩
  · have h1 := hcomm₀ (κ⁻¹ a) ⟨a, ha, rfl⟩ (κ⁻¹ b) ⟨b, hb, rfl⟩
    rw [← map_mul, ← map_mul] at h1
    exact κ⁻¹.injective h1
  · obtain ⟨i, -, hα⟩ := hfield α hαA hαU
    refine ⟨(2 ^ i : ℕ), fun a b hab => ?_⟩
    have hb : b = a ^ 2 ^ i := Subtype.ext (by rw [hab, hα a a.2, coe_pow])
    have hexp : ((a : A ⧸ N)) ^ p = 1 :=
      Monoid.exponent_dvd_iff_forall_pow_eq_one.1 (IsElementaryAbelian.exponent_dvd_p p (A ⧸ N)) _
    rw [hb, QuotientGroup.mk_pow, ZMod.val_natCast, ← pow_eq_pow_mod _ hexp]

end CFSG.Quasithin.H13.NQSetup
