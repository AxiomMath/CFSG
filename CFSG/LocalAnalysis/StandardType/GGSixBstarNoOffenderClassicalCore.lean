module

public import CFSG.LocalAnalysis.StandardType.GGSixBstarUniqueBasic

public section

namespace CFSG.StandardType

open CFSG.Assembly

namespace NoOffenderClassical

section Regular

variable {G : Type*} [Group G]

theorem card_mul_lt_of_regular [Finite G] {Bs E : Subgroup G}
    (hBc : ∀ a ∈ Bs, ∀ b ∈ Bs, a * b = b * a)
    (hEN : E ≤ Subgroup.normalizer (Bs : Set G)) {v : G} (hv : v ∈ Bs)
    (hreg : ∀ e ∈ E, e * v * e⁻¹ * v⁻¹ ∈ Subgroup.centralizer (E : Set G) →
      e ∈ Subgroup.centralizer (Bs : Set G))
    (hEC : ¬ E ≤ Subgroup.centralizer (Bs : Set G)) :
    Nat.card (Bs ⊓ Subgroup.centralizer (E : Set G) : Subgroup G) * Nat.card E <
      Nat.card Bs * Nat.card (E ⊓ Subgroup.centralizer (Bs : Set G) : Subgroup G) := by
  classical
  set C := Bs ⊓ Subgroup.centralizer (E : Set G) with hCdef
  set N : Subgroup ↥E := (Subgroup.centralizer (Bs : Set G)).subgroupOf E with hNdef
  have hconj : ∀ e ∈ E, ∀ b ∈ Bs, e * b * e⁻¹ ∈ Bs := fun e he b hb =>
    (Subgroup.mem_normalizer_iff.mp (hEN he) b).mp hb
  have hcE : ∀ c ∈ C, ∀ e ∈ E, e * c * e⁻¹ = c := fun c hc e he => by
    rw [Subgroup.mem_centralizer_iff.mp hc.2 e he, mul_inv_cancel_right]
  have hkey : ∀ e ∈ E, ∀ c ∈ C, ∀ c' ∈ C, e * v * e⁻¹ * c = v * c' →
      e ∈ Subgroup.centralizer (Bs : Set G) := by
    intro e he c hc c' hc' h
    apply hreg e he
    have h1 : e * v * e⁻¹ = v * c' * c⁻¹ := by
      rw [← h]
      group
    have h2 : e * v * e⁻¹ * v⁻¹ = c' * c⁻¹ := by
      rw [h1, mul_assoc v, hBc v hv _ (Bs.mul_mem hc'.1 (Bs.inv_mem hc.1)), mul_assoc,
        mul_inv_cancel, mul_one]
    rw [h2]
    exact Subgroup.mul_mem _ hc'.2 (Subgroup.inv_mem _ hc.2)
  have hfixv : ∀ a b : ↥E, a⁻¹ * b ∈ N → (a : G) * v * (a : G)⁻¹ = (b : G) * v * (b : G)⁻¹ := by
    intro a b hab
    have hn : ((a⁻¹ * b : ↥E) : G) ∈ Subgroup.centralizer (Bs : Set G) := hab
    have hc := Subgroup.mem_centralizer_iff.mp hn v hv
    have hb : (b : G) = a * ((a⁻¹ * b : ↥E) : G) := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, mul_inv_cancel_left]
    rw [hb]
    calc (a : G) * v * (a : G)⁻¹ =
        (a : G) * (v * ((a⁻¹ * b : ↥E) : G)) * ((a⁻¹ * b : ↥E) : G)⁻¹ * (a : G)⁻¹ := by group
      _ = (a : G) * (((a⁻¹ * b : ↥E) : G) * v) * ((a⁻¹ * b : ↥E) : G)⁻¹ * (a : G)⁻¹ := by
          rw [hc]
      _ = _ := by group
  let f : (↥E ⧸ N) × ↥C → ↥Bs := fun x =>
    ⟨Quotient.liftOn' x.1 (fun e : ↥E => (e : G) * v * (e : G)⁻¹)
        (fun a b hab => hfixv a b (QuotientGroup.leftRel_apply.mp hab)) * (x.2 : G), by
      obtain ⟨q, c⟩ := x
      induction q using QuotientGroup.induction_on with
      | H e => exact Bs.mul_mem (hconj e e.2 v hv) c.2.1⟩
  have hf : ∀ (e : ↥E) (c : ↥C), ((f (QuotientGroup.mk e, c) : ↥Bs) : G) =
      (e : G) * v * (e : G)⁻¹ * c := fun _ _ => rfl
  have hinj : Function.Injective f := by
    rintro ⟨q₁, c₁⟩ ⟨q₂, c₂⟩ h
    induction q₁ using QuotientGroup.induction_on with
    | H e₁ =>
    induction q₂ using QuotientGroup.induction_on with
    | H e₂ =>
    have h1 : (e₁ : G) * v * (e₁ : G)⁻¹ * c₁ = (e₂ : G) * v * (e₂ : G)⁻¹ * c₂ := by
      rw [← hf, ← hf, h]
    have h2 : ((e₂⁻¹ * e₁ : ↥E) : G) * v * ((e₂⁻¹ * e₁ : ↥E) : G)⁻¹ * c₁ = v * c₂ := by
      have hc1 := hcE c₁ c₁.2 _ (e₂⁻¹ : ↥E).2
      have hc2 := hcE c₂ c₂.2 _ (e₂⁻¹ : ↥E).2
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, inv_inv] at hc1 hc2 ⊢
      calc (e₂ : G)⁻¹ * e₁ * v * ((e₂ : G)⁻¹ * e₁)⁻¹ * c₁ =
          (e₂ : G)⁻¹ * ((e₁ : G) * v * (e₁ : G)⁻¹ * c₁) * e₂ *
            ((e₂ : G)⁻¹ * c₁ * e₂)⁻¹ * c₁ := by group
        _ = (e₂ : G)⁻¹ * ((e₂ : G) * v * (e₂ : G)⁻¹ * c₂) * e₂ *
            ((e₂ : G)⁻¹ * c₁ * e₂)⁻¹ * c₁ := by rw [h1]
        _ = v * ((e₂ : G)⁻¹ * c₂ * e₂) * ((e₂ : G)⁻¹ * c₁ * e₂)⁻¹ * c₁ := by group
        _ = v * c₂ := by rw [hc1, hc2]; group
    have hn : e₂⁻¹ * e₁ ∈ N := hkey _ (e₂⁻¹ * e₁).2 c₁ c₁.2 c₂ c₂.2 h2
    have hq : (QuotientGroup.mk e₁ : ↥E ⧸ N) = QuotientGroup.mk e₂ :=
      (QuotientGroup.eq.mpr hn).symm
    have hv' := hfixv e₂ e₁ hn
    have hc : c₁ = c₂ := by
      apply Subtype.ext
      rw [hv'] at h1
      exact mul_left_cancel h1
    rw [hq, hc]
  have hnot : (1 : ↥Bs) ∉ Set.range f := by
    rintro ⟨⟨q, c⟩, hqc⟩
    induction q using QuotientGroup.induction_on with
    | H e =>
    have h1 : (e : G) * v * (e : G)⁻¹ * c = 1 := by rw [← hf, hqc]; rfl
    have hvc : v = (c : G)⁻¹ := by
      have h2 : (e : G) * v * (e : G)⁻¹ = (c : G)⁻¹ := eq_inv_of_mul_eq_one_left h1
      have h3 := hcE (c : G)⁻¹ (C.inv_mem c.2) _ (e⁻¹ : ↥E).2
      simp only [Subgroup.coe_inv, inv_inv] at h3
      calc v = (e : G)⁻¹ * ((e : G) * v * (e : G)⁻¹) * e := by group
        _ = (e : G)⁻¹ * (c : G)⁻¹ * e := by rw [h2]
        _ = (c : G)⁻¹ := h3
    apply hEC
    intro e' he'
    apply hreg e' he'
    have hv1 : e' * v * e'⁻¹ * v⁻¹ = 1 := by
      rw [hvc, hcE _ (C.inv_mem c.2) e' he', mul_inv_cancel]
    rw [hv1]
    exact Subgroup.one_mem _
  have : Fintype ((↥E ⧸ N) × ↥C) := Fintype.ofFinite _
  have : Fintype ↥Bs := Fintype.ofFinite _
  have hlt := Fintype.card_lt_of_injective_of_notMem f hinj hnot
  rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, Nat.card_prod] at hlt
  have hE := Subgroup.card_eq_card_quotient_mul_card_subgroup N
  have hN : Nat.card N = Nat.card (E ⊓ Subgroup.centralizer (Bs : Set G) : Subgroup G) := by
    rw [hNdef, ← Subgroup.card_map_of_injective E.subtype_injective,
      Subgroup.subgroupOf_map_subtype, inf_comm]
  have hpos : 0 < Nat.card N := Nat.card_pos
  calc Nat.card C * Nat.card E = Nat.card (↥E ⧸ N) * Nat.card C * Nat.card N := by
        rw [hE]; ring
    _ < Nat.card Bs * Nat.card N := Nat.mul_lt_mul_of_pos_right hlt hpos
    _ = Nat.card Bs * Nat.card (E ⊓ Subgroup.centralizer (Bs : Set G) : Subgroup G) := by
        rw [hN]

theorem card_mul_lt_of_quadratic [Finite G] {Bs E : Subgroup G}
    (hBc : ∀ a ∈ Bs, ∀ b ∈ Bs, a * b = b * a)
    (hEN : E ≤ Subgroup.normalizer (Bs : Set G)) {v : G} (hv : v ∈ Bs)
    (hreg : ∀ e ∈ E, e ∉ Subgroup.centralizer (Bs : Set G) →
      e * (e * v * e⁻¹ * v⁻¹) * e⁻¹ ≠ e * v * e⁻¹ * v⁻¹)
    (hEC : ¬ E ≤ Subgroup.centralizer (Bs : Set G)) :
    Nat.card (Bs ⊓ Subgroup.centralizer (E : Set G) : Subgroup G) * Nat.card E <
      Nat.card Bs * Nat.card (E ⊓ Subgroup.centralizer (Bs : Set G) : Subgroup G) := by
  refine card_mul_lt_of_regular hBc hEN hv (fun e he hc => ?_) hEC
  by_contra hne
  apply hreg e he hne
  rw [Subgroup.mem_centralizer_iff.mp hc e he, mul_inv_cancel_right]

end Regular

section Coords

variable {G : Type*} [Group G] {F : Type*} [Field F] {ι : Type*} [Fintype ι] [DecidableEq ι]

structure Coords (p : ℕ) (Bs : Subgroup G) (κ : G → ι → Fˣ) : Prop where
  mul : ∀ a ∈ Bs, ∀ b ∈ Bs, κ (a * b) = κ a * κ b
  inj : ∀ a ∈ Bs, ∀ b ∈ Bs, κ a = κ b → a = b
  surj : ∀ t : ι → Fˣ, (∀ i, t i ^ p = 1) → ∃ b ∈ Bs, κ b = t

namespace Coords

variable {p : ℕ} {Bs : Subgroup G} {κ : G → ι → Fˣ}

omit [Fintype ι] [DecidableEq ι]

theorem one (h : Coords p Bs κ) : κ 1 = 1 := by
  have h1 := h.mul 1 Bs.one_mem 1 Bs.one_mem
  rw [mul_one] at h1
  exact left_eq_mul.mp h1

theorem inv (h : Coords p Bs κ) {b : G} (hb : b ∈ Bs) : κ b⁻¹ = (κ b)⁻¹ := by
  have h1 := h.mul b hb b⁻¹ (Bs.inv_mem hb)
  rw [mul_inv_cancel, h.one] at h1
  exact (eq_inv_of_mul_eq_one_right h1.symm)

theorem pow (h : Coords p Bs κ) {b : G} (hb : b ∈ Bs) (k : ℕ) : κ (b ^ k) = κ b ^ k := by
  induction k with
  | zero => rw [pow_zero, pow_zero, h.one]
  | succ k ih => rw [pow_succ, pow_succ, h.mul _ (Bs.pow_mem hb k) _ hb, ih]

theorem pow_p (h : Coords p Bs κ) {b : G} (hb : b ∈ Bs) (hbp : b ^ p = 1) (i : ι) :
    κ b i ^ p = 1 := by
  have h1 := congrFun (h.pow hb p) i
  rw [hbp, h.one] at h1
  rw [← Pi.pow_apply, ← h1]
  rfl

end Coords

variable {p : ℕ} {Bs E : Subgroup G} {κ : G → ι → Fˣ}

omit [Fintype ι]

theorem eq_of_supp {ζ : Fˣ} (hζ1 : ζ ≠ 1) (hζp : ζ ^ p = 1) (h : Coords p Bs κ) {e : G}
    {τ τ' : Equiv.Perm ι}
    (hτ : ∀ b ∈ Bs, ∀ i, κ (e * b * e⁻¹) (τ i) = 1 ↔ κ b i = 1)
    (hτ' : ∀ b ∈ Bs, ∀ i, κ (e * b * e⁻¹) (τ' i) = 1 ↔ κ b i = 1) : τ = τ' := by
  ext i
  obtain ⟨a, ha, hai⟩ := h.surj (Pi.mulSingle i ζ) fun j => by
    by_cases hj : j = i
    · rw [hj, Pi.mulSingle_eq_same, hζp]
    · rw [Pi.mulSingle_eq_of_ne hj, one_pow]
  have h1 : κ (e * a * e⁻¹) (τ i) ≠ 1 := fun h1 => by
    have := (hτ a ha i).mp h1
    rw [hai, Pi.mulSingle_eq_same] at this
    exact hζ1 this
  set j := τ'.symm (τ i) with hj
  have h2 : κ (e * a * e⁻¹) (τ' j) ≠ 1 := by rwa [hj, Equiv.apply_symm_apply]
  have h3 : κ a j ≠ 1 := fun h3 => h2 ((hτ' a ha j).mpr h3)
  have hji : j = i := by
    by_contra hne
    rw [hai, Pi.mulSingle_eq_of_ne hne] at h3
    exact h3 rfl
  have hj2 : τ' j = τ i := by rw [hj, Equiv.apply_symm_apply]
  rw [hji] at hj2
  exact hj2.symm

theorem exists_hom_of_supp [Finite G] {ζ : Fˣ} (hζ1 : ζ ≠ 1) (hζp : ζ ^ p = 1)
    (h : Coords p Bs κ) (hEN : E ≤ Subgroup.normalizer (Bs : Set G))
    (hmono : ∀ e ∈ E, ∃ τ : Equiv.Perm ι, ∀ b ∈ Bs, ∀ i,
      κ (e * b * e⁻¹) (τ i) = 1 ↔ κ b i = 1) :
    ∃ T : ↥E →* Equiv.Perm ι, ∀ e : ↥E, ∀ b ∈ Bs, ∀ i,
      κ ((e : G) * b * (e : G)⁻¹) (T e i) = 1 ↔ κ b i = 1 := by
  choose τ hτ using hmono
  have hconj : ∀ e ∈ E, ∀ b ∈ Bs, e * b * e⁻¹ ∈ Bs := fun e he b hb =>
    (Subgroup.mem_normalizer_iff.mp (hEN he) b).mp hb
  refine ⟨{ toFun := fun e => τ e e.2, map_one' := ?_, map_mul' := ?_ }, fun e => hτ e e.2⟩
  · refine (eq_of_supp hζ1 hζp h (hτ 1 E.one_mem) fun b _ i => ?_)
    simp only [one_mul, inv_one, mul_one, Equiv.Perm.one_apply]
  · intro a b
    refine eq_of_supp hζ1 hζp h (hτ _ (a * b).2) fun x hx i => ?_
    simp only [Subgroup.coe_mul, Equiv.Perm.mul_apply, mul_inv_rev]
    have e1 : (a : G) * b * x * ((b : G)⁻¹ * (a : G)⁻¹) = a * (b * x * (b : G)⁻¹) * (a : G)⁻¹ := by
      group
    rw [e1, hτ a a.2 _ (hconj b b.2 x hx), hτ b b.2 x hx]

theorem mem_centralizer_of_supp {ζ : F} (hp : p.Prime) (hζ : IsPrimitiveRoot ζ p)
    (h : Coords p Bs κ) (hBp : ∀ b ∈ Bs, b ^ p = 1) {e : G}
    (he : e ∈ Subgroup.normalizer (Bs : Set G)) (hep : e ^ p = 1)
    (hfix : ∀ b ∈ Bs, ∀ i, κ (e * b * e⁻¹) i = 1 ↔ κ b i = 1) :
    e ∈ Subgroup.centralizer (Bs : Set G) := by
  have : NeZero p := ⟨hp.ne_zero⟩
  have : Fact p.Prime := ⟨hp⟩
  have hconj : ∀ b ∈ Bs, e * b * e⁻¹ ∈ Bs := fun b hb =>
    (Subgroup.mem_normalizer_iff.mp he b).mp hb
  set ζu : Fˣ := (hζ.isUnit hp.ne_zero).unit with hζudef
  have hζu : (ζu : F) = ζ := IsUnit.unit_spec _
  have hζup : ζu ^ p = 1 :=
    Units.ext (by rw [Units.val_pow_eq_pow_val, hζu, hζ.pow_eq_one, Units.val_one])
  have hord : orderOf ζu = p :=
    ((IsPrimitiveRoot.coe_units_iff.mp (hζu ▸ hζ : IsPrimitiveRoot (ζu : F) p)).eq_orderOf).symm
  have hpow : ∀ z : Fˣ, z ^ p = 1 → ∃ c < p, ζu ^ c = z := fun z hz => by
    obtain ⟨c, hc, hcz⟩ := hζ.eq_pow_of_pow_eq_one (ξ := (z : F))
      (by rw [← Units.val_pow_eq_pow_val, hz, Units.val_one])
    exact ⟨c, hc, Units.ext (by rw [Units.val_pow_eq_pow_val, hζu, hcz])⟩
  have haxis : ∀ i (z : Fˣ), z ^ p = 1 → ∃ a ∈ Bs, κ a = Pi.mulSingle i z := fun i z hz =>
    h.surj _ fun j => by
      by_cases hj : j = i
      · rw [hj, Pi.mulSingle_eq_same, hz]
      · rw [Pi.mulSingle_eq_of_ne hj, one_pow]
  have hfixζ : ∀ i, ∀ a ∈ Bs, κ a = Pi.mulSingle i ζu → e * a * e⁻¹ = a := by
    intro i a ha hai
    have ha' := hconj a ha
    have hsupp : ∀ j, j ≠ i → κ (e * a * e⁻¹) j = 1 := fun j hj =>
      (hfix a ha j).mpr (by rw [hai, Pi.mulSingle_eq_of_ne hj])
    obtain ⟨c, -, hc⟩ := hpow (κ (e * a * e⁻¹) i)
      (h.pow_p ha' (by rw [conj_pow, hBp a ha, mul_one, mul_inv_cancel]) i)
    have hea : e * a * e⁻¹ = a ^ c := h.inj _ ha' _ (Bs.pow_mem ha c) (by
      funext j
      rw [h.pow ha, Pi.pow_apply, hai]
      by_cases hj : j = i
      · subst hj
        rw [Pi.mulSingle_eq_same, hc]
      · rw [hsupp j hj, Pi.mulSingle_eq_of_ne hj, one_pow])
    have hiter : ∀ m : ℕ, e ^ m * a * (e ^ m)⁻¹ = a ^ (c ^ m) := by
      intro m
      induction m with
      | zero => simp
      | succ m ih =>
        calc e ^ (m + 1) * a * (e ^ (m + 1))⁻¹ = e * (e ^ m * a * (e ^ m)⁻¹) * e⁻¹ := by
              rw [pow_succ']
              group
          _ = e * a ^ (c ^ m) * e⁻¹ := by rw [ih]
          _ = (e * a * e⁻¹) ^ (c ^ m) := by rw [conj_pow]
          _ = a ^ (c ^ (m + 1)) := by rw [hea, ← pow_mul, pow_succ', mul_comm]
    have hp1 := hiter p
    rw [hep, one_mul, inv_one, mul_one] at hp1
    have hζeq : ζu ^ (c ^ p) = ζu ^ 1 := by
      have h2 := congrFun (congrArg κ hp1) i
      rw [h.pow ha, Pi.pow_apply, hai, Pi.mulSingle_eq_same] at h2
      rw [pow_one]
      exact h2.symm
    rw [pow_eq_pow_iff_modEq, hord] at hζeq
    have hc1 : c ≡ 1 [MOD p] := by
      have := (ZMod.natCast_eq_natCast_iff _ _ _).mpr hζeq
      rw [Nat.cast_pow, ZMod.pow_card, Nat.cast_one] at this
      exact (ZMod.natCast_eq_natCast_iff _ _ _).mp (by rw [this, Nat.cast_one])
    have hζc : ζu ^ c = ζu := by
      have hc1' : c ≡ 1 [MOD orderOf ζu] := by rw [hord]; exact hc1
      have h3 := pow_eq_pow_iff_modEq.mpr hc1'
      rwa [pow_one] at h3
    rw [hea]
    apply h.inj _ (Bs.pow_mem ha c) _ ha
    rw [h.pow ha, hai]
    funext j
    rw [Pi.pow_apply]
    by_cases hj : j = i
    · subst hj
      rw [Pi.mulSingle_eq_same, hζc]
    · rw [Pi.mulSingle_eq_of_ne hj, one_pow]
  have hfixall : ∀ i, ∀ a ∈ Bs, (∀ j, j ≠ i → κ a j = 1) → e * a * e⁻¹ = a := by
    intro i a ha hsupp
    obtain ⟨k, -, hk⟩ := hpow (κ a i) (h.pow_p ha (hBp a ha) i)
    obtain ⟨a₀, ha₀, ha₀i⟩ := haxis i ζu hζup
    have haa : a = a₀ ^ k := h.inj _ ha _ (Bs.pow_mem ha₀ k) (by
      funext j
      rw [h.pow ha₀, Pi.pow_apply, ha₀i]
      by_cases hj : j = i
      · subst hj
        rw [Pi.mulSingle_eq_same, hk]
      · rw [hsupp j hj, Pi.mulSingle_eq_of_ne hj, one_pow])
    rw [haa, ← conj_pow, hfixζ i a₀ ha₀ ha₀i]
  rw [Subgroup.mem_centralizer_iff]
  intro b hb
  have heb : e * b * e⁻¹ = b := by
    apply h.inj _ (hconj b hb) _ hb
    funext i
    obtain ⟨a, ha, hai⟩ := haxis i (κ b i) (h.pow_p hb (hBp b hb) i)
    have hb' : a⁻¹ * b ∈ Bs := Bs.mul_mem (Bs.inv_mem ha) hb
    have hb'i : κ (a⁻¹ * b) i = 1 := by
      rw [h.mul _ (Bs.inv_mem ha) _ hb, h.inv ha, Pi.mul_apply, Pi.inv_apply, hai,
        Pi.mulSingle_eq_same, inv_mul_cancel]
    have e1 : e * b * e⁻¹ = (e * a * e⁻¹) * (e * (a⁻¹ * b) * e⁻¹) := by group
    rw [e1, h.mul _ (hconj a ha) _ (hconj _ hb'), Pi.mul_apply, (hfix _ hb' i).mpr hb'i, mul_one,
      hfixall i a ha (fun j hj => by rw [hai, Pi.mulSingle_eq_of_ne hj]), hai,
      Pi.mulSingle_eq_same]
  calc b * e = (e * b * e⁻¹) * e := by rw [heb]
    _ = e * b := by group

end Coords

section Main

variable {G : Type*} [Group G] [Finite G] {F : Type*} [Field F] {ι : Type*} [Fintype ι]
  [LinearOrder ι]

theorem exists_regular_of_coords {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {ζ : F}
    (hζ : IsPrimitiveRoot ζ p) {Bs E : Subgroup G} {κ : G → ι → Fˣ} (h : Coords p Bs κ)
    (hBp : ∀ b ∈ Bs, b ^ p = 1) (hEp : ∀ e ∈ E, e ^ p = 1)
    (hEc : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a) (hEN : E ≤ Subgroup.normalizer (Bs : Set G))
    (hmono : ∀ e ∈ E, ∃ τ : Equiv.Perm ι, ∀ b ∈ Bs, ∀ i,
      κ (e * b * e⁻¹) (τ i) = 1 ↔ κ b i = 1) :
    ∃ v ∈ Bs, ∀ e ∈ E, e ∉ Subgroup.centralizer (Bs : Set G) →
      e * (e * v * e⁻¹ * v⁻¹) * e⁻¹ ≠ e * v * e⁻¹ * v⁻¹ := by
  classical
  have : NeZero p := ⟨hp.ne_zero⟩
  set ζu : Fˣ := (hζ.isUnit hp.ne_zero).unit with hζudef
  have hζu : (ζu : F) = ζ := IsUnit.unit_spec _
  have hζup : ζu ^ p = 1 :=
    Units.ext (by rw [Units.val_pow_eq_pow_val, hζu, hζ.pow_eq_one, Units.val_one])
  have hζu1 : ζu ≠ 1 := fun h1 => hζ.ne_one hp.one_lt (by rw [← hζu, h1, Units.val_one])
  obtain ⟨T, hT⟩ := exists_hom_of_supp hζu1 hζup h hEN hmono
  have : Fintype ↥E := Fintype.ofFinite _
  have hconj : ∀ e ∈ E, ∀ b ∈ Bs, e * b * e⁻¹ ∈ Bs := fun e he b hb =>
    (Subgroup.mem_normalizer_iff.mp (hEN he) b).mp hb
  set X : Set ι := {x | ∀ g : ↥E, x ≤ T g x} with hXdef
  obtain ⟨v, hv, hvX⟩ := h.surj (fun i => if i ∈ X then ζu else 1) fun i => by
    split_ifs
    · exact hζup
    · exact one_pow p
  have hvx : ∀ i, κ v i = if i ∈ X then ζu else 1 := fun i => by rw [hvX]
  refine ⟨v, hv, fun e he heC => ?_⟩
  set e' : ↥E := ⟨e, he⟩ with he'
  have hT1 : T e' ≠ 1 := by
    intro h1
    apply heC
    refine mem_centralizer_of_supp hp hζ h hBp (hEN he) (hEp e he) fun b hb i => ?_
    have h2 := hT e' b hb i
    rwa [h1, Equiv.Perm.one_apply] at h2
  obtain ⟨y, hy⟩ : ∃ y, T e' y ≠ y := by
    by_contra hne
    push Not at hne
    exact hT1 (Equiv.ext hne)
  set S : Finset ι := Finset.univ.image (fun g : ↥E => T g y) with hS
  have hSne : S.Nonempty := ⟨T 1 y, Finset.mem_image_of_mem _ (Finset.mem_univ _)⟩
  obtain ⟨g₀, -, hg₀⟩ := Finset.mem_image.mp (S.min'_mem hSne)
  set x := S.min' hSne with hx
  have hxX : x ∈ X := fun g => by
    apply S.min'_le
    rw [← hg₀, ← Equiv.Perm.mul_apply, ← map_mul]
    exact Finset.mem_image_of_mem _ (Finset.mem_univ _)
  have hTex : T e' x ≠ x := by
    intro h1
    rw [← hg₀, ← Equiv.Perm.mul_apply, ← map_mul,
      show e' * g₀ = g₀ * e' from Subtype.ext (hEc e he g₀ g₀.2), map_mul,
      Equiv.Perm.mul_apply] at h1
    exact hy ((T g₀).injective h1)
  have hw : T e' x ∉ X := by
    intro hwX
    have h1 := hwX e'⁻¹
    rw [← Equiv.Perm.mul_apply, ← map_mul, inv_mul_cancel, map_one, Equiv.Perm.one_apply] at h1
    exact hTex (le_antisymm h1 (hxX e'))
  have hT2 : T e' (T e' x) ≠ x := by
    intro h2
    have hk : ∀ k : ℕ, (T e' ^ (2 * k)) x = x := by
      intro k
      induction k with
      | zero => rfl
      | succ k ih =>
        rw [show 2 * (k + 1) = 2 * k + 2 by ring, pow_add, Equiv.Perm.mul_apply, pow_two,
          Equiv.Perm.mul_apply, h2, ih]
    obtain ⟨k, hk2⟩ := (hp.odd_of_ne_two hp2)
    have hpe : T e' ^ p = 1 := by
      rw [← map_pow, show e' ^ p = 1 from Subtype.ext (by simpa using hEp e he), map_one]
    have h3 := congrArg (fun σ : Equiv.Perm ι => σ x) hpe
    simp only [Equiv.Perm.one_apply] at h3
    rw [hk2, pow_succ', Equiv.Perm.mul_apply, hk k] at h3
    exact hTex h3
  have hw' : T e' (T e' x) ∉ X := by
    intro hwX
    have h1 := hwX (e'⁻¹ * e'⁻¹)
    have e1 : T (e'⁻¹ * e'⁻¹) (T e' (T e' x)) = x := by
      have h4 : e'⁻¹ * e'⁻¹ * e' * e' = 1 := by group
      rw [show T (e'⁻¹ * e'⁻¹) (T e' (T e' x)) = (T (e'⁻¹ * e'⁻¹) * T e' * T e') x from rfl,
        ← map_mul, ← map_mul, h4, map_one, Equiv.Perm.one_apply]
    rw [e1] at h1
    have h2 := hxX (e' * e')
    rw [map_mul, Equiv.Perm.mul_apply] at h2
    exact hT2 (le_antisymm h1 h2)
  have hv' : v⁻¹ ∈ Bs := Bs.inv_mem hv
  have hu : e * v * e⁻¹ * v⁻¹ ∈ Bs := Bs.mul_mem (hconj e he v hv) hv'
  have hκu : ∀ i, κ (e * v * e⁻¹ * v⁻¹) i = κ (e * v * e⁻¹) i * (κ v i)⁻¹ := fun i => by
    rw [h.mul _ (hconj e he v hv) _ hv', h.inv hv, Pi.mul_apply, Pi.inv_apply]
  have h1 : κ (e * v * e⁻¹ * v⁻¹) (T e' x) ≠ 1 := by
    rw [hκu, hvx, ite_eq_right hw, inv_one, mul_one]
    intro h0
    have h3 := (hT e' v hv x).mp h0
    rw [hvx, ite_eq_left hxX] at h3
    exact hζu1 h3
  have h2 : κ (e * v * e⁻¹ * v⁻¹) (T e' (T e' x)) = 1 := by
    rw [hκu, (hT e' v hv (T e' x)).mpr (by rw [hvx, ite_eq_right hw]), one_mul, hvx,
      ite_eq_right hw', inv_one]
  intro hfix
  apply h1
  have h3 := (hT e' _ hu (T e' x)).mp
  rw [he'] at h3
  simp only at h3
  rw [hfix] at h3
  exact h3 h2

theorem card_mul_lt_of_coords {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {ζ : F}
    (hζ : IsPrimitiveRoot ζ p) {Bs E : Subgroup G} {κ : G → ι → Fˣ} (h : Coords p Bs κ)
    (hBs : IsElemAbelian p Bs) (hE : IsElemAbelian p E)
    (hEN : E ≤ Subgroup.normalizer (Bs : Set G))
    (hmono : ∀ e ∈ E, ∃ τ : Equiv.Perm ι, ∀ b ∈ Bs, ∀ i,
      κ (e * b * e⁻¹) (τ i) = 1 ↔ κ b i = 1)
    (hEC : ¬ E ≤ Subgroup.centralizer (Bs : Set G)) :
    Nat.card (Bs ⊓ Subgroup.centralizer (E : Set G) : Subgroup G) * Nat.card E <
      Nat.card Bs * Nat.card (E ⊓ Subgroup.centralizer (Bs : Set G) : Subgroup G) := by
  obtain ⟨v, hv, hreg⟩ := exists_regular_of_coords hp hp2 hζ h hBs.2 hE.2
    (fun a ha b hb => TableB.IsElemAbelian.comm hE ha hb) hEN hmono
  exact card_mul_lt_of_quadratic (fun a ha b hb => TableB.IsElemAbelian.comm hBs ha hb) hEN hv
    hreg hEC

end Main

end NoOffenderClassical

end CFSG.StandardType
