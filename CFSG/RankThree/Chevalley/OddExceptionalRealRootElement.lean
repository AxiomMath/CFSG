module

public import CFSG.LieType.Chevalley.AdjointCenter
public import CFSG.LieType.Chevalley.RankOneCentralImage
public import CFSG.LieType.Chevalley.GraphFixedFinitePerfect
public import CFSG.LieType.Chevalley.GraphFixedCenterTrivial

public noncomputable section

namespace CFSG.RankThree.Chevalley

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial CFSG.Assembly.LowTwoRank

theorem exists_real_of_injective {G S : Type*} [Group G] [Group S] (φ : G →* S)
    (hφ : Function.Injective φ) {p : ℕ} {x z b : G} (hx : orderOf x = p) (hz : orderOf z = 2)
    (hxz : x * z = z * x) (hb : b * x * b⁻¹ = x⁻¹) :
    ∃ x z b : S, orderOf x = p ∧ orderOf z = 2 ∧ x * z = z * x ∧ b * x * b⁻¹ = x⁻¹ :=
  ⟨φ x, φ z, φ b, by rw [orderOf_injective φ hφ, hx], by rw [orderOf_injective φ hφ, hz],
    by rw [← map_mul, ← map_mul, hxz], by rw [← map_inv, ← map_mul, ← map_mul, hb, map_inv]⟩

theorem exists_real_of_injective_subgroup {G S : Type*} [Group G] [Group S] {C : Subgroup G}
    (φ : C →* S) (hφ : Function.Injective φ) {p : ℕ} {x z b : G} (hxC : x ∈ C) (hzC : z ∈ C)
    (hbC : b ∈ C) (hx : orderOf x = p) (hz : orderOf z = 2) (hxz : x * z = z * x)
    (hb : b * x * b⁻¹ = x⁻¹) :
    ∃ x z b : S, orderOf x = p ∧ orderOf z = 2 ∧ x * z = z * x ∧ b * x * b⁻¹ = x⁻¹ :=
  exists_real_of_injective φ hφ (x := ⟨x, hxC⟩) (z := ⟨z, hzC⟩) (b := ⟨b, hbC⟩)
    (by rw [Subgroup.orderOf_mk, hx]) (by rw [Subgroup.orderOf_mk, hz]) (Subtype.ext hxz)
    (Subtype.ext hb)

theorem two_ne_zero_of_charP {K : Type*} [Field K] {p : ℕ} [Fact p.Prime] [CharP K p]
    (hp2 : p ≠ 2) : (2 : K) ≠ 0 := by
  intro h
  have h' : ((2 : ℕ) : K) = 0 := by exact_mod_cast h
  rw [CharP.cast_eq_zero_iff K p] at h'
  exact hp2 ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).1 h')

section Elements

variable {τ : Tag} {K : Type} [Field K]

theorem xUnit_pow (i : Fin τ.rank) (c : K) (n : ℕ) :
    xUnit τ K i c ^ n = xUnit τ K i (n * c) := by
  induction n with
  | zero => rw [pow_zero, Nat.cast_zero, zero_mul, xUnit_zero]
  | succ n ih => rw [pow_succ, ih, ← xUnit_add, Nat.cast_succ, add_mul, one_mul]

theorem torusElt_neg_one_conj_xUnit_of_odd {i j : Fin τ.rank} (h : Odd (τ.cartan j i)) (c : K) :
    torusElt τ K j (-1) * xUnit τ K i c * (torusElt τ K j (-1))⁻¹ = xUnit τ K i (-c) := by
  rw [(simple_torus_root_conjugation τ K j i (-1) c).1, h.neg_one_zpow, Units.val_neg,
    Units.val_one, neg_one_mul]

theorem torusElt_neg_one_conj_xUnit_self (i : Fin τ.rank) (c : K) :
    torusElt τ K i (-1) * xUnit τ K i c * (torusElt τ K i (-1))⁻¹ = xUnit τ K i c := by
  rw [(simple_torus_root_conjugation τ K i i (-1) c).1, Tag.cartan_self,
    (even_two : Even (2 : ℤ)).neg_one_zpow, Units.val_one, one_mul]

theorem xUnit_mul_torusElt_neg_one_comm (i : Fin τ.rank) (c : K) :
    xUnit τ K i c * torusElt τ K i (-1) = torusElt τ K i (-1) * xUnit τ K i c :=
  (mul_inv_eq_iff_eq_mul.1 (torusElt_neg_one_conj_xUnit_self i c)).symm

theorem torusElt_neg_one_sq (i : Fin τ.rank) : torusElt τ K i (-1) ^ 2 = 1 := by
  rw [sq, ← torusElt_mul, neg_one_mul, neg_neg, torusElt_one]

theorem orderOf_xUnit_one {p : ℕ} [Fact p.Prime] [CharP K p] (i : Fin τ.rank) :
    orderOf (xUnit τ K i 1) = p := by
  obtain ⟨-, -, -, -, -, -, -, hinj, -⟩ := exceptional_ordinary_rank_one_central_image τ K i
  refine orderOf_eq_prime ?_ fun h => one_ne_zero (hinj (h.trans (xUnit_zero i).symm))
  rw [xUnit_pow, mul_one, CharP.cast_eq_zero, xUnit_zero]

theorem orderOf_torusElt_neg_one {i j : Fin τ.rank} (hij : Odd (τ.cartan i j))
    (h2 : (2 : K) ≠ 0) : orderOf (torusElt τ K i (-1)) = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, -, -, -, -, -, -, hinj, -⟩ := exceptional_ordinary_rank_one_central_image τ K j
  refine orderOf_eq_prime (torusElt_neg_one_sq i) fun h => h2 ?_
  have hc := torusElt_neg_one_conj_xUnit_of_odd (K := K) hij 1
  rw [h, one_mul, inv_one, mul_one] at hc
  have h1 := hinj hc
  linear_combination h1

end Elements

theorem exists_real_root_element_adjointQuotient {τ : Tag} {K : Type} [Field K] [Finite K]
    {p : ℕ} [Fact p.Prime] [CharP K p] (h2 : (2 : K) ≠ 0) {i j : Fin τ.rank}
    (hij : Odd (τ.cartan i j)) (hji : Odd (τ.cartan j i)) :
    ∃ x z b : AdjointQuotient τ K, orderOf x = p ∧ orderOf z = 2 ∧ x * z = z * x ∧
      b * x * b⁻¹ = x⁻¹ := by
  have hinj : Function.Injective (QuotientGroup.mk' (Subgroup.center (adjointGroup τ K))) := by
    rw [← MonoidHom.ker_eq_bot_iff, QuotientGroup.ker_mk']
    exact center_adjointGroup_eq_bot
  refine exists_real_of_injective_subgroup _ hinj (xUnit_mem_adjointGroup i 1)
    (torusElt_mem_adjointGroup i (-1)) (torusElt_mem_adjointGroup j (-1)) (orderOf_xUnit_one i)
    (orderOf_torusElt_neg_one hij h2) (xUnit_mul_torusElt_neg_one_comm i 1) ?_
  rw [torusElt_neg_one_conj_xUnit_of_odd hji, xUnit_neg]

theorem exists_real_root_element_of_untwisted (S : Type) [Group S] (τ : Tag) {p f : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f) {i j : Fin τ.rank} (hij : Odd (τ.cartan i j))
    (hji : Odd (τ.cartan j i)) (h : UntwistedChevalleyModel S τ (p ^ f)) :
    ∃ x z b : S, orderOf x = p ∧ orderOf z = 2 ∧ x * z = z * x ∧ b * x * b⁻¹ = x⁻¹ := by
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := h
  have : Fact p.Prime := ⟨hp⟩
  have : CharP K p := finite_field_prime_power_characteristic hp hf hK
  obtain ⟨x, z, b, hx, hz, hxz, hb⟩ :=
    exists_real_root_element_adjointQuotient (K := K) (two_ne_zero_of_charP hp2) hij hji
  exact exists_real_of_injective e.symm.toMonoidHom e.symm.injective hx hz hxz hb

section Twisted

variable {t : TwistTag} {K : Type} [Field K]

theorem units_map_neg_one {R R' : Type*} [Ring R] [Ring R'] (g : R →+* R') :
    Units.map g.toMonoidHom (-1 : Rˣ) = -1 :=
  Units.ext (by simp)

theorem coe_orbitH_neg_one (σ : K →+* K) (a : Fin t.foldedTag.rank) :
    (orbitH t K σ a (-1) : ModGL t.tag K) = ((List.range (t.orbit a).card).map fun k =>
      torusElt t.tag K ((t.perm ^ k) (t.orbitMin a)) (-1)).prod := by
  rw [coe_orbitH]
  simp only [units_map_neg_one]

theorem orbitMin_orbitIndex_of_singleton {i : Fin t.tag.rank}
    (hi : t.orbit (t.orbitIndex i) = {i}) : t.orbitMin (t.orbitIndex i) = i := by
  have h := t.orbitMin_mem (t.orbitIndex i)
  rw [hi] at h
  exact Finset.mem_singleton.1 h

theorem xUnit_mem_graphFixedRootGroup_of_singleton (σ : K →+* K) {i : Fin t.tag.rank}
    (hi : t.orbit (t.orbitIndex i) = {i}) {c : K} (hc : σ c = c) :
    xUnit t.tag K i c ∈ graphFixedRootGroup t K σ := by
  have h1 : (t.orbit (t.orbitIndex i)).card = 1 := by rw [hi, Finset.card_singleton]
  have hcL : c ∈ orbitField t K σ (t.orbitIndex i) := by
    rw [mem_orbitField, h1, pow_one]
    exact hc
  have hm := graphFixedPosUnipotent_le_graphFixedRootGroup t K σ
    (orbitX_mem_graphFixedPosUnipotent t σ (t.orbitIndex i) ⟨c, hcL⟩)
  rwa [coe_orbitX_of_card_eq_one h1, orbitMin_orbitIndex_of_singleton hi] at hm

theorem torusElt_neg_one_mem_graphFixedRootGroup_of_singleton (σ : K →+* K)
    {i : Fin t.tag.rank} (hi : t.orbit (t.orbitIndex i) = {i}) :
    torusElt t.tag K i (-1) ∈ graphFixedRootGroup t K σ := by
  have h1 : (t.orbit (t.orbitIndex i)).card = 1 := by rw [hi, Finset.card_singleton]
  have hm := orbitH_mem_graphFixedRootGroup t σ (t.orbitIndex i) (-1)
  rw [coe_orbitH_neg_one, h1, orbitMin_orbitIndex_of_singleton hi] at hm
  simpa using hm

theorem exists_real_root_element_twistedE6 (σ : K →+* K) {p : ℕ} [Fact p.Prime] [CharP K p]
    (h2 : (2 : K) ≠ 0) :
    ∃ x ∈ graphFixedRootGroup .E6 K σ, ∃ z ∈ graphFixedRootGroup .E6 K σ,
      ∃ b ∈ graphFixedRootGroup .E6 K σ,
        orderOf x = p ∧ orderOf z = 2 ∧ x * z = z * x ∧ b * x * b⁻¹ = x⁻¹ := by
  refine ⟨xUnit TwistTag.E6.tag K ⟨1, by decide⟩ 1,
    xUnit_mem_graphFixedRootGroup_of_singleton σ (by decide) (map_one σ),
    torusElt TwistTag.E6.tag K ⟨1, by decide⟩ (-1),
    torusElt_neg_one_mem_graphFixedRootGroup_of_singleton σ (by decide),
    torusElt TwistTag.E6.tag K ⟨3, by decide⟩ (-1),
    torusElt_neg_one_mem_graphFixedRootGroup_of_singleton σ (by decide),
    orderOf_xUnit_one _, orderOf_torusElt_neg_one (j := ⟨3, by decide⟩) (by decide) h2,
    xUnit_mul_torusElt_neg_one_comm _ 1, ?_⟩
  rw [torusElt_neg_one_conj_xUnit_of_odd (by decide), xUnit_neg]

theorem exists_real_root_element_trialityD4 (σ : K →+* K) {p : ℕ} [Fact p.Prime] [CharP K p]
    (h2 : (2 : K) ≠ 0) :
    ∃ x ∈ graphFixedRootGroup .D4 K σ, ∃ z ∈ graphFixedRootGroup .D4 K σ,
      ∃ b ∈ graphFixedRootGroup .D4 K σ,
        orderOf x = p ∧ orderOf z = 2 ∧ x * z = z * x ∧ b * x * b⁻¹ = x⁻¹ := by
  have hb : torusElt TwistTag.D4.tag K ⟨0, by decide⟩ (-1) *
      (torusElt TwistTag.D4.tag K ⟨1, by decide⟩ (-1) *
        torusElt TwistTag.D4.tag K ⟨3, by decide⟩ (-1)) ∈ graphFixedRootGroup .D4 K σ := by
    have hm := orbitH_mem_graphFixedRootGroup TwistTag.D4 σ ⟨0, by decide⟩ (-1)
    have e0 : (TwistTag.D4.perm ^ 0) (TwistTag.D4.orbitMin ⟨0, by decide⟩) = ⟨0, by decide⟩ := by
      decide
    have e1 : (TwistTag.D4.perm ^ 1) (TwistTag.D4.orbitMin ⟨0, by decide⟩) = ⟨1, by decide⟩ := by
      decide
    have e2 : (TwistTag.D4.perm ^ 2) (TwistTag.D4.orbitMin ⟨0, by decide⟩) = ⟨3, by decide⟩ := by
      decide
    have hc : (TwistTag.D4.orbit ⟨0, by decide⟩).card = 3 := by decide
    rw [coe_orbitH_neg_one, hc] at hm
    simpa only [show List.range 3 = [0, 1, 2] from rfl, List.map_cons, List.map_nil,
      List.prod_cons, List.prod_nil, mul_one, e0, e1, e2] using hm
  refine ⟨xUnit TwistTag.D4.tag K ⟨2, by decide⟩ 1,
    xUnit_mem_graphFixedRootGroup_of_singleton σ (by decide) (map_one σ),
    torusElt TwistTag.D4.tag K ⟨2, by decide⟩ (-1),
    torusElt_neg_one_mem_graphFixedRootGroup_of_singleton σ (by decide), _, hb,
    orderOf_xUnit_one _, orderOf_torusElt_neg_one (j := ⟨0, by decide⟩) (by decide) h2,
    xUnit_mul_torusElt_neg_one_comm _ 1, ?_⟩
  set d₀ := torusElt TwistTag.D4.tag K ⟨0, by decide⟩ (-1)
  set d₁ := torusElt TwistTag.D4.tag K ⟨1, by decide⟩ (-1)
  set d₃ := torusElt TwistTag.D4.tag K ⟨3, by decide⟩ (-1)
  set x := xUnit TwistTag.D4.tag K ⟨2, by decide⟩ 1
  have e : d₀ * (d₁ * d₃) * x * (d₀ * (d₁ * d₃))⁻¹ =
      d₀ * (d₁ * (d₃ * x * d₃⁻¹) * d₁⁻¹) * d₀⁻¹ := by
    group
  rw [e, torusElt_neg_one_conj_xUnit_of_odd (by decide), torusElt_neg_one_conj_xUnit_of_odd
    (by decide), torusElt_neg_one_conj_xUnit_of_odd (by decide), neg_neg, xUnit_neg]

theorem exists_real_of_graphFixedRootGroup [Finite K] {σ : K →+* K} {p f : ℕ} (hp : p.Prime)
    (hf : 1 ≤ f) (hK : Nat.card K = (p ^ f) ^ t.order) (hσ : ∀ c, σ c = c ^ (p ^ f))
    {x z b : ModGL t.tag K} (hx : x ∈ graphFixedRootGroup t K σ)
    (hz : z ∈ graphFixedRootGroup t K σ) (hb : b ∈ graphFixedRootGroup t K σ)
    (hxo : orderOf x = p) (hzo : orderOf z = 2) (hxz : x * z = z * x)
    (hbx : b * x * b⁻¹ = x⁻¹) :
    ∃ x z b : DerivedCentralQuotient (twistedFixedGroup t K σ),
      orderOf x = p ∧ orderOf z = 2 ∧ x * z = z * x ∧ b * x * b⁻¹ = x⁻¹ := by
  obtain ⟨-, -, hΓ, -, -⟩ := finite_fixed_root_group_perfect t hp hf K hK σ hσ
  have hsurj : Function.Surjective σ := Finite.surjective_of_injective σ.injective
  have hZ : Subgroup.center ↥⁅twistedFixedGroup t K σ, twistedFixedGroup t K σ⁆ = ⊥ := by
    rw [hΓ]
    exact center_graphFixedRootGroup_eq_bot hsurj
  have hinj : Function.Injective (QuotientGroup.mk'
      (Subgroup.center ↥⁅twistedFixedGroup t K σ, twistedFixedGroup t K σ⁆)) := by
    rw [← MonoidHom.ker_eq_bot_iff, QuotientGroup.ker_mk']
    exact hZ
  rw [← hΓ] at hx hz hb
  exact exists_real_of_injective_subgroup _ hinj hx hz hb hxo hzo hxz hbx

end Twisted

theorem exists_real_root_element_of_twisted (S : Type) [Group S] (t : TwistTag) {p f : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f) (h : TwistedChevalleyModel S t (p ^ f)) :
    ∃ x z b : S, orderOf x = p ∧ orderOf z = 2 ∧ x * z = z * x ∧ b * x * b⁻¹ = x⁻¹ := by
  obtain ⟨K, _, _, hK, σ, hσ, ⟨e⟩⟩ := h
  have : Fact p.Prime := ⟨hp⟩
  have hK' : Nat.card K = p ^ (f * t.order) := by rw [hK, ← pow_mul]
  have hfm : 1 ≤ f * t.order :=
    Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (Nat.one_le_iff_ne_zero.1 hf) t.order_pos.ne')
  have : CharP K p := finite_field_prime_power_characteristic hp hfm hK'
  have h2 : (2 : K) ≠ 0 := two_ne_zero_of_charP hp2
  obtain ⟨x, hx, z, hz, b, hb, hxo, hzo, hxz, hbx⟩ : ∃ x ∈ graphFixedRootGroup t K σ,
      ∃ z ∈ graphFixedRootGroup t K σ, ∃ b ∈ graphFixedRootGroup t K σ,
        orderOf x = p ∧ orderOf z = 2 ∧ x * z = z * x ∧ b * x * b⁻¹ = x⁻¹ := by
    cases t
    · exact exists_real_root_element_twistedE6 σ h2
    · exact exists_real_root_element_trialityD4 σ h2
  obtain ⟨x', z', b', h₁, h₂, h₃, h₄⟩ :=
    exists_real_of_graphFixedRootGroup hp hf hK hσ hx hz hb hxo hzo hxz hbx
  exact exists_real_of_injective e.symm.toMonoidHom e.symm.injective h₁ h₂ h₃ h₄

theorem odd_Chevalley_exceptional_real_root_element_centralizing_involution (S : Type) [Group S]
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (f : ℕ) (t : StatedLieTag)
    (h : ChevalleyExceptionalModel S t p f) :
    ∃ x z b : S, orderOf x = p ∧ orderOf z = 2 ∧ x * z = z * x ∧ b * x * b⁻¹ = x⁻¹ ∧
      x ∈ Subgroup.centralizer (Subgroup.zpowers z : Set S) ∧
      Subgroup.centralizer (Subgroup.zpowers z : Set S) ≤
        Subgroup.normalizer (Subgroup.zpowers z : Set S) := by
  obtain ⟨⟨-, hf, -⟩, hmodel⟩ := h
  suffices hS : ∃ x z b : S, orderOf x = p ∧ orderOf z = 2 ∧ x * z = z * x ∧
      b * x * b⁻¹ = x⁻¹ by
    obtain ⟨x, z, b, hx, hz, hxz, hb⟩ := hS
    refine ⟨x, z, b, hx, hz, hxz, hb, Subgroup.mem_centralizer_iff.2 fun g hg => ?_,
      Subgroup.centralizer_le_normalizer _⟩
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hg
    exact (Commute.zpow_left (hxz.symm : Commute z x) n).eq
  cases t
  case G2 =>
    exact exists_real_root_element_of_untwisted S .G2 hp hp2 hf (i := ⟨0, by decide⟩)
      (j := ⟨1, by decide⟩) (by decide) (by decide) hmodel
  case F4 =>
    exact exists_real_root_element_of_untwisted S .F4 hp hp2 hf (i := ⟨0, by decide⟩)
      (j := ⟨1, by decide⟩) (by decide) (by decide) hmodel
  case E6 =>
    exact exists_real_root_element_of_untwisted S .E6 hp hp2 hf (i := ⟨0, by decide⟩)
      (j := ⟨2, by decide⟩) (by decide) (by decide) hmodel
  case E7 =>
    exact exists_real_root_element_of_untwisted S .E7 hp hp2 hf (i := ⟨0, by decide⟩)
      (j := ⟨2, by decide⟩) (by decide) (by decide) hmodel
  case E8 =>
    exact exists_real_root_element_of_untwisted S .E8 hp hp2 hf (i := ⟨0, by decide⟩)
      (j := ⟨2, by decide⟩) (by decide) (by decide) hmodel
  case twistedE6 => exact exists_real_root_element_of_twisted S .E6 hp hp2 hf hmodel
  case trialityD4 => exact exists_real_root_element_of_twisted S .D4 hp hp2 hf hmodel
  all_goals exact False.elim hmodel

end CFSG.RankThree.Chevalley
