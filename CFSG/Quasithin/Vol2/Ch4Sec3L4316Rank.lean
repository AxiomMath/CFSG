module

public import CFSG.Quasithin.Vol2.Ch4Sec3L4311Y
public import CFSG.Quasithin.Background.VolIExtraspecialRank

public section

namespace CFSG.Quasithin.H13.Ch4

open Module CFSG.LinearAlgebra

namespace L4316

@[expose] noncomputable def autFrattini (L : Type) [Group L] :
    MulAut L →* MulAut (L ⧸ frattini L) where
  toFun φ := QuotientGroup.congr (frattini L) (frattini L) φ
    (Subgroup.characteristic_iff_map_eq.mp inferInstance φ)
  map_one' := by
    ext x
    induction x using QuotientGroup.induction_on
    rfl
  map_mul' φ ψ := by
    ext x
    induction x using QuotientGroup.induction_on
    rfl

variable {G : Type} [Group G]

@[expose] noncomputable def conjFrattini (T : Subgroup G) :
    ↥(Subgroup.normalizer (T : Set G)) →* MulAut (↥T ⧸ frattini ↥T) :=
  (autFrattini ↥T).comp T.normalizerMonoidHom

theorem conjFrattini_mk (T : Subgroup G) (g : ↥(Subgroup.normalizer (T : Set G))) (t : ↥T) :
    conjFrattini T g (QuotientGroup.mk t) =
      QuotientGroup.mk (⟨(g : G) * t * (g : G)⁻¹, (g.2 t).mp t.2⟩ : ↥T) := rfl

theorem le_centralizer_of_conjFrattini_eq_one [Finite G] {T : Subgroup G} (hT : IsPGroup 2 ↥T)
    {z : G} (hzN : z ∈ Subgroup.normalizer (T : Set G)) (hodd : Odd (orderOf z))
    (h1 : conjFrattini T ⟨z, hzN⟩ = 1) : T ≤ Subgroup.centralizer ({z} : Set G) := by
  have hXN : Subgroup.zpowers z ≤ Subgroup.normalizer (T : Set G) :=
    (Subgroup.zpowers_le).mpr hzN
  have hsolv : Group.IsSolvable ↥T := by
    have := hT.isNilpotent
    infer_instance
  have hcop : Nat.Coprime (Nat.card (Subgroup.zpowers z)) (Nat.card T) := by
    rw [Nat.card_zpowers]
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hT
    rw [hk]
    exact Nat.Coprime.pow_right k (Nat.coprime_two_right.mpr hodd)
  have hle := Setting4311.le_commutator_sup_centralizer' hXN hsolv hcop
  have hcommΦ : ⁅T, Subgroup.zpowers z⁆ ≤ (frattini ↥T).map T.subtype := by
    rw [Subgroup.commutator_le]
    intro t ht w hw
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
    have hzj : z ^ j ∈ Subgroup.normalizer (T : Set G) := Subgroup.zpow_mem _ hzN j
    have h2 : conjFrattini T ⟨z ^ j, hzj⟩ = 1 := by
      have e : (⟨z ^ j, hzj⟩ : ↥(Subgroup.normalizer (T : Set G))) = ⟨z, hzN⟩ ^ j := by
        apply Subtype.ext
        simp
      rw [e, map_zpow, h1, one_zpow]
    have h3 := congrArg (fun φ : MulAut (↥T ⧸ frattini ↥T) =>
      φ (QuotientGroup.mk (⟨t⁻¹, T.inv_mem ht⟩ : ↥T))) h2
    simp only [conjFrattini_mk, MulAut.one_apply] at h3
    rw [QuotientGroup.eq] at h3
    refine ⟨_, inv_mem h3, ?_⟩
    simp only [Subgroup.coe_subtype, Subgroup.coe_inv, Subgroup.coe_mul, commutatorElement_def]
    group
  set C : Subgroup ↥T :=
    (T ⊓ Subgroup.centralizer ((Subgroup.zpowers z : Subgroup G) : Set G)).subgroupOf T with hC
  have htop : C ⊔ frattini ↥T = ⊤ := by
    rw [eq_top_iff]
    intro x _
    have hx := hle x.2
    have hx' : (x : G) ∈ (C ⊔ frattini ↥T).map T.subtype := by
      rw [Subgroup.map_sup, hC, Subgroup.map_subgroupOf_eq_of_le inf_le_left, sup_comm]
      exact (sup_le_sup_right hcommΦ _) hx
    exact (Subgroup.mem_map_iff_mem T.subtype_injective).mp hx'
  have hCtop := frattini_nongenerating htop
  intro x hx
  have hxC : (⟨x, hx⟩ : ↥T) ∈ C := hCtop ▸ Subgroup.mem_top _
  have hxz : x ∈ Subgroup.centralizer ((Subgroup.zpowers z : Subgroup G) : Set G) :=
    (Subgroup.mem_subgroupOf.mp hxC).2
  rw [Subgroup.mem_centralizer_iff] at hxz ⊢
  intro g hg
  rw [Set.mem_singleton_iff] at hg
  rw [hg]
  exact hxz z (Subgroup.mem_zpowers z)

theorem orderOf_two_zmod_five : orderOf (2 : ZMod 5) = 5 - 1 := by
  rw [orderOf_eq_iff (by norm_num)]
  refine ⟨by decide, fun k hk hk0 => ?_⟩
  interval_cases k <;> decide

theorem two_pow_twenty_mul_card_le [Finite G] {T Q : Subgroup G} (hT : IsPGroup 2 ↥T)
    (hQT : Q ≤ Subgroup.normalizer (T : Set G)) (hexp : ∀ g ∈ Q, g ^ 5 = 1) {a b : G}
    (ha : a ∈ Q) (hb : b ∈ Q)
    (hzc : ∀ g ∈ Q, g * (a * b * a⁻¹ * b⁻¹) = a * b * a⁻¹ * b⁻¹ * g)
    (hnt : ¬ T ≤ Subgroup.centralizer ({a * b * a⁻¹ * b⁻¹} : Set G)) :
    2 ^ 20 * Nat.card ↥(T ⊓ Subgroup.centralizer ({a * b * a⁻¹ * b⁻¹} : Set G)) ≤
      Nat.card ↥T := by
  classical
  set z := a * b * a⁻¹ * b⁻¹ with hzdef
  have hzQ : z ∈ Q := Q.mul_mem (Q.mul_mem (Q.mul_mem ha hb) (Q.inv_mem ha)) (Q.inv_mem hb)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have : Fact (IsPGroup 2 ↥T) := ⟨hT⟩
  have hEA : CFSG.IsElementaryAbelian 2 (↥T ⧸ frattini ↥T) :=
    CFSG.isElementaryAbelian_quotient_frattini
  set W := ↥T ⧸ frattini ↥T with hWdef
  have hsq : ∀ w : W, w ^ 2 = 1 := fun w =>
    (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp hEA.exponent_dvd_p) w
  let _ : CommGroup W := { (inferInstance : Group W) with mul_comm := hEA.is_comm.comm }
  let _ : Module (ZMod 2) (Additive W) := AddCommGroup.zmodModule fun u => by
    apply Additive.toMul.injective
    rw [toMul_nsmul, toMul_zero]
    exact hsq _
  have : Finite (Additive W) := Finite.of_equiv W Additive.ofMul
  have : FiniteDimensional (ZMod 2) (Additive W) := Module.Finite.of_finite
  let act : ↥Q →* MulAut W := (conjFrattini T).comp (Subgroup.inclusion hQT)
  let ρ : Representation (ZMod 2) ↥Q (Additive W) :=
    { toFun := fun q => AddMonoidHom.toZModLinearMap 2 (MonoidHom.toAdditive (act q).toMonoidHom)
      map_one' := by
        ext w
        change Additive.ofMul (act 1 w.toMul) = w
        rw [map_one]
        rfl
      map_mul' := fun q q' => by
        ext w
        change Additive.ofMul (act (q * q') w.toMul) = Additive.ofMul (act q (act q' w.toMul))
        rw [map_mul]
        rfl }
  have hρ : ∀ (q : ↥Q) (w : W), ρ q (Additive.ofMul w) = Additive.ofMul (act q w) := fun _ _ => rfl
  set z₀ : ↥Q := ⟨z, hzQ⟩ with hz₀
  have hzc' : ∀ g : ↥Q, Commute g z₀ := fun g => Subtype.ext (hzc g g.2)
  have hexp' : ∀ g : ↥Q, g ^ 5 = 1 := fun g => Subtype.ext (by
    rw [SubgroupClass.coe_pow, OneMemClass.coe_one]
    exact hexp g g.2)
  have hyx : (⟨b⁻¹, Q.inv_mem hb⟩ : ↥Q)⁻¹ * ⟨a⁻¹, Q.inv_mem ha⟩ * ⟨b⁻¹, Q.inv_mem hb⟩ =
      ⟨a⁻¹, Q.inv_mem ha⟩ * z₀ := by
    apply Subtype.ext
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, hz₀, hzdef]
    group
  have hdvd := VolI.dvd_finrank_centralImage (p := 5) (by norm_num) orderOf_two_zmod_five
    (ρ := ρ) hzc' hexp' hyx
  have hzN : z ∈ Subgroup.normalizer (T : Set G) := hQT hzQ
  have hodd : Odd (orderOf z) := by
    have h5 : orderOf z ∣ 5 := orderOf_dvd_of_pow_eq_one (hexp z hzQ)
    rcases (Nat.dvd_prime (by norm_num : Nat.Prime 5)).mp h5 with h | h <;> rw [h] <;> decide
  have hact : act z₀ ≠ 1 := by
    intro h
    apply hnt
    exact le_centralizer_of_conjFrattini_eq_one hT hzN hodd h
  have hne : centralImage ρ z₀ ≠ ⊥ := by
    intro hbot
    apply hact
    ext w
    have h1 : (ρ z₀ - 1) (Additive.ofMul w) ∈ centralImage ρ z₀ := LinearMap.mem_range_self _ _
    rw [hbot, Submodule.mem_bot, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero, hρ] at h1
    exact congrArg Additive.toMul h1
  have hpos : finrank (ZMod 2) (centralImage ρ z₀) ≠ 0 := fun h =>
    hne (Submodule.finrank_eq_zero.mp h)
  have h20 : 20 ≤ finrank (ZMod 2) (centralImage ρ z₀) := by
    obtain ⟨c, hc⟩ := hdvd
    have hc0 : c ≠ 0 := by
      rintro rfl
      rw [mul_zero] at hc
      exact hpos hc
    rw [hc]
    norm_num
    omega
  have hrn := LinearMap.finrank_range_add_finrank_ker (ρ z₀ - 1)
  have hcardW : Nat.card W = 2 ^ finrank (ZMod 2) (Additive W) := by
    rw [Nat.card_congr (Additive.ofMul : W ≃ Additive W),
      Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]
  have hcardK : Nat.card ↥(LinearMap.ker (ρ z₀ - 1)) =
      2 ^ finrank (ZMod 2) ↥(LinearMap.ker (ρ z₀ - 1)) := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]
  have hWK : 2 ^ 20 * Nat.card ↥(LinearMap.ker (ρ z₀ - 1)) ≤ Nat.card W := by
    rw [hcardW, hcardK, ← hrn, pow_add]
    exact Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by norm_num) h20)
  have hTW := Subgroup.card_eq_card_quotient_mul_card_subgroup (frattini ↥T)
  set CT := T ⊓ Subgroup.centralizer ({z} : Set G) with hCT
  let π : ↥CT →* W := (QuotientGroup.mk' (frattini ↥T)).comp (Subgroup.inclusion inf_le_left)
  have hker : Nat.card π.ker ≤ Nat.card (frattini ↥T) := by
    refine Nat.card_le_card_of_injective (fun c => (⟨Subgroup.inclusion inf_le_left (c : ↥CT),
      (QuotientGroup.eq_one_iff _).mp c.2⟩ : ↥(frattini ↥T))) fun c c' h => ?_
    have h1 := congrArg (fun w : ↥(frattini ↥T) => ((w : ↥T) : G)) h
    exact Subtype.ext (Subtype.ext h1)
  have hrange : Nat.card π.range ≤ Nat.card ↥(LinearMap.ker (ρ z₀ - 1)) := by
    refine Nat.card_le_card_of_injective (fun w => (⟨Additive.ofMul (w : W), ?_⟩ :
      ↥(LinearMap.ker (ρ z₀ - 1)))) fun w w' h => ?_
    · obtain ⟨c, hc⟩ := w.2
      rw [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero, hρ, ← hc]
      congr 1
      have hcz : z * (c : G) * z⁻¹ = c := by
        have := Subgroup.mem_centralizer_iff.mp (c.2.2) z (Set.mem_singleton z)
        rw [this, mul_inv_cancel_right]
      show conjFrattini T ⟨z, hzN⟩ (QuotientGroup.mk (Subgroup.inclusion inf_le_left c)) =
        QuotientGroup.mk (Subgroup.inclusion inf_le_left c)
      rw [conjFrattini_mk]
      congr 1
      exact Subtype.ext hcz
    · have h1 := congrArg (fun u : ↥(LinearMap.ker (ρ z₀ - 1)) => Additive.toMul (u : Additive W)) h
      exact Subtype.ext h1
  have hCT : Nat.card ↥CT = Nat.card π.ker * Nat.card π.range := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup π.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivRange π).toEquiv, mul_comm]
  calc 2 ^ 20 * Nat.card ↥CT
      = 2 ^ 20 * (Nat.card π.ker * Nat.card π.range) := by rw [hCT]
    _ ≤ 2 ^ 20 * (Nat.card (frattini ↥T) * Nat.card ↥(LinearMap.ker (ρ z₀ - 1))) :=
        Nat.mul_le_mul_left _ (Nat.mul_le_mul hker hrange)
    _ = (2 ^ 20 * Nat.card ↥(LinearMap.ker (ρ z₀ - 1))) * Nat.card (frattini ↥T) := by ring
    _ ≤ Nat.card W * Nat.card (frattini ↥T) := Nat.mul_le_mul_right _ hWK
    _ = Nat.card ↥T := hTW.symm

end L4316

end CFSG.Quasithin.H13.Ch4
