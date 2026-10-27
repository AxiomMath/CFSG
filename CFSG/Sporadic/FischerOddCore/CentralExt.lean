module

public import CFSG.Assembly.Defs
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogEvenCore

public noncomputable section

namespace CFSG.Sporadic.FischerOddCore

open CFSG.ComponentClassification.UnbalancedCatalog.EvenCatalog

theorem oddCore_eq_bot_of_isSimpleGroup {Q : Type*} [Group Q] [Finite Q] [IsSimpleGroup Q]
    (hQ : Even (Nat.card Q)) : CFSG.oddCore Q = ⊥ := by
  rcases (CFSG.oddCore_normal (G := Q)).eq_bot_or_eq_top with h | h
  · exact h
  · have hodd := odd_card_oddCore (G := Q)
    rw [h, Subgroup.card_top] at hodd
    exact absurd hQ (Nat.not_even_iff_odd.2 hodd)

theorem map_oddCore_le {G : Type*} [Group G] [Finite G] (φ : G ≃* G) :
    (CFSG.oddCore G).map φ.toMonoidHom ≤ CFSG.oddCore G := by
  apply le_oddCore_of_normal (Subgroup.Normal.map (CFSG.oddCore_normal (G := G)) _ φ.surjective)
  have hc : Nat.card ((CFSG.oddCore G).map φ.toMonoidHom) = Nat.card (CFSG.oddCore G) :=
    Nat.card_congr ((CFSG.oddCore G).equivMapOfInjective _ φ.injective).toEquiv.symm
  rw [hc]
  exact odd_card_oddCore

variable {G H : Type*} [Group G] [Group H]

theorem map_centralizer_inf_centralizer (e : G ≃* H) (a b : G) :
    (Subgroup.centralizer {a} ⊓ Subgroup.centralizer {b}).map e.toMonoidHom =
      Subgroup.centralizer {e a} ⊓ Subgroup.centralizer {e b} := by
  ext y
  rw [Subgroup.mem_map, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff,
    Subgroup.mem_centralizer_singleton_iff]
  constructor
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨hxa, hxb⟩ := Subgroup.mem_inf.1 hx
    rw [Subgroup.mem_centralizer_singleton_iff] at hxa hxb
    exact ⟨by rw [MulEquiv.coe_toMonoidHom, ← map_mul, hxa, map_mul],
      by rw [MulEquiv.coe_toMonoidHom, ← map_mul, hxb, map_mul]⟩
  · rintro ⟨hya, hyb⟩
    refine ⟨e.symm y, Subgroup.mem_inf.2 ⟨Subgroup.mem_centralizer_singleton_iff.2 ?_,
      Subgroup.mem_centralizer_singleton_iff.2 ?_⟩, by simp⟩
    · apply e.injective
      rw [map_mul, map_mul, MulEquiv.apply_symm_apply, hya]
    · apply e.injective
      rw [map_mul, map_mul, MulEquiv.apply_symm_apply, hyb]

@[expose] def centralizerInfEquiv (e : G ≃* H) (a b : G) :
    ↥(Subgroup.centralizer {a} ⊓ Subgroup.centralizer {b}) ≃*
      ↥(Subgroup.centralizer {e a} ⊓ Subgroup.centralizer {e b}) :=
  ((Subgroup.centralizer {a} ⊓ Subgroup.centralizer {b}).equivMapOfInjective e.toMonoidHom
    e.injective).trans (MulEquiv.subgroupCongr (map_centralizer_inf_centralizer e a b))

@[expose] def infCentralizerEquiv (K : Subgroup G) {h : G} (hh : h ∈ K) :
    ↥(K ⊓ Subgroup.centralizer {h}) ≃* ↥(Subgroup.centralizer ({⟨h, hh⟩} : Set K)) where
  toFun x := ⟨⟨x, (Subgroup.mem_inf.1 x.2).1⟩, Subgroup.mem_centralizer_singleton_iff.2
    (Subtype.ext (Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 x.2).2))⟩
  invFun y := ⟨y, Subgroup.mem_inf.2 ⟨(y : K).2, Subgroup.mem_centralizer_singleton_iff.2
    (congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.1 y.2))⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

theorem conj_mem_centralizer_of_central {a s k : G}
    (hc : a * s * a⁻¹ * s⁻¹ ∈ Subgroup.center G) (hk : k * s = s * k) :
    a * k * a⁻¹ * s = s * (a * k * a⁻¹) := by
  have hcx := Subgroup.mem_center_iff.1 hc (a * k * a⁻¹)
  have e1 : a * k * a⁻¹ * (a * s * a⁻¹ * s⁻¹ * s) = a * s * a⁻¹ * s⁻¹ * s * (a * k * a⁻¹) := by
    calc a * k * a⁻¹ * (a * s * a⁻¹ * s⁻¹ * s) = a * (k * s) * a⁻¹ := by group
      _ = a * (s * k) * a⁻¹ := by rw [hk]
      _ = a * s * a⁻¹ * s⁻¹ * s * (a * k * a⁻¹) := by group
  calc a * k * a⁻¹ * s
      = (a * s * a⁻¹ * s⁻¹)⁻¹ * ((a * k * a⁻¹) * (a * s * a⁻¹ * s⁻¹)) * s := by
        rw [hcx]; group
    _ = (a * s * a⁻¹ * s⁻¹)⁻¹ * (a * k * a⁻¹ * (a * s * a⁻¹ * s⁻¹ * s)) := by group
    _ = (a * s * a⁻¹ * s⁻¹)⁻¹ * (a * s * a⁻¹ * s⁻¹ * s * (a * k * a⁻¹)) := by rw [e1]
    _ = s * (a * k * a⁻¹) := by group

theorem oddCore_centralizer_eq_bot_of_central {M Q : Type*} [Group M] [Group Q] [Finite M]
    (κ : M →* Q) (hκ : Function.Surjective κ) (hker : κ.ker ≤ Subgroup.center M)
    (hcard : Nat.card κ.ker ∣ 2) (s : M)
    (hQ : CFSG.oddCore ↥(Subgroup.centralizer ({κ s} : Set Q)) = ⊥) :
    CFSG.oddCore ↥(Subgroup.centralizer ({s} : Set M)) = ⊥ := by
  set K := Subgroup.centralizer ({s} : Set M)
  set N := (CFSG.oddCore K).map K.subtype with hNdef
  have hNodd : Odd (Nat.card N) := by
    rw [Nat.card_congr ((CFSG.oddCore K).equivMapOfInjective _ K.subtype_injective).toEquiv.symm]
    exact odd_card_oddCore
  have hA : ∀ a : M, κ a * κ s = κ s * κ a → ∀ n ∈ N, a * n * a⁻¹ ∈ N := by
    intro a ha
    have hc : a * s * a⁻¹ * s⁻¹ ∈ Subgroup.center M := hker (by
      rw [MonoidHom.mem_ker, map_mul, map_mul, map_mul, map_inv, map_inv]
      calc κ a * κ s * (κ a)⁻¹ * (κ s)⁻¹ = κ s * κ a * (κ a)⁻¹ * (κ s)⁻¹ := by rw [ha]
        _ = 1 := by group)
    have hK : ∀ k ∈ K, a * k * a⁻¹ ∈ K := fun k hk => by
      rw [Subgroup.mem_centralizer_singleton_iff] at hk ⊢
      exact conj_mem_centralizer_of_central hc hk
    have hK' : ∀ k ∈ K, a⁻¹ * k * a ∈ K := by
      intro k hk
      have hci : (a * s * a⁻¹ * s⁻¹)⁻¹ ∈ Subgroup.center M := Subgroup.inv_mem _ hc
      have hc' : a⁻¹ * s * a⁻¹⁻¹ * s⁻¹ ∈ Subgroup.center M := by
        have e : a⁻¹ * s * a⁻¹⁻¹ * s⁻¹ = a⁻¹ * (a * s * a⁻¹ * s⁻¹)⁻¹ * a := by group
        rw [e, Subgroup.mem_center_iff.1 hci a⁻¹, inv_mul_cancel_right]
        exact hci
      rw [Subgroup.mem_centralizer_singleton_iff] at hk ⊢
      have := conj_mem_centralizer_of_central hc' hk
      simpa only [inv_inv] using this
    let φ : K ≃* K :=
      { toFun := fun k => ⟨a * k * a⁻¹, hK k k.2⟩
        invFun := fun k => ⟨a⁻¹ * k * a, hK' k k.2⟩
        left_inv := fun k => Subtype.ext (by simp [mul_assoc])
        right_inv := fun k => Subtype.ext (by simp [mul_assoc])
        map_mul' := fun k l => Subtype.ext (by simp [mul_assoc]) }
    rintro n ⟨k, hk, rfl⟩
    have := map_oddCore_le φ ⟨k, hk, rfl⟩
    exact ⟨φ k, this, rfl⟩
  have hNK : N.map κ ≤ Subgroup.centralizer ({κ s} : Set Q) := by
    rintro _ ⟨n, ⟨k, -, rfl⟩, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul]
    exact congrArg κ (Subgroup.mem_centralizer_singleton_iff.1 k.2)
  have hnormal : ((N.map κ).subgroupOf (Subgroup.centralizer ({κ s} : Set Q))).Normal := by
    refine ⟨fun x hx q => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    obtain ⟨a, ha⟩ := hκ (q : Q)
    have hqa : κ a * κ s = κ s * κ a := by
      rw [ha]; exact Subgroup.mem_centralizer_singleton_iff.1 q.2
    obtain ⟨n, hn, hnx⟩ := hx
    refine ⟨a * n * a⁻¹, hA a hqa n hn, ?_⟩
    rw [map_mul, map_mul, map_inv, ha, hnx]
    rfl
  have hodd : Odd (Nat.card ((N.map κ).subgroupOf (Subgroup.centralizer ({κ s} : Set Q)))) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNK).toEquiv]
    exact Odd.of_dvd_nat hNodd (Subgroup.card_map_dvd N κ)
  have hle := le_oddCore_of_normal hnormal hodd
  rw [hQ, le_bot_iff, Subgroup.subgroupOf_eq_bot] at hle
  have hbot : N.map κ = ⊥ := disjoint_self.1 (hle.mono_right hNK)
  rw [Subgroup.map_eq_bot_iff] at hbot
  have h1 : Nat.card N = 1 := by
    have hd := (Subgroup.card_dvd_of_le hbot).trans hcard
    rcases (Nat.dvd_prime Nat.prime_two).1 hd with h | h
    · exact h
    · rw [h] at hNodd
      exact absurd hNodd (by decide)
  rw [Subgroup.card_eq_one, hNdef] at h1
  exact (Subgroup.map_eq_bot_iff_of_injective _ K.subtype_injective).1 h1

theorem card_dvd_of_free {K X : Type*} [Group K] [Finite K] [MulAction K X] [Finite X]
    (hfree : ∀ (k : K) (x : X), k • x = x → k = 1) : Nat.card K ∣ Nat.card X := by
  classical
  have : Fintype K := Fintype.ofFinite K
  have : Fintype X := Fintype.ofFinite X
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card,
    MulAction.card_eq_sum_card_group_div_card_stabilizer K X]
  refine Finset.dvd_sum fun ω _ => ?_
  have hstab : Fintype.card (MulAction.stabilizer K ω.out) = 1 := by
    rw [Fintype.card_eq_one_iff]
    refine ⟨1, fun k => Subtype.ext ?_⟩
    exact hfree k ω.out (MulAction.mem_stabilizer_iff.mp k.2)
  rw [hstab, Nat.div_one]

end CFSG.Sporadic.FischerOddCore
