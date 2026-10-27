module

public import CFSG.GroupTheory.Fitting.CharacteristicP
public import CFSG.GroupTheory.LocalCores.Layer
public import CFSG.Walter.AStar.Subnormal

public section

namespace CFSG.Quasithin

namespace S143

namespace InspW2

section Cores

variable {X : Type*} [Group X] [Finite X]

omit [Finite X] in
theorem map_pCore_le_pCore (Z : Subgroup X) [hZ : Z.Normal] :
    (CFSG.pCore 2 ↥Z).map Z.subtype ≤ CFSG.pCore 2 X := by
  apply le_sSup
  refine ⟨⟨fun l hl g => CFSG.Walter.conj_mem_map_of_characteristic ?_ hl⟩, ?_⟩
  · rw [Subgroup.normalizer_eq_top_iff.mpr hZ]; exact Subgroup.mem_top g
  · exact CFSG.pCore_isPGroup.map Z.subtype

theorem centralizer_pCore_le_of_no_component {Z : Subgroup X} [hZ : Z.Normal]
    (hO : CFSG.pPrimeCore 2 X = ⊥) (hno : ∀ K : Subgroup X, CFSG.IsComponent K → ¬ K ≤ Z) :
    Z ⊓ Subgroup.centralizer (CFSG.pCore 2 X : Set X) ≤ CFSG.pCore 2 X := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcoreZ : CFSG.pPrimeCore 2 ↥Z = ⊥ := by
    have h := CFSG.Walter.map_pPrimeCore_le_of_isSubnormal (Subgroup.Normal.isSubnormal hZ)
    rw [hO] at h
    exact (Subgroup.map_eq_bot_iff_of_injective _ Z.subtype_injective).mp (le_bot_iff.mp h)
  have hlayerZ : CFSG.layer ↥Z = ⊥ := by
    apply CFSG.LocalCores.layer_eq_bot_of_forall
    intro K hK
    have hK' : CFSG.IsComponent (K.map Z.subtype) :=
      ⟨CFSG.LocalCores.isQuasisimple_of_mulEquiv
        (K.equivMapOfInjective Z.subtype Z.subtype_injective) hK.1,
        Subgroup.IsSubnormal.trans' hK.2 (Subgroup.Normal.isSubnormal hZ)⟩
    exact hno _ hK' (Subgroup.map_subtype_le K)
  have hchar := CFSG.isCharacteristicP_of_pPrimeCore_eq_bot_of_layer_eq_bot ↥Z 2 hcoreZ hlayerZ
  rintro y ⟨hyZ, hyC⟩
  have hcen : (⟨y, hyZ⟩ : ↥Z) ∈ Subgroup.centralizer (CFSG.pCore 2 ↥Z : Set ↥Z) := by
    refine Subgroup.mem_centralizer_iff.mpr fun p hp => ?_
    have hp' : (p : X) ∈ CFSG.pCore 2 X := map_pCore_le_pCore Z ⟨p, hp, rfl⟩
    exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hyC _ hp')
  exact map_pCore_le_pCore Z ⟨_, hchar hcen, rfl⟩

theorem fix_of_odd_of_small {P : Subgroup X} (hP : Nat.card P ≤ 4) {y w : X} (hw : w ∈ P)
    (hw1 : w ≠ 1) (hy : Odd (orderOf y)) (hyP : ∀ p ∈ P, y * p * y⁻¹ ∈ P)
    (hyw : y * w * y⁻¹ = w) : ∀ p ∈ P, y * p * y⁻¹ = p := by
  classical
  have : Fintype X := Fintype.ofFinite X
  intro p hp
  by_contra hne
  set q := y * p * y⁻¹ with hq
  have hqP : q ∈ P := hyP p hp
  have hinj : ∀ a b : X, y * a * y⁻¹ = y * b * y⁻¹ → a = b := fun a b h => by
    simpa using h
  have hp1 : p ≠ 1 := fun h => hne (by rw [hq, h]; group)
  have hpw : p ≠ w := fun h => hne (by rw [hq, h, hyw])
  have hq1 : q ≠ 1 := fun h => hp1 (hinj p 1 (by rw [← hq, h]; group))
  have hqw : q ≠ w := fun h => hpw (hinj p w (by rw [← hq, h, hyw]))
  have hpq : p ≠ q := fun h => hne h.symm
  have hw1' : w ≠ 1 := hw1
  set F : Finset X := {1, w, p, q} with hF
  have hFcard : F.card = 4 := by
    have h1 : (1 : X) ∉ ({w, p, q} : Finset X) := by
      simp [hw1.symm, hp1.symm, hq1.symm]
    have h2 : w ∉ ({p, q} : Finset X) := by simp [hpw.symm, hqw.symm]
    have h3 : p ∉ ({q} : Finset X) := by simpa using hpq
    rw [hF, Finset.card_insert_of_notMem h1, Finset.card_insert_of_notMem h2,
      Finset.card_insert_of_notMem h3, Finset.card_singleton]
  have hPcard : (Finset.univ.filter (· ∈ P)).card ≤ 4 := by
    have : (Finset.univ.filter (· ∈ P)).card = Nat.card P := by
      rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    omega
  have hFP : F ⊆ Finset.univ.filter (· ∈ P) := by
    intro r hr
    simp only [hF, Finset.mem_insert, Finset.mem_singleton] at hr
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rcases hr with rfl | rfl | rfl | rfl
    · exact P.one_mem
    · exact hw
    · exact hp
    · exact hqP
  have hFeq : F = Finset.univ.filter (· ∈ P) :=
    Finset.eq_of_subset_of_card_le hFP (by omega)
  have hrP : y * q * y⁻¹ ∈ P := hyP q hqP
  have hrF : y * q * y⁻¹ ∈ F := by
    rw [hFeq]; simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact hrP
  simp only [hF, Finset.mem_insert, Finset.mem_singleton] at hrF
  have hrp : y * q * y⁻¹ = p := by
    rcases hrF with h | h | h | h
    · exact absurd (hinj q 1 (by rw [h]; group)) hq1
    · exact absurd (hinj q w (by rw [h, hyw])) hqw
    · exact h
    · exact absurd (hinj q p (by rw [h, ← hq])).symm hpq
  have h2 : ∀ j : ℕ, y ^ (2 * j) * p * (y ^ (2 * j))⁻¹ = p := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      have e : y ^ (2 * (j + 1)) * p * (y ^ (2 * (j + 1)))⁻¹ =
          y * (y * (y ^ (2 * j) * p * (y ^ (2 * j))⁻¹) * y⁻¹) * y⁻¹ := by
        rw [show 2 * (j + 1) = 2 * j + 1 + 1 by ring, pow_succ, pow_succ]; group
      rw [e, ih, ← hq, hrp]
  obtain ⟨j, hj⟩ := hy
  have h3 : y ^ (2 * j + 1) = 1 := by rw [← hj]; exact pow_orderOf_eq_one y
  have e : y ^ (2 * j + 1) * p * (y ^ (2 * j + 1))⁻¹ =
      y * (y ^ (2 * j) * p * (y ^ (2 * j))⁻¹) * y⁻¹ := by
    rw [pow_succ']; group
  rw [h2 j, h3] at e
  exact hne (by simpa [hq] using e.symm)

theorem le_pCore_of_no_component {Z : Subgroup X} [hZ : Z.Normal]
    (hO : CFSG.pPrimeCore 2 X = ⊥) (hno : ∀ K : Subgroup X, CFSG.IsComponent K → ¬ K ≤ Z)
    {w : X} (hwc : ∀ g : X, g * w = w * g) (hw1 : w ≠ 1) (hwP : w ∈ CFSG.pCore 2 X)
    (hP : Nat.card (CFSG.pCore 2 X) ≤ 4) : Z ≤ CFSG.pCore 2 X := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hodd : ∀ y ∈ Z, Odd (orderOf y) → y = 1 := by
    intro y hyZ hy
    have hyP : ∀ p ∈ CFSG.pCore 2 X, y * p * y⁻¹ ∈ CFSG.pCore 2 X := fun p hp =>
      (inferInstance : (CFSG.pCore 2 X).Normal).conj_mem p hp y
    have hyw : y * w * y⁻¹ = w := by rw [hwc y]; group
    have hfix := fix_of_odd_of_small hP hwP hw1 hy hyP hyw
    have hyC : y ∈ Subgroup.centralizer (CFSG.pCore 2 X : Set X) := by
      refine Subgroup.mem_centralizer_iff.mpr fun p hp => ?_
      have := hfix p hp
      calc p * y = (y * p * y⁻¹) * y := by rw [this]
        _ = y * p := by group
    have hyPc : y ∈ CFSG.pCore 2 X :=
      centralizer_pCore_le_of_no_component hO hno ⟨hyZ, hyC⟩
    obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp (CFSG.pCore_isPGroup (p := 2) (G := X)))
      ⟨y, hyPc⟩
    have hk' : orderOf y = 2 ^ k := (Subgroup.orderOf_mk _ _).symm.trans hk
    rw [hk'] at hy
    have hk0 : k = 0 := by
      by_contra hk0
      exact (Nat.not_even_iff_odd.mpr hy) (by
        rw [even_iff_two_dvd]; exact dvd_pow_self 2 hk0)
    rw [hk0, pow_zero] at hk'
    exact orderOf_eq_one_iff.mp hk'
  have hZ2 : IsPGroup 2 Z := by
    have hn : Nat.card Z ≠ 0 := Nat.card_pos.ne'
    have hk : Nat.card Z = 2 ^ (Nat.card Z).primeFactorsList.length := by
      refine Nat.eq_prime_pow_of_unique_prime_dvd hn ?_
      intro q hq hqd
      by_contra hq2
      have : Fact q.Prime := ⟨hq⟩
      obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := Z) q hqd
      have hyodd : Odd (orderOf (y : X)) := by
        rw [Subgroup.orderOf_coe, hy]; exact hq.odd_of_ne_two hq2
      have h1 := hodd y y.2 hyodd
      have : orderOf y = 1 := by
        have : y = 1 := Subtype.ext h1
        rw [this]; exact orderOf_one
      rw [hy] at this
      exact hq.one_lt.ne' this
    exact IsPGroup.of_card hk
  exact le_sSup ⟨hZ, hZ2⟩

end Cores

end InspW2

end S143

end CFSG.Quasithin
