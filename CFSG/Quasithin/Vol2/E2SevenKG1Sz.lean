module

public import CFSG.Quasithin.Vol2.E2SevenKG1TwoL2
public import CFSG.RankThree.SteinbergR3ESuzukiInvolutionCentralizers
public import CFSG.LieType.Simplicity.Suzuki

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique B6
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)

namespace E2

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem exists_conj_eq_of_isSz {K : Subgroup G} {n : ℕ}
    (hK : IsSz n ↥K) {u : G} (huK : u ∈ Subgroup.normalizer (K : Set G)) {m : ℕ}
    (hum : u ^ 2 ^ m = 1) : ∃ k ∈ K, ∀ x ∈ K, u * x * u⁻¹ = k * x * k⁻¹ := by
  have hmapK : K.map (MulAut.conj u).toMonoidHom = K := by
    ext x
    constructor
    · rintro ⟨k, hk, rfl⟩
      exact (Subgroup.mem_normalizer_iff.mp huK k).mp hk
    · intro hx
      refine ⟨u⁻¹ * x * u, ?_, by simp [MulAut.conj_apply, mul_assoc]⟩
      have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ huK) x).mp hx
      simpa using this
  let β : ↥K ≃* ↥K := ((MulAut.conj u).subgroupMap K).trans (MulEquiv.subgroupCongr hmapK)
  have hβ : ∀ k : ↥K, ((β k : ↥K) : G) = u * k * u⁻¹ := fun k => rfl
  have hβpow : ∀ j : ℕ, ∀ k : ↥K, (((β ^ j) k : ↥K) : G) = u ^ j * k * (u ^ j)⁻¹ := by
    intro j
    induction j with
    | zero => intro k; simp
    | succ j ih =>
      intro k
      rw [pow_succ']
      change ((β ((β ^ j) k) : ↥K) : G) = _
      rw [hβ, ih k]
      group
  have hβm : β ^ (2 ^ m) = 1 := by
    ext k
    rw [hβpow, hum, one_mul, inv_one, mul_one]
    rfl
  have hodd := (CFSG.LieType.Suzuki.Suzuki_model_and_perfect_cover_outer_cyclicity.{0}
    ↥K 2 n hK).1.2.2
  set o : Outer ↥K := (β : Outer ↥K) with ho
  have hom : o ^ (2 ^ m) = 1 := by
    rw [ho, ← QuotientGroup.mk_pow, hβm]
    rfl
  have h1 : orderOf o ∣ 2 ^ m := orderOf_dvd_of_pow_eq_one hom
  have h2 : orderOf o ∣ Nat.card (Outer ↥K) := orderOf_dvd_natCard o
  have hcop : Nat.Coprime (2 ^ m) (Nat.card (Outer ↥K)) :=
    Nat.Coprime.pow_left m (Nat.coprime_two_left.mpr hodd)
  have ho1 : o = 1 := orderOf_eq_one_iff.mp ((hcop.coprime_dvd_left h1).eq_one_of_dvd h2)
  have hβinn : β ∈ inner ↥K := (QuotientGroup.eq_one_iff β).mp ho1
  obtain ⟨k, hk⟩ := hβinn
  refine ⟨k, k.2, fun x hx => ?_⟩
  have h3 := congrArg (fun f : MulAut ↥K => ((f ⟨x, hx⟩ : ↥K) : G)) hk
  simp only [MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_inv] at h3
  rw [h3, hβ]

theorem comm_of_involution_of_isSz {K S : Subgroup G} {n : ℕ}
    (hK : IsSz n ↥K) (hS : IsSylowTwoOf S K) :
    ∀ x ∈ S, x ^ 2 = 1 → ∀ y ∈ S, x * y = y * x := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro x hx hx2 y hy
  by_cases hx1 : x = 1
  · rw [hx1, one_mul, mul_one]
  obtain ⟨-, a, ha, F, _, _, rfl, hcard, ⟨e⟩⟩ := hK
  have : Finite ↥(CFSG.Blueprint.suzukiGroup a F) := Finite.of_equiv ↥K e.toEquiv
  set P' := toSylow2 hS
  have hP'c : (P' : Subgroup ↥K) = S.subgroupOf K := toSylow2_coe hS
  set P : Sylow 2 ↥(CFSG.Blueprint.suzukiGroup a F) :=
    P'.mapSurjective (f := e.toMonoidHom) e.surjective
  have hPc : (P : Subgroup ↥(CFSG.Blueprint.suzukiGroup a F)) =
      (P' : Subgroup ↥K).map e.toMonoidHom := Sylow.coe_mapSurjective _ _
  have hmemP : ∀ k : ↥K, e k ∈ (P : Subgroup ↥(CFSG.Blueprint.suzukiGroup a F)) ↔
      (k : G) ∈ S := by
    intro k
    rw [hPc, ← MulEquiv.coe_toMonoidHom, Subgroup.mem_map_equiv, MulEquiv.coe_toMonoidHom,
      MulEquiv.symm_apply_apply, hP'c, Subgroup.mem_subgroupOf]
  set z := e ⟨x, hS.1 hx⟩ with hz
  have hz2 : orderOf z = 2 := by
    rw [hz, MulEquiv.orderOf_eq]
    refine orderOf_eq_prime ?_ ?_
    · exact Subtype.ext (by simpa using hx2)
    · intro h
      exact hx1 (congrArg Subtype.val h)
  have hzP := (hmemP ⟨x, hS.1 hx⟩).mpr hx
  have hcent := CFSG.RankThree.centralizer_eq_sylow hcard hz2 P hzP
  have hyP := (hmemP ⟨y, hS.1 hy⟩).mpr hy
  rw [← hcent, Subgroup.mem_centralizer_singleton_iff] at hyP
  have h1 : e (⟨x, hS.1 hx⟩ * ⟨y, hS.1 hy⟩) = e (⟨y, hS.1 hy⟩ * ⟨x, hS.1 hx⟩) := by
    rw [map_mul, map_mul]
    exact hyP.symm
  exact congrArg Subtype.val (e.injective h1)

theorem not_isPGroup_normalizer_of_isSz {K S : Subgroup G} {n : ℕ}
    (hK : IsSz n ↥K) (hS : IsSylowTwoOf S K) :
    ¬ IsPGroup 2 ↥(K ⊓ Subgroup.normalizer (S : Set G)) := by
  intro hp
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, a, ha, F, _, _, rfl, hcard, ⟨e⟩⟩ := hK
  set Y := ↥(CFSG.Blueprint.suzukiGroup a F)
  have : Finite Y := Finite.of_equiv ↥K e.toEquiv
  set P' := toSylow2 hS
  have hP'c : (P' : Subgroup ↥K) = S.subgroupOf K := toSylow2_coe hS
  set P : Sylow 2 Y := P'.mapSurjective (f := e.toMonoidHom) e.surjective
  have hPc : (P : Subgroup Y) = (P' : Subgroup ↥K).map e.toMonoidHom := Sylow.coe_mapSurjective _ _
  have hN2 : IsPGroup 2 (Subgroup.normalizer ((P : Subgroup Y) : Set Y)) := by
    rintro ⟨d, hd⟩
    rw [hPc, ← Subgroup.map_equiv_normalizer_eq] at hd
    obtain ⟨k, hk, hke⟩ := hd
    rw [hP'c] at hk
    have hkN : (k : G) ∈ Subgroup.normalizer (S : Set G) := by
      rw [Subgroup.mem_normalizer_iff]
      intro z
      constructor
      · intro hz
        have h1 := (Subgroup.mem_normalizer_iff.mp hk ⟨z, hS.1 hz⟩).mp
          (Subgroup.mem_subgroupOf.mpr hz)
        exact Subgroup.mem_subgroupOf.mp h1
      · intro hz
        have hzK : z ∈ K := by
          have := K.mul_mem (K.mul_mem (K.inv_mem k.2) (hS.1 hz)) k.2
          simpa [mul_assoc] using this
        have h1 := (Subgroup.mem_normalizer_iff.mp hk ⟨z, hzK⟩).mpr
          (Subgroup.mem_subgroupOf.mpr hz)
        exact Subgroup.mem_subgroupOf.mp h1
    obtain ⟨j, hj⟩ := hp ⟨(k : G), k.2, hkN⟩
    refine ⟨j, Subtype.ext ?_⟩
    have hj' : (k : G) ^ 2 ^ j = 1 := by simpa using congrArg Subtype.val hj
    have hk1 : k ^ 2 ^ j = 1 := Subtype.ext (by simpa using hj')
    have : d = e k := hke.symm
    simp only [Subgroup.coe_pow, Subgroup.coe_one, this, ← map_pow, hk1, map_one]
  obtain ⟨-, -, hTcard, hTN, -, -, -, -⟩ := CFSG.LieType.Ree.suzuki_borel_structure hcard
  set P₀ : Sylow 2 Y := Sylow.ofCard _ (CFSG.RankThree.card_suzukiU_eq hcard)
  have hP₀ : (P₀ : Subgroup Y) = CFSG.LieType.Ree.suzukiU a F := Sylow.coe_ofCard _ _
  obtain ⟨y, hy⟩ := MulAction.exists_smul_eq Y P₀ P
  set D := (CFSG.LieType.Ree.suzukiT a F).map (MulAut.conj y).toMonoidHom with hD
  have hDN : D ≤ Subgroup.normalizer ((P : Subgroup Y) : Set Y) := by
    rintro _ ⟨d, hd, rfl⟩
    have hd' := hTN hd
    rw [← hP₀] at hd'
    rw [← hy, Sylow.coe_subgroup_smul]
    change (MulAut.conj y) d ∈ Subgroup.normalizer
      (((P₀ : Subgroup Y).map (MulAut.conj y).toMonoidHom : Subgroup Y) : Set Y)
    rw [← Subgroup.map_equiv_normalizer_eq]
    exact Subgroup.mem_map_of_mem _ hd'
  have hD2 : IsPGroup 2 D := hN2.to_le hDN
  have hDcard : Nat.card D = 2 ^ (2 * a + 1) - 1 := by
    rw [hD, Subgroup.card_map_of_injective (MulAut.conj y).injective, hTcard]
  obtain ⟨j, hj⟩ := hD2.exists_card_eq
  rw [hDcard] at hj
  have h2 : 2 ∣ 2 ^ (2 * a + 1) := dvd_pow_self 2 (by omega)
  have h8 : 8 ≤ 2 ^ (2 * a + 1) :=
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ (2 * a + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  rcases Nat.eq_zero_or_pos j with rfl | hj0
  · rw [pow_zero] at hj
    omega
  · have : 2 ∣ 2 ^ j := dvd_pow_self 2 (by omega)
    omega

theorem exists_mul_ne_mul_of_isSz {K : Subgroup G} {n : ℕ}
    (hK : IsSz n ↥K) : ∃ a b : ↥K, a * b ≠ b * a := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hab
  push Not at hab
  obtain ⟨Q⟩ : Nonempty (Sylow 2 ↥K) := inferInstance
  have hS : IsSylowTwoOf ((Q : Subgroup ↥K).map K.subtype) K := A4.isSylowTwoOf_map K Q
  apply not_isPGroup_normalizer_of_isSz hK hS
  have hK2 : IsPGroup 2 ↥K := by
    obtain ⟨-, a, ha, F, _, _, rfl, hcard, ⟨e⟩⟩ := hK
    have : Finite ↥(CFSG.Blueprint.suzukiGroup a F) := Finite.of_equiv ↥K e.toEquiv
    have h2 : 2 ∣ Nat.card ↥(CFSG.Blueprint.suzukiGroup a F) := by
      rw [CFSG.LieType.Ree.suzuki_order hcard]
      exact Dvd.dvd.mul_right (Dvd.dvd.mul_right (dvd_pow (dvd_pow_self 2 (by omega))
        (by norm_num)) _) _
    obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' 2 h2
    obtain ⟨P, hP⟩ : ∃ P : Sylow 2 ↥(CFSG.Blueprint.suzukiGroup a F),
        Subgroup.zpowers z ≤ P := by
      refine IsPGroup.exists_le_sylow (IsPGroup.of_card (n := 1) ?_)
      rw [Nat.card_zpowers, hz, pow_one]
    have hcent := CFSG.RankThree.centralizer_eq_sylow hcard hz P (hP (Subgroup.mem_zpowers z))
    intro k
    have hkP : e k ∈ (P : Subgroup ↥(CFSG.Blueprint.suzukiGroup a F)) := by
      rw [← hcent, Subgroup.mem_centralizer_singleton_iff]
      have := hab k (e.symm z)
      have h3 := congrArg e this
      simpa using h3
    obtain ⟨r, hr⟩ := P.isPGroup' ⟨e k, hkP⟩
    refine ⟨r, e.injective ?_⟩
    have := congrArg Subtype.val hr
    simpa using this
  intro x
  obtain ⟨r, hr⟩ := hK2 ⟨(x : G), x.2.1⟩
  have hr' : (x : G) ^ 2 ^ r = 1 := by simpa using congrArg Subtype.val hr
  exact ⟨r, Subtype.ext (by rw [Subgroup.coe_pow, Subgroup.coe_one]; exact hr')⟩

theorem kgBenderInnerSz_holds : KGBenderInnerSz := by
  intro G _ _ X T M K n hP hJ hKX hXN hC hKT hn hK hMK
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hTK : IsSylowTwoOf (T ⊓ K) K := A4.isSylowTwoOf_inf_normal hP.isSylow hKX hXN
  refine ⟨?_, fun x hx hx2 => ?_⟩
  swap
  · rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact (comm_of_involution_of_isSz hK hTK x hx hx2 y hy).symm
  intro u hu
  obtain ⟨hMmax, hTM⟩ : IsMaxSubgroupIn X M ∧ T ≤ M := by
    have : M ∈ maxOver X T := by rw [hP.uniqueMax]; exact rfl
    exact this
  have hMX : M ≤ X := hMmax.le
  have huM : u ∈ M := CFSG.LieType.BorelTits.pCoreOf_le 2 M hu
  have hO2 : IsPGroup 2 (pCoreOf 2 M) := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 M
  have huNK : u ∈ Subgroup.normalizer (K : Set G) := hXN (hMX huM)
  obtain ⟨m, hm⟩ := hO2 ⟨u, hu⟩
  have hum : u ^ 2 ^ m = 1 := by simpa using congrArg Subtype.val hm
  obtain ⟨k, hkK, hag⟩ := exists_conj_eq_of_isSz hK huNK hum
  have hc : k⁻¹ * u ∈ X ⊓ Subgroup.centralizer (K : Set G) := by
    refine ⟨X.mul_mem (X.inv_mem (hKX hkK)) (hMX huM), ?_⟩
    show k⁻¹ * u ∈ Subgroup.centralizer (K : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have h1 := hag y hy
    calc y * (k⁻¹ * u) = k⁻¹ * (k * y * k⁻¹) * u := by group
      _ = k⁻¹ * (u * y * u⁻¹) * u := by rw [h1]
      _ = k⁻¹ * u * y := by group
  rw [hC, Subgroup.mem_bot, inv_mul_eq_one] at hc
  rw [← hc]
  exact hkK

theorem kgBenderInnerTwoSz_holds : KGBenderInnerTwoSz := by
  intro G _ _ X T M K t n hP hJ ht hKX htK hXN hC hKK hcomm hKT hn hK hM hMK
  have hK' : IsSz n ↥(cjSub t K) := by
    obtain ⟨h2, a, ha, F, h1, h3, hn', hcard, ⟨g⟩⟩ := hK
    exact ⟨h2, a, ha, F, h1, h3, hn', hcard,
      ⟨(K.equivMapOfInjective (MulAut.conj t).toMonoidHom (MulAut.conj t).injective).symm.trans g⟩⟩
  have hfam : ∀ K₀ : Subgroup G, (K₀ = K ∨ K₀ = cjSub t K) → IsSz n ↥K₀ := by
    rintro K₀ (rfl | rfl)
    · exact hK
    · exact hK'
  refine kgBenderInnerTwo_of_facts hP ht hKX htK hXN hC hKK hcomm hMK
    (CFSG.LieType.Simplicity.fam_2b2_simplicity ↥K 2 n hK).2 (exists_mul_ne_mul_of_isSz hK)
    (not_isPGroup_normalizer_of_isSz hK) ?_ ?_
  · intro K₀ hK₀ _ u huK ⟨m, hum⟩ _
    exact exists_conj_eq_of_isSz (hfam K₀ hK₀) huK hum
  · intro K₀ hK₀ hS x hx hx2 y hy
    exact comm_of_involution_of_isSz (hfam K₀ hK₀) hS x hx hx2 y hy

end E2

end CFSG.Quasithin
