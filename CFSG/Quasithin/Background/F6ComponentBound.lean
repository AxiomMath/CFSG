module

public import CFSG.Quasithin.Background.F6Cyclic
public import CFSG.Walter.AStar.Subnormal

public section

namespace CFSG.Quasithin

open CFSG.Open

namespace F6

variable {D : Type*} [Group D] [Finite D]

theorem map_pPrimeCore_le_of_isSubnormal (p : ℕ) [Fact p.Prime] {X : Subgroup D}
    (hX : X.IsSubnormal) : (CFSG.pPrimeCore p X).map X.subtype ≤ CFSG.pPrimeCore p D := by
  have key : ∀ {X Z : Subgroup D}, X ≤ Z → Z ≤ Subgroup.normalizer (X : Set D) →
      (CFSG.pPrimeCore p X).map X.subtype ≤ (CFSG.pPrimeCore p Z).map Z.subtype := by
    intro X Z hXZ hZN
    have hLZ : (CFSG.pPrimeCore p X).map X.subtype ≤ Z :=
      (Subgroup.map_subtype_le _).trans hXZ
    have hle : ((CFSG.pPrimeCore p X).map X.subtype).subgroupOf Z ≤ CFSG.pPrimeCore p Z := by
      apply le_sSup
      refine ⟨⟨fun l hl z => ?_⟩, ?_⟩
      · rw [Subgroup.mem_subgroupOf] at hl ⊢
        simpa using CFSG.Walter.conj_mem_map_of_characteristic (hZN z.2) hl
      · rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hLZ).toEquiv,
          Subgroup.card_map_of_injective X.subtype_injective]
        exact CFSG.pPrimeCore_coprime_card
    calc (CFSG.pPrimeCore p X).map X.subtype
        = (((CFSG.pPrimeCore p X).map X.subtype).subgroupOf Z).map Z.subtype :=
          (Subgroup.map_subgroupOf_eq_of_le hLZ).symm
      _ ≤ (CFSG.pPrimeCore p Z).map Z.subtype := Subgroup.map_mono hle
  induction hX with
  | top =>
    apply le_sSup
    refine ⟨⟨fun l hl g => CFSG.Walter.conj_mem_map_of_characteristic ?_ hl⟩, ?_⟩
    · rw [Subgroup.normalizer_eq_top_iff.mpr inferInstance]
      exact Subgroup.mem_top g
    · rw [Subgroup.card_map_of_injective (Subgroup.subtype_injective _)]
      exact CFSG.pPrimeCore_coprime_card
  | step X Z hXZ hZ hN ih =>
    exact (key hXZ ((Subgroup.normal_subgroupOf_iff_le_normalizer hXZ).mp hN)).trans ih

theorem eq_bot_of_isSubnormal_of_coprime (p : ℕ) [Fact p.Prime] (hO : CFSG.pPrimeCore p D = ⊥)
    {K : Subgroup D} (hK : K.IsSubnormal) (hcop : Nat.Coprime p (Nat.card K)) : K = ⊥ := by
  have htop : CFSG.pPrimeCore p K = ⊤ :=
    le_antisymm le_top (le_sSup ⟨inferInstance, by rwa [Subgroup.card_top]⟩)
  have h := map_pPrimeCore_le_of_isSubnormal p hK
  rw [htop, hO, ← MonoidHom.range_eq_map, Subgroup.range_subtype] at h
  exact le_bot_iff.mp h

theorem exists_not_mem_centralizer_of_isComponent (hO : CFSG.pPrimeCore 3 D = ⊥)
    {K : Subgroup D} (hK : CFSG.IsComponent K) :
    ∃ x ∈ K, x ∉ Subgroup.centralizer (K : Set D) ∧
      x ^ 3 ∈ Subgroup.centralizer (K : Set D) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h3 : 3 ∣ Nat.card (↥K ⧸ Subgroup.center ↥K) := by
    by_contra h
    have hS := Subgroup.card_commutator_dvd_index_center_pow ↥K
    have hperf : commutator ↥K = ⊤ := Group.isPerfect_def.mp hK.1.1
    rw [hperf, Subgroup.card_top] at hS
    have hcop : Nat.Coprime 3 (Nat.card ↥K) :=
      (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr fun hd =>
        h (Nat.prime_three.dvd_of_dvd_pow (hd.trans hS))
    have hbot := eq_bot_of_isSubnormal_of_coprime 3 hO hK.2 hcop
    obtain ⟨⟨a, ha⟩, ⟨b, hb⟩, hab⟩ := CFSG.LocalCores.isQuasisimple_nontrivial hK.1
    rw [hbot, Subgroup.mem_bot] at ha hb
    exact hab (Subtype.ext (ha.trans hb.symm))
  obtain ⟨q, hq⟩ := exists_prime_orderOf_dvd_card' 3 h3
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective q
  have hyc : ∀ {z : ↥K}, z ∈ Subgroup.center ↥K →
      (z : D) ∈ Subgroup.centralizer (K : Set D) := by
    intro z hz
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hz ⟨k, hk⟩)
  refine ⟨y, y.2, fun hy => ?_, ?_⟩
  · have h1 : (QuotientGroup.mk y : ↥K ⧸ Subgroup.center ↥K) = 1 := by
      rw [QuotientGroup.eq_one_iff, Subgroup.mem_center_iff]
      intro k
      exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hy k k.2)
    rw [h1, orderOf_one] at hq
    omega
  · have h1 : (QuotientGroup.mk (y ^ 3) : ↥K ⧸ Subgroup.center ↥K) = 1 := by
      rw [QuotientGroup.mk_pow, ← hq, pow_orderOf_eq_one]
    rw [QuotientGroup.eq_one_iff] at h1
    simpa using hyc h1

omit [Finite D] in
theorem three_dvd_of_zpow_mem {x : D} {C : Subgroup D} (hx : x ∉ C) (h3 : x ^ 3 ∈ C) {a : ℤ}
    (ha : x ^ a ∈ C) : (3 : ℤ) ∣ a := by
  by_contra hdvd
  have h3' : x ^ (3 : ℤ) ∈ C := by simpa using h3
  obtain ⟨s, t, hst⟩ : ∃ s t : ℤ, a * s + 3 * t = 1 := by
    rcases (by omega : a % 3 = 1 ∨ a % 3 = 2) with h | h
    · exact ⟨1, -(a / 3), by omega⟩
    · exact ⟨2, -(2 * (a / 3) + 1), by omega⟩
  apply hx
  have hxe : x = (x ^ a) ^ s * (x ^ (3 : ℤ)) ^ t := by
    rw [← zpow_mul, ← zpow_mul, ← zpow_add, hst, zpow_one]
  rw [hxe]
  exact C.mul_mem (C.zpow_mem ha s) (C.zpow_mem h3' t)

theorem three_le_pRank_of_commute {x₁ x₂ x₃ : D} {C₁ C₂ C₃ : Subgroup D}
    (h₁₂ : Commute x₁ x₂) (h₁₃ : Commute x₁ x₃) (h₂₃ : Commute x₂ x₃)
    (hx₁ : x₁ ∉ C₁) (hx₂ : x₂ ∉ C₂) (hx₃ : x₃ ∉ C₃)
    (hc₁ : x₁ ^ 3 ∈ C₁) (hc₂ : x₂ ^ 3 ∈ C₂) (hc₃ : x₃ ^ 3 ∈ C₃)
    (h₂₁ : x₂ ∈ C₁) (h₃₁ : x₃ ∈ C₁) (h₁₂' : x₁ ∈ C₂) (h₃₂ : x₃ ∈ C₂)
    (h₁₃' : x₁ ∈ C₃) (h₂₃' : x₂ ∈ C₃) :
    3 ≤ Open.pRank 3 (⊤ : Subgroup D) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let ψ₂₃ : Multiplicative ℤ × Multiplicative ℤ →* D :=
    (zpowersHom D x₂).noncommCoprod (zpowersHom D x₃) fun m n => h₂₃.zpow_zpow _ _
  let ψ : Multiplicative ℤ × (Multiplicative ℤ × Multiplicative ℤ) →* D :=
    (zpowersHom D x₁).noncommCoprod ψ₂₃ fun m n =>
      (h₁₂.zpow_zpow _ _).mul_right (h₁₃.zpow_zpow _ _)
  have hψ : ∀ m, ψ m = x₁ ^ m.1.toAdd * (x₂ ^ m.2.1.toAdd * x₃ ^ m.2.2.toAdd) := fun m => rfl
  have hrel : ∀ m, ψ m = 1 → (3 : ℤ) ∣ m.1.toAdd ∧ (3 : ℤ) ∣ m.2.1.toAdd ∧
      (3 : ℤ) ∣ m.2.2.toAdd := by
    intro m hm
    rw [hψ] at hm
    refine ⟨three_dvd_of_zpow_mem hx₁ hc₁ ?_, three_dvd_of_zpow_mem hx₂ hc₂ ?_,
      three_dvd_of_zpow_mem hx₃ hc₃ ?_⟩
    · rw [eq_inv_of_mul_eq_one_left hm]
      exact C₁.inv_mem (C₁.mul_mem (C₁.zpow_mem h₂₁ _) (C₁.zpow_mem h₃₁ _))
    · have hb : x₂ ^ m.2.1.toAdd = (x₁ ^ m.1.toAdd)⁻¹ * (x₃ ^ m.2.2.toAdd)⁻¹ := by
        calc x₂ ^ m.2.1.toAdd = (x₁ ^ m.1.toAdd)⁻¹ *
              (x₁ ^ m.1.toAdd * (x₂ ^ m.2.1.toAdd * x₃ ^ m.2.2.toAdd)) *
              (x₃ ^ m.2.2.toAdd)⁻¹ := by group
          _ = (x₁ ^ m.1.toAdd)⁻¹ * (x₃ ^ m.2.2.toAdd)⁻¹ := by rw [hm, mul_one]
      rw [hb]
      exact C₂.mul_mem (C₂.inv_mem (C₂.zpow_mem h₁₂' _)) (C₂.inv_mem (C₂.zpow_mem h₃₂ _))
    · have hc : x₃ ^ m.2.2.toAdd = (x₂ ^ m.2.1.toAdd)⁻¹ * (x₁ ^ m.1.toAdd)⁻¹ := by
        calc x₃ ^ m.2.2.toAdd = (x₂ ^ m.2.1.toAdd)⁻¹ * ((x₁ ^ m.1.toAdd)⁻¹ *
              (x₁ ^ m.1.toAdd * (x₂ ^ m.2.1.toAdd * x₃ ^ m.2.2.toAdd))) := by group
          _ = (x₂ ^ m.2.1.toAdd)⁻¹ * (x₁ ^ m.1.toAdd)⁻¹ := by rw [hm, mul_one]
      rw [hc]
      exact C₃.mul_mem (C₃.inv_mem (C₃.zpow_mem h₂₃' _)) (C₃.inv_mem (C₃.zpow_mem h₁₃' _))
  have hAc : ∀ a b : ↥ψ.range, a * b = b * a := by
    rintro ⟨_, m, rfl⟩ ⟨_, n, rfl⟩
    exact Subtype.ext (by
      change ψ m * ψ n = ψ n * ψ m
      rw [← map_mul, ← map_mul, mul_comm])
  let φ : ↥ψ.range →* ↥ψ.range :=
    MonoidHom.mk' (fun a => a ^ 3) fun a b => (Commute.mul_pow (hAc a b) 3)
  let ι : Fin 3 × Fin 3 × Fin 3 → Multiplicative ℤ × (Multiplicative ℤ × Multiplicative ℤ) :=
    fun u => (Multiplicative.ofAdd ((u.1 : ℕ) : ℤ), Multiplicative.ofAdd ((u.2.1 : ℕ) : ℤ),
      Multiplicative.ofAdd ((u.2.2 : ℕ) : ℤ))
  let f : Fin 3 × Fin 3 × Fin 3 → ↥ψ.range ⧸ φ.range := fun u =>
    QuotientGroup.mk (⟨ψ (ι u), ι u, rfl⟩ : ↥ψ.range)
  have hf : Function.Injective f := by
    intro u v huv
    rw [QuotientGroup.eq] at huv
    obtain ⟨⟨_, n, rfl⟩, hw⟩ := huv
    have hw' : ψ n ^ 3 = (ψ (ι u))⁻¹ * ψ (ι v) := congrArg Subtype.val hw
    have h1 : ψ ((ι u)⁻¹ * ι v * (n ^ 3)⁻¹) = 1 := by
      rw [map_mul, map_mul, map_inv, map_inv, map_pow, hw', mul_inv_cancel]
    obtain ⟨d₁, d₂, d₃⟩ := hrel _ h1
    simp only [ι, Prod.fst_mul, Prod.snd_mul, Prod.fst_inv, Prod.snd_inv, Prod.pow_fst,
      Prod.pow_snd, toAdd_mul, toAdd_inv, toAdd_pow, toAdd_ofAdd, nsmul_eq_mul] at d₁ d₂ d₃
    have := u.1.isLt
    have := u.2.1.isLt
    have := u.2.2.isLt
    have := v.1.isLt
    have := v.2.1.isLt
    have := v.2.2.isLt
    refine Prod.ext (Fin.ext ?_) (Prod.ext (Fin.ext ?_) (Fin.ext ?_)) <;> push_cast at d₁ d₂ d₃ <;>
      omega
  have h27 : 27 ≤ Nat.card (↥ψ.range ⧸ φ.range) := by
    have := Nat.card_le_card_of_injective f hf
    simpa using this
  have hker : Nat.card φ.ker = Nat.card (↥ψ.range ⧸ φ.range) := by
    have h1 := Subgroup.card_ker_mul_card_range φ
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup φ.range] at h1
    exact Nat.eq_of_mul_eq_mul_right Nat.card_pos h1
  set E : Subgroup D := φ.ker.map ψ.range.subtype with hE
  have hEe : Open.IsElemAbelian 3 E := by
    refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, fun x hx => ?_⟩
    · obtain ⟨a', -, ha⟩ := Subgroup.mem_map.mp a.2
      obtain ⟨b', -, hb⟩ := Subgroup.mem_map.mp b.2
      change (a : D) * b = b * a
      rw [← ha, ← hb]
      exact congrArg Subtype.val (hAc a' b')
    · obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.mp hx
      have hw3 : w ^ 3 = 1 := MonoidHom.mem_ker.mp hw
      simpa using congrArg Subtype.val hw3
  have hEcard : Nat.card E = Nat.card φ.ker :=
    Subgroup.card_map_of_injective ψ.range.subtype_injective
  have hE3 : IsPGroup 3 ↥E := fun x => ⟨1, Subtype.ext (by simpa using hEe.2 x x.2)⟩
  obtain ⟨k, hk⟩ := hE3.exists_card_eq
  have hk3 : 3 ≤ k := by
    have h : 3 ^ 3 ≤ 3 ^ k := by
      rw [← hk, hEcard, hker]
      exact h27
    exact (Nat.pow_le_pow_iff_right (by norm_num)).mp h
  exact hk3.trans (CFSG.SectionRank.le_pRank (by norm_num) le_top hEe hk)

omit [Finite D] in
theorem mem_map_conj_iff {K : Subgroup D} {g y : D} :
    y ∈ K.map (MulAut.conj g).toMonoidHom ↔ g⁻¹ * y * g ∈ K := by
  rw [Subgroup.mem_map_equiv, MulAut.conj_symm_apply]

omit [Finite D] in
theorem mem_normalizer_of_map_conj_eq {K : Subgroup D} {g h : D}
    (hgh : K.map (MulAut.conj g).toMonoidHom = K.map (MulAut.conj h).toMonoidHom) :
    g⁻¹ * h ∈ Subgroup.normalizer (K : Set D) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  have hy := congrArg (fun H : Subgroup D => h * x * h⁻¹ ∈ H) hgh
  simp only [mem_map_conj_iff, eq_iff_iff] at hy
  have e1 : h⁻¹ * (h * x * h⁻¹) * h = x := by group
  have e2 : g⁻¹ * (h * x * h⁻¹) * g = g⁻¹ * h * x * (g⁻¹ * h)⁻¹ := by group
  rw [e1, e2] at hy
  exact hy.symm

theorem index_normalizer_le_two_of_isComponent (hO : CFSG.pPrimeCore 3 D = ⊥)
    (hm : Open.pRank 3 (⊤ : Subgroup D) ≤ 2) {K : Subgroup D} (hK : CFSG.IsComponent K) :
    (Subgroup.normalizer (K : Set D)).index ≤ 2 := by
  set N := Subgroup.normalizer (K : Set D) with hN
  by_contra hidx
  have hcard : 2 < Nat.card (D ⧸ N) := not_le.mp hidx
  obtain ⟨q₂, hq₂⟩ : ∃ q : D ⧸ N, q ≠ (QuotientGroup.mk 1 : D ⧸ N) := by
    by_contra hall
    push Not at hall
    have : Nat.card (D ⧸ N) ≤ 1 :=
      Finite.card_le_one_iff_subsingleton.mpr ⟨fun a b => (hall a).trans (hall b).symm⟩
    omega
  obtain ⟨q₃, hq₃, hq₃'⟩ : ∃ q : D ⧸ N, q ≠ (QuotientGroup.mk 1 : D ⧸ N) ∧ q ≠ q₂ := by
    by_contra hall
    push Not at hall
    have hsurj : Function.Surjective
        (fun b : Bool => if b then (QuotientGroup.mk 1 : D ⧸ N) else q₂) := by
      intro q
      by_cases h : q = QuotientGroup.mk 1
      · exact ⟨true, by simp [h]⟩
      · exact ⟨false, by simp [hall q h]⟩
    have := Nat.card_le_card_of_surjective _ hsurj
    have h2 : Nat.card Bool = 2 := by simp
    omega
  obtain ⟨g₂, rfl⟩ := QuotientGroup.mk_surjective q₂
  obtain ⟨g₃, rfl⟩ := QuotientGroup.mk_surjective q₃
  let c : D → Subgroup D := fun g => K.map (MulAut.conj g).toMonoidHom
  have hc : ∀ g, CFSG.IsComponent (c g) := fun g =>
    CFSG.LocalCores.isComponent_map_mulEquiv (MulAut.conj g) hK
  have hne : ∀ g h : D, (QuotientGroup.mk g : D ⧸ N) ≠ QuotientGroup.mk h → c g ≠ c h :=
    fun g h hgh hc' => hgh (QuotientGroup.eq.mpr (mem_normalizer_of_map_conj_eq hc'))
  have hle : ∀ g h : D, c g ≠ c h → c g ≤ Subgroup.centralizer (c h : Set D) := by
    intro g h hgh
    rcases CFSG.LocalCores.distinct_components_commute (hc g) (hc h) with heq | hbot
    · exact absurd heq hgh
    · exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp hbot
  have h12 := hne 1 g₂ (Ne.symm hq₂)
  have h13 := hne 1 g₃ (Ne.symm hq₃)
  have h23 := hne g₂ g₃ (Ne.symm hq₃')
  obtain ⟨x₁, hx₁K, hx₁, hc₁⟩ := exists_not_mem_centralizer_of_isComponent hO (hc 1)
  obtain ⟨x₂, hx₂K, hx₂, hc₂⟩ := exists_not_mem_centralizer_of_isComponent hO (hc g₂)
  obtain ⟨x₃, hx₃K, hx₃, hc₃⟩ := exists_not_mem_centralizer_of_isComponent hO (hc g₃)
  have h₂₁ := hle g₂ 1 (Ne.symm h12) hx₂K
  have h₃₁ := hle g₃ 1 (Ne.symm h13) hx₃K
  have h₁₂' := hle 1 g₂ h12 hx₁K
  have h₃₂ := hle g₃ g₂ (Ne.symm h23) hx₃K
  have h₁₃' := hle 1 g₃ h13 hx₁K
  have h₂₃' := hle g₂ g₃ h23 hx₂K
  have := three_le_pRank_of_commute (Subgroup.mem_centralizer_iff.mp h₂₁ x₁ hx₁K)
    (Subgroup.mem_centralizer_iff.mp h₃₁ x₁ hx₁K) (Subgroup.mem_centralizer_iff.mp h₃₂ x₂ hx₂K)
    hx₁ hx₂ hx₃ hc₁ hc₂ hc₃ h₂₁ h₃₁ h₁₂' h₃₂ h₁₃' h₂₃'
  omega

theorem componentConjugatesBound : ComponentConjugatesBound := by
  intro D _ _ hX K hK
  obtain ⟨X, _, _, hsq, -, ⟨e⟩⟩ := hX
  obtain ⟨hO, hm⟩ := pPrimeCore_eq_bot_and_pRank_le (hsq 3 Nat.prime_three (by norm_num)) e
  exact index_normalizer_le_two_of_isComponent hO hm hK

theorem theoremF618Cyclic_of_cases (hNQ : F617NonquasisimpleCase)
    (hQS : F618QuasisimpleCase) : TheoremF618Cyclic :=
  theoremF618Cyclic_of componentConjugatesBound hNQ hQS

theorem theoremF618_of_cases (hNQ : F617NonquasisimpleCase) (hQS : F618QuasisimpleCase) :
    TheoremF618 :=
  theoremF618_of componentConjugatesBound hNQ hQS

end F6

end CFSG.Quasithin
