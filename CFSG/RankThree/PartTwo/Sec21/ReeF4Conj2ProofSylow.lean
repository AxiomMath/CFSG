module

public import Mathlib.GroupTheory.Sylow
public import Mathlib.GroupTheory.IndexNormal

public section

namespace CFSG.RankThree.PartTwo.Sec8.ReeF4Conj2Proof

variable {Γ : Type*} [Group Γ] [Finite Γ]

@[expose] def torsion3 (T : Subgroup Γ) (hT : ∀ x ∈ T, ∀ y ∈ T, x * y = y * x) : Subgroup Γ where
  carrier := {t | t ∈ T ∧ t ^ 3 = 1}
  mul_mem' := fun {x y} hx hy => ⟨mul_mem hx.1 hy.1, by
    rw [(Commute.mul_pow (hT x hx.1 y hy.1) 3), hx.2, hy.2, one_mul]⟩
  one_mem' := ⟨one_mem T, one_pow 3⟩
  inv_mem' := fun {x} hx => ⟨inv_mem hx.1, by rw [inv_pow, hx.2, inv_one]⟩

theorem normal_of_index_dvd_prime {p : ℕ} [hp : Fact p.Prime] {P : Type*} [Group P] [Finite P]
    (hP : IsPGroup p P) (H : Subgroup P) (hH : H.index ∣ p) : H.Normal := by
  rcases (Nat.dvd_prime hp.out).1 hH with h1 | hpH
  · exact Subgroup.normal_of_index_eq_one h1
  · refine Subgroup.normal_of_index_eq_minFac_card ?_
    obtain ⟨k, hk⟩ := hP.exists_card_eq
    have hk0 : k ≠ 0 := by
      rintro rfl
      have := H.index_dvd_card
      rw [hpH, hk, pow_zero] at this
      exact hp.out.one_lt.ne' (Nat.dvd_one.1 this)
    rw [hpH, hk, Nat.Prime.pow_minFac hp.out hk0]

theorem relindex_dvd_three (T : Subgroup Γ) (hidx : ¬ 9 ∣ T.index) (S : Sylow 3 T)
    (P : Sylow 3 Γ) (hle : (S : Subgroup T).map T.subtype ≤ P) :
    (((S : Subgroup T).map T.subtype).subgroupOf (P : Subgroup Γ)).index ∣ 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hT3 : Nat.card ((S : Subgroup T).map T.subtype) = 3 ^ (Nat.card T).factorization 3 := by
    rw [Nat.card_congr (Subgroup.equivMapOfInjective _ _ T.subtype_injective).symm.toEquiv]
    exact S.card_eq_multiplicity
  have hP3 : Nat.card (P : Subgroup Γ) = 3 ^ (Nat.card Γ).factorization 3 :=
    P.card_eq_multiplicity
  have hcardΓ : Nat.card Γ = Nat.card T * T.index := (Subgroup.card_mul_index T).symm
  have hT0 : Nat.card T ≠ 0 := Nat.card_pos.ne'
  have hi0 : T.index ≠ 0 := Subgroup.index_ne_zero_of_finite
  have hv : (Nat.card Γ).factorization 3 =
      (Nat.card T).factorization 3 + T.index.factorization 3 := by
    rw [hcardΓ, Nat.factorization_mul hT0 hi0, Finsupp.add_apply]
  have hvi : T.index.factorization 3 ≤ 1 := by
    by_contra h
    push Not at h
    apply hidx
    have h2 : 3 ^ 2 ∣ T.index :=
      (Nat.pow_dvd_pow 3 h).trans (Nat.ordProj_dvd T.index 3)
    simpa using h2
  have hrel := Subgroup.card_mul_index
    (((S : Subgroup T).map T.subtype).subgroupOf (P : Subgroup Γ))
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv, hT3, hP3, hv, pow_add] at hrel
  have hpos : 0 < 3 ^ (Nat.card T).factorization 3 := pow_pos (by norm_num) _
  have hidx' := Nat.eq_of_mul_eq_mul_left hpos hrel
  rw [hidx']
  interval_cases h : T.index.factorization 3 <;> simp

theorem exists_conj_commute_torsion (T : Subgroup Γ) (hT : ∀ x ∈ T, ∀ y ∈ T, x * y = y * x)
    (hidx : ¬ 9 ∣ T.index) {a₀ : Γ} (ha₀T : a₀ ∈ T) (ha₀1 : a₀ ≠ 1) (ha₀3 : a₀ ^ 3 = 1)
    {y : Γ} (hy : y ^ 3 = 1) :
    ∃ g : Γ, ∃ z ∈ T, z ≠ 1 ∧ z ^ 3 = 1 ∧ g⁻¹ * y * g * z = z * (g⁻¹ * y * g) := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set A := torsion3 T hT with hA
  have hAp : IsPGroup 3 (A.subgroupOf T) := by
    intro t
    refine ⟨1, ?_⟩
    have h3 : ((t : T) : Γ) ^ 3 = 1 := (Subgroup.mem_subgroupOf.1 t.2).2
    apply Subtype.ext
    apply Subtype.ext
    simpa using h3
  obtain ⟨S, hAS⟩ := hAp.exists_le_sylow
  set T₃ := (S : Subgroup T).map T.subtype with hT₃
  have hT₃p : IsPGroup 3 T₃ := S.isPGroup'.map T.subtype
  obtain ⟨P, hT₃P⟩ := hT₃p.exists_le_sylow
  have hAT₃ : A ≤ T₃ := by
    intro t ht
    exact ⟨⟨t, ht.1⟩, hAS (Subgroup.mem_subgroupOf.2 ht), rfl⟩
  have hT₃T : T₃ ≤ T := by
    rintro _ ⟨t, -, rfl⟩
    exact t.2
  have hnorm : (T₃.subgroupOf (P : Subgroup Γ)).Normal :=
    normal_of_index_dvd_prime P.isPGroup' _ (relindex_dvd_three T hidx S P hT₃P)
  have hyp : IsPGroup 3 (Subgroup.zpowers y) := by
    rintro ⟨_, k, rfl⟩
    refine ⟨1, Subtype.ext ?_⟩
    simp only [pow_one, Subgroup.coe_pow, Subgroup.coe_one]
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hy, one_zpow]
  obtain ⟨Q, hQ⟩ := hyp.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq Γ P Q
  have hyQ : y ∈ (Q : Subgroup Γ) := hQ (Subgroup.mem_zpowers y)
  rw [← hg, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hyQ
  have hy₁P : g⁻¹ * y * g ∈ (P : Subgroup Γ) := by
    have : (MulAut.conj g)⁻¹ • y = g⁻¹ * y * g := by
      simp [MulAut.smul_def]
    rw [← this]
    exact hyQ
  set y₁ := g⁻¹ * y * g with hy₁
  have hy₁3 : y₁ ^ 3 = 1 := by
    rw [hy₁, show g⁻¹ * y * g = g⁻¹ * y * g⁻¹⁻¹ by rw [inv_inv], conj_pow, hy]
    group
  set φ : Γ → Γ := fun t => y₁ * t * y₁⁻¹ with hφ
  have hφA : ∀ t ∈ A, φ t ∈ A := by
    intro t ht
    have h1 : φ t ∈ T₃ := by
      have := hnorm.conj_mem ⟨t, hT₃P (hAT₃ ht)⟩ (Subgroup.mem_subgroupOf.2 (hAT₃ ht))
        ⟨y₁, hy₁P⟩
      exact Subgroup.mem_subgroupOf.1 this
    refine ⟨hT₃T h1, ?_⟩
    show (y₁ * t * y₁⁻¹) ^ 3 = 1
    rw [conj_pow, ht.2]
    group
  have hφ3 : ∀ t, φ (φ (φ t)) = t := by
    intro t
    have h : y₁ * (y₁ * (y₁ * t * y₁⁻¹) * y₁⁻¹) * y₁⁻¹ =
        y₁ * y₁ * y₁ * t * (y₁ * y₁ * y₁)⁻¹ := by group
    have h3 : y₁ * y₁ * y₁ = 1 := by rw [← pow_three', hy₁3]
    show y₁ * (y₁ * (y₁ * t * y₁⁻¹) * y₁⁻¹) * y₁⁻¹ = t
    rw [h, h3]
    group
  have hφmul : ∀ s t, φ (s * t) = φ s * φ t := by
    intro s t
    simp only [hφ]
    group
  have hφinv : ∀ t, φ t⁻¹ = (φ t)⁻¹ := by
    intro t
    simp only [hφ]
    group
  have hcomm : ∀ s ∈ A, ∀ t ∈ A, s * t = t * s := fun s hs t ht => hT s hs.1 t ht.1
  have hfix : ∀ z ∈ A, z ≠ 1 → φ z = z →
      ∃ g : Γ, ∃ z ∈ T, z ≠ 1 ∧ z ^ 3 = 1 ∧ g⁻¹ * y * g * z = z * (g⁻¹ * y * g) := by
    intro z hz hz1 hφz
    refine ⟨g, z, hz.1, hz1, hz.2, ?_⟩
    have h : y₁ * z * y₁⁻¹ = z := hφz
    calc y₁ * z = y₁ * z * y₁⁻¹ * y₁ := by group
      _ = z * y₁ := by rw [h]
  have ha₀ : a₀ ∈ A := ⟨ha₀T, ha₀3⟩
  have hφa := hφA a₀ ha₀
  have hφφa := hφA _ hφa
  by_cases hN : a₀ * φ a₀ * φ (φ a₀) = 1
  ·
    by_cases hb : φ a₀ * a₀⁻¹ = 1
    · refine hfix a₀ ha₀ ha₀1 ?_
      exact (mul_inv_eq_one.1 hb)
    · refine hfix (φ a₀ * a₀⁻¹) (mul_mem hφa (inv_mem ha₀)) hb ?_
      rw [hφmul, hφinv]
      have h2 : φ (φ a₀) = (a₀ * φ a₀)⁻¹ := eq_inv_of_mul_eq_one_right hN
      rw [h2]
      have h3 : (φ a₀) ^ 3 = 1 := (hφA _ ha₀).2
      have hc := hcomm a₀ ha₀ (φ a₀) hφa
      calc (a₀ * φ a₀)⁻¹ * (φ a₀)⁻¹ = a₀⁻¹ * ((φ a₀)⁻¹ * (φ a₀)⁻¹) := by
            rw [mul_inv_rev, hcomm _ (inv_mem hφa) _ (inv_mem ha₀)]
            group
        _ = a₀⁻¹ * φ a₀ := by
            congr 1
            calc (φ a₀)⁻¹ * (φ a₀)⁻¹ = (φ a₀)⁻¹ * (φ a₀)⁻¹ * (φ a₀) ^ 3 := by rw [h3, mul_one]
              _ = φ a₀ := by group
        _ = φ a₀ * a₀⁻¹ := hcomm _ (inv_mem ha₀) _ hφa
  · refine hfix _ (mul_mem (mul_mem ha₀ hφa) hφφa) hN ?_
    rw [hφmul, hφmul, hφ3]
    have h1 := hcomm a₀ ha₀ (φ a₀ * φ (φ a₀)) (mul_mem hφa hφφa)
    rw [mul_assoc a₀, h1, mul_assoc]

end CFSG.RankThree.PartTwo.Sec8.ReeF4Conj2Proof
