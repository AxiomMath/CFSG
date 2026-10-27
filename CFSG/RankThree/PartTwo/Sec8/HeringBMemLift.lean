module

public import CFSG.RankThree.PartTwo.Sec8.Steps
public import CFSG.RankThree.PartTwo.KFacts.K72Lift
public import CFSG.RankThree.PartTwo.Sec12.Item124Bar

public section

namespace CFSG.RankThree.PartTwo.Sec8.HeringBMem

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo

theorem exists_lift_of_mem_normalizer {K : Type} [Group K] [Finite K] {T E : Subgroup K}
    [T.Normal] (hT : ¬ 3 ∣ Nat.card T) (hE : IsPGroup 3 E) {n : K ⧸ T}
    (hn : n ∈ Subgroup.normalizer
      ((E.map (QuotientGroup.mk' T) : Subgroup (K ⧸ T)) : Set (K ⧸ T))) :
    ∃ s ∈ Subgroup.normalizer (E : Set K), QuotientGroup.mk' T s = n := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨y₀, rfl⟩ := QuotientGroup.mk'_surjective T n
  have hxA : ∀ y ∈ E, y₀ * y * y₀⁻¹ ∈ E ⊔ T := by
    intro y hy
    have h1 : QuotientGroup.mk' T (y₀ * y * y₀⁻¹) ∈ E.map (QuotientGroup.mk' T) := by
      rw [map_mul, map_mul, map_inv]
      exact (Subgroup.mem_normalizer_iff.mp hn _).mp ⟨y, hy, rfl⟩
    obtain ⟨e, he, hee⟩ := h1
    have h2 : e⁻¹ * (y₀ * y * y₀⁻¹) ∈ T := by
      rw [← QuotientGroup.eq]
      exact hee
    have e1 : y₀ * y * y₀⁻¹ = e * (e⁻¹ * (y₀ * y * y₀⁻¹)) := by group
    rw [e1]
    exact Subgroup.mul_mem_sup he h2
  obtain ⟨t, htT, htN, -⟩ :=
    KFacts.exists_mul_mem_normalizer hE hT Subgroup.le_normalizer_of_normal hxA
  refine ⟨t * y₀, htN, ?_⟩
  have h1 : QuotientGroup.mk' T t = 1 := (QuotientGroup.eq_one_iff t).mpr htT
  rw [map_mul, h1, one_mul]

theorem exists_three_pow_lift {X Y : Type*} [Group X] [Group Y] [Finite X] (φ : X →* Y) {x : X}
    {k : ℕ} (hz : (φ x) ^ 3 ^ k = 1) :
    ∃ y : X, (∃ e : ℕ, y ^ 3 ^ e = 1) ∧ φ y = φ x ∧ ∃ u : ℕ, y = x ^ u := by
  obtain ⟨e, m, hm, hn⟩ := Nat.exists_eq_pow_mul_and_not_dvd (orderOf_pos x).ne' 3 (by norm_num)
  have hcop : Nat.Coprime m (3 ^ k) :=
    Nat.Coprime.pow_right k ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hm).symm
  let u := (Nat.chineseRemainder hcop 0 1 : ℕ)
  have hu0 : u ≡ 0 [MOD m] := (Nat.chineseRemainder hcop 0 1).2.1
  have hu1 : u ≡ 1 [MOD 3 ^ k] := (Nat.chineseRemainder hcop 0 1).2.2
  refine ⟨x ^ u, ⟨e, ?_⟩, ?_, u, rfl⟩
  · obtain ⟨u₀, hu₀⟩ := (Nat.modEq_zero_iff_dvd.mp hu0)
    rw [← pow_mul, hu₀, show m * u₀ * 3 ^ e = (3 ^ e * m) * u₀ by ring, pow_mul, ← hn,
      pow_orderOf_eq_one, one_pow]
  · rw [map_pow, pow_eq_pow_mod u hz, hu1]
    by_cases hk : k = 0
    · subst hk
      simp only [pow_zero, pow_one] at hz
      simp [hz]
    · have : 1 % 3 ^ k = 1 := Nat.mod_eq_of_lt (Nat.one_lt_pow hk (by norm_num))
      rw [this, pow_one]

section Normalizer

variable {G : Type} [Group G] [Finite G]

theorem conj_mem_of_mem_normalizer {H : Subgroup G} {g x : G}
    (hg : g ∈ Subgroup.normalizer (H : Set G)) (hx : x ∈ H) : g * x * g⁻¹ ∈ H :=
  (Subgroup.mem_normalizer_iff.mp hg x).mp hx

theorem mem_normalizer_sec8B {A X : Subgroup G} {g : G}
    (hgA : g ∈ Subgroup.normalizer (A : Set G)) (hgX : g ∈ Subgroup.normalizer (X : Set G)) :
    g ∈ Subgroup.normalizer ((sec8B A X : Subgroup G) : Set G) := by
  refine Subgroup.mem_normalizer_fintype fun x hx => ?_
  obtain ⟨hxA, hxXC⟩ := Subgroup.mem_inf.mp hx
  refine Subgroup.mem_inf.mpr ⟨conj_mem_of_mem_normalizer hgA hxA, ?_⟩
  have hmap : (X ⊔ Sec4.thetaQuotCentralizer X).map (MulAut.conj g).toMonoidHom ≤
      X ⊔ Sec4.thetaQuotCentralizer X := by
    rw [Subgroup.map_sup]
    refine sup_le_sup ?_ ?_
    · rintro _ ⟨y, hy, rfl⟩
      exact conj_mem_of_mem_normalizer hgX hy
    · rintro _ ⟨y, hy, rfl⟩
      exact Sec12.conj_mem_thetaQuotCentralizer hgX hy
  exact hmap ⟨x, hxXC, rfl⟩

theorem mem_normalizer_inf {H K : Subgroup G} {g : G}
    (hgH : g ∈ Subgroup.normalizer (H : Set G)) (hgK : g ∈ Subgroup.normalizer (K : Set G)) :
    g ∈ Subgroup.normalizer ((H ⊓ K : Subgroup G) : Set G) :=
  Subgroup.mem_normalizer_fintype fun _ hx =>
    ⟨conj_mem_of_mem_normalizer hgH hx.1, conj_mem_of_mem_normalizer hgK hx.2⟩

theorem mem_normalizer_zpowers_sup {H : Subgroup G} {a g : G}
    (hgH : g ∈ Subgroup.normalizer (H : Set G)) (hga : g * a = a * g) :
    g ∈ Subgroup.normalizer ((Subgroup.zpowers a ⊔ H : Subgroup G) : Set G) := by
  refine Subgroup.mem_normalizer_fintype fun x hx => ?_
  have hmap : (Subgroup.zpowers a ⊔ H).map (MulAut.conj g).toMonoidHom ≤
      Subgroup.zpowers a ⊔ H := by
    rw [Subgroup.map_sup]
    refine sup_le_sup ?_ ?_
    · rintro _ ⟨y, hy, rfl⟩
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
      have : g * a ^ k * g⁻¹ = a ^ k := by
        have h1 : g * a ^ k = a ^ k * g := (Commute.zpow_right (show Commute g a from hga) k).eq
        rw [h1]
        group
      show g * a ^ k * g⁻¹ ∈ _
      rw [this]
      exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers a) k
    · rintro _ ⟨y, hy, rfl⟩
      exact conj_mem_of_mem_normalizer hgH hy
  exact hmap ⟨x, hx, rfl⟩

end Normalizer

end CFSG.RankThree.PartTwo.Sec8.HeringBMem
