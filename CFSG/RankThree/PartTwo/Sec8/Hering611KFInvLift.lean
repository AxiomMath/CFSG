module

public import CFSG.RankThree.PartTwo.Sec6.Item612Basic
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.CardSupOfDisjointNormalizer

public section

namespace CFSG.RankThree.PartTwo.Sec8.Hering611

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

theorem exists_conj_mem_zpowers_of_mem_sup {θ : Subgroup G} {c y : G} (hc3 : orderOf c = 3)
    (hy3 : orderOf y = 3) (hθ3 : ¬ 3 ∣ Nat.card θ) (hcθ : c ∈ Subgroup.normalizer (θ : Set G))
    (hyR : y ∈ θ ⊔ Subgroup.zpowers c) : ∃ u ∈ θ, u⁻¹ * y * u ∈ Subgroup.zpowers c := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set X := Subgroup.zpowers c with hX
  set Y := Subgroup.zpowers y with hY
  set R := θ ⊔ X with hR
  have hXθ : X ≤ Subgroup.normalizer (θ : Set G) := Subgroup.zpowers_le.mpr hcθ
  have hcop : Nat.Coprime 3 (Nat.card θ) := (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hθ3
  have hdisj : Disjoint θ X := by
    rw [Subgroup.disjoint_def]
    intro x hxθ hxX
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hxX
    have hc3' : c ^ 3 = 1 := hc3 ▸ pow_orderOf_eq_one c
    have hx3 : (c ^ k) ^ 3 = 1 := by
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hc3', one_zpow]
    have h1 : orderOf (c ^ k) ∣ 3 := orderOf_dvd_of_pow_eq_one hx3
    have h2 := Subgroup.orderOf_dvd_natCard _ hxθ
    exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop h1 h2)
  have hXcard : Nat.card X = 3 := by rw [hX, Nat.card_zpowers, hc3]
  have hYcard : Nat.card Y = 3 := by rw [hY, Nat.card_zpowers, hy3]
  have hRcard : Nat.card R = Nat.card θ * 3 := by
    rw [hR, CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer θ X hXθ hdisj,
      hXcard]
  have hXR : X ≤ R := le_sup_right
  have hYR : Y ≤ R := Subgroup.zpowers_le.mpr hyR
  have hval : (Nat.card R).factorization 3 = 1 := by
    have hθ0 : Nat.card θ ≠ 0 := Nat.card_pos.ne'
    rw [hRcard, Nat.factorization_mul hθ0 (by norm_num), Finsupp.add_apply,
      Nat.factorization_eq_zero_of_not_dvd hθ3, zero_add,
      Nat.Prime.factorization_self Nat.prime_three]
  have hXs : Nat.card (X.subgroupOf R) = 3 ^ (Nat.card R).factorization 3 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hXR).toEquiv, hXcard, hval, pow_one]
  have hYs : Nat.card (Y.subgroupOf R) = 3 ^ (Nat.card R).factorization 3 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hYR).toEquiv, hYcard, hval, pow_one]
  let PX : Sylow 3 R := Sylow.ofCard (X.subgroupOf R) hXs
  let PY : Sylow 3 R := Sylow.ofCard (Y.subgroupOf R) hYs
  have hPX : (PX : Subgroup R) = X.subgroupOf R := Sylow.coe_ofCard _ _
  have hPY : (PY : Subgroup R) = Y.subgroupOf R := Sylow.coe_ofCard _ _
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq R PX PY
  have hyY : (⟨y, hyR⟩ : R) ∈ (PY : Subgroup R) := by
    rw [hPY, Subgroup.mem_subgroupOf]
    exact Subgroup.mem_zpowers y
  have hmem : g⁻¹ * ⟨y, hyR⟩ * g ∈ (PX : Subgroup R) := by
    rw [← hg, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hyY
    simpa [MulAut.smul_def, MulAut.conj_apply, mul_assoc] using hyY
  rw [hPX, Subgroup.mem_subgroupOf] at hmem
  obtain ⟨g', hg'⟩ := g
  have hg'R : g' ∈ ((θ : Set G) * (X : Set G)) := by
    rw [← Subgroup.coe_mul_of_right_le_normalizer_left θ X hXθ]
    exact hg'
  obtain ⟨u, hu, x, hx, rfl⟩ := Set.mem_mul.mp hg'R
  refine ⟨u, hu, ?_⟩
  have h1 : x⁻¹ * (u⁻¹ * y * u) * x ∈ X := by
    have := hmem
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, InvMemClass.coe_inv] at this
    have e : (u * x)⁻¹ * y * (u * x) = x⁻¹ * (u⁻¹ * y * u) * x := by group
    rw [← e]
    exact this
  have h2 := X.mul_mem (X.mul_mem hx h1) (X.inv_mem hx)
  have e2 : x * (x⁻¹ * (u⁻¹ * y * u) * x) * x⁻¹ = u⁻¹ * y * u := by group
  rwa [e2] at h2

theorem exists_involution_lift {K : Subgroup G} {c t₀ e : G}
    (hcN : c ∈ Subgroup.normalizer (K : Set G)) (hc3 : orderOf c = 3)
    (hθodd : Odd (Nat.card (inSubgroup (aschbacherSolvableCore 3) K))) (hce : e = c ∨ e = c⁻¹)
    (ht₀K : t₀ ∈ K) (ht₀θ : t₀ ∉ inSubgroup (aschbacherSolvableCore 3) K)
    (ht₀sq : t₀ ^ 2 ∈ inSubgroup (aschbacherSolvableCore 3) K)
    (hrel : t₀ * c * t₀⁻¹ * e⁻¹ ∈ inSubgroup (aschbacherSolvableCore 3) K) :
    ∃ s : G, s ∈ K ∧ s ^ 2 = 1 ∧ s⁻¹ * t₀ ∈ inSubgroup (aschbacherSolvableCore 3) K ∧
      s * c * s⁻¹ = e := by
  classical
  set θ := inSubgroup (aschbacherSolvableCore 3) K with hθ
  have hθ3 : ¬ 3 ∣ Nat.card θ := (Sec6.theta_solvable_and_not_dvd K).2
  have hθK : θ ≤ K := Sec6.theta_le K
  have hcθ : c ∈ Subgroup.normalizer (θ : Set G) := Sec6.normalizer_le_normalizer_theta K hcN
  have ht₀θN : t₀ ∈ Subgroup.normalizer (θ : Set G) := Sec6.le_normalizer_theta K ht₀K
  have hec : e ∈ Subgroup.zpowers c := by
    rcases hce with rfl | rfl
    · exact Subgroup.mem_zpowers _
    · exact Subgroup.inv_mem _ (Subgroup.mem_zpowers _)
  set y := t₀ * c * t₀⁻¹ with hy
  have hy3 : orderOf y = 3 := by
    rw [hy, ← hc3]
    exact orderOf_injective (MulAut.conj t₀).toMonoidHom (MulAut.conj t₀).injective c
  have hyR : y ∈ θ ⊔ Subgroup.zpowers c := by
    have : y = (y * e⁻¹) * e := by group
    rw [this]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hrel) (Subgroup.mem_sup_right hec)
  obtain ⟨u, huθ, hu⟩ := exists_conj_mem_zpowers_of_mem_sup hc3 hy3 hθ3 hcθ hyR
  set s₁ := u⁻¹ * t₀ with hs₁
  have hs₁K : s₁ ∈ K := K.mul_mem (K.inv_mem (hθK huθ)) ht₀K
  have hs₁c : s₁ * c * s₁⁻¹ = e := by
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hu
    have h1 : s₁ * c * s₁⁻¹ = c ^ k := by rw [hk, hs₁, hy]; group
    have h2 : (c ^ k) * e⁻¹ ∈ θ := by
      rw [← h1]
      have : s₁ * c * s₁⁻¹ * e⁻¹ = (u⁻¹ * (t₀ * c * t₀⁻¹ * e⁻¹)) * (e * u * e⁻¹) := by
        rw [hs₁]; group
      rw [this]
      have heθ : e * u * e⁻¹ ∈ θ :=
        (Subgroup.mem_normalizer_iff.mp (Subgroup.zpowers_le.mpr hcθ hec) u).mp huθ
      exact θ.mul_mem (θ.mul_mem (θ.inv_mem huθ) hrel) heθ
    have h3 : c ^ k * e⁻¹ ∈ Subgroup.zpowers c :=
      Subgroup.mul_mem _ (Subgroup.zpow_mem _ (Subgroup.mem_zpowers c) k)
        (Subgroup.inv_mem _ hec)
    have hc3' : c ^ 3 = 1 := hc3 ▸ pow_orderOf_eq_one c
    have hdisj : (c ^ k * e⁻¹) = 1 := by
      obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp h3
      have hx3 : (c ^ j) ^ 3 = 1 := by
        rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hc3', one_zpow]
      rw [← hj] at h2 ⊢
      have h1' : orderOf (c ^ j) ∣ 3 := orderOf_dvd_of_pow_eq_one hx3
      have h2' := Subgroup.orderOf_dvd_natCard _ h2
      have hcop : Nat.Coprime 3 (Nat.card θ) :=
        (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hθ3
      exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop h1' h2')
    exact (mul_inv_eq_one.mp hdisj ▸ h1)
  have hs₁sq : s₁ ^ 2 ∈ θ := by
    have hq : s₁ ^ 2 = u⁻¹ * (t₀ * u⁻¹ * t₀⁻¹) * t₀ ^ 2 := by rw [hs₁, pow_two, pow_two]; group
    rw [hq]
    refine θ.mul_mem (θ.mul_mem (θ.inv_mem huθ) ?_) ht₀sq
    exact (Subgroup.mem_normalizer_iff.mp ht₀θN u⁻¹).mp (θ.inv_mem huθ)
  have hs₁θ : s₁ ∉ θ := by
    intro h
    exact ht₀θ (by
      have : t₀ = u * s₁ := by rw [hs₁]; group
      rw [this]
      exact θ.mul_mem huθ h)
  have hs₁e : s₁ * e * s₁⁻¹ = c := by
    rcases hce with rfl | rfl
    · exact hs₁c
    · have : s₁ * c⁻¹ * s₁⁻¹ = (s₁ * c * s₁⁻¹)⁻¹ := by group
      rw [this, hs₁c, inv_inv]
  have hs₁sqc : s₁ ^ 2 * c * (s₁ ^ 2)⁻¹ = c := by
    have : s₁ ^ 2 * c * (s₁ ^ 2)⁻¹ = s₁ * (s₁ * c * s₁⁻¹) * s₁⁻¹ := by rw [pow_two]; group
    rw [this, hs₁c, hs₁e]
  obtain ⟨a, m, hm, hn⟩ := Nat.exists_eq_two_pow_mul_odd (n := orderOf s₁) (orderOf_pos s₁).ne'
  obtain ⟨r, rfl⟩ := hm
  set s := s₁ * (s₁ ^ 2) ^ r with hs
  have hsK : s ∈ K := K.mul_mem hs₁K (Subgroup.pow_mem _ (Subgroup.pow_mem _ hs₁K 2) r)
  have hs_eq : s = s₁ ^ (2 * r + 1) := by rw [hs, ← pow_mul, ← pow_succ']
  have hspow : s ^ (2 ^ a) = 1 := by
    rw [hs_eq, ← pow_mul, mul_comm, ← hn]
    exact pow_orderOf_eq_one s₁
  have hssq : s ^ 2 ∈ θ := by
    have : s ^ 2 = (s₁ ^ 2) ^ (2 * r + 1) := by rw [hs_eq, ← pow_mul, ← pow_mul, mul_comm]
    rw [this]
    exact Subgroup.pow_mem _ hs₁sq _
  have hodd : Odd (Nat.card θ) := hθodd
  have hs2 : s ^ 2 = 1 := by
    have h1 : orderOf (s ^ 2) ∣ 2 ^ a := by
      apply orderOf_dvd_of_pow_eq_one
      rw [← pow_mul, mul_comm, pow_mul, hspow, one_pow]
    have h2 := Subgroup.orderOf_dvd_natCard _ hssq
    have hcop : Nat.Coprime (2 ^ a) (Nat.card θ) :=
      Nat.Coprime.pow_left _ ((Nat.coprime_two_left).mpr hodd)
    exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop h1 h2)
  have hsθ : s⁻¹ * t₀ ∈ θ := by
    have e1 : s⁻¹ * t₀ = ((s₁ ^ 2) ^ r)⁻¹ * (s₁⁻¹ * t₀) := by rw [hs]; group
    rw [e1]
    refine θ.mul_mem (θ.inv_mem (Subgroup.pow_mem _ hs₁sq r)) ?_
    have : s₁⁻¹ * t₀ = t₀⁻¹ * u * t₀ := by rw [hs₁]; group
    rw [this]
    have h3 := (Subgroup.mem_normalizer_iff.mp (inv_mem ht₀θN) u).mp huθ
    simpa using h3
  have hsc : s * c * s⁻¹ = e := by
    have hcomm : ((s₁ ^ 2) ^ r) * c * ((s₁ ^ 2) ^ r)⁻¹ = c := by
      have hc' : Commute (s₁ ^ 2) c := by
        have : s₁ ^ 2 * c = c * s₁ ^ 2 := by
          have := hs₁sqc
          calc s₁ ^ 2 * c = (s₁ ^ 2 * c * (s₁ ^ 2)⁻¹) * s₁ ^ 2 := by group
            _ = c * s₁ ^ 2 := by rw [this]
        exact this
      have := (hc'.pow_left r).eq
      calc ((s₁ ^ 2) ^ r) * c * ((s₁ ^ 2) ^ r)⁻¹ = c * (s₁ ^ 2) ^ r * ((s₁ ^ 2) ^ r)⁻¹ := by
            rw [this]
        _ = c := by group
    calc s * c * s⁻¹ = s₁ * (((s₁ ^ 2) ^ r) * c * ((s₁ ^ 2) ^ r)⁻¹) * s₁⁻¹ := by rw [hs]; group
      _ = e := by rw [hcomm]; exact hs₁c
  exact ⟨s, hsK, hs2, hsθ, hsc⟩

end CFSG.RankThree.PartTwo.Sec8.Hering611
