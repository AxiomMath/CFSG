module

public import CFSG.RankThree.PartTwo.Sec21.FF79Sec3L4Lift2
public import CFSG.RankThree.PartTwo.Sec21.FF79Lemma41Base

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF79

open CFSG CFSG.RankThree.PartTwo.Sec21

section Abstract

variable {Γ : Type} [Group Γ] [Finite Γ]

theorem fix_lift_gen (Q : Subgroup Γ) (hQ : Nat.Coprime 3 (Nat.card Q)) (σ : MulAut Γ)
    (h3 : ∀ x, σ (σ (σ x)) = x) (hσQ : ∀ q ∈ Q, σ q ∈ Q) (c₀ : Γ)
    (h : (σ c₀)⁻¹ * c₀ ∈ Q) : ∃ q ∈ Q, σ (c₀ * q) = c₀ * q := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let X : Type _ := {x : Γ // c₀⁻¹ * x ∈ Q}
  have hmem : ∀ x : X, c₀⁻¹ * σ x.1 ∈ Q := by
    intro x
    have h1 : c₀⁻¹ * σ x.1 = (c₀⁻¹ * σ c₀) * σ (c₀⁻¹ * x.1) := by
      simp [map_mul, mul_assoc]
    rw [h1]
    refine Q.mul_mem ?_ (hσQ _ x.2)
    have := Q.inv_mem h
    simpa [mul_assoc] using this
  let f : X → X := fun x => ⟨σ x.1, hmem x⟩
  have hfinj : Function.Injective f := by
    intro x y hxy
    exact Subtype.ext (σ.injective (congrArg Subtype.val hxy))
  have hfbij : Function.Bijective f := Finite.injective_iff_bijective.mp hfinj
  let π : Equiv.Perm X := Equiv.ofBijective f hfbij
  have hπ3 : π ^ 3 = 1 := by
    ext x
    show (π (π (π x))).1 = x.1
    exact h3 x.1
  have hXcard : Nat.card X = Nat.card Q := by
    refine Nat.card_congr
      { toFun := fun x => ⟨c₀⁻¹ * x.1, x.2⟩
        invFun := fun q => ⟨c₀ * q.1, by simpa using q.2⟩
        left_inv := fun x => by ext; simp
        right_inv := fun q => by ext; simp }
  haveI : Fintype X := Fintype.ofFinite X
  have hndvd : ¬ 3 ∣ Fintype.card X := by
    rw [← Nat.card_eq_fintype_card, hXcard]
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp hQ
  obtain ⟨x, hx⟩ := Equiv.Perm.exists_fixed_point_of_prime (p := 3) (n := 1) hndvd
    (by simpa using hπ3)
  refine ⟨c₀⁻¹ * x.1, x.2, ?_⟩
  have : σ x.1 = x.1 := congrArg Subtype.val hx
  simpa using this

theorem isSylowOf_sup_normal (Q P : Subgroup Γ) [Q.Normal] (hQ : Nat.Coprime 3 (Nat.card Q))
    (hP : IsPGroup 3 P) : IsSylowOf 3 P (Q ⊔ P) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hPR : P ≤ Q ⊔ P := le_sup_right
  have hQR : Q ≤ Q ⊔ P := le_sup_left
  let P' : Subgroup ↥(Q ⊔ P) := P.subgroupOf (Q ⊔ P)
  have hP' : IsPGroup 3 P' := hP.of_equiv (Subgroup.subgroupOfEquivOfLe hPR).symm
  obtain ⟨S, hS⟩ := hP'.exists_le_sylow
  have hSP : (S : Subgroup ↥(Q ⊔ P)) ≤ P' := by
    intro s hs
    have hsR : (s : Γ) ∈ Q ⊔ P := s.2
    obtain ⟨q, hq, p, hp, hqp⟩ := Subgroup.mem_sup_of_normal_left.mp hsR
    have hpS : (⟨p, hPR hp⟩ : ↥(Q ⊔ P)) ∈ (S : Subgroup ↥(Q ⊔ P)) :=
      hS (show _ ∈ P' from hp)
    have hqS : (⟨q, hQR hq⟩ : ↥(Q ⊔ P)) ∈ (S : Subgroup ↥(Q ⊔ P)) := by
      have : (⟨q, hQR hq⟩ : ↥(Q ⊔ P)) = s * (⟨p, hPR hp⟩ : ↥(Q ⊔ P))⁻¹ := by
        apply Subtype.ext
        simp [← hqp]
      rw [this]
      exact S.mul_mem hs (S.inv_mem hpS)
    have hcop : Nat.Coprime 3 (Nat.card (Q.subgroupOf (Q ⊔ P))) := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQR).toEquiv]
      exact hQ
    have h1 := eq_one_of_pgroup_of_coprime (P := (S : Subgroup ↥(Q ⊔ P)))
      (Q := Q.subgroupOf (Q ⊔ P)) S.isPGroup' hcop hqS (show _ ∈ Q.subgroupOf (Q ⊔ P) from hq)
    have hq1 : q = 1 := congrArg Subtype.val h1
    show (s : Γ) ∈ P
    rw [← hqp, hq1, one_mul]
    exact hp
  have hPS : P' = S := le_antisymm hS hSP
  refine ⟨hPR, hP, ?_⟩
  have h2 : P.relIndex (Q ⊔ P) = (S : Subgroup ↥(Q ⊔ P)).index := by
    rw [Subgroup.relIndex]
    exact congrArg Subgroup.index hPS
  rw [h2]
  exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr S.not_dvd_index

theorem tau_mem_nor {P : Subgroup Γ} (τ : MulAut Γ) (h3 : ∀ x, τ (τ (τ x)) = x)
    (hτP : ∀ x, x ∈ P ↔ τ x ∈ P) {y : Γ} (hy : ∀ x ∈ P, y * x * y⁻¹ ∈ P) :
    ∀ x ∈ P, τ y * x * (τ y)⁻¹ ∈ P := by
  intro x hx
  have hx' : τ (τ x) ∈ P := (hτP _).mp ((hτP _).mp hx)
  have h1 := hy _ hx'
  have h2 := (hτP _).mp h1
  have : τ (y * τ (τ x) * y⁻¹) = τ y * x * (τ y)⁻¹ := by
    simp [map_mul, map_inv, h3]
  rwa [this] at h2

theorem sigma_frattini_fix (Q : Subgroup Γ) [Q.Normal] (hQ : Nat.Coprime 3 (Nat.card Q))
    (P : Subgroup Γ) (hP : IsPGroup 3 P) (τ : MulAut Γ) (h3 : ∀ x, τ (τ (τ x)) = x)
    (hτQ : ∀ q ∈ Q, τ q ∈ Q) (hτP : ∀ x, x ∈ P ↔ τ x ∈ P) (g : Γ) (hg : τ g = g)
    (hgP : ∀ x ∈ P, g * x * g⁻¹ ∈ Q ⊔ P) :
    ∃ g' : Γ, τ g' = g' ∧ (∀ x ∈ P, g' * x * g'⁻¹ ∈ P) ∧ g'⁻¹ * g ∈ Q := by
  have hS := isSylowOf_sup_normal Q P hQ hP
  have hQ₂R : conjBy g P ≤ Q ⊔ P := by
    rintro _ ⟨y, hy, rfl⟩
    exact hgP y hy
  have hQ₂p : IsPGroup 3 (conjBy g P) := hP.map _
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨k, hkR, hk⟩ := L41.exists_conj_le_sylowOf_p hS hQ₂R hQ₂p
  obtain ⟨q, hq, p, hp, hqp⟩ := Subgroup.mem_sup_of_normal_left.mp hkR
  have hq₁ : p⁻¹ * q * p ∈ Q := by
    simpa using (inferInstance : Q.Normal).conj_mem q hq p⁻¹
  have hg₁ : ∀ x ∈ P, (p⁻¹ * q * p * g) * x * (p⁻¹ * q * p * g)⁻¹ ∈ P := by
    intro x hx
    have h1 := hk (g * x * g⁻¹) ⟨x, hx, rfl⟩
    rw [← hqp] at h1
    have h2 := P.mul_mem (P.mul_mem (P.inv_mem hp) h1) hp
    convert h2 using 1
    group
  obtain ⟨q₁, hq₁Q, hg₁⟩ : ∃ q₁ ∈ Q, ∀ x ∈ P, (q₁ * g) * x * (q₁ * g)⁻¹ ∈ P := ⟨_, hq₁, hg₁⟩
  have hg₁nor : q₁ * g ∈ Nor P := L41.mem_nor_of_forall hg₁
  have hτg₁ : ∀ x ∈ P, τ (q₁ * g) * x * (τ (q₁ * g))⁻¹ ∈ P := tau_mem_nor τ h3 hτP hg₁
  have hτg₁nor : τ (q₁ * g) ∈ Nor P := L41.mem_nor_of_forall hτg₁
  have hcop : Nat.Coprime 3 (Nat.card (Q ⊓ Nor P : Subgroup Γ)) :=
    Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le inf_le_left) hQ
  have hstab : ∀ y ∈ (Q ⊓ Nor P : Subgroup Γ), τ y ∈ (Q ⊓ Nor P : Subgroup Γ) := by
    intro y hy
    obtain ⟨hyQ, hyN⟩ := Subgroup.mem_inf.mp hy
    refine Subgroup.mem_inf.mpr ⟨hτQ y hyQ, L41.mem_nor_of_forall ?_⟩
    exact tau_mem_nor τ h3 hτP fun x hx => (Subgroup.mem_set_normalizer_iff.mp hyN x).mp hx
  obtain ⟨q₀, hq₀, hfix⟩ := fix_lift_gen (Q ⊓ Nor P) hcop τ h3 hstab (q₁ * g) (by
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · have : (τ (q₁ * g))⁻¹ * (q₁ * g) = g⁻¹ * ((τ q₁)⁻¹ * q₁) * g := by
        rw [map_mul, hg]
        group
      rw [this]
      have h5 := Q.mul_mem (Q.inv_mem (hτQ _ hq₁Q)) hq₁Q
      simpa using (inferInstance : Q.Normal).conj_mem _ h5 g⁻¹
    · exact Subgroup.mul_mem _ (Subgroup.inv_mem _ hτg₁nor) hg₁nor)
  refine ⟨q₁ * g * q₀, hfix, ?_, ?_⟩
  · have hq₀N : q₀ ∈ Nor P := (Subgroup.mem_inf.mp hq₀).2
    have hmem : q₁ * g * q₀ ∈ Nor P := Subgroup.mul_mem _ hg₁nor hq₀N
    intro x hx
    exact (Subgroup.mem_set_normalizer_iff.mp hmem x).mp hx
  · have : (q₁ * g * q₀)⁻¹ * g = q₀⁻¹ * (g⁻¹ * q₁⁻¹ * g) := by group
    rw [this]
    refine Q.mul_mem (Q.inv_mem (Subgroup.mem_inf.mp hq₀).1) ?_
    simpa [mul_assoc] using (inferInstance : Q.Normal).conj_mem _ (Q.inv_mem hq₁Q) g⁻¹

end Abstract

end CFSG.RankThree.PartTwo.Sec21.FF79
