module

public import Mathlib.GroupTheory.Transfer

public section

namespace CFSG.Quasithin.RonanE43

open MonoidHom

theorem exists_retraction_of_central_three {K Zc : Type*} [Group K] [Finite K] [CommGroup Zc]
    (hZc : Nat.card Zc = 3) (ι : Zc →* K) (hι : Function.Injective ι)
    (hcent : ∀ z, ι z ∈ Subgroup.center K) {m : ℕ} (hK : Nat.card K = 9 * m) (hm : ¬ 3 ∣ m)
    (h9 : ∀ x : K, x ^ 3 ∈ ι.range → x ^ 3 = 1) : ∃ θ : K →* Zc, ∀ z, θ (ι z) = z := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Finite Zc := Nat.finite_of_card_ne_zero (by rw [hZc]; norm_num)
  have hz3 : ∀ z : Zc, z ^ 3 = 1 := fun z => by
    have := pow_card_eq_one' (G := Zc) (x := z)
    rwa [hZc] at this
  obtain ⟨P⟩ : Nonempty (Sylow 3 K) := inferInstance
  have hPcard : Nat.card (P : Subgroup K) = 9 := by
    rw [Sylow.card_eq_multiplicity, hK]
    have hm0 : m ≠ 0 := by
      rintro rfl
      simp at hm
    have h1 : (9 * m).factorization 3 = 2 := by
      rw [Nat.factorization_mul (by norm_num) hm0]
      simp only [Finsupp.coe_add, Pi.add_apply]
      have h9f : (9 : ℕ).factorization 3 = 2 := by
        have : (9 : ℕ) = 3 ^ 2 := by norm_num
        rw [this, Nat.Prime.factorization_pow Nat.prime_three]
        simp
      rw [h9f, Nat.factorization_eq_zero_of_not_dvd hm]
    rw [h1]
    norm_num
  set Zr : Subgroup K := ι.range with hZr
  have hZrcard : Nat.card Zr = 3 := by
    rw [← hZc]
    exact (Nat.card_congr (MonoidHom.ofInjective hι).toEquiv).symm
  have hZrcent : ∀ z ∈ Zr, z ∈ Subgroup.center K := by
    rintro _ ⟨z, rfl⟩
    exact hcent z
  haveI hZrn : Zr.Normal := ⟨fun n hn g => by
    have := Subgroup.mem_center_iff.mp (hZrcent n hn) g
    rw [this]
    simpa using hn⟩
  have hZrp : IsPGroup 3 Zr := IsPGroup.of_card (n := 1) (by rw [hZrcard]; norm_num)
  have hZrP : Zr ≤ (P : Subgroup K) := hZrp.le_sylow_of_normal P
  obtain ⟨x, hxP, hxZ⟩ : ∃ x ∈ (P : Subgroup K), x ∉ Zr := by
    by_contra hcon
    push Not at hcon
    have : Nat.card (P : Subgroup K) ≤ Nat.card Zr := Subgroup.card_le_of_le hcon
    rw [hPcard, hZrcard] at this
    omega
  have hx3 : x ^ 3 = 1 := by
    apply h9
    haveI : (Zr.subgroupOf (P : Subgroup K)).Normal := hZrn.subgroupOf (P : Subgroup K)
    have hidx : (Zr.subgroupOf (P : Subgroup K)).index = 3 := by
      have h1 := Subgroup.card_mul_index (Zr.subgroupOf (P : Subgroup K))
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZrP).toEquiv, hZrcard, hPcard] at h1
      omega
    have := Subgroup.pow_index_mem (Zr.subgroupOf (P : Subgroup K)) (⟨x, hxP⟩ : ↥(P : Subgroup K))
    rw [hidx] at this
    exact this
  have hx1 : x ≠ 1 := fun h => hxZ (h ▸ Zr.one_mem)
  have hxord : orderOf x = 3 := orderOf_eq_prime hx3 hx1
  have hPcomm : ∀ a b : ↥(P : Subgroup K), a * b = b * a :=
    IsPGroup.commutative_of_card_eq_prime_sq (p := 3) (by rw [hPcard]; norm_num)
  let xP : ↥(P : Subgroup K) := ⟨x, hxP⟩
  let Xs : Subgroup ↥(P : Subgroup K) := Subgroup.zpowers xP
  haveI hXsn : Xs.Normal := ⟨fun n _ g => by
    have h := hPcomm g n
    rw [show g * n * g⁻¹ = n by rw [h]; group]
    assumption⟩
  have hXscard : Nat.card Xs = 3 := by
    rw [Nat.card_zpowers]
    exact (Subgroup.orderOf_coe xP).symm.trans hxord
  have hquot : Nat.card (↥(P : Subgroup K) ⧸ Xs) = 3 := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup Xs
    rw [hPcard, hXscard] at h1
    omega
  let ιP : Zc →* ↥(P : Subgroup K) := ι.codRestrict _ (fun z => hZrP ⟨z, rfl⟩)
  let ε : Zc →* ↥(P : Subgroup K) ⧸ Xs := (QuotientGroup.mk' Xs).comp ιP
  have hεinj : Function.Injective ε := by
    rw [injective_iff_map_eq_one]
    intro z hz
    have h1 : ιP z ∈ Xs := (QuotientGroup.eq_one_iff _).mp hz
    have h2 : ι z ∈ Subgroup.zpowers x := by
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp h1
      exact Subgroup.mem_zpowers_iff.mpr ⟨k, congrArg Subtype.val hk⟩
    by_contra hz1
    have hι1 : ι z ≠ 1 := fun h => hz1 (hι (by rw [h, map_one]))
    have hcube : (ι z) ^ 3 = 1 := by
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp h2
      rw [← hk, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul]
      simp [← zpow_natCast, hx3]
    have hordz : orderOf (ι z) = 3 := orderOf_eq_prime hcube hι1
    have hle : Subgroup.zpowers (ι z) ≤ Subgroup.zpowers x :=
      (Subgroup.zpowers_le).mpr h2
    have heq : Subgroup.zpowers (ι z) = Subgroup.zpowers x := by
      apply Subgroup.eq_of_le_of_card_ge hle
      rw [Nat.card_zpowers, Nat.card_zpowers, hxord, hordz]
    apply hxZ
    have : x ∈ Subgroup.zpowers (ι z) := by rw [heq]; exact Subgroup.mem_zpowers x
    exact ((Subgroup.zpowers_le (H := Zr)).mpr (MonoidHom.mem_range.mpr ⟨z, rfl⟩)) this
  have hεbij : Function.Bijective ε :=
    hεinj.bijective_of_nat_card_le (by rw [hquot, hZc])
  let e : Zc ≃* ↥(P : Subgroup K) ⧸ Xs := MulEquiv.ofBijective ε hεbij
  let pr : ↥(P : Subgroup K) →* Zc := e.symm.toMonoidHom.comp (QuotientGroup.mk' Xs)
  have hpr : ∀ z, pr (ιP z) = z := fun z => by
    show e.symm (QuotientGroup.mk' Xs (ιP z)) = z
    have : QuotientGroup.mk' Xs (ιP z) = e z := rfl
    rw [this, MulEquiv.symm_apply_apply]
  haveI hfi : (P : Subgroup K).FiniteIndex := Subgroup.finiteIndex_of_finite
  have hidxP : (P : Subgroup K).index = m := by
    have h1 := Subgroup.card_mul_index (P : Subgroup K)
    rw [hPcard, hK] at h1
    omega
  have hτι : ∀ z, (pr.transfer : K →* Zc) (ι z) = z ^ m := by
    intro z
    have key : ∀ (k : ℕ) (g₀ : K), g₀⁻¹ * (ι z) ^ k * g₀ ∈ (P : Subgroup K) →
        g₀⁻¹ * (ι z) ^ k * g₀ = (ι z) ^ k := by
      intro k g₀ _
      have hc := Subgroup.mem_center_iff.mp
        ((Subgroup.center K).pow_mem (hcent z) k) g₀
      rw [mul_assoc, ← hc, ← mul_assoc, inv_mul_cancel, one_mul]
    rw [MonoidHom.transfer_eq_pow pr (ι z) key]
    refine (congrArg pr (Subtype.ext ?_ : _ = ιP (z ^ m))).trans (hpr _)
    show (ι z) ^ (P : Subgroup K).index = ι (z ^ m)
    rw [hidxP, map_pow]
  obtain ⟨m', hm'⟩ : ∃ m' : ℕ, m * m' % 3 = 1 := by
    have : m % 3 = 1 ∨ m % 3 = 2 := by omega
    rcases this with h | h
    · exact ⟨1, by omega⟩
    · exact ⟨2, by omega⟩
  refine ⟨(pr.transfer : K →* Zc) ^ m', fun z => ?_⟩
  rw [MonoidHom.pow_apply, hτι, ← pow_mul]
  have hdm := Nat.div_add_mod (m * m') 3
  rw [hm'] at hdm
  rw [← hdm, pow_add, pow_mul, hz3, one_pow, one_mul, pow_one]

theorem exists_equivariant_retraction {K Zc : Type*} [Group K] [Finite K] [CommGroup Zc]
    (hZc : Nat.card Zc = 3) (ι : Zc →* K) (hι : Function.Injective ι)
    {Q : Type*} [Group Q] [Finite Q] (hQ : IsPGroup 2 Q) (τ : Q →* MulAut K)
    (hγ : ∀ q : Q, ∃ γ : Zc ≃* Zc, ∀ z, ι (γ z) = τ q (ι z))
    (θ₀ : K →* Zc) (hθ₀ : ∀ z, θ₀ (ι z) = z) :
    ∃ θ : K →* Zc, (∀ z, θ (ι z) = z) ∧ ∀ q : Q, ∀ k, ι (θ (τ q k)) = τ q (ι (θ k)) := by
  classical
  haveI : Finite Zc := Nat.finite_of_card_ne_zero (by rw [hZc]; norm_num)
  haveI : Fintype Q := Fintype.ofFinite _
  have hz3 : ∀ z : Zc, z ^ 3 = 1 := fun z => by
    have := pow_card_eq_one' (G := Zc) (x := z)
    rwa [hZc] at this
  let γ : Q → (Zc ≃* Zc) := fun q => Classical.choose (hγ q)
  have hγs : ∀ (q : Q) z, ι (γ q z) = τ q (ι z) := fun q => Classical.choose_spec (hγ q)
  have hγmul : ∀ α β : Q, ∀ z, γ (α * β) z = γ α (γ β z) := fun α β z => by
    apply hι
    rw [hγs, hγs, hγs, map_mul]
    rfl
  let tw : Q → (K →* Zc) → (K →* Zc) := fun α θ =>
    (γ α).toMonoidHom.comp (θ.comp ((τ α)⁻¹).toMonoidHom)
  have tw_apply : ∀ α θ k, tw α θ k = γ α (θ (((τ α)⁻¹) k)) := fun _ _ _ => rfl
  have tw_mul : ∀ α θ₁ θ₂, tw α (θ₁ * θ₂) = tw α θ₁ * tw α θ₂ := by
    intro α θ₁ θ₂
    ext k
    simp [tw_apply]
  have tw_one : ∀ α, tw α 1 = 1 := by
    intro α
    ext k
    simp [tw_apply]
  have tw_comp : ∀ α β θ, tw α (tw β θ) = tw (α * β) θ := by
    intro α β θ
    ext k
    rw [tw_apply, tw_apply, tw_apply, hγmul]
    simp [mul_inv_rev]
  have tw_ret : ∀ α θ, (∀ z, θ (ι z) = z) → ∀ z, tw α θ (ι z) = z := by
    intro α θ hθ z
    rw [tw_apply]
    have h1 : ι ((γ α).symm z) = (τ α)⁻¹ (ι z) := by
      have := hγs α ((γ α).symm z)
      rw [MulEquiv.apply_symm_apply] at this
      rw [this]
      simp
    rw [← h1, hθ, MulEquiv.apply_symm_apply]
  let twH : Q → (K →* Zc) →* (K →* Zc) := fun α =>
    { toFun := tw α
      map_one' := tw_one α
      map_mul' := tw_mul α }
  let Θ : K →* Zc := ∏ α : Q, tw α θ₀
  have hΘι : ∀ z, Θ (ι z) = z ^ Nat.card Q := by
    intro z
    show (∏ α : Q, tw α θ₀) (ι z) = _
    rw [MonoidHom.finset_prod_apply]
    simp only [tw_ret _ θ₀ hθ₀ z]
    rw [Finset.prod_const, Finset.card_univ, Nat.card_eq_fintype_card]
  have hΘinv : ∀ β : Q, tw β Θ = Θ := by
    intro β
    show twH β (∏ α : Q, tw α θ₀) = ∏ α : Q, tw α θ₀
    rw [map_prod]
    simp only [twH, MonoidHom.coe_mk, OneHom.coe_mk, tw_comp]
    exact Fintype.prod_equiv (Equiv.mulLeft β) _ _ (fun α => rfl)
  obtain ⟨a, ha⟩ := (IsPGroup.iff_card).mp hQ
  obtain ⟨m', hm'⟩ : ∃ m' : ℕ, Nat.card Q * m' % 3 = 1 := by
    have h3 : ¬ 3 ∣ Nat.card Q := by
      intro h
      rw [ha] at h
      have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h
      omega
    have : Nat.card Q % 3 = 1 ∨ Nat.card Q % 3 = 2 := by omega
    rcases this with h | h
    · exact ⟨1, by omega⟩
    · exact ⟨2, by omega⟩
  refine ⟨Θ ^ m', fun z => ?_, fun q k => ?_⟩
  · rw [MonoidHom.pow_apply, hΘι, ← pow_mul]
    have hdm := Nat.div_add_mod (Nat.card Q * m') 3
    rw [hm'] at hdm
    rw [← hdm, pow_add, pow_mul, hz3, one_pow, one_mul, pow_one]
  · have hβ : tw q (Θ ^ m') = Θ ^ m' := by
      have : tw q (Θ ^ m') = (tw q Θ) ^ m' := map_pow (twH q) Θ m'
      rw [this, hΘinv]
    have h1 := congrArg (fun θ : K →* Zc => θ (τ q k)) hβ
    simp only [tw_apply] at h1
    have h2 : ((τ q)⁻¹) (τ q k) = k := by simp
    simp only [h2] at h1
    rw [← h1, hγs]

theorem cube_eq_one_of_real {Λ Γ Zc : Type*} [Group Λ] [Group Γ] [CommGroup Zc]
    (hZc : Nat.card Zc = 3) (ι : Zc →* Λ) (hι : Function.Injective ι)
    (hcent : ∀ z, ι z ∈ Subgroup.center Λ) (φ : Λ →* Γ) (hφs : Function.Surjective φ)
    (hφk : φ.ker = ι.range) (hreal : ∀ y : Γ, y ^ 3 = 1 → ∃ g : Γ, g * y * g⁻¹ = y⁻¹) :
    ∀ x : Λ, x ^ 3 ∈ ι.range → x ^ 3 = 1 := by
  haveI : Finite Zc := Nat.finite_of_card_ne_zero (by rw [hZc]; norm_num)
  have hz3 : ∀ z : Zc, z ^ 3 = 1 := fun z => by
    have := pow_card_eq_one' (G := Zc) (x := z)
    rwa [hZc] at this
  intro x hx
  have hφx : (φ x) ^ 3 = 1 := by
    rw [← map_pow]
    have : x ^ 3 ∈ φ.ker := by rw [hφk]; exact hx
    exact this
  obtain ⟨g, hg⟩ := hreal (φ x) hφx
  obtain ⟨ĝ, rfl⟩ := hφs g
  have hker : ĝ * x * ĝ⁻¹ * x ∈ φ.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_mul, map_mul, map_inv, hg, inv_mul_cancel]
  rw [hφk] at hker
  obtain ⟨z, hz⟩ := hker
  have hconj : ĝ * x * ĝ⁻¹ = ι z * x⁻¹ := by
    rw [hz]
    group
  obtain ⟨w, hw⟩ := hx
  have hc1 : (ĝ * x * ĝ⁻¹) ^ 3 = x ^ 3 := by
    rw [conj_pow, ← hw]
    have := Subgroup.mem_center_iff.mp (hcent w) ĝ
    rw [this]
    group
  have hc2 : (ι z * x⁻¹) ^ 3 = x⁻¹ ^ 3 := by
    have hcomm : Commute (ι z) (x⁻¹) :=
      (Subgroup.mem_center_iff.mp (hcent z) x⁻¹).symm
    rw [hcomm.mul_pow, ← map_pow, hz3 z, map_one, one_mul]
  rw [hconj] at hc1
  rw [hc2] at hc1
  have h6 : ι (w ^ 2) = 1 := by
    have h1 : x⁻¹ ^ 3 = x ^ 3 := hc1
    rw [inv_pow] at h1
    rw [map_pow, hw, pow_two]
    calc x ^ 3 * x ^ 3 = x ^ 3 * (x ^ 3)⁻¹ := by rw [h1]
      _ = 1 := mul_inv_cancel _
  have hw2 : w ^ 2 = 1 := hι (by rw [h6, map_one])
  have hw1 : w = 1 := by
    calc w = w ^ 3 * (w ^ 2)⁻¹ := by group
      _ = 1 := by rw [hz3, hw2]; simp
  rw [← hw, hw1, map_one]

end CFSG.Quasithin.RonanE43
