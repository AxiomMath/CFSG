module

public import Mathlib.GroupTheory.Sylow

public section

namespace CFSG.RankThree.PartTwo.Sec14.Res148

theorem fix_center_of_pow_three {Λ : Type*} [Group Λ] (σ : MulAut Λ) (hσ : σ ^ 3 = 1)
    (hZ : Nat.card (Subgroup.center Λ) = 3) : ∀ z ∈ Subgroup.center Λ, σ z = z := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  intro z hz
  by_cases hz1 : z = 1
  · rw [hz1, map_one]
  have hσz : σ z ∈ Subgroup.center Λ := by
    rw [Subgroup.mem_center_iff]
    intro g
    obtain ⟨g', rfl⟩ := σ.surjective g
    rw [← map_mul, ← map_mul, (Subgroup.mem_center_iff.mp hz g').symm]
  have hz' : (⟨z, hz⟩ : Subgroup.center Λ) ≠ 1 := fun h => hz1 (congrArg Subtype.val h)
  have htop := zpowers_eq_top_of_prime_card hZ hz'
  have hz3 : z ^ 3 = 1 := by
    have h := pow_card_eq_one' (G := Subgroup.center Λ) (x := ⟨z, hz⟩)
    rw [hZ] at h
    exact congrArg Subtype.val h
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp
    (htop ▸ Subgroup.mem_top (⟨σ z, hσz⟩ : Subgroup.center Λ))
  have hk' : σ z = z ^ k := by
    have h := congrArg Subtype.val hk
    simpa using h.symm
  have h3 : z ^ (3 : ℤ) = 1 := by exact_mod_cast hz3
  have hmod : z ^ k = z ^ (k % 3) := by
    conv_lhs => rw [← Int.emod_add_mul_ediv k 3]
    rw [zpow_add, zpow_mul, h3, one_zpow, mul_one]
  have hσσσ : (σ ^ 3) z = σ (σ (σ z)) := by
    rw [pow_succ, pow_succ, pow_one]
    rfl
  rcases (by omega : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2) with h0 | h1 | h2
  · exfalso
    rw [hmod, h0, zpow_zero] at hk'
    exact hz1 (σ.injective (hk'.trans (map_one σ).symm))
  · rw [hk', hmod, h1, zpow_one]
  · exfalso
    rw [hmod, h2] at hk'
    have hk2 : σ z = z ^ 2 := by rw [hk']; norm_cast
    have h4 : σ (σ z) = z := by
      rw [hk2, map_pow, hk2, ← pow_mul]
      calc z ^ (2 * 2) = z ^ 3 * z := by rw [← pow_succ]
        _ = z := by rw [hz3, one_mul]
    have h5 : (σ ^ 3) z = z ^ 2 := by rw [hσσσ, h4, hk2]
    rw [hσ, MulAut.one_apply] at h5
    have : z = 1 := by
      have h6 : z * z = z * 1 := by rw [mul_one, ← sq, ← h5]
      exact mul_left_cancel h6
    exact hz1 this

theorem card_le_orderOf_of_conj_mem_zpowers {Γ : Type*} [Group Γ] [Finite Γ] {x : Γ}
    {R : Subgroup Γ} (hR : ∀ r ∈ R, r * x * r⁻¹ ∈ Subgroup.zpowers x)
    (hcop : Nat.Coprime (Nat.card R) (Nat.card (Subgroup.centralizer ({x} : Set Γ)))) :
    Nat.card R ≤ orderOf x := by
  have hbot : R ⊓ Subgroup.centralizer ({x} : Set Γ) = ⊥ :=
    disjoint_iff.mp (Subgroup.disjoint_of_coprime_natCard hcop)
  have hinj : Function.Injective
      (fun r : R => (⟨r * x * (r : Γ)⁻¹, hR r r.2⟩ : Subgroup.zpowers x)) := by
    intro r s h
    have h' : (r : Γ) * x * (r : Γ)⁻¹ = s * x * (s : Γ)⁻¹ := congrArg Subtype.val h
    have hc : (s : Γ)⁻¹ * r ∈ R ⊓ Subgroup.centralizer ({x} : Set Γ) := by
      refine Subgroup.mem_inf.mpr ⟨R.mul_mem (R.inv_mem s.2) r.2, ?_⟩
      rw [Subgroup.mem_centralizer_singleton_iff]
      calc (s : Γ)⁻¹ * r * x = (s : Γ)⁻¹ * (r * x * (r : Γ)⁻¹) * r := by group
        _ = (s : Γ)⁻¹ * (s * x * (s : Γ)⁻¹) * r := by rw [h']
        _ = x * ((s : Γ)⁻¹ * r) := by group
    rw [hbot, Subgroup.mem_bot, inv_mul_eq_one] at hc
    exact Subtype.ext hc.symm
  calc Nat.card R ≤ Nat.card (Subgroup.zpowers x) := Nat.card_le_card_of_injective _ hinj
    _ = orderOf x := Nat.card_zpowers x

theorem exists_mem_normalizer_map_eq {H L : Type*} [Group H] [Group L] [Finite H] {p : ℕ}
    [Fact p.Prime] (f : H →* L) (Q : Sylow p H) {t : L}
    (ht : t ∈ Subgroup.normalizer (((Q : Subgroup H).map f : Subgroup L) : Set L))
    (htr : t ∈ f.range) :
    ∃ n ∈ Subgroup.normalizer ((Q : Subgroup H) : Set H), f n = t := by
  obtain ⟨h, rfl⟩ := htr
  set M : Subgroup H := ((Q : Subgroup H).map f).comap f with hM
  have hQM : (Q : Subgroup H) ≤ M := Subgroup.le_comap_map f Q
  have hhQM : ((h • Q : Sylow p H) : Subgroup H) ≤ M := by
    intro x hx
    rw [Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem, MulAut.smul_def,
      MulAut.conj_inv_apply] at hx
    show f x ∈ (Q : Subgroup H).map f
    have he : f x = f h * f (h⁻¹ * x * h) * (f h)⁻¹ := by
      simp only [map_mul, map_inv]
      group
    rw [he]
    exact (Subgroup.mem_normalizer_iff.mp ht _).mp ⟨_, hx, rfl⟩
  obtain ⟨m, hm⟩ := MulAction.exists_smul_eq M (Q.subtype hQM) ((h • Q).subtype hhQM)
  rw [Sylow.smul_subtype] at hm
  have hm' : (m : H) • Q = h • Q := Sylow.subtype_injective hm
  have hn : (m : H)⁻¹ * h ∈ Subgroup.normalizer ((Q : Subgroup H) : Set H) := by
    have he : ((m : H)⁻¹ * h) • Q = Q := by rw [mul_smul, ← hm', inv_smul_smul]
    exact Sylow.smul_eq_iff_mem_normalizer.mp he
  obtain ⟨q, hq, hqm⟩ := m.2
  refine ⟨q * ((m : H)⁻¹ * h), Subgroup.mul_mem _ (Subgroup.le_normalizer hq) hn, ?_⟩
  rw [map_mul, map_mul, map_inv, hqm, mul_inv_cancel_left]

theorem three_dvd_card_normalizer_of_surjective {H L : Type*} [Group H] [Group L] [Finite H]
    [Finite L] {p : ℕ} [Fact p.Prime] (f : H →* L) (hf : Function.Surjective f) (Q : Sylow p H)
    (hL : 3 ∣ Nat.card (Subgroup.normalizer (((Q : Subgroup H).map f : Subgroup L) : Set L))) :
    3 ∣ Nat.card (Subgroup.normalizer ((Q : Subgroup H) : Set H)) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨⟨t, ht⟩, htord⟩ := exists_prime_orderOf_dvd_card' 3 hL
  rw [Subgroup.orderOf_mk] at htord
  obtain ⟨n, hn, rfl⟩ := exists_mem_normalizer_map_eq f Q ht (hf t)
  have h1 : 3 ∣ orderOf n := htord ▸ orderOf_map_dvd f n
  have h2 : orderOf n ∣ Nat.card (Subgroup.normalizer ((Q : Subgroup H) : Set H)) := by
    rw [← Subgroup.orderOf_mk n hn]
    exact orderOf_dvd_natCard _
  exact h1.trans h2

theorem card_subgroupOf_comm {Γ : Type*} [Group Γ] (H K : Subgroup Γ) :
    Nat.card (H.subgroupOf K) = Nat.card (K.subgroupOf H) :=
  Nat.card_congr
    { toFun := fun x => ⟨⟨x.1.1, x.2⟩, x.1.2⟩
      invFun := fun y => ⟨⟨y.1.1, y.2⟩, y.1.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

theorem nine_dvd_card_normalizer_of_normal {Γ : Type*} [Group Γ] [Finite Γ] {p : ℕ}
    [Fact p.Prime] {H : Subgroup Γ} [H.Normal] (Q : Sylow p H) {g : Γ} (hgH : g ∉ H)
    (hg3 : g ^ 3 = 1) (h3 : 3 ∣ Nat.card (Subgroup.normalizer ((Q : Subgroup H) : Set H))) :
    9 ∣ Nat.card
      (Subgroup.normalizer (((Q : Subgroup H).map H.subtype : Subgroup Γ) : Set Γ)) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set K := Subgroup.normalizer (((Q : Subgroup H).map H.subtype : Subgroup Γ) : Set Γ) with hK
  have hF : K ⊔ H = ⊤ := Sylow.normalizer_sup_eq_top Q
  have hidx : H.index = H.relIndex K := by
    rw [← Subgroup.relIndex_top_right, ← hF, Subgroup.relIndex_sup_right]
  have h3i : 3 ∣ H.index := by
    have hord : orderOf (QuotientGroup.mk g : Γ ⧸ H) = 3 := by
      apply orderOf_eq_prime
      · rw [← QuotientGroup.mk_pow, hg3, QuotientGroup.mk_one]
      · rwa [Ne, QuotientGroup.eq_one_iff]
    rw [Subgroup.index, ← hord]
    exact orderOf_dvd_natCard _
  have hKc : Nat.card (H.subgroupOf K) * H.relIndex K = Nat.card K :=
    (H.subgroupOf K).card_mul_index
  have hNH : Nat.card (H.subgroupOf K) =
      Nat.card (Subgroup.normalizer ((Q : Subgroup H) : Set H)) := by
    rw [card_subgroupOf_comm]
    have hc : K.subgroupOf H = Subgroup.normalizer ((Q : Subgroup H) : Set H) := by
      rw [Subgroup.subgroupOf, hK, Subgroup.comap_normalizer_eq_of_le_range (by
        rw [Subgroup.range_subtype]; exact Subgroup.map_subtype_le _),
        Subgroup.comap_map_eq_self_of_injective H.subtype_injective]
    rw [hc]
  rw [← hKc, ← hidx, hNH, show (9 : ℕ) = 3 * 3 from rfl]
  exact Nat.mul_dvd_mul h3 h3i

end CFSG.RankThree.PartTwo.Sec14.Res148
