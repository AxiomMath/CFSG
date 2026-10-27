module

public import CFSG.Walter.J1.Sylow

public section

namespace CFSG.Walter.J1Props

open scoped Pointwise

open scoped IsMulCommutative in
theorem eq_one_of_mem_sylow_of_commute_normalizer {G : Type*} [Group G] [Finite G] {p : ℕ}
    [Fact p.Prime] (hG : ∀ H : Subgroup G, H.Normal → H.index ≠ p) (S : Sylow p G)
    [IsMulCommutative (S : Subgroup G)] {z : G} (hzS : z ∈ S)
    (hz : ∀ n ∈ Subgroup.normalizer ((S : Subgroup G) : Set G), n * z = z * n) : z = 1 := by
  classical
  let φ : G →* S := MonoidHom.transfer (MonoidHom.id S)
  have key : ∀ (k : ℕ) (g₀ : G), g₀⁻¹ * z ^ k * g₀ ∈ (S : Subgroup G) →
      g₀⁻¹ * z ^ k * g₀ = z ^ k := by
    intro k g₀ hk
    obtain ⟨n, hn, heq⟩ := Sylow.conj_eq_normalizer_conj_of_mem S (z ^ k) g₀
      (S.toSubgroup.pow_mem hzS k) hk
    rw [heq]
    have hc : Commute n (z ^ k) := Commute.pow_right (hz n hn) k
    rw [mul_assoc, ← hc.eq, ← mul_assoc, inv_mul_cancel, one_mul]
  have hφz : φ z = ⟨z ^ (S : Subgroup G).index, _⟩ :=
    MonoidHom.transfer_eq_pow (MonoidHom.id S) z key
  have hrange : φ.range = ⊥ := by
    by_contra hne
    have hR : IsPGroup p φ.range := S.isPGroup'.to_subgroup φ.range
    obtain ⟨n, hn⟩ := hR.exists_card_eq
    have hn0 : n ≠ 0 := by
      rintro rfl
      rw [pow_zero] at hn
      exact hne (Subgroup.card_eq_one.mp hn)
    obtain ⟨K, hK⟩ := Sylow.exists_subgroup_card_pow_prime (G := φ.range) p (n := n - 1)
      (by rw [hn]; exact pow_dvd_pow p (Nat.sub_le n 1))
    have hKidx : K.index = p := by
      have h := K.card_mul_index
      rw [hK, hn] at h
      have hpos : 0 < p ^ (n - 1) := pow_pos (Fact.out : p.Prime).pos _
      have : p ^ (n - 1) * K.index = p ^ (n - 1) * p := by
        rw [h, ← pow_succ, Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hn0)]
      exact Nat.eq_of_mul_eq_mul_left hpos this
    have hKn : K.Normal := Subgroup.normal_of_isMulCommutative K
    exact hG (K.comap φ.rangeRestrict) (hKn.comap _)
      (by rw [Subgroup.index_comap_of_surjective _ φ.rangeRestrict_surjective, hKidx])
  have h1 : z ^ (S : Subgroup G).index = 1 := by
    have hmem : φ z ∈ φ.range := ⟨z, rfl⟩
    rw [hrange, Subgroup.mem_bot, hφz] at hmem
    exact congrArg Subtype.val hmem
  have h2 : orderOf z ∣ Nat.card (S : Subgroup G) := Subgroup.orderOf_dvd_natCard _ hzS
  exact orderOf_eq_one_iff.mp (Nat.Coprime.eq_one_of_dvd
    (Nat.Coprime.coprime_dvd_left h2 S.card_coprime_index) (orderOf_dvd_of_pow_eq_one h1))

theorem sylow_two_card_eight_transitive {G : Type*} [Group G] [Finite G]
    (hG : ∀ H : Subgroup G, H.Normal → H.index ≠ 2) (S : Sylow 2 G)
    (hS : IsMulCommutative (S : Subgroup G)) (hcard : Nat.card (S : Subgroup G) = 8) :
    ∀ x ∈ (S : Subgroup G), x ≠ 1 → ∀ y ∈ (S : Subgroup G), y ≠ 1 →
      ∃ n ∈ Subgroup.normalizer ((S : Subgroup G) : Set G), n * x * n⁻¹ = y := by
  classical
  set Sg := (S : Subgroup G) with hSg
  set N := Subgroup.normalizer (Sg : Set G) with hN
  set φ : N →* MulAut Sg := Sg.normalizerMonoidHom with hφ
  set A : Subgroup (MulAut Sg) := φ.range with hA
  have hcommS : ∀ a b : Sg, a * b = b * a := fun a b => hS.is_comm.comm a b
  have hAodd : Odd (Nat.card A) := by
    have hSN : Sg ≤ N := Subgroup.le_normalizer
    have hker : Sg.subgroupOf N ≤ φ.ker := by
      rw [hφ, Subgroup.normalizerMonoidHom_ker]
      intro x hx
      rw [Subgroup.mem_subgroupOf] at hx ⊢
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      exact congrArg Subtype.val (hcommS ⟨y, hy⟩ ⟨x, hx⟩)
    have h1 : φ.ker.index = Nat.card A := Subgroup.index_ker φ
    have h2 : φ.ker.index ∣ (Sg.subgroupOf N).index := Subgroup.index_dvd_of_le hker
    have h3 : (Sg.subgroupOf N).index ∣ Sg.index := Subgroup.relIndex_dvd_index_of_le hSN
    rw [← Nat.not_even_iff_odd, even_iff_two_dvd]
    intro h
    rw [← h1] at h
    exact S.not_dvd_index (h.trans (h2.trans h3))
  have hfix : ∀ x : Sg, (∀ a : A, a • x = x) → x = 1 := by
    intro x hx
    apply Subtype.ext
    have : IsMulCommutative (S : Subgroup G) := hS
    refine eq_one_of_mem_sylow_of_commute_normalizer hG S x.2 ?_
    intro n hn
    have h := congrArg Subtype.val (hx ⟨φ ⟨n, hn⟩, ⟨n, hn⟩, rfl⟩)
    change (n : G) * x * n⁻¹ = x at h
    calc n * (x : G) = (n * x * n⁻¹) * n := by group
      _ = x * n := by rw [h]
  set T : Set Sg := {x | x ≠ 1} with hT
  have hTcard : T.ncard = 7 := by
    have : T = (Set.univ : Set Sg) \ {1} := by ext; simp [hT]
    rw [this, Set.ncard_sdiff_singleton_of_mem (Set.mem_univ _), Set.ncard_univ, hcard]
  have hTinv : ∀ a : A, ∀ x ∈ T, a • x ∈ T := by
    intro a x hx h
    apply hx
    have h' : (a : MulAut Sg) x = (a : MulAut Sg) 1 := by rw [map_one]; exact h
    exact (a : MulAut Sg).injective h'
  have horbit : ∀ x ∈ T, MulAction.orbit A x = T := by
    apply J1.orbit_eq_of_ncard_eq_seven T hTcard hTinv
    intro x hx
    have hdvd : (MulAction.orbit A x).ncard ∣ Nat.card A := by
      rw [← MulAction.index_stabilizer]
      exact Subgroup.index_dvd_card _
    refine ⟨Odd.of_dvd_nat hAodd hdvd, fun h1 => hx (hfix x ?_)⟩
    intro a
    obtain ⟨y, hy⟩ := Set.ncard_eq_one.mp h1
    have hxo : x ∈ MulAction.orbit A x := MulAction.mem_orbit_self x
    have hao : a • x ∈ MulAction.orbit A x := MulAction.mem_orbit x a
    rw [hy] at hxo hao
    rw [Set.mem_singleton_iff] at hxo hao
    rw [hao, hxo]
  intro x hx hx1 y hy hy1
  have hxT : (⟨x, hx⟩ : Sg) ∈ T := fun h => hx1 (congrArg Subtype.val h)
  have hyT : (⟨y, hy⟩ : Sg) ∈ T := fun h => hy1 (congrArg Subtype.val h)
  rw [← horbit _ hxT] at hyT
  obtain ⟨⟨a, n, rfl⟩, ha⟩ := hyT
  exact ⟨n, n.2, congrArg Subtype.val ha⟩

theorem exists_conj_of_orderOf_eq_two {G : Type*} [Group G] [Finite G]
    (hG : ∀ H : Subgroup G, H.Normal → H.index ≠ 2) (hab : HasAbelianSylowTwo G)
    (h8 : ∀ S : Sylow 2 G, Nat.card (S : Subgroup G) = 8) {x y : G} (hx : orderOf x = 2)
    (hy : orderOf y = 2) : ∃ g : G, g * x * g⁻¹ = y := by
  have hpg : ∀ z : G, orderOf z = 2 → IsPGroup 2 (Subgroup.zpowers z) := fun z hz =>
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hz, pow_one])
  obtain ⟨S, hyS⟩ := (hpg y hy).exists_le_sylow
  obtain ⟨S', hxS'⟩ := (hpg x hx).exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G S' S
  have hgx : g * x * g⁻¹ ∈ (S : Subgroup G) := by
    rw [← hg]
    change g * x * g⁻¹ ∈ MulAut.conj g • (S' : Subgroup G)
    have := Subgroup.smul_mem_pointwise_smul x (MulAut.conj g) (S' : Subgroup G)
      (hxS' (Subgroup.mem_zpowers x))
    simpa [MulAut.smul_def, MulAut.conj_apply] using this
  have hne : ∀ z : G, orderOf z = 2 → z ≠ 1 := fun z hz h1 => by
    rw [h1, orderOf_one] at hz
    omega
  have hgx1 : g * x * g⁻¹ ≠ 1 := by
    intro h1
    apply hne x hx
    have := congrArg (fun w => g⁻¹ * w * g) h1
    simpa [mul_assoc] using this
  obtain ⟨n, -, hn⟩ := sylow_two_card_eight_transitive hG S (hab S) (h8 S) _ hgx hgx1 y
    (hyS (Subgroup.mem_zpowers y)) (hne y hy)
  exact ⟨n * g, by rw [← hn]; group⟩

theorem eq_bot_of_four_group {G : Type*} [Group G] [Finite G] {K : Subgroup G} [hK : K.Normal]
    {v₁ v₂ : G} (h₁ : v₁ * v₁ = 1) (h₂ : v₂ * v₂ = 1)
    (hf₁ : K ⊓ Subgroup.centralizer ({v₁} : Set G) = ⊥)
    (hf₂ : K ⊓ Subgroup.centralizer ({v₂} : Set G) = ⊥)
    (hf₃ : K ⊓ Subgroup.centralizer ({v₁ * v₂} : Set G) = ⊥) : K = ⊥ := by
  have hN : ∀ v : G, v ∈ Subgroup.normalizer (K : Set G) := fun v => by
    rw [Subgroup.normalizer_eq_top]
    exact Subgroup.mem_top v
  have i₁ := J1.inv_of_inf_centralizer_eq_bot h₁ (hN v₁) hf₁
  have i₂ := J1.inv_of_inf_centralizer_eq_bot h₂ (hN v₂) hf₂
  rw [eq_bot_iff]
  intro k hk
  rw [← hf₃]
  refine ⟨hk, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
  have e₂ := i₂ k hk
  have e₁ := i₁ k⁻¹ (K.inv_mem hk)
  rw [inv_inv] at e₁
  symm
  calc v₁ * v₂ * k = v₁ * (v₂ * k * v₂⁻¹) * v₁⁻¹ * (v₁ * v₂) := by group
    _ = v₁ * k⁻¹ * v₁⁻¹ * (v₁ * v₂) := by rw [e₂]
    _ = k * (v₁ * v₂) := by rw [e₁]

end CFSG.Walter.J1Props
