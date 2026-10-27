module

public import CFSG.Quasithin.Background.RonanE43Split

public section

namespace CFSG.Quasithin.RonanE43

variable {G : Type*} [Group G]

@[expose] def conjOn (K : Subgroup G) (g : G) (hg : g ∈ Subgroup.normalizer (K : Set G)) :
    MulAut ↥K where
  toFun k := ⟨g * k * g⁻¹, (Subgroup.mem_normalizer_iff.mp hg k).mp k.2⟩
  invFun k := ⟨g⁻¹ * k * g, by
    have := (Subgroup.mem_normalizer_iff.mp ((Subgroup.normalizer (K : Set G)).inv_mem hg) k).mp k.2
    simpa using this⟩
  left_inv k := by
    apply Subtype.ext
    simp [mul_assoc]
  right_inv k := by
    apply Subtype.ext
    simp [mul_assoc]
  map_mul' a b := by
    apply Subtype.ext
    simp [mul_assoc]

theorem conjOn_apply (K : Subgroup G) (g : G) (hg : g ∈ Subgroup.normalizer (K : Set G)) (k : ↥K) :
    ((conjOn K g hg k : ↥K) : G) = g * k * g⁻¹ := rfl

@[expose] def conjHom (K T : Subgroup G) (hT : T ≤ Subgroup.normalizer (K : Set G)) :
    ↥T →* MulAut ↥K where
  toFun t := conjOn K t (hT t.2)
  map_one' := by
    apply MulEquiv.ext
    intro k
    apply Subtype.ext
    simp [conjOn_apply]
  map_mul' a b := by
    apply MulEquiv.ext
    intro k
    apply Subtype.ext
    simp [conjOn_apply, mul_assoc]

variable [Finite G]

theorem exists_invariant_complement {K Z T : Subgroup G} (hZK : Z ≤ K) (hZ3 : Nat.card Z = 3)
    (hZc : ∀ z ∈ Z, ∀ k ∈ K, z * k = k * z) (hZT : T ≤ Subgroup.normalizer (Z : Set G))
    (hTK : T ≤ Subgroup.normalizer (K : Set G)) (hT2 : IsPGroup 2 T) {m : ℕ}
    (hK : Nat.card K = 9 * m) (hm : ¬ 3 ∣ m) (h9 : ∀ x ∈ K, x ^ 3 ∈ Z → x ^ 3 = 1) :
    ∃ C : Subgroup G, C ≤ K ∧ C ⊓ Z = ⊥ ∧ C ⊔ Z = K ∧ T ≤ Subgroup.normalizer (C : Set G) ∧
      ∀ x ∈ K, ∀ n : ℕ, x ^ 2 ^ n = 1 → x ∈ C := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : IsCyclic ↥Z := isCyclic_of_prime_card (p := 3) hZ3
  letI : CommGroup ↥Z := IsCyclic.commGroup
  let ι : ↥Z →* ↥K := Subgroup.inclusion hZK
  have hι : Function.Injective ι := Subgroup.inclusion_injective hZK
  have hιval : ∀ z : ↥Z, ((ι z : ↥K) : G) = (z : G) := fun z => rfl
  have hcent : ∀ z, ι z ∈ Subgroup.center ↥K := fun z => by
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (hZc z z.2 g g.2).symm
  have h9' : ∀ x : ↥K, x ^ 3 ∈ ι.range → x ^ 3 = 1 := by
    intro x hx
    obtain ⟨z, hz⟩ := hx
    apply Subtype.ext
    have hzx : (z : G) = (x : G) ^ 3 := by
      have h1 : ((ι z : ↥K) : G) = ((x ^ 3 : ↥K) : G) := congrArg Subtype.val hz
      rw [Subgroup.coe_pow] at h1
      exact h1
    have := h9 x x.2 (by rw [← hzx]; exact z.2)
    simpa using this
  obtain ⟨θ₀, hθ₀⟩ := exists_retraction_of_central_three hZ3 ι hι hcent hK hm h9'
  let τ : ↥T →* MulAut ↥K := conjHom K T hTK
  have hγ : ∀ t : ↥T, ∃ γ : ↥Z ≃* ↥Z, ∀ z, ι (γ z) = τ t (ι z) := fun t =>
    ⟨conjOn Z t (hZT t.2), fun z => Subtype.ext rfl⟩
  obtain ⟨θ, hθ, hθτ⟩ := exists_equivariant_retraction hZ3 ι hι hT2 τ hγ θ₀ hθ₀
  have hz3 : ∀ z : ↥Z, z ^ 3 = 1 := fun z => by
    have := pow_card_eq_one' (G := ↥Z) (x := z)
    rwa [hZ3] at this
  have hker : ∀ k : ↥K, k ∈ θ.ker → θ k = 1 := fun k hk => MonoidHom.mem_ker.mp hk
  have hker_inv : ∀ t : ↥T, ∀ k : ↥K, θ k = 1 → θ (τ t k) = 1 := by
    intro t k hk
    apply hι
    rw [hθτ, hk, map_one, map_one]
  refine ⟨θ.ker.map K.subtype, Subgroup.map_subtype_le _, ?_, ?_, ?_, ?_⟩
  ·
    rw [Subgroup.eq_bot_iff_forall]
    rintro x ⟨hxC, hxZ⟩
    obtain ⟨k, hk, rfl⟩ := Subgroup.mem_map.mp hxC
    obtain ⟨z₀, hz₀⟩ : ∃ z₀ : ↥Z, ι z₀ = k := ⟨⟨(K.subtype k), hxZ⟩, Subtype.ext rfl⟩
    have h2 := hker k hk
    rw [← hz₀, hθ] at h2
    rw [← hz₀, h2]
    simp
  ·
    apply le_antisymm
    · exact sup_le (Subgroup.map_subtype_le _) hZK
    · intro x hx
      set k : ↥K := ⟨x, hx⟩ with hkdef
      set z : ↥Z := θ k with hzdef
      have hc : k * (ι z)⁻¹ ∈ θ.ker := by
        rw [MonoidHom.mem_ker, map_mul, map_inv, hθ, hzdef]
        exact mul_inv_cancel _
      have hxc : x = ((k * (ι z)⁻¹ : ↥K) : G) * (z : G) := by
        simp [hkdef, hιval]
      rw [hxc]
      exact Subgroup.mul_mem_sup (Subgroup.mem_map_of_mem _ hc) z.2
  ·
    have key : ∀ t ∈ T, ∀ c ∈ θ.ker.map K.subtype, t * c * t⁻¹ ∈ θ.ker.map K.subtype := by
      intro t ht c hc
      obtain ⟨k, hk, rfl⟩ := Subgroup.mem_map.mp hc
      refine Subgroup.mem_map.mpr ⟨τ ⟨t, ht⟩ k, ?_, ?_⟩
      · exact hker_inv ⟨t, ht⟩ k (hker k hk)
      · rfl
    intro t ht
    rw [Subgroup.mem_normalizer_iff]
    intro c
    refine ⟨key t ht c, fun hc => ?_⟩
    have := key t⁻¹ (T.inv_mem ht) _ hc
    simpa [mul_assoc] using this
  ·
    intro x hx n hxn
    have hθx : (θ ⟨x, hx⟩) ^ 2 ^ n = 1 := by
      rw [← map_pow]
      have : (⟨x, hx⟩ : ↥K) ^ 2 ^ n = 1 := Subtype.ext (by simpa using hxn)
      rw [this, map_one]
    set z : ↥Z := θ ⟨x, hx⟩ with hzdef
    have h3 : orderOf z ∣ 3 := orderOf_dvd_of_pow_eq_one (hz3 z)
    have h2 : orderOf z ∣ 2 ^ n := orderOf_dvd_of_pow_eq_one hθx
    have hcop : Nat.Coprime 3 (2 ^ n) := Nat.Coprime.pow_right n (by norm_num)
    have h1 : orderOf z ∣ 1 := by
      have := Nat.dvd_gcd h3 h2
      rwa [hcop] at this
    have hz1 : z = 1 := orderOf_eq_one_iff.mp (Nat.dvd_one.mp h1)
    exact Subgroup.mem_map.mpr ⟨⟨x, hx⟩, MonoidHom.mem_ker.mpr hz1, rfl⟩

end CFSG.Quasithin.RonanE43
