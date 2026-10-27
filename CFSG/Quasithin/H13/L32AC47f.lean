module

public import CFSG.Quasithin.H13.L32AC47e

public section

namespace CFSG.Quasithin.H13.L32A.C.Alt6

open scoped Pointwise

variable {G : Type*} [Group G]

@[expose] def conjK {K : Subgroup G} {t : G} (ht : t ∈ Subgroup.normalizer (K : Set G)) :
    ↥K →* ↥K where
  toFun k := ⟨t * k * t⁻¹, (Subgroup.mem_normalizer_iff.mp ht k).mp k.2⟩
  map_one' := Subtype.ext (by simp)
  map_mul' a b := Subtype.ext (by simp only [Subgroup.coe_mul]; group)

theorem conjK_apply {K : Subgroup G} {t : G} (ht : t ∈ Subgroup.normalizer (K : Set G)) (k : ↥K) :
    ((conjK ht k : ↥K) : G) = t * k * t⁻¹ := rfl

@[expose] def parab {K : Subgroup G} (π : ↥K →* A6) (N : Subgroup A6) : Subgroup G :=
  (N.comap π).map K.subtype

theorem mem_parab {K : Subgroup G} {π : ↥K →* A6} {N : Subgroup A6} {g : G} :
    g ∈ parab π N ↔ ∃ hg : g ∈ K, π ⟨g, hg⟩ ∈ N := by
  constructor
  · rintro ⟨k, hk, rfl⟩
    exact ⟨k.2, hk⟩
  · rintro ⟨hg, h⟩
    exact ⟨⟨g, hg⟩, h, rfl⟩

theorem orderOf_xA : orderOf xA = 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  rw [orderOf_eq_prime_iff]
  exact ⟨Subtype.ext x0_y0_facts.2.1, fun h => x0_y0_facts.2.2.1 (congrArg Subtype.val h)⟩

theorem orderOf_yA : orderOf yA = 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  rw [orderOf_eq_prime_iff]
  exact ⟨Subtype.ext x0_y0_facts.2.2.2.2.2.2.1,
    fun h => x0_y0_facts.2.2.2.2.2.2.2.1 (congrArg Subtype.val h)⟩

theorem exists_conj_map_eq_D0 {K : Type*} [Group K] [Finite K] (π₀ : K →* A6)
    (hπ₀ : Function.Surjective π₀) {S : Subgroup K} (hS2 : IsPGroup 2 S)
    (hSi : ¬ 2 ∣ S.index) :
    ∃ h : A6, (S.map π₀).map (MulAut.conj h⁻¹).toMonoidHom = D0 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h1 : IsPGroup 2 (S.map π₀) := hS2.map π₀
  have h2 : ¬ 2 ∣ (S.map π₀).index := fun h => hSi (h.trans (Subgroup.index_map_dvd S hπ₀))
  have h3 : IsPGroup 2 D0 := IsPGroup.of_card (n := 3) (by rw [card_D0]; rfl)
  have h4 : ¬ 2 ∣ D0.index := by
    have := D0.card_mul_index
    rw [card_D0, card_A6] at this
    rintro ⟨m, hm⟩
    omega
  obtain ⟨h, hh⟩ := MulAction.exists_smul_eq A6 (h3.toSylow h4) (h1.toSylow h2)
  have key : ∀ x : A6, x ∈ S.map π₀ ↔ h⁻¹ * x * h ∈ D0 := by
    intro x
    change x ∈ ((h1.toSylow h2 : Sylow 2 A6) : Subgroup A6) ↔ _
    rw [← hh]
    simp only [Sylow.smul_def]
    change x ∈ (MulAut.conj h • ((h3.toSylow h4 : Sylow 2 A6) : Subgroup A6)) ↔ _
    rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
    simp [MulAut.smul_def]
  refine ⟨h, ?_⟩
  ext x
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    have := (key y).mp hy
    simpa [MulAut.conj_apply] using this
  · intro hx
    refine ⟨h * x * h⁻¹, (key _).mpr (by simpa [mul_assoc] using hx), ?_⟩
    simp [mul_assoc]

section Lift

variable {K Z : Subgroup G} (π : ↥K →* A6)

noncomputable def inducedEndo (hπ : Function.Surjective π) {t : G}
    (ht : t ∈ Subgroup.normalizer (K : Set G))
    (hZ : ∀ k : ↥K, π k = 1 → π (conjK ht k) = 1) : A6 →* A6 :=
  π.liftOfRightInverse (Function.surjInv hπ) (Function.rightInverse_surjInv hπ)
    ⟨π.comp (conjK ht), fun k hk => hZ k hk⟩

theorem inducedEndo_apply (hπ : Function.Surjective π) {t : G}
    (ht : t ∈ Subgroup.normalizer (K : Set G))
    (hZ : ∀ k : ↥K, π k = 1 → π (conjK ht k) = 1) (k : ↥K) :
    inducedEndo π hπ ht hZ (π k) = π (conjK ht k) :=
  MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ k

theorem exists_parabolics (hπ : Function.Surjective π) {T : Subgroup G} (hZK : Z ≤ K)
    (hker : ∀ k : ↥K, π k = 1 ↔ (k : G) ∈ Z)
    (hTK : T ≤ Subgroup.normalizer (K : Set G)) (hTZ : T ≤ Subgroup.normalizer (Z : Set G))
    (hD : (T.subgroupOf K).map π = D0)
    (hfus : ∀ t (ht : t ∈ T) (x : ↥K), orderOf (π x) = 3 →
      ∃ k : ↥K, π (conjK (hTK ht) x) = π (k * x * k⁻¹)) :
    T ≤ Subgroup.normalizer (parab π N1 : Set G) ∧ T ≤ Subgroup.normalizer (parab π N2 : Set G) ∧
      Z ≤ parab π N1 ∧ Z ≤ parab π N2 ∧ K ≤ parab π N1 ⊔ parab π N2 := by
  have hZ : ∀ t (ht : t ∈ T) (k : ↥K), π k = 1 → π (conjK (hTK ht) k) = 1 := by
    intro t ht k hk
    rw [hker] at hk ⊢
    rw [conjK_apply]
    exact (Subgroup.mem_normalizer_iff.mp (hTZ ht) k).mp hk
  have key : ∀ t (ht : t ∈ T), (∀ n ∈ N1, inducedEndo π hπ (hTK ht) (hZ t ht) n ∈ N1) ∧
      ∀ n ∈ N2, inducedEndo π hπ (hTK ht) (hZ t ht) n ∈ N2 := by
    intro t ht
    set β := inducedEndo π hπ (hTK ht) (hZ t ht) with hβ
    have hβa : ∀ k : ↥K, β (π k) = π (conjK (hTK ht) k) := inducedEndo_apply π hπ _ _
    have hinj : Function.Injective β := by
      rw [← MonoidHom.ker_eq_bot_iff, Subgroup.eq_bot_iff_forall]
      intro a ha
      obtain ⟨k, rfl⟩ := hπ a
      rw [MonoidHom.mem_ker, hβa, hker, conjK_apply] at ha
      rw [hker]
      have := (Subgroup.mem_normalizer_iff.mp (hTZ (T.inv_mem ht)) _).mp ha
      simpa [mul_assoc] using this
    have hDD : ∀ d ∈ D0, β d ∈ D0 := by
      intro d hd
      rw [← hD] at hd ⊢
      obtain ⟨s, hs, rfl⟩ := hd
      refine ⟨conjK (hTK ht) s, ?_, (hβa s).symm⟩
      rw [SetLike.mem_coe, Subgroup.mem_subgroupOf] at hs
      rw [SetLike.mem_coe, Subgroup.mem_subgroupOf, conjK_apply]
      exact T.mul_mem (T.mul_mem ht hs) (T.inv_mem ht)
    have hconj : ∀ a : A6, orderOf a = 3 → ∃ g : A6, β a = g * a * g⁻¹ := by
      intro a ha
      obtain ⟨x, rfl⟩ := hπ a
      obtain ⟨k, hk⟩ := hfus t ht x ha
      exact ⟨π k, by rw [hβa, hk, map_mul, map_mul, map_inv]⟩
    exact map_N_of_endo β hinj hDD (hconj _ orderOf_xA) (hconj _ orderOf_yA)
  have hnorm : ∀ N : Subgroup A6, (∀ t (ht : t ∈ T),
      ∀ n ∈ N, inducedEndo π hπ (hTK ht) (hZ t ht) n ∈ N) →
      T ≤ Subgroup.normalizer (parab π N : Set G) := by
    intro N hN
    have one_dir : ∀ t ∈ T, ∀ g ∈ parab π N, t * g * t⁻¹ ∈ parab π N := by
      intro t ht g hg
      obtain ⟨hgK, hgN⟩ := mem_parab.mp hg
      refine mem_parab.mpr ⟨(Subgroup.mem_normalizer_iff.mp (hTK ht) g).mp hgK, ?_⟩
      have := hN t ht _ hgN
      rwa [inducedEndo_apply] at this
    intro t ht
    rw [Subgroup.mem_normalizer_iff]
    intro g
    refine ⟨one_dir t ht g, fun hg => ?_⟩
    have := one_dir t⁻¹ (T.inv_mem ht) _ hg
    simpa [mul_assoc] using this
  have hZB : ∀ N : Subgroup A6, Z ≤ parab π N := by
    intro N z hz
    refine mem_parab.mpr ⟨hZK hz, ?_⟩
    rw [(hker ⟨z, hZK hz⟩).mpr hz]
    exact N.one_mem
  refine ⟨hnorm N1 fun t ht => (key t ht).1, hnorm N2 fun t ht => (key t ht).2, hZB N1, hZB N2,
    fun k hk => ?_⟩
  have htop : (⊤ : Subgroup ↥K) = N1.comap π ⊔ N2.comap π := by
    rw [Subgroup.comap_sup_eq π N1 N2 hπ, sup_N_eq_top, Subgroup.comap_top]
  have hk' : (⟨k, hk⟩ : ↥K) ∈ N1.comap π ⊔ N2.comap π := htop ▸ Subgroup.mem_top _
  have := Subgroup.mem_map_of_mem K.subtype hk'
  rwa [Subgroup.map_sup] at this

end Lift

end CFSG.Quasithin.H13.L32A.C.Alt6
