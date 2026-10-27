module

public import CFSG.SignalizerFunctorTheorem.MinimalAction.Main

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF79

open CFSG

section Abstract

theorem le_normalizer_of_conj_mem {G : Type*} [Group G] (M T : Subgroup G)
    (hMT : ∀ g ∈ M, ∀ t ∈ T, g * t * g⁻¹ ∈ T) : M ≤ Subgroup.normalizer (T : Set G) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨fun hx => hMT g hg x hx, fun hx => ?_⟩
  have := hMT g⁻¹ (M.inv_mem hg) _ hx
  have e : g⁻¹ * (g * x * g⁻¹) * g⁻¹⁻¹ = x := by group
  rwa [e] at this

variable {H : Type} [Group H] [Finite H]

theorem ap_pxq_elem (β : MulAut H) (hβ : β ^ 3 = 1) (k : H) (hk2 : orderOf k = 2)
    (hkfix : β k = k) (hcore : ∀ y ∈ pCore 3 H, β y = y → y * k = k * y) :
    ∀ y ∈ pCore 3 H, y * k = k * y := by
  let P0 : Subgroup (MulAut H) := Subgroup.zpowers β
  let S := H ⋊[P0.subtype] P0
  haveI : Finite S := Finite.of_injective (fun s : S => (s.left, s.right))
    (fun s t h => by
      have h1 := congrArg Prod.fst h
      have h2 := congrArg Prod.snd h
      exact SemidirectProduct.ext h1 h2)
  have hP0 : IsPGroup 3 P0 := by
    intro g
    obtain ⟨g, n, rfl⟩ := g
    refine ⟨1, ?_⟩
    apply Subtype.ext
    simp only [pow_one, Subgroup.coe_pow, Subgroup.coe_one]
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul]
    simp only [Nat.cast_ofNat]
    rw [show (β ^ (3 : ℤ)) = 1 by exact_mod_cast hβ, one_zpow]
  let π : P0 := ⟨β, Subgroup.mem_zpowers β⟩
  have hact : ∀ (g : P0) (x : H), (SemidirectProduct.inr g * SemidirectProduct.inl x *
      (SemidirectProduct.inr g)⁻¹ : S) = SemidirectProduct.inl (g.1 x) := by
    intro g x
    rw [← map_inv]
    exact (SemidirectProduct.inl_aut g x).symm
  have key := @le_normalizer_of_conj_mem S _
  let X : Subgroup S := (pCore 3 H).map SemidirectProduct.inl
  let Q : Subgroup S := (Subgroup.zpowers k).map SemidirectProduct.inl
  let Pp : Subgroup S := (SemidirectProduct.inr : P0 →* S).range
  have hQcop : Nat.Coprime 3 (Nat.card Q) := by
    have : Nat.card Q = 2 := by
      rw [Subgroup.card_map_of_injective SemidirectProduct.inl_injective, Nat.card_zpowers, hk2]
    rw [this]; norm_num
  have hkfix' : ∀ g : P0, g.1 k = k := by
    rintro ⟨g, n, rfl⟩
    show (β ^ n) k = k
    induction n using Int.induction_on with
    | zero => simp
    | succ m ih =>
      rw [zpow_add_one, MulAut.mul_apply, hkfix, ih]
    | pred m ih =>
      rw [zpow_sub_one, MulAut.mul_apply]
      have : (β⁻¹) k = k := by
        rw [MulAut.inv_apply]; exact (MulEquiv.symm_apply_eq β).mpr hkfix.symm
      rw [this, ih]
  have hTh := CFSG.SignalizerFunctorTheorem.MinimalAction.thompson_semidirect_centralizer
    (Nat.prime_three) (by norm_num) (P := Pp) (Q := Q) (X := X)
    (hP0.of_surjective (SemidirectProduct.inr : P0 →* S).rangeRestrict
      (SemidirectProduct.inr : P0 →* S).rangeRestrict_surjective) hQcop ?_
    (pCore_isPGroup.map _) ?_ ?_ ?_
  · intro y hy
    have hyX : (SemidirectProduct.inl y : S) ∈ X := Subgroup.mem_map_of_mem _ hy
    have hkQ : (SemidirectProduct.inl k : S) ∈ Q := Subgroup.mem_map_of_mem _
      (Subgroup.mem_zpowers k)
    have := Subgroup.mem_centralizer_iff.mp (hTh hyX) _ hkQ
    rw [← map_mul, ← map_mul] at this
    exact (SemidirectProduct.inl_injective this).symm
  · refine key _ _ ?_
    rintro _ ⟨g, rfl⟩ _ ⟨q, hq, rfl⟩
    rw [hact]
    refine Subgroup.mem_map_of_mem _ ?_
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hq
    rw [map_zpow, hkfix' g]
    exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers k) m
  · have hchar : ∀ (φ : MulAut H) (y : H), y ∈ pCore 3 H → φ y ∈ pCore 3 H := by
      intro φ y hy
      have := Subgroup.characteristic_iff_map_eq.mp (inferInstance : (pCore 3 H).Characteristic)
        φ
      rw [← this]
      exact Subgroup.mem_map_of_mem _ hy
    refine key _ _ ?_
    rintro _ ⟨g, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [hact]
    exact Subgroup.mem_map_of_mem _ (hchar g.1 y hy)
  · refine key _ _ ?_
    rintro _ ⟨q, hq, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [← map_inv, ← map_mul, ← map_mul]
    exact Subgroup.mem_map_of_mem _ ((pCore_normal (p := 3) (G := H)).conj_mem y hy q)
  · rintro _ ⟨⟨y, hy, rfl⟩, hyC⟩
    have hβy : β y = y := by
      have h1 := Subgroup.mem_centralizer_iff.mp hyC (SemidirectProduct.inr π) ⟨π, rfl⟩
      have h2 := hact π y
      rw [mul_inv_eq_iff_eq_mul.mpr h1.symm.symm] at h2
      exact SemidirectProduct.inl_injective h2.symm
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨q, hq, rfl⟩
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hq
    have hc : Commute y k := hcore y hy hβy
    rw [← map_mul, ← map_mul]
    exact congrArg _ ((hc.zpow_right m).symm.eq)

theorem ap_pxq (β : MulAut H) (hβ : β ^ 3 = 1) (K : Subgroup H)
    (hKa : Nonempty (K ≃* alternatingGroup (Fin 5))) (hKfix : ∀ k ∈ K, β k = k)
    (hcore : ∀ y ∈ pCore 3 H, β y = y → ∀ k ∈ K, y * k = k * y) :
    ∀ y ∈ pCore 3 H, ∀ k ∈ K, y * k = k * y := by
  obtain ⟨e⟩ := hKa
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hdvd : 2 ∣ Nat.card (alternatingGroup (Fin 5)) := by
    rw [nat_card_alternatingGroup]
    simp [Nat.factorial]
  obtain ⟨k0, hk0⟩ := exists_prime_orderOf_dvd_card' 2 hdvd
  set k1 : K := e.symm k0 with hk1
  have hk1o : orderOf k1 = 2 := by rw [hk1, MulEquiv.orderOf_eq, hk0]
  have hk1ne : k1 ≠ 1 := by
    intro h; rw [h, orderOf_one] at hk1o; omega
  have hkH : orderOf (k1 : H) = 2 := by rw [Subgroup.orderOf_coe, hk1o]
  have hone := ap_pxq_elem β hβ (k1 : H) hkH (hKfix _ k1.2)
    (fun y hy hβy => hcore y hy hβy _ k1.2)
  let Cs : Subgroup K := (Subgroup.centralizer (pCore 3 H : Set H)).comap K.subtype
  haveI : Cs.Normal := by
    refine ⟨fun c hc g => ?_⟩
    rw [Subgroup.mem_comap, Subgroup.mem_centralizer_iff] at hc ⊢
    intro y hy
    have hy' : (g : H)⁻¹ * y * ((g : H)⁻¹)⁻¹ ∈ pCore 3 H :=
      (pCore_normal (p := 3) (G := H)).conj_mem y hy _
    have h1 := hc _ hy'
    simp only [Subgroup.coe_subtype, inv_inv] at h1
    show y * ((g : H) * (c : H) * (g : H)⁻¹) = ((g : H) * (c : H) * (g : H)⁻¹) * y
    calc y * ((g : H) * (c : H) * (g : H)⁻¹)
        = (g : H) * (((g : H)⁻¹ * y * (g : H)) * (c : H)) * (g : H)⁻¹ := by group
      _ = (g : H) * ((c : H) * ((g : H)⁻¹ * y * (g : H))) * (g : H)⁻¹ := by rw [h1]
      _ = _ := by group
  haveI : IsSimpleGroup K := e.isSimpleGroup
  have hk1C : k1 ∈ Cs := by
    rw [Subgroup.mem_comap, Subgroup.mem_centralizer_iff]
    intro y hy
    exact hone y hy
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal Cs with h | h
  · exact absurd (by simpa [h] using hk1C) hk1ne
  · intro y hy k hk
    have : (⟨k, hk⟩ : K) ∈ Cs := by rw [h]; trivial
    rw [Subgroup.mem_comap, Subgroup.mem_centralizer_iff] at this
    exact this y hy

end Abstract

end CFSG.RankThree.PartTwo.Sec21.FF79
