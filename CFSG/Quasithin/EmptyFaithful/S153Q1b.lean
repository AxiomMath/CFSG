module

public import CFSG.Quasithin.EmptyFaithful.S153QDef

public section

namespace CFSG.Quasithin

namespace S153Q

namespace Q1

theorem le_center_of_isCyclic {G : Type*} [Group G] (hG : commutator G = ⊤) {K : Subgroup G}
    [K.Normal] [IsCyclic K] : K ≤ Subgroup.center G := by
  let φ : G →* MulAut K := MulAut.conjNormal
  have hcomm : ∀ α β : MulAut K, α * β = β * α := by
    intro α β
    obtain ⟨m, hm⟩ := MonoidHom.map_cyclic α.toMonoidHom
    obtain ⟨n, hn⟩ := MonoidHom.map_cyclic β.toMonoidHom
    refine MulEquiv.ext fun k => ?_
    change α (β k) = β (α k)
    have e1 : α (β k) = (k ^ n) ^ m := by
      rw [show β k = k ^ n from hn k, show α (k ^ n) = (k ^ n) ^ m from hm (k ^ n)]
    have e2 : β (α k) = (k ^ m) ^ n := by
      rw [show α k = k ^ m from hm k, show β (k ^ m) = (k ^ m) ^ n from hn (k ^ m)]
    rw [e1, e2, ← zpow_mul, ← zpow_mul, mul_comm]
  have hker : commutator G ≤ φ.ker := by
    rw [_root_.commutator_def, Subgroup.commutator_le]
    intro a _ b _
    rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_def, hcomm (φ a) (φ b),
      mul_inv_cancel_right, mul_inv_cancel]
  intro k hk
  rw [Subgroup.mem_center_iff]
  intro g
  have hg : g ∈ φ.ker := hker (hG ▸ Subgroup.mem_top g)
  rw [MonoidHom.mem_ker] at hg
  have := congrArg (fun α : MulAut K => ((α ⟨k, hk⟩ : K) : G)) hg
  simp only [φ, MulAut.conjNormal_apply, MulAut.one_apply] at this
  calc g * k = g * k * g⁻¹ * g := by group
    _ = k * g := by rw [this]

theorem exists_ne_one_of_card_three {X : Type*} [Group X] [Finite X] {K : Subgroup X}
    (hK : Nat.card K = 3) : ∃ z ∈ K, z ≠ 1 ∧ z ^ 3 = 1 := by
  obtain ⟨z, hz⟩ : ∃ z : K, z ≠ 1 := by
    have : Nontrivial K := by
      rw [← Finite.one_lt_card_iff_nontrivial, hK]
      norm_num
    exact exists_ne 1
  refine ⟨z, z.2, fun h => hz (Subtype.ext h), ?_⟩
  have := pow_card_eq_one' (x := z)
  rw [hK] at this
  exact congrArg Subtype.val this

theorem normal_closure_of_conj {H : Type*} [Group H] {S : Set H}
    (hS : ∀ x ∈ S, ∀ g : H, g * x * g⁻¹ ∈ S) : (Subgroup.closure S).Normal where
  conj_mem n hn g := by
    induction hn using Subgroup.closure_induction with
    | mem x hx => exact Subgroup.subset_closure (hS x hx g)
    | one => simp
    | mul x y _ _ hx hy =>
      have : g * (x * y) * g⁻¹ = (g * x * g⁻¹) * (g * y * g⁻¹) := by group
      rw [this]
      exact Subgroup.mul_mem _ hx hy
    | inv x _ hx =>
      have : g * x⁻¹ * g⁻¹ = (g * x * g⁻¹)⁻¹ := by group
      rw [this]
      exact Subgroup.inv_mem _ hx

theorem closure_odd_eq_top {H : Type*} [Group H] [Finite H] [Group.IsPerfect H] :
    Subgroup.closure {x : H | Odd (orderOf x)} = ⊤ := by
  classical
  set S : Set H := {x | Odd (orderOf x)} with hS
  have hSconj : ∀ x ∈ S, ∀ g : H, g * x * g⁻¹ ∈ S := by
    intro x hx g
    have h1 : orderOf (g * x * g⁻¹) = orderOf x := by
      simpa using orderOf_injective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective x
    show Odd (orderOf (g * x * g⁻¹))
    rw [h1]
    exact hx
  have : (Subgroup.closure S).Normal := normal_closure_of_conj hSconj
  have h2 : IsPGroup 2 (H ⧸ Subgroup.closure S) := by
    intro q
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
    have hn : orderOf g ≠ 0 := (orderOf_pos g).ne'
    obtain ⟨a, m, hm, hgm⟩ := Nat.exists_eq_two_pow_mul_odd hn
    refine ⟨a, ?_⟩
    have hdvd : 2 ^ a ∣ orderOf g := ⟨m, hgm⟩
    have hord : orderOf (g ^ 2 ^ a) = m := by
      rw [orderOf_pow_of_dvd (pow_ne_zero _ two_ne_zero) hdvd, hgm,
        Nat.mul_div_cancel_left _ (by positivity)]
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
    exact Subgroup.subset_closure (show Odd (orderOf (g ^ 2 ^ a)) by rw [hord]; exact hm)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Group.IsNilpotent (H ⧸ Subgroup.closure S) := h2.isNilpotent
  have : Group.IsSolvable (H ⧸ Subgroup.closure S) := IsNilpotent.to_isSolvable
  by_contra hne
  have : Nontrivial (H ⧸ Subgroup.closure S) := QuotientGroup.nontrivial_iff.mpr hne
  exact Group.IsPerfect.not_isSolvable (H ⧸ Subgroup.closure S) inferInstance

theorem hatGrp_map {G K : Type*} [Group G] [Group K] {Γ₀ Ah₀ : Subgroup G} {z₀ : G}
    (h : HatGrp Γ₀ Ah₀ z₀) (f : G →* K) (hf : Function.Injective f) {Γ : Subgroup K}
    (hΓ : Γ = Γ₀.map f) : HatGrp Γ (Ah₀.map f) (f z₀) := by
  subst hΓ
  have hmem : ∀ x : G, f x ∈ Ah₀.map f ↔ x ∈ Ah₀ := fun x => Subgroup.mem_map_iff_mem hf
  refine
    { Ah_le := Subgroup.map_mono h.Ah_le
      Ah_norm := ?_
      index2 := ?_
      z_mem := ⟨z₀, h.z_mem, rfl⟩
      z_ne := fun e => h.z_ne (hf (by rw [e, map_one]))
      z_cube := by rw [← map_pow, h.z_cube, map_one]
      z_central := ?_
      outer := ?_
      perfect := ?_
      card := ?_
      psi := ?_
      gen_odd := ?_ }
  · rintro _ ⟨g, hg, rfl⟩ _ ⟨a, ha, rfl⟩
    exact ⟨g * a * g⁻¹, h.Ah_norm g hg a ha, by simp⟩
  · rintro _ ⟨g, hg, rfl⟩ _ ⟨g', hg', rfl⟩ hng hng'
    rw [← map_mul]
    exact ⟨g * g', h.index2 g hg g' hg' (fun hh => hng ((hmem g).2 hh))
      (fun hh => hng' ((hmem g').2 hh)), rfl⟩
  · rintro _ ⟨g, hg, rfl⟩
    rw [← map_mul, ← map_mul, h.z_central g hg]
  · rintro _ ⟨t, ht, rfl⟩ hnt
    have e : f t * f z₀ * (f t)⁻¹ = f (t * z₀ * t⁻¹) := by simp
    rw [e, h.outer t ht (fun hh => hnt ((hmem t).2 hh)), map_inv]
  · rw [← Subgroup.map_commutator]
    exact Subgroup.map_mono h.perfect
  · rw [Subgroup.card_map_of_injective hf]
    exact h.card
  · obtain ⟨ψ, hψs, hψk⟩ := h.psi
    let e := Subgroup.equivMapOfInjective Ah₀ f hf
    refine ⟨ψ.comp e.symm.toMonoidHom, hψs.comp e.symm.surjective, fun g => ?_⟩
    obtain ⟨g₀, rfl⟩ := e.surjective g
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply,
      Subgroup.coe_equivMapOfInjective_apply, e]
    rw [hψk g₀, ← MonoidHom.map_zpowers]
    exact (Subgroup.mem_map_iff_mem hf).symm
  · intro X hX
    refine Subgroup.map_le_iff_le_comap.2 (h.gen_odd (X.comap f) fun x hx hxo => ?_)
    exact hX (f x) ⟨x, hx, rfl⟩ (by rwa [orderOf_injective f hf])

end Q1

end S153Q

end CFSG.Quasithin
