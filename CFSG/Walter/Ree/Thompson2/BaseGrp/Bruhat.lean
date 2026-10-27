module

public import CFSG.Walter.Ree.Thompson2.BaseGrp.UB
public import CFSG.Walter.Ree.Thompson2.BaseGrp.Field

public section

namespace CFSG.Walter.Ree.T2.BaseGrp

open CFSG.Walter.Ward
open scoped Pointwise

theorem mul_pow_three_of_kleinFour {G : Type*} [Group G] {V : Subgroup G} (hV : IsKleinFour V)
    {τ v : G} (hτ : τ ^ 3 = 1) (hτV : τ ∈ Subgroup.normalizer (V : Set G)) (hv : v ∈ V)
    (hvτ : τ * v * τ⁻¹ ≠ v) : (v * τ) ^ 3 = 1 := by
  obtain ⟨v₁, hv₁⟩ : ∃ v₁, v₁ = τ * v * τ⁻¹ := ⟨_, rfl⟩
  obtain ⟨v₂, hv₂⟩ : ∃ v₂, v₂ = τ * v₁ * τ⁻¹ := ⟨_, rfl⟩
  rw [← hv₁] at hvτ
  have hv₁V : v₁ ∈ V := hv₁ ▸ (Subgroup.mem_normalizer_iff.mp hτV v).mp hv
  have hv₂V : v₂ ∈ V := hv₂ ▸ (Subgroup.mem_normalizer_iff.mp hτV v₁).mp hv₁V
  have hconj_ne : ∀ {a b : G}, a ≠ b → τ * a * τ⁻¹ ≠ τ * b * τ⁻¹ := fun hab h' =>
    hab (by simpa using h')
  have hv1 : v ≠ 1 := by
    rintro rfl
    apply hvτ
    rw [hv₁]
    group
  have hv₁1 : v₁ ≠ 1 := by
    have := hconj_ne hv1
    rw [← hv₁] at this
    simpa using this
  have hv₂1 : v₂ ≠ 1 := by
    have := hconj_ne hv₁1
    rw [← hv₂] at this
    simpa using this
  have hvv₁ : v ≠ v₁ := fun h' => hvτ h'.symm
  have hv₁v₂ : v₁ ≠ v₂ := by
    have := hconj_ne hvv₁
    rwa [← hv₁, ← hv₂] at this
  have hvv₂ : v₂ ≠ v := by
    intro h'
    apply hvτ
    rw [hv₂, hv₁] at h'
    calc v₁ = τ * v * τ⁻¹ := hv₁
      _ = τ * (τ * (τ * v * τ⁻¹) * τ⁻¹) * τ⁻¹ := by rw [h']
      _ = τ * τ * τ * v * (τ * τ * τ)⁻¹ := by group
      _ = v := by rw [← pow_three', hτ]; group
  let _ : IsKleinFour V := hV
  have h3 : (⟨v₂, hv₂V⟩ : V) = ⟨v, hv⟩ * ⟨v₁, hv₁V⟩ := by
    apply IsKleinFour.eq_mul_of_ne_all
    · exact fun h' => hv1 (congrArg Subtype.val h')
    · exact fun h' => hv₁1 (congrArg Subtype.val h')
    · exact fun h' => hvv₁ (congrArg Subtype.val h')
    · exact fun h' => hv₂1 (congrArg Subtype.val h')
    · exact fun h' => hvv₂ (congrArg Subtype.val h')
    · exact fun h' => hv₁v₂ (congrArg Subtype.val h').symm
  have h3' : v₂ = v * v₁ := congrArg Subtype.val h3
  have hsq : (⟨v * v₁, V.mul_mem hv hv₁V⟩ : V) * ⟨v * v₁, V.mul_mem hv hv₁V⟩ = 1 :=
    IsKleinFour.mul_self _
  have hsq' : v * v₁ * (v * v₁) = 1 := congrArg Subtype.val hsq
  calc (v * τ) ^ 3 = v * v₁ * v₂ * (τ * τ * τ) := by rw [hv₂, hv₁, pow_three']; group
    _ = 1 := by rw [← pow_three', hτ, mul_one, h3']; exact hsq'

namespace Ctx

variable {G : Type} [Group G] [Finite G] {k : Type} [Field k] [CharP k 3] {σ : k ≃+* k}
variable (C : Ctx G k σ) [Fintype k]

omit [Fintype k] in
theorem p_eq_three : C.h.p = 3 := by
  obtain ⟨n, -, hq⟩ := C.q_eq
  exact WardLocal.ree_p_eq_three C.h hq

theorem bruhat_unique
    {w : G} (hwN : w ∉ C.N) {p₁ p₁' p₂ p₂' b b' : G} (hp₁ : p₁ ∈ C.U)
    (hp₁' : p₁' ∈ C.U) (hp₂ : p₂ ∈ C.U) (hp₂' : p₂' ∈ C.U) (hb : b ∈ C.B) (hb' : b' ∈ C.B)
    (h : p₁ * w * b * p₂ = p₁' * w * b' * p₂') : p₁ = p₁' ∧ b = b' ∧ p₂ = p₂' := by
  set u := p₁'⁻¹ * p₁ with hu
  have huU : u ∈ C.U := C.U.mul_mem (C.U.inv_mem hp₁') hp₁
  have hconj : w⁻¹ * u * w = b' * p₂' * p₂⁻¹ * b⁻¹ := by
    have : p₁'⁻¹ * (p₁ * w * b * p₂) * p₂⁻¹ * b⁻¹ = p₁'⁻¹ * (p₁' * w * b' * p₂') * p₂⁻¹ * b⁻¹ :=
      by rw [h]
    calc w⁻¹ * u * w = w⁻¹ * (p₁'⁻¹ * (p₁ * w * b * p₂) * p₂⁻¹ * b⁻¹) := by rw [hu]; group
      _ = w⁻¹ * (p₁'⁻¹ * (p₁' * w * b' * p₂') * p₂⁻¹ * b⁻¹) := by rw [this]
      _ = b' * p₂' * p₂⁻¹ * b⁻¹ := by group
  have hN : w⁻¹ * u * w ∈ C.N := by
    rw [hconj]
    exact C.N.mul_mem (C.N.mul_mem (C.N.mul_mem (C.B_le_N hb') (C.U_le_N hp₂'))
      (C.N.inv_mem (C.U_le_N hp₂))) (C.N.inv_mem (C.B_le_N hb))
  have hP : w⁻¹ * u * w ∈ (C.P : Subgroup G) := by
    refine C.mem_P_of_pow hN (j := 1) (by norm_num) ?_
    rw [pow_one, show w⁻¹ * u * w = w⁻¹ * u * w⁻¹⁻¹ by rw [inv_inv], conj_pow,
      C.pow_three_of_mem_U huU]
    group
  have hu1 : u = 1 := by
    by_contra hu1
    have huP : u ∈ (C.P : Subgroup G) := (C.mem_P_iff u).mpr (by
      obtain ⟨β, hβ⟩ := C.mem_U.mp huU
      exact ⟨_, pp_mem_P 0 β 0, hβ⟩)
    exact hwN (mem_normalizer_of_conj_mem C.h C.P huP hu1 hP)
  have hp₁eq : p₁ = p₁' := by
    have : p₁' * u = p₁ := by rw [hu]; group
    rw [← this, hu1, mul_one]
  subst hp₁eq
  have h2 : b * p₂ = b' * p₂' := by
    have := congrArg (fun x => w⁻¹ * p₁⁻¹ * x) h
    simpa [mul_assoc] using this
  have hc : b'⁻¹ * b = p₂' * p₂⁻¹ := by
    calc b'⁻¹ * b = b'⁻¹ * (b * p₂) * p₂⁻¹ := by group
      _ = b'⁻¹ * (b' * p₂') * p₂⁻¹ := by rw [h2]
      _ = p₂' * p₂⁻¹ := by group
  have hc1 : b'⁻¹ * b = 1 := C.eq_one_of_mem_U_B
    (hc ▸ C.U.mul_mem hp₂' (C.U.inv_mem hp₂)) (C.B.mul_mem (C.B.inv_mem hb') hb)
  have hbb : b = b' := by
    have : b' * (b'⁻¹ * b) = b := by group
    rw [← this, hc1, mul_one]
  subst hbb
  refine ⟨rfl, rfl, ?_⟩
  exact mul_left_cancel h2

theorem eq_one_of_mul_sq
    {p b : G} (hp : p ∈ C.U) (hb : b ∈ C.B) (h2 : p * b * (p * b) = 1) :
    p * b = 1 := by
  obtain ⟨n, -, hk⟩ := C.card_k_eq
  obtain ⟨β, rfl⟩ := C.mem_U.mp hp
  obtain ⟨t, rfl⟩ := C.exists_of_mem_B hb
  have h2' : pp σ 0 β 0 * ThompsonN.torus σ (t ^ 2) * (pp σ 0 β 0 * ThompsonN.torus σ (t ^ 2))
      = 1 := C.ι_injective (by simp only [map_mul, map_one]; exact h2)
  have hκ : (((t : k) ^ 2) * ((t : k) ^ 2)) = 1 := by
    have := congrArg (fun x : ThompsonN k σ => (x.κ : k)) h2'
    simp only [ThompsonN.mul_κ, ThompsonN.one_κ, ThompsonN.torus_κ, pp, Units.val_mul,
      Units.val_one, one_mul, Units.val_pow_eq_pow_val] at this
    exact this
  have ht2 : (t : k) ^ 2 = 1 := by
    rcases mul_self_eq_one_iff.mp hκ with h | h
    · exact h
    · exact absurd ⟨(t : k), by rw [← h, sq]⟩ (not_isSquare_neg_one hk)
  have ht : t ^ 2 = 1 := Units.ext (by simpa using ht2)
  rw [ht, tor, map_one, map_one, mul_one] at h2 ⊢
  have h3 : C.ι (pp σ 0 β 0) ^ 3 = 1 := C.pow_three_of_mem_U (C.ι_pp_mem_U β)
  calc C.ι (pp σ 0 β 0) = C.ι (pp σ 0 β 0) ^ 3 * (C.ι (pp σ 0 β 0) * C.ι (pp σ 0 β 0))⁻¹ := by
        group
    _ = 1 := by rw [h3, h2]; group

theorem bruhat
    {w : G} (hwL : w ∈ C.L) (hwN : w ∉ C.N) {x : G} (hxL : x ∈ C.L)
    (hx : ∀ p ∈ C.U, ∀ b ∈ C.B, x ≠ p * b) :
    ∃ p₁ ∈ C.U, ∃ b ∈ C.B, ∃ p₂ ∈ C.U, x = p₁ * w * b * p₂ := by
  classical
  let F : C.U × C.B × C.U → G := fun y => y.1 * w * y.2.1 * y.2.2
  let F' : C.U × C.B → G := fun y => y.1 * y.2
  have hF : Function.Injective F := by
    rintro ⟨p₁, b, p₂⟩ ⟨p₁', b', p₂'⟩ h
    obtain ⟨h1, h2, h3⟩ := C.bruhat_unique hwN p₁.2 p₁'.2 p₂.2 p₂'.2 b.2 b'.2 h
    exact Prod.ext (Subtype.ext h1) (Prod.ext (Subtype.ext h2) (Subtype.ext h3))
  have hF' : Function.Injective F' := by
    rintro ⟨⟨p, hp⟩, ⟨b, hb⟩⟩ ⟨⟨p', hp'⟩, ⟨b', hb'⟩⟩ h
    change p * b = p' * b' at h
    have h0 : p'⁻¹ * p = b' * b⁻¹ := by
      calc p'⁻¹ * p = p'⁻¹ * (p * b) * b⁻¹ := by group
        _ = p'⁻¹ * (p' * b') * b⁻¹ := by rw [h]
        _ = b' * b⁻¹ := by group
    have h1 : p'⁻¹ * p = 1 := C.eq_one_of_mem_U_B (C.U.mul_mem (C.U.inv_mem hp') hp)
      (h0 ▸ C.B.mul_mem hb' (C.B.inv_mem hb))
    have hpp : p = p' := by
      have : p' * (p'⁻¹ * p) = p := by group
      rw [← this, h1, mul_one]
    subst hpp
    have hbb : b = b' := mul_left_cancel h
    subst hbb
    rfl
  have hdisj : Disjoint (Set.range F) (Set.range F') := by
    rw [Set.disjoint_left]
    rintro _ ⟨⟨⟨p₁, hp₁⟩, ⟨b, hb⟩, ⟨p₂, hp₂⟩⟩, rfl⟩ ⟨⟨⟨p, hp⟩, ⟨b', hb'⟩⟩, h⟩
    change p * b' = p₁ * w * b * p₂ at h
    apply hwN
    have : w = p₁⁻¹ * p * b' * p₂⁻¹ * b⁻¹ := by
      calc w = p₁⁻¹ * (p₁ * w * b * p₂) * p₂⁻¹ * b⁻¹ := by group
        _ = p₁⁻¹ * (p * b') * p₂⁻¹ * b⁻¹ := by rw [h]
        _ = _ := by group
    rw [this]
    exact C.N.mul_mem (C.N.mul_mem (C.N.mul_mem (C.N.mul_mem (C.N.inv_mem (C.U_le_N hp₁))
      (C.U_le_N hp)) (C.B_le_N hb')) (C.N.inv_mem (C.U_le_N hp₂)))
      (C.N.inv_mem (C.B_le_N hb))
  have hsub : Set.range F ∪ Set.range F' ⊆ (C.L : Set G) := by
    rintro _ (⟨⟨p₁, b, p₂⟩, rfl⟩ | ⟨⟨p, b⟩, rfl⟩)
    · exact C.L.mul_mem (C.L.mul_mem (C.L.mul_mem (C.U_le_L p₁.2) hwL) (C.B_le_L b.2))
        (C.U_le_L p₂.2)
    · exact C.L.mul_mem (C.U_le_L p.2) (C.B_le_L b.2)
  have hcard : (C.L : Set G).ncard ≤ (Set.range F ∪ Set.range F').ncard := by
    rw [Set.ncard_union_eq hdisj, Set.ncard_range_of_injective hF,
      Set.ncard_range_of_injective hF', Nat.card_prod, Nat.card_prod, Nat.card_prod, C.card_U]
    have hL : (C.L : Set G).ncard = Nat.card C.L := (Nat.card_coe_set_eq (C.L : Set G)).symm
    rw [hL, C.card_L]
    have hB := C.card_B
    set m := Nat.card C.B
    rw [← hB]
    have e1 : (2 * m + 1) ^ 2 - 1 = 2 * (2 * m * m + 2 * m) := by
      have : (2 * m + 1) ^ 2 = 2 * (2 * m * m + 2 * m) + 1 := by ring
      omega
    rw [e1, show (2 * m + 1) * (2 * (2 * m * m + 2 * m)) = 2 * ((2 * m + 1) *
      (2 * m * m + 2 * m)) by ring, Nat.mul_div_cancel_left _ (by norm_num)]
    apply le_of_eq
    ring
  have heq := Set.eq_of_subset_of_ncard_le hsub hcard (Set.toFinite _)
  have hx' : x ∈ Set.range F ∪ Set.range F' := heq ▸ hxL
  rcases hx' with ⟨⟨p₁, b, p₂⟩, hy⟩ | ⟨⟨p, b⟩, hy⟩
  · exact ⟨p₁, p₁.2, b, b.2, p₂, p₂.2, hy.symm⟩
  · exact absurd hy.symm (hx p p.2 b b.2)

theorem bruhat_invol
    {w : G} (hwL : w ∈ C.L) (hwN : w ∉ C.N) (hw2 : w * w = 1)
    (hwinv : ∀ b ∈ C.B, w * b * w⁻¹ = b⁻¹) {x : G} (hxL : x ∈ C.L) (hx2 : x * x = 1)
    (hx1 : x ≠ 1) : ∃ p ∈ C.U, ∃ b ∈ C.B, x = p * (w * b) * p⁻¹ := by
  obtain ⟨p₁, hp₁, b, hb, p₂, hp₂, rfl⟩ := C.bruhat hwL hwN hxL (by
    rintro p hp b hb rfl
    exact hx1 (C.eq_one_of_mul_sq hp hb hx2))
  have hwi : w⁻¹ = w := inv_eq_of_mul_eq_one_right hw2
  have hbw : b⁻¹ * w = w * b := by
    have := hwinv b hb
    calc b⁻¹ * w = w * b * w⁻¹ * w := by rw [this]
      _ = w * b := by group
  have hinv : p₂⁻¹ * w * b * p₁⁻¹ = p₁ * w * b * p₂ := by
    have hxi : (p₁ * w * b * p₂)⁻¹ = p₁ * w * b * p₂ := inv_eq_of_mul_eq_one_right hx2
    calc p₂⁻¹ * w * b * p₁⁻¹ = p₂⁻¹ * (w * b) * p₁⁻¹ := by group
      _ = p₂⁻¹ * (b⁻¹ * w) * p₁⁻¹ := by rw [hbw]
      _ = p₂⁻¹ * b⁻¹ * w⁻¹ * p₁⁻¹ := by rw [hwi]; group
      _ = (p₁ * w * b * p₂)⁻¹ := by group
      _ = p₁ * w * b * p₂ := hxi
  obtain ⟨-, -, h3⟩ := C.bruhat_unique hwN (C.U.inv_mem hp₂) hp₁ (C.U.inv_mem hp₁) hp₂ hb hb
    hinv
  refine ⟨p₁, hp₁, b, hb, ?_⟩
  rw [← h3]
  group

theorem exists_conj_mem_U
    {τ : G} (hτL : τ ∈ C.L) (hτ3 : τ ^ 3 = 1) :
    ∃ y ∈ C.L, y * τ * y⁻¹ ∈ C.U := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨n, -, hq⟩ := C.q_eq
  have hUfacts := JT.psl2UnipotentFacts C.L C.Liso C.h.p_ne_two C.h.f_pos.ne'
  have hp3 := C.p_eq_three
  set U' : Subgroup C.L := C.U.subgroupOf C.L with hU'
  have hU'card : Nat.card U' = C.h.q := by
    rw [hU', Nat.card_congr (Subgroup.subgroupOfEquivOfLe C.U_le_L).toEquiv, C.card_U]
  have hU'p : IsPGroup 3 U' := IsPGroup.of_card (n := 2 * n + 1) (by rw [hU'card, hq])
  have hmax : ∀ {Q : Subgroup C.L}, IsPGroup 3 Q → U' ≤ Q → Q = U' := by
    intro Q hQ hle
    have hQmap : IsPGroup 3 (Q.map C.L.subtype) := hQ.map _
    have hdvd := hUfacts.card_dvd (Q.map C.L.subtype) (Subgroup.map_subtype_le Q)
      (hp3 ▸ hQmap)
    rw [Subgroup.card_map_of_injective C.L.subtype_injective] at hdvd
    refine (Subgroup.eq_of_le_of_card_ge hle ?_).symm
    rw [hU'card]
    exact Nat.le_of_dvd (by have := C.h.three_le_q; omega) hdvd
  let S : Sylow 3 C.L := ⟨U', hU'p, fun hQ hle => hmax hQ hle⟩
  have hτp : IsPGroup 3 (Subgroup.zpowers (⟨τ, hτL⟩ : C.L)) := by
    have h1 : orderOf τ ∣ 3 := orderOf_dvd_of_pow_eq_one hτ3
    rcases (Nat.dvd_prime Nat.prime_three).mp h1 with h | h
    · exact IsPGroup.of_card (n := 0) (by rw [Nat.card_zpowers, Subgroup.orderOf_mk, h, pow_zero])
    · exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, Subgroup.orderOf_mk, h, pow_one])
  obtain ⟨S', hS'⟩ := hτp.exists_le_sylow
  obtain ⟨y, hy⟩ := MulAction.exists_smul_eq C.L S' S
  have hmem : (MulAut.conj y) • (⟨τ, hτL⟩ : C.L) ∈ ((y • S' : Sylow 3 C.L) : Subgroup C.L) := by
    rw [Sylow.coe_subgroup_smul]
    exact Subgroup.smul_mem_pointwise_smul _ _ _ (hS' (Subgroup.mem_zpowers _))
  rw [hy] at hmem
  refine ⟨y, y.2, ?_⟩
  have : ((MulAut.conj y • (⟨τ, hτL⟩ : C.L) : C.L) : G) = y * τ * (y : G)⁻¹ := by
    simp [MulAut.smul_def, MulAut.conj_apply]
  rw [← this]
  exact hmem

end Ctx

end CFSG.Walter.Ree.T2.BaseGrp
