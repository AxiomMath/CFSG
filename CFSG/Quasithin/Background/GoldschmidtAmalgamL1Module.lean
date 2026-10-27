module

public import CFSG.Quasithin.Background.GoldschmidtAmalgamL1Basic
public import CFSG.Quasithin.Recognition.F112WLocal

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.F7

namespace F6

namespace GoldAmL

variable {D : Type*} [Group D] [Finite D]

theorem exists_klein_four {a b : D} (ha : a ^ 2 = 1) (hb : b ^ 2 = 1) (hab : a * b = b * a)
    (ha1 : a ≠ 1) (hb1 : b ≠ 1) (hne : a ≠ b) :
    ∃ K : Subgroup D, (K : Set D) = {1, a, b, a * b} ∧ Nat.card K = 4 := by
  have ha' : a * a = 1 := by rw [← pow_two]; exact ha
  have hb' : b * b = 1 := by rw [← pow_two]; exact hb
  have hba : b * a = a * b := hab.symm
  have hbab : b * (a * b) = a := by rw [← mul_assoc, hba, mul_assoc, hb', mul_one]
  have haab : a * (a * b) = b := by rw [← mul_assoc, ha', one_mul]
  have habb : a * b * b = a := by rw [mul_assoc, hb', mul_one]
  have habab : a * b * (a * b) = 1 := by rw [mul_assoc, hbab, ha']
  have haba : a * b * a = b := by rw [← hba, mul_assoc, ha', mul_one]
  let K : Subgroup D :=
    { carrier := {1, a, b, a * b}
      one_mem' := by simp
      mul_mem' := by
        intro x y hx hy
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy ⊢
        rcases hx with rfl | rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl | rfl <;>
          simp [ha', hb', hba, hbab, haab, habb, habab, haba]
      inv_mem' := by
        intro x hx
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢
        rcases hx with rfl | rfl | rfl | rfl
        · simp
        · right; left; exact inv_eq_of_mul_eq_one_right ha'
        · right; right; left; exact inv_eq_of_mul_eq_one_right hb'
        · right; right; right
          rw [mul_inv_rev, inv_eq_of_mul_eq_one_right ha', inv_eq_of_mul_eq_one_right hb', hba] }
  refine ⟨K, rfl, ?_⟩
  have hab1 : a * b ≠ 1 := by
    intro h
    exact hne (by rw [← inv_eq_of_mul_eq_one_right h, inv_eq_of_mul_eq_one_right ha'])
  have haab' : a ≠ a * b := by
    intro h
    exact hb1 (by simpa using (congrArg (fun y => a⁻¹ * y) h).symm)
  have hbab' : b ≠ a * b := by
    intro h
    exact ha1 (by simpa using congrArg (fun y => y * b⁻¹) h.symm)
  show Nat.card ↥(K : Set D) = 4
  rw [Nat.card_coe_set_eq]
  show ({1, a, b, a * b} : Set D).ncard = 4
  rw [Set.ncard_insert_of_notMem, Set.ncard_insert_of_notMem, Set.ncard_pair hbab']
  · simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨hne, haab'⟩
  · simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨ha1.symm, hb1.symm, hab1.symm⟩

theorem coset_decomp {H T : Subgroup D} (h3 : T.relIndex H = 3) {x : D} (hx : x ∈ H)
    (hxT : x ∉ T) (hx2T : x * x ∉ T) {g : D} (hg : g ∈ H) :
    g ∈ T ∨ (∃ t ∈ T, g = x * t) ∨ (∃ t ∈ T, g = x * x * t) := by
  classical
  let x' : ↥H := ⟨x, hx⟩
  let g' : ↥H := ⟨g, hg⟩
  let T' : Subgroup ↥H := T.subgroupOf H
  have hcard : Nat.card (↥H ⧸ T') = 3 := h3
  let _inst : Fintype (↥H ⧸ T') := Fintype.ofFinite _
  have hcard' : Fintype.card (↥H ⧸ T') = 3 := by rw [← Nat.card_eq_fintype_card]; exact hcard
  let a₀ : ↥H ⧸ T' := ((1 : ↥H) : ↥H ⧸ T')
  let a₁ : ↥H ⧸ T' := ((x' : ↥H) : ↥H ⧸ T')
  let a₂ : ↥H ⧸ T' := ((x' * x' : ↥H) : ↥H ⧸ T')
  have h01 : a₀ ≠ a₁ := by
    intro h
    have := QuotientGroup.eq.mp h
    exact hxT (by simpa [T', Subgroup.mem_subgroupOf, x'] using this)
  have h02 : a₀ ≠ a₂ := by
    intro h
    have := QuotientGroup.eq.mp h
    exact hx2T (by simpa [T', Subgroup.mem_subgroupOf, x'] using this)
  have h12 : a₁ ≠ a₂ := by
    intro h
    have := QuotientGroup.eq.mp h
    apply hxT
    have := Subgroup.mem_subgroupOf.mp (show x'⁻¹ * (x' * x') ∈ T' from this)
    simpa [x', mul_assoc] using this
  have hmem : (g' : ↥H ⧸ T') = a₀ ∨ (g' : ↥H ⧸ T') = a₁ ∨ (g' : ↥H ⧸ T') = a₂ := by
    by_contra hcon
    push Not at hcon
    obtain ⟨c0, c1, c2⟩ := hcon
    have hsub : ({a₀, a₁, a₂, (g' : ↥H ⧸ T')} : Finset (↥H ⧸ T')).card = 4 := by
      rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_pair c2.symm]
      · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨h12, c1.symm⟩
      · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨h01, h02, c0.symm⟩
    have := Finset.card_le_univ ({a₀, a₁, a₂, (g' : ↥H ⧸ T')} : Finset (↥H ⧸ T'))
    omega
  rcases hmem with h | h | h
  · left
    have := QuotientGroup.eq.mp h.symm
    simpa [T', Subgroup.mem_subgroupOf, g'] using this
  · right; left
    have := QuotientGroup.eq.mp h.symm
    have h2 : x⁻¹ * g ∈ T := by
      simpa [T', Subgroup.mem_subgroupOf, g', x'] using this
    exact ⟨x⁻¹ * g, h2, by group⟩
  · right; right
    have := QuotientGroup.eq.mp h.symm
    have h2 : (x * x)⁻¹ * g ∈ T := by
      simpa [T', Subgroup.mem_subgroupOf, g', x'] using this
    exact ⟨(x * x)⁻¹ * g, h2, by group⟩

structure Vertex (H T : Subgroup D) : Prop where
  sylow : IsSylowTwoOf T H
  index_eq : T.relIndex H = 3
  quotient : Nonempty (↥H ⧸ CFSG.Open.pCore 2 ↥H ≃* Equiv.Perm (Fin 3))
  charTwo : CharTwo H

theorem GoldHyp.vertex_left {G₁ G₂ : Subgroup D} (h : GoldHyp G₁ G₂) : Vertex G₁ (G₁ ⊓ G₂) :=
  ⟨h.isSylowTwoOf_left, h.relIndex_left, h.amalgam.quotient₁, h.charTwo₁⟩

theorem GoldHyp.vertex_right {G₁ G₂ : Subgroup D} (h : GoldHyp G₁ G₂) : Vertex G₂ (G₁ ⊓ G₂) :=
  ⟨h.isSylowTwoOf_right, h.relIndex_right, h.amalgam.quotient₂, h.charTwo₂⟩

namespace Vertex

variable {H T : Subgroup D} (hv : Vertex H T)

include hv

omit [Finite D] in
theorem T_le : T ≤ H := hv.sylow.1

omit [Finite D] in
theorem isPGroup : IsPGroup 2 T := hv.sylow.2.1

theorem pCoreOf_le : pCoreOf 2 H ≤ T := isSylowTwoOf_pCoreOf_le hv.sylow

omit [Finite D] in
theorem relIndex_pCoreOf : (pCoreOf 2 H).relIndex H = 6 :=
  F112W.relIndex_pCoreOf_eq_six hv.quotient

theorem centerOf_le : centerOf T ≤ pCoreOf 2 H := by
  intro z hz
  exact hv.charTwo ⟨hv.T_le hz.1, Subgroup.centralizer_le hv.pCoreOf_le hz.2⟩

theorem exists_order_three : ∃ x ∈ H, orderOf x = 3 := by
  have h3 : 3 ∣ Nat.card ↥H := by
    rw [← Subgroup.card_mul_index (T.subgroupOf H)]
    rw [show (T.subgroupOf H).index = 3 from hv.index_eq]
    exact dvd_mul_left 3 _
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥H) 3 h3
  exact ⟨x, x.2, by rw [← hx]; exact Subgroup.orderOf_coe x⟩

theorem relIndex_pCoreOf_T : (pCoreOf 2 H).relIndex T = 2 := by
  have h1 := Subgroup.relIndex_mul_relIndex (pCoreOf 2 H) T H hv.pCoreOf_le hv.T_le
  rw [hv.relIndex_pCoreOf, hv.index_eq] at h1
  omega

omit [Finite D] in
theorem not_mem_of_orderOf {x : D} (hx : orderOf x = 3) : x ∉ T := by
  intro hxT
  obtain ⟨k, hk⟩ := hv.isPGroup ⟨x, hxT⟩
  have h1 : x ^ (2 ^ k) = 1 := congrArg Subtype.val hk
  have h2 : 3 ∣ 2 ^ k := hx ▸ orderOf_dvd_of_pow_eq_one h1
  have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h2
  omega

omit [Finite D] in
theorem sq_not_mem_of_orderOf {x : D} (hx : orderOf x = 3) : x * x ∉ T := by
  intro hx2
  apply hv.not_mem_of_orderOf hx
  have h3 : x * x * x = 1 := by
    have := pow_orderOf_eq_one x
    rw [hx, pow_three'] at this
    exact this
  have : x = (x * x) * (x * x) := by
    calc x = x * (x * x * x) := by rw [h3, mul_one]
      _ = (x * x) * (x * x) := by group
  rw [this]
  exact T.mul_mem hx2 hx2

end Vertex

structure IsNaturalAt (H T : Subgroup D) (z : D) (V : Subgroup D) : Prop where
  z_mem : z ∈ centerOf T
  z_sq : z ^ 2 = 1
  z_ne : z ≠ 1
  V_eq : V = conjClosure (Subgroup.zpowers z) H
  not_normalizes : ¬ H ≤ Subgroup.normalizer (Subgroup.zpowers z : Set D)
  card_eq : Nat.card V = 4
  basis : ∃ a : D, a ≠ 1 ∧ a ≠ z ∧ (V : Set D) = {1, z, a, z * a}
  le_center : V ≤ centerOf (pCoreOf 2 H)
  reduced : IsTwoReducedIn H V
  natural : F112W.IsNaturalS3 H V
  centralizer_eq : H ⊓ Subgroup.centralizer (V : Set D) = pCoreOf 2 H
  cT : T ⊓ Subgroup.centralizer (V : Set D) =
    pCoreOf 2 (H ⊓ Subgroup.centralizer (V : Set D))


omit [Finite D] in
theorem zpow_eq_one_or_self {z : D} (hz : z ^ 2 = 1) (k : ℤ) : z ^ k = 1 ∨ z ^ k = z := by
  have hz' : z ^ (2 : ℤ) = 1 := by exact_mod_cast hz
  rcases Int.even_or_odd' k with ⟨m, rfl | rfl⟩
  · left
    rw [zpow_mul, hz', one_zpow]
  · right
    rw [zpow_add_one, zpow_mul, hz', one_zpow, one_mul]

omit [Finite D] in
theorem eq_of_conj_eq_of_conj_fixed {t w ω : D} (hω : t * ω * t⁻¹ = ω)
    (h : t * w * t⁻¹ = ω) : w = ω :=
  mul_left_cancel (mul_right_cancel (h.trans hω.symm))

omit [Finite D] in
theorem mul_eq_of_conj_eq {t z : D} (h : t * z * t⁻¹ = z) : t * z = z * t := by
  calc t * z = (t * z * t⁻¹) * t := by group
    _ = z * t := by rw [h]

omit [Finite D] in
theorem conj_mem_centralizer' {S : Subgroup D} {g c : D}
    (hg : g ∈ Subgroup.normalizer (S : Set D)) (hc : c ∈ Subgroup.centralizer (S : Set D)) :
    g * c * g⁻¹ ∈ Subgroup.centralizer (S : Set D) := by
  rw [Subgroup.mem_centralizer_iff] at hc ⊢
  intro s hs
  have hs' : g⁻¹ * s * g ∈ S := (Subgroup.mem_normalizer_iff''.mp hg s).mp hs
  have key := hc _ hs'
  calc s * (g * c * g⁻¹) = g * ((g⁻¹ * s * g) * c) * g⁻¹ := by group
    _ = g * (c * (g⁻¹ * s * g)) * g⁻¹ := by rw [key]
    _ = g * c * g⁻¹ * s := by group

omit [Finite D] in
theorem conj_mem_centerOf' {O : Subgroup D} {g c : D}
    (hg : g ∈ Subgroup.normalizer (O : Set D)) (hc : c ∈ centerOf O) :
    g * c * g⁻¹ ∈ centerOf O :=
  ⟨(Subgroup.mem_normalizer_iff.mp hg c).mp hc.1, conj_mem_centralizer' hg hc.2⟩

theorem exists_natural_data {H T : Subgroup D} (hv : Vertex H T) {ω : D} (hωZ : ω ∈ centerOf T)
    (hω2 : ω ^ 2 = 1) (hn : ∃ g ∈ H, g * ω * g⁻¹ ≠ ω) :
    ∃ (x z : D) (V : Subgroup D), x ∈ H ∧ x * x * x = 1 ∧ x * ω * x⁻¹ ≠ ω ∧
      z = (x * ω * x⁻¹) * (x * x * ω * (x * x)⁻¹) ∧ IsNaturalAt H T z V ∧
      z ∈ conjClosure (Subgroup.zpowers ω) H := by
  obtain ⟨x, hxH, hx3⟩ := hv.exists_order_three
  have hxT : x ∉ T := hv.not_mem_of_orderOf hx3
  have hx2T : x * x ∉ T := hv.sq_not_mem_of_orderOf hx3
  have hx3' : x * x * x = 1 := by
    have := pow_orderOf_eq_one x
    rwa [hx3, pow_three'] at this
  have hω2' : ω * ω = 1 := by rw [← pow_two]; exact hω2
  have hTH : T ≤ H := hv.T_le
  have hQT : pCoreOf 2 H ≤ T := hv.pCoreOf_le
  have hQN : H ≤ Subgroup.normalizer (pCoreOf 2 H : Set D) := le_normalizer_pCoreOf 2 H
  have hωc : ∀ t ∈ T, t * ω * t⁻¹ = ω := by
    intro t ht
    have h1 : t * ω = ω * t := Subgroup.mem_centralizer_iff.mp hωZ.2 t ht
    rw [h1]
    group
  have hconj : ∀ g ∈ H, g * ω * g⁻¹ = ω ∨ g * ω * g⁻¹ = x * ω * x⁻¹ ∨
      g * ω * g⁻¹ = x * x * ω * (x * x)⁻¹ := by
    intro g hg
    rcases coset_decomp hv.index_eq hxH hxT hx2T hg with h | ⟨t, ht, rfl⟩ | ⟨t, ht, rfl⟩
    · exact Or.inl (hωc g h)
    · right; left
      have := hωc t ht
      calc x * t * ω * (x * t)⁻¹ = x * (t * ω * t⁻¹) * x⁻¹ := by group
        _ = x * ω * x⁻¹ := by rw [this]
    · right; right
      have := hωc t ht
      calc x * x * t * ω * (x * x * t)⁻¹ = x * x * (t * ω * t⁻¹) * (x * x)⁻¹ := by group
        _ = x * x * ω * (x * x)⁻¹ := by rw [this]
  have hxω : x * ω * x⁻¹ ≠ ω := by
    intro hxc
    obtain ⟨g, hg, hgω⟩ := hn
    apply hgω
    rcases hconj g hg with h | h | h
    · exact h
    · rw [h, hxc]
    · rw [h]
      calc x * x * ω * (x * x)⁻¹ = x * (x * ω * x⁻¹) * x⁻¹ := by group
        _ = ω := by rw [hxc, hxc]
  obtain ⟨w₁, hw₁⟩ : ∃ w : D, w = x * ω * x⁻¹ := ⟨_, rfl⟩
  obtain ⟨w₂, hw₂⟩ : ∃ w : D, w = x * x * ω * (x * x)⁻¹ := ⟨_, rfl⟩
  have hx_w₁ : x * w₁ * x⁻¹ = w₂ := by rw [hw₁, hw₂]; group
  have hx_w₂ : x * w₂ * x⁻¹ = ω := by
    rw [hw₂]
    calc x * (x * x * ω * (x * x)⁻¹) * x⁻¹ = (x * x * x) * ω * (x * x * x)⁻¹ := by group
      _ = ω := by rw [hx3']; group
  have hωQ : ω ∈ centerOf (pCoreOf 2 H) :=
    ⟨hv.centerOf_le hωZ, Subgroup.centralizer_le hQT hωZ.2⟩
  have hw₁Q : w₁ ∈ centerOf (pCoreOf 2 H) := by
    rw [hw₁]; exact conj_mem_centerOf' (hQN hxH) hωQ
  have hw₂Q : w₂ ∈ centerOf (pCoreOf 2 H) := by
    rw [← hx_w₁]; exact conj_mem_centerOf' (hQN hxH) hw₁Q
  have hcomm : ∀ u ∈ centerOf (pCoreOf 2 H), ∀ v ∈ centerOf (pCoreOf 2 H), u * v = v * u :=
    fun u hu v hv' => Subgroup.mem_centralizer_iff.mp hv'.2 u hu.1
  have hw₁2 : w₁ * w₁ = 1 := by
    rw [← pow_two, hw₁, conj_pow, hω2]; group
  have hw₂2 : w₂ * w₂ = 1 := by
    rw [← pow_two, hw₂, conj_pow, hω2]; group
  have hne01 : ω ≠ w₁ := fun h => hxω (by rw [← hw₁]; exact h.symm)
  have hne02 : ω ≠ w₂ := by
    intro h
    apply hxω
    calc x * ω * x⁻¹ = x * w₂ * x⁻¹ := by rw [← h]
      _ = ω := hx_w₂
  have hne12 : w₁ ≠ w₂ := by
    intro h
    apply hne01
    calc ω = x * w₂ * x⁻¹ := hx_w₂.symm
      _ = x * w₁ * x⁻¹ := by rw [h]
      _ = w₂ := hx_w₁
      _ = w₁ := h.symm
  have hT₁ : ∀ t ∈ T, t * w₁ * t⁻¹ = w₁ ∨ t * w₁ * t⁻¹ = w₂ := by
    intro t ht
    have h1 : t * w₁ * t⁻¹ = t * x * ω * (t * x)⁻¹ := by rw [hw₁]; group
    rcases hconj (t * x) (H.mul_mem (hTH ht) hxH) with h | h | h
    · exact absurd (eq_of_conj_eq_of_conj_fixed (hωc t ht) (h1.trans h)).symm hne01
    · left; rw [h1, h, hw₁]
    · right; rw [h1, h, hw₂]
  have hT₂ : ∀ t ∈ T, t * w₂ * t⁻¹ = w₁ ∨ t * w₂ * t⁻¹ = w₂ := by
    intro t ht
    have h1 : t * w₂ * t⁻¹ = t * (x * x) * ω * (t * (x * x))⁻¹ := by rw [hw₂]; group
    rcases hconj (t * (x * x)) (H.mul_mem (hTH ht) (H.mul_mem hxH hxH)) with h | h | h
    · exact absurd (eq_of_conj_eq_of_conj_fixed (hωc t ht) (h1.trans h)).symm hne02
    · left; rw [h1, h, hw₁]
    · right; rw [h1, h, hw₂]
  obtain ⟨z, hz⟩ : ∃ z : D, z = w₁ * w₂ := ⟨_, rfl⟩
  have hzQ : z ∈ centerOf (pCoreOf 2 H) := by
    rw [hz]; exact (centerOf (pCoreOf 2 H)).mul_mem hw₁Q hw₂Q
  have hzc : ∀ t ∈ T, t * z * t⁻¹ = z := by
    intro t ht
    have hinj : t * w₁ * t⁻¹ ≠ t * w₂ * t⁻¹ := fun h =>
      hne12 (mul_left_cancel (mul_right_cancel h))
    have hexp : t * z * t⁻¹ = (t * w₁ * t⁻¹) * (t * w₂ * t⁻¹) := by rw [hz]; group
    rw [hexp]
    rcases hT₁ t ht with h1 | h1 <;> rcases hT₂ t ht with h2 | h2
    · exact absurd (h1.trans h2.symm) hinj
    · rw [h1, h2, hz]
    · rw [h1, h2, hz]; exact hcomm w₂ hw₂Q w₁ hw₁Q
    · exact absurd (h1.trans h2.symm) hinj
  have hzZ : z ∈ centerOf T :=
    ⟨hQT hzQ.1, Subgroup.mem_centralizer_iff.mpr fun t ht => mul_eq_of_conj_eq (hzc t ht)⟩
  have hz2 : z * z = 1 := by
    rw [hz]
    calc w₁ * w₂ * (w₁ * w₂) = w₁ * (w₂ * w₁) * w₂ := by group
      _ = w₁ * (w₁ * w₂) * w₂ := by rw [hcomm w₂ hw₂Q w₁ hw₁Q]
      _ = (w₁ * w₁) * (w₂ * w₂) := by group
      _ = 1 := by rw [hw₁2, hw₂2, one_mul]
  have hz1 : z ≠ 1 := by
    intro h
    apply hne12
    have h' : w₁ * w₂ = w₁ * w₁ := by rw [← hz, h, hw₁2]
    exact (mul_left_cancel h').symm
  obtain ⟨z₁, hz₁⟩ : ∃ z₁ : D, z₁ = w₂ * ω := ⟨_, rfl⟩
  have hz₁Q : z₁ ∈ centerOf (pCoreOf 2 H) := by
    rw [hz₁]; exact (centerOf (pCoreOf 2 H)).mul_mem hw₂Q hωQ
  have hxz : x * z * x⁻¹ = z₁ := by
    rw [hz, hz₁]
    calc x * (w₁ * w₂) * x⁻¹ = (x * w₁ * x⁻¹) * (x * w₂ * x⁻¹) := by group
      _ = w₂ * ω := by rw [hx_w₁, hx_w₂]
  have hz₁2 : z₁ * z₁ = 1 := by
    rw [hz₁]
    calc w₂ * ω * (w₂ * ω) = w₂ * (ω * w₂) * ω := by group
      _ = w₂ * (w₂ * ω) * ω := by rw [hcomm ω hωQ w₂ hw₂Q]
      _ = (w₂ * w₂) * (ω * ω) := by group
      _ = 1 := by rw [hw₂2, hω2', one_mul]
  have hz₁1 : z₁ ≠ 1 := by
    intro h
    apply hne02
    have h' : w₂ * ω = ω * ω := by rw [← hz₁, h, hω2']
    exact (mul_right_cancel h').symm
  have hzz₁ : z ≠ z₁ := by
    intro h
    apply hne01
    have h' : w₁ * w₂ = ω * w₂ := by
      rw [← hz, h, hz₁]; exact hcomm w₂ hw₂Q ω hωQ
    exact (mul_right_cancel h').symm
  have hxz₁ : x * z₁ * x⁻¹ = z * z₁ := by
    have h1 : x * z₁ * x⁻¹ = ω * w₁ := by
      rw [hz₁]
      calc x * (w₂ * ω) * x⁻¹ = (x * w₂ * x⁻¹) * (x * ω * x⁻¹) := by group
        _ = ω * w₁ := by rw [hx_w₂, hw₁]
    have h2 : z * z₁ = ω * w₁ := by
      rw [hz, hz₁]
      calc w₁ * w₂ * (w₂ * ω) = w₁ * (w₂ * w₂) * ω := by group
        _ = w₁ * ω := by rw [hw₂2, mul_one]
        _ = ω * w₁ := hcomm w₁ hw₁Q ω hωQ
    rw [h1, h2]
  have hz2' : z ^ 2 = 1 := by rw [pow_two]; exact hz2
  obtain ⟨K, hKset, hKcard⟩ := exists_klein_four hz2' (by rw [pow_two]; exact hz₁2)
    (hcomm z hzQ z₁ hz₁Q) hz1 hz₁1 hzz₁
  have hzK : z ∈ K := by
    have : z ∈ (K : Set D) := by rw [hKset]; simp
    exact this
  have hz₁K : z₁ ∈ K := by
    have : z₁ ∈ (K : Set D) := by rw [hKset]; simp
    exact this
  have hz_cl : ∀ g ∈ H, g * z * g⁻¹ ∈ K := by
    intro g hg
    rcases coset_decomp hv.index_eq hxH hxT hx2T hg with h | ⟨t, ht, rfl⟩ | ⟨t, ht, rfl⟩
    · rw [hzc g h]; exact hzK
    · have : x * t * z * (x * t)⁻¹ = z₁ := by
        calc x * t * z * (x * t)⁻¹ = x * (t * z * t⁻¹) * x⁻¹ := by group
          _ = z₁ := by rw [hzc t ht, hxz]
      rw [this]; exact hz₁K
    · have : x * x * t * z * (x * x * t)⁻¹ = z * z₁ := by
        calc x * x * t * z * (x * x * t)⁻¹ = x * (x * (t * z * t⁻¹) * x⁻¹) * x⁻¹ := by group
          _ = z * z₁ := by rw [hzc t ht, hxz, hxz₁]
      rw [this]; exact K.mul_mem hzK hz₁K
  have hVK : conjClosure (Subgroup.zpowers z) H = K := by
    apply le_antisymm
    · refine conjClosure_le fun g hg y hy => ?_
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
      rcases zpow_eq_one_or_self hz2' k with h | h
      · rw [h]; simp
      · rw [h]; exact hz_cl g hg
    · intro y hy
      have hy' : y ∈ ({1, z, z₁, z * z₁} : Set D) := by rw [← hKset]; exact hy
      have hzC : z ∈ conjClosure (Subgroup.zpowers z) H :=
        le_conjClosure _ _ (Subgroup.mem_zpowers z)
      have hz₁C : z₁ ∈ conjClosure (Subgroup.zpowers z) H := by
        rw [← hxz]; exact mem_conjClosure hxH (Subgroup.mem_zpowers z)
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy'
      rcases hy' with h | h | h | h
      · rw [h]; exact Subgroup.one_mem _
      · rw [h]; exact hzC
      · rw [h]; exact hz₁C
      · rw [h]; exact Subgroup.mul_mem _ hzC hz₁C
  have hcard : Nat.card (conjClosure (Subgroup.zpowers z) H) = 4 := by
    rw [hVK]; exact hKcard
  have hZle : Subgroup.zpowers z ≤ quasithinOmegaOneCenter T :=
    Subgroup.zpowers_le.mpr (mem_omega hzZ hz2')
  have hodd : ¬ 2 ∣ T.relIndex H := hv.sylow.2.2
  obtain ⟨hVle, -⟩ := conjClosure_le_centerOf_pCoreOf_of_sylowIn hTH hv.isPGroup hodd
    hv.charTwo hZle
  have hred := isTwoReducedIn_conjClosure_of_sylowIn hTH hv.isPGroup hodd hv.charTwo hZle
  have hnorm : ¬ H ≤ Subgroup.normalizer (Subgroup.zpowers z : Set D) := by
    intro hHN
    have h1 := (Subgroup.mem_normalizer_iff.mp (hHN hxH) z).mp (Subgroup.mem_zpowers z)
    rw [hxz] at h1
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp h1
    rcases zpow_eq_one_or_self hz2' k with h | h
    · exact hz₁1 (hk.symm.trans h)
    · exact hzz₁ (h.symm.trans hk)
  have hQcent : pCoreOf 2 H ≤
      Subgroup.centralizer ((conjClosure (Subgroup.zpowers z) H : Subgroup D) : Set D) :=
    fun q hq => Subgroup.mem_centralizer_iff.mpr fun v hv' =>
      (Subgroup.mem_centralizer_iff.mp (hVle hv').2 q hq).symm
  have hTcent : T ≤ Subgroup.centralizer (Subgroup.zpowers z : Set D) :=
    Subgroup.le_centralizer_iff.mp (Subgroup.zpowers_le.mpr hzZ.2)
  have hTN : T ≤ Subgroup.normalizer (Subgroup.zpowers z : Set D) :=
    hTcent.trans (Subgroup.centralizer_le_normalizer _)
  have hCV : H ⊓ Subgroup.centralizer
      ((conjClosure (Subgroup.zpowers z) H : Subgroup D) : Set D) ≤ pCoreOf 2 H :=
    F112W.centralizer_conjClosure_le_pCoreOf hv.quotient hv.sylow hTN (hQT.trans hTcent) hnorm
  have hcentEq : H ⊓ Subgroup.centralizer
      ((conjClosure (Subgroup.zpowers z) H : Subgroup D) : Set D) = pCoreOf 2 H :=
    le_antisymm hCV (le_inf (pCoreOf_le 2 H) hQcent)
  have hw₁C : w₁ ∈ conjClosure (Subgroup.zpowers ω) H := by
    rw [hw₁]; exact mem_conjClosure hxH (Subgroup.mem_zpowers ω)
  have hw₂C : w₂ ∈ conjClosure (Subgroup.zpowers ω) H := by
    rw [hw₂]; exact mem_conjClosure (H.mul_mem hxH hxH) (Subgroup.mem_zpowers ω)
  refine ⟨x, z, conjClosure (Subgroup.zpowers z) H, hxH, hx3', hxω, by rw [hz, hw₁, hw₂],
    ⟨hzZ, hz2', hz1, rfl, hnorm, hcard,
    ⟨z₁, hz₁1, hzz₁.symm, by rw [hVK]; exact hKset⟩, hVle, hred,
    ⟨hcard, ?_⟩, hcentEq, ?_⟩, by rw [hz]; exact Subgroup.mul_mem _ hw₁C hw₂C⟩
  · rw [hcentEq]; exact hv.relIndex_pCoreOf
  · rw [hcentEq, pCoreOf_eq_self_of_isPGroup (pCoreOf_isPGroup 2 H)]
    exact le_antisymm ((inf_le_inf_right _ hTH).trans hcentEq.le) (le_inf hQT hQcent)

theorem exists_natural {H T : Subgroup D} (hv : Vertex H T) {ω : D} (hωZ : ω ∈ centerOf T)
    (hω2 : ω ^ 2 = 1) (hn : ∃ g ∈ H, g * ω * g⁻¹ ≠ ω) :
    ∃ z V, IsNaturalAt H T z V ∧ z ∈ conjClosure (Subgroup.zpowers ω) H := by
  obtain ⟨-, z, V, -, -, -, -, hn', hz⟩ := exists_natural_data hv hωZ hω2 hn
  exact ⟨z, V, hn', hz⟩

end GoldAmL

end F6

end CFSG.Quasithin
