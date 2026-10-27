module

public import CFSG.Quasithin.H13.GoldschmidtU43BStruct
public import CFSG.Quasithin.H13.GoldschmidtU43BCard

public section

namespace CFSG.Quasithin.H13.U43

open CFSG.Quasithin CFSG.Open CFSG.Quasithin.H13.A6

variable {G : Type} [Group G]

theorem exists_mul_of_card {K : Type} [Group K] [Finite K] (N₁ N₂ : Subgroup K) [N₁.Normal]
    (h1 : Nat.card ↥N₁ = 16) (h2 : Nat.card ↥N₂ = 16) (h12 : Nat.card ↥(N₁ ⊓ N₂) = 4)
    (hK : Nat.card K = 64) (b : K) : ∃ n₁ ∈ N₁, ∃ n₂ ∈ N₂, n₁ * n₂ = b := by
  have e1 : N₁.relIndex N₂ * Nat.card ↥(N₁ ⊓ N₂) = Nat.card ↥N₂ :=
    Subgroup.relIndex_mul_card N₁ N₂
  have e2 : N₁.relIndex (N₁ ⊔ N₂) = N₁.relIndex N₂ := Subgroup.relIndex_sup_left N₂ N₁
  have e3 : N₁.relIndex (N₁ ⊔ N₂) * Nat.card ↥(N₁ ⊓ (N₁ ⊔ N₂)) = Nat.card ↥(N₁ ⊔ N₂) :=
    Subgroup.relIndex_mul_card N₁ (N₁ ⊔ N₂)
  rw [inf_of_le_left le_sup_left, h1, e2] at e3
  rw [h12, h2] at e1
  have hsup : N₁ ⊔ N₂ = ⊤ := by
    apply Subgroup.eq_top_of_card_eq
    rw [← e3, hK]
    omega
  have hb : b ∈ N₁ ⊔ N₂ := hsup ▸ Subgroup.mem_top b
  exact Subgroup.mem_sup_of_normal_left.mp hb

namespace Swap

variable {z t w : G}

theorem card_N1 [Finite G] (d : Swap z t w) : Nat.card ↥(N1g z t) = 16 := by
  classical
  have h := d.hyp
  have hne := h.t_ne_zt (t := t)
  have hΩ : ∀ g ∈ Uz z, ∀ y ∈ ({t, z * t} : Set G), g * y * g⁻¹ ∈ ({t, z * t} : Set G) := by
    intro g hg y hy
    have hgz : g * z * g⁻¹ = z := by
      have := h.z_comm hg
      calc g * z * g⁻¹ = (z * g) * g⁻¹ := by rw [← this]
        _ = z := by group
    have hgt : g * t * g⁻¹ = t ∨ g * t * g⁻¹ = z * t := by
      have := h.comm_eq ⟨g, hg⟩ ⟨t, d.ht.1⟩
      rcases zmod_two_cases (bq (Multiplicative.toAdd (h.θ ⟨g, hg⟩))
          (Multiplicative.toAdd (h.θ ⟨t, d.ht.1⟩))) with e | e
      · left
        rw [e, zp_zero] at this
        calc g * t * g⁻¹ = (g * t * g⁻¹ * t⁻¹) * t := by group
          _ = t := by rw [this]; group
      · right
        rw [e, zp_one] at this
        calc g * t * g⁻¹ = (g * t * g⁻¹ * t⁻¹) * t := by group
          _ = z * t := by rw [this]
    have hgzt : g * (z * t) * g⁻¹ = z * (g * t * g⁻¹) := by
      calc g * (z * t) * g⁻¹ = (g * z * g⁻¹) * (g * t * g⁻¹) := by group
        _ = z * (g * t * g⁻¹) := by rw [hgz]
    rcases hy with rfl | rfl
    · exact hgt
    · rw [hgzt]
      rcases hgt with e | e
      · rw [e]; exact Or.inr rfl
      · rw [e, ← mul_assoc, h.sq_z, one_mul]; exact Or.inl rfl
  have htr : ∀ y ∈ ({t, z * t} : Set G), ∃ g ∈ Uz z, g * t * g⁻¹ = y := by
    intro y hy
    rcases hy with rfl | rfl
    · exact ⟨1, one_mem _, by group⟩
    · obtain ⟨u, hu, hu'⟩ := h.exists_comm_eq_z d.ht.1 d.ht.2.2.1 d.ht.2.2.2
      refine ⟨u, hu, ?_⟩
      calc u * t * u⁻¹ = (u * t * u⁻¹ * t⁻¹) * t := by group
        _ = z * t := by rw [hu']
  have := card_eq_ncard_mul_card_inf_centralizer (Uz z) {t, z * t} t hΩ (by simp) htr
  rw [Set.ncard_pair hne, h.card_U] at this
  change Nat.card ↥(Uz z ⊓ Subgroup.centralizer ({t} : Set G)) = 16
  omega

theorem card_N2 [Finite G] (d : Swap z t w) : Nat.card ↥(N2g z t w) = 16 := by
  rw [card_conj, d.card_N1]

theorem N1_inf_N2 (d : Swap z t w) : N1g z t ⊓ N2g z t w = Vg z t :=
  Subgroup.ext fun x => d.mem_N1_inf_N2 x

theorem card_Vg [Finite G] (d : Swap z t w) : Nat.card ↥(Vg z t) = 4 := by
  classical
  have hp := d.cm
  have h1 := d.hyp.z_ne_one
  have ht1 := d.ht.2.2.1
  have hzt := d.ht.2.2.2
  have hne := d.hyp.t_ne_zt (t := t)
  have hset : (Vg z t : Set G) = {1, z, t, z * t} := by
    ext x
    rw [SetLike.mem_coe, hp.mem_Vg_iff₄]
    simp
  rw [show Nat.card ↥(Vg z t) = Set.ncard (Vg z t : Set G) from Nat.card_coe_set_eq _, hset]
  have hz1 : z ≠ 1 := h1
  have ht' : t ≠ z := hzt
  have h4 : z * t ≠ 1 := fun e => hzt (by
    calc t = z⁻¹ * (z * t) := by group
      _ = z⁻¹ := by rw [e, mul_one]
      _ = z := inv_eq_of_mul_eq_one_right d.hyp.sq_z)
  have h5 : z * t ≠ z := fun e => ht1 (by
    calc t = z⁻¹ * (z * t) := by group
      _ = z⁻¹ * z := by rw [e]
      _ = 1 := by group)
  have h6 : z * t ≠ t := fun e => h1 (by
    calc z = (z * t) * t⁻¹ := by group
      _ = t * t⁻¹ := by rw [e]
      _ = 1 := by group)
  have s1 : (1 : G) ∉ ({z, t, z * t} : Set G) := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨hz1.symm, ht1.symm, h4.symm⟩
  have s2 : z ∉ ({t, z * t} : Set G) := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨ht'.symm, h5.symm⟩
  rw [Set.ncard_insert_of_notMem s1, Set.ncard_insert_of_notMem s2, Set.ncard_pair hne]

theorem exists_mul [Finite G] (d : Swap z t w) {b : G} (hb : b ∈ Bg z t) :
    ∃ n₁ ∈ N1g z t, ∃ n₂ ∈ N2g z t w, n₁ * n₂ = b := by
  classical
  let M₁ : Subgroup ↥(Bg z t) := (N1g z t).subgroupOf (Bg z t)
  let M₂ : Subgroup ↥(Bg z t) := (N2g z t w).subgroupOf (Bg z t)
  have : M₁.Normal := ⟨fun n hn g => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    simpa using N1_normal g.2 hn⟩
  have h1 : Nat.card ↥M₁ = 16 := by
    rw [← d.card_N1]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe N1_le_B).toEquiv
  have h2 : Nat.card ↥M₂ = 16 := by
    rw [← d.card_N2]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe d.N2_le_B).toEquiv
  have h12 : Nat.card ↥(M₁ ⊓ M₂) = 4 := by
    have hle : N1g z t ⊓ N2g z t w ≤ Bg z t := inf_le_left.trans N1_le_B
    have heq : (N1g z t ⊓ N2g z t w).subgroupOf (Bg z t) = M₁ ⊓ M₂ := by
      ext x
      simp [M₁, M₂, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    rw [← heq, ← d.card_Vg, ← d.N1_inf_N2]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv
  have hB : Nat.card ↥(Bg z t) = 64 := d.hyp.card_centralizer_S d.ht
  obtain ⟨n₁, hn₁, n₂, hn₂, h⟩ := exists_mul_of_card M₁ M₂ h1 h2 h12 hB ⟨b, hb⟩
  refine ⟨n₁, Subgroup.mem_subgroupOf.mp hn₁, n₂, Subgroup.mem_subgroupOf.mp hn₂, ?_⟩
  have := congrArg Subtype.val h
  simpa using this

theorem V_central (d : Swap z t w) {b v : G} (hb : b ∈ Bg z t) (hv : v ∈ Vg z t) :
    b * v = v * b := by
  obtain ⟨a, c, rfl⟩ := (d.cm.mem_Vg_iff v).1 hv
  have hz : ∀ a : ZMod 2, b * zp z a = zp z a * b := by
    intro a
    rcases zmod_two_cases a with rfl | rfl
    · simp [zp_zero]
    · rw [zp_one]; exact Subgroup.mem_centralizer_singleton_iff.mp hb.1
  have ht : ∀ a : ZMod 2, b * zp t a = zp t a * b := by
    intro a
    rcases zmod_two_cases a with rfl | rfl
    · simp [zp_zero]
    · rw [zp_one]; exact Subgroup.mem_centralizer_singleton_iff.mp hb.2
  calc b * (zp z a * zp t c) = (b * zp z a) * zp t c := by group
    _ = (zp z a * b) * zp t c := by rw [hz a]
    _ = zp z a * (b * zp t c) := by group
    _ = zp z a * (zp t c * b) := by rw [ht c]
    _ = zp z a * zp t c * b := by group

theorem zp_z_mem (z t : G) (a : ZMod 2) : zp z a ∈ Vg z t := by
  rcases zmod_two_cases a with rfl | rfl
  · rw [zp_zero]; exact one_mem _
  · rw [zp_one]; exact z_mem_Vg z t

theorem sq_N1_mem_V (d : Swap z t w) {n : G} (hn : n ∈ N1g z t) : n * n ∈ Vg z t := by
  have := d.hyp.sq_eq ⟨n, hn.1⟩
  rw [pow_two] at this
  have e : n * n = _ := this
  rw [e]
  exact zp_z_mem z t _

theorem sq_N2_mem_V (d : Swap z t w) {n : G} (hn : n ∈ N2g z t w) : n * n ∈ Vg z t := by
  have h1 := d.sq_N1_mem_V ((mem_N2 n).1 hn)
  have h2 : (w⁻¹) * (w * n * w⁻¹ * (w * n * w⁻¹)) * (w⁻¹)⁻¹ ∈ Vg z t :=
    d.cm.conj_mem_of_mem (g := w⁻¹) (by simpa using (d.w1 ▸ t_mem_Vg z t))
      (by simpa using (d.w2 ▸ z_mem_Vg z t)) h1
  have e : (w⁻¹) * (w * n * w⁻¹ * (w * n * w⁻¹)) * (w⁻¹)⁻¹ = n * n := by group
  rwa [e] at h2

theorem sq_mem_V [Finite G] (d : Swap z t w) {b : G} (hb : b ∈ Bg z t) : b * b ∈ Vg z t := by
  obtain ⟨n₁, hn₁, n₂, hn₂, rfl⟩ := d.exists_mul hb
  have hn₂B : n₂ ∈ Bg z t := d.N2_le_B hn₂
  have hn₁B : n₁⁻¹ ∈ Bg z t := (Bg z t).inv_mem (N1_le_B hn₁)
  have hc1 : n₁⁻¹ * (n₂ * n₁ * n₂⁻¹) ∈ N1g z t :=
    mul_mem ((N1g z t).inv_mem hn₁) (N1_normal hn₂B hn₁)
  have hc2 : n₁⁻¹ * (n₂ * n₁ * n₂⁻¹) ∈ N2g z t w := by
    have := d.N2_normal hn₁B hn₂
    have e : n₁⁻¹ * (n₂ * n₁ * n₂⁻¹) = (n₁⁻¹ * n₂ * n₁⁻¹⁻¹) * n₂⁻¹ := by group
    rw [e]
    exact mul_mem this ((N2g z t w).inv_mem hn₂)
  have hc : n₁⁻¹ * (n₂ * n₁ * n₂⁻¹) ∈ Vg z t := (d.mem_N1_inf_N2 _).1 ⟨hc1, hc2⟩
  have e : n₁ * n₂ * (n₁ * n₂) = (n₁ * n₁) * (n₁⁻¹ * (n₂ * n₁ * n₂⁻¹)) * (n₂ * n₂) := by group
  rw [e]
  exact mul_mem (mul_mem (d.sq_N1_mem_V hn₁) hc) (d.sq_N2_mem_V hn₂)

theorem comm_mem_V [Finite G] (d : Swap z t w) {b b' : G} (hb : b ∈ Bg z t) (hb' : b' ∈ Bg z t) :
    b * b' * b⁻¹ * b'⁻¹ ∈ Vg z t := by
  have h1 := d.sq_mem_V (mul_mem hb hb')
  have h2 := d.sq_mem_V hb
  have h3 := d.sq_mem_V hb'
  have hc : b' * (b * b) = (b * b) * b' := d.V_central hb' h2
  have hc' : b' * (b * b)⁻¹ = (b * b)⁻¹ * b' := (Commute.inv_right hc : Commute b' (b * b)⁻¹)
  have e : b * b' * b⁻¹ * b'⁻¹ = ((b * b') * (b * b')) * (b * b)⁻¹ * (b' * b')⁻¹ := by
    calc b * b' * b⁻¹ * b'⁻¹
        = b * b' * b * ((b * b)⁻¹ * b') * (b' * b')⁻¹ := by group
      _ = b * b' * b * (b' * (b * b)⁻¹) * (b' * b')⁻¹ := by rw [hc']
      _ = ((b * b') * (b * b')) * (b * b)⁻¹ * (b' * b')⁻¹ := by group
  rw [e]
  exact mul_mem (mul_mem h1 ((Vg z t).inv_mem h2)) ((Vg z t).inv_mem h3)

end Swap

end CFSG.Quasithin.H13.U43
