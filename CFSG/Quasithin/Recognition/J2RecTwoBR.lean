module

public import CFSG.Quasithin.Recognition.J2RecTwoBCent

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique Equiv CFSG.LieType.BorelTits J2Cz J2Cz.QM

structure J2A5Config {G : Type} [Group G] (z : G) (A R : Subgroup G) (y : G) : Prop where
  equiv : Nonempty (↥A ≃* alternatingGroup (Fin 5))
  z_mem : z ∈ A
  le_centralizer : R ≤ Subgroup.centralizer (A : Set G)
  card : Nat.card R = 4
  mul_self : ∀ r ∈ R, r * r = 1
  not_isConj : ∀ r ∈ R, r ≠ 1 → ¬ IsConj z r
  y_mem : y ∈ Subgroup.centralizer (A : Set G)
  y_normalizes : y ∈ Subgroup.normalizer (R : Set G)
  y_not_mem : y ∉ Subgroup.centralizer (R : Set G)

namespace J2Frame

variable {G : Type} [Group G] {z : G} (F : J2Frame G z)

theorem pt_four_ne_one : F.pt 4 ≠ 1 := fun h1 =>
  x_ne_one 4 (F.emb_injective (h1.trans (map_one F.emb).symm))

theorem pt_four_ne_z : F.pt 4 ≠ z := fun h1 =>
  x_ne_z 4 (F.emb_injective (h1.trans F.emb_z.symm))

theorem card_W : Nat.card F.W = 4 := by
  classical
  have hz1 : z ≠ 1 := F.isTypeH2.ne_one
  have hzz : z * z = 1 := F.mul_self_of_mem_W F.z_mem_W
  have hx1 := F.pt_four_ne_one
  have hxz := F.pt_four_ne_z
  have hzx1 : z * F.pt 4 ≠ 1 := fun h1 => hxz (by
    calc F.pt 4 = z * (z * F.pt 4) := by rw [← mul_assoc, hzz, one_mul]
      _ = z := by rw [h1, mul_one])
  have hzxz : z * F.pt 4 ≠ z := fun h1 => hx1 (by
    calc F.pt 4 = z * (z * F.pt 4) := by rw [← mul_assoc, hzz, one_mul]
      _ = 1 := by rw [h1, hzz])
  have hzxx : z * F.pt 4 ≠ F.pt 4 := fun h1 => hz1 (by
    calc z = z * F.pt 4 * (F.pt 4)⁻¹ := by group
      _ = 1 := by rw [h1, mul_inv_cancel])
  have hset : (F.W : Set G) = ↑({1, z, F.pt 4, z * F.pt 4} : Finset G) := by
    ext w
    simp only [SetLike.mem_coe, Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff]
    exact F.mem_W
  have h4 : (F.W : Set G).ncard = 4 := by
    rw [hset, Set.ncard_coe_finset, Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
      Finset.card_pair hzxx.symm]
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨hxz.symm, hzxz.symm⟩
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨hz1.symm, hx1.symm, hzx1.symm⟩
  rw [← Nat.card_coe_set_eq] at h4
  exact h4

theorem card_T_le : Nat.card F.T ≤ 16 := by
  classical
  set l : Fin 4 → G := ![1, F.t, F.a, F.t * F.a] with hl
  set w : Fin 4 → G := ![1, z, F.pt 4, z * F.pt 4] with hw
  have key : ∀ s : ↥F.T, ∃ p : Fin 4 × Fin 4, (s : G) = l p.1 * w p.2 := by
    intro s
    obtain ⟨l', hl', w', hw', hs⟩ := F.exists_eq_mul_of_mem_T s.2
    obtain ⟨i, hi⟩ : ∃ i, l' = l i := by
      rcases hl' with h1 | h1 | h1 | h1
      exacts [⟨0, h1⟩, ⟨1, h1⟩, ⟨2, h1⟩, ⟨3, h1⟩]
    obtain ⟨j, hj⟩ : ∃ j, w' = w j := by
      rcases F.mem_W.mp hw' with h1 | h1 | h1 | h1
      exacts [⟨0, h1⟩, ⟨1, h1⟩, ⟨2, h1⟩, ⟨3, h1⟩]
    exact ⟨(i, j), by rw [hs, hi, hj]⟩
  choose p hp using key
  have hinj : Function.Injective p := fun s s' h1 => Subtype.ext (by rw [hp s, hp s', h1])
  have h1 := Nat.card_le_card_of_injective p hinj
  rwa [Nat.card_prod, Nat.card_fin] at h1

end J2Frame

namespace J2A5Config

variable {G : Type} [Group G] {z : G} {A R : Subgroup G} {y : G} (c : J2A5Config z A R y)
include c

theorem comm_A {r a : G} (hr : r ∈ R) (ha : a ∈ A) : r * a = a * r :=
  ((Subgroup.mem_centralizer_iff.mp (c.le_centralizer hr)) a ha).symm

theorem mem_centralizer_z {r : G} (hr : r ∈ R) : r ∈ Subgroup.centralizer ({z} : Set G) :=
  Subgroup.mem_centralizer_singleton_iff.mpr (c.comm_A hr c.z_mem)

theorem comm_R {r r' : G} (hr : r ∈ R) (hr' : r' ∈ R) : r * r' = r' * r := by
  have h1 := c.mul_self _ (R.mul_mem hr hr')
  have h2 := c.mul_self r hr
  have h3 := c.mul_self r' hr'
  calc r * r' = r * r' * (r' * r * (r' * r)) := by rw [c.mul_self _ (R.mul_mem hr' hr), mul_one]
    _ = r * (r' * r') * r * (r' * r) := by group
    _ = r' * r := by rw [h3, mul_one, h2, one_mul]

theorem not_mem_pCoreOf (h : IsTypeH2 G z) {r : G} (hr : r ∈ R) (hr1 : r ≠ 1) :
    r ∉ pCoreOf 2 (Subgroup.centralizer ({z} : Set G)) := fun hQ =>
  c.not_isConj r hr hr1 (h.isConj_of_mem_pCoreOf hQ (c.mul_self r hr) hr1)

theorem card_A : Nat.card A = 60 := by
  obtain ⟨e⟩ := c.equiv
  rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_fin]
  rfl

variable [Finite G]

theorem exists_mul_eq_of_mem_centralizer (h : IsTypeH2 G z)
    (hcount : involutionClassCount G = 2) {t : G} (htR : t ∈ R) (ht1 : t ≠ 1) {g : G}
    (hg : g ∈ Subgroup.centralizer ({t} : Set G)) : ∃ r ∈ R, ∃ a ∈ A, g = r * a := by
  obtain ⟨e⟩ := c.equiv
  have htH := c.mem_centralizer_z htR
  have ht2 := c.mul_self t htR
  have htQ := c.not_mem_pCoreOf h htR ht1
  obtain ⟨L, hLC, hLQ, hL⟩ := h.exists_complement_of_involution htH ht2 htQ
  obtain ⟨F, rfl⟩ := J2Frame.exists_frame h hLC hLQ hL
  obtain ⟨k, hkH, hk⟩ := F.exists_conj_eq_t htH ht2 htQ
  have hconjX : ∀ {u : G}, u * t = t * u → k * u * k⁻¹ ∈ F.X := fun {u} hu => by
    rw [F.mem_X, ← hk]
    calc k * u * k⁻¹ * (k * t * k⁻¹) = k * (u * t) * k⁻¹ := by group
      _ = k * (t * u) * k⁻¹ := by rw [hu]
      _ = k * t * k⁻¹ * (k * u * k⁻¹) := by group
  have hAX : ∀ a ∈ A, k * a * k⁻¹ ∈ F.X := fun a ha => hconjX (c.comm_A htR ha).symm
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hsimp : IsSimpleGroup ↥A := e.isSimpleGroup_congr.mpr inferInstance
  set N : Subgroup ↥A := ((F.M hcount).comap (MulAut.conj k).toMonoidHom).subgroupOf A with hN
  have hmemN : ∀ a (ha : a ∈ A), (⟨a, ha⟩ : ↥A) ∈ N ↔ k * a * k⁻¹ ∈ F.M hcount := fun a ha => by
    rw [hN, Subgroup.mem_subgroupOf, Subgroup.mem_comap]
    rfl
  have hoddN : ∀ (a : ↥A) (n : ℕ), Odd n → (a : G) ^ n = 1 → a ∈ N := fun a n hn han => by
    rw [hmemN a a.2]
    refine F.mem_M_of_pow_eq_one hcount (hAX a a.2) hn ?_
    rw [conj_pow, han, mul_one, mul_inv_cancel]
  have hordA : ∀ (σ : alternatingGroup (Fin 5)) (p : ℕ), p.Prime →
      (σ : Perm (Fin 5)) ^ p = 1 → (σ : Perm (Fin 5)) ≠ 1 →
      orderOf (e.symm σ) = p ∧ ((e.symm σ : ↥A) : G) ^ p = 1 := fun σ p hp hσp hσ1 => by
    have : Fact p.Prime := ⟨hp⟩
    have h1 : orderOf σ = p := orderOf_eq_prime (Subtype.ext (by simpa using hσp))
      (fun h2 => hσ1 (congrArg Subtype.val h2))
    have h2 : orderOf (e.symm σ) = p := by rw [MulEquiv.orderOf_eq, h1]
    refine ⟨h2, ?_⟩
    have h3 : (e.symm σ) ^ p = 1 := by rw [← h2]; exact pow_orderOf_eq_one _
    simpa using congrArg Subtype.val h3
  obtain ⟨ho3, hp3⟩ := hordA ⟨pb, pb_mem⟩ 3 Nat.prime_three (by rw [pow_three, ← mul_assoc]; exact pb_cube)
    pb_ne_one
  obtain ⟨ho5, hp5⟩ := hordA ⟨pa * pb, mul_mem pa_mem pb_mem⟩ 5 (by norm_num) papb_pow_five
    papb_ne_one
  have h3N : 3 ∣ Nat.card N := by
    have h1 := Subgroup.orderOf_dvd_natCard N (hoddN _ 3 ⟨1, rfl⟩ hp3)
    rwa [ho3] at h1
  have h5N : 5 ∣ Nat.card N := by
    have h1 := Subgroup.orderOf_dvd_natCard N (hoddN _ 5 ⟨2, rfl⟩ hp5)
    rwa [ho5] at h1
  have hNtop : N = ⊤ := subgroup_eq_top_of_fifteen_dvd c.card_A
    (Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num : Nat.Coprime 3 5) h3N h5N)
  have hAM : ∀ a ∈ A, k * a * k⁻¹ ∈ F.M hcount := fun a ha =>
    (hmemN a ha).mp (hNtop ▸ Subgroup.mem_top _)
  have h5M : 5 ∣ Nat.card (F.M hcount) := by
    have h1 := Subgroup.orderOf_dvd_natCard (F.M hcount)
      (hAM _ (e.symm ⟨pa * pb, mul_mem pa_mem pb_mem⟩).2)
    rwa [show k * ((e.symm ⟨pa * pb, mul_mem pa_mem pb_mem⟩ : ↥A) : G) * k⁻¹ =
        (MulAut.conj k).toMonoidHom ((e.symm ⟨pa * pb, mul_mem pa_mem pb_mem⟩ : ↥A) : G) from rfl,
      orderOf_injective _ (MulAut.conj k).injective, Subgroup.orderOf_coe, ho5] at h1
  obtain ⟨eM⟩ := F.nonempty_mulEquiv_M hcount h5M
  have hM60 : Nat.card (F.M hcount) = 60 := by
    rw [Nat.card_congr eM.toEquiv, nat_card_alternatingGroup, Nat.card_fin]
    rfl
  set Ak : Subgroup G := A.map (MulAut.conj k).toMonoidHom with hAk
  have hAkM : Ak ≤ F.M hcount := by
    rintro _ ⟨a, ha, rfl⟩
    exact hAM a ha
  have hAk60 : Nat.card Ak = 60 := by
    rw [hAk, Subgroup.card_map_of_injective (MulAut.conj k).injective, c.card_A]
  have hAkeq : Ak = F.M hcount :=
    Subgroup.eq_of_le_of_card_ge hAkM (by rw [hM60, hAk60])
  have hMA : ∀ m ∈ F.M hcount, ∃ a ∈ A, m = k * a * k⁻¹ := fun m hm => by
    rw [← hAkeq] at hm
    obtain ⟨a, ha, rfl⟩ := hm
    exact ⟨a, ha, rfl⟩
  have hRT : ∀ r ∈ R, k * r * k⁻¹ ∈ F.T := fun r hr =>
    ⟨hconjX (c.comm_R hr htR),
      Subgroup.mul_mem _ (Subgroup.mul_mem _ hkH (c.mem_centralizer_z hr)) (Subgroup.inv_mem _ hkH)⟩
  have hRW : ∀ r ∈ R, k * r * k⁻¹ ∈ F.W → r = 1 := fun r hr hW => by
    by_contra hr1
    have hkr1 : k * r * k⁻¹ ≠ 1 := fun h1 => hr1 (by
      calc r = k⁻¹ * (k * r * k⁻¹) * k := by group
        _ = 1 := by rw [h1]; group)
    exact c.not_isConj r hr hr1 ((F.isConj_of_mem_W hW hkr1).trans
      (isConj_iff.mpr ⟨k⁻¹, by group⟩))
  set φ : ↥R × ↥F.W → ↥F.T := fun p =>
    ⟨k * p.1 * k⁻¹ * p.2, F.T.mul_mem (hRT p.1 p.1.2) (F.W_le_T p.2.2)⟩ with hφ
  have hφinj : Function.Injective φ := by
    rintro ⟨⟨r, hr⟩, ⟨w, hw⟩⟩ ⟨⟨r', hr'⟩, ⟨w', hw'⟩⟩ h1
    have h2 : k * r * k⁻¹ * w = k * r' * k⁻¹ * w' := congrArg Subtype.val h1
    have h3 : k * (r'⁻¹ * r) * k⁻¹ = w' * w⁻¹ := by
      calc k * (r'⁻¹ * r) * k⁻¹ = (k * r' * k⁻¹)⁻¹ * (k * r * k⁻¹ * w) * w⁻¹ := by group
        _ = (k * r' * k⁻¹)⁻¹ * (k * r' * k⁻¹ * w') * w⁻¹ := by rw [h2]
        _ = w' * w⁻¹ := by group
    have h4 : r'⁻¹ * r = 1 := hRW _ (R.mul_mem (R.inv_mem hr') hr)
      (h3 ▸ F.W.mul_mem hw' (F.W.inv_mem hw))
    have hrr : r = r' := by
      calc r = r' * (r'⁻¹ * r) := by group
        _ = r' := by rw [h4, mul_one]
    subst hrr
    have hww : w = w' := by
      have h5 : k * r * k⁻¹ * w = k * r * k⁻¹ * w' := h2
      exact mul_left_cancel h5
    subst hww
    rfl
  have hφsurj : Function.Surjective φ := by
    have hcard : Nat.card (↥R × ↥F.W) = 16 := by rw [Nat.card_prod, c.card, F.card_W]
    exact ((Nat.bijective_iff_injective_and_card φ).mpr
      ⟨hφinj, le_antisymm (Nat.card_le_card_of_injective φ hφinj) (by
        rw [hcard]; exact F.card_T_le)⟩).2
  obtain ⟨s, hsT, hsM⟩ := F.exists_mem_T_mul_inv_mem_M hcount
    (hconjX (Subgroup.mem_centralizer_singleton_iff.mp hg))
  obtain ⟨⟨⟨r, hr⟩, ⟨w, hw⟩⟩, hrw⟩ := hφsurj ⟨s, hsT⟩
  have hs : s = k * r * k⁻¹ * w := (congrArg Subtype.val hrw).symm
  obtain ⟨a, ha, hak⟩ := hMA _ hsM
  obtain ⟨aw, haw, hawk⟩ := hMA _ (F.W_le_M hcount hw)
  refine ⟨r, hr, a * aw, A.mul_mem ha haw, ?_⟩
  have e1 : k * g * k⁻¹ = k * (a * r * aw) * k⁻¹ := by
    calc k * g * k⁻¹ = k * g * k⁻¹ * s⁻¹ * s := by group
      _ = k * a * k⁻¹ * (k * r * k⁻¹ * (k * aw * k⁻¹)) := by rw [hak, hs, hawk]
      _ = k * (a * r * aw) * k⁻¹ := by group
  have e2 : g = a * r * aw := by
    calc g = k⁻¹ * (k * g * k⁻¹) * k := by group
      _ = a * r * aw := by rw [e1]; group
  rw [e2, (c.comm_A hr ha).symm, mul_assoc]

end J2A5Config

end CFSG.Quasithin
