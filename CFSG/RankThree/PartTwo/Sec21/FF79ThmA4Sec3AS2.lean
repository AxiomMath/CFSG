module

public import CFSG.RankThree.PartTwo.Sec21.FF79ThmA4Sec3AStarDefs

import CFSG.RankThree.PartTwo.Sec21.FF79Lemma41Base
import CFSG.RankThree.PartTwo.Sec21.FF79ThmA4Sec3L4Exp32
import CFSG.RankThree.PartTwo.Sec21.FF79Sec3AS1

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF79.H4.AS
open CFSG.RankThree.PartTwo.Sec21.FF79.H4.AS
open CFSG.RankThree.PartTwo.Sec21.FF79.AS
open CFSG CFSG.RankThree.PartTwo.Sec21
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]
variable {b : G} {J B A P D : Subgroup G}

theorem comm_of_conj {g a : G} (h : g * a * g⁻¹ = a) : a * g = g * a := by
  calc a * g = g * a * g⁻¹ * g := by rw [h]
    _ = g * a := by group

theorem ord_b (h : FF79Sec34Pre4 b J B A P D) : orderOf b = 3 := h.hyp.ord

theorem J_le (h : FF79Sec34Pre4 b J B A P D) : J ≤ Cen b := by
  rw [h.hJ]; exact Subgroup.map_subtype_le _

theorem comm_A (h : FF79Sec34Pre4 b J B A P D) {x y : G} (hx : x ∈ A) (hy : y ∈ A) :
    x * y = y * x :=
  congrArg Subtype.val (h.elemA.1.toIsMulCommutative.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)

theorem comm_B (h : FF79Sec34Pre4 b J B A P D) {x y : G} (hx : x ∈ B) (hy : y ∈ B) :
    x * y = y * x :=
  congrArg Subtype.val (h.elemB.1.toIsMulCommutative.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)

theorem pow3_A (h : FF79Sec34Pre4 b J B A P D) {x : G} (hx : x ∈ A) : x ^ 3 = 1 := by
  haveI := h.elemA.1
  exact elemPow_eq_one_of_isElementaryAbelian (A := A) x hx

theorem b_mem_B (h : FF79Sec34Pre4 b J B A P D) : b ∈ B :=
  h.supB ▸ Subgroup.mem_sup_left (Subgroup.mem_zpowers b)

theorem B0_le_A (h : FF79Sec34Pre4 b J B A P D) : B ⊓ J ≤ A := h.B0A

theorem A_le_cenS (h : FF79Sec34Pre4 b J B A P D) : A ≤ CenS A := fun x hx =>
  Subgroup.mem_centralizer_iff.mpr fun y hy => comm_A h hy hx

theorem cenS_le_nor (A : Subgroup G) : CenS A ≤ Nor A := fun c hc =>
  L41.mem_nor_of_forall fun a ha => by
    rw [← Subgroup.mem_centralizer_iff.mp hc a ha]; group; exact ha

theorem isPGroup_A (h : FF79Sec34Pre4 b J B A P D) : IsPGroup 3 A :=
  IsPGroup.of_card (n := 4) h.elemA.2

theorem zpowers_isPGroup_of_mem {X : Subgroup G} (hX : IsPGroup 3 X) {x : G} (hx : x ∈ X) :
    IsPGroup 3 (Subgroup.zpowers x) :=
  hX.to_le ((Subgroup.zpowers_le).mpr hx)

theorem b_not_cenS (h : FF79Sec34Pre4 b J B A P D) : b ∉ CenS A := by
  intro hb
  have h1 : Subgroup.zpowers b ≤ Subgroup.centralizer (A : Set G) := (Subgroup.zpowers_le).mpr hb
  have h2 : ⁅Subgroup.zpowers b, A⁆ = ⊥ := (Subgroup.commutator_eq_bot_iff_le_centralizer).mpr h1
  rw [h.commbA] at h2
  have := h.elemB0.2
  rw [h2, Subgroup.card_bot] at this
  omega

theorem b_not_A (h : FF79Sec34Pre4 b J B A P D) : b ∉ A := fun hb =>
  b_not_cenS h (A_le_cenS h hb)

theorem card_B (h : FF79Sec34Pre4 b J B A P D) : Nat.card B = 3 * Nat.card ↥(B ⊓ J) := by
  rw [h.elemB.2, h.elemB0.2]; norm_num

theorem B_inf_cenS (h : FF79Sec34Pre4 b J B A P D) : B ⊓ CenS A = B ⊓ J := by
  rcases eq_or_eq_of_card_three_mul (le_inf inf_le_left ((B0_le_A h).trans (A_le_cenS h)))
    inf_le_left (card_B h) with e | e
  · exact e
  · exfalso
    have : b ∈ B ⊓ CenS A := by rw [e]; exact b_mem_B h
    exact b_not_cenS h this.2

theorem mem_B0_of_cen (h : FF79Sec34Pre4 b J B A P D) {x : G} (hxA : x ∈ CenS A)
    (hxb : x * b = b * x) (hx3 : IsPGroup 3 (Subgroup.zpowers x)) : x ∈ B ⊓ J := by
  have hxC : x ∈ Cen b := Subgroup.mem_centralizer_iff.mpr fun y hy => by
    rw [Set.mem_singleton_iff] at hy; subst hy; exact hxb.symm
  have hBx : B ≤ Cen x := by
    rw [← h.supB]
    refine sup_le ((Subgroup.zpowers_le).mpr ?_) fun c hc => ?_
    · exact Subgroup.mem_centralizer_iff.mpr fun y hy => by
        rw [Set.mem_singleton_iff] at hy; subst hy; exact hxb
    · exact Subgroup.mem_centralizer_iff.mpr fun y hy => by
        rw [Set.mem_singleton_iff] at hy; subst hy
        exact (Subgroup.mem_centralizer_iff.mp hxA c (B0_le_A h hc)).symm
  have hxN : x ∈ Nor B := L41.mem_nor_of_forall fun y hy => by
    have := Subgroup.mem_centralizer_iff.mp (hBx hy) x rfl
    rw [this]; group; exact hy
  have hxB := mem_of_sylowOf_of_mem_nor h.sylB hxC hxN hx3
  rw [← B_inf_cenS h]
  exact ⟨hxB, hxA⟩

theorem B_decomp (h : FF79Sec34Pre4 b J B A P D) {y : G} (hy : y ∈ B) :
    ∃ k : ℤ, ∃ c ∈ B ⊓ J, y = b ^ k * c := by
  have hle : B ⊓ J ≤ Subgroup.normalizer (Subgroup.zpowers b : Set G) := fun c hc =>
    L41.mem_nor_of_forall fun x hx => by
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
      have hcb : Commute c b := comm_B h hc.1 (b_mem_B h)
      rw [(hcb.zpow_right k).eq]; group; exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers b) k
  have hset := Subgroup.coe_mul_of_right_le_normalizer_left (Subgroup.zpowers b) (B ⊓ J) hle
  have hy' : y ∈ ((Subgroup.zpowers b : Set G) * ((B ⊓ J : Subgroup G) : Set G)) := by
    rw [← hset, h.supB]; exact hy
  obtain ⟨x, hx, c, hc, rfl⟩ := Set.mem_mul.mp hy'
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
  exact ⟨k, c, hc, rfl⟩

section Z

variable {z : D}

theorem z_inv_A (h : FF79Sec34Pre4 b J B A P D) (hz : z ∈ Subgroup.center D) (hz1 : z ≠ 1)
    {a : G} (ha : a ∈ A) : (z : G) * a * (z : G)⁻¹ = a⁻¹ :=
  h.zA z hz hz1 a ha

theorem z_comm_b (h : FF79Sec34Pre4 b J B A P D) : (z : G) * b = b * (z : G) :=
  (Subgroup.mem_centralizer_iff.mp ((J_le h) (h.DJ z.2)) b rfl).symm

theorem z_sq (h : FF79Sec34Pre4 b J B A P D) (hodd : Odd (Nat.card (CenS A)))
    (hz : z ∈ Subgroup.center D) (hz1 : z ≠ 1) : (z : G) * (z : G) = 1 := by
  set w : G := (z : G) * (z : G) with hw
  have hwC : w ∈ CenS A := Subgroup.mem_centralizer_iff.mpr fun a ha => by
    have e1 := z_inv_A h hz hz1 ha
    have e2 := z_inv_A h hz hz1 (A.inv_mem ha)
    rw [inv_inv] at e2
    have e3 : w * a * w⁻¹ = a := by
      calc w * a * w⁻¹ = (z : G) * ((z : G) * a * (z : G)⁻¹) * (z : G)⁻¹ := by rw [hw]; group
        _ = a := by rw [e1, e2]
    exact comm_of_conj e3
  have h8 : (z : G) ^ 8 = 1 := by
    have := pow_card_eq_one' (G := D) (x := z)
    rw [h.D8.1] at this
    simpa using congrArg Subtype.val this
  have hw4 : w ^ 4 = 1 := by rw [hw, ← sq, ← pow_mul]; exact h8
  have h1 : orderOf w ∣ 4 := orderOf_dvd_of_pow_eq_one hw4
  have h2 : orderOf w ∣ Nat.card (CenS A) := Subgroup.orderOf_dvd_natCard _ hwC
  have h3 : Odd (orderOf w) := Odd.of_dvd_nat hodd h2
  have h4 : orderOf w = 1 := by
    obtain ⟨i, hi, he⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (show orderOf w ∣ 2 ^ 2 from h1)
    interval_cases i
    · simpa using he
    · rw [he] at h3; exact absurd h3 (by decide)
    · rw [he] at h3; exact absurd h3 (by decide)
  exact orderOf_eq_one_iff.mp h4

theorem mem_zpowers_of_Y (h : FF79Sec34Pre4 b J B A P D) (hz : z ∈ Subgroup.center D)
    (hz1 : z ≠ 1) {y : G} (hyN : y ∈ Nor A) (hyz : y * (z : G) = (z : G) * y)
    (hyb : y * b = b * y) (hy3 : IsPGroup 3 (Subgroup.zpowers y)) :
    y ∈ Subgroup.zpowers b := by
  have hyC : y ∈ Cen b := Subgroup.mem_centralizer_iff.mpr fun x hx => by
    rw [Set.mem_singleton_iff] at hx; subst hx; exact hyb.symm
  have hyB0 : y ∈ Nor (B ⊓ J) := L41.mem_nor_of_forall fun c hc => by
    have hcA := B0_le_A h hc
    have h1 : y * c * y⁻¹ ∈ A := (Subgroup.mem_normalizer_iff.mp hyN c).mp hcA
    have hcb : c * b = b * c := comm_B h hc.1 (b_mem_B h)
    have h2 : y * c * y⁻¹ * b = b * (y * c * y⁻¹) := by
      have hyb' : y⁻¹ * b = b * y⁻¹ := by
        calc y⁻¹ * b = y⁻¹ * (b * y) * y⁻¹ := by group
          _ = y⁻¹ * (y * b) * y⁻¹ := by rw [hyb]
          _ = b * y⁻¹ := by group
      calc y * c * y⁻¹ * b = y * c * (b * y⁻¹) := by rw [mul_assoc (y * c), hyb']
        _ = y * (b * c) * y⁻¹ := by rw [← hcb]; group
        _ = b * (y * c * y⁻¹) := by rw [← mul_assoc, hyb]; group
    exact mem_B0_of_cen h (A_le_cenS h h1) h2 (zpowers_isPGroup_of_mem (isPGroup_A h) h1)
  have hyZ : y ∈ Nor (Subgroup.zpowers b) := L41.mem_nor_of_forall fun x hx => by
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    rw [((Commute.zpow_right hyb k).eq)]; group
    exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers b) k
  have hyNB : y ∈ Nor B := h.supB ▸ mem_nor_sup hyZ hyB0
  have hyB := mem_of_sylowOf_of_mem_nor h.sylB hyC hyNB hy3
  obtain ⟨k, c, hc, rfl⟩ := B_decomp h hyB
  have hzb : Commute (z : G) b := z_comm_b h
  have e1 : (z : G) * (b ^ k * c) * (z : G)⁻¹ = b ^ k * c⁻¹ := by
    have e2 := z_inv_A h hz hz1 (B0_le_A h hc)
    calc (z : G) * (b ^ k * c) * (z : G)⁻¹ = ((z : G) * b ^ k) * c * (z : G)⁻¹ := by group
      _ = b ^ k * ((z : G) * c * (z : G)⁻¹) := by rw [(hzb.zpow_right k).eq]; group
      _ = b ^ k * c⁻¹ := by rw [e2]
  have e3 : (z : G) * (b ^ k * c) * (z : G)⁻¹ = b ^ k * c := by
    rw [← hyz]; group
  rw [e3] at e1
  have hcc : c = c⁻¹ := mul_left_cancel e1
  have hc3 := pow3_A h (B0_le_A h hc)
  have hc1 : c = 1 := by
    have : c ^ 2 = 1 := by
      calc c ^ 2 = c * c := sq c
        _ = c * c⁻¹ := by rw [← hcc]
        _ = 1 := mul_inv_cancel c
    calc c = c ^ 3 * (c ^ 2)⁻¹ := by group
      _ = 1 := by rw [hc3, this]; group
  rw [hc1, mul_one]
  exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers b) k

theorem card_le_three_of_Y (h : FF79Sec34Pre4 b J B A P D) (hz : z ∈ Subgroup.center D)
    (hz1 : z ≠ 1) {T : Subgroup G} (hT : IsPGroup 3 T) (hTY : T ≤ Nor A ⊓ Cen (z : G)) :
    Nat.card T ≤ 3 := by
  have hbY : Subgroup.zpowers b ≤ Nor A ⊓ Cen (z : G) := (Subgroup.zpowers_le).mpr
    ⟨h.bA, Subgroup.mem_centralizer_iff.mpr fun y hy => by
      rw [Set.mem_singleton_iff] at hy; subst hy; exact (z_comm_b h)⟩
  have hb3 : IsPGroup 3 (Subgroup.zpowers b) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, ord_b h, pow_one])
  obtain ⟨R, hR, hbR⟩ := exists_sylowOf_three_ge hbY hb3
  have hRb : R ≤ Subgroup.zpowers b := by
    refine le_zpowers_of_cen (ord_b h) hR.2.1 (hbR (Subgroup.mem_zpowers b)) fun t ht htb => ?_
    have htY := hR.1 ht
    have htz : t * (z : G) = (z : G) * t := (Subgroup.mem_centralizer_iff.mp htY.2 _ rfl).symm
    exact mem_zpowers_of_Y h hz hz1 htY.1 htz htb (zpowers_isPGroup_of_mem hR.2.1 ht)
  calc Nat.card T ≤ Nat.card R := card_le_of_sylowOf_three hR hT hTY
    _ ≤ Nat.card (Subgroup.zpowers b) := Subgroup.card_le_of_le hRb
    _ = 3 := by rw [Nat.card_zpowers, ord_b h]

theorem exists_mul_of_nor (h : FF79Sec34Pre4 b J B A P D) (hodd : Odd (Nat.card (CenS A)))
    (hz : z ∈ Subgroup.center D) (hz1 : z ≠ 1) {n : G} (hn : n ∈ Nor A) :
    ∃ c ∈ CenS A, ∃ y ∈ Nor A ⊓ Cen (z : G), n = c * y := by
  set zz : G := (z : G) with hzz
  have hz2 : zz * zz = 1 := z_sq h hodd hz hz1
  set w : G := n * zz * n⁻¹ with hw
  have hw2 : w * w = 1 := by
    calc w * w = n * (zz * zz) * n⁻¹ := by rw [hw]; group
      _ = 1 := by rw [hz2]; group
  have hwinv : ∀ a ∈ A, w * a * w⁻¹ = a⁻¹ := by
    intro a ha
    have h1 : n⁻¹ * a * n⁻¹⁻¹ ∈ A :=
      (Subgroup.mem_normalizer_iff.mp ((Subgroup.normalizer (A : Set G)).inv_mem hn) a).mp ha
    have h2 := z_inv_A h hz hz1 h1
    calc w * a * w⁻¹ = n * (zz * (n⁻¹ * a * n⁻¹⁻¹) * zz⁻¹) * n⁻¹ := by rw [hw]; group
      _ = a⁻¹ := by rw [h2]; group
  have huC : w * zz ∈ CenS A := Subgroup.mem_centralizer_iff.mpr fun a ha => by
    have e1 := z_inv_A h hz hz1 ha
    have e2 := hwinv a⁻¹ (A.inv_mem ha)
    rw [inv_inv] at e2
    have e3 : (w * zz) * a * (w * zz)⁻¹ = a := by
      calc (w * zz) * a * (w * zz)⁻¹ = w * (zz * a * zz⁻¹) * w⁻¹ := by group
        _ = a := by rw [e1, e2]
    exact comm_of_conj e3
  have ho : Odd (orderOf (w * zz)) :=
    Odd.of_dvd_nat hodd (Subgroup.orderOf_dvd_natCard _ huC)
  obtain ⟨k, hk⟩ := exists_conj_eq_of_odd hw2 hz2 ho
  set h0 : G := (w * zz) ^ k with hh0
  have hh0C : h0 ∈ CenS A := Subgroup.pow_mem _ huC k
  refine ⟨h0⁻¹, (CenS A).inv_mem hh0C, h0 * n, ⟨?_, ?_⟩, by group⟩
  · exact (Subgroup.normalizer (A : Set G)).mul_mem (cenS_le_nor A hh0C) hn
  · refine Subgroup.mem_centralizer_iff.mpr fun y hy => ?_
    rw [Set.mem_singleton_iff] at hy; subst hy
    have : h0 * n * zz * (h0 * n)⁻¹ = zz := by
      calc h0 * n * zz * (h0 * n)⁻¹ = h0 * (n * zz * n⁻¹) * h0⁻¹ := by group
        _ = zz := by rw [← hw]; exact hk
    exact comm_of_conj this

end Z

end CFSG.RankThree.PartTwo.Sec21.FF79.H4.AS
