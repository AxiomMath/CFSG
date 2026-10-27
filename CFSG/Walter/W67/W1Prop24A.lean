module

public import CFSG.Walter.W67.Lemma22

public section

namespace CFSG.Walter.W67

open scoped MatrixGroups
open CFSG.GorensteinWalter

variable {G : Type} [Group G] [Finite G]

namespace Hyp

variable (h : Hyp G)

theorem p_eq_three (hq : h.q = 3) : h.p = 3 := by
  have h1 : h.p ∣ 3 := hq ▸ dvd_pow_self h.p h.f_pos.ne'
  rcases (Nat.dvd_prime Nat.prime_three).mp h1 with h1 | h1
  · exact absurd h1 (Fact.out : h.p.Prime).one_lt.ne'
  · exact h1

theorem f_eq_one (hq : h.q = 3) : h.f = 1 := by
  have h1 : h.p ^ h.f = 3 ^ 1 := hq
  rw [h.p_eq_three hq] at h1
  exact Nat.pow_right_injective (by norm_num) h1

theorem card_K_of_three (hq : h.q = 3) : Nat.card h.K = 12 := by
  rw [PSL2Sub.card_eq h.iso h.odd_p h.f_pos, show h.p ^ h.f = h.q from rfl, hq]
  norm_num

end Hyp

namespace Frame

variable {h : Hyp G} (fr : Frame h)

theorem K_le_normalizer_T_of_three
    (hq : h.q = 3) :
    h.K ≤ Subgroup.normalizer (fr.T : Set G) := by
  have h12 := PSL2Sub.card_inf_normalizer h.iso h.odd_p h.f_pos h.mod_eight fr.T_le_K
    fr.isKleinFour_T
  have heq : h.K ⊓ Subgroup.normalizer (fr.T : Set G) = h.K :=
    Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [h12, h.card_K_of_three hq])
  rw [← heq]
  exact inf_le_right

theorem E_le_centralizer_K_of_three
    (hq : h.q = 3) :
    fr.E ≤ Subgroup.centralizer (h.K : Set G) := by
  obtain ⟨e', P₀, hT⟩ := fr.exists_coords
  have hsub : Subsingleton (GaloisField h.p h.f ≃+* GaloisField h.p h.f) :=
    Suzuki.subsingleton_ringEquiv_of_card_prime (GaloisField h.p h.f) (p := h.p)
      (by rw [GaloisField.card _ _ h.f_pos.ne', h.f_eq_one hq, pow_one])
  intro x hx
  obtain ⟨σ, hσ⟩ := fr.conj_eq_fieldAut hT hx
  rw [Subsingleton.elim σ 1, map_one] at hσ
  rw [Subgroup.mem_centralizer_iff]
  intro k hk
  obtain ⟨y, rfl⟩ := PSL2Sub.exists_emb_eq e' hk
  have := hσ y
  rw [MulAut.one_apply] at this
  calc psl2Emb e' y * x = (x * psl2Emb e' y * x⁻¹) * x := by rw [this]
    _ = x * psl2Emb e' y := by group

theorem H_le_normalizer_S_of_three
    (hq : h.q = 3) :
    h.H ≤ Subgroup.normalizer ((fr.S : Subgroup G) : Set G) := by
  rw [← fr.isInternalDirectProduct_H.1]
  refine sup_le ((Subgroup.zpowers_le).mpr (Subgroup.le_normalizer fr.J_mem)) (sup_le ?_ ?_)
  · intro k hk
    refine JT.mem_normalizer_of_conj_mem fun s hs => ?_
    rw [← fr.zpowers_J_sup_T] at hs ⊢
    have hTN : Subgroup.zpowers h.J ≤ Subgroup.normalizer (fr.T : Set G) := by
      rw [Subgroup.zpowers_le]
      exact JT.mem_normalizer_of_conj_mem fun y hy => by
        rw [← h.commute_J (h.K_le_H hy.2), mul_inv_cancel_right]
        exact hy
    rw [sup_comm] at hs ⊢
    obtain ⟨t, ht, j, hj, rfl⟩ := (mem_sup_iff_of_le_normalizer hTN).mp hs
    have hj' : k * j * k⁻¹ = j := by
      rcases eq_one_or_eq_of_mem_zpowers h.orderOf_J hj with rfl | rfl
      · group
      · rw [h.commute_J (h.K_le_H hk), mul_inv_cancel_right]
    have : k * (t * j) * k⁻¹ = (k * t * k⁻¹) * (k * j * k⁻¹) := by group
    rw [this, hj']
    exact mul_mem (Subgroup.mem_sup_left ((Subgroup.mem_normalizer_iff.mp
      (fr.K_le_normalizer_T_of_three hq hk) t).mp ht)) (Subgroup.mem_sup_right hj)
  · exact fr.E_le_CS.trans (Subgroup.centralizer_le_normalizer _)

theorem le_S_of_isPGroup {P : Subgroup G} (hP : IsPGroup 2 P)
    (hPN : P ≤ Subgroup.normalizer ((fr.S : Subgroup G) : Set G)) : P ≤ (fr.S : Subgroup G) := by
  have h2 : IsPGroup 2 (P ⊔ (fr.S : Subgroup G) : Subgroup G) :=
    IsPGroup.to_sup_of_normal_right' hP fr.S.isPGroup' hPN
  have heq : P ⊔ (fr.S : Subgroup G) = fr.S :=
    (Subgroup.eq_of_le_of_card_ge le_sup_right (by rw [fr.card_S]; exact h.card_le_eight h2)).symm
  rw [← heq]
  exact le_sup_left

theorem mem_S_of_sq_eq_one {x : G} (hx : x ∈ Subgroup.normalizer ((fr.S : Subgroup G) : Set G))
    (hx2 : x ^ 2 = 1) : x ∈ (fr.S : Subgroup G) := by
  have hP : IsPGroup 2 (Subgroup.zpowers x) := by
    rcases (Nat.dvd_prime Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hx2) with h1 | h1
    · exact IsPGroup.of_card (n := 0) (by rw [Nat.card_zpowers, h1, pow_zero])
    · exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, h1, pow_one])
  exact fr.le_S_of_isPGroup hP ((Subgroup.zpowers_le).mpr hx) (Subgroup.mem_zpowers x)

theorem pPrimeCore_inf_normalizer_le :
    CFSG.pPrimeCore 2 G ⊓ Subgroup.normalizer ((fr.S : Subgroup G) : Set G) ≤ fr.CS := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hO : Odd (Nat.card (CFSG.pPrimeCore 2 G)) := by
    have := CFSG.pPrimeCore_coprime_card (p := 2) (G := G)
    rwa [Nat.coprime_two_left] at this
  rintro o ⟨hoO, hoN⟩
  rw [Subgroup.mem_centralizer_iff]
  intro s hs
  have hcS : o * s * o⁻¹ * s⁻¹ ∈ (fr.S : Subgroup G) :=
    mul_mem ((Subgroup.mem_normalizer_iff.mp hoN s).mp hs) (inv_mem hs)
  have hcO : o * s * o⁻¹ * s⁻¹ ∈ CFSG.pPrimeCore 2 G := by
    rw [show o * s * o⁻¹ * s⁻¹ = o * (s * o⁻¹ * s⁻¹) by group]
    exact mul_mem hoO ((CFSG.pPrimeCore_normal).conj_mem _ (inv_mem hoO) s)
  have h1 := eq_one_of_odd_of_isPGroup fr.S.isPGroup' hcS
    (Odd.of_dvd_nat hO (Subgroup.orderOf_dvd_natCard _ hcO))
  calc s * o = (o * s * o⁻¹ * s⁻¹)⁻¹ * (o * s) := by group
    _ = o * s := by rw [h1, inv_one, one_mul]

section Three

variable (hq : h.q = 3) (hidx : ∀ N : Subgroup G, N.Normal → N.index ≠ 2)
include hq hidx

theorem centralizer_le_normalizer_S_of_three
    {s : G} (hs : s ∈ (fr.S : Subgroup G))
    (hs1 : s ≠ 1) :
    Subgroup.centralizer ({s} : Set G) ≤ Subgroup.normalizer ((fr.S : Subgroup G) : Set G) := by
  obtain ⟨n, hn, hns⟩ := fr.exists_conj_of_mem_S hidx fr.J_mem h.J_ne_one hs hs1
  intro x hx
  rw [Subgroup.mem_centralizer_singleton_iff] at hx
  have hy : n⁻¹ * x * n ∈ h.H := by
    rw [h.mem_H_iff]
    calc n⁻¹ * x * n * h.J = n⁻¹ * (x * (n * h.J * n⁻¹)) * n := by group
      _ = n⁻¹ * ((n * h.J * n⁻¹) * x) * n := by rw [hns, hx]
      _ = h.J * (n⁻¹ * x * n) := by group
  have := mul_mem (mul_mem hn (fr.H_le_normalizer_S_of_three hq hy)) (inv_mem hn)
  rwa [show n * (n⁻¹ * x * n) * n⁻¹ = x by group] at this

theorem mem_normalizer_S_of_conj_mem
    {s g : G} (hs : s ∈ (fr.S : Subgroup G)) (hs1 : s ≠ 1)
    (hgs : g * s * g⁻¹ ∈ (fr.S : Subgroup G)) :
    g ∈ Subgroup.normalizer ((fr.S : Subgroup G) : Set G) := by
  have hgs1 : g * s * g⁻¹ ≠ 1 := fun h1 => hs1 (by
    calc s = g⁻¹ * (g * s * g⁻¹) * g := by group
      _ = 1 := by rw [h1]; group)
  set Sg := (fr.S : Subgroup G).map (MulAut.conj g).toMonoidHom
  have hSg : Sg ≤ Subgroup.normalizer ((fr.S : Subgroup G) : Set G) := by
    rintro _ ⟨s', hs', rfl⟩
    refine fr.centralizer_le_normalizer_S_of_three hq hidx hgs hgs1 ?_
    rw [Subgroup.mem_centralizer_singleton_iff]
    change g * s' * g⁻¹ * (g * s * g⁻¹) = g * s * g⁻¹ * (g * s' * g⁻¹)
    calc g * s' * g⁻¹ * (g * s * g⁻¹) = g * (s' * s) * g⁻¹ := by group
      _ = g * (s * s') * g⁻¹ := by rw [fr.comm_of_mem_S hs' hs]
      _ = g * s * g⁻¹ * (g * s' * g⁻¹) := by group
  have hle := fr.le_S_of_isPGroup (fr.S.isPGroup'.map _) hSg
  exact JT.mem_normalizer_of_conj_mem fun s' hs' => hle ⟨s', hs', rfl⟩

theorem pPrimeCore_le_CS_of_three :
    CFSG.pPrimeCore 2 G ≤ fr.CS := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set O := CFSG.pPrimeCore 2 G
  have hO : Odd (Nat.card O) := by
    have := CFSG.pPrimeCore_coprime_card (p := 2) (G := G)
    rwa [Nat.coprime_two_left] at this
  have hT := fr.isKleinFour_T
  have hTab : ∀ a b : fr.T, a * b = b * a := mul_comm_of_exponent_two hT.exponent_two
  have : CFSG.IsElementaryAbelian 2 fr.T :=
    { toIsMulCommutative := ⟨⟨hTab⟩⟩
      exponent_dvd_p := by rw [hT.exponent_two] }
  let : MulDistribMulAction fr.T O :=
    MulDistribMulAction.compHom O ((MulAut.conjNormal (H := O)).comp fr.T.subtype)
  have hgen := CFSG.SolvableHall.coprime_centralizer_generation (p := 2) (A := fr.T) (H := O)
    (by rw [hT.card_four]; norm_num)
    (fun h2 => (Nat.not_even_iff_odd.mpr hO) (even_iff_two_dvd.mpr h2))
  have hle : ⨆ (a : fr.T) (_ : a ≠ 1), CFSG.fixedPointSubgroup (Subgroup.zpowers a) O ≤
      fr.CS.comap O.subtype := by
    refine iSup₂_le fun a ha => ?_
    intro y hy
    rw [CFSG.SolvableHall.mem_fixedPointSubgroup_zpowers_iff] at hy
    have hya : (y : G) * a = a * y := by
      have h := congrArg Subtype.val hy
      change ((MulAut.conjNormal (a : G)) y : G) = y at h
      rw [MulAut.conjNormal_apply] at h
      calc (y : G) * a = (a * y * (a : G)⁻¹) * a := by rw [h]
        _ = a * y := by group
    have ha1 : (a : G) ≠ 1 := fun h => ha (Subtype.ext h)
    have hyN := fr.centralizer_le_normalizer_S_of_three hq hidx (fr.T_le_S a.2) ha1
      (Subgroup.mem_centralizer_singleton_iff.mpr hya)
    exact fr.pPrimeCore_inf_normalizer_le ⟨y.2, hyN⟩
  intro x hx
  exact hle (hgen.symm ▸ Subgroup.mem_top (⟨x, hx⟩ : O))

theorem pPrimeCore_le_E_of_three :
    CFSG.pPrimeCore 2 G ≤ fr.E := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hO : Odd (Nat.card (CFSG.pPrimeCore 2 G)) := by
    have := CFSG.pPrimeCore_coprime_card (p := 2) (G := G)
    rwa [Nat.coprime_two_left] at this
  intro x hx
  exact fr.mem_E_of_odd (fr.pPrimeCore_le_CS_of_three hq hidx hx)
    (Odd.of_dvd_nat hO (Subgroup.orderOf_dvd_natCard _ hx))

include fr in
theorem pPrimeCore_le_centralizer_K_of_three :
    CFSG.pPrimeCore 2 G ≤ Subgroup.centralizer (h.K : Set G) :=
  (fr.pPrimeCore_le_E_of_three hq hidx).trans (fr.E_le_centralizer_K_of_three hq)

end Three

theorem K_inf_centralizer_of_three (hq : h.q = 3) {t : G} (ht : t ∈ fr.T) (ht1 : t ≠ 1) :
    h.K ⊓ Subgroup.centralizer ({t} : Set G) = fr.T := by
  have hto : orderOf t = 2 := orderOf_eq_prime (by
    rw [pow_two]; exact JT.mul_self_of_isKleinFour fr.isKleinFour_T ht) ht1
  obtain ⟨y, hy⟩ := PSL2Sub.exists_emb_eq h.iso (fr.T_le_K ht)
  have hyo : orderOf y = 2 := by
    have := orderOf_injective (psl2Emb h.iso) (PSL2Sub.emb_injective h.iso) y
    rw [hy, hto] at this
    exact this.symm
  have h4 := Suzuki.card_centralizer_of_card_three (GaloisField h.p h.f)
    (GaloisField.card _ _ h.f_pos.ne') h.odd_p h.f_pos hq hyo
  have h2 := JT.map_centralizer_singleton_of_injective (psl2Emb h.iso)
    (PSL2Sub.emb_injective h.iso) y
  rw [PSL2Sub.emb_range, hy] at h2
  have hcard : Nat.card (h.K ⊓ Subgroup.centralizer ({t} : Set G) : Subgroup G) = 4 := by
    rw [← h2, Subgroup.card_map_of_injective (PSL2Sub.emb_injective h.iso), h4]
  have hle : fr.T ≤ h.K ⊓ Subgroup.centralizer ({t} : Set G) := fun x hx =>
    ⟨fr.T_le_K hx, Subgroup.mem_centralizer_singleton_iff.mpr
      (fr.comm_of_mem_S (fr.T_le_S hx) (fr.T_le_S ht))⟩
  exact (Subgroup.eq_of_le_of_card_ge hle (by rw [hcard, fr.card_T])).symm

theorem exists_three (hq : h.q = 3) :
    ∃ k ∈ h.K, orderOf k = 3 ∧ ∀ t ∈ fr.T, k * t = t * k → t = 1 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨k, hk⟩ := exists_prime_orderOf_dvd_card' (G := h.K) 3
    (by rw [h.card_K_of_three hq]; norm_num)
  refine ⟨k, k.2, by rw [← Subgroup.orderOf_coe] at hk; exact hk, fun t ht hkt => ?_⟩
  by_contra ht1
  have hkT : (k : G) ∈ fr.T := by
    rw [← fr.K_inf_centralizer_of_three hq ht ht1]
    exact ⟨k.2, Subgroup.mem_centralizer_singleton_iff.mpr hkt⟩
  have hk2 : (k : G) * k = 1 := JT.mul_self_of_isKleinFour fr.isKleinFour_T hkT
  have : orderOf (k : G) ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hk2)
  rw [Subgroup.orderOf_coe, hk] at this
  omega

theorem eq_one_or_eq_J_of_commute {k : G} (hk : k ∈ h.K)
    (hfix : ∀ t ∈ fr.T, k * t = t * k → t = 1) {s : G} (hs : s ∈ (fr.S : Subgroup G))
    (hks : k * s = s * k) : s = 1 ∨ s = h.J := by
  rw [← fr.zpowers_J_sup_T] at hs
  have hTN : Subgroup.zpowers h.J ≤ Subgroup.normalizer (fr.T : Set G) := by
    rw [Subgroup.zpowers_le]
    exact JT.mem_normalizer_of_conj_mem fun y hy => by
      rw [← h.commute_J (h.K_le_H hy.2), mul_inv_cancel_right]
      exact hy
  rw [sup_comm] at hs
  obtain ⟨t, ht, j, hj, rfl⟩ := (mem_sup_iff_of_le_normalizer hTN).mp hs
  have hkj : k * j = j * k := by
    rcases eq_one_or_eq_of_mem_zpowers h.orderOf_J hj with rfl | rfl
    · rw [one_mul, mul_one]
    · exact h.commute_J (h.K_le_H hk)
  have hkt : k * t = t * k := by
    have h1 : k * t * j = t * k * j := by
      calc k * t * j = k * (t * j) := by group
        _ = t * j * k := hks
        _ = t * (j * k) := by group
        _ = t * (k * j) := by rw [hkj]
        _ = t * k * j := by group
    exact mul_right_cancel h1
  rw [hfix t ht hkt, one_mul]
  exact eq_one_or_eq_of_mem_zpowers h.orderOf_J hj

end Frame

end CFSG.Walter.W67
