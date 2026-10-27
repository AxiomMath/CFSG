module

public import CFSG.RankThree.PartTwo.Sec14.Notation
public import CFSG.GroupTheory.Fitting.CharacteristicP

public section

namespace CFSG.RankThree.PartTwo.Sec14

open CFSG CFSG.GH74.GLS
open scoped Pointwise

variable {G : Type*} [Group G]

theorem mem_left_of_coprime_orderOf {D C : Subgroup G} (hCD : C ≤ Subgroup.normalizer (D : Set G))
    {x : G} (hx : x ∈ D ⊔ C) (hcop : Nat.Coprime (orderOf x) (Nat.card C)) : x ∈ D := by
  set K := D ⊔ C with hK
  have hDK : D ≤ K := le_sup_left
  have hCK : C ≤ K := le_sup_right
  have hKN : K ≤ Subgroup.normalizer (D : Set G) := sup_le Subgroup.le_normalizer hCD
  have hN : (D.subgroupOf K).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hDK).mpr hKN
  have hx' : x ∈ ((D : Set G) * (C : Set G)) := by
    rw [← Subgroup.coe_mul_of_right_le_normalizer_left D C hCD]
    exact hx
  obtain ⟨d, hd, c, hc, hdc⟩ := hx'
  let π : K →* K ⧸ D.subgroupOf K := QuotientGroup.mk' (D.subgroupOf K)
  have hπd : π ⟨d, hDK hd⟩ = 1 :=
    (QuotientGroup.eq_one_iff (N := D.subgroupOf K) _).mpr (Subgroup.mem_subgroupOf.mpr hd)
  have hπx : π ⟨x, hx⟩ = π ⟨c, hCK hc⟩ := by
    have hxdc : (⟨x, hx⟩ : K) = ⟨d, hDK hd⟩ * ⟨c, hCK hc⟩ := Subtype.ext hdc.symm
    rw [hxdc, map_mul, hπd, one_mul]
  have h1 : orderOf (π ⟨x, hx⟩) ∣ Nat.card C := by
    rw [hπx]
    refine (orderOf_map_dvd π _).trans ?_
    rw [Subgroup.orderOf_mk]
    have := orderOf_dvd_natCard (⟨c, hc⟩ : C)
    rwa [Subgroup.orderOf_mk] at this
  have h2 : orderOf (π ⟨x, hx⟩) ∣ orderOf x := by
    refine (orderOf_map_dvd π _).trans ?_
    rw [Subgroup.orderOf_mk]
  have hord : orderOf (π ⟨x, hx⟩) = 1 :=
    Nat.dvd_one.mp (hcop.gcd_eq_one ▸ Nat.dvd_gcd h2 h1)
  rw [orderOf_eq_one_iff] at hord
  exact Subgroup.mem_subgroupOf.mp ((QuotientGroup.eq_one_iff (N := D.subgroupOf K) _).mp hord)

theorem mem_left_of_pow_prime_pow {p : ℕ} (hp : p.Prime) {D C : Subgroup G}
    (hCD : C ≤ Subgroup.normalizer (D : Set G)) (hcop : Nat.Coprime p (Nat.card C)) {x : G}
    (hx : x ∈ D ⊔ C) {k : ℕ} (hxk : x ^ p ^ k = 1) : x ∈ D := by
  refine mem_left_of_coprime_orderOf hCD hx ?_
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hp).mp (orderOf_dvd_of_pow_eq_one hxk)
  rw [hj]
  exact Nat.Coprime.pow_left j hcop

theorem mem_left_of_coprime_of_isPGroup [Finite G] {p : ℕ} (hp : p.Prime) {D C : Subgroup G}
    (hCD : C ≤ Subgroup.normalizer (D : Set G)) (hC : IsPGroup p C) {x : G}
    (hx : x ∈ D ⊔ C) (hxp : Nat.Coprime (orderOf x) p) : x ∈ D := by
  have : Fact p.Prime := ⟨hp⟩
  refine mem_left_of_coprime_orderOf hCD hx ?_
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card.mp hC)
  rw [hn]
  exact Nat.Coprime.pow_right n hxp

theorem oPrimeResidualOf_eq_closure (p : ℕ) (K : Subgroup G) :
    oPrimeResidualOf p K = Subgroup.closure {x | x ∈ K ∧ ∃ k : ℕ, x ^ p ^ k = 1} := by
  rw [oPrimeResidualOf, oPrimeResidual, MonoidHom.map_closure]
  congr 1
  ext x
  constructor
  · rintro ⟨y, ⟨k, hk⟩, rfl⟩
    exact ⟨y.2, k, by rw [Subgroup.coe_subtype, ← Subgroup.coe_pow, hk, Subgroup.coe_one]⟩
  · rintro ⟨hx, k, hk⟩
    exact ⟨⟨x, hx⟩, ⟨k, Subtype.ext (by rw [Subgroup.coe_pow, Subgroup.coe_one, hk])⟩, rfl⟩

theorem inSubgroup_oResidual_eq_closure (p : ℕ) (K : Subgroup G) :
    inSubgroup (oResidual p) K = Subgroup.closure {x | x ∈ K ∧ Nat.Coprime (orderOf x) p} := by
  rw [inSubgroup, oResidual, MonoidHom.map_closure]
  congr 1
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    refine ⟨y.2, ?_⟩
    rwa [Subgroup.coe_subtype, Subgroup.orderOf_coe]
  · rintro ⟨hx, hco⟩
    refine ⟨⟨x, hx⟩, ?_, rfl⟩
    change Nat.Coprime (orderOf (⟨x, hx⟩ : K)) p
    rwa [Subgroup.orderOf_mk]

theorem oPrimeResidualOf_eq_of_le {p : ℕ} {N K : Subgroup G} (hNK : N ≤ K)
    (h : ∀ x ∈ K, ∀ k : ℕ, x ^ p ^ k = 1 → x ∈ N) :
    oPrimeResidualOf p N = oPrimeResidualOf p K := by
  rw [oPrimeResidualOf_eq_closure, oPrimeResidualOf_eq_closure]
  congr 1
  ext x
  exact ⟨fun ⟨hx, k, hk⟩ => ⟨hNK hx, k, hk⟩, fun ⟨hx, k, hk⟩ => ⟨h x hx k hk, k, hk⟩⟩

theorem inSubgroup_oResidual_eq_of_le {p : ℕ} {N K : Subgroup G} (hNK : N ≤ K)
    (h : ∀ x ∈ K, Nat.Coprime (orderOf x) p → x ∈ N) :
    inSubgroup (oResidual p) N = inSubgroup (oResidual p) K := by
  rw [inSubgroup_oResidual_eq_closure, inSubgroup_oResidual_eq_closure]
  congr 1
  ext x
  exact ⟨fun ⟨hx, hc⟩ => ⟨hNK hx, hc⟩, fun ⟨hx, hc⟩ => ⟨h x hx hc, hc⟩⟩

theorem oPrimeResidualOf_le_self (p : ℕ) (K : Subgroup G) : oPrimeResidualOf p K ≤ K :=
  Subgroup.map_subtype_le _

theorem inSubgroup_oResidual_le_self (p : ℕ) (K : Subgroup G) :
    inSubgroup (oResidual p) K ≤ K :=
  Subgroup.map_subtype_le _

theorem le_normalizer_closure_of_forall_conj {H : Subgroup G} {s : Set G}
    (hs : ∀ h ∈ H, ∀ x ∈ s, h * x * h⁻¹ ∈ s) :
    H ≤ Subgroup.normalizer ((Subgroup.closure s : Subgroup G) : Set G) := by
  intro h hh
  have key : ∀ g ∈ H, ∀ y ∈ Subgroup.closure s, g * y * g⁻¹ ∈ Subgroup.closure s := by
    intro g hg y hy
    induction hy using Subgroup.closure_induction with
    | mem x hx => exact Subgroup.subset_closure (hs g hg x hx)
    | one => simp
    | mul x y _ _ hx hy =>
      have e : g * (x * y) * g⁻¹ = (g * x * g⁻¹) * (g * y * g⁻¹) := by group
      rw [e]
      exact mul_mem hx hy
    | inv x _ hx =>
      have e : g * x⁻¹ * g⁻¹ = (g * x * g⁻¹)⁻¹ := by group
      rw [e]
      exact inv_mem hx
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · exact key h hh y
  · intro hy
    have := key h⁻¹ (inv_mem hh) _ hy
    simpa [mul_assoc] using this

theorem le_normalizer_oPrimeResidualOf {p : ℕ} {H K : Subgroup G}
    (hHK : H ≤ Subgroup.normalizer (K : Set G)) :
    H ≤ Subgroup.normalizer (oPrimeResidualOf p K : Set G) := by
  rw [oPrimeResidualOf_eq_closure]
  refine le_normalizer_closure_of_forall_conj fun h hh x ⟨hx, k, hk⟩ => ⟨?_, k, ?_⟩
  · exact (Subgroup.mem_normalizer_iff.mp (hHK hh) x).mp hx
  · rw [conj_pow, hk, mul_one, mul_inv_cancel]

theorem le_normalizer_inSubgroup_oResidual {p : ℕ} {H K : Subgroup G}
    (hHK : H ≤ Subgroup.normalizer (K : Set G)) :
    H ≤ Subgroup.normalizer (inSubgroup (oResidual p) K : Set G) := by
  rw [inSubgroup_oResidual_eq_closure]
  refine le_normalizer_closure_of_forall_conj fun h hh x ⟨hx, hc⟩ => ⟨?_, ?_⟩
  · exact (Subgroup.mem_normalizer_iff.mp (hHK hh) x).mp hx
  · have e := (MulAut.conj h).orderOf_eq x
    rw [MulAut.conj_apply] at e
    rwa [e]

theorem le_normalizer_sup_commutator (D R : Subgroup G) :
    R ≤ Subgroup.normalizer ((D ⊔ ⁅D, R⁆ : Subgroup G) : Set G) := by
  have hRC : R ≤ Subgroup.normalizer ((⁅D, R⁆ : Subgroup G) : Set G) :=
    Subgroup.normalizer_commutator_ge_right D R
  have hDC : D ≤ Subgroup.normalizer ((⁅D, R⁆ : Subgroup G) : Set G) :=
    Subgroup.normalizer_commutator_ge_left D R
  have key : ∀ r ∈ R, ∀ y ∈ D ⊔ ⁅D, R⁆, r * y * r⁻¹ ∈ D ⊔ ⁅D, R⁆ := by
    intro r hr y hy
    rw [sup_comm] at hy ⊢
    have hy' : y ∈ (((⁅D, R⁆ : Subgroup G) : Set G) * (D : Set G)) := by
      rw [← Subgroup.coe_mul_of_right_le_normalizer_left _ D hDC]
      exact hy
    obtain ⟨c, hc, d, hd, rfl⟩ := hy'
    have e : r * (c * d) * r⁻¹ = (r * c * r⁻¹) * ((r * d * r⁻¹ * d⁻¹) * d) := by group
    rw [e]
    refine mul_mem (Subgroup.mem_sup_left ?_) (mul_mem (Subgroup.mem_sup_left ?_)
      (Subgroup.mem_sup_right hd))
    · exact (Subgroup.mem_normalizer_iff.mp (hRC hr) c).mp hc
    · rw [Subgroup.commutator_comm]
      exact Subgroup.commutator_mem_commutator hr hd
  intro r hr
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · exact key r hr y
  · intro hy
    have := key r⁻¹ (inv_mem hr) _ hy
    simpa [mul_assoc] using this

section CharP

variable {K : Type*} [Group K] {p : ℕ}

theorem pCore_map_normal (N : Subgroup K) [N.Normal] :
    ((CFSG.pCore p ↥N).map N.subtype).Normal := by
  refine ⟨fun x hx k => ?_⟩
  obtain ⟨y, hy, rfl⟩ := hx
  have h := CFSG.pCore_map_iso p (MulAut.conjNormal (H := N) k)
  have hmem : MulAut.conjNormal (H := N) k y ∈ CFSG.pCore p ↥N := by
    rw [← h]
    exact ⟨y, hy, rfl⟩
  refine ⟨_, hmem, ?_⟩
  simp [MulAut.conjNormal_apply]

theorem pCore_map_le_pCore (N : Subgroup K) [N.Normal] :
    (CFSG.pCore p ↥N).map N.subtype ≤ CFSG.pCore p K :=
  le_sSup ⟨pCore_map_normal N, CFSG.pCore_isPGroup.map _⟩

theorem isCharacteristicP_of_mulEquiv' {K' : Type*} [Group K'] (e : K ≃* K')
    (h : IsCharacteristicP p K) : IsCharacteristicP p K' := by
  change Subgroup.centralizer (CFSG.pCore p K' : Set K') ≤ CFSG.pCore p K'
  rw [← CFSG.pCore_map_iso p e, ← CFSG.RankThreeEvenClassification.Helpers.centralizer_map_equiv]
  exact Subgroup.map_mono h

theorem isCharacteristicP_of_isPGroup_quotient (N : Subgroup K) [N.Normal]
    (hq : IsPGroup p (K ⧸ N)) (hN : IsCharacteristicP p ↥N) : IsCharacteristicP p K := by
  change Subgroup.centralizer (CFSG.pCore p K : Set K) ≤ CFSG.pCore p K
  set C := Subgroup.centralizer (CFSG.pCore p K : Set K)
  set Q := (CFSG.pCore p ↥N).map N.subtype
  have hQ : Q ≤ CFSG.pCore p K := pCore_map_le_pCore N
  have hCN : ∀ c ∈ C, c ∈ N → c ∈ Q := by
    intro c hc hcN
    refine ⟨⟨c, hcN⟩, hN ?_, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    apply Subtype.ext
    have := Subgroup.mem_centralizer_iff.mp hc (y : K) (hQ ⟨y, hy, rfl⟩)
    simpa using this
  have hQp : IsPGroup p Q := CFSG.pCore_isPGroup.map _
  have hCp : IsPGroup p C := by
    intro c
    obtain ⟨a, ha⟩ := hq (QuotientGroup.mk (c : K))
    have hcN : (c : K) ^ p ^ a ∈ N := by
      rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow, ha]
    have hcQ : (c : K) ^ p ^ a ∈ Q := hCN _ (pow_mem c.2 _) hcN
    obtain ⟨b, hb⟩ := hQp ⟨_, hcQ⟩
    refine ⟨a + b, Subtype.ext ?_⟩
    have hb' : ((c : K) ^ p ^ a) ^ p ^ b = 1 := by
      have := congrArg Subtype.val hb
      simpa using this
    rw [Subgroup.coe_pow, Subgroup.coe_one, pow_add, pow_mul, hb']
  have hCn : C.Normal := Subgroup.normal_centralizer
  exact le_sSup ⟨hCn, hCp⟩

theorem isCharacteristicP_of_pCore_le (J : Subgroup K) (hK : IsCharacteristicP p K)
    (hPJ : CFSG.pCore p K ≤ J) : IsCharacteristicP p ↥J := by
  change Subgroup.centralizer (CFSG.pCore p ↥J : Set ↥J) ≤ CFSG.pCore p ↥J
  have hPJ' : (CFSG.pCore p K).subgroupOf J ≤ CFSG.pCore p ↥J := by
    refine le_sSup ⟨?_, ?_⟩
    · exact Subgroup.Normal.subgroupOf CFSG.pCore_normal J
    · exact (CFSG.pCore_isPGroup).comap_of_injective (J.subtype) J.subtype_injective
  intro x hx
  have hxK : (x : K) ∈ CFSG.pCore p K := by
    refine hK (Subgroup.mem_centralizer_iff.mpr fun y hy => ?_)
    have hyJ : y ∈ J := hPJ hy
    have := Subgroup.mem_centralizer_iff.mp hx ⟨y, hyJ⟩ (hPJ' (Subgroup.mem_subgroupOf.mpr hy))
    simpa using congrArg Subtype.val this
  exact hPJ' (Subgroup.mem_subgroupOf.mpr hxK)

variable [Finite K] [Fact p.Prime]

theorem isCharacteristicP_of_normal (N : Subgroup K) [N.Normal] (hK : IsCharacteristicP p K) :
    IsCharacteristicP p ↥N := by
  have hKF := (isCharacteristicP_iff_generalizedFitting_eq_pCore K p).mp hK
  have hmono := CFSG.ComponentClassification.GeneralizedFitting.normal_monotone N
  rw [← generalizedFitting_eq_componentClassification,
    ← generalizedFitting_eq_componentClassification, hKF] at hmono
  have hFp : IsPGroup p ↥(generalizedFitting ↥N) := by
    have h := (CFSG.pCore_isPGroup (p := p) (G := K)).to_le hmono
    exact h.of_injective ((generalizedFitting ↥N).equivMapOfInjective N.subtype
      N.subtype_injective).toMonoidHom (MulEquiv.injective _)
  have hFn : (generalizedFitting ↥N).Normal := by
    rw [generalizedFitting_eq_componentClassification]
    exact CFSG.ComponentClassification.GeneralizedFitting.normal _
  have hFO : generalizedFitting ↥N ≤ CFSG.pCore p ↥N := le_sSup ⟨hFn, hFp⟩
  change Subgroup.centralizer (CFSG.pCore p ↥N : Set ↥N) ≤ CFSG.pCore p ↥N
  exact (Subgroup.centralizer_le hFO).trans
    ((centralizer_generalizedFitting_le ↥N).trans hFO)

end CharP

theorem map_mk_normal_iff {X Y : Subgroup G} (hXY : X ≤ Y) :
    ((X.subgroupOf Y).map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥Y))).Normal ↔
      Y ≤ Subgroup.normalizer ((X ⊔ pPrimeCoreOf 3 Y : Subgroup G) : Set G) := by
  have hRY : pPrimeCoreOf 3 Y ≤ Y := pPrimeCoreOf_le 3 Y
  have hsub : (X ⊔ pPrimeCoreOf 3 Y).subgroupOf Y = X.subgroupOf Y ⊔ CFSG.pPrimeCore 3 ↥Y := by
    rw [Subgroup.subgroupOf_sup hXY hRY]
    congr 1
    unfold pPrimeCoreOf
    exact Subgroup.comap_map_eq_self_of_injective Y.subtype_injective _
  rw [← Subgroup.normal_subgroupOf_iff_le_normalizer (sup_le hXY hRY), hsub]
  constructor
  · intro h
    have h' := h.comap (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥Y))
    rwa [Subgroup.comap_map_eq, QuotientGroup.ker_mk'] at h'
  · intro h
    have h' := h.map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥Y)) (QuotientGroup.mk'_surjective _)
    have hN : (CFSG.pPrimeCore 3 ↥Y).map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥Y)) = ⊥ := by
      rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
    rwa [Subgroup.map_sup, hN, sup_bot_eq] at h'

end CFSG.RankThree.PartTwo.Sec14
