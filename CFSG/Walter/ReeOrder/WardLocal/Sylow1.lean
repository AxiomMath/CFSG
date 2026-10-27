module

public import CFSG.Walter.ReeOrder.WardLocal.CentT

public section

open scoped BigOperators Classical MatrixGroups

namespace CFSG.Walter.WardLocal

open CFSG.Walter.Ward CFSG.Walter.JT

variable {G : Type} [Group G] [Fintype G] {K : Type} [Field K] [Fintype K] [DecidableEq K]
  {q : ℕ} (S : WardSetup G PSL(2, K) q (-1))

@[expose] noncomputable def FF : Subgroup G := (pslE K).map S.κ

@[expose] noncomputable def TT : G := S.κ (pslU 1)

@[expose] noncomputable def RR : Subgroup G := (Subgroup.zpowers (dgen K)).map S.κ

variable {S}

theorem mem_FF {x : G} : x ∈ FF S ↔ ∃ b : K, S.κ (pslU b) = x := by
  simp only [FF, Subgroup.mem_map, mem_pslE_iff]
  constructor
  · rintro ⟨y, ⟨b, rfl⟩, rfl⟩; exact ⟨b, rfl⟩
  · rintro ⟨b, rfl⟩; exact ⟨pslU b, ⟨b, rfl⟩, rfl⟩

theorem card_FF : Nat.card (FF S) = Fintype.card K := by
  rw [FF, Subgroup.card_map_of_injective S.κ_inj, card_pslE, Nat.card_eq_fintype_card]

theorem FF_comm {x y : G} (hx : x ∈ FF S) (hy : y ∈ FF S) : x * y = y * x := by
  obtain ⟨b, rfl⟩ := mem_FF.mp hx
  obtain ⟨c, rfl⟩ := mem_FF.mp hy
  rw [← map_mul, ← map_mul, pslU_mul, pslU_mul, add_comm]

theorem FF_pow_three [CharP K 3] {x : G} (hx : x ∈ FF S) : x ^ 3 = 1 := by
  obtain ⟨b, rfl⟩ := mem_FF.mp hx
  rw [← map_pow, pslU_pow_three, map_one]

theorem FF_comm_J {x : G} (hx : x ∈ FF S) : x * S.J = S.J * x := by
  obtain ⟨b, rfl⟩ := mem_FF.mp hx
  exact S.κ_comm _

theorem TT_mem : TT S ∈ FF S := mem_FF.mpr ⟨1, rfl⟩

theorem orderOf_TT [CharP K 3] : orderOf (TT S) = 3 := by
  rw [TT, S.orderOf_κ, Block.orderOf_pslU one_ne_zero]

theorem mem_RR {x : G} : x ∈ RR S ↔ ∃ j : ℕ, S.κ (dgen K ^ j) = x := by
  simp only [RR, Subgroup.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨j, rfl⟩ := (mem_powers_iff_mem_zpowers.mpr hy)
    exact ⟨j, rfl⟩
  · rintro ⟨j, rfl⟩
    exact ⟨_, Subgroup.pow_mem _ (Subgroup.mem_zpowers _) j, rfl⟩

theorem RR_comm_J {x : G} (hx : x ∈ RR S) : x * S.J = S.J * x := by
  obtain ⟨j, rfl⟩ := mem_RR.mp hx
  exact S.κ_comm _

theorem RR_le_normalizer : RR S ≤ Subgroup.normalizer (FF S : Set G) := by
  rw [RR, FF]
  refine le_trans (Subgroup.map_mono ?_) (Subgroup.le_normalizer_map S.κ)
  rw [Subgroup.zpowers_le, dgen_eq]
  exact pslD_mem_normalizer (gen K)

theorem card_centralizer_of_isConj {x y : G} (h : IsConj x y) :
    Nat.card (Subgroup.centralizer ({x} : Set G)) = Nat.card (Subgroup.centralizer ({y} : Set G)) :=
  by
  have hx := CFSG.SmallDefect.card_conjClass_mul_card_centralizer x
  have hy := CFSG.SmallDefect.card_conjClass_mul_card_centralizer y
  rw [ConjClasses.mk_eq_mk_iff_isConj.mpr h] at hx
  have hpos : 0 < Nat.card (ConjClasses.mk y).carrier := by
    rcases Nat.eq_zero_or_pos (Nat.card (ConjClasses.mk y).carrier) with h0 | h0
    · rw [h0, zero_mul] at hy; exact absurd hy.symm Nat.card_pos.ne'
    · exact h0
  exact Nat.eq_of_mul_eq_mul_left hpos (hx.trans hy.symm)

variable (hK : Fintype.card K = q)
include hK

theorem card_RR {k : ℕ} (hq : q = 3 ^ (2 * k + 1)) : 2 * Nat.card (RR S) + 1 = q := by
  obtain ⟨k', hk', -⟩ := Block.q_half hq
  rw [RR, Subgroup.card_map_of_injective S.κ_inj, Nat.card_zpowers,
    orderOf_dgen (hK.trans hk'), hk']

theorem card_centralizer_RR {k : ℕ} (hq : q = 3 ^ (2 * k + 1)) {x : G} (hx : x ∈ RR S)
    (hx1 : x ≠ 1) : Nat.card (Subgroup.centralizer ({x} : Set G)) = q - 1 := by
  obtain ⟨j, rfl⟩ := mem_RR.mp hx
  have hRo : 2 * Nat.card S.W.Ro + 1 = q := by have := S.W.Ro_card; omega
  have hcR := card_RR (S := S) hK hq
  have hord : orderOf (dgen K ^ j) ∣ Nat.card S.W.Ro := by
    have h1 : Nat.card S.W.Ro = Nat.card (RR S) := by omega
    rw [h1, RR, Subgroup.card_map_of_injective S.κ_inj, Nat.card_zpowers]
    exact orderOf_pow_dvd j
  obtain ⟨g, hg⟩ := S.W.Ro_conj _ hord
  have hg1 : g⁻¹ * dgen K ^ j * g ≠ 1 := by
    intro h
    apply hx1
    have : dgen K ^ j = 1 := by
      have := congrArg (fun t => g * t * g⁻¹) h
      simpa [mul_assoc] using this
    rw [this, map_one]
  have hconj : IsConj (S.κ (dgen K ^ j)) (S.κ (g⁻¹ * dgen K ^ j * g)) := by
    refine isConj_iff.mpr ⟨S.κ g⁻¹, ?_⟩
    simp only [map_mul, map_inv, inv_inv]
  rw [card_centralizer_of_isConj hconj, S.card_centralizer_κR hg hg1,
    S.W.Ro_centralizer _ hg hg1]
  omega

theorem not_three_dvd_of_commute_RR {k : ℕ} (hq : q = 3 ^ (2 * k + 1)) {d x : G}
    (hd : d ∈ RR S) (hd1 : d ≠ 1) (hxd : x * d = d * x) : ¬ 3 ∣ orderOf x := by
  intro h3
  have hmem : x ∈ Subgroup.centralizer ({d} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr hxd
  have hdvd := Subgroup.orderOf_dvd_natCard _ hmem
  rw [card_centralizer_RR hK hq hd hd1] at hdvd
  have h3q : 3 ∣ q := hq ▸ dvd_pow_self 3 (by omega)
  have hq1 : 1 ≤ q := by rw [hq]; exact Nat.one_le_pow _ _ (by norm_num)
  have := h3.trans hdvd
  omega

omit hK [DecidableEq K] in
theorem exists_conj_pslE {k : ℕ} (hq : q = 3 ^ (2 * k + 1)) (hK : Fintype.card K = q)
    [CharP K 3] {y : PSL(2, K)} (hy : IsPGroup 3 (Subgroup.zpowers y)) :
    ∃ g : PSL(2, K), g⁻¹ * y * g ∈ pslE K := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hKc : Nat.card K = 3 ^ (2 * k + 1) := by rw [Nat.card_eq_fintype_card, hK, hq]
  apply exists_conj_mem_of_full _ _ hy
  have h1 := psl2_card_sylow_p hKc (by norm_num) (by omega) (default : Sylow 3 PSL(2, K))
  rw [Sylow.card_eq_multiplicity] at h1
  rw [h1, card_pslE, hKc]

omit hK in
theorem isConj_T_of_commute {k : ℕ} (hq : q = 3 ^ (2 * k + 1)) (hK : Fintype.card K = q)
    [CharP K 3] {x t : G} (hx1 : x ≠ 1) (hx : IsPGroup 3 (Subgroup.zpowers x))
    (ht : orderOf t = 2) (hxt : x * t = t * x) :
    IsConj x (TT S) ∨ IsConj x (TT S)⁻¹ := by
  obtain ⟨c, hc⟩ := isConj_iff.mp (S.involution_conj t ht)
  set x' := c * x * c⁻¹ with hx'
  have hx'J : x' * S.J = S.J * x' := by
    rw [← hc, hx']
    calc c * x * c⁻¹ * (c * t * c⁻¹) = c * (x * t) * c⁻¹ := by group
      _ = c * (t * x) * c⁻¹ := by rw [hxt]
      _ = c * t * c⁻¹ * (c * x * c⁻¹) := by group
  have hox : orderOf x' = orderOf x := by
    rw [hx', ← MulAut.conj_apply, MulEquiv.orderOf_eq]
  obtain ⟨N, hN⟩ := (IsPGroup.iff_orderOf.mp hx) ⟨x, Subgroup.mem_zpowers x⟩
  rw [Subgroup.orderOf_mk] at hN
  have hodd : Odd (orderOf x') := by
    rw [hox, hN]; exact Odd.pow (by decide)
  obtain ⟨y, hy⟩ := S.odd_mem_κ hx'J hodd
  have hoy : orderOf y = 3 ^ N := by rw [← S.orderOf_κ, ← hy, hox, hN]
  have hyp : IsPGroup 3 (Subgroup.zpowers y) := by
    apply IsPGroup.of_card (n := N)
    rw [Nat.card_zpowers, hoy]
  obtain ⟨g, hg⟩ := exists_conj_pslE hq hK hyp
  obtain ⟨b, hb⟩ := mem_pslE_iff.mp hg
  have hb0 : b ≠ 0 := by
    rintro rfl
    rw [pslU_zero] at hb
    have : y = 1 := by
      have := congrArg (fun t => g * t * g⁻¹) hb.symm
      simpa [mul_assoc] using this
    rw [this, map_one] at hy
    apply hx1
    have := congrArg (fun t => c⁻¹ * t * c) hy
    simpa [hx', mul_assoc] using this
  obtain ⟨k', hk', hodd'⟩ := Block.q_half hq
  obtain ⟨j, hj | hj⟩ := conj_pslU (hK.trans hk') hodd' hb0
  · left
    refine isConj_iff.mpr ⟨(c⁻¹ * S.κ (g * dgen K ^ j))⁻¹, ?_⟩
    have hy' : y = g * (dgen K ^ j * pslU 1 * (dgen K ^ j)⁻¹) * g⁻¹ := by
      rw [hj, hb]; group
    have hxe : x = c⁻¹ * S.κ y * c := by rw [← hy, hx']; group
    rw [hxe, hy', TT]
    simp only [map_mul, map_inv]
    group
  · right
    refine isConj_iff.mpr ⟨(c⁻¹ * S.κ (g * dgen K ^ j))⁻¹, ?_⟩
    have hy' : y = g * (dgen K ^ j * (pslU 1)⁻¹ * (dgen K ^ j)⁻¹) * g⁻¹ := by
      rw [pslU_inv, hj, hb]; group
    have hxe : x = c⁻¹ * S.κ y * c := by rw [← hy, hx']; group
    rw [hxe, hy', TT]
    simp only [map_mul, map_inv]
    group

end CFSG.Walter.WardLocal
