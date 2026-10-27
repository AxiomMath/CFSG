module

public import CFSG.Foundations.Basic

public section

namespace CFSG.LocalAnalysis

open Subgroup MulAction

theorem eq_of_sq_eq_one_of_isCyclic {Q : Type*} [Group Q] [Finite Q] [IsCyclic Q] {a b : Q}
    (ha : a ^ 2 = 1) (hb : b ^ 2 = 1) (ha1 : a ≠ 1) (hb1 : b ≠ 1) : a = b := by
  classical
  let := Fintype.ofFinite Q
  by_contra hab
  have h := IsCyclic.card_pow_eq_one_le (α := Q) (n := 2) two_pos
  have hsub : ({1, a, b} : Finset Q) ⊆ Finset.univ.filter (fun c => c ^ 2 = 1) := by
    intro c hc
    simp only [Finset.mem_insert, Finset.mem_singleton] at hc
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rcases hc with rfl | rfl | rfl
    · exact one_pow 2
    · exact ha
    · exact hb
  have hcard : ({1, a, b} : Finset Q).card = 3 := by
    rw [Finset.card_insert_of_notMem, Finset.card_pair hab]
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨Ne.symm ha1, Ne.symm hb1⟩
  have := Finset.card_le_card hsub
  omega

theorem exists_normal_index_two_of_ne_one {G A : Type*} [Group G] [CommGroup A] [Finite A]
    (hA : IsPGroup 2 A) (T : G →* A) {x : G} (hx : T x ≠ 1) :
    ∃ M : Subgroup G, M.Normal ∧ M.index = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp (hA.to_subgroup T.range)
  have hk0 : k ≠ 0 := by
    rintro rfl
    rw [pow_zero, Subgroup.card_eq_one] at hk
    have h1 : T x ∈ T.range := ⟨x, rfl⟩
    rw [hk, Subgroup.mem_bot] at h1
    exact hx h1
  obtain ⟨K, hK⟩ := Sylow.exists_subgroup_card_pow_prime (G := T.range) 2 (n := k - 1)
    (by rw [hk]; exact pow_dvd_pow 2 (Nat.sub_le k 1))
  have hKidx : K.index = 2 := by
    have h1 := K.card_mul_index
    rw [hK, hk, show k = k - 1 + 1 by omega, pow_succ, Nat.add_sub_cancel] at h1
    exact Nat.eq_of_mul_eq_mul_left (pow_pos two_pos _) h1
  refine ⟨K.comap T.rangeRestrict,
    Subgroup.Normal.comap (Subgroup.normal_of_isMulCommutative K) _, ?_⟩
  rw [Subgroup.index_comap_of_surjective K T.rangeRestrict_surjective, hKidx]

theorem cyclic_two_quotient_transfer_centralizer_preserving_fusion {G : Type*} [Group G]
    [Finite G] (hG : ∀ M : Subgroup G, M.Normal → M.index ≠ 2) (S : Sylow 2 G)
    {N : Subgroup G} (hNS : N ≤ S) [hN : (N.subgroupOf (S : Subgroup G)).Normal]
    (hcyc : IsCyclic ((S : Subgroup G) ⧸ N.subgroupOf (S : Subgroup G))) {x : G} (hxS : x ∈ S)
    (_hxN : x ∉ N) (hx : orderOf x = 2) :
    ∃ g : G, g⁻¹ * x * g ∈ N ∧
      CFSG.conjugate ((S : Subgroup G) ⊓ centralizer {x}) g ≤ S := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set H : Subgroup G := (S : Subgroup G) with hHdef
  have hx2 : x ^ 2 = 1 := by rw [← hx]; exact pow_orderOf_eq_one x
  have hNconj : ∀ n ∈ N, ∀ h ∈ H, h * n * h⁻¹ ∈ N := by
    intro n hn h hh
    have := hN.conj_mem ⟨n, hNS hn⟩ (Subgroup.mem_subgroupOf.mpr hn) ⟨h, hh⟩
    exact Subgroup.mem_subgroupOf.mp this
  have hrep : ∀ a b : G, (a : G ⧸ H) = b → (a⁻¹ * x * a ∈ N ↔ b⁻¹ * x * b ∈ N) := by
    intro a b hab
    have hh : a⁻¹ * b ∈ H := QuotientGroup.eq.mp hab
    constructor
    · intro h1
      have := hNconj _ h1 _ (H.inv_mem hh)
      rwa [show (a⁻¹ * b)⁻¹ * (a⁻¹ * x * a) * (a⁻¹ * b)⁻¹⁻¹ = b⁻¹ * x * b by group] at this
    · intro h1
      have := hNconj _ h1 _ hh
      rwa [show a⁻¹ * b * (b⁻¹ * x * b) * (a⁻¹ * b)⁻¹ = a⁻¹ * x * a by group] at this
  set P : Subgroup G := H ⊓ centralizer {x} with hPdef
  have hPp : IsPGroup 2 P := S.isPGroup'.to_le inf_le_left
  have hxP : x ∈ P := ⟨hxS, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩
  let Y : SubMulAction P (G ⧸ H) :=
    { carrier := {ω | x • ω = ω ∧ (Quotient.out ω)⁻¹ * x * Quotient.out ω ∉ N}
      smul_mem' := by
        rintro ⟨p, hpH, hpx⟩ ω ⟨hω1, hω2⟩
        have hpx' : p * x = x * p := Subgroup.mem_centralizer_singleton_iff.mp hpx
        refine ⟨?_, ?_⟩
        · change x • p • ω = p • ω
          rw [smul_smul, ← hpx', mul_smul, hω1]
        · have h1 : ((Quotient.out ((⟨p, hpH, hpx⟩ : P) • ω) : G) : G ⧸ H) =
              ((p * Quotient.out ω : G) : G ⧸ H) := by
            rw [QuotientGroup.out_eq', ← smul_eq_mul, ← MulAction.Quotient.smul_mk,
              QuotientGroup.out_eq']
            rfl
          rw [hrep _ _ h1, show (p * Quotient.out ω)⁻¹ * x * (p * Quotient.out ω) =
            (Quotient.out ω)⁻¹ * (p⁻¹ * (x * p)) * Quotient.out ω by group, ← hpx',
            inv_mul_cancel_left]
          exact hω2 }
  by_contra hcon
  push Not at hcon
  have hmemY : ∀ ω : G ⧸ H, ω ∈ fixedPoints P (G ⧸ H) → ω ∈ Y := by
    intro ω hω
    set a := Quotient.out ω with ha
    have hconj : CFSG.conjugate P a ≤ H := by
      rintro _ ⟨c, hc, rfl⟩
      have h1 : (⟨c, hc⟩ : P) • ω = ω := hω ⟨c, hc⟩
      have h2 : ((c * a : G) : G ⧸ H) = (a : G ⧸ H) := by
        rw [← smul_eq_mul, ← MulAction.Quotient.smul_mk, ha, QuotientGroup.out_eq']
        exact h1
      have h3 : a⁻¹ * (c * a) ∈ H := by
        have := H.inv_mem (QuotientGroup.eq.mp h2)
        rwa [mul_inv_rev, inv_inv] at this
      change a⁻¹ * c * a⁻¹⁻¹ ∈ H
      rwa [inv_inv, mul_assoc]
    refine ⟨hω ⟨x, hxP⟩, fun h => hcon a h hconj⟩
  have hfix : Nat.card (fixedPoints P Y) = Nat.card (fixedPoints P (G ⧸ H)) :=
    Nat.card_congr
      { toFun := fun y => ⟨(y.1 : G ⧸ H), fun p => congrArg Subtype.val (y.2 p)⟩
        invFun := fun ω => ⟨⟨ω.1, hmemY ω.1 ω.2⟩, fun p => Subtype.ext (ω.2 p)⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
  have hYodd : Nat.card Y % 2 = 1 := by
    have h1 := hPp.card_modEq_card_fixedPoints Y
    have h2 := hPp.card_modEq_card_fixedPoints (G ⧸ H)
    have h3 : Nat.card (G ⧸ H) % 2 = 1 := Nat.two_dvd_ne_zero.mp S.not_dvd_index
    rw [hfix] at h1
    unfold Nat.ModEq at h1 h2
    omega
  let : CommGroup (H ⧸ N.subgroupOf H) := IsCyclic.commGroup
  set φ : H →* H ⧸ N.subgroupOf H := QuotientGroup.mk' (N.subgroupOf H) with hφ
  let _ : Fintype (Quotient (orbitRel (zpowers x) (G ⧸ H))) := Fintype.ofFinite _
  have hT := MonoidHom.transfer_eq_prod_quotient_orbitRel_zpowers_quot φ x
  set F : Quotient (orbitRel (zpowers x) (G ⧸ H)) → H ⧸ N.subgroupOf H := fun q =>
    φ ⟨(Quotient.out (Quotient.out q))⁻¹ * x ^ Function.minimalPeriod (x • ·) (Quotient.out q) *
      Quotient.out (Quotient.out q), QuotientGroup.out_conj_pow_minimalPeriod_mem H x _⟩ with hF
  have hF1 : ∀ q, F q ^ 2 = 1 := by
    intro q
    rw [hF, ← map_pow]
    convert map_one φ
    apply Subtype.ext
    rw [Subgroup.coe_pow, OneMemClass.coe_one]
    set a := Quotient.out (Quotient.out q)
    set r := Function.minimalPeriod (x • ·) (Quotient.out q)
    rw [sq, show a⁻¹ * x ^ r * a * (a⁻¹ * x ^ r * a) = a⁻¹ * (x ^ r * x ^ r) * a by group,
      ← pow_add, ← two_mul, pow_mul, hx2, one_pow, mul_one, inv_mul_cancel]
  have hperiod : ∀ ω : G ⧸ H, Function.minimalPeriod (x • ·) ω = 1 ∨
      Function.minimalPeriod (x • ·) ω = 2 := by
    intro ω
    have hp : Function.IsPeriodicPt (x • ·) 2 ω := by
      change (x • · : G ⧸ H → G ⧸ H)^[2] ω = ω
      rw [smul_iterate, hx2]
      exact one_smul _ ω
    exact (Nat.dvd_prime Nat.prime_two).mp hp.minimalPeriod_dvd
  have hF2 : ∀ q, F q ≠ 1 ↔ Quotient.out q ∈ Y := by
    intro q
    have h1 : F q = 1 ↔ (Quotient.out (Quotient.out q))⁻¹ *
        x ^ Function.minimalPeriod (x • ·) (Quotient.out q) *
          Quotient.out (Quotient.out q) ∈ N := by
      rw [hF]
      beta_reduce
      rw [hφ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    rw [Ne, h1]
    rcases hperiod (Quotient.out q) with h | h
    · rw [h, pow_one]
      have hfixed : x • Quotient.out q = Quotient.out q :=
        Function.minimalPeriod_eq_one_iff_isFixedPt.mp h
      exact ⟨fun h2 => ⟨hfixed, h2⟩, fun h2 => h2.2⟩
    · rw [h, hx2, mul_one, inv_mul_cancel]
      refine ⟨fun h2 => absurd N.one_mem h2, fun h2 => ?_⟩
      have h3 : Function.minimalPeriod (x • ·) (Quotient.out q) = 1 :=
        Function.minimalPeriod_eq_one_iff_isFixedPt.mpr h2.1
      omega
  have hout : ∀ ω : G ⧸ H, ω ∈ Y →
      Quotient.out (Quotient.mk (orbitRel (zpowers x) (G ⧸ H)) ω) = ω := by
    intro ω hω
    obtain ⟨⟨g, hg⟩, hgω⟩ :=
      (orbitRel_apply).mp (Quotient.mk_out (s := orbitRel (zpowers x) (G ⧸ H)) ω)
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
    have hst : x ∈ stabilizer G ω := mem_stabilizer_iff.mpr hω.1
    rw [← hgω]
    exact mem_stabilizer_iff.mp (Subgroup.zpow_mem _ hst k)
  obtain ⟨ω₀⟩ : Nonempty Y := (Nat.card_ne_zero.mp (by omega)).1
  set q₀ := Quotient.mk (orbitRel (zpowers x) (G ⧸ H)) (ω₀ : G ⧸ H) with hq₀def
  have hq₀ : Quotient.out q₀ ∈ Y := by rw [hout _ ω₀.2]; exact ω₀.2
  set ε := F q₀ with hεdef
  have hε1 : ε ≠ 1 := (hF2 q₀).mpr hq₀
  have hε2 : ε ^ 2 = 1 := hF1 q₀
  have hFε : ∀ q, F q = if Quotient.out q ∈ Y then ε else 1 := by
    intro q
    split_ifs with h
    · exact eq_of_sq_eq_one_of_isCyclic (hF1 q) hε2 ((hF2 q).mpr h) hε1
    · by_contra h'
      exact h ((hF2 q).mp h')
  have hcardY : (Finset.univ.filter fun q : Quotient (orbitRel (zpowers x) (G ⧸ H)) =>
      Quotient.out q ∈ Y).card = Nat.card Y := by
    rw [← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
    exact Nat.card_congr
      { toFun := fun q => ⟨Quotient.out q.1, q.2⟩
        invFun := fun ω => ⟨Quotient.mk _ (ω : G ⧸ H), by rw [hout _ ω.2]; exact ω.2⟩
        left_inv := fun q => Subtype.ext (Quotient.out_eq q.1)
        right_inv := fun ω => Subtype.ext (hout _ ω.2) }
  have hTx : φ.transfer x = ε := by
    rw [hT]
    change ∏ q, F q = ε
    rw [Finset.prod_congr rfl fun q _ => hFε q, Finset.prod_ite, Finset.prod_const,
      Finset.prod_const_one, mul_one, hcardY]
    obtain ⟨m, hm⟩ : ∃ m, Nat.card Y = 2 * m + 1 := ⟨Nat.card Y / 2, by omega⟩
    rw [hm, pow_succ, pow_mul, hε2, one_pow, one_mul]
  obtain ⟨M, hMn, hM2⟩ := exists_normal_index_two_of_ne_one (S.isPGroup'.to_quotient _)
    φ.transfer (x := x) (by rw [hTx]; exact hε1)
  exact hG M hMn hM2

end CFSG.LocalAnalysis
