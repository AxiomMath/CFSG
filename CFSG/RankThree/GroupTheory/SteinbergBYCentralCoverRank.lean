module

public import CFSG.RankThree.GroupTheory.SteinbergCDCentralElementaryRank
public import CFSG.RankThree.GroupTheory.SteinbergBYMinimalCoprimeAction
public import CFSG.RankThree.GroupTheory.SteinbergBYCentralQuotientTheta

public section

namespace CFSG.RankThree.GroupTheory.SteinbergBY

open CFSG Subgroup
open scoped commutatorElement

theorem le_pRank_of_elementaryAbelian_card {p : ℕ} (hp : 1 < p) {H : Type*} [Group H]
    [Finite H] {E : Subgroup H} (hE : IsElementaryAbelian p E) {k : ℕ}
    (hk : Nat.card E = p ^ k) : k ≤ pRank p H := by
  refine le_csSup ⟨Nat.card H, ?_⟩ ⟨E, hE, hk⟩
  rintro r ⟨B, -, hB⟩
  calc r ≤ p ^ r := (Nat.lt_pow_self hp).le
    _ = Nat.card B := hB.symm
    _ ≤ Nat.card H := Subgroup.card_le_card_group B

theorem pRank_subgroup_le_pRank {p : ℕ} (hp : 1 < p) {Y : Type*} [Group Y] [Finite Y]
    (F : Subgroup Y) : pRank p F ≤ pRank p Y := by
  rw [SectionRank.pRank_eq_open_pRank_top, SectionRank.pRank_eq_open_pRank_top]
  exact (SectionRank.pRank_le_map hp F.subtype F.subtype_injective ⊤).trans
    (SectionRank.pRank_mono hp le_top)

theorem commutatorElement_pow_left_of_le_center {F : Type*} [Group F]
    (hc : commutator F ≤ center F) (x y : F) (n : ℕ) : ⁅x ^ n, y⁆ = ⁅x, y⁆ ^ n := by
  rw [← commutatorElement_inv, commutatorElement_pow_right_of_le_center hc,
    ← commutatorElement_inv y x, inv_pow]

variable {Y T : Type*} [Group Y] [Group T] [Finite Y]

omit [Finite Y] in
theorem exists_quotient_comap_mulEquiv (φ : Y →* T) (hφ : Function.Surjective φ)
    (U : Subgroup T) :
    ∃ e : (U.comap φ) ⧸ φ.ker.subgroupOf (U.comap φ) ≃* U,
      ∀ x : U.comap φ, (e (x : (U.comap φ) ⧸ φ.ker.subgroupOf (U.comap φ)) : T) = φ x := by
  set F := U.comap φ
  set g : F →* U := (φ.comp F.subtype).codRestrict U fun x => x.2
  have hg : Function.Surjective g := by
    rintro ⟨u, hu⟩
    obtain ⟨y, rfl⟩ := hφ u
    exact ⟨⟨y, hu⟩, rfl⟩
  have hker : g.ker = φ.ker.subgroupOf F := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, MonoidHom.mem_ker]
    exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective g hg), fun x => rfl⟩

theorem four_le_pRank_of_central_cover {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) (φ : Y →* T)
    (hφ : Function.Surjective φ) (hker : φ.ker ≤ center Y) {U : Subgroup T}
    (hU : IsElementaryAbelian ℓ U) {r : ℕ} (hUcard : Nat.card U = ℓ ^ r) (hr : 6 ≤ r) :
    4 ≤ pRank ℓ Y := by
  by_contra hcon
  push Not at hcon
  set F := U.comap φ
  set Z := φ.ker.subgroupOf F
  have hZ : Z ≤ center F := fun x hx =>
    Subgroup.mem_center_iff.mpr fun y => Subtype.ext (Subgroup.mem_center_iff.mp (hker hx) y)
  have hFrank : pRank ℓ F ≤ 3 := by
    have := pRank_subgroup_le_pRank hℓ.one_lt F
    omega
  obtain ⟨e, -⟩ := exists_quotient_comap_mulEquiv φ hφ U
  have hd := central_elementary_odd_quotient_rank_three_bound hℓ hℓ2 hFrank Z hZ r
  have hel : IsElementaryAbelian ℓ (F ⧸ Z) := by
    have hc : IsMulCommutative (F ⧸ Z) :=
      ⟨⟨fun a b => e.injective (by
        rw [map_mul, map_mul]
        exact (IsMulCommutative.is_comm (M := U)).comm _ _)⟩⟩
    have hexp : Monoid.exponent (F ⧸ Z) ∣ ℓ := Monoid.exponent_dvd_of_forall_pow_eq_one fun a =>
      e.injective (by
        rw [map_pow, map_one]
        exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
          (IsElementaryAbelian.exponent_dvd_p ℓ U) _)
    exact ⟨hexp⟩
  have hcard : Nat.card (F ⧸ Z) = ℓ ^ r := by
    rw [Nat.card_congr e.toEquiv, hUcard]
  have := hd hel hcard
  omega

theorem le_pRank_of_central_cover_of_power_action {ℓ : ℕ} (hℓ : ℓ.Prime) (φ : Y →* T)
    (hφ : Function.Surjective φ) (hker : φ.ker ≤ center Y) {U : Subgroup T}
    (hU : IsElementaryAbelian ℓ U) {r : ℕ} (hUcard : Nat.card U = ℓ ^ r) {d : T} {s : ℕ}
    (hs : ¬ ℓ ∣ s ^ 2 - 1) (hs1 : 1 ≤ s) (hd : ∀ u ∈ U, d * u * d⁻¹ = u ^ s) :
    r ≤ pRank ℓ Y := by
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have := hU
  set F := U.comap φ with hF
  have hUcomm : ∀ a b : T, a ∈ U → b ∈ U → a * b = b * a := fun a b ha hb =>
    congrArg Subtype.val ((IsMulCommutative.is_comm (M := U)).comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hUpow : ∀ a ∈ U, a ^ ℓ = 1 := fun a ha => elemPow_eq_one_of_isElementaryAbelian a ha
  have hcommZ : ∀ x y : F, ⁅(x : Y), (y : Y)⁆ ∈ center Y := fun x y => hker (by
    rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact hUcomm _ _ x.2 y.2)
  have hFc : commutator F ≤ center F := by
    rw [commutator_eq_closure, Subgroup.closure_le]
    rintro _ ⟨x, y, rfl⟩
    exact Subgroup.mem_center_iff.mpr fun z => Subtype.ext
      (Subgroup.mem_center_iff.mp (hcommZ x y) z)
  have hpowker : ∀ x : F, (x : Y) ^ ℓ ∈ φ.ker := fun x => by
    rw [MonoidHom.mem_ker, map_pow]
    exact hUpow _ x.2
  obtain ⟨δ, hδ⟩ := hφ d
  have hδF : ∀ x : F, δ * x * δ⁻¹ ∈ F := fun x => by
    change φ (δ * x * δ⁻¹) ∈ U
    rw [map_mul, map_mul, map_inv, hδ, hd _ x.2]
    exact pow_mem (show φ x ∈ U from x.2) s
  have hδpow : ∀ x : F, ((x : Y) ^ s)⁻¹ * (δ * x * δ⁻¹) ∈ center Y := fun x => hker (by
    rw [MonoidHom.mem_ker, map_mul, map_inv, map_mul, map_mul, map_inv, hδ, hd _ x.2, map_pow,
      inv_mul_cancel])
  have key : ∀ a b : F, ((⁅a, b⁆ : F) : Y) = ⁅(a : Y), (b : Y)⁆ := fun a b =>
    map_commutatorElement F.subtype a b
  have hFab : ∀ x y : F, (x : Y) * y = y * x := by
    intro x y
    set c : Y := ⁅(x : Y), (y : Y)⁆ with hcdef
    have hcl : c ^ ℓ = 1 := by
      have h := commutatorElement_pow_left_of_le_center hFc x y ℓ
      have h' := congrArg (fun z : F => (z : Y)) h
      simp only [key, Subgroup.coe_pow] at h'
      rw [hcdef, ← h', commutatorElement_eq_one_iff_mul_comm]
      exact (Subgroup.mem_center_iff.mp (hker (hpowker x)) (y : Y)).symm
    have hcs : c ^ (s * s) = c := by
      have h1 : ⁅(x : Y) ^ s, (y : Y) ^ s⁆ = c ^ (s * s) := by
        have h := commutatorElement_pow_left_of_le_center hFc x (y ^ s) s
        rw [commutatorElement_pow_right_of_le_center hFc x y s, ← pow_mul] at h
        have h' := congrArg (fun z : F => (z : Y)) h
        simp only [key, Subgroup.coe_pow] at h'
        exact h'
      have h2 : ⁅δ * x * δ⁻¹, δ * y * δ⁻¹⁆ = δ * c * δ⁻¹ := by
        simp only [hcdef, commutatorElement_def]
        group
      have hc_cen : c ∈ center Y := hcommZ x y
      have h3 : δ * c * δ⁻¹ = c := by
        rw [Subgroup.mem_center_iff.mp hc_cen δ, mul_inv_cancel_right]
      have h4 : ⁅δ * x * δ⁻¹, δ * y * δ⁻¹⁆ = ⁅(x : Y) ^ s, (y : Y) ^ s⁆ := by
        have ex : δ * x * δ⁻¹ = (x : Y) ^ s * (((x : Y) ^ s)⁻¹ * (δ * x * δ⁻¹)) := by
          rw [mul_inv_cancel_left]
        have ey : δ * y * δ⁻¹ = (y : Y) ^ s * (((y : Y) ^ s)⁻¹ * (δ * y * δ⁻¹)) := by
          rw [mul_inv_cancel_left]
        rw [ex, ey, commutatorElement_mul_of_mem_center_left _ _ (hδpow x),
          commutatorElement_mul_of_mem_center_right _ _ (hδpow y)]
      rw [← h1, ← h4, h2, h3]
    have hcop : Nat.Coprime ℓ (s * s - 1) := by
      rw [hℓ.coprime_iff_not_dvd]
      rwa [← sq]
    have hc1 : c ^ (s * s - 1) = 1 := by
      have hss : 1 ≤ s * s := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
      have := hcs
      rw [show s * s = (s * s - 1) + 1 by omega, pow_succ] at this
      exact mul_eq_right.mp this
    have hord : orderOf c = 1 := Nat.eq_one_of_dvd_coprimes hcop
      (orderOf_dvd_of_pow_eq_one hcl) (orderOf_dvd_of_pow_eq_one hc1)
    rw [orderOf_eq_one_iff, hcdef, commutatorElement_eq_one_iff_mul_comm] at hord
    exact hord
  set pw : F →* F :=
    { toFun := fun x => x ^ ℓ
      map_one' := one_pow ℓ
      map_mul' := fun x y => (Commute.mul_pow (Subtype.ext (hFab x y)) ℓ) } with hpw
  set Ω := pw.ker with hΩ
  have hΩel : IsElementaryAbelian ℓ (Ω.map F.subtype) := by
    have hc : IsMulCommutative (Ω.map F.subtype) :=
      ⟨⟨fun a b => by
        obtain ⟨a', -, ha'⟩ := a.2
        obtain ⟨b', -, hb'⟩ := b.2
        apply Subtype.ext
        change (a : Y) * b = b * a
        rw [← ha', ← hb']
        exact hFab a' b'⟩⟩
    have hexp : Monoid.exponent (Ω.map F.subtype) ∣ ℓ :=
      Monoid.exponent_dvd_of_forall_pow_eq_one fun a => by
        obtain ⟨a', ha'Ω, ha'⟩ := a.2
        apply Subtype.ext
        change (a : Y) ^ ℓ = 1
        rw [← ha']
        have : a' ^ ℓ = 1 := ha'Ω
        simpa using congrArg F.subtype this
    exact ⟨hexp⟩
  have hΩp : IsPGroup ℓ (Ω.map F.subtype) := IsElementaryAbelian.isPGroup ℓ _
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hΩp
  have hcardΩ : Nat.card (Ω.map F.subtype) = Nat.card Ω :=
    Subgroup.card_map_of_injective F.subtype_injective
  have hF1 : Nat.card F = Nat.card Ω * Nat.card pw.range := by
    rw [← Nat.card_congr (QuotientGroup.quotientKerEquivRange pw).toEquiv, mul_comm]
    exact Subgroup.card_eq_card_quotient_mul_card_subgroup pw.ker
  set Zf := φ.ker.subgroupOf F
  have hrange : pw.range ≤ Zf := by
    rintro _ ⟨x, rfl⟩
    exact hpowker x
  obtain ⟨e, -⟩ := exists_quotient_comap_mulEquiv φ hφ U
  have hF2 : Nat.card F = Nat.card U * Nat.card Zf := by
    rw [← Nat.card_congr e.toEquiv]
    exact Subgroup.card_eq_card_quotient_mul_card_subgroup _
  have hle : Nat.card U ≤ Nat.card Ω := by
    have h1 := Subgroup.card_le_of_le hrange
    have hZpos : 0 < Nat.card Zf := Nat.card_pos
    have : Nat.card U * Nat.card Zf ≤ Nat.card Ω * Nat.card Zf := by
      rw [← hF2, hF1]
      exact Nat.mul_le_mul_left _ h1
    exact Nat.le_of_mul_le_mul_right this hZpos
  rw [hUcard, ← hcardΩ, hk] at hle
  have hrk : r ≤ k := (Nat.pow_le_pow_iff_right hℓ.one_lt).mp hle
  exact hrk.trans (le_pRank_of_elementaryAbelian_card hℓ.one_lt hΩel hk)

end CFSG.RankThree.GroupTheory.SteinbergBY
