module

public import CFSG.RankThree.PartOne.LIT.RankAbstract
public import CFSG.RankThree.PartTwo.Census.LinearRank
public import TauCeti.LinearAlgebra.BilinearForm.SymplecticBasis

public section

namespace CFSG.RankThree.PartOne.KFU

open Module CFSG.RankThree.PartOne.LIT

section Counting

variable {K : Type} [Field K] [Finite K] {X : Type} [AddCommGroup X] [Module K X]
  [FiniteDimensional K X]

theorem pow_sub_one_dvd_of_fixed_point_free {p : ℕ} (hp : p.Prime) {g : X ≃ₗ[K] X}
    (hgp : g ^ p = 1) (hfree : ∀ v, g v = v → v = 0) : p ∣ Nat.card K ^ finrank K X - 1 := by
  have : Fact p.Prime := ⟨hp⟩
  have : Finite X := Module.finite_of_finite K
  have hP : IsPGroup p (Subgroup.zpowers g) := by
    intro h
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp h.2
    refine ⟨1, Subtype.ext ?_⟩
    rw [pow_one, Subgroup.coe_pow, Subgroup.coe_one, ← hk, ← zpow_natCast, ← zpow_mul, mul_comm,
      zpow_mul, zpow_natCast, hgp, one_zpow]
  have hmod := hP.card_modEq_card_fixedPoints X
  have hfix : MulAction.fixedPoints (Subgroup.zpowers g) X = {0} := by
    ext v
    simp only [MulAction.mem_fixedPoints, Set.mem_singleton_iff]
    constructor
    · intro h
      exact hfree v (h ⟨g, Subgroup.mem_zpowers g⟩)
    · rintro rfl h
      exact map_zero _
  have hcard : Nat.card (MulAction.fixedPoints (Subgroup.zpowers g) X) = 1 := by
    rw [hfix]
    simp
  rw [hcard, Module.natCard_eq_pow_finrank (K := K) (V := X)] at hmod
  have hpos : 1 ≤ Nat.card K ^ finrank K X := Nat.one_le_pow _ _ Nat.card_pos
  exact (Nat.modEq_iff_dvd' hpos).1 hmod.symm

end Counting

theorem dvd_of_dvd_pow_sub_one {p q d n : ℕ} (hp : p.Prime) (hd : 0 < d) (hq : 1 ≤ q)
    (hdiv : ∀ i : ℕ, 0 < i → i < d → ¬ p ∣ q ^ i - 1) (hd' : p ∣ q ^ d - 1)
    (hn : p ∣ q ^ n - 1) : d ∣ n := by
  have : Fact p.Prime := ⟨hp⟩
  have key : ∀ i : ℕ, p ∣ q ^ i - 1 ↔ ((q : ZMod p)) ^ i = 1 := by
    intro i
    have h1 : 1 ≤ q ^ i := Nat.one_le_pow _ _ hq
    rw [← Nat.modEq_iff_dvd' h1, ← ZMod.natCast_eq_natCast_iff]
    constructor <;> intro h <;> simpa [eq_comm] using h
  have hord : orderOf (q : ZMod p) = d := by
    rw [orderOf_eq_iff hd]
    refine ⟨(key d).1 hd', fun m hm hm0 h => hdiv m hm0 hm ((key m).2 h)⟩
  rw [← hord]
  exact orderOf_dvd_of_pow_eq_one ((key n).1 hn)

theorem card_le_pow_div_alt_odd {K : Type} [Field K] [Finite K] {p : ℕ} (hp : p.Prime)
    (hpK : (p : K) ≠ 0) {d : ℕ} (hd : 0 < d) (hdodd : Odd d)
    (hdiv : ∀ i : ℕ, 0 < i → i < d → ¬ p ∣ Nat.card K ^ i - 1) (hd' : p ∣ Nat.card K ^ d - 1) :
    ∀ (n : ℕ) (X : Type) [AddCommGroup X] [Module K X] [FiniteDimensional K X],
      finrank K X = n → ∀ (B : X →ₗ[K] X →ₗ[K] K), (∀ v, (∀ w, B v w = 0) → v = 0) →
      (∀ v, B v v = 0) → ∀ (E : Subgroup (X ≃ₗ[K] X)) [Finite E],
      (∀ g ∈ E, ∀ h ∈ E, g * h = h * g) → (∀ g ∈ E, g ^ p = 1) →
      (∀ g ∈ E, ∀ u w, B (g u) (g w) = B u w) → Nat.card E ≤ p ^ (n / (2 * d)) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro X _ _ _ hn B hB hAlt E _ hcomm hexp hpres
  have hexpE : ∀ a : E, a ^ p = 1 := fun a => Subtype.ext (hexp a a.2)
  obtain ⟨k, hk⟩ := CFSG.RankThree.PartTwo.Census.exists_card_eq_pow_of_exponent hp hexpE
  have hq1 : 1 ≤ Nat.card K := Nat.card_pos
  by_cases hfix : ∃ x ∈ E, x ≠ 1 ∧ ∃ v : X, v ≠ 0 ∧ x v = v
  · obtain ⟨x, hxE, hx1, v, hv0, hxv⟩ := hfix
    have hc := isCompl_fixedSpace_commSpace hpK (hexp x hxE)
    have hxcomm : ∀ g ∈ E, g * x = x * g := fun g hg => hcomm g hg x hxE
    have hUinv : ∀ g : E, ∀ u ∈ fixedSpace x, (E.subtype g) u ∈ fixedSpace x :=
      fun g u hu => map_mem_fixedSpace (hxcomm g g.2) hu
    have hWinv : ∀ g : E, ∀ w ∈ commSpace x, (E.subtype g) w ∈ commSpace x :=
      fun g w hw => map_mem_commSpace (hxcomm g g.2) hw
    have hsum := Submodule.finrank_add_eq_of_isCompl hc
    have hUpos : 0 < finrank K (fixedSpace x) := by
      apply Module.finrank_pos_iff_exists_ne_zero.mpr
      exact ⟨⟨v, mem_fixedSpace.mpr hxv⟩, fun h => hv0 (congrArg Subtype.val h)⟩
    have hWpos : 0 < finrank K (commSpace x) := by
      apply Module.finrank_pos_iff_exists_ne_zero.mpr
      by_contra hcon
      have hcon' : ∀ w : commSpace x, w = 0 := fun w => by_contra fun hw => hcon ⟨w, hw⟩
      apply hx1
      apply LinearEquiv.ext
      intro y
      have hy : x y - y ∈ commSpace x := mem_commSpace.mpr ⟨y, rfl⟩
      have h2 : x y - y = 0 := congrArg Subtype.val (hcon' ⟨x y - y, hy⟩)
      simpa [sub_eq_zero] using h2
    have hskew := alt_skew hAlt
    have hUW : ∀ u ∈ fixedSpace x, ∀ w ∈ commSpace x, B u w = 0 := by
      intro u hu w hw
      obtain ⟨y, rfl⟩ := mem_commSpace.mp hw
      have h1 := hpres x hxE u y
      rw [mem_fixedSpace.mp hu] at h1
      rw [map_sub, h1, sub_self]
    have hWU : ∀ w ∈ commSpace x, ∀ u ∈ fixedSpace x, B w u = 0 := by
      intro w hw u hu
      rw [hskew w u, hUW u hu w hw, neg_zero]
    have hsplit : ∀ y : X, ∃ u ∈ fixedSpace x, ∃ w ∈ commSpace x, u + w = y := by
      intro y
      have : y ∈ fixedSpace x ⊔ commSpace x := by rw [hc.sup_eq_top]; trivial
      exact Submodule.mem_sup.mp this
    let ρ : E →* (X ≃ₗ[K] X) := E.subtype
    let ρU := restrictAction ρ (fixedSpace x) hUinv
    let ρW := restrictAction ρ (commSpace x) hWinv
    let BU : fixedSpace x →ₗ[K] fixedSpace x →ₗ[K] K :=
      B.compl₁₂ (fixedSpace x).subtype (fixedSpace x).subtype
    let BW : commSpace x →ₗ[K] commSpace x →ₗ[K] K :=
      B.compl₁₂ (commSpace x).subtype (commSpace x).subtype
    have hBU : ∀ u : fixedSpace x, (∀ u' : fixedSpace x, BU u u' = 0) → u = 0 := by
      intro u hu
      apply Subtype.ext
      apply hB
      intro y
      obtain ⟨u₁, hu₁, w₁, hw₁, rfl⟩ := hsplit y
      rw [map_add, hUW u u.2 w₁ hw₁, add_zero]
      exact hu ⟨u₁, hu₁⟩
    have hBW : ∀ w : commSpace x, (∀ w' : commSpace x, BW w w' = 0) → w = 0 := by
      intro w hw
      apply Subtype.ext
      apply hB
      intro y
      obtain ⟨u₁, hu₁, w₁, hw₁, rfl⟩ := hsplit y
      rw [map_add, hWU w w.2 u₁ hu₁, zero_add]
      exact hw ⟨w₁, hw₁⟩
    have hAltU : ∀ u : fixedSpace x, BU u u = 0 := fun u => hAlt u
    have hAltW : ∀ w : commSpace x, BW w w = 0 := fun w => hAlt w
    let EU : Subgroup (fixedSpace x ≃ₗ[K] fixedSpace x) := ρU.range
    let EW : Subgroup (commSpace x ≃ₗ[K] commSpace x) := ρW.range
    have : Finite EU := Finite.of_surjective ρU.rangeRestrict ρU.rangeRestrict_surjective
    have : Finite EW := Finite.of_surjective ρW.rangeRestrict ρW.rangeRestrict_surjective
    have hcommU : ∀ g ∈ EU, ∀ h ∈ EU, g * h = h * g := by
      rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
      rw [← map_mul, ← map_mul]
      exact congrArg ρU (Subtype.ext (hcomm a a.2 b b.2))
    have hcommW : ∀ g ∈ EW, ∀ h ∈ EW, g * h = h * g := by
      rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
      rw [← map_mul, ← map_mul]
      exact congrArg ρW (Subtype.ext (hcomm a a.2 b b.2))
    have hexpU : ∀ g ∈ EU, g ^ p = 1 := by
      rintro _ ⟨a, rfl⟩
      rw [← map_pow, hexpE a, map_one]
    have hexpW : ∀ g ∈ EW, g ^ p = 1 := by
      rintro _ ⟨a, rfl⟩
      rw [← map_pow, hexpE a, map_one]
    have hpresU : ∀ g ∈ EU, ∀ u w, BU (g u) (g w) = BU u w := by
      rintro _ ⟨a, rfl⟩ u w
      exact hpres a a.2 u w
    have hpresW : ∀ g ∈ EW, ∀ u w, BW (g u) (g w) = BW u w := by
      rintro _ ⟨a, rfl⟩ u w
      exact hpres a a.2 u w
    have hIU := ih (finrank K (fixedSpace x)) (by omega) (fixedSpace x) rfl BU hBU hAltU EU
      hcommU hexpU hpresU
    have hIW := ih (finrank K (commSpace x)) (by omega) (commSpace x) rfl BW hBW hAltW EW
      hcommW hexpW hpresW
    have hinj : Function.Injective
        (fun g : E => ((⟨ρU g, g, rfl⟩ : EU), (⟨ρW g, g, rfl⟩ : EW))) := by
      intro g h hgh
      simp only [Prod.mk.injEq] at hgh
      obtain ⟨h1, h2⟩ := hgh
      have h1' : ρU g = ρU h := congrArg Subtype.val h1
      have h2' : ρW g = ρW h := congrArg Subtype.val h2
      apply Subtype.ext
      apply LinearEquiv.ext
      intro y
      have hfun : (g : X ≃ₗ[K] X).toLinearMap = (h : X ≃ₗ[K] X).toLinearMap := by
        apply ext_of_isCompl hc
        · intro u hu
          exact (restrictAction_apply ρ (fixedSpace x) hUinv g ⟨u, hu⟩).symm.trans
            ((congrArg Subtype.val (LinearEquiv.congr_fun h1' ⟨u, hu⟩)).trans
              (restrictAction_apply ρ (fixedSpace x) hUinv h ⟨u, hu⟩))
        · intro w hw
          exact (restrictAction_apply ρ (commSpace x) hWinv g ⟨w, hw⟩).symm.trans
            ((congrArg Subtype.val (LinearEquiv.congr_fun h2' ⟨w, hw⟩)).trans
              (restrictAction_apply ρ (commSpace x) hWinv h ⟨w, hw⟩))
      exact LinearMap.congr_fun hfun y
    have hle : Nat.card E ≤ Nat.card EU * Nat.card EW := by
      rw [← Nat.card_prod]
      exact Nat.card_le_card_of_injective _ hinj
    calc Nat.card E ≤ Nat.card EU * Nat.card EW := hle
      _ ≤ p ^ (finrank K (fixedSpace x) / (2 * d)) * p ^ (finrank K (commSpace x) / (2 * d)) :=
        Nat.mul_le_mul hIU hIW
      _ = p ^ (finrank K (fixedSpace x) / (2 * d) + finrank K (commSpace x) / (2 * d)) :=
        (pow_add _ _ _).symm
      _ ≤ p ^ (n / (2 * d)) := by
        refine Nat.pow_le_pow_right hp.pos ?_
        have : finrank K (fixedSpace x) / (2 * d) + finrank K (commSpace x) / (2 * d) ≤
            (finrank K (fixedSpace x) + finrank K (commSpace x)) / (2 * d) :=
          Nat.div_add_div_le_add_div
        rwa [hsum, hn] at this
  · push Not at hfix
    have hk1 : k ≤ 1 := by
      by_contra hk2
      push Not at hk2
      have hbig : p ^ 2 ≤ Nat.card E := by
        rw [hk]; exact Nat.pow_le_pow_right hp.pos hk2
      obtain ⟨x, hxE, hx1, v, hv0, hxv⟩ := exists_fixed_of_sq_le_card hp hpK E hcomm hexp hbig
      exact hfix x hxE hx1 v hv0 hxv
    rcases Nat.lt_or_ge k 1 with hk0 | hk0
    · have : k = 0 := by omega
      rw [hk, this, pow_zero]
      exact Nat.one_le_pow _ _ hp.pos
    · have hk1' : k = 1 := by omega
      have hcardE : Nat.card E = p := by rw [hk, hk1', pow_one]
      have hnt : Nontrivial E :=
        Finite.one_lt_card_iff_nontrivial.mp (by rw [hcardE]; exact hp.one_lt)
      obtain ⟨g, hg1⟩ := exists_ne (1 : E)
      have hgfree : ∀ v, (g : X ≃ₗ[K] X) v = v → v = 0 := by
        intro v hv
        by_contra hv0
        exact hfix g g.2 (fun h => hg1 (Subtype.ext h)) v hv0 hv
      have hpn := pow_sub_one_dvd_of_fixed_point_free hp (hexp g g.2) hgfree
      rw [hn] at hpn
      have hdn : d ∣ n := dvd_of_dvd_pow_sub_one hp hd hq1 hdiv hd' hpn
      have hnd : B.Nondegenerate := by
        refine ⟨hB, ?_⟩
        intro w hw
        apply hB
        intro v
        rw [alt_skew hAlt, hw v, neg_zero]
      have hev : Even n := by
        rw [← hn]
        exact LinearMap.BilinForm.IsAlt.even_finrank hAlt hnd
      have hnpos : 0 < n := by
        by_contra h0
        have h0' : n = 0 := by omega
        have hsub : Subsingleton X := Module.finrank_zero_iff.mp (by rw [hn, h0'])
        exact hg1 (Subtype.ext (LinearEquiv.ext fun v => Subsingleton.elim _ _))
      have hcop : Nat.Coprime 2 d := Nat.coprime_two_left.2 hdodd
      have h2dn : 2 * d ∣ n :=
        Nat.Coprime.mul_dvd_of_dvd_of_dvd hcop (even_iff_two_dvd.mp hev) hdn
      have hge : 1 ≤ n / (2 * d) := by
        obtain ⟨c, hc⟩ := h2dn
        have hd2 : 0 < 2 * d := by omega
        rw [hc, Nat.mul_div_cancel_left c hd2]
        rcases Nat.eq_zero_or_pos c with h | h
        · rw [h] at hc
          omega
        · exact h
      calc Nat.card E = p := hcardE
        _ = p ^ 1 := (pow_one p).symm
        _ ≤ p ^ (n / (2 * d)) := Nat.pow_le_pow_right hp.pos hge

end CFSG.RankThree.PartOne.KFU
