module

public import CFSG.Quasithin.Background.F918Z8d

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique

section Arithmetic

theorem sxidiv_card_dvd_of_free {G X : Type*} [Group G] [Finite G] [Finite X] [MulAction G X]
    (hfree : ∀ (g : G) (x : X), g • x = x → g = 1) : Nat.card G ∣ Nat.card X := by
  classical
  have : Fintype (MulAction.orbitRel.Quotient G X) := Fintype.ofFinite _
  rw [Nat.card_congr (MulAction.selfEquivSigmaOrbitsQuotientStabilizer G X), Nat.card_sigma]
  refine Finset.dvd_sum fun ω _ => ?_
  have hst : MulAction.stabilizer G ω.out = ⊥ :=
    (Subgroup.eq_bot_iff_forall _).2 fun g hg => hfree g _ hg
  rw [hst]
  exact (Subgroup.index_bot (G := G)).symm ▸ dvd_rfl

theorem sxidiv_dvd_of_pow_sub_one_dvd {n m : ℕ} (h : 2 ^ n - 1 ∣ 2 ^ m - 1) : n ∣ m := by
  have h1 : Nat.gcd (2 ^ n - 1) (2 ^ m - 1) = 2 ^ n - 1 := Nat.gcd_eq_left h
  rw [Nat.pow_sub_one_gcd_pow_sub_one] at h1
  have h2 : 2 ^ Nat.gcd n m = 2 ^ n := by
    have := Nat.one_le_two_pow (n := Nat.gcd n m)
    have := Nat.one_le_two_pow (n := n)
    omega
  exact Nat.gcd_eq_left_iff_dvd.1 (Nat.pow_right_injective (le_refl 2) h2)

end Arithmetic

section Torus

variable {Y : Type} [CommGroup Y]

theorem sxidiv_pow_mem {t : MulAut Y} {U : Subgroup Y} (hU : ∀ w ∈ U, t w ∈ U) (k : ℕ) {w : Y}
    (hw : w ∈ U) : (t ^ k) w ∈ U := by
  induction k with
  | zero => simpa using hw
  | succ k ih =>
    rw [pow_succ']
    exact hU _ ih

theorem sxidiv_zpowers_mem [Finite Y] {t : MulAut Y} {U : Subgroup Y} (hU : ∀ w ∈ U, t w ∈ U)
    {g : MulAut Y} (hg : g ∈ Subgroup.zpowers t) {w : Y} (hw : w ∈ U) : g w ∈ U := by
  obtain ⟨k, rfl⟩ := (Submonoid.mem_powers_iff _ _).1 (mem_powers_iff_mem_zpowers.2 hg)
  exact sxidiv_pow_mem hU k hw

@[expose] def sxidivNonid [Finite Y] (t : MulAut Y) (U : Subgroup Y) (hU : ∀ w ∈ U, t w ∈ U) :
    SubMulAction (Subgroup.zpowers t) Y where
  carrier := {u | u ∈ U ∧ u ≠ 1}
  smul_mem' := by
    rintro ⟨g, hg⟩ u ⟨huU, hu1⟩
    refine ⟨sxidiv_zpowers_mem hU hg huU, fun h => hu1 ?_⟩
    exact g.injective (by rw [map_one]; exact h)

theorem sxidiv_free [Finite Y] {n : ℕ} {t : MulAut Y} (htord : orderOf t = 2 ^ n - 1)
    {M U : Subgroup Y} (hUM : U ≤ M) (hU : ∀ w ∈ U, t w ∈ U)
    (hfree : ∀ k : ℕ, ¬ (2 ^ n - 1 ∣ k) → M ⊓ fixV (Subgroup.zpowers (t ^ k)) = ⊥)
    (g : Subgroup.zpowers t) (x : sxidivNonid t U hU) (hgx : g • x = x) : g = 1 := by
  obtain ⟨g, hg⟩ := g
  obtain ⟨x, hxU, hx1⟩ := x
  obtain ⟨k, rfl⟩ := (Submonoid.mem_powers_iff _ _).1 (mem_powers_iff_mem_zpowers.2 hg)
  have hk : (t ^ k) x = x := congrArg Subtype.val hgx
  by_cases hdvd : 2 ^ n - 1 ∣ k
  · have : t ^ k = 1 := orderOf_dvd_iff_pow_eq_one.1 (htord ▸ hdvd)
    exact Subtype.ext this
  · exfalso
    have hmem : x ∈ M ⊓ fixV (Subgroup.zpowers (t ^ k)) := by
      refine ⟨hUM hxU, fun y hy => ?_⟩
      have : Subgroup.zpowers (t ^ k) ≤ MulAction.stabilizer (MulAut Y) x := by
        rw [Subgroup.zpowers_le, MulAction.mem_stabilizer_iff]
        exact hk
      exact MulAction.mem_stabilizer_iff.1 (this hy)
    rw [hfree k hdvd, Subgroup.mem_bot] at hmem
    exact hx1 hmem

theorem sxidiv_dvd_rk [Finite Y] (hexp : ∀ y : Y, y ^ 2 = 1) {n : ℕ} {t : MulAut Y}
    (htord : orderOf t = 2 ^ n - 1) {M U : Subgroup Y} (hUM : U ≤ M) (hU : ∀ w ∈ U, t w ∈ U)
    (hfree : ∀ k : ℕ, ¬ (2 ^ n - 1 ∣ k) → M ⊓ fixV (Subgroup.zpowers (t ^ k)) = ⊥) :
    n ∣ rk U := by
  have h1 := sxidiv_card_dvd_of_free (G := Subgroup.zpowers t) (X := sxidivNonid t U hU)
    (sxidiv_free htord hUM hU hfree)
  rw [Nat.card_zpowers, htord] at h1
  have h2 : Nat.card (sxidivNonid t U hU) = Nat.card U - 1 := by
    have h3 : Nat.card (sxidivNonid t U hU) = Set.ncard ((U : Set Y) \ {1}) :=
      Nat.card_coe_set_eq _
    rw [h3, Set.ncard_sdiff_singleton_of_mem U.one_mem, ← Nat.card_coe_set_eq]
    rfl
  rw [h2, card_eq_two_pow hexp U] at h1
  exact sxidiv_dvd_of_pow_sub_one_dvd h1

end Torus

section

variable {Y : Type} [CommGroup Y] [Finite Y]

theorem sxi_div (hexp : ∀ y : Y, y ^ 2 = 1) {n : ℕ} (hn : 2 ≤ n) {t : MulAut Y}
    (htord : orderOf t = 2 ^ n - 1) {M I J : Subgroup Y} (hJI : J ≤ I) (hIM : I ≤ M)
    (htI : ∀ w ∈ I, t w ∈ I) (htJ : ∀ w ∈ J, t w ∈ J)
    (hfree : ∀ k : ℕ, ¬ (2 ^ n - 1 ∣ k) → M ⊓ fixV (Subgroup.zpowers (t ^ k)) = ⊥)
    {A : Subgroup (MulAut Y)} (htA : ∀ a ∈ A, t * a = a * t) (hAI : A ≤ stabSub I)
    (hAJ : A ≤ stabSub J) : n ∣ rkIdx (fixV (autSec A I J)) := by
  have _hn : 2 ≤ n := hn
  have h0 := d321d_rkIdx_add_rk_commModSub hJI hAI hAJ
  have htI' : ∀ w ∈ commModSub I A J, t w ∈ commModSub I A J := by
    rintro w ⟨hwI, hw⟩
    refine ⟨htI w hwI, fun a ha => ?_⟩
    have h1 : t (a w) = a (t w) := congrArg (fun φ : MulAut Y => φ w) (htA a ha)
    have h2 : a (t w) * (t w)⁻¹ = t (a w * w⁻¹) := by
      rw [map_mul, map_inv, h1]
    rw [h2]
    exact htJ _ (hw a ha)
  have h1 := sxidiv_dvd_rk hexp htord hIM htI hfree
  have h2 := sxidiv_dvd_rk hexp htord ((commModSub_le I A J).trans hIM) htI' hfree
  rw [← h0] at h1
  exact (Nat.dvd_add_left h2).1 h1

end

end CFSG.Quasithin
