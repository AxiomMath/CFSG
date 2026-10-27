module

public import CFSG.GH74.GLS.IVK.L2.BorelStd
public import CFSG.LocalAnalysis.ComponentInitial.DiagonalSemilinear
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open Subgroup CFSG.GH74.GLS.IVK CFSG.PSL2Table CFSG.GorensteinWalter
  CFSG.ComponentClassification.CatalogueSchreierLinearTwo
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

theorem uc22p22qz_action_trivial {F : Type} [Field F] [Finite F] {K : Type} [Group K] {e : K ≃* L2 F}
    {W : Subgroup K} (h : L2Borel.IsStd e W) (h2 : (2 : F) ≠ 0) {p n j : ℕ} (hp : p.Prime)
    (hF : Nat.card F = p ^ n) (hn : 1 ≤ n) (hpn : ¬ p ∣ n) {α : MulAut K}
    (hα : α ∈ MulAction.stabilizer (MulAut K) W) (hord : α ^ p ^ j = 1) (t : F) :
    α (L2Borel.wt e t) = L2Borel.wt e t := by
  obtain ⟨a, b, σ, hασ⟩ := L2Borel.exists_bor_decomp h hα
  have hit : ∀ t : F, (fun x => (a : F) * σ x)^[p ^ j] t = t := by
    intro t
    apply L2Borel.wt_injective e h2
    rw [← L2Borel.pow_action_wt, ← hασ, hord]
    rfl
  have h3 : ∀ t : F, (∏ i ∈ Finset.range (p ^ j), (σ ^ i) (a : F)) * (σ ^ p ^ j) t = t := fun t => by
    rw [← L2Borel.iterate_semilinear]
    exact hit t
  have hprod : ∏ i ∈ Finset.range (p ^ j), (σ ^ i) (a : F) = 1 := by
    have := h3 1
    simpa using this
  have hσpow : σ ^ p ^ j = 1 := by
    refine RingEquiv.ext fun t => ?_
    have := h3 t
    rw [hprod, one_mul] at this
    simpa using this
  have hcardAut : Nat.card (RingAut F) = n :=
    (CFSG.LocalAnalysis.ComponentInitial.card_ringAut_and_isCyclic hp F hF).1
  have hcop : Nat.Coprime (p ^ j) n := (Nat.Prime.coprime_iff_not_dvd hp |>.2 hpn).pow_left j
  have hσ : σ = 1 := by
    have h1 : orderOf σ ∣ p ^ j := orderOf_dvd_of_pow_eq_one hσpow
    have h2' : orderOf σ ∣ n := hcardAut ▸ orderOf_dvd_natCard σ
    have : orderOf σ ∣ Nat.gcd (p ^ j) n := Nat.dvd_gcd h1 h2'
    rw [hcop.gcd_eq_one] at this
    exact orderOf_eq_one_iff.1 (Nat.dvd_one.1 this)
  subst hσ
  have hapow : (a : F) ^ p ^ j = 1 := by
    simpa [Finset.prod_const] using hprod
  have hunit : a ^ p ^ j = 1 := Units.ext (by simpa using hapow)
  have ha1 : a = 1 := by
    have h1 : orderOf a ∣ p ^ j := orderOf_dvd_of_pow_eq_one hunit
    have h2' : orderOf a ∣ p ^ n - 1 := by
      have := orderOf_dvd_natCard a
      rwa [Nat.card_units, hF] at this
    have hpn1 : ¬ p ∣ p ^ n - 1 := fun hd => by
      have hd' : p ∣ p ^ n - 1 + 1 := by
        rw [Nat.sub_add_cancel (Nat.one_le_pow _ _ hp.pos)]
        exact dvd_pow_self p (by omega)
      exact hp.one_lt.ne' (Nat.dvd_one.1 ((Nat.dvd_add_right hd).1 hd'))
    have hcop' : Nat.Coprime (p ^ j) (p ^ n - 1) := (Nat.Prime.coprime_iff_not_dvd hp |>.2 hpn1).pow_left j
    have : orderOf a ∣ Nat.gcd (p ^ j) (p ^ n - 1) := Nat.dvd_gcd h1 h2'
    rw [hcop'.gcd_eq_one] at this
    exact orderOf_eq_one_iff.1 (Nat.dvd_one.1 this)
  rw [hασ, L2Borel.action_wt, ha1]
  simp

theorem uc22p22qz_pow_apply {L : Subgroup G} {a : G} {α : MulAut ↥L}
    (hα : ∀ k : ↥L, ((α k : ↥L) : G) = a * k * a⁻¹) (m : ℕ) (k : ↥L) :
    (((α ^ m) k : ↥L) : G) = a ^ m * (k : G) * (a ^ m)⁻¹ := by
  induction m generalizing k with
  | zero => simp
  | succ m ih =>
    rw [pow_succ, MulAut.mul_apply, ih, hα]
    group

theorem uc22p22qz_exists_pow {p : ℕ} {S : Subgroup G} (hS : IsPGroup p S) {a : G} (ha : a ∈ S) :
    ∃ j : ℕ, a ^ p ^ j = 1 := by
  obtain ⟨j, hj⟩ := hS ⟨a, ha⟩
  exact ⟨j, by simpa using congrArg Subtype.val hj⟩

theorem uc22p22qz_eq_one_of_central {p n : ℕ} (hp : p.Prime) (hn : 2 ≤ n) {L : Subgroup G} [IsSimpleGroup ↥L]
    (hdvd : p ^ n ∣ Nat.card ↥L) {z : G} (hzL : z ∈ L) (hz : ∀ l ∈ L, z * l = l * z) : z = 1 := by
  by_contra hz1
  have hcen : (⟨z, hzL⟩ : ↥L) ∈ Subgroup.center ↥L := by
    rw [Subgroup.mem_center_iff]
    intro l
    exact Subtype.ext (hz l l.2).symm
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center ↥L) with h | h
  · rw [h, Subgroup.mem_bot] at hcen
    exact hz1 (congrArg Subtype.val hcen)
  · have hcomm : IsMulCommutative ↥L := ⟨⟨fun a b => by
      have : a ∈ Subgroup.center ↥L := h ▸ Subgroup.mem_top a
      exact (Subgroup.mem_center_iff.1 this b).symm⟩⟩
    have hq' : (Nat.card ↥L).Prime := Group.is_simple_iff_prime_card.1 inferInstance
    have hp1 : p ∣ Nat.card ↥L := (dvd_pow_self p (by omega)).trans hdvd
    have h1 : p = Nat.card ↥L := (Nat.prime_dvd_prime_iff_eq hp hq').1 hp1
    have h2 : p ^ 2 ≤ p ^ n := Nat.pow_le_pow_right hp.pos hn
    have h3 : p < p ^ 2 := by nlinarith [hp.two_le]
    have h4 : p ^ n ≤ Nat.card ↥L := Nat.le_of_dvd hq'.pos hdvd
    omega

end CFSG.LocalAnalysis.UniquenessCase.UC22
