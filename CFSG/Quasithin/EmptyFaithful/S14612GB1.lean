module

public import CFSG.Quasithin.EmptyFaithful.S146P14

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
open scoped commutatorElement

section Abstract

variable {G : Type} [Group G]

theorem mem_of_pow_mem_of_coprime_GB1 {Q : Subgroup G} {x : G} {m n : ℕ} (h : Nat.Coprime m n)
    (hm : x ^ m ∈ Q) (hn : x ^ n ∈ Q) : x ∈ Q := by
  obtain ⟨a, b, hab⟩ := Nat.isCoprime_iff_coprime.mpr h
  have hx : x = (x ^ m) ^ a * (x ^ n) ^ b := by
    rw [← zpow_natCast x m, ← zpow_natCast x n, ← zpow_mul, ← zpow_mul, ← zpow_add,
      show (m : ℤ) * a + n * b = 1 by linarith, zpow_one]
  rw [hx]
  exact Q.mul_mem (Q.zpow_mem hm a) (Q.zpow_mem hn b)

theorem commutator_sq_eq_GB1 {U : Subgroup G} (hUc : ∀ x ∈ U, ∀ y ∈ U, x * y = y * x)
    (hU2 : ∀ x ∈ U, x ^ 2 = 1) {y u : G} (hu : u ∈ U) (hyU : ∀ v ∈ U, y * v * y⁻¹ ∈ U) :
    u * y ^ 2 * u⁻¹ * (y ^ 2)⁻¹ = ⁅⁅u, y⁆, y⁆ := by
  have ha : y * u * y⁻¹ ∈ U := hyU u hu
  have hb : y * (y * u * y⁻¹) * y⁻¹ ∈ U := hyU _ ha
  have ha2 : (y * u * y⁻¹) * (y * u * y⁻¹) = 1 := by
    simpa [pow_two] using hU2 _ ha
  have hb2 : (y * (y * u * y⁻¹) * y⁻¹) * (y * (y * u * y⁻¹) * y⁻¹) = 1 := by
    simpa [pow_two] using hU2 _ hb
  have hab := hUc _ hb _ ha
  set a := y * u * y⁻¹ with ha_def
  set b := y * a * y⁻¹ with hb_def
  have hainv : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha2
  have hbinv : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb2
  have e1 : ⁅⁅u, y⁆, y⁆ = u * a⁻¹ * b * a⁻¹ := by
    simp only [ha_def, hb_def, commutatorElement_def]
    group
  have e2 : u * y ^ 2 * u⁻¹ * (y ^ 2)⁻¹ = u * b⁻¹ := by
    simp only [hb_def, ha_def]
    group
  rw [e1, e2, hainv, hbinv]
  calc u * b = u * b * (a * a) := by rw [ha2, mul_one]
    _ = u * (b * a) * a := by group
    _ = u * (a * b) * a := by rw [hab]
    _ = u * a * b * a := by group

end Abstract

section Main

variable {G : Type} [Group G] [Finite G]

theorem exists_odd_not_mem_of_pSec_GB1 {Y Q : Subgroup G} {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hlt : Q < Y) (hY : ∀ x ∈ Y, ∃ k : ℕ, x ^ p ^ k ∈ Q) :
    ∃ z ∈ Y, z ∉ Q ∧ Odd (orderOf z) := by
  obtain ⟨x, hxY, hxQ⟩ := IsConcreteLE.exists_of_lt hlt
  obtain ⟨k, hk⟩ := exists_odd_orderOf_pow x
  obtain ⟨j, hj⟩ := hY x hxY
  refine ⟨x ^ 2 ^ k, Y.pow_mem hxY _, fun hzQ => hxQ ?_, hk⟩
  have hcop : Nat.Coprime (2 ^ k) (p ^ j) :=
    Nat.Coprime.pow k j ((Nat.coprime_primes Nat.prime_two hp).mpr (Ne.symm hp2))
  exact mem_of_pow_mem_of_coprime_GB1 hcop hzQ hj

theorem commutator_oTwoUpper_le_GB1 {U H Y : Subgroup G}
    (hUc : ∀ x ∈ U, ∀ y ∈ U, x * y = y * x) (hU2 : ∀ x ∈ U, x ^ 2 = 1)
    (hHU : ∀ g ∈ H, ∀ u ∈ U, g * u * g⁻¹ ∈ U) (hYH : Y ≤ H) :
    ⁅U, oTwoUpper Y⁆ ≤ ⁅⁅U, H⁆, Y⁆ := by
  have hK : ⁅U, H⁆ ≤ U := commutator_le_of_normalizes_P14 hHU
  have hLU : ⁅⁅U, H⁆, Y⁆ ≤ U :=
    (Subgroup.commutator_mono hK le_rfl).trans
      (commutator_le_of_normalizes_P14 fun g hg => hHU g (hYH hg))
  have key : oTwoUpper Y ≤ centralizerSection Y U ⁅⁅U, H⁆, Y⁆ := by
    refine (Subgroup.closure_le _).mpr fun x hx => ?_
    rw [SetLike.mem_coe, mem_centralizerSection_iff_of_le hLU]
    refine ⟨hx.1, fun u hu => ?_⟩
    obtain ⟨n, hn⟩ := hx.2
    have hy2 : (x ^ (n + 1)) ^ 2 = x := by
      rw [← pow_mul, show (n + 1) * 2 = orderOf x + 1 by omega, pow_succ, pow_orderOf_eq_one,
        one_mul]
    have hyY : x ^ (n + 1) ∈ Y := Y.pow_mem hx.1 _
    have e := commutator_sq_eq_GB1 hUc hU2 hu (fun v hv => hHU (x ^ (n + 1)) (hYH hyY) v hv)
    rw [hy2] at e
    rw [e]
    exact Subgroup.commutator_mem_commutator
      (Subgroup.commutator_mem_commutator hu (hYH hyY)) hyY
  exact ((le_centralizerSection_iff hLU).mp key).2

end Main

theorem Setting146.not_uK_le_centralizer_pCoreOf {G : Type} [Group G] [Finite G] {T M : Subgroup G}
    (h5 : Stage1461Five) (S : Setting146 G T M) {H PQ : Subgroup G} {p : ℕ}
    (hred : IsRedCE T M H PQ p) :
    ¬ (uK T M H ≤ Subgroup.centralizer (pCoreOf 2 H : Set G)) := by
  intro hKC
  have hH : IsHTM T M H := hred.isHTM
  have hHG : H ≤ mcOf T := S.le_mcOf hH
  have hUab : IsElemAbelian 2 (conjClosure (VZ T M) H) := S.lemma_14_5_15_two hH
  have hHU' : H ≤ Subgroup.normalizer (conjClosure (VZ T M) H : Set G) :=
    le_normalizer_conjClosure _ _
  have hHU : ∀ g ∈ H, ∀ u ∈ conjClosure (VZ T M) H, g * u * g⁻¹ ∈ conjClosure (VZ T M) H :=
    fun g hg u hu => (Subgroup.mem_normalizer_iff.mp (hHU' hg) u).mp hu
  have hUc : ∀ x ∈ conjClosure (VZ T M) H, ∀ y ∈ conjClosure (VZ T M) H, x * y = y * x :=
    fun x hx y hy => isElemAbelian_comm hUab hx hy
  have hU2 : ∀ x ∈ conjClosure (VZ T M) H, x ^ 2 = 1 :=
    fun x hx => isElemAbelian_pow_eq_one hUab hx
  have hKU : uK T M H ≤ conjClosure (VZ T M) H := commutator_le_of_normalizes_P14 hHU
  have hPQH : PQ ≤ H := hred.le
  obtain ⟨z₀, hz₀Y, hz₀Q, hz₀odd⟩ :=
    exists_odd_not_mem_of_pSec_GB1 hred.prime hred.odd hred.lt hred.pSec
  have hX1 : oTwoUpper PQ ≠ ⊥ := by
    intro hbot
    have hzX : z₀ ∈ oTwoUpper PQ := mem_oTwoUpper_of_odd hz₀Y hz₀odd
    rw [hbot, Subgroup.mem_bot] at hzX
    exact hz₀Q (hzX ▸ (pCoreOf 2 H).one_mem)
  have hXF : oTwoUpper PQ ≤ oTwoFstarIn H :=
    ((oTwoUpper_le PQ).trans hred.le_oTwoPIn).trans (oTwoPIn_le_oTwoFstarIn hred.prime H)
  have hZle : quasithinOmegaOneCenter T ≤ ⁅conjClosure (VZ T M) H, oTwoUpper PQ⁆ :=
    S.lemma_14_6_2 hH (h5 G T M S H hH) hX1 (S146A.oTwoUpper_idem PQ) hXF
      (hred.lt.le.trans (le_normalizer_oTwoUpper PQ))
  have hZK : quasithinOmegaOneCenter T ≤ ⁅uK T M H, PQ⁆ :=
    hZle.trans (commutator_oTwoUpper_le_GB1 hUc hU2 hHU hPQH)
  have hXU : ∀ g ∈ PQ, ∀ k ∈ uK T M H, g * k * g⁻¹ ∈ uK T M H := fun g hg k hk =>
    (Subgroup.mem_normalizer_iff.mp (mem_normalizer_commutator_P14 (hHU' (hPQH hg))
      (Subgroup.le_normalizer (hPQH hg))) k).mp hk
  have hQU : ∀ q ∈ pCoreOf 2 H, ∀ k ∈ uK T M H, q * k * q⁻¹ = k := by
    intro q hq k hk
    have h1 : q * k = k * q := Subgroup.mem_centralizer_iff.mp (hKC hk) q hq
    rw [h1]
    group
  have hXnQ : ∀ g ∈ PQ, ∀ q ∈ pCoreOf 2 H, g * q * g⁻¹ ∈ pCoreOf 2 H := fun g hg q hq =>
    (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 H (hPQH hg)) q).mp hq
  have hkey := comm_inf_fixed_P14 (U := uK T M H) (X := PQ) (Q := pCoreOf 2 H) hred.prime
    hred.odd (fun x hx y hy => hUc x (hKU hx) y (hKU hy)) (fun x hx => hU2 x (hKU hx)) hXU hQU
    hXnQ hred.pSec
  obtain ⟨z, hzZ, hz1⟩ : ∃ z ∈ quasithinOmegaOneCenter T, z ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have hbot : quasithinOmegaOneCenter T = ⊥ := (Subgroup.eq_bot_iff_forall _).mpr hcon
    have h2 := S.card_Z
    rw [hbot, Subgroup.card_bot] at h2
    omega
  refine hz1 (hkey z (hZK hzZ) fun g hg => ?_)
  have hgz : g * z = z * g := S146T.comm_Z (hHG (hPQH hg)) hzZ
  rw [hgz]
  group

end CFSG.Quasithin
