module

public import CFSG.Quasithin.H13.A5S1327n

public section

namespace CFSG.Quasithin.H13.A5

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.A5Model
open CFSG.LieType.BorelTits

section Parts

variable {G : Type} [Group G] [Finite G]

theorem exists_mem_oTwoUpper_inv_mul_mem {J N : Subgroup G} {k : G}
    (hk : k ∈ J) {q : ℕ} (hq : Odd q) (hkq : k ^ q ∈ N) :
    ∃ x ∈ oTwoUpper J, x⁻¹ * k ∈ N := by
  obtain ⟨e, m, hm, hkm⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos k).ne'
  have hkmN : k ^ m ∈ N := by
    have h1 : (k ^ m) ^ q ∈ N := by
      rw [← pow_mul, mul_comm, pow_mul]
      exact N.pow_mem hkq m
    have h2 : orderOf (k ^ m) ∣ 2 ^ e := by
      refine orderOf_dvd_of_pow_eq_one ?_
      rw [← pow_mul, mul_comm, ← hkm, pow_orderOf_eq_one]
    obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 h2
    refine B6.mem_of_pow_mem_of_coprime h1 ?_
    rw [hi]
    exact Nat.Coprime.pow_left _ (Nat.coprime_two_left.mpr hq)
  have hodd : Odd (orderOf (k ^ 2 ^ e)) := by
    have h2k : (2 ^ e : ℕ) ≠ 0 := by positivity
    rw [orderOf_pow' _ h2k, hkm, Nat.gcd_mul_right_left, Nat.mul_div_cancel_left _ (by positivity)]
    exact hm
  have hxJ : k ^ 2 ^ e ∈ oTwoUpper J := mem_oTwoUpper_of_odd (J.pow_mem hk _) hodd
  have hcop : Nat.Coprime (2 ^ e) m := Nat.Coprime.pow_left _ (Nat.coprime_two_left.mpr hm)
  have hbez : ((Nat.gcd (2 ^ e) m : ℕ) : ℤ) = (2 ^ e : ℕ) * Nat.gcdA (2 ^ e) m +
      (m : ℤ) * Nat.gcdB (2 ^ e) m := Nat.gcd_eq_gcd_ab _ _
  rw [hcop, Nat.cast_one] at hbez
  refine ⟨(k ^ 2 ^ e) ^ Nat.gcdA (2 ^ e) m, (oTwoUpper J).zpow_mem hxJ _, ?_⟩
  have e1 : k = (k ^ 2 ^ e) ^ Nat.gcdA (2 ^ e) m * (k ^ m) ^ Nat.gcdB (2 ^ e) m := by
    rw [← zpow_natCast, ← zpow_natCast (n := m), ← zpow_mul, ← zpow_mul, ← zpow_add, ← hbez,
      zpow_one]
  have e2 : ((k ^ 2 ^ e) ^ Nat.gcdA (2 ^ e) m)⁻¹ * k = (k ^ m) ^ Nat.gcdB (2 ^ e) m := by
    nth_rewrite 2 [e1]
    rw [inv_mul_cancel_left]
  rw [e2]
  exact N.zpow_mem hkmN _

theorem exists_prime_pow_mem_of_mem_kerIn {H T M : Subgroup G} (h : MinParabolic H T M)
    (hsolv : Group.IsSolvable ↥H) :
    ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ ∀ k ∈ kerIn M H, ∃ n : ℕ, k ^ p ^ n ∈ pCoreOf 2 H := by
  have := hsolv
  have hX := h.subgroupOf
  obtain ⟨p, hp, hp2, -, hJbar, -, -⟩ := hX.solvable_structure hsolv
  have : Fact p.Prime := ⟨hp⟩
  refine ⟨p, hp, hp2, fun k hk => ?_⟩
  have hkH : k ∈ H := h.kerIn_le_H hk
  have hk' : (⟨k, hkH⟩ : ↥H) ∈ kerIn (M.subgroupOf H) (⊤ : Subgroup ↥H) := by
    rw [B6.kerIn_subgroupOf_top, Subgroup.mem_subgroupOf]
    exact hk
  have hmem : QuotientGroup.mk' (CFSG.Open.pCore 2 ↥H) ⟨k, hkH⟩ ∈
      CFSG.Open.pCore p (↥H ⧸ CFSG.Open.pCore 2 ↥H) := by
    have : QuotientGroup.mk' (CFSG.Open.pCore 2 ↥H) ⟨k, hkH⟩ ∈
        (kerIn (M.subgroupOf H) (⊤ : Subgroup ↥H)).map
          (QuotientGroup.mk' (CFSG.Open.pCore 2 ↥H)) := ⟨_, hk', rfl⟩
    rw [hJbar] at this
    obtain ⟨z, -, hz⟩ := this
    rw [← hz]
    exact z.2
  obtain ⟨n, hn⟩ := (CFSG.LieType.BorelTits.pCore_isPGroup (G := ↥H ⧸ CFSG.Open.pCore 2 ↥H) p)
    ⟨_, hmem⟩
  refine ⟨n, ?_⟩
  have h1 : QuotientGroup.mk' (CFSG.Open.pCore 2 ↥H) ((⟨k, hkH⟩ : ↥H) ^ p ^ n) = 1 := by
    rw [map_pow]
    exact congrArg Subtype.val hn
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, mem_pCore_iff] at h1
  simpa using h1

end Parts

section AutI

variable {G : Type} [Group G] [Finite G] {U : Subgroup G} (hU : IsElemAbelian 2 U)

theorem autI_le_normalizer {K N : Subgroup G} (hNK : N ≤ Subgroup.normalizer (K : Set G)) :
    autI hU N ≤ Subgroup.normalizer (autI hU K : Set (MulAut (IntMod U hU))) := by
  intro φ hφ
  obtain ⟨g, hgN, rfl⟩ := (mem_autI hU).1 hφ
  refine A4.mem_normalizer_of_conj_mem fun ψ hψ => ?_
  obtain ⟨k, hkK, rfl⟩ := (mem_autI hU).1 hψ
  refine (mem_autI hU).2 ⟨g * k * g⁻¹, ?_, by rw [map_mul, map_mul, map_inv]⟩
  exact (Subgroup.mem_normalizer_iff.mp (hNK hgN) k).mp hkK

end AutI

namespace Setting

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} (S : Setting G T L V)
include S

theorem thompsonJ_not_le_centralizer_UH (h331 : Stmt3_3_1)
    (h5172 : Stmt5_1_7_two) {H : Subgroup G} (hH : IsHStar T (Subgroup.normalizer (L : Set G)) H)
    (hHZ : ¬ H ≤ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G)) :
    ¬ thompsonJ T ≤ Subgroup.centralizer (S.UH H : Set G) := by
  have h501 := S.hyp501
  have hTH : T ≤ H := hH.1.1
  have hZH' : ⁅quasithinOmegaOneCenter T, H⁆ ≠ ⊥ := by
    intro h
    apply hHZ
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp
      (by rw [Subgroup.commutator_comm]; exact h)
  obtain ⟨-, hLHJ, -⟩ := h5172 G T _ L V H 2 h501 S.isCh5Module hH hZH'
  obtain ⟨hMP, -⟩ := h501.minParabolic_of_isHStar h331 hH
  have hsyl : IsSylowTwoOf T H := isSylowTwoOf_of_le S.h13.sylow hTH
  have hF : CharTwo H := S.charTwo_of_inH hH.1
  obtain ⟨-, -, hUred⟩ := conjClosure_isTwoReducedIn_of_charTwo hsyl hF le_rfl
  have hZU : quasithinOmegaOneCenter T ≤ S.UH H := le_conjClosure _ _
  have hHU : ¬ H ≤ Subgroup.centralizer (S.UH H : Set G) :=
    fun h => hHZ (h.trans (Subgroup.centralizer_le hZU))
  intro hJ
  have h1 := (hMP.le_pCoreOf_iff_le_centralizer hUred hHU (thompsonJ T)).mpr
    (le_inf (thompsonJ_le_self T) hJ)
  have h2 := (hMP.commutator_lt_iff_le_pCoreOf (thompsonJ_le_self T)
    (B2F.R_le_normalizer_thompsonJ T)).mpr h1
  rw [twoResidual_eq_oTwoUpper', ← hLHJ] at h2
  exact lt_irrefl _ h2

end Setting

end CFSG.Quasithin.H13.A5
