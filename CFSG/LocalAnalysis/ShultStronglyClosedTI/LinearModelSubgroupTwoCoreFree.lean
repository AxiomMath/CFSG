module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.LinearModelSubgroupTwoCoreFreeBasic
public import CFSG.GroupTheory.BurnsideNormalComplement
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.LinearModelSubgroupInvertedTorus

public noncomputable section

namespace CFSG.ShultStronglyClosedTI.LinearModel

open CFSG.BenderSuzuki.MatrixGroups
open CFSG.ShultStronglyClosedTI.TwoCoreGrowth

universe u

variable {K : Type u} [Field K] [Finite K]

theorem two_core_free_order_two_torus (f : ℕ) (hf : 2 ≤ f) (hcard : Nat.card K = 2 ^ f)
    (A : Subgroup (PSL2MatrixGroup K)) (hcore : CFSG.pCore 2 A = ⊥) (S : Sylow 2 A)
    (hS : Nat.card S = 2) {u : A} (hu : orderOf u = 2) :
    ∃ W : Subgroup A, W ≠ ⊥ ∧ IsCyclic W ∧ Odd (Nat.card W) ∧
      (∀ w ∈ W, u * w * u⁻¹ = w⁻¹) ∧ W ⊓ Subgroup.zpowers u = ⊥ ∧
      (∀ W₀ : Subgroup A, W₀ ≤ W → W₀ ≠ ⊥ →
        Subgroup.centralizer (W₀ : Set A) = W ∧
        Subgroup.normalizer (W₀ : Set A) = W ⊔ Subgroup.zpowers u) ∧
      W = CFSG.oddCore A ∧ W.Normal ∧ Nat.Coprime (Nat.card W) W.index ∧
        W ⊔ Subgroup.zpowers u = ⊤ := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hNC : Subgroup.normalizer ((S : Subgroup A) : Set A) ≤
      Subgroup.centralizer ((S : Subgroup A) : Set A) := by
    intro g hg
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    by_cases hx1 : x = 1
    · rw [hx1, one_mul, mul_one]
    have hgx : g * x * g⁻¹ ∈ (S : Subgroup A) := (Subgroup.mem_normalizer_iff.mp hg x).mp hx
    have hgx1 : g * x * g⁻¹ ≠ 1 := fun h => hx1 (conj_eq_one_iff.mp h)
    obtain ⟨s, -, hsuniq⟩ := (Nat.card_eq_two_iff' (1 : (S : Subgroup A))).mp hS
    have h1 : (⟨x, hx⟩ : (S : Subgroup A)) = s := hsuniq _ fun h => hx1 (congrArg Subtype.val h)
    have h2 : (⟨g * x * g⁻¹, hgx⟩ : (S : Subgroup A)) = s :=
      hsuniq _ fun h => hgx1 (congrArg Subtype.val h)
    have heq : g * x * g⁻¹ = x := congrArg Subtype.val (h2.trans h1.symm)
    calc x * g = g * x * g⁻¹ * g := by rw [heq]
      _ = g * x := by group
  obtain ⟨Kb, hKn, hK2, hKindex, -, -, -, hKsup, -, -, -⟩ :=
    CFSG.GroupTheory.burnside_normal_complement S hNC
  have hKodd : Odd (Nat.card Kb) := Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp hK2)
  have hKne : Kb ≠ ⊥ := by
    intro hK
    rw [hK, bot_sup_eq] at hKsup
    have hSn : (S : Subgroup A).Normal := by rw [hKsup]; infer_instance
    have hSle : (S : Subgroup A) ≤ CFSG.pCore 2 A := le_sSup ⟨hSn, S.isPGroup'⟩
    rw [hcore, le_bot_iff] at hSle
    have h := congrArg (fun H : Subgroup A => Nat.card H) hSle
    simp only [hS, Subgroup.card_bot] at h
    omega
  let φ : MulAut Kb := MulAut.conjNormal (H := Kb) u
  have hu2 : u ^ 2 = 1 := by
    have h := pow_orderOf_eq_one u
    rwa [hu] at h
  have huL : orderOf (u : PSL2MatrixGroup K) = 2 := (Subgroup.orderOf_coe u).trans hu
  have hφfree : MonoidHom.FixedPointFree φ := by
    intro k hk
    have hfix : u * k * u⁻¹ = k := by
      simpa only [φ, MulAut.conjNormal_apply] using congrArg Subtype.val hk
    have hkodd : Odd (orderOf (((k : A) : PSL2MatrixGroup K))) := by
      rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe]
      exact hKodd.of_dvd_nat (orderOf_dvd_natCard k)
    have hcomm : ((k : A) : PSL2MatrixGroup K) * u = u * ((k : A) : PSL2MatrixGroup K) := by
      have h : (k : A) * u = u * k := by
        calc (k : A) * u = u * k * u⁻¹ * u := by rw [hfix]
          _ = u * k := by group
      exact congrArg Subtype.val h
    exact Subtype.ext (Subtype.ext (eq_one_of_odd_of_commute_involution hcard huL hkodd hcomm))
  have hφinv : Function.Involutive φ := by
    intro k
    apply Subtype.ext
    simp only [φ, MulAut.conjNormal_apply]
    have hu2' : u * u = 1 := by rw [← pow_two, hu2]
    calc u * (u * k * u⁻¹) * u⁻¹ = (u * u) * k * (u * u)⁻¹ := by group
      _ = k := by rw [hu2', one_mul, inv_one, mul_one]
  have hKinv : ∀ k ∈ Kb, u * k * u⁻¹ = k⁻¹ := by
    intro k hk
    have h := congrFun (hφfree.coe_eq_inv_of_involutive hφinv) ⟨k, hk⟩
    simpa only [φ, MulAut.conjNormal_apply, Pi.inv_apply, Subgroup.coe_inv,
      Subgroup.coe_mk] using congrArg Subtype.val h
  obtain ⟨⟨y, hyK⟩, hy1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hKne
  have hy : y ≠ 1 := fun h => hy1 (Subtype.ext h)
  have hyodd : Odd (orderOf y) := by
    have h := orderOf_dvd_natCard (⟨y, hyK⟩ : Kb)
    rw [Subgroup.orderOf_mk] at h
    exact hKodd.of_dvd_nat h
  obtain ⟨hWne, hWcyc, hWodd, hWinv, hWu, hW⟩ :=
    inverted_odd_centralizer_torus f hf hcard A hu hy hyodd (hKinv y hyK)
  set W := Subgroup.centralizer ({y} : Set A)
  have hKW : Kb ≤ W := by
    intro k hk
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h := hφfree.commute_all_of_involutive hφinv ⟨k, hk⟩ ⟨y, hyK⟩
    exact congrArg Subtype.val h.eq
  have hAcard : Nat.card A = Nat.card Kb * 2 := by
    have h := Kb.card_mul_index
    rw [hKindex, hS] at h
    exact h.symm
  have hWK : W = Kb := by
    obtain ⟨c, hc⟩ := Subgroup.card_dvd_of_le hKW
    have hWA : Nat.card W ∣ Nat.card A := Subgroup.card_subgroup_dvd_card W
    rw [hAcard, hc] at hWA
    have hKpos : 0 < Nat.card Kb := Nat.card_pos
    have hc2 : c ∣ 2 := (Nat.mul_dvd_mul_iff_left hKpos).mp hWA
    rcases (Nat.dvd_prime Nat.prime_two).mp hc2 with h | h
    · exact (Subgroup.eq_of_le_of_card_ge hKW (by rw [hc, h, mul_one])).symm
    · exfalso
      rw [hc, h] at hWodd
      exact (Nat.not_even_iff_odd.mpr hWodd) (even_two.mul_left _)
  have hWnormal : W.Normal := hWK ▸ hKn
  have hWindex : W.index = 2 := by rw [hWK, hKindex, hS]
  have hWtop : W ⊔ Subgroup.zpowers u = ⊤ := by
    rw [← (hW W le_rfl hWne).2]
    exact Subgroup.normalizer_eq_top_iff.mpr hWnormal
  have hWcore : W = CFSG.oddCore A := by
    refine le_antisymm (le_sSup ⟨hWnormal, hWodd⟩) (sSup_le fun N hN => ?_)
    have hq : IsPGroup 2 (A ⧸ W) :=
      IsPGroup.of_card (n := 1) (by rw [← Subgroup.index_eq_card, hWindex, pow_one])
    exact CFSG.GroupTheory.le_of_normal_coprime_of_isPGroup_quotient W N hq
      (fun h => (Nat.not_even_iff_odd.mpr hN.2) (even_iff_two_dvd.mpr h))
  exact ⟨W, hWne, hWcyc, hWodd, hWinv, hWu, hW, hWcore, hWnormal,
    by rw [hWindex]; exact hWodd.coprime_two_right, hWtop⟩

theorem linear_two_core_free_subgroup_torus_and_involutions (f : ℕ) (hf : 2 ≤ f)
    (hcard : Nat.card K = 2 ^ f) (A : Subgroup (PSL2MatrixGroup K))
    (hAeven : Even (Nat.card A)) (hcore : CFSG.pCore 2 A = ⊥) :
    (∀ u v : A, orderOf u = 2 → orderOf v = 2 → IsConj u v) ∧
    (∀ u : A, orderOf u = 2 → ∃ W : Subgroup A, W ≠ ⊥ ∧ IsCyclic W ∧ Odd (Nat.card W) ∧
      (∀ w ∈ W, u * w * u⁻¹ = w⁻¹) ∧ W ⊓ Subgroup.zpowers u = ⊥ ∧
      (∀ W₀ : Subgroup A, W₀ ≤ W → W₀ ≠ ⊥ →
        Subgroup.centralizer (W₀ : Set A) = W ∧
        Subgroup.normalizer (W₀ : Set A) = W ⊔ Subgroup.zpowers u) ∧
      (∀ S : Sylow 2 A, Nat.card S = 2 →
        W = CFSG.oddCore A ∧ W.Normal ∧ Nat.Coprime (Nat.card W) W.index ∧
          W ⊔ Subgroup.zpowers u = ⊤)) ∧
    (∀ S : Sylow 2 A, 4 ≤ Nat.card S → CFSG.oddCore A = ⊥) := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine ⟨fun u v hu hv => two_core_free_involutions_conjugate hcard A hAeven hcore hu hv, ?_,
    fun S hS => oddCore_eq_bot_of_four_le hcard A S hS⟩
  intro u hu
  let S₀ : Sylow 2 A := default
  have hS₀ : (S₀ : Subgroup A) ≠ ⊥ := S₀.ne_bot_of_dvd_card (even_iff_two_dvd.mp hAeven)
  obtain ⟨k, hk⟩ := S₀.isPGroup'.exists_card_eq
  have hcardS : ∀ S : Sylow 2 A, Nat.card S = 2 ^ k := fun S => by
    rw [Sylow.card_eq_multiplicity, ← hk, Sylow.card_eq_multiplicity]
  have hk0 : k ≠ 0 := by
    rintro rfl
    exact hS₀ (Subgroup.card_eq_one.mp (by rw [hk, pow_zero]))
  by_cases hk1 : k = 1
  ·
    obtain ⟨W, hWne, hWcyc, hWodd, hWinv, hWu, hW, hWcore⟩ :=
      two_core_free_order_two_torus f hf hcard A hcore S₀ (by rw [hk, hk1, pow_one]) hu
    exact ⟨W, hWne, hWcyc, hWodd, hWinv, hWu, hW, fun _ _ => hWcore⟩
  ·
    obtain ⟨a, b, ha, hb, hab⟩ := exists_noncommuting_involutions hcard A hAeven hcore
    obtain ⟨c, hc⟩ := isConj_iff.mp (two_core_free_involutions_conjugate hcard A hAeven hcore hu ha)
    set v := c⁻¹ * b * c
    have hv : orderOf v = 2 := by
      rw [show v = (MulAut.conj c⁻¹) b by simp [v], MulEquiv.orderOf_eq, hb]
    have huv : u * v ≠ v * u := by
      intro h
      apply hab
      rw [← hc]
      calc c * u * c⁻¹ * b = c * (u * v) * c⁻¹ := by simp only [v]; group
        _ = c * (v * u) * c⁻¹ := by rw [h]
        _ = b * (c * u * c⁻¹) := by simp only [v]; group
    have hui : u⁻¹ = u := inv_eq_self_of_orderOf_eq_two hu
    have hvi : v⁻¹ = v := inv_eq_self_of_orderOf_eq_two hv
    have hy : u * v ≠ 1 := by
      intro h
      apply huv
      rw [mul_eq_one_iff_eq_inv.mp h, hvi]
    have hyodd : Odd (orderOf (u * v)) := by
      by_contra heven
      rw [Nat.not_odd_iff_even, ← Subgroup.orderOf_coe] at heven
      have h2 := orderOf_eq_two_of_even hcard heven
      rw [Subgroup.orderOf_coe] at h2
      have hsq : (u * v) ^ 2 = 1 := by
        have h := pow_orderOf_eq_one (u * v)
        rwa [h2] at h
      apply huv
      have h' : (u * v) * (u * v) = 1 := by rw [← pow_two, hsq]
      calc u * v = (u * v) * (u * v) * (v⁻¹ * u⁻¹) := by group
        _ = v * u := by rw [h', one_mul, hvi, hui]
    have huy : u * (u * v) * u⁻¹ = (u * v)⁻¹ := by
      rw [mul_inv_rev, hvi, hui]
      calc u * (u * v) * u = (u * u) * v * u := by group
        _ = v * u := by rw [← pow_two, show u ^ 2 = 1 by
              have h := pow_orderOf_eq_one u
              rwa [hu] at h, one_mul]
    obtain ⟨hWne, hWcyc, hWodd, hWinv, hWu, hW⟩ :=
      inverted_odd_centralizer_torus f hf hcard A hu hy hyodd huy
    refine ⟨_, hWne, hWcyc, hWodd, hWinv, hWu, hW, fun S hS => ?_⟩
    exfalso
    rw [hcardS S] at hS
    have : k ≤ 1 := by
      by_contra h
      have h' : 2 ^ 2 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    omega

end CFSG.ShultStronglyClosedTI.LinearModel
