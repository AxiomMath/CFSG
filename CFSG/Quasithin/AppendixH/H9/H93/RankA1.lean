module

public import CFSG.Quasithin.AppendixH.H9.H93.ExplicitA1
public import CFSG.Quasithin.AppendixH.H9.H93.RankGeneric

public section

namespace CFSG.ASVolI.ChH

open scoped Matrix
open CFSG.Quasithin CFSG.Open

namespace A1FixedPoints

private theorem mZJ_mulVec (a : Fin 4 → ZMod 2) : mZJ *ᵥ a = vZJ a := by
  revert a
  decide +kernel

private theorem mZJ_transpose : mZJᵀ = mZJ := by
  decide +kernel

private theorem pairActN_gZJ_pairVec (a b : Fin 4 → ZMod 2) :
    pairActN 4 gZJ (pairVec a b) = pairVec (vZJ a) (vZJ b) := by
  refine (pairActN_pairVec gZJ a b).trans ?_
  have h1 : ((gZJ : GL (Fin 4) (ZMod 2)) : Matrix (Fin 4) (Fin 4) (ZMod 2)) = mZJ := rfl
  have h2 : ((dualGLn 4 gZJ : GL (Fin 4) (ZMod 2)) : Matrix (Fin 4) (Fin 4) (ZMod 2)) = mZJ :=
    (dualGLn_val gZJ).trans mZJ_transpose
  rw [h1, h2, mZJ_mulVec, mZJ_mulVec]

private theorem card_fixed_by_A1 :
    Fintype.card {p : (Fin 4 → ZMod 2) × (Fin 4 → ZMod 2) //
      ∀ ε : Fin 4 → ZMod 2, A1fst ε p.1 p.2 = p.1 ∧ A1snd ε p.1 p.2 = p.2} = 2 := by
  decide +kernel

private theorem card_fixed_by_vZJ :
    Fintype.card {p : (Fin 4 → ZMod 2) × (Fin 4 → ZMod 2) //
      vZJ p.1 = p.1 ∧ vZJ p.2 = p.2} = 64 := by
  decide +kernel

private theorem vZJ_fixed_of_four_le (a b : Fin 4 → ZMod 2)
    (h : 4 ≤ Fintype.card {ε : Fin 4 → ZMod 2 // A1fst ε a b = a ∧ A1snd ε a b = b}) :
    vZJ a = a ∧ vZJ b = b :=
  (by decide +kernel : ∀ a b : Fin 4 → ZMod 2,
    4 ≤ Fintype.card {ε : Fin 4 → ZMod 2 // A1fst ε a b = a ∧ A1snd ε a b = b} →
      vZJ a = a ∧ vZJ b = b) a b h

private theorem four_le_fixed_fst (a : Fin 4 → ZMod 2) (h : vZJ a = a) :
    4 ≤ Fintype.card {ε : Fin 4 → ZMod 2 // A1fst ε a 0 = a ∧ A1snd ε a 0 = 0} :=
  (by decide +kernel : ∀ a : Fin 4 → ZMod 2, vZJ a = a →
    4 ≤ Fintype.card {ε : Fin 4 → ZMod 2 // A1fst ε a 0 = a ∧ A1snd ε a 0 = 0}) a h

private theorem four_le_fixed_snd (b : Fin 4 → ZMod 2) (h : vZJ b = b) :
    4 ≤ Fintype.card {ε : Fin 4 → ZMod 2 // A1fst ε 0 b = 0 ∧ A1snd ε 0 b = b} :=
  (by decide +kernel : ∀ b : Fin 4 → ZMod 2, vZJ b = b →
    4 ≤ Fintype.card {ε : Fin 4 → ZMod 2 // A1fst ε 0 b = 0 ∧ A1snd ε 0 b = b}) b h

private def pairCoordEquiv (n : ℕ) : PairN n ≃ (Fin n → ZMod 2) × (Fin n → ZMod 2) where
  toFun w := (Multiplicative.toAdd w.1, Multiplicative.toAdd w.2)
  invFun p := pairVec p.1 p.2
  left_inv _ := rfl
  right_inv _ := rfl

private theorem rk_eq_of_card_pairVec {n : ℕ} (H : Subgroup (PairN n))
    (Q : (Fin n → ZMod 2) × (Fin n → ZMod 2) → Prop) [Fintype {p // Q p}]
    (h : ∀ a b : Fin n → ZMod 2, pairVec a b ∈ H ↔ Q (a, b)) {m : ℕ}
    (hc : Fintype.card {p // Q p} = 2 ^ m) : rk H = m := by
  have hcard : Nat.card H = Nat.card {p // Q p} := by
    refine Nat.card_congr (Equiv.subtypeEquiv (pairCoordEquiv n) fun w => ?_)
    obtain ⟨a, b, rfl⟩ := pairVec_surj w
    exact h a b
  unfold rk
  rw [hcard, Nat.card_eq_fintype_card, hc, padicValNat.prime_pow]

private theorem rho_fix_iff {ρ : Multiplicative (Fin 4 → ZMod 2) →* MulAut (PairN 4)}
    (hρa : ∀ ε a b : Fin 4 → ZMod 2,
      ρ (Multiplicative.ofAdd ε) (pairVec a b) = pairVec (A1fst ε a b) (A1snd ε a b))
    (ε a b : Fin 4 → ZMod 2) :
    ρ (Multiplicative.ofAdd ε) (pairVec a b) = pairVec a b ↔
      A1fst ε a b = a ∧ A1snd ε a b = b :=
  ⟨fun h => pairVec_inj.mp ((hρa ε a b).symm.trans h),
    fun h => (hρa ε a b).trans (pairVec_inj.mpr h)⟩

private theorem natCard_fixing {ρ : Multiplicative (Fin 4 → ZMod 2) →* MulAut (PairN 4)}
    (hρa : ∀ ε a b : Fin 4 → ZMod 2,
      ρ (Multiplicative.ofAdd ε) (pairVec a b) = pairVec (A1fst ε a b) (A1snd ε a b))
    (a b : Fin 4 → ZMod 2) :
    Nat.card {ε : Fin 4 → ZMod 2 // ρ (Multiplicative.ofAdd ε) (pairVec a b) = pairVec a b} =
      Fintype.card {ε : Fin 4 → ZMod 2 // A1fst ε a b = a ∧ A1snd ε a b = b} :=
  (Nat.card_congr (Equiv.subtypeEquivRight fun ε => rho_fix_iff hρa ε a b)).trans
    Nat.card_eq_fintype_card

private theorem rk_fixV_range {ρ : Multiplicative (Fin 4 → ZMod 2) →* MulAut (PairN 4)}
    (hρa : ∀ ε a b : Fin 4 → ZMod 2,
      ρ (Multiplicative.ofAdd ε) (pairVec a b) = pairVec (A1fst ε a b) (A1snd ε a b)) :
    rk ↥(fixV ρ.range) = 1 :=
  rk_eq_of_card_pairVec (fixV ρ.range)
    (fun p => ∀ ε : Fin 4 → ZMod 2, A1fst ε p.1 p.2 = p.1 ∧ A1snd ε p.1 p.2 = p.2)
    (fun a b => (mem_fixV_range ρ (pairVec a b)).trans
      (forall_congr' fun ε => rho_fix_iff hρa ε a b))
    (m := 1) card_fixed_by_A1

private theorem rk_fixV_zpowers :
    rk ↥(fixV (Subgroup.zpowers (pairActN 4 gZJ))) = 6 :=
  rk_eq_of_card_pairVec (fixV (Subgroup.zpowers (pairActN 4 gZJ)))
    (fun p => vZJ p.1 = p.1 ∧ vZJ p.2 = p.2)
    (fun a b => (mem_fixV_zpowers _ _).trans
      ((congrArg (· = pairVec a b) (pairActN_gZJ_pairVec a b)).to_iff.trans pairVec_inj))
    (m := 6) card_fixed_by_vZJ

private theorem gammaCheck_two_eq_fixV {ρ : Multiplicative (Fin 4 → ZMod 2) →* MulAut (PairN 4)}
    (hρi : Function.Injective ρ)
    (hρa : ∀ ε a b : Fin 4 → ZMod 2,
      ρ (Multiplicative.ofAdd ε) (pairVec a b) = pairVec (A1fst ε a b) (A1snd ε a b)) :
    E3.gammaCheck 2 ρ.range = fixV (Subgroup.zpowers (pairActN 4 gZJ)) := by
  refine (CFSG.ASVolI.ChH.gammaCheck_two_range ρ hρi).trans
    (le_antisymm ((Subgroup.closure_le _).mpr ?_) ?_)
  · intro w hw
    obtain ⟨a, b, rfl⟩ := pairVec_surj w
    have h4 : 4 ≤ Fintype.card {ε : Fin 4 → ZMod 2 // A1fst ε a b = a ∧ A1snd ε a b = b} :=
      (natCard_fixing hρa a b) ▸ hw
    obtain ⟨h1, h2⟩ := vZJ_fixed_of_four_le a b h4
    refine (mem_fixV_zpowers _ _).mpr ((pairActN_gZJ_pairVec a b).trans ?_)
    rw [h1, h2]
  · intro w hw
    obtain ⟨a, b, rfl⟩ := pairVec_surj w
    obtain ⟨h1, h2⟩ := pairVec_inj.mp
      ((pairActN_gZJ_pairVec a b).symm.trans ((mem_fixV_zpowers _ _).mp hw))
    have ha : pairVec a 0 ∈ {w : PairN 4 |
        4 ≤ Nat.card {ε : Fin 4 → ZMod 2 // ρ (Multiplicative.ofAdd ε) w = w}} :=
      ((natCard_fixing hρa a 0).symm ▸ four_le_fixed_fst a h1 :)
    have hb : pairVec 0 b ∈ {w : PairN 4 |
        4 ≤ Nat.card {ε : Fin 4 → ZMod 2 // ρ (Multiplicative.ofAdd ε) w = w}} :=
      ((natCard_fixing hρa 0 b).symm ▸ four_le_fixed_snd b h2 :)
    have e : pairVec a b = pairVec a 0 * pairVec 0 b := by
      rw [pairVec_mul, add_zero, zero_add]
    rw [e]
    exact Subgroup.mul_mem _ (Subgroup.subset_closure ha) (Subgroup.subset_closure hb)

end A1FixedPoints

theorem rank_A1g :
    rk ↥(fixV A1g) = 1 ∧
      ∃ r ∈ A1g, (r ∈ Lg 4 ∧ rk ↥(commOn (V1n 4) (Subgroup.zpowers r)) = 1) ∧
        (∀ r' ∈ A1g, (r' ∈ Lg 4 ∧ rk ↥(commOn (V1n 4) (Subgroup.zpowers r')) = 1) → r' = r) ∧
        E3.gammaCheck 2 A1g = fixV (Subgroup.zpowers r) ∧
        rk ↥(fixV (Subgroup.zpowers r)) = 6 := by
  obtain ⟨ρ, hρi, hρr, hρa, -⟩ := exists_param_A1g
  have huniq : ∀ r' ∈ A1g,
      (r' ∈ Lg 4 ∧ rk ↥(commOn (V1n 4) (Subgroup.zpowers r')) = 1) → r' = pairActN 4 gZJ := by
    obtain ⟨r₀, hr₀⟩ := Set.ncard_eq_one.mp ncard_tv_A1g
    intro r' hr' htv'
    have h1 : r' ∈ {g : MulAut (PairN 4) | g ∈ A1g ∧ IsTvElt g} := ⟨hr', htv'⟩
    have h2 : pairActN 4 gZJ ∈ {g : MulAut (PairN 4) | g ∈ A1g ∧ IsTvElt g} :=
      ⟨pairActN_gZJ_mem_A1g, isTvElt_pairActN_gZJ⟩
    rw [hr₀] at h1 h2
    exact (Set.mem_singleton_iff.mp h1).trans (Set.mem_singleton_iff.mp h2).symm
  refine ⟨?_, pairActN 4 gZJ, pairActN_gZJ_mem_A1g, isTvElt_pairActN_gZJ, huniq, ?_,
    A1FixedPoints.rk_fixV_zpowers⟩
  · rw [← hρr]
    exact A1FixedPoints.rk_fixV_range hρa
  · rw [← hρr]
    exact A1FixedPoints.gammaCheck_two_eq_fixV hρi hρa

end CFSG.ASVolI.ChH
