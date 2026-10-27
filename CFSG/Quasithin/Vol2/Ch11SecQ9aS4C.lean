module

public import CFSG.Quasithin.Vol2.Ch5Sec1Hall
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticFourSylow
public import CFSG.ClassicalInvolution.ModelFacts.OddCover.Sp4Basic
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticHigherSylow
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListBasic
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7aResidualSp
public import CFSG.Quasithin.Vol2.Ch11SecAKind

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecS.C11P9A

open Matrix CFSG.Quasithin CFSG.Assembly.LowTwoRank
  CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
  CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
  CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl CFSG.QuasithinUnique.Setup.X7a
  CFSG.QuasithinUnique.Vol2Native.A312L CFSG.ClassicalInvolution.ModelFacts.OddCover
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_apply)

variable {K : Type} [Field K]

theorem qSp_mem_unipotent (x y z : K) : qSp x y z ∈ unipotent 2 K := by
  have e : qSp x y z =
      CFSG.LocalAnalysis.ComponentInitial.SymplecticFour.tau (symm3_transpose x y z) := by
    apply statedSp_ext
    rw [CFSG.LocalAnalysis.ComponentInitial.SymplecticFour.coe_tau]
    rfl
  rw [e]
  exact CFSG.LocalAnalysis.ComponentInitial.SymplecticFour.tau_mem_unipotent _

theorem nSp_mem_unipotent (r : K) : nSp r ∈ unipotent 2 K := by
  have e : nSp r = CFSG.LocalAnalysis.ComponentInitial.SymplecticFour.lam r := by
    apply statedSp_ext
    rw [CFSG.LocalAnalysis.ComponentInitial.SymplecticFour.coe_lam]
    change mat 2 K (lSp K (uGL r)) = _
    rw [mat_lSp, coe_uGL]
    rfl
  rw [e]
  exact CFSG.LocalAnalysis.ComponentInitial.SymplecticFour.lam_mem_unipotent r

theorem Usp_eq_unipotent [Finite K] : Usp K = unipotent 2 K := by
  apply Subgroup.eq_of_le_of_card_ge
  · rintro _ ⟨x, y, z, r, rfl⟩
    exact mul_mem (qSp_mem_unipotent x y z) (nSp_mem_unipotent r)
  · rw [card_unipotent, card_Usp]
    norm_num

theorem card_torus [Finite K] : Nat.card ↥(torus 2 K) = (Nat.card K - 1) ^ 2 := by
  rw [torus, ← Nat.card_congr (MonoidHom.ofInjective torusHom_injective).toEquiv, Nat.card_fun,
    Nat.card_units, Nat.card_eq_fintype_card (α := Fin 2), Fintype.card_fin]

theorem unipotent_inf_torus [Finite K] [CharP K 2] : unipotent 2 K ⊓ torus 2 K = ⊥ := by
  obtain ⟨P₀, hP₀⟩ := exists_sylow_unipotent (K := K) 2 2
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hU2 : IsPGroup 2 (unipotent 2 K) := hP₀ ▸ P₀.isPGroup'
  obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp hU2
  have hodd : Odd (Nat.card ↥(torus 2 K)) := by
    have := Fintype.ofFinite K
    have h2 : 2 ∣ Nat.card K := by
      rw [Nat.card_eq_fintype_card, ← CharP.cast_eq_zero_iff K 2]
      exact FiniteField.cast_card_eq_zero K
    have h1 : 1 ≤ Nat.card K := Nat.card_pos
    rw [card_torus]
    exact (Nat.Even.sub_odd h1 (even_iff_two_dvd.mpr h2) odd_one).pow
  exact (Subgroup.disjoint_of_coprime_natCard (by
    rw [hm]
    exact Nat.Coprime.pow_left m (Nat.coprime_two_left.mpr hodd))).eq_bot

theorem exists_conj_torus_of_isHall_sp [Finite K] [CharP K 2] {D : Subgroup (StatedSp 2 K)}
    (hD : CFSG.QuasithinUnique.Lin2.IsHallTwoPrimeOf D (borelSubgroup 2 K)) :
    ∃ x ∈ unipotent 2 K, D = (torus 2 K).map (MulAut.conj x).toMonoidHom := by
  obtain ⟨hDB, hDodd, k, hk⟩ := hD
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P, hP⟩ := exists_sylow_unipotent (K := K) 2 2
  have hU2 : IsPGroup 2 (unipotent 2 K) := hP ▸ P.isPGroup'
  have hUB : unipotent 2 K ≤ borelSubgroup 2 K := unipotent_le_borelSubgroup
  have hBN : borelSubgroup 2 K ≤ Subgroup.normalizer (unipotent 2 K : Set (StatedSp 2 K)) :=
    (normalizer_unipotent (r := 2) (K := K)).ge
  have hodd : Odd ((unipotent 2 K).relIndex (borelSubgroup 2 K)) := by
    have h1 : ¬ 2 ∣ (P : Subgroup (StatedSp 2 K)).index := P.not_dvd_index
    rw [hP] at h1
    exact Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp fun h =>
      h1 (h.trans (Subgroup.relIndex_dvd_index_of_le hUB)))
  have hT : torus 2 K ≤ borelSubgroup 2 K := torus_le_borelSubgroup
  have hUTs : unipotent 2 K ⊔ torus 2 K = borelSubgroup 2 K :=
    le_antisymm (sup_le hUB hT) borelSubgroup_le_sup_torus
  obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp hU2
  have hUD : unipotent 2 K ⊓ D = ⊥ := (Subgroup.disjoint_of_coprime_natCard (by
    rw [hm]
    exact Nat.Coprime.pow_left m (Nat.coprime_two_left.mpr hDodd))).eq_bot
  have hcU := Subgroup.relIndex_mul_card (unipotent 2 K) (borelSubgroup 2 K)
  have hcD := Subgroup.relIndex_mul_card D (borelSubgroup 2 K)
  rw [inf_of_le_left hUB, hm] at hcU
  rw [inf_of_le_left hDB, hk] at hcD
  have hmk : m = k := CFSG.Quasithin.Vol2.Ch11.SecA.eq_of_two_pow_mul_odd
    (m := (unipotent 2 K).relIndex (borelSubgroup 2 K)) (m' := Nat.card D) hodd hDodd
    (by rw [mul_comm, hcU, ← hcD])
  subst hmk
  have hB : Nat.card ↥(borelSubgroup 2 K) = Nat.card ↥(unipotent 2 K) * Nat.card D := by
    rw [hm, ← hcD]
  have hUDs : unipotent 2 K ⊔ D = borelSubgroup 2 K := by
    refine Subgroup.eq_of_le_of_card_ge (sup_le hUB hDB) ?_
    rw [hB]
    refine Nat.le_of_dvd Nat.card_pos (Nat.Coprime.mul_dvd_of_dvd_of_dvd ?_
      (Subgroup.card_dvd_of_le le_sup_left) (Subgroup.card_dvd_of_le le_sup_right))
    rw [hm]
    exact Nat.Coprime.pow_left m (Nat.coprime_two_left.mpr hDodd)
  exact CFSG.Quasithin.H13.exists_mem_conj_of_complements hUB hBN hU2 hodd hT
    unipotent_inf_torus hUTs hDB hUD hUDs

end CFSG.Quasithin.Vol2.Ch11.SecS.C11P9A
