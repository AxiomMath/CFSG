module

public import CFSG.RankThree.PartTwo.Sec4.RonanK432RowU52Dg
public import CFSG.RankThree.PartTwo.Sec4.RonanK432WreathProd
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434SmallTwoIVU52
public import CFSG.CharacterTheory.Semidihedral.CyclicPairFrattini
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHigherLinearInnerFixed
public import CFSG.Quasithin.EmptyFaithful.S1422Basic
public import Certificates.Data.A5

public section

namespace CFSG.RankThree.PartTwo.Sec4.RonanK432

open Matrix CFSG.RankThree.PartTwo.Sec4 CFSG.RankThree.PartTwo.Sec4.Item434Kit
open CFSG.Assembly.RankThreeEven (projSU)

@[expose] def zv : Fin 3 → (Fin 5 → ZMod 3) :=
  ![![1, 0, 0, 0, -1], ![0, 1, 0, 0, -1], ![0, 0, 1, 0, -1]]

@[expose] def ev : Fin 5 → ZMod 3 := ![0, 0, 0, 1, -1]

@[expose] def Bv (a k : ZMod 3) : Fin 5 → ZMod 3 := ![a, a, a, k, -k]

@[expose] def τc : Equiv.Perm (Fin 5) := Equiv.swap 0 1 * Equiv.swap 1 2

@[expose] def Vec (v : Fin 3 → ZMod 3) : Fin 5 → ZMod 3 :=
  (v 0).val • zv 0 + (v 1).val • zv 1 + (v 2).val • zv 2

theorem zv_sum (i : Fin 3) : ∑ j, zv i j = 0 := by
  fin_cases i <;> decide

theorem ev_sum : ∑ j, ev j = 0 := by
  decide

theorem Vec_eq (v : Fin 3 → ZMod 3) :
    Vec v = ![v 0, v 1, v 2, 0, -(v 0 + v 1 + v 2)] := by
  funext j
  fin_cases j <;> simp [Vec, zv, nsmul_eq_mul] <;> ring

theorem three_nsmul_eq_zero (v : Fin 5 → ZMod 3) : (3 : ℕ) • v = 0 := by
  have h3z : (3 : ZMod 3) = 0 := by decide
  funext j
  simp [nsmul_eq_mul, h3z]

theorem vec_lin (a k : ZMod 3) (C : Fin 5 → ZMod 3) (hC : C = ![1, 1, 1, 0, 0]) :
    a • C + k • ev = Bv a k := by
  subst hC
  funext j
  fin_cases j <;> simp [ev, Bv, smul_eq_mul]

section Elements

variable {ω : U52Fieldˣ}

@[expose] noncomputable def zS (h3 : ω ^ 3 = 1) (i : Fin 3) : projSU 5 2 1 :=
  ⟨ProjGenLinGroup.mk (dg ω (zv i)), mk_dg_mem h3 (zv_sum i)⟩

@[expose] noncomputable def eS (h3 : ω ^ 3 = 1) : projSU 5 2 1 :=
  ⟨ProjGenLinGroup.mk (dg ω ev), mk_dg_mem h3 ev_sum⟩

@[expose] noncomputable def tS : projSU 5 2 1 :=
  ⟨ProjGenLinGroup.mk (pg τc), mk_pg_mem τc⟩

theorem coe_zS (h3 : ω ^ 3 = 1) (i : Fin 3) :
    ((zS h3 i : projSU 5 2 1) : ProjGenLinGroup (Fin 5) U52Field) =
      ProjGenLinGroup.mk (dg ω (zv i)) := rfl

theorem coe_eS (h3 : ω ^ 3 = 1) :
    ((eS h3 : projSU 5 2 1) : ProjGenLinGroup (Fin 5) U52Field) =
      ProjGenLinGroup.mk (dg ω ev) := rfl

theorem coe_tS :
    ((tS : projSU 5 2 1) : ProjGenLinGroup (Fin 5) U52Field) =
      ProjGenLinGroup.mk (pg τc) := rfl

theorem dg_pow (h3 : ω ^ 3 = 1) (β : Fin 5 → ZMod 3) (n : ℕ) :
    dg ω β ^ n = dg ω (n • β) := by
  rw [← zpow_natCast, dg_zpow h3, natCast_zsmul]

theorem u52CoeVecElt (h3 : ω ^ 3 = 1) (v : Fin 3 → ZMod 3) :
    ((vecElt (zS h3) v : projSU 5 2 1) : ProjGenLinGroup (Fin 5) U52Field) =
      ProjGenLinGroup.mk (dg ω (Vec v)) := by
  unfold vecElt
  simp only [Subgroup.coe_mul, Subgroup.coe_pow, coe_zS]
  rw [← map_pow, ← map_pow, ← map_pow, ← map_mul, ← map_mul, dg_pow h3, dg_pow h3, dg_pow h3,
    ← dg_mul h3, ← dg_mul h3]
  rfl

theorem coe_vecElt_ones (h3 : ω ^ 3 = 1) :
    ((vecElt (zS h3) ![1, 1, 1] : projSU 5 2 1) : ProjGenLinGroup (Fin 5) U52Field) =
      ProjGenLinGroup.mk (dg ω ![1, 1, 1, 0, 0]) := by
  rw [u52CoeVecElt h3]
  have hv : Vec ![1, 1, 1] = ![1, 1, 1, 0, 0] := by decide
  rw [hv]

end Elements


section Relations

variable {ω : U52Fieldˣ}

theorem zS_pow_three (h3 : ω ^ 3 = 1) (i : Fin 3) : zS h3 i ^ 3 = 1 := by
  apply Subtype.ext
  rw [Subgroup.coe_pow, OneMemClass.coe_one, coe_zS, ← map_pow, dg_pow h3, three_nsmul_eq_zero,
    dg_zero, map_one]

theorem zS_comm (h3 : ω ^ 3 = 1) (i j : Fin 3) : zS h3 i * zS h3 j = zS h3 j * zS h3 i := by
  apply Subtype.ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul, coe_zS, coe_zS]
  exact mk_dg_comm h3 _ _

theorem eS_pow_three (h3 : ω ^ 3 = 1) : eS h3 ^ 3 = 1 := by
  apply Subtype.ext
  rw [Subgroup.coe_pow, OneMemClass.coe_one, coe_eS, ← map_pow, dg_pow h3, three_nsmul_eq_zero,
    dg_zero, map_one]

theorem tS_pow_three : tS ^ 3 = 1 := by
  have h : τc ^ 3 = 1 := by decide
  apply Subtype.ext
  rw [Subgroup.coe_pow, OneMemClass.coe_one, coe_tS, ← map_pow, ← map_pow, h, map_one, map_one]

theorem zS_eS_comm (h3 : ω ^ 3 = 1) (i : Fin 3) : zS h3 i * eS h3 = eS h3 * zS h3 i := by
  apply Subtype.ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul, coe_zS, coe_eS]
  exact mk_dg_comm h3 _ _

theorem tS_eS_comm (h3 : ω ^ 3 = 1) : tS * eS h3 = eS h3 * tS := by
  apply Subtype.ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul, coe_tS, coe_eS]
  have h := mk_pg_mul_dg_mul_inv (ω := ω) τc ev
  have hf : (fun j => ev (τc⁻¹ j)) = ev := by decide
  rw [hf] at h
  calc ProjGenLinGroup.mk (pg τc) * ProjGenLinGroup.mk (dg ω ev)
      = (ProjGenLinGroup.mk (pg τc) * ProjGenLinGroup.mk (dg ω ev) *
          (ProjGenLinGroup.mk (pg τc))⁻¹) * ProjGenLinGroup.mk (pg τc) := by group
    _ = ProjGenLinGroup.mk (dg ω ev) * ProjGenLinGroup.mk (pg τc) := by rw [h]

theorem conj0 (h3 : ω ^ 3 = 1) : tS * zS h3 0 * tS⁻¹ = zS h3 1 := by
  apply Subtype.ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, coe_tS, coe_zS, coe_zS,
    mk_pg_mul_dg_mul_inv]
  have hf : (fun j => zv 0 (τc⁻¹ j)) = zv 1 := by decide
  rw [hf]

theorem conj1 (h3 : ω ^ 3 = 1) : tS * zS h3 1 * tS⁻¹ = zS h3 2 := by
  apply Subtype.ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, coe_tS, coe_zS, coe_zS,
    mk_pg_mul_dg_mul_inv]
  have hf : (fun j => zv 1 (τc⁻¹ j)) = zv 2 := by decide
  rw [hf]

theorem conj2 (h3 : ω ^ 3 = 1) : tS * zS h3 2 * tS⁻¹ = zS h3 0 := by
  apply Subtype.ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, coe_tS, coe_zS, coe_zS,
    mk_pg_mul_dg_mul_inv]
  have hf : (fun j => zv 2 (τc⁻¹ j)) = zv 0 := by decide
  rw [hf]

theorem mk_dg_ne_mk_dg_mul_pg {ρ : Equiv.Perm (Fin 5)} (hρ : ρ⁻¹ 0 ≠ 0) (β V : Fin 5 → ZMod 3) :
    (ProjGenLinGroup.mk (dg ω β) : ProjGenLinGroup (Fin 5) U52Field) ≠
      ProjGenLinGroup.mk (dg ω V * pg ρ) := by
  intro h
  obtain ⟨u, hu⟩ := Matrix.ProjGenLinGroup.mk_eq_mk_iff.mp h
  have h0 := congrArg (fun g : GL (Fin 5) U52Field =>
    ((g : GL (Fin 5) U52Field) : Matrix (Fin 5) (Fin 5) U52Field) 0 (ρ⁻¹ 0)) hu
  have hne : (0 : Fin 5) ≠ (Equiv.symm ρ) 0 := by
    intro h1
    exact hρ (by rw [Equiv.Perm.inv_def]; exact h1.symm)
  simp [dg_apply, pg_apply, Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.scalar_apply,
    Matrix.diagonal_apply, hne] at h0
  exact Units.ne_zero _ h0.symm

theorem vec_inj (h3 : ω ^ 3 = 1) (hω : orderOf ω = 3) (v : Fin 3 → ZMod 3)
    (hv : vecElt (zS h3) v = 1) : v = 0 := by
  have h := congrArg (fun x : projSU 5 2 1 => (x : ProjGenLinGroup (Fin 5) U52Field)) hv
  rw [u52CoeVecElt h3, OneMemClass.coe_one] at h
  have h' : ProjGenLinGroup.mk (dg ω (Vec v)) = ProjGenLinGroup.mk (dg ω 0) := by
    rw [dg_zero, map_one]
    exact h
  obtain ⟨c, hc⟩ := mk_dg_eq_iff h3 hω h'
  have k0 : (0 : ZMod 3) = v 0 + c := by
    have := hc 0
    rw [Vec_eq] at this
    exact this
  have k1 : (0 : ZMod 3) = v 1 + c := by
    have := hc 1
    rw [Vec_eq] at this
    exact this
  have k2 : (0 : ZMod 3) = v 2 + c := by
    have := hc 2
    rw [Vec_eq] at this
    exact this
  have k3 : (0 : ZMod 3) = 0 + c := by
    have := hc 3
    rw [Vec_eq] at this
    exact this
  obtain ⟨e0, e1, e2⟩ := (by decide : ∀ x y z d : ZMod 3, (0 : ZMod 3) = x + d →
    (0 : ZMod 3) = y + d → (0 : ZMod 3) = z + d → (0 : ZMod 3) = 0 + d →
    x = 0 ∧ y = 0 ∧ z = 0) (v 0) (v 1) (v 2) c k0 k1 k2 k3
  funext i
  fin_cases i
  · exact e0
  · exact e1
  · exact e2

theorem t_ne_aux (h3 : ω ^ 3 = 1) (v : Fin 3 → ZMod 3) (hv : vecElt (zS h3) v = tS) : False := by
  have h := congrArg (fun x : projSU 5 2 1 => (x : ProjGenLinGroup (Fin 5) U52Field)) hv
  rw [u52CoeVecElt h3, coe_tS] at h
  have h' : ProjGenLinGroup.mk (dg ω (Vec v)) = ProjGenLinGroup.mk (dg ω 0 * pg τc) := by
    rw [dg_zero, one_mul (pg τc)]
    exact h
  exact mk_dg_ne_mk_dg_mul_pg (ρ := τc) (by decide) (Vec v) 0 h'

theorem wreathFacts_u52 (h3 : ω ^ 3 = 1) (hω : orderOf ω = 3) : WreathFacts (zS h3) tS where
  pow_z := zS_pow_three h3
  comm_z := zS_comm h3
  inj := fun v hv => vec_inj h3 hω v hv
  pow_t := tS_pow_three
  conj0 := conj0 h3
  conj1 := conj1 h3
  conj2 := conj2 h3
  t_ne := fun v hv => t_ne_aux h3 v hv

theorem eS_not_mem_wreathW (h3 : ω ^ 3 = 1) (hω : orderOf ω = 3) :
    eS h3 ∉ wreathW (zS h3) tS := by
  intro hmem
  obtain ⟨v, j, hx⟩ := mem_wreathW (wreathFacts_u52 h3 hω) hmem
  have hpow : ∀ n : ℕ, (ProjGenLinGroup.mk (pg τc)) ^ n = ProjGenLinGroup.mk (pg (τc ^ n)) :=
    fun n => by rw [map_pow, map_pow]
  have h := congrArg (fun x : projSU 5 2 1 => (x : ProjGenLinGroup (Fin 5) U52Field)) hx
  rw [coe_eS, Subgroup.coe_mul, u52CoeVecElt h3, Subgroup.coe_pow, coe_tS, hpow, ← map_mul] at h
  have hj : (j : ℕ) = 0 ∨ (j : ℕ) = 1 ∨ (j : ℕ) = 2 := by omega
  rcases hj with hj | hj | hj
  · rw [hj, pow_zero, map_one, mul_one (dg ω (Vec v))] at h
    obtain ⟨c, hc⟩ := mk_dg_eq_iff h3 hω h
    have k0 : v 0 = 0 + c := by
      have := hc 0
      rw [Vec_eq] at this
      exact this
    have k1 : v 1 = 0 + c := by
      have := hc 1
      rw [Vec_eq] at this
      exact this
    have k2 : v 2 = 0 + c := by
      have := hc 2
      rw [Vec_eq] at this
      exact this
    have k3 : (0 : ZMod 3) = 1 + c := by
      have := hc 3
      rw [Vec_eq] at this
      exact this
    have k4 : -(v 0 + v 1 + v 2) = -1 + c := by
      have := hc 4
      rw [Vec_eq] at this
      exact this
    exact (by decide : ∀ x y z d : ZMod 3, x = 0 + d → y = 0 + d → z = 0 + d →
      (0 : ZMod 3) = 1 + d → -(x + y + z) = -1 + d → False)
      (v 0) (v 1) (v 2) c k0 k1 k2 k3 k4
  · rw [hj] at h
    exact mk_dg_ne_mk_dg_mul_pg (ρ := τc ^ 1) (by decide) ev (Vec v) h
  · rw [hj] at h
    exact mk_dg_ne_mk_dg_mul_pg (ρ := τc ^ 2) (by decide) ev (Vec v) h

theorem witness_cases : ∀ a k : ZMod 3, (a ≠ 0 ∨ k ≠ 0) →
    (∀ j c : ZMod 3, ∃ i : Fin 5,
        j * Bv a k i ≠ Bv a k ((Equiv.swap (0 : Fin 5) 3)⁻¹ i) + c) ∨
    (∀ j c : ZMod 3, ∃ i : Fin 5,
        j * Bv a k i ≠ Bv a k ((Equiv.swap (3 : Fin 5) 4)⁻¹ i) + c) := by
  decide

theorem witness_generic (h3 : ω ^ 3 = 1) (hω : orderOf ω = 3) (σ : Equiv.Perm (Fin 5))
    {u : projSU 5 2 1} {B : Fin 5 → ZMod 3}
    (hu : ((u : projSU 5 2 1) : ProjGenLinGroup (Fin 5) U52Field) = ProjGenLinGroup.mk (dg ω B))
    (hσ : ∀ j c : ZMod 3, ∃ i : Fin 5, j * B i ≠ B (σ⁻¹ i) + c) :
    ∃ g : projSU 5 2 1, (g * u * g⁻¹) * u = u * (g * u * g⁻¹) ∧
      g * u * g⁻¹ ∉ Subgroup.zpowers u := by
  refine ⟨⟨ProjGenLinGroup.mk (pg σ), mk_pg_mem σ⟩, ?_, ?_⟩
  · apply Subtype.ext
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    change ProjGenLinGroup.mk (pg σ) * (u : ProjGenLinGroup (Fin 5) U52Field) *
        (ProjGenLinGroup.mk (pg σ))⁻¹ * (u : ProjGenLinGroup (Fin 5) U52Field) =
      (u : ProjGenLinGroup (Fin 5) U52Field) * (ProjGenLinGroup.mk (pg σ) *
        (u : ProjGenLinGroup (Fin 5) U52Field) * (ProjGenLinGroup.mk (pg σ))⁻¹)
    rw [hu, mk_pg_mul_dg_mul_inv]
    exact mk_dg_comm h3 _ _
  · intro hmem
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
    have h := congrArg (fun x : projSU 5 2 1 => (x : ProjGenLinGroup (Fin 5) U52Field)) hk
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_zpow] at h
    rw [hu, mk_pg_mul_dg_mul_inv, ← map_zpow, dg_zpow h3] at h
    obtain ⟨c, hc⟩ := mk_dg_eq_iff h3 hω h
    obtain ⟨i, hi⟩ := hσ (k : ZMod 3) (-c)
    apply hi
    have h1 := hc i
    simp only [Pi.smul_apply, zsmul_eq_mul] at h1
    linear_combination -h1

theorem hw_u52 (h3 : ω ^ 3 = 1) (hω : orderOf ω = 3) (a k : ℤ)
    (hnot : ¬ ((3 : ℤ) ∣ a ∧ (3 : ℤ) ∣ k)) :
    ∃ g : projSU 5 2 1,
      (g * (vecElt (zS h3) ![1, 1, 1] ^ a * eS h3 ^ k) * g⁻¹) *
          (vecElt (zS h3) ![1, 1, 1] ^ a * eS h3 ^ k) =
        (vecElt (zS h3) ![1, 1, 1] ^ a * eS h3 ^ k) *
          (g * (vecElt (zS h3) ![1, 1, 1] ^ a * eS h3 ^ k) * g⁻¹) ∧
      g * (vecElt (zS h3) ![1, 1, 1] ^ a * eS h3 ^ k) * g⁻¹ ∉
        Subgroup.zpowers (vecElt (zS h3) ![1, 1, 1] ^ a * eS h3 ^ k) := by
  have hlin : a • (![1, 1, 1, 0, 0] : Fin 5 → ZMod 3) + k • ev =
      Bv (a : ZMod 3) (k : ZMod 3) := by
    rw [← Int.cast_smul_eq_zsmul (ZMod 3) a, ← Int.cast_smul_eq_zsmul (ZMod 3) k]
    exact vec_lin _ _ _ rfl
  have hu : ((vecElt (zS h3) ![1, 1, 1] ^ a * eS h3 ^ k : projSU 5 2 1) :
      ProjGenLinGroup (Fin 5) U52Field) = ProjGenLinGroup.mk (dg ω (Bv (a : ZMod 3) (k : ZMod 3))) := by
    rw [Subgroup.coe_mul, Subgroup.coe_zpow, Subgroup.coe_zpow, coe_vecElt_ones h3, coe_eS,
      ← map_zpow, ← map_zpow, dg_zpow h3, dg_zpow h3, ← map_mul, ← dg_mul h3, hlin]
  have hcase : (a : ZMod 3) ≠ 0 ∨ (k : ZMod 3) ≠ 0 := by
    by_contra hcon
    simp only [not_or, not_not] at hcon
    apply hnot
    exact ⟨(ZMod.intCast_zmod_eq_zero_iff_dvd a 3).mp hcon.1,
      (ZMod.intCast_zmod_eq_zero_iff_dvd k 3).mp hcon.2⟩
  rcases witness_cases _ _ hcase with h | h
  · exact witness_generic h3 hω (Equiv.swap 0 3) hu h
  · exact witness_generic h3 hω (Equiv.swap 3 4) hu h

end Relations

theorem not_729_dvd_card_u52 : ¬ 729 ∣ Nat.card (projSU 5 2 1) := by
  intro h
  have hne : Nat.card (projSU 5 2 1) ≠ 0 := by
    intro h0
    have h2 := CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIV.factorization_card_projSU_five_two
    rw [h0, Nat.factorization_zero] at h2
    simp at h2
  have h3 : 3 ^ 6 ∣ Nat.card (projSU 5 2 1) := by
    norm_num
    exact h
  have h4 := (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_three hne).mp h3
  rw [CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIV.factorization_card_projSU_five_two] at h4
  omega

theorem exists_omega : ∃ ω : U52Fieldˣ, orderOf ω = 3 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  apply exists_prime_orderOf_dvd_card' 3
  rw [Nat.card_units, GaloisField.card 2 (2 * 1) (by norm_num)]
  norm_num

section Final

variable {ω : U52Fieldˣ}

theorem listRow_u52_of (h3 : ω ^ 3 = 1) (hω : orderOf ω = 3) : ListRow (projSU 5 2 1) :=
  listRow_of_wreath3_prod_gen (wreathFacts_u52 h3 hω)
    (card_wreathW_eq_eighty_one (wreathFacts_u52 h3 hω)) not_729_dvd_card_u52 (eS_pow_three h3)
    (fun i => zS_eS_comm h3 i) (tS_eS_comm h3) (eS_not_mem_wreathW h3 hω) (hw_u52 h3 hω)

end Final

theorem listRow_u52 : ListRow (projSU 5 2 1) := by
  obtain ⟨ω, hω⟩ := exists_omega
  exact listRow_u52_of (by rw [← hω]; exact pow_orderOf_eq_one ω) hω

end CFSG.RankThree.PartTwo.Sec4.RonanK432
