module

public import CFSG.RankThree.PartTwo.Sec4.RonanK432RowSp62
public import CFSG.RankThree.PartTwo.KFacts.KS21SylowSp64
public import CFSG.RankThree.Classical.SteinbergR3EHigherSymplecticOuterOrder

public section

namespace CFSG.RankThree.PartTwo.Sec4.RonanK432

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open CFSG.RankThree.PartTwo.Sec4.Item434Kit
open CFSG.RankThree.PartTwo.KFacts.KS21.DFT
open CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl
open CFSG.Assembly.RankThreeEven (projSp)
open CFSG.RankThree.PartTwo.KFacts.KS21.Sp64 (three_smul_V3)

abbrev F4 : Type := GaloisField 2 2

abbrev Sp6 : Type := KFacts.KS21.Sp64.Sp

theorem vecElt_map {G X : Type} [Group G] [Group X] (ψ : G →* X) (z : Fin 3 → G)
    (v : Fin 3 → ZMod 3) : vecElt (fun i => ψ (z i)) v = ψ (vecElt z v) := by
  simp [vecElt, map_mul, map_pow]

theorem wreathFacts_map {G X : Type} [Group G] [Group X] {ψ : G →* X}
    (hψ : Function.Injective ψ) {z : Fin 3 → G} {t : G} (hf : WreathFacts z t) :
    WreathFacts (fun i => ψ (z i)) (ψ t) where
  pow_z i := by rw [← map_pow, hf.pow_z i, map_one]
  comm_z i j := by rw [← map_mul, ← map_mul, hf.comm_z i j]
  inj v hv := by
    rw [vecElt_map] at hv
    exact hf.inj v (hψ (by rw [map_one]; exact hv))
  pow_t := by rw [← map_pow, hf.pow_t, map_one]
  conj0 := by rw [← map_inv, ← map_mul, ← map_mul, hf.conj0]
  conj1 := by rw [← map_inv, ← map_mul, ← map_mul, hf.conj1]
  conj2 := by rw [← map_inv, ← map_mul, ← map_mul, hf.conj2]
  t_ne v hv := by
    rw [vecElt_map] at hv
    exact hf.t_ne v (hψ hv)

theorem rot3_single_zero : rot3 (Pi.single 0 1 : Fin 3 → ZMod 3) = Pi.single 1 1 := by
  funext k
  fin_cases k <;> simp [rot3_apply_zero, rot3_apply_one, rot3_apply_two, Pi.single_apply]

theorem rot3_single_one : rot3 (Pi.single 1 1 : Fin 3 → ZMod 3) = Pi.single 2 1 := by
  funext k
  fin_cases k <;> simp [rot3_apply_zero, rot3_apply_one, rot3_apply_two, Pi.single_apply]

theorem rot3_single_two : rot3 (Pi.single 2 1 : Fin 3 → ZMod 3) = Pi.single 0 1 := by
  funext k
  fin_cases k <;> simp [rot3_apply_zero, rot3_apply_one, rot3_apply_two, Pi.single_apply]

theorem vec_sum : ∀ v : Fin 3 → ZMod 3,
    (v 0).val • (Pi.single 0 1 : Fin 3 → ZMod 3) + (v 1).val • (Pi.single 1 1 : Fin 3 → ZMod 3) +
      (v 2).val • (Pi.single 2 1 : Fin 3 → ZMod 3) = v := by
  decide

theorem vecElt_tau {H : Type} [Group H] (τ : Multiplicative (Fin 3 → ZMod 3) →* H)
    (v : Fin 3 → ZMod 3) :
    vecElt (fun i => τ (Multiplicative.ofAdd (Pi.single i 1))) v = τ (Multiplicative.ofAdd v) := by
  have e : ∀ (i : Fin 3) (n : ℕ), τ (Multiplicative.ofAdd (Pi.single i 1)) ^ n =
      τ (Multiplicative.ofAdd (n • (Pi.single i 1 : Fin 3 → ZMod 3))) := by
    intro i n
    rw [ofAdd_nsmul, map_pow]
  simp only [vecElt]
  rw [e, e, e, ← map_mul, ← map_mul]
  congr 1
  apply Multiplicative.toAdd.injective
  simpa only [toAdd_mul, toAdd_ofAdd] using vec_sum v

theorem wreathFacts_tau {H : Type} [Group H] (τ : Multiplicative (Fin 3 → ZMod 3) →* H)
    (hτ : Function.Injective τ) {w : H} (hw3 : w ^ 3 = 1)
    (hwτ : ∀ v : Fin 3 → ZMod 3, w * τ (Multiplicative.ofAdd v) =
      τ (Multiplicative.ofAdd (rot3 v)) * w)
    (hne : ∀ v : Fin 3 → ZMod 3, τ (Multiplicative.ofAdd v) ≠ w) :
    WreathFacts (fun i => τ (Multiplicative.ofAdd (Pi.single i 1))) w where
  pow_z i := by
    rw [← map_pow, ← ofAdd_nsmul, three_smul_V3, ofAdd_zero, map_one]
  comm_z i j := (Commute.all _ _).map τ
  inj v hv := by
    rw [vecElt_tau] at hv
    have h1 : τ (Multiplicative.ofAdd v) = τ 1 := by rw [map_one]; exact hv
    exact ofAdd_eq_one.mp (hτ h1)
  pow_t := hw3
  conj0 := by
    show w * τ (Multiplicative.ofAdd (Pi.single 0 1)) * w⁻¹ =
      τ (Multiplicative.ofAdd (Pi.single 1 1))
    rw [hwτ, mul_assoc, mul_inv_cancel, mul_one, rot3_single_zero]
  conj1 := by
    show w * τ (Multiplicative.ofAdd (Pi.single 1 1)) * w⁻¹ =
      τ (Multiplicative.ofAdd (Pi.single 2 1))
    rw [hwτ, mul_assoc, mul_inv_cancel, mul_one, rot3_single_one]
  conj2 := by
    show w * τ (Multiplicative.ofAdd (Pi.single 2 1)) * w⁻¹ =
      τ (Multiplicative.ofAdd (Pi.single 0 1))
    rw [hwτ, mul_assoc, mul_inv_cancel, mul_one, rot3_single_two]
  t_ne v hv := by
    rw [vecElt_tau] at hv
    exact hne v hv

theorem tau3_ne_permGL3 {K : Type} [Field K] {ω : Kˣ} (hω3 : ω ^ 3 = 1)
    (v : Fin 3 → ZMod 3) : tau3 hω3 (Multiplicative.ofAdd v) ≠ permGL3 := by
  intro h
  have h1 := congrArg (fun g : GL (Fin 3) K => (g : Matrix (Fin 3) (Fin 3) K) 1 0) h
  simp [tau3_apply, coe_permGL3, permMat3, TauCeti.diagGL_coe] at h1

theorem tau3_single_eq {K : Type} [Field K] (ω : Kˣ) (i : Fin 3) :
    (fun k : Fin 3 => ω ^ ((Pi.single i (1 : ZMod 3) : Fin 3 → ZMod 3) k).val) =
      Pi.mulSingle i ω := by
  have h1 : (1 : ZMod 3).val = 1 := rfl
  funext k
  by_cases hk : k = i
  · subst hk
    simp [h1]
  · simp [Pi.single_eq_of_ne hk, Pi.mulSingle_eq_of_ne hk]

theorem leviSp_tau3_single {K : Type} [Field K] {ω : Kˣ} (hω3 : ω ^ 3 = 1) (i : Fin 3) :
    leviSp (tau3 hω3 (Multiplicative.ofAdd (Pi.single i 1))) = lam i (sl2Diag ω) := by
  rw [lam_sl2Diag, tau3_apply, tau3_single_eq]
  rfl

theorem wreathFacts_Sp6 {ω : F4ˣ} (hω3 : ω ^ 3 = 1) (hord : orderOf ω = 3) :
    WreathFacts (fun i => lam i (sl2Diag ω)) (leviSp permGL3) := by
  have hGL := wreathFacts_tau (tau3 hω3) (tau3_injective hω3 hord) permGL3_pow_three
    (permGL3_mul_tau3 hω3) (tau3_ne_permGL3 hω3)
  have hS := wreathFacts_map (ψ := leviSp) KFacts.KS21.Sp64.leviSp_injective hGL
  have hz : (fun i => lam i (sl2Diag ω)) =
      (fun i => leviSp (tau3 hω3 (Multiplicative.ofAdd (Pi.single i 1)))) :=
    funext fun i => (leviSp_tau3_single hω3 i).symm
  rw [hz]
  exact hS

instance finite_Sp6 : Finite Sp6 :=
  Finite.of_equiv (projSp 3 F4) KFacts.KS21.Sp64.equivSp.toEquiv

theorem factorization_card_Sp6 : (Nat.card Sp6).factorization 3 = 4 := by
  rw [KFacts.KS21.Sp64.card_Sp_eq]
  exact Item434AltPerm.factorization_three_pow_mul 4 (by norm_num)

theorem not_243_dvd_Sp6 : ¬ 243 ∣ Nat.card Sp6 := by
  rw [KFacts.KS21.Sp64.card_Sp_eq]
  norm_num

theorem card_wreathW_Sp6 {ω : F4ˣ} (hω3 : ω ^ 3 = 1) (hord : orderOf ω = 3) :
    Nat.card (wreathW (fun i => lam i (sl2Diag ω)) (leviSp permGL3)) = 81 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hwz := wreathFacts_Sp6 hω3 hord
  have hle := Item434AltPerm.card_le_of_isPGroup (isPGroup_wreathW hwz)
  rw [factorization_card_Sp6] at hle
  have := le_card_wreathW hwz
  norm_num at hle
  omega

theorem flip_conj_z0 (ω : F4ˣ) :
    lam (0 : Fin 3) sl2W * lam (0 : Fin 3) (sl2Diag ω) * (lam (0 : Fin 3) sl2W)⁻¹ =
      (lam (0 : Fin 3) (sl2Diag ω))⁻¹ := by
  have key : (sl2W : Matrix.SpecialLinearGroup (Fin 2) F4) * sl2Diag ω * (sl2W)⁻¹ =
      sl2Diag ω⁻¹ := by
    rw [sl2W_mul_sl2Diag, mul_assoc, mul_inv_cancel, mul_one]
  calc lam (0 : Fin 3) sl2W * lam (0 : Fin 3) (sl2Diag ω) * (lam (0 : Fin 3) sl2W)⁻¹
      = lam (0 : Fin 3) ((sl2W : Matrix.SpecialLinearGroup (Fin 2) F4) * sl2Diag ω *
          (sl2W)⁻¹) := by
        rw [map_mul, map_mul, map_inv]
    _ = lam (0 : Fin 3) (sl2Diag ω⁻¹) := by rw [key]
    _ = (lam (0 : Fin 3) (sl2Diag ω))⁻¹ := by rw [map_inv sl2Diag, map_inv (lam (0 : Fin 3))]

theorem flip_commute (ω : F4ˣ) {i : Fin 3} (hi : (0 : Fin 3) ≠ i) :
    lam (0 : Fin 3) sl2W * lam i (sl2Diag ω) * (lam (0 : Fin 3) sl2W)⁻¹ =
      lam i (sl2Diag ω) := by
  rw [(commute_lam_lam hi (sl2W : Matrix.SpecialLinearGroup (Fin 2) F4) (sl2Diag ω)).eq,
    mul_inv_cancel_right]

theorem listRow_Sp6 : ListRow Sp6 := by
  obtain ⟨ω, hord, hω3, -⟩ := KFacts.KS21.Sp64.exists_omega_data
  have hwz := wreathFacts_Sp6 hω3 hord
  have h0 := flip_conj_z0 ω
  have h1 := flip_commute ω (i := 1) (by decide)
  have h2 := flip_commute ω (i := 2) (by decide)
  exact listRow_of_wreath3 hwz (card_wreathW_Sp6 hω3 hord) not_243_dvd_Sp6
    ⟨lam (0 : Fin 3) sl2W, flip_facts hwz h0 h1 h2⟩

theorem listRow_projSp6 : ListRow (projSp 3 F4) :=
  ListRow.of_mulEquiv KFacts.KS21.Sp64.equivSp.symm listRow_Sp6

theorem not_three_dvd_card_outer_projSp6 :
    ¬ 3 ∣ Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer
      (projSp 3 (GaloisField 2 2))) := by
  intro h3
  have hd := CFSG.RankThree.Classical.higher_symplectic_outer_order_divides_field_multiplier_bound
    (ℓ := 2) (f := 2) (r := 3) (K := GaloisField 2 2) Nat.prime_two (by norm_num) (by norm_num)
    (GaloisField.card 2 2 (by norm_num))
  rw [Nat.card_congr (CFSG.ComponentClassification.OuterAutomorphisms.equivalence
    (CFSG.PGLModel.projSpEquivStatedProj 3 (GaloisField 2 2))).toEquiv] at h3
  have := h3.trans hd.1
  norm_num at this

theorem outerRow_projSp6 : OuterRow (projSp 3 (GaloisField 2 2)) :=
  outerRow_of_not_three_dvd_outer not_three_dvd_card_outer_projSp6

theorem row_sp64 : RowOf (projSp 3 (GaloisField 2 2)) := by
  intro S _ _ _ _ ⟨e⟩
  haveI : Finite (projSp 3 (GaloisField 2 2)) := Finite.of_equiv S e.toEquiv
  exact GoodRow.of_mulEquiv (S := projSp 3 (GaloisField 2 2)) e.symm
    ⟨listRow_projSp6, outerRow_projSp6⟩

end CFSG.RankThree.PartTwo.Sec4.RonanK432
