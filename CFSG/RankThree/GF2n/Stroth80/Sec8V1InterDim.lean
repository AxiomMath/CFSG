module

public import CFSG.RankThree.GF2n.Stroth80.Sec84InputStmt
public import CFSG.RankThree.GF2n.Stroth80.Sec8StepsLin
public import CFSG.RankThree.GF2n.Stroth80.Sec8StepsClose81
public import CFSG.RankThree.GF2n.Stroth80.Sec8StepsModel
public import CFSG.RankThree.GF2n.Stroth80.Sec83NatSection
public import CFSG.RankThree.GF2n.Stroth80.Sec8EndMain

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement


theorem sec8V1InterDim_of (h51 : Stroth51Statement) (hA : Sec8AExistsStatement)
    (hzt : Sec8ZtStatement) (h310chi : Stroth310ChiStatement) (h53a : Stroth53aStatement) :
    Sec8V1InterDimStatement := by
  intro G _ _ M Q Z B hc n t hs r hr m hmsp Z0 hZ0 s hs0 hsQ g hg hW
  classical
  have h5 := hs.toSec5
  have hsL : s ∈ LB M Q B := sec8_Z0_le_LB h51 hA hc hs hZ0 hs0
  have hsM : s ∈ M := hc.LB_le_M hsL
  have hZQ : Z ≤ Q := hc.Z_le_Q
  have hV : Vt M (LB M Q B) B Z t = Ut Q Z s :=
    (sec8_ZV_of_parts h51 hA hzt h310chi hc hs hZ0 hs0 hsQ).symm
  have hQn : ∀ a ∈ M, ∀ y ∈ Q, a * y * a⁻¹ ∈ Q := fun a ha y hy =>
    (Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 ha) y).mp hy
  have hzpos : 0 < Nat.card Z := Nat.card_pos
  have hq2 : 2 ≤ Nat.card Z := by have := hc.hyp.q4; omega
  have hxM : g * s * g⁻¹ ∈ M := M.mul_mem (M.mul_mem hg hsM) (M.inv_mem hg)
  have hxH : g * s * g⁻¹ ∈ H0 M Z := sec8_conj_mem_H0 hc hg (hc.LB_le_H0 hsL)
  have hx2 : (g * s * g⁻¹) ^ 2 ∈ Q := by
    have h1 := hQn g hg _ (hc.sq_mem_Q_of_mem_LB hsL)
    have e : (g * s * g⁻¹) ^ 2 = g * s ^ 2 * g⁻¹ := by rw [pow_two, pow_two]; group
    rwa [e]
  have hxcz : ∀ z ∈ Z, (g * s * g⁻¹) * z * (g * s * g⁻¹)⁻¹ = z := fun z hz => by
    rw [← Subgroup.mem_centralizer_iff.mp hxH.2 z hz, mul_inv_cancel_right]
  have hVQ : Vt M (LB M Q B) B Z t ≤ Q := hc.Vt_le_Q t
  have hZV : Z ≤ Vt M (LB M Q B) B Z t := sec39_Z_le_Vt
  have hVg : conjSubgroup g (Vt M (LB M Q B) B Z t) = Ut Q Z (g * s * g⁻¹) := by
    rw [Ut_conj_of_normalizes (hc.conj_Q_eq hg) (hc.conj_Z_eq hg) s, hV]
  have hVgQ : conjSubgroup g (Vt M (LB M Q B) B Z t) ≤ Q := by
    have h1 : conjSubgroup g (Vt M (LB M Q B) B Z t) ≤ conjSubgroup g Q :=
      Subgroup.map_mono hVQ
    rwa [hc.conj_Q_eq hg] at h1
  have hZVg : Z ≤ conjSubgroup g (Vt M (LB M Q B) B Z t) := by
    have h1 : conjSubgroup g Z ≤ conjSubgroup g (Vt M (LB M Q B) B Z t) :=
      Subgroup.map_mono hZV
    rwa [hc.conj_Z_eq hg] at h1
  obtain ⟨K, iF, iFin, -, γ, M₀, hD⟩ := stroth_globalModelData hc.hyp
  haveI hEfin : Module.Finite K M₀.E := M₀.fin
  haveI hEfinite : Finite M₀.E := Module.finite_of_finite K
  have hq : Nat.card K = Nat.card Z := hD.card
  obtain ⟨A, A₀, hAmem, hA₀mem, hA₀A, hdim⟩ := sec8_exists_codim_one h310chi h53a hc hs hr hD
  have hA : (A : Set M₀.E) = ↑(M₀.img (Sec8V1 M Q Z B t r)) := Set.ext hAmem
  obtain ⟨T, hTπ, -, hTB⟩ := hD.linear_of_centralizes hxM hxcz
  have hnd : M₀.B.Nondegenerate := by
    refine ⟨fun x hx => M₀.nondeg x hx, fun y hy => M₀.nondeg y fun f => ?_⟩
    rw [Tim79.QuadModel.B_comm, hy f, neg_zero]
  have hrefl : M₀.B.IsRefl := fun x y h => by rw [Tim79.QuadModel.B_comm, h, neg_zero]
  set ψ : M₀.E →ₗ[K] M₀.E := (T : M₀.E →ₗ[K] M₀.E) - 1 with hψdef
  have hψ : ∀ e, ψ e = T e - e := fun e => by simp [hψdef]
  have hker : LinearMap.ker ψ = M₀.B.orthogonal (LinearMap.range ψ) :=
    ker_sub_one_eq_orthogonal_range M₀.B hnd hrefl (T : M₀.E →ₗ[K] M₀.E) (fun u v => hTB u v)
      T.surjective
  have hψA : ∀ w ∈ M₀.B.orthogonal A, ψ w ∈ A := by
    intro e he
    obtain ⟨w, hwW, hwQ, rfl⟩ := (Tim79.QuadModel.mem_img M₀).mp
      ((sec8_img_W1_eq_orthogonal hc hD A hA e).mpr he)
    have hxw : ⁅g * s * g⁻¹, w⁆ ∈ Sec8V1 M Q Z B t r := hW w hwW
    have hxwQ : ⁅g * s * g⁻¹, w⁆ ∈ Q := sec8_V1_le_Q hc t r hxw
    have hπ := sec8_pi_comm M₀ hwQ (hQn _ hxM w hwQ) (hTπ w hwQ)
    rw [hψ, ← hπ]
    exact (hAmem _).mpr (M₀.pi_mem_img hxw hxwQ)
  have hcore := lemmaD_core M₀.B hnd hrefl ψ A hker hψA
  have hRange : ∀ e, e ∈ LinearMap.range ψ ↔
      e ∈ M₀.img (conjSubgroup g (Vt M (LB M Q B) B Z t)) := by
    intro e
    rw [hVg, sec8_img_Ut_iff hc hD hxM hx2 hTπ e, LinearMap.mem_range]
    constructor
    · rintro ⟨f, hf⟩
      exact ⟨f, by rw [← hf, hψ]⟩
    · rintro ⟨f, hf⟩
      exact ⟨f, by rw [hψ, hf]⟩
  have hcVg : Nat.card ↥(conjSubgroup g (Vt M (LB M Q B) B Z t)) =
      Nat.card Z * Nat.card ↥(M₀.img (conjSubgroup g (Vt M (LB M Q B) B Z t))) :=
    M₀.card_eq hVgQ hZVg
  have hVcard : Nat.card ↥(Vt M (LB M Q B) B Z t) = Nat.card Z ^ (2 * m + 1) := hmsp.card_V
  have hcVg' : Nat.card ↥(conjSubgroup g (Vt M (LB M Q B) B Z t)) = Nat.card Z ^ (2 * m + 1) := by
    rw [card_conjSubgroup, hVcard]
  have hrankR : Module.finrank K ↥(LinearMap.range ψ) = 2 * m := by
    have h1 : Nat.card ↥(LinearMap.range ψ) =
        Nat.card ↥(M₀.img (conjSubgroup g (Vt M (LB M Q B) B Z t))) :=
      Nat.card_congr (Equiv.subtypeEquivRight hRange)
    have h2 : Nat.card ↥(M₀.img (conjSubgroup g (Vt M (LB M Q B) B Z t))) =
        Nat.card Z ^ (2 * m) := by
      refine Nat.eq_of_mul_eq_mul_left hzpos ?_
      rw [← hcVg, hcVg', pow_succ']
    rw [Module.natCard_eq_pow_finrank (K := K) (V := ↥(LinearMap.range ψ)), hq] at h1
    exact Nat.pow_right_injective hq2 (h1.trans h2)
  have hSQ : Sec8V1 M Q Z B t r ⊓ conjSubgroup g (Vt M (LB M Q B) B Z t) ≤ Q :=
    inf_le_left.trans (sec8_V1_le_Q hc t r)
  have hZS : Z ≤ Sec8V1 M Q Z B t r ⊓ conjSubgroup g (Vt M (LB M Q B) B Z t) :=
    le_inf (sec8_Z_le_V1 hc t r) hZVg
  have hcS : Nat.card ↥(Sec8V1 M Q Z B t r ⊓ conjSubgroup g (Vt M (LB M Q B) B Z t)) =
      Nat.card Z * Nat.card ↥(M₀.img (Sec8V1 M Q Z B t r ⊓
        conjSubgroup g (Vt M (LB M Q B) B Z t))) :=
    M₀.card_eq hSQ hZS
  have himgS : ∀ e, e ∈ M₀.img (Sec8V1 M Q Z B t r ⊓
      conjSubgroup g (Vt M (LB M Q B) B Z t)) ↔ e ∈ LinearMap.range ψ ⊓ A := by
    intro e
    rw [Submodule.mem_inf, hRange e, hAmem e]
    constructor
    · rintro ⟨u, huS, huQ, rfl⟩
      exact ⟨M₀.pi_mem_img huS.2 huQ, M₀.pi_mem_img huS.1 huQ⟩
    · rintro ⟨h1, h2⟩
      obtain ⟨u, huQ, rfl⟩ := M₀.π_surj e
      exact M₀.pi_mem_img ⟨(M₀.mem_img_iff (sec8_Z_le_V1 hc t r) huQ).mp h2,
        (M₀.mem_img_iff hZVg huQ).mp h1⟩ huQ
  have hcardS : Nat.card ↥(M₀.img (Sec8V1 M Q Z B t r ⊓
      conjSubgroup g (Vt M (LB M Q B) B Z t))) =
      Nat.card Z ^ Module.finrank K ↥(LinearMap.range ψ ⊓ A) := by
    rw [← hq, ← Module.natCard_eq_pow_finrank (K := K) (V := ↥(LinearMap.range ψ ⊓ A))]
    exact Nat.card_congr (Equiv.subtypeEquivRight himgS)
  have hfm : m ≤ Module.finrank K ↥(LinearMap.range ψ ⊓ A) := by
    rw [hrankR] at hcore
    omega
  rw [hcS, hcardS, ← pow_succ']
  exact Nat.pow_le_pow_right hzpos (by omega)

end CFSG.RankThree.GF2n.Stroth80
