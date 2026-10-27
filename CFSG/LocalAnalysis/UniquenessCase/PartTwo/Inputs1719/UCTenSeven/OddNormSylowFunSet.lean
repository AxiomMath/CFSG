module

public import CFSG.LocalAnalysis.UniquenessCase.UCFront14
public import CFSG.LocalAnalysis.UniquenessCase.FundamentalLie
import CFSG.LocalAnalysis.UniquenessCase.UC22FunSplitNormalizerGeometry
import CFSG.LocalAnalysis.UniquenessCase.UC22FunSplitInnerModels
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.UCTenSeven.OddNormSylowPSp
import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1Spin410RS

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.UCTenSeven

open Subgroup CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped Pointwise MatrixGroups

theorem mem_centralizer_of_commute_funSet {X : Type} [Group X] [Finite X]
    {𝔉 : ∀ {Y : Type} [Group Y], Subgroup Y → Subgroup Y → Prop}
    (hconj : ∀ (g : X) {K : Subgroup X}, 𝔉 ⊤ K → 𝔉 ⊤ (K.map (MulAut.conj g).toMonoidHom))
    (P : Sylow 2 X) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hcomm : ∀ z₁ z₂ : X, (∃ j : ℕ, z₁ ^ p ^ j = 1) → (∃ j : ℕ, z₂ ^ p ^ j = 1) →
      (∀ K ∈ F14.FunSet 𝔉 X (P : Subgroup X), z₁ ∈ centralizer (K : Set X)) →
      (∀ K ∈ F14.FunSet 𝔉 X (P : Subgroup X), z₂ ∈ centralizer (K : Set X)) →
      z₁ * z₂ = z₂ * z₁)
    {y : X} (hyN : y ∈ normalizer ((P : Subgroup X) : Set X)) {j : ℕ} (hyj : y ^ p ^ j = 1)
    (hyK : ∀ K ∈ F14.FunSet 𝔉 X (P : Subgroup X), y ∈ centralizer (K : Set X)) :
    y ∈ centralizer ((P : Subgroup X) : Set X) := by
  have h2 : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [Subgroup.mem_centralizer_iff]
  intro s hs
  let z : X := s * y⁻¹ * s⁻¹
  have hzpow : z ^ p ^ j = 1 := by
    have h1 : z = (MulAut.conj s) y⁻¹ := by simp [z]
    calc z ^ p ^ j = ((MulAut.conj s) y⁻¹) ^ p ^ j := by rw [h1]
      _ = (MulAut.conj s) (y⁻¹ ^ p ^ j) :=
            (map_pow (MulAut.conj s) y⁻¹ (p ^ j)).symm
      _ = (MulAut.conj s) 1 := by
            rw [show y⁻¹ ^ p ^ j = 1 by rw [inv_pow, hyj, inv_one]]
      _ = 1 := map_one _
  have hzK : ∀ K ∈ F14.FunSet 𝔉 X (P : Subgroup X), z ∈ centralizer (K : Set X) := by
    intro K hK
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have hK' : K.map (MulAut.conj s⁻¹).toMonoidHom ∈ F14.FunSet 𝔉 X (P : Subgroup X) :=
      F14.mem_funSet_map_conj_of_mem_normalizer hconj
        (Subgroup.le_normalizer (Subgroup.inv_mem _ hs)) hK
    have hx' : s⁻¹ * x * s ∈ (K.map (MulAut.conj s⁻¹).toMonoidHom : Subgroup X) := by
      rw [Subgroup.mem_map]
      exact ⟨x, hx, by simp⟩
    have h1 : Commute (s⁻¹ * x * s) y :=
      (Subgroup.mem_centralizer_iff.mp (hyK _ hK')) _ hx'
    have h2' : (s⁻¹ * x * s) * y⁻¹ = y⁻¹ * (s⁻¹ * x * s) := h1.inv_right.eq
    calc x * z = s * ((s⁻¹ * x * s) * y⁻¹) * s⁻¹ := by simp [z]; group
      _ = s * (y⁻¹ * (s⁻¹ * x * s)) * s⁻¹ := by rw [h2']
      _ = z * x := by simp [z]; group
  have hcomm_yz : y * z = z * y := hcomm y z ⟨j, hyj⟩ ⟨j, hzpow⟩ hyK hzK
  have hyzP : y * z ∈ (P : Subgroup X) := by
    have hys : y * s * y⁻¹ ∈ (P : Subgroup X) :=
      (Subgroup.mem_normalizer_iff.mp hyN s).mp hs
    have hz : y * z = (y * s * y⁻¹) * s⁻¹ := by simp [z]; group
    rw [hz]
    exact Subgroup.mul_mem _ hys (Subgroup.inv_mem _ hs)
  have hyzpow : (y * z) ^ p ^ j = 1 := by
    have hc : Commute y z := hcomm_yz
    rw [hc.mul_pow, hyj, hzpow, mul_one]
  obtain ⟨k, hk⟩ := P.isPGroup' ⟨y * z, hyzP⟩
  have hk' : (y * z) ^ 2 ^ k = 1 := by
    simpa using congrArg Subtype.val hk
  have hdvd2 : orderOf (y * z) ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk'
  have hdvd1 : orderOf (y * z) ∣ p ^ j := orderOf_dvd_of_pow_eq_one hyzpow
  have hcop : Nat.Coprime (2 ^ k) (p ^ j) :=
    (Odd.coprime_two_left (hp.odd_of_ne_two hp2)).pow k j
  have hyz1 : y * z = 1 :=
    orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop hdvd2 hdvd1)
  have hyseq : y * s * y⁻¹ = s := by
    have hz' : y * z = (y * s * y⁻¹) * s⁻¹ := by simp [z]; group
    rw [hz'] at hyz1
    calc y * s * y⁻¹ = ((y * s * y⁻¹) * s⁻¹) * s := by group
      _ = 1 * s := by rw [hyz1]
      _ = s := one_mul s
  have hys : y * s = s * y := by
    calc y * s = (y * s * y⁻¹) * y := by group
      _ = s * y := by rw [hyseq]
  exact hys.symm


theorem mem_normalizer_funSet_of_mem_normalizer {X : Type} [Group X] [Finite X]
    [IsSimpleGroup X] {t : StatedLieTag} {n r f : ℕ} (hr : r.Prime) (hr2 : r ≠ 2)
    (hadm : StatedLieAdmissible t n r f) (hX : CFSG.Blueprint.LieModel X t n r f)
    (hA1 : ¬ (t = .PSL ∧ n = 2)) (hRee : t ≠ .twistedG2) (P : Sylow 2 X) {y : X}
    (hyN : y ∈ normalizer ((P : Subgroup X) : Set X)) (hyo : Odd (orderOf y))
    (hy3 : ¬ 3 ∣ orderOf y) :
    ∀ K ∈ F14.FunSet (fundPred (r ^ f)) X (P : Subgroup X), y ∈ normalizer (K : Set X) := by
  have : Fact r.Prime := ⟨hr⟩
  intro K hK
  let B : Subgroup X := Subgroup.zpowers y
  have hBN : B ≤ normalizer ((P : Subgroup X) : Set X) := Subgroup.zpowers_le.mpr hyN
  have hBo : Odd (Nat.card B) := by rw [Nat.card_zpowers]; exact hyo
  have hB3 : ¬ 3 ∣ Nat.card B := by rwa [Nat.card_zpowers]
  have hconj : ∀ (g : X) {J : Subgroup X}, fundPred (r ^ f) ⊤ J →
      fundPred (r ^ f) ⊤ (J.map (MulAut.conj g).toMonoidHom) :=
    fun g _ hJ =>
      CFSG.LocalAnalysis.UniquenessCase.isFundamentalOver_map_mulEquiv (MulAut.conj g) hJ
  have hBpres : ∀ b ∈ B, Set.MapsTo (Subgroup.map (MulAut.conj b).toMonoidHom)
      (F14.FunSet (fundPred (r ^ f)) X (P : Subgroup X))
      (F14.FunSet (fundPred (r ^ f)) X (P : Subgroup X)) := by
    intro b hb J hJ
    exact F14.mem_funSet_map_conj_of_mem_normalizer hconj (hBN hb) hJ
  have hperm : (B : Set X) * (P : Set X) = (P : Set X) * (B : Set X) :=
    Subgroup.set_mul_normalizer_comm (B : Set X) (P : Subgroup X) hBN
  by_cases htwo : FunTwoType t n
  · obtain ⟨N, hNnormal, hN2, ⟨eN⟩⟩ :=
      F14.funSet_action_twoKernel_quotient_of_funTwoType X t n r f hr hr2 hadm hX htwo P
    let := hNnormal
    exact (F14.le_normalizer_funSet_of_preserves_of_quotient_perm hconj P B hBpres
      hBo hB3 hperm (Fin 1) N hN2 eN K hK) (Subgroup.mem_zpowers y)
  by_cases hsmall : (F14.FunSet (fundPred (r ^ f)) X (P : Subgroup X)).ncard ≤ 4
  · let Δ := F14.FunSet (fundPred (r ^ f)) X (P : Subgroup X)
    let T := CFSG.ComponentClassification.AS81.Sec2.conjSetStab Δ
    have hBT : B ≤ T := F14.le_conjSetStab_of_mapsTo_conj hBpres
    have hbot := funSet_action_eq_bot_of_ncard_le_four Δ B hBT hBo hB3 hsmall
    have hyT : (⟨y, hBT (Subgroup.mem_zpowers y)⟩ : T) ∈ B.subgroupOf T :=
      Subgroup.mem_zpowers y
    have himage := Subgroup.mem_map_of_mem
      (CFSG.ComponentClassification.AS81.Sec2.conjPermHom (le_refl T)) hyT
    rw [hbot, Subgroup.mem_bot] at himage
    exact (CFSG.ComponentClassification.AS81.Sec2.conjPermHom_eq_one_iff (le_refl T) _).mp
      himage K hK
  rcases funSet_action_twoKernel_quotient_of_four_lt hr hr2 hadm hX hA1 hRee P hK htwo
      (Nat.lt_of_not_ge hsmall) with
    ⟨m, N, hNnormal, hN2, ⟨eN⟩⟩ | ⟨N, hNnormal, hN2, hNsimple, hNcard⟩
  · let := hNnormal
    exact (F14.le_normalizer_funSet_of_preserves_of_quotient_perm hconj P B hBpres
      hBo hB3 hperm (Fin m) N hN2 eN K hK) (Subgroup.mem_zpowers y)
  · let := hNnormal
    let := hNsimple
    exact (F14.le_normalizer_funSet_of_preserves_of_quotient_card_168 hNcard hconj P B hBpres
      hBo hB3 hperm N hN2 (MulEquiv.refl _) K hK) (Subgroup.mem_zpowers y)

private lemma mem_centralizer_of_isSylowOf_sl2_commute {X F : Type} [Group X] [Field F] [Finite F]
    (hF : Odd (Nat.card F)) {K Q : Subgroup X} (e : ↥K ≃* SL(2, F))
    (hQ : CFSG.ABGLocalTools.IsSylowOf 2 Q K) {w : X} (hw : w ∈ K)
    (hwQ : w ∈ centralizer (Q : Set X)) :
    w ∈ centralizer (K : Set X) := by
  have h2 : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite ↥K := Finite.of_equiv (SL(2, F)) e.symm.toEquiv
  obtain ⟨Q₀, hQ₀⟩ := hQ
  let Q' : Sylow 2 (SL(2, F)) := Q₀.mapSurjective (f := e.toMonoidHom) e.surjective
  have hQ'coe : (Q' : Subgroup (SL(2, F))) = (Q₀ : Subgroup ↥K).map e.toMonoidHom :=
    Sylow.coe_mapSurjective e.surjective Q₀
  have hmem : ∀ A ∈ (Q' : Subgroup (SL(2, F))),
      ((e ⟨w, hw⟩ : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) *
        (A : Matrix (Fin 2) (Fin 2) F) =
      (A : Matrix (Fin 2) (Fin 2) F) *
        ((e ⟨w, hw⟩ : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) := by
    intro A hA
    rw [hQ'coe] at hA
    obtain ⟨q, hq, rfl⟩ := hA
    have hqQ : (q : X) ∈ Q := by
      rw [← hQ₀]
      exact Subgroup.mem_map_of_mem K.subtype hq
    have hwq : (q : X) * w = w * (q : X) :=
      (Subgroup.mem_centralizer_iff.mp hwQ) (q : X) hqQ
    have hcomm : Commute (e ⟨w, hw⟩) (e.toMonoidHom q) := by
      show (e.toMonoidHom ⟨w, hw⟩) * (e.toMonoidHom q) =
        (e.toMonoidHom q) * (e.toMonoidHom ⟨w, hw⟩)
      rw [← map_mul, ← map_mul]
      exact congrArg e (Subtype.ext hwq.symm)
    rw [← Matrix.SpecialLinearGroup.coe_mul, ← Matrix.SpecialLinearGroup.coe_mul, hcomm.eq]
  obtain ⟨c, hc⟩ :=
    CFSG.ComponentClassification.HarrisLit.T1.eq_smul_one_of_commute_sylow_sl2 hF Q' hmem
  have hcentral : ∀ A : SL(2, F), (e ⟨w, hw⟩) * A = A * (e ⟨w, hw⟩) := by
    intro A
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, hc,
      Matrix.smul_mul, Matrix.one_mul, Matrix.mul_smul, Matrix.mul_one]
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  let wx : ↥K := ⟨w * x * w⁻¹, K.mul_mem (K.mul_mem hw hx) (K.inv_mem hw)⟩
  have hxfix : e wx = e ⟨x, hx⟩ := by
    have heq : wx = ⟨w, hw⟩ * ⟨x, hx⟩ * ⟨w, hw⟩⁻¹ := by
      apply Subtype.ext
      simp [wx, mul_assoc]
    rw [heq, map_mul, map_mul, map_inv, hcentral]
    group
  have hwx : w * x * w⁻¹ = x := by
    have heq : wx = ⟨x, hx⟩ := e.injective hxfix
    have h2' := congrArg Subtype.val heq
    simpa [wx] using h2'
  calc x * w = (w * x * w⁻¹) * w := by conv_lhs => rw [← hwx]
    _ = w * x := by group

theorem mem_centralizer_funSet_of_mem_normalizer {X : Type} [Group X] [Finite X]
    [IsSimpleGroup X] {t : StatedLieTag} {n r f : ℕ} (hr : r.Prime) (hr2 : r ≠ 2)
    (hadm : StatedLieAdmissible t n r f) (hX : CFSG.Blueprint.LieModel X t n r f)
    (hA1 : ¬ (t = .PSL ∧ n = 2)) (hRee : t ≠ .twistedG2) (P : Sylow 2 X) {y : X}
    (hyN : y ∈ normalizer ((P : Subgroup X) : Set X)) {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    {j : ℕ} (hyj : y ^ p ^ j = 1) (hyp : y ^ p ∈ centralizer ((P : Subgroup X) : Set X)) :
    ∀ K ∈ F14.FunSet (fundPred (r ^ f)) X (P : Subgroup X), y ∈ centralizer (K : Set X) := by
  have hp2 : p ≠ 2 := by omega
  have hpo : Odd p := hp.odd_of_ne_two hp2
  have hdvd : orderOf y ∣ p ^ j := orderOf_dvd_of_pow_eq_one hyj
  have hyo : Odd (orderOf y) := Odd.of_dvd_nat hpo.pow hdvd
  have hy3 : ¬ 3 ∣ orderOf y := by
    intro h3
    have hEq : 3 = p := Nat.prime_eq_prime_of_dvd_pow Nat.prime_three hp (h3.trans hdvd)
    omega
  intro K hK
  have hyKn : y ∈ normalizer (K : Set X) :=
    mem_normalizer_funSet_of_mem_normalizer hr hr2 hadm hX hA1 hRee P hyN hyo hy3 K hK
  have : Fact r.Prime := ⟨hr⟩
  obtain ⟨f', hf', ⟨e⟩⟩ :=
    isFundamentalOver_mulEquiv_sl2 (r := r) (f := f) (q := r ^ f) hr2 rfl
      (fundamental_ambient_of_lieModel hr hr2 hadm hX hA1 hK.1).2.2.1 hK.1
  have hf1 : 1 ≤ f := hadm.2.1
  have hf'1 : 1 ≤ f' := by rcases hf' with h | h <;> omega
  have hFodd : Odd (Nat.card (GaloisField r f')) :=
    CFSG.ClassicalInvolution.Disconnected.AschTight.S19M.odd_natCard_galoisField hr2 hf'1
  let Q : Subgroup X := (P : Subgroup X) ⊓ K
  have hyQ : y ∈ normalizer (Q : Set X) :=
    Subgroup.inf_normalizer_le_normalizer_inf (Subgroup.mem_inf.mpr ⟨hyN, hyKn⟩)
  have hypQ : y ^ p ∈ centralizer (Q : Set X) :=
    Subgroup.centralizer_le (inf_le_left : (P : Subgroup X) ⊓ K ≤ (P : Subgroup X)) hyp
  have hyQcent : y ∈ centralizer (Q : Set X) :=
    mem_centralizer_of_isSylowOf_sl2 hFodd (K := K) (Q := Q) e hK.2 hyQ hp hp5 hypQ
  have hinner := odd_normalizer_inner_of_isFundamentalOver_general hK.1 hyKn hyo
  obtain ⟨w, hwK, hconjW⟩ :=
    (CFSG.GroupTheory.normalizerMonoidHom_mem_range_conj_iff hyKn).mp hinner
  have hwQ : w ∈ centralizer (Q : Set X) := by
    rw [Subgroup.mem_centralizer_iff]
    intro q hq
    have hqK : q ∈ K := hK.2.le hq
    have hyq : y * q * y⁻¹ = q := by
      have hcomm := (Subgroup.mem_centralizer_iff.mp hyQcent) q hq
      rw [← hcomm]; group
    have hwq : w * q * w⁻¹ = q := (hconjW q hqK) ▸ hyq
    calc q * w = (w * q * w⁻¹) * w := by conv_lhs => rw [← hwq]
      _ = w * q := by group
  have hwC : w ∈ centralizer (K : Set X) :=
    mem_centralizer_of_isSylowOf_sl2_commute hFodd e hK.2 hwK hwQ
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  have hwx : w * x * w⁻¹ = x := by
    have hcomm := (Subgroup.mem_centralizer_iff.mp hwC) x hx
    rw [← hcomm]; group
  have hyx : y * x * y⁻¹ = x := by
    rw [hconjW x hx, hwx]
  calc x * y = (y * x * y⁻¹) * y := by conv_lhs => rw [← hyx]
    _ = y * x := by group

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.UCTenSeven

end
