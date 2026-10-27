module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightSum
public import CFSG.LocalAnalysis.GLTheoremA.CatA.H81Orth.Aut

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LieType.Universal.Spin
open CFSG.ClassicalGroups.Orthogonal

variable {W : Type} [CommGroup W]

private theorem s16e_eq_one_of_mem_zpowers_allOnes {n : ℕ} (hn : Odd n) {x : G6.PermMod n}
    (hx : x ∈ Subgroup.zpowers (G6.allOnes n)) (hc : x ∈ G6.coreMod n) : x = 1 := by
  obtain ⟨k, rfl⟩ := hx
  rw [G6.mem_coreMod] at hc
  have hcoord : ∀ i : Fin n, Multiplicative.toAdd (G6.allOnes n ^ k) i = (k : ZMod 2) := by
    intro i
    simp [G6.allOnes, toAdd_zpow]
  have hsum : (n : ZMod 2) * (k : ZMod 2) = 0 := by
    have h := hc
    rw [Finset.sum_congr rfl (fun i _ => hcoord i)] at h
    rwa [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h
  have hk : (k : ZMod 2) = 0 := by
    rwa [hn.natCast_zmod_two, one_mul] at hsum
  apply Multiplicative.toAdd.injective
  funext i
  rw [hcoord i, hk]
  rfl

theorem s16e_inf_fixV_eq_bot_alternatingNatural {H : Subgroup (MulAut W)} {U : Subgroup W}
    {n : ℕ} (hn : 3 ≤ n) (hodd : Odd n) (h : AlternatingNatural H U ⊥ n) :
    U ⊓ fixV H = ⊥ := by
  obtain ⟨π, hsurj, hZU, hkerle, hUinv, hZinv, hsec, hkerinv, β, hβs, hβk, hβe⟩ := h
  refine le_bot_iff.1 fun w hw => ?_
  obtain ⟨hwU, hwfix⟩ := Subgroup.mem_inf.1 hw
  obtain ⟨m, hm⟩ := QuotientGroup.mk_surjective (β ⟨w, hwU⟩)
  let x : G6.PermMod n := m.1
  let xa : (FFModel.altDn n).Amb := x
  have hxcore : x ∈ G6.coreMod n := m.2
  have hxsec : xa ∈ (FFModel.altDn n).sec := hxcore
  have hfixval : ∀ γ : (FFModel.altDn n).Gam, (FFModel.altDn n).act γ xa = xa := by
    intro γ
    have hfixw : ((π γ : ↥H) : MulAut W) w = w := (mem_fixV.1 hwfix) (π γ) (π γ).2
    have hu : ((π γ : ↥H) : MulAut W) w ∈ U := by rw [hfixw]; exact hwU
    have hm' : (FFModel.altDn n).act γ xa ∈ (FFModel.altDn n).sec := hsec γ xa hxsec
    have he := hβe γ ⟨w, hwU⟩ m hu hm' hm.symm
    have hleft : β ⟨((π γ : ↥H) : MulAut W) w, hu⟩ = β ⟨w, hwU⟩ := by
      congr 1
      exact Subtype.ext hfixw
    have hq : QuotientGroup.mk m =
        QuotientGroup.mk (⟨(FFModel.altDn n).act γ xa, hm'⟩ :
          ↥(FFModel.altDn n).sec) :=
      hm.trans (hleft.symm.trans he)
    have hq' : QuotientGroup.mk ((m : ↥(FFModel.altDn n).sec) /
        (⟨(FFModel.altDn n).act γ xa, hm'⟩ : ↥(FFModel.altDn n).sec)) =
        (1 : ↥(FFModel.altDn n).sec ⧸
          (FFModel.altDn n).ker.subgroupOf (FFModel.altDn n).sec) := by
      rw [QuotientGroup.mk_div, hq]
      exact div_self' _
    have hmem := (QuotientGroup.eq_one_iff ((m : ↥(FFModel.altDn n).sec) /
      (⟨(FFModel.altDn n).act γ xa, hm'⟩ : ↥(FFModel.altDn n).sec))).1 hq'
    rw [Subgroup.mem_subgroupOf] at hmem
    have hone := s16e_eq_one_of_mem_zpowers_allOnes hodd
      (Subgroup.mem_inf.1 hmem).1 (Subgroup.mem_inf.1 hmem).2
    have hdiv : (m : ↥(FFModel.altDn n).sec) /
        (⟨(FFModel.altDn n).act γ xa, hm'⟩ : ↥(FFModel.altDn n).sec) = 1 := Subtype.ext hone
    have heq : m = ⟨(FFModel.altDn n).act γ xa, hm'⟩ := div_eq_one.1 hdiv
    exact (congrArg Subtype.val heq).symm
  have hconst : ∀ i j : Fin n, Multiplicative.toAdd x i = Multiplicative.toAdd x j := by
    intro i j
    obtain ⟨σ, hσ⟩ := (alternatingGroup.isPretransitive_of_three_le_card (α := Fin n)
      (by simpa using hn)).exists_smul_eq j i
    let σ' : (FFModel.altDn n).Gam := σ
    have hact : (FFModel.altDn n).act σ' xa =
        G6.permAct n (σ : Equiv.Perm (Fin n)) x := rfl
    have h := congrArg (fun y : (FFModel.altDn n).Amb =>
      Multiplicative.toAdd (show G6.PermMod n from y) i) (hfixval σ')
    rw [hact, G6.permAct_apply] at h
    have hσ' : (σ : Equiv.Perm (Fin n)) j = i := by
      simpa only [MulAction.subgroup_smul_def, Equiv.Perm.smul_def] using hσ
    have hσinv : (σ : Equiv.Perm (Fin n))⁻¹ i = j := by
      rw [← hσ']
      simp
    rw [hσinv] at h
    exact h.symm
  let c : ZMod 2 := Multiplicative.toAdd x ⟨0, by omega⟩
  have hmc : ∀ i : Fin n, Multiplicative.toAdd x i = c :=
    fun i => hconst i _
  have hsum : (∑ i : Fin n, c) = 0 := by
    calc ∑ i : Fin n, c
        = ∑ i : Fin n, Multiplicative.toAdd x i :=
          Finset.sum_congr rfl fun i _ => (hmc i).symm
      _ = 0 := G6.mem_coreMod.1 hxcore
  have hc : c = 0 := by
    have hsum' : (n : ZMod 2) * c = 0 := by
      rwa [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
    rwa [hodd.natCast_zmod_two, one_mul] at hsum'
  have hm1 : m = 1 := by
    apply Subtype.ext
    apply Multiplicative.toAdd.injective
    funext i
    change Multiplicative.toAdd x i = Multiplicative.toAdd (1 : G6.PermMod n) i
    rw [hmc i, hc]
    rfl
  have hbeta : β ⟨w, hwU⟩ = 1 := by
    calc β ⟨w, hwU⟩ = QuotientGroup.mk m := hm.symm
      _ = QuotientGroup.mk (1 : ↥(FFModel.altDn n).sec) := by rw [hm1]
      _ = 1 := by simp
  exact (hβk ⟨w, hwU⟩).1 hbeta

theorem s16e_natAct_fixed_eq_one_statedOmega {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type}
    [Field K] [Finite K] {Q : QuadraticForm K (ι → K)} {Q₀ : (ι → K) → K} (hQ : ⇑Q = Q₀)
    (hK : 2 < Nat.card K) (hnd : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hdim : 3 ≤ Fintype.card ι) {m : Multiplicative (ι → K)}
    (hm : ∀ γ : ↥(StatedOmega Q₀), natAct (StatedOmega Q₀) γ m = m) : m = 1 := by
  show Multiplicative.toAdd m = 0
  let w : ι → K := Multiplicative.toAdd m
  have hw : ∀ g ∈ ⁅TauCeti.QuadraticMap.orthogonalGroup Q,
      TauCeti.QuadraticMap.orthogonalGroup Q⁆, g w = w := by
    intro g hg
    have hA : (toLinEquiv ι K).symm g ∈ StatedOmega Q₀ := by
      rw [statedOmega_eq_comap hQ]
      exact Subgroup.mem_comap.2 (by simpa using hg)
    have h := hm ⟨(toLinEquiv ι K).symm g, hA⟩
    have h2 : (toLinEquiv ι K ((toLinEquiv ι K).symm g)) w = w := by
      rw [toLinEquiv_apply]
      simpa [natAct, w] using congrArg Multiplicative.toAdd h
    rwa [MulEquiv.apply_symm_apply] at h2
  exact CFSG.LocalAnalysis.GLTheoremA.H81Orth.eq_zero_of_forall_mem_omega_apply_eq hK Q hnd
    (by rwa [Module.finrank_fintype_fun_eq_card]) hw

theorem s16e_inf_fixV_eq_bot_natOmegaMinus {H : Subgroup (MulAut W)} {U : Subgroup W}
    (h : NatOmegaMinus H U ⊥ 4 3) : U ⊓ fixV H = ⊥ := by
  obtain ⟨-, K, hKf, hKfin, b, c, hK, hirr, hreal⟩ := h
  letI := hKf
  haveI := hKfin
  have hreal' : (FFModel.nat (StatedOmega (StatedQuadMinus 2 K b c))).Realizes H U ⊥ := hreal
  refine s16e_inf_fixV_eq_bot_of_nat hreal' fun m hm => ?_
  refine s16e_natAct_fixed_eq_one_statedOmega (Q := quadMinus 2 K b c)
    (coe_quadMinus 2 K b c) ?_ (nondegenerate_polarBilin_quadMinus_of_finite 2 K hirr) ?_ hm
  · rw [hK]
    norm_num
  · simp

theorem s16e_inf_fixV_eq_bot_natOmegaPlus {H : Subgroup (MulAut W)} {U : Subgroup W}
    (h : NatOmegaPlus H U ⊥ 4 2) : U ⊓ fixV H = ⊥ := by
  obtain ⟨-, K, hKf, hKfin, hK, hreal⟩ := h
  letI := hKf
  haveI := hKfin
  have hreal' : (FFModel.nat (StatedOmega (StatedQuadPlus 2 K))).Realizes H U ⊥ := hreal
  refine s16e_inf_fixV_eq_bot_of_nat hreal' fun m hm => ?_
  refine s16e_natAct_fixed_eq_one_statedOmega (Q := quadPlus 2 K)
    (coe_quadPlus 2 K) ?_ (nondegenerate_polarBilin_quadPlus 2 K) ?_ hm
  · rw [hK]
    norm_num
  · simp

private theorem s16e_fix_stable_of_alt {H : Subgroup (MulAut W)} {U Z : Subgroup W} {n : ℕ}
    (h : AlternatingNatural H U Z n) : ∀ x : ↥H, ∀ u ∈ U, (x : MulAut W) u ∈ U := by
  obtain ⟨π, -, -, -, hU, -⟩ := h
  exact hU

theorem s16e_inf_fixV_eq_bot_sumOfNat_alt {H : Subgroup (MulAut W)} {U : Subgroup W} {n k : ℕ}
    (hn : 3 ≤ n) (hodd : Odd n)
    (h : SumOfNat (fun H U Z => AlternatingNatural H U Z n) H U ⊥ k) : U ⊓ fixV H = ⊥ :=
  s16e_inf_fixV_eq_bot_of_sumOfNat (fun _ hI => s16e_fix_stable_of_alt hI)
    (fun _ hI => s16e_inf_fixV_eq_bot_alternatingNatural hn hodd hI) h

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
