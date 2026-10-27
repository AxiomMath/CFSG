module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.FourTenDefs
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.FourTenBasic
import CFSG.LocalAnalysis.WeakClosure81.GenEiConj
import CFSG.LocalAnalysis.WeakClosure81.PSLTwoNormalTorus
import CFSG.LocalAnalysis.WeakClosure81.PSLTwoOuterInvolutions
import CFSG.LocalAnalysis.WeakClosure81.SecU1PrintMember
import CFSG.LocalAnalysis.WeakClosure81.InCalEOneMembers
import CFSG.GroupTheory.CyclicNormalizerInvolution
import CFSG.GroupTheory.SylowCover
public import CFSG.Quasithin.Vol2.Ch11SecU1Defs
import CFSG.Quasithin.Background.RonanE114L2Main
import CFSG.GH74.GLS.IVK.L2.ExistNotation
import CFSG.LocalAnalysis.WeakClosure81.Asc80BOddL2Gen
import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch5ASIn
import CFSG.LocalAnalysis.GH72.PGammaL2Field
import CFSG.Quasithin.Background.E6Hyp
public import CFSG.GroupTheory.ABGLocalTools.PStabilityCoreGW

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.Quasithin.F6 CFSG.GH74.GLS CFSG.GH74.GLS.IVK CFSG.GorensteinWalter
open CFSG.LocalAnalysis.WeakClosure81

namespace FourTenSetting

variable {Q : Type} [Group Q] [Finite Q] {L : Subgroup Q} {p e : ℕ}

theorem secU1Setting
    (h : FourTenSetting Q L p e)
    (hL : 3 ≤ e ∨ (e = 2 ∧ 5 ≤ p)) :
    CFSG.Quasithin.Vol2.Ch11.SecU1.Setting L := by
  have hgf : CFSG.generalizedFitting Q = L := by
    rw [← fstar_top_eq_generalizedFitting Q, h.fstar_eq]
  have hF : IsPSL 2 p e ↥(CFSG.generalizedFitting Q) := by
    refine CFSG.Open.StatedAPI.statedClassicalModel_of_mulEquiv ?_ h.isL2
    exact (MulEquiv.subgroupCongr hgf).symm
  have hs : IsSimpleGroup ↥(CFSG.generalizedFitting Q) := by
    rw [hgf]
    exact h.isSimpleGroup
  obtain ⟨T, hT, hLT⟩ := h.sup_eq_top
  have hLgen : CFSG.generalizedFitting Q ⊔ T = ⊤ := by
    rw [hgf]
    exact hLT
  have hset : CFSG.Quasithin.Vol2.Ch11.SecU1.Setting (CFSG.generalizedFitting Q) := by
    rcases hL with h3 | ⟨he, hp5⟩
    · exact CFSG.Quasithin.RonanE114.L2.setting_of_psl2_pow h.prime h.ne_two h3 hs hF
        hT.isPGroup hLgen
    · have hF2 := hF
      rw [he] at hF2
      exact CFSG.Quasithin.Vol2.Ch11.SecU1.setting_of_psl2_sq h.prime hp5 hs hF2
        hT.isPGroup hLgen
  rwa [hgf] at hset

end FourTenSetting

private theorem card_dvd_two_of_le_two_centralizers {Q : Type} [Group Q]
    {L P : Subgroup Q} {a z : Q} {q ε : ℤ} (hε1 : ε = 1 ∨ ε = -1)
    (hLa : (Nat.card ↥(L ⊓ Subgroup.centralizer ({a} : Set Q)) : ℤ) = q + ε)
    (hLz : (Nat.card ↥(L ⊓ Subgroup.centralizer ({z} : Set Q)) : ℤ) = q - ε)
    (hPla : P ≤ L ⊓ Subgroup.centralizer ({a} : Set Q))
    (hPlz : P ≤ L ⊓ Subgroup.centralizer ({z} : Set Q)) :
    Nat.card P ∣ 2 := by
  have h1 : (Nat.card P : ℤ) ∣ q + ε := by
    rw [← hLa]
    exact_mod_cast Subgroup.card_dvd_of_le hPla
  have h2 : (Nat.card P : ℤ) ∣ q - ε := by
    rw [← hLz]
    exact_mod_cast Subgroup.card_dvd_of_le hPlz
  have h3 : (Nat.card P : ℤ) ∣ (q + ε) - (q - ε) := dvd_sub h1 h2
  have h3' : (Nat.card P : ℤ) ∣ 2 := by
    rcases hε1 with hε | hε
    · have h4 : (q + ε) - (q - ε) = 2 := by rw [hε]; ring
      rwa [h4] at h3
    · have h4 : (q + ε) - (q - ε) = -2 := by rw [hε]; ring
      rw [h4] at h3
      simpa using dvd_neg.mp h3
  exact_mod_cast h3'

private theorem eq_bot_of_le_two_centralizers {Q : Type} [Group Q] [Finite Q]
    {L P : Subgroup Q} {a z : Q} {q ε : ℤ} {r : ℕ} (hε1 : ε = 1 ∨ ε = -1)
    (hLa : (Nat.card ↥(L ⊓ Subgroup.centralizer ({a} : Set Q)) : ℤ) = q + ε)
    (hLz : (Nat.card ↥(L ⊓ Subgroup.centralizer ({z} : Set Q)) : ℤ) = q - ε)
    (hr : r.Prime) (hr2 : r ≠ 2) (hP : IsPGroup r P)
    (hPla : P ≤ L ⊓ Subgroup.centralizer ({a} : Set Q))
    (hPlz : P ≤ L ⊓ Subgroup.centralizer ({z} : Set Q)) : P = ⊥ := by
  have hfr : Fact r.Prime := ⟨hr⟩
  have hdvd : Nat.card P ∣ 2 :=
    card_dvd_two_of_le_two_centralizers hε1 hLa hLz hPla hPlz
  obtain ⟨k, hk⟩ := hP.exists_card_eq
  have hodd : Odd (Nat.card P) := by
    rw [hk]
    exact (hr.odd_of_ne_two hr2).pow
  have hone : Nat.card P = 1 := by
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
    · exact h
    · rw [h] at hodd
      norm_num at hodd
  exact Subgroup.card_eq_one.mp hone

private theorem oddSylow_le {Q : Type} [Group Q] [Finite Q] {L T A : Subgroup Q}
    {Ω : Set (Subgroup Q)} (hS : CFSG.Quasithin.Vol2.Ch11.SecU1.Setting L)
    (hT : IsSylowIn 2 T ⊤) (hAΩ : A ∈ Ω) (hAT : A ≤ T)
    (hA : IsElemAbelian 2 A) {z : Q} (hz2 : orderOf z = 2)
    (hTz : T ≤ Subgroup.centralizer ({z} : Set Q)) {U : Subgroup Q}
    (hUle : U ≤ L ⊓ Subgroup.centralizer ({z} : Set Q)) (hUcyc : IsCyclic ↥U)
    (hzU : z ∈ U)
    (hUD : ∀ d ∈ L ⊓ Subgroup.centralizer ({z} : Set Q), d ∉ U →
      d * d = 1 ∧ ∀ u ∈ U, d * u * d⁻¹ = u⁻¹)
    {q ε : ℤ} (hε1 : ε = 1 ∨ ε = -1)
    (hLz : (Nat.card ↥(L ⊓ Subgroup.centralizer ({z} : Set Q)) : ℤ) = q - ε)
    {a : Q} (haA : a ∈ A) (ha2 : orderOf a = 2)
    (hclass : (a ∈ L ∧ a ≠ z) ∨
      (a ∉ L ∧ (Nat.card ↥(L ⊓ Subgroup.centralizer ({a} : Set Q)) : ℤ) = q + ε))
    {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) {P : Subgroup Q}
    (hPsyl : IsSylowIn r P (Subgroup.centralizer ({z} : Set Q))) :
    P ≤ genEi 1 T Ω ⊔ T := by
  have hQL : ∀ x : Q, ∃ k : ℕ, x ^ 2 ^ k ∈ L := hS.almostSimple.two
  by_cases hPbot : P = ⊥
  · rw [hPbot]
    exact bot_le
  have hD : ∀ d ∈ L ⊓ Subgroup.centralizer ({z} : Set Q), d ∉ U → d * d = 1 :=
    fun d hd hdU => (hUD d hd hdU).1
  have hPle : P ≤ U := le_of_isPGroup_of_le_centralizer hQL hD hr hr2 hPsyl.isPGroup hPsyl.le
  have hPcyc : IsCyclic ↥P := Subgroup.isCyclic_of_le hPle
  have hleCN : Subgroup.centralizer ({z} : Set Q) ≤ Subgroup.normalizer (P : Set Q) :=
    centralizer_le_normalizer_of_isSylowIn hUcyc hQL hD hr hr2 hPsyl
  have hτP : tA T A ≤ Subgroup.normalizer (P : Set Q) :=
    (CFSG.Quasithin.E1.tauOf_le ⊤ T A).trans (hTz.trans hleCN)
  have hnotC : ¬ P ≤ Subgroup.centralizer ({a} : Set Q) := by
    rcases hclass with ⟨haL, hane⟩ | ⟨-, hcarda⟩
    · have haLC : a ∈ L ⊓ Subgroup.centralizer ({z} : Set Q) :=
        ⟨haL, hTz (hAT haA)⟩
      have haU : a ∉ U := by
        intro haU
        have hEq : (⟨a, haU⟩ : ↥U) = ⟨z, hzU⟩ :=
          CFSG.ABGLocalTools.eq_of_orderOf_eq_two_of_isCyclic
            (by rw [Subgroup.orderOf_mk]; exact ha2)
            (by rw [Subgroup.orderOf_mk]; exact hz2)
        exact hane (by simpa using congrArg Subtype.val hEq)
      exact CFSG.GroupTheory.not_le_centralizer_of_forall_conj_eq_inv hr hr2 hPsyl.isPGroup
        hPbot fun x hx => (hUD a haLC haU).2 x (hPle hx)
    · have haN : a ∈ Subgroup.normalizer (P : Set Q) := hleCN (hTz (hAT haA))
      have ha2' : a ^ 2 = 1 := by
        rw [← ha2]
        exact pow_orderOf_eq_one a
      rcases CFSG.GroupTheory.conj_eq_or_eq_inv_of_isCyclic_of_isPGroup hr hr2 hPsyl.isPGroup
        hPcyc haN ha2' with hcen | hinv
      · intro hle
        apply hPbot
        have hPa : P ≤ Subgroup.centralizer ({a} : Set Q) := by
          intro x hx
          rw [Subgroup.mem_centralizer_singleton_iff]
          calc x * a = (a * x * a⁻¹) * a := by rw [hcen x hx]
            _ = a * x := by group
        have hPleL : P ≤ L := fun x hx => (hUle (hPle hx)).1
        exact eq_bot_of_le_two_centralizers hε1 hcarda hLz hr hr2 hPsyl.isPGroup
          (le_inf hPleL hPa) (le_inf hPleL hPsyl.le)
      · exact CFSG.GroupTheory.not_le_centralizer_of_forall_conj_eq_inv hr hr2 hPsyl.isPGroup
          hPbot hinv
  have hIn : InCalEi 1 T A (P ⊔ tA T A) :=
    inCalEi_sup_tA_of_isCyclic hr hr2 hT hAT hA le_rfl hPsyl.isPGroup hPcyc hτP
      ⟨a, haA, hnotC⟩
  exact (le_sup_left.trans (le_genEi_of_inCalEi hAΩ hAT hIn)).trans le_sup_left

private theorem pow_ne_nine {p e : ℕ} (hp : p.Prime) (h3 : 3 < p ^ e)
    (hP : 3 ≤ e ∨ (e = 2 ∧ 5 ≤ p)) : p ^ e ≠ 9 := by
  intro h9
  have he0 : e ≠ 0 := by
    rintro rfl
    norm_num at h3
  have hp3 : p = 3 := by
    have hd : p ∣ 3 ^ 2 := by
      rw [show (3 : ℕ) ^ 2 = 9 by norm_num, ← h9]
      exact dvd_pow_self p he0
    exact ((Nat.prime_three.dvd_iff_eq hp.ne_one).mp (hp.dvd_of_dvd_pow hd)).symm
  have he2 : e = 2 := by
    have h1 : 3 ^ e = 3 ^ 2 := by
      rw [← hp3, h9, hp3]
      norm_num
    exact Nat.pow_right_injective (by norm_num) h1
  rcases hP with h3' | ⟨-, hp5⟩
  · have hq : (3 : ℕ) ^ e = 9 := by rw [← hp3, h9]
    have h : 3 ^ 3 ≤ 3 ^ e := Nat.pow_le_pow_right (by norm_num) h3'
    rw [hq] at h
    norm_num at h
  · omega

theorem fourTenLarge_holds :
    FourTenLarge := by
  intro Q _ _ L p e hset hP T hT Ω hΩ hcard
  have hS : CFSG.Quasithin.Vol2.Ch11.SecU1.Setting L := FourTenSetting.secU1Setting hset hP
  have hLN : L.Normal := hS.almostSimple.normal
  obtain ⟨z, hzL, hz2, -, hzT⟩ := hS.exists_central_involution hT
  have hcoat : IsCoatom (Subgroup.centralizer ({z} : Set Q)) :=
    hS.isCoatom_centralizer hzL hz2
  obtain ⟨-, K, hKfield, hKfin, hKcard, ⟨e₀⟩⟩ := hset.isL2
  have hKodd : IsOddPrimePower (Nat.card K) :=
    ⟨p, e, hset.prime, hset.prime.odd_of_ne_two hset.ne_two, by omega, hKcard⟩
  have hKL2 : L2Field K := ⟨odd_of_isOddPrimePower hKodd, by rw [hKcard]; exact hset.three_lt⟩
  let eP : ↥L ≃* PSL2 K := e₀.trans (L2.equivPSL K)
  obtain ⟨ε, hε1, hε⟩ := L2Seitz.exists_eps hKL2
  obtain ⟨N⟩ := exists_notation hKL2 e₀
  have hKne9 : Nat.card K ≠ 9 := by
    rw [hKcard]
    exact pow_ne_nine hset.prime hset.three_lt hP
  obtain ⟨A, hAΩ, hAT⟩ := hΩ.exists_mem_le hT
  have hA : IsElemAbelian 2 A := hΩ.elemAbelian A hAΩ
  have hA4 : 4 ≤ Nat.card A := hcard A hAΩ hAT
  obtain ⟨A', hA'Ω, hA'T, a, haA', ha2, hclass⟩ :=
    exists_mem_omega_inner_ne_or_diag hS hKL2 e₀ N hKne9 hε1 hε hT hzL hz2 hzT hΩ hAΩ hAT hA4
  have hA'el : IsElemAbelian 2 A' := hΩ.elemAbelian A' hA'Ω
  have hA'4 : 4 ≤ Nat.card A' := hcard A' hA'Ω hA'T
  have hTz : T ≤ Subgroup.centralizer ({z} : Set Q) := fun t ht =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hzT t ht)
  have hcz : (Nat.card ↥(L ⊓ Subgroup.centralizer ({z} : Set Q)) : ℤ) = Nat.card K - ε :=
    CFSG.GH72.card_inf_centralizer_of_psl2 hKodd eP hε hε1 hzL hz2
  obtain ⟨U, hUle, hUcyc, hzU, hUD⟩ := exists_cyclic_torus_inf_centralizer eP hKodd hzL hz2
  have hC_le : Subgroup.centralizer ({z} : Set Q) ≤ genEi 1 T Ω ⊔ T := by
    refine CFSG.GroupTheory.le_of_forall_exists_isSylowIn_le ?_
    intro r hr
    by_cases hr2 : r = 2
    · subst hr2
      exact ⟨T, CFSG.Quasithin.E6.isSylowIn_of_le hT hTz le_top, le_sup_right⟩
    · have hfr : Fact r.Prime := ⟨hr⟩
      obtain ⟨P, hPsyl, -⟩ := CFSG.Quasithin.exists_isSylowIn_ge r (P := ⊥)
        (H := Subgroup.centralizer ({z} : Set Q)) bot_le IsPGroup.of_bot
      exact ⟨P, hPsyl, oddSylow_le hS hT hA'Ω hA'T hA'el hz2 hTz hUle hUcyc hzU hUD
        hε1 hcz haA' ha2 hclass hr hr2 hPsyl⟩
  obtain ⟨g, hgT, K', hK', hK'z⟩ :=
    exists_conj_inCalEi_not_le_centralizer hS hT hset.pCoreOf_two_top hzL hz2 hzT
      hA'el hA'4 (i := 1) le_rfl
  have hA''Ω : A1b.conjSub g A' ∈ Ω := by
    have h1 := hΩ.conj A' hA'Ω g⁻¹
    rwa [CFSG.Quasithin.conjSubgroup_eq_conjSub A' g⁻¹, inv_inv] at h1
  have hK'le : K' ≤ genEi 1 T Ω := le_genEi_of_inCalEi hA''Ω hgT hK'
  have hlt : Subgroup.centralizer ({z} : Set Q) < genEi 1 T Ω ⊔ T := by
    refine lt_of_le_of_ne hC_le ?_
    intro hCX
    exact hK'z (hK'le.trans (le_sup_left.trans (le_of_eq hCX.symm)))
  exact hcoat.lt_iff.mp hlt

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

end
