module

public import CFSG.RankThree.PartTwo.Sec16.Item16Res3ProofCent
public import CFSG.RankThree.PartTwo.Sec14.Item143N
import CFSG.RankThree.PartTwo.Sec16.Item16Res3ProofIndex
import CFSG.RankThree.PartTwo.Sec16.Item16Tail13
import CFSG.RankThree.PartTwo.Sec15.Item1515StepsProofLA7
import CFSG.RankThree.PartTwo.Sec6.Item612Plus
import CFSG.GroupTheory.TwoElementSquare
import CFSG.RankThree.PartTwo.Sec5.Tools
import CFSG.RankThree.PartTwo.Sec17.Item17Q0ProofTools
import CFSG.RankThree.PartTwo.KFacts.KS14HJBasic
import CFSG.Goldschmidt.Steps.G310Basic
public import CFSG.LocalAnalysis.RankThreeEvenClassification.CoprimeFactorization
import CFSG.RankThree.PartTwo.Sec13.Item136Pair

public section

namespace CFSG.RankThree.PartTwo.Sec16.Res163U35Facts

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15
  CFSG.GH74.GLS
open CFSG.Assembly.RankThreeEven (projSU)
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L Y : Subgroup G}

theorem facts (h : Sec15R G A c L) (hY : Y ∈ scriptY0Star A (lB A))
    (hC : Case1514Three A (lB A) c L Y) :
    IsSimpleGroup ↥L ∧ Nat.card L = 126000 ∧
      Nonempty (↥(Y ⊓ L) ≃* alternatingGroup (Fin 7)) ∧
      (∀ z ∈ L, z ∈ Subgroup.centralizer (L : Set G) → z = 1) ∧
      A ≤ Subgroup.normalizer ((Y ⊓ L : Subgroup G) : Set G) ∧
      Nat.card ↥(A ⊓ L) = 9 ∧ A ⊓ L ≤ Y ⊓ L ∧
      (∀ σ : MulAut ↥L, (∀ k : ↥L, (k : G) ∈ Y ⊓ L → σ k = k) → σ = 1) := by
  obtain ⟨⟨inst5, ⟨φU⟩⟩, ⟨φY⟩, hcov, -, -, hLs, -⟩ := hC
  have hD := h.toSec13Data
  haveI := inst5
  set U := ↥(projSU 3 5 1) with hUdef
  have hUcard : Nat.card U = 126000 := Proof1515.card_projSU_three_five
  have : Finite U := Nat.finite_of_card_ne_zero (by rw [hUcard]; norm_num)
  have : Nontrivial U := Finite.one_lt_card_iff_nontrivial.mp (by rw [hUcard]; norm_num)
  obtain ⟨ψ⟩ := Res163.nonempty_mulEquiv_of_isSimpleGroup hLs φU
  have hLcard : Nat.card L = 126000 := by
    rw [Nat.card_congr ψ.toEquiv, hUcard]
  have h5040 : ∀ H : Subgroup ↥L, Nat.card H ≠ 5040 := fun H hH =>
    Res3U35.ks163U35NoIndex25 inst5 (H.map ψ.toMonoidHom)
      (by rw [Subgroup.card_map_of_injective ψ.injective]; exact hH)
  set K := Y ⊓ L with hKdef
  have hKL : K ≤ L := inf_le_right
  obtain ⟨φK⟩ := Res163.nonempty_mulEquiv_a7_of_cover hLcard h5040 φY hcov
  have hcent : ∀ σ : MulAut ↥L, (∀ k : ↥L, (k : G) ∈ K → σ k = k) → σ = 1 := by
    intro σ hσ
    set K' := (K.subgroupOf L).map ψ.toMonoidHom with hK'
    have hK'7 : Nonempty (↥K' ≃* alternatingGroup (Fin 7)) :=
      ⟨((Subgroup.equivMapOfInjective _ _ ψ.injective).symm.trans
        (Subgroup.subgroupOfEquivOfLe hKL)).trans φK⟩
    have h1 := Res3U35.ks163U35CentA7 inst5 K' hK'7 ((ψ.symm.trans σ).trans ψ) (by
      rintro _ ⟨k, hk, rfl⟩
      show ψ (σ (ψ.symm (ψ k))) = ψ k
      rw [MulEquiv.symm_apply_apply, hσ k (Subgroup.mem_subgroupOf.mp hk)])
    refine MulEquiv.ext fun l => ?_
    have h2 := congrArg (fun τ : MulAut U => τ (ψ l)) h1
    simp only [MulEquiv.trans_apply, MulEquiv.symm_apply_apply, MulAut.one_apply] at h2
    exact ψ.injective h2
  have hZ : ∀ z ∈ L, z ∈ Subgroup.centralizer (L : Set G) → z = 1 := by
    intro z hzL hzC
    have hc := Res163.center_eq_bot_of_isQuasisimple_quot hLs (aschbacherSolvableCore 3 ↥L)
      (Sec6.isQuasisimple_of_mem_thetaComponentsAt hD.mem_thetaComponentsAt)
    have hzc : (⟨z, hzL⟩ : ↥L) ∈ Subgroup.center ↥L := by
      rw [Subgroup.mem_center_iff]
      intro l
      exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hzC l l.2)
    rw [hc, Subgroup.mem_bot] at hzc
    exact congrArg Subtype.val hzc
  have hAY : A ≤ Subgroup.normalizer (Y : Set G) := hY.prop.1.1.2
  have hAK : A ≤ Subgroup.normalizer (K : Set G) := fun a ha =>
    Subgroup.inf_normalizer_le_normalizer_inf ⟨hAY ha, hD.le_normalizer ha⟩
  have hinner : ∀ a ∈ A, ∃ k ∈ K, k⁻¹ * a ∈ Subgroup.centralizer (L : Set G) := fun a ha =>
    Res163.exists_inner_of_cent hKL ⟨φK⟩ hcent (hD.le_normalizer ha) (hAK ha)
      (hD.isElemAbelian.2 a ha)
  obtain ⟨-, hTK, hT9⟩ := Res163.inner_facts h hKL hinner hZ
  exact ⟨hLs, hLcard, ⟨φK⟩, hZ, hAK, hT9, hTK, hcent⟩

theorem pCoreOf_inf_centralizer_c_eq_bot (h : Sec15R G A c L)
    (hY : Y ∈ scriptY0Star A (lB A)) (hC : Case1514Three A (lB A) c L Y) :
    CFSG.Open.pCoreOf 2 Y ⊓ Subgroup.centralizer ({c} : Set G) = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, -, ⟨φK⟩, -, -, -, -, hcent⟩ := facts h hY hC
  obtain ⟨-, -, -, -, -, -, hOdd⟩ := hC
  set Q : Subgroup G := CFSG.Open.pCoreOf 2 Y with hQdef
  set P : Subgroup G := Q ⊓ Subgroup.centralizer ({c} : Set G) with hPdef
  have hQleY : Q ≤ Y := CFSG.LieType.BorelTits.pCoreOf_le 2 Y
  have hQ2 : IsPGroup 2 Q := CFSG.LieType.BorelTits.pCoreOf_isPGroup (r := 2) Y
  have hYQn : Y ≤ Subgroup.normalizer (Q : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 Y
  have hQL : Q ⊓ L = ⊥ := by
    have hK : Q ⊓ L = Q ⊓ (Y ⊓ L) := by
      rw [← inf_assoc, inf_eq_left.mpr hQleY]
    rw [hK]
    set K : Subgroup G := Y ⊓ L with hKdef
    have hKn : K ≤ Subgroup.normalizer (Q ⊓ K : Subgroup G) :=
      (le_inf (inf_le_left.trans hYQn) Subgroup.le_normalizer).trans
        Subgroup.inf_normalizer_le_normalizer_inf
    have hRnorm : ((Q ⊓ K).subgroupOf K).Normal := by
      rw [Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_right]
      exact hKn
    have hR2 : IsPGroup 2 ((Q ⊓ K).subgroupOf K) :=
      (hQ2.to_inf_left (K := K)).of_equiv
        (Subgroup.subgroupOfEquivOfLe inf_le_right).symm
    have hKsimple : IsSimpleGroup ↥K := by
      haveI : IsSimpleGroup (alternatingGroup (Fin 7)) := alternatingGroup.isSimpleGroup (by simp)
      haveI : Nontrivial ↥K := φK.surjective.nontrivial
      exact IsSimpleGroup.isSimpleGroup_of_surjective φK.symm.toMonoidHom φK.symm.surjective
    have hnonab : ∃ a b : ↥K, a * b ≠ b * a := by
      obtain ⟨a, b, hab⟩ : ∃ a b : alternatingGroup (Fin 7), a * b ≠ b * a := by
        let a : alternatingGroup (Fin 7) :=
          ⟨Equiv.swap 0 1 * Equiv.swap 1 2, by
            rw [Equiv.Perm.mem_alternatingGroup, Equiv.Perm.sign_mul,
              Equiv.Perm.sign_swap (by decide : (0 : Fin 7) ≠ 1),
              Equiv.Perm.sign_swap (by decide : (1 : Fin 7) ≠ 2)]
            norm_num⟩
        let b : alternatingGroup (Fin 7) :=
          ⟨Equiv.swap 0 1 * Equiv.swap 0 3, by
            rw [Equiv.Perm.mem_alternatingGroup, Equiv.Perm.sign_mul,
              Equiv.Perm.sign_swap (by decide : (0 : Fin 7) ≠ 1),
              Equiv.Perm.sign_swap (by decide : (0 : Fin 7) ≠ 3)]
            norm_num⟩
        refine ⟨a, b, ?_⟩
        intro h
        have h' := congrArg (fun x : alternatingGroup (Fin 7) => (x : Equiv.Perm (Fin 7))) h
        simp only [Subgroup.coe_mul] at h'
        exact (by decide : (a : Equiv.Perm (Fin 7)) * b ≠ b * a) h'
      refine ⟨φK.symm a, φK.symm b, fun h => hab ?_⟩
      have := congrArg φK h
      simpa using this
    have hRbot : (Q ⊓ K).subgroupOf K = ⊥ := by
      haveI := hRnorm
      exact CFSG.eq_bot_of_normal_isPGroup_of_isSimpleGroup hnonab hR2
    rw [← Subgroup.map_subgroupOf_eq_of_le (inf_le_right : Q ⊓ K ≤ K), hRbot,
      Subgroup.map_bot]
  have hPK : ∀ p ∈ P, ∀ k ∈ Y ⊓ L, p * k = k * p := by
    intro p hp k hk
    have hpP : p ∈ Q ⊓ Subgroup.centralizer ({c} : Set G) := hPdef ▸ hp
    have hpQ : p ∈ Q := hpP.1
    have hpY : p ∈ Y := hQleY hpQ
    have hkY : k ∈ Y := hk.1
    have hkL : k ∈ L := hk.2
    have hcommQ : p * k * p⁻¹ * k⁻¹ ∈ Q := by
      have h1 : k * p * k⁻¹ ∈ Q :=
        (Subgroup.mem_normalizer_iff.mp (hYQn hkY) p).mp hpQ
      have h3 : p * (k * p * k⁻¹)⁻¹ ∈ Q := Q.mul_mem hpQ (Q.inv_mem h1)
      convert h3 using 1 <;> group
    have hcommL : p * k * p⁻¹ * k⁻¹ ∈ L := by
      have hpC : p ∈ Subgroup.centralizer ({c} : Set G) := (hPdef ▸ hp).2
      have hpN : p ∈ Subgroup.normalizer (L : Set G) :=
        Proof1613.centralizer_le_normalizer_L h.toSec14Std hpC
      have h1 : p * k * p⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp hpN k).mp hkL
      exact L.mul_mem h1 (L.inv_mem hkL)
    have hbot : p * k * p⁻¹ * k⁻¹ ∈ (⊥ : Subgroup G) := by
      rw [← hQL]
      exact ⟨hcommQ, hcommL⟩
    have h1 : p * k * p⁻¹ * k⁻¹ = 1 := Subgroup.mem_bot.mp hbot
    calc p * k = (p * k * p⁻¹ * k⁻¹) * (k * p) := by group
      _ = k * p := by rw [h1, one_mul]
  have hPleC : P ≤ Subgroup.centralizer ({c} : Set G) := by
    rw [hPdef]
    exact inf_le_right
  have hPleNL : P ≤ Subgroup.normalizer (L : Set G) :=
    hPleC.trans (Proof1613.centralizer_le_normalizer_L h.toSec14Std)
  have hPleCL : P ≤ Subgroup.centralizer (L : Set G) := by
    intro p hp
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    let σ : MulAut ↥L := L.normalizerMonoidHom ⟨p, hPleNL hp⟩
    have hσ1 : σ = 1 := hcent σ fun k hk => by
      apply Subtype.ext
      have hpk : p * (k : G) = (k : G) * p := hPK p hp k hk
      rw [show ((σ k : ↥L) : G) = p * (k : G) * p⁻¹ from
        Subgroup.normalizerMonoidHom_apply_apply_coe L ⟨p, hPleNL hp⟩ k]
      rw [hpk]
      group
    have h1 := congrArg (fun τ : MulAut ↥L => τ ⟨l, hl⟩) hσ1
    simp only [MulAut.one_apply] at h1
    have h2 : p * l * p⁻¹ = l := by
      have h3 := congrArg Subtype.val h1
      rw [show ((σ ⟨l, hl⟩ : ↥L) : G) = p * l * p⁻¹ from
        Subgroup.normalizerMonoidHom_apply_apply_coe L ⟨p, hPleNL hp⟩ ⟨l, hl⟩] at h3
      exact h3
    calc l * p = (p * l * p⁻¹) * p := by rw [h2]
      _ = p * l := by group
  have hPle : P ≤ Subgroup.centralizer ({c} : Set G) ⊓ Subgroup.centralizer (L : Set G) :=
    le_inf hPleC hPleCL
  have hOddP : Odd (Nat.card P) := Odd.of_dvd_nat hOdd (Subgroup.card_dvd_of_le hPle)
  have hP2 : IsPGroup 2 P := by
    rw [hPdef]
    exact hQ2.to_inf_left
  have hPbot : P = ⊥ := by
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hP2
    have hn0 : n = 0 := by
      rcases n with _ | n
      · rfl
      · exfalso
        have heven : Even (Nat.card P) := by
          rw [hn]
          exact even_two.pow_of_ne_zero (Nat.succ_ne_zero n)
        exact (Nat.not_even_iff_odd.mpr hOddP) heven
    exact Subgroup.card_eq_one.mp (by rw [hn, hn0, pow_zero])
  simpa [hPdef] using hPbot

theorem exists_a (h : Sec15R G A c L) (hY : Y ∈ scriptY0Star A (lB A))
    (hC : Case1514Three A (lB A) c L Y) {w : G}
    (hwA : w ∈ Subgroup.normalizer (A : Set G)) (hwL : w ∈ L) :
    ∃ a ∈ A, a ∉ Subgroup.zpowers c ∧
      CFSG.Open.pCoreOf 2 Y ⊓ Subgroup.centralizer ({a} : Set G) ≠ ⊥ ∧
      (CFSG.Open.pCoreOf 2 Y).map (MulAut.conj w).toMonoidHom ⊓
        Subgroup.centralizer ({a} : Set G) ≠ ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Q : Subgroup G := CFSG.Open.pCoreOf 2 Y with hQdef
  set Qw : Subgroup G := Q.map (MulAut.conj w).toMonoidHom with hQwdef
  have hQleY : Q ≤ Y := CFSG.LieType.BorelTits.pCoreOf_le 2 Y
  have hQ2 : IsPGroup 2 Q := CFSG.LieType.BorelTits.pCoreOf_isPGroup (r := 2) Y
  have hQne : Q ≠ ⊥ := hY.prop.2.2
  have hAY : A ≤ Subgroup.normalizer (Y : Set G) := hY.prop.1.1.2
  have hAQ : A ≤ Subgroup.normalizer (Q : Set G) :=
    hAY.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 Y)
  have hQw2 : IsPGroup 2 Qw := hQ2.map _
  have hQwne : Qw ≠ ⊥ := by
    rw [hQwdef]
    intro hbot
    apply hQne
    rwa [Subgroup.map_eq_bot_iff_of_injective _ (MulAut.conj w).injective] at hbot
  have hconjQw : ∀ a ∈ A, ∀ y, y ∈ Qw → a * y * a⁻¹ ∈ Qw := by
    intro a ha y hy
    obtain ⟨q, hq, rfl⟩ := Subgroup.mem_map.mp hy
    have hwa : w⁻¹ * a * w ∈ A := by
      simpa using (Subgroup.mem_normalizer_iff.mp (inv_mem hwA) a).mp ha
    have hq' : (w⁻¹ * a * w) * q * (w⁻¹ * a * w)⁻¹ ∈ Q :=
      (Subgroup.mem_normalizer_iff.mp (hAQ hwa) q).mp hq
    refine Subgroup.mem_map.mpr ⟨_, hq', ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  have hAQw : A ≤ Subgroup.normalizer (Qw : Set G) := by
    intro a ha
    refine Subgroup.mem_normalizer_iff.mpr fun y => ⟨fun hy => hconjQw a ha y hy, fun hy => ?_⟩
    have h := hconjQw a⁻¹ (A.inv_mem ha) (a * y * a⁻¹) hy
    convert h using 1 <;> group
  have gen : ∀ X : Subgroup G, X ≠ ⊥ → IsPGroup 2 X → A ≤ Subgroup.normalizer (X : Set G) →
      ∃ B : Subgroup G, B ≤ A ∧ Nat.card B = 9 ∧ X ⊓ Subgroup.centralizer (B : Set G) ≠ ⊥ := by
    intro X hXne hX2 hAX
    by_contra hno
    have htriv : ∀ H : Subgroup G, H ≤ A → Nat.card H = 9 →
        X ⊓ Subgroup.centralizer (H : Set G) = ⊥ := by
      intro H hHA hH
      by_contra hne
      exact hno ⟨H, hHA, hH, hne⟩
    have hcop : Nat.Coprime 3 (Nat.card X) := by
      obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hX2
      rw [hn]
      exact Nat.Coprime.pow_right n (by norm_num)
    have hle : X ≤ ⊥ := Sec5.le_of_forall_inf_centralizer_sub_le (p := 3) (k := 2)
      Nat.prime_three h.toSec13Data.isElemAbelian (by rw [h.toSec13Data.card_eq]; norm_num)
      hAX hcop (fun H hHA hH => by rw [htriv H hHA hH])
    exact hXne (le_bot_iff.mp hle)
  obtain ⟨B₁, hB₁A, hB₁card, hB₁ne⟩ := gen Q hQne hQ2 hAQ
  obtain ⟨B₂, hB₂A, hB₂card, hB₂ne⟩ := gen Qw hQwne hQw2 hAQw
  have hQc : Q ⊓ Subgroup.centralizer ({c} : Set G) = ⊥ :=
    pCoreOf_inf_centralizer_c_eq_bot h hY hC
  have hQwC : Qw ⊓ Subgroup.centralizer ({c} : Set G) = ⊥ := by
    have hwC : w ∈ Subgroup.centralizer ({c} : Set G) :=
      Sec14.le_centralizer_of_mem_thetaComponentsAt h.mem_lA.1 hwL
    have hz : (Subgroup.zpowers c).map (MulAut.conj w).toMonoidHom = Subgroup.zpowers c := by
      rw [MonoidHom.map_zpowers]
      congr 1
      change w * c * w⁻¹ = c
      rw [← Subgroup.mem_centralizer_iff.mp hwC c (by simp)]
      group
    have hCeq : Subgroup.centralizer ({c} : Set G) =
        Subgroup.centralizer ((Subgroup.zpowers c : Subgroup G) : Set G) := by
      rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
    have hmapC : (Subgroup.centralizer ({c} : Set G)).map
        (MulAut.conj w).toMonoidHom = Subgroup.centralizer ({c} : Set G) := by
      rw [hCeq, Sec14.map_conj_centralizer, hz]
    have hmapinf : Qw ⊓ Subgroup.centralizer ({c} : Set G) =
        (Q ⊓ Subgroup.centralizer ({c} : Set G)).map (MulAut.conj w).toMonoidHom := by
      rw [Subgroup.map_inf _ _ _ (MulAut.conj w).injective, hmapC]
    rw [hmapinf, hQc, Subgroup.map_bot]
  have hcB₁ : c ∉ B₁ := by
    intro hc
    apply hB₁ne
    rw [← le_bot_iff]
    calc Q ⊓ Subgroup.centralizer (B₁ : Set G) ≤
          Q ⊓ Subgroup.centralizer ({c} : Set G) :=
        inf_le_inf_left _ (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hc))
      _ = ⊥ := hQc
  have hcB₂ : c ∉ B₂ := by
    intro hc
    apply hB₂ne
    rw [← le_bot_iff]
    calc Qw ⊓ Subgroup.centralizer (B₂ : Set G) ≤
          Qw ⊓ Subgroup.centralizer ({c} : Set G) :=
        inf_le_inf_left _ (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hc))
      _ = ⊥ := hQwC
  have hAab : IsMulCommutative A := h.toSec13Data.isElemAbelian.1
  have hB₁C : B₁ ≤ Subgroup.centralizer (B₂ : Set G) := by
    intro b hb
    rw [Subgroup.mem_centralizer_iff]
    intro b' hb'
    have hcommA : (⟨b, hB₁A hb⟩ : ↥A) * ⟨b', hB₂A hb'⟩ =
        ⟨b', hB₂A hb'⟩ * ⟨b, hB₁A hb⟩ := hAab.is_comm.comm _ _
    exact (congrArg Subtype.val hcommA).symm
  have hprod := Sec6.card_sup_mul_card_inf (X := B₁) (N := B₂)
    (hB₁C.trans (Subgroup.centralizer_le_normalizer (B₂ : Set G)))
  have hsup_le : Nat.card (B₁ ⊔ B₂ : Subgroup G) ≤ 27 := by
    rw [← h.toSec13Data.card_eq]
    exact Subgroup.card_le_of_le (sup_le hB₁A hB₂A)
  have hdvd : Nat.card (B₁ ⊓ B₂ : Subgroup G) ∣ 9 := by
    have := Subgroup.card_dvd_of_le (inf_le_left : B₁ ⊓ B₂ ≤ B₁)
    rwa [hB₁card] at this
  have hdvd' : Nat.card (B₁ ⊓ B₂ : Subgroup G) ∣ 3 ^ 2 := by
    simpa using hdvd
  obtain ⟨k, -, hkcard⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 hdvd'
  have hk0 : k ≠ 0 := by
    rintro rfl
    rw [pow_zero] at hkcard
    rw [hkcard, mul_one, hB₁card, hB₂card] at hprod
    omega
  have h3le : 3 ≤ Nat.card (B₁ ⊓ B₂ : Subgroup G) := by
    rw [hkcard]
    calc 3 = 3 ^ 1 := by norm_num
      _ ≤ 3 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hDne : B₁ ⊓ B₂ ≠ ⊥ := by
    intro hbot
    rw [hbot, Subgroup.card_bot] at h3le
    omega
  obtain ⟨⟨a, haD⟩, ha1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hDne
  have ha1' : a ≠ 1 := fun h => ha1 (Subtype.ext h)
  have haA : a ∈ A := hB₁A haD.1
  have hazc : a ∉ Subgroup.zpowers c := by
    intro haz
    apply hcB₁
    have hca : Nat.card (Subgroup.zpowers c) = 3 := h.zpowers_mem_omegaA.2.1
    have hc3 : orderOf c = 3 := by
      rwa [← Nat.card_zpowers]
    have hadvd : orderOf a ∣ orderOf c := orderOf_dvd_of_mem_zpowers haz
    have hane : orderOf a ≠ 1 := fun h => ha1' (orderOf_eq_one_iff.mp h)
    have ha3 : orderOf a = 3 := by
      rcases (Nat.dvd_prime Nat.prime_three).mp (hc3 ▸ hadvd) with h | h
      · exact absurd h hane
      · exact h
    have hcarda : Nat.card (Subgroup.zpowers a) = 3 := by
      rw [Nat.card_zpowers, ha3]
    have heq : Subgroup.zpowers a = Subgroup.zpowers c :=
      Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr haz) (by rw [hcarda, hca])
    have hc : c ∈ Subgroup.zpowers a := heq ▸ Subgroup.mem_zpowers c
    exact (Subgroup.zpowers_le.mpr haD.1) hc
  have hQa : Q ⊓ Subgroup.centralizer ({a} : Set G) ≠ ⊥ := by
    intro hbot
    apply hB₁ne
    rw [← le_bot_iff]
    calc Q ⊓ Subgroup.centralizer (B₁ : Set G) ≤
          Q ⊓ Subgroup.centralizer ({a} : Set G) :=
        inf_le_inf_left _ (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr haD.1))
      _ = ⊥ := hbot
  have hQwa : Qw ⊓ Subgroup.centralizer ({a} : Set G) ≠ ⊥ := by
    intro hbot
    apply hB₂ne
    rw [← le_bot_iff]
    calc Qw ⊓ Subgroup.centralizer (B₂ : Set G) ≤
          Qw ⊓ Subgroup.centralizer ({a} : Set G) :=
        inf_le_inf_left _ (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr haD.2))
      _ = ⊥ := hbot
  exact ⟨a, haA, hazc, hQa, hQwa⟩

theorem xA_le_centralizer (h : Sec15R G A c L) (hY : Y ∈ scriptY0Star A (lB A))
    (hC : Case1514Three A (lB A) c L Y) :
    xA A ≤ Subgroup.centralizer (L : Set G) := by
  obtain ⟨hLs, -, -, -, -, hT9, -, -⟩ := facts h hY hC
  intro x hx
  have hxC : x ∈ Subgroup.centralizer (A : Set G) := pPrimeCoreOf_le 3 _ hx
  have hxL : x ∈ Subgroup.normalizer (L : Set G) :=
    xA_le_normalizer_of_mem_lA h h.zpowers_mem_omegaA h.mem_lA hx
  have h3not : ¬ 3 ∣ orderOf x := by
    have hcop : Nat.Coprime 3 (Nat.card (xA A)) :=
      coprime_card_pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G))
    have hnot : ¬ 3 ∣ Nat.card (xA A) :=
      (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).1 hcop
    intro h3
    exact hnot (h3.trans (Subgroup.orderOf_dvd_natCard (xA A) hx))
  let σ : MulAut ↥L := L.normalizerMonoidHom ⟨x, hxL⟩
  have hσfix : ∀ l : ↥L, (l : G) ∈ A → σ l = l := by
    intro l hlA
    apply Subtype.ext
    change x * (l : G) * x⁻¹ = (l : G)
    have hcomm : (l : G) * x = x * (l : G) :=
      Subgroup.mem_centralizer_iff.mp hxC (l : G) hlA
    rw [← hcomm]
    group
  have hσpow : σ ^ orderOf x = 1 := by
    change (L.normalizerMonoidHom ⟨x, hxL⟩) ^ orderOf x = 1
    rw [← map_pow]
    have h1 : (⟨x, hxL⟩ : Subgroup.normalizer (L : Set G)) ^ orderOf x = 1 :=
      Subtype.ext (pow_orderOf_eq_one x)
    rw [h1, map_one]
  obtain ⟨inst5, ⟨φU⟩⟩ := hC.1
  haveI := inst5
  have hUcard : Nat.card ↥(projSU 3 5 1) = 126000 := Proof1515.card_projSU_three_five
  haveI : Finite ↥(projSU 3 5 1) := Nat.finite_of_card_ne_zero (by rw [hUcard]; norm_num)
  haveI : Nontrivial ↥(projSU 3 5 1) :=
    Finite.one_lt_card_iff_nontrivial.mp (by rw [hUcard]; norm_num)
  obtain ⟨ψL⟩ := Res163.nonempty_mulEquiv_of_isSimpleGroup hLs φU
  let ψ : ↥L ≃* Res3U35.PU5 := ψL.trans Res3U35.equivPU
  let σ' : MulAut Res3U35.PU5 := MulAut.congr ψ σ
  set T : Subgroup G := A ⊓ L with hTdef
  have hTL : T ≤ L := inf_le_right
  have hTA : T ≤ A := inf_le_left
  have hT9' : Nat.card T = 9 := by
    rw [hTdef]
    exact hT9
  let E : Subgroup Res3U35.PU5 := (T.subgroupOf L).map ψ.toMonoidHom
  have hEcard : Nat.card E = 9 := by
    rw [Subgroup.card_map_of_injective ψ.injective,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTL).toEquiv, hT9']
  obtain ⟨g, hg⟩ := Res3U35.exists_conj_eq_E0 hEcard
  have hσfixE : ∀ y ∈ E, σ' y = y := by
    rintro _ ⟨t, ht, rfl⟩
    have htA : ((t : ↥L) : G) ∈ A := hTA (Subgroup.mem_subgroupOf.mp ht)
    change ψ (σ (ψ.symm (ψ t))) = ψ t
    rw [MulEquiv.symm_apply_apply, hσfix t htA]
  let β : MulAut Res3U35.PU5 := MulAut.conj (MulAut.conj g) σ'
  have hβfix : ∀ y ∈ Res3U35.E0, β y = y := by
    intro y hy
    have hyE : g⁻¹ * y * g ∈ E := by
      rw [hg (g⁻¹ * y * g)]
      convert hy using 1 <;> group
    have h1 := hσfixE _ hyE
    change MulAut.conj (MulAut.conj g) σ' y = y
    simp only [MulAut.mul_apply, MulAut.inv_apply, MulAut.conj_apply, MulAut.conj_symm_apply]
    rw [h1]
    group
  obtain ⟨B, τ, hBτ⟩ := KFacts.exists_psuConj_mul_psuField (h := Res3U35.hF) (by norm_num) β
  have hτ : τ = 1 := by
    refine CFSG.Quasithin.H13.U35A6.eq_one_of_fix_omega Res3U35.hF Res3U35.om_pow_three Res3U35.om_ne_one ?_
    exact CFSG.Quasithin.H13.U35A6.sigma_eq_of_fix Res3U35.hF Res3U35.om_pow_three B τ
      (by rw [← hBτ]; exact hβfix _ (by simpa using Res3U35.mem_E0 1 0))
      (by rw [← hBτ]; exact hβfix _ (by simpa using Res3U35.mem_E0 0 1))
  rw [hτ, map_one, mul_one] at hBτ
  obtain ⟨e, he, hβe⟩ := Res3U35.exists_eq_conj_of_fix B
    (by rw [← hBτ]; exact hβfix _ (by simpa using Res3U35.mem_E0 1 0))
    (by rw [← hBτ]; exact hβfix _ (by simpa using Res3U35.mem_E0 0 1))
  have hβe' : β = MulAut.conj e := hBτ.trans hβe
  have hβ3 : β ^ 3 = 1 := by
    rw [hβe', ← map_pow, Res3U35.pow_three_of_mem_E0 he, map_one]
  have hσ'pow : σ' ^ orderOf x = 1 := by
    change (MulAut.congr ψ σ) ^ orderOf x = 1
    rw [← map_pow, hσpow, map_one]
  have hβpow : β ^ orderOf x = 1 := by
    change (MulAut.conj (MulAut.conj g) σ') ^ orderOf x = 1
    rw [← map_pow, hσ'pow, map_one]
  have hβord : orderOf β ∣ orderOf x := orderOf_dvd_of_pow_eq_one hβpow
  have hcopx : Nat.Coprime (orderOf x) 3 :=
    ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 h3not).symm
  have hβ1 : β = 1 := by
    have h := Nat.eq_one_of_dvd_coprimes hcopx hβord (orderOf_dvd_of_pow_eq_one hβ3)
    exact orderOf_eq_one_iff.mp h
  have hσ'1 : σ' = 1 := by
    have hβeq : β = (MulAut.conj g) * σ' * (MulAut.conj g)⁻¹ := MulAut.conj_apply _ _
    have h := hβ1
    rw [hβeq] at h
    calc σ' = (MulAut.conj g)⁻¹ * ((MulAut.conj g) * σ' * (MulAut.conj g)⁻¹) *
          MulAut.conj g := by group
      _ = 1 := by rw [h]; group
  have hσ1 : σ = 1 := (MulAut.congr ψ).injective (by simpa only [map_one] using hσ'1)
  rw [Subgroup.mem_centralizer_iff]
  intro l hl
  have h1 := congrArg (fun τ : MulAut ↥L => τ ⟨l, hl⟩) hσ1
  simp only [MulAut.one_apply] at h1
  have h2 : x * l * x⁻¹ = l := by
    have h3 := congrArg Subtype.val h1
    rw [show ((σ ⟨l, hl⟩ : ↥L) : G) = x * l * x⁻¹ from
      Subgroup.normalizerMonoidHom_apply_apply_coe L ⟨x, hxL⟩ ⟨l, hl⟩] at h3
    exact h3
  calc l * x = (x * l * x⁻¹) * x := by rw [h2]
    _ = x * l := by group

theorem lB_eq_bot_of_case1514Three (h : Sec15R G A c L)
    (hY : Y ∈ scriptY0Star A (lB A)) (hC : Case1514Three A (lB A) c L Y) :
    ∀ B : Subgroup G, IsHyperplane A B → lB A B = ⊥ := by
  obtain ⟨-, hLcard, -, -, -, -, -, -⟩ := facts h hY hC
  have hΩ : omegaA A = {Subgroup.zpowers c} := hC.2.2.2.1
  intro B hB
  refine lB_eq_bot fun b d L' hc => ?_
  obtain ⟨-, hbΩ, hLb, ⟨φJ⟩, -⟩ := hc
  have hzw : Subgroup.zpowers b = Subgroup.zpowers c := by
    rw [hΩ] at hbΩ
    simpa using hbΩ
  have hLb_eq : lA A b = lA A c := Sec13.lA_congr hzw
  have hLmem : L ∈ lA A b := by
    rw [hLb_eq]
    exact h.mem_lA
  have hLL' : L' = L := by
    have hmem : L ∈ ({L'} : Set (Subgroup G)) := by
      rwa [← hLb]
    exact (Set.mem_singleton_iff.mp hmem).symm
  subst L'
  have hdvd : Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) ∣ Nat.card L :=
    Subgroup.card_quotient_dvd_card _
  have hquot : Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) = 604800 := by
    rw [Nat.card_congr φJ.toEquiv, KFacts.KS14.card_nativeJ2]
  rw [hquot, hLcard] at hdvd
  norm_num at hdvd

theorem pCoreOf_mem_scriptQ (h : Sec15R G A c L) (hY : Y ∈ scriptY0Star A (lB A))
    (hC : Case1514Three A (lB A) c L Y) (h1444 : Item1444 A (lB A))
    (h146 : Item146 A (lB A)) :
    CFSG.Open.pCoreOf 2 Y ∈ scriptQ A (lB A) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set Q : Subgroup G := CFSG.Open.pCoreOf 2 Y with hQdef
  have hQleY : Q ≤ Y := CFSG.LieType.BorelTits.pCoreOf_le 2 Y
  have hAY : A ≤ Subgroup.normalizer (Y : Set G) := hY.prop.1.1.2
  have hAV : A ≤ Subgroup.normalizer (Q : Set G) :=
    hAY.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 Y)
  have hhyper : ∃ B : Subgroup G, IsHyperplane A B := by
    obtain ⟨B', hB'⟩ := Sylow.exists_subgroup_card_pow_prime (G := A) 3 (n := 2) (by
      rw [h.toSec13Data.card_eq]; norm_num)
    refine ⟨B'.map A.subtype, Subgroup.map_subtype_le _, ?_⟩
    rw [h.toSec13Data.card_eq, Subgroup.card_map_of_injective A.subtype_injective, hB']
    norm_num
  obtain ⟨B, hB⟩ := hhyper
  have hbot : ∃ B : Subgroup G, IsHyperplane A B ∧ lB A B = ⊥ :=
    ⟨B, hB, lB_eq_bot_of_case1514Three h hY hC B hB⟩
  have hbotmem : (⊥ : Subgroup G) ∈ scriptQ A (lB A) := by
    refine ⟨bot_mem_invariantPiSubgroups ⊤ A (piCompl 3), fun B hB => ?_⟩
    simp
  have hCmem : Q ⊓ Subgroup.centralizer ({c} : Set G) ∈ scriptQ A (lB A) := by
    rw [pCoreOf_inf_centralizer_c_eq_bot h hY hC]
    exact hbotmem
  have hN : ⁅Q, Y⁆ ∈ scriptQ A (lB A) :=
    Sec17.Proof17Q0.commutator_pCoreOf_mem_scriptQ h.isE27 h1444 h146 hbot hY.prop.1
  have hcov : Y = (Y ⊓ L) ⊔ Q := hC.2.2.1
  refine Sec17.Proof17Q0.pCoreOf_mem_scriptQ_of_scriptY4 h.isE27 h146 hY.prop.1 hN
    h.toSec13Data.mem_A ?_ hCmem
  exact Or.inr (Sec17.Proof17Q0.commutatorElement_mem_of_eq_sup hcov
    (inf_le_left.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 Y))
    (hAV h.toSec13Data.mem_A) (inf_le_right.trans h.toSec13Data.le_centralizer))

theorem le_pPrimeCoreOf (h : Sec15R G A c L) (hY : Y ∈ scriptY0Star A (lB A))
    (hC : Case1514Three A (lB A) c L Y) (h143 : Item143N A (lB A))
    {X : Subgroup G} (hX : X ∈ scriptQ A (lB A))
    (hXc : X ⊓ Subgroup.centralizer ({c} : Set G) = ⊥)
    {a : G} (haA : a ∈ A) (ha1 : a ≠ 1) (haz : a ∉ Subgroup.zpowers c) :
    X ⊓ Subgroup.centralizer ({a} : Set G) ≤
      pPrimeCoreOf 3 (Subgroup.centralizer ({a} : Set G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨-, hLcard, -, -, -, -, -, -⟩ := facts h hY hC
  set C : Subgroup G := Subgroup.centralizer ({a} : Set G) with hCdef
  set O : Subgroup G := pPrimeCoreOf 3 C with hOdef
  set OA : Subgroup G := pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G)) with hOAdef
  set P : Subgroup G := X ⊓ C with hPdef
  have hPleX : P ≤ X := by rw [hPdef]; exact inf_le_left
  have hPleC : P ≤ C := by rw [hPdef]; exact inf_le_right
  have hAC : A ≤ C := by
    intro α hα
    rw [Subgroup.mem_centralizer_iff]
    intro β hβ
    rw [Set.mem_singleton_iff] at hβ
    subst β
    exact (congrArg Subtype.val (h.toSec13Data.isElemAbelian.1.is_comm.comm ⟨α, hα⟩ ⟨a, haA⟩)).symm
  have hA3 : IsPGroup 3 A := fun x =>
    ⟨1, Subtype.ext (by simpa using h.toSec13Data.isElemAbelian.2 x x.2)⟩
  have hAP : A ≤ Subgroup.normalizer (P : Set G) :=
    CFSG.RankThree.PartTwo.Late.le_normalizer_inf hX.1.2.2
      (hAC.trans Subgroup.le_normalizer)
  have hP3 : ¬ 3 ∣ Nat.card P := by
    have hX3 : ¬ 3 ∣ Nat.card X :=
      (isPiSubgroup_piCompl_iff Nat.prime_three X).mp hX.1.2.1
    intro h3
    exact hX3 (h3.trans (Subgroup.card_dvd_of_le hPleX))
  have hPmem : P ∈ scriptQ A (lB A) := mem_scriptQ_of_le hX hPleX hAP
  have hPdelta : P ≤ delta A (lB A) C := le_delta hPmem hPleC
  have hPinv : P ∈ invariantPiSubgroups (delta A (lB A) C) A (piCompl 3) :=
    ⟨hPdelta, (isPiSubgroup_piCompl_iff Nat.prime_three P).mpr hP3, hAP⟩
  obtain ⟨M, hMmax, hPM⟩ := exists_le_mem_maxInvariantPiSubgroups hPinv
  have hΩ : Subgroup.zpowers a ∉ omegaA A := by
    rw [hC.2.2.2.1]
    intro hmem
    rw [Set.mem_singleton_iff] at hmem
    exact haz (hmem ▸ Subgroup.mem_zpowers a)
  obtain ⟨-, hdich⟩ := h143 a haA ha1 hΩ M hMmax
  have hdelta : delta A (lB A) C = O ⊔ OA := by
    rcases hdich with h | ⟨b, d, Lb, hbΩ, hLb, ⟨φJ⟩, hdA, hd1, hdc, hab, X', hdeltaX, -, -⟩
    · simpa [hCdef, hOdef, hOAdef] using h
    · exfalso
      have hzw : Subgroup.zpowers b = Subgroup.zpowers c := by
        rw [hC.2.2.2.1] at hbΩ
        simpa using hbΩ
      have hLbTheta : Lb ∈ thetaComponentsAt 3 c := by
        have h : Lb ∈ lA A c := by
          rwa [Sec13.lA_congr hzw] at hLb
        exact h.1
      have hLbL : Lb = L :=
        (h.chosen136.2 c h.zpowers_mem_omegaA L h.mem_lA).2 Lb hLbTheta
          (three_dvd_card_of_mem_lA h hbΩ hLb)
      subst Lb
      have hdvd : Nat.card (↥L ⧸ aschbacherSolvableCore 3 ↥L) ∣ Nat.card L :=
        Subgroup.card_quotient_dvd_card _
      have hquot : Nat.card (↥L ⧸ aschbacherSolvableCore 3 ↥L) = 604800 := by
        rw [Nat.card_congr φJ.toEquiv, KFacts.KS14.card_nativeJ2]
      rw [hquot, hLcard] at hdvd
      norm_num at hdvd
  have hCAc : Subgroup.centralizer (A : Set G) ≤ C :=
    Subgroup.centralizer_le (Set.singleton_subset_iff.mpr haA)
  have hOleC : O ≤ C := by rw [hOdef]; exact pPrimeCoreOf_le 3 C
  have hOAleC : OA ≤ C := by rw [hOAdef]; exact (pPrimeCoreOf_le 3 _).trans hCAc
  have hdeltaA : ⁅delta A (lB A) C, A⁆ ≤ O := by
    refine Subgroup.commutator_le.mpr fun y hy α hα => ?_
    have hy' : y ∈ O ⊔ OA := by rwa [hdelta] at hy
    have hyC : y ∈ C := (sup_le hOleC hOAleC) hy'
    have hySup : (⟨y, hyC⟩ : ↥C) ∈ O.subgroupOf C ⊔ OA.subgroupOf C := by
      rw [← Subgroup.subgroupOf_sup hOleC hOAleC]
      exact Subgroup.mem_subgroupOf.mpr hy'
    have hOn : (O.subgroupOf C).Normal := by
      rw [Subgroup.normal_subgroupOf_iff_le_normalizer hOleC, hOdef]
      exact le_normalizer_pPrimeCoreOf 3 C
    haveI := hOn
    obtain ⟨o, ho, x, hx, hox⟩ := Subgroup.mem_sup_of_normal_left.mp hySup
    have hoO : (o : G) ∈ O := Subgroup.mem_subgroupOf.mp ho
    have hxOA : (x : G) ∈ OA := Subgroup.mem_subgroupOf.mp hx
    have hxα : (x : G) * α = α * (x : G) :=
      (Subgroup.mem_centralizer_iff.mp (pPrimeCoreOf_le 3 _ hxOA) α hα).symm
    have hαN : α ∈ Subgroup.normalizer (O : Set G) :=
      le_normalizer_pPrimeCoreOf 3 C (hAC hα)
    have hoα : (o : G) * α * (o : G)⁻¹ * α⁻¹ ∈ O := by
      have h2 : α * (o : G) * α⁻¹ * (o : G)⁻¹ ∈ O :=
        O.mul_mem ((Subgroup.mem_normalizer_iff.mp hαN o).mp hoO) (O.inv_mem hoO)
      have := O.inv_mem h2
      simpa only [mul_inv_rev, inv_inv, mul_assoc] using this
    have hcomm : ⁅y, α⁆ = ⁅(o : G), α⁆ := by
      have hoxG : (o : G) * (x : G) = y := congrArg Subtype.val hox
      rw [← hoxG, commutatorElement_def, commutatorElement_def]
      calc (o : G) * (x : G) * α * ((o : G) * (x : G))⁻¹ * α⁻¹ =
            (o : G) * ((x : G) * α * (x : G)⁻¹) * (o : G)⁻¹ * α⁻¹ := by group
        _ = (o : G) * α * (o : G)⁻¹ * α⁻¹ := by rw [hxα]; group
    rw [hcomm]
    exact hoα
  have hfac :=
    CFSG.RankThreeEvenClassification.Helpers.coprime_commutator_centralizer_factorization
      3 Nat.prime_three A P hA3 hP3 hAP
  have hPCbot' : P ⊓ Subgroup.centralizer (A : Set G) = ⊥ := by
    rw [← le_bot_iff]
    have hCAc : Subgroup.centralizer (A : Set G) ≤ Subgroup.centralizer ({c} : Set G) :=
      Subgroup.centralizer_le (Set.singleton_subset_iff.mpr h.toSec13Data.mem_A)
    exact (le_inf (inf_le_left.trans hPleX) (inf_le_right.trans hCAc)).trans
      (le_of_eq hXc)
  have hPleO : P ≤ O := by
    rw [hfac, hPCbot', sup_bot_eq]
    exact (Subgroup.commutator_mono hPdelta le_rfl).trans hdeltaA
  simpa [hPdef, hOdef, hCdef] using hPleO

theorem map_conj_pCoreOf_inf_centralizer_c_eq_bot (h : Sec15R G A c L)
    (hY : Y ∈ scriptY0Star A (lB A)) (hC : Case1514Three A (lB A) c L Y) {w : G}
    (hwL : w ∈ L) :
    (CFSG.Open.pCoreOf 2 Y).map (MulAut.conj w).toMonoidHom ⊓
      Subgroup.centralizer ({c} : Set G) = ⊥ := by
  set Q : Subgroup G := CFSG.Open.pCoreOf 2 Y with hQdef
  have hwC : w ∈ Subgroup.centralizer ({c} : Set G) :=
    Sec14.le_centralizer_of_mem_thetaComponentsAt h.mem_lA.1 hwL
  have hz : (Subgroup.zpowers c).map (MulAut.conj w).toMonoidHom = Subgroup.zpowers c := by
    rw [MonoidHom.map_zpowers]
    congr 1
    change w * c * w⁻¹ = c
    rw [← Subgroup.mem_centralizer_iff.mp hwC c (by simp)]
    group
  have hCeq : Subgroup.centralizer ({c} : Set G) =
      Subgroup.centralizer ((Subgroup.zpowers c : Subgroup G) : Set G) := by
    rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
  have hmapC : (Subgroup.centralizer ({c} : Set G)).map
      (MulAut.conj w).toMonoidHom = Subgroup.centralizer ({c} : Set G) := by
    rw [hCeq, Sec14.map_conj_centralizer, hz]
  have hmapinf : Q.map (MulAut.conj w).toMonoidHom ⊓ Subgroup.centralizer ({c} : Set G) =
      (Q ⊓ Subgroup.centralizer ({c} : Set G)).map (MulAut.conj w).toMonoidHom := by
    rw [Subgroup.map_inf _ _ _ (MulAut.conj w).injective, hmapC]
  rw [hmapinf, pCoreOf_inf_centralizer_c_eq_bot h hY hC, Subgroup.map_bot]

theorem pCoreOf_le_pPrimeCoreOf (h : Sec15R G A c L) (hY : Y ∈ scriptY0Star A (lB A))
    (hC : Case1514Three A (lB A) c L Y) (h1444 : Item1444 A (lB A))
    (h146 : Item146 A (lB A)) (h143 : Item143N A (lB A)) {a : G} (haA : a ∈ A)
    (ha1 : a ≠ 1) (haz : a ∉ Subgroup.zpowers c) :
    CFSG.Open.pCoreOf 2 Y ⊓ Subgroup.centralizer ({a} : Set G) ≤
      pPrimeCoreOf 3 (Subgroup.centralizer ({a} : Set G)) :=
  le_pPrimeCoreOf h hY hC h143 (pCoreOf_mem_scriptQ h hY hC h1444 h146)
    (pCoreOf_inf_centralizer_c_eq_bot h hY hC) haA ha1 haz

theorem map_conj_pCoreOf_le_pPrimeCoreOf (h : Sec15R G A c L)
    (hY : Y ∈ scriptY0Star A (lB A)) (hC : Case1514Three A (lB A) c L Y)
    (h1444 : Item1444 A (lB A)) (h146 : Item146 A (lB A)) (h143 : Item143N A (lB A))
    {w a : G} (hwA : w ∈ Subgroup.normalizer (A : Set G)) (hwL : w ∈ L) (haA : a ∈ A)
    (ha1 : a ≠ 1) (haz : a ∉ Subgroup.zpowers c) :
    (CFSG.Open.pCoreOf 2 Y).map (MulAut.conj w).toMonoidHom ⊓
        Subgroup.centralizer ({a} : Set G) ≤
      pPrimeCoreOf 3 (Subgroup.centralizer ({a} : Set G)) := by
  have hQmem : CFSG.Open.pCoreOf 2 Y ∈ scriptQ A (lB A) :=
    pCoreOf_mem_scriptQ h hY hC h1444 h146
  have hQpi : CFSG.Open.pCoreOf 2 Y ∈ scriptQPi A (lB A) ⊤ (piCompl 3) :=
    ⟨⟨hQmem, le_top⟩, hQmem.1.2.1⟩
  have hQwpi := Sec17.HeadProof.map_conj_mem_scriptQPi hwA hQpi
  rw [Subgroup.map_top] at hQwpi
  exact le_pPrimeCoreOf h hY hC h143 hQwpi.1.1
    (map_conj_pCoreOf_inf_centralizer_c_eq_bot h hY hC hwL) haA ha1 haz

theorem exists_x (h : Sec15R G A c L) (hY : Y ∈ scriptY0Star A (lB A))
    (hC : Case1514Three A (lB A) c L Y) (h1444 : Item1444 A (lB A))
    (h146 : Item146 A (lB A)) (h143 : Item143N A (lB A)) {w a : G}
    (hwA : w ∈ Subgroup.normalizer (A : Set G)) (hwL : w ∈ L) (haA : a ∈ A)
    (ha1 : a ≠ 1) (haz : a ∉ Subgroup.zpowers c) :
    ∃ g ∈ xA A, IsPGroup 2 ↑((CFSG.Open.pCoreOf 2 Y ⊓
        Subgroup.centralizer ({a} : Set G)) ⊔
      (((CFSG.Open.pCoreOf 2 Y).map (MulAut.conj w).toMonoidHom ⊓
        Subgroup.centralizer ({a} : Set G)).map (MulAut.conj g).toMonoidHom)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set C : Subgroup G := Subgroup.centralizer ({a} : Set G) with hCdef
  set Q : Subgroup G := CFSG.Open.pCoreOf 2 Y with hQdef
  set Qw : Subgroup G := Q.map (MulAut.conj w).toMonoidHom with hQwdef
  set P1 : Subgroup G := Q ⊓ C with hP1def
  set P2 : Subgroup G := Qw ⊓ C with hP2def
  set D : Subgroup G := pPrimeCoreOf 3 C with hDdef
  have hQ2 : IsPGroup 2 Q := CFSG.LieType.BorelTits.pCoreOf_isPGroup (r := 2) Y
  have hQw2 : IsPGroup 2 Qw := hQ2.map _
  have hP12 : IsPGroup 2 P1 := by rw [hP1def]; exact hQ2.to_inf_left
  have hP22 : IsPGroup 2 P2 := by rw [hP2def]; exact hQw2.to_inf_left
  have hP1D : P1 ≤ D := pCoreOf_le_pPrimeCoreOf h hY hC h1444 h146 h143 haA ha1 haz
  have hP2D : P2 ≤ D :=
    map_conj_pCoreOf_le_pPrimeCoreOf h hY hC h1444 h146 h143 hwA hwL haA ha1 haz
  have hQmem : Q ∈ scriptQ A (lB A) := pCoreOf_mem_scriptQ h hY hC h1444 h146
  have hQpi : Q ∈ scriptQPi A (lB A) ⊤ (piCompl 3) :=
    ⟨⟨hQmem, le_top⟩, hQmem.1.2.1⟩
  have hQwpi := Sec17.HeadProof.map_conj_mem_scriptQPi hwA hQpi
  rw [Subgroup.map_top] at hQwpi
  have hQwmem : Qw ∈ scriptQ A (lB A) := hQwpi.1.1
  have hAC : A ≤ C := by
    intro α hα
    rw [Subgroup.mem_centralizer_iff]
    intro β hβ
    rw [Set.mem_singleton_iff] at hβ
    subst β
    exact (congrArg Subtype.val
      (h.toSec13Data.isElemAbelian.1.is_comm.comm ⟨α, hα⟩ ⟨a, haA⟩)).symm
  have hACnorm : A ≤ Subgroup.normalizer (C : Set G) := hAC.trans Subgroup.le_normalizer
  have hA3 : IsPGroup 3 A := fun x =>
    ⟨1, Subtype.ext (by simpa using h.toSec13Data.isElemAbelian.2 x x.2)⟩
  have hAD : A ≤ Subgroup.normalizer (D : Set G) := by
    rw [hDdef]
    exact hAC.trans (le_normalizer_pPrimeCoreOf 3 C)
  have hM : ¬ 3 ∣ Nat.card D := by
    rw [hDdef]
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).1
      (coprime_card_pPrimeCoreOf 3 C)
  have hAP1 : A ≤ Subgroup.normalizer (P1 : Set G) := by
    rw [hP1def]
    exact CFSG.RankThree.PartTwo.Late.le_normalizer_inf hQmem.1.2.2 hACnorm
  have hAP2 : A ≤ Subgroup.normalizer (P2 : Set G) := by
    rw [hP2def]
    exact CFSG.RankThree.PartTwo.Late.le_normalizer_inf hQwmem.1.2.2 hACnorm
  obtain ⟨S1, hS1, hP1S1, hAS1⟩ :=
    CFSG.Goldschmidt.G310.exists_invariant_sylow_containing (r := 3) (q := 2)
      Nat.prime_three Nat.prime_two hA3 hM hAD hP1D hP12 hAP1
  obtain ⟨S2, hS2, hP2S2, hAS2⟩ :=
    CFSG.Goldschmidt.G310.exists_invariant_sylow_containing (r := 3) (q := 2)
      Nat.prime_three Nat.prime_two hA3 hM hAD hP2D hP22 hAP2
  obtain ⟨c0, hc0, hS2conj⟩ :=
    CFSG.Goldschmidt.G310.exists_conj_of_invariant_sylows (r := 3) (q := 2)
      Nat.prime_three Nat.prime_two hA3 hM hAD hS1 hS2 hAS1 hAS2
  have hDX : D ⊓ Subgroup.centralizer (A : Set G) ≤ xA A := by
    have hCAc : Subgroup.centralizer (A : Set G) ≤ C :=
      Subgroup.centralizer_le (Set.singleton_subset_iff.mpr haA)
    refine Sec14.le_pPrimeCoreOf inf_le_right ?_ ?_
    · refine CFSG.RankThree.PartTwo.Late.le_normalizer_inf ?_ Subgroup.le_normalizer
      exact hCAc.trans (by rw [hDdef]; exact le_normalizer_pPrimeCoreOf 3 C)
    · exact Nat.Coprime.of_dvd_right (Subgroup.card_dvd_of_le inf_le_left)
        (coprime_card_pPrimeCoreOf 3 C)
  have hgX : c0⁻¹ ∈ xA A := by
    apply hDX
    exact ⟨D.inv_mem hc0.1,
      (Subgroup.centralizer (A : Set G)).inv_mem hc0.2⟩
  have hS2inv : S2.map (MulAut.conj c0⁻¹).toMonoidHom = S1 := by
    rw [hS2conj, Subgroup.map_map]
    have hcomp : (MulEquiv.toMonoidHom (MulAut.conj c0⁻¹)).comp
        (MulEquiv.toMonoidHom (MulAut.conj c0)) = MonoidHom.id G := by
      ext x
      simp [MulAut.conj_apply, mul_assoc]
    rw [hcomp, Subgroup.map_id]
  have hP2gS1 : P2.map (MulAut.conj c0⁻¹).toMonoidHom ≤ S1 :=
    (Subgroup.map_mono hP2S2).trans_eq hS2inv
  have hsup : P1 ⊔ P2.map (MulAut.conj c0⁻¹).toMonoidHom ≤ S1 :=
    sup_le hP1S1 hP2gS1
  exact ⟨c0⁻¹, hgX, hS1.2.1.to_le hsup⟩

end CFSG.RankThree.PartTwo.Sec16.Res163U35Facts
