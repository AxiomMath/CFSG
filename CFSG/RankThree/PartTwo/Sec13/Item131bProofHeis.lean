module

public import CFSG.RankThree.PartTwo.Sec13.Item136E
import CFSG.RankThree.PartTwo.Sec12.Item125Basic
import CFSG.RankThree.PartTwo.Sec19.O2Centralizer
import CFSG.RankThree.PartTwo.Sec19.Step1910O2Proof
import CFSG.RankThree.PartTwo.Sec6.Item612Plus
import CFSG.RankThree.PartTwo.KFacts.KS14HJBasic
import CFSG.LocalAnalysis.SectionRank.OddCover.DegreeThree
import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.RankThree.PartTwo.Sec12.Item124Bar
public import CFSG.RankThree.PartTwo.Sec13.Item13SetupAt

public section

namespace CFSG.RankThree.PartTwo.Sec13.Item131bProof

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

variable {G : Type} [Group G] [Finite G] {A L : Subgroup G} {c : G}

abbrev HBar (c : G) : Type :=
  Subgroup.normalizer (Subgroup.zpowers c : Set G) ⧸
    aschbacherSolvableCore 3 (Subgroup.normalizer (Subgroup.zpowers c : Set G))

abbrev HeisType (X : Type) [Group X] : Prop :=
  Sec4.IsSLThreePi X ∨ Sec4.IsTripleCover X (alternatingGroup (Fin 7)) ∨
    Sec4.IsTripleCover X CFSG.Blueprint.NativeSporadic.M22

theorem card_center_eq_three {X : Type} [Group X] (hty : HeisType X) :
    Nat.card (Subgroup.center X) = 3 := by
  rcases hty with h | h | h
  · exact Sec12.card_center_eq_three_of_isSLThreePi h
  · exact h.1
  · exact h.1

theorem type122_of {X : Type} [Group X] (hty : HeisType X) :
    Sec4.IsSLThreePi X ∨ Sec4.IsTripleCover X (alternatingGroup (Fin 6)) ∨
      Sec4.IsTripleCover X (alternatingGroup (Fin 7)) ∨
      Sec4.IsTripleCover X CFSG.Blueprint.NativeSporadic.M22 := by
  rcases hty with h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr h))

theorem eleven_dvd_card_M22 : 11 ∣ Nat.card CFSG.Blueprint.NativeSporadic.M22 := by
  have : Fact (Nat.Prime 11) := ⟨by norm_num⟩
  set a : Equiv.Perm (Fin 22) := List.formPerm [0, 12] * List.formPerm [1, 7] *
    List.formPerm [2, 15] * List.formPerm [3, 11] * List.formPerm [5, 21] *
    List.formPerm [6, 16] * List.formPerm [8, 9] * List.formPerm [10, 13] with ha
  set b : Equiv.Perm (Fin 22) := List.formPerm [0, 21, 2, 20] * List.formPerm [1, 17, 3, 12] *
    List.formPerm [4, 11] * List.formPerm [5, 10, 6, 14] * List.formPerm [7, 13, 19, 9] *
    List.formPerm [16, 18] with hb
  have haM : a ∈ CFSG.Blueprint.NativeSporadic.M22 :=
    Subgroup.subset_closure (Set.mem_insert _ _)
  have hbM : b ∈ CFSG.Blueprint.NativeSporadic.M22 :=
    Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
  have h11 : (a * b) ^ 11 = 1 := by rw [ha, hb]; decide +kernel
  have h1 : a * b ≠ 1 := by rw [ha, hb]; decide
  set x : CFSG.Blueprint.NativeSporadic.M22 := ⟨a * b, mul_mem haM hbM⟩ with hx
  have hx11 : x ^ 11 = 1 := Subtype.ext (by simpa [hx] using h11)
  have hx1 : x ≠ 1 := fun h => h1 (by simpa [hx] using congrArg Subtype.val h)
  rw [← orderOf_eq_prime hx11 hx1]
  exact orderOf_dvd_natCard x

theorem card_ne_of_isSLThreePi {X : Type} [Group X] (hX : Sec4.IsSLThreePi X) :
    Nat.card X ≠ 1080 := by
  obtain ⟨q, K, _, _, hcase⟩ := hX
  rcases hcase with ⟨hK, -, ⟨e⟩⟩ | ⟨hK, hq, ⟨e⟩⟩
  · rw [Nat.card_congr e.toEquiv, CFSG.SectionRank.OddCover.card_statedSL_three]
    set r := Nat.card K
    have hr : 2 ≤ r := Finite.one_lt_card
    rcases Nat.lt_or_ge r 3 with h2 | h3
    · have hr2 : r = 2 := by omega
      rw [hr2]
      norm_num
    · have h1 : 27 ≤ r ^ 3 := by
        calc 27 = 3 ^ 3 := by norm_num
          _ ≤ r ^ 3 := Nat.pow_le_pow_left h3 3
      have h2 : 8 ≤ r ^ 2 - 1 := by
        have : 9 ≤ r ^ 2 := by
          calc 9 = 3 ^ 2 := by norm_num
            _ ≤ r ^ 2 := Nat.pow_le_pow_left h3 2
        omega
      have h4 : 26 ≤ r ^ 3 - 1 := by omega
      have := Nat.mul_le_mul (Nat.mul_le_mul h1 h2) h4
      omega
  · have := Fintype.ofFinite K
    obtain ⟨n, hp, hn⟩ := FiniteField.card K (ringChar K)
    have : Fact (ringChar K).Prime := ⟨hp⟩
    have : CharP K (ringChar K) := ringChar.charP K
    have hnc : Nat.card K = ringChar K ^ (n : ℕ) := by rw [Nat.card_eq_fintype_card, hn]
    have hqd : q ∣ ringChar K ^ (n : ℕ) := ⟨q, by rw [← hnc, hK, sq]⟩
    obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow hp).mp hqd
    subst hm
    rw [Nat.card_congr e.toEquiv, CFSG.SectionRank.OddCover.card_statedSU_three hK]
    set r := ringChar K ^ m
    have hr : 2 ≤ r := by
      rcases Nat.lt_or_ge r 2 with h | h
      · interval_cases r <;> simp_all
      · exact h
    rcases Nat.lt_or_ge r 3 with h2 | h3
    · have hr2 : r = 2 := by omega
      rw [hr2]
      norm_num
    · have h1 : 27 ≤ r ^ 3 := by
        calc 27 = 3 ^ 3 := by norm_num
          _ ≤ r ^ 3 := Nat.pow_le_pow_left h3 3
      have h2 : 8 ≤ r ^ 2 - 1 := by
        have : 9 ≤ r ^ 2 := by
          calc 9 = 3 ^ 2 := by norm_num
            _ ≤ r ^ 2 := Nat.pow_le_pow_left h3 2
        omega
      have h4 : 28 ≤ r ^ 3 + 1 := by omega
      have := Nat.mul_le_mul (Nat.mul_le_mul h1 h2) h4
      omega

theorem not_isTripleCover_six {X : Type} [Group X] (hty : HeisType X)
    (h6 : Sec4.IsTripleCover X (alternatingGroup (Fin 6))) : False := by
  have hcard : Nat.card X = 1080 := KFacts.KS14.card_eq_of_isExtOf_alternating_six h6.isExtOf
  obtain ⟨-, ⟨e6⟩⟩ := h6
  rcases hty with hSL | ⟨-, ⟨e7⟩⟩ | ⟨-, ⟨eM⟩⟩
  · exact card_ne_of_isSLThreePi hSL hcard
  · have h := Nat.card_congr (e7.symm.trans e6).toEquiv
    rw [nat_card_alternatingGroup, nat_card_alternatingGroup, Nat.card_eq_fintype_card,
      Nat.card_eq_fintype_card, Fintype.card_fin, Fintype.card_fin] at h
    revert h
    decide
  · have h := Nat.card_congr (eM.symm.trans e6).toEquiv
    have h6 : Nat.card (alternatingGroup (Fin 6)) = 360 := by
      rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
      rfl
    rw [h6] at h
    have h11 := eleven_dvd_card_M22
    rw [h] at h11
    revert h11
    decide

theorem no_E27_le (hD : Sec13Data G A c L) (hty : HeisType (L ⧸ aschbacherSolvableCore 3 L))
    {D : Subgroup G} (hDe : CFSG.Assembly.IsElemAbelian 3 D) (hD27 : Nat.card D = 27)
    (hDC : D ≤ Sec4.thetaQuotCentralizer L) : False := by
  have hFE : partTwoF G = partTwoE G :=
    (hD.toTheoremFourHyp.partTwoF_eq_partTwoE hD.partTwoS_eq).1
  have hperf : commutator (L ⧸ aschbacherSolvableCore 3 L) = ⊤ := by
    have h1 := (Sec12.isQuasisimple_thetaQuot_of_mem hD.mem_thetaComponentsAt).1
    rwa [Group.isPerfect_def] at h1
  exact Sec12.false_of_E27_le_thetaQuotCentralizer hFE hperf (card_center_eq_three hty)
    (KFacts.two_dvd_card_of_item122_type (type122_of hty)) hDe hD27 hDC

omit [Finite G] in
theorem isElemAbelian_of_le {E S : Subgroup G} (hE : CFSG.Assembly.IsElemAbelian 3 E)
    (hSE : S ≤ E) : CFSG.Assembly.IsElemAbelian 3 S := CFSG.Open.IsElemAbelian.mono hE hSE

theorem nine_le_card {S : Subgroup G} (hexp : ∀ x ∈ S, x ^ 3 = 1) (hS : ¬ IsCyclic S) :
    9 ≤ Nat.card S := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hp : IsPGroup 3 S := fun g => ⟨1, Subtype.ext (by simpa using hexp g g.2)⟩
  obtain ⟨n, hn⟩ := hp.exists_card_eq
  by_contra hlt
  have hn1 : n ≤ 1 := by
    by_contra h
    have : 3 ^ 2 ≤ 3 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  interval_cases n
  · have : Subsingleton S := (Nat.card_eq_one_iff_unique.mp (by simpa using hn)).1
    exact hS isCyclic_of_subsingleton
  · exact hS (isCyclic_of_prime_card (p := 3) (by simpa using hn))

theorem e_facts (hD : Sec13Data G A c L) (hty : HeisType (L ⧸ aschbacherSolvableCore 3 L))
    (hcL : c ∈ L) {E : Subgroup G} (hEle : E ≤ L ⊔ A) (hEe : CFSG.Assembly.IsElemAbelian 3 E)
    (hE27 : Nat.card E = 27) (hEC : ¬ IsCyclic (E ⊓ Sec4.thetaQuotCentralizer L : Subgroup G))
    (hEL : ¬ IsCyclic (E ⊓ L : Subgroup G)) :
    c ∈ E ∧ Nat.card (E ⊓ Sec4.thetaQuotCentralizer L : Subgroup G) = 9 ∧
      Nat.card (E ⊓ L : Subgroup G) = 9 ∧
      (E ⊓ Sec4.thetaQuotCentralizer L) ⊔ (E ⊓ L) = E := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hE3 : ∀ x ∈ E, x ^ 3 = 1 := hEe.2
  have hEcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hEe.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hEc : E ≤ Subgroup.centralizer ({c} : Set G) :=
    hEle.trans (sup_le hD.le_centralizer hD.A_le_centralizer)
  have hcC : c ∈ Sec4.thetaQuotCentralizer L :=
    Sec12.mem_thetaQuotCentralizer_of_central hcL hD.le_centralizer
  have hZ3 := card_center_eq_three hty
  have hdvd : ∀ S : Subgroup G, S ≤ E → Nat.card S ∣ 3 ^ 3 := fun S hS => by
    rw [show (3 : ℕ) ^ 3 = 27 by norm_num, ← hE27]
    exact Subgroup.card_dvd_of_le hS
  set C := E ⊓ Sec4.thetaQuotCentralizer L with hCdef
  have hC9 : Nat.card C = 9 := by
    have h9 := nine_le_card (S := C) (fun x hx => hE3 x hx.1) hEC
    obtain ⟨k, hk3, hk⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp (hdvd C inf_le_left)
    interval_cases k
    · rw [hk] at h9; norm_num at h9
    · rw [hk] at h9; norm_num at h9
    · rw [hk]; norm_num
    · exfalso
      have hCE : C = E := Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [hk, hE27]; norm_num)
      exact no_E27_le hD hty hEe hE27 (hCE ▸ inf_le_right)
  have hcE : c ∈ E := by
    by_contra hcE
    have hc3 : c ^ 3 = 1 := by rw [← hD.orderOf_eq]; exact pow_orderOf_eq_one c
    have hCe : CFSG.Assembly.IsElemAbelian 3 C := isElemAbelian_of_le hEe inf_le_left
    have hDe := Sec15.isElemAbelian_sup_zpowers hCe hc3 fun e he =>
      (Subgroup.mem_centralizer_singleton_iff.mp (hEc he.1))
    have hcN : Subgroup.zpowers c ≤ Subgroup.normalizer (C : Set G) := by
      rw [Subgroup.zpowers_le]
      refine Subgroup.mem_normalizer_fintype fun e he => ?_
      have hce : c * e = e * c := (Subgroup.mem_centralizer_singleton_iff.mp (hEc he.1)).symm
      rw [hce, mul_inv_cancel_right]
      exact he
    have hcard := Sec6.card_sup_mul_card_inf hcN
    have hbot : Subgroup.zpowers c ⊓ C = ⊥ := by
      rw [inf_comm]
      exact Sec12.inf_zpowers_eq_bot_of_not_mem hD.orderOf_eq fun h => hcE h.1
    rw [hbot, Subgroup.card_bot, mul_one, Nat.card_zpowers, hD.orderOf_eq, hC9] at hcard
    rw [sup_comm] at hcard
    exact no_E27_le hD hty hDe (by rw [hcard]) (sup_le inf_le_right (Subgroup.zpowers_le.mpr hcC))
  have hCL : ∀ S : Subgroup G, S ≤ C → S ≤ L → Nat.card S ≤ 3 := fun S hSC hSL => by
    have hS3 : IsPGroup 3 S := fun g => ⟨1, Subtype.ext (by simpa using hE3 g (hSC g.2).1)⟩
    have h := Sec19.Step1910O2Proof.card_le_card_center_thetaQuot hS3 hSL
      (hSC.trans inf_le_right)
    rwa [hZ3] at h
  have hEL9 : Nat.card (E ⊓ L : Subgroup G) = 9 := by
    have h9 := nine_le_card (S := E ⊓ L) (fun x hx => hE3 x hx.1) hEL
    obtain ⟨k, hk3, hk⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp (hdvd _ inf_le_left)
    interval_cases k
    · rw [hk] at h9; norm_num at h9
    · rw [hk] at h9; norm_num at h9
    · rw [hk]; norm_num
    · exfalso
      have hEL' : E ⊓ L = E :=
        Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [hk, hE27]; norm_num)
      have hEL'' : E ≤ L := calc E = E ⊓ L := hEL'.symm
        _ ≤ L := inf_le_right
      have h := hCL C le_rfl (inf_le_left.trans hEL'')
      omega
  refine ⟨hcE, hC9, hEL9, ?_⟩
  have hTN : C ≤ Subgroup.normalizer ((E ⊓ L : Subgroup G) : Set G) := fun t ht =>
    Subgroup.mem_normalizer_fintype fun b hb => by
      rw [hEcomm t ht.1 b hb.1, mul_inv_cancel_right]
      exact hb
  refine Subgroup.eq_of_le_of_card_ge (sup_le inf_le_left inf_le_left) ?_
  have h1 := Sec6.card_sup_mul_card_inf hTN
  have h2 : Nat.card (C ⊓ (E ⊓ L) : Subgroup G) ≤ 3 :=
    hCL _ inf_le_left (inf_le_right.trans inf_le_right)
  have hpos : 0 < Nat.card (C ⊓ (E ⊓ L) : Subgroup G) := Nat.card_pos
  rw [hC9, hEL9] at h1
  rw [hE27]
  nlinarith

theorem range_aBarHom_inf_lBar (hD : Sec13Data G A c L)
    (hH : Sec4.IsHeisCentral (lBarA c L A) (L ⧸ aschbacherSolvableCore 3 L)) (hcL : c ∈ L)
    (hZ3 : Nat.card (Subgroup.center (L ⧸ aschbacherSolvableCore 3 L)) = 3) :
    (aBarHom hD).range ⊓ (Sec12.lBar c L).subgroupOf (lBarA c L A) =
      Subgroup.zpowers (mkC (L := L) hD.mem_A) := by
  obtain ⟨U, hU, hUΛ, -, -⟩ := isHeisCentral_facts hD hH
  set Λ := (Sec12.lBar c L).subgroupOf (lBarA c L A) with hΛ
  set Ab := (aBarHom hD).range with hAb
  set N := Subgroup.centralizer (Λ : Set (lBarA c L A)) with hN
  have hUN : U ≤ N := fun u hu =>
    Subgroup.mem_centralizer_iff.mpr fun v hv => (hUΛ u hu v hv).symm
  have hU27 : Nat.card U = 27 := hU.2.1
  have hΛn : Λ.Normal := lBar_normal hD
  have hNΛ : Nat.card (N ⊓ Λ : Subgroup (lBarA c L A)) ≤ 3 := by
    have hle : (N ⊓ Λ).subgroupOf Λ ≤ Subgroup.center Λ := by
      intro x hx
      rw [Subgroup.mem_subgroupOf] at hx
      exact Subgroup.mem_center_iff.mpr fun y =>
        Subtype.ext ((Subgroup.mem_centralizer_iff.mp hx.1) y y.2)
    have h1 : Nat.card ((N ⊓ Λ).subgroupOf Λ) = Nat.card (N ⊓ Λ : Subgroup (lBarA c L A)) := by
      rw [← Subgroup.card_map_of_injective Λ.subtype_injective, Subgroup.subgroupOf_map_subtype,
        inf_assoc, inf_idem]
    calc Nat.card (N ⊓ Λ : Subgroup (lBarA c L A)) = Nat.card ((N ⊓ Λ).subgroupOf Λ) := h1.symm
      _ ≤ Nat.card (Subgroup.center Λ) := Subgroup.card_le_of_le hle
      _ = 3 := by rw [card_center_lBar hD, hZ3]
  have hall : ∀ x : lBarA c L A, x ∈ Subgroup.normalizer (Λ : Set (lBarA c L A)) := fun x =>
    Subgroup.mem_normalizer_iff.mpr fun y => ⟨fun hy => hΛn.conj_mem y hy x, fun hy => by
      have h1 := hΛn.conj_mem _ hy x⁻¹
      simpa [mul_assoc] using h1⟩
  have hNnorm : N ≤ Subgroup.normalizer (Λ : Set (lBarA c L A)) := fun x _ => hall x
  have hAbnorm : Ab ≤ Subgroup.normalizer (Λ : Set (lBarA c L A)) := fun x _ => hall x
  have h1 := Sec6.card_sup_mul_card_inf hNnorm
  have h2 := Sec6.card_sup_mul_card_inf hAbnorm
  have hAbΛ : Ab ⊔ Λ = ⊤ := by
    rw [sup_comm]
    exact lBar_sup_range_aBarHom hD
  have hle : Nat.card (N ⊔ Λ : Subgroup (lBarA c L A)) ≤ Nat.card (Ab ⊔ Λ : Subgroup _) := by
    rw [hAbΛ]
    exact Subgroup.card_le_of_le le_top
  have hAb27 : Nat.card Ab = 27 := by
    rw [hAb, ← Nat.card_congr (MonoidHom.ofInjective (aBarHom_injective hD)).toEquiv,
      hD.card_eq]
  have hN27 : 27 ≤ Nat.card N := hU27 ▸ Subgroup.card_le_of_le hUN
  have hΛpos : 0 < Nat.card Λ := Nat.card_pos
  have hkey : Nat.card (Ab ⊓ Λ : Subgroup (lBarA c L A)) ≤ 3 := by
    set x := Nat.card (Ab ⊓ Λ : Subgroup (lBarA c L A))
    set l := Nat.card Λ
    have h3 : Nat.card N * l ≤ Nat.card (Ab ⊔ Λ : Subgroup _) * 3 := by
      rw [← h1]
      exact Nat.mul_le_mul hle hNΛ
    have h4 : 27 * l * x ≤ 81 * l := by
      calc 27 * l * x ≤ Nat.card N * l * x := by
            exact Nat.mul_le_mul (Nat.mul_le_mul hN27 le_rfl) le_rfl
        _ ≤ Nat.card (Ab ⊔ Λ : Subgroup _) * 3 * x := Nat.mul_le_mul h3 le_rfl
        _ = 3 * (Nat.card (Ab ⊔ Λ : Subgroup _) * x) := by ring
        _ = 81 * l := by rw [h2, hAb27]; ring
    have h5 : l * (27 * x) ≤ l * 81 := by nlinarith
    have h6 := Nat.le_of_mul_le_mul_left h5 hΛpos
    omega
  set z := mkC (L := L) hD.mem_A with hz
  have hzAb : z ∈ Ab := ⟨⟨c, hD.mem_A⟩, (mkC_eq_aBarHom hD).symm⟩
  have hzΛ : z ∈ Λ := mkC_mem_lBar hD hcL
  have hzeq : Subgroup.zpowers z = Ab ⊓ Λ := by
    refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr ⟨hzAb, hzΛ⟩) ?_
    rw [Nat.card_zpowers, orderOf_mkC hD]
    exact hkey
  exact hzeq.symm

theorem inf_le_zpowers (hD : Sec13Data G A c L)
    (hH : Sec4.IsHeisCentral (lBarA c L A) (L ⧸ aschbacherSolvableCore 3 L)) (hcL : c ∈ L)
    (hZ3 : Nat.card (Subgroup.center (L ⧸ aschbacherSolvableCore 3 L)) = 3) :
    A ⊓ L ≤ Subgroup.zpowers c := by
  have hzeq := (range_aBarHom_inf_lBar hD hH hcL hZ3).symm
  intro a ha
  set a' : A := ⟨a, ha.1⟩ with ha'
  have hmem : aBarHom hD a' ∈ (aBarHom hD).range ⊓ (Sec12.lBar c L).subgroupOf (lBarA c L A) := by
    refine ⟨⟨a', rfl⟩, Subgroup.mem_subgroupOf.mpr ?_⟩
    rw [aBarHom_apply]
    exact ⟨⟨a, hD.A_le_normalizer_zpowers ha.1⟩, Subgroup.mem_subgroupOf.mpr ha.2, rfl⟩
  rw [← hzeq] at hmem
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
  have hk' : aBarHom hD ((⟨c, hD.mem_A⟩ : A) ^ k) = aBarHom hD a' := by
    rw [map_zpow, ← mkC_eq_aBarHom hD, hk]
  have heq := aBarHom_injective hD hk'
  have : a = c ^ k := by
    have h := congrArg Subtype.val heq
    simpa [ha'] using h.symm
  rw [this]
  exact Subgroup.zpow_mem_zpowers c k

theorem le_lcBar (hD : Sec13Data G A c L)
    (hH : Sec4.IsHeisCentral (lBarA c L A) (L ⧸ aschbacherSolvableCore 3 L)) :
    A ≤ Sec12.lcBar c L := by
  obtain ⟨U, -, hUΛ, hUV, -⟩ := isHeisCentral_facts hD hH
  set Λ := (Sec12.lBar c L).subgroupOf (lBarA c L A) with hΛ
  intro a ha
  refine ⟨⟨a, hD.A_le_normalizer_zpowers ha⟩, ?_, rfl⟩
  change QuotientGroup.mk' _ ⟨a, hD.A_le_normalizer_zpowers ha⟩ ∈
    Sec12.lBar c L ⊔ Subgroup.centralizer (Sec12.lBar c L : Set _)
  have hmem : aBarHom hD ⟨a, ha⟩ ∈ U ⊔ Λ := by
    rw [hUV]
    exact Subgroup.mem_top _
  have hmap := Subgroup.mem_map_of_mem (lBarA c L A).subtype hmem
  rw [Subgroup.coe_subtype, aBarHom_apply, Subgroup.map_sup] at hmap
  refine (sup_le ?_ ?_ : _ ≤ Sec12.lBar c L ⊔ Subgroup.centralizer (Sec12.lBar c L : Set _))
    hmap
  · rintro _ ⟨u, hu, rfl⟩
    refine Subgroup.mem_sup_right (Subgroup.mem_centralizer_iff.mpr fun x hx => ?_)
    have h := hUΛ u hu ⟨x, lBar_le_lBarA hx⟩ (Subgroup.mem_subgroupOf.mpr hx)
    exact (congrArg Subtype.val h).symm
  · rintro _ ⟨v, hv, rfl⟩
    exact Subgroup.mem_sup_left (Subgroup.mem_subgroupOf.mp hv)

theorem inf_thetaQuotCentralizer_eq (hD : Sec13Data G A c L) :
    A ⊓ Sec4.thetaQuotCentralizer L = Subgroup.zpowers c := by
  have hsc := hD.sectionCentralizer_eq
  rw [sectionCentralizer_eq_inf hD.le_normalizer] at hsc
  exact SetLike.coe_injective hsc

theorem le_normalizer_of_heis (hD : Sec13Data G A c L)
    (hAL : A ⊓ L ≤ Subgroup.zpowers c) {E : Subgroup G}
    (hEW : E ≤ Subgroup.normalizer (A : Set G)) (hcE : c ∈ E)
    (hsup : (E ⊓ Sec4.thetaQuotCentralizer L) ⊔ (E ⊓ L) = E) :
    A ≤ Subgroup.normalizer (E : Set G) := by
  have hAC := inf_thetaQuotCentralizer_eq hD
  have hcE' : Subgroup.zpowers c ≤ E := Subgroup.zpowers_le.mpr hcE
  intro a ha
  have haL : a ∈ Subgroup.normalizer (L : Set G) := hD.le_normalizer ha
  have hcomm_mem : ∀ e ∈ E, a * e * a⁻¹ * e⁻¹ ∈ A := fun e he => by
    have h1 : e * a⁻¹ * e⁻¹ ∈ A := (Subgroup.mem_normalizer_iff.mp (hEW he) _).mp (inv_mem ha)
    have h2 : a * e * a⁻¹ * e⁻¹ = a * (e * a⁻¹ * e⁻¹) := by group
    rw [h2]
    exact mul_mem ha h1
  have hsub : E ≤ E.comap (MulAut.conj a).toMonoidHom := by
    conv_lhs => rw [← hsup]
    refine sup_le (fun d hd => ?_) (fun l hl => ?_)
    · obtain ⟨hd1, hd2⟩ := Subgroup.mem_inf.mp hd
      have hx : a * d * a⁻¹ * d⁻¹ ∈ A ⊓ Sec4.thetaQuotCentralizer L :=
        Subgroup.mem_inf.mpr ⟨hcomm_mem d hd1,
          mul_mem (Sec12.conj_mem_thetaQuotCentralizer haL hd2) (inv_mem hd2)⟩
      rw [hAC] at hx
      have h := mul_mem (hcE' hx) hd1
      change a * d * a⁻¹ ∈ E
      simpa [mul_assoc] using h
    · obtain ⟨hl1, hl2⟩ := Subgroup.mem_inf.mp hl
      have hlL : a * l * a⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp haL l).mp hl2
      have hx : a * l * a⁻¹ * l⁻¹ ∈ A ⊓ L :=
        Subgroup.mem_inf.mpr ⟨hcomm_mem l hl1, mul_mem hlL (inv_mem hl2)⟩
      have h := mul_mem (hcE' (hAL hx)) hl1
      change a * l * a⁻¹ ∈ E
      simpa [mul_assoc] using h
  exact Subgroup.mem_normalizer_fintype fun e he => hsub he

theorem sec12StdBar_of_heis (hD : Sec13Data G A c L) (hcL : c ∈ L) {E : Subgroup G}
    (hEe : CFSG.Assembly.IsElemAbelian 3 E) (hE27 : Nat.card E = 27) (hcE : c ∈ E)
    (hC9 : Nat.card (E ⊓ Sec4.thetaQuotCentralizer L : Subgroup G) = 9)
    (hsup : (E ⊓ Sec4.thetaQuotCentralizer L) ⊔ (E ⊓ L) = E)
    (hAN : A ≤ Subgroup.normalizer (E : Set G)) : Sec12.Sec12StdBar G E c L := by
  have hst := hD.toPartTwoStanding
  have hS := hD.partTwoS_eq
  have hFE : partTwoF G = partTwoE G :=
    (hD.toTheoremFourHyp.partTwoF_eq_partTwoE hS).1
  have hAC := inf_thetaQuotCentralizer_eq hD
  refine ⟨hst, hFE, ⟨hEe, hE27⟩, hcE, hD.ne_one, hD.mem_thetaComponentsAt, hcL, hC9, hsup, ?_⟩
  set H := Subgroup.normalizer (E : Set G) ⊓ Subgroup.normalizer (Subgroup.zpowers c : Set G)
    with hH
  have hAH : A ≤ H := fun a ha => ⟨hAN ha, hD.A_le_normalizer_zpowers ha⟩
  have hA3 : IsPGroup 3 A := fun g => ⟨1, Subtype.ext (by simpa using hD.isElemAbelian.2 g g.2)⟩
  obtain ⟨Q, hQ⟩ := (hA3.comap_subtype (K := H)).exists_le_sylow
  refine ⟨(Q : Subgroup H).map H.subtype, ⟨Q, rfl⟩, fun hle => ?_⟩
  have hAP : ∀ a ∈ A, a ∈ (Q : Subgroup H).map H.subtype := fun a ha =>
    ⟨⟨a, hAH ha⟩, hQ (Subgroup.mem_comap.mpr ha), rfl⟩
  have hDc : E ⊓ Sec4.thetaQuotCentralizer L ≤ Subgroup.zpowers c := by
    intro d hd
    obtain ⟨z, hz, hzd⟩ := hle hd
    have hdA : d ∈ A := Sec19.mem_of_le_centralizer hst hS hD.mem_partTwoE (hEe.2 d hd.1)
      fun a ha => by
        have h1 := Subgroup.mem_center_iff.mp hz ⟨a, hAP a ha⟩
        rw [Subgroup.mem_centralizer_singleton_iff, ← hzd]
        exact (congrArg Subtype.val h1)
    rw [← hAC]
    exact ⟨hdA, hd.2⟩
  have h1 := Subgroup.card_le_of_le hDc
  rw [Nat.card_zpowers, hD.orderOf_eq, hC9] at h1
  omega

theorem isElemAbelian_zpowers {H : Type*} [Group H] {x : H} (hx : x ^ 3 = 1) :
    CFSG.Assembly.IsElemAbelian 3 (Subgroup.zpowers x) := CFSG.Open.isElemAbelian_zpowers hx


theorem mk_mem_normalizer_lBar {K : Subgroup G}
    {g : Subgroup.normalizer (Subgroup.zpowers c : Set G)}
    (hg : (g : G) ∈ Subgroup.normalizer (K : Set G)) :
    QuotientGroup.mk' (aschbacherSolvableCore 3
        (Subgroup.normalizer (Subgroup.zpowers c : Set G))) g ∈
      Subgroup.normalizer ((Sec12.lBar c K : Subgroup _) : Set (Subgroup.normalizer
        (Subgroup.zpowers c : Set G) ⧸ aschbacherSolvableCore 3
          (Subgroup.normalizer (Subgroup.zpowers c : Set G)))) := by
  refine Subgroup.mem_normalizer_fintype fun y hy => ?_
  obtain ⟨k, hk, rfl⟩ := hy
  refine ⟨g * k * g⁻¹, Subgroup.mem_subgroupOf.mpr ?_, by simp⟩
  have := (Subgroup.mem_normalizer_iff.mp hg k).mp (Subgroup.mem_subgroupOf.mp hk)
  simpa using this

end CFSG.RankThree.PartTwo.Sec13.Item131bProof
