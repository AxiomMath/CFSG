module

public import CFSG.RankThree.PartTwo.Sec14.Ronan148NCentTools
public import CFSG.RankThree.PartTwo.Sec14.Item148PointProofPGL
public import CFSG.RankThree.PartTwo.Sec4.StatementsSporadic
import CFSG.RankThree.PartTwo.Sec14.Item147
import CFSG.RankThree.PartTwo.Sec14.Item148MainProofHyp
import CFSG.RankThree.PartTwo.Sec14.Item148MainProofKTypeTheta
import CFSG.RankThree.PartTwo.Sec14.Item148Res6ProofPGLNorm
import CFSG.RankThree.PartTwo.Sec14.Item148Res6ProofPGLFacts
import CFSG.RankThree.PartTwo.Sec14.Item148Res5ProofImgLe
import CFSG.RankThree.PartTwo.Sec14.Item148ProofNHJ
import CFSG.RankThree.PartTwo.Sec4.Item462AltProofModels
import CFSG.RankThree.PartTwo.KFacts.KS14Orders
public import CFSG.RankThree.PartTwo.Sec14.Ronan148MInd

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan148N

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec14
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.LocalRank CFSG.GH74.GLS
open scoped Pointwise commutatorElement

@[expose] def KF148PGLCentAct : Prop :=
  ∀ (Γ : Type) [Group Γ] [Finite Γ] (J E : Subgroup Γ) (p f : ℕ), 1 ≤ f →
    IsZ3PGLThreeAt ↥(J ⊔ E) p f → Group.IsPerfect ↥J → E ≤ Subgroup.normalizer (J : Set Γ) →
    ∀ a ∈ J, a ≠ 1 → a ^ 3 = 1 → ∀ t ∈ J ⊔ E, t * a = a * t →
      ∃ s ∈ J ⊓ Subgroup.centralizer ({a} : Set Γ),
        ∀ y ∈ pPrimeCoreOf 3 (J ⊓ Subgroup.centralizer ({a} : Set Γ)),
          t * y * t⁻¹ = s * y * s⁻¹

variable {G : Type} [Group G] [Finite G]

section Alpha

variable {A Y : Subgroup G} [(ker148 A Y).Normal]

omit [Finite G] in
theorem exists_alpha148_eq {y : ↥(Y ⊔ A) ⧸ ker148 A Y} (hy : y ∈ img148 A Y A) :
    ∃ (a : G) (ha : a ∈ A), alpha148 A Y a ha = y := by
  obtain ⟨a, haM, haA, rfl⟩ := mem_img148_iff.mp hy
  exact ⟨a, haA, rfl⟩

end Alpha

section Passage

variable {A Y : Subgroup G} [(ker148 A Y).Normal]

theorem img148_le_of_hyperplane148 {LB : Subgroup G → Subgroup G} (hA : Late.IsE27 A)
    (hAY : A ≤ Subgroup.normalizer (Y : Set G)) {J : Subgroup G} (hJY : J ≤ Y)
    (hAJ : A ≤ Subgroup.normalizer (J : Set G)) {e a₀ : G} (he : e ∈ A) (he1 : e ≠ 1)
    (ha₀ : a₀ ∈ A) (ha₀J : alpha148 A Y a₀ ha₀ ∈ img148 A Y J)
    (ha₀e : a₀ ∉ Subgroup.zpowers e)
    (heJ : alpha148 A Y e he ∈
      Subgroup.centralizer (img148 A Y J : Set (↥(Y ⊔ A) ⧸ ker148 A Y)))
    (hZ : img148 A Y J ⊓
      Subgroup.centralizer (img148 A Y J : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) = ⊥)
    (hKF : ∀ (t : G) (ht : t ∈ A), ∃ s ∈ img148 A Y J ⊓
        Subgroup.centralizer ({alpha148 A Y a₀ ha₀} : Set (↥(Y ⊔ A) ⧸ ker148 A Y)),
      ∀ y ∈ pPrimeCoreOf 3 (img148 A Y J ⊓
        Subgroup.centralizer ({alpha148 A Y a₀ ha₀} : Set (↥(Y ⊔ A) ⧸ ker148 A Y))),
        alpha148 A Y t ht * y * (alpha148 A Y t ht)⁻¹ = s * y * s⁻¹)
    {B Q : Subgroup G} (hB : IsHyperplane A B) (hLB : LB B = ⊥) (hQ : Q ∈ scriptQZero A LB)
    (hQY : Q ≤ Y ⊓ Subgroup.centralizer (B : Set G))
    (hQJ : img148 A Y Q ≤ img148 A Y J ⊔
      Subgroup.centralizer (img148 A Y J : Set (↥(Y ⊔ A) ⧸ ker148 A Y))) :
    img148 A Y Q ≤ img148 A Y J ⊔ img148 A Y (deltaZero A LB (Ronan148M.centPre148 A Y J)) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set J' := img148 A Y J with hJ'
  set Z := Subgroup.centralizer (J' : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) with hZdef
  set Abar := img148 A Y A with hAbar
  set Qbar := img148 A Y Q with hQbar
  set D₁ := img148 A Y (deltaZero A LB (Ronan148M.centPre148 A Y J)) with hD₁
  have hcomm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hA.1.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hA3 : ∀ a ∈ A, a ^ 3 = 1 := hA.1.2
  have hQM : Q ≤ Y ⊔ A := hQY.trans (inf_le_left.trans le_sup_left)
  have hQA : Qbar = ⁅Qbar, Abar⁆ := by
    rw [hQbar]
    conv_lhs => rw [hQ.2]
    rw [Item148PtRes.img148_commutator hQM le_sup_right]
  have hAJbar : Abar ≤ Subgroup.normalizer (J' : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) :=
    img148_le_normalizer hAJ
  have hAZ : ∀ y ∈ Abar, y ∈ Subgroup.normalizer (Z : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) :=
    fun y hy => mem_normalizer_centralizer148 (hAJbar hy)
  have hJZ : J' ≤ Subgroup.normalizer (Z : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) :=
    fun j hj => mem_normalizer_centralizer148 (Subgroup.le_normalizer hj)
  have hJZN : J' ⊔ Z ≤ Subgroup.normalizer (Z : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) :=
    sup_le hJZ Subgroup.le_normalizer
  have hdec : ∀ x ∈ Qbar, ∃ u ∈ J', ∃ v ∈ Z, u * v = x := by
    intro x hx
    have h1 : x ∈ ((J' ⊔ Z : Subgroup _) : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) := hQJ hx
    rw [Subgroup.coe_mul_of_left_le_normalizer_right J' Z hJZ] at h1
    obtain ⟨u, hu, v, hv, huv⟩ := h1
    exact ⟨u, hu, v, hv, huv⟩
  have hcommB : ∀ S : Subgroup G, S ≤ Subgroup.centralizer (B : Set G) →
      ∀ x ∈ img148 A Y S, ∀ (b : G) (hb : b ∈ B),
        x * alpha148 A Y b (hB.1 hb) = alpha148 A Y b (hB.1 hb) * x := by
    intro S hS x hx b hb
    obtain ⟨q, hqM, hqS, rfl⟩ := mem_img148_iff.mp hx
    rw [alpha148_eq_mk', ← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    exact (Subgroup.mem_centralizer_iff.mp (hS hqS) b hb).symm
  have hQB : ∀ x ∈ Qbar, ∀ (b : G) (hb : b ∈ B),
      x * alpha148 A Y b (hB.1 hb) = alpha148 A Y b (hB.1 hb) * x :=
    hcommB Q (hQY.trans inf_le_right)
  have hBJ : ∀ (b : G) (hb : b ∈ B), alpha148 A Y b (hB.1 hb) ∈
      Subgroup.normalizer (J' : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) :=
    fun b hb => hAJbar (alpha148_mem_img148 (hB.1 hb))
  by_cases heB : e ∈ B
  · by_cases ha₀B : a₀ ∈ B
    ·
      have hB9 : Nat.card B = 9 := by
        have h := hB.2
        rw [hA.2] at h
        omega
      have he3 : orderOf e = 3 := orderOf_eq_prime (hA3 e he) he1
      have hBle : B ≤ Subgroup.zpowers e ⊔ Subgroup.zpowers a₀ := by
        set S := Subgroup.zpowers e ⊔ Subgroup.zpowers a₀ with hS
        have hSB : S ≤ B :=
          sup_le (Subgroup.zpowers_le.mpr heB) (Subgroup.zpowers_le.mpr ha₀B)
        have h1 : Nat.card S ∣ 3 ^ 2 := by
          rw [show (3 : ℕ) ^ 2 = 9 by norm_num, ← hB9]
          exact Subgroup.card_dvd_of_le hSB
        have h2 : 3 ∣ Nat.card S := by
          have := Subgroup.card_dvd_of_le (le_sup_left : Subgroup.zpowers e ≤ S)
          rwa [Nat.card_zpowers, he3] at this
        have h3 : Nat.card S ≠ 3 := by
          intro h
          have heS : Subgroup.zpowers e = S :=
            Subgroup.eq_of_le_of_card_ge le_sup_left (by rw [h, Nat.card_zpowers, he3])
          exact ha₀e (heS ▸ Subgroup.mem_sup_right (Subgroup.mem_zpowers a₀))
        have h9 : Nat.card S = 9 := by
          obtain ⟨k, hk, hSk⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp h1
          rw [hSk] at h2 h3 ⊢
          interval_cases k
          · norm_num at h2
          · norm_num at h3
          · norm_num
        exact (Subgroup.eq_of_le_of_card_ge hSB (by rw [h9, hB9])).ge
      set a0b := alpha148 A Y a₀ ha₀ with ha0b
      set C := J' ⊓ Subgroup.centralizer ({a0b} : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) with hC
      set O := pPrimeCoreOf 3 (Subgroup.centralizer (B : Set G)) with hO
      set Obar := img148 A Y O with hObar
      set N := J' ⊓ Obar with hN
      have hQO : Q ≤ O :=
        le_pPrimeCoreOf_centralizer_of_scriptQZero hA hB hLB hQ (hQY.trans inf_le_right)
      have hO3 : Nat.Coprime 3 (Nat.card O) := coprime_card_pPrimeCoreOf 3 _
      have hOB : O ≤ Subgroup.centralizer (B : Set G) := pPrimeCoreOf_le 3 _
      have hBB : B ≤ Subgroup.centralizer (B : Set G) := by
        intro b hb
        rw [Subgroup.mem_centralizer_iff]
        intro b' hb'
        exact hcomm b' (hB.1 hb') b (hB.1 hb)
      have hAC : A ≤ Subgroup.centralizer (B : Set G) := by
        intro a ha
        rw [Subgroup.mem_centralizer_iff]
        intro b hb
        exact hcomm b (hB.1 hb) a ha
      have hCB : ∀ c ∈ C, c ∈ Subgroup.centralizer
          (img148 A Y B : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) := by
        intro c hc
        set W : Subgroup G := ((Subgroup.centralizer ({c} : Set (↥(Y ⊔ A) ⧸ ker148 A Y))).comap
          (QuotientGroup.mk' (ker148 A Y))).map (Y ⊔ A).subtype with hW
        have heW : e ∈ W := by
          refine ⟨⟨e, Subgroup.mem_sup_right he⟩, ?_, rfl⟩
          rw [SetLike.mem_coe, Subgroup.mem_comap, Subgroup.mem_centralizer_singleton_iff]
          exact (Subgroup.mem_centralizer_iff.mp heJ c hc.1).symm
        have ha₀W : a₀ ∈ W := by
          refine ⟨⟨a₀, Subgroup.mem_sup_right ha₀⟩, ?_, rfl⟩
          rw [SetLike.mem_coe, Subgroup.mem_comap, Subgroup.mem_centralizer_singleton_iff]
          have := Subgroup.mem_centralizer_singleton_iff.mp hc.2
          exact this.symm
        have hBW : B ≤ W :=
          hBle.trans (sup_le (Subgroup.zpowers_le.mpr heW) (Subgroup.zpowers_le.mpr ha₀W))
        rw [Subgroup.mem_centralizer_iff]
        intro y hy
        obtain ⟨b, hbM, hbB, rfl⟩ := mem_img148_iff.mp hy
        obtain ⟨m, hm, hmb⟩ := hBW hbB
        have hmeq : m = ⟨b, hbM⟩ := Subtype.ext hmb
        rw [← hmeq]
        rw [SetLike.mem_coe, Subgroup.mem_comap, Subgroup.mem_centralizer_singleton_iff] at hm
        exact hm
      have hB3 : IsPGroup 3 B := isPGroup_three_of_pow148 fun b hb => hA3 b (hB.1 hb)
      have hlift : ∀ c ∈ C, ∃ (x : G) (hx : x ∈ Y ⊔ A), x ∈ J ∧
          x ∈ Subgroup.centralizer (B : Set G) ∧ QuotientGroup.mk' (ker148 A Y) ⟨x, hx⟩ = c :=
        fun c hc => exists_lift_centralizer148 hAY hJY hB.1 (hB.1.trans hAJ) hB3 hc.1 (hCB c hc)
      have h3c : ∀ x ∈ Qbar, ∀ c ∈ C, ⁅x, c⁆ ∈ Obar := by
        intro x hx c hc
        obtain ⟨q, hqM, hqQ, rfl⟩ := mem_img148_iff.mp hx
        obtain ⟨w, hwM, hwJ, hwB, rfl⟩ := hlift c hc
        rw [← map_commutatorElement]
        refine mem_img148_iff.mpr ⟨_, (⁅(⟨q, hqM⟩ : ↥(Y ⊔ A)), ⟨w, hwM⟩⁆ : ↥(Y ⊔ A)).2, ?_, rfl⟩
        have hwO : w ∈ Subgroup.normalizer (O : Set G) := le_normalizer_pPrimeCoreOf 3 _ hwB
        have hq : q ∈ O := hQO hqQ
        show q * w * q⁻¹ * w⁻¹ ∈ O
        have e1 : q * w * q⁻¹ * w⁻¹ = q * (w * q⁻¹ * w⁻¹) := by group
        rw [e1]
        exact O.mul_mem hq ((Subgroup.mem_normalizer_iff.mp hwO q⁻¹).mp (O.inv_mem hq))
      have hNC : N ≤ C := by
        intro x hx
        refine Subgroup.mem_inf.mpr ⟨hx.1, ?_⟩
        rw [Subgroup.mem_centralizer_singleton_iff]
        exact hcommB O hOB x hx.2 a₀ ha₀B
      have hCN : C ≤ Subgroup.normalizer (N : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) := by
        intro c hc
        obtain ⟨w, hwM, hwJ, hwB, rfl⟩ := hlift c hc
        have h1 : QuotientGroup.mk' (ker148 A Y) ⟨w, hwM⟩ ∈
            img148 A Y (J ⊓ Subgroup.centralizer (B : Set G)) :=
          mem_img148_iff.mpr ⟨w, hwM, ⟨hwJ, hwB⟩, rfl⟩
        exact mem_normalizer_inf148
          (img148_le_normalizer (inf_le_left.trans Subgroup.le_normalizer) h1)
          (img148_le_normalizer (inf_le_right.trans (le_normalizer_pPrimeCoreOf 3 _)) h1)
      set U := J' ⊓ (Qbar ⊔ Z) with hU
      have hQZN : Qbar ≤ Subgroup.normalizer (Z : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) :=
        hQJ.trans hJZN
      have hUdec : ∀ u ∈ U, ∃ x ∈ Qbar, ∃ z ∈ Z, x * z = u := by
        intro u hu
        have h1 : u ∈ ((Qbar ⊔ Z : Subgroup _) : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) := hu.2
        rw [Subgroup.coe_mul_of_left_le_normalizer_right Qbar Z hQZN] at h1
        obtain ⟨x, hx, z, hz, hxz⟩ := h1
        exact ⟨x, hx, z, hz, hxz⟩
      have hUC : U ≤ C := by
        intro u hu
        refine Subgroup.mem_inf.mpr ⟨hu.1, ?_⟩
        obtain ⟨x, hx, z, hz, rfl⟩ := hUdec u hu
        rw [Subgroup.mem_centralizer_singleton_iff]
        have h1 := hQB x hx a₀ ha₀B
        have h2 : z * a0b = a0b * z := (Subgroup.mem_centralizer_iff.mp hz _ ha₀J).symm
        calc x * z * a0b = x * (z * a0b) := by group
          _ = x * (a0b * z) := by rw [h2]
          _ = (x * a0b) * z := by group
          _ = (a0b * x) * z := by rw [h1]
          _ = a0b * (x * z) := by group
      have hUN : ∀ u ∈ U, ∀ c ∈ C, ⁅u, c⁆ ∈ N := by
        intro u hu c hc
        refine ⟨?_, ?_⟩
        · rw [commutatorElement_def]
          exact J'.mul_mem (J'.mul_mem (J'.mul_mem hu.1 hc.1) (J'.inv_mem hu.1)) (J'.inv_mem hc.1)
        · obtain ⟨x, hx, z, hz, rfl⟩ := hUdec u hu
          have hzc : z * c = c * z := (Subgroup.mem_centralizer_iff.mp hz c hc.1).symm
          rw [commutatorElement_mul_left_of_commute148 hzc]
          exact h3c x hx c hc
      have hQ3 : ¬ 3 ∣ Nat.card Q := (isPiSubgroup_piCompl_iff Nat.prime_three Q).mp hQ.1.1.2.1
      have hQbar3 : Nat.Coprime 3 (Nat.card Qbar) :=
        (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr
          (Item148PtRes.not_three_dvd_card_img148 hQ3)
      have hUord : ∀ u ∈ U, Nat.Coprime 3 (orderOf u) := by
        intro u hu
        obtain ⟨x, hx, z, hz, rfl⟩ := hUdec u hu
        obtain ⟨u', hu', v', hv', rfl⟩ := hdec x hx
        have hvz : v' * z = 1 := by
          have h1 : v' * z ∈ J' := by
            have e1 : v' * z = u'⁻¹ * (u' * v' * z) := by group
            rw [e1]
            exact J'.mul_mem (J'.inv_mem hu') hu.1
          have h3 : v' * z ∈ J' ⊓ Z := ⟨h1, Z.mul_mem hv' hz⟩
          rw [hZ] at h3
          exact h3
        have hu_eq : u' * v' * z = u' := by rw [mul_assoc, hvz, mul_one]
        rw [hu_eq]
        have hcomm' : Commute u' v' := Subgroup.mem_centralizer_iff.mp hv' u' hu'
        set m := orderOf (u' * v') with hm
        have hm1 : (u' * v') ^ m = 1 := pow_orderOf_eq_one _
        rw [hcomm'.mul_pow] at hm1
        have hum : u' ^ m = 1 := by
          have h1 : u' ^ m = (v' ^ m)⁻¹ := eq_inv_of_mul_eq_one_left hm1
          have h2 : u' ^ m ∈ J' ⊓ Z := ⟨J'.pow_mem hu' m, h1 ▸ Z.inv_mem (Z.pow_mem hv' m)⟩
          rw [hZ] at h2
          exact h2
        have hdvd : orderOf u' ∣ m := orderOf_dvd_of_pow_eq_one hum
        have hmQ : m ∣ Nat.card Qbar := Subgroup.orderOf_dvd_natCard Qbar hx
        exact Nat.Coprime.coprime_dvd_right (hdvd.trans hmQ) hQbar3
      have hUcard : Nat.Coprime 3 (Nat.card U) := by
        rw [Nat.Prime.coprime_iff_not_dvd Nat.prime_three]
        intro h3
        obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' (G := ↥U) 3 h3
        have h1 := hUord u u.2
        rw [Subgroup.orderOf_coe, hu] at h1
        norm_num at h1
      have hNbar3 : Nat.Coprime 3 (Nat.card N) := by
        have h1 : ¬ 3 ∣ Nat.card Obar := Item148PtRes.not_three_dvd_card_img148
          ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp hO3)
        exact Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le inf_le_right)
          ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr h1)
      have hUNn : U ≤ Subgroup.normalizer (N : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) := hUC.trans hCN
      have hW3 : Nat.Coprime 3 (Nat.card ↥(N ⊔ U)) :=
        Nat.Coprime.coprime_dvd_right (Main148.card_sup_dvd_of_le_normalizer148 N U hUNn)
          (Nat.Coprime.mul_right hNbar3 hUcard)
      have hWC : N ⊔ U ≤ C := sup_le hNC hUC
      have hCW : C ≤ Subgroup.normalizer ((N ⊔ U : Subgroup _) : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) := by
        refine le_normalizer_of_forall148 fun c hc w hw => ?_
        have hw' : w ∈ ((N ⊔ U : Subgroup _) : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) := hw
        rw [Subgroup.coe_mul_of_right_le_normalizer_left N U hUNn] at hw'
        obtain ⟨n, hn, u, hu, rfl⟩ := hw'
        have hcn : c * n * c⁻¹ ∈ N := (Subgroup.mem_normalizer_iff.mp (hCN hc) n).mp hn
        have hcu : ⁅u, c⁆⁻¹ ∈ N := N.inv_mem (hUN u hu c hc)
        have e1 : c * (n * u) * c⁻¹ = (c * n * c⁻¹) * ⁅u, c⁆⁻¹ * u := by
          rw [commutatorElement_def]
          group
        rw [e1]
        exact (N ⊔ U).mul_mem ((N ⊔ U).mul_mem (Subgroup.mem_sup_left hcn)
          (Subgroup.mem_sup_left hcu)) (Subgroup.mem_sup_right hu)
      have hWO : N ⊔ U ≤ pPrimeCoreOf 3 C := le_pPrimeCoreOf hWC hCW hW3
      obtain ⟨t, htA, htB⟩ : ∃ t ∈ A, t ∉ B := by
        by_contra hcon
        push Not at hcon
        have h1 := Subgroup.card_le_of_le (show A ≤ B from fun t ht => hcon t ht)
        have h2 := hB.2
        have h3 : 0 < Nat.card B := Nat.card_pos
        omega
      obtain ⟨s, hsC, hs⟩ := hKF t htA
      set tb := alpha148 A Y t htA with htb
      have hsW : ∀ n : ℕ, ∀ y ∈ pPrimeCoreOf 3 C,
          tb ^ n * y * (tb ^ n)⁻¹ = s ^ n * y * (s ^ n)⁻¹ := by
        intro n
        induction n with
        | zero => intro y _; simp
        | succ n ih =>
          intro y hy
          have hsn : s ^ n ∈ Subgroup.normalizer ((pPrimeCoreOf 3 C : Subgroup _) : Set _) :=
            Subgroup.pow_mem _ (le_normalizer_pPrimeCoreOf 3 C hsC) n
          have hyn : s ^ n * y * (s ^ n)⁻¹ ∈ pPrimeCoreOf 3 C :=
            (Subgroup.mem_normalizer_iff.mp hsn y).mp hy
          calc tb ^ (n + 1) * y * (tb ^ (n + 1))⁻¹ = tb * (tb ^ n * y * (tb ^ n)⁻¹) * tb⁻¹ := by
                group
            _ = tb * (s ^ n * y * (s ^ n)⁻¹) * tb⁻¹ := by rw [ih y hy]
            _ = s * (s ^ n * y * (s ^ n)⁻¹) * s⁻¹ := hs _ hyn
            _ = s ^ (n + 1) * y * (s ^ (n + 1))⁻¹ := by group
      have hbN : ∀ (b : G) (hb : b ∈ B),
          alpha148 A Y b (hB.1 hb) ∈ Subgroup.normalizer (N : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) := by
        intro b hb
        have h1 : alpha148 A Y b (hB.1 hb) ∈ img148 A Y B :=
          mem_img148_iff.mpr ⟨b, _, hb, rfl⟩
        exact mem_normalizer_inf148 (hBJ b hb)
          (img148_le_normalizer (hBB.trans (le_normalizer_pPrimeCoreOf 3 _)) h1)
      have h3l : ∀ u ∈ U, ∀ (a : G) (ha : a ∈ A), ⁅u, alpha148 A Y a ha⁆ ∈ N := by
        intro u hu a ha
        obtain ⟨b, hb, k, rfl⟩ := exists_mem_mul_zpow_of_hyperplane148 hA hB htA htB ha
        have e1 : alpha148 A Y (b * t ^ k) ha = alpha148 A Y b (hB.1 hb) * tb ^ k := by
          rw [htb, ← alpha148_pow htA k, ← alpha148_mul]
        rw [e1]
        have hub : u * alpha148 A Y b (hB.1 hb) = alpha148 A Y b (hB.1 hb) * u :=
          (Subgroup.mem_centralizer_iff.mp (hCB u (hUC hu)) _
            (mem_img148_iff.mpr ⟨b, _, hb, rfl⟩)).symm
        rw [commutatorElement_mul_right_of_commute148 hub]
        have h1 : ⁅u, tb ^ k⁆ = ⁅u, s ^ k⁆ := by
          rw [commutatorElement_def, commutatorElement_def]
          have h2 := hsW k u⁻¹ ((pPrimeCoreOf 3 C).inv_mem (hWO (Subgroup.mem_sup_right hu)))
          calc u * tb ^ k * u⁻¹ * (tb ^ k)⁻¹ = u * (tb ^ k * u⁻¹ * (tb ^ k)⁻¹) := by group
            _ = u * (s ^ k * u⁻¹ * (s ^ k)⁻¹) := by rw [h2]
            _ = u * s ^ k * u⁻¹ * (s ^ k)⁻¹ := by group
        rw [h1]
        exact (Subgroup.mem_normalizer_iff.mp (hbN b hb) _).mp (hUN u hu (s ^ k) (C.pow_mem hsC k))
      have hcommZ : ∀ v ∈ Z, ∀ (a : G) (ha : a ∈ A), ⁅v, alpha148 A Y a ha⁆ ∈ Z := by
        intro v hv a ha
        have haZ := hAZ _ (alpha148_mem_img148 ha)
        rw [commutatorElement_def]
        have e1 : v * alpha148 A Y a ha * v⁻¹ * (alpha148 A Y a ha)⁻¹ =
            v * (alpha148 A Y a ha * v⁻¹ * (alpha148 A Y a ha)⁻¹) := by group
        rw [e1]
        exact Z.mul_mem hv ((Subgroup.mem_normalizer_iff.mp haZ v⁻¹).mp (Z.inv_mem hv))
      have hmemU : ∀ x ∈ Qbar, ∀ u ∈ J', ∀ v ∈ Z, u * v = x → u ∈ U := by
        intro x hx u hu v hv huv
        refine ⟨hu, ?_⟩
        have e1 : u = x * v⁻¹ := by rw [← huv]; group
        rw [e1]
        exact (Qbar ⊔ Z).mul_mem (Subgroup.mem_sup_left hx) (Subgroup.mem_sup_right (Z.inv_mem hv))
      have h3m : Qbar ≤ N ⊔ Z := by
        rw [hQA, Subgroup.commutator_le]
        intro x hx y hy
        obtain ⟨a, ha, rfl⟩ := exists_alpha148_eq hy
        obtain ⟨u, hu, v, hv, rfl⟩ := hdec x hx
        have huU := hmemU _ hx u hu v hv rfl
        have hvz := hcommZ v hv a ha
        have hsplit : u * ⁅v, alpha148 A Y a ha⁆ = ⁅v, alpha148 A Y a ha⁆ * u :=
          Subgroup.mem_centralizer_iff.mp hvz u hu
        rw [commutatorElement_mul_split148 hsplit]
        exact (N ⊔ Z).mul_mem (Subgroup.mem_sup_right hvz) (Subgroup.mem_sup_left (h3l u huU a ha))
      have h3n : U ≤ N := by
        intro u hu
        have h1 : u ∈ N ⊔ Z := (sup_le h3m le_sup_right) hu.2
        have hNZ : N ≤ Subgroup.normalizer (Z : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) :=
          inf_le_left.trans hJZ
        have h2 : u ∈ ((N ⊔ Z : Subgroup _) : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) := h1
        rw [Subgroup.coe_mul_of_left_le_normalizer_right N Z hNZ] at h2
        obtain ⟨n, hn, z, hz, hnz⟩ := h2
        have hnz' : n * z = u := hnz
        have hz1 : z = 1 := by
          have hzJ : z ∈ J' := by
            have e1 : z = n⁻¹ * (n * z) := by group
            rw [e1, hnz']
            exact J'.mul_mem (J'.inv_mem hn.1) hu.1
          have h3 : z ∈ J' ⊓ Z := ⟨hzJ, hz⟩
          rw [hZ] at h3
          exact h3
        rw [← hnz', hz1, mul_one]
        exact hn
      have hAP : A ≤ Subgroup.normalizer
          ((O ⊓ Ronan148M.centPre148 A Y J : Subgroup G) : Set G) := fun a ha =>
        mem_normalizer_inf148 ((hAC.trans (le_normalizer_pPrimeCoreOf 3 _)) ha)
          (Ronan148M.le_normalizer_centPre148 hAY hAJ ha)
      have hPQ : O ⊓ Ronan148M.centPre148 A Y J ∈ scriptQ A LB :=
        mem_scriptQ_of_le (pPrimeCoreOf_centralizer_mem_scriptQ hA hB) inf_le_left hAP
      have hPB : (O ⊓ Ronan148M.centPre148 A Y J) ⊓ Subgroup.centralizer (B : Set G) =
          O ⊓ Ronan148M.centPre148 A Y J := inf_eq_left.mpr (inf_le_left.trans hOB)
      have hPQ0 : ⁅O ⊓ Ronan148M.centPre148 A Y J, A⁆ ∈ scriptQZero A LB := by
        have := commutator_inf_centralizer_mem_scriptQZero hA hPQ hB.1
        rwa [hPB] at this
      have hPY₁ : ⁅O ⊓ Ronan148M.centPre148 A Y J, A⁆ ≤ Ronan148M.centPre148 A Y J :=
        (Subgroup.le_normalizer_iff_commutator_le_left.mp hAP).trans inf_le_right
      rw [hQA, Subgroup.commutator_le]
      intro x hx y hy
      obtain ⟨a, ha, rfl⟩ := exists_alpha148_eq hy
      obtain ⟨u, hu, v, hv, rfl⟩ := hdec x hx
      have huN := h3n (hmemU _ hx u hu v hv rfl)
      have hvO : v ∈ Obar := by
        have e1 : v = u⁻¹ * (u * v) := by group
        rw [e1]
        exact Obar.mul_mem (Obar.inv_mem huN.2) (img148_mono hQO hx)
      obtain ⟨o, hoM, hoO, rfl⟩ := mem_img148_iff.mp hvO
      have hoY : o ∈ Y := Main148.mem_of_coprime_three_of_mem_sup hAY hA3 hoM
        (Nat.Coprime.coprime_dvd_right (Subgroup.orderOf_dvd_natCard O hoO) hO3)
      have hoY₁ : o ∈ Ronan148M.centPre148 A Y J := Ronan148M.mem_centPre148_iff.mpr ⟨hoY, hv⟩
      have hvD : ⁅QuotientGroup.mk' (ker148 A Y) ⟨o, hoM⟩, alpha148 A Y a ha⁆ ∈ D₁ := by
        rw [alpha148_eq_mk', ← map_commutatorElement]
        refine mem_img148_iff.mpr ⟨_, (⁅(⟨o, hoM⟩ : ↥(Y ⊔ A)),
          ⟨a, Subgroup.mem_sup_right ha⟩⁆ : ↥(Y ⊔ A)).2, ?_, rfl⟩
        have h1 : ⁅o, a⁆ ∈ ⁅O ⊓ Ronan148M.centPre148 A Y J, A⁆ :=
          Subgroup.commutator_mem_commutator ⟨hoO, hoY₁⟩ ha
        exact le_deltaZero hPQ0 hPY₁ h1
      have hvz := hcommZ _ hv a ha
      have hsplit : u * ⁅QuotientGroup.mk' (ker148 A Y) ⟨o, hoM⟩, alpha148 A Y a ha⁆ =
          ⁅QuotientGroup.mk' (ker148 A Y) ⟨o, hoM⟩, alpha148 A Y a ha⁆ * u :=
        Subgroup.mem_centralizer_iff.mp hvz u hu
      rw [commutatorElement_mul_split148 hsplit]
      have huJ : ⁅u, alpha148 A Y a ha⁆ ∈ J' := by
        have hN' := hAJbar (alpha148_mem_img148 ha)
        rw [commutatorElement_def]
        have e1 : u * alpha148 A Y a ha * u⁻¹ * (alpha148 A Y a ha)⁻¹ =
            u * (alpha148 A Y a ha * u⁻¹ * (alpha148 A Y a ha)⁻¹) := by group
        rw [e1]
        exact J'.mul_mem hu ((Subgroup.mem_normalizer_iff.mp hN' u⁻¹).mp (J'.inv_mem hu))
      exact (J' ⊔ D₁).mul_mem (Subgroup.mem_sup_right hvD) (Subgroup.mem_sup_left huJ)
    ·
      refine le_trans ?_ le_sup_left
      rw [hQA, Subgroup.commutator_le]
      intro x hx y hy
      obtain ⟨a, ha, rfl⟩ := exists_alpha148_eq hy
      obtain ⟨b, hb, k, rfl⟩ := exists_mem_mul_zpow_of_hyperplane148 hA hB ha₀ ha₀B ha
      have e1 : alpha148 A Y (b * a₀ ^ k) ha =
          alpha148 A Y b (hB.1 hb) * alpha148 A Y a₀ ha₀ ^ k := by
        rw [← alpha148_pow ha₀ k, ← alpha148_mul]
      rw [e1, commutatorElement_mul_right_of_commute148 (hQB x hx b hb)]
      obtain ⟨u, hu, v, hv, rfl⟩ := hdec x hx
      have hvc : v * alpha148 A Y a₀ ha₀ ^ k = alpha148 A Y a₀ ha₀ ^ k * v :=
        (Subgroup.mem_centralizer_iff.mp hv _ (J'.pow_mem ha₀J k)).symm
      rw [commutatorElement_mul_left_of_commute148 hvc]
      have h1 : ⁅u, alpha148 A Y a₀ ha₀ ^ k⁆ ∈ J' := by
        rw [commutatorElement_def]
        exact J'.mul_mem (J'.mul_mem (J'.mul_mem hu (J'.pow_mem ha₀J k)) (J'.inv_mem hu))
          (J'.inv_mem (J'.pow_mem ha₀J k))
      exact (Subgroup.mem_normalizer_iff.mp (hBJ b hb) _).mp h1
  ·
    have hQZ : Qbar ≤ Z := by
      rw [hQA, Subgroup.commutator_le]
      intro x hx y hy
      obtain ⟨a, ha, rfl⟩ := exists_alpha148_eq hy
      obtain ⟨b, hb, k, rfl⟩ := exists_mem_mul_zpow_of_hyperplane148 hA hB he heB ha
      have e1 : alpha148 A Y (b * e ^ k) ha =
          alpha148 A Y b (hB.1 hb) * alpha148 A Y e he ^ k := by
        rw [← alpha148_pow he k, ← alpha148_mul]
      rw [e1, commutatorElement_mul_right_of_commute148 (hQB x hx b hb)]
      have hxN : x ∈ Subgroup.normalizer (Z : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) := hJZN (hQJ hx)
      have hek : alpha148 A Y e he ^ k ∈ Z := Z.pow_mem heJ k
      have h1 : ⁅x, alpha148 A Y e he ^ k⁆ ∈ Z := by
        rw [commutatorElement_def]
        exact Z.mul_mem ((Subgroup.mem_normalizer_iff.mp hxN _).mp hek) (Z.inv_mem hek)
      exact (Subgroup.mem_normalizer_iff.mp (hAZ _ (alpha148_mem_img148 (hB.1 hb))) _).mp h1
    have hQY₁ : Q ≤ Ronan148M.centPre148 A Y J := by
      intro q hq
      have hqY : q ∈ Y := (hQY hq).1
      refine Ronan148M.mem_centPre148_iff.mpr ⟨hqY, hQZ ?_⟩
      exact mem_img148_iff.mpr ⟨q, _, hq, rfl⟩
    exact (img148_mono (le_deltaZero hQ hQY₁)).trans le_sup_right

theorem img148_deltaZero_le_sup148 {LB : Subgroup G → Subgroup G} (hA : Late.IsE27 A)
    (hAY : A ≤ Subgroup.normalizer (Y : Set G)) {J : Subgroup G} (hJY : J ≤ Y)
    (hAJ : A ≤ Subgroup.normalizer (J : Set G)) {e a₀ : G} (he : e ∈ A) (he1 : e ≠ 1)
    (ha₀ : a₀ ∈ A) (ha₀J : alpha148 A Y a₀ ha₀ ∈ img148 A Y J)
    (ha₀e : a₀ ∉ Subgroup.zpowers e)
    (heJ : alpha148 A Y e he ∈
      Subgroup.centralizer (img148 A Y J : Set (↥(Y ⊔ A) ⧸ ker148 A Y)))
    (hZ : img148 A Y J ⊓
      Subgroup.centralizer (img148 A Y J : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) = ⊥)
    (hKF : ∀ (t : G) (ht : t ∈ A), ∃ s ∈ img148 A Y J ⊓
        Subgroup.centralizer ({alpha148 A Y a₀ ha₀} : Set (↥(Y ⊔ A) ⧸ ker148 A Y)),
      ∀ y ∈ pPrimeCoreOf 3 (img148 A Y J ⊓
        Subgroup.centralizer ({alpha148 A Y a₀ ha₀} : Set (↥(Y ⊔ A) ⧸ ker148 A Y))),
        alpha148 A Y t ht * y * (alpha148 A Y t ht)⁻¹ = s * y * s⁻¹)
    (hLB : ∀ B : Subgroup G, IsHyperplane A B → LB B = ⊥)
    (hQJ : ∀ Q ∈ scriptQZero A LB, Q ≤ Y → img148 A Y Q ≤ img148 A Y J ⊔
      Subgroup.centralizer (img148 A Y J : Set (↥(Y ⊔ A) ⧸ ker148 A Y))) :
    img148 A Y (deltaZero A LB Y) ≤
      img148 A Y J ⊔ img148 A Y (deltaZero A LB (Ronan148M.centPre148 A Y J)) := by
  set T := img148 A Y J ⊔ img148 A Y (deltaZero A LB (Ronan148M.centPre148 A Y J)) with hT
  set T' : Subgroup G := (T.comap (QuotientGroup.mk' (ker148 A Y))).map (Y ⊔ A).subtype
    with hT'
  have hle : deltaZero A LB Y ≤ T' := by
    rw [deltaZero_eq_iSup hA Y]
    refine iSup₂_le fun B hB => sSup_le fun Q hQ => ?_
    obtain ⟨hQ0, hQB⟩ := hQ
    have h := img148_le_of_hyperplane148 hA hAY hJY hAJ he he1 ha₀ ha₀J ha₀e heJ hZ hKF hB
      (hLB B hB) hQ0 hQB (hQJ Q hQ0 (hQB.trans inf_le_left))
    intro g hg
    have hgM : g ∈ Y ⊔ A := Subgroup.mem_sup_left (hQB hg).1
    exact ⟨⟨g, hgM⟩, h (mem_img148_iff.mpr ⟨g, hgM, hg, rfl⟩), rfl⟩
  intro x hx
  obtain ⟨g, hgM, hgD, rfl⟩ := mem_img148_iff.mp hx
  obtain ⟨m, hm, hmg⟩ := hle hgD
  have hmeq : m = ⟨g, hgM⟩ := Subtype.ext hmg
  rw [← hmeq]
  exact hm

end Passage

section Model

open CFSG.Assembly.RankThreeEven (projImage)
open Matrix (ProjGenLinGroup)

theorem isoLThreePi_of_isZ3PGLThreeAt148 {Γ : Type} [Group Γ] [Finite Γ] {J E : Subgroup Γ}
    {p f : ℕ} (hX : IsZ3PGLThreeAt ↥(J ⊔ E) p f) (hJp : Group.IsPerfect ↥J)
    (hJnt : Nontrivial ↥J) (hEJ : E ≤ Subgroup.normalizer (J : Set Γ)) :
    ∃ _ : Fact p.Prime, Sec4.IsoLThreePi ↥J p f := by
  classical
  obtain ⟨π, K, _, hK, hq, φ, -, hsurj, hmem⟩ :=
    Item148Res6.exists_tau_of_isZ3PGLThreeAt hX hJp hJnt hEJ
  have hp : Fact p.Prime := ⟨hK.prime⟩
  set τ : ↥J →* ↥(projImage (Sec4.slPi π 3 (p ^ f) K)) :=
    { toFun := fun j => ⟨((φ (Subgroup.inclusion le_sup_left j)).2 :
        ProjGenLinGroup (Fin 3) K), hmem j⟩
      map_one' := by
        apply Subtype.ext
        simp
      map_mul' := fun j j' => by
        apply Subtype.ext
        simp } with hτ
  have hτinj : Function.Injective τ := by
    rw [injective_iff_map_eq_one]
    intro j hj
    have h2 : (φ (Subgroup.inclusion le_sup_left j)).2 = 1 :=
      Subtype.ext (show ((φ (Subgroup.inclusion le_sup_left j)).2 : ProjGenLinGroup (Fin 3) K) =
        1 from congrArg Subtype.val hj)
    have h1 : (φ (Subgroup.inclusion le_sup_left j)).1 = 1 :=
      Item148PtRes2.eq_one_of_isPerfect
        ((MonoidHom.fst _ _).comp (φ.toMonoidHom.comp (Subgroup.inclusion le_sup_left))) j
    have h12 : φ (Subgroup.inclusion le_sup_left j) = 1 := Prod.ext h1 h2
    have h3 : Subgroup.inclusion (le_sup_left : J ≤ J ⊔ E) j = 1 :=
      φ.injective (h12.trans (map_one φ).symm)
    exact Subgroup.inclusion_injective le_sup_left (h3.trans (map_one _).symm)
  have hτsurj : Function.Surjective τ := by
    rintro ⟨s, hs⟩
    obtain ⟨j, hj⟩ := hsurj s hs
    exact ⟨j, Subtype.ext hj⟩
  exact ⟨hp, isoLThreePi_of_mulEquiv148 (MulEquiv.ofBijective τ ⟨hτinj, hτsurj⟩)
    (Sec4.Item462AltProof.isoLThreePi_projImage_slPi hK hq)⟩

end Model

section NoHJ

variable {A Y : Subgroup G} [(ker148 A Y).Normal]

theorem false_of_kType148_j2 {e : G} {K Le : Subgroup G} (hkt : KType148 A Y e K Le)
    (hKJ2 : IsEmpty (↥(img148 A Y K) ≃* CFSG.Blueprint.NativeSporadic.J2))
    (φ : ↥Le ⧸ aschbacherSolvableCore 3 ↥Le ≃* CFSG.Blueprint.NativeSporadic.J2)
    (hcen : Subgroup.center (↥Le ⧸ aschbacherSolvableCore 3 ↥Le) = ⊥) : False := by
  have hJ2 := KFacts.KS14.ks17J2NotList
  rcases hkt.2 with ⟨-, -, ⟨⟨ψ⟩⟩ | ⟨hM, -⟩ | ⟨p', f', e', hp', -, -, hLpi, -⟩⟩ | ⟨hTC, -⟩
  · exact hKJ2.false (ψ.trans φ)
  · rcases hM with ⟨⟨ψ⟩⟩ | ⟨h5, ⟨ψ⟩⟩ | ⟨h5, ⟨ψ⟩⟩
    · exact hJ2.2.2.false (φ.symm.trans ψ)
    · have h25 : Sec4.IsoLThreePi CFSG.Blueprint.NativeSporadic.J2 5 2 :=
        Or.inl ⟨by norm_num, ⟨φ.symm.trans ψ⟩⟩
      exact hJ2.1 5 2 h25
    · have h5' : Sec4.IsoLThreePi CFSG.Blueprint.NativeSporadic.J2 5 1 :=
        Or.inr ⟨by norm_num, ⟨φ.symm.trans ψ⟩⟩
      exact hJ2.1 5 1 h5'
  · exact hJ2.1 p' (f' * e') (isoLThreePi_of_mulEquiv148 φ.symm hLpi)
  · have hc := hTC.1
    rw [hcen, Subgroup.card_bot] at hc
    omega

end NoHJ

section Steps


@[expose] def Step148PGLCentInd : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec14Std G A c L → ∀ (Y : Subgroup G) (hY : Y ∈ scriptY A), ¬ Group.IsSolvable ↥Y →
      Ind148 A (lB A) Y → (∀ B' : Subgroup G, IsHyperplane A B' → YBOne A (lB A) Y B') →
      ∀ (B Q : Subgroup G) (e : G) (K Le : Subgroup G), IsPoint148 A (lB A) Y B Q e K Le →
      (letI := ker148_normal hY.2; KType148 A Y e K Le) →
      ∀ (_he : e ∈ A) (J : Subgroup G), J ∈ thetaComponentsIn Y → K ≤ J →
        A ≤ Subgroup.normalizer (J : Set G) →
        (letI := ker148_normal hY.2; Lift148Eq A Y K J) →
        (∃ (p f : ℕ), 1 ≤ f ∧
          (letI := ker148_normal hY.2; IsZ3PGLThreeAt ↥(img148 A Y (J ⊔ A)) p f)) →
        Subgroup.zpowers e ∈ omegaA A → Le ∈ lA A e →
        letI := ker148_normal hY.2
        img148 A Y (deltaZero A (lB A) (Ronan148M.centPre148 A Y J)) ≤ img148 A Y J ∨
          Case148Seven A (lB A) Y

theorem step148PGLCentInd_of_cent (h : Step148PGLCent) : Step148PGLCentInd := by
  intro G _ _ A c L hS Y hY hs ih hYB B Q e K Le hP hkt he J hJ hKJ hAJ halt hpgl heΩ hLeA
  letI := ker148_normal hY.2
  rcases h G A c L hS Y hY hs ih hYB B Q e K Le hP hkt he J hJ hKJ hAJ halt hpgl heΩ hLeA with
    hc | h7
  · exact Or.inl (Ronan148M.img148_deltaZero_centPre148_le.trans hc)
  · exact Or.inr h7

theorem step148PGLCent_of_ind
    (h134 : Item134) (h48 : Sec4.Item4_8)
    (h415 : Sec4.Item4_15) (hKF : KF148PGLCentAct) (hInd : Step148PGLCentInd) :
    Step148PGLCent := by
  intro G _ _ A c L h Y hY hs ih hYB B Q e K Le hP hkt he J hJ hKJ hAJ hEq hpgl heΩ hLeA
  letI := ker148_normal hY.2
  rcases hInd G A c L h Y hY hs ih hYB B Q e K Le hP hkt he J hJ hKJ hAJ hEq hpgl heΩ hLeA with
    hD1 | h7
  swap
  · exact Or.inr h7
  rcases Item148Res6.step148PGLNorm_holds G A c L h Y hY hs ih hYB B Q e K Le hP hkt he J hJ hKJ
      hAJ hEq hpgl heΩ hLeA with hnorm | h7
  swap
  · exact Or.inr h7
  left
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hA : Late.IsE27 A := h.isE27'
  have hAF : A ∈ partTwoF G := h.mem_partTwoF
  have hAY : A ≤ Subgroup.normalizer (Y : Set G) := hY.2
  have hJY : J ≤ Y := le_of_mem_thetaComponentsIn hJ
  have hJM : J ≤ Y ⊔ A := hJY.trans le_sup_left
  have hKYC : K ≤ Y ⊓ Subgroup.centralizer ({e} : Set G) :=
    le_of_mem_thetaComponentsIn hP.2.2.2.2.2.1
  have hKM : K ≤ Y ⊔ A := (hKYC.trans inf_le_left).trans le_sup_left
  have hKe : K ≤ Subgroup.centralizer {e} := hKYC.trans inf_le_right
  have hJeq : img148 A Y K = img148 A Y J := hEq
  have he1 : e ≠ 1 := hP.2.2.2.2.1
  have hJs : IsSimpleGroup ↥(img148 A Y J) := by
    have h1 := isSimpleGroup_img148_of_kType148 h hkt
    rw [hJeq] at h1
    exact h1
  obtain ⟨-, hJZ⟩ := Item148Res5.isComponent_img148 hAY hJ hJs
  have hZ : img148 A Y J ⊓
      Subgroup.centralizer (img148 A Y J : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have hxZ : (⟨x, hx.1⟩ : ↥(img148 A Y J)) ∈ Subgroup.center ↥(img148 A Y J) := by
      rw [Subgroup.mem_center_iff]
      intro g
      exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hx.2 g g.2)
    rw [hJZ, Subgroup.mem_bot] at hxZ
    rw [Subgroup.mem_bot]
    exact congrArg Subtype.val hxZ
  have hAJc := img148_inf_centralizer_eq hKM he hKe hkt.1 hJeq
  have heJ : alpha148 A Y e he ∈
      Subgroup.centralizer (img148 A Y J : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) := by
    have h1 : alpha148 A Y e he ∈ img148 A Y A ⊓
        Subgroup.centralizer (img148 A Y J : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) := by
      rw [hAJc]
      exact Subgroup.mem_zpowers _
    exact h1.2
  obtain ⟨p, f, hf, hpgl'⟩ := hpgl
  rw [img148_sup hJM le_sup_right] at hpgl'
  have : Group.IsPerfect ↥J := isPerfect_of_mem_thetaComponentsIn hJ
  have hJp : Group.IsPerfect ↥(img148 A Y J) := isPerfect_img148 hJM
  have hJnt : Nontrivial ↥(img148 A Y J) := hJs.toNontrivial
  obtain ⟨hAE, h27⟩ := img148_isE27 (Y := Y) hA
  have hAbar3 : ∀ a ∈ img148 A Y A, a ^ 3 = 1 := hAE.2
  have hAN : img148 A Y A ≤
      Subgroup.normalizer (img148 A Y J : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) :=
    img148_le_normalizer hAJ
  have hcomm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hA.1.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  obtain ⟨b, ⟨hbA, hbJ⟩, hb1⟩ :=
    Item148Res6.exists_ne_one_mem_inf_of_isZ3PGLThreeAt hpgl' hJp hJnt hAN hAbar3 h27
  obtain ⟨a₀, ha₀, rfl⟩ := exists_alpha148_eq hbA
  have ha₀e : a₀ ∉ Subgroup.zpowers e := by
    intro hmem
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
    apply hb1
    have h1 : alpha148 A Y a₀ ha₀ ∈ img148 A Y J ⊓
        Subgroup.centralizer (img148 A Y J : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) := by
      refine ⟨hbJ, ?_⟩
      have e1 : alpha148 A Y a₀ ha₀ = alpha148 A Y e he ^ k := by
        subst hk
        rw [alpha148_eq_mk', alpha148_eq_mk', ← map_zpow]
        rfl
      rw [e1]
      exact Subgroup.zpow_mem _ heJ k
    rw [hZ] at h1
    exact h1
  have hNHJ : ¬ AllPointsHJ A := by
    intro hall
    obtain ⟨Le', hLe', ⟨φ⟩⟩ := hall e heΩ
    have h3 : 3 ∣ Nat.card Le' := by
      have hc : Nat.card (↥Le' ⧸ aschbacherSolvableCore 3 ↥Le') = 604800 := by
        rw [Nat.card_congr φ.toEquiv, KFacts.KS14.card_nativeJ2]
      have hdvd := Subgroup.card_quotient_dvd_card (aschbacherSolvableCore 3 ↥Le')
      rw [hc] at hdvd
      exact (by norm_num : (3 : ℕ) ∣ 604800).trans hdvd
    have hLL : Le' = Le := (h.chosen136.2 e heΩ Le hLeA).2 Le' hLe'.1 h3
    subst hLL
    obtain ⟨hp, hJpi⟩ := isoLThreePi_of_isZ3PGLThreeAt148 hpgl' hJp hJnt hAN
    have hKpi : Sec4.IsoLThreePi ↥(img148 A Y K) p f := by
      rw [hJeq]
      exact hJpi
    have hKJ2 : IsEmpty (↥(img148 A Y K) ≃* CFSG.Blueprint.NativeSporadic.J2) :=
      ⟨fun χ => KFacts.KS14.ks17J2NotList.1 p f
        (isoLThreePi_of_mulEquiv148 (p := p) (e := f) χ.symm hKpi)⟩
    exact false_of_kType148_j2 hkt hKJ2 φ
      (Sec15.center_eq_bot_of_types hLe'.1 (h.chosen136.2 e heΩ Le' hLe').1)
  have hLB : ∀ B' : Subgroup G, IsHyperplane A B' → lB A B' = ⊥ :=
    fun B' hB' => lB_eq_bot_of_not_allPointsHJ h134 CFSG.Sporadic.J2.isSimpleGroup_J2 h48
      h415 (KFacts.KS14.center_nativeJ2_eq_bot h415) h hNHJ hB'
  have hAc : IsMulCommutative ↥(img148 A Y A) :=
    Item148PtRes.isMulCommutative_img148 hcomm
  have hQJ : ∀ Q' ∈ scriptQZero A (lB A), Q' ≤ Y → img148 A Y Q' ≤ img148 A Y J ⊔
      Subgroup.centralizer (img148 A Y J : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) := by
    intro Q' hQ' hQ'Y
    have hQ'M : Q' ≤ Y ⊔ A := hQ'Y.trans le_sup_left
    have hQ'3 : ¬ 3 ∣ Nat.card Q' :=
      (isPiSubgroup_piCompl_iff Nat.prime_three Q').mp hQ'.1.1.2.1
    have hcomm' : img148 A Y Q' = ⁅img148 A Y Q', img148 A Y A⁆ := by
      rw [← Item148PtRes.img148_commutator hQ'M le_sup_right, ← hQ'.2]
    exact kf148PGLInnerV _ (img148 A Y J) (img148 A Y A) (img148 A Y Q') p f hf hpgl' hJp hAc
      hAN (hnorm Q' hQ' hQ'Y) (img148_le_normalizer hQ'.1.1.2.2)
      (Item148PtRes.not_three_dvd_card_img148 hQ'3) hcomm'
  have hKF' : ∀ (t : G) (ht : t ∈ A), ∃ s ∈ img148 A Y J ⊓
      Subgroup.centralizer ({alpha148 A Y a₀ ha₀} : Set (↥(Y ⊔ A) ⧸ ker148 A Y)),
      ∀ y ∈ pPrimeCoreOf 3 (img148 A Y J ⊓
        Subgroup.centralizer ({alpha148 A Y a₀ ha₀} : Set (↥(Y ⊔ A) ⧸ ker148 A Y))),
        alpha148 A Y t ht * y * (alpha148 A Y t ht)⁻¹ = s * y * s⁻¹ := by
    intro t ht
    have hta : alpha148 A Y t ht * alpha148 A Y a₀ ha₀ =
        alpha148 A Y a₀ ha₀ * alpha148 A Y t ht := by
      rw [← alpha148_mul, ← alpha148_mul]
      congr 1
      exact hcomm t ht a₀ ha₀
    exact hKF _ (img148 A Y J) (img148 A Y A) p f hf hpgl' hJp hAN _ hbJ hb1
      (hAbar3 _ hbA) _ (Subgroup.mem_sup_right (alpha148_mem_img148 ht)) hta
  have hpass := img148_deltaZero_le_sup148 hA hAY hJY hAJ he he1 ha₀ hbJ ha₀e heJ hZ hKF' hLB hQJ
  exact inf_le_left.trans (hpass.trans (sup_le le_rfl hD1))

end Steps

end CFSG.RankThree.PartTwo.Sec14.Ronan148N
