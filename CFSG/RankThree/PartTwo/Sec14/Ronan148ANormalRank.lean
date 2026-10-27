module

public import CFSG.RankThree.PartTwo.Sec14.Item148Steps
import CFSG.RankThree.PartTwo.Sec14.Ronan148ANormal
import CFSG.RankThree.PartTwo.Sec14.Ronan148ANormalGroup
import CFSG.RankThree.PartTwo.Sec14.Ronan148JStruct
import CFSG.RankThree.PartTwo.Sec14.Item148OneRepairProofCore
import CFSG.RankThree.PartTwo.Sec14.Item148MainProofKTypeTheta
import CFSG.RankThree.PartTwo.Sec14.Item148Res5ProofImgLe
import CFSG.RankThree.PartTwo.Sec19.Step1914Tri
import CFSG.Quasithin.EmptyFaithful.S1422Basic
import CFSG.RankThree.PartTwo.Sec14.Concl143Std

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan148A

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec14
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.LocalRank CFSG.GH74.GLS

variable {G : Type} [Group G] [Finite G]


theorem normal_of_rank {A L : Subgroup G} {c : G} (h : Sec14Std G A c L) {Y : Subgroup G}
    (hY : Y ∈ scriptY A) [(ker148 A Y).Normal] {B Q : Subgroup G} {e : G} {K Le : Subgroup G}
    (hP : IsPoint148 A (lB A) Y B Q e K Le) (hkt : KType148 A Y e K Le) (he : e ∈ A)
    {J : Subgroup G} (hJ : J ∈ thetaComponentsIn Y) (hKJ : K ≤ J)
    (hAJ : A ≤ Subgroup.normalizer (J : Set G))
    (halt : Lift148Eq A Y K J ∨ Lift148Ten A Y K J ∨ Lift148Field A Y e he K J)
    (hA : A = Subgroup.zpowers e ⊔ (A ⊓ J))
    (hXJ : img148 A Y (deltaZero A (lB A) Y) = img148 A Y J) :
    (((deltaZero A (lB A) Y).subgroupOf Y).map
      (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥Y))).Normal := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hA27 : Late.IsE27 A := h.isE27'
  have hAF : A ∈ partTwoF G := h.mem_partTwoF
  have hAY : A ≤ Subgroup.normalizer (Y : Set G) := hY.2
  have hA3 : ∀ a ∈ A, a ^ 3 = 1 := hAF.1.2
  have hAc : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hA27.1.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hJY : J ≤ Y := le_of_mem_thetaComponentsIn hJ
  have hJM : J ≤ Y ⊔ A := hJY.trans le_sup_left
  have hKYC : K ≤ Y ⊓ Subgroup.centralizer ({e} : Set G) :=
    le_of_mem_thetaComponentsIn hP.2.2.2.2.2.1
  have hKM : K ≤ Y ⊔ A := (hKYC.trans inf_le_left).trans le_sup_left
  have hKe : K ≤ Subgroup.centralizer {e} := hKYC.trans inf_le_right
  have he1 : e ≠ 1 := hP.2.2.2.2.1
  have : Group.IsPerfect ↥J := isPerfect_of_mem_thetaComponentsIn hJ
  have hJp : Group.IsPerfect ↥(img148 A Y J) := isPerfect_img148 hJM
  have hJs : IsSimpleGroup ↥(img148 A Y J) := by
    rcases halt with hEq | hTen | ⟨n, hn, -, hJn, -⟩
    · have h1 := isSimpleGroup_img148_of_kType148 h hkt
      rw [show img148 A Y K = img148 A Y J from hEq] at h1
      exact h1
    · obtain ⟨φ⟩ := hTen.2
      have : IsSimpleGroup (alternatingGroup (Fin 10)) := alternatingGroup.isSimpleGroup (by simp)
      exact MulEquiv.isSimpleGroup φ
    · rcases hJn with ⟨-, ⟨φ⟩⟩ | ⟨-, ⟨φ⟩⟩
      · have := Sec19.Step1914TriProof.isSimpleGroup_projSL_three_of_field (GaloisField 2 (3 * n))
        exact MulEquiv.isSimpleGroup φ
      · have := Sec19.Step1914TriProof.isSimpleGroup_projSU_three_of_ne_two 2 (3 * n)
          (by omega) (by
            have : 2 ^ 3 ≤ 2 ^ (3 * n) := Nat.pow_le_pow_right (by norm_num) (by omega)
            omega)
        exact MulEquiv.isSimpleGroup φ
  obtain ⟨hJc, hJZ⟩ := Item148Res5.isComponent_img148 hAY hJ hJs
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
  have hKAc := img148_inf_centralizer_eq hKM he hKe hkt.1 rfl
  have hAJc : img148 A Y A ⊓
      Subgroup.centralizer (img148 A Y J : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) ≤
        Subgroup.zpowers (alpha148 A Y e he) := by
    rw [← hKAc]
    exact inf_le_inf_left _ (Subgroup.centralizer_le (img148_mono hKJ))
  have hF3 : ∀ w : ↥(Y ⊔ A) ⧸ ker148 A Y,
      w ∈ Subgroup.centralizer (img148 A Y A : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) →
        w ^ 3 = 1 → w ∈ img148 A Y A := fun w hw hw3 => mem_img148_of_commute hAF hAY hw hw3
  have hFJ : img148 A Y (A ⊓ J) ≤ img148 A Y J := img148_mono inf_le_right
  have hAeq : img148 A Y A = Subgroup.zpowers (alpha148 A Y e he) ⊔ img148 A Y (A ⊓ J) := by
    refine le_antisymm ?_ (sup_le ((Subgroup.zpowers_le).mpr (alpha148_mem_img148 he))
      (img148_mono inf_le_left))
    have hle : img148 A Y A ≤
        img148 A Y (Subgroup.zpowers e) ⊔ img148 A Y (A ⊓ J) := by
      rw [← img148_sup ((Subgroup.zpowers_le.mpr he).trans le_sup_right)
        (inf_le_left.trans le_sup_right)]
      exact img148_mono hA.le
    exact hle.trans (sup_le_sup_right (img148_zpowers_le he) _)
  have he3 : alpha148 A Y e he ^ 3 = 1 := alpha148_pow_three hA3 he
  have hord : orderOf e = 3 := orderOf_eq_prime (hA3 e he) he1
  have hprod := Item148OneRepair.card_sup_mul_card_inf148 (A := Subgroup.zpowers e) (B := A ⊓ J)
    (fun x hx => Subgroup.mem_normalizer_iff.mpr fun y => by
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
      have hxA : e ^ k ∈ A := A.zpow_mem he k
      constructor
      · intro hy
        have hyA : y ∈ A := hy.1
        rw [hAc _ hxA y hyA, mul_inv_cancel_right]
        exact hy
      · intro hy
        have hyA : y ∈ A := by
          have := A.mul_mem (A.mul_mem (A.inv_mem hxA) hy.1) hxA
          simpa [mul_assoc] using this
        rwa [hAc _ hxA y hyA, mul_inv_cancel_right] at hy)
  rw [← hA, hA27.2, Nat.card_zpowers, hord] at hprod
  have hcardAJ : Nat.card (img148 A Y (A ⊓ J)) = Nat.card (A ⊓ J : Subgroup G) :=
    Ronan148J.card_img148_of_le hA3 inf_le_left
  have hconj : ∀ x : ↥(Y ⊔ A) ⧸ ker148 A Y,
      (img148 A Y J).map (MulAut.conj x).toMonoidHom = img148 A Y J := by
    by_cases heC : alpha148 A Y e he ∈
        Subgroup.centralizer (img148 A Y J : Set (↥(Y ⊔ A) ⧸ ker148 A Y))
    ·
      have heJ : e ∉ J := by
        intro heJ
        have hmem : alpha148 A Y e he ∈ img148 A Y J ⊓
            Subgroup.centralizer (img148 A Y J : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) :=
          ⟨mem_img148_iff.mpr ⟨e, Subgroup.mem_sup_right he, heJ, rfl⟩, heC⟩
        rw [hZ, Subgroup.mem_bot] at hmem
        exact he1 (alpha148_injective hA3 he (one_mem A) (hmem.trans (map_one _).symm))
      have hinf : (Subgroup.zpowers e ⊓ (A ⊓ J) : Subgroup G) = ⊥ := by
        rw [eq_bot_iff]
        intro x hx
        obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx.1
        by_contra hk
        have hx1 : e ^ k ≠ 1 := fun h' => hk (by rw [h']; exact Subgroup.one_mem _)
        have : e ∈ Subgroup.zpowers (e ^ k) := by
          have hle : Subgroup.zpowers (e ^ k) ≤ Subgroup.zpowers e :=
            Subgroup.zpowers_le.mpr (Subgroup.zpow_mem_zpowers e k)
          have hord' : orderOf (e ^ k) = 3 :=
            orderOf_eq_prime (by rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul,
              zpow_natCast, hA3 e he, one_zpow]) hx1
          have heq := Subgroup.eq_of_le_of_card_ge hle
            (by rw [Nat.card_zpowers, Nat.card_zpowers, hord, hord'])
          rw [heq]
          exact Subgroup.mem_zpowers e
        exact heJ ((Subgroup.zpowers_le.mpr hx.2.2) this)
      rw [hinf, Subgroup.card_bot] at hprod
      have h9 : Nat.card (img148 A Y (A ⊓ J)) = 9 := by omega
      have hB₀3 : ∀ b ∈ img148 A Y (A ⊓ J), b ^ 3 = 1 := fun b hb => by
        obtain ⟨a, ha, haAJ, rfl⟩ := mem_img148_iff.mp hb
        rw [← map_pow]
        have : (⟨a, ha⟩ : ↥(Y ⊔ A)) ^ 3 = 1 := Subtype.ext (by simpa using hA3 a haAJ.1)
        rw [this, map_one]
      have he1' : alpha148 A Y e he ≠ 1 := fun h' =>
        he1 (alpha148_injective hA3 he (one_mem A) (h'.trans (map_one _).symm))
      exact map_conj_eq_of_rank_two hJc hFJ h9 hB₀3 he1' he3 heC hAeq hF3 hAJc
    ·
      have h3 : 3 ∣ Nat.card ↥(img148 A Y J) := by
        have hle9 : 9 ≤ Nat.card (A ⊓ J : Subgroup G) := by
          have := Nat.card_pos (α := ↥(Subgroup.zpowers e ⊓ (A ⊓ J) : Subgroup G))
          nlinarith
        have hAJ3 : IsPGroup 3 (A ⊓ J : Subgroup G) :=
          isPGroup_three_of_pow148 fun a ha => hA3 a ha.1
        obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hAJ3
        have hk1 : 1 ≤ k := by
          by_contra hk0
          push Not at hk0
          interval_cases k
          rw [hk] at hle9
          norm_num at hle9
        have h3AJ : 3 ∣ Nat.card (A ⊓ J : Subgroup G) := by
          rw [hk]
          exact dvd_pow_self 3 (by omega)
        rw [← hcardAJ] at h3AJ
        exact h3AJ.trans (Subgroup.card_dvd_of_le hFJ)
      exact map_conj_eq_of_not_mem_centralizer hJc h3 he3
        (img148_le_normalizer hAJ (alpha148_mem_img148 he)) heC hFJ hAeq hF3 hAJc
  refine map_normal_of_img148_eq (sSup_le fun _ hQ => hQ.2) hXJ fun y hy => ?_
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  exact hconj _

end CFSG.RankThree.PartTwo.Sec14.Ronan148A
