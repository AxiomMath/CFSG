module

public import CFSG.RankThree.PartTwo.Sec5.Item56
import CFSG.LocalAnalysis.RankThreeEvenClassification.CoprimeFactorization
import CFSG.RankThree.PartTwo.Source.OrderThreeMinimalTwoGroup
import CFSG.RankThree.PartTwo.Source.MinimalFaithfulCentralProduct
import CFSG.RankThree.Literature.ThompsonDihedralCore
import CFSG.SignalizerFunctorTheorem.MinimalAction.ElemAbelian
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.CardSupOfDisjointNormalizer

public section

namespace CFSG.RankThree.PartTwo.Sec5

open CFSG

universe u

variable {G : Type u} [Group G] [Finite G]

omit [Finite G] in
theorem eq_one_of_eq_inv_of_pow_three {y : G} (h : y = y⁻¹) (h3 : y ^ 3 = 1) : y = 1 := by
  have h2 : y * y = 1 := by
    calc y * y = y * y⁻¹ := by rw [← h]
      _ = 1 := mul_inv_cancel y
  calc y = y ^ 3 * (y * y)⁻¹ := by group
    _ = 1 := by rw [h3, h2]; simp

omit [Finite G] in
theorem mem_centralizer_singleton_comm {a b : G}
    (h : a ∈ Subgroup.centralizer ({b} : Set G)) : b ∈ Subgroup.centralizer ({a} : Set G) :=
  Subgroup.mem_centralizer_singleton_iff.mpr (Subgroup.mem_centralizer_singleton_iff.mp h).symm

theorem isElemAbelian_sup_zpowers_of_inv {E : Subgroup G} (hE : CFSG.Assembly.IsElemAbelian 3 E)
    {t y : G} (hEt : E ≤ Subgroup.centralizer ({t} : Set G))
    (hEy : E ≤ Subgroup.centralizer ({y} : Set G)) (hinv : t * y * t⁻¹ = y⁻¹) (hy1 : y ≠ 1)
    (hy3 : y ^ 3 = 1) :
    CFSG.Assembly.IsElemAbelian 3 (E ⊔ Subgroup.zpowers y) ∧
      Nat.card (E ⊔ Subgroup.zpowers y : Subgroup G) = Nat.card E * 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine isElemAbelian_sup_zpowers hE ?_ hy3 fun e he =>
    Subgroup.mem_centralizer_singleton_iff.mp (hEy he)
  intro hyE
  have hty : t * y * t⁻¹ = y := by
    rw [← Subgroup.mem_centralizer_singleton_iff.mp (hEt hyE), mul_inv_cancel_right]
  rw [hty] at hinv
  exact hy1 (eq_one_of_eq_inv_of_pow_three hinv hy3)

theorem rank3II_5_8 {A S U : Subgroup G} (h : SectionFiveHyp A S)
    (hU : IsNormalFourGroup A S U) :
    ⁅S, A ⊓ Subgroup.centralizer (U : Set G)⁆ = ⊥ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hB9 : Nat.card (A ⊓ Subgroup.centralizer (U : Set G) : Subgroup G) = 9 :=
    card_inf_centralizer_fourGroup h hU
  set B := A ⊓ Subgroup.centralizer (U : Set G) with hBdef
  have hBA : B ≤ A := inf_le_left
  have hBel : CFSG.Assembly.IsElemAbelian 3 B := isElemAbelian_of_le h.elemAbelian hBA
  have hUB : U ≤ Subgroup.centralizer (B : Set G) :=
    Subgroup.le_centralizer_iff.mp inf_le_right
  have hS2 := h.isPGroup
  have hcop2 : ∀ X : Subgroup G, X ≤ S → Nat.Coprime 3 (Nat.card X) := fun X hX => by
    obtain ⟨k, hk⟩ := (hS2.to_le hX).exists_card_eq
    rw [hk]
    exact Nat.Coprime.pow_right k (by norm_num)
  have hAcomm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (h.elemAbelian.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hAcen : ∀ x ∈ A, ∀ y ∈ A, x ∈ Subgroup.centralizer ({y} : Set G) := fun x hx y hy =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hAcomm x hx y hy)
  have hUZ := le_centralizer_fourGroup h hU
  have h55 := rank3II_5_5 h hBA hB9
  by_contra hSB
  obtain ⟨c, hcB, hc1, hcS⟩ : ∃ c ∈ B, c ≠ 1 ∧
      ¬ S ⊓ Subgroup.centralizer ({c} : Set G) ≤ Subgroup.centralizer (B : Set G) := by
    by_contra hno
    push Not at hno
    apply hSB
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    exact le_of_forall_inf_centralizer_le Nat.prime_three hBel (by norm_num [hB9])
      (hBA.trans h.le_normalizer) (hcop2 S le_rfl) hno
  have hcA : c ∈ A := hBA hcB
  have hAS₁ : A ≤ Subgroup.normalizer
      ((S ⊓ Subgroup.centralizer ({c} : Set G) : Subgroup G) : Set G) := fun x hx =>
    Subgroup.inf_normalizer_le_normalizer_inf
      ⟨h.le_normalizer hx, Subgroup.le_normalizer (hAcen x hx c hcA)⟩
  obtain ⟨H, hHA, hH9, hHS⟩ : ∃ H : Subgroup G, H ≤ A ∧ Nat.card H = 3 ^ 2 ∧
      ¬ (S ⊓ Subgroup.centralizer ({c} : Set G)) ⊓ Subgroup.centralizer (H : Set G) ≤
        Subgroup.centralizer (B : Set G) := by
    by_contra hno
    push Not at hno
    exact hcS (le_of_forall_inf_centralizer_sub_le (k := 2) Nat.prime_three h.elemAbelian
      (by norm_num [h.card_eq]) hAS₁ (hcop2 _ inf_le_left) hno)
  have hHB : ¬ H ≤ B := by
    intro hHB
    have hHeq : H = B := Subgroup.eq_of_le_of_card_ge hHB (by rw [hB9, hH9]; norm_num)
    apply hHS
    rw [hHeq]
    exact inf_le_right
  obtain ⟨a, haH, haB⟩ := IsConcreteLE.not_le_iff_exists.mp hHB
  have haA : a ∈ A := hHA haH
  have haU : a ∉ Subgroup.centralizer (U : Set G) := fun h' =>
    haB (Subgroup.mem_inf.mpr ⟨haA, h'⟩)
  have hUa : ∀ x ∈ U, a * x = x * a → x = 1 := by
    intro x hx hax
    by_contra hx1
    exact haU (mem_centralizer_of_fourGroup hU.elemAbelian hU.card_eq
      (hU.le_normalizer_right haA) (h.elemAbelian.2 a haA) hx hx1 hax)
  set S₂ := (S ⊓ Subgroup.centralizer ({c} : Set G)) ⊓ Subgroup.centralizer ({a} : Set G)
    with hS₂def
  have hS₂B : ¬ S₂ ≤ Subgroup.centralizer (B : Set G) := fun hle =>
    hHS ((inf_le_inf_left _ (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr haH))).trans
      hle)
  have hS₂S : S₂ ≤ S := inf_le_left.trans inf_le_left
  have hS₂c : S₂ ≤ Subgroup.centralizer ({c} : Set G) := inf_le_left.trans inf_le_right
  have hS₂a : S₂ ≤ Subgroup.centralizer ({a} : Set G) := inf_le_right
  obtain ⟨s, hsS₂, hsB⟩ := IsConcreteLE.not_le_iff_exists.mp hS₂B
  rw [Subgroup.mem_centralizer_iff] at hsB
  push Not at hsB
  obtain ⟨b, hbB, hbs⟩ := hsB
  have hbA : b ∈ A := hBA hbB
  have hb3 : b ^ 3 = 1 := hBel.2 b hbB
  have hb1 : b ≠ 1 := by
    rintro rfl
    exact hbs (by rw [one_mul, mul_one])
  have hbc : b ∉ Subgroup.zpowers c := by
    intro hb
    have hcs : c ∈ Subgroup.centralizer ({s} : Set G) := mem_centralizer_singleton_comm (hS₂c hsS₂)
    exact hbs (Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.zpowers_le.mpr hcs hb))
  have hcb : ∀ x ∈ Subgroup.zpowers c, x * b = b * x := fun x hx =>
    congrArg Subtype.val (hBel.1.is_comm.comm ⟨x, Subgroup.zpowers_le.mpr hcB hx⟩ ⟨b, hbB⟩)
  obtain ⟨-, hcbcard⟩ := isElemAbelian_sup_zpowers
    (isElemAbelian_of_le hBel (Subgroup.zpowers_le.mpr hcB)) hbc hb3 hcb
  have hc3 : c ^ 3 = 1 := hBel.2 c hcB
  have hccard : Nat.card (Subgroup.zpowers c) = 3 := by
    rw [Nat.card_zpowers, orderOf_eq_prime hc3 hc1]
  have hBeq : Subgroup.zpowers c ⊔ Subgroup.zpowers b = B :=
    Subgroup.eq_of_le_of_card_ge
      (sup_le (Subgroup.zpowers_le.mpr hcB) (Subgroup.zpowers_le.mpr hbB))
      (by rw [hcbcard, hccard, hB9])
  have hCB : ∀ z : G, z ∈ Subgroup.centralizer ({c} : Set G) →
      z ∈ Subgroup.centralizer ({b} : Set G) → z ∈ Subgroup.centralizer (B : Set G) := by
    intro z hzc hzb
    rw [← hBeq, Source.centralizer_sup_eq, Subgroup.zpowers_eq_closure,
      Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure, Subgroup.centralizer_closure]
    exact Subgroup.mem_inf.mpr ⟨hzc, hzb⟩
  have hbcard : Nat.card (Subgroup.zpowers b) = 3 := by
    rw [Nat.card_zpowers, orderOf_eq_prime hb3 hb1]
  have hb3' : IsPGroup 3 (Subgroup.zpowers b) := IsPGroup.of_card (n := 1) (by rw [hbcard, pow_one])
  have hbN : Subgroup.zpowers b ≤ Subgroup.normalizer (S₂ : Set G) := by
    rw [Subgroup.zpowers_le]
    exact Subgroup.inf_normalizer_le_normalizer_inf ⟨hAS₁ hbA,
      Subgroup.le_normalizer (hAcen b hbA a haA)⟩
  have hS₂2 : IsPGroup 2 S₂ := hS2.to_le hS₂S
  have hS₂3 : ¬ 3 ∣ Nat.card S₂ := Source.not_three_dvd_card_of_isPGroup_two hS₂2
  have hidem := CFSG.RankThreeEvenClassification.Helpers.coprime_commutator_idempotent 3
    Nat.prime_three (Subgroup.zpowers b) S₂ hb3' hS₂3 hbN
  have hRbot : ⁅S₂, Subgroup.zpowers b⁆ ≠ ⊥ := by
    intro hR
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer] at hR
    exact hbs (Subgroup.mem_centralizer_iff.mp (hR hsS₂) b (Subgroup.mem_zpowers b))
  have hRS₂ : ⁅S₂, Subgroup.zpowers b⁆ ≤ S₂ :=
    Subgroup.le_normalizer_iff_commutator_le_left.mp hbN
  obtain ⟨V, ⟨hVS₂, hVX, hVbot⟩, hVmin⟩ := Source.exists_minimal_subgroup
    (fun W : Subgroup G => W ≤ S₂ ∧ ⁅W, Subgroup.zpowers b⁆ = W ∧ W ≠ ⊥) ⟨hRS₂, hidem, hRbot⟩
  have hVS : V ≤ S := hVS₂.trans hS₂S
  have hVc : V ≤ Subgroup.centralizer ({c} : Set G) := hVS₂.trans hS₂c
  have hVa : V ≤ Subgroup.centralizer ({a} : Set G) := hVS₂.trans hS₂a
  have hbV : b ∈ Subgroup.normalizer (V : Set G) :=
    Subgroup.le_normalizer_iff_commutator_le_left.mpr hVX.le (Subgroup.mem_zpowers b)
  have h34 := Source.kleinFour_or_quaternion_of_minimal_commutator hbcard (hS2.to_le hVS) hVX
    hVbot fun S' hS'V hS'X hS'bot => hVmin S' hS'V ⟨hS'V.trans hVS₂, hS'X, hS'bot⟩
  rcases h34 with hV4 | hQ
  ·
    have hV4card : Nat.card V = 4 := hV4.card_four
    have hVel : CFSG.Assembly.IsElemAbelian 2 V := ⟨IsKleinFour.isMulCommutative, fun x hx => by
      rw [pow_two]
      exact congrArg Subtype.val (IsKleinFour.mul_self (⟨x, hx⟩ : V))⟩
    have hVUcomm : ∀ x ∈ V, ∀ y ∈ U, x * y = y * x := fun x hx y hy =>
      Subgroup.mem_centralizer_iff.mp (hUZ hy) x (hVS hx)
    have hTel : CFSG.Assembly.IsElemAbelian 2 (V ⊔ U) :=
      CFSG.SignalizerFunctorTheorem.MinimalAction.isElemAbelian_sup hVel hU.elemAbelian hVUcomm
    have hUV : U ≤ Subgroup.normalizer (V : Set G) := fun y hy =>
      Subgroup.centralizer_le_normalizer _
        (Subgroup.mem_centralizer_iff.mpr fun x hx => hVUcomm x hx y hy)
    have hVUdisj : Disjoint V U := by
      rw [Subgroup.disjoint_def]
      intro x hxV hxU
      exact hUa x hxU (Subgroup.mem_centralizer_singleton_iff.mp (hVa hxV)).symm
    have hTcard : Nat.card (V ⊔ U : Subgroup G) = 2 ^ 4 := by
      rw [CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer V U hUV hVUdisj,
        hV4card, hU.card_eq]
      norm_num
    have hcC : Subgroup.centralizer (B : Set G) ≤ Subgroup.centralizer ({c} : Set G) :=
      Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hcB)
    have hTc : V ⊔ U ≤ Subgroup.centralizer ({c} : Set G) := sup_le hVc (hUB.trans hcC)
    set P := CFSG.pCore 3 G with hPdef
    have hP3 : IsPGroup 3 P := CFSG.pCore_isPGroup
    have hNP : ∀ g : G, g ∈ Subgroup.normalizer (P : Set G) := fun g => by
      rw [Subgroup.normalizer_eq_top]
      exact Subgroup.mem_top g
    have hX3 : IsPGroup 3 (P ⊓ Subgroup.centralizer ({c} : Set G) : Subgroup G) :=
      hP3.to_le inf_le_left
    have hTX : V ⊔ U ≤ Subgroup.normalizer
        ((P ⊓ Subgroup.centralizer ({c} : Set G) : Subgroup G) : Set G) := fun t ht =>
      Subgroup.inf_normalizer_le_normalizer_inf ⟨hNP t, Subgroup.le_normalizer (hTc ht)⟩
    have hCzc : Subgroup.centralizer ((Subgroup.zpowers c : Subgroup G) : Set G) =
        Subgroup.centralizer ({c} : Set G) := by
      rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
    have hfaith : (V ⊔ U) ⊓ Subgroup.centralizer
        ((P ⊓ Subgroup.centralizer ({c} : Set G) : Subgroup G) : Set G) = ⊥ := by
      set K := (V ⊔ U) ⊓ Subgroup.centralizer
        ((P ⊓ Subgroup.centralizer ({c} : Set G) : Subgroup G) : Set G) with hKdef
      have hKS : K ≤ S := inf_le_left.trans (sup_le hVS hU.le)
      have hK3 : ¬ 3 ∣ Nat.card K := Source.not_three_dvd_card_of_isPGroup_two (hS2.to_le hKS)
      have hzc3 : IsPGroup 3 (Subgroup.zpowers c) :=
        isPGroup_of_isElemAbelian (isElemAbelian_of_le hBel (Subgroup.zpowers_le.mpr hcB))
      have hPc3 : IsPGroup 3 ((P ⊔ Subgroup.zpowers c : Subgroup G)) :=
        IsPGroup.to_sup_of_normal_left' hP3 hzc3 (fun x _ => hNP x)
      have hKc : K ≤ Subgroup.centralizer ((Subgroup.zpowers c : Subgroup G) : Set G) := by
        rw [hCzc]
        exact inf_le_left.trans hTc
      have hKT : K ≤ Subgroup.normalizer ((P ⊔ Subgroup.zpowers c : Subgroup G) : Set G) :=
        fun k hk => Subgroup.inf_normalizer_le_normalizer_sup P (Subgroup.zpowers c)
          ⟨hNP k, Subgroup.centralizer_le_normalizer _ (hKc hk)⟩
      have hzcc : Subgroup.zpowers c ≤
          Subgroup.centralizer ((Subgroup.zpowers c : Subgroup G) : Set G) := by
        rw [hCzc, Subgroup.zpowers_le, Subgroup.mem_centralizer_singleton_iff]
      have hfix : K ≤ Subgroup.centralizer
          (((P ⊔ Subgroup.zpowers c) ⊓ Subgroup.centralizer
            ((Subgroup.zpowers c : Subgroup G) : Set G) : Subgroup G) : Set G) := by
        refine le_trans ?_ (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr
          (sup_inf_centralizer_le (fun x _ => hNP x) hzcc)))
        rw [Source.centralizer_sup_eq, hCzc]
        exact le_inf inf_le_right (hKc.trans hCzc.le)
      have hKP := Source.le_centralizer_of_le_centralizer_inf_centralizer hPc3 hK3 le_sup_right
        hKT hKc hfix
      have hKC : K ≤ S ⊓ Subgroup.centralizer (P : Set G) :=
        le_inf hKS (hKP.trans (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr le_sup_left)))
      rw [rank3II_5_3 h] at hKC
      exact le_bot_iff.mp hKC
    have hnil : ∀ H : Subgroup G, H ≤ P ⊓ Subgroup.centralizer ({c} : Set G) →
        Group.IsNilpotent H := fun H hH => (hX3.to_le hH).isNilpotent
    have hodd : Odd (Nat.card (P ⊓ Subgroup.centralizer ({c} : Set G) : Subgroup G)) := by
      obtain ⟨k, hk⟩ := hX3.exists_card_eq
      rw [hk]
      exact Odd.pow ⟨1, by norm_num⟩
    have hTcomm : ∀ s ∈ V ⊔ U, ∀ t ∈ V ⊔ U, s * t = t * s := fun s hs t ht =>
      congrArg Subtype.val (hTel.1.is_comm.comm ⟨s, hs⟩ ⟨t, ht⟩)
    have hTinv : ∀ t ∈ V ⊔ U, t * t = 1 := fun t ht => by
      rw [← pow_two]
      exact hTel.2 t ht
    obtain ⟨Ai, ti, hDB⟩ := CFSG.RankThree.Literature.Thompson534.exists_dihedral_basis 4 hnil
      hodd hTcomm hTinv hTcard hTX hfaith
    have hAi3 : ∀ i, Nat.card (Ai i) = 3 := by
      intro i
      have hp := hDB.prime i
      obtain ⟨k, hk⟩ := (hX3.to_le (hDB.le i)).exists_card_eq
      rw [hk] at hp ⊢
      exact ((Nat.Prime.pow_eq_iff hp).mp rfl).1.symm
    have hgen : ∀ i, ∃ x ∈ Ai i, x ≠ 1 ∧ Ai i = Subgroup.zpowers x := fun i =>
      exists_eq_zpowers_of_card_eq_prime Nat.prime_three (hAi3 i)
    choose x hxA hx1 _hxeq using hgen
    have hx3 : ∀ i, x i ^ 3 = 1 := fun i => by
      have h1 := orderOf_dvd_iff_pow_eq_one.mp (Subgroup.orderOf_dvd_natCard (Ai i) (hxA i))
      rwa [hAi3 i] at h1
    have hxc : ∀ i, c ∈ Subgroup.centralizer ({x i} : Set G) := fun i =>
      mem_centralizer_singleton_comm (Subgroup.mem_inf.mp ((hDB.le i) (hxA i))).2
    have htc : ∀ i, c ∈ Subgroup.centralizer ({ti i} : Set G) := fun i =>
      mem_centralizer_singleton_comm (hTc (hDB.mem i))
    have htx : ∀ i j, i ≠ j → x j ∈ Subgroup.centralizer ({ti i} : Set G) := fun i j hij =>
      Subgroup.mem_centralizer_singleton_iff.mpr
        (Subgroup.mem_centralizer_iff.mp (hDB.mem_centralizer i j hij) (x j) (hxA j))
    have hxx : ∀ i j, i ≠ j → x i ∈ Subgroup.centralizer ({x j} : Set G) := fun i j hij =>
      Subgroup.mem_centralizer_singleton_iff.mpr (hDB.comm hij (x i) (hxA i) (x j) (hxA j)).eq
    have hE₁ : CFSG.Assembly.IsElemAbelian 3 (Subgroup.zpowers c) :=
      isElemAbelian_of_le hBel (Subgroup.zpowers_le.mpr hcB)
    have hE₂ := isElemAbelian_sup_zpowers_of_inv hE₁ (Subgroup.zpowers_le.mpr (htc 1))
      (Subgroup.zpowers_le.mpr (hxc 1)) (hDB.inv 1 (x 1) (hxA 1)) (hx1 1) (hx3 1)
    have hE₃ := isElemAbelian_sup_zpowers_of_inv hE₂.1
      (sup_le (Subgroup.zpowers_le.mpr (htc 2)) (Subgroup.zpowers_le.mpr (htx 2 1 (by decide))))
      (sup_le (Subgroup.zpowers_le.mpr (hxc 2)) (Subgroup.zpowers_le.mpr (hxx 1 2 (by decide))))
      (hDB.inv 2 (x 2) (hxA 2)) (hx1 2) (hx3 2)
    have hE₄ := isElemAbelian_sup_zpowers_of_inv hE₃.1
      (sup_le (sup_le (Subgroup.zpowers_le.mpr (htc 3))
        (Subgroup.zpowers_le.mpr (htx 3 1 (by decide))))
        (Subgroup.zpowers_le.mpr (htx 3 2 (by decide))))
      (sup_le (sup_le (Subgroup.zpowers_le.mpr (hxc 3))
        (Subgroup.zpowers_le.mpr (hxx 1 3 (by decide))))
        (Subgroup.zpowers_le.mpr (hxx 2 3 (by decide))))
      (hDB.inv 3 (x 3) (hxA 3)) (hx1 3) (hx3 3)
    have hEt : Subgroup.zpowers c ⊔ Subgroup.zpowers (x 1) ⊔ Subgroup.zpowers (x 2) ⊔
        Subgroup.zpowers (x 3) ≤ Subgroup.centralizer ({ti 0} : Set G) :=
      sup_le (sup_le (sup_le (Subgroup.zpowers_le.mpr (htc 0))
        (Subgroup.zpowers_le.mpr (htx 0 1 (by decide))))
        (Subgroup.zpowers_le.mpr (htx 0 2 (by decide))))
        (Subgroup.zpowers_le.mpr (htx 0 3 (by decide)))
    have ht01 : ti 0 ≠ 1 := by
      intro h1
      have hinv0 := hDB.inv 0 (x 0) (hxA 0)
      rw [h1, one_mul, inv_one, mul_one] at hinv0
      exact hx1 0 (eq_one_of_eq_inv_of_pow_three hinv0 (hx3 0))
    have ht02 : ti 0 ^ 2 = 1 := by
      rw [pow_two]
      exact hTinv _ (hDB.mem 0)
    have hle := card_le_of_le_centralizer_involution h.evenRank_eq ht01 ht02 hE₄.1 hEt
    rw [hE₄.2, hE₃.2, hE₂.2, hccard] at hle
    norm_num at hle
  ·
    obtain ⟨e⟩ := hQ
    have hinvQ : ∀ q : QuaternionGroup 2, q ^ 2 = 1 → q = 1 ∨ q = QuaternionGroup.a 2 := by
      decide
    have hQa : (QuaternionGroup.a 2 : QuaternionGroup 2) ^ 2 = 1 := by decide
    have hQa1 : (QuaternionGroup.a 2 : QuaternionGroup 2) ≠ 1 := by decide
    have hzV : ((e.symm (QuaternionGroup.a 2) : V) : G) ∈ V := (e.symm (QuaternionGroup.a 2)).2
    have hz2 : ((e.symm (QuaternionGroup.a 2) : V) : G) ^ 2 = 1 := by
      rw [← Subgroup.coe_pow, ← map_pow, hQa, map_one, Subgroup.coe_one]
    have hz1 : ((e.symm (QuaternionGroup.a 2) : V) : G) ≠ 1 := by
      intro h'
      apply hQa1
      have h1 : e.symm (QuaternionGroup.a 2) = 1 := Subtype.ext h'
      rw [← e.apply_symm_apply (QuaternionGroup.a 2), h1, map_one]
    have huniq : ∀ y ∈ V, y ^ 2 = 1 → y = 1 ∨ y = ((e.symm (QuaternionGroup.a 2) : V) : G) := by
      intro y hy hy2
      have hy2' : (⟨y, hy⟩ : V) ^ 2 = 1 := Subtype.ext (by rw [Subgroup.coe_pow]; exact hy2)
      rcases hinvQ (e ⟨y, hy⟩) (by rw [← map_pow, hy2', map_one]) with h1 | h1
      · left
        have h2 : (⟨y, hy⟩ : V) = 1 := by rw [← e.symm_apply_apply ⟨y, hy⟩, h1, map_one]
        exact congrArg Subtype.val h2
      · right
        have h2 : (⟨y, hy⟩ : V) = e.symm (QuaternionGroup.a 2) := by
          rw [← h1, e.symm_apply_apply]
        exact congrArg Subtype.val h2
    set z : G := ((e.symm (QuaternionGroup.a 2) : V) : G) with hzdef
    have hbz : b * z * b⁻¹ = z := by
      have hmem : b * z * b⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.mp hbV z).mp hzV
      rcases huniq _ hmem (by rw [conj_pow, hz2, mul_one, mul_inv_cancel]) with h1 | h1
      · exact absurd (by simpa using h1) hz1
      · exact h1
    have hzb : z ∈ Subgroup.centralizer ({b} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      calc z * b = b * z * b⁻¹ * b := by rw [hbz]
        _ = b * z := by group
    have hzB : z ∈ Subgroup.centralizer (B : Set G) := hCB z (hVc hzV) hzb
    have hzS : z ∈ S := hVS hzV
    have hzU : z ∉ U := fun hzU =>
      hz1 (hUa z hzU (Subgroup.mem_centralizer_singleton_iff.mp (hVa hzV)).symm)
    obtain ⟨hE, hEcard⟩ := isElemAbelian_sup_zpowers (p := 2) hU.elemAbelian hzU hz2
      (fun u hu => (Subgroup.mem_centralizer_iff.mp (hUZ hu) z hzS).symm)
    have hEle : U ⊔ Subgroup.zpowers z ≤ S ⊓ Subgroup.centralizer (B : Set G) :=
      sup_le (le_inf hU.le hUB) (Subgroup.zpowers_le.mpr (Subgroup.mem_inf.mpr ⟨hzS, hzB⟩))
    have h3 := le_pRank_of_elemAbelian Nat.prime_two hEle hE (k := 3)
      (by simp [hEcard, hU.card_eq])
    omega

end CFSG.RankThree.PartTwo.Sec5
