module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S21rU4XD
import CFSG.LocalAnalysis.UniquenessCase.UC22P22ry
import CFSG.LocalAnalysis.UniquenessCase.UC22P22rq
import CFSG.LocalAnalysis.UniquenessCase.UC22P22c
import CFSG.LocalAnalysis.UniquenessCase.UC22InE229Cong
import CFSG.LocalAnalysis.UniquenessCase.UC22InE229NSE
import CFSG.LocalAnalysis.UniquenessCase.UC22BarImagePreimage
import CFSG.LocalAnalysis.UniquenessCase.UC6Syl
import CFSG.LocalAnalysis.EvenBN.GMSK.SzFacts

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup

variable {G : Type} [Group G] [Finite G]

theorem u4x_mem_normalizer_right {Q : Type} [Group Q] [Finite Q] {p : ℕ} [Fact p.Prime]
    {X C S : Subgroup Q} (hcomm : ∀ x ∈ X, ∀ y ∈ C, x * y = y * x) (hXC : X ⊓ C = ⊥)
    (hXn : X.Normal) (hCn : C.Normal) (hS : CFSG.ABGLocalTools.IsSylowOf p S ⊤) {x c : Q}
    (hx : x ∈ X) (hc : c ∈ C) (hN : x * c ∈ normalizer (S : Set Q)) :
    c ∈ normalizer (S : Set Q) := by
  refine Subgroup.mem_normalizer_fintype fun t ht => ?_
  have hv : t * x⁻¹ * t⁻¹ ∈ X := hXn.conj_mem _ (X.inv_mem hx) t
  have hu : c * t * c⁻¹ * t⁻¹ ∈ C := by
    rw [show c * t * c⁻¹ * t⁻¹ = c * (t * c⁻¹ * t⁻¹) by group]
    exact C.mul_mem hc (hCn.conj_mem _ (C.inv_mem hc) t)
  have e : c * t * c⁻¹ * t⁻¹ * (t * x⁻¹ * t⁻¹) = t * x⁻¹ * t⁻¹ * (c * t * c⁻¹ * t⁻¹) :=
    (hcomm _ hv _ hu).symm
  have h1 : x * (t * x⁻¹ * t⁻¹) * (c * t * c⁻¹ * t⁻¹) ∈ S := by
    have h2 : x * c * t * (x * c)⁻¹ * t⁻¹ ∈ S :=
      S.mul_mem ((Subgroup.mem_normalizer_iff.1 hN t).1 ht) (S.inv_mem ht)
    rw [show x * c * t * (x * c)⁻¹ * t⁻¹ = x * (c * t * c⁻¹ * t⁻¹ * (t * x⁻¹ * t⁻¹)) by group,
      e] at h2
    simpa only [mul_assoc] using h2
  haveI := hXn
  haveI := hCn
  obtain ⟨-, hb⟩ := u4x_mem_of_mul_mem hcomm hXC hS inferInstance (X.mul_mem hx hv) hu h1
  simpa using S.mul_mem hb ht

theorem u4x_exists_lift {M T : Subgroup G} (hTM : T ≤ M) (hOT : pCoreOf 2 M ≤ T)
    {Y : Subgroup (Bar2 M)} {c : Bar2 M} (hcY : c ∈ Y)
    (hcN : c ∈ normalizer (barImage M T : Set (Bar2 M))) (hc1 : c ≠ 1) {r : ℕ} (hr : r.Prime)
    (hcr : c ^ r = 1) :
    ∃ m : ↥M, (m : G) ∈ normalizer (T : Set G) ∧ orderOf m = r ∧ uc22p21cPi M m ∈ Y := by
  haveI : Fact r.Prime := ⟨hr⟩
  obtain ⟨m, rfl⟩ := uc22p21c_pi_surjective M c
  have hmN : (m : G) ∈ normalizer (T : Set G) := by
    have h := uc22ine229_mem_normalizer_barPreimage hcN
    rwa [barPreimage_barImage_of_pCoreOf_le hTM hOT] at h
  have hdvd : r ∣ orderOf m := by
    rw [← orderOf_eq_prime hcr hc1]
    exact orderOf_map_dvd _ m
  refine ⟨m ^ (orderOf m / r), ?_, orderOf_pow_orderOf_div (orderOf_pos m).ne' hdvd, ?_⟩
  · rw [Subgroup.coe_pow]
    exact Subgroup.pow_mem _ hmN _
  · rw [map_pow]
    exact Subgroup.pow_mem _ hcY _

theorem u4x_mem_uniqueSet {D : Data G} {L : Subgroup G} (hLM : L ≤ D.M)
    (hc2 : (conjSetOf D.M L).ncard = 2) {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2)
    (hrL : r ∣ Nat.card L)
    (hA : ∀ A : Subgroup G, A ≤ L → Nat.card A = r → A ∈ uniqueSet D.M) {z : G}
    (hzM : z ∈ D.M) (hzo : orderOf z = r) (hN : normalizer (zpowers z : Set G) ≤ D.M) :
    zpowers z ∈ uniqueSet D.M := by
  haveI : Fact r.Prime := ⟨hr⟩
  refine ⟨zpowers_le.2 hzM, fun g hg => ?_⟩
  have hz'M : g⁻¹ * z * g ∈ D.M := uc22p21c_mem_map_conj.1 (hg (mem_zpowers z))
  have hsc : SemiconjBy g (g⁻¹ * z * g) z := by
    show g * (g⁻¹ * z * g) = z * g
    group
  have hP : IsPGroup r (zpowers (g⁻¹ * z * g)) := IsPGroup.of_card (n := 1)
    (by rw [Nat.card_zpowers, SemiconjBy.orderOf_eq g hsc, hzo, pow_one])
  obtain ⟨R, hR, hzR⟩ := UC6.exists_isSylowOf_ge (zpowers_le.2 hz'M) hP
  have hRp := hR.isPGroup
  obtain ⟨k, hk⟩ := hRp.exists_card_eq
  have hRN : R ≤ normalizer (L : Set G) := fun x hx =>
    uc22p2214_mem_normalizer_of_odd hc2 (hR.le hx) (Odd.of_dvd_nat (hr.odd_of_ne_two hr2).pow
      (by rw [← hk]; exact Subgroup.orderOf_dvd_natCard R hx))
  have hRL : CFSG.ABGLocalTools.IsSylowOf r (R ⊓ L) L :=
    (hR.of_le (le_inf hR.le hRN) inf_le_left).inf_of_le_normalizer
      (le_inf hLM Subgroup.le_normalizer) inf_le_right
  have hne : L.subgroupOf R ≠ ⊥ := fun h => by
    have h1 := (CFSG.ABGLocalTools.isSylowOf_iff.1 hRL).2.2
    rw [Subgroup.subgroupOf_eq_bot, disjoint_iff] at h
    rw [inf_comm, h, Subgroup.relIndex_bot_left] at h1
    exact h1 hrL
  haveI : (L.subgroupOf R).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hRN
  haveI : Group.IsNilpotent ↥R := hRp.isNilpotent
  obtain ⟨⟨a, haL, haZ⟩, ha1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1
    (Group.IsNilpotent.inf_center_ne_bot_of_normal hne)
  have ha1' : a ≠ 1 := fun h => ha1 (Subtype.ext h)
  have hao : r ∣ orderOf a := by
    obtain ⟨j, hj⟩ := hRp a
    obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow hr).1 (orderOf_dvd_of_pow_eq_one hj)
    rcases i with _ | i
    · exact absurd (orderOf_eq_one_iff.1 (by rw [hi, pow_zero])) ha1'
    · rw [hi, pow_succ]
      exact dvd_mul_left r _
  have ha₁L : ((a ^ (orderOf a / r) : ↥R) : G) ∈ L := Subgroup.pow_mem _ haL _
  have ha₁Z : a ^ (orderOf a / r) ∈ center ↥R := Subgroup.pow_mem _ haZ _
  have hAU := hA (zpowers ((a ^ (orderOf a / r) : ↥R) : G)) (zpowers_le.2 ha₁L)
    (by rw [Nat.card_zpowers, Subgroup.orderOf_coe,
      orderOf_pow_orderOf_div (orderOf_pos a).ne' hao])
  set a₁ : G := ((a ^ (orderOf a / r) : ↥R) : G) with ha₁
  have hcomm : a₁ * (g⁻¹ * z * g) = g⁻¹ * z * g * a₁ :=
    (congrArg Subtype.val ((Subgroup.mem_center_iff.1 ha₁Z) ⟨_, hzR (mem_zpowers _)⟩)).symm
  have hcz : g * a₁ * g⁻¹ * z = z * (g * a₁ * g⁻¹) := by
    calc g * a₁ * g⁻¹ * z = g * (a₁ * (g⁻¹ * z * g)) * g⁻¹ := by group
      _ = g * (g⁻¹ * z * g * a₁) * g⁻¹ := by rw [hcomm]
      _ = z * (g * a₁ * g⁻¹) := by group
  have hgaM : g * a₁ * g⁻¹ ∈ D.M := hN (Subgroup.mem_normalizer_fintype fun y hy => by
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
    rw [(Commute.zpow_right (hcz : Commute (g * a₁ * g⁻¹) z) i).eq, mul_inv_cancel_right]
    exact Subgroup.zpow_mem _ (mem_zpowers z) i)
  have hgM : g⁻¹ ∈ D.M := uc22p22r_mem_of_conj_mem_of_unique D hAU (by rw [inv_inv]; exact hgaM)
  exact Subgroup.mem_normalizer_iff_map_conj_eq.1
    (Subgroup.le_normalizer (by simpa using D.M.inv_mem hgM))

namespace U4X

variable {D : Data G} {L K : Subgroup G} {n : ℕ}

theorem r_dvd_card (u : U4X D L K n) : 2 ^ n - 1 ∣ Nat.card L := by
  have h : 2 ^ n - 1 ∣ Nat.card (Bar2 L) := by
    rcases u.hLS with ⟨rfl, h⟩ | ⟨rfl, h⟩
    · rw [uc22p22r_L2_card h]
      norm_num
    · rw [CFSG.LocalAnalysis.EvenBN.GMSK.card_of_lieModel_twistedB2 h]
      exact dvd_mul_left _ _
  exact h.trans (Subgroup.card_quotient_dvd_card _)

theorem false_of_ne_one (u : U4X D L K n) {Ch : Choice2011 G}
    (h211 : S21_1 D Ch) (h869 : F08.R869NS5 D) (h1930 : H1930 D) (c : Ctx21 D Ch)
    (hA : ∀ A : Subgroup G, A ≤ L → Nat.card A = 2 ^ n - 1 → A ∈ uniqueSet D.M)
    {b : G} (hb : b ∈ c.B0) (hbN : b ∈ normalizer (D.T : Set G)) (hbo : orderOf b = 2 ^ n - 1)
    {x₀ x₁ : Bar2 D.M} (hx₀ : x₀ ∈ barImage D.M L) (hx₁ : x₁ ∈ barImage D.M K)
    (hx₀q : x₀ ^ (2 ^ n - 1) = 1) (hx₁q : x₁ ^ (2 ^ n - 1) = 1)
    (hc₀ : ∀ f ∈ barImage D.M L, uc22p21cPi D.M ⟨b, c.hBM hb⟩ * f *
      (uc22p21cPi D.M ⟨b, c.hBM hb⟩)⁻¹ = x₀ * f * x₀⁻¹)
    (hc₁ : ∀ f ∈ barImage D.M K, uc22p21cPi D.M ⟨b, c.hBM hb⟩ * f *
      (uc22p21cPi D.M ⟨b, c.hBM hb⟩)⁻¹ = x₁ * f * x₁⁻¹)
    (hc : uc22p21cPi D.M ⟨b, c.hBM hb⟩ * (x₀ * x₁)⁻¹ ∈ centralizer
      ((barImage D.M L ⊔ barImage D.M K : Subgroup (Bar2 D.M)) : Set (Bar2 D.M)))
    (hc1 : uc22p21cPi D.M ⟨b, c.hBM hb⟩ * (x₀ * x₁)⁻¹ ≠ 1) : False := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hcomm, -, -, -, hX, hXn, hXC⟩ := u4x_bar_structure u.hL u.hK u.hne u.hset u.shape
  have hbq : b ^ (2 ^ n - 1) = 1 := by rw [← hbo]; exact pow_orderOf_eq_one b
  have hβq : uc22p21cPi D.M ⟨b, c.hBM hb⟩ ^ (2 ^ n - 1) = 1 := by
    rw [← map_pow, show (⟨b, c.hBM hb⟩ : ↥D.M) ^ (2 ^ n - 1) = 1 from
      Subtype.ext (by simpa using hbq), map_one]
  have hcq := u4x_pow_eq_one hcomm hx₀ hx₁ hc₀ hc₁ hβq hx₀q hx₁q
  have hxX : x₀ * x₁ ∈ barImage D.M L ⊔ barImage D.M K :=
    mul_mem (mem_sup_left hx₀) (mem_sup_right hx₁)
  haveI := hXn
  have hcN : uc22p21cPi D.M ⟨b, c.hBM hb⟩ * (x₀ * x₁)⁻¹ ∈
      normalizer (barImage D.M D.T : Set (Bar2 D.M)) := by
    refine u4x_mem_normalizer_right (fun x hx y hy => Subgroup.mem_centralizer_iff.1 hy x hx)
      hXC hXn inferInstance (u4x_isSylowOf_barImage D.sylowM) hxX hc ?_
    rw [Subgroup.mem_centralizer_iff.1 hc _ hxX, inv_mul_cancel_right]
    exact uc22ine229_mk_mem_normalizer hbN
  obtain ⟨m, hmN, hmo, hmC⟩ := u4x_exists_lift D.sylowM.le (uc22p22c_pCoreOf_le_T D) hc hcN hc1
    u.prime_r hcq
  have hmo' : orderOf (m : G) = 2 ^ n - 1 := by rw [Subgroup.orderOf_coe]; exact hmo
  have hN := u4x_normalizer_le h869 u.hL u.hK u.hne u.hset u.hc2 u.hLS u.hσ m.2 u.prime_r
    u.r_ne_two hmo' (by rw [hX]; exact hmC)
  have hU := u4x_mem_uniqueSet u.hL.1.le u.hc2 u.prime_r u.r_ne_two u.r_dvd_card hA m.2 hmo' hN
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := uc22ine229_s21_1Hyp u.prime_r u.r_ne_two
    (by rw [Nat.card_zpowers, hmo']) (zpowers_le.2 hmN) hU
  exact (h211 h1930 c _ h1 h2 h3 h4 h5 h6).2 (zpowers_le.2 hmN)

end U4X

end CFSG.LocalAnalysis.UniquenessCase.UC22
