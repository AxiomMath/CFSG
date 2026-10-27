module

public import CFSG.RankThree.PartTwo.Sec21.FF79ThmA4Sec3L4Ap2
public import CFSG.RankThree.PartTwo.Sec21.FF79Sec3L4KA5


public section

namespace CFSG.RankThree.PartTwo.Sec21.FF79.H4

open CFSG CFSG.RankThree.PartTwo.Sec21
open CFSG.Assembly (KProper InCatalog)

section Generic

theorem mapEquiv_of_injOn {X Y : Type*} [Group X] [Group Y] (T : Subgroup X) (f : X →* Y)
    (hinj : ∀ x ∈ T, ∀ y ∈ T, f x = f y → x = y) : Nonempty (↥T ≃* ↥(T.map f)) := by
  have : Function.Injective (f.subgroupMap T) := by
    intro x y hxy
    exact Subtype.ext (hinj x x.2 y y.2 (congrArg Subtype.val hxy))
  exact ⟨MulEquiv.ofBijective _ ⟨this, f.subgroupMap_surjective T⟩⟩

theorem not_isPGroup_three_of_card_sixty {Y : Type*} [Group Y] [Finite Y] (K : Subgroup Y)
    (h : Nat.card K = 60) : ¬ IsPGroup 3 K := by
  intro hK
  obtain ⟨n, hn⟩ := hK.exists_card_eq
  rw [h] at hn
  have h5 : 5 ∣ 3 ^ n := hn ▸ (by norm_num : 5 ∣ 60)
  have := Nat.Prime.dvd_of_dvd_pow (by norm_num : Nat.Prime 5) h5
  omega

end Generic

section K

variable {G : Type} [Group G] [Finite G]
variable {b : G} {J B A P D : Subgroup G} {a : G}

theorem sec34_K1_a5 (hU : FF79Sec34UFacts b a J A) (hK : IsLnq 2 2 2 (Lay (J ⊓ Cen a))) :
    Nonempty ((Lay (J ⊓ Cen a)).subgroupOf (CenS (U34 b a J A)) ≃*
      alternatingGroup (Fin 5)) := by
  obtain ⟨e⟩ := nonempty_equiv_alt5_of_isLnq hK
  exact ⟨(Subgroup.subgroupOfEquivOfLe hU.K_cen_U).trans e⟩

theorem sec34_K_inf_core (hU : FF79Sec34UFacts b a J A) (hK : IsLnq 2 2 2 (Lay (J ⊓ Cen a))) :
    ∀ x ∈ (Lay (J ⊓ Cen a)).subgroupOf (CenS (U34 b a J A)),
      x ∈ pPrimeCore 3 ↥(CenS (U34 b a J A)) → x = 1 := by
  haveI : (pPrimeCore 3 ↥(CenS (U34 b a J A))).Normal := pPrimeCore_normal
  have e := sec34_K1_a5 hU hK
  refine a5_inf_eq_bot _ _ e fun hle => ?_
  have h60 : Nat.card ((Lay (J ⊓ Cen a)).subgroupOf (CenS (U34 b a J A))) = 60 :=
    a5_card_dvd _ e
  have hdvd := Subgroup.card_dvd_of_le hle
  rw [h60] at hdvd
  have h3 : 3 ∣ Nat.card (pPrimeCore 3 ↥(CenS (U34 b a J A))) :=
    dvd_trans (by norm_num) hdvd
  exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp (coprime_pPrimeCore _) h3

theorem sec34_ap_K_a5 (hU : FF79Sec34UFacts b a J A) (hK : IsLnq 2 2 2 (Lay (J ⊓ Cen a))) :
    Nonempty (cqImg (U34 b a J A) (Lay (J ⊓ Cen a)) ≃* alternatingGroup (Fin 5)) := by
  obtain ⟨e⟩ := sec34_K1_a5 hU hK
  obtain ⟨f⟩ := mapEquiv_of_injOn ((Lay (J ⊓ Cen a)).subgroupOf (CenS (U34 b a J A)))
    (QuotientGroup.mk' (pPrimeCore 3 ↥(CenS (U34 b a J A)))) (by
      intro x hx y hy hxy
      have hmem : x⁻¹ * y ∈ pPrimeCore 3 ↥(CenS (U34 b a J A)) :=
        QuotientGroup.eq.mp hxy
      have := sec34_K_inf_core hU hK _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hx) hy) hmem
      exact inv_mul_eq_one.mp this)
  exact ⟨f.symm.trans e⟩

theorem sec34_ap_K_nor (h : FF79Sec34In4 b J B A P D) (hU : FF79Sec34UFacts b a J A) :
    ∀ y : CQ (U34 b a J A), cqβ (U34 b a J A) b hU.b_nor y = y →
      ∀ k ∈ cqImg (U34 b a J A) (Lay (J ⊓ Cen a)),
        y * k * y⁻¹ ∈ cqImg (U34 b a J A) (Lay (J ⊓ Cen a)) := by
  intro y hy k hk
  have hb3 : orderOf b = 3 := h.hyp.ord
  have hb3' : b ^ 3 = 1 := by rw [← hb3]; exact pow_orderOf_eq_one b
  obtain ⟨c, hcb, rfl⟩ := cq_lift_fixed hU.b_nor hb3' hy
  obtain ⟨d, hdK, rfl⟩ := mem_cqImg.mp hk
  have hca : (c : G) ∈ Cen a := Subgroup.mem_centralizer_iff.mpr fun x hx => by
    rw [Set.mem_singleton_iff] at hx
    subst hx
    exact Subgroup.mem_centralizer_iff.mp c.2 x hU.a_mem
  have hcN := hU.K_nor c ⟨hca, hcb⟩
  have hcd : (c : G) * d * (c : G)⁻¹ ∈ Lay (J ⊓ Cen a) :=
    (Subgroup.mem_normalizer_iff.mp hcN d).mp hdK
  rw [← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
  exact mk_mem_cqImg (c * d * c⁻¹) hcd

theorem sec34_ap_K (hs : FF79Sec3 b J) (h : FF79Sec34In4 b J B A P D)
    (hU : FF79Sec34UFacts b a J A) (hoa : orderOf a = 3)
    (hK : IsLnq 2 2 2 (Lay (J ⊓ Cen a))) :
    Nonempty (cqImg (U34 b a J A) (Lay (J ⊓ Cen a)) ≃* alternatingGroup (Fin 5)) ∧
    (∀ k ∈ cqImg (U34 b a J A) (Lay (J ⊓ Cen a)),
      cqβ (U34 b a J A) b hU.b_nor k = k) ∧
    (∀ y : CQ (U34 b a J A), cqβ (U34 b a J A) b hU.b_nor y = y →
      ∀ k ∈ cqImg (U34 b a J A) (Lay (J ⊓ Cen a)),
        y * k * y⁻¹ ∈ cqImg (U34 b a J A) (Lay (J ⊓ Cen a))) ∧
    (∀ y ∈ pCore 3 (CQ (U34 b a J A)), cqβ (U34 b a J A) b hU.b_nor y = y →
      ∀ k ∈ cqImg (U34 b a J A) (Lay (J ⊓ Cen a)), y * k = k * y) := by
  have ha5 := sec34_ap_K_a5 hU hK
  refine ⟨ha5, ?_, sec34_ap_K_nor h hU, ?_⟩
  · intro k hk
    obtain ⟨d, hdK, rfl⟩ := mem_cqImg.mp hk
    exact cqβ_mk_of_cen hU.b_nor d (hU.K_cen_b hdK)
  · intro y hyR hy k hk
    have hkn := sec34_ap_K_nor h hU y hy k hk
    have hz : y * k * y⁻¹ * k⁻¹ ∈ cqImg (U34 b a J A) (Lay (J ⊓ Cen a)) :=
      Subgroup.mul_mem _ hkn (Subgroup.inv_mem _ hk)
    have hzR : y * k * y⁻¹ * k⁻¹ ∈ pCore 3 (CQ (U34 b a J A)) := by
      have := (pCore_normal (p := 3) (G := CQ (U34 b a J A))).conj_mem y⁻¹
        (Subgroup.inv_mem _ hyR) k
      have h2 := Subgroup.mul_mem _ hyR this
      simpa [mul_assoc] using h2
    haveI : (pCore 3 (CQ (U34 b a J A))).Normal := pCore_normal
    have hKR : ¬ cqImg (U34 b a J A) (Lay (J ⊓ Cen a)) ≤ pCore 3 (CQ (U34 b a J A)) := by
      intro hle
      have h60 : Nat.card (cqImg (U34 b a J A) (Lay (J ⊓ Cen a))) = 60 :=
        a5_card_dvd _ ha5
      exact not_isPGroup_three_of_card_sixty _ h60 (pCore_isPGroup.to_le hle)
    have h1 := a5_inf_eq_bot _ _ ha5 hKR _ hz hzR
    have h2 : y * k * y⁻¹ = k := mul_inv_eq_one.mp h1
    exact mul_inv_eq_iff_eq_mul.mp h2

end K

end CFSG.RankThree.PartTwo.Sec21.FF79.H4
