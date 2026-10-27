module

public import CFSG.LocalAnalysis.StandardType.ZS.DThreeConfig
public import CFSG.Blueprint.FischerDefs
import CFSG.LocalAnalysis.StandardType.ZS.DThreeUnitary
import CFSG.LocalAnalysis.StandardType.ZS.DThreeTransport
import CFSG.Fischer.Classification.FischerTypeLocal
import CFSG.GroupTheory.LocalCores.Fitting
import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Isaacs.VII.lemma_7_7
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Basic

public section

namespace CFSG.StandardType.ZS

open CFSG.Blueprint.Fischer
open CFSG.Fischer
open CFSG.Fischer.Classification

variable {G : Type} [Group G] {F : Set G}

private lemma orderOf_mul_of_orderOf_localQuotient (hP : Pair G F) {e : G} {x y : LocalGroup F e}
    (hx : (x : G) ∈ F) (hy : (y : G) ∈ F) {n : ℕ} (hn : n = 2 ∨ n = 3)
    (h : orderOf ((x : LocalQuotient F e) * (y : LocalQuotient F e)) = n) :
    orderOf ((x : G) * (y : G)) = n := by
  have hmap : orderOf (QuotientGroup.mk' (Subgroup.center (LocalGroup F e)) (x * y)) = n := by
    simpa only [map_mul, QuotientGroup.mk'_apply] using h
  have hdvd : n ∣ orderOf ((x : G) * (y : G)) := by
    have hdiv := orderOf_map_dvd (QuotientGroup.mk' (Subgroup.center (LocalGroup F e))) (x * y)
    rw [hmap, ← Subgroup.orderOf_coe (x * y)] at hdiv
    exact hdiv
  have hmem := Pair.orderOf_mul_mem hP hx hy
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
  rcases hn with rfl | rfl
  · rcases hmem with h1 | h1 | h1
    · rw [h1] at hdvd; norm_num at hdvd
    · exact h1
    · rw [h1] at hdvd; norm_num at hdvd
  · rcases hmem with h1 | h1 | h1
    · rw [h1] at hdvd; norm_num at hdvd
    · rw [h1] at hdvd; norm_num at hdvd
    · exact h1

private lemma commute_of_mul_mem_center (hP : Pair G F) {e : G} {x y g : LocalGroup F e}
    (hxE : (x : G) ∈ F) (hyE : (y : G) ∈ F) (hgE : (g : G) ∈ F)
    (hz2 : orderOf (x * y) = 2) (hzcent : x * y ∈ Subgroup.center (LocalGroup F e)) :
    Commute g x := by
  have hx2 : x * x = 1 := Subtype.ext (Pair.mul_self hP hxE)
  have hzsq : (x * y) ^ 2 = 1 := by
    have := pow_orderOf_eq_one (x * y)
    rwa [hz2] at this
  have hz1 : x * y ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hz2
    norm_num at hz2
  by_contra hgc
  have hneX : (g : G) * (x : G) ≠ (x : G) * (g : G) := fun h =>
    hgc ((commute_iff_eq g x).mpr (Subtype.ext h))
  have h3 : orderOf (g * x) = 3 := by
    rw [← Subgroup.orderOf_coe (g * x)]
    exact Pair.orderOf_mul_eq_three hP hgE hxE (by simpa using hneX)
  have hgx2 : (g * x) ^ 2 ≠ 1 := by
    intro h2
    have hdvd : orderOf (g * x) ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr h2
    rw [h3] at hdvd
    norm_num at hdvd
  have hcommz : Commute (g * x) (x * y) :=
    (commute_iff_eq (g * x) (x * y)).mpr ((Subgroup.mem_center_iff.mp hzcent) (g * x))
  have hgy_eq : g * y = (g * x) * (x * y) := by
    have hy_eq : y = x * (x * y) := by
      rw [← mul_assoc, hx2, one_mul]
    calc g * y = g * (x * (x * y)) := congrArg (fun t => g * t) hy_eq
      _ = (g * x) * (x * y) := by rw [mul_assoc]
  have hgy2 : (g * y) ^ 2 ≠ 1 := by
    intro h2
    rw [hgy_eq, hcommz.mul_pow 2, hzsq, mul_one] at h2
    exact hgx2 h2
  have hgy3 : (g * y) ^ 3 ≠ 1 := by
    intro h3gy
    rw [hgy_eq, hcommz.mul_pow 3] at h3gy
    have hgx3 : (g * x) ^ 3 = 1 := by
      have := pow_orderOf_eq_one (g * x)
      rwa [h3] at this
    rw [hgx3, one_mul] at h3gy
    have hz3 : (x * y) ^ 3 = x * y := by
      change (x * y) ^ (2 + 1) = x * y
      rw [pow_succ, hzsq, one_mul]
    rw [hz3] at h3gy
    exact hz1 h3gy
  have hmem : orderOf (g * y) ∈ ({1, 2, 3} : Set ℕ) := by
    rw [← Subgroup.orderOf_coe (g * y)]
    exact Pair.orderOf_mul_mem hP hgE hyE
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
  rcases hmem with h1 | h2 | h3'
  · have hgy1 : g * y = 1 := orderOf_eq_one_iff.mp h1
    exact hgy2 (by rw [hgy1]; exact one_pow 2)
  · have := pow_orderOf_eq_one (g * y)
    rw [h2] at this
    exact hgy2 this
  · have := pow_orderOf_eq_one (g * y)
    rw [h3'] at this
    exact hgy3 this

private lemma localQuotient_eq_one_of_eq (hP : Pair G F) {e : G} {x y : LocalGroup F e}
    (hxE : (x : G) ∈ F) (hyE : (y : G) ∈ F)
    (heq : (x : LocalQuotient F e) = (y : LocalQuotient F e))
    (hz2 : orderOf (x * y) = 2) : (x : LocalQuotient F e) = 1 := by
  have hx2 : x * x = 1 := Subtype.ext (Pair.mul_self hP hxE)
  have hquot : ((x * y : LocalGroup F e) : LocalQuotient F e) = 1 := by
    rw [QuotientGroup.mk_mul, ← heq, ← QuotientGroup.mk_mul, hx2, QuotientGroup.mk_one]
  have hzcent : x * y ∈ Subgroup.center (LocalGroup F e) :=
    (QuotientGroup.eq_one_iff (x * y)).mp hquot
  have hcomm : ∀ (g : G) (hg : g ∈ LocalClass F e),
      Commute (⟨g, mem_localGroup hg⟩ : LocalGroup F e) x :=
    fun g hg => commute_of_mul_mem_center hP hxE hyE hg.1 hz2 hzcent
  have htop : Subgroup.closure ((LocalGroup F e).subtype ⁻¹' LocalClass F e) = ⊤ :=
    Subgroup.closure_closure_coe_preimage
  have hle : Subgroup.closure ((LocalGroup F e).subtype ⁻¹' LocalClass F e) ≤
      Subgroup.centralizer ({x} : Set (LocalGroup F e)) := by
    rw [Subgroup.closure_le]
    rintro g hg
    change g ∈ Subgroup.centralizer ({x} : Set (LocalGroup F e))
    exact Subgroup.mem_centralizer_singleton_iff.mpr
      (by simpa using (hcomm (g : G) hg).eq)
  refine (QuotientGroup.eq_one_iff x).mpr ?_
  rw [Subgroup.mem_center_iff]
  intro l
  exact Subgroup.mem_centralizer_singleton_iff.mp (hle (htop.symm ▸ Subgroup.mem_top l))

private lemma orderOf_mul_eq_three_or_eq_of_localQuotient (hP : Pair G F) {e : G}
    {x y : LocalGroup F e}
    (hxE : (x : G) ∈ F) (hyE : (y : G) ∈ F)
    (hlast : orderOf ((x : LocalQuotient F e) * (y : LocalQuotient F e)) = 3 ∨
      (x : LocalQuotient F e) = (y : LocalQuotient F e))
    {la lb : LocalGroup F e}
    (hxq : (x : LocalQuotient F e) = (lb : LocalQuotient F e) *
      (la : LocalQuotient F e) * (lb : LocalQuotient F e))
    (hlbE : (lb : G) ∈ F)
    (hab3 : orderOf ((la : LocalQuotient F e) * (lb : LocalQuotient F e)) = 3) :
    orderOf ((x : G) * (y : G)) = 3 ∨ (x : G) = (y : G) := by
  rcases hlast with h3 | heq
  · left
    exact orderOf_mul_of_orderOf_localQuotient hP hxE hyE (Or.inr rfl) h3
  · by_cases h3 : orderOf ((x : G) * (y : G)) = 3
    · left; exact h3
    · right
      have hmem := Pair.orderOf_mul_mem hP hxE hyE
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
      rcases hmem with h1 | h2 | h3'
      · have hyX2 : orderOf (y : G) = 2 := Pair.orderOf_eq_two hP hyE
        have hy2 : (y : G) * (y : G) = 1 := by
          rw [← sq, ← hyX2, pow_orderOf_eq_one]
        have hxy1 : (x : G) * (y : G) = 1 := orderOf_eq_one_iff.mp h1
        exact (eq_inv_of_mul_eq_one_left hxy1).trans (inv_eq_of_mul_eq_one_right hy2)
      · exfalso
        have hz2 : orderOf (x * y) = 2 := by
          rw [← Subgroup.orderOf_coe (x * y)]
          exact h2
        have hmkx : (x : LocalQuotient F e) = 1 :=
          localQuotient_eq_one_of_eq hP hxE hyE heq hz2
        have hbab : (lb : LocalQuotient F e) * (la : LocalQuotient F e) *
            (lb : LocalQuotient F e) = 1 := by rw [← hxq, hmkx]
        have hb2 : (lb : LocalQuotient F e) * (lb : LocalQuotient F e) = 1 := by
          have hlb2 : lb * lb = 1 := Subtype.ext (Pair.mul_self hP hlbE)
          rw [← QuotientGroup.mk_mul, hlb2, QuotientGroup.mk_one]
        have h1' : (la : LocalQuotient F e) * (lb : LocalQuotient F e) =
            (lb : LocalQuotient F e) := by
          calc (la : LocalQuotient F e) * (lb : LocalQuotient F e)
              = ((lb : LocalQuotient F e) * (lb : LocalQuotient F e)) *
                ((la : LocalQuotient F e) * (lb : LocalQuotient F e)) := by
                rw [hb2, one_mul]
            _ = (lb : LocalQuotient F e) * ((lb : LocalQuotient F e) *
                (la : LocalQuotient F e) * (lb : LocalQuotient F e)) := by group
            _ = (lb : LocalQuotient F e) := by rw [hbab, mul_one]
        have ha1 : (la : LocalQuotient F e) = 1 := by
          calc (la : LocalQuotient F e) = ((la : LocalQuotient F e) *
                (lb : LocalQuotient F e)) * (lb : LocalQuotient F e) := by
                rw [mul_assoc, hb2, mul_one]
            _ = (lb : LocalQuotient F e) * (lb : LocalQuotient F e) := by rw [h1']
            _ = 1 := hb2
        have hb_dvd : orderOf (lb : LocalQuotient F e) ∣ 2 := by
          have h := orderOf_map_dvd
            (QuotientGroup.mk' (Subgroup.center (LocalGroup F e))) lb
          rw [QuotientGroup.mk'_apply, ← Subgroup.orderOf_coe lb,
            Pair.orderOf_eq_two hP hlbE] at h
          exact h
        rw [ha1, one_mul] at hab3
        rw [hab3] at hb_dvd
        norm_num at hb_dvd
      · exact absurd h3' h3

theorem UnitaryFourConfig.exists_of_localImages {X : Type} [Group X] {E : Set X}
    (hP : Pair X E) {e : X} {a b c d : LocalQuotient E e}
    (h : UnitaryFourConfig (LocalImages E e) a b c d) :
    ∃ a' b' c' d' : X, UnitaryFourConfig E a' b' c' d' := by
  simp only [LocalImages] at h
  obtain ⟨ha, hb, hc, hd, hab3, hac3, had3, hbc3, hcd3, hbd2, hcacb3, hcacd3,
    hlast⟩ := h
  obtain ⟨la, hla, hlaq⟩ := ha
  obtain ⟨lb, hlb, hlbq⟩ := hb
  obtain ⟨lc, hlc, hlcq⟩ := hc
  obtain ⟨ld, hld, hldq⟩ := hd
  have hlaE : (la : X) ∈ E := hla.1
  have hlbE : (lb : X) ∈ E := hlb.1
  have hlcE : (lc : X) ∈ E := hlc.1
  have hldE : (ld : X) ∈ E := hld.1
  let x : LocalGroup E e := lb * la * lb
  let y : LocalGroup E e := ld * lc * ld
  have hxE : (x : X) ∈ E := by
    simpa only [x, Subgroup.coe_mul] using Pair.mul_mul_mem hP hlbE hlaE
  have hyE : (y : X) ∈ E := by
    simpa only [y, Subgroup.coe_mul] using Pair.mul_mul_mem hP hldE hlcE
  have hcacE : (((lc * la * lc : LocalGroup E e) : X)) ∈ E := by
    simpa only [Subgroup.coe_mul] using Pair.mul_mul_mem hP hlcE hlaE
  have hcacb3' : orderOf (((lc * la * lc : LocalGroup E e) : LocalQuotient E e) *
      (lb : LocalQuotient E e)) = 3 := by
    simpa only [QuotientGroup.mk_mul, hlcq, hlaq, hlbq] using hcacb3
  have hcacd3' : orderOf (((lc * la * lc : LocalGroup E e) : LocalQuotient E e) *
      (ld : LocalQuotient E e)) = 3 := by
    simpa only [QuotientGroup.mk_mul, hlcq, hlaq, hldq] using hcacd3
  have hlastq : orderOf ((x : LocalQuotient E e) * (y : LocalQuotient E e)) = 3 ∨
      (x : LocalQuotient E e) = (y : LocalQuotient E e) := by
    simpa only [x, y, QuotientGroup.mk_mul, hlaq, hlbq, hlcq, hldq] using hlast
  have hlastX : orderOf ((x : X) * (y : X)) = 3 ∨ (x : X) = (y : X) :=
    orderOf_mul_eq_three_or_eq_of_localQuotient hP hxE hyE hlastq (la := la) (lb := lb)
      (by simp only [x, QuotientGroup.mk_mul])
      hlbE (by simpa only [hlaq, hlbq] using hab3)
  refine ⟨(la : X), (lb : X), (lc : X), (ld : X), hlaE, hlbE, hlcE, hldE,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact orderOf_mul_of_orderOf_localQuotient hP hlaE hlbE (Or.inr rfl)
      (by simpa only [hlaq, hlbq] using hab3)
  · exact orderOf_mul_of_orderOf_localQuotient hP hlaE hlcE (Or.inr rfl)
      (by simpa only [hlaq, hlcq] using hac3)
  · exact orderOf_mul_of_orderOf_localQuotient hP hlaE hldE (Or.inr rfl)
      (by simpa only [hlaq, hldq] using had3)
  · exact orderOf_mul_of_orderOf_localQuotient hP hlbE hlcE (Or.inr rfl)
      (by simpa only [hlbq, hlcq] using hbc3)
  · exact orderOf_mul_of_orderOf_localQuotient hP hlcE hldE (Or.inr rfl)
      (by simpa only [hlcq, hldq] using hcd3)
  · exact orderOf_mul_of_orderOf_localQuotient hP hlbE hldE (Or.inl rfl)
      (by simpa only [hlbq, hldq] using hbd2)
  · exact orderOf_mul_of_orderOf_localQuotient hP hcacE hlbE (Or.inr rfl) hcacb3'
  · exact orderOf_mul_of_orderOf_localQuotient hP hcacE hldE (Or.inr rfl) hcacd3'
  · simpa only [x, y, Subgroup.coe_mul] using hlastX

theorem exists_unitaryFourConfig_of_hasType {X : Type} [Group X] {E : Set X} {k : Fin 3}
    (h : HasType k X E) : ∃ a b c d : X, UnitaryFourConfig E a b c d := by
  have hF22 : ∀ {Y : Type} [Group Y] {F : Set Y}, F22 Y F →
      ∃ a b c d : Y, UnitaryFourConfig F a b c d := by
    intro Y _ F h
    obtain ⟨e, he, -⟩ := h.2
    obtain ⟨iso, hiso⟩ := F22.exists_mulEquiv_U2 h he
    obtain ⟨a, b, c, d, hconf⟩ := exists_unitaryFourConfig_DU (m := 6) (by norm_num)
    have hEF : ∀ x : LocalQuotient F e, x ∈ LocalImages F e ↔ iso x ∈ Unitary.DU 6 := by
      intro x
      rw [← hiso]
      constructor
      · intro hx
        exact ⟨x, hx, rfl⟩
      · rintro ⟨y, hy, hyx⟩
        exact (iso.injective hyx) ▸ hy
    have hconf' : UnitaryFourConfig (LocalImages F e) (iso.symm a) (iso.symm b)
        (iso.symm c) (iso.symm d) := UnitaryFourConfig.comap iso hEF hconf
    exact UnitaryFourConfig.exists_of_localImages h.1 hconf'
  have hF23 : ∀ {Y : Type} [Group Y] {F : Set Y}, F23 Y F →
      ∃ a b c d : Y, UnitaryFourConfig F a b c d := by
    intro Y _ F h
    obtain ⟨hP, e, he, h22⟩ := h
    obtain ⟨a, b, c, d, hconf⟩ := hF22 h22
    exact UnitaryFourConfig.exists_of_localImages hP hconf
  have hF24 : ∀ {Y : Type} [Group Y] {F : Set Y}, F24 Y F →
      ∃ a b c d : Y, UnitaryFourConfig F a b c d := by
    intro Y _ F h
    obtain ⟨hP, e, he, h23⟩ := h
    obtain ⟨a, b, c, d, hconf⟩ := hF23 h23
    exact UnitaryFourConfig.exists_of_localImages hP hconf
  obtain ⟨_ | _ | n, hk⟩ := k
  · exact hF22 h
  · exact hF23 h
  · exact hF24 h

end CFSG.StandardType.ZS
