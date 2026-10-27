module

public import CFSG.RankThree.GF2n.Tim77.Sec33Root
public import CFSG.RankThree.GF2n.Tim77.Cor2BetaInner

public section

namespace CFSG.RankThree.GF2n.Tim77

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Timmesfeld.RootInvolutions Subgroup
open CFSG.GH74.Uniqueness.Bender
open scoped commutatorElement

variable {G : Type} [Group G]

section Certified3


theorem sec33_cr_aux [Finite G] {A Abar S₀ B : Subgroup G} {s : G}
    (hC : Sec3Ctx A Abar S₀ B) (hs : Section3.IsSChoice A Abar S₀ B s)
    (hq : 2 < Section3.q A Abar)
    [hNn : ((Section3.N A Abar s).subgroupOf (Section3.Y A Abar s)).Normal] {n i : ℕ}
    (hi : i = 1 ∨ i = 2)
    (hK : BenderType ((↥(Section3.Y A Abar s) ⧸
        (Section3.N A Abar s).subgroupOf (Section3.Y A Abar s)) ⧸
        Subgroup.center (↥(Section3.Y A Abar s) ⧸
          (Section3.N A Abar s).subgroupOf (Section3.Y A Abar s))) n i 1)
    {g : G} (hgY : g ∈ Section3.Y A Abar s)
    (h1 : ∀ a ∈ A, g * a * g⁻¹ * a⁻¹ ∈ Section3.N A Abar s)
    (h2 : ∀ y ∈ Section3.Y A Abar s,
      (g * g) * y * (g * g)⁻¹ * y⁻¹ ∈ Section3.N A Abar s) :
    ∃ a ∈ A, ∀ y ∈ Section3.Y A Abar s,
      (g * a⁻¹) * y * (g * a⁻¹)⁻¹ * y⁻¹ ∈ Section3.N A Abar s := by
  classical
  obtain ⟨hNY, hYN, hNab⟩ := tim77Sec32a_holds G A Abar S₀ B s hC hs
  have hNc : ∀ x ∈ Section3.N A Abar s, ∀ w ∈ Section3.N A Abar s, x * w = w * x :=
    fun x hx w hw => congrArg Subtype.val (hNab.1.is_comm.comm ⟨x, hx⟩ ⟨w, hw⟩)
  obtain ⟨hperf, hB⟩ := sec33_quot_bender hC hs hq
  have hAY : A ≤ Section3.Y A Abar s := sec32d_A_le_Y
  have hcen := sec33_mem_center_iff (Y := Section3.Y A Abar s) (N := Section3.N A Abar s) hYN
  let π : ↥(Section3.Y A Abar s) →* ((↥(Section3.Y A Abar s) ⧸
      (Section3.N A Abar s).subgroupOf (Section3.Y A Abar s)) ⧸ Subgroup.center
        (↥(Section3.Y A Abar s) ⧸ (Section3.N A Abar s).subgroupOf (Section3.Y A Abar s))) :=
    (QuotientGroup.mk' _).comp (QuotientGroup.mk' _)
  have hπ1 : ∀ z : ↥(Section3.Y A Abar s), π z = 1 ↔
      (QuotientGroup.mk z : ↥(Section3.Y A Abar s) ⧸
        (Section3.N A Abar s).subgroupOf (Section3.Y A Abar s)) ∈ Subgroup.center _ := by
    intro z
    exact QuotientGroup.eq_one_iff _
  have hπsurj : Function.Surjective π := by
    intro k
    obtain ⟨q, rfl⟩ := QuotientGroup.mk_surjective k
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective q
    exact ⟨y, rfl⟩
  have hcen' : ∀ z : ↥(Section3.Y A Abar s), π z = 1 ↔
      ∀ y ∈ Section3.Y A Abar s, (z : G) * y * (z : G)⁻¹ * y⁻¹ ∈ Section3.N A Abar s :=
    fun z => (hπ1 z).trans (hcen z)
  by_cases hπg : π ⟨g, hgY⟩ = 1
  · refine ⟨1, Subgroup.one_mem _, fun y hy => ?_⟩
    have := (hcen' ⟨g, hgY⟩).mp hπg y hy
    simpa using this
  have hgg1 : π (⟨g, hgY⟩ * ⟨g, hgY⟩) = 1 := by
    rw [hcen']
    intro y hy
    simpa using h2 y hy
  have hgord : orderOf (π ⟨g, hgY⟩) = 2 := by
    refine orderOf_eq_prime ?_ hπg
    rw [sq, ← map_mul]
    exact hgg1
  obtain ⟨a₀, ha₀A, ha₀L⟩ := SetLike.exists_of_lt (lt_of_le_of_ne hC.setup.L_le hC.a0_ne)
  have hxx : (⟨a₀, hAY ha₀A⟩ : ↥(Section3.Y A Abar s)) * ⟨a₀, hAY ha₀A⟩ = 1 :=
    Subtype.ext (by simpa using hC.setup.sq_A ha₀A)
  have hπx1 : π ⟨a₀, hAY ha₀A⟩ ≠ 1 := fun h =>
    sec33_not_central hC hs ha₀A ha₀L ((hπ1 _).mp h)
  have hxord : orderOf (π ⟨a₀, hAY ha₀A⟩) = 2 := by
    refine orderOf_eq_prime ?_ hπx1
    rw [sq, ← map_mul, hxx, map_one]
  obtain ⟨c, hc⟩ := isConj_iff.mp (CFSG.Asc75.isConj_of_involutions_bender hB hgord hxord)
  obtain ⟨y₀, rfl⟩ := hπsurj c
  have hπgd : π ⟨g, hgY⟩ = π (y₀⁻¹ * ⟨a₀, hAY ha₀A⟩ * y₀) := by
    rw [map_mul, map_mul, map_inv]
    calc π ⟨g, hgY⟩ = (π y₀)⁻¹ * (π y₀ * π ⟨g, hgY⟩ * (π y₀)⁻¹) * π y₀ := by group
      _ = (π y₀)⁻¹ * π ⟨a₀, hAY ha₀A⟩ * π y₀ := by rw [hc]
  have hy₁ : (y₀ : G)⁻¹ ∈ Section3.Y A Abar s := Subgroup.inv_mem _ y₀.2
  have hd : (y₀ : G)⁻¹ * a₀ * (y₀ : G) ∈ conjSubgroup (y₀ : G)⁻¹ A := by
    have := (mem_conjSubgroup_conj_t77 (y₀ : G)⁻¹ a₀ A).2 ha₀A
    simpa using this
  by_cases hcomm : ∀ x ∈ A, ∀ w ∈ conjSubgroup (y₀ : G)⁻¹ A, x * w = w * x
  · obtain ⟨a, ha, hz⟩ := sec33_root_types hC hs hq hi hK hy₁ hcomm _ (by simpa using hd)
    refine ⟨a, ha, ?_⟩
    have h3 : π (y₀⁻¹ * ⟨a₀, hAY ha₀A⟩ * y₀ * (⟨a, hAY ha⟩ : ↥(Section3.Y A Abar s))⁻¹) = 1 := by
      rw [hcen']
      intro z hz'
      have := hz z hz'
      simpa using this
    have h4 : π (⟨g, hgY⟩ * (⟨a, hAY ha⟩ : ↥(Section3.Y A Abar s))⁻¹) = 1 := by
      rw [map_mul, map_inv, hπgd, ← map_inv, ← map_mul]
      exact h3
    intro y hy
    have := (hcen' _).mp h4 y hy
    simpa using this
  ·
    have hnc' : ¬ ∀ x ∈ conjSubgroup 1 A, ∀ w ∈ conjSubgroup (y₀ : G)⁻¹ A, x * w = w * x :=
      fun hall => hcomm fun x hx w hw => hall x (by rwa [conjSubgroup_one]) w hw
    have S := sec41_prop24 hC hYN hNc (one_mem _) hy₁ hnc'
    rw [conjSubgroup_one, conjSubgroup_one] at S
    have hdL : (y₀ : G)⁻¹ * a₀ * (y₀ : G) ∉ conjSubgroup (y₀ : G)⁻¹ (Section3.A0 A Abar) := by
      have := sec41_not_mem_conj (g := (y₀ : G)⁻¹) ha₀L
      simpa using this
    have hodd := S.odd_orderOf_mul ha₀A ha₀L hd hdL
    have hcg : (QuotientGroup.mk (⟨a₀, hAY ha₀A⟩ * ⟨g, hgY⟩) : ↥(Section3.Y A Abar s) ⧸
        (Section3.N A Abar s).subgroupOf (Section3.Y A Abar s)) =
        QuotientGroup.mk (⟨g, hgY⟩ * ⟨a₀, hAY ha₀A⟩) := by
      rw [sec33_mk_eq_iff]
      have hc1 := h1 a₀ ha₀A
      have hc2 := (Subgroup.mem_normalizer_iff.mp (hYN a₀⁻¹ (Subgroup.inv_mem _ (hAY ha₀A)))
        _).mp hc1
      have hc3 := (Subgroup.mem_normalizer_iff.mp (hYN g⁻¹ (Subgroup.inv_mem _ hgY)) _).mp hc2
      have e : ((⟨a₀, hAY ha₀A⟩ * ⟨g, hgY⟩ : ↥(Section3.Y A Abar s)) : G)⁻¹ *
          ((⟨g, hgY⟩ * ⟨a₀, hAY ha₀A⟩ : ↥(Section3.Y A Abar s)) : G) =
          g⁻¹ * (a₀⁻¹ * (g * a₀ * g⁻¹ * a₀⁻¹) * a₀⁻¹⁻¹) * g⁻¹⁻¹ := by
        simp only [Subgroup.coe_mul]
        group
      rw [e]
      exact hc3
    have hcomm2 : π ⟨a₀, hAY ha₀A⟩ * π ⟨g, hgY⟩ = π ⟨g, hgY⟩ * π ⟨a₀, hAY ha₀A⟩ := by
      rw [← map_mul, ← map_mul]
      exact congrArg (QuotientGroup.mk (s := Subgroup.center _)) hcg
    have hsq2 : (π ⟨a₀, hAY ha₀A⟩ * π ⟨g, hgY⟩) ^ 2 = 1 := by
      refine sec33_sq_of_comm ?_ ?_ hcomm2
      · rw [← map_mul, hxx, map_one]
      · rw [← map_mul]
        exact hgg1
    have hdvd := orderOf_map_dvd π (⟨a₀, hAY ha₀A⟩ * (y₀⁻¹ * ⟨a₀, hAY ha₀A⟩ * y₀))
    have hord : orderOf (⟨a₀, hAY ha₀A⟩ * (y₀⁻¹ * ⟨a₀, hAY ha₀A⟩ * y₀) :
        ↥(Section3.Y A Abar s)) = orderOf (a₀ * ((y₀ : G)⁻¹ * a₀ * (y₀ : G))) := by
      rw [← Subgroup.orderOf_coe]
      simp
    have hodd' : Odd (orderOf (π (⟨a₀, hAY ha₀A⟩ * (y₀⁻¹ * ⟨a₀, hAY ha₀A⟩ * y₀)))) :=
      Odd.of_dvd_nat (hord ▸ hodd) hdvd
    have hone : π (⟨a₀, hAY ha₀A⟩ * (y₀⁻¹ * ⟨a₀, hAY ha₀A⟩ * y₀)) = 1 := by
      rw [← orderOf_eq_one_iff]
      have h2dvd : orderOf (π (⟨a₀, hAY ha₀A⟩ * (y₀⁻¹ * ⟨a₀, hAY ha₀A⟩ * y₀))) ∣ 2 := by
        refine orderOf_dvd_of_pow_eq_one ?_
        rw [map_mul, ← hπgd]
        exact hsq2
      rcases (Nat.dvd_prime Nat.prime_two).mp h2dvd with h1' | h1'
      · exact h1'
      · rw [h1'] at hodd'
        exact absurd hodd' (by decide)
    refine ⟨a₀, ha₀A, ?_⟩
    have h4 : π (⟨g, hgY⟩ * (⟨a₀, hAY ha₀A⟩ : ↥(Section3.Y A Abar s))⁻¹) = 1 := by
      rw [map_mul, ← hπgd] at hone
      rw [map_mul, map_inv]
      have : π ⟨g, hgY⟩ = (π ⟨a₀, hAY ha₀A⟩)⁻¹ := eq_inv_of_mul_eq_one_right hone
      rw [this, ← mul_inv_rev, ← map_mul, hxx, map_one, inv_one]
    intro y hy
    have := (hcen' _).mp h4 y hy
    simpa using this

theorem sec33_inner [Finite G] {A Abar S₀ B : Subgroup G} {s : G}
    (hC : Sec3Ctx A Abar S₀ B) (hs : Section3.IsSChoice A Abar S₀ B s)
    (hq : 2 < Section3.q A Abar) (hne : conjSubgroup s Abar ≠ Abar) :
    Section3.Y A Abar s ≤ Section3.X A Abar ⊔ Section3.N A Abar s := by
  classical
  obtain ⟨hNY, hYN, hNab⟩ := tim77Sec32a_holds G A Abar S₀ B s hC hs
  haveI hNn : ((Section3.N A Abar s).subgroupOf (Section3.Y A Abar s)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hNY).mpr (fun y hy => hYN y hy)
  have hsY := sec33_s_mem_normalizer_Y hC hs
  have hsN : s ∈ normalizer (Section3.N A Abar s : Set G) := by
    apply mem_normalizer_of_conjSubgroup_eq (conjSubgroup_eq_of_le _)
    intro x hx
    obtain ⟨n, hn, rfl⟩ := (mem_conjSubgroup_exists_t77 s _ x).1 hx
    exact sec33_conj_mem_N hC hs n hn
  have hsq := sec33_sq_mem_N hC hs
  have hsA : ∀ a ∈ A, s * a = a * s := (sec32a_s_facts hC hs).2
  have hAY : A ≤ Section3.Y A Abar s := sec32d_A_le_Y
  obtain ⟨hperf, hB⟩ := sec33_quot_bender hC hs hq
  haveI : Group.IsPerfect (↥(Section3.Y A Abar s) ⧸
      (Section3.N A Abar s).subgroupOf (Section3.Y A Abar s)) := Group.isPerfect_def.mpr hperf
  have hτ2 := sec33_tau_sq hsY hsN hYN hsq
  obtain ⟨a₀, ha₀A, ha₀L⟩ := SetLike.exists_of_lt (lt_of_le_of_ne hC.setup.L_le hC.a0_ne)
  have hsQ1 := sec33_not_central hC hs ha₀A ha₀L
  have hτa : ∀ a : G, ∀ ha : a ∈ A, sec33Tau hsY hsN (QuotientGroup.mk ⟨a, hAY ha⟩) =
      QuotientGroup.mk ⟨a, hAY ha⟩ := by
    intro a ha
    rw [sec33Tau_mk]
    congr 1
    apply Subtype.ext
    simp only [sec33ConjAut_apply]
    exact sec32a_conj_eq_of_comm (hsA a ha)
  have hsQ2 : (QuotientGroup.mk ⟨a₀, hAY ha₀A⟩ : ↥(Section3.Y A Abar s) ⧸
      (Section3.N A Abar s).subgroupOf (Section3.Y A Abar s)) * QuotientGroup.mk ⟨a₀, hAY ha₀A⟩ ∈
      Subgroup.center _ := by
    have : (QuotientGroup.mk ⟨a₀, hAY ha₀A⟩ : ↥(Section3.Y A Abar s) ⧸
      (Section3.N A Abar s).subgroupOf (Section3.Y A Abar s)) * QuotientGroup.mk ⟨a₀, hAY ha₀A⟩
        = 1 := by
      rw [← QuotientGroup.mk_mul]
      have : (⟨a₀, hAY ha₀A⟩ : ↥(Section3.Y A Abar s)) * ⟨a₀, hAY ha₀A⟩ = 1 :=
        Subtype.ext (by simpa using hC.setup.sq_A ha₀A)
      rw [this, QuotientGroup.mk_one]
    rw [this]
    exact Subgroup.one_mem _
  have hτs : (QuotientGroup.mk ⟨a₀, hAY ha₀A⟩ : ↥(Section3.Y A Abar s) ⧸
      (Section3.N A Abar s).subgroupOf (Section3.Y A Abar s))⁻¹ *
      sec33Tau hsY hsN (QuotientGroup.mk ⟨a₀, hAY ha₀A⟩) ∈ Subgroup.center _ := by
    rw [hτa a₀ ha₀A, inv_mul_cancel]
    exact Subgroup.one_mem _
  have hstar : ∀ x : ↥(Section3.Y A Abar s) ⧸
      (Section3.N A Abar s).subgroupOf (Section3.Y A Abar s),
      x⁻¹ * sec33Tau hsY hsN x ∈ Subgroup.center _ →
      ⁅x * QuotientGroup.mk ⟨a₀, hAY ha₀A⟩ * x⁻¹,
        (QuotientGroup.mk ⟨a₀, hAY ha₀A⟩ : ↥(Section3.Y A Abar s) ⧸
          (Section3.N A Abar s).subgroupOf (Section3.Y A Abar s))⁆ ∈
        Subgroup.center _ := by
    intro x hx
    induction x using QuotientGroup.induction_on with
    | H k =>
      by_cases hcomm : ∀ a ∈ A, ∀ w ∈ conjSubgroup (k : G) A, a * w = w * a
      · have hc := hcomm a₀ ha₀A ((k : G) * a₀ * (k : G)⁻¹)
          ((mem_conjSubgroup_conj_t77 (k : G) a₀ A).2 ha₀A)
        have hc' : (k * (⟨a₀, hAY ha₀A⟩ : ↥(Section3.Y A Abar s)) * k⁻¹) *
            (⟨a₀, hAY ha₀A⟩ : ↥(Section3.Y A Abar s)) =
            (⟨a₀, hAY ha₀A⟩ : ↥(Section3.Y A Abar s)) *
              (k * (⟨a₀, hAY ha₀A⟩ : ↥(Section3.Y A Abar s)) * k⁻¹) :=
          Subtype.ext (by simpa using hc.symm)
        have h1 : ⁅(QuotientGroup.mk k : ↥(Section3.Y A Abar s) ⧸
            (Section3.N A Abar s).subgroupOf (Section3.Y A Abar s)) *
            QuotientGroup.mk ⟨a₀, hAY ha₀A⟩ * (QuotientGroup.mk k)⁻¹,
            (QuotientGroup.mk ⟨a₀, hAY ha₀A⟩ : ↥(Section3.Y A Abar s) ⧸
              (Section3.N A Abar s).subgroupOf (Section3.Y A Abar s))⁆ = 1 := by
          rw [commutatorElement_eq_one_iff_mul_comm]
          simp only [← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul]
          rw [hc']
        rw [h1]
        exact Subgroup.one_mem _
      · exfalso
        apply hcomm
        refine sec33_comm_of_fixed_central hC hs hne k.2 ?_
        rw [sec33Tau_mk, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul] at hx
        intro y hy
        have := (sec33_mem_center_iff hYN _).mp hx y hy
        simpa [sec33ConjAut_apply] using this
  obtain ⟨g, hg⟩ := cor2Beta_c3_exists_inner hB hτ2 hsQ1 hsQ2 hτs hstar
  obtain ⟨g', rfl⟩ := QuotientGroup.mk_surjective g
  have h1 : ∀ a ∈ A, (g' : G) * a * (g' : G)⁻¹ * a⁻¹ ∈ Section3.N A Abar s := by
    intro a ha
    have h := hg (QuotientGroup.mk ⟨a, hAY ha⟩)
    rw [hτa a ha, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul,
      sec33_mk_eq_iff] at h
    have h' : a⁻¹ * ((g' : G) * a * (g' : G)⁻¹) ∈ Section3.N A Abar s := by simpa using h
    have := (Subgroup.mem_normalizer_iff.mp (hYN a (hAY ha)) _).mp h'
    have e : (g' : G) * a * (g' : G)⁻¹ * a⁻¹ = a * (a⁻¹ * ((g' : G) * a * (g' : G)⁻¹)) * a⁻¹ := by
      group
    rw [e]
    exact this
  have hgg : (QuotientGroup.mk (g' * g') : ↥(Section3.Y A Abar s) ⧸
      (Section3.N A Abar s).subgroupOf (Section3.Y A Abar s)) ∈ Subgroup.center _ := by
    rw [Subgroup.mem_center_iff]
    intro x
    have h := congrArg (fun φ : MulAut (↥(Section3.Y A Abar s) ⧸
      (Section3.N A Abar s).subgroupOf (Section3.Y A Abar s)) => φ x) hτ2
    simp only [MulAut.mul_apply, MulAut.one_apply, hg] at h
    rw [QuotientGroup.mk_mul]
    calc x * (QuotientGroup.mk g' * QuotientGroup.mk g')
        = (QuotientGroup.mk g' * (QuotientGroup.mk g' * x * (QuotientGroup.mk g')⁻¹) *
            (QuotientGroup.mk g')⁻¹) * (QuotientGroup.mk g' * QuotientGroup.mk g') := by rw [h]
      _ = (QuotientGroup.mk g' * QuotientGroup.mk g') * x := by group
  have h2 : ∀ y ∈ Section3.Y A Abar s,
      ((g' : G) * g') * y * ((g' : G) * g')⁻¹ * y⁻¹ ∈ Section3.N A Abar s := by
    intro y hy
    have := (sec33_mem_center_iff hYN (g' * g')).mp hgg y hy
    simpa using this
  obtain ⟨n, i, e, hKt⟩ :=
    CFSG.GH74.Uniqueness.Bender.isBenderGroup_iff_exists_benderType.mp hB
  obtain ⟨a, ha, hcen⟩ : ∃ a ∈ A, ∀ y ∈ Section3.Y A Abar s,
      ((g' : G) * a⁻¹) * y * ((g' : G) * a⁻¹)⁻¹ * y⁻¹ ∈ Section3.N A Abar s := by
    rcases hKt.cases' with ⟨hi, he, -⟩ | ⟨hi, he, -⟩ | ⟨hi, -, -⟩
    · subst hi
      subst he
      exact sec33_cr_aux hC hs hq (Or.inl rfl) hKt g'.2 h1 h2
    · subst hi
      subst he
      exact sec33_cr_aux hC hs hq (Or.inr rfl) hKt g'.2 h1 h2
    · subst hi
      exact (sec33_type3_false hC hs hKt hsY hsN g'.2 h1 h2 hg).elim
  have hcz : (QuotientGroup.mk (g' * ⟨a, hAY ha⟩⁻¹) : ↥(Section3.Y A Abar s) ⧸
      (Section3.N A Abar s).subgroupOf (Section3.Y A Abar s)) ∈ Subgroup.center _ := by
    refine (sec33_mem_center_iff hYN _).mpr fun y hy => ?_
    simpa using hcen y hy
  have hu : ∀ u ∈ Abar, s * u * s⁻¹ ∈ Section3.X A Abar ⊔ Section3.N A Abar s := by
    intro u hu
    have huY : u ∈ Section3.Y A Abar s := sec32d_Abar_le_Y hu
    have h := hg (QuotientGroup.mk ⟨u, huY⟩)
    rw [sec33Tau_mk] at h
    have hgz : (QuotientGroup.mk g' : ↥(Section3.Y A Abar s) ⧸
        (Section3.N A Abar s).subgroupOf (Section3.Y A Abar s)) =
        QuotientGroup.mk (g' * ⟨a, hAY ha⟩⁻¹) * QuotientGroup.mk ⟨a, hAY ha⟩ := by
      rw [← QuotientGroup.mk_mul]
      congr 1
      group
    have hzc := Subgroup.mem_center_iff.mp hcz
    rw [hgz] at h
    have h' : (QuotientGroup.mk (sec33ConjAut (Section3.Y A Abar s) hsY ⟨u, huY⟩) :
        ↥(Section3.Y A Abar s) ⧸ (Section3.N A Abar s).subgroupOf (Section3.Y A Abar s)) =
        QuotientGroup.mk ⟨a, hAY ha⟩ * QuotientGroup.mk ⟨u, huY⟩ *
          (QuotientGroup.mk ⟨a, hAY ha⟩)⁻¹ := by
      rw [h]
      generalize (QuotientGroup.mk (g' * ⟨a, hAY ha⟩⁻¹) : ↥(Section3.Y A Abar s) ⧸
        (Section3.N A Abar s).subgroupOf (Section3.Y A Abar s)) = z at hzc ⊢
      generalize (QuotientGroup.mk ⟨a, hAY ha⟩ : ↥(Section3.Y A Abar s) ⧸
        (Section3.N A Abar s).subgroupOf (Section3.Y A Abar s)) = α
      generalize (QuotientGroup.mk ⟨u, huY⟩ : ↥(Section3.Y A Abar s) ⧸
        (Section3.N A Abar s).subgroupOf (Section3.Y A Abar s)) = μ
      have hz1 : z * (α * μ * α⁻¹) = (α * μ * α⁻¹) * z := (hzc _).symm
      calc z * α * μ * (z * α)⁻¹ = z * (α * μ * α⁻¹) * z⁻¹ := by group
        _ = ((α * μ * α⁻¹) * z) * z⁻¹ := by rw [hz1]
        _ = α * μ * α⁻¹ := by group
    rw [← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul,
      sec33_mk_eq_iff] at h'
    have hw : (s * u * s⁻¹)⁻¹ * (a * u * a⁻¹) ∈ Section3.N A Abar s := by
      simpa [sec33ConjAut_apply] using h'
    have e : s * u * s⁻¹ = (a * u * a⁻¹) * ((s * u * s⁻¹)⁻¹ * (a * u * a⁻¹))⁻¹ := by group
    rw [e]
    refine Subgroup.mul_mem _ (Subgroup.mem_sup_left ?_) (Subgroup.mem_sup_right
      (Subgroup.inv_mem _ hw))
    rw [hC.x_eq]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mem_sup_left ha)
      (Subgroup.mem_sup_right hu)) (Subgroup.inv_mem _ (Subgroup.mem_sup_left ha))
  have hXA : A ≤ Section3.X A Abar := by rw [hC.x_eq]; exact le_sup_left
  have hXAb : Abar ≤ Section3.X A Abar := by rw [hC.x_eq]; exact le_sup_right
  unfold Section3.Y
  refine sup_le (sup_le (hXA.trans le_sup_left) (hXAb.trans le_sup_left)) ?_
  intro w hw
  obtain ⟨u, hu', rfl⟩ := (mem_conjSubgroup_exists_t77 s Abar w).1 hw
  exact hu u hu'


end Certified3

end CFSG.RankThree.GF2n.Tim77
