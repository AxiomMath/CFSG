module

public import CFSG.RankThree.PartOne.SLBN.LocalFive
public import CFSG.RankThree.PartOne.SLBN.SmallAction
public import CFSG.RankThree.PartOne.S9.Sylow.GlobalOddCore
public import CFSG.RankThree.PartTwo.ExponentPrimeSmallRank
public import CFSG.GroupTheory.FrattiniQuotient
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection4.lemma_4_5_a

public section

namespace CFSG.RankThree.PartOne.SLBN

open Subgroup CFSG CFSG.OrderReductions.FrattiniAutomorphisms
open scoped commutatorElement

variable {G : Type*} [Group G] [Finite G] {S : Type*} [Group S]

theorem isCyclic_of_local (φ : G →* S) (R : Subgroup G) [R.Normal] (hR3 : IsPGroup 3 R)
    (hRk : R ≤ φ.ker) (hrank : ∀ E : Subgroup G, IsElementaryAbelian 3 E → Nat.card E ≤ 27)
    {W₁ W₂ : Subgroup G} (h₁ : Comp G W₁) (h₂ : Comp G W₂)
    (hcomm : ∀ x ∈ W₁, ∀ y ∈ W₂, x * y = y * x)
    (he₁ : ∃ e ∈ W₁, e ^ 3 = 1 ∧ φ e ≠ 1) (he₂ : ∃ e ∈ W₂, e ^ 3 = 1 ∧ φ e ≠ 1)
    (hdisj : ∀ x ∈ W₁, ∀ y ∈ W₂, φ x = φ y → φ x ^ 2 = 1) : IsCyclic R := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  by_cases hR1 : R = ⊥
  · subst hR1
    infer_instance
  obtain ⟨D, hDR, hD1, hDnorm, hDexp, hDcomm, hDdet⟩ :=
    CFSG.RankThree.PartOne.Sec9B.exists_critical Nat.prime_three (by norm_num) hR3 hR1
  have hDN : D.Normal := by
    rw [← Subgroup.normalizer_eq_top_iff]
    refine eq_top_iff.mpr fun g _ => hDnorm g ?_
    rw [Subgroup.normalizer_eq_top_iff.mpr inferInstance]
    exact Subgroup.mem_top g
  have hDp : IsPGroup 3 D := hR3.to_le hDR
  have hexpD : ∀ x : D, x ^ 3 = 1 := fun x => Subtype.ext (hDexp x x.2)
  have hclass : commutator ↥D ≤ center ↥D := by
    rw [_root_.commutator_def, Subgroup.commutator_le]
    intro a _ b _
    have h1 := hDcomm (Subgroup.commutator_mem_commutator a.2 (hDR b.2))
    rw [Subgroup.mem_center_iff]
    intro c
    have h2 := Subgroup.mem_centralizer_iff.mp h1.2 (c : G) c.2
    exact Subtype.ext h2
  have hrankD : CFSG.pRank 3 ↥D ≤ 3 := by
    refine CFSG.RankThree.PartTwo.pRank_le_of_forall_isMulCommutative Nat.prime_three fun E hE => ?_
    have hEel : IsElementaryAbelian 3 (E.map D.subtype) := by
      refine { toIsMulCommutative := Subgroup.map_isMulCommutative E D.subtype, exponent_dvd_p := ?_ }
      refine Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr fun x => ?_
      obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp x.2
      apply Subtype.ext
      rw [Subgroup.coe_pow, ← hyx]
      simpa using hDexp y y.2
    have := hrank _ hEel
    rwa [Subgroup.card_map_of_injective D.subtype_injective] at this
  have hbound := CFSG.RankThree.PartTwo.class_two_small_rank_order_bounds hDp hexpD hclass
  have hfc : frattini ↥D = commutator ↥D :=
    CFSG.RankThree.PartTwo.frattini_eq_commutator hDp hexpD
  have hVp : IsPGroup 3 (↥D ⧸ frattini ↥D) := hDp.to_quotient _
  obtain ⟨n, hn⟩ := hVp.exists_card_eq
  have hVcard : Nat.card (↥D ⧸ frattini ↥D) = Nat.card (↥D ⧸ commutator ↥D) :=
    Nat.card_congr (QuotientGroup.quotientMulEquivOfEq hfc).toEquiv
  have hcommU : ∀ a b : ↥D ⧸ frattini ↥D, a * b = b * a := by
    intro a b
    have := CFSG.RankThree.PartTwo.isMulCommutative_quotient_commutator (P := ↥D)
    apply (QuotientGroup.quotientMulEquivOfEq hfc).injective
    rw [map_mul, map_mul]
    exact this.is_comm.comm _ _
  have hpowU : ∀ a : ↥D ⧸ frattini ↥D, a ^ 3 = 1 :=
    CFSG.RankThree.PartTwo.quotient_pow_eq_one hexpD _
  obtain ⟨ecoord⟩ := CFSG.SectionRank.Ccomm.nonempty_mulEquiv_of_elementary (p := 3) hcommU hpowU hn
  have hcardAut : Nat.card (MulAut (↥D ⧸ frattini ↥D)) =
      Nat.card (Matrix.GeneralLinearGroup (Fin n) (ZMod 3)) :=
    CFSG.SectionRank.Ccomm.card_mulAut_eq_card_GL ecoord
  have hnrank : CFSG.pRank 3 (↥D ⧸ commutator ↥D) = n := by
    have hk : Nat.card (↥D ⧸ commutator ↥D) = 3 ^ n := by rw [← hVcard, hn]
    exact (CFSG.RankThree.PartTwo.quotient_commutator_rank Nat.prime_three hexpD hk).2
  have hn4 : n ≤ 4 := by rw [← hnrank]; exact hbound.2.2 hrankD
  let ψ : G →* MulAut (↥D ⧸ frattini ↥D) :=
    (quotientAutomorphism (frattini ↥D)).comp MulAut.conjNormal
  have hA25 : ¬ 25 ∣ Nat.card (MulAut (↥D ⧸ frattini ↥D)) := by
    rw [hcardAut]
    exact not_dvd_card_GL_three (by omega)
  have hNR : ∀ g : G, g ∈ Subgroup.normalizer (R : Set G) := fun g => by
    rw [Subgroup.normalizer_eq_top_iff.mpr inferInstance]
    exact Subgroup.mem_top g
  have hcent : ∀ {W : Subgroup G}, Comp G W → (∀ w ∈ W, ψ w = 1) →
      ∀ w ∈ W, ∀ m ∈ R, w * m = m * w := by
    intro W hW htriv
    have := hW.perfect
    have hPker : IsPGroup 3 (quotientAutomorphism (frattini ↥D)).ker :=
      (CFSG.GroupTheory.frattini_automorphism_kernel hDp).2
    let α : W →* MulAut ↥D := MulAut.conjNormal.comp W.subtype
    have hα : α = 1 := eq_one_of_perfect_of_range_isPGroup α _ hPker (fun w => by
      rw [MonoidHom.mem_ker]
      exact htriv (w : G) w.2)
    have hDc : ∀ w ∈ W, ∀ d ∈ D, w * d = d * w := by
      intro w hw d hd
      have h := congrArg (fun a : MulAut ↥D => ((a ⟨d, hd⟩ : ↥D) : G)) (congrArg (fun f => f ⟨w, hw⟩) hα)
      simp only [α, MonoidHom.comp_apply, MulAut.conjNormal_apply] at h
      calc w * d = (w * d * w⁻¹) * w := by group
        _ = d * w := by rw [show w * d * w⁻¹ = d from h]
    have := normal_centralizer_of_normal R
    have hN : (Subgroup.centralizer (R : Set G)).subgroupOf W = ⊤ := by
      refine hW.eq_top_of_forall_coprime _ (fun g hg => ?_)
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_iff]
      intro m hm
      have hcop : Nat.Coprime (orderOf (g : G)) 3 := by rwa [Subgroup.orderOf_coe]
      have hfix := hDdet (g : G) (hNR g) (fun x hx => by
        rw [hDc g g.2 x hx, mul_inv_cancel_right]) hcop m hm
      calc m * (g : G) = ((g : G) * m * (g : G)⁻¹) * (g : G) := by rw [hfix]
        _ = (g : G) * m := inv_mul_cancel_right _ _
    intro w hw m hm
    have hw' : (⟨w, hw⟩ : W) ∈ (Subgroup.centralizer (R : Set G)).subgroupOf W := by
      rw [hN]; exact Subgroup.mem_top _
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_iff] at hw'
    exact (hw' m hm).symm
  have hn4' : ∀ {W : Subgroup G}, Comp G W → (¬ ∀ w ∈ W, ψ w = 1) → 4 ≤ n := by
    intro W hW hnt
    obtain ⟨h, h5, hψ, -⟩ := hW.exists_five_map_ne_one ψ hnt
    have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
    have hh5 : (h : G) ^ 5 = 1 := by
      have := pow_orderOf_eq_one h
      rw [h5] at this
      exact congrArg Subtype.val this
    have hord : orderOf (ψ (h : G)) = 5 :=
      orderOf_eq_prime (by rw [← map_pow, hh5, map_one]) hψ
    have hdvd : 5 ∣ Nat.card (Matrix.GeneralLinearGroup (Fin n) (ZMod 3)) := by
      rw [← hcardAut, ← hord]
      exact orderOf_dvd_natCard _
    by_contra hlt
    exact not_five_dvd_card_GL_three (by omega) hdvd
  have hz3 : ∀ {e : G}, e ^ 3 = 1 → ∀ x ∈ Subgroup.zpowers e, x ^ 3 = 1 := by
    intro e he x hx
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, he, one_zpow]
  have hord3 : ∀ {e : G}, e ^ 3 = 1 → φ e ≠ 1 → Nat.card (Subgroup.zpowers e) = 3 := by
    intro e he hφe
    have he1 : e ≠ 1 := fun h => hφe (by rw [h, map_one])
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime he he1
  have hphi1 : ∀ {e : G}, e ^ 3 = 1 → φ e ≠ 1 → ∀ x ∈ Subgroup.zpowers e,
      φ x ^ 2 = 1 → x = 1 := by
    intro e he hφe x hx hsq
    have h3 : φ x ^ 3 = 1 := by rw [← map_pow, hz3 he x hx, map_one]
    have h1 : φ x = 1 := by
      have : φ x = φ x ^ 3 * (φ x ^ 2)⁻¹ := by group
      rw [this, h3, hsq]; simp
    exact eq_one_of_mem_zpowers_of_map_eq_one φ he hφe hx h1
  have caseII : ∀ {W W' : Subgroup G}, Comp G W → (∀ w ∈ W, ψ w = 1) → Comp G W' →
      (¬ ∀ w ∈ W', ψ w = 1) → (∃ e ∈ W, e ^ 3 = 1 ∧ φ e ≠ 1) → False := by
    intro W W' hW htW hW' hnt he
    obtain ⟨e, heW, he3, heφ⟩ := he
    have hn4'' := hn4' hW' hnt
    have hr3 : 3 ≤ CFSG.pRank 3 ↥D := by
      by_contra hlt
      have h2 : CFSG.pRank 3 ↥D ≤ 2 := by omega
      have := hbound.1 h2
      omega
    obtain ⟨E, hEc, hEcard⟩ :=
      CFSG.RankThree.PartTwo.exists_isMulCommutative_card_eq_pRank (P := ↥D) Nat.prime_three
    have hpR : CFSG.pRank 3 ↥D = 3 := le_antisymm hrankD hr3
    rw [hpR] at hEcard
    have hEel : IsElementaryAbelian 3 E :=
      CFSG.RankThree.PartTwo.isElementaryAbelian_of_isMulCommutative hEc
        (fun x => CFSG.RankThree.PartTwo.subgroup_pow_eq_one hexpD E x)
    have hE'el : IsElementaryAbelian 3 (E.map D.subtype) :=
      CFSG.RankThree.PartOne.SRC.isElementaryAbelian_map' D.subtype hEel
    have hE'card : Nat.card (E.map D.subtype) = 27 := by
      rw [Subgroup.card_map_of_injective D.subtype_injective, hEcard]; norm_num
    have hE'R : ∀ x ∈ E.map D.subtype, x ∈ R := by
      rintro _ ⟨y, -, rfl⟩
      exact hDR y.2
    obtain ⟨E₃, hE₃, hcard, -⟩ := exists_isElementaryAbelian_sup (p := 3) hE'el
      (IsElementaryAbelian.zpowers_of_pow_eq_one he3)
      (fun a ha b hb => by
        obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
        exact ((Commute.symm (show Commute e a from hcent hW htW e heW a (hE'R a ha))).zpow_right
          k).eq)
      (fun x hx hxe => by
        have hφx : φ x = 1 := hRk (hE'R x hx)
        exact eq_one_of_mem_zpowers_of_map_eq_one φ he3 heφ hxe hφx)
    have := hrank E₃ hE₃
    rw [hcard, hE'card, hord3 he3 heφ] at this
    omega
  by_cases ht₁ : ∀ w ∈ W₁, ψ w = 1 <;> by_cases ht₂ : ∀ w ∈ W₂, ψ w = 1
  ·
    by_contra hnc
    have : Fact (IsPGroup 3 ↥R) := ⟨hR3⟩
    obtain ⟨ER, -, hERcard, hERel⟩ := CFSG.lemma_4_5_a (p := 3) (by norm_num) hnc
    have hER'el : IsElementaryAbelian 3 (ER.map R.subtype) :=
      CFSG.RankThree.PartOne.SRC.isElementaryAbelian_map' R.subtype hERel
    have hER'card : Nat.card (ER.map R.subtype) = 9 := by
      rw [Subgroup.card_map_of_injective R.subtype_injective, hERcard]; norm_num
    have hER'R : ∀ x ∈ ER.map R.subtype, x ∈ R := by
      rintro _ ⟨y, -, rfl⟩
      exact y.2
    obtain ⟨e₁, he₁W, he₁3, he₁φ⟩ := he₁
    obtain ⟨e₂, he₂W, he₂3, he₂φ⟩ := he₂
    have hc12 : Commute e₁ e₂ := hcomm e₁ he₁W e₂ he₂W
    have hz1W : Subgroup.zpowers e₁ ≤ W₁ := Subgroup.zpowers_le.2 he₁W
    have hz2W : Subgroup.zpowers e₂ ≤ W₂ := Subgroup.zpowers_le.2 he₂W
    obtain ⟨E₂, hE₂el, hE₂card, hE₂mem, -, -⟩ := exists_isElementaryAbelian_sup (p := 3)
      (IsElementaryAbelian.zpowers_of_pow_eq_one he₁3)
      (IsElementaryAbelian.zpowers_of_pow_eq_one he₂3)
      (fun a ha b hb => by
        obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
        obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
        exact (hc12.zpow_zpow i j).eq)
      (fun x hx1 hx2 => hphi1 he₁3 he₁φ x hx1 (hdisj x (hz1W hx1) x (hz2W hx2) rfl))
    obtain ⟨E, hEel, hEcard, -⟩ := exists_isElementaryAbelian_sup (p := 3) hE₂el hER'el
      (fun a ha b hb => by
        obtain ⟨a₁, ha₁, a₂, ha₂, rfl⟩ := hE₂mem a ha
        have h1 := hcent h₁ ht₁ a₁ (hz1W ha₁) b (hER'R b hb)
        have h2 := hcent h₂ ht₂ a₂ (hz2W ha₂) b (hER'R b hb)
        calc a₁ * a₂ * b = a₁ * (a₂ * b) := by rw [mul_assoc]
          _ = a₁ * (b * a₂) := by rw [h2]
          _ = a₁ * b * a₂ := by rw [mul_assoc]
          _ = b * a₁ * a₂ := by rw [h1]
          _ = b * (a₁ * a₂) := by rw [mul_assoc])
      (fun x hx hxR => by
        obtain ⟨a₁, ha₁, a₂, ha₂, rfl⟩ := hE₂mem x hx
        have hφx : φ (a₁ * a₂) = 1 := hRk (hER'R _ hxR)
        rw [map_mul] at hφx
        have hq : φ a₁ = φ a₂⁻¹ := by
          rw [map_inv]; exact eq_inv_of_mul_eq_one_left hφx
        have hsq := hdisj a₁ (hz1W ha₁) a₂⁻¹ (Subgroup.inv_mem _ (hz2W ha₂)) hq
        have ha1 : a₁ = 1 := hphi1 he₁3 he₁φ a₁ ha₁ hsq
        have hφ2 : φ a₂ = 1 := by rw [ha1, map_one, one_mul] at hφx; exact hφx
        have ha2 : a₂ = 1 :=
          eq_one_of_mem_zpowers_of_map_eq_one φ he₂3 he₂φ ha₂ hφ2
        rw [ha1, ha2, one_mul])
    have := hrank E hEel
    rw [hEcard, hE₂card, hER'card, hord3 he₁3 he₁φ, hord3 he₂3 he₂φ] at this
    omega
  · exact (caseII h₁ ht₁ h₂ ht₂ he₁).elim
  · exact (caseII h₂ ht₂ h₁ ht₁ he₂).elim
  · exact (false_of_both_nontrivial ψ h₁ h₂ hcomm ht₁ ht₂ hA25).elim

end CFSG.RankThree.PartOne.SLBN
