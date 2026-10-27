module

public import CFSG.RankThree.GF2n.Tim78S44Aux
import CFSG.RankThree.GF2n.Tim77Prop24Core
import CFSG.RankThree.GF2n.Tim77TI
import CFSG.RankThree.GF2n.Tim78Involution

public section

namespace CFSG.RankThree.GF2n.Tim78

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.RankThree.GF2n
open scoped commutatorElement

variable {G : Type} [Group G]

theorem isElemAbelian_conjSubgroup {A : Subgroup G} (hA : Assembly.IsElemAbelian 2 A) (g : G) :
    Assembly.IsElemAbelian 2 (conjSubgroup g A) := by
  obtain ⟨hc, h2⟩ := hA
  refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, fun x hx => ?_⟩
  · obtain ⟨a', ha', ha⟩ := Subgroup.mem_map.mp a.2
    obtain ⟨b', hb', hb⟩ := Subgroup.mem_map.mp b.2
    have h := congrArg Subtype.val (hc.is_comm.comm ⟨a', ha'⟩ ⟨b', hb'⟩)
    rw [Subgroup.coe_mul, Subgroup.coe_mul, ← ha, ← hb, ← map_mul, ← map_mul]
    exact congrArg _ h
  · obtain ⟨x', hx', rfl⟩ := Subgroup.mem_map.mp hx
    rw [← map_pow, h2 x' hx', map_one]

namespace Hyp4

variable [Finite G] {M B Q P T : Subgroup G} (H : Hyp4 M B Q P T)
include H

section Certified


theorem commute_conj_pair {g e p : G} (hBBg : B ⊓ conjSubgroup g B = ⊥)
    (hBBgc : ∀ a ∈ B, ∀ b ∈ conjSubgroup g B, a * b = b * a)
    (heBg : e ∈ conjSubgroup g B) (heQ : e ∈ Q) (he1 : e ≠ 1) (hp : p ∈ Q) :
    ∀ y ∈ conjSubgroup g B, ∀ y' ∈ conjSubgroup p (conjSubgroup g B), y * y' = y' * y := by
  classical
  intro y hy y' hy'
  set Bg := conjSubgroup g B with hBgdef
  set Ab := conjSubgroup p Bg with hAbdef
  have hBgel : Assembly.IsElemAbelian 2 Bg := isElemAbelian_conjSubgroup H.elemAb g
  have hAbel : Assembly.IsElemAbelian 2 Ab := isElemAbelian_conjSubgroup hBgel p
  have hBgti : IsTI Bg := isTI_conjSubgroup H.ti g
  have hAbti : IsTI Ab := isTI_conjSubgroup hBgti p
  by_cases hpN : p ∈ Subgroup.normalizer (Bg : Set G)
  · have : Ab = Bg := conjSubgroup_eq_self_iff.mpr hpN
    rw [this] at hy'
    exact comm_of_isElemAbelian hBgel hy hy'
  have hb : ⁅p, e⁆ ∈ B := H.commutator_mem hp heQ
  set b := ⁅p, e⁆ with hbdef
  have hb1 : b ≠ 1 := by
    intro h1
    apply hpN
    have hpe : p * e = e * p := commutatorElement_eq_one_iff_mul_comm.mp h1
    have := H.centralizer_le_conj heBg he1 (Subgroup.mem_centralizer_singleton_iff.mpr hpe)
    rwa [← H.normalizer_conj_eq] at this
  set e' := p * e * p⁻¹ with he'def
  have he'b : e' = b * e := by rw [he'def, hbdef, commutatorElement_def]; group
  have he'Ab : e' ∈ Ab := by
    rw [hAbdef, mem_conjSubgroup, he'def, show p⁻¹ * (p * e * p⁻¹) * p = e by group]
    exact heBg
  have he'1 : e' ≠ 1 := fun h => he1 (by
    calc e = p⁻¹ * (p * e * p⁻¹) * p := by group
      _ = 1 := by rw [← he'def, h]; group)
  have hcomm : e * e' = e' * e := by
    rw [he'b]
    have := H.center_Q hb heQ
    calc e * (b * e) = (e * b) * e := by group
      _ = (b * e) * e := by rw [← this]
  have he'N : e' ∈ Subgroup.normalizer (Bg : Set G) := by
    have := H.centralizer_le_conj heBg he1 (Subgroup.mem_centralizer_singleton_iff.mpr hcomm.symm)
    rwa [← H.normalizer_conj_eq] at this
  have hAbeq : Ab = conjSubgroup (p * g) B := by rw [hAbdef, hBgdef, ← conjSubgroup_mul]
  have heN : e ∈ Subgroup.normalizer (Ab : Set G) := by
    have he'' : e' ∈ conjSubgroup (p * g) B := hAbeq ▸ he'Ab
    have := H.centralizer_le_conj he'' he'1 (Subgroup.mem_centralizer_singleton_iff.mpr hcomm)
    rwa [← H.normalizer_conj_eq, ← hAbeq] at this
  by_cases hLA : Bg ⊓ Subgroup.normalizer (Ab : Set G) = Bg
  ·
    have hAN : Bg ≤ Subgroup.normalizer (Ab : Set G) := hLA ▸ inf_le_right
    have hconj : conjSubgroup p⁻¹ Ab = Bg := by
      rw [hAbdef, ← conjSubgroup_mul, inv_mul_cancel, conjSubgroup_one]
    have h23 := Tim77.tim77_2_3 hAbel hAbti (g := p⁻¹) (by rw [hconj]; exact hAN)
    rw [hconj] at h23
    exact comm_of_isElemAbelian h23 (Subgroup.mem_sup_right hy) (Subgroup.mem_sup_left hy')
  · exfalso
    set L := Bg ⊓ Subgroup.normalizer (Ab : Set G) with hLdef
    set Lb := Ab ⊓ Subgroup.normalizer (Bg : Set G) with hLbdef
    have hLbot : L ≠ ⊥ := by
      intro hbot
      have : e ∈ L := Subgroup.mem_inf.mpr ⟨heBg, heN⟩
      rw [hbot, Subgroup.mem_bot] at this
      exact he1 this
    have S : Tim77.Prop24Setup Bg Ab L Lb (L ⊔ Lb) :=
      ⟨hBgel, hBgti, ⟨p, rfl⟩, rfl, rfl, rfl, hLbot, hLA⟩
    have heL : e ∈ L := Subgroup.mem_inf.mpr ⟨heBg, heN⟩
    have he'L : e' ∈ Lb := Subgroup.mem_inf.mpr ⟨he'Ab, he'N⟩
    have hbM : b ∈ L ⊔ Lb := by
      have : b = e' * e⁻¹ := by rw [he'b]; group
      rw [this]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_right he'L)
        (Subgroup.inv_mem _ (Subgroup.mem_sup_left heL))
    obtain ⟨t, htA, htL⟩ := IsConcreteLE.exists_of_lt (lt_of_le_of_ne S.L_le S.ne)
    have hbL : b ∈ L := S.mem_L_of_commute_M htA htL hbM (hBBgc b hb t htA).symm
    have : b ∈ B ⊓ Bg := ⟨hb, S.L_le hbL⟩
    rw [hBBg, Subgroup.mem_bot] at this
    exact hb1 this

theorem commutator_conj_mem_B {g e : G} (hBBg : B ⊓ conjSubgroup g B = ⊥)
    (hBBgc : ∀ a ∈ B, ∀ b ∈ conjSubgroup g B, a * b = b * a)
    (heBg : e ∈ conjSubgroup g B) (heQ : e ∈ Q) (he1 : e ≠ 1)
    (hBgM : conjSubgroup g B ≤ M) (hBgP : conjSubgroup g B ⊓ P = ⊥)
    (hBgT : conjSubgroup g B ⊓ T = ⊥) :
    ∀ y ∈ conjSubgroup g B, ∀ p ∈ P, ⁅y, p⁆ ∈ B := by
  classical
  set Bg := conjSubgroup g B with hBgdef
  set C := P ⊓ Subgroup.centralizer ({e} : Set G) with hCdef
  have hCN : ∀ c ∈ C, c ∈ Subgroup.normalizer (Bg : Set G) := fun c hc => by
    have := H.centralizer_le_conj heBg he1 hc.2
    rwa [← H.normalizer_conj_eq g] at this
  have hBgNP : ∀ y ∈ Bg, y ∈ Subgroup.normalizer (P : Set G) := fun y hy =>
    H.M_le_normalizer_P (hBgM hy)
  have hBC : B ≤ C := fun b hb =>
    ⟨H.B_le_P hb, Subgroup.mem_centralizer_singleton_iff.mpr (H.center_Q hb heQ)⟩
  have hBgC : ∀ y ∈ Bg, ∀ c ∈ C, y * c = c * y := by
    intro y hy c hc
    have h1 : ⁅y, c⁆ ∈ Bg := by
      have e0 : ⁅y, c⁆ = y * (c * y⁻¹ * c⁻¹) := by simp only [commutatorElement_def]; group
      rw [e0]
      exact Bg.mul_mem hy ((Subgroup.mem_normalizer_iff.mp (hCN c hc) y⁻¹).mp (Bg.inv_mem hy))
    have h2 : ⁅y, c⁆ ∈ P := by
      have e0 : ⁅y, c⁆ = (y * c * y⁻¹) * c⁻¹ := rfl
      rw [e0]
      exact P.mul_mem ((Subgroup.mem_normalizer_iff.mp (hBgNP y hy) c).mp hc.1) (P.inv_mem hc.1)
    have h3 : ⁅y, c⁆ ∈ Bg ⊓ P := ⟨h1, h2⟩
    rw [hBgP, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at h3
    exact h3
  obtain ⟨h, hhQ, hhC⟩ : ∃ h : G, conjSubgroup h B ≤ Q ∧ ¬ conjSubgroup h B ≤ C := by
    by_contra hcon
    push Not at hcon
    have hPC : P ≤ C := by
      rw [H.hP]
      exact iSup₂_le fun h hh => hcon h hh
    have heT : e ∈ T := by
      rw [H.hT]
      exact ⟨heQ, Subgroup.mem_centralizer_iff.mpr fun p hp =>
        Subgroup.mem_centralizer_singleton_iff.mp (hPC hp).2⟩
    have : e ∈ Bg ⊓ T := ⟨heBg, heT⟩
    rw [hBgT, Subgroup.mem_bot] at this
    exact he1 this
  set Bh := conjSubgroup h B with hBhdef
  have hhP : Bh ≤ P := H.conj_le_P hhQ
  have hhB : Bh ≠ B := fun hh => hhC (hh ▸ hBC)
  have hBBh : B ⊓ Bh = ⊥ := inf_conjSubgroup_eq_bot_of_isTI H.ti hhB
  have hBhe : ∀ u ∈ Bh, u * e = e * u → u = 1 := by
    intro u hu hue
    by_contra hu1
    have heN : e ∈ Subgroup.normalizer (Bh : Set G) := by
      have := H.centralizer_le_conj hu hu1 (Subgroup.mem_centralizer_singleton_iff.mpr hue.symm)
      rwa [← H.normalizer_conj_eq h] at this
    apply hhC
    intro u' hu'
    refine ⟨hhP hu', Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
    have h1 : ⁅e, u'⁆ ∈ Bh := by
      have e0 : ⁅e, u'⁆ = (e * u' * e⁻¹) * u'⁻¹ := rfl
      rw [e0]
      exact Bh.mul_mem ((Subgroup.mem_normalizer_iff.mp heN u').mp hu') (Bh.inv_mem hu')
    have h2 : ⁅e, u'⁆ ∈ B := H.commutator_mem heQ (H.P_le_Q (hhP hu'))
    have h3 : ⁅e, u'⁆ ∈ B ⊓ Bh := ⟨h2, h1⟩
    rw [hBBh, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at h3
    exact h3.symm
  have hPfac : ∀ p ∈ P, ∃ u ∈ Bh, ∃ c ∈ C, p = u * c := by
    let f : Bh → B := fun u => ⟨⁅(u : G), e⁆, H.commutator_mem (H.P_le_Q (hhP u.2)) heQ⟩
    have hf : Function.Injective f := by
      intro u u' hu
      have h1 : ⁅(u : G), e⁆ = ⁅(u' : G), e⁆ := congrArg Subtype.val hu
      have h2 : (u : G) * e * (u : G)⁻¹ = (u' : G) * e * (u' : G)⁻¹ := by
        have := h1
        simp only [commutatorElement_def] at this
        exact mul_right_cancel this
      have h3 : ((u : G)⁻¹ * u') * e = e * ((u : G)⁻¹ * u') := by
        calc ((u : G)⁻¹ * u') * e = (u : G)⁻¹ * ((u' : G) * e * (u' : G)⁻¹) * u' := by group
          _ = (u : G)⁻¹ * ((u : G) * e * (u : G)⁻¹) * u' := by rw [h2]
          _ = e * ((u : G)⁻¹ * u') := by group
      have h4 : (u : G)⁻¹ * u' = 1 := hBhe _ (Bh.mul_mem (Bh.inv_mem u.2) u'.2) h3
      exact Subtype.ext (inv_mul_eq_one.mp h4)
    have hcard : Nat.card B ≤ Nat.card Bh := (card_conjSubgroup h B).symm.le
    have hbij := hf.bijective_of_nat_card_le hcard
    intro p hp
    obtain ⟨u, hu⟩ := hbij.2 ⟨⁅p, e⁆, H.commutator_mem (H.P_le_Q hp) heQ⟩
    have h1 : ⁅(u : G), e⁆ = ⁅p, e⁆ := congrArg Subtype.val hu
    have h2 : (u : G) * e * (u : G)⁻¹ = p * e * p⁻¹ := by
      have := h1
      simp only [commutatorElement_def] at this
      exact mul_right_cancel this
    refine ⟨u, u.2, (u : G)⁻¹ * p, ⟨P.mul_mem (P.inv_mem (hhP u.2)) hp,
      Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩, by group⟩
    calc (u : G)⁻¹ * p * e = (u : G)⁻¹ * (p * e * p⁻¹) * p := by group
      _ = (u : G)⁻¹ * ((u : G) * e * (u : G)⁻¹) * p := by rw [h2]
      _ = e * ((u : G)⁻¹ * p) := by group
  have hBgel : Assembly.IsElemAbelian 2 Bg := isElemAbelian_conjSubgroup H.elemAb g
  have hkey : ∀ y ∈ Bg, ∀ u ∈ Bh, ⁅y, u⁆ ∈ B := by
    intro y hy u hu
    have huP := hhP hu
    have huQ := H.P_le_Q huP
    have hyM := hBgM hy
    set z := ⁅y, u⁆ with hz
    have hzP : z ∈ P := by
      have e0 : z = (y * u * y⁻¹) * u⁻¹ := rfl
      rw [e0]
      exact P.mul_mem ((Subgroup.mem_normalizer_iff.mp (hBgNP y hy) u).mp huP) (P.inv_mem huP)
    have hy2 : y * y = 1 := by rw [← sq]; exact hBgel.2 y hy
    have hy''Bg : u * y⁻¹ * u⁻¹ ∈ conjSubgroup u Bg := by
      rw [mem_conjSubgroup, show u⁻¹ * (u * y⁻¹ * u⁻¹) * u = y⁻¹ by group]
      exact Bg.inv_mem hy
    have hcommy := H.commute_conj_pair hBBg hBBgc heBg heQ he1 huQ y hy _ hy''Bg
    have hy''2 : (u * y⁻¹ * u⁻¹) * (u * y⁻¹ * u⁻¹) = 1 := by
      calc (u * y⁻¹ * u⁻¹) * (u * y⁻¹ * u⁻¹) = u * (y * y)⁻¹ * u⁻¹ := by group
        _ = 1 := by rw [hy2]; group
    have hzz : z * z = 1 := by
      have e0 : z = y * (u * y⁻¹ * u⁻¹) := by rw [hz]; simp only [commutatorElement_def]; group
      rw [e0]
      calc y * (u * y⁻¹ * u⁻¹) * (y * (u * y⁻¹ * u⁻¹))
          = y * ((u * y⁻¹ * u⁻¹) * y) * (u * y⁻¹ * u⁻¹) := by group
        _ = y * (y * (u * y⁻¹ * u⁻¹)) * (u * y⁻¹ * u⁻¹) := by rw [← hcommy]
        _ = (y * y) * ((u * y⁻¹ * u⁻¹) * (u * y⁻¹ * u⁻¹)) := by group
        _ = 1 := by rw [hy2, hy''2]; group
    have hzu : z * u = u * z := by
      have hu2B : u * u ∈ B := by rw [← sq]; exact H.sq_mem huQ
      have h1 : ⁅y, u * u⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.mpr (hBBgc _ hu2B y hy).symm
      have e0 : ⁅y, u * u⁆ = z * (u * z * u⁻¹) := by
        rw [hz]; simp only [commutatorElement_def]; group
      rw [e0] at h1
      have h2 : u * z * u⁻¹ = z := by
        have : u * z * u⁻¹ = z⁻¹ := eq_inv_of_mul_eq_one_right h1
        rw [this]
        exact inv_eq_of_mul_eq_one_right hzz
      calc z * u = (u * z * u⁻¹) * u := by rw [h2]
        _ = u * z := by group
    have hzC : ∀ c ∈ C, c * z = z * c := by
      intro c hc
      have h1 : ⁅u, ⁅c⁻¹, y⁻¹⁆⁆ = 1 := by
        have : ⁅c⁻¹, y⁻¹⁆ = 1 := by
          rw [commutatorElement_eq_one_iff_mul_comm]
          exact (hBgC y⁻¹ (Bg.inv_mem hy) c⁻¹ (C.inv_mem hc)).symm
        rw [this, commutatorElement_one_right]
      have h2 : ⁅y⁻¹, ⁅u⁻¹, c⁆⁆ = 1 := by
        rw [commutatorElement_eq_one_iff_mul_comm]
        exact (hBBgc _ (H.commutator_mem (H.P_le_Q (P.inv_mem huP)) (H.P_le_Q hc.1)) y⁻¹
          (Bg.inv_mem hy)).symm
      exact commutatorElement_eq_one_iff_mul_comm.mp
        (commutator_eq_one_of_rotate (x := y) (y := u) (z := c) h1 h2)
    have hzBh : ∀ u' ∈ Bh, u' * z = z * u' := by
      by_cases hu1 : u = 1
      · intro u' _
        have : z = 1 := by rw [hz, hu1, commutatorElement_one_right]
        rw [this]
        group
      · have hzN : z ∈ Subgroup.normalizer (Bh : Set G) := by
          have := H.centralizer_le_conj hu hu1 (Subgroup.mem_centralizer_singleton_iff.mpr hzu)
          rwa [← H.normalizer_conj_eq h] at this
        intro u' hu'
        have h1 : ⁅z, u'⁆ ∈ Bh := by
          have e0 : ⁅z, u'⁆ = (z * u' * z⁻¹) * u'⁻¹ := rfl
          rw [e0]
          exact Bh.mul_mem ((Subgroup.mem_normalizer_iff.mp hzN u').mp hu') (Bh.inv_mem hu')
        have h2 : ⁅z, u'⁆ ∈ B := H.commutator_mem (H.P_le_Q hzP) (H.P_le_Q (hhP hu'))
        have h3 : ⁅z, u'⁆ ∈ B ⊓ Bh := ⟨h2, h1⟩
        rw [hBBh, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at h3
        exact h3.symm
    have hzZ : z ∈ P ⊓ Subgroup.centralizer (P : Set G) := by
      refine ⟨hzP, Subgroup.mem_centralizer_iff.mpr fun p hp => ?_⟩
      obtain ⟨u', hu', c, hc, rfl⟩ := hPfac p hp
      calc u' * c * z = u' * (c * z) := by group
        _ = u' * (z * c) := by rw [hzC c hc]
        _ = (u' * z) * c := by group
        _ = (z * u') * c := by rw [hzBh u' hu']
        _ = z * (u' * c) := by group
    rwa [H.inf_centralizer_P] at hzZ
  intro y hy p hp
  obtain ⟨u, hu, c, hc, rfl⟩ := hPfac p hp
  have hyc : ⁅y, c⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.mpr (hBgC y hy c hc)
  have e0 : ⁅y, u * c⁆ = ⁅y, u⁆ * (u * ⁅y, c⁆ * u⁻¹) := by
    simp only [commutatorElement_def]; group
  rw [e0, hyc]
  simpa using hkey y hy u hu

end Certified

end Hyp4

end CFSG.RankThree.GF2n.Tim78
