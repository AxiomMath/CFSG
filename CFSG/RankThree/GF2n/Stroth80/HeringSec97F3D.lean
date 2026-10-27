module

public import CFSG.RankThree.GF2n.Stroth80.HeringSec97F3C
public import CFSG.RankThree.GF2n.Stroth80.HeringSec97F2
public import CFSG.RankThree.GF2n.Stroth80.HeringSec97F3B

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix Pointwise

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

namespace HS9

theorem lineGeom_of_QB (hc : Ctx M Q Z B) {h : G} (hh : h ∈ M) (hFB : conjSubgroup h B ≤ QB B) :
    LineGeom M Q Z B h := by
  have hcF : Ctx M Q Z (conjSubgroup h B) := hc.conj_of_mem hh
  have hFQ : conjSubgroup h B ≤ Q := hcF.le
  by_cases hF : conjSubgroup h B ≤ Z ⊔ B
  ·
    have hFle : conjSubgroup h B ≤ B ⊔ Z := by rw [sup_comm]; exact hF
    have hconj : conjSubgroup h (LB M Q B) = LB M Q B := hc.conj_LB_eq_of_le_sup_Z hh hFle
    have hLFeq : LB M Q (conjSubgroup h B) = LB M Q B := by rw [hc.LB_conj hh, hconj]
    have hV : Z ⊔ B ⊔ conjSubgroup h B = Z ⊔ B := sup_eq_left.mpr hF
    refine ⟨fun x hx => ?_, fun P hP hPle => ?_⟩
    · rw [hLFeq, sup_idem] at hx
      rw [hV]
      have hLB : LB M Q B ≤ Subgroup.normalizer ((Z ⊔ B : Subgroup G) : Set G) := by
        unfold LB
        exact sup_le (Smith81.Ctx.Q_le_normalizer_ZB hc)
          (inf_le_left.trans (Smith81.Ctx.QB_le_normalizer_ZB hc))
      exact conjSubgroup_eq_self_iff.mpr (hLB hx)
    · obtain ⟨m, hmM, rfl⟩ := hP
      rw [hV] at hPle
      left
      have hPle' : conjSubgroup m B ≤ B ⊔ Z := by rw [sup_comm]; exact hPle
      rw [hc.LB_conj hmM, hc.conj_LB_eq_of_le_sup_Z hmM hPle']
  ·
    have hFB' : conjSubgroup h B ≠ B := fun h' => hF (by rw [h']; exact le_sup_right)
    obtain ⟨gB, hgB⟩ := hc.conj
    obtain ⟨gF, hgF⟩ := hcF.conj
    have hBF : B ≤ QB (conjSubgroup h B) :=
      (hc.hyp.le_QB_iff_le_QB ⟨gB, hgB⟩ ⟨gF, hgF⟩ (Ne.symm hFB')).mpr hFB
    have hQM : Q ≤ M := hc.hyp.Q_normal.1
    have hLB1 : LB M Q B ≤
        Subgroup.normalizer ((Z ⊔ B ⊔ conjSubgroup h B : Subgroup G) : Set G) := by
      unfold LB
      refine sup_le (fun q hq => ?_) (fun x hx => ?_)
      · exact conjSubgroup_eq_self_iff.mp (Q_conj_V hc hcF hq)
      · exact conjSubgroup_eq_self_iff.mp (QB_inf_M_conj_V hc hFB hx.1 hx.2)
    have hLB2 : LB M Q (conjSubgroup h B) ≤
        Subgroup.normalizer ((Z ⊔ B ⊔ conjSubgroup h B : Subgroup G) : Set G) := by
      unfold LB
      refine sup_le (fun q hq => ?_) (fun x hx => ?_)
      · exact conjSubgroup_eq_self_iff.mp (Q_conj_V hc hcF hq)
      · exact conjSubgroup_eq_self_iff.mp (QF_inf_M_conj_V hc hcF hBF hx.1 hx.2)
    refine ⟨fun x hx => conjSubgroup_eq_self_iff.mpr (sup_le hLB1 hLB2 hx), ?_⟩
    rintro P ⟨m, hmM, rfl⟩ hPle
    have hcP : Ctx M Q Z (conjSubgroup m B) := hc.conj_of_mem hmM
    obtain ⟨b₁, hb₁, hb₁1⟩ := exists_ne_one_mem hc
    obtain ⟨p, hpP, hp1⟩ : ∃ p ∈ conjSubgroup m B, p ≠ 1 := by
      refine ⟨m * b₁ * m⁻¹, mem_conjSubgroup.mpr ?_, ?_⟩
      · rw [show m⁻¹ * (m * b₁ * m⁻¹) * m = b₁ by group]
        exact hb₁
      · intro h1
        apply hb₁1
        have : b₁ = m⁻¹ * (m * b₁ * m⁻¹) * m := by group
        rw [this, h1]
        group
    obtain ⟨z, hz, b, hb, f, hf, hpe⟩ := mem_sup_sup_iff hc hFQ (hPle hpP)
    have hpZ : p ∉ Z := by
      intro h'
      have : p ∈ Z ⊓ conjSubgroup m B := ⟨h', hpP⟩
      rw [hcP.inf_eq_bot, Subgroup.mem_bot] at this
      exact hp1 this
    have hLQ : ∀ {X : Subgroup G} {q : G}, q ∈ Q → conjSubgroup q (LB M Q X) = LB M Q X :=
      fun hq => conjSubgroup_eq_self_iff.mpr (Subgroup.le_normalizer (Subgroup.mem_sup_left hq))
    by_cases hf1 : f = 1
    ·
      subst hf1
      have hb1 : b ≠ 1 := by
        intro hb1
        apply hpZ
        rw [hpe, hb1]
        simpa using hz
      obtain ⟨q, hq, hqe⟩ := exists_conj_eq_mul hc hz hb hb1
      have hqM : q ∈ M := hQM hq
      have hpq : p ∈ conjSubgroup q B := by
        rw [mem_conjSubgroup]
        have : p = q * b * q⁻¹ := by rw [hpe, mul_one, hqe]
        rw [this, show q⁻¹ * (q * b * q⁻¹) * q = b by group]
        exact hb
      have hne : conjSubgroup m B ⊓ conjSubgroup q B ≠ ⊥ := by
        intro h0
        have : p ∈ conjSubgroup m B ⊓ conjSubgroup q B := ⟨hpP, hpq⟩
        rw [h0, Subgroup.mem_bot] at this
        exact hp1 this
      obtain ⟨gP, hgP⟩ := hcP.conj
      obtain ⟨gq, hgq⟩ := (hc.conj_of_mem hqM).conj
      have hPq : conjSubgroup m B = conjSubgroup q B :=
        eq_of_inf_ne_bot_conj hc.hyp.ti ⟨gP, hgP⟩ ⟨gq, hgq⟩ hne
      left
      rw [hPq, hc.LB_conj hqM, hLQ hq]
    ·
      obtain ⟨ε, hε, hεf⟩ := exists_mem_QB_inf_M_comm_eq hc hcF hFB hF hf hf1 hb
      have hεM : ε ∈ M := hε.2
      have hw : ε * f * ε⁻¹ = b * f := by
        have h1 : ε * f * ε⁻¹ * f⁻¹ = b := hεf
        calc ε * f * ε⁻¹ = (ε * f * ε⁻¹ * f⁻¹) * f := by group
          _ = b * f := by rw [h1]
      have hcF' : Ctx M Q Z (conjSubgroup ε (conjSubgroup h B)) := hcF.conj_of_mem hεM
      have hwF' : b * f ∈ conjSubgroup ε (conjSubgroup h B) := by
        rw [← hw, mem_conjSubgroup, show ε⁻¹ * (ε * f * ε⁻¹) * ε = f by group]
        exact hf
      have hw1 : b * f ≠ 1 := by
        intro h1
        apply hf1
        rw [← hw] at h1
        have : f = ε⁻¹ * (ε * f * ε⁻¹) * ε := by group
        rw [this, h1]
        group
      obtain ⟨q, hq, hqe⟩ := exists_conj_eq_mul hcF' hz hwF' hw1
      have hqM : q ∈ M := hQM hq
      have hpq : p ∈ conjSubgroup q (conjSubgroup ε (conjSubgroup h B)) := by
        rw [mem_conjSubgroup]
        have : p = q * (b * f) * q⁻¹ := by rw [hqe, hpe, mul_assoc]
        rw [this, show q⁻¹ * (q * (b * f) * q⁻¹) * q = b * f by group]
        exact hwF'
      have hcq : Ctx M Q Z (conjSubgroup q (conjSubgroup ε (conjSubgroup h B))) :=
        hcF'.conj_of_mem hqM
      have hne : conjSubgroup m B ⊓ conjSubgroup q (conjSubgroup ε (conjSubgroup h B)) ≠ ⊥ := by
        intro h0
        have : p ∈ conjSubgroup m B ⊓ conjSubgroup q (conjSubgroup ε (conjSubgroup h B)) :=
          ⟨hpP, hpq⟩
        rw [h0, Subgroup.mem_bot] at this
        exact hp1 this
      obtain ⟨gP, hgP⟩ := hcP.conj
      obtain ⟨gq, hgq⟩ := hcq.conj
      have hPq : conjSubgroup m B = conjSubgroup q (conjSubgroup ε (conjSubgroup h B)) :=
        eq_of_inf_ne_bot_conj hc.hyp.ti ⟨gP, hgP⟩ ⟨gq, hgq⟩ hne
      right
      refine ⟨ε, Subgroup.mem_sup_right hε, ?_⟩
      rw [hPq, hcF'.LB_conj hqM, hLQ hq, hcF.LB_conj hεM]

end HS9

theorem sec97FourLine_of : Sec97FourLineStatement := by
  intro G _ _ M Q Z B hc n t _ h hh hFB
  exact HS9.lineGeom_of_QB hc hh hFB

theorem sec97Four_of_core (h34 : Stroth34Statement) (h311a : Stroth311aStatement)
    (hCore : Sec97FourCoreStatement) : Sec97FourStatement :=
  sec97Four_of_line_core h34 h311a sec97FourLine_of hCore

end CFSG.RankThree.GF2n.Stroth80
