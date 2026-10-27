module

public import CFSG.RankThree.GF2n.Stroth80.Sec312bAux
public import CFSG.RankThree.GF2n.Stroth80.Sec311Lines
public import CFSG.RankThree.GF2n.Stroth80.Sec312bOpp
public import CFSG.RankThree.GF2n.Stroth80.Sec312bOrth
public import CFSG.RankThree.GF2n.Stroth80.Sec312Stmt
public import CFSG.RankThree.GF2n.Stroth80.Sec310ClData
public import CFSG.RankThree.GF2n.Stroth80.Sec310Main
public import CFSG.RankThree.GF2n.Stroth80.Sec310Nt
public import CFSG.RankThree.GF2n.Stroth80.Sec310SLDirect

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank CFSG.RankThree.GF2n
open CFSG.RankThree.GF2n.Stroth80.Classify
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem stroth312b_of_311a (h34 : Stroth34Statement) (hX : Classify.TheoremXStatement)
    (ha : Stroth311aStatement) : Stroth312bStatement := by
  classical
  intro G _ _ M Q Z B hc n hw hn hno hgen t ht htQ L₁ L₂ ⟨m₁, hm₁, hL₁⟩ ⟨m₂, hm₂, hL₂⟩ ht₁ ht₂
    hne12 hnotSL
  subst hL₁ hL₂
  have hs : Sec5Hyp hc n t := ⟨hw, hn, hno, hgen, ht, htQ⟩
  have hL₁R : conjSubgroup m₁ (LB M Q B) ≤ Rt M (LB M Q B) t := conjSubgroup_le_Rt hm₁ ht₁
  have hL₂R : conjSubgroup m₂ (LB M Q B) ≤ Rt M (LB M Q B) t := conjSubgroup_le_Rt hm₂ ht₂
  have hR : Rt M (LB M Q B) t ≠ LB M Q B := by
    intro hRL
    apply hne12
    have c₁ : Nat.card (conjSubgroup m₁ (LB M Q B)) = Nat.card (LB M Q B) :=
      card_conjSubgroup m₁ _
    have c₂ : Nat.card (conjSubgroup m₂ (LB M Q B)) = Nat.card (LB M Q B) :=
      card_conjSubgroup m₂ _
    have e₁ : conjSubgroup m₁ (LB M Q B) = LB M Q B :=
      Subgroup.eq_of_le_of_card_ge (hL₁R.trans hRL.le) c₁.ge
    have e₂ : conjSubgroup m₂ (LB M Q B) = LB M Q B :=
      Subgroup.eq_of_le_of_card_ge (hL₂R.trans hRL.le) c₂.ge
    exact e₁.trans e₂.symm
  have hnot : ¬ Vt M (LB M Q B) B Z t ≤ QB B := fun hV =>
    hnotSL (stroth310SLBranch_of_transv (stroth310SLTransv_of_34 h34) G M Q Z B hc n t hs hR hV)
  have hN2 : IsPGroup 2 ↥(hc.CN t) :=
    hc.isPGroup_CN_of_311 h34 hs (ha G M Q Z B hc n hw hn hno hgen t ht htQ hR)
  obtain ⟨n', γ, M₀, -, h⟩ := stroth_globalModelDataGF hc.hyp
  have hS : ∀ (c : GaloisField 2 n') (e : M₀.E), e ∈ M₀.img (Vt M (LB M Q B) B Z t) →
      c • e ∈ M₀.img (Vt M (LB M Q B) B Z t) :=
    fun c _ he => hc.smul_mem_img_Vt h t c he
  obtain ⟨D⟩ := hc.exists_reprData h34 hs hnot h hS
  have hSymp := sympRep_two_of_not_le_QB h34 hc hs hnot
    (stroth310SympForm_of_34 h34 G M Q Z B hc n t hs hR hnot)
  have hKZ : Nat.card (GaloisField 2 n') = Nat.card Z := h.card
  have hq4 : 4 ≤ Nat.card (GaloisField 2 n') := by
    rw [hKZ]
    exact hc.hyp.q4
  have hdim : 4 ≤ Module.finrank (GaloisField 2 n')
      ↥(imgSub M₀ (Vt M (LB M Q B) B Z t) hS) := by
    obtain ⟨K₁, _, _, hK₁, m₁', hm₁', φ₁, -, -, hsec⟩ := hSymp
    have hcardV := card_eq_of_sectionAct
      (sec39_Z_le_Vt (M := M) (L := LB M Q B) (B := B) (t := t)) hsec
    have hcardM := M₀.card_eq (hc.Vt_le_Q t)
      (sec39_Z_le_Vt (M := M) (L := LB M Q B) (B := B) (t := t))
    have hfin : Nat.card (M₀.img (Vt M (LB M Q B) B Z t)) =
        Nat.card ↥(imgSub M₀ (Vt M (LB M Q B) B Z t) hS) :=
      Nat.card_congr (Equiv.subtypeEquivRight fun v => mem_imgSub.symm)
    have hpow : Nat.card ↥(imgSub M₀ (Vt M (LB M Q B) B Z t) hS) =
        Nat.card (GaloisField 2 n') ^ Module.finrank (GaloisField 2 n')
          ↥(imgSub M₀ (Vt M (LB M Q B) B Z t) hS) :=
      Module.natCard_eq_pow_finrank (K := GaloisField 2 n')
        (V := ↥(imgSub M₀ (Vt M (LB M Q B) B Z t) hS))
    rw [hcardV, hfin] at hcardM
    have h2 := Nat.eq_of_mul_eq_mul_left Nat.card_pos hcardM
    simp only [Fintype.card_sum, Fintype.card_fin] at h2
    rw [hK₁, hpow, hKZ] at h2
    have h3 : 2 ≤ Nat.card Z := by
      have := hc.hyp.q4
      omega
    have h4 := Nat.pow_right_injective h3 h2
    omega
  obtain ⟨P, hP0, hPspan, hPful, hPgen⟩ := hc.theoremX_data h34 hs h D hdim
  have hH : D.ρ.range ≤ Classify.sympSubgroup D.F := by
    rintro _ ⟨r, rfl⟩
    exact D.isom r
  have hcases := hX (GaloisField 2 n') ↥(imgSub M₀ (Vt M (LB M Q B) B Z t) hS) D.F hq4 D.nondeg
    D.alt hdim D.ρ.range hH P hP0 hPspan hPful hPgen
  obtain ⟨e₁, he₁0, heB₁, hepr₁, heful₁⟩ := D.elation_data h34 hs h hdim hm₁ ht₁
  obtain ⟨e₂, he₂0, heB₂, hepr₂, heful₂⟩ := D.elation_data h34 hs h hdim hm₂ ht₂
  have hne : ∀ c : GaloisField 2 n', e₂ ≠ c • e₁ := by
    intro c hc2
    apply hne12
    have hc0 : c ≠ 0 := by
      rintro rfl
      exact he₂0 (by rw [hc2, zero_smul])
    refine hc.conj_LB_eq_of_img_eq (M₀ := M₀) hm₁ hm₂ fun v => ?_
    rw [heB₁, heB₂]
    have hv : ((e₂ : ↥(imgSub M₀ (Vt M (LB M Q B) B Z t) hS)) : M₀.E) =
        c • (e₁ : M₀.E) := by rw [hc2]; rfl
    constructor
    · rintro ⟨s, rfl⟩
      exact ⟨s * c⁻¹, by rw [hv, smul_smul, mul_assoc, inv_mul_cancel₀ hc0, mul_one]⟩
    · rintro ⟨s, rfl⟩
      exact ⟨s * c, by rw [hv, smul_smul]⟩
  have hind : LinearIndependent (GaloisField 2 n') ![e₁, e₂] := by
    rw [LinearIndependent.pair_iff]
    intro s t' hst
    by_cases ht' : t' = 0
    · subst ht'
      rw [zero_smul, add_zero] at hst
      rcases smul_eq_zero.mp hst with h0 | h0
      · exact ⟨h0, rfl⟩
      · exact absurd h0 he₁0
    · exfalso
      refine hne (-(s / t')) ?_
      have h1 : t' • e₂ = -(s • e₁) := eq_neg_of_add_eq_zero_right hst
      have h2 : e₂ = t'⁻¹ • (-(s • e₁)) := by
        rw [← h1, smul_smul, inv_mul_cancel₀ ht', one_smul]
      rw [h2, smul_neg, smul_smul, ← neg_smul]
      congr 1
      field_simp
  by_cases hF : D.F e₁ e₂ = 0
  ·
    left
    have hL12 : conjSubgroup m₁ (LB M Q B) ⊔ conjSubgroup m₂ (LB M Q B) ≤
        Rt M (LB M Q B) t := sup_le hL₁R hL₂R
    have hq4' : 4 ≤ Nat.card (GaloisField 2 n') := hq4
    have hQS := orth_quotSat (conjSubgroup m₁ (LB M Q B)) (conjSubgroup m₂ (LB M Q B)) hq4'
      D.F D.alt e₁ e₂ hind hF (D.ρ.comp (Subgroup.inclusion hL12))
      (fun l hl => hepr₁ (Subgroup.mem_map.mpr
        ⟨⟨l, hL₁R hl⟩, Subgroup.mem_subgroupOf.mpr hl, rfl⟩))
      (fun l hl => hepr₂ (Subgroup.mem_map.mpr
        ⟨⟨l, hL₂R hl⟩, Subgroup.mem_subgroupOf.mpr hl, rfl⟩))
      (fun φ hφ => by
        obtain ⟨g, hg, hgφ⟩ := heful₁ φ hφ
        obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hg
        have hy' : (y : G) ∈ conjSubgroup m₁ (LB M Q B) := Subgroup.mem_subgroupOf.mp hy
        exact ⟨D.ρ y, ⟨(y : G), hy', rfl⟩, hgφ⟩)
      (fun φ hφ => by
        obtain ⟨g, hg, hgφ⟩ := heful₂ φ hφ
        obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hg
        have hy' : (y : G) ∈ conjSubgroup m₂ (LB M Q B) := Subgroup.mem_subgroupOf.mp hy
        exact ⟨D.ρ y, ⟨(y : G), hy', rfl⟩, hgφ⟩)
      (fun s hs1 => by
        have hmem : (⟨(s : G), hL12 s.2⟩ : ↥(Rt M (LB M Q B) t)) ∈ D.ρ.ker := hs1
        rw [D.ker, Subgroup.mem_subgroupOf] at hmem
        obtain ⟨j, hj⟩ := hN2 ⟨(s : G), hmem⟩
        exact ⟨j, by simpa using congrArg (fun z : ↥(hc.CN t) => (z : G)) hj⟩)
    rwa [hKZ] at hQS
  ·
    right
    have hSinv : D.ρ.range = Classify.sympSubgroup D.F →
        ∀ x : ↥(imgSub M₀ (Vt M (LB M Q B) B Z t) hS), D.F x e₁ = 0 →
        ∀ g ∈ ((conjSubgroup m₁ (LB M Q B)).subgroupOf (Rt M (LB M Q B) t)).map D.ρ,
          Classify.symTransvection D.alt x 1 * g * (Classify.symTransvection D.alt x 1)⁻¹ ∈
            ((conjSubgroup m₁ (LB M Q B)).subgroupOf (Rt M (LB M Q B) t)).map D.ρ := by
      intro hsp x hx g hg
      have htx : Classify.symTransvection D.alt x 1 ∈ D.ρ.range := by
        rw [hsp]
        exact Classify.symTransvection_mem D.alt x 1
      obtain ⟨r, hr⟩ := htx
      have hre : D.ρ r e₁ = (1 : GaloisField 2 n') • e₁ := by
        rw [hr, one_smul, Classify.symTransvection_apply, one_mul]
        have : D.F e₁ x = 0 := by rw [Classify.form_comm D.alt]; exact hx
        rw [this, zero_smul, add_zero]
      have hrn := hc.mem_normalizer_conj_LB_of_fix hs h D hm₁ ht₁ e₁ heB₁ r 1 hre
      obtain ⟨y, hy, rfl⟩ := hg
      refine ⟨r * y * r⁻¹, ?_, ?_⟩
      · have hy' : y ∈ (conjSubgroup m₁ (LB M Q B)).subgroupOf (Rt M (LB M Q B) t) := hy
        show r * y * r⁻¹ ∈ (conjSubgroup m₁ (LB M Q B)).subgroupOf (Rt M (LB M Q B) t)
        rw [Subgroup.mem_subgroupOf] at hy' ⊢
        have := (Subgroup.mem_normalizer_iff.mp hrn (y : G)).mp hy'
        simpa using this
      · rw [map_mul, map_mul, map_inv, hr]
    have hsup := opp_glue hX (Rt M (LB M Q B) t) (hc.CN t) (conjSubgroup m₁ (LB M Q B))
      (conjSubgroup m₂ (LB M Q B)) hL₁R hL₂R D.F D.nondeg D.alt hq4 hdim D.ρ D.ker hH e₁ e₂ hF
      hepr₁ hepr₂ heful₁ heful₂ hcases hSinv
    have hle := hc.Rt_le_of_mul_CN h34 ha hs hR hm₁ ht₁ le_sup_left hsup
    exact (le_antisymm (sup_le hL₁R hL₂R) hle)

end CFSG.RankThree.GF2n.Stroth80
