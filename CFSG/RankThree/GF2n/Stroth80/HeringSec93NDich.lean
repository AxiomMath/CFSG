module

public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.RankThree.GF2n.Stroth80.Sec310ClCaseQuad
public import CFSG.RankThree.GF2n.Stroth80.Sec310ClData
public import CFSG.RankThree.GF2n.Stroth80.Sec310Main
public import CFSG.RankThree.GF2n.Stroth80.Sec310SLDirect
public import CFSG.RankThree.GF2n.Stroth80.Sec312bAux
public import CFSG.RankThree.GF2n.Stroth80.Sec312bOpp
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank CFSG.RankThree.GF2n
open CFSG.RankThree.GF2n.Stroth80.Classify
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

namespace HS9

theorem conj_le_QB_or_eq_Rt (h34 : Stroth34Statement) (hX : Classify.TheoremXStatement)
    (ha : Stroth311aStatement) {hc : Ctx M Q Z B} {n : ℕ} {t : G} (hs : Sec5Hyp hc n t)
    (hnotSL : ¬ SLNat hc t) {m₁ m₂ : G} (hm₁ : m₁ ∈ M) (hm₂ : m₂ ∈ M)
    (ht₁ : t ∈ conjSubgroup m₁ (LB M Q B)) (ht₂ : t ∈ conjSubgroup m₂ (LB M Q B))
    (hne12 : conjSubgroup m₁ (LB M Q B) ≠ conjSubgroup m₂ (LB M Q B)) :
    conjSubgroup m₂ B ≤ QB (conjSubgroup m₁ B) ∨
      (conjSubgroup m₁ (LB M Q B) ⊔ conjSubgroup m₂ (LB M Q B) = Rt M (LB M Q B) t ∧
        Nat.card Z ^ 2 ≤ (hc.CN t).relIndex (conjSubgroup m₁ (LB M Q B))) := by
  classical
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
  obtain ⟨e₂, -, heB₂, hepr₂, heful₂⟩ := D.elation_data h34 hs h hdim hm₂ ht₂
  by_cases hF : D.F e₁ e₂ = 0
  ·
    left
    have hnotC := D.not_Vt_le_QB_conj h34 hs h hdim hm₁ ht₁
    intro v hv
    have hvV : v ∈ Vt M (LB M Q B) B Z t := sec39_conjB_le_Vt hm₂ ht₂ hv
    have hvQ : v ∈ Q := hc.Vt_le_Q t hvV
    obtain ⟨s, hs'⟩ := (heB₂ _).mp (M₀.pi_mem_img hv hvQ)
    refine (D.mem_QB_iff h34 hs h hm₁ ht₁ hnotC heB₁ e₁.2 hvV).mpr ?_
    have hw : (⟨M₀.π v, mem_imgSub.mpr (M₀.pi_mem_img hvV hvQ)⟩ :
        ↥(imgSub M₀ (Vt M (LB M Q B) B Z t) hS)) = s • e₂ := Subtype.ext hs'
    have hF' : D.F ⟨(e₁ : M₀.E), e₁.2⟩ e₂ = 0 := hF
    rw [hw, map_smul, hF', smul_zero]
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
    refine ⟨le_antisymm (sup_le hL₁R hL₂R) hle, ?_⟩
    obtain ⟨f₀, hf₀⟩ : ∃ f₀, D.F e₁ f₀ ≠ 0 := by
      by_contra hcon
      exact he₁0 (D.nondeg.1 e₁ fun y => by_contra fun hy => hcon ⟨y, hy⟩)
    obtain ⟨f, hef⟩ : ∃ f, D.F e₁ f = 1 :=
      ⟨(D.F e₁ f₀)⁻¹ • f₀, by rw [map_smul, smul_eq_mul]; exact inv_mul_cancel₀ hf₀⟩
    have hcount := Classify.card_le_of_elationFull D.nondeg D.alt (by omega) hef hepr₁ heful₁
    have hrel : Nat.card (((conjSubgroup m₁ (LB M Q B)).subgroupOf (Rt M (LB M Q B) t)).map D.ρ) =
        (hc.CN t).relIndex (conjSubgroup m₁ (LB M Q B)) := by
      rw [← Subgroup.relIndex_ker, D.ker, Subgroup.relIndex_subgroupOf hL₁R]
    rw [← hrel, ← hKZ]
    exact hcount

end HS9

end CFSG.RankThree.GF2n.Stroth80
