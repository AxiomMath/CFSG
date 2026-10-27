module

public import CFSG.LocalAnalysis.UniquenessCase.UC22K148NonSplitC
import CFSG.LocalAnalysis.UniquenessCase.UC22K148Asm
import CFSG.LocalAnalysis.UniquenessCase.UC22K148CaseA3
import CFSG.LocalAnalysis.UniquenessCase.UC22K148CaseA4
import CFSG.LocalAnalysis.UniquenessCase.UC22K148CompDich
import CFSG.LocalAnalysis.UniquenessCase.UC22K148IdL2b
import CFSG.LocalAnalysis.UniquenessCase.UC22K148NoExc
import CFSG.LocalAnalysis.UniquenessCase.UC22K148S5Br
import CFSG.LocalAnalysis.UniquenessCase.UC22K148S5Split
import CFSG.LocalAnalysis.UniquenessCase.UC22K148Split
import CFSG.LocalAnalysis.UniquenessCase.UC22K148SplitFac
import CFSG.Quasithin.Background.G119Group2

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.K148

open CFSG.RankThree.FFModules CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF
open CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22.Ext

variable {G : Type} [Group G] {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
variable {ρ : Representation (ZMod 2) G V}

theorem exists_mem_calP_fitting_commutator_ne_bot [Finite G] (hO : CFSG.pCore 2 G = ⊥)
    (hH : hP ρ = ⊤) (hG : (⊤ : Subgroup G) ≠ ⊥) (hnc : ∀ L : Subgroup G, ¬ IsComponentOf L ⊤) :
    ∃ A ∈ calP ρ, ⁅CFSG.fittingSubgroup G, A⁆ ≠ ⊥ := by
  by_contra hne
  have hle : hP ρ ≤ Subgroup.centralizer (CFSG.fittingSubgroup G : Set G) :=
    iSup₂_le fun A hA => by
      have h : ⁅CFSG.fittingSubgroup G, A⁆ = ⊥ := Classical.byContradiction fun h => hne ⟨A, hA, h⟩
      rwa [Subgroup.commutator_comm, Subgroup.commutator_eq_bot_iff_le_centralizer] at h
  have hF := CFSG.centralizer_generalizedFitting_le G
  rw [CFSG.generalizedFitting.eq_sup, CFSG.LocalCores.layer_eq_bot_of_forall fun K hK =>
    hnc K ((CFSG.isComponent_iff_open K).1 hK), sup_bot_eq] at hF
  refine hG (eq_bot_iff.2 ?_)
  rw [← hH]
  refine iSup₂_le fun A hA => ?_
  have h := CFSG.ABGLocalTools.le_pCore_of_isPGroup_of_le_fitting hA.2.1.isPGroup
    ((le_hP_of_mem_calP hA).trans (hle.trans hF))
  rwa [hO] at h

theorem hasFactors148_of_isComponentOf
    [Finite G] [Finite V]
    (hO : CFSG.pCore 2 G = ⊥) (hρ : Function.Injective ρ)
    (hshape : ∀ L : Subgroup G, IsComponentOf L ⊤ →
      (∃ n : ℕ, 2 ≤ n ∧ IsL2 ↥L n) ∨ (IsL2Odd ↥L 7 ∧ Nonempty (↥L ≃* GL (Fin 3) (ZMod 2))))
    (hH : hP ρ = ⊤) (IH : HasFactors148Below (Nat.card G))
    (hinner : ∀ L : Subgroup G, IsComponentOf L ⊤ →
      ¬ ∀ g : G, ∃ l ∈ L, ∀ u ∈ commOn ρ L ⊤, ρ g u = ρ l u)
    {L : Subgroup G} (hL : IsComponentOf L ⊤) : HasFactors148 G := by
  rcases component_dichotomy hρ hH hL (hshape L hL) with h | ⟨hZ, a, ha2, haN, haL, hS5⟩
  · exact (hinner L hL h.1).elim
  have hLn : L.Normal := by
    rw [← Subgroup.normalizer_eq_top_iff, eq_top_iff, ← hH]
    exact hP_le_normalizer hρ hL
  have hN : ∀ g : G, g ∈ Subgroup.normalizer (L : Set G) := fun g => by
    rw [Subgroup.normalizer_eq_top_iff.2 hLn]
    exact Subgroup.mem_top g
  have hL1 : L ≠ ⊥ := by
    haveI := hL.2.2.2
    haveI : Nontrivial ↥L := (QuotientGroup.mk'_surjective (Subgroup.center ↥L)).nontrivial
    exact (Subgroup.nontrivial_iff_ne_bot L).1 inferInstance
  have hact : ∀ g : G, ∃ h ∈ L ⊔ Subgroup.zpowers a, ∀ u ∈ commOn ρ L ⊤, ρ g u = ρ h u :=
    fun g => exists_eq_apply_of_secNatS5 ha2 haN haL hS5 (hN g)
  refine hasFactors148_of_forall_isFactor148 hO hρ hshape hH IH hinner hLn hL1
    (isCompl_commOn_fixSub_of_secNatS5 ha2 haN haL hS5 hZ) ha2
    (fun n hn h => eq_one_of_secNatS5 hS5 (Subgroup.mem_sup_left hn) h) hact
    (fun n hn => not_apply_eq_of_secNatS5 haL hS5 hn)
    (fun X hX => noExcess_of_secNatS5 hS5 hX fun x _ => hact x) fun r hr2 _ hrLK hMK => ?_
  obtain ⟨-, -, -, φ, -⟩ := secNatS5_sup_zpowers_of_inf_eq_bot hLn ha2 haL hS5 hact hr2
    (fun h => hrLK (Subgroup.mem_sup_left h)) hMK
  exact Or.inr (Or.inr ⟨φ⟩)

theorem hasFactors148_of_card_three
    [Finite G] [Finite V]
    (hO : CFSG.pCore 2 G = ⊥) (hρ : Function.Injective ρ)
    (hshape : ∀ L : Subgroup G, IsComponentOf L ⊤ →
      (∃ n : ℕ, 2 ≤ n ∧ IsL2 ↥L n) ∨ (IsL2Odd ↥L 7 ∧ Nonempty (↥L ≃* GL (Fin 3) (ZMod 2))))
    (hH : hP ρ = ⊤) (IH : HasFactors148Below (Nat.card G))
    (hinner : ∀ L : Subgroup G, IsComponentOf L ⊤ →
      ¬ ∀ g : G, ∃ l ∈ L, ∀ u ∈ commOn ρ L ⊤, ρ g u = ρ l u)
    {Q : Subgroup G} {b : G} (hQn : Q.Normal) (hQ3 : Nat.card ↥Q = 3)
    (hQV : Module.finrank (ZMod 2) ↥(commOn ρ Q ⊤) = 2) (hb2 : b * b = 1)
    (hb : ∀ q ∈ Q, b * q * b⁻¹ = q⁻¹) : HasFactors148 G := by
  have hNN : (⊤ : Subgroup G) ≤ Subgroup.normalizer (Q : Set G) := by
    rw [Subgroup.normalizer_eq_top_iff.2 hQn]
  have hQ1 : Q ≠ ⊥ := fun h => by
    rw [h, Subgroup.card_bot] at hQ3
    exact absurd hQ3 (by norm_num)
  have hcen := cenOn_commOn_eq_bot_of_odd (ρ := ρ) hρ (X := Q) fun x hx =>
    Odd.of_dvd_nat (by rw [hQ3]; decide) (Subgroup.orderOf_dvd_natCard Q hx)
  have hfa : ∀ n ∈ Q, (∀ x ∈ commOn ρ Q ⊤, ρ n x = x) → n = 1 := fun n hn h => by
    have h1 : n ∈ cenOn ρ Q (commOn ρ Q ⊤) := ⟨hn, h⟩
    rw [hcen] at h1
    exact (Subgroup.mem_bot).1 h1
  have hK : (cenOn ρ ⊤ (commOn ρ Q ⊤)).Normal := cenOn_commOn_normal hQn
  refine hasFactors148_of_forall_isFactor148 hO hρ hshape hH IH hinner hQn hQ1
    (isCompl_commOn_fixSub_of_odd (by rw [hQ3]; decide)) hb2 hfa
    (fun g => exists_eq_apply_of_card_three hρ hQ3 hQV hb (hNN (Subgroup.mem_top b))
      (hNN (Subgroup.mem_top g)))
    (fun n hn => not_forall_apply_eq_of_inverts hρ hQ3 hb hn)
    (fun X hX => noExcess_of_finrank_two hQV hX fun g _ u hu =>
      (invariant_commOn_top hNN).2 g (Subgroup.mem_top g) u hu)
    fun r hr2 hrK hrQK _ => Or.inr (Or.inl ?_)
  have hrb : r * b ∈ cenOn ρ ⊤ (commOn ρ Q ⊤) := by
    rcases CFSG.Quasithin.G11.g119_mem_or_mul_mem_of_sup_zpowers hb2
      (fun k hk => hK.conj_mem k hk b) hrK with h | h
    · exact (hrQK (Subgroup.mem_sup_right h)).elim
    · exact h
  exact nonempty_sup_zpowers_mulEquiv_perm_three hQ3 hb hb2
    (fun x hx k hk => Subgroup.commute_of_normal_of_disjoint Q _ hQn hK
      (disjoint_iff.2 (inf_cenOn_commOn_eq_bot hfa)) x k hx hk) hr2
    (fun h => hrQK (by rw [h]; exact Subgroup.one_mem _)) hrb

theorem hasFactors148_of_below
    [Finite G] [Finite V] (hO : CFSG.pCore 2 G = ⊥)
    (hρ : Function.Injective ρ)
    (hshape : ∀ L : Subgroup G, IsComponentOf L ⊤ →
      (∃ n : ℕ, 2 ≤ n ∧ IsL2 ↥L n) ∨ (IsL2Odd ↥L 7 ∧ Nonempty (↥L ≃* GL (Fin 3) (ZMod 2))))
    (hH : hP ρ = ⊤) (IH : HasFactors148Below (Nat.card G)) : HasFactors148 G := by
  by_cases hG : (⊤ : Subgroup G) = ⊥
  · exact ⟨0, Fin.elim0, ⟨by rw [iSup_of_empty, hG], fun i => i.elim0, fun i => i.elim0⟩,
      fun i => i.elim0⟩
  by_cases hin : ∃ L : Subgroup G, IsComponentOf L ⊤ ∧
      ∀ g : G, ∃ l ∈ L, ∀ u ∈ commOn ρ L ⊤, ρ g u = ρ l u
  · obtain ⟨L, hL, hLin⟩ := hin
    exact hasFactors148_of_inner hO hρ hshape hH IH hL hLin
  have hinner : ∀ L : Subgroup G, IsComponentOf L ⊤ →
      ¬ ∀ g : G, ∃ l ∈ L, ∀ u ∈ commOn ρ L ⊤, ρ g u = ρ l u := fun L hL h => hin ⟨L, hL, h⟩
  by_cases hc : ∃ L : Subgroup G, IsComponentOf L ⊤
  · obtain ⟨L, hL⟩ := hc
    exact hasFactors148_of_isComponentOf hO hρ hshape hH IH hinner hL
  obtain ⟨A, hA, hFA⟩ :=
    exists_mem_calP_fitting_commutator_ne_bot hO hH hG fun L hL => hc ⟨L, hL⟩
  obtain ⟨Q, b, hbA, hQn, hQ3, hQV, hb⟩ := exists_normal_Q hρ hO hH hA hFA
  have hb2 : b * b = 1 := by
    rw [← pow_two]
    exact hA.2.1.2 b hbA
  exact hasFactors148_of_card_three hO hρ hshape hH IH hinner hQn hQ3 hQV hb2 hb

theorem hasFactors148Below_all
    (n : ℕ) : HasFactors148Below n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro G' _ _ V' _ _ _ ρ' hn hO hρ hshape hH
    exact hasFactors148_of_below hO hρ hshape hH (ih _ hn)

theorem hasFactors148_of_hP_eq_top
    [Finite G] [Finite V] (hO : CFSG.pCore 2 G = ⊥)
    (hρ : Function.Injective ρ)
    (hshape : ∀ L : Subgroup G, IsComponentOf L ⊤ →
      (∃ n : ℕ, 2 ≤ n ∧ IsL2 ↥L n) ∨ (IsL2Odd ↥L 7 ∧ Nonempty (↥L ≃* GL (Fin 3) (ZMod 2))))
    (hH : hP ρ = ⊤) : HasFactors148 G :=
  hasFactors148_of_below hO hρ hshape hH (hasFactors148Below_all _)

theorem k148Top_holds :
    K148Top := by
  intro G _ _ V _ _ _ ρ _ hO hρ hshape hH _
  exact k148Concl_of_hasFactors148 hρ hshape hH (hasFactors148_of_hP_eq_top hO hρ hshape hH)

end CFSG.LocalAnalysis.UniquenessCase.UC22.K148

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.Ext

theorem k148_holds :
    K148 :=
  K148.k148_of_top K148.k148Top_holds

end CFSG.LocalAnalysis.UniquenessCase.UC22.Ext
