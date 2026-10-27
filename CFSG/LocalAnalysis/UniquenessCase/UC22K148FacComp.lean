module

public import CFSG.LocalAnalysis.UniquenessCase.UCFrontExt
public import CFSG.LocalAnalysis.UniquenessCase.UC22K148Strip
import CFSG.LocalAnalysis.UniquenessCase.UC22K148FacS3
import CFSG.LocalAnalysis.UniquenessCase.UC22K148CompDich
import CFSG.LocalAnalysis.UniquenessCase.UC22K148S5Br
import CFSG.LocalAnalysis.UniquenessCase.UC22K148S5Split
import CFSG.LocalAnalysis.UniquenessCase.UC22K148NoExc
import CFSG.LocalAnalysis.UniquenessCase.UC22K148IdL2b
import CFSG.LocalAnalysis.UniquenessCase.UC22K148Sec
import CFSG.Adapters.StatedPSLTwo

public section

set_option linter.unusedSectionVars false

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.K148

open CFSG.Open CFSG.RankThree.FFModules CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF
open CFSG.LocalAnalysis.UniquenessCase.UC22.Ext

variable {G : Type} [Group G] {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
variable {ρ : Representation (ZMod 2) G V}

theorem commute_of_forall_apply_eq {L : Subgroup G} [IsSimpleGroup ↥L]
    (hnt : ¬ commOn ρ L ⊤ ≤ fixSub ρ L) {b : G} (hbN : b ∈ Subgroup.normalizer (L : Set G))
    (hb : ∀ n ∈ commOn ρ L ⊤, ρ b n = n) : ∀ l ∈ L, l * b = b * l := by
  have hY : CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant ρ L (commOn ρ L ⊤) :=
    (invariant_commOn_top (A := L) Subgroup.le_normalizer).1
  have hZ : ∀ K : Subgroup G, CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant ρ K (⊥ : Submodule (ZMod 2) V) := fun _ _ _ v hv => by
    rw [(Submodule.mem_bot _).1 hv, map_zero]
    exact zero_mem _
  obtain ⟨y, hy, hyf⟩ := SetLike.not_le_iff_exists.1 hnt
  obtain ⟨l, hl, hly⟩ : ∃ l ∈ L, ρ l y ≠ y := by
    by_contra h
    exact hyf (mem_fixSub.2 fun l hl => Classical.byContradiction fun hne => h ⟨l, hl, hne⟩)
  refine commute_of_mem_secKer hY (hZ L) ⟨l, hl, y, hy, fun h0 => hly ?_⟩ hbN
    (mem_secKer_of (hZ ⊤) (Subgroup.mem_top b) fun n hn => ?_)
  · exact sub_eq_zero.1 ((Submodule.mem_bot _).1 h0)
  · rw [hb n hn, sub_self]
    exact zero_mem _


theorem factorData_of_isComponentOf [Finite G] [Finite V] (hρ : Function.Injective ρ)
    (hH : hP ρ = ⊤) {L : Subgroup G} (hL : IsComponentOf L ⊤)
    (hshape : (∃ n : ℕ, 2 ≤ n ∧ IsL2 ↥L n) ∨
      (IsL2Odd ↥L 7 ∧ Nonempty (↥L ≃* GL (Fin 3) (ZMod 2))))
    (hLC : L ⊔ Subgroup.centralizer (L : Set G) = ⊤) :
    (∀ c : G, (∀ x ∈ L, c * x = x * c) → ∀ n ∈ commOn ρ L ⊤, ρ c n = n) ∧
      commOn ρ L (commOn ρ L ⊤) = commOn ρ L ⊤ ∧ Shape148 ρ L (commOn ρ L ⊤) (fixSub ρ L) := by
  haveI : IsSimpleGroup ↥L := by
    rcases hshape with ⟨n, -, hX⟩ | ⟨hX, -⟩
    · exact CFSG.Blueprint.LieModel.isSimpleGroup_psl_two hX
    · exact CFSG.Blueprint.LieModel.isSimpleGroup_psl_two hX
  obtain ⟨A, hA, hLA⟩ := exists_mem_calP_commutator_ne_bot hH hL
  obtain ⟨hperf, hnt⟩ := commOn_facts_of_mem_calP hρ hL hA hLA
  haveI hLN : L.Normal := by
    rw [← Subgroup.normalizer_eq_top_iff, eq_top_iff, ← hLC]
    exact sup_le Subgroup.le_normalizer (Subgroup.centralizer_le_normalizer _)
  have hZ : Subgroup.center ↥L = ⊥ := by
    refine (IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center ↥L)).resolve_right
      fun hc => ?_
    obtain ⟨a, b, hab⟩ := hL.2.2.2.exists_pair_ne
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective b
    exact hab (QuotientGroup.eq.2 (by rw [hc]; exact Subgroup.mem_top _))
  have hfaith : ∀ l ∈ L, (∀ n ∈ commOn ρ L ⊤, ρ l n = n) → l = 1 := fun l hl hln => by
    have h1 : (⟨l, hl⟩ : ↥L) ∈ Subgroup.center ↥L := Subgroup.mem_center_iff.2 fun z =>
      Subtype.ext (commute_of_forall_apply_eq hnt (Subgroup.le_normalizer hl) hln z z.2)
    rw [hZ, Subgroup.mem_bot] at h1
    exact congrArg Subtype.val h1
  have hNL : CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant ρ L (commOn ρ L ⊤) :=
    (invariant_commOn_top (A := L) Subgroup.le_normalizer).1
  rcases component_dichotomy hρ hH hL hshape with ⟨hin, hsh⟩ | ⟨-, a, ha2, haN, haL, hS5⟩
  · refine ⟨fun c hc => ?_, hperf, hsh⟩
    obtain ⟨l, hl, hcl⟩ := hin c
    exact apply_eq_self_of_commute_of_faithful hNL hfaith hZ hc hl hcl
  · exfalso
    have ha : a ∈ ((L ⊔ Subgroup.centralizer (L : Set G) : Subgroup G) : Set G) := by
      rw [hLC]
      exact Subgroup.mem_top a
    rw [Subgroup.normal_mul] at ha
    obtain ⟨x, hx, c, hc, rfl⟩ := Set.mem_mul.1 ha
    have hc' : ∀ l ∈ L, c * l = l * c := fun l hl =>
      (Subgroup.mem_centralizer_iff.1 (SetLike.mem_coe.1 hc) l hl).symm
    have hc1 := apply_eq_self_of_commute_of_secNatS5 ha2 haN haL hS5 hc'
    exact not_apply_eq_of_secNatS5 haL hS5 (SetLike.mem_coe.1 hx) fun u hu => by
      rw [glRep_mul_apply, hc1 u hu]

theorem factorData_of_mulEquiv_perm_five [Finite G] [Finite V] (hρ : Function.Injective ρ)
    (hshape : ∀ L : Subgroup G, IsComponentOf L ⊤ →
      (∃ n : ℕ, 2 ≤ n ∧ IsL2 ↥L n) ∨ (IsL2Odd ↥L 7 ∧ Nonempty (↥L ≃* GL (Fin 3) (ZMod 2))))
    (hH : hP ρ = ⊤) {H : Subgroup G} (hHN : H.Normal) (e : ↥H ≃* Equiv.Perm (Fin 5)) :
    (∀ c : G, (∀ x ∈ H, c * x = x * c) → ∀ n ∈ commOn ρ ⁅H, H⁆ ⊤, ρ c n = n) ∧
      (∀ h ∈ H, (∀ n ∈ commOn ρ ⁅H, H⁆ ⊤, ρ h n = n) → h = 1) ∧
      IsCompl (commOn ρ ⁅H, H⁆ ⊤) (fixSub ρ ⁅H, H⁆) ∧
      (∀ X : Subgroup G, IsElemAbelian 2 X → NoExcess ρ X (commOn ρ ⁅H, H⁆ ⊤)) ∧
      Shape148 ρ H (commOn ρ ⁅H, H⁆ ⊤) (fixSub ρ H) := by
  have h5 : 5 ≤ Nat.card (Fin 5) := by simp
  have hAeq : ⁅H, H⁆ = (alternatingGroup (Fin 5)).map (H.subtype.comp e.symm.toMonoidHom) := by
    rw [commutator_eq_map_of_mulEquiv e, alternatingGroup.commutator_perm_eq h5]
  have hinj : Function.Injective (H.subtype.comp e.symm.toMonoidHom) :=
    fun x y hxy => e.symm.injective (Subtype.ext hxy)
  let eA : ↥⁅H, H⁆ ≃* ↥(alternatingGroup (Fin 5)) :=
    ((Subgroup.equivMapOfInjective _ _ hinj).trans (MulEquiv.subgroupCongr hAeq.symm)).symm
  have hmem : ∀ x (hx : x ∈ H), x ∈ ⁅H, H⁆ ↔ e ⟨x, hx⟩ ∈ alternatingGroup (Fin 5) := fun x hx => by
    rw [mem_commutator_iff_of_mulEquiv e hx, alternatingGroup.commutator_perm_eq h5]
  have hQN : (⁅H, H⁆ : Subgroup G).Normal := by
    haveI := hHN
    infer_instance
  have hQH : ⁅H, H⁆ ≤ H := Subgroup.commutator_le_self H
  set A : Subgroup G := ⁅H, H⁆ with hAdef
  haveI : IsSimpleGroup ↥A := eA.isSimpleGroup
  have hAcomm : commutator ↥A = ⊤ := by
    rw [← TauCeti.Subgroup.map_commutator_eq_commutator (f := eA.symm.toMonoidHom)
      eA.symm.surjective, commutator_alternatingGroup_eq_top h5,
      Subgroup.map_top_of_surjective eA.symm.toMonoidHom eA.symm.surjective]
  have hZA : Subgroup.center ↥A = ⊥ := by
    refine (IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center ↥A)).resolve_right
      fun hc => ?_
    have h1 : commutator ↥A = ⊥ := (commutator_eq_bot_iff_center_eq_top ↥A).2 hc
    rw [hAcomm] at h1
    exact bot_ne_top h1.symm
  have hAcomp : IsComponentOf A ⊤ := by
    haveI := hQN
    exact ⟨le_top, IsSubnormal.step le_top inferInstance (IsSubnormal.refl ⊤), hAcomm,
      ((QuotientGroup.quotientMulEquivOfEq hZA).trans QuotientGroup.quotientBot).isSimpleGroup⟩
  have hcen : Subgroup.centralizer (alternatingGroup (Fin 5) : Set (Equiv.Perm (Fin 5))) = ⊥ := by
    by_contra hne
    have hA5 := Equiv.Perm.alternatingGroup_le_of_normal h5
      ((Subgroup.nontrivial_iff_ne_bot _).2 hne)
    have hc : Subgroup.center ↥(alternatingGroup (Fin 5)) = ⊤ := eq_top_iff.2 fun x _ =>
      Subgroup.mem_center_iff.2 fun y =>
        Subtype.ext (Subgroup.mem_centralizer_iff.1 (hA5 x.2) y y.2)
    rw [alternatingGroup.center_eq_bot (by simp)] at hc
    exact bot_ne_top hc
  have hCH : ∀ h ∈ H, (∀ l ∈ A, l * h = h * l) → h = 1 := fun h hh hc => by
    have h1 : e ⟨h, hh⟩ ∈
        Subgroup.centralizer (alternatingGroup (Fin 5) : Set (Equiv.Perm (Fin 5))) := by
      refine Subgroup.mem_centralizer_iff.2 fun τ hτ => ?_
      obtain ⟨w, rfl⟩ := e.surjective τ
      have hw : (w : G) ∈ A := (hmem w w.2).2 hτ
      rw [← map_mul, ← map_mul]
      exact congrArg e (Subtype.ext (hc w hw))
    rw [hcen, Subgroup.mem_bot] at h1
    have h2 : (⟨h, hh⟩ : ↥H) = 1 := e.injective (by rw [h1, map_one])
    exact congrArg Subtype.val h2
  have hH120 : Nat.card ↥H = 120 := by
    rw [Nat.card_congr e.toEquiv, Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin]
    rfl
  have hA60 : Nat.card ↥A = 60 := by
    rw [Nat.card_congr eA.toEquiv, nat_card_alternatingGroup, Nat.card_eq_fintype_card,
      Fintype.card_fin]
    rfl
  obtain ⟨A', hA', hAA'⟩ := exists_mem_calP_commutator_ne_bot hH hAcomp
  obtain ⟨-, hnt⟩ := commOn_facts_of_mem_calP hρ hAcomp hA' hAA'
  have hnormA : ∀ g : G, g ∈ Subgroup.normalizer (A : Set G) := fun g => by
    rw [Subgroup.normalizer_eq_top_iff.2 hQN]
    exact Subgroup.mem_top g
  have hfaith : ∀ h ∈ H, (∀ n ∈ commOn ρ A ⊤, ρ h n = n) → h = 1 := fun h hh hN =>
    hCH h hh (commute_of_forall_apply_eq hnt (hnormA h) hN)
  rcases component_dichotomy hρ hH hAcomp (hshape A hAcomp) with
    ⟨hin, -⟩ | ⟨hZ, a, ha2, haN, haL, hS5⟩
  · exfalso
    obtain ⟨g, hgH, hgA⟩ := SetLike.exists_of_lt (lt_of_le_of_ne hQH fun h => by
      rw [h] at hA60
      omega)
    obtain ⟨l, hl, hgl⟩ := hin g
    have h1 : l⁻¹ * g = 1 := hfaith _ (mul_mem (inv_mem (hQH hl)) hgH) fun n hn => by
      rw [glRep_mul_apply, hgl n hn, glRep_inv_apply]
    exact hgA (inv_mul_eq_one.1 h1 ▸ hl)
  · have hcompl := isCompl_commOn_fixSub_of_secNatS5 ha2 haN haL hS5 hZ
    have hact : ∀ g : G, ∃ h₀ ∈ A ⊔ Subgroup.zpowers a, ∀ u ∈ commOn ρ A ⊤, ρ g u = ρ h₀ u :=
      fun g => exists_eq_apply_of_secNatS5 ha2 haN haL hS5 (hnormA g)
    have hinf : commOn ρ A ⊤ ⊓ fixSub ρ H = ⊥ := by
      refine eq_bot_iff.2 fun v hv => ?_
      rw [← hZ]
      exact Submodule.mem_inf.2 ⟨(Submodule.mem_inf.1 hv).1,
        mem_fixSub.2 fun q hq => mem_fixSub.1 (Submodule.mem_inf.1 hv).2 q (hQH hq)⟩
    have hcard : Nat.card ↥(A ⊔ Subgroup.zpowers a) = 120 := by
      obtain ⟨-, -, -, φ, -⟩ := hS5
      rw [Nat.card_congr φ.toEquiv, Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin]
      rfl
    refine ⟨fun c hc => apply_eq_self_of_commute_of_secNatS5 ha2 haN haL hS5
      fun l hl => hc l (hQH hl), hfaith, hcompl,
      fun X hX => noExcess_of_secNatS5 hS5 hX fun x _ => hact x, Or.inr (Or.inr (Or.inr ?_))⟩
    rw [hinf]
    exact secNatS5_of_forall_exists_eq_apply hS5 hfaith (fun h _ => hact h)
      (by rw [hcard, hH120])

end CFSG.LocalAnalysis.UniquenessCase.UC22.K148
