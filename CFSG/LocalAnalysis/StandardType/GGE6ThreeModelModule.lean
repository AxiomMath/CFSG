module

public import CFSG.LocalAnalysis.StandardType.GGTableBE6ThreeWeylModule
public import CFSG.LocalAnalysis.StandardType.GGSixBstarNoOffenderExcRestProofE6Hyp
public import CFSG.LocalAnalysis.StandardType.GGTableBExcAdLinear

public section

open scoped Matrix

namespace CFSG.StandardType.TableBExc.E6Three

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

private instance : NeZero Tag.E6.rank := ⟨by decide⟩

private lemma kE6_cast_eq_radE6 (i : Fin Tag.E6.rank) :
    ((NoOffRest.kE6 i : ℤ) : ZMod 3) = radE6 i := by
  fin_cases i <;> decide

private lemma dotProduct_radE6_eq_kDotP (v : Fin Tag.E6.rank → ZMod 3) :
    v ⬝ᵥ radE6 = NoOffRest.kDotP 3 v := by
  rw [dotProduct, NoOffRest.kDotP]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [kE6_cast_eq_radE6 i, mul_comm]

private def x1 : Fin Tag.E6.rank → ZMod 3 := Pi.single (0 : Fin Tag.E6.rank) 1

private lemma kDotP_x1 : NoOffRest.kDotP 3 x1 = 1 := by
  decide +kernel

private def proj : (Fin Tag.E6.rank → ZMod 3) →+ (Fin Tag.E6.rank → ZMod 3) :=
  AddMonoidHom.mk' (fun v => v - NoOffRest.kDotP 3 v • x1) (by
    intro a b
    show a + b - NoOffRest.kDotP 3 (a + b) • x1 =
      (a - NoOffRest.kDotP 3 a • x1) + (b - NoOffRest.kDotP 3 b • x1)
    rw [NoOffRest.kDotP_add, add_smul]
    abel)

private lemma proj_mem (v : Fin Tag.E6.rank → ZMod 3) : proj v ∈ NoOffRest.hypE6 := by
  rw [NoOffRest.mem_hypE6]
  show NoOffRest.kDotP 3 (v - NoOffRest.kDotP 3 v • x1) = 0
  rw [NoOffRest.kDotP_sub, NoOffRest.kDotP_smul, kDotP_x1, mul_one, sub_self]

private def proj' : (Fin Tag.E6.rank → ZMod 3) →+ NoOffRest.hypE6 :=
  proj.codRestrict NoOffRest.hypE6 proj_mem

private lemma proj_fix (v : Fin Tag.E6.rank → ZMod 3) (hv : v ∈ NoOffRest.hypE6) :
    proj v = v := by
  show v - NoOffRest.kDotP 3 v • x1 = v
  rw [NoOffRest.mem_hypE6.mp hv, zero_smul]
  exact sub_zero v

theorem vInn_eq_hypE6 : vInn = NoOffRest.hypE6 := by
  ext v
  rw [mem_vInn_iff, NoOffRest.mem_hypE6, dotProduct_radE6_eq_kDotP]

theorem adAct_sub_mem_hypE6 (w : WeylGroup .E6) (x : Fin Tag.E6.rank → ZMod 3) :
    adAct .E6 3 w x - x ∈ NoOffRest.hypE6 := by
  rw [NoOffRest.mem_hypE6, NoOffRest.kDotP_sub, NoOffRest.kDot_adAct, sub_self]

theorem hypE6_le_of_invariant (G : AddSubgroup (Fin Tag.E6.rank → ZMod 3))
    (hG : ∀ i, ∀ v ∈ G, adRefl .E6 3 i v ∈ G) (hne : G ≠ ⊥) : NoOffRest.hypE6 ≤ G := by
  rw [← vInn_eq_hypE6]
  exact vInn_le_of_invariant G hG hne

theorem exists_smul_of_commute_hypE6 (f : NoOffRest.hypE6 →+ NoOffRest.hypE6)
    (hc : ∀ (i : Fin Tag.E6.rank) (x y : NoOffRest.hypE6),
      (y : Fin Tag.E6.rank → ZMod 3) = adRefl .E6 3 i (x : Fin Tag.E6.rank → ZMod 3) →
        ((f y : NoOffRest.hypE6) : Fin Tag.E6.rank → ZMod 3) =
          adRefl .E6 3 i ((f x : NoOffRest.hypE6) : Fin Tag.E6.rank → ZMod 3)) :
    ∃ c : ZMod 3, ∀ x : NoOffRest.hypE6,
      ((f x : NoOffRest.hypE6) : Fin Tag.E6.rank → ZMod 3) =
        c • (x : Fin Tag.E6.rank → ZMod 3) := by
  let f' : (Fin Tag.E6.rank → ZMod 3) →+ (Fin Tag.E6.rank → ZMod 3) :=
    NoOffRest.hypE6.subtype.comp (f.comp proj')
  have hf : ∀ v ∈ vInn, f' v ∈ vInn := by
    intro v _
    rw [vInn_eq_hypE6]
    exact (f (proj' v)).2
  have hcomm : ∀ i, ∀ v ∈ vInn, f' (adRefl Tag.E6 3 i v) = adRefl Tag.E6 3 i (f' v) := by
    intro i v hv
    have hv' : v ∈ NoOffRest.hypE6 := by rwa [vInn_eq_hypE6] at hv
    have hAv : adRefl Tag.E6 3 i v ∈ NoOffRest.hypE6 := by
      rw [← vInn_eq_hypE6]; exact adRefl_mem_vInn hv
    have e1 : f' (adRefl Tag.E6 3 i v) =
        ((f ⟨adRefl Tag.E6 3 i v, hAv⟩ : NoOffRest.hypE6) :
          Fin Tag.E6.rank → ZMod 3) := by
      show ((f (proj' (adRefl Tag.E6 3 i v)) : NoOffRest.hypE6) :
        Fin Tag.E6.rank → ZMod 3) = _
      rw [show proj' (adRefl Tag.E6 3 i v) = ⟨adRefl Tag.E6 3 i v, hAv⟩ from
        Subtype.ext (proj_fix _ hAv)]
    have e2 : f' v = ((f ⟨v, hv'⟩ : NoOffRest.hypE6) : Fin Tag.E6.rank → ZMod 3) := by
      show ((f (proj' v) : NoOffRest.hypE6) : Fin Tag.E6.rank → ZMod 3) = _
      rw [show proj' v = ⟨v, hv'⟩ from Subtype.ext (proj_fix _ hv')]
    rw [e1, e2]
    exact hc i ⟨v, hv'⟩ ⟨adRefl Tag.E6 3 i v, hAv⟩ rfl
  obtain ⟨c, hc'⟩ := exists_smul_of_commute_adRefl f' hf hcomm
  refine ⟨c, fun x => ?_⟩
  have hx : (x : Fin Tag.E6.rank → ZMod 3) ∈ vInn := by
    rw [vInn_eq_hypE6]; exact x.2
  have h := hc' (x : Fin Tag.E6.rank → ZMod 3) hx
  have e : f' (x : Fin Tag.E6.rank → ZMod 3) =
      ((f x : NoOffRest.hypE6) : Fin Tag.E6.rank → ZMod 3) := by
    show ((f (proj' (x : Fin Tag.E6.rank → ZMod 3)) : NoOffRest.hypE6) :
      Fin Tag.E6.rank → ZMod 3) = _
    rw [show proj' (x : Fin Tag.E6.rank → ZMod 3) = x from
      Subtype.ext (proj_fix _ x.2)]
  rwa [e] at h

section Faithful

theorem eq_one_of_adAct_eq_on_hypE6 {w : WeylGroup .E6}
    (h : ∀ x ∈ NoOffRest.hypE6, adAct .E6 3 w x = x) : w = 1 := by
  apply NoOffRest.hypPerm_injective
  apply Equiv.ext
  intro x
  apply Subtype.ext
  change adAct .E6 3 w (x : Fin Tag.E6.rank → ZMod 3) =
    adAct .E6 3 1 (x : Fin Tag.E6.rank → ZMod 3)
  rw [h x.1 x.2, adAct_one]

end Faithful

theorem weyl_induction (P : WeylGroup .E6 → Prop) (h1 : P 1)
    (hs : ∀ (i : Fin Tag.E6.rank) (w : WeylGroup .E6), P w → P (simple .E6 i * w)) :
    ∀ w, P w := by
  intro w
  obtain ⟨ω, rfl⟩ := (coxeterSystem .E6).wordProd_surjective w
  induction ω with
  | nil => rw [CoxeterSystem.wordProd_nil]; exact h1
  | cons i ω ih => rw [CoxeterSystem.wordProd_cons]; exact hs i _ ih

theorem exists_not_mem_hypE6 : ∃ x : Fin Tag.E6.rank → ZMod 3, x ∉ NoOffRest.hypE6 := by
  refine ⟨x1, ?_⟩
  rw [NoOffRest.mem_hypE6, kDotP_x1]
  decide

theorem card_top : Nat.card (Fin Tag.E6.rank → ZMod 3) = 3 ^ 6 := by
  rw [Nat.card_pi]
  simp [Nat.card_zmod, Finset.prod_const, Fintype.card_fin]
  decide

end CFSG.StandardType.TableBExc.E6Three
