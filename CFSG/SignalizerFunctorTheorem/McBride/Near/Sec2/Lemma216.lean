module

public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec2.Thm211
public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec2.Lemma216AuxB

public section

open CFSG.Open
open scoped Pointwise commutatorElement

namespace CFSG.SignalizerFunctorTheorem.McBride.Near

open Thm210

variable {Γ : Type*} [Group Γ] [Finite Γ] {p : ℕ} {A G : Subgroup Γ}

section Lemma216

variable {S : Subgroup Γ} (h : NearAsolvAction p A G) (hsol : sol G = ⊥) (hG1 : G ≠ ⊥)
  (hS : IsGreatest {Z : Subgroup Γ | Z ≤ G ∧ Admits (cenIn G A ⊔ A) Z ∧ Group.IsSolvable Z} S)

include h hsol hG1 hS

theorem lemma216_d0 :
    d0 A G S = cenIn G A ⊓ kOf G :=
  (Lemma216.Hyp.d0_eq ⟨h, hsol, hG1, hS⟩).trans (Lemma216.cenIn_inf_kOf G A).symm

theorem lemma216a :
    s0 G S ≤ G ⊓ sectionCentralizer (s1 G S) (d2 A G S ⊔ s1 G S) ∧
      G ⊓ sectionCentralizer (s1 G S) (d2 A G S ⊔ s1 G S) ≤ khat G :=
  ⟨Lemma216.Hyp.s0_le_W ⟨h, hsol, hG1, hS⟩, Lemma216.Hyp.W_le_khat ⟨h, hsol, hG1, hS⟩⟩

theorem lemma216b
    : s2 G S = G ⊓ sectionCentralizer (s1 G S) (d0 A G S ⊔ s1 G S) :=
  Lemma216.Hyp.s2_eq ⟨h, hsol, hG1, hS⟩

theorem lemma216c
    {Z : Subgroup Γ} (hZ : Z ≤ G) (hZadm : Admits (cenIn G A ⊔ A) Z)
    (hZK : Z ⊓ kOf G ≤ s1 G S) : Z ≤ s2 G S := by
  have H : Lemma216.Hyp p A G S := ⟨h, hsol, hG1, hS⟩
  have hKG : kOf G ≤ G := kOf_le G
  have hKN : G ⊔ A ≤ Subgroup.normalizer (kOf G : Set Γ) :=
    sup_le (Nonsolv.le_normalizer_kOf G) H.A_le_normalizer
  have hS0 : s0 G S ≤ S := inf_le_left
  have hsolv : Group.IsSolvable ↥(Z ⊓ kOf G) := by
    have : Group.IsSolvable ↥S := hS.1.2.2
    exact Group.isSolvable_of_isSolvable_injective
      (Subgroup.inclusion_injective (hZK.trans (Lemma216.s1_le_s0.trans hS0)))
  have hZN := thm211c_le h hKG ⟨hKG.trans le_sup_left, hKN⟩ hZ hZadm hsolv
  have hX : Admits (cenIn G A ⊔ A) (kOf G) :=
    sup_le (fun d hd => Nonsolv.le_normalizer_kOf G (mem_cenIn_iff.mp hd).1) H.A_le_normalizer
  have hscal : scalJoin (kOf G) A (cenIn G A) = s0 G S := by
    rw [(thm211b h hKG hX).1, H.scalJoin_eq]
    rfl
  rw [hscal] at hZN
  have hZS1 : Z ≤ Subgroup.normalizer (s1 G S : Set Γ) := fun z hz =>
    Lemma216.mem_normalizer_fittingSubgroupOf (hZN hz)
  have hD0S1 : d0 A G S ≤ Subgroup.normalizer (s1 G S : Set Γ) := fun d hd =>
    le_normalizer_fittingSubgroupOf (s0 G S) (Lemma216.d0_le_s0 hd)
  have hc : ∀ z ∈ Z, ∀ y ∈ d0 A G S ⊔ s1 G S, ⁅z, y⁆ ∈ s1 G S := by
    intro z hz
    refine Lemma216.commutator_mem_of_mem_sup hD0S1 Subgroup.le_normalizer (fun d hd => ?_)
      (fun s hs => ?_)
    · have hdK : d ∈ kOf G := Lemma216.s0_le_kOf (Lemma216.d0_le_s0 hd)
      have hdD : d ∈ cenIn G A := (inf_le_left : d0 A G S ≤ cenIn G A) hd
      have hdN : d ∈ Subgroup.normalizer (Z : Set Γ) := hZadm (Subgroup.mem_sup_left hdD)
      have hzK : ⁅z, d⁆ ∈ kOf G :=
        Lemma216.commutator_mem_of_mem_normalizer (Nonsolv.le_normalizer_kOf G (hZ hz)) hdK
      have hzZ : ⁅z, d⁆ ∈ Z := by
        have h1 := (Subgroup.mem_normalizer_iff.mp hdN z⁻¹).mp (inv_mem hz)
        have e : ⁅z, d⁆ = z * (d * z⁻¹ * d⁻¹) := by
          simp only [commutatorElement_def]
          group
        rw [e]
        exact mul_mem hz h1
      exact hZK (Subgroup.mem_inf.mpr ⟨hzZ, hzK⟩)
    · exact Lemma216.commutator_mem_of_mem_normalizer (hZS1 hz) hs
  intro z hz
  rw [H.s2_eq]
  exact Subgroup.mem_inf.mpr ⟨hZ hz,
    (Lemma216.mem_sectionCentralizer_iff_of_le le_sup_right).mpr ⟨hZS1 hz, hc z hz⟩⟩

theorem lemma216d
    {Z : Subgroup Γ} (hZ : Z ≤ G) (hZadm : Admits (cenIn G A ⊔ A) Z)
    (hZK : Z ⊓ kOf G ⊓ cenIn G A = ⊥) : Z ≤ s1 G S := by
  have H : Lemma216.Hyp p A G S := ⟨h, hsol, hG1, hS⟩
  have hK := H.semisimpleAction
  have hKN : cenIn (kOf G) A ⊔ A ≤ Subgroup.normalizer (kOf G : Set Γ) :=
    sup_le (fun d hd => Nonsolv.le_normalizer_kOf G (kOf_le G (mem_cenIn_iff.mp hd).1))
      H.A_le_normalizer
  have hadm : Admits (cenIn (kOf G) A ⊔ A) (Z ⊓ kOf G) := fun x hx =>
    Lemma216.mem_normalizer_inf
      (hZadm (sup_le_sup_right (Lemma216.cenIn_kOf_le G A) A hx)) (hKN hx)
  have hbot : Z ⊓ kOf G ⊓ cenIn (kOf G) A = ⊥ :=
    eq_bot_iff.mpr ((inf_le_inf_left _ (Lemma216.cenIn_kOf_le G A)).trans hZK.le)
  have hmax := (thm210k hK).2
    (show Z ⊓ kOf G ∈ {X | X ≤ kOf G ∧ Admits (cenIn (kOf G) A ⊔ A) X ∧
      X ⊓ cenIn (kOf G) A = ⊥} from ⟨inf_le_right, hadm, hbot⟩)
  have hF : CFSG.fittingSubgroupOf (mOf A (kOf G)) = s1 G S := by
    rw [hK.mOf_eq_kProd, hK.fittingSubgroupOf_kProd, H.s1_eq]
  have hAS1 : A ≤ Subgroup.normalizer (s1 G S : Set Γ) := by
    rw [H.s1_eq]
    exact hK.admits_fProd
  have hcomm : ⁅CFSG.fittingSubgroupOf (mOf A (kOf G)), A⁆ ≤ s1 G S := by
    rw [hF]
    refine Subgroup.commutator_le.mpr fun x hx a ha => ?_
    have := Lemma216.commutator_mem_of_mem_normalizer (hAS1 ha) hx
    rw [← commutatorElement_inv]
    exact inv_mem this
  have hZK' : Z ⊓ kOf G ≤ s1 G S := hmax.trans hcomm
  have hZS2 := lemma216c h hsol hG1 hS hZ hZadm hZK'
  intro z hz
  exact hZK' (Subgroup.mem_inf.mpr ⟨hz,
    Lemma216.s0_le_kOf (Lemma216.s2_le_s0 (hZS2 hz))⟩)

end Lemma216

end CFSG.SignalizerFunctorTheorem.McBride.Near
