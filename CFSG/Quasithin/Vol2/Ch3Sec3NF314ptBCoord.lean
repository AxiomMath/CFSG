module

public import CFSG.Quasithin.Vol2.Ch3Sec3NF314ptBFL
public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3314D
public import CFSG.CharacterTheory.Semidihedral.CyclicPairFrattini

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Quasithin.H13.Ins314

open CFSG.Quasithin CFSG.Quasithin.H13.CZL32

namespace Coord

variable {V : Type} [CommGroup V] {H : Subgroup (MulAut V)} {U Z : Subgroup V} {k : ℕ}
  (c : Coord H U Z k)

theorem img_one : c.img 1 = 1 := by
  simp [img]

theorem img_inv (γ : L3.Γ) : c.img γ⁻¹ = (c.img γ)⁻¹ := by
  simp [img]

theorem img_conj (b γ : L3.Γ) :
    c.img (b * γ * b⁻¹) = c.img b * c.img γ * (c.img b)⁻¹ := by
  rw [c.img_mul, c.img_mul, c.img_inv]

theorem β_injective (hZ : Z = ⊥) : Function.Injective c.β := by
  intro a b hab
  have h1 : (b : V) * (a : V)⁻¹ ∈ Z := (c.mul_inv_mem_iff a b).mpr hab.symm
  rw [hZ, Subgroup.mem_bot, mul_inv_eq_one] at h1
  exact Subtype.ext h1.symm

theorem le_of_commutators (hZ : Z = ⊥) {γ : L3.Γ} (hγ3 : γ ^ 3 = 1) (hγ1 : γ ≠ 1)
    {u₀ : V} (hu₀U : u₀ ∈ U) (hu₀1 : u₀ ≠ 1)
    (hfix : ∀ b ∈ bSub, c.img (b * γ * b⁻¹) u₀ = u₀)
    {W : Subgroup V} (hW : ∀ b ∈ bSub, ∀ u ∈ U, u * c.img (b * γ * b⁻¹) u⁻¹ ∈ W) : U ≤ W := by
  classical
  have hneg : ∀ y : L3.Vec, -y = y := by decide +kernel
  set x₀ := Multiplicative.toAdd (c.β ⟨u₀, hu₀U⟩) with hx₀
  have hx₀ne : x₀ ≠ 0 := by
    intro h0
    have h1 : c.β ⟨u₀, hu₀U⟩ = 1 := by
      rw [← ofAdd_toAdd (c.β ⟨u₀, hu₀U⟩)]
      exact congrArg Multiplicative.ofAdd h0
    rw [c.ker_β] at h1
    rw [hZ, Subgroup.mem_bot] at h1
    exact hu₀1 h1
  obtain ⟨j, hj⟩ : ∃ j, x₀ j ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hx₀ne (funext hcon)
  have hfixvec : ∀ b : L3.Γ, (L3.act b e1 = e1 ∧ ∀ w, w ∈ P12 ↔ L3.act b w ∈ P12) →
      L3.act (b * γ * b⁻¹) (x₀ j) = x₀ j := by
    intro b hb
    have h1 := hfix b (mem_bSub.mpr hb)
    have h3 : c.β ⟨c.img (b * γ * b⁻¹) u₀, c.img_mem_U _ hu₀U⟩ = c.β ⟨u₀, hu₀U⟩ := by
      congr 1
      exact Subtype.ext h1
    have h4 := congrFun (c.β_img (b * γ * b⁻¹) ⟨u₀, hu₀U⟩) j
    have h5 := congrArg (fun w : Multiplicative (Fin k → L3.Vec) => Multiplicative.toAdd w j) h3
    exact h4.symm.trans h5
  have hspan := fl_check γ hγ3 hγ1 (x₀ j) hj hfixvec
  set Wc : Subgroup (Multiplicative (Fin k → L3.Vec)) := (W.subgroupOf U).map c.β with hWc
  have hS : ∀ i : Fin k, ∀ s ∈ S0 γ,
      Multiplicative.ofAdd (Pi.single i s : Fin k → L3.Vec) ∈ Wc := by
    intro i s hs
    obtain ⟨b, hb', w, rfl⟩ := mem_S0.mp hs
    obtain ⟨ũ, hũ⟩ := c.β_surj (Multiplicative.ofAdd (Pi.single i w : Fin k → L3.Vec))
    have hWu := hW b (mem_bSub.mpr hb') ũ ũ.2
    refine ⟨ũ * ⟨c.img (b * γ * b⁻¹) ((ũ⁻¹ : ↥U) : V), c.img_mem_U _ (ũ⁻¹).2⟩, ?_, ?_⟩
    · show (ũ : V) * c.img (b * γ * b⁻¹) ((ũ : V)⁻¹) ∈ W
      exact hWu
    · rw [map_mul, hũ]
      have h1 : c.β ⟨c.img (b * γ * b⁻¹) ((ũ⁻¹ : ↥U) : V), c.img_mem_U _ (ũ⁻¹).2⟩ =
          Multiplicative.ofAdd (fun l => L3.act (b * γ * b⁻¹)
            (Multiplicative.toAdd (c.β ũ⁻¹) l)) := by
        apply Multiplicative.toAdd.injective
        exact c.β_img (b * γ * b⁻¹) ũ⁻¹
      rw [h1, map_inv, hũ]
      apply Multiplicative.toAdd.injective
      funext l
      simp only [toAdd_mul, toAdd_inv, toAdd_ofAdd, Pi.add_apply, Pi.neg_apply]
      by_cases hl : l = i
      · subst hl
        simp only [Pi.single_eq_same]
        rw [hneg, sub_eq_add_neg, hneg, add_comm]
      · simp only [Pi.single_eq_of_ne hl, neg_zero, L3.act_zero, add_zero]
  have hP : ∀ i : Fin k, ∀ F : Finset L3.Vec,
      (∀ f ∈ F, Multiplicative.ofAdd (Pi.single i f : Fin k → L3.Vec) ∈ Wc) →
      ∀ v ∈ spanStep (S0 γ) F, Multiplicative.ofAdd (Pi.single i v : Fin k → L3.Vec) ∈ Wc := by
    intro i F hF
    refine spanStep_induction
      (P := fun v => Multiplicative.ofAdd (Pi.single i v : Fin k → L3.Vec) ∈ Wc) ?_ hF
    intro s hs a ha
    have h1 : Multiplicative.ofAdd (Pi.single i (a + s) : Fin k → L3.Vec) =
        Multiplicative.ofAdd (Pi.single i a : Fin k → L3.Vec) *
          Multiplicative.ofAdd (Pi.single i s : Fin k → L3.Vec) := by
      rw [Pi.single_add, ofAdd_add]
    show Multiplicative.ofAdd (Pi.single i (a + s) : Fin k → L3.Vec) ∈ Wc
    rw [h1]
    exact Wc.mul_mem ha (hS i s hs)
  have hsingle : ∀ i : Fin k, ∀ v : L3.Vec,
      Multiplicative.ofAdd (Pi.single i v : Fin k → L3.Vec) ∈ Wc := by
    intro i v
    have hv : v ∈ spanStep (S0 γ) (spanStep (S0 γ) (spanStep (S0 γ) {0})) := by
      rw [hspan]
      exact Finset.mem_univ v
    have h0 : ∀ f ∈ ({0} : Finset L3.Vec),
        Multiplicative.ofAdd (Pi.single i f : Fin k → L3.Vec) ∈ Wc := by
      intro f hf
      rw [Finset.mem_singleton] at hf
      subst hf
      rw [Pi.single_zero, ofAdd_zero]
      exact Wc.one_mem
    have h1 := hP i ({0} : Finset L3.Vec) h0
    have h2 := hP i (spanStep (S0 γ) {0}) h1
    exact hP i (spanStep (S0 γ) (spanStep (S0 γ) {0})) h2 v hv
  have htop : ∀ x : Multiplicative (Fin k → L3.Vec), x ∈ Wc := by
    intro x
    have hx : x = ∏ i : Fin k,
        Multiplicative.ofAdd (Pi.single i (Multiplicative.toAdd x i) : Fin k → L3.Vec) := by
      apply Multiplicative.toAdd.injective
      rw [toAdd_prod]
      simp only [toAdd_ofAdd]
      exact (Finset.univ_sum_single (Multiplicative.toAdd x)).symm
    rw [hx]
    exact Subgroup.prod_mem _ fun i _ => hsingle i _
  intro u hu
  obtain ⟨z, hz, hzu⟩ := htop (c.β ⟨u, hu⟩)
  have hzeq : z = ⟨u, hu⟩ := c.β_injective hZ hzu
  rw [hzeq] at hz
  exact hz

end Coord

end CFSG.Quasithin.H13.Ins314
