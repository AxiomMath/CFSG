module

public import CFSG.Open.LocalVocabulary
import CFSG.GroupTheory.ElemAbelianClosure
import CFSG.CGT.PushingUpLit.SYMB.ProdCard

public section

namespace CFSG.LocalAnalysis.WeakClosure81

variable {Γ : Type} [Group Γ]

private lemma w172_plift_closure_insert_eq (y : Γ → Γ) (e : Γ) (S : Finset Γ) :
    Subgroup.closure (y '' (insert e (S : Set Γ))) =
      Subgroup.zpowers (y e) ⊔ Subgroup.closure (y '' (S : Set Γ)) := by
  rw [Set.image_insert_eq, Set.insert_eq, Subgroup.closure_union,
    ← Subgroup.zpowers_eq_closure]

theorem w172_plift_card_family {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {D : Finset Γ} (y : Γ → Γ)
    (hy1 : ∀ e ∈ D, y e ≠ 1) (hyp : ∀ e ∈ D, y e ^ p = 1)
    (hinv : ∀ e ∈ D, e * y e * e⁻¹ = (y e)⁻¹)
    (hcen : ∀ e ∈ D, ∀ f ∈ D, f ≠ e → f * y e * f⁻¹ = y e)
    (hcomm : ∀ e ∈ D, ∀ f ∈ D, y e * y f = y f * y e) {S : Finset Γ} (hS : S ⊆ D) :
    CFSG.Open.IsElemAbelian p (Subgroup.closure (y '' (S : Set Γ))) ∧
      Nat.card (Subgroup.closure (y '' (S : Set Γ))) = p ^ S.card := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  induction S using Finset.induction_on with
  | empty =>
      constructor
      · simpa [Finset.coe_empty, Set.image_empty, Subgroup.closure_empty] using
          (CFSG.Open.IsElemAbelian.closure_of_commute (s := (∅ : Set Γ)) (by simp) (by simp))
      · rw [Finset.coe_empty, Set.image_empty, Subgroup.closure_empty, Finset.card_empty,
          pow_zero]
        exact Subgroup.card_bot
  | insert e S he ih =>
      have heD : e ∈ D := hS (Finset.mem_insert_self e S)
      have hSB : S ⊆ D := fun f hf => hS (Finset.mem_insert_of_mem hf)
      have hclosure : Subgroup.closure (y '' ((insert e S : Finset Γ) : Set Γ)) =
          Subgroup.zpowers (y e) ⊔ Subgroup.closure (y '' (S : Set Γ)) := by
        rw [Finset.coe_insert]
        exact w172_plift_closure_insert_eq y e S
      rw [hclosure]
      constructor
      · rw [← hclosure]
        refine CFSG.Open.IsElemAbelian.closure_of_commute ?_ ?_
        · rintro a ⟨f, hf, rfl⟩ b ⟨g, hg, rfl⟩
          exact hcomm f (hS (by simpa using hf)) g (hS (by simpa using hg))
        · rintro a ⟨f, hf, rfl⟩
          exact hyp f (hS (by simpa using hf))
      · set B : Subgroup Γ := Subgroup.closure (y '' (S : Set Γ)) with hBdef
        set C : Subgroup Γ := Subgroup.zpowers (y e) with hCdef
        have hBelem : CFSG.Open.IsElemAbelian p B := by
          rw [hBdef]
          exact (ih hSB).1
        have hBcard : Nat.card B = p ^ S.card := by
          rw [hBdef]
          exact (ih hSB).2
        have hcommCB : ∀ c ∈ C, ∀ d ∈ B, c * d = d * c := by
          intro c hc d hd
          have hcomm_gen : Commute (y e) d := by
            rw [hBdef] at hd
            refine Subgroup.closure_induction (p := fun z _ => Commute (y e) z) ?_ ?_ ?_ ?_ hd
            · intro z hz
              obtain ⟨f, hf, rfl⟩ := hz
              exact hcomm e heD f (hSB (by simpa using hf))
            · exact Commute.one_right _
            · intro u v hu hv ihu ihv
              exact ihu.mul_right ihv
            · intro u hu ihu
              exact ihu.inv_right
          rw [hCdef] at hc
          obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hc
          exact hcomm_gen.zpow_left k
        have hinf : C ⊓ B = ⊥ := by
          rw [Subgroup.eq_bot_iff_forall]
          intro x hx
          obtain ⟨hxC, hxB⟩ := Subgroup.mem_inf.mp hx
          rw [hCdef] at hxC
          rw [hBdef] at hxB
          have hfix : e * x * e⁻¹ = x := by
            refine Subgroup.closure_induction (p := fun z _ => e * z * e⁻¹ = z) ?_ ?_ ?_ ?_ hxB
            · intro z hz
              obtain ⟨f, hf, rfl⟩ := hz
              have hfS : f ∈ S := by simpa using hf
              exact hcen f (hSB hfS) e heD (fun h => he (by rw [h]; exact hfS))
            · simp
            · intro u v hu hv ihu ihv
              rw [show e * (u * v) * e⁻¹ = (e * u * e⁻¹) * (e * v * e⁻¹) by group, ihu, ihv]
            · intro u hu ihu
              rw [show e * u⁻¹ * e⁻¹ = (e * u * e⁻¹)⁻¹ by group, ihu]
          have hxinv : e * x * e⁻¹ = x⁻¹ := by
            obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hxC
            rw [← hk]
            rw [show e * (y e) ^ k * e⁻¹ = (e * y e * e⁻¹) ^ k from
              (conj_zpow (i := k) (a := e) (b := y e)).symm, hinv e heD]
            simp
          have hxx : x * x = 1 := by
            have hxinv' : x = x⁻¹ := hfix.symm.trans hxinv
            have h := congrArg (fun z => x * z) hxinv'
            simpa using h
          have hxp : x ^ p = 1 := hBelem.2 x hxB
          have h2 : orderOf x ∣ 2 :=
            orderOf_dvd_iff_pow_eq_one.mpr (by rw [pow_two]; exact hxx)
          have hpdvd : orderOf x ∣ p := orderOf_dvd_iff_pow_eq_one.mpr hxp
          rcases hp.eq_one_or_self_of_dvd (orderOf x) hpdvd with h1 | h1
          · exact orderOf_eq_one_iff.mp h1
          · have hp2dvd : p ∣ 2 := h1 ▸ h2
            rcases Nat.prime_two.eq_one_or_self_of_dvd p hp2dvd with h | h
            · exact absurd h hp.ne_one
            · exact absurd h hp2
        have hCcard : Nat.card C = p := by
          rw [hCdef, Nat.card_zpowers]
          exact orderOf_eq_prime (hyp e heD) (hy1 e heD)
        have hcardsup : Nat.card ↥(C ⊔ B) = Nat.card ↥C * Nat.card ↥B := by
          have h := CFSG.CGT.PushingUpLit.SYMB.card_sup_mul_card_inf_of_commute
            (C := C) (D := B) hcommCB
          rw [hinf, Subgroup.card_bot, mul_one] at h
          exact h
        rw [hcardsup, hCcard, hBcard, Finset.card_insert_of_notMem he]
        rw [pow_succ]
        exact Nat.mul_comm _ _

end CFSG.LocalAnalysis.WeakClosure81

end
