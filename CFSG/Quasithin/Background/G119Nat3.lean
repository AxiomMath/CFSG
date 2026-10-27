module

public import CFSG.Quasithin.Background.G119Nat2
public import CFSG.Quasithin.Background.G11BridgeG6
public import CFSG.Quasithin.Background.G6Transvection

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

namespace G11

section Multiplicative

variable {Q : Type} [CommGroup Q]

theorem g119_commV_zero_ne_bot_and_ne_top {K : Subgroup (MulAut Q)}
    {Ks : Fin 2 → Subgroup (MulAut Q)} (hd : G6.IsTransvectionDecomposition K Ks) :
    commV (Ks 0) ≠ ⊥ ∧ commV (Ks 0) ≠ ⊤ := by
  have h01 : (0 : Fin 2) ≠ 1 := by decide
  have htriv : ∀ i j : Fin 2, i ≠ j → commV (Ks j) = ⊤ → Ks i = ⊥ := by
    intro i j hij hj
    have h1 := hd.commOn_eq_bot i j hij
    rw [hj, ← G6.commV_eq_commOn_top] at h1
    rw [eq_bot_iff]
    intro f hf
    rw [Subgroup.mem_bot]
    ext v
    have := G6.mem_commV_of_mem hf v
    rw [h1, Subgroup.mem_bot, mul_inv_eq_one] at this
    exact this
  have hsup : commV (Ks 0) ⊔ commV (Ks 1) = ⊤ := by
    have := G6.iSup_fin_two (fun i => commV (Ks i))
    rw [hd.iSup_commV] at this
    exact this.symm
  have hdis : Disjoint (commV (Ks 0)) (commV (Ks 1)) := hd.commV_indep.pairwiseDisjoint h01
  constructor
  · intro h0
    rw [h0, bot_sup_eq] at hsup
    exact hd.ne_bot 0 (htriv 0 1 h01 hsup)
  · intro h0
    rw [h0] at hdis
    have h1 : commV (Ks 1) = ⊥ := by
      rw [eq_bot_iff]
      exact (disjoint_top.1 hdis.symm).le
    rw [h1, sup_bot_eq] at hsup
    exact hd.ne_bot 1 (htriv 1 0 h01.symm hsup)

end Multiplicative

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
  {B : LinearMap.BilinForm (ZMod 2) V} {Γ : Subgroup (GLV V)} {v₁ : V}
  {W : Submodule (ZMod 2) V} {X X₀ L : Subgroup (GLV V)} {I : Submodule (ZMod 2) V}

namespace G119Ctx

variable (c : G119Ctx B Γ v₁ W X X₀ L I)

include c

theorem restrictRange_H_le :
    restrictRange (normalClosure Γ L) I c.irrPlus.1 ≤
      restrictRange (normalClosure Γ L ⊔ X) I c.irr_sup.1 :=
  g119_restrictRange_mono le_sup_left c.irrPlus.1 c.irr_sup.1

theorem restrictEquiv_mem_G {x₀ : GLV V} (hx₀ : x₀ ∈ X) :
    restrictEquiv x₀ I (c.conjSub_I hx₀) ∈ restrictRange (normalClosure Γ L ⊔ X) I c.irr_sup.1 :=
  restrictEquiv_mem_restrictRange c.irr_sup.1 (Subgroup.mem_sup_right hx₀)

theorem isPerfect_restrictRange_H :
    Group.IsPerfect ↥(restrictRange (normalClosure Γ L) I c.irrPlus.1) := by
  have := c.isPerfect_H
  exact Group.IsPerfect.range (restrictHom (normalClosure Γ L) I c.irrPlus.1)

theorem false_of_two_factors {x₀ : GLV V} (hx₀ : x₀ ∈ X)
    (Ks : Fin 2 → Subgroup (MulAut (Multiplicative ↥I)))
    (hd : G6.G64Decomposition (toMulSub (restrictRange (normalClosure Γ L ⊔ X) I c.irr_sup.1))
      (linEquivMulAut (restrictEquiv x₀ I (c.conjSub_I hx₀))) Ks)
    {t : MulAut (Multiplicative ↥I)}
    (hteq : toMulSub (restrictRange (normalClosure Γ L ⊔ X) I c.irr_sup.1) =
      G6.classClosure (toMulSub (restrictRange (normalClosure Γ L ⊔ X) I c.irr_sup.1))
        (linEquivMulAut (restrictEquiv x₀ I (c.conjSub_I hx₀))) ⊔ Subgroup.zpowers t) :
    False := by
  classical
  set G' := restrictRange (normalClosure Γ L ⊔ X) I c.irr_sup.1 with hG'
  set ā := restrictEquiv x₀ I (c.conjSub_I hx₀) with hā
  set Hb := restrictRange (normalClosure Γ L) I c.irrPlus.1 with hHb
  set Nn : Subgroup (GLV ↥I) := normalClosure G' (Subgroup.zpowers ā) with hNn
  have hāG : ā ∈ G' := c.restrictEquiv_mem_G hx₀
  have hNnG : Nn ≤ G' := normalClosure_le (Subgroup.zpowers_le.2 hāG)
  have hclos : G6.classClosure (toMulSub G') (linEquivMulAut ā) = toMulSub Nn :=
    classClosure_toMulSub G' ā
  set t' : GLV ↥I := linEquivMulAut.symm t with ht'
  have htt' : linEquivMulAut t' = t := by simp [ht']
  have hGeq : Nn ⊔ Subgroup.zpowers t' = G' := by
    apply toMulSub_injective
    rw [toMulSub_sup, ← zpowers_linEquivMulAut, htt', ← hclos]
    exact hteq.symm
  have hHbNn : Hb ≤ Nn :=
    g119_le_of_perfect_of_sup_zpowers hNnG (fun g hg n hn => normalClosure_normal G' _ g hg n hn)
      hGeq (c.restrictRange_H_le) c.isPerfect_restrictRange_H
  set Ki : Fin 2 → Subgroup (GLV ↥I) := fun i => toMulSubIso.symm (Ks i) with hKi
  have hKi' : ∀ i, toMulSub (Ki i) = Ks i := fun i => toMulSubIso.apply_symm_apply (Ks i)
  have hKsup : Ki 0 ⊔ Ki 1 = Nn := by
    apply toMulSub_injective
    rw [toMulSub_sup, hKi', hKi', ← hclos, ← hd.decomp.iSup_eq, G6.iSup_fin_two]
  set Vi : Fin 2 → Submodule (ZMod 2) ↥I := fun i => subToSubgroup.symm (commV (Ks i)) with hVi
  have hVi' : ∀ i, subToSubgroup (Vi i) = commV (Ks i) := fun i =>
    subToSubgroup.apply_symm_apply _
  have hinv : ∀ i j : Fin 2, Invariant (Ki j) (Vi i) := by
    intro i j
    by_cases hij : i = j
    · subst hij
      exact isHSubmodule_toMulSub_iff.1 (by rw [hKi', hVi']; exact hd.decomp.isHSubmodule i)
    · intro k hk u hu
      have hk' : linEquivMulAut k ∈ Ks j := by
        have : linEquivMulAut k ∈ toMulSub (Ki j) := linEquivMulAut_mem_toMulSub.2 hk
        rwa [hKi'] at this
      have hu' : Multiplicative.ofAdd u ∈ commV (Ks i) := by
        rw [← hVi']
        exact hu
      have := hd.decomp.apply_eq_of_ne (Ne.symm hij) hk' hu'
      have h2 : k u = u := congrArg Multiplicative.toAdd this
      rw [h2]
      exact hu
  have hinvN : ∀ i, Invariant Hb (Vi i) := by
    intro i
    have h1 : Invariant (Ki 0 ⊔ Ki 1) (Vi i) := (hinv i 0).sup_subgroup (hinv i 1)
    rw [hKsup] at h1
    exact h1.mono hHbNn
  have hirr := isIrr_restrictRange_top c.irr
  obtain ⟨hne0, hnetop⟩ := g119_commV_zero_ne_bot_and_ne_top hd.decomp
  rcases hirr.eq_bot_or_eq (hinvN 0) le_top with h | h
  · apply hne0
    rw [← hVi', h]
    exact OrderIso.map_bot _
  · apply hnetop
    rw [← hVi', h]
    exact OrderIso.map_top _

end G119Ctx

end G11

end CFSG.Quasithin
