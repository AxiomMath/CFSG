module

public import CFSG.LocalAnalysis.StandardType.GGTBJE6ThreeData
public import CFSG.LocalAnalysis.StandardType.GGCoxeterFaithfulE6Three
public import CFSG.LocalAnalysis.StandardType.GGTBRowE6Equiv

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley TableBExc
  TableBExc.E6Three

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private def e6c3w_hypMod : Submodule (ZMod 3) (Fin Tag.E6.rank → ZMod 3) where
  carrier := NoOffRest.hypE6
  zero_mem' := NoOffRest.hypE6.zero_mem'
  add_mem' := fun ha hb => NoOffRest.hypE6.add_mem' ha hb
  smul_mem' := by
    intro c x hx
    have hx' : NoOffRest.kDotP 3 x = 0 := NoOffRest.mem_hypE6.mp hx
    show NoOffRest.kDotP 3 (c • x) = 0
    rw [NoOffRest.kDotP_smul, hx', mul_zero]

private theorem e6c3w_h_mem (i : Fin Tag.E6.rank) :
    (fun j => (Tag.cartan .E6 i j : ZMod 3)) ∈ NoOffRest.hypE6 := by
  rw [NoOffRest.mem_hypE6]
  exact NoOffRest.kDot_cartan i

private def e6c3w_h (i : Fin Tag.E6.rank) : ↥e6c3w_hypMod :=
  ⟨fun j => (Tag.cartan .E6 i j : ZMod 3), e6c3w_h_mem i⟩

private def e6c3w_α (i : Fin Tag.E6.rank) :
    Module.Dual (ZMod 3) ↥e6c3w_hypMod where
  toFun v := v.1 i
  map_add' v u := rfl
  map_smul' c v := rfl

private theorem e6c3w_cartan_symm (i j : Fin Tag.E6.rank) :
    Tag.cartan .E6 i j = Tag.cartan .E6 j i := by
  fin_cases i <;> fin_cases j <;> decide

private theorem e6c3w_hα (i : Fin Tag.E6.rank) : e6c3w_α i (e6c3w_h i) = 2 := by
  change ((Tag.cartan .E6 i i : ℤ) : ZMod 3) = 2
  rw [Tag.cartan_self]
  norm_num

private theorem e6c3w_hP (i j : Fin Tag.E6.rank) :
    e6c3w_α i (e6c3w_h j) = (Tag.cartan .E6 i j : ZMod 3) := by
  change ((Tag.cartan .E6 j i : ℤ) : ZMod 3) = (Tag.cartan .E6 i j : ZMod 3)
  rw [e6c3w_cartan_symm j i]

private theorem e6c3w_intCartan_E6 :
    GGIntCartan CoxeterMatrix.E₆ (Tag.cartan .E6) := by
  rw [show Tag.cartan .E6 = Tag.cartanE 6 from rfl, cartanE_eq]
  exact ggIntCartan_E₆

private noncomputable def e6c3w_F :
    CoxeterMatrix.E₆.Group →* (↥e6c3w_hypMod ≃ₗ[ZMod 3] ↥e6c3w_hypMod) :=
  CoxeterMatrix.E₆.toCoxeterSystem.lift
    ⟨fun i => Module.reflection (e6c3w_hα i),
      isLiftable_reflection_of_intCartan e6c3w_intCartan_E6 e6c3w_h e6c3w_α
        e6c3w_hα e6c3w_hP⟩

private theorem e6c3w_F_injective : Function.Injective e6c3w_F :=
  ggCoxeterFaithful_of_E6_three e6c3w_intCartan_E6 e6c3w_h e6c3w_α e6c3w_hα e6c3w_hP

private theorem e6c3w_F_simple (i : Fin Tag.E6.rank) :
    e6c3w_F (CoxeterMatrix.E₆.simple i) = Module.reflection (e6c3w_hα i) := by
  unfold e6c3w_F
  rw [← CoxeterMatrix.toCoxeterSystem_simple]
  exact CoxeterSystem.lift_apply_simple CoxeterMatrix.E₆.toCoxeterSystem _ i

private noncomputable def e6c3w_adActLin (w : WeylGroup .E6) :
    ↥e6c3w_hypMod ≃ₗ[ZMod 3] ↥e6c3w_hypMod where
  toFun v := ⟨adAct .E6 3 w v.1, NoOffRest.adAct_mem_hypE6 w v.2⟩
  invFun v := ⟨adAct .E6 3 w⁻¹ v.1, NoOffRest.adAct_mem_hypE6 w⁻¹ v.2⟩
  left_inv v := Subtype.ext (by
    show adAct .E6 3 w⁻¹ (adAct .E6 3 w v.1) = v.1
    rw [← adAct_mul, inv_mul_cancel, adAct_one])
  right_inv v := Subtype.ext (by
    show adAct .E6 3 w (adAct .E6 3 w⁻¹ v.1) = v.1
    rw [← adAct_mul, mul_inv_cancel, adAct_one])
  map_add' v u := Subtype.ext (NoOffRest.adAct_add w v.1 u.1)
  map_smul' c v := Subtype.ext (TableBExc.E6Three.adAct_smul w c v.1)

private theorem e6c3w_adActLin_simple (i : Fin Tag.E6.rank) :
    e6c3w_adActLin (simple .E6 i) = Module.reflection (e6c3w_hα i) := by
  apply LinearEquiv.ext
  intro v
  apply Subtype.ext
  show adAct .E6 3 (simple .E6 i) v.1 = (Module.reflection (e6c3w_hα i) v).1
  rw [adAct_simple, Module.reflection_apply]
  rfl

private noncomputable def e6c3w_H :
    WeylGroup .E6 →* (↥e6c3w_hypMod ≃ₗ[ZMod 3] ↥e6c3w_hypMod) where
  toFun w := e6c3w_adActLin w
  map_one' := by
    apply LinearEquiv.ext
    intro v
    apply Subtype.ext
    show adAct .E6 3 1 v.1 = v.1
    rw [adAct_one]
  map_mul' w w' := by
    apply LinearEquiv.ext
    intro v
    apply Subtype.ext
    show adAct .E6 3 (w * w') v.1 = adAct .E6 3 w (adAct .E6 3 w' v.1)
    rw [adAct_mul]

private theorem e6c3w_H_eq :
    e6c3w_H = e6c3w_F.comp
      (ggE6Row_coxeterGroupEquiv.symm : WeylGroup .E6 →* CoxeterMatrix.E₆.Group) := by
  refine (CFSG.LieType.Chevalley.coxeterSystem .E6).ext_simple fun i => ?_
  simp only [MonoidHom.comp_apply]
  show e6c3w_adActLin (simple .E6 i) =
    e6c3w_F (ggE6Row_coxeterGroupEquiv.symm (simple .E6 i))
  have hs : ggE6Row_coxeterGroupEquiv.symm (simple .E6 i) =
      CoxeterMatrix.E₆.simple i :=
    (MulEquiv.symm_apply_eq _).mpr (ggE6Row_coxeterGroupEquiv_simple i).symm
  rw [hs, e6c3w_F_simple, e6c3w_adActLin_simple]

private theorem e6c3w_eq_one_of_adAct_eq_on_hypE6 {w : WeylGroup .E6}
    (h : ∀ x ∈ NoOffRest.hypE6, adAct .E6 3 w x = x) : w = 1 := by
  have hH : e6c3w_H w = 1 := by
    apply LinearEquiv.ext
    intro v
    apply Subtype.ext
    show adAct .E6 3 w v.1 = v.1
    exact h v.1 v.2
  have hF : e6c3w_F (ggE6Row_coxeterGroupEquiv.symm w) = 1 := by
    have h2 : (e6c3w_F.comp
        (ggE6Row_coxeterGroupEquiv.symm : WeylGroup .E6 →* CoxeterMatrix.E₆.Group)) w = 1 := by
      rw [← e6c3w_H_eq]
      exact hH
    exact h2
  have hv : ggE6Row_coxeterGroupEquiv.symm w = 1 :=
    e6c3w_F_injective (by rw [hF, map_one])
  have : w = 1 := by
    have h3 := congrArg ggE6Row_coxeterGroupEquiv hv
    simpa using h3
  exact this

theorem e6Three_exists_weylIso {G : Type} [Group G] [Finite G] {Bs X : Subgroup G}
    (cd : ↥Bs →* Multiplicative (Fin Tag.E6.rank → ZMod 3))
    (hrange : cd.range = ⊤ ∨ ∀ x, Multiplicative.ofAdd x ∈ cd.range ↔ x ∈ NoOffRest.hypE6)
    (hKer : ∀ n : ↥(X ⊓ Subgroup.normalizer (Bs : Set G)),
      (∀ b : ↥Bs, cd (ggTDρB X Bs n b) = cd b) → ggTDρB X Bs n = 1)
    (hnorm : ∀ n : ↥(X ⊓ Subgroup.normalizer (Bs : Set G)), ∃ u : WeylGroup Tag.E6,
      ∀ b : ↥Bs, cd (ggTDρB X Bs n b) =
        Multiplicative.ofAdd (adAct Tag.E6 3 u (Multiplicative.toAdd (cd b))))
    (nk : Fin 6 → ↥(X ⊓ Subgroup.normalizer (Bs : Set G)))
    (hnk : ∀ (k : Fin 6) (b : ↥Bs), cd (ggTDρB X Bs (nk k) b) =
      Multiplicative.ofAdd (adRefl Tag.E6 3 k (Multiplicative.toAdd (cd b)))) :
    ∃ (f : CoxeterMatrix.E₆.Group ≃* ↥(ggAutomizer X Bs))
      (κW : WeylGroup Tag.E6 ≃* CoxeterMatrix.E₆.Group),
      (∀ k, (f (CoxeterMatrix.E₆.simple k) : MulAut ↥Bs) = ggTDρB X Bs (nk k)) ∧
      (∀ j, κW (simple Tag.E6 j) = CoxeterMatrix.E₆.simple j) ∧
      (∀ (u : WeylGroup Tag.E6) (b : ↥Bs), cd ((f (κW u) : MulAut ↥Bs) b) =
        Multiplicative.ofAdd (adAct Tag.E6 3 u (Multiplicative.toAdd (cd b)))) ∧
      (∀ (n : ↥(X ⊓ Subgroup.normalizer (Bs : Set G))) (u : WeylGroup Tag.E6),
        (∀ b : ↥Bs, cd (ggTDρB X Bs n b) =
          Multiplicative.ofAdd (adAct Tag.E6 3 u (Multiplicative.toAdd (cd b)))) →
        ggTDρB X Bs n = (f (κW u) : MulAut ↥Bs)) ∧
      ggAutomizer X Bs = Subgroup.closure (Set.range fun k => ggTDρB X Bs (nk k)) := by
  classical
  have huniq : ∀ {t t' : ↥(ggAutomizer X Bs)},
      (∀ b : ↥Bs, cd ((t : MulAut ↥Bs) b) = cd ((t' : MulAut ↥Bs) b)) → t = t' := by
    intro t t' h
    obtain ⟨n, hn⟩ : ∃ n, ggTDρB X Bs n = (t : MulAut ↥Bs) := by
      have ht : (t : MulAut ↥Bs) ∈ (ggTDρB X Bs).range := by
        rw [ggTDρB_range]; exact t.2
      exact ht
    obtain ⟨n', hn'⟩ : ∃ n', ggTDρB X Bs n' = (t' : MulAut ↥Bs) := by
      have ht : (t' : MulAut ↥Bs) ∈ (ggTDρB X Bs).range := by
        rw [ggTDρB_range]; exact t'.2
      exact ht
    have hker : ggTDρB X Bs (n * n'⁻¹) = 1 := by
      apply hKer
      intro b
      calc cd (ggTDρB X Bs (n * n'⁻¹) b)
          = cd (ggTDρB X Bs n (ggTDρB X Bs n'⁻¹ b)) := by rw [map_mul]; rfl
        _ = cd (ggTDρB X Bs n' (ggTDρB X Bs n'⁻¹ b)) := by
              have h1 := h (ggTDρB X Bs n'⁻¹ b)
              simpa only [hn, hn'] using h1
        _ = cd (ggTDρB X Bs (n' * n'⁻¹) b) := by rw [map_mul]; rfl
        _ = cd b := by rw [mul_inv_cancel, map_one]; rfl
    have hnm : ggTDρB X Bs n = ggTDρB X Bs n' := by
      have h1 : ggTDρB X Bs n * (ggTDρB X Bs n')⁻¹ = 1 := by
        simpa only [map_mul, map_inv] using hker
      exact mul_inv_eq_one.mp h1
    exact Subtype.ext (by rw [← hn, ← hn', hnm])
  have hex : ∀ u : WeylGroup .E6, ∃ n : ↥(X ⊓ Subgroup.normalizer (Bs : Set G)),
      ∀ b : ↥Bs, cd (ggTDρB X Bs n b) =
        Multiplicative.ofAdd (adAct .E6 3 u (Multiplicative.toAdd (cd b))) := by
    intro u
    refine weyl_induction (fun u => ∃ n : ↥(X ⊓ Subgroup.normalizer (Bs : Set G)),
      ∀ b : ↥Bs, cd (ggTDρB X Bs n b) =
        Multiplicative.ofAdd (adAct .E6 3 u (Multiplicative.toAdd (cd b)))) ?_ ?_ u
    · exact ⟨1, fun b => by rw [map_one, MulAut.one_apply, adAct_one, ofAdd_toAdd]⟩
    · intro i w ih
      obtain ⟨n, hn⟩ := ih
      refine ⟨nk i * n, fun b => ?_⟩
      calc cd (ggTDρB X Bs (nk i * n) b)
          = cd (ggTDρB X Bs (nk i) (ggTDρB X Bs n b)) := by rw [map_mul]; rfl
        _ = Multiplicative.ofAdd
              (adRefl .E6 3 i (Multiplicative.toAdd (cd (ggTDρB X Bs n b)))) :=
              hnk i (ggTDρB X Bs n b)
        _ = Multiplicative.ofAdd
              (adRefl .E6 3 i (adAct .E6 3 w (Multiplicative.toAdd (cd b)))) := by
              rw [hn b, toAdd_ofAdd]
        _ = Multiplicative.ofAdd
              (adAct .E6 3 (simple .E6 i * w) (Multiplicative.toAdd (cd b))) := by
              rw [adAct_mul, adAct_simple]
  let nOf : WeylGroup .E6 → ↥(X ⊓ Subgroup.normalizer (Bs : Set G)) :=
    fun u => Classical.choose (hex u)
  have hnOf : ∀ (u : WeylGroup .E6) (b : ↥Bs),
      cd (ggTDρB X Bs (nOf u) b) =
        Multiplicative.ofAdd (adAct .E6 3 u (Multiplicative.toAdd (cd b))) :=
    fun u b => Classical.choose_spec (hex u) b
  let Fa : WeylGroup .E6 →* ↥(ggAutomizer X Bs) :=
    { toFun := fun u => ⟨ggTDρB X Bs (nOf u), by
        rw [← ggTDρB_range]; exact ⟨nOf u, rfl⟩⟩
      map_one' := by
        apply huniq
        intro b
        rw [hnOf 1 b, adAct_one, ofAdd_toAdd]
        simp
      map_mul' := fun u v => by
        apply huniq
        intro b
        simp only [Subgroup.coe_mul, MulAut.mul_apply]
        rw [hnOf (u * v) b, adAct_mul,
          hnOf u (ggTDρB X Bs (nOf v) b), hnOf v b]
        simp only [toAdd_ofAdd] }
  have hFa_simple : ∀ i : Fin 6,
      Fa (simple .E6 i) = (⟨ggTDρB X Bs (nk i), by
        rw [← ggTDρB_range]; exact ⟨nk i, rfl⟩⟩ : ↥(ggAutomizer X Bs)) := by
    intro i
    apply huniq
    intro b
    change cd (ggTDρB X Bs (nOf (simple .E6 i)) b) = cd (ggTDρB X Bs (nk i) b)
    rw [hnOf (simple .E6 i) b]
    have h1 : adAct .E6 3 (simple .E6 i) (Multiplicative.toAdd (cd b)) =
        adRefl .E6 3 i (Multiplicative.toAdd (cd b)) := adAct_simple (τ := .E6) (p := 3) i _
    rw [h1]
    exact (hnk i b).symm
  have hker_Fa : ∀ u : WeylGroup .E6, Fa u = 1 → u = 1 := by
    intro u hu
    apply e6c3w_eq_one_of_adAct_eq_on_hypE6
    intro x hx
    have hmem : Multiplicative.ofAdd x ∈ cd.range := by
      rcases hrange with htop | hiff
      · rw [htop]; exact Subgroup.mem_top _
      · exact (hiff x).mpr hx
    obtain ⟨b, hb⟩ := hmem
    have h1 : ggTDρB X Bs (nOf u) b = b := by
      have h2 := congrArg (fun t : ↥(ggAutomizer X Bs) => ((t : MulAut ↥Bs) b)) hu
      simpa [Fa] using h2
    have h3 : cd (ggTDρB X Bs (nOf u) b) = cd b := by rw [h1]
    rw [hnOf u b, hb, toAdd_ofAdd] at h3
    exact Multiplicative.ofAdd.injective h3
  have hinj : Function.Injective Fa := by
    intro u v huv
    have h1 : Fa (u * v⁻¹) = 1 := by
      rw [map_mul, huv, map_inv, mul_inv_cancel]
    have h2 : u * v⁻¹ = 1 := hker_Fa (u * v⁻¹) h1
    calc u = u * v⁻¹ * v := by group
      _ = 1 * v := by rw [h2]
      _ = v := by rw [one_mul]
  have hsurj : Function.Surjective Fa := by
    intro t
    obtain ⟨n, hn⟩ : ∃ n, ggTDρB X Bs n = (t : MulAut ↥Bs) := by
      have ht : (t : MulAut ↥Bs) ∈ (ggTDρB X Bs).range := by
        rw [ggTDρB_range]; exact t.2
      exact ht
    obtain ⟨u, hu⟩ := hnorm n
    refine ⟨u, ?_⟩
    apply huniq
    intro b
    change cd (ggTDρB X Bs (nOf u) b) = cd ((t : MulAut ↥Bs) b)
    rw [hnOf u b, ← hn]
    exact (hu b).symm
  let f0 : WeylGroup .E6 ≃* ↥(ggAutomizer X Bs) :=
    MulEquiv.ofBijective Fa ⟨hinj, hsurj⟩
  refine ⟨ggE6Row_coxeterGroupEquiv.trans f0, ggE6Row_coxeterGroupEquiv.symm,
    ?_, ?_, ?_, ?_, ?_⟩
  · intro k
    rw [MulEquiv.trans_apply, ggE6Row_coxeterGroupEquiv_simple]
    change ((f0 (simple .E6 k)) : MulAut ↥Bs) = ggTDρB X Bs (nk k)
    rw [show f0 (simple .E6 k) = Fa (simple .E6 k) from rfl, hFa_simple k]
  · intro j
    exact (MulEquiv.symm_apply_eq _).mpr (ggE6Row_coxeterGroupEquiv_simple j).symm
  · intro u b
    rw [MulEquiv.trans_apply, MulEquiv.apply_symm_apply]
    change cd (ggTDρB X Bs (nOf u) b) =
      Multiplicative.ofAdd (adAct .E6 3 u (Multiplicative.toAdd (cd b)))
    rw [hnOf u b]
  · intro n u hu
    have hFa : (Fa u : MulAut ↥Bs) = ggTDρB X Bs n := by
      have h1 : Fa u = (⟨ggTDρB X Bs n, by
          rw [← ggTDρB_range]; exact ⟨n, rfl⟩⟩ : ↥(ggAutomizer X Bs)) := by
        apply huniq
        intro b
        change cd (ggTDρB X Bs (nOf u) b) = cd (ggTDρB X Bs n b)
        rw [hnOf u b]
        exact (hu b).symm
      exact congrArg Subtype.val h1
    rw [MulEquiv.trans_apply, MulEquiv.apply_symm_apply]
    change ggTDρB X Bs n = (Fa u : MulAut ↥Bs)
    exact hFa.symm
  · apply le_antisymm
    · intro t ht
      obtain ⟨u, hu⟩ := hsurj ⟨t, ht⟩
      have hut : (Fa u : MulAut ↥Bs) = t := congrArg Subtype.val hu
      rw [← hut]
      refine weyl_induction (fun u => (Fa u : MulAut ↥Bs) ∈
        Subgroup.closure (Set.range fun k => ggTDρB X Bs (nk k))) ?_ ?_ u
      · rw [map_one]; exact Subgroup.one_mem _
      · intro i w ih
        have hmul : (Fa (simple .E6 i * w) : MulAut ↥Bs) =
            (Fa (simple .E6 i) : MulAut ↥Bs) * (Fa w : MulAut ↥Bs) := by
          rw [map_mul]; rfl
        rw [hmul]
        exact Subgroup.mul_mem _
          (by rw [hFa_simple i]; exact Subgroup.subset_closure ⟨i, rfl⟩) ih
    · rw [Subgroup.closure_le]
      rintro _ ⟨k, rfl⟩
      rw [← ggTDρB_range]
      exact ⟨nk k, rfl⟩

end CFSG.StandardType

end
