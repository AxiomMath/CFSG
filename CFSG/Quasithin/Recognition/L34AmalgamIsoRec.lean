module

public import CFSG.Quasithin.Recognition.L34AmalgamIsoA5

public section

namespace CFSG.Quasithin.L34Amalgam

open MulAction CFSG.ComponentClassification.WittDesign CFSG.Quasithin.Asc94 CFSG.CosetTable

abbrev barA1' : Subgroup ↥m22TwoStab := barA1.subgroupOf m22TwoStab

abbrev barC' : Subgroup ↥m22TwoStab := barC.subgroupOf m22TwoStab

instance barA1'_normal :
    barA1'.Normal :=
  ⟨fun n hn g => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    exact conj_mem_barA1 g.2 hn⟩

theorem card_barA1' : Nat.card barA1' = 16 := by
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe barA1_le_two).toEquiv, card_barA1]

theorem card_barC' : Nat.card barC' = 60 := by
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe barC_le_two).toEquiv, card_barC]

theorem isComplement'_P1 :
    barA1'.IsComplement' barC' := by
  refine Subgroup.isComplement'_of_card_mul_and_disjoint
    (by rw [card_barA1', card_barC', card_m22TwoStab]) ?_
  rw [Subgroup.disjoint_def]
  intro x hxA hxC
  have h : (x : M22) ∈ barA1 ⊓ barC := ⟨hxA, hxC⟩
  rw [barA1_inf_barC, Subgroup.mem_bot] at h
  exact Subtype.ext h

@[expose] def refa'
    : ↥m22TwoStab := ⟨refa, mem_m22TwoStab_iff.mpr ⟨ref_facts.1, ref_facts.2.1⟩⟩

@[expose] def refb' : ↥m22TwoStab :=
  ⟨refb, mem_m22TwoStab_iff.mpr ⟨ref_facts.2.2.1, ref_facts.2.2.2.1⟩⟩

@[expose] def crd'
    (x : Fin 16) : ↥m22TwoStab := ⟨crd x, barA1_le_two ⟨x, rfl⟩⟩

theorem closure_ref' : Subgroup.closure {refa', refb'} = barC' := by
  apply Subgroup.map_injective m22TwoStab.subtype_injective
  rw [MonoidHom.map_closure, Subgroup.map_subgroupOf_eq_of_le barC_le_two]
  have : (m22TwoStab.subtype '' {refa', refb'}) = {refa, refb} := by
    ext g
    simp [refa', refb']
  rw [this]
  rfl

theorem refa'_mul
    : refa' * refa' = 1 := Subtype.ext ref_facts.2.2.2.2.1

theorem refb'_pow : refb' ^ 3 = 1 := Subtype.ext (by
  rw [Subgroup.coe_pow]; exact ref_facts.2.2.2.2.2.1)

theorem refab'_pow : (refa' * refb') ^ 5 = 1 := Subtype.ext (by
  rw [Subgroup.coe_pow, Subgroup.coe_mul]; exact ref_facts.2.2.2.2.2.2)

@[expose] noncomputable def a5EquivRef
    : PG 2 a5Rels ≃* barC' :=
  a5Equiv refa'_mul refb'_pow refab'_pow closure_ref' card_barC'

section Abstract

variable {X : Type*} [Group X] {E C : Subgroup X} [hEn : E.Normal]

@[expose] def conjE (c : X) (e : ↥E) : ↥E := ⟨c * e * c⁻¹, hEn.conj_mem _ e.2 c⟩

theorem conjE_mul (c : X) (e e' : ↥E) : conjE c (e * e') = conjE c e * conjE c e' :=
  Subtype.ext (by simp [conjE, mul_assoc])

theorem conjE_conjE (c d : X) (e : ↥E) : conjE c (conjE d e) = conjE (c * d) e :=
  Subtype.ext (by simp [conjE, mul_assoc])

theorem conjE_one (e : ↥E) : conjE 1 e = e := Subtype.ext (by simp [conjE])

variable (η : ↥E ≃* Multiplicative (Fin 4 → ZMod 2))

@[expose] noncomputable def actBits (c : X) (x : Fin 16) : Fin 16 :=
  bitDecode η (conjE c (bitCoord η x))

theorem actBits_bxor (c : X) (x y : Fin 16) :
    actBits η c (bxor x y) = bxor (actBits η c x) (actBits η c y) := by
  rw [actBits, actBits, actBits, bitCoord_bxor, conjE_mul, bitDecode_mul]

@[expose] noncomputable def matOf (c : X) : Fin 4 → Fin 16 := fun i => actBits η c (basisVec i)

theorem actBits_eq_lin (c : X) (x : Fin 16) : actBits η c x = lin (matOf η c) x :=
  additive_eq_lin _ (actBits_bxor η c) x

theorem actBits_mul (c d : X) (x : Fin 16) : actBits η (c * d) x = actBits η c (actBits η d x) := by
  rw [actBits, actBits, actBits, bitCoord_bitDecode, conjE_conjE]

theorem actBits_one (x : Fin 16) : actBits η 1 x = x := by
  rw [actBits, conjE_one, bitDecode_bitCoord]

theorem actBits_pow (c : X) (n : ℕ) (x : Fin 16) : actBits η (c ^ n) x = (actBits η c)^[n] x := by
  induction n generalizing x with
  | zero => rw [pow_zero, actBits_one, Function.iterate_zero, id]
  | succ n ih => rw [pow_succ, actBits_mul, ih, Function.iterate_succ_apply]

end Abstract

theorem exists_mulEquiv_P1
    {X : Type*} [Group X] [Finite X] {E C : Subgroup X} [hEn : E.Normal]
    (hEab : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x) (hE2 : ∀ x ∈ E, x * x = 1) (hEc : Nat.card E = 16)
    (hCE : E ⊓ C = ⊥) (hCc : Nat.card C = 60) (hX : Nat.card X = 960)
    {a b : X} (hC : Subgroup.closure {a, b} = C)
    (ha : a * a = 1) (hb : b ^ 3 = 1) (hab : (a * b) ^ 5 = 1)
    (hfpf : ∀ e ∈ E, b * e = e * b → e = 1) :
    ∃ ψ : ↥m22TwoStab ≃* X, (∀ x : Fin 16, (ψ (crd' x)) ∈ E) ∧
      (∀ e ∈ E, ∃ x : Fin 16, ψ (crd' x) = e) ∧ ψ refa' = a ∧ ψ refb' = b := by
  classical
  obtain ⟨η⟩ := CFSG.SectionRank.Ccomm.nonempty_mulEquiv_of_elementary (p := 2) (n := 4)
    (W := ↥E) (fun x y => Subtype.ext (hEab x x.2 y y.2))
    (fun x => Subtype.ext (by rw [Subgroup.coe_pow, sq, hE2 x x.2]; rfl))
    (by rw [hEc]; norm_num)
  set u := matOf η a with hu
  set v := matOf η b with hv
  have hlin : ∀ (c : X) (x : Fin 16), actBits η c x = lin (matOf η c) x :=
    fun c x => actBits_eq_lin η c x
  have hu2 : ∀ x, lin u (lin u x) = x := by
    intro x
    rw [hu, ← hlin, ← hlin, ← actBits_mul, ha, actBits_one]
  have hv3 : ∀ x, lin v (lin v (lin v x)) = x := by
    intro x
    rw [hv, ← hlin, ← hlin, ← hlin, ← actBits_mul, ← actBits_mul, ← pow_two,
      show b ^ 2 * b = b ^ 3 by group, hb, actBits_one]
  have hvf : ∀ x, x ≠ 0 → lin v x ≠ x := by
    intro x hx h
    apply hx
    rw [hv, ← hlin] at h
    have h1 : conjE b (bitCoord η x) = bitCoord η x := by
      rw [← bitCoord_bitDecode η (conjE b (bitCoord η x))]
      exact congrArg (bitCoord η) h
    have h2 : b * ((bitCoord η x : ↥E) : X) = ((bitCoord η x : ↥E) : X) * b := by
      have := congrArg Subtype.val h1
      simp only [conjE] at this
      calc b * ((bitCoord η x : ↥E) : X) = b * ((bitCoord η x : ↥E) : X) * b⁻¹ * b := by group
        _ = _ := by rw [this]
    have h3 := hfpf _ (bitCoord η x).2 h2
    have h4 : bitCoord η x = bitCoord η 0 := by
      rw [bitCoord_zero]; exact Subtype.ext h3
    exact bitCoord_injective η h4
  have h5 : ∀ x, (lin u ∘ lin v)^[5] x = x := by
    intro x
    have hcomp : (lin u ∘ lin v) = actBits η (a * b) := by
      funext y
      rw [Function.comp_apply, hu, hv, ← hlin, ← hlin, ← actBits_mul]
    rw [hcomp, ← actBits_pow, hab, actBits_one]
  obtain ⟨w, hTinj, hTA, hTB⟩ := module_unique u hu2 v hv3 hvf h5
  set T := conjMap u v w with hT
  obtain ⟨τ, hτ⟩ : ∃ τ : Fin 16 → ↥E, ∀ x, τ x = bitCoord η (lin T x) := ⟨_, fun _ => rfl⟩
  have τ_inj : Function.Injective τ := fun x y h => by
    rw [hτ, hτ] at h
    exact hTinj x y (bitCoord_injective η h)
  have τ_surj : Function.Surjective τ :=
    (τ_inj.bijective_of_nat_card_le (by rw [hEc, Nat.card_eq_fintype_card, Fintype.card_fin])).2
  have τ_mul : ∀ x y, τ (bxor x y) = τ x * τ y := fun x y => by
    rw [hτ, hτ, hτ, lin_bxor, bitCoord_bxor]
  have crd'_mem : ∀ x, crd' x ∈ barA1' := fun x => Subgroup.mem_subgroupOf.mpr ⟨x, rfl⟩
  obtain ⟨crdE, hcrdE⟩ : ∃ crdE : Fin 16 ≃ ↥barA1',
      ∀ x, ((crdE x : ↥barA1') : ↥m22TwoStab) = crd' x :=
    ⟨Equiv.ofBijective (fun x => ⟨crd' x, crd'_mem x⟩)
      ⟨fun x y h => crd_injective (congrArg (fun z : ↥barA1' => ((z : ↥m22TwoStab) : M22)) h),
        fun n => by
          obtain ⟨x, hx⟩ := Subgroup.mem_subgroupOf.mp n.2
          exact ⟨x, Subtype.ext (Subtype.ext hx)⟩⟩, fun _ => rfl⟩
  have crdE_mul : ∀ x y, crdE x * crdE y = crdE (bxor x y) := fun x y => by
    apply Subtype.ext; apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, hcrdE, hcrdE, hcrdE]
    exact (crd_mul x y).symm
  obtain ⟨fn, hfn⟩ : ∃ fn : ↥barA1' ≃* ↥E, ∀ x, fn (crdE x) = τ x :=
    ⟨{ crdE.symm.trans (Equiv.ofBijective τ ⟨τ_inj, τ_surj⟩) with
        map_mul' := fun n m => by
          obtain ⟨x, rfl⟩ := crdE.surjective n
          obtain ⟨y, rfl⟩ := crdE.surjective m
          simp only [Equiv.toFun_as_coe, Equiv.trans_apply]
          rw [crdE_mul, Equiv.symm_apply_apply, Equiv.symm_apply_apply, Equiv.symm_apply_apply]
          exact τ_mul x y }, fun x => by
      show (Equiv.ofBijective τ ⟨τ_inj, τ_surj⟩) (crdE.symm (crdE x)) = τ x
      rw [Equiv.symm_apply_apply]
      rfl⟩
  have hrefa_mem : refa' ∈ barC' := closure_ref' ▸ Subgroup.subset_closure (Set.mem_insert _ _)
  have hrefb_mem : refb' ∈ barC' :=
    closure_ref' ▸ Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
  obtain ⟨fg, fg_a, fg_b⟩ : ∃ fg : ↥barC' ≃* ↥C, ((fg ⟨refa', hrefa_mem⟩ : ↥C) : X) = a ∧
      ((fg ⟨refb', hrefb_mem⟩ : ↥C) : X) = b := by
    refine ⟨a5EquivRef.symm.trans (a5Equiv ha hb hab hC hCc), ?_, ?_⟩
    · have h1 : a5EquivRef (PresentedGroup.of 0) = ⟨refa', hrefa_mem⟩ :=
        Subtype.ext (a5Equiv_of refa'_mul refb'_pow refab'_pow closure_ref' card_barC' 0)
      rw [MulEquiv.trans_apply, ← h1, MulEquiv.symm_apply_apply, a5Equiv_of]
      rfl
    · have h1 : a5EquivRef (PresentedGroup.of 1) = ⟨refb', hrefb_mem⟩ :=
        Subtype.ext (a5Equiv_of refa'_mul refb'_pow refab'_pow closure_ref' card_barC' 1)
      rw [MulEquiv.trans_apply, ← h1, MulEquiv.symm_apply_apply, a5Equiv_of]
      rfl
  have hconjA : ∀ (g : ↥m22TwoStab) (n : ↥barA1'), g * (n : ↥m22TwoStab) * g⁻¹ ∈ barA1' :=
    fun g n => (barA1'_normal).conj_mem _ n.2 g
  have hτ_conj : ∀ (c : X) (M : Fin 4 → Fin 16), (∀ x, lin T (lin M x) =
      lin (matOf η c) (lin T x)) → ∀ x, ((τ (lin M x) : ↥E) : X) = c * (τ x : X) * c⁻¹ := by
    intro c M hM x
    rw [hτ, hτ, hM, ← hlin, actBits, bitCoord_bitDecode]
    rfl
  have hP : ∀ g : ↥m22TwoStab, g ∈ Subgroup.closure {refa', refb'} → ∀ (hg : g ∈ barC')
      (n : ↥barA1'), ((fn ⟨g * n * g⁻¹, hconjA g n⟩ : ↥E) : X) =
        (fg ⟨g, hg⟩ : X) * (fn n : X) * ((fg ⟨g, hg⟩ : ↥C) : X)⁻¹ := by
    intro g hgcl
    induction hgcl using Subgroup.closure_induction with
    | mem x hx =>
      intro hg n
      obtain ⟨y, rfl⟩ := crdE.surjective n
      rcases hx with rfl | rfl
      · have hy : ((crdE y : ↥m22TwoStab) : M22) = crd y := by rw [hcrdE]; rfl
        have hy' : ((crdE (lin refA y) : ↥m22TwoStab) : M22) = crd (lin refA y) := by
          rw [hcrdE]; rfl
        have e1 : (⟨refa' * (crdE y : ↥m22TwoStab) * refa'⁻¹, hconjA _ _⟩ : ↥barA1') =
            crdE (lin refA y) := by
          apply Subtype.ext; apply Subtype.ext
          show refa * ((crdE y : ↥m22TwoStab) : M22) * refa⁻¹ = _
          rw [hy, hy']
          exact crd_conj_a y
        rw [e1, hfn, hfn, fg_a]
        exact hτ_conj a refA hTA y
      · have hy : ((crdE y : ↥m22TwoStab) : M22) = crd y := by rw [hcrdE]; rfl
        have hy' : ((crdE (lin refB y) : ↥m22TwoStab) : M22) = crd (lin refB y) := by
          rw [hcrdE]; rfl
        have e1 : (⟨refb' * (crdE y : ↥m22TwoStab) * refb'⁻¹, hconjA _ _⟩ : ↥barA1') =
            crdE (lin refB y) := by
          apply Subtype.ext; apply Subtype.ext
          show refb * ((crdE y : ↥m22TwoStab) : M22) * refb⁻¹ = _
          rw [hy, hy']
          exact crd_conj_b y
        rw [e1, hfn, hfn, fg_b]
        exact hτ_conj b refB hTB y
    | one =>
      intro hg n
      have e1 : (⟨1 * (n : ↥m22TwoStab) * 1⁻¹, hconjA 1 n⟩ : ↥barA1') = n :=
        Subtype.ext (by simp)
      have e2 : (⟨1, hg⟩ : ↥barC') = 1 := rfl
      rw [e1, e2, map_one]
      simp
    | mul x y hx hy ihx ihy =>
      intro hxy n
      have hxC : x ∈ barC' := by rw [← closure_ref']; exact hx
      have hyC : y ∈ barC' := by rw [← closure_ref']; exact hy
      have e1 : (⟨x * y * (n : ↥m22TwoStab) * (x * y)⁻¹, hconjA _ n⟩ : ↥barA1') =
          ⟨x * ((⟨y * n * y⁻¹, hconjA y n⟩ : ↥barA1') : ↥m22TwoStab) * x⁻¹, hconjA _ _⟩ :=
        Subtype.ext (by group)
      have e2 : (⟨x * y, hxy⟩ : ↥barC') = ⟨x, hxC⟩ * ⟨y, hyC⟩ := rfl
      rw [e1, ihx hxC, ihy hyC, e2, map_mul, Subgroup.coe_mul, mul_inv_rev]
      group
    | inv x hx ihx =>
      intro hxi n
      have hxC : x ∈ barC' := by rw [← closure_ref']; exact hx
      have key := ihx hxC ⟨x⁻¹ * n * x⁻¹⁻¹, hconjA x⁻¹ n⟩
      have e1 : (⟨x * ((⟨x⁻¹ * n * x⁻¹⁻¹, hconjA x⁻¹ n⟩ : ↥barA1') : ↥m22TwoStab) * x⁻¹,
          hconjA _ _⟩ : ↥barA1') = n := Subtype.ext (by group)
      rw [e1] at key
      have e2 : (⟨x⁻¹, hxi⟩ : ↥barC') = (⟨x, hxC⟩ : ↥barC')⁻¹ := rfl
      rw [e2, map_inv, Subgroup.coe_inv, key]
      group
  have hcomplX : E.IsComplement' C := by
    refine Subgroup.isComplement'_of_card_mul_and_disjoint (by rw [hEc, hCc, hX]) ?_
    rw [Subgroup.disjoint_def]
    intro x hxE hxC
    have h : x ∈ E ⊓ C := ⟨hxE, hxC⟩
    rwa [hCE, Subgroup.mem_bot] at h
  obtain ⟨ψ, hψA, hψC⟩ : ∃ ψ : ↥m22TwoStab ≃* X, (∀ n : ↥barA1', ψ n = (fn n : X)) ∧
      ∀ g : ↥barC', ψ g = (fg g : X) := by
    have hh : ∀ g : ↥barC', ((barA1'.normalizerMonoidHom).comp
        (Subgroup.inclusion (barA1'.normalizer_eq_top ▸ le_top)) g).trans fn =
        fn.trans ((E.normalizerMonoidHom).comp
          (Subgroup.inclusion (E.normalizer_eq_top ▸ le_top)) (fg g)) := by
      intro g
      ext n
      exact hP g (by rw [closure_ref']; exact g.2) g.2 n
    refine ⟨(SemidirectProduct.mulEquivSubgroup isComplement'_P1).symm.trans
      ((SemidirectProduct.congr fn fg hh).trans (SemidirectProduct.mulEquivSubgroup hcomplX)),
      fun n => ?_, fun g => ?_⟩
    · have h1 : SemidirectProduct.mulEquivSubgroup isComplement'_P1 (SemidirectProduct.inl n) =
          (n : ↥m22TwoStab) := by
        simp [SemidirectProduct.mulEquivSubgroup_apply]
      rw [MulEquiv.trans_apply, ← h1, MulEquiv.symm_apply_apply, MulEquiv.trans_apply]
      simp [SemidirectProduct.mulEquivSubgroup_apply]
    · have h1 : SemidirectProduct.mulEquivSubgroup isComplement'_P1 (SemidirectProduct.inr g) =
          (g : ↥m22TwoStab) := by
        simp [SemidirectProduct.mulEquivSubgroup_apply]
      rw [MulEquiv.trans_apply, ← h1, MulEquiv.symm_apply_apply, MulEquiv.trans_apply]
      simp [SemidirectProduct.mulEquivSubgroup_apply]
  refine ⟨ψ, fun x => ?_, fun e he => ?_, ?_, ?_⟩
  · rw [← hcrdE, hψA]
    exact (fn _).2
  · obtain ⟨n, hn⟩ := fn.surjective ⟨e, he⟩
    obtain ⟨x, rfl⟩ := crdE.surjective n
    refine ⟨x, ?_⟩
    rw [← hcrdE, hψA, hn]
  · rw [show refa' = ((⟨refa', hrefa_mem⟩ : ↥barC') : ↥m22TwoStab) from rfl, hψC, fg_a]
  · rw [show refb' = ((⟨refb', hrefb_mem⟩ : ↥barC') : ↥m22TwoStab) from rfl, hψC, fg_b]

end CFSG.Quasithin.L34Amalgam
