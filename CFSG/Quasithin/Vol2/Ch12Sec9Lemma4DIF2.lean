module

public import CFSG.Quasithin.Vol2.Ch12Sec9Lemma4DIF1Stab

public section

namespace CFSG.Quasithin.H13.C1294

open Module

variable {I : Type} [AddCommGroup I] [Module (ZMod 2) I] [Module.Finite (ZMod 2) I]

section Basic

theorem eq_of_smul_eq_smul_zmod2 {p0 : I} (hp0 : p0 ≠ 0) {a b : ZMod 2} (h : a • p0 = b • p0) :
    a = b := by
  have h' : (a - b) • p0 = 0 := by rw [sub_smul, h, sub_self]
  rcases smul_eq_zero.1 h' with h'' | h''
  · exact sub_eq_zero.1 h''
  · exact absurd h'' hp0

theorem exists_span_singleton_eq {p : Submodule (ZMod 2) I} (hp : finrank (ZMod 2) p = 1) :
    ∃ p0 : I, p0 ≠ 0 ∧ p = Submodule.span (ZMod 2) {p0} := by
  have hne : p ≠ ⊥ := by
    intro h
    rw [h, finrank_bot] at hp
    exact zero_ne_one hp
  obtain ⟨x, hxp, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  refine ⟨x, hx0, ?_⟩
  symm
  apply Submodule.eq_of_le_of_finrank_eq
  · rw [Submodule.span_le, Set.singleton_subset_iff]
    exact hxp
  · rw [finrank_span_singleton hx0, hp]

theorem natCard_submodule_eq {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    (W : Submodule (ZMod 2) V) : Nat.card W = 2 ^ finrank (ZMod 2) W := by
  haveI : Fintype W := Fintype.ofFinite W
  rw [Nat.card_eq_fintype_card, Module.card_eq_pow_finrank (K := ZMod 2) (V := W)]
  rfl

theorem mem_unipRad_iff' (W : Submodule (ZMod 2) I) (g : I ≃ₗ[ZMod 2] I) :
    g ∈ unipRad W ↔ (∀ w ∈ W, g w = w) ∧ ∀ x, g x - x ∈ W :=
  Iff.rfl

theorem mem_D0p_iff {p ℓ : Submodule (ZMod 2) I} (hpℓ : p ≤ ℓ) (g : I ≃ₗ[ZMod 2] I) :
    g ∈ D0p p ℓ ↔ (∀ v ∈ ℓ, g v = v) ∧ ∀ x, g x - x ∈ p := by
  unfold D0p
  rw [pCoreOf_two_stabS, pCoreOf_two_stabS, Subgroup.mem_inf, mem_unipRad_iff', mem_unipRad_iff']
  constructor
  · rintro ⟨⟨_, h2⟩, ⟨h3, _⟩⟩
    exact ⟨h3, h2⟩
  · rintro ⟨h3, h2⟩
    exact ⟨⟨fun w hw => h3 w (hpℓ hw), h2⟩, ⟨h3, fun x => hpℓ (h2 x)⟩⟩

theorem mem_D0P_iff {ℓ Pl : Submodule (ZMod 2) I} (hℓPl : ℓ ≤ Pl) (g : I ≃ₗ[ZMod 2] I) :
    g ∈ D0P ℓ Pl ↔ (∀ v ∈ Pl, g v = v) ∧ ∀ x, g x - x ∈ ℓ := by
  unfold D0P
  rw [pCoreOf_two_stabS, pCoreOf_two_stabS, Subgroup.mem_inf, mem_unipRad_iff', mem_unipRad_iff']
  constructor
  · rintro ⟨⟨h1, _⟩, ⟨_, h4⟩⟩
    exact ⟨h1, h4⟩
  · rintro ⟨h1, h4⟩
    exact ⟨⟨h1, fun x => hℓPl (h4 x)⟩, ⟨fun w hw => h1 w (hℓPl hw), h4⟩⟩

end Basic

section CountD0p

variable [Finite I]

theorem natCard_forms_vanishing (hI : finrank (ZMod 2) I = 4) {ℓ : Submodule (ZMod 2) I}
    (hℓ : finrank (ZMod 2) ℓ = 2) :
    Nat.card {φ : I →ₗ[ZMod 2] ZMod 2 // ∀ v ∈ ℓ, φ v = 0} = 4 := by
  obtain ⟨C, hC⟩ := Submodule.exists_isCompl ℓ
  have hCd : finrank (ZMod 2) C = 2 := by
    have h := Submodule.finrank_add_eq_of_isCompl hC
    omega
  haveI : Module.Finite (ZMod 2) C := Module.finite_of_finrank_pos (by omega)
  let b := Module.finBasisOfFinrankEq (ZMod 2) C hCd
  let π : I →ₗ[ZMod 2] C := C.projectionOnto ℓ hC.symm
  have hπC : ∀ c : C, π (c : I) = c := fun c => Submodule.projectionOnto_apply_left hC.symm c
  have hπℓ : ∀ v ∈ ℓ, π v = 0 := fun v hv =>
    (Submodule.projectionOnto_apply_eq_zero_iff hC.symm).2 hv
  have hsub : ∀ x : I, x - ((π x : C) : I) ∈ ℓ := by
    intro x
    apply (Submodule.projectionOnto_apply_eq_zero_iff hC.symm).1
    rw [map_sub, hπC, sub_self]
  let e1 : {φ : I →ₗ[ZMod 2] ZMod 2 // ∀ v ∈ ℓ, φ v = 0} ≃ (C →ₗ[ZMod 2] ZMod 2) :=
    { toFun := fun φ => φ.1.comp C.subtype
      invFun := fun ψ => ⟨ψ.comp π, fun v hv => by
        show ψ (π v) = 0
        rw [hπℓ v hv, map_zero]⟩
      left_inv := fun φ => Subtype.ext (LinearMap.ext fun x => by
        show φ.1 ((π x : C) : I) = φ.1 x
        have h0 := φ.2 _ (hsub x)
        calc φ.1 ((π x : C) : I) = φ.1 (x - ((π x : C) : I)) + φ.1 ((π x : C) : I) := by
              rw [h0, zero_add]
          _ = φ.1 x := by rw [← map_add, sub_add_cancel])
      right_inv := fun ψ => LinearMap.ext fun c => by
        show ψ (π (c : I)) = ψ c
        rw [hπC] }
  have e2 : (C →ₗ[ZMod 2] ZMod 2) ≃ (Fin 2 → ZMod 2) := (b.constr (ZMod 2)).symm.toEquiv
  rw [Nat.card_congr (e1.trans e2), Nat.card_fun, Nat.card_eq_fintype_card (α := ZMod 2),
    ZMod.card, Nat.card_eq_fintype_card (α := Fin 2), Fintype.card_fin]
  norm_num

theorem card_D0p (hI : finrank (ZMod 2) I = 4) {p ℓ : Submodule (ZMod 2) I}
    (hp : finrank (ZMod 2) p = 1) (hℓ : finrank (ZMod 2) ℓ = 2) (hpℓ : p ≤ ℓ) :
    Nat.card (D0p p ℓ) = 4 := by
  obtain ⟨p0, hp0, rfl⟩ := exists_span_singleton_eq hp
  have hp0ℓ : p0 ∈ ℓ := hpℓ (Submodule.mem_span_singleton_self p0)
  let Φ : {φ : I →ₗ[ZMod 2] ZMod 2 // ∀ v ∈ ℓ, φ v = 0} → D0p (Submodule.span (ZMod 2) {p0}) ℓ :=
    fun φ => ⟨LinearEquiv.transvection (f := φ.1) (v := p0) (φ.2 p0 hp0ℓ), by
      rw [mem_D0p_iff hpℓ]
      refine ⟨fun v hv => ?_, fun x => ?_⟩
      · show v + φ.1 v • p0 = v
        rw [φ.2 v hv, zero_smul, add_zero]
      · show x + φ.1 x • p0 - x ∈ _
        rw [add_sub_cancel_left]
        exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self p0)⟩
  have hinj : Function.Injective Φ := by
    intro φ ψ h
    have hh := congrArg Subtype.val h
    have h' : ∀ x, φ.1 x • p0 = ψ.1 x • p0 := by
      intro x
      have h3 : x + φ.1 x • p0 = x + ψ.1 x • p0 := congrArg (fun e : I ≃ₗ[ZMod 2] I => e x) hh
      exact add_left_cancel h3
    exact Subtype.ext (LinearMap.ext fun x => eq_of_smul_eq_smul_zmod2 hp0 (h' x))
  have hsurj : Function.Surjective Φ := by
    rintro ⟨g, hg⟩
    obtain ⟨h1, h2⟩ := (mem_D0p_iff hpℓ g).1 hg
    have hcx : ∀ x : I, ∃ c : ZMod 2, c • p0 = g x - x := fun x =>
      Submodule.mem_span_singleton.1 (h2 x)
    choose c hc using hcx
    let φ : I →ₗ[ZMod 2] ZMod 2 :=
      { toFun := c
        map_add' := fun x y => by
          apply eq_of_smul_eq_smul_zmod2 hp0
          show c (x + y) • p0 = (c x + c y) • p0
          rw [add_smul, hc, hc, hc, map_add]
          abel
        map_smul' := fun a x => by
          apply eq_of_smul_eq_smul_zmod2 hp0
          show c (a • x) • p0 = (a * c x) • p0
          rw [mul_smul, hc, hc, map_smul, smul_sub] }
    have hφℓ : ∀ v ∈ ℓ, φ v = 0 := by
      intro v hv
      have h := hc v
      rw [h1 v hv, sub_self] at h
      rcases smul_eq_zero.1 h with h' | h'
      · exact h'
      · exact absurd h' hp0
    refine ⟨⟨φ, hφℓ⟩, Subtype.ext (LinearEquiv.ext fun x => ?_)⟩
    show x + c x • p0 = g x
    rw [hc x]
    abel
  exact (Nat.card_congr (Equiv.ofBijective Φ ⟨hinj, hsurj⟩)).symm.trans
    (natCard_forms_vanishing hI hℓ)

theorem card_D0P (hI : finrank (ZMod 2) I = 4) {ℓ Pl : Submodule (ZMod 2) I}
    (hℓ : finrank (ZMod 2) ℓ = 2) (hPl : finrank (ZMod 2) Pl = 3) (hℓPl : ℓ ≤ Pl) :
    Nat.card (D0P ℓ Pl) = 4 := by
  obtain ⟨C', hC'⟩ := Submodule.exists_isCompl Pl
  have hC'd : finrank (ZMod 2) C' = 1 := by
    have h := Submodule.finrank_add_eq_of_isCompl hC'
    omega
  obtain ⟨x0, hx0, hC'eq⟩ := exists_span_singleton_eq hC'd
  have hx0C : x0 ∈ C' := hC'eq ▸ Submodule.mem_span_singleton_self x0
  let π : I →ₗ[ZMod 2] C' := C'.projectionOnto Pl hC'.symm
  have hπC : ∀ c : C', π (c : I) = c := fun c => Submodule.projectionOnto_apply_left hC'.symm c
  have hπPl : ∀ w ∈ Pl, π w = 0 := fun w hw =>
    (Submodule.projectionOnto_apply_eq_zero_iff hC'.symm).2 hw
  have hcoef : ∀ x : I, ∃ a : ZMod 2, a • x0 = ((π x : C') : I) := fun x => by
    have hmem : ((π x : C') : I) ∈ Submodule.span (ZMod 2) {x0} := by
      rw [← hC'eq]
      exact (π x).2
    exact Submodule.mem_span_singleton.1 hmem
  choose lam hlam using hcoef
  let f : I →ₗ[ZMod 2] ZMod 2 :=
    { toFun := lam
      map_add' := fun x y => by
        apply eq_of_smul_eq_smul_zmod2 hx0
        show lam (x + y) • x0 = (lam x + lam y) • x0
        rw [hlam (x + y), add_smul, hlam x, hlam y, map_add, Submodule.coe_add]
      map_smul' := fun a x => by
        apply eq_of_smul_eq_smul_zmod2 hx0
        show lam (a • x) • x0 = (a * lam x) • x0
        rw [hlam (a • x), mul_smul, hlam x, map_smul, Submodule.coe_smul] }
  have hpx0 : π x0 = ⟨x0, hx0C⟩ := hπC ⟨x0, hx0C⟩
  have hf1 : f x0 = 1 := by
    apply eq_of_smul_eq_smul_zmod2 hx0
    rw [one_smul]
    show lam x0 • x0 = x0
    rw [hlam x0, hpx0]
  have hkill : ∀ w ∈ Pl, f w = 0 := by
    intro w hw
    have h := hlam w
    rw [hπPl w hw, Submodule.coe_zero] at h
    have h' : lam w • x0 = 0 := h
    rcases smul_eq_zero.1 h' with h'' | h''
    · exact h''
    · exact absurd h'' hx0
  have hker : ∀ y, f y = 0 → y ∈ Pl := by
    intro y hy
    apply (Submodule.projectionOnto_apply_eq_zero_iff hC'.symm).1
    apply Subtype.ext
    have h := hlam y
    have hy' : lam y = 0 := hy
    rw [hy', zero_smul] at h
    rw [Submodule.coe_zero] at *
    exact h.symm
  have hrest : ∀ x : I, x - f x • x0 ∈ Pl := by
    intro x
    apply (Submodule.projectionOnto_apply_eq_zero_iff hC'.symm).1
    apply Subtype.ext
    show ((π (x - lam x • x0) : C') : I) = 0
    rw [map_sub, map_smul, hpx0, Submodule.coe_sub, Submodule.coe_smul, hlam x, sub_self]
  let Φ : ℓ → D0P ℓ Pl := fun a =>
    ⟨LinearEquiv.transvection (f := f) (v := a.1) (hkill a.1 (hℓPl a.2)), by
      rw [mem_D0P_iff hℓPl]
      refine ⟨fun v hv => ?_, fun x => ?_⟩
      · show v + f v • a.1 = v
        rw [hkill v hv, zero_smul, add_zero]
      · show x + f x • a.1 - x ∈ ℓ
        rw [add_sub_cancel_left]
        exact Submodule.smul_mem _ _ a.2⟩
  have hinj : Function.Injective Φ := by
    intro a b h
    have hh := congrArg Subtype.val h
    have h3 : x0 + f x0 • a.1 = x0 + f x0 • b.1 :=
      congrArg (fun e : I ≃ₗ[ZMod 2] I => e x0) hh
    rw [hf1, one_smul, one_smul] at h3
    exact Subtype.ext (add_left_cancel h3)
  have hsurj : Function.Surjective Φ := by
    rintro ⟨g, hg⟩
    obtain ⟨h1, h2⟩ := (mem_D0P_iff hℓPl g).1 hg
    refine ⟨⟨g x0 - x0, h2 x0⟩, Subtype.ext (LinearEquiv.ext fun x => ?_)⟩
    show x + f x • (g x0 - x0) = g x
    have hdec : g x = g (f x • x0 + (x - f x • x0)) := congrArg g (by abel)
    rw [hdec, map_add, map_smul, h1 _ (hrest x), smul_sub]
    abel
  exact (Nat.card_congr (Equiv.ofBijective Φ ⟨hinj, hsurj⟩)).symm.trans (by
    rw [natCard_submodule_eq, hℓ]
    rfl)

end CountD0p

section Fixed

theorem fix_D0p_iff {p ℓ : Submodule (ZMod 2) I} (hp : finrank (ZMod 2) p = 1)
    (hpℓ : p ≤ ℓ) (v : I) : (∀ d ∈ D0p p ℓ, d v = v) ↔ v ∈ ℓ := by
  constructor
  · intro hv
    by_contra hvℓ
    obtain ⟨f, hfv, hfℓ⟩ : ∃ f : Module.Dual (ZMod 2) I, f v ≠ 0 ∧ ℓ.map f = ⊥ :=
      Submodule.exists_dual_map_eq_bot_of_notMem hvℓ inferInstance
    obtain ⟨p0, hp0, rfl⟩ := exists_span_singleton_eq hp
    have hp0ℓ : p0 ∈ ℓ := hpℓ (Submodule.mem_span_singleton_self p0)
    have hf0 : f p0 = 0 := by
      have hmem : f p0 ∈ ℓ.map f := Submodule.mem_map_of_mem hp0ℓ
      rw [hfℓ] at hmem
      exact (Submodule.mem_bot _).1 hmem
    have hd : LinearEquiv.transvection (f := f) (v := p0) hf0 ∈
        D0p (Submodule.span (ZMod 2) {p0}) ℓ := by
      rw [mem_D0p_iff hpℓ]
      refine ⟨fun w hw => ?_, fun x => ?_⟩
      · have hfw : f w = 0 := by
          have hmem : f w ∈ ℓ.map f := Submodule.mem_map_of_mem hw
          rw [hfℓ] at hmem
          exact (Submodule.mem_bot _).1 hmem
        show w + f w • p0 = w
        rw [hfw, zero_smul, add_zero]
      · show x + f x • p0 - x ∈ _
        rw [add_sub_cancel_left]
        exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self p0)
    have h1 : v + f v • p0 = v := hv _ hd
    have h2 : f v • p0 = 0 := by simpa using h1
    rcases smul_eq_zero.1 h2 with h | h
    · exact hfv h
    · exact hp0 h
  · intro hv d hd
    exact ((mem_D0p_iff hpℓ d).1 hd).1 v hv

theorem fix_D0P_iff {ℓ Pl : Submodule (ZMod 2) I} (hℓ : finrank (ZMod 2) ℓ = 2)
    (hℓPl : ℓ ≤ Pl) (v : I) : (∀ d ∈ D0P ℓ Pl, d v = v) ↔ v ∈ Pl := by
  constructor
  · intro hv
    by_contra hvPl
    obtain ⟨f, hfv, hfPl⟩ : ∃ f : Module.Dual (ZMod 2) I, f v ≠ 0 ∧ Pl.map f = ⊥ :=
      Submodule.exists_dual_map_eq_bot_of_notMem hvPl inferInstance
    have hℓne : ℓ ≠ ⊥ := by
      intro h
      rw [h, finrank_bot] at hℓ
      omega
    obtain ⟨a, ha, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hℓne
    have hfa : f a = 0 := by
      have hmem : f a ∈ Pl.map f := Submodule.mem_map_of_mem (hℓPl ha)
      rw [hfPl] at hmem
      exact (Submodule.mem_bot _).1 hmem
    have hd : LinearEquiv.transvection (f := f) (v := a) hfa ∈ D0P ℓ Pl := by
      rw [mem_D0P_iff hℓPl]
      refine ⟨fun w hw => ?_, fun x => ?_⟩
      · have hfw : f w = 0 := by
          have hmem : f w ∈ Pl.map f := Submodule.mem_map_of_mem hw
          rw [hfPl] at hmem
          exact (Submodule.mem_bot _).1 hmem
        show w + f w • a = w
        rw [hfw, zero_smul, add_zero]
      · show x + f x • a - x ∈ ℓ
        rw [add_sub_cancel_left]
        exact Submodule.smul_mem _ _ ha
    have h1 : v + f v • a = v := hv _ hd
    have h2 : f v • a = 0 := by simpa using h1
    rcases smul_eq_zero.1 h2 with h | h
    · exact hfv h
    · exact ha0 h
  · intro hv d hd
    exact ((mem_D0P_iff hℓPl d).1 hd).1 v hv

end Fixed

theorem factF2_holds : FactF2 := by
  intro I _ _ hFin hI p ℓ Pl hp hℓ hPl hpℓ' hℓPl'
  have hpℓ : p ≤ ℓ := hpℓ'.le
  have hℓPl : ℓ ≤ Pl := hℓPl'.le
  haveI : Module.Finite (ZMod 2) I := Module.finite_of_finrank_pos (by omega)
  refine ⟨⟨card_D0p hI hp hℓ hpℓ, fun d hd => ?_, fun v => fix_D0p_iff hp hpℓ v⟩,
    ⟨card_D0P hI hℓ hPl hℓPl, fun d hd => ?_, fun v => fix_D0P_iff hℓ hℓPl v⟩⟩
  · obtain ⟨h1, h2⟩ := (mem_D0p_iff hpℓ d).1 hd
    exact unipRad_sq p d ((mem_unipRad_iff' p d).2 ⟨fun w hw => h1 w (hpℓ hw), h2⟩)
  · obtain ⟨h1, h2⟩ := (mem_D0P_iff hℓPl d).1 hd
    exact unipRad_sq Pl d ((mem_unipRad_iff' Pl d).2 ⟨h1, fun x => hℓPl (h2 x)⟩)

end CFSG.Quasithin.H13.C1294
