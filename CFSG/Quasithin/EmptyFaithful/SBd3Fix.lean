module

public import CFSG.Quasithin.Background.P4InspOrthA8
public import CFSG.Quasithin.EmptyFaithful.SBd2Two
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.ReducedImage

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.G11 CFSG.Quasithin.G11.P4InspOrth

namespace SBd3

@[expose] def c8 : Equiv.Perm (Fin 8) := ⟨fun i => i + 1, fun i => i - 1, by decide, by decide⟩

theorem c8_pow_eight : c8 ^ 8 = 1 := by decide

@[expose] def w8 : ↥(permCore 8) :=
  ⟨fun i => if i.val % 2 = 0 then 1 else 0, by
    show ∑ i : Fin 8, (fun i : Fin 8 => if i.val % 2 = 0 then (1 : ZMod 2) else 0) i = 0
    decide⟩

theorem fix_c8_aux : ∀ (y : Fin 8 → ZMod 2) (b : ZMod 2),
    (∀ i : Fin 8, y (c8.symm i) - y i = b) →
      (y = 0 ∨ y = 1 ∨ y = w8.1 ∨ y = w8.1 + 1) := by
  decide +kernel

theorem fix_c8 (v : p4insporth_V8) (h : p4insporth_perm8Hom c8 v = v) :
    v = 0 ∨ v = Submodule.Quotient.mk w8 := by
  revert h
  refine Submodule.Quotient.induction_on _ v fun x => ?_
  intro h
  rw [p4insporth_perm8Hom_mk] at h
  have h1 : p4insporth_permHom 8 c8 x - x ∈ p4insporth_L8 := (Submodule.Quotient.eq _).1 h
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.1 h1
  have key : ∀ i : Fin 8, x.1 (c8.symm i) - x.1 i = a := by
    intro i
    have := congrFun (congrArg Subtype.val ha) i
    simpa [p4insporth_L8, p4insporth_one8, p4insporth_permHom_apply, permAct] using this.symm
  have hx := fix_c8_aux x.1 a key
  have hone : (Submodule.Quotient.mk p4insporth_one8 : p4insporth_V8) = 0 :=
    (Submodule.Quotient.mk_eq_zero _).2 (Submodule.mem_span_singleton_self _)
  rcases hx with hx | hx | hx | hx
  · left
    have : x = 0 := Subtype.ext hx
    rw [this]; rfl
  · left
    have : x = p4insporth_one8 := Subtype.ext hx
    rw [this, hone]
  · right
    have : x = w8 := Subtype.ext hx
    rw [this]
  · right
    have : x = w8 + p4insporth_one8 := Subtype.ext hx
    rw [this, Submodule.Quotient.mk_add, hone, add_zero]


section Bridge

variable {V : Type} [CommGroup V]

private theorem zmod_cases2 (a : ZMod 2) : a = 0 ∨ a = 1 := by revert a; decide

private theorem q_mul' {q : V → ZMod 2} (x y : V) :
    q (x * y) = q x + q y + quadPolar q x y := by
  unfold quadPolar
  generalize q (x * y) = a
  generalize q x = b
  generalize q y = c
  revert a b c
  decide

private theorem polar_one_left' {q : V → ZMod 2} (hq : IsQuadraticFormOn q) (x : V) :
    quadPolar q 1 x = 0 := by
  unfold quadPolar
  rw [one_mul, hq.1]
  generalize q x = b
  revert b
  decide

private theorem polar_one_right' {q : V → ZMod 2} (hq : IsQuadraticFormOn q) (x : V) :
    quadPolar q x 1 = 0 := by
  have h := hq.2.2 x 1 1
  rw [mul_one] at h
  generalize quadPolar q x 1 = a at h
  revert a
  decide

private theorem polar_self' {q : V → ZMod 2} (hq : IsQuadraticFormOn q) (hsq : ∀ v : V, v * v = 1)
    (x : V) : quadPolar q x x = 0 := by
  unfold quadPolar
  rw [hsq x, hq.1]
  generalize q x = a
  revert a
  decide

private theorem two_nsmul_eq_zero' (hsq : ∀ x : V, x * x = 1) (u : Additive V) :
    (2 : ℕ) • u = 0 := by
  obtain ⟨x, rfl⟩ := Additive.ofMul.surjective u
  rw [← ofMul_pow, pow_two, hsq x]
  rfl


theorem exists_eight_cycle_isometry [Finite V] (hsq : ∀ x : V, x * x = 1) {q : V → ZMod 2}
    (hq : IsQuadraticFormOn q) (hnd : IsNondegQuadratic q)
    (hE : ∃ E : Subgroup V, Nat.card E = 2 ^ 3 ∧ ∀ e ∈ E, q e = 0) (hcard : Nat.card V = 2 ^ 6) :
    ∃ γ : MulAut V, γ ∈ orthogonalGroupOf q ∧ γ ^ 8 = 1 ∧ Nat.card {v : V // γ v = v} ≤ 2 := by
  classical
  let _ : Module (ZMod 2) (Additive V) := AddCommGroup.zmodModule (two_nsmul_eq_zero' hsq)
  let f : LinearMap.BilinForm (ZMod 2) (Additive V) :=
    LinearMap.mk₂ (ZMod 2) (fun u v => quadPolar q (Additive.toMul u) (Additive.toMul v))
      (fun a b c => hq.2.1 _ _ _)
      (fun c u v => by
        rcases zmod_cases2 c with rfl | rfl
        · simp [polar_one_left' hq]
        · simp)
      (fun a b c => hq.2.2 _ _ _)
      (fun c u v => by
        rcases zmod_cases2 c with rfl | rfl
        · simp [polar_one_right' hq]
        · simp)
  have hfq : ∀ x y : Additive V, (fun u : Additive V => q (Additive.toMul u)) (x + y) =
      (fun u : Additive V => q (Additive.toMul u)) x +
        (fun u : Additive V => q (Additive.toMul u)) y + f x y := by
    intro x y
    show q (Additive.toMul x * Additive.toMul y) = q (Additive.toMul x) + q (Additive.toMul y) +
      quadPolar q (Additive.toMul x) (Additive.toMul y)
    exact q_mul' _ _
  have hsym : IsSymplectic f := by
    refine ⟨fun x => polar_self' hq hsq _, fun x hx => ?_⟩
    have h1 := hnd (Additive.toMul x) (fun y => hx (Additive.ofMul y))
    exact Additive.toMul.injective (by simpa using h1)
  have hU : Nat.card (Additive V) = 2 ^ 6 := by
    rw [Nat.card_congr (Additive.toMul : Additive V ≃ V), hcard]
  have hfin : Module.finrank (ZMod 2) (Additive V) = 6 := by
    have h := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive V)
    rw [hU, Nat.card_zmod] at h
    exact (Nat.pow_right_injective (le_refl 2) h).symm
  obtain ⟨E, hEc, hEq⟩ := hE
  let W : Submodule (ZMod 2) (Additive V) :=
    { carrier := {u | Additive.toMul u ∈ E}
      add_mem' := fun {a b} ha hb => E.mul_mem ha hb
      zero_mem' := E.one_mem
      smul_mem' := fun c u hu => by
        rcases zmod_cases2 c with rfl | rfl
        · simp
        · simpa using hu }
  have hWc : Nat.card W = 2 ^ 3 := by
    rw [← hEc]
    exact Nat.card_congr ⟨fun w => ⟨Additive.toMul w.1, w.2⟩, fun x => ⟨Additive.ofMul x.1, x.2⟩,
      fun w => rfl, fun x => rfl⟩
  have hWf : Module.finrank (ZMod 2) W = 3 := by
    have h := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := W)
    rw [hWc, Nat.card_zmod] at h
    exact (Nat.pow_right_injective (le_refl 2) h).symm
  have hplus : CFSG.GroupTheory.WeirSylow.IsPlusType (p4insporth_quad hfq) :=
    ⟨W, by rw [hWf, hfin], fun x hx => hEq _ hx⟩
  obtain ⟨e⟩ := CFSG.GroupTheory.WeirSylow.nonempty_isometry_of_isPlusType_iff (n := 3)
    (p4insporth_nondegenerate_quad hsym hfq)
    (p4insporth_nondegenerate_quad p4insporth_symplectic8 p4insporth_q8_add)
    hfin p4insporth_finrank8 (iff_of_true hplus p4insporth_plus8)
  let ι := e.toLinearEquiv
  have hι : ∀ x, p4insporth_q8 (ι x) = q (Additive.toMul x) := fun x => e.map_app x
  have hι' : ∀ y, q (Additive.toMul (ι.symm y)) = p4insporth_q8 y := fun y => by
    rw [← hι, LinearEquiv.apply_symm_apply]
  let Φ : GLV p4insporth_V8 →* MulAut V :=
    { toFun := fun g =>
        { toFun := fun x => Additive.toMul (ι.symm (g (ι (Additive.ofMul x))))
          invFun := fun x => Additive.toMul (ι.symm (g.symm (ι (Additive.ofMul x))))
          left_inv := fun x => by simp
          right_inv := fun x => by simp
          map_mul' := fun x y => by simp [ofMul_mul, map_add, toMul_add] }
      map_one' := by
        ext x
        simp
      map_mul' := fun g h => by
        ext x
        simp }
  have hΦ : ∀ g v, Φ g v = Additive.toMul (ι.symm (g (ι (Additive.ofMul v)))) := fun g v => rfl
  refine ⟨Φ (p4insporth_perm8Hom c8), ?_, ?_, ?_⟩
  · intro v
    rw [hΦ]
    rw [hι', p4insporth_q8_perm, hι]
    simp
  · rw [← map_pow Φ, ← map_pow p4insporth_perm8Hom, c8_pow_eight, map_one, map_one]
  · let v₀ : V := Additive.toMul (ι.symm 0)
    let v₁ : V := Additive.toMul (ι.symm (Submodule.Quotient.mk w8))
    have hsub : {v : V | Φ (p4insporth_perm8Hom c8) v = v} ⊆ {v₀, v₁} := by
      intro v hv
      have h1 : ι.symm (p4insporth_perm8Hom c8 (ι (Additive.ofMul v))) = Additive.ofMul v := by
        have hv' : Φ (p4insporth_perm8Hom c8) v = v := hv
        rw [hΦ] at hv'
        have := congrArg Additive.ofMul hv'
        simpa using this
      have h2 : p4insporth_perm8Hom c8 (ι (Additive.ofMul v)) = ι (Additive.ofMul v) := by
        have := congrArg ι h1
        simpa using this
      rcases fix_c8 _ h2 with h3 | h3
      · left
        show v = Additive.toMul (ι.symm 0)
        rw [← h3]
        simp
      · right
        show v = Additive.toMul (ι.symm (Submodule.Quotient.mk w8))
        rw [← h3]
        simp
    calc Nat.card {v : V // Φ (p4insporth_perm8Hom c8) v = v}
        = Set.ncard {v : V | Φ (p4insporth_perm8Hom c8) v = v} :=
          (Nat.card_coe_set_eq _)
      _ ≤ Set.ncard ({v₀, v₁} : Set V) := Set.ncard_le_ncard hsub (Set.toFinite _)
      _ ≤ 2 := by
          refine (Set.ncard_insert_le v₀ {v₁}).trans ?_
          rw [Set.ncard_singleton]


theorem card_fixed_sylow_le_two [Finite V] (hsq : ∀ x : V, x * x = 1) {q : V → ZMod 2}
    (hq : IsQuadraticFormOn q) (hnd : IsNondegQuadratic q)
    (hE : ∃ E : Subgroup V, Nat.card E = 2 ^ 3 ∧ ∀ e ∈ E, q e = 0) (hcard : Nat.card V = 2 ^ 6)
    {P : Subgroup (MulAut V)} (hP : IsSylowTwoOf P (orthogonalGroupOf q)) :
    Nat.card {v : V // ∀ g ∈ P, g v = v} ≤ 2 := by
  obtain ⟨γ, hγO, hγ8, hγfix⟩ := exists_eight_cycle_isometry hsq hq hnd hE hcard
  have hp2 : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hord : orderOf γ ∣ 2 ^ 3 := orderOf_dvd_of_pow_eq_one hγ8
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hord
  have hD2 : IsPGroup 2 (Subgroup.zpowers γ) :=
    IsPGroup.of_card (n := k) (by rw [Nat.card_zpowers, hk])
  have hDO : Subgroup.zpowers γ ≤ orthogonalGroupOf q := Subgroup.zpowers_le.mpr hγO
  obtain ⟨S, hS, hDS⟩ := B6.exists_isSylowTwoOf_ge hD2 hDO
  obtain ⟨g, hg, hPg⟩ := B6.isSylowTwoOf_exists_conj hS hP
  have hγ' : g * γ * g⁻¹ ∈ P := by
    rw [hPg, B6.mem_conjSub]
    have : γ ∈ S := hDS (Subgroup.mem_zpowers γ)
    simpa [mul_assoc] using this
  have hmap : ∀ v : {v : V // ∀ h ∈ P, h v = v}, γ ((g⁻¹ : MulAut V) v.1) = (g⁻¹ : MulAut V) v.1 := by
    intro v
    have h1 := v.2 _ hγ'
    rw [MulAut.mul_apply, MulAut.mul_apply] at h1
    have h2 := congrArg (g⁻¹ : MulAut V) h1
    simpa using h2
  refine le_trans (Nat.card_le_card_of_injective
    (fun v : {v : V // ∀ h ∈ P, h v = v} => (⟨(g⁻¹ : MulAut V) v.1, hmap v⟩ : {v : V // γ v = v}))
    ?_) hγfix
  intro a b hab
  have h1 : (g⁻¹ : MulAut V) a.1 = (g⁻¹ : MulAut V) b.1 := congrArg Subtype.val hab
  exact Subtype.ext ((g⁻¹ : MulAut V).injective h1)

end Bridge

section Context

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ Yp I L : Subgroup G} {t : G}

theorem sylowFixedOrder32_holds : SylowFixedOrder32 := by
  intro G _ _ T Mc M V₁ V₂ Yp I L t c h1
  obtain ⟨q, hq, hnd, hE, hcard, hautq⟩ := h1
  have c25 : Ctx15325L T Mc M V₁ V₂ Yp I L t :=
    c.toCtx15331.toCtx15330.toCtx15328.toCtx15327.toCtx15325L
  have hF : Facts153 T M V₁ Yp I := c25.facts.toFacts153
  have hUL : IsElemAbelian 2 (UL153 T I L) := SBc.isElemAbelian_UL c
  have hIN : I ≤ Subgroup.normalizer (UL153 T I L : Set G) := S153H.I_le_normalizer_UL c
  have hsyl : IsSylowTwoOf (autOn (Sgp153 T V₁) (UL153 T I L)) (autOn I (UL153 T I L)) :=
    CFSG.QuasithinUnique.Setup.isSylowTwoOf_autOn hF.sylow hIN
  rw [hautq] at hsyl
  let _ : CommGroup ↥(UL153 T I L) := commGroupOfElemAbelian hUL
  have hsq : ∀ x : ↥(UL153 T I L), x * x = 1 := fun x =>
    Subtype.ext (by simpa [pow_two] using hUL.2 x.1 x.2)
  have key := card_fixed_sylow_le_two hsq hq hnd hE hcard hsyl
  have hfix : ∀ x : ↥(UL153 T I L ⊓ Subgroup.centralizer (Sgp153 T V₁ : Set G)),
      ∀ g ∈ autOn (Sgp153 T V₁) (UL153 T I L), g ⟨x.1, x.2.1⟩ = ⟨x.1, x.2.1⟩ := by
    intro x g hg
    obtain ⟨s, hsN, hsS, rfl⟩ := mem_autOn_iff_exists.mp hg
    apply Subtype.ext
    rw [conjAct_apply_coe''']
    have := Subgroup.mem_centralizer_iff.mp x.2.2 s hsS
    rw [this]
    group
  refine le_trans (Nat.card_le_card_of_injective
    (fun x : ↥(UL153 T I L ⊓ Subgroup.centralizer (Sgp153 T V₁ : Set G)) =>
      (⟨⟨x.1, x.2.1⟩, hfix x⟩ :
        {v : ↥(UL153 T I L) // ∀ g ∈ autOn (Sgp153 T V₁) (UL153 T I L), g v = v})) ?_) key
  intro a b hab
  have := congrArg (fun z => ((z.1 : ↥(UL153 T I L)) : G)) hab
  exact Subtype.ext (by simpa using this)

end Context

end SBd3
end CFSG.Quasithin
