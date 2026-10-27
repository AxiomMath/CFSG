module

public import CFSG.RankThree.PartTwo.Sec21.RudvalisFF81Sp6Over
import CFSG.RankThree.PartTwo.Sec21.HeringFFLKE9
import CFSG.Quasithin.AppendixH.H14.H141Octad
import CFSG.RankThree.PartTwo.Sec4.RonanK429RowFSp8

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF81.Sp6O7

open CFSG CFSG.RankThree.PartTwo.Sec21 CFSG.RankThree.PartTwo.Sec21.FF79
open CFSG.RankThree.PartTwo.Sec21.FF81.Sp6Over
open CFSG.RankThree.PartTwo.Census.Carrier.Sp6Two (H6)
open CFSG.Quasithin.H13.MatNCert Matrix
open scoped commutatorElement

@[expose] noncomputable def actM (σ : H6 →* GL7) : H6 →* MulAut (Multiplicative V7) where
  toFun g :=
    { toFun := fun v => Multiplicative.ofAdd (((σ g : GL7) : M7) *ᵥ Multiplicative.toAdd v)
      invFun := fun v => Multiplicative.ofAdd (((σ g⁻¹ : GL7) : M7) *ᵥ Multiplicative.toAdd v)
      left_inv := fun v => by
        simp only [toAdd_ofAdd, Matrix.mulVec_mulVec, ← Units.val_mul, ← map_mul, inv_mul_cancel,
          map_one, Units.val_one, Matrix.one_mulVec, ofAdd_toAdd]
      right_inv := fun v => by
        simp only [toAdd_ofAdd, Matrix.mulVec_mulVec, ← Units.val_mul, ← map_mul, mul_inv_cancel,
          map_one, Units.val_one, Matrix.one_mulVec, ofAdd_toAdd]
      map_mul' := fun v w => by
        simp only [toAdd_mul, Matrix.mulVec_add, ofAdd_add] }
  map_one' := by
    ext v
    simp only [map_one, Units.val_one, Matrix.one_mulVec, ofAdd_toAdd, MulEquiv.coe_mk,
      Equiv.coe_fn_mk, MulAut.one_apply]
  map_mul' g h := by
    ext v
    simp only [map_mul, Units.val_mul, ← Matrix.mulVec_mulVec, MulEquiv.coe_mk, Equiv.coe_fn_mk,
      MulAut.mul_apply, toAdd_ofAdd]

theorem actM_apply (σ : H6 →* GL7) (g : H6) (v : Multiplicative V7) :
    actM σ g v = Multiplicative.ofAdd (((σ g : GL7) : M7) *ᵥ Multiplicative.toAdd v) := rfl

abbrev Model (σ : H6 →* GL7) : Type := Multiplicative V7 ⋊[actM σ] H6

section Equiv

variable {X : Type} [Group X] {C T L : Subgroup X}

theorem exists_equiv_model (hTC : T ≤ C) (hLC : L ≤ C)
    (hdec : ∀ c ∈ C, ∃ u ∈ T, ∃ l ∈ L, c = u * l) (f : H6 →* X) (hfL : ∀ g, f g ∈ L)
    (hLf : ∀ l ∈ L, ∃ g, f g = l) (hTL : ∀ g, f g ∈ T → g = 1) (σ : H6 →* GL7)
    (τ : ↥T ≃* Multiplicative V7)
    (hconj : ∀ (g : H6) (u : ↥T), f g * u * (f g)⁻¹ = (τ.symm (actM σ g (τ u)) : X)) :
    ∃ Ψ : Model σ ≃* ↥C, (∀ v, (Ψ (SemidirectProduct.inl v) : X) = (τ.symm v : X)) ∧
      ∀ g, (Ψ (SemidirectProduct.inr g) : X) = f g := by
  set φ₁ : Multiplicative V7 →* X := T.subtype.comp τ.symm.toMonoidHom with hφ₁
  have hcompat : ∀ g, φ₁.comp (actM σ g).toMonoidHom =
      (MulAut.conj (f g)).toMonoidHom.comp φ₁ := by
    intro g
    refine MonoidHom.ext fun v => ?_
    simp only [hφ₁, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, Subgroup.coe_subtype,
      MulAut.conj_apply]
    rw [hconj g (τ.symm v), MulEquiv.apply_symm_apply]
  set Ψ₀ : Model σ →* X := SemidirectProduct.lift φ₁ f hcompat with hΨ₀
  have hΨ₀m : ∀ m : Model σ, Ψ₀ m = (τ.symm m.left : X) * f m.right := by
    intro m
    conv_lhs => rw [← SemidirectProduct.inl_left_mul_inr_right m]
    rw [map_mul, SemidirectProduct.lift_inl, SemidirectProduct.lift_inr]
    rfl
  have hmem : ∀ m, Ψ₀ m ∈ C := fun m => by
    rw [hΨ₀m]
    exact C.mul_mem (hTC (τ.symm m.left).2) (hLC (hfL _))
  set Ψ₁ : Model σ →* ↥C := Ψ₀.codRestrict C hmem with hΨ₁
  have hinj : Function.Injective Ψ₁ := by
    rw [injective_iff_map_eq_one]
    intro m hm
    have h1 : (τ.symm m.left : X) * f m.right = 1 := by
      rw [← hΨ₀m]
      exact congrArg Subtype.val hm
    have h2 : f m.right ∈ T := by
      rw [eq_inv_of_mul_eq_one_right h1]
      exact T.inv_mem (τ.symm m.left).2
    have hr : m.right = 1 := hTL _ h2
    rw [hr, map_one, mul_one] at h1
    have hl : m.left = 1 := by
      have : τ.symm m.left = 1 := Subtype.ext h1
      rwa [MulEquiv.symm_apply_eq, map_one] at this
    exact SemidirectProduct.ext hl hr
  have hsurj : Function.Surjective Ψ₁ := by
    rintro ⟨c, hc⟩
    obtain ⟨u, hu, l, hl, rfl⟩ := hdec c hc
    obtain ⟨g, rfl⟩ := hLf l hl
    refine ⟨⟨τ ⟨u, hu⟩, g⟩, Subtype.ext ?_⟩
    show Ψ₀ _ = _
    rw [hΨ₀m]
    simp
  refine ⟨MulEquiv.ofBijective Ψ₁ ⟨hinj, hsurj⟩, fun v => ?_, fun g => ?_⟩
  · show Ψ₀ _ = _
    rw [SemidirectProduct.lift_inl]
    rfl
  · show Ψ₀ _ = _
    rw [SemidirectProduct.lift_inr]

theorem mem_iff_left_eq_one {f : H6 →* X} (hfL : ∀ g, f g ∈ L) (hLf : ∀ l ∈ L, ∃ g, f g = l)
    (hTL : ∀ g, f g ∈ T → g = 1) {σ : H6 →* GL7} {τ : ↥T ≃* Multiplicative V7}
    {Ψ : Model σ ≃* ↥C} (hΨl : ∀ v, (Ψ (SemidirectProduct.inl v) : X) = (τ.symm v : X))
    (hΨr : ∀ g, (Ψ (SemidirectProduct.inr g) : X) = f g) (m : Model σ) :
    (Ψ m : X) ∈ L ↔ m.left = 1 := by
  have hm : (Ψ m : X) = (τ.symm m.left : X) * f m.right := by
    conv_lhs => rw [← SemidirectProduct.inl_left_mul_inr_right m]
    rw [map_mul, Subgroup.coe_mul, hΨl, hΨr]
  rw [hm]
  constructor
  · intro h
    have h1 : (τ.symm m.left : X) ∈ L := by
      have := L.mul_mem h (L.inv_mem (hfL m.right))
      rwa [mul_inv_cancel_right] at this
    obtain ⟨g, hg⟩ := hLf _ h1
    have hg1 : g = 1 := hTL g (hg ▸ (τ.symm m.left).2)
    rw [hg1, map_one] at hg
    have h2 : τ.symm m.left = 1 := Subtype.ext hg.symm
    rwa [MulEquiv.symm_apply_eq, map_one] at h2
  · intro h
    rw [h, map_one, OneMemClass.coe_one, one_mul]
    exact hfL _

end Equiv

@[expose] def fixRow0 : Subgroup GL7 where
  carrier := {A | ∀ w : V7, ((A : M7) *ᵥ w) 0 = w 0}
  mul_mem' {A B} hA hB w := by
    simp only [Set.mem_setOf_eq] at hA hB ⊢
    rw [Units.val_mul, ← Matrix.mulVec_mulVec, hA, hB]
  one_mem' w := by simp
  inv_mem' {A} hA w := by
    simp only [Set.mem_setOf_eq] at hA ⊢
    have h := hA (((A⁻¹ : GL7) : M7) *ᵥ w)
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      Matrix.one_mulVec] at h
    exact h.symm

theorem mem_fixRow0_of {A : GL7} {x : List ℕ} (hA : (A : M7) = decN 7 x)
    (h : ∀ j : Fin 7, decN 7 x 0 j = if j = 0 then 1 else 0) : A ∈ fixRow0 := by
  intro w
  rw [hA, Matrix.mulVec, dotProduct, Fintype.sum_eq_single 0]
  · rw [h, if_pos rfl, one_mul]
  · intro j hj
    rw [h, if_neg hj, zero_mul]

@[expose] noncomputable def chiM (σ : H6 →* GL7) (hσ : ∀ g, σ g ∈ fixRow0) :
    Model σ →* Multiplicative (ZMod 2) where
  toFun m := Multiplicative.ofAdd ((Multiplicative.toAdd m.left) 0)
  map_one' := rfl
  map_mul' m m' := by
    simp only [SemidirectProduct.mul_left, toAdd_mul, Pi.add_apply, actM_apply, toAdd_ofAdd,
      hσ m.right _, ofAdd_add]

@[expose] noncomputable def matEquiv (A : GL7) : Multiplicative V7 ≃* Multiplicative V7 where
  toFun v := Multiplicative.ofAdd ((A : M7) *ᵥ Multiplicative.toAdd v)
  invFun v := Multiplicative.ofAdd (((A⁻¹ : GL7) : M7) *ᵥ Multiplicative.toAdd v)
  left_inv v := by
    simp only [toAdd_ofAdd, Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      Matrix.one_mulVec, ofAdd_toAdd]
  right_inv v := by
    simp only [toAdd_ofAdd, Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      Matrix.one_mulVec, ofAdd_toAdd]
  map_mul' v w := by simp only [toAdd_mul, Matrix.mulVec_add, ofAdd_add]

section Setting


open CFSG.RankThree.PartTwo.Census.Carrier.Sp6Two (H6)

theorem commutator_eq_of_comm {X : Type} [Group X] {u u' l l' : X} (h1 : u * l = l * u)
    (h2 : u * l' = l' * u) (h3 : u' * l = l * u') (h4 : u' * l' = l' * u') (h5 : u * u' = u' * u) :
    ⁅u * l, u' * l'⁆ = ⁅l, l'⁆ := by
  have e1 : u * l * (u' * l') = l * l' * (u * u') := by
    calc u * l * (u' * l') = l * (u * u') * l' := by rw [h1]; group
      _ = l * (u * (u' * l')) := by group
      _ = l * (u * (l' * u')) := by rw [h4]
      _ = l * ((u * l') * u') := by group
      _ = l * ((l' * u) * u') := by rw [h2]
      _ = l * l' * (u * u') := by group
  have e2 : u' * l' * (u * l) = l' * l * (u * u') := by
    calc u' * l' * (u * l) = l' * (u' * u) * l := by rw [h4]; group
      _ = l' * (u' * (u * l)) := by group
      _ = l' * (u' * (l * u)) := by rw [h1]
      _ = l' * ((u' * l) * u) := by group
      _ = l' * ((l * u') * u) := by rw [h3]
      _ = l' * l * (u' * u) := by group
      _ = l' * l * (u * u') := by rw [h5]
  rw [commutatorElement_def, commutatorElement_def,
    show u * l * (u' * l') * (u * l)⁻¹ * (u' * l')⁻¹ =
      (u * l * (u' * l')) * (u' * l' * (u * l))⁻¹ by group, e1, e2]
  group

theorem exists_coords {X : Type} [Group X] [Finite X] {L : Subgroup X} {t₀ : X}
    (ht₀ : orderOf t₀ = 2) (hLC : L ≤ Cen t₀)
    (hL : CFSG.Assembly.LowTwoRank.StatedClassicalModel ↥L .PSp 3 2 1)
    (hTL : setMul (Op 2 (Cen t₀)) L = Cen t₀) (hT : IsElemAb 2 7 (Op 2 (Cen t₀)))
    (hcomm : t₀ ∈ ⁅Cen t₀, Cen t₀⁆) :
    ∃ (f : H6 →* X) (σ : H6 →* GL7) (τ : ↥(Op 2 (Cen t₀)) ≃* Multiplicative V7)
      (ht : t₀ ∈ Op 2 (Cen t₀)), (∀ g, f g ∈ L) ∧ (∀ l ∈ L, ∃ g, f g = l) ∧
      (∀ g, f g ∈ Op 2 (Cen t₀) → g = 1) ∧
      τ ⟨t₀, ht⟩ = Multiplicative.ofAdd (Pi.single 0 1) ∧
      ((σ gamH : GL7) : M7) = decN 7 nGc ∧ ((σ hH : GL7) : M7) = decN 7 nHc ∧
      ((σ cH : GL7) : M7) = decN 7 xIc ∧
      ∀ (g : H6) (u : ↥(Op 2 (Cen t₀))), f g * u * (f g)⁻¹ = (τ.symm (actM σ g (τ u)) : X) := by
  classical
  set C := Cen t₀ with hCdef
  set T := Op 2 C with hTdef
  have hTC : T ≤ C := Subgroup.map_subtype_le _
  have hTn : ∀ g ∈ C, ∀ u ∈ T, g * u * g⁻¹ ∈ T := by
    intro g hg u hu
    obtain ⟨u', hu', rfl⟩ := Subgroup.mem_map.mp hu
    exact Subgroup.mem_map.mpr ⟨⟨g, hg⟩ * u' * ⟨g, hg⟩⁻¹,
      (CFSG.pCore_normal (p := 2) (G := ↥C)).conj_mem u' hu' ⟨g, hg⟩, by simp⟩
  have ht₀C : t₀ ∈ C := Subgroup.mem_centralizer_singleton_iff.mpr rfl
  have ht : t₀ ∈ T := by
    set N : Subgroup ↥C := Subgroup.zpowers ⟨t₀, ht₀C⟩ with hNdef
    have hN : N.Normal := by
      constructor
      intro n hn g
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hn
      have hc : Commute g ⟨t₀, ht₀C⟩ :=
        Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp g.2)
      rw [((hc.zpow_right k).eq), mul_inv_cancel_right]
      exact Subgroup.zpow_mem_zpowers _ k
    have hNp : IsPGroup 2 N := by
      refine IsPGroup.of_card (n := 1) ?_
      rw [hNdef, Nat.card_zpowers, Subgroup.orderOf_mk, ht₀, pow_one]
    have hle : N ≤ CFSG.pCore 2 ↥C := le_sSup ⟨hN, hNp⟩
    exact Subgroup.mem_map.mpr ⟨⟨t₀, ht₀C⟩, hle (Subgroup.mem_zpowers _), rfl⟩
  obtain ⟨e⟩ := CFSG.RankThree.PartTwo.Sec21.nonempty_mulEquiv_H6_of_stated hL
  set f : H6 →* X := L.subtype.comp e.symm.toMonoidHom with hfdef
  have hfinj : Function.Injective f := Subtype.val_injective.comp e.symm.injective
  have hfL : ∀ g, f g ∈ L := fun g => (e.symm g).2
  have hLf : ∀ l ∈ L, ∃ g, f g = l := fun l hl => ⟨e ⟨l, hl⟩, by simp [hfdef]⟩
  have hfC : ∀ g, f g ∈ C := fun g => hLC (hfL g)
  have hdec : ∀ c ∈ C, ∃ u ∈ T, ∃ l ∈ L, c = u * l := by
    intro c hc
    have hc' : c ∈ setMul T L := by rw [hTL]; exact hc
    obtain ⟨u, hu, l, hl, rfl⟩ := hc'
    exact ⟨u, hu, l, hl, rfl⟩
  haveI : IsElementaryAbelian 2 ↥T := hT.1
  have hsq : ∀ u ∈ T, u ^ 2 = 1 := fun u hu => elemPow_eq_one_of_isElementaryAbelian u hu
  have hTab : ∀ u ∈ T, ∀ v ∈ T, u * v = v * u := fun u hu v hv =>
    congrArg Subtype.val (hT.1.toIsMulCommutative.is_comm.comm (⟨u, hu⟩ : ↥T) ⟨v, hv⟩)
  haveI : IsSimpleGroup H6 := CFSG.RankThree.PartTwo.Sec4.RonanK429F.Sp8.isSimpleGroup_H6
  have hTL1 : ∀ g, f g ∈ T → g = 1 := by
    set N := T.comap f with hNdef
    have hN : N.Normal := ⟨fun n hn g => by
      simp only [hNdef, Subgroup.mem_comap, map_mul, map_inv] at hn ⊢
      exact hTn _ (hfC g) _ hn⟩
    rcases (haveI := hN; IsSimpleGroup.eq_bot_or_eq_top_of_normal N) with h | h
    · intro g hg
      exact Subgroup.mem_bot.mp (h ▸ (hg : g ∈ N))
    · exfalso
      have hg : f gamH ∈ T := (h ▸ Subgroup.mem_top gamH : gamH ∈ N)
      have h3 : gamH ^ 2 = 1 := hfinj (by rw [map_pow, hsq _ hg, map_one])
      apply gamH_ne_one
      calc gamH = gamH ^ 7 * ((gamH ^ 2) ^ 3)⁻¹ := by group
        _ = 1 := by rw [gamH_pow_seven, h3, one_pow, inv_one, one_mul]
  have hCT : C ⊓ CenS T ≤ T := by
    set N := (CenS T).comap f with hNdef
    have hN : N.Normal := by
      constructor
      intro n hn g
      simp only [hNdef, Subgroup.mem_comap, Subgroup.mem_centralizer_iff, map_mul,
        map_inv] at hn ⊢
      intro u hu
      have hu' : (f g)⁻¹ * u * f g ∈ T := by
        have := hTn _ (C.inv_mem (hfC g)) u hu
        rwa [inv_inv] at this
      have e1 := hn _ hu'
      calc u * (f g * f n * (f g)⁻¹) = f g * ((f g)⁻¹ * u * f g * f n) * (f g)⁻¹ := by group
        _ = f g * (f n * ((f g)⁻¹ * u * f g)) * (f g)⁻¹ := by rw [e1]
        _ = f g * f n * (f g)⁻¹ * u := by group
    rcases (haveI := hN; IsSimpleGroup.eq_bot_or_eq_top_of_normal N) with h | h
    · intro c hc
      obtain ⟨hcC, hcT⟩ := Subgroup.mem_inf.mp hc
      obtain ⟨u, hu, l, hl, rfl⟩ := hdec c hcC
      obtain ⟨g, rfl⟩ := hLf l hl
      have hl' : f g ∈ CenS T := by
        have hu' : u ∈ CenS T := Subgroup.mem_centralizer_iff.mpr fun v hv => hTab v hv u hu
        have := (CenS T).mul_mem ((CenS T).inv_mem hu') hcT
        rwa [inv_mul_cancel_left] at this
      have hg : g = 1 := Subgroup.mem_bot.mp (h ▸ (hl' : g ∈ N))
      rw [hg, map_one, mul_one]
      exact hu
    · exfalso
      have hLT : ∀ g, ∀ u ∈ T, u * f g = f g * u := fun g u hu =>
        Subgroup.mem_centralizer_iff.mp (h ▸ Subgroup.mem_top g : g ∈ N) u hu
      have hcl : ⁅C, C⁆ ≤ L := by
        rw [Subgroup.commutator_le]
        intro x hx y hy
        obtain ⟨u, hu, l, hl, rfl⟩ := hdec x hx
        obtain ⟨u', hu', l', hl', rfl⟩ := hdec y hy
        obtain ⟨g, rfl⟩ := hLf l hl
        obtain ⟨g', rfl⟩ := hLf l' hl'
        rw [commutator_eq_of_comm (hLT g u hu) (hLT g' u hu) (hLT g u' hu') (hLT g' u' hu')
          (hTab u hu u' hu'), commutatorElement_def]
        exact L.mul_mem (L.mul_mem (L.mul_mem (hfL g) (hfL g')) (L.inv_mem (hfL g)))
          (L.inv_mem (hfL g'))
      obtain ⟨g, hg⟩ := hLf t₀ (hcl hcomm)
      have hg1 : g = 1 := hTL1 g (hg ▸ ht)
      rw [hg1, map_one] at hg
      rw [← hg, orderOf_one] at ht₀
      exact absurd ht₀ (by norm_num)
  have hTe : CFSG.Open.IsElemAbelian 2 T :=
    CFSG.Open.isElemAbelian_of_isElementaryAbelian (h := hT.1)
  obtain ⟨κ⟩ := CFSG.Quasithin.AppendixH.H14.exists_mulEquiv_elemAbelian_two T hTe 7 hT.2
  set ρ := rhoT hTn κ with hρ
  have hTcen : ∀ u ∈ T, u ∈ CenS T := fun u hu =>
    Subgroup.mem_centralizer_iff.mpr fun v hv => hTab v hv u hu
  have hker : ∀ g : ↥C, ρ g = 1 ↔ (g : X) ∈ T := fun g =>
    (rhoT_eq_one_iff hTn κ g).trans ⟨fun h => hCT (Subgroup.mem_inf.mpr ⟨g.2, h⟩), hTcen _⟩
  set f' : H6 →* ↥C := f.codRestrict C hfC with hf'def
  set x₀ : V7 := Multiplicative.toAdd (κ ⟨t₀, ht⟩) with hx₀def
  have hfix : ∀ g : ↥C, ((ρ g : GL7) : M7) *ᵥ x₀ = x₀ := by
    intro g
    rw [hx₀def, rhoT_mulVec]
    congr 2
    apply Subtype.ext
    rw [conjT_apply, mul_inv_eq_iff_eq_mul]
    exact Subgroup.mem_centralizer_singleton_iff.mp g.2
  set M : M7 := ((ρ (f' gamH) : GL7) : M7) with hMdef
  set N : M7 := ((ρ (f' hH) : GL7) : M7) with hNdef
  have hcoe : ∀ (g : H6) (k : ℕ), ((ρ (f' g) : GL7) : M7) ^ k =
      ((ρ (f' (g ^ k)) : GL7) : M7) := by
    intro g k
    rw [map_pow, map_pow, Units.val_pow_eq_pow_val]
  have hM7 : M ^ 7 = 1 := by rw [hMdef, hcoe, gamH_pow_seven, map_one, map_one, Units.val_one]
  have hN6 : N ^ 6 = 1 := by rw [hNdef, hcoe, hH_pow_six, map_one, map_one, Units.val_one]
  have hNM : N * M = M ^ 3 * N := by
    rw [hMdef, hNdef, hcoe, ← Units.val_mul, ← Units.val_mul, ← map_mul, ← map_mul, ← map_mul,
      ← map_mul, hH_mul_gamH]
  have hM1 : M ≠ 1 := by
    intro h
    have h1 : ρ (f' gamH) = 1 := Units.ext h
    have hT' : f gamH ∈ T := (hker _).mp h1
    exact gamH_ne_one (hTL1 _ hT')
  have hx₀ : x₀ ≠ 0 := by
    intro h
    have h1 : κ ⟨t₀, ht⟩ = 1 := by
      have e1 : κ ⟨t₀, ht⟩ = Multiplicative.ofAdd x₀ := rfl
      rw [e1, h, ofAdd_zero]
    have h2 : (⟨t₀, ht⟩ : ↥T) = 1 := κ.injective (h1.trans κ.map_one.symm)
    have h3 : t₀ = 1 := congrArg Subtype.val h2
    rw [h3, orderOf_one] at ht₀
    exact absurd ht₀ (by norm_num)
  obtain ⟨P, hPu, hP0, hMP, hNP⟩ := normal_form hM7 hN6 hNM hM1 hx₀ (hfix _) (hfix _)
  set Pu : GL7 := hPu.unit with hPudef
  have hPuv : (Pu : M7) = P := hPu.unit_spec
  have hPinv1 : ((Pu⁻¹ : GL7) : M7) * P = 1 := by
    rw [← hPuv, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hPinv2 : P * ((Pu⁻¹ : GL7) : M7) = 1 := by
    rw [← hPuv, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  set ρ' : ↥C →* GL7 := (MulAut.conj Pu⁻¹).toMonoidHom.comp ρ with hρ'def
  have hρ' : ∀ g, ((ρ' g : GL7) : M7) = ((Pu⁻¹ : GL7) : M7) * ((ρ g : GL7) : M7) * P := by
    intro g
    simp only [hρ'def, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
      inv_inv, Units.val_mul, hPuv]
  have hρ'e : ∀ g, ((ρ' g : GL7) : M7) *ᵥ Pi.single 0 1 = Pi.single 0 1 := by
    intro g
    rw [hρ', ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hP0, hfix, ← hP0,
      Matrix.mulVec_mulVec, hPinv1, Matrix.one_mulVec]
  set σ : H6 →* GL7 := ρ'.comp f' with hσdef
  have hσg : ((σ gamH : GL7) : M7) = decN 7 nGc := by
    rw [← nG_eq]
    show ((ρ' (f' gamH) : GL7) : M7) = nG
    rw [hρ', Matrix.mul_assoc, ← hMdef, hMP, ← Matrix.mul_assoc, hPinv1, Matrix.one_mul]
  have hσh : ((σ hH : GL7) : M7) = decN 7 nHc := by
    rw [← nH_eq]
    show ((ρ' (f' hH) : GL7) : M7) = nH
    rw [hρ', Matrix.mul_assoc, ← hNdef, hNP, ← Matrix.mul_assoc, hPinv1, Matrix.one_mul]
  set τ : ↥T ≃* Multiplicative V7 := κ.trans (matEquiv Pu⁻¹) with hτdef
  have hτ : ∀ u, Multiplicative.toAdd (τ u) =
      ((Pu⁻¹ : GL7) : M7) *ᵥ Multiplicative.toAdd (κ u) := fun u => rfl
  have hτt : τ ⟨t₀, ht⟩ = Multiplicative.ofAdd (Pi.single 0 1) := by
    apply Multiplicative.toAdd.injective
    rw [hτ, toAdd_ofAdd, ← hx₀def, ← hP0, Matrix.mulVec_mulVec, hPinv1, Matrix.one_mulVec]
  have hconj : ∀ (g : H6) (u : ↥T), f g * u * (f g)⁻¹ = (τ.symm (actM σ g (τ u)) : X) := by
    intro g u
    have hw : f g * u * (f g)⁻¹ ∈ T := hTn _ (hfC g) u u.2
    have e1 : τ ⟨f g * u * (f g)⁻¹, hw⟩ = actM σ g (τ u) := by
      apply Multiplicative.toAdd.injective
      rw [actM_apply, toAdd_ofAdd, hτ, hτ]
      have e2 : κ ⟨f g * u * (f g)⁻¹, hw⟩ = κ (conjT hTn (f' g) u) := rfl
      rw [e2, ← rhoT_mulVec, show σ g = ρ' (f' g) from rfl, hρ', Matrix.mulVec_mulVec,
        Matrix.mulVec_mulVec, Matrix.mul_assoc, Matrix.mul_assoc, hPinv2, Matrix.mul_one]
    rw [← e1, MulEquiv.symm_apply_apply]
  rcases pin σ hσg hσh (hρ'e _) with hS | hI
  ·
    exfalso
    obtain ⟨Ψ, hΨl, -⟩ := exists_equiv_model hTC hLC hdec f hfL hLf hTL1 σ τ hconj
    have hrow : ∀ g, σ g ∈ fixRow0 := by
      have hcl : Subgroup.closure ({gamH, hH, cH} : Set H6) ≤ fixRow0.comap σ := by
        rw [Subgroup.closure_le]
        rintro _ (rfl | rfl | rfl)
        · exact mem_fixRow0_of hσg (by decide)
        · exact mem_fixRow0_of hσh (by decide)
        · exact mem_fixRow0_of hS (by decide)
      intro g
      exact hcl (closure_gens_eq_top ▸ Subgroup.mem_top g)
    set χ := (chiM σ hrow).comp Ψ.symm.toMonoidHom with hχ
    have hmem : (⟨t₀, ht₀C⟩ : ↥C) ∈ commutator ↥C := by
      have h1 : ⁅C, C⁆ = (commutator ↥C).map C.subtype := by
        rw [commutator, Subgroup.map_commutator, ← MonoidHom.range_eq_map,
          Subgroup.range_subtype]
      rw [h1] at hcomm
      obtain ⟨y, hy, hyt⟩ := Subgroup.mem_map.mp hcomm
      have hy' : y = ⟨t₀, ht₀C⟩ := Subtype.ext hyt
      rwa [← hy']
    have hk : χ ⟨t₀, ht₀C⟩ = 1 := Abelianization.commutator_subset_ker χ hmem
    have hΨt : Ψ.symm ⟨t₀, ht₀C⟩ = SemidirectProduct.inl (Multiplicative.ofAdd (Pi.single 0 1)) := by
      rw [MulEquiv.symm_apply_eq]
      apply Subtype.ext
      rw [hΨl, ← hτt, MulEquiv.symm_apply_apply]
    rw [hχ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, hΨt] at hk
    simp [chiM] at hk
  · exact ⟨f, σ, τ, ht, hfL, hLf, hTL1, hτt, hσg, hσh, hI, hconj⟩

end Setting

end CFSG.RankThree.PartTwo.Sec21.FF81.Sp6O7
