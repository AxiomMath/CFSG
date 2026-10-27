module

public import CFSG.Milestones.ASVolI.H5
public import CFSG.Quasithin.H13.L32AH63b
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilyGL3Classify
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.ASVolI.ChH

open CFSG.Quasithin CFSG.Open

@[expose] def permModAct (G : Type*) [Group G] (X : Type*) [MulAction G X] :
    G →* MulAut (Multiplicative (X → ZMod 2)) where
  toFun g :=
    { toFun := fun f => Multiplicative.ofAdd fun x => Multiplicative.toAdd f (g⁻¹ • x)
      invFun := fun f => Multiplicative.ofAdd fun x => Multiplicative.toAdd f (g • x)
      left_inv := fun f => by
        apply Multiplicative.toAdd.injective
        funext x
        simp
      right_inv := fun f => by
        apply Multiplicative.toAdd.injective
        funext x
        simp
      map_mul' := fun f f' => by
        apply Multiplicative.toAdd.injective
        funext x
        simp }
  map_one' := by
    ext f x
    simp
  map_mul' g h := by
    ext f x
    simp [mul_smul]

@[expose] noncomputable def permCore (X : Type*) [Finite X] :
    Subgroup (Multiplicative (X → ZMod 2)) :=
  letI := Fintype.ofFinite X
  AddSubgroup.toSubgroup (AddMonoidHom.ker (∑ x : X, Pi.evalAddMonoidHom (fun _ : X => ZMod 2) x))

abbrev AdjAmb : Type := Multiplicative (Matrix (Fin 3) (Fin 3) (ZMod 2))

@[expose] def adjAmbAct : GL (Fin 3) (ZMod 2) →* MulAut AdjAmb where
  toFun g :=
    { toFun := fun X => Multiplicative.ofAdd
          ((g : Matrix (Fin 3) (Fin 3) (ZMod 2)) * Multiplicative.toAdd X *
            ((g⁻¹ : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)))
      invFun := fun X => Multiplicative.ofAdd
          (((g⁻¹ : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)) * Multiplicative.toAdd X *
            (g : Matrix (Fin 3) (Fin 3) (ZMod 2)))
      left_inv := fun X => by
        apply Multiplicative.toAdd.injective
        simp only [toAdd_ofAdd]
        have h1 : ((g⁻¹ : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)) *
            (g : Matrix (Fin 3) (Fin 3) (ZMod 2)) = 1 := by
          rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
        have h3 : ((g⁻¹ : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)) *
            ((g : Matrix (Fin 3) (Fin 3) (ZMod 2)) * Multiplicative.toAdd X *
              ((g⁻¹ : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2))) *
            (g : Matrix (Fin 3) (Fin 3) (ZMod 2)) =
          (((g⁻¹ : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)) *
            (g : Matrix (Fin 3) (Fin 3) (ZMod 2))) * Multiplicative.toAdd X *
            (((g⁻¹ : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)) *
            (g : Matrix (Fin 3) (Fin 3) (ZMod 2))) := by
          simp only [Matrix.mul_assoc]
        rw [h3, h1, Matrix.one_mul, Matrix.mul_one]
      right_inv := fun X => by
        apply Multiplicative.toAdd.injective
        simp only [toAdd_ofAdd]
        have h1 : (g : Matrix (Fin 3) (Fin 3) (ZMod 2)) *
            ((g⁻¹ : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)) = 1 := by
          rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
        have h3 : (g : Matrix (Fin 3) (Fin 3) (ZMod 2)) *
            (((g⁻¹ : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)) * Multiplicative.toAdd X *
              (g : Matrix (Fin 3) (Fin 3) (ZMod 2))) *
            ((g⁻¹ : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)) =
          ((g : Matrix (Fin 3) (Fin 3) (ZMod 2)) *
            ((g⁻¹ : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2))) * Multiplicative.toAdd X *
            ((g : Matrix (Fin 3) (Fin 3) (ZMod 2)) *
            ((g⁻¹ : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2))) := by
          simp only [Matrix.mul_assoc]
        rw [h3, h1, Matrix.one_mul, Matrix.mul_one]
      map_mul' := fun X Y => by
        apply Multiplicative.toAdd.injective
        simp [Matrix.mul_add, Matrix.add_mul] }
  map_one' := by
    ext X
    simp
  map_mul' g h := by
    ext X
    apply Multiplicative.toAdd.injective
    simp [Matrix.mul_assoc]

@[expose] def Adj3 : Subgroup AdjAmb :=
  AddSubgroup.toSubgroup (AddMonoidHom.ker (Matrix.traceAddMonoidHom (Fin 3) (ZMod 2)))

@[expose] def prodAct {G : Type*} [Group G] {A B : Type*} [CommGroup A] [CommGroup B]
    (a : G →* MulAut A) (b : G →* MulAut B) : G →* MulAut (A × B) where
  toFun g :=
    { toFun := fun x => (a g x.1, b g x.2)
      invFun := fun x => (a g⁻¹ x.1, b g⁻¹ x.2)
      left_inv := fun x => by
        ext
        · simp only
          rw [← MulAut.mul_apply, ← map_mul, inv_mul_cancel, map_one, MulAut.one_apply]
        · simp only
          rw [← MulAut.mul_apply, ← map_mul, inv_mul_cancel, map_one, MulAut.one_apply]
      right_inv := fun x => by
        ext
        · simp only
          rw [← MulAut.mul_apply, ← map_mul, mul_inv_cancel, map_one, MulAut.one_apply]
        · simp only
          rw [← MulAut.mul_apply, ← map_mul, mul_inv_cancel, map_one, MulAut.one_apply]
      map_mul' := fun x y => by
        ext <;> simp }
  map_one' := by
    ext x <;> simp
  map_mul' g h := by
    ext x <;> simp

@[expose] def ModIsoSub {G : Type*} [Group G] {A B : Type*} [CommGroup A] [CommGroup B]
    (a : G →* MulAut A) (b : G →* MulAut B) (S : Subgroup B) : Prop :=
  ∃ e : A →* B, Function.Injective e ∧ e.range = S ∧ ∀ (g : G) (x : A), e (a g x) = b g (e x)

@[expose] def ModIso {G : Type*} [Group G] {A B : Type*} [CommGroup A] [CommGroup B]
    (a : G →* MulAut A) (b : G →* MulAut B) : Prop :=
  ModIsoSub a b ⊤

@[expose] def IsoSecIn {G : Type*} [Group G] {X : Type*} [CommGroup X] (ρ : G →* MulAut X)
    (U Z : Subgroup X) (A : Type*) [CommGroup A] (act : G →* MulAut A) (S : Subgroup A) : Prop :=
  Z ≤ U ∧ (∀ g, ∀ u ∈ U, ρ g u ∈ U) ∧ (∀ g, ∀ z ∈ Z, ρ g z ∈ Z) ∧
  ∃ β : ↥U →* A, β.range = S ∧ (∀ u : ↥U, β u = 1 ↔ (u : X) ∈ Z) ∧
    ∀ (g : G) (u u' : ↥U), (u' : X) = ρ g u → β u' = act g (β u)

@[expose] def IsQuotOfSub {G : Type*} [Group G] {A B : Type*} [CommGroup A] [CommGroup B]
    (act : G →* MulAut A) (b : G →* MulAut B) (S : Subgroup B) : Prop :=
  ∃ π : ↥S →* A, Function.Surjective π ∧
    ∀ (g : G) (x x' : ↥S), (x' : B) = b g x → π x' = act g (π x)

@[expose] def IsMaxSub {G : Type*} [Group G] {X : Type*} [CommGroup X] (ρ : G →* MulAut X)
    (W N : Subgroup X) : Prop :=
  N < W ∧ (∀ g, ∀ u ∈ N, ρ g u ∈ N) ∧
    ∀ N' : Subgroup X, N ≤ N' → N' ≤ W → (∀ g, ∀ u ∈ N', ρ g u ∈ N') → N' = N ∨ N' = W

@[expose] def radSub {G : Type*} [Group G] {X : Type*} [CommGroup X] (ρ : G →* MulAut X)
    (W : Subgroup X) : Subgroup X :=
  W ⊓ ⨅ (N : Subgroup X) (_ : IsMaxSub ρ W N), N

abbrev PermLT (T : Subgroup (GL (Fin 3) (ZMod 2))) : Type :=
  Multiplicative ((GL (Fin 3) (ZMod 2) ⧸ T) → ZMod 2)

@[expose] def permLH (H : Subgroup (GL (Fin 3) (ZMod 2))) :
    GL (Fin 3) (ZMod 2) →* MulAut (Multiplicative ((GL (Fin 3) (ZMod 2) ⧸ H) → ZMod 2)) :=
  permModAct (GL (Fin 3) (ZMod 2)) (GL (Fin 3) (ZMod 2) ⧸ H)

end CFSG.ASVolI.ChH

namespace CFSG.ASVolI

open CFSG.Quasithin CFSG.ASVolI.ChH

@[expose] def H_6_1 : Prop :=
  (IsIrredOn modTriv.range ⊤ ∧ IsIrredOn modNat.range ⊤ ∧ IsIrredOn modDual.range ⊤ ∧
    IsIrredOn (adjAmbAct.range) Adj3) ∧
  (Nat.card (Multiplicative (ZMod 2)) = 2 ^ 1 ∧ Nat.card (Multiplicative V3) = 2 ^ 3 ∧
    Nat.card Adj3 = 2 ^ 8) ∧
  (¬ ModIso modTriv modNat ∧ ¬ ModIso modTriv modDual ∧ ¬ ModIso modNat modDual ∧
    ¬ ModIsoSub modTriv adjAmbAct Adj3 ∧ ¬ ModIsoSub modNat adjAmbAct Adj3 ∧
    ¬ ModIsoSub modDual adjAmbAct Adj3) ∧
  (∀ (A : Type) [CommGroup A] [Finite A], (∀ a : A, a ^ 2 = 1) →
    ∀ act : GL (Fin 3) (ZMod 2) →* MulAut A, IsIrredOn act.range ⊤ →
      ModIso act modTriv ∨ ModIso act modNat ∨ ModIso act modDual ∨ ModIsoSub act adjAmbAct Adj3)

section H61

private abbrev H61_TZ : Type := ↥(CFSG.ProperTwoGeneratedCore.BinaryThreeSpace.traceZero)

private abbrev H61_M3 : Type := Matrix (Fin 3) (Fin 3) (ZMod 2)

private theorem H61_zmod2 : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide

private def H61_subOfMul {E : Type} [AddCommGroup E] [Module (ZMod 2) E]
    (U : Subgroup (Multiplicative E)) : Submodule (ZMod 2) E where
  carrier := {x | Multiplicative.ofAdd x ∈ U}
  add_mem' := fun {x y} hx hy => by
    show Multiplicative.ofAdd (x + y) ∈ U
    rw [ofAdd_add]
    exact U.mul_mem hx hy
  zero_mem' := by
    show Multiplicative.ofAdd (0 : E) ∈ U
    rw [ofAdd_zero]
    exact U.one_mem
  smul_mem' := fun c {x} hx => by
    show Multiplicative.ofAdd (c • x) ∈ U
    rcases H61_zmod2 c with rfl | rfl
    · rw [zero_smul, ofAdd_zero]
      exact U.one_mem
    · rw [one_smul]
      exact hx

private def H61_linRep {A : Type} [CommGroup A] [Module (ZMod 2) (Additive A)]
    (act : GL (Fin 3) (ZMod 2) →* MulAut A) :
    GL (Fin 3) (ZMod 2) →* (Additive A ≃ₗ[ZMod 2] Additive A) where
  toFun g :=
    { toFun := fun x => MulEquiv.toAdditive (act g) x
      map_add' := fun x y => map_add (MulEquiv.toAdditive (act g)) x y
      map_smul' := fun c x => ZMod.map_smul (MulEquiv.toAdditive (act g)) c x
      invFun := fun x => (MulEquiv.toAdditive (act g)).symm x
      left_inv := fun x => (MulEquiv.toAdditive (act g)).symm_apply_apply x
      right_inv := fun x => (MulEquiv.toAdditive (act g)).apply_symm_apply x }
  map_one' := LinearEquiv.ext fun x => by
    show Additive.ofMul (act 1 (Additive.toMul x)) = x
    rw [map_one, MulAut.one_apply]
    rfl
  map_mul' g h := LinearEquiv.ext fun x => by
    show Additive.ofMul (act (g * h) (Additive.toMul x)) =
      Additive.ofMul (act g (Additive.toMul (Additive.ofMul (act h (Additive.toMul x)))))
    rw [map_mul, MulAut.mul_apply]
    rfl

private theorem H61_isIrrRep_linRep {A : Type} [CommGroup A] [Module (ZMod 2) (Additive A)]
    {act : GL (Fin 3) (ZMod 2) →* MulAut A} (hirr : IsIrredOn act.range ⊤) :
    CFSG.QuasithinUnique.Setup.Family.IsIrrRep (H61_linRep act) := by
  obtain ⟨hne, hU⟩ := hirr
  have hnt : Nontrivial (Additive A) := by
    by_contra hnt
    apply hne
    rw [eq_bot_iff]
    intro a _
    rw [Subgroup.mem_bot]
    by_contra ha
    exact hnt ⟨⟨Additive.ofMul a, 0, fun h => ha (ofMul_eq_zero.1 h)⟩⟩
  refine ⟨hnt, fun g => map_zero (H61_linRep act g), fun N hN => ?_⟩
  obtain ⟨U, hUdef⟩ : ∃ U : Subgroup A, ∀ a, a ∈ U ↔ Additive.ofMul a ∈ N := by
    refine ⟨{ carrier := {a | Additive.ofMul a ∈ N}
              mul_mem' := fun {a b} ha hb => ?_
              one_mem' := ?_
              inv_mem' := fun {a} ha => ?_ }, fun a => Iff.rfl⟩
    · have ha' : Additive.ofMul a ∈ N := ha
      have hb' : Additive.ofMul b ∈ N := hb
      show Additive.ofMul (a * b) ∈ N
      rw [ofMul_mul]
      exact N.add_mem ha' hb'
    · show Additive.ofMul (1 : A) ∈ N
      rw [ofMul_one]
      exact N.zero_mem
    · have ha' : Additive.ofMul a ∈ N := ha
      show Additive.ofMul a⁻¹ ∈ N
      rw [ofMul_inv]
      exact N.neg_mem ha'
  have hUinv : ∀ l ∈ act.range, ∀ u ∈ U, l u ∈ U := by
    rintro l ⟨g, rfl⟩ u hu
    rw [hUdef] at hu ⊢
    exact hN g _ hu
  rcases hU U le_top hUinv with hUb | hUt
  · left
    rw [Submodule.eq_bot_iff]
    intro x hx
    have hxU : Additive.toMul x ∈ U := by
      rw [hUdef, ofMul_toMul]
      exact hx
    rw [hUb, Subgroup.mem_bot] at hxU
    exact Additive.toMul.injective (hxU.trans toMul_zero.symm)
  · right
    rw [eq_top_iff]
    intro x _
    have hxU : Additive.toMul x ∈ U := by
      rw [hUt]
      exact Subgroup.mem_top _
    rw [hUdef, ofMul_toMul] at hxU
    exact hxU

private theorem H61_isIrredOn_of_isIrrRep {E : Type} [AddCommGroup E] [Module (ZMod 2) E]
    {ρ : GL (Fin 3) (ZMod 2) →* (E ≃ₗ[ZMod 2] E)}
    (hρ : CFSG.QuasithinUnique.Setup.Family.IsIrrRep ρ)
    {b : GL (Fin 3) (ZMod 2) →* MulAut (Multiplicative E)}
    (hb : ∀ (g : GL (Fin 3) (ZMod 2)) (x : Multiplicative E),
      b g x = Multiplicative.ofAdd (ρ g (Multiplicative.toAdd x))) :
    IsIrredOn b.range ⊤ := by
  obtain ⟨hnt, -, hirr⟩ := hρ
  obtain ⟨x0, hx0⟩ := exists_ne (0 : E)
  refine ⟨fun htop => ?_, fun U _ hU => ?_⟩
  · have hmem : Multiplicative.ofAdd x0 ∈ (⊤ : Subgroup (Multiplicative E)) :=
      Subgroup.mem_top _
    rw [htop, Subgroup.mem_bot] at hmem
    exact hx0 (ofAdd_eq_one.1 hmem)
  · have hNinv : ∀ (g : GL (Fin 3) (ZMod 2)), ∀ x ∈ H61_subOfMul U, ρ g x ∈ H61_subOfMul U := by
      intro g x hx
      have hx' : Multiplicative.ofAdd x ∈ U := hx
      show Multiplicative.ofAdd (ρ g x) ∈ U
      have key : Multiplicative.ofAdd (ρ g x) = b g (Multiplicative.ofAdd x) := (hb g _).symm
      rw [key]
      exact hU (b g) (MonoidHom.mem_range.2 ⟨g, rfl⟩) _ hx'
    rcases hirr (H61_subOfMul U) hNinv with hN | hN
    · left
      rw [eq_bot_iff]
      intro u hu
      rw [Subgroup.mem_bot]
      have h1 : Multiplicative.toAdd u ∈ H61_subOfMul U := by
        show Multiplicative.ofAdd (Multiplicative.toAdd u) ∈ U
        exact hu
      rw [hN, Submodule.mem_bot] at h1
      exact Multiplicative.toAdd.injective (h1.trans toAdd_one.symm)
    · right
      rw [eq_top_iff]
      intro u _
      have h1 : Multiplicative.toAdd u ∈ H61_subOfMul U := by
        rw [hN]
        exact Submodule.mem_top
      have h2 : Multiplicative.ofAdd (Multiplicative.toAdd u) ∈ U := h1
      exact h2

private theorem H61_mem_Adj3 (X : AdjAmb) : X ∈ Adj3 ↔ (Multiplicative.toAdd X).trace = 0 :=
  Iff.rfl

private def H61_adjEquiv : ↥Adj3 ≃ H61_TZ where
  toFun x := ⟨Multiplicative.toAdd (x : AdjAmb),
    CFSG.QuasithinUnique.Setup.Family.mem_traceZero_iff_trace.2 ((H61_mem_Adj3 _).1 x.2)⟩
  invFun y := ⟨Multiplicative.ofAdd (y : H61_M3), (H61_mem_Adj3 _).2
    (CFSG.QuasithinUnique.Setup.Family.mem_traceZero_iff_trace.1 y.2)⟩
  left_inv x := Subtype.ext rfl
  right_inv y := Subtype.ext rfl

private theorem H61_natCard_Adj3 : Nat.card Adj3 = 256 :=
  (Nat.card_congr H61_adjEquiv).trans CFSG.QuasithinUnique.Setup.Family.natCard_traceZero

private def H61_subOfAdj (U : Subgroup AdjAmb) : Submodule (ZMod 2) H61_TZ where
  carrier := {x | Multiplicative.ofAdd (x : H61_M3) ∈ U}
  add_mem' := fun {x y} hx hy => by
    show Multiplicative.ofAdd (((x + y : H61_TZ)) : H61_M3) ∈ U
    rw [Submodule.coe_add, ofAdd_add]
    exact U.mul_mem hx hy
  zero_mem' := by
    show Multiplicative.ofAdd (((0 : H61_TZ)) : H61_M3) ∈ U
    rw [Submodule.coe_zero, ofAdd_zero]
    exact U.one_mem
  smul_mem' := fun c {x} hx => by
    show Multiplicative.ofAdd (((c • x : H61_TZ)) : H61_M3) ∈ U
    rw [Submodule.coe_smul]
    rcases H61_zmod2 c with rfl | rfl
    · rw [zero_smul, ofAdd_zero]
      exact U.one_mem
    · rw [one_smul]
      exact hx

private theorem H61_isIrredOn_adj : IsIrredOn adjAmbAct.range Adj3 := by
  obtain ⟨hnt, -, hN⟩ := CFSG.QuasithinUnique.Setup.Family.isIrr_repA
  refine ⟨fun h => ?_, fun U hUle hU => ?_⟩
  · obtain ⟨y, hy⟩ := exists_ne (0 : H61_TZ)
    have hmem : Multiplicative.ofAdd (y : H61_M3) ∈ Adj3 :=
      (H61_mem_Adj3 _).2 (CFSG.QuasithinUnique.Setup.Family.mem_traceZero_iff_trace.1 y.2)
    have h1 : Multiplicative.ofAdd (y : H61_M3) = 1 :=
      (Subgroup.eq_bot_iff_forall Adj3).1 h _ hmem
    apply hy
    apply Subtype.ext
    have h2 := congrArg Multiplicative.toAdd h1
    rw [toAdd_ofAdd, toAdd_one] at h2
    exact h2
  · have hNinv : ∀ (g : GL (Fin 3) (ZMod 2)), ∀ x ∈ H61_subOfAdj U,
        CFSG.QuasithinUnique.Setup.Family.repA g x ∈ H61_subOfAdj U := by
      intro g x hx
      have hx' : Multiplicative.ofAdd (x : H61_M3) ∈ U := hx
      show Multiplicative.ofAdd (((CFSG.QuasithinUnique.Setup.Family.repA g x : H61_TZ)) :
        H61_M3) ∈ U
      rw [CFSG.QuasithinUnique.Setup.Family.repA_apply]
      exact hU (adjAmbAct g) ⟨g, rfl⟩ _ hx'
    rcases hN (H61_subOfAdj U) hNinv with hb | ht
    · left
      rw [eq_bot_iff]
      intro u hu
      rw [Subgroup.mem_bot]
      have h1 : H61_adjEquiv ⟨u, hUle hu⟩ ∈ H61_subOfAdj U := by
        show Multiplicative.ofAdd (Multiplicative.toAdd u) ∈ U
        exact hu
      rw [hb, Submodule.mem_bot] at h1
      have h2 : Multiplicative.toAdd u = 0 := congrArg Subtype.val h1
      exact Multiplicative.toAdd.injective (h2.trans toAdd_one.symm)
    · right
      apply le_antisymm hUle
      intro u hu
      have h1 : H61_adjEquiv ⟨u, hu⟩ ∈ H61_subOfAdj U := by
        rw [ht]
        exact Submodule.mem_top
      have h2 : Multiplicative.ofAdd (Multiplicative.toAdd u) ∈ U := h1
      exact h2

private theorem H61_modIsoSub_of_equiv {A : Type} [CommGroup A] [Module (ZMod 2) (Additive A)]
    {act : GL (Fin 3) (ZMod 2) →* MulAut A} {W : Type} [AddCommGroup W] [Module (ZMod 2) W]
    {ρ : GL (Fin 3) (ZMod 2) →* (W ≃ₗ[ZMod 2] W)}
    {b : GL (Fin 3) (ZMod 2) →* MulAut (Multiplicative W)}
    (hb : ∀ (g : GL (Fin 3) (ZMod 2)) (x : Multiplicative W),
      b g x = Multiplicative.ofAdd (ρ g (Multiplicative.toAdd x)))
    (f : W ≃ₗ[ZMod 2] Additive A)
    (hf : ∀ (g : GL (Fin 3) (ZMod 2)) (x : W), f (ρ g x) = H61_linRep act g (f x)) :
    ModIsoSub act b ⊤ := by
  let e : A →* Multiplicative W :=
    { toFun := fun a => Multiplicative.ofAdd (f.symm (Additive.ofMul a))
      map_one' := by
        show Multiplicative.ofAdd (f.symm (Additive.ofMul (1 : A))) = 1
        rw [ofMul_one, map_zero, ofAdd_zero]
      map_mul' := fun a a' => by
        show Multiplicative.ofAdd (f.symm (Additive.ofMul (a * a'))) =
          Multiplicative.ofAdd (f.symm (Additive.ofMul a)) *
            Multiplicative.ofAdd (f.symm (Additive.ofMul a'))
        rw [ofMul_mul, map_add, ofAdd_add] }
  unfold ModIsoSub
  refine ⟨e, ?_, ?_, ?_⟩
  · intro a a' h
    have h' : Multiplicative.ofAdd (f.symm (Additive.ofMul a)) =
        Multiplicative.ofAdd (f.symm (Additive.ofMul a')) := h
    have h1 : f.symm (Additive.ofMul a) = f.symm (Additive.ofMul a') :=
      Multiplicative.ofAdd.injective h'
    exact Additive.ofMul.injective (f.symm.injective h1)
  · rw [MonoidHom.range_eq_top]
    intro y
    refine ⟨Additive.toMul (f (Multiplicative.toAdd y)), ?_⟩
    show Multiplicative.ofAdd (f.symm (f (Multiplicative.toAdd y))) = y
    rw [LinearEquiv.symm_apply_apply, ofAdd_toAdd]
  · intro g a
    show Multiplicative.ofAdd (f.symm (Additive.ofMul (act g a))) =
      b g (Multiplicative.ofAdd (f.symm (Additive.ofMul a)))
    rw [hb]
    congr 1
    apply f.injective
    rw [LinearEquiv.apply_symm_apply, hf, toAdd_ofAdd, LinearEquiv.apply_symm_apply]
    rfl

private theorem H61_modIsoSub_adj_of_equiv {A : Type} [CommGroup A]
    [Module (ZMod 2) (Additive A)] {act : GL (Fin 3) (ZMod 2) →* MulAut A}
    (f : H61_TZ ≃ₗ[ZMod 2] Additive A)
    (hf : ∀ (g : GL (Fin 3) (ZMod 2)) (x : H61_TZ),
      f (CFSG.QuasithinUnique.Setup.Family.repA g x) = H61_linRep act g (f x)) :
    ModIsoSub act adjAmbAct Adj3 := by
  let e : A →* AdjAmb :=
    { toFun := fun a => Multiplicative.ofAdd ((f.symm (Additive.ofMul a) : H61_TZ) : H61_M3)
      map_one' := by
        show Multiplicative.ofAdd ((f.symm (Additive.ofMul (1 : A)) : H61_TZ) : H61_M3) = 1
        rw [ofMul_one, map_zero, Submodule.coe_zero, ofAdd_zero]
      map_mul' := fun a a' => by
        show Multiplicative.ofAdd ((f.symm (Additive.ofMul (a * a')) : H61_TZ) : H61_M3) =
          Multiplicative.ofAdd ((f.symm (Additive.ofMul a) : H61_TZ) : H61_M3) *
            Multiplicative.ofAdd ((f.symm (Additive.ofMul a') : H61_TZ) : H61_M3)
        rw [ofMul_mul, map_add, Submodule.coe_add, ofAdd_add] }
  unfold ModIsoSub
  refine ⟨e, ?_, ?_, ?_⟩
  · intro a a' h
    have h' : Multiplicative.ofAdd ((f.symm (Additive.ofMul a) : H61_TZ) : H61_M3) =
        Multiplicative.ofAdd ((f.symm (Additive.ofMul a') : H61_TZ) : H61_M3) := h
    have h1 := Multiplicative.ofAdd.injective h'
    have h2 : f.symm (Additive.ofMul a) = f.symm (Additive.ofMul a') := Subtype.ext h1
    exact Additive.ofMul.injective (f.symm.injective h2)
  · ext X
    constructor
    · intro hX
      obtain ⟨a, rfl⟩ := MonoidHom.mem_range.1 hX
      exact (H61_mem_Adj3 _).2
        (CFSG.QuasithinUnique.Setup.Family.mem_traceZero_iff_trace.1 (f.symm (Additive.ofMul a)).2)
    · intro hX
      obtain ⟨y, hy1⟩ : ∃ y : H61_TZ, (y : H61_M3) = Multiplicative.toAdd X :=
        ⟨⟨Multiplicative.toAdd X,
          CFSG.QuasithinUnique.Setup.Family.mem_traceZero_iff_trace.2 ((H61_mem_Adj3 X).1 hX)⟩,
          rfl⟩
      refine MonoidHom.mem_range.2 ⟨Additive.toMul (f y), ?_⟩
      show Multiplicative.ofAdd ((f.symm (f y) : H61_TZ) : H61_M3) = X
      rw [LinearEquiv.symm_apply_apply, hy1]
      exact ofAdd_toAdd X
  · intro g a
    show Multiplicative.ofAdd ((f.symm (Additive.ofMul (act g a)) : H61_TZ) : H61_M3) =
      adjAmbAct g (Multiplicative.ofAdd ((f.symm (Additive.ofMul a) : H61_TZ) : H61_M3))
    have key : f.symm (Additive.ofMul (act g a)) =
        CFSG.QuasithinUnique.Setup.Family.repA g (f.symm (Additive.ofMul a)) := by
      apply f.injective
      rw [LinearEquiv.apply_symm_apply, hf, LinearEquiv.apply_symm_apply]
      rfl
    rw [key, CFSG.QuasithinUnique.Setup.Family.repA_apply]
    rfl

private theorem H61_modIso_of_modIsoSub {W : Type} [AddCommGroup W] [Module (ZMod 2) W]
    {ρ ρ' : GL (Fin 3) (ZMod 2) →* (W ≃ₗ[ZMod 2] W)}
    {b b' : GL (Fin 3) (ZMod 2) →* MulAut (Multiplicative W)}
    (hb : ∀ (g : GL (Fin 3) (ZMod 2)) (x : Multiplicative W),
      b g x = Multiplicative.ofAdd (ρ g (Multiplicative.toAdd x)))
    (hb' : ∀ (g : GL (Fin 3) (ZMod 2)) (x : Multiplicative W),
      b' g x = Multiplicative.ofAdd (ρ' g (Multiplicative.toAdd x)))
    (h : ModIsoSub b b' ⊤) :
    CFSG.QuasithinUnique.Setup.Family.ModIso ρ ρ' := by
  obtain ⟨e, hinj, hrange, heq⟩ := h
  have hsurj : Function.Surjective e := MonoidHom.range_eq_top.1 hrange
  let φ : W →+ W :=
    { toFun := fun w => Multiplicative.toAdd (e (Multiplicative.ofAdd w))
      map_zero' := by
        show Multiplicative.toAdd (e (Multiplicative.ofAdd 0)) = 0
        rw [ofAdd_zero, map_one, toAdd_one]
      map_add' := fun w w' => by
        show Multiplicative.toAdd (e (Multiplicative.ofAdd (w + w'))) =
          Multiplicative.toAdd (e (Multiplicative.ofAdd w)) +
            Multiplicative.toAdd (e (Multiplicative.ofAdd w'))
        rw [ofAdd_add, map_mul, toAdd_mul] }
  have hφinj : Function.Injective φ := by
    intro w w' h1
    have h2 : e (Multiplicative.ofAdd w) = e (Multiplicative.ofAdd w') :=
      Multiplicative.toAdd.injective h1
    exact Multiplicative.ofAdd.injective (hinj h2)
  have hφsurj : Function.Surjective φ := by
    intro w'
    obtain ⟨z, hz⟩ := hsurj (Multiplicative.ofAdd w')
    refine ⟨Multiplicative.toAdd z, ?_⟩
    show Multiplicative.toAdd (e (Multiplicative.ofAdd (Multiplicative.toAdd z))) = w'
    rw [ofAdd_toAdd, hz, toAdd_ofAdd]
  unfold CFSG.QuasithinUnique.Setup.Family.ModIso CFSG.QuasithinUnique.Setup.Family.ActIso
  refine ⟨LinearEquiv.ofBijective (φ.toZModLinearMap 2) ⟨hφinj, hφsurj⟩, fun g x => ?_⟩
  have h1 := heq g (Multiplicative.ofAdd x)
  rw [hb, hb', toAdd_ofAdd] at h1
  have h2 := congrArg Multiplicative.toAdd h1
  rw [toAdd_ofAdd] at h2
  exact h2

private theorem H61_natCard_le {A B : Type} [CommGroup A] [CommGroup B] [Finite A]
    {a : GL (Fin 3) (ZMod 2) →* MulAut A} {b : GL (Fin 3) (ZMod 2) →* MulAut B}
    {S : Subgroup B} (h : ModIsoSub a b S) : Nat.card S ≤ Nat.card A := by
  obtain ⟨e, -, hrange, -⟩ := h
  have hmem : ∀ x : A, e x ∈ S := fun x => by
    rw [← hrange]
    exact MonoidHom.mem_range.2 ⟨x, rfl⟩
  refine Nat.card_le_card_of_surjective (fun x : A => (⟨e x, hmem x⟩ : S)) ?_
  rintro ⟨s, hs⟩
  rw [← hrange] at hs
  obtain ⟨x, hx⟩ := hs
  exact ⟨x, Subtype.ext hx⟩

private theorem H61_natCard_top {G : Type} [Group G] :
    Nat.card (⊤ : Subgroup G) = Nat.card G :=
  Nat.card_congr Subgroup.topEquiv.toEquiv

private theorem H61_natCard_F2 : Nat.card (Multiplicative (ZMod 2)) = 2 :=
  Nat.card_zmod 2

private theorem H61_natCard_V3 : Nat.card (Multiplicative V3) = 8 :=
  CFSG.QuasithinUnique.Setup.Family.natCard_Vec3

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent in
theorem as_H_6_1 : H_6_1 := by
  refine ⟨⟨H61_isIrredOn_of_isIrrRep CFSG.QuasithinUnique.Setup.Family.isIrr_repTriv
      (b := modTriv) (fun _ _ => rfl),
    H61_isIrredOn_of_isIrrRep CFSG.QuasithinUnique.Setup.Family.isIrr_repV
      (b := modNat) (fun _ _ => rfl),
    H61_isIrredOn_of_isIrrRep CFSG.QuasithinUnique.Setup.Family.isIrr_repDual
      (b := modDual) (fun _ _ => rfl),
    H61_isIrredOn_adj⟩,
    ⟨H61_natCard_F2.trans (by norm_num), H61_natCard_V3.trans (by norm_num),
      H61_natCard_Adj3.trans (by norm_num)⟩,
    ⟨fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_⟩, ?_⟩
  · have h' : Nat.card (Multiplicative V3) ≤ Nat.card (Multiplicative (ZMod 2)) :=
      (H61_natCard_top (G := Multiplicative V3)).symm.le.trans (H61_natCard_le h)
    rw [H61_natCard_V3, H61_natCard_F2] at h'
    omega
  · have h' : Nat.card (Multiplicative V3) ≤ Nat.card (Multiplicative (ZMod 2)) :=
      (H61_natCard_top (G := Multiplicative V3)).symm.le.trans (H61_natCard_le h)
    rw [H61_natCard_V3, H61_natCard_F2] at h'
    omega
  · exact CFSG.QuasithinUnique.Setup.Family.not_modIso_repV_repDual
      (H61_modIso_of_modIsoSub (ρ := CFSG.QuasithinUnique.Setup.Family.repV)
        (ρ' := CFSG.QuasithinUnique.Setup.Family.repDual) (b := modNat) (b' := modDual)
        (fun _ _ => rfl) (fun _ _ => rfl) h)
  · have h' : Nat.card Adj3 ≤ Nat.card (Multiplicative (ZMod 2)) := H61_natCard_le h
    rw [H61_natCard_Adj3, H61_natCard_F2] at h'
    omega
  · have h' : Nat.card Adj3 ≤ Nat.card (Multiplicative V3) := H61_natCard_le h
    rw [H61_natCard_Adj3, H61_natCard_V3] at h'
    omega
  · have h' : Nat.card Adj3 ≤ Nat.card (Multiplicative V3) := H61_natCard_le h
    rw [H61_natCard_Adj3, H61_natCard_V3] at h'
    omega
  · intro A _ _ h2 act hirr
    letI : Module (ZMod 2) (Additive A) := AddCommGroup.zmodModule (n := 2) (fun x => by
      rw [two_nsmul]
      apply Additive.toMul.injective
      rw [toMul_add, toMul_zero, ← sq]
      exact h2 _)
    rcases CFSG.QuasithinUnique.Setup.Family.irreducible_binary_GL3_classification
        (E := Additive A) (H61_linRep act) (H61_isIrrRep_linRep hirr) with h | h | h | h
    · obtain ⟨f, hf⟩ := h
      exact Or.inl (H61_modIsoSub_of_equiv (ρ := CFSG.QuasithinUnique.Setup.Family.repTriv)
        (b := modTriv) (fun _ _ => rfl) f hf)
    · obtain ⟨f, hf⟩ := h
      exact Or.inr (Or.inl (H61_modIsoSub_of_equiv (ρ := CFSG.QuasithinUnique.Setup.Family.repV)
        (b := modNat) (fun _ _ => rfl) f hf))
    · obtain ⟨f, hf⟩ := h
      exact Or.inr (Or.inr (Or.inl (H61_modIsoSub_of_equiv
        (ρ := CFSG.QuasithinUnique.Setup.Family.repDual) (b := modDual) (fun _ _ => rfl) f hf)))
    · obtain ⟨f, hf⟩ := h
      exact Or.inr (Or.inr (Or.inr (H61_modIsoSub_adj_of_equiv f hf)))

end H61

@[expose] def H_6_2 : Prop :=
  ∀ (T : Subgroup (GL (Fin 3) (ZMod 2))) (p : V3) (l : Submodule (ZMod 2) V3), HypH5 T p l →
    (∃ U₁ U₂ U₃ U₄ : Subgroup (PermLT T),
      (∀ g, ∀ u ∈ U₁, permLH T g u ∈ U₁) ∧ (∀ g, ∀ u ∈ U₂, permLH T g u ∈ U₂) ∧
      (∀ g, ∀ u ∈ U₃, permLH T g u ∈ U₃) ∧ (∀ g, ∀ u ∈ U₄, permLH T g u ∈ U₄) ∧
      U₁ ⊔ U₂ ⊔ U₃ ⊔ U₄ = ⊤ ∧
      U₁ ⊓ (U₂ ⊔ U₃ ⊔ U₄) = ⊥ ∧ U₂ ⊓ (U₁ ⊔ U₃ ⊔ U₄) = ⊥ ∧
      U₃ ⊓ (U₁ ⊔ U₂ ⊔ U₄) = ⊥ ∧ U₄ ⊓ (U₁ ⊔ U₂ ⊔ U₃) = ⊥ ∧
      IsoSecIn (permLH T) U₁ ⊥ (Multiplicative (ZMod 2)) modTriv ⊤ ∧
      IsoSecIn (permLH T) U₂ ⊥ (Multiplicative ((GL (Fin 3) (ZMod 2) ⧸ Lpt p) → ZMod 2))
        (permLH (Lpt p)) (permCore (GL (Fin 3) (ZMod 2) ⧸ Lpt p)) ∧
      IsoSecIn (permLH T) U₂ (radSub (permLH T) U₂) (Multiplicative V3) modNat ⊤ ∧
      IsoSecIn (permLH T) U₃ ⊥ (Multiplicative ((GL (Fin 3) (ZMod 2) ⧸ Lln l) → ZMod 2))
        (permLH (Lln l)) (permCore (GL (Fin 3) (ZMod 2) ⧸ Lln l)) ∧
      IsoSecIn (permLH T) U₃ (radSub (permLH T) U₃) (Multiplicative V3) modDual ⊤ ∧
      IsoSecIn (permLH T) U₄ ⊥ AdjAmb adjAmbAct Adj3 ∧
      (radSub (permLH T) ⊤ = radSub (permLH T) U₂ ⊔ radSub (permLH T) U₃ ∧
        radSub (permLH T) U₂ ⊓ radSub (permLH T) U₃ = ⊥ ∧
        IsoSecIn (permLH T) (radSub (permLH T) ⊤) ⊥ (Multiplicative V3 × Multiplicative V3)
          (prodAct modNat modDual) ⊤ ∧
        rk ↥(radSub (permLH T) ⊤) = 6))

@[expose] def H_6_3 : Prop :=
  (∃ (ι : ↥Adj3 →* Multiplicative (GL (Fin 3) (ZMod 2) → ZMod 2))
      (π : Multiplicative (GL (Fin 3) (ZMod 2) → ZMod 2) →* AdjAmb),
      (∀ x : ↥Adj3, π (ι x) = (x : AdjAmb)) ∧ (∀ f, π f ∈ Adj3) ∧
      (∀ (g : GL (Fin 3) (ZMod 2)) (x x' : ↥Adj3), (x' : AdjAmb) = adjAmbAct g x →
        ι x' = permModAct (GL (Fin 3) (ZMod 2)) (GL (Fin 3) (ZMod 2)) g (ι x)) ∧
      (∀ (g : GL (Fin 3) (ZMod 2)) (f : Multiplicative (GL (Fin 3) (ZMod 2) → ZMod 2)),
        π (permModAct (GL (Fin 3) (ZMod 2)) (GL (Fin 3) (ZMod 2)) g f) = adjAmbAct g (π f))) ∧
  ((∃ β : AdjAmb → AdjAmb → ZMod 2,
      (∀ u ∈ Adj3, ∀ u' ∈ Adj3, ∀ w ∈ Adj3, β (u * u') w = β u w + β u' w) ∧
      (∀ u ∈ Adj3, ∀ w ∈ Adj3, ∀ w' ∈ Adj3, β u (w * w') = β u w + β u w') ∧
      (∀ (g : GL (Fin 3) (ZMod 2)), ∀ u ∈ Adj3, ∀ w ∈ Adj3, β (adjAmbAct g u) (adjAmbAct g w) = β u w) ∧
      (∀ u ∈ Adj3, u ≠ 1 → ∃ w ∈ Adj3, β u w ≠ 0)) ∧
    (∀ α : MulAut (GL (Fin 3) (ZMod 2)),
      ∃ e : ↥Adj3 →* AdjAmb, Function.Injective e ∧ e.range = Adj3 ∧
        ∀ (g : GL (Fin 3) (ZMod 2)) (x y : ↥Adj3), (y : AdjAmb) = adjAmbAct (α g) x →
          e y = adjAmbAct g (e x))) ∧
  ∀ (T : Subgroup (GL (Fin 3) (ZMod 2))) (p : V3) (l : Submodule (ZMod 2) V3), HypH5 T p l →
    (NoncentralChiefCount {f | ∃ g ∈ Lpt p, f = fun x => adjAmbAct g x} Adj3 3 ∧
      NoncentralChiefCount {f | ∃ g ∈ Lln l, f = fun x => adjAmbAct g x} Adj3 3) ∧
    (∃ m ∈ Adj3, m ≠ 1 ∧ (∀ g ∈ T, adjAmbAct g m = m) ∧
      (∀ m' ∈ Adj3, m' ≠ 1 → (∀ g ∈ T, adjAmbAct g m' = m') → m' = m) ∧
      ∀ g : GL (Fin 3) (ZMod 2), adjAmbAct g m = m → g ∈ T) ∧
    (commOn Adj3 ((Lln l).map adjAmbAct) = Adj3 ∧ commOn Adj3 ((Lpt p).map adjAmbAct) = Adj3)

@[expose] def H_6_4 : Prop :=
  ∀ (R : Type) [Ring R] (M : Type) [AddCommGroup M] [Module R M], IsFiniteLength R M →
  ∀ A B K : Submodule R M, A ⊔ B = ⊤ →
  ∀ (S : Type) [AddCommGroup S] [Module R S], IsSimpleModule R S →
    Nonempty ((↥A ⧸ Module.jacobson R ↥A) ≃ₗ[R] S) →
    (¬ ∃ N₁ N₂ : Submodule R ↥B, N₁ ≤ N₂ ∧ Nonempty ((↥N₂ ⧸ N₁.comap N₂.subtype) ≃ₗ[R] S)) →
      A ≤ K ∨ ∃ N : Submodule R (M ⧸ K), Nonempty (((M ⧸ K) ⧸ N) ≃ₗ[R] S)

private theorem h64_mkQ_zero {R X : Type} [Ring R] [AddCommGroup X] [Module R X]
    (N : Submodule R X) {x : X} (hx : x ∈ N) : N.mkQ x = 0 := by
  rw [← LinearMap.mem_ker, Submodule.ker_mkQ]
  exact hx

private theorem h64_mem_of_mkQ_zero {R X : Type} [Ring R] [AddCommGroup X] [Module R X]
    (N : Submodule R X) {x : X} (h : N.mkQ x = 0) : x ∈ N := by
  rw [← LinearMap.mem_ker, Submodule.ker_mkQ] at h
  exact h

private theorem h64_le_jacobson {R N S : Type} [Ring R] [AddCommGroup N] [Module R N]
    [IsNoetherian R N] [AddCommGroup S] [Module R S] [IsSimpleModule R S]
    (e : (N ⧸ Module.jacobson R N) ≃ₗ[R] S) (L : Submodule R N) (hL : L ≠ ⊤) :
    L ≤ Module.jacobson R N := by
  rcases eq_top_or_exists_le_coatom L with h | ⟨m, hm, hLm⟩
  · exact absurd h hL
  have hJm : Module.jacobson R N ≤ m := sInf_le (s := {n : Submodule R N | IsCoatom n}) hm
  haveI : IsSimpleModule R (N ⧸ Module.jacobson R N) := IsSimpleModule.congr e
  have key : m = Module.jacobson R N := by
    rcases IsSimpleOrder.eq_bot_or_eq_top (m.map (Module.jacobson R N).mkQ) with h0 | htop
    · have h1 := Submodule.comap_map_mkQ (Module.jacobson R N) m
      rw [h0, Submodule.comap_bot, Submodule.ker_mkQ] at h1
      exact le_antisymm (le_trans le_sup_right h1.ge) hJm
    · have h2 := (Submodule.map_mkQ_eq_top (Module.jacobson R N) m).mp htop
      rw [sup_eq_right.mpr hJm] at h2
      exact absurd h2 hm.ne_top
  exact hLm.trans key.le

private theorem h64_lift_surj {R X Y S : Type} [Ring R] [AddCommGroup X] [Module R X]
    [AddCommGroup Y] [Module R Y] [AddCommGroup S] [Module R S]
    (f : X →ₗ[R] Y) (hf : Function.Surjective f) (θ : X →ₗ[R] S)
    (hθ : Function.Surjective θ) (hker : LinearMap.ker f ≤ LinearMap.ker θ) :
    ∃ θ' : Y →ₗ[R] S, Function.Surjective θ' ∧ θ'.comp f = θ := by
  let θ' : Y →ₗ[R] S := (Submodule.liftQ (LinearMap.ker f) θ hker).comp
    (f.quotKerEquivOfSurjective hf).symm.toLinearMap
  have hcomp : θ'.comp f = θ := by
    ext x
    simp [θ', Submodule.liftQ_apply]
  refine ⟨θ', fun s => ?_, hcomp⟩
  obtain ⟨x, rfl⟩ := hθ s
  exact ⟨f x, LinearMap.congr_fun hcomp x⟩

private theorem h64_no_surj {R X S : Type} [Ring R] [AddCommGroup X] [Module R X]
    [AddCommGroup S] [Module R S]
    (h : ¬ ∃ N₁ N₂ : Submodule R X, N₁ ≤ N₂ ∧ Nonempty ((↥N₂ ⧸ N₁.comap N₂.subtype) ≃ₗ[R] S))
    (Q : Submodule R X) (f : ↥Q →ₗ[R] S) (hf : Function.Surjective f) : False := by
  apply h
  have hk : LinearMap.ker Q.subtype ≤ LinearMap.ker f := by
    rw [Submodule.ker_subtype]
    exact bot_le
  refine ⟨(LinearMap.ker f).map Q.subtype, Q, Submodule.map_subtype_le Q _, ?_⟩
  rw [Submodule.comap_map_eq_self hk]
  exact ⟨f.quotKerEquivOfSurjective hf⟩

theorem as_H_6_4 : H_6_4 := by
  intro R _ M _ _ hfin A B K hAB S _ _ hS he hnoSub
  obtain ⟨e⟩ := he
  by_cases hAK : A ≤ K
  · exact Or.inl hAK
  refine Or.inr ?_
  haveI : IsNoetherian R M := (isFiniteLength_iff_isNoetherian_isArtinian.mp hfin).1
  have hJ : ∀ L : Submodule R ↥A, L ≠ ⊤ → L ≤ Module.jacobson R ↥A :=
    fun L hL => h64_le_jacobson e L hL
  let φ : ↥A →ₗ[R] S := e.toLinearMap ∘ₗ (Module.jacobson R ↥A).mkQ
  have hφ : Function.Surjective φ := by
    intro s
    obtain ⟨x, hx⟩ := e.surjective s
    obtain ⟨a, rfl⟩ := (Module.jacobson R ↥A).mkQ_surjective x
    exact ⟨a, hx⟩
  have hφJ : Module.jacobson R ↥A ≤ LinearMap.ker φ := by
    intro x hx
    show e ((Module.jacobson R ↥A).mkQ x) = 0
    rw [h64_mkQ_zero _ hx, map_zero]
  by_cases hAP : A ≤ B ⊔ K
  ·
    exfalso
    let fA : ↥A →ₗ[R] ↥((A ⊔ K).map K.mkQ) :=
      LinearMap.codRestrict _ (K.mkQ ∘ₗ A.subtype)
        (fun a => Submodule.mem_map_of_mem (Submodule.mem_sup_left a.2))
    have hfA : Function.Surjective fA := by
      intro z
      obtain ⟨w, hw, hwz⟩ := Submodule.mem_map.mp z.2
      obtain ⟨a, ha, k, hk, hak⟩ := Submodule.mem_sup.mp hw
      refine ⟨⟨a, ha⟩, Subtype.ext ?_⟩
      show K.mkQ a = (z : M ⧸ K)
      rw [← hwz, ← hak, map_add, h64_mkQ_zero K hk, add_zero]
    have hkerA : LinearMap.ker fA ≤ LinearMap.ker φ := by
      refine (hJ _ ?_).trans hφJ
      intro htop
      apply hAK
      intro a ha
      have hmem : (⟨a, ha⟩ : ↥A) ∈ LinearMap.ker fA := by
        rw [htop]
        exact Submodule.mem_top
      have h0 : K.mkQ a = 0 := congrArg Subtype.val (LinearMap.mem_ker.mp hmem)
      exact h64_mem_of_mkQ_zero K h0
    obtain ⟨θA, hθA, -⟩ := h64_lift_surj fA hfA φ hφ hkerA
    let Q : Submodule R ↥B := (A ⊔ K).comap B.subtype
    let gQ : ↥Q →ₗ[R] ↥((A ⊔ K).map K.mkQ) :=
      LinearMap.codRestrict _ (K.mkQ ∘ₗ B.subtype ∘ₗ Q.subtype)
        (fun q => Submodule.mem_map_of_mem (show ((q : ↥B) : M) ∈ A ⊔ K from q.2))
    have hgQ : Function.Surjective gQ := by
      intro z
      obtain ⟨w, hw, hwz⟩ := Submodule.mem_map.mp z.2
      obtain ⟨a, ha, k, hk, hak⟩ := Submodule.mem_sup.mp hw
      obtain ⟨b, hb, k', hk', hbk⟩ := Submodule.mem_sup.mp (hAP ha)
      have hbW : b ∈ A ⊔ K := by
        rw [eq_sub_of_add_eq hbk]
        exact Submodule.sub_mem _ (Submodule.mem_sup_left ha) (Submodule.mem_sup_right hk')
      refine ⟨⟨⟨b, hb⟩, hbW⟩, Subtype.ext ?_⟩
      show K.mkQ b = (z : M ⧸ K)
      rw [← hwz, ← hak, ← hbk, map_add, map_add, h64_mkQ_zero K hk', h64_mkQ_zero K hk,
        add_zero, add_zero]
    exact h64_no_surj hnoSub Q (θA ∘ₗ gQ) (hθA.comp hgQ)
  ·
    have hρ : Function.Surjective ((B ⊔ K).mkQ ∘ₗ A.subtype) := by
      intro y
      obtain ⟨x, rfl⟩ := (B ⊔ K).mkQ_surjective y
      have hx : x ∈ A ⊔ B := by
        rw [hAB]
        exact Submodule.mem_top
      obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hx
      refine ⟨⟨a, ha⟩, ?_⟩
      show (B ⊔ K).mkQ a = (B ⊔ K).mkQ (a + b)
      rw [map_add, h64_mkQ_zero (B ⊔ K) (Submodule.mem_sup_left hb), add_zero]
    have hker : LinearMap.ker ((B ⊔ K).mkQ ∘ₗ A.subtype) ≠ ⊤ := by
      intro htop
      apply hAP
      intro a ha
      have hmem : (⟨a, ha⟩ : ↥A) ∈ LinearMap.ker ((B ⊔ K).mkQ ∘ₗ A.subtype) := by
        rw [htop]
        exact Submodule.mem_top
      exact h64_mem_of_mkQ_zero (B ⊔ K) (LinearMap.mem_ker.mp hmem)
    have hle : LinearMap.ker ((B ⊔ K).mkQ ∘ₗ A.subtype) ≤ LinearMap.ker φ :=
      (hJ _ hker).trans hφJ
    obtain ⟨θ, hθ, -⟩ := h64_lift_surj _ hρ φ hφ hle
    have hΦ : Function.Surjective (θ ∘ₗ (B ⊔ K).mkQ) := hθ.comp (B ⊔ K).mkQ_surjective
    have hKΦ : K ≤ LinearMap.ker (θ ∘ₗ (B ⊔ K).mkQ) := by
      intro k hk
      show θ ((B ⊔ K).mkQ k) = 0
      rw [h64_mkQ_zero (B ⊔ K) (Submodule.mem_sup_right hk), map_zero]
    have hΘ : Function.Surjective (K.liftQ (θ ∘ₗ (B ⊔ K).mkQ) hKΦ) := by
      intro s
      obtain ⟨m, hm⟩ := hΦ s
      have hcomp := LinearMap.congr_fun (Submodule.liftQ_mkQ K (θ ∘ₗ (B ⊔ K).mkQ) hKΦ) m
      exact ⟨K.mkQ m, hcomp.trans hm⟩
    exact ⟨LinearMap.ker (K.liftQ (θ ∘ₗ (B ⊔ K).mkQ) hKΦ),
      ⟨LinearMap.quotKerEquivOfSurjective _ hΘ⟩⟩

@[expose] def H_6_5 : Prop :=
  ∀ (T : Subgroup (GL (Fin 3) (ZMod 2))) (p : V3) (l : Submodule (ZMod 2) V3), HypH5 T p l →
  ∀ (A : Type) [CommGroup A] [Finite A], (∀ a : A, a ^ 2 = 1) →
  ∀ act : GL (Fin 3) (ZMod 2) →* MulAut A, (∀ g, (∀ a, act g a = a) → g = 1) →
  ∀ m : A, (∀ t ∈ T, act t m = m) →
    Subgroup.closure (Set.range fun g : GL (Fin 3) (ZMod 2) => act g m) = ⊤ →
    rk ↥(Subgroup.closure ((fun g : GL (Fin 3) (ZMod 2) => act g m) '' (Lln l : Set _))) = 2 →
      IsQuotOfSub act (prodAct (permLH (Lpt p)) adjAmbAct)
        ((permCore (GL (Fin 3) (ZMod 2) ⧸ Lpt p)).prod Adj3) ∧
      (ModIsoSub act (permLH (Lpt p)) (permCore (GL (Fin 3) (ZMod 2) ⧸ Lpt p)) ∨
        ModIsoSub act adjAmbAct Adj3 ∨ ModIso act modNat ∨
        ModIsoSub act (prodAct modNat adjAmbAct) ((⊤ : Subgroup (Multiplicative V3)).prod Adj3) ∨
        ModIsoSub act (prodAct (permLH (Lpt p)) adjAmbAct)
          ((permCore (GL (Fin 3) (ZMod 2) ⧸ Lpt p)).prod Adj3))

section HBridge65
open CFSG.Quasithin.MS93 Matrix

set_option synthInstance.maxHeartbeats 400000
private abbrev e1 : Fin 3 → ZMod 2 := ![1, 0, 0]

private def line0 : Submodule (ZMod 2) (Fin 3 → ZMod 2) :=
  LinearMap.ker (LinearMap.proj (R := ZMod 2) (φ := fun _ : Fin 3 => ZMod 2) (2 : Fin 3))

private theorem mem_line0 {v : Fin 3 → ZMod 2} : v ∈ line0 ↔ v 2 = 0 := by
  simp [line0]

private theorem toGL_surjective' :
    Function.Surjective (Matrix.SpecialLinearGroup.toGL :
      Matrix.SpecialLinearGroup (Fin 3) (ZMod 2) →* GL (Fin 3) (ZMod 2)) := by
  intro g
  have hdet : (g : Matrix (Fin 3) (Fin 3) (ZMod 2)).det = 1 := by
    have hu : IsUnit (g : Matrix (Fin 3) (Fin 3) (ZMod 2)).det :=
      (Matrix.isUnit_iff_isUnit_det _).mp g.isUnit
    have hne : (g : Matrix (Fin 3) (Fin 3) (ZMod 2)).det ≠ 0 := hu.ne_zero
    revert hne
    generalize (g : Matrix (Fin 3) (Fin 3) (ZMod 2)).det = d
    revert d
    decide
  exact ⟨⟨(g : Matrix (Fin 3) (Fin 3) (ZMod 2)), hdet⟩, Units.ext rfl⟩

private noncomputable def slGL : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2) ≃* GL (Fin 3) (ZMod 2) :=
  MulEquiv.ofBijective Matrix.SpecialLinearGroup.toGL
    ⟨Matrix.SpecialLinearGroup.toGL_injective, toGL_surjective'⟩

private theorem slGL_coe (g : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) :
    ((slGL g : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)) =
      (g : Matrix (Fin 3) (Fin 3) (ZMod 2)) := rfl

private noncomputable def B0 : Subgroup (GL (Fin 3) (ZMod 2)) :=
  CFSG.Quasithin.MS93.sStar.map slGL.toMonoidHom

private theorem mem_B0 (x : GL (Fin 3) (ZMod 2)) :
    x ∈ B0 ↔ ∃ a b c : ZMod 2,
      (x : Matrix (Fin 3) (Fin 3) (ZMod 2)) = !![1, a, b; 0, 1, c; 0, 0, 1] := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨a, b, c, rfl⟩ := mem_sStar_iff.mp hy
    exact ⟨a, b, c, rfl⟩
  · rintro ⟨a, b, c, hx⟩
    refine ⟨uniTri a b c, mem_sStar_iff.mpr ⟨a, b, c, rfl⟩, ?_⟩
    apply Units.ext
    exact hx.symm

private theorem sylow_smul_mem {G : Type*} [Group G] {p : ℕ} {P : Sylow p G} {g x : G} :
    x ∈ (g • P : Sylow p G) ↔ g⁻¹ * x * g ∈ (P : Subgroup G) := by
  show x ∈ ((g • P : Sylow p G) : Subgroup G) ↔ _
  rw [Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ← map_inv,
    MulAut.smul_def, MulAut.conj_apply, inv_inv]

private theorem sylow_conj (T : Subgroup (GL (Fin 3) (ZMod 2))) (hT : IsPGroup 2 T)
    (hTi : ¬ 2 ∣ T.index) :
    ∃ c : GL (Fin 3) (ZMod 2), ∀ x : GL (Fin 3) (ZMod 2), x ∈ T ↔ c⁻¹ * x * c ∈ B0 := by
  classical
  have hF : Nat.card (ZMod 2) = 2 ^ 1 := by simp
  set Ts : Subgroup (Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) := T.comap slGL.toMonoidHom
    with hTs
  have hmap : Ts.map slGL.toMonoidHom = T :=
    Subgroup.map_comap_eq_self_of_surjective slGL.surjective T
  have hTsP : IsPGroup 2 Ts := by
    have h1 : IsPGroup 2 (Ts.map slGL.toMonoidHom) := by rw [hmap]; exact hT
    exact h1.of_injective (Subgroup.equivMapOfInjective Ts slGL.toMonoidHom slGL.injective).toMonoidHom
      (Subgroup.equivMapOfInjective Ts slGL.toMonoidHom slGL.injective).injective
  have hTsi : ¬ 2 ∣ Ts.index := by
    rw [hTs, Subgroup.index_comap_of_surjective T (f := slGL.toMonoidHom) slGL.surjective]
    exact hTi
  let P' : Sylow 2 (Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) :=
    (isPGroup_sStar hF).toSylow (not_two_dvd_index_sStar hF)
  let Q : Sylow 2 (Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) := hTsP.toSylow hTsi
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) P' Q
  refine ⟨slGL g, fun x => ?_⟩
  obtain ⟨y, rfl⟩ := slGL.surjective x
  have hQ : y ∈ Q ↔ y ∈ Ts := Iff.rfl
  have hA : slGL y ∈ T ↔ y ∈ Ts := by
    rw [hTs, Subgroup.mem_comap]
    rfl
  have hB : slGL y ∈ T ↔ g⁻¹ * y * g ∈ CFSG.Quasithin.MS93.sStar := by
    rw [hA, ← hQ, ← hg, sylow_smul_mem]
    rfl
  rw [hB, B0, Subgroup.mem_map_equiv]
  simp [map_inv, map_mul]

private theorem fix_decide : ∀ v : Fin 3 → ZMod 2,
    (!![1, 1, 0; 0, 1, 0; 0, 0, 1] : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec v = v →
    (!![1, 0, 0; 0, 1, 1; 0, 0, 1] : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec v = v →
    v = 0 ∨ v = e1 := by
  decide

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
private theorem line_decide : ∀ F : Finset (Fin 3 → ZMod 2), (0 : Fin 3 → ZMod 2) ∈ F →
    (∀ a ∈ F, ∀ b ∈ F, a + b ∈ F) → F.card = 4 →
    (∀ v ∈ F, (!![1, 1, 0; 0, 1, 0; 0, 0, 1] : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec v ∈ F) →
    (∀ v ∈ F, (!![1, 0, 0; 0, 1, 1; 0, 0, 1] : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec v ∈ F) →
    F = Finset.univ.filter (fun v : Fin 3 → ZMod 2 => v 2 = 0) := by
  decide +kernel




private theorem natCard_submod_field {K : Type} [Field K] [Fintype K] {V : Type} [AddCommGroup V]
    {inst : Module K V} [Finite V] (W : Submodule K V) :
    Nat.card W = Fintype.card K ^ Module.finrank K W := by
  haveI : Module.Finite K V := Module.Finite.of_finite
  rw [Module.natCard_eq_pow_finrank (K := K) (V := W), Nat.card_eq_fintype_card]

private theorem natCard_of_finrank_two (l : Submodule (ZMod 2) (Fin 3 → ZMod 2))
    (h : Module.finrank (ZMod 2) l = 2) : Nat.card l = 4 := by
  have hc : Nat.card l = Fintype.card (ZMod 2) ^ Module.finrank (ZMod 2) l := natCard_submod_field l
  rw [hc, h, ZMod.card]
  norm_num

private theorem line_unique (P : (Fin 3 → ZMod 2) → Prop) [DecidablePred P] (h0 : P 0)
    (hadd : ∀ a b, P a → P b → P (a + b)) (hcard : (Finset.univ.filter P).card = 4)
    (ht : ∀ v, P v → P ((!![1, 1, 0; 0, 1, 0; 0, 0, 1] : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec v))
    (hu : ∀ v, P v → P ((!![1, 0, 0; 0, 1, 1; 0, 0, 1] : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec v)) :
    ∀ v, P v ↔ v 2 = 0 := by
  have key := line_decide (Finset.univ.filter P)
    (by simpa using h0)
    (by
      intro a ha b hb
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha hb ⊢
      exact hadd a b ha hb)
    hcard
    (by
      intro v hv
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv ⊢
      exact ht v hv)
    (by
      intro v hv
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv ⊢
      exact hu v hv)
  intro v
  have hv : v ∈ Finset.univ.filter P ↔ v ∈ Finset.univ.filter (fun v : Fin 3 → ZMod 2 => v 2 = 0) := by
    rw [key]
  simpa using hv

private theorem card_of_rk_two {A : Type} [CommGroup A] [Finite A] (hA : ∀ a : A, a ^ 2 = 1)
    (W : Subgroup A) (h : CFSG.Quasithin.rk ↥W = 2) : Nat.card W = 4 := by
  have hP : IsPGroup 2 W := fun w => ⟨1, Subtype.ext (by simpa using hA (w : A))⟩
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card).1 hP
  unfold CFSG.Quasithin.rk at h
  rw [hn, padicValNat.prime_pow] at h
  rw [hn, h]
  rfl

private theorem natCard_toAddSubgroup {A : Type} [CommGroup A] (W : Subgroup A) :
    Nat.card ↥(W.toAddSubgroup) = Nat.card ↥W :=
  Nat.card_congr (Equiv.subtypeEquiv Additive.ofMul (fun a => Iff.rfl))

private theorem mem_Lpt (k : GL (Fin 3) (ZMod 2)) (p : Fin 3 → ZMod 2) :
    k ∈ Lpt p ↔ ∀ v ∈ ({p} : Set (Fin 3 → ZMod 2)), (k : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec v = v :=
  Iff.rfl

private theorem mem_Lln (k : GL (Fin 3) (ZMod 2)) (l : Submodule (ZMod 2) (Fin 3 → ZMod 2)) :
    k ∈ Lln l ↔ ∀ v ∈ (l : Set (Fin 3 → ZMod 2)),
      (k : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec v ∈ l ∧
        ((k⁻¹ : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec v ∈ l :=
  Iff.rfl

private theorem mulVec_gl (g h : GL (Fin 3) (ZMod 2)) (v : Fin 3 → ZMod 2) :
    ((g * h : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec v =
      (g : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec ((h : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec v) := by
  rw [Units.val_mul, Matrix.mulVec_mulVec]

private theorem mem_Lp_iff (g : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) :
    g ∈ CFSG.Quasithin.H6.Lp ↔ slGL g ∈ Lpt e1 := by
  rw [CFSG.Quasithin.H6.Lp, MulAction.mem_stabilizer_iff, mem_Lpt]
  have hsm : ∀ v : Fin 3 → ZMod 2, g • v = (g : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec v :=
    fun v => rfl
  constructor
  · intro h v hv
    rw [Set.mem_singleton_iff.mp hv, slGL_coe, ← hsm]
    exact h
  · intro h
    have h' := h e1 (Set.mem_singleton _)
    rw [slGL_coe, ← hsm] at h'
    exact h'

private theorem mem_Ll_iff (g : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) :
    g ∈ CFSG.Quasithin.H6.Ll ↔ slGL g ∈ Lln line0 := by
  have hL : g ∈ CFSG.Quasithin.H6.Ll ↔ CFSG.Quasithin.H6.IsLl g := Iff.rfl
  rw [hL, mem_Lln]
  have hg' : ∀ k : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2), CFSG.Quasithin.H6.IsLl k →
      ∀ w : Fin 3 → ZMod 2, w 2 = 0 → (k : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec w 2 = 0 := by
    rintro k ⟨k20, k21⟩ w hw
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, k20, k21, hw]
  constructor
  · rintro ⟨h20, h21⟩ v hv
    have hv' : v ∈ line0 := hv
    rw [mem_line0] at hv'
    refine ⟨?_, ?_⟩
    · rw [slGL_coe, mem_line0]
      exact hg' g ⟨h20, h21⟩ v hv'
    · rw [← map_inv, slGL_coe, mem_line0]
      exact hg' g⁻¹ (CFSG.Quasithin.H6.isLl_inv g ⟨h20, h21⟩) v hv'
  · intro h
    have h0 := (h (fun i => if i = 0 then 1 else 0) (by simp [mem_line0])).1
    have h1 := (h (fun i => if i = 1 then 1 else 0) (by simp [mem_line0])).1
    rw [slGL_coe, mem_line0] at h0 h1
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three] at h0 h1
    exact ⟨h0, h1⟩


private theorem mulVec_gl' (g h : GL (Fin 3) (ZMod 2)) (v : Fin 3 → ZMod 2) :
    ((g * h : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec v =
      (g : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec ((h : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec v) :=
  mulVec_gl g h v

private theorem mem_Lln_conj (c : GL (Fin 3) (ZMod 2)) (l : Submodule (ZMod 2) (Fin 3 → ZMod 2))
    (hl : ∀ v : Fin 3 → ZMod 2, (c : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec v ∈ l ↔ v 2 = 0)
    (k : GL (Fin 3) (ZMod 2)) : k ∈ Lln line0 ↔ c * k * c⁻¹ ∈ Lln l := by
  have hcinv : ∀ w : Fin 3 → ZMod 2,
      ((c⁻¹ : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec
        ((c : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec w) = w := by
    intro w; rw [← mulVec_gl, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
  have hcc : ∀ w : Fin 3 → ZMod 2,
      (c : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec
        (((c⁻¹ : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec w) = w := by
    intro w; rw [← mulVec_gl, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
  have hconj : ∀ (k' : GL (Fin 3) (ZMod 2)) (w : Fin 3 → ZMod 2),
      ((c * k' * c⁻¹ : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec
        ((c : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec w) =
      (c : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec ((k' : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec w) := by
    intro k' w; rw [mulVec_gl, mulVec_gl, hcinv]
  have hinvconj : ∀ k' : GL (Fin 3) (ZMod 2), (c * k' * c⁻¹ : GL (Fin 3) (ZMod 2))⁻¹ = c * k'⁻¹ * c⁻¹ :=
    fun k' => by group
  rw [mem_Lln, mem_Lln]
  constructor
  · intro h v hv
    obtain ⟨w, rfl⟩ : ∃ w, v = (c : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec w :=
      ⟨_, (hcc v).symm⟩
    have hw : w 2 = 0 := (hl w).1 hv
    obtain ⟨hk1, hk2⟩ := h w ((mem_line0).2 hw)
    rw [hconj]
    rw [hinvconj, hconj]
    exact ⟨(hl _).2 ((mem_line0).1 hk1), (hl _).2 ((mem_line0).1 hk2)⟩
  · intro h w hw
    have hwl : (c : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec w ∈ l := (hl w).2 ((mem_line0).1 hw)
    obtain ⟨h1, h2⟩ := h _ hwl
    rw [hconj] at h1
    rw [hinvconj, hconj] at h2
    exact ⟨(mem_line0).2 ((hl _).1 h1), (mem_line0).2 ((hl _).1 h2)⟩

private theorem fixB0 (v : Fin 3 → ZMod 2)
    (hv : ∀ y ∈ B0, (y : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec v = v) : v = 0 ∨ v = e1 := by
  have tmem : slGL (uniTri 1 0 0) ∈ B0 := (mem_B0 _).2 ⟨1, 0, 0, rfl⟩
  have umem : slGL (uniTri 0 0 1) ∈ B0 := (mem_B0 _).2 ⟨0, 0, 1, rfl⟩
  exact fix_decide v (hv _ tmem) (hv _ umem)

private theorem tG_mem : slGL (uniTri 1 0 0) ∈ B0 := (mem_B0 _).2 ⟨1, 0, 0, rfl⟩
private theorem uG_mem : slGL (uniTri 0 0 1) ∈ B0 := (mem_B0 _).2 ⟨0, 0, 1, rfl⟩

private theorem tG_mat : ((slGL (uniTri 1 0 0) : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)) =
    !![1, 1, 0; 0, 1, 0; 0, 0, 1] := rfl

private theorem uG_mat : ((slGL (uniTri 0 0 1) : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)) =
    !![1, 0, 0; 0, 1, 1; 0, 0, 1] := rfl





private theorem decide_transitive : ∀ v : Fin 3 → ZMod 2, v ≠ 0 →
    ∃ g : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2),
      (g : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec e1 = v := by
  decide +kernel

private theorem mulVec_inv_mulVec_gl (k : GL (Fin 3) (ZMod 2)) (w : Fin 3 → ZMod 2) :
    ((k⁻¹ : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec
      ((k : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec w) = w := by
  rw [← mulVec_gl, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]

private theorem exists_gl_map (p v : Fin 3 → ZMod 2) (hp : p ≠ 0) (hv : v ≠ 0) :
    ∃ g : GL (Fin 3) (ZMod 2), (g : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec p = v := by
  obtain ⟨cp, hcp⟩ := decide_transitive p hp
  obtain ⟨gv, hgv⟩ := decide_transitive v hv
  refine ⟨slGL gv * (slGL cp)⁻¹, ?_⟩
  rw [mulVec_gl]
  have hp' : (slGL cp : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec e1 = p := by
    rw [slGL_coe]; exact hcp
  have h1 : (((slGL cp)⁻¹ : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec p = e1 := by
    rw [← hp']
    exact mulVec_inv_mulVec_gl (slGL cp) e1
  rw [h1, slGL_coe, hgv]

private noncomputable def kappa (p : Fin 3 → ZMod 2) : GL (Fin 3) (ZMod 2) ⧸ Lpt p → Fin 3 → ZMod 2 :=
  Quotient.lift (fun g : GL (Fin 3) (ZMod 2) => (g : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec p)
    (by
      intro a b hab
      have hab' : a⁻¹ * b ∈ Lpt p := QuotientGroup.leftRel_apply.1 hab
      have h1 : ((a⁻¹ * b : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec p = p :=
        (mem_Lpt _ p).1 hab' p (Set.mem_singleton p)
      show (a : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec p = (b : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec p
      calc (a : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec p
          = (a : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec
              (((a⁻¹ * b : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec p) := by
            rw [h1]
        _ = (a * (a⁻¹ * b) : GL (Fin 3) (ZMod 2)).val.mulVec p := (mulVec_gl a (a⁻¹ * b) p).symm
        _ = (b : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec p := by rw [mul_inv_cancel_left])

private theorem kappa_mk (p : Fin 3 → ZMod 2) (g : GL (Fin 3) (ZMod 2)) :
    kappa p (QuotientGroup.mk g) = (g : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec p := rfl

private theorem kappa_smul (p : Fin 3 → ZMod 2) (h : GL (Fin 3) (ZMod 2)) (q : GL (Fin 3) (ZMod 2) ⧸ Lpt p) :
    kappa p (h • q) = (h : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec (kappa p q) := by
  refine QuotientGroup.induction_on q (fun g => ?_)
  show kappa p (QuotientGroup.mk (h * g)) = _
  rw [kappa_mk, kappa_mk, mulVec_gl]

private theorem kappa_ne_zero (p : Fin 3 → ZMod 2) (hp : p ≠ 0) (q : GL (Fin 3) (ZMod 2) ⧸ Lpt p) :
    kappa p q ≠ 0 := by
  refine QuotientGroup.induction_on q (fun g => ?_)
  rw [kappa_mk]
  intro h0
  apply hp
  have := mulVec_inv_mulVec_gl g p
  rw [h0, Matrix.mulVec_zero] at this
  exact this.symm

private theorem kappa_injective (p : Fin 3 → ZMod 2) (q₁ q₂ : GL (Fin 3) (ZMod 2) ⧸ Lpt p)
    (h : kappa p q₁ = kappa p q₂) : q₁ = q₂ := by
  obtain ⟨g₁, rfl⟩ := QuotientGroup.mk_surjective q₁
  obtain ⟨g₂, rfl⟩ := QuotientGroup.mk_surjective q₂
  rw [kappa_mk, kappa_mk] at h
  rw [QuotientGroup.eq, mem_Lpt]
  intro v hv
  rw [Set.mem_singleton_iff.mp hv]
  have h3 : ((g₁⁻¹ * g₂ : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec p = p := by
    rw [mulVec_gl, ← h, mulVec_inv_mulVec_gl]
  exact h3


private noncomputable def cosetFintype (p : Fin 3 → ZMod 2) : Fintype (GL (Fin 3) (ZMod 2) ⧸ Lpt p) :=
  Fintype.ofFinite _

attribute [local instance] cosetFintype

private noncomputable def kappaEquiv (p : Fin 3 → ZMod 2) (hp : p ≠ 0) :
    GL (Fin 3) (ZMod 2) ⧸ Lpt p ≃ {v : Fin 3 → ZMod 2 // v ≠ 0} :=
  Equiv.ofBijective (fun q => ⟨kappa p q, kappa_ne_zero p hp q⟩)
    ⟨fun q₁ q₂ h => kappa_injective p q₁ q₂ (congrArg Subtype.val h), fun w => by
      obtain ⟨g, hg⟩ := exists_gl_map p w.1 hp w.2
      exact ⟨QuotientGroup.mk g, Subtype.ext (by
        show kappa p (QuotientGroup.mk g) = w.1
        rw [kappa_mk]
        exact hg)⟩⟩

private theorem kappaEquiv_apply (p : Fin 3 → ZMod 2) (hp : p ≠ 0) (q : GL (Fin 3) (ZMod 2) ⧸ Lpt p) :
    ((kappaEquiv p hp q : {v : Fin 3 → ZMod 2 // v ≠ 0}) : Fin 3 → ZMod 2) = kappa p q := rfl

private noncomputable def coreVal (f : CFSG.Quasithin.H6.Core) (v : Fin 3 → ZMod 2) : ZMod 2 :=
  f.1 (CFSG.Quasithin.H6.idxOf v)

private noncomputable def PhiFun (p : Fin 3 → ZMod 2) (f : CFSG.Quasithin.H6.Core) :
    GL (Fin 3) (ZMod 2) ⧸ Lpt p → ZMod 2 :=
  fun q => coreVal f (kappa p q)

private theorem sum_sub_ne_zero (G : (Fin 3 → ZMod 2) → ZMod 2) (h0 : G 0 = 0) :
    ∑ w : {v : Fin 3 → ZMod 2 // v ≠ 0}, G w.1 = ∑ v : Fin 3 → ZMod 2, G v := by
  rw [← Finset.sum_subtype (Finset.univ.filter (fun v : Fin 3 → ZMod 2 => v ≠ 0))
    (p := fun v : Fin 3 → ZMod 2 => v ≠ 0) (by intro x; simp) G]
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro x _ hx
  have : x = 0 := by simpa using hx
  rw [this, h0]

private theorem sum_vec_eq_core (f : CFSG.Quasithin.H6.Core) :
    ∑ v : Fin 3 → ZMod 2, coreVal f v = ∑ i : Fin 8, f.1 i := by
  unfold coreVal
  exact Equiv.sum_comp CFSG.Quasithin.H6.vecEquiv.symm (fun i => f.1 i)

private theorem coreVal_zero (f : CFSG.Quasithin.H6.Core) : coreVal f 0 = 0 := by
  unfold coreVal
  have h := (CFSG.Quasithin.H6.mem_coreSub.1 f.2).1
  have : CFSG.Quasithin.H6.idxOf (0 : Fin 3 → ZMod 2) = 0 := by decide
  rw [this]
  exact h

private theorem sum_PhiFun (p : Fin 3 → ZMod 2) (hp : p ≠ 0) (f : CFSG.Quasithin.H6.Core) :
    ∑ q, PhiFun p f q = 0 := by
  have h1 : ∑ q, PhiFun p f q = ∑ w : {v : Fin 3 → ZMod 2 // v ≠ 0}, coreVal f w.1 :=
    Equiv.sum_comp (kappaEquiv p hp) (fun w => coreVal f w.1)
  rw [h1, sum_sub_ne_zero (coreVal f) (coreVal_zero f), sum_vec_eq_core]
  exact (CFSG.Quasithin.H6.mem_coreSub.1 f.2).2


private noncomputable def PhiInvFun (p : Fin 3 → ZMod 2) (hp : p ≠ 0)
    (F : GL (Fin 3) (ZMod 2) ⧸ Lpt p → ZMod 2) (v : Fin 3 → ZMod 2) : ZMod 2 :=
  if h : v = 0 then 0 else F ((kappaEquiv p hp).symm ⟨v, h⟩)

private theorem PhiInvFun_zero (p : Fin 3 → ZMod 2) (hp : p ≠ 0) (F : GL (Fin 3) (ZMod 2) ⧸ Lpt p → ZMod 2) :
    PhiInvFun p hp F 0 = 0 := by
  unfold PhiInvFun
  rw [dif_pos rfl]

private theorem PhiInv_mem (p : Fin 3 → ZMod 2) (hp : p ≠ 0) (F : GL (Fin 3) (ZMod 2) ⧸ Lpt p → ZMod 2)
    (hF : ∑ q, F q = 0) :
    (fun i : Fin 8 => PhiInvFun p hp F (CFSG.Quasithin.H6.vecOf i)) ∈ CFSG.Quasithin.H6.coreSub := by
  rw [CFSG.Quasithin.H6.mem_coreSub]
  refine ⟨?_, ?_⟩
  · have h0 : CFSG.Quasithin.H6.vecOf (0 : Fin 8) = 0 := by decide
    simp only [h0]
    exact PhiInvFun_zero p hp F
  · have hsum : ∑ i : Fin 8, PhiInvFun p hp F (CFSG.Quasithin.H6.vecOf i) =
        ∑ v : Fin 3 → ZMod 2, PhiInvFun p hp F v :=
      Equiv.sum_comp CFSG.Quasithin.H6.vecEquiv (fun v => PhiInvFun p hp F v)
    rw [hsum, ← sum_sub_ne_zero (PhiInvFun p hp F) (PhiInvFun_zero p hp F)]
    unfold PhiInvFun
    have hh : ∑ w : {v : Fin 3 → ZMod 2 // v ≠ 0},
        (if h : w.1 = 0 then (0 : ZMod 2) else F ((kappaEquiv p hp).symm ⟨w.1, h⟩)) =
        ∑ w : {v : Fin 3 → ZMod 2 // v ≠ 0}, F ((kappaEquiv p hp).symm w) := by
      apply Finset.sum_congr rfl
      intro w _
      rw [dif_neg w.2]
    rw [hh]
    exact (Equiv.sum_comp (kappaEquiv p hp).symm F).trans hF


private theorem smul_inv_eq_mulVec (g : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) (v : Fin 3 → ZMod 2) :
    g⁻¹ • v = (((slGL g)⁻¹ : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec v := by
  rw [← map_inv]
  rfl

private theorem PhiFun_smul (p : Fin 3 → ZMod 2) (g : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2))
    (f : CFSG.Quasithin.H6.Core) (q : GL (Fin 3) (ZMod 2) ⧸ Lpt p) :
    PhiFun p (CFSG.Quasithin.H6.ρCore g f) q = PhiFun p f ((slGL g)⁻¹ • q) := by
  unfold PhiFun coreVal
  rw [kappa_smul]
  have hL : (CFSG.Quasithin.H6.ρCore g f).1 (CFSG.Quasithin.H6.idxOf (kappa p q)) =
      f.1 (CFSG.Quasithin.H6.idxOf (g⁻¹ • kappa p q)) := by
    show (g • f).1 _ = _
    rw [CFSG.Quasithin.H6.coe_smul_core, CFSG.Quasithin.H6.permOf_apply,
      CFSG.Quasithin.H6.vecOf_idxOf]
  rw [hL, smul_inv_eq_mulVec]

private theorem PhiFun_smul' (p : Fin 3 → ZMod 2) (h : GL (Fin 3) (ZMod 2))
    (f : CFSG.Quasithin.H6.Core) (q : GL (Fin 3) (ZMod 2) ⧸ Lpt p) :
    PhiFun p (CFSG.Quasithin.H6.ρCore (slGL.symm h) f) q = PhiFun p f (h⁻¹ • q) := by
  rw [PhiFun_smul, MulEquiv.apply_symm_apply]

private theorem PhiFun_smul_fun (p : Fin 3 → ZMod 2) (h : GL (Fin 3) (ZMod 2))
    (f : CFSG.Quasithin.H6.Core) :
    PhiFun p (CFSG.Quasithin.H6.ρCore (slGL.symm h) f) = fun q => PhiFun p f (h⁻¹ • q) := by
  funext q
  exact PhiFun_smul' p h f q

private theorem PhiFun_add (p : Fin 3 → ZMod 2) (f g : CFSG.Quasithin.H6.Core) :
    PhiFun p (f + g) = PhiFun p f + PhiFun p g := by
  funext q
  unfold PhiFun coreVal
  rw [Pi.add_apply]
  show (f.1 + g.1) _ = _
  rw [Pi.add_apply]

private noncomputable def PhiHom (p : Fin 3 → ZMod 2) : CFSG.Quasithin.H6.Core →+ (GL (Fin 3) (ZMod 2) ⧸ Lpt p → ZMod 2) where
  toFun := PhiFun p
  map_zero' := by
    funext q
    unfold PhiFun coreVal
    rfl
  map_add' := PhiFun_add p


private theorem gl_det_one (k : GL (Fin 3) (ZMod 2)) : (k : Matrix (Fin 3) (Fin 3) (ZMod 2)).det = 1 := by
  have hu : IsUnit (k : Matrix (Fin 3) (Fin 3) (ZMod 2)).det :=
    (Matrix.isUnit_iff_isUnit_det _).mp k.isUnit
  have hne : (k : Matrix (Fin 3) (Fin 3) (ZMod 2)).det ≠ 0 := hu.ne_zero
  revert hne
  generalize (k : Matrix (Fin 3) (Fin 3) (ZMod 2)).det = d
  revert d
  decide

private theorem zmod2_mul_eq_one : ∀ a b : ZMod 2, a * b = 1 → a = 1 ∧ b = 1 := by decide

private theorem Lpt_inter_le_B0 (k : GL (Fin 3) (ZMod 2))
    (hk1 : ∀ v ∈ ({e1} : Set (Fin 3 → ZMod 2)), (k : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec v = v)
    (hk2 : ∀ v ∈ (line0 : Set (Fin 3 → ZMod 2)),
      (k : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec v ∈ line0) :
    k ∈ B0 := by
  rw [mem_B0]
  have hcol := hk1 e1 (Set.mem_singleton _)
  have e0 : (![1, 0, 0] : Fin 3 → ZMod 2) ∈ (line0 : Set (Fin 3 → ZMod 2)) := by
    simp [mem_line0]
  have e1' : (![0, 1, 0] : Fin 3 → ZMod 2) ∈ (line0 : Set (Fin 3 → ZMod 2)) := by
    simp [mem_line0]
  have h20 := mem_line0.1 (hk2 _ e0)
  have h21 := mem_line0.1 (hk2 _ e1')
  have hdet := gl_det_one k
  have m00 : (k : Matrix (Fin 3) (Fin 3) (ZMod 2)) 0 0 = 1 := by
    have := congrFun hcol 0
    simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_three, e1] using this
  have m10 : (k : Matrix (Fin 3) (Fin 3) (ZMod 2)) 1 0 = 0 := by
    have := congrFun hcol 1
    simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_three, e1] using this
  have m20 : (k : Matrix (Fin 3) (Fin 3) (ZMod 2)) 2 0 = 0 := by
    have := congrFun hcol 2
    simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_three, e1] using this
  have m21 : (k : Matrix (Fin 3) (Fin 3) (ZMod 2)) 2 1 = 0 := by
    simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_three] using h21
  have hdet' : (k : Matrix (Fin 3) (Fin 3) (ZMod 2)) 1 1 * (k : Matrix (Fin 3) (Fin 3) (ZMod 2)) 2 2 = 1 := by
    rw [Matrix.det_fin_three, m00, m10, m20, m21] at hdet
    linear_combination hdet
  obtain ⟨h11, h22⟩ := zmod2_mul_eq_one _ _ hdet'
  refine ⟨(k : Matrix (Fin 3) (Fin 3) (ZMod 2)) 0 1, (k : Matrix (Fin 3) (Fin 3) (ZMod 2)) 0 2,
    (k : Matrix (Fin 3) (Fin 3) (ZMod 2)) 1 2, ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;> simp [m00, m10, m20, m21, h11, h22]

private theorem conj_data (T : Subgroup (GL (Fin 3) (ZMod 2))) (p : Fin 3 → ZMod 2)
    (l : Submodule (ZMod 2) (Fin 3 → ZMod 2))
    (hyp : CFSG.ASVolI.ChH.HypH5 T p l) :
    ∃ c : GL (Fin 3) (ZMod 2), (∀ y ∈ B0, c * y * c⁻¹ ∈ T) ∧
      (c : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec e1 = p ∧
      (∀ v : Fin 3 → ZMod 2, (c : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec v ∈ l ↔ v 2 = 0) := by
  obtain ⟨-, hTp, hTi⟩ := hyp.sylow
  rw [Subgroup.relIndex_top_right] at hTi
  obtain ⟨c, hc⟩ := sylow_conj T hTp hTi
  have hconjT : ∀ y ∈ B0, c * y * c⁻¹ ∈ T := by
    intro y hy
    refine (hc _).2 ?_
    rw [show c⁻¹ * (c * y * c⁻¹) * c = y by group]
    exact hy
  have hcinv : ∀ w : Fin 3 → ZMod 2,
      ((c⁻¹ : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec
        ((c : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec w) = w := by
    intro w; rw [← mulVec_gl, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
  have hcc : ∀ w : Fin 3 → ZMod 2,
      (c : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec
        (((c⁻¹ : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec w) = w := by
    intro w; rw [← mulVec_gl, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
  obtain ⟨q, hq⟩ : ∃ q : Fin 3 → ZMod 2,
      ((c⁻¹ : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec p = q := ⟨_, rfl⟩
  have hpq : (c : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec q = p := by rw [← hq, hcc]
  have hfixq : ∀ y ∈ B0, (y : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec q = q := by
    intro y hy
    have h1 := hyp.p_fix _ (hconjT y hy)
    rw [mulVec_gl, mulVec_gl, hq] at h1
    calc (y : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec q
        = ((c⁻¹ : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec
            ((c : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec ((y : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec q)) :=
          (hcinv _).symm
      _ = q := by rw [h1, hq]
  have hq0 : q = e1 := by
    rcases fixB0 q hfixq with h | h
    · exfalso
      apply hyp.p_ne
      rw [← hpq, h, Matrix.mulVec_zero]
    · exact h
  have hpc : (c : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec e1 = p := by rw [← hq0, hpq]
  have hline : ∀ v : Fin 3 → ZMod 2, (c : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec v ∈ l ↔ v 2 = 0 := by
    classical
    have hfr : Module.finrank (ZMod 2) l = 2 := hyp.l_line
    have hcardl : Nat.card l = 4 := natCard_of_finrank_two l hfr
    refine line_unique (fun v => (c : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec v ∈ l) ?_ ?_ ?_ ?_ ?_
    · simp
    · intro a b ha hb
      rw [Matrix.mulVec_add]
      exact l.add_mem ha hb
    · let e' : (Fin 3 → ZMod 2) ≃ (Fin 3 → ZMod 2) :=
        { toFun := fun v => (c : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec v
          invFun := fun w => ((c⁻¹ : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec w
          left_inv := hcinv
          right_inv := hcc }
      have h1 : (Finset.univ.filter (fun v : Fin 3 → ZMod 2 =>
            (c : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec v ∈ l)).card =
          (Finset.univ.filter (fun w : Fin 3 → ZMod 2 => w ∈ l)).card :=
        Finset.card_equiv e' (fun i => by simp [e'])
      rw [h1, ← Fintype.card_subtype]
      have := hcardl
      rw [Nat.card_eq_fintype_card] at this
      exact this
    · intro v hv
      have h := hyp.l_inv _ (hconjT _ tG_mem) _ hv
      rw [mulVec_gl, mulVec_gl, hcinv] at h
      show (c : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec
        ((!![1, 1, 0; 0, 1, 0; 0, 0, 1] : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec v) ∈ l
      rw [← tG_mat]
      exact h
    · intro v hv
      have h := hyp.l_inv _ (hconjT _ uG_mem) _ hv
      rw [mulVec_gl, mulVec_gl, hcinv] at h
      show (c : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec
        ((!![1, 0, 0; 0, 1, 1; 0, 0, 1] : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec v) ∈ l
      rw [← uG_mat]
      exact h
  exact ⟨c, hconjT, hpc, hline⟩



private theorem modIsoSub_of_hom {G A B : Type} [Group G] [CommGroup A] [CommGroup B]
    (act : G →* MulAut A) (b : G →* MulAut B) (S : Subgroup B) (e : A →* B)
    (he : Function.Injective e) (hS : ∀ x : B, x ∈ S ↔ ∃ a : A, e a = x)
    (hφ : ∀ (g : G) (a : A), e (act g a) = b g (e a)) : ModIsoSub act b S := by
  refine ⟨e, he, ?_, hφ⟩
  ext x
  rw [MonoidHom.mem_range, hS]

private theorem sigma_mul {N : Type} [AddCommGroup N] (σ : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2) →* AddMonoid.End N)
    (x y : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) (n : N) : σ (x * y) n = σ x (σ y n) := by
  rw [map_mul]
  rfl

private theorem Emap_intertwine {N : Type} [AddCommGroup N] (A : Type) [CommGroup A]
    (act : GL (Fin 3) (ZMod 2) →* MulAut A) (c : GL (Fin 3) (ZMod 2))
    (ρ : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2) →* AddMonoid.End (Additive A))
    (hρ : ∀ (g : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) (y : Additive A),
      ρ g y = Additive.ofMul (act (c * slGL g * c⁻¹) (Additive.toMul y)))
    (σ : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2) →* AddMonoid.End N)
    (fe : N ≃+ Additive A) (hfe : ∀ (g : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) (n : N),
      fe (σ g n) = ρ g (fe n))
    (h : GL (Fin 3) (ZMod 2)) (a : A) :
    σ (slGL.symm c) (fe.symm (Additive.ofMul (act h a))) =
      σ (slGL.symm h) (σ (slGL.symm c) (fe.symm (Additive.ofMul a))) := by
  have hk : c * slGL (slGL.symm (c⁻¹ * h * c)) * c⁻¹ = h := by
    rw [MulEquiv.apply_symm_apply]
    group
  have h1 : fe (σ (slGL.symm (c⁻¹ * h * c)) (fe.symm (Additive.ofMul a))) =
      Additive.ofMul (act h a) := by
    rw [hfe, AddEquiv.apply_symm_apply, hρ, hk]
    rfl
  have h2 : fe.symm (Additive.ofMul (act h a)) =
      σ (slGL.symm (c⁻¹ * h * c)) (fe.symm (Additive.ofMul a)) := by
    rw [← h1, AddEquiv.symm_apply_apply]
  rw [h2, ← sigma_mul, ← sigma_mul]
  congr 2
  apply slGL.injective
  simp only [map_mul slGL, MulEquiv.apply_symm_apply]
  group


private theorem sigma_inv_left {N : Type} [AddCommGroup N]
    (σ : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2) →* AddMonoid.End N)
    (g : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) (n : N) : σ g⁻¹ (σ g n) = n := by
  rw [← sigma_mul, inv_mul_cancel, map_one]
  rfl

private theorem sigma_inv_right {N : Type} [AddCommGroup N]
    (σ : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2) →* AddMonoid.End N)
    (g : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) (n : N) : σ g (σ g⁻¹ n) = n := by
  rw [← sigma_mul, mul_inv_cancel, map_one]
  rfl

private theorem mem_permCore_iff (p : Fin 3 → ZMod 2)
    (x : Multiplicative (GL (Fin 3) (ZMod 2) ⧸ Lpt p → ZMod 2)) :
    x ∈ CFSG.ASVolI.ChH.permCore (GL (Fin 3) (ZMod 2) ⧸ Lpt p) ↔
      ∑ q : GL (Fin 3) (ZMod 2) ⧸ Lpt p, Multiplicative.toAdd x q = 0 := by
  unfold CFSG.ASVolI.ChH.permCore
  simp only [Multiplicative.mem_toSubgroup, AddMonoidHom.mem_ker, AddMonoidHom.finset_sum_apply,
    Pi.evalAddMonoidHom_apply]
  rfl

private theorem mem_Adj3_iff (y : AdjAmb) : y ∈ Adj3 ↔ (Multiplicative.toAdd y).trace = 0 := by
  simp [Adj3]

private noncomputable def PhiInvCore (p : Fin 3 → ZMod 2) (hp : p ≠ 0)
    (x : ↥(permCore (GL (Fin 3) (ZMod 2) ⧸ Lpt p))) : CFSG.Quasithin.H6.Core :=
  ⟨fun i : Fin 8 => PhiInvFun p hp (Multiplicative.toAdd x.1) (CFSG.Quasithin.H6.vecOf i),
    PhiInv_mem p hp (Multiplicative.toAdd x.1) ((mem_permCore_iff p x.1).1 x.2)⟩

private theorem PhiInvCore_val (p : Fin 3 → ZMod 2) (hp : p ≠ 0)
    (x : ↥(permCore (GL (Fin 3) (ZMod 2) ⧸ Lpt p))) (i : Fin 8) :
    (PhiInvCore p hp x).1 i = PhiInvFun p hp (Multiplicative.toAdd x.1) (CFSG.Quasithin.H6.vecOf i) :=
  rfl

private theorem kappa_kappaEquiv_symm (p : Fin 3 → ZMod 2) (hp : p ≠ 0) (v : Fin 3 → ZMod 2) (hv : v ≠ 0) :
    kappa p ((kappaEquiv p hp).symm ⟨v, hv⟩) = v := by
  have := kappaEquiv_apply p hp ((kappaEquiv p hp).symm ⟨v, hv⟩)
  rw [Equiv.apply_symm_apply] at this
  exact this.symm

private theorem PhiFun_PhiInvCore (p : Fin 3 → ZMod 2) (hp : p ≠ 0)
    (x : ↥(permCore (GL (Fin 3) (ZMod 2) ⧸ Lpt p))) :
    PhiFun p (PhiInvCore p hp x) = Multiplicative.toAdd x.1 := by
  funext q
  unfold PhiFun coreVal
  rw [PhiInvCore_val, CFSG.Quasithin.H6.vecOf_idxOf]
  unfold PhiInvFun
  have hq : kappa p q ≠ 0 := kappa_ne_zero p hp q
  rw [dif_neg hq]
  have hsymm : (kappaEquiv p hp).symm ⟨kappa p q, hq⟩ = q := by
    apply (kappaEquiv p hp).injective
    apply Subtype.ext
    rw [Equiv.apply_symm_apply]
    exact (kappaEquiv_apply p hp q).symm
  rw [hsymm]

private theorem PhiInvCore_PhiFun (p : Fin 3 → ZMod 2) (hp : p ≠ 0) (f : CFSG.Quasithin.H6.Core) :
    PhiInvCore p hp ⟨Multiplicative.ofAdd (PhiFun p f), (mem_permCore_iff p _).2 (by
      simp only [toAdd_ofAdd]; exact sum_PhiFun p hp f)⟩ = f := by
  apply Subtype.ext
  funext i
  rw [PhiInvCore_val]
  simp only [toAdd_ofAdd]
  unfold PhiInvFun
  by_cases h0 : CFSG.Quasithin.H6.vecOf i = 0
  · rw [dif_pos h0]
    have hi : i = 0 := by
      have h' : i = CFSG.Quasithin.H6.idxOf (CFSG.Quasithin.H6.vecOf i) :=
        (CFSG.Quasithin.H6.idxOf_vecOf i).symm
      rw [h0] at h'
      rw [h']
      decide
    rw [hi]
    exact ((CFSG.Quasithin.H6.mem_coreSub.1 f.2).1).symm
  · rw [dif_neg h0]
    unfold PhiFun coreVal
    rw [kappa_kappaEquiv_symm p hp _ h0, CFSG.Quasithin.H6.idxOf_vecOf]

private theorem PhiFun_injective (p : Fin 3 → ZMod 2) (hp : p ≠ 0) (f g : CFSG.Quasithin.H6.Core)
    (h : PhiFun p f = PhiFun p g) : f = g := by
  have hf := PhiInvCore_PhiFun p hp f
  have hg := PhiInvCore_PhiFun p hp g
  rw [← hf, ← hg]
  congr 1
  apply Subtype.ext
  simp only [toAdd_ofAdd]
  exact h

private theorem permLH_mem (p : Fin 3 → ZMod 2) (h : GL (Fin 3) (ZMod 2))
    (x : Multiplicative (GL (Fin 3) (ZMod 2) ⧸ Lpt p → ZMod 2))
    (hx : x ∈ permCore (GL (Fin 3) (ZMod 2) ⧸ Lpt p)) :
    permLH (Lpt p) h x ∈ permCore (GL (Fin 3) (ZMod 2) ⧸ Lpt p) := by
  rw [mem_permCore_iff] at hx ⊢
  have key : ∀ q, Multiplicative.toAdd (permLH (Lpt p) h x) q =
      Multiplicative.toAdd x (h⁻¹ • q) := fun q => rfl
  simp only [key]
  exact (Equiv.sum_comp (MulAction.toPerm h⁻¹) (fun q => Multiplicative.toAdd x q)).trans hx

private theorem PhiInvCore_smul (p : Fin 3 → ZMod 2) (hp : p ≠ 0) (h : GL (Fin 3) (ZMod 2))
    (x : ↥(permCore (GL (Fin 3) (ZMod 2) ⧸ Lpt p))) :
    PhiInvCore p hp ⟨permLH (Lpt p) h x.1, permLH_mem p h x.1 x.2⟩ =
      CFSG.Quasithin.H6.ρCore (slGL.symm h) (PhiInvCore p hp x) := by
  apply PhiFun_injective p hp
  rw [PhiFun_PhiInvCore, PhiFun_smul_fun, PhiFun_PhiInvCore]
  rfl



private theorem slGL_symm_coe (h : GL (Fin 3) (ZMod 2)) :
    ((slGL.symm h : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)) =
      (h : Matrix (Fin 3) (Fin 3) (ZMod 2)) := by
  have := slGL_coe (slGL.symm h)
  rw [MulEquiv.apply_symm_apply] at this
  exact this.symm

private theorem slGL_symm_inv_coe (h : GL (Fin 3) (ZMod 2)) :
    (((slGL.symm h)⁻¹ : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)) =
      ((h⁻¹ : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)) := by
  rw [← map_inv slGL.symm h, slGL_symm_coe]

private theorem rhoV_apply (g : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) (v : Fin 3 → ZMod 2) :
    CFSG.Quasithin.H6.ρV g v = (g : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec v := rfl

private theorem E_package {N : Type} [AddCommGroup N] (A : Type) [CommGroup A]
    (act : GL (Fin 3) (ZMod 2) →* MulAut A) (c : GL (Fin 3) (ZMod 2))
    (ρ : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2) →* AddMonoid.End (Additive A))
    (hρ : ∀ (g : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) (y : Additive A),
      ρ g y = Additive.ofMul (act (c * slGL g * c⁻¹) (Additive.toMul y)))
    (σ : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2) →* AddMonoid.End N)
    (fe : N ≃+ Additive A) (hfe : ∀ (g : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) (n : N),
      fe (σ g n) = ρ g (fe n)) :
    ∃ E : A → N, (∀ a b, E (a * b) = E a + E b) ∧ Function.Bijective E ∧
      (∀ (h : GL (Fin 3) (ZMod 2)) (a : A), E (act h a) = σ (slGL.symm h) (E a)) := by
  refine ⟨fun a => σ (slGL.symm c) (fe.symm (Additive.ofMul a)), ?_, ⟨?_, ?_⟩, ?_⟩
  · intro a b
    simp only [ofMul_mul, map_add]
  · intro a b hab
    have h1 := congrArg (σ (slGL.symm c)⁻¹) hab
    simp only [sigma_inv_left] at h1
    exact Additive.ofMul.injective (fe.symm.injective h1)
  · intro n
    refine ⟨Additive.toMul (fe (σ (slGL.symm c)⁻¹ n)), ?_⟩
    show σ (slGL.symm c) (fe.symm (Additive.ofMul (Additive.toMul (fe (σ (slGL.symm c)⁻¹ n))))) = n
    rw [show Additive.ofMul (Additive.toMul (fe (σ (slGL.symm c)⁻¹ n))) = fe (σ (slGL.symm c)⁻¹ n) from rfl,
      AddEquiv.symm_apply_apply, sigma_inv_right]
  · intro h a
    exact Emap_intertwine A act c ρ hρ σ fe hfe h a


private theorem caseV (A : Type) [CommGroup A]
    (act : GL (Fin 3) (ZMod 2) →* MulAut A) (c : GL (Fin 3) (ZMod 2))
    (ρ : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2) →* AddMonoid.End (Additive A))
    (hρ : ∀ (g : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) (y : Additive A),
      ρ g y = Additive.ofMul (act (c * slGL g * c⁻¹) (Additive.toMul y)))
    (f : (Fin 3 → ZMod 2) →+ Additive A) (hf : Function.Bijective f)
    (hfe : ∀ (g : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) (n : Fin 3 → ZMod 2),
      f (CFSG.Quasithin.H6.ρV g n) = ρ g (f n)) :
    ModIso act CFSG.ASVolI.ChH.modNat := by
  unfold ModIso
  obtain ⟨E, hEmul, hEbij, hEint⟩ := E_package A act c ρ hρ CFSG.Quasithin.H6.ρV
    (AddEquiv.ofBijective f hf) (fun g n => hfe g n)
  refine modIsoSub_of_hom act CFSG.ASVolI.ChH.modNat ⊤
    (MonoidHom.mk' (fun a => Multiplicative.ofAdd (E a)) (fun a b => by
      show Multiplicative.ofAdd (E (a * b)) = Multiplicative.ofAdd (E a + E b)
      rw [hEmul]
      rfl))
    ?_ ?_ ?_
  · intro a b hab
    exact Additive.ofMul.injective (hEbij.1 (Multiplicative.ofAdd.injective hab)) |>.symm ▸ rfl
  · intro x
    refine ⟨fun _ => ?_, fun _ => trivial⟩
    obtain ⟨a, ha⟩ := hEbij.2 (Multiplicative.toAdd x)
    exact ⟨a, by show Multiplicative.ofAdd (E a) = x; rw [ha]; rfl⟩
  · intro g a
    show Multiplicative.ofAdd (E (act g a)) = Multiplicative.ofAdd ((g : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec (E a))
    rw [hEint]
    show Multiplicative.ofAdd (((slGL.symm g : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) :
      Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec (E a)) =
        Multiplicative.ofAdd ((g : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec (E a))
    rw [slGL_symm_coe]



private theorem caseSt (A : Type) [CommGroup A]
    (act : GL (Fin 3) (ZMod 2) →* MulAut A) (c : GL (Fin 3) (ZMod 2))
    (ρ : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2) →* AddMonoid.End (Additive A))
    (hρ : ∀ (g : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) (y : Additive A),
      ρ g y = Additive.ofMul (act (c * slGL g * c⁻¹) (Additive.toMul y)))
    (f : CFSG.Quasithin.H6.St →+ Additive A) (hf : Function.Bijective f)
    (hfe : ∀ (g : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) (n : CFSG.Quasithin.H6.St),
      f (CFSG.Quasithin.H6.ρSt g n) = ρ g (f n)) :
    ModIsoSub act CFSG.ASVolI.ChH.adjAmbAct CFSG.ASVolI.ChH.Adj3 := by
  obtain ⟨E, hEmul, hEbij, hEint⟩ := E_package A act c ρ hρ CFSG.Quasithin.H6.ρSt
    (AddEquiv.ofBijective f hf) (fun g n => hfe g n)
  have key : ∀ (g : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) (x : CFSG.Quasithin.H6.St),
      (CFSG.Quasithin.H6.ρSt g x).1 =
        (g : Matrix (Fin 3) (Fin 3) (ZMod 2)) * x.1 * ((g⁻¹ : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) :
          Matrix (Fin 3) (Fin 3) (ZMod 2)) :=
    fun g x => CFSG.Quasithin.H6.coe_smul_st g x
  refine modIsoSub_of_hom act CFSG.ASVolI.ChH.adjAmbAct CFSG.ASVolI.ChH.Adj3
    (MonoidHom.mk' (fun a => Multiplicative.ofAdd (E a).1) (fun a b => by
      show Multiplicative.ofAdd (E (a * b)).1 = Multiplicative.ofAdd (E a).1 * Multiplicative.ofAdd (E b).1
      rw [hEmul]
      rfl)) ?_ ?_ ?_
  · intro a b hab
    have h1 : (E a).1 = (E b).1 := Multiplicative.ofAdd.injective hab
    exact hEbij.1 (Subtype.ext h1)
  · intro x
    constructor
    · intro hx
      have htr := (mem_Adj3_iff x).1 hx
      obtain ⟨a, ha⟩ := hEbij.2 ⟨Multiplicative.toAdd x, (CFSG.Quasithin.H6.mem_stSub).2 htr⟩
      refine ⟨a, ?_⟩
      show Multiplicative.ofAdd (E a).1 = x
      rw [ha]
      rfl
    · rintro ⟨a, rfl⟩
      exact (mem_Adj3_iff _).2 ((CFSG.Quasithin.H6.mem_stSub).1 (E a).2)
  · intro h a
    show Multiplicative.ofAdd (E (act h a)).1 = adjAmbAct h (Multiplicative.ofAdd (E a).1)
    rw [hEint]
    show Multiplicative.ofAdd ((CFSG.Quasithin.H6.ρSt (slGL.symm h) (E a)).1) =
      adjAmbAct h (Multiplicative.ofAdd (E a).1)
    rw [key, slGL_symm_coe, slGL_symm_inv_coe]
    rfl



private noncomputable def iotaInv (y : ↥Adj3) : CFSG.Quasithin.H6.St :=
  ⟨Multiplicative.toAdd y.1, (CFSG.Quasithin.H6.mem_stSub).2 ((mem_Adj3_iff y.1).1 y.2)⟩

private def iotaOf (m : CFSG.Quasithin.H6.St) : ↥Adj3 :=
  ⟨Multiplicative.ofAdd m.1, (mem_Adj3_iff _).2 ((CFSG.Quasithin.H6.mem_stSub).1 m.2)⟩

private theorem iotaInv_iotaOf (m : CFSG.Quasithin.H6.St) : iotaInv (iotaOf m) = m := rfl

private theorem iotaOf_iotaInv (y : ↥Adj3) : iotaOf (iotaInv y) = y := rfl

private theorem adjAmbAct_mem (h : GL (Fin 3) (ZMod 2)) (X : AdjAmb) (hX : X ∈ Adj3) :
    adjAmbAct h X ∈ Adj3 := by
  rw [mem_Adj3_iff] at hX ⊢
  have hinv : ((h⁻¹ : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)) *
      (h : Matrix (Fin 3) (Fin 3) (ZMod 2)) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  show ((h : Matrix (Fin 3) (Fin 3) (ZMod 2)) * Multiplicative.toAdd X *
    ((h⁻¹ : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2))).trace = 0
  rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, hinv, Matrix.one_mul]
  exact hX

private theorem coe_rhoSt (g : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) (x : CFSG.Quasithin.H6.St) :
    (CFSG.Quasithin.H6.ρSt g x).1 =
      (g : Matrix (Fin 3) (Fin 3) (ZMod 2)) * x.1 *
        ((g⁻¹ : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)) :=
  CFSG.Quasithin.H6.coe_smul_st g x

private theorem iotaInv_smul (h : GL (Fin 3) (ZMod 2)) (y : ↥Adj3) :
    iotaInv ⟨adjAmbAct h y.1, adjAmbAct_mem h y.1 y.2⟩ =
      CFSG.Quasithin.H6.ρSt (slGL.symm h) (iotaInv y) := by
  apply Subtype.ext
  show Multiplicative.toAdd (adjAmbAct h y.1) = (CFSG.Quasithin.H6.ρSt (slGL.symm h) (iotaInv y)).1
  rw [coe_rhoSt, slGL_symm_coe, slGL_symm_inv_coe]
  rfl

private theorem iotaInv_mul (x y : ↥Adj3) : iotaInv (x * y) = iotaInv x + iotaInv y := by
  apply Subtype.ext
  rfl

private theorem PhiInvFun_add (p : Fin 3 → ZMod 2) (hp : p ≠ 0) (F G : GL (Fin 3) (ZMod 2) ⧸ Lpt p → ZMod 2)
    (v : Fin 3 → ZMod 2) :
    PhiInvFun p hp (F + G) v = PhiInvFun p hp F v + PhiInvFun p hp G v := by
  unfold PhiInvFun
  by_cases h : v = 0
  · simp only [dif_pos h, add_zero]
  · simp only [dif_neg h, Pi.add_apply]

private theorem PhiInvCore_mul (p : Fin 3 → ZMod 2) (hp : p ≠ 0)
    (x y : ↥(permCore (GL (Fin 3) (ZMod 2) ⧸ Lpt p))) :
    PhiInvCore p hp (x * y) = PhiInvCore p hp x + PhiInvCore p hp y := by
  apply Subtype.ext
  funext i
  simp only [AddSubgroup.coe_add, Pi.add_apply, PhiInvCore_val]
  show PhiInvFun p hp (Multiplicative.toAdd (x.1 * y.1)) (CFSG.Quasithin.H6.vecOf i) = _
  rw [toAdd_mul, PhiInvFun_add]



private theorem caseVSt (A : Type) [CommGroup A]
    (act : GL (Fin 3) (ZMod 2) →* MulAut A) (c : GL (Fin 3) (ZMod 2))
    (ρ : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2) →* AddMonoid.End (Additive A))
    (hρ : ∀ (g : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) (y : Additive A),
      ρ g y = Additive.ofMul (act (c * slGL g * c⁻¹) (Additive.toMul y)))
    (f : (Fin 3 → ZMod 2) × CFSG.Quasithin.H6.St →+ Additive A) (hf : Function.Bijective f)
    (hfe : ∀ (g : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2))
      (n : (Fin 3 → ZMod 2) × CFSG.Quasithin.H6.St),
      f (CFSG.Quasithin.H6.prodRep CFSG.Quasithin.H6.ρV CFSG.Quasithin.H6.ρSt g n) = ρ g (f n)) :
    ModIsoSub act (prodAct CFSG.ASVolI.ChH.modNat CFSG.ASVolI.ChH.adjAmbAct)
      ((⊤ : Subgroup (Multiplicative (Fin 3 → ZMod 2))).prod CFSG.ASVolI.ChH.Adj3) := by
  obtain ⟨E, hEmul, hEbij, hEint⟩ := E_package A act c ρ hρ
    (CFSG.Quasithin.H6.prodRep CFSG.Quasithin.H6.ρV CFSG.Quasithin.H6.ρSt)
    (AddEquiv.ofBijective f hf) (fun g n => hfe g n)
  refine modIsoSub_of_hom act (prodAct CFSG.ASVolI.ChH.modNat CFSG.ASVolI.ChH.adjAmbAct)
    ((⊤ : Subgroup (Multiplicative (Fin 3 → ZMod 2))).prod CFSG.ASVolI.ChH.Adj3)
    (MonoidHom.mk' (fun a => (Multiplicative.ofAdd (E a).1, Multiplicative.ofAdd (E a).2.1))
      (fun a b => by
        show (Multiplicative.ofAdd (E (a * b)).1, Multiplicative.ofAdd (E (a * b)).2.1) =
          (Multiplicative.ofAdd (E a).1, Multiplicative.ofAdd (E a).2.1) *
            (Multiplicative.ofAdd (E b).1, Multiplicative.ofAdd (E b).2.1)
        rw [hEmul]
        rfl)) ?_ ?_ ?_
  · intro a b hab
    have hab' : (Multiplicative.ofAdd (E a).1, Multiplicative.ofAdd (E a).2.1) =
        (Multiplicative.ofAdd (E b).1, Multiplicative.ofAdd (E b).2.1) := hab
    obtain ⟨hab1, hab2⟩ := Prod.mk.inj hab'
    have h1 : (E a).1 = (E b).1 := Multiplicative.ofAdd.injective hab1
    have h2 : (E a).2.1 = (E b).2.1 := Multiplicative.ofAdd.injective hab2
    exact hEbij.1 (Prod.ext h1 (Subtype.ext h2))
  · intro x
    constructor
    · intro hx
      obtain ⟨hx1, hx2⟩ := Subgroup.mem_prod.1 hx
      obtain ⟨a, ha⟩ := hEbij.2 (Multiplicative.toAdd x.1, iotaInv ⟨x.2, hx2⟩)
      refine ⟨a, ?_⟩
      show (Multiplicative.ofAdd (E a).1, Multiplicative.ofAdd (E a).2.1) = x
      rw [ha]
      rfl
    · rintro ⟨a, rfl⟩
      exact Subgroup.mem_prod.2 ⟨Subgroup.mem_top _,
        (mem_Adj3_iff _).2 ((CFSG.Quasithin.H6.mem_stSub).1 (E a).2.2)⟩
  · intro h a
    show (Multiplicative.ofAdd (E (act h a)).1, Multiplicative.ofAdd (E (act h a)).2.1) =
      prodAct CFSG.ASVolI.ChH.modNat CFSG.ASVolI.ChH.adjAmbAct h
        (Multiplicative.ofAdd (E a).1, Multiplicative.ofAdd (E a).2.1)
    rw [hEint]
    have h1 : CFSG.Quasithin.H6.ρV (slGL.symm h) (E a).1 =
        (h : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec (E a).1 := by
      rw [rhoV_apply, slGL_symm_coe]
    have h2 : (CFSG.Quasithin.H6.ρSt (slGL.symm h) (E a).2).1 =
        (h : Matrix (Fin 3) (Fin 3) (ZMod 2)) * (E a).2.1 *
          ((h⁻¹ : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)) := by
      rw [coe_rhoSt, slGL_symm_coe, slGL_symm_inv_coe]
    show (Multiplicative.ofAdd (CFSG.Quasithin.H6.ρV (slGL.symm h) (E a).1),
        Multiplicative.ofAdd (CFSG.Quasithin.H6.ρSt (slGL.symm h) (E a).2).1) =
      (modNat h (Multiplicative.ofAdd (E a).1), adjAmbAct h (Multiplicative.ofAdd (E a).2.1))
    rw [h1, h2]
    rfl

private theorem caseCore (A : Type) [CommGroup A] (p : Fin 3 → ZMod 2) (hp : p ≠ 0)
    (act : GL (Fin 3) (ZMod 2) →* MulAut A) (c : GL (Fin 3) (ZMod 2))
    (ρ : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2) →* AddMonoid.End (Additive A))
    (hρ : ∀ (g : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) (y : Additive A),
      ρ g y = Additive.ofMul (act (c * slGL g * c⁻¹) (Additive.toMul y)))
    (f : CFSG.Quasithin.H6.Core →+ Additive A) (hf : Function.Bijective f)
    (hfe : ∀ (g : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) (n : CFSG.Quasithin.H6.Core),
      f (CFSG.Quasithin.H6.ρCore g n) = ρ g (f n)) :
    ModIsoSub act (permLH (Lpt p)) (permCore (GL (Fin 3) (ZMod 2) ⧸ Lpt p)) := by
  obtain ⟨E, hEmul, hEbij, hEint⟩ := E_package A act c ρ hρ CFSG.Quasithin.H6.ρCore
    (AddEquiv.ofBijective f hf) (fun g n => hfe g n)
  refine modIsoSub_of_hom act (permLH (Lpt p)) (permCore (GL (Fin 3) (ZMod 2) ⧸ Lpt p))
    (MonoidHom.mk' (fun a => Multiplicative.ofAdd (PhiFun p (E a))) (fun a b => by
      show Multiplicative.ofAdd (PhiFun p (E (a * b))) =
        Multiplicative.ofAdd (PhiFun p (E a)) * Multiplicative.ofAdd (PhiFun p (E b))
      have hfun : PhiFun p (E (a * b)) = PhiFun p (E a) + PhiFun p (E b) := by
        rw [hEmul]
        exact PhiFun_add p (E a) (E b)
      exact congrArg (fun z => Multiplicative.ofAdd z) hfun)) ?_ ?_ ?_
  · intro a b hab
    have h1 : PhiFun p (E a) = PhiFun p (E b) := Multiplicative.ofAdd.injective hab
    exact hEbij.1 (PhiFun_injective p hp _ _ h1)
  · intro x
    constructor
    · intro hx
      obtain ⟨a, ha⟩ := hEbij.2 (PhiInvCore p hp ⟨x, hx⟩)
      refine ⟨a, ?_⟩
      show Multiplicative.ofAdd (PhiFun p (E a)) = x
      rw [ha, PhiFun_PhiInvCore]
      rfl
    · rintro ⟨a, rfl⟩
      exact (mem_permCore_iff p (Multiplicative.ofAdd (PhiFun p (E a)))).2 (sum_PhiFun p hp (E a))
  · intro h a
    have h1 : PhiFun p (CFSG.Quasithin.H6.ρCore (slGL.symm h) (E a)) =
        fun q => PhiFun p (E a) (h⁻¹ • q) := PhiFun_smul_fun p h (E a)
    show Multiplicative.ofAdd (PhiFun p (E (act h a))) =
      permLH (Lpt p) h (Multiplicative.ofAdd (PhiFun p (E a)))
    rw [hEint]
    show Multiplicative.ofAdd (PhiFun p (CFSG.Quasithin.H6.ρCore (slGL.symm h) (E a))) =
      permLH (Lpt p) h (Multiplicative.ofAdd (PhiFun p (E a)))
    rw [h1]
    rfl

private theorem caseCoreSt (A : Type) [CommGroup A] (p : Fin 3 → ZMod 2) (hp : p ≠ 0)
    (act : GL (Fin 3) (ZMod 2) →* MulAut A) (c : GL (Fin 3) (ZMod 2))
    (ρ : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2) →* AddMonoid.End (Additive A))
    (hρ : ∀ (g : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) (y : Additive A),
      ρ g y = Additive.ofMul (act (c * slGL g * c⁻¹) (Additive.toMul y)))
    (f : CFSG.Quasithin.H6.Core × CFSG.Quasithin.H6.St →+ Additive A) (hf : Function.Bijective f)
    (hfe : ∀ (g : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2))
      (n : CFSG.Quasithin.H6.Core × CFSG.Quasithin.H6.St),
      f (CFSG.Quasithin.H6.prodRep CFSG.Quasithin.H6.ρCore CFSG.Quasithin.H6.ρSt g n) = ρ g (f n)) :
    ModIsoSub act (prodAct (permLH (Lpt p)) adjAmbAct)
      ((permCore (GL (Fin 3) (ZMod 2) ⧸ Lpt p)).prod Adj3) := by
  obtain ⟨E, hEmul, hEbij, hEint⟩ := E_package A act c ρ hρ
    (CFSG.Quasithin.H6.prodRep CFSG.Quasithin.H6.ρCore CFSG.Quasithin.H6.ρSt)
    (AddEquiv.ofBijective f hf) (fun g n => hfe g n)
  refine modIsoSub_of_hom act (prodAct (permLH (Lpt p)) adjAmbAct)
    ((permCore (GL (Fin 3) (ZMod 2) ⧸ Lpt p)).prod Adj3)
    (MonoidHom.mk' (fun a => (Multiplicative.ofAdd (PhiFun p (E a).1), Multiplicative.ofAdd (E a).2.1))
      (fun a b => by
        show (Multiplicative.ofAdd (PhiFun p (E (a * b)).1), Multiplicative.ofAdd (E (a * b)).2.1) =
          (Multiplicative.ofAdd (PhiFun p (E a).1), Multiplicative.ofAdd (E a).2.1) *
            (Multiplicative.ofAdd (PhiFun p (E b).1), Multiplicative.ofAdd (E b).2.1)
        rw [hEmul]
        simp only [Prod.fst_add, Prod.snd_add, PhiFun_add, AddSubgroup.coe_add]
        rfl)) ?_ ?_ ?_
  · intro a b hab
    have h1 : PhiFun p (E a).1 = PhiFun p (E b).1 := Multiplicative.ofAdd.injective (congrArg Prod.fst hab)
    have h2 : (E a).2.1 = (E b).2.1 := Multiplicative.ofAdd.injective (congrArg Prod.snd hab)
    have h3 : (E a).1 = (E b).1 := PhiFun_injective p hp _ _ h1
    exact hEbij.1 (Prod.ext h3 (Subtype.ext h2))
  · intro x
    constructor
    · intro hx
      obtain ⟨hx1, hx2⟩ := Subgroup.mem_prod.1 hx
      obtain ⟨a, ha⟩ := hEbij.2 (PhiInvCore p hp ⟨x.1, hx1⟩, iotaInv ⟨x.2, hx2⟩)
      refine ⟨a, ?_⟩
      show (Multiplicative.ofAdd (PhiFun p (E a).1), Multiplicative.ofAdd (E a).2.1) = x
      rw [ha]
      apply Prod.ext
      · show Multiplicative.ofAdd (PhiFun p (PhiInvCore p hp ⟨x.1, hx1⟩)) = x.1
        rw [PhiFun_PhiInvCore]
        rfl
      · rfl
    · rintro ⟨a, rfl⟩
      exact Subgroup.mem_prod.2 ⟨(mem_permCore_iff p (Multiplicative.ofAdd (PhiFun p (E a).1))).2
          (sum_PhiFun p hp (E a).1),
        (mem_Adj3_iff _).2 ((CFSG.Quasithin.H6.mem_stSub).1 (E a).2.2)⟩
  · intro h a
    show (Multiplicative.ofAdd (PhiFun p (E (act h a)).1), Multiplicative.ofAdd (E (act h a)).2.1) =
      prodAct (permLH (Lpt p)) adjAmbAct h (Multiplicative.ofAdd (PhiFun p (E a).1),
        Multiplicative.ofAdd (E a).2.1)
    rw [hEint]
    have h1 : PhiFun p (CFSG.Quasithin.H6.ρCore (slGL.symm h) (E a).1) =
        fun q => PhiFun p (E a).1 (h⁻¹ • q) := PhiFun_smul_fun p h _
    have h2 : (CFSG.Quasithin.H6.ρSt (slGL.symm h) (E a).2).1 =
        (h : Matrix (Fin 3) (Fin 3) (ZMod 2)) * (E a).2.1 *
          ((h⁻¹ : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)) := by
      rw [coe_rhoSt, slGL_symm_coe, slGL_symm_inv_coe]
    show (Multiplicative.ofAdd (PhiFun p (CFSG.Quasithin.H6.ρCore (slGL.symm h) (E a).1)),
        Multiplicative.ofAdd (CFSG.Quasithin.H6.ρSt (slGL.symm h) (E a).2).1) =
      (permLH (Lpt p) h (Multiplicative.ofAdd (PhiFun p (E a).1)),
        adjAmbAct h (Multiplicative.ofAdd (E a).2.1))
    rw [h1, h2]
    rfl



private theorem PhiInvCore_congr (p : Fin 3 → ZMod 2) (hp : p ≠ 0)
    {u v : ↥(permCore (GL (Fin 3) (ZMod 2) ⧸ Lpt p))} (h : u = v) :
    PhiInvCore p hp u = PhiInvCore p hp v := by
  rw [h]

private theorem iotaInv_congr {u v : ↥Adj3} (h : u = v) : iotaInv u = iotaInv v := by
  rw [h]

private theorem act_eq_rho (A : Type) [CommGroup A] (act : GL (Fin 3) (ZMod 2) →* MulAut A) (c : GL (Fin 3) (ZMod 2))
    (ρ : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2) →* AddMonoid.End (Additive A))
    (hρ : ∀ (g : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) (y : Additive A),
      ρ g y = Additive.ofMul (act (c * slGL g * c⁻¹) (Additive.toMul y)))
    (g : GL (Fin 3) (ZMod 2)) (a : A) :
    act g a = Additive.toMul (ρ (slGL.symm (c⁻¹ * g * c)) (Additive.ofMul a)) := by
  rw [hρ]
  have hk : c * slGL (slGL.symm (c⁻¹ * g * c)) * c⁻¹ = g := by
    rw [MulEquiv.apply_symm_apply]
    group
  rw [hk]
  rfl

private theorem isQuot_case (A : Type) [CommGroup A] (p : Fin 3 → ZMod 2) (hp : p ≠ 0)
    (act : GL (Fin 3) (ZMod 2) →* MulAut A) (c : GL (Fin 3) (ZMod 2))
    (ρ : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2) →* AddMonoid.End (Additive A))
    (hρ : ∀ (g : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) (y : Additive A),
      ρ g y = Additive.ofMul (act (c * slGL g * c⁻¹) (Additive.toMul y)))
    (F : CFSG.Quasithin.H6.Core × CFSG.Quasithin.H6.St →+ Additive A)
    (hFs : Function.Surjective F)
    (hFe : ∀ (g : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2))
      (n : CFSG.Quasithin.H6.Core × CFSG.Quasithin.H6.St),
      F (CFSG.Quasithin.H6.prodRep CFSG.Quasithin.H6.ρCore CFSG.Quasithin.H6.ρSt g n) = ρ g (F n)) :
    IsQuotOfSub act (prodAct (permLH (Lpt p)) adjAmbAct)
      ((permCore (GL (Fin 3) (ZMod 2) ⧸ Lpt p)).prod Adj3) := by
  set S := (permCore (GL (Fin 3) (ZMod 2) ⧸ Lpt p)).prod Adj3 with hS
  let Θ : ↥S → CFSG.Quasithin.H6.Core × CFSG.Quasithin.H6.St := fun x =>
    (PhiInvCore p hp ⟨x.1.1, (Subgroup.mem_prod.1 x.2).1⟩,
      iotaInv ⟨x.1.2, (Subgroup.mem_prod.1 x.2).2⟩)
  have hΘmul : ∀ x y : ↥S, Θ (x * y) = Θ x + Θ y := fun x y =>
    Prod.ext (PhiInvCore_mul p hp ⟨x.1.1, (Subgroup.mem_prod.1 x.2).1⟩
      ⟨y.1.1, (Subgroup.mem_prod.1 y.2).1⟩) (iotaInv_mul ⟨x.1.2, (Subgroup.mem_prod.1 x.2).2⟩
      ⟨y.1.2, (Subgroup.mem_prod.1 y.2).2⟩)
  let P : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2) →* AddMonoid.End
      (CFSG.Quasithin.H6.Core × CFSG.Quasithin.H6.St) :=
    CFSG.Quasithin.H6.prodRep CFSG.Quasithin.H6.ρCore CFSG.Quasithin.H6.ρSt
  let π0 : ↥S →* A :=
    MonoidHom.mk' (fun x => Additive.toMul (F (P (slGL.symm c)⁻¹ (Θ x)))) (fun x y => by
      show Additive.toMul (F (P (slGL.symm c)⁻¹ (Θ (x * y)))) =
        Additive.toMul (F (P (slGL.symm c)⁻¹ (Θ x))) * Additive.toMul (F (P (slGL.symm c)⁻¹ (Θ y)))
      rw [hΘmul, map_add (P (slGL.symm c)⁻¹), map_add F]
      rfl)
  have hsurj : Function.Surjective π0 := by
    intro a
    obtain ⟨w, hw⟩ := hFs (Additive.ofMul a)
    let w' := P (slGL.symm c) w
    have hmemP : Multiplicative.ofAdd (PhiFun p w'.1) ∈ permCore (GL (Fin 3) (ZMod 2) ⧸ Lpt p) :=
      (mem_permCore_iff p _).2 (sum_PhiFun p hp w'.1)
    have hmemA : Multiplicative.ofAdd w'.2.1 ∈ Adj3 :=
      (mem_Adj3_iff _).2 ((CFSG.Quasithin.H6.mem_stSub).1 w'.2.2)
    let x : ↥S := ⟨(Multiplicative.ofAdd (PhiFun p w'.1), Multiplicative.ofAdd w'.2.1),
      Subgroup.mem_prod.2 ⟨hmemP, hmemA⟩⟩
    refine ⟨x, ?_⟩
    have hΘx : Θ x = w' := by
      apply Prod.ext
      · exact PhiInvCore_PhiFun p hp w'.1
      · rfl
    have hcancel : P (slGL.symm c)⁻¹ w' = w := sigma_inv_left (P) (slGL.symm c) w
    show Additive.toMul (F (P (slGL.symm c)⁻¹ (Θ x))) = a
    rw [hΘx, hcancel, hw]
    rfl
  refine ⟨π0, hsurj, ?_⟩
  intro g x x' hx'
  have hx'1 : x'.1.1 = permLH (Lpt p) g x.1.1 := congrArg Prod.fst hx'
  have hx'2 : x'.1.2 = adjAmbAct g x.1.2 := congrArg Prod.snd hx'
  have hΘ' : Θ x' = P (slGL.symm g) (Θ x) := by
    apply Prod.ext
    · show PhiInvCore p hp ⟨x'.1.1, (Subgroup.mem_prod.1 x'.2).1⟩ =
        CFSG.Quasithin.H6.ρCore (slGL.symm g) (PhiInvCore p hp ⟨x.1.1, (Subgroup.mem_prod.1 x.2).1⟩)
      rw [← PhiInvCore_smul p hp g ⟨x.1.1, (Subgroup.mem_prod.1 x.2).1⟩]
      exact PhiInvCore_congr p hp (Subtype.ext hx'1)
    · show iotaInv ⟨x'.1.2, (Subgroup.mem_prod.1 x'.2).2⟩ =
        CFSG.Quasithin.H6.ρSt (slGL.symm g) (iotaInv ⟨x.1.2, (Subgroup.mem_prod.1 x.2).2⟩)
      rw [← iotaInv_smul g ⟨x.1.2, (Subgroup.mem_prod.1 x.2).2⟩]
      exact iotaInv_congr (Subtype.ext hx'2)
  have hcomm : (slGL.symm c)⁻¹ * slGL.symm g = slGL.symm (c⁻¹ * g * c) * (slGL.symm c)⁻¹ := by
    apply slGL.injective
    simp only [map_mul, map_inv, MulEquiv.apply_symm_apply]
    group
  show Additive.toMul (F (P (slGL.symm c)⁻¹ (Θ x'))) =
    act g (Additive.toMul (F (P (slGL.symm c)⁻¹ (Θ x))))
  rw [hΘ', act_eq_rho A act c ρ hρ g]
  show Additive.toMul (F (P (slGL.symm c)⁻¹ (P (slGL.symm g) (Θ x)))) =
    Additive.toMul (ρ (slGL.symm (c⁻¹ * g * c)) (F (P (slGL.symm c)⁻¹ (Θ x))))
  rw [← hFe (slGL.symm (c⁻¹ * g * c)) (P (slGL.symm c)⁻¹ (Θ x))]
  show Additive.toMul (F (P (slGL.symm c)⁻¹ (P (slGL.symm g) (Θ x)))) =
    Additive.toMul (F (P (slGL.symm (c⁻¹ * g * c)) (P (slGL.symm c)⁻¹ (Θ x))))
  have hPmul : ∀ (u v : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2))
      (n : CFSG.Quasithin.H6.Core × CFSG.Quasithin.H6.St), P (u * v) n = P u (P v n) := by
    intro u v n
    rw [map_mul]
    exact congrFun (AddMonoid.End.coe_mul _ (P u) (P v)) n
  rw [← hPmul (slGL.symm c)⁻¹ (slGL.symm g) (Θ x),
    ← hPmul (slGL.symm (c⁻¹ * g * c)) (slGL.symm c)⁻¹ (Θ x), hcomm]



theorem as_H_6_5 : H_6_5 := by
  intro T p l hyp A _ _ hA act hfaith m hTm hclos hrk
  have hp : p ≠ 0 := hyp.p_ne
  obtain ⟨c, hconjT, hpc, hline⟩ := conj_data T p l hyp
  let actA : GL (Fin 3) (ZMod 2) →* AddMonoid.End (Additive A) :=
    { toFun := fun h => AddMonoidHom.mk' (fun y => Additive.ofMul (act h (Additive.toMul y)))
        (fun y z => by
          show Additive.ofMul (act h (Additive.toMul y * Additive.toMul z)) = _
          rw [map_mul]
          rfl)
      map_one' := by
        ext y
        show Additive.ofMul (act 1 (Additive.toMul y)) = y
        rw [map_one]
        rfl
      map_mul' := fun h k => by
        ext y
        show Additive.ofMul (act (h * k) (Additive.toMul y)) =
          Additive.ofMul (act h (Additive.toMul (Additive.ofMul (act k (Additive.toMul y)))))
        rw [map_mul]
        rfl }
  let ρ : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2) →* AddMonoid.End (Additive A) :=
    (actA.comp (MulAut.conj c).toMonoidHom).comp slGL.toMonoidHom
  have hρ : ∀ (g : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) (y : Additive A),
      ρ g y = Additive.ofMul (act (c * slGL g * c⁻¹) (Additive.toMul y)) := fun g y => rfl
  have hm2 : ∀ n : Additive A, n + n = 0 := by
    intro n
    have h := hA (Additive.toMul n)
    rw [sq] at h
    exact h
  have hfaith' : ∀ g : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2),
      (∀ n : Additive A, ρ g n = n) → g = 1 := by
    intro g hg
    have hA' : ∀ a : A, act (c * slGL g * c⁻¹) a = a := fun a => by
      have := hg (Additive.ofMul a)
      rw [hρ] at this
      exact congrArg Additive.toMul this
    have h1 : c * slGL g * c⁻¹ = 1 := hfaith _ hA'
    have h2 : slGL g = 1 := by
      have e : slGL g = c⁻¹ * (c * slGL g * c⁻¹) * c := by group
      rw [e, h1]
      group
    exact slGL.injective (by rw [h2, map_one])
  have hborel : ∀ t ∈ CFSG.Quasithin.H6.borel, ρ t (Additive.ofMul m) = Additive.ofMul m := by
    intro t ht
    rw [CFSG.Quasithin.H6.borel, Subgroup.mem_inf] at ht
    have hk1 := (mem_Lp_iff t).1 ht.1
    have hk2 := (mem_Ll_iff t).1 ht.2
    have hB : slGL t ∈ B0 := Lpt_inter_le_B0 (slGL t)
      (fun v hv => (mem_Lpt _ _).1 hk1 v hv)
      (fun v hv => ((mem_Lln _ _).1 hk2 v hv).1)
    have hfix := hTm _ (hconjT _ hB)
    rw [hρ]
    show Additive.ofMul (act _ m) = Additive.ofMul m
    rw [hfix]
  have hmemLl : ∀ g : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2),
      g ∈ CFSG.Quasithin.H6.Ll → c * slGL g * c⁻¹ ∈ Lln l :=
    fun g hg => (mem_Lln_conj c l hline (slGL g)).1 ((mem_Ll_iff g).1 hg)
  have hrange : Additive.toMul ⁻¹' (Set.range fun h : GL (Fin 3) (ZMod 2) => act h m) =
      Set.range fun g : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2) => ρ g (Additive.ofMul m) := by
    ext y
    simp only [Set.mem_preimage, Set.mem_range]
    constructor
    · rintro ⟨h, hh⟩
      refine ⟨slGL.symm (c⁻¹ * h * c), ?_⟩
      rw [hρ, MulEquiv.apply_symm_apply, show c * (c⁻¹ * h * c) * c⁻¹ = h by group]
      show Additive.ofMul (act h m) = y
      rw [hh]
      rfl
    · rintro ⟨g, rfl⟩
      exact ⟨c * slGL g * c⁻¹, by rw [hρ]; rfl⟩
  have hclos' : AddSubgroup.closure
      (Set.range fun g : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2) => ρ g (Additive.ofMul m)) = ⊤ := by
    rw [← hrange]
    have h1 := Subgroup.toAddSubgroup_closure (Set.range fun h : GL (Fin 3) (ZMod 2) => act h m)
    rw [hclos] at h1
    rw [← h1]
    exact AddSubgroup.ext (fun _ => Iff.rfl)
  have hsetLl : {y : Additive A | ∃ g ∈ CFSG.Quasithin.H6.Ll, ρ g (Additive.ofMul m) = y} =
      Additive.toMul ⁻¹' ((fun h => act h m) '' (Lln l : Set (GL (Fin 3) (ZMod 2)))) := by
    ext y
    simp only [Set.mem_setOf_eq, Set.mem_preimage, Set.mem_image, SetLike.mem_coe]
    constructor
    · rintro ⟨g, hg, rfl⟩
      exact ⟨c * slGL g * c⁻¹, hmemLl g hg, by rw [hρ]; rfl⟩
    · rintro ⟨h, hh, hact⟩
      refine ⟨slGL.symm (c⁻¹ * h * c), ?_, ?_⟩
      · rw [mem_Ll_iff, MulEquiv.apply_symm_apply, mem_Lln_conj c l hline (c⁻¹ * h * c),
          show c * (c⁻¹ * h * c) * c⁻¹ = h by group]
        exact hh
      · rw [hρ, MulEquiv.apply_symm_apply, show c * (c⁻¹ * h * c) * c⁻¹ = h by group]
        show Additive.ofMul (act h m) = y
        rw [hact]
        rfl
  have hcard' : Nat.card ↥(AddSubgroup.closure
      {y : Additive A | ∃ g ∈ CFSG.Quasithin.H6.Ll, ρ g (Additive.ofMul m) = y}) = 4 := by
    rw [hsetLl, ← Subgroup.toAddSubgroup_closure, natCard_toAddSubgroup]
    exact card_of_rk_two hA _ hrk
  obtain ⟨⟨F, hFs, hFe⟩, hiso⟩ := CFSG.Quasithin.H6.volI_H_6_5 (Additive A) ρ hm2 hfaith'
    (Additive.ofMul m) hborel hclos' hcard'
  refine ⟨isQuot_case A p hp act c ρ hρ F hFs hFe, ?_⟩
  rcases hiso with ⟨f1, hf1, hfe1⟩ | ⟨f2, hf2, hfe2⟩ | ⟨f3, hf3, hfe3⟩ | ⟨f4, hf4, hfe4⟩ |
    ⟨f5, hf5, hfe5⟩
  · exact Or.inl (caseCore A p hp act c ρ hρ f1 hf1 hfe1)
  · exact Or.inr (Or.inl (caseSt A act c ρ hρ f2 hf2 hfe2))
  · exact Or.inr (Or.inr (Or.inl (caseV A act c ρ hρ f3 hf3 hfe3)))
  · exact Or.inr (Or.inr (Or.inr (Or.inl (caseVSt A act c ρ hρ f4 hf4 hfe4))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (caseCoreSt A p hp act c ρ hρ f5 hf5 hfe5))))

end HBridge65


section H63
open CFSG.Quasithin.MS93 Matrix

private theorem zmod2_self_add' (a : ZMod 2) : a + a = 0 := by revert a; decide

private def h63a : GL (Fin 3) (ZMod 2) :=
  ⟨!![1, 0, 0; 0, 0, 1; 0, 1, 0], !![1, 0, 0; 0, 0, 1; 0, 1, 0], by decide, by decide⟩
private def h63b : GL (Fin 3) (ZMod 2) := ⟨1, 1, by simp, by simp⟩
private def h63c : GL (Fin 3) (ZMod 2) :=
  ⟨!![0, 0, 1; 1, 0, 0; 0, 1, 0], !![0, 1, 0; 0, 0, 1; 1, 0, 0], by decide, by decide⟩
private def h63d : GL (Fin 3) (ZMod 2) :=
  ⟨!![0, 1, 0; 1, 0, 0; 0, 0, 1], !![0, 1, 0; 1, 0, 0; 0, 0, 1], by decide, by decide⟩
private def h63e : GL (Fin 3) (ZMod 2) :=
  ⟨!![0, 1, 0; 0, 0, 1; 1, 0, 0], !![0, 0, 1; 1, 0, 0; 0, 1, 0], by decide, by decide⟩
private def h63f : GL (Fin 3) (ZMod 2) :=
  ⟨!![0, 0, 1; 0, 1, 0; 1, 0, 0], !![0, 0, 1; 0, 1, 0; 1, 0, 0], by decide, by decide⟩
private def h63g : GL (Fin 3) (ZMod 2) :=
  ⟨!![1, 0, 0; 0, 1, 0; 1, 0, 1], !![1, 0, 0; 0, 1, 0; 1, 0, 1], by decide, by decide⟩
private def h63h : GL (Fin 3) (ZMod 2) :=
  ⟨!![0, 1, 0; 1, 0, 0; 1, 0, 1], !![0, 1, 0; 1, 0, 0; 0, 1, 1], by decide, by decide⟩

set_option synthInstance.maxHeartbeats 1000000 in
set_option synthInstance.maxSize 65536 in
set_option maxRecDepth 10000 in
private theorem trace_detect63 : ∀ X : Matrix (Fin 3) (Fin 3) (ZMod 2), X.trace = 0 →
    (X * ((h63a : Matrix (Fin 3) (Fin 3) (ZMod 2)) * CFSG.Quasithin.H6.stE13.1 *
      ((h63a⁻¹ : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)))).trace = 0 →
    (X * ((h63b : Matrix (Fin 3) (Fin 3) (ZMod 2)) * CFSG.Quasithin.H6.stE13.1 *
      ((h63b⁻¹ : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)))).trace = 0 →
    (X * ((h63c : Matrix (Fin 3) (Fin 3) (ZMod 2)) * CFSG.Quasithin.H6.stE13.1 *
      ((h63c⁻¹ : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)))).trace = 0 →
    (X * ((h63d : Matrix (Fin 3) (Fin 3) (ZMod 2)) * CFSG.Quasithin.H6.stE13.1 *
      ((h63d⁻¹ : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)))).trace = 0 →
    (X * ((h63e : Matrix (Fin 3) (Fin 3) (ZMod 2)) * CFSG.Quasithin.H6.stE13.1 *
      ((h63e⁻¹ : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)))).trace = 0 →
    (X * ((h63f : Matrix (Fin 3) (Fin 3) (ZMod 2)) * CFSG.Quasithin.H6.stE13.1 *
      ((h63f⁻¹ : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)))).trace = 0 →
    (X * ((h63g : Matrix (Fin 3) (Fin 3) (ZMod 2)) * CFSG.Quasithin.H6.stE13.1 *
      ((h63g⁻¹ : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)))).trace = 0 →
    (X * ((h63h : Matrix (Fin 3) (Fin 3) (ZMod 2)) * CFSG.Quasithin.H6.stE13.1 *
      ((h63h⁻¹ : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)))).trace = 0 →
    X = 0 := by
  decide +kernel

private theorem rhoSt_slGL_symm_coe (h : GL (Fin 3) (ZMod 2)) (x : CFSG.Quasithin.H6.St) :
    (CFSG.Quasithin.H6.ρSt (slGL.symm h) x).1 =
      (h : Matrix (Fin 3) (Fin 3) (ZMod 2)) * x.1 *
        ((h⁻¹ : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)) := by
  rw [coe_rhoSt, slGL_symm_coe, slGL_symm_inv_coe]

private noncomputable def stF63 : CFSG.Quasithin.H6.St →+ (GL (Fin 3) (ZMod 2) → ZMod 2) where
  toFun x h := CFSG.Quasithin.H6.stForm x (CFSG.Quasithin.H6.ρSt (slGL.symm h) CFSG.Quasithin.H6.stE13)
  map_zero' := by
    funext h
    simp
  map_add' x y := by
    funext h
    simp

private theorem stF63_apply (x : CFSG.Quasithin.H6.St) (h : GL (Fin 3) (ZMod 2)) :
    stF63 x h = (x.1 * ((h : Matrix (Fin 3) (Fin 3) (ZMod 2)) * CFSG.Quasithin.H6.stE13.1 *
      ((h⁻¹ : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)))).trace := by
  show CFSG.Quasithin.H6.stForm x (CFSG.Quasithin.H6.ρSt (slGL.symm h) CFSG.Quasithin.H6.stE13) = _
  rw [CFSG.Quasithin.H6.stForm_apply, rhoSt_slGL_symm_coe]

private theorem stF63_injective : Function.Injective stF63 := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  have key : ∀ h : GL (Fin 3) (ZMod 2),
      (x.1 * ((h : Matrix (Fin 3) (Fin 3) (ZMod 2)) * CFSG.Quasithin.H6.stE13.1 *
        ((h⁻¹ : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)))).trace = 0 := by
    intro h
    have hh : stF63 x h = 0 := congrFun hx h
    rw [stF63_apply] at hh
    exact hh
  apply Subtype.ext
  exact trace_detect63 x.1 (CFSG.Quasithin.H6.mem_stSub.1 x.2) (key h63a) (key h63b) (key h63c)
    (key h63d) (key h63e) (key h63f) (key h63g) (key h63h)

private noncomputable def regAct63 :
    GL (Fin 3) (ZMod 2) →* AddMonoid.End (GL (Fin 3) (ZMod 2) → ZMod 2) where
  toFun k :=
    { toFun := fun φ h => φ (k⁻¹ * h)
      map_zero' := rfl
      map_add' := fun φ ψ => rfl }
  map_one' := by
    ext φ h
    show φ (1⁻¹ * h) = φ h
    simp
  map_mul' k l := by
    ext φ h
    show φ ((k * l)⁻¹ * h) = φ (l⁻¹ * (k⁻¹ * h))
    simp [mul_assoc, _root_.mul_inv_rev]

private theorem regAct63_apply (k : GL (Fin 3) (ZMod 2)) (φ : GL (Fin 3) (ZMod 2) → ZMod 2)
    (h : GL (Fin 3) (ZMod 2)) : regAct63 k φ h = φ (k⁻¹ * h) := rfl

private noncomputable def regSL63 :
    CFSG.Quasithin.H6.Γ →* AddMonoid.End (GL (Fin 3) (ZMod 2) → ZMod 2) :=
  regAct63.comp slGL.toMonoidHom

private theorem regSL63_apply (g : CFSG.Quasithin.H6.Γ) (φ : GL (Fin 3) (ZMod 2) → ZMod 2)
    (h : GL (Fin 3) (ZMod 2)) : regSL63 g φ h = φ ((slGL g)⁻¹ * h) := rfl

private theorem trace_conj_GL63 (G : GL (Fin 3) (ZMod 2)) (x M : Matrix (Fin 3) (Fin 3) (ZMod 2)) :
    ((G : Matrix (Fin 3) (Fin 3) (ZMod 2)) * x * ((G⁻¹ : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)) * M).trace =
      (x * (((G⁻¹ : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)) * M * (G : Matrix (Fin 3) (Fin 3) (ZMod 2)))).trace := by
  have e1 : (G : Matrix (Fin 3) (Fin 3) (ZMod 2)) * x * ((G⁻¹ : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)) * M =
      (G : Matrix (Fin 3) (Fin 3) (ZMod 2)) * (x * ((G⁻¹ : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)) * M) := by
    simp only [Matrix.mul_assoc]
  rw [e1, Matrix.trace_mul_comm]
  simp only [Matrix.mul_assoc]

private theorem stF63_equiv (g : CFSG.Quasithin.H6.Γ) (x : CFSG.Quasithin.H6.St) :
    stF63 (CFSG.Quasithin.H6.ρSt g x) = regSL63 g (stF63 x) := by
  funext h
  rw [regSL63_apply, stF63_apply, stF63_apply, coe_rhoSt]
  have h1 : ((g : CFSG.Quasithin.H6.Γ) : Matrix (Fin 3) (Fin 3) (ZMod 2)) =
      ((slGL g : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)) := (slGL_coe g).symm
  have h2 : (((g⁻¹ : CFSG.Quasithin.H6.Γ)) : Matrix (Fin 3) (Fin 3) (ZMod 2)) =
      (((slGL g)⁻¹ : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)) := by
    rw [← slGL_coe, map_inv]
  rw [h1, h2]
  have hK : ((((slGL g)⁻¹ * h : GL (Fin 3) (ZMod 2))⁻¹ : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)) =
      ((h⁻¹ : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)) * (slGL g : Matrix (Fin 3) (Fin 3) (ZMod 2)) := by
    rw [_root_.mul_inv_rev, inv_inv, Units.val_mul]
  have hK' : (((slGL g)⁻¹ * h : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)) =
      (((slGL g)⁻¹ : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)) * (h : Matrix (Fin 3) (Fin 3) (ZMod 2)) :=
    Units.val_mul _ _
  rw [hK, hK']
  rw [trace_conj_GL63 (slGL g) x.1]
  simp only [Matrix.mul_assoc]


open scoped Classical in
private noncomputable def betaAdj (u w : AdjAmb) : ZMod 2 :=
  if h : u ∈ Adj3 ∧ w ∈ Adj3 then
    CFSG.Quasithin.H6.stForm (iotaInv ⟨u, h.1⟩) (iotaInv ⟨w, h.2⟩) else 0

private theorem betaAdj_mul_left (u u' w : AdjAmb) (hu : u ∈ Adj3) (hu' : u' ∈ Adj3) (hw : w ∈ Adj3) :
    betaAdj (u * u') w = betaAdj u w + betaAdj u' w := by
  unfold betaAdj
  rw [dif_pos ⟨Subgroup.mul_mem _ hu hu', hw⟩, dif_pos ⟨hu, hw⟩, dif_pos ⟨hu', hw⟩]
  have h1 : iotaInv ⟨u * u', Subgroup.mul_mem _ hu hu'⟩ = iotaInv ⟨u, hu⟩ + iotaInv ⟨u', hu'⟩ :=
    iotaInv_mul ⟨u, hu⟩ ⟨u', hu'⟩
  rw [h1, map_add, AddMonoidHom.add_apply]

private theorem betaAdj_mul_right (u w w' : AdjAmb) (hu : u ∈ Adj3) (hw : w ∈ Adj3) (hw' : w' ∈ Adj3) :
    betaAdj u (w * w') = betaAdj u w + betaAdj u w' := by
  unfold betaAdj
  rw [dif_pos ⟨hu, Subgroup.mul_mem _ hw hw'⟩, dif_pos ⟨hu, hw⟩, dif_pos ⟨hu, hw'⟩]
  have h1 : iotaInv ⟨w * w', Subgroup.mul_mem _ hw hw'⟩ = iotaInv ⟨w, hw⟩ + iotaInv ⟨w', hw'⟩ :=
    iotaInv_mul ⟨w, hw⟩ ⟨w', hw'⟩
  rw [h1, map_add]

private theorem betaAdj_adj (g : GL (Fin 3) (ZMod 2)) (u w : AdjAmb) (hu : u ∈ Adj3) (hw : w ∈ Adj3) :
    betaAdj (adjAmbAct g u) (adjAmbAct g w) = betaAdj u w := by
  unfold betaAdj
  rw [dif_pos ⟨adjAmbAct_mem g u hu, adjAmbAct_mem g w hw⟩, dif_pos ⟨hu, hw⟩]
  have h1 : iotaInv ⟨adjAmbAct g u, adjAmbAct_mem g u hu⟩ =
      CFSG.Quasithin.H6.ρSt (slGL.symm g) (iotaInv ⟨u, hu⟩) := iotaInv_smul g ⟨u, hu⟩
  have h2 : iotaInv ⟨adjAmbAct g w, adjAmbAct_mem g w hw⟩ =
      CFSG.Quasithin.H6.ρSt (slGL.symm g) (iotaInv ⟨w, hw⟩) := iotaInv_smul g ⟨w, hw⟩
  rw [h1, h2]
  exact CFSG.Quasithin.H6.stForm_conj _ _ _

private theorem betaAdj_nondeg (u : AdjAmb) (hu : u ∈ Adj3) (hu1 : u ≠ 1) :
    ∃ w ∈ Adj3, betaAdj u w ≠ 0 := by
  by_contra hcon
  push_neg at hcon
  apply hu1
  have hx : iotaInv ⟨u, hu⟩ = 0 := by
    apply CFSG.Quasithin.H6.stForm_nondeg
    intro y
    have hw : Multiplicative.ofAdd y.1 ∈ Adj3 := (mem_Adj3_iff _).2 (CFSG.Quasithin.H6.mem_stSub.1 y.2)
    have h0 := hcon _ hw
    unfold betaAdj at h0
    rw [dif_pos ⟨hu, hw⟩] at h0
    have hy : iotaInv ⟨Multiplicative.ofAdd y.1, hw⟩ = y := by
      apply Subtype.ext
      rfl
    rw [hy] at h0
    exact h0
  have h2 : Multiplicative.toAdd u = 0 := congrArg Subtype.val hx
  apply Multiplicative.toAdd.injective
  rw [h2, toAdd_one]


private theorem H63_part1 : ∃ (ι : ↥Adj3 →* Multiplicative (GL (Fin 3) (ZMod 2) → ZMod 2))
    (π : Multiplicative (GL (Fin 3) (ZMod 2) → ZMod 2) →* AdjAmb),
    (∀ x : ↥Adj3, π (ι x) = (x : AdjAmb)) ∧ (∀ f, π f ∈ Adj3) ∧
    (∀ (g : GL (Fin 3) (ZMod 2)) (x x' : ↥Adj3), (x' : AdjAmb) = adjAmbAct g x →
      ι x' = permModAct (GL (Fin 3) (ZMod 2)) (GL (Fin 3) (ZMod 2)) g (ι x)) ∧
    (∀ (g : GL (Fin 3) (ZMod 2)) (f : Multiplicative (GL (Fin 3) (ZMod 2) → ZMod 2)),
      π (permModAct (GL (Fin 3) (ZMod 2)) (GL (Fin 3) (ZMod 2)) g f) = adjAmbAct g (π f)) := by
  obtain ⟨p, hp1, hp2⟩ := CFSG.Quasithin.H6.st_injective regSL63
    (fun φ => funext fun h => zmod2_self_add' _) stF63 stF63_injective stF63_equiv
  let ι : ↥Adj3 →* Multiplicative (GL (Fin 3) (ZMod 2) → ZMod 2) :=
    { toFun := fun y => Multiplicative.ofAdd (stF63 (iotaInv y))
      map_one' := by
        have h0 : iotaInv (1 : ↥Adj3) = 0 := by
          apply Subtype.ext
          rfl
        show Multiplicative.ofAdd (stF63 (iotaInv 1)) = 1
        rw [h0, map_zero, ofAdd_zero]
      map_mul' := fun y z => by
        show Multiplicative.ofAdd (stF63 (iotaInv (y * z))) =
          Multiplicative.ofAdd (stF63 (iotaInv y)) * Multiplicative.ofAdd (stF63 (iotaInv z))
        rw [iotaInv_mul, map_add, ofAdd_add] }
  let π : Multiplicative (GL (Fin 3) (ZMod 2) → ZMod 2) →* AdjAmb :=
    { toFun := fun F => Multiplicative.ofAdd ((p (Multiplicative.toAdd F)).1)
      map_one' := by
        show Multiplicative.ofAdd ((p (Multiplicative.toAdd (1 : Multiplicative (GL (Fin 3) (ZMod 2) → ZMod 2)))).1) = 1
        rw [toAdd_one, map_zero]
        rfl
      map_mul' := fun F G => by
        show Multiplicative.ofAdd ((p (Multiplicative.toAdd (F * G))).1) =
          Multiplicative.ofAdd ((p (Multiplicative.toAdd F)).1) * Multiplicative.ofAdd ((p (Multiplicative.toAdd G)).1)
        rw [toAdd_mul, map_add, AddSubgroup.coe_add, ofAdd_add] }
  refine ⟨ι, π, ?_, ?_, ?_, ?_⟩
  · intro x
    show Multiplicative.ofAdd ((p (Multiplicative.toAdd (Multiplicative.ofAdd (stF63 (iotaInv x))))).1) = (x : AdjAmb)
    rw [toAdd_ofAdd, hp1]
    rfl
  · intro F
    exact (mem_Adj3_iff _).2 (CFSG.Quasithin.H6.mem_stSub.1 (p _).2)
  · intro g x x' hx'
    have hx2 : iotaInv x' = CFSG.Quasithin.H6.ρSt (slGL.symm g) (iotaInv x) := by
      have e : x' = ⟨adjAmbAct g x, adjAmbAct_mem g x x.2⟩ := Subtype.ext hx'
      rw [e]
      exact iotaInv_smul g x
    apply Multiplicative.toAdd.injective
    funext h
    show stF63 (iotaInv x') h = stF63 (iotaInv x) (g⁻¹ • h)
    rw [hx2, stF63_equiv, regSL63_apply, MulEquiv.apply_symm_apply, smul_eq_mul]
  · intro g F
    have hF : Multiplicative.toAdd (permModAct (GL (Fin 3) (ZMod 2)) (GL (Fin 3) (ZMod 2)) g F) =
        regSL63 (slGL.symm g) (Multiplicative.toAdd F) := by
      funext h
      rw [regSL63_apply, MulEquiv.apply_symm_apply]
      rfl
    show Multiplicative.ofAdd ((p (Multiplicative.toAdd (permModAct (GL (Fin 3) (ZMod 2)) (GL (Fin 3) (ZMod 2)) g F))).1) =
      adjAmbAct g (Multiplicative.ofAdd ((p (Multiplicative.toAdd F)).1))
    rw [hF, hp2, rhoSt_slGL_symm_coe]
    rfl

end H63


private theorem conj_data6 (T : Subgroup (GL (Fin 3) (ZMod 2))) (p : V3)
    (l : Submodule (ZMod 2) V3)
    (hyp : CFSG.ASVolI.ChH.HypH5 T p l) :
    ∃ c : GL (Fin 3) (ZMod 2), (∀ g : GL (Fin 3) (ZMod 2), g ∈ T ↔ c⁻¹ * g * c ∈ B0) ∧
      (∀ y ∈ B0, c * y * c⁻¹ ∈ T) ∧
      (c : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec e1 = p ∧
      (∀ v : V3, (c : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec v ∈ l ↔ v 2 = 0) := by
  obtain ⟨-, hTp, hTi⟩ := hyp.sylow
  rw [Subgroup.relIndex_top_right] at hTi
  obtain ⟨c, hc⟩ := sylow_conj T hTp hTi
  have hconjT : ∀ y ∈ B0, c * y * c⁻¹ ∈ T := by
    intro y hy
    refine (hc _).2 ?_
    rw [show c⁻¹ * (c * y * c⁻¹) * c = y by group]
    exact hy
  have hcinv : ∀ w : Fin 3 → ZMod 2,
      ((c⁻¹ : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec
        ((c : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec w) = w := by
    intro w; rw [← mulVec_gl, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
  have hcc : ∀ w : Fin 3 → ZMod 2,
      (c : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec
        (((c⁻¹ : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec w) = w := by
    intro w; rw [← mulVec_gl, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
  obtain ⟨q, hq⟩ : ∃ q : Fin 3 → ZMod 2,
      ((c⁻¹ : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec p = q := ⟨_, rfl⟩
  have hpq : (c : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec q = p := by rw [← hq, hcc]
  have hfixq : ∀ y ∈ B0, (y : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec q = q := by
    intro y hy
    have h1 := hyp.p_fix _ (hconjT y hy)
    rw [mulVec_gl, mulVec_gl, hq] at h1
    calc (y : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec q
        = ((c⁻¹ : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec
            ((c : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec ((y : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec q)) :=
          (hcinv _).symm
      _ = q := by rw [h1, hq]
  have hq0 : q = e1 := by
    rcases fixB0 q hfixq with h | h
    · exfalso
      apply hyp.p_ne
      rw [← hpq, h, Matrix.mulVec_zero]
    · exact h
  have hpc : (c : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec e1 = p := by rw [← hq0, hpq]
  have hline : ∀ v : Fin 3 → ZMod 2, (c : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec v ∈ l ↔ v 2 = 0 := by
    classical
    have hfr : Module.finrank (ZMod 2) l = 2 := hyp.l_line
    have hcardl : Nat.card l = 4 := natCard_of_finrank_two l hfr
    refine line_unique (fun v => (c : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec v ∈ l) ?_ ?_ ?_ ?_ ?_
    · simp
    · intro a b ha hb
      rw [Matrix.mulVec_add]
      exact l.add_mem ha hb
    · let e' : (Fin 3 → ZMod 2) ≃ (Fin 3 → ZMod 2) :=
        { toFun := fun v => (c : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec v
          invFun := fun w => ((c⁻¹ : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec w
          left_inv := hcinv
          right_inv := hcc }
      have h1 : (Finset.univ.filter (fun v : Fin 3 → ZMod 2 =>
            (c : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec v ∈ l)).card =
          (Finset.univ.filter (fun w : Fin 3 → ZMod 2 => w ∈ l)).card :=
        Finset.card_equiv e' (fun i => by simp [e'])
      rw [h1, ← Fintype.card_subtype]
      have := hcardl
      rw [Nat.card_eq_fintype_card] at this
      exact this
    · intro v hv
      have h := hyp.l_inv _ (hconjT _ tG_mem) _ hv
      rw [mulVec_gl, mulVec_gl, hcinv] at h
      show (c : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec
        ((!![1, 1, 0; 0, 1, 0; 0, 0, 1] : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec v) ∈ l
      rw [← tG_mat]
      exact h
    · intro v hv
      have h := hyp.l_inv _ (hconjT _ uG_mem) _ hv
      rw [mulVec_gl, mulVec_gl, hcinv] at h
      show (c : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec
        ((!![1, 0, 0; 0, 1, 1; 0, 0, 1] : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec v) ∈ l
      rw [← uG_mat]
      exact h
  exact ⟨c, hc, hconjT, hpc, hline⟩



private theorem B0_fix_e1_6 (x : GL (Fin 3) (ZMod 2)) (hx : x ∈ B0) : x ∈ Lpt e1 := by
  obtain ⟨a, b, c, hx'⟩ := (mem_B0 x).1 hx
  rw [mem_Lpt]
  intro v hv
  rw [Set.mem_singleton_iff.1 hv, hx']
  funext i
  fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, e1]

private theorem B0_le_Lln_line0_6 (x : GL (Fin 3) (ZMod 2)) (hx : x ∈ B0) : x ∈ Lln line0 := by
  have key : ∀ k : GL (Fin 3) (ZMod 2), k ∈ B0 → ∀ v : V3, v 2 = 0 →
      (k : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec v 2 = 0 := by
    intro k hk v hv
    obtain ⟨a, b', c', hk'⟩ := (mem_B0 k).1 hk
    rw [hk']
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, hv]
  rw [mem_Lln]
  intro v hv
  have hv' : v 2 = 0 := mem_line0.1 (SetLike.mem_coe.1 hv)
  exact ⟨mem_line0.2 (key x hx v hv'), mem_line0.2 (key _ (Subgroup.inv_mem B0 hx) v hv')⟩

private theorem borel_iff_B0 (h : CFSG.Quasithin.H6.Γ) :
    h ∈ CFSG.Quasithin.H6.borel ↔ slGL h ∈ B0 := by
  rw [CFSG.Quasithin.H6.borel, Subgroup.mem_inf]
  constructor
  · rintro ⟨hLp, hLl⟩
    exact Lpt_inter_le_B0 (slGL h) ((mem_Lpt _ _).1 ((mem_Lp_iff h).1 hLp))
      (fun v hv => ((mem_Lln _ _).1 ((mem_Ll_iff h).1 hLl) v hv).1)
  · intro hB
    exact ⟨(mem_Lp_iff h).2 (B0_fix_e1_6 _ hB), (mem_Ll_iff h).2 (B0_le_Lln_line0_6 _ hB)⟩

private theorem mulVec_conj6 (c b : GL (Fin 3) (ZMod 2)) (y : V3) :
    ((c * b * c⁻¹ : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec y =
      (c : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec
        ((b : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec
          (((c⁻¹ : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec y)) := by
  rw [mulVec_gl, mulVec_gl]

private theorem mem_Lpt_conj6 (c : GL (Fin 3) (ZMod 2)) (p : V3)
    (hpc : (c : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec e1 = p) (k : GL (Fin 3) (ZMod 2))
    (hk : k ∈ Lpt e1) : c * k * c⁻¹ ∈ Lpt p := by
  rw [mem_Lpt]
  intro v hv
  rw [Set.mem_singleton_iff.1 hv, ← hpc, mulVec_conj6, inv_mulVec_mulVec]
  rw [(mem_Lpt _ _).1 hk e1 (Set.mem_singleton _)]

private theorem rho_mul_apply6 (a b : CFSG.Quasithin.H6.Γ) (x : CFSG.Quasithin.H6.St) :
    CFSG.Quasithin.H6.ρSt (a * b) x = CFSG.Quasithin.H6.ρSt a (CFSG.Quasithin.H6.ρSt b x) :=
  sigma_mul CFSG.Quasithin.H6.ρSt a b x

private theorem iotaInv_inj6 {y z : ↥Adj3} (h : iotaInv y = iotaInv z) : y = z := by
  apply Subtype.ext
  have h4 : Multiplicative.toAdd y.1 = Multiplicative.toAdd z.1 :=
    congrArg (fun m : CFSG.Quasithin.H6.St => m.1) h
  exact Multiplicative.toAdd.injective h4

private theorem adj_fix_iff6 (g : GL (Fin 3) (ZMod 2)) (y : ↥Adj3) :
    adjAmbAct g (y : AdjAmb) = (y : AdjAmb) ↔
      CFSG.Quasithin.H6.ρSt (slGL.symm g) (iotaInv y) = iotaInv y := by
  have key : iotaInv (⟨adjAmbAct g (y : AdjAmb), adjAmbAct_mem g _ y.2⟩ : ↥Adj3) =
      CFSG.Quasithin.H6.ρSt (slGL.symm g) (iotaInv y) := iotaInv_smul g y
  constructor
  · intro h
    have e : (⟨adjAmbAct g (y : AdjAmb), adjAmbAct_mem g _ y.2⟩ : ↥Adj3) = y := Subtype.ext h
    rw [← key, e]
  · intro h
    have e : (⟨adjAmbAct g (y : AdjAmb), adjAmbAct_mem g _ y.2⟩ : ↥Adj3) = y :=
      iotaInv_inj6 (by rw [key, h])
    exact congrArg Subtype.val e


private theorem H63_part2b (α : MulAut (GL (Fin 3) (ZMod 2))) :
    ∃ e : ↥Adj3 →* AdjAmb, Function.Injective e ∧ e.range = Adj3 ∧
      ∀ (g : GL (Fin 3) (ZMod 2)) (x y : ↥Adj3), (y : AdjAmb) = adjAmbAct (α g) x →
        e y = adjAmbAct g (e x) := by
  let α' : CFSG.Quasithin.H6.Γ ≃* CFSG.Quasithin.H6.Γ := slGL.trans (α.trans slGL.symm)
  obtain ⟨f, hfbij, hfeq⟩ := CFSG.Quasithin.H6.isoMod_twist CFSG.Quasithin.H6.volI_H_6_5 α'
  let e : ↥Adj3 →* AdjAmb :=
    { toFun := fun y => Multiplicative.ofAdd ((f (iotaInv y)).1)
      map_one' := by
        have h0 : iotaInv (1 : ↥Adj3) = 0 := by
          apply Subtype.ext
          rfl
        show Multiplicative.ofAdd ((f (iotaInv 1)).1) = 1
        rw [h0, map_zero, AddSubgroup.coe_zero, ofAdd_zero]
      map_mul' := fun y z => by
        show Multiplicative.ofAdd ((f (iotaInv (y * z))).1) =
          Multiplicative.ofAdd ((f (iotaInv y)).1) * Multiplicative.ofAdd ((f (iotaInv z)).1)
        rw [iotaInv_mul, map_add, AddSubgroup.coe_add, ofAdd_add] }
  refine ⟨e, ?_, ?_, ?_⟩
  · intro y z hyz
    have h1 : (f (iotaInv y)).1 = (f (iotaInv z)).1 := Multiplicative.ofAdd.injective hyz
    have h2 : f (iotaInv y) = f (iotaInv z) := Subtype.ext h1
    exact iotaInv_inj6 (hfbij.1 h2)
  · ext X
    rw [MonoidHom.mem_range]
    constructor
    · rintro ⟨y, rfl⟩
      exact (mem_Adj3_iff _).2 (CFSG.Quasithin.H6.mem_stSub.1 (f (iotaInv y)).2)
    · intro hX
      obtain ⟨z, hz⟩ := hfbij.2 ⟨Multiplicative.toAdd X, CFSG.Quasithin.H6.mem_stSub.2 ((mem_Adj3_iff X).1 hX)⟩
      refine ⟨iotaOf z, ?_⟩
      show Multiplicative.ofAdd ((f (iotaInv (iotaOf z))).1) = X
      rw [iotaInv_iotaOf, hz]
      rfl
  · intro g x y hy
    have hy' : iotaInv y = CFSG.Quasithin.H6.ρSt (slGL.symm (α g)) (iotaInv x) := by
      have e1 : y = ⟨adjAmbAct (α g) x.1, adjAmbAct_mem (α g) x.1 x.2⟩ := Subtype.ext hy
      rw [e1]
      exact iotaInv_smul (α g) x
    have hα : slGL.symm (α g) = α' (slGL.symm g) := by
      show slGL.symm (α g) = slGL.symm (α (slGL (slGL.symm g)))
      rw [MulEquiv.apply_symm_apply]
    have hfg : f (CFSG.Quasithin.H6.ρSt (α' (slGL.symm g)) (iotaInv x)) =
        CFSG.Quasithin.H6.ρSt (slGL.symm g) (f (iotaInv x)) := hfeq (slGL.symm g) (iotaInv x)
    show Multiplicative.ofAdd ((f (iotaInv y)).1) =
      adjAmbAct g (Multiplicative.ofAdd ((f (iotaInv x)).1))
    rw [hy', hα, hfg, rhoSt_slGL_symm_coe]
    rfl

private theorem conj_cancel6 {G : Type*} [Group G] (a b : G) : a * (a⁻¹ * b * a) * a⁻¹ = b := by
  simp [mul_assoc]

private theorem H63_part4 (T : Subgroup (GL (Fin 3) (ZMod 2))) (p : V3) (l : Submodule (ZMod 2) V3)
    (hyp : CFSG.ASVolI.ChH.HypH5 T p l) :
    ∃ m ∈ Adj3, m ≠ 1 ∧ (∀ g ∈ T, adjAmbAct g m = m) ∧
      (∀ m' ∈ Adj3, m' ≠ 1 → (∀ g ∈ T, adjAmbAct g m' = m') → m' = m) ∧
      ∀ g : GL (Fin 3) (ZMod 2), adjAmbAct g m = m → g ∈ T := by
  obtain ⟨c, hc, -, -, -⟩ := conj_data6 T p l hyp
  obtain ⟨m0, hm0, hfix, huniq⟩ := CFSG.Quasithin.H6.st_fix_borel
  obtain ⟨sc, hsc⟩ : ∃ sc : CFSG.Quasithin.H6.Γ, slGL sc = c :=
    ⟨slGL.symm c, MulEquiv.apply_symm_apply slGL c⟩
  have hinv : ∀ w : CFSG.Quasithin.H6.St, CFSG.Quasithin.H6.ρSt sc⁻¹ (CFSG.Quasithin.H6.ρSt sc w) = w :=
    fun w => sigma_inv_left CFSG.Quasithin.H6.ρSt sc w
  have hfwd : ∀ w : CFSG.Quasithin.H6.St, CFSG.Quasithin.H6.ρSt sc (CFSG.Quasithin.H6.ρSt sc⁻¹ w) = w :=
    fun w => sigma_inv_right CFSG.Quasithin.H6.ρSt sc w
  have hconv : ∀ g : GL (Fin 3) (ZMod 2),
      g ∈ T ↔ sc⁻¹ * slGL.symm g * sc ∈ CFSG.Quasithin.H6.borel := by
    intro g
    rw [borel_iff_B0, map_mul, map_mul, map_inv, hsc, MulEquiv.apply_symm_apply]
    exact hc g
  have hsymm : ∀ h : CFSG.Quasithin.H6.Γ, slGL.symm (c * slGL h * c⁻¹) = sc * h * sc⁻¹ := by
    intro h
    apply slGL.injective
    rw [MulEquiv.apply_symm_apply, map_mul, map_mul, map_inv, hsc]
  have hm1ne : CFSG.Quasithin.H6.ρSt sc m0 ≠ 0 := by
    intro h0
    apply hm0
    calc m0 = CFSG.Quasithin.H6.ρSt sc⁻¹ (CFSG.Quasithin.H6.ρSt sc m0) := (hinv m0).symm
      _ = CFSG.Quasithin.H6.ρSt sc⁻¹ 0 := by rw [h0]
      _ = 0 := map_zero _
  have hkey : ∀ h : CFSG.Quasithin.H6.Γ, CFSG.Quasithin.H6.ρSt h m0 = m0 →
      CFSG.Quasithin.H6.ρSt (sc * h * sc⁻¹) (CFSG.Quasithin.H6.ρSt sc m0) =
        CFSG.Quasithin.H6.ρSt sc m0 := by
    intro h hh
    rw [rho_mul_apply6 (sc * h) sc⁻¹, hinv m0, rho_mul_apply6 sc h, hh]
  refine ⟨((iotaOf (CFSG.Quasithin.H6.ρSt sc m0) : ↥Adj3) : AdjAmb), (iotaOf (CFSG.Quasithin.H6.ρSt sc m0)).2,
    ?_, ?_, ?_, ?_⟩
  · intro h1
    apply hm1ne
    have h2 : (CFSG.Quasithin.H6.ρSt sc m0).1 = 0 :=
      congrArg (fun y : AdjAmb => Multiplicative.toAdd y) h1
    exact Subtype.ext h2
  · intro g hg
    rw [adj_fix_iff6, iotaInv_iotaOf]
    have hb : sc⁻¹ * slGL.symm g * sc ∈ CFSG.Quasithin.H6.borel := (hconv g).1 hg
    have e2 : sc * (sc⁻¹ * slGL.symm g * sc) * sc⁻¹ = slGL.symm g := conj_cancel6 sc _
    have := hkey _ (hfix _ hb)
    rw [e2] at this
    exact this
  · intro m' hm' hne hfixT
    have hyne : iotaInv (⟨m', hm'⟩ : ↥Adj3) ≠ 0 := by
      intro h0
      apply hne
      have h1 : Multiplicative.toAdd m' = 0 := congrArg Subtype.val h0
      exact Multiplicative.toAdd.injective (by rw [h1, toAdd_one])
    have hfixz : ∀ h ∈ CFSG.Quasithin.H6.borel,
        CFSG.Quasithin.H6.ρSt h (CFSG.Quasithin.H6.ρSt sc⁻¹ (iotaInv (⟨m', hm'⟩ : ↥Adj3))) =
          CFSG.Quasithin.H6.ρSt sc⁻¹ (iotaInv (⟨m', hm'⟩ : ↥Adj3)) := by
      intro h hh
      have hT : c * slGL h * c⁻¹ ∈ T := (hc _).2 (by
        rw [show c⁻¹ * (c * slGL h * c⁻¹) * c = slGL h from conj_cancel6 c⁻¹ _ |>.symm ▸ rfl]
        exact (borel_iff_B0 h).1 hh)
      have e1 := (adj_fix_iff6 (c * slGL h * c⁻¹) ⟨m', hm'⟩).1 (hfixT _ hT)
      rw [hsymm h] at e1
      have e3 : sc⁻¹ * (sc * h * sc⁻¹) = h * sc⁻¹ := by simp [mul_assoc]
      calc CFSG.Quasithin.H6.ρSt h (CFSG.Quasithin.H6.ρSt sc⁻¹ (iotaInv (⟨m', hm'⟩ : ↥Adj3)))
          = CFSG.Quasithin.H6.ρSt (h * sc⁻¹) (iotaInv (⟨m', hm'⟩ : ↥Adj3)) :=
            (rho_mul_apply6 h sc⁻¹ _).symm
        _ = CFSG.Quasithin.H6.ρSt (sc⁻¹ * (sc * h * sc⁻¹)) (iotaInv (⟨m', hm'⟩ : ↥Adj3)) := by
            rw [e3]
        _ = CFSG.Quasithin.H6.ρSt sc⁻¹ (CFSG.Quasithin.H6.ρSt (sc * h * sc⁻¹) (iotaInv (⟨m', hm'⟩ : ↥Adj3))) :=
            rho_mul_apply6 _ _ _
        _ = CFSG.Quasithin.H6.ρSt sc⁻¹ (iotaInv (⟨m', hm'⟩ : ↥Adj3)) := by rw [e1]
    have hzne : CFSG.Quasithin.H6.ρSt sc⁻¹ (iotaInv (⟨m', hm'⟩ : ↥Adj3)) ≠ 0 := by
      intro h0
      apply hyne
      calc iotaInv (⟨m', hm'⟩ : ↥Adj3) = CFSG.Quasithin.H6.ρSt sc (CFSG.Quasithin.H6.ρSt sc⁻¹
              (iotaInv (⟨m', hm'⟩ : ↥Adj3))) := (hfwd _).symm
        _ = CFSG.Quasithin.H6.ρSt sc 0 := by rw [h0]
        _ = 0 := map_zero _
    have hz0 := huniq _ hzne hfixz
    have hw : iotaInv (⟨m', hm'⟩ : ↥Adj3) = CFSG.Quasithin.H6.ρSt sc m0 := by
      calc iotaInv (⟨m', hm'⟩ : ↥Adj3) = CFSG.Quasithin.H6.ρSt sc (CFSG.Quasithin.H6.ρSt sc⁻¹
              (iotaInv (⟨m', hm'⟩ : ↥Adj3))) := (hfwd _).symm
        _ = CFSG.Quasithin.H6.ρSt sc m0 := by rw [hz0]
    exact congrArg Subtype.val (iotaInv_inj6 (hw.trans (iotaInv_iotaOf _).symm))
  · intro g hg
    rw [adj_fix_iff6, iotaInv_iotaOf] at hg
    apply (hconv g).2
    apply CFSG.Quasithin.H6.st_stabilizer m0 hm0 hfix
    rw [rho_mul_apply6 (sc⁻¹ * slGL.symm g) sc, rho_mul_apply6 sc⁻¹ (slGL.symm g), hg, hinv m0]

private theorem H63_part2a : ∃ β : AdjAmb → AdjAmb → ZMod 2,
    (∀ u ∈ Adj3, ∀ u' ∈ Adj3, ∀ w ∈ Adj3, β (u * u') w = β u w + β u' w) ∧
    (∀ u ∈ Adj3, ∀ w ∈ Adj3, ∀ w' ∈ Adj3, β u (w * w') = β u w + β u w') ∧
    (∀ (g : GL (Fin 3) (ZMod 2)), ∀ u ∈ Adj3, ∀ w ∈ Adj3,
      β (adjAmbAct g u) (adjAmbAct g w) = β u w) ∧
    (∀ u ∈ Adj3, u ≠ 1 → ∃ w ∈ Adj3, β u w ≠ 0) :=
  ⟨betaAdj, fun u hu u' hu' w hw => betaAdj_mul_left u u' w hu hu' hw,
    fun u hu w hw w' hw' => betaAdj_mul_right u w w' hu hw hw',
    fun g u hu w hw => betaAdj_adj g u w hu hw,
    fun u hu hu1 => betaAdj_nondeg u hu hu1⟩

private theorem theta_rho (c : GL (Fin 3) (ZMod 2)) (g : CFSG.Quasithin.H6.Γ)
    (m : CFSG.Quasithin.H6.St) :
    adjAmbAct c (Multiplicative.ofAdd (CFSG.Quasithin.H6.ρSt g m).1) =
      adjAmbAct (c * slGL g * c⁻¹) (adjAmbAct c (Multiplicative.ofAdd m.1)) := by
  have hm : (CFSG.Quasithin.H6.ρSt g m).1 =
      ((slGL g : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)) * m.1 *
        (((slGL g)⁻¹ : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)) := by
    rw [coe_rhoSt, slGL_coe, ← map_inv slGL g, slGL_coe]
  rw [← MulAut.mul_apply, ← map_mul, show c * slGL g * c⁻¹ * c = c * slGL g by group, map_mul,
    MulAut.mul_apply, hm]
  rfl

private theorem comm_full_gen (c : GL (Fin 3) (ZMod 2)) (Hs : Subgroup CFSG.Quasithin.H6.Γ)
    (A : Subgroup (MulAut AdjAmb)) (hA2 : ∀ a ∈ A, ∀ x ∈ Adj3, a x ∈ Adj3)
    (hA : ∀ g ∈ Hs, adjAmbAct (c * slGL g * c⁻¹) ∈ A)
    (hclos : AddSubgroup.closure {y : CFSG.Quasithin.H6.St | ∃ g ∈ Hs, ∃ m : CFSG.Quasithin.H6.St,
      y = CFSG.Quasithin.H6.ρSt g m - m} = ⊤) :
    commOn Adj3 A = Adj3 := by
  apply le_antisymm
  · unfold commOn
    apply (Subgroup.closure_le _).2
    rintro u ⟨a, ha, w, hw, rfl⟩
    exact Subgroup.mul_mem _ (hA2 a ha w hw) (Subgroup.inv_mem _ hw)
  · intro X hX
    let θ : CFSG.Quasithin.H6.St → AdjAmb := fun x => adjAmbAct c (Multiplicative.ofAdd x.1)
    have hθmem : ∀ x : CFSG.Quasithin.H6.St, θ x ∈ Adj3 := fun x =>
      adjAmbAct_mem c _ ((mem_Adj3_iff _).2 (CFSG.Quasithin.H6.mem_stSub.1 x.2))
    have hθ : ∀ x ∈ AddSubgroup.closure {y : CFSG.Quasithin.H6.St | ∃ g ∈ Hs, ∃ m : CFSG.Quasithin.H6.St,
        y = CFSG.Quasithin.H6.ρSt g m - m}, θ x ∈ commOn Adj3 A := by
      intro x hx
      induction hx using AddSubgroup.closure_induction with
      | mem y hy =>
        obtain ⟨g, hg, m, rfl⟩ := hy
        have e : θ (CFSG.Quasithin.H6.ρSt g m - m) = θ (CFSG.Quasithin.H6.ρSt g m) * (θ m)⁻¹ := by
          show adjAmbAct c (Multiplicative.ofAdd (CFSG.Quasithin.H6.ρSt g m - m).1) =
            adjAmbAct c (Multiplicative.ofAdd (CFSG.Quasithin.H6.ρSt g m).1) *
              (adjAmbAct c (Multiplicative.ofAdd m.1))⁻¹
          rw [AddSubgroup.coe_sub, ofAdd_sub, div_eq_mul_inv, map_mul, map_inv]
        rw [e]
        have e2 : θ (CFSG.Quasithin.H6.ρSt g m) = adjAmbAct (c * slGL g * c⁻¹) (θ m) :=
          theta_rho c g m
        rw [e2]
        exact Subgroup.subset_closure ⟨_, hA g hg, θ m, hθmem m, rfl⟩
      | zero =>
        have e : θ 0 = 1 := by
          show adjAmbAct c (Multiplicative.ofAdd (0 : CFSG.Quasithin.H6.St).1) = 1
          rw [AddSubgroup.coe_zero, ofAdd_zero, map_one]
        rw [e]
        exact one_mem _
      | add y z _ _ hy hz =>
        have e : θ (y + z) = θ y * θ z := by
          show adjAmbAct c (Multiplicative.ofAdd (y + z).1) =
            adjAmbAct c (Multiplicative.ofAdd y.1) * adjAmbAct c (Multiplicative.ofAdd z.1)
          rw [AddSubgroup.coe_add, ofAdd_add, map_mul]
        rw [e]
        exact mul_mem hy hz
      | neg y _ hy =>
        have e : θ (-y) = (θ y)⁻¹ := by
          show adjAmbAct c (Multiplicative.ofAdd (-y).1) = (adjAmbAct c (Multiplicative.ofAdd y.1))⁻¹
          rw [AddSubgroup.coe_neg, ofAdd_neg, map_inv]
        rw [e]
        exact inv_mem hy
    have hX' : adjAmbAct c⁻¹ X ∈ Adj3 := adjAmbAct_mem c⁻¹ X hX
    let x : CFSG.Quasithin.H6.St :=
      ⟨Multiplicative.toAdd (adjAmbAct c⁻¹ X), CFSG.Quasithin.H6.mem_stSub.2 ((mem_Adj3_iff _).1 hX')⟩
    have hxmem : x ∈ AddSubgroup.closure {y : CFSG.Quasithin.H6.St | ∃ g ∈ Hs, ∃ m : CFSG.Quasithin.H6.St,
        y = CFSG.Quasithin.H6.ρSt g m - m} := by
      rw [hclos]
      exact AddSubgroup.mem_top x
    have hx := hθ x hxmem
    have e : θ x = X := by
      show adjAmbAct c (Multiplicative.ofAdd (Multiplicative.toAdd (adjAmbAct c⁻¹ X))) = X
      rw [ofAdd_toAdd, ← MulAut.mul_apply, ← map_mul, mul_inv_cancel, map_one, MulAut.one_apply]
    rw [e] at hx
    exact hx

private theorem H63_part5 (T : Subgroup (GL (Fin 3) (ZMod 2))) (p : V3) (l : Submodule (ZMod 2) V3)
    (hyp : CFSG.ASVolI.ChH.HypH5 T p l) :
    commOn Adj3 ((Lln l).map adjAmbAct) = Adj3 ∧ commOn Adj3 ((Lpt p).map adjAmbAct) = Adj3 := by
  obtain ⟨c, -, -, hpc, hline⟩ := conj_data6 T p l hyp
  constructor
  · refine comm_full_gen c CFSG.Quasithin.H6.Ll ((Lln l).map adjAmbAct) ?_ ?_
      CFSG.Quasithin.H6.st_comm_Ll
    · intro a ha x hx
      obtain ⟨g, -, rfl⟩ := Subgroup.mem_map.1 ha
      exact adjAmbAct_mem g x hx
    · intro g hg
      exact Subgroup.mem_map_of_mem adjAmbAct
        ((mem_Lln_conj c l hline (slGL g)).1 ((mem_Ll_iff g).1 hg))
  · refine comm_full_gen c CFSG.Quasithin.H6.Lp ((Lpt p).map adjAmbAct) ?_ ?_
      CFSG.Quasithin.H6.st_comm_Lp
    · intro a ha x hx
      obtain ⟨g, -, rfl⟩ := Subgroup.mem_map.1 ha
      exact adjAmbAct_mem g x hx
    · intro g hg
      exact Subgroup.mem_map_of_mem adjAmbAct (mem_Lpt_conj6 c p hpc (slGL g) ((mem_Lp_iff g).1 hg))


private theorem adj_cancel6 (c : GL (Fin 3) (ZMod 2)) (x : AdjAmb) :
    adjAmbAct c (adjAmbAct c⁻¹ x) = x := by
  rw [← MulAut.mul_apply, ← map_mul, mul_inv_cancel, map_one, MulAut.one_apply]

private theorem adj_cancel6' (c : GL (Fin 3) (ZMod 2)) (x : AdjAmb) :
    adjAmbAct c⁻¹ (adjAmbAct c x) = x := by
  rw [← MulAut.mul_apply, ← map_mul, inv_mul_cancel, map_one, MulAut.one_apply]

private theorem adj_conj_comm2 (c g : GL (Fin 3) (ZMod 2)) (y : AdjAmb) :
    adjAmbAct (c⁻¹ * g * c) y = adjAmbAct c⁻¹ (adjAmbAct g (adjAmbAct c y)) := by
  rw [map_mul, map_mul, MulAut.mul_apply, MulAut.mul_apply]

private theorem adj_inv_act (c g : GL (Fin 3) (ZMod 2)) (x : AdjAmb) :
    adjAmbAct c⁻¹ (adjAmbAct g x) = adjAmbAct (c⁻¹ * g * c) (adjAmbAct c⁻¹ x) := by
  rw [adj_conj_comm2, adj_cancel6]

private theorem adj_conj_comm (c g : GL (Fin 3) (ZMod 2)) (y : AdjAmb) :
    adjAmbAct (c * g * c⁻¹) y = adjAmbAct c (adjAmbAct g (adjAmbAct c⁻¹ y)) := by
  rw [map_mul, map_mul, MulAut.mul_apply, MulAut.mul_apply]

set_option maxHeartbeats 1000000 in
private theorem ncc_transport (c : GL (Fin 3) (ZMod 2)) (H H' : Subgroup (GL (Fin 3) (ZMod 2)))
    (hH : ∀ g : GL (Fin 3) (ZMod 2), g ∈ H ↔ c * g * c⁻¹ ∈ H') (k : ℕ)
    (hnc : NoncentralChiefCount {f : AdjAmb → AdjAmb | ∃ g ∈ H, f = fun x => adjAmbAct g x} Adj3 k) :
    NoncentralChiefCount {f : AdjAmb → AdjAmb | ∃ g ∈ H', f = fun x => adjAmbAct g x} Adj3 k := by
  obtain ⟨n, S, h0, hn, hch, hcount⟩ := hnc
  obtain ⟨S', hS'def⟩ : ∃ S' : ℕ → Subgroup AdjAmb,
      S' = fun i => (S i).map (adjAmbAct c : MulAut AdjAmb).toMonoidHom := ⟨_, rfl⟩
  have hmem : ∀ i x, x ∈ S' i ↔ adjAmbAct c⁻¹ x ∈ S i := by
    intro i x
    rw [hS'def]
    constructor
    · rintro ⟨y, hy, rfl⟩
      show adjAmbAct c⁻¹ (adjAmbAct c y) ∈ S i
      rw [adj_cancel6']
      exact hy
    · intro hx
      exact ⟨adjAmbAct c⁻¹ x, hx, adj_cancel6 c x⟩
  have hH' : ∀ g' : GL (Fin 3) (ZMod 2), g' ∈ H' → c⁻¹ * g' * c ∈ H := fun g' hg' => by
    rw [hH]
    simpa [mul_assoc] using hg'
  have hH'' : ∀ g : GL (Fin 3) (ZMod 2), g ∈ H → c * g * c⁻¹ ∈ H' := fun g hg => (hH g).1 hg
  have hS'0 : S' 0 = ⊥ := by
    ext x
    rw [hmem, h0, Subgroup.mem_bot, Subgroup.mem_bot]
    exact MulEquiv.map_eq_one_iff (adjAmbAct c⁻¹ : MulAut AdjAmb)
  have hS'n : S' n = Adj3 := by
    ext x
    rw [hmem, hn]
    constructor
    · intro h
      have := adjAmbAct_mem c _ h
      rwa [adj_cancel6] at this
    · intro h
      exact adjAmbAct_mem c⁻¹ x h
  have hactS' : ∀ j, IsActsInv {f : AdjAmb → AdjAmb | ∃ g ∈ H, f = fun x => adjAmbAct g x} (S j) →
      IsActsInv {f : AdjAmb → AdjAmb | ∃ g ∈ H', f = fun x => adjAmbAct g x} (S' j) := by
    intro j hinv f hf x hx
    obtain ⟨g', hg', rfl⟩ := hf
    show adjAmbAct g' x ∈ S' j
    rw [hmem] at hx ⊢
    have e : adjAmbAct c⁻¹ (adjAmbAct g' x) = adjAmbAct (c⁻¹ * g' * c) (adjAmbAct c⁻¹ x) := by
      rw [adj_conj_comm2, adj_cancel6]
    rw [e]
    exact hinv (fun y => adjAmbAct (c⁻¹ * g' * c) y) ⟨c⁻¹ * g' * c, hH' g' hg', rfl⟩ _ hx
  have hchief : ∀ i, i < n → IsChiefFactorUnder {f : AdjAmb → AdjAmb | ∃ g ∈ H', f = fun x => adjAmbAct g x}
      (S' i) (S' (i + 1)) := by
    intro i hi
    obtain ⟨hlt, hinvX, hinvY, hmax⟩ := hch i hi
    refine ⟨?_, hactS' i hinvX, hactS' (i + 1) hinvY, ?_⟩
    · have hle : S' i ≤ S' (i + 1) := by
        rw [hS'def]
        exact Subgroup.map_mono hlt.le
      refine lt_of_le_of_ne hle ?_
      intro heq
      rw [hS'def] at heq
      exact hlt.ne (Subgroup.map_injective (f := (adjAmbAct c : MulAut AdjAmb).toMonoidHom)
        (MulEquiv.injective _) heq)
    · intro W hW1 hW2 hWact
      obtain ⟨W0, hW0def⟩ : ∃ W0 : Subgroup AdjAmb,
          W0 = W.comap (adjAmbAct c : MulAut AdjAmb).toMonoidHom := ⟨_, rfl⟩
      have hW0mem : ∀ x, x ∈ W0 ↔ adjAmbAct c x ∈ W := fun x => by rw [hW0def]; rfl
      have hW0a : S i ≤ W0 := by
        intro x hx
        rw [hW0mem]
        exact hW1 ((hmem i _).2 (by rw [adj_cancel6']; exact hx))
      have hW0b : W0 ≤ S (i + 1) := by
        intro x hx
        rw [hW0mem] at hx
        have h := (hmem (i + 1) _).1 (hW2 hx)
        rwa [adj_cancel6'] at h
      have hW0c : IsActsInv {f : AdjAmb → AdjAmb | ∃ g ∈ H, f = fun x => adjAmbAct g x} W0 := by
        intro f hf x hx
        obtain ⟨g, hg, rfl⟩ := hf
        rw [hW0mem] at hx ⊢
        have e : adjAmbAct c (adjAmbAct g x) = adjAmbAct (c * g * c⁻¹) (adjAmbAct c x) := by
          rw [adj_conj_comm, adj_cancel6']
        show adjAmbAct c (adjAmbAct g x) ∈ W
        rw [e]
        exact hWact (fun y => adjAmbAct (c * g * c⁻¹) y) ⟨c * g * c⁻¹, hH'' g hg, rfl⟩ _ hx
      have key : ∀ y, y ∈ W ↔ adjAmbAct c⁻¹ y ∈ W0 := fun y => by
        rw [hW0mem, adj_cancel6]
      rcases hmax W0 hW0a hW0b hW0c with h | h
      · left
        ext y
        rw [key y, h, hmem]
      · right
        ext y
        rw [key y, h, hmem]
  refine ⟨n, S', hS'0, hS'n, hchief, ?_⟩
  have hset : {i : ℕ | i < n ∧ ∃ f ∈ {f : AdjAmb → AdjAmb | ∃ g ∈ H', f = fun x => adjAmbAct g x},
        ∃ u ∈ S' (i + 1), f u * u⁻¹ ∉ S' i} =
      {i : ℕ | i < n ∧ ∃ f ∈ {f : AdjAmb → AdjAmb | ∃ g ∈ H, f = fun x => adjAmbAct g x},
        ∃ u ∈ S (i + 1), f u * u⁻¹ ∉ S i} := by
    ext i
    simp only [Set.mem_setOf_eq]
    constructor
    · rintro ⟨hi, f, ⟨g', hg', rfl⟩, u, hu, hnot⟩
      refine ⟨hi, fun x => adjAmbAct (c⁻¹ * g' * c) x, ⟨c⁻¹ * g' * c, hH' g' hg', rfl⟩,
        adjAmbAct c⁻¹ u, (hmem (i + 1) u).1 hu, ?_⟩
      intro hin
      apply hnot
      rw [hmem]
      show adjAmbAct c⁻¹ (adjAmbAct g' u * u⁻¹) ∈ S i
      have hm : adjAmbAct c⁻¹ (adjAmbAct g' u * u⁻¹) =
          adjAmbAct c⁻¹ (adjAmbAct g' u) * adjAmbAct c⁻¹ u⁻¹ :=
        map_mul (adjAmbAct c⁻¹ : MulAut AdjAmb) _ _
      have hi : adjAmbAct c⁻¹ u⁻¹ = (adjAmbAct c⁻¹ u)⁻¹ := map_inv (adjAmbAct c⁻¹ : MulAut AdjAmb) u
      have ha : adjAmbAct c⁻¹ (adjAmbAct g' u) = adjAmbAct (c⁻¹ * g' * c) (adjAmbAct c⁻¹ u) :=
        adj_inv_act c g' u
      rw [hm, hi, ha]
      exact hin
    · rintro ⟨hi, f, ⟨g, hg, rfl⟩, u, hu, hnot⟩
      refine ⟨hi, fun x => adjAmbAct (c * g * c⁻¹) x, ⟨c * g * c⁻¹, hH'' g hg, rfl⟩,
        adjAmbAct c u, (hmem (i + 1) _).2 (by rw [adj_cancel6']; exact hu), ?_⟩
      intro hin
      rw [hmem] at hin
      apply hnot
      have e5 : adjAmbAct c⁻¹ (adjAmbAct (c * g * c⁻¹) (adjAmbAct c u) * (adjAmbAct c u)⁻¹) =
          adjAmbAct g u * u⁻¹ := by
        have hm : adjAmbAct c⁻¹ (adjAmbAct (c * g * c⁻¹) (adjAmbAct c u) * (adjAmbAct c u)⁻¹) =
            adjAmbAct c⁻¹ (adjAmbAct (c * g * c⁻¹) (adjAmbAct c u)) * adjAmbAct c⁻¹ (adjAmbAct c u)⁻¹ :=
          map_mul (adjAmbAct c⁻¹ : MulAut AdjAmb) _ _
        have hi : adjAmbAct c⁻¹ (adjAmbAct c u)⁻¹ = (adjAmbAct c⁻¹ (adjAmbAct c u))⁻¹ :=
          map_inv (adjAmbAct c⁻¹ : MulAut AdjAmb) _
        have hc1 : adjAmbAct c⁻¹ (adjAmbAct c u) = u := adj_cancel6' c u
        have hc2 : adjAmbAct c⁻¹ (adjAmbAct (c * g * c⁻¹) (adjAmbAct c u)) = adjAmbAct g u := by
          rw [adj_conj_comm, adj_cancel6', adj_cancel6']
        rw [hm, hi, hc1, hc2]
      rw [← e5]
      exact hin
  exact (congrArg Set.ncard hset).trans hcount

end CFSG.ASVolI

namespace CFSG.ASVolI.ChH

open CFSG.Quasithin CFSG.Open

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

private theorem ncc_entry_mul (a b : AdjAmb) (i j : Fin 3) :
    Multiplicative.toAdd (a * b) i j = Multiplicative.toAdd a i j + Multiplicative.toAdd b i j := by
  rw [toAdd_mul, Matrix.add_apply]

private theorem ncc_entry_inv (a : AdjAmb) (i j : Fin 3) :
    Multiplicative.toAdd a⁻¹ i j = -Multiplicative.toAdd a i j := by
  rw [toAdd_inv, Matrix.neg_apply]

private theorem ncc_entry_one (i j : Fin 3) : Multiplicative.toAdd (1 : AdjAmb) i j = 0 := by
  rw [toAdd_one, Matrix.zero_apply]

private def nccCut (Y : Subgroup AdjAmb) (i j : Fin 3) : Subgroup AdjAmb where
  carrier := {x | Multiplicative.toAdd x i j = 0 ∧ x ∈ Y}
  mul_mem' {a b} ha hb := ⟨by rw [ncc_entry_mul, ha.1, hb.1, add_zero], Y.mul_mem ha.2 hb.2⟩
  one_mem' := ⟨ncc_entry_one i j, Y.one_mem⟩
  inv_mem' {a} ha := ⟨by rw [ncc_entry_inv, ha.1, neg_zero], Y.inv_mem ha.2⟩

private theorem ncc_mem_cut {Y : Subgroup AdjAmb} {i j : Fin 3} {x : AdjAmb} :
    x ∈ nccCut Y i j ↔ Multiplicative.toAdd x i j = 0 ∧ x ∈ Y := Iff.rfl

private theorem ncc_mem_Adj3 {x : AdjAmb} :
    x ∈ Adj3 ↔ Multiplicative.toAdd x 0 0 + Multiplicative.toAdd x 1 1 +
      Multiplicative.toAdd x 2 2 = 0 := by
  simp [Adj3, Matrix.trace, Fin.sum_univ_three]

private instance nccDecCut (Y : Subgroup AdjAmb) [DecidablePred (· ∈ Y)] (i j : Fin 3) :
    DecidablePred (· ∈ nccCut Y i j) :=
  fun x => decidable_of_iff (Multiplicative.toAdd x i j = 0 ∧ x ∈ Y) Iff.rfl

private instance nccDecAdj3 : DecidablePred (· ∈ Adj3) :=
  fun _ => decidable_of_iff _ ncc_mem_Adj3.symm

private def nccActs (G : Subgroup (GL (Fin 3) (ZMod 2))) : Set (AdjAmb → AdjAmb) :=
  {f | ∃ g ∈ G, f = fun x => adjAmbAct g x}

private theorem ncc_inv_of {G : Subgroup (GL (Fin 3) (ZMod 2))} {S : Subgroup AdjAmb}
    (h : ∀ g ∈ G, ∀ x ∈ S, adjAmbAct g x ∈ S) : IsActsInv (nccActs G) S := by
  rintro f ⟨g, hg, rfl⟩ u hu
  exact h g hg u hu

private theorem ncc_hom {G : Subgroup (GL (Fin 3) (ZMod 2))} :
    ∀ f ∈ nccActs G, ∀ a b, f (a * b) = f a * f b := by
  rintro f ⟨g, -, rfl⟩ a b
  exact map_mul _ a b

private theorem ncc_toAdd_act (g : GL (Fin 3) (ZMod 2)) (x : AdjAmb) :
    Multiplicative.toAdd (adjAmbAct g x) =
      (g : Matrix (Fin 3) (Fin 3) (ZMod 2)) * Multiplicative.toAdd x *
        ((g⁻¹ : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)) := rfl

private theorem ncc_z2 (a : ZMod 2) : a = 0 ∨ a = 1 := by
  revert a; decide

private theorem ncc_z2_eq {a b : ZMod 2} (h : a + b = 0) : b = a := by
  revert a b; decide

private theorem ncc_four (c1 c2 e1 e2 d1 d2 : ZMod 2) (hc : ¬ (c1 = 0 ∧ c2 = 0))
    (he : ¬ (e1 = 0 ∧ e2 = 0)) (hce : ¬ (e1 = c1 ∧ e2 = c2)) :
    (d1 = 0 ∧ d2 = 0) ∨ (d1 = c1 ∧ d2 = c2) ∨ (d1 = e1 ∧ d2 = e2) ∨
      (d1 = c1 + e1 ∧ d2 = c2 + e2) := by
  revert hc he hce
  rcases ncc_z2 c1 with rfl | rfl <;> rcases ncc_z2 c2 with rfl | rfl <;>
    rcases ncc_z2 e1 with rfl | rfl <;> rcases ncc_z2 e2 with rfl | rfl <;>
    rcases ncc_z2 d1 with rfl | rfl <;> rcases ncc_z2 d2 with rfl | rfl <;> decide

private theorem ncc_mul3 (A X B : Matrix (Fin 3) (Fin 3) (ZMod 2)) (i j : Fin 3) :
    (A * X * B) i j =
      (A i 0 * X 0 0 + A i 1 * X 1 0 + A i 2 * X 2 0) * B 0 j +
      (A i 0 * X 0 1 + A i 1 * X 1 1 + A i 2 * X 2 1) * B 1 j +
      (A i 0 * X 0 2 + A i 1 * X 1 2 + A i 2 * X 2 2) * B 2 j := by
  simp only [Matrix.mul_apply, Fin.sum_univ_three]

private theorem ncc_AB (g : GL (Fin 3) (ZMod 2)) (i j : Fin 3) :
    (g : Matrix (Fin 3) (Fin 3) (ZMod 2)) i 0 *
        ((g⁻¹ : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)) 0 j +
      (g : Matrix (Fin 3) (Fin 3) (ZMod 2)) i 1 *
        ((g⁻¹ : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)) 1 j +
      (g : Matrix (Fin 3) (Fin 3) (ZMod 2)) i 2 *
        ((g⁻¹ : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)) 2 j =
      (1 : Matrix (Fin 3) (Fin 3) (ZMod 2)) i j := by
  have h : (g : Matrix (Fin 3) (Fin 3) (ZMod 2)) *
      ((g⁻¹ : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  rw [← h, Matrix.mul_apply, Fin.sum_univ_three]

private theorem ncc_Adj3_inv (g : GL (Fin 3) (ZMod 2)) (x : AdjAmb) (hx : x ∈ Adj3) :
    adjAmbAct g x ∈ Adj3 := by
  have key : Matrix.trace (Multiplicative.toAdd (adjAmbAct g x)) =
      Matrix.trace (Multiplicative.toAdd x) := by
    rw [ncc_toAdd_act, Matrix.trace_mul_cycle, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      Matrix.one_mul]
  have h1 : ∀ y : AdjAmb, y ∈ Adj3 ↔ Matrix.trace (Multiplicative.toAdd y) = 0 := fun y => by
    simp only [Adj3, Multiplicative.mem_toSubgroup, AddMonoidHom.mem_ker,
      Matrix.traceAddMonoidHom_apply]
  rw [h1] at hx ⊢
  rw [key]
  exact hx

private theorem ncc_act_inv_act (g : GL (Fin 3) (ZMod 2)) (u : AdjAmb) :
    adjAmbAct g⁻¹ (adjAmbAct g u) = u := by
  rw [← MulAut.mul_apply, ← map_mul, inv_mul_cancel, map_one, MulAut.one_apply]

private theorem ncc_chief_one (acts : Set (AdjAmb → AdjAmb)) (Y : Subgroup AdjAmb) (i j : Fin 3) :
    ∀ W : Subgroup AdjAmb, nccCut Y i j ≤ W → W ≤ Y → IsActsInv acts W →
      W = nccCut Y i j ∨ W = Y := by
  intro W hXW hWY _
  by_cases h : W ≤ nccCut Y i j
  · exact Or.inl (le_antisymm h hXW)
  right
  refine le_antisymm hWY ?_
  obtain ⟨w, hwW, hwX⟩ := SetLike.not_le_iff_exists.mp h
  have hwY : w ∈ Y := hWY hwW
  have hw1 : Multiplicative.toAdd w i j = 1 := by
    rcases ncc_z2 (Multiplicative.toAdd w i j) with h0 | h1
    · exact (hwX ⟨h0, hwY⟩).elim
    · exact h1
  intro y hy
  rcases ncc_z2 (Multiplicative.toAdd y i j) with h0 | h1
  · exact hXW ⟨h0, hy⟩
  · have hm : y * w⁻¹ ∈ nccCut Y i j :=
      ⟨by rw [ncc_entry_mul, ncc_entry_inv, h1, hw1]; decide, Y.mul_mem hy (Y.inv_mem hwY)⟩
    simpa using W.mul_mem (hXW hm) hwW

private theorem ncc_chief_two (acts : Set (AdjAmb → AdjAmb)) (Y : Subgroup AdjAmb) (i j k l : Fin 3)
    (hhom : ∀ f ∈ acts, ∀ a b, f (a * b) = f a * f b)
    (hX : IsActsInv acts (nccCut (nccCut Y i j) k l))
    (hwit : ∀ a b : ZMod 2, ¬ (a = 0 ∧ b = 0) → ∃ r ∈ Y, Multiplicative.toAdd r i j = a ∧
      Multiplicative.toAdd r k l = b ∧ ∃ f ∈ acts,
        ¬ (Multiplicative.toAdd (f r) i j = 0 ∧ Multiplicative.toAdd (f r) k l = 0) ∧
        ¬ (Multiplicative.toAdd (f r) i j = a ∧ Multiplicative.toAdd (f r) k l = b)) :
    ∀ W : Subgroup AdjAmb, nccCut (nccCut Y i j) k l ≤ W → W ≤ Y → IsActsInv acts W →
      W = nccCut (nccCut Y i j) k l ∨ W = Y := by
  intro W hXW hWY hW
  by_cases h : W ≤ nccCut (nccCut Y i j) k l
  · exact Or.inl (le_antisymm h hXW)
  right
  refine le_antisymm hWY ?_
  obtain ⟨w, hwW, hwX⟩ := SetLike.not_le_iff_exists.mp h
  have hwY : w ∈ Y := hWY hwW
  have hab : ¬ (Multiplicative.toAdd w i j = 0 ∧ Multiplicative.toAdd w k l = 0) :=
    fun hh => hwX ⟨hh.2, hh.1, hwY⟩
  obtain ⟨r, hrY, hra, hrb, f, hf, he0, hec⟩ := hwit _ _ hab
  have hx : r⁻¹ * w ∈ nccCut (nccCut Y i j) k l :=
    ⟨by rw [ncc_entry_mul, ncc_entry_inv, hrb, neg_add_cancel],
      by rw [ncc_entry_mul, ncc_entry_inv, hra, neg_add_cancel], Y.mul_mem (Y.inv_mem hrY) hwY⟩
  have hfx := hX f hf _ hx
  have hfw : f w = f r * f (r⁻¹ * w) := by rw [← hhom f hf, mul_inv_cancel_left]
  have hfwW : f w ∈ W := hW f hf w hwW
  have hfwY : f w ∈ Y := hWY hfwW
  have e1 : Multiplicative.toAdd (f w) i j = Multiplicative.toAdd (f r) i j := by
    rw [hfw, ncc_entry_mul, hfx.2.1, add_zero]
  have e2 : Multiplicative.toAdd (f w) k l = Multiplicative.toAdd (f r) k l := by
    rw [hfw, ncc_entry_mul, hfx.1, add_zero]
  intro y hy
  have key := ncc_four (Multiplicative.toAdd w i j) (Multiplicative.toAdd w k l)
    (Multiplicative.toAdd (f w) i j) (Multiplicative.toAdd (f w) k l)
    (Multiplicative.toAdd y i j) (Multiplicative.toAdd y k l) hab (by rwa [e1, e2])
    (by rwa [e1, e2])
  rcases key with ⟨d1, d2⟩ | ⟨d1, d2⟩ | ⟨d1, d2⟩ | ⟨d1, d2⟩
  · exact hXW ⟨d2, d1, hy⟩
  · have hm : y * w⁻¹ ∈ nccCut (nccCut Y i j) k l :=
      ⟨by rw [ncc_entry_mul, ncc_entry_inv, d2, add_neg_cancel],
        by rw [ncc_entry_mul, ncc_entry_inv, d1, add_neg_cancel], Y.mul_mem hy (Y.inv_mem hwY)⟩
    simpa using W.mul_mem (hXW hm) hwW
  · have hm : y * (f w)⁻¹ ∈ nccCut (nccCut Y i j) k l :=
      ⟨by rw [ncc_entry_mul, ncc_entry_inv, d2, add_neg_cancel],
        by rw [ncc_entry_mul, ncc_entry_inv, d1, add_neg_cancel], Y.mul_mem hy (Y.inv_mem hfwY)⟩
    simpa using W.mul_mem (hXW hm) hfwW
  · have hm : y * w⁻¹ * (f w)⁻¹ ∈ nccCut (nccCut Y i j) k l :=
      ⟨by simp only [ncc_entry_mul, ncc_entry_inv, d2]; ring,
        by simp only [ncc_entry_mul, ncc_entry_inv, d1]; ring,
        Y.mul_mem (Y.mul_mem hy (Y.inv_mem hwY)) (Y.inv_mem hfwY)⟩
    simpa [mul_assoc] using W.mul_mem (hXW hm) (W.mul_mem hfwW hwW)

private theorem ncc_cf_one (acts : Set (AdjAmb → AdjAmb)) (Y : Subgroup AdjAmb) (i j : Fin 3)
    (hY : IsActsInv acts Y) (hX : IsActsInv acts (nccCut Y i j)) (y : AdjAmb) (hy : y ∈ Y)
    (hyij : Multiplicative.toAdd y i j ≠ 0) : IsChiefFactorUnder acts (nccCut Y i j) Y :=
  ⟨SetLike.lt_iff_le_and_exists.2 ⟨fun _ hx => hx.2, y, hy, fun h => hyij h.1⟩, hX, hY,
    ncc_chief_one acts Y i j⟩

private theorem ncc_cf_two (acts : Set (AdjAmb → AdjAmb)) (Y : Subgroup AdjAmb) (i j k l : Fin 3)
    (hhom : ∀ f ∈ acts, ∀ a b, f (a * b) = f a * f b)
    (hY : IsActsInv acts Y) (hX : IsActsInv acts (nccCut (nccCut Y i j) k l))
    (hwit : ∀ a b : ZMod 2, ¬ (a = 0 ∧ b = 0) → ∃ r ∈ Y, Multiplicative.toAdd r i j = a ∧
      Multiplicative.toAdd r k l = b ∧ ∃ f ∈ acts,
        ¬ (Multiplicative.toAdd (f r) i j = 0 ∧ Multiplicative.toAdd (f r) k l = 0) ∧
        ¬ (Multiplicative.toAdd (f r) i j = a ∧ Multiplicative.toAdd (f r) k l = b)) :
    IsChiefFactorUnder acts (nccCut (nccCut Y i j) k l) Y := by
  refine ⟨SetLike.lt_iff_le_and_exists.2 ⟨fun _ hx => hx.2.2, ?_⟩, hX, hY,
    ncc_chief_two acts Y i j k l hhom hX hwit⟩
  obtain ⟨r, hr, hra, -, -⟩ := hwit 1 0 (by decide)
  exact ⟨r, hr, fun h => absurd (h.2.1.symm.trans hra) (by decide)⟩

private theorem ncc_central {G : Subgroup (GL (Fin 3) (ZMod 2))} {Y : Subgroup AdjAmb} {i j : Fin 3}
    (hY : ∀ g ∈ G, ∀ y ∈ Y, adjAmbAct g y ∈ Y)
    (hX : ∀ g ∈ G, ∀ y ∈ nccCut Y i j, adjAmbAct g y ∈ nccCut Y i j) :
    ∀ f ∈ nccActs G, ∀ u ∈ Y, f u * u⁻¹ ∈ nccCut Y i j := by
  rintro f ⟨g, hg, rfl⟩ u hu
  show adjAmbAct g u * u⁻¹ ∈ nccCut Y i j
  have hfu : adjAmbAct g u ∈ Y := hY g hg u hu
  refine ⟨?_, Y.mul_mem hfu (Y.inv_mem hu)⟩
  rcases ncc_z2 (Multiplicative.toAdd u i j) with h0 | h1
  · have := (hX g hg u ⟨h0, hu⟩).1
    rw [ncc_entry_mul, ncc_entry_inv, this, h0, neg_zero, add_zero]
  · rcases ncc_z2 (Multiplicative.toAdd (adjAmbAct g u) i j) with k0 | k1
    · exfalso
      have := (hX g⁻¹ (G.inv_mem hg) _ ⟨k0, hfu⟩).1
      rw [ncc_act_inv_act] at this
      rw [this] at h1
      exact absurd h1 (by decide)
    · rw [ncc_entry_mul, ncc_entry_inv, k1, h1]
      decide

private def nccSeq (S1 S2 S3 S4 : Subgroup AdjAmb) : ℕ → Subgroup AdjAmb
  | 0 => ⊥
  | 1 => S1
  | 2 => S2
  | 3 => S3
  | 4 => S4
  | _ => Adj3

private theorem ncc_chain (acts : Set (AdjAmb → AdjAmb)) (S1 S2 S3 S4 : Subgroup AdjAmb)
    (h0 : IsChiefFactorUnder acts ⊥ S1) (h1 : IsChiefFactorUnder acts S1 S2)
    (h2 : IsChiefFactorUnder acts S2 S3) (h3 : IsChiefFactorUnder acts S3 S4)
    (h4 : IsChiefFactorUnder acts S4 Adj3)
    (n0 : ∃ f ∈ acts, ∃ u ∈ S1, f u * u⁻¹ ∉ (⊥ : Subgroup AdjAmb))
    (c1 : ∀ f ∈ acts, ∀ u ∈ S2, f u * u⁻¹ ∈ S1)
    (n2 : ∃ f ∈ acts, ∃ u ∈ S3, f u * u⁻¹ ∉ S2)
    (c3 : ∀ f ∈ acts, ∀ u ∈ S4, f u * u⁻¹ ∈ S3)
    (n4 : ∃ f ∈ acts, ∃ u ∈ Adj3, f u * u⁻¹ ∉ S4) :
    NoncentralChiefCount acts Adj3 3 := by
  refine ⟨5, nccSeq S1 S2 S3 S4, rfl, rfl, ?_, ?_⟩
  · intro i hi
    interval_cases i
    · exact h0
    · exact h1
    · exact h2
    · exact h3
    · exact h4
  · rw [Set.ncard_eq_three]
    refine ⟨0, 2, 4, by norm_num, by norm_num, by norm_num, ?_⟩
    ext i
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨hi, f, hf, u, hu, hfu⟩
      interval_cases i
      · exact Or.inl rfl
      · exact absurd (c1 f hf u hu) hfu
      · exact Or.inr (Or.inl rfl)
      · exact absurd (c3 f hf u hu) hfu
      · exact Or.inr (Or.inr rfl)
    · rintro (rfl | rfl | rfl)
      · exact ⟨by norm_num, n0⟩
      · exact ⟨by norm_num, n2⟩
      · exact ⟨by norm_num, n4⟩

private def nccP23 : GL (Fin 3) (ZMod 2) :=
  ⟨!![1, 0, 0; 0, 0, 1; 0, 1, 0], !![1, 0, 0; 0, 0, 1; 0, 1, 0], by decide, by decide⟩

private def nccT12 : GL (Fin 3) (ZMod 2) :=
  ⟨!![1, 0, 0; 0, 1, 1; 0, 0, 1], !![1, 0, 0; 0, 1, 1; 0, 0, 1], by decide, by decide⟩

private theorem ncc_Lp_facts {g : GL (Fin 3) (ZMod 2)} (hg : g ∈ Lpt ![1, 0, 0]) :
    (g : Matrix (Fin 3) (Fin 3) (ZMod 2)) 0 0 = 1 ∧ (g : Matrix (Fin 3) (Fin 3) (ZMod 2)) 1 0 = 0 ∧
      (g : Matrix (Fin 3) (Fin 3) (ZMod 2)) 2 0 = 0 := by
  have h : (g : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec ![1, 0, 0] = ![1, 0, 0] :=
    hg ![1, 0, 0] (Set.mem_singleton _)
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  have h2 := congrFun h 2
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three] at h0 h1 h2
  exact ⟨h0, h1, h2⟩

private theorem ncc_mem_Lp_of {g : GL (Fin 3) (ZMod 2)} (h0 : (g : Matrix (Fin 3) (Fin 3) (ZMod 2)) 0 0 = 1)
    (h1 : (g : Matrix (Fin 3) (Fin 3) (ZMod 2)) 1 0 = 0)
    (h2 : (g : Matrix (Fin 3) (Fin 3) (ZMod 2)) 2 0 = 0) : g ∈ Lpt ![1, 0, 0] := by
  intro v hv
  rw [Set.mem_singleton_iff] at hv
  subst hv
  ext i
  fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, h0, h1, h2]

private theorem ncc_P23_mem : nccP23 ∈ Lpt ![1, 0, 0] := ncc_mem_Lp_of (by decide) (by decide) (by decide)

private theorem ncc_T12_mem : nccT12 ∈ Lpt ![1, 0, 0] := ncc_mem_Lp_of (by decide) (by decide) (by decide)

private abbrev nccLpD : Subgroup AdjAmb := nccCut (nccCut Adj3 1 0) 2 0
private abbrev nccLpC : Subgroup AdjAmb := nccCut nccLpD 0 0
private abbrev nccLpB : Subgroup AdjAmb := nccCut (nccCut nccLpC 1 2) 2 1
private abbrev nccLpA : Subgroup AdjAmb := nccCut nccLpB 1 1

private theorem ncc_Lp_bot : nccCut (nccCut nccLpA 0 1) 0 2 = ⊥ := by
  refine (Subgroup.eq_bot_iff_forall _).2 fun x hx => ?_
  obtain ⟨x02, x01, x11, x21, x12, x00, x20, x10, htr⟩ := hx
  have x22 : Multiplicative.toAdd x 2 2 = 0 := by
    rw [ncc_mem_Adj3, x00, x11, zero_add, zero_add] at htr; exact htr
  apply Multiplicative.toAdd.injective
  ext i j
  rw [toAdd_one, Matrix.zero_apply]
  fin_cases i <;> fin_cases j <;> assumption

private theorem ncc_Lp_inv {g : GL (Fin 3) (ZMod 2)} (hg : g ∈ Lpt ![1, 0, 0]) :
    (∀ x ∈ nccLpD, adjAmbAct g x ∈ nccLpD) ∧ (∀ x ∈ nccLpC, adjAmbAct g x ∈ nccLpC) ∧
    (∀ x ∈ nccLpB, adjAmbAct g x ∈ nccLpB) ∧ (∀ x ∈ nccLpA, adjAmbAct g x ∈ nccLpA) := by
  obtain ⟨-, a10, a20⟩ := ncc_Lp_facts hg
  obtain ⟨-, b10, b20⟩ := ncc_Lp_facts ((Lpt ![1, 0, 0]).inv_mem hg)
  have h12 := ncc_AB g 1 2
  have h21 := ncc_AB g 2 1
  rw [Matrix.one_apply_ne (show (1 : Fin 3) ≠ 2 by decide), a10, zero_mul, zero_add] at h12
  rw [Matrix.one_apply_ne (show (2 : Fin 3) ≠ 1 by decide), a20, zero_mul, zero_add] at h21
  have hD : ∀ x ∈ nccLpD, adjAmbAct g x ∈ nccLpD := by
    rintro x ⟨x20, x10, hx⟩
    refine ⟨?_, ?_, ncc_Adj3_inv g x hx⟩
    · rw [ncc_toAdd_act, ncc_mul3]; simp [a20, b10, b20, x10, x20]
    · rw [ncc_toAdd_act, ncc_mul3]; simp [a10, b10, b20, x10, x20]
  have hC : ∀ x ∈ nccLpC, adjAmbAct g x ∈ nccLpC := by
    rintro x ⟨x00, hxD⟩
    refine ⟨?_, hD x hxD⟩
    obtain ⟨x20, x10, -⟩ := hxD
    rw [ncc_toAdd_act, ncc_mul3]; simp [b10, b20, x00, x10, x20]
  have hB : ∀ x ∈ nccLpB, adjAmbAct g x ∈ nccLpB := by
    rintro x ⟨x21, x12, hxC⟩
    have hC' := hC x hxC
    obtain ⟨x00, x20, x10, htr⟩ := hxC
    have x22 : Multiplicative.toAdd x 2 2 = Multiplicative.toAdd x 1 1 := by
      rw [ncc_mem_Adj3, x00, zero_add] at htr; exact ncc_z2_eq htr
    refine ⟨?_, ?_, hC'⟩
    · rw [ncc_toAdd_act, ncc_mul3]
      simp only [a20, x00, x10, x20, x12, x21, x22, zero_mul, mul_zero, zero_add, add_zero]
      linear_combination (Multiplicative.toAdd x 1 1) * h21
    · rw [ncc_toAdd_act, ncc_mul3]
      simp only [a10, x00, x10, x20, x12, x21, x22, zero_mul, mul_zero, zero_add, add_zero]
      linear_combination (Multiplicative.toAdd x 1 1) * h12
  have hA : ∀ x ∈ nccLpA, adjAmbAct g x ∈ nccLpA := by
    rintro x ⟨x11, hxB⟩
    refine ⟨?_, hB x hxB⟩
    obtain ⟨x21, x12, x00, x20, x10, htr⟩ := hxB
    have x22 : Multiplicative.toAdd x 2 2 = 0 := by
      rw [ncc_mem_Adj3, x00, x11, zero_add, zero_add] at htr; exact htr
    rw [ncc_toAdd_act, ncc_mul3]
    simp [a10, x00, x10, x20, x11, x12, x21, x22]
  exact ⟨hD, hC, hB, hA⟩

private theorem ncc_Lp_w0 : ∀ a b : ZMod 2, ¬ (a = 0 ∧ b = 0) → ∃ r ∈ nccLpA,
    Multiplicative.toAdd r 0 1 = a ∧ Multiplicative.toAdd r 0 2 = b ∧
      ∃ f ∈ nccActs (Lpt ![1, 0, 0]),
        ¬ (Multiplicative.toAdd (f r) 0 1 = 0 ∧ Multiplicative.toAdd (f r) 0 2 = 0) ∧
        ¬ (Multiplicative.toAdd (f r) 0 1 = a ∧ Multiplicative.toAdd (f r) 0 2 = b) := by
  intro a b hab
  rcases ncc_z2 a with rfl | rfl <;> rcases ncc_z2 b with rfl | rfl
  · exact (hab ⟨rfl, rfl⟩).elim
  · exact ⟨Multiplicative.ofAdd !![0, 0, 1; 0, 0, 0; 0, 0, 0], by decide, by decide, by decide,
      fun x => adjAmbAct nccP23 x, ⟨nccP23, ncc_P23_mem, rfl⟩, by decide, by decide⟩
  · exact ⟨Multiplicative.ofAdd !![0, 1, 0; 0, 0, 0; 0, 0, 0], by decide, by decide, by decide,
      fun x => adjAmbAct nccP23 x, ⟨nccP23, ncc_P23_mem, rfl⟩, by decide, by decide⟩
  · exact ⟨Multiplicative.ofAdd !![0, 1, 1; 0, 0, 0; 0, 0, 0], by decide, by decide, by decide,
      fun x => adjAmbAct nccT12 x, ⟨nccT12, ncc_T12_mem, rfl⟩, by decide, by decide⟩

private theorem ncc_Lp_w2 : ∀ a b : ZMod 2, ¬ (a = 0 ∧ b = 0) → ∃ r ∈ nccLpC,
    Multiplicative.toAdd r 1 2 = a ∧ Multiplicative.toAdd r 2 1 = b ∧
      ∃ f ∈ nccActs (Lpt ![1, 0, 0]),
        ¬ (Multiplicative.toAdd (f r) 1 2 = 0 ∧ Multiplicative.toAdd (f r) 2 1 = 0) ∧
        ¬ (Multiplicative.toAdd (f r) 1 2 = a ∧ Multiplicative.toAdd (f r) 2 1 = b) := by
  intro a b hab
  rcases ncc_z2 a with rfl | rfl <;> rcases ncc_z2 b with rfl | rfl
  · exact (hab ⟨rfl, rfl⟩).elim
  · exact ⟨Multiplicative.ofAdd !![0, 0, 0; 0, 0, 0; 0, 1, 0], by decide, by decide, by decide,
      fun x => adjAmbAct nccP23 x, ⟨nccP23, ncc_P23_mem, rfl⟩, by decide, by decide⟩
  · exact ⟨Multiplicative.ofAdd !![0, 0, 0; 0, 0, 1; 0, 0, 0], by decide, by decide, by decide,
      fun x => adjAmbAct nccP23 x, ⟨nccP23, ncc_P23_mem, rfl⟩, by decide, by decide⟩
  · exact ⟨Multiplicative.ofAdd !![0, 0, 0; 0, 0, 1; 0, 1, 0], by decide, by decide, by decide,
      fun x => adjAmbAct nccT12 x, ⟨nccT12, ncc_T12_mem, rfl⟩, by decide, by decide⟩

private theorem ncc_Lp_w4 : ∀ a b : ZMod 2, ¬ (a = 0 ∧ b = 0) → ∃ r ∈ Adj3,
    Multiplicative.toAdd r 1 0 = a ∧ Multiplicative.toAdd r 2 0 = b ∧
      ∃ f ∈ nccActs (Lpt ![1, 0, 0]),
        ¬ (Multiplicative.toAdd (f r) 1 0 = 0 ∧ Multiplicative.toAdd (f r) 2 0 = 0) ∧
        ¬ (Multiplicative.toAdd (f r) 1 0 = a ∧ Multiplicative.toAdd (f r) 2 0 = b) := by
  intro a b hab
  rcases ncc_z2 a with rfl | rfl <;> rcases ncc_z2 b with rfl | rfl
  · exact (hab ⟨rfl, rfl⟩).elim
  · exact ⟨Multiplicative.ofAdd !![0, 0, 0; 0, 0, 0; 1, 0, 0], by decide, by decide, by decide,
      fun x => adjAmbAct nccP23 x, ⟨nccP23, ncc_P23_mem, rfl⟩, by decide, by decide⟩
  · exact ⟨Multiplicative.ofAdd !![0, 0, 0; 1, 0, 0; 0, 0, 0], by decide, by decide, by decide,
      fun x => adjAmbAct nccP23 x, ⟨nccP23, ncc_P23_mem, rfl⟩, by decide, by decide⟩
  · exact ⟨Multiplicative.ofAdd !![0, 0, 0; 1, 0, 0; 1, 0, 0], by decide, by decide, by decide,
      fun x => adjAmbAct nccT12 x, ⟨nccT12, ncc_T12_mem, rfl⟩, by decide, by decide⟩

private theorem ncc_std_Lp : NoncentralChiefCount
    {f : AdjAmb → AdjAmb | ∃ g ∈ Lpt ![1, 0, 0], f = fun x => adjAmbAct g x} Adj3 3 := by
  show NoncentralChiefCount (nccActs (Lpt ![1, 0, 0])) Adj3 3
  have iAdj : IsActsInv (nccActs (Lpt ![1, 0, 0])) Adj3 :=
    ncc_inv_of fun g _ x hx => ncc_Adj3_inv g x hx
  have iD : IsActsInv (nccActs (Lpt ![1, 0, 0])) nccLpD :=
    ncc_inv_of fun _ hg => (ncc_Lp_inv hg).1
  have iC : IsActsInv (nccActs (Lpt ![1, 0, 0])) nccLpC :=
    ncc_inv_of fun _ hg => (ncc_Lp_inv hg).2.1
  have iB : IsActsInv (nccActs (Lpt ![1, 0, 0])) nccLpB :=
    ncc_inv_of fun _ hg => (ncc_Lp_inv hg).2.2.1
  have iA : IsActsInv (nccActs (Lpt ![1, 0, 0])) nccLpA :=
    ncc_inv_of fun _ hg => (ncc_Lp_inv hg).2.2.2
  have iBot : IsActsInv (nccActs (Lpt ![1, 0, 0])) (nccCut (nccCut nccLpA 0 1) 0 2) := by
    rw [ncc_Lp_bot]
    rintro f ⟨g, -, rfl⟩ u hu
    rw [Subgroup.mem_bot] at hu ⊢
    subst hu
    exact map_one _
  refine ncc_chain (nccActs (Lpt ![1, 0, 0])) nccLpA nccLpB nccLpC nccLpD ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    ?_ ?_
  · rw [← ncc_Lp_bot]
    exact ncc_cf_two _ nccLpA 0 1 0 2 ncc_hom iA iBot ncc_Lp_w0
  · exact ncc_cf_one _ nccLpB 1 1 iB iA (Multiplicative.ofAdd !![0, 0, 0; 0, 1, 0; 0, 0, 1])
      (by decide) (by decide)
  · exact ncc_cf_two _ nccLpC 1 2 2 1 ncc_hom iC iB ncc_Lp_w2
  · exact ncc_cf_one _ nccLpD 0 0 iD iC (Multiplicative.ofAdd !![1, 0, 0; 0, 1, 0; 0, 0, 0])
      (by decide) (by decide)
  · exact ncc_cf_two _ Adj3 1 0 2 0 ncc_hom iAdj iD ncc_Lp_w4
  · exact ⟨fun x => adjAmbAct nccP23 x, ⟨nccP23, ncc_P23_mem, rfl⟩,
      Multiplicative.ofAdd !![0, 1, 0; 0, 0, 0; 0, 0, 0], by decide,
      by rw [Subgroup.mem_bot]; decide⟩
  · exact ncc_central (fun _ hg => (ncc_Lp_inv hg).2.2.1) (fun _ hg => (ncc_Lp_inv hg).2.2.2)
  · exact ⟨fun x => adjAmbAct nccP23 x, ⟨nccP23, ncc_P23_mem, rfl⟩,
      Multiplicative.ofAdd !![0, 0, 0; 0, 0, 1; 0, 0, 0], by decide, by decide⟩
  · exact ncc_central (fun _ hg => (ncc_Lp_inv hg).1) (fun _ hg => (ncc_Lp_inv hg).2.1)
  · exact ⟨fun x => adjAmbAct nccP23 x, ⟨nccP23, ncc_P23_mem, rfl⟩,
      Multiplicative.ofAdd !![0, 0, 0; 1, 0, 0; 0, 0, 0], by decide, by decide⟩

private abbrev nccLlG : Subgroup (GL (Fin 3) (ZMod 2)) :=
  Lln (LinearMap.ker (LinearMap.proj (R := ZMod 2) (φ := fun _ : Fin 3 => ZMod 2) (2 : Fin 3)))

private def nccP12 : GL (Fin 3) (ZMod 2) :=
  ⟨!![0, 1, 0; 1, 0, 0; 0, 0, 1], !![0, 1, 0; 1, 0, 0; 0, 0, 1], by decide, by decide⟩

private def nccT01 : GL (Fin 3) (ZMod 2) :=
  ⟨!![1, 1, 0; 0, 1, 0; 0, 0, 1], !![1, 1, 0; 0, 1, 0; 0, 0, 1], by decide, by decide⟩

private theorem ncc_Ll_facts {g : GL (Fin 3) (ZMod 2)} (hg : g ∈ nccLlG) :
    (g : Matrix (Fin 3) (Fin 3) (ZMod 2)) 2 0 = 0 ∧
      (g : Matrix (Fin 3) (Fin 3) (ZMod 2)) 2 1 = 0 := by
  have h1 := (hg ![1, 0, 0] (by simp)).1
  have h2 := (hg ![0, 1, 0] (by simp)).1
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three] at h1 h2
  exact ⟨h1, h2⟩

private theorem ncc_mem_Ll_of {g : GL (Fin 3) (ZMod 2)}
    (h1 : (g : Matrix (Fin 3) (Fin 3) (ZMod 2)) 2 0 = 0)
    (h2 : (g : Matrix (Fin 3) (Fin 3) (ZMod 2)) 2 1 = 0)
    (h3 : ((g⁻¹ : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)) 2 0 = 0)
    (h4 : ((g⁻¹ : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)) 2 1 = 0) :
    g ∈ nccLlG := by
  intro v hv
  simp only [SetLike.mem_coe, LinearMap.mem_ker, LinearMap.proj_apply] at hv ⊢
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_three, h1, h2, h3, h4, hv, zero_mul,
    mul_zero, add_zero, and_self]

private theorem ncc_P12_mem : nccP12 ∈ nccLlG :=
  ncc_mem_Ll_of (by decide) (by decide) (by decide) (by decide)

private theorem ncc_T01_mem : nccT01 ∈ nccLlG :=
  ncc_mem_Ll_of (by decide) (by decide) (by decide) (by decide)

private abbrev nccLl4 : Subgroup AdjAmb := nccCut (nccCut Adj3 2 0) 2 1
private abbrev nccLl3 : Subgroup AdjAmb := nccCut nccLl4 2 2
private abbrev nccLl2 : Subgroup AdjAmb := nccCut (nccCut nccLl3 0 1) 1 0
private abbrev nccLl1 : Subgroup AdjAmb := nccCut nccLl2 0 0

private theorem ncc_Ll_bot : nccCut (nccCut nccLl1 0 2) 1 2 = ⊥ := by
  refine (Subgroup.eq_bot_iff_forall _).2 fun x hx => ?_
  obtain ⟨x12, x02, x00, x10, x01, x22, x21, x20, htr⟩ := hx
  have x11 : Multiplicative.toAdd x 1 1 = 0 := by
    rw [ncc_mem_Adj3, x00, x22, zero_add, add_zero] at htr; exact htr
  apply Multiplicative.toAdd.injective
  ext i j
  rw [toAdd_one, Matrix.zero_apply]
  fin_cases i <;> fin_cases j <;> assumption

private theorem ncc_Ll_inv {g : GL (Fin 3) (ZMod 2)} (hg : g ∈ nccLlG) :
    (∀ x ∈ nccLl4, adjAmbAct g x ∈ nccLl4) ∧ (∀ x ∈ nccLl3, adjAmbAct g x ∈ nccLl3) ∧
    (∀ x ∈ nccLl2, adjAmbAct g x ∈ nccLl2) ∧ (∀ x ∈ nccLl1, adjAmbAct g x ∈ nccLl1) := by
  obtain ⟨a20, a21⟩ := ncc_Ll_facts hg
  obtain ⟨b20, b21⟩ := ncc_Ll_facts (nccLlG.inv_mem hg)
  have h01 := ncc_AB g 0 1
  have h10 := ncc_AB g 1 0
  rw [Matrix.one_apply_ne (show (0 : Fin 3) ≠ 1 by decide), b21, mul_zero, add_zero] at h01
  rw [Matrix.one_apply_ne (show (1 : Fin 3) ≠ 0 by decide), b20, mul_zero, add_zero] at h10
  have h4 : ∀ x ∈ nccLl4, adjAmbAct g x ∈ nccLl4 := by
    rintro x ⟨x21, x20, hx⟩
    refine ⟨?_, ?_, ncc_Adj3_inv g x hx⟩
    · rw [ncc_toAdd_act, ncc_mul3]; simp [a20, a21, b21, x20, x21]
    · rw [ncc_toAdd_act, ncc_mul3]; simp [a20, a21, b20, x20, x21]
  have h3 : ∀ x ∈ nccLl3, adjAmbAct g x ∈ nccLl3 := by
    rintro x ⟨x22, hx4⟩
    refine ⟨?_, h4 x hx4⟩
    obtain ⟨x21, x20, -⟩ := hx4
    rw [ncc_toAdd_act, ncc_mul3]; simp [a20, a21, x20, x21, x22]
  have h2 : ∀ x ∈ nccLl2, adjAmbAct g x ∈ nccLl2 := by
    rintro x ⟨x10, x01, hx3⟩
    have h3' := h3 x hx3
    obtain ⟨x22, x21, x20, htr⟩ := hx3
    have x11 : Multiplicative.toAdd x 1 1 = Multiplicative.toAdd x 0 0 := by
      rw [ncc_mem_Adj3, x22, add_zero] at htr; exact ncc_z2_eq htr
    refine ⟨?_, ?_, h3'⟩
    · rw [ncc_toAdd_act, ncc_mul3]
      simp only [b20, x10, x20, x01, x21, x22, x11, zero_mul, mul_zero, zero_add, add_zero]
      linear_combination (Multiplicative.toAdd x 0 0) * h10
    · rw [ncc_toAdd_act, ncc_mul3]
      simp only [b21, x10, x20, x01, x21, x22, x11, zero_mul, mul_zero, zero_add, add_zero]
      linear_combination (Multiplicative.toAdd x 0 0) * h01
  have h1 : ∀ x ∈ nccLl1, adjAmbAct g x ∈ nccLl1 := by
    rintro x ⟨x00, hx2⟩
    refine ⟨?_, h2 x hx2⟩
    obtain ⟨x10, x01, x22, x21, x20, htr⟩ := hx2
    have x11 : Multiplicative.toAdd x 1 1 = 0 := by
      rw [ncc_mem_Adj3, x00, x22, zero_add, add_zero] at htr; exact htr
    rw [ncc_toAdd_act, ncc_mul3]
    simp [b20, x00, x10, x20, x01, x11, x21]
  exact ⟨h4, h3, h2, h1⟩

private theorem ncc_Ll_w0 : ∀ a b : ZMod 2, ¬ (a = 0 ∧ b = 0) → ∃ r ∈ nccLl1,
    Multiplicative.toAdd r 0 2 = a ∧ Multiplicative.toAdd r 1 2 = b ∧
      ∃ f ∈ nccActs nccLlG,
        ¬ (Multiplicative.toAdd (f r) 0 2 = 0 ∧ Multiplicative.toAdd (f r) 1 2 = 0) ∧
        ¬ (Multiplicative.toAdd (f r) 0 2 = a ∧ Multiplicative.toAdd (f r) 1 2 = b) := by
  intro a b hab
  rcases ncc_z2 a with rfl | rfl <;> rcases ncc_z2 b with rfl | rfl
  · exact (hab ⟨rfl, rfl⟩).elim
  · exact ⟨Multiplicative.ofAdd !![0, 0, 0; 0, 0, 1; 0, 0, 0], by decide, by decide, by decide,
      fun x => adjAmbAct nccP12 x, ⟨nccP12, ncc_P12_mem, rfl⟩, by decide, by decide⟩
  · exact ⟨Multiplicative.ofAdd !![0, 0, 1; 0, 0, 0; 0, 0, 0], by decide, by decide, by decide,
      fun x => adjAmbAct nccP12 x, ⟨nccP12, ncc_P12_mem, rfl⟩, by decide, by decide⟩
  · exact ⟨Multiplicative.ofAdd !![0, 0, 1; 0, 0, 1; 0, 0, 0], by decide, by decide, by decide,
      fun x => adjAmbAct nccT01 x, ⟨nccT01, ncc_T01_mem, rfl⟩, by decide, by decide⟩

private theorem ncc_Ll_w2 : ∀ a b : ZMod 2, ¬ (a = 0 ∧ b = 0) → ∃ r ∈ nccLl3,
    Multiplicative.toAdd r 0 1 = a ∧ Multiplicative.toAdd r 1 0 = b ∧
      ∃ f ∈ nccActs nccLlG,
        ¬ (Multiplicative.toAdd (f r) 0 1 = 0 ∧ Multiplicative.toAdd (f r) 1 0 = 0) ∧
        ¬ (Multiplicative.toAdd (f r) 0 1 = a ∧ Multiplicative.toAdd (f r) 1 0 = b) := by
  intro a b hab
  rcases ncc_z2 a with rfl | rfl <;> rcases ncc_z2 b with rfl | rfl
  · exact (hab ⟨rfl, rfl⟩).elim
  · exact ⟨Multiplicative.ofAdd !![0, 0, 0; 1, 0, 0; 0, 0, 0], by decide, by decide, by decide,
      fun x => adjAmbAct nccP12 x, ⟨nccP12, ncc_P12_mem, rfl⟩, by decide, by decide⟩
  · exact ⟨Multiplicative.ofAdd !![0, 1, 0; 0, 0, 0; 0, 0, 0], by decide, by decide, by decide,
      fun x => adjAmbAct nccP12 x, ⟨nccP12, ncc_P12_mem, rfl⟩, by decide, by decide⟩
  · exact ⟨Multiplicative.ofAdd !![0, 1, 0; 1, 0, 0; 0, 0, 0], by decide, by decide, by decide,
      fun x => adjAmbAct nccT01 x, ⟨nccT01, ncc_T01_mem, rfl⟩, by decide, by decide⟩

private theorem ncc_Ll_w4 : ∀ a b : ZMod 2, ¬ (a = 0 ∧ b = 0) → ∃ r ∈ Adj3,
    Multiplicative.toAdd r 2 0 = a ∧ Multiplicative.toAdd r 2 1 = b ∧
      ∃ f ∈ nccActs nccLlG,
        ¬ (Multiplicative.toAdd (f r) 2 0 = 0 ∧ Multiplicative.toAdd (f r) 2 1 = 0) ∧
        ¬ (Multiplicative.toAdd (f r) 2 0 = a ∧ Multiplicative.toAdd (f r) 2 1 = b) := by
  intro a b hab
  rcases ncc_z2 a with rfl | rfl <;> rcases ncc_z2 b with rfl | rfl
  · exact (hab ⟨rfl, rfl⟩).elim
  · exact ⟨Multiplicative.ofAdd !![0, 0, 0; 0, 0, 0; 0, 1, 0], by decide, by decide, by decide,
      fun x => adjAmbAct nccP12 x, ⟨nccP12, ncc_P12_mem, rfl⟩, by decide, by decide⟩
  · exact ⟨Multiplicative.ofAdd !![0, 0, 0; 0, 0, 0; 1, 0, 0], by decide, by decide, by decide,
      fun x => adjAmbAct nccP12 x, ⟨nccP12, ncc_P12_mem, rfl⟩, by decide, by decide⟩
  · exact ⟨Multiplicative.ofAdd !![0, 0, 0; 0, 0, 0; 1, 1, 0], by decide, by decide, by decide,
      fun x => adjAmbAct nccT01 x, ⟨nccT01, ncc_T01_mem, rfl⟩, by decide, by decide⟩

private theorem ncc_std_Ll : NoncentralChiefCount
    {f : AdjAmb → AdjAmb | ∃ g ∈ Lln (LinearMap.ker (LinearMap.proj (R := ZMod 2)
      (φ := fun _ : Fin 3 => ZMod 2) (2 : Fin 3))), f = fun x => adjAmbAct g x} Adj3 3 := by
  show NoncentralChiefCount (nccActs nccLlG) Adj3 3
  have iAdj : IsActsInv (nccActs nccLlG) Adj3 :=
    ncc_inv_of fun g _ x hx => ncc_Adj3_inv g x hx
  have i4 : IsActsInv (nccActs nccLlG) nccLl4 := ncc_inv_of fun _ hg => (ncc_Ll_inv hg).1
  have i3 : IsActsInv (nccActs nccLlG) nccLl3 := ncc_inv_of fun _ hg => (ncc_Ll_inv hg).2.1
  have i2 : IsActsInv (nccActs nccLlG) nccLl2 := ncc_inv_of fun _ hg => (ncc_Ll_inv hg).2.2.1
  have i1 : IsActsInv (nccActs nccLlG) nccLl1 := ncc_inv_of fun _ hg => (ncc_Ll_inv hg).2.2.2
  have iBot : IsActsInv (nccActs nccLlG) (nccCut (nccCut nccLl1 0 2) 1 2) := by
    rw [ncc_Ll_bot]
    rintro f ⟨g, -, rfl⟩ u hu
    rw [Subgroup.mem_bot] at hu ⊢
    subst hu
    exact map_one _
  refine ncc_chain (nccActs nccLlG) nccLl1 nccLl2 nccLl3 nccLl4 ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · rw [← ncc_Ll_bot]
    exact ncc_cf_two _ nccLl1 0 2 1 2 ncc_hom i1 iBot ncc_Ll_w0
  · exact ncc_cf_one _ nccLl2 0 0 i2 i1 (Multiplicative.ofAdd !![1, 0, 0; 0, 1, 0; 0, 0, 0])
      (by decide) (by decide)
  · exact ncc_cf_two _ nccLl3 0 1 1 0 ncc_hom i3 i2 ncc_Ll_w2
  · exact ncc_cf_one _ nccLl4 2 2 i4 i3 (Multiplicative.ofAdd !![0, 0, 0; 0, 1, 0; 0, 0, 1])
      (by decide) (by decide)
  · exact ncc_cf_two _ Adj3 2 0 2 1 ncc_hom iAdj i4 ncc_Ll_w4
  · exact ⟨fun x => adjAmbAct nccP12 x, ⟨nccP12, ncc_P12_mem, rfl⟩,
      Multiplicative.ofAdd !![0, 0, 1; 0, 0, 0; 0, 0, 0], by decide,
      by rw [Subgroup.mem_bot]; decide⟩
  · exact ncc_central (fun _ hg => (ncc_Ll_inv hg).2.2.1) (fun _ hg => (ncc_Ll_inv hg).2.2.2)
  · exact ⟨fun x => adjAmbAct nccP12 x, ⟨nccP12, ncc_P12_mem, rfl⟩,
      Multiplicative.ofAdd !![0, 1, 0; 0, 0, 0; 0, 0, 0], by decide, by decide⟩
  · exact ncc_central (fun _ hg => (ncc_Ll_inv hg).1) (fun _ hg => (ncc_Ll_inv hg).2.1)
  · exact ⟨fun x => adjAmbAct nccP12 x, ⟨nccP12, ncc_P12_mem, rfl⟩,
      Multiplicative.ofAdd !![0, 0, 0; 0, 0, 0; 1, 0, 0], by decide, by decide⟩

end CFSG.ASVolI.ChH

namespace CFSG.ASVolI

open CFSG.Quasithin CFSG.ASVolI.ChH

private theorem mem_Lpt_conj_iff6 (c : GL (Fin 3) (ZMod 2)) (p : V3)
    (hpc : (c : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec e1 = p) (k : GL (Fin 3) (ZMod 2)) :
    k ∈ Lpt e1 ↔ c * k * c⁻¹ ∈ Lpt p := by
  refine ⟨mem_Lpt_conj6 c p hpc k, fun h => ?_⟩
  rw [mem_Lpt] at h ⊢
  intro v hv
  rw [Set.mem_singleton_iff.1 hv]
  have h1 := h p (Set.mem_singleton p)
  rw [← hpc, mulVec_conj6, inv_mulVec_mulVec] at h1
  have h2 := congrArg ((c⁻¹ : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec h1
  rwa [inv_mulVec_mulVec, inv_mulVec_mulVec] at h2

private theorem H63_part3 (T : Subgroup (GL (Fin 3) (ZMod 2))) (p : V3) (l : Submodule (ZMod 2) V3)
    (hyp : CFSG.ASVolI.ChH.HypH5 T p l) :
    NoncentralChiefCount {f | ∃ g ∈ Lpt p, f = fun x => adjAmbAct g x} Adj3 3 ∧
      NoncentralChiefCount {f | ∃ g ∈ Lln l, f = fun x => adjAmbAct g x} Adj3 3 := by
  obtain ⟨c, -, -, hpc, hline⟩ := conj_data6 T p l hyp
  exact ⟨ncc_transport c (Lpt e1) (Lpt p) (fun g => mem_Lpt_conj_iff6 c p hpc g) 3 CFSG.ASVolI.ChH.ncc_std_Lp,
    ncc_transport c (Lln line0) (Lln l) (fun g => mem_Lln_conj c l hline g) 3 CFSG.ASVolI.ChH.ncc_std_Ll⟩

theorem as_H_6_3 : H_6_3 :=
  ⟨H63_part1, ⟨H63_part2a, H63_part2b⟩, fun T p l hyp =>
    ⟨H63_part3 T p l hyp, H63_part4 T p l hyp, H63_part5 T p l hyp⟩⟩


namespace ArtH62

section Art

variable {G : Type*} [Group G] {M : Type*} [CommGroup M]

private theorem inv_sup_of {ρ : G →* MulAut M} {A B : Subgroup M}
    (hA : ∀ g, ∀ u ∈ A, ρ g u ∈ A) (hB : ∀ g, ∀ u ∈ B, ρ g u ∈ B) :
    ∀ g, ∀ u ∈ A ⊔ B, ρ g u ∈ A ⊔ B := by
  intro g u hu
  obtain ⟨y, hy, z, hz, rfl⟩ := Subgroup.mem_sup.1 hu
  rw [map_mul]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (hA g y hy))
    (Subgroup.mem_sup_right (hB g z hz))

private theorem inv_inf_of {ρ : G →* MulAut M} {A B : Subgroup M}
    (hA : ∀ g, ∀ u ∈ A, ρ g u ∈ A) (hB : ∀ g, ∀ u ∈ B, ρ g u ∈ B) :
    ∀ g, ∀ u ∈ A ⊓ B, ρ g u ∈ A ⊓ B :=
  fun g u hu => ⟨hA g u hu.1, hB g u hu.2⟩

private structure Setup (ρ : G →* MulAut M) (U₁ U₂ U₃ U₄ K₂ K₃ : Subgroup M) : Prop where
  i₁ : ∀ g, ∀ u ∈ U₁, ρ g u ∈ U₁
  i₂ : ∀ g, ∀ u ∈ U₂, ρ g u ∈ U₂
  i₃ : ∀ g, ∀ u ∈ U₃, ρ g u ∈ U₃
  i₄ : ∀ g, ∀ u ∈ U₄, ρ g u ∈ U₄
  hsum : U₁ ⊔ U₂ ⊔ U₃ ⊔ U₄ = ⊤
  h₁ : U₁ ⊓ (U₂ ⊔ U₃ ⊔ U₄) = ⊥
  h₂ : U₂ ⊓ (U₁ ⊔ U₃ ⊔ U₄) = ⊥
  h₃ : U₃ ⊓ (U₁ ⊔ U₂ ⊔ U₄) = ⊥
  h₄ : U₄ ⊓ (U₁ ⊔ U₂ ⊔ U₃) = ⊥
  hU₁ : U₁ ≠ ⊥
  hU₄ : U₄ ≠ ⊥
  s₁ : ∀ W : Subgroup M, W ≤ U₁ → (∀ g, ∀ u ∈ W, ρ g u ∈ W) → W = ⊥ ∨ W = U₁
  s₄ : ∀ W : Subgroup M, W ≤ U₄ → (∀ g, ∀ u ∈ W, ρ g u ∈ W) → W = ⊥ ∨ W = U₄
  k₂ : K₂ ≤ U₂
  k₂ne : K₂ ≠ ⊥
  k₂max : IsMaxSub ρ U₂ K₂
  soc₂ : ∀ W : Subgroup M, W ≤ U₂ → (∀ g, ∀ u ∈ W, ρ g u ∈ W) → W ≠ ⊥ → K₂ ≤ W
  k₃ : K₃ ≤ U₃
  k₃ne : K₃ ≠ ⊥
  k₃max : IsMaxSub ρ U₃ K₃
  soc₃ : ∀ W : Subgroup M, W ≤ U₃ → (∀ g, ∀ u ∈ W, ρ g u ∈ W) → W ≠ ⊥ → K₃ ≤ W

variable {ρ : G →* MulAut M} {U₁ U₂ U₃ U₄ K₂ K₃ : Subgroup M}

private theorem Setup.decomp (S : Setup ρ U₁ U₂ U₃ U₄ K₂ K₃) (x : M) :
    ∃ a ∈ U₁, ∃ b ∈ U₂, ∃ c ∈ U₃, ∃ d ∈ U₄, a * b * c * d = x := by
  have hx : x ∈ U₁ ⊔ U₂ ⊔ U₃ ⊔ U₄ := by rw [S.hsum]; exact Subgroup.mem_top x
  obtain ⟨y, hy, d, hd, rfl⟩ := Subgroup.mem_sup.1 hx
  obtain ⟨z, hz, c, hc, rfl⟩ := Subgroup.mem_sup.1 hy
  obtain ⟨a, ha, b, hb, rfl⟩ := Subgroup.mem_sup.1 hz
  exact ⟨a, ha, b, hb, c, hc, d, hd, rfl⟩

private theorem Setup.mem_K₂_of (S : Setup ρ U₁ U₂ U₃ U₄ K₂ K₃) {y : M}
    (hy : y ∈ K₂ ⊔ (U₁ ⊔ U₃ ⊔ U₄)) (hy2 : y ∈ U₂) : y ∈ K₂ := by
  obtain ⟨k, hk, r, hr, rfl⟩ := Subgroup.mem_sup.1 hy
  have hr2 : r ∈ U₂ ⊓ (U₁ ⊔ U₃ ⊔ U₄) := by
    refine ⟨?_, hr⟩
    have e : r = k⁻¹ * (k * r) := by group
    rw [e]
    exact Subgroup.mul_mem _ (U₂.inv_mem (S.k₂ hk)) hy2
  rw [S.h₂, Subgroup.mem_bot] at hr2
  rw [hr2, mul_one]
  exact hk

private theorem Setup.mem_K₃_of (S : Setup ρ U₁ U₂ U₃ U₄ K₂ K₃) {y : M}
    (hy : y ∈ K₃ ⊔ (U₁ ⊔ U₂ ⊔ U₄)) (hy3 : y ∈ U₃) : y ∈ K₃ := by
  obtain ⟨k, hk, r, hr, rfl⟩ := Subgroup.mem_sup.1 hy
  have hr3 : r ∈ U₃ ⊓ (U₁ ⊔ U₂ ⊔ U₄) := by
    refine ⟨?_, hr⟩
    have e : r = k⁻¹ * (k * r) := by group
    rw [e]
    exact Subgroup.mul_mem _ (U₃.inv_mem (S.k₃ hk)) hy3
  rw [S.h₃, Subgroup.mem_bot] at hr3
  rw [hr3, mul_one]
  exact hk

private theorem Setup.k₂_of_top (S : Setup ρ U₁ U₂ U₃ U₄ K₂ K₃) (N : Subgroup M)
    (hN : IsMaxSub ρ ⊤ N) : K₂ ≤ N := by
  by_cases hI : N ⊓ U₂ = ⊥
  · exfalso
    have hinvK : ∀ g, ∀ u ∈ K₂, ρ g u ∈ K₂ := S.k₂max.2.1
    have hinv' : ∀ g, ∀ u ∈ N ⊔ K₂, ρ g u ∈ N ⊔ K₂ := inv_sup_of hN.2.1 hinvK
    have hne : N ≠ N ⊔ K₂ := by
      intro hEq
      apply S.k₂ne
      have hK : K₂ ≤ N ⊓ U₂ := le_inf (by rw [hEq]; exact le_sup_right) S.k₂
      rw [hI] at hK
      exact eq_bot_iff.2 hK
    have htop : N ⊔ K₂ ≠ ⊤ := by
      intro hTop
      apply S.k₂max.1.ne
      apply le_antisymm S.k₂
      intro u hu
      have hu' : u ∈ N ⊔ K₂ := by rw [hTop]; exact Subgroup.mem_top u
      obtain ⟨n, hn, k, hk, rfl⟩ := Subgroup.mem_sup.1 hu'
      have hnU : n ∈ N ⊓ U₂ := by
        refine ⟨hn, ?_⟩
        have e : n = (n * k) * k⁻¹ := by group
        rw [e]
        exact U₂.mul_mem hu (U₂.inv_mem (S.k₂ hk))
      rw [hI, Subgroup.mem_bot] at hnU
      rw [hnU, one_mul]
      exact hk
    rcases hN.2.2 (N ⊔ K₂) le_sup_left le_top hinv' with h | h
    · exact hne h.symm
    · exact htop h
  · exact (S.soc₂ (N ⊓ U₂) inf_le_right (inv_inf_of hN.2.1 S.i₂) hI).trans inf_le_left

private theorem Setup.k₃_of_top (S : Setup ρ U₁ U₂ U₃ U₄ K₂ K₃) (N : Subgroup M)
    (hN : IsMaxSub ρ ⊤ N) : K₃ ≤ N := by
  by_cases hI : N ⊓ U₃ = ⊥
  · exfalso
    have hinvK : ∀ g, ∀ u ∈ K₃, ρ g u ∈ K₃ := S.k₃max.2.1
    have hinv' : ∀ g, ∀ u ∈ N ⊔ K₃, ρ g u ∈ N ⊔ K₃ := inv_sup_of hN.2.1 hinvK
    have hne : N ≠ N ⊔ K₃ := by
      intro hEq
      apply S.k₃ne
      have hK : K₃ ≤ N ⊓ U₃ := le_inf (by rw [hEq]; exact le_sup_right) S.k₃
      rw [hI] at hK
      exact eq_bot_iff.2 hK
    have htop : N ⊔ K₃ ≠ ⊤ := by
      intro hTop
      apply S.k₃max.1.ne
      apply le_antisymm S.k₃
      intro u hu
      have hu' : u ∈ N ⊔ K₃ := by rw [hTop]; exact Subgroup.mem_top u
      obtain ⟨n, hn, k, hk, rfl⟩ := Subgroup.mem_sup.1 hu'
      have hnU : n ∈ N ⊓ U₃ := by
        refine ⟨hn, ?_⟩
        have e : n = (n * k) * k⁻¹ := by group
        rw [e]
        exact U₃.mul_mem hu (U₃.inv_mem (S.k₃ hk))
      rw [hI, Subgroup.mem_bot] at hnU
      rw [hnU, one_mul]
      exact hk
    rcases hN.2.2 (N ⊔ K₃) le_sup_left le_top hinv' with h | h
    · exact hne h.symm
    · exact htop h
  · exact (S.soc₃ (N ⊓ U₃) inf_le_right (inv_inf_of hN.2.1 S.i₃) hI).trans inf_le_left

private theorem mem_N1 {U₂ U₃ U₄ : Subgroup M} {b c d : M} (hb : b ∈ U₂) (hc : c ∈ U₃)
    (hd : d ∈ U₄) :
    b * c * d ∈ U₂ ⊔ U₃ ⊔ U₄ :=
  Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mem_sup_left (Subgroup.mem_sup_left hb))
    (Subgroup.mem_sup_left (Subgroup.mem_sup_right hc))) (Subgroup.mem_sup_right hd)

private theorem mem_N2 {U₁ U₃ U₄ : Subgroup M} {a c d : M} (ha : a ∈ U₁) (hc : c ∈ U₃)
    (hd : d ∈ U₄) :
    a * c * d ∈ U₁ ⊔ U₃ ⊔ U₄ :=
  Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mem_sup_left (Subgroup.mem_sup_left ha))
    (Subgroup.mem_sup_left (Subgroup.mem_sup_right hc))) (Subgroup.mem_sup_right hd)

private theorem mem_N3 {U₁ U₂ U₄ : Subgroup M} {a b d : M} (ha : a ∈ U₁) (hb : b ∈ U₂)
    (hd : d ∈ U₄) :
    a * b * d ∈ U₁ ⊔ U₂ ⊔ U₄ :=
  Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mem_sup_left (Subgroup.mem_sup_left ha))
    (Subgroup.mem_sup_left (Subgroup.mem_sup_right hb))) (Subgroup.mem_sup_right hd)

private theorem mem_N4 {U₁ U₂ U₃ : Subgroup M} {a b c : M} (ha : a ∈ U₁) (hb : b ∈ U₂)
    (hc : c ∈ U₃) :
    a * b * c ∈ U₁ ⊔ U₂ ⊔ U₃ :=
  Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mem_sup_left (Subgroup.mem_sup_left ha))
    (Subgroup.mem_sup_left (Subgroup.mem_sup_right hb))) (Subgroup.mem_sup_right hc)

private theorem mem_of_mul_mem {N : Subgroup M} {x u r : M} (hx : x ∈ N) (hr : r ∈ N)
    (h : u * r = x) :
    u ∈ N := by
  rw [← h] at hx
  exact (N.mul_mem_cancel_right hr).1 hx

private theorem Setup.max_N1 (S : Setup ρ U₁ U₂ U₃ U₄ K₂ K₃) :
    IsMaxSub ρ ⊤ (U₂ ⊔ U₃ ⊔ U₄) := by
  refine ⟨?_, inv_sup_of (inv_sup_of S.i₂ S.i₃) S.i₄, ?_⟩
  · refine lt_of_le_of_ne le_top ?_
    intro h
    apply S.hU₁
    have h1 : U₁ ⊓ (U₂ ⊔ U₃ ⊔ U₄) = U₁ := by rw [h, inf_top_eq]
    exact h1.symm.trans S.h₁
  · intro N' hle _ hinv
    by_cases hN : N' = U₂ ⊔ U₃ ⊔ U₄
    · exact Or.inl hN
    right
    have hx : ∃ x ∈ N', x ∉ U₂ ⊔ U₃ ⊔ U₄ := by
      by_contra hcon
      push_neg at hcon
      exact hN (le_antisymm (fun x hx => hcon x hx) hle)
    obtain ⟨x, hxN', hxN⟩ := hx
    obtain ⟨a, ha, b, hb, c, hc, d, hd, rfl⟩ := S.decomp x
    have hb1 : b ∈ (U₂ ⊔ U₃) ⊔ U₄ := Subgroup.mem_sup_left (Subgroup.mem_sup_left hb)
    have hc1 : c ∈ (U₂ ⊔ U₃) ⊔ U₄ := Subgroup.mem_sup_left (Subgroup.mem_sup_right hc)
    have hd1 : d ∈ (U₂ ⊔ U₃) ⊔ U₄ := Subgroup.mem_sup_right hd
    have hbcd : b * c * d ∈ U₂ ⊔ U₃ ⊔ U₄ :=
      Subgroup.mul_mem _ (Subgroup.mul_mem _ hb1 hc1) hd1
    have hbcd' : b * c * d ∈ N' := hle hbcd
    have ha' : a ∈ N' := mem_of_mul_mem hxN' hbcd' (by ac_rfl)
    have ha1 : a ≠ 1 := by
      rintro rfl
      apply hxN
      simpa using hbcd
    have hU1N' : U₁ ≤ N' := by
      rcases S.s₁ (U₁ ⊓ N') inf_le_left (inv_inf_of S.i₁ hinv) with h | h
      · exfalso
        have hm : a ∈ U₁ ⊓ N' := ⟨ha, ha'⟩
        rw [h, Subgroup.mem_bot] at hm
        exact ha1 hm
      · have := (inf_le_right : U₁ ⊓ N' ≤ N')
        rwa [h] at this
    apply eq_top_iff.2
    intro y _
    obtain ⟨a', ha', b', hb', c', hc', d', hd', rfl⟩ := S.decomp y
    have hr : b' * c' * d' ∈ N' := hle (mem_N1 hb' hc' hd')
    have e : a' * b' * c' * d' = a' * (b' * c' * d') := by group
    rw [e]
    exact N'.mul_mem (hU1N' ha') hr

private theorem Setup.max_N4 (S : Setup ρ U₁ U₂ U₃ U₄ K₂ K₃) :
    IsMaxSub ρ ⊤ (U₁ ⊔ U₂ ⊔ U₃) := by
  refine ⟨?_, inv_sup_of (inv_sup_of S.i₁ S.i₂) S.i₃, ?_⟩
  · refine lt_of_le_of_ne le_top ?_
    intro h
    apply S.hU₄
    have h1 : U₄ ⊓ (U₁ ⊔ U₂ ⊔ U₃) = U₄ := by rw [h, inf_top_eq]
    exact h1.symm.trans S.h₄
  · intro N' hle _ hinv
    by_cases hN : N' = U₁ ⊔ U₂ ⊔ U₃
    · exact Or.inl hN
    right
    have hx : ∃ x ∈ N', x ∉ U₁ ⊔ U₂ ⊔ U₃ := by
      by_contra hcon
      push_neg at hcon
      exact hN (le_antisymm (fun x hx => hcon x hx) hle)
    obtain ⟨x, hxN', hxN⟩ := hx
    obtain ⟨a, ha, b, hb, c, hc, d, hd, rfl⟩ := S.decomp x
    have ha1 : a ∈ (U₁ ⊔ U₂) ⊔ U₃ := Subgroup.mem_sup_left (Subgroup.mem_sup_left ha)
    have hb1 : b ∈ (U₁ ⊔ U₂) ⊔ U₃ := Subgroup.mem_sup_left (Subgroup.mem_sup_right hb)
    have hc1 : c ∈ (U₁ ⊔ U₂) ⊔ U₃ := Subgroup.mem_sup_right hc
    have habc : a * b * c ∈ U₁ ⊔ U₂ ⊔ U₃ :=
      Subgroup.mul_mem _ (Subgroup.mul_mem _ ha1 hb1) hc1
    have habc' : a * b * c ∈ N' := hle habc
    have hd' : d ∈ N' := mem_of_mul_mem hxN' habc' (by ac_rfl)
    have hd1 : d ≠ 1 := by
      rintro rfl
      apply hxN
      simpa using habc
    have hU4N' : U₄ ≤ N' := by
      rcases S.s₄ (U₄ ⊓ N') inf_le_left (inv_inf_of S.i₄ hinv) with h | h
      · exfalso
        have hm : d ∈ U₄ ⊓ N' := ⟨hd, hd'⟩
        rw [h, Subgroup.mem_bot] at hm
        exact hd1 hm
      · have := (inf_le_right : U₄ ⊓ N' ≤ N')
        rwa [h] at this
    apply eq_top_iff.2
    intro y _
    obtain ⟨a', ha', b', hb', c', hc', d', hd', rfl⟩ := S.decomp y
    have hr : a' * b' * c' ∈ N' := hle (mem_N4 ha' hb' hc')
    exact N'.mul_mem hr (hU4N' hd')

section Art2

variable {ρ : G →* MulAut M} {U₁ U₂ U₃ U₄ K₂ K₃ : Subgroup M}

private theorem Setup.max_N2 (S : Setup ρ U₁ U₂ U₃ U₄ K₂ K₃) :
    IsMaxSub ρ ⊤ (K₂ ⊔ (U₁ ⊔ U₃ ⊔ U₄)) := by
  refine ⟨?_, inv_sup_of S.k₂max.2.1 (inv_sup_of (inv_sup_of S.i₁ S.i₃) S.i₄), ?_⟩
  · refine lt_of_le_of_ne le_top ?_
    intro h
    apply S.k₂max.1.ne
    apply le_antisymm S.k₂
    intro u hu
    have hu' : u ∈ K₂ ⊔ (U₁ ⊔ U₃ ⊔ U₄) := by rw [h]; exact Subgroup.mem_top u
    exact S.mem_K₂_of hu' hu
  · intro N' hle _ hinv
    by_cases hN : N' = K₂ ⊔ (U₁ ⊔ U₃ ⊔ U₄)
    · exact Or.inl hN
    right
    have hx : ∃ x ∈ N', x ∉ K₂ ⊔ (U₁ ⊔ U₃ ⊔ U₄) := by
      by_contra hcon
      push_neg at hcon
      exact hN (le_antisymm (fun x hx => hcon x hx) hle)
    obtain ⟨x, hxN', hxN⟩ := hx
    obtain ⟨a, ha, b, hb, c, hc, d, hd, rfl⟩ := S.decomp x
    have hacd : a * c * d ∈ U₁ ⊔ U₃ ⊔ U₄ := mem_N2 ha hc hd
    have hacd' : a * c * d ∈ N' := hle (Subgroup.mem_sup_right hacd)
    have hb' : b ∈ N' := mem_of_mul_mem hxN' hacd' (by ac_rfl)
    have hbK : b ∉ K₂ := by
      intro hbK
      apply hxN
      have e : a * b * c * d = b * (a * c * d) := by ac_rfl
      rw [e]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hbK) (Subgroup.mem_sup_right hacd)
    have hW : U₂ ≤ N' := by
      rcases S.k₂max.2.2 (U₂ ⊓ N') (le_inf S.k₂ (fun y hy => hle (Subgroup.mem_sup_left hy)))
        inf_le_left (inv_inf_of S.i₂ hinv) with h | h
      · exfalso
        have hm : b ∈ U₂ ⊓ N' := ⟨hb, hb'⟩
        rw [h] at hm
        exact hbK hm
      · have := (inf_le_right : U₂ ⊓ N' ≤ N')
        rwa [h] at this
    apply eq_top_iff.2
    intro y _
    obtain ⟨a', ha', b', hb', c', hc', d', hd', rfl⟩ := S.decomp y
    have hr : a' * c' * d' ∈ N' := hle (Subgroup.mem_sup_right (mem_N2 ha' hc' hd'))
    have e : a' * b' * c' * d' = b' * (a' * c' * d') := by ac_rfl
    rw [e]
    exact N'.mul_mem (hW hb') hr

private theorem Setup.max_N3 (S : Setup ρ U₁ U₂ U₃ U₄ K₂ K₃) :
    IsMaxSub ρ ⊤ (K₃ ⊔ (U₁ ⊔ U₂ ⊔ U₄)) := by
  refine ⟨?_, inv_sup_of S.k₃max.2.1 (inv_sup_of (inv_sup_of S.i₁ S.i₂) S.i₄), ?_⟩
  · refine lt_of_le_of_ne le_top ?_
    intro h
    apply S.k₃max.1.ne
    apply le_antisymm S.k₃
    intro u hu
    have hu' : u ∈ K₃ ⊔ (U₁ ⊔ U₂ ⊔ U₄) := by rw [h]; exact Subgroup.mem_top u
    exact S.mem_K₃_of hu' hu
  · intro N' hle _ hinv
    by_cases hN : N' = K₃ ⊔ (U₁ ⊔ U₂ ⊔ U₄)
    · exact Or.inl hN
    right
    have hx : ∃ x ∈ N', x ∉ K₃ ⊔ (U₁ ⊔ U₂ ⊔ U₄) := by
      by_contra hcon
      push_neg at hcon
      exact hN (le_antisymm (fun x hx => hcon x hx) hle)
    obtain ⟨x, hxN', hxN⟩ := hx
    obtain ⟨a, ha, b, hb, c, hc, d, hd, rfl⟩ := S.decomp x
    have habd : a * b * d ∈ U₁ ⊔ U₂ ⊔ U₄ := mem_N3 ha hb hd
    have habd' : a * b * d ∈ N' := hle (Subgroup.mem_sup_right habd)
    have hc' : c ∈ N' := mem_of_mul_mem hxN' habd' (by ac_rfl)
    have hcK : c ∉ K₃ := by
      intro hcK
      apply hxN
      have e : a * b * c * d = c * (a * b * d) := by ac_rfl
      rw [e]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hcK) (Subgroup.mem_sup_right habd)
    have hW : U₃ ≤ N' := by
      rcases S.k₃max.2.2 (U₃ ⊓ N') (le_inf S.k₃ (fun y hy => hle (Subgroup.mem_sup_left hy)))
        inf_le_left (inv_inf_of S.i₃ hinv) with h | h
      · exfalso
        have hm : c ∈ U₃ ⊓ N' := ⟨hc, hc'⟩
        rw [h] at hm
        exact hcK hm
      · have := (inf_le_right : U₃ ⊓ N' ≤ N')
        rwa [h] at this
    apply eq_top_iff.2
    intro y _
    obtain ⟨a', ha', b', hb', c', hc', d', hd', rfl⟩ := S.decomp y
    have hr : a' * b' * d' ∈ N' := hle (Subgroup.mem_sup_right (mem_N3 ha' hb' hd'))
    have e : a' * b' * c' * d' = c' * (a' * b' * d') := by ac_rfl
    rw [e]
    exact N'.mul_mem (hW hc') hr

private theorem Setup.rad_U2 (S : Setup ρ U₁ U₂ U₃ U₄ K₂ K₃) : radSub ρ U₂ = K₂ := by
  apply le_antisymm
  · unfold radSub
    exact inf_le_of_right_le (iInf₂_le K₂ S.k₂max)
  · unfold radSub
    refine le_inf S.k₂ (le_iInf fun N => le_iInf fun hN => ?_)
    by_cases hN0 : N = ⊥
    · exfalso
      subst hN0
      rcases hN.2.2 K₂ bot_le S.k₂ S.k₂max.2.1 with h | h
      · exact S.k₂ne h
      · exact S.k₂max.1.ne h
    · exact S.soc₂ N hN.1.le hN.2.1 hN0

private theorem Setup.rad_U3 (S : Setup ρ U₁ U₂ U₃ U₄ K₂ K₃) : radSub ρ U₃ = K₃ := by
  apply le_antisymm
  · unfold radSub
    exact inf_le_of_right_le (iInf₂_le K₃ S.k₃max)
  · unfold radSub
    refine le_inf S.k₃ (le_iInf fun N => le_iInf fun hN => ?_)
    by_cases hN0 : N = ⊥
    · exfalso
      subst hN0
      rcases hN.2.2 K₃ bot_le S.k₃ S.k₃max.2.1 with h | h
      · exact S.k₃ne h
      · exact S.k₃max.1.ne h
    · exact S.soc₃ N hN.1.le hN.2.1 hN0

private theorem Setup.inf_K (S : Setup ρ U₁ U₂ U₃ U₄ K₂ K₃) : K₂ ⊓ K₃ = ⊥ := by
  apply eq_bot_iff.2
  intro x hx
  rw [Subgroup.mem_bot]
  have hR : x ∈ U₂ ⊓ (U₁ ⊔ U₃ ⊔ U₄) :=
    ⟨S.k₂ hx.1, Subgroup.mem_sup_left (Subgroup.mem_sup_right (S.k₃ hx.2))⟩
  rw [S.h₂, Subgroup.mem_bot] at hR
  exact hR

private theorem Setup.rad_top (S : Setup ρ U₁ U₂ U₃ U₄ K₂ K₃) : radSub ρ ⊤ = K₂ ⊔ K₃ := by
  apply le_antisymm
  · intro x hx
    unfold radSub at hx
    have hxI := (Subgroup.mem_inf.1 hx).2
    have hx2 : x ∈ K₂ ⊔ (U₁ ⊔ U₃ ⊔ U₄) :=
      Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 hxI (K₂ ⊔ (U₁ ⊔ U₃ ⊔ U₄))) S.max_N2
    have hx3 : x ∈ K₃ ⊔ (U₁ ⊔ U₂ ⊔ U₄) :=
      Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 hxI (K₃ ⊔ (U₁ ⊔ U₂ ⊔ U₄))) S.max_N3
    have hx1 : x ∈ U₂ ⊔ U₃ ⊔ U₄ :=
      Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 hxI (U₂ ⊔ U₃ ⊔ U₄)) S.max_N1
    have hx4 : x ∈ U₁ ⊔ U₂ ⊔ U₃ :=
      Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 hxI (U₁ ⊔ U₂ ⊔ U₃)) S.max_N4
    obtain ⟨a, ha, b, hb, c, hc, d, hd, rfl⟩ := S.decomp x
    have ha1 : a = 1 := by
      have hm : a ∈ U₁ ⊓ (U₂ ⊔ U₃ ⊔ U₄) :=
        ⟨ha, mem_of_mul_mem hx1 (mem_N1 hb hc hd) (by ac_rfl)⟩
      rw [S.h₁, Subgroup.mem_bot] at hm
      exact hm
    have hd1 : d = 1 := by
      have hm : d ∈ U₄ ⊓ (U₁ ⊔ U₂ ⊔ U₃) :=
        ⟨hd, mem_of_mul_mem hx4 (mem_N4 ha hb hc) (by ac_rfl)⟩
      rw [S.h₄, Subgroup.mem_bot] at hm
      exact hm
    have hbN : b ∈ K₂ ⊔ (U₁ ⊔ U₃ ⊔ U₄) :=
      mem_of_mul_mem hx2 (Subgroup.mem_sup_right (mem_N2 ha hc hd))
        (by ac_rfl)
    have hcN : c ∈ K₃ ⊔ (U₁ ⊔ U₂ ⊔ U₄) :=
      mem_of_mul_mem hx3 (Subgroup.mem_sup_right (mem_N3 ha hb hd))
        (by ac_rfl)
    have hbK : b ∈ K₂ := S.mem_K₂_of hbN hb
    have hcK : c ∈ K₃ := S.mem_K₃_of hcN hc
    rw [ha1, hd1, one_mul, mul_one]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hbK) (Subgroup.mem_sup_right hcK)
  · exact le_inf le_top (le_iInf fun N => le_iInf fun hN =>
      sup_le (S.k₂_of_top N hN) (S.k₃_of_top N hN))

private theorem Setup.radical (S : Setup ρ U₁ U₂ U₃ U₄ K₂ K₃) :
    radSub ρ ⊤ = K₂ ⊔ K₃ ∧ radSub ρ U₂ = K₂ ∧ radSub ρ U₃ = K₃ ∧ K₂ ⊓ K₃ = ⊥ :=
  ⟨S.rad_top, S.rad_U2, S.rad_U3, S.inf_K⟩

end Art2

end Art

end ArtH62


namespace FlagH62

open CFSG.ASVolI.ChH Matrix

private abbrev Fl : Type := {p : V3 × V3 // p.1 ≠ 0 ∧ p.2 ≠ 0 ∧ p.2 ⬝ᵥ p.1 = 0}

private instance : Fintype Fl := Subtype.fintype _

private def gPt (g : GL (Fin 3) (ZMod 2)) (x : V3) : V3 :=
  (g : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec x

private def gDu (g : GL (Fin 3) (ZMod 2)) (a : V3) : V3 :=
  ((g⁻¹ : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)).transpose.mulVec a

private theorem gPt_mul (g h : GL (Fin 3) (ZMod 2)) (x : V3) : gPt (g * h) x = gPt g (gPt h x) := by
  unfold gPt
  rw [Units.val_mul, Matrix.mulVec_mulVec]

private theorem gPt_one (x : V3) : gPt 1 x = x := by
  unfold gPt
  simp

private theorem gPt_zero (g : GL (Fin 3) (ZMod 2)) : gPt g 0 = 0 := by
  unfold gPt
  simp

private theorem gDu_mul (g h : GL (Fin 3) (ZMod 2)) (a : V3) : gDu (g * h) a = gDu g (gDu h a) := by
  unfold gDu
  rw [_root_.mul_inv_rev, Units.val_mul, Matrix.transpose_mul, Matrix.mulVec_mulVec]

private theorem gDu_one (a : V3) : gDu 1 a = a := by
  unfold gDu
  simp

private theorem gDu_zero (g : GL (Fin 3) (ZMod 2)) : gDu g 0 = 0 := by
  unfold gDu
  simp

private theorem dot_gDu_gPt (g : GL (Fin 3) (ZMod 2)) (a x : V3) :
    gDu g a ⬝ᵥ gPt g x = a ⬝ᵥ x := by
  unfold gDu gPt
  rw [Matrix.mulVec_transpose, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec,
    ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]

private theorem dot_gDu (g : GL (Fin 3) (ZMod 2)) (a v : V3) :
    gDu g a ⬝ᵥ v = a ⬝ᵥ gPt g⁻¹ v := by
  have h := dot_gDu_gPt g a (gPt g⁻¹ v)
  rwa [← gPt_mul, mul_inv_cancel, gPt_one] at h

private theorem gPt_ne (g : GL (Fin 3) (ZMod 2)) {x : V3} (hx : x ≠ 0) : gPt g x ≠ 0 := by
  intro h
  apply hx
  have h' := congrArg (gPt g⁻¹) h
  rwa [← gPt_mul, inv_mul_cancel, gPt_one, gPt_zero] at h'

private theorem gDu_ne (g : GL (Fin 3) (ZMod 2)) {a : V3} (ha : a ≠ 0) : gDu g a ≠ 0 := by
  intro h
  apply ha
  have h' := congrArg (gDu g⁻¹) h
  rwa [← gDu_mul, inv_mul_cancel, gDu_one, gDu_zero] at h'

private instance flagAct : MulAction (GL (Fin 3) (ZMod 2)) Fl where
  smul g φ := ⟨(gPt g φ.1.1, gDu g φ.1.2),
    gPt_ne g φ.2.1, gDu_ne g φ.2.2.1, by rw [dot_gDu_gPt]; exact φ.2.2.2⟩
  one_smul φ := Subtype.ext (Prod.ext (gPt_one _) (gDu_one _))
  mul_smul g h φ := Subtype.ext (Prod.ext (gPt_mul g h _) (gDu_mul g h _))

private theorem smul_fst (g : GL (Fin 3) (ZMod 2)) (φ : Fl) : (g • φ).1.1 = gPt g φ.1.1 := rfl

private theorem smul_snd (g : GL (Fin 3) (ZMod 2)) (φ : Fl) : (g • φ).1.2 = gDu g φ.1.2 := rfl

private theorem card_Fl : Fintype.card Fl = 21 := by decide

private theorem dual_eq_of_ker : ∀ a b : V3, (∀ v : V3, a ⬝ᵥ v = 0 ↔ b ⬝ᵥ v = 0) → a = b := by
  decide

end FlagH62

namespace FlagH62

open CFSG.ASVolI.ChH Matrix

private theorem exists_dual {T : Subgroup (GL (Fin 3) (ZMod 2))} {p : V3}
    {l : Submodule (ZMod 2) V3}
    (hyp : HypH5 T p l) :
    ∃ a : V3, a ≠ 0 ∧ (∀ v : V3, v ∈ l ↔ a ⬝ᵥ v = 0) ∧ a ⬝ᵥ p = 0 := by
  obtain ⟨c, -, -, hpc, hline⟩ := conj_data6 T p l hyp
  refine ⟨((c⁻¹ : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)) 2, ?_, ?_, ?_⟩
  · intro h0
    have h1 := mulVec_inv_mulVec_gl c ![0, 0, 1]
    have h2 : ((c⁻¹ : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec
        ((c : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec ![0, 0, 1]) 2 = 1 := by
      rw [h1]
      rfl
    have h3 : ((c⁻¹ : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec
        ((c : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec ![0, 0, 1]) 2 =
        ((c⁻¹ : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)) 2 ⬝ᵥ
          ((c : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec ![0, 0, 1]) := rfl
    rw [h3, h0] at h2
    simp at h2
  · intro v
    have h := hline (((c⁻¹ : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec v)
    rw [mulVec_inv_mulVec] at h
    exact h
  · rw [← hpc]
    show ((c⁻¹ : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec
      ((c : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec e1) 2 = 0
    rw [mulVec_inv_mulVec_gl c e1]
    rfl

private theorem stab_mem {T : Subgroup (GL (Fin 3) (ZMod 2))} {p : V3} {l : Submodule (ZMod 2) V3}
    (hyp : HypH5 T p l) {a : V3} (ha : ∀ v : V3, v ∈ l ↔ a ⬝ᵥ v = 0)
    (g : GL (Fin 3) (ZMod 2)) (hp : gPt g p = p) (hd : gDu g a = a) : g ∈ T := by
  obtain ⟨c, hcT, -, hpc, hline⟩ := conj_data6 T p l hyp
  have hgp : (g : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec p = p := hp
  have hgl : ∀ w ∈ l, (g : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec w ∈ l := by
    intro w hw
    apply (ha _).2
    have h := dot_gDu_gPt g a w
    rw [hd] at h
    exact h.trans ((ha w).1 hw)
  apply (hcT g).2
  apply Lpt_inter_le_B0
  · intro v hv
    rw [Set.mem_singleton_iff.1 hv, mulVec_gl, mulVec_gl, hpc, hgp, ← hpc,
      mulVec_inv_mulVec_gl]
  · intro v hv
    have hv' : v ∈ line0 := hv
    rw [mem_line0] at hv'
    rw [mulVec_gl, mulVec_gl]
    have hX : (g : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec
        ((c : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec v) ∈ l :=
      hgl _ ((hline v).2 hv')
    have h := hline (((c⁻¹ : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec
      ((g : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec
        ((c : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec v)))
    rw [mulVec_inv_mulVec] at h
    exact mem_line0.2 (h.1 hX)

private theorem gDu_fix {T : Subgroup (GL (Fin 3) (ZMod 2))} {p : V3} {l : Submodule (ZMod 2) V3}
    (hyp : HypH5 T p l) {a : V3} (ha : ∀ v : V3, v ∈ l ↔ a ⬝ᵥ v = 0)
    (t : GL (Fin 3) (ZMod 2)) (ht : t ∈ T) : gDu t a = a := by
  apply dual_eq_of_ker
  intro v
  rw [dot_gDu]
  constructor
  · intro h
    apply (ha v).1
    have hm : gPt t⁻¹ v ∈ l := (ha _).2 h
    have := hyp.l_inv t ht _ hm
    rwa [show (t : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec (gPt t⁻¹ v) = v from
      mulVec_inv_mulVec t v] at this
  · intro h
    exact (ha _).1 (hyp.l_inv t⁻¹ (T.inv_mem ht) v ((ha v).2 h))

private theorem B0_card : Nat.card CFSG.ASVolI.B0 = 8 := by
  unfold CFSG.ASVolI.B0
  rw [Subgroup.card_map_of_injective (f := slGL.toMonoidHom) slGL.injective,
    CFSG.Quasithin.MS93.card_sStar]
  simp [Nat.card_eq_fintype_card, ZMod.card]

private theorem card_T {T : Subgroup (GL (Fin 3) (ZMod 2))} {p : V3} {l : Submodule (ZMod 2) V3}
    (hyp : HypH5 T p l) : Nat.card T = 8 := by
  obtain ⟨c, hcT, hcB, -, -⟩ := conj_data6 T p l hyp
  have hmap : T.map (MulAut.conj c⁻¹).toMonoidHom = CFSG.ASVolI.B0 := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      have h1 := (hcT x).1 hx
      simpa [MulAut.conj_apply, mul_assoc] using h1
    · intro hy
      refine ⟨c * y * c⁻¹, hcB y hy, ?_⟩
      simp [MulAut.conj_apply, mul_assoc]
  rw [← Subgroup.card_map_of_injective (f := (MulAut.conj c⁻¹).toMonoidHom)
    (MulAut.conj c⁻¹).injective, hmap, B0_card]

private theorem card_quot {T : Subgroup (GL (Fin 3) (ZMod 2))} {p : V3} {l : Submodule (ZMod 2) V3}
    (hyp : HypH5 T p l) : Nat.card (GL (Fin 3) (ZMod 2) ⧸ T) = 21 := by
  have h1 : T.index * Nat.card T = Nat.card (GL (Fin 3) (ZMod 2)) := Subgroup.index_mul_card T
  have h2 : Nat.card (GL (Fin 3) (ZMod 2)) = 168 := by
    rw [← Nat.card_congr slGL.toEquiv]
    exact CFSG.Quasithin.H6.card_gamma
  rw [card_T hyp, h2] at h1
  have h3 : T.index = 21 := by omega
  have h4 : Nat.card (GL (Fin 3) (ZMod 2) ⧸ T) = T.index := rfl
  rw [h4, h3]

private def thetaOf (T : Subgroup (GL (Fin 3) (ZMod 2))) (φ₀ : Fl) (hT : ∀ t ∈ T, t • φ₀ = φ₀) :
    GL (Fin 3) (ZMod 2) ⧸ T → Fl :=
  Quotient.lift (fun g => g • φ₀) (fun g h hgh => by
    have hgh' : g⁻¹ * h ∈ T := QuotientGroup.leftRel_apply.1 hgh
    show g • φ₀ = h • φ₀
    rw [show h = g * (g⁻¹ * h) by group, mul_smul, hT _ hgh'])

private theorem thetaOf_mk (T : Subgroup (GL (Fin 3) (ZMod 2))) (φ₀ : Fl)
    (hT : ∀ t ∈ T, t • φ₀ = φ₀)
    (g : GL (Fin 3) (ZMod 2)) : thetaOf T φ₀ hT (QuotientGroup.mk g) = g • φ₀ := rfl

private theorem thetaOf_smul (T : Subgroup (GL (Fin 3) (ZMod 2))) (φ₀ : Fl)
    (hT : ∀ t ∈ T, t • φ₀ = φ₀) (x : GL (Fin 3) (ZMod 2)) (q : GL (Fin 3) (ZMod 2) ⧸ T) :
    thetaOf T φ₀ hT (x • q) = x • thetaOf T φ₀ hT q := by
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
  show thetaOf T φ₀ hT (QuotientGroup.mk (x * g)) = x • (g • φ₀)
  rw [thetaOf_mk, mul_smul]

private theorem thetaOf_bijective (T : Subgroup (GL (Fin 3) (ZMod 2))) (φ₀ : Fl)
    (hT : ∀ t ∈ T, t • φ₀ = φ₀) (hstab : ∀ x : GL (Fin 3) (ZMod 2), x • φ₀ = φ₀ → x ∈ T)
    (hcard : Nat.card (GL (Fin 3) (ZMod 2) ⧸ T) = 21) :
    Function.Bijective (thetaOf T φ₀ hT) := by
  have hinj : Function.Injective (thetaOf T φ₀ hT) := by
    intro q₁ q₂ h
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q₁
    obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective q₂
    have h' : g • φ₀ = k • φ₀ := h
    apply QuotientGroup.eq.2
    apply hstab
    rw [mul_smul, ← h', inv_smul_smul]
  have hF : Nat.card Fl = 21 := by
    rw [Nat.card_eq_fintype_card]
    exact card_Fl
  apply hinj.bijective_of_nat_card_le
  exact (hF.trans hcard.symm).le

end FlagH62

namespace FlagH62

open CFSG.ASVolI.ChH Matrix

private def fstAdd : (V3 → ZMod 2) →+ (Fl → ZMod 2) where
  toFun F φ := F φ.1.1
  map_zero' := rfl
  map_add' _ _ := rfl

private def sndAdd : (V3 → ZMod 2) →+ (Fl → ZMod 2) where
  toFun G φ := G φ.1.2
  map_zero' := rfl
  map_add' _ _ := rfl

private def linFstAdd : V3 →+ (Fl → ZMod 2) where
  toFun b φ := b ⬝ᵥ φ.1.1
  map_zero' := by funext φ; simp
  map_add' b c := by funext φ; simp [add_dotProduct]

private def linSndAdd : V3 →+ (Fl → ZMod 2) where
  toFun v φ := φ.1.2 ⬝ᵥ v
  map_zero' := by funext φ; simp
  map_add' v w := by funext φ; simp [dotProduct_add]

private def steinAdd : Matrix (Fin 3) (Fin 3) (ZMod 2) →+ (Fl → ZMod 2) where
  toFun X φ := φ.1.2 ⬝ᵥ (X *ᵥ φ.1.1)
  map_zero' := by funext φ; simp
  map_add' X Y := by funext φ; simp [Matrix.add_mulVec, dotProduct_add]

private def constAdd : ZMod 2 →+ (Fl → ZMod 2) where
  toFun z _ := z
  map_zero' := rfl
  map_add' _ _ := rfl

private abbrev MF : Type := Multiplicative (Fl → ZMod 2)

private abbrev fstHom : Multiplicative (V3 → ZMod 2) →* MF := AddMonoidHom.toMultiplicative fstAdd
private abbrev sndHom : Multiplicative (V3 → ZMod 2) →* MF := AddMonoidHom.toMultiplicative sndAdd
private abbrev linFstHom : Multiplicative V3 →* MF := AddMonoidHom.toMultiplicative linFstAdd
private abbrev linSndHom : Multiplicative V3 →* MF := AddMonoidHom.toMultiplicative linSndAdd
private abbrev steinHom : AdjAmb →* MF := AddMonoidHom.toMultiplicative steinAdd
private abbrev constHom : Multiplicative (ZMod 2) →* MF := AddMonoidHom.toMultiplicative constAdd

private def coreAdd : AddSubgroup (V3 → ZMod 2) :=
  AddMonoidHom.ker (Pi.evalAddMonoidHom (fun _ : V3 => ZMod 2) 0) ⊓
    AddMonoidHom.ker (∑ v : V3, Pi.evalAddMonoidHom (fun _ : V3 => ZMod 2) v)

private def coreV : Subgroup (Multiplicative (V3 → ZMod 2)) := AddSubgroup.toSubgroup coreAdd

private theorem mem_coreV (F : Multiplicative (V3 → ZMod 2)) :
    F ∈ coreV ↔ Multiplicative.toAdd F 0 = 0 ∧ ∑ v : V3, Multiplicative.toAdd F v = 0 := by
  simp [coreV, coreAdd, AddMonoidHom.mem_ker, Finset.sum_apply]

private def U1F : Subgroup MF := (⊤ : Subgroup (Multiplicative (ZMod 2))).map constHom

private def U2F : Subgroup MF := coreV.map fstHom

private def U3F : Subgroup MF := coreV.map sndHom

private def U4F : Subgroup MF := Adj3.map steinHom

private def K2F : Subgroup MF := (⊤ : Subgroup (Multiplicative V3)).map linFstHom

private def K3F : Subgroup MF := (⊤ : Subgroup (Multiplicative V3)).map linSndHom

private abbrev ρF : GL (Fin 3) (ZMod 2) →* MulAut MF := permModAct (GL (Fin 3) (ZMod 2)) Fl

private theorem ρF_apply (g : GL (Fin 3) (ZMod 2)) (f : MF) (φ : Fl) :
    Multiplicative.toAdd (ρF g f) φ = Multiplicative.toAdd f (g⁻¹ • φ) := rfl

private theorem ρF_fst (g : GL (Fin 3) (ZMod 2)) (F : Multiplicative (V3 → ZMod 2)) :
    ρF g (fstHom F) =
      fstHom (Multiplicative.ofAdd fun v => Multiplicative.toAdd F (gPt g⁻¹ v)) := by
  apply Multiplicative.toAdd.injective
  funext φ
  rfl

private theorem ρF_snd (g : GL (Fin 3) (ZMod 2)) (G : Multiplicative (V3 → ZMod 2)) :
    ρF g (sndHom G) =
      sndHom (Multiplicative.ofAdd fun v => Multiplicative.toAdd G (gDu g⁻¹ v)) := by
  apply Multiplicative.toAdd.injective
  funext φ
  rfl

private theorem ρF_linFst (g : GL (Fin 3) (ZMod 2)) (b : Multiplicative V3) :
    ρF g (linFstHom b) = linFstHom (Multiplicative.ofAdd (gDu g (Multiplicative.toAdd b))) := by
  apply Multiplicative.toAdd.injective
  funext φ
  show Multiplicative.toAdd b ⬝ᵥ gPt g⁻¹ φ.1.1 = gDu g (Multiplicative.toAdd b) ⬝ᵥ φ.1.1
  rw [dot_gDu]

private theorem ρF_linSnd (g : GL (Fin 3) (ZMod 2)) (v : Multiplicative V3) :
    ρF g (linSndHom v) = linSndHom (Multiplicative.ofAdd (gPt g (Multiplicative.toAdd v))) := by
  apply Multiplicative.toAdd.injective
  funext φ
  show gDu g⁻¹ φ.1.2 ⬝ᵥ Multiplicative.toAdd v = φ.1.2 ⬝ᵥ gPt g (Multiplicative.toAdd v)
  rw [dot_gDu, inv_inv]

private theorem ρF_stein (g : GL (Fin 3) (ZMod 2)) (X : AdjAmb) :
    ρF g (steinHom X) = steinHom (adjAmbAct g X) := by
  apply Multiplicative.toAdd.injective
  funext φ
  show gDu g⁻¹ φ.1.2 ⬝ᵥ (Multiplicative.toAdd X *ᵥ gPt g⁻¹ φ.1.1) =
    φ.1.2 ⬝ᵥ ((((g : Matrix (Fin 3) (Fin 3) (ZMod 2)) * Multiplicative.toAdd X *
      ((g⁻¹ : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2))) *ᵥ φ.1.1))
  rw [dot_gDu, inv_inv]
  unfold gPt
  simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc]

end FlagH62

namespace FlagH62

open CFSG.ASVolI.ChH Matrix

private theorem steinAdd_apply (X : Matrix (Fin 3) (Fin 3) (ZMod 2)) (φ : Fl) :
    steinAdd X φ = φ.1.2 ⬝ᵥ (X *ᵥ φ.1.1) := rfl

private def bas : Fin 8 → Matrix (Fin 3) (Fin 3) (ZMod 2) :=
  ![!![0, 1, 0; 0, 0, 0; 0, 0, 0], !![0, 0, 0; 1, 0, 0; 0, 0, 0], !![0, 0, 0; 0, 0, 1; 0, 0, 0],
    !![0, 0, 0; 0, 0, 0; 0, 1, 0], !![0, 0, 1; 0, 0, 0; 0, 0, 0], !![0, 0, 0; 0, 0, 0; 1, 0, 0],
    !![1, 1, 0; 1, 1, 0; 0, 0, 0], !![0, 0, 0; 0, 1, 1; 0, 1, 1]]

private def coefX (X : Matrix (Fin 3) (Fin 3) (ZMod 2)) : Fin 8 → ZMod 2 :=
  ![X 0 1 + X 0 0, X 1 0 + X 0 0, X 1 2 + X 2 2, X 2 1 + X 2 2, X 0 2, X 2 0, X 0 0, X 2 2]

private theorem sl3_decomp : ∀ X : Matrix (Fin 3) (Fin 3) (ZMod 2), X.trace = 0 →
    X = ∑ i ∈ Finset.univ.filter (fun i => coefX X i = 1), bas i := by
  decide +kernel

private theorem sl3_fixed_B0 : ∀ X : Matrix (Fin 3) (Fin 3) (ZMod 2), X.trace = 0 →
    !![1, 1, 0; 0, 1, 0; 0, 0, 1] * X = X * !![1, 1, 0; 0, 1, 0; 0, 0, 1] →
    !![1, 0, 0; 0, 1, 1; 0, 0, 1] * X = X * !![1, 0, 0; 0, 1, 1; 0, 0, 1] →
    X = 0 ∨ X = bas 4 := by
  decide +kernel

private def pairF (f g : Fl → ZMod 2) : ZMod 2 := ∑ φ : Fl, f φ * g φ

private theorem fiber_pt_sum : ∀ x : V3, x ≠ 0 →
    ∑ φ ∈ (Finset.univ : Finset Fl).filter (fun φ => φ.1.1 = x), φ.1.2 = 0 := by
  decide

private theorem fiber_du_sum : ∀ a : V3, a ≠ 0 →
    ∑ φ ∈ (Finset.univ : Finset Fl).filter (fun φ => φ.1.2 = a), φ.1.1 = 0 := by
  decide

private theorem pair_stein_fst (X : Matrix (Fin 3) (Fin 3) (ZMod 2)) (F : V3 → ZMod 2) :
    pairF (steinAdd X) (fun φ => F φ.1.1) = 0 := by
  unfold pairF
  rw [← Finset.sum_fiberwise (Finset.univ : Finset Fl) (fun φ : Fl => φ.1.1)]
  apply Finset.sum_eq_zero
  intro x _
  by_cases hx : x = 0
  · apply Finset.sum_eq_zero
    intro φ hφ
    rw [Finset.mem_filter] at hφ
    exact absurd (hφ.2.trans hx) φ.2.1
  · have hsum := fiber_pt_sum x hx
    have h1 : ∀ φ ∈ (Finset.univ : Finset Fl).filter (fun φ => φ.1.1 = x),
        steinAdd X φ * F φ.1.1 = (φ.1.2 ⬝ᵥ (X *ᵥ x)) * F x := by
      intro φ hφ
      rw [Finset.mem_filter] at hφ
      rw [steinAdd_apply, hφ.2]
    rw [Finset.sum_congr rfl h1, ← Finset.sum_mul, ← sum_dotProduct, hsum]
    simp

private theorem pair_stein_snd (X : Matrix (Fin 3) (Fin 3) (ZMod 2)) (G : V3 → ZMod 2) :
    pairF (steinAdd X) (fun φ => G φ.1.2) = 0 := by
  unfold pairF
  rw [← Finset.sum_fiberwise (Finset.univ : Finset Fl) (fun φ : Fl => φ.1.2)]
  apply Finset.sum_eq_zero
  intro a _
  by_cases ha : a = 0
  · apply Finset.sum_eq_zero
    intro φ hφ
    rw [Finset.mem_filter] at hφ
    exact absurd (hφ.2.trans ha) φ.2.2.1
  · have hsum := fiber_du_sum a ha
    have h1 : ∀ φ ∈ (Finset.univ : Finset Fl).filter (fun φ => φ.1.2 = a),
        steinAdd X φ * G φ.1.2 = (a ⬝ᵥ (X *ᵥ φ.1.1)) * G a := by
      intro φ hφ
      rw [Finset.mem_filter] at hφ
      rw [steinAdd_apply, hφ.2]
    rw [Finset.sum_congr rfl h1, ← Finset.sum_mul, ← dotProduct_sum, ← Matrix.mulVec_sum, hsum]
    simp

end FlagH62

namespace FlagH62

open CFSG.ASVolI.ChH Matrix

private theorem zmod2_add_self (x : ZMod 2) : x + x = 0 := by revert x; decide

private def mkInvol (M : Matrix (Fin 3) (Fin 3) (ZMod 2)) (h : M * M = 1) : GL (Fin 3) (ZMod 2) :=
  ⟨M, M, h, h⟩

private def gP : GL (Fin 3) (ZMod 2) := mkInvol !![1, 0, 0; 0, 0, 1; 0, 1, 0] (by decide)
private def gP2 : GL (Fin 3) (ZMod 2) := mkInvol !![1, 0, 0; 0, 1, 0; 0, 1, 1] (by decide)
private def gS : GL (Fin 3) (ZMod 2) := mkInvol !![0, 1, 0; 1, 0, 0; 0, 0, 1] (by decide)
private def gH : GL (Fin 3) (ZMod 2) := mkInvol !![1, 0, 0; 1, 1, 0; 0, 0, 1] (by decide)
private def gT : GL (Fin 3) (ZMod 2) := mkInvol !![1, 1, 0; 0, 1, 0; 0, 0, 1] (by decide)
private def gU : GL (Fin 3) (ZMod 2) := mkInvol !![1, 0, 0; 0, 1, 1; 0, 0, 1] (by decide)

private def d2 (x : V3) : ZMod 2 := x 1 * (1 + x 2)

private def d4 (x : V3) : ZMod 2 := x 2

private def d12 (x : V3) : ZMod 2 :=
  (if x = ![1, 0, 0] then 1 else 0) + (if x = ![0, 1, 0] then 1 else 0)

private theorem I1 : ∀ x : V3, d4 x = d2 (gPt gP⁻¹ x) + d2 (gPt gP2⁻¹ x) := by decide
private theorem I2 : ∀ x : V3,
    (d2 x + d4 x) + (d2 (gPt gS⁻¹ x) + d4 (gPt gS⁻¹ x)) = d12 x := by decide
private theorem I3 : ∀ x : V3, d12 x = d2 (gPt gH⁻¹ x) := by decide
private theorem I5 : ∀ x : V3, d12 (gPt gH⁻¹ x) = d2 x := by decide

private theorem zmod2_one_add_one : (1 : ZMod 2) + 1 = 0 := by decide

private def vec8 : Fin 8 → V3 :=
  ![0, ![1, 0, 0], ![0, 1, 0], ![1, 1, 0], ![0, 0, 1], ![1, 0, 1], ![0, 1, 1], ![1, 1, 1]]

private theorem vec8_bij : Function.Bijective vec8 := by
  decide +kernel

private theorem sum_V3 {M : Type*} [AddCommMonoid M] (f : V3 → M) :
    ∑ v, f v = f 0 + f ![1, 0, 0] + f ![0, 1, 0] + f ![1, 1, 0] + f ![0, 0, 1] +
      f ![1, 0, 1] + f ![0, 1, 1] + f ![1, 1, 1] := by
  rw [← Equiv.sum_comp (Equiv.ofBijective vec8 vec8_bij) f, Fin.sum_univ_eight]
  rfl

private theorem V3_cases : ∀ x : V3, x = 0 ∨ x = ![1, 0, 0] ∨ x = ![0, 1, 0] ∨ x = ![1, 1, 0] ∨
    x = ![0, 0, 1] ∨ x = ![1, 0, 1] ∨ x = ![0, 1, 1] ∨ x = ![1, 1, 1] := by
  decide +kernel

private theorem I4 (F : V3 → ZMod 2) (h0 : F 0 = 0)
    (hsum : F 0 + F ![1, 0, 0] + F ![0, 1, 0] + F ![1, 1, 0] + F ![0, 0, 1] + F ![1, 0, 1] +
      F ![0, 1, 1] + F ![1, 1, 1] = 0)
    (ht : ∀ x, F (gPt gT⁻¹ x) = F x) (hu : ∀ x, F (gPt gU⁻¹ x) = F x) :
    ∀ x, F x = F ![0, 1, 0] * d2 x + F ![0, 0, 1] * d4 x := by
  have e1 : F ![1, 1, 0] = F ![0, 1, 0] := by
    have h := ht ![0, 1, 0]
    rwa [show gPt gT⁻¹ ![0, 1, 0] = ![1, 1, 0] from by decide] at h
  have e2 : F ![1, 1, 1] = F ![0, 1, 1] := by
    have h := ht ![0, 1, 1]
    rwa [show gPt gT⁻¹ ![0, 1, 1] = ![1, 1, 1] from by decide] at h
  have e3 : F ![0, 1, 1] = F ![0, 0, 1] := by
    have h := hu ![0, 0, 1]
    rwa [show gPt gU⁻¹ ![0, 0, 1] = ![0, 1, 1] from by decide] at h
  have e4 : F ![1, 0, 1] = F ![1, 1, 1] := by
    have h := hu ![1, 0, 1]
    rw [show gPt gU⁻¹ ![1, 0, 1] = ![1, 1, 1] from by decide] at h
    exact h.symm
  rw [h0, e1, e4, e2, e3] at hsum
  have key : ∀ a b c : ZMod 2, 0 + a + b + b + c + c + c + c = 0 → a = 0 := by decide
  have h100 : F ![1, 0, 0] = 0 := key _ _ _ hsum
  have hF111 : F ![1, 1, 1] = F ![0, 0, 1] := e2.trans e3
  have hF101 : F ![1, 0, 1] = F ![0, 0, 1] := e4.trans hF111
  intro x
  rcases V3_cases x with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [d2, d4, h0, h100, e1, hF111, hF101, e3, zmod2_one_add_one]

private theorem gT_mem : gT ∈ CFSG.ASVolI.B0 := by
  rw [mem_B0]
  exact ⟨1, 0, 0, rfl⟩

private theorem gU_mem : gU ∈ CFSG.ASVolI.B0 := by
  rw [mem_B0]
  exact ⟨0, 0, 1, rfl⟩

private theorem exists_fixed_pgroup {G : Type*} [Group G] {M : Type*} [CommGroup M] [Finite M]
    (ρ : G →* MulAut M) (H : Subgroup G) (hH : IsPGroup 2 H) (W : Subgroup M)
    (hWi : ∀ g ∈ H, ∀ u ∈ W, ρ g u ∈ W) (hW : W ≠ ⊥) (hexp : ∀ x : M, x ^ 2 = 1) :
    ∃ w ∈ W, w ≠ 1 ∧ ∀ g ∈ H, ρ g w = w := by
  letI : MulAction H W :=
    { smul := fun h w => ⟨ρ (h : G) (w : M), hWi (h : G) h.2 w w.2⟩
      one_smul := fun w => Subtype.ext (by
        show ρ ((1 : H) : G) (w : M) = (w : M)
        rw [Subgroup.coe_one, map_one, MulAut.one_apply])
      mul_smul := fun h k w => Subtype.ext (by
        show ρ ((h * k : H) : G) (w : M) = ρ (h : G) (ρ (k : G) (w : M))
        rw [Subgroup.coe_mul, map_mul, MulAut.mul_apply]) }
  obtain ⟨⟨x, hxW⟩, hx1'⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hW
  have hx1 : x ≠ 1 := fun h => hx1' (Subtype.ext h)
  have h2 : 2 ∣ Nat.card W := by
    have hord : orderOf (⟨x, hxW⟩ : W) = 2 := by
      have hdvd : orderOf (⟨x, hxW⟩ : W) ∣ 2 := by
        apply orderOf_dvd_of_pow_eq_one
        apply Subtype.ext
        simpa using hexp x
      rcases (Nat.dvd_prime Nat.prime_two).1 hdvd with h | h
      · exfalso
        apply hx1
        have := orderOf_eq_one_iff.1 h
        exact congrArg Subtype.val this
      · exact h
    rw [← hord]
    exact orderOf_dvd_natCard _
  have hfix0 : (1 : W) ∈ MulAction.fixedPoints H W := by
    rw [MulAction.mem_fixedPoints]
    intro h
    apply Subtype.ext
    show ρ (h : G) 1 = 1
    exact map_one _
  obtain ⟨b, hb, hne⟩ := hH.exists_fixed_point_of_prime_dvd_card_of_fixed_point W h2 hfix0
  refine ⟨(b : M), b.2, fun h => hne (Subtype.ext h.symm), fun g hg => ?_⟩
  have := MulAction.mem_fixedPoints.1 hb ⟨g, hg⟩
  exact congrArg Subtype.val this

private theorem mf_sq (x : MF) : x ^ 2 = 1 := by
  rw [pow_two]
  apply Multiplicative.toAdd.injective
  funext φ
  show Multiplicative.toAdd x φ + Multiplicative.toAdd x φ = 0
  exact zmod2_add_self _

private theorem dual_trans_e3 : ∀ b : V3, b ≠ 0 → ∃ g : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2),
    gDu (Matrix.SpecialLinearGroup.toGL g) ![0, 0, 1] = b := by
  decide

private theorem dualTrans (b : V3) (hb : b ≠ 0) :
    ∃ g : GL (Fin 3) (ZMod 2), gDu g ![0, 0, 1] = b := by
  obtain ⟨g, hg⟩ := dual_trans_e3 b hb
  exact ⟨_, hg⟩

private theorem dualTrans2 (b b' : V3) (hb : b ≠ 0) (hb' : b' ≠ 0) :
    ∃ g : GL (Fin 3) (ZMod 2), gDu g b = b' := by
  obtain ⟨h₁, h₁e⟩ := dualTrans b hb
  obtain ⟨h₂, h₂e⟩ := dualTrans b' hb'
  refine ⟨h₂ * h₁⁻¹, ?_⟩
  have hinv : gDu h₁⁻¹ (gDu h₁ ![0, 0, 1]) = ![0, 0, 1] := by
    rw [← gDu_mul, inv_mul_cancel, gDu_one]
  rw [gDu_mul, ← h₁e, hinv, h₂e]

private theorem fst_eq_lin_e3 :
    fstHom (Multiplicative.ofAdd d4) = linFstHom (Multiplicative.ofAdd ![0, 0, 1]) := by
  apply Multiplicative.toAdd.injective
  funext φ
  show d4 φ.1.1 = ![0, 0, 1] ⬝ᵥ φ.1.1
  simp [d4, dotProduct, Fin.sum_univ_three]

private theorem socleA (W : Subgroup MF) (hWi : ∀ g, ∀ u ∈ W, ρF g u ∈ W)
    (hw : linFstHom (Multiplicative.ofAdd ![0, 0, 1]) ∈ W) : K2F ≤ W := by
  intro k hk
  obtain ⟨b, -, rfl⟩ := Subgroup.mem_map.1 hk
  by_cases hb : Multiplicative.toAdd b = 0
  · have : b = 1 := by
      apply Multiplicative.toAdd.injective
      simpa using hb
    rw [this, map_one]
    exact W.one_mem
  · obtain ⟨g, hg⟩ := dualTrans (Multiplicative.toAdd b) hb
    have h := hWi g _ hw
    rw [ρF_linFst, toAdd_ofAdd, hg, ofAdd_toAdd] at h
    exact h

private theorem socleB (W : Subgroup MF) (hWi : ∀ g, ∀ u ∈ W, ρF g u ∈ W)
    (hw : fstHom (Multiplicative.ofAdd d2) ∈ W) :
    linFstHom (Multiplicative.ofAdd ![0, 0, 1]) ∈ W := by
  have h3 := W.mul_mem (hWi gP _ hw) (hWi gP2 _ hw)
  have e : ρF gP (fstHom (Multiplicative.ofAdd d2)) * ρF gP2 (fstHom (Multiplicative.ofAdd d2)) =
      linFstHom (Multiplicative.ofAdd ![0, 0, 1]) := by
    rw [ρF_fst, ρF_fst, ← map_mul]
    apply Multiplicative.toAdd.injective
    funext φ
    show d2 (gPt gP⁻¹ φ.1.1) + d2 (gPt gP2⁻¹ φ.1.1) = ![0, 0, 1] ⬝ᵥ φ.1.1
    rw [← I1]
    simp [d4, dotProduct, Fin.sum_univ_three]
  rw [e] at h3
  exact h3

private theorem socleC (W : Subgroup MF) (hWi : ∀ g, ∀ u ∈ W, ρF g u ∈ W)
    (hw : fstHom (Multiplicative.ofAdd (fun x => d2 x + d4 x)) ∈ W) :
    fstHom (Multiplicative.ofAdd d2) ∈ W := by
  have h2 := W.mul_mem hw (hWi gS _ hw)
  have e1 : fstHom (Multiplicative.ofAdd (fun x => d2 x + d4 x)) *
      ρF gS (fstHom (Multiplicative.ofAdd (fun x => d2 x + d4 x))) =
      fstHom (Multiplicative.ofAdd d12) := by
    rw [ρF_fst, ← map_mul]
    congr 1
    apply Multiplicative.toAdd.injective
    funext x
    show (d2 x + d4 x) + (d2 (gPt gS⁻¹ x) + d4 (gPt gS⁻¹ x)) = d12 x
    exact I2 x
  rw [e1] at h2
  have h3 := hWi gH _ h2
  have e2 : ρF gH (fstHom (Multiplicative.ofAdd d12)) = fstHom (Multiplicative.ofAdd d2) := by
    rw [ρF_fst]
    congr 1
    apply Multiplicative.toAdd.injective
    funext x
    show d12 (gPt gH⁻¹ x) = d2 x
    exact I5 x
  rw [e2] at h3
  exact h3

private theorem pt_has_dual : ∀ x : V3, x ≠ 0 → ∃ a : V3, a ≠ 0 ∧ a ⬝ᵥ x = 0 := by decide

private theorem dual_has_pt : ∀ a : V3, a ≠ 0 → ∃ x : V3, x ≠ 0 ∧ a ⬝ᵥ x = 0 := by decide

private theorem fst_inj (F₁ F₂ : Multiplicative (V3 → ZMod 2)) (h₁ : Multiplicative.toAdd F₁ 0 = 0)
    (h₂ : Multiplicative.toAdd F₂ 0 = 0) (h : fstHom F₁ = fstHom F₂) : F₁ = F₂ := by
  apply Multiplicative.toAdd.injective
  funext x
  by_cases hx : x = 0
  · rw [hx, h₁, h₂]
  · obtain ⟨a, ha, hax⟩ := pt_has_dual x hx
    exact congrArg (fun f : MF => Multiplicative.toAdd f ⟨(x, a), hx, ha, hax⟩) h

private theorem snd_inj (G₁ G₂ : Multiplicative (V3 → ZMod 2)) (h₁ : Multiplicative.toAdd G₁ 0 = 0)
    (h₂ : Multiplicative.toAdd G₂ 0 = 0) (h : sndHom G₁ = sndHom G₂) : G₁ = G₂ := by
  apply Multiplicative.toAdd.injective
  funext a
  by_cases ha : a = 0
  · rw [ha, h₁, h₂]
  · obtain ⟨x, hx, hax⟩ := dual_has_pt a ha
    exact congrArg (fun f : MF => Multiplicative.toAdd f ⟨(x, a), hx, ha, hax⟩) h

private theorem pgroupB0 : IsPGroup 2 ↥CFSG.ASVolI.B0 :=
  IsPGroup.iff_card.2 ⟨3, by rw [B0_card]; norm_num⟩

private theorem socle_fun (W : Subgroup MF) (hWi : ∀ g, ∀ u ∈ W, ρF g u ∈ W) (β γ : ZMod 2)
    (hne : β ≠ 0 ∨ γ ≠ 0)
    (h : fstHom (Multiplicative.ofAdd (fun x => β * d2 x + γ * d4 x)) ∈ W) : K2F ≤ W := by
  apply socleA W hWi
  have hz : ∀ z : ZMod 2, z = 0 ∨ z = 1 := by decide
  rcases hz β with rfl | rfl <;> rcases hz γ with rfl | rfl
  · exact hne.elim (fun h => (h rfl).elim) (fun h => (h rfl).elim)
  · have e : fstHom (Multiplicative.ofAdd (fun x => (0 : ZMod 2) * d2 x + 1 * d4 x)) =
        linFstHom (Multiplicative.ofAdd ![0, 0, 1]) := by
      rw [← fst_eq_lin_e3]
      congr 1
      apply Multiplicative.toAdd.injective
      funext x
      simp
    rw [e] at h
    exact h
  · have e : fstHom (Multiplicative.ofAdd (fun x => (1 : ZMod 2) * d2 x + 0 * d4 x)) =
        fstHom (Multiplicative.ofAdd d2) := by
      congr 1
      apply Multiplicative.toAdd.injective
      funext x
      simp
    rw [e] at h
    exact socleB W hWi h
  · have e : fstHom (Multiplicative.ofAdd (fun x => (1 : ZMod 2) * d2 x + 1 * d4 x)) =
        fstHom (Multiplicative.ofAdd (fun x => d2 x + d4 x)) := by
      congr 1
      apply Multiplicative.toAdd.injective
      funext x
      simp
    rw [e] at h
    exact socleB W hWi (socleC W hWi h)

private theorem socle2 (W : Subgroup MF) (hWU : W ≤ U2F) (hWi : ∀ g, ∀ u ∈ W, ρF g u ∈ W)
    (hW : W ≠ ⊥) : K2F ≤ W := by
  obtain ⟨w, hwW, hw1, hfix⟩ := exists_fixed_pgroup ρF CFSG.ASVolI.B0 pgroupB0 W
    (fun g _ u hu => hWi g u hu) hW mf_sq
  obtain ⟨F, hF, hFw⟩ := Subgroup.mem_map.1 (hWU hwW)
  subst hFw
  obtain ⟨h0, hsum⟩ := (mem_coreV F).1 hF
  have hT : ∀ x, Multiplicative.toAdd F (gPt gT⁻¹ x) = Multiplicative.toAdd F x := by
    intro x
    have h := (ρF_fst gT F).symm.trans (hfix gT gT_mem)
    have h' := fst_inj _ _ (by simp [gPt_zero, h0]) h0 h
    exact congrFun (congrArg Multiplicative.toAdd h') x
  have hU : ∀ x, Multiplicative.toAdd F (gPt gU⁻¹ x) = Multiplicative.toAdd F x := by
    intro x
    have h := (ρF_fst gU F).symm.trans (hfix gU gU_mem)
    have h' := fst_inj _ _ (by simp [gPt_zero, h0]) h0 h
    exact congrFun (congrArg Multiplicative.toAdd h') x
  have hcl := I4 (Multiplicative.toAdd F) h0 ((sum_V3 _).symm.trans hsum) hT hU
  have hFeq : F = Multiplicative.ofAdd (fun x => Multiplicative.toAdd F ![0, 1, 0] * d2 x +
      Multiplicative.toAdd F ![0, 0, 1] * d4 x) := by
    apply Multiplicative.toAdd.injective
    funext x
    simp only [toAdd_ofAdd]
    exact hcl x
  rw [hFeq] at hwW
  refine socle_fun W hWi _ _ ?_ hwW
  by_contra hcon
  push_neg at hcon
  apply hw1
  rw [hFeq, hcon.1, hcon.2]
  apply Multiplicative.toAdd.injective
  funext φ
  simp [fstAdd] <;> rfl

end FlagH62

namespace FlagH62

open CFSG.ASVolI.ChH Matrix

private def d2p (a : V3) : ZMod 2 := (1 + a 0) * a 1

private def d4p (a : V3) : ZMod 2 := a 0

private def gM1 : GL (Fin 3) (ZMod 2) :=
  ⟨!![0, 1, 0; 0, 0, 1; 1, 0, 0], !![0, 0, 1; 1, 0, 0; 0, 1, 0],
  by decide, by decide⟩
private def gM2 : GL (Fin 3) (ZMod 2) :=
  ⟨!![1, 0, 0; 0, 0, 1; 1, 1, 0], !![1, 0, 0; 1, 0, 1; 0, 1, 0],
  by decide, by decide⟩

private theorem I4d (G : V3 → ZMod 2) (h0 : G 0 = 0)
    (hsum : G 0 + G ![1, 0, 0] + G ![0, 1, 0] + G ![1, 1, 0] + G ![0, 0, 1] + G ![1, 0, 1] +
      G ![0, 1, 1] + G ![1, 1, 1] = 0)
    (ht : ∀ a, G (gDu gT⁻¹ a) = G a) (hu : ∀ a, G (gDu gU⁻¹ a) = G a) :
    ∀ a, G a = G ![0, 1, 0] * d2p a + G ![1, 0, 0] * d4p a := by
  have f1 : G ![1, 1, 0] = G ![1, 0, 0] := by
    have h := ht ![1, 0, 0]
    rwa [show gDu gT⁻¹ ![1, 0, 0] = ![1, 1, 0] from by decide] at h
  have f2 : G ![1, 1, 1] = G ![1, 0, 1] := by
    have h := ht ![1, 0, 1]
    rwa [show gDu gT⁻¹ ![1, 0, 1] = ![1, 1, 1] from by decide] at h
  have f3 : G ![0, 1, 1] = G ![0, 1, 0] := by
    have h := hu ![0, 1, 0]
    rwa [show gDu gU⁻¹ ![0, 1, 0] = ![0, 1, 1] from by decide] at h
  have f4 : G ![1, 1, 1] = G ![1, 1, 0] := by
    have h := hu ![1, 1, 0]
    rwa [show gDu gU⁻¹ ![1, 1, 0] = ![1, 1, 1] from by decide] at h
  have hG111 : G ![1, 1, 1] = G ![1, 0, 0] := f4.trans f1
  have hG101 : G ![1, 0, 1] = G ![1, 0, 0] := f2.symm.trans hG111
  rw [h0, f1, hG111, hG101, f3] at hsum
  have key : ∀ g b c : ZMod 2, 0 + g + b + g + c + g + b + g = 0 → c = 0 := by decide
  have h001 : G ![0, 0, 1] = 0 := key _ _ _ hsum
  intro a
  rcases V3_cases a with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [d2p, d4p, h0, h001, f1, f3, hG111, hG101, zmod2_one_add_one]

private theorem I6 : ∀ a : V3, d2p (gDu gM1⁻¹ a) + d2p (gDu gM2⁻¹ a) = a 0 := by decide

private theorem I7 : ∀ a : V3, (d2p a + d4p a) + (d2p (gDu gM1⁻¹ a) + d4p (gDu gM1⁻¹ a)) =
    (if a = ![0, 0, 1] then 1 else 0) + (if a = ![0, 1, 0] then 1 else 0) := by
  decide +kernel

private theorem I8 : ∀ a : V3, d2p (gDu gP2⁻¹ a) =
    (if a = ![0, 0, 1] then 1 else 0) + (if a = ![0, 1, 0] then 1 else 0) := by
  decide

private theorem I8' : ∀ a : V3, (if gDu gP2⁻¹ a = ![0, 0, 1] then (1 : ZMod 2) else 0) +
    (if gDu gP2⁻¹ a = ![0, 1, 0] then 1 else 0) = d2p a := by
  decide

private theorem sndHom_d4p :
    sndHom (Multiplicative.ofAdd d4p) = linSndHom (Multiplicative.ofAdd ![1, 0, 0]) := by
  apply Multiplicative.toAdd.injective
  funext φ
  show d4p φ.1.2 = φ.1.2 ⬝ᵥ ![1, 0, 0]
  simp [d4p, dotProduct, Fin.sum_univ_three]

private theorem socleA3 (W : Subgroup MF) (hWi : ∀ g, ∀ u ∈ W, ρF g u ∈ W)
    (hw : linSndHom (Multiplicative.ofAdd ![1, 0, 0]) ∈ W) : K3F ≤ W := by
  intro k hk
  obtain ⟨v, -, rfl⟩ := Subgroup.mem_map.1 hk
  by_cases hv : Multiplicative.toAdd v = 0
  · have : v = 1 := by
      apply Multiplicative.toAdd.injective
      simpa using hv
    rw [this, map_one]
    exact W.one_mem
  · obtain ⟨g, hg⟩ := exists_gl_map ![1, 0, 0] (Multiplicative.toAdd v) (by decide) hv
    have hg' : gPt g ![1, 0, 0] = Multiplicative.toAdd v := hg
    have h := hWi g _ hw
    rw [ρF_linSnd, toAdd_ofAdd, hg', ofAdd_toAdd] at h
    exact h

private theorem socleB3 (W : Subgroup MF) (hWi : ∀ g, ∀ u ∈ W, ρF g u ∈ W)
    (hw : sndHom (Multiplicative.ofAdd d2p) ∈ W) :
    linSndHom (Multiplicative.ofAdd ![1, 0, 0]) ∈ W := by
  have h3 := W.mul_mem (hWi gM1 _ hw) (hWi gM2 _ hw)
  have e : ρF gM1 (sndHom (Multiplicative.ofAdd d2p)) * ρF gM2 (sndHom (Multiplicative.ofAdd d2p)) =
      linSndHom (Multiplicative.ofAdd ![1, 0, 0]) := by
    rw [ρF_snd, ρF_snd, ← map_mul]
    apply Multiplicative.toAdd.injective
    funext φ
    show d2p (gDu gM1⁻¹ φ.1.2) + d2p (gDu gM2⁻¹ φ.1.2) = φ.1.2 ⬝ᵥ ![1, 0, 0]
    rw [I6 φ.1.2]
    simp [dotProduct, Fin.sum_univ_three]
  rw [e] at h3
  exact h3

private theorem socleC3 (W : Subgroup MF) (hWi : ∀ g, ∀ u ∈ W, ρF g u ∈ W)
    (hw : sndHom (Multiplicative.ofAdd (fun a => d2p a + d4p a)) ∈ W) :
    sndHom (Multiplicative.ofAdd d2p) ∈ W := by
  have h2 := W.mul_mem hw (hWi gM1 _ hw)
  have e1 : sndHom (Multiplicative.ofAdd (fun a => d2p a + d4p a)) *
      ρF gM1 (sndHom (Multiplicative.ofAdd (fun a => d2p a + d4p a))) =
      sndHom (Multiplicative.ofAdd (fun a => (if a = ![0, 0, 1] then 1 else 0) +
        (if a = ![0, 1, 0] then 1 else 0))) := by
    rw [ρF_snd, ← map_mul]
    congr 1
    apply Multiplicative.toAdd.injective
    funext a
    exact I7 a
  rw [e1] at h2
  have h3 := hWi gP2 _ h2
  have e2 : ρF gP2 (sndHom (Multiplicative.ofAdd (fun a => (if a = ![0, 0, 1] then 1 else 0) +
        (if a = ![0, 1, 0] then 1 else 0)))) = sndHom (Multiplicative.ofAdd d2p) := by
    rw [ρF_snd]
    congr 1
    apply Multiplicative.toAdd.injective
    funext a
    exact I8' a
  rw [e2] at h3
  exact h3

private theorem socle_fun3 (W : Subgroup MF) (hWi : ∀ g, ∀ u ∈ W, ρF g u ∈ W) (β γ : ZMod 2)
    (hne : β ≠ 0 ∨ γ ≠ 0)
    (h : sndHom (Multiplicative.ofAdd (fun a => β * d2p a + γ * d4p a)) ∈ W) : K3F ≤ W := by
  apply socleA3 W hWi
  have hz : ∀ z : ZMod 2, z = 0 ∨ z = 1 := by decide
  rcases hz β with rfl | rfl <;> rcases hz γ with rfl | rfl
  · exact hne.elim (fun h => (h rfl).elim) (fun h => (h rfl).elim)
  · have e : sndHom (Multiplicative.ofAdd (fun a => (0 : ZMod 2) * d2p a + 1 * d4p a)) =
        linSndHom (Multiplicative.ofAdd ![1, 0, 0]) := by
      rw [← sndHom_d4p]
      congr 1
      apply Multiplicative.toAdd.injective
      funext a
      simp
    rw [e] at h
    exact h
  · have e : sndHom (Multiplicative.ofAdd (fun a => (1 : ZMod 2) * d2p a + 0 * d4p a)) =
        sndHom (Multiplicative.ofAdd d2p) := by
      congr 1
      apply Multiplicative.toAdd.injective
      funext a
      simp
    rw [e] at h
    exact socleB3 W hWi h
  · have e : sndHom (Multiplicative.ofAdd (fun a => (1 : ZMod 2) * d2p a + 1 * d4p a)) =
        sndHom (Multiplicative.ofAdd (fun a => d2p a + d4p a)) := by
      congr 1
      apply Multiplicative.toAdd.injective
      funext a
      simp
    rw [e] at h
    exact socleB3 W hWi (socleC3 W hWi h)

private theorem socle3 (W : Subgroup MF) (hWU : W ≤ U3F) (hWi : ∀ g, ∀ u ∈ W, ρF g u ∈ W)
    (hW : W ≠ ⊥) : K3F ≤ W := by
  obtain ⟨w, hwW, hw1, hfix⟩ := exists_fixed_pgroup ρF CFSG.ASVolI.B0 pgroupB0 W
    (fun g _ u hu => hWi g u hu) hW mf_sq
  obtain ⟨G, hG, hGw⟩ := Subgroup.mem_map.1 (hWU hwW)
  subst hGw
  obtain ⟨h0, hsum⟩ := (mem_coreV G).1 hG
  have hT : ∀ a, Multiplicative.toAdd G (gDu gT⁻¹ a) = Multiplicative.toAdd G a := by
    intro a
    have h := (ρF_snd gT G).symm.trans (hfix gT gT_mem)
    have h' := snd_inj _ _ (by simp [gDu_zero, h0]) h0 h
    exact congrFun (congrArg Multiplicative.toAdd h') a
  have hU : ∀ a, Multiplicative.toAdd G (gDu gU⁻¹ a) = Multiplicative.toAdd G a := by
    intro a
    have h := (ρF_snd gU G).symm.trans (hfix gU gU_mem)
    have h' := snd_inj _ _ (by simp [gDu_zero, h0]) h0 h
    exact congrFun (congrArg Multiplicative.toAdd h') a
  have hcl := I4d (Multiplicative.toAdd G) h0 ((sum_V3 _).symm.trans hsum) hT hU
  have hGeq : G = Multiplicative.ofAdd (fun a => Multiplicative.toAdd G ![0, 1, 0] * d2p a +
      Multiplicative.toAdd G ![1, 0, 0] * d4p a) := by
    apply Multiplicative.toAdd.injective
    funext a
    simp only [toAdd_ofAdd]
    exact hcl a
  rw [hGeq] at hwW
  refine socle_fun3 W hWi _ _ ?_ hwW
  by_contra hcon
  push_neg at hcon
  apply hw1
  rw [hGeq, hcon.1, hcon.2]
  apply Multiplicative.toAdd.injective
  funext a
  simp [sndAdd] <;> rfl

end FlagH62


namespace FlagH62

open CFSG.ASVolI.ChH Matrix

private theorem pairF_comm (f g : Fl → ZMod 2) : pairF f g = pairF g f := by
  unfold pairF
  exact Finset.sum_congr rfl (fun φ _ => mul_comm _ _)

private theorem pairF_add_left (f g h : Fl → ZMod 2) :
    pairF (fun φ => f φ + g φ) h = pairF f h + pairF g h := by
  unfold pairF
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun φ _ => add_mul _ _ _)

private theorem conn_pt : ∀ x x' : V3, x ≠ 0 → x' ≠ 0 →
    ∃ a : V3, a ≠ 0 ∧ a ⬝ᵥ x = 0 ∧ a ⬝ᵥ x' = 0 := by
  decide +kernel

private theorem psi_X_zero : ∀ X : Matrix (Fin 3) (Fin 3) (ZMod 2), X.trace = 0 →
    (∀ j : Fin 8, pairF (steinAdd X) (steinAdd (bas j)) = 0) → X = 0 := by
  decide +kernel

private theorem key7 : ∀ d : ZMod 2, 0 + d + d + d + d + d + d + d = 0 → d = 0 := by decide

private theorem psi_inj_core (c : ZMod 2) (F G : V3 → ZMod 2) (hF0 : F 0 = 0) (hG0 : G 0 = 0)
    (hFs : F 0 + F ![1, 0, 0] + F ![0, 1, 0] + F ![1, 1, 0] + F ![0, 0, 1] + F ![1, 0, 1] +
      F ![0, 1, 1] + F ![1, 1, 1] = 0)
    (hGs : G 0 + G ![1, 0, 0] + G ![0, 1, 0] + G ![1, 1, 0] + G ![0, 0, 1] + G ![1, 0, 1] +
      G ![0, 1, 1] + G ![1, 1, 1] = 0)
    (X : Matrix (Fin 3) (Fin 3) (ZMod 2)) (hX : X.trace = 0)
    (h : ∀ φ : Fl, c + F φ.1.1 + G φ.1.2 + steinAdd X φ = 0) :
    c = 0 ∧ (∀ v, F v = 0) ∧ (∀ a, G a = 0) ∧ X = 0 := by
  have hsX : ∀ φ : Fl, steinAdd X φ = c + F φ.1.1 + G φ.1.2 := by
    intro φ
    have h1 := h φ
    have h2 : steinAdd X φ + (c + F φ.1.1 + G φ.1.2) = 0 := by
      linear_combination h1
    have h3 := eq_neg_of_add_eq_zero_left h2
    rw [h3]
    have hneg : ∀ z : ZMod 2, -z = z := by decide
    rw [hneg]
  have hX0 : X = 0 := by
    apply psi_X_zero X hX
    intro j
    have hpair : pairF (steinAdd X) (steinAdd (bas j)) =
        pairF (fun φ => c + F φ.1.1 + G φ.1.2) (steinAdd (bas j)) := by
      unfold pairF
      exact Finset.sum_congr rfl (fun φ _ => by rw [hsX φ])
    have z1 : pairF (fun _ => c) (steinAdd (bas j)) = 0 := by
      rw [pairF_comm]
      exact pair_stein_fst (bas j) (fun _ => c)
    have z2 : pairF (fun φ => F φ.1.1) (steinAdd (bas j)) = 0 := by
      rw [pairF_comm]
      exact pair_stein_fst (bas j) F
    have z3 : pairF (fun φ => G φ.1.2) (steinAdd (bas j)) = 0 := by
      rw [pairF_comm]
      exact pair_stein_snd (bas j) G
    rw [hpair, pairF_add_left, pairF_add_left, z1, z2, z3, add_zero, add_zero]
  subst hX0
  have hs0 : ∀ φ : Fl, steinAdd (0 : Matrix (Fin 3) (Fin 3) (ZMod 2)) φ = 0 := by
    intro φ
    rw [steinAdd_apply]
    simp
  have h0 : ∀ φ : Fl, c + F φ.1.1 + G φ.1.2 = 0 := by
    intro φ
    have := h φ
    rwa [hs0 φ, add_zero] at this
  have hneg : ∀ z : ZMod 2, -z = z := by decide
  have hF : ∀ x : V3, x ≠ 0 → F x = F ![1, 0, 0] := by
    intro x hx
    have he1 : (![1, 0, 0] : V3) ≠ 0 := by decide
    obtain ⟨a, ha, hax, ha1⟩ := conn_pt x ![1, 0, 0] hx he1
    have h1 : c + F x + G a = 0 := h0 ⟨(x, a), hx, ha, hax⟩
    have h2 : c + F ![1, 0, 0] + G a = 0 := h0 ⟨(![1, 0, 0], a), he1, ha, ha1⟩
    linear_combination h1 - h2
  have hd : F ![1, 0, 0] = 0 := by
    rw [hF0, hF ![0, 1, 0] (by decide), hF ![1, 1, 0] (by decide), hF ![0, 0, 1] (by decide),
      hF ![1, 0, 1] (by decide), hF ![0, 1, 1] (by decide), hF ![1, 1, 1] (by decide)] at hFs
    exact key7 _ hFs
  have hFv : ∀ v, F v = 0 := by
    intro v
    by_cases hv : v = 0
    · rw [hv, hF0]
    · rw [hF v hv, hd]
  have hG : ∀ a : V3, a ≠ 0 → G a = c := by
    intro a ha
    obtain ⟨x, hx, hxa⟩ := dual_has_pt a ha
    have h1 : c + F x + G a = 0 := h0 ⟨(x, a), hx, ha, hxa⟩
    rw [hFv x, add_zero] at h1
    have hG' : G a + c = 0 := by
      rw [add_comm]
      exact h1
    have h2 : G a = -c := eq_neg_of_add_eq_zero_left hG'
    rw [h2, hneg]
  have hc : c = 0 := by
    rw [hG0, hG ![1, 0, 0] (by decide), hG ![0, 1, 0] (by decide), hG ![1, 1, 0] (by decide),
      hG ![0, 0, 1] (by decide), hG ![1, 0, 1] (by decide), hG ![0, 1, 1] (by decide),
      hG ![1, 1, 1] (by decide)] at hGs
    exact key7 c hGs
  have hGv : ∀ a, G a = 0 := by
    intro a
    by_cases ha : a = 0
    · rw [ha, hG0]
    · rw [hG a ha, hc]
  exact ⟨hc, hFv, hGv, rfl⟩

end FlagH62

namespace FlagH62

open CFSG.ASVolI.ChH Matrix

private abbrev Dom : Type := Multiplicative (ZMod 2) × (↥coreV) × (↥coreV) × (↥Adj3)

private def phi (p : Dom) : MF :=
  constHom p.1 * fstHom (p.2.1 : Multiplicative (V3 → ZMod 2)) *
    sndHom (p.2.2.1 : Multiplicative (V3 → ZMod 2)) * steinHom (p.2.2.2 : AdjAmb)

private theorem phi_apply (p : Dom) (φ : Fl) :
    Multiplicative.toAdd (phi p) φ = Multiplicative.toAdd p.1 +
      Multiplicative.toAdd (p.2.1 : Multiplicative (V3 → ZMod 2)) φ.1.1 +
      Multiplicative.toAdd (p.2.2.1 : Multiplicative (V3 → ZMod 2)) φ.1.2 +
      steinAdd (Multiplicative.toAdd (p.2.2.2 : AdjAmb)) φ := rfl

private theorem phi_one : phi 1 = 1 := by
  apply Multiplicative.toAdd.injective
  funext φ
  rw [phi_apply]
  simp

private theorem phi_injective : Function.Injective phi := by
  rintro ⟨c₁, ⟨F₁, hF₁⟩, ⟨G₁, hG₁⟩, ⟨X₁, hX₁⟩⟩ ⟨c₂, ⟨F₂, hF₂⟩, ⟨G₂, hG₂⟩, ⟨X₂, hX₂⟩⟩ h
  have hpt : ∀ φ : Fl, Multiplicative.toAdd c₁ +
      Multiplicative.toAdd F₁ φ.1.1 + Multiplicative.toAdd G₁ φ.1.2 +
      steinAdd (Multiplicative.toAdd X₁) φ =
      Multiplicative.toAdd c₂ + Multiplicative.toAdd F₂ φ.1.1 +
      Multiplicative.toAdd G₂ φ.1.2 + steinAdd (Multiplicative.toAdd X₂) φ := by
    intro φ
    have := congrArg (fun f : MF => Multiplicative.toAdd f φ) h
    simpa only [phi_apply] using this
  have hF₁' := (mem_coreV F₁).1 hF₁
  have hF₂' := (mem_coreV F₂).1 hF₂
  have hG₁' := (mem_coreV G₁).1 hG₁
  have hG₂' := (mem_coreV G₂).1 hG₂
  have hX₁' := (mem_Adj3_iff X₁).1 hX₁
  have hX₂' := (mem_Adj3_iff X₂).1 hX₂
  have hsF := (sum_V3 (Multiplicative.toAdd F₁)).symm.trans hF₁'.2
  have hsF2 := (sum_V3 (Multiplicative.toAdd F₂)).symm.trans hF₂'.2
  have hsG := (sum_V3 (Multiplicative.toAdd G₁)).symm.trans hG₁'.2
  have hsG2 := (sum_V3 (Multiplicative.toAdd G₂)).symm.trans hG₂'.2
  obtain ⟨hc, hF0, hG0, hX0⟩ := psi_inj_core (Multiplicative.toAdd c₁ - Multiplicative.toAdd c₂)
    (fun v => Multiplicative.toAdd F₁ v - Multiplicative.toAdd F₂ v)
    (fun v => Multiplicative.toAdd G₁ v - Multiplicative.toAdd G₂ v)
    (by simp [hF₁'.1, hF₂'.1]) (by simp [hG₁'.1, hG₂'.1])
    (by simp only [sub_eq_add_neg]; linear_combination hsF - hsF2)
    (by simp only [sub_eq_add_neg]; linear_combination hsG - hsG2)
    (Multiplicative.toAdd X₁ - Multiplicative.toAdd X₂)
    (by
      have htr : ∀ A B : Matrix (Fin 3) (Fin 3) (ZMod 2), (A - B).trace = A.trace - B.trace :=
        fun A B => map_sub (Matrix.traceAddMonoidHom (Fin 3) (ZMod 2)) A B
      rw [htr]
      simp [hX₁', hX₂'])
    (by
      intro φ
      rw [map_sub]
      simp only [Pi.sub_apply]
      refine Eq.trans ?_ (sub_eq_zero.2 (hpt φ))
      abel)
  have hc' : Multiplicative.toAdd c₁ = Multiplicative.toAdd c₂ := sub_eq_zero.1 hc
  have hF' : Multiplicative.toAdd F₁ = Multiplicative.toAdd F₂ :=
    funext fun v => sub_eq_zero.1 (hF0 v)
  have hG' : Multiplicative.toAdd G₁ = Multiplicative.toAdd G₂ :=
    funext fun v => sub_eq_zero.1 (hG0 v)
  have hX' : Multiplicative.toAdd X₁ = Multiplicative.toAdd X₂ := sub_eq_zero.1 hX0
  have e1 : c₁ = c₂ := Multiplicative.toAdd.injective hc'
  have e2 : (⟨F₁, hF₁⟩ : ↥coreV) = ⟨F₂, hF₂⟩ := Subtype.ext (Multiplicative.toAdd.injective hF')
  have e3 : (⟨G₁, hG₁⟩ : ↥coreV) = ⟨G₂, hG₂⟩ := Subtype.ext (Multiplicative.toAdd.injective hG')
  have e4 : (⟨X₁, hX₁⟩ : ↥Adj3) = ⟨X₂, hX₂⟩ := Subtype.ext (Multiplicative.toAdd.injective hX')
  rw [e1, e2, e3, e4]

private theorem card_mul_zmod2 : Nat.card (Multiplicative (ZMod 2)) = 2 := by
  rw [show Nat.card (Multiplicative (ZMod 2)) = Nat.card (ZMod 2) from rfl, Nat.card_zmod]

private theorem card_MF : Nat.card MF = 2 ^ 21 := by
  rw [show Nat.card MF = Nat.card (Fl → ZMod 2) from rfl, Nat.card_fun, Nat.card_zmod,
    Nat.card_eq_fintype_card (α := Fl), card_Fl]

private theorem card_sl3 :
    Fintype.card {X : Matrix (Fin 3) (Fin 3) (ZMod 2) // X.trace = 0} = 256 := by
  decide +kernel

private theorem card_Adj3 : Nat.card ↥Adj3 = 256 := by
  rw [← card_sl3, ← Nat.card_eq_fintype_card]
  apply Nat.card_congr
  exact
    { toFun := fun x => ⟨Multiplicative.toAdd (x : AdjAmb), (mem_Adj3_iff _).1 x.2⟩
      invFun := fun y => ⟨Multiplicative.ofAdd y.1, (mem_Adj3_iff _).2 (by simpa using y.2)⟩
      left_inv := fun x => by apply Subtype.ext; rfl
      right_inv := fun y => by apply Subtype.ext; rfl }

private def psiAdd : (V3 → ZMod 2) →+ ZMod 2 × ZMod 2 :=
  (Pi.evalAddMonoidHom (fun _ : V3 => ZMod 2) 0).prod
    (∑ v : V3, Pi.evalAddMonoidHom (fun _ : V3 => ZMod 2) v)

private def psiHom : Multiplicative (V3 → ZMod 2) →* Multiplicative (ZMod 2 × ZMod 2) :=
  AddMonoidHom.toMultiplicative psiAdd

private theorem psiHom_apply (F : Multiplicative (V3 → ZMod 2)) :
    psiHom F =
      Multiplicative.ofAdd (Multiplicative.toAdd F 0, ∑ v : V3, Multiplicative.toAdd F v) := by
  apply Multiplicative.toAdd.injective
  simp [psiHom, psiAdd, AddMonoidHom.finset_sum_apply]

private theorem psiHom_surj : Function.Surjective psiHom := by
  rintro y
  obtain ⟨⟨a, b⟩, rfl⟩ : ∃ p : ZMod 2 × ZMod 2, y = Multiplicative.ofAdd p :=
    ⟨Multiplicative.toAdd y, rfl⟩
  have hsumF : ∀ a b : ZMod 2,
      ∑ v : V3, (if v = 0 then a else if v = ![1, 0, 0] then a + b else 0) = b := by
    decide
  refine ⟨Multiplicative.ofAdd
    (fun v : V3 => if v = 0 then a else if v = ![1, 0, 0] then a + b else 0), ?_⟩
  rw [psiHom_apply]
  apply Multiplicative.toAdd.injective
  simp only [toAdd_ofAdd]
  exact Prod.ext (by simp) (hsumF a b)

private theorem card_coreV : Nat.card ↥coreV = 64 := by
  have hker : psiHom.ker = coreV := by
    ext F
    rw [MonoidHom.mem_ker, mem_coreV, psiHom_apply]
    constructor
    · intro h
      have h' := congrArg Multiplicative.toAdd h
      simp only [toAdd_ofAdd, toAdd_one, Prod.mk_eq_zero] at h'
      exact h'
    · rintro ⟨h1, h2⟩
      rw [h1, h2]
      rfl
  have h := Subgroup.card_ker_mul_card_of_surjective psiHom_surj
  rw [hker] at h
  have hG : Nat.card (Multiplicative (V3 → ZMod 2)) = 256 := by
    rw [show Nat.card (Multiplicative (V3 → ZMod 2)) = Nat.card (V3 → ZMod 2) from rfl,
      Nat.card_fun, Nat.card_zmod, show Nat.card V3 = 8 by simp [Nat.card_fun]]
    norm_num
  have hG' : Nat.card (Multiplicative (ZMod 2 × ZMod 2)) = 4 := by
    rw [show Nat.card (Multiplicative (ZMod 2 × ZMod 2)) = Nat.card (ZMod 2 × ZMod 2) from rfl,
      Nat.card_prod, Nat.card_zmod]
  rw [hG, hG'] at h
  omega

private theorem sup3_decomp {A B C : Subgroup MF} {x : MF} (h : x ∈ A ⊔ B ⊔ C) :
    ∃ a ∈ A, ∃ b ∈ B, ∃ c ∈ C, a * b * c = x := by
  obtain ⟨y, hy, c, hc, rfl⟩ := Subgroup.mem_sup.1 h
  obtain ⟨a, ha, b, hb, rfl⟩ := Subgroup.mem_sup.1 hy
  exact ⟨a, ha, b, hb, c, hc, rfl⟩

private theorem phi_eq (c : Multiplicative (ZMod 2)) (F : ↥coreV) (G : ↥coreV) (X : ↥Adj3) :
    phi (c, F, G, X) = constHom c * fstHom (F : Multiplicative (V3 → ZMod 2)) *
      sndHom (G : Multiplicative (V3 → ZMod 2)) * steinHom (X : AdjAmb) := rfl

private theorem phi_eq_one_iff (p : Dom) : phi p = 1 ↔ p = 1 := by
  constructor
  · intro h
    apply phi_injective
    rw [h, phi_one]
  · rintro rfl
    exact phi_one

private theorem dsum_inter1 : U1F ⊓ (U2F ⊔ U3F ⊔ U4F) = ⊥ := by
  apply eq_bot_iff.2
  rintro x ⟨hx1, hx2⟩
  obtain ⟨c, -, rfl⟩ := Subgroup.mem_map.1 hx1
  obtain ⟨a, ha, b, hb, d, hd, hab⟩ := sup3_decomp hx2
  obtain ⟨F, hF, rfl⟩ := Subgroup.mem_map.1 ha
  obtain ⟨G, hG, rfl⟩ := Subgroup.mem_map.1 hb
  obtain ⟨X, hX, rfl⟩ := Subgroup.mem_map.1 hd
  have key : phi (c, ⟨F, hF⟩, ⟨G, hG⟩, ⟨X, hX⟩) = 1 := by
    rw [phi_eq]
    calc constHom c * fstHom F * sndHom G * steinHom X
        = constHom c * (fstHom F * sndHom G * steinHom X) := by ac_rfl
      _ = constHom c * constHom c := by rw [hab]
      _ = 1 := by rw [← pow_two]; exact mf_sq _
  have hc : c = 1 := by
    have := (phi_eq_one_iff _).1 key
    exact congrArg Prod.fst this
  rw [hc, map_one, Subgroup.mem_bot]

private theorem dsum_inter2 : U2F ⊓ (U1F ⊔ U3F ⊔ U4F) = ⊥ := by
  apply eq_bot_iff.2
  rintro x ⟨hx2, hx1⟩
  obtain ⟨F, hF, rfl⟩ := Subgroup.mem_map.1 hx2
  obtain ⟨a, ha, b, hb, d, hd, hab⟩ := sup3_decomp hx1
  obtain ⟨c, -, rfl⟩ := Subgroup.mem_map.1 ha
  obtain ⟨G, hG, rfl⟩ := Subgroup.mem_map.1 hb
  obtain ⟨X, hX, rfl⟩ := Subgroup.mem_map.1 hd
  have key : phi (c, ⟨F, hF⟩, ⟨G, hG⟩, ⟨X, hX⟩) = 1 := by
    rw [phi_eq]
    calc constHom c * fstHom F * sndHom G * steinHom X
        = (constHom c * sndHom G * steinHom X) * fstHom F := by ac_rfl
      _ = fstHom F * fstHom F := by rw [hab]
      _ = 1 := by rw [← pow_two]; exact mf_sq _
  have hF1 : F = 1 :=
    congrArg Subtype.val (congrArg (fun p : Dom => p.2.1) ((phi_eq_one_iff _).1 key))
  rw [hF1, map_one, Subgroup.mem_bot]

private theorem dsum_inter3 : U3F ⊓ (U1F ⊔ U2F ⊔ U4F) = ⊥ := by
  apply eq_bot_iff.2
  rintro x ⟨hx3, hx1⟩
  obtain ⟨G, hG, rfl⟩ := Subgroup.mem_map.1 hx3
  obtain ⟨a, ha, b, hb, d, hd, hab⟩ := sup3_decomp hx1
  obtain ⟨c, -, rfl⟩ := Subgroup.mem_map.1 ha
  obtain ⟨F, hF, rfl⟩ := Subgroup.mem_map.1 hb
  obtain ⟨X, hX, rfl⟩ := Subgroup.mem_map.1 hd
  have key : phi (c, ⟨F, hF⟩, ⟨G, hG⟩, ⟨X, hX⟩) = 1 := by
    rw [phi_eq]
    calc constHom c * fstHom F * sndHom G * steinHom X
        = sndHom G * (constHom c * fstHom F * steinHom X) := by ac_rfl
      _ = sndHom G * sndHom G := by rw [hab]
      _ = 1 := by rw [← pow_two]; exact mf_sq _
  have hG1 : G = 1 :=
    congrArg Subtype.val (congrArg (fun p : Dom => p.2.2.1) ((phi_eq_one_iff _).1 key))
  rw [hG1, map_one, Subgroup.mem_bot]

private theorem dsum_inter4 : U4F ⊓ (U1F ⊔ U2F ⊔ U3F) = ⊥ := by
  apply eq_bot_iff.2
  rintro x ⟨hx4, hx1⟩
  obtain ⟨X, hX, rfl⟩ := Subgroup.mem_map.1 hx4
  obtain ⟨a, ha, b, hb, d, hd, hab⟩ := sup3_decomp hx1
  obtain ⟨c, -, rfl⟩ := Subgroup.mem_map.1 ha
  obtain ⟨F, hF, rfl⟩ := Subgroup.mem_map.1 hb
  obtain ⟨G, hG, rfl⟩ := Subgroup.mem_map.1 hd
  have key : phi (c, ⟨F, hF⟩, ⟨G, hG⟩, ⟨X, hX⟩) = 1 := by
    rw [phi_eq]
    calc constHom c * fstHom F * sndHom G * steinHom X
        = steinHom X * (constHom c * fstHom F * sndHom G) := by ac_rfl
      _ = steinHom X * steinHom X := by rw [hab]
      _ = 1 := by rw [← pow_two]; exact mf_sq _
  have hX1 : X = 1 :=
    congrArg Subtype.val (congrArg (fun p : Dom => p.2.2.2) ((phi_eq_one_iff _).1 key))
  rw [hX1, map_one, Subgroup.mem_bot]

private theorem phi_surjective : Function.Surjective phi := by
  have hc : Nat.card MF ≤ Nat.card Dom := by
    rw [card_MF]
    simp only [Dom, Nat.card_prod, card_mul_zmod2, card_coreV, card_Adj3]
    norm_num
  exact (phi_injective.bijective_of_nat_card_le hc).2

private theorem dsum_top : U1F ⊔ U2F ⊔ U3F ⊔ U4F = ⊤ := by
  rw [eq_top_iff]
  intro f _
  obtain ⟨⟨c, ⟨F, hF⟩, ⟨G, hG⟩, ⟨X, hX⟩⟩, rfl⟩ := phi_surjective f
  have h1 : constHom c ∈ U1F := Subgroup.mem_map.2 ⟨c, Subgroup.mem_top _, rfl⟩
  have h2 : fstHom F ∈ U2F := Subgroup.mem_map.2 ⟨F, hF, rfl⟩
  have h3 : sndHom G ∈ U3F := Subgroup.mem_map.2 ⟨G, hG, rfl⟩
  have h4 : steinHom X ∈ U4F := Subgroup.mem_map.2 ⟨X, hX, rfl⟩
  rw [phi_eq]
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _
    (Subgroup.mem_sup_left (Subgroup.mem_sup_left (Subgroup.mem_sup_left h1)))
    (Subgroup.mem_sup_left (Subgroup.mem_sup_left (Subgroup.mem_sup_right h2))))
    (Subgroup.mem_sup_left (Subgroup.mem_sup_right h3))) (Subgroup.mem_sup_right h4)


private def mkGL (M N : Matrix (Fin 3) (Fin 3) (ZMod 2)) (h1 : M * N = 1) (h2 : N * M = 1) :
    GL (Fin 3) (ZMod 2) :=
  ⟨M, N, h1, h2⟩

private theorem sl3_fixed_B0' : ∀ X : Matrix (Fin 3) (Fin 3) (ZMod 2), X.trace = 0 →
    !![1, 1, 0; 0, 1, 0; 0, 0, 1] * X * !![1, 1, 0; 0, 1, 0; 0, 0, 1] = X →
    !![1, 0, 0; 0, 1, 1; 0, 0, 1] * X * !![1, 0, 0; 0, 1, 1; 0, 0, 1] = X →
    X = 0 ∨ X = bas 4 := by
  decide +kernel

private theorem stein_zero_imp (Z : Matrix (Fin 3) (Fin 3) (ZMod 2)) (hZ : Z.trace = 0)
    (h : steinAdd Z = 0) : Z = 0 := by
  apply psi_X_zero Z hZ
  intro j
  rw [h]
  simp [pairF]

private theorem stein_inj_adj (X Y : AdjAmb) (hX : X ∈ Adj3) (hY : Y ∈ Adj3)
    (h : steinHom X = steinHom Y) : X = Y := by
  have hZ : (Multiplicative.toAdd X - Multiplicative.toAdd Y).trace = 0 := by
    have htr : ∀ A B : Matrix (Fin 3) (Fin 3) (ZMod 2), (A - B).trace = A.trace - B.trace :=
      fun A B => map_sub (Matrix.traceAddMonoidHom (Fin 3) (ZMod 2)) A B
    rw [htr, (mem_Adj3_iff X).1 hX, (mem_Adj3_iff Y).1 hY]
    simp
  have h' : steinAdd (Multiplicative.toAdd X) = steinAdd (Multiplicative.toAdd Y) :=
    congrArg Multiplicative.toAdd h
  have hs : steinAdd (Multiplicative.toAdd X - Multiplicative.toAdd Y) = 0 := by
    rw [map_sub, h']
    exact sub_self _
  have := stein_zero_imp _ hZ hs
  apply Multiplicative.toAdd.injective
  exact sub_eq_zero.1 this

private theorem stein_conj_mem (W : Subgroup MF) (hWi : ∀ g, ∀ u ∈ W, ρF g u ∈ W)
    (M N : Matrix (Fin 3) (Fin 3) (ZMod 2)) (h1 : M * N = 1) (h2 : N * M = 1)
    (hmem : steinHom (Multiplicative.ofAdd (bas 4)) ∈ W) (B : Matrix (Fin 3) (Fin 3) (ZMod 2))
    (hB : M * bas 4 * N = B) : steinHom (Multiplicative.ofAdd B) ∈ W := by
  have h := hWi (mkGL M N h1 h2) _ hmem
  rw [ρF_stein] at h
  have e : adjAmbAct (mkGL M N h1 h2) (Multiplicative.ofAdd (bas 4)) = Multiplicative.ofAdd B :=
    congrArg Multiplicative.ofAdd hB
  rwa [e] at h


set_option maxHeartbeats 1000000 in
private theorem stein_basis_mem (W : Subgroup MF) (hWi : ∀ g, ∀ u ∈ W, ρF g u ∈ W)
    (hwW : steinHom (Multiplicative.ofAdd (bas 4)) ∈ W) :
    ∀ i : Fin 8, steinHom (Multiplicative.ofAdd (bas i)) ∈ W := by
  have m0 : steinHom (Multiplicative.ofAdd (bas 0)) ∈ W :=
    stein_conj_mem W hWi !![1, 0, 0; 0, 0, 1; 0, 1, 0] !![1, 0, 0; 0, 0, 1; 0, 1, 0]
      (by decide) (by decide) hwW (bas 0) (by decide)
  have m1 : steinHom (Multiplicative.ofAdd (bas 1)) ∈ W :=
    stein_conj_mem W hWi !![0, 0, 1; 1, 0, 0; 0, 1, 0] !![0, 1, 0; 0, 0, 1; 1, 0, 0]
      (by decide) (by decide) hwW (bas 1) (by decide)
  have m2 : steinHom (Multiplicative.ofAdd (bas 2)) ∈ W :=
    stein_conj_mem W hWi !![0, 1, 0; 1, 0, 0; 0, 0, 1] !![0, 1, 0; 1, 0, 0; 0, 0, 1]
      (by decide) (by decide) hwW (bas 2) (by decide)
  have m3 : steinHom (Multiplicative.ofAdd (bas 3)) ∈ W :=
    stein_conj_mem W hWi !![0, 1, 0; 0, 0, 1; 1, 0, 0] !![0, 0, 1; 1, 0, 0; 0, 1, 0]
      (by decide) (by decide) hwW (bas 3) (by decide)
  have m4 : steinHom (Multiplicative.ofAdd (bas 4)) ∈ W := hwW
  have m5 : steinHom (Multiplicative.ofAdd (bas 5)) ∈ W :=
    stein_conj_mem W hWi !![0, 0, 1; 0, 1, 0; 1, 0, 0] !![0, 0, 1; 0, 1, 0; 1, 0, 0]
      (by decide) (by decide) hwW (bas 5) (by decide)
  have m6 : steinHom (Multiplicative.ofAdd (bas 6)) ∈ W :=
    stein_conj_mem W hWi !![1, 0, 0; 1, 0, 1; 0, 1, 0] !![1, 0, 0; 0, 0, 1; 1, 1, 0]
      (by decide) (by decide) hwW (bas 6) (by decide)
  have m7 : steinHom (Multiplicative.ofAdd (bas 7)) ∈ W :=
    stein_conj_mem W hWi !![0, 1, 0; 1, 0, 0; 1, 0, 1] !![0, 1, 0; 1, 0, 0; 0, 1, 1]
      (by decide) (by decide) hwW (bas 7) (by decide)
  intro i
  fin_cases i
  exacts [m0, m1, m2, m3, m4, m5, m6, m7]

private theorem U4_simple (W : Subgroup MF) (hWU : W ≤ U4F) (hWi : ∀ g, ∀ u ∈ W, ρF g u ∈ W)
    (hW : W ≠ ⊥) : U4F ≤ W := by
  obtain ⟨w, hwW, hw1, hfix⟩ := exists_fixed_pgroup ρF CFSG.ASVolI.B0 pgroupB0 W
    (fun g _ u hu => hWi g u hu) hW mf_sq
  obtain ⟨X, hX, hXw⟩ := Subgroup.mem_map.1 (hWU hwW)
  subst hXw
  have hfT : steinHom (adjAmbAct gT X) = steinHom X :=
    (ρF_stein gT X).symm.trans (hfix gT gT_mem)
  have hfU : steinHom (adjAmbAct gU X) = steinHom X :=
    (ρF_stein gU X).symm.trans (hfix gU gU_mem)
  have hXT : adjAmbAct gT X = X := stein_inj_adj _ _ (adjAmbAct_mem gT X hX) hX hfT
  have hXU : adjAmbAct gU X = X := stein_inj_adj _ _ (adjAmbAct_mem gU X hX) hX hfU
  have hT' : !![1, 1, 0; 0, 1, 0; 0, 0, 1] * Multiplicative.toAdd X *
      !![1, 1, 0; 0, 1, 0; 0, 0, 1] = Multiplicative.toAdd X :=
    congrArg Multiplicative.toAdd hXT
  have hU' : !![1, 0, 0; 0, 1, 1; 0, 0, 1] * Multiplicative.toAdd X *
      !![1, 0, 0; 0, 1, 1; 0, 0, 1] = Multiplicative.toAdd X :=
    congrArg Multiplicative.toAdd hXU
  rcases sl3_fixed_B0' (Multiplicative.toAdd X) ((mem_Adj3_iff X).1 hX) hT' hU' with h0 | hb
  · exfalso
    apply hw1
    have hX1 : X = 1 := by
      apply Multiplicative.toAdd.injective
      rw [h0]
      rfl
    rw [hX1]
    exact map_one steinHom
  · have hXb : X = Multiplicative.ofAdd (bas 4) := by
      rw [← hb, ofAdd_toAdd]
    subst hXb
    have hall := stein_basis_mem W hWi hwW
    intro Y hY
    obtain ⟨Z, hZ, rfl⟩ := Subgroup.mem_map.1 hY
    have hdec := sl3_decomp (Multiplicative.toAdd Z) ((mem_Adj3_iff Z).1 hZ)
    have hZeq : Z = Multiplicative.ofAdd (∑ i ∈ Finset.univ.filter
        (fun i => coefX (Multiplicative.toAdd Z) i = 1), bas i) := by
      rw [← hdec, ofAdd_toAdd]
    rw [hZeq, ofAdd_sum, map_prod]
    exact Subgroup.prod_mem W (fun i _ => hall i)

end FlagH62


namespace FlagH62

open CFSG.ASVolI.ChH Matrix

private def gEquiv (g : GL (Fin 3) (ZMod 2)) : V3 ≃ V3 where
  toFun := gPt g
  invFun := gPt g⁻¹
  left_inv v := by
    show gPt g⁻¹ (gPt g v) = v
    rw [← gPt_mul, inv_mul_cancel, gPt_one]
  right_inv v := by
    show gPt g (gPt g⁻¹ v) = v
    rw [← gPt_mul, mul_inv_cancel, gPt_one]

private def gDuEquiv (g : GL (Fin 3) (ZMod 2)) : V3 ≃ V3 where
  toFun := gDu g
  invFun := gDu g⁻¹
  left_inv a := by
    show gDu g⁻¹ (gDu g a) = a
    rw [← gDu_mul, inv_mul_cancel, gDu_one]
  right_inv a := by
    show gDu g (gDu g⁻¹ a) = a
    rw [← gDu_mul, mul_inv_cancel, gDu_one]

private theorem gPt_smul_vec (g : GL (Fin 3) (ZMod 2)) (c : ZMod 2) (v : V3) :
    gPt g (c • v) = c • gPt g v := by
  unfold gPt
  rw [Matrix.mulVec_smul]

private theorem gPt_sum (g : GL (Fin 3) (ZMod 2)) {ι : Type*} (s : Finset ι) (f : ι → V3) :
    gPt g (∑ i ∈ s, f i) = ∑ i ∈ s, gPt g (f i) := by
  unfold gPt
  rw [Matrix.mulVec_sum]

private theorem gDu_smul_vec (g : GL (Fin 3) (ZMod 2)) (c : ZMod 2) (a : V3) :
    gDu g (c • a) = c • gDu g a := by
  unfold gDu
  rw [Matrix.mulVec_smul]

private theorem gDu_sum (g : GL (Fin 3) (ZMod 2)) {ι : Type*} (s : Finset ι) (f : ι → V3) :
    gDu g (∑ i ∈ s, f i) = ∑ i ∈ s, gDu g (f i) := by
  unfold gDu
  rw [Matrix.mulVec_sum]

private def betaV (F : V3 → ZMod 2) : V3 := ∑ v : V3, F v • v

private def betaD (G : V3 → ZMod 2) : V3 := ∑ a : V3, G a • a

private theorem betaV_comp (g : GL (Fin 3) (ZMod 2)) (F : V3 → ZMod 2) :
    betaV (fun v => F (gPt g⁻¹ v)) = gPt g (betaV F) := by
  unfold betaV
  rw [gPt_sum]
  rw [← Equiv.sum_comp (gEquiv g)]
  apply Finset.sum_congr rfl
  intro w _
  show F (gPt g⁻¹ (gPt g w)) • gPt g w = gPt g (F w • w)
  rw [gPt_smul_vec]
  congr 2
  show gPt g⁻¹ (gPt g w) = w
  rw [← gPt_mul, inv_mul_cancel, gPt_one]

private theorem betaD_comp (g : GL (Fin 3) (ZMod 2)) (G : V3 → ZMod 2) :
    betaD (fun a => G (gDu g⁻¹ a)) = gDu g (betaD G) := by
  unfold betaD
  rw [gDu_sum]
  rw [← Equiv.sum_comp (gDuEquiv g)]
  apply Finset.sum_congr rfl
  intro w _
  show G (gDu g⁻¹ (gDu g w)) • gDu g w = gDu g (G w • w)
  rw [gDu_smul_vec]
  congr 2
  show gDu g⁻¹ (gDu g w) = w
  rw [← gDu_mul, inv_mul_cancel, gDu_one]

private theorem key7_lin : ∀ f1 f2 f3 f12 f13 f23 f123 : ZMod 2,
    f1 + f2 + f3 + f12 + f13 + f23 + f123 = 0 →
    f1 + f12 + f13 + f123 = 0 → f2 + f12 + f23 + f123 = 0 → f3 + f13 + f23 + f123 = 0 →
    f12 = f1 + f2 ∧ f13 = f1 + f3 ∧ f23 = f2 + f3 ∧ f123 = f1 + f2 + f3 := by
  decide +kernel

private theorem beta_zero_linear (F : V3 → ZMod 2) (h0 : F 0 = 0)
    (hs : F 0 + F ![1, 0, 0] + F ![0, 1, 0] + F ![1, 1, 0] + F ![0, 0, 1] + F ![1, 0, 1] +
      F ![0, 1, 1] + F ![1, 1, 1] = 0)
    (hb : betaV F = 0) :
    ∃ b : V3, ∀ x, F x = b ⬝ᵥ x := by
  have hb' : (∑ v : V3, F v • v) = 0 := hb
  rw [sum_V3] at hb'
  have c0 : F ![1, 0, 0] + F ![1, 1, 0] + F ![1, 0, 1] + F ![1, 1, 1] = 0 := by
    have := congrFun hb' 0
    simpa using this
  have c1 : F ![0, 1, 0] + F ![1, 1, 0] + F ![0, 1, 1] + F ![1, 1, 1] = 0 := by
    have := congrFun hb' 1
    simpa using this
  have c2 : F ![0, 0, 1] + F ![1, 0, 1] + F ![0, 1, 1] + F ![1, 1, 1] = 0 := by
    have := congrFun hb' 2
    simpa using this
  rw [h0, zero_add] at hs
  obtain ⟨e12, e13, e23, e123⟩ := key7_lin (F ![1, 0, 0]) (F ![0, 1, 0]) (F ![0, 0, 1])
    (F ![1, 1, 0]) (F ![1, 0, 1]) (F ![0, 1, 1]) (F ![1, 1, 1])
    (by convert hs using 1; abel) c0 c1 c2
  refine ⟨![F ![1, 0, 0], F ![0, 1, 0], F ![0, 0, 1]], fun x => ?_⟩
  rcases V3_cases x with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [dotProduct, Fin.sum_univ_three, h0, e12, e13, e23, e123]

private theorem fst_eq_linFst_of (F : V3 → ZMod 2) (b : V3) (h : ∀ x, F x = b ⬝ᵥ x) :
    fstHom (Multiplicative.ofAdd F) = linFstHom (Multiplicative.ofAdd b) := by
  apply Multiplicative.toAdd.injective
  funext φ
  exact h φ.1.1

private theorem snd_eq_linSnd_of (G : V3 → ZMod 2) (v : V3) (h : ∀ a, G a = a ⬝ᵥ v) :
    sndHom (Multiplicative.ofAdd G) = linSndHom (Multiplicative.ofAdd v) := by
  apply Multiplicative.toAdd.injective
  funext φ
  exact h φ.1.2

private theorem coreV_comp (g : GL (Fin 3) (ZMod 2)) (F : Multiplicative (V3 → ZMod 2))
    (hF : F ∈ coreV) :
    (Multiplicative.ofAdd (fun v => Multiplicative.toAdd F (gPt g⁻¹ v)) :
      Multiplicative (V3 → ZMod 2)) ∈ coreV := by
  obtain ⟨h0, hs⟩ := (mem_coreV F).1 hF
  rw [mem_coreV]
  refine ⟨?_, ?_⟩
  · simp [gPt_zero, h0]
  · simp only [toAdd_ofAdd]
    calc ∑ v : V3, Multiplicative.toAdd F (gPt g⁻¹ v) = ∑ v : V3, Multiplicative.toAdd F v :=
          Equiv.sum_comp (gEquiv g⁻¹) (fun v => Multiplicative.toAdd F v)
      _ = 0 := hs

private theorem coreV_compD (g : GL (Fin 3) (ZMod 2)) (G : Multiplicative (V3 → ZMod 2))
    (hG : G ∈ coreV) :
    (Multiplicative.ofAdd (fun a => Multiplicative.toAdd G (gDu g⁻¹ a)) :
      Multiplicative (V3 → ZMod 2)) ∈ coreV := by
  obtain ⟨h0, hs⟩ := (mem_coreV G).1 hG
  rw [mem_coreV]
  refine ⟨?_, ?_⟩
  · simp [gDu_zero, h0]
  · simp only [toAdd_ofAdd]
    calc ∑ a : V3, Multiplicative.toAdd G (gDu g⁻¹ a) = ∑ a : V3, Multiplicative.toAdd G a :=
          Equiv.sum_comp (gDuEquiv g⁻¹) (fun a => Multiplicative.toAdd G a)
      _ = 0 := hs

private theorem betaV_sub (F G : V3 → ZMod 2) :
    betaV (fun v => F v - G v) = betaV F - betaV G := by
  unfold betaV
  have hs : ∀ v : V3, (F v - G v) • v = F v • v - G v • v := fun v => by
    ext i
    simp [sub_mul]
  simp only [hs]
  exact Finset.sum_sub_distrib _ _

private theorem sum_sub_core (F G : V3 → ZMod 2) (hF : ∑ v : V3, F v = 0) (hG : ∑ v : V3, G v = 0) :
    ∑ v : V3, (F v - G v) = 0 := by
  calc ∑ v : V3, (F v - G v) = ∑ v : V3, F v - ∑ v : V3, G v := Finset.sum_sub_distrib _ _
    _ = 0 := by simp [hF, hG]

private theorem sum_V3_zero (F : V3 → ZMod 2) (hs : ∑ v : V3, F v = 0) :
    F 0 + F ![1, 0, 0] + F ![0, 1, 0] + F ![1, 1, 0] + F ![0, 0, 1] +
      F ![1, 0, 1] + F ![0, 1, 1] + F ![1, 1, 1] = 0 :=
  (sum_V3 F).symm.trans hs

set_option maxHeartbeats 1000000 in
private theorem core_beta_zero_mem (F₀ : Multiplicative (V3 → ZMod 2)) (hF₀ : F₀ ∈ coreV)
    (h : betaV (Multiplicative.toAdd F₀) = 0) : fstHom F₀ ∈ K2F := by
  obtain ⟨h0, hs⟩ := (mem_coreV F₀).1 hF₀
  obtain ⟨b, hb⟩ := beta_zero_linear (Multiplicative.toAdd F₀) h0 ((sum_V3 _).symm.trans hs) h
  have e := fst_eq_linFst_of (Multiplicative.toAdd F₀) b hb
  rw [ofAdd_toAdd] at e
  rw [e]
  exact Subgroup.mem_map.2 ⟨Multiplicative.ofAdd b, Subgroup.mem_top _, rfl⟩

set_option maxHeartbeats 1000000 in
private theorem core_lift (W : Subgroup MF) (hWi : ∀ g, ∀ u ∈ W, ρF g u ∈ W)
    (F₀ : Multiplicative (V3 → ZMod 2)) (hF₀ : F₀ ∈ coreV) (hwW : fstHom F₀ ∈ W)
    (hβ0 : betaV (Multiplicative.toAdd F₀) ≠ 0) (v : V3) :
    ∃ F' : Multiplicative (V3 → ZMod 2), F' ∈ coreV ∧ fstHom F' ∈ W ∧
      betaV (Multiplicative.toAdd F') = v := by
  by_cases hv : v = 0
  · subst hv
    refine ⟨1, one_mem _, ?_, ?_⟩
    · rw [map_one]
      exact W.one_mem
    · rw [toAdd_one]
      simp [betaV]
  · obtain ⟨g, hg⟩ := exists_gl_map (betaV (Multiplicative.toAdd F₀)) v hβ0 hv
    have hg' : gPt g (betaV (Multiplicative.toAdd F₀)) = v := hg
    refine ⟨Multiplicative.ofAdd (fun x => Multiplicative.toAdd F₀ (gPt g⁻¹ x)),
      coreV_comp g F₀ hF₀, ?_, ?_⟩
    · have h1 : fstHom (Multiplicative.ofAdd (fun x => Multiplicative.toAdd F₀ (gPt g⁻¹ x))) =
          ρF g (fstHom F₀) := (ρF_fst g F₀).symm
      rw [h1]
      exact hWi g _ hwW
    · rw [toAdd_ofAdd, betaV_comp, hg']

set_option maxHeartbeats 1000000 in
private theorem core_split_mem (W : Subgroup MF) (hK : K2F ≤ W)
    (F₁ F' : Multiplicative (V3 → ZMod 2)) (hF₁ : F₁ ∈ coreV) (hF'c : F' ∈ coreV)
    (hβ' : betaV (Multiplicative.toAdd F') = betaV (Multiplicative.toAdd F₁))
    (hF'W : fstHom F' ∈ W) : fstHom F₁ ∈ W := by
  have hF₁' := (mem_coreV F₁).1 hF₁
  have hF'' := (mem_coreV F').1 hF'c
  have hD0 : (fun v => Multiplicative.toAdd F₁ v - Multiplicative.toAdd F' v) 0 = 0 := by
    simp [hF₁'.1, hF''.1]
  have hDs : ∑ v : V3, (Multiplicative.toAdd F₁ v - Multiplicative.toAdd F' v) = 0 :=
    sum_sub_core _ _ hF₁'.2 hF''.2
  have hDb : betaV (fun v => Multiplicative.toAdd F₁ v - Multiplicative.toAdd F' v) = 0 := by
    rw [betaV_sub, hβ']
    exact sub_self _
  obtain ⟨b, hb⟩ := beta_zero_linear
    (fun v => Multiplicative.toAdd F₁ v - Multiplicative.toAdd F' v) hD0
    (sum_V3_zero (fun v => Multiplicative.toAdd F₁ v - Multiplicative.toAdd F' v) hDs) hDb
  have hlin := fst_eq_linFst_of
    (fun v => Multiplicative.toAdd F₁ v - Multiplicative.toAdd F' v) b hb
  have hsplit : fstHom F₁ = fstHom F' * fstHom (Multiplicative.ofAdd
      (fun v => Multiplicative.toAdd F₁ v - Multiplicative.toAdd F' v)) := by
    rw [← map_mul]
    congr 1
    apply Multiplicative.toAdd.injective
    funext x
    show Multiplicative.toAdd F₁ x =
      Multiplicative.toAdd F' x + (Multiplicative.toAdd F₁ x - Multiplicative.toAdd F' x)
    ring
  rw [hsplit]
  refine W.mul_mem hF'W (hK ?_)
  rw [hlin]
  exact Subgroup.mem_map.2 ⟨Multiplicative.ofAdd b, Subgroup.mem_top _, rfl⟩

set_option maxHeartbeats 1000000 in
private theorem K2_maximal (W : Subgroup MF) (hWU : W ≤ U2F)
    (hWi : ∀ g, ∀ u ∈ W, ρF g u ∈ W) (hK : K2F ≤ W) : W = K2F ∨ W = U2F := by
  by_cases hWK : W ≤ K2F
  · exact Or.inl (le_antisymm hWK hK)
  right
  obtain ⟨w, hwW, hwK⟩ := Set.not_subset.1 hWK
  obtain ⟨F₀, hF₀, rfl⟩ := Subgroup.mem_map.1 (hWU hwW)
  have hβ0 : betaV (Multiplicative.toAdd F₀) ≠ 0 :=
    fun h => hwK (core_beta_zero_mem F₀ hF₀ h)
  refine le_antisymm hWU (fun u hu => ?_)
  obtain ⟨F₁, hF₁, rfl⟩ := Subgroup.mem_map.1 hu
  obtain ⟨F', hF'c, hF'W, hβ'⟩ :=
    core_lift W hWi F₀ hF₀ hwW hβ0 (betaV (Multiplicative.toAdd F₁))
  exact core_split_mem W hK F₁ F' hF₁ hF'c hβ' hF'W

set_option maxHeartbeats 1000000 in
private theorem dual_beta_zero_mem (G₀ : Multiplicative (V3 → ZMod 2)) (hG₀ : G₀ ∈ coreV)
    (h : betaD (Multiplicative.toAdd G₀) = 0) : sndHom G₀ ∈ K3F := by
  obtain ⟨h0, hs⟩ := (mem_coreV G₀).1 hG₀
  obtain ⟨v, hv⟩ := beta_zero_linear (Multiplicative.toAdd G₀) h0 ((sum_V3 _).symm.trans hs) h
  have e := snd_eq_linSnd_of (Multiplicative.toAdd G₀) v
    (fun a => (hv a).trans (dotProduct_comm _ _))
  rw [ofAdd_toAdd] at e
  rw [e]
  exact Subgroup.mem_map.2 ⟨Multiplicative.ofAdd v, Subgroup.mem_top _, rfl⟩

set_option maxHeartbeats 1000000 in
private theorem dual_lift (W : Subgroup MF) (hWi : ∀ g, ∀ u ∈ W, ρF g u ∈ W)
    (G₀ : Multiplicative (V3 → ZMod 2)) (hG₀ : G₀ ∈ coreV) (hwW : sndHom G₀ ∈ W)
    (hβ0 : betaD (Multiplicative.toAdd G₀) ≠ 0) (v : V3) :
    ∃ G' : Multiplicative (V3 → ZMod 2), G' ∈ coreV ∧ sndHom G' ∈ W ∧
      betaD (Multiplicative.toAdd G') = v := by
  by_cases hv : v = 0
  · subst hv
    refine ⟨1, one_mem _, ?_, ?_⟩
    · rw [map_one]
      exact W.one_mem
    · rw [toAdd_one]
      simp [betaD]
  · obtain ⟨g, hg⟩ := dualTrans2 (betaD (Multiplicative.toAdd G₀)) v hβ0 hv
    have hg' : gDu g (betaD (Multiplicative.toAdd G₀)) = v := hg
    refine ⟨Multiplicative.ofAdd (fun a => Multiplicative.toAdd G₀ (gDu g⁻¹ a)),
      coreV_compD g G₀ hG₀, ?_, ?_⟩
    · have h1 : sndHom (Multiplicative.ofAdd (fun a => Multiplicative.toAdd G₀ (gDu g⁻¹ a))) =
          ρF g (sndHom G₀) := (ρF_snd g G₀).symm
      rw [h1]
      exact hWi g _ hwW
    · rw [toAdd_ofAdd, betaD_comp, hg']

set_option maxHeartbeats 1000000 in
private theorem dual_split_mem (W : Subgroup MF) (hK : K3F ≤ W)
    (G₁ G' : Multiplicative (V3 → ZMod 2)) (hG₁ : G₁ ∈ coreV) (hG'c : G' ∈ coreV)
    (hβ' : betaD (Multiplicative.toAdd G') = betaD (Multiplicative.toAdd G₁))
    (hG'W : sndHom G' ∈ W) : sndHom G₁ ∈ W := by
  have hG₁' := (mem_coreV G₁).1 hG₁
  have hG'' := (mem_coreV G').1 hG'c
  have hD0 : (fun a => Multiplicative.toAdd G₁ a - Multiplicative.toAdd G' a) 0 = 0 := by
    simp [hG₁'.1, hG''.1]
  have hDs : ∑ a : V3, (Multiplicative.toAdd G₁ a - Multiplicative.toAdd G' a) = 0 :=
    sum_sub_core _ _ hG₁'.2 hG''.2
  have hDb : betaV (fun a => Multiplicative.toAdd G₁ a - Multiplicative.toAdd G' a) = 0 := by
    rw [betaV_sub]
    exact sub_eq_zero.2 hβ'.symm
  obtain ⟨b, hb⟩ := beta_zero_linear
    (fun a => Multiplicative.toAdd G₁ a - Multiplicative.toAdd G' a) hD0
    (sum_V3_zero (fun a => Multiplicative.toAdd G₁ a - Multiplicative.toAdd G' a) hDs) hDb
  have hlin := snd_eq_linSnd_of
    (fun a => Multiplicative.toAdd G₁ a - Multiplicative.toAdd G' a) b
    (fun a => (hb a).trans (dotProduct_comm _ _))
  have hsplit : sndHom G₁ = sndHom G' * sndHom (Multiplicative.ofAdd
      (fun a => Multiplicative.toAdd G₁ a - Multiplicative.toAdd G' a)) := by
    rw [← map_mul]
    congr 1
    apply Multiplicative.toAdd.injective
    funext x
    show Multiplicative.toAdd G₁ x =
      Multiplicative.toAdd G' x + (Multiplicative.toAdd G₁ x - Multiplicative.toAdd G' x)
    ring
  rw [hsplit]
  refine W.mul_mem hG'W (hK ?_)
  rw [hlin]
  exact Subgroup.mem_map.2 ⟨Multiplicative.ofAdd b, Subgroup.mem_top _, rfl⟩

set_option maxHeartbeats 1000000 in
private theorem K3_maximal (W : Subgroup MF) (hWU : W ≤ U3F)
    (hWi : ∀ g, ∀ u ∈ W, ρF g u ∈ W) (hK : K3F ≤ W) : W = K3F ∨ W = U3F := by
  by_cases hWK : W ≤ K3F
  · exact Or.inl (le_antisymm hWK hK)
  right
  obtain ⟨w, hwW, hwK⟩ := Set.not_subset.1 hWK
  obtain ⟨G₀, hG₀, rfl⟩ := Subgroup.mem_map.1 (hWU hwW)
  have hβ0 : betaD (Multiplicative.toAdd G₀) ≠ 0 :=
    fun h => hwK (dual_beta_zero_mem G₀ hG₀ h)
  refine le_antisymm hWU (fun u hu => ?_)
  obtain ⟨G₁, hG₁, rfl⟩ := Subgroup.mem_map.1 hu
  obtain ⟨G', hG'c, hG'W, hβ'⟩ :=
    dual_lift W hWi G₀ hG₀ hwW hβ0 (betaD (Multiplicative.toAdd G₁))
  exact dual_split_mem W hK G₁ G' hG₁ hG'c hβ' hG'W

end FlagH62

namespace FlagH62

open CFSG.ASVolI.ChH Matrix

private theorem zmod2_cases (z : ZMod 2) : z = 0 ∨ z = 1 := by
  revert z
  decide

set_option maxHeartbeats 1000000 in
private theorem sum_lin_zero : ∀ b : V3, ∑ v : V3, b ⬝ᵥ v = 0 := by
  decide

set_option maxHeartbeats 1000000 in
private theorem sum_lin_zero' : ∀ v : V3, ∑ a : V3, a ⬝ᵥ v = 0 := by
  decide

private theorem mem_U1F {u : MF} :
    u ∈ U1F ↔ ∃ c : Multiplicative (ZMod 2), constHom c = u := by
  unfold U1F
  rw [Subgroup.mem_map]
  simp

private theorem ρF_const (g : GL (Fin 3) (ZMod 2)) (c : Multiplicative (ZMod 2)) :
    ρF g (constHom c) = constHom c := by
  apply Multiplicative.toAdd.injective
  funext φ
  rfl

private theorem U1F_inv : ∀ g, ∀ u ∈ U1F, ρF g u ∈ U1F := by
  intro g u hu
  obtain ⟨c, rfl⟩ := mem_U1F.1 hu
  rw [ρF_const]
  exact mem_U1F.2 ⟨c, rfl⟩

private theorem U1F_eq {u : MF} (hu : u ∈ U1F) :
    u = 1 ∨ u = constHom (Multiplicative.ofAdd 1) := by
  obtain ⟨c, rfl⟩ := mem_U1F.1 hu
  rcases zmod2_cases (Multiplicative.toAdd c) with h | h
  · left
    rw [show c = 1 from Multiplicative.toAdd.injective (h.trans toAdd_one.symm), map_one]
  · right
    rw [show c = Multiplicative.ofAdd 1 from
      Multiplicative.toAdd.injective (h.trans (toAdd_ofAdd 1).symm)]

private theorem U1F_simple (W : Subgroup MF) (hWU : W ≤ U1F)
    (_hWi : ∀ g, ∀ u ∈ W, ρF g u ∈ W) : W = ⊥ ∨ W = U1F := by
  by_cases hW : W = ⊥
  · exact Or.inl hW
  right
  obtain ⟨⟨w, hwW⟩, hw1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hW
  have hw1' : w ≠ 1 := fun h => hw1 (Subtype.ext h)
  have hw : w = constHom (Multiplicative.ofAdd 1) := by
    rcases U1F_eq (hWU hwW) with h | h
    · exact absurd h hw1'
    · exact h
  have hle : U1F ≤ W := by
    intro u hu
    rcases U1F_eq hu with rfl | rfl
    · exact W.one_mem
    · rw [← hw]
      exact hwW
  exact le_antisymm hWU hle

private def flagE1E2 : Fl := ⟨(![1, 0, 0], ![0, 1, 0]), by decide⟩

private def flagE2E1 : Fl := ⟨(![0, 1, 0], ![1, 0, 0]), by decide⟩

private theorem U1F_ne_bot : U1F ≠ ⊥ := by
  intro h
  have hm : constHom (Multiplicative.ofAdd 1) ∈ U1F := mem_U1F.2 ⟨_, rfl⟩
  rw [h, Subgroup.mem_bot] at hm
  have h0 : (1 : ZMod 2) = 0 :=
    congrArg (fun x : MF => Multiplicative.toAdd x flagE1E2) hm
  exact absurd h0 (by decide)

set_option maxHeartbeats 1000000 in
private theorem key_lin_point : ∀ c : V3, (∀ φ : Fl, c ⬝ᵥ φ.1.1 = 0) → c = 0 := by
  decide

set_option maxHeartbeats 1000000 in
private theorem key_lin_du : ∀ c : V3, (∀ φ : Fl, φ.1.2 ⬝ᵥ c = 0) → c = 0 := by
  decide

private def indPt12 (v : V3) : ZMod 2 := if v = ![1, 0, 0] ∨ v = ![0, 1, 0] then 1 else 0

private def indDu12 (a : V3) : ZMod 2 := if a = ![1, 0, 0] ∨ a = ![0, 1, 0] then 1 else 0

set_option maxHeartbeats 1000000 in
private theorem indPt12_not_lin :
    ∀ c : V3, (∀ φ : Fl, c ⬝ᵥ φ.1.1 = indPt12 φ.1.1) → False := by
  decide

set_option maxHeartbeats 1000000 in
private theorem indDu12_not_lin :
    ∀ c : V3, (∀ φ : Fl, φ.1.2 ⬝ᵥ c = indDu12 φ.1.2) → False := by
  decide

private theorem K2F_le_U2F : K2F ≤ U2F := by
  intro u hu
  obtain ⟨b, -, rfl⟩ := Subgroup.mem_map.1 hu
  refine Subgroup.mem_map.2 ⟨Multiplicative.ofAdd (fun v => Multiplicative.toAdd b ⬝ᵥ v), ?_, ?_⟩
  · rw [mem_coreV]
    refine ⟨?_, ?_⟩
    · show Multiplicative.toAdd b ⬝ᵥ (0 : V3) = 0
      exact dotProduct_zero _
    · show ∑ v : V3, Multiplicative.toAdd b ⬝ᵥ v = 0
      exact sum_lin_zero _
  · apply Multiplicative.toAdd.injective
    funext φ
    rfl

private theorem K2F_ne_U2F : K2F ≠ U2F := by
  intro heq
  have hmem : fstHom (Multiplicative.ofAdd indPt12) ∈ U2F := by
    refine Subgroup.mem_map.2 ⟨Multiplicative.ofAdd indPt12, ?_, rfl⟩
    rw [mem_coreV]
    refine ⟨?_, ?_⟩
    · exact (by decide : indPt12 0 = 0)
    · exact (by decide : ∑ v : V3, indPt12 v = 0)
  rw [← heq] at hmem
  obtain ⟨b, -, hb⟩ := Subgroup.mem_map.1 hmem
  refine indPt12_not_lin (Multiplicative.toAdd b) (fun φ => ?_)
  exact congrArg (fun x : MF => Multiplicative.toAdd x φ) hb

private theorem K2F_ne_bot : K2F ≠ ⊥ := by
  intro h
  have hm : linFstHom (Multiplicative.ofAdd ![1, 0, 0]) ∈ K2F :=
    Subgroup.mem_map.2 ⟨_, Subgroup.mem_top _, rfl⟩
  rw [h, Subgroup.mem_bot] at hm
  have h0 : ∀ φ : Fl, (![1, 0, 0] : V3) ⬝ᵥ φ.1.1 = 0 := fun φ =>
    congrArg (fun x : MF => Multiplicative.toAdd x φ) hm
  exact absurd (key_lin_point _ h0) (by decide)

private theorem K2F_inv : ∀ g, ∀ u ∈ K2F, ρF g u ∈ K2F := by
  intro g u hu
  obtain ⟨b, -, rfl⟩ := Subgroup.mem_map.1 hu
  rw [ρF_linFst]
  exact Subgroup.mem_map.2 ⟨_, Subgroup.mem_top _, rfl⟩

private theorem K2F_isMax : IsMaxSub ρF U2F K2F := by
  unfold IsMaxSub
  exact ⟨lt_of_le_of_ne K2F_le_U2F K2F_ne_U2F, K2F_inv,
    fun N hKN hNW hNi => K2_maximal N hNW hNi hKN⟩

private theorem K3F_le_U3F : K3F ≤ U3F := by
  intro u hu
  obtain ⟨v, -, rfl⟩ := Subgroup.mem_map.1 hu
  refine Subgroup.mem_map.2 ⟨Multiplicative.ofAdd (fun a => a ⬝ᵥ Multiplicative.toAdd v), ?_, ?_⟩
  · rw [mem_coreV]
    refine ⟨?_, ?_⟩
    · show (0 : V3) ⬝ᵥ Multiplicative.toAdd v = 0
      exact zero_dotProduct _
    · show ∑ a : V3, a ⬝ᵥ Multiplicative.toAdd v = 0
      exact sum_lin_zero' _
  · apply Multiplicative.toAdd.injective
    funext φ
    rfl

private theorem K3F_ne_U3F : K3F ≠ U3F := by
  intro heq
  have hmem : sndHom (Multiplicative.ofAdd indDu12) ∈ U3F := by
    refine Subgroup.mem_map.2 ⟨Multiplicative.ofAdd indDu12, ?_, rfl⟩
    rw [mem_coreV]
    refine ⟨?_, ?_⟩
    · exact (by decide : indDu12 0 = 0)
    · exact (by decide : ∑ v : V3, indDu12 v = 0)
  rw [← heq] at hmem
  obtain ⟨v, -, hv⟩ := Subgroup.mem_map.1 hmem
  refine indDu12_not_lin (Multiplicative.toAdd v) (fun φ => ?_)
  exact congrArg (fun x : MF => Multiplicative.toAdd x φ) hv

private theorem K3F_ne_bot : K3F ≠ ⊥ := by
  intro h
  have hm : linSndHom (Multiplicative.ofAdd ![1, 0, 0]) ∈ K3F :=
    Subgroup.mem_map.2 ⟨_, Subgroup.mem_top _, rfl⟩
  rw [h, Subgroup.mem_bot] at hm
  have h0 : ∀ φ : Fl, φ.1.2 ⬝ᵥ (![1, 0, 0] : V3) = 0 := fun φ =>
    congrArg (fun x : MF => Multiplicative.toAdd x φ) hm
  exact absurd (key_lin_du _ h0) (by decide)

private theorem K3F_inv : ∀ g, ∀ u ∈ K3F, ρF g u ∈ K3F := by
  intro g u hu
  obtain ⟨v, -, rfl⟩ := Subgroup.mem_map.1 hu
  rw [ρF_linSnd]
  exact Subgroup.mem_map.2 ⟨_, Subgroup.mem_top _, rfl⟩

private theorem K3F_isMax : IsMaxSub ρF U3F K3F := by
  unfold IsMaxSub
  exact ⟨lt_of_le_of_ne K3F_le_U3F K3F_ne_U3F, K3F_inv,
    fun N hKN hNW hNi => K3_maximal N hNW hNi hKN⟩

private theorem U2F_inv : ∀ g, ∀ u ∈ U2F, ρF g u ∈ U2F := by
  intro g u hu
  obtain ⟨F, hF, rfl⟩ := Subgroup.mem_map.1 hu
  rw [ρF_fst]
  refine Subgroup.mem_map.2 ⟨_, ?_, rfl⟩
  rw [mem_coreV] at hF ⊢
  obtain ⟨h0, hs⟩ := hF
  refine ⟨?_, ?_⟩
  · show Multiplicative.toAdd F (gPt g⁻¹ 0) = 0
    rw [gPt_zero]
    exact h0
  · exact (Equiv.sum_comp (gEquiv g⁻¹) (fun v => Multiplicative.toAdd F v)).trans hs

private theorem U3F_inv : ∀ g, ∀ u ∈ U3F, ρF g u ∈ U3F := by
  intro g u hu
  obtain ⟨F, hF, rfl⟩ := Subgroup.mem_map.1 hu
  rw [ρF_snd]
  refine Subgroup.mem_map.2 ⟨_, ?_, rfl⟩
  rw [mem_coreV] at hF ⊢
  obtain ⟨h0, hs⟩ := hF
  refine ⟨?_, ?_⟩
  · show Multiplicative.toAdd F (gDu g⁻¹ 0) = 0
    rw [gDu_zero]
    exact h0
  · exact (Equiv.sum_comp (gDuEquiv g⁻¹) (fun v => Multiplicative.toAdd F v)).trans hs

private theorem adjAmb_mem_Adj3 (g : GL (Fin 3) (ZMod 2)) (X : AdjAmb) (hX : X ∈ Adj3) :
    adjAmbAct g X ∈ Adj3 := by
  have hX' : (Multiplicative.toAdd X).trace = 0 := hX
  show (Multiplicative.toAdd (adjAmbAct g X)).trace = 0
  change ((g : Matrix (Fin 3) (Fin 3) (ZMod 2)) * Multiplicative.toAdd X *
    ((g⁻¹ : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2))).trace = 0
  rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]
  exact hX'

private theorem U4F_inv : ∀ g, ∀ u ∈ U4F, ρF g u ∈ U4F := by
  intro g u hu
  obtain ⟨X, hX, rfl⟩ := Subgroup.mem_map.1 hu
  rw [ρF_stein]
  exact Subgroup.mem_map.2 ⟨_, adjAmb_mem_Adj3 g X hX, rfl⟩

private theorem U4F_ne_bot : U4F ≠ ⊥ := by
  intro h
  have hX : (Multiplicative.ofAdd !![0, 1, 0; 0, 0, 0; 0, 0, 0] : AdjAmb) ∈ Adj3 := by
    show Matrix.trace (!![0, 1, 0; 0, 0, 0; 0, 0, 0] : Matrix (Fin 3) (Fin 3) (ZMod 2)) = 0
    decide
  have hm : steinHom (Multiplicative.ofAdd !![0, 1, 0; 0, 0, 0; 0, 0, 0]) ∈ U4F :=
    Subgroup.mem_map.2 ⟨_, hX, rfl⟩
  rw [h, Subgroup.mem_bot] at hm
  have h0 : (![1, 0, 0] : V3) ⬝ᵥ
      ((!![0, 1, 0; 0, 0, 0; 0, 0, 0] : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ ![0, 1, 0]) = 0 :=
    congrArg (fun x : MF => Multiplicative.toAdd x flagE2E1) hm
  exact absurd h0 (by decide)

private theorem setupF : ArtH62.Setup ρF U1F U2F U3F U4F K2F K3F where
  i₁ := U1F_inv
  i₂ := U2F_inv
  i₃ := U3F_inv
  i₄ := U4F_inv
  hsum := dsum_top
  h₁ := dsum_inter1
  h₂ := dsum_inter2
  h₃ := dsum_inter3
  h₄ := dsum_inter4
  hU₁ := U1F_ne_bot
  hU₄ := U4F_ne_bot
  s₁ := U1F_simple
  s₄ := fun W hWU hWi => by
    by_cases hW : W = ⊥
    · exact Or.inl hW
    · exact Or.inr (le_antisymm hWU (U4_simple W hWU hWi hW))
  k₂ := K2F_le_U2F
  k₂ne := K2F_ne_bot
  k₂max := K2F_isMax
  soc₂ := fun W hWU hWi hW => socle2 W hWU hWi hW
  k₃ := K3F_le_U3F
  k₃ne := K3F_ne_bot
  k₃max := K3F_isMax
  soc₃ := fun W hWU hWi hW => socle3 W hWU hWi hW

end FlagH62

namespace FlagH62

open CFSG.ASVolI.ChH Matrix

section Transport

variable {G : Type*} [Group G] {X Y : Type*} [CommGroup X] [CommGroup Y]
  {ρ : G →* MulAut X} {ρ' : G →* MulAut Y}

private theorem tr_inv (e : Y ≃* X) (hρ : ∀ g y, e (ρ' g y) = ρ g (e y)) {U : Subgroup Y}
    (hU : ∀ g, ∀ u ∈ U, ρ' g u ∈ U) : ∀ g, ∀ u ∈ U.map e.toMonoidHom,
      ρ g u ∈ U.map e.toMonoidHom := by
  intro g u hu
  obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 hu
  show ρ g (e y) ∈ _
  rw [← hρ]
  exact Subgroup.mem_map.2 ⟨_, hU g y hy, rfl⟩

private theorem tr_symm (e : Y ≃* X) (hρ : ∀ g y, e (ρ' g y) = ρ g (e y)) (g : G) (x : X) :
    e.symm (ρ g x) = ρ' g (e.symm x) := by
  apply e.injective
  rw [MulEquiv.apply_symm_apply, hρ, MulEquiv.apply_symm_apply]

private theorem tr_isoSec (e : Y ≃* X) (hρ : ∀ g y, e (ρ' g y) = ρ g (e y)) {U Z : Subgroup Y}
    {A : Type*} [CommGroup A] {act : G →* MulAut A} {S : Subgroup A}
    (h : IsoSecIn ρ' U Z A act S) :
    IsoSecIn ρ (U.map e.toMonoidHom) (Z.map e.toMonoidHom) A act S := by
  obtain ⟨hZU, hU, hZ, β, hrange, hker, hequiv⟩ := h
  let eS : ↥(U.map e.toMonoidHom) →* ↥U :=
    { toFun := fun x => ⟨e.symm x, Subgroup.mem_map_equiv.1 x.2⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun x y => Subtype.ext (by
        show e.symm ((x * y : ↥(U.map e.toMonoidHom)) : X) = e.symm (x : X) * e.symm (y : X)
        rw [Subgroup.coe_mul, map_mul]) }
  refine ⟨Subgroup.map_mono hZU, tr_inv e hρ hU, tr_inv e hρ hZ, β.comp eS, ?_, ?_, ?_⟩
  · ext a
    constructor
    · intro ha
      obtain ⟨u, rfl⟩ := MonoidHom.mem_range.1 ha
      rw [← hrange]
      exact MonoidHom.mem_range.2 ⟨eS u, rfl⟩
    · intro ha
      rw [← hrange] at ha
      obtain ⟨u, rfl⟩ := MonoidHom.mem_range.1 ha
      refine MonoidHom.mem_range.2 ⟨⟨e u, Subgroup.mem_map.2 ⟨u, u.2, rfl⟩⟩, ?_⟩
      show β (eS _) = β u
      congr 1
      exact Subtype.ext (e.symm_apply_apply u)
  · intro u
    show β (eS u) = 1 ↔ (u : X) ∈ Z.map e.toMonoidHom
    rw [hker (eS u)]
    exact Subgroup.mem_map_equiv.symm
  · intro g u u' h
    show β (eS u') = act g (β (eS u))
    apply hequiv g (eS u) (eS u')
    show e.symm (u' : X) = ρ' g (e.symm (u : X))
    rw [h, tr_symm e hρ]

private theorem tr_isMax_map (e : Y ≃* X) (hρ : ∀ g y, e (ρ' g y) = ρ g (e y)) (W N : Subgroup Y)
    (h : IsMaxSub ρ' W N) : IsMaxSub ρ (W.map e.toMonoidHom) (N.map e.toMonoidHom) := by
  obtain ⟨hlt, hinv, hmax⟩ := h
  refine ⟨?_, tr_inv e hρ hinv, ?_⟩
  · refine lt_of_le_of_ne (Subgroup.map_mono hlt.le) ?_
    intro heq
    exact hlt.ne (Subgroup.map_injective (f := e.toMonoidHom) e.injective heq)
  · intro N' hNN' hN'W hN'i
    have hNeq : (N'.comap e.toMonoidHom).map e.toMonoidHom = N' :=
      Subgroup.map_comap_eq_self_of_surjective e.surjective N'
    have hMW : N'.comap e.toMonoidHom ≤ W := by
      intro y hy
      have hy' : e y ∈ W.map e.toMonoidHom := hN'W hy
      obtain ⟨w, hw, hwy⟩ := Subgroup.mem_map.1 hy'
      rw [e.injective hwy] at hw
      exact hw
    have hNM : N ≤ N'.comap e.toMonoidHom := by
      intro y hy
      exact hNN' (Subgroup.mem_map.2 ⟨y, hy, rfl⟩)
    have hMi : ∀ g, ∀ u ∈ N'.comap e.toMonoidHom, ρ' g u ∈ N'.comap e.toMonoidHom := by
      intro g u hu
      show e (ρ' g u) ∈ N'
      rw [hρ]
      exact hN'i g _ hu
    rcases hmax (N'.comap e.toMonoidHom) hNM hMW hMi with h1 | h1
    · left
      rw [← h1]
      exact hNeq.symm
    · right
      rw [← h1]
      exact hNeq.symm

private theorem tr_isMax_comap (e : Y ≃* X) (hρ : ∀ g y, e (ρ' g y) = ρ g (e y)) (W : Subgroup Y)
    (N : Subgroup X) (h : IsMaxSub ρ (W.map e.toMonoidHom) N) :
    IsMaxSub ρ' W (N.comap e.toMonoidHom) := by
  obtain ⟨hlt, hinv, hmax⟩ := h
  have hNeq : (N.comap e.toMonoidHom).map e.toMonoidHom = N :=
    Subgroup.map_comap_eq_self_of_surjective e.surjective N
  refine ⟨?_, ?_, ?_⟩
  · refine lt_of_le_of_ne ?_ ?_
    · intro y hy
      have hy' : e y ∈ W.map e.toMonoidHom := hlt.le hy
      obtain ⟨w, hw, hwy⟩ := Subgroup.mem_map.1 hy'
      rw [e.injective hwy] at hw
      exact hw
    · intro heq
      apply hlt.ne
      rw [← hNeq, heq]
  · intro g u hu
    show e (ρ' g u) ∈ N
    rw [hρ]
    exact hinv g _ hu
  · intro M' hM'N hM'W hM'i
    have hNle : N ≤ M'.map e.toMonoidHom := by
      rw [← hNeq]
      exact Subgroup.map_mono hM'N
    have hN' := hmax (M'.map e.toMonoidHom) hNle (Subgroup.map_mono hM'W) (tr_inv e hρ hM'i)
    rcases hN' with h1 | h1
    · left
      apply Subgroup.map_injective (f := e.toMonoidHom) e.injective
      rw [hNeq, h1]
    · right
      exact Subgroup.map_injective (f := e.toMonoidHom) e.injective h1

private theorem tr_radSub (e : Y ≃* X) (hρ : ∀ g y, e (ρ' g y) = ρ g (e y)) (W : Subgroup Y) :
    radSub ρ (W.map e.toMonoidHom) = (radSub ρ' W).map e.toMonoidHom := by
  ext x
  constructor
  · intro hx
    unfold radSub at hx
    obtain ⟨hxW, hxI⟩ := Subgroup.mem_inf.1 hx
    obtain ⟨y, hyW, rfl⟩ := Subgroup.mem_map.1 hxW
    refine Subgroup.mem_map.2 ⟨y, ?_, rfl⟩
    unfold radSub
    refine Subgroup.mem_inf.2 ⟨hyW, Subgroup.mem_iInf.2 fun N => Subgroup.mem_iInf.2 fun hN => ?_⟩
    have hmem : e y ∈ N.map e.toMonoidHom :=
      Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 hxI (N.map e.toMonoidHom))
        (tr_isMax_map e hρ W N hN)
    obtain ⟨z, hz, hzy⟩ := Subgroup.mem_map.1 hmem
    rwa [e.injective hzy] at hz
  · intro hx
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 hx
    unfold radSub at hy
    obtain ⟨hyW, hyI⟩ := Subgroup.mem_inf.1 hy
    unfold radSub
    refine Subgroup.mem_inf.2 ⟨Subgroup.mem_map.2 ⟨y, hyW, rfl⟩,
      Subgroup.mem_iInf.2 fun N => Subgroup.mem_iInf.2 fun hN => ?_⟩
    have hyN : y ∈ N.comap e.toMonoidHom :=
      Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 hyI (N.comap e.toMonoidHom))
        (tr_isMax_comap e hρ W N hN)
    exact hyN

end Transport

private noncomputable def eqT (T : Subgroup (GL (Fin 3) (ZMod 2))) (φ₀ : Fl)
    (hT : ∀ t ∈ T, t • φ₀ = φ₀) (hθ : Function.Bijective (thetaOf T φ₀ hT)) : MF ≃* PermLT T where
  toFun F := Multiplicative.ofAdd (fun q => Multiplicative.toAdd F (thetaOf T φ₀ hT q))
  invFun f := Multiplicative.ofAdd
    (fun φ => Multiplicative.toAdd f ((Equiv.ofBijective _ hθ).symm φ))
  left_inv F := by
    apply Multiplicative.toAdd.injective
    funext φ
    have hs : thetaOf T φ₀ hT ((Equiv.ofBijective _ hθ).symm φ) = φ :=
      (Equiv.ofBijective _ hθ).apply_symm_apply φ
    show Multiplicative.toAdd F (thetaOf T φ₀ hT ((Equiv.ofBijective _ hθ).symm φ)) =
      Multiplicative.toAdd F φ
    rw [hs]
  right_inv f := by
    apply Multiplicative.toAdd.injective
    funext q
    simp
  map_mul' F G := by
    apply Multiplicative.toAdd.injective
    funext q
    simp

private theorem eqT_apply (T : Subgroup (GL (Fin 3) (ZMod 2))) (φ₀ : Fl)
    (hT : ∀ t ∈ T, t • φ₀ = φ₀) (hθ : Function.Bijective (thetaOf T φ₀ hT)) (F : MF)
    (q : GL (Fin 3) (ZMod 2) ⧸ T) :
    Multiplicative.toAdd (eqT T φ₀ hT hθ F) q = Multiplicative.toAdd F (thetaOf T φ₀ hT q) :=
  rfl

private theorem permLH_apply (H : Subgroup (GL (Fin 3) (ZMod 2))) (g : GL (Fin 3) (ZMod 2))
    (f : PermLT H) (q : GL (Fin 3) (ZMod 2) ⧸ H) :
    Multiplicative.toAdd (permLH H g f) q = Multiplicative.toAdd f (g⁻¹ • q) :=
  rfl

private theorem eqT_equiv (T : Subgroup (GL (Fin 3) (ZMod 2))) (φ₀ : Fl)
    (hT : ∀ t ∈ T, t • φ₀ = φ₀) (hθ : Function.Bijective (thetaOf T φ₀ hT))
    (g : GL (Fin 3) (ZMod 2)) (F : MF) :
    eqT T φ₀ hT hθ (ρF g F) = permLH T g (eqT T φ₀ hT hθ F) := by
  apply Multiplicative.toAdd.injective
  funext q
  rw [eqT_apply, ρF_apply, permLH_apply, eqT_apply, thetaOf_smul]

private theorem constHom_inj : Function.Injective constHom := by
  intro c d h
  have h1 : Multiplicative.toAdd c = Multiplicative.toAdd d :=
    congrArg (fun F : MF => Multiplicative.toAdd F flagE1E2) h
  exact Multiplicative.toAdd.injective h1

private theorem constHom_range : constHom.range = U1F := MonoidHom.range_eq_map constHom

private noncomputable def iso1 : Multiplicative (ZMod 2) ≃* ↥U1F :=
  (MonoidHom.ofInjective constHom_inj).trans (MulEquiv.subgroupCongr constHom_range)

private theorem iso_U1 : IsoSecIn ρF U1F ⊥ (Multiplicative (ZMod 2)) modTriv ⊤ := by
  refine ⟨bot_le, U1F_inv, fun g z hz => ?_, iso1.symm.toMonoidHom, ?_, ?_, ?_⟩
  · have hz1 : z = 1 := Subgroup.mem_bot.1 hz
    subst hz1
    exact Subgroup.mem_bot.2 (map_one (ρF g))
  · ext c
    constructor
    · intro _
      exact Subgroup.mem_top _
    · intro _
      refine MonoidHom.mem_range.2 ⟨iso1 c, ?_⟩
      exact iso1.symm_apply_apply c
  · intro u
    constructor
    · intro h
      have h' : iso1.symm u = 1 := h
      have hu : u = 1 := by
        rw [← iso1.apply_symm_apply u, h', map_one iso1]
      rw [Subgroup.mem_bot]
      exact congrArg Subtype.val hu
    · intro h
      rw [Subgroup.mem_bot] at h
      have hu : u = 1 := Subtype.ext h
      show iso1.symm u = 1
      rw [hu, map_one iso1.symm]
  · intro g u u' h
    obtain ⟨c, hc⟩ := mem_U1F.1 u.2
    have hu' : (u' : MF) = (u : MF) :=
      h.trans (((congrArg (ρF g) hc).symm.trans (ρF_const g c)).trans hc)
    have huu : u' = u := Subtype.ext hu'
    subst huu
    rfl

private theorem iso_U4 : IsoSecIn ρF U4F ⊥ AdjAmb adjAmbAct Adj3 := by
  have hinj : Function.Injective (steinHom.comp Adj3.subtype) := by
    intro x y h
    apply Subtype.ext
    exact stein_inj_adj x y x.2 y.2 h
  have hrange : (steinHom.comp Adj3.subtype).range = U4F := by
    rw [U4F, ← MonoidHom.map_range, Subgroup.range_subtype]
  let iso : ↥Adj3 ≃* ↥U4F := (MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr hrange)
  refine ⟨bot_le, U4F_inv, fun g z hz => ?_, Adj3.subtype.comp iso.symm.toMonoidHom, ?_, ?_, ?_⟩
  · have hz1 : z = 1 := Subgroup.mem_bot.1 hz
    subst hz1
    exact Subgroup.mem_bot.2 (map_one (ρF g))
  · ext X
    constructor
    · intro hX
      obtain ⟨u, rfl⟩ := MonoidHom.mem_range.1 hX
      exact (iso.symm u).2
    · intro hX
      refine MonoidHom.mem_range.2 ⟨iso ⟨X, hX⟩, ?_⟩
      show ((iso.symm (iso ⟨X, hX⟩) : ↥Adj3) : AdjAmb) = X
      rw [MulEquiv.symm_apply_apply]
  · intro u
    constructor
    · intro h
      have h' : iso.symm u = 1 := Subtype.ext h
      have hu : u = 1 := by
        rw [← iso.apply_symm_apply u, h', map_one]
      rw [Subgroup.mem_bot, hu]
      rfl
    · intro h
      rw [Subgroup.mem_bot] at h
      have hu : u = 1 := Subtype.ext h
      subst hu
      exact map_one _
  · intro g u u' h
    have hu : (u : MF) = steinHom ((iso.symm u : ↥Adj3) : AdjAmb) :=
      (congrArg Subtype.val (iso.apply_symm_apply u)).symm
    have hmem : adjAmbAct g ((iso.symm u : ↥Adj3) : AdjAmb) ∈ Adj3 :=
      adjAmb_mem_Adj3 g _ (iso.symm u).2
    have hu' : iso.symm u' = ⟨adjAmbAct g ((iso.symm u : ↥Adj3) : AdjAmb), hmem⟩ := by
      rw [MulEquiv.symm_apply_eq]
      apply Subtype.ext
      show (u' : MF) = steinHom (adjAmbAct g ((iso.symm u : ↥Adj3) : AdjAmb))
      rw [h, hu]
      exact ρF_stein g _
    show ((iso.symm u' : ↥Adj3) : AdjAmb) = adjAmbAct g ((iso.symm u : ↥Adj3) : AdjAmb)
    rw [hu']

private theorem fstCore_range : (fstHom.comp coreV.subtype).range = U2F := by
  ext u
  constructor
  · intro hu
    obtain ⟨F, rfl⟩ := MonoidHom.mem_range.1 hu
    exact Subgroup.mem_map.2 ⟨F.1, F.2, rfl⟩
  · intro hu
    obtain ⟨F, hF, rfl⟩ := Subgroup.mem_map.1 hu
    exact MonoidHom.mem_range.2 ⟨⟨F, hF⟩, rfl⟩

private theorem fstCore_inj : Function.Injective (fstHom.comp coreV.subtype) := by
  intro F₁ F₂ h
  apply Subtype.ext
  exact fst_inj _ _ ((mem_coreV _).1 F₁.2).1 ((mem_coreV _).1 F₂.2).1 h

private noncomputable def coreFstIso : ↥coreV ≃* ↥U2F :=
  (MonoidHom.ofInjective fstCore_inj).trans (MulEquiv.subgroupCongr fstCore_range)

private theorem sndCore_range : (sndHom.comp coreV.subtype).range = U3F := by
  ext u
  constructor
  · intro hu
    obtain ⟨F, rfl⟩ := MonoidHom.mem_range.1 hu
    exact Subgroup.mem_map.2 ⟨F.1, F.2, rfl⟩
  · intro hu
    obtain ⟨F, hF, rfl⟩ := Subgroup.mem_map.1 hu
    exact MonoidHom.mem_range.2 ⟨⟨F, hF⟩, rfl⟩

private theorem sndCore_inj : Function.Injective (sndHom.comp coreV.subtype) := by
  intro G₁ G₂ h
  apply Subtype.ext
  exact snd_inj _ _ ((mem_coreV _).1 G₁.2).1 ((mem_coreV _).1 G₂.2).1 h

private noncomputable def coreSndIso : ↥coreV ≃* ↥U3F :=
  (MonoidHom.ofInjective sndCore_inj).trans (MulEquiv.subgroupCongr sndCore_range)

private theorem lin_mem_coreV (b : V3) :
    (Multiplicative.ofAdd (fun v => b ⬝ᵥ v) : Multiplicative (V3 → ZMod 2)) ∈ coreV := by
  rw [mem_coreV]
  refine ⟨?_, ?_⟩
  · show b ⬝ᵥ (0 : V3) = 0
    exact dotProduct_zero _
  · show ∑ v : V3, b ⬝ᵥ v = 0
    exact sum_lin_zero _

private theorem lin_mem_coreV' (v : V3) :
    (Multiplicative.ofAdd (fun a => a ⬝ᵥ v) : Multiplicative (V3 → ZMod 2)) ∈ coreV := by
  rw [mem_coreV]
  refine ⟨?_, ?_⟩
  · show (0 : V3) ⬝ᵥ v = 0
    exact zero_dotProduct _
  · show ∑ a : V3, a ⬝ᵥ v = 0
    exact sum_lin_zero' _

private theorem betaV_add' (F G : V3 → ZMod 2) : betaV (F + G) = betaV F + betaV G := by
  unfold betaV
  simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]

private theorem betaV_zero_fun : betaV (0 : V3 → ZMod 2) = 0 := by
  unfold betaV
  simp

private def betaAdd : (V3 → ZMod 2) →+ V3 where
  toFun := betaV
  map_zero' := betaV_zero_fun
  map_add' := betaV_add'

private noncomputable def betaHom : Multiplicative (V3 → ZMod 2) →* Multiplicative V3 :=
  AddMonoidHom.toMultiplicative betaAdd

private theorem betaHom_apply (F : Multiplicative (V3 → ZMod 2)) :
    betaHom F = Multiplicative.ofAdd (betaV (Multiplicative.toAdd F)) :=
  rfl

set_option maxHeartbeats 1000000 in
private theorem betaV_lin : ∀ b : V3, betaV (fun x => b ⬝ᵥ x) = 0 := by
  decide

set_option maxHeartbeats 1000000 in
private theorem betaD_lin : ∀ v : V3, betaD (fun a => a ⬝ᵥ v) = 0 := by
  decide

set_option maxHeartbeats 1000000 in
private theorem betaV_indPt12_ne : betaV indPt12 ≠ 0 := by
  decide

set_option maxHeartbeats 1000000 in
private theorem betaD_indDu12_ne : betaD indDu12 ≠ 0 := by
  decide

private theorem indPt12_coreV :
    (Multiplicative.ofAdd indPt12 : Multiplicative (V3 → ZMod 2)) ∈ coreV := by
  rw [mem_coreV]
  refine ⟨?_, ?_⟩
  · exact (by decide : indPt12 0 = 0)
  · exact (by decide : ∑ v : V3, indPt12 v = 0)

private theorem indDu12_coreV :
    (Multiplicative.ofAdd indDu12 : Multiplicative (V3 → ZMod 2)) ∈ coreV := by
  rw [mem_coreV]
  refine ⟨?_, ?_⟩
  · exact (by decide : indDu12 0 = 0)
  · exact (by decide : ∑ v : V3, indDu12 v = 0)

private theorem betaD_add' (F G : V3 → ZMod 2) : betaD (F + G) = betaD F + betaD G := by
  unfold betaD
  simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]

private theorem betaD_zero_fun : betaD (0 : V3 → ZMod 2) = 0 := by
  unfold betaD
  simp

private def betaDAdd : (V3 → ZMod 2) →+ V3 where
  toFun := betaD
  map_zero' := betaD_zero_fun
  map_add' := betaD_add'

private noncomputable def betaDHom : Multiplicative (V3 → ZMod 2) →* Multiplicative V3 :=
  AddMonoidHom.toMultiplicative betaDAdd

private theorem coreFst_symm_coe' (u : ↥U2F) :
    fstHom ((coreFstIso.symm u : ↥coreV) : Multiplicative (V3 → ZMod 2)) = (u : MF) :=
  congrArg Subtype.val (coreFstIso.apply_symm_apply u)

private theorem coreSnd_symm_coe' (u : ↥U3F) :
    sndHom ((coreSndIso.symm u : ↥coreV) : Multiplicative (V3 → ZMod 2)) = (u : MF) :=
  congrArg Subtype.val (coreSndIso.apply_symm_apply u)

private theorem iso_U2_rad : IsoSecIn ρF U2F K2F (Multiplicative V3) modNat ⊤ := by
  have hβ0 : betaV (Multiplicative.toAdd (Multiplicative.ofAdd indPt12 :
      Multiplicative (V3 → ZMod 2))) ≠ 0 := by
    rw [toAdd_ofAdd]
    exact betaV_indPt12_ne
  have hwW : fstHom (Multiplicative.ofAdd indPt12 : Multiplicative (V3 → ZMod 2)) ∈ U2F :=
    Subgroup.mem_map.2 ⟨_, indPt12_coreV, rfl⟩
  refine ⟨K2F_le_U2F, U2F_inv, K2F_inv,
    (betaHom.comp coreV.subtype).comp coreFstIso.symm.toMonoidHom, ?_, ?_, ?_⟩
  · ext v
    constructor
    · intro _
      exact Subgroup.mem_top _
    · intro _
      obtain ⟨F', hF', -, hβF'⟩ :=
        core_lift U2F U2F_inv _ indPt12_coreV hwW hβ0 (Multiplicative.toAdd v)
      refine MonoidHom.mem_range.2 ⟨coreFstIso ⟨F', hF'⟩, ?_⟩
      have hsymm : coreFstIso.symm (coreFstIso ⟨F', hF'⟩) = ⟨F', hF'⟩ :=
        coreFstIso.symm_apply_apply _
      have e1 : (((coreFstIso.symm (coreFstIso ⟨F', hF'⟩)) : ↥coreV) :
          Multiplicative (V3 → ZMod 2)) = F' :=
        congrArg Subtype.val hsymm
      have e2 : betaV (Multiplicative.toAdd (((coreFstIso.symm (coreFstIso ⟨F', hF'⟩)) : ↥coreV) :
          Multiplicative (V3 → ZMod 2))) = Multiplicative.toAdd v := by
        rw [e1]
        exact hβF'
      exact (congrArg Multiplicative.ofAdd e2).trans (ofAdd_toAdd v)
  · intro u
    constructor
    · intro h
      have h' : Multiplicative.ofAdd (betaV (Multiplicative.toAdd
          ((coreFstIso.symm u : ↥coreV) : Multiplicative (V3 → ZMod 2)))) = 1 := h
      have h0 := ofAdd_eq_one.1 h'
      have hK := core_beta_zero_mem _ (coreFstIso.symm u).2 h0
      exact (congrArg (fun x => x ∈ K2F) (coreFst_symm_coe' u)).mp hK
    · intro h
      obtain ⟨b, -, hb⟩ := Subgroup.mem_map.1 h
      have hfst : fstHom (Multiplicative.ofAdd (fun v => Multiplicative.toAdd b ⬝ᵥ v)) =
          linFstHom b := by
        have := fst_eq_linFst_of (fun v => Multiplicative.toAdd b ⬝ᵥ v) (Multiplicative.toAdd b)
          (fun x => rfl)
        rwa [ofAdd_toAdd] at this
      have hsymm : coreFstIso.symm u =
          ⟨Multiplicative.ofAdd (fun v => Multiplicative.toAdd b ⬝ᵥ v),
            lin_mem_coreV (Multiplicative.toAdd b)⟩ :=
        (MulEquiv.symm_apply_eq _).2 (Subtype.ext (hfst.trans hb).symm)
      have e2 : ((coreFstIso.symm u : ↥coreV) : Multiplicative (V3 → ZMod 2)) =
          Multiplicative.ofAdd (fun v => Multiplicative.toAdd b ⬝ᵥ v) :=
        congrArg Subtype.val hsymm
      have e3 : betaV (Multiplicative.toAdd
          ((coreFstIso.symm u : ↥coreV) : Multiplicative (V3 → ZMod 2))) = 0 := by
        rw [e2, toAdd_ofAdd]
        exact betaV_lin _
      exact congrArg Multiplicative.ofAdd e3
  · intro g u u' h
    have hu'eq : (u' : MF) = fstHom (Multiplicative.ofAdd (fun v =>
        Multiplicative.toAdd ((coreFstIso.symm u : ↥coreV) : Multiplicative (V3 → ZMod 2))
          (gPt g⁻¹ v))) :=
      h.trans ((congrArg (ρF g) (coreFst_symm_coe' u).symm).trans (ρF_fst g _))
    have hF'' : coreFstIso.symm u' = ⟨Multiplicative.ofAdd (fun v =>
        Multiplicative.toAdd ((coreFstIso.symm u : ↥coreV) : Multiplicative (V3 → ZMod 2))
          (gPt g⁻¹ v)),
          coreV_comp g _ (coreFstIso.symm u).2⟩ :=
      (MulEquiv.symm_apply_eq _).2 (Subtype.ext hu'eq)
    have e1 : ((coreFstIso.symm u' : ↥coreV) : Multiplicative (V3 → ZMod 2)) =
        Multiplicative.ofAdd (fun v =>
          Multiplicative.toAdd ((coreFstIso.symm u : ↥coreV) : Multiplicative (V3 → ZMod 2))
            (gPt g⁻¹ v)) :=
      congrArg Subtype.val hF''
    show Multiplicative.ofAdd (betaV (Multiplicative.toAdd
        ((coreFstIso.symm u' : ↥coreV) : Multiplicative (V3 → ZMod 2)))) =
      modNat g (Multiplicative.ofAdd
          (betaV (Multiplicative.toAdd
            ((coreFstIso.symm u : ↥coreV) : Multiplicative (V3 → ZMod 2)))))
    rw [e1, toAdd_ofAdd, betaV_comp g (Multiplicative.toAdd
      ((coreFstIso.symm u : ↥coreV) : Multiplicative (V3 → ZMod 2)))]
    rfl

private theorem iso_U3_rad : IsoSecIn ρF U3F K3F (Multiplicative V3) modDual ⊤ := by
  have hβ0 : betaD (Multiplicative.toAdd (Multiplicative.ofAdd indDu12 :
      Multiplicative (V3 → ZMod 2))) ≠ 0 := by
    rw [toAdd_ofAdd]
    exact betaD_indDu12_ne
  have hwW : sndHom (Multiplicative.ofAdd indDu12 : Multiplicative (V3 → ZMod 2)) ∈ U3F :=
    Subgroup.mem_map.2 ⟨_, indDu12_coreV, rfl⟩
  refine ⟨K3F_le_U3F, U3F_inv, K3F_inv,
    (betaDHom.comp coreV.subtype).comp coreSndIso.symm.toMonoidHom, ?_, ?_, ?_⟩
  · ext v
    constructor
    · intro _
      exact Subgroup.mem_top _
    · intro _
      obtain ⟨G', hG', -, hβG'⟩ :=
        dual_lift U3F U3F_inv _ indDu12_coreV hwW hβ0 (Multiplicative.toAdd v)
      refine MonoidHom.mem_range.2 ⟨coreSndIso ⟨G', hG'⟩, ?_⟩
      have hsymm : coreSndIso.symm (coreSndIso ⟨G', hG'⟩) = ⟨G', hG'⟩ :=
        coreSndIso.symm_apply_apply _
      have e1 : (((coreSndIso.symm (coreSndIso ⟨G', hG'⟩)) : ↥coreV) :
          Multiplicative (V3 → ZMod 2)) = G' :=
        congrArg Subtype.val hsymm
      have e2 : betaD (Multiplicative.toAdd (((coreSndIso.symm (coreSndIso ⟨G', hG'⟩)) : ↥coreV) :
          Multiplicative (V3 → ZMod 2))) = Multiplicative.toAdd v := by
        rw [e1]
        exact hβG'
      exact (congrArg Multiplicative.ofAdd e2).trans (ofAdd_toAdd v)
  · intro u
    constructor
    · intro h
      have h' : Multiplicative.ofAdd (betaD (Multiplicative.toAdd
          ((coreSndIso.symm u : ↥coreV) : Multiplicative (V3 → ZMod 2)))) = 1 := h
      have h0 := ofAdd_eq_one.1 h'
      have hK := dual_beta_zero_mem _ (coreSndIso.symm u).2 h0
      exact (congrArg (fun x => x ∈ K3F) (coreSnd_symm_coe' u)).mp hK
    · intro h
      obtain ⟨b, -, hb⟩ := Subgroup.mem_map.1 h
      have hsnd : sndHom (Multiplicative.ofAdd (fun a => a ⬝ᵥ Multiplicative.toAdd b)) =
          linSndHom b := by
        have := snd_eq_linSnd_of (fun a => a ⬝ᵥ Multiplicative.toAdd b) (Multiplicative.toAdd b)
          (fun x => rfl)
        rwa [ofAdd_toAdd] at this
      have hsymm : coreSndIso.symm u =
          ⟨Multiplicative.ofAdd (fun a => a ⬝ᵥ Multiplicative.toAdd b),
            lin_mem_coreV' (Multiplicative.toAdd b)⟩ :=
        (MulEquiv.symm_apply_eq _).2 (Subtype.ext (hsnd.trans hb).symm)
      have e2 : ((coreSndIso.symm u : ↥coreV) : Multiplicative (V3 → ZMod 2)) =
          Multiplicative.ofAdd (fun a => a ⬝ᵥ Multiplicative.toAdd b) :=
        congrArg Subtype.val hsymm
      have e3 : betaD (Multiplicative.toAdd
          ((coreSndIso.symm u : ↥coreV) : Multiplicative (V3 → ZMod 2))) = 0 := by
        rw [e2, toAdd_ofAdd]
        exact betaD_lin _
      exact congrArg Multiplicative.ofAdd e3
  · intro g u u' h
    have hu'eq : (u' : MF) = sndHom (Multiplicative.ofAdd (fun a =>
        Multiplicative.toAdd ((coreSndIso.symm u : ↥coreV) : Multiplicative (V3 → ZMod 2))
          (gDu g⁻¹ a))) :=
      h.trans ((congrArg (ρF g) (coreSnd_symm_coe' u).symm).trans (ρF_snd g _))
    have hG'' : coreSndIso.symm u' = ⟨Multiplicative.ofAdd (fun a =>
        Multiplicative.toAdd ((coreSndIso.symm u : ↥coreV) : Multiplicative (V3 → ZMod 2))
          (gDu g⁻¹ a)),
          coreV_compD g _ (coreSndIso.symm u).2⟩ :=
      (MulEquiv.symm_apply_eq _).2 (Subtype.ext hu'eq)
    have e1 : ((coreSndIso.symm u' : ↥coreV) : Multiplicative (V3 → ZMod 2)) =
        Multiplicative.ofAdd (fun a =>
          Multiplicative.toAdd ((coreSndIso.symm u : ↥coreV) : Multiplicative (V3 → ZMod 2))
            (gDu g⁻¹ a)) :=
      congrArg Subtype.val hG''
    show Multiplicative.ofAdd (betaD (Multiplicative.toAdd
        ((coreSndIso.symm u' : ↥coreV) : Multiplicative (V3 → ZMod 2)))) =
      modDual g (Multiplicative.ofAdd
          (betaD (Multiplicative.toAdd
            ((coreSndIso.symm u : ↥coreV) : Multiplicative (V3 → ZMod 2)))))
    rw [e1, toAdd_ofAdd, betaD_comp g (Multiplicative.toAdd
      ((coreSndIso.symm u : ↥coreV) : Multiplicative (V3 → ZMod 2)))]
    rfl


attribute [local instance] cosetFintype

private noncomputable def invOfEquiv {X : Type*} [Fintype X] (e : X ≃ {v : V3 // v ≠ 0})
    (F : X → ZMod 2) (v : V3) : ZMod 2 :=
  if h : v = 0 then 0 else F (e.symm ⟨v, h⟩)

private theorem invOfEquiv_zero {X : Type*} [Fintype X] (e : X ≃ {v : V3 // v ≠ 0})
    (F : X → ZMod 2) : invOfEquiv e F 0 = 0 := by
  unfold invOfEquiv
  rw [dif_pos rfl]

private theorem invOfEquiv_apply {X : Type*} [Fintype X] (e : X ≃ {v : V3 // v ≠ 0})
    (F : X → ZMod 2) (q : X) : invOfEquiv e F (e q).1 = F q := by
  unfold invOfEquiv
  rw [dif_neg (e q).2]
  exact congrArg F (e.symm_apply_apply q)

private theorem sum_invOfEquiv {X : Type*} [Fintype X] (e : X ≃ {v : V3 // v ≠ 0})
    (F : X → ZMod 2) : ∑ v : V3, invOfEquiv e F v = ∑ q : X, F q := by
  rw [← sum_sub_ne_zero (invOfEquiv e F) (invOfEquiv_zero e F)]
  have h2 : ∑ w : {v : V3 // v ≠ 0}, invOfEquiv e F w.1 =
      ∑ w : {v : V3 // v ≠ 0}, F (e.symm w) := by
    apply Finset.sum_congr rfl
    intro w _
    unfold invOfEquiv
    rw [dif_neg w.2]
  rw [h2]
  exact Equiv.sum_comp e.symm F

private theorem kappa_surj (p : V3) (hp : p ≠ 0) (v : V3) (hv : v ≠ 0) :
    ∃ q : GL (Fin 3) (ZMod 2) ⧸ Lpt p, kappa p q = v := by
  obtain ⟨g, hg⟩ := exists_gl_map p v hp hv
  exact ⟨QuotientGroup.mk g, hg⟩

private noncomputable def gammaP (p : V3) :
    (V3 → ZMod 2) →+ (GL (Fin 3) (ZMod 2) ⧸ Lpt p → ZMod 2) where
  toFun F := fun q => F (kappa p q)
  map_zero' := rfl
  map_add' _ _ := rfl

private theorem gammaP_mem_permCore (p : V3) (hp : p ≠ 0)
    (F : Multiplicative (V3 → ZMod 2)) (hF : F ∈ coreV) :
    AddMonoidHom.toMultiplicative (gammaP p) F ∈ permCore (GL (Fin 3) (ZMod 2) ⧸ Lpt p) := by
  obtain ⟨h0, hs⟩ := (mem_coreV F).1 hF
  refine (mem_permCore_iff p _).2 ?_
  calc ∑ q, Multiplicative.toAdd (AddMonoidHom.toMultiplicative (gammaP p) F) q
      = ∑ q, Multiplicative.toAdd F (kappa p q) := rfl
    _ = ∑ w : {v : V3 // v ≠ 0}, Multiplicative.toAdd F w.1 :=
        Equiv.sum_comp (kappaEquiv p hp) (fun w => Multiplicative.toAdd F w.1)
    _ = ∑ v, Multiplicative.toAdd F v := sum_sub_ne_zero (fun v => Multiplicative.toAdd F v) h0
    _ = 0 := hs

private theorem exists_core_of_permCore (p : V3) (hp : p ≠ 0)
    (G : Multiplicative (GL (Fin 3) (ZMod 2) ⧸ Lpt p → ZMod 2))
    (hG : G ∈ permCore (GL (Fin 3) (ZMod 2) ⧸ Lpt p)) :
    ∃ F : Multiplicative (V3 → ZMod 2), F ∈ coreV ∧
      AddMonoidHom.toMultiplicative (gammaP p) F = G := by
  have hG' := (mem_permCore_iff p G).1 hG
  refine ⟨Multiplicative.ofAdd (invOfEquiv (kappaEquiv p hp) (Multiplicative.toAdd G)), ?_, ?_⟩
  · rw [mem_coreV]
    refine ⟨?_, ?_⟩
    · exact invOfEquiv_zero (kappaEquiv p hp) (Multiplicative.toAdd G)
    · show ∑ v : V3, invOfEquiv (kappaEquiv p hp) (Multiplicative.toAdd G) v = 0
      rw [sum_invOfEquiv]
      exact hG'
  · apply Multiplicative.toAdd.injective
    funext q
    exact invOfEquiv_apply (kappaEquiv p hp) (Multiplicative.toAdd G) q

private noncomputable def betaCoreP (p : V3) :
    ↥U2F →* Multiplicative (GL (Fin 3) (ZMod 2) ⧸ Lpt p → ZMod 2) :=
  (AddMonoidHom.toMultiplicative (gammaP p)).comp (coreV.subtype.comp coreFstIso.symm.toMonoidHom)

private theorem iso_U2_core (p : V3) (hp : p ≠ 0) :
    IsoSecIn ρF U2F ⊥ (Multiplicative (GL (Fin 3) (ZMod 2) ⧸ Lpt p → ZMod 2)) (permLH (Lpt p))
      (permCore (GL (Fin 3) (ZMod 2) ⧸ Lpt p)) := by
  refine ⟨bot_le, U2F_inv, fun g z hz => ?_, betaCoreP p, ?_, ?_, ?_⟩
  · have hz1 : z = 1 := Subgroup.mem_bot.1 hz
    subst hz1
    exact Subgroup.mem_bot.2 (map_one (ρF g))
  · ext G
    constructor
    · intro hG
      obtain ⟨u, rfl⟩ := MonoidHom.mem_range.1 hG
      exact gammaP_mem_permCore p hp _ (coreFstIso.symm u).2
    · intro hG
      obtain ⟨F, hF, hFG⟩ := exists_core_of_permCore p hp G hG
      refine MonoidHom.mem_range.2 ⟨coreFstIso ⟨F, hF⟩, ?_⟩
      have hsymm : coreFstIso.symm (coreFstIso ⟨F, hF⟩) = ⟨F, hF⟩ :=
        coreFstIso.symm_apply_apply _
      exact (congrArg (fun x => AddMonoidHom.toMultiplicative (gammaP p) x)
        (congrArg Subtype.val hsymm)).trans hFG
  · intro u
    constructor
    · intro h
      have h' : AddMonoidHom.toMultiplicative (gammaP p)
          ((coreFstIso.symm u : ↥coreV) : Multiplicative (V3 → ZMod 2)) = 1 := h
      have hz : (gammaP p) (Multiplicative.toAdd
          ((coreFstIso.symm u : ↥coreV) : Multiplicative (V3 → ZMod 2))) = 0 :=
        congrArg Multiplicative.toAdd h'
      have hzero : Multiplicative.toAdd
          ((coreFstIso.symm u : ↥coreV) : Multiplicative (V3 → ZMod 2)) = 0 := by
        funext v
        by_cases hv : v = 0
        · rw [hv]
          exact ((mem_coreV _).1 (coreFstIso.symm u).2).1
        · obtain ⟨q, hq⟩ := kappa_surj p hp v hv
          have h2 : Multiplicative.toAdd
              ((coreFstIso.symm u : ↥coreV) : Multiplicative (V3 → ZMod 2)) (kappa p q) = 0 :=
            congrFun hz q
          rw [hq] at h2
          exact h2
      have hF1 : ((coreFstIso.symm u : ↥coreV) : Multiplicative (V3 → ZMod 2)) = 1 :=
        Multiplicative.toAdd.injective (hzero.trans toAdd_one.symm)
      exact Subgroup.mem_bot.2 ((coreFst_symm_coe' u).symm.trans
        ((congrArg fstHom hF1).trans (map_one fstHom)))
    · intro h
      rw [Subgroup.mem_bot] at h
      have hu : u = 1 := Subtype.ext h
      subst hu
      exact map_one _
  · intro g u u' h
    have hu'eq : (u' : MF) = fstHom (Multiplicative.ofAdd (fun v =>
        Multiplicative.toAdd ((coreFstIso.symm u : ↥coreV) : Multiplicative (V3 → ZMod 2))
          (gPt g⁻¹ v))) :=
      h.trans ((congrArg (ρF g) (coreFst_symm_coe' u).symm).trans (ρF_fst g _))
    have hF'' : coreFstIso.symm u' = ⟨Multiplicative.ofAdd (fun v =>
        Multiplicative.toAdd ((coreFstIso.symm u : ↥coreV) : Multiplicative (V3 → ZMod 2))
          (gPt g⁻¹ v)), coreV_comp g _ (coreFstIso.symm u).2⟩ :=
      (MulEquiv.symm_apply_eq _).2 (Subtype.ext hu'eq)
    have e1 : ((coreFstIso.symm u' : ↥coreV) : Multiplicative (V3 → ZMod 2)) =
        Multiplicative.ofAdd (fun v => Multiplicative.toAdd
          ((coreFstIso.symm u : ↥coreV) : Multiplicative (V3 → ZMod 2)) (gPt g⁻¹ v)) :=
      congrArg Subtype.val hF''
    refine (congrArg (AddMonoidHom.toMultiplicative (gammaP p)) e1).trans ?_
    apply Multiplicative.toAdd.injective
    funext q
    show Multiplicative.toAdd ((coreFstIso.symm u : ↥coreV) : Multiplicative (V3 → ZMod 2))
        (gPt g⁻¹ (kappa p q)) = Multiplicative.toAdd
          ((coreFstIso.symm u : ↥coreV) : Multiplicative (V3 → ZMod 2)) (kappa p (g⁻¹ • q))
    rw [kappa_smul]
    rfl


private theorem gDu_fix_Lln {l : Submodule (ZMod 2) V3} {a : V3}
    (hal : ∀ v : V3, v ∈ l ↔ a ⬝ᵥ v = 0) (k : GL (Fin 3) (ZMod 2)) (hk : k ∈ Lln l) :
    gDu k a = a := by
  apply dual_eq_of_ker
  intro v
  rw [dot_gDu]
  have hk' := (mem_Lln k l).1 hk
  constructor
  · intro h
    have hw : gPt k⁻¹ v ∈ l := (hal _).2 h
    have hkw := (hk' _ hw).1
    have e : (k : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec (gPt k⁻¹ v) = v :=
      mulVec_inv_mulVec k v
    exact (hal v).1 (e ▸ hkw)
  · intro h
    exact (hal _).1 (hk' v ((hal v).2 h)).2

private theorem Lln_of_gDu_fix {l : Submodule (ZMod 2) V3} {a : V3}
    (hal : ∀ v : V3, v ∈ l ↔ a ⬝ᵥ v = 0) (k : GL (Fin 3) (ZMod 2)) (hgf : gDu k a = a) :
    k ∈ Lln l := by
  have hinv : gDu k⁻¹ a = a := by
    have h := gDu_mul k⁻¹ k a
    rw [inv_mul_cancel, gDu_one, hgf] at h
    exact h.symm
  have key : ∀ w : V3, a ⬝ᵥ gPt k w = a ⬝ᵥ w := by
    intro w
    have h := dot_gDu_gPt k a w
    rw [hgf] at h
    exact h
  have key' : ∀ w : V3, a ⬝ᵥ gPt k⁻¹ w = a ⬝ᵥ w := by
    intro w
    have h := dot_gDu_gPt k⁻¹ a w
    rw [hinv] at h
    exact h
  rw [mem_Lln]
  intro v hv
  have hv0 : a ⬝ᵥ v = 0 := (hal v).1 hv
  exact ⟨(hal _).2 ((key v).trans hv0), (hal _).2 ((key' v).trans hv0)⟩

private noncomputable def dualKappa {l : Submodule (ZMod 2) V3} {a : V3}
    (hal : ∀ v : V3, v ∈ l ↔ a ⬝ᵥ v = 0) : GL (Fin 3) (ZMod 2) ⧸ Lln l → V3 :=
  Quotient.lift (fun g : GL (Fin 3) (ZMod 2) => gDu g a) (by
    intro x y hxy
    have hxy' : x⁻¹ * y ∈ Lln l := QuotientGroup.leftRel_apply.1 hxy
    have hk := gDu_fix_Lln hal (x⁻¹ * y) hxy'
    show gDu x a = gDu y a
    calc gDu x a = gDu x (gDu (x⁻¹ * y) a) := by rw [hk]
      _ = gDu (x * (x⁻¹ * y)) a := (gDu_mul _ _ _).symm
      _ = gDu y a := by rw [mul_inv_cancel_left])

private theorem dualKappa_smul {l : Submodule (ZMod 2) V3} {a : V3}
    (hal : ∀ v : V3, v ∈ l ↔ a ⬝ᵥ v = 0) (h : GL (Fin 3) (ZMod 2))
    (q : GL (Fin 3) (ZMod 2) ⧸ Lln l) :
    dualKappa hal (h • q) = gDu h (dualKappa hal q) := by
  refine QuotientGroup.induction_on q (fun g => ?_)
  exact gDu_mul h g a

private theorem dualKappa_ne_zero {l : Submodule (ZMod 2) V3} {a : V3}
    (hal : ∀ v : V3, v ∈ l ↔ a ⬝ᵥ v = 0) (ha0 : a ≠ 0) (q : GL (Fin 3) (ZMod 2) ⧸ Lln l) :
    dualKappa hal q ≠ 0 := by
  refine QuotientGroup.induction_on q (fun g => ?_)
  exact gDu_ne g ha0

private theorem dualKappa_injective {l : Submodule (ZMod 2) V3} {a : V3}
    (hal : ∀ v : V3, v ∈ l ↔ a ⬝ᵥ v = 0) (q₁ q₂ : GL (Fin 3) (ZMod 2) ⧸ Lln l)
    (h : dualKappa hal q₁ = dualKappa hal q₂) : q₁ = q₂ := by
  obtain ⟨g₁, rfl⟩ := QuotientGroup.mk_surjective q₁
  obtain ⟨g₂, rfl⟩ := QuotientGroup.mk_surjective q₂
  have h' : gDu g₁ a = gDu g₂ a := h
  rw [QuotientGroup.eq]
  apply Lln_of_gDu_fix hal
  rw [gDu_mul, ← h', ← gDu_mul, inv_mul_cancel, gDu_one]

private theorem dualKappa_surj {l : Submodule (ZMod 2) V3} {a : V3}
    (hal : ∀ v : V3, v ∈ l ↔ a ⬝ᵥ v = 0) (ha0 : a ≠ 0) (b : V3) (hb : b ≠ 0) :
    ∃ q : GL (Fin 3) (ZMod 2) ⧸ Lln l, dualKappa hal q = b := by
  obtain ⟨g, hg⟩ := dualTrans2 a b ha0 hb
  exact ⟨QuotientGroup.mk g, hg⟩

private noncomputable def dualKappaEquiv {l : Submodule (ZMod 2) V3} {a : V3}
    (hal : ∀ v : V3, v ∈ l ↔ a ⬝ᵥ v = 0) (ha0 : a ≠ 0) :
    GL (Fin 3) (ZMod 2) ⧸ Lln l ≃ {v : V3 // v ≠ 0} :=
  Equiv.ofBijective (fun q => ⟨dualKappa hal q, dualKappa_ne_zero hal ha0 q⟩)
    ⟨fun q₁ q₂ h => dualKappa_injective hal q₁ q₂ (congrArg Subtype.val h),
      fun w => by
        obtain ⟨q, hq⟩ := dualKappa_surj hal ha0 w.1 w.2
        exact ⟨q, Subtype.ext hq⟩⟩

private noncomputable def cosetFintypeLln (l : Submodule (ZMod 2) V3) :
    Fintype (GL (Fin 3) (ZMod 2) ⧸ Lln l) :=
  Fintype.ofFinite _

attribute [local instance] cosetFintypeLln

private theorem mem_permCore_iffLln (l : Submodule (ZMod 2) V3)
    (x : Multiplicative (GL (Fin 3) (ZMod 2) ⧸ Lln l → ZMod 2)) :
    x ∈ CFSG.ASVolI.ChH.permCore (GL (Fin 3) (ZMod 2) ⧸ Lln l) ↔
      ∑ q : GL (Fin 3) (ZMod 2) ⧸ Lln l, Multiplicative.toAdd x q = 0 := by
  unfold CFSG.ASVolI.ChH.permCore
  simp only [Multiplicative.mem_toSubgroup, AddMonoidHom.mem_ker, AddMonoidHom.finset_sum_apply,
    Pi.evalAddMonoidHom_apply]
  rfl

private noncomputable def gammaD {l : Submodule (ZMod 2) V3} {a : V3}
    (hal : ∀ v : V3, v ∈ l ↔ a ⬝ᵥ v = 0) :
    (V3 → ZMod 2) →+ (GL (Fin 3) (ZMod 2) ⧸ Lln l → ZMod 2) where
  toFun F := fun q => F (dualKappa hal q)
  map_zero' := rfl
  map_add' _ _ := rfl

private theorem gammaD_mem_permCore {l : Submodule (ZMod 2) V3} {a : V3}
    (hal : ∀ v : V3, v ∈ l ↔ a ⬝ᵥ v = 0) (ha0 : a ≠ 0)
    (G : Multiplicative (V3 → ZMod 2)) (hG : G ∈ coreV) :
    AddMonoidHom.toMultiplicative (gammaD hal) G ∈
      permCore (GL (Fin 3) (ZMod 2) ⧸ Lln l) := by
  obtain ⟨h0, hs⟩ := (mem_coreV G).1 hG
  refine (mem_permCore_iffLln l _).2 ?_
  calc ∑ q, Multiplicative.toAdd (AddMonoidHom.toMultiplicative (gammaD hal) G) q
      = ∑ q, Multiplicative.toAdd G (dualKappa hal q) := rfl
    _ = ∑ w : {v : V3 // v ≠ 0}, Multiplicative.toAdd G w.1 :=
        Equiv.sum_comp (dualKappaEquiv hal ha0) (fun w => Multiplicative.toAdd G w.1)
    _ = ∑ v, Multiplicative.toAdd G v := sum_sub_ne_zero (fun v => Multiplicative.toAdd G v) h0
    _ = 0 := hs

private theorem exists_core_of_permCore_Lln {l : Submodule (ZMod 2) V3} {a : V3}
    (hal : ∀ v : V3, v ∈ l ↔ a ⬝ᵥ v = 0) (ha0 : a ≠ 0)
    (G : Multiplicative (GL (Fin 3) (ZMod 2) ⧸ Lln l → ZMod 2))
    (hG : G ∈ permCore (GL (Fin 3) (ZMod 2) ⧸ Lln l)) :
    ∃ F : Multiplicative (V3 → ZMod 2), F ∈ coreV ∧
      AddMonoidHom.toMultiplicative (gammaD hal) F = G := by
  have hG' := (mem_permCore_iffLln l G).1 hG
  refine ⟨Multiplicative.ofAdd (invOfEquiv (dualKappaEquiv hal ha0) (Multiplicative.toAdd G)),
    ?_, ?_⟩
  · rw [mem_coreV]
    refine ⟨?_, ?_⟩
    · exact invOfEquiv_zero (dualKappaEquiv hal ha0) (Multiplicative.toAdd G)
    · show ∑ v : V3, invOfEquiv (dualKappaEquiv hal ha0) (Multiplicative.toAdd G) v = 0
      rw [sum_invOfEquiv]
      exact hG'
  · apply Multiplicative.toAdd.injective
    funext q
    exact invOfEquiv_apply (dualKappaEquiv hal ha0) (Multiplicative.toAdd G) q

private noncomputable def betaCoreD {l : Submodule (ZMod 2) V3} {a : V3}
    (hal : ∀ v : V3, v ∈ l ↔ a ⬝ᵥ v = 0) :
    ↥U3F →* Multiplicative (GL (Fin 3) (ZMod 2) ⧸ Lln l → ZMod 2) :=
  (AddMonoidHom.toMultiplicative (gammaD hal)).comp
    (coreV.subtype.comp coreSndIso.symm.toMonoidHom)

private theorem iso_U3_core {l : Submodule (ZMod 2) V3} {a : V3}
    (hal : ∀ v : V3, v ∈ l ↔ a ⬝ᵥ v = 0) (ha0 : a ≠ 0) :
    IsoSecIn ρF U3F ⊥ (Multiplicative (GL (Fin 3) (ZMod 2) ⧸ Lln l → ZMod 2)) (permLH (Lln l))
      (permCore (GL (Fin 3) (ZMod 2) ⧸ Lln l)) := by
  refine ⟨bot_le, U3F_inv, fun g z hz => ?_, betaCoreD hal, ?_, ?_, ?_⟩
  · have hz1 : z = 1 := Subgroup.mem_bot.1 hz
    subst hz1
    exact Subgroup.mem_bot.2 (map_one (ρF g))
  · ext G
    constructor
    · intro hG
      obtain ⟨u, rfl⟩ := MonoidHom.mem_range.1 hG
      exact gammaD_mem_permCore hal ha0 _ (coreSndIso.symm u).2
    · intro hG
      obtain ⟨F, hF, hFG⟩ := exists_core_of_permCore_Lln hal ha0 G hG
      refine MonoidHom.mem_range.2 ⟨coreSndIso ⟨F, hF⟩, ?_⟩
      have hsymm : coreSndIso.symm (coreSndIso ⟨F, hF⟩) = ⟨F, hF⟩ :=
        coreSndIso.symm_apply_apply _
      exact (congrArg (fun x => AddMonoidHom.toMultiplicative (gammaD hal) x)
        (congrArg Subtype.val hsymm)).trans hFG
  · intro u
    constructor
    · intro h
      have h' : AddMonoidHom.toMultiplicative (gammaD hal)
          ((coreSndIso.symm u : ↥coreV) : Multiplicative (V3 → ZMod 2)) = 1 := h
      have hz : (gammaD hal) (Multiplicative.toAdd
          ((coreSndIso.symm u : ↥coreV) : Multiplicative (V3 → ZMod 2))) = 0 :=
        congrArg Multiplicative.toAdd h'
      have hzero : Multiplicative.toAdd
          ((coreSndIso.symm u : ↥coreV) : Multiplicative (V3 → ZMod 2)) = 0 := by
        funext v
        by_cases hv : v = 0
        · rw [hv]
          exact ((mem_coreV _).1 (coreSndIso.symm u).2).1
        · obtain ⟨q, hq⟩ := dualKappa_surj hal ha0 v hv
          have h2 : Multiplicative.toAdd
              ((coreSndIso.symm u : ↥coreV) : Multiplicative (V3 → ZMod 2))
                (dualKappa hal q) = 0 :=
            congrFun hz q
          rw [hq] at h2
          exact h2
      have hG1 : ((coreSndIso.symm u : ↥coreV) : Multiplicative (V3 → ZMod 2)) = 1 :=
        Multiplicative.toAdd.injective (hzero.trans toAdd_one.symm)
      exact Subgroup.mem_bot.2 ((coreSnd_symm_coe' u).symm.trans
        ((congrArg sndHom hG1).trans (map_one sndHom)))
    · intro h
      rw [Subgroup.mem_bot] at h
      have hu : u = 1 := Subtype.ext h
      subst hu
      exact map_one _
  · intro g u u' h
    have hu'eq : (u' : MF) = sndHom (Multiplicative.ofAdd (fun a' =>
        Multiplicative.toAdd ((coreSndIso.symm u : ↥coreV) : Multiplicative (V3 → ZMod 2))
          (gDu g⁻¹ a'))) :=
      h.trans ((congrArg (ρF g) (coreSnd_symm_coe' u).symm).trans (ρF_snd g _))
    have hG'' : coreSndIso.symm u' = ⟨Multiplicative.ofAdd (fun a' =>
        Multiplicative.toAdd ((coreSndIso.symm u : ↥coreV) : Multiplicative (V3 → ZMod 2))
          (gDu g⁻¹ a')), coreV_compD g _ (coreSndIso.symm u).2⟩ :=
      (MulEquiv.symm_apply_eq _).2 (Subtype.ext hu'eq)
    have e1 : ((coreSndIso.symm u' : ↥coreV) : Multiplicative (V3 → ZMod 2)) =
        Multiplicative.ofAdd (fun a' => Multiplicative.toAdd
          ((coreSndIso.symm u : ↥coreV) : Multiplicative (V3 → ZMod 2)) (gDu g⁻¹ a')) :=
      congrArg Subtype.val hG''
    refine (congrArg (AddMonoidHom.toMultiplicative (gammaD hal)) e1).trans ?_
    apply Multiplicative.toAdd.injective
    funext q
    show Multiplicative.toAdd ((coreSndIso.symm u : ↥coreV) : Multiplicative (V3 → ZMod 2))
        (gDu g⁻¹ (dualKappa hal q)) = Multiplicative.toAdd
          ((coreSndIso.symm u : ↥coreV) : Multiplicative (V3 → ZMod 2)) (dualKappa hal (g⁻¹ • q))
    rw [dualKappa_smul]


private noncomputable def iotaRad : Multiplicative V3 × Multiplicative V3 →* MF where
  toFun z := linSndHom z.1 * linFstHom z.2
  map_one' := by simp
  map_mul' z w := by
    simp only [Prod.fst_mul, Prod.snd_mul, map_mul]
    exact mul_mul_mul_comm _ _ _ _

private theorem iotaRad_injective : Function.Injective iotaRad := by
  rw [injective_iff_map_eq_one]
  intro z hz
  have hz' : linSndHom z.1 * linFstHom z.2 = 1 := hz
  have hA : linSndHom z.1 ∈ K3F := Subgroup.mem_map.2 ⟨z.1, Subgroup.mem_top _, rfl⟩
  have hB : linFstHom z.2 ∈ K2F := Subgroup.mem_map.2 ⟨z.2, Subgroup.mem_top _, rfl⟩
  have hAB : linSndHom z.1 = (linFstHom z.2)⁻¹ := eq_inv_of_mul_eq_one_left hz'
  have hAK2 : linSndHom z.1 ∈ K2F := by
    rw [hAB]
    exact K2F.inv_mem hB
  have hinf : K2F ⊓ K3F = ⊥ := setupF.inf_K
  have hA1 : linSndHom z.1 = 1 := by
    have hmem : linSndHom z.1 ∈ K2F ⊓ K3F := ⟨hAK2, hA⟩
    exact Subgroup.mem_bot.1 ((congrArg (fun H : Subgroup MF => linSndHom z.1 ∈ H) hinf).mp hmem)
  have hB1 : linFstHom z.2 = 1 := by
    have h := hz'
    rw [hA1, one_mul] at h
    exact h
  have hz1 : Multiplicative.toAdd z.1 = 0 := by
    apply key_lin_du
    intro φ
    have h := congrArg (fun F : MF => Multiplicative.toAdd F φ) hA1
    exact h
  have hz2 : Multiplicative.toAdd z.2 = 0 := by
    apply key_lin_point
    intro φ
    have h := congrArg (fun F : MF => Multiplicative.toAdd F φ) hB1
    exact h
  exact Prod.ext (Multiplicative.toAdd.injective (hz1.trans toAdd_one.symm))
    (Multiplicative.toAdd.injective (hz2.trans toAdd_one.symm))

private theorem iotaRad_range : iotaRad.range = K2F ⊔ K3F := by
  ext w
  constructor
  · intro hw
    obtain ⟨z, rfl⟩ := MonoidHom.mem_range.1 hw
    exact Subgroup.mul_mem _
      (Subgroup.mem_sup_right (Subgroup.mem_map.2 ⟨z.1, Subgroup.mem_top _, rfl⟩))
      (Subgroup.mem_sup_left (Subgroup.mem_map.2 ⟨z.2, Subgroup.mem_top _, rfl⟩))
  · intro hw
    obtain ⟨k2, hk2, k3, hk3, hkw⟩ := Subgroup.mem_sup.1 hw
    obtain ⟨y, -, rfl⟩ := Subgroup.mem_map.1 hk2
    obtain ⟨x, -, rfl⟩ := Subgroup.mem_map.1 hk3
    refine MonoidHom.mem_range.2 ⟨(x, y), ?_⟩
    show linSndHom x * linFstHom y = w
    rw [← hkw]
    exact mul_comm _ _

private noncomputable def isoRad : Multiplicative V3 × Multiplicative V3 ≃* ↥(K2F ⊔ K3F) :=
  (MonoidHom.ofInjective iotaRad_injective).trans (MulEquiv.subgroupCongr iotaRad_range)

private theorem card_multV3 : Nat.card (Multiplicative V3) = 8 := by
  show Nat.card V3 = 8
  simp [Nat.card_fun]

private theorem card_rad : Nat.card ↥(K2F ⊔ K3F) = 64 := by
  rw [← Nat.card_congr isoRad.toEquiv, Nat.card_prod, card_multV3]

private theorem iso_rad :
    IsoSecIn ρF (K2F ⊔ K3F) ⊥ (Multiplicative V3 × Multiplicative V3)
      (prodAct modNat modDual) ⊤ := by
  refine ⟨bot_le, ArtH62.inv_sup_of K2F_inv K3F_inv, fun g z hz => ?_,
    isoRad.symm.toMonoidHom, ?_, ?_, ?_⟩
  · have hz1 : z = 1 := Subgroup.mem_bot.1 hz
    subst hz1
    exact Subgroup.mem_bot.2 (map_one (ρF g))
  · ext z
    constructor
    · intro _
      exact Subgroup.mem_top _
    · intro _
      exact MonoidHom.mem_range.2 ⟨isoRad z, isoRad.symm_apply_apply z⟩
  · intro u
    constructor
    · intro h
      have h' : isoRad.symm u = 1 := h
      have hu : u = 1 :=
        (isoRad.apply_symm_apply u).symm.trans ((congrArg isoRad h').trans (map_one isoRad))
      exact Subgroup.mem_bot.2 (congrArg Subtype.val hu)
    · intro h
      rw [Subgroup.mem_bot] at h
      have hu : u = 1 := Subtype.ext h
      subst hu
      exact map_one _
  · intro g u u' h
    have hu : (u : MF) = iotaRad (isoRad.symm u) :=
      (congrArg Subtype.val (isoRad.apply_symm_apply u)).symm
    have hact : ρF g (iotaRad (isoRad.symm u)) = iotaRad
        (Multiplicative.ofAdd (gPt g (Multiplicative.toAdd (isoRad.symm u).1)),
          Multiplicative.ofAdd (gDu g (Multiplicative.toAdd (isoRad.symm u).2))) :=
      (map_mul (ρF g) _ _).trans (congrArg₂ (· * ·) (ρF_linSnd g _) (ρF_linFst g _))
    have hu' : (u' : MF) = iotaRad
        (Multiplicative.ofAdd (gPt g (Multiplicative.toAdd (isoRad.symm u).1)),
          Multiplicative.ofAdd (gDu g (Multiplicative.toAdd (isoRad.symm u).2))) :=
      h.trans ((congrArg (ρF g) hu).trans hact)
    have hsymm : isoRad.symm u' =
        (Multiplicative.ofAdd (gPt g (Multiplicative.toAdd (isoRad.symm u).1)),
          Multiplicative.ofAdd (gDu g (Multiplicative.toAdd (isoRad.symm u).2))) :=
      (MulEquiv.symm_apply_eq isoRad).2 (Subtype.ext hu')
    exact hsymm


private theorem tr_isoSec_bot {G : Type*} [Group G] {X Y : Type*} [CommGroup X] [CommGroup Y]
    {ρ : G →* MulAut X} {ρ' : G →* MulAut Y} (e : Y ≃* X)
    (hρ : ∀ g y, e (ρ' g y) = ρ g (e y)) {U : Subgroup Y}
    {A : Type*} [CommGroup A] {act : G →* MulAut A} {S : Subgroup A}
    (h : IsoSecIn ρ' U ⊥ A act S) : IsoSecIn ρ (U.map e.toMonoidHom) ⊥ A act S := by
  have h' := tr_isoSec e hρ h
  rwa [Subgroup.map_bot] at h'

private def flag0 (p a : V3) (hp : p ≠ 0) (ha : a ≠ 0) (hpa : a ⬝ᵥ p = 0) : Fl :=
  ⟨(p, a), hp, ha, hpa⟩

private theorem H62_main (T : Subgroup (GL (Fin 3) (ZMod 2))) (p : V3)
    (l : Submodule (ZMod 2) V3) (a : V3) (hyp : HypH5 T p l) (ha0 : a ≠ 0)
    (hal : ∀ v : V3, v ∈ l ↔ a ⬝ᵥ v = 0) (E : MF ≃* PermLT T)
    (hρ : ∀ (g : GL (Fin 3) (ZMod 2)) (F : MF), E (ρF g F) = permLH T g (E F)) :
    ∃ U₁ U₂ U₃ U₄ : Subgroup (PermLT T),
      (∀ g, ∀ u ∈ U₁, permLH T g u ∈ U₁) ∧ (∀ g, ∀ u ∈ U₂, permLH T g u ∈ U₂) ∧
      (∀ g, ∀ u ∈ U₃, permLH T g u ∈ U₃) ∧ (∀ g, ∀ u ∈ U₄, permLH T g u ∈ U₄) ∧
      U₁ ⊔ U₂ ⊔ U₃ ⊔ U₄ = ⊤ ∧
      U₁ ⊓ (U₂ ⊔ U₃ ⊔ U₄) = ⊥ ∧ U₂ ⊓ (U₁ ⊔ U₃ ⊔ U₄) = ⊥ ∧
      U₃ ⊓ (U₁ ⊔ U₂ ⊔ U₄) = ⊥ ∧ U₄ ⊓ (U₁ ⊔ U₂ ⊔ U₃) = ⊥ ∧
      IsoSecIn (permLH T) U₁ ⊥ (Multiplicative (ZMod 2)) modTriv ⊤ ∧
      IsoSecIn (permLH T) U₂ ⊥ (Multiplicative ((GL (Fin 3) (ZMod 2) ⧸ Lpt p) → ZMod 2))
        (permLH (Lpt p)) (permCore (GL (Fin 3) (ZMod 2) ⧸ Lpt p)) ∧
      IsoSecIn (permLH T) U₂ (radSub (permLH T) U₂) (Multiplicative V3) modNat ⊤ ∧
      IsoSecIn (permLH T) U₃ ⊥ (Multiplicative ((GL (Fin 3) (ZMod 2) ⧸ Lln l) → ZMod 2))
        (permLH (Lln l)) (permCore (GL (Fin 3) (ZMod 2) ⧸ Lln l)) ∧
      IsoSecIn (permLH T) U₃ (radSub (permLH T) U₃) (Multiplicative V3) modDual ⊤ ∧
      IsoSecIn (permLH T) U₄ ⊥ AdjAmb adjAmbAct Adj3 ∧
      (radSub (permLH T) ⊤ = radSub (permLH T) U₂ ⊔ radSub (permLH T) U₃ ∧
        radSub (permLH T) U₂ ⊓ radSub (permLH T) U₃ = ⊥ ∧
        IsoSecIn (permLH T) (radSub (permLH T) ⊤) ⊥ (Multiplicative V3 × Multiplicative V3)
          (prodAct modNat modDual) ⊤ ∧
        rk ↥(radSub (permLH T) ⊤) = 6) := by
  have hp : p ≠ 0 := hyp.p_ne
  have eU2 : radSub (permLH T) (U2F.map E.toMonoidHom) = K2F.map E.toMonoidHom :=
    (tr_radSub E hρ U2F).trans (congrArg (fun H => H.map E.toMonoidHom) setupF.rad_U2)
  have eU3 : radSub (permLH T) (U3F.map E.toMonoidHom) = K3F.map E.toMonoidHom :=
    (tr_radSub E hρ U3F).trans (congrArg (fun H => H.map E.toMonoidHom) setupF.rad_U3)
  have htop : (⊤ : Subgroup (PermLT T)) = (⊤ : Subgroup MF).map E.toMonoidHom :=
    (Subgroup.map_top_of_surjective E.toMonoidHom E.surjective).symm
  have eTop : radSub (permLH T) (⊤ : Subgroup (PermLT T)) = (K2F ⊔ K3F).map E.toMonoidHom := by
    rw [htop]
    exact (tr_radSub E hρ ⊤).trans (congrArg (fun H => H.map E.toMonoidHom) setupF.rad_top)
  have iU2rad : IsoSecIn (permLH T) (U2F.map E.toMonoidHom)
      (radSub (permLH T) (U2F.map E.toMonoidHom)) (Multiplicative V3) modNat ⊤ := by
    rw [eU2]
    exact tr_isoSec E hρ iso_U2_rad
  have iU3rad : IsoSecIn (permLH T) (U3F.map E.toMonoidHom)
      (radSub (permLH T) (U3F.map E.toMonoidHom)) (Multiplicative V3) modDual ⊤ := by
    rw [eU3]
    exact tr_isoSec E hρ iso_U3_rad
  have irad : IsoSecIn (permLH T) (radSub (permLH T) (⊤ : Subgroup (PermLT T))) ⊥
      (Multiplicative V3 × Multiplicative V3) (prodAct modNat modDual) ⊤ := by
    rw [eTop]
    exact tr_isoSec_bot E hρ iso_rad
  have hsumT : U1F.map E.toMonoidHom ⊔ U2F.map E.toMonoidHom ⊔ U3F.map E.toMonoidHom ⊔
      U4F.map E.toMonoidHom = ⊤ := by
    have h : (U1F ⊔ U2F ⊔ U3F ⊔ U4F).map E.toMonoidHom =
        (⊤ : Subgroup MF).map E.toMonoidHom := congrArg (fun H => H.map E.toMonoidHom) dsum_top
    rw [Subgroup.map_sup, Subgroup.map_sup, Subgroup.map_sup,
      Subgroup.map_top_of_surjective E.toMonoidHom E.surjective] at h
    exact h
  have hI1 : U1F.map E.toMonoidHom ⊓ (U2F.map E.toMonoidHom ⊔ U3F.map E.toMonoidHom ⊔
      U4F.map E.toMonoidHom) = ⊥ := by
    rw [← Subgroup.map_sup, ← Subgroup.map_sup, ← Subgroup.map_inf_eq _ _ E.toMonoidHom E.injective,
      dsum_inter1, Subgroup.map_bot]
  have hI2 : U2F.map E.toMonoidHom ⊓ (U1F.map E.toMonoidHom ⊔ U3F.map E.toMonoidHom ⊔
      U4F.map E.toMonoidHom) = ⊥ := by
    rw [← Subgroup.map_sup, ← Subgroup.map_sup, ← Subgroup.map_inf_eq _ _ E.toMonoidHom E.injective,
      dsum_inter2, Subgroup.map_bot]
  have hI3 : U3F.map E.toMonoidHom ⊓ (U1F.map E.toMonoidHom ⊔ U2F.map E.toMonoidHom ⊔
      U4F.map E.toMonoidHom) = ⊥ := by
    rw [← Subgroup.map_sup, ← Subgroup.map_sup, ← Subgroup.map_inf_eq _ _ E.toMonoidHom E.injective,
      dsum_inter3, Subgroup.map_bot]
  have hI4 : U4F.map E.toMonoidHom ⊓ (U1F.map E.toMonoidHom ⊔ U2F.map E.toMonoidHom ⊔
      U3F.map E.toMonoidHom) = ⊥ := by
    rw [← Subgroup.map_sup, ← Subgroup.map_sup, ← Subgroup.map_inf_eq _ _ E.toMonoidHom E.injective,
      dsum_inter4, Subgroup.map_bot]
  have hRadSum : radSub (permLH T) (⊤ : Subgroup (PermLT T)) =
      radSub (permLH T) (U2F.map E.toMonoidHom) ⊔ radSub (permLH T) (U3F.map E.toMonoidHom) := by
    rw [eTop, eU2, eU3, Subgroup.map_sup]
    rfl
  have hRadInf : radSub (permLH T) (U2F.map E.toMonoidHom) ⊓
      radSub (permLH T) (U3F.map E.toMonoidHom) = ⊥ := by
    rw [eU2, eU3]
    exact (Subgroup.map_inf_eq K2F K3F E.toMonoidHom E.injective).symm.trans
      ((congrArg (fun H => H.map E.toMonoidHom) setupF.inf_K).trans (Subgroup.map_bot _))
  have hcard : Nat.card ↥(radSub (permLH T) (⊤ : Subgroup (PermLT T))) = 64 := by
    rw [eTop]
    exact (Nat.card_congr (Subgroup.equivMapOfInjective (K2F ⊔ K3F) E.toMonoidHom
      E.injective).toEquiv).symm.trans card_rad
  have hrk : rk ↥(radSub (permLH T) (⊤ : Subgroup (PermLT T))) = 6 := by
    show padicValNat 2 (Nat.card ↥(radSub (permLH T) (⊤ : Subgroup (PermLT T)))) = 6
    rw [hcard]
    have h64 : (64 : ℕ) = 2 ^ 6 := by norm_num
    rw [h64]
    exact padicValNat.prime_pow 6
  exact ⟨U1F.map E.toMonoidHom, U2F.map E.toMonoidHom, U3F.map E.toMonoidHom, U4F.map E.toMonoidHom,
    tr_inv E hρ U1F_inv, tr_inv E hρ U2F_inv, tr_inv E hρ U3F_inv, tr_inv E hρ U4F_inv,
    hsumT, hI1, hI2, hI3, hI4,
    tr_isoSec_bot E hρ iso_U1, tr_isoSec_bot E hρ (iso_U2_core p hp), iU2rad,
    tr_isoSec_bot E hρ (iso_U3_core hal ha0), iU3rad, tr_isoSec_bot E hρ iso_U4,
    hRadSum, hRadInf, irad, hrk⟩

end FlagH62

open FlagH62 in
theorem as_H_6_2 : H_6_2 := by
  intro T p l hyp
  obtain ⟨a, ha0, hal, hap⟩ := exists_dual hyp
  have hT : ∀ t ∈ T, t • flag0 p a hyp.p_ne ha0 hap = flag0 p a hyp.p_ne ha0 hap := by
    intro t ht
    exact Subtype.ext (Prod.ext (hyp.p_fix t ht) (gDu_fix hyp hal t ht))
  have hstab : ∀ x : GL (Fin 3) (ZMod 2),
      x • flag0 p a hyp.p_ne ha0 hap = flag0 p a hyp.p_ne ha0 hap → x ∈ T := by
    intro x hx
    exact stab_mem hyp hal x (congrArg (fun φ : Fl => φ.1.1) hx)
      (congrArg (fun φ : Fl => φ.1.2) hx)
  have hθ := thetaOf_bijective T _ hT hstab (card_quot hyp)
  exact H62_main T p l a hyp ha0 hal (eqT T _ hT hθ) (eqT_equiv T _ hT hθ)

end CFSG.ASVolI
