module

public import CFSG.Quasithin.Recognition.M12AscPinCore
public import CFSG.CharacterTheory.Semidihedral.GL2Recognition.SharplyFourTransitiveM11

public section

namespace CFSG.Quasithin.M12Pin

open MulAction Equiv

section Complement

variable {G : Type*} [Group G] {Ω : Type*} [MulAction G Ω]

private instance complAction (w : Ω) : MulAction (stabilizer G w) {x : Ω // x ≠ w} where
  smul g x := ⟨(g : G) • (x : Ω), fun h => x.2 (by
    have hg : (g : G) • w = w := mem_stabilizer_iff.1 g.2
    calc (x : Ω) = (g : G)⁻¹ • ((g : G) • (x : Ω)) := (inv_smul_smul _ _).symm
      _ = (g : G)⁻¹ • w := by rw [h]
      _ = w := inv_smul_eq_iff.2 hg.symm)⟩
  one_smul x := Subtype.ext (one_smul G (x : Ω))
  mul_smul g h x := Subtype.ext (mul_smul (g : G) (h : G) (x : Ω))

private theorem coe_smul_compl (w : Ω) (g : stabilizer G w) (x : {x : Ω // x ≠ w}) :
    ((g • x : {x : Ω // x ≠ w}) : Ω) = (g : G) • (x : Ω) := rfl

private theorem faithful_compl [FaithfulSMul G Ω] (w : Ω) :
    FaithfulSMul (stabilizer G w) {x : Ω // x ≠ w} := by
  refine ⟨fun {g₁ g₂} h => ?_⟩
  apply Subtype.ext
  apply eq_of_smul_eq_smul (α := Ω)
  intro y
  by_cases hy : y = w
  · subst hy
    rw [mem_stabilizer_iff.1 g₁.2, mem_stabilizer_iff.1 g₂.2]
  · exact congrArg Subtype.val (h ⟨y, hy⟩)

private theorem card_compl [Finite Ω] (w : Ω) (hΩ : Nat.card Ω = 12) :
    Nat.card {x : Ω // x ≠ w} = 11 := by
  classical
  have h := Nat.card_congr (Equiv.optionSubtypeNe w)
  rw [Finite.card_option, hΩ] at h
  omega

private theorem sharp4_compl (w : Ω)
    (hsharp : ∀ a b : Fin 5 → Ω, Function.Injective a → Function.Injective b →
      ∃! g : G, ∀ i, g • a i = b i) :
    ∀ a b : Fin 4 → {x : Ω // x ≠ w}, Function.Injective a → Function.Injective b →
      ∃! g : stabilizer G w, ∀ i, g • a i = b i := by
  intro a b ha hb
  have hinj : ∀ c : Fin 4 → {x : Ω // x ≠ w}, Function.Injective c →
      Function.Injective (Fin.cons w (fun i => (c i : Ω)) : Fin 5 → Ω) := by
    intro c hc
    rw [Fin.cons_injective_iff]
    refine ⟨?_, fun i j h => hc (Subtype.ext h)⟩
    rintro ⟨i, hi⟩
    exact (c i).2 hi
  obtain ⟨g, hg, huniq⟩ := hsharp _ _ (hinj a ha) (hinj b hb)
  have hgw : g • w = w := by simpa using hg 0
  refine ⟨⟨g, mem_stabilizer_iff.2 hgw⟩, fun i => Subtype.ext ?_, fun g' hg' => ?_⟩
  · rw [coe_smul_compl]
    simpa using hg i.succ
  refine Subtype.ext (huniq g' fun i => ?_)
  induction i using Fin.cases with
  | zero => simpa using mem_stabilizer_iff.1 g'.2
  | succ j =>
    have h := congrArg Subtype.val (hg' j)
    rw [coe_smul_compl] at h
    simpa using h

private theorem exists_quaternion_compl (w x y z : Ω) (hwx : w ≠ x) (hwy : w ≠ y) (hwz : w ≠ z)
    (ψ : ↥(stabilizer G w ⊓ stabilizer G x ⊓ stabilizer G y ⊓ stabilizer G z) ≃*
      QuaternionGroup 2) :
    Nonempty (↥(stabilizer (stabilizer G w) (⟨x, hwx.symm⟩ : {x : Ω // x ≠ w}) ⊓
      stabilizer (stabilizer G w) (⟨y, hwy.symm⟩ : {x : Ω // x ≠ w}) ⊓
      stabilizer (stabilizer G w) (⟨z, hwz.symm⟩ : {x : Ω // x ≠ w})) ≃* QuaternionGroup 2) := by
  refine ⟨MulEquiv.trans ?_ ψ⟩
  exact
  { toFun := fun m => ⟨(m.1 : G), ⟨⟨⟨m.1.2,
      mem_stabilizer_iff.2 (congrArg Subtype.val (mem_stabilizer_iff.1 m.2.1.1))⟩,
      mem_stabilizer_iff.2 (congrArg Subtype.val (mem_stabilizer_iff.1 m.2.1.2))⟩,
      mem_stabilizer_iff.2 (congrArg Subtype.val (mem_stabilizer_iff.1 m.2.2))⟩⟩
    invFun := fun g => ⟨⟨(g : G), g.2.1.1.1⟩, ⟨⟨mem_stabilizer_iff.2
      (Subtype.ext (mem_stabilizer_iff.1 g.2.1.1.2)),
      mem_stabilizer_iff.2 (Subtype.ext (mem_stabilizer_iff.1 g.2.1.2))⟩,
      mem_stabilizer_iff.2 (Subtype.ext (mem_stabilizer_iff.1 g.2.2))⟩⟩
    left_inv := fun m => rfl
    right_inv := fun g => rfl
    map_mul' := fun a b => rfl }

end Complement

section Labelling

variable {Ω : Type*} [DecidableEq Ω]

@[expose] def liftEquiv (w : Ω) (u : {x : Ω // x ≠ w} ≃ Fin 11) : Ω ≃ Fin 12 :=
  (Equiv.optionSubtypeNe w).symm.trans ((Equiv.optionCongr u).trans (finSuccEquiv 11).symm)

theorem liftEquiv_self (w : Ω) (u : {x : Ω // x ≠ w} ≃ Fin 11) : liftEquiv w u w = 0 := by
  simp [liftEquiv]

theorem liftEquiv_coe (w : Ω) (u : {x : Ω // x ≠ w} ≃ Fin 11) (z : {x : Ω // x ≠ w}) :
    liftEquiv w u z = (u z).succ := by
  simp [liftEquiv, Equiv.optionSubtypeNe_symm_of_ne z.2]

theorem liftEquiv_symm_zero (w : Ω) (u : {x : Ω // x ≠ w} ≃ Fin 11) :
    (liftEquiv w u).symm 0 = w := by
  rw [Equiv.symm_apply_eq, liftEquiv_self]

theorem liftEquiv_symm_succ (w : Ω) (u : {x : Ω // x ≠ w} ≃ Fin 11) (i : Fin 11) :
    (liftEquiv w u).symm i.succ = ((u.symm i : {x : Ω // x ≠ w}) : Ω) := by
  rw [Equiv.symm_apply_eq, liftEquiv_coe, Equiv.apply_symm_apply]

@[expose] def shiftPerm (σ : Perm (Fin 11)) : Perm (Fin 12) :=
  (finSuccEquiv 11).trans ((Equiv.optionCongr σ).trans (finSuccEquiv 11).symm)

theorem shiftPerm_zero (σ : Perm (Fin 11)) : shiftPerm σ 0 = 0 := by simp [shiftPerm]

theorem shiftPerm_succ (σ : Perm (Fin 11)) (i : Fin 11) : shiftPerm σ i.succ = (σ i).succ := by
  simp [shiftPerm]

@[expose] def shiftHom : Perm (Fin 11) →* Perm (Fin 12) where
  toFun := shiftPerm
  map_one' := by
    ext y
    obtain rfl | ⟨i, rfl⟩ := Fin.eq_zero_or_eq_succ y <;> simp [shiftPerm_zero, shiftPerm_succ]
  map_mul' σ τ := by
    ext y
    obtain rfl | ⟨i, rfl⟩ := Fin.eq_zero_or_eq_succ y <;> simp [shiftPerm_zero, shiftPerm_succ]

@[expose] def e0 : Perm (Fin 11) := List.formPerm [4, 7, 9, 8, 10]

@[expose] def relabelHom : Perm (Fin 11) →* Perm (Fin 12) :=
  shiftHom.comp (MulAut.conj e0).toMonoidHom

theorem map_statedM11 : Subgroup.map relabelHom CFSG.Open.StatedM11 = S0 := by
  rw [CFSG.Open.statedM11_eq_closure_cycles]
  unfold S0
  rw [MonoidHom.map_closure, Set.image_pair]
  have h1 : relabelHom (CFSG.Open.StatedCyclePerm 11 [[2, 10], [4, 11], [5, 7], [8, 9]]) = s1 := by
    decide +kernel
  have h2 : relabelHom (CFSG.Open.StatedCyclePerm 11 [[1, 4, 3, 8], [2, 5, 6, 9]]) = s2 := by
    decide +kernel
  rw [h1, h2]

end Labelling

section ActHom

variable {G : Type*} [Group G] {Ω : Type*} [MulAction G Ω]

@[expose] def actHom (G : Type*) (Ω : Type*) [Group G] [MulAction G Ω] (F : Ω ≃ Fin 12) :
    G →* Perm (Fin 12) :=
  (Equiv.permCongrHom F).toMonoidHom.comp (MulAction.toPermHom G Ω)

theorem actHom_apply (F : Ω ≃ Fin 12) (g : G) (y : Fin 12) :
    actHom G Ω F g y = F (g • F.symm y) := by
  simp [actHom, Equiv.permCongrHom_coe, Equiv.permCongr_apply]

theorem actHom_injective [FaithfulSMul G Ω] (F : Ω ≃ Fin 12) :
    Function.Injective (actHom G Ω F) := by
  intro g₁ g₂ h
  apply eq_of_smul_eq_smul (α := Ω)
  intro x
  have := DFunLike.congr_fun h (F x)
  rw [actHom_apply, actHom_apply, Equiv.symm_apply_apply] at this
  exact F.injective this

private theorem hA_of_sharp (F : Ω ≃ Fin 12)
    (hsharp : ∀ a b : Fin 5 → Ω, Function.Injective a → Function.Injective b →
      ∃! g : G, ∀ i, g • a i = b i) :
    ∀ g' ∈ (actHom G Ω F).range, ∀ a : Fin 5 → Fin 12, Function.Injective a →
      (∀ i, g' (a i) = a i) → g' = 1 := by
  rintro _ ⟨g, rfl⟩ a ha hfix
  have ha' : Function.Injective (fun i => F.symm (a i)) := F.symm.injective.comp ha
  obtain ⟨g₀, -, huniq⟩ := hsharp _ _ ha' ha'
  have h1 : g = g₀ := huniq g fun i => by
    have h := hfix i
    rw [actHom_apply] at h
    exact (Equiv.eq_symm_apply F).2 h
  have h2 : (1 : G) = g₀ := huniq 1 fun i => one_smul G _
  rw [h1, ← h2, map_one]

private theorem hτ_of_sharp (F : Ω ≃ Fin 12)
    (hsharp : ∀ a b : Fin 5 → Ω, Function.Injective a → Function.Injective b →
      ∃! g : G, ∀ i, g • a i = b i) :
    ∃ τ ∈ (actHom G Ω F).range, τ 0 = 1 ∧ τ 1 = 0 ∧ τ 2 = 2 ∧ τ 3 = 3 ∧ τ 4 = 4 := by
  have ha : Function.Injective (![0, 1, 2, 3, 4] : Fin 5 → Fin 12) := by decide
  have hb : Function.Injective (![1, 0, 2, 3, 4] : Fin 5 → Fin 12) := by decide
  obtain ⟨g, hg, -⟩ := hsharp (fun i => F.symm (![0, 1, 2, 3, 4] i))
    (fun i => F.symm (![1, 0, 2, 3, 4] i)) (F.symm.injective.comp ha) (F.symm.injective.comp hb)
  have key : ∀ i, actHom G Ω F g (![0, 1, 2, 3, 4] i) = ![1, 0, 2, 3, 4] i := fun i => by
    rw [actHom_apply, hg i, Equiv.apply_symm_apply]
  exact ⟨actHom G Ω F g, ⟨g, rfl⟩, by simpa using key 0, by simpa using key 1,
    by simpa using key 2, by simpa using key 3, by simpa using key 4⟩

end ActHom

section Transport

variable {G : Type*} [Group G] {Ω : Type*} [DecidableEq Ω] [MulAction G Ω]

private theorem actHom_eq_shiftPerm (w : Ω) (u : {x : Ω // x ≠ w} ≃ Fin 11)
    (g : stabilizer G w) (σ : Perm (Fin 11)) (hσ : ∀ i, σ i = u (g • u.symm i)) :
    actHom G Ω (liftEquiv w u) (g : G) = shiftPerm σ := by
  refine Equiv.ext fun y => ?_
  obtain rfl | ⟨i, rfl⟩ := Fin.eq_zero_or_eq_succ y
  · rw [actHom_apply, shiftPerm_zero, liftEquiv_symm_zero, mem_stabilizer_iff.1 g.2,
      liftEquiv_self]
  · rw [actHom_apply, shiftPerm_succ, liftEquiv_symm_succ, hσ]
    exact liftEquiv_coe w u (g • u.symm i)

private theorem mem_S0_iff (w : Ω) (f : {x : Ω // x ≠ w} ≃ Fin 11)
    (hf : ∀ p : Perm (Fin 11), p ∈ CFSG.Open.StatedM11 ↔
      ∃ g : stabilizer G w, ∀ i, p i = f (g • f.symm i)) (g' : Perm (Fin 12)) :
    (g' ∈ (actHom G Ω (liftEquiv w (f.trans e0))).range ∧ g' 0 = 0) ↔ g' ∈ S0 := by
  rw [← map_statedM11]
  constructor
  · rintro ⟨⟨g, rfl⟩, hg0⟩
    have hgw : g • w = w := by
      rw [actHom_apply, liftEquiv_symm_zero] at hg0
      exact (liftEquiv w (f.trans e0)).injective (hg0.trans (liftEquiv_self w _).symm)
    let gM : stabilizer G w := ⟨g, mem_stabilizer_iff.2 hgw⟩
    let p : Perm (Fin 11) := f.permCongr (MulAction.toPerm gM)
    have hp : p ∈ CFSG.Open.StatedM11 := (hf p).2 ⟨gM, fun i => by simp [p]⟩
    refine ⟨p, hp, ?_⟩
    exact (actHom_eq_shiftPerm w (f.trans e0) gM (e0 * p * e0⁻¹) fun i => rfl).symm
  · rintro ⟨p, hp, rfl⟩
    obtain ⟨gM, hgM⟩ := (hf p).1 hp
    have key := actHom_eq_shiftPerm w (f.trans e0) gM (e0 * p * e0⁻¹) fun i => by
      show e0 (p (e0.symm i)) = e0 (f (gM • f.symm (e0.symm i)))
      rw [hgM]
    exact ⟨⟨(gM : G), key⟩, shiftPerm_zero _⟩

end Transport

end CFSG.Quasithin.M12Pin

namespace CFSG.Quasithin

open MulAction Equiv CFSG.Quasithin.M12Pin

theorem isSporadic_M12_of_sharply_five_transitive
    {G : Type} [Group G] [Finite G] {Ω : Type*} [MulAction G Ω] [FaithfulSMul G Ω]
    (hΩ : Nat.card Ω = 12)
    (hsharp : ∀ a b : Fin 5 → Ω, Function.Injective a → Function.Injective b →
      ∃! g : G, ∀ i, g • a i = b i)
    (hQ : ∃ w x y z : Ω, w ≠ x ∧ w ≠ y ∧ w ≠ z ∧ x ≠ y ∧ x ≠ z ∧ y ≠ z ∧
      Nonempty (↥(MulAction.stabilizer G w ⊓ MulAction.stabilizer G x ⊓
        MulAction.stabilizer G y ⊓ MulAction.stabilizer G z) ≃* QuaternionGroup 2)) :
    CFSG.Blueprint.NativeSporadic.IsSporadic G .M12 := by
  classical
  obtain ⟨w, x, y, z, hwx, hwy, hwz, hxy, hxz, hyz, ⟨ψQ⟩⟩ := hQ
  have : Finite Ω := Nat.finite_of_card_ne_zero (by rw [hΩ]; norm_num)
  have : FaithfulSMul (stabilizer G w) {x : Ω // x ≠ w} := faithful_compl w
  obtain ⟨f, hf, -⟩ :=
    CFSG.Semidihedral.GL2Recognition.sharply_four_transitive_quaternion_action_exact_M11
      (G := stabilizer G w) (Ω := {x : Ω // x ≠ w}) (card_compl w hΩ) (sharp4_compl w hsharp)
      ⟨⟨x, hwx.symm⟩, ⟨y, hwy.symm⟩, ⟨z, hwz.symm⟩, fun h => hxy (congrArg Subtype.val h),
        fun h => hxz (congrArg Subtype.val h), fun h => hyz (congrArg Subtype.val h),
        exists_quaternion_compl w x y z hwx hwy hwz ψQ⟩
  have hP : (actHom G Ω (liftEquiv w (f.trans e0))).range =
      CFSG.Blueprint.NativeSporadic.M12 :=
    eq_M12_of_sharply_five_transitive _ (hA_of_sharp _ hsharp) (hτ_of_sharp _ hsharp)
      (mem_S0_iff w f hf)
  exact ⟨(MonoidHom.ofInjective (actHom_injective (liftEquiv w (f.trans e0)))).trans
    (MulEquiv.subgroupCongr hP)⟩

end CFSG.Quasithin
