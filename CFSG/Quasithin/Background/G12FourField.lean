module

public import CFSG.Quasithin.Background.G12Part4

public section

namespace CFSG.Quasithin.G11

section NoInst

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V]

@[expose] def fourEndK (K : Subgroup (GLV V)) : Subalgebra (ZMod 2) (Module.End (ZMod 2) V) :=
  Subalgebra.centralizer (ZMod 2) {T | ∃ k ∈ K, T = (k : V →ₗ[ZMod 2] V)}

theorem mem_fourEndK {K : Subgroup (GLV V)} {T : Module.End (ZMod 2) V} :
    T ∈ fourEndK K ↔ G12CommK K T := by
  rw [fourEndK, Subalgebra.mem_centralizer_iff]
  constructor
  · intro h k hk x
    have := congrArg (fun S : Module.End (ZMod 2) V => S x) (h _ ⟨k, hk, rfl⟩)
    exact this.symm
  · rintro h _ ⟨k, hk, rfl⟩
    exact LinearMap.ext fun x => (h k hk x).symm

section Fin

variable [Finite V] {K : Subgroup (GLV V)}

theorem g12f_endK_isUnit (hirr : IsIrr K ⊤) (T : fourEndK K) : IsUnit T ∨ T = 0 := by
  by_cases h0 : T = 0
  · exact Or.inr h0
  left
  have hT : G12CommK K (T : Module.End (ZMod 2) V) := mem_fourEndK.1 T.2
  have hT0 : (T : Module.End (ZMod 2) V) ≠ 0 := fun h => h0 (Subtype.ext h)
  have hinj := hT.injective hirr hT0
  let e := LinearEquiv.ofInjectiveEndo (T : Module.End (ZMod 2) V) hinj
  have h1 : ∀ y, (T : Module.End (ZMod 2) V) (e.symm y) = y := fun y => by
    have := e.apply_symm_apply y
    rwa [LinearEquiv.coe_ofInjectiveEndo] at this
  have hS : (e.symm : Module.End (ZMod 2) V) ∈ fourEndK K := by
    rw [mem_fourEndK]
    intro k hk x
    apply hinj
    show (T : Module.End (ZMod 2) V) (e.symm (k x)) = (T : Module.End (ZMod 2) V) (k (e.symm x))
    rw [hT k hk, h1, h1]
  refine ⟨⟨T, ⟨_, hS⟩, ?_, ?_⟩, rfl⟩
  · exact Subtype.ext (LinearEquiv.ofInjectiveEndo_right_inv _ _)
  · exact Subtype.ext (LinearEquiv.ofInjectiveEndo_left_inv _ _)

theorem g12f_finite_endK : Finite (fourEndK K) :=
  Finite.of_injective (fun T : fourEndK K => ((T : Module.End (ZMod 2) V) : V → V))
    (fun _ _ h => Subtype.ext (LinearMap.ext (congrFun h)))

end Fin

variable {K : Subgroup (GLV V)}

@[expose] noncomputable def fourSig (y : GLV V) (hy : ∀ k ∈ K, y⁻¹ * k * y ∈ K) :
    fourEndK K →ₐ[ZMod 2] fourEndK K where
  toFun T := ⟨(y : Module.End (ZMod 2) V) * T * (y.symm : Module.End (ZMod 2) V), by
    rw [mem_fourEndK]
    intro k hk x
    have hT := mem_fourEndK.1 T.2 (y⁻¹ * k * y) (hy k hk) (y.symm x)
    have e1 : (y⁻¹ * k * y) (y.symm x) = y.symm (k x) := by
      show y.symm (k (y (y.symm x))) = y.symm (k x)
      rw [LinearEquiv.apply_symm_apply]
    rw [e1] at hT
    show y ((T : Module.End (ZMod 2) V) (y.symm (k x))) =
      k (y ((T : Module.End (ZMod 2) V) (y.symm x)))
    rw [hT]
    show y (y.symm (k (y ((T : Module.End (ZMod 2) V) (y.symm x))))) = _
    rw [LinearEquiv.apply_symm_apply]⟩
  map_one' := Subtype.ext (LinearMap.ext fun x => by
    show y (y.symm x) = x
    exact LinearEquiv.apply_symm_apply y x)
  map_mul' S T := Subtype.ext (LinearMap.ext fun x => by
    show y ((S : Module.End (ZMod 2) V) ((T : Module.End (ZMod 2) V) (y.symm x))) =
      y ((S : Module.End (ZMod 2) V) (y.symm (y ((T : Module.End (ZMod 2) V) (y.symm x)))))
    rw [LinearEquiv.symm_apply_apply])
  map_zero' := Subtype.ext (LinearMap.ext fun x => by
    show y ((0 : Module.End (ZMod 2) V) (y.symm x)) = 0
    simp)
  map_add' S T := Subtype.ext (LinearMap.ext fun x => by
    show y (((S : Module.End (ZMod 2) V) + (T : Module.End (ZMod 2) V)) (y.symm x)) =
      y ((S : Module.End (ZMod 2) V) (y.symm x)) + y ((T : Module.End (ZMod 2) V) (y.symm x))
    rw [LinearMap.add_apply, map_add])
  commutes' c := Subtype.ext (LinearMap.ext fun x => by
    show y (((algebraMap (ZMod 2) (fourEndK K) c : fourEndK K) : Module.End (ZMod 2) V)
      (y.symm x)) = ((algebraMap (ZMod 2) (fourEndK K) c : fourEndK K) : Module.End (ZMod 2) V) x
    simp [Algebra.algebraMap_eq_smul_one])

@[expose] noncomputable def fourSigE (y : GLV V) (hy : ∀ k ∈ K, y⁻¹ * k * y ∈ K)
    (hy' : ∀ k ∈ K, y⁻¹⁻¹ * k * y⁻¹ ∈ K) : fourEndK K ≃ₐ[ZMod 2] fourEndK K :=
  AlgEquiv.ofAlgHom (fourSig y hy) (fourSig y⁻¹ hy')
    (AlgHom.ext fun T => Subtype.ext (LinearMap.ext fun x => by
      show y (y.symm ((T : Module.End (ZMod 2) V) (y.symm.symm (y.symm x)))) = _
      rw [LinearEquiv.apply_symm_apply, LinearEquiv.symm_symm, LinearEquiv.apply_symm_apply]
      rfl))
    (AlgHom.ext fun T => Subtype.ext (LinearMap.ext fun x => by
      show y.symm (y ((T : Module.End (ZMod 2) V) (y.symm (y.symm.symm x)))) = _
      rw [LinearEquiv.symm_apply_apply, LinearEquiv.symm_symm, LinearEquiv.symm_apply_apply]
      rfl))

@[expose] noncomputable def fourSigHom (Q : Subgroup (GLV V))
    (hQ : ∀ y ∈ Q, ∀ k ∈ K, y⁻¹ * k * y ∈ K) (hQ' : ∀ y ∈ Q, ∀ k ∈ K, y * k * y⁻¹ ∈ K) :
    ↥Q →* (fourEndK K ≃ₐ[ZMod 2] fourEndK K) where
  toFun y := fourSigE y.1 (hQ y.1 y.2) (fun k hk => by rw [inv_inv]; exact hQ' y.1 y.2 k hk)
  map_one' := AlgEquiv.ext fun T => Subtype.ext (LinearMap.ext fun x => rfl)
  map_mul' y z := AlgEquiv.ext fun T => Subtype.ext (LinearMap.ext fun x => rfl)

theorem fourSigHom_apply (Q : Subgroup (GLV V))
    (hQ : ∀ y ∈ Q, ∀ k ∈ K, y⁻¹ * k * y ∈ K) (hQ' : ∀ y ∈ Q, ∀ k ∈ K, y * k * y⁻¹ ∈ K)
    (y : ↥Q) (T : fourEndK K) (x : V) :
    ((fourSigHom Q hQ hQ' y T : fourEndK K) : Module.End (ZMod 2) V) x =
      (y : GLV V) ((T : Module.End (ZMod 2) V) ((y : GLV V).symm x)) := rfl

section Main

variable [Finite V] {K : Subgroup (GLV V)}

theorem g12f_card_endK_le_four (hirr : IsIrr K ⊤) {Q : Subgroup (GLV V)}
    (hQ : ∀ y ∈ Q, ∀ k ∈ K, y⁻¹ * k * y ∈ K) (hQ' : ∀ y ∈ Q, ∀ k ∈ K, y * k * y⁻¹ ∈ K)
    (hQ2 : ∀ a ∈ Q, a * a = 1)
    (hfix : ∀ T : V →ₗ[ZMod 2] V, G12CommK K T → (∀ y ∈ Q, ∀ x, T (y x) = y (T x)) → T ≠ 0 →
      T = LinearMap.id) :
    Nat.card (fourEndK K) ≤ 4 := by
  have hfin : Finite (fourEndK K) := g12f_finite_endK
  have hV : ∃ x : V, x ≠ 0 := by
    by_contra h
    push Not at h
    apply (lt_irrefl (⊥ : Submodule (ZMod 2) V))
    calc (⊥ : Submodule (ZMod 2) V) < ⊤ := hirr.2.1
      _ = ⊥ := eq_bot_iff.2 fun x _ => by rw [h x]; exact Submodule.zero_mem _
  have hnt : Nontrivial (fourEndK K) := by
    obtain ⟨x, hx⟩ := hV
    refine ⟨⟨0, 1, fun h => hx ?_⟩⟩
    have := congrArg (fun S : fourEndK K => (S : Module.End (ZMod 2) V) x) h
    exact this.symm
  let iD : DivisionRing (fourEndK K) := DivisionRing.ofIsUnitOrEqZero (g12f_endK_isUnit hirr)
  let iF : Field (fourEndK K) := littleWedderburn _
  let σ := fourSigHom Q hQ hQ'
  have hfixed : IntermediateField.fixedField (F := ZMod 2) (E := ↥(fourEndK K)) σ.range = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [IntermediateField.mem_fixedField_iff] at hx
    have hcomm : ∀ y ∈ Q, ∀ z,
        (x : Module.End (ZMod 2) V) (y z) = y ((x : Module.End (ZMod 2) V) z) := by
      intro y hy z
      have h := hx (σ ⟨y, hy⟩) ⟨⟨y, hy⟩, rfl⟩
      have h2 := congrArg (fun S : fourEndK K => (S : Module.End (ZMod 2) V) (y z)) h
      rw [fourSigHom_apply, LinearEquiv.symm_apply_apply] at h2
      exact h2.symm
    by_cases hx0 : (x : Module.End (ZMod 2) V) = 0
    · have : x = 0 := Subtype.ext hx0
      rw [this]
      exact IntermediateField.zero_mem _
    · have h1 := hfix _ (mem_fourEndK.1 x.2) hcomm hx0
      have : x = 1 := Subtype.ext h1
      rw [this]
      exact IntermediateField.one_mem _
  have hcard := IntermediateField.finrank_fixedField_eq_card (F := ZMod 2) (E := ↥(fourEndK K)) σ.range
  rw [hfixed, IntermediateField.finrank_bot'] at hcard
  have hG : Nat.card σ.range ≤ 2 := by
    obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := σ.range)
    rw [← orderOf_eq_card_of_forall_mem_zpowers hg]
    obtain ⟨y, hy⟩ := g.2
    have hg2 : g ^ 2 = 1 := by
      apply Subtype.ext
      rw [pow_two, Subgroup.coe_mul, ← hy, ← map_mul,
        show y * y = 1 from Subtype.ext (hQ2 y.1 y.2), map_one]
      rfl
    exact Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one hg2)
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod, hcard]
  calc 2 ^ Nat.card σ.range ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) hG
    _ = 4 := by norm_num

theorem g12f_endK_eq_of_ne (hirr : IsIrr K ⊤) (hcard : Nat.card (fourEndK K) ≤ 4)
    {T : V →ₗ[ZMod 2] V} (hT : G12CommK K T) (hT0 : T ≠ 0) (hT1 : T ≠ LinearMap.id) :
    T * T = T + 1 ∧ ∀ S : V →ₗ[ZMod 2] V, G12CommK K S → S = 0 ∨ S = 1 ∨ S = T ∨ S = T + 1 := by
  have hfin : Finite (fourEndK K) := g12f_finite_endK
  obtain ⟨x0, hx0⟩ : ∃ x : V, x ≠ 0 := by
    by_contra h
    push Not at h
    apply (lt_irrefl (⊥ : Submodule (ZMod 2) V))
    calc (⊥ : Submodule (ZMod 2) V) < ⊤ := hirr.2.1
      _ = ⊥ := eq_bot_iff.2 fun x _ => by rw [h x]; exact Submodule.zero_mem _
  have h11 : (1 : Module.End (ZMod 2) V) + 1 = 0 := g12_vadd_self _
  have hTT : T + T = 0 := g12_vadd_self _
  have h01 : (0 : Module.End (ZMod 2) V) ≠ 1 := fun h => hx0 (by
    have := congrArg (fun S : Module.End (ZMod 2) V => S x0) h
    exact this.symm)
  have hT1' : T ≠ 1 := hT1
  have hTa0 : T + 1 ≠ 0 := fun h => hT1' (by
    calc T = T + (1 + 1) := by rw [h11, add_zero]
      _ = (T + 1) + 1 := by rw [add_assoc]
      _ = 1 := by rw [h, zero_add])
  have hTa1 : T + 1 ≠ 1 := fun h => hT0 (by
    calc T = (T + 1) + 1 := by rw [add_assoc, h11, add_zero]
      _ = 0 := by rw [h, h11])
  have hTaT : T + 1 ≠ T := fun h => h01 (by
    calc (0 : Module.End (ZMod 2) V) = T + T := hTT.symm
      _ = T + (T + 1) := by rw [h]
      _ = 1 := by rw [← add_assoc, hTT, zero_add])
  have hmemT : T ∈ fourEndK K := mem_fourEndK.2 hT
  have hmem1 : T + 1 ∈ fourEndK K := (fourEndK K).add_mem hmemT (fourEndK K).one_mem
  have hall : ∀ S : V →ₗ[ZMod 2] V, G12CommK K S → S = 0 ∨ S = 1 ∨ S = T ∨ S = T + 1 := by
    intro S hS
    by_contra hne
    push Not at hne
    obtain ⟨hS0, hS1, hST, hST1⟩ := hne
    let f : Fin 5 → fourEndK K := ![0, 1, ⟨T, hmemT⟩, ⟨T + 1, hmem1⟩, ⟨S, mem_fourEndK.2 hS⟩]
    have hf : Function.Injective f := by
      intro i j hij
      have hij' := congrArg Subtype.val hij
      fin_cases i <;> fin_cases j <;> first
        | rfl
        | (exfalso; simp only [f, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
            Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.tail_cons,
            ZeroMemClass.coe_zero, OneMemClass.coe_one, Fin.zero_eta, Fin.mk_one,
            Fin.reduceFinMk] at hij'
           first
            | exact h01 hij' | exact h01 hij'.symm | exact hT0 hij'.symm | exact hT0 hij'
            | exact hTa0 hij'.symm | exact hTa0 hij' | exact hS0 hij'.symm | exact hS0 hij'
            | exact hT1' hij'.symm | exact hT1' hij' | exact hTa1 hij'.symm | exact hTa1 hij'
            | exact hS1 hij'.symm | exact hS1 hij' | exact hTaT hij'.symm | exact hTaT hij'
            | exact hST hij'.symm | exact hST hij' | exact hST1 hij'.symm | exact hST1 hij')
    have := Nat.card_le_card_of_injective f hf
    rw [Nat.card_eq_fintype_card, Fintype.card_fin] at this
    omega
  refine ⟨?_, hall⟩
  have hinjT := hT.injective hirr hT0
  have hmTT : T * T ∈ fourEndK K := (fourEndK K).mul_mem hmemT hmemT
  rcases hall (T * T) (mem_fourEndK.1 hmTT) with h | h | h | h
  · exfalso
    apply hx0
    apply hinjT
    apply hinjT
    have := congrArg (fun S : Module.End (ZMod 2) V => S x0) h
    simpa using this
  · exfalso
    have hsq : (T + 1) * (T + 1) = 0 := by
      rw [add_mul, mul_add, mul_add, h, mul_one, one_mul, mul_one, add_assoc, ← add_assoc T T,
        hTT, zero_add, h11]
    have hinj1 := (mem_fourEndK.1 hmem1).injective hirr hTa0
    apply hx0
    apply hinj1
    apply hinj1
    have := congrArg (fun S : Module.End (ZMod 2) V => S x0) hsq
    simpa using this
  · exfalso
    apply hTa0
    apply LinearMap.ext
    intro x
    apply hinjT
    have := congrArg (fun S : Module.End (ZMod 2) V => S x) h
    have e : T ((T + 1) x) = T (T x) + T x := by
      rw [LinearMap.add_apply, map_add, Module.End.one_apply]
    rw [e, LinearMap.zero_apply, map_zero]
    simp only [Module.End.mul_apply] at this
    rw [this, g12_vadd_self]
  · exact h

end Main

end NoInst

end CFSG.Quasithin.G11
