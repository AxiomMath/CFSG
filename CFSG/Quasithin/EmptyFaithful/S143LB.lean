module

public import CFSG.Quasithin.EmptyFaithful.S143LA
public import CFSG.Quasithin.Background.B3ThreeCoh

public section

namespace CFSG.Quasithin.S143

open CFSG.Quasithin.B3 CFSG.Quasithin.S143.A6Model

instance instCommGroupN6 : CommGroup N6 :=
  { (inferInstance : Group N6) with mul_comm := fun a b => Subtype.ext (mul_comm a.1 b.1) }

@[expose] def n6ActL : LG 6 →* MulAut N6 := n6Act.comp (alternatingGroup (Fin 6)).subtype

@[expose] def n6ToU (a : N6) : U 6 := ⟨Multiplicative.toAdd a.1⟩

theorem n6ToU_mul (a b : N6) : n6ToU (a * b) = n6ToU a * n6ToU b := U.ext fun _ => rfl

theorem n6ToU_mem (a : N6) : n6ToU a ∈ U0 6 := by
  show wt 6 (n6ToU a) = 1
  have h2 : wt 6 (n6ToU a) = Multiplicative.ofAdd (∑ i, (n6ToU a).val i) := rfl
  rw [h2]
  have h := (mem_n6Sub_iff.1 a.2).1
  show Multiplicative.ofAdd (∑ i, Multiplicative.toAdd a.1 i) = 1
  rw [h]
  rfl

theorem esub_of_const (x y : U 6) (c : ZMod 2) (h : ∀ i, y.val i = x.val i + c) :
    x⁻¹ * y ∈ Esub 6 := by
  have hc' : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide
  rw [mem_Esub_iff]
  rcases hc' c with rfl | rfl
  · left
    apply U.ext
    intro i
    simp [h i]
    exact neg_add_cancel _
  · right
    apply U.ext
    intro i
    simp [h i, eVec]
    exact neg_add_cancel_left _ _

@[expose] noncomputable def pi6 : ↥(U0 6) →* Mod.V 6 Mod.ut0 :=
  QuotientGroup.mk' ((Esub 6).subgroupOf (U0 6))

theorem pi6_eq_iff (x y : ↥(U0 6)) : pi6 x = pi6 y ↔ (x : U 6)⁻¹ * (y : U 6) ∈ Esub 6 := by
  show (QuotientGroup.mk x : ↥(U0 6) ⧸ (Esub 6).subgroupOf (U0 6)) = QuotientGroup.mk y ↔ _
  rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
  rfl

theorem pi6_surjective : Function.Surjective pi6 := QuotientGroup.mk'_surjective _

theorem act_pi6 (σ : Equiv.Perm (Fin 6)) (w : ↥(U0 6)) :
    Mod.act 6 Mod.ut0 σ (pi6 w) = pi6 ⟨permAct 6 σ w, isInv_U0 6 σ w w.2⟩ := rfl

@[expose] def n6ToU0 : N6 →* ↥(U0 6) :=
  MonoidHom.mk' (fun a => ⟨n6ToU a, n6ToU_mem a⟩) (fun a b => Subtype.ext (n6ToU_mul a b))

@[expose] noncomputable def n6ToV : N6 →* Mod.V 6 Mod.ut0 := pi6.comp n6ToU0

theorem n6ToV_apply (a : N6) : n6ToV a = pi6 ⟨n6ToU a, n6ToU_mem a⟩ := rfl

private theorem zmod_two_add_self' (x : ZMod 2) : x + x = 0 := by
  revert x
  decide

theorem n6ToV_act (σ : LG 6) (a : N6) : n6ToV (n6ActL σ a) = actL 6 Mod.ut0 σ (n6ToV a) := by
  rw [n6ToV_apply, n6ToV_apply, actL_apply, act_pi6, pi6_eq_iff]
  refine esub_of_const _ _ (Multiplicative.toAdd a.1 (σ.1⁻¹ 5)) fun i => ?_
  show Multiplicative.toAdd a.1 (σ.1.symm i) = Multiplicative.toAdd (n6Act σ.1 a).1 i + _
  rw [n6Act_val]
  show _ = Multiplicative.toAdd a.1 (σ.1⁻¹ i) + Multiplicative.toAdd a.1 (σ.1⁻¹ 5) +
    Multiplicative.toAdd a.1 (σ.1⁻¹ 5)
  rw [add_assoc, zmod_two_add_self', add_zero]
  rfl

theorem n6ToV_injective : Function.Injective n6ToV := by
  rw [injective_iff_map_eq_one]
  intro a ha
  have h1 : pi6 ⟨n6ToU a, n6ToU_mem a⟩ = pi6 1 := by rw [map_one]; exact ha
  rw [pi6_eq_iff] at h1
  have h2 : n6ToU a ∈ Esub 6 := by simpa using h1
  rcases (mem_Esub_iff _).1 h2 with h | h
  · apply Subtype.ext
    apply Multiplicative.toAdd.injective
    funext i
    have := congrArg (fun u : U 6 => u.val i) h
    exact this
  · exfalso
    have h5 := (mem_n6Sub_iff.1 a.2).2
    have := congrArg (fun u : U 6 => u.val 5) h
    simp only [n6ToU, eVec] at this
    rw [h5] at this
    exact zero_ne_one this

theorem n6ToV_surjective : Function.Surjective n6ToV := by
  intro v
  obtain ⟨w, rfl⟩ := pi6_surjective v
  have hw : ∑ i, (w : U 6).val i = 0 := by
    have h1 : wt 6 (w : U 6) = 1 := w.2
    have h2 : wt 6 (w : U 6) = Multiplicative.ofAdd (∑ i, (w : U 6).val i) := rfl
    rw [h2] at h1
    exact ofAdd_eq_one.mp h1
  let f : Fin 6 → ZMod 2 := fun i => (w : U 6).val i + (w : U 6).val 5
  have hf : Multiplicative.ofAdd f ∈ n6Sub := by
    refine mem_n6Sub_iff.2 ⟨?_, ?_⟩
    · rw [toAdd_ofAdd]
      show ∑ i, ((w : U 6).val i + (w : U 6).val 5) = 0
      rw [Finset.sum_add_distrib, hw, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
      have : (6 : ℕ) • (w : U 6).val 5 = 0 := by
        generalize (w : U 6).val 5 = x
        revert x
        decide
      rw [this, add_zero]
    · rw [toAdd_ofAdd]
      exact zmod_two_add_self' _
  refine ⟨⟨Multiplicative.ofAdd f, hf⟩, ?_⟩
  rw [n6ToV_apply, pi6_eq_iff]
  refine esub_of_const _ _ ((w : U 6).val 5) fun i => ?_
  show (w : U 6).val i = (w : U 6).val i + (w : U 6).val 5 + (w : U 6).val 5
  rw [add_assoc, zmod_two_add_self', add_zero]

@[expose] noncomputable def n6ModEquiv : N6 ≃* Mod.V 6 Mod.ut0 :=
  MulEquiv.ofBijective n6ToV ⟨n6ToV_injective, n6ToV_surjective⟩

theorem n6ModEquiv_apply (a : N6) : n6ModEquiv a = n6ToV a := rfl

theorem n6ModEquiv_isModIso :
    IsModIso (V := N6) (V' := Mod.V 6 Mod.ut0) n6ActL (actL 6 Mod.ut0) n6ModEquiv :=
  fun σ a => n6ToV_act σ a

@[expose] def e0vec : Fin 6 → ZMod 2 := (vecOfNat 6 1).val

theorem e0vec_five : e0vec 5 = 0 := by
  show (if (1 : ℕ).testBit 5 then (1 : ZMod 2) else 0) = 0
  decide

theorem dW_vec_eq (a : N6) (σ : Equiv.Perm (Fin 6)) :
    dW (Multiplicative.toAdd a.1) σ = n6Act σ a * a⁻¹ := by
  have h5 := (mem_n6Sub_iff.1 a.2).2
  have hinv : a⁻¹ = a := inv_eq_of_mul_eq_one_right (n6_mul_self a)
  rw [hinv]
  apply Subtype.ext
  apply Multiplicative.toAdd.injective
  funext i
  show rawD _ σ i = Multiplicative.toAdd (n6Act σ a).1 i + Multiplicative.toAdd a.1 i
  rw [n6Act_val]
  simp only [rawD, Pi.add_apply]
  rw [n6Norm_one _ h5]
  rfl

theorem d0_eq (σ : LG 6) : d0 6 Mod.ut0 σ = n6ToV (dW e0vec σ.1) := by
  have hm := inWk_d0m (n := 6) (k := Mod.ut0) (Or.inr rfl) (popPar_one_false (Or.inr (Or.inl rfl)))
    σ.1
  show toV 6 Mod.ut0 (actM 6 (tab σ.1) 1 ^^^ 1) = _
  rw [toV_of_inW hm, n6ToV_apply]
  show pi6 ⟨vecOfNat 6 (actM 6 (tab σ.1) 1 ^^^ 1), _⟩ = pi6 ⟨n6ToU (dW e0vec σ.1), _⟩
  rw [pi6_eq_iff]
  refine esub_of_const _ _ (e0vec (σ.1⁻¹ 5)) fun i => ?_
  show rawD e0vec σ.1 i = (vecOfNat 6 (actM 6 (tab σ.1) 1 ^^^ 1)).val i + e0vec (σ.1⁻¹ 5)
  rw [vecOfNat_xor, vecOfNat_actM, U.val_mul, permAct_val]
  simp only [rawD, Pi.add_apply, n6Norm, inv_one, Equiv.Perm.coe_one, id_eq, e0vec_five]
  show _ = e0vec (σ.1.symm i) + e0vec i + e0vec (σ.1⁻¹ 5)
  have : σ.1.symm i = σ.1⁻¹ i := rfl
  rw [this]
  ring

theorem z1_N6 (d : LG 6 → N6) (hd : IsDer n6ActL d) :
    ∃ w : Fin 6 → ZMod 2, ∀ σ : LG 6, d σ = dW w σ.1 := by
  have hmod := n6ModEquiv_isModIso
  have hd' : IsDer (actL 6 Mod.ut0) (fun σ => n6ModEquiv (d σ)) := hmod.isDer hd
  obtain ⟨_, _, hall⟩ := H1_natural_even (n := 6) (Or.inl rfl)
  have hinvV : ∀ v : Mod.V 6 Mod.ut0, v⁻¹ = v := fun v =>
    inv_eq_of_mul_eq_one_right (by rw [← pow_two]; exact V_sq _ v)
  rcases hall _ hd' with ⟨v, hv⟩ | ⟨v, hv⟩
  · obtain ⟨a, rfl⟩ := n6ModEquiv.surjective v
    refine ⟨Multiplicative.toAdd a.1, fun σ => ?_⟩
    have h1 := congrFun hv σ
    apply n6ModEquiv.injective
    rw [h1, dW_vec_eq]
    simp only [pder, map_mul, map_inv]
    exact congrArg (· * (n6ModEquiv a)⁻¹) (hmod σ a).symm
  · obtain ⟨a, rfl⟩ := n6ModEquiv.surjective v
    refine ⟨Multiplicative.toAdd a.1 + e0vec, fun σ => ?_⟩
    have h1 := congrFun hv σ
    simp only [Pi.mul_apply, pder] at h1
    have h2 : n6ModEquiv (d σ) =
        (actL 6 Mod.ut0 σ (n6ModEquiv a) * (n6ModEquiv a)⁻¹) * (d0 6 Mod.ut0 σ)⁻¹ :=
      eq_mul_inv_of_mul_eq h1
    rw [hinvV (d0 6 Mod.ut0 σ)] at h2
    rw [dW_add, dW_vec_eq]
    apply n6ModEquiv.injective
    rw [h2, d0_eq, map_mul, map_mul, map_inv, ← hmod σ a]
    rfl

end CFSG.Quasithin.S143
