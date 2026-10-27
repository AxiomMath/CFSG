module

public import CFSG.Quasithin.Background.ShultG53Model
public import CFSG.Quasithin.Background.ShultG53Cyc

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Quasithin.ShultG53

open CFSG.CharacterTheory.SteinbergBY CFSG.Quasithin.RonanG51 Equiv

abbrev Fn : Type := V4 → ZMod 2

@[expose] def Phi : Fn →+ V4 where
  toFun u := ∑ w : V4, u w • w
  map_zero' := by simp
  map_add' a b := by simp [add_smul, Finset.sum_add_distrib]

@[expose] def psi1 : Fn →+ ZMod 2 where
  toFun u := ∑ w : V4, u w * Qf w
  map_zero' := by simp
  map_add' a b := by simp [add_mul, Finset.sum_add_distrib]

@[expose] def Qfun : Fn := fun w => Qf w

@[expose] def Cf (x : V4) : Fn := fun w => B0 w x

theorem Cf_add (x y : V4) : Cf (x + y) = Cf x + Cf y := by
  funext w
  simp only [Cf, B0, Pi.add_apply]
  ring

theorem Cf_zero : Cf 0 = 0 := by
  funext w
  simp [Cf, B0]

@[expose] def Cadd : V4 →+ Fn where
  toFun := Cf
  map_zero' := Cf_zero
  map_add' := Cf_add

@[expose] def Q3 : (ZMod 2 × V4) →+ Fn where
  toFun p := p.1 • Qfun + Cf p.2
  map_zero' := by simp [Cf_zero]
  map_add' a b := by
    simp only [Prod.fst_add, Prod.snd_add, Cf_add, add_smul]
    abel

@[expose] noncomputable def Nk (k : Fin 2) : ℕ → AddSubgroup Fn
  | 0 => permCore (Mk k)
  | 1 => permCore (Mk k) ⊓ Phi.ker
  | 2 => permCore (Mk k) ⊓ Phi.ker ⊓ psi1.ker
  | 3 => Q3.range
  | 4 => Cadd.range
  | _ => ⊥

theorem permAct_apply (k : Fin 2) (g : ↥(alternatingGroup (Fin 6))) (u : Fn) (w : V4) :
    permAct (Mk k) g u w = u (ρk k g⁻¹ w) := rfl

@[expose] noncomputable def eqv (k : Fin 2) (g : ↥(alternatingGroup (Fin 6))) : V4 ≃ V4 where
  toFun := ρk k g
  invFun := ρk k g⁻¹
  left_inv x := by
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
  right_inv x := by
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]

theorem weightHom_apply (k : Fin 2) (u : Fn) : weightHom (Mk k) u = ∑ w : V4, u w :=
  finsum_eq_sum_of_fintype u

theorem mem_permCore (k : Fin 2) (u : Fn) :
    u ∈ permCore (Mk k) ↔ u 0 = 0 ∧ ∑ w : V4, u w = 0 := by
  unfold permCore
  rw [AddSubgroup.mem_inf]
  exact and_congr Iff.rfl (by rw [AddMonoidHom.mem_ker, weightHom_apply])

theorem sum_permAct (k : Fin 2) (g : ↥(alternatingGroup (Fin 6))) (u : Fn) :
    ∑ w : V4, permAct (Mk k) g u w = ∑ w : V4, u w :=
  (eqv k g⁻¹).sum_comp u

theorem permCore_inv (k : Fin 2) : InvSub (permAct (Mk k)) (permCore (Mk k)) := by
  intro g u hu
  rw [mem_permCore] at hu ⊢
  refine ⟨?_, by rw [sum_permAct]; exact hu.2⟩
  show u (ρk k g⁻¹ 0) = 0
  rw [map_zero]
  exact hu.1

theorem phi_equiv (k : Fin 2) (g : ↥(alternatingGroup (Fin 6))) (u : Fn) :
    Phi (permAct (Mk k) g u) = ρk k g (Phi u) := by
  show ∑ w : V4, u (ρk k g⁻¹ w) • w = ρk k g (∑ w : V4, u w • w)
  rw [map_sum]
  simp only [map_smul]
  rw [← (eqv k g).sum_comp]
  refine Finset.sum_congr rfl fun w _ => ?_
  show u (ρk k g⁻¹ (ρk k g w)) • ρk k g w = u w • ρk k g w
  rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]

theorem permAct_Cf (k : Fin 2) (g : ↥(alternatingGroup (Fin 6))) (x : V4) :
    permAct (Mk k) g (Cf x) = Cf (ρk k g x) := by
  funext w
  show B0 (ρk k g⁻¹ w) x = B0 w (ρk k g x)
  have h := B0_inv k g (ρk k g⁻¹ w) x
  have h2 : ρk k g (ρk k g⁻¹ w) = w := (eqv k g).right_inv w
  rw [h2] at h
  exact h.symm

theorem permAct_Qfun (k : Fin 2) (g : ↥(alternatingGroup (Fin 6))) :
    ∃ m : V4, permAct (Mk k) g Qfun = Qfun + Cf m := by
  obtain ⟨m, hm⟩ := qlaw (ρk k g⁻¹) (fun x y => B0_inv k g⁻¹ x y)
  exact ⟨m, funext fun w => hm w⟩

theorem B0_sum (u : Fn) (m : V4) : B0 (Phi u) m = ∑ w : V4, u w * B0 w m := by
  show B0form (∑ w : V4, u w • w) m = _
  rw [← LinearMap.flip_apply, map_sum]
  simp [LinearMap.flip_apply, B0form_apply]

theorem psi1_law (k : Fin 2) (g : ↥(alternatingGroup (Fin 6))) (u : Fn) :
    ∃ m : V4, psi1 (permAct (Mk k) g u) = psi1 u + B0 (Phi u) m := by
  obtain ⟨m, hm⟩ := qlaw (ρk k g) (fun x y => B0_inv k g x y)
  refine ⟨m, ?_⟩
  rw [B0_sum]
  show ∑ w : V4, u (ρk k g⁻¹ w) * Qf w = ∑ w : V4, u w * Qf w + ∑ w : V4, u w * B0 w m
  rw [← Finset.sum_add_distrib, ← (eqv k g).sum_comp]
  refine Finset.sum_congr rfl fun w _ => ?_
  show u (ρk k g⁻¹ (ρk k g w)) * Qf (ρk k g w) = _
  have h2 : ρk k g⁻¹ (ρk k g w) = w := (eqv k g).left_inv w
  rw [h2, hm w]
  ring

theorem N1_inv (k : Fin 2) : InvSub (permAct (Mk k)) (Nk k 1) := by
  intro g u hu
  obtain ⟨h0, h1⟩ := AddSubgroup.mem_inf.mp hu
  refine AddSubgroup.mem_inf.mpr ⟨permCore_inv k g u h0, ?_⟩
  rw [AddMonoidHom.mem_ker, phi_equiv, AddMonoidHom.mem_ker.mp h1, map_zero]

theorem N2_inv (k : Fin 2) : InvSub (permAct (Mk k)) (Nk k 2) := by
  intro g u hu
  obtain ⟨h01, h2⟩ := AddSubgroup.mem_inf.mp hu
  have h1 : permAct (Mk k) g u ∈ Nk k 1 := N1_inv k g u h01
  refine AddSubgroup.mem_inf.mpr ⟨h1, ?_⟩
  obtain ⟨m, hm⟩ := psi1_law k g u
  have hphi : Phi u = 0 := AddMonoidHom.mem_ker.mp (AddSubgroup.mem_inf.mp h01).2
  rw [AddMonoidHom.mem_ker, hm, hphi, AddMonoidHom.mem_ker.mp h2]
  simp [B0]

theorem Q3_apply (c : ZMod 2) (x : V4) (w : V4) : Q3 (c, x) w = c * Qf w + B0 w x := rfl

theorem N3_inv (k : Fin 2) : InvSub (permAct (Mk k)) (Nk k 3) := by
  intro g u hu
  obtain ⟨⟨c, x⟩, rfl⟩ := hu
  obtain ⟨m, hm⟩ := permAct_Qfun k g
  refine ⟨(c, c • m + ρk k g x), ?_⟩
  funext w
  have h1 : permAct (Mk k) g (Q3 (c, x)) w = c * Qf (ρk k g⁻¹ w) + B0 (ρk k g⁻¹ w) x := rfl
  have h2 := congrFun hm w
  have h3 := congrFun (permAct_Cf k g x) w
  have h4 : Qf (ρk k g⁻¹ w) = Qf w + B0 w m := h2
  have h5 : B0 (ρk k g⁻¹ w) x = B0 w (ρk k g x) := h3
  rw [h1, h4, h5, Q3_apply]
  simp only [B0, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

theorem N4_inv (k : Fin 2) : InvSub (permAct (Mk k)) (Nk k 4) := by
  intro g u hu
  obtain ⟨x, rfl⟩ := hu
  exact ⟨ρk k g x, (permAct_Cf k g x).symm⟩

theorem Cf_mem_N4 (k : Fin 2) (x : V4) : Cf x ∈ Nk k 4 := ⟨x, rfl⟩

theorem N4_le_N3 (k : Fin 2) : Nk k 4 ≤ Nk k 3 := by
  rintro _ ⟨x, rfl⟩
  refine ⟨(0, x), ?_⟩
  funext w
  simp [Q3_apply, Cadd, Cf]

theorem Qfun_mem_aux : ∀ x : V4, (Cf x 0 = 0 ∧ ∑ w : V4, Cf x w = 0) ∧
    (∑ w : V4, Cf x w • w = 0) ∧ (∑ w : V4, Cf x w * Qf w = 0) := by decide +kernel

theorem Qfun_aux : (Qfun 0 = 0 ∧ ∑ w : V4, Qfun w = 0) ∧ (∑ w : V4, Qfun w • w = 0) ∧
    (∑ w : V4, Qfun w * Qf w = 0) := by decide +kernel

theorem N3_le_N2 (k : Fin 2) : Nk k 3 ≤ Nk k 2 := by
  have hC : ∀ x : V4, Cf x ∈ Nk k 2 := by
    intro x
    obtain ⟨⟨h1, h2⟩, h3, h4⟩ := Qfun_mem_aux x
    exact AddSubgroup.mem_inf.mpr ⟨AddSubgroup.mem_inf.mpr
      ⟨(mem_permCore k _).mpr ⟨h1, h2⟩, AddMonoidHom.mem_ker.mpr h3⟩, AddMonoidHom.mem_ker.mpr h4⟩
  have hQ : Qfun ∈ Nk k 2 := by
    obtain ⟨⟨h1, h2⟩, h3, h4⟩ := Qfun_aux
    exact AddSubgroup.mem_inf.mpr ⟨AddSubgroup.mem_inf.mpr
      ⟨(mem_permCore k _).mpr ⟨h1, h2⟩, AddMonoidHom.mem_ker.mpr h3⟩, AddMonoidHom.mem_ker.mpr h4⟩
  rintro _ ⟨⟨c, x⟩, rfl⟩
  show c • Qfun + Cf x ∈ Nk k 2
  refine AddSubgroup.add_mem _ ?_ (hC x)
  fin_cases c
  · show (0 : ZMod 2) • Qfun ∈ Nk k 2
    rw [zero_smul]
    exact AddSubgroup.zero_mem _
  · show (1 : ZMod 2) • Qfun ∈ Nk k 2
    rw [one_smul]
    exact hQ

theorem N2_le_N1 (k : Fin 2) : Nk k 2 ≤ Nk k 1 := inf_le_left

theorem N1_le_N0 (k : Fin 2) : Nk k 1 ≤ Nk k 0 := inf_le_left

theorem card_Fn : Nat.card Fn = 2 ^ 16 := by
  simp [Nat.card_fun, Nat.card_zmod]

theorem sum_single_smul (a : V4) (c : ZMod 2) :
    ∑ w : V4, (Pi.single a c : V4 → ZMod 2) w • w = c • a := by
  simp [Pi.single_apply]

theorem sum_single (a : V4) (c : ZMod 2) : ∑ w : V4, (Pi.single a c : V4 → ZMod 2) w = c := by
  simp [Pi.single_apply]

theorem exists_ab : ∀ t : V4, ∃ a b : V4, a ≠ 0 ∧ b ≠ 0 ∧ a + b = t := by decide +kernel

theorem card_N0 (k : Fin 2) : Nat.card (Nk k 0) = 2 ^ 14 := by
  let P0 : Fn →+ ZMod 2 × ZMod 2 := (evalZero (Mk k)).prod (weightHom (Mk k))
  have hker : P0.ker = Nk k 0 := by
    ext u
    show (u 0, weightHom (Mk k) u) = ((0 : ZMod 2), (0 : ZMod 2)) ↔ u ∈ permCore (Mk k)
    rw [mem_permCore, weightHom_apply, Prod.mk.injEq]
  have hsurj : Function.Surjective P0 := by
    rintro ⟨a, b⟩
    let e : V4 := ![1, 0, 0, 0]
    refine ⟨Pi.single 0 a + Pi.single e (a + b), ?_⟩
    have he : e ≠ 0 := by decide +kernel
    refine Prod.ext ?_ ?_
    · show (Pi.single 0 a + Pi.single e (a + b) : Fn) 0 = a
      simp [Pi.single_apply, he.symm]
    · show weightHom (Mk k) (Pi.single 0 a + Pi.single e (a + b) : Fn) = b
      rw [weightHom_apply]
      simp only [Pi.add_apply, Finset.sum_add_distrib, sum_single]
      have key : ∀ x y : ZMod 2, x + (x + y) = y := by decide
      exact key a b
  have h := AddSubgroup.card_ker_mul_card_of_surjective hsurj
  rw [hker, card_Fn] at h
  have h4 : Nat.card (ZMod 2 × ZMod 2) = 4 := by simp [Nat.card_prod, Nat.card_zmod]
  rw [h4] at h
  omega

theorem card_V4 : Nat.card V4 = 16 := by
  simp [Nat.card_fun, Nat.card_zmod]

@[expose] def U1gen : Fn := fun w =>
  if w = 0 ∨ w = ![1, 0, 0, 0] ∨ w = ![0, 1, 0, 0] ∨ w = ![1, 1, 0, 0] then 0 else 1

theorem U1gen_aux : (U1gen 0 = 0 ∧ ∑ w : V4, U1gen w = 0) ∧ (∑ w : V4, U1gen w • w = 0) ∧
    (∑ w : V4, U1gen w * Qf w = 1) := by decide +kernel

theorem phi_two_single (a b t : V4) (hab : a + b = t) :
    Phi (Pi.single a 1 + Pi.single b 1 : Fn) = t := by
  rw [map_add]
  show ∑ w : V4, (Pi.single a 1 : Fn) w • w + ∑ w : V4, (Pi.single b 1 : Fn) w • w = t
  rw [sum_single_smul, sum_single_smul, one_smul, one_smul, hab]

theorem two_single_mem (k : Fin 2) (a b : V4) (ha : a ≠ 0) (hb : b ≠ 0) :
    (Pi.single a 1 + Pi.single b 1 : Fn) ∈ permCore (Mk k) := by
  rw [mem_permCore]
  refine ⟨?_, ?_⟩
  · simp [Pi.single_apply, ha.symm, hb.symm]
  · simp only [Pi.add_apply, Finset.sum_add_distrib, sum_single]
    decide

theorem card_N1 (k : Fin 2) : Nat.card (Nk k 1) = 2 ^ 10 := by
  have hs : Function.Surjective ((Phi).comp (Nk k 0).subtype) := by
    intro t
    obtain ⟨a, b, ha, hb, hab⟩ := exists_ab t
    exact ⟨⟨(Pi.single a 1 + Pi.single b 1 : Fn), two_single_mem k a b ha hb⟩,
      phi_two_single a b t hab⟩
  have h := card_eq_mul_of_quot (N := Nk k 0) (K := Nk k 1) (N1_le_N0 k)
    ((Phi).comp (Nk k 0).subtype) hs (fun n => by
      show Phi (n : Fn) = 0 ↔ (n : Fn) ∈ permCore (Mk k) ⊓ Phi.ker
      rw [AddSubgroup.mem_inf, AddMonoidHom.mem_ker]
      exact ⟨fun h => ⟨n.2, h⟩, fun h => h.2⟩)
  rw [card_N0, card_V4] at h
  omega

theorem card_N2 (k : Fin 2) : Nat.card (Nk k 2) = 2 ^ 9 := by
  have hU : U1gen ∈ Nk k 1 := by
    obtain ⟨⟨h1, h2⟩, h3, -⟩ := U1gen_aux
    exact AddSubgroup.mem_inf.mpr ⟨(mem_permCore k _).mpr ⟨h1, h2⟩, AddMonoidHom.mem_ker.mpr h3⟩
  have hs : Function.Surjective ((psi1).comp (Nk k 1).subtype) := by
    intro t
    have ht : ∀ t : ZMod 2, t = 0 ∨ t = 1 := by decide
    rcases ht t with rfl | rfl
    · exact ⟨0, map_zero _⟩
    · exact ⟨⟨U1gen, hU⟩, U1gen_aux.2.2⟩
  have h := card_eq_mul_of_quot (N := Nk k 1) (K := Nk k 2) (N2_le_N1 k)
    ((psi1).comp (Nk k 1).subtype) hs (fun n => by
      show psi1 (n : Fn) = 0 ↔ (n : Fn) ∈ (permCore (Mk k) ⊓ Phi.ker) ⊓ psi1.ker
      rw [AddSubgroup.mem_inf, AddMonoidHom.mem_ker]
      exact ⟨fun h => ⟨n.2, h⟩, fun h => h.2⟩)
  rw [card_N1] at h
  have h2 : Nat.card (ZMod 2) = 2 := Nat.card_zmod 2
  rw [h2] at h
  omega

theorem Q3_inj : Function.Injective Q3 := by
  rw [injective_iff_map_eq_zero]
  rintro ⟨c, x⟩ h
  have key : ∀ (c : ZMod 2) (x : V4), (∀ w : V4, c * Qf w + B0 w x = 0) → c = 0 ∧ x = 0 := by
    decide +kernel
  have := key c x (fun w => congrFun h w)
  exact Prod.ext this.1 this.2

theorem Cadd_inj : Function.Injective Cadd := by
  rw [injective_iff_map_eq_zero]
  intro x h
  have key : ∀ x : V4, (∀ w : V4, B0 w x = 0) → x = 0 := by decide +kernel
  exact key x (fun w => congrFun h w)

theorem card_N3 (k : Fin 2) : Nat.card (Nk k 3) = 2 ^ 5 := by
  have : Nat.card (Nk k 3) = Nat.card (ZMod 2 × V4) :=
    Nat.card_congr (AddMonoidHom.ofInjective Q3_inj).toEquiv.symm
  rw [this, Nat.card_prod, card_V4, Nat.card_zmod]
  norm_num

theorem card_N4 (k : Fin 2) : Nat.card (Nk k 4) = 2 ^ 4 := by
  have : Nat.card (Nk k 4) = Nat.card V4 :=
    Nat.card_congr (AddMonoidHom.ofInjective Cadd_inj).toEquiv.symm
  rw [this, card_V4]
  norm_num

end CFSG.Quasithin.ShultG53
