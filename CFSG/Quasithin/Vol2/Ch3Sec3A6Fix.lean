module

public import CFSG.Quasithin.Vol2.Ch3Sec3A6Cocycle
public import CFSG.Quasithin.Vol2.Ch3Sec3P5Act

public section

namespace CFSG.Quasithin.H13

open CFSG.Quasithin

namespace P5

theorem sec_add (u v : Vec5) : sec (u + v) = sec u + sec v := Matrix.mulVec_add _ _ _

theorem act_add (σ : Equiv.Perm (Fin 6)) (u v : Vec5) : act σ (u + v) = act σ u + act σ v := by
  show crd (fun i => sec (u + v) (σ⁻¹ i)) =
    crd (fun i => sec u (σ⁻¹ i)) + crd (fun i => sec v (σ⁻¹ i))
  rw [← crd_add, sec_add]
  rfl

@[expose] def actAdd (σ : Equiv.Perm (Fin 6)) : Vec5 ≃+ Vec5 where
  toFun := act σ
  invFun := act σ⁻¹
  left_inv v := by rw [← act_mul, inv_mul_cancel, act_one]
  right_inv v := by rw [← act_mul, mul_inv_cancel, act_one]
  map_add' := act_add σ

theorem actAdd_apply (σ : Equiv.Perm (Fin 6)) (v : Vec5) : actAdd σ v = act σ v := rfl

theorem fix_ab : ∀ v : Vec5, act A6Coc.aP v = v → act A6Coc.bP v = v → v = 0 := by
  decide +kernel

theorem two_mul_aux : ∀ a b c d : ZMod 2, a + b = c + d → a + d = b + c := by decide

theorem add_swap {a b c d : Vec5} (h : a + b = c + d) : a + d = b + c :=
  funext fun i => two_mul_aux (a i) (b i) (c i) (d i) (congrFun h i)

theorem sub_eq_add (a b : Vec5) : a - b = a + b :=
  funext fun i => by
    show a i - b i = a i + b i
    exact (by decide : ∀ x y : ZMod 2, x - y = x + y) (a i) (b i)

theorem eq_of_add_eq_zero {a b : Vec5} (h : a + b = 0) : a = b :=
  funext fun i => (by decide : ∀ x y : ZMod 2, x + y = 0 → x = y) (a i) (b i) (congrFun h i)

theorem add_self (v : Vec5) : v + v = 0 :=
  funext fun i => (by decide : ∀ x : ZMod 2, x + x = 0) (v i)

end P5

namespace A6Coc

theorem fix_b : ∀ v : Vec4, act bP v = v → v = 0 := by decide +kernel

theorem sum_pair : ∀ a b : Fin 6, ∑ i, (Pi.single a 1 + Pi.single b 1 : Fin 6 → ZMod 2) i = 0 := by
  decide +kernel

theorem crd_pair : ∀ j k : Fin 6, crd (Pi.single k 1 + Pi.single 0 1) =
    crd (Pi.single j 1 + Pi.single 0 1) + crd (Pi.single k 1 + Pi.single j 1) := by
  decide +kernel

theorem act_pair (σ : Equiv.Perm (Fin 6)) (a b : Fin 6) :
    act σ (crd (Pi.single a 1 + Pi.single b 1)) = crd (Pi.single (σ a) 1 + Pi.single (σ b) 1) := by
  rw [act_crd σ _ (sum_pair a b)]
  congr 1
  funext i
  simp only [Pi.add_apply, Pi.single_apply, Equiv.Perm.inv_eq_iff_eq]

@[expose] def j45 (v : Vec4) : P5.Vec5 := P5.crd (sec v)

theorem j45_crd (x : Fin 6 → ZMod 2) (hx : ∑ i, x i = 0) : j45 (crd x) = P5.crd x := by
  obtain ⟨c, hc⟩ := sec_crd x hx
  have e : sec (crd x) = x + fun _ => c := funext hc
  rw [j45, e, P5.crd_add, P5.crd_const, add_zero]

theorem j45_add (u v : Vec4) : j45 (u + v) = j45 u + j45 v := by
  rw [j45, sec_add, P5.crd_add]
  rfl

theorem j45_zero : j45 0 = 0 := by
  rw [j45, sec_zero]
  exact Matrix.mulVec_zero _

theorem j45_sub (u v : Vec4) : j45 (u - v) = j45 u - j45 v := by
  have h := j45_add (u - v) v
  rw [sub_add_cancel] at h
  rw [h, add_sub_cancel_right]

theorem j45_act (σ : Equiv.Perm (Fin 6)) (v : Vec4) : j45 (act σ v) = P5.act σ (j45 v) := by
  have hs : ∑ i, sec v (σ⁻¹ i) = 0 := by
    rw [Equiv.sum_comp σ⁻¹ (sec v)]
    exact sum_sec v
  show j45 (crd fun i => sec v (σ⁻¹ i)) = P5.act σ (P5.crd (sec v))
  rw [j45_crd _ hs, P5.act_crd]

theorem j45_eq_zero : ∀ v : Vec4, j45 v = 0 → v = 0 := by decide +kernel

theorem j45_injective : Function.Injective j45 := by
  intro u v h
  have h1 : j45 (u - v) = 0 := by rw [j45_sub, h, sub_self]
  exact sub_eq_zero.mp (j45_eq_zero _ h1)

@[expose] def e0 : P5.Vec5 := P5.crd (Pi.single 0 1)

theorem j45_ne_e0 : ∀ v : Vec4, j45 v ≠ e0 := by decide +kernel

@[expose] noncomputable def del0 (σ : Equiv.Perm (Fin 6)) : AltHeart 6 :=
  epsInv (crd (Pi.single (σ 0) 1 + Pi.single 0 1))

theorem eps_del0 (σ : Equiv.Perm (Fin 6)) :
    eps (del0 σ) = crd (Pi.single (σ 0) 1 + Pi.single 0 1) :=
  eps_epsInv _

theorem del0_mul (σ τ : Equiv.Perm (Fin 6)) :
    del0 (σ * τ) = del0 σ + heartAct 6 σ (del0 τ) := by
  apply eps_injective
  rw [map_add, eps_heartAct, eps_del0, eps_del0, eps_del0, act_pair, Equiv.Perm.mul_apply,
    crd_pair (σ 0) (σ (τ 0))]

theorem j45_eps_del0 (σ : Equiv.Perm (Fin 6)) :
    j45 (eps (del0 σ)) = P5.act σ e0 + e0 := by
  rw [eps_del0, j45_crd _ (sum_pair _ _), P5.crd_add, e0, P5.act_single]

theorem j45_eps_sub (σ : Equiv.Perm (Fin 6)) (u : AltHeart 6) :
    j45 (eps (u - heartAct 6 σ u)) = j45 (eps u) + P5.act σ (j45 (eps u)) := by
  rw [map_sub, eps_heartAct]
  calc j45 (eps u - act σ (eps u)) = j45 (eps u) - j45 (act σ (eps u)) := j45_sub _ _
    _ = j45 (eps u) + P5.act σ (j45 (eps u)) := by rw [j45_act, P5.sub_eq_add]

theorem del0_not_inner :
    ¬ ∃ u : AltHeart 6, ∀ g : Γ, del0 (g : Equiv.Perm (Fin 6)) =
      u - heartAct 6 (g : Equiv.Perm (Fin 6)) u := by
  rintro ⟨u, hu⟩
  set w : P5.Vec5 := j45 (eps u)
  have key : ∀ g : Γ, P5.act (g : Equiv.Perm (Fin 6)) (e0 + w) = e0 + w := by
    intro g
    have h1 := congrArg (fun y => j45 (eps y)) (hu g)
    have h2 : j45 (eps (u - heartAct 6 (g : Equiv.Perm (Fin 6)) u)) =
        w + P5.act (g : Equiv.Perm (Fin 6)) w := by
      rw [map_sub, eps_heartAct]
      calc j45 (eps u - act (g : Equiv.Perm (Fin 6)) (eps u)) =
          j45 (eps u) - j45 (act (g : Equiv.Perm (Fin 6)) (eps u)) := j45_sub _ _
        _ = w + P5.act (g : Equiv.Perm (Fin 6)) w := by rw [j45_act, P5.sub_eq_add]
    rw [j45_eps_del0, h2] at h1
    rw [P5.act_add]
    exact P5.add_swap h1
  have h0 := P5.fix_ab _ (key aL) (key bL)
  exact j45_ne_e0 _ (P5.eq_of_add_eq_zero h0).symm

theorem heartAct_mul_aux (σ τ : Equiv.Perm (Fin 6)) (y : AltHeart 6) :
    heartAct 6 (σ * τ) y = heartAct 6 σ (heartAct 6 τ y) := by
  apply eps_injective
  rw [eps_heartAct, eps_heartAct, eps_heartAct, act_mul]

theorem crossed_eq_zero {ε : Equiv.Perm (Fin 6) → AltHeart 6}
    (hε : ∀ σ τ, ε (σ * τ) = ε σ + heartAct 6 σ (ε τ))
    (h0 : ∀ x ∈ alternatingGroup (Fin 6), ε x = 0) (σ : Equiv.Perm (Fin 6)) : ε σ = 0 := by
  have hinv : heartAct 6 σ (ε σ⁻¹) = -ε σ := by
    have h1 := hε σ σ⁻¹
    rw [mul_inv_cancel, h0 1 (one_mem _)] at h1
    exact (neg_eq_of_add_eq_zero_right h1.symm).symm
  have hx : σ⁻¹ * bP * σ ∈ alternatingGroup (Fin 6) := by
    have hb : bP ∈ alternatingGroup (Fin 6) := bP_mem
    have := (alternatingGroup.normal (α := Fin 6)).conj_mem _ hb σ⁻¹
    simpa using this
  have h2 : ε (σ * (σ⁻¹ * bP * σ) * σ⁻¹) = 0 := by
    have e : σ * (σ⁻¹ * bP * σ) * σ⁻¹ = bP := by group
    rw [e]
    exact h0 _ bP_mem
  rw [hε, hε, h0 _ hx, map_zero, add_zero, show σ * (σ⁻¹ * bP * σ) = bP * σ by group,
    heartAct_mul_aux, hinv, map_neg] at h2
  have h3 : heartAct 6 bP (ε σ) = ε σ := (eq_of_sub_eq_zero (by rw [sub_eq_add_neg]; exact h2)).symm
  have h4 : act bP (eps (ε σ)) = eps (ε σ) := by rw [← eps_heartAct, h3]
  exact eps_injective (by rw [fix_b _ h4, map_zero])

end A6Coc

end CFSG.Quasithin.H13
