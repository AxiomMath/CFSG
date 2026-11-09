module

public import Certificates.Data.Kernel.PermCent.CV

public section

namespace CFSG.Certificates.Kernel.PkCV

open CFSG.KC.Enum

variable {n : Nat}

@[expose] def inM (M x : Nat) : Bool := Nat.blt 0 (Nat.land M (Nat.shiftLeft 1 x))

@[expose] noncomputable def closedC (M : Nat) (t : CV n) : Bool :=
  allN n fun x => Bool.rec true (inM M (img n t.1 x)) (inM M x)

@[expose] noncomputable def masksC (f₁ f₂ : Nat) (L : List (List (CV n) × Nat)) : Bool :=
  List.rec (motive := fun _ => Bool) true
    (fun hd tl ih => inM hd.2 f₁ && inM hd.2 f₂ && (tl.all fun e => e.1.all (closedC hd.2)) && ih) L

variable [Small n]

@[expose] noncomputable def walkC (body : CV n → Bool) (L : List (List (CV n) × Nat)) :
    CV n → Nat → Nat → Bool :=
  List.rec (motive := fun _ => CV n → Nat → Nat → Bool) (fun p _ _ => body p)
    (fun hd _ ih p a b => hd.1.all fun t => strictB (t⁻¹).1 fun ti =>
      strictB (img n ti a) fun a' => strictB (img n ti b) fun b' =>
        Bool.rec true (Bool.rec true (ih (p * t) a' b') (inM hd.2 b')) (inM hd.2 a')) L

@[expose] noncomputable def fixC (f₁ f₂ : Nat) (S G : List (CV n)) : Bool :=
  (G.all fun s => decide (s ∈ S)) &&
    (S.all fun s => Nat.beq (img n s.1 f₁) f₁ && Nat.beq (img n s.1 f₂) f₂) &&
    allN n fun x => !(G.all fun s => Nat.beq (img n s.1 x) x) || Nat.beq x f₁ || Nat.beq x f₂

theorem strictB_eqW (y : Nat) (k : Nat → Bool) : strictB y k = k y := by
  cases y <;> rfl

theorem walkC_nil (body : CV n → Bool) (p : CV n) (a b : Nat) : walkC body [] p a b = body p := rfl

theorem walkC_cons (body : CV n → Bool) (T : List (CV n)) (M : Nat) (tl : List (List (CV n) × Nat))
    (p : CV n) (a b : Nat) : walkC body ((T, M) :: tl) p a b = T.all fun t =>
      strictB (t⁻¹).1 fun ti => strictB (img n ti a) fun a' => strictB (img n ti b) fun b' =>
        Bool.rec true (Bool.rec true (walkC body tl (p * t) a' b') (inM M b')) (inM M a') := rfl

theorem masksC_cons (f₁ f₂ : Nat) (T : List (CV n)) (M : Nat) (tl : List (List (CV n) × Nat)) :
    masksC f₁ f₂ ((T, M) :: tl) =
      (inM M f₁ && inM M f₂ && (tl.all fun e => e.1.all (closedC M)) && masksC f₁ f₂ tl) := rfl

theorem fixC_sub {f₁ f₂ : Nat} {S G : List (CV n)} (hf : fixC f₁ f₂ S G = true) :
    (G.all fun s => decide (s ∈ S)) = true := by
  rw [fixC, Bool.and_eq_true, Bool.and_eq_true] at hf
  exact hf.1.1

theorem closedC_apply {M : Nat} {t : CV n} (h : closedC M t = true) (x : Fin n)
    (hx : inM M x = true) : inM M (ev t x) = true := by
  rw [closedC, CFSG.KS.PK.allN_iff] at h
  have h' := h x x.2
  beta_reduce at h'
  rw [hx] at h'
  exact h'

theorem prod_closed (M : Nat) : ∀ Ls : List (List (CV n)), (∀ e ∈ Ls, ∀ t ∈ e, closedC M t = true) →
    ∀ r ∈ productsC Ls, ∀ x : Fin n, inM M x = true → inM M (ev r x) = true
  | [], _, r, hr, x, hx => by
    rw [productsC, List.mem_singleton] at hr
    rw [hr, ev_one, Equiv.Perm.one_apply]
    exact hx
  | T :: Ts, h, r, hr, x, hx => by
    rw [productsC, List.mem_flatMap] at hr
    obtain ⟨t, ht, hr⟩ := hr
    obtain ⟨r', hr', rfl⟩ := List.mem_map.1 hr
    rw [ev_mul, Equiv.Perm.mul_apply]
    exact closedC_apply (h T (List.mem_cons.2 (Or.inl rfl)) t ht) _
      (prod_closed M Ts (fun e he => h e (List.mem_cons_of_mem _ he)) r' hr' x hx)

theorem pre_in {M : Nat} {f₁ f₂ : Fin n} (h₁ : inM M f₁ = true) (h₂ : inM M f₂ = true)
    {Ls : List (List (CV n))} (hc : ∀ e ∈ Ls, ∀ t ∈ e, closedC M t = true) (q r : CV n)
    (hr : r ∈ productsC Ls) (y : Fin n)
    (hy : (ev (q * r))⁻¹ y = f₁ ∨ (ev (q * r))⁻¹ y = f₂) : inM M ((ev q)⁻¹ y) = true := by
  have e : (ev q)⁻¹ y = ev r ((ev (q * r))⁻¹ y) := by
    rw [ev_mul, mul_inv_rev, Equiv.Perm.mul_apply]
    exact (Equiv.apply_symm_apply (ev r) _).symm
  rw [e]
  apply prod_closed M Ls hc r hr
  rcases hy with h | h <;> rw [h] <;> assumption

theorem inv_step (p t : CV n) (y : Fin n) :
    img n (t⁻¹).1 ((ev p)⁻¹ y) = ((ev (p * t))⁻¹ y : Nat) := by
  rw [ev_mul, mul_inv_rev, Equiv.Perm.mul_apply, ← ev_inv]
  rfl

theorem walkC_sound (body : CV n → Bool) (f₁ f₂ : Fin n) :
    ∀ (L : List (List (CV n) × Nat)) (p : CV n) (a b : Nat), masksC f₁ f₂ L = true →
      walkC body L p a b = true → a = ((ev p)⁻¹ f₁ : Nat) → b = ((ev p)⁻¹ f₂ : Nat) →
      ∀ u ∈ productsC (L.map Prod.fst),
        ((ev (p * u))⁻¹ f₁ = f₁ ∨ (ev (p * u))⁻¹ f₁ = f₂) →
        ((ev (p * u))⁻¹ f₂ = f₁ ∨ (ev (p * u))⁻¹ f₂ = f₂) → body (p * u) = true
  | [], p, a, b, _, hw, _, _, u, hu, _, _ => by
    rw [List.map_nil, productsC, List.mem_singleton] at hu
    rw [hu, mul_one]
    exact hw
  | (T, M) :: tl, p, a, b, hm, hw, ha, hb, u, hu, hg₁, hg₂ => by
    rw [masksC_cons, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at hm
    obtain ⟨⟨⟨h₁, h₂⟩, hc⟩, hm⟩ := hm
    have hc' : ∀ e ∈ tl.map Prod.fst, ∀ t ∈ e, closedC M t = true := by
      intro e he t ht
      obtain ⟨e', he', rfl⟩ := List.mem_map.1 he
      exact List.all_eq_true.1 (List.all_eq_true.1 hc e' he') t ht
    rw [List.map_cons, productsC, List.mem_flatMap] at hu
    obtain ⟨t, ht, hu⟩ := hu
    obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hu
    rw [← mul_assoc] at hg₁ hg₂ ⊢
    rw [walkC_cons, List.all_eq_true] at hw
    have hw' := hw t ht
    simp only [strictB_eqW] at hw'
    have ea : img n (t⁻¹).1 a = ((ev (p * t))⁻¹ f₁ : Nat) := by rw [ha]; exact inv_step p t f₁
    have eb : img n (t⁻¹).1 b = ((ev (p * t))⁻¹ f₂ : Nat) := by rw [hb]; exact inv_step p t f₂
    have ia : inM M (img n (t⁻¹).1 a) = true := by
      rw [ea]; exact pre_in h₁ h₂ hc' (p * t) r hr f₁ hg₁
    have ib : inM M (img n (t⁻¹).1 b) = true := by
      rw [eb]; exact pre_in h₁ h₂ hc' (p * t) r hr f₂ hg₂
    rw [ia, ib] at hw'
    exact walkC_sound body f₁ f₂ tl (p * t) _ _ hm hw' ea eb r hr hg₁ hg₂

theorem good_of_nrm {f₁ f₂ : Fin n} {S G : List (CV n)} (hf : fixC f₁ f₂ S G = true) (g : CV n)
    (hn : (G.all fun s => decide (g * s * g⁻¹ ∈ S)) = true) (y : Fin n) (hy : y = f₁ ∨ y = f₂) :
    (ev g)⁻¹ y = f₁ ∨ (ev g)⁻¹ y = f₂ := by
  rw [fixC, Bool.and_eq_true, Bool.and_eq_true] at hf
  obtain ⟨⟨_, hS⟩, hA⟩ := hf
  rw [CFSG.KS.PK.allN_iff] at hA
  have hfix : ∀ s ∈ S, ev s y = y := by
    intro s hs
    have h := List.all_eq_true.1 hS s hs
    rw [Bool.and_eq_true, Nat.beq_eq, Nat.beq_eq] at h
    apply Fin.ext
    rw [ev_apply]
    rcases hy with rfl | rfl
    · exact h.1
    · exact h.2
  set x := (ev g)⁻¹ y
  have hx : ∀ s ∈ G, ev s x = x := by
    intro s hs
    have hm := of_decide_eq_true (List.all_eq_true.1 hn s hs)
    have e := hfix _ hm
    rw [ev_mul, ev_mul, ev_inv, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply] at e
    calc ev s x = (ev g)⁻¹ (ev g (ev s x)) := (Equiv.symm_apply_apply (ev g) _).symm
      _ = x := by rw [e]
  have h := hA x x.2
  beta_reduce at h
  have hG : (G.all fun s => Nat.beq (img n s.1 x) x) = true :=
    List.all_eq_true.2 fun s hs => Nat.beq_eq.mpr (congrArg Fin.val (hx s hs))
  rw [hG, Bool.not_true, Bool.false_or, Bool.or_eq_true, Nat.beq_eq, Nat.beq_eq] at h
  rcases h with h | h
  · exact Or.inl (Fin.ext h)
  · exact Or.inr (Fin.ext h)

end CFSG.Certificates.Kernel.PkCV

end
