module

public import CFSG.Quasithin.Background.JonesParshallG2Stab

public noncomputable section

namespace CFSG.Quasithin.JonesParshall

open Matrix CFSG.Quasithin.Explicit CFSG.Open

abbrev Ix3 : Type := Fin 3 ⊕ Fin 3

variable {F : Type} [Field F]

@[expose] def q6 (u₀ u₁ u₂ v₀ v₁ v₂ : F) : Ix3 → F := Sum.elim ![u₀, u₁, u₂] ![v₀, v₁, v₂]

omit [Field F] in
theorem q6_eta (w : Ix3 → F) :
    w = q6 (w (.inl 0)) (w (.inl 1)) (w (.inl 2)) (w (.inr 0)) (w (.inr 1)) (w (.inr 2)) := by
  funext i
  rcases i with i | i <;> fin_cases i <;> rfl

omit [Field F] in
theorem q6_inj {a₀ a₁ a₂ b₀ b₁ b₂ a₀' a₁' a₂' b₀' b₁' b₂' : F}
    (h : q6 a₀ a₁ a₂ b₀ b₁ b₂ = q6 a₀' a₁' a₂' b₀' b₁' b₂') :
    a₀ = a₀' ∧ a₁ = a₁' ∧ a₂ = a₂' ∧ b₀ = b₀' ∧ b₁ = b₁' ∧ b₂ = b₂' :=
  ⟨congrFun h (.inl 0), congrFun h (.inl 1), congrFun h (.inl 2), congrFun h (.inr 0),
    congrFun h (.inr 1), congrFun h (.inr 2)⟩

omit [Field F] in
theorem q6_congr {a₀ a₁ a₂ b₀ b₁ b₂ a₀' a₁' a₂' b₀' b₁' b₂' : F} (h1 : a₀ = a₀') (h2 : a₁ = a₁')
    (h3 : a₂ = a₂') (h4 : b₀ = b₀') (h5 : b₁ = b₁') (h6 : b₂ = b₂') :
    q6 a₀ a₁ a₂ b₀ b₁ b₂ = q6 a₀' a₁' a₂' b₀' b₁' b₂' := by
  subst h1 h2 h3 h4 h5 h6
  rfl

theorem q6_add (a₀ a₁ a₂ b₀ b₁ b₂ a₀' a₁' a₂' b₀' b₁' b₂' : F) :
    q6 a₀ a₁ a₂ b₀ b₁ b₂ + q6 a₀' a₁' a₂' b₀' b₁' b₂' =
      q6 (a₀ + a₀') (a₁ + a₁') (a₂ + a₂') (b₀ + b₀') (b₁ + b₁') (b₂ + b₂') := by
  funext i
  rcases i with i | i <;> fin_cases i <;> rfl

theorem q6_sub (a₀ a₁ a₂ b₀ b₁ b₂ a₀' a₁' a₂' b₀' b₁' b₂' : F) :
    q6 a₀ a₁ a₂ b₀ b₁ b₂ - q6 a₀' a₁' a₂' b₀' b₁' b₂' =
      q6 (a₀ - a₀') (a₁ - a₁') (a₂ - a₂') (b₀ - b₀') (b₁ - b₁') (b₂ - b₂') := by
  funext i
  rcases i with i | i <;> fin_cases i <;> rfl

theorem q6_smul (c a₀ a₁ a₂ b₀ b₁ b₂ : F) :
    c • q6 a₀ a₁ a₂ b₀ b₁ b₂ = q6 (c * a₀) (c * a₁) (c * a₂) (c * b₀) (c * b₁) (c * b₂) := by
  funext i
  rcases i with i | i <;> fin_cases i <;> rfl

theorem q6_zero : q6 (0 : F) 0 0 0 0 0 = 0 := by
  funext i
  rcases i with i | i <;> fin_cases i <;> rfl

@[expose] def zI (w : Ix3 → F) : quasithinZorn F :=
  zmk 0 (w (.inl 0)) (w (.inl 1)) (w (.inl 2)) (w (.inr 0)) (w (.inr 1)) (w (.inr 2)) 0

@[expose] def zP (x : quasithinZorn F) : Ix3 → F :=
  q6 (x.2.1 0) (x.2.1 1) (x.2.1 2) (x.2.2.1 0) (x.2.2.1 1) (x.2.2.1 2)

theorem zI_q6 (a₀ a₁ a₂ b₀ b₁ b₂ : F) : zI (q6 a₀ a₁ a₂ b₀ b₁ b₂) = zmk 0 a₀ a₁ a₂ b₀ b₁ b₂ 0 :=
  rfl

omit [Field F] in
theorem zP_zmk (r u₀ u₁ u₂ v₀ v₁ v₂ s : F) :
    zP (zmk r u₀ u₁ u₂ v₀ v₁ v₂ s) = q6 u₀ u₁ u₂ v₀ v₁ v₂ := rfl

theorem zP_zI (w : Ix3 → F) : zP (zI w) = w := by
  rw [q6_eta w]
  rfl

theorem zI_add (w w' : Ix3 → F) : zI (w + w') = zI w + zI w' := by
  rw [q6_eta w, q6_eta w', q6_add, zI_q6, zI_q6, zI_q6, zmk_add]
  simp

theorem zI_zero : zI (0 : Ix3 → F) = 0 := by
  rw [← q6_zero, zI_q6, zmk_zero]

theorem zP_add (x y : quasithinZorn F) : zP (x + y) = zP x + zP y := by
  rw [zorn_eta x, zorn_eta y, zmk_add, zP_zmk, zP_zmk, zP_zmk, q6_add]

theorem zP_smul (c : F) (x : quasithinZorn F) : zP (c • x) = c • zP x := by
  rw [zorn_eta x, zmk_smul, zP_zmk, zP_zmk, q6_smul]

theorem zP_one : zP (cayleyOne F) = 0 := by
  rw [cayleyOne_eq, zP_zmk, q6_zero]

theorem cayleyTr_zI (w : Ix3 → F) : cayleyTr (zI w) = 0 := by
  rw [q6_eta w, zI_q6, cayleyTr_zmk, add_zero]

theorem trace_zero_eq [CharP F 2] {x : quasithinZorn F} (hx : cayleyTr x = 0) :
    x = zI (zP x) + x.1 • cayleyOne F := by
  have key : ∀ r u₀ u₁ u₂ v₀ v₁ v₂ s : F, r + s = 0 →
      zmk r u₀ u₁ u₂ v₀ v₁ v₂ s = zI (zP (zmk r u₀ u₁ u₂ v₀ v₁ v₂ s)) +
        (zmk r u₀ u₁ u₂ v₀ v₁ v₂ s).1 • cayleyOne F := by
    intro r u₀ u₁ u₂ v₀ v₁ v₂ s h
    have hs : s = r := by rw [eq_neg_of_add_eq_zero_right h, CharTwo.neg_eq]
    rw [zP_zmk, zI_q6, cayleyOne_eq, zmk_smul, zmk_add]
    apply zmk_congr <;> simp [zmk, hs]
  have h := key x.1 (x.2.1 0) (x.2.1 1) (x.2.1 2) (x.2.2.1 0) (x.2.2.1 1) (x.2.2.1 2) x.2.2.2
    (by rw [zorn_eta x, cayleyTr_zmk] at hx; exact hx)
  rwa [← zorn_eta x] at h

variable [CharP F 2]

theorem g2_zP_apply (g : ↥(cayleyGroup F)) (x : quasithinZorn F) (hx : cayleyTr x = 0) :
    zP (cgE g x) = zP (cgE g (zI (zP x))) := by
  conv_lhs => rw [trace_zero_eq hx]
  rw [map_add, map_smul, cg_one, zP_add, zP_smul, zP_one, smul_zero, add_zero]

@[expose] def g2Act : ↥(cayleyGroup F) →* AddMonoid.End (Ix3 → F) where
  toFun g :=
    { toFun := fun w => zP (cgE g (zI w))
      map_zero' := by rw [zI_zero, map_zero, ← zmk_zero, zP_zmk, q6_zero]
      map_add' := fun w w' => by rw [zI_add, map_add, zP_add] }
  map_one' := AddMonoidHom.ext fun w => zP_zI w
  map_mul' g h := AddMonoidHom.ext fun w => by
    change zP (cgE g (cgE h (zI w))) = zP (cgE g (zI (zP (cgE h (zI w)))))
    exact g2_zP_apply g _ (by rw [cg_tr, cayleyTr_zI])

theorem g2Act_apply (g : ↥(cayleyGroup F)) (w : Ix3 → F) :
    g2Act g w = zP (cgE g (zI w)) := rfl

theorem g2_zI_eq (g : ↥(cayleyGroup F)) (w : Ix3 → F) :
    cgE g (zI w) = zI (g2Act g w) + (cgE g (zI w)).1 • cayleyOne F :=
  trace_zero_eq (by rw [cg_tr, cayleyTr_zI])

end CFSG.Quasithin.JonesParshall
