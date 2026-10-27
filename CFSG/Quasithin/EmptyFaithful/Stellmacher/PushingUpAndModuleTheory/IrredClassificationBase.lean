module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.PushingUpAndModuleTheory.ModelBase

public section

namespace CFSG.Quasithin.F53Mod

open Equiv

@[expose] def Model.InvSub {n : ℕ} (M : Model n) (U : Subgroup M.W) : Prop :=
  ∀ σ : Perm (Fin n), ∀ u ∈ U, M.act σ u ∈ U

@[expose] def triv : Model 5 where
  W := Multiplicative (ZMod 2)
  act := 1
  sq := by
    intro w
    revert w
    decide

theorem triv_isIrred : triv.IsIrred := by
  refine ⟨⟨(Multiplicative.ofAdd (1 : ZMod 2) : Multiplicative (ZMod 2)), fun h => ?_⟩,
    fun U hU => ?_⟩
  · have h1 := congrArg Multiplicative.toAdd h
    exact (by decide : (1 : ZMod 2) ≠ 0) h1
  by_cases h : ∀ u ∈ U, u = 1
  · exact Or.inl ((Subgroup.eq_bot_iff_forall U).mpr h)
  · right
    push Not at h
    obtain ⟨u, hu, hu1⟩ := h
    rw [eq_top_iff]
    intro w _
    have key : ∀ a b : ZMod 2, a ≠ 0 → b ≠ 0 → a = b := by decide
    by_cases hw : w = 1
    · rw [hw]; exact U.one_mem
    · have h3 : w = u := Multiplicative.toAdd.injective
        (key _ _ (fun h => hw (Multiplicative.toAdd.injective h))
          (fun h => hu1 (Multiplicative.toAdd.injective h)))
      rw [h3]; exact hu

theorem exists_fixed_vector (M : Model 5) (hnt : ∃ w : M.W, w ≠ 1) :
    ∃ v : M.W, v ≠ 1 ∧ ∀ s ∈ S5Syl, M.act s v = v := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let _ : MulAction S5Syl M.W := MulAction.compHom M.W (M.act.comp S5Syl.subtype)
  have hG : IsPGroup 2 S5Syl := IsPGroup.of_card (n := 3) (by rw [card_S5Syl]; norm_num)
  have hmod := hG.card_modEq_card_fixedPoints M.W
  have heven : 2 ∣ Nat.card M.W := by
    obtain ⟨w, hw⟩ := hnt
    have h2 : w ^ 2 = 1 := by rw [pow_two]; exact M.sq w
    have := orderOf_eq_prime h2 hw
    rw [← this]
    exact orderOf_dvd_natCard w
  by_contra hcon
  push Not at hcon
  have h1 : Nat.card (MulAction.fixedPoints S5Syl M.W) = 1 := by
    rw [Nat.card_eq_one_iff_unique]
    have hone : ∀ a : MulAction.fixedPoints S5Syl M.W, a.1 = 1 := by
      intro a
      by_contra h
      obtain ⟨s, hs, hne⟩ := hcon a.1 h
      exact hne (a.2 ⟨s, hs⟩)
    refine ⟨⟨fun a b => Subtype.ext ((hone a).trans (hone b).symm)⟩, ⟨⟨1, fun g => ?_⟩⟩⟩
    show M.act (g : Perm (Fin 5)) 1 = 1
    exact map_one _
  rw [h1] at hmod
  unfold Nat.ModEq at hmod
  omega

@[expose] def Step (P : Model 5) (Q Q' : Subgroup P.W) (X : Model 5) : Prop :=
  Q' ≤ Q ∧ P.InvSub Q' ∧ X.IsIrred ∧ ∃ f : P.W →* X.W,
    (∀ x ∈ Q, f x = 1 ↔ x ∈ Q') ∧ (∀ y : X.W, ∃ x ∈ Q, f x = y) ∧
    (∀ x ∈ Q, ∀ σ, f (P.act σ x) = X.act σ (f x))

theorem step_iso {P V X : Model 5} {Q Q' : Subgroup P.W} (hstep : Step P Q Q' X)
    (hQ : P.InvSub Q) (hV : V.IsIrred) (φ : P.W →* V.W)
    (hφ : ∀ σ x, φ (P.act σ x) = V.act σ (φ x))
    (hsurj : ∀ y : V.W, ∃ x ∈ Q, φ x = y) (hker : ∀ x ∈ Q', φ x = 1) :
    Nonempty (V.Iso X) := by
  obtain ⟨hle, hQ', hX, f, hf1, hf2, hfeq⟩ := hstep
  have hK : ∀ x ∈ Q, φ x = 1 → x ∈ Q' := by
    have hKinv : P.InvSub (Q ⊓ φ.ker) := fun σ x hx => by
      obtain ⟨hx1, hx2⟩ := Subgroup.mem_inf.mp hx
      exact Subgroup.mem_inf.mpr ⟨hQ σ x hx1, by
        rw [MonoidHom.mem_ker, hφ, MonoidHom.mem_ker.mp hx2, map_one]⟩
    have hU : IsInvSub X ⊤ ((Q ⊓ φ.ker).map f) := by
      intro b _ u hu
      obtain ⟨x, hx, rfl⟩ := hu
      exact ⟨P.act b x, hKinv b x hx, hfeq x (Subgroup.mem_inf.mp hx).1 b⟩
    rcases hX.2 _ hU with h0 | h0
    · intro x hx hφx
      have : f x ∈ (Q ⊓ φ.ker).map f :=
        ⟨x, Subgroup.mem_inf.mpr ⟨hx, MonoidHom.mem_ker.mpr hφx⟩, rfl⟩
      rw [h0, Subgroup.mem_bot] at this
      exact (hf1 x hx).mp this
    · exfalso
      obtain ⟨w, hw⟩ := hV.1
      obtain ⟨x, hxQ, hxφ⟩ := hsurj w
      have : f x ∈ (Q ⊓ φ.ker).map f := by rw [h0]; trivial
      obtain ⟨k, hk, hfk⟩ := this
      obtain ⟨hk1, hk2⟩ := Subgroup.mem_inf.mp hk
      have hq : x * k⁻¹ ∈ Q' :=
        (hf1 _ (Q.mul_mem hxQ (Q.inv_mem hk1))).mp (by rw [map_mul, map_inv, hfk, mul_inv_cancel])
      have h1 : φ (x * k⁻¹) = 1 := hker _ hq
      have h2 : φ k = 1 := MonoidHom.mem_ker.mp hk2
      apply hw
      rw [← hxφ]
      have h3 : x = (x * k⁻¹) * k := by group
      rw [h3, map_mul, h1, h2, one_mul]
  choose g hgQ hgφ using hsurj
  have hh : ∀ x ∈ Q, f (g (φ x)) = f x := by
    intro x hx
    have hq : x * (g (φ x))⁻¹ ∈ Q' :=
      hK _ (Q.mul_mem hx (Q.inv_mem (hgQ _))) (by rw [map_mul, map_inv, hgφ, mul_inv_cancel])
    have := (hf1 _ (hle hq)).mpr hq
    rw [map_mul, map_inv] at this
    exact (mul_inv_eq_one.mp this).symm
  let h : V.W →* X.W := MonoidHom.mk' (fun y => f (g y)) (by
    intro y y'
    have e1 := hh (g y * g y') (Q.mul_mem (hgQ y) (hgQ y'))
    rw [map_mul φ, hgφ, hgφ, map_mul f] at e1
    exact e1)
  have hinj : Function.Injective h := by
    rw [injective_iff_map_eq_one]
    intro y hy
    have h1 : g y ∈ Q' := (hf1 _ (hgQ y)).mp hy
    rw [← hgφ y]
    exact hker _ h1
  have hsurjh : Function.Surjective h := by
    intro y'
    obtain ⟨x, hx, hfx⟩ := hf2 y'
    exact ⟨φ x, by show f (g (φ x)) = y'; rw [hh x hx, hfx]⟩
  refine ⟨⟨MulEquiv.ofBijective h ⟨hinj, hsurjh⟩, fun σ y => ?_⟩⟩
  have hy : V.act σ y = φ (P.act σ (g y)) := by rw [hφ, hgφ]
  show f (g (V.act σ y)) = X.act σ (f (g y))
  rw [hy, hh _ (hQ σ _ (hgQ y)), hfeq _ (hgQ y) σ]

theorem chain_iso {P V : Model 5} (hV : V.IsIrred) (φ : P.W →* V.W)
    (hφ : ∀ σ x, φ (P.act σ x) = V.act σ (φ x)) (hsurj : ∀ y, ∃ x, φ x = y)
    (Q : ℕ → Subgroup P.W) (X : ℕ → Model 5) (m : ℕ) (h0 : Q 0 = ⊤) (hm : Q m = ⊥)
    (hinv : ∀ i ≤ m, P.InvSub (Q i))
    (hstep : ∀ i < m, Step P (Q i) (Q (i + 1)) (X i)) :
    ∃ i < m, Nonempty (V.Iso (X i)) := by
  have key : ∀ d n : ℕ, n + d = m → (∀ y, ∃ x ∈ Q n, φ x = y) →
      ∃ i < m, Nonempty (V.Iso (X i)) := by
    intro d
    induction d with
    | zero =>
      intro n hn hs
      have hnm : n = m := by omega
      subst hnm
      obtain ⟨w, hw⟩ := hV.1
      obtain ⟨x, hx, hxw⟩ := hs w
      rw [hm, Subgroup.mem_bot] at hx
      exact absurd (by rw [← hxw, hx, map_one]) hw
    | succ d ih =>
      intro n hn hs
      by_cases hs' : ∀ y, ∃ x ∈ Q (n + 1), φ x = y
      · exact ih (n + 1) (by omega) hs'
      · have hn' : n < m := by omega
        refine ⟨n, hn', step_iso (hstep n hn') (hinv n hn'.le) hV φ hφ hs ?_⟩
        have hU : IsInvSub V ⊤ ((Q (n + 1)).map φ) := by
          intro b _ u hu
          obtain ⟨x, hx, rfl⟩ := hu
          exact ⟨P.act b x, hinv (n + 1) (by omega) b x hx, hφ b x⟩
        rcases hV.2 _ hU with h0 | h0
        · intro x hx
          have : φ x ∈ (Q (n + 1)).map φ := ⟨x, hx, rfl⟩
          rw [h0] at this
          exact Subgroup.mem_bot.mp this
        · exfalso
          apply hs'
          intro y
          have : y ∈ (Q (n + 1)).map φ := by rw [h0]; trivial
          obtain ⟨x, hx, hxy⟩ := this
          exact ⟨x, hx, hxy⟩
  exact key m 0 (by omega) (by
    rw [h0]
    intro y
    obtain ⟨x, hx⟩ := hsurj y
    exact ⟨x, trivial, hx⟩)

theorem equiv_of_gens {P X : Model 5} {gens : Set (Perm (Fin 5))}
    (hgens : Subgroup.closure gens = ⊤) {Q : Subgroup P.W} (hQ : P.InvSub Q) (f : P.W →* X.W)
    (h : ∀ g ∈ gens, ∀ x ∈ Q, f (P.act g x) = X.act g (f x)) :
    ∀ σ : Perm (Fin 5), ∀ x ∈ Q, f (P.act σ x) = X.act σ (f x) := by
  intro σ
  have hσ : σ ∈ Subgroup.closure gens := by rw [hgens]; trivial
  induction hσ using Subgroup.closure_induction with
  | mem g hg => exact h g hg
  | one => intro x _; simp
  | mul a b _ _ ha hb =>
    intro x hx
    rw [act_mul_apply, act_mul_apply, ha _ (hQ b x hx), hb x hx]
  | inv a _ ha =>
    intro x hx
    have hy := hQ a⁻¹ x hx
    have h1 := ha _ hy
    rw [act_act_inv] at h1
    rw [h1, act_inv_act]

theorem step_of_section {P X : Model 5} {gens : Set (Perm (Fin 5))}
    (hgens : Subgroup.closure gens = ⊤) {Q Q' : Subgroup P.W} (hQ : P.InvSub Q)
    (hQ' : P.InvSub Q') (hle : Q' ≤ Q) (hX : X.IsIrred) (f : P.W →* X.W)
    (hker : ∀ x ∈ Q, f x = 1 ↔ x ∈ Q')
    (hsec : ∀ y : X.W, ∃ x0 ∈ Q, f x0 = y ∧ ∀ g ∈ gens, f (P.act g x0) = X.act g y) :
    Step P Q Q' X := by
  refine ⟨hle, hQ', hX, f, hker, fun y => ?_, fun x hx σ => ?_⟩
  · obtain ⟨x0, hx0, hfx0, -⟩ := hsec y
    exact ⟨x0, hx0, hfx0⟩
  · refine equiv_of_gens hgens hQ f ?_ σ x hx
    intro g hg x hx
    obtain ⟨x0, hx0, hfx0, hg0⟩ := hsec (f x)
    have hq : x * x0⁻¹ ∈ Q' :=
      (hker _ (Q.mul_mem hx (Q.inv_mem hx0))).mp (by rw [map_mul, map_inv, hfx0, mul_inv_cancel])
    have hq' : P.act g (x * x0⁻¹) ∈ Q' := hQ' g _ hq
    have h1 : f (P.act g (x * x0⁻¹)) = 1 := (hker _ (hle hq')).mpr hq'
    have h2 : P.act g x = P.act g (x * x0⁻¹) * P.act g x0 := by
      rw [← map_mul]; simp
    rw [h2, map_mul, h1, one_mul, hg0 g hg]

theorem invSub_of_gens {P : Model 5} {gens : Set (Perm (Fin 5))}
    (hgens : Subgroup.closure gens = ⊤) {Q : Subgroup P.W}
    (h : ∀ g ∈ gens, ∀ x ∈ Q, P.act g x ∈ Q) : P.InvSub Q := by
  intro σ
  have hσ : σ ∈ Subgroup.closure gens := by rw [hgens]; trivial
  induction hσ using Subgroup.closure_induction with
  | mem g hg => exact h g hg
  | one => intro x hx; simpa using hx
  | mul a b _ _ ha hb =>
    intro x hx
    rw [act_mul_apply]
    exact ha _ (hb x hx)
  | inv a _ ha =>
    intro x hx
    have hinj : Function.Injective fun y : Q => (⟨P.act a y, ha y y.2⟩ : Q) := by
      intro y z hyz
      exact Subtype.ext ((P.act a).injective (congrArg Subtype.val hyz))
    obtain ⟨y, hy⟩ := Finite.injective_iff_surjective.mp hinj ⟨x, hx⟩
    have : P.act a y = x := congrArg Subtype.val hy
    rw [← this, act_inv_act]
    exact y.2

theorem Model.Faithful.of_iso {M N : Model 5} (e : M.Iso N) (h : N.Faithful) : M.Faithful := by
  rw [Model.Faithful, injective_iff_map_eq_one]
  intro σ hσ
  have hN : N.act σ = 1 := by
    ext w
    have h1 := e.map_act σ (e.toMulEquiv.symm w)
    rw [MulEquiv.apply_symm_apply] at h1
    rw [← h1, hσ]
    simp
  exact (injective_iff_map_eq_one _).mp h σ hN

theorem orth_faithful : orth.Faithful := by
  rw [Model.Faithful, injective_iff_map_eq_one]
  have h : ∀ σ : Perm (Fin 5), (∀ w : orth.W, orth.act σ w = w) → σ = 1 := by decide +kernel
  intro σ hσ
  exact h σ fun w => by rw [hσ]; rfl

theorem nat_faithful : nat.Faithful := by
  rw [Model.Faithful, injective_iff_map_eq_one]
  have h : ∀ σ : Perm (Fin 5), (∀ w : nat.W, nat.act σ w = w) → σ = 1 := by decide +kernel
  intro σ hσ
  exact h σ fun w => by rw [hσ]; rfl

theorem orth_not_iso_nat : ¬ Nonempty (orth.Iso nat) := by
  rintro ⟨e⟩
  have h1 : ∃ w : orth.W, w ≠ 1 ∧ orth.act (swap 0 1 * swap 1 2) w = w := by decide +kernel
  have h2 : ∀ w : nat.W, nat.act (swap 0 1 * swap 1 2) w = w → w = 1 := by decide +kernel
  obtain ⟨w, hw1, hw2⟩ := h1
  have := h2 (e.toMulEquiv w) (by rw [← e.map_act, hw2])
  exact hw1 (e.toMulEquiv.injective (by rw [this, map_one]))

theorem Model.Iso.card_eq {n : ℕ} {M N : Model n} (e : M.Iso N) : Nat.card M.W = Nat.card N.W :=
  Nat.card_congr e.toMulEquiv.toEquiv

end CFSG.Quasithin.F53Mod
