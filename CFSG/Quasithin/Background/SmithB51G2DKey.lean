module

public import CFSG.Quasithin.Background.SmithB51G2DOct

public section

namespace CFSG.Quasithin.B5.G2D

open CFSG.Quasithin CFSG.Quasithin.JonesParshall CFSG.Quasithin.Explicit CFSG.Open
open Polynomial Module

theorem even_finrank_of_quad {F : Type} [Field F] [Finite F] {W : Type} [AddCommGroup W]
    [Module F W] [Finite W] (J : Module.End F W) (t N : F)
    (hJ : ∀ w, J (J w) = t • J w + N • w) (hroot : ∀ c : F, c * c - t * c - N ≠ 0) :
    Even (finrank F W) := by
  classical
  set p : F[X] := X ^ 2 - C t * X - C N with hp
  have hdeg : p.natDegree = 2 := by
    rw [hp]
    compute_degree!
  have hp0 : p ≠ 0 := by
    intro h0
    rw [h0, natDegree_zero] at hdeg
    exact absurd hdeg (by norm_num)
  have hirr : Irreducible p := by
    refine irreducible_of_degree_le_three_of_not_isRoot (by rw [hdeg]; decide) (fun c hc => ?_)
    apply hroot c
    have := hc
    simp only [IsRoot, hp, eval_sub, eval_pow, eval_X, eval_mul, eval_C] at this
    linear_combination this
  have : Fact (Irreducible p) := ⟨hirr⟩
  have hker : ∀ a ∈ Ideal.span {p}, (aeval J).toRingHom a = 0 := by
    intro a ha
    obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.1 ha
    rw [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, map_mul]
    have : aeval J p = 0 := by
      rw [hp]
      ext w
      simp [pow_two, hJ]
    rw [this, mul_zero]
  let φ : AdjoinRoot p →+* Module.End F W := Ideal.Quotient.lift _ (aeval J).toRingHom hker
  let _ : Module (AdjoinRoot p) W := Module.compHom W φ
  have := (AdjoinRoot.powerBasis hp0).finite
  have h1 : Nat.card W = Nat.card (AdjoinRoot p) ^ finrank (AdjoinRoot p) W :=
    Module.natCard_eq_pow_finrank
  have h2 : Nat.card (AdjoinRoot p) = Nat.card F ^ 2 := by
    rw [Module.natCard_eq_pow_finrank (K := F), (AdjoinRoot.powerBasis hp0).finrank,
      AdjoinRoot.powerBasis_dim, hdeg]
  have h3 : Nat.card W = Nat.card F ^ finrank F W := Module.natCard_eq_pow_finrank
  rw [h2, ← pow_mul] at h1
  rw [h1] at h3
  have hq : 2 ≤ Nat.card F := Finite.one_lt_card
  exact ⟨finrank (AdjoinRoot p) W, by
    have := Nat.pow_right_injective hq h3
    omega⟩

variable {F : Type} [Field F]

theorem bilQ_comm (w w' : Ix3 → F) : bilQ w w' = bilQ w' w := by
  simp only [bilQ]
  ring

theorem bilQ_add_right (w x x' : Ix3 → F) : bilQ w (x + x') = bilQ w x + bilQ w x' := by
  rw [bilQ_comm, bilQ_add_left, bilQ_comm x, bilQ_comm x']

theorem bilQ_smul_right (c : F) (w x : Ix3 → F) : bilQ w (c • x) = c * bilQ w x := by
  rw [bilQ_comm, bilQ_smul_left, bilQ_comm]

theorem bilQ_sub_left (w w' x : Ix3 → F) : bilQ (w - w') x = bilQ w x - bilQ w' x := by
  simp only [bilQ, Pi.sub_apply]
  ring

theorem bilQ_zero_left (x : Ix3 → F) : bilQ 0 x = 0 := by
  simp [bilQ]

theorem eq_zero_of_bilQ {z : Ix3 → F} (h : ∀ w, bilQ z w = 0) : z = 0 :=
  eq_of_bilQ fun w => by rw [h, bilQ_zero_left]

@[expose] def bilQLin : (Ix3 → F) →ₗ[F] (Ix3 → F) →ₗ[F] F :=
  LinearMap.mk₂ F bilQ bilQ_add_left bilQ_smul_left bilQ_add_right bilQ_smul_right

variable [CharP F 2]

@[expose] def g2Lin (g : ↥(cayleyGroup F)) : (Ix3 → F) →ₗ[F] (Ix3 → F) where
  toFun := g2Act g
  map_add' := map_add (g2Act g)
  map_smul' c w := g2Act_smul g c w

theorem g2Act_mul_apply (g h : ↥(cayleyGroup F)) (w : Ix3 → F) :
    g2Act (g * h) w = g2Act g (g2Act h w) := by
  rw [map_mul]
  rfl

theorem g2Act_one_apply (w : Ix3 → F) : g2Act (1 : ↥(cayleyGroup F)) w = w := by
  rw [map_one]
  rfl

theorem g2Act_sub (g : ↥(cayleyGroup F)) (w w' : Ix3 → F) :
    g2Act g (w - w') = g2Act g w - g2Act g w' :=
  map_sub (g2Act g) w w'

theorem neg_eq_self (w : Ix3 → F) : -w = w :=
  funext fun i => CharTwo.neg_eq (w i)

@[expose] def fixQ (A : Subgroup ↥(cayleyGroup F)) : Submodule F (Ix3 → F) where
  carrier := {w | ∀ a ∈ A, g2Act a w = w}
  add_mem' {w w'} hw hw' a ha := by rw [map_add, hw a ha, hw' a ha]
  zero_mem' a _ := map_zero (g2Act a)
  smul_mem' c w hw a ha := by rw [g2Act_smul, hw a ha]

@[expose] noncomputable def opJLin (x : quasithinZorn F) : (Ix3 → F) →ₗ[F] (Ix3 → F) where
  toFun := opJ x
  map_add' := opJ_add x
  map_smul' := opJ_smul x

omit [CharP F 2] in
theorem opJLin_apply (x : quasithinZorn F) (w : Ix3 → F) : opJLin x w = opJ x w := rfl

omit [CharP F 2] in
theorem opJ_sub (x : quasithinZorn F) (w w' : Ix3 → F) : opJ x (w - w') = opJ x w - opJ x w' :=
  (opJLin x).map_sub w w'

theorem fix_of_fix_compl {c : ↥(cayleyGroup F)} {P P' : Submodule F (Ix3 → F)}
    (hsup : P ⊔ P' = ⊤) (hiso : ∀ w ∈ P', ∀ w' ∈ P', bilQ w w' = 0)
    (hinv : ∀ w ∈ P', g2Act c w ∈ P') (hfix : ∀ w ∈ P, g2Act c w = w) :
    ∀ w, g2Act c w = w := by
  have hP' : ∀ w' ∈ P', g2Act c w' = w' := by
    intro w' hw'
    have hz : g2Act c w' - w' ∈ P' := P'.sub_mem (hinv w' hw') hw'
    rw [← sub_eq_zero]
    refine eq_zero_of_bilQ fun y => ?_
    have hy : y ∈ P ⊔ P' := by rw [hsup]; trivial
    obtain ⟨p, hp, p', hp', rfl⟩ := Submodule.mem_sup.1 hy
    rw [bilQ_add_right, hiso _ hz _ hp', add_zero, bilQ_sub_left]
    have h1 : bilQ (g2Act c w') p = bilQ w' p := by
      conv_lhs => rw [← hfix p hp]
      exact bilQ_g2Act c w' p
    rw [h1, sub_self]
  intro w
  have hw : w ∈ P ⊔ P' := by rw [hsup]; trivial
  obtain ⟨p, hp, p', hp', rfl⟩ := Submodule.mem_sup.1 hw
  rw [map_add, hfix p hp, hP' p' hp']

omit [CharP F 2] in
theorem finrank_le_of_iso_compl {P P' : Submodule F (Ix3 → F)} (hsup : P ⊔ P' = ⊤)
    (hiso : ∀ w ∈ P', ∀ w' ∈ P', bilQ w w' = 0) : finrank F P' ≤ finrank F P := by
  let T : ↥P' →ₗ[F] Module.Dual F ↥P := (bilQLin.compl₂ P.subtype).domRestrict P'
  have hT : Function.Injective T := by
    rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    intro w hw
    rw [LinearMap.mem_ker] at hw
    rw [Submodule.mem_bot]
    apply Subtype.ext
    refine eq_zero_of_bilQ fun y => ?_
    have hy : y ∈ P ⊔ P' := by rw [hsup]; trivial
    obtain ⟨p, hp, p', hp', rfl⟩ := Submodule.mem_sup.1 hy
    rw [bilQ_add_right, hiso _ w.2 _ hp', add_zero]
    have := LinearMap.congr_fun hw ⟨p, hp⟩
    exact this
  calc finrank F P' ≤ finrank F (Module.Dual F ↥P) := LinearMap.finrank_le_finrank_of_injective hT
    _ = finrank F P := Subspace.dual_finrank_eq

theorem card_le_of_hyperplane [Finite F] {A : Subgroup ↥(cayleyGroup F)}
    (hinv : ∀ a ∈ A, a * a = 1) {P P' : Submodule F (Ix3 → F)} (hsup : P ⊔ P' = ⊤)
    (hiso : ∀ w ∈ P', ∀ w' ∈ P', bilQ w w' = 0) (hPinv : ∀ a ∈ A, ∀ w ∈ P, g2Act a w ∈ P)
    (hP'inv : ∀ a ∈ A, ∀ w ∈ P', g2Act a w ∈ P') (hdim : finrank F P = 3)
    (hD : finrank F ↥(P ⊓ fixQ A) = 2) : Nat.card A ≤ Nat.card F ^ 2 := by
  classical
  set D := P ⊓ fixQ A with hDdef
  have hDP : D ≤ P := inf_le_left
  have hlt : D < P := by
    refine lt_of_le_of_ne hDP fun h => ?_
    have h1 : finrank F D = finrank F P := by rw [h]
    omega
  obtain ⟨w₀, hw₀P, hw₀D⟩ := IsConcreteLE.exists_of_lt hlt
  have hinf : F ∙ w₀ ⊓ D = ⊥ := by
    rw [eq_bot_iff]
    intro y hy
    obtain ⟨hy1, hy2⟩ := hy
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hy1
    rw [Submodule.mem_bot]
    by_contra hc
    have hc0 : c ≠ 0 := fun h0 => hc (by rw [h0, zero_smul])
    apply hw₀D
    have := D.smul_mem c⁻¹ hy2
    rwa [smul_smul, inv_mul_cancel₀ hc0, one_smul] at this
  have hspan : F ∙ w₀ ⊔ D = P := by
    refine Submodule.eq_of_le_of_finrank_eq (sup_le ((Submodule.span_singleton_le_iff_mem _ _).2
      hw₀P) hDP) ?_
    have h1 := Submodule.finrank_sup_add_finrank_inf_eq (F ∙ w₀) D
    have hw₀0 : w₀ ≠ 0 := fun h0 => hw₀D (by rw [h0]; exact D.zero_mem)
    rw [hinf, finrank_bot, add_zero, finrank_span_singleton hw₀0, hD] at h1
    rw [h1, hdim]
  have hmemD : ∀ a ∈ A, g2Act a w₀ - w₀ ∈ D := by
    intro a ha
    have hmem : g2Act a w₀ - w₀ ∈ F ∙ w₀ ⊔ D := by
      rw [hspan]
      exact P.sub_mem (hPinv a ha w₀ hw₀P) hw₀P
    obtain ⟨y, hy, d, hd, hyd⟩ := Submodule.mem_sup.1 hmem
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hy
    have hsq : g2Act a (g2Act a w₀ - w₀) - (g2Act a w₀ - w₀) = 0 := by
      rw [g2Act_sub, ← g2Act_mul_apply, hinv a ha, g2Act_one_apply]
      have : w₀ - g2Act a w₀ = -(g2Act a w₀ - w₀) := by abel
      rw [this, neg_eq_self, sub_self]
    have hdfix : g2Act a d = d := hd.2 a ha
    rw [← hyd, map_add, g2Act_smul, hdfix] at hsq
    have h2 : c • (g2Act a w₀ - w₀) = 0 := by
      have : c • g2Act a w₀ + d - (c • w₀ + d) = c • (g2Act a w₀ - w₀) := by
        rw [smul_sub]
        abel
      rw [← this]
      exact hsq
    rw [← hyd, smul_add, smul_smul] at h2
    by_cases hc : c = 0
    · rw [← hyd, hc, zero_smul, zero_add]
      exact hd
    · exfalso
      apply hw₀D
      have h3 : (c * c) • w₀ = -(c • d) := eq_neg_of_add_eq_zero_left h2
      have h4 : (c * c) • w₀ ∈ D := by rw [h3]; exact D.neg_mem (D.smul_mem c hd)
      have h5 := D.smul_mem (c * c)⁻¹ h4
      rwa [smul_smul, inv_mul_cancel₀ (mul_ne_zero hc hc), one_smul] at h5
  let φ : ↥A → ↥D := fun a => ⟨g2Act a w₀ - w₀, hmemD a a.2⟩
  have hφ : Function.Injective φ := by
    intro a b hab
    have h1 : g2Act (a : ↥(cayleyGroup F)) w₀ = g2Act (b : ↥(cayleyGroup F)) w₀ := by
      have := congrArg Subtype.val hab
      simpa [φ] using this
    set c : ↥(cayleyGroup F) := (b : ↥(cayleyGroup F))⁻¹ * a with hc
    have hcA : c ∈ A := A.mul_mem (A.inv_mem b.2) a.2
    have hcw : g2Act c w₀ = w₀ := by
      rw [hc, g2Act_mul_apply, h1, ← g2Act_mul_apply, inv_mul_cancel, g2Act_one_apply]
    have hcP : ∀ w ∈ P, g2Act c w = w := by
      intro w hw
      rw [← hspan] at hw
      obtain ⟨y, hy, d, hd, rfl⟩ := Submodule.mem_sup.1 hw
      obtain ⟨e, rfl⟩ := Submodule.mem_span_singleton.1 hy
      rw [map_add, g2Act_smul, hcw, hd.2 c hcA]
    have hall := fix_of_fix_compl hsup hiso (hP'inv c hcA) hcP
    have hc1 : c = 1 := eq_one_of_g2Act c hall
    apply Subtype.ext
    rw [hc, inv_mul_eq_one] at hc1
    exact hc1.symm
  calc Nat.card A ≤ Nat.card D := Nat.card_le_card_of_injective φ hφ
    _ = Nat.card F ^ finrank F D := Module.natCard_eq_pow_finrank
    _ = Nat.card F ^ 2 := by rw [hD]

omit [CharP F 2] in
theorem finrank_Q : finrank F (Ix3 → F) = 6 := by
  rw [Module.finrank_fintype_fun_eq_card]
  rfl

omit [CharP F 2] in
theorem finrank_eq_of_card [Finite F] {W : Submodule F (Ix3 → F)} {k : ℕ}
    (h : Nat.card W = Nat.card F ^ k) : finrank F W = k := by
  have hq : 2 ≤ Nat.card F := Finite.one_lt_card
  rw [Module.natCard_eq_pow_finrank (K := F)] at h
  exact Nat.pow_right_injective hq h

omit [CharP F 2] in
theorem cayleyNorm_add_smul_one (x : quasithinZorn F) (c : F) :
    cayleyNorm (x + c • cayleyOne F) = cayleyNorm x + c * cayleyTr x + c * c := by
  rw [zorn_eta x, cayleyOne_eq, zmk_smul, zmk_add, cayleyNorm_zmk, cayleyNorm_zmk, cayleyTr_zmk]
  ring

theorem shift_eq_zero_or {g : ↥(cayleyGroup F)} {x : quasithinZorn F} {c : F}
    (h : cgE g x = x + c • cayleyOne F) : c = 0 ∨ c = cayleyTr x := by
  have h1 := cg_norm g x
  rw [h, cayleyNorm_add_smul_one] at h1
  have h2 : c * (c + cayleyTr x) = 0 := by linear_combination h1
  rcases mul_eq_zero.1 h2 with h3 | h3
  · exact Or.inl h3
  · right
    rw [eq_neg_of_add_eq_zero_left h3, CharTwo.neg_eq]

omit [CharP F 2] in
theorem cg_add_smul_one (g : ↥(cayleyGroup F)) (y : quasithinZorn F) (c : F) :
    cgE g (y + c • cayleyOne F) = cgE g y + c • cayleyOne F := by
  rw [map_add, map_smul, cg_one]

theorem false_of_shift [Finite F] {A : Subgroup ↥(cayleyGroup F)}
    (hcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) (hinv : ∀ a ∈ A, a * a = 1)
    (hA : 2 < Nat.card A) (hfix : Nat.card (fixQ A) = Nat.card F ^ 3)
    {x : quasithinZorn F} (hx : cayleyTr x ≠ 0)
    (hxA : ∀ a ∈ A, cgE a x = x ∨ cgE a x = x + cayleyTr x • cayleyOne F)
    {a₁ : ↥(cayleyGroup F)} (ha₁ : a₁ ∈ A) (ha₁x : cgE a₁ x = x + cayleyTr x • cayleyOne F) :
    False := by
  classical
  let A₀ : Subgroup ↥(cayleyGroup F) :=
    { carrier := {a | a ∈ A ∧ cgE a x = x}
      mul_mem' := fun {a b} ha hb => ⟨A.mul_mem ha.1 hb.1, by rw [cg_mul_apply, hb.2, ha.2]⟩
      one_mem' := ⟨A.one_mem, rfl⟩
      inv_mem' := fun {a} ha => ⟨A.inv_mem ha.1, by
        conv_lhs => rw [← ha.2]
        exact cg_inv_apply a x⟩ }
  have hsplit : ∀ a ∈ A, a ∈ A₀ ∨ a₁ * a ∈ A₀ := by
    intro a ha
    rcases hxA a ha with h | h
    · exact Or.inl ⟨ha, h⟩
    · right
      refine ⟨A.mul_mem ha₁ ha, ?_⟩
      rw [cg_mul_apply, h, cg_add_smul_one, ha₁x, add_assoc, ← add_smul,
        CharTwo.add_self_eq_zero, zero_smul, add_zero]
  have ha₁a : ∀ a, a₁ * (a₁ * a) = a := fun a => by rw [← mul_assoc, hinv a₁ ha₁, one_mul]
  set X := fixQ A₀ with hX
  have hfixA : ∀ w, w ∈ fixQ A ↔ w ∈ X ∧ g2Act a₁ w = w := by
    intro w
    constructor
    · intro hw
      exact ⟨fun a ha => hw a ha.1, hw a₁ ha₁⟩
    · rintro ⟨hw, hw1⟩ a ha
      rcases hsplit a ha with h | h
      · exact hw a h
      · rw [← ha₁a a, g2Act_mul_apply, hw _ h, hw1]
  have hXinv : ∀ w ∈ X, g2Act a₁ w ∈ X := by
    intro w hw a ha
    rw [← g2Act_mul_apply, hcomm a ha.1 a₁ ha₁, g2Act_mul_apply, hw a ha]
  let ψ : ↥X →ₗ[F] ↥X :=
    (g2Lin a₁ - LinearMap.id).restrict (fun w hw => X.sub_mem (hXinv w hw) hw)
  have hψ : ∀ w : ↥X, (ψ w : Ix3 → F) = g2Act a₁ w - w := fun w => rfl
  have hker : (LinearMap.ker ψ).map X.subtype = fixQ A := by
    ext w
    constructor
    · rintro ⟨y, hy, rfl⟩
      have h1 : g2Act a₁ (y : Ix3 → F) - y = 0 := by
        rw [← hψ, LinearMap.mem_ker.1 hy]
        rfl
      exact (hfixA _).2 ⟨y.2, sub_eq_zero.1 h1⟩
    · intro hw
      obtain ⟨hwX, hw1⟩ := (hfixA w).1 hw
      refine ⟨⟨w, hwX⟩, ?_, rfl⟩
      show ψ ⟨w, hwX⟩ = 0
      apply Subtype.ext
      rw [hψ]
      simp [hw1]
  have hrange : (LinearMap.range ψ).map X.subtype = fixQ A := by
    ext w
    constructor
    · rintro ⟨y, ⟨z, rfl⟩, rfl⟩
      refine (hfixA _).2 ⟨(ψ z).2, ?_⟩
      show g2Act a₁ (ψ z : Ix3 → F) = ψ z
      rw [hψ, g2Act_sub, ← g2Act_mul_apply, hinv a₁ ha₁, g2Act_one_apply,
        show (z : Ix3 → F) - g2Act a₁ z = -(g2Act a₁ z - z) by abel, neg_eq_self]
    · intro hw
      obtain ⟨hwX, hw1⟩ := (hfixA w).1 hw
      have hJX : (cayleyTr x)⁻¹ • opJ x w ∈ X := by
        refine X.smul_mem _ (fun a ha => ?_)
        have h0 : cgE a x = x + (0 : F) • cayleyOne F := by rw [zero_smul, add_zero]; exact ha.2
        rw [g2Act_opJ hx h0, hwX a ha, zero_smul, add_zero]
      refine ⟨ψ ⟨_, hJX⟩, ⟨⟨_, hJX⟩, rfl⟩, ?_⟩
      show (ψ ⟨_, hJX⟩ : Ix3 → F) = w
      rw [hψ]
      show g2Act a₁ ((cayleyTr x)⁻¹ • opJ x w) - (cayleyTr x)⁻¹ • opJ x w = w
      rw [g2Act_smul, g2Act_opJ hx ha₁x, hw1, ← smul_sub, add_sub_cancel_left, smul_smul,
        inv_mul_cancel₀ hx, one_smul]
  have hfr : finrank F (fixQ A) = 3 := finrank_eq_of_card hfix
  have hX6 : finrank F X = 6 := by
    have h1 := LinearMap.finrank_range_add_finrank_ker ψ
    have h2 : finrank F (LinearMap.ker ψ) = 3 := by
      rw [← hfr, ← hker, Submodule.finrank_map_subtype_eq]
    have h3 : finrank F (LinearMap.range ψ) = 3 := by
      rw [← hfr, ← hrange, Submodule.finrank_map_subtype_eq]
    omega
  have hXtop : X = ⊤ := Submodule.eq_top_of_finrank_eq (by rw [hX6, finrank_Q])
  have hA₀1 : ∀ a ∈ A₀, a = 1 := fun a ha =>
    eq_one_of_g2Act a (fun w => (show w ∈ X by rw [hXtop]; trivial) a ha)
  have hsub : ∀ a ∈ A, a = 1 ∨ a = a₁ := by
    intro a ha
    rcases hsplit a ha with h | h
    · exact Or.inl (hA₀1 a h)
    · right
      have h1 := hA₀1 _ h
      rw [← ha₁a a, h1, mul_one]
  have hne : a₁ ≠ 1 := by
    intro h1
    have h4 := ha₁x
    rw [h1] at h4
    have h5 : cayleyTr x • cayleyOne F = 0 := by
      have : cgE (1 : ↥(cayleyGroup F)) x = x := rfl
      rw [this] at h4
      exact add_eq_left.1 h4.symm
    have h6 := congrArg Prod.fst h5
    apply hx
    simpa [cayleyOne] using h6
  have hcard : Nat.card A ≤ 2 := by
    let f : ↥A → Bool := fun a => decide ((a : ↥(cayleyGroup F)) = 1)
    have hf : Function.Injective f := by
      intro a b hab
      apply Subtype.ext
      simp only [f] at hab
      rcases hsub a a.2 with ha1 | ha1 <;> rcases hsub b b.2 with hb1 | hb1
      · rw [ha1, hb1]
      · rw [ha1, hb1] at hab
        simp [hne] at hab
      · rw [ha1, hb1] at hab
        simp [hne] at hab
      · rw [ha1, hb1]
    calc Nat.card A ≤ Nat.card Bool := Nat.card_le_card_of_injective f hf
      _ = 2 := by simp
  omega

theorem false_of_fix [Finite F] {A : Subgroup ↥(cayleyGroup F)} (hinv : ∀ a ∈ A, a * a = 1)
    (hA : Nat.card F ^ 2 < Nat.card A) (hfix : Nat.card (fixQ A) = Nat.card F ^ 3)
    {x : quasithinZorn F} (hx : cayleyTr x ≠ 0) (hxA : ∀ a ∈ A, cgE a x = x) : False := by
  classical
  set t := cayleyTr x with ht
  set N := cayleyNorm x with hN
  have hJA : ∀ a ∈ A, ∀ w, g2Act a (opJ x w) = opJ x (g2Act a w) := by
    intro a ha w
    have h0 : cgE a x = x + (0 : F) • cayleyOne F := by rw [zero_smul, add_zero]; exact hxA a ha
    rw [g2Act_opJ hx h0, zero_smul, add_zero]
  have hfr : finrank F (fixQ A) = 3 := finrank_eq_of_card hfix
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  by_cases hr : ∃ l : F, l * l - t * l - N = 0
  · obtain ⟨l, hl⟩ := hr
    set l' := t - l with hl'
    set P₁ := LinearMap.ker (opJLin x - l • LinearMap.id) with hP₁
    set P₂ := LinearMap.ker (opJLin x - l' • LinearMap.id) with hP₂
    have hmem₁ : ∀ w, w ∈ P₁ ↔ opJ x w = l • w := by
      intro w
      rw [hP₁, LinearMap.mem_ker, LinearMap.sub_apply, opJLin_apply, LinearMap.smul_apply,
        LinearMap.id_apply, sub_eq_zero]
    have hmem₂ : ∀ w, w ∈ P₂ ↔ opJ x w = l' • w := by
      intro w
      rw [hP₂, LinearMap.mem_ker, LinearMap.sub_apply, opJLin_apply, LinearMap.smul_apply,
        LinearMap.id_apply, sub_eq_zero]
    have hll : l - l' ≠ 0 := by
      have : l - l' = -t := by rw [hl']; linear_combination l * h2
      rw [this]
      exact neg_ne_zero.2 hx
    have hinf : P₁ ⊓ P₂ = ⊥ := by
      rw [eq_bot_iff]
      rintro w ⟨hw1, hw2⟩
      rw [Submodule.mem_bot]
      have h1 := (hmem₁ w).1 hw1
      rw [(hmem₂ w).1 hw2] at h1
      have h3 : (l - l') • w = 0 := by rw [sub_smul, h1, sub_self]
      exact (smul_eq_zero.1 h3).resolve_left hll
    have hsup : P₁ ⊔ P₂ = ⊤ := by
      rw [eq_top_iff]
      intro w _
      have hw1 : opJ x w - l' • w ∈ P₁ := by
        rw [hmem₁, opJ_sub, opJ_smul, opJ_opJ hx, smul_sub, smul_smul]
        have : t • opJ x w + N • w - l' • opJ x w = l • opJ x w - (l * l') • w := by
          rw [hl']
          have hN' : N = -(l * (t - l)) := by linear_combination -hl
          rw [hN', neg_smul]
          module
        exact this
      have hw2 : opJ x w - l • w ∈ P₂ := by
        rw [hmem₂, opJ_sub, opJ_smul, opJ_opJ hx, smul_sub, smul_smul]
        have : t • opJ x w + N • w - l • opJ x w = l' • opJ x w - (l' * l) • w := by
          rw [hl']
          have hN' : N = -(l * (t - l)) := by linear_combination -hl
          rw [hN', neg_smul]
          module
        exact this
      have hw : w = (l - l')⁻¹ • ((opJ x w - l' • w) - (opJ x w - l • w)) := by
        rw [show (opJ x w - l' • w) - (opJ x w - l • w) = (l - l') • w by module, smul_smul,
          inv_mul_cancel₀ hll, one_smul]
      rw [hw]
      exact Submodule.smul_mem _ _ (Submodule.sub_mem _ (Submodule.mem_sup_left hw1)
        (Submodule.mem_sup_right hw2))
    have hiso : ∀ c : F, ∀ w, opJ x w = c • w → ∀ w', opJ x w' = c • w' → bilQ w w' = 0 := by
      intro c w hw w' hw'
      have h1 := bilQ_opJ_add hx w w'
      rw [hw, hw', bilQ_smul_left, bilQ_smul_right] at h1
      have h3 : t * bilQ w w' = 0 := by linear_combination -h1 + c * bilQ w w' * h2
      exact (mul_eq_zero.1 h3).resolve_left hx
    have hiso₁ : ∀ w ∈ P₁, ∀ w' ∈ P₁, bilQ w w' = 0 := fun w hw w' hw' =>
      hiso l w ((hmem₁ w).1 hw) w' ((hmem₁ w').1 hw')
    have hiso₂ : ∀ w ∈ P₂, ∀ w' ∈ P₂, bilQ w w' = 0 := fun w hw w' hw' =>
      hiso l' w ((hmem₂ w).1 hw) w' ((hmem₂ w').1 hw')
    have hinv₁ : ∀ a ∈ A, ∀ w ∈ P₁, g2Act a w ∈ P₁ := by
      intro a ha w hw
      rw [hmem₁, ← hJA a ha, (hmem₁ w).1 hw, g2Act_smul]
    have hinv₂ : ∀ a ∈ A, ∀ w ∈ P₂, g2Act a w ∈ P₂ := by
      intro a ha w hw
      rw [hmem₂, ← hJA a ha, (hmem₂ w).1 hw, g2Act_smul]
    have hd₁ : finrank F P₂ ≤ finrank F P₁ := finrank_le_of_iso_compl hsup hiso₂
    have hd₂ : finrank F P₁ ≤ finrank F P₂ :=
      finrank_le_of_iso_compl (by rw [sup_comm]; exact hsup) hiso₁
    have hd : finrank F P₁ + finrank F P₂ = 6 := by
      have h1 := Submodule.finrank_sup_add_finrank_inf_eq P₁ P₂
      rw [hsup, hinf, finrank_bot, add_zero, finrank_top, finrank_Q] at h1
      exact h1.symm
    have hP₁3 : finrank F P₁ = 3 := by omega
    have hP₂3 : finrank F P₂ = 3 := by omega
    have hdec : (P₁ ⊓ fixQ A) ⊔ (P₂ ⊓ fixQ A) = fixQ A := by
      refine le_antisymm (sup_le inf_le_right inf_le_right) (fun w hw => ?_)
      have hw' : w ∈ P₁ ⊔ P₂ := by rw [hsup]; trivial
      obtain ⟨w₁, hw₁, w₂, hw₂, rfl⟩ := Submodule.mem_sup.1 hw'
      have hfix₁ : ∀ a ∈ A, g2Act a w₁ = w₁ ∧ g2Act a w₂ = w₂ := by
        intro a ha
        have h1 := hw a ha
        rw [map_add] at h1
        have h3 : g2Act a w₁ - w₁ ∈ P₁ ⊓ P₂ := by
          refine ⟨P₁.sub_mem (hinv₁ a ha w₁ hw₁) hw₁, ?_⟩
          have : g2Act a w₁ - w₁ = w₂ - g2Act a w₂ := by
            rw [sub_eq_sub_iff_add_eq_add, h1, add_comm]
          rw [this]
          exact P₂.sub_mem hw₂ (hinv₂ a ha w₂ hw₂)
        rw [hinf, Submodule.mem_bot, sub_eq_zero] at h3
        refine ⟨h3, ?_⟩
        rw [h3] at h1
        exact add_left_cancel h1
      exact Submodule.add_mem_sup ⟨hw₁, fun a ha => (hfix₁ a ha).1⟩
        ⟨hw₂, fun a ha => (hfix₁ a ha).2⟩
    have hdecinf : (P₁ ⊓ fixQ A) ⊓ (P₂ ⊓ fixQ A) = ⊥ := by
      rw [eq_bot_iff, ← hinf]
      exact le_inf (inf_le_left.trans inf_le_left) (inf_le_right.trans inf_le_left)
    have hsum : finrank F ↥(P₁ ⊓ fixQ A) + finrank F ↥(P₂ ⊓ fixQ A) = 3 := by
      have h1 := Submodule.finrank_sup_add_finrank_inf_eq (P₁ ⊓ fixQ A) (P₂ ⊓ fixQ A)
      rw [hdec, hdecinf, finrank_bot, add_zero, hfr] at h1
      exact h1.symm
    have hle₁ : finrank F ↥(P₁ ⊓ fixQ A) ≤ 3 :=
      hP₁3 ▸ Submodule.finrank_mono inf_le_left
    have hle₂ : finrank F ↥(P₂ ⊓ fixQ A) ≤ 3 :=
      hP₂3 ▸ Submodule.finrank_mono inf_le_left
    have hq : 2 ≤ Nat.card F := Finite.one_lt_card
    by_cases e₁ : finrank F ↥(P₁ ⊓ fixQ A) = 2
    · have := card_le_of_hyperplane hinv hsup hiso₂ hinv₁ hinv₂ hP₁3 e₁
      omega
    by_cases e₂ : finrank F ↥(P₂ ⊓ fixQ A) = 2
    · have := card_le_of_hyperplane hinv (by rw [sup_comm]; exact hsup) hiso₁ hinv₂ hinv₁
        hP₂3 e₂
      omega
    have hall : ∀ a ∈ A, a = 1 := by
      intro a ha
      rcases (show finrank F ↥(P₁ ⊓ fixQ A) = 3 ∨ finrank F ↥(P₂ ⊓ fixQ A) = 3 by omega)
        with e | e
      · have hP : P₁ ⊓ fixQ A = P₁ :=
          Submodule.eq_of_le_of_finrank_eq inf_le_left (by rw [e, hP₁3])
        refine eq_one_of_g2Act a (fix_of_fix_compl hsup hiso₂ (hinv₂ a ha) fun w hw => ?_)
        rw [← hP] at hw
        exact hw.2 a ha
      · have hP : P₂ ⊓ fixQ A = P₂ :=
          Submodule.eq_of_le_of_finrank_eq inf_le_left (by rw [e, hP₂3])
        refine eq_one_of_g2Act a (fix_of_fix_compl (by rw [sup_comm]; exact hsup) hiso₁
          (hinv₁ a ha) fun w hw => ?_)
        rw [← hP] at hw
        exact hw.2 a ha
    have hA1 : Nat.card A ≤ 1 := by
      have hinj : Function.Injective (fun _ : ↥A => ()) := fun a b _ =>
        Subtype.ext (by rw [hall a a.2, hall b b.2])
      calc Nat.card A ≤ Nat.card Unit := Nat.card_le_card_of_injective _ hinj
        _ = 1 := Nat.card_unique
    have : 1 ≤ Nat.card F ^ 2 := Nat.one_le_pow _ _ (by omega)
    omega
  · push Not at hr
    have hW : ∀ w ∈ fixQ A, opJLin x w ∈ fixQ A := fun w hw a ha => by
      rw [opJLin_apply, hJA a ha, hw a ha]
    let JW := (opJLin x).restrict hW
    have hJW : ∀ w, JW (JW w) = t • JW w + N • w := fun w => Subtype.ext (opJ_opJ hx w)
    have := even_finrank_of_quad JW t N hJW hr
    rw [hfr] at this
    exact absurd this (by decide)

theorem false_of_offender [Finite F] {A : Subgroup ↥(cayleyGroup F)}
    (hcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) (hinv : ∀ a ∈ A, a * a = 1)
    (hA : Nat.card A = Nat.card F ^ 3) (hfix : Nat.card (fixQ A) = Nat.card F ^ 3)
    {x : quasithinZorn F} (hx : cayleyTr x ≠ 0)
    (hxA : ∀ a ∈ A, ∃ c : F, cgE a x = x + c • cayleyOne F) : False := by
  have hq : 2 ≤ Nat.card F := Finite.one_lt_card
  have hshift : ∀ a ∈ A, cgE a x = x ∨ cgE a x = x + cayleyTr x • cayleyOne F := by
    intro a ha
    obtain ⟨c, hc⟩ := hxA a ha
    rcases shift_eq_zero_or hc with h0 | h0
    · left
      rw [hc, h0, zero_smul, add_zero]
    · right
      rw [hc, h0]
  by_cases hmove : ∃ a₁ ∈ A, cgE a₁ x ≠ x
  · obtain ⟨a₁, ha₁, ha₁x⟩ := hmove
    have h1 : cgE a₁ x = x + cayleyTr x • cayleyOne F := (hshift a₁ ha₁).resolve_left ha₁x
    refine false_of_shift hcomm hinv ?_ hfix hx hshift ha₁ h1
    have : 2 ^ 3 ≤ Nat.card F ^ 3 := Nat.pow_le_pow_left hq 3
    omega
  · push Not at hmove
    refine false_of_fix hinv ?_ hfix hx hmove
    rw [hA]
    exact Nat.pow_lt_pow_right (by omega) (by norm_num)

end CFSG.Quasithin.B5.G2D
