module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.SubgroupConjAction
public import CFSG.LocalAnalysis.SectionRank.Ccomm.ElementaryAut

public section

namespace CFSG.Walter.W67.P56Ab

section conj

variable {A : Type*} [Group A]

@[expose] noncomputable def conjAut (X W : Subgroup A) (h : X ≤ Subgroup.normalizer (W : Set A)) :
    X →* MulAut W :=
  @MulDistribMulAction.toMulAut X W _ _ (Subgroup.conjMulDistribMulActionOfLeNormalizer X W h)

theorem conjAut_apply_coe (X W : Subgroup A) (h : X ≤ Subgroup.normalizer (W : Set A)) (x : X)
    (w : W) : ((conjAut X W h x w : W) : A) = (x : A) * w * (x : A)⁻¹ := rfl

theorem conjAut_eq_one_iff (X W : Subgroup A) (h : X ≤ Subgroup.normalizer (W : Set A))
    (x : X) : conjAut X W h x = 1 ↔ ∀ w ∈ W, (x : A) * w = w * x := by
  constructor
  · intro hx w hw
    have := congrArg (fun α : MulAut W => ((α ⟨w, hw⟩ : W) : A)) hx
    simp only [conjAut_apply_coe, MulAut.one_apply] at this
    calc (x : A) * w = (x : A) * w * (x : A)⁻¹ * x := by group
      _ = w * x := by rw [this]
  · intro hx
    ext w
    rw [conjAut_apply_coe, MulAut.one_apply, hx w w.2, mul_inv_cancel_right]

end conj

theorem eq_one_of_forall_pow_eq_one {V : Type*} [Group V] {p : ℕ} [Fact p.Prime]
    (hV : IsPGroup p V) (hcomm : ∀ a b : V, a * b = b * a) (α : MulAut V)
    (hα : Nat.Coprime (orderOf α) p) (hfix : ∀ x : V, x ^ p = 1 → α x = x) : α = 1 := by
  have key : ∀ k : ℕ, ∀ x : V, x ^ (p ^ k) = 1 → α x = x := by
    intro k
    induction k with
    | zero =>
      intro x hx
      rw [pow_zero, pow_one] at hx
      rw [hx, map_one]
    | succ k ih =>
      intro x hx
      have hxp : α (x ^ p) = x ^ p := ih _ (by rw [← pow_mul, ← pow_succ']; exact hx)
      set d := α x * x⁻¹ with hd
      have hdp : d ^ p = 1 := by
        have hmulpow : ∀ (a b : V) (m : ℕ), (a * b) ^ m = a ^ m * b ^ m := by
          intro a b m
          induction m with
          | zero => simp
          | succ m ihm =>
            rw [pow_succ, ihm, pow_succ, pow_succ, mul_assoc, mul_assoc]
            congr 1
            rw [← mul_assoc, hcomm (b ^ m) a, mul_assoc]
        rw [hd, hmulpow, ← map_pow, hxp, inv_pow, mul_inv_cancel]
      have hαd : α d = d := hfix d hdp
      have hαx : α x = d * x := by rw [hd, inv_mul_cancel_right]
      have hiter : ∀ j : ℕ, (α ^ j) x = d ^ j * x := by
        intro j
        induction j with
        | zero => simp
        | succ j ihj =>
          rw [pow_succ', MulAut.mul_apply, ihj, map_mul, map_pow, hαd, hαx, pow_succ',
            ← mul_assoc, hcomm (d ^ j) d]
      have hdm : d ^ orderOf α = 1 := by
        have := hiter (orderOf α)
        rw [pow_orderOf_eq_one, MulAut.one_apply] at this
        exact (mul_eq_right.mp this.symm)
      have hd1 : d = 1 := by
        have h1 : orderOf d ∣ Nat.gcd (orderOf α) p :=
          Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hdm) (orderOf_dvd_of_pow_eq_one hdp)
        rw [hα] at h1
        exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp h1)
      rw [hαx, hd1, one_mul]
  ext x
  obtain ⟨k, hk⟩ := hV x
  rw [key k x hk, MulAut.one_apply]

theorem card_le_of_isCyclic {C : Type*} [Group C] [IsCyclic C] {p : ℕ} (hp : 0 < p)
    (E : Subgroup C) (hE : ∀ x ∈ E, x ^ p = 1) : Nat.card E ≤ p := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := E)
  have hcard : Nat.card E = orderOf g := (orderOf_eq_card_of_forall_mem_zpowers hg).symm
  rw [hcard]
  have : g ^ p = 1 := Subtype.ext (by simpa using hE g g.2)
  exact orderOf_le_of_pow_eq_one hp this

theorem card_le_sq_of_ker_inf {X C₁ C₂ : Type*} [Group X] [Finite X] [Group C₁] [Group C₂]
    [IsCyclic C₁] [IsCyclic C₂] (f₁ : X →* C₁) (f₂ : X →* C₂)
    (hinj : ∀ x : X, f₁ x = 1 → f₂ x = 1 → x = 1) {p : ℕ} (hp : 0 < p) (E : Subgroup X)
    (hE : ∀ x ∈ E, x ^ p = 1) : Nat.card E ≤ p ^ 2 := by
  set g₁ := f₁.comp E.subtype
  have hcard := Subgroup.card_ker_mul_card_range g₁
  have hrange : Nat.card g₁.range ≤ p := by
    have : g₁.range = E.map f₁ := by
      rw [MonoidHom.range_comp, Subgroup.range_subtype]
    rw [this]
    refine card_le_of_isCyclic hp _ ?_
    rintro _ ⟨x, hx, rfl⟩
    rw [← map_pow, hE x hx, map_one]
  have hker : Nat.card g₁.ker ≤ p := by
    set g₂ := f₂.comp (E.subtype.comp g₁.ker.subtype)
    have hg₂ : Function.Injective g₂ := by
      rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
      intro y hy
      rw [Subgroup.mem_bot]
      have h1 : f₁ ((y : E) : X) = 1 := y.2
      have h2 : f₂ ((y : E) : X) = 1 := hy
      exact Subtype.ext (Subtype.ext (hinj _ h1 h2))
    rw [Nat.card_congr (MonoidHom.ofInjective hg₂).toEquiv]
    refine card_le_of_isCyclic hp _ ?_
    rintro _ ⟨y, rfl⟩
    rw [← map_pow]
    have : y ^ p = 1 := Subtype.ext (Subtype.ext (by simpa using hE _ (y : E).2))
    rw [this, map_one]
  rw [← hcard, sq]
  exact Nat.mul_le_mul hker hrange

theorem exists_injective_of_factorization_le {X : Type*} [Group X] [Finite X] {p : ℕ}
    [Fact p.Prime] (T : Subgroup X)
    (hT : (Nat.card X).factorization p ≤ (Nat.card T).factorization p) (R : Subgroup X)
    (hR : IsPGroup p R) : ∃ f : R →* T, Function.Injective f := by
  classical
  obtain ⟨S₀⟩ := (inferInstance : Nonempty (Sylow p T))
  set S : Subgroup X := (S₀ : Subgroup T).map T.subtype with hSdef
  have hTX : (Nat.card T).factorization p ≤ (Nat.card X).factorization p :=
    (Nat.factorization_le_iff_dvd Nat.card_pos.ne' Nat.card_pos.ne').mpr
      (Subgroup.card_subgroup_dvd_card T) p
  have hScard : Nat.card S = p ^ (Nat.card X).factorization p := by
    rw [hSdef, Subgroup.card_map_of_injective T.subtype_injective, Sylow.card_eq_multiplicity,
      le_antisymm hTX hT]
  set S' : Sylow p X := Sylow.ofCard S hScard
  obtain ⟨Q, hRQ⟩ := hR.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq X Q S'
  have hmem : ∀ r : R, g * (r : X) * g⁻¹ ∈ S := by
    intro r
    have h1 : (r : X) ∈ (Q : Subgroup X) := hRQ r.2
    have h2 : g * (r : X) * g⁻¹ ∈ ((g • Q : Sylow p X) : Subgroup X) := by
      rw [Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists]
      exact ⟨r, h1, by rw [MulAut.smul_def, MulAut.conj_apply]⟩
    rw [hg] at h2
    exact h2
  have hST : S ≤ T := Subgroup.map_subtype_le _
  refine ⟨{ toFun := fun r => ⟨g * r * g⁻¹, hST (hmem r)⟩
            map_one' := Subtype.ext (by simp)
            map_mul' := fun a b => Subtype.ext (by simp [mul_assoc]) }, ?_⟩
  intro a b hab
  have := congrArg Subtype.val hab
  simp only [MonoidHom.coe_mk, OneHom.coe_mk, mul_left_inj, mul_right_inj] at this
  exact Subtype.ext this

section torus

variable {v : ℕ} [hv : Fact v.Prime]

@[expose] noncomputable def torusAut (u : Fin 2 → (ZMod v)ˣ) :
    MulAut (Multiplicative (Fin 2 → ZMod v)) where
  toFun x := Multiplicative.ofAdd fun i => (u i : ZMod v) * Multiplicative.toAdd x i
  invFun x := Multiplicative.ofAdd fun i => ((u i)⁻¹ : (ZMod v)ˣ) * Multiplicative.toAdd x i
  left_inv x := by
    apply Multiplicative.toAdd.injective
    funext i
    change ((u i)⁻¹ : (ZMod v)ˣ) * ((u i : ZMod v) * Multiplicative.toAdd x i) =
      Multiplicative.toAdd x i
    rw [Units.inv_mul_cancel_left]
  right_inv x := by
    apply Multiplicative.toAdd.injective
    funext i
    change (u i : ZMod v) * (((u i)⁻¹ : (ZMod v)ˣ) * Multiplicative.toAdd x i) =
      Multiplicative.toAdd x i
    rw [Units.mul_inv_cancel_left]
  map_mul' x y := by
    apply Multiplicative.toAdd.injective
    funext i
    change (u i : ZMod v) * (Multiplicative.toAdd x i + Multiplicative.toAdd y i) =
      (u i : ZMod v) * Multiplicative.toAdd x i + (u i : ZMod v) * Multiplicative.toAdd y i
    rw [mul_add]

theorem torusAut_apply (u : Fin 2 → (ZMod v)ˣ) (x : Multiplicative (Fin 2 → ZMod v))
    (i : Fin 2) :
    Multiplicative.toAdd (torusAut u x) i = (u i : ZMod v) * Multiplicative.toAdd x i := rfl

@[expose] noncomputable def torus (v : ℕ) [Fact v.Prime] :
    (Fin 2 → (ZMod v)ˣ) →* MulAut (Multiplicative (Fin 2 → ZMod v)) where
  toFun := torusAut
  map_one' := MulEquiv.ext fun x => Multiplicative.toAdd.injective (funext fun i => by
    rw [torusAut_apply, Pi.one_apply, Units.val_one, one_mul, MulAut.one_apply])
  map_mul' u u' := MulEquiv.ext fun x => Multiplicative.toAdd.injective (funext fun i => by
    rw [MulAut.mul_apply, torusAut_apply, torusAut_apply, torusAut_apply, Pi.mul_apply,
      Units.val_mul, mul_assoc])

theorem torus_injective : Function.Injective (torus v) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro u hu
  rw [Subgroup.mem_bot]
  funext i
  have := congrArg (fun α : MulAut (Multiplicative (Fin 2 → ZMod v)) =>
    Multiplicative.toAdd (α (Multiplicative.ofAdd fun _ => (1 : ZMod v))) i) hu
  have h' : (u i : ZMod v) * 1 = 1 := this
  rw [mul_one] at h'
  show u i = 1
  exact Units.ext (by rw [h', Units.val_one])

theorem factorization_card_GL_two (h3 : 3 ∣ v - 1) :
    (Nat.card (GL (Fin 2) (ZMod v))).factorization 3 = 2 * (v - 1).factorization 3 := by
  have hv2 : 2 ≤ v := hv.out.two_le
  rw [SectionRank.Ccomm.card_GL_zmod, Fin.prod_univ_two]
  simp only [Fin.val_zero, Fin.val_one, pow_zero, pow_one]
  obtain ⟨w, rfl⟩ : ∃ w, v = w + 1 := ⟨v - 1, by omega⟩
  have e1 : (w + 1) ^ 2 - 1 = w * (w + 2) := Nat.sub_eq_of_eq_add (by ring)
  have e2 : (w + 1) ^ 2 - (w + 1) = (w + 1) * w := Nat.sub_eq_of_eq_add (by ring)
  rw [e1, e2, Nat.add_sub_cancel]
  rw [Nat.add_sub_cancel] at h3
  have hw : w ≠ 0 := by omega
  have h3v : ¬ 3 ∣ w + 2 := by omega
  have h3p : ¬ 3 ∣ w + 1 := by omega
  rw [Nat.factorization_mul (mul_ne_zero hw (by omega)) (mul_ne_zero (by omega) hw),
    Nat.factorization_mul hw (by omega), Nat.factorization_mul (by omega) hw]
  simp only [Finsupp.coe_add, Pi.add_apply]
  rw [Nat.factorization_eq_zero_of_not_dvd h3v, Nat.factorization_eq_zero_of_not_dvd h3p]
  ring

theorem card_torus_domain : Nat.card (Fin 2 → (ZMod v)ˣ) = (v - 1) ^ 2 := by
  rw [Nat.card_pi, Fin.prod_univ_two, Nat.card_eq_fintype_card, ZMod.card_units, sq]

theorem exists_injective_torus (h3 : 3 ∣ v - 1) (R : Subgroup (MulAut (Multiplicative
    (Fin 2 → ZMod v)))) (hR : IsPGroup 3 R) :
    ∃ f : R →* (Fin 2 → (ZMod v)ˣ), Function.Injective f := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set T := (torus v).range with hTdef
  have hTcard : Nat.card T = (v - 1) ^ 2 := by
    rw [hTdef, MonoidHom.range_eq_map, Subgroup.card_map_of_injective torus_injective,
      Subgroup.card_top, card_torus_domain]
  have hX : Nat.card (MulAut (Multiplicative (Fin 2 → ZMod v))) =
      Nat.card (GL (Fin 2) (ZMod v)) :=
    SectionRank.Ccomm.card_mulAut_eq_card_GL (MulEquiv.refl _)
  have hT : (Nat.card (MulAut (Multiplicative (Fin 2 → ZMod v)))).factorization 3 ≤
      (Nat.card T).factorization 3 := by
    rw [hX, factorization_card_GL_two h3, hTcard, Nat.factorization_pow]
    simp
  obtain ⟨f, hf⟩ := exists_injective_of_factorization_le T hT R hR
  let e : (Fin 2 → (ZMod v)ˣ) ≃* T :=
    MulEquiv.ofBijective (torus v).rangeRestrict
      ⟨fun a b h => torus_injective (congrArg Subtype.val h), (torus v).rangeRestrict_surjective⟩
  exact ⟨e.symm.toMonoidHom.comp f, e.symm.injective.comp hf⟩

end torus

theorem card_le_sq_pi_two {C : Type*} [Group C] [Finite C] [IsCyclic C] {p : ℕ} (hp : 0 < p)
    (E : Subgroup (Fin 2 → C)) (hE : ∀ x ∈ E, x ^ p = 1) : Nat.card E ≤ p ^ 2 := by
  refine card_le_sq_of_ker_inf (Pi.evalMonoidHom (fun _ : Fin 2 => C) 0)
    (Pi.evalMonoidHom (fun _ : Fin 2 => C) 1) ?_ hp E hE
  intro x h0 h1
  funext i
  fin_cases i
  · exact h0
  · exact h1

theorem isMulCommutative_and_card_le_of_mulAut {W : Type*} [Group W] [Finite W] {v : ℕ}
    [Fact v.Prime] (hcomm : ∀ a b : W, a * b = b * a) (hpow : ∀ w : W, w ^ v = 1) {r : ℕ}
    (hr : r ≤ 2) (hcard : Nat.card W = v ^ r) (h3 : 3 ∣ v - 1) (R : Subgroup (MulAut W))
    (hR : IsPGroup 3 R) :
    (∀ a ∈ R, ∀ b ∈ R, a * b = b * a) ∧
      ∀ E : Subgroup (MulAut W), E ≤ R → (∀ x ∈ E, x ^ 3 = 1) → Nat.card E ≤ 3 ^ 2 := by
  set Z := Multiplicative (Fin (2 - r) → ZMod v)
  have hZcard : Nat.card Z = v ^ (2 - r) := by
    rw [Nat.card_congr (Multiplicative.toAdd : Z ≃ (Fin (2 - r) → ZMod v)), Nat.card_fun,
      Nat.card_zmod, Nat.card_eq_fintype_card, Fintype.card_fin]
  have hWZcomm : ∀ a b : W × Z, a * b = b * a := fun a b =>
    Prod.ext (hcomm _ _) (mul_comm (a.2 : Z) b.2)
  have hWZpow : ∀ w : W × Z, w ^ v = 1 := by
    intro w
    refine Prod.ext (by simpa using hpow w.1) ?_
    change (w.2 : Z) ^ v = 1
    have : ∀ z : Z, z ^ v = 1 := by
      intro z
      change Multiplicative.ofAdd (v • Multiplicative.toAdd z) = 1
      have : v • Multiplicative.toAdd z = 0 := by
        funext i
        simp
      rw [this, ofAdd_zero]
    exact this _
  have hWZcard : Nat.card (W × Z) = v ^ 2 := by
    rw [Nat.card_prod, hcard, hZcard, ← pow_add, Nat.add_sub_cancel' hr]
  obtain ⟨e⟩ := SectionRank.Ccomm.nonempty_mulEquiv_of_elementary hWZcomm hWZpow hWZcard
  let ι : MulAut W →* MulAut (W × Z) :=
    { toFun := fun α => MulEquiv.prodCongr α (MulEquiv.refl Z)
      map_one' := by ext <;> rfl
      map_mul' := fun _ _ => by ext <;> rfl }
  have hι : Function.Injective ι := by
    intro α β h
    ext w
    have := congrArg (fun γ : MulAut (W × Z) => (γ (w, 1)).1) h
    exact this
  let κ : MulAut W →* MulAut (Multiplicative (Fin 2 → ZMod v)) :=
    (MulAut.congr e).toMonoidHom.comp ι
  have hκ : Function.Injective κ := (MulAut.congr e).injective.comp hι
  obtain ⟨f, hf⟩ := exists_injective_torus h3 (R.map κ) (hR.map κ)
  let g : R →* (Fin 2 → (ZMod v)ˣ) := f.comp (κ.subgroupMap R)
  have hg : Function.Injective g := hf.comp (κ.subgroupMap_injective R hκ)
  refine ⟨?_, ?_⟩
  · intro a ha b hb
    have h := hg.eq_iff (a := ⟨a, ha⟩ * ⟨b, hb⟩) (b := ⟨b, hb⟩ * ⟨a, ha⟩)
    have : g (⟨a, ha⟩ * ⟨b, hb⟩) = g (⟨b, hb⟩ * ⟨a, ha⟩) := by
      rw [map_mul, map_mul, mul_comm]
    exact congrArg Subtype.val (h.mp this)
  · intro E hER hE
    have hEcard : Nat.card E = Nat.card ((E.subgroupOf R).map g) := by
      rw [Subgroup.card_map_of_injective hg,
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hER).toEquiv]
    rw [hEcard]
    refine card_le_sq_pi_two (by norm_num) _ ?_
    rintro _ ⟨x, hx, rfl⟩
    rw [← map_pow]
    have : x ^ 3 = 1 := Subtype.ext (by simpa using hE _ hx)
    rw [this, map_one]

theorem eq_one_of_coprime_six {W : Type*} [Group W] [Finite W]
    (hcomm : ∀ a b : W, a * b = b * a) (hpow : ∀ w : W, w ^ 3 = 1) (hcard : Nat.card W ≤ 3 ^ 2)
    (α : MulAut W) (hα : Nat.Coprime (orderOf α) 6) : α = 1 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hW : IsPGroup 3 W := fun w => ⟨1, by rw [pow_one]; exact hpow w⟩
  obtain ⟨r, hr⟩ := IsPGroup.iff_card.mp hW
  have hr2 : r ≤ 2 := by
    have := hr ▸ hcard
    exact (Nat.pow_le_pow_iff_right (by norm_num)).mp this
  obtain ⟨e⟩ := SectionRank.Ccomm.nonempty_mulEquiv_of_elementary hcomm hpow hr
  have hAut : Nat.card (MulAut W) ∣ 48 := by
    rw [SectionRank.Ccomm.card_mulAut_eq_card_GL e, SectionRank.Ccomm.card_GL_zmod]
    interval_cases r <;> decide
  have hdvd : orderOf α ∣ 48 := (orderOf_dvd_natCard α).trans hAut
  have hcop : Nat.Coprime (orderOf α) 48 :=
    Nat.Coprime.coprime_dvd_right (by norm_num : 48 ∣ 6 ^ 4) (Nat.Coprime.pow_right 4 hα)
  exact orderOf_eq_one_iff.mp (Nat.Coprime.eq_one_of_dvd hcop hdvd)

end CFSG.Walter.W67.P56Ab
