module

public import CFSG.LocalAnalysis.StandardType.GGKGReflection

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Open

@[expose] def GGKGLatticeAt (p : ℕ) {R : Type} [Group R] (E : Subgroup R) : Prop :=
  ∃ (m : ℕ) (Q : Matrix (Fin m) (Fin m) ℤ) (π : (Fin m → ℤ) →+ Additive ↥E),
    GGLatForm Q ∧ Function.Surjective π ∧
      ∀ w₀ : R, GGKGIsReflAt p E w₀ → ∃ w : Fin m → ℤ, GGLatRoot Q w ∧
        ∀ y : Fin m → ℤ, w₀ * ((Additive.toMul (π y) : ↥E) : R) * w₀⁻¹ =
          ((Additive.toMul (π (ggLatRefl Q w y)) : ↥E) : R)

@[expose] def GGKGLatticeElt (p r : ℕ) (R : Type) [Group R] : Prop :=
  ∀ E : Subgroup R, IsElemAbelian p E → p ^ 3 ≤ Nat.card E → p ^ r ≤ Nat.card E →
    (∀ g : R, (∀ e ∈ E, g * e = e * g) → g ^ p = 1 → g ∈ E) → GGKGLatticeAt p E

private theorem ggKGLe_lift_conj_mul_inv {L' R : Type} [Group L'] [Group R] {ψ : L' →* R}
    (Λ : R →* MulAut L') {n : L'} {w : R} (hΛn : Λ (ψ n) = MulAut.conj n) (hw : ψ n = w)
    (e : R) : Λ (w * e * w⁻¹) = MulAut.conj n * Λ e * (MulAut.conj n)⁻¹ := by
  have h : Λ w = MulAut.conj n := by rw [← hw, hΛn]
  rw [← h, ← map_mul, ← map_inv, ← map_mul]

private theorem ggKGLe_map_centralizer {R R' : Type} [Group R] [Group R'] (e : R ≃* R')
    (S : Set R) :
    (Subgroup.centralizer S).map e.toMonoidHom = Subgroup.centralizer (e '' S) := by
  ext y
  rw [Subgroup.mem_map_equiv, Subgroup.mem_centralizer_iff, Subgroup.mem_centralizer_iff]
  constructor
  · rintro h z ⟨x, hx, rfl⟩
    have h' := h x hx
    calc e x * y = e (x * e.symm y) := by rw [map_mul, MulEquiv.apply_symm_apply]
      _ = e (e.symm y * x) := by rw [h']
      _ = y * e x := by rw [map_mul, MulEquiv.apply_symm_apply]
  · intro h x hx
    have h' := h (e x) ⟨x, hx, rfl⟩
    calc x * e.symm y = e.symm (e x * y) := by rw [map_mul, MulEquiv.symm_apply_apply]
      _ = e.symm (y * e x) := by rw [h']
      _ = e.symm y * x := by rw [map_mul, MulEquiv.symm_apply_apply]

private theorem ggKGLe_injective_toMonoidHom {R R' : Type} [Group R] [Group R'] (e : R ≃* R') :
    Function.Injective e.toMonoidHom := by
  intro a b h
  exact e.injective (by simpa using h)

private theorem ggKGLe_symm_coe_of {R R' : Type} [Group R] [Group R'] (e : R ≃* R')
    {E : Subgroup R} {E' : Subgroup R'} (eE : ↥E ≃* ↥E')
    (heE : ∀ x : ↥E, (eE x : R') = e (x : R)) (z : ↥E') :
    ((eE.symm z : ↥E) : R) = e.symm (z : R') := by
  apply e.injective
  rw [← heE (eE.symm z), MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply]

theorem ggTorusLattice_of_latticeElt {p r : ℕ} {R : Type} [Group R] {I : Set (MulAut R)}
    (hp : p.Prime) (hIp : ∀ φ ∈ I, φ ^ p = 1 → φ ∈ Set.range (MulAut.conj : R →* MulAut R))
    (hZ : Subgroup.center R = ⊥) (hcp : GGCenterPrime p R) (h : GGKGLatticeElt p r R) :
    GGTorusLattice p r R I := by
  classical
  intro L' _ _ ψ A hTB
  obtain ⟨hψ, hker, hperf, hA, hAI, hr, h3, hsc⟩ := hTB
  have hcpL := hcp L' ψ hψ hker hperf
  obtain ⟨Λ, hΛeq, hΛinj, hΛmap⟩ : ∃ Λ : R →* MulAut L',
      (∀ {e : R} {x : L'}, ψ x = e → Λ e = MulAut.conj x) ∧ Function.Injective Λ ∧
      (∀ e l, ψ (Λ e l) = e * ψ l * e⁻¹) :=
    ⟨ReflInner.liftConj ψ hψ hker, fun hx => ReflInner.liftConj_eq hψ hker hx,
      ReflInner.liftConj_injective hψ hker hZ, ReflInner.map_liftConj_apply hψ hker⟩
  have hΛn : ∀ n : L', Λ (ψ n) = MulAut.conj n := fun n => hΛeq rfl
  have hAΛ : ∀ a ∈ A, ∃ e, Λ e = a := by
    intro a ha
    obtain ⟨φ', hφ'I, hφ'⟩ := hAI a ha
    have hk : ∀ k : ℕ, ∀ l, (φ' ^ k) (ψ l) = ψ ((a ^ k) l) := by
      intro k
      induction k with
      | zero => intro l; simp
      | succ k ih =>
        intro l
        rw [pow_succ, pow_succ, MulAut.mul_apply, MulAut.mul_apply, hφ', ih]
    have hφp : φ' ^ p = 1 := by
      refine MulEquiv.ext fun r => ?_
      obtain ⟨l, rfl⟩ := hψ r
      rw [hk, hA.2 a ha]
      rfl
    obtain ⟨e, rfl⟩ := hIp φ' hφ'I hφp
    refine ⟨e, TypeA.mulAut_eq_of_forall ψ hker hperf fun l => ?_⟩
    rw [hΛmap, ← hφ' l, MulAut.conj_apply]
  set E : Subgroup R := A.comap Λ with hE
  have hΦmem : ∀ e : E, Λ (e : R) ∈ A := fun e => Subgroup.mem_comap.mp (hE ▸ e.2)
  let Φfun : E →* A :=
    { toFun := fun e => ⟨Λ (e : R), hΦmem e⟩
      map_one' := Subtype.ext (map_one Λ)
      map_mul' := fun a b => Subtype.ext (map_mul Λ (a : R) (b : R)) }
  have hΦfun_val : ∀ e : E, (Φfun e : MulAut L') = Λ (e : R) := fun e => rfl
  have hΦbij : Function.Bijective Φfun := by
    refine ⟨fun e₁ e₂ h12 => Subtype.ext (hΛinj (congrArg Subtype.val h12)), fun a => ?_⟩
    obtain ⟨e, he⟩ := hAΛ a a.2
    exact ⟨⟨e, show Λ e ∈ A from he ▸ a.2⟩, Subtype.ext he⟩
  let eE : ↥E ≃* ↥A := MulEquiv.ofBijective Φfun hΦbij
  have hcardE : Nat.card E = Nat.card A := Nat.card_congr eE.toEquiv
  have hEab : IsElemAbelian p E := by
    refine ⟨⟨⟨fun e₁ e₂ => Subtype.ext (hΛinj ?_)⟩⟩, fun e he => hΛinj ?_⟩
    · rw [Subgroup.coe_mul, Subgroup.coe_mul, map_mul, map_mul]
      exact TableB.IsElemAbelian.comm hA e₁.2 e₂.2
    · rw [map_pow, map_one]
      exact hA.2 _ he
  have hscE : ∀ g : R, (∀ e ∈ E, g * e = e * g) → g ^ p = 1 → g ∈ E := by
    intro g hg hgp
    obtain ⟨n, hn, hnp⟩ := exists_lift_pow_eq_one hp hψ hker hcpL hgp
    have hfix : ∀ a ∈ A, a n = n := by
      intro a ha
      obtain ⟨e, rfl⟩ := hAΛ a ha
      have heE : e ∈ E := show Λ e ∈ A from ha
      refine eq_of_lift_pow_eq_one hp hker hcpL ?_ ?_ hnp
      · rw [hΛmap, hn, ← hg e heE, mul_inv_cancel_right]
      · rw [← map_pow, hnp, map_one]
    have h1 := hsc n hfix hnp
    rw [← hΛn n, hn] at h1
    exact h1
  have h3' : p ^ 3 ≤ Nat.card E := hcardE ▸ h3
  have hr' : p ^ r ≤ Nat.card E := hcardE ▸ hr
  obtain ⟨m, Q, πE, hQform, hπEsurj, hπEprop⟩ := h E hEab h3' hr' hscE
  let πA : (Fin m → ℤ) →+ Additive ↥A := eE.toMonoidHom.toAdditive.comp πE
  refine ⟨m, Q, πA, hQform, ?_, ?_⟩
  · have hsurj : Function.Surjective (eE.toMonoidHom.toAdditive) := eE.surjective
    exact hsurj.comp hπEsurj
  · intro φ hφauto hφrefl
    obtain ⟨c, ⟨n, rfl⟩, hcN, hvc⟩ := mem_ggAutomizer_iff.mp hφauto
    have hvφ : φ = ggConjAut A hcN := MulEquiv.ext fun b => Subtype.ext (hvc b)
    set w₀ : R := ψ n with hw₀
    have hΛw0 : Λ w₀ = MulAut.conj n := by rw [hw₀, hΛn n]
    have hconj : ∀ e : R, Λ (w₀ * e * w₀⁻¹) = MulAut.conj n * Λ e * (MulAut.conj n)⁻¹ :=
      fun e => ggKGLe_lift_conj_mul_inv Λ (hΛn n) hw₀.symm e
    have hnorm : w₀ ∈ Subgroup.normalizer (E : Set R) := by
      rw [Subgroup.mem_normalizer_iff]
      intro e
      constructor
      · intro he
        have h2 : MulAut.conj n * Λ e * (MulAut.conj n)⁻¹ ∈ A :=
          (Subgroup.mem_normalizer_iff.mp hcN (Λ e)).mp (show Λ e ∈ A from he)
        rwa [← hconj e] at h2
      · intro he
        have h2 : MulAut.conj n * Λ e * (MulAut.conj n)⁻¹ ∈ A := by
          rw [← hconj e]
          exact he
        exact (Subgroup.mem_normalizer_iff.mp hcN (Λ e)).mpr h2
    have hinv : ∀ e ∈ E, w₀ * (w₀ * e * w₀⁻¹) * w₀⁻¹ = e := by
      intro e he
      refine hΛinj ?_
      have hconj2 : ggConjAut A hcN ^ 2 = 1 := by rw [← hvφ, hφrefl.1]
      have hpow : (MulAut.conj n) ^ 2 * Λ e * ((MulAut.conj n) ^ 2)⁻¹ = Λ e := by
        have h1 : (((ggConjAut A hcN ^ 2) ⟨Λ e, show Λ e ∈ A from he⟩ : ↥A) : MulAut L') = Λ e := by
          rw [hconj2]
          rfl
        rwa [ggConjAut_pow_apply A hcN 2 ⟨Λ e, show Λ e ∈ A from he⟩] at h1
      calc Λ (w₀ * (w₀ * e * w₀⁻¹) * w₀⁻¹)
          = MulAut.conj n * (MulAut.conj n * Λ e * (MulAut.conj n)⁻¹) *
              (MulAut.conj n)⁻¹ := by
            rw [map_mul, map_mul, hconj e, map_inv, hΛw0]
        _ = (MulAut.conj n) ^ 2 * Λ e * ((MulAut.conj n) ^ 2)⁻¹ := by
            rw [pow_two]
            group
        _ = Λ e := hpow
    have hfixcard : Nat.card {e : E // w₀ * (e : R) * w₀⁻¹ = e} * p = Nat.card E := by
      rw [show Nat.card {e : E // w₀ * (e : R) * w₀⁻¹ = e} =
          Nat.card {b : A // φ b = b} from
        Nat.card_congr (Equiv.subtypeEquiv (Equiv.ofBijective Φfun hΦbij) (fun e => ?_))]
      · rw [hφrefl.2, hcardE]
      · constructor
        · intro he
          apply Subtype.ext
          rw [Equiv.coe_ofBijective, hvc, hΦfun_val e, ← hconj (e : R), he]
        · intro hb
          have h1 : MulAut.conj n * Λ (e : R) * (MulAut.conj n)⁻¹ = Λ (e : R) := by
            have h2 := congrArg (fun b : ↥A => ((b : ↥A) : MulAut L')) hb
            rw [Equiv.coe_ofBijective] at h2
            rw [hvc, hΦfun_val e] at h2
            exact h2
          rw [← hconj (e : R)] at h1
          exact hΛinj h1
    have hrefl : GGKGIsReflAt p E w₀ := ⟨hnorm, hinv, hfixcard⟩
    obtain ⟨w, hwroot, hwformula⟩ := hπEprop w₀ hrefl
    refine ⟨w, hwroot, fun y => ?_⟩
    have hπA : ∀ y, ((Additive.toMul (πA y) : ↥A) : MulAut L') =
        Λ ((Additive.toMul (πE y) : ↥E) : R) := fun y => rfl
    apply Subtype.ext
    rw [hvφ, ggConjAut_apply, hπA y, hπA (ggLatRefl Q w y)]
    rw [← hconj ((Additive.toMul (πE y) : ↥E) : R)]
    congr 1
    exact hwformula y

theorem ggKGLatticeElt_of_mulEquiv {p r : ℕ} {R R' : Type} [Group R] [Group R'] (e : R ≃* R')
    (h : GGKGLatticeElt p r R') : GGKGLatticeElt p r R := by
  intro E hEab h3 hr hsc
  let E' : Subgroup R' := E.map e.toMonoidHom
  have hEab' : IsElemAbelian p E' := IsElemAbelian.map hEab e.toMonoidHom
  have hcardE' : Nat.card E' = Nat.card E :=
    Subgroup.card_map_of_injective (ggKGLe_injective_toMonoidHom e)
  have h3' : p ^ 3 ≤ Nat.card E' := by rw [hcardE']; exact h3
  have hr' : p ^ r ≤ Nat.card E' := by rw [hcardE']; exact hr
  have hsc' : ∀ g : R', (∀ e' ∈ E', g * e' = e' * g) → g ^ p = 1 → g ∈ E' := by
    intro g hg hgp
    have hcomm : ∀ x ∈ E, e.symm g * x = x * e.symm g := by
      intro x hx
      have h1 : e x ∈ E' := Subgroup.mem_map_of_mem e.toMonoidHom hx
      have h2 : g * e x = e x * g := hg (e x) h1
      apply e.injective
      rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
      exact h2
    have hge : e.symm g ∈ E := hsc (e.symm g) hcomm (by
      apply e.injective
      rw [map_pow, MulEquiv.apply_symm_apply, hgp, map_one])
    rw [← MulEquiv.apply_symm_apply e g]
    exact Subgroup.mem_map_of_mem e.toMonoidHom hge
  obtain ⟨m, Q, π', hQform, hπ'surj, hπ'prop⟩ := h E' hEab' h3' hr' hsc'
  let eE : ↥E ≃* ↥E' := E.equivMapOfInjective e.toMonoidHom (ggKGLe_injective_toMonoidHom e)
  have heE : ∀ x : ↥E, (eE x : R') = e (x : R) := fun x =>
    Subgroup.coe_equivMapOfInjective_apply E e.toMonoidHom (ggKGLe_injective_toMonoidHom e) x
  let π : (Fin m → ℤ) →+ Additive ↥E := eE.symm.toMonoidHom.toAdditive.comp π'
  refine ⟨m, Q, π, hQform, ?_, ?_⟩
  · have hsurj : Function.Surjective (eE.symm.toMonoidHom.toAdditive) := eE.symm.surjective
    exact hsurj.comp hπ'surj
  · intro w₀ hw₀
    have hw₀' : GGKGIsReflAt p E' (e w₀) :=
      hw₀.map e.toMonoidHom (ggKGLe_injective_toMonoidHom e)
    obtain ⟨w, hwroot, hwformula⟩ := hπ'prop (e w₀) hw₀'
    refine ⟨w, hwroot, fun y => ?_⟩
    have hπcoe : ∀ y, ((Additive.toMul (π y) : ↥E) : R) =
        e.symm ((Additive.toMul (π' y) : ↥E') : R') := fun y =>
      ggKGLe_symm_coe_of e eE heE (Additive.toMul (π' y))
    apply e.injective
    rw [map_mul, map_mul, map_inv, hπcoe y, hπcoe (ggLatRefl Q w y),
      MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply]
    exact hwformula y

theorem ggKGRootDatumAt_of_mulEquiv {p : ℕ} {R R' : Type} [Group R] [Group R'] (e : R ≃* R')
    {E : Subgroup R} (hE' : GGKGRootDatumAt p (E.map e.toMonoidHom)) : GGKGRootDatumAt p E := by
  let E' : Subgroup R' := E.map e.toMonoidHom
  intro w₀ hw₀
  have hw₀' : GGKGIsReflAt p E' (e w₀) :=
    hw₀.map e.toMonoidHom (ggKGLe_injective_toMonoidHom e)
  obtain ⟨w', hw'formula, J', hw'J', hJ'comp, hpJ', hlay'⟩ := hE' (e w₀) hw₀'
  let w : R := e.symm w'
  have hew : e w = w' := e.apply_symm_apply w'
  let J : Subgroup R := J'.comap e.toMonoidHom
  have hCmap : (Subgroup.centralizer
        ((E ⊓ Subgroup.centralizer ({w} : Set R) : Subgroup R) : Set R)).map e.toMonoidHom =
      Subgroup.centralizer
        ((E' ⊓ Subgroup.centralizer ({w'} : Set R') : Subgroup R') : Set R') := by
    rw [ggKGLe_map_centralizer]
    congr 1
    change ⇑e.toMonoidHom '' ↑(E ⊓ Subgroup.centralizer ({w} : Set R)) =
      ↑(Subgroup.map e.toMonoidHom E ⊓ Subgroup.centralizer ({w'} : Set R'))
    rw [← Subgroup.coe_map e.toMonoidHom (E ⊓ Subgroup.centralizer ({w} : Set R)),
      Subgroup.map_inf _ _ _ (ggKGLe_injective_toMonoidHom e)]
    rw [ggKGLe_map_centralizer e ({w} : Set R), Set.image_singleton, hew]
  have hcomp' : Assembly.IsComponentOf J'
      (Subgroup.map e.toMonoidHom (Subgroup.centralizer
        ((E ⊓ Subgroup.centralizer ({w} : Set R) : Subgroup R) : Set R))) := by
    rw [hCmap]
    exact hJ'comp
  have hJcomp : Assembly.IsComponentOf (J'.comap e.toMonoidHom)
      (Subgroup.centralizer ((E ⊓ Subgroup.centralizer ({w} : Set R) : Subgroup R) : Set R)) :=
    (isComponentOf_comap_of_injective e.toMonoidHom (ggKGLe_injective_toMonoidHom e) hcomp').1
  have hJmap : (J'.comap e.toMonoidHom).map e.toMonoidHom = J' :=
    (isComponentOf_comap_of_injective e.toMonoidHom (ggKGLe_injective_toMonoidHom e) hcomp').2
  refine ⟨w, ?_, J'.comap e.toMonoidHom, ?_, hJcomp, ?_, ?_⟩
  · intro a ha
    have ha' : e a ∈ E' := Subgroup.mem_map_of_mem e.toMonoidHom ha
    have h' : w' * e a * w'⁻¹ = e w₀ * e a * (e w₀)⁻¹ := hw'formula (e a) ha'
    apply e.injective
    simp only [map_mul, map_inv]
    rw [hew]
    exact h'
  · rw [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, hew]
    exact hw'J'
  · rw [← Subgroup.card_map_of_injective (ggKGLe_injective_toMonoidHom e)
      (K := J'.comap e.toMonoidHom), hJmap]
    exact hpJ'
  · intro a ha haw
    have ha' : e a ∈ E' := Subgroup.mem_map_of_mem e.toMonoidHom ha
    have haw' : w' * e a = e a * w' := by
      have h' := congrArg e haw
      simpa only [map_mul, hew] using h'
    have hle' : J' ≤ LargeEvenLayer (Subgroup.centralizer ({e a} : Set R')) :=
      hlay' (e a) ha' haw'
    have hBig : LargeEvenLayer (Subgroup.centralizer ({e a} : Set R')) =
        (LargeEvenLayer (Subgroup.centralizer ({a} : Set R))).map e.toMonoidHom := by
      have h1 : Subgroup.centralizer ({e a} : Set R') =
          (Subgroup.centralizer ({a} : Set R)).map e.toMonoidHom := by
        rw [ggKGLe_map_centralizer, Set.image_singleton]
      rw [h1, largeEvenLayer_map_of_injective e.toMonoidHom (ggKGLe_injective_toMonoidHom e)]
    have hle : J' ≤ (LargeEvenLayer (Subgroup.centralizer ({a} : Set R))).map e.toMonoidHom := by
      rw [← hBig]
      exact hle'
    rw [← Subgroup.comap_map_eq_self_of_injective (ggKGLe_injective_toMonoidHom e)
      (LargeEvenLayer (Subgroup.centralizer ({a} : Set R)))]
    exact (Subgroup.map_le_iff_le_comap).mp (by rw [hJmap]; exact hle)

theorem ggKGRootDatum_of_mulEquiv {p r : ℕ} {R R' : Type} [Group R] [Group R'] (e : R ≃* R')
    (h : GGKGRootDatum p r R') : GGKGRootDatum p r R := by
  intro E hEab h3 hr hsc
  let E' : Subgroup R' := E.map e.toMonoidHom
  have hEab' : IsElemAbelian p E' := IsElemAbelian.map hEab e.toMonoidHom
  have hcardE' : Nat.card E' = Nat.card E :=
    Subgroup.card_map_of_injective (ggKGLe_injective_toMonoidHom e)
  have h3' : p ^ 3 ≤ Nat.card E' := by rw [hcardE']; exact h3
  have hr' : p ^ r ≤ Nat.card E' := by rw [hcardE']; exact hr
  have hsc' : ∀ g : R', (∀ e' ∈ E', g * e' = e' * g) → g ^ p = 1 → g ∈ E' := by
    intro g hg hgp
    have hcomm : ∀ x ∈ E, e.symm g * x = x * e.symm g := by
      intro x hx
      have h1 : e x ∈ E' := Subgroup.mem_map_of_mem e.toMonoidHom hx
      have h2 : g * e x = e x * g := hg (e x) h1
      apply e.injective
      rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
      exact h2
    have hge : e.symm g ∈ E := hsc (e.symm g) hcomm (by
      apply e.injective
      rw [map_pow, MulEquiv.apply_symm_apply, hgp, map_one])
    rw [← MulEquiv.apply_symm_apply e g]
    exact Subgroup.mem_map_of_mem e.toMonoidHom hge
  exact ggKGRootDatumAt_of_mulEquiv e (h E' hEab' h3' hr' hsc')

end CFSG.StandardType

end
