module

public import CFSG.Quasithin.MS93.MSPNorm

public section

namespace CFSG.Quasithin.MS93.S36SP

open CFSG.Quasithin.MS93.MSP Matrix

variable {G : Type} [Group G] {F : Type} [Field F] {U : Subgroup G}

@[expose] def ActsAdd (vec : ↥U →* Multiplicative (V4 F)) (t : G) (f : V4 F →+ V4 F) : Prop :=
  ∀ u v : ↥U, (v : G) = t * u * t⁻¹ →
    Multiplicative.toAdd (vec v) = f (Multiplicative.toAdd (vec u))

@[expose] def ActsMat (vec : ↥U →* Multiplicative (V4 F)) (t : G) (g : Sp4 F) : Prop :=
  ∀ u v : ↥U, (v : G) = t * u * t⁻¹ →
    Multiplicative.toAdd (vec v) = mat g *ᵥ Multiplicative.toAdd (vec u)

variable {vec : ↥U →* Multiplicative (V4 F)}

theorem actsMat_iff {t : G} {g : Sp4 F} :
    ActsMat vec t g ↔ ActsAdd vec t (mulVecLin (mat g)).toAddMonoidHom := Iff.rfl

theorem conj_mem {t : G} (ht : t ∈ Subgroup.normalizer (U : Set G)) (u : ↥U) :
    t * (u : G) * t⁻¹ ∈ U :=
  (Subgroup.mem_normalizer_iff.1 ht u).1 u.2

theorem actsAdd_unique (hs : Function.Surjective vec) {t : G}
    (ht : t ∈ Subgroup.normalizer (U : Set G)) {f f' : V4 F →+ V4 F}
    (hf : ActsAdd vec t f) (hf' : ActsAdd vec t f') : f = f' := by
  refine AddMonoidHom.ext fun w => ?_
  obtain ⟨u, hu⟩ := hs (Multiplicative.ofAdd w)
  have h1 := hf u ⟨_, conj_mem ht u⟩ rfl
  have h2 := hf' u ⟨_, conj_mem ht u⟩ rfl
  rw [hu] at h1 h2
  exact h1.symm.trans h2

theorem actsMat_unique (hs : Function.Surjective vec) {t : G}
    (ht : t ∈ Subgroup.normalizer (U : Set G)) {g g' : Sp4 F}
    (hg : ActsMat vec t g) (hg' : ActsMat vec t g') : g = g' := by
  have h := actsAdd_unique hs ht (actsMat_iff.1 hg) (actsMat_iff.1 hg')
  refine ext_mulVec fun w => ?_
  have := DFunLike.congr_fun h w
  simpa using this

theorem actsMat_one : ActsMat vec 1 (1 : Sp4 F) := by
  intro u v huv
  have : v = u := Subtype.ext (by simpa using huv)
  rw [this, mat_one, one_mulVec]

theorem actsMat_mul {t t' : G} (ht' : t' ∈ Subgroup.normalizer (U : Set G)) {g g' : Sp4 F}
    (hg : ActsMat vec t g) (hg' : ActsMat vec t' g') : ActsMat vec (t * t') (g * g') := by
  intro u v huv
  have hw := conj_mem ht' u
  have h1 := hg' u ⟨_, hw⟩ rfl
  have h2 := hg ⟨_, hw⟩ v (by rw [huv]; group)
  rw [h2, h1, mat_mul_mulVec]

theorem actsMat_inv {t : G} {g : Sp4 F} (hg : ActsMat vec t g) : ActsMat vec t⁻¹ g⁻¹ := by
  intro u v huv
  have h := hg v u (by rw [huv]; group)
  rw [h, mat_inv_mulVec]

theorem actsMat_pow {t : G} (ht : t ∈ Subgroup.normalizer (U : Set G)) {g : Sp4 F}
    (hg : ActsMat vec t g) (n : ℕ) : ActsMat vec (t ^ n) (g ^ n) := by
  induction n with
  | zero => simpa using (actsMat_one (vec := vec))
  | succ n ih =>
    rw [pow_succ, pow_succ]
    exact actsMat_mul ht ih hg

theorem vec_conj_eq {t : G} (ht : t ∈ Subgroup.normalizer (U : Set G)) {g : Sp4 F}
    (hg : ActsMat vec t g) (u : ↥U) :
    Multiplicative.toAdd (vec ⟨_, conj_mem ht u⟩) = mat g *ᵥ Multiplicative.toAdd (vec u) :=
  hg u _ rfl

theorem vec_commutator {t : G} (ht : t ∈ Subgroup.normalizer (U : Set G)) {g : Sp4 F}
    (hg : ActsMat vec t g) (u : ↥U) :
    Multiplicative.toAdd (vec ⟨t * u * t⁻¹ * (u : G)⁻¹, mul_mem (conj_mem ht u) (inv_mem u.2)⟩) =
      mat g *ᵥ Multiplicative.toAdd (vec u) - Multiplicative.toAdd (vec u) := by
  have e : (⟨t * u * t⁻¹ * (u : G)⁻¹, mul_mem (conj_mem ht u) (inv_mem u.2)⟩ : ↥U) =
      ⟨_, conj_mem ht u⟩ * u⁻¹ := rfl
  rw [e, map_mul, toAdd_mul, map_inv, toAdd_inv, vec_conj_eq ht hg u, sub_eq_add_neg]

theorem exists_actsAdd [Finite F] (hs : Function.Surjective vec) {C : Subgroup G}
    (hker : ∀ u : ↥U, vec u = 1 ↔ (u : G) ∈ C) {t : G}
    (ht : t ∈ Subgroup.normalizer (U : Set G)) (htC : t ∈ Subgroup.normalizer (C : Set G)) :
    ∃ f : V4 F →+ V4 F, Function.Bijective f ∧ ActsAdd vec t f := by
  let κ : ↥U →* ↥U :=
    { toFun := fun u => ⟨_, conj_mem ht u⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun u v => Subtype.ext (by simp [mul_assoc]) }
  have hκ : vec.ker ≤ (vec.comp κ).ker := by
    intro u hu
    rw [MonoidHom.mem_ker] at hu ⊢
    rw [MonoidHom.comp_apply, hker]
    exact (Subgroup.mem_normalizer_iff.1 htC u).1 ((hker u).1 hu)
  let φ : Multiplicative (V4 F) →* Multiplicative (V4 F) :=
    (QuotientGroup.lift vec.ker (vec.comp κ) hκ).comp
      (QuotientGroup.quotientKerEquivOfSurjective vec hs).symm.toMonoidHom
  have hφ : ∀ u, φ (vec u) = vec (κ u) := by
    intro u
    have e : (QuotientGroup.quotientKerEquivOfSurjective vec hs).symm (vec u) =
        QuotientGroup.mk u := by
      rw [MulEquiv.symm_apply_eq]
      rfl
    show QuotientGroup.lift vec.ker (vec.comp κ) hκ
      ((QuotientGroup.quotientKerEquivOfSurjective vec hs).symm (vec u)) = _
    rw [e, QuotientGroup.lift_mk]
    rfl
  let f : V4 F →+ V4 F := φ.toAdditive
  have hf : ∀ u, f (Multiplicative.toAdd (vec u)) = Multiplicative.toAdd (vec (κ u)) := by
    intro u
    show Multiplicative.toAdd (φ (Multiplicative.ofAdd (Multiplicative.toAdd (vec u)))) = _
    rw [ofAdd_toAdd, hφ]
  refine ⟨f, ?_, fun u v huv => ?_⟩
  ·
    have hinj : Function.Injective f := by
      rw [injective_iff_map_eq_zero]
      intro w hw
      obtain ⟨u, hu⟩ := hs (Multiplicative.ofAdd w)
      have hw' : w = Multiplicative.toAdd (vec u) := by rw [hu]; rfl
      subst hw'
      rw [hf] at hw
      have h1 : vec (κ u) = 1 := Multiplicative.toAdd.injective (by rw [hw]; rfl)
      rw [hker] at h1
      have h2 : (u : G) ∈ C := by
        have := (Subgroup.mem_normalizer_iff.1 (inv_mem htC) _).1 h1
        simpa [κ, mul_assoc] using this
      rw [← (hker u)] at h2
      rw [h2]
      rfl
    exact ⟨hinj, Finite.surjective_of_injective hinj⟩
  · have : v = κ u := Subtype.ext huv
    rw [this, hf]

theorem actsAdd_mul {t t' : G} (ht' : t' ∈ Subgroup.normalizer (U : Set G))
    {f f' : V4 F →+ V4 F} (hf : ActsAdd vec t f) (hf' : ActsAdd vec t' f') :
    ActsAdd vec (t * t') (f.comp f') := by
  intro u v huv
  have hw := conj_mem ht' u
  have h1 := hf' u ⟨_, hw⟩ rfl
  have h2 := hf ⟨_, hw⟩ v (by rw [huv]; group)
  rw [h2, h1]
  rfl

theorem actsAdd_iterate {t : G} (ht : t ∈ Subgroup.normalizer (U : Set G)) {f : V4 F →+ V4 F}
    (hf : ActsAdd vec t f) (n : ℕ) (u v : ↥U) (huv : (v : G) = t ^ n * u * (t ^ n)⁻¹) :
    Multiplicative.toAdd (vec v) = f^[n] (Multiplicative.toAdd (vec u)) := by
  induction n generalizing u v with
  | zero =>
    have : v = u := Subtype.ext (by simpa using huv)
    rw [this]
    rfl
  | succ n ih =>
    have hw := conj_mem ht u
    rw [Function.iterate_succ_apply, ← hf u ⟨_, hw⟩ rfl]
    refine ih ⟨_, hw⟩ v ?_
    rw [huv]
    simp only [pow_succ, _root_.mul_inv_rev]
    group

theorem iterate_eq_of_actsAdd (hs : Function.Surjective vec) {t : G}
    (ht : t ∈ Subgroup.normalizer (U : Set G)) {f : V4 F →+ V4 F} (hf : ActsAdd vec t f)
    {m : ℕ} (hm : t ^ 2 ^ m = 1) (v : V4 F) : f^[2 ^ m] v = v := by
  obtain ⟨u, hu⟩ := hs (Multiplicative.ofAdd v)
  have hv : v = Multiplicative.toAdd (vec u) := by rw [hu]; rfl
  subst hv
  exact (actsAdd_iterate ht hf (2 ^ m) u u (by rw [hm]; group)).symm

@[expose] noncomputable def rho (hs : Function.Surjective vec) (E : Subgroup G)
    (hEn : E ≤ Subgroup.normalizer (U : Set G)) (hE : ∀ e ∈ E, ∃ g, ActsMat vec e g) :
    ↥E →* Sp4 F where
  toFun e := Classical.choose (hE e e.2)
  map_one' := actsMat_unique hs (one_mem _) (Classical.choose_spec (hE 1 (one_mem _)))
    actsMat_one
  map_mul' e e' := actsMat_unique hs (hEn (mul_mem e.2 e'.2))
    (Classical.choose_spec (hE _ (mul_mem e.2 e'.2)))
    (actsMat_mul (hEn e'.2) (Classical.choose_spec (hE e e.2))
      (Classical.choose_spec (hE e' e'.2)))

theorem actsMat_rho (hs : Function.Surjective vec) {E : Subgroup G}
    (hEn : E ≤ Subgroup.normalizer (U : Set G)) (hE : ∀ e ∈ E, ∃ g, ActsMat vec e g)
    (e : ↥E) : ActsMat vec e (rho hs E hEn hE e) :=
  Classical.choose_spec (hE e e.2)

theorem rho_eq (hs : Function.Surjective vec) {E : Subgroup G}
    (hEn : E ≤ Subgroup.normalizer (U : Set G)) (hE : ∀ e ∈ E, ∃ g, ActsMat vec e g)
    {e : ↥E} {g : Sp4 F} (hg : ActsMat vec e g) : rho hs E hEn hE e = g :=
  actsMat_unique hs (hEn e.2) (actsMat_rho hs hEn hE e) hg

theorem normalizes_of_actsAdd (hs : Function.Surjective vec) {t : G}
    (ht : t ∈ Subgroup.normalizer (U : Set G)) {f : V4 F →+ V4 F} (hf : ActsAdd vec t f)
    (hgen : ∀ g : Sp4 F, ∃ x ∈ Subgroup.normalizer (U : Set G), ActsMat vec x g ∧
      ∃ g', ActsMat vec (t * x * t⁻¹) g') : Normalizes f := by
  intro g
  obtain ⟨x, hx, hxg, g', hg'⟩ := hgen g
  refine ⟨g', fun v => ?_⟩
  obtain ⟨u, hu⟩ := hs (Multiplicative.ofAdd v)
  have hv : v = Multiplicative.toAdd (vec u) := by rw [hu]; rfl
  subst hv
  have hxu := conj_mem hx u
  have htxu := conj_mem ht ⟨_, hxu⟩
  have htu := conj_mem ht u
  rw [← hxg u ⟨_, hxu⟩ rfl, ← hf ⟨_, hxu⟩ ⟨_, htxu⟩ rfl, ← hf u ⟨_, htu⟩ rfl,
    hg' ⟨_, htu⟩ ⟨_, htxu⟩ (by simp only; group)]

variable [Finite F] [CharP F 2]

theorem exists_actsMat_of_linear (hs : Function.Surjective vec) {t : G}
    (ht : t ∈ Subgroup.normalizer (U : Set G)) {f : V4 F →+ V4 F} (hf : ActsAdd vec t f)
    (hfb : Function.Bijective f) (hfn : Normalizes f)
    (hlin : ∀ (c : F) (v : V4 F), f (c • v) = c • f v)
    {m : ℕ} (hm : t ^ 2 ^ m = 1) : ∃ g : Sp4 F, ActsMat vec t g := by
  obtain ⟨g, hg⟩ := exists_eq_mat_of_two_power hfb hfn hlin (iterate_eq_of_actsAdd hs ht hf hm)
  exact ⟨g, fun u v huv => by rw [hf u v huv, hg]⟩

omit [CharP F 2] in
theorem linear_of_card {f : V4 F →+ V4 F} (hfb : Function.Bijective f) (hfn : Normalizes f)
    (hcard : Nat.card (V4 F) < Nat.card (CFSG.Quasithin.Vol2.KGNat.fixAdd f) ^ 2) :
    ∀ (c : F) (v : V4 F), f (c • v) = c • f v := by
  obtain ⟨σ, hσ⟩ := exists_semilinear hfb hfn
  by_cases hne : ∃ c : F, σ c ≠ c
  · exact absurd (card_fixAdd_sq_le hσ hne) (not_le.2 hcard)
  · push Not at hne
    intro c v
    rw [hσ, hne]

omit [CharP F 2] in
theorem linear_of_commute_transv {f : V4 F →+ V4 F} (hfb : Function.Bijective f)
    (hfn : Normalizes f) {a : V4 F} (ha : a ≠ 0)
    (hcomm : ∀ (c : F) (v : V4 F), f (mat (transv a c) *ᵥ v) = mat (transv a c) *ᵥ f v) :
    ∀ (c : F) (v : V4 F), f (c • v) = c • f v := by
  obtain ⟨σ, hσ⟩ := exists_semilinear hfb hfn
  obtain ⟨w, hw⟩ := exists_form_eq_one ha
  have key : ∀ c : F, σ c • f a = (c * form F a (f w)) • a := by
    intro c
    have h := hcomm c w
    rw [transv_mulVec, transv_mulVec, hw, mul_one, map_add, hσ] at h
    exact add_left_cancel h
  have hfa : f a = form F a (f w) • a := by simpa using key 1
  have hν : form F a (f w) ≠ 0 := by
    intro h0
    rw [h0, zero_smul] at hfa
    exact ha (hfb.1 (hfa.trans (map_zero f).symm))
  have hσc : ∀ c : F, σ c = c := by
    intro c
    have h := key c
    rw [hfa, smul_smul] at h
    have h' := smul_left_injective F ha h
    exact mul_right_cancel₀ hν (by simpa [mul_comm] using h')
  intro c v
  rw [hσ, hσc]

omit [CharP F 2] in
theorem linear_of_fix_mod {f : V4 F →+ V4 F} (hfb : Function.Bijective f) (hfn : Normalizes f)
    {p : Submodule F (V4 F)} {w : V4 F} (hw : w ∉ p) (hfw : ∀ c : F, f (c • w) - c • w ∈ p) :
    ∀ (c : F) (v : V4 F), f (c • v) = c • f v := by
  obtain ⟨σ, hσ⟩ := exists_semilinear hfb hfn
  have hσc : ∀ c : F, σ c = c := by
    intro c
    have h1 := hfw c
    have h2 := p.smul_mem (σ c) (by simpa using hfw 1)
    have h3 := p.sub_mem h2 h1
    rw [hσ, smul_sub] at h3
    have h4 : (c - σ c) • w ∈ p := by
      convert h3 using 1
      rw [sub_smul]
      abel
    by_contra hne
    exact hw ((Submodule.smul_mem_iff p (sub_ne_zero.2 (Ne.symm hne))).1 h4)
  intro c v
  rw [hσ, hσc]

end CFSG.Quasithin.MS93.S36SP
