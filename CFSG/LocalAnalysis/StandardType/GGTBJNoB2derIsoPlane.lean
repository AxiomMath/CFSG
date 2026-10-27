module

public import CFSG.LocalAnalysis.StandardType.GGTBJNoB2derFixOrth

public section

namespace CFSG.StandardType

open Module CFSG.Open


private theorem l48dB_restrict_apply {K : Type*} [Field K] [CharP K 2] [Finite K] {V : Type*}
    [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (B : LinearMap.BilinForm K V) (W : Submodule K V) (x y : W) :
    (B.restrict W) x y = B (x : V) (y : V) := by
  rw [LinearMap.BilinForm.restrict_apply]
  rfl

private theorem l48dB_apply_ne_zero {K : Type*} [Field K] [CharP K 2] [Finite K] {V : Type*}
    [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    {f : (Module.End K V)ˣ} {v : V} (hv : v ≠ 0) :
    (f : Module.End K V) v ≠ 0 := by
  intro h
  apply hv
  have h2 : ((f⁻¹ : (Module.End K V)ˣ) : Module.End K V) ((f : Module.End K V) v) =
      ((f⁻¹ : (Module.End K V)ˣ) : Module.End K V) 0 := by rw [h]
  rwa [map_zero, ← Module.End.mul_apply, ← Units.val_mul, inv_mul_cancel, Units.val_one,
    Module.End.one_apply] at h2

private theorem l48dB_zpowers_fix {K : Type*} [Field K] [CharP K 2] [Finite K] {V : Type*}
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] {G : Type*} [Group G]
    {ρ : G →* (Module.End K V)ˣ} {z : G} {v : V}
    (hv : (ρ z : Module.End K V) v = v) {w : G} (hw : w ∈ Subgroup.zpowers z) :
    (ρ w : Module.End K V) v = v := by
  let H : Subgroup G :=
    { carrier := {w | (ρ w : Module.End K V) v = v}
      one_mem' := by simp
      mul_mem' := by
        intro a b ha hb
        change (ρ (a * b) : Module.End K V) v = v
        have ha' : (ρ a : Module.End K V) v = v := ha
        have hb' : (ρ b : Module.End K V) v = v := hb
        rw [map_mul, Units.val_mul, Module.End.mul_apply, hb', ha']
      inv_mem' := by
        intro a ha
        change (ρ a⁻¹ : Module.End K V) v = v
        have ha' : (ρ a : Module.End K V) v = v := ha
        have h4 : (ρ a⁻¹ : Module.End K V) ((ρ a : Module.End K V) v) = v := by
          rw [← Module.End.mul_apply, ← Units.val_mul, ← map_mul]
          simp
        rw [ha'] at h4
        exact h4 }
  exact (Subgroup.zpowers_le.mpr (show z ∈ H from hv)) hw

private theorem l48dB_inv_line_fix {K : Type*} [Field K] [CharP K 2] [Finite K] {V : Type*}
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] {G : Type*} [Group G]
    (hK : Nat.card K = 2) (ρ : G →* (Module.End K V)ˣ)
    {E : Subgroup G} {W : Submodule K V} (hfin : Module.finrank K W = 1)
    (hact : ∀ a ∈ E, ∀ v ∈ W, (ρ a : Module.End K V) v ∈ W) :
    W ≤ SmallRule.fixSpaceOf ρ E := by
  classical
  haveI : Finite V := Module.finite_of_finite K
  haveI : Finite W := Finite.of_injective (fun w : W => (w : V)) (fun _ _ h => Subtype.ext h)
  haveI : Fintype W := Fintype.ofFinite W
  have hcardW : Fintype.card W = 2 := by
    rw [← Nat.card_eq_fintype_card, Module.natCard_eq_pow_finrank (K := K), hK, hfin]
    norm_num
  intro v hvW
  rw [SmallRule.mem_fixSpaceOf]
  intro a ha
  by_cases hv0 : v = 0
  · rw [hv0]; simp
  · by_contra hne
    have hρvW : (ρ a : Module.End K V) v ∈ W := hact a ha v hvW
    have hρv0 : (ρ a : Module.End K V) v ≠ 0 := l48dB_apply_ne_zero (f := ρ a) hv0
    let w : W := ⟨v, hvW⟩
    let z' : W := ⟨(ρ a : Module.End K V) v, hρvW⟩
    have hw0 : (0 : W) ≠ w := by
      intro h; exact hv0 (congrArg Subtype.val h.symm)
    have hz'0 : (0 : W) ≠ z' := by
      intro h; exact hρv0 (congrArg Subtype.val h.symm)
    have hwz : w ≠ z' := by
      intro h; exact hne (congrArg Subtype.val h).symm
    have h3 : ({0, w, z'} : Finset W).card = 3 := by
      rw [Finset.card_triple_eq_three_iff]
      exact ⟨hw0, hz'0, hwz⟩
    have hle : ({0, w, z'} : Finset W).card ≤ (Finset.univ : Finset W).card :=
      Finset.card_le_card (Finset.subset_univ _)
    rw [Finset.card_univ, hcardW, h3] at hle
    omega

private theorem l48dB_no_inv_isotropic {K : Type*} [Field K] [CharP K 2] [Finite K] {V : Type*}
    [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (hK : Nat.card K = 2) (B : LinearMap.BilinForm K V) (hB : B.Nondegenerate) (hr : B.IsRefl)
    (X : Subgroup (Module.End K V)ˣ)
    (hcomm : ∀ x ∈ X, ∀ y ∈ X, x * y = y * x) (hexp : ∀ x ∈ X, x ^ 3 = 1)
    (hisoX : ∀ x ∈ X, ∀ v w, B ((x : Module.End K V) v) ((x : Module.End K V) w) = B v w)
    (hcard : 9 ≤ Nat.card X) (hdim : Module.finrank K V = 4)
    {T : Submodule K V} (hT0 : T ≠ ⊥) (hTiso : ∀ u ∈ T, ∀ v ∈ T, B u v = 0)
    (hTX : ∀ x ∈ X, ∀ t ∈ T, (x : Module.End K V) t ∈ T) : False := by
  have h := SmallRule.card_sq_le_of_isotropic hK B hB hr X hcomm hexp hisoX hT0 hTiso hTX
  have h1 : 1 ≤ Module.finrank K T := Submodule.one_le_finrank_iff.mpr hT0
  have h9 : 9 ^ 2 ≤ Nat.card X ^ 2 := Nat.pow_le_pow_left hcard 2
  have h27 : 3 ^ (4 - Module.finrank K T) ≤ 3 ^ 3 :=
    Nat.pow_le_pow_right (by norm_num) (by omega)
  rw [hdim] at h
  have h81 : 81 ≤ 27 := by
    calc (81 : ℕ) = 9 ^ 2 := by norm_num
      _ ≤ Nat.card X ^ 2 := h9
      _ ≤ 3 ^ (4 - Module.finrank K T) := h
      _ ≤ 3 ^ 3 := h27
      _ = 27 := by norm_num
  omega

private noncomputable def l48dB_resUnit {K : Type*} [Field K] [CharP K 2] [Finite K] {V : Type*}
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] {G : Type*} [Group G]
    (ρ : G →* (Module.End K V)ˣ) {E : Subgroup G}
    {W0 : Submodule K V}
    (hinv : ∀ a ∈ E, ∀ v ∈ W0, (ρ a : Module.End K V) v ∈ W0) (a : E) :
    (Module.End K W0)ˣ :=
  Units.mk
    ((ρ (a : G) : Module.End K V).restrict (fun x hx => hinv (a : G) a.2 x hx))
    ((ρ ((a : G)⁻¹) : Module.End K V).restrict
      (fun x hx => hinv ((a : G)⁻¹) (E.inv_mem a.2) x hx))
    (by
      apply LinearMap.ext
      intro x
      apply Subtype.ext
      simp only [Module.End.mul_apply, LinearMap.restrict_apply, Module.End.one_apply]
      rw [← Module.End.mul_apply, ← Units.val_mul, map_inv, mul_inv_cancel, Units.val_one,
        Module.End.one_apply])
    (by
      apply LinearMap.ext
      intro x
      apply Subtype.ext
      simp only [Module.End.mul_apply, LinearMap.restrict_apply, Module.End.one_apply]
      rw [← Module.End.mul_apply, ← Units.val_mul, map_inv, inv_mul_cancel, Units.val_one,
        Module.End.one_apply])

private theorem l48dB_resUnit_val {K : Type*} [Field K] [CharP K 2] [Finite K] {V : Type*}
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] {G : Type*} [Group G]
    (ρ : G →* (Module.End K V)ˣ) {E : Subgroup G}
    {W0 : Submodule K V}
    (hinv : ∀ a ∈ E, ∀ v ∈ W0, (ρ a : Module.End K V) v ∈ W0) (a : E) (v : W0) :
    ((l48dB_resUnit ρ hinv a : Module.End K W0) v : V) = (ρ (a : G) : Module.End K V) v := by
  simp [l48dB_resUnit, LinearMap.restrict_apply]

private noncomputable def l48dB_resHom {K : Type*} [Field K] [CharP K 2] [Finite K] {V : Type*}
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] {G : Type*} [Group G]
    (ρ : G →* (Module.End K V)ˣ) {E : Subgroup G}
    {W0 : Submodule K V}
    (hinv : ∀ a ∈ E, ∀ v ∈ W0, (ρ a : Module.End K V) v ∈ W0) :
    E →* (Module.End K W0)ˣ where
  toFun := l48dB_resUnit ρ hinv
  map_one' := by
    apply Units.ext
    apply LinearMap.ext
    intro v
    apply Subtype.ext
    rw [l48dB_resUnit_val]
    simp
  map_mul' := by
    intro a b
    apply Units.ext
    apply LinearMap.ext
    intro v
    apply Subtype.ext
    rw [l48dB_resUnit_val]
    simp [l48dB_resUnit_val, Module.End.mul_apply, map_mul]

theorem ggB2der_no_fixed_isotropic_plane {K : Type*} [Field K] [CharP K 2] [Finite K] {V : Type*}
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] {G : Type*} [Group G]
    (hK : Nat.card K = 2) (ρ : G →* (Module.End K V)ˣ)
    (hρ : Function.Injective ρ) (B : LinearMap.BilinForm K V) (hB : B.Nondegenerate)
    (hr : B.IsRefl) (halt : ∀ v, B v v = 0)
    (hiso : ∀ g v w, B ((ρ g : Module.End K V) v) ((ρ g : Module.End K V) w) = B v w)
    (hdim : Module.finrank K V = 8) {E U : Subgroup G} (hE : IsElemAbelian 3 E)
    (hEc : Nat.card E = 27) {z : G} (hzE : z ∈ E) (hz1 : z ≠ 1)
    (hW0 : Module.finrank K (SmallRule.fixSpaceOf ρ (Subgroup.zpowers z)) = 4)
    (hker : ∀ a ∈ E, (∀ v ∈ SmallRule.fixSpaceOf ρ (Subgroup.zpowers z),
        (ρ a : Module.End K V) v = v) → a ∈ Subgroup.zpowers z)
    (hU1 : U ≠ ⊥) (hU2 : IsPGroup 2 U) (hEU : ∀ a ∈ E, ∀ u ∈ U, a * u * a⁻¹ ∈ U) :
    SmallRule.fixSpaceOf ρ E = ⊥ ∧
      ∃ T : Submodule K V, Module.finrank K T = 2 ∧ (∀ u ∈ T, ∀ v ∈ T, B u v = 0) ∧
        (∀ a ∈ E, ∀ v ∈ T, (ρ a : Module.End K V) v ∈ T) ∧
        T ≤ B.orthogonal (SmallRule.fixSpaceOf ρ (Subgroup.zpowers z)) := by
  classical
  set W0 : Submodule K V := SmallRule.fixSpaceOf ρ (Subgroup.zpowers z) with hW0def
  have hW0' : Module.finrank K W0 = 4 := by rw [hW0def]; exact hW0
  have hz3 : z ^ 3 = 1 := hE.2 z hzE
  have hcommE : ∀ a b : E, a * b = b * a := isMulCommutative_iff.mp hE.1
  have hcommG : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a := by
    intro a ha b hb
    simpa using congrArg Subtype.val (hcommE ⟨a, ha⟩ ⟨b, hb⟩)
  obtain ⟨hcompl0, hinvW0z, hinvW1z0, hfixW1z⟩ :=
    ggB2der_fix_orth_decomp hK ρ B hB hr hiso hz3
  rw [← hW0def] at hcompl0 hinvW0z hinvW1z0 hfixW1z
  set W1 : Submodule K V := B.orthogonal W0 with hW1def
  have hinvW0 : ∀ a ∈ E, ∀ v ∈ W0, (ρ a : Module.End K V) v ∈ W0 :=
    fun a ha => hinvW0z a (hcommG a ha z hzE)
  have hinvW1 : ∀ a ∈ E, ∀ v ∈ W1, (ρ a : Module.End K V) v ∈ W1 :=
    fun a ha => hinvW1z0 a (hcommG a ha z hzE)
  have hW1fin : Module.finrank K W1 = 4 := by
    have h := Submodule.finrank_add_eq_of_isCompl hcompl0
    rw [hW0', hdim] at h
    omega
  have hB0 : (B.restrict W0).Nondegenerate :=
    LinearMap.BilinForm.nondegenerate_restrict_of_disjoint_orthogonal B hr hcompl0.disjoint
  have hr0 : (B.restrict W0).IsRefl := by
    intro x y
    rw [l48dB_restrict_apply, l48dB_restrict_apply]
    exact hr.eq_iff.mp
  let φ : E →* (Module.End K W0)ˣ := l48dB_resHom ρ hinvW0
  let X0 : Subgroup (Module.End K W0)ˣ := φ.range
  have hφapply : ∀ (a : E) (v : W0),
      ((φ a : Module.End K W0) v : V) = (ρ (a : G) : Module.End K V) v := by
    intro a v
    exact l48dB_resUnit_val ρ hinvW0 a v
  have hX0comm : ∀ x ∈ X0, ∀ y ∈ X0, x * y = y * x := by
    intro x hx y hy
    obtain ⟨a, rfl⟩ := MonoidHom.mem_range.mp hx
    obtain ⟨b, rfl⟩ := MonoidHom.mem_range.mp hy
    rw [← map_mul, ← map_mul, hcommE a b]
  have hX0exp : ∀ x ∈ X0, x ^ 3 = 1 := by
    intro x hx
    obtain ⟨a, rfl⟩ := MonoidHom.mem_range.mp hx
    have h := map_pow φ a 3
    have ha3 : a ^ 3 = 1 := by
      apply Subtype.ext
      rw [Subgroup.coe_pow, Subgroup.coe_one]
      exact hE.2 (a : G) a.2
    rw [ha3, map_one] at h
    exact h.symm
  have hX0iso : ∀ x ∈ X0, ∀ v w : W0,
      (B.restrict W0) ((x : Module.End K W0) v) ((x : Module.End K W0) w) =
        (B.restrict W0) v w := by
    intro x hx v w
    obtain ⟨a, rfl⟩ := MonoidHom.mem_range.mp hx
    rw [l48dB_restrict_apply, l48dB_restrict_apply, hφapply, hφapply]
    exact hiso (a : G) (v : V) (w : V)
  haveI : Finite (Subgroup.zpowers z) :=
    finite_zpowers.mpr (isOfFinOrder_iff_pow_eq_one.mpr ⟨3, by norm_num, by simpa using hz3⟩)
  have hker_le : Nat.card φ.ker ≤ 3 := by
    have hmem : ∀ a : φ.ker, (a.1 : G) ∈ Subgroup.zpowers z := by
      intro a
      refine hker (a.1 : G) a.1.2 ?_
      intro v hv
      have ha : φ a.1 = 1 := MonoidHom.mem_ker.mp a.2
      have h1 : ((φ a.1 : Module.End K W0) ⟨v, hv⟩ : V) = v := by
        have h2 := congrArg (fun u : (Module.End K W0)ˣ =>
          (u : Module.End K W0) ⟨v, hv⟩) ha
        simp only [Units.val_one, Module.End.one_apply] at h2
        exact congrArg Subtype.val h2
      simpa using (hφapply a.1 ⟨v, hv⟩).symm.trans h1
    have hinj : Function.Injective
        (fun a : φ.ker => (⟨(a.1 : G), hmem a⟩ : Subgroup.zpowers z)) := by
      intro a b hab
      have h1 : (a.1 : G) = (b.1 : G) :=
        congrArg (fun x : Subgroup.zpowers z => (x : G)) hab
      exact Subtype.ext (Subtype.ext h1)
    calc Nat.card φ.ker ≤ Nat.card (Subgroup.zpowers z) :=
          Nat.card_le_card_of_injective _ hinj
      _ = orderOf z := Nat.card_zpowers (a := z)
      _ ≤ 3 := Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one hz3)
  have hquot : Nat.card (E ⧸ φ.ker) = Nat.card φ.range :=
    Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv
  have hprod : Nat.card φ.range * Nat.card φ.ker = 27 := by
    have h := Subgroup.card_eq_card_quotient_mul_card_subgroup φ.ker
    rw [hEc, hquot] at h
    omega
  have hX0card : 9 ≤ Nat.card X0 := by
    have hb : Nat.card φ.range * Nat.card φ.ker ≤ Nat.card φ.range * 3 :=
      Nat.mul_le_mul_left _ hker_le
    rw [hprod] at hb
    show 9 ≤ Nat.card φ.range
    omega
  have hnoiso : ∀ T : Submodule K W0, T ≠ ⊥ →
      (∀ u ∈ T, ∀ v ∈ T, (B.restrict W0) u v = 0) →
      (∀ x ∈ X0, ∀ t ∈ T, (x : Module.End K W0) t ∈ T) → False :=
    fun T hT0 hTiso hTX =>
      l48dB_no_inv_isotropic hK (B.restrict W0) hB0 hr0 X0 hX0comm hX0exp hX0iso hX0card
        hW0' hT0 hTiso hTX
  have hfix_bot : SmallRule.fixSpaceOf ρ E = ⊥ := by
    rw [eq_bot_iff]
    intro v hv
    rw [Submodule.mem_bot]
    by_contra hv0
    have hvW0 : v ∈ W0 := by
      rw [hW0def, SmallRule.mem_fixSpaceOf]
      intro w hw
      exact hv w (Subgroup.zpowers_le.mpr hzE hw)
    let x : W0 := ⟨v, hvW0⟩
    have hx0 : x ≠ 0 := by intro h; exact hv0 (congrArg Subtype.val h)
    have hT0 : (Submodule.span K {x} : Submodule K W0) ≠ ⊥ := by
      intro h
      have hxbot : x ∈ (⊥ : Submodule K W0) := by
        rw [← h]
        exact Submodule.mem_span_singleton_self x
      rw [Submodule.mem_bot] at hxbot
      exact hx0 hxbot
    have hTiso : ∀ u ∈ (Submodule.span K {x} : Submodule K W0),
        ∀ w ∈ (Submodule.span K {x} : Submodule K W0), (B.restrict W0) u w = 0 := by
      intro u hu w hw
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hu
      obtain ⟨d, rfl⟩ := Submodule.mem_span_singleton.mp hw
      rw [l48dB_restrict_apply]
      simp [halt]
    have hTX : ∀ y ∈ X0, ∀ t ∈ (Submodule.span K {x} : Submodule K W0),
        (y : Module.End K W0) t ∈ (Submodule.span K {x} : Submodule K W0) := by
      intro y hy t ht
      obtain ⟨a, rfl⟩ := MonoidHom.mem_range.mp hy
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp ht
      rw [map_smul]
      have hxfix : (φ a : Module.End K W0) x = x := by
        apply Subtype.ext
        rw [hφapply]
        exact hv (a : G) a.2
      rw [hxfix]
      exact Submodule.smul_mem _ c (Submodule.mem_span_singleton_self x)
    exact hnoiso _ hT0 hTiso hTX
  obtain ⟨T, hT0ne, hTisoV, hTE⟩ :=
    SmallRule.exists_isotropic_of_normalizes_two hK ρ hρ B hB hr hiso hU1 hU2 hEU
  have hTbound : Nat.card (E.map ρ) ^ 2 ≤ 3 ^ (Module.finrank K V - Module.finrank K T) := by
    refine SmallRule.card_sq_le_of_isotropic hK B hB hr (E.map ρ) ?_ ?_ ?_ hT0ne hTisoV ?_
    · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
      rw [← map_mul, ← map_mul, hcommG a ha b hb]
    · rintro _ ⟨a, ha, rfl⟩
      have h := map_pow ρ a 3
      rw [hE.2 a ha, map_one] at h
      exact h.symm
    · rintro _ ⟨a, ha, rfl⟩ v w
      exact hiso a v w
    · rintro _ ⟨a, ha, rfl⟩ t ht
      exact hTE a ha t ht
  have hcardE : Nat.card (E.map ρ) = 27 := by
    rw [(Nat.card_congr (E.equivMapOfInjective ρ hρ).toEquiv).symm, hEc]
  rw [hcardE, hdim] at hTbound
  have hTfin_le : Module.finrank K T ≤ 2 := by
    have h6 : (3 : ℕ) ^ 6 ≤ 3 ^ (8 - Module.finrank K T) := by
      have h27 : (27 : ℕ) ^ 2 = 3 ^ 6 := by norm_num
      rw [h27] at hTbound
      exact hTbound
    have := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 3)).mp h6
    omega
  have hTne1 : Module.finrank K T ≠ 1 := by
    intro h1
    have hle : T ≤ SmallRule.fixSpaceOf ρ E := l48dB_inv_line_fix hK ρ h1 hTE
    rw [hfix_bot] at hle
    exact hT0ne (le_bot_iff.mp hle)
  have hTfin : Module.finrank K T = 2 := by
    have h1 : 1 ≤ Module.finrank K T := Submodule.one_le_finrank_iff.mpr hT0ne
    omega
  have hinter_bot : T ⊓ W0 = ⊥ := by
    by_contra hne
    have hle2 : Module.finrank K (T ⊓ W0 : Submodule K V) ≤ 2 := by
      calc Module.finrank K (T ⊓ W0 : Submodule K V) ≤ Module.finrank K T :=
            Submodule.finrank_mono inf_le_left
        _ = 2 := hTfin
    have hcases : Module.finrank K (T ⊓ W0 : Submodule K V) = 1 ∨
        Module.finrank K (T ⊓ W0 : Submodule K V) = 2 := by
      have hpos : 1 ≤ Module.finrank K (T ⊓ W0 : Submodule K V) :=
        Submodule.one_le_finrank_iff.mpr hne
      omega
    rcases hcases with h1 | h2
    · have hinv : ∀ a ∈ E, ∀ v ∈ T ⊓ W0, (ρ a : Module.End K V) v ∈ T ⊓ W0 :=
        fun a ha v hv => ⟨hTE a ha v hv.1, hinvW0 a ha v hv.2⟩
      have hle' : T ⊓ W0 ≤ SmallRule.fixSpaceOf ρ E := l48dB_inv_line_fix hK ρ h1 hinv
      rw [hfix_bot] at hle'
      exact (hne (le_bot_iff.mp hle')).elim
    · have hTeq : T ⊓ W0 = T :=
        Submodule.eq_of_le_of_finrank_eq inf_le_left (by rw [h2, hTfin])
      have hTle : T ≤ W0 := inf_eq_left.mp hTeq
      have hT'ne : T.comap W0.subtype ≠ ⊥ := by
        obtain ⟨t, ht, ht0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hT0ne
        intro hbot
        have hmem : (⟨t, hTle ht⟩ : W0) ∈ T.comap W0.subtype := by
          show (W0.subtype ⟨t, hTle ht⟩) ∈ T
          exact ht
        rw [hbot] at hmem
        rw [Submodule.mem_bot] at hmem
        exact ht0 (congrArg Subtype.val hmem)
      have hT'iso : ∀ u ∈ T.comap W0.subtype, ∀ v ∈ T.comap W0.subtype,
          (B.restrict W0) u v = 0 := by
        intro u hu v hv
        rw [l48dB_restrict_apply]
        exact hTisoV (u : V) (show (u : V) ∈ T from hu) (v : V) (show (v : V) ∈ T from hv)
      have hT'X : ∀ x ∈ X0, ∀ t ∈ T.comap W0.subtype,
          (x : Module.End K W0) t ∈ T.comap W0.subtype := by
        intro x hx t ht
        obtain ⟨a, rfl⟩ := MonoidHom.mem_range.mp hx
        change (((φ a : Module.End K W0) t : W0) : V) ∈ T
        rw [hφapply a t]
        exact hTE (a : G) a.2 (t : V) (show (t : V) ∈ T from ht)
      exact hnoiso _ hT'ne hT'iso hT'X
  have hzsub : ∀ t : V, (ρ z : Module.End K V) t - t ∈ W1 := by
    intro t
    rw [hW1def, LinearMap.BilinForm.mem_orthogonal_iff]
    intro w hw
    have hzw : (ρ z⁻¹ : Module.End K V) w = w :=
      (SmallRule.mem_fixSpaceOf.mp hw) z⁻¹ (by simpa using Subgroup.zpow_mem_zpowers z (-1))
    have hzt : (ρ z⁻¹ : Module.End K V) ((ρ z : Module.End K V) t) = t := by
      rw [← Module.End.mul_apply, ← Units.val_mul, map_inv, inv_mul_cancel, Units.val_one,
        Module.End.one_apply]
    have h1 : B w ((ρ z : Module.End K V) t) = B w t := by
      have h2 := hiso z⁻¹ w ((ρ z : Module.End K V) t)
      rw [hzw, hzt] at h2
      exact h2.symm
    rw [map_sub, h1, sub_self]
  have hTleW1 : T ≤ W1 := by
    have hSle : Module.finrank K (T ⊓ W1 : Submodule K V) ≤ 2 := by
      calc Module.finrank K (T ⊓ W1 : Submodule K V) ≤ Module.finrank K T :=
            Submodule.finrank_mono inf_le_left
        _ = 2 := hTfin
    have hcases : Module.finrank K (T ⊓ W1 : Submodule K V) = 0 ∨
        Module.finrank K (T ⊓ W1 : Submodule K V) = 1 ∨
        Module.finrank K (T ⊓ W1 : Submodule K V) = 2 := by omega
    rcases hcases with h0 | h1 | h2
    · have hSbot : T ⊓ W1 = ⊥ := (Submodule.finrank_eq_zero).mp h0
      have hTW0 : T ≤ W0 := by
        intro t ht
        have hmem : (ρ z : Module.End K V) t - t ∈ T ⊓ W1 :=
          ⟨Submodule.sub_mem (p := T) (hTE z hzE t ht) ht, hzsub t⟩
        rw [hSbot, Submodule.mem_bot] at hmem
        have hzt : (ρ z : Module.End K V) t = t := sub_eq_zero.mp hmem
        rw [hW0def, SmallRule.mem_fixSpaceOf]
        intro w hw
        exact l48dB_zpowers_fix hzt hw
      have hTbot : T = ⊥ := by
        rw [← hinter_bot]
        exact le_antisymm (le_inf le_rfl hTW0) inf_le_left
      exact absurd hTbot hT0ne
    · have hne' : T ⊓ W1 ≠ ⊥ := by
        intro h
        rw [h, finrank_bot] at h1
        omega
      have hinv : ∀ a ∈ E, ∀ v ∈ T ⊓ W1, (ρ a : Module.End K V) v ∈ T ⊓ W1 :=
        fun a ha v hv => ⟨hTE a ha v hv.1, hinvW1 a ha v hv.2⟩
      have hle' : T ⊓ W1 ≤ SmallRule.fixSpaceOf ρ E := l48dB_inv_line_fix hK ρ h1 hinv
      rw [hfix_bot] at hle'
      exact (hne' (le_bot_iff.mp hle')).elim
    · have hSeq : T ⊓ W1 = T :=
        Submodule.eq_of_le_of_finrank_eq inf_le_left (by rw [h2, hTfin])
      exact inf_eq_left.mp hSeq
  exact ⟨hfix_bot, T, hTfin, hTisoV, hTE, hTleW1⟩

end CFSG.StandardType

end
