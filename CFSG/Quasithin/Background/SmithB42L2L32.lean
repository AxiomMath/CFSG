module

public import CFSG.Quasithin.Background.SmithB42Families
public import CFSG.Quasithin.H13.NQTermTensorEquality
public import CFSG.Quasithin.Background.G64NatSec
public import CFSG.Quasithin.Background.SmithB42L2Sl2
public import CFSG.Quasithin.Background.SmithB51LnB42

public section

namespace CFSG.Quasithin

namespace B42L2

open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup.Layer
  CFSG.QuasithinUnique.Setup.Layer.Actor CFSG.QuasithinUnique.Setup.Lift
  CFSG.QuasithinUnique.Setup.Family CFSG.ProperTwoGeneratedCore.BinaryThreeSpace
open scoped Matrix

theorem center_sl3_eq_bot {K : Type} [Field K] [Fintype K] (hK : Fintype.card K = 2) :
    Subgroup.center (Matrix.SpecialLinearGroup (Fin 3) K) = ⊥ := by
  classical
  rw [Subgroup.eq_bot_iff_forall]
  intro A hA
  obtain ⟨r, hr, hrA⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hA
  have hr0 : r ≠ 0 := by
    rintro rfl
    rw [Fintype.card_fin, zero_pow (by norm_num)] at hr
    exact zero_ne_one hr
  have hr1 : r = 1 := by
    have h01 : (0 : K) ≠ 1 := zero_ne_one
    have huniv : (Finset.univ : Finset K) = {0, 1} := by
      symm
      apply Finset.eq_univ_of_card
      rw [Finset.card_pair h01, hK]
    have hmem : r ∈ (Finset.univ : Finset K) := Finset.mem_univ r
    rw [huniv, Finset.mem_insert, Finset.mem_singleton] at hmem
    exact hmem.resolve_left hr0
  subst hr1
  ext1
  rw [Matrix.SpecialLinearGroup.coe_one, ← hrA, map_one]

@[expose] noncomputable def slEquivGL32 :
    Matrix.SpecialLinearGroup (Fin 3) (ZMod 2) ≃* GL32 :=
  MulEquiv.ofBijective Matrix.SpecialLinearGroup.toGL
    ⟨Matrix.SpecialLinearGroup.toGL_injective, fun g => by
      have hdet : IsUnit (g : Mat3).det := (Matrix.isUnit_iff_isUnit_det _).mp g.isUnit
      have h1 : (g : Mat3).det = 1 := by
        rcases hdet with ⟨u, hu⟩
        rw [← hu]
        exact congrArg Units.val (Subsingleton.elim u 1)
      exact ⟨⟨g, h1⟩, Units.ext rfl⟩⟩

theorem exists_gl32_of_model {X : Type} [Group X] (hZ : Subgroup.center X = ⊥)
    (h : StatedClassicalModel (X ⧸ Subgroup.center X) .PSL 3 2 1) : Nonempty (X ≃* GL32) := by
  obtain ⟨-, K, hK, hKfin, hcard, ⟨e⟩⟩ := h
  have : Fintype K := Fintype.ofFinite K
  have hcardK : Fintype.card K = 2 := by rw [← Nat.card_eq_fintype_card, hcard]; norm_num
  have hc : Fintype.card K = Fintype.card (ZMod 2) := by rw [hcardK, ZMod.card]
  let ε : K ≃+* ZMod 2 := FiniteField.ringEquivOfCardEq hc
  let e₁ : X ≃* X ⧸ Subgroup.center X :=
    QuotientGroup.quotientBot.symm.trans (QuotientGroup.quotientMulEquivOfEq hZ.symm)
  let e₂ : Matrix.ProjectiveSpecialLinearGroup (Fin 3) K ≃* Matrix.SpecialLinearGroup (Fin 3) K :=
    (QuotientGroup.quotientMulEquivOfEq (center_sl3_eq_bot hcardK)).trans QuotientGroup.quotientBot
  let e₃ : Matrix.SpecialLinearGroup (Fin 3) K ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2) :=
    MonoidHom.toMulEquiv (Matrix.SpecialLinearGroup.map ε.toRingHom)
      (Matrix.SpecialLinearGroup.map ε.symm.toRingHom)
      (MonoidHom.ext fun A => Subtype.ext (by
        ext i j
        simp [Matrix.SpecialLinearGroup.map_apply_coe]))
      (MonoidHom.ext fun A => Subtype.ext (by
        ext i j
        simp [Matrix.SpecialLinearGroup.map_apply_coe]))
  exact ⟨(e₁.trans e).trans ((projectiveSpecialLinearGroupEquivStatedProj 3 K).symm.trans
    ((e₂.trans e₃).trans slEquivGL32))⟩

theorem axis_faithful : ∀ b c : ZMod 2, (∀ w : Fin 3 → ZMod 2, unitri 0 b c *ᵥ w = w) →
    b = 0 ∧ c = 0 := by
  decide +kernel

theorem axis_fix_card :
    Fintype.card {w : Fin 3 → ZMod 2 // ∀ b c : ZMod 2, unitri 0 b c *ᵥ w = w} = 4 := by
  decide +kernel

@[expose] noncomputable def axisHom : Multiplicative (ZMod 2 × ZMod 2) →* GL32 where
  toFun x := unitriGL 0 (Multiplicative.toAdd x).1 (Multiplicative.toAdd x).2
  map_one' := Units.ext unitri_zero
  map_mul' x y := Units.ext (by
    change unitri 0 _ _ = unitri 0 _ _ * unitri 0 _ _
    rw [unitri_mul]
    simp)

theorem axisHom_val (x : Multiplicative (ZMod 2 × ZMod 2)) :
    ((axisHom x : GL32) : Mat3) = unitri 0 (Multiplicative.toAdd x).1 (Multiplicative.toAdd x).2 :=
  rfl

theorem det_eq_one_GL32 (g : GL32) : (g : Mat3).det = 1 := by
  have hdet : IsUnit (g : Mat3).det := (Matrix.isUnit_iff_isUnit_det _).mp g.isUnit
  rcases hdet with ⟨u, hu⟩
  rw [← hu]
  exact congrArg Units.val (Subsingleton.elim u 1)

section Units

variable {V : Type} [CommGroup V] {W : Type} [AddCommGroup W] [Module (ZMod 2) W]

@[expose] noncomputable def unitsPsi (θ : V ≃* Multiplicative W) :
    MulAut V ≃* (Module.End (ZMod 2) W)ˣ :=
  (binPsi θ).trans (unitsEquiv (ZMod 2) W).symm

theorem unitsPsi_apply (θ : V ≃* Multiplicative W) (φ : MulAut V) (w : W) :
    (unitsPsi θ φ : Module.End (ZMod 2) W) w = binPsi θ φ w := by
  rw [← unitsEquiv_apply, unitsPsi, MulEquiv.trans_apply, MulEquiv.apply_symm_apply]

theorem unitsPsi_toAdd (θ : V ≃* Multiplicative W) (φ : MulAut V) (v : V) :
    (unitsPsi θ φ : Module.End (ZMod 2) W) (Multiplicative.toAdd (θ v)) =
      Multiplicative.toAdd (θ (φ v)) := by
  rw [unitsPsi_apply, toAdd_binPsi]

theorem natCard_fixedSub_map (θ : V ≃* Multiplicative W) (A : Subgroup (MulAut V)) :
    Nat.card ↥(LocalAnalysis.CommutingFactor.fixedSub (A.map (unitsPsi θ).toMonoidHom)) =
      Nat.card ↥(fixV A) := by
  symm
  refine Nat.card_congr
    { toFun := fun v => ⟨Multiplicative.toAdd (θ v), fun a ha => ?_⟩
      invFun := fun w => ⟨θ.symm (Multiplicative.ofAdd w), fun φ hφ => ?_⟩
      left_inv := fun v => Subtype.ext (by simp)
      right_inv := fun w => Subtype.ext (by simp) }
  · obtain ⟨φ, hφ, rfl⟩ := ha
    show (unitsPsi θ φ : Module.End (ZMod 2) W) (Multiplicative.toAdd (θ v)) = _
    rw [unitsPsi_toAdd, v.2 φ hφ]
  · have h1 := w.2 (unitsPsi θ φ) ⟨φ, hφ, rfl⟩
    have h2 : (unitsPsi θ φ : Module.End (ZMod 2) W)
        (Multiplicative.toAdd (θ (θ.symm (Multiplicative.ofAdd (w : W))))) = w := by
      simpa using h1
    rw [unitsPsi_toAdd] at h2
    apply θ.injective
    apply Multiplicative.toAdd.injective
    rw [h2]
    simp

theorem eq_one_of_unitsPsi (θ : V ≃* Multiplicative W) {φ : MulAut V}
    (h : ∀ w, (unitsPsi θ φ : Module.End (ZMod 2) W) w = w) : φ = 1 := by
  ext v
  have h1 := h (Multiplicative.toAdd (θ v))
  rw [unitsPsi_toAdd] at h1
  exact θ.injective (Multiplicative.toAdd.injective h1)

end Units

section Core

variable {V : Type} [CommGroup V] [Finite V] {W : Type} [AddCommGroup W] [Module (ZMod 2) W]
  [Finite W]

omit [Finite V] [Finite W] in
theorem map_unitsPsi_ne_bot (θ : V ≃* Multiplicative W) {A : Subgroup (MulAut V)}
    (hA : A ≠ ⊥) : A.map (unitsPsi θ).toMonoidHom ≠ ⊥ := by
  rw [Ne, Subgroup.map_eq_bot_iff_of_injective A (unitsPsi θ).injective]
  exact hA

omit [Finite V] [Finite W] in
theorem comm_map_unitsPsi (θ : V ≃* Multiplicative W) {A : Subgroup (MulAut V)}
    (hA : IsElemAbelian2 A) :
    (∀ a ∈ A.map (unitsPsi θ).toMonoidHom, ∀ b ∈ A.map (unitsPsi θ).toMonoidHom,
      a * b = b * a) ∧ ∀ a ∈ A.map (unitsPsi θ).toMonoidHom, a ^ 2 = 1 := by
  refine ⟨?_, ?_⟩
  · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    rw [← map_mul, ← map_mul, hA.1 a ha b hb]
  · rintro _ ⟨a, ha, rfl⟩
    rw [← map_pow, hA.2 a ha, map_one]

theorem finrank_le_of_offender (θ : V ≃* Multiplicative W) {G A : Subgroup (MulAut V)}
    (hA : IsFFStarOffender G A) :
    Module.finrank (ZMod 2) W ≤ rk ↥A + Module.finrank (ZMod 2)
      ↥(LocalAnalysis.CommutingFactor.fixedSub (A.map (unitsPsi θ).toMonoidHom)) := by
  have h1 := card_le_of_offender hA
  rw [← natCard_fixedSub_map θ, B1.card_elemAbelian hA.2.2.1, natCard_eq θ,
    H13.NQTerm.card_eq_two_pow_finrank (M := W), H13.NQTerm.card_eq_two_pow_finrank
      (M := ↥(LocalAnalysis.CommutingFactor.fixedSub (A.map (unitsPsi θ).toMonoidHom))),
    ← pow_add] at h1
  exact (Nat.pow_le_pow_iff_right (by norm_num)).1 h1

private theorem data_of_b4HypCore {G L : Subgroup (MulAut V)} (h : B4HypCore G L) :
    L ≤ G ∧ (∀ g ∈ G, ∀ l ∈ L, g * l * g⁻¹ ∈ L) ∧
      (∀ g ∈ G, (∀ l ∈ L, g * l = l * g) → g ∈ L) ∧ CFSG.IsQuasisimple ↥L := by
  obtain ⟨hL, hq, -⟩ := h
  subst hL
  refine ⟨quasithinGenFitting_le G, fun g hg l hl => ?_, fun g hg hcomm => ?_, hq⟩
  · exact (Subgroup.mem_normalizer_iff.1 (le_normalizer_quasithinGenFitting G hg) l).1 hl
  · apply centralizer_quasithinGenFitting_le G
    exact ⟨hg, Subgroup.mem_centralizer_iff.2 fun l hl => (hcomm l hl).symm⟩

theorem eq_of_l32_core (θ : V ≃* Multiplicative W) {G L : Subgroup (MulAut V)}
    (hHyp : B4HypCore G L) (hZ : Subgroup.center ↥L = ⊥) (eL : ↥L ≃* GL32)
    {A : Subgroup (MulAut V)} (hA : IsFFStarOffender G A) : G = L := by
  classical
  have : FiniteDimensional (ZMod 2) W := Module.Finite.of_finite
  obtain ⟨hLG, hLn, hself, -⟩ := data_of_b4HypCore hHyp
  by_contra hne
  obtain ⟨g, hgG, hgL⟩ : ∃ g ∈ G, g ∉ L := by
    by_contra hcon
    push Not at hcon
    exact hne (le_antisymm hcon hLG)
  set Φ := unitsPsi θ with hΦ
  have hfaith : ∀ d ∈ G.map Φ.toMonoidHom,
      (∀ v ∈ (⊤ : Submodule (ZMod 2) W), (d : Module.End (ZMod 2) W) v = v) → d = 1 := by
    rintro _ ⟨φ, -, rfl⟩ h
    rw [eq_one_of_unitsPsi θ fun w => h w Submodule.mem_top]
    exact map_one _
  have hYn : ∀ d ∈ G.map Φ.toMonoidHom, ∀ y ∈ L.map Φ.toMonoidHom,
      d * y * d⁻¹ ∈ L.map Φ.toMonoidHom := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨l, hl, rfl⟩
    exact ⟨x * l * x⁻¹, hLn x hx l hl, by simp⟩
  have hCY : ∀ d ∈ G.map Φ.toMonoidHom,
      (∀ y ∈ L.map Φ.toMonoidHom, d * y = y * d) → d = 1 := by
    rintro _ ⟨x, hx, rfl⟩ h
    have hc : ∀ l ∈ L, x * l = l * x := fun l hl =>
      Φ.injective (by rw [map_mul, map_mul]; exact h _ ⟨l, hl, rfl⟩)
    have hxL := hself x hx hc
    have hcen : (⟨x, hxL⟩ : ↥L) ∈ Subgroup.center ↥L := by
      rw [Subgroup.mem_center_iff]
      intro y
      exact Subtype.ext (hc y y.2).symm
    rw [hZ, Subgroup.mem_bot] at hcen
    have : x = 1 := congrArg Subtype.val hcen
    rw [this]
    exact map_one _
  let eY : ↥(L.map Φ.toMonoidHom) ≃* GL32 :=
    (L.equivMapOfInjective Φ.toMonoidHom Φ.injective).symm.trans eL
  obtain ⟨hAc, hA2⟩ := comm_map_unitsPsi θ hA.2.2.1
  have hd₀Y : Φ g ∉ L.map Φ.toMonoidHom := by
    rintro ⟨l, hl, hlg⟩
    exact hgL (Φ.injective hlg ▸ hl)
  have hlt := H13.NQTerm.lt_finrank_of_not_le (I := ⊤) (fun _ _ _ _ => Submodule.mem_top)
    hfaith (Subgroup.map_mono hLG) hYn eY hCY (Subgroup.map_mono hA.1)
    (map_unitsPsi_ne_bot θ hA.2.1) hAc hA2 (d₀ := Φ g) ⟨g, hgG, rfl⟩ hd₀Y
    (a := rk ↥A) (by rw [Subgroup.card_map_of_injective Φ.injective, B1.card_elemAbelian hA.2.2.1])
  rw [top_inf_eq, finrank_top] at hlt
  have hle := finrank_le_of_offender θ hA
  rw [← hΦ] at hle
  omega

theorem eq_of_l32 (θ : V ≃* Multiplicative W) {G L : Subgroup (MulAut V)} (hHyp : B4Hyp G L)
    (hZ : Subgroup.center ↥L = ⊥) (eL : ↥L ≃* GL32) {A : Subgroup (MulAut V)}
    (hA : IsFFStarOffender G A) : G = L :=
  eq_of_l32_core θ hHyp.core hZ eL hA

end Core

section Data

variable {V : Type} [CommGroup V] [Finite V] {W : Type} [AddCommGroup W] [Module (ZMod 2) W]
  [Finite W]

theorem rk_of_card {X : Type*} [Group X] {k : ℕ} (h : Nat.card X = 2 ^ k) : rk X = k := by
  unfold rk
  rw [h, padicValNat.prime_pow]

theorem l32_offender_data (θ : V ≃* Multiplicative W) [Nontrivial W] {L : Subgroup (MulAut V)}
    (hirr : ∀ J : Subgroup V, (∀ l ∈ L, ∀ v ∈ J, l v ∈ J) → J = ⊥ ∨ J = ⊤)
    (eL : ↥L ≃* GL32) {B : Subgroup (MulAut V)} (hB : IsFFStarOffender L B) :
    Module.finrank (ZMod 2) W = 3 ∧
      ((rk ↥B = 1 ∧ Module.finrank (ZMod 2)
          ↥(LocalAnalysis.CommutingFactor.fixedSub (B.map (unitsPsi θ).toMonoidHom)) = 2) ∨
        (rk ↥B = 2 ∧ (Module.finrank (ZMod 2)
          ↥(LocalAnalysis.CommutingFactor.fixedSub (B.map (unitsPsi θ).toMonoidHom)) = 1 ∨
          Module.finrank (ZMod 2)
          ↥(LocalAnalysis.CommutingFactor.fixedSub (B.map (unitsPsi θ).toMonoidHom)) = 2))) := by
  classical
  have : FiniteDimensional (ZMod 2) W := Module.Finite.of_finite
  set Φ := unitsPsi θ with hΦ
  have hfaith : ∀ d ∈ L.map Φ.toMonoidHom,
      (∀ v ∈ (⊤ : Submodule (ZMod 2) W), (d : Module.End (ZMod 2) W) v = v) → d = 1 := by
    rintro _ ⟨φ, -, rfl⟩ h
    rw [eq_one_of_unitsPsi θ fun w => h w Submodule.mem_top]
    exact map_one _
  have hIirr : ∀ U ≤ (⊤ : Submodule (ZMod 2) W), (∀ d ∈ L.map Φ.toMonoidHom, ∀ v ∈ U,
      (d : Module.End (ZMod 2) W) v ∈ U) → U = ⊥ ∨ U = ⊤ := by
    intro U _ hU
    refine irr_map θ hirr U ?_
    rintro _ ⟨l, hl, rfl⟩ u hu
    have h1 := hU (Φ l) ⟨l, hl, rfl⟩ u hu
    rw [hΦ, unitsPsi_apply] at h1
    exact h1
  let eY : ↥(L.map Φ.toMonoidHom) ≃* GL32 :=
    (L.equivMapOfInjective Φ.toMonoidHom Φ.injective).symm.trans eL
  obtain ⟨hBc, hB2⟩ := comm_map_unitsPsi θ hB.2.2.1
  have hcases := H13.NQTerm.gl3_cases (I := ⊤) (fun _ _ _ _ => Submodule.mem_top)
    top_ne_bot hIirr hfaith le_rfl le_rfl eY
    (Subgroup.map_mono hB.1) (map_unitsPsi_ne_bot θ hB.2.1) hBc hB2 (a := rk ↥B)
    (by rw [Subgroup.card_map_of_injective Φ.injective, B1.card_elemAbelian hB.2.2.1])
  have hle := finrank_le_of_offender θ hB
  rw [← hΦ] at hle
  rw [top_inf_eq, finrank_top] at hcases
  rcases hcases with ⟨h3, -, h⟩ | ⟨h8, h⟩
  · exact ⟨h3, h⟩
  · exfalso
    rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega

end Data

section Natural

variable {V : Type} [CommGroup V] {W : Type} [AddCommGroup W] [Module (ZMod 2) W] [Finite W]

theorem exists_natural_l32 (θ : V ≃* Multiplicative W) [Nontrivial W]
    {L : Subgroup (MulAut V)}
    (hirr : ∀ J : Subgroup V, (∀ l ∈ L, ∀ v ∈ J, l v ∈ J) → J = ⊥ ∨ J = ⊤)
    (eL : ↥L ≃* GL32) (h3 : Module.finrank (ZMod 2) W = 3) :
    ∃ π' : GL32 →* ↥L, Function.Surjective π' ∧ ∃ f : V ≃* Multiplicative (Fin 3 → ZMod 2),
      ∀ (g : GL32) (v : V), f (((π' g : ↥L) : MulAut V) v) =
        Multiplicative.ofAdd ((g : Mat3) *ᵥ Multiplicative.toAdd (f v)) := by
  classical
  let ρ : GL32 →* (W ≃ₗ[ZMod 2] W) :=
    (binPsi θ).toMonoidHom.comp (L.subtype.comp eL.symm.toMonoidHom)
  have hρ : ∀ g w, ρ g w = binPsi θ (eL.symm g : MulAut V) w := fun _ _ => rfl
  have hirrρ : IsIrrRep ρ := by
    refine isIrrRep_of inferInstance fun N hN => irr_map θ hirr N ?_
    rintro _ ⟨l, hl, rfl⟩ u hu
    have h1 := hN (eL ⟨l, hl⟩) u hu
    rw [hρ, MulEquiv.symm_apply_apply] at h1
    exact h1
  have hW8 : Nat.card W = 8 := by
    rw [H13.NQTerm.card_eq_two_pow_finrank (M := W), h3]
    norm_num
  have key : ∀ (τ : GL32 →* GL32), Function.Surjective τ →
      (∃ e : Vec3 ≃ₗ[ZMod 2] W, ∀ g v, e ((τ g : Mat3) *ᵥ v) = ρ g (e v)) →
      ∃ π' : GL32 →* ↥L, Function.Surjective π' ∧
        ∃ f : V ≃* Multiplicative (Fin 3 → ZMod 2), ∀ (g : GL32) (v : V),
          f (((π' g : ↥L) : MulAut V) v) =
            Multiplicative.ofAdd ((g : Mat3) *ᵥ Multiplicative.toAdd (f v)) := by
    intro τ hτs ⟨e, he⟩
    obtain ⟨σ, hσ⟩ : ∃ σ : GL32 → GL32, ∀ g, τ (σ g) = g :=
      ⟨fun g => (hτs g).choose, fun g => (hτs g).choose_spec⟩
    have hτinj : Function.Injective τ := by
      have : Finite GL32 := inferInstance
      exact Finite.injective_iff_surjective.mpr hτs
    let τe : GL32 ≃* GL32 := MulEquiv.ofBijective τ ⟨hτinj, hτs⟩
    refine ⟨eL.symm.toMonoidHom.comp τe.symm.toMonoidHom,
      eL.symm.surjective.comp τe.symm.surjective,
      θ.trans (AddEquiv.toMultiplicative e.symm.toAddEquiv), fun g v => ?_⟩
    set w := Multiplicative.toAdd (θ v) with hw
    have h1 : e ((τ (τe.symm g) : Mat3) *ᵥ e.symm w) = ρ (τe.symm g) w := by
      rw [he, LinearEquiv.apply_symm_apply]
    have h2 : τ (τe.symm g) = g := τe.apply_symm_apply g
    rw [h2] at h1
    show Multiplicative.ofAdd (e.symm (Multiplicative.toAdd
        (θ (((eL.symm (τe.symm g) : ↥L) : MulAut V) v)))) =
      Multiplicative.ofAdd ((g : Mat3) *ᵥ e.symm w)
    rw [← toAdd_binPsi, ← hρ, ← h1, LinearEquiv.symm_apply_apply]
  rcases irreducible_binary_GL3_classification ρ hirrρ with h | h | h | h
  · exfalso
    have := card_eq_of_modIso h
    rw [hW8, Nat.card_zmod] at this
    omega
  · obtain ⟨e, he⟩ := h
    exact key (MonoidHom.id GL32) Function.surjective_id ⟨e, fun g v => he g v⟩
  · obtain ⟨e, he⟩ := h
    refine key tauHom tauHom_surjective ⟨e, fun g v => ?_⟩
    exact he g v
  · exfalso
    have := card_eq_of_modIso h
    rw [hW8, natCard_traceZero] at this
    omega

end Natural

section Final

variable {V : Type} [CommGroup V] [Finite V]

theorem rAV_eq_of_card {B : Subgroup (MulAut V)} {k c : ℕ} (hV8 : Nat.card V = 2 ^ 3)
    (hB : rk ↥B = k) (hc : Nat.card ↥(fixV B) = 2 ^ c) :
    rAV B = ((3 - c : ℕ) : ℚ) / (k : ℚ) := by
  have h1 := rk_add_rkIdx (fixV B)
  rw [rk_of_card hc, rk_of_card hV8] at h1
  unfold rAV
  rw [hB, show rkIdx (fixV B) = 3 - c by omega]

omit [Finite V] in
theorem exists_axis {L : Subgroup (MulAut V)} (π' : GL32 →* ↥L)
    (f : V ≃* Multiplicative (Fin 3 → ZMod 2))
    (hf : ∀ (g : GL32) (v : V), f (((π' g : ↥L) : MulAut V) v) =
      Multiplicative.ofAdd ((g : Mat3) *ᵥ Multiplicative.toAdd (f v))) :
    ∃ B₀ : Subgroup (MulAut V), B₀ ≤ L ∧ B₀ ≠ ⊥ ∧ IsElemAbelian2 B₀ ∧ rk ↥B₀ = 2 ∧
      Nat.card ↥(fixV B₀) = 2 ^ 2 := by
  classical
  let ι₀ : Multiplicative (ZMod 2 × ZMod 2) →* MulAut V := L.subtype.comp (π'.comp axisHom)
  have hι : ∀ x v, f (ι₀ x v) = Multiplicative.ofAdd ((axisHom x : Mat3) *ᵥ
      Multiplicative.toAdd (f v)) := fun x v => hf _ v
  have hinj : Function.Injective ι₀ := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have hw : ∀ w : Fin 3 → ZMod 2, unitri 0 (Multiplicative.toAdd x).1
        (Multiplicative.toAdd x).2 *ᵥ w = w := by
      intro w
      have h1 := hι x (f.symm (Multiplicative.ofAdd w))
      rw [hx, MulAut.one_apply, MulEquiv.apply_symm_apply, toAdd_ofAdd, axisHom_val] at h1
      exact (Multiplicative.ofAdd.injective h1).symm
    obtain ⟨h1, h2⟩ := axis_faithful _ _ hw
    apply Multiplicative.toAdd.injective
    exact Prod.ext h1 h2
  have hcard : Nat.card ↥ι₀.range = 4 := by
    rw [← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv]
    simp [Nat.card_eq_fintype_card]
  refine ⟨ι₀.range, ?_, ?_, ⟨?_, ?_⟩, rk_of_card (by rw [hcard]; norm_num), ?_⟩
  · rintro _ ⟨x, rfl⟩
    exact (π' (axisHom x)).2
  · intro h
    rw [h, Subgroup.card_bot] at hcard
    omega
  · rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩
    rw [← map_mul, ← map_mul, mul_comm]
  · rintro _ ⟨x, rfl⟩
    rw [← map_pow]
    have hx : x ^ 2 = 1 := by
      apply Multiplicative.toAdd.injective
      rw [toAdd_pow, toAdd_one, two_nsmul]
      exact Prod.ext (CharTwo.add_self_eq_zero _) (CharTwo.add_self_eq_zero _)
    rw [hx, map_one]
  · rw [show (2 : ℕ) ^ 2 = 4 by norm_num, ← axis_fix_card, ← Nat.card_eq_fintype_card]
    refine Nat.card_congr
      { toFun := fun v => ⟨Multiplicative.toAdd (f v), fun b c => ?_⟩
        invFun := fun w => ⟨f.symm (Multiplicative.ofAdd w), fun φ hφ => ?_⟩
        left_inv := fun v => Subtype.ext (by simp)
        right_inv := fun w => Subtype.ext (by simp) }
    · have h1 := hι (Multiplicative.ofAdd (b, c)) v
      rw [show ι₀ (Multiplicative.ofAdd (b, c)) v = v from v.2 _ ⟨_, rfl⟩, axisHom_val] at h1
      exact (congrArg Multiplicative.toAdd h1).symm
    · obtain ⟨x, rfl⟩ := hφ
      apply f.injective
      rw [hι, MulEquiv.apply_symm_apply, toAdd_ofAdd, axisHom_val]
      exact congrArg Multiplicative.ofAdd (w.2 _ _)

end Final

end B42L2

open B42L2 CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique
  CFSG.QuasithinUnique.Setup.Layer.Actor CFSG.QuasithinUnique.Setup.Family in
theorem asB42L32_holds : AsB42L32 := by
  classical
  intro V _ _ hV G L hHyp hP A hA
  obtain ⟨hZ, hmodel⟩ := hP
  obtain ⟨eL⟩ := exists_gl32_of_model hZ hmodel
  have hV' : ∀ v : V, v * v = 1 := fun v => by rw [← pow_two]; exact hV v
  obtain ⟨W, _, _, _, ⟨θ⟩⟩ := exists_binModel_of_binary hV'
  have hirr := Bridge.TypeList.irr_of_isIrrSec hHyp.2.2.2
  have hntW : Nontrivial W := by
    obtain ⟨v, -, hv⟩ := IsConcreteLE.exists_of_lt hHyp.2.2.2.1
    replace hv : v ≠ 1 := fun h => hv (h ▸ Subgroup.one_mem _)
    refine ⟨⟨Multiplicative.toAdd (θ v), 0, fun h => hv ?_⟩⟩
    have h1 : θ v = 1 := Multiplicative.toAdd.injective (by simpa using h)
    simpa using congrArg θ.symm h1
  have hGL : G = L := eq_of_l32 θ hHyp hZ eL hA
  have hoffL : ∀ B, IsFFStarOffender G B → IsFFStarOffender L B := fun B hB => hGL ▸ hB
  obtain ⟨h3, -⟩ := l32_offender_data θ hirr eL (hoffL A hA)
  obtain ⟨π', hπ's, f, hf⟩ := exists_natural_l32 θ hirr eL h3
  have hV8 : Nat.card V = 2 ^ 3 := by
    rw [natCard_eq θ, H13.NQTerm.card_eq_two_pow_finrank (M := W), h3]
  refine Or.inr (Or.inl ⟨le_antisymm (hGL ▸ B6.ffJ_le G) (B5.Ln.le_ffJ_of_center hHyp hZ hA),
    ⟨1, ?_⟩, ?_⟩)
  ·
    set Γ := StatedSL 3 (ZMod 2) with hΓ
    let π : ↥Γ →* ↥L := π'.comp Γ.subtype
    have hπ : Function.Surjective π := by
      intro l
      obtain ⟨g, rfl⟩ := hπ's l
      exact ⟨⟨g, Subgroup.subset_closure (det_eq_one_GL32 g)⟩, rfl⟩
    refine ⟨ZMod 2, inferInstance, inferInstance, by rw [Nat.card_zmod]; norm_num, π, ?_⟩
    exact G64.realizesVia_nat_of hπ bot_le (fun _ _ _ => trivial) (fun h z hz => by
      rw [Subgroup.mem_bot] at hz ⊢
      rw [hz, map_one]) (f.toMonoidHom.comp (⊤ : Subgroup V).subtype)
      (fun x => ⟨⟨f.symm x, trivial⟩, by simp⟩)
      (fun u => by
        rw [Subgroup.mem_bot]
        simp only [MonoidHom.comp_apply, Subgroup.coe_subtype, MulEquiv.coe_toMonoidHom,
          MulEquivClass.map_eq_one_iff])
      (fun γ u _ => hf (γ : GL32) u)
  ·
    refine qOf_eq_of_offenders hV (s := 1 / 2) (by norm_num) (fun B hB => ?_) ?_
    · obtain ⟨-, hdata⟩ := l32_offender_data θ hirr eL (hoffL B hB)
      have hc : Nat.card ↥(fixV B) = 2 ^ Module.finrank (ZMod 2)
          ↥(LocalAnalysis.CommutingFactor.fixedSub (B.map (unitsPsi θ).toMonoidHom)) := by
        rw [← natCard_fixedSub_map θ, H13.NQTerm.card_eq_two_pow_finrank]
      rcases hdata with ⟨hk, hd⟩ | ⟨hk, hd | hd⟩ <;> rw [hd] at hc <;>
        rw [rAV_eq_of_card hV8 hk hc] <;> norm_num
    · obtain ⟨B₀, hB₀L, hB₀ne, hB₀el, hB₀rk, hB₀fix⟩ := exists_axis π' f hf
      have hA2 : IsA2 G B₀ := ⟨hB₀L.trans hGL.ge, hB₀ne, hB₀el⟩
      have hr : rAV B₀ = 1 / 2 := by
        rw [rAV_eq_of_card hV8 hB₀rk hB₀fix]
        norm_num
      obtain ⟨B, -, hB, hBr⟩ := exists_offender_rAV_le hV hA2 (by rw [hr]; norm_num)
      exact ⟨B, hB, hBr.trans hr.le⟩

end CFSG.Quasithin
