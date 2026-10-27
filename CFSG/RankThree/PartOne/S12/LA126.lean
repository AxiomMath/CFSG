module

public import CFSG.RankThree.PartOne.S12.Node126
public import CFSG.RankThree.PartOne.S12.LinAlg
public import CFSG.RankThree.PartOne.S12.LA126Aux
import CFSG.RankThree.PartOne.S12.LAFaithful
import CFSG.RankThree.PartOne.S12.LAMaschke
import CFSG.RankThree.PartOne.S12.OmegaFiveAlt
import CFSG.RankThree.SubgroupLists.DicksonGL2
import CFSG.Adapters.SpecialLinearPerfect

public section

namespace CFSG.RankThree.PartOne

namespace LA126

open Matrix
open CFSG.Assembly.LowTwoRank (StatedSL)
open CFSG.RankThree.SubgroupLists (omegaGL)
open CFSG.RepresentationTheory (IsIrreducibleMatrixRep)
open scoped commutatorElement

variable {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V] [Module (ZMod p) V]
  {Γ : Subgroup (V ≃ₗ[ZMod p] V)} {B : Submodule (ZMod p) V} {n : ℕ}

@[expose] def quotientKernel (B : Submodule (ZMod p) V) : Subgroup (V ≃ₗ[ZMod p] V) where
  carrier := {g | ∀ v, g v - v ∈ B}
  mul_mem' {a b} ha hb v := by
    have h := B.add_mem (ha (b v)) (hb v)
    rw [sub_add_sub_cancel] at h
    exact h
  one_mem' v := by simp
  inv_mem' {a} ha v := by
    have h := B.neg_mem (ha (a.symm v))
    rwa [LinearEquiv.apply_symm_apply, neg_sub] at h

theorem commutator_mem_quotientKernel {h g : V ≃ₗ[ZMod p] V} {lam : ZMod p}
    (hh : ∀ b ∈ B, h b ∈ B) (hlam : ∀ v, g v - lam • v ∈ B) :
    ⁅h, g⁆ ∈ quotientKernel B := by
  intro v
  have e1 : g (g⁻¹ v) = v := LinearEquiv.apply_symm_apply g v
  have e2 : h (h⁻¹ (g⁻¹ v)) = g⁻¹ v := LinearEquiv.apply_symm_apply h (g⁻¹ v)
  have e : ⁅h, g⁆ v - v =
      h (g (h⁻¹ (g⁻¹ v)) - lam • h⁻¹ (g⁻¹ v)) - (g (g⁻¹ v) - lam • g⁻¹ v) := by
    rw [map_sub, map_smul, e2, e1]
    show h (g (h⁻¹ (g⁻¹ v))) - v = _
    abel
  rw [e]
  exact B.sub_mem (hh _ (hlam _)) (hlam _)

theorem perfect_le_quotientKernel [Module.Finite (ZMod p) V]
    (hdim : Module.finrank (ZMod p) B + 1 = Module.finrank (ZMod p) V)
    (hinv : ∀ g ∈ Γ, ∀ b ∈ B, g b ∈ B) {Λ : Subgroup (V ≃ₗ[ZMod p] V)} (hΛ : Λ ≤ Γ)
    (hperf : Group.IsPerfect Λ) : Λ ≤ quotientKernel B := by
  rw [← Subgroup.commutator_eq_self (H := Λ)]
  refine Subgroup.commutator_le.2 fun a ha b hb => ?_
  obtain ⟨lam, hlam⟩ := LAFaithful.exists_scalar_of_stabilizes hdim (hinv b (hΛ hb))
  exact commutator_mem_quotientKernel (hinv a (hΛ ha)) hlam

@[expose] def restrictAut (hinv : ∀ g ∈ Γ, ∀ b ∈ B, g b ∈ B) : Γ →* (B ≃ₗ[ZMod p] B) where
  toFun g :=
    { toFun := fun b => ⟨(g : V ≃ₗ[ZMod p] V) b, hinv g g.2 b b.2⟩
      map_add' := fun _ _ => Subtype.ext (map_add _ _ _)
      map_smul' := fun _ _ => Subtype.ext (map_smul _ _ _)
      invFun := fun b => ⟨(g : V ≃ₗ[ZMod p] V)⁻¹ b, hinv _ (Γ.inv_mem g.2) b b.2⟩
      left_inv := fun _ => Subtype.ext (LinearEquiv.symm_apply_apply _ _)
      right_inv := fun _ => Subtype.ext (LinearEquiv.apply_symm_apply _ _) }
  map_one' := LinearEquiv.ext fun _ => rfl
  map_mul' _ _ := LinearEquiv.ext fun _ => Subtype.ext rfl

@[expose] def conjCoord (θ : B ≃ₗ[ZMod p] (Fin n → ZMod p)) :
    (B ≃ₗ[ZMod p] B) →* ((Fin n → ZMod p) ≃ₗ[ZMod p] (Fin n → ZMod p)) where
  toFun e := θ.symm.trans (e.trans θ)
  map_one' := LinearEquiv.ext fun w => by simp
  map_mul' e f := LinearEquiv.ext fun w => by simp

@[expose] noncomputable def coordRestrict (θ : B ≃ₗ[ZMod p] (Fin n → ZMod p))
    (hinv : ∀ g ∈ Γ, ∀ b ∈ B, g b ∈ B) : Γ →* GL (Fin n) (ZMod p) :=
  (LinAlg.toGL (p := p) (n := n)).toMonoidHom.comp ((conjCoord θ).comp (restrictAut hinv))

theorem coordRestrict_mulVec (θ : B ≃ₗ[ZMod p] (Fin n → ZMod p))
    (hinv : ∀ g ∈ Γ, ∀ b ∈ B, g b ∈ B) (g : Γ) (b : B) :
    (coordRestrict θ hinv g : Matrix (Fin n) (Fin n) (ZMod p)) *ᵥ θ b =
      θ ⟨(g : V ≃ₗ[ZMod p] V) b, hinv g g.2 b b.2⟩ := by
  rw [coordRestrict, MonoidHom.comp_apply, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    LinAlg.toGL_mulVec]
  show θ (restrictAut hinv g (θ.symm (θ b))) = _
  rw [LinearEquiv.symm_apply_apply]
  rfl

section Model

variable (θ : B ≃ₗ[ZMod p] (Fin n → ZMod p)) (hinv : ∀ g ∈ Γ, ∀ b ∈ B, g b ∈ B)

theorem coordRestrict_injective (hfaith : ∀ g ∈ Γ, (∀ b ∈ B, g b = b) → g = 1) :
    Function.Injective (coordRestrict θ hinv) := by
  refine (injective_iff_map_eq_one _).2 fun g hg => ?_
  refine Subtype.ext (hfaith g g.2 fun b hb => ?_)
  have h := coordRestrict_mulVec θ hinv g ⟨b, hb⟩
  rw [hg, Units.val_one, Matrix.one_mulVec] at h
  exact (congrArg Subtype.val (θ.injective h)).symm

theorem isIrreducibleMatrixRep_range
    (hirr : ∀ B' ≤ B, (∀ g ∈ Γ, ∀ b ∈ B', g b ∈ B') → B' = ⊥ ∨ B' = B) :
    IsIrreducibleMatrixRep (coordRestrict θ hinv).range.subtype := by
  intro W hW
  have hinvB : ∀ g ∈ Γ, ∀ x ∈ (W.comap θ.toLinearMap).map B.subtype,
      g x ∈ (W.comap θ.toLinearMap).map B.subtype := by
    intro g hg x hx
    obtain ⟨b, hb, rfl⟩ := Submodule.mem_map.1 hx
    refine Submodule.mem_map.2 ⟨⟨(g : V ≃ₗ[ZMod p] V) b, hinv g hg b b.2⟩, ?_, rfl⟩
    have h : ((coordRestrict θ hinv ⟨g, hg⟩ : GL (Fin n) (ZMod p)) :
        Matrix (Fin n) (Fin n) (ZMod p)) *ᵥ θ b ∈ W :=
      hW ⟨_, MonoidHom.mem_range.2 ⟨⟨g, hg⟩, rfl⟩⟩ (θ b) hb
    rwa [coordRestrict_mulVec] at h
  rcases hirr _ (Submodule.map_subtype_le B _) hinvB with h | h
  · left
    refine eq_bot_iff.2 fun w hw => ?_
    have hmem : ((θ.symm w : B) : V) ∈ (W.comap θ.toLinearMap).map B.subtype :=
      Submodule.mem_map.2 ⟨θ.symm w, by simpa using hw, rfl⟩
    rw [h, Submodule.mem_bot] at hmem
    have h0 : θ.symm w = 0 := Subtype.ext hmem
    rw [Submodule.mem_bot]
    simpa using congrArg θ h0
  · right
    refine eq_top_iff.2 fun w _ => ?_
    have hw : ((θ.symm w : B) : V) ∈ (W.comap θ.toLinearMap).map B.subtype := by
      rw [h]
      exact (θ.symm w).2
    obtain ⟨b, hb, hbe⟩ := Submodule.mem_map.1 hw
    have hb' : b = θ.symm w := Subtype.ext hbe
    rw [hb'] at hb
    simpa using hb

theorem pCore_range_eq_bot (hfaith : ∀ g ∈ Γ, (∀ b ∈ B, g b = b) → g = 1)
    (hcore : CFSG.pCore p Γ = ⊥) : CFSG.pCore p (coordRestrict θ hinv).range = ⊥ :=
  (LinAlg.pCore_eq_bot_iff_of_mulEquiv p
    (MonoidHom.ofInjective (coordRestrict_injective θ hinv hfaith))).1 hcore

theorem natCard_range (hfaith : ∀ g ∈ Γ, (∀ b ∈ B, g b = b) → g = 1) :
    Nat.card (coordRestrict θ hinv).range = Nat.card Γ :=
  (Nat.card_congr (MonoidHom.ofInjective (coordRestrict_injective θ hinv hfaith)).toEquiv).symm

theorem exists_normal_lift (hfaith : ∀ g ∈ Γ, (∀ b ∈ B, g b = b) → g = 1)
    (H : Subgroup (GL (Fin n) (ZMod p))) (hH : H ≤ (coordRestrict θ hinv).range)
    (hHn : ∀ g ∈ (coordRestrict θ hinv).range, ∀ x ∈ H, g * x * g⁻¹ ∈ H) :
    ∃ ρ : H →* (V ≃ₗ[ZMod p] V), Function.Injective ρ ∧ (∀ y, ρ y ∈ Γ) ∧
      (∀ g ∈ Γ, ∀ x ∈ ρ.range, g * x * g⁻¹ ∈ ρ.range) ∧
      (∀ (y : H) (b : B), ρ y (b : V) =
        ((θ.symm (((y : GL (Fin n) (ZMod p)) : Matrix (Fin n) (Fin n) (ZMod p)) *ᵥ θ b) : B) :
          V)) ∧
      (∀ x : Γ, coordRestrict θ hinv x ∈ H → (x : V ≃ₗ[ZMod p] V) ∈ ρ.range) := by
  have hinj := coordRestrict_injective θ hinv hfaith
  let e : Γ ≃* (coordRestrict θ hinv).range := MonoidHom.ofInjective hinj
  let γ : H →* Γ :=
    (e.symm : (coordRestrict θ hinv).range ≃* Γ).toMonoidHom.comp (Subgroup.inclusion hH)
  have hγ : ∀ y : H, coordRestrict θ hinv (γ y) = y := by
    intro y
    have h := e.apply_symm_apply (Subgroup.inclusion hH y)
    exact congrArg Subtype.val h
  refine ⟨Γ.subtype.comp γ, ?_, ?_, ?_, ?_, ?_⟩
  · intro y y' h
    have h1 : γ y = γ y' := Subtype.ext h
    apply Subtype.ext
    rw [← hγ y, ← hγ y', h1]
  · exact fun y => (γ y).2
  · rintro g hg _ ⟨y, rfl⟩
    have hyH : coordRestrict θ hinv ⟨g, hg⟩ * y * (coordRestrict θ hinv ⟨g, hg⟩)⁻¹ ∈ H :=
      hHn _ (MonoidHom.mem_range.2 ⟨⟨g, hg⟩, rfl⟩) y y.2
    refine ⟨⟨_, hyH⟩, ?_⟩
    have h : γ ⟨_, hyH⟩ = ⟨g, hg⟩ * γ y * ⟨g, hg⟩⁻¹ := by
      apply hinj
      rw [hγ, map_mul, map_mul, map_inv, hγ]
    exact congrArg Subtype.val h
  · intro y b
    have h := coordRestrict_mulVec θ hinv (γ y) b
    rw [hγ y] at h
    rw [h, LinearEquiv.symm_apply_apply]
    rfl
  · intro x hx
    refine ⟨⟨coordRestrict θ hinv x, hx⟩, ?_⟩
    have h : γ ⟨coordRestrict θ hinv x, hx⟩ = x := hinj (hγ _)
    exact congrArg Subtype.val h

theorem false_of_fixed_vector [Module.Finite (ZMod p) V]
    (hdim : Module.finrank (ZMod p) B + 1 = Module.finrank (ZMod p) V)
    (hfaith : ∀ g ∈ Γ, (∀ b ∈ B, g b = b) → g = 1)
    (hirr : ∀ B' ≤ B, (∀ g ∈ Γ, ∀ b ∈ B', g b ∈ B') → B' = ⊥ ∨ B' = B)
    (hnoline : ¬ ∃ ℓ : Submodule (ZMod p) V, Module.finrank (ZMod p) ℓ = 1 ∧ Disjoint ℓ B ∧
      ∀ g ∈ Γ, ∀ x ∈ ℓ, g x ∈ ℓ)
    (H : Subgroup (GL (Fin n) (ZMod p))) (hH : H ≤ (coordRestrict θ hinv).range)
    (hHn : ∀ g ∈ (coordRestrict θ hinv).range, ∀ x ∈ H, g * x * g⁻¹ ∈ H)
    (hperf : Group.IsPerfect H) (hne : H ≠ ⊥)
    (hjp : ∀ ρ : H →* (V ≃ₗ[ZMod p] V),
      (∀ (y : H) (b : B), ρ y (b : V) =
        ((θ.symm (((y : GL (Fin n) (ZMod p)) : Matrix (Fin n) (Fin n) (ZMod p)) *ᵥ θ b) : B) :
          V)) →
      (∀ (y : H) (v : V), ρ y v - v ∈ B) → ∃ v : V, v ∉ B ∧ ∀ y : H, ρ y v = v) :
    False := by
  obtain ⟨ρ, hρinj, hρΓ, hρnorm, hρnat, -⟩ := exists_normal_lift θ hinv hfaith H hH hHn
  have hperfY : Group.IsPerfect ρ.range := Group.IsPerfect.range ρ
  have hYΓ : ρ.range ≤ Γ := by
    rintro _ ⟨y, rfl⟩
    exact hρΓ y
  have htriv : ∀ (y : H) (v : V), ρ y v - v ∈ B := fun y v =>
    perfect_le_quotientKernel hdim hinv hYΓ hperfY (MonoidHom.mem_range.2 ⟨y, rfl⟩) v
  obtain ⟨v, hvB, hv⟩ := hjp ρ hρnat htriv
  have hY1 : ρ.range ≠ ⊥ := by
    obtain ⟨y, hy⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hne
    refine Subgroup.ne_bot_iff_exists_ne_one.2
      ⟨⟨ρ y, MonoidHom.mem_range.2 ⟨y, rfl⟩⟩, fun h => hy ?_⟩
    apply hρinj
    rw [map_one]
    exact congrArg Subtype.val h
  exact hnoline (exists_invariant_line_of_fixed Γ B hdim hinv hfaith hirr ρ.range hYΓ hρnorm hY1
    v hvB (by
      rintro _ ⟨y, rfl⟩
      exact hv y))

end Model

theorem statedSL_two_ne_bot : StatedSL 2 (ZMod p) ≠ ⊥ := by
  refine Subgroup.ne_bot_iff_exists_ne_one.2
    ⟨⟨CFSG.RankThree.SubgroupLists.upperGL 1, ?_⟩, fun h => ?_⟩
  · rw [CFSG.RankThree.SubgroupLists.mem_statedSL_iff,
      CFSG.RankThree.SubgroupLists.coe_upperGL]
    simp [Matrix.det_fin_two]
  · have h' : CFSG.RankThree.SubgroupLists.upperGL (1 : ZMod p) = 1 := congrArg Subtype.val h
    have h2 := congrArg
      (fun g : GL (Fin 2) (ZMod p) => (g : Matrix (Fin 2) (Fin 2) (ZMod p)) 0 1) h'
    simp [CFSG.RankThree.SubgroupLists.coe_upperGL] at h2

theorem isPerfect_statedSL_two (hp5 : 5 ≤ p) : Group.IsPerfect (StatedSL 2 (ZMod p)) := by
  have h : Group.IsPerfect (SpecialLinearGroup (Fin 2) (ZMod p)) :=
    CFSG.ClassicalModels.specialLinear_isPerfect_two_of_four_le_card (ZMod p)
      (by rw [Nat.card_zmod]; omega)
  exact Group.IsPerfect.ofSurjective
    (f := (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 2 (ZMod p) :
      SpecialLinearGroup (Fin 2) (ZMod p) →* StatedSL 2 (ZMod p))) (MulEquiv.surjective _)

theorem false_of_finrank_two (hD : ExtDickson) (hJP : ExtJonesParshall) (hp5 : 5 ≤ p)
    [Module.Finite (ZMod p) V]
    (hdim : Module.finrank (ZMod p) B + 1 = Module.finrank (ZMod p) V)
    (hB2 : Module.finrank (ZMod p) B = 2) (hinv : ∀ g ∈ Γ, ∀ b ∈ B, g b ∈ B)
    (hcore : CFSG.pCore p Γ = ⊥) (hfaith : ∀ g ∈ Γ, (∀ b ∈ B, g b = b) → g = 1)
    (hirr : ∀ B' ≤ B, (∀ g ∈ Γ, ∀ b ∈ B', g b ∈ B') → B' = ⊥ ∨ B' = B)
    (hnoline : ¬ ∃ ℓ : Submodule (ZMod p) V, Module.finrank (ZMod p) ℓ = 1 ∧ Disjoint ℓ B ∧
      ∀ g ∈ Γ, ∀ x ∈ ℓ, g x ∈ ℓ)
    (hpΓ : p ∣ Nat.card Γ) : False := by
  let θ : B ≃ₗ[ZMod p] (Fin 2 → ZMod p) :=
    LinearEquiv.ofFinrankEq B (Fin 2 → ZMod p) (by simp [hB2])
  have hpG : p ∣ Nat.card (coordRestrict θ hinv).range := by
    rw [natCard_range θ hinv hfaith]
    exact hpΓ
  have hcoreG := pCore_range_eq_bot θ hinv hfaith hcore
  rcases hD p _ hpG with ⟨P, hPn, hPcard⟩ | hSL
  · have hle : (P : Subgroup (coordRestrict θ hinv).range) ≤
        CFSG.pCore p (coordRestrict θ hinv).range := le_sSup ⟨hPn, P.isPGroup'⟩
    rw [hcoreG, le_bot_iff] at hle
    have h1 : Nat.card (P : Subgroup (coordRestrict θ hinv).range) = 1 := by
      rw [hle]
      exact Subgroup.card_bot
    have h2 : p = 1 := hPcard.symm.trans h1
    omega
  · exact false_of_fixed_vector θ hinv hdim hfaith hirr hnoline (StatedSL 2 (ZMod p)) hSL
      (fun g _ x hx => (inferInstance : (StatedSL 2 (ZMod p)).Normal).conj_mem x hx g)
      (isPerfect_statedSL_two hp5) statedSL_two_ne_bot
      (fun ρ hnat htriv => hJP.1 p hp5 V B 2 (Or.inl rfl) θ ρ hdim hnat htriv)

theorem ne_bot_of_isIrreducibleMatrixRep (H : Subgroup (GL (Fin 3) (ZMod p)))
    (hirr : IsIrreducibleMatrixRep H.subtype) : H ≠ ⊥ := by
  intro hbot
  have hinvW : ∀ (g : H) (w : Fin 3 → ZMod p),
      w ∈ Submodule.span (ZMod p) {(Pi.single (0 : Fin 3) 1 : Fin 3 → ZMod p)} →
      ((H.subtype g : GL (Fin 3) (ZMod p)) : Matrix (Fin 3) (Fin 3) (ZMod p)) *ᵥ w ∈
        Submodule.span (ZMod p) {(Pi.single (0 : Fin 3) 1 : Fin 3 → ZMod p)} := by
    intro g w hw
    have hg : (g : GL (Fin 3) (ZMod p)) = 1 := (Subgroup.eq_bot_iff_forall H).1 hbot _ g.2
    rw [Subgroup.coe_subtype, hg, Units.val_one, Matrix.one_mulVec]
    exact hw
  rcases hirr _ hinvW with h | h
  · have h0 : (Pi.single (0 : Fin 3) 1 : Fin 3 → ZMod p) ∈
        Submodule.span (ZMod p) {(Pi.single (0 : Fin 3) 1 : Fin 3 → ZMod p)} :=
      Submodule.subset_span (Set.mem_singleton _)
    rw [h, Submodule.mem_bot] at h0
    have h1 := congrFun h0 0
    simp at h1
  · have h1 : (Pi.single (1 : Fin 3) 1 : Fin 3 → ZMod p) ∈
        Submodule.span (ZMod p) {(Pi.single (0 : Fin 3) 1 : Fin 3 → ZMod p)} := by
      rw [h]
      exact Submodule.mem_top
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 h1
    have h2 := congrFun hc 1
    simp at h2

theorem coordRestrict_commute (θ : B ≃ₗ[ZMod p] (Fin n → ZMod p))
    (hinv : ∀ g ∈ Γ, ∀ b ∈ B, g b ∈ B) (g : Γ) {r : V ≃ₗ[ZMod p] V}
    (h : GL (Fin n) (ZMod p)) (hrB : ∀ b ∈ B, r b ∈ B)
    (hr : ∀ b : B, r (b : V) =
      ((θ.symm (((h : GL (Fin n) (ZMod p)) : Matrix (Fin n) (Fin n) (ZMod p)) *ᵥ θ b) : B) : V))
    (hcomm : (g : V ≃ₗ[ZMod p] V) * r = r * (g : V ≃ₗ[ZMod p] V)) :
    ((coordRestrict θ hinv g : GL (Fin n) (ZMod p)) : Matrix (Fin n) (Fin n) (ZMod p)) *
        (h : Matrix (Fin n) (Fin n) (ZMod p)) =
      (h : Matrix (Fin n) (Fin n) (ZMod p)) *
        ((coordRestrict θ hinv g : GL (Fin n) (ZMod p)) : Matrix (Fin n) (Fin n) (ZMod p)) := by
  have hθ : ∀ b : B, ((h : GL (Fin n) (ZMod p)) : Matrix (Fin n) (Fin n) (ZMod p)) *ᵥ θ b =
      θ ⟨r (b : V), hrB b b.2⟩ := fun b => by
    have h1 : (⟨r (b : V), hrB b b.2⟩ : B) =
        θ.symm (((h : GL (Fin n) (ZMod p)) : Matrix (Fin n) (Fin n) (ZMod p)) *ᵥ θ b) :=
      Subtype.ext (hr b)
    rw [h1, LinearEquiv.apply_symm_apply]
  have key : ∀ w : Fin n → ZMod p,
      (((coordRestrict θ hinv g : GL (Fin n) (ZMod p)) : Matrix (Fin n) (Fin n) (ZMod p)) *
          (h : Matrix (Fin n) (Fin n) (ZMod p))) *ᵥ w =
        ((h : Matrix (Fin n) (Fin n) (ZMod p)) *
          ((coordRestrict θ hinv g : GL (Fin n) (ZMod p)) : Matrix (Fin n) (Fin n) (ZMod p))) *ᵥ
            w := by
    intro w
    obtain ⟨b, rfl⟩ := θ.surjective w
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hθ b,
      coordRestrict_mulVec θ hinv g ⟨r (b : V), hrB b b.2⟩, coordRestrict_mulVec θ hinv g b,
      hθ ⟨(g : V ≃ₗ[ZMod p] V) b, hinv g g.2 b b.2⟩]
    congr 1
    apply Subtype.ext
    have := congrArg (fun t : V ≃ₗ[ZMod p] V => t (b : V)) hcomm
    simpa using this
  ext i j
  have := congrFun (key (Pi.single j 1)) i
  simpa [Matrix.mulVec_single_one] using this

theorem exists_normal_of_omega_five (hK : KF126) (hp : p = 5)
    (θ : B ≃ₗ[ZMod p] (Fin 3 → ZMod p)) (hinv : ∀ g ∈ Γ, ∀ b ∈ B, g b ∈ B)
    (hfaith : ∀ g ∈ Γ, (∀ b ∈ B, g b = b) → g = 1) (M : Matrix (Fin 3) (Fin 3) (ZMod p))
    (hMt : Mᵀ = M) (hMdet : M.det ≠ 0) (hH : omegaGL M ≤ (coordRestrict θ hinv).range)
    (hHn : ∀ g ∈ (coordRestrict θ hinv).range, ∀ x ∈ omegaGL M, g * x * g⁻¹ ∈ omegaGL M)
    (hHperf : Group.IsPerfect (omegaGL M))
    (hHirr : IsIrreducibleMatrixRep (omegaGL M).subtype) :
    ∃ Y : Subgroup (V ≃ₗ[ZMod p] V), Y ≤ Γ ∧ (∀ g ∈ Γ, ∀ y ∈ Y, g * y * g⁻¹ ∈ Y) ∧
      Nat.card Y = 60 ∧
      (∀ Λ : Subgroup (V ≃ₗ[ZMod p] V), Λ ≤ Γ → Group.IsPerfect Λ → Λ ≤ Y) ∧
      Group.IsPerfect Y ∧ Nonempty (Y ≃* alternatingGroup (Fin 5)) ∧
      ∀ g ∈ Γ, (∀ y ∈ Y, g * y = y * g) → ∃ c : ZMod p, ∀ b ∈ B, g b = c • b := by
  subst hp
  obtain ⟨ρ, hρinj, hρΓ, hρnorm, hρnat, hρmem⟩ :=
    exists_normal_lift θ hinv hfaith (omegaGL M) hH hHn
  obtain ⟨e⟩ := OmegaAlt.omegaGL_equiv_alternating M hMt hMdet
  refine ⟨ρ.range, ?_, hρnorm, ?_, ?_, Group.IsPerfect.range ρ,
    ⟨(MonoidHom.ofInjective hρinj).symm.trans e⟩, ?_⟩
  · rintro _ ⟨y, rfl⟩
    exact hρΓ y
  · have h : Nat.card ρ.range = Nat.card (omegaGL M) :=
      Nat.card_congr (MonoidHom.ofInjective hρinj).toEquiv.symm
    rw [h]
    exact (hK M hMt hMdet).1
  · intro Λ hΛ hperf
    let f : Λ →* GL (Fin 3) (ZMod 5) := (coordRestrict θ hinv).comp (Subgroup.inclusion hΛ)
    have hperf' : Group.IsPerfect f.range := Group.IsPerfect.range f
    have hle : f.range ≤ omegaGL M := by
      refine (hK M hMt hMdet).2 f.range ?_ hperf'
      rintro _ ⟨l, rfl⟩
      have hxG : f l ∈ (coordRestrict θ hinv).range := ⟨⟨l.1, hΛ l.2⟩, rfl⟩
      refine Subgroup.mem_set_normalizer_iff.2 fun h => ⟨fun hh => hHn _ hxG h hh, fun hh => ?_⟩
      have h' := hHn _ ((coordRestrict θ hinv).range.inv_mem hxG) _ hh
      simpa [mul_assoc] using h'
    intro x hx
    exact hρmem ⟨x, hΛ hx⟩ (hle ⟨⟨x, hx⟩, rfl⟩)
  · intro g hg hcomm
    have hnc : ¬ IsCyclic (omegaGL M) := OmegaAlt.not_isCyclic_of_equiv_alternating e
    rcases CFSG.RankThree.SubgroupLists.scalar_commutant_or_cyclic Nat.prime_three hHirr with
      hs | ⟨hc, -⟩
    · obtain ⟨c, hc⟩ := hs
        ((coordRestrict θ hinv ⟨g, hg⟩ : GL (Fin 3) (ZMod 5)) : Matrix (Fin 3) (Fin 3) (ZMod 5))
        (fun h hh => (coordRestrict_commute θ hinv ⟨g, hg⟩ h (hinv _ (hρΓ ⟨h, hh⟩))
          (hρnat ⟨h, hh⟩) (hcomm _ ⟨⟨h, hh⟩, rfl⟩)).symm)
      refine ⟨c, fun b hb => ?_⟩
      have h1 := coordRestrict_mulVec θ hinv ⟨g, hg⟩ ⟨b, hb⟩
      rw [hc, CFSG.RankThree.SubgroupLists.scalar_mulVec_eq_smul] at h1
      have h2 : (⟨g b, hinv g hg b hb⟩ : B) = c • (⟨b, hb⟩ : B) :=
        θ.injective (by rw [← h1, map_smul])
      exact congrArg Subtype.val h2
    · exact (hnc hc).elim

theorem exists_normal_of_finrank_three (hB : ExtBloomPrime) (hJP : ExtJonesParshall)
    (hK : KF126) (hp5 : 5 ≤ p) [Module.Finite (ZMod p) V]
    (hdim : Module.finrank (ZMod p) B + 1 = Module.finrank (ZMod p) V)
    (hB3 : Module.finrank (ZMod p) B = 3) (hinv : ∀ g ∈ Γ, ∀ b ∈ B, g b ∈ B)
    (hfaith : ∀ g ∈ Γ, (∀ b ∈ B, g b = b) → g = 1)
    (hirr : ∀ B' ≤ B, (∀ g ∈ Γ, ∀ b ∈ B', g b ∈ B') → B' = ⊥ ∨ B' = B)
    (hnoline : ¬ ∃ ℓ : Submodule (ZMod p) V, Module.finrank (ZMod p) ℓ = 1 ∧ Disjoint ℓ B ∧
      ∀ g ∈ Γ, ∀ x ∈ ℓ, g x ∈ ℓ)
    (hpΓ : p ∣ Nat.card Γ) :
    p = 5 ∧ ∃ Y : Subgroup (V ≃ₗ[ZMod p] V), Y ≤ Γ ∧ (∀ g ∈ Γ, ∀ y ∈ Y, g * y * g⁻¹ ∈ Y) ∧
      Nat.card Y = 60 ∧
      (∀ Λ : Subgroup (V ≃ₗ[ZMod p] V), Λ ≤ Γ → Group.IsPerfect Λ → Λ ≤ Y) ∧
      Group.IsPerfect Y ∧ Nonempty (Y ≃* alternatingGroup (Fin 5)) ∧
      ∀ g ∈ Γ, (∀ y ∈ Y, g * y = y * g) → ∃ c : ZMod p, ∀ b ∈ B, g b = c • b := by
  let θ : B ≃ₗ[ZMod p] (Fin 3 → ZMod p) :=
    LinearEquiv.ofFinrankEq B (Fin 3 → ZMod p) (by simp [hB3])
  have hpG : p ∣ Nat.card (coordRestrict θ hinv).range := by
    rw [natCard_range θ hinv hfaith]
    exact hpΓ
  obtain ⟨H, hHG, hHn, hHirr, hHperf, hcases⟩ :=
    hB p hp5 (isIrreducibleMatrixRep_range θ hinv hirr) hpG
  have hne : H ≠ ⊥ := ne_bot_of_isIrreducibleMatrixRep H hHirr
  rcases hcases with rfl | ⟨M, hMt, hMdet, rfl⟩
  · exact (false_of_fixed_vector θ hinv hdim hfaith hirr hnoline _ hHG hHn hHperf hne
      (fun ρ hnat htriv => hJP.1 p hp5 V B 3 (Or.inr rfl) θ ρ hdim hnat htriv)).elim
  · by_cases hp : p = 5
    · exact ⟨hp, exists_normal_of_omega_five hK hp θ hinv hfaith M hMt hMdet hHG hHn hHperf hHirr⟩
    · exact (false_of_fixed_vector θ hinv hdim hfaith hirr hnoline _ hHG hHn hHperf hne
        (fun ρ hnat htriv => hJP.2 p hp5 hp V B M hMt hMdet θ ρ hdim hnat htriv)).elim

end LA126

theorem la126 : LA126 := by
  intro hD hB hJP hK p _ hp5 V _ _ _ Γ B hdim hn hinv hcore hfaith hirr hnoline
  have hpΓ : p ∣ Nat.card Γ := by
    by_contra hnd
    obtain ⟨C, hC, hCinv⟩ := exists_invariant_compl_of_not_dvd Γ hnd B hinv
    refine hnoline ⟨C, ?_, hC.disjoint.symm, hCinv⟩
    have h := Submodule.finrank_add_eq_of_isCompl hC
    omega
  rcases hn with h2 | h3
  · exact (LA126.false_of_finrank_two hD hJP hp5 hdim h2 hinv hcore hfaith hirr hnoline hpΓ).elim
  · obtain ⟨hp, hY⟩ :=
      LA126.exists_normal_of_finrank_three hB hJP hK hp5 hdim h3 hinv hfaith hirr hnoline hpΓ
    exact ⟨hp, h3, hY⟩

end CFSG.RankThree.PartOne
