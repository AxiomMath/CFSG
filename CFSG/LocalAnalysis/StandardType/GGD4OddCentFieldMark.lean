module

public import CFSG.LocalAnalysis.StandardType.GGD4OddCentVocab
public import CFSG.Assembly.Subnormal

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

section Recipe

abbrev D4Recipe (K : Type) [Field K] : Type :=
  LargeEvenProj (LargeEvenOmega (LargeEvenQPlus K 4))

abbrev D4FieldSet (K : Type) [Field K] : Set (MulAut (D4Recipe K)) :=
  LargeEvenMatFieldImage (LargeEvenProjMk (LargeEvenOmega (LargeEvenQPlus K 4)))

end Recipe

section CenterBot

variable {X : Type*} {R : Type} [Group X] [Group R]

@[expose] def markIso (e : X ≃* R) (h : Subgroup.center X = ⊥) :
    X ⧸ Subgroup.center X ≃* R :=
  ((QuotientGroup.quotientMulEquivOfEq h).trans QuotientGroup.quotientBot).trans e

theorem markIso_mk (e : X ≃* R) (h : Subgroup.center X = ⊥) (x : X) :
    markIso e h (x : X ⧸ Subgroup.center X) = e x := by
  rfl

@[expose] def mulEquivOfCenterBot (θ : X ⧸ Subgroup.center X ≃* R)
    (h : Subgroup.center X = ⊥) : X ≃* R :=
  (QuotientGroup.quotientBot.symm.trans (QuotientGroup.quotientMulEquivOfEq h.symm)).trans θ

theorem mulEquivOfCenterBot_apply (θ : X ⧸ Subgroup.center X ≃* R) (h : Subgroup.center X = ⊥)
    (x : X) : mulEquivOfCenterBot θ h x = θ (x : X ⧸ Subgroup.center X) := by
  rfl

theorem ggInducedAut_mulEquivOfCenterBot (θ : X ⧸ Subgroup.center X ≃* R)
    (h : Subgroup.center X = ⊥) (a : MulAut X) (x : X) :
    ggInducedAut θ a (mulEquivOfCenterBot θ h x) = mulEquivOfCenterBot θ h (a x) := by
  simp only [mulEquivOfCenterBot_apply, ggInducedAut_apply]

theorem ggAutFixedSubgroup_ggInducedAut (θ : X ⧸ Subgroup.center X ≃* R)
    (h : Subgroup.center X = ⊥) (a : MulAut X) :
    ggAutFixedSubgroup (ggInducedAut θ a) =
      (ggAutFixedSubgroup a).map (mulEquivOfCenterBot θ h).toMonoidHom := by
  ext r
  rw [Subgroup.mem_map, mem_ggAutFixedSubgroup]
  constructor
  · intro hr
    refine ⟨(mulEquivOfCenterBot θ h).symm r, ?_,
      (mulEquivOfCenterBot θ h).apply_symm_apply r⟩
    have h2 : (mulEquivOfCenterBot θ h) (a ((mulEquivOfCenterBot θ h).symm r)) =
        (mulEquivOfCenterBot θ h) ((mulEquivOfCenterBot θ h).symm r) := by
      calc (mulEquivOfCenterBot θ h) (a ((mulEquivOfCenterBot θ h).symm r))
          = ggInducedAut θ a
              ((mulEquivOfCenterBot θ h) ((mulEquivOfCenterBot θ h).symm r)) :=
            (ggInducedAut_mulEquivOfCenterBot θ h a _).symm
        _ = ggInducedAut θ a r := by rw [MulEquiv.apply_symm_apply]
        _ = r := hr
        _ = (mulEquivOfCenterBot θ h) ((mulEquivOfCenterBot θ h).symm r) :=
            (MulEquiv.apply_symm_apply _ _).symm
    exact (mulEquivOfCenterBot θ h).injective h2
  · rintro ⟨x, hx, hxr⟩
    rw [← hxr]
    calc ggInducedAut θ a ((mulEquivOfCenterBot θ h) x)
        = (mulEquivOfCenterBot θ h) (a x) := ggInducedAut_mulEquivOfCenterBot θ h a x
      _ = (mulEquivOfCenterBot θ h) x := by rw [hx]

end CenterBot

section Component

theorem isComponentOf_map_mulEquiv {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y)
    {J H : Subgroup X} (h : IsComponentOf J H) :
    IsComponentOf (J.map e.toMonoidHom) (H.map e.toMonoidHom) := by
  refine ⟨Subgroup.map_mono h.1, IsSubnormal.map e.toMonoidHom h.2.1, ?_⟩
  exact Assembly.IsQuasisimple.of_mulEquiv
    (Subgroup.equivMapOfInjective J e.toMonoidHom e.injective).symm h.2.2

end Component

section Marking

theorem largeEvenMarking_D4_of_mulEquiv {X : Type} [Group X] (hX : commutator X = ⊤)
    {K : Type} [Field K] [Finite K] {n : ℕ} (hn : 1 ≤ n) (hK : Nat.card K = 2 ^ n)
    (f : X ≃* D4Recipe K) (hs : IsSimpleGroup (D4Recipe K))
    (hna : ∃ a b : D4Recipe K, a * b ≠ b * a) {P : LargeEvenMarkProp X}
    (hP : ∀ hZ : Subgroup.center X = ⊥,
      P ⟨.D, 4, n⟩ (D4Recipe K) (LargeEvenInnSet (D4Recipe K)) (D4FieldSet K) (markIso f hZ)) :
    LargeEvenMarking X P := by
  haveI : IsSimpleGroup (D4Recipe K) := hs
  have hZ : Subgroup.center X = ⊥ :=
    center_eq_bot_of_mulEquiv f (center_eq_bot_of_simple_nonabelian hna)
  refine ⟨hX, ⟨.D, 4, n⟩, ⟨hn, by norm_num⟩, ?_⟩
  change LargeEvenRecipeOmegaPlus 4 (2 ^ n)
    (fun R _ I F => IsSimpleGroup R ∧ (∃ a b : R, a * b ≠ b * a) ∧
      ∃ θ : X ⧸ Subgroup.center X ≃* R, P ⟨.D, 4, n⟩ R I F θ)
  exact ⟨K, inferInstance, inferInstance, hK, hs, hna, markIso f hZ, hP hZ⟩

theorem not_ggAutsInduceOn_of_outer {X : Type*} [Group X] {A : Subgroup (MulAut X)}
    {J : Subgroup X} {R : Type} [Group R] (f : ↥J ≃* R) (hZ : Subgroup.center ↥J = ⊥)
    {a : MulAut X} (haA : a ∈ A) (hinv : ∀ x ∈ J, a x ∈ J)
    (hout : ¬ ∃ j ∈ J, ∀ x ∈ J, a x = j * x * j⁻¹) :
    ¬ GGAutsInduceOn A J (markIso f hZ) (LargeEvenInnSet R) := by
  intro h
  obtain ⟨φ, hφ, hind⟩ := h a haA
  rw [LargeEvenInnSet] at hφ
  obtain ⟨r, rfl⟩ := hφ
  apply hout
  refine ⟨((f.symm r : ↥J) : X), (f.symm r).2, ?_⟩
  intro x hx
  have h1 := hind ⟨x, hx⟩ ⟨a x, hinv x hx⟩ rfl
  simp only [MulAut.conj_apply] at h1
  rw [markIso_mk, markIso_mk] at h1
  have key : (⟨a x, hinv x hx⟩ : ↥J) = f.symm r * ⟨x, hx⟩ * (f.symm r)⁻¹ := by
    apply f.injective
    rw [map_mul, map_mul, map_inv]
    rw [show f (f.symm r) = r from MulEquiv.apply_symm_apply f r]
    exact h1.symm
  simpa using congrArg Subtype.val key

end Marking

end CFSG.StandardType
