module

public import CFSG.Quasithin.Background.G10FifteenNondegB
public import CFSG.Quasithin.Background.G10FifteenInputs
public import CFSG.Quasithin.Background.G10FifteenNondegA

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

namespace G11

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V]

namespace G108Hyp

variable [Finite V] {B : LinearMap.BilinForm (ZMod 2) V} {Γ : Subgroup (GLV V)} {v₁ : V}
  {W : Submodule (ZMod 2) V} {X X₀ L : Subgroup (GLV V)} (hyp : G108Hyp B Γ v₁ W X X₀ L)

include hyp

theorem restrictRange_normalizes {I : Submodule (ZMod 2) V}
    (hI : Invariant (normalClosure Γ L) I) :
    restrictRange (stabilizerOf X I) I (invariant_stabilizerOf X I) ≤
      Subgroup.normalizer ((restrictRange (normalClosure Γ L) I hI : Subgroup (GLV ↥I)) :
        Set (GLV ↥I)) := by
  have key : ∀ q ∈ restrictRange (stabilizerOf X I) I (invariant_stabilizerOf X I),
      ∀ k ∈ restrictRange (normalClosure Γ L) I hI,
      q * k * q⁻¹ ∈ restrictRange (normalClosure Γ L) I hI := by
    rintro q ⟨⟨y, hy⟩, rfl⟩ k ⟨⟨h, hh⟩, rfl⟩
    have hyΓ : y ∈ Γ := hyp.X_le hy.1
    have hyh : y * h * y⁻¹ ∈ normalClosure Γ L := normalClosure_normal Γ L y hyΓ h hh
    refine ⟨⟨y * h * y⁻¹, hyh⟩, ?_⟩
    apply LinearEquiv.ext
    intro u
    apply Subtype.ext
    have hinv : (restrictHom (stabilizerOf X I) I (invariant_stabilizerOf X I) ⟨y, hy⟩)⁻¹ =
        restrictHom (stabilizerOf X I) I (invariant_stabilizerOf X I) ⟨y, hy⟩⁻¹ :=
      (map_inv _ _).symm
    rw [hinv]
    rfl
  intro q hq
  rw [Subgroup.mem_normalizer_iff]
  intro k
  constructor
  · intro hk
    exact key q hq k hk
  · intro hk
    have hq' : q⁻¹ ∈ restrictRange (stabilizerOf X I) I (invariant_stabilizerOf X I) :=
      Subgroup.inv_mem _ hq
    have := key q⁻¹ hq' _ hk
    simpa [mul_assoc] using this


theorem apply_h1212 (h1212 : G1212Stmt) {I : Submodule (ZMod 2) V}
    (hI : IrrPlus (normalClosure Γ L) I) {i : V} (hi : i ∈ I ⊓ perp B v₁) (hi0 : i ≠ 0)
    (hFT : FullTransvections (stabilizerOf X I) (I ⊓ perp B v₁) i hi)
    (hnd : NondegOn B I) (hnle : ¬ I ≤ perp B v₁) :
    ∃ f : LinearMap.BilinForm (ZMod 2) ↥I,
      G121Data f (restrictRange (normalClosure Γ L) I hI.1 ⊔
          restrictRange (stabilizerOf X I) I (invariant_stabilizerOf X I))
        (restrictRange (normalClosure Γ L) I hI.1)
        (restrictRange (stabilizerOf X I) I (invariant_stabilizerOf X I)) ⟨i, hi.1⟩ := by
  have hYI := invariant_stabilizerOf X I
  have hirr : IsIrr (normalClosure Γ L) I := hI.isIrr hyp.fixedSpace_H
  have : Group.IsPerfect ↥(normalClosure Γ L) :=
    isPerfect_normalClosure ⟨hyp.component.2.2.1⟩
  have hrefl := hyp.toG101Hyp.isRefl
  have hMnorm : ∀ m ∈ restrictRange (normalClosure Γ L) I hI.1 ⊔
      restrictRange (stabilizerOf X I) I hYI, ∀ k ∈ restrictRange (normalClosure Γ L) I hI.1,
      m * k * m⁻¹ ∈ restrictRange (normalClosure Γ L) I hI.1 := by
    intro m hm k hk
    have hle : restrictRange (normalClosure Γ L) I hI.1 ⊔ restrictRange (stabilizerOf X I) I hYI ≤
        Subgroup.normalizer ((restrictRange (normalClosure Γ L) I hI.1 : Subgroup (GLV ↥I)) :
          Set (GLV ↥I)) :=
      sup_le Subgroup.le_normalizer (hyp.restrictRange_normalizes hI.1)
    exact ((Subgroup.mem_normalizer_iff.1 (hle hm)) k).1 hk
  have hQcomm : ∀ a ∈ restrictRange (stabilizerOf X I) I hYI,
      ∀ b ∈ restrictRange (stabilizerOf X I) I hYI, a * b = b * a := by
    rintro _ ⟨⟨y₁, hy₁⟩, rfl⟩ _ ⟨⟨y₂, hy₂⟩, rfl⟩
    rw [← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    exact hyp.X_comm _ hy₁.1 _ hy₂.1
  have hQsq : ∀ a ∈ restrictRange (stabilizerOf X I) I hYI, a * a = 1 := by
    rintro _ ⟨⟨y, hy⟩, rfl⟩
    rw [← map_mul]
    have : (⟨y, hy⟩ * ⟨y, hy⟩ : ↥(stabilizerOf X I)) = 1 := Subtype.ext (hyp.X_sq y hy.1)
    rw [this, map_one]
  have hsd : SelfDual (restrictRange (normalClosure Γ L) I hI.1) ⊤ := by
    refine selfDual_of_nondegOn (B := B.restrict I) (I := ⊤) ?_ ?_ ?_
    · intro x y h
      exact hrefl _ _ h
    · rintro _ ⟨⟨h, hh⟩, rfl⟩ v w
      exact hyp.H_isometry h hh _ _
    · intro u _ hu
      apply Subtype.ext
      exact hnd (u : V) u.2 fun w hw => hu ⟨w, hw⟩ trivial
  set W' : Submodule (ZMod 2) ↥I := (I ⊓ perp B v₁).comap I.subtype with hW'
  have hvW : (⟨i, hi.1⟩ : ↥I) ∈ W' := hi
  have hFT' := fullTransvections_restrict hYI (inf_le_left : I ⊓ perp B v₁ ≤ I) hi hFT
  have hhyper : Module.finrank (ZMod 2) ↥W' + 1 = Module.finrank (ZMod 2) ↥I := by
    have h1 : Module.finrank (ZMod 2) ↥W' = Module.finrank (ZMod 2) ↥(I ⊓ perp B v₁) :=
      LinearEquiv.finrank_eq
        (Submodule.comapSubtypeEquivOfLe (inf_le_left : I ⊓ perp B v₁ ≤ I))
    have h2 := hyp.finrank_inf_perp_add_one hnle
    omega
  have hvne : (⟨i, hi.1⟩ : ↥I) ≠ 0 := fun h => hi0 (congrArg Subtype.val h)
  have hhyp : G1212Hyp (restrictRange (normalClosure Γ L) I hI.1 ⊔
        restrictRange (stabilizerOf X I) I hYI) (restrictRange (normalClosure Γ L) I hI.1)
      (restrictRange (stabilizerOf X I) I hYI) W' ⟨i, hi.1⟩ :=
    { dim := hyp.two_lt_finrank hirr
      le := le_sup_left
      normal := hMnorm
      irr := isIrr_restrictRange_top hirr
      selfDual := hsd
      q_le := le_sup_right
      q_comm := hQcomm
      q_sq := hQsq
      hyperplane := hhyper
      v_mem := hvW
      v_ne := hvne
      transvections := hFT' }
  obtain ⟨f, hsymp, hle, hW, -, -, -, hG, -⟩ :=
    h1212 ↥I _ (restrictRange (normalClosure Γ L) I hI.1)
      (restrictRange (stabilizerOf X I) I hYI) W' ⟨i, hi.1⟩ hhyp
  exact ⟨f, { dim := hyp.two_lt_finrank hirr
              symp := hsymp
              M_le := hle
              concl := hG
              K_le := le_sup_left
              K_norm := hMnorm
              K_irr := isIrr_restrictRange_top hirr
              K_perf := Group.IsPerfect.range _
              Q_le := le_sup_right
              Q_comm := hQcomm
              Q_sq := hQsq
              Q_trans := ⟨hvne, _, fullTransvections_congr hW hFT'⟩ }⟩

end G108Hyp

end G11

end CFSG.Quasithin
