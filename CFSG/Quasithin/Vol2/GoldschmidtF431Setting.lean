module

public import CFSG.Quasithin.Vol2.GoldschmidtF431Main
public import CFSG.Quasithin.Recognition.F4Main

public section

namespace CFSG.Quasithin.H13.F431

open CFSG.Blueprint CFSG.Quasithin

section Setting

variable {D : Type} [Group D]

theorem finite_mulAut_of_finite [Finite D] : Finite (MulAut D) :=
  Finite.of_injective (fun φ : MulAut D => (φ : D → D)) fun _ _ h => MulEquiv.ext (congrFun h)

theorem innRange_normal : ((MulAut.conj : D →* MulAut D).range).Normal := by
  refine ⟨fun x hx φ => ?_⟩
  obtain ⟨d, rfl⟩ := hx
  refine ⟨φ d, ?_⟩
  ext y
  simp [MulAut.conj_apply]

@[expose] noncomputable def LieAmalgamExt.ι0 (A : LieAmalgamExt D) :
    (RankTwoAmalgam.ofSubgroups A.N1 A.N2).Completion ↥A.K :=
  RankTwoAmalgam.inclusionCompletion A.N1 A.N2 A.K rfl

@[expose] noncomputable def LieAmalgamExt.setting (A : LieAmalgamExt D) (hfin : Finite D) (pm : ℕ)
    (hpm : 3 ≤ pm) : LieSetting.{0, 0} :=
  haveI : Finite (MulAut D) := finite_mulAut_of_finite
  { α := RankTwoAmalgam.ofSubgroups A.N1 A.N2
    Yb := ↥A.K
    grp := inferInstance
    fin := inferInstance
    ι := A.ι0
    hι := RankTwoAmalgam.inclusionCompletion_isFaithful A.N1 A.N2 A.K rfl
    N := ((MulAut.conj : D →* MulAut D).range).comap
      (A.K.subtype.comp (A.ι0.φ1.range ⊔ A.ι0.φ2.range).subtype)
    hN := (innRange_normal (D := D)).comap _
    p := 2
    hp := Nat.prime_two
    m := pm
    hm := hpm }

end Setting

section SettingN

variable {D : Type} [Group D] (A : LieAmalgamExt D) (hfin : Finite D) (pm : ℕ) (hpm : 3 ≤ pm)

@[expose] noncomputable def toSettingN (hgen : (MulAut.conj : D →* MulAut D).range ≤ A.K) :
    D →* ↥(A.setting hfin pm hpm).N :=
  (((MulAut.conj : D →* MulAut D).codRestrict A.K (fun d => hgen ⟨d, rfl⟩)).codRestrict
      (A.ι0.φ1.range ⊔ A.ι0.φ2.range)
      (fun d => by rw [A.ι0.gen]; exact Subgroup.mem_top _)).codRestrict
    (A.setting hfin pm hpm).N (fun d => ⟨d, rfl⟩)

@[expose] noncomputable def settingToAut : (A.setting hfin pm hpm).ι.G0 →* MulAut D :=
  A.K.subtype.comp (A.ι0.φ1.range ⊔ A.ι0.φ2.range).subtype

theorem toSettingN_injective (hZ : Subgroup.center D = ⊥)
    (hgen : (MulAut.conj : D →* MulAut D).range ≤ A.K) :
    Function.Injective (toSettingN A hfin pm hpm hgen) := by
  intro a b h
  have h1 : (MulAut.conj a : MulAut D) = MulAut.conj b :=
    congrArg (fun x : ↥(A.setting hfin pm hpm).N => settingToAut A hfin pm hpm x.1) h
  have hc : b⁻¹ * a ∈ Subgroup.center D := by
    rw [Subgroup.mem_center_iff]
    intro y
    have h2 : (MulAut.conj (b⁻¹ * a) : MulAut D) = 1 := by
      rw [map_mul, map_inv, h1, inv_mul_cancel]
    have h3 := congrArg (fun φ : MulAut D => φ y) h2
    simp only [MulAut.conj_apply, MulAut.one_apply] at h3
    calc y * (b⁻¹ * a) = (b⁻¹ * a * y * (b⁻¹ * a)⁻¹) * (b⁻¹ * a) := by rw [h3]
      _ = (b⁻¹ * a) * y := by group
  rw [hZ, Subgroup.mem_bot, inv_mul_eq_one] at hc
  exact hc.symm

theorem toSettingN_surjective (hgen : (MulAut.conj : D →* MulAut D).range ≤ A.K) :
    Function.Surjective (toSettingN A hfin pm hpm hgen) := by
  rintro ⟨x, d, hd⟩
  exact ⟨d, Subtype.ext (Subtype.ext (Subtype.ext hd))⟩

theorem nonempty_mulEquiv_settingN (hZ : Subgroup.center D = ⊥)
    (hgen : (MulAut.conj : D →* MulAut D).range ≤ A.K) :
    Nonempty (D ≃* ↥(A.setting hfin pm hpm).N) :=
  ⟨MulEquiv.ofBijective (toSettingN A hfin pm hpm hgen)
    ⟨toSettingN_injective A hfin pm hpm hZ hgen, toSettingN_surjective A hfin pm hpm hgen⟩⟩

end SettingN

section Recognition

variable {D : Type} [Group D]

@[expose] noncomputable def completionOf (A : LieAmalgamExt D) {Y : Type} [Group Y]
    (β1 : ↥A.N1 →* Y) (β2 : ↥A.N2 →* Y)
    (hag : ∀ (x : MulAut D) (h1 : x ∈ A.N1) (h2 : x ∈ A.N2), β1 ⟨x, h1⟩ = β2 ⟨x, h2⟩)
    (hint : ∀ y : Y, y ∈ β1.range → y ∈ β2.range →
      ∃ (x : MulAut D) (h1 : x ∈ A.N1) (_ : x ∈ A.N2), β1 ⟨x, h1⟩ = y)
    (hgen : β1.range ⊔ β2.range = ⊤) : (RankTwoAmalgam.ofSubgroups A.N1 A.N2).Completion Y where
  φ1 := β1
  φ12 := β1.comp (Subgroup.inclusion (inf_le_left : A.N1 ⊓ A.N2 ≤ A.N1))
  φ2 := β2
  comm1 _ := rfl
  comm2 g := (hag g.1 g.2.1 g.2.2).symm
  inter := by
    ext y
    constructor
    · rintro ⟨h1, h2⟩
      obtain ⟨x, hx1, hx2, hxy⟩ := hint y h1 h2
      exact ⟨⟨x, hx1, hx2⟩, hxy⟩
    · rintro ⟨g, rfl⟩
      exact ⟨⟨_, rfl⟩, ⟨⟨g.1, g.2.2⟩, (hag g.1 g.2.1 g.2.2).symm⟩⟩
  gen := hgen

theorem recognition_of_facts {t : CFSG.Assembly.LowTwoRank.StatedLieTag} {m f : ℕ}
    (hmodel : ∀ (D : Type) [Group D], LieModel D t m 2 f → Finite D ∧ Subgroup.center D = ⊥)
    (hgen : ∀ (D : Type) [Group D], LieModel D t m 2 f → ∀ A : LieAmalgamExt D,
      (MulAut.conj : D →* MulAut D).range ≤ A.K)
    (pm : ℕ) (hpm : 3 ≤ pm)
    (h45 : ∀ (D : Type) [Group D] (hD : LieModel D t m 2 f) (A : LieAmalgamExt D),
      (A.setting (hmodel D hD).1 pm hpm).Facts45L)
    (h48 : ∀ (D : Type) [Group D] (hD : LieModel D t m 2 f) (A : LieAmalgamExt D) (Y : Type)
      [Group Y] [Finite Y] (β : (A.setting (hmodel D hD).1 pm hpm).α.Completion Y),
      β.IsFaithful → β.IsSmall pm → (A.setting (hmodel D hD).1 pm hpm).F48Concl β) :
    F431Recognition t m f := by
  intro D _ hD A Y _ _ β1 β2 hi1 hi2 hag hint hgenY hle
  obtain ⟨hfinD, hZ⟩ := hmodel D hD
  have hβ : (completionOf A β1 β2 hag hint hgenY).IsFaithful :=
    ⟨hi1, hi1.comp (Subgroup.inclusion_injective _), hi2⟩
  obtain ⟨hY, Ġ, hĠ, hext, ⟨e⟩⟩ := (h45 D hD A).lemma_F424 (completionOf A β1 β2 hag hint hgenY)
    hβ hle (h48 D hD A Y _ hβ)
  obtain ⟨ν, hνi, hνn, hνc, -⟩ := hext
  obtain ⟨eN⟩ := nonempty_mulEquiv_settingN A hfinD pm hpm hZ (hgen D hD A)
  have hrange : (ν.comp eN.toMonoidHom).range = ν.range := by
    ext y
    constructor
    · rintro ⟨d, rfl⟩
      exact ⟨_, rfl⟩
    · rintro ⟨n, rfl⟩
      exact ⟨eN.symm n, by simp⟩
  refine ⟨hY, Ġ, hĠ, ν.comp eN.toMonoidHom, hνi.comp eN.injective, ?_, ?_, ⟨e⟩⟩
  · rw [hrange]
    exact hνn
  · rw [hrange]
    exact hνc

end Recognition

section Facts

@[expose] def polyNumber (t : CFSG.Assembly.LowTwoRank.StatedLieTag) : ℕ :=
  match t with
  | .PSL => 3
  | .PSp => 4
  | .PSU => 4
  | .G2 => 6
  | .trialityD4 => 6
  | .twistedF4 => 8
  | _ => 3

theorem three_le_polyNumber (t : CFSG.Assembly.LowTwoRank.StatedLieTag) : 3 ≤ polyNumber t := by
  cases t <;> simp [polyNumber]

@[expose] def F431ModelFacts (t : CFSG.Assembly.LowTwoRank.StatedLieTag) (m f : ℕ) : Prop :=
  ∀ (D : Type) [Group D], LieModel D t m 2 f → Finite D ∧ Subgroup.center D = ⊥

@[expose] def F431Generation (t : CFSG.Assembly.LowTwoRank.StatedLieTag) (m f : ℕ) : Prop :=
  ∀ (D : Type) [Group D], LieModel D t m 2 f → ∀ A : LieAmalgamExt D,
    (MulAut.conj : D →* MulAut D).range ≤ A.K

@[expose] def F431Facts45 (t : CFSG.Assembly.LowTwoRank.StatedLieTag) (m f : ℕ)
    (hm : F431ModelFacts t m f) : Prop :=
  ∀ (D : Type) [Group D] (hD : LieModel D t m 2 f) (A : LieAmalgamExt D),
    (A.setting (hm D hD).1 (polyNumber t) (three_le_polyNumber t)).Facts45L

@[expose] def F431F48 (t : CFSG.Assembly.LowTwoRank.StatedLieTag) (m f : ℕ)
    (hm : F431ModelFacts t m f) : Prop :=
  ∀ (D : Type) [Group D] (hD : LieModel D t m 2 f) (A : LieAmalgamExt D) (Y : Type) [Group Y]
    [Finite Y] (β : (A.setting (hm D hD).1 (polyNumber t) (three_le_polyNumber t)).α.Completion Y),
    β.IsFaithful → β.IsSmall (polyNumber t) →
    (A.setting (hm D hD).1 (polyNumber t) (three_le_polyNumber t)).F48Concl β

end Facts

end CFSG.Quasithin.H13.F431
