module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps136SimpleIsoUnique
public import CFSG.Quasithin.Background.F918V2F

public section

namespace CFSG.LocalAnalysis.WeakClosure81.GF2Reps136

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open scoped commutatorElement Pointwise Matrix

variable {Q : Type} [CommGroup Q]

lemma w1369_ta_isInv_iff {Λ : Subgroup (MulAut Q)} {S : Subgroup Q} :
    StableUnder Λ S ↔ XMod.IsInv ↥Λ S := by
  constructor
  · exact fun h a => h a a.2
  · exact fun h x hx => h ⟨x, hx⟩

lemma w1369_ta_isIrr_iff {Λ : Subgroup (MulAut Q)} {S : Subgroup Q} :
    w1369_ta_IsSimple Λ S ↔ XMod.IsIrr ↥Λ S := by
  unfold w1369_ta_IsSimple XMod.IsIrr XMod.IsIrrSec
  rw [bot_lt_iff_ne_bot]
  constructor
  · rintro ⟨hne, hstab, hmin⟩
    exact ⟨(w1369_ta_isInv_iff (Λ := Λ) (S := S)).1 hstab, hne, fun J hJ _ hJS =>
      hmin J ((w1369_ta_isInv_iff (Λ := Λ) (S := J)).2 hJ) hJS⟩
  · rintro ⟨hstab, hne, hmin⟩
    exact ⟨hne, (w1369_ta_isInv_iff (Λ := Λ) (S := S)).2 hstab, fun J hJ hJS =>
      hmin J ((w1369_ta_isInv_iff (Λ := Λ) (S := J)).1 hJ) bot_le hJS⟩

lemma w1369_ta_v2fEqv_iff {Λ : Subgroup (MulAut Q)} {A B : Subgroup Q}
    {hA : StableUnder Λ A} {hB : StableUnder Λ B} {e : ↥A ≃* ↥B} :
    w1369_ta_Equiv hA hB e ↔ CFSG.Quasithin.Z391.V2fEqv ↥Λ e := by
  constructor
  · intro he a l l' ha
    have hl' : l' = ⟨(a : MulAut Q) (l : Q), hA (a : MulAut Q) a.2 (l : Q) l.2⟩ :=
      Subtype.ext ha.symm
    rw [hl']
    exact (he (a : MulAut Q) a.2 l).symm
  · intro h g hg x
    have hx := h ⟨g, hg⟩ x ⟨g (x : Q), hA g hg (x : Q) x.2⟩ rfl
    exact hx.symm

lemma w1369_ta_v2fEqv_aut_eq_one {Λ : Subgroup (MulAut Q)} {k : ℕ} {I : Fin k → Subgroup Q}
    (P : w1369_ta_Proj I Λ) (hstab : ∀ i, StableUnder Λ (I i))
    (hsimple : ∀ i, w1369_ta_IsSimple Λ (I i))
    (hend : ∀ i j, i ≠ j → SecIsoOn Λ (I i) ⊥ (I j) ⊥ → ∀ f : Q →* Q,
      (∀ g ∈ Λ, ∀ x, f (g x) = g (f x)) → (∀ x ∈ I i, f x ∈ I i) →
      (∀ j', j' ≠ i → ∀ x ∈ I j', f x = 1) → (∀ x ∈ I i, f x = x) ∨ (∀ x ∈ I i, f x = 1))
    (hisoAll : ∀ i j, i ≠ j → SecIsoOn Λ (I i) ⊥ (I j) ⊥)
    (hpart : ∀ i : Fin k, ∃ j : Fin k, j ≠ i) {X : Subgroup Q} (hX : w1369_ta_IsSimple Λ X)
    (φ : ↥X ≃* ↥X) (hφ : CFSG.Quasithin.Z391.V2fEqv ↥Λ φ) : φ = 1 := by
  obtain ⟨i, hSec⟩ := w1369_ta_simple_iso_some P hstab hsimple hX
  exact w1369_ta_aut_eq_one_of_secIsoOn P hstab hsimple hend hisoAll (hpart i) hX hSec φ
    (w1369_ta_v2fEqv_iff.2 hφ)

@[expose] noncomputable def w1369_ta_third {X Y : Subgroup Q} (e : ↥X ≃* ↥Y) : Subgroup Q :=
  (w1369_ta_graphHom e).range

lemma w1369_ta_third_isSimple {Λ : Subgroup (MulAut Q)} {X Y : Subgroup Q}
    (hX : w1369_ta_IsSimple Λ X) (hY : w1369_ta_IsSimple Λ Y) (hXY : X ⊓ Y = ⊥)
    (e : ↥X ≃* ↥Y) (he : w1369_ta_Equiv hX.2.1 hY.2.1 e) :
    w1369_ta_IsSimple Λ (w1369_ta_third e) :=
  w1369_ta_graph_isSimple hX hY hXY e he

lemma w1369_ta_third_le_sup {X Y : Subgroup Q} (e : ↥X ≃* ↥Y) :
    w1369_ta_third e ≤ X ⊔ Y :=
  w1369_ta_graph_le_sup e

lemma w1369_ta_third_ne_left {Λ : Subgroup (MulAut Q)} {X Y : Subgroup Q}
    (hX : w1369_ta_IsSimple Λ X) (hXY : X ⊓ Y = ⊥) (e : ↥X ≃* ↥Y) :
    w1369_ta_third e ≠ X := by
  intro h
  obtain ⟨x, hx⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hX.1
  have hmem : ((x : Q) * (e x : Q)) ∈ w1369_ta_third e := MonoidHom.mem_range.mpr ⟨x, rfl⟩
  rw [h] at hmem
  have h2 : (e x : Q) ∈ X ⊓ Y := by
    refine ⟨?_, (e x).2⟩
    rw [show (e x : Q) = (x : Q)⁻¹ * ((x : Q) * (e x : Q)) from by group]
    exact X.mul_mem (X.inv_mem x.2) hmem
  rw [hXY, Subgroup.mem_bot] at h2
  exact hx (e.injective (by rw [map_one]; exact Subtype.ext h2))

lemma w1369_ta_third_ne_right {Λ : Subgroup (MulAut Q)} {X Y : Subgroup Q}
    (hX : w1369_ta_IsSimple Λ X) (hXY : X ⊓ Y = ⊥) (e : ↥X ≃* ↥Y) :
    w1369_ta_third e ≠ Y := by
  intro h
  obtain ⟨x, hx⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hX.1
  have hmem : ((x : Q) * (e x : Q)) ∈ w1369_ta_third e := MonoidHom.mem_range.mpr ⟨x, rfl⟩
  rw [h] at hmem
  have h2 : (x : Q) ∈ X ⊓ Y := by
    refine ⟨x.2, ?_⟩
    rw [show (x : Q) = ((x : Q) * (e x : Q)) * (e x : Q)⁻¹ from by group]
    exact Y.mul_mem hmem (Y.inv_mem (e x).2)
  rw [hXY, Subgroup.mem_bot] at h2
  exact hx (Subtype.ext h2)

lemma w1369_ta_third_eq {Λ : Subgroup (MulAut Q)} {k : ℕ} {I : Fin k → Subgroup Q}
    (P : w1369_ta_Proj I Λ) (hstab : ∀ i, StableUnder Λ (I i))
    (hsimple : ∀ i, w1369_ta_IsSimple Λ (I i))
    (hend : ∀ i j, i ≠ j → SecIsoOn Λ (I i) ⊥ (I j) ⊥ → ∀ f : Q →* Q,
      (∀ g ∈ Λ, ∀ x, f (g x) = g (f x)) → (∀ x ∈ I i, f x ∈ I i) →
      (∀ j', j' ≠ i → ∀ x ∈ I j', f x = 1) → (∀ x ∈ I i, f x = x) ∨ (∀ x ∈ I i, f x = 1))
    (hisoAll : ∀ i j, i ≠ j → SecIsoOn Λ (I i) ⊥ (I j) ⊥)
    (hpart : ∀ i : Fin k, ∃ j : Fin k, j ≠ i)
    {X Y : Subgroup Q} (hX : w1369_ta_IsSimple Λ X) (hY : w1369_ta_IsSimple Λ Y)
    (hXY : X ⊓ Y = ⊥) {e : ↥X ≃* ↥Y} (he : w1369_ta_Equiv hX.2.1 hY.2.1 e)
    {R : Subgroup Q} (hR : w1369_ta_IsSimple Λ R) (hRle : R ≤ X ⊔ Y)
    (hRX : R ≠ X) (hRY : R ≠ Y) : R = w1369_ta_third e := by
  have hE : ∀ φ : ↥X ≃* ↥X, CFSG.Quasithin.Z391.V2fEqv ↥Λ φ → φ = MulEquiv.refl _ := by
    intro φ hφ
    exact w1369_ta_v2fEqv_aut_eq_one P hstab hsimple hend hisoAll hpart hX φ hφ
  have hg : w1369_ta_IsSimple Λ (w1369_ta_third e) := w1369_ta_third_isSimple hX hY hXY e he
  have hle : w1369_ta_third e ≤ X ⊔ Y := w1369_ta_third_le_sup e
  have hneX : w1369_ta_third e ≠ X := w1369_ta_third_ne_left hX hXY e
  have hneY : w1369_ta_third e ≠ Y := w1369_ta_third_ne_right hX hXY e
  exact CFSG.Quasithin.Z391.v2f_eq_of_le_sup (A := ↥Λ)
    (w1369_ta_isIrr_iff.1 hX) (w1369_ta_isIrr_iff.1 hY) hE
    (w1369_ta_isIrr_iff.1 hR) (w1369_ta_isIrr_iff.1 hg) hRle hle hRX hRY hneX hneY

lemma w1369_ta_third_map {Λ N : Subgroup (MulAut Q)}
    (hnorm : ∀ n ∈ N, ∀ l ∈ Λ, n * l * n⁻¹ ∈ Λ)
    {k : ℕ} {I : Fin k → Subgroup Q} (P : w1369_ta_Proj I Λ)
    (hstab : ∀ i, StableUnder Λ (I i)) (hsimple : ∀ i, w1369_ta_IsSimple Λ (I i))
    (hend : ∀ i j, i ≠ j → SecIsoOn Λ (I i) ⊥ (I j) ⊥ → ∀ f : Q →* Q,
      (∀ g ∈ Λ, ∀ x, f (g x) = g (f x)) → (∀ x ∈ I i, f x ∈ I i) →
      (∀ j', j' ≠ i → ∀ x ∈ I j', f x = 1) → (∀ x ∈ I i, f x = x) ∨ (∀ x ∈ I i, f x = 1))
    (hisoAll : ∀ i j, i ≠ j → SecIsoOn Λ (I i) ⊥ (I j) ⊥)
    (hpart : ∀ i : Fin k, ∃ j : Fin k, j ≠ i)
    {X Y : Subgroup Q} (hX : w1369_ta_IsSimple Λ X) (hY : w1369_ta_IsSimple Λ Y)
    (hXY : X ⊓ Y = ⊥) {e : ↥X ≃* ↥Y} (he : w1369_ta_Equiv hX.2.1 hY.2.1 e)
    {n : MulAut Q} (hn : n ∈ N)
    {e' : ↥(X.map n.toMonoidHom) ≃* ↥(Y.map n.toMonoidHom)}
    (he' : w1369_ta_Equiv (w1369_simple_map hnorm hX hn).2.1
      (w1369_simple_map hnorm hY hn).2.1 e') :
    (w1369_ta_third e).map n.toMonoidHom = w1369_ta_third e' := by
  have hX' : w1369_ta_IsSimple Λ (X.map n.toMonoidHom) := w1369_simple_map hnorm hX hn
  have hY' : w1369_ta_IsSimple Λ (Y.map n.toMonoidHom) := w1369_simple_map hnorm hY hn
  have hXY' : (X.map n.toMonoidHom) ⊓ (Y.map n.toMonoidHom) = ⊥ := by
    rw [← Subgroup.map_inf X Y n.toMonoidHom n.injective, hXY, Subgroup.map_bot]
  have hR : w1369_ta_IsSimple Λ ((w1369_ta_third e).map n.toMonoidHom) :=
    w1369_simple_map hnorm (w1369_ta_third_isSimple hX hY hXY e he) hn
  have hRle : (w1369_ta_third e).map n.toMonoidHom ≤
      (X.map n.toMonoidHom) ⊔ (Y.map n.toMonoidHom) := by
    rw [← Subgroup.map_sup]
    exact Subgroup.map_mono (w1369_ta_third_le_sup e)
  have hneX : (w1369_ta_third e).map n.toMonoidHom ≠ X.map n.toMonoidHom := by
    intro h
    have h1 := congrArg (Subgroup.map (n⁻¹ : MulAut Q).toMonoidHom) h
    rw [Subgroup.map_map, Subgroup.map_map] at h1
    have hid : ((n⁻¹ : MulAut Q).toMonoidHom.comp n.toMonoidHom) = MonoidHom.id Q := by
      ext z
      exact MulEquiv.symm_apply_apply n z
    rw [hid, Subgroup.map_id, Subgroup.map_id] at h1
    exact w1369_ta_third_ne_left hX hXY e h1
  have hneY : (w1369_ta_third e).map n.toMonoidHom ≠ Y.map n.toMonoidHom := by
    intro h
    have h1 := congrArg (Subgroup.map (n⁻¹ : MulAut Q).toMonoidHom) h
    rw [Subgroup.map_map, Subgroup.map_map] at h1
    have hid : ((n⁻¹ : MulAut Q).toMonoidHom.comp n.toMonoidHom) = MonoidHom.id Q := by
      ext z
      exact MulEquiv.symm_apply_apply n z
    rw [hid, Subgroup.map_id, Subgroup.map_id] at h1
    exact w1369_ta_third_ne_right hX hXY e h1
  exact w1369_ta_third_eq P hstab hsimple hend hisoAll hpart hX' hY' hXY' he' hR hRle hneX hneY

end CFSG.LocalAnalysis.WeakClosure81.GF2Reps136
