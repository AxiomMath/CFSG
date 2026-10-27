module

public import CFSG.SignalizerFunctorTheorem.Quadratic.Toolkit
public import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.SignalizerFunctorTheorem.Quadratic

variable {p : ℕ} {V : Type*} [AddCommGroup V] [Module (ZMod p) V]

theorem mem_cj {g : LGL p V} {A : Subgroup (LGL p V)} {x : LGL p V} :
    x ∈ cj g A ↔ g⁻¹ * x * g ∈ A := by
  constructor
  · intro hx
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hx
    simpa [MulAut.conj_apply, mul_assoc] using ha
  · intro hx
    refine Subgroup.mem_map.mpr ⟨g⁻¹ * x * g, hx, ?_⟩
    simp [MulAut.conj_apply, mul_assoc]

theorem cj_mono (g : LGL p V) {A B : Subgroup (LGL p V)} (h : A ≤ B) : cj g A ≤ cj g B :=
  Subgroup.map_mono h

theorem cj_one (A : Subgroup (LGL p V)) : cj 1 A = A := by
  ext x
  rw [mem_cj]
  simp

theorem cj_mul (g h : LGL p V) (A : Subgroup (LGL p V)) : cj (g * h) A = cj g (cj h A) := by
  ext x
  rw [mem_cj, mem_cj, mem_cj]
  simp [mul_assoc]

theorem cj_inv_cj (g : LGL p V) (A : Subgroup (LGL p V)) : cj g⁻¹ (cj g A) = A := by
  rw [← cj_mul]
  simp [cj_one]

theorem cj_cj_inv (g : LGL p V) (A : Subgroup (LGL p V)) : cj g (cj g⁻¹ A) = A := by
  rw [← cj_mul]
  simp [cj_one]

theorem cj_le_cj_iff (g : LGL p V) {A B : Subgroup (LGL p V)} : cj g A ≤ cj g B ↔ A ≤ B := by
  refine ⟨fun h => ?_, cj_mono g⟩
  have := cj_mono g⁻¹ h
  rwa [cj_inv_cj, cj_inv_cj] at this

theorem QOne.cj {A : Subgroup (LGL p V)} (hA : QOne A) (g : LGL p V) : QOne (cj g A) := by
  intro B hB
  have hB' : Quadratic.cj g⁻¹ B ≤ A := by
    have := cj_mono g⁻¹ hB
    rwa [cj_inv_cj] at this
  have h := hA _ hB'
  rw [card_cj B g⁻¹, card_fixSub_cj B g⁻¹] at h
  rw [card_cj A g, card_fixSub_cj A g]
  exact h

theorem IsElemAb.map {G G' : Type*} [Group G] [Group G'] {A : Subgroup G}
    (hA : IsElemAb p A) (f : G →* G') : IsElemAb p (A.map f) :=
  CFSG.Open.IsElemAbelian.map hA f

theorem IsElemAb.map_conj {A : Subgroup (LGL p V)} (hA : IsElemAb p A) (g : LGL p V) :
    IsElemAb p (cj g A) :=
  hA.map (MulAut.conj g).toMonoidHom

theorem IsAV.cj {H A : Subgroup (LGL p V)} (hA : IsAV H A) (g : LGL p V) :
    IsAV (cj g H) (cj g A) :=
  ⟨cj_mono g hA.1, hA.2.1.map_conj g, hA.2.2.cj g⟩

theorem commSub_cj_eq_bot_iff (A : Subgroup (LGL p V)) (g : LGL p V) :
    commSub (cj g A) = ⊥ ↔ commSub A = ⊥ := by
  rw [commSub_cj]
  constructor
  · intro h
    rw [Submodule.eq_bot_iff]
    intro x hx
    have h1 : g x ∈ (commSub A).map (g : V →ₗ[ZMod p] V) := Submodule.mem_map_of_mem hx
    rw [h] at h1
    exact g.map_eq_zero_iff.mp ((Submodule.mem_bot _).mp h1)
  · intro h
    rw [h, Submodule.map_bot]

theorem IsAVMin.cj {H A : Subgroup (LGL p V)} (hA : IsAVMin H A) (g : LGL p V) :
    IsAVMin (cj g H) (cj g A) := by
  obtain ⟨hAV, hne, hmin⟩ := hA
  refine ⟨hAV.cj g, fun h => hne ((commSub_cj_eq_bot_iff A g).mp h), ?_⟩
  intro B hB hBne hBle
  have hB' : IsAV H (Quadratic.cj g⁻¹ B) := by
    have := hB.cj g⁻¹
    rwa [cj_inv_cj] at this
  have hne' : commSub (Quadratic.cj g⁻¹ B) ≠ ⊥ :=
    fun h => hBne ((commSub_cj_eq_bot_iff B g⁻¹).mp h)
  have hle' : Quadratic.cj g⁻¹ B ≤ A := by
    have := cj_mono g⁻¹ hBle
    rwa [cj_inv_cj] at this
  have := hmin _ hB' hne' hle'
  rw [← this, cj_cj_inv]

theorem cj_map_conj (g h : LGL p V) (A : Subgroup (LGL p V)) :
    cj g (A.map (MulAut.conj h).toMonoidHom) =
      (cj g A).map (MulAut.conj (g * h * g⁻¹)).toMonoidHom := by
  ext x
  constructor
  · intro hx
    obtain ⟨y, ⟨a, ha, rfl⟩, rfl⟩ := Subgroup.mem_map.mp hx
    refine Subgroup.mem_map.mpr ⟨g * a * g⁻¹, Subgroup.mem_map.mpr ⟨a, ha, rfl⟩, ?_⟩
    simp [MulAut.conj_apply, mul_assoc]
  · intro hx
    obtain ⟨y, ⟨a, ha, rfl⟩, rfl⟩ := Subgroup.mem_map.mp hx
    refine Subgroup.mem_map.mpr ⟨h * a * h⁻¹, Subgroup.mem_map.mpr ⟨a, ha, rfl⟩, ?_⟩
    simp [MulAut.conj_apply, mul_assoc]

theorem cj_blk (H A : Subgroup (LGL p V)) (g : LGL p V) :
    cj g (blk H A) = blk (cj g H) (cj g A) := by
  apply le_antisymm
  · unfold blk
    refine (Subgroup.map_iSup _ _).le.trans (iSup_le fun h => ?_)
    refine (Subgroup.map_iSup _ _).le.trans (iSup_le fun hh => ?_)
    have e : cj g (A.map (MulAut.conj h).toMonoidHom) =
        (cj g A).map (MulAut.conj (g * h * g⁻¹)).toMonoidHom := cj_map_conj g h A
    change cj g (A.map (MulAut.conj h).toMonoidHom) ≤ _
    rw [e]
    exact le_iSup₂_of_le (g * h * g⁻¹) (mem_cj.mpr (by simpa [mul_assoc] using hh)) le_rfl
  · unfold blk
    refine iSup₂_le fun h' hh' => ?_
    have hh : g⁻¹ * h' * g ∈ H := mem_cj.mp hh'
    have e := cj_map_conj g (g⁻¹ * h' * g) A
    have e2 : g * (g⁻¹ * h' * g) * g⁻¹ = h' := by group
    rw [e2] at e
    rw [← e]
    exact cj_mono g (le_iSup₂_of_le (g⁻¹ * h' * g) hh le_rfl)

theorem cj_eq_of_mem_normalizer {H : Subgroup (LGL p V)} {g : LGL p V}
    (hg : g ∈ Subgroup.normalizer (H : Set (LGL p V))) : cj g H = H := by
  ext x
  rw [mem_cj]
  have := Subgroup.mem_normalizer_iff.mp (inv_mem hg) x
  simpa using this.symm

theorem blocks_cj {H : Subgroup (LGL p V)} {g : LGL p V}
    (hg : g ∈ Subgroup.normalizer (H : Set (LGL p V))) {E : Subgroup (LGL p V)}
    (hE : E ∈ blocks H) : cj g E ∈ blocks H := by
  obtain ⟨A, hA, rfl⟩ := hE
  refine ⟨cj g A, ?_, ?_⟩
  · have := hA.cj g
    rwa [cj_eq_of_mem_normalizer hg] at this
  · rw [cj_blk, cj_eq_of_mem_normalizer hg]

end CFSG.SignalizerFunctorTheorem.Quadratic
