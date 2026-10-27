module

public import CFSG.LocalAnalysis.StandardType.FS81.D6Model
public import CFSG.ClassicalInvolution.Models.LinearPairs.Pairs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveTier1Subtype

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.StandardType.FrameRoute.FS81.D6M

open CFSG.ClassicalInvolution.WeakCT

variable {G : Type} [Group G] {K : Subgroup G}

noncomputable abbrev tr (e : ↥K ≃* ↥Om12) (X : Subgroup (V12 ≃ₗ[ZMod 2] V12)) : Subgroup G :=
  (X.subgroupOf Om12).map (K.subtype.comp e.symm.toMonoidHom)

noncomputable abbrev pull (e : ↥K ≃* ↥Om12) (H : Subgroup G) : Subgroup (V12 ≃ₗ[ZMod 2] V12) :=
  (H.comap (K.subtype.comp e.symm.toMonoidHom)).map Om12.subtype

theorem mem_tr {e : ↥K ≃* ↥Om12} {X : Subgroup (V12 ≃ₗ[ZMod 2] V12)} {x : G} :
    x ∈ tr e X ↔ ∃ y : ↥Om12, (y : V12 ≃ₗ[ZMod 2] V12) ∈ X ∧ ((e.symm y : ↥K) : G) = x := by
  simp only [tr, Subgroup.mem_map, Subgroup.mem_subgroupOf, MonoidHom.coe_comp,
    Subgroup.coe_subtype, Function.comp_apply, MulEquiv.coe_toMonoidHom]

theorem mem_tr_iff (e : ↥K ≃* ↥Om12) (X : Subgroup (V12 ≃ₗ[ZMod 2] V12)) (k : ↥K) :
    (k : G) ∈ tr e X ↔ ((e k : ↥Om12) : V12 ≃ₗ[ZMod 2] V12) ∈ X := by
  rw [mem_tr]
  constructor
  · rintro ⟨y, hy, hyk⟩
    have : e.symm y = k := Subtype.ext hyk
    rw [← this, MulEquiv.apply_symm_apply]
    exact hy
  · intro h
    exact ⟨e k, h, by rw [MulEquiv.symm_apply_apply]⟩

theorem tr_le_K (e : ↥K ≃* ↥Om12) (X : Subgroup (V12 ≃ₗ[ZMod 2] V12)) : tr e X ≤ K := by
  rintro _ ⟨y, -, rfl⟩
  exact (e.symm y).2

theorem tr_mono (e : ↥K ≃* ↥Om12) {X Y : Subgroup (V12 ≃ₗ[ZMod 2] V12)} (h : X ≤ Y) :
    tr e X ≤ tr e Y :=
  Subgroup.map_mono fun _ hy => h hy

theorem pull_le_Om12 (e : ↥K ≃* ↥Om12) (H : Subgroup G) : pull e H ≤ Om12 := by
  rintro _ ⟨y, -, rfl⟩
  exact y.2

theorem le_pull_iff (e : ↥K ≃* ↥Om12) {X : Subgroup (V12 ≃ₗ[ZMod 2] V12)} (hX : X ≤ Om12)
    (H : Subgroup G) : X ≤ pull e H ↔ tr e X ≤ H := by
  constructor
  · intro h x hx
    obtain ⟨y, hyX, rfl⟩ := mem_tr.mp hx
    obtain ⟨z, hz, hzy⟩ := h hyX
    have : z = y := Subtype.ext hzy
    subst this
    exact hz
  · intro h y hy
    exact ⟨⟨y, hX hy⟩, h (mem_tr.mpr ⟨⟨y, hX hy⟩, hy, rfl⟩), rfl⟩

theorem tr_pull (e : ↥K ≃* ↥Om12) {H : Subgroup G} (hH : H ≤ K) : tr e (pull e H) = H := by
  apply le_antisymm ((le_pull_iff e (pull_le_Om12 e H) H).mp le_rfl)
  intro x hx
  refine mem_tr.mpr ⟨e ⟨x, hH hx⟩, ⟨e ⟨x, hH hx⟩, ?_, rfl⟩, by rw [MulEquiv.symm_apply_apply]⟩
  show ((e.symm (e ⟨x, hH hx⟩) : ↥K) : G) ∈ H
  rw [MulEquiv.symm_apply_apply]
  exact hx

theorem pull_tr (e : ↥K ≃* ↥Om12) {X : Subgroup (V12 ≃ₗ[ZMod 2] V12)} (hX : X ≤ Om12) :
    pull e (tr e X) = X := by
  apply le_antisymm _ ((le_pull_iff e hX _).mpr le_rfl)
  rintro _ ⟨z, hz, rfl⟩
  have h := (mem_tr_iff e X (e.symm z)).mp hz
  rw [MulEquiv.apply_symm_apply] at h
  exact h

theorem tr_commute (e : ↥K ≃* ↥Om12) {X Y : Subgroup (V12 ≃ₗ[ZMod 2] V12)}
    (h : ∀ a ∈ X, ∀ c ∈ Y, a * c = c * a) :
    ∀ a ∈ tr e X, ∀ c ∈ tr e Y, a * c = c * a := by
  intro a ha c hc
  obtain ⟨y, hyX, rfl⟩ := mem_tr.mp ha
  obtain ⟨z, hzY, rfl⟩ := mem_tr.mp hc
  have hyz : y * z = z * y := Subtype.ext (h _ hyX _ hzY)
  rw [← Subgroup.coe_mul, ← Subgroup.coe_mul, ← map_mul, ← map_mul, hyz]

theorem tr_pair (e : ↥K ≃* ↥Om12) {W X Y : Subgroup (V12 ≃ₗ[ZMod 2] V12)} (hX : X ≤ Om12)
    (hY : Y ≤ Om12) (h : LinearBlockStandardPair (ZMod 2) W X Y) :
    ∃ W' : Subgroup G, LinearBlockStandardPair (ZMod 2) W' (tr e X) (tr e Y) := by
  have hW : W ≤ Om12 := (CFSG.StandardType.linearBlockStandardPair_eq_sup h) ▸ sup_le hX hY
  exact ⟨_, CFSG.ClassicalInvolution.Models.linearBlockStandardPair_map
    (CFSG.StandardType.linearBlockStandardPair_subgroupOf Om12 hW h)
    (K.subtype.comp e.symm.toMonoidHom) (Subtype.val_injective.comp e.symm.injective)⟩

@[expose] noncomputable def conjModel (e : ↥K ≃* ↥Om12) (w : G) :
    ↥(K.map (MulAut.conj w).toMonoidHom) ≃* ↥Om12 :=
  (K.equivMapOfInjective _ (MulAut.conj w).injective).symm.trans e

theorem conjModel_symm_apply (e : ↥K ≃* ↥Om12) (w : G) (y : ↥Om12) :
    (((conjModel e w).symm y : ↥(K.map (MulAut.conj w).toMonoidHom)) : G) =
      w * ((e.symm y : ↥K) : G) * w⁻¹ := rfl

theorem conjModel_apply (e : ↥K ≃* ↥Om12) (w : G) (k : ↥K)
    (h : w * (k : G) * w⁻¹ ∈ K.map (MulAut.conj w).toMonoidHom) :
    conjModel e w ⟨w * k * w⁻¹, h⟩ = e k := by
  apply (conjModel e w).symm.injective
  rw [MulEquiv.symm_apply_apply]
  apply Subtype.ext
  rw [conjModel_symm_apply, MulEquiv.symm_apply_apply]

theorem tr_conjModel (e : ↥K ≃* ↥Om12) (w : G) (X : Subgroup (V12 ≃ₗ[ZMod 2] V12)) :
    tr (conjModel e w) X = (tr e X).map (MulAut.conj w).toMonoidHom := by
  ext x
  rw [mem_tr, Subgroup.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨_, mem_tr.mpr ⟨y, hy, rfl⟩, (conjModel_symm_apply e w y).symm⟩
  · rintro ⟨_, hz, rfl⟩
    obtain ⟨y, hy, rfl⟩ := mem_tr.mp hz
    exact ⟨y, hy, conjModel_symm_apply e w y⟩

end CFSG.StandardType.FrameRoute.FS81.D6M
