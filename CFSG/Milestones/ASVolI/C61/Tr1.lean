module

public import CFSG.Milestones.ASVolI.C5

public section

namespace CFSG.ASVolI

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChC
open scoped Pointwise

variable {A B : Type} [Group A] [Group B] {f : A →* B} (hf : Function.Injective f)
include hf

theorem burnsideC56_tr_eq_map_comap {X : Subgroup A} {Y : Subgroup B} (hY : Y ≤ X.map f) :
    (Y.comap f).map f = Y := by
  rw [Subgroup.map_comap_eq, inf_eq_right.mpr (hY.trans (Subgroup.map_le_range f X))]

theorem burnsideC56_tr_comap_le {X : Subgroup A} {Y : Subgroup B} (hY : Y ≤ X.map f) :
    Y.comap f ≤ X := by
  intro a ha
  have : f a ∈ X.map f := hY ha
  exact (Subgroup.mem_map_iff_mem hf).mp this

theorem burnsideC56_tr_normalizer (X Y : Subgroup A) :
    (X ⊓ Subgroup.normalizer (Y : Set A)).map f =
      X.map f ⊓ Subgroup.normalizer ((Y.map f : Subgroup B) : Set B) := by
  have key : ∀ a : A, f a ∈ Subgroup.normalizer ((Y.map f : Subgroup B) : Set B) ↔
      a ∈ Subgroup.normalizer (Y : Set A) := by
    intro a
    simp only [Subgroup.mem_normalizer_iff]
    constructor
    · intro h y
      have := h (f y)
      rwa [Subgroup.mem_map_iff_mem hf, ← map_inv, ← map_mul, ← map_mul,
        Subgroup.mem_map_iff_mem hf] at this
    · intro h b
      constructor
      · rintro ⟨y, hy, rfl⟩
        rw [← map_inv, ← map_mul, ← map_mul, Subgroup.mem_map_iff_mem hf]
        exact (h y).mp hy
      · intro hb
        have hbr : f a * b * (f a)⁻¹ ∈ f.range := (Subgroup.map_le_range f Y) hb
        obtain ⟨y, hy⟩ := hbr
        have hb' : b = f (a⁻¹ * y * a) := by
          rw [map_mul, map_mul, map_inv, hy]; group
        rw [hb'] at hb ⊢
        refine Subgroup.mem_map_of_mem f ((h _).mpr ?_)
        rwa [← map_inv, ← map_mul, ← map_mul, Subgroup.mem_map_iff_mem hf] at hb
  ext b
  constructor
  · rintro ⟨a, ⟨haX, haN⟩, rfl⟩
    exact ⟨Subgroup.mem_map_of_mem f haX, (key a).mpr haN⟩
  · rintro ⟨⟨a, haX, rfl⟩, hN⟩
    exact ⟨a, ⟨haX, (key a).mp hN⟩, rfl⟩

theorem burnsideC56_tr_centralizer (X Y : Subgroup A) :
    (X ⊓ Subgroup.centralizer (Y : Set A)).map f =
      X.map f ⊓ Subgroup.centralizer ((Y.map f : Subgroup B) : Set B) := by
  have key : ∀ a : A, f a ∈ Subgroup.centralizer ((Y.map f : Subgroup B) : Set B) ↔
      a ∈ Subgroup.centralizer (Y : Set A) := by
    intro a
    simp only [Subgroup.mem_centralizer_iff]
    constructor
    · intro h y hy
      have := h (f y) (Subgroup.mem_map_of_mem f hy)
      rw [← map_mul, ← map_mul] at this
      exact hf this
    · rintro h _ ⟨y, hy, rfl⟩
      rw [← map_mul, ← map_mul, h y hy]
  ext b
  constructor
  · rintro ⟨a, ⟨haX, haC⟩, rfl⟩
    exact ⟨Subgroup.mem_map_of_mem f haX, (key a).mpr haC⟩
  · rintro ⟨⟨a, haX, rfl⟩, hC⟩
    exact ⟨a, ⟨haX, (key a).mp hC⟩, rfl⟩

theorem burnsideC56_tr_pCoreOf (p : ℕ) (X : Subgroup A) :
    pCoreOf p (X.map f) = (pCoreOf p X).map f := by
  let e : X ≃* (X.map f) := X.equivMapOfInjective f hf
  have h1 := CFSG.LieType.BorelTits.map_pCore_mulEquiv p e
  unfold pCoreOf
  rw [← h1, Subgroup.map_map, Subgroup.map_map]
  congr 1

theorem burnsideC56_tr_oTwoUpper (X : Subgroup A) :
    oTwoUpper (X.map f) = (oTwoUpper X).map f := by
  unfold oTwoUpper
  rw [MonoidHom.map_closure]
  congr 1
  ext b
  constructor
  · rintro ⟨⟨a, haX, rfl⟩, hodd⟩
    exact ⟨a, ⟨haX, by rwa [orderOf_injective f hf a] at hodd⟩, rfl⟩
  · rintro ⟨a, ⟨haX, hodd⟩, rfl⟩
    exact ⟨Subgroup.mem_map_of_mem f haX, by rwa [orderOf_injective f hf a]⟩

theorem burnsideC56_tr_relIndex (X Y : Subgroup A) :
    (X.map f).relIndex (Y.map f) = X.relIndex Y :=
  Subgroup.relIndex_map_map_of_injective X Y hf

theorem burnsideC56_tr_card (X : Subgroup A) : Nat.card ↥(X.map f) = Nat.card X :=
  Subgroup.card_map_of_injective hf

theorem burnsideC56_tr_isElemAbelian (p : ℕ) (X : Subgroup A) :
    IsElemAbelian p (X.map f) ↔ IsElemAbelian p X := by
  let e : X ≃* (X.map f) := X.equivMapOfInjective f hf
  unfold IsElemAbelian
  constructor
  · rintro ⟨⟨hc⟩, hp⟩
    refine ⟨⟨⟨fun a b => e.injective (by rw [map_mul, map_mul]; exact hc.comm _ _)⟩⟩, fun a ha => ?_⟩
    have := hp (f a) (Subgroup.mem_map_of_mem f ha)
    rw [← map_pow] at this
    exact hf (this.trans (map_one f).symm)
  · rintro ⟨⟨hc⟩, hp⟩
    refine ⟨⟨⟨fun a b => e.symm.injective (by rw [map_mul, map_mul]; exact hc.comm _ _)⟩⟩, ?_⟩
    rintro _ ⟨a, ha, rfl⟩
    rw [← map_pow, hp a ha, map_one]

theorem burnsideC56_tr_isPGroup (p : ℕ) (X : Subgroup A) :
    IsPGroup p ↥(X.map f) ↔ IsPGroup p ↥X := by
  let e : X ≃* (X.map f) := X.equivMapOfInjective f hf
  exact ⟨fun h => h.of_equiv e.symm, fun h => h.of_equiv e⟩

theorem burnsideC56_tr_isSylowTwoOf (X Y : Subgroup A) :
    IsSylowTwoOf (X.map f) (Y.map f) ↔ IsSylowTwoOf X Y := by
  unfold IsSylowTwoOf
  rw [Subgroup.map_le_map_iff_of_injective hf, burnsideC56_tr_isPGroup hf]
  have : ((X.map f).subgroupOf (Y.map f)).index = (X.subgroupOf Y).index :=
    burnsideC56_tr_relIndex hf X Y
  rw [this]

theorem burnsideC56_tr_charTwo (X : Subgroup A) : CharTwo (X.map f) ↔ CharTwo X := by
  unfold CharTwo
  rw [burnsideC56_tr_pCoreOf hf, ← burnsideC56_tr_centralizer hf,
    Subgroup.map_le_map_iff_of_injective hf]

theorem burnsideC56_tr_rconj (g : A) (X : Subgroup A) :
    ChC.rconj (f g) (X.map f) = (ChC.rconj g X).map f := by
  unfold ChC.rconj conjByElt
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1
  ext a
  simp [MulAut.conj_apply, map_mul, map_inv]

theorem burnsideC56_tr_set_mul (X Y Z : Subgroup A) :
    ((X.map f : Subgroup B) : Set B) = ((Y.map f : Subgroup B) : Set B) * ((Z.map f : Subgroup B) : Set B) ↔
      (X : Set A) = (Y : Set A) * (Z : Set A) := by
  simp only [Subgroup.coe_map]
  rw [← Set.image_mul]
  exact (Set.image_injective.mpr hf).eq_iff

theorem burnsideC56_tr_isMaxElemAbelian (X Y : Subgroup A) :
    IsMaxElemAbelian (X.map f) (Y.map f) ↔ IsMaxElemAbelian X Y := by
  unfold IsMaxElemAbelian
  rw [Subgroup.map_le_map_iff_of_injective hf, burnsideC56_tr_isElemAbelian hf]
  constructor
  · rintro ⟨h1, h2, h3⟩
    refine ⟨h1, h2, fun B' hB hBe => ?_⟩
    have := h3 (B'.map f) ((Subgroup.map_le_map_iff_of_injective hf).mpr hB)
      ((burnsideC56_tr_isElemAbelian hf 2 B').mpr hBe)
    rwa [burnsideC56_tr_card hf, burnsideC56_tr_card hf] at this
  · rintro ⟨h1, h2, h3⟩
    refine ⟨h1, h2, fun B' hB hBe => ?_⟩
    have hB' := burnsideC56_tr_eq_map_comap hf hB
    rw [← hB'] at hBe ⊢
    rw [burnsideC56_tr_isElemAbelian hf] at hBe
    rw [burnsideC56_tr_card hf, burnsideC56_tr_card hf]
    exact h3 _ (burnsideC56_tr_comap_le hf hB) hBe

theorem burnsideC56_tr_AFam (X : Subgroup A) :
    AFam (X.map f) = Subgroup.map f '' AFam X := by
  ext Y
  constructor
  · intro hY
    have hle : Y ≤ X.map f := hY.1
    refine ⟨Y.comap f, ?_, burnsideC56_tr_eq_map_comap hf hle⟩
    show IsMaxElemAbelian X (Y.comap f)
    rw [← burnsideC56_tr_isMaxElemAbelian hf, burnsideC56_tr_eq_map_comap hf hle]
    exact hY
  · rintro ⟨Z, hZ, rfl⟩
    exact (burnsideC56_tr_isMaxElemAbelian hf X Z).mpr hZ

theorem burnsideC56_tr_thompsonJ (X : Subgroup A) :
    thompsonJ (X.map f) = (thompsonJ X).map f := by
  unfold thompsonJ
  apply le_antisymm
  · refine iSup₂_le fun Y hY => ?_
    have hle : Y ≤ X.map f := hY.1
    rw [← burnsideC56_tr_eq_map_comap hf hle]
    refine Subgroup.map_mono (le_iSup₂_of_le (Y.comap f) ?_ le_rfl)
    rw [← burnsideC56_tr_isMaxElemAbelian hf, burnsideC56_tr_eq_map_comap hf hle]
    exact hY
  · rw [Subgroup.map_le_iff_le_comap]
    refine iSup₂_le fun Z hZ => ?_
    rw [← Subgroup.map_le_iff_le_comap]
    exact le_iSup₂_of_le (Z.map f) ((burnsideC56_tr_isMaxElemAbelian hf X Z).mpr hZ) le_rfl

theorem burnsideC56_tr_omegaOneOf (X : Subgroup A) :
    omegaOneOf (X.map f) = (omegaOneOf X).map f := by
  unfold omegaOneOf
  rw [MonoidHom.map_closure]
  congr 1
  ext b
  constructor
  · rintro ⟨⟨a, haX, rfl⟩, h2⟩
    refine ⟨a, ⟨haX, ?_⟩, rfl⟩
    rw [← map_pow] at h2
    exact hf (h2.trans (map_one f).symm)
  · rintro ⟨a, ⟨haX, h2⟩, rfl⟩
    exact ⟨Subgroup.mem_map_of_mem f haX, by rw [← map_pow, h2, map_one]⟩

theorem burnsideC56_tr_centerOf (X : Subgroup A) : centerOf (X.map f) = (centerOf X).map f := by
  unfold centerOf
  rw [burnsideC56_tr_centralizer hf]

theorem burnsideC56_tr_baum (X : Subgroup A) : baum (X.map f) = (baum X).map f := by
  unfold baum omegaOneCenterOf
  rw [burnsideC56_tr_thompsonJ hf, burnsideC56_tr_centerOf hf, burnsideC56_tr_omegaOneOf hf,
    burnsideC56_tr_centralizer hf]

end CFSG.ASVolI
