module

public import CFSG.LocalAnalysis.StandardType.GGLayerAbelianInd
public import CFSG.LocalAnalysis.StandardType.GGLayerSubCoreFamily
public import CFSG.LocalAnalysis.StandardType.GGTwE6LayerCentConverse
public import CFSG.Adapters.CatalogueFieldBridges.Exceptional
public import CFSG.HardMathSupport.Dickson.Sec6.I923Fam.TriD4Aux.Basic
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.Basic

public section

namespace CFSG.StandardType

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.Yardstones.Md0ec50421ce4
  CFSG.LocalAnalysis.GLTheoremA

namespace LayerCores

theorem centFix_map_conj {S : Type*} [Group S] (A : Subgroup S) :
    I142.centFix (A.map (MulAut.conj : S →* MulAut S)) = Subgroup.centralizer (A : Set S) := by
  ext x
  rw [I142.mem_centFix, Subgroup.mem_centralizer_iff]
  constructor
  · intro h a ha
    have h1 := h _ ⟨a, ha, rfl⟩
    rw [MulAut.conj_apply, mul_inv_eq_iff_eq_mul] at h1
    exact h1
  · rintro h _ ⟨a, ha, rfl⟩
    rw [MulAut.conj_apply, mul_inv_eq_iff_eq_mul]
    exact h a ha

theorem isPGroup_map_conj {S : Type*} [Group S] {p : ℕ} {A : Subgroup S} (hA : IsPGroup p A) :
    IsPGroup p (A.map (MulAut.conj : S →* MulAut S)) := by
  rintro ⟨_, a, ha, rfl⟩
  obtain ⟨k, hk⟩ := hA ⟨a, ha⟩
  refine ⟨k, Subtype.ext ?_⟩
  have h1 : a ^ p ^ k = 1 := congrArg Subtype.val hk
  show (MulAut.conj a) ^ p ^ k = 1
  rw [← map_pow, h1, map_one]

theorem comm_map_conj {S : Type*} [Group S] {A : Subgroup S}
    (hA : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) :
    ∀ e ∈ A.map (MulAut.conj : S →* MulAut S), ∀ f ∈ A.map (MulAut.conj : S →* MulAut S),
      e * f = f * e := by
  rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
  rw [← map_mul, ← map_mul, hA a ha b hb]

end LayerCores

section Chev


namespace LayerCores

theorem adjointGroup_isSimple_nonabelian {τ : Tag} (hτ : τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    (K : Type) [Field K] [Finite K] :
    IsSimpleGroup ↥(adjointGroup τ K) ∧ ∃ a b : ↥(adjointGroup τ K), a * b ≠ b * a := by
  have hq : CFSG.IsQuasisimple ↥(adjointGroup τ K) := by
    rcases hτ with rfl | rfl | rfl | rfl
    · exact CFSG.LieType.Steinberg.Adjoint.isQuasisimple_f4 K
    · exact CFSG.LieType.Simplicity.isQuasisimple_adjointGroup_e6 K
    · exact CFSG.LieType.Simplicity.isQuasisimple_adjointGroup_e7 K
    · exact CFSG.LieType.Steinberg.Adjoint.isQuasisimple_e8 K
  exact CFSG.HardMathSupport.Dickson.Sec6.I923.TriD4Aux.isSimple_of_isQuasisimple_center_bot hq
    CFSG.LieType.Chevalley.center_adjointGroup_eq_bot

theorem isChevSimple_adjointGroup_charTwo {τ : Tag}
    (hτ : τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) (K : Type) [Field K] [Finite K] [CharP K 2] :
    IsChevSimple 2 ↥(adjointGroup τ K) := by
  haveI := Fintype.ofFinite K
  obtain ⟨n, -, hn⟩ := FiniteField.card K 2
  let q₀ : TauCeti.PrimePower := ⟨2, n, Nat.prime_two, n.pos⟩
  have hk : Nat.card K = q₀.card := by
    rw [Nat.card_eq_fintype_card, hn, TauCeti.PrimePower.card_def]
  have hv0 : ∀ c : TauCeti.LieTypeIndex, c.InStandardRange → ¬ c.IsDuplicateRepresentative →
      c.Valid := fun c h1 h2 => (TauCeti.LieTypeIndex.valid_iff c).2 ⟨h1, h2⟩
  rcases hτ with rfl | rfl | rfl | rfl
  · have hv : (TauCeti.LieTypeIndex.F4 q₀).Valid := hv0 _ (by
      rw [TauCeti.LieTypeIndex.inStandardRange_iff]; trivial) (by
      rw [TauCeti.LieTypeIndex.isDuplicateRepresentative_iff]; exact fun h => h)
    obtain ⟨e⟩ := CFSG.Adapters.CatalogueFieldBridges.nonempty_adjointGroup_catEquiv
      (CFSG.TauCetiBridge.Even.chevalleyBridgesAll).f4 hv hk
    exact CFSG.HardMathSupport.Solomon.Coordinator.LieComp.isChevSimple_of_lie ⟨_, hv⟩
      (TauCeti.LieTypeIndex.characteristic_F4 q₀) e
  · have hv : (TauCeti.LieTypeIndex.E6 q₀).Valid := TauCeti.LieTypeIndex.valid_E6 q₀
    obtain ⟨e⟩ := CFSG.Adapters.CatalogueFieldBridges.nonempty_adjointGroup_catEquiv
      (CFSG.TauCetiBridge.Even.chevalleyBridgesAll).e6 hv hk
    exact CFSG.HardMathSupport.Solomon.Coordinator.LieComp.isChevSimple_of_lie ⟨_, hv⟩
      (TauCeti.LieTypeIndex.characteristic_E6 q₀) e
  · have hv : (TauCeti.LieTypeIndex.E7 q₀).Valid := TauCeti.LieTypeIndex.valid_E7 q₀
    obtain ⟨e⟩ := CFSG.Adapters.CatalogueFieldBridges.nonempty_adjointGroup_catEquiv
      (CFSG.TauCetiBridge.Even.chevalleyBridgesAll).e7 hv hk
    exact CFSG.HardMathSupport.Solomon.Coordinator.LieComp.isChevSimple_of_lie ⟨_, hv⟩
      (TauCeti.LieTypeIndex.characteristic_E7 q₀) e
  · have hv : (TauCeti.LieTypeIndex.E8 q₀).Valid := hv0 _ (by
      rw [TauCeti.LieTypeIndex.inStandardRange_iff]; trivial) (by
      rw [TauCeti.LieTypeIndex.isDuplicateRepresentative_iff]; exact fun h => h)
    obtain ⟨e⟩ := CFSG.Adapters.CatalogueFieldBridges.nonempty_adjointGroup_catEquiv
      (CFSG.TauCetiBridge.Even.chevalleyBridgesAll).e8 hv hk
    exact CFSG.HardMathSupport.Solomon.Coordinator.LieComp.isChevSimple_of_lie ⟨_, hv⟩
      (TauCeti.LieTypeIndex.characteristic_E8 q₀) e

theorem exists_subCoreFamily_of_chevSimple {S : Type} [Group S] [Finite S] (hS : IsSimpleGroup S)
    (hnc : ∃ a b : S, a * b ≠ b * a) (hchev : IsChevSimple 2 S) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (E : Subgroup (MulAut S)) (hEp : IsPGroup p E)
    (hEc : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a)
    (hZ : ∀ z ∈ CFSG.Open.GLALayer (I142.centFix E),
      (∀ y ∈ CFSG.Open.GLALayer (I142.centFix E), z * y = y * z) → z ^ 2 = 1 → z = 1) :
    ∃ (β : Type) (T : β → Subgroup S), IsSubCoreFamily (I142.centFix E) T :=
  exists_subCoreFamily_of_layer _
    (fun P hP hPp =>
      LayerAbelian.lieSemisimpleCentAbelian S hS hnc hchev p hp hp2 E hEp hEc P hP hPp)
    hZ

theorem exists_subCoreFamily_iff_layerCentre {S : Type} [Group S] [Finite S] (hS : IsSimpleGroup S)
    (hnc : ∃ a b : S, a * b ≠ b * a) (hchev : IsChevSimple 2 S) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (E : Subgroup (MulAut S)) (hEp : IsPGroup p E)
    (hEc : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a) :
    (∃ (β : Type) (T : β → Subgroup S), IsSubCoreFamily (I142.centFix E) T) ↔
      ∀ z ∈ CFSG.Open.GLALayer (I142.centFix E),
        (∀ y ∈ CFSG.Open.GLALayer (I142.centFix E), z * y = y * z) → z ^ 2 = 1 → z = 1 :=
  ⟨fun ⟨_, _, h⟩ => layerCentre_of_isSubCoreFamily h,
    exists_subCoreFamily_of_chevSimple hS hnc hchev hp hp2 E hEp hEc⟩

end LayerCores

end Chev

end CFSG.StandardType
