module

public import CFSG.Sporadic.Fi24.Out
public import CFSG.Sporadic.Fi24.Complete

public section

namespace CFSG.Sporadic.Fi24

open CFSG.Blueprint.Fischer CFSG.Fischer

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

@[expose] def ExistenceF24 (G : Type) [Group G] (D : Set G) : Prop :=
  Subgroup.center G = ⊥ ∧ IsSimpleGroup (commutator G) ∧ HasType 2 G D ∧
    (∀ E : Set G, Pair G E → E = D) ∧ ∀ d ∈ D, LocalStructureAt 2 d

theorem ExistenceF24.congr {G H : Type} [Group G] [Group H] {D : Set G} (h : ExistenceF24 G D)
    (φ : G ≃* H) : ExistenceF24 H (φ '' D) := by
  obtain ⟨hZ, hS, hT, hU, hL⟩ := h
  refine ⟨?_, ?_, hasType_map hT φ, fun E hE => ?_, ?_⟩
  · rw [eq_bot_iff]
    intro z hz
    have h : φ.symm z ∈ Subgroup.center G := by
      rw [Subgroup.mem_center_iff] at hz ⊢
      intro g
      apply φ.injective
      rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
      exact hz (φ g)
    rw [hZ, Subgroup.mem_bot] at h
    rw [Subgroup.mem_bot]
    simpa using congrArg φ h
  · let e : commutator G ≃* commutator H :=
      ((commutator G).equivMapOfInjective (φ : G →* H) φ.injective).trans
        (MulEquiv.subgroupCongr (map_commutator_mulEquiv φ))
    exact e.symm.isSimpleGroup
  · have h1 := hU _ (pair_map hE φ.symm)
    rw [← h1, ← Set.image_comp]
    simp
  · rintro _ ⟨d, hd, rfl⟩
    exact (hL d hd).map φ

theorem existence_R
    (hPF : PolarFacts) : ExistenceF24 R D24 :=
  ⟨center_R, isSimpleGroup_commutator_R, f24_R, pair_eq_D24 hPF,
    fun _ hx => localStructureAt_of_mem hx⟩

section Carrier

variable (hPF : PolarFacts) (hHF : HyperovalFacts) (hFF : Fi22Facts)
  {tr cs : Set (Set Fi23.D23)} {r : tr} (hTF : Fi23Facts tr cs r)
  (hfix22 : ∀ g : Fi22.J, g ^ 2 = 1 → g ≠ 1 →
    Nat.card {x : Fi22.D // g * (x : Fi22.J) * g⁻¹ = x} ∈ ({54, 182, 694} : Set ℕ))
  (hcent22 : ∀ (χ : Fi22.D) (σ : Equiv.Perm Fi22.D),
    (∀ g : Fi22.J, g * χ = χ * g →
      σ * Pair.conjPerm Fi22.pair_D g = Pair.conjPerm Fi22.pair_D g * σ) →
    σ = 1 ∨ σ = Pair.conjPerm Fi22.pair_D (χ : Fi22.J))
  {e : J} (he : EdgeSwap e) {d1 t2 : Fi23.J} (hd1 : d1 ∈ LocalClass Fi23.D23 Fi23.d)
  (hcover : ∀ g : Fi23.J, g ^ 2 = 1 → g ≠ 1 →
    IsConj Fi23.d g ∨ IsConj (Fi23.d * d1) g ∨ IsConj t2 g)

@[expose] noncomputable def rEquivAut :
    R ≃* MulAut Blueprint.NativeSporadic.Fi24prime :=
  (mulAutEquivR (pow_mem_innerAut_J hPF hfix22 hcent22 he hd1 hcover)
    (complete_R hPF hHF hFF hTF)).trans
      (MulAut.congr (G := J) (H := Blueprint.NativeSporadic.Fi24prime) fi24EquivJ.symm)

noncomputable abbrev D24c :
    Set (Carrier 2) :=
  rEquivAut hPF hHF hFF hTF hfix22 hcent22 he hd1 hcover '' D24

theorem existence_native :
    ExistenceF24 (MulAut Blueprint.NativeSporadic.Fi24prime)
      (rEquivAut hPF hHF hFF hTF hfix22 hcent22 he hd1 hcover '' D24) :=
  (existence_R hPF).congr _

set_option maxRecDepth 100000 in
theorem carrierGroup_two :
    carrierGroup 2 = (inferInstance : Group (MulAut Blueprint.NativeSporadic.Fi24prime)) :=
  rfl

theorem existence_carrier :
    @ExistenceF24 (Carrier 2) (carrierGroup 2)
      (D24c hPF hHF hFF hTF hfix22 hcent22 he hd1 hcover) := by
  rw [carrierGroup_two]
  exact existence_native hPF hHF hFF hTF hfix22 hcent22 he hd1 hcover

include hPF hHF hFF hTF hfix22 hcent22 he hd1 hcover in
theorem fischer_existence_two :
    Subgroup.center (Carrier 2) = ⊥ ∧ IsSimpleGroup (commutator (Carrier 2)) ∧
      ∃ D : Set (Carrier 2), HasType 2 (Carrier 2) D ∧
        (∀ E : Set (Carrier 2), Pair (Carrier 2) E → E = D) ∧ LocalStructure 2 D := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := existence_carrier hPF hHF hFF hTF hfix22 hcent22 he hd1 hcover
  exact ⟨h1, h2, _, h3, h4, h5⟩

theorem fischer_uniqueness_two
    (X : Type) [Group X] (E : Set X) (_hP : Pair X E)
    (hZ : Subgroup.center X = ⊥) (hS : IsSimpleGroup (commutator X)) (hT : HasType 2 X E) :
    ∃ iso : X ≃* Carrier 2, iso '' E = D24c hPF hHF hFF hTF hfix22 hcent22 he hd1 hcover := by
  obtain ⟨hZ0, hS0, hT0, -, -⟩ := existence_carrier hPF hHF hFF hTF hfix22 hcent22 he hd1 hcover
  exact F24.exists_mulEquiv hPF hHF hFF hTF (hT : F24 X E) hT0 hZ hZ0 hS hS0

end Carrier

end CFSG.Sporadic.Fi24
