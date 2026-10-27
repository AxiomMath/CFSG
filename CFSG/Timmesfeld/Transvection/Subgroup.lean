module

public import CFSG.Timmesfeld.Transvection.Statement
public import CFSG.Timmesfeld.ARS.Sec8Restrict

public section

namespace CFSG.Timmesfeld.Transvection

open CFSG.Timmesfeld.ARS CFSG.LieType CFSG.LieType.Universal CFSG.LieType.BorelTits
  CFSG.Assembly.LowTwoRank

@[expose] def SubgroupTransvectionStatement : Prop :=
  ∀ (G : Type) [Group G] (V : Subgroup G) (Δ : Set (Subgroup G)), (∀ X ∈ Δ, X ≤ V) →
    TransvectionHyp ↥V (restrict Δ V) →
    ∃ f : ℕ, ∃ hf : 1 ≤ f, (∀ A ∈ Δ, Nat.card A = 2 ^ f) ∧
      ((∃ n : ℕ, ∃ hn : 2 ≤ n, ∃ Φ : ↥(StatedSp n (GaloisField 2 f)) →* G,
          Function.Injective Φ ∧ Φ.range = V ∧ ∀ X : Subgroup G, X ∈ Δ ↔
            ∃ g, X = (conjSub ((Symplectic.rootDatum n (GaloisField 2 f)).rootGroup
              (Pi.single (⟨n - 1, by omega⟩ : Fin n) 1)) g).map Φ) ∨
        (∃ m : ℕ, ∃ hm : 4 ≤ m,
          ∃ Φ : ↥(Unitary.SU (unitaryInvolution (GaloisField 2 (2 * f)) 2 f) m) →* G,
            Φ.ker = Subgroup.center _ ∧ Φ.range = V ∧ ∀ X : Subgroup G, X ∈ Δ ↔
              ∃ g, X = (conjSub ((Unitary.rootDatum (card_galoisField_two_mul hf) m).rootGroup
                (unitaryLongRoot m (by omega))) g).map Φ))

namespace SubgroupForm

variable {G : Type} [Group G] {V : Subgroup G} {Δ : Set (Subgroup G)}

theorem map_subtype_mem {X' : Subgroup V} (hX' : X' ∈ restrict Δ V) :
    X'.map V.subtype ∈ Δ := by
  obtain ⟨B, ⟨hB, hBV⟩, rfl⟩ := hX'
  rwa [Subgroup.map_subgroupOf_eq_of_le hBV]

theorem subgroupOf_mem {X : Subgroup G} (hX : X ∈ Δ) (hXV : X ≤ V) :
    X.subgroupOf V ∈ restrict Δ V :=
  ⟨X, ⟨hX, hXV⟩, rfl⟩

theorem mem_iff_of_restrict {K : Type*} [Group K] (hΔV : ∀ X ∈ Δ, X ≤ V) (Φ : K →* V)
    (T : Subgroup K)
    (hΦ : ∀ X' : Subgroup V, X' ∈ restrict Δ V ↔ ∃ g, X' = (conjSub T g).map Φ)
    (X : Subgroup G) : X ∈ Δ ↔ ∃ g, X = (conjSub T g).map (V.subtype.comp Φ) := by
  constructor
  · intro hX
    obtain ⟨g, hg⟩ := (hΦ _).1 (subgroupOf_mem hX (hΔV X hX))
    refine ⟨g, ?_⟩
    rw [← Subgroup.map_map, ← hg, Subgroup.map_subgroupOf_eq_of_le (hΔV X hX)]
  · rintro ⟨g, rfl⟩
    rw [← Subgroup.map_map]
    exact map_subtype_mem ((hΦ _).2 ⟨g, rfl⟩)

theorem ker_subtype_comp {K : Type*} [Group K] (Φ : K →* V) :
    (V.subtype.comp Φ).ker = Φ.ker := by
  ext x
  simp only [MonoidHom.mem_ker, MonoidHom.coe_comp, Function.comp_apply, Subgroup.coe_subtype,
    OneMemClass.coe_eq_one]

theorem range_subtype_comp {K : Type*} [Group K] {Φ : K →* V} (hΦ : Function.Surjective Φ) :
    (V.subtype.comp Φ).range = V := by
  rw [MonoidHom.range_comp, MonoidHom.range_eq_top.2 hΦ, ← MonoidHom.range_eq_map,
    Subgroup.range_subtype]

end SubgroupForm

open SubgroupForm in
theorem subgroupTransvectionStatement_of (h : TransvectionStatement) :
    SubgroupTransvectionStatement := by
  intro G _ V Δ hΔV hV
  obtain ⟨f, hf, hcard, hcon⟩ := h ↥V (restrict Δ V) hV
  refine ⟨f, hf, fun A hA => ?_, ?_⟩
  · rw [← hcard _ (subgroupOf_mem hA (hΔV A hA))]
    exact (Nat.card_congr (Subgroup.subgroupOfEquivOfLe (hΔV A hA)).toEquiv).symm
  rcases hcon with ⟨n, hn, Φ, hΦ, hmem⟩ | ⟨m, hm, Φ, hΦ, hker, hmem⟩
  · exact Or.inl ⟨n, hn, V.subtype.comp Φ, V.subtype_injective.comp hΦ.1,
      range_subtype_comp hΦ.2, mem_iff_of_restrict hΔV Φ _ hmem⟩
  · exact Or.inr ⟨m, hm, V.subtype.comp Φ, (ker_subtype_comp Φ).trans hker,
      range_subtype_comp hΦ, mem_iff_of_restrict hΔV Φ _ hmem⟩

end CFSG.Timmesfeld.Transvection
