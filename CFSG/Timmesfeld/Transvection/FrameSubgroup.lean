module

public import CFSG.Timmesfeld.Transvection.Frame
public import CFSG.Timmesfeld.Transvection.Subgroup

public section

namespace CFSG.Timmesfeld.Transvection

open CFSG.Timmesfeld.ARS CFSG.LieType CFSG.LieType.Universal CFSG.LieType.BorelTits
  CFSG.Assembly.LowTwoRank

@[expose] def SubgroupTransvectionStatementFrame : Prop :=
  ∀ (G : Type) [Group G] (V : Subgroup G) (Δ : Set (Subgroup G)), (∀ X ∈ Δ, X ≤ V) →
    TransvectionHyp ↥V (restrict Δ V) → MeetsLines Δ →
    ∀ (r : ℕ) (hr : 2 ≤ r) (P Q : Fin r → Subgroup G) (k : Fin r), IsSmallFrame Δ P Q k →
      ∃ f : ℕ, ∃ hf : 1 ≤ f, (∀ A ∈ Δ, Nat.card A = 2 ^ f) ∧
        ((∃ Φ : ↥(StatedSp r (GaloisField 2 f)) →* G, Function.Injective Φ ∧ Φ.range = V ∧
            ∀ X : Subgroup G, X ∈ Δ ↔ ∃ g, X = (conjSub ((Symplectic.rootDatum r
              (GaloisField 2 f)).rootGroup (Pi.single (⟨r - 1, by omega⟩ : Fin r) 1)) g).map Φ) ∨
          (∃ Φ : ↥(Unitary.SU (unitaryInvolution (GaloisField 2 (2 * f)) 2 f) (2 * r)) →* G,
            Φ.ker = Subgroup.center _ ∧ Φ.range = V ∧ ∀ X : Subgroup G, X ∈ Δ ↔
              ∃ g, X = (conjSub ((Unitary.rootDatum (card_galoisField_two_mul hf)
                (2 * r)).rootGroup (unitaryLongRoot (2 * r) (by omega))) g).map Φ))

namespace SubgroupForm

variable {G : Type*} [Group G] {V : Subgroup G} {Δ : Set (Subgroup G)}

theorem commuting_subgroupOf_iff' {B C : Subgroup G} (hB : B ≤ V) (hC : C ≤ V) :
    Commuting (B.subgroupOf V) (C.subgroupOf V) ↔ Commuting B C := by
  rw [Restrict.commuting_subgroupOf_iff, inf_of_le_left hB, inf_of_le_left hC]

theorem meetsLines_restrict (hΔV : ∀ X ∈ Δ, X ≤ V) (h : MeetsLines Δ) :
    MeetsLines (restrict Δ V) := by
  rintro _ ⟨A, ⟨hA, hAV⟩, rfl⟩ _ ⟨B, ⟨hB, hBV⟩, rfl⟩ hAB hc _ ⟨C, ⟨hC, hCV⟩, rfl⟩
  have hAB' : A ≠ B := fun e => hAB (e ▸ rfl)
  obtain ⟨D, ⟨hD, hDl⟩, hCD⟩ := h A hA B hB hAB' ((commuting_subgroupOf_iff' hAV hBV).1 hc) C hC
  have hDV := hΔV D hD
  refine ⟨D.subgroupOf V, ⟨⟨D, ⟨hD, hDV⟩, rfl⟩, ?_⟩,
    (commuting_subgroupOf_iff' hCV hDV).2 hCD⟩
  rintro _ ⟨X, ⟨hX, hXV⟩, rfl⟩ hXA hXB
  exact (commuting_subgroupOf_iff' hXV hDV).2 (hDl X hX ((commuting_subgroupOf_iff' hXV hAV).1 hXA)
    ((commuting_subgroupOf_iff' hXV hBV).1 hXB))

theorem isSmallFrame_restrict (hΔV : ∀ X ∈ Δ, X ≤ V) {r : ℕ} {P Q : Fin r → Subgroup G}
    {k : Fin r} (h : IsSmallFrame Δ P Q k) :
    IsSmallFrame (restrict Δ V) (fun i => (P i).subgroupOf V) (fun i => (Q i).subgroupOf V) k := by
  have hP : ∀ i, P i ≤ V := fun i => hΔV _ (h.memP i)
  have hQ : ∀ i, Q i ≤ V := fun i => hΔV _ (h.memQ i)
  refine ⟨⟨fun i => ⟨P i, ⟨h.memP i, hP i⟩, rfl⟩, fun i => ⟨Q i, ⟨h.memQ i, hQ i⟩, rfl⟩,
    fun i => Restrict.opposite_subgroupOf (hP i) (hQ i) (h.opposite i), fun i j hij => ?_⟩, ?_⟩
  · rw [← Subgroup.subgroupOf_sup (hP i) (hQ i), ← Subgroup.subgroupOf_sup (hP j) (hQ j),
      commuting_subgroupOf_iff' (sup_le (hP i) (hQ i)) (sup_le (hP j) (hQ j))]
    exact h.commuting i j hij
  · rintro _ ⟨X, ⟨hX, hXV⟩, rfl⟩ hXc
    have hle := h.residue X hX fun i hi =>
      ⟨(commuting_subgroupOf_iff' hXV (hP i)).1 (hXc i hi).1,
        (commuting_subgroupOf_iff' hXV (hQ i)).1 (hXc i hi).2⟩
    simp only
    rw [← Subgroup.subgroupOf_sup (hP k) (hQ k)]
    intro x hx
    exact Subgroup.mem_subgroupOf.2 (hle (Subgroup.mem_subgroupOf.1 hx))

end SubgroupForm

open SubgroupForm in
theorem subgroupTransvectionStatementFrame_of (h : TransvectionStatementFrame) :
    SubgroupTransvectionStatementFrame := by
  intro G _ V Δ hΔV hV hlines r hr P Q k hfr
  obtain ⟨f, hf, hcard, hcon⟩ := h ↥V (restrict Δ V) hV (meetsLines_restrict hΔV hlines) r hr _ _
    k (isSmallFrame_restrict hΔV hfr)
  refine ⟨f, hf, fun A hA => ?_, ?_⟩
  · rw [← hcard _ (subgroupOf_mem hA (hΔV A hA))]
    exact (Nat.card_congr (Subgroup.subgroupOfEquivOfLe (hΔV A hA)).toEquiv).symm
  rcases hcon with ⟨Φ, hΦ, hmem⟩ | ⟨Φ, hΦ, hker, hmem⟩
  · exact Or.inl ⟨V.subtype.comp Φ, V.subtype_injective.comp hΦ.1,
      range_subtype_comp hΦ.2, mem_iff_of_restrict hΔV Φ _ hmem⟩
  · exact Or.inr ⟨V.subtype.comp Φ, (ker_subtype_comp Φ).trans hker,
      range_subtype_comp hΦ, mem_iff_of_restrict hΔV Φ _ hmem⟩

end CFSG.Timmesfeld.Transvection
