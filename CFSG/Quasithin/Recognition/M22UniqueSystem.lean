module

public import CFSG.Quasithin.Recognition.M22UniqueData
public import CFSG.Quasithin.Background.F3Paths

public section

namespace CFSG.Quasithin.Asc94

open MulAction CFSG.ComponentClassification.WittDesign
open scoped Pointwise

instance graphAction_top {H V : Type*} [Group H] [MulAction H V] :
    GraphAction H (⊤ : SimpleGraph V) where
  adj_smul g a b := by simp only [SimpleGraph.top_adj, ne_eq, smul_left_cancel_iff]

abbrev m22Hexad : Set (Fin 22) := ↑m22HexadF

abbrev m22HexStab : Subgroup M22 := stabilizer M22 m22Hexad

abbrev m22TwoStab : Subgroup M22 := stabilizer M22 (0 : Fin 22) ⊓ stabilizer M22 (1 : Fin 22)

abbrev m22PtHexStab : Subgroup M22 := stabilizer M22 (0 : Fin 22) ⊓ m22HexStab

theorem smul_m22_def (g : M22) (p : Fin 22) : g • p = (g : Equiv.Perm (Fin 22)) p := rfl

theorem mem_m22HexStab_iff {g : M22} :
    g ∈ m22HexStab ↔ PresHex (g : Equiv.Perm (Fin 22)) := by
  rw [MulAction.mem_stabilizer_set]
  simp only [PresHex, Finset.mem_coe, smul_m22_def]

theorem exists_fix_zero
    {w : Fin 22} (hw : w ∈ m22HexadF) (hw0 : w ≠ 0) :
    ∃ i ∈ m22HexStab ⊓ stabilizer M22 (0 : Fin 22), i • (1 : Fin 22) = w := by
  obtain ⟨⟨a0, a1, ah⟩, ⟨b0, b1, bh⟩, ⟨c0, c1, ch⟩, ⟨d0, d1, dh⟩⟩ := m22Fix_spec
  have mk : ∀ {i : M22}, PresHex (i : Equiv.Perm (Fin 22)) → (i : Equiv.Perm (Fin 22)) 0 = 0 →
      i ∈ m22HexStab ⊓ stabilizer M22 (0 : Fin 22) := fun h h0 =>
    Subgroup.mem_inf.mpr ⟨mem_m22HexStab_iff.mpr h,
      MulAction.mem_stabilizer_iff.mpr ((smul_m22_def _ _).trans h0)⟩
  simp only [m22HexadF, Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd rfl hw0
  · exact ⟨1, one_mem _, one_smul _ _⟩
  · exact ⟨m22Fix2, mk ah a0, (smul_m22_def _ _).trans a1⟩
  · exact ⟨m22Fix9, mk bh b0, (smul_m22_def _ _).trans b1⟩
  · exact ⟨m22Fix17, mk ch c0, (smul_m22_def _ _).trans c1⟩
  · exact ⟨m22Fix19, mk dh d0, (smul_m22_def _ _).trans d1⟩

theorem card_m22TwoStab :
    Nat.card m22TwoStab = 960 := by
  rw [← count_two_point, ← card_m22_subtype]
  refine Nat.card_congr (Equiv.subtypeEquivRight fun g => ?_)
  simp only [Subgroup.mem_inf, MulAction.mem_stabilizer_iff, Subgroup.smul_def,
    Equiv.Perm.smul_def]

theorem presHex_iff_mapsTo (σ : Equiv.Perm (Fin 22)) :
    PresHex σ ↔ ∀ p ∈ m22HexadL, σ p ∈ m22HexadL := by
  simp only [mem_m22HexadL_iff]
  constructor
  · intro h p hp; exact (h p).mpr hp
  · intro h p
    refine ⟨fun hσp => ?_, h p⟩
    have hsub : m22HexadF.map σ.toEmbedding ⊆ m22HexadF := by
      intro q hq
      obtain ⟨r, hr, rfl⟩ := Finset.mem_map.mp hq
      exact h r hr
    have heq := Finset.eq_of_subset_of_card_le hsub (by rw [Finset.card_map])
    rw [← heq] at hσp
    obtain ⟨r, hr, hrp⟩ := Finset.mem_map.mp hσp
    have hrp' : σ r = σ p := hrp
    rwa [← σ.injective hrp']

theorem card_m22TwoStab_hexad :
    Nat.card ((m22HexStab).subgroupOf m22TwoStab) = 192 := by
  rw [← count_two_point_hexad, ← card_m22_subtype]
  refine Nat.card_congr ((Equiv.subtypeSubtypeEquivSubtypeInter (fun x : M22 => x ∈ m22TwoStab)
    (fun x => x ∈ m22HexStab)).trans (Equiv.subtypeEquivRight fun g => ?_))
  rw [mem_m22HexStab_iff, presHex_iff_mapsTo]
  simp only [Subgroup.mem_inf, MulAction.mem_stabilizer_iff, Subgroup.smul_def,
    Equiv.Perm.smul_def, and_assoc]

end CFSG.Quasithin.Asc94
