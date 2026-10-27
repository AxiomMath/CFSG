module

public import CFSG.Quasithin.Vol2.Ch11SecA13Basic
public import CFSG.Quasithin.Vol2.Ch11SecA15Q

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecA

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13 CFSG.QuasithinUnique
open scoped commutatorElement

variable {G : Type} [Group G]

theorem mem_normalizer_commutator {A B : Subgroup G} {x : G}
    (hA : x ∈ Subgroup.normalizer (A : Set G)) (hB : x ∈ Subgroup.normalizer (B : Set G)) :
    x ∈ Subgroup.normalizer ((⁅A, B⁆ : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq] at *
  rw [Subgroup.map_commutator, hA, hB]

theorem L_le_normalizer_blockU (L : Subgroup G) :
    L ≤ Subgroup.normalizer (blockU L : Set G) := fun _ hl =>
  mem_normalizer_commutator (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 L hl)
    (Subgroup.le_normalizer hl)

theorem L_le_normalizer_blockZ (L : Subgroup G) :
    L ≤ Subgroup.normalizer (blockZ L : Set G) := fun _ hl =>
  Subgroup.inf_normalizer_le_normalizer_inf
    ⟨L_le_normalizer_blockU L hl, mem_normalizer_centralizer (Subgroup.le_normalizer hl)⟩

variable [Finite G] {T L I : Subgroup G} {n : ℕ}

theorem fsuV_le_pCoreOf_L (h1102 : Stmt11_0_2) (h : Hyp11 G T L I n) :
    fsuV T I ≤ pCoreOf 2 L :=
  CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 (fsuV_le_L h1102 h)
    (L_le_normalizer_fsuV h) (isPGroup_fsuV h)

theorem fsuV_le_blockU (h1102 : Stmt11_0_2) (h : Hyp11 G T L I n) : fsuV T I ≤ blockU L := by
  obtain ⟨_, hirr, -, -, -⟩ := h1102 G T L I n h
  rw [← hirr.2.2.2.1]
  exact Subgroup.commutator_mono (fsuV_le_pCoreOf_L h1102 h) le_rfl

theorem fsuV_sup_blockZ (h1102 : Stmt11_0_2) (h : Hyp11 G T L I n) (hS : IsShort2 L) :
    fsuV T I ⊔ blockZ L = blockU L := by
  obtain ⟨_, hirr, -, -, -⟩ := h1102 G T L I n h
  rcases hS.2.2.2.2.2 (fsuV T I ⊔ blockZ L) le_sup_right
      (sup_le (fsuV_le_blockU h1102 h) inf_le_left)
      (fun l hl => mem_normalizer_sup (L_le_normalizer_fsuV h hl) (L_le_normalizer_blockZ L hl))
    with h0 | h0
  · exfalso
    have hVZ : fsuV T I ≤ Subgroup.centralizer (L : Set G) :=
      (le_sup_left.trans h0.le).trans inf_le_right
    have hbot : ⁅fsuV T I, L⁆ = ⊥ := by
      rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
      exact hVZ
    exact fsuV_ne_bot h (hirr.2.2.2.1.symm.trans hbot)
  · exact h0

theorem blockZ_le_centralizer_fsuV (h1102 : Stmt11_0_2) (h : Hyp11 G T L I n)
    (hS : IsShort2 L) : blockZ L ≤ Subgroup.centralizer (fsuV T I : Set G) := by
  intro z hz
  rw [Subgroup.mem_centralizer_iff]
  intro v hv
  exact (Subgroup.mem_centralizer_iff.mp (hS.2.2.1.1 hz.1).2 v
    (fsuV_le_pCoreOf_L h1102 h hv))

theorem commutator_blockU_eq (h1102 : Stmt11_0_2) (h : Hyp11 G T L I n) (hS : IsShort2 L) :
    ⁅blockU L, L⁆ = fsuV T I := by
  obtain ⟨_, hirr, -, -, -⟩ := h1102 G T L I n h
  apply le_antisymm
  · rw [Subgroup.commutator_le]
    intro u hu l hl
    have hu' : u ∈ ((fsuV T I ⊔ blockZ L : Subgroup G) : Set G) := by
      rw [fsuV_sup_blockZ h1102 h hS]; exact hu
    rw [Subgroup.coe_mul_of_right_le_normalizer_left _ _
      ((blockZ_le_centralizer_fsuV h1102 h hS).trans
        (Subgroup.centralizer_le_normalizer _))] at hu'
    obtain ⟨v, hv, z, hz, rfl⟩ := hu'
    have hzl : z * l = l * z := (Subgroup.mem_centralizer_iff.mp hz.2 l hl).symm
    have : ⁅v * z, l⁆ = ⁅v, l⁆ := by
      rw [commutatorElement_def, commutatorElement_def]
      calc v * z * l * (v * z)⁻¹ * l⁻¹ = v * (z * l) * z⁻¹ * v⁻¹ * l⁻¹ := by group
        _ = v * (l * z) * z⁻¹ * v⁻¹ * l⁻¹ := by rw [hzl]
        _ = v * l * v⁻¹ * l⁻¹ := by group
    rw [this, ← hirr.2.2.2.1]
    exact Subgroup.commutator_mem_commutator hv hl
  · calc fsuV T I = ⁅fsuV T I, L⁆ := hirr.2.2.2.1.symm
      _ ≤ ⁅blockU L, L⁆ := Subgroup.commutator_mono (fsuV_le_blockU h1102 h) le_rfl

theorem normalizer_le_normalizer_fsuV (h1102 : Stmt11_0_2) (h : Hyp11 G T L I n)
    (hS : IsShort2 L) :
    Subgroup.normalizer (L : Set G) ≤ Subgroup.normalizer (fsuV T I : Set G) := by
  intro x hx
  rw [← commutator_blockU_eq h1102 h hS]
  exact mem_normalizer_commutator (mem_normalizer_commutator
    (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 L hx) hx) hx

theorem fsuV_eq_VM (h1102 : Stmt11_0_2) (h : Hyp11 G T L I n) (hS : IsShort2 L) :
    fsuV T I = VM T L I :=
  (conjClosure_eq_of_le_normalizer (normalizer_le_normalizer_fsuV h1102 h hS)).symm

theorem blockZ_le (h : Hyp11 G T L I n) :
    blockZ L ≤ T ⊓ Subgroup.centralizer (L : Set G) := by
  have hQ : blockU L ≤ pCoreOf 2 L :=
    Subgroup.le_normalizer_iff_commutator_le_left.mp
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 L)
  exact le_inf (inf_le_left.trans (hQ.trans
    ((CFSG.Quasithin.pCoreOf_le_of_isSylowTwoOf (isSylowTwoOf_inf_L h)).trans inf_le_left)))
    inf_le_right

theorem blockU_eq_of (h1102 : Stmt11_0_2) (h : Hyp11 G T L I n) (hS : IsShort2 L)
    (hC : T ⊓ Subgroup.centralizer (L : Set G) = ⊥) : blockU L = fsuV T I := by
  have hZ : blockZ L = ⊥ := le_bot_iff.mp (hC ▸ blockZ_le h)
  rw [← fsuV_sup_blockZ h1102 h hS, hZ, sup_bot_eq]

end CFSG.Quasithin.Vol2.Ch11.SecA
