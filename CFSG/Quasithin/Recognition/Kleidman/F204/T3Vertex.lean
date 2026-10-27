module

public import CFSG.Quasithin.Recognition.Kleidman.F204.T3Fix
public import CFSG.Quasithin.Recognition.Kleidman.F204.LocalDich
public import CFSG.Quasithin.Recognition.Kleidman.F204.LocalPath
public import CFSG.Quasithin.Recognition.Kleidman.F204.T3F2a

public section

namespace CFSG.Quasithin.Kleidman.F204

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin CFSG.Quasithin.F7
  CFSG.Quasithin.FA5 CFSG.Quasithin.F53 CFSG.Quasithin.CosetGeom
  CFSG.QuasithinUnique.A5.Delta5

open scoped commutatorElement

set_option linter.unusedSectionVars false

variable {G : Type} [Group G] [Finite G] {L1 L2 S D X : Subgroup G}

section Vertex3

variable (F : Frame L1 L2 S D X)
include F

theorem relIndex_Qv_inf_Qv {x δ : Geo (P1 L1 L2 S) (P2 L1 L2 S)} (hx : vtype x = true)
    (hδ : δ ∈ nbrs x) : (Qv δ ⊓ Qv x).relIndex (Qv δ) = 4 := by
  have h₁ : P1 L1 L2 S ≤ P1 L1 L2 S ⊔ P2 L1 L2 S := le_sup_left
  have h₂ : P2 L1 L2 S ≤ P1 L1 L2 S ⊔ P2 L1 L2 S := le_sup_right
  obtain ⟨g, hg1, hg0⟩ := exists_edge_conj_true hx hδ
  have hQx : Qv x = conjSub (g : G) (Q2 L1 L2 S) := by
    rw [← hg1, Qv_smul]; unfold Qv; rw [stab_γ₁ h₂]
  have hQδ : Qv δ = conjSub (g : G) (Q1 L1 L2 S) := by
    rw [← hg0, Qv_smul]; unfold Qv; rw [stab_γ₀ h₁]
  rw [hQx, hQδ, ← conjSub_inf, relIndex_conjSub]
  have h := card_Q1 F
  have h2 := Subgroup.relIndex_mul_card (H := Q1 L1 L2 S ⊓ Q2 L1 L2 S) (K := Q1 L1 L2 S)
  rw [inf_eq_left.mpr (inf_le_left : Q1 L1 L2 S ⊓ Q2 L1 L2 S ≤ Q1 L1 L2 S)] at h2
  have hpos : 0 < Nat.card (Q1 L1 L2 S ⊓ Q2 L1 L2 S : Subgroup G) := Nat.card_pos
  nlinarith


theorem fix_three_vertex {x δ : Geo (P1 L1 L2 S) (P2 L1 L2 S)} (hx : vtype x = true)
    (hδ : δ ∈ nbrs x) {A : Subgroup G} (hAx : A ≤ stab x)
    (hA : IsPGroup 2 (A.subgroupOf (stab x)))
    (hAnt : ∃ a ∈ A, ∃ v ∈ Zv x, a * v ≠ v * a)
    (hidx : (Zv x ⊓ Subgroup.centralizer (A : Set G)).relIndex (Zv x) ≤ (A ⊓ Qv x).relIndex A)
    {r : G} (hrx : r ∈ stab x) (hrδ : r ∈ stab δ) (hr3 : r ^ 3 = 1) (hrQ : r ∉ Qv x) :
    ∀ v ∈ Zv x, r * v = v * r → v ∈ Subgroup.centralizer (stab x : Set G) := by
  have hA' := Amal.of_frame F
  obtain ⟨φ, hφs, hφk⟩ := exists_phi_stab F hx
  have hV2 : ∀ a ∈ Zv x, a * a = 1 := fun a ha => by
    rw [← pow_two]
    exact (hA'.isElemAbelian_Zv x).2 a ha
  have hLV : stab x ≤ Subgroup.normalizer (Zv x : Set G) := hA'.stab_le_normalizer_Zv x
  have hker : ∀ l : ↥(stab x), φ l = 1 → (l : G) ∈ Subgroup.centralizer (Zv x : Set G) := by
    intro l hl
    have hlk : l ∈ φ.ker := MonoidHom.mem_ker.mpr hl
    rw [hφk] at hlk
    exact Qv_le_centralizer_Zv F x (Subgroup.mem_subgroupOf.mp hlk)
  have hbridge : ∀ B : Subgroup G, B ≤ stab x →
      (B ⊓ Qv x).relIndex B = Nat.card ((B.subgroupOf (stab x)).map φ) := by
    intro B hB
    calc (B ⊓ Qv x).relIndex B = (Qv x).relIndex B := by
          rw [inf_comm]; exact Subgroup.inf_relIndex_right (H := Qv x) (K := B)
      _ = ((Qv x).subgroupOf (stab x)).relIndex (B.subgroupOf (stab x)) :=
          (Subgroup.relIndex_subgroupOf hB).symm
      _ = φ.ker.relIndex (B.subgroupOf (stab x)) := by rw [hφk]
      _ = Nat.card ((B.subgroupOf (stab x)).map φ) := Subgroup.relIndex_ker _ φ
  have hmapB : ∀ B : Subgroup G, B ≤ stab x →
      ((B.subgroupOf (stab x)).map (stab x).subtype : Subgroup G) = B := by
    intro B hB
    rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hB]
  have hnc : ∃ l : ↥(stab x), ∃ v ∈ Zv x, ¬ Commute (l : G) v := by
    obtain ⟨a, haA, v, hv, hne⟩ := hAnt
    exact ⟨⟨a, hAx haA⟩, v, hv, hne⟩
  have hAnt' : ∃ a ∈ A.subgroupOf (stab x), ∃ v ∈ Zv x, (a : G) * v ≠ v * (a : G) := by
    obtain ⟨a, haA, v, hv, hne⟩ := hAnt
    exact ⟨⟨a, hAx haA⟩, Subgroup.mem_subgroupOf.mpr haA, v, hv, hne⟩
  have hidx' : (Zv x ⊓ Subgroup.centralizer
      (((A.subgroupOf (stab x)).map (stab x).subtype : Subgroup G) : Set G)).relIndex (Zv x) ≤
      Nat.card ((A.subgroupOf (stab x)).map φ) := by
    rw [hmapB A hAx, ← hbridge A hAx]
    exact hidx
  obtain ⟨h16, -, hC4, -⟩ := fa5_ff_card' hV2 hLV φ hφs hker hA hAnt' hidx'
  obtain ⟨-, -, hC4all, hmeet⟩ := fa5_ff_all' hV2 hLV φ hφs hker hA hAnt' hidx'
  set T₁ : Subgroup ↥(stab x) := (Qv δ).subgroupOf (stab x) with hT₁
  have hQδx : Qv δ ≤ stab x := (Amal.of_frame F).Qv_le_stab_of_mem_nbrs (mem_nbrs_symm hδ)
  have hT₁4 : Nat.card (T₁.map φ) = 4 := by
    rw [← hbridge (Qv δ) hQδx]
    exact relIndex_Qv_inf_Qv F hx hδ
  set r' : ↥(stab x) := ⟨r, hrx⟩ with hr'
  have hr'3 : r' ^ 3 = 1 := Subtype.ext (by simpa using hr3)
  have hr'1 : φ r' ≠ 1 := by
    intro h1
    have : r' ∈ φ.ker := MonoidHom.mem_ker.mpr h1
    rw [hφk] at this
    exact hrQ (Subgroup.mem_subgroupOf.mp this)
  have hrQδ : ∀ t ∈ Qv δ, r * t * r⁻¹ ∈ Qv δ := fun t ht =>
    (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 (stab δ) hrδ) t).mp ht
  have hrT : φ r' ∈ Subgroup.normalizer ((T₁.map φ : Subgroup (alternatingGroup (Fin 5))) :
      Set (alternatingGroup (Fin 5))) := by
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · rintro ⟨t, ht, rfl⟩
      have ht' : (t : G) ∈ Qv δ := ht
      refine ⟨r' * t * r'⁻¹, ?_, by simp⟩
      show ((r' * t * r'⁻¹ : ↥(stab x)) : G) ∈ Qv δ
      have e : ((r' * t * r'⁻¹ : ↥(stab x)) : G) = r * t * r⁻¹ := by simp [hr']
      rw [e]; exact hrQδ _ ht'
    · rintro ⟨t, ht, hty⟩
      have ht' : (t : G) ∈ Qv δ := ht
      have h2 : (r⁻¹ : G) ∈ stab δ := (stab δ).inv_mem hrδ
      refine ⟨r'⁻¹ * t * r', ?_, ?_⟩
      · show ((r'⁻¹ * t * r' : ↥(stab x)) : G) ∈ Qv δ
        have e : ((r'⁻¹ * t * r' : ↥(stab x)) : G) = r⁻¹ * t * r⁻¹⁻¹ := by simp [hr']
        rw [e]
        exact (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 (stab δ) h2) t).mp ht'
      · rw [map_mul, map_mul, map_inv, hty]; group
  exact fix_three_abs hV2 hLV φ hφs hker hnc h16 hC4all hmeet hT₁4 hr'3 hrT hr'1

end Vertex3

end CFSG.Quasithin.Kleidman.F204
