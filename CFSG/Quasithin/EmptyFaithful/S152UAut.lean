module

public import CFSG.Quasithin.EmptyFaithful.S151Basic

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped commutatorElement

variable {G : Type} [Group G]

theorem conj_coe_apply (V : Subgroup G) (g : Subgroup.normalizer (V : Set G)) (v : V) :
    ((conjAct V g v : V) : G) = g * v * (g : G)⁻¹ :=
  CFSG.Quasithin.AutOn.coe_conjAct_apply V g v

theorem conjAct_eq_iff {V : Subgroup G} {x y : G} (hx : x ∈ Subgroup.normalizer (V : Set G))
    (hy : y ∈ Subgroup.normalizer (V : Set G)) :
    conjAct V ⟨x, hx⟩ = conjAct V ⟨y, hy⟩ ↔ x⁻¹ * y ∈ Subgroup.centralizer (V : Set G) := by
  constructor
  · intro h
    have h1 : conjAct V ((⟨x, hx⟩ : Subgroup.normalizer (V : Set G))⁻¹ * ⟨y, hy⟩) = 1 := by
      rw [map_mul, map_inv, h]
      exact inv_mul_cancel _
    exact A4.conjAct_eq_one_iff.mp h1
  · intro h
    have h1 : conjAct V ((⟨x, hx⟩ : Subgroup.normalizer (V : Set G))⁻¹ * ⟨y, hy⟩) = 1 :=
      A4.conjAct_eq_one_iff.mpr h
    rw [map_mul, map_inv, inv_mul_eq_one] at h1
    exact h1

theorem mem_autOn_of_mem {X V : Subgroup G} {x : G} (hx : x ∈ Subgroup.normalizer (V : Set G))
    (hxX : x ∈ X) : conjAct V ⟨x, hx⟩ ∈ autOn X V :=
  mem_autOn_iff_exists.mpr ⟨x, hx, hxX, rfl⟩

theorem preOn_autOn_eq {M V N : Subgroup G} (hMV : M ≤ Subgroup.normalizer (V : Set G))
    (hNM : N ≤ M) (hC : M ⊓ Subgroup.centralizer (V : Set G) ≤ N) :
    preOn M V (autOn N V) = N := by
  apply le_antisymm
  · intro x hx
    obtain ⟨hxM, hxN, hxa⟩ := mem_preOn.mp hx
    obtain ⟨y, hyN, hyN', hy⟩ := mem_autOn_iff_exists.mp hxa
    have hc : y⁻¹ * x ∈ Subgroup.centralizer (V : Set G) := (conjAct_eq_iff hyN hxN).mp hy
    have hcM : y⁻¹ * x ∈ M := M.mul_mem (M.inv_mem (hNM hyN')) hxM
    have : x = y * (y⁻¹ * x) := by group
    rw [this]
    exact N.mul_mem hyN' (hC ⟨hcM, hc⟩)
  · intro x hx
    exact mem_preOn.mpr ⟨hNM hx, hMV (hNM hx), mem_autOn_iff_exists.mpr ⟨x, hMV (hNM hx), hx, rfl⟩⟩

theorem mem_of_conjAct_mem_autOn {M V N : Subgroup G} (hMV : M ≤ Subgroup.normalizer (V : Set G))
    (hNM : N ≤ M) (hC : M ⊓ Subgroup.centralizer (V : Set G) ≤ N) {x : G} (hxM : x ∈ M)
    (h : conjAct V ⟨x, hMV hxM⟩ ∈ autOn N V) : x ∈ N :=
  CFSG.Quasithin.AutOn.mem_of_conjAct_mem_autOn hMV hNM hC hxM h

theorem relIndex_autOn [Finite G] {S T V : Subgroup G} (hST : S ≤ T)
    (hTV : T ≤ Subgroup.normalizer (V : Set G))
    (hC : T ⊓ Subgroup.centralizer (V : Set G) ≤ S) :
    (autOn S V).relIndex (autOn T V) = S.relIndex T := by
  have hSV : S ≤ Subgroup.normalizer (V : Set G) := hST.trans hTV
  set C : Subgroup G := Subgroup.centralizer (V : Set G) with hCdef
  have e1 : Nat.card (autOn T V) = (T ⊓ C).relIndex T := card_autOn_eq_relIndex hTV
  have e2 : Nat.card (autOn S V) = (S ⊓ C).relIndex S := card_autOn_eq_relIndex hSV
  have hSC : S ⊓ C = T ⊓ C := le_antisymm (inf_le_inf_right C hST) (le_inf hC inf_le_right)
  rw [hSC] at e2
  have e3 := Subgroup.relIndex_mul_relIndex (T ⊓ C) S T hC hST
  have e4 : (autOn S V).relIndex (autOn T V) * Nat.card (autOn S V) = Nat.card (autOn T V) := by
    have := Subgroup.relIndex_mul_card (autOn S V) (autOn T V)
    rwa [inf_of_le_left (A4.autOn_mono hST)] at this
  have hpos : 0 < Nat.card (autOn S V) := Nat.card_pos
  have : (autOn S V).relIndex (autOn T V) * Nat.card (autOn S V) =
      S.relIndex T * Nat.card (autOn S V) := by
    rw [e4, e1, ← e3, e2, mul_comm]
  exact Nat.eq_of_mul_eq_mul_right hpos this

theorem isPGroup_autOn {P V : Subgroup G} (hP : IsPGroup 2 P)
    (hPV : P ≤ Subgroup.normalizer (V : Set G)) : IsPGroup 2 (autOn P V) :=
  CFSG.Quasithin.AutOn.isPGroup_autOn hP

theorem coe_mem_commutator_of_mem_commV {P V : Subgroup G} (hV : IsElemAbelian 2 V)
    {B : Subgroup (MulAut V)} (hB : B ≤ autOn P V) {z : V}
    (hz : z ∈ @commV V (commGroupOfElemAbelian hV) B) : (z : G) ∈ ⁅V, preOn P V B⁆ := by
  let _ : CommGroup V := commGroupOfElemAbelian hV
  unfold commV at hz
  induction hz using Subgroup.closure_induction with
  | mem w hw =>
    obtain ⟨x, hx, v, rfl⟩ := hw
    obtain ⟨p, hpN, hpP, hpx⟩ := mem_autOn_iff_exists.mp (hB hx)
    have hpB : p ∈ preOn P V B := mem_preOn.mpr ⟨hpP, hpN, by rw [hpx]; exact hx⟩
    have hxv : ((x v : V) : G) = p * v * p⁻¹ := by
      rw [← hpx]
      exact conj_coe_apply V ⟨p, hpN⟩ v
    have hcomm : ((x v * v⁻¹ : V) : G) = ⁅p, (v : G)⁆ := by
      rw [commutatorElement_def]
      show ((x v : V) : G) * (v : G)⁻¹ = p * v * p⁻¹ * (v : G)⁻¹
      rw [hxv]
    show ((x v * v⁻¹ : V) : G) ∈ ⁅V, preOn P V B⁆
    rw [hcomm, Subgroup.commutator_comm V]
    exact Subgroup.commutator_mem_commutator hpB v.2
  | one => exact Subgroup.one_mem _
  | mul a b _ _ ha hb => exact Subgroup.mul_mem _ ha hb
  | inv a _ ha => exact Subgroup.inv_mem _ ha

end CFSG.Quasithin
