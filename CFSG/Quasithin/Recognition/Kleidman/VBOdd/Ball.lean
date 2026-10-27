module

public import CFSG.Quasithin.Background.F7
public import CFSG.Assembly.LowTwoRankDefs

public section

namespace CFSG.Quasithin.Kleidman.VBOdd

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.F7 CFSG.Quasithin.CosetGeom

variable {G : Type} [Group G] {G₀ G₁ G₂ T V : Subgroup G}

@[expose] noncomputable def ballV (V : Subgroup G) (n : ℕ) (u : CosetGeom G₀ G₁ G₂) :
    Subgroup G :=
  ⨆ x : {x : CosetGeom G₀ G₁ G₂ // vtype x = false ∧ dist u x ≤ n}, Vv V x.1

theorem Vv_le_ballV {n : ℕ} {u x : CosetGeom G₀ G₁ G₂} (hx : vtype x = false)
    (hd : dist u x ≤ n) : Vv V x ≤ ballV V n u :=
  le_iSup (fun x : {x : CosetGeom G₀ G₁ G₂ // vtype x = false ∧ dist u x ≤ n} => Vv V x.1)
    ⟨x, hx, hd⟩

theorem ballV_le {n : ℕ} {u : CosetGeom G₀ G₁ G₂} {X : Subgroup G}
    (h : ∀ x : CosetGeom G₀ G₁ G₂, vtype x = false → dist u x ≤ n → Vv V x ≤ X) :
    ballV V n u ≤ X :=
  iSup_le fun x => h x.1 x.2.1 x.2.2

theorem mem_Γ0_of_vtype {x : CosetGeom G₀ G₁ G₂} (hx : vtype x = false) : x ∈ Γ0 G₀ G₁ G₂ := by
  cases x with
  | inl y => exact ⟨y, rfl⟩
  | inr y => simp [vtype] at hx

theorem ballV_smul (hN : G₁ ≤ Subgroup.normalizer (V : Set G)) (n : ℕ) (g : ↥G₀)
    (u : CosetGeom G₀ G₁ G₂) : ballV V n (g • u) = conjSub (g : G) (ballV V n u) := by
  apply le_antisymm
  · refine ballV_le fun x hx hd => ?_
    have hx' : vtype (g⁻¹ • x) = false := by rw [vtype_smul]; exact hx
    have hd' : dist u (g⁻¹ • x) ≤ n := by
      have := dist_smul g u (g⁻¹ • x)
      rw [smul_inv_smul] at this
      rw [← this]; exact hd
    have e : Vv V x = conjSub (g : G) (Vv V (g⁻¹ • x)) := by
      rw [← Vv_smul hN, smul_inv_smul]
    rw [e]
    exact conjSub_mono _ (Vv_le_ballV hx' hd')
  · rw [conjSub_le_iff]
    refine ballV_le fun x hx hd => ?_
    rw [le_conjSub_iff, inv_inv, ← Vv_smul hN]
    refine Vv_le_ballV (by rw [vtype_smul]; exact hx) ?_
    rw [CosetGeom.dist_smul]; exact hd

theorem stab_le_normalizer_ballV (hN : G₁ ≤ Subgroup.normalizer (V : Set G)) (n : ℕ)
    (u : CosetGeom G₀ G₁ G₂) : stab u ≤ Subgroup.normalizer (ballV V n u : Set G) := by
  intro s hs
  obtain ⟨hs0, hsu⟩ := mem_stab.mp hs
  apply mem_normalizer_of_conjSub_eq
  have := ballV_smul hN n ⟨s, hs0⟩ u
  rw [hsu] at this
  exact this.symm

variable [Finite G]

theorem isElemAbelian_ballV (hyp : AmalgamHypV G₀ G₁ G₂ T V) (hV : V ≠ ⊥) {n : ℕ}
    (hn : 2 * n < critDist G₀ G₁ G₂ V) (u : CosetGeom G₀ G₁ G₂) :
    IsElemAbelian 2 (ballV V n u) := by
  refine isElemAbelian_iSup _ (fun x => isElemAbelian_Vv_of_mem_Γ0 hyp.normalizes
    hyp.elemAbelian (mem_Γ0_of_vtype x.2.1)) ?_
  intro x x' a ha a' ha'
  have hd : dist x.1 x'.1 < critDist G₀ G₁ G₂ V := by
    have h1 := dist_triangle hyp.gen x.1 u x'.1
    have h2 := x.2.2
    have h3 := x'.2.2
    rw [CosetGeom.dist_comm x.1 u] at h1
    omega
  have hc := commutator_Vv_Vv_eq_bot hyp hV (mem_Γ0_of_vtype x.2.1) (mem_Γ0_of_vtype x'.2.1) hd
  have := Subgroup.commutator_eq_bot_iff_le_centralizer.mp hc ha
  exact (Subgroup.mem_centralizer_iff.mp this a' ha').symm

end CFSG.Quasithin.Kleidman.VBOdd
