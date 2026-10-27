module

public import CFSG.Quasithin.Recognition.Kleidman.F204.LocalPUd

public section

namespace CFSG.Quasithin.Kleidman.F204

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin CFSG.Quasithin.S152X
open CFSG.Quasithin.F7 CFSG.Quasithin.FA5
open CFSG.Quasithin.F53
open CFSG.Quasithin.CosetGeom

set_option linter.unusedSectionVars false

variable {G : Type} [Group G] [Finite G] {H M : Subgroup G}

@[expose] def Vball (n : ℕ) (δ : Geo H M) : Subgroup G :=
  ⨆ (x : Geo H M) (_ : dist δ x ≤ n), Zv x

omit [Finite G] in
theorem Zv_le_Vball {n : ℕ} {δ x : Geo H M} (h : dist δ x ≤ n) : Zv x ≤ Vball n δ :=
  le_iSup₂_of_le (f := fun (x : Geo H M) (_ : dist δ x ≤ n) => Zv x) x h le_rfl

omit [Finite G] in
theorem Vball_le_iff {n : ℕ} {δ : Geo H M} {K : Subgroup G} :
    Vball n δ ≤ K ↔ ∀ x : Geo H M, dist δ x ≤ n → Zv x ≤ K :=
  ⟨fun h _ hx => (Zv_le_Vball hx).trans h, fun h => iSup₂_le h⟩

omit [Finite G] in
theorem Vball_mono {m n : ℕ} (hmn : m ≤ n) (δ : Geo H M) : Vball m δ ≤ Vball n δ :=
  Vball_le_iff.mpr fun _ hx => Zv_le_Vball (hx.trans hmn)

omit [Finite G] in
theorem Vn_le_Vball_one (δ : Geo H M) : Vn δ ≤ Vball 1 δ :=
  iSup₂_le fun _ hμ => Zv_le_Vball (le_of_eq (dist_eq_one_iff_adj.mpr hμ))

omit [Finite G] in
theorem Vball_le_Vball_of_mem_nbrs {m : ℕ} {δ μ : Geo H M}
    (hμ : μ ∈ nbrs δ) : Vball m μ ≤ Vball (m + 1) δ := by
  refine Vball_le_iff.mpr fun x hx => Zv_le_Vball ?_
  have h1 : dist δ μ = 1 := dist_eq_one_iff_adj.mpr hμ
  have := dist_triangle (G₀ := H ⊔ M) rfl δ μ x
  omega

omit [Finite G] in
theorem Vn_le_Vball_two_of_mem_nbrs {δ μ : Geo H M} (hμ : μ ∈ nbrs δ) :
    Vn δ ≤ Vball 2 μ := by
  refine iSup₂_le fun x hx => Zv_le_Vball ?_
  have h1 : dist μ δ = 1 := by
    rw [CosetGeom.dist_comm]; exact dist_eq_one_iff_adj.mpr hμ
  have h2 : dist δ x = 1 := dist_eq_one_iff_adj.mpr hx
  have := dist_triangle (G₀ := H ⊔ M) rfl μ δ x
  omega

omit [Finite G] in
theorem Vball_smul (g : ↥(H ⊔ M)) (n : ℕ) (δ : Geo H M) :
    Vball n (g • δ) = conjSub (g : G) (Vball n δ) := by
  apply le_antisymm
  · refine Vball_le_iff.mpr fun x hx => ?_
    obtain ⟨x', rfl⟩ : ∃ x', x = g • x' := ⟨g⁻¹ • x, by simp⟩
    rw [CosetGeom.dist_smul] at hx
    rw [Zv_smul]
    exact conjSub_mono _ (Zv_le_Vball hx)
  · rw [conjSub_le_iff]
    refine Vball_le_iff.mpr fun x hx => ?_
    rw [← conjSub_le_iff, ← Zv_smul]
    exact Zv_le_Vball (by rw [CosetGeom.dist_smul]; exact hx)

omit [Finite G] in
theorem stab_le_normalizer_Vball (n : ℕ) (δ : Geo H M) :
    stab δ ≤ Subgroup.normalizer (Vball n δ : Set G) := by
  intro g hg
  obtain ⟨hG0, hfix⟩ := mem_stab.mp hg
  have e := Vball_smul (⟨g, hG0⟩ : ↥(H ⊔ M)) n δ
  rw [hfix] at e
  exact mem_normalizer_of_conjSub_eq e.symm

namespace Amal

variable {B S : Subgroup G} (hA : Amal H M B S)
include hA

theorem Vball_le_Qv {n : ℕ} {δ μ : Geo H M} (h : dist δ μ + n < bMin H M) :
    Vball n δ ≤ Qv μ := by
  refine Vball_le_iff.mpr fun x hx => Zv_le_Qv_of_dist_lt ?_
  have h1 := dist_triangle hA.amalgam.gen x δ μ
  have h2 := bMin_le_bAt (H := H) (M := M) x
  rw [CosetGeom.dist_comm x δ] at h1
  omega

theorem isElemAbelian_Vball {n : ℕ} (hb : 2 * n < bMin H M) (δ : Geo H M) :
    IsElemAbelian 2 (Vball n δ) := by
  have e : Vball n δ = ⨆ x : {x : Geo H M // dist δ x ≤ n}, Zv x.1 := by
    unfold Vball; exact iSup_subtype'
  rw [e]
  refine isElemAbelian_iSup _ (fun x => hA.isElemAbelian_Zv x.1) (fun x y a ha c hc => ?_)
  have h1 := dist_triangle hA.amalgam.gen x.1 δ y.1
  rw [CosetGeom.dist_comm x.1 δ] at h1
  have h2 := bMin_le_bAt (H := H) (M := M) x.1
  have hxy : Zv x.1 ≤ Qv y.1 := Zv_le_Qv_of_dist_lt (by have := x.2; have := y.2; omega)
  exact (Subgroup.mem_centralizer_iff.mp (hA.Zv_le_centerOf_Qv y.1 hc).2 a (hxy ha))

end Amal

end CFSG.Quasithin.Kleidman.F204
