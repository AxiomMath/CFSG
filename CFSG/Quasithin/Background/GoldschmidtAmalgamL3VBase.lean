module

public import CFSG.Quasithin.Background.GoldschmidtAmalgamL3UCent

public section

namespace CFSG.Quasithin

open CFSG.Quasithin CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.F7
  CFSG.Quasithin.CosetGeom CFSG.Quasithin.F6.GoldAmL

namespace F6

namespace GoldAmL3

variable {D : Type*} [Group D] {A B : Subgroup D} {z : D} {V : Subgroup D}

@[expose] noncomputable def Zlab (V : Subgroup D) (z : D) (v : CosetGeom (A ⊔ B) A B) :
    Subgroup D :=
  if vtype v = true then Zv z v else Vv V v

@[expose] noncomputable def Vn (V : Subgroup D) (n : ℕ) (x : CosetGeom (A ⊔ B) A B) :
    Subgroup D :=
  ⨆ (l : CosetGeom (A ⊔ B) A B) (_ : vtype l = false) (_ : CosetGeom.dist x l ≤ n), Vv V l

theorem Vv_le_Vn {n : ℕ} {x l : CosetGeom (A ⊔ B) A B} (hl : vtype l = false)
    (hd : CosetGeom.dist x l ≤ n) : Vv V l ≤ Vn V n x :=
  le_iSup₂_of_le l hl (le_iSup_of_le hd le_rfl)

theorem Vn_le_iff {n : ℕ} {x : CosetGeom (A ⊔ B) A B} {H : Subgroup D} :
    Vn V n x ≤ H ↔ ∀ l : CosetGeom (A ⊔ B) A B, vtype l = false → CosetGeom.dist x l ≤ n →
      Vv V l ≤ H := by
  simp only [Vn, iSup_le_iff]

theorem Vn_mono {m n : ℕ} (hmn : m ≤ n) (x : CosetGeom (A ⊔ B) A B) :
    Vn V m x ≤ Vn V n x :=
  Vn_le_iff.mpr fun _ hl hd => Vv_le_Vn hl (hd.trans hmn)

theorem Zlab_of_vtype_true {v : CosetGeom (A ⊔ B) A B} (hv : vtype v = true) :
    Zlab V z v = Zv z v := by
  simp [Zlab, hv]

theorem Zlab_of_vtype_false {v : CosetGeom (A ⊔ B) A B} (hv : vtype v = false) :
    Zlab V z v = Vv V v := by
  simp [Zlab, hv]

namespace GoldHyp3

variable (h : GoldHyp3 A B z V)

include h

theorem conjSub_Vn (g : ↥(A ⊔ B)) (n : ℕ) (x : CosetGeom (A ⊔ B) A B) :
    conjSub (g : D) (Vn V n x) = Vn V n (g • x) := by
  apply le_antisymm
  · rw [conjSub_le_iff]
    refine Vn_le_iff.mpr fun l hl hd => ?_
    have e : Vv V (g • l) = conjSub (g : D) (Vv V l) := Vv_smul h.natural.reduced.2.1 g l
    have h1 : Vv V (g • l) ≤ Vn V n (g • x) := by
      refine Vv_le_Vn (by rwa [vtype_smul]) ?_
      rw [CosetGeom.dist_smul]
      exact hd
    rw [e, conjSub_le_iff] at h1
    exact h1
  · refine Vn_le_iff.mpr fun l hl hd => ?_
    have h1 : Vv V (g⁻¹ • l) ≤ Vn V n x := by
      refine Vv_le_Vn (by rwa [vtype_smul]) ?_
      have := CosetGeom.dist_smul g⁻¹ (g • x) l
      rw [inv_smul_smul] at this
      rw [this]
      exact hd
    have e : Vv V l = conjSub (g : D) (Vv V (g⁻¹ • l)) := by
      have := Vv_smul h.natural.reduced.2.1 g (g⁻¹ • l)
      rwa [smul_inv_smul] at this
    rw [e]
    exact conjSub_mono _ h1

theorem stab_le_normalizer_Vn (n : ℕ) (x : CosetGeom (A ⊔ B) A B) :
    stab x ≤ Subgroup.normalizer (Vn V n x : Set D) := by
  intro y hy
  obtain ⟨hyG, hyx⟩ := mem_stab.mp hy
  apply mem_normalizer_of_conjSub_eq
  have := h.conjSub_Vn (⟨y, hyG⟩ : ↥(A ⊔ B)) n x
  rw [hyx] at this
  exact this

variable [Finite D]

theorem Vn_le_ballStab_one {b n : ℕ} (hb : critDist (A ⊔ B) A B V = b)
    {x y : CosetGeom (A ⊔ B) A B} (hn : n + CosetGeom.dist x y + 1 ≤ b) :
    Vn V n x ≤ ballStab 1 y := by
  refine Vn_le_iff.mpr fun l hl hd => h.Vv_le_ballStab_one_of_dist hb hl ?_
  have := CosetGeom.dist_triangle (G₀ := A ⊔ B) (G₁ := A) (G₂ := B) rfl l x y
  rw [CosetGeom.dist_comm l x] at this
  omega

theorem Vn_le_centralizer_Vn {b n n' : ℕ} (hb : critDist (A ⊔ B) A B V = b)
    {x x' : CosetGeom (A ⊔ B) A B} (hn : n + CosetGeom.dist x x' + n' < b) :
    Vn V n x ≤ Subgroup.centralizer (Vn V n' x' : Set D) := by
  refine Vn_le_iff.mpr fun l hl hd => ?_
  rw [Subgroup.le_centralizer_iff]
  refine Vn_le_iff.mpr fun l' hl' hd' => ?_
  refine h.Vv_le_centralizer_of_dist hb hl' hl ?_
  have h1 := CosetGeom.dist_triangle (G₀ := A ⊔ B) (G₁ := A) (G₂ := B) rfl l' x' l
  have h2 := CosetGeom.dist_triangle (G₀ := A ⊔ B) (G₁ := A) (G₂ := B) rfl x' x l
  rw [CosetGeom.dist_comm x' x, CosetGeom.dist_comm l' x'] at *
  omega

end GoldHyp3

end GoldAmL3

end F6

end CFSG.Quasithin
