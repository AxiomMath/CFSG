module

public import CFSG.Quasithin.Background.GoldschmidtAmalgamL3RVertex
public import CFSG.Quasithin.Background.GoldschmidtAmalgamLab7SysAll

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.F7
  CFSG.Quasithin.CosetGeom CFSG.Quasithin.F6.GoldAmL CFSG.Quasithin.F6.GoldAmLab6

namespace F6

namespace GoldAmLab7

variable {D : Type*} [Group D] [Finite D] {A B : Subgroup D} {V V₂ : Subgroup D} {z c : D}

omit [Finite D] in
theorem Nm_eq_Vv_of_vtype_false {u : CosetGeom (A ⊔ B) A B} (hu : vtype u = false) :
    Nm A B V V₂ u = Vv V u := by
  cases u with
  | inl x => rfl
  | inr y => simp [vtype] at hu

theorem Nm_le_ballStab_A (h3 : GoldAmL3.GoldHyp3 A B z V) {b : ℕ}
    (hb : critDist (A ⊔ B) A B V = b) {x v : CosetGeom (A ⊔ B) A B} (hx : vtype x = false)
    (hd : CosetGeom.dist x v + 1 ≤ b) : Nm A B V V₂ x ≤ ballStab 1 v := by
  rw [Nm_eq_Vv_of_vtype_false hx]
  exact (h3.Vv_le_ballStab_A hb hx).trans (ballStab_le_ballStab_of_dist rfl hd)

theorem Nm_le_ballStab_B_two (h : TwoSys A B z V c V₂) (h3 : GoldAmL3.GoldHyp3 A B z V) {b : ℕ}
    (hb : critDist (A ⊔ B) A B V = b) (hb4 : 4 ≤ b) {u w m : CosetGeom (A ⊔ B) A B}
    (hm : vtype m = true) (huw : (graph (A ⊔ B) A B).Adj u w)
    (hwm : (graph (A ⊔ B) A B).Adj w m) : Nm A B V V₂ u ≤ ballStab 1 m := by
  intro n hn
  have hVu := goodV_all h u
  have hnw : n ∈ ballStab 1 w := (goodE0_all h huw).nm_le hn
  have hnst : n ∈ stab m := ballStab_le_stab_of_dist_le (n := 1) (γ := w) (δ := m)
    (dist_eq_one_iff_adj.mpr hwm).le hnw
  obtain ⟨y, rfl⟩ : ∃ y, m = Sum.inr y := by
    cases m with
    | inl x => simp [vtype] at hm
    | inr y => exact ⟨y, rfl⟩
  refine h3.mem_ballStab_one_of_commutator hm hnst fun w' hw' => ?_
  have hcent : Vv V (Sum.inr y : CosetGeom (A ⊔ B) A B) ≤ Subgroup.centralizer ({n} : Set D) := by
    rw [Vv_inr]
    refine iSup₂_le fun x hx => ?_
    have hxt : vtype (Sum.inl x : CosetGeom (A ⊔ B) A B) = false := rfl
    have hdist : CosetGeom.dist (Sum.inl x : CosetGeom (A ⊔ B) A B) u + 1 ≤ b := by
      have h1 := CosetGeom.dist_triangle (G₁ := A) (G₂ := B) rfl (Sum.inl x : CosetGeom (A ⊔ B) A B)
        (Sum.inr y) u
      have h2 : CosetGeom.dist (Sum.inl x : CosetGeom (A ⊔ B) A B) (Sum.inr y) = 1 :=
        dist_eq_one_iff_adj.mpr hx.symm
      have h3' : CosetGeom.dist (Sum.inr y : CosetGeom (A ⊔ B) A B) u ≤ 2 := by
        have h4 := CosetGeom.dist_triangle (G₁ := A) (G₂ := B) rfl
          (Sum.inr y : CosetGeom (A ⊔ B) A B) w u
        have h5 : CosetGeom.dist (Sum.inr y : CosetGeom (A ⊔ B) A B) w = 1 :=
          dist_eq_one_iff_adj.mpr hwm.symm
        have h6 : CosetGeom.dist w u = 1 := dist_eq_one_iff_adj.mpr huw.symm
        omega
      omega
    have hle := Nm_le_ballStab_A (V₂ := V₂) h3 hb hxt hdist
    intro v hv
    rw [Subgroup.mem_centralizer_iff]
    intro n' hn'
    rw [Set.mem_singleton_iff.mp hn']
    have hv' : v ∈ Nm A B V V₂ (Sum.inl x : CosetGeom (A ⊔ B) A B) := hv
    exact hVu.qv_cent v (hle hv') n hn
  have hcomm := Subgroup.mem_centralizer_iff.mp (hcent hw') n (Set.mem_singleton n)
  have e : n * w' * n⁻¹ * w'⁻¹ = 1 := by rw [hcomm]; group
  rw [e]
  exact Subgroup.one_mem _

end GoldAmLab7

end F6

end CFSG.Quasithin
