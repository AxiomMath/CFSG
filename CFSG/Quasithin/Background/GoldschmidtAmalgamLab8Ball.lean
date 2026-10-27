module

public import CFSG.Quasithin.Background.GoldschmidtAmalgamLab7Ball

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.F7
  CFSG.Quasithin.CosetGeom CFSG.Quasithin.F6.GoldAmL CFSG.Quasithin.F6.GoldAmLab6
  CFSG.Quasithin.F6.GoldAmLab7

namespace F6

namespace GoldAmLab8

variable {D : Type*} [Group D] [Finite D] {A B : Subgroup D} {V V₂ : Subgroup D} {z c : D}

theorem Nm_le_ballStab_of_dist (h : TwoSys A B z V c V₂) (h3 : GoldAmL3.GoldHyp3 A B z V) {b : ℕ}
    (hb : critDist (A ⊔ B) A B V = b) (u : CosetGeom (A ⊔ B) A B) :
    ∀ (d : ℕ) (v : CosetGeom (A ⊔ B) A B), CosetGeom.dist u v = d → d + 2 ≤ b →
      Nm A B V V₂ u ≤ ballStab 1 v := by
  intro d
  induction d with
  | zero =>
    intro v hv _
    obtain rfl : u = v := (dist_eq_zero_iff rfl).mp hv
    exact (goodV_all h u).nm_le
  | succ d ih =>
    intro v hv hdb
    obtain ⟨v', hv', hd'⟩ :=
      exists_adj_dist_eq (rfl : A ⊔ B = A ⊔ B) (α := u) (δ := v) (d := d) hv
    have ih' := ih v' hd' (by omega)
    have hnst : Nm A B V V₂ u ≤ stab v := fun n hn =>
      ballStab_le_stab_of_dist_le (n := 1) (γ := v') (δ := v)
        (dist_eq_one_iff_adj.mpr hv'.symm).le (ih' hn)
    have hVu := goodV_all h u
    cases hvt : vtype v with
    | false =>
      intro n hn
      refine (goodV_all h v).cent_le n (hnst hn) fun x hx => ?_
      have hdx : CosetGeom.dist v u + 1 ≤ b := by rw [CosetGeom.dist_comm, hv]; omega
      have hle := Nm_le_ballStab_A (V₂ := V₂) h3 hb hvt hdx
      exact (hVu.qv_cent x (hle hx) n hn).symm
    | true =>
      intro n hn
      obtain ⟨y, rfl⟩ : ∃ y, v = Sum.inr y := by
        cases v with
        | inl x => simp [vtype] at hvt
        | inr y => exact ⟨y, rfl⟩
      refine h3.mem_ballStab_one_of_commutator hvt (hnst hn) fun w' hw' => ?_
      have hcent : Vv V (Sum.inr y : CosetGeom (A ⊔ B) A B) ≤
          Subgroup.centralizer ({n} : Set D) := by
        rw [Vv_inr]
        refine iSup₂_le fun x hx => ?_
        have hxt : vtype (Sum.inl x : CosetGeom (A ⊔ B) A B) = false := rfl
        have hdist : CosetGeom.dist (Sum.inl x : CosetGeom (A ⊔ B) A B) u + 1 ≤ b := by
          have h1 := CosetGeom.dist_triangle (G₁ := A) (G₂ := B) rfl
            (Sum.inl x : CosetGeom (A ⊔ B) A B) (Sum.inr y) u
          have h2 : CosetGeom.dist (Sum.inl x : CosetGeom (A ⊔ B) A B) (Sum.inr y) = 1 :=
            dist_eq_one_iff_adj.mpr hx.symm
          have h3' : CosetGeom.dist (Sum.inr y : CosetGeom (A ⊔ B) A B) u = d + 1 := by
            rw [CosetGeom.dist_comm]; exact hv
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

end GoldAmLab8

end F6

end CFSG.Quasithin
