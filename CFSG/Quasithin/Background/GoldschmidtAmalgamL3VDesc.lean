module

public import CFSG.Quasithin.Background.GoldschmidtAmalgamL3VBase
public import CFSG.Quasithin.Background.GoldschmidtAmalgamL3XFix

public section

namespace CFSG.Quasithin

open CFSG.Quasithin CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.F7
  CFSG.Quasithin.CosetGeom CFSG.Quasithin.F6.GoldAmL

namespace F6

namespace GoldAmL3

variable {D : Type*} [Group D] [Finite D] {A B : Subgroup D} {z : D} {V : Subgroup D}

namespace GoldHyp3

variable (h : GoldHyp3 A B z V)

include h

theorem mem_stab_of_centralizes_Zlab {u s : CosetGeom (A ⊔ B) A B}
    (hs : (graph (A ⊔ B) A B).Adj u s) {g : D} (hg : g ∈ stab u)
    (hc : ∀ x ∈ Zlab V z s, g * x * g⁻¹ = x) : g ∈ stab s := by
  by_cases hu : vtype u = true
  · have hst : vtype s = false := vtype_eq_false_of_adj hs hu
    rw [Zlab_of_vtype_false hst] at hc
    exact h.mem_stab_of_centralizes_Vv hu hs hg hc
  · have hu' : vtype u = false := by simpa using hu
    have hst : vtype s = true := vtype_eq_true_of_adj hs hu'
    rw [Zlab_of_vtype_true hst] at hc
    exact h.mem_stab_of_centralizes_Zv hu' hs hg hc

theorem mem_ballStab_one_of_fix_two_any {u v w : CosetGeom (A ⊔ B) A B}
    (hv : (graph (A ⊔ B) A B).Adj u v) (hw : (graph (A ⊔ B) A B).Adj u w) (hvw : v ≠ w) {x : D}
    (hxu : x ∈ stab u) (hxv : x ∈ stab v) (hxw : x ∈ stab w) : x ∈ ballStab 1 u := by
  by_cases hu : vtype u = true
  · exact h.mem_ballStab_one_of_fix_two hu hv hw hvw hxu hxv hxw
  · exact h.mem_ballStab_one_of_fix_two_A (by simpa using hu) hv hw hvw hxu hxv hxw

theorem mem_ballStab_one_desc {n i : ℕ} {p : ℕ → CosetGeom (A ⊔ B) A B} (hp : IsGeo p n)
    (hi : 1 ≤ i) (hin : i + 1 ≤ n) {g : D} (hg0 : g ∈ ballStab 1 (p (i - 1)))
    (hc : ∀ x ∈ Zlab V z (p (i + 1)), g * x * g⁻¹ = x) : g ∈ ballStab 1 (p i) := by
  have hadj0 : (graph (A ⊔ B) A B).Adj (p (i - 1)) (p i) := by
    have := hp.adj (i := i - 1) (by omega)
    rwa [show i - 1 + 1 = i by omega] at this
  have hadj1 : (graph (A ⊔ B) A B).Adj (p i) (p (i + 1)) := hp.adj (i := i) (by omega)
  have hd1 : CosetGeom.dist (p (i - 1)) (p i) ≤ 1 := by
    have := hp (i - 1) i (by omega) (by omega)
    omega
  have hgs0 : g ∈ stab (p (i - 1)) := ballStab_le_stab 1 _ hg0
  have hgs : g ∈ stab (p i) := ballStab_le_stab_of_dist_le (n := 1) hd1 hg0
  have hgs1 : g ∈ stab (p (i + 1)) := h.mem_stab_of_centralizes_Zlab hadj1 hgs hc
  exact h.mem_ballStab_one_of_fix_two_any hadj0.symm hadj1 (hp.ne (by omega) (by omega)) hgs hgs0
    hgs1

theorem le_ballStab_one_desc {n i : ℕ} {p : ℕ → CosetGeom (A ⊔ B) A B} (hp : IsGeo p n)
    (hi : 1 ≤ i) (hin : i + 1 ≤ n) {H : Subgroup D} (hH : H ≤ ballStab 1 (p (i - 1)))
    (hc : H ≤ Subgroup.centralizer (Zlab V z (p (i + 1)) : Set D)) : H ≤ ballStab 1 (p i) :=
  fun g hg => h.mem_ballStab_one_desc hp hi hin (hH hg) fun x hx => by
    have := Subgroup.mem_centralizer_iff.mp (hc hg) x hx
    exact mul_inv_eq_iff_eq_mul.mpr this.symm

end GoldHyp3

end GoldAmL3

end F6

end CFSG.Quasithin
