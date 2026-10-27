module

public import Mathlib.Algebra.CharP.Two
public import Mathlib.Tactic.Abel
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs

public section

namespace CFSG.RankThree.GF2n.Stroth80

theorem sec7_step7_algebra {K E : Type*} [Field K] [CharP K 2] [AddCommGroup E] [Module K E]
    (U W : Submodule K E) (Tf Tv : E →ₗ[K] E) (hTf : ∀ e, Tf (Tf e) = e)
    (hTv : ∀ e, Tv (Tv e) = e) (hvU : ∀ u ∈ U, Tv u = u) (hvW : ∀ e, Tv e - e ∈ W)
    (hfU : ∀ u ∈ U, Tf u = u) (hfW : ∀ w ∈ W, Tf w - w ∈ U)
    (hperp : ∀ e, Tf (Tv (Tf (Tv e)) - e) - (Tv (Tf (Tv e)) - e) = 0) (e : E) :
    Tf (Tv (Tf (Tv e))) - e = (Tv (Tf e - e) - (Tf e - e)) + (Tf (Tv e - e) - (Tv e - e)) := by
  have h2 : ∀ x : E, x + x = 0 := fun x => by
    rw [← two_smul K x, (CharTwo.two_eq_zero : (2 : K) = 0), zero_smul]
  have hneg : ∀ x : E, -x = x := fun x => neg_eq_of_add_eq_zero_left (h2 x)
  obtain ⟨a, ha⟩ : ∃ a, a = Tf e - e := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b, b = Tv e - e := ⟨_, rfl⟩
  obtain ⟨c, hc⟩ : ∃ c, c = Tf b - b := ⟨_, rfl⟩
  rw [← ha, ← hb, ← hc]
  have hTe : Tf e = e + a := by rw [ha]; abel
  have hve : Tv e = e + b := by rw [hb]; abel
  have hbW : b ∈ W := by rw [hb]; exact hvW e
  have hcU : c ∈ U := by rw [hc]; exact hfW b hbW
  have hTfa : Tf a = a := by
    rw [ha, map_sub, hTf]
    have := hneg (Tf e - e)
    rw [neg_sub] at this
    exact this
  have hTvb : Tv b = b := by
    rw [hb, map_sub, hTv]
    have := hneg (Tv e - e)
    rw [neg_sub] at this
    exact this
  have hTb : Tf b = b + c := by rw [hc]; abel
  have s2 : Tf (Tv e) = e + a + b + c := by
    rw [hve, map_add, hTe, hTb]
    abel
  have s3 : Tv (Tf (Tv e)) = e + Tv a + c := by
    rw [s2, map_add, map_add, map_add, hvU c hcU, hTvb, hve]
    calc e + b + Tv a + b + c = e + Tv a + c + (b + b) := by abel
      _ = e + Tv a + c := by rw [h2 b, add_zero]
  have h6 : Tf (Tv a) = Tv a := by
    have h := hperp e
    rw [s3] at h
    have e1 : e + Tv a + c - e = Tv a + c := by abel
    rw [e1, map_add, hfU c hcU] at h
    have e2 : Tf (Tv a) + c - (Tv a + c) = Tf (Tv a) - Tv a := by abel
    rw [e2] at h
    exact sub_eq_zero.mp h
  rw [s3, map_add, map_add, hfU c hcU, h6, hTe]
  calc e + a + Tv a + c - e = (Tv a - a) + c + (a + a) := by abel
    _ = (Tv a - a) + c := by rw [h2 a, add_zero]

end CFSG.RankThree.GF2n.Stroth80
