module

public import CFSG.Quasithin.Vol2.Ch10SecQ6WrA
public import CFSG.Quasithin.Vol2.Ch10SecQ6WrCl

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecD

namespace C10P06

open Equiv

@[expose] def coordPre (A : Subgroup SymFiveWrTwo) (hbase : ∀ g ∈ A, g.right = 1)
    (q : Multiplicative (ZMod 2)) (D' : Subgroup (Perm (Fin 5))) : Subgroup SymFiveWrTwo where
  carrier := {g | g ∈ A ∧ g.left q ∈ D'}
  one_mem' := ⟨A.one_mem, D'.one_mem⟩
  mul_mem' := fun {a b} ha hb => ⟨A.mul_mem ha.1 hb.1, by
    rw [left_mul_base (hbase _ ha.1)]
    exact D'.mul_mem ha.2 hb.2⟩
  inv_mem' := fun {a} ha => ⟨A.inv_mem ha.1, by
    rw [inv_left_base (hbase _ ha.1)]
    exact D'.inv_mem ha.2⟩

theorem coordPre_le {A : Subgroup SymFiveWrTwo} {hbase : ∀ g ∈ A, g.right = 1}
    {q : Multiplicative (ZMod 2)} {D' : Subgroup (Perm (Fin 5))} : coordPre A hbase q D' ≤ A :=
  fun _ h => h.1

theorem coordPre_cover {A : Subgroup SymFiveWrTwo} (hbase : ∀ g ∈ A, g.right = 1)
    {q : Multiplicative (ZMod 2)} {D' : Subgroup (Perm (Fin 5))} {x1 : Perm (Fin 5)}
    (hx1 : x1 ∈ projSub A q) (hx1D : x1 ∉ D')
    (hcov : ∀ d ∈ projSub A q, d ∈ D' ∨ d * x1 ∈ D') :
    ∃ x ∈ A, x ∉ coordPre A hbase q D' ∧
      ∀ g ∈ A, g ∈ coordPre A hbase q D' ∨ g * x ∈ coordPre A hbase q D' := by
  obtain ⟨x, hxA, -, rfl⟩ := hx1
  refine ⟨x, hxA, fun h => hx1D h.2, fun g hg => ?_⟩
  rcases hcov _ ⟨g, hg, hbase g hg, rfl⟩ with h | h
  · exact Or.inl ⟨hg, h⟩
  · right
    refine ⟨A.mul_mem hg hxA, ?_⟩
    rwa [left_mul_base (hbase g hg)]

theorem projSub_zs_ne_bot {A : Subgroup SymFiveWrTwo} (hbase : ∀ g ∈ A, g.right = 1)
    (hA : A ≠ ⊥) (hD1 : projSub A 1 = ⊥) : projSub A zs ≠ ⊥ := by
  intro hD2
  apply hA
  rw [eq_bot_iff]
  intro g hg
  have h1 : g.left 1 ∈ projSub A 1 := ⟨g, hg, hbase g hg, rfl⟩
  have hz : g.left zs ∈ projSub A zs := ⟨g, hg, hbase g hg, rfl⟩
  rw [hD1, Subgroup.mem_bot] at h1
  rw [hD2, Subgroup.mem_bot] at hz
  rw [Subgroup.mem_bot]
  refine RegularWreathProduct.ext (funext fun q => ?_) (hbase g hg)
  rcases zmod2_cases q with rfl | rfl
  · exact h1
  · exact hz

theorem hypFix_Mcl {A : Subgroup SymFiveWrTwo} (hc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a)
    (h2 : ∀ a ∈ A, a * a = 1) (hA : A ≠ ⊥) : HypFix Mcl A := by
  by_cases hbase : ∀ g ∈ A, g.right = 1
  · by_cases hD1 : projSub A 1 = ⊥
    · obtain ⟨D', -, ⟨x1, hx1, hx1D, hcov⟩, u, hu, hufix, d, hd, hdu⟩ :=
        exists_hyperplane_fix (projSub_comm hc zs) (projSub_sq h2 zs)
          (projSub_zs_ne_bot hbase hA hD1)
      obtain ⟨x, hxA, hxB, hcovA⟩ := coordPre_cover hbase hx1 hx1D hcov
      obtain ⟨gd, hgdA, hgdr, rfl⟩ := hd
      refine ⟨coordPre A hbase zs D', coordPre_le, ⟨x, hxA, hxB, hcovA⟩, sumv 0 u,
        sumv_right_mem_Mcl hu, fun b hb => ?_, gd, hgdA, fun h => hdu ?_⟩
      · rw [gP_sumv_base (hbase b hb.1), pv_zero, hufix _ hb.2]
      · rw [gP_sumv_base hgdr, pv_zero] at h
        exact (sumv_inj (by simp [IsO]) (by simp [IsO]) h).2 |>.trans rfl
    · obtain ⟨D', -, ⟨x1, hx1, hx1D, hcov⟩, u, hu, hufix, d, hd, hdu⟩ :=
        exists_hyperplane_fix (projSub_comm hc 1) (projSub_sq h2 1) hD1
      obtain ⟨x, hxA, hxB, hcovA⟩ := coordPre_cover hbase hx1 hx1D hcov
      obtain ⟨gd, hgdA, hgdr, rfl⟩ := hd
      refine ⟨coordPre A hbase 1 D', coordPre_le, ⟨x, hxA, hxB, hcovA⟩, sumv u 0,
        sumv_left_mem_Mcl hu, fun b hb => ?_, gd, hgdA, fun h => hdu ?_⟩
      · rw [gP_sumv_base (hbase b hb.1), pv_zero, hufix _ hb.2]
      · rw [gP_sumv_base hgdr, pv_zero] at h
        exact (sumv_inj ((isO_pv _ _).mpr hu) hu h).1
  · push Not at hbase
    obtain ⟨t, htA, ht⟩ := hbase
    have htz : t.right = zs := (zmod2_cases t.right).resolve_left ht
    obtain ⟨u, hu, hu0, hufix⟩ := exists_fix_ne_zero (projSub_comm hc 1) (projSub_sq h2 1)
    let B : Subgroup SymFiveWrTwo :=
      { carrier := {g | g ∈ A ∧ g.right = 1}
        one_mem' := ⟨A.one_mem, rfl⟩
        mul_mem' := fun {a b} ha hb => ⟨A.mul_mem ha.1 hb.1, by rw [right_mul, ha.2, hb.2, one_mul]⟩
        inv_mem' := fun {a} ha => ⟨A.inv_mem ha.1, inv_right_base ha.2⟩ }
    refine ⟨B, fun _ h => h.1, ⟨t, htA, fun h => ht h.2, fun g hg => ?_⟩, sumv u 0,
      sumv_left_mem_Mcl hu, fun b hb => ?_, t, htA, fun h => hu0 ?_⟩
    · rcases zmod2_cases g.right with hr | hr
      · exact Or.inl ⟨hg, hr⟩
      · exact Or.inr ⟨A.mul_mem hg htA, by rw [right_mul, hr, htz, zs_mul_zs]⟩
    · rw [gP_sumv_base hb.2, pv_zero, hufix _ ⟨b, hb.1, hb.2, rfl⟩]
    · rw [gP_sumv_swap htz, pv_zero] at h
      exact (sumv_inj (by simp [IsO]) hu h).1.symm

end C10P06

end CFSG.Quasithin.Vol2.Ch10.SecD
