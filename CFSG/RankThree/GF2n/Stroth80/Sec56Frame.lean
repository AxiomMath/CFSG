module

public import CFSG.RankThree.GF2n.Smith81.Sec220Conj
public import CFSG.RankThree.GF2n.Stroth80.Conj

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Timmesfeld CFSG.Timmesfeld.RankOne
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem Ctx.frame (hc : Ctx M Q Z B) {h : G}
    (hh : B = conjSubgroup h Z) {C : Subgroup G} {c : G} (hcC : C = conjSubgroup c Z)
    (hCQ : C ≤ QB B) (hCB : C ≠ B) : Ctx (conjSubgroup h M) (conjSubgroup h Q) B C where
  hyp := by
    rw [hh]
    exact hc.hyp.conj h
  conj := ⟨c * h⁻¹, by
    rw [hcC, hh, ← conjSubgroup_mul, inv_mul_cancel_right]⟩
  le := by
    rw [← (Ctx.QB_eq hc hh).2]
    exact hCQ
  ne := hCB

theorem Ctx.QB_comm (hc : Ctx M Q Z B) {x b : G} (hx : x ∈ QB B)
    (hb : b ∈ B) : x * b = b * x := by
  obtain ⟨g, hg⟩ := hc.conj
  rw [(Ctx.QB_eq hc hg).2] at hx
  rw [hg] at hb
  have h1 := hc.hyp.toHyp79.V_central (mem_conjSubgroup.mp hb) (mem_conjSubgroup.mp hx)
  have h2 : g⁻¹ * (b * x) * g = g⁻¹ * (x * b) * g := by
    calc g⁻¹ * (b * x) * g = (g⁻¹ * b * g) * (g⁻¹ * x * g) := by group
      _ = (g⁻¹ * x * g) * (g⁻¹ * b * g) := h1
      _ = g⁻¹ * (x * b) * g := by group
  exact (mul_left_cancel (mul_right_cancel h2)).symm

theorem card_subgroupOf_inf_subgroupOf {A C H : Subgroup G} (hA : A ≤ H) :
    Nat.card ↥(A.subgroupOf H ⊓ C.subgroupOf H) = Nat.card ↥(A ⊓ C) :=
  Nat.card_congr
    { toFun := fun x => ⟨x.1, ⟨Subgroup.mem_subgroupOf.mp x.2.1, Subgroup.mem_subgroupOf.mp x.2.2⟩⟩
      invFun := fun y => ⟨⟨y.1, hA y.2.1⟩,
        ⟨Subgroup.mem_subgroupOf.mpr y.2.1, Subgroup.mem_subgroupOf.mpr y.2.2⟩⟩
      left_inv := fun x => rfl
      right_inv := fun y => rfl }

theorem card_subgroupOf_of_le {A H : Subgroup G} (hA : A ≤ H) :
    Nat.card ↥(A.subgroupOf H) = Nat.card A :=
  Nat.card_congr (Subgroup.subgroupOfEquivOfLe hA).toEquiv

theorem mem_centralizer_sup {B C : Subgroup G} {x : G} (hB : x ∈ Subgroup.centralizer (B : Set G))
    (hC : x ∈ Subgroup.centralizer (C : Set G)) :
    x ∈ Subgroup.centralizer ((B ⊔ C : Subgroup G) : Set G) := by
  have h : B ⊔ C ≤ Subgroup.centralizer ({x} : Set G) := by
    refine sup_le (fun b hb => ?_) (fun c hc => ?_)
    · exact Subgroup.mem_centralizer_singleton_iff.mpr (Subgroup.mem_centralizer_iff.mp hB b hb)
    · exact Subgroup.mem_centralizer_singleton_iff.mpr (Subgroup.mem_centralizer_iff.mp hC c hc)
  refine Subgroup.mem_centralizer_iff.mpr fun w hw => ?_
  exact (Subgroup.mem_centralizer_singleton_iff.mp (h hw))

theorem Ctx.QB_comm_mem (hc : Ctx M Q Z B) {x y : G}
    (hx : x ∈ QB B) (hy : y ∈ QB B) : ⁅x, y⁆ ∈ B := by
  obtain ⟨h, hh⟩ := hc.conj
  have H' := hc.hyp.conj h
  rw [(Ctx.QB_eq hc hh).2] at hx hy
  rw [hh]
  exact H'.toHyp79.comm_mem_V hx hy

theorem Ctx.conj_mem_sup (hc : Ctx M Q Z B) {C : Subgroup G}
    (hCQ : C ≤ QB B) {x : G} (hx : x ∈ QB B) {w : G} (hw : w ∈ B ⊔ C) :
    x * w * x⁻¹ ∈ B ⊔ C := by
  have hle : B ⊔ C ≤ (B ⊔ C).comap (MulAut.conj x).toMonoidHom := by
    refine sup_le (fun b hb => ?_) (fun c hcC => ?_)
    · show x * b * x⁻¹ ∈ B ⊔ C
      rw [hc.QB_comm hx hb, mul_inv_cancel_right]
      exact Subgroup.mem_sup_left hb
    · show x * c * x⁻¹ ∈ B ⊔ C
      have h1 : x * c * x⁻¹ = ⁅x, c⁆ * c := by
        rw [commutatorElement_def]
        group
      rw [h1]
      exact Subgroup.mul_mem_sup (hc.QB_comm_mem hx (hCQ hcC)) hcC
  exact hle hw

theorem mem_of_coord_zero {W : Type*} [Group W] [Finite W] {F : Type*} [Field F] [Finite F]
    {i j : Fin 2} (hij : i ≠ j) (ψ : W ≃* Multiplicative (Fin 2 → F)) {C : Subgroup W}
    (hcard : Nat.card C = Nat.card F) (hC : ∀ w ∈ C, Multiplicative.toAdd (ψ w) i = 0) {w : W}
    (hw : Multiplicative.toAdd (ψ w) i = 0) : w ∈ C := by
  have hk : ∀ k : Fin 2, k = i ∨ k = j := by
    intro k
    fin_cases i <;> fin_cases j <;> fin_cases k <;> simp_all
  have hext : ∀ v v' : Fin 2 → F, v i = v' i → v j = v' j → v = v' := by
    intro v v' hi hj
    funext k
    rcases hk k with rfl | rfl
    · exact hi
    · exact hj
  let f : C → F := fun c => Multiplicative.toAdd (ψ c) j
  have hinj : Function.Injective f := by
    intro c c' hcc'
    apply Subtype.ext
    apply ψ.injective
    apply Multiplicative.toAdd.injective
    exact hext _ _ ((hC c c.2).trans (hC c' c'.2).symm) hcc'
  have hbij := hinj.bijective_of_nat_card_le hcard.ge
  obtain ⟨c, hc⟩ := hbij.2 (Multiplicative.toAdd (ψ w) j)
  have hcw : (c : W) = w := by
    apply ψ.injective
    apply Multiplicative.toAdd.injective
    exact hext _ _ ((hC c c.2).trans hw.symm) hc
  rw [← hcw]
  exact c.2

end CFSG.RankThree.GF2n.Stroth80
