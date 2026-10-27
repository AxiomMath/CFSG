module

public import CFSG.Quasithin.EmptyFaithful.A38c15IrrHess

public section

namespace CFSG.Quasithin.A312U3

open CFSG.RankThree.SubgroupLists CFSG.RepresentationTheory CFSG.Quasithin.A38c15
open scoped commutatorElement

variable {K : Type} [Field K] {G H : Subgroup (GL (Fin 3) K)}

theorem hessK_mem_center_of_commute [Finite K] (hirr : IsIrreducibleMatrixRep H.subtype)
    (hnc : ¬ IsMulCommutative H) {y : GL (Fin 3) K} (hy : ∀ x ∈ H, y * x = x * y) :
    y ∈ Subgroup.center (GL (Fin 3) K) := by
  rcases scalar_commutant_or_cyclic Nat.prime_three hirr with h | ⟨hcyc, -⟩
  · obtain ⟨c, hc⟩ := h (y : Matrix (Fin 3) (Fin 3) K) fun g hg => by
      simpa only [Units.val_mul] using congrArg Units.val (hy g hg).symm
    refine Subgroup.mem_center_iff.mpr fun z => Units.ext ?_
    rw [Units.val_mul, Units.val_mul, hc]
    exact (Matrix.scalar_commute c (fun r => Commute.all c r) _).symm.eq
  · exact absurd (inferInstance : IsMulCommutative H) hnc

@[expose] noncomputable def hessK_conj (hnorm : ∀ g ∈ G, ∀ x ∈ H, g * x * g⁻¹ ∈ H) (g : G) :
    MulAut H where
  toFun x := ⟨(g : GL (Fin 3) K) * x * (g : GL (Fin 3) K)⁻¹, hnorm g g.2 x x.2⟩
  invFun x := ⟨(g : GL (Fin 3) K)⁻¹ * x * (g : GL (Fin 3) K), by
    simpa using hnorm (g : GL (Fin 3) K)⁻¹ (G.inv_mem g.2) x x.2⟩
  left_inv x := Subtype.ext (by simp [mul_assoc])
  right_inv x := Subtype.ext (by simp [mul_assoc])
  map_mul' x y := Subtype.ext (by simp [mul_assoc])

theorem hessK_conj_apply (hnorm : ∀ g ∈ G, ∀ x ∈ H, g * x * g⁻¹ ∈ H) (g : G) (x : H) :
    ((hessK_conj hnorm g x : H) : GL (Fin 3) K) = (g : GL (Fin 3) K) * x * (g : GL (Fin 3) K)⁻¹ :=
  rfl

@[expose] noncomputable def hessK_conjHom (hnorm : ∀ g ∈ G, ∀ x ∈ H, g * x * g⁻¹ ∈ H) :
    G →* MulAut H where
  toFun := hessK_conj hnorm
  map_one' := MulEquiv.ext fun x => Subtype.ext (by simp [hessK_conj_apply])
  map_mul' g g' := MulEquiv.ext fun x => Subtype.ext (by simp [hessK_conj_apply, mul_assoc])

@[expose] noncomputable def hessK_act (hnorm : ∀ g ∈ G, ∀ x ∈ H, g * x * g⁻¹ ∈ H) :
    G →* MulAut (H ⧸ Subgroup.center H) :=
  (hessQuotAut H).comp (hessK_conjHom hnorm)

theorem hessK_ker_commute (hnorm : ∀ g ∈ G, ∀ x ∈ H, g * x * g⁻¹ ∈ H) {g : G}
    (hg : g ∈ (hessK_act hnorm).ker) {x y : GL (Fin 3) K} (hx : x ∈ H) (hy : y ∈ H) :
    y * (x⁻¹ * ((g : GL (Fin 3) K) * x * (g : GL (Fin 3) K)⁻¹)) =
      x⁻¹ * ((g : GL (Fin 3) K) * x * (g : GL (Fin 3) K)⁻¹) * y := by
  have h1 : hessK_act hnorm g (QuotientGroup.mk ⟨x, hx⟩) = QuotientGroup.mk ⟨x, hx⟩ := by
    rw [MonoidHom.mem_ker.mp hg]
    rfl
  have h2 : (QuotientGroup.mk (hessK_conj hnorm g ⟨x, hx⟩) : H ⧸ Subgroup.center H) =
      QuotientGroup.mk ⟨x, hx⟩ := h1
  have h3 := Subgroup.mem_center_iff.mp (QuotientGroup.eq.mp h2.symm) ⟨y, hy⟩
  simpa [hessK_conj_apply] using congrArg Subtype.val h3

theorem hessK_isSolvable_ker (hnorm : ∀ g ∈ G, ∀ x ∈ H, g * x * g⁻¹ ∈ H)
    (hscalar : ∀ y : GL (Fin 3) K, (∀ x ∈ H, y * x = x * y) →
      y ∈ Subgroup.center (GL (Fin 3) K)) :
    Group.IsSolvable (hessK_act hnorm).ker := by
  set N := (hessK_act hnorm).ker
  let ι : N →* GL (Fin 3) K := G.subtype.comp N.subtype
  have hι : Function.Injective ι := G.subtype_injective.comp N.subtype_injective
  have hK : ∀ (a : N) (x : GL (Fin 3) K), x ∈ H →
      ∃ z ∈ Subgroup.center (GL (Fin 3) K), ι a * x * (ι a)⁻¹ = x * z := by
    intro a x hx
    refine ⟨x⁻¹ * (ι a * x * (ι a)⁻¹), hscalar _ fun y hy => ?_, by group⟩
    exact (hessK_ker_commute hnorm a.2 hx hy).symm
  have hcomm : ∀ a b : N, (ι a)⁻¹ * (ι b)⁻¹ * ι a * ι b ∈ Subgroup.center (GL (Fin 3) K) := by
    intro a b
    refine hscalar _ fun x hx => ?_
    obtain ⟨za, hza, ha⟩ := hK a x hx
    obtain ⟨zb, hzb, hb⟩ := hK b x hx
    have e1 : ι a * zb * (ι a)⁻¹ = zb := by
      rw [Subgroup.mem_center_iff.mp hzb (ι a), mul_inv_cancel_right]
    have e2 : ι b * za * (ι b)⁻¹ = za := by
      rw [Subgroup.mem_center_iff.mp hza (ι b), mul_inv_cancel_right]
    have e3 : ι a * ι b * x * (ι b)⁻¹ * (ι a)⁻¹ = x * (za * zb) := by
      calc ι a * ι b * x * (ι b)⁻¹ * (ι a)⁻¹ = ι a * (ι b * x * (ι b)⁻¹) * (ι a)⁻¹ := by group
        _ = ι a * (x * zb) * (ι a)⁻¹ := by rw [hb]
        _ = (ι a * x * (ι a)⁻¹) * (ι a * zb * (ι a)⁻¹) := by group
        _ = x * (za * zb) := by rw [ha, e1, mul_assoc]
    have e4 : ι b * ι a * x * (ι a)⁻¹ * (ι b)⁻¹ = x * (zb * za) := by
      calc ι b * ι a * x * (ι a)⁻¹ * (ι b)⁻¹ = ι b * (ι a * x * (ι a)⁻¹) * (ι b)⁻¹ := by group
        _ = ι b * (x * za) * (ι b)⁻¹ := by rw [ha]
        _ = (ι b * x * (ι b)⁻¹) * (ι b * za * (ι b)⁻¹) := by group
        _ = x * (zb * za) := by rw [hb, e2, mul_assoc]
    have e5 : za * zb = zb * za := (Subgroup.mem_center_iff.mp hza zb).symm
    calc (ι a)⁻¹ * (ι b)⁻¹ * ι a * ι b * x
        = (ι a)⁻¹ * (ι b)⁻¹ * (ι a * ι b * x * (ι b)⁻¹ * (ι a)⁻¹) * (ι a * ι b) := by group
      _ = (ι a)⁻¹ * (ι b)⁻¹ * (ι b * ι a * x * (ι a)⁻¹ * (ι b)⁻¹) * (ι a * ι b) := by
        rw [e3, e4, e5]
      _ = x * ((ι a)⁻¹ * (ι b)⁻¹ * ι a * ι b) := by group
  have hc : ∀ a b : N, ι ⁅a, b⁆ ∈ Subgroup.center (GL (Fin 3) K) := by
    intro a b
    have := hcomm a⁻¹ b⁻¹
    simp only [map_inv, inv_inv] at this
    rwa [map_commutatorElement, commutatorElement_def]
  have hcN : commutator N ≤ Subgroup.center N := by
    rw [commutator_def, Subgroup.commutator_le]
    intro a _ b _
    refine Subgroup.mem_center_iff.mpr fun n => hι ?_
    rw [map_mul, map_mul]
    exact Subgroup.mem_center_iff.mp (hc a b) (ι n)
  refine ⟨⟨2, ?_⟩⟩
  rw [show derivedSeries N 2 = ⁅derivedSeries N 1, derivedSeries N 1⁆ from derivedSeries_succ N 1,
    derivedSeries_one]
  exact Subgroup.commutator_eq_bot_iff_le_centralizer.mpr
    (hcN.trans (Subgroup.center_le_centralizer _))

theorem isSolvable_of_extraspecial27_normal_K [Finite K] (_hHG : H ≤ G)
    (hnorm : ∀ g ∈ G, ∀ x ∈ H, g * x * g⁻¹ ∈ H)
    (hirr : IsIrreducibleMatrixRep H.subtype) (hcard : Nat.card ↥H = 27)
    (hext : CFSG.IsExtraspecialPGroup 3 ↥H) : Group.IsSolvable ↥G := by
  obtain ⟨hQcard, hQcomm, hQexp⟩ := hess_quotient hcard hext
  have hscalar : ∀ y : GL (Fin 3) K, (∀ x ∈ H, y * x = x * y) →
      y ∈ Subgroup.center (GL (Fin 3) K) := fun y hy =>
    hessK_mem_center_of_commute hirr (hess_not_isMulCommutative hcard hext) hy
  have hN := hessK_isSolvable_ker hnorm hscalar
  have hA := hess_isSolvable_mulAut hQcard hQcomm hQexp
  exact Group.isSolvable_of_ker_le_range (hessK_act hnorm).ker.subtype (hessK_act hnorm)
    (Subgroup.range_subtype _).ge

end CFSG.Quasithin.A312U3
