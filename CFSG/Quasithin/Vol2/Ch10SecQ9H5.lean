module

public import CFSG.Quasithin.Vol2.Ch10SecQ9H4

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecC.C10P4F

open Matrix CFSG.Assembly.LowTwoRank

variable {K : Type} [Field K]

abbrev ut3SL (K : Type) [Field K] : Subgroup ↥(StatedSL 3 K) := (ut3Sub K).subgroupOf (StatedSL 3 K)

@[expose] def ut3Proj (K : Type) [Field K] : Subgroup (StatedProj (StatedSL 3 K)) :=
  (ut3SL K).map (QuotientGroup.mk' _)

theorem eq_one_of_mk_eq_one {u : ↥(StatedSL 3 K)} (hu : u ∈ ut3SL K)
    (h : (QuotientGroup.mk' ((StatedScalars (Fin 3) K).subgroupOf (StatedSL 3 K)) u) = 1) :
    u = 1 := by
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at h
  obtain ⟨c, hc⟩ := h
  obtain ⟨a, b, d, hab⟩ := Subgroup.mem_subgroupOf.mp hu
  have hm := congrArg (fun g : GL (Fin 3) K => (g : Matrix (Fin 3) (Fin 3) K)) (hc.trans hab)
  simp only [coe_ut3, Matrix.GeneralLinearGroup.coe_scalar] at hm
  have h00 := congrFun (congrFun hm 0) 0
  have h01 := congrFun (congrFun hm 0) 1
  have h02 := congrFun (congrFun hm 0) 2
  have h12 := congrFun (congrFun hm 1) 2
  simp [utM] at h00 h01 h02 h12
  apply Subtype.ext
  rw [hab, ← h01, ← h02, ← h12]
  exact ut3_zero

theorem mk_injOn {u v : ↥(StatedSL 3 K)} (hu : u ∈ ut3SL K) (hv : v ∈ ut3SL K)
    (h : QuotientGroup.mk' ((StatedScalars (Fin 3) K).subgroupOf (StatedSL 3 K)) u =
      QuotientGroup.mk' ((StatedScalars (Fin 3) K).subgroupOf (StatedSL 3 K)) v) : u = v := by
  have h1 := eq_one_of_mk_eq_one (Subgroup.mul_mem _ (Subgroup.inv_mem _ hu) hv)
    (by rw [map_mul, map_inv, h, inv_mul_cancel])
  rw [inv_mul_eq_one] at h1
  exact h1

theorem card_ut3Proj [Finite K] : Nat.card (ut3Proj K) = Nat.card K ^ 3 := by
  have hbij : Function.Bijective (fun u : ↥(ut3SL K) => (⟨QuotientGroup.mk' _ (u : ↥(StatedSL 3 K)),
      Subgroup.mem_map_of_mem _ u.2⟩ : ↥(ut3Proj K))) := by
    refine ⟨fun u v h => Subtype.ext (mk_injOn u.2 v.2 (congrArg Subtype.val h)), fun p => ?_⟩
    obtain ⟨u, hu, hp⟩ := p.2
    exact ⟨⟨u, hu⟩, Subtype.ext hp⟩
  rw [← Nat.card_congr (Equiv.ofBijective _ hbij),
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe ut3Sub_le_statedSL).toEquiv, card_ut3Sub]

@[expose] def zSL (x : K) : ↥(StatedSL 3 K) := ⟨ut3 0 x 0, ut3Sub_le_statedSL (ut3_mem 0 x 0)⟩

theorem zSL_mem (x : K) : zSL x ∈ ut3SL K := Subgroup.mem_subgroupOf.mpr (ut3_mem 0 x 0)

@[expose] def zProj (x : K) : ↥(ut3Proj K) := ⟨_, Subgroup.mem_map_of_mem _ (zSL_mem x)⟩

theorem zProj_mem_center (x : K) : zProj x ∈ Subgroup.center ↥(ut3Proj K) := by
  rw [Subgroup.mem_center_iff]
  rintro ⟨_, u, hu, rfl⟩
  apply Subtype.ext
  obtain ⟨a, b, c, hab⟩ := Subgroup.mem_subgroupOf.mp hu
  show QuotientGroup.mk' _ u * QuotientGroup.mk' _ (zSL x) =
    QuotientGroup.mk' _ (zSL x) * QuotientGroup.mk' _ u
  rw [← map_mul, ← map_mul]
  congr 1
  apply Subtype.ext
  simp only [Subgroup.coe_mul, zSL, hab]
  exact (ut3_comm_centre x a b c).symm

theorem card_center_ut3Proj [Finite K] : Nat.card K ≤ Nat.card (Subgroup.center ↥(ut3Proj K)) := by
  refine Nat.card_le_card_of_injective (fun x => ⟨zProj x, zProj_mem_center x⟩) fun x y h => ?_
  have h1 := mk_injOn (zSL_mem x) (zSL_mem y)
    (congrArg Subtype.val (congrArg Subtype.val h))
  exact (ut3_injective (congrArg Subtype.val h1)).2.1

end CFSG.Quasithin.Vol2.Ch10.SecC.C10P4F
