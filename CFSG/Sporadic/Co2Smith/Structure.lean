module

public import CFSG.Sporadic.Co2Smith.ResSp
public import CFSG.Sporadic.Co2Smith.Timmesfeld

public section

namespace CFSG.Sporadic.Co2Smith

open CFSG.Sporadic.Co2Cert CFSG.Sporadic.SmallF2 CFSG.Sporadic.SmallF2.Native Matrix
open CFSG.Assembly.LowTwoRank
open scoped Matrix

attribute [local irreducible] Matrix.instHMulOfFintypeOfMulOfAddCommMonoid

attribute [local instance] vAction

theorem z0_mem_Cz : z0 ∈ Cz := mem_Cz_of_comm rfl

theorem Qsub_le_Cz : Qsub ≤ Cz := by
  rw [Subgroup.closure_le]
  rintro _ (rfl | ⟨i, rfl⟩)
  · exact z0_mem_Cz
  · exact hE_mem_Cz i

theorem z0_fix_Zsub
    {v : V} (hv : v ∈ Zsub) : z0.val.val *ᵥ v = v := by
  obtain ⟨u, rfl⟩ := hv
  have hsq : z0.val.val * z0.val.val = 1 := by
    rw [← val_val_mul, seedA_mul_self, val_val_one]
  simp only [zEnd, Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, Matrix.mul_sub, hsq,
    Matrix.mul_one]
  funext i
  simp only [Matrix.sub_mulVec, Pi.sub_apply, Matrix.one_mulVec]
  generalize u i = a
  generalize (z0.val.val *ᵥ u) i = b
  revert a b
  decide

theorem Qsub_le_Zfix :
    Qsub ≤ Zfix := by
  rw [Subgroup.closure_le]
  rintro _ (rfl | ⟨i, rfl⟩) <;> rw [SetLike.mem_coe, mem_fixingSubgroup_iff] <;> intro v hv
  · exact z0_fix_Zsub hv
  · exact hE_fix_Zsub i hv

@[expose] noncomputable def prodMap
    (p : S0 × Qsub) : Cz :=
  ⟨p.1 * p.2, Cz.mul_mem (S0_le_Cz p.1.2) (Qsub_le_Cz p.2.2)⟩

theorem prodMap_injective :
    Function.Injective prodMap := by
  rintro ⟨s, q⟩ ⟨s', q'⟩ h
  have h1 : (s : K) * q = s' * q' := congrArg Subtype.val h
  have h2 : (s' : K)⁻¹ * s = q' * (q : K)⁻¹ :=
    calc (s' : K)⁻¹ * s = (s' : K)⁻¹ * (s * q) * (q : K)⁻¹ := by group
      _ = (s' : K)⁻¹ * (s' * q') * (q : K)⁻¹ := by rw [h1]
      _ = q' * (q : K)⁻¹ := by group
  have hmem : (s' : K)⁻¹ * s ∈ S0 ⊓ Qsub :=
    ⟨S0.mul_mem (S0.inv_mem s'.2) s.2, by rw [h2]; exact Qsub.mul_mem q'.2 (Qsub.inv_mem q.2)⟩
  rw [S0_inf_Q, Subgroup.mem_bot, inv_mul_eq_one] at hmem
  have hq : (q : K) = q' := by
    rw [← hmem] at h1
    exact mul_left_cancel h1
  exact Prod.ext (Subtype.ext hmem.symm) (Subtype.ext hq)

theorem card_S0_mul_le :
    Nat.card S0 * Nat.card Qsub ≤ Nat.card Cz := by
  rw [← Nat.card_prod]
  exact Nat.card_le_card_of_injective prodMap prodMap_injective

theorem card_S0 :
    Nat.card S0 = 1451520 := by
  have h1 := card_S0_ge
  have h2 := card_S0_mul_le
  rw [natCard_Q, natCard_centralizer_z0] at h2
  have h3 : 0 < Nat.card (Zfix ⊓ S0 : Subgroup K) := Nat.card_pos
  omega

theorem Zfix_inf_S0 :
    Zfix ⊓ S0 = ⊥ := by
  have h1 := card_S0_ge
  rw [card_S0] at h1
  have h3 : 0 < Nat.card (Zfix ⊓ S0 : Subgroup K) := Nat.card_pos
  exact Subgroup.eq_bot_of_card_eq _ (by omega)

theorem prodMap_bijective :
    Function.Bijective prodMap :=
  prodMap_injective.bijective_of_nat_card_le
    (by rw [Nat.card_prod, card_S0, natCard_Q, natCard_centralizer_z0]; norm_num)

theorem exists_mul_eq
    {g : K} (hg : g ∈ Cz) : ∃ s ∈ S0, ∃ q ∈ Qsub, s * q = g := by
  obtain ⟨⟨s, q⟩, h⟩ := prodMap_bijective.2 ⟨g, hg⟩
  exact ⟨s, s.2, q, q.2, congrArg Subtype.val h⟩

theorem Zfix_inf_Cz :
    Zfix ⊓ Cz = Qsub := by
  refine le_antisymm ?_ (le_inf Qsub_le_Zfix Qsub_le_Cz)
  rintro g ⟨hgZ, hgC⟩
  obtain ⟨s, hs, q, hq, rfl⟩ := exists_mul_eq hgC
  have hsZ : s ∈ Zfix := by
    have e : s = s * q * q⁻¹ := by group
    rw [e]
    exact Zfix.mul_mem hgZ (Zfix.inv_mem (Qsub_le_Zfix hq))
  have h : s ∈ Zfix ⊓ S0 := ⟨hsZ, hs⟩
  rw [Zfix_inf_S0, Subgroup.mem_bot] at h
  rw [h, one_mul]
  exact hq

theorem mem_ker_res
    (g : Cz) : res g = 1 ↔ (g : K) ∈ Qsub := by
  rw [res_eq_one_iff, ← Zfix_inf_Cz, Subgroup.mem_inf, mem_fixingSubgroup_iff]
  exact ⟨fun h => ⟨h, g.2⟩, fun h => h.1⟩

theorem ker_res :
    res.ker = Qsub.subgroupOf Cz := by
  ext g
  rw [MonoidHom.mem_ker, mem_ker_res, Subgroup.mem_subgroupOf]

theorem res_mem_statedSp :
    ∀ {s : K} (_ : s ∈ S0) (hC : s ∈ Cz),
    res ⟨s, hC⟩ ∈ StatedSp 3 (ZMod 2) := by
  intro s hs
  induction hs using Subgroup.closure_induction with
  | mem x hx =>
    intro hC
    rcases hx with rfl | rfl
    · exact res_aE_mem
    · exact res_bE_mem
  | one =>
    intro hC
    show res 1 ∈ StatedSp 3 (ZMod 2)
    rw [map_one]
    exact Subgroup.one_mem _
  | mul x y hx hy ihx ihy =>
    intro hC
    have e : (⟨x * y, hC⟩ : Cz) = ⟨x, S0_le_Cz hx⟩ * ⟨y, S0_le_Cz hy⟩ := rfl
    rw [e, map_mul]
    exact Subgroup.mul_mem _ (ihx _) (ihy _)
  | inv x hx ihx =>
    intro hC
    have e : (⟨x⁻¹, hC⟩ : Cz) = (⟨x, S0_le_Cz hx⟩ : Cz)⁻¹ := rfl
    rw [e, map_inv]
    exact Subgroup.inv_mem _ (ihx _)

theorem range_res_le :
    res.range ≤ StatedSp 3 (ZMod 2) := by
  rintro _ ⟨g, rfl⟩
  obtain ⟨s, hs, q, hq, hsq⟩ := exists_mul_eq g.2
  have e : g = ⟨s, S0_le_Cz hs⟩ * ⟨q, Qsub_le_Cz hq⟩ := Subtype.ext hsq.symm
  rw [e, map_mul, (mem_ker_res ⟨q, Qsub_le_Cz hq⟩).mpr hq, mul_one]
  exact res_mem_statedSp hs _

theorem natCard_Q_subgroupOf :
    Nat.card (Qsub.subgroupOf Cz) = 2 ^ 9 := by
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe Qsub_le_Cz).toEquiv, natCard_Q]

theorem card_range_res :
    Nat.card res.range = 1451520 := by
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup res.ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange res).toEquiv, ker_res,
    natCard_Q_subgroupOf, natCard_centralizer_z0] at h1
  omega

theorem range_res :
    res.range = StatedSp 3 (ZMod 2) :=
  Subgroup.eq_of_le_of_card_ge range_res_le (by rw [card_range_res]; exact natCard_sp62.le)

@[expose] noncomputable def resSp :
    Cz →* Sp62 :=
  res.codRestrict (StatedSp 3 (ZMod 2)) fun g => range_res_le ⟨g, rfl⟩

theorem resSp_surjective :
    Function.Surjective resSp := by
  rintro ⟨A, hA⟩
  rw [← range_res] at hA
  obtain ⟨g, hg⟩ := hA
  exact ⟨g, Subtype.ext hg⟩

theorem ker_resSp :
    resSp.ker = Qsub.subgroupOf Cz := by
  rw [resSp, MonoidHom.ker_codRestrict, ker_res]

instance Qsub_subgroupOf_normal :
    (Qsub.subgroupOf Cz).Normal := by
  rw [← ker_resSp]
  exact MonoidHom.normal_ker _

@[expose] noncomputable def quotientEquiv :
    Cz ⧸ Qsub.subgroupOf Cz ≃* Sp62 :=
  (QuotientGroup.quotientMulEquivOfEq ker_resSp.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective resSp resSp_surjective)

end CFSG.Sporadic.Co2Smith
