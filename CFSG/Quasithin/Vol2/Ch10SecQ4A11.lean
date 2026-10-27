module

public import CFSG.Quasithin.Vol2.Ch10SecQ4A10
public import CFSG.LocalAnalysis.ComponentInitial.LocalComponents
public import CFSG.Quasithin.Background.A3Structure312Nonquasi
public import CFSG.Quasithin.Vol2.Ch1ModO2
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecF.C10E4

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

variable {G : Type} [Group G] {X J : Subgroup G}

theorem mem_cComp_self (hJ : J ∈ cComp X) : J ∈ cComp J :=
  ⟨hJ.1, hJ.2.1, IsSubnormal.refl J, fun K hKJ hK hKp hsub =>
    hJ.2.2.2 K hKJ hK hKp (A3.subnormal_trans hsub (subnormal_of_mem_cComp hJ))⟩

theorem top_mem_cComp_quot [Finite G] (hJ : J ∈ cComp X) :
    (⊤ : Subgroup (↥J ⧸ CFSG.pCore 2 ↥J)) ∈ cComp ⊤ := by
  have h := modO2Image_mem_cComp (mem_cComp_self hJ)
  have heq : modO2Image J J = ⊤ := by
    unfold modO2Image
    rw [Subgroup.subgroupOf_self, Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)]
  rwa [heq] at h

theorem sl2_one_ne_neg_one {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) :
    (1 : Matrix.SpecialLinearGroup (Fin 2) (ZMod p)) ≠ -1 := by
  intro h
  have h1 := congrArg (fun x : Matrix.SpecialLinearGroup (Fin 2) (ZMod p) =>
    (x : Matrix (Fin 2) (Fin 2) (ZMod p)) 0 0) h
  simp only [Matrix.SpecialLinearGroup.coe_one, Matrix.SpecialLinearGroup.coe_neg,
    Matrix.one_apply_eq, Matrix.neg_apply] at h1
  have h2 : ((2 : ℕ) : ZMod p) = 0 := by
    push_cast
    linear_combination h1
  rw [ZMod.natCast_eq_zero_iff] at h2
  exact hp2 ((Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) Nat.prime_two).mp h2)

theorem false_of_four {Y : Type} [Group Y] [Finite Y] (h36 : A36Statement Y)
    (hT : (⊤ : Subgroup Y) ∈ cComp ⊤) (hnq : ¬ CFSG.IsQuasisimple Y) {a b : Y} (ha : a ^ 2 = 1)
    (hb : b ^ 2 = 1) (ha1 : a ≠ 1) (hb1 : b ≠ 1) (hab : a ≠ b) (hc : a * b = b * a) : False := by
  have hS := h36 ⊤ hT
  have hnq' : ¬ CFSG.IsQuasisimple ↥(⊤ : Subgroup Y) := fun h =>
    hnq ((CFSG.LocalAnalysis.ComponentInitial.isQuasisimple_congr Subgroup.topEquiv).mp h)
  obtain ⟨p, hp, hp3, ⟨e⟩⟩ := A312.exists_isSL2_oddCore hS hnq'
  have : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := by omega
  let ψ : Y →* Matrix.SpecialLinearGroup (Fin 2) (ZMod p) :=
    e.toMonoidHom.comp ((QuotientGroup.mk' (CFSG.oddCore ↥(⊤ : Subgroup Y))).comp
      (Subgroup.topEquiv (G := Y)).symm.toMonoidHom)
  have hodd := A312.odd_card_oddCore ↥(⊤ : Subgroup Y)
  have key : ∀ y : Y, y ^ 2 = 1 → y ≠ 1 → ψ y = -1 := by
    intro y hy hy1
    refine sl2_eq_neg_one hp2 _ (by rw [← map_pow, hy, map_one]) fun h => ?_
    have h1 : QuotientGroup.mk' (CFSG.oddCore ↥(⊤ : Subgroup Y))
        ((Subgroup.topEquiv (G := Y)).symm y) = 1 := e.injective (by rw [map_one]; exact h)
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    have h2 : orderOf ((Subgroup.topEquiv (G := Y)).symm y) = 2 := by
      rw [MulEquiv.orderOf_eq]
      exact orderOf_eq_prime hy hy1
    have h3 : orderOf (⟨_, h1⟩ : ↥(CFSG.oddCore ↥(⊤ : Subgroup Y))) ∣
        Nat.card ↥(CFSG.oddCore ↥(⊤ : Subgroup Y)) := orderOf_dvd_natCard _
    rw [Subgroup.orderOf_mk, h2] at h3
    exact (Nat.not_even_iff_odd.mpr (hodd.of_dvd_nat h3)) even_two
  have hab1 : a * b ≠ 1 := by
    intro h
    have h1 : a = b⁻¹ := eq_inv_of_mul_eq_one_left h
    have h2 : b⁻¹ = b := inv_eq_iff_mul_eq_one.mpr (by rw [← sq, hb])
    exact hab (h1.trans h2)
  have habsq : (a * b) ^ 2 = 1 := by rw [Commute.mul_pow hc 2, ha, hb, one_mul]
  have h1 := key (a * b) habsq hab1
  rw [map_mul, key a ha ha1, key b hb hb1, neg_one_mul, neg_neg] at h1
  exact sl2_one_ne_neg_one hp2 h1

end CFSG.Quasithin.Vol2.Ch10.SecF.C10E4
