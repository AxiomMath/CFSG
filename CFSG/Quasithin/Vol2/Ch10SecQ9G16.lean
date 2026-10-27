module

public import CFSG.Quasithin.Vol2.Ch10SecQ9G15
public import CFSG.Quasithin.Vol2.Ch10SecC9S5c

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecC.C10P4F

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.H13 CFSG.QuasithinUnique

variable {G : Type} [Group G] [Finite G] {T L I J : Subgroup G} {t w : G}

theorem Conf.false_of_case5_A7 (c : Conf T L I t w J)
    (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat) (h1011 : Stmt10_1_1)
    (h1012 : Stmt10_1_2) (h1027 : Stmt10_2_7) (h322 : TmpL6_3_2_2_two) (hK8a : FactK8a)
    (hK8b : FactK8b) (hVe : IsElemAbelian 2 (VI T L I J w)) (hblk : IsExcA7Block J)
    (h5 : Case10_1_1Five T L I) : False := by
  have hyp := c.hyp
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hV1VI := c.fsuUL_le_VI h37 h38 h1011 h1012 h1027 h322 hK8a hK8b
    (Or.inr (cV1_eq_bot_of_case5 hyp h5))
  have hVIJ := c.VI_le_J h37 h38 h1011
  have hJN : J ≤ Subgroup.normalizer (VI T L I J w : Set G) :=
    le_sup_left.trans (le_normalizer_VI T L I J w)
  have hVI2 : IsPGroup 2 ↥(VI T L I J w) := fun x =>
    ⟨1, Subtype.ext (by simpa using hVe.2 x x.2)⟩
  have hVIO : VI T L I J w ≤ pCoreOf 2 J :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hVIJ hJN hVI2
  have hV1U : fsuUL T L I ≤ blockU J := by
    calc fsuUL T L I = ⁅fsuUL T L I, L⁆ := (commutator_fsuUL_eq hyp).symm
      _ ≤ ⁅pCoreOf 2 J, J⁆ := Subgroup.commutator_mono (hV1VI.trans hVIO) c.le
  have hV1Z : fsuUL T L I ⊓ blockZ J = ⊥ := by
    rw [eq_bot_iff, ← inf_centralizer_eq_bot_of_case5 hyp h5]
    rintro x ⟨hx1, -, hx2⟩
    exact ⟨hx1, Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr c.le) hx2⟩
  set B := (blockZ J).subgroupOf (blockU J) with hB
  set A := (fsuUL T L I).subgroupOf (blockU J) with hA
  have hUJ : blockU J ≤ J := by
    refine Subgroup.commutator_le.mpr fun a ha b hb => ?_
    have haJ : a ∈ J := CFSG.LieType.BorelTits.pCoreOf_le 2 J ha
    exact J.mul_mem (J.mul_mem (J.mul_mem haJ hb) (J.inv_mem haJ)) (J.inv_mem hb)
  have hBn : B.Normal := by
    refine ⟨fun z hz u => ?_⟩
    rw [hB, Subgroup.mem_subgroupOf] at hz ⊢
    have hzu : (u : G) * z = z * u :=
      (Subgroup.mem_centralizer_iff.mp hz.2 _ (hUJ u.2))
    have e1 : ((u * z * u⁻¹ : ↥(blockU J)) : G) = z := by
      rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, hzu, mul_inv_cancel_right]
    rw [e1]
    exact hz
  have h1 : B.relIndex A ∣ B.index := Subgroup.relIndex_dvd_index_of_normal B A
  have h2 : B.relIndex A = 64 := by
    have hdisj : B.subgroupOf A = ⊥ := by
      rw [Subgroup.subgroupOf_eq_bot, disjoint_iff, eq_bot_iff]
      rintro x ⟨hxB, hxA⟩
      have : (x : G) ∈ fsuUL T L I ⊓ blockZ J := ⟨hxA, hxB⟩
      rw [hV1Z, Subgroup.mem_bot] at this
      exact Subgroup.mem_bot.mpr (Subtype.ext this)
    rw [Subgroup.relIndex, hdisj, Subgroup.index_bot, hA,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hV1U).toEquiv, card_fsuUL_of_case5 hyp h5]
  rw [h2, hB, hblk.2.2] at h1
  norm_num at h1

end CFSG.Quasithin.Vol2.Ch10.SecC.C10P4F
