module

public import CFSG.Quasithin.Background.B1MoreQuot
public import CFSG.Quasithin.Background.B2FactorizationResidual
public import CFSG.Quasithin.Vol2.Ch10SecABasicAut
public import CFSG.Quasithin.Vol2.Ch10SecABasicV
public import CFSG.Quasithin.Vol2.Ch10SecAShape

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecA

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.H13 CFSG.QuasithinUnique
open scoped IsMulCommutative

@[expose] def Case10_1_1SevenWeak {G : Type} [Group G] (T L I : Subgroup G) : Prop :=
  ∃ n : ℕ, CFSG.Blueprint.SuzukiModel (↥L ⧸ CFSG.pCore 2 ↥L) 2 n ∧
    ∃ _ : IsMulCommutative ↥(fsuUL T L I),
      BinaryNaturalSz (V := ↥(fsuUL T L I)) (autOn L (fsuUL T L I)) ⊤ (Ch10.cV1 T L I) n

theorem sec_sq_eq_one {V : Type} [CommGroup V] (hV : ∀ v : V, v ^ 2 = 1) (W C : Subgroup V) :
    ∀ v : Sec W C, v ^ 2 = 1 := by
  intro v
  induction v using QuotientGroup.induction_on with
  | H w =>
    rw [← QuotientGroup.mk_pow, show w ^ 2 = 1 from Subtype.ext (by simpa using hV w),
      QuotientGroup.mk_one]

theorem equiv_SL_three_of_card
    {X : Type} [Group X] (hsh : IsShapeGroup X)
    (hc : Nat.card X = 168) : Nonempty (X ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) := by
  rcases hsh with ⟨n, -, K, _, _, hK, ⟨e⟩⟩ | ⟨n, -, a, -, K, _, _, hf, hK, ⟨e⟩⟩ | he
  · exfalso
    rw [Nat.card_congr e.toEquiv, card_SL_two_pow hK] at hc
    have hodd : Odd (4 ^ n - 1) := by
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · norm_num at hc
      · exact Nat.Even.sub_odd (Nat.one_le_pow _ _ (by norm_num))
          (Nat.even_pow.mpr ⟨by decide, by omega⟩) odd_one
    obtain ⟨rfl, h⟩ := two_pow_mul_odd_inj hodd (by decide : Odd 21)
      (hc.trans (by norm_num : (168 : ℕ) = 2 ^ 3 * 21))
    norm_num at h
  · exfalso
    subst hf
    rw [Nat.card_congr e.toEquiv, CFSG.LieType.Ree.suzuki_order hK] at hc
    exact three_not_dvd_card_suzuki a (hc ▸ (by norm_num : 3 ∣ 168))
  · exact he

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G}

theorem cV1_eq (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat)
    (hyp : Ch10.Hyp10 G T L I) :
    Ch10.cV1 T L I = (Subgroup.centralizer (L : Set G)).subgroupOf (fsuUL T L I) := by
  obtain ⟨t, ht, htn⟩ : ∃ t ∈ T, t ∉ Subgroup.normalizer (L : Set G) := by
    by_contra hne
    push Not at hne
    exact hyp.not_normal hne
  obtain ⟨_, -, -, ha, -⟩ := hyp.three
  have hUt := (ha t ht htn).2.2
  have hU0 : fsuUL T L I ⊓ Subgroup.centralizer (L : Set G) ≤
      Subgroup.centralizer (fsuL0 T L : Set G) := by
    rw [fsuL0_eq_sup h37 h38 hyp ht htn, Subgroup.le_centralizer_iff]
    refine sup_le ?_ ?_
    · rw [← Subgroup.le_centralizer_iff]
      exact inf_le_right
    · exact (Subgroup.le_centralizer_iff.mp hUt).trans (Subgroup.centralizer_le inf_le_left)
  ext u
  simp only [Ch10.cV1, Subgroup.mem_subgroupOf]
  exact ⟨fun h => Subgroup.centralizer_le (le_fsuL0 T L) h, fun h => hU0 ⟨u.2, h⟩⟩

theorem fixV_autOn_fsuUL (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat)
    (hyp : Ch10.Hyp10 G T L I) [IsMulCommutative ↥(fsuUL T L I)] :
    fixV (autOn L (fsuUL T L I)) = Ch10.cV1 T L I := by
  have hLV : L ≤ Subgroup.normalizer (fsuVM T L I : Set G) :=
    (le_fsuL0 T L).trans (fsuL0_le_normalizer_fsuVM T L I)
  have hLU : L ≤ Subgroup.normalizer (fsuUL T L I : Set G) :=
    le_normalizer_commutator hLV Subgroup.le_normalizer
  rw [cV1_eq h37 h38 hyp]
  ext v
  rw [mem_fixV_autOn hLU v, Subgroup.mem_subgroupOf]

end CFSG.Quasithin.Vol2.Ch10.SecA
