module

public import CFSG.Quasithin.Recognition.RuTypeJ44f
public import CFSG.Quasithin.Recognition.F112TitsMain
public import CFSG.Quasithin.Recognition.RuTypeJ44e

public section

namespace CFSG.Quasithin.RuType

open CFSG.Open CFSG.Quasithin CFSG.LieType.BorelTits CFSG.QuasithinUnique
open scoped MatrixGroups

namespace SL3

theorem x0_not_mem_Stab0 : x0 ∉ Stab0 := by decide

theorem Stab0_inf_Pl : ∀ g ∈ Stab0, g ∈ Pl → g ∈ P0 := by decide +kernel

end SL3

namespace RuDataM

variable {G : Type} [Group G] (M : RuDataM G) [Finite G]

theorem mem_T_of_θ_mem_P0 {x : G} (hxL : x ∈ M.L) (hx : M.θ ⟨x, hxL⟩ ∈ SL3.P0) :
    x ∈ (M.T : Subgroup G) := by
  rw [← M.hP0] at hx
  obtain ⟨t1, ht1, ht1θ⟩ := hx
  have ht1T : (t1 : G) ∈ (M.T : Subgroup G) := Subgroup.mem_subgroupOf.mp ht1
  have hsL : (t1 : G)⁻¹ * x ∈ M.L := mul_mem (inv_mem t1.2) hxL
  have hsS : (t1 : G)⁻¹ * x ∈ ruS M.L := by
    rw [M.mem_S_iff_θ hsL]
    have e : (⟨(t1 : G)⁻¹ * x, hsL⟩ : M.L) = t1⁻¹ * ⟨x, hxL⟩ := rfl
    rw [e, map_mul, map_inv, ht1θ, inv_mul_cancel]
  have e : x = (t1 : G) * ((t1 : G)⁻¹ * x) := by group
  rw [e]
  exact mul_mem ht1T (M.toRuData.S_le_T hsS)

theorem H_inf_G2_le_T {x : G} (hxH : x ∈ ruH M.T) (hxG : x ∈ M.G2) :
    x ∈ (M.T : Subgroup G) := by
  obtain ⟨hxL, hxP⟩ := mem_pullL.mp hxG
  have hLT1 : x ∈ M.LT1 := by
    rw [← M.L_inf_H]
    exact ⟨hxL, hxH⟩
  obtain ⟨hxL', hxS⟩ := mem_pullL.mp hLT1
  exact M.mem_T_of_θ_mem_P0 hxL (SL3.Stab0_inf_Pl _ hxS hxP)

theorem F1_inf_F2 : M.F1 ⊓ M.F2 = M.TF := by
  refine le_antisymm ?_ (le_inf M.TF_le_F1 M.TF_le_F2)
  have hle : M.F1 ⊓ M.F2 ≤ M.F1 ⊓ (M.T : Subgroup G) := fun x hx =>
    ⟨hx.1, M.H_inf_G2_le_T (M.F1_le_H hx.1) (M.F2_le_G2 hx.2)⟩
  have heq : M.F1 ⊓ (M.T : Subgroup G) = M.TF := by
    symm
    refine Subgroup.eq_of_le_of_card_ge (le_inf M.TF_le_F1 M.TF_le_T) ?_
    rw [M.card_TF]
    have hT : Nat.card (M.T : Subgroup G) = 2 ^ 14 := by
      rw [← M.toRuData.TL_eq, M.toRuData.card_TL]
    obtain ⟨k, hk, hcard⟩ := RuDataN.exists_card_eq_two_pow
      (inf_le_right : M.F1 ⊓ (M.T : Subgroup G) ≤ (M.T : Subgroup G)) hT
    have hdvd := Subgroup.card_dvd_of_le (inf_le_left : M.F1 ⊓ (M.T : Subgroup G) ≤ M.F1)
    rw [hcard, M.card_F1] at hdvd
    have hk12 : k ≤ 12 := by
      have hc : Nat.Coprime (2 ^ k) 5 := Nat.Coprime.pow_left k (by norm_num)
      exact (Nat.pow_dvd_pow_iff_le_right (by norm_num : 1 < 2)).mp
        (hc.dvd_of_dvd_mul_right hdvd)
    rw [hcard]
    exact Nat.pow_le_pow_right (by norm_num) hk12
  exact hle.trans heq.le

theorem x2el_not_mem_LT1 : M.x2el ∉ M.LT1 := by
  intro h
  obtain ⟨hL, hS⟩ := mem_pullL.mp h
  have : M.θ ⟨M.x2el, hL⟩ = SL3.x0 := M.θ_x2el
  rw [this] at hS
  exact SL3.x0_not_mem_Stab0 hS

theorem conjU_x2el_ne : M.conjU M.x2el ≠ ruU M.L M.T :=
  fun h => M.x2el_not_mem_LT1 ((M.conjU_eq_U_iff M.x2el_mem_L).mp h)

theorem conjU_x2el_le_W : M.conjU M.x2el ≤ M.W := by
  rintro _ ⟨u, hu, rfl⟩
  exact M.conj_mem_W M.x2el_mem_G2 (M.U_le_W hu)

theorem eq_of_mem_Z {c z : G} (hc : c ∈ ruZ M.T) (hc1 : c ≠ 1) (hz : z ∈ ruZ M.T) :
    z = 1 ∨ z = c := by
  classical
  by_contra h
  push Not at h
  have _ : Fintype ↥(ruZ M.T) := Fintype.ofFinite _
  have hs : ({⟨1, one_mem _⟩, ⟨c, hc⟩, ⟨z, hz⟩} : Finset ↥(ruZ M.T)).card = 3 := by
    rw [Finset.card_insert_of_notMem, Finset.card_pair]
    · intro he
      exact h.2 (congrArg Subtype.val he).symm
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨fun he => hc1 (congrArg Subtype.val he).symm,
        fun he => h.1 (congrArg Subtype.val he).symm⟩
  have := Finset.card_le_univ ({⟨1, one_mem _⟩, ⟨c, hc⟩, ⟨z, hz⟩} : Finset ↥(ruZ M.T))
  rw [hs, ← Nat.card_eq_fintype_card, M.toRuData.card_Z] at this
  omega

theorem card_mod_five {D : Subgroup G}
    (hDU : D ≤ ruU M.L M.T) (hZD : ruZ M.T ≤ D) (hbD : ∀ d ∈ D, M.b5el * d * M.b5el⁻¹ ∈ D) :
    Nat.card D % 5 = 2 := by
  classical
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have _ : Fintype ↥D := Fintype.ofFinite _
  let f : Function.End ↥D := fun d => ⟨M.b5el * d * M.b5el⁻¹, hbD d d.2⟩
  have hf5 : f ^ 5 ^ 1 = 1 := by
    rw [pow_one, show (5 : ℕ) = 0 + 1 + 1 + 1 + 1 + 1 from rfl, pow_succ, pow_succ, pow_succ,
      pow_succ, pow_succ, pow_zero, one_mul]
    funext d
    apply Subtype.ext
    show M.b5el * (M.b5el * (M.b5el * (M.b5el * (M.b5el * (d : G) * M.b5el⁻¹) * M.b5el⁻¹) *
      M.b5el⁻¹) * M.b5el⁻¹) * M.b5el⁻¹ = d
    have h5 := pow_five_of_orderOf M.orderOf_b5el
    calc _ = M.b5el ^ 5 * (d : G) * (M.b5el ^ 5)⁻¹ := by
          simp only [pow_succ, pow_zero, one_mul]
          group
      _ = d := by rw [h5, one_mul, inv_one, mul_one]
  have hmod := Equiv.Perm.card_fixedPoints_modEq (p := 5) (n := 1) hf5
  have hfix : Fintype.card (Function.fixedPoints f) = 2 := by
    rw [← Nat.card_eq_fintype_card, ← M.toRuData.card_Z]
    refine Nat.card_congr
      { toFun := fun d => ⟨d.1.1, ?_⟩
        invFun := fun z => ⟨⟨z.1, hZD z.2⟩, ?_⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    · have hd : M.b5el * d.1.1 * M.b5el⁻¹ = d.1.1 := congrArg Subtype.val d.2
      have hT5 : (d.1 : G) ∈ M.T5 M.b5el :=
        ⟨M.U_le_Q (hDU d.1.2), mem_G5.mpr (by
          calc (d.1 : G) * M.b5el = M.b5el * d.1.1 * M.b5el⁻¹ * M.b5el := by rw [hd]
            _ = M.b5el * d.1 := by group)⟩
      exact mem_Z_of_T5_U M.b5el_mem_H M.orderOf_b5el hT5 (hDU d.1.2)
    · apply Subtype.ext
      show M.b5el * z.1 * M.b5el⁻¹ = z.1
      rw [(M.toRuData.mem_H_iff.mp M.b5el_mem_H z.1 z.2).symm, mul_inv_cancel_right]
  rw [hfix, ← Nat.card_eq_fintype_card] at hmod
  exact hmod

theorem pCoreOf_F_eq_bot :
    pCoreOf 2 (M.F1 ⊔ M.F2 ⊔ M.TF) = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set F := M.F1 ⊔ M.F2 ⊔ M.TF with hF
  set K := pCoreOf 2 F with hKdef
  have hKp : IsPGroup 2 K := pCoreOf_isPGroup 2 F
  have hFK : F ≤ Subgroup.normalizer (K : Set G) := le_normalizer_pCoreOf 2 F
  have hF1 : M.F1 ≤ F := le_sup_left.trans le_sup_left
  have hF2 : M.F2 ≤ F := le_sup_right.trans le_sup_left
  have hTF : M.TF ≤ F := le_sup_right
  by_contra hK
  have hTK : M.TF ≤ Subgroup.normalizer (K : Set G) := hTF.trans hFK
  have hKTF : IsPGroup 2 ↥(K ⊔ M.TF) := by
    obtain ⟨a, ha⟩ := hKp.exists_card_eq
    have h := card_sup_mul_inf_of_normalizes (A := M.TF) (B := K) hTK
    rw [sup_comm, M.card_TF, ha] at h
    have hdvd : Nat.card ↥(K ⊔ M.TF) ∣ 2 ^ (12 + a) := by
      rw [pow_add]
      exact Dvd.intro _ h
    obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
    exact IsPGroup.of_card hm
  have hnil := hKTF.isNilpotent
  let H' : Subgroup ↥(K ⊔ M.TF) := K.subgroupOf (K ⊔ M.TF)
  have hH'n : H'.Normal := by
    refine ⟨fun x hx g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    have hgN : (g : G) ∈ Subgroup.normalizer (K : Set G) := sup_le Subgroup.le_normalizer hTK g.2
    have hc := (Subgroup.mem_normalizer_iff.mp hgN (x : G)).mp hx
    simpa using hc
  have hH'ne : H' ≠ ⊥ := by
    intro h
    apply hK
    rw [eq_bot_iff]
    intro x hx
    have : (⟨x, Subgroup.mem_sup_left hx⟩ : ↥(K ⊔ M.TF)) ∈ H' := hx
    rw [h, Subgroup.mem_bot] at this
    exact (Subgroup.mem_bot).mpr (congrArg Subtype.val this)
  obtain ⟨⟨⟨c, hcKT⟩, hcmem⟩, hc1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp
    (Group.IsNilpotent.inf_center_ne_bot_of_normal hH'ne)
  have hcK : c ∈ K := (Subgroup.mem_inf.mp hcmem).1
  have hcZ := (Subgroup.mem_inf.mp hcmem).2
  have hcne : c ≠ 1 := fun h => hc1 (Subtype.ext (Subtype.ext h))
  have hcT : ∀ t ∈ M.TF, t * c = c * t := by
    intro t ht
    have := Subgroup.mem_center_iff.mp hcZ ⟨t, Subgroup.mem_sup_right ht⟩
    exact congrArg Subtype.val this
  have hYTF : M.Ygrp ≤ M.TF := by
    rw [← M.TF_inf_Q]
    exact inf_le_left
  have hUTF : ruU M.L M.T ≤ M.TF := (M.U_le_Q5 M.b5el_mem_H).trans
    ((le_sup_left : M.Q5 M.b5el_mem_H ≤ M.Ygrp).trans hYTF)
  have hcU : ∀ u ∈ ruU M.L M.T, u * c = c * u := fun u hu => hcT u (hUTF hu)
  have hcHC : c ∈ M.HC :=
    Subgroup.mem_inf.mpr ⟨M.mem_H_of_centralizes_U hcU, Subgroup.mem_centralizer_iff.mpr hcU⟩
  have hcUmem : c ∈ ruU M.L M.T := by
    by_contra hcU'
    have hcard := M.card_le_of_centralizes_HC hcHC hcU' (X := M.Ygrp)
      (M.Y_le_Q5W_inf_Q.trans inf_le_right) (fun x hx => hcT x (hYTF hx))
    rw [M.card_Y] at hcard
    norm_num at hcard
  have hcZ' : c ∈ ruZ M.T := by
    refine M.mem_Z_of_comm_Q hcUmem fun q hq => ?_
    obtain ⟨a, ha, h, hh, rfl⟩ := exists_Q5_mul_HC M.b5el_mem_H M.orderOf_b5el hq
    have h1 := hcT a (Subgroup.mem_sup_right ha)
    have h2 : h * c = c * h :=
      ((Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hh).2 c hcUmem)).symm
    calc a * h * c = a * (h * c) := mul_assoc _ _ _
      _ = a * (c * h) := by rw [h2]
      _ = (a * c) * h := (mul_assoc _ _ _).symm
      _ = (c * a) * h := by rw [h1]
      _ = c * (a * h) := mul_assoc _ _ _
  have hxF : M.x2el ∈ F := hF2 M.x2el_mem_F2
  have hc'K : M.x2el * c * M.x2el⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.mp (hFK hxF) c).mp hcK
  have hcV : c ∈ ruV M.L := M.toRuData.Z_le_V hcZ'
  have hc'V : M.x2el * c * M.x2el⁻¹ ∈ ruV M.L := M.toRuData.conj_mem_V M.x2el_mem_L hcV
  have hc'U : M.x2el * c * M.x2el⁻¹ ∈ ruU M.L M.T := M.V_le_U hc'V
  have hc'Z : M.x2el * c * M.x2el⁻¹ ∉ ruZ M.T := by
    intro hZ
    rcases M.eq_of_mem_Z hcZ' hcne hZ with h | h
    · apply hcne
      have := congrArg (fun z => M.x2el⁻¹ * z * M.x2el) h
      simpa [mul_assoc] using this
    ·
      have hxH : M.x2el ∈ ruH M.T := by
        refine M.toRuData.mem_H_iff.mpr fun z hz => ?_
        rcases M.eq_of_mem_Z hcZ' hcne hz with hz1 | hzc
        · rw [hz1, one_mul, mul_one]
        · rw [hzc]
          calc c * M.x2el = M.x2el * c * M.x2el⁻¹ * M.x2el := by rw [h]
            _ = M.x2el * c := by group
      apply M.x2el_not_mem_LT1
      rw [← M.L_inf_H]
      exact ⟨M.x2el_mem_L, hxH⟩
  set D := K ⊓ ruU M.L M.T with hD
  have hZD : ruZ M.T ≤ D := by
    intro z hz
    rcases M.eq_of_mem_Z hcZ' hcne hz with hz1 | hzc
    · rw [hz1]
      exact one_mem _
    · rw [hzc]
      exact ⟨hcK, hcUmem⟩
  have hbD : ∀ d ∈ D, M.b5el * d * M.b5el⁻¹ ∈ D := by
    rintro d ⟨hdK, hdU⟩
    exact ⟨(Subgroup.mem_normalizer_iff.mp (hFK (hF1 M.b5el_mem_F1)) d).mp hdK,
      M.conj_mem_U M.b5el_mem_H hdU⟩
  have hmod := M.card_mod_five (inf_le_right : D ≤ ruU M.L M.T) hZD hbD
  obtain ⟨k, hk, hcardD⟩ := RuDataN.exists_card_eq_two_pow (inf_le_right : D ≤ ruU M.L M.T)
    (by rw [M.toRuData.card_U]; norm_num : Nat.card ↥(ruU M.L M.T) = 2 ^ 5)
  have hk2 : 2 ≤ k := by
    by_contra hk2
    have hle : Nat.card D ≤ 2 := by
      rw [hcardD]
      have hk1 : k ≤ 1 := by omega
      calc 2 ^ k ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) hk1
        _ = 2 := by norm_num
    classical
    have _ : Fintype ↥D := Fintype.ofFinite _
    have hs : ({⟨1, one_mem _⟩, ⟨c, hcK, hcUmem⟩, ⟨M.x2el * c * M.x2el⁻¹, hc'K, hc'U⟩} :
        Finset ↥D).card = 3 := by
      rw [Finset.card_insert_of_notMem, Finset.card_pair]
      · intro he
        have he' := congrArg Subtype.val he
        simp only at he'
        exact hc'Z (by rw [← he']; exact hcZ')
      · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        refine ⟨fun he => hcne (congrArg Subtype.val he).symm, fun he => hc'Z ?_⟩
        have he' := congrArg Subtype.val he
        simp only at he'
        rw [← he']
        exact one_mem _
    have := Finset.card_le_univ ({⟨1, one_mem _⟩, ⟨c, hcK, hcUmem⟩,
      ⟨M.x2el * c * M.x2el⁻¹, hc'K, hc'U⟩} : Finset ↥D)
    rw [hs, ← Nat.card_eq_fintype_card] at this
    omega
  have hk5 : k = 5 := by
    rw [hcardD] at hmod
    interval_cases k <;> first | rfl | (norm_num at hmod)
  have hDU : D = ruU M.L M.T := by
    refine Subgroup.eq_of_le_of_card_ge inf_le_right ?_
    rw [hcardD, hk5, M.toRuData.card_U]
    norm_num
  have hUK : ruU M.L M.T ≤ K := by
    rw [← hDU]
    exact inf_le_left
  have hKF1 : K ⊓ M.F1 ≤ M.Ygrp := by
    rw [← M.pCoreOf_F1]
    refine le_pCoreOf_of_le_normalizer 2 inf_le_right (fun f hf => ?_) (hKp.to_le inf_le_left)
    refine mem_normalizer_of_conj_mem fun x hx => Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · exact (Subgroup.mem_normalizer_iff.mp (hFK (hF1 hf)) x).mp (Subgroup.mem_inf.mp hx).1
    · exact mul_mem (mul_mem hf (Subgroup.mem_inf.mp hx).2) (inv_mem hf)
  have hle : M.conjU M.x2el ≤ ruQ M.T := by
    intro x hx
    have hxK : x ∈ K := by
      obtain ⟨u, hu, rfl⟩ := hx
      exact (Subgroup.mem_normalizer_iff.mp (hFK hxF) u).mp (hUK hu)
    have hxF1 : x ∈ M.F1 := M.Agrp_le_F1 (M.W_le_Agrp (M.conjU_x2el_le_W hx))
    exact M.Y_le_Q5W_inf_Q (hKF1 ⟨hxK, hxF1⟩) |>.2
  have hcard := M.card_conjU_inf_Q M.x2el_mem_L M.conjU_x2el_ne
  rw [inf_eq_left.mpr hle, M.card_conjU, M.toRuData.card_U] at hcard
  norm_num at hcard

theorem borelOf_F2_TF : borelOf M.F2 M.TF = M.TF := by
  unfold borelOf
  rw [inf_eq_left.mpr M.TF_le_F2]
  exact M.F2_inf_normalizer_TF

theorem borelOf_F1_TF : borelOf M.F1 M.TF = M.TF := by
  unfold borelOf
  rw [inf_eq_left.mpr M.TF_le_F1]
  exact M.F1_inf_normalizer_TF

theorem isPGroup_TF : IsPGroup 2 M.TF :=
  IsPGroup.of_card M.card_TF

theorem isRankOneListed_F1 :
    IsRankOneListed (oTwoQuot ↥M.F1) := by
  obtain ⟨e⟩ := M.nonempty_oTwoQuot_F1
  exact Or.inr (Or.inl ⟨0, ⟨e⟩⟩)

theorem isRankOneListed_F2 :
    IsRankOneListed (oTwoQuot ↥M.F2) := by
  obtain ⟨e⟩ := M.isL2Quot_F2
  exact Or.inl ⟨1, le_rfl, ⟨e⟩⟩

theorem hyp111 : Hyp111 M.F1 M.F2 M.TF where
  h1 :=
    { finite := inferInstance
      pgroup := M.isPGroup_TF
      normalizes := M.TF_le_F1.trans Subgroup.le_normalizer
      sylow := by rw [inf_eq_left.mpr M.TF_le_F1]; exact M.isSylowTwoOf_TF_F1
      listed := M.isRankOneListed_F1
      borel_le := by rw [M.borelOf_F2_TF]; exact M.TF_le_F1.trans Subgroup.le_normalizer
      charTwo := by
        rw [M.borelOf_F2_TF, sup_eq_left.mpr M.TF_le_F1, sup_eq_left.mpr M.TF_le_F1]
        exact M.charTwo_F1 }
  h2 :=
    { finite := inferInstance
      pgroup := M.isPGroup_TF
      normalizes := M.TF_le_F2.trans Subgroup.le_normalizer
      sylow := by rw [inf_eq_left.mpr M.TF_le_F2]; exact M.isSylowTwoOf_TF_F2
      listed := M.isRankOneListed_F2
      borel_le := by rw [M.borelOf_F1_TF]; exact M.TF_le_F2.trans Subgroup.le_normalizer
      charTwo := by
        rw [M.borelOf_F1_TF, sup_eq_left.mpr M.TF_le_F2, sup_eq_left.mpr M.TF_le_F2]
        exact M.charTwo_F2 }
  o2 := M.pCoreOf_F_eq_bot

theorem card_pCoreOf_F1 : Nat.card (pCoreOf 2 M.F1) = 2 ^ 10 := by
  rw [M.pCoreOf_F1, M.card_Y]

theorem case2F4 (hHay : HayashiFiveThree)
    (hQT : IsQuasithinSub (M.F1 ⊔ M.F2 ⊔ M.TF)) : Case2F4 M.F1 M.F2 := by
  obtain ⟨e⟩ := M.nonempty_oTwoQuot_F1
  rcases hHay G M.F1 M.F2 M.TF M.hyp111 hQT M.TF_le_F1 M.TF_le_F2 M.F1_inf_F2
      M.F1_inf_normalizer_TF M.F2_inf_normalizer_TF (Or.inr ⟨e⟩) M.isL2Quot_F2 with h | h
  · exfalso
    have := h.2.2.1
    rw [M.card_pCoreOf_F1] at this
    norm_num at this
  · exact h

end RuDataM

end CFSG.Quasithin.RuType
