module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.R8101RankFour
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenFortyFiveFixed
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenSixtyOneNonMainB
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TorusQSSL2
import CFSG.LocalAnalysis.UniquenessCase.UC22R8100BL2
public import CFSG.LocalAnalysis.UniquenessCase.UC6S846b
public import CFSG.Walter.W67.Section6.Util
import CFSG.LargeExtraspecial.S12Seven

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open Subgroup CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.UC22.F08
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

structure Ctx147 (D : Data G) (L : Fin 2 → Subgroup G) (n : Fin 2 → ℕ) (r p : ℕ)
    (A X B R : Subgroup G) : Prop where
  hH : Hyp8100 D L n r p A X
  hc : Case8100ThreeR D L p X
  hR : CFSG.ABGLocalTools.IsSylowOf r R X
  hB : B ≤ D.M
  hBp : Nat.card B = p
  hRB : ⁅R, B⁆ = R

namespace Ctx147

variable {D : Data G} {L : Fin 2 → Subgroup G} {n : Fin 2 → ℕ} {r p : ℕ} {A X B R : Subgroup G}

theorem p_eq (c : Ctx147 D L n r p A X B R) : p = 3 := c.hc.2.2.1

theorem three_mem_sig (c : Ctx147 D L n r p A X B R) : 3 ∈ D.sig :=
  c.p_eq ▸ c.hH.2.2.2.2.2.1

theorem card_B (c : Ctx147 D L n r p A X B R) : Nat.card B = 3 := c.p_eq ▸ c.hBp

theorem r_eq (c : Ctx147 D L n r p A X B R) : r = 7 := r_eq_seven_of_case8100Three c.hH c.hc

theorem R_le (c : Ctx147 D L n r p A X B R) : R ≤ D.M := by
  obtain ⟨hcal, -, -, -, -, -, -, -, hXset, -⟩ := c.hH
  intro x hx
  have hx' : x ∈ (L 0 : Set G) * (L 1 : Set G) := by rw [← hXset]; exact c.hR.le hx
  obtain ⟨a, ha, b, hb, rfl⟩ := Set.mem_mul.1 hx'
  exact D.M.mul_mem ((hcal 0).1.le ha) ((hcal 1).1.le hb)

theorem X_eq_sup (c : Ctx147 D L n r p A X B R) : X = L 0 ⊔ L 1 := by
  obtain ⟨-, -, -, -, -, -, -, -, hXset, -⟩ := c.hH
  apply SetLike.coe_injective
  rw [Subgroup.sup_eq_closure_mul, ← hXset, Subgroup.closure_eq]

theorem L_le_X (c : Ctx147 D L n r p A X B R) (i : Fin 2) : L i ≤ X := by
  rw [c.X_eq_sup]
  fin_cases i
  · exact le_sup_left
  · exact le_sup_right

theorem X_le_M (c : Ctx147 D L n r p A X B R) : X ≤ D.M := by
  obtain ⟨hcal, -⟩ := c.hH
  rw [c.X_eq_sup]
  exact sup_le (CFSG.Quasithin.A3.subnormal_le (hcal 0).1)
    (CFSG.Quasithin.A3.subnormal_le (hcal 1).1)

theorem M_le_normalizer_X (c : Ctx147 D L n r p A X B R) :
    D.M ≤ normalizer (X : Set G) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, hMX⟩ := c.hH
  exact hMX

theorem X_le_normalizer_L (c : Ctx147 D L n r p A X B R) (i : Fin 2) :
    X ≤ normalizer ((L i : Subgroup G) : Set G) := by
  obtain ⟨hcal, hne, -⟩ := c.hH
  have h01 : L 0 ≤ normalizer ((L 1 : Subgroup G) : Set G) :=
    calC_le_normalizer_of_ne (hcal 1) (hcal 0) hne.symm
  have h10 : L 1 ≤ normalizer ((L 0 : Subgroup G) : Set G) :=
    calC_le_normalizer_of_ne (hcal 0) (hcal 1) hne
  fin_cases i
  · rw [c.X_eq_sup]
    exact sup_le (L 0).le_normalizer h10
  · rw [c.X_eq_sup]
    exact sup_le h01 (L 1).le_normalizer

theorem L_subgroupOf_X_normal (c : Ctx147 D L n r p A X B R) (i : Fin 2) :
    ((L i).subgroupOf X).Normal :=
  Subgroup.normal_subgroupOf_of_le_normalizer (c.X_le_normalizer_L i)

theorem L_mem_calC_X (c : Ctx147 D L n r p A X B R) (i : Fin 2) : L i ∈ calC X := by
  obtain ⟨hcal, -⟩ := c.hH
  refine ⟨?_, (hcal i).2.1, (hcal i).2.2⟩
  exact CFSG.Open.IsSubnormal.step (c.L_le_X i) (c.L_subgroupOf_X_normal i)
    (CFSG.Open.IsSubnormal.refl X)

theorem R_inf_L_sylow (c : Ctx147 D L n r p A X B R) (i : Fin 2) :
    CFSG.ABGLocalTools.IsSylowOf 7 (R ⊓ L i) (L i) := by
  obtain ⟨-, -, -, hr, -⟩ := c.hH
  have : Fact r.Prime := ⟨hr⟩
  have h := c.hR.inf_of_le_normalizer (c.L_le_X i) (c.X_le_normalizer_L i)
  simpa [c.r_eq] using h

theorem isL2_Bar2 (c : Ctx147 D L n r p A X B R) (i : Fin 2) : IsL2 (Bar2 (L i)) 3 := by
  obtain ⟨-, hL2, -⟩ := c.hc
  have hne : L 0 ≠ L 1 := c.hH.2.1
  have hset := c.hc.1
  have hL1mem : L 1 ∈ conjSetOf D.M (L 0) := by
    have h : L 1 ∈ ({L 0, L 1} : Set (Subgroup G)) := by simp
    rwa [hset] at h
  fin_cases i
  · exact hL2
  · change IsL2 (Bar2 (L 1)) 3
    obtain ⟨m, -, hL1eq⟩ := hL1mem
    obtain ⟨e⟩ := uc22p20d_bar2_conj m (L 0)
    rw [hL1eq]
    exact CFSG.Blueprint.LieModel.of_mulEquiv e hL2

theorem card_Bar2 (c : Ctx147 D L n r p A X B R) (i : Fin 2) :
    Nat.card (Bar2 (L i)) = 504 := by
  have hcard := CFSG.GH74.card_of_lieModel_PSL (n := 2) (p := 2) (f := 3) (by norm_num)
    (c.isL2_Bar2 i)
  rw [hcard]
  norm_num [CFSG.Open.ordA]

theorem center_eq_bot_Bar2 (c : Ctx147 D L n r p A X B R) (i : Fin 2) :
    Subgroup.center (Bar2 (L i)) = ⊥ :=
  TorusQS.center_eq_bot_of_isL2 (c.isL2_Bar2 i)

theorem card_R_inf_L (c : Ctx147 D L n r p A X B R) (i : Fin 2) :
    Nat.card ↥(R ⊓ L i) = 7 := by
  have : Fact (Nat.Prime 7) := ⟨Nat.prime_seven⟩
  refine PartTwo.S17.card_sylow_seven_eq_seven (c.R_inf_L_sylow i) ?_ ?_
  · rw [c.card_Bar2 i]; norm_num
  · rw [c.card_Bar2 i]; norm_num

theorem factorization_seven_L (c : Ctx147 D L n r p A X B R) (i : Fin 2) :
    (Nat.card (L i)).factorization 7 = 1 := by
  have hcard : Nat.card (L i) =
      Nat.card (Bar2 (L i)) * Nat.card ↥(CFSG.pCore 2 ↥(L i)) :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup (CFSG.pCore 2 ↥(L i))
  have hzero : (Nat.card ↥(CFSG.pCore 2 ↥(L i))).factorization 7 = 0 := by
    obtain ⟨m, hm⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥(L i))).exists_card_eq
    rw [hm]
    exact Nat.factorization_eq_zero_of_not_dvd (by
      intro hd
      exact absurd (Nat.prime_seven.dvd_of_dvd_pow hd) (by norm_num))
  rw [hcard, Nat.factorization_mul Nat.card_pos.ne' Nat.card_pos.ne', Finsupp.add_apply,
    c.card_Bar2 i, hzero, add_zero]
  exact CFSG.GroupTheory.factorization_eq_one_of_dvd_of_not_sq_dvd Nat.prime_seven
    (by norm_num) (by norm_num) (by norm_num)

theorem factorization_seven_inf (c : Ctx147 D L n r p A X B R) :
    (Nat.card ↥(L 0 ⊓ L 1)).factorization 7 = 0 := by
  obtain ⟨hcal, hne, -⟩ := c.hH
  have hle : L 0 ⊓ L 1 ≤ CFSG.Open.pCoreOf 2 (L 0) :=
    (calC_inf_le_pCore_of_ne (hcal 0) (hcal 1) hne (c.center_eq_bot_Bar2 0)
      (c.center_eq_bot_Bar2 1)).trans inf_le_left
  obtain ⟨m, hm⟩ := (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (L 0)).to_le hle |>.exists_card_eq
  rw [hm]
  exact Nat.factorization_eq_zero_of_not_dvd (by
    intro hd
    exact absurd (Nat.prime_seven.dvd_of_dvd_pow hd) (by norm_num))

theorem factorization_seven_X (c : Ctx147 D L n r p A X B R) :
    (Nat.card X).factorization 7 = 2 := by
  obtain ⟨hcal, hne, -⟩ := c.hH
  have hfac := congrArg (fun t : ℕ => t.factorization 7)
    (card_sup_mul_card_inf_of_le_normalizer (A := L 0) (C := L 1)
      (calC_le_normalizer_of_ne (hcal 0) (hcal 1) hne))
  rw [sup_comm, ← c.X_eq_sup,
    Nat.factorization_mul Nat.card_pos.ne' Nat.card_pos.ne', Finsupp.add_apply,
    Nat.factorization_mul Nat.card_pos.ne' Nat.card_pos.ne', Finsupp.add_apply,
    c.factorization_seven_L 0, c.factorization_seven_L 1, c.factorization_seven_inf] at hfac
  omega

theorem card_R (c : Ctx147 D L n r p A X B R) : Nat.card R = 49 := by
  obtain ⟨-, -, -, hr, -⟩ := c.hH
  have : Fact r.Prime := ⟨hr⟩
  have h := c.hR.card_eq
  rw [c.r_eq, c.factorization_seven_X] at h
  norm_num at h
  exact h

theorem commute_R_inf_L (c : Ctx147 D L n r p A X B R) :
    ∀ x ∈ R ⊓ L 0, ∀ y ∈ R ⊓ L 1, x * y = y * x := by
  obtain ⟨hcal, hne, -⟩ := c.hH
  have hle : L 0 ⊓ L 1 ≤ CFSG.Open.pCoreOf 2 (L 0) :=
    (calC_inf_le_pCore_of_ne (hcal 0) (hcal 1) hne (c.center_eq_bot_Bar2 0)
      (c.center_eq_bot_Bar2 1)).trans inf_le_left
  obtain ⟨m, hm⟩ := (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (L 0)).exists_card_eq
  intro x hx y hy
  have hcomm2 : ⁅x, y⁆ ∈ CFSG.Open.pCoreOf 2 (L 0) :=
    (calC_commutator_le_of_ne (hcal 0) (hcal 1) hne
      (Subgroup.commutator_mem_commutator hx.2 hy.2)).1
  have hcommR : ⁅x, y⁆ ∈ R :=
    R.mul_mem (R.mul_mem (R.mul_mem hx.1 hy.1) (R.inv_mem hx.1)) (R.inv_mem hy.1)
  have hdvd2 : orderOf ⁅x, y⁆ ∣ 2 ^ m := by
    have := Subgroup.orderOf_dvd_natCard (CFSG.Open.pCoreOf 2 (L 0)) hcomm2
    rwa [hm] at this
  have hdvd7 : orderOf ⁅x, y⁆ ∣ 7 ^ 2 := by
    have h := Subgroup.orderOf_dvd_natCard R hcommR
    rw [c.card_R] at h
    exact h
  have hone := Nat.eq_one_of_dvd_coprimes
    (Nat.Coprime.pow (k := 2) (l := 7) m 2 (by norm_num)) hdvd2 hdvd7
  exact commutatorElement_eq_one_iff_mul_comm.mp (orderOf_eq_one_iff.mp hone)

theorem R_inf_L_inf_bot (c : Ctx147 D L n r p A X B R) :
    (R ⊓ L 0) ⊓ (R ⊓ L 1) = ⊥ := by
  obtain ⟨hcal, hne, -⟩ := c.hH
  have hle : L 0 ⊓ L 1 ≤ CFSG.Open.pCoreOf 2 (L 0) :=
    (calC_inf_le_pCore_of_ne (hcal 0) (hcal 1) hne (c.center_eq_bot_Bar2 0)
      (c.center_eq_bot_Bar2 1)).trans inf_le_left
  obtain ⟨m, hm⟩ := (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (L 0)).exists_card_eq
  have hle2 : (R ⊓ L 0) ⊓ (R ⊓ L 1) ≤ CFSG.Open.pCoreOf 2 (L 0) :=
    (le_inf (inf_le_left.trans inf_le_right) (inf_le_right.trans inf_le_right)).trans hle
  have hleR : (R ⊓ L 0) ⊓ (R ⊓ L 1) ≤ R := inf_le_left.trans inf_le_left
  have hcard : Nat.card ↥((R ⊓ L 0) ⊓ (R ⊓ L 1)) = 1 := by
    have hdvd2 := Subgroup.card_dvd_of_le hle2
    have hdvd7 := Subgroup.card_dvd_of_le hleR
    rw [hm] at hdvd2
    rw [c.card_R] at hdvd7
    norm_num at hdvd7
    exact Nat.eq_one_of_dvd_coprimes
      (Nat.Coprime.pow (k := 2) (l := 7) m 2 (by norm_num)) hdvd2 hdvd7
  exact Subgroup.card_eq_one.1 hcard

theorem R_eq_sup (c : Ctx147 D L n r p A X B R) :
    R = (R ⊓ L 0) ⊔ (R ⊓ L 1) := by
  have hprod := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute (R ⊓ L 0) (R ⊓ L 1)
    (c.commute_R_inf_L)).1
  rw [c.R_inf_L_inf_bot, Subgroup.card_bot, mul_one, c.card_R_inf_L 0,
    c.card_R_inf_L 1] at hprod
  have hcard : Nat.card ↥((R ⊓ L 0) ⊔ (R ⊓ L 1)) = 49 := by omega
  exact (Subgroup.eq_of_le_of_card_ge (sup_le inf_le_left inf_le_left)
    (by rw [c.card_R, hcard])).symm

theorem isElemAbelian_R (c : Ctx147 D L n r p A X B R) : IsElemAbelian 7 R := by
  have hR49 : Nat.card ↥R = 7 ^ 2 := by rw [c.card_R]; norm_num
  have hRcomm : IsMulCommutative ↥R :=
    IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 7) hR49
  refine ⟨hRcomm, ?_⟩
  have hprod := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute (R ⊓ L 0) (R ⊓ L 1)
    (c.commute_R_inf_L)).2
  rw [← c.R_eq_sup] at hprod
  intro x hx
  change x ∈ ((R : Set G)) at hx
  rw [hprod] at hx
  obtain ⟨a, ha, b, hb, rfl⟩ := Set.mem_mul.mp hx
  have haR : a ∈ R := (inf_le_left : R ⊓ L 0 ≤ R) ha
  have hbR : b ∈ R := (inf_le_left : R ⊓ L 1 ≤ R) hb
  have ha7 : a ^ 7 = 1 := by
    have h := pow_card_eq_one' (G := ↥(R ⊓ L 0)) (x := ⟨a, ha⟩)
    rw [c.card_R_inf_L 0] at h
    simpa using congrArg Subtype.val h
  have hb7 : b ^ 7 = 1 := by
    have h := pow_card_eq_one' (G := ↥(R ⊓ L 1)) (x := ⟨b, hb⟩)
    rw [c.card_R_inf_L 1] at h
    simpa using congrArg Subtype.val h
  have hcommab : Commute a b := by
    rw [commute_iff_eq]
    exact congrArg (fun z : ↥R => (z : G))
      (hRcomm.is_comm.comm (⟨a, haR⟩ : ↥R) ⟨b, hbR⟩)
  calc (a * b) ^ 7 = a ^ 7 * b ^ 7 := hcommab.mul_pow 7
    _ = 1 := by rw [ha7, hb7, mul_one]

theorem center_eq_bot_barImage (c : Ctx147 D L n r p A X B R) (i : Fin 2) :
    Subgroup.center ↥(barImage X (L i)) = ⊥ := by
  obtain ⟨e, -⟩ := uc22p22l_barImage_equiv (L := X) (K := L i) (c.L_mem_calC_X i)
  rw [eq_bot_iff]
  intro z hz
  rw [Subgroup.mem_bot]
  have hz' : e.symm z ∈ Subgroup.center (Bar2 (L i)) :=
    (MulEquivClass.apply_mem_center_iff e.symm).mpr hz
  rw [c.center_eq_bot_Bar2 i, Subgroup.mem_bot] at hz'
  simpa using congrArg e hz'

theorem kernel_le_normalizer_L (c : Ctx147 D L n r p A X B R) (i : Fin 2) :
    X ⊔ F08.CentOverO2 D.M X ≤ normalizer ((L i : Subgroup G) : Set G) := by
  obtain ⟨-, hne, -⟩ := c.hH
  have hset : ({L 0, L 1} : Set (Subgroup G)) = conjSetOf D.M (L 0) := by
    simpa [conjSetOf] using c.hc.1
  fin_cases i
  · exact PartTwo.S17.sup_centOverO2_le_normalizer_of_component c.X_le_M c.M_le_normalizer_X
      c.X_eq_sup hne hset (c.L_mem_calC_X 0) (c.L_mem_calC_X 1) (c.center_eq_bot_barImage 0)
  · have hL1mem : L 1 ∈ conjSetOf D.M (L 0) := by
      have h : L 1 ∈ ({L 0, L 1} : Set (Subgroup G)) := by simp
      rwa [hset] at h
    have hset' : ({L 1, L 0} : Set (Subgroup G)) = conjSetOf D.M (L 1) := by
      rw [uc22p2214_conjSetOf_eq hL1mem, Set.pair_comm]
      exact hset
    have hXeq : X = L 1 ⊔ L 0 := by rw [c.X_eq_sup, sup_comm]
    exact PartTwo.S17.sup_centOverO2_le_normalizer_of_component c.X_le_M c.M_le_normalizer_X
      hXeq hne.symm hset' (c.L_mem_calC_X 1) (c.L_mem_calC_X 0) (c.center_eq_bot_barImage 1)

theorem B_le_normalizer_R (c : Ctx147 D L n r p A X B R) :
    B ≤ normalizer (R : Set G) := by
  intro b hb
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  refine Subgroup.eq_of_le_of_card_ge ?_
    (by rw [Subgroup.card_map_of_injective (MulAut.conj b).injective])
  rintro _ ⟨x, hx, rfl⟩
  have hcomm : ⁅x, b⁆ ∈ R := by
    rw [← c.hRB]
    exact Subgroup.commutator_mem_commutator hx hb
  rw [commutatorElement_def] at hcomm
  have hmem : x⁻¹ * (x * b * x⁻¹ * b⁻¹) ∈ R := R.mul_mem (R.inv_mem hx) hcomm
  have hinv : (x⁻¹ * (x * b * x⁻¹ * b⁻¹))⁻¹ ∈ R := R.inv_mem hmem
  simpa [MulAut.conj_apply, mul_assoc] using hinv

theorem B_le_normalizer_L (c : Ctx147 D L n r p A X B R) (i : Fin 2) :
    B ≤ normalizer ((L i : Subgroup G) : Set G) := by
  obtain ⟨-, hne, -⟩ := c.hH
  have hset := c.hc.1
  intro b hbB
  have hbM : b ∈ D.M := c.hB hbB
  have hb3 : b ^ 3 = 1 := by
    have h := pow_card_eq_one' (G := ↥B) (x := ⟨b, hbB⟩)
    rw [c.card_B] at h
    simpa using congrArg Subtype.val h
  have hS2 : (conjSetOf D.M (L 0)).ncard = 2 := by
    rw [show conjSetOf D.M (L 0) = ({L 0, L 1} : Set (Subgroup G)) from hset.symm]
    exact Set.ncard_pair hne
  have hSφ : ∀ X ∈ conjSetOf D.M (L 0),
      X.map (MulAut.conj b).toMonoidHom ∈ conjSetOf D.M (L 0) := by
    intro X hX
    obtain ⟨m, hmM, rfl⟩ := hX
    exact ⟨b * m, D.M.mul_mem hbM hmM, uc22p22d_map_conj_map_conj (L 0) m b⟩
  have hLimem : L i ∈ conjSetOf D.M (L 0) := by
    have h : L i ∈ ({L 0, L 1} : Set (Subgroup G)) := by
      fin_cases i <;> simp
    rwa [hset] at h
  exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr
    (c23_map_conj_eq_of_odd_order hS2 (by decide : Odd 3) hb3 hSφ hLimem)

theorem B_le_normalizer_R_inf_L (c : Ctx147 D L n r p A X B R) (i : Fin 2) :
    B ≤ normalizer ((R ⊓ L i : Subgroup G) : Set G) := by
  intro b hbB
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  have hRmap : R.map (MulAut.conj b).toMonoidHom = R :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (c.B_le_normalizer_R hbB)
  have hLmap : (L i).map (MulAut.conj b).toMonoidHom = L i :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (c.B_le_normalizer_L i hbB)
  have hmap : (R ⊓ L i).map (MulAut.conj b).toMonoidHom = R ⊓ L i := by
    rw [Subgroup.map_inf_eq R (L i) (MulAut.conj b).toMonoidHom (MulAut.conj b).injective,
      hRmap, hLmap]
  simpa using hmap

theorem exists_generator_B (c : Ctx147 D L n r p A X B R) :
    ∃ b ∈ B, b ≠ 1 ∧ B = Subgroup.zpowers b := by
  have hB1 : 1 < Nat.card B := by rw [c.card_B]; norm_num
  have : Nontrivial ↥B := Finite.one_lt_card_iff_nontrivial.mp hB1
  obtain ⟨b, hb1⟩ := exists_ne (1 : ↥B)
  have hbB : (b : G) ∈ B := b.2
  refine ⟨(b : G), hbB, by simpa using hb1, ?_⟩
  have hzle : Subgroup.zpowers (b : G) ≤ B := Subgroup.zpowers_le.mpr hbB
  have hord : orderOf (b : G) = 3 := by
    have hdvd : orderOf (b : G) ∣ Nat.card B := Subgroup.orderOf_dvd_natCard B hbB
    rw [c.card_B] at hdvd
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) (by simpa using hb1)
    · exact h
  have hcardz : Nat.card ↥(Subgroup.zpowers (b : G)) = 3 := by
    rw [Nat.card_zpowers, hord]
  exact (Subgroup.eq_of_le_of_card_ge hzle (by rw [hcardz, c.card_B])).symm

theorem mulAut_eq_id_or_inv_of_sq_one {A : Type} [Group A] [Finite A] [IsCyclic A]
    (hcard : Nat.card A = 7) (α : MulAut A) (hα : α ^ 2 = 1) :
    (∀ x, α x = x) ∨ (∀ x, α x = x⁻¹) := by
  obtain ⟨m, hm⟩ := MonoidHom.map_cyclic α.toMonoidHom
  have hm' : ∀ x : A, α x = x ^ m := fun x => hm x
  have hα2 : ∀ x, α (α x) = x := by
    intro x
    have h := congrArg (fun f : MulAut A => f x) hα
    simpa [pow_two, MulAut.mul_apply] using h
  have hm2 : ∀ x : A, x ^ (m * m) = x := by
    intro x
    calc x ^ (m * m) = (x ^ m) ^ m := by rw [zpow_mul]
      _ = (α x) ^ m := by rw [hm' x]
      _ = α (α x) := (hm' (α x)).symm
      _ = x := hα2 x
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := A)
  have hgtop : Subgroup.zpowers g = ⊤ := le_antisymm le_top (fun x _ => hg x)
  have hgord : orderOf g = 7 := by
    rw [← Nat.card_zpowers, hgtop, Subgroup.card_top, hcard]
  have hmod : m * m ≡ 1 [ZMOD 7] := by
    have h := (zpow_eq_zpow_iff_modEq (x := g) (m := m * m) (n := 1)).mp (by
      simpa using hm2 g)
    rwa [hgord] at h
  have hz : ((m : ZMod 7)) ^ 2 = 1 := by
    have h : ((m * m : ℤ) : ZMod 7) = ((1 : ℤ) : ZMod 7) :=
      (ZMod.intCast_eq_intCast_iff (m * m) 1 7).mpr hmod
    simpa [Int.cast_mul, sq] using h
  have hu : (m : ZMod 7) = 1 ∨ (m : ZMod 7) = -1 := by
    have key : ∀ u : ZMod 7, u ^ 2 = 1 → u = 1 ∨ u = -1 := by decide
    exact key _ hz
  have hm1 : m ≡ 1 [ZMOD 7] ∨ m ≡ -1 [ZMOD 7] := by
    rcases hu with h | h
    · exact Or.inl ((ZMod.intCast_eq_intCast_iff m 1 7).mp (by simpa using h))
    · exact Or.inr ((ZMod.intCast_eq_intCast_iff m (-1) 7).mp (by simpa using h))
  rcases hm1 with hm1 | hm1
  · left
    intro x
    rw [hm' x]
    have hxdvd : orderOf x ∣ 7 := by
      rw [← hcard]
      exact orderOf_dvd_natCard x
    have hdvd7 : (7 : ℤ) ∣ (1 - m) := Int.modEq_iff_dvd.mp hm1
    have hdvd : ((orderOf x : ℕ) : ℤ) ∣ (1 - m) :=
      (Int.natCast_dvd_natCast.mpr hxdvd).trans hdvd7
    simpa using (zpow_eq_zpow_iff_modEq (x := x) (m := m) (n := 1)).mpr
      (Int.modEq_iff_dvd.mpr hdvd)
  · right
    intro x
    rw [hm' x]
    have hxdvd : orderOf x ∣ 7 := by
      rw [← hcard]
      exact orderOf_dvd_natCard x
    have hdvd7 : (7 : ℤ) ∣ (-1 - m) := Int.modEq_iff_dvd.mp hm1
    have hdvd : ((orderOf x : ℕ) : ℤ) ∣ (-1 - m) :=
      (Int.natCast_dvd_natCast.mpr hxdvd).trans hdvd7
    have hmodx : m ≡ -1 [ZMOD orderOf x] := Int.modEq_iff_dvd.mpr hdvd
    simpa using (zpow_eq_zpow_iff_modEq (x := x) (m := m) (n := -1)).mpr hmodx

theorem barImage_R_inf_L_sylow (c : Ctx147 D L n r p A X B R) (i : Fin 2) :
    CFSG.ABGLocalTools.IsSylowOf 7 (barImage (L i) (R ⊓ L i)) ⊤ :=
  u4x_isSylowOf_barImage (c.R_inf_L_sylow i)

theorem kernel_rhoL_inner (c : Ctx147 D L n r p A X B R) (i : Fin 2) {y : G}
    (hyN : y ∈ X ⊔ F08.CentOverO2 D.M X) :
    UC6S846.rhoL (L i) ⟨y, c.kernel_le_normalizer_L i hyN⟩ ∈
      CFSG.ComponentClassification.OuterAutomorphisms.inner (Bar2 (L i)) := by
  obtain ⟨hcal, hne, -⟩ := c.hH
  fin_cases i
  · exact PartTwo.S17.rhoL_mem_inner_of_mem_sup_centOverO2 c.X_le_M c.M_le_normalizer_X
      (by rw [c.X_eq_sup, sup_comm]) hne.symm (hcal 1) (hcal 0) (c.L_mem_calC_X 1)
      (c.L_mem_calC_X 0) (c.kernel_le_normalizer_L 0) hyN
  · exact PartTwo.S17.rhoL_mem_inner_of_mem_sup_centOverO2 c.X_le_M c.M_le_normalizer_X
      c.X_eq_sup hne (hcal 0) (hcal 1) (c.L_mem_calC_X 0) (c.L_mem_calC_X 1)
      (c.kernel_le_normalizer_L 1) hyN

theorem kernel_inner_data (c : Ctx147 D L n r p A X B R) (i : Fin 2) {y : G}
    (hyN : y ∈ X ⊔ F08.CentOverO2 D.M X)
    (hyR : y ∈ normalizer (R : Set G)) :
    ∃ tbar : Bar2 (L i),
      UC6S846.rhoL (L i) ⟨y, c.kernel_le_normalizer_L i hyN⟩ = MulAut.conj tbar ∧
      tbar ∈ normalizer ((barImage (L i) (R ⊓ L i) : Subgroup (Bar2 (L i))) :
        Set (Bar2 (L i))) ∧ ¬ 3 ∣ orderOf tbar := by
  have hyL : y ∈ normalizer ((L i : Subgroup G) : Set G) := c.kernel_le_normalizer_L i hyN
  have hyH : y ∈ normalizer ((R ⊓ L i : Subgroup G) : Set G) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    have hRmap : R.map (MulAut.conj y).toMonoidHom = R :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp hyR
    have hLmap : (L i).map (MulAut.conj y).toMonoidHom = L i :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp hyL
    have hmap : (R ⊓ L i).map (MulAut.conj y).toMonoidHom = R ⊓ L i := by
      rw [Subgroup.map_inf_eq R (L i) (MulAut.conj y).toMonoidHom (MulAut.conj y).injective,
        hRmap, hLmap]
    simpa using hmap
  obtain ⟨tbar, htbar⟩ := c.kernel_rhoL_inner i hyN
  set S : Subgroup (Bar2 (L i)) := barImage (L i) (R ⊓ L i) with hS
  have hSy : S.map ((UC6S846.rhoL (L i) ⟨y, hyL⟩).toMonoidHom) = S := by
    refine Subgroup.eq_of_le_of_card_ge ?_
      (by
        have hcardmap : Nat.card (S.map ((UC6S846.rhoL (L i) ⟨y, hyL⟩).toMonoidHom)) =
            Nat.card S :=
          Subgroup.card_map_of_injective (UC6S846.rhoL (L i) ⟨y, hyL⟩).injective
        omega)
    rintro _ ⟨s, hs, rfl⟩
    rw [hS, barImage] at hs ⊢
    obtain ⟨x, hx, hxval⟩ := Subgroup.mem_map.mp hs
    have hxR : (x : G) ∈ R ⊓ L i := Subgroup.mem_subgroupOf.mp hx
    have hLmem : y * (x : G) * y⁻¹ ∈ L i :=
      (Subgroup.mem_normalizer_iff.mp hyL (x : G)).mp hxR.2
    have hRmem : y * (x : G) * y⁻¹ ∈ R :=
      (Subgroup.mem_normalizer_iff.mp hyR (x : G)).mp hxR.1
    refine ⟨⟨y * (x : G) * y⁻¹, hLmem⟩, ?_, ?_⟩
    · exact Subgroup.mem_subgroupOf.mpr ⟨hRmem, hLmem⟩
    · have h1 : (UC6S846.rhoL (L i) ⟨y, hyL⟩) (QuotientGroup.mk x) =
          QuotientGroup.mk' _ ⟨y * (x : G) * y⁻¹, hLmem⟩ := by
        rw [UC6S846.rhoL_mk (L i) _ x]
        congr 1
      have h2 : (MulAut.conj tbar) s =
          QuotientGroup.mk' _ ⟨y * (x : G) * y⁻¹, hLmem⟩ := by
        rw [← hxval]
        simpa [← htbar] using h1
      rw [← htbar]
      exact h2.symm
  have hSconj : S.map (MulAut.conj tbar).toMonoidHom = S := by
    have h : (MulAut.conj tbar).toMonoidHom =
        (UC6S846.rhoL (L i) ⟨y, hyL⟩).toMonoidHom := by
      rw [htbar]
    rw [h, hSy]
  have htbarN : tbar ∈ normalizer (S : Set (Bar2 (L i))) :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mpr hSconj
  refine ⟨tbar, htbar.symm, htbarN, ?_⟩
  have hSyl : CFSG.ABGLocalTools.IsSylowOf 7 S ⊤ := by
    rw [hS]
    exact c.barImage_R_inf_L_sylow i
  have hKbar : IsL2 (⊤ : Subgroup (Bar2 (L i))) 3 :=
    CFSG.Blueprint.LieModel.of_mulEquiv (Subgroup.topEquiv.symm) (c.isL2_Bar2 i)
  have hnot3 := uc22r8100b_not_dvd_normalizer_of_le (Γ := Bar2 (L i)) (K := ⊤) (S := S)
    (n := 3) hKbar (by norm_num : Nat.Prime 3) (by norm_num : (3 : ℕ) ≠ 2)
    (by norm_num : 3 ∣ 2 ^ 3 + 1) (by norm_num : Nat.Prime 7)
    (by norm_num : 7 ∣ 2 ^ 3 - 1) hSyl
  intro hdvd
  have hcardz : 3 ∣ Nat.card ↥(Subgroup.zpowers tbar) := by
    rwa [Nat.card_zpowers]
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card'
    (G := ↥(Subgroup.zpowers tbar)) 3 hcardz
  have hgN : (g : Bar2 (L i)) ∈ normalizer (S : Set (Bar2 (L i))) :=
    Subgroup.zpowers_le.mpr htbarN g.2
  have hgord : orderOf (g : Bar2 (L i)) = 3 := by
    rw [Subgroup.orderOf_coe, hg]
  exact hnot3 (g : Bar2 (L i)) (Subgroup.mem_top _) hgN hgord

theorem R_inf_L_inf_pCore_bot (c : Ctx147 D L n r p A X B R) (i : Fin 2) :
    (R ⊓ L i) ⊓ CFSG.Open.pCoreOf 2 (L i) = ⊥ := by
  have : Fact (Nat.Prime 7) := ⟨Nat.prime_seven⟩
  have hH7 : IsPGroup 7 ((R ⊓ L i).subgroupOf (L i)) :=
    (c.R_inf_L_sylow i).isPGroup.comap_subtype
  have hnotdvd : ¬ 7 ∣ Nat.card ↥(CFSG.pCore 2 ↥(L i)) := by
    obtain ⟨m, hm⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥(L i))).exists_card_eq
    rw [hm]
    intro hd
    exact absurd (Nat.prime_seven.dvd_of_dvd_pow hd) (by norm_num)
  have hbot := CFSG.GroupTheory.SteinbergBS.inf_eq_bot_of_isPGroup_of_not_dvd
    (p := 7) (N := CFSG.pCore 2 ↥(L i)) hnotdvd hH7
  have hmap : ((R ⊓ L i).subgroupOf (L i) ⊓ CFSG.pCore 2 ↥(L i)).map (L i).subtype = ⊥ := by
    rw [hbot, Subgroup.map_bot]
  rw [Subgroup.map_inf_eq ((R ⊓ L i).subgroupOf (L i)) (CFSG.pCore 2 ↥(L i))
    (L i).subtype (L i).subtype_injective] at hmap
  rw [Subgroup.map_subgroupOf_eq_of_le (inf_le_right : R ⊓ L i ≤ L i)] at hmap
  change R ⊓ L i ⊓ (CFSG.pCore 2 ↥(L i)).map (L i).subtype = ⊥
  exact hmap

theorem card_barImage_R_inf_L (c : Ctx147 D L n r p A X B R) (i : Fin 2) :
    Nat.card ↥(barImage (L i) (R ⊓ L i)) = 7 := by
  have hH7 : IsPGroup 7 ((R ⊓ L i).subgroupOf (L i)) :=
    (c.R_inf_L_sylow i).isPGroup.comap_subtype
  have hnotdvd : ¬ 7 ∣ Nat.card ↥(CFSG.pCore 2 ↥(L i)) := by
    obtain ⟨m, hm⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥(L i))).exists_card_eq
    rw [hm]
    intro hd
    exact absurd (Nat.prime_seven.dvd_of_dvd_pow hd) (by norm_num)
  have hbot := CFSG.GroupTheory.SteinbergBS.inf_eq_bot_of_isPGroup_of_not_dvd
    (p := 7) (N := CFSG.pCore 2 ↥(L i)) hnotdvd hH7
  have hdisj : Disjoint ((R ⊓ L i).subgroupOf (L i))
      (QuotientGroup.mk' (CFSG.pCore 2 ↥(L i))).ker := by
    rw [show (QuotientGroup.mk' (CFSG.pCore 2 ↥(L i))).ker = CFSG.pCore 2 ↥(L i) from
      QuotientGroup.ker_mk' _]
    exact disjoint_iff.mpr hbot
  rw [barImage, UC6S846.card_map_of_disjoint_ker _ _ hdisj,
    ← c.card_R_inf_L i]
  exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (c.R_inf_L_sylow i).le).toEquiv

theorem kernel_acts_pm_one (c : Ctx147 D L n r p A X B R) (i : Fin 2) {y : G}
    (hyN : y ∈ X ⊔ F08.CentOverO2 D.M X)
    (hyR : y ∈ normalizer (R : Set G)) :
    (∀ x ∈ R ⊓ L i, y * x * y⁻¹ = x) ∨
      ∀ x ∈ R ⊓ L i, y * x * y⁻¹ = x⁻¹ := by
  have hyL : y ∈ normalizer ((L i : Subgroup G) : Set G) := c.kernel_le_normalizer_L i hyN
  have hyH : y ∈ normalizer ((R ⊓ L i : Subgroup G) : Set G) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    have hRmap : R.map (MulAut.conj y).toMonoidHom = R :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp hyR
    have hLmap : (L i).map (MulAut.conj y).toMonoidHom = L i :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp hyL
    have hmap : (R ⊓ L i).map (MulAut.conj y).toMonoidHom = R ⊓ L i := by
      rw [Subgroup.map_inf_eq R (L i) (MulAut.conj y).toMonoidHom (MulAut.conj y).injective,
        hRmap, hLmap]
    simpa using hmap
  obtain ⟨tbar, htbar, htbarN, hnot3⟩ := c.kernel_inner_data i hyN hyR
  let H : Subgroup G := R ⊓ L i
  let S : Subgroup (Bar2 (L i)) := barImage (L i) H
  let mk : ↥(L i) →* Bar2 (L i) := QuotientGroup.mk' (CFSG.pCore 2 ↥(L i))
  let mkH : ↥H →* Bar2 (L i) :=
    mk.comp (Subgroup.inclusion (show H ≤ L i from inf_le_right))
  have hScard : Nat.card ↥S = 7 := by
    change Nat.card ↥(barImage (L i) (R ⊓ L i)) = 7
    exact c.card_barImage_R_inf_L i
  have : Fact (Nat.Prime 7) := ⟨Nat.prime_seven⟩
  have : IsCyclic ↥S := isCyclic_of_prime_card hScard
  have hcardAut : Nat.card (MulAut ↥S) = 6 := by
    rw [IsCyclic.card_mulAut, hScard, Nat.totient_prime Nat.prime_seven]
  let α : MulAut ↥S := S.normalizerMonoidHom ⟨tbar, htbarN⟩
  have hαdvd_t : orderOf α ∣ orderOf tbar := by
    have h := orderOf_map_dvd (S.normalizerMonoidHom) ⟨tbar, htbarN⟩
    rwa [← Subgroup.orderOf_coe] at h
  have hαdvd6 : orderOf α ∣ 6 := by
    rw [← hcardAut]
    exact orderOf_dvd_natCard α
  have hαdvd2 : orderOf α ∣ 2 := by
    have h3 : ¬ 3 ∣ orderOf α := fun h => hnot3 (h.trans hαdvd_t)
    have hpos : 0 < orderOf α := orderOf_pos α
    have hle : orderOf α ≤ 6 := Nat.le_of_dvd (by norm_num) hαdvd6
    interval_cases orderOf α <;> norm_num at *
  have hα2 : α ^ 2 = 1 := (orderOf_dvd_iff_pow_eq_one).mp hαdvd2
  have hαsq : ∀ s : ↥S, α (α s) = s := by
    intro s
    have h := congrArg (fun f : MulAut ↥S => (f s : ↥S)) hα2
    simpa [pow_two, MulAut.mul_apply] using h
  have hymem : ∀ x : ↥H, y * (x : G) * y⁻¹ ∈ H := by
    intro x
    exact ⟨(Subgroup.mem_normalizer_iff.mp hyR (x : G)).mp x.2.1,
      (Subgroup.mem_normalizer_iff.mp hyL (x : G)).mp x.2.2⟩
  have hmkH : ∀ x : ↥H, mkH x ∈ S := by
    intro x
    change mkH x ∈ barImage (L i) H
    rw [barImage]
    refine Subgroup.mem_map.mpr ⟨⟨x, ?_⟩, ?_, ?_⟩
    · exact x.2.2
    · exact Subgroup.mem_subgroupOf.mpr x.2
    · rfl
  let sx : ↥H → ↥S := fun x => ⟨mkH x, hmkH x⟩
  have hsx_act : ∀ x : ↥H, α (sx x) = sx ⟨y * (x : G) * y⁻¹, hymem x⟩ := by
    intro x
    apply Subtype.ext
    change (α (sx x) : Bar2 (L i)) = mkH ⟨y * (x : G) * y⁻¹, hymem x⟩
    have hαapp : (α (sx x) : Bar2 (L i)) = tbar * (sx x : Bar2 (L i)) * tbar⁻¹ := rfl
    rw [hαapp]
    change tbar * mkH x * tbar⁻¹ = mkH ⟨y * (x : G) * y⁻¹, hymem x⟩
    rw [← MulAut.conj_apply, ← htbar]
    have hrho : (UC6S846.rhoL (L i) ⟨y, hyL⟩) (mkH x) =
        mkH ⟨y * (x : G) * y⁻¹, hymem x⟩ := by
      change (UC6S846.rhoL (L i) ⟨y, hyL⟩)
          (QuotientGroup.mk ⟨(x : G), x.2.2⟩) = _
      rw [UC6S846.rhoL_mk (L i) _ ⟨(x : G), x.2.2⟩]
      congr 1
    exact hrho
  have hsx_inj : Function.Injective sx := by
    intro a b hab
    have hmk : mkH a = mkH b := congrArg (fun z : ↥S => (z : Bar2 (L i))) hab
    have hmul : mkH (a * b⁻¹) = 1 := by
      rw [map_mul, map_inv, hmk, mul_inv_cancel]
    have habH : (a : G) * (b : G)⁻¹ ∈ H := H.mul_mem a.2 (H.inv_mem b.2)
    have hmemK : (a : G) * (b : G)⁻¹ ∈ CFSG.Open.pCoreOf 2 (L i) := by
      rw [CFSG.Open.pCoreOf]
      refine Subgroup.mem_map.mpr ⟨⟨(a : G) * (b : G)⁻¹, habH.2⟩, ?_, rfl⟩
      refine (QuotientGroup.eq_one_iff _).mp ?_
      simpa [mkH, mk, Subgroup.inclusion] using hmul
    have hmem : (a : G) * (b : G)⁻¹ ∈ H ⊓ CFSG.Open.pCoreOf 2 (L i) :=
      ⟨habH, hmemK⟩
    rw [c.R_inf_L_inf_pCore_bot i, Subgroup.mem_bot] at hmem
    exact Subtype.ext (eq_of_mul_inv_eq_one hmem)
  have hy2 : ∀ x ∈ H, y * (y * x * y⁻¹) * y⁻¹ = x := by
    intro x hx
    let xH : ↥H := ⟨x, hx⟩
    have hx' : y * x * y⁻¹ ∈ H := hymem xH
    let x'H : ↥H := ⟨y * x * y⁻¹, hx'⟩
    have h1 : sx x'H = α (sx xH) := (hsx_act xH).symm
    have h2 : α (sx x'H) = sx ⟨y * (x'H : G) * y⁻¹, hymem x'H⟩ := hsx_act x'H
    have h3 : α (sx x'H) = sx xH := by rw [h1]; exact hαsq (sx xH)
    have h4 : sx ⟨y * (x'H : G) * y⁻¹, hymem x'H⟩ = sx xH := by rw [← h2, h3]
    have h5 := hsx_inj h4
    exact congrArg Subtype.val h5
  let β : MulAut ↥H := H.normalizerMonoidHom ⟨y, hyH⟩
  have hβapp : ∀ x : ↥H, ((β x : ↥H) : G) = y * (x : G) * y⁻¹ := by
    intro x
    rfl
  have hβ2 : β ^ 2 = 1 := by
    ext x
    have h := hy2 (x : G) x.2
    simp only [pow_two, MulAut.mul_apply, MulAut.one_apply]
    rw [hβapp]
    rw [hβapp]
    exact h
  have hHcard : Nat.card ↥H = 7 := c.card_R_inf_L i
  have : IsCyclic ↥H := isCyclic_of_prime_card hHcard
  rcases mulAut_eq_id_or_inv_of_sq_one hHcard β hβ2 with h | h
  · left
    intro x hx
    have hx' := congrArg Subtype.val (h ⟨x, hx⟩)
    rw [hβapp] at hx'
    exact hx'
  · right
    intro x hx
    have hx' := congrArg Subtype.val (h ⟨x, hx⟩)
    rw [hβapp] at hx'
    simpa using hx'

theorem rotation_map_conj_eq (c : Ctx147 D L n r p A X B R)
    {φ : ↥D.M →* DihedralGroup 3} (hφ : Function.Surjective φ)
    (hker : φ.ker = (X ⊔ F08.CentOverO2 D.M X).subgroupOf D.M)
    {m : G} (hmM : m ∈ D.M) (hmrot : φ ⟨m, hmM⟩ ^ 3 = 1) :
    (L 0).map (MulAut.conj m).toMonoidHom = L 0 := by
  have _ := hφ
  obtain ⟨-, hne, -⟩ := c.hH
  have hset : ({L 0, L 1} : Set (Subgroup G)) = conjSetOf D.M (L 0) := by
    simpa [conjSetOf] using c.hc.1
  let f : G →* G := (MulAut.conj m).toMonoidHom
  have hm3ker : (⟨m ^ 3, D.M.pow_mem hmM 3⟩ : ↥D.M) ∈ φ.ker := by
    rw [MonoidHom.mem_ker]
    have harg : (⟨m ^ 3, D.M.pow_mem hmM 3⟩ : ↥D.M) = ⟨m, hmM⟩ ^ 3 := Subtype.ext rfl
    rw [harg, map_pow, hmrot]
  have hm3N : m ^ 3 ∈ X ⊔ F08.CentOverO2 D.M X := by
    have hmem := Subgroup.mem_subgroupOf.mp (hker ▸ hm3ker)
    exact hmem
  have hm3L : m ^ 3 ∈ normalizer ((L 0 : Subgroup G) : Set G) :=
    c.kernel_le_normalizer_L 0 hm3N
  have hmap3 : (L 0).map (MulAut.conj (m ^ 3)).toMonoidHom = L 0 :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp hm3L
  have hA : (L 0).map f = L 0 ∨ (L 0).map f = L 1 := by
    have hmem : (L 0).map f ∈ conjSetOf D.M (L 0) := ⟨m, hmM, rfl⟩
    have hmem' : (L 0).map f ∈ ({L 0, L 1} : Set (Subgroup G)) := by rwa [← hset] at hmem
    simpa using hmem'
  have hB : ((L 0).map f).map f = L 0 ∨ ((L 0).map f).map f = L 1 := by
    have hBmap : ((L 0).map f).map f =
        (L 0).map (MulAut.conj (m * m)).toMonoidHom := by
      simp only [f, Subgroup.map_map]
      congr 1
      ext x
      simp [mul_assoc]
    have hmem : ((L 0).map f).map f ∈ conjSetOf D.M (L 0) := by
      rw [hBmap]
      exact ⟨m * m, D.M.mul_mem hmM hmM, rfl⟩
    have hmem' : ((L 0).map f).map f ∈ ({L 0, L 1} : Set (Subgroup G)) := by
      rwa [← hset] at hmem
    simpa using hmem'
  have hC : (((L 0).map f).map f).map f = L 0 := by
    have hiter : (((L 0).map f).map f).map f =
        (L 0).map (MulAut.conj (m ^ 3)).toMonoidHom := by
      simp only [f, Subgroup.map_map]
      congr 1
      ext x
      simp [pow_three, mul_assoc]
    rw [hiter, hmap3]
  rcases hA with hA | hA
  · exact hA
  · rcases hB with hB | hB
    · have hval : (((L 0).map f).map f).map f = L 1 := by rw [hB, hA]
      exact absurd (hC.symm.trans hval) hne
    · have hL1f : (L 1).map f = L 1 := by
        calc (L 1).map f = ((L 0).map f).map f := by rw [← hA]
          _ = L 1 := hB
      have hEq : (L 0).map f = (L 1).map f := by rw [hA, hL1f]
      exact absurd (Subgroup.map_injective (MulAut.conj m).injective hEq) hne

theorem exists_reflection (c : Ctx147 D L n r p A X B R)
    {φ : ↥D.M →* DihedralGroup 3} (hφ : Function.Surjective φ)
    (hker : φ.ker = (X ⊔ F08.CentOverO2 D.M X).subgroupOf D.M) :
    ∃ (t : G) (htM : t ∈ D.M) (i : ZMod 3), t ∈ normalizer (R : Set G) ∧
      (L 0).map (MulAut.conj t).toMonoidHom = L 1 ∧
      φ ⟨t, htM⟩ = DihedralGroup.sr i := by
  obtain ⟨hcal, hne, -⟩ := c.hH
  have hset : ({L 0, L 1} : Set (Subgroup G)) = conjSetOf D.M (L 0) := by
    simpa [conjSetOf] using c.hc.1
  have hL1mem : L 1 ∈ conjSetOf D.M (L 0) := by
    have h : L 1 ∈ ({L 0, L 1} : Set (Subgroup G)) := by simp
    rwa [hset] at h
  obtain ⟨u, huM, huL⟩ := hL1mem
  have huN : u ∈ normalizer (X : Set G) := c.M_le_normalizer_X huM
  have hnotrot : φ ⟨u, huM⟩ ∉ TauCeti.dihedralRotations 3 := by
    intro hmem
    have hdvd : orderOf (φ ⟨u, huM⟩) ∣ 3 := by
      have h := Subgroup.orderOf_dvd_natCard (TauCeti.dihedralRotations 3) hmem
      rwa [TauCeti.card_dihedralRotations] at h
    have hcube : φ ⟨u, huM⟩ ^ 3 = 1 := (orderOf_dvd_iff_pow_eq_one).mp hdvd
    have hL0u : (L 0).map (MulAut.conj u).toMonoidHom = L 0 :=
      c.rotation_map_conj_eq hφ hker huM hcube
    have hL1L0 : L 1 = L 0 := huL.trans hL0u
    exact hne hL1L0.symm
  obtain ⟨i, hi⟩ : ∃ i : ZMod 3, φ ⟨u, huM⟩ = DihedralGroup.sr i := by
    rcases hd : φ ⟨u, huM⟩ with j | j
    · exact absurd (by rw [hd]; exact TauCeti.r_mem_dihedralRotations j) hnotrot
    · exact ⟨j, rfl⟩
  have : Fact (Nat.Prime 7) := ⟨Nat.prime_seven⟩
  have hPc : Nat.card R = 7 ^ (Nat.card X).factorization 7 := by
    have hr : r = 7 := c.r_eq
    have : Fact r.Prime := ⟨c.hH.2.2.2.1⟩
    have h := c.hR.card_eq
    rwa [hr] at h
  obtain ⟨ℓ, hℓX, htN⟩ :=
    CFSG.Walter.W67.Sec6.exists_mul_mem_normalizer_of_sylowIn (r := 7)
      (L := X) (P := R) c.hR.le hPc huN
  have hℓM : ℓ ∈ D.M := c.X_le_M hℓX
  let t : G := ℓ * u
  have htM : t ∈ D.M := D.M.mul_mem hℓM huM
  have htφ : φ ⟨t, htM⟩ = DihedralGroup.sr i := by
    have hℓker : (⟨ℓ, hℓM⟩ : ↥D.M) ∈ φ.ker := by
      rw [hker]
      exact Subgroup.mem_subgroupOf.mpr (Subgroup.mem_sup_left hℓX)
    have hℓφ : φ ⟨ℓ, hℓM⟩ = 1 := MonoidHom.mem_ker.mp hℓker
    have harg : (⟨t, htM⟩ : ↥D.M) = ⟨ℓ, hℓM⟩ * ⟨u, huM⟩ := Subtype.ext rfl
    rw [harg, map_mul, hℓφ, one_mul, hi]
  have htL : (L 0).map (MulAut.conj t).toMonoidHom = L 1 := by
    have hℓL1 : (L 1).map (MulAut.conj ℓ).toMonoidHom = L 1 :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (c.X_le_normalizer_L 1 hℓX)
    have hcomp : (MulAut.conj t).toMonoidHom =
        (MulAut.conj ℓ).toMonoidHom.comp (MulAut.conj u).toMonoidHom := by
      ext x
      simp [t, MulAut.conj_apply, mul_assoc]
    rw [hcomp, ← Subgroup.map_map, ← huL, hℓL1]
  exact ⟨t, htM, i, htN, htL, htφ⟩

omit [Finite G] in
theorem le_of_inf_ne_bot_of_prime_card {H K : Subgroup G} {p : ℕ} (hp : p.Prime)
    (hcard : Nat.card H = p) (hne : H ⊓ K ≠ ⊥) : H ≤ K := by
  have : Fact (Nat.card ↥H).Prime := ⟨by rw [hcard]; exact hp⟩
  have htop : (H ⊓ K).subgroupOf H = ⊤ := by
    rcases Subgroup.eq_bot_or_eq_top_of_prime_card (G := ↥H) ((H ⊓ K).subgroupOf H) with h | h
    · exfalso
      apply hne
      rw [eq_bot_iff]
      intro x hx
      have hx' : (⟨x, hx.1⟩ : ↥H) ∈ (H ⊓ K).subgroupOf H := Subgroup.mem_subgroupOf.mpr hx
      rw [h] at hx'
      have hx1 : (⟨x, hx.1⟩ : ↥H) = 1 := Subgroup.mem_bot.mp hx'
      exact Subgroup.mem_bot.mpr (congrArg Subtype.val hx1)
    · exact h
  intro x hx
  have hx' : (⟨x, hx⟩ : ↥H) ∈ (H ⊓ K).subgroupOf H := by rw [htop]; exact Subgroup.mem_top _
  exact (Subgroup.mem_subgroupOf.mp hx').2

omit [Finite G] in
theorem orderOf_eq_seven_of_mem_of_ne_one {H : Subgroup G} (hcard : Nat.card H = 7) {x : G}
    (hx : x ∈ H) (hx1 : x ≠ 1) : orderOf x = 7 := by
  have hdvd : orderOf x ∣ Nat.card H := Subgroup.orderOf_dvd_natCard H hx
  rw [hcard] at hdvd
  rcases (Nat.dvd_prime Nat.prime_seven).mp hdvd with h | h
  · exact absurd (orderOf_eq_one_iff.mp h) hx1
  · exact h

omit [Finite G] in
theorem not_dvd_sub_one_of_intCast_ne_one {k : ℤ} (hk : (k : ZMod 7) ≠ 1) :
    ¬ (7 : ℤ) ∣ k - 1 := by
  intro hd
  apply hk
  have hzero : ((k - 1 : ℤ) : ZMod 7) = 0 := by
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact hd
  have h : (k : ZMod 7) - 1 = 0 := by simpa using hzero
  exact sub_eq_zero.mp h

omit [Finite G] in
theorem not_dvd_one_sub_of_intCast_ne_one {k : ℤ} (hk : (k : ZMod 7) ≠ 1) :
    ¬ (7 : ℤ) ∣ 1 - k := by
  intro hd
  apply hk
  have hzero : ((1 - k : ℤ) : ZMod 7) = 0 := by
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact hd
  have h : (1 : ZMod 7) - k = 0 := by simpa using hzero
  exact (sub_eq_zero.mp h).symm

omit [Finite G] in
theorem not_dvd_sub_of_intCast_ne {a b : ℤ} (h : (a : ZMod 7) ≠ b) :
    ¬ (7 : ℤ) ∣ a - b := by
  intro hd
  apply h
  have hzero : ((a - b : ℤ) : ZMod 7) = 0 := by
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact hd
  have h' : (a : ZMod 7) - b = 0 := by simpa using hzero
  exact sub_eq_zero.mp h'

omit [Finite G] in
theorem eq_one_of_zpow_eq_one_of_not_dvd {H : Subgroup G} (hcard : Nat.card H = 7) {x : G}
    (hx : x ∈ H) {m : ℤ} (hm : ¬ (7 : ℤ) ∣ m) (hpow : x ^ m = 1) : x = 1 := by
  by_contra hx1
  have hdvd : (7 : ℤ) ∣ m := by
    have h := (orderOf_dvd_iff_zpow_eq_one (x := x)).mpr hpow
    rwa [orderOf_eq_seven_of_mem_of_ne_one hcard hx hx1] at h
  exact hm hdvd

omit [Finite G] in
theorem zpow_sub_one_eq_one_of_mem_sup_of_conj_eq_self {R₀ R₁ : Subgroup G} {b : G}
    {k₀ k₁ : ℤ} (hbot : R₀ ⊓ R₁ = ⊥)
    (hb₀ : ∀ x ∈ R₀, b * x * b⁻¹ = x ^ k₀)
    (hb₁ : ∀ x ∈ R₁, b * x * b⁻¹ = x ^ k₁)
    {x₀ x₁ : G} (hx₀ : x₀ ∈ R₀) (hx₁ : x₁ ∈ R₁)
    (hfix : b * (x₀ * x₁) * b⁻¹ = x₀ * x₁) :
    x₀ ^ (k₀ - 1) = 1 ∧ x₁ ^ (1 - k₁) = 1 := by
  have hconj : b * (x₀ * x₁) * b⁻¹ = x₀ ^ k₀ * x₁ ^ k₁ := by
    rw [← conj_mul, hb₀ x₀ hx₀, hb₁ x₁ hx₁]
  rw [hconj] at hfix
  have h1 : x₀⁻¹ * x₀ ^ k₀ = x₀ ^ (k₀ - 1) := by
    rw [← zpow_neg_one, ← zpow_add]
    congr 1
    ring
  have h2 : x₁ * (x₁ ^ k₁)⁻¹ = x₁ ^ (1 - k₁) := by
    simpa using (zpow_sub x₁ 1 k₁).symm
  have hkey : x₀ ^ (k₀ - 1) = x₁ ^ (1 - k₁) := by
    have hstep : x₀ ^ (k₀ - 1) * x₁ ^ k₁ = x₁ := by
      have h := congrArg (fun z => x₀⁻¹ * z) hfix
      calc x₀ ^ (k₀ - 1) * x₁ ^ k₁ = (x₀⁻¹ * x₀ ^ k₀) * x₁ ^ k₁ := by rw [h1]
        _ = x₀⁻¹ * (x₀ ^ k₀ * x₁ ^ k₁) := by rw [mul_assoc]
        _ = x₀⁻¹ * (x₀ * x₁) := h
        _ = x₁ := by group
    calc x₀ ^ (k₀ - 1) = x₀ ^ (k₀ - 1) * x₁ ^ k₁ * (x₁ ^ k₁)⁻¹ := by group
      _ = x₁ * (x₁ ^ k₁)⁻¹ := by rw [hstep]
      _ = x₁ ^ (1 - k₁) := h2
  have hmem : x₀ ^ (k₀ - 1) ∈ R₀ ⊓ R₁ := by
    refine ⟨R₀.zpow_mem hx₀ _, ?_⟩
    rw [hkey]
    exact R₁.zpow_mem hx₁ _
  have h₀ : x₀ ^ (k₀ - 1) = 1 := by
    rw [hbot, Subgroup.mem_bot] at hmem
    exact hmem
  exact ⟨h₀, by rw [← hkey, h₀]⟩

omit [Finite G] in
theorem eq_one_of_mem_sup_of_conj_eq_self {R₀ R₁ : Subgroup G} {b : G} {k₀ k₁ : ℤ}
    (hcard₀ : Nat.card R₀ = 7) (hcard₁ : Nat.card R₁ = 7)
    (hcomm : ∀ x ∈ R₀, ∀ y ∈ R₁, x * y = y * x) (hbot : R₀ ⊓ R₁ = ⊥)
    (hb₀ : ∀ x ∈ R₀, b * x * b⁻¹ = x ^ k₀)
    (hb₁ : ∀ x ∈ R₁, b * x * b⁻¹ = x ^ k₁)
    (hk₀ : (k₀ : ZMod 7) ≠ 1) (hk₁ : (k₁ : ZMod 7) ≠ 1) :
    ∀ x ∈ R₀ ⊔ R₁, b * x * b⁻¹ = x → x = 1 := by
  have hle : R₀ ≤ normalizer (R₁ : Set G) := by
    rw [Subgroup.le_set_normalizer_iff]
    intro x hx y hy
    rw [hcomm x hx y hy, mul_assoc, mul_inv_cancel, mul_one]
    exact hy
  intro x hx hfix
  have hxmul : x ∈ (R₀ : Set G) * (R₁ : Set G) := by
    rw [← Subgroup.coe_mul_of_left_le_normalizer_right R₀ R₁ hle]
    exact hx
  obtain ⟨x₀, hx₀, x₁, hx₁, rfl⟩ := Set.mem_mul.mp hxmul
  obtain ⟨hpow₀, hpow₁⟩ :=
    zpow_sub_one_eq_one_of_mem_sup_of_conj_eq_self hbot hb₀ hb₁ hx₀ hx₁ hfix
  have hx₀1 : x₀ = 1 :=
    eq_one_of_zpow_eq_one_of_not_dvd hcard₀ hx₀ (not_dvd_sub_one_of_intCast_ne_one hk₀) hpow₀
  have hx₁1 : x₁ = 1 :=
    eq_one_of_zpow_eq_one_of_not_dvd hcard₁ hx₁ (not_dvd_one_sub_of_intCast_ne_one hk₁) hpow₁
  rw [hx₀1, hx₁1, mul_one]

omit [Finite G] in
theorem mul_conj_mul_zpow_eq {b y₀ y₁ : G} {k₀ k₁ : ℤ} (hcomm : Commute y₀ y₁)
    (hby : b * (y₀ * y₁) * b⁻¹ = y₀ ^ k₀ * y₁ ^ k₁) :
    (b * (y₀ * y₁) * b⁻¹) * (y₀ * y₁) ^ (-k₁) = y₀ ^ (k₀ - k₁) := by
  rw [hby, hcomm.mul_zpow]
  have h₀ : y₀ ^ k₀ * y₀ ^ (-k₁) = y₀ ^ (k₀ - k₁) := by
    rw [← zpow_add, show k₀ + -k₁ = k₀ - k₁ by ring]
  have h₁ : y₁ ^ k₁ * y₁ ^ (-k₁) = 1 := by
    rw [← zpow_add, show k₁ + -k₁ = 0 by ring, zpow_zero]
  calc (y₀ ^ k₀ * y₁ ^ k₁) * (y₀ ^ (-k₁) * y₁ ^ (-k₁))
      = y₀ ^ k₀ * (y₁ ^ k₁ * y₀ ^ (-k₁)) * y₁ ^ (-k₁) := by group
    _ = y₀ ^ k₀ * (y₀ ^ (-k₁) * y₁ ^ k₁) * y₁ ^ (-k₁) := by
          rw [(hcomm.symm.zpow_zpow k₁ (-k₁)).eq]
    _ = (y₀ ^ k₀ * y₀ ^ (-k₁)) * (y₁ ^ k₁ * y₁ ^ (-k₁)) := by group
    _ = y₀ ^ (k₀ - k₁) * 1 := by rw [h₀, h₁]
    _ = y₀ ^ (k₀ - k₁) := mul_one _

omit [Finite G] in
theorem le_left_or_le_right_of_normalizer {R₀ R₁ : Subgroup G} {b : G} {k₀ k₁ : ℤ}
    (hcard₀ : Nat.card R₀ = 7) (hcard₁ : Nat.card R₁ = 7)
    (hcomm : ∀ x ∈ R₀, ∀ y ∈ R₁, x * y = y * x)
    (hb₀ : ∀ x ∈ R₀, b * x * b⁻¹ = x ^ k₀)
    (hb₁ : ∀ x ∈ R₁, b * x * b⁻¹ = x ^ k₁)
    (hk : (k₀ : ZMod 7) ≠ k₁) :
    ∀ Y : Subgroup G, Y ≤ R₀ ⊔ R₁ → b ∈ normalizer (Y : Set G) → Y ≠ ⊥ →
      R₀ ≤ Y ∨ R₁ ≤ Y := by
  have hle : R₀ ≤ normalizer (R₁ : Set G) := by
    rw [Subgroup.le_set_normalizer_iff]
    intro x hx y hy
    rw [hcomm x hx y hy, mul_assoc, mul_inv_cancel, mul_one]
    exact hy
  intro Y hYR hbN hYne
  obtain ⟨yH, hyH1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hYne
  have hyY : (yH : G) ∈ Y := yH.2
  have hy1 : (yH : G) ≠ 1 := fun h => hyH1 (Subtype.ext h)
  have hyR : (yH : G) ∈ (R₀ : Set G) * (R₁ : Set G) := by
    rw [← Subgroup.coe_mul_of_left_le_normalizer_right R₀ R₁ hle]
    exact hYR hyY
  obtain ⟨y₀, hy₀, y₁, hy₁, hy_eq⟩ := Set.mem_mul.mp hyR
  have hcomm01 : Commute y₀ y₁ := hcomm y₀ hy₀ y₁ hy₁
  have hby : b * (y₀ * y₁) * b⁻¹ = y₀ ^ k₀ * y₁ ^ k₁ := by
    rw [← conj_mul, hb₀ y₀ hy₀, hb₁ y₁ hy₁]
  have hbyY : b * (yH : G) * b⁻¹ ∈ Y :=
    (Subgroup.mem_normalizer_iff.mp hbN (yH : G)).mp hyY
  have hzY : (b * (yH : G) * b⁻¹) * (yH : G) ^ (-k₁) ∈ Y :=
    Y.mul_mem hbyY (Y.zpow_mem hyY _)
  have hz : (b * (yH : G) * b⁻¹) * (yH : G) ^ (-k₁) = y₀ ^ (k₀ - k₁) := by
    rw [← hy_eq]
    exact mul_conj_mul_zpow_eq hcomm01 hby
  have hy₀powY : y₀ ^ (k₀ - k₁) ∈ Y := hz ▸ hzY
  by_cases hy₀1 : y₀ = 1
  · right
    have hyR1 : (yH : G) ∈ R₁ := by
      rw [← hy_eq, hy₀1, one_mul]
      exact hy₁
    have hne : R₁ ⊓ Y ≠ ⊥ := by
      intro hbot
      have hmem : (yH : G) ∈ R₁ ⊓ Y := ⟨hyR1, hyY⟩
      rw [hbot, Subgroup.mem_bot] at hmem
      exact hy1 hmem
    exact le_of_inf_ne_bot_of_prime_card Nat.prime_seven hcard₁ hne
  · left
    have hpowne : y₀ ^ (k₀ - k₁) ≠ 1 := by
      intro h
      exact hy₀1 <| eq_one_of_zpow_eq_one_of_not_dvd hcard₀ hy₀
        (not_dvd_sub_of_intCast_ne hk) h
    have hne : R₀ ⊓ Y ≠ ⊥ := by
      intro hbot
      have hmem : y₀ ^ (k₀ - k₁) ∈ R₀ ⊓ Y := ⟨R₀.zpow_mem hy₀ _, hy₀powY⟩
      rw [hbot, Subgroup.mem_bot] at hmem
      exact hpowne hmem
    exact le_of_inf_ne_bot_of_prime_card Nat.prime_seven hcard₀ hne

theorem exists_zpow_action_on_R_inf_L (c : Ctx147 D L n r p A X B R) (i : Fin 2) {b : G}
    (hb : b ∈ B) :
    ∃ k : ℤ, (∀ x ∈ R ⊓ L i, b * x * b⁻¹ = x ^ k) ∧
      (b ^ 3 = 1 → (k : ZMod 7) ^ 3 = 1) := by
  let H : Subgroup G := R ⊓ L i
  have hbN : b ∈ normalizer (H : Set G) := c.B_le_normalizer_R_inf_L i hb
  let β : MulAut ↥H := H.normalizerMonoidHom ⟨b, hbN⟩
  have hcard : Nat.card ↥H = 7 := by simpa [H] using c.card_R_inf_L i
  have hcyc : IsCyclic ↥H := isCyclic_of_prime_card (p := 7) (hp := ⟨Nat.prime_seven⟩) hcard
  obtain ⟨k, hk⟩ := MonoidHom.map_cyclic β.toMonoidHom
  have hact : ∀ x ∈ H, b * x * b⁻¹ = x ^ k := by
    intro x hx
    have h := congrArg Subtype.val (hk ⟨x, hx⟩)
    simpa [β] using h
  refine ⟨k, fun x hx => hact x (by simpa [H] using hx), ?_⟩
  intro hb3
  obtain ⟨s, hs_ord⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := ↥H)
  have hsord : orderOf s = 7 := by rw [hs_ord, hcard]
  have h1 : b * (s : G) * b⁻¹ = (s : G) ^ k := hact (s : G) s.2
  have h2 : b * (s : G) ^ k * b⁻¹ = ((s : G) ^ k) ^ k :=
    hact _ (H.zpow_mem s.2 k)
  have h3 : b * ((s : G) ^ k) ^ k * b⁻¹ = (((s : G) ^ k) ^ k) ^ k :=
    hact _ (H.zpow_mem (H.zpow_mem s.2 k) k)
  have hiter : b ^ 3 * (s : G) * (b ^ 3)⁻¹ = (((s : G) ^ k) ^ k) ^ k := by
    calc b ^ 3 * (s : G) * (b ^ 3)⁻¹
        = (b * b * b) * (s : G) * (b * b * b)⁻¹ := by
          rw [pow_three']
      _ = b * (b * (b * (s : G) * b⁻¹) * b⁻¹) * b⁻¹ := by group
      _ = b * (b * ((s : G) ^ k) * b⁻¹) * b⁻¹ := by rw [h1]
      _ = b * (((s : G) ^ k) ^ k) * b⁻¹ := by rw [h2]
      _ = (((s : G) ^ k) ^ k) ^ k := by rw [h3]
  have hzpow : (((s : G) ^ k) ^ k) ^ k = (s : G) ^ (k ^ 3) := by
    have h12 : ((s : G) ^ k) ^ k = (s : G) ^ (k * k) := (zpow_mul (s : G) k k).symm
    have h23 : ((s : G) ^ (k * k)) ^ k = (s : G) ^ (k * k * k) :=
      (zpow_mul (s : G) (k * k) k).symm
    rw [h12, h23]
    congr 1
    ring
  have hse : (s : G) ^ (k ^ 3) = (s : G) := by
    rw [← hzpow, ← hiter, hb3]
    group
  have hmod : k ^ 3 ≡ 1 [ZMOD 7] := by
    have h := (zpow_eq_zpow_iff_modEq (x := (s : G)) (m := k ^ 3) (n := 1)).mp
      (by simpa using hse)
    rwa [Subgroup.orderOf_coe, hsord] at h
  have hz : ((k ^ 3 : ℤ) : ZMod 7) = 1 := (ZMod.intCast_eq_intCast_iff _ _ _).mpr hmod
  simpa using hz

omit [Finite G] in
theorem kernel_element_action {b t : G} {k₀ k₁ : ℤ}
    (hb₀ : ∀ x ∈ R ⊓ L 0, b * x * b⁻¹ = x ^ k₀)
    (hb₁ : ∀ x ∈ R ⊓ L 1, b * x * b⁻¹ = x ^ k₁)
    (htL : (L 0).map (MulAut.conj t).toMonoidHom = L 1)
    (htN : t ∈ normalizer (R : Set G)) {s : G} (hs : s ∈ R ⊓ L 1) :
    (t * b * t⁻¹ * b) * s * (t * b * t⁻¹ * b)⁻¹ = s ^ (k₀ * k₁) := by
  have hsmap : s ∈ (L 0).map (MulAut.conj t).toMonoidHom := by rw [htL]; exact hs.2
  obtain ⟨s', hs'L0, hs'eq⟩ := Subgroup.mem_map.mp hsmap
  have hseq : t * s' * t⁻¹ = s := hs'eq
  have hseq' : t⁻¹ * s * t = s' := by rw [← hseq]; group
  have htinvN : t⁻¹ ∈ normalizer (R : Set G) := (normalizer (R : Set G)).inv_mem htN
  have hs'R : s' ∈ R := by
    rw [← hseq']
    simpa using (Subgroup.mem_normalizer_iff.mp htinvN s).mp hs.1
  have hs' : s' ∈ R ⊓ L 0 := ⟨hs'R, hs'L0⟩
  have hconj : t⁻¹ * s ^ k₁ * t = (s') ^ k₁ := by
    rw [← hseq, conj_zpow]
    group
  calc (t * b * t⁻¹ * b) * s * (t * b * t⁻¹ * b)⁻¹
      = (t * b * t⁻¹) * (b * s * b⁻¹) * (t * b * t⁻¹)⁻¹ := by group
    _ = (t * b * t⁻¹) * s ^ k₁ * (t * b * t⁻¹)⁻¹ := by rw [hb₁ s hs]
    _ = t * (b * (t⁻¹ * s ^ k₁ * t) * b⁻¹) * t⁻¹ := by group
    _ = t * (b * (s') ^ k₁ * b⁻¹) * t⁻¹ := by rw [hconj]
    _ = t * ((s') ^ k₁) ^ k₀ * t⁻¹ := by rw [hb₀ _ ((R ⊓ L 0).zpow_mem hs' k₁)]
    _ = t * (s') ^ (k₁ * k₀) * t⁻¹ := by rw [← zpow_mul]
    _ = t * (s') ^ (k₀ * k₁) * t⁻¹ := by rw [Int.mul_comm k₁ k₀]
    _ = (t * s' * t⁻¹) ^ (k₀ * k₁) := (conj_zpow).symm
    _ = s ^ (k₀ * k₁) := by rw [hseq]

theorem exists_kernel_element (c : Ctx147 D L n r p A X B R) {b : G} (hb : b ∈ B)
    (hb3 : b ^ 3 = 1) :
    ∃ (t y : G), t ∈ normalizer (R : Set G) ∧
      (L 0).map (MulAut.conj t).toMonoidHom = L 1 ∧ y = t * b * t⁻¹ * b ∧
      y ∈ X ⊔ F08.CentOverO2 D.M X ∧ y ∈ normalizer (R : Set G) := by
  obtain ⟨φ, hφ, hker⟩ := c.hc.2.2.2.2
  obtain ⟨t, htM, i, htN, htL, htφ⟩ := c.exists_reflection hφ hker
  have hbM : b ∈ D.M := c.hB hb
  have hφb3 : φ ⟨b, hbM⟩ ^ 3 = 1 := by
    rw [← map_pow]
    have h : (⟨b, hbM⟩ : ↥D.M) ^ 3 = 1 := by
      ext
      simpa using hb3
    rw [h, map_one]
  obtain ⟨j, hj⟩ : ∃ j : ZMod 3, φ ⟨b, hbM⟩ = DihedralGroup.r j := by
    rcases hd : φ ⟨b, hbM⟩ with j | j
    · exact ⟨j, rfl⟩
    · exfalso
      have h1 : DihedralGroup.sr j ^ 3 = 1 := by rw [← hd]; exact hφb3
      rw [pow_three, DihedralGroup.sr_mul_self, mul_one] at h1
      have hne : DihedralGroup.sr j ≠ 1 := by
        intro h0
        have h2 := DihedralGroup.orderOf_sr j
        rw [h0, orderOf_one] at h2
        norm_num at h2
      exact hne h1
  have hdihedral : DihedralGroup.sr i * DihedralGroup.r j * (DihedralGroup.sr i)⁻¹ *
      DihedralGroup.r j = 1 := by
    rw [DihedralGroup.inv_sr, DihedralGroup.sr_mul_r, DihedralGroup.sr_mul_sr,
      DihedralGroup.r_mul_r]
    change DihedralGroup.r (i - (i + j) + j) = DihedralGroup.r 0
    rw [DihedralGroup.r.injEq]
    ring
  let y : G := t * b * t⁻¹ * b
  have hyM : y ∈ D.M := by
    apply D.M.mul_mem
    · apply D.M.mul_mem
      · exact D.M.mul_mem htM hbM
      · exact D.M.inv_mem htM
    · exact hbM
  have hbN : b ∈ normalizer (R : Set G) := c.B_le_normalizer_R hb
  have hyN : y ∈ normalizer (R : Set G) := by
    apply (normalizer (R : Set G)).mul_mem
    · apply (normalizer (R : Set G)).mul_mem
      · exact (normalizer (R : Set G)).mul_mem htN hbN
      · exact (normalizer (R : Set G)).inv_mem htN
    · exact hbN
  have hyφ : φ ⟨y, hyM⟩ = 1 := by
    have harg : (⟨y, hyM⟩ : ↥D.M) = ⟨t, htM⟩ * ⟨b, hbM⟩ * ⟨t, htM⟩⁻¹ * ⟨b, hbM⟩ :=
      Subtype.ext rfl
    rw [harg]
    simpa only [map_mul, map_inv, htφ, hj] using hdihedral
  have hyker : y ∈ X ⊔ F08.CentOverO2 D.M X := by
    have hmem : (⟨y, hyM⟩ : ↥D.M) ∈ φ.ker := MonoidHom.mem_ker.mpr hyφ
    rw [hker] at hmem
    exact Subgroup.mem_subgroupOf.mp hmem
  exact ⟨t, y, htN, htL, rfl, hyker, hyN⟩

theorem mul_exponents_eq_one (c : Ctx147 D L n r p A X B R) {b : G} (hb : b ∈ B)
    (hb3 : b ^ 3 = 1) {k₀ k₁ : ℤ}
    (hb₀ : ∀ x ∈ R ⊓ L 0, b * x * b⁻¹ = x ^ k₀)
    (hb₁ : ∀ x ∈ R ⊓ L 1, b * x * b⁻¹ = x ^ k₁)
    (hk₀c : (k₀ : ZMod 7) ^ 3 = 1) (hk₁c : (k₁ : ZMod 7) ^ 3 = 1) :
    ((k₀ * k₁ : ℤ) : ZMod 7) = 1 := by
  obtain ⟨t, y, htN, htL, hy_eq, hyker, hyN⟩ := c.exists_kernel_element hb hb3
  have hcyc : IsCyclic ↥(R ⊓ L 1) :=
    isCyclic_of_prime_card (p := 7) (hp := ⟨Nat.prime_seven⟩) (c.card_R_inf_L 1)
  obtain ⟨s, hs_ord⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := ↥(R ⊓ L 1))
  have hcard : Nat.card ↥(R ⊓ L 1) = 7 := c.card_R_inf_L 1
  have hsord : orderOf s = 7 := by rw [hs_ord, hcard]
  have hs : (s : G) ∈ R ⊓ L 1 := s.2
  have hyact : y * (s : G) * y⁻¹ = (s : G) ^ (k₀ * k₁) := by
    rw [hy_eq]
    exact kernel_element_action hb₀ hb₁ htL htN hs
  have hcube : ((k₀ * k₁ : ℤ) : ZMod 7) ^ 3 = 1 := by
    rw [Int.cast_mul, mul_pow, hk₀c, hk₁c, one_mul]
  rcases c.kernel_acts_pm_one 1 hyker hyN with hact | hact
  · have hse : (s : G) ^ (k₀ * k₁) = (s : G) := by
      rw [← hyact]; exact hact (s : G) hs
    have hmod : k₀ * k₁ ≡ 1 [ZMOD 7] := by
      have h := (zpow_eq_zpow_iff_modEq (x := (s : G)) (m := k₀ * k₁) (n := 1)).mp
        (by simpa using hse)
      rwa [Subgroup.orderOf_coe, hsord] at h
    exact (ZMod.intCast_eq_intCast_iff _ _ _).mpr hmod
  · have hse : (s : G) ^ (k₀ * k₁) = (s : G) ^ (-1 : ℤ) := by
      rw [← hyact]
      rw [hact (s : G) hs, zpow_neg_one]
    have hmod : k₀ * k₁ ≡ -1 [ZMOD 7] := by
      have h := (zpow_eq_zpow_iff_modEq (x := (s : G)) (m := k₀ * k₁) (n := -1)).mp hse
      rwa [Subgroup.orderOf_coe, hsord] at h
    have hneg : ((k₀ * k₁ : ℤ) : ZMod 7) = -1 :=
      (ZMod.intCast_eq_intCast_iff _ _ _).mpr hmod
    have key : ∀ u : ZMod 7, u ^ 3 = 1 → (u = 1 ∨ u = -1) → u = 1 := by decide
    exact key _ hcube (Or.inr hneg)

theorem centralizer_R_of_actions (c : Ctx147 D L n r p A X B R) {b : G}
    (hB_eq : B = Subgroup.zpowers b) {k₀ k₁ : ℤ}
    (hb₀ : ∀ x ∈ R ⊓ L 0, b * x * b⁻¹ = x ^ k₀)
    (hb₁ : ∀ x ∈ R ⊓ L 1, b * x * b⁻¹ = x ^ k₁)
    (hk₀ : (k₀ : ZMod 7) = 1) (hk₁ : (k₁ : ZMod 7) = 1) :
    R ≤ Subgroup.centralizer (B : Set G) := by
  have hle : R ⊓ L 0 ≤ normalizer ((R ⊓ L 1 : Subgroup G) : Set G) := by
    rw [Subgroup.le_set_normalizer_iff]
    intro x hx y hy
    rw [c.commute_R_inf_L x hx y hy, mul_assoc, mul_inv_cancel, mul_one]
    exact hy
  have hfix : ∀ x ∈ R, b * x * b⁻¹ = x := by
    intro x hx
    have hxmul : x ∈ ((R ⊓ L 0 : Subgroup G) : Set G) *
        ((R ⊓ L 1 : Subgroup G) : Set G) := by
      rw [← Subgroup.coe_mul_of_left_le_normalizer_right (R ⊓ L 0) (R ⊓ L 1) hle]
      rw [← c.R_eq_sup]
      exact hx
    obtain ⟨x₀, hx₀, x₁, hx₁, hx_eq⟩ := Set.mem_mul.mp hxmul
    have hfix₀ : b * x₀ * b⁻¹ = x₀ := by
      rw [hb₀ x₀ hx₀]
      have hmod : k₀ ≡ 1 [ZMOD 7] := (ZMod.intCast_eq_intCast_iff k₀ 1 7).mp hk₀
      have hord : orderOf x₀ ∣ 7 := by
        have h := Subgroup.orderOf_dvd_natCard (R ⊓ L 0) hx₀
        rwa [c.card_R_inf_L 0] at h
      have hordZ : ((orderOf x₀ : ℕ) : ℤ) ∣ (7 : ℤ) := by exact_mod_cast hord
      have hmod' : k₀ ≡ 1 [ZMOD orderOf x₀] := Int.ModEq.of_dvd hordZ hmod
      simpa using (zpow_eq_zpow_iff_modEq (x := x₀) (m := k₀) (n := 1)).mpr hmod'
    have hfix₁ : b * x₁ * b⁻¹ = x₁ := by
      rw [hb₁ x₁ hx₁]
      have hmod : k₁ ≡ 1 [ZMOD 7] := (ZMod.intCast_eq_intCast_iff k₁ 1 7).mp hk₁
      have hord : orderOf x₁ ∣ 7 := by
        have h := Subgroup.orderOf_dvd_natCard (R ⊓ L 1) hx₁
        rwa [c.card_R_inf_L 1] at h
      have hordZ : ((orderOf x₁ : ℕ) : ℤ) ∣ (7 : ℤ) := by exact_mod_cast hord
      have hmod' : k₁ ≡ 1 [ZMOD orderOf x₁] := Int.ModEq.of_dvd hordZ hmod
      simpa using (zpow_eq_zpow_iff_modEq (x := x₁) (m := k₁) (n := 1)).mpr hmod'
    rw [← hx_eq, ← conj_mul, hfix₀, hfix₁]
  intro x hx
  rw [Subgroup.mem_centralizer_iff]
  intro b' hb'
  rw [hB_eq] at hb'
  obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb'
  have hcomm : Commute b x := by
    rw [commute_iff_eq]
    exact mul_inv_eq_iff_eq_mul.mp (hfix x hx)
  exact (hcomm.zpow_left m).eq

theorem exponents_ne_one (c : Ctx147 D L n r p A X B R) {b : G}
    (hB_eq : B = Subgroup.zpowers b) {k₀ k₁ : ℤ}
    (hb₀ : ∀ x ∈ R ⊓ L 0, b * x * b⁻¹ = x ^ k₀)
    (hb₁ : ∀ x ∈ R ⊓ L 1, b * x * b⁻¹ = x ^ k₁)
    (hk₀c : (k₀ : ZMod 7) ^ 3 = 1)
    (hprod : ((k₀ * k₁ : ℤ) : ZMod 7) = 1) :
    (k₀ : ZMod 7) ≠ 1 ∧ (k₁ : ZMod 7) ≠ 1 ∧ (k₀ : ZMod 7) ≠ k₁ := by
  have hk₀ne : (k₀ : ZMod 7) ≠ 1 := by
    intro hk₀
    have hk₁ : (k₁ : ZMod 7) = 1 := by
      have h := hprod
      rw [Int.cast_mul, hk₀, one_mul] at h
      exact h
    have hcent := c.centralizer_R_of_actions hB_eq hb₀ hb₁ hk₀ hk₁
    have hcomm : ⁅R, B⁆ = ⊥ := by
      rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
      exact hcent
    have hRbot : R = ⊥ := by rw [← c.hRB, hcomm]
    have hcard : Nat.card R = 1 := by rw [hRbot]; exact Subgroup.card_bot
    have h49 : Nat.card R = 49 := c.card_R
    omega
  have hk₁ne : (k₁ : ZMod 7) ≠ 1 := by
    intro hk₁
    apply hk₀ne
    have h := hprod
    rw [Int.cast_mul, hk₁, mul_one] at h
    exact h
  refine ⟨hk₀ne, hk₁ne, ?_⟩
  intro h
  apply hk₀ne
  have hsq : (k₀ : ZMod 7) ^ 2 = 1 := by
    have h' := hprod
    rw [Int.cast_mul, ← h, ← pow_two] at h'
    exact h'
  have key : ∀ u : ZMod 7, u ^ 3 = 1 → u ^ 2 = 1 → u = 1 := by decide
  exact key _ hk₀c hsq

theorem frame (c : Ctx147 D L n r p A X B R) :
    IsElemAbelian 7 R ∧ Nat.card R = 49 ∧
      (∀ i, Nat.card ↥(R ⊓ L i) = 7 ∧ B ≤ normalizer ((R ⊓ L i : Subgroup G) : Set G)) ∧
      B ≤ normalizer (R : Set G) ∧ R ⊓ centralizer (B : Set G) = ⊥ ∧
      ∀ Y : Subgroup G, Y ≤ R → B ≤ normalizer (Y : Set G) → Y ≠ ⊥ →
        R ⊓ L 0 ≤ Y ∨ R ⊓ L 1 ≤ Y := by
  obtain ⟨b, hb, hb1, hB_eq⟩ := c.exists_generator_B
  have hb3 : b ^ 3 = 1 := by
    have h := pow_card_eq_one' (G := ↥B) (x := ⟨b, hb⟩)
    rw [c.card_B] at h
    simpa using congrArg Subtype.val h
  obtain ⟨k₀, hb₀, hk₀c'⟩ := c.exists_zpow_action_on_R_inf_L 0 hb
  obtain ⟨k₁, hb₁, hk₁c'⟩ := c.exists_zpow_action_on_R_inf_L 1 hb
  have hk₀c : (k₀ : ZMod 7) ^ 3 = 1 := hk₀c' hb3
  have hk₁c : (k₁ : ZMod 7) ^ 3 = 1 := hk₁c' hb3
  have hprod : ((k₀ * k₁ : ℤ) : ZMod 7) = 1 :=
    c.mul_exponents_eq_one hb hb3 hb₀ hb₁ hk₀c hk₁c
  obtain ⟨hk₀, hk₁, hk₀₁⟩ := c.exponents_ne_one hB_eq hb₀ hb₁ hk₀c hprod
  refine ⟨c.isElemAbelian_R, c.card_R, fun i => ⟨c.card_R_inf_L i, c.B_le_normalizer_R_inf_L i⟩,
    c.B_le_normalizer_R, ?_, ?_⟩
  · rw [eq_bot_iff]
    intro x hx
    have hxsup : x ∈ (R ⊓ L 0) ⊔ (R ⊓ L 1) := by
      simpa [← c.R_eq_sup] using hx.1
    have hcomm : b * x * b⁻¹ = x := by
      have hbx : b * x = x * b := Subgroup.mem_centralizer_iff.mp hx.2 b hb
      rw [hbx, mul_assoc, mul_inv_cancel, mul_one]
    have hx1 : x = 1 :=
      eq_one_of_mem_sup_of_conj_eq_self (c.card_R_inf_L 0) (c.card_R_inf_L 1)
        c.commute_R_inf_L c.R_inf_L_inf_bot hb₀ hb₁ hk₀ hk₁ x hxsup hcomm
    rw [hx1, Subgroup.mem_bot]
  · intro Y hYR hBY hYne
    have hYR' : Y ≤ (R ⊓ L 0) ⊔ (R ⊓ L 1) := by
      simpa [← c.R_eq_sup] using hYR
    exact le_left_or_le_right_of_normalizer (c.card_R_inf_L 0) (c.card_R_inf_L 1)
      c.commute_R_inf_L hb₀ hb₁ hk₀₁ Y hYR' (hBY hb) hYne

end Ctx147

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
