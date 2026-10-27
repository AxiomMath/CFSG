module

public import CFSG.Quasithin.Background.F9Tilde
public import CFSG.Quasithin.EmptyFaithful.S153E59A
public import CFSG.Quasithin.EmptyFaithful.S153E59B

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.S1417 CFSG.LieType.BorelTits
open scoped commutatorElement Pointwise

namespace S153E59

section IYU

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ : Subgroup G} {t : G}

abbrev IYU (T Mc M V₁ : Subgroup G) : Subgroup G := Y153 Mc M ⊔ UH153 T M V₁ Mc

theorem U_le_M (cx : Ctx15350 T Mc M V₁ V₂ t) : UH153 T M V₁ Mc ≤ M :=
  (S153E.U_le_T cx).trans (S153E.T_le_M cx)

theorem U_le_normalizer_Y (cx : Ctx15350 T Mc M V₁ V₂ t) :
    UH153 T M V₁ Mc ≤ Subgroup.normalizer (Y153 Mc M : Set G) :=
  (U_le_M cx).trans (le_normalizer_Y153 Mc M)

theorem T_le_normalizer_Y (cx : Ctx15350 T Mc M V₁ V₂ t) :
    T ≤ Subgroup.normalizer (Y153 Mc M : Set G) :=
  (S153E.T_le_M cx).trans (le_normalizer_Y153 Mc M)

theorem IYU_le_M (cx : Ctx15350 T Mc M V₁ V₂ t) : IYU T Mc M V₁ ≤ M :=
  sup_le (Y153_le Mc M) (U_le_M cx)

theorem T_le_normalizer_U (cx : Ctx15350 T Mc M V₁ V₂ t) :
    T ≤ Subgroup.normalizer (UH153 T M V₁ Mc : Set G) :=
  (S153E.T_le_Mc cx).trans (le_normalizer_conjClosure _ _)

theorem T_le_normalizer_IYU (cx : Ctx15350 T Mc M V₁ V₂ t) :
    T ≤ Subgroup.normalizer (IYU T Mc M V₁ : Set G) :=
  B2F.le_normalizer_sup (T_le_normalizer_Y cx) (T_le_normalizer_U cx)

theorem mem_IYU_iff (cx : Ctx15350 T Mc M V₁ V₂ t) {x : G} :
    x ∈ IYU T Mc M V₁ ↔ ∃ u ∈ UH153 T M V₁ Mc, ∃ y ∈ Y153 Mc M, x = u * y := by
  have hmul := Subgroup.coe_mul_of_left_le_normalizer_right (UH153 T M V₁ Mc) (Y153 Mc M)
    (U_le_normalizer_Y cx)
  have : IYU T Mc M V₁ = UH153 T M V₁ Mc ⊔ Y153 Mc M := sup_comm _ _
  rw [this]
  constructor
  · intro hx
    have : x ∈ ((UH153 T M V₁ Mc : Subgroup G) : Set G) * ((Y153 Mc M : Subgroup G) : Set G) := by
      rw [← hmul]; exact hx
    obtain ⟨u, hu, y, hy, rfl⟩ := this
    exact ⟨u, hu, y, hy, rfl⟩
  · rintro ⟨u, hu, y, hy, rfl⟩
    exact Subgroup.mul_mem_sup hu hy

omit [Finite G] in
theorem Y_le_IYU : Y153 Mc M ≤ IYU T Mc M V₁ := le_sup_left

omit [Finite G] in
theorem U_le_IYU : UH153 T M V₁ Mc ≤ IYU T Mc M V₁ := le_sup_right

theorem pCoreOf_Y_le_T (cx : Ctx15350 T Mc M V₁ V₂ t) : pCoreOf 2 (Y153 Mc M) ≤ T := by
  have h1 : pCoreOf 2 (Y153 Mc M) ≤ pCoreOf 2 M :=
    le_pCoreOf_of_le_normalizer 2 ((pCoreOf_le 2 _).trans (Y153_le Mc M))
      ((le_normalizer_Y153 Mc M).trans (normalizer_le_normalizer_pCoreOf 2 _))
      (pCoreOf_isPGroup 2 _)
  exact h1.trans (pCoreOf_two_le_of_isSylowTwoOf cx.c.hyp.isSylowTwoOf)

theorem IYU_inf_Mc_le_T (cx : Ctx15350 T Mc M V₁ V₂ t) {x : G} (hxI : x ∈ IYU T Mc M V₁)
    (hxH : x ∈ Mc) : x ∈ T := by
  obtain ⟨u, hu, y, hy, rfl⟩ := (mem_IYU_iff cx).mp hxI
  have hyH : y ∈ Mc := by
    have := Mc.mul_mem (Mc.inv_mem (U_le_Mc cx hu)) hxH
    simpa using this
  have hyC : y ∈ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) := by
    rw [centralizer_Z_eq cx]; exact hyH
  have hyO : y ∈ pCoreOf 2 (Y153 Mc M) := by
    rw [cx.r49.pCore_eq_centralizer_Z]
    exact ⟨hy, hyC⟩
  exact T.mul_mem (S153E.U_le_T cx hu) (pCoreOf_Y_le_T cx hyO)

end IYU

section CIV

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ : Subgroup G} {t : G}

theorem odd_orderOf_conjAct_Y (h113 : StageLemma14113) (cx : Ctx15350 T Mc M V₁ V₂ t) {y : G}
    (hy : y ∈ Y153 Mc M) (hyN : y ∈ Subgroup.normalizer (VZ T M : Set G)) :
    Odd (orderOf (conjAct (VZ T M) ⟨y, hyN⟩)) := by
  have hmem : conjAct (VZ T M) ⟨y, hyN⟩ ∈ autOn (Y153 Mc M) (VZ T M) :=
    mem_autOn_iff.mpr ⟨⟨y, hyN⟩, hy, rfl⟩
  have hodd : Odd (Nat.card (autOn (Y153 Mc M) (VZ T M))) := by
    rw [cx.c.hyp.autOn_Y153 h113, A4.oTwoUpper_autOn cx.c.hyp.le_normalizer]
    exact cx.c.hyp.odd_card_autOn_oTwoUpper
  have hd : orderOf (⟨conjAct (VZ T M) ⟨y, hyN⟩, hmem⟩ : ↥(autOn (Y153 Mc M) (VZ T M))) ∣
      Nat.card (autOn (Y153 Mc M) (VZ T M)) := orderOf_dvd_natCard _
  rw [Subgroup.orderOf_mk] at hd
  exact Odd.of_dvd_nat hodd hd

omit [Finite G] in
theorem conjAct_eq_one_iff (V : Subgroup G) (g : ↥(Subgroup.normalizer (V : Set G))) :
    conjAct V g = 1 ↔ (g : G) ∈ Subgroup.centralizer (V : Set G) :=
  CFSG.Quasithin.AutOn.conjAct_eq_one_iff g

theorem centralizer_IYU_le (h113 : StageLemma14113) (cx : Ctx15350 T Mc M V₁ V₂ t) {x : G}
    (hx : x ∈ IYU T Mc M V₁) (hxV : x ∈ Subgroup.centralizer (VZ T M : Set G)) :
    x ∈ UH153 T M V₁ Mc ⊔ pCoreOf 2 (Y153 Mc M) := by
  obtain ⟨u, hu, y, hy, rfl⟩ := (mem_IYU_iff cx).mp hx
  have huN : u ∈ Subgroup.normalizer (VZ T M : Set G) := S153E.U_le_N cx hu
  have hyN : y ∈ Subgroup.normalizer (VZ T M : Set G) :=
    cx.c.hyp.le_normalizer (Y153_le Mc M hy)
  have h1 : conjAct (VZ T M) ⟨u, huN⟩ * conjAct (VZ T M) ⟨y, hyN⟩ = 1 := by
    rw [← map_mul]
    exact (conjAct_eq_one_iff _ _).mpr hxV
  have h2 : conjAct (VZ T M) ⟨y, hyN⟩ = (conjAct (VZ T M) ⟨u, huN⟩)⁻¹ :=
    eq_inv_of_mul_eq_one_right h1
  have hodd := odd_orderOf_conjAct_Y h113 cx hy hyN
  obtain ⟨k, hk⟩ := (pCoreOf_isPGroup 2 Mc).to_le (S153E.U_le_Q cx) ⟨u, hu⟩
  have hu2 : (conjAct (VZ T M) ⟨u, huN⟩) ^ 2 ^ k = 1 := by
    rw [← map_pow]
    have : (⟨u, huN⟩ : ↥(Subgroup.normalizer (VZ T M : Set G))) ^ 2 ^ k = 1 :=
      Subtype.ext (by simpa using congrArg Subtype.val hk)
    rw [this, map_one]
  have hdvd : orderOf (conjAct (VZ T M) ⟨u, huN⟩) ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hu2
  have hord : orderOf (conjAct (VZ T M) ⟨u, huN⟩) = orderOf (conjAct (VZ T M) ⟨y, hyN⟩) := by
    rw [h2, orderOf_inv]
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
  have hj0 : j = 0 := by
    rw [hj] at hord
    rw [← hord] at hodd
    by_contra hne
    exact (Nat.not_odd_iff_even.mpr (Nat.even_pow.mpr ⟨even_two, hne⟩)) hodd
  rw [hj0, pow_zero] at hj
  have hy1 : conjAct (VZ T M) ⟨y, hyN⟩ = 1 := orderOf_eq_one_iff.mp (hord ▸ hj)
  have hyC : y ∈ Subgroup.centralizer (VZ T M : Set G) := (conjAct_eq_one_iff _ _).mp hy1
  have hyO : y ∈ pCoreOf 2 (Y153 Mc M) := by
    rw [cx.r49.case_one.1]
    exact ⟨hy, hyC⟩
  exact Subgroup.mul_mem_sup hu hyO

theorem isPGroup_centralizer_IYU (h113 : StageLemma14113) (cx : Ctx15350 T Mc M V₁ V₂ t) :
    IsPGroup 2 ↥(IYU T Mc M V₁ ⊓ Subgroup.centralizer (VZ T M : Set G)) := by
  have hle : IYU T Mc M V₁ ⊓ Subgroup.centralizer (VZ T M : Set G) ≤
      UH153 T M V₁ Mc ⊔ pCoreOf 2 (Y153 Mc M) := fun x hx => centralizer_IYU_le h113 cx hx.1 hx.2
  have hU2 : IsPGroup 2 ↥(UH153 T M V₁ Mc) := (pCoreOf_isPGroup 2 Mc).to_le (S153E.U_le_Q cx)
  have hO2 : IsPGroup 2 ↥(pCoreOf 2 (Y153 Mc M)) := pCoreOf_isPGroup 2 _
  have hnorm : UH153 T M V₁ Mc ≤ Subgroup.normalizer (pCoreOf 2 (Y153 Mc M) : Set G) :=
    (U_le_normalizer_Y cx).trans (normalizer_le_normalizer_pCoreOf 2 _)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact (isPGroup_sup_of_normalizes hnorm hU2 hO2).to_le hle

theorem pCoreOf_IYU_eq (h113 : StageLemma14113) (cx : Ctx15350 T Mc M V₁ V₂ t)
    (hP : VZ T M ≤ centerOf (pCoreOf 2 (IYU T Mc M V₁))) :
    pCoreOf 2 (IYU T Mc M V₁) = IYU T Mc M V₁ ⊓ Subgroup.centralizer (VZ T M : Set G) := by
  apply le_antisymm
  · refine le_inf (pCoreOf_le 2 _) ?_
    intro p hp
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    exact (Subgroup.mem_centralizer_iff.mp (hP hv).2 p hp).symm
  · have hnorm : IYU T Mc M V₁ ≤ Subgroup.normalizer
        ((IYU T Mc M V₁ ⊓ Subgroup.centralizer (VZ T M : Set G) : Subgroup G) : Set G) :=
      fun g hg => Subgroup.inf_normalizer_le_normalizer_inf
        ⟨Subgroup.le_normalizer hg, B2F.normalizer_le_normalizer_centralizer _
          (cx.c.hyp.le_normalizer (IYU_le_M cx hg))⟩
    exact le_pCoreOf_of_le_normalizer 2 inf_le_left hnorm (isPGroup_centralizer_IYU h113 cx)

end CIV


end S153E59

end CFSG.Quasithin
