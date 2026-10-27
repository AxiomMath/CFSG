module

public import CFSG.Quasithin.Vol2.Ch11SecHHall
public import CFSG.Quasithin.Vol2.Ch11SecHInputs

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecH

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13 CFSG.Quasithin.InternalSec

variable {G : Type} [Group G] [Finite G]

structure Inp32 : Prop where
  h1102 : Stmt11_0_2
  h1134 : Stmt11_3_4
  h1135 : Stmt11_3_5
  h1136 : Stmt11_3_6
  h1137 : Stmt11_3_7
  hG16 : ASInputs.AS_G_1_6
  hI13 : AS_I_1_3_L2
  hG2 : SecA.FactG2DerivedOrder
  hKF1 : FactTransvInSL3
  hKF2 : FactAxisGroupSp4
  hKF3 : FactSL2NatBorel
  hKF5 : FactSL2TwoSylow
  hKF6 : FactSL2BorelFPF

structure Cfg (T L I : Subgroup G) (n : ℕ) (V₁ H : Subgroup G) (g h : G) : Prop where
  s : SecC.Set37 T L I n V₁ H g
  hH : h ∈ H
  hM : h ∉ Subgroup.normalizer (L : Set G)

structure Data (T L I : Subgroup G) (n : ℕ) (V₁ H : Subgroup G) (g h y : G) : Prop where
  c : Cfg T L I n V₁ H g h
  comp : quasithinIsCComponent (oTwoUpper H) H
  kStar : ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 2 ^ n ∧
    Nonempty (↥(autOn (oTwoUpper H) (VZ T H)) ≃* Matrix.SpecialLinearGroup (Fin 2) F)
  kQuot : ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 2 ^ n ∧
    Nonempty (↥(oTwoUpper H) ⧸ CFSG.pCore 2 ↥(oTwoUpper H) ≃*
      Matrix.SpecialLinearGroup (Fin 2) F)
  VL : fsuV T I ⊓ Subgroup.centralizer (L : Set G) = ⊥
  VHK : VZ T H ⊓ Subgroup.centralizer (oTwoUpper H : Set G) = ⊥
  Vg : fsuV T I = conjSubgroup (fsuV T I) g
  sylow : QuasithinUnique.IsSylowTwoOf (autOn (fsuV T I) (VZ T H))
    (autOn (oTwoUpper H) (VZ T H))
  yL : y ∈ L
  yH : y ∈ H
  yodd : Odd (orderOf y)
  yne : y ≠ 1

omit [Finite G] in
theorem conj_mem_centralizer {W : Subgroup G} {x z : G}
    (hx : x ∈ Subgroup.normalizer (W : Set G)) (hz : z ∈ Subgroup.centralizer (W : Set G)) :
    x * z * x⁻¹ ∈ Subgroup.centralizer (W : Set G) := by
  rw [Subgroup.mem_centralizer_iff] at hz ⊢
  intro w hw
  have hw' : x⁻¹ * w * x ∈ W := by
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hx) w).mp hw
    simpa using this
  have := hz _ hw'
  calc w * (x * z * x⁻¹) = x * ((x⁻¹ * w * x) * z) * x⁻¹ := by group
    _ = x * (z * (x⁻¹ * w * x)) * x⁻¹ := by rw [this]
    _ = x * z * x⁻¹ * w := by group

omit [Finite G] in
theorem le_normalizer_inf_centralizer {X W : Subgroup G}
    (hX : X ≤ Subgroup.normalizer (W : Set G)) :
    X ≤ Subgroup.normalizer ((X ⊓ Subgroup.centralizer (W : Set G) : Subgroup G) : Set G) := by
  intro x hx
  rw [Subgroup.mem_normalizer_iff]
  intro z
  constructor
  · intro hz
    exact ⟨X.mul_mem (X.mul_mem hx hz.1) (X.inv_mem hx), conj_mem_centralizer (hX hx) hz.2⟩
  · intro hz
    have h1 := conj_mem_centralizer (Subgroup.inv_mem _ (hX hx)) hz.2
    have h2 : x⁻¹ * (x * z * x⁻¹) * x⁻¹⁻¹ = z := by group
    rw [h2] at h1
    have h3 := X.mul_mem (X.mul_mem (X.inv_mem hx) hz.1) (X.inv_mem (X.inv_mem hx))
    rw [h2] at h3
    exact ⟨h3, h1⟩

namespace Cfg

variable {T L I : Subgroup G} {n : ℕ} {V₁ H : Subgroup G} {g h : G}
  (c : Cfg T L I n V₁ H g h)
include c

theorem two_le : 2 ≤ n := c.s.two_le

theorem V_le_T : fsuV T I ≤ T := SecA.fsuV_le_T c.s.hyp

theorem V_le_H : fsuV T I ≤ H := c.V_le_T.trans c.s.T_le

theorem centralizer_VZ_le (h1135 : Stmt11_3_5) (h1136 : Stmt11_3_6) :
    H ⊓ Subgroup.centralizer (VZ T H : Set G) ≤ pCoreOf 2 H := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hKC := SecC.inf_centralizer_VZ_eq h1135 h1136 c.s.hyp c.s.hV₁ c.s.h31 c.s.hnot
  refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_left
    (le_normalizer_inf_centralizer (SecC.le_normalizer_VZ T H)) ?_
  rintro ⟨x, hx⟩
  obtain ⟨e, he⟩ := two_of_sup c.s.hyp.fsu.sylow.1
    (c.s.T_le.trans (le_normalizer_oTwoUpper H)) x (c.s.sup_eq.ge hx.1)
  have hmem : x ^ 2 ^ e ∈ pCoreOf 2 (oTwoUpper H) := by
    rw [← hKC]
    exact ⟨he, Subgroup.pow_mem _ hx.2 _⟩
  obtain ⟨k, hk⟩ := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (oTwoUpper H) ⟨_, hmem⟩
  refine ⟨e + k, Subtype.ext ?_⟩
  have hk' : (x ^ 2 ^ e) ^ 2 ^ k = 1 := by
    simpa using congrArg Subtype.val hk
  simp [pow_add, pow_mul, hk']

theorem fsuV_inf_pCoreOf (h1135 : Stmt11_3_5) (h1136 : Stmt11_3_6) :
    fsuV T I ⊓ pCoreOf 2 H = fsuV T I ⊓ Subgroup.centralizer (VZ T H : Set G) := by
  refine le_antisymm (inf_le_inf_left _ (SecC.pCoreOf_le_centralizer_VZ c.s.hyp c.s.h31)) ?_
  exact le_inf inf_le_left ((le_inf (inf_le_left.trans c.V_le_H) inf_le_right).trans
    (c.centralizer_VZ_le h1135 h1136))

theorem exists_data (i : Inp32) : ∃ y : G, Data T L I n V₁ H g h y := by
  obtain ⟨D, hD⟩ := exists_hall c.s i.h1135 i.h1136 i.hKF5
  obtain ⟨⟨hcomp, ⟨e1⟩, F, _, _, hF, ⟨e2⟩⟩, hD0L, ⟨-, hVL, hVHK⟩, ⟨hVg, hsyl⟩, hV1, -⟩ :=
    i.h1137 G T L I n V₁ H D g c.s.hyp c.s.hV₁ c.s.h31 c.s.hnot c.s.hAT c.s.hAC hD
  rcases Subgroup.bot_or_exists_ne_one (d0Of D) with hbot | ⟨y, hy, hy1⟩
  · exact absurd (by rw [hV1, hbot, Subgroup.commutator_bot_right])
      (SecA.IsVi.ne_bot c.s.hyp c.s.hV₁ le_rfl)
  have hyD : y ∈ D := SecC.d0Of_le_self D hy
  refine ⟨y, ⟨c, hcomp, ⟨F, inferInstance, inferInstance, hF, ⟨e1.trans e2⟩⟩,
    ⟨F, inferInstance, inferInstance, hF, ⟨e2⟩⟩, hVL, hVHK, hVg, hsyl, hD0L hy,
    (hD.1 hyD).1, ?_, hy1⟩⟩
  exact hD.2.1.of_dvd_nat (Subgroup.orderOf_dvd_natCard D hyD)

end Cfg

end CFSG.Quasithin.Vol2.Ch11.SecH
