module

public import CFSG.Quasithin.Background.GoldschmidtAmalgamL2TQB
public import CFSG.Quasithin.Background.F6GoldschmidtList

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.F7
  CFSG.Quasithin.CosetGeom CFSG.Quasithin.F6.GoldAmL CFSG.Quasithin.F6.GoldAmL2S

open scoped commutatorElement

namespace F6

namespace GoldAmL2T

theorem isSpecialTwoOnePlusFour_of_center {P : Type*} [Group P] [Finite P] (hP : IsPGroup 2 P)
    (hcard : Nat.card P = 2 ^ 5) {Z : Subgroup P} (hZ : Nat.card Z = 2)
    (hZc : Z ≤ Subgroup.center P) (hcomm : ∀ x y : P, ⁅x, y⁆ ∈ Z) (hsq : ∀ x : P, x ^ 2 ∈ Z)
    (hcent : ∀ x : P, (∀ y : P, x * y = y * x) → x ∈ Z) (hnab : ∃ x : P, x ∉ Z) :
    IsSpecialTwoOnePlusFour P := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (IsPGroup 2 P) := ⟨hP⟩
  have hcenter : Subgroup.center P = Z := by
    refine le_antisymm (fun x hx => hcent x fun y => ?_) hZc
    exact (Subgroup.mem_center_iff.mp hx y).symm
  have hcom_le : _root_.commutator P ≤ Z := by
    rw [_root_.commutator_def]
    exact Subgroup.commutator_le.mpr fun x _ y _ => hcomm x y
  have hcom : _root_.commutator P = Z := by
    refine le_antisymm hcom_le ?_
    obtain ⟨x, hx⟩ := hnab
    have hnc : ¬ ∀ y : P, x * y = y * x := fun h => hx (hcent x h)
    push Not at hnc
    obtain ⟨y, hy⟩ := hnc
    have hg1 : ⁅x, y⁆ ≠ 1 := fun h => hy (commutatorElement_eq_one_iff_mul_comm.mp h)
    have hgZ : ⁅x, y⁆ ∈ Z := hcomm x y
    have hgc : ⁅x, y⁆ ∈ _root_.commutator P := by
      rw [_root_.commutator_def]
      exact Subgroup.commutator_mem_commutator (Subgroup.mem_top x) (Subgroup.mem_top y)
    have hzp : Subgroup.zpowers ⁅x, y⁆ = Z := by
      refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hgZ) ?_
      rw [hZ, Nat.card_zpowers]
      have h2 : orderOf ⁅x, y⁆ ∣ 2 := by
        have := orderOf_dvd_natCard (⟨_, hgZ⟩ : Z)
        rwa [hZ, Subgroup.orderOf_mk] at this
      rcases (Nat.dvd_prime Nat.prime_two).mp h2 with h | h
      · exact absurd (orderOf_eq_one_iff.mp h) hg1
      · exact h.ge
    rw [← hzp]
    exact (Subgroup.zpowers_le).mpr hgc
  have hfr : frattini P = Z := by
    refine le_antisymm ?_ (hcom ▸ CFSG.commutator_le_frattini_of_isPGroup (R := P) (p := 2))
    rw [CFSG.frattini_eq_closure_commutator_union_powers (p := 2)]
    refine (Subgroup.closure_le _).mpr ?_
    rintro _ (hx | ⟨y, rfl⟩)
    · exact hcom_le hx
    · exact hsq y
  refine ⟨hcard, ?_, ?_, ?_⟩
  · rw [hcenter]; exact hZ
  · rw [hcom, hcenter]
  · rw [hfr, hcenter]

variable {D : Type*} [Group D] {A B : Subgroup D} {z : D} {V : Subgroup D}

section Special

variable [Finite D] {x a a₁ a₂ : D} (g : Gen A B z V x a a₁ a₂)

include g

theorem not_mem_U_of_comm_eq_z {q : D}
    (hcomm : (a * a₁ * a₂) * q * (a * a₁ * a₂)⁻¹ * q⁻¹ = z) : q ∉ conjClosure V B := fun hU => by
  have h1 : (a * a₁ * a₂) * q = q * (a * a₁ * a₂) := g.c_central q hU
  have h2 : (a * a₁ * a₂) * q * (a * a₁ * a₂)⁻¹ * q⁻¹ = 1 := by rw [h1]; group
  rw [h2] at hcomm
  exact g.hyp.natural.z_ne hcomm.symm

theorem isSpecialTwoOnePlusFour_pCoreOf_right (hT : Nat.card ↥(A ⊓ B) = 64) :
    IsSpecialTwoOnePlusFour ↥(pCoreOf 2 B) := by
  have hzQ : z ∈ pCoreOf 2 B := g.hyp.U_le g.hyp.z_mem_U
  have hzle : Subgroup.zpowers z ≤ pCoreOf 2 B := Subgroup.zpowers_le.mpr hzQ
  have hP : IsPGroup 2 ↥(pCoreOf 2 B) := g.hyp.isPGroup_T.to_le g.hyp.QB_le_T
  refine isSpecialTwoOnePlusFour_of_center hP (by rw [card_QB_of_card_T g hT]; norm_num)
    (Z := (Subgroup.zpowers z).subgroupOf (pCoreOf 2 B)) ?_ ?_ ?_ ?_ ?_ ?_
  · rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hzle).toEquiv]
    exact g.hyp.card_zpowers
  · rintro ⟨w, hw⟩ hwZ
    rw [Subgroup.mem_subgroupOf] at hwZ
    rw [Subgroup.mem_center_iff]
    intro y
    exact Subtype.ext (g.hyp.zpowers_comm (g.hyp.QB_le_T y.2).2 hwZ)
  · intro p q
    rw [commutatorElement_def, Subgroup.mem_subgroupOf]
    exact comm_mem_zpowers_QB g hT p.2 q.2
  · intro p
    rw [Subgroup.mem_subgroupOf, Subgroup.coe_pow, pow_two]
    exact sq_mem_zpowers_QB g hT p.2
  · intro p hp
    rw [Subgroup.mem_subgroupOf]
    exact center_QB_le g hT p.2 fun y hy => congrArg Subtype.val (hp ⟨y, hy⟩)
  · obtain ⟨q₀, hq₀, hcomm⟩ := exists_q0 g hT
    refine ⟨⟨q₀, hq₀⟩, fun hmem => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hmem
    exact not_mem_U_of_comm_eq_z g hcomm (Subgroup.zpowers_le.mpr g.hyp.z_mem_U hmem)

end Special

end GoldAmL2T

end F6

end CFSG.Quasithin
