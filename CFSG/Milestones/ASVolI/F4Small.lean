module

public import CFSG.Milestones.ASVolI.F4
import all CFSG.Milestones.ASVolI.F4
public import CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisExc.WeylConj
public import CFSG.Quasithin.Recognition.CertG2TwoOuter
public import CFSG.Timmesfeld.Orders.ExceptionalUntwisted
public import CFSG.LieType.Chevalley.EvenRootCommutatorG2

public section

namespace CFSG.ASVolI.ChF

open CFSG.Open

open CFSG.Quasithin in
@[expose] def burnsideF4c_InvolInCore {G : Type*} [Group G] (P : Subgroup G) : Prop :=
  ∃ Q : Subgroup G, Q ≤ P ∧ P ≤ Subgroup.normalizer (Q : Set G) ∧ IsPGroup 2 Q ∧
    ∀ s ∈ P, s * s = 1 → s ∈ Q

open CFSG.Quasithin in
def burnsideF4c_qIdx : List ℕ := [0, 5, 6, 7, 8, 9, 11, 12, 18, 20, 21, 23, 24, 25, 26, 31]

open CFSG.Quasithin in
theorem burnsideF4c_qIdx_lt : ∀ i ∈ burnsideF4c_qIdx, i < 32 := by decide

open CFSG.Quasithin in
theorem burnsideF4c_x_moves_z : u33GenP 3 * u33Z * (u33GenP 3)⁻¹ ≠ u33Z := by decide +kernel

open CFSG.Quasithin in
theorem burnsideF4c_T_cent : ∀ i : Fin 32,
    u33Tel u33GenP i * u33GenP 0 = u33GenP 0 * u33Tel u33GenP i →
    u33Tel u33GenP i * u33GenP 1 = u33GenP 1 * u33Tel u33GenP i →
    u33Tel u33GenP i * u33GenP 2 = u33GenP 2 * u33Tel u33GenP i →
    u33Tel u33GenP i * u33Tel u33GenP i = 1 → u33Tel u33GenP i ≠ 1 →
    u33Tel u33GenP i = u33Z := by
  decide +kernel

open CFSG.Quasithin in
theorem burnsideF4c_Q_norm_perm :
    ∀ k ∈ [0, 1, 2, 4], ∀ i ∈ burnsideF4c_qIdx,
      (∃ j ∈ burnsideF4c_qIdx,
        u33GenP k * u33Tel u33GenP i * (u33GenP k)⁻¹ = u33Tel u33GenP j) ∧
      (∃ j ∈ burnsideF4c_qIdx,
        (u33GenP k)⁻¹ * u33Tel u33GenP i * u33GenP k = u33Tel u33GenP j) := by
  decide +kernel

open CFSG.Quasithin in
theorem burnsideF4c_T_invol_perm : ∀ i : Fin 32,
    u33Tel u33GenP i * u33Tel u33GenP i = 1 → i.val ∈ burnsideF4c_qIdx := by
  decide +kernel

open CFSG.Quasithin in
theorem burnsideF4c_B_invol_perm : ∀ i₁ i₂ : Fin 32,
    (u33Tel u33GenP i₁ * u33D u33GenP ((2 : Fin 14) : ℕ) * u33Tel u33GenP i₂) *
      (u33Tel u33GenP i₁ * u33D u33GenP ((2 : Fin 14) : ℕ) * u33Tel u33GenP i₂) = 1 →
    ∃ i ∈ burnsideF4c_qIdx,
      u33Tel u33GenP i₁ * u33D u33GenP ((2 : Fin 14) : ℕ) * u33Tel u33GenP i₂ =
        u33Tel u33GenP i := by
  decide +kernel

open CFSG.Quasithin in
theorem burnsideF4c_x_moves_z' : u33GenPG 3 * u33z * (u33GenPG 3)⁻¹ ≠ u33z := by
  intro h
  apply burnsideF4c_x_moves_z
  have := congrArg u33PresHom h
  simpa only [map_mul, map_inv, u33PresHom_genPG, u33PresHom_z] using this

open CFSG.Quasithin in
theorem burnsideF4c_T_cent'
    (i : Fin 32)
    (h0 : u33Tel u33GenPG i * u33GenPG 0 = u33GenPG 0 * u33Tel u33GenPG i)
    (h1 : u33Tel u33GenPG i * u33GenPG 1 = u33GenPG 1 * u33Tel u33GenPG i)
    (h2 : u33Tel u33GenPG i * u33GenPG 2 = u33GenPG 2 * u33Tel u33GenPG i)
    (hsq : u33Tel u33GenPG i * u33Tel u33GenPG i = 1) (hne : u33Tel u33GenPG i ≠ 1) :
    u33Tel u33GenPG i = u33z := by
  apply u33PresHom_injective
  rw [u33Tel_hom, u33PresHom_z]
  refine burnsideF4c_T_cent i ?_ ?_ ?_ ?_ ?_
  · have := congrArg u33PresHom h0
    simpa only [map_mul, u33Tel_hom, u33PresHom_genPG] using this
  · have := congrArg u33PresHom h1
    simpa only [map_mul, u33Tel_hom, u33PresHom_genPG] using this
  · have := congrArg u33PresHom h2
    simpa only [map_mul, u33Tel_hom, u33PresHom_genPG] using this
  · have := congrArg u33PresHom hsq
    simpa only [map_mul, map_one, u33Tel_hom] using this
  · intro h
    apply hne
    apply u33PresHom_injective
    rw [u33Tel_hom, h, map_one]

open CFSG.Quasithin in
def burnsideF4c_Qset : Set U33G :=
  {g | ∃ i ∈ burnsideF4c_qIdx, u33Tel u33GenPG i = g}

open CFSG.Quasithin in
theorem burnsideF4c_Tel_mem_T
    (i : ℕ) (hi : i < 32) : u33Tel u33GenPG i ∈ u33Data.T :=
  u33Data.Tel_mem_T ⟨i, hi⟩

open CFSG.Quasithin in
theorem burnsideF4c_Qset_le_T
    : Subgroup.closure burnsideF4c_Qset ≤ u33Data.T := by
  refine (Subgroup.closure_le _).2 ?_
  rintro g ⟨i, hi, rfl⟩
  exact burnsideF4c_Tel_mem_T i (burnsideF4c_qIdx_lt i hi)

open CFSG.Quasithin in
theorem burnsideF4c_gen_norm
    (k : ℕ) (hk : k ∈ [0, 1, 2, 4]) :
    u33GenPG k ∈ Subgroup.normalizer (Subgroup.closure burnsideF4c_Qset : Set U33G) := by
  apply mem_normalizer_closure_of
  · rintro _ ⟨i, hi, rfl⟩
    obtain ⟨⟨j, hj, hjeq⟩, -⟩ := burnsideF4c_Q_norm_perm k hk i hi
    refine ⟨j, hj, ?_⟩
    apply u33PresHom_injective
    simpa only [map_mul, map_inv, u33Tel_hom, u33PresHom_genPG] using hjeq.symm
  · rintro _ ⟨i, hi, rfl⟩
    obtain ⟨-, ⟨j, hj, hjeq⟩⟩ := burnsideF4c_Q_norm_perm k hk i hi
    refine ⟨j, hj, ?_⟩
    apply u33PresHom_injective
    simpa only [map_mul, map_inv, u33Tel_hom, u33PresHom_genPG] using hjeq.symm

open CFSG.Quasithin in
theorem burnsideF4c_T_mem_of_double
    (i₁ i₂ : Fin 32) :
    u33Data.Tel i₁ * u33Data.D u33Data.j0 * u33Data.Tel i₂ ∈ u33Data.T := by
  rw [u33Data.D_zero, mul_one]
  exact u33Data.T.mul_mem (u33Data.Tel_mem_T i₁) (u33Data.Tel_mem_T i₂)

open CFSG.Quasithin in
theorem burnsideF4c_Tel_sq (k : Fin 32) (h : u33Tel u33GenPG k * u33Tel u33GenPG k = 1) :
    u33Tel u33GenP k * u33Tel u33GenP k = 1 := by
  rw [← u33Tel_hom, ← map_mul, h, map_one]

open CFSG.Quasithin in
theorem burnsideF4c_double_sq (i₁ i₂ : Fin 32)
    (h : (u33Tel u33GenPG i₁ * u33D u33GenPG ((2 : Fin 14) : ℕ) * u33Tel u33GenPG i₂) *
      (u33Tel u33GenPG i₁ * u33D u33GenPG ((2 : Fin 14) : ℕ) * u33Tel u33GenPG i₂) = 1) :
    (u33Tel u33GenP i₁ * u33D u33GenP ((2 : Fin 14) : ℕ) * u33Tel u33GenP i₂) *
      (u33Tel u33GenP i₁ * u33D u33GenP ((2 : Fin 14) : ℕ) * u33Tel u33GenP i₂) = 1 := by
  have := congrArg u33PresHom h
  simp only [map_one, map_mul, u33Tel_hom, u33D_hom] at this
  exact this

open CFSG.Quasithin in
theorem burnsideF4c_double_eq
    (i₁ i₂ i : Fin 32)
    (h : u33Tel u33GenP i₁ * u33D u33GenP ((2 : Fin 14) : ℕ) * u33Tel u33GenP i₂ =
      u33Tel u33GenP i) :
    u33Tel u33GenPG i₁ * u33D u33GenPG ((2 : Fin 14) : ℕ) * u33Tel u33GenPG i₂ =
      u33Tel u33GenPG i := by
  apply u33PresHom_injective
  simp only [map_mul, u33Tel_hom, u33D_hom]
  exact h

open CFSG.Quasithin in
theorem burnsideF4c_u33_no_x
    (P : Subgroup U33G) (hT : u33Data.T ≤ P) (hx : u33GenPG 3 ∈ P)
    (z : U33G) (hz1 : z ≠ 1) (hz2 : z * z = 1) (hPz : ∀ p ∈ P, p * z = z * p) : False := by
  have hcomm : ∀ t ∈ u33Data.T, z * t = t * z := fun t ht => (hPz t (hT ht)).symm
  have hzT : z ∈ u33Data.T := by
    rw [← u33Extra.normalizer_T, Subgroup.mem_normalizer_iff]
    intro g
    constructor
    · intro hg
      have e : z * g * z⁻¹ = g := by rw [hcomm g hg]; group
      rwa [e]
    · intro hg
      have e : z * g * z⁻¹ = g := by
        have := hcomm (z * g * z⁻¹) hg
        have h2 : z * (z * g * z⁻¹) = (z * g * z⁻¹) * z := this
        have h3 : z * g = z * (z * g * z⁻¹) := by
          calc z * g = (z * g * z⁻¹) * z := by group
            _ = z * (z * g * z⁻¹) := h2.symm
        exact (mul_left_cancel h3).symm
      rwa [e] at hg
  obtain ⟨i, hi⟩ := (u33Data.mem_T_iff z).1 hzT
  have hi' : u33Tel u33GenPG i = z := hi
  have ha : z * u33GenPG 0 = u33GenPG 0 * z := hcomm _ u33Data.a_mem_T
  have hb : z * u33GenPG 1 = u33GenPG 1 * z := hcomm _ u33Data.b_mem_T
  have hs : z * u33GenPG 2 = u33GenPG 2 * z := hcomm _ u33Data.s_mem_T
  have hcz := burnsideF4c_T_cent' i (by rw [hi']; exact ha) (by rw [hi']; exact hb)
    (by rw [hi']; exact hs) (by rw [hi']; exact hz2) (by rw [hi']; exact hz1)
  rw [hi'] at hcz
  have hx' : u33GenPG 3 * z = z * u33GenPG 3 := hPz _ hx
  apply burnsideF4c_x_moves_z'
  rw [hcz] at hx'
  calc u33GenPG 3 * u33z * (u33GenPG 3)⁻¹ = (u33z * u33GenPG 3) * (u33GenPG 3)⁻¹ := by rw [hx']
    _ = u33z := by group

open CFSG.Quasithin in
theorem burnsideF4c_u33_invol
    (P : Subgroup U33G) (hT : u33Data.T ≤ P) (hne : P ≠ u33Data.T)
    (z : U33G) (hz1 : z ≠ 1) (hz2 : z * z = 1)
    (hPz : ∀ p ∈ P, p * z = z * p) : burnsideF4c_InvolInCore P := by
  rcases u33Data.lattice P hT with h | h | h | h
  · exact absurd h hne
  · subst h
    exact (burnsideF4c_u33_no_x _ hT u33Data.x_mem_A z hz1 hz2 hPz).elim
  · subst h
    refine ⟨Subgroup.closure burnsideF4c_Qset, burnsideF4c_Qset_le_T.trans u33Data.T_le_B, ?_,
      u33_syl.1.to_le burnsideF4c_Qset_le_T, ?_⟩
    · refine (Subgroup.closure_le _).2 ?_
      rintro g (rfl | rfl | rfl | rfl)
      · exact burnsideF4c_gen_norm 0 (by simp)
      · exact burnsideF4c_gen_norm 1 (by simp)
      · exact burnsideF4c_gen_norm 2 (by simp)
      · exact burnsideF4c_gen_norm 4 (by simp)
    · intro s hs hs2
      obtain ⟨j, hj, i₁, i₂, rfl⟩ := (u33Data.mem_B_iff s).1 hs
      rcases hj with rfl | hj
      · obtain ⟨k, hk⟩ := (u33Data.mem_T_iff _).1 (burnsideF4c_T_mem_of_double i₁ i₂)
        rw [← hk] at hs2 ⊢
        exact Subgroup.subset_closure ⟨k, burnsideF4c_T_invol_perm k
          (burnsideF4c_Tel_sq k hs2), rfl⟩
      · have hj2 : j = 2 := hj.trans rfl
        subst hj2
        have hD : u33Data.D 2 = u33D u33GenPG ((2 : Fin 14) : ℕ) := rfl
        rw [hD] at hs2 ⊢
        obtain ⟨i, hi, hieq⟩ := burnsideF4c_B_invol_perm i₁ i₂ (burnsideF4c_double_sq i₁ i₂ hs2)
        exact Subgroup.subset_closure ⟨i, hi, (burnsideF4c_double_eq i₁ i₂
          ⟨i, burnsideF4c_qIdx_lt i hi⟩ hieq).symm⟩
  · subst h
    exact (burnsideF4c_u33_no_x _ hT (Subgroup.mem_top _) z hz1 hz2 hPz).elim

section G2Bridge

variable {K : Type} [Field K] [CharP K 2]

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisExc in
open CFSG.Quasithin (isSimpleGroup_u33Pres u33GenP u33PresHom u33PresHom_genPG card_u33Pres u33_orders u33_syl g2HomC g2RhoC g2IndexTwoData g2HomC_injective finite_g2Group G2Group U33G u33GenPG u33Data u33Extra g2Hom g2Img g2L g2L_one g2L_three g2L_zero g2L_zero_eq_img g2L_one_mul_three g2Img_mem_range g2L_mem_normalizer g2_derived_eq_range adjointGroup_G2_eq g2Hom_of u33GenPG_of g2Hom_injective two_eq_zero_of_card_two eq_zero_or_eq_one_of_card_two) in
noncomputable def burnsideF4c_wU
    : List (Fin 2) → ModGL Tag.G2 K → ModGL Tag.G2 K
  | [], a => a
  | i :: w, a => burnsideF4c_wU w (weylElt Tag.G2 K i 1 * a)

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisExc in
open CFSG.Quasithin (isSimpleGroup_u33Pres u33GenP u33PresHom u33PresHom_genPG card_u33Pres u33_orders u33_syl g2HomC g2RhoC g2IndexTwoData g2HomC_injective finite_g2Group G2Group U33G u33GenPG u33Data u33Extra g2Hom g2Img g2L g2L_one g2L_three g2L_zero g2L_zero_eq_img g2L_one_mul_three g2Img_mem_range g2L_mem_normalizer g2_derived_eq_range adjointGroup_G2_eq g2Hom_of u33GenPG_of g2Hom_injective two_eq_zero_of_card_two eq_zero_or_eq_one_of_card_two) in
def burnsideF4c_reflW : List (Fin 2) → (Fin 2 → ℤ) → (Fin 2 → ℤ)
  | [], v => v
  | i :: w, v => burnsideF4c_reflW w (reflect Tag.G2 i v)

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisExc in
open CFSG.Quasithin (isSimpleGroup_u33Pres u33GenP u33PresHom u33PresHom_genPG card_u33Pres u33_orders u33_syl g2HomC g2RhoC g2IndexTwoData g2HomC_injective finite_g2Group G2Group U33G u33GenPG u33Data u33Extra g2Hom g2Img g2L g2L_one g2L_three g2L_zero g2L_zero_eq_img g2L_one_mul_three g2Img_mem_range g2L_mem_normalizer g2_derived_eq_range adjointGroup_G2_eq g2Hom_of u33GenPG_of g2Hom_injective two_eq_zero_of_card_two eq_zero_or_eq_one_of_card_two) in
theorem burnsideF4c_reflW_eq (w : List (Fin 2)) (v : Fin 2 → ℤ) :
    G2Native.reflectedVector w v = burnsideF4c_reflW w v := by
  induction w generalizing v with
  | nil => rfl
  | cons i w ih => exact ih _

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisExc in
open CFSG.Quasithin (isSimpleGroup_u33Pres u33GenP u33PresHom u33PresHom_genPG card_u33Pres u33_orders u33_syl g2HomC g2RhoC g2IndexTwoData g2HomC_injective finite_g2Group G2Group U33G u33GenPG u33Data u33Extra g2Hom g2Img g2L g2L_one g2L_three g2L_zero g2L_zero_eq_img g2L_one_mul_three g2Img_mem_range g2L_mem_normalizer g2_derived_eq_range adjointGroup_G2_eq g2Hom_of u33GenPG_of g2Hom_injective two_eq_zero_of_card_two eq_zero_or_eq_one_of_card_two) in
theorem burnsideF4c_coe_wU
    (w : List (Fin 2)) (a : ModGL Tag.G2 K) :
    ((burnsideF4c_wU w a : ModGL Tag.G2 K) : Module.End K (RootModule Tag.G2 K)) =
      w.foldl (fun op i => G2Native.weylOperator K i 1 * op)
        (a : Module.End K (RootModule Tag.G2 K)) := by
  induction w generalizing a with
  | nil => rfl
  | cons i w ih => exact ih _

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisExc in
open CFSG.Quasithin (isSimpleGroup_u33Pres u33GenP u33PresHom u33PresHom_genPG card_u33Pres u33_orders u33_syl g2HomC g2RhoC g2IndexTwoData g2HomC_injective finite_g2Group G2Group U33G u33GenPG u33Data u33Extra g2Hom g2Img g2L g2L_one g2L_three g2L_zero g2L_zero_eq_img g2L_one_mul_three g2Img_mem_range g2L_mem_normalizer g2_derived_eq_range adjointGroup_G2_eq g2Hom_of u33GenPG_of g2Hom_injective two_eq_zero_of_card_two eq_zero_or_eq_one_of_card_two) in
theorem burnsideF4c_wU_conj
    (w : List (Fin 2)) :
    ∀ (a : ModGL Tag.G2 K) (α β : Fin 2 → ℤ) (c : K), IsRoot Tag.G2 β →
      a * pinnedX Tag.G2 K α c * a⁻¹ = pinnedX Tag.G2 K β c →
      IsRoot Tag.G2 (burnsideF4c_reflW w β) ∧
        burnsideF4c_wU w a * pinnedX Tag.G2 K α c * (burnsideF4c_wU w a)⁻¹ =
          pinnedX Tag.G2 K (burnsideF4c_reflW w β) c := by
  induction w with
  | nil => intro a α β c hβ h; exact ⟨hβ, h⟩
  | cons i w ih =>
    intro a α β c hβ h
    refine ih (weylElt Tag.G2 K i 1 * a) α (reflect Tag.G2 i β) c
      (IsRoot.reflect (τ := Tag.G2) i hβ) ?_
    calc weylElt Tag.G2 K i 1 * a * pinnedX Tag.G2 K α c * (weylElt Tag.G2 K i 1 * a)⁻¹
        = weylElt Tag.G2 K i 1 * (a * pinnedX Tag.G2 K α c * a⁻¹) * (weylElt Tag.G2 K i 1)⁻¹ := by
          group
      _ = pinnedX Tag.G2 K (reflect Tag.G2 i β) c := by
          rw [h]; exact nC_conj_pinnedX (τ := Tag.G2) (K := K) i hβ c

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisExc in
open CFSG.Quasithin (isSimpleGroup_u33Pres u33GenP u33PresHom u33PresHom_genPG card_u33Pres u33_orders u33_syl g2HomC g2RhoC g2IndexTwoData g2HomC_injective finite_g2Group G2Group U33G u33GenPG u33Data u33Extra g2Hom g2Img g2L g2L_one g2L_three g2L_zero g2L_zero_eq_img g2L_one_mul_three g2Img_mem_range g2L_mem_normalizer g2_derived_eq_range adjointGroup_G2_eq g2Hom_of u33GenPG_of g2Hom_injective two_eq_zero_of_card_two eq_zero_or_eq_one_of_card_two) in
theorem burnsideF4c_reflW_snoc (w : List (Fin 2)) (i : Fin 2) (v : Fin 2 → ℤ) :
    burnsideF4c_reflW (w ++ [i]) v = reflect Tag.G2 i (burnsideF4c_reflW w v) := by
  induction w generalizing v with
  | nil => rfl
  | cons j w ih => exact ih _

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisExc in
open CFSG.Quasithin (isSimpleGroup_u33Pres u33GenP u33PresHom u33PresHom_genPG card_u33Pres u33_orders u33_syl g2HomC g2RhoC g2IndexTwoData g2HomC_injective finite_g2Group G2Group U33G u33GenPG u33Data u33Extra g2Hom g2Img g2L g2L_one g2L_three g2L_zero g2L_zero_eq_img g2L_one_mul_three g2Img_mem_range g2L_mem_normalizer g2_derived_eq_range adjointGroup_G2_eq g2Hom_of u33GenPG_of g2Hom_injective two_eq_zero_of_card_two eq_zero_or_eq_one_of_card_two) in
theorem burnsideF4c_reach {α : Fin Tag.G2.rank → ℤ} (hα : IsRoot Tag.G2 α) :
    ∃ (w : List (Fin Tag.G2.rank)) (i : Fin Tag.G2.rank),
      burnsideF4c_reflW w (Pi.single i 1) = α := by
  induction hα with
  | basis j => exact ⟨[], j, rfl⟩
  | reflect i hv ih =>
    obtain ⟨w, j, hw⟩ := ih
    exact ⟨w ++ [i], j, (burnsideF4c_reflW_snoc w i _).trans (congrArg (reflect Tag.G2 i) hw)⟩

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisExc in
open CFSG.Quasithin (isSimpleGroup_u33Pres u33GenP u33PresHom u33PresHom_genPG card_u33Pres u33_orders u33_syl g2HomC g2RhoC g2IndexTwoData g2HomC_injective finite_g2Group G2Group U33G u33GenPG u33Data u33Extra g2Hom g2Img g2L g2L_one g2L_three g2L_zero g2L_zero_eq_img g2L_one_mul_three g2Img_mem_range g2L_mem_normalizer g2_derived_eq_range adjointGroup_G2_eq g2Hom_of u33GenPG_of g2Hom_injective two_eq_zero_of_card_two eq_zero_or_eq_one_of_card_two) in
theorem burnsideF4c_wU_mem
    (w : List (Fin 2)) (a : ModGL Tag.G2 K)
    (ha : a ∈ adjointGroup Tag.G2 K) : burnsideF4c_wU w a ∈ adjointGroup Tag.G2 K := by
  induction w generalizing a with
  | nil => exact ha
  | cons i w ih => exact ih _ (Subgroup.mul_mem _ (weylElt_mem_adjointGroup _ _) ha)

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisExc in
open CFSG.Quasithin (isSimpleGroup_u33Pres u33GenP u33PresHom u33PresHom_genPG card_u33Pres u33_orders u33_syl g2HomC g2RhoC g2IndexTwoData g2HomC_injective finite_g2Group G2Group U33G u33GenPG u33Data u33Extra g2Hom g2Img g2L g2L_one g2L_three g2L_zero g2L_zero_eq_img g2L_one_mul_three g2Img_mem_range g2L_mem_normalizer g2_derived_eq_range adjointGroup_G2_eq g2Hom_of u33GenPG_of g2Hom_injective two_eq_zero_of_card_two eq_zero_or_eq_one_of_card_two) in
theorem burnsideF4c_wU_one_conj
    (w : List (Fin 2)) (i : Fin 2) (c : K) :
    IsRoot Tag.G2 (burnsideF4c_reflW w (Pi.single i 1)) ∧
      burnsideF4c_wU w 1 * pinnedX Tag.G2 K (Pi.single i 1) c * (burnsideF4c_wU w 1)⁻¹ =
        pinnedX Tag.G2 K (burnsideF4c_reflW w (Pi.single i 1)) c :=
  burnsideF4c_wU_conj w 1 _ _ c (isRoot_single Tag.G2 i)
    (by simp only [inv_one, one_mul, mul_one] <;> rfl)

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisExc in
open CFSG.Quasithin (isSimpleGroup_u33Pres u33GenP u33PresHom u33PresHom_genPG card_u33Pres u33_orders u33_syl g2HomC g2RhoC g2IndexTwoData g2HomC_injective finite_g2Group G2Group U33G u33GenPG u33Data u33Extra g2Hom g2Img g2L g2L_one g2L_three g2L_zero g2L_zero_eq_img g2L_one_mul_three g2Img_mem_range g2L_mem_normalizer g2_derived_eq_range adjointGroup_G2_eq g2Hom_of u33GenPG_of g2Hom_injective two_eq_zero_of_card_two eq_zero_or_eq_one_of_card_two) in
theorem burnsideF4c_mem_rootGenerators
    {root : Fin 2 → ℤ} (hroot : IsRoot Tag.G2 root)
    (x : G2Native.Parent K) :
    x ∈ G2Native.rootGenerators K root ↔
      ∃ c : K, (x : ModGL Tag.G2 K) = pinnedX Tag.G2 K root c := by
  constructor
  · rintro ⟨w, i, hw, rep, hrep, gen, ⟨c, hc⟩, rfl⟩
    have hrep' : (rep : ModGL Tag.G2 K) = burnsideF4c_wU w 1 :=
      Units.ext (hrep.trans (burnsideF4c_coe_wU w 1).symm)
    have hgen' : (gen : ModGL Tag.G2 K) = pinnedX Tag.G2 K (Pi.single i 1) c :=
      (Units.ext hc : (gen : ModGL Tag.G2 K) = xUnit Tag.G2 K i c).trans
        (pinnedX_single (τ := Tag.G2) (R := K) i c).symm
    have hw' : burnsideF4c_reflW w (Pi.single i 1) = root :=
      (burnsideF4c_reflW_eq w _).symm.trans hw
    refine ⟨c, ?_⟩
    have e1 : ((rep * gen * rep⁻¹ : G2Native.Parent K) : ModGL Tag.G2 K) =
        (rep : ModGL Tag.G2 K) * (gen : ModGL Tag.G2 K) * (rep : ModGL Tag.G2 K)⁻¹ := rfl
    refine e1.trans ?_
    rw [hrep', hgen']
    refine (burnsideF4c_wU_one_conj w i c).2.trans ?_
    rw [hw']
  · rintro ⟨c, hc⟩
    obtain ⟨w, i, hw⟩ := burnsideF4c_reach hroot
    refine ⟨w, i, (burnsideF4c_reflW_eq w _).trans hw, ⟨burnsideF4c_wU w 1,
      burnsideF4c_wU_mem w 1 (Subgroup.one_mem _)⟩, ?_,
      ⟨xUnit Tag.G2 K i c, xUnit_mem_adjointGroup _ _⟩, ⟨c, rfl⟩, ?_⟩
    · exact burnsideF4c_coe_wU w 1
    · refine Subtype.ext ?_
      have e1 : ((⟨burnsideF4c_wU w 1, burnsideF4c_wU_mem w 1 (Subgroup.one_mem _)⟩ *
          ⟨xUnit Tag.G2 K i c, xUnit_mem_adjointGroup _ _⟩ *
          ⟨burnsideF4c_wU w 1, burnsideF4c_wU_mem w 1 (Subgroup.one_mem _)⟩⁻¹ :
            G2Native.Parent K) : ModGL Tag.G2 K) =
          burnsideF4c_wU w 1 * xUnit Tag.G2 K i c * (burnsideF4c_wU w 1)⁻¹ := rfl
      refine Eq.trans ?_ e1.symm
      rw [hc, ← pinnedX_single (τ := Tag.G2) (R := K) i c]
      refine Eq.trans ?_ (burnsideF4c_wU_one_conj w i c).2.symm
      rw [hw]

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisExc in
open CFSG.Quasithin (isSimpleGroup_u33Pres u33GenP u33PresHom u33PresHom_genPG card_u33Pres u33_orders u33_syl g2HomC g2RhoC g2IndexTwoData g2HomC_injective finite_g2Group G2Group U33G u33GenPG u33Data u33Extra g2Hom g2Img g2L g2L_one g2L_three g2L_zero g2L_zero_eq_img g2L_one_mul_three g2Img_mem_range g2L_mem_normalizer g2_derived_eq_range adjointGroup_G2_eq g2Hom_of u33GenPG_of g2Hom_injective two_eq_zero_of_card_two eq_zero_or_eq_one_of_card_two) in
theorem burnsideF4c_weylElt_neg_one
    (i : Fin Tag.G2.rank) :
    weylElt Tag.G2 K i (-1) = (weylElt Tag.G2 K i 1)⁻¹ := by
  refine Units.ext ?_
  rw [coe_weylElt, coe_weylElt_inv]
  simp

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisExc in
open CFSG.Quasithin (isSimpleGroup_u33Pres u33GenP u33PresHom u33PresHom_genPG card_u33Pres u33_orders u33_syl g2HomC g2RhoC g2IndexTwoData g2HomC_injective finite_g2Group G2Group U33G u33GenPG u33Data u33Extra g2Hom g2Img g2L g2L_one g2L_three g2L_zero g2L_zero_eq_img g2L_one_mul_three g2Img_mem_range g2L_mem_normalizer g2_derived_eq_range adjointGroup_G2_eq g2Hom_of u33GenPG_of g2Hom_injective two_eq_zero_of_card_two eq_zero_or_eq_one_of_card_two) in
theorem burnsideF4c_torusElt_one
    (i : Fin Tag.G2.rank) : torusElt Tag.G2 K i 1 = 1 := by
  unfold torusElt
  rw [burnsideF4c_weylElt_neg_one]
  exact mul_inv_cancel _

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisExc in
open CFSG.Quasithin (isSimpleGroup_u33Pres u33GenP u33PresHom u33PresHom_genPG card_u33Pres u33_orders u33_syl g2HomC g2RhoC g2IndexTwoData g2HomC_injective finite_g2Group G2Group U33G u33GenPG u33Data u33Extra g2Hom g2Img g2L g2L_one g2L_three g2L_zero g2L_zero_eq_img g2L_one_mul_three g2Img_mem_range g2L_mem_normalizer g2_derived_eq_range adjointGroup_G2_eq g2Hom_of u33GenPG_of g2Hom_injective two_eq_zero_of_card_two eq_zero_or_eq_one_of_card_two) in
theorem burnsideF4c_isRoot_of_mem_rootGenerators
    {root : Fin 2 → ℤ} {x : G2Native.Parent K}
    (hx : x ∈ G2Native.rootGenerators K root) : IsRoot Tag.G2 root := by
  obtain ⟨w, i, hw, -⟩ := hx
  have hw' : burnsideF4c_reflW w (Pi.single i 1) = root :=
    (burnsideF4c_reflW_eq w _).symm.trans hw
  rw [← hw']
  exact (burnsideF4c_wU_one_conj (K := K) w i 1).1

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisExc in
open CFSG.Quasithin (isSimpleGroup_u33Pres u33GenP u33PresHom u33PresHom_genPG card_u33Pres u33_orders u33_syl g2HomC g2RhoC g2IndexTwoData g2HomC_injective finite_g2Group G2Group U33G u33GenPG u33Data u33Extra g2Hom g2Img g2L g2L_one g2L_three g2L_zero g2L_zero_eq_img g2L_one_mul_three g2Img_mem_range g2L_mem_normalizer g2_derived_eq_range adjointGroup_G2_eq g2Hom_of u33GenPG_of g2Hom_injective two_eq_zero_of_card_two eq_zero_or_eq_one_of_card_two) in
theorem burnsideF4c_rootSubgroup_le_posUnipotent
    {root : Fin 2 → ℤ} (hroot : IsRoot Tag.G2 root)
    (hpos : 0 < height (τ := Tag.G2) root) :
    CFSG.Blueprint.Chevalley.rootSubgroup Tag.G2 K root ≤ posUnipotent Tag.G2 K :=
  le_iSup₂_of_le (f := fun α (_ : α ∈ {α : Fin Tag.G2.rank → ℤ | IsRoot Tag.G2 α ∧ 0 < height (τ := Tag.G2) α}) =>
    CFSG.Blueprint.Chevalley.rootSubgroup Tag.G2 K α) root ⟨hroot, hpos⟩ le_rfl

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisExc in
open CFSG.Quasithin (isSimpleGroup_u33Pres u33GenP u33PresHom u33PresHom_genPG card_u33Pres u33_orders u33_syl g2HomC g2RhoC g2IndexTwoData g2HomC_injective finite_g2Group G2Group U33G u33GenPG u33Data u33Extra g2Hom g2Img g2L g2L_one g2L_three g2L_zero g2L_zero_eq_img g2L_one_mul_three g2Img_mem_range g2L_mem_normalizer g2_derived_eq_range adjointGroup_G2_eq g2Hom_of u33GenPG_of g2Hom_injective two_eq_zero_of_card_two eq_zero_or_eq_one_of_card_two) in
theorem burnsideF4c_map_positiveBorel
    [Finite K] (hK : Nat.card K = 2) :
    (G2Native.positiveBorel K).map (adjointGroup Tag.G2 K).subtype =
      posUnipotent Tag.G2 K := by
  have hk2 : ∀ c : K, c = 0 ∨ c = 1 := CFSG.Quasithin.eq_zero_or_eq_one_of_card_two hK
  apply le_antisymm
  · rw [Subgroup.map_le_iff_le_comap]
    refine (Subgroup.closure_le _).2 ?_
    rintro x (⟨i, u, hu⟩ | ⟨root, hpos, hx⟩)
    · have hu1 : u = 1 := by
        refine Units.ext ?_
        rcases hk2 (u : K) with h | h
        · exact absurd h u.ne_zero
        · exact h
      subst hu1
      have hx1 : (x : ModGL Tag.G2 K) = torusElt Tag.G2 K i 1 := Units.ext hu
      have hx2 : (x : ModGL Tag.G2 K) = 1 := hx1.trans (burnsideF4c_torusElt_one i)
      have hx3 : x = 1 := Subtype.ext hx2
      rw [hx3]
      exact Subgroup.one_mem _
    · have hroot := burnsideF4c_isRoot_of_mem_rootGenerators hx
      obtain ⟨c, hc⟩ := (burnsideF4c_mem_rootGenerators hroot x).1 hx
      show (x : ModGL Tag.G2 K) ∈ posUnipotent Tag.G2 K
      rw [hc]
      exact burnsideF4c_rootSubgroup_le_posUnipotent hroot hpos (mem_rootSubgroup.2 ⟨c, rfl⟩)
  · refine iSup₂_le fun α hα => ?_
    refine (Subgroup.closure_le _).2 ?_
    rintro _ ⟨c, rfl⟩
    refine ⟨⟨pinnedX Tag.G2 K α c, pinnedX_mem_adjointGroup α c⟩, ?_, rfl⟩
    refine Subgroup.subset_closure (Or.inr ⟨α, hα.2, ?_⟩)
    exact (burnsideF4c_mem_rootGenerators hα.1 _).2 ⟨c, rfl⟩

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisExc in
open CFSG.Quasithin (isSimpleGroup_u33Pres u33GenP u33PresHom u33PresHom_genPG card_u33Pres u33_orders u33_syl g2HomC g2RhoC g2IndexTwoData g2HomC_injective finite_g2Group G2Group U33G u33GenPG u33Data u33Extra g2Hom g2Img g2L g2L_one g2L_three g2L_zero g2L_zero_eq_img g2L_one_mul_three g2Img_mem_range g2L_mem_normalizer g2_derived_eq_range adjointGroup_G2_eq g2Hom_of u33GenPG_of g2Hom_injective two_eq_zero_of_card_two eq_zero_or_eq_one_of_card_two) in
theorem burnsideF4c_map_rootSubgroup
    {root : Fin 2 → ℤ} (hroot : IsRoot Tag.G2 root) :
    (G2Native.rootSubgroup K root).map (adjointGroup Tag.G2 K).subtype =
      CFSG.Blueprint.Chevalley.rootSubgroup Tag.G2 K root := by
  unfold G2Native.rootSubgroup CFSG.Blueprint.Chevalley.rootSubgroup
  rw [MonoidHom.map_closure]
  congr 1
  ext g
  constructor
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨c, hc⟩ := (burnsideF4c_mem_rootGenerators hroot x).1 hx
    exact ⟨c, hc.symm⟩
  · rintro ⟨c, rfl⟩
    exact ⟨⟨pinnedX Tag.G2 K root c, pinnedX_mem_adjointGroup (τ := Tag.G2) root c⟩,
      (burnsideF4c_mem_rootGenerators hroot _).2 ⟨c, rfl⟩, rfl⟩

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisExc in
open CFSG.Quasithin (isSimpleGroup_u33Pres u33GenP u33PresHom u33PresHom_genPG card_u33Pres u33_orders u33_syl g2HomC g2RhoC g2IndexTwoData g2HomC_injective finite_g2Group G2Group U33G u33GenPG u33Data u33Extra g2Hom g2Img g2L g2L_one g2L_three g2L_zero g2L_zero_eq_img g2L_one_mul_three g2Img_mem_range g2L_mem_normalizer g2_derived_eq_range adjointGroup_G2_eq g2Hom_of u33GenPG_of g2Hom_injective two_eq_zero_of_card_two eq_zero_or_eq_one_of_card_two) in
theorem burnsideF4c_map_pointParabolic
    [Finite K] (hK : Nat.card K = 2) :
    (G2Native.pointParabolic K).map (adjointGroup Tag.G2 K).subtype =
      posUnipotent Tag.G2 K ⊔
        CFSG.Blueprint.Chevalley.rootSubgroup Tag.G2 K (-Pi.single (1 : Fin 2) 1) := by
  unfold G2Native.pointParabolic
  rw [Subgroup.map_sup, burnsideF4c_map_positiveBorel hK]
  congr 1
  exact burnsideF4c_map_rootSubgroup (isRoot_neg_single Tag.G2 (1 : Fin 2))

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisExc in
open CFSG.Quasithin (isSimpleGroup_u33Pres u33GenP u33PresHom u33PresHom_genPG card_u33Pres u33_orders u33_syl g2HomC g2RhoC g2IndexTwoData g2HomC_injective finite_g2Group G2Group U33G u33GenPG u33Data u33Extra g2Hom g2Img g2L g2L_one g2L_three g2L_zero g2L_zero_eq_img g2L_one_mul_three g2Img_mem_range g2L_mem_normalizer g2_derived_eq_range adjointGroup_G2_eq g2Hom_of u33GenPG_of g2Hom_injective two_eq_zero_of_card_two eq_zero_or_eq_one_of_card_two) in
theorem burnsideF4c_card_positiveBorel
    [Finite K] (hK : Nat.card K = 2) :
    Nat.card (G2Native.positiveBorel K) = 64 := by
  have h1 := burnsideF4c_map_positiveBorel hK
  have h2 : Nat.card ((G2Native.positiveBorel K).map (adjointGroup Tag.G2 K).subtype) =
      Nat.card (G2Native.positiveBorel K) :=
    Subgroup.card_map_of_injective (adjointGroup Tag.G2 K).subtype_injective
  rw [← h2, h1, card_posUnipotent, hK, CFSG.Timmesfeld.ExceptionalOrders.ncard_posRoots_G2]
  norm_num

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisExc in
open CFSG.Quasithin (isSimpleGroup_u33Pres u33GenP u33PresHom u33PresHom_genPG card_u33Pres u33_orders u33_syl g2HomC g2RhoC g2IndexTwoData g2HomC_injective finite_g2Group G2Group U33G u33GenPG u33Data u33Extra g2Hom g2Img g2L g2L_one g2L_three g2L_zero g2L_zero_eq_img g2L_one_mul_three g2Img_mem_range g2L_mem_normalizer g2_derived_eq_range adjointGroup_G2_eq g2Hom_of u33GenPG_of g2Hom_injective two_eq_zero_of_card_two eq_zero_or_eq_one_of_card_two) in
theorem burnsideF4c_card_le_two_mul {G : Type*} [Group G] (U R : Subgroup G) (ρ : G)
    (hcov : ∀ g : G, g ∈ R ∨ g * ρ ∈ R) [Finite U] :
    Nat.card U ≤ 2 * Nat.card ↥(R ⊓ U) := by
  have hdvd : R.relIndex U ∣ 2 := by
    rw [Subgroup.relIndex_dvd_two_iff]
    by_cases hU : U ≤ R
    · exact ⟨1, U.one_mem, fun b hb => Or.inr (hU hb)⟩
    · obtain ⟨a₀, ha₀U, ha₀R⟩ := SetLike.not_le_iff_exists.1 hU
      refine ⟨a₀⁻¹, U.inv_mem ha₀U, fun b hb => ?_⟩
      by_cases hbR : b ∈ R
      · exact Or.inr hbR
      · refine Or.inl ?_
        have h1 : b * ρ ∈ R := (hcov b).resolve_left hbR
        have h2 : a₀ * ρ ∈ R := (hcov a₀).resolve_left ha₀R
        have := R.mul_mem h1 (R.inv_mem h2)
        simpa [mul_assoc] using this
  have hle : R.relIndex U ≤ 2 := Nat.le_of_dvd (by norm_num) hdvd
  have hmul := Subgroup.relIndex_mul_card (H := R) (K := U)
  calc Nat.card U = R.relIndex U * Nat.card ↥(R ⊓ U) := hmul.symm
    _ ≤ 2 * Nat.card ↥(R ⊓ U) := Nat.mul_le_mul_right _ hle

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisExc in
open CFSG.Quasithin (isSimpleGroup_u33Pres u33GenP u33PresHom u33PresHom_genPG card_u33Pres u33_orders u33_syl g2HomC g2RhoC g2IndexTwoData g2HomC_injective finite_g2Group G2Group U33G u33GenPG u33Data u33Extra g2Hom g2Img g2L g2L_one g2L_three g2L_zero g2L_zero_eq_img g2L_one_mul_three g2Img_mem_range g2L_mem_normalizer g2_derived_eq_range adjointGroup_G2_eq g2Hom_of u33GenPG_of g2Hom_injective two_eq_zero_of_card_two eq_zero_or_eq_one_of_card_two) in
theorem burnsideF4c_Sg_syl
    [Finite K] (hK : Nat.card K = 2) (h2 : (2 : K) = 0)
    (hk2 : ∀ c : K, c = 0 ∨ c = 1) :
    IsPGroup 2 ((G2Native.positiveBorel K).comap (g2HomC h2)) ∧
      32 ≤ Nat.card ((G2Native.positiveBorel K).comap (g2HomC h2)) := by
  haveI : Finite (G2Group K) := finite_g2Group
  have hU : IsPGroup 2 (G2Native.positiveBorel K) :=
    IsPGroup.of_card (n := 6) (by rw [burnsideF4c_card_positiveBorel hK]; norm_num)
  have hinj := g2HomC_injective h2
  refine ⟨?_, ?_⟩
  · refine hU.of_injective
      (((g2HomC h2).comp ((G2Native.positiveBorel K).comap (g2HomC h2)).subtype).codRestrict
        (G2Native.positiveBorel K) (fun g => g.2)) ?_
    intro a b hab
    apply Subtype.ext
    apply hinj
    exact congrArg Subtype.val hab
  · have hmap : Nat.card (((G2Native.positiveBorel K).comap (g2HomC h2)).map (g2HomC h2)) =
        Nat.card ((G2Native.positiveBorel K).comap (g2HomC h2)) :=
      Subgroup.card_map_of_injective hinj
    have hcov := fun g : G2Group K => (g2IndexTwoData h2 hk2).cover g
    have h64 : Nat.card (G2Native.positiveBorel K) ≤
        2 * Nat.card ↥((g2HomC h2).range ⊓ G2Native.positiveBorel K) :=
      burnsideF4c_card_le_two_mul (G2Native.positiveBorel K) (g2HomC h2).range (g2RhoC h2) hcov
    rw [burnsideF4c_card_positiveBorel hK] at h64
    have hm : Nat.card ↥((g2HomC h2).range ⊓ G2Native.positiveBorel K) =
        Nat.card ((G2Native.positiveBorel K).comap (g2HomC h2)) := by
      rw [← hmap, Subgroup.map_comap_eq]
    rw [hm] at h64
    omega

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisExc in
open CFSG.Quasithin (isSimpleGroup_u33Pres u33GenP u33PresHom u33PresHom_genPG card_u33Pres u33_orders u33_syl g2HomC g2RhoC g2IndexTwoData g2HomC_injective finite_g2Group G2Group U33G u33GenPG u33Data u33Extra g2Hom g2Img g2L g2L_one g2L_three g2L_zero g2L_zero_eq_img g2L_one_mul_three g2Img_mem_range g2L_mem_normalizer g2_derived_eq_range adjointGroup_G2_eq g2Hom_of u33GenPG_of g2Hom_injective two_eq_zero_of_card_two eq_zero_or_eq_one_of_card_two) in
theorem burnsideF4c_phi_y
    (h2 : (2 : K) = 0) :
    ((g2HomC h2 (u33GenPG 4) : G2Group K) : ModGL Tag.G2 K) =
      xUnit Tag.G2 K (1 : Fin 2) 1 * yUnit Tag.G2 K (1 : Fin 2) 1 := by
  have e0 : u33GenPG 4 = PresentedGroup.of (4 : Fin 5) := u33GenPG_of 4
  have e1 : ((g2HomC h2 (u33GenPG 4) : G2Group K) : ModGL Tag.G2 K) =
      g2Hom h2 (u33GenPG 4) := rfl
  have e2 : g2Hom h2 (u33GenPG 4) = g2L 1 * g2L 3 := by
    rw [e0, g2Hom_of]
    exact g2L_one_mul_three.symm
  have e3 : (g2L 1 : ModGL Tag.G2 K) * g2L 3 =
      xUnit Tag.G2 K (1 : Fin 2) 1 * yUnit Tag.G2 K (1 : Fin 2) 1 := by
    rw [g2L_one, g2L_three]; rfl
  exact e1.trans (e2.trans e3)

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisExc in
open CFSG.Quasithin (isSimpleGroup_u33Pres u33GenP u33PresHom u33PresHom_genPG card_u33Pres u33_orders u33_syl g2HomC g2RhoC g2IndexTwoData g2HomC_injective finite_g2Group G2Group U33G u33GenPG u33Data u33Extra g2Hom g2Img g2L g2L_one g2L_three g2L_zero g2L_zero_eq_img g2L_one_mul_three g2Img_mem_range g2L_mem_normalizer g2_derived_eq_range adjointGroup_G2_eq g2Hom_of u33GenPG_of g2Hom_injective two_eq_zero_of_card_two eq_zero_or_eq_one_of_card_two) in
theorem burnsideF4c_y_mem
    [Finite K] (hK : Nat.card K = 2) (h2 : (2 : K) = 0) :
    u33GenPG 4 ∈ (G2Native.pointParabolic K).comap (g2HomC h2) := by
  rw [Subgroup.mem_comap]
  suffices h : ((g2HomC h2 (u33GenPG 4) : G2Group K) : ModGL Tag.G2 K) ∈
      (G2Native.pointParabolic K).map (adjointGroup Tag.G2 K).subtype by
    obtain ⟨x, hx, hxe⟩ := h
    have : x = g2HomC h2 (u33GenPG 4) := Subtype.ext hxe
    rwa [this] at hx
  rw [burnsideF4c_map_pointParabolic hK, burnsideF4c_phi_y h2]
  refine Subgroup.mul_mem_sup ?_ ?_
  · rw [← pinnedX_single (τ := Tag.G2) (R := K) (1 : Fin 2) 1]
    refine burnsideF4c_rootSubgroup_le_posUnipotent (isRoot_single Tag.G2 (1 : Fin 2)) ?_
      (mem_rootSubgroup.2 ⟨1, rfl⟩)
    show 0 < height (τ := Tag.G2) (Pi.single (1 : Fin 2) 1)
    decide +kernel
  · rw [← pinnedX_neg_single (τ := Tag.G2) (R := K) (1 : Fin 2) 1]
    exact mem_rootSubgroup.2 ⟨1, rfl⟩

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisExc in
open CFSG.Quasithin (isSimpleGroup_u33Pres u33GenP u33PresHom u33PresHom_genPG card_u33Pres u33_orders u33_syl g2HomC g2RhoC g2IndexTwoData g2HomC_injective finite_g2Group G2Group U33G u33GenPG u33Data u33Extra g2Hom g2Img g2L g2L_one g2L_three g2L_zero g2L_zero_eq_img g2L_one_mul_three g2Img_mem_range g2L_mem_normalizer g2_derived_eq_range adjointGroup_G2_eq g2Hom_of u33GenPG_of g2Hom_injective two_eq_zero_of_card_two eq_zero_or_eq_one_of_card_two) in
theorem burnsideF4c_le_Pg
    [Finite K] (h2 : (2 : K) = 0) :
    (G2Native.positiveBorel K).comap (g2HomC h2) ≤ (G2Native.pointParabolic K).comap (g2HomC h2) :=
  Subgroup.comap_mono le_sup_left

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisExc in
open CFSG.Quasithin (isSimpleGroup_u33Pres u33GenP u33PresHom u33PresHom_genPG card_u33Pres u33_orders u33_syl g2HomC g2RhoC g2IndexTwoData g2HomC_injective finite_g2Group G2Group U33G u33GenPG u33Data u33Extra g2Hom g2Img g2L g2L_one g2L_three g2L_zero g2L_zero_eq_img g2L_one_mul_three g2Img_mem_range g2L_mem_normalizer g2_derived_eq_range adjointGroup_G2_eq g2Hom_of u33GenPG_of g2Hom_injective two_eq_zero_of_card_two eq_zero_or_eq_one_of_card_two) in
theorem burnsideF4c_posRoot_cases
    {α : Fin Tag.G2.rank → ℤ} (hα : IsRoot Tag.G2 α)
    (hpos : 0 < height (τ := Tag.G2) α) :
    α = ![1, 0] ∨ α = ![0, 1] ∨ α = ![1, 1] ∨ α = ![1, 2] ∨ α = ![1, 3] ∨ α = ![2, 3] := by
  have key : ∀ k < 12, 0 < height (τ := Tag.G2) (Tag.G2.rootCertificate.root k) →
      List.ofFn (Tag.G2.rootCertificate.root k) = [1, 0] ∨
        List.ofFn (Tag.G2.rootCertificate.root k) = [0, 1] ∨
        List.ofFn (Tag.G2.rootCertificate.root k) = [1, 1] ∨
        List.ofFn (Tag.G2.rootCertificate.root k) = [1, 2] ∨
        List.ofFn (Tag.G2.rootCertificate.root k) = [1, 3] ∨
        List.ofFn (Tag.G2.rootCertificate.root k) = [2, 3] := by
    decide +kernel
  obtain ⟨k, hk, rfl⟩ := (Tag.G2.rootCertificate.isRoot_iff (Tag.rootCertificate_check Tag.G2)).1 hα
  rcases key k hk hpos with h | h | h | h | h | h
  · exact Or.inl (List.ofFn_injective (h.trans (by decide)))
  · exact Or.inr (Or.inl (List.ofFn_injective (h.trans (by decide))))
  · exact Or.inr (Or.inr (Or.inl (List.ofFn_injective (h.trans (by decide)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inl (List.ofFn_injective (h.trans (by decide))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (List.ofFn_injective (h.trans (by decide)))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (List.ofFn_injective (h.trans (by decide)))))))

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisExc in
open CFSG.Quasithin (isSimpleGroup_u33Pres u33GenP u33PresHom u33PresHom_genPG card_u33Pres u33_orders u33_syl g2HomC g2RhoC g2IndexTwoData g2HomC_injective finite_g2Group G2Group U33G u33GenPG u33Data u33Extra g2Hom g2Img g2L g2L_one g2L_three g2L_zero g2L_zero_eq_img g2L_one_mul_three g2Img_mem_range g2L_mem_normalizer g2_derived_eq_range adjointGroup_G2_eq g2Hom_of u33GenPG_of g2Hom_injective two_eq_zero_of_card_two eq_zero_or_eq_one_of_card_two) in
theorem burnsideF4c_cRoot_isRoot : IsRoot Tag.G2 ![2, 3] := by
  have h : IsRoot Tag.G2 (reflect Tag.G2 (0 : Fin 2) (reflect Tag.G2 (1 : Fin 2)
      (Pi.single (0 : Fin 2) 1))) :=
    IsRoot.reflect (τ := Tag.G2) (0 : Fin 2) (IsRoot.reflect (τ := Tag.G2) (1 : Fin 2)
      (IsRoot.basis (τ := Tag.G2) (0 : Fin 2)))
  have e : reflect Tag.G2 (0 : Fin 2) (reflect Tag.G2 (1 : Fin 2) (Pi.single (0 : Fin 2) 1)) =
      ![2, 3] := List.ofFn_injective (by decide +kernel)
  rwa [e] at h

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisExc in
open CFSG.Quasithin (isSimpleGroup_u33Pres u33GenP u33PresHom u33PresHom_genPG card_u33Pres u33_orders u33_syl g2HomC g2RhoC g2IndexTwoData g2HomC_injective finite_g2Group G2Group U33G u33GenPG u33Data u33Extra g2Hom g2Img g2L g2L_one g2L_three g2L_zero g2L_zero_eq_img g2L_one_mul_three g2Img_mem_range g2L_mem_normalizer g2_derived_eq_range adjointGroup_G2_eq g2Hom_of u33GenPG_of g2Hom_injective two_eq_zero_of_card_two eq_zero_or_eq_one_of_card_two) in
theorem burnsideF4c_commute_cRoot
    {α : Fin Tag.G2.rank → ℤ} (hα : IsRoot Tag.G2 α)
    (hpos : 0 < height (τ := Tag.G2) α) (x : K) :
    pinnedX Tag.G2 K α x * pinnedX Tag.G2 K ![2, 3] 1 =
      pinnedX Tag.G2 K ![2, 3] 1 * pinnedX Tag.G2 K α x := by
  have T := g2_even_root_commutator_table (R := K) x 1
  rcases burnsideF4c_posRoot_cases hα hpos with rfl | rfl | rfl | rfl | rfl | rfl
  · exact T.2.2.2.2.2.2.2.2.1
  · exact T.2.2.2.2.2.2.2.2.2.2.1
  · exact T.2.2.2.2.2.2.2.2.2.2.2.2.1
  · exact T.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  · exact T.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  · have h1 := pinnedX_add Tag.G2 K ![2, 3] x 1
    have h2 := pinnedX_add Tag.G2 K ![2, 3] 1 x
    exact h1.symm.trans ((congrArg (pinnedX Tag.G2 K ![2, 3]) (add_comm x 1)).trans h2)

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisExc in
open CFSG.Quasithin (isSimpleGroup_u33Pres u33GenP u33PresHom u33PresHom_genPG card_u33Pres u33_orders u33_syl g2HomC g2RhoC g2IndexTwoData g2HomC_injective finite_g2Group G2Group U33G u33GenPG u33Data u33Extra g2Hom g2Img g2L g2L_one g2L_three g2L_zero g2L_zero_eq_img g2L_one_mul_three g2Img_mem_range g2L_mem_normalizer g2_derived_eq_range adjointGroup_G2_eq g2Hom_of u33GenPG_of g2Hom_injective two_eq_zero_of_card_two eq_zero_or_eq_one_of_card_two) in
theorem burnsideF4c_commute_negr
    (y : K) :
    pinnedX Tag.G2 K (-Pi.single (1 : Fin 2) 1) y * pinnedX Tag.G2 K ![2, 3] 1 =
      pinnedX Tag.G2 K ![2, 3] 1 * pinnedX Tag.G2 K (-Pi.single (1 : Fin 2) 1) y := by
  have hc : IsRoot Tag.G2 ![2, 3] := burnsideF4c_cRoot_isRoot
  have hr : IsRoot Tag.G2 (-Pi.single (1 : Fin 2) 1) := isRoot_neg_single Tag.G2 (1 : Fin 2)
  have h1 : weylElt Tag.G2 K (1 : Fin 2) 1 * pinnedX Tag.G2 K ![2, 3] 1 *
      (weylElt Tag.G2 K (1 : Fin 2) 1)⁻¹ = pinnedX Tag.G2 K ![2, 3] 1 := by
    have := nC_conj_pinnedX (τ := Tag.G2) (K := K) (1 : Fin 2) hc 1
    have e : reflect Tag.G2 (1 : Fin 2) ![2, 3] = ![2, 3] :=
      List.ofFn_injective (by decide +kernel)
    rwa [e] at this
  have h2 : weylElt Tag.G2 K (1 : Fin 2) 1 * pinnedX Tag.G2 K (-Pi.single (1 : Fin 2) 1) y *
      (weylElt Tag.G2 K (1 : Fin 2) 1)⁻¹ = pinnedX Tag.G2 K ![0, 1] y := by
    have := nC_conj_pinnedX (τ := Tag.G2) (K := K) (1 : Fin 2) hr y
    have e : reflect Tag.G2 (1 : Fin 2) (-Pi.single (1 : Fin 2) 1) = ![0, 1] :=
      List.ofFn_injective (by decide +kernel)
    rwa [e] at this
  have h3 : pinnedX Tag.G2 K ![0, 1] y * pinnedX Tag.G2 K ![2, 3] 1 =
      pinnedX Tag.G2 K ![2, 3] 1 * pinnedX Tag.G2 K ![0, 1] y := by
    have T := g2_even_root_commutator_table (R := K) y 1
    exact T.2.2.2.2.2.2.2.2.2.2.1
  have h4 : weylElt Tag.G2 K (1 : Fin 2) 1 * (pinnedX Tag.G2 K (-Pi.single (1 : Fin 2) 1) y *
        pinnedX Tag.G2 K ![2, 3] 1) * (weylElt Tag.G2 K (1 : Fin 2) 1)⁻¹ =
      weylElt Tag.G2 K (1 : Fin 2) 1 * (pinnedX Tag.G2 K ![2, 3] 1 *
        pinnedX Tag.G2 K (-Pi.single (1 : Fin 2) 1) y) * (weylElt Tag.G2 K (1 : Fin 2) 1)⁻¹ := by
    calc _ = (weylElt Tag.G2 K (1 : Fin 2) 1 * pinnedX Tag.G2 K (-Pi.single (1 : Fin 2) 1) y *
          (weylElt Tag.G2 K (1 : Fin 2) 1)⁻¹) * (weylElt Tag.G2 K (1 : Fin 2) 1 *
          pinnedX Tag.G2 K ![2, 3] 1 * (weylElt Tag.G2 K (1 : Fin 2) 1)⁻¹) := by group
      _ = pinnedX Tag.G2 K ![0, 1] y * pinnedX Tag.G2 K ![2, 3] 1 := by rw [h2, h1]
      _ = pinnedX Tag.G2 K ![2, 3] 1 * pinnedX Tag.G2 K ![0, 1] y := h3
      _ = (weylElt Tag.G2 K (1 : Fin 2) 1 * pinnedX Tag.G2 K ![2, 3] 1 *
          (weylElt Tag.G2 K (1 : Fin 2) 1)⁻¹) * (weylElt Tag.G2 K (1 : Fin 2) 1 *
          pinnedX Tag.G2 K (-Pi.single (1 : Fin 2) 1) y * (weylElt Tag.G2 K (1 : Fin 2) 1)⁻¹) := by
        rw [h1, h2]
      _ = _ := by group
  exact mul_left_cancel (mul_right_cancel h4)

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisExc in
open CFSG.Quasithin (isSimpleGroup_u33Pres u33GenP u33PresHom u33PresHom_genPG card_u33Pres u33_orders u33_syl g2HomC g2RhoC g2IndexTwoData g2HomC_injective finite_g2Group G2Group U33G u33GenPG u33Data u33Extra g2Hom g2Img g2L g2L_one g2L_three g2L_zero g2L_zero_eq_img g2L_one_mul_three g2Img_mem_range g2L_mem_normalizer g2_derived_eq_range adjointGroup_G2_eq g2Hom_of u33GenPG_of g2Hom_injective two_eq_zero_of_card_two eq_zero_or_eq_one_of_card_two) in
theorem burnsideF4c_adj_le_normalizer
    (h2 : (2 : K) = 0) (hk2 : ∀ c : K, c = 0 ∨ c = 1) :
    adjointGroup Tag.G2 K ≤ Subgroup.normalizer ((g2Hom h2).range : Set (ModGL Tag.G2 K)) := by
  rw [adjointGroup_G2_eq hk2]
  refine (Subgroup.closure_le _).2 ?_
  rintro g (rfl | ⟨t, rfl⟩)
  · exact (Subgroup.normalizer _).one_mem
  · exact g2L_mem_normalizer h2 t.2

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisExc in
open CFSG.Quasithin (isSimpleGroup_u33Pres u33GenP u33PresHom u33PresHom_genPG card_u33Pres u33_orders u33_syl g2HomC g2RhoC g2IndexTwoData g2HomC_injective finite_g2Group G2Group U33G u33GenPG u33Data u33Extra g2Hom g2Img g2L g2L_one g2L_three g2L_zero g2L_zero_eq_img g2L_one_mul_three g2Img_mem_range g2L_mem_normalizer g2_derived_eq_range adjointGroup_G2_eq g2Hom_of u33GenPG_of g2Hom_injective two_eq_zero_of_card_two eq_zero_or_eq_one_of_card_two) in
theorem burnsideF4c_x0_mem
    (h2 : (2 : K) = 0) :
    xUnit Tag.G2 K (0 : Fin 2) 1 ∈ (g2Hom h2).range := by
  have h := g2Img_mem_range h2 (2 : Fin 5)
  rw [← g2L_zero_eq_img, g2L_zero] at h
  exact h

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisExc in
open CFSG.Quasithin (isSimpleGroup_u33Pres u33GenP u33PresHom u33PresHom_genPG card_u33Pres u33_orders u33_syl g2HomC g2RhoC g2IndexTwoData g2HomC_injective finite_g2Group G2Group U33G u33GenPG u33Data u33Extra g2Hom g2Img g2L g2L_one g2L_three g2L_zero g2L_zero_eq_img g2L_one_mul_three g2Img_mem_range g2L_mem_normalizer g2_derived_eq_range adjointGroup_G2_eq g2Hom_of u33GenPG_of g2Hom_injective two_eq_zero_of_card_two eq_zero_or_eq_one_of_card_two) in
theorem burnsideF4c_z_mem_range
    (h2 : (2 : K) = 0) (hk2 : ∀ c : K, c = 0 ∨ c = 1) :
    pinnedX Tag.G2 K ![2, 3] 1 ∈ (g2Hom h2).range := by
  have hw := (burnsideF4c_wU_one_conj (K := K) [1, 0] 0 1).2
  have e : burnsideF4c_reflW [1, 0] (Pi.single (0 : Fin 2) 1) = ![2, 3] :=
    List.ofFn_injective (by decide +kernel)
  rw [e, pinnedX_single (τ := Tag.G2) (R := K) (0 : Fin 2) 1] at hw
  rw [← hw]
  have hN := burnsideF4c_adj_le_normalizer h2 hk2
    (burnsideF4c_wU_mem [1, 0] 1 (Subgroup.one_mem _))
  exact (Subgroup.mem_normalizer_iff.1 hN _).1 (burnsideF4c_x0_mem h2)

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisExc in
open CFSG.Quasithin (isSimpleGroup_u33Pres u33GenP u33PresHom u33PresHom_genPG card_u33Pres u33_orders u33_syl g2HomC g2RhoC g2IndexTwoData g2HomC_injective finite_g2Group G2Group U33G u33GenPG u33Data u33Extra g2Hom g2Img g2L g2L_one g2L_three g2L_zero g2L_zero_eq_img g2L_one_mul_three g2Img_mem_range g2L_mem_normalizer g2_derived_eq_range adjointGroup_G2_eq g2Hom_of u33GenPG_of g2Hom_injective two_eq_zero_of_card_two eq_zero_or_eq_one_of_card_two) in
theorem burnsideF4c_exists_z
    (h2 : (2 : K) = 0) (hk2 : ∀ c : K, c = 0 ∨ c = 1) :
    ∃ z : U33G, z ≠ 1 ∧ z * z = 1 ∧ g2Hom h2 z = pinnedX Tag.G2 K ![2, 3] 1 := by
  obtain ⟨z, hz⟩ := burnsideF4c_z_mem_range h2 hk2
  refine ⟨z, ?_, ?_, hz⟩
  · intro h1
    rw [h1, map_one] at hz
    have h0 : pinnedX Tag.G2 K ![2, 3] 0 = pinnedX Tag.G2 K ![2, 3] 1 :=
      (pinnedX_zero Tag.G2 K ![2, 3]).trans hz
    exact zero_ne_one (pinnedX_injective Tag.G2 K _ h0)
  · apply g2Hom_injective h2
    have h11 : (1 : K) + 1 = 0 := by rw [one_add_one_eq_two]; exact h2
    calc g2Hom h2 (z * z) = g2Hom h2 z * g2Hom h2 z := map_mul _ _ _
      _ = pinnedX Tag.G2 K ![2, 3] 1 * pinnedX Tag.G2 K ![2, 3] 1 := by rw [hz]
      _ = pinnedX Tag.G2 K ![2, 3] (1 + 1) := (pinnedX_add Tag.G2 K ![2, 3] 1 1).symm
      _ = pinnedX Tag.G2 K ![2, 3] 0 := congrArg (pinnedX Tag.G2 K ![2, 3]) h11
      _ = 1 := pinnedX_zero Tag.G2 K ![2, 3]
      _ = g2Hom h2 1 := (map_one _).symm

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisExc in
open CFSG.Quasithin (isSimpleGroup_u33Pres u33GenP u33PresHom u33PresHom_genPG card_u33Pres u33_orders u33_syl g2HomC g2RhoC g2IndexTwoData g2HomC_injective finite_g2Group G2Group U33G u33GenPG u33Data u33Extra g2Hom g2Img g2L g2L_one g2L_three g2L_zero g2L_zero_eq_img g2L_one_mul_three g2Img_mem_range g2L_mem_normalizer g2_derived_eq_range adjointGroup_G2_eq g2Hom_of u33GenPG_of g2Hom_injective two_eq_zero_of_card_two eq_zero_or_eq_one_of_card_two) in
theorem burnsideF4c_Pg_comm
    [Finite K] (hK : Nat.card K = 2) (h2 : (2 : K) = 0)
    (z : U33G) (hz : g2Hom h2 z = pinnedX Tag.G2 K ![2, 3] 1) :
    ∀ p ∈ (G2Native.pointParabolic K).comap (g2HomC h2), p * z = z * p := by
  intro p hp
  apply g2Hom_injective h2
  rw [map_mul, map_mul, hz]
  have hP : (g2Hom h2 p : ModGL Tag.G2 K) ∈
      posUnipotent Tag.G2 K ⊔
        CFSG.Blueprint.Chevalley.rootSubgroup Tag.G2 K (-Pi.single (1 : Fin 2) 1) := by
    have h : ((g2HomC h2 p : G2Group K) : ModGL Tag.G2 K) ∈
        (G2Native.pointParabolic K).map (adjointGroup Tag.G2 K).subtype := ⟨_, hp, rfl⟩
    rw [burnsideF4c_map_pointParabolic hK] at h
    exact h
  have hC : posUnipotent Tag.G2 K ⊔
      CFSG.Blueprint.Chevalley.rootSubgroup Tag.G2 K (-Pi.single (1 : Fin 2) 1) ≤
      Subgroup.centralizer ({pinnedX Tag.G2 K ![2, 3] 1} : Set (ModGL Tag.G2 K)) := by
    refine sup_le ?_ ?_
    · refine iSup₂_le fun α hα => (Subgroup.closure_le _).2 ?_
      rintro _ ⟨x, rfl⟩
      rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
      rintro h rfl
      exact (burnsideF4c_commute_cRoot hα.1 hα.2 x).symm
    · refine (Subgroup.closure_le _).2 ?_
      rintro _ ⟨x, rfl⟩
      rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
      rintro h rfl
      exact (burnsideF4c_commute_negr x).symm
  have hmem := hC hP
  exact (Subgroup.mem_centralizer_iff.1 hmem _ rfl).symm

end G2Bridge

section Transport

variable {G H : Type*} [Group G] [Group H]

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisExc in
open CFSG.Quasithin (isSimpleGroup_u33Pres u33GenP u33PresHom u33PresHom_genPG card_u33Pres u33_orders u33_syl g2HomC g2RhoC g2IndexTwoData g2HomC_injective finite_g2Group G2Group U33G u33GenPG u33Data u33Extra g2Hom g2Img g2L g2L_one g2L_three g2L_zero g2L_zero_eq_img g2L_one_mul_three g2Img_mem_range g2L_mem_normalizer g2_derived_eq_range adjointGroup_G2_eq g2Hom_of u33GenPG_of g2Hom_injective two_eq_zero_of_card_two eq_zero_or_eq_one_of_card_two) in
theorem burnsideF4c_InvolInCore_map (f : G →* H) (hf : Function.Injective f) {P : Subgroup G}
    (hP : burnsideF4c_InvolInCore P) : burnsideF4c_InvolInCore (P.map f) := by
  obtain ⟨Q, hQP, hQn, hQp, hQi⟩ := hP
  refine ⟨Q.map f, Subgroup.map_mono hQP, ?_, hQp.map f, ?_⟩
  · rintro _ ⟨p, hp, rfl⟩
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · rintro ⟨q, hq, rfl⟩
      refine ⟨p * q * p⁻¹, (Subgroup.mem_normalizer_iff.1 (hQn hp) q).1 hq, ?_⟩
      simp
    · intro hy
      obtain ⟨q, hq, hqe⟩ := hy
      refine ⟨p⁻¹ * q * p, ?_, ?_⟩
      · have := (Subgroup.mem_normalizer_iff.1 (hQn (P.inv_mem hp)) q).1 hq
        simpa using this
      · have e : f q = f p * y * (f p)⁻¹ := hqe
        have e2 : y = (f p)⁻¹ * f q * f p := by rw [e]; group
        rw [e2]; simp
  · rintro _ ⟨s, hs, rfl⟩ h
    have hs2 : s * s = 1 := hf (by rw [map_mul, h, map_one])
    exact ⟨s, hQi s hs hs2, rfl⟩

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisExc in
open CFSG.Quasithin (isSimpleGroup_u33Pres u33GenP u33PresHom u33PresHom_genPG card_u33Pres u33_orders u33_syl g2HomC g2RhoC g2IndexTwoData g2HomC_injective finite_g2Group G2Group U33G u33GenPG u33Data u33Extra g2Hom g2Img g2L g2L_one g2L_three g2L_zero g2L_zero_eq_img g2L_one_mul_three g2Img_mem_range g2L_mem_normalizer g2_derived_eq_range adjointGroup_G2_eq g2Hom_of u33GenPG_of g2Hom_injective two_eq_zero_of_card_two eq_zero_or_eq_one_of_card_two) in
theorem burnsideF4c_InvolInCore_of_map (f : G →* H) (hf : Function.Injective f) {P : Subgroup G}
    (hP : burnsideF4c_InvolInCore (P.map f)) : burnsideF4c_InvolInCore P := by
  obtain ⟨Q, hQP, hQn, hQp, hQi⟩ := hP
  have hle : Q.comap f ≤ P := by
    intro x hx
    obtain ⟨p, hp, hpx⟩ := hQP hx
    have : p = x := hf hpx
    rwa [← this]
  refine ⟨Q.comap f, hle, ?_, hQp.comap_of_injective f hf, ?_⟩
  · intro p hp
    rw [Subgroup.mem_normalizer_iff]
    intro x
    have hfp : f p ∈ Subgroup.normalizer (Q : Set H) := hQn ⟨p, hp, rfl⟩
    have := Subgroup.mem_normalizer_iff.1 hfp (f x)
    simpa [Subgroup.mem_comap] using this
  · intro s hs h
    have : f s ∈ Q := hQi (f s) ⟨s, hs, rfl⟩ (by rw [← map_mul, h, map_one])
    exact this

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisExc in
open CFSG.Quasithin (isSimpleGroup_u33Pres u33GenP u33PresHom u33PresHom_genPG card_u33Pres u33_orders u33_syl g2HomC g2RhoC g2IndexTwoData g2HomC_injective finite_g2Group G2Group U33G u33GenPG u33Data u33Extra g2Hom g2Img g2L g2L_one g2L_three g2L_zero g2L_zero_eq_img g2L_one_mul_three g2Img_mem_range g2L_mem_normalizer g2_derived_eq_range adjointGroup_G2_eq g2Hom_of u33GenPG_of g2Hom_injective two_eq_zero_of_card_two eq_zero_or_eq_one_of_card_two) in
theorem burnsideF4c_involInCore_pCoreOf {E : Type} [Group E] {P : Subgroup E}
    (hP : burnsideF4c_InvolInCore P) : ∀ s ∈ P, s * s = 1 → s ∈ pCoreOf 2 P := by
  obtain ⟨Q, hQP, hQn, hQp, hQi⟩ := hP
  intro s hs hs2
  have hQ0 : Q.subgroupOf P ≤ pCore 2 ↥P := by
    refine le_sSup ⟨⟨fun x hx g => ?_⟩, hQp.comap_subtype⟩
    show ((g : E) * (x : E) * (g : E)⁻¹ ∈ Q)
    exact (Subgroup.mem_normalizer_iff.1 (hQn g.2) _).1 hx
  exact ⟨⟨s, hs⟩, hQ0 (show s ∈ Q from hQi s hs hs2), rfl⟩

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisExc in
open CFSG.Quasithin (isSimpleGroup_u33Pres u33GenP u33PresHom u33PresHom_genPG card_u33Pres u33_orders u33_syl g2HomC g2RhoC g2IndexTwoData g2HomC_injective finite_g2Group G2Group U33G u33GenPG u33Data u33Extra g2Hom g2Img g2L g2L_one g2L_three g2L_zero g2L_zero_eq_img g2L_one_mul_three g2Img_mem_range g2L_mem_normalizer g2_derived_eq_range adjointGroup_G2_eq g2Hom_of u33GenPG_of g2Hom_injective two_eq_zero_of_card_two eq_zero_or_eq_one_of_card_two) in
open scoped Pointwise in
theorem burnsideF4c_sylow_conj [Finite G] (S T : Subgroup G)
    (hS : IsPGroup 2 S) (hSi : ¬ 2 ∣ S.index) (hT : IsPGroup 2 T) (hTi : ¬ 2 ∣ T.index) :
    ∃ h : G, ∀ g : G, g ∈ T ↔ ∃ s ∈ S, h * s * h⁻¹ = g := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let S' : Sylow 2 G := hS.toSylow hSi
  let T' : Sylow 2 G := hT.toSylow hTi
  obtain ⟨h, hh⟩ := MulAction.exists_smul_eq G S' T'
  refine ⟨h, fun g => ?_⟩
  have hT' : (T : Subgroup G) = MulAut.conj h • S := by
    have := congrArg (fun P : Sylow 2 G => (P : Subgroup G)) hh
    simpa [Sylow.coe_subgroup_smul, S', T', IsPGroup.toSylow_coe] using this.symm
  rw [hT', Subgroup.mem_smul_pointwise_iff_exists]
  simp [MulAut.smul_def, MulAut.conj_apply]

end Transport

section Assembly

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisExc in
open CFSG.Quasithin (isSimpleGroup_u33Pres u33GenP u33PresHom u33PresHom_genPG card_u33Pres u33_orders u33_syl g2HomC g2RhoC g2IndexTwoData g2HomC_injective finite_g2Group G2Group U33G u33GenPG u33Data u33Extra g2Hom g2Img g2L g2L_one g2L_three g2L_zero g2L_zero_eq_img g2L_one_mul_three g2Img_mem_range g2L_mem_normalizer g2_derived_eq_range adjointGroup_G2_eq g2Hom_of u33GenPG_of g2Hom_injective two_eq_zero_of_card_two eq_zero_or_eq_one_of_card_two) in
theorem burnsideF4c_y_ne_one : u33GenP 4 ≠ 1 := by decide +kernel

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisExc in
open CFSG.Quasithin (isSimpleGroup_u33Pres u33GenP u33PresHom u33PresHom_genPG card_u33Pres u33_orders u33_syl g2HomC g2RhoC g2IndexTwoData g2HomC_injective finite_g2Group G2Group U33G u33GenPG u33Data u33Extra g2Hom g2Img g2L g2L_one g2L_three g2L_zero g2L_zero_eq_img g2L_one_mul_three g2Img_mem_range g2L_mem_normalizer g2_derived_eq_range adjointGroup_G2_eq g2Hom_of u33GenPG_of g2Hom_injective two_eq_zero_of_card_two eq_zero_or_eq_one_of_card_two) in
theorem burnsideF4c_y_not_mem_Sylow
    (S : Subgroup U33G) (hS : IsPGroup 2 S) :
    u33GenPG 4 ∉ S := by
  intro hy
  obtain ⟨k, hk⟩ := hS ⟨u33GenPG 4, hy⟩
  have h3 : u33GenPG 4 ^ 3 = 1 := u33_orders.2.2.2.2
  have h1 : u33GenPG 4 ≠ 1 := by
    intro h
    apply burnsideF4c_y_ne_one
    have := congrArg u33PresHom h
    rwa [u33PresHom_genPG, map_one] at this
  have hord : orderOf (u33GenPG 4) = 3 := orderOf_eq_prime h3 h1
  have hk' : u33GenPG 4 ^ (2 ^ k) = 1 := by
    have := congrArg Subtype.val hk
    simpa using this
  have hdvd : 3 ∣ 2 ^ k := hord ▸ orderOf_dvd_of_pow_eq_one hk'
  have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three hdvd
  omega

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisExc in
open CFSG.Quasithin (isSimpleGroup_u33Pres u33GenP u33PresHom u33PresHom_genPG card_u33Pres u33_orders u33_syl g2HomC g2RhoC g2IndexTwoData g2HomC_injective finite_g2Group G2Group U33G u33GenPG u33Data u33Extra g2Hom g2Img g2L g2L_one g2L_three g2L_zero g2L_zero_eq_img g2L_one_mul_three g2Img_mem_range g2L_mem_normalizer g2_derived_eq_range adjointGroup_G2_eq g2Hom_of u33GenPG_of g2Hom_injective two_eq_zero_of_card_two eq_zero_or_eq_one_of_card_two) in
theorem burnsideF4c_Pg_invol
    {K : Type} [Field K] [Finite K] [CharP K 2] (hK : Nat.card K = 2)
    (h2 : (2 : K) = 0) (hk2 : ∀ c : K, c = 0 ∨ c = 1) :
    burnsideF4c_InvolInCore ((G2Native.pointParabolic K).comap (g2HomC h2)) := by
  obtain ⟨hSp, hS32⟩ := burnsideF4c_Sg_syl hK h2 hk2
  set S := (G2Native.positiveBorel K).comap (g2HomC h2) with hS
  set P := (G2Native.pointParabolic K).comap (g2HomC h2) with hP
  have hcard : Nat.card U33G = 6048 := card_u33Pres
  haveI : Finite U33G := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  have hSle : Nat.card S ∣ 6048 := hcard ▸ Subgroup.card_subgroup_dvd_card S
  obtain ⟨n, hn⟩ := hSp.exists_card_eq
  have hn5 : n = 5 := by
    rw [hn] at hSle hS32
    have h1 : 5 ≤ n := by
      by_contra hc
      have : 2 ^ n ≤ 2 ^ 4 := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    have h2' : n ≤ 5 := by
      by_contra hc
      have h64 : 2 ^ 6 ∣ 2 ^ n := pow_dvd_pow 2 (by omega)
      have := dvd_trans h64 hSle
      omega
    omega
  have hS32' : Nat.card S = 32 := by rw [hn, hn5]; norm_num
  have hSi : ¬ 2 ∣ S.index := by
    have h := Subgroup.card_mul_index S
    rw [hS32', hcard] at h
    have : S.index = 189 := by omega
    rw [this]; norm_num
  obtain ⟨h, hh⟩ := burnsideF4c_sylow_conj S u33Data.T hSp hSi u33_syl.1 u33_syl.2
  obtain ⟨z, hz1, hz2, hzφ⟩ := burnsideF4c_exists_z (K := K) h2 hk2
  have hzc := burnsideF4c_Pg_comm hK h2 z hzφ
  refine burnsideF4c_InvolInCore_of_map (MulAut.conj h).toMonoidHom (MulAut.conj h).injective ?_
  refine burnsideF4c_u33_invol _ ?_ ?_ (h * z * h⁻¹) ?_ ?_ ?_
  · intro g hg
    obtain ⟨s, hs, rfl⟩ := (hh g).1 hg
    exact ⟨s, burnsideF4c_le_Pg h2 hs, by simp⟩
  · intro heq
    have hyP : u33GenPG 4 ∈ P := burnsideF4c_y_mem hK h2
    have hmem : h * u33GenPG 4 * h⁻¹ ∈ u33Data.T := by
      rw [← heq]
      exact ⟨_, hyP, by simp⟩
    obtain ⟨s, hs, hse⟩ := (hh _).1 hmem
    have hsy : s = u33GenPG 4 := by simpa using hse
    exact burnsideF4c_y_not_mem_Sylow S hSp (hsy ▸ hs)
  · intro h1
    apply hz1
    have : h * z * h⁻¹ = h * 1 * h⁻¹ := by rw [h1]; group
    simpa using this
  · calc h * z * h⁻¹ * (h * z * h⁻¹) = h * (z * z) * h⁻¹ := by group
      _ = 1 := by rw [hz2]; group
  · rintro _ ⟨p, hp, rfl⟩
    show h * p * h⁻¹ * (h * z * h⁻¹) = h * z * h⁻¹ * (h * p * h⁻¹)
    calc h * p * h⁻¹ * (h * z * h⁻¹) = h * (p * z) * h⁻¹ := by group
      _ = h * (z * p) * h⁻¹ := by rw [hzc p hp]
      _ = h * z * h⁻¹ * (h * p * h⁻¹) := by group

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisExc in
open CFSG.Quasithin (isSimpleGroup_u33Pres u33GenP u33PresHom u33PresHom_genPG card_u33Pres u33_orders u33_syl g2HomC g2RhoC g2IndexTwoData g2HomC_injective finite_g2Group G2Group U33G u33GenPG u33Data u33Extra g2Hom g2Img g2L g2L_one g2L_three g2L_zero g2L_zero_eq_img g2L_one_mul_three g2Img_mem_range g2L_mem_normalizer g2_derived_eq_range adjointGroup_G2_eq g2Hom_of u33GenPG_of g2Hom_injective two_eq_zero_of_card_two eq_zero_or_eq_one_of_card_two) in
theorem burnsideF4c_center_u33
    : Subgroup.center U33G = ⊥ := by
  haveI := isSimpleGroup_u33Pres
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center U33G) with h | h
  · exact h
  · exfalso
    have hc : u33GenPG 0 ∈ Subgroup.center U33G := by rw [h]; trivial
    have := Subgroup.mem_center_iff.1 hc (u33GenPG 3)
    have h' := congrArg u33PresHom this
    simp only [map_mul, u33PresHom_genPG] at h'
    exact (by decide +kernel : u33GenP 3 * u33GenP 0 ≠ u33GenP 0 * u33GenP 3) h'

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisExc in
open CFSG.Quasithin (isSimpleGroup_u33Pres u33GenP u33PresHom u33PresHom_genPG card_u33Pres u33_orders u33_syl g2HomC g2RhoC g2IndexTwoData g2HomC_injective finite_g2Group G2Group U33G u33GenPG u33Data u33Extra g2Hom g2Img g2L g2L_one g2L_three g2L_zero g2L_zero_eq_img g2L_one_mul_three g2Img_mem_range g2L_mem_normalizer g2_derived_eq_range adjointGroup_G2_eq g2Hom_of u33GenPG_of g2Hom_injective two_eq_zero_of_card_two eq_zero_or_eq_one_of_card_two) in
noncomputable def burnsideF4c_iota
    {K : Type} [Field K] (h2 : (2 : K) = 0)
    (hk2 : ∀ c : K, c = 0 ∨ c = 1) : U33G →* G2Native.Derived K :=
  (g2Hom h2).codRestrict _ (fun x => by
    rw [g2_derived_eq_range h2 hk2]; exact ⟨x, rfl⟩)

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisExc in
open CFSG.Quasithin (isSimpleGroup_u33Pres u33GenP u33PresHom u33PresHom_genPG card_u33Pres u33_orders u33_syl g2HomC g2RhoC g2IndexTwoData g2HomC_injective finite_g2Group G2Group U33G u33GenPG u33Data u33Extra g2Hom g2Img g2L g2L_one g2L_three g2L_zero g2L_zero_eq_img g2L_one_mul_three g2Img_mem_range g2L_mem_normalizer g2_derived_eq_range adjointGroup_G2_eq g2Hom_of u33GenPG_of g2Hom_injective two_eq_zero_of_card_two eq_zero_or_eq_one_of_card_two) in
theorem burnsideF4c_iota_injective
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2)
    (h2 : (2 : K) = 0) (hk2 : ∀ c : K, c = 0 ∨ c = 1) :
    Function.Injective (burnsideF4c_iota h2 hk2) := fun a b hab =>
  g2Hom_injective h2 (congrArg Subtype.val hab)

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisExc in
open CFSG.Quasithin (isSimpleGroup_u33Pres u33GenP u33PresHom u33PresHom_genPG card_u33Pres u33_orders u33_syl g2HomC g2RhoC g2IndexTwoData g2HomC_injective finite_g2Group G2Group U33G u33GenPG u33Data u33Extra g2Hom g2Img g2L g2L_one g2L_three g2L_zero g2L_zero_eq_img g2L_one_mul_three g2Img_mem_range g2L_mem_normalizer g2_derived_eq_range adjointGroup_G2_eq g2Hom_of u33GenPG_of g2Hom_injective two_eq_zero_of_card_two eq_zero_or_eq_one_of_card_two) in
theorem burnsideF4c_iota_surjective
    {K : Type} [Field K] (h2 : (2 : K) = 0)
    (hk2 : ∀ c : K, c = 0 ∨ c = 1) : Function.Surjective (burnsideF4c_iota h2 hk2) := by
  rintro ⟨d, hd⟩
  rw [g2_derived_eq_range h2 hk2] at hd
  obtain ⟨u, hu⟩ := hd
  exact ⟨u, Subtype.ext hu⟩

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisExc in
open CFSG.Quasithin (isSimpleGroup_u33Pres u33GenP u33PresHom u33PresHom_genPG card_u33Pres u33_orders u33_syl g2HomC g2RhoC g2IndexTwoData g2HomC_injective finite_g2Group G2Group U33G u33GenPG u33Data u33Extra g2Hom g2Img g2L g2L_one g2L_three g2L_zero g2L_zero_eq_img g2L_one_mul_three g2Img_mem_range g2L_mem_normalizer g2_derived_eq_range adjointGroup_G2_eq g2Hom_of u33GenPG_of g2Hom_injective two_eq_zero_of_card_two eq_zero_or_eq_one_of_card_two) in
theorem burnsideF4c_center_derived
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2)
    (h2 : (2 : K) = 0) (hk2 : ∀ c : K, c = 0 ∨ c = 1) :
    Subgroup.center (G2Native.Derived K) = ⊥ := by
  rw [eq_bot_iff]
  intro c hc
  obtain ⟨u, rfl⟩ := burnsideF4c_iota_surjective h2 hk2 c
  have hu : u ∈ Subgroup.center U33G := by
    rw [Subgroup.mem_center_iff]
    intro v
    have := Subgroup.mem_center_iff.1 hc (burnsideF4c_iota h2 hk2 v)
    exact burnsideF4c_iota_injective hK h2 hk2 (by simpa [map_mul] using this)
  rw [burnsideF4c_center_u33, Subgroup.mem_bot] at hu
  rw [hu, map_one]
  exact Subgroup.one_mem _

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisExc in
open CFSG.Quasithin (isSimpleGroup_u33Pres u33GenP u33PresHom u33PresHom_genPG card_u33Pres u33_orders u33_syl g2HomC g2RhoC g2IndexTwoData g2HomC_injective finite_g2Group G2Group U33G u33GenPG u33Data u33Extra g2Hom g2Img g2L g2L_one g2L_three g2L_zero g2L_zero_eq_img g2L_one_mul_three g2Img_mem_range g2L_mem_normalizer g2_derived_eq_range adjointGroup_G2_eq g2Hom_of u33GenPG_of g2Hom_injective two_eq_zero_of_card_two eq_zero_or_eq_one_of_card_two) in
theorem burnsideF4c_points_eq
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2)
    (h2 : (2 : K) = 0) (hk2 : ∀ c : K, c = 0 ∨ c = 1)
    {E : Type} [Group E] {Gp : Subgroup E} (marking : G2Native.SmallModel K ≃* ↥Gp)
    (L : Subgroup (G2Native.Parent K)) :
    ∃ ψ : U33G →* E, Function.Injective ψ ∧
      (G2Native.smallImage K marking L).map Gp.subtype = (L.comap (g2HomC h2)).map ψ := by
  set ι := burnsideF4c_iota h2 hk2 with hι
  have hιs := burnsideF4c_iota_surjective h2 hk2
  have hιi := burnsideF4c_iota_injective hK h2 hk2
  have hcomp : (G2Native.derivedInclusion K).comp ι = g2HomC h2 := by
    ext x; rfl
  have hder : G2Native.derivedLocal K L = (L.comap (g2HomC h2)).map ι := by
    have h1 : (L.comap (G2Native.derivedInclusion K)).comap ι = L.comap (g2HomC h2) := by
      rw [Subgroup.comap_comap, hcomp]
    rw [← h1, Subgroup.map_comap_eq_self_of_surjective hιs]
    rfl
  have hcen := burnsideF4c_center_derived hK h2 hk2
  refine ⟨Gp.subtype.comp (marking.toMonoidHom.comp
    ((QuotientGroup.mk' (Subgroup.center (G2Native.Derived K))).comp ι)), ?_, ?_⟩
  · have hmk : Function.Injective (QuotientGroup.mk' (Subgroup.center (G2Native.Derived K))) := by
      rw [← MonoidHom.ker_eq_bot_iff, QuotientGroup.ker_mk', hcen]
    intro a b hab
    exact hιi (hmk (marking.injective (Subtype.coe_injective hab)))
  · unfold G2Native.smallImage G2Native.smallLocal
    rw [hder, Subgroup.map_map, Subgroup.map_map, Subgroup.map_map]
    rfl

end Assembly


abbrev burnsideF4c_SL : Type := Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)

@[expose] def burnsideF4c_ent (A : burnsideF4c_SL) (i j : Fin 3) : ZMod 2 :=
  (A : Matrix (Fin 3) (Fin 3) (ZMod 2)) i j

@[expose] def burnsideF4c_inP (A : burnsideF4c_SL) : Prop :=
  burnsideF4c_ent A 1 0 = 0 ∧ burnsideF4c_ent A 2 0 = 0

@[expose] def burnsideF4c_inL (A : burnsideF4c_SL) : Prop :=
  burnsideF4c_ent A 2 0 = 0 ∧ burnsideF4c_ent A 2 1 = 0

instance : DecidablePred burnsideF4c_inP := fun A => inferInstanceAs (Decidable (_ ∧ _))
instance : DecidablePred burnsideF4c_inL := fun A => inferInstanceAs (Decidable (_ ∧ _))

theorem burnsideF4c_inP_mul (A B : burnsideF4c_SL) (hA : burnsideF4c_inP A)
    (hB : burnsideF4c_inP B) : burnsideF4c_inP (A * B) := by
  obtain ⟨hA1, hA2⟩ := hA
  obtain ⟨hB1, hB2⟩ := hB
  unfold burnsideF4c_inP burnsideF4c_ent at *
  simp [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_three, hA1, hA2, hB1, hB2]

theorem burnsideF4c_inL_mul (A B : burnsideF4c_SL) (hA : burnsideF4c_inL A)
    (hB : burnsideF4c_inL B) : burnsideF4c_inL (A * B) := by
  obtain ⟨hA1, hA2⟩ := hA
  obtain ⟨hB1, hB2⟩ := hB
  unfold burnsideF4c_inL burnsideF4c_ent at *
  simp [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_three, hA1, hA2, hB1, hB2]

theorem burnsideF4c_inP_inv : ∀ A : burnsideF4c_SL, burnsideF4c_inP A → burnsideF4c_inP A⁻¹ := by
  decide +kernel

theorem burnsideF4c_inL_inv : ∀ A : burnsideF4c_SL, burnsideF4c_inL A → burnsideF4c_inL A⁻¹ := by
  decide +kernel

@[expose] def burnsideF4c_P : Subgroup burnsideF4c_SL where
  carrier := {A | burnsideF4c_inP A}
  one_mem' := by decide +kernel
  mul_mem' := fun {A B} hA hB => burnsideF4c_inP_mul A B hA hB
  inv_mem' := fun {A} hA => burnsideF4c_inP_inv A hA

@[expose] def burnsideF4c_L : Subgroup burnsideF4c_SL where
  carrier := {A | burnsideF4c_inL A}
  one_mem' := by decide +kernel
  mul_mem' := fun {A B} hA hB => burnsideF4c_inL_mul A B hA hB
  inv_mem' := fun {A} hA => burnsideF4c_inL_inv A hA

instance : DecidablePred (· ∈ burnsideF4c_P) := fun A => inferInstanceAs (Decidable (burnsideF4c_inP A))
instance : DecidablePred (· ∈ burnsideF4c_L) := fun A => inferInstanceAs (Decidable (burnsideF4c_inL A))
instance : DecidablePred (· ∈ burnsideF4c_P ⊓ burnsideF4c_L) :=
  fun A => inferInstanceAs (Decidable (A ∈ burnsideF4c_P ∧ A ∈ burnsideF4c_L))

@[expose] def burnsideF4c_t : burnsideF4c_SL := ⟨!![0, 1, 0; 1, 0, 0; 0, 0, 1], by decide +kernel⟩

@[expose] def burnsideF4c_s : burnsideF4c_SL := ⟨!![1, 0, 0; 0, 0, 1; 0, 1, 0], by decide +kernel⟩

theorem burnsideF4c_t_mem : burnsideF4c_t ∈ burnsideF4c_L ∧ burnsideF4c_t ∉ burnsideF4c_P ⊓ burnsideF4c_L := by
  decide +kernel

theorem burnsideF4c_s_mem : burnsideF4c_s ∈ burnsideF4c_P ∧ burnsideF4c_s ∉ burnsideF4c_P ⊓ burnsideF4c_L := by
  decide +kernel

theorem burnsideF4c_t_sq : burnsideF4c_t * burnsideF4c_t = 1 := by decide +kernel
theorem burnsideF4c_s_sq : burnsideF4c_s * burnsideF4c_s = 1 := by decide +kernel

theorem burnsideF4c_card_SL : Nat.card burnsideF4c_SL = 168 := by
  rw [Nat.card_eq_fintype_card]; decide +kernel

theorem burnsideF4c_F1 : ∀ b : burnsideF4c_SL, b ∈ burnsideF4c_L → b ∉ burnsideF4c_P ⊓ burnsideF4c_L →
    ∃ δ : burnsideF4c_SL, δ ∈ burnsideF4c_P ⊓ burnsideF4c_L ∧
      burnsideF4c_t * δ * b ∈ burnsideF4c_P ⊓ burnsideF4c_L := by
  decide +kernel

theorem burnsideF4c_F2 : ∀ a : burnsideF4c_SL, a ∈ burnsideF4c_P → a ∉ burnsideF4c_P ⊓ burnsideF4c_L →
    ∃ δ : burnsideF4c_SL, δ ∈ burnsideF4c_P ⊓ burnsideF4c_L ∧
      burnsideF4c_t * δ * burnsideF4c_t ∈ burnsideF4c_P ⊓ burnsideF4c_L ∧
      burnsideF4c_s * (burnsideF4c_t * δ * burnsideF4c_t) * a ∈ burnsideF4c_P ⊓ burnsideF4c_L := by
  decide +kernel

theorem burnsideF4c_F3 : ∀ b : burnsideF4c_SL, b ∈ burnsideF4c_L → b ∉ burnsideF4c_P ⊓ burnsideF4c_L →
    ∃ δ : burnsideF4c_SL, δ ∈ burnsideF4c_P ⊓ burnsideF4c_L ∧
      burnsideF4c_t * δ * burnsideF4c_t ∈ burnsideF4c_P ⊓ burnsideF4c_L ∧
      burnsideF4c_s * (burnsideF4c_t * δ * burnsideF4c_t) * burnsideF4c_s ∈ burnsideF4c_P ⊓ burnsideF4c_L ∧
      burnsideF4c_t * (burnsideF4c_s * (burnsideF4c_t * δ * burnsideF4c_t) * burnsideF4c_s) * b ∈
        burnsideF4c_P ⊓ burnsideF4c_L := by
  decide +kernel


abbrev burnsideF4c_V : Type := {v : Fin 3 → ZMod 2 // v ≠ 0}

instance : MulAction burnsideF4c_SL burnsideF4c_V where
  smul A v := ⟨A • (v : Fin 3 → ZMod 2), by
    intro h
    exact v.2 ((smul_eq_zero_iff_eq A).1 h)⟩
  one_smul v := Subtype.ext (one_smul _ _)
  mul_smul A B v := Subtype.ext (mul_smul A B (v : Fin 3 → ZMod 2))

theorem burnsideF4c_smul_coe (A : burnsideF4c_SL) (v : burnsideF4c_V) :
    ((A • v : burnsideF4c_V) : Fin 3 → ZMod 2) = A • (v : Fin 3 → ZMod 2) := rfl

@[expose] def burnsideF4c_e0 : burnsideF4c_V := ⟨![1, 0, 0], by decide⟩

@[expose] def burnsideF4c_nat : burnsideF4c_SL →* Equiv.Perm burnsideF4c_V :=
  MulAction.toPermHom burnsideF4c_SL burnsideF4c_V

theorem burnsideF4c_nat_apply (A : burnsideF4c_SL) (v : burnsideF4c_V) :
    burnsideF4c_nat A v = A • v := rfl

theorem burnsideF4c_nat_injective : Function.Injective burnsideF4c_nat := by
  rw [injective_iff_map_eq_one]
  intro A hA
  have h : ∀ v : burnsideF4c_V, A • v = v := fun v => by
    have := congrArg (fun p : Equiv.Perm burnsideF4c_V => p v) hA
    simpa [burnsideF4c_nat_apply] using this
  revert h
  revert A
  decide +kernel


@[expose] def burnsideF4c_a : burnsideF4c_SL := ⟨!![1, 1, 0; 0, 1, 1; 0, 0, 1], by decide +kernel⟩
@[expose] def burnsideF4c_b : burnsideF4c_SL := ⟨!![1, 0, 0; 0, 1, 1; 0, 0, 1], by decide +kernel⟩
@[expose] def burnsideF4c_z : burnsideF4c_SL := ⟨!![1, 0, 1; 0, 1, 0; 0, 0, 1], by decide +kernel⟩

theorem burnsideF4c_a_mem : burnsideF4c_a ∈ burnsideF4c_P ⊓ burnsideF4c_L := by decide +kernel
theorem burnsideF4c_b_mem : burnsideF4c_b ∈ burnsideF4c_P ⊓ burnsideF4c_L := by decide +kernel
theorem burnsideF4c_z_mem : burnsideF4c_z ∈ burnsideF4c_P ⊓ burnsideF4c_L := by decide +kernel
theorem burnsideF4c_z_sq : burnsideF4c_z * burnsideF4c_z = 1 := by decide +kernel
theorem burnsideF4c_z_ne : burnsideF4c_z ≠ 1 := by decide +kernel
theorem burnsideF4c_z_central : ∀ d : burnsideF4c_SL, d ∈ burnsideF4c_P ⊓ burnsideF4c_L →
    burnsideF4c_z * d = d * burnsideF4c_z := by decide +kernel
theorem burnsideF4c_rel2 : burnsideF4c_a⁻¹ * burnsideF4c_t * burnsideF4c_b⁻¹ * burnsideF4c_t *
    burnsideF4c_a⁻¹ = 1 := by decide +kernel
theorem burnsideF4c_rel3 : (burnsideF4c_t * burnsideF4c_a) * (burnsideF4c_t * burnsideF4c_a) *
    (burnsideF4c_t * burnsideF4c_a) = 1 := by decide +kernel


theorem burnsideF4c_val1 : ∃ a₂ a₃ : burnsideF4c_SL, a₂ ∈ burnsideF4c_P ∧ a₃ ∈ burnsideF4c_P ∧
    a₂ ∉ burnsideF4c_L ∧ a₃ ∉ burnsideF4c_L ∧ a₂⁻¹ * a₃ ∉ burnsideF4c_L := by
  decide +kernel

theorem burnsideF4c_val2 : ∃ b₂ b₃ : burnsideF4c_SL, b₂ ∈ burnsideF4c_L ∧ b₃ ∈ burnsideF4c_L ∧
    b₂ ∉ burnsideF4c_P ∧ b₃ ∉ burnsideF4c_P ∧ b₂⁻¹ * b₃ ∉ burnsideF4c_P := by
  decide +kernel

theorem burnsideF4c_card_P : Nat.card burnsideF4c_P = 24 := by
  rw [Nat.card_eq_fintype_card]; decide +kernel

theorem burnsideF4c_P_sup_L : burnsideF4c_P ⊔ burnsideF4c_L = ⊤ := by
  have hidx : burnsideF4c_P.index = 7 := by
    have h := Subgroup.card_mul_index burnsideF4c_P
    rw [burnsideF4c_card_P, burnsideF4c_card_SL] at h
    omega
  have hdvd : (burnsideF4c_P ⊔ burnsideF4c_L).index ∣ 7 := by
    rw [← hidx]; exact Subgroup.index_dvd_of_le le_sup_left
  have h7 : Nat.Prime 7 := by norm_num
  rcases (Nat.dvd_prime h7).1 hdvd with h1 | h7'
  · exact Subgroup.index_eq_one.1 h1
  · exfalso
    have hcard : Nat.card (burnsideF4c_P ⊔ burnsideF4c_L : Subgroup burnsideF4c_SL) ≤ Nat.card burnsideF4c_P := by
      have h := Subgroup.card_mul_index (burnsideF4c_P ⊔ burnsideF4c_L)
      rw [h7', burnsideF4c_card_SL] at h
      rw [burnsideF4c_card_P]
      omega
    have heq := Subgroup.eq_of_le_of_card_ge (le_sup_left : burnsideF4c_P ≤ burnsideF4c_P ⊔ burnsideF4c_L) hcard
    have : burnsideF4c_t ∈ burnsideF4c_P := by
      rw [heq]; exact Subgroup.mem_sup_right burnsideF4c_t_mem.1
    exact burnsideF4c_t_mem.2 ⟨this, burnsideF4c_t_mem.1⟩

@[expose] def burnsideF4c_e1 : burnsideF4c_V := burnsideF4c_t • burnsideF4c_e0

theorem burnsideF4c_P_fix_e0 : ∀ a : burnsideF4c_SL, a ∈ burnsideF4c_P → a • burnsideF4c_e0 = burnsideF4c_e0 := by
  decide +kernel

theorem burnsideF4c_e1_ne : burnsideF4c_e1 ≠ burnsideF4c_e0 := by decide +kernel

theorem burnsideF4c_V_orbit : ∀ v : burnsideF4c_V, v = burnsideF4c_e0 ∨
    ∃ a : burnsideF4c_SL, a ∈ burnsideF4c_P ∧ v = a • burnsideF4c_e1 := by
  decide +kernel

theorem burnsideF4c_stab_e1 : ∀ a : burnsideF4c_SL, a ∈ burnsideF4c_P →
    (a • burnsideF4c_e1 = burnsideF4c_e1 ↔
      (a ∈ burnsideF4c_P ⊓ burnsideF4c_L ∧ burnsideF4c_t * a * burnsideF4c_t ∈ burnsideF4c_P ⊓ burnsideF4c_L)) := by
  decide +kernel


@[expose] def burnsideF4c_vecRaw : Fin 7 → (Fin 3 → ZMod 2) :=
  ![![0, 0, 1], ![0, 1, 0], ![0, 1, 1], ![1, 0, 0], ![1, 0, 1], ![1, 1, 0], ![1, 1, 1]]

theorem burnsideF4c_vecRaw_ne : ∀ i, burnsideF4c_vecRaw i ≠ 0 := by decide

@[expose] def burnsideF4c_vecOf (i : Fin 7) : burnsideF4c_V := ⟨burnsideF4c_vecRaw i, burnsideF4c_vecRaw_ne i⟩

theorem burnsideF4c_vecOf_bijective : Function.Bijective burnsideF4c_vecOf := by
  constructor
  · intro i j h
    have := congrArg Subtype.val h
    revert this; revert i j; decide
  · intro v
    revert v; decide +kernel

@[expose] def burnsideF4c_tabA : Fin 7 → Fin 7 := ![2, 5, 4, 3, 6, 1, 0]
@[expose] def burnsideF4c_tabAi : Fin 7 → Fin 7 := ![6, 5, 0, 3, 2, 1, 4]
@[expose] def burnsideF4c_tabB : Fin 7 → Fin 7 := ![2, 1, 0, 3, 6, 5, 4]
@[expose] def burnsideF4c_tabT : Fin 7 → Fin 7 := ![0, 3, 4, 1, 2, 5, 6]
@[expose] def burnsideF4c_tabZTZ : Fin 7 → Fin 7 := ![6, 3, 2, 1, 4, 5, 0]

theorem burnsideF4c_tabA_spec : ∀ i, burnsideF4c_a • burnsideF4c_vecOf i =
    burnsideF4c_vecOf (burnsideF4c_tabA i) := by decide +kernel
theorem burnsideF4c_tabAi_spec : ∀ i, burnsideF4c_a⁻¹ • burnsideF4c_vecOf i =
    burnsideF4c_vecOf (burnsideF4c_tabAi i) := by decide +kernel
theorem burnsideF4c_tabB_spec : ∀ i, burnsideF4c_b⁻¹ • burnsideF4c_vecOf i =
    burnsideF4c_vecOf (burnsideF4c_tabB i) := by decide +kernel
theorem burnsideF4c_tabT_spec : ∀ i, burnsideF4c_t • burnsideF4c_vecOf i =
    burnsideF4c_vecOf (burnsideF4c_tabT i) := by decide +kernel
theorem burnsideF4c_tabZTZ_spec : ∀ i, (burnsideF4c_z * burnsideF4c_t * burnsideF4c_z⁻¹) •
    burnsideF4c_vecOf i = burnsideF4c_vecOf (burnsideF4c_tabZTZ i) := by decide +kernel

theorem burnsideF4c_e0_eq : burnsideF4c_e0 = burnsideF4c_vecOf 3 := by decide +kernel
theorem burnsideF4c_e1_eq : burnsideF4c_e1 = burnsideF4c_vecOf 1 := by decide +kernel

@[expose] def burnsideF4c_tmpl (f0 f2 f4 f5 f6 : Fin 7) : Fin 7 → Fin 7 := ![f0, 3, f2, 1, f4, f5, f6]

theorem burnsideF4c_classify_tab : ∀ f0 f2 f4 f5 f6 : Fin 7,
    (∀ i, burnsideF4c_tmpl f0 f2 f4 f5 f6 (burnsideF4c_tmpl f0 f2 f4 f5 f6 i) = i) →
    (∀ i, burnsideF4c_tabAi (burnsideF4c_tmpl f0 f2 f4 f5 f6 (burnsideF4c_tabB
      (burnsideF4c_tmpl f0 f2 f4 f5 f6 (burnsideF4c_tabAi i)))) = i) →
    (∀ i, burnsideF4c_tmpl f0 f2 f4 f5 f6 (burnsideF4c_tabA (burnsideF4c_tmpl f0 f2 f4 f5 f6
      (burnsideF4c_tabA (burnsideF4c_tmpl f0 f2 f4 f5 f6 (burnsideF4c_tabA i))))) = i) →
    (burnsideF4c_tmpl f0 f2 f4 f5 f6 = burnsideF4c_tabT ∨
      burnsideF4c_tmpl f0 f2 f4 f5 f6 = burnsideF4c_tabZTZ) := by
  decide +kernel

section Step

open CFSG.Quasithin CFSG.Quasithin.CosetGeom in
theorem burnsideF4c_inv_smul_path {V : Type*} {Γ : SimpleGraph V} {H : Type*} [Group H]
    [MulAction H V] [GraphAction H Γ] {n : ℕ} {r : GPath Γ n} {h : H} (hh : h • r = r) : h⁻¹ • r = r := by
  calc h⁻¹ • r = h⁻¹ • (h • r) := by rw [hh]
    _ = (h⁻¹ * h) • r := (GPath.mul_smul' _ _ _).symm
    _ = r := by rw [inv_mul_cancel, GPath.one_smul']


variable {V : Type*} {Γ : SimpleGraph V} {H : Type*} [Group H] [MulAction H V] [CFSG.Quasithin.GraphAction H Γ]

open CFSG.Quasithin CFSG.Quasithin.CosetGeom in
theorem burnsideF4c_pathTrans_succ (u : V) (n : ℕ)
    (hT : ∀ q q' : GPath Γ n, q ∈ GPath.nbPaths Γ u n → q' ∈ GPath.nbPaths Γ u n →
      ∃ g : H, g • u = u ∧ g • q = q')
    (p : GPath Γ n) (hp : p ∈ GPath.nbPaths Γ u n) (w₀ : V)
    (hS : ∀ w : V, Γ.Adj (p n) w → (1 ≤ n → w ≠ p (n - 1)) →
      ∃ h : H, h • p = p ∧ h • w = w₀) :
    ∀ q q' : GPath Γ (n + 1), q ∈ GPath.nbPaths Γ u (n + 1) → q' ∈ GPath.nbPaths Γ u (n + 1) →
      ∃ g : H, g • u = u ∧ g • q = q' := by
  intro q q' hq hq'
  set r := q.take n (Nat.le_succ n) with hr
  set r' := q'.take n (Nat.le_succ n) with hr'
  have hqn : r ∈ GPath.nbPaths Γ u n :=
    ⟨by simpa [hr, GPath.take_apply_of_le _ _ _ (Nat.zero_le n)] using hq.1,
      hq.2.take n (Nat.le_succ n)⟩
  have hq'n : r' ∈ GPath.nbPaths Γ u n :=
    ⟨by simpa [hr', GPath.take_apply_of_le _ _ _ (Nat.zero_le n)] using hq'.1,
      hq'.2.take n (Nat.le_succ n)⟩
  obtain ⟨g₀, hg₀u, hg₀⟩ := hT _ _ hqn hq'n
  obtain ⟨k, hku, hk⟩ := hT p r' hp hq'n
  have hr_apply : ∀ i, i ≤ n → r i = q i := fun i hi => GPath.take_apply_of_le _ _ _ hi
  have hr'_apply : ∀ i, i ≤ n → r' i = q' i := fun i hi => GPath.take_apply_of_le _ _ _ hi
  have hg₀i : ∀ i, i ≤ n → g₀ • q i = q' i := by
    intro i hi
    have := (GPath.smul_eq_iff.mp hg₀) i hi
    rwa [hr_apply i hi, hr'_apply i hi] at this
  have hki : ∀ i, i ≤ n → k • p i = q' i := by
    intro i hi
    have := (GPath.smul_eq_iff.mp hk) i hi
    rwa [hr'_apply i hi] at this
  have hadj1 : Γ.Adj (q' n) (g₀ • q (n + 1)) := by
    rw [← hg₀i n le_rfl]
    exact (GraphAction.adj_smul g₀ _ _).mpr (q.adj n (Nat.lt_succ_self n))
  have hne1 : 1 ≤ n → g₀ • q (n + 1) ≠ q' (n - 1) := by
    intro hn heq
    rw [← hg₀i (n - 1) (by omega)] at heq
    have hinj : q (n + 1) = q (n - 1) := by
      have := congrArg (fun x => g₀⁻¹ • x) heq
      simpa using this
    exact hq.2 (n - 1) (by omega) (by rw [show n - 1 + 2 = n + 1 by omega]; exact hinj.symm)
  have hmove : ∀ w : V, Γ.Adj (q' n) w → (1 ≤ n → w ≠ q' (n - 1)) →
      ∃ h : H, h • r' = r' ∧ h • w = k • w₀ := by
    intro w hw hwn
    have hadj : Γ.Adj (p n) (k⁻¹ • w) := by
      have hh : Γ.Adj (k • p n) w := by rw [hki n le_rfl]; exact hw
      have := (GraphAction.adj_smul k⁻¹ _ _).mpr hh
      simpa using this
    have hne : 1 ≤ n → k⁻¹ • w ≠ p (n - 1) := by
      intro hn heq
      apply hwn hn
      have h1 : w = k • p (n - 1) := by
        have := congrArg (fun x => k • x) heq
        simpa using this
      rw [h1, hki (n - 1) (by omega)]
    obtain ⟨h₁, hh₁p, hh₁w⟩ := hS _ hadj hne
    refine ⟨k * h₁ * k⁻¹, ?_, ?_⟩
    · rw [GPath.smul_eq_iff]
      intro i hi
      have e1 : k⁻¹ • r' i = p i := by rw [hr'_apply i hi, ← hki i hi, inv_smul_smul]
      have e2 := (GPath.smul_eq_iff.mp hh₁p) i hi
      rw [mul_smul, mul_smul, e1, e2]
      exact (hki i hi).trans (hr'_apply i hi).symm
    · rw [mul_smul, mul_smul, hh₁w]
  obtain ⟨ha, hha, hhaw⟩ := hmove _ hadj1 hne1
  have hadj2 : Γ.Adj (q' n) (q' (n + 1)) := q'.adj n (Nat.lt_succ_self n)
  have hne2 : 1 ≤ n → q' (n + 1) ≠ q' (n - 1) := by
    intro hn heq
    exact hq'.2 (n - 1) (by omega) (by rw [show n - 1 + 2 = n + 1 by omega]; exact heq.symm)
  obtain ⟨hb, hhb, hhbw⟩ := hmove _ hadj2 hne2
  refine ⟨hb⁻¹ * ha * g₀, ?_, ?_⟩
  · have e0 : ∀ h : H, h • r' = r' → h • u = u := by
      intro h hh
      have := (GPath.smul_eq_iff.mp hh) 0 (Nat.zero_le n)
      rwa [hr'_apply 0 (Nat.zero_le n), hq'.1] at this
    have hb' : hb⁻¹ • r' = r' := burnsideF4c_inv_smul_path hhb
    have ha' := e0 ha hha
    have hb'' := e0 _ hb'
    rw [mul_smul, mul_smul, hg₀u, ha', hb'']
  · rw [GPath.smul_eq_iff]
    intro i hi
    by_cases hin : i ≤ n
    · rw [mul_smul, mul_smul, hg₀i i hin]
      have h1 := (GPath.smul_eq_iff.mp hha) i hin
      have h2 : hb⁻¹ • r' = r' := burnsideF4c_inv_smul_path hhb
      have h2i := (GPath.smul_eq_iff.mp h2) i hin
      rw [hr'_apply i hin] at h1 h2i
      rw [h1, h2i]
    · have hi' : i = n + 1 := by omega
      subst hi'
      rw [mul_smul, mul_smul, hhaw]
      have : hb⁻¹ • k • w₀ = q' (n + 1) := by
        rw [← hhbw]; simp
      exact this

end Step



section Vertices

variable {Y : Type*} [Group Y] (G₁ G₂ : Subgroup Y)

open CFSG.Quasithin CFSG.Quasithin.CosetGeom in
theorem burnsideF4c_le₁ : G₁ ≤ G₁ ⊔ G₂ := le_sup_left
open CFSG.Quasithin CFSG.Quasithin.CosetGeom in
theorem burnsideF4c_le₂ : G₂ ≤ G₁ ⊔ G₂ := le_sup_right

open CFSG.Quasithin CFSG.Quasithin.CosetGeom in
theorem burnsideF4c_smul_γ₀_eq_iff (g h : ↥(G₁ ⊔ G₂)) :
    g • γ₀ (G₁ ⊔ G₂) G₁ G₂ = h • γ₀ (G₁ ⊔ G₂) G₁ G₂ ↔ ((g⁻¹ * h : ↥(G₁ ⊔ G₂)) : Y) ∈ G₁ := by
  constructor
  · intro hgh
    have : (g⁻¹ * h) • γ₀ (G₁ ⊔ G₂) G₁ G₂ = γ₀ (G₁ ⊔ G₂) G₁ G₂ := by
      rw [mul_smul, ← hgh, inv_smul_smul]
    have h2 := mem_stab_of_smul_eq this
    rwa [stab_γ₀ (burnsideF4c_le₁ G₁ G₂)] at h2
  · intro hmem
    have : (g⁻¹ * h) • γ₀ (G₁ ⊔ G₂) G₁ G₂ = γ₀ (G₁ ⊔ G₂) G₁ G₂ :=
      smul_eq_of_mem_stab (by rw [stab_γ₀ (burnsideF4c_le₁ G₁ G₂)]; exact hmem)
    rw [mul_smul, inv_smul_eq_iff] at this
    exact this.symm

open CFSG.Quasithin CFSG.Quasithin.CosetGeom in
theorem burnsideF4c_smul_γ₁_eq_iff (g h : ↥(G₁ ⊔ G₂)) :
    g • γ₁ (G₁ ⊔ G₂) G₁ G₂ = h • γ₁ (G₁ ⊔ G₂) G₁ G₂ ↔ ((g⁻¹ * h : ↥(G₁ ⊔ G₂)) : Y) ∈ G₂ := by
  constructor
  · intro hgh
    have : (g⁻¹ * h) • γ₁ (G₁ ⊔ G₂) G₁ G₂ = γ₁ (G₁ ⊔ G₂) G₁ G₂ := by
      rw [mul_smul, ← hgh, inv_smul_smul]
    have h2 := mem_stab_of_smul_eq this
    rwa [stab_γ₁ (burnsideF4c_le₂ G₁ G₂)] at h2
  · intro hmem
    have : (g⁻¹ * h) • γ₁ (G₁ ⊔ G₂) G₁ G₂ = γ₁ (G₁ ⊔ G₂) G₁ G₂ :=
      smul_eq_of_mem_stab (by rw [stab_γ₁ (burnsideF4c_le₂ G₁ G₂)]; exact hmem)
    rw [mul_smul, inv_smul_eq_iff] at this
    exact this.symm

open CFSG.Quasithin CFSG.Quasithin.CosetGeom in
theorem burnsideF4c_adj_smul_γ₀ (g : ↥(G₁ ⊔ G₂)) (w : CosetGeom (G₁ ⊔ G₂) G₁ G₂) :
    (graph (G₁ ⊔ G₂) G₁ G₂).Adj (g • γ₀ (G₁ ⊔ G₂) G₁ G₂) w ↔
      ∃ a : ↥(G₁ ⊔ G₂), (a : Y) ∈ G₁ ∧ w = (g * a) • γ₁ (G₁ ⊔ G₂) G₁ G₂ := by
  have key : (graph (G₁ ⊔ G₂) G₁ G₂).Adj (g • γ₀ (G₁ ⊔ G₂) G₁ G₂) w ↔
      (graph (G₁ ⊔ G₂) G₁ G₂).Adj (γ₀ (G₁ ⊔ G₂) G₁ G₂) (g⁻¹ • w) := by
    rw [← smul_adj g⁻¹, inv_smul_smul]
  rw [key]
  constructor
  · intro h
    cases hw : g⁻¹ • w with
    | inl x => rw [hw] at h; exact (not_adj_inl_inl h).elim
    | inr y =>
      rw [hw] at h
      obtain ⟨a, ha, hay⟩ := adj_γ₀_inr_iff.mp h
      refine ⟨a, ha, ?_⟩
      have h1 : w = g • Sum.inr y := by rw [← hw, smul_inv_smul]
      rw [h1, ← hay, mul_smul, smul_γ₁]
  · rintro ⟨a, ha, hwa⟩
    rw [hwa, mul_smul, inv_smul_smul]
    have hmem : (a : Y) ∈ stab (γ₀ (G₁ ⊔ G₂) G₁ G₂) := by
      rw [stab_γ₀ (burnsideF4c_le₁ G₁ G₂)]; exact ha
    have hfix : a • γ₀ (G₁ ⊔ G₂) G₁ G₂ = γ₀ (G₁ ⊔ G₂) G₁ G₂ := smul_eq_of_mem_stab hmem
    have h2 := (smul_adj a).mpr (adj_γ₀_γ₁ (G₀ := G₁ ⊔ G₂) (G₁ := G₁) (G₂ := G₂))
    rw [hfix] at h2
    exact h2

open CFSG.Quasithin CFSG.Quasithin.CosetGeom in
theorem burnsideF4c_adj_smul_γ₁ (g : ↥(G₁ ⊔ G₂)) (w : CosetGeom (G₁ ⊔ G₂) G₁ G₂) :
    (graph (G₁ ⊔ G₂) G₁ G₂).Adj (g • γ₁ (G₁ ⊔ G₂) G₁ G₂) w ↔
      ∃ b : ↥(G₁ ⊔ G₂), (b : Y) ∈ G₂ ∧ w = (g * b) • γ₀ (G₁ ⊔ G₂) G₁ G₂ := by
  have key : (graph (G₁ ⊔ G₂) G₁ G₂).Adj (g • γ₁ (G₁ ⊔ G₂) G₁ G₂) w ↔
      (graph (G₁ ⊔ G₂) G₁ G₂).Adj (γ₁ (G₁ ⊔ G₂) G₁ G₂) (g⁻¹ • w) := by
    rw [← smul_adj g⁻¹, inv_smul_smul]
  rw [key]
  constructor
  · intro h
    cases hw : g⁻¹ • w with
    | inr y => rw [hw] at h; exact (not_adj_inr_inr h).elim
    | inl x =>
      rw [hw] at h
      obtain ⟨b, hb, hbx⟩ := adj_γ₁_inl_iff.mp h
      refine ⟨b, hb, ?_⟩
      have h1 : w = g • Sum.inl x := by rw [← hw, smul_inv_smul]
      rw [h1, ← hbx, mul_smul, smul_γ₀]
  · rintro ⟨b, hb, hwb⟩
    rw [hwb, mul_smul, inv_smul_smul]
    have hmem : (b : Y) ∈ stab (γ₁ (G₁ ⊔ G₂) G₁ G₂) := by
      rw [stab_γ₁ (burnsideF4c_le₂ G₁ G₂)]; exact hb
    have hfix : b • γ₁ (G₁ ⊔ G₂) G₁ G₂ = γ₁ (G₁ ⊔ G₂) G₁ G₂ := smul_eq_of_mem_stab hmem
    have h2 := (smul_adj b).mpr (adj_γ₀_γ₁ (G₀ := G₁ ⊔ G₂) (G₁ := G₁) (G₂ := G₂)).symm
    rw [hfix] at h2
    exact h2

end Vertices



section Trans

variable {Y : Type*} [Group Y] {G₁ G₂ : Subgroup Y}

open CFSG.Quasithin CFSG.Quasithin.CosetGeom in
noncomputable def burnsideF4c_basePath (t s : ↥(G₁ ⊔ G₂)) (ht2 : (t : Y) ∈ G₂) (hs1 : (s : Y) ∈ G₁) :
    GPath (graph (G₁ ⊔ G₂) G₁ G₂) 4 where
  toFun i :=
    match i with
    | 0 => γ₀ (G₁ ⊔ G₂) G₁ G₂
    | 1 => γ₁ (G₁ ⊔ G₂) G₁ G₂
    | 2 => t • γ₀ (G₁ ⊔ G₂) G₁ G₂
    | 3 => (t * s) • γ₁ (G₁ ⊔ G₂) G₁ G₂
    | _ => (t * s * t) • γ₀ (G₁ ⊔ G₂) G₁ G₂
  adj i hi := by
    have hmem : ∀ x : ↥(G₁ ⊔ G₂), (x : Y) ∈ G₂ → x • γ₁ (G₁ ⊔ G₂) G₁ G₂ = γ₁ (G₁ ⊔ G₂) G₁ G₂ := by
      intro x hx
      have hm : (x : Y) ∈ stab (γ₁ (G₁ ⊔ G₂) G₁ G₂) := by
        rw [stab_γ₁ (burnsideF4c_le₂ G₁ G₂)]; exact hx
      exact smul_eq_of_mem_stab hm
    have hmem0 : ∀ x : ↥(G₁ ⊔ G₂), (x : Y) ∈ G₁ → x • γ₀ (G₁ ⊔ G₂) G₁ G₂ = γ₀ (G₁ ⊔ G₂) G₁ G₂ := by
      intro x hx
      have hm : (x : Y) ∈ stab (γ₀ (G₁ ⊔ G₂) G₁ G₂) := by
        rw [stab_γ₀ (burnsideF4c_le₁ G₁ G₂)]; exact hx
      exact smul_eq_of_mem_stab hm
    have hadj_t : (graph (G₁ ⊔ G₂) G₁ G₂).Adj (γ₁ (G₁ ⊔ G₂) G₁ G₂) (t • γ₀ (G₁ ⊔ G₂) G₁ G₂) := by
      have h1 := (smul_adj t).mpr (adj_γ₀_γ₁ (G₀ := G₁ ⊔ G₂) (G₁ := G₁) (G₂ := G₂)).symm
      rw [hmem t ht2] at h1
      exact h1
    interval_cases i
    · exact adj_γ₀_γ₁
    · exact hadj_t
    ·
      have h1 := (smul_adj (t * s)).mpr (adj_γ₀_γ₁ (G₀ := G₁ ⊔ G₂) (G₁ := G₁) (G₂ := G₂))
      have h2 : (t * s) • γ₀ (G₁ ⊔ G₂) G₁ G₂ = t • γ₀ (G₁ ⊔ G₂) G₁ G₂ := by
        rw [mul_smul, hmem0 s hs1]
      rw [h2] at h1
      exact h1
    ·
      have h1 := (smul_adj (t * s)).mpr hadj_t
      rw [← mul_smul] at h1
      exact h1
  tail i hi := by
    obtain ⟨k, rfl⟩ : ∃ k, i = k + 4 := ⟨i - 4, by omega⟩
    rfl



open CFSG.Quasithin CFSG.Quasithin.CosetGeom in
theorem burnsideF4c_basePath_noBack (t s : ↥(G₁ ⊔ G₂)) (ht2 : (t : Y) ∈ G₂) (ht1 : (t : Y) ∉ G₁)
    (hs1 : (s : Y) ∈ G₁) (hs2 : (s : Y) ∉ G₂) :
    (burnsideF4c_basePath t s ht2 hs1).NoBack := by
  intro i hi
  have hi' : i ≤ 2 := by omega
  interval_cases i
  · intro h
    have h' : (1 : ↥(G₁ ⊔ G₂)) • γ₀ (G₁ ⊔ G₂) G₁ G₂ = t • γ₀ (G₁ ⊔ G₂) G₁ G₂ := by
      simpa [burnsideF4c_basePath] using h
    rw [burnsideF4c_smul_γ₀_eq_iff] at h'
    exact ht1 (by simpa using h')
  · intro h
    have h' : (1 : ↥(G₁ ⊔ G₂)) • γ₁ (G₁ ⊔ G₂) G₁ G₂ = (t * s) • γ₁ (G₁ ⊔ G₂) G₁ G₂ := by
      simpa [burnsideF4c_basePath] using h
    rw [burnsideF4c_smul_γ₁_eq_iff] at h'
    have h2 : ((t : Y) * (s : Y)) ∈ G₂ := by simpa using h'
    exact hs2 (by simpa using G₂.mul_mem (G₂.inv_mem ht2) h2)
  · intro h
    have h' : t • γ₀ (G₁ ⊔ G₂) G₁ G₂ = (t * s * t) • γ₀ (G₁ ⊔ G₂) G₁ G₂ := by
      simpa [burnsideF4c_basePath] using h
    rw [burnsideF4c_smul_γ₀_eq_iff] at h'
    have h2 : ((s : Y) * (t : Y)) ∈ G₁ := by simpa [mul_assoc] using h'
    exact ht1 (by simpa using G₁.mul_mem (G₁.inv_mem hs1) h2)



open CFSG.Quasithin CFSG.Quasithin.CosetGeom in
theorem burnsideF4c_pathTrans4 (t s : Y) (ht2 : t ∈ G₂) (ht1 : t ∉ G₁) (hs1 : s ∈ G₁)
    (hs2 : s ∉ G₂) (htt : t * t = 1) (hss : s * s = 1)
    (hF1 : ∀ b ∈ G₂, b ∉ G₁ → ∃ δ ∈ G₁ ⊓ G₂, t * δ * b ∈ G₁ ⊓ G₂)
    (hF2 : ∀ a ∈ G₁, a ∉ G₂ → ∃ δ ∈ G₁ ⊓ G₂, t * δ * t ∈ G₁ ⊓ G₂ ∧
      s * (t * δ * t) * a ∈ G₁ ⊓ G₂)
    (hF3 : ∀ b ∈ G₂, b ∉ G₁ → ∃ δ ∈ G₁ ⊓ G₂, t * δ * t ∈ G₁ ⊓ G₂ ∧
      s * (t * δ * t) * s ∈ G₁ ⊓ G₂ ∧ t * (s * (t * δ * t) * s) * b ∈ G₁ ⊓ G₂) :
    ∀ q q' : GPath (graph (G₁ ⊔ G₂) G₁ G₂) 4,
      q ∈ GPath.nbPaths (graph (G₁ ⊔ G₂) G₁ G₂) (γ₀ (G₁ ⊔ G₂) G₁ G₂) 4 →
      q' ∈ GPath.nbPaths (graph (G₁ ⊔ G₂) G₁ G₂) (γ₀ (G₁ ⊔ G₂) G₁ G₂) 4 →
      ∃ g : ↥(G₁ ⊔ G₂), g • γ₀ (G₁ ⊔ G₂) G₁ G₂ = γ₀ (G₁ ⊔ G₂) G₁ G₂ ∧ g • q = q' := by
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right htt
  have hsi : s⁻¹ = s := inv_eq_of_mul_eq_one_right hss
  set t' : ↥(G₁ ⊔ G₂) := ⟨t, burnsideF4c_le₂ G₁ G₂ ht2⟩ with ht'
  set s' : ↥(G₁ ⊔ G₂) := ⟨s, burnsideF4c_le₁ G₁ G₂ hs1⟩ with hs'
  have ht2' : (t' : Y) ∈ G₂ := ht2
  have ht1' : (t' : Y) ∉ G₁ := ht1
  have hs1' : (s' : Y) ∈ G₁ := hs1
  have hs2' : (s' : Y) ∉ G₂ := hs2
  set P := burnsideF4c_basePath t' s' ht2' hs1' with hP
  have hPnb : P.NoBack := burnsideF4c_basePath_noBack t' s' ht2' ht1' hs1' hs2'
  have fix0 : ∀ x : ↥(G₁ ⊔ G₂), (x : Y) ∈ G₁ →
      x • γ₀ (G₁ ⊔ G₂) G₁ G₂ = γ₀ (G₁ ⊔ G₂) G₁ G₂ := by
    intro x hx
    have hm : (x : Y) ∈ stab (γ₀ (G₁ ⊔ G₂) G₁ G₂) := by
      rw [stab_γ₀ (burnsideF4c_le₁ G₁ G₂)]; exact hx
    exact smul_eq_of_mem_stab hm
  have fix1 : ∀ x : ↥(G₁ ⊔ G₂), (x : Y) ∈ G₂ →
      x • γ₁ (G₁ ⊔ G₂) G₁ G₂ = γ₁ (G₁ ⊔ G₂) G₁ G₂ := by
    intro x hx
    have hm : (x : Y) ∈ stab (γ₁ (G₁ ⊔ G₂) G₁ G₂) := by
      rw [stab_γ₁ (burnsideF4c_le₂ G₁ G₂)]; exact hx
    exact smul_eq_of_mem_stab hm
  have hfixTake : ∀ (k : ℕ) (hk : k ≤ 4) (h : ↥(G₁ ⊔ G₂)), (∀ i ≤ k, h • P i = P i) →
      h • P.take k hk = P.take k hk := by
    intro k hk h hh
    rw [GPath.smul_eq_iff]
    intro i hi
    rw [GPath.take_apply_of_le _ _ _ hi]
    exact hh i hi
  have hTake : ∀ (k : ℕ) (hk : k ≤ 4), P.take k hk ∈
      GPath.nbPaths (graph (G₁ ⊔ G₂) G₁ G₂) (γ₀ (G₁ ⊔ G₂) G₁ G₂) k := fun k hk =>
    ⟨by rw [GPath.take_apply_of_le _ _ _ (Nat.zero_le k)]; rfl, hPnb.take k hk⟩
  have T0 : ∀ q q' : GPath (graph (G₁ ⊔ G₂) G₁ G₂) 0,
      q ∈ GPath.nbPaths (graph (G₁ ⊔ G₂) G₁ G₂) (γ₀ (G₁ ⊔ G₂) G₁ G₂) 0 →
      q' ∈ GPath.nbPaths (graph (G₁ ⊔ G₂) G₁ G₂) (γ₀ (G₁ ⊔ G₂) G₁ G₂) 0 →
      ∃ g : ↥(G₁ ⊔ G₂), g • γ₀ (G₁ ⊔ G₂) G₁ G₂ = γ₀ (G₁ ⊔ G₂) G₁ G₂ ∧ g • q = q' := by
    intro q q' hq hq'
    refine ⟨1, one_smul _ _, ?_⟩
    rw [GPath.one_smul']
    exact GPath.ext' (fun i hi => by
      have : i = 0 := by omega
      subst this
      rw [hq.1, hq'.1])
  have T1 := burnsideF4c_pathTrans_succ (Γ := graph (G₁ ⊔ G₂) G₁ G₂) (H := ↥(G₁ ⊔ G₂))
    (γ₀ (G₁ ⊔ G₂) G₁ G₂) 0 T0 (P.take 0 (by omega)) (hTake 0 (by omega))
    (γ₁ (G₁ ⊔ G₂) G₁ G₂) (by
      intro w hw _
      have hw' : (graph (G₁ ⊔ G₂) G₁ G₂).Adj (γ₀ (G₁ ⊔ G₂) G₁ G₂) w := by
        rw [GPath.take_apply_of_le _ _ _ (le_refl 0)] at hw
        exact hw
      obtain ⟨g, hg1, hg2⟩ := exists_stab_smul_eq hw' adj_γ₀_γ₁
      refine ⟨g, hfixTake 0 (by omega) g (fun i hi => ?_), hg2⟩
      have : i = 0 := by omega
      subst this
      exact hg1)
  have T2 := burnsideF4c_pathTrans_succ (Γ := graph (G₁ ⊔ G₂) G₁ G₂) (H := ↥(G₁ ⊔ G₂))
    (γ₀ (G₁ ⊔ G₂) G₁ G₂) 1 T1 (P.take 1 (by omega)) (hTake 1 (by omega))
    (t' • γ₀ (G₁ ⊔ G₂) G₁ G₂) (by
      intro w hw hwn
      have hw' : (graph (G₁ ⊔ G₂) G₁ G₂).Adj (γ₁ (G₁ ⊔ G₂) G₁ G₂) w := by
        rw [GPath.take_apply_of_le _ _ _ (le_refl 1)] at hw
        exact hw
      have hwn' : w ≠ γ₀ (G₁ ⊔ G₂) G₁ G₂ := by
        have := hwn (le_refl 1)
        rwa [show 1 - 1 = 0 from rfl, GPath.take_apply_of_le _ _ _ (Nat.zero_le 1)] at this
      obtain ⟨b, hb, hwb⟩ := (burnsideF4c_adj_smul_γ₁ G₁ G₂ 1 w).mp (by rw [one_smul]; exact hw')
      have hb1 : (b : Y) ∉ G₁ := by
        intro hb1
        apply hwn'
        rw [hwb, one_mul]
        exact fix0 b hb1
      obtain ⟨δ, hδ, hc⟩ := hF1 (b : Y) hb hb1
      set h : ↥(G₁ ⊔ G₂) := ⟨δ, burnsideF4c_le₁ G₁ G₂ hδ.1⟩ with hh
      refine ⟨h, hfixTake 1 (by omega) h (fun i hi => ?_), ?_⟩
      · interval_cases i
        · exact fix0 h hδ.1
        · exact fix1 h hδ.2
      · rw [hwb, one_mul, ← mul_smul]
        refine (burnsideF4c_smul_γ₀_eq_iff G₁ G₂ (h * b) t').mpr ?_
        have e : (((h * b)⁻¹ * t' : ↥(G₁ ⊔ G₂)) : Y) = (t * δ * b)⁻¹ := by
          simp [hh, ht', mul_inv_rev, mul_assoc, hti]
        rw [e]
        exact G₁.inv_mem hc.1)
  have T3 := burnsideF4c_pathTrans_succ (Γ := graph (G₁ ⊔ G₂) G₁ G₂) (H := ↥(G₁ ⊔ G₂))
    (γ₀ (G₁ ⊔ G₂) G₁ G₂) 2 T2 (P.take 2 (by omega)) (hTake 2 (by omega))
    ((t' * s') • γ₁ (G₁ ⊔ G₂) G₁ G₂) (by
      intro w hw hwn
      have hw' : (graph (G₁ ⊔ G₂) G₁ G₂).Adj (t' • γ₀ (G₁ ⊔ G₂) G₁ G₂) w := by
        rw [GPath.take_apply_of_le _ _ _ (le_refl 2)] at hw
        exact hw
      have hwn' : w ≠ γ₁ (G₁ ⊔ G₂) G₁ G₂ := by
        have := hwn (by omega)
        rwa [show 2 - 1 = 1 from rfl, GPath.take_apply_of_le _ _ _ (by omega)] at this
      obtain ⟨a, ha, hwa⟩ := (burnsideF4c_adj_smul_γ₀ G₁ G₂ t' w).mp hw'
      have ha2 : (a : Y) ∉ G₂ := by
        intro ha2
        apply hwn'
        rw [hwa]
        exact fix1 (t' * a) (G₂.mul_mem ht2' ha2)
      obtain ⟨δ, hδ, hδ2, hc⟩ := hF2 (a : Y) ha ha2
      set h : ↥(G₁ ⊔ G₂) := ⟨δ, burnsideF4c_le₁ G₁ G₂ hδ.1⟩ with hh
      refine ⟨h, hfixTake 2 (by omega) h (fun i hi => ?_), ?_⟩
      · interval_cases i
        · exact fix0 h hδ.1
        · exact fix1 h hδ.2
        · show h • t' • γ₀ (G₁ ⊔ G₂) G₁ G₂ = t' • γ₀ (G₁ ⊔ G₂) G₁ G₂
          rw [← mul_smul]
          refine (burnsideF4c_smul_γ₀_eq_iff G₁ G₂ (h * t') t').mpr ?_
          have e : (((h * t')⁻¹ * t' : ↥(G₁ ⊔ G₂)) : Y) = (t * δ * t)⁻¹ := by
            simp [hh, ht', mul_inv_rev, mul_assoc, hti]
          rw [e]
          exact G₁.inv_mem hδ2.1
      · rw [hwa, ← mul_smul]
        refine (burnsideF4c_smul_γ₁_eq_iff G₁ G₂ (h * (t' * a)) (t' * s')).mpr ?_
        have e : (((h * (t' * a))⁻¹ * (t' * s') : ↥(G₁ ⊔ G₂)) : Y) = (s * (t * δ * t) * a)⁻¹ := by
          simp [hh, ht', hs', mul_inv_rev, mul_assoc, hti, hsi]
        rw [e]
        exact G₂.inv_mem hc.2)
  have T4 := burnsideF4c_pathTrans_succ (Γ := graph (G₁ ⊔ G₂) G₁ G₂) (H := ↥(G₁ ⊔ G₂))
    (γ₀ (G₁ ⊔ G₂) G₁ G₂) 3 T3 (P.take 3 (by omega)) (hTake 3 (by omega))
    ((t' * s' * t') • γ₀ (G₁ ⊔ G₂) G₁ G₂) (by
      intro w hw hwn
      have hw' : (graph (G₁ ⊔ G₂) G₁ G₂).Adj ((t' * s') • γ₁ (G₁ ⊔ G₂) G₁ G₂) w := by
        rw [GPath.take_apply_of_le _ _ _ (le_refl 3)] at hw
        exact hw
      have hwn' : w ≠ t' • γ₀ (G₁ ⊔ G₂) G₁ G₂ := by
        have := hwn (by omega)
        rwa [show 3 - 1 = 2 from rfl, GPath.take_apply_of_le _ _ _ (by omega)] at this
      obtain ⟨b, hb, hwb⟩ := (burnsideF4c_adj_smul_γ₁ G₁ G₂ (t' * s') w).mp hw'
      have hb1 : (b : Y) ∉ G₁ := by
        intro hb1
        apply hwn'
        rw [hwb]
        refine (burnsideF4c_smul_γ₀_eq_iff G₁ G₂ (t' * s' * b) t').mpr ?_
        have e : (((t' * s' * b)⁻¹ * t' : ↥(G₁ ⊔ G₂)) : Y) = (b : Y)⁻¹ * s := by
          simp [ht', hs', mul_inv_rev, mul_assoc, hsi]
        rw [e]
        exact G₁.mul_mem (G₁.inv_mem hb1) hs1
      obtain ⟨δ, hδ, hδ2, hδ3, hc⟩ := hF3 (b : Y) hb hb1
      set h : ↥(G₁ ⊔ G₂) := ⟨δ, burnsideF4c_le₁ G₁ G₂ hδ.1⟩ with hh
      refine ⟨h, hfixTake 3 (by omega) h (fun i hi => ?_), ?_⟩
      · interval_cases i
        · exact fix0 h hδ.1
        · exact fix1 h hδ.2
        · show h • t' • γ₀ (G₁ ⊔ G₂) G₁ G₂ = t' • γ₀ (G₁ ⊔ G₂) G₁ G₂
          rw [← mul_smul]
          refine (burnsideF4c_smul_γ₀_eq_iff G₁ G₂ (h * t') t').mpr ?_
          have e : (((h * t')⁻¹ * t' : ↥(G₁ ⊔ G₂)) : Y) = (t * δ * t)⁻¹ := by
            simp [hh, ht', mul_inv_rev, mul_assoc, hti]
          rw [e]
          exact G₁.inv_mem hδ2.1
        · show h • (t' * s') • γ₁ (G₁ ⊔ G₂) G₁ G₂ = (t' * s') • γ₁ (G₁ ⊔ G₂) G₁ G₂
          rw [← mul_smul]
          refine (burnsideF4c_smul_γ₁_eq_iff G₁ G₂ (h * (t' * s')) (t' * s')).mpr ?_
          have e : (((h * (t' * s'))⁻¹ * (t' * s') : ↥(G₁ ⊔ G₂)) : Y) =
              (s * (t * δ * t) * s)⁻¹ := by
            simp [hh, ht', hs', mul_inv_rev, mul_assoc, hti, hsi]
          rw [e]
          exact G₂.inv_mem hδ3.2
      · rw [hwb, ← mul_smul]
        refine (burnsideF4c_smul_γ₀_eq_iff G₁ G₂ (h * (t' * s' * b)) (t' * s' * t')).mpr ?_
        have e : (((h * (t' * s' * b))⁻¹ * (t' * s' * t') : ↥(G₁ ⊔ G₂)) : Y) =
            (t * (s * (t * δ * t) * s) * b)⁻¹ := by
          simp [hh, ht', hs', mul_inv_rev, mul_assoc, hti, hsi]
        rw [e]
        exact G₁.inv_mem hc.1)
  exact T4



open CFSG.Quasithin CFSG.Quasithin.CosetGeom in
@[expose] def burnsideF4c_revPath {V : Type*} {Γ : SimpleGraph V} {n : ℕ} (p : GPath Γ n) : GPath Γ n where
  toFun i := p (n - i)
  adj i hi := by
    have h1 := p.adj (n - (i + 1)) (by omega)
    have h2 : n - (i + 1) + 1 = n - i := by omega
    rw [h2] at h1
    exact h1.symm
  tail i hi := by
    show p (n - i) = p (n - n)
    rw [Nat.sub_eq_zero_of_le hi, Nat.sub_self]

open CFSG.Quasithin CFSG.Quasithin.CosetGeom in
theorem burnsideF4c_revPath_apply {V : Type*} {Γ : SimpleGraph V} {n : ℕ} (p : GPath Γ n) {i : ℕ}
    (hi : i ≤ n) : burnsideF4c_revPath p i = p (n - i) := rfl

open CFSG.Quasithin CFSG.Quasithin.CosetGeom in
theorem burnsideF4c_revPath_injective {V : Type*} {Γ : SimpleGraph V} {n : ℕ} {p q : GPath Γ n}
    (h : burnsideF4c_revPath p = burnsideF4c_revPath q) : p = q := by
  refine GPath.ext' (fun i hi => ?_)
  have := congrArg (fun r : GPath Γ n => r (n - i)) h
  simpa [burnsideF4c_revPath, Nat.sub_sub_self hi] using this

open CFSG.Quasithin CFSG.Quasithin.CosetGeom in
theorem burnsideF4c_small_from_point
    (hsmall : ∃ p q : GPath (graph (G₁ ⊔ G₂) G₁ G₂) 3, p.IsGeodesic ∧ q.IsGeodesic ∧ p 0 = q 0 ∧
      p 3 = q 3 ∧ p ≠ q) :
    ∃ p q : GPath (graph (G₁ ⊔ G₂) G₁ G₂) 3, p.IsGeodesic ∧ q.IsGeodesic ∧
      p 0 = γ₀ (G₁ ⊔ G₂) G₁ G₂ ∧ q 0 = γ₀ (G₁ ⊔ G₂) G₁ G₂ ∧ p 3 = q 3 ∧ p ≠ q := by
  have hconn : (graph (G₁ ⊔ G₂) G₁ G₂).Connected := connected rfl
  obtain ⟨p, q, hp, hq, h0, h3, hne⟩ := hsmall
  have hpar : vtype (p 0) ≠ vtype (p 3) := by
    intro h
    have := (GPath.dist_even_iff hconn (fun a b h => vtype_ne_of_adj h) (p 0) (p 3)).mp h
    have h3' : (graph (G₁ ⊔ G₂) G₁ G₂).dist (p 0) (p 3) = 3 := hp
    rw [h3'] at this
    exact absurd this (by decide)
  obtain ⟨p', q', hp', hq', h0', h3', hne', hv⟩ : ∃ p' q' : GPath (graph (G₁ ⊔ G₂) G₁ G₂) 3,
      p'.IsGeodesic ∧ q'.IsGeodesic ∧ p' 0 = q' 0 ∧ p' 3 = q' 3 ∧ p' ≠ q' ∧
      vtype (p' 0) = false := by
    cases hv : vtype (p 0)
    · exact ⟨p, q, hp, hq, h0, h3, hne, hv⟩
    · have hv3 : vtype (p 3) = false := by
        rw [hv] at hpar
        cases h : vtype (p 3)
        · rfl
        · exact absurd h.symm hpar
      refine ⟨burnsideF4c_revPath p, burnsideF4c_revPath q, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · show (graph (G₁ ⊔ G₂) G₁ G₂).dist (burnsideF4c_revPath p 0) (burnsideF4c_revPath p 3) = 3
        simp only [burnsideF4c_revPath_apply _ (Nat.zero_le 3), burnsideF4c_revPath_apply _ le_rfl,
          Nat.sub_zero, Nat.sub_self]
        rw [SimpleGraph.dist_comm]; exact hp
      · show (graph (G₁ ⊔ G₂) G₁ G₂).dist (burnsideF4c_revPath q 0) (burnsideF4c_revPath q 3) = 3
        simp only [burnsideF4c_revPath_apply _ (Nat.zero_le 3), burnsideF4c_revPath_apply _ le_rfl,
          Nat.sub_zero, Nat.sub_self]
        rw [SimpleGraph.dist_comm]; exact hq
      · simp only [burnsideF4c_revPath_apply _ (Nat.zero_le 3)]; simpa using h3
      · simp only [burnsideF4c_revPath_apply _ (le_refl 3)]; simpa using h0
      · intro h; exact hne (burnsideF4c_revPath_injective h)
      · simp only [burnsideF4c_revPath_apply _ (Nat.zero_le 3)]; simpa using hv3
  obtain ⟨g, hg⟩ := exists_smul_eq_γ₀ (G₂ := G₂) (G₁ := G₁) (G₀ := G₁ ⊔ G₂) hv
  refine ⟨g⁻¹ • p', g⁻¹ • q', ?_, ?_, ?_, ?_, ?_, ?_⟩
  · show (graph (G₁ ⊔ G₂) G₁ G₂).dist ((g⁻¹ • p') 0) ((g⁻¹ • p') 3) = 3
    rw [GPath.smul_apply, GPath.smul_apply, GPath.dist_smul hconn]; exact hp'
  · show (graph (G₁ ⊔ G₂) G₁ G₂).dist ((g⁻¹ • q') 0) ((g⁻¹ • q') 3) = 3
    rw [GPath.smul_apply, GPath.smul_apply, GPath.dist_smul hconn]; exact hq'
  · rw [GPath.smul_apply, hg, inv_smul_smul]
  · rw [GPath.smul_apply, ← h0', hg, inv_smul_smul]
  · rw [GPath.smul_apply, GPath.smul_apply, h3']
  · intro h
    apply hne'
    refine GPath.ext' (fun i hi => ?_)
    have := (GPath.smul_eq_iff.mp (show g⁻¹ • p' = g⁻¹ • q' from h)) i hi
    rw [GPath.smul_apply] at this
    exact smul_left_cancel g⁻¹ this



open CFSG.Quasithin CFSG.Quasithin.CosetGeom in
theorem burnsideF4c_encard_gt_two {α : Type*} (S : Set α) {v₁ v₂ v₃ : α} (h1 : v₁ ∈ S) (h2 : v₂ ∈ S)
    (h3 : v₃ ∈ S) (h12 : v₁ ≠ v₂) (h13 : v₁ ≠ v₃) (h23 : v₂ ≠ v₃) : 2 < S.encard := by
  have hsub : ({v₁, v₂, v₃} : Set α) ⊆ S := by
    intro x hx
    rcases hx with rfl | rfl | rfl
    · exact h1
    · exact h2
    · exact h3
  have hc : ({v₁, v₂, v₃} : Set α).encard = 3 := by
    rw [Set.encard_insert_of_notMem (by simp [h12, h13]), Set.encard_pair h23]
    norm_num
  calc (2 : ℕ∞) < 3 := by norm_num
    _ = ({v₁, v₂, v₃} : Set α).encard := hc.symm
    _ ≤ S.encard := Set.encard_le_encard hsub

open CFSG.Quasithin CFSG.Quasithin.CosetGeom in
theorem burnsideF4c_valence0
    (hval1 : ∃ a₂ a₃ : Y, a₂ ∈ G₁ ∧ a₃ ∈ G₁ ∧ a₂ ∉ G₂ ∧ a₃ ∉ G₂ ∧ a₂⁻¹ * a₃ ∉ G₂) :
    2 < (nbrs (γ₀ (G₁ ⊔ G₂) G₁ G₂)).encard := by
  obtain ⟨a₂, a₃, ha₂, ha₃, ha₂', ha₃', ha₂₃⟩ := hval1
  set b₂ : ↥(G₁ ⊔ G₂) := ⟨a₂, burnsideF4c_le₁ G₁ G₂ ha₂⟩
  set b₃ : ↥(G₁ ⊔ G₂) := ⟨a₃, burnsideF4c_le₁ G₁ G₂ ha₃⟩
  have hadj : ∀ a : ↥(G₁ ⊔ G₂), (a : Y) ∈ G₁ →
      a • γ₁ (G₁ ⊔ G₂) G₁ G₂ ∈ nbrs (γ₀ (G₁ ⊔ G₂) G₁ G₂) := by
    intro a ha
    have := (burnsideF4c_adj_smul_γ₀ G₁ G₂ 1 (a • γ₁ (G₁ ⊔ G₂) G₁ G₂)).mpr ⟨a, ha, by rw [one_mul]⟩
    rw [one_smul] at this
    exact this
  refine burnsideF4c_encard_gt_two _ (v₁ := (1 : ↥(G₁ ⊔ G₂)) • γ₁ (G₁ ⊔ G₂) G₁ G₂)
    (v₂ := b₂ • γ₁ (G₁ ⊔ G₂) G₁ G₂) (v₃ := b₃ • γ₁ (G₁ ⊔ G₂) G₁ G₂)
    (hadj 1 (by simpa using G₁.one_mem)) (hadj b₂ ha₂) (hadj b₃ ha₃) ?_ ?_ ?_
  · intro h
    rw [burnsideF4c_smul_γ₁_eq_iff] at h
    exact ha₂' (by simpa using h)
  · intro h
    rw [burnsideF4c_smul_γ₁_eq_iff] at h
    exact ha₃' (by simpa using h)
  · intro h
    rw [burnsideF4c_smul_γ₁_eq_iff] at h
    exact ha₂₃ (by simpa using h)

open CFSG.Quasithin CFSG.Quasithin.CosetGeom in
theorem burnsideF4c_valence1
    (hval2 : ∃ b₂ b₃ : Y, b₂ ∈ G₂ ∧ b₃ ∈ G₂ ∧ b₂ ∉ G₁ ∧ b₃ ∉ G₁ ∧ b₂⁻¹ * b₃ ∉ G₁) :
    2 < (nbrs (γ₁ (G₁ ⊔ G₂) G₁ G₂)).encard := by
  obtain ⟨a₂, a₃, ha₂, ha₃, ha₂', ha₃', ha₂₃⟩ := hval2
  set b₂ : ↥(G₁ ⊔ G₂) := ⟨a₂, burnsideF4c_le₂ G₁ G₂ ha₂⟩
  set b₃ : ↥(G₁ ⊔ G₂) := ⟨a₃, burnsideF4c_le₂ G₁ G₂ ha₃⟩
  have hadj : ∀ a : ↥(G₁ ⊔ G₂), (a : Y) ∈ G₂ →
      a • γ₀ (G₁ ⊔ G₂) G₁ G₂ ∈ nbrs (γ₁ (G₁ ⊔ G₂) G₁ G₂) := by
    intro a ha
    have := (burnsideF4c_adj_smul_γ₁ G₁ G₂ 1 (a • γ₀ (G₁ ⊔ G₂) G₁ G₂)).mpr ⟨a, ha, by rw [one_mul]⟩
    rw [one_smul] at this
    exact this
  refine burnsideF4c_encard_gt_two _ (v₁ := (1 : ↥(G₁ ⊔ G₂)) • γ₀ (G₁ ⊔ G₂) G₁ G₂)
    (v₂ := b₂ • γ₀ (G₁ ⊔ G₂) G₁ G₂) (v₃ := b₃ • γ₀ (G₁ ⊔ G₂) G₁ G₂)
    (hadj 1 (by simpa using G₂.one_mem)) (hadj b₂ ha₂) (hadj b₃ ha₃) ?_ ?_ ?_
  · intro h
    rw [burnsideF4c_smul_γ₀_eq_iff] at h
    exact ha₂' (by simpa using h)
  · intro h
    rw [burnsideF4c_smul_γ₀_eq_iff] at h
    exact ha₃' (by simpa using h)
  · intro h
    rw [burnsideF4c_smul_γ₀_eq_iff] at h
    exact ha₂₃ (by simpa using h)



open CFSG.Quasithin CFSG.Quasithin.CosetGeom in
theorem burnsideF4c_geom_small (t s : Y) (ht2 : t ∈ G₂) (ht1 : t ∉ G₁) (hs1 : s ∈ G₁)
    (hs2 : s ∉ G₂) (htt : t * t = 1) (hss : s * s = 1)
    (hF1 : ∀ b ∈ G₂, b ∉ G₁ → ∃ δ ∈ G₁ ⊓ G₂, t * δ * b ∈ G₁ ⊓ G₂)
    (hF2 : ∀ a ∈ G₁, a ∉ G₂ → ∃ δ ∈ G₁ ⊓ G₂, t * δ * t ∈ G₁ ⊓ G₂ ∧
      s * (t * δ * t) * a ∈ G₁ ⊓ G₂)
    (hF3 : ∀ b ∈ G₂, b ∉ G₁ → ∃ δ ∈ G₁ ⊓ G₂, t * δ * t ∈ G₁ ⊓ G₂ ∧
      s * (t * δ * t) * s ∈ G₁ ⊓ G₂ ∧ t * (s * (t * δ * t) * s) * b ∈ G₁ ⊓ G₂)
    (hval1 : ∃ a₂ a₃ : Y, a₂ ∈ G₁ ∧ a₃ ∈ G₁ ∧ a₂ ∉ G₂ ∧ a₃ ∉ G₂ ∧ a₂⁻¹ * a₃ ∉ G₂)
    (hval2 : ∃ b₂ b₃ : Y, b₂ ∈ G₂ ∧ b₃ ∈ G₂ ∧ b₂ ∉ G₁ ∧ b₃ ∉ G₁ ∧ b₂⁻¹ * b₃ ∉ G₁)
    (hsmall : ∃ p q : GPath (graph (G₁ ⊔ G₂) G₁ G₂) 3, p.IsGeodesic ∧ q.IsGeodesic ∧ p 0 = q 0 ∧
      p 3 = q 3 ∧ p ≠ q) :
    (∀ g ∈ G₁ ⊔ G₂, g ∈ G₁ ∨ ∃ a ∈ G₁, ∃ c ∈ G₁, g = a * t * c) ∧
      (∀ a ∈ G₁, t * a * t ∈ G₁ → a ∈ G₂) := by
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right htt
  have hconn : (graph (G₁ ⊔ G₂) G₁ G₂).Connected := connected rfl
  set t' : ↥(G₁ ⊔ G₂) := ⟨t, burnsideF4c_le₂ G₁ G₂ ht2⟩ with ht'
  set s' : ↥(G₁ ⊔ G₂) := ⟨s, burnsideF4c_le₁ G₁ G₂ hs1⟩ with hs'
  have ht2' : (t' : Y) ∈ G₂ := ht2
  have ht1' : (t' : Y) ∉ G₁ := ht1
  have hs1' : (s' : Y) ∈ G₁ := hs1
  have hs2' : (s' : Y) ∉ G₂ := hs2
  set P := burnsideF4c_basePath t' s' ht2' hs1' with hP
  have hPnb : P.NoBack := burnsideF4c_basePath_noBack t' s' ht2' ht1' hs1' hs2'
  have htrans := burnsideF4c_pathTrans4 t s ht2 ht1 hs1 hs2 htt hss hF1 hF2 hF3
  have hP4 : P ∈ GPath.nbPaths (graph (G₁ ⊔ G₂) G₁ G₂) (γ₀ (G₁ ⊔ G₂) G₁ G₂) (3 + 1) := ⟨rfl, hPnb⟩
  have F := CosetGeom.lemma_F35 (burnsideF4c_valence0 hval1) (burnsideF4c_valence1 hval2)
    (u := γ₀ (G₁ ⊔ G₂) G₁ G₂) (m := 3) (by norm_num) htrans hP4
  unfold GPath.F35Conclusion at F
  obtain ⟨c11, c12, c13, c21, c22, c3, c4⟩ := F
  obtain ⟨p, q, hp, hq, hp0, hq0, hpq3, hne⟩ := burnsideF4c_small_from_point hsmall
  have hle : ∀ v, (graph (G₁ ⊔ G₂) G₁ G₂).dist (γ₀ (G₁ ⊔ G₂) G₁ G₂) v ≤ 3 := by
    rcases c3 with hi | hii
    · exfalso
      have hpnb : p ∈ GPath.nbPaths (graph (G₁ ⊔ G₂) G₁ G₂) (γ₀ (G₁ ⊔ G₂) G₁ G₂) 3 :=
        ⟨hp0, GPath.noBack_of_dist_eq hconn p hp⟩
      obtain ⟨w, hw, hext⟩ := GPath.exists_extension
        (CosetGeom.exists_nbr_ne (burnsideF4c_valence0 hval1) (burnsideF4c_valence1 hval2)) hpnb
      obtain ⟨-, hu⟩ := hi _ hext
      have e1 := hu p hp0 hp (by rw [GPath.snoc_of_le _ _ _ le_rfl])
      have e2 := hu q hq0 hq (by rw [GPath.snoc_of_le _ _ _ le_rfl, ← hpq3])
      exact hne (e1.trans e2.symm)
    · exact hii.1
  have fix0 : ∀ x : ↥(G₁ ⊔ G₂), (x : Y) ∈ G₁ →
      x • γ₀ (G₁ ⊔ G₂) G₁ G₂ = γ₀ (G₁ ⊔ G₂) G₁ G₂ := by
    intro x hx
    have hm : (x : Y) ∈ stab (γ₀ (G₁ ⊔ G₂) G₁ G₂) := by
      rw [stab_γ₀ (burnsideF4c_le₁ G₁ G₂)]; exact hx
    exact smul_eq_of_mem_stab hm
  have hdist2 : (graph (G₁ ⊔ G₂) G₁ G₂).dist (γ₀ (G₁ ⊔ G₂) G₁ G₂) (t' • γ₀ (G₁ ⊔ G₂) G₁ G₂) = 2 :=
    c11 2 (by norm_num)
  constructor
  · intro g hg
    set g' : ↥(G₁ ⊔ G₂) := ⟨g, hg⟩ with hg'
    have hpar : Even ((graph (G₁ ⊔ G₂) G₁ G₂).dist (γ₀ (G₁ ⊔ G₂) G₁ G₂)
        (g' • γ₀ (G₁ ⊔ G₂) G₁ G₂)) := by
      refine (GPath.dist_even_iff hconn (fun a b h => vtype_ne_of_adj h) _ _).mp ?_
      rw [vtype_smul]
    have hle' := hle (g' • γ₀ (G₁ ⊔ G₂) G₁ G₂)
    have hcases : (graph (G₁ ⊔ G₂) G₁ G₂).dist (γ₀ (G₁ ⊔ G₂) G₁ G₂)
        (g' • γ₀ (G₁ ⊔ G₂) G₁ G₂) = 0 ∨ (graph (G₁ ⊔ G₂) G₁ G₂).dist (γ₀ (G₁ ⊔ G₂) G₁ G₂)
        (g' • γ₀ (G₁ ⊔ G₂) G₁ G₂) = 2 := by
      obtain ⟨k, hk⟩ := hpar
      omega
    rcases hcases with h0 | h2
    · left
      have := (hconn.dist_eq_zero_iff).mp h0
      have h1 : (1 : ↥(G₁ ⊔ G₂)) • γ₀ (G₁ ⊔ G₂) G₁ G₂ = g' • γ₀ (G₁ ⊔ G₂) G₁ G₂ := by
        rw [one_smul]; exact this
      have := (burnsideF4c_smul_γ₀_eq_iff G₁ G₂ 1 g').mp h1
      simpa using this
    · right
      obtain ⟨k, hk1, hk2⟩ := c13 2 (by norm_num) _ _ hdist2 h2
      have hkG : (k : Y) ∈ G₁ := by
        have hm := mem_stab_of_smul_eq hk1
        rwa [stab_γ₀ (burnsideF4c_le₁ G₁ G₂)] at hm
      have hk3 : (k * t') • γ₀ (G₁ ⊔ G₂) G₁ G₂ = g' • γ₀ (G₁ ⊔ G₂) G₁ G₂ := by
        rw [mul_smul]; exact hk2
      have hmem := (burnsideF4c_smul_γ₀_eq_iff G₁ G₂ (k * t') g').mp hk3
      refine ⟨(k : Y), hkG, (((k * t')⁻¹ * g' : ↥(G₁ ⊔ G₂)) : Y), hmem, ?_⟩
      simp [hg', ht']
      group
  · intro a ha hta
    set a' : ↥(G₁ ⊔ G₂) := ⟨a, burnsideF4c_le₁ G₁ G₂ ha⟩ with ha'
    have hfixt : a' • t' • γ₀ (G₁ ⊔ G₂) G₁ G₂ = t' • γ₀ (G₁ ⊔ G₂) G₁ G₂ := by
      rw [← mul_smul]
      refine (burnsideF4c_smul_γ₀_eq_iff G₁ G₂ (a' * t') t').mpr ?_
      have e : (((a' * t')⁻¹ * t' : ↥(G₁ ⊔ G₂)) : Y) = (t * a * t)⁻¹ := by
        simp [ha', ht', mul_inv_rev, mul_assoc, hti]
      rw [e]
      exact G₁.inv_mem hta
    have hq0 : (a' • P.take 2 (by omega)) 0 = γ₀ (G₁ ⊔ G₂) G₁ G₂ := by
      rw [GPath.smul_apply, GPath.take_apply_of_le _ _ _ (Nat.zero_le 2)]
      exact fix0 a' ha
    have hq2 : (a' • P.take 2 (by omega)) 2 = P 2 := by
      rw [GPath.smul_apply, GPath.take_apply_of_le _ _ _ (le_refl 2)]
      exact hfixt
    have hqg : (a' • P.take 2 (by omega)).IsGeodesic := by
      show (graph (G₁ ⊔ G₂) G₁ G₂).dist ((a' • P.take 2 (by omega)) 0) ((a' • P.take 2 (by omega)) 2) = 2
      rw [hq0, hq2]
      exact hdist2
    have heq := c21 2 (by norm_num) _ hq0 hq2 hqg
    have h1 := congrArg (fun r : GPath (graph (G₁ ⊔ G₂) G₁ G₂) 2 => r 1) heq
    simp only [GPath.smul_apply, GPath.take_apply_of_le _ _ _ (show 1 ≤ 2 by norm_num)] at h1
    have hfix1 : a' • γ₁ (G₁ ⊔ G₂) G₁ G₂ = γ₁ (G₁ ⊔ G₂) G₁ G₂ := h1
    have hm := mem_stab_of_smul_eq hfix1
    rwa [stab_γ₁ (burnsideF4c_le₂ G₁ G₂)] at hm



open CFSG.Quasithin CFSG.Quasithin.CosetGeom in
theorem burnsideF4c_small_of (t s : Y) (ht2 : t ∈ G₂) (ht1 : t ∉ G₁) (hs1 : s ∈ G₁) (hs2 : s ∉ G₂)
    (hbraid : t * s * t = s * t * s) (hnadj : ∀ a ∈ G₁, a⁻¹ * (t * s) ∉ G₂) :
    ∃ p q : GPath (graph (G₁ ⊔ G₂) G₁ G₂) 3, p.IsGeodesic ∧ q.IsGeodesic ∧ p 0 = q 0 ∧
      p 3 = q 3 ∧ p ≠ q := by
  have hconn : (graph (G₁ ⊔ G₂) G₁ G₂).Connected := connected rfl
  set t' : ↥(G₁ ⊔ G₂) := ⟨t, burnsideF4c_le₂ G₁ G₂ ht2⟩ with ht'
  set s' : ↥(G₁ ⊔ G₂) := ⟨s, burnsideF4c_le₁ G₁ G₂ hs1⟩ with hs'
  have ht2' : (t' : Y) ∈ G₂ := ht2
  have ht1' : (t' : Y) ∉ G₁ := ht1
  have hs1' : (s' : Y) ∈ G₁ := hs1
  have hs2' : (s' : Y) ∉ G₂ := hs2
  set P := burnsideF4c_basePath t' s' ht2' hs1' with hP
  have fix0 : ∀ x : ↥(G₁ ⊔ G₂), (x : Y) ∈ G₁ →
      x • γ₀ (G₁ ⊔ G₂) G₁ G₂ = γ₀ (G₁ ⊔ G₂) G₁ G₂ := by
    intro x hx
    have hm : (x : Y) ∈ stab (γ₀ (G₁ ⊔ G₂) G₁ G₂) := by
      rw [stab_γ₀ (burnsideF4c_le₁ G₁ G₂)]; exact hx
    exact smul_eq_of_mem_stab hm
  have fix1 : ∀ x : ↥(G₁ ⊔ G₂), (x : Y) ∈ G₂ →
      x • γ₁ (G₁ ⊔ G₂) G₁ G₂ = γ₁ (G₁ ⊔ G₂) G₁ G₂ := by
    intro x hx
    have hm : (x : Y) ∈ stab (γ₁ (G₁ ⊔ G₂) G₁ G₂) := by
      rw [stab_γ₁ (burnsideF4c_le₂ G₁ G₂)]; exact hx
    exact smul_eq_of_mem_stab hm
  set p := P.take 3 (by omega) with hpdef
  have hp0 : p 0 = γ₀ (G₁ ⊔ G₂) G₁ G₂ := by
    rw [hpdef, GPath.take_apply_of_le _ _ _ (Nat.zero_le 3)]; rfl
  have hp1 : p 1 = γ₁ (G₁ ⊔ G₂) G₁ G₂ := by
    rw [hpdef, GPath.take_apply_of_le _ _ _ (by norm_num)]; rfl
  have hp3 : p 3 = (t' * s') • γ₁ (G₁ ⊔ G₂) G₁ G₂ := by
    rw [hpdef, GPath.take_apply_of_le _ _ _ (le_refl 3)]; rfl
  have hdist : (graph (G₁ ⊔ G₂) G₁ G₂).dist (p 0) (p 3) = 3 := by
    rw [hp0, hp3]
    have hle : (graph (G₁ ⊔ G₂) G₁ G₂).dist (p 0) (p 3) ≤ 3 := GPath.dist_le_length hconn p
    rw [hp0, hp3] at hle
    have hodd : ¬ Even ((graph (G₁ ⊔ G₂) G₁ G₂).dist (γ₀ (G₁ ⊔ G₂) G₁ G₂)
        ((t' * s') • γ₁ (G₁ ⊔ G₂) G₁ G₂)) := by
      intro hev
      have := (GPath.dist_even_iff hconn (fun a b h => vtype_ne_of_adj h) _ _).mpr hev
      rw [vtype_smul, vtype_γ₀, vtype_γ₁] at this
      exact Bool.false_ne_true this
    have hne1 : (graph (G₁ ⊔ G₂) G₁ G₂).dist (γ₀ (G₁ ⊔ G₂) G₁ G₂)
        ((t' * s') • γ₁ (G₁ ⊔ G₂) G₁ G₂) ≠ 1 := by
      intro h1
      have hadj := SimpleGraph.dist_eq_one_iff_adj.mp h1
      obtain ⟨a, ha, hw⟩ := (burnsideF4c_adj_smul_γ₀ G₁ G₂ 1 _).mp (by rw [one_smul]; exact hadj)
      rw [one_mul] at hw
      have := (burnsideF4c_smul_γ₁_eq_iff G₁ G₂ a (t' * s')).mp hw.symm
      exact hnadj a ha (by simpa [ht', hs'] using this)
    obtain ⟨k, hk⟩ := Nat.not_even_iff_odd.mp hodd
    omega
  have hq0 : (s' • p) 0 = p 0 := by
    rw [GPath.smul_apply, hp0]; exact fix0 s' hs1'
  have hq3 : (s' • p) 3 = p 3 := by
    rw [GPath.smul_apply, hp3, ← mul_smul]
    have e : s' * (t' * s') = t' * s' * t' := by
      apply Subtype.ext
      simp only [Subgroup.coe_mul, ht', hs']
      rw [← mul_assoc, ← hbraid]
    rw [e, mul_smul, fix1 t' ht2']
  refine ⟨p, s' • p, hdist, ?_, hq0.symm, hq3.symm, ?_⟩
  · show (graph (G₁ ⊔ G₂) G₁ G₂).dist ((s' • p) 0) ((s' • p) 3) = 3
    rw [hq0, hq3]; exact hdist
  · intro h
    have h1 := congrArg (fun r : GPath (graph (G₁ ⊔ G₂) G₁ G₂) 3 => r 1) h
    simp only [GPath.smul_apply, hp1] at h1
    have hm := mem_stab_of_smul_eq h1.symm
    rw [stab_γ₁ (burnsideF4c_le₂ G₁ G₂)] at hm
    exact hs2' hm

end Trans

open CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam in
abbrev burnsideF4c_Amal : RankTwoAmalgam := RankTwoAmalgam.ofSubgroups burnsideF4c_P burnsideF4c_L

open CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam in
@[expose] def burnsideF4c_ph1 {Y : Type} [Group Y] (β : burnsideF4c_Amal.Completion Y) :
    ↥burnsideF4c_P →* Y := β.φ1
open CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam in
@[expose] def burnsideF4c_ph2 {Y : Type} [Group Y] (β : burnsideF4c_Amal.Completion Y) :
    ↥burnsideF4c_L →* Y := β.φ2
open CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam in
@[expose] def burnsideF4c_ph12 {Y : Type} [Group Y] (β : burnsideF4c_Amal.Completion Y) :
    ↥(burnsideF4c_P ⊓ burnsideF4c_L) →* Y := β.φ12

section Transport

variable {Y : Type} [Group Y] (β : burnsideF4c_Amal.Completion Y)

open CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam in
theorem burnsideF4c_f1_eq_f12 (d : burnsideF4c_SL) (hd : d ∈ burnsideF4c_P ⊓ burnsideF4c_L) :
    burnsideF4c_ph1 β (⟨d, hd.1⟩ : burnsideF4c_P) =
      burnsideF4c_ph12 β (⟨d, hd⟩ : ↥(burnsideF4c_P ⊓ burnsideF4c_L)) :=
  β.comm1 ⟨d, hd⟩

open CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam in
theorem burnsideF4c_f2_eq_f12 (d : burnsideF4c_SL) (hd : d ∈ burnsideF4c_P ⊓ burnsideF4c_L) :
    burnsideF4c_ph2 β (⟨d, hd.2⟩ : burnsideF4c_L) =
      burnsideF4c_ph12 β (⟨d, hd⟩ : ↥(burnsideF4c_P ⊓ burnsideF4c_L)) :=
  β.comm2 ⟨d, hd⟩

open CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam in
theorem burnsideF4c_f1_mul (a b : burnsideF4c_SL) (ha : a ∈ burnsideF4c_P) (hb : b ∈ burnsideF4c_P) :
    burnsideF4c_ph1 β (⟨a, ha⟩ : burnsideF4c_P) * burnsideF4c_ph1 β (⟨b, hb⟩ : burnsideF4c_P) =
      burnsideF4c_ph1 β (⟨a * b, burnsideF4c_P.mul_mem ha hb⟩ : burnsideF4c_P) :=
  (map_mul (burnsideF4c_ph1 β) ⟨a, ha⟩ ⟨b, hb⟩).symm

open CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam in
theorem burnsideF4c_f2_mul (a b : burnsideF4c_SL) (ha : a ∈ burnsideF4c_L) (hb : b ∈ burnsideF4c_L) :
    burnsideF4c_ph2 β (⟨a, ha⟩ : burnsideF4c_L) * burnsideF4c_ph2 β (⟨b, hb⟩ : burnsideF4c_L) =
      burnsideF4c_ph2 β (⟨a * b, burnsideF4c_L.mul_mem ha hb⟩ : burnsideF4c_L) :=
  (map_mul (burnsideF4c_ph2 β) ⟨a, ha⟩ ⟨b, hb⟩).symm

open CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam in
theorem burnsideF4c_f12_mem (d : burnsideF4c_SL) (hd : d ∈ burnsideF4c_P ⊓ burnsideF4c_L) :
    burnsideF4c_ph12 β (⟨d, hd⟩ : ↥(burnsideF4c_P ⊓ burnsideF4c_L)) ∈
      (burnsideF4c_ph1 β).range ⊓ (burnsideF4c_ph2 β).range :=
  ⟨⟨⟨d, hd.1⟩, burnsideF4c_f1_eq_f12 β d hd⟩, ⟨⟨d, hd.2⟩, burnsideF4c_f2_eq_f12 β d hd⟩⟩

open CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam in
theorem burnsideF4c_inter_iff (g : Y) :
    g ∈ (burnsideF4c_ph1 β).range ⊓ (burnsideF4c_ph2 β).range ↔
      ∃ (d : burnsideF4c_SL) (hd : d ∈ burnsideF4c_P ⊓ burnsideF4c_L),
        g = burnsideF4c_ph12 β ⟨d, hd⟩ := by
  constructor
  · intro hg
    have : g ∈ (burnsideF4c_ph12 β).range := by
      have h := β.inter
      exact h ▸ hg
    obtain ⟨d', hd'⟩ := this
    exact ⟨d'.1, d'.2, hd'.symm⟩
  · rintro ⟨d, hd, rfl⟩
    exact burnsideF4c_f12_mem β d hd

variable {β}

open CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam in
theorem burnsideF4c_f1_mem_G2 (hβ : β.IsFaithful) (a : burnsideF4c_SL) (ha : a ∈ burnsideF4c_P) :
    burnsideF4c_ph1 β (⟨a, ha⟩ : burnsideF4c_P) ∈ (burnsideF4c_ph2 β).range ↔
      a ∈ burnsideF4c_L := by
  constructor
  · intro h
    have h1 : burnsideF4c_ph1 β (⟨a, ha⟩ : burnsideF4c_P) ∈
        (burnsideF4c_ph1 β).range ⊓ (burnsideF4c_ph2 β).range := ⟨⟨_, rfl⟩, h⟩
    obtain ⟨d, hd, hdd⟩ := (burnsideF4c_inter_iff β _).1 h1
    have h2 : burnsideF4c_ph1 β (⟨a, ha⟩ : burnsideF4c_P) =
        burnsideF4c_ph1 β (⟨d, hd.1⟩ : burnsideF4c_P) := by
      rw [hdd, burnsideF4c_f1_eq_f12 β d hd]
    have := hβ.1 h2
    have h3 : a = d := congrArg Subtype.val this
    rw [h3]; exact hd.2
  · intro hL
    exact ⟨⟨a, hL⟩, (burnsideF4c_f2_eq_f12 β a ⟨ha, hL⟩).trans
      (burnsideF4c_f1_eq_f12 β a ⟨ha, hL⟩).symm⟩

open CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam in
theorem burnsideF4c_f2_mem_G1 (hβ : β.IsFaithful) (b : burnsideF4c_SL) (hb : b ∈ burnsideF4c_L) :
    burnsideF4c_ph2 β (⟨b, hb⟩ : burnsideF4c_L) ∈ (burnsideF4c_ph1 β).range ↔
      b ∈ burnsideF4c_P := by
  constructor
  · intro h
    have h1 : burnsideF4c_ph2 β (⟨b, hb⟩ : burnsideF4c_L) ∈
        (burnsideF4c_ph1 β).range ⊓ (burnsideF4c_ph2 β).range := ⟨h, ⟨_, rfl⟩⟩
    obtain ⟨d, hd, hdd⟩ := (burnsideF4c_inter_iff β _).1 h1
    have h2 : burnsideF4c_ph2 β (⟨b, hb⟩ : burnsideF4c_L) =
        burnsideF4c_ph2 β (⟨d, hd.2⟩ : burnsideF4c_L) := by
      rw [hdd, burnsideF4c_f2_eq_f12 β d hd]
    have := hβ.2.2 h2
    have h3 : b = d := congrArg Subtype.val this
    rw [h3]; exact hd.1
  · intro hP
    exact ⟨⟨b, hP⟩, (burnsideF4c_f1_eq_f12 β b ⟨hP, hb⟩).trans
      (burnsideF4c_f2_eq_f12 β b ⟨hP, hb⟩).symm⟩

open CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam in
@[expose] def burnsideF4c_tb (β : burnsideF4c_Amal.Completion Y) : Y :=
  burnsideF4c_ph2 β (⟨burnsideF4c_t, burnsideF4c_t_mem.1⟩ : burnsideF4c_L)

open CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam in
@[expose] def burnsideF4c_sb (β : burnsideF4c_Amal.Completion Y) : Y :=
  burnsideF4c_ph1 β (⟨burnsideF4c_s, burnsideF4c_s_mem.1⟩ : burnsideF4c_P)

open CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam in
theorem burnsideF4c_tb_sq : burnsideF4c_tb β * burnsideF4c_tb β = 1 := by
  unfold burnsideF4c_tb
  rw [burnsideF4c_f2_mul β _ _ burnsideF4c_t_mem.1 burnsideF4c_t_mem.1]
  have : (⟨burnsideF4c_t * burnsideF4c_t, burnsideF4c_L.mul_mem burnsideF4c_t_mem.1 burnsideF4c_t_mem.1⟩ :
      burnsideF4c_L) = 1 := Subtype.ext burnsideF4c_t_sq
  rw [this, map_one]

open CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam in
theorem burnsideF4c_sb_sq : burnsideF4c_sb β * burnsideF4c_sb β = 1 := by
  unfold burnsideF4c_sb
  rw [burnsideF4c_f1_mul β _ _ burnsideF4c_s_mem.1 burnsideF4c_s_mem.1]
  have : (⟨burnsideF4c_s * burnsideF4c_s, burnsideF4c_P.mul_mem burnsideF4c_s_mem.1 burnsideF4c_s_mem.1⟩ :
      burnsideF4c_P) = 1 := Subtype.ext burnsideF4c_s_sq
  rw [this, map_one]

open CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam in
theorem burnsideF4c_hF1 (hβ : β.IsFaithful) :
    ∀ b ∈ (burnsideF4c_ph2 β).range, b ∉ (burnsideF4c_ph1 β).range →
      ∃ δ ∈ (burnsideF4c_ph1 β).range ⊓ (burnsideF4c_ph2 β).range,
        burnsideF4c_tb β * δ * b ∈ (burnsideF4c_ph1 β).range ⊓ (burnsideF4c_ph2 β).range := by
  rintro _ ⟨b', rfl⟩ hb
  have hbP : (b' : burnsideF4c_SL) ∉ burnsideF4c_P := fun h =>
    hb ((burnsideF4c_f2_mem_G1 hβ b' b'.2).2 h)
  have hbD : (b' : burnsideF4c_SL) ∉ burnsideF4c_P ⊓ burnsideF4c_L := fun h => hbP h.1
  obtain ⟨δ, hδ, hc⟩ := burnsideF4c_F1 b' b'.2 hbD
  refine ⟨burnsideF4c_ph12 β ⟨δ, hδ⟩, burnsideF4c_f12_mem β δ hδ, ?_⟩
  have e : burnsideF4c_tb β * burnsideF4c_ph12 β ⟨δ, hδ⟩ * burnsideF4c_ph2 β b' =
      burnsideF4c_ph12 β ⟨burnsideF4c_t * δ * (b' : burnsideF4c_SL), hc⟩ := by
    rw [← burnsideF4c_f2_eq_f12 β δ hδ, ← burnsideF4c_f2_eq_f12 β _ hc]
    unfold burnsideF4c_tb
    rw [burnsideF4c_f2_mul β _ _ burnsideF4c_t_mem.1 hδ.2]
    have := burnsideF4c_f2_mul β (burnsideF4c_t * δ) (b' : burnsideF4c_SL)
      (burnsideF4c_L.mul_mem burnsideF4c_t_mem.1 hδ.2) b'.2
    exact this
  rw [e]
  exact burnsideF4c_f12_mem β _ hc


open CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam in
theorem burnsideF4c_f12_mul_f1 (x y : burnsideF4c_SL) (hx : x ∈ burnsideF4c_P ⊓ burnsideF4c_L)
    (hy : y ∈ burnsideF4c_P) :
    burnsideF4c_ph12 β ⟨x, hx⟩ * burnsideF4c_ph1 β ⟨y, hy⟩ =
      burnsideF4c_ph1 β ⟨x * y, burnsideF4c_P.mul_mem hx.1 hy⟩ := by
  rw [← burnsideF4c_f1_eq_f12 β x hx, burnsideF4c_f1_mul β]

open CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam in
theorem burnsideF4c_f1_mul_f12 (y x : burnsideF4c_SL) (hx : x ∈ burnsideF4c_P ⊓ burnsideF4c_L)
    (hy : y ∈ burnsideF4c_P) :
    burnsideF4c_ph1 β ⟨y, hy⟩ * burnsideF4c_ph12 β ⟨x, hx⟩ =
      burnsideF4c_ph1 β ⟨y * x, burnsideF4c_P.mul_mem hy hx.1⟩ := by
  rw [← burnsideF4c_f1_eq_f12 β x hx, burnsideF4c_f1_mul β]

open CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam in
theorem burnsideF4c_f12_mul_f2 (x y : burnsideF4c_SL) (hx : x ∈ burnsideF4c_P ⊓ burnsideF4c_L)
    (hy : y ∈ burnsideF4c_L) :
    burnsideF4c_ph12 β ⟨x, hx⟩ * burnsideF4c_ph2 β ⟨y, hy⟩ =
      burnsideF4c_ph2 β ⟨x * y, burnsideF4c_L.mul_mem hx.2 hy⟩ := by
  rw [← burnsideF4c_f2_eq_f12 β x hx, burnsideF4c_f2_mul β]

open CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam in
theorem burnsideF4c_f2_mul_f12 (y x : burnsideF4c_SL) (hx : x ∈ burnsideF4c_P ⊓ burnsideF4c_L)
    (hy : y ∈ burnsideF4c_L) :
    burnsideF4c_ph2 β ⟨y, hy⟩ * burnsideF4c_ph12 β ⟨x, hx⟩ =
      burnsideF4c_ph2 β ⟨y * x, burnsideF4c_L.mul_mem hy hx.2⟩ := by
  rw [← burnsideF4c_f2_eq_f12 β x hx, burnsideF4c_f2_mul β]

open CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam in
theorem burnsideF4c_tdt (δ : burnsideF4c_SL) (hδ : δ ∈ burnsideF4c_P ⊓ burnsideF4c_L)
    (h2 : burnsideF4c_t * δ * burnsideF4c_t ∈ burnsideF4c_P ⊓ burnsideF4c_L) :
    burnsideF4c_tb β * burnsideF4c_ph12 β ⟨δ, hδ⟩ * burnsideF4c_tb β =
      burnsideF4c_ph12 β ⟨burnsideF4c_t * δ * burnsideF4c_t, h2⟩ := by
  unfold burnsideF4c_tb
  rw [burnsideF4c_f2_mul_f12 _ _ hδ burnsideF4c_t_mem.1,
    burnsideF4c_f2_mul β _ _ (burnsideF4c_L.mul_mem burnsideF4c_t_mem.1 hδ.2) burnsideF4c_t_mem.1,
    ← burnsideF4c_f2_eq_f12 β _ h2]

open CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam in
theorem burnsideF4c_hF2 (hβ : β.IsFaithful) :
    ∀ a ∈ (burnsideF4c_ph1 β).range, a ∉ (burnsideF4c_ph2 β).range →
      ∃ δ ∈ (burnsideF4c_ph1 β).range ⊓ (burnsideF4c_ph2 β).range,
        burnsideF4c_tb β * δ * burnsideF4c_tb β ∈
          (burnsideF4c_ph1 β).range ⊓ (burnsideF4c_ph2 β).range ∧
        burnsideF4c_sb β * (burnsideF4c_tb β * δ * burnsideF4c_tb β) * a ∈
          (burnsideF4c_ph1 β).range ⊓ (burnsideF4c_ph2 β).range := by
  rintro _ ⟨a', rfl⟩ ha
  have haL : (a' : burnsideF4c_SL) ∉ burnsideF4c_L := fun h =>
    ha ((burnsideF4c_f1_mem_G2 hβ a' a'.2).2 h)
  have haD : (a' : burnsideF4c_SL) ∉ burnsideF4c_P ⊓ burnsideF4c_L := fun h => haL h.2
  obtain ⟨δ, hδ, h2, h3⟩ := burnsideF4c_F2 a' a'.2 haD
  refine ⟨burnsideF4c_ph12 β ⟨δ, hδ⟩, burnsideF4c_f12_mem β δ hδ, ?_, ?_⟩
  · rw [burnsideF4c_tdt δ hδ h2]
    exact burnsideF4c_f12_mem β _ h2
  · rw [burnsideF4c_tdt δ hδ h2]
    have e : burnsideF4c_sb β * burnsideF4c_ph12 β ⟨burnsideF4c_t * δ * burnsideF4c_t, h2⟩ *
        burnsideF4c_ph1 β a' = burnsideF4c_ph12 β ⟨burnsideF4c_s * (burnsideF4c_t * δ * burnsideF4c_t) *
          (a' : burnsideF4c_SL), h3⟩ := by
      rw [← burnsideF4c_f1_eq_f12 β _ h3]
      unfold burnsideF4c_sb
      rw [burnsideF4c_f1_mul_f12 _ _ h2 burnsideF4c_s_mem.1,
        burnsideF4c_f1_mul β _ _ (burnsideF4c_P.mul_mem burnsideF4c_s_mem.1 h2.1) a'.2]
    rw [e]
    exact burnsideF4c_f12_mem β _ h3

open CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam in
theorem burnsideF4c_hF3 (hβ : β.IsFaithful) :
    ∀ b ∈ (burnsideF4c_ph2 β).range, b ∉ (burnsideF4c_ph1 β).range →
      ∃ δ ∈ (burnsideF4c_ph1 β).range ⊓ (burnsideF4c_ph2 β).range,
        burnsideF4c_tb β * δ * burnsideF4c_tb β ∈
          (burnsideF4c_ph1 β).range ⊓ (burnsideF4c_ph2 β).range ∧
        burnsideF4c_sb β * (burnsideF4c_tb β * δ * burnsideF4c_tb β) * burnsideF4c_sb β ∈
          (burnsideF4c_ph1 β).range ⊓ (burnsideF4c_ph2 β).range ∧
        burnsideF4c_tb β * (burnsideF4c_sb β * (burnsideF4c_tb β * δ * burnsideF4c_tb β) *
          burnsideF4c_sb β) * b ∈ (burnsideF4c_ph1 β).range ⊓ (burnsideF4c_ph2 β).range := by
  rintro _ ⟨b', rfl⟩ hb
  have hbP : (b' : burnsideF4c_SL) ∉ burnsideF4c_P := fun h =>
    hb ((burnsideF4c_f2_mem_G1 hβ b' b'.2).2 h)
  have hbD : (b' : burnsideF4c_SL) ∉ burnsideF4c_P ⊓ burnsideF4c_L := fun h => hbP h.1
  obtain ⟨δ, hδ, h2, h3, h4⟩ := burnsideF4c_F3 b' b'.2 hbD
  refine ⟨burnsideF4c_ph12 β ⟨δ, hδ⟩, burnsideF4c_f12_mem β δ hδ, ?_, ?_, ?_⟩
  · rw [burnsideF4c_tdt δ hδ h2]
    exact burnsideF4c_f12_mem β _ h2
  · rw [burnsideF4c_tdt δ hδ h2]
    have e : burnsideF4c_sb β * burnsideF4c_ph12 β ⟨burnsideF4c_t * δ * burnsideF4c_t, h2⟩ *
        burnsideF4c_sb β = burnsideF4c_ph12 β ⟨burnsideF4c_s * (burnsideF4c_t * δ * burnsideF4c_t) *
          burnsideF4c_s, h3⟩ := by
      rw [← burnsideF4c_f1_eq_f12 β _ h3]
      unfold burnsideF4c_sb
      rw [burnsideF4c_f1_mul_f12 _ _ h2 burnsideF4c_s_mem.1,
        burnsideF4c_f1_mul β _ _ (burnsideF4c_P.mul_mem burnsideF4c_s_mem.1 h2.1) burnsideF4c_s_mem.1]
    rw [e]
    exact burnsideF4c_f12_mem β _ h3
  · rw [burnsideF4c_tdt δ hδ h2]
    have e : burnsideF4c_sb β * burnsideF4c_ph12 β ⟨burnsideF4c_t * δ * burnsideF4c_t, h2⟩ *
        burnsideF4c_sb β = burnsideF4c_ph12 β ⟨burnsideF4c_s * (burnsideF4c_t * δ * burnsideF4c_t) *
          burnsideF4c_s, h3⟩ := by
      rw [← burnsideF4c_f1_eq_f12 β _ h3]
      unfold burnsideF4c_sb
      rw [burnsideF4c_f1_mul_f12 _ _ h2 burnsideF4c_s_mem.1,
        burnsideF4c_f1_mul β _ _ (burnsideF4c_P.mul_mem burnsideF4c_s_mem.1 h2.1) burnsideF4c_s_mem.1]
    rw [e]
    have e2 : burnsideF4c_tb β * burnsideF4c_ph12 β ⟨burnsideF4c_s * (burnsideF4c_t * δ * burnsideF4c_t) *
          burnsideF4c_s, h3⟩ * burnsideF4c_ph2 β b' =
        burnsideF4c_ph12 β ⟨burnsideF4c_t * (burnsideF4c_s * (burnsideF4c_t * δ * burnsideF4c_t) *
          burnsideF4c_s) * (b' : burnsideF4c_SL), h4⟩ := by
      rw [← burnsideF4c_f2_eq_f12 β _ h4]
      unfold burnsideF4c_tb
      rw [burnsideF4c_f2_mul_f12 _ _ h3 burnsideF4c_t_mem.1,
        burnsideF4c_f2_mul β _ _ (burnsideF4c_L.mul_mem burnsideF4c_t_mem.1 h3.2) b'.2]
    rw [e2]
    exact burnsideF4c_f12_mem β _ h4


open CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam in
theorem burnsideF4c_hval1 (hβ : β.IsFaithful) :
    ∃ a₂ a₃ : Y, a₂ ∈ (burnsideF4c_ph1 β).range ∧ a₃ ∈ (burnsideF4c_ph1 β).range ∧
      a₂ ∉ (burnsideF4c_ph2 β).range ∧ a₃ ∉ (burnsideF4c_ph2 β).range ∧
      a₂⁻¹ * a₃ ∉ (burnsideF4c_ph2 β).range := by
  obtain ⟨x, y, hx, hy, hxL, hyL, hxyL⟩ := burnsideF4c_val1
  refine ⟨burnsideF4c_ph1 β ⟨x, hx⟩, burnsideF4c_ph1 β ⟨y, hy⟩, ⟨_, rfl⟩, ⟨_, rfl⟩, ?_, ?_, ?_⟩
  · intro h; exact hxL ((burnsideF4c_f1_mem_G2 hβ x hx).1 h)
  · intro h; exact hyL ((burnsideF4c_f1_mem_G2 hβ y hy).1 h)
  · have e : (burnsideF4c_ph1 β ⟨x, hx⟩)⁻¹ * burnsideF4c_ph1 β ⟨y, hy⟩ =
        burnsideF4c_ph1 β ⟨x⁻¹ * y, burnsideF4c_P.mul_mem (burnsideF4c_P.inv_mem hx) hy⟩ := by
      rw [← map_inv, ← map_mul]; rfl
    rw [e]
    intro h
    exact hxyL ((burnsideF4c_f1_mem_G2 hβ _ _).1 h)

open CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam in
theorem burnsideF4c_hval2 (hβ : β.IsFaithful) :
    ∃ b₂ b₃ : Y, b₂ ∈ (burnsideF4c_ph2 β).range ∧ b₃ ∈ (burnsideF4c_ph2 β).range ∧
      b₂ ∉ (burnsideF4c_ph1 β).range ∧ b₃ ∉ (burnsideF4c_ph1 β).range ∧
      b₂⁻¹ * b₃ ∉ (burnsideF4c_ph1 β).range := by
  obtain ⟨x, y, hx, hy, hxP, hyP, hxyP⟩ := burnsideF4c_val2
  refine ⟨burnsideF4c_ph2 β ⟨x, hx⟩, burnsideF4c_ph2 β ⟨y, hy⟩, ⟨_, rfl⟩, ⟨_, rfl⟩, ?_, ?_, ?_⟩
  · intro h; exact hxP ((burnsideF4c_f2_mem_G1 hβ x hx).1 h)
  · intro h; exact hyP ((burnsideF4c_f2_mem_G1 hβ y hy).1 h)
  · have e : (burnsideF4c_ph2 β ⟨x, hx⟩)⁻¹ * burnsideF4c_ph2 β ⟨y, hy⟩ =
        burnsideF4c_ph2 β ⟨x⁻¹ * y, burnsideF4c_L.mul_mem (burnsideF4c_L.inv_mem hx) hy⟩ := by
      rw [← map_inv, ← map_mul]; rfl
    rw [e]
    intro h
    exact hxyP ((burnsideF4c_f2_mem_G1 hβ _ _).1 h)

open CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam in
theorem burnsideF4c_Y_decomp (hβ : β.IsFaithful) (hsmall : β.IsSmall 3) :
    (∀ g : Y, g ∈ (burnsideF4c_ph1 β).range ∨ ∃ a ∈ (burnsideF4c_ph1 β).range,
      ∃ c ∈ (burnsideF4c_ph1 β).range, g = a * burnsideF4c_tb β * c) ∧
    (∀ a ∈ (burnsideF4c_ph1 β).range, burnsideF4c_tb β * a * burnsideF4c_tb β ∈
      (burnsideF4c_ph1 β).range → a ∈ (burnsideF4c_ph2 β).range) := by
  have hsm : ∃ p q : GPath (CosetGeom.graph ((burnsideF4c_ph1 β).range ⊔ (burnsideF4c_ph2 β).range)
      (burnsideF4c_ph1 β).range (burnsideF4c_ph2 β).range) 3, p.IsGeodesic ∧ q.IsGeodesic ∧
      p 0 = q 0 ∧ p 3 = q 3 ∧ p ≠ q := by
    unfold RankTwoAmalgam.Completion.IsSmall RankTwoAmalgam.Completion.IsLarge at hsmall
    push Not at hsmall
    exact hsmall
  have ht1 : burnsideF4c_tb β ∉ (burnsideF4c_ph1 β).range := fun h =>
    burnsideF4c_t_mem.2 ⟨(burnsideF4c_f2_mem_G1 hβ _ burnsideF4c_t_mem.1).1 h, burnsideF4c_t_mem.1⟩
  have hs2 : burnsideF4c_sb β ∉ (burnsideF4c_ph2 β).range := fun h =>
    burnsideF4c_s_mem.2 ⟨burnsideF4c_s_mem.1, (burnsideF4c_f1_mem_G2 hβ _ burnsideF4c_s_mem.1).1 h⟩
  have key := burnsideF4c_geom_small (G₁ := (burnsideF4c_ph1 β).range)
    (G₂ := (burnsideF4c_ph2 β).range) (burnsideF4c_tb β) (burnsideF4c_sb β) ⟨_, rfl⟩ ht1 ⟨_, rfl⟩ hs2
    burnsideF4c_tb_sq burnsideF4c_sb_sq (burnsideF4c_hF1 hβ) (burnsideF4c_hF2 hβ)
    (burnsideF4c_hF3 hβ) (burnsideF4c_hval1 hβ) (burnsideF4c_hval2 hβ) hsm
  refine ⟨fun g => key.1 g ?_, key.2⟩
  have hgen : (burnsideF4c_ph1 β).range ⊔ (burnsideF4c_ph2 β).range = ⊤ := β.gen
  rw [hgen]; exact Subgroup.mem_top g

end Transport

section Classify

variable {Y : Type} [Group Y] {β : burnsideF4c_Amal.Completion Y}

open CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam in
@[expose] def burnsideF4c_Rel (β : burnsideF4c_Amal.Completion Y) (y : Y) (v : burnsideF4c_V) : Prop :=
  (y ∈ (burnsideF4c_ph1 β).range ∧ v = burnsideF4c_e0) ∨
    ∃ (a c : burnsideF4c_SL) (ha : a ∈ burnsideF4c_P) (hc : c ∈ burnsideF4c_P),
      y = burnsideF4c_ph1 β ⟨a, ha⟩ * burnsideF4c_tb β * burnsideF4c_ph1 β ⟨c, hc⟩ ∧
        v = a • burnsideF4c_e1

open CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam in
theorem burnsideF4c_Rel_exists (hβ : β.IsFaithful) (hsm : β.IsSmall 3) (y : Y) :
    ∃ v, burnsideF4c_Rel β y v := by
  rcases (burnsideF4c_Y_decomp hβ hsm).1 y with h | ⟨a, ⟨a', rfl⟩, c, ⟨c', rfl⟩, rfl⟩
  · exact ⟨_, Or.inl ⟨h, rfl⟩⟩
  · exact ⟨(a' : burnsideF4c_SL) • burnsideF4c_e1,
      Or.inr ⟨a', c', a'.2, c'.2, rfl, rfl⟩⟩


open CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam in
theorem burnsideF4c_tb_ph12_tb (δ : burnsideF4c_SL) (hδ : δ ∈ burnsideF4c_P ⊓ burnsideF4c_L) :
    burnsideF4c_tb β * burnsideF4c_ph12 β ⟨δ, hδ⟩ * burnsideF4c_tb β =
      burnsideF4c_ph2 β ⟨burnsideF4c_t * δ * burnsideF4c_t,
        burnsideF4c_L.mul_mem (burnsideF4c_L.mul_mem burnsideF4c_t_mem.1 hδ.2) burnsideF4c_t_mem.1⟩ := by
  unfold burnsideF4c_tb
  rw [burnsideF4c_f2_mul_f12 _ _ hδ burnsideF4c_t_mem.1,
    burnsideF4c_f2_mul β _ _ (burnsideF4c_L.mul_mem burnsideF4c_t_mem.1 hδ.2) burnsideF4c_t_mem.1]

open CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam in
theorem burnsideF4c_u_fix (hβ : β.IsFaithful) (hsm : β.IsSmall 3) (u w : burnsideF4c_SL)
    (hu : u ∈ burnsideF4c_P) (hw : w ∈ burnsideF4c_P)
    (h : burnsideF4c_ph1 β ⟨u, hu⟩ * burnsideF4c_tb β = burnsideF4c_tb β * burnsideF4c_ph1 β ⟨w, hw⟩) :
    u • burnsideF4c_e1 = burnsideF4c_e1 := by
  have hS2 := (burnsideF4c_Y_decomp hβ hsm).2
  have hW : burnsideF4c_tb β * burnsideF4c_ph1 β ⟨u, hu⟩ * burnsideF4c_tb β =
      burnsideF4c_ph1 β ⟨w, hw⟩ := by
    calc burnsideF4c_tb β * burnsideF4c_ph1 β ⟨u, hu⟩ * burnsideF4c_tb β
        = burnsideF4c_tb β * (burnsideF4c_ph1 β ⟨u, hu⟩ * burnsideF4c_tb β) := by group
      _ = burnsideF4c_tb β * (burnsideF4c_tb β * burnsideF4c_ph1 β ⟨w, hw⟩) := by rw [h]
      _ = (burnsideF4c_tb β * burnsideF4c_tb β) * burnsideF4c_ph1 β ⟨w, hw⟩ := by group
      _ = burnsideF4c_ph1 β ⟨w, hw⟩ := by rw [burnsideF4c_tb_sq, one_mul]
  have hUG2 : burnsideF4c_ph1 β ⟨u, hu⟩ ∈ (burnsideF4c_ph2 β).range :=
    hS2 _ ⟨_, rfl⟩ (by rw [hW]; exact ⟨_, rfl⟩)
  have huL : u ∈ burnsideF4c_L := (burnsideF4c_f1_mem_G2 hβ u hu).1 hUG2
  have huD : u ∈ burnsideF4c_P ⊓ burnsideF4c_L := ⟨hu, huL⟩
  have e1 : burnsideF4c_ph1 β ⟨u, hu⟩ = burnsideF4c_ph12 β ⟨u, huD⟩ :=
    burnsideF4c_f1_eq_f12 β u huD
  have h2 := burnsideF4c_tb_ph12_tb (β := β) u huD
  rw [← e1, hW] at h2
  have htut : burnsideF4c_t * u * burnsideF4c_t ∈ burnsideF4c_P :=
    (burnsideF4c_f2_mem_G1 hβ _ _).1 (by rw [← h2]; exact ⟨_, rfl⟩)
  have htutL : burnsideF4c_t * u * burnsideF4c_t ∈ burnsideF4c_L :=
    burnsideF4c_L.mul_mem (burnsideF4c_L.mul_mem burnsideF4c_t_mem.1 huL) burnsideF4c_t_mem.1
  exact ((burnsideF4c_stab_e1 u hu).2 ⟨huD, ⟨htut, htutL⟩⟩)

open CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam in
theorem burnsideF4c_Rel_unique (hβ : β.IsFaithful) (hsm : β.IsSmall 3) {y : Y}
    {v v' : burnsideF4c_V} (h : burnsideF4c_Rel β y v) (h' : burnsideF4c_Rel β y v') : v = v' := by
  have ht1 : burnsideF4c_tb β ∉ (burnsideF4c_ph1 β).range := fun h =>
    burnsideF4c_t_mem.2 ⟨(burnsideF4c_f2_mem_G1 hβ _ burnsideF4c_t_mem.1).1 h, burnsideF4c_t_mem.1⟩
  have key : ∀ (a c : burnsideF4c_SL) (ha : a ∈ burnsideF4c_P) (hc : c ∈ burnsideF4c_P),
      burnsideF4c_ph1 β ⟨a, ha⟩ * burnsideF4c_tb β * burnsideF4c_ph1 β ⟨c, hc⟩ ∈
        (burnsideF4c_ph1 β).range → False := by
    intro a c ha hc hmem
    apply ht1
    have : burnsideF4c_tb β = (burnsideF4c_ph1 β ⟨a, ha⟩)⁻¹ *
        (burnsideF4c_ph1 β ⟨a, ha⟩ * burnsideF4c_tb β * burnsideF4c_ph1 β ⟨c, hc⟩) *
        (burnsideF4c_ph1 β ⟨c, hc⟩)⁻¹ := by group
    rw [this]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ ⟨_, rfl⟩) hmem)
      (Subgroup.inv_mem _ ⟨_, rfl⟩)
  rcases h with ⟨hy, rfl⟩ | ⟨a, c, ha, hc, rfl, rfl⟩
  · rcases h' with ⟨_, rfl⟩ | ⟨a, c, ha, hc, hyy, rfl⟩
    · rfl
    · exact (key a c ha hc (hyy ▸ hy)).elim
  · rcases h' with ⟨hy, rfl⟩ | ⟨a', c', ha', hc', hyy, rfl⟩
    · exact (key a c ha hc hy).elim
    ·
      have e1 : (burnsideF4c_ph1 β ⟨a', ha'⟩)⁻¹ * burnsideF4c_ph1 β ⟨a, ha⟩ * burnsideF4c_tb β =
          burnsideF4c_tb β * (burnsideF4c_ph1 β ⟨c', hc'⟩ * (burnsideF4c_ph1 β ⟨c, hc⟩)⁻¹) := by
        have h2 : burnsideF4c_ph1 β ⟨a, ha⟩ * burnsideF4c_tb β =
            burnsideF4c_ph1 β ⟨a', ha'⟩ * burnsideF4c_tb β * burnsideF4c_ph1 β ⟨c', hc'⟩ *
              (burnsideF4c_ph1 β ⟨c, hc⟩)⁻¹ := by
          rw [← hyy]; group
        calc (burnsideF4c_ph1 β ⟨a', ha'⟩)⁻¹ * burnsideF4c_ph1 β ⟨a, ha⟩ * burnsideF4c_tb β
            = (burnsideF4c_ph1 β ⟨a', ha'⟩)⁻¹ * (burnsideF4c_ph1 β ⟨a, ha⟩ * burnsideF4c_tb β) := by group
          _ = (burnsideF4c_ph1 β ⟨a', ha'⟩)⁻¹ * (burnsideF4c_ph1 β ⟨a', ha'⟩ * burnsideF4c_tb β *
              burnsideF4c_ph1 β ⟨c', hc'⟩ * (burnsideF4c_ph1 β ⟨c, hc⟩)⁻¹) := by rw [h2]
          _ = _ := by group
      have hu : a'⁻¹ * a ∈ burnsideF4c_P := burnsideF4c_P.mul_mem (burnsideF4c_P.inv_mem ha') ha
      have hw : c' * c⁻¹ ∈ burnsideF4c_P := burnsideF4c_P.mul_mem hc' (burnsideF4c_P.inv_mem hc)
      have e2 : burnsideF4c_ph1 β ⟨a'⁻¹ * a, hu⟩ * burnsideF4c_tb β =
          burnsideF4c_tb β * burnsideF4c_ph1 β ⟨c' * c⁻¹, hw⟩ := by
        have e3 : burnsideF4c_ph1 β ⟨a'⁻¹ * a, hu⟩ =
            (burnsideF4c_ph1 β ⟨a', ha'⟩)⁻¹ * burnsideF4c_ph1 β ⟨a, ha⟩ := by
          rw [← map_inv, ← map_mul]; rfl
        have e4 : burnsideF4c_ph1 β ⟨c' * c⁻¹, hw⟩ =
            burnsideF4c_ph1 β ⟨c', hc'⟩ * (burnsideF4c_ph1 β ⟨c, hc⟩)⁻¹ := by
          rw [← map_inv, ← map_mul]; rfl
        rw [e3, e4]; exact e1
      have hfix := burnsideF4c_u_fix hβ hsm _ _ hu hw e2
      have : a = a' * (a'⁻¹ * a) := by group
      rw [this, mul_smul, hfix]


open CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam in
noncomputable def burnsideF4c_iota0 (hβ : β.IsFaithful) (hsm : β.IsSmall 3) (y : Y) :
    burnsideF4c_V := Classical.choose (burnsideF4c_Rel_exists hβ hsm y)

open CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam in
theorem burnsideF4c_iota0_rel (hβ : β.IsFaithful) (hsm : β.IsSmall 3) (y : Y) :
    burnsideF4c_Rel β y (burnsideF4c_iota0 hβ hsm y) :=
  Classical.choose_spec (burnsideF4c_Rel_exists hβ hsm y)

open CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam in
theorem burnsideF4c_iota0_eq (hβ : β.IsFaithful) (hsm : β.IsSmall 3) {y : Y} {v : burnsideF4c_V}
    (h : burnsideF4c_Rel β y v) : burnsideF4c_iota0 hβ hsm y = v :=
  burnsideF4c_Rel_unique hβ hsm (burnsideF4c_iota0_rel hβ hsm y) h

open CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam in
theorem burnsideF4c_iota0_G1 (hβ : β.IsFaithful) (hsm : β.IsSmall 3) {y : Y}
    (hy : y ∈ (burnsideF4c_ph1 β).range) : burnsideF4c_iota0 hβ hsm y = burnsideF4c_e0 :=
  burnsideF4c_iota0_eq hβ hsm (Or.inl ⟨hy, rfl⟩)

open CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam in
theorem burnsideF4c_iota0_smul (hβ : β.IsFaithful) (hsm : β.IsSmall 3) (a : burnsideF4c_SL)
    (ha : a ∈ burnsideF4c_P) (y : Y) :
    burnsideF4c_iota0 hβ hsm (burnsideF4c_ph1 β ⟨a, ha⟩ * y) = a • burnsideF4c_iota0 hβ hsm y := by
  apply burnsideF4c_iota0_eq hβ hsm
  rcases burnsideF4c_iota0_rel hβ hsm y with ⟨hy, hv⟩ | ⟨a₁, c, ha₁, hc, hyy, hv⟩
  · left
    refine ⟨Subgroup.mul_mem _ ⟨_, rfl⟩ hy, ?_⟩
    rw [hv]; exact burnsideF4c_P_fix_e0 a ha
  · right
    refine ⟨a * a₁, c, burnsideF4c_P.mul_mem ha ha₁, hc, ?_, ?_⟩
    · rw [hyy, ← mul_assoc, ← mul_assoc, burnsideF4c_f1_mul β a a₁ ha ha₁]
    · rw [hv, mul_smul]

open CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam in
theorem burnsideF4c_iota0_mul (hβ : β.IsFaithful) (hsm : β.IsSmall 3) (c : burnsideF4c_SL)
    (hc : c ∈ burnsideF4c_P) (y : Y) :
    burnsideF4c_iota0 hβ hsm (y * burnsideF4c_ph1 β ⟨c, hc⟩) = burnsideF4c_iota0 hβ hsm y := by
  apply burnsideF4c_iota0_eq hβ hsm
  rcases burnsideF4c_iota0_rel hβ hsm y with ⟨hy, hv⟩ | ⟨a₁, c₁, ha₁, hc₁, hyy, hv⟩
  · left
    exact ⟨Subgroup.mul_mem _ hy ⟨_, rfl⟩, hv⟩
  · right
    refine ⟨a₁, c₁ * c, ha₁, burnsideF4c_P.mul_mem hc₁ hc, ?_, hv⟩
    rw [hyy, mul_assoc, burnsideF4c_f1_mul β c₁ c hc₁ hc]

open CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam in
theorem burnsideF4c_iota0_tb (hβ : β.IsFaithful) (hsm : β.IsSmall 3) :
    burnsideF4c_iota0 hβ hsm (burnsideF4c_tb β) = burnsideF4c_e1 := by
  apply burnsideF4c_iota0_eq hβ hsm
  right
  refine ⟨1, 1, burnsideF4c_P.one_mem, burnsideF4c_P.one_mem, ?_, ?_⟩
  · have h1 : (⟨1, burnsideF4c_P.one_mem⟩ : burnsideF4c_P) = 1 := rfl
    rw [h1, map_one, one_mul, mul_one]
  · rw [one_smul]


open CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam in
theorem burnsideF4c_smul_e1_ne_e0 (a : burnsideF4c_SL) (ha : a ∈ burnsideF4c_P) :
    a • burnsideF4c_e1 ≠ burnsideF4c_e0 := by
  intro h
  have : a • burnsideF4c_e1 = a • burnsideF4c_e0 := by rw [h, burnsideF4c_P_fix_e0 a ha]
  exact burnsideF4c_e1_ne (smul_left_cancel a this)

open CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam in
theorem burnsideF4c_iota0_inj (hβ : β.IsFaithful) (hsm : β.IsSmall 3) {y y' : Y}
    (h : burnsideF4c_iota0 hβ hsm y = burnsideF4c_iota0 hβ hsm y') :
    y⁻¹ * y' ∈ (burnsideF4c_ph1 β).range := by
  have r := burnsideF4c_iota0_rel hβ hsm y
  have r' := burnsideF4c_iota0_rel hβ hsm y'
  rw [← h] at r'
  have htbi : (burnsideF4c_tb β)⁻¹ = burnsideF4c_tb β := inv_eq_of_mul_eq_one_right burnsideF4c_tb_sq
  rcases r with ⟨hy, hv⟩ | ⟨a, c, ha, hc, hyy, hv⟩
  · rcases r' with ⟨hy', _⟩ | ⟨a', c', ha', hc', hyy', hv'⟩
    · exact Subgroup.mul_mem _ (Subgroup.inv_mem _ hy) hy'
    · exact (burnsideF4c_smul_e1_ne_e0 a' ha' (hv'.symm.trans hv)).elim
  · rcases r' with ⟨hy', hv'⟩ | ⟨a', c', ha', hc', hyy', hv'⟩
    · exact (burnsideF4c_smul_e1_ne_e0 a ha (hv.symm.trans hv')).elim
    · have hu : a⁻¹ * a' ∈ burnsideF4c_P :=
        burnsideF4c_P.mul_mem (burnsideF4c_P.inv_mem ha) ha'
      have hfix : (a⁻¹ * a') • burnsideF4c_e1 = burnsideF4c_e1 := by
        rw [mul_smul, ← hv.symm.trans hv', inv_smul_smul]
      obtain ⟨huD, hutD⟩ := (burnsideF4c_stab_e1 _ hu).1 hfix
      have e1 : burnsideF4c_ph1 β ⟨a⁻¹ * a', hu⟩ = burnsideF4c_ph12 β ⟨a⁻¹ * a', huD⟩ :=
        burnsideF4c_f1_eq_f12 β _ huD
      have e2 := burnsideF4c_tb_ph12_tb (β := β) _ huD
      have e3 : burnsideF4c_ph1 β ⟨a⁻¹ * a', hu⟩ =
          (burnsideF4c_ph1 β ⟨a, ha⟩)⁻¹ * burnsideF4c_ph1 β ⟨a', ha'⟩ := by
        rw [← map_inv, ← map_mul]; rfl
      have e4 : burnsideF4c_ph2 β ⟨burnsideF4c_t * (a⁻¹ * a') * burnsideF4c_t,
          burnsideF4c_L.mul_mem (burnsideF4c_L.mul_mem burnsideF4c_t_mem.1 huD.2)
            burnsideF4c_t_mem.1⟩ = burnsideF4c_ph12 β ⟨burnsideF4c_t * (a⁻¹ * a') * burnsideF4c_t, hutD⟩ :=
        burnsideF4c_f2_eq_f12 β _ hutD
      have hmem : burnsideF4c_tb β * burnsideF4c_ph1 β ⟨a⁻¹ * a', hu⟩ * burnsideF4c_tb β ∈
          (burnsideF4c_ph1 β).range := by
        rw [e1, e2, e4]
        exact ⟨⟨_, hutD.1⟩, burnsideF4c_f1_eq_f12 β _ hutD⟩
      have e5 : y⁻¹ * y' = (burnsideF4c_ph1 β ⟨c, hc⟩)⁻¹ *
          (burnsideF4c_tb β * burnsideF4c_ph1 β ⟨a⁻¹ * a', hu⟩ * burnsideF4c_tb β) *
          burnsideF4c_ph1 β ⟨c', hc'⟩ := by
        rw [hyy, hyy', e3]
        simp [mul_inv_rev, htbi, mul_assoc]
      rw [e5]
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ ⟨_, rfl⟩) hmem) ⟨_, rfl⟩

open CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam in
theorem burnsideF4c_iota0_surj (hβ : β.IsFaithful) (hsm : β.IsSmall 3) (v : burnsideF4c_V) :
    ∃ y, burnsideF4c_iota0 hβ hsm y = v := by
  rcases burnsideF4c_V_orbit v with rfl | ⟨a, ha, rfl⟩
  · exact ⟨1, burnsideF4c_iota0_G1 hβ hsm (Subgroup.one_mem _)⟩
  · refine ⟨burnsideF4c_ph1 β ⟨a, ha⟩ * burnsideF4c_tb β, ?_⟩
    rw [burnsideF4c_iota0_smul, burnsideF4c_iota0_tb]

open CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam in
@[expose] noncomputable def burnsideF4c_iotaMap (hβ : β.IsFaithful) (hsm : β.IsSmall 3) :
    (Y ⧸ (burnsideF4c_ph1 β).range) → burnsideF4c_V :=
  Quotient.lift (burnsideF4c_iota0 hβ hsm) (by
    intro y y' h
    have h' : y⁻¹ * y' ∈ (burnsideF4c_ph1 β).range := QuotientGroup.leftRel_apply.mp h
    obtain ⟨c, hc⟩ := h'
    have : y' = y * burnsideF4c_ph1 β ⟨c.1, c.2⟩ := by
      have hc' : burnsideF4c_ph1 β c = y⁻¹ * y' := hc
      have : burnsideF4c_ph1 β ⟨c.1, c.2⟩ = y⁻¹ * y' := hc'
      rw [this]; group
    rw [this]
    exact (burnsideF4c_iota0_mul hβ hsm c.1 c.2 y).symm)

open CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam in
theorem burnsideF4c_iotaMap_mk (hβ : β.IsFaithful) (hsm : β.IsSmall 3) (y : Y) :
    burnsideF4c_iotaMap hβ hsm (y : Y ⧸ (burnsideF4c_ph1 β).range) = burnsideF4c_iota0 hβ hsm y := rfl

open CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam in
@[expose] noncomputable def burnsideF4c_iotaV (hβ : β.IsFaithful) (hsm : β.IsSmall 3) :
    (Y ⧸ (burnsideF4c_ph1 β).range) ≃ burnsideF4c_V :=
  Equiv.ofBijective (burnsideF4c_iotaMap hβ hsm) ⟨by
    intro q q' h
    induction q using QuotientGroup.induction_on with
    | H y =>
      induction q' using QuotientGroup.induction_on with
      | H y' =>
        exact QuotientGroup.eq.mpr (burnsideF4c_iota0_inj hβ hsm h), by
    intro v
    obtain ⟨y, hy⟩ := burnsideF4c_iota0_surj hβ hsm v
    exact ⟨(y : Y ⧸ (burnsideF4c_ph1 β).range), hy⟩⟩


open CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam in
@[expose] noncomputable def burnsideF4c_R (hβ : β.IsFaithful) (hsm : β.IsSmall 3) :
    Y →* Equiv.Perm burnsideF4c_V where
  toFun y := (burnsideF4c_iotaV hβ hsm).symm.trans
    ((MulAction.toPermHom Y (Y ⧸ (burnsideF4c_ph1 β).range) y).trans (burnsideF4c_iotaV hβ hsm))
  map_one' := by
    ext v
    simp
  map_mul' y z := by
    ext v
    simp [mul_smul]

open CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam in
theorem burnsideF4c_R_apply (hβ : β.IsFaithful) (hsm : β.IsSmall 3) (y : Y) (v : burnsideF4c_V) :
    burnsideF4c_R hβ hsm y v = burnsideF4c_iotaV hβ hsm
      (y • (burnsideF4c_iotaV hβ hsm).symm v) := rfl

open CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam in
theorem burnsideF4c_iota_mk (hβ : β.IsFaithful) (hsm : β.IsSmall 3) (y : Y) :
    burnsideF4c_iotaV hβ hsm (y : Y ⧸ (burnsideF4c_ph1 β).range) = burnsideF4c_iota0 hβ hsm y := rfl

open CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam in
theorem burnsideF4c_R_ph1 (hβ : β.IsFaithful) (hsm : β.IsSmall 3) (a : burnsideF4c_SL)
    (ha : a ∈ burnsideF4c_P) (v : burnsideF4c_V) :
    burnsideF4c_R hβ hsm (burnsideF4c_ph1 β ⟨a, ha⟩) v = a • v := by
  rw [burnsideF4c_R_apply]
  obtain ⟨q, rfl⟩ := (burnsideF4c_iotaV hβ hsm).surjective v
  rw [Equiv.symm_apply_apply]
  induction q using QuotientGroup.induction_on with
  | H y =>
    show burnsideF4c_iotaV hβ hsm ((burnsideF4c_ph1 β ⟨a, ha⟩ * y : Y) : Y ⧸ (burnsideF4c_ph1 β).range) =
      a • burnsideF4c_iotaV hβ hsm (y : Y ⧸ (burnsideF4c_ph1 β).range)
    rw [burnsideF4c_iota_mk, burnsideF4c_iota_mk, burnsideF4c_iota0_smul]

open CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam in
theorem burnsideF4c_iota_one (hβ : β.IsFaithful) (hsm : β.IsSmall 3) :
    burnsideF4c_iotaV hβ hsm ((1 : Y) : Y ⧸ (burnsideF4c_ph1 β).range) = burnsideF4c_e0 := by
  rw [burnsideF4c_iota_mk]
  exact burnsideF4c_iota0_G1 hβ hsm (Subgroup.one_mem _)

open CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam in
theorem burnsideF4c_R_tb (hβ : β.IsFaithful) (hsm : β.IsSmall 3) :
    burnsideF4c_R hβ hsm (burnsideF4c_tb β) burnsideF4c_e0 = burnsideF4c_e1 := by
  rw [burnsideF4c_R_apply]
  have : (burnsideF4c_iotaV hβ hsm).symm burnsideF4c_e0 = ((1 : Y) : Y ⧸ (burnsideF4c_ph1 β).range) := by
    rw [Equiv.symm_apply_eq]; exact (burnsideF4c_iota_one hβ hsm).symm
  rw [this]
  show burnsideF4c_iotaV hβ hsm ((burnsideF4c_tb β * 1 : Y) : Y ⧸ (burnsideF4c_ph1 β).range) = _
  rw [burnsideF4c_iota_mk, mul_one, burnsideF4c_iota0_tb]

open CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam in
theorem burnsideF4c_R_ker (hβ : β.IsFaithful) (hsm : β.IsSmall 3) {y : Y}
    (h : burnsideF4c_R hβ hsm y = 1) : y ∈ (burnsideF4c_ph1 β).range := by
  have h1 : burnsideF4c_R hβ hsm y burnsideF4c_e0 = burnsideF4c_e0 := by rw [h]; rfl
  have h0 : (burnsideF4c_iotaV hβ hsm).symm burnsideF4c_e0 = ((1 : Y) : Y ⧸ (burnsideF4c_ph1 β).range) := by
    rw [Equiv.symm_apply_eq]; exact (burnsideF4c_iota_one hβ hsm).symm
  rw [burnsideF4c_R_apply, h0] at h1
  have h3 : burnsideF4c_iotaV hβ hsm (y • ((1 : Y) : Y ⧸ (burnsideF4c_ph1 β).range)) =
      burnsideF4c_iotaV hβ hsm ((1 : Y) : Y ⧸ (burnsideF4c_ph1 β).range) := by
    rw [h1, burnsideF4c_iota_one]
  have h4 := (burnsideF4c_iotaV hβ hsm).injective h3
  have h5 : ((y * 1 : Y) : Y ⧸ (burnsideF4c_ph1 β).range) = ((1 : Y) : Y ⧸ (burnsideF4c_ph1 β).range) := h4
  have h6 := QuotientGroup.eq.mp h5
  have h7 : (y * 1)⁻¹ * 1 ∈ (burnsideF4c_ph1 β).range := h6
  simp only [mul_one, one_mul] at h7
  simpa using Subgroup.inv_mem _ h7


open CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam in
theorem burnsideF4c_R_ph2_D (hβ : β.IsFaithful) (hsm : β.IsSmall 3) (d : burnsideF4c_SL)
    (hd : d ∈ burnsideF4c_P ⊓ burnsideF4c_L) (v : burnsideF4c_V) :
    burnsideF4c_R hβ hsm (burnsideF4c_ph2 β ⟨d, hd.2⟩) v = d • v := by
  rw [burnsideF4c_f2_eq_f12 β d hd, ← burnsideF4c_f1_eq_f12 β d hd]
  exact burnsideF4c_R_ph1 hβ hsm d hd.1 v

open CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam in
theorem burnsideF4c_extend (hβ : β.IsFaithful) (hsm : β.IsSmall 3) (g : burnsideF4c_SL ≃* burnsideF4c_SL)
    (hgD : ∀ d ∈ burnsideF4c_P ⊓ burnsideF4c_L, g d = d)
    (hgL : ∀ x ∈ burnsideF4c_L, g x ∈ burnsideF4c_L) (hgL' : ∀ x ∈ burnsideF4c_L, g.symm x ∈ burnsideF4c_L)
    (hgt : ∀ v, burnsideF4c_R hβ hsm (burnsideF4c_tb β) v = g burnsideF4c_t • v) :
    ∃ e : Y ≃* burnsideF4c_SL, (∀ (a : burnsideF4c_SL) (ha : a ∈ burnsideF4c_P),
        e (burnsideF4c_ph1 β ⟨a, ha⟩) = a) ∧
      (∀ (b : burnsideF4c_SL) (hb : b ∈ burnsideF4c_L), e (burnsideF4c_ph2 β ⟨b, hb⟩) = g b) := by
  set R := burnsideF4c_R hβ hsm with hR
  have hRL : ∀ (x : burnsideF4c_SL) (hx : x ∈ burnsideF4c_L) (v : burnsideF4c_V),
      R (burnsideF4c_ph2 β ⟨x, hx⟩) v = g x • v := by
    intro x hx v
    by_cases hxP : x ∈ burnsideF4c_P
    · rw [burnsideF4c_R_ph2_D hβ hsm x ⟨hxP, hx⟩ v, hgD x ⟨hxP, hx⟩]
    · obtain ⟨δ, hδ, hc⟩ := burnsideF4c_F1 x hx (fun h => hxP h.1)
      have hδi : δ⁻¹ ∈ burnsideF4c_P ⊓ burnsideF4c_L := (burnsideF4c_P ⊓ burnsideF4c_L).inv_mem hδ
      have hxeq : x = δ⁻¹ * burnsideF4c_t * (burnsideF4c_t * δ * x) := by
        calc x = δ⁻¹ * (burnsideF4c_t * burnsideF4c_t) * δ * x := by
              rw [burnsideF4c_t_sq]; group
          _ = δ⁻¹ * burnsideF4c_t * (burnsideF4c_t * δ * x) := by group
      have hph : burnsideF4c_ph2 β ⟨x, hx⟩ = burnsideF4c_ph2 β ⟨δ⁻¹, hδi.2⟩ * burnsideF4c_tb β *
          burnsideF4c_ph2 β ⟨burnsideF4c_t * δ * x, hc.2⟩ := by
        unfold burnsideF4c_tb
        rw [burnsideF4c_f2_mul β _ _ hδi.2 burnsideF4c_t_mem.1,
          burnsideF4c_f2_mul β _ _ (burnsideF4c_L.mul_mem hδi.2 burnsideF4c_t_mem.1) hc.2]
        congr 1
        exact Subtype.ext hxeq
      rw [hph, map_mul, map_mul]
      simp only [Equiv.Perm.mul_apply]
      rw [burnsideF4c_R_ph2_D hβ hsm _ hc v, hgt, burnsideF4c_R_ph2_D hβ hsm _ hδi]
      have hgx : g x = δ⁻¹ * g burnsideF4c_t * (burnsideF4c_t * δ * x) := by
        conv_lhs => rw [hxeq]
        rw [map_mul, map_mul, hgD _ hδi, hgD _ hc]
      rw [hgx]
      simp only [mul_smul]
  have hRmem : ∀ y : Y, R y ∈ burnsideF4c_nat.range := by
    have hsup : (burnsideF4c_ph1 β).range ⊔ (burnsideF4c_ph2 β).range ≤
        burnsideF4c_nat.range.comap R := by
      refine sup_le ?_ ?_
      · rintro _ ⟨⟨a, ha⟩, rfl⟩
        refine ⟨a, ?_⟩
        ext v
        rw [burnsideF4c_nat_apply, burnsideF4c_R_ph1 hβ hsm a ha v]
      · rintro _ ⟨⟨b, hb⟩, rfl⟩
        refine ⟨g b, ?_⟩
        ext v
        rw [burnsideF4c_nat_apply, hRL b hb v]
    intro y
    have hgen : (burnsideF4c_ph1 β).range ⊔ (burnsideF4c_ph2 β).range = ⊤ := β.gen
    have hy : y ∈ (burnsideF4c_ph1 β).range ⊔ (burnsideF4c_ph2 β).range := by
      rw [hgen]; exact Subgroup.mem_top y
    exact hsup hy
  let eHom : Y →* burnsideF4c_SL := (MonoidHom.ofInjective burnsideF4c_nat_injective).symm.toMonoidHom.comp
    (R.codRestrict burnsideF4c_nat.range hRmem)
  have heR : ∀ y, burnsideF4c_nat (eHom y) = R y := by
    intro y
    exact MonoidHom.apply_ofInjective_symm burnsideF4c_nat_injective ⟨R y, hRmem y⟩
  have he1 : ∀ (a : burnsideF4c_SL) (ha : a ∈ burnsideF4c_P), eHom (burnsideF4c_ph1 β ⟨a, ha⟩) = a := by
    intro a ha
    apply burnsideF4c_nat_injective
    rw [heR]
    ext v
    rw [burnsideF4c_R_ph1 hβ hsm a ha v, burnsideF4c_nat_apply]
  have he2 : ∀ (b : burnsideF4c_SL) (hb : b ∈ burnsideF4c_L),
      eHom (burnsideF4c_ph2 β ⟨b, hb⟩) = g b := by
    intro b hb
    apply burnsideF4c_nat_injective
    rw [heR]
    ext v
    rw [hRL b hb v, burnsideF4c_nat_apply]
  have hinj : Function.Injective eHom := by
    rw [injective_iff_map_eq_one]
    intro y hy
    have hRy : R y = 1 := by rw [← heR, hy, map_one]
    obtain ⟨⟨a, ha⟩, rfl⟩ := burnsideF4c_R_ker hβ hsm hRy
    have := he1 a ha
    rw [hy] at this
    have ha1 : (⟨a, ha⟩ : burnsideF4c_P) = 1 := Subtype.ext this.symm
    rw [ha1, map_one]
  have hsurj : Function.Surjective eHom := by
    have hle : burnsideF4c_P ⊔ burnsideF4c_L ≤ eHom.range := by
      refine sup_le ?_ ?_
      · intro a ha
        exact ⟨burnsideF4c_ph1 β ⟨a, ha⟩, he1 a ha⟩
      · intro b hb
        exact ⟨burnsideF4c_ph2 β ⟨g.symm b, hgL' b hb⟩, by rw [he2]; simp⟩
    rw [burnsideF4c_P_sup_L] at hle
    intro x
    exact hle (Subgroup.mem_top x)
  exact ⟨MulEquiv.ofBijective eHom ⟨hinj, hsurj⟩, he1, he2⟩


open CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam in
theorem burnsideF4c_classify (hβ : β.IsFaithful) (hsm : β.IsSmall 3) :
    (∃ e : Y ≃* burnsideF4c_SL, (∀ (a : burnsideF4c_SL) (ha : a ∈ burnsideF4c_P),
        e (burnsideF4c_ph1 β ⟨a, ha⟩) = a) ∧
      (∀ (b : burnsideF4c_SL) (hb : b ∈ burnsideF4c_L), e (burnsideF4c_ph2 β ⟨b, hb⟩) = b)) ∨
    (∃ e : Y ≃* burnsideF4c_SL, (∀ (a : burnsideF4c_SL) (ha : a ∈ burnsideF4c_P),
        e (burnsideF4c_ph1 β ⟨a, ha⟩) = a) ∧
      (∀ (b : burnsideF4c_SL) (hb : b ∈ burnsideF4c_L),
        e (burnsideF4c_ph2 β ⟨b, hb⟩) = burnsideF4c_z * b * burnsideF4c_z⁻¹)) := by
  set R := burnsideF4c_R hβ hsm with hR
  have haD := burnsideF4c_a_mem
  have hbD := burnsideF4c_b_mem
  have haiD : burnsideF4c_a⁻¹ ∈ burnsideF4c_P ⊓ burnsideF4c_L := (burnsideF4c_P ⊓ burnsideF4c_L).inv_mem haD
  have hbiD : burnsideF4c_b⁻¹ ∈ burnsideF4c_P ⊓ burnsideF4c_L := (burnsideF4c_P ⊓ burnsideF4c_L).inv_mem hbD
  have htL := burnsideF4c_t_mem.1
  set p := R (burnsideF4c_tb β) with hp
  have r1 : p * p = 1 := by
    rw [hp, ← map_mul, burnsideF4c_tb_sq, map_one]
  have r2 : R (burnsideF4c_ph2 β ⟨burnsideF4c_a⁻¹, haiD.2⟩) * p * R (burnsideF4c_ph2 β ⟨burnsideF4c_b⁻¹, hbiD.2⟩) *
      p * R (burnsideF4c_ph2 β ⟨burnsideF4c_a⁻¹, haiD.2⟩) = 1 := by
    have hrel : (⟨burnsideF4c_a⁻¹, haiD.2⟩ : burnsideF4c_L) * ⟨burnsideF4c_t, htL⟩ *
        ⟨burnsideF4c_b⁻¹, hbiD.2⟩ * ⟨burnsideF4c_t, htL⟩ * ⟨burnsideF4c_a⁻¹, haiD.2⟩ = 1 :=
      Subtype.ext burnsideF4c_rel2
    have := congrArg (fun x : burnsideF4c_L => R (burnsideF4c_ph2 β x)) hrel
    simp only [map_mul, map_one] at this
    exact this
  have r3 : (p * R (burnsideF4c_ph2 β ⟨burnsideF4c_a, haD.2⟩)) * (p * R (burnsideF4c_ph2 β ⟨burnsideF4c_a, haD.2⟩)) *
      (p * R (burnsideF4c_ph2 β ⟨burnsideF4c_a, haD.2⟩)) = 1 := by
    have hrel : ((⟨burnsideF4c_t, htL⟩ : burnsideF4c_L) * ⟨burnsideF4c_a, haD.2⟩) *
        (⟨burnsideF4c_t, htL⟩ * ⟨burnsideF4c_a, haD.2⟩) * (⟨burnsideF4c_t, htL⟩ * ⟨burnsideF4c_a, haD.2⟩) = 1 :=
      Subtype.ext burnsideF4c_rel3
    have := congrArg (fun x : burnsideF4c_L => R (burnsideF4c_ph2 β x)) hrel
    simp only [map_mul, map_one] at this
    exact this
  choose f hf using fun i => burnsideF4c_vecOf_bijective.2 (p (burnsideF4c_vecOf i))
  have hfi : ∀ i, p (burnsideF4c_vecOf i) = burnsideF4c_vecOf (f i) := fun i => (hf i).symm
  have vinj := burnsideF4c_vecOf_bijective.1
  have hf3 : f 3 = 1 := by
    apply vinj
    rw [← hfi, ← burnsideF4c_e0_eq, ← burnsideF4c_e1_eq]
    exact burnsideF4c_R_tb hβ hsm
  have R1 : ∀ i, f (f i) = i := by
    intro i
    apply vinj
    have := congrArg (fun σ : Equiv.Perm burnsideF4c_V => σ (burnsideF4c_vecOf i)) r1
    simp only [Equiv.Perm.mul_apply, Equiv.Perm.coe_one, id] at this
    rw [hfi, hfi] at this
    exact this
  have hf1 : f 1 = 3 := by
    have := R1 3
    rwa [hf3] at this
  have hnaD : ∀ (d : burnsideF4c_SL) (hd : d ∈ burnsideF4c_P ⊓ burnsideF4c_L) (v : burnsideF4c_V),
      R (burnsideF4c_ph2 β ⟨d, hd.2⟩) v = d • v := fun d hd v => burnsideF4c_R_ph2_D hβ hsm d hd v
  have R2 : ∀ i, burnsideF4c_tabAi (f (burnsideF4c_tabB (f (burnsideF4c_tabAi i)))) = i := by
    intro i
    apply vinj
    have := congrArg (fun σ : Equiv.Perm burnsideF4c_V => σ (burnsideF4c_vecOf i)) r2
    simp only [Equiv.Perm.mul_apply, Equiv.Perm.coe_one, id] at this
    have s1 : R (burnsideF4c_ph2 β ⟨burnsideF4c_a⁻¹, haiD.2⟩) (burnsideF4c_vecOf i) =
        burnsideF4c_vecOf (burnsideF4c_tabAi i) := by rw [hnaD _ haiD, burnsideF4c_tabAi_spec]
    have s2 := hfi (burnsideF4c_tabAi i)
    have s3 : R (burnsideF4c_ph2 β ⟨burnsideF4c_b⁻¹, hbiD.2⟩) (burnsideF4c_vecOf (f (burnsideF4c_tabAi i))) =
        burnsideF4c_vecOf (burnsideF4c_tabB (f (burnsideF4c_tabAi i))) := by
      rw [hnaD _ hbiD, burnsideF4c_tabB_spec]
    have s4 := hfi (burnsideF4c_tabB (f (burnsideF4c_tabAi i)))
    have s5 : R (burnsideF4c_ph2 β ⟨burnsideF4c_a⁻¹, haiD.2⟩)
        (burnsideF4c_vecOf (f (burnsideF4c_tabB (f (burnsideF4c_tabAi i))))) =
        burnsideF4c_vecOf (burnsideF4c_tabAi (f (burnsideF4c_tabB (f (burnsideF4c_tabAi i))))) := by
      rw [hnaD _ haiD, burnsideF4c_tabAi_spec]
    rw [s1, s2, s3, s4, s5] at this
    exact this
  have R3 : ∀ i, f (burnsideF4c_tabA (f (burnsideF4c_tabA (f (burnsideF4c_tabA i))))) = i := by
    intro i
    apply vinj
    have := congrArg (fun σ : Equiv.Perm burnsideF4c_V => σ (burnsideF4c_vecOf i)) r3
    simp only [Equiv.Perm.mul_apply, Equiv.Perm.coe_one, id] at this
    have sA : ∀ j, R (burnsideF4c_ph2 β ⟨burnsideF4c_a, haD.2⟩) (burnsideF4c_vecOf j) =
        burnsideF4c_vecOf (burnsideF4c_tabA j) := by
      intro j; rw [hnaD _ haD, burnsideF4c_tabA_spec]
    rw [sA, hfi, sA, hfi, sA, hfi] at this
    exact this
  have hfT : f = burnsideF4c_tmpl (f 0) (f 2) (f 4) (f 5) (f 6) := by
    funext i
    fin_cases i
    · rfl
    · simpa [burnsideF4c_tmpl] using hf1
    · rfl
    · simpa [burnsideF4c_tmpl] using hf3
    · rfl
    · rfl
    · rfl
  have hcl := burnsideF4c_classify_tab (f 0) (f 2) (f 4) (f 5) (f 6) (by rw [← hfT]; exact R1)
    (by rw [← hfT]; exact R2) (by rw [← hfT]; exact R3)
  rw [← hfT] at hcl
  have hzL := burnsideF4c_z_mem.2
  rcases hcl with hT | hZ
  · left
    obtain ⟨e, he1, he2⟩ := burnsideF4c_extend hβ hsm (MulEquiv.refl burnsideF4c_SL)
      (fun d hd => rfl) (fun x hx => hx) (fun x hx => hx) (by
        intro v
        obtain ⟨i, rfl⟩ := burnsideF4c_vecOf_bijective.2 v
        show p (burnsideF4c_vecOf i) = burnsideF4c_t • burnsideF4c_vecOf i
        rw [hfi, hT, burnsideF4c_tabT_spec])
    exact ⟨e, he1, fun b hb => he2 b hb⟩
  · right
    obtain ⟨e, he1, he2⟩ := burnsideF4c_extend hβ hsm (MulAut.conj burnsideF4c_z)
      (fun d hd => by
        rw [MulAut.conj_apply, burnsideF4c_z_central d hd]
        exact mul_inv_cancel_right d burnsideF4c_z)
      (fun x hx => by
        rw [MulAut.conj_apply]
        exact burnsideF4c_L.mul_mem (burnsideF4c_L.mul_mem hzL hx) (burnsideF4c_L.inv_mem hzL))
      (fun x hx => by
        rw [MulAut.conj_symm_apply]
        exact burnsideF4c_L.mul_mem (burnsideF4c_L.mul_mem (burnsideF4c_L.inv_mem hzL) hx) hzL)
      (by
        intro v
        obtain ⟨i, rfl⟩ := burnsideF4c_vecOf_bijective.2 v
        show p (burnsideF4c_vecOf i) = (burnsideF4c_z * burnsideF4c_t * burnsideF4c_z⁻¹) •
          burnsideF4c_vecOf i
        rw [hfi, hZ, burnsideF4c_tabZTZ_spec])
    exact ⟨e, he1, fun b hb => by rw [he2 b hb, MulAut.conj_apply]⟩

end Classify

open CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam in
theorem burnsideF4c_braid : burnsideF4c_t * burnsideF4c_s * burnsideF4c_t =
    burnsideF4c_s * burnsideF4c_t * burnsideF4c_s := by decide +kernel

open CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam in
theorem burnsideF4c_nadj : ∀ a : burnsideF4c_SL, a ∈ burnsideF4c_P →
    a⁻¹ * (burnsideF4c_t * burnsideF4c_s) ∉ burnsideF4c_L := by decide +kernel

open CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam in
theorem burnsideF4c_st3 : (burnsideF4c_s * burnsideF4c_t) * (burnsideF4c_s * burnsideF4c_t) *
    (burnsideF4c_s * burnsideF4c_t) = 1 := by decide +kernel

open CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam in
theorem burnsideF4c_szt3 : (burnsideF4c_s * (burnsideF4c_z * burnsideF4c_t * burnsideF4c_z⁻¹)) *
    (burnsideF4c_s * (burnsideF4c_z * burnsideF4c_t * burnsideF4c_z⁻¹)) *
    (burnsideF4c_s * (burnsideF4c_z * burnsideF4c_t * burnsideF4c_z⁻¹)) ≠ 1 := by decide +kernel

open CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam in
theorem burnsideF4c_beta1_inter : burnsideF4c_P.subtype.range ⊓ burnsideF4c_L.subtype.range =
    (burnsideF4c_P ⊓ burnsideF4c_L).subtype.range := by
  rw [Subgroup.range_subtype, Subgroup.range_subtype, Subgroup.range_subtype]

open CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam in
theorem burnsideF4c_beta1_gen : burnsideF4c_P.subtype.range ⊔ burnsideF4c_L.subtype.range = ⊤ := by
  rw [Subgroup.range_subtype, Subgroup.range_subtype]
  exact burnsideF4c_P_sup_L

open CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam in
@[expose] def burnsideF4c_beta1 : burnsideF4c_Amal.Completion burnsideF4c_SL where
  φ1 := burnsideF4c_P.subtype
  φ12 := (burnsideF4c_P ⊓ burnsideF4c_L).subtype
  φ2 := burnsideF4c_L.subtype
  comm1 _ := rfl
  comm2 _ := rfl
  inter := burnsideF4c_beta1_inter
  gen := burnsideF4c_beta1_gen

open CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam in
@[expose] def burnsideF4c_cz : ↥burnsideF4c_L →* ↥burnsideF4c_L :=
  (MulAut.conj (⟨burnsideF4c_z, burnsideF4c_z_mem.2⟩ : ↥burnsideF4c_L)).toMonoidHom

open CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam in
theorem burnsideF4c_cz_apply (b : ↥burnsideF4c_L) :
    (burnsideF4c_cz b : burnsideF4c_SL) = burnsideF4c_z * (b : burnsideF4c_SL) * burnsideF4c_z⁻¹ := rfl

open CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam in
theorem burnsideF4c_cz_range (x : burnsideF4c_SL) :
    x ∈ (burnsideF4c_L.subtype.comp burnsideF4c_cz).range ↔ x ∈ burnsideF4c_L := by
  constructor
  · rintro ⟨b, rfl⟩
    exact burnsideF4c_L.mul_mem (burnsideF4c_L.mul_mem burnsideF4c_z_mem.2 b.2)
      (burnsideF4c_L.inv_mem burnsideF4c_z_mem.2)
  · intro hx
    have hz := burnsideF4c_z_mem.2
    refine ⟨⟨burnsideF4c_z⁻¹ * x * burnsideF4c_z, burnsideF4c_L.mul_mem
      (burnsideF4c_L.mul_mem (burnsideF4c_L.inv_mem hz) hx) hz⟩, ?_⟩
    show burnsideF4c_z * (burnsideF4c_z⁻¹ * x * burnsideF4c_z) * burnsideF4c_z⁻¹ = x
    group

open CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam in
theorem burnsideF4c_cz_range_eq : (burnsideF4c_L.subtype.comp burnsideF4c_cz).range = burnsideF4c_L := by
  ext x; exact burnsideF4c_cz_range x

open CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam in
theorem burnsideF4c_cz_injective : Function.Injective burnsideF4c_cz :=
  (MulAut.conj (⟨burnsideF4c_z, burnsideF4c_z_mem.2⟩ : ↥burnsideF4c_L)).injective

open CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam in
theorem burnsideF4c_beta2_comm2 (d : ↥(burnsideF4c_P ⊓ burnsideF4c_L)) :
    (burnsideF4c_L.subtype.comp burnsideF4c_cz) (Subgroup.inclusion inf_le_right d) =
      (burnsideF4c_P ⊓ burnsideF4c_L).subtype d := by
  show burnsideF4c_z * (d : burnsideF4c_SL) * burnsideF4c_z⁻¹ = d
  rw [burnsideF4c_z_central d d.2]
  exact mul_inv_cancel_right _ _

open CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam in
theorem burnsideF4c_beta2_inter : burnsideF4c_P.subtype.range ⊓
    (burnsideF4c_L.subtype.comp burnsideF4c_cz).range = (burnsideF4c_P ⊓ burnsideF4c_L).subtype.range := by
  rw [burnsideF4c_cz_range_eq, Subgroup.range_subtype, Subgroup.range_subtype]

open CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam in
theorem burnsideF4c_beta2_gen : burnsideF4c_P.subtype.range ⊔
    (burnsideF4c_L.subtype.comp burnsideF4c_cz).range = ⊤ := by
  rw [burnsideF4c_cz_range_eq, Subgroup.range_subtype]
  exact burnsideF4c_P_sup_L

open CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam in
@[expose] def burnsideF4c_beta2 : burnsideF4c_Amal.Completion burnsideF4c_SL where
  φ1 := burnsideF4c_P.subtype
  φ12 := (burnsideF4c_P ⊓ burnsideF4c_L).subtype
  φ2 := burnsideF4c_L.subtype.comp burnsideF4c_cz
  comm1 _ := rfl
  comm2 d := burnsideF4c_beta2_comm2 d
  inter := burnsideF4c_beta2_inter
  gen := burnsideF4c_beta2_gen

open CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam in
theorem burnsideF4c_beta1_faithful : burnsideF4c_beta1.IsFaithful :=
  ⟨Subtype.val_injective, Subtype.val_injective, Subtype.val_injective⟩

open CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam in
theorem burnsideF4c_beta2_faithful : burnsideF4c_beta2.IsFaithful :=
  ⟨Subtype.val_injective, Subtype.val_injective,
    Subtype.val_injective.comp burnsideF4c_cz_injective⟩


open CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam in
theorem burnsideF4c_beta1_range1 (a : burnsideF4c_SL) :
    a ∈ burnsideF4c_beta1.φ1.range ↔ a ∈ burnsideF4c_P :=
  ⟨fun ⟨x, hx⟩ => hx ▸ Subtype.property (p := (· ∈ burnsideF4c_P)) x, fun h => ⟨⟨a, h⟩, rfl⟩⟩

open CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam in
theorem burnsideF4c_beta1_range2 (a : burnsideF4c_SL) :
    a ∈ burnsideF4c_beta1.φ2.range ↔ a ∈ burnsideF4c_L :=
  ⟨fun ⟨x, hx⟩ => hx ▸ Subtype.property (p := (· ∈ burnsideF4c_L)) x, fun h => ⟨⟨a, h⟩, rfl⟩⟩

open CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam in
theorem burnsideF4c_beta2_range1 (a : burnsideF4c_SL) :
    a ∈ burnsideF4c_beta2.φ1.range ↔ a ∈ burnsideF4c_P :=
  ⟨fun ⟨x, hx⟩ => hx ▸ Subtype.property (p := (· ∈ burnsideF4c_P)) x, fun h => ⟨⟨a, h⟩, rfl⟩⟩

open CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam in
theorem burnsideF4c_beta2_range2 (a : burnsideF4c_SL) :
    a ∈ burnsideF4c_beta2.φ2.range ↔ a ∈ burnsideF4c_L := burnsideF4c_cz_range a

open CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam in
theorem burnsideF4c_beta1_small : burnsideF4c_beta1.IsSmall 3 := by
  intro hL
  have ht1 : burnsideF4c_t ∉ burnsideF4c_beta1.φ1.range := fun h =>
    burnsideF4c_t_mem.2 ⟨(burnsideF4c_beta1_range1 _).1 h, burnsideF4c_t_mem.1⟩
  have hs2 : burnsideF4c_s ∉ burnsideF4c_beta1.φ2.range := fun h =>
    burnsideF4c_s_mem.2 ⟨burnsideF4c_s_mem.1, (burnsideF4c_beta1_range2 _).1 h⟩
  have hnadj : ∀ a ∈ burnsideF4c_beta1.φ1.range, a⁻¹ * (burnsideF4c_t * burnsideF4c_s) ∉
      burnsideF4c_beta1.φ2.range := fun a ha h =>
    burnsideF4c_nadj a ((burnsideF4c_beta1_range1 a).1 ha) ((burnsideF4c_beta1_range2 _).1 h)
  obtain ⟨p, q, hp, hq, h0, h3, hne⟩ := burnsideF4c_small_of
    (G₁ := burnsideF4c_beta1.φ1.range) (G₂ := burnsideF4c_beta1.φ2.range) burnsideF4c_t
    burnsideF4c_s ((burnsideF4c_beta1_range2 _).2 burnsideF4c_t_mem.1) ht1
    ((burnsideF4c_beta1_range1 _).2 burnsideF4c_s_mem.1) hs2 burnsideF4c_braid hnadj
  exact hne (hL p q hp hq h0 h3)

open CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam in
theorem burnsideF4c_beta2_small : burnsideF4c_beta2.IsSmall 3 := by
  intro hL
  have ht1 : burnsideF4c_t ∉ burnsideF4c_beta2.φ1.range := fun h =>
    burnsideF4c_t_mem.2 ⟨(burnsideF4c_beta2_range1 _).1 h, burnsideF4c_t_mem.1⟩
  have hs2 : burnsideF4c_s ∉ burnsideF4c_beta2.φ2.range := fun h =>
    burnsideF4c_s_mem.2 ⟨burnsideF4c_s_mem.1, (burnsideF4c_beta2_range2 _).1 h⟩
  have hnadj : ∀ a ∈ burnsideF4c_beta2.φ1.range, a⁻¹ * (burnsideF4c_t * burnsideF4c_s) ∉
      burnsideF4c_beta2.φ2.range := fun a ha h =>
    burnsideF4c_nadj a ((burnsideF4c_beta2_range1 a).1 ha) ((burnsideF4c_beta2_range2 _).1 h)
  obtain ⟨p, q, hp, hq, h0, h3, hne⟩ := burnsideF4c_small_of
    (G₁ := burnsideF4c_beta2.φ1.range) (G₂ := burnsideF4c_beta2.φ2.range) burnsideF4c_t
    burnsideF4c_s ((burnsideF4c_beta2_range2 _).2 burnsideF4c_t_mem.1) ht1
    ((burnsideF4c_beta2_range1 _).2 burnsideF4c_s_mem.1) hs2 burnsideF4c_braid hnadj
  exact hne (hL p q hp hq h0 h3)

open CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam in
theorem burnsideF4c_beta_not_equiv :
    ¬ Amalgam.Completion.IsEquivalent burnsideF4c_beta1.toCompletion burnsideF4c_beta2.toCompletion := by
  rintro ⟨θ, hθ⟩
  have h1 : ∀ a : ↥burnsideF4c_P, θ (a : burnsideF4c_SL) = (a : burnsideF4c_SL) := fun a => hθ RankTwoIndex.one a
  have h2 : ∀ b : ↥burnsideF4c_L, θ (b : burnsideF4c_SL) =
      burnsideF4c_z * (b : burnsideF4c_SL) * burnsideF4c_z⁻¹ := fun b => hθ RankTwoIndex.two b
  have hs := h1 ⟨burnsideF4c_s, burnsideF4c_s_mem.1⟩
  have ht := h2 ⟨burnsideF4c_t, burnsideF4c_t_mem.1⟩
  have := congrArg θ burnsideF4c_st3
  rw [map_one] at this
  simp only [map_mul] at this
  change θ burnsideF4c_s * θ burnsideF4c_t * (θ burnsideF4c_s * θ burnsideF4c_t) *
    (θ burnsideF4c_s * θ burnsideF4c_t) = 1 at this
  rw [hs, ht] at this
  exact burnsideF4c_szt3 this


open CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam in
theorem burnsideF4c_partB_concrete :
    ∃ (Y₁ Y₂ : Type) (_ : Group Y₁) (_ : Group Y₂) (β₁ : burnsideF4c_Amal.Completion Y₁)
      (β₂ : burnsideF4c_Amal.Completion Y₂),
      β₁.IsFaithful ∧ β₂.IsFaithful ∧ β₁.IsSmall 3 ∧ β₂.IsSmall 3 ∧
      ¬ Amalgam.Completion.IsEquivalent β₁.toCompletion β₂.toCompletion ∧
      ∀ (Y : Type) [Group Y] (β : burnsideF4c_Amal.Completion Y), β.IsFaithful → β.IsSmall 3 →
        Amalgam.Completion.IsEquivalent β.toCompletion β₁.toCompletion ∨
          Amalgam.Completion.IsEquivalent β.toCompletion β₂.toCompletion := by
  refine ⟨burnsideF4c_SL, burnsideF4c_SL, inferInstance, inferInstance, burnsideF4c_beta1,
    burnsideF4c_beta2, burnsideF4c_beta1_faithful, burnsideF4c_beta2_faithful,
    burnsideF4c_beta1_small, burnsideF4c_beta2_small, burnsideF4c_beta_not_equiv, ?_⟩
  intro Y _ β hβ hsm
  rcases burnsideF4c_classify hβ hsm with ⟨e, he1, he2⟩ | ⟨e, he1, he2⟩
  · left
    refine ⟨e, fun d x => ?_⟩
    cases d
    · exact he1 (x : ↥burnsideF4c_P).1 (x : ↥burnsideF4c_P).2
    · exact he2 (x : ↥burnsideF4c_L).1 (x : ↥burnsideF4c_L).2
    · have hx : (x : ↥(burnsideF4c_P ⊓ burnsideF4c_L)).1 ∈ burnsideF4c_P :=
        (x : ↥(burnsideF4c_P ⊓ burnsideF4c_L)).2.1
      have := he1 (x : ↥(burnsideF4c_P ⊓ burnsideF4c_L)).1 hx
      exact (congrArg e (β.comm1 x).symm).trans this
  · right
    refine ⟨e, fun d x => ?_⟩
    cases d
    · exact he1 (x : ↥burnsideF4c_P).1 (x : ↥burnsideF4c_P).2
    · exact he2 (x : ↥burnsideF4c_L).1 (x : ↥burnsideF4c_L).2
    · have hx : (x : ↥(burnsideF4c_P ⊓ burnsideF4c_L)).1 ∈ burnsideF4c_P :=
        (x : ↥(burnsideF4c_P ⊓ burnsideF4c_L)).2.1
      have := he1 (x : ↥(burnsideF4c_P ⊓ burnsideF4c_L)).1 hx
      exact (congrArg e (β.comm1 x).symm).trans this

section PartA

variable {E : Type} [Group E] {M₁ M₂ : Subgroup E}

open CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam in
@[expose] def burnsideF4c_mkAut (a1 : MulAut ↥M₁) (a12 : MulAut ↥(M₁ ⊓ M₂)) (a2 : MulAut ↥M₂)
    (c1 : ∀ x : ↥(M₁ ⊓ M₂), Subgroup.inclusion (inf_le_left : M₁ ⊓ M₂ ≤ M₁) (a12 x) =
      a1 (Subgroup.inclusion (inf_le_left : M₁ ⊓ M₂ ≤ M₁) x))
    (c2 : ∀ x : ↥(M₁ ⊓ M₂), Subgroup.inclusion (inf_le_right : M₁ ⊓ M₂ ≤ M₂) (a12 x) =
      a2 (Subgroup.inclusion (inf_le_right : M₁ ⊓ M₂ ≤ M₂) x)) :
    Amalgam.Aut (RankTwoAmalgam.ofSubgroups M₁ M₂).toAmalgam :=
  ⟨fun d => match d with
    | RankTwoIndex.one => a1
    | RankTwoIndex.two => a2
    | RankTwoIndex.onetwo => a12, by
    intro d e h x
    cases d <;> cases e
    · rfl
    · exact h.elim
    · exact h.elim
    · exact h.elim
    · rfl
    · exact h.elim
    · exact c1 x
    · exact c2 x
    · rfl⟩

open CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam in
theorem burnsideF4c_mkAut_one (a1 : MulAut ↥M₁) (a12 : MulAut ↥(M₁ ⊓ M₂)) (a2 : MulAut ↥M₂) (c1 c2) :
    (burnsideF4c_mkAut a1 a12 a2 c1 c2).1 RankTwoIndex.one = a1 := rfl


open CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam in
@[expose] def burnsideF4c_F49A (E : Type) [Group E] (M₁ M₂ : Subgroup E) : Prop :=
  ∃ tau : Amalgam.Aut (RankTwoAmalgam.ofSubgroups M₁ M₂).toAmalgam,
    tau ≠ 1 ∧ tau * tau = 1 ∧
    (∀ pointElement : ↥M₁, tau.1 .one pointElement = pointElement) ∧
    (∃ centralInvolution ∈ CFSG.Open.pCoreOf 2 (M₁ ⊓ M₂) ⊓
        Subgroup.centralizer ((CFSG.Open.pCoreOf 2 (M₁ ⊓ M₂) : Subgroup E) : Set E),
      centralInvolution ≠ 1 ∧ centralInvolution * centralInvolution = 1 ∧
      ∀ lineElement : ↥M₂, M₂.subtype (tau.1 .two lineElement) =
        centralInvolution * (lineElement : E) * centralInvolution⁻¹) ∧
    ∃ autEquiv : (↥(CFSG.Open.pCoreOf 2 (M₁ ⊓ M₂)) × Multiplicative (ZMod 2)) ≃*
        Amalgam.Aut (RankTwoAmalgam.ofSubgroups M₁ M₂).toAmalgam,
      autEquiv (1, Multiplicative.ofAdd (1 : ZMod 2)) = tau ∧
      (∀ sylowElement : ↥(CFSG.Open.pCoreOf 2 (M₁ ⊓ M₂)), ∀ pointElement : ↥M₁,
        M₁.subtype ((autEquiv (sylowElement, 1)).1 .one pointElement) =
          (sylowElement : E) * (pointElement : E) * (sylowElement : E)⁻¹) ∧
      (∀ sylowElement : ↥(CFSG.Open.pCoreOf 2 (M₁ ⊓ M₂)), ∀ lineElement : ↥M₂,
        M₂.subtype ((autEquiv (sylowElement, 1)).1 .two lineElement) =
          (sylowElement : E) * (lineElement : E) * (sylowElement : E)⁻¹)

open CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam in
structure burnsideF4c_L2Iface (E : Type) [Group E] (M₁ M₂ : Subgroup E) : Prop where
  pgroup : IsPGroup 2 ↥(M₁ ⊓ M₂)
  zdata : ∃ z : E, z ∈ M₁ ⊓ M₂ ∧ z ≠ 1 ∧ z * z = 1 ∧ (∀ b ∈ M₁ ⊓ M₂, z * b = b * z) ∧
    (∀ b ∈ M₁ ⊓ M₂, (∀ b' ∈ M₁ ⊓ M₂, b * b' = b' * b) → b = 1 ∨ b = z) ∧
    ∃ m ∈ M₂, z * m ≠ m * z
  cen1 : ∀ g ∈ M₁, (∀ m ∈ M₁, g * m = m * g) → g = 1
  cen2 : ∀ g ∈ M₂, (∀ m ∈ M₂, g * m = m * g) → g = 1
  norm1 : ∀ g ∈ M₁, (∀ b ∈ M₁ ⊓ M₂, g * b * g⁻¹ ∈ M₁ ⊓ M₂) → g ∈ M₁ ⊓ M₂
  norm2 : ∀ g ∈ M₂, (∀ b ∈ M₁ ⊓ M₂, g * b * g⁻¹ ∈ M₁ ⊓ M₂) → g ∈ M₁ ⊓ M₂
  inn1 : ∀ φ : MulAut ↥M₁, ∃ g : ↥M₁, ∀ m : ↥M₁, φ m = g * m * g⁻¹
  inn2 : ∀ φ : MulAut ↥M₂, ∃ g : ↥M₂, ∀ m : ↥M₂, φ m = g * m * g⁻¹

open CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam in
theorem burnsideF4c_pCoreOf_eq_self {B : Subgroup E} (hp : IsPGroup 2 ↥B) :
    CFSG.Open.pCoreOf 2 B = B := by
  apply le_antisymm (Subgroup.map_subtype_le _)
  intro b hb
  have htop : (⊤ : Subgroup ↥B) ≤ CFSG.pCore 2 ↥B := by
    refine le_sSup ⟨⟨fun x hx g => ?_⟩, hp.of_equiv Subgroup.topEquiv.symm⟩
    exact Subgroup.mem_top _
  exact ⟨⟨b, hb⟩, htop (Subgroup.mem_top _), rfl⟩

open CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam in
@[expose] def burnsideF4c_autOf (s w : E) (hs : s ∈ M₁ ⊓ M₂) (hw : w ∈ M₂)
    (hcomm : ∀ b ∈ M₁ ⊓ M₂, s * b * s⁻¹ = w * b * w⁻¹) :
    Amalgam.Aut (RankTwoAmalgam.ofSubgroups M₁ M₂).toAmalgam :=
  burnsideF4c_mkAut (MulAut.conj (⟨s, hs.1⟩ : ↥M₁)) (MulAut.conj (⟨s, hs⟩ : ↥(M₁ ⊓ M₂)))
    (MulAut.conj (⟨w, hw⟩ : ↥M₂))
    (fun x => Subtype.ext (by simp [MulAut.conj_apply]))
    (fun x => Subtype.ext (by simpa [MulAut.conj_apply] using hcomm x x.2))

open CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam in
theorem burnsideF4c_autOf_one (s w : E) (hs : s ∈ M₁ ⊓ M₂) (hw : w ∈ M₂) (hcomm) (m : ↥M₁) :
    M₁.subtype ((burnsideF4c_autOf s w hs hw hcomm).1 RankTwoIndex.one m) = s * M₁.subtype m * s⁻¹ := rfl

open CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam in
theorem burnsideF4c_autOf_two (s w : E) (hs : s ∈ M₁ ⊓ M₂) (hw : w ∈ M₂) (hcomm) (m : ↥M₂) :
    M₂.subtype ((burnsideF4c_autOf s w hs hw hcomm).1 RankTwoIndex.two m) = w * M₂.subtype m * w⁻¹ := rfl

open CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam in
theorem burnsideF4c_autOf_onetwo (s w : E) (hs : s ∈ M₁ ⊓ M₂) (hw : w ∈ M₂) (hcomm)
    (m : ↥(M₁ ⊓ M₂)) :
    (M₁ ⊓ M₂).subtype ((burnsideF4c_autOf s w hs hw hcomm).1 RankTwoIndex.onetwo m) =
      s * (M₁ ⊓ M₂).subtype m * s⁻¹ := rfl

open CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam in
theorem burnsideF4c_aut_ext {a b : Amalgam.Aut (RankTwoAmalgam.ofSubgroups M₁ M₂).toAmalgam}
    (h1 : ∀ m : ↥M₁, a.1 RankTwoIndex.one m = b.1 RankTwoIndex.one m)
    (h2 : ∀ m : ↥M₂, a.1 RankTwoIndex.two m = b.1 RankTwoIndex.two m)
    (h12 : ∀ m : ↥(M₁ ⊓ M₂), a.1 RankTwoIndex.onetwo m = b.1 RankTwoIndex.onetwo m) : a = b := by
  apply Subtype.ext
  funext d
  cases d
  · exact MulEquiv.ext h1
  · exact MulEquiv.ext h2
  · exact MulEquiv.ext h12


open CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam in
theorem burnsideF4c_partA_of_iface (h : burnsideF4c_L2Iface E M₁ M₂) : burnsideF4c_F49A E M₁ M₂ := by
  obtain ⟨z, hzB, hz1, hzz, hzc, hcB, m0, hm0, hzm0⟩ := h.zdata
  have hS : CFSG.Open.pCoreOf 2 (M₁ ⊓ M₂) = M₁ ⊓ M₂ := burnsideF4c_pCoreOf_eq_self h.pgroup
  have hSB : ∀ s ∈ CFSG.Open.pCoreOf 2 (M₁ ⊓ M₂), s ∈ M₁ ⊓ M₂ := fun s hs => hS ▸ hs
  have hBS : ∀ s ∈ M₁ ⊓ M₂, s ∈ CFSG.Open.pCoreOf 2 (M₁ ⊓ M₂) := fun s hs => by
    rw [hS]; exact hs
  have hzi : z⁻¹ = z := inv_eq_of_mul_eq_one_right hzz
  let cc : Multiplicative (ZMod 2) → E := fun ε => if ε = 1 then 1 else z
  have hε : ∀ ε : Multiplicative (ZMod 2), ε = 1 ∨ ε = Multiplicative.ofAdd 1 := by decide
  have hgne : (Multiplicative.ofAdd (1 : ZMod 2)) ≠ 1 := by decide
  have hgg : (Multiplicative.ofAdd (1 : ZMod 2)) * Multiplicative.ofAdd 1 = 1 := by decide
  have hcc1 : cc 1 = 1 := by simp [cc]
  have hccg : cc (Multiplicative.ofAdd 1) = z := by simp [cc, hgne]
  have hccB : ∀ ε, cc ε ∈ M₁ ⊓ M₂ := by
    intro ε
    rcases hε ε with rfl | rfl
    · rw [hcc1]; exact (M₁ ⊓ M₂).one_mem
    · rw [hccg]; exact hzB
  have hccc : ∀ ε, ∀ b ∈ M₁ ⊓ M₂, cc ε * b = b * cc ε := by
    intro ε b hb
    rcases hε ε with rfl | rfl
    · rw [hcc1, one_mul, mul_one]
    · rw [hccg]; exact hzc b hb
  have hccmul : ∀ ε ε', cc (ε * ε') = cc ε * cc ε' := by
    intro ε ε'
    rcases hε ε with rfl | rfl <;> rcases hε ε' with rfl | rfl
    · simp [hcc1]
    · simp [hcc1]
    · simp [hcc1]
    · rw [hgg, hcc1, hccg, hzz]
  have hcomm : ∀ (s : E), s ∈ M₁ ⊓ M₂ → ∀ ε, ∀ b ∈ M₁ ⊓ M₂,
      s * b * s⁻¹ = (s * cc ε) * b * (s * cc ε)⁻¹ := by
    intro s hs ε b hb
    calc s * b * s⁻¹ = s * (b * cc ε) * (cc ε)⁻¹ * s⁻¹ := by group
      _ = s * (cc ε * b) * (cc ε)⁻¹ * s⁻¹ := by rw [hccc ε b hb]
      _ = (s * cc ε) * b * (s * cc ε)⁻¹ := by group
  have hw2 : ∀ (s : E), s ∈ M₁ ⊓ M₂ → ∀ ε, s * cc ε ∈ M₂ := fun s hs ε =>
    M₂.mul_mem hs.2 (hccB ε).2
  let fAut : ∀ (s : E), s ∈ M₁ ⊓ M₂ → Multiplicative (ZMod 2) →
      Amalgam.Aut (RankTwoAmalgam.ofSubgroups M₁ M₂).toAmalgam :=
    fun s hs ε => burnsideF4c_autOf s (s * cc ε) hs (hw2 s hs ε) (hcomm s hs ε)
  have hmul : ∀ (s s' : E) (hs : s ∈ M₁ ⊓ M₂) (hs' : s' ∈ M₁ ⊓ M₂) (ε ε' : Multiplicative (ZMod 2)),
      fAut (s * s') ((M₁ ⊓ M₂).mul_mem hs hs') (ε * ε') = fAut s hs ε * fAut s' hs' ε' := by
    intro s s' hs hs' ε ε'
    have hwmul : (s * s') * cc (ε * ε') = (s * cc ε) * (s' * cc ε') := by
      rw [hccmul]
      calc s * s' * (cc ε * cc ε') = s * (s' * cc ε) * cc ε' := by group
        _ = s * (cc ε * s') * cc ε' := by rw [hccc ε s' hs']
        _ = s * cc ε * (s' * cc ε') := by group
    apply burnsideF4c_aut_ext
    · intro m
      apply Subtype.ext
      show (s * s') * (m : E) * (s * s')⁻¹ = s * (s' * (m : E) * s'⁻¹) * s⁻¹
      group
    · intro m
      apply Subtype.ext
      show ((s * s') * cc (ε * ε')) * (m : E) * ((s * s') * cc (ε * ε'))⁻¹ =
        (s * cc ε) * ((s' * cc ε') * (m : E) * (s' * cc ε')⁻¹) * (s * cc ε)⁻¹
      rw [hwmul]; group
    · intro m
      apply Subtype.ext
      show (s * s') * (m : E) * (s * s')⁻¹ = s * (s' * (m : E) * s'⁻¹) * s⁻¹
      group
  let φ : (↥(CFSG.Open.pCoreOf 2 (M₁ ⊓ M₂)) × Multiplicative (ZMod 2)) →*
      Amalgam.Aut (RankTwoAmalgam.ofSubgroups M₁ M₂).toAmalgam :=
    { toFun := fun x => fAut (x.1 : E) (hSB _ x.1.2) x.2
      map_one' := by
        apply burnsideF4c_aut_ext
        · intro m
          apply Subtype.ext
          show (1 : E) * (m : E) * (1 : E)⁻¹ = m
          group
        · intro m
          apply Subtype.ext
          show ((1 : E) * cc 1) * (m : E) * ((1 : E) * cc 1)⁻¹ = m
          rw [hcc1]; group
        · intro m
          apply Subtype.ext
          show (1 : E) * (m : E) * (1 : E)⁻¹ = m
          group
      map_mul' := fun x y => hmul _ _ (hSB _ x.1.2) (hSB _ y.1.2) x.2 y.2 }
  have hinj : Function.Injective φ := by
    rw [injective_iff_map_eq_one]
    rintro ⟨⟨s, hsS⟩, ε⟩ hφ
    have hsB := hSB s hsS
    have h1 : ∀ m : ↥M₁, s * (m : E) * s⁻¹ = m := by
      intro m
      exact congrArg (fun a : Amalgam.Aut (RankTwoAmalgam.ofSubgroups M₁ M₂).toAmalgam =>
        M₁.subtype (a.1 RankTwoIndex.one m)) hφ
    have hs1 : s = 1 := h.cen1 s hsB.1 (fun m hm => mul_inv_eq_iff_eq_mul.mp (h1 ⟨m, hm⟩))
    have hε1 : ε = 1 := by
      by_contra hne
      have hεg : ε = Multiplicative.ofAdd 1 := (hε ε).resolve_left hne
      have h2 : ∀ m : ↥M₂, (s * cc ε) * (m : E) * (s * cc ε)⁻¹ = m := by
        intro m
        exact congrArg (fun a : Amalgam.Aut (RankTwoAmalgam.ofSubgroups M₁ M₂).toAmalgam =>
          M₂.subtype (a.1 RankTwoIndex.two m)) hφ
      have h3 := h2 ⟨m0, hm0⟩
      rw [hs1, hεg, hccg] at h3
      apply hzm0
      have : z * m0 * z⁻¹ = m0 := by simpa using h3
      exact mul_inv_eq_iff_eq_mul.mp this
    exact Prod.ext (Subtype.ext hs1) hε1
  have hsurj : Function.Surjective φ := by
    intro a
    obtain ⟨g, hg⟩ := h.inn1 (a.1 RankTwoIndex.one)
    obtain ⟨k, hk⟩ := h.inn2 (a.1 RankTwoIndex.two)
    have c1 : ∀ x : ↥(M₁ ⊓ M₂), Subgroup.inclusion (inf_le_left : M₁ ⊓ M₂ ≤ M₁)
        (a.1 RankTwoIndex.onetwo x) = a.1 RankTwoIndex.one
        (Subgroup.inclusion (inf_le_left : M₁ ⊓ M₂ ≤ M₁) x) :=
      fun x => Amalgam.Aut.comm a (show RankTwoIndex.onetwo ≤ RankTwoIndex.one from trivial) x
    have c2 : ∀ x : ↥(M₁ ⊓ M₂), Subgroup.inclusion (inf_le_right : M₁ ⊓ M₂ ≤ M₂)
        (a.1 RankTwoIndex.onetwo x) = a.1 RankTwoIndex.two
        (Subgroup.inclusion (inf_le_right : M₁ ⊓ M₂ ≤ M₂) x) :=
      fun x => Amalgam.Aut.comm a (show RankTwoIndex.onetwo ≤ RankTwoIndex.two from trivial) x
    have hgb : ∀ b (hb : b ∈ M₁ ⊓ M₂), (g : E) * b * (g : E)⁻¹ =
        (M₁ ⊓ M₂).subtype (a.1 RankTwoIndex.onetwo ⟨b, hb⟩) := by
      intro b hb
      have e1 := hg (Subgroup.inclusion (inf_le_left : M₁ ⊓ M₂ ≤ M₁) ⟨b, hb⟩)
      exact (congrArg Subtype.val ((c1 ⟨b, hb⟩).trans e1)).symm
    have hkb : ∀ b (hb : b ∈ M₁ ⊓ M₂), (k : E) * b * (k : E)⁻¹ =
        (M₁ ⊓ M₂).subtype (a.1 RankTwoIndex.onetwo ⟨b, hb⟩) := by
      intro b hb
      have e1 := hk (Subgroup.inclusion (inf_le_right : M₁ ⊓ M₂ ≤ M₂) ⟨b, hb⟩)
      exact (congrArg Subtype.val ((c2 ⟨b, hb⟩).trans e1)).symm
    have hgB : (g : E) ∈ M₁ ⊓ M₂ := h.norm1 g g.2 (fun b hb => by
      rw [hgb b hb]
      exact Subtype.property (p := (· ∈ M₁ ⊓ M₂)) (a.1 RankTwoIndex.onetwo ⟨b, hb⟩))
    have hkB : (k : E) ∈ M₁ ⊓ M₂ := h.norm2 k k.2 (fun b hb => by
      rw [hkb b hb]
      exact Subtype.property (p := (· ∈ M₁ ⊓ M₂)) (a.1 RankTwoIndex.onetwo ⟨b, hb⟩))
    have hkgB : (k : E)⁻¹ * g ∈ M₁ ⊓ M₂ := (M₁ ⊓ M₂).mul_mem ((M₁ ⊓ M₂).inv_mem hkB) hgB
    have hcommk : ∀ b ∈ M₁ ⊓ M₂, ((k : E)⁻¹ * g) * b = b * ((k : E)⁻¹ * g) := by
      intro b hb
      have e : (g : E) * b * (g : E)⁻¹ = (k : E) * b * (k : E)⁻¹ := (hgb b hb).trans (hkb b hb).symm
      have e2 : (g : E) * b = (k : E) * b * (k : E)⁻¹ * g := by
        rw [← e]; group
      calc ((k : E)⁻¹ * g) * b = (k : E)⁻¹ * ((g : E) * b) := by group
        _ = (k : E)⁻¹ * ((k : E) * b * (k : E)⁻¹ * g) := by rw [← e2]
        _ = b * ((k : E)⁻¹ * g) := by group
    have hgs : (g : E) ∈ CFSG.Open.pCoreOf 2 (M₁ ⊓ M₂) := hBS _ hgB
    rcases hcB _ hkgB hcommk with hk1 | hkz
    · refine ⟨(⟨g, hgs⟩, 1), ?_⟩
      have hgk : (g : E) = k := by
        have : (k : E)⁻¹ * g = 1 := hk1
        calc (g : E) = (k : E) * ((k : E)⁻¹ * g) := by group
          _ = k := by rw [this, mul_one]
      apply burnsideF4c_aut_ext
      · intro m
        apply Subtype.ext
        exact (congrArg (fun x : ↥M₁ => (x : E)) (hg m)).symm
      · intro m
        apply Subtype.ext
        show ((g : E) * cc 1) * (m : E) * ((g : E) * cc 1)⁻¹ = M₂.subtype (a.1 RankTwoIndex.two m)
        rw [hcc1, mul_one, hgk]
        exact (congrArg (fun x : ↥M₂ => (x : E)) (hk m)).symm
      · intro m
        apply Subtype.ext
        exact (hgb m m.2)
    · refine ⟨(⟨g, hgs⟩, Multiplicative.ofAdd 1), ?_⟩
      have hgk : (g : E) * z = k := by
        have : (k : E)⁻¹ * g = z := hkz
        calc (g : E) * z = (k : E) * ((k : E)⁻¹ * g) * z := by group
          _ = (k : E) * z * z := by rw [this]
          _ = k := by rw [mul_assoc, hzz, mul_one]
      apply burnsideF4c_aut_ext
      · intro m
        apply Subtype.ext
        exact (congrArg (fun x : ↥M₁ => (x : E)) (hg m)).symm
      · intro m
        apply Subtype.ext
        show ((g : E) * cc (Multiplicative.ofAdd 1)) * (m : E) *
          ((g : E) * cc (Multiplicative.ofAdd 1))⁻¹ = M₂.subtype (a.1 RankTwoIndex.two m)
        rw [hccg, hgk]
        exact (congrArg (fun x : ↥M₂ => (x : E)) (hk m)).symm
      · intro m
        apply Subtype.ext
        exact (hgb m m.2)
  have hbij : Function.Bijective φ := ⟨hinj, hsurj⟩
  have hgne' : ((1 : ↥(CFSG.Open.pCoreOf 2 (M₁ ⊓ M₂))), Multiplicative.ofAdd (1 : ZMod 2)) ≠ 1 :=
    fun h' => hgne (congrArg Prod.snd h')
  refine ⟨φ (1, Multiplicative.ofAdd 1), ?_, ?_, ?_, ?_, MulEquiv.ofBijective φ hbij, rfl, ?_, ?_⟩
  · intro h'
    exact hgne' (hinj (h'.trans (map_one φ).symm))
  · rw [← map_mul]
    have : ((1 : ↥(CFSG.Open.pCoreOf 2 (M₁ ⊓ M₂))), Multiplicative.ofAdd (1 : ZMod 2)) *
        ((1 : ↥(CFSG.Open.pCoreOf 2 (M₁ ⊓ M₂))), Multiplicative.ofAdd (1 : ZMod 2)) = 1 := by
      refine Prod.ext (by simp) ?_
      exact hgg
    rw [this, map_one]
  · intro m
    apply Subtype.ext
    show (1 : E) * (m : E) * (1 : E)⁻¹ = m
    group
  · refine ⟨z, ⟨hBS z hzB, ?_⟩, hz1, hzz, ?_⟩
    · exact Subgroup.mem_centralizer_iff.mpr (fun b hb => (hzc b (hSB b hb)).symm)
    · intro m
      show ((1 : E) * cc (Multiplicative.ofAdd 1)) * (m : E) *
        ((1 : E) * cc (Multiplicative.ofAdd 1))⁻¹ = z * (m : E) * z⁻¹
      rw [hccg, one_mul]
  · intro s m
    rfl
  · intro s m
    show ((s : E) * cc 1) * (m : E) * ((s : E) * cc 1)⁻¹ = (s : E) * (m : E) * (s : E)⁻¹
    rw [hcc1, mul_one]

end PartA

open CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam in
@[expose] def burnsideF4c_evalWord {G : Type*} [Group G] (u v : G) : List Bool → G
  | [] => 1
  | true :: w => u * burnsideF4c_evalWord u v w
  | false :: w => v * burnsideF4c_evalWord u v w

open CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam in
@[expose] def burnsideF4c_words : List (List Bool) :=
  [[], [true], [false], [false, true], [true, false], [false, false], [true, false, true],
   [false, false, true], [false, true, false], [true, false, false], [false, true, false, true],
   [true, false, false, true], [true, false, true, false], [false, false, true, false],
   [false, true, false, false], [true, false, true, false, true], [false, false, true, false, true],
   [false, true, false, false, true], [true, false, false, true, false],
   [true, false, true, false, false], [true, false, false, true, false, true],
   [true, false, true, false, false, true], [false, true, false, false, true, false],
   [false, true, false, false, true, false, true]]

open CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam in
theorem burnsideF4c_inner_of_gen {G : Type*} [Group G] (u v : G)
    (hW : ∀ x : G, ∃ w ∈ burnsideF4c_words, burnsideF4c_evalWord u v w = x)
    (hu : u * u = 1) (hu1 : u ≠ 1) (hv : v * v * v = 1) (hv1 : v ≠ 1)
    (huv4 : (u * v) * (u * v) * (u * v) * (u * v) = 1) (huv2 : (u * v) * (u * v) ≠ 1)
    (hdec : ∀ u' v' : G, u' * u' = 1 → u' ≠ 1 → v' * v' * v' = 1 → v' ≠ 1 →
      (u' * v') * (u' * v') * (u' * v') * (u' * v') = 1 → (u' * v') * (u' * v') ≠ 1 →
      ∃ g : G, g * u = u' * g ∧ g * v = v' * g) :
    ∀ φ : MulAut G, ∃ g : G, ∀ m : G, φ m = g * m * g⁻¹ := by
  intro φ
  have h1 : φ u * φ u = 1 := by rw [← map_mul, hu, map_one]
  have h2 : φ u ≠ 1 := fun h => hu1 (φ.injective (by rw [h, map_one]))
  have h3 : φ v * φ v * φ v = 1 := by rw [← map_mul, ← map_mul, hv, map_one]
  have h4 : φ v ≠ 1 := fun h => hv1 (φ.injective (by rw [h, map_one]))
  have h5 : (φ u * φ v) * (φ u * φ v) * (φ u * φ v) * (φ u * φ v) = 1 := by
    simp only [← map_mul]; rw [huv4, map_one]
  have h6 : (φ u * φ v) * (φ u * φ v) ≠ 1 := fun h =>
    huv2 (φ.injective (by simp only [← map_mul] at h; rw [h, map_one]))
  obtain ⟨g, hgu, hgv⟩ := hdec _ _ h1 h2 h3 h4 h5 h6
  have hu' : φ u = g * u * g⁻¹ := by rw [hgu]; group
  have hv' : φ v = g * v * g⁻¹ := by rw [hgv]; group
  have key : ∀ w : List Bool, φ (burnsideF4c_evalWord u v w) = g * burnsideF4c_evalWord u v w * g⁻¹ := by
    intro w
    induction w with
    | nil => simp [burnsideF4c_evalWord]
    | cons c w ih =>
      cases c
      · simp only [burnsideF4c_evalWord, map_mul, ih, hv']; group
      · simp only [burnsideF4c_evalWord, map_mul, ih, hu']; group
  refine ⟨g, fun m => ?_⟩
  obtain ⟨w, -, rfl⟩ := hW m
  exact key w


open CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam in
@[expose] def burnsideF4c_vP : burnsideF4c_SL := ⟨!![1, 0, 1; 0, 1, 1; 0, 1, 0], by decide +kernel⟩
open CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam in
@[expose] def burnsideF4c_vL : burnsideF4c_SL := ⟨!![0, 1, 1; 1, 1, 0; 0, 0, 1], by decide +kernel⟩

open CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam in
theorem burnsideF4c_vP_mem : burnsideF4c_vP ∈ burnsideF4c_P := by decide +kernel
open CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam in
theorem burnsideF4c_vL_mem : burnsideF4c_vL ∈ burnsideF4c_L := by decide +kernel

open CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam in
@[expose] def burnsideF4c_uP : ↥burnsideF4c_P := ⟨burnsideF4c_s, burnsideF4c_s_mem.1⟩
open CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam in
@[expose] def burnsideF4c_vP' : ↥burnsideF4c_P := ⟨burnsideF4c_vP, burnsideF4c_vP_mem⟩
open CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam in
@[expose] def burnsideF4c_uL : ↥burnsideF4c_L := ⟨burnsideF4c_t, burnsideF4c_t_mem.1⟩
open CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam in
@[expose] def burnsideF4c_vL' : ↥burnsideF4c_L := ⟨burnsideF4c_vL, burnsideF4c_vL_mem⟩

open CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam in
theorem burnsideF4c_P_cover : ∀ x : ↥burnsideF4c_P, ∃ w ∈ burnsideF4c_words,
    burnsideF4c_evalWord burnsideF4c_uP burnsideF4c_vP' w = x := by decide +kernel

open CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam in
theorem burnsideF4c_L_cover : ∀ x : ↥burnsideF4c_L, ∃ w ∈ burnsideF4c_words,
    burnsideF4c_evalWord burnsideF4c_uL burnsideF4c_vL' w = x := by decide +kernel

open CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam in
theorem burnsideF4c_P_dec : ∀ u' v' : ↥burnsideF4c_P, u' * u' = 1 → u' ≠ 1 → v' * v' * v' = 1 → v' ≠ 1 →
    (u' * v') * (u' * v') * (u' * v') * (u' * v') = 1 → (u' * v') * (u' * v') ≠ 1 →
    ∃ g : ↥burnsideF4c_P, g * burnsideF4c_uP = u' * g ∧ g * burnsideF4c_vP' = v' * g := by
  decide +kernel

open CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam in
theorem burnsideF4c_L_dec : ∀ u' v' : ↥burnsideF4c_L, u' * u' = 1 → u' ≠ 1 → v' * v' * v' = 1 → v' ≠ 1 →
    (u' * v') * (u' * v') * (u' * v') * (u' * v') = 1 → (u' * v') * (u' * v') ≠ 1 →
    ∃ g : ↥burnsideF4c_L, g * burnsideF4c_uL = u' * g ∧ g * burnsideF4c_vL' = v' * g := by
  decide +kernel

open CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam in
theorem burnsideF4c_P_rels : burnsideF4c_uP * burnsideF4c_uP = 1 ∧ burnsideF4c_uP ≠ 1 ∧
    burnsideF4c_vP' * burnsideF4c_vP' * burnsideF4c_vP' = 1 ∧ burnsideF4c_vP' ≠ 1 ∧
    (burnsideF4c_uP * burnsideF4c_vP') * (burnsideF4c_uP * burnsideF4c_vP') *
      (burnsideF4c_uP * burnsideF4c_vP') * (burnsideF4c_uP * burnsideF4c_vP') = 1 ∧
    (burnsideF4c_uP * burnsideF4c_vP') * (burnsideF4c_uP * burnsideF4c_vP') ≠ 1 := by
  decide +kernel

open CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam in
theorem burnsideF4c_L_rels : burnsideF4c_uL * burnsideF4c_uL = 1 ∧ burnsideF4c_uL ≠ 1 ∧
    burnsideF4c_vL' * burnsideF4c_vL' * burnsideF4c_vL' = 1 ∧ burnsideF4c_vL' ≠ 1 ∧
    (burnsideF4c_uL * burnsideF4c_vL') * (burnsideF4c_uL * burnsideF4c_vL') *
      (burnsideF4c_uL * burnsideF4c_vL') * (burnsideF4c_uL * burnsideF4c_vL') = 1 ∧
    (burnsideF4c_uL * burnsideF4c_vL') * (burnsideF4c_uL * burnsideF4c_vL') ≠ 1 := by
  decide +kernel

open CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam in
theorem burnsideF4c_inn_P : ∀ φ : MulAut ↥burnsideF4c_P, ∃ g : ↥burnsideF4c_P, ∀ m : ↥burnsideF4c_P,
    φ m = g * m * g⁻¹ := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := burnsideF4c_P_rels
  exact burnsideF4c_inner_of_gen _ _ burnsideF4c_P_cover h1 h2 h3 h4 h5 h6 burnsideF4c_P_dec

open CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam in
theorem burnsideF4c_inn_L : ∀ φ : MulAut ↥burnsideF4c_L, ∃ g : ↥burnsideF4c_L, ∀ m : ↥burnsideF4c_L,
    φ m = g * m * g⁻¹ := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := burnsideF4c_L_rels
  exact burnsideF4c_inner_of_gen _ _ burnsideF4c_L_cover h1 h2 h3 h4 h5 h6 burnsideF4c_L_dec

open CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam in
theorem burnsideF4c_cen_P : ∀ g : burnsideF4c_SL, g ∈ burnsideF4c_P →
    (∀ m : burnsideF4c_SL, m ∈ burnsideF4c_P → g * m = m * g) → g = 1 := by decide +kernel

open CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam in
theorem burnsideF4c_cen_L : ∀ g : burnsideF4c_SL, g ∈ burnsideF4c_L →
    (∀ m : burnsideF4c_SL, m ∈ burnsideF4c_L → g * m = m * g) → g = 1 := by decide +kernel

open CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam in
theorem burnsideF4c_norm_P : ∀ g : burnsideF4c_SL, g ∈ burnsideF4c_P →
    (∀ b : burnsideF4c_SL, b ∈ burnsideF4c_P ⊓ burnsideF4c_L → g * b * g⁻¹ ∈ burnsideF4c_P ⊓ burnsideF4c_L) →
    g ∈ burnsideF4c_P ⊓ burnsideF4c_L := by decide +kernel

open CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam in
theorem burnsideF4c_norm_L : ∀ g : burnsideF4c_SL, g ∈ burnsideF4c_L →
    (∀ b : burnsideF4c_SL, b ∈ burnsideF4c_P ⊓ burnsideF4c_L → g * b * g⁻¹ ∈ burnsideF4c_P ⊓ burnsideF4c_L) →
    g ∈ burnsideF4c_P ⊓ burnsideF4c_L := by decide +kernel

open CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam in
theorem burnsideF4c_centD : ∀ b : burnsideF4c_SL, b ∈ burnsideF4c_P ⊓ burnsideF4c_L →
    (∀ b' : burnsideF4c_SL, b' ∈ burnsideF4c_P ⊓ burnsideF4c_L → b * b' = b' * b) →
    b = 1 ∨ b = burnsideF4c_z := by decide +kernel

open CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam in
theorem burnsideF4c_z_nc : ∃ m : burnsideF4c_SL, m ∈ burnsideF4c_L ∧ burnsideF4c_z * m ≠ m * burnsideF4c_z := by
  decide +kernel

open CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam in
theorem burnsideF4c_card_D : Nat.card ↥(burnsideF4c_P ⊓ burnsideF4c_L) = 8 := by
  rw [Nat.card_eq_fintype_card]; decide +kernel


open CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam in
theorem burnsideF4c_iface_concrete :
    burnsideF4c_L2Iface burnsideF4c_SL burnsideF4c_P burnsideF4c_L where
  pgroup := IsPGroup.of_card (p := 2) (n := 3) burnsideF4c_card_D
  zdata := ⟨burnsideF4c_z, burnsideF4c_z_mem, burnsideF4c_z_ne, burnsideF4c_z_sq,
    burnsideF4c_z_central, burnsideF4c_centD, burnsideF4c_z_nc⟩
  cen1 := burnsideF4c_cen_P
  cen2 := burnsideF4c_cen_L
  norm1 := burnsideF4c_norm_P
  norm2 := burnsideF4c_norm_L
  inn1 := burnsideF4c_inn_P
  inn2 := burnsideF4c_inn_L

open CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam in
theorem burnsideF4c_inn_map {E₀ E : Type} [Group E₀] [Group E] (θ : E₀ ≃* E) (H : Subgroup E₀)
    (h : ∀ φ : MulAut ↥H, ∃ g : ↥H, ∀ m : ↥H, φ m = g * m * g⁻¹) :
    ∀ φ : MulAut ↥(H.map θ.toMonoidHom), ∃ g : ↥(H.map θ.toMonoidHom),
      ∀ m : ↥(H.map θ.toMonoidHom), φ m = g * m * g⁻¹ := by
  intro φ
  let S : ↥H ≃* ↥(H.map θ.toMonoidHom) := MulEquiv.subgroupMap θ H
  let φ₀ : MulAut ↥H := S.trans (φ.trans S.symm)
  obtain ⟨g₀, hg₀⟩ := h φ₀
  refine ⟨S g₀, fun m => ?_⟩
  obtain ⟨m₀, rfl⟩ := S.surjective m
  have e : φ (S m₀) = S (φ₀ m₀) := by
    show φ (S m₀) = S (S.symm (φ (S m₀)))
    exact (S.apply_symm_apply _).symm
  rw [e, hg₀ m₀, map_mul, map_mul, map_inv]

open CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam in
theorem burnsideF4c_iface_map {E₀ E : Type} [Group E₀] [Group E] (θ : E₀ ≃* E)
    {P L : Subgroup E₀} (h : burnsideF4c_L2Iface E₀ P L) :
    burnsideF4c_L2Iface E (P.map θ.toMonoidHom) (L.map θ.toMonoidHom) := by
  have hmem : ∀ (H : Subgroup E₀) (x : E), x ∈ H.map θ.toMonoidHom ↔ θ.symm x ∈ H :=
    fun H x => Subgroup.mem_map_equiv
  have hD : ∀ x : E, x ∈ P.map θ.toMonoidHom ⊓ L.map θ.toMonoidHom ↔ θ.symm x ∈ P ⊓ L := by
    intro x
    rw [Subgroup.mem_inf, Subgroup.mem_inf, hmem, hmem]
  obtain ⟨z, hzB, hz1, hzz, hzc, hcB, m0, hm0, hzm0⟩ := h.zdata
  refine ⟨?_, ⟨θ z, ?_, ?_, ?_, ?_, ?_, θ m0, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro g
    obtain ⟨x, hx⟩ := g
    obtain ⟨k, hk⟩ := h.pgroup ⟨θ.symm x, (hD x).1 hx⟩
    have h2 := congrArg (fun y : ↥(P ⊓ L) => θ (y : E₀)) hk
    simp only [Subgroup.coe_pow, map_pow, MulEquiv.apply_symm_apply, Subgroup.coe_one, map_one] at h2
    exact ⟨k, Subtype.ext h2⟩
  · rw [hD]; simpa using hzB
  · exact fun h' => hz1 (θ.injective (by rw [h', map_one]))
  · rw [← map_mul, hzz, map_one]
  · intro b hb
    have hb' := (hD b).1 hb
    have := hzc (θ.symm b) hb'
    have h2 := congrArg θ this
    simpa using h2
  · intro b hb hcomm
    have hb' := (hD b).1 hb
    have := hcB (θ.symm b) hb' (fun b' hb'' => by
      have := hcomm (θ b') ((hD _).2 (by simpa using hb''))
      have h2 := congrArg θ.symm this
      simpa using h2)
    rcases this with h1 | h1
    · left
      have := congrArg θ h1
      simpa using this
    · right
      have := congrArg θ h1
      simpa using this
  · exact (hmem L (θ m0)).2 (by simpa using hm0)
  · intro h'
    apply hzm0
    have := congrArg θ.symm h'
    simpa using this
  · intro g hg hc
    have hg' := (hmem P g).1 hg
    have := h.cen1 (θ.symm g) hg' (fun m hm => by
      have := hc (θ m) ((hmem P _).2 (by simpa using hm))
      have h2 := congrArg θ.symm this
      simpa using h2)
    have h2 := congrArg θ this
    simpa using h2
  · intro g hg hc
    have hg' := (hmem L g).1 hg
    have := h.cen2 (θ.symm g) hg' (fun m hm => by
      have := hc (θ m) ((hmem L _).2 (by simpa using hm))
      have h2 := congrArg θ.symm this
      simpa using h2)
    have h2 := congrArg θ this
    simpa using h2
  · intro g hg hn
    have hg' := (hmem P g).1 hg
    have := h.norm1 (θ.symm g) hg' (fun b hb => by
      have := hn (θ b) ((hD _).2 (by simpa using hb))
      have h2 := (hD _).1 this
      simpa using h2)
    exact (hD g).2 this |> fun h' => by simpa [hD] using (hD g).2 this
  · intro g hg hn
    have hg' := (hmem L g).1 hg
    have := h.norm2 (θ.symm g) hg' (fun b hb => by
      have := hn (θ b) ((hD _).2 (by simpa using hb))
      have h2 := (hD _).1 this
      simpa using h2)
    exact (hD g).2 this
  · exact burnsideF4c_inn_map θ P h.inn1
  · exact burnsideF4c_inn_map θ L h.inn2

section Pull

variable {α β : CFSG.Quasithin.RankTwoAmalgam.{0}} {Y : Type} [Group Y]

open CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam in
theorem burnsideF4c_range_comp_equiv {A B C : Type*} [Group A] [Group B] [Group C] (g : B →* C)
    (e : A ≃* B) : (g.comp e.toMonoidHom).range = g.range := by
  ext x
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨e a, rfl⟩
  · rintro ⟨b, rfl⟩
    exact ⟨e.symm b, by simp⟩

open CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam in
@[expose] def burnsideF4c_pull (e : α.Iso β) (c : β.Completion Y) : α.Completion Y where
  φ1 := c.φ1.comp e.φ1.toMonoidHom
  φ12 := c.φ12.comp e.φ12.toMonoidHom
  φ2 := c.φ2.comp e.φ2.toMonoidHom
  comm1 g := by
    show c.φ1 (e.φ1 (α.α1 g)) = c.φ12 (e.φ12 g)
    rw [← e.comm1 g]; exact c.comm1 _
  comm2 g := by
    show c.φ2 (e.φ2 (α.α2 g)) = c.φ12 (e.φ12 g)
    rw [← e.comm2 g]; exact c.comm2 _
  inter := by
    rw [burnsideF4c_range_comp_equiv, burnsideF4c_range_comp_equiv, burnsideF4c_range_comp_equiv]
    exact c.inter
  gen := by
    rw [burnsideF4c_range_comp_equiv, burnsideF4c_range_comp_equiv]
    exact c.gen

open CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam in
theorem burnsideF4c_pull_faithful (e : α.Iso β) (c : β.Completion Y) (hc : c.IsFaithful) :
    (burnsideF4c_pull e c).IsFaithful :=
  ⟨hc.1.comp e.φ1.injective, hc.2.1.comp e.φ12.injective, hc.2.2.comp e.φ2.injective⟩

open CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam in
@[expose] def burnsideF4c_LargeGeom (G₁ G₂ : Subgroup Y) (m : ℕ) : Prop :=
  ∀ p q : GPath (CosetGeom.graph (G₁ ⊔ G₂) G₁ G₂) m, p.IsGeodesic → q.IsGeodesic → p 0 = q 0 →
    p m = q m → p = q

open CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam in
theorem burnsideF4c_LargeGeom_congr {G₁ G₂ G₁' G₂' : Subgroup Y} (h1 : G₁ = G₁') (h2 : G₂ = G₂')
    (m : ℕ) : burnsideF4c_LargeGeom G₁ G₂ m ↔ burnsideF4c_LargeGeom G₁' G₂' m := by
  subst h1; subst h2; exact Iff.rfl

open CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam in
theorem burnsideF4c_isLarge_iff (c : β.Completion Y) (m : ℕ) :
    c.IsLarge m ↔ burnsideF4c_LargeGeom c.φ1.range c.φ2.range m := Iff.rfl

open CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam in
theorem burnsideF4c_pull_small (e : α.Iso β) (c : β.Completion Y) (m : ℕ) (hc : c.IsSmall m) :
    (burnsideF4c_pull e c).IsSmall m := by
  intro hL
  apply hc
  rw [burnsideF4c_isLarge_iff]
  have := (burnsideF4c_isLarge_iff (burnsideF4c_pull e c) m).1 hL
  exact (burnsideF4c_LargeGeom_congr (burnsideF4c_range_comp_equiv _ _)
    (burnsideF4c_range_comp_equiv _ _) m).1 this

open CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam in
theorem burnsideF4c_pull_equiv {Y' : Type} [Group Y'] (e : α.Iso β) {c : β.Completion Y}
    {c' : β.Completion Y'}
    (h : Amalgam.Completion.IsEquivalent c.toCompletion c'.toCompletion) :
    Amalgam.Completion.IsEquivalent (burnsideF4c_pull e c).toCompletion
      (burnsideF4c_pull e c').toCompletion := by
  obtain ⟨φ, hφ⟩ := h
  refine ⟨φ, fun d x => ?_⟩
  cases d
  · exact hφ RankTwoIndex.one (e.φ1 x)
  · exact hφ RankTwoIndex.two (e.φ2 x)
  · exact hφ RankTwoIndex.onetwo (e.φ12 x)


open CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam in
@[expose] def burnsideF4c_isoSymm (e : α.Iso β) : β.Iso α where
  φ1 := e.φ1.symm
  φ12 := e.φ12.symm
  φ2 := e.φ2.symm
  comm1 g := by
    apply e.φ1.injective
    have := e.comm1 (e.φ12.symm g)
    simp only [MulEquiv.apply_symm_apply] at this ⊢
    exact this.symm
  comm2 g := by
    apply e.φ2.injective
    have := e.comm2 (e.φ12.symm g)
    simp only [MulEquiv.apply_symm_apply] at this ⊢
    exact this.symm

open CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam in
theorem burnsideF4c_pull_pull_equiv (e : α.Iso β) (c : α.Completion Y) :
    Amalgam.Completion.IsEquivalent (burnsideF4c_pull e (burnsideF4c_pull (burnsideF4c_isoSymm e) c)).toCompletion
      c.toCompletion := by
  refine ⟨MulEquiv.refl Y, fun d x => ?_⟩
  cases d
  · exact congrArg c.φ1 (e.φ1.symm_apply_apply x)
  · exact congrArg c.φ2 (e.φ2.symm_apply_apply x)
  · exact congrArg c.φ12 (e.φ12.symm_apply_apply x)

open CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam in
theorem burnsideF4c_pull_symm_pull_equiv (e : α.Iso β) (c : β.Completion Y) :
    Amalgam.Completion.IsEquivalent (burnsideF4c_pull (burnsideF4c_isoSymm e)
      (burnsideF4c_pull e c)).toCompletion c.toCompletion := by
  refine ⟨MulEquiv.refl Y, fun d x => ?_⟩
  cases d
  · exact congrArg c.φ1 (e.φ1.apply_symm_apply x)
  · exact congrArg c.φ2 (e.φ2.apply_symm_apply x)
  · exact congrArg c.φ12 (e.φ12.apply_symm_apply x)

end Pull

section Iso

variable {E₀ E : Type} [Group E₀] [Group E] (θ : E₀ ≃* E) (P L : Subgroup E₀)

open CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam in
@[expose] def burnsideF4c_amalIso :
    (RankTwoAmalgam.ofSubgroups (P.map θ.toMonoidHom) (L.map θ.toMonoidHom)).Iso
      (RankTwoAmalgam.ofSubgroups P L) where
  φ1 := (MulEquiv.subgroupMap θ P).symm
  φ2 := (MulEquiv.subgroupMap θ L).symm
  φ12 := (MulEquiv.subgroupCongr (Subgroup.map_inf P L θ.toMonoidHom θ.injective)).symm.trans
    (MulEquiv.subgroupMap θ (P ⊓ L)).symm
  comm1 g := by
    apply Subtype.ext
    rfl
  comm2 g := by
    apply Subtype.ext
    rfl


open CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam in
@[expose] def burnsideF4c_F49B (E : Type) [Group E] (M₁ M₂ : Subgroup E) : Prop :=
  ∃ (Y₁ Y₂ : Type) (_ : Group Y₁) (_ : Group Y₂)
    (β₁ : (RankTwoAmalgam.ofSubgroups M₁ M₂).Completion Y₁)
    (β₂ : (RankTwoAmalgam.ofSubgroups M₁ M₂).Completion Y₂),
    β₁.IsFaithful ∧ β₂.IsFaithful ∧ β₁.IsSmall 3 ∧ β₂.IsSmall 3 ∧
    ¬ Amalgam.Completion.IsEquivalent β₁.toCompletion β₂.toCompletion ∧
    ∀ (Y : Type) [Group Y] (β : (RankTwoAmalgam.ofSubgroups M₁ M₂).Completion Y), β.IsFaithful →
      β.IsSmall 3 →
      Amalgam.Completion.IsEquivalent β.toCompletion β₁.toCompletion ∨
        Amalgam.Completion.IsEquivalent β.toCompletion β₂.toCompletion

open CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam in
theorem burnsideF4c_partB_map {E : Type} [Group E] (θ : burnsideF4c_SL ≃* E) :
    burnsideF4c_F49B E (burnsideF4c_P.map θ.toMonoidHom) (burnsideF4c_L.map θ.toMonoidHom) := by
  obtain ⟨Y₁, Y₂, g1, g2, β₁, β₂, f1, f2, s1, s2, hne, hcl⟩ := burnsideF4c_partB_concrete
  let e := burnsideF4c_amalIso θ burnsideF4c_P burnsideF4c_L
  refine ⟨Y₁, Y₂, g1, g2, burnsideF4c_pull e β₁, burnsideF4c_pull e β₂,
    burnsideF4c_pull_faithful e β₁ f1, burnsideF4c_pull_faithful e β₂ f2,
    burnsideF4c_pull_small e β₁ 3 s1, burnsideF4c_pull_small e β₂ 3 s2, ?_, ?_⟩
  · intro hE
    have h1 := burnsideF4c_pull_equiv (burnsideF4c_isoSymm e) hE
    apply hne
    exact (burnsideF4c_pull_symm_pull_equiv e β₁).symm.trans
      (h1.trans (burnsideF4c_pull_symm_pull_equiv e β₂))
  · intro Y _ β hβ hsm
    have hβ' := burnsideF4c_pull_faithful (burnsideF4c_isoSymm e) β hβ
    have hsm' := burnsideF4c_pull_small (burnsideF4c_isoSymm e) β 3 hsm
    have hback := burnsideF4c_pull_pull_equiv e β
    rcases hcl Y (burnsideF4c_pull (burnsideF4c_isoSymm e) β) hβ' hsm' with h | h
    · left
      exact hback.symm.trans (burnsideF4c_pull_equiv e h)
    · right
      exact hback.symm.trans (burnsideF4c_pull_equiv e h)

end Iso

open CFSG.ASVolI.ChF.ClassicalRoots in
theorem burnsideF4c_marking {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E}
    (h : HypF_4_4g .L3 2 1 Gp M₁ M₂) :
    ∃ marking : ClassicalRoots.Marking .L3 2 1 Gp,
      M₁.subgroupOf Gp = marking.parabolic false ∧ M₂.subgroupOf Gp = marking.parabolic true := by
  obtain ⟨chart, -, hpts, hlines⟩ := h.lie_amalgam
  rcases chart.coordinates with
    ⟨c, hk, marking, h1, h2, h3, h4, h5⟩ | ⟨hk, -⟩ | ⟨hk, -⟩ | ⟨hk, -⟩ |
    ⟨-, exponent, K, fK, finK, charK, scope, ⟨hk, -⟩ | ⟨hk, -⟩⟩
  · have hc : c = .L3 := by
      cases c
      · rfl
      all_goals exact absurd hk (by decide)
    subst hc
    refine ⟨marking, ?_, ?_⟩
    · have : Gp ⊓ M₁ = (marking.parabolic false).map Gp.subtype := hpts.trans h2
      rw [← Subgroup.inf_subgroupOf_left M₁ Gp, this]
      exact Subgroup.comap_map_eq_self_of_injective Gp.subtype_injective _
    · have : Gp ⊓ M₂ = (marking.parabolic true).map Gp.subtype := hlines.trans h3
      rw [← Subgroup.inf_subgroupOf_left M₂ Gp, this]
      exact Subgroup.comap_map_eq_self_of_injective Gp.subtype_injective _
  all_goals exact absurd hk (by decide)


open CFSG.ASVolI.ChF.ClassicalRoots in
theorem burnsideF4c_mem_rawStabilizer {index : Type} [Fintype index] [DecidableEq index]
    {K : Type} [Field K] (space : Set (index → K)) (g : GL index K) :
    g ∈ rawStabilizer space ↔
      ∀ vector : index → K, (g : Matrix index index K).mulVec vector ∈ space ↔ vector ∈ space := by
  let S : Subgroup (GL index K) :=
    { carrier := {actor | ∀ vector : index → K,
        (actor : Matrix index index K).mulVec vector ∈ space ↔ vector ∈ space}
      one_mem' := by
        intro vector
        simp
      mul_mem' := by
        intro a b ha hb vector
        have h1 := ha ((b : Matrix index index K).mulVec vector)
        have h2 := hb vector
        rw [Units.val_mul, ← Matrix.mulVec_mulVec]
        exact h1.trans h2
      inv_mem' := by
        intro a ha vector
        have h1 := ha (((a⁻¹ : GL index K) : Matrix index index K).mulVec vector)
        rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec] at h1
        exact h1.symm }
  have hS : rawStabilizer space = S := Subgroup.closure_eq S
  rw [hS]
  exact Iff.rfl

open CFSG.ASVolI.ChF.ClassicalRoots in
theorem burnsideF4c_image_one {index : Type} [Fintype index] [DecidableEq index] {K : Type}
    [Field K] (S : Set (index → K)) :
    (fun vector => ((1 : GL index K) : Matrix index index K).mulVec vector) '' S = S := by
  simp

open CFSG.ASVolI.ChF.ClassicalRoots in
theorem burnsideF4c_flag_one {K : Type} [Field K] (A : GL (Fin 3) K) :
    A ∈ rawStabilizer ((fun vector => ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).mulVec vector) ''
        coordinateSpace (flagOne .L3)) ↔
      (A : Matrix (Fin 3) (Fin 3) K) 1 0 = 0 ∧ (A : Matrix (Fin 3) (Fin 3) K) 2 0 = 0 := by
  rw [burnsideF4c_mem_rawStabilizer, burnsideF4c_image_one]
  have hdet : (A : Matrix (Fin 3) (Fin 3) K).det ≠ 0 := by
    have := (Matrix.GeneralLinearGroup.det A).ne_zero
    simpa using this
  have hmem : ∀ v : Fin 3 → K, v ∈ coordinateSpace (flagOne .L3) ↔ v 1 = 0 ∧ v 2 = 0 := by
    intro v
    constructor
    · intro h
      exact ⟨h 1 (by simp [flagOne]), h 2 (by simp [flagOne])⟩
    · rintro ⟨h1, h2⟩ i hi
      fin_cases i
      · exact absurd (by simp [flagOne]) hi
      · exact h1
      · exact h2
  simp only [hmem]
  constructor
  · intro h
    have := (h (Pi.single 0 1)).2 (by simp)
    simpa [Matrix.mulVec_single_one] using this
  · rintro ⟨h1, h2⟩ v
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_three, h1, h2, zero_mul, zero_add]
    constructor
    · rintro ⟨e1, e2⟩
      have hD : (A : Matrix (Fin 3) (Fin 3) K) 1 1 * (A : Matrix (Fin 3) (Fin 3) K) 2 2 -
          (A : Matrix (Fin 3) (Fin 3) K) 1 2 * (A : Matrix (Fin 3) (Fin 3) K) 2 1 ≠ 0 := by
        intro h0
        apply hdet
        rw [Matrix.det_fin_three, h1, h2]
        linear_combination ((A : Matrix (Fin 3) (Fin 3) K) 0 0) * h0
      have hv1 : ((A : Matrix (Fin 3) (Fin 3) K) 1 1 * (A : Matrix (Fin 3) (Fin 3) K) 2 2 -
          (A : Matrix (Fin 3) (Fin 3) K) 1 2 * (A : Matrix (Fin 3) (Fin 3) K) 2 1) * v 1 = 0 := by
        linear_combination ((A : Matrix (Fin 3) (Fin 3) K) 2 2) * e1 - ((A : Matrix (Fin 3) (Fin 3) K) 1 2) * e2
      have hv2 : ((A : Matrix (Fin 3) (Fin 3) K) 1 1 * (A : Matrix (Fin 3) (Fin 3) K) 2 2 -
          (A : Matrix (Fin 3) (Fin 3) K) 1 2 * (A : Matrix (Fin 3) (Fin 3) K) 2 1) * v 2 = 0 := by
        linear_combination ((A : Matrix (Fin 3) (Fin 3) K) 1 1) * e2 - ((A : Matrix (Fin 3) (Fin 3) K) 2 1) * e1
      exact ⟨(mul_eq_zero.mp hv1).resolve_left hD, (mul_eq_zero.mp hv2).resolve_left hD⟩
    · rintro ⟨e1, e2⟩
      simp [e1, e2]


open CFSG.ASVolI.ChF.ClassicalRoots in
theorem burnsideF4c_flag_two {K : Type} [Field K] (A : GL (Fin 3) K) :
    A ∈ rawStabilizer ((fun vector => ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).mulVec vector) ''
        coordinateSpace (flagTwo .L3)) ↔
      (A : Matrix (Fin 3) (Fin 3) K) 2 0 = 0 ∧ (A : Matrix (Fin 3) (Fin 3) K) 2 1 = 0 := by
  rw [burnsideF4c_mem_rawStabilizer, burnsideF4c_image_one]
  have hdet : (A : Matrix (Fin 3) (Fin 3) K).det ≠ 0 := by
    have := (Matrix.GeneralLinearGroup.det A).ne_zero
    simpa using this
  have hmem : ∀ v : Fin 3 → K, v ∈ coordinateSpace (flagTwo .L3) ↔ v 2 = 0 := by
    intro v
    constructor
    · intro h
      exact h 2 (by simp [flagTwo])
    · intro h2 i hi
      fin_cases i
      · exact absurd (by simp [flagTwo]) hi
      · exact absurd (by simp [flagTwo]) hi
      · exact h2
  simp only [hmem]
  constructor
  · intro h
    have e0 := (h (Pi.single 0 1)).2 (by simp)
    have e1 := (h (Pi.single 1 1)).2 (by simp)
    exact ⟨by simpa [Matrix.mulVec_single_one] using e0, by simpa [Matrix.mulVec_single_one] using e1⟩
  · rintro ⟨h1, h2⟩ v
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_three, h1, h2, zero_mul, zero_add]
    constructor
    · intro e
      have hD : (A : Matrix (Fin 3) (Fin 3) K) 2 2 ≠ 0 := by
        intro h0
        apply hdet
        rw [Matrix.det_fin_three, h1, h2]
        linear_combination ((A : Matrix (Fin 3) (Fin 3) K) 0 0 * (A : Matrix (Fin 3) (Fin 3) K) 1 1 -
          (A : Matrix (Fin 3) (Fin 3) K) 0 1 * (A : Matrix (Fin 3) (Fin 3) K) 1 0) * h0
      exact (mul_eq_zero.mp e).resolve_left hD
    · intro e
      simp [e]


section Iso0

open CFSG.ASVolI.ChF.ClassicalRoots in
noncomputable def burnsideF4c_ringEquiv (K : Type) [Field K] [Finite K] (hK : Nat.card K = 2) :
    K ≃+* ZMod 2 :=
  letI := Fintype.ofFinite K
  FiniteField.ringEquivOfCardEq (by rw [← Nat.card_eq_fintype_card, hK, ZMod.card])

open CFSG.ASVolI.ChF.ClassicalRoots in
noncomputable def burnsideF4c_slEquiv (K : Type) [Field K] (ε : ZMod 2 ≃+* K) :
    Matrix.SpecialLinearGroup (Fin 3) (ZMod 2) ≃* Matrix.SpecialLinearGroup (Fin 3) K :=
  MonoidHom.toMulEquiv (Matrix.SpecialLinearGroup.map ε.toRingHom)
    (Matrix.SpecialLinearGroup.map ε.symm.toRingHom)
    (by ext i j; simp) (by ext i j; simp)

open CFSG.ASVolI.ChF.ClassicalRoots in
theorem burnsideF4c_slEquiv_coe (K : Type) [Field K] (ε : ZMod 2 ≃+* K)
    (x : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) (i j : Fin 3) :
    ((burnsideF4c_slEquiv K ε x : Matrix.SpecialLinearGroup (Fin 3) K) :
      Matrix (Fin 3) (Fin 3) K) i j = ε ((x : Matrix (Fin 3) (Fin 3) (ZMod 2)) i j) := by
  simp [burnsideF4c_slEquiv]

open CFSG.ASVolI.ChF.ClassicalRoots in
theorem burnsideF4c_center_bot (K : Type) [Field K] (ε : K ≃+* ZMod 2) :
    Subgroup.center (Matrix.SpecialLinearGroup (Fin 3) K) = ⊥ := by
  ext A
  rw [Matrix.SpecialLinearGroup.mem_center_iff, Subgroup.mem_bot]
  constructor
  · rintro ⟨r, hr, hA⟩
    have hr1 : r = 1 := by
      have h01 : ∀ y : ZMod 2, y = 0 ∨ y = 1 := by decide
      rcases h01 (ε r) with h | h
      · exfalso
        have : ε r = 0 := h
        have hr0 : r = 0 := ε.injective (by rw [this, map_zero])
        rw [hr0, Fintype.card_fin, zero_pow (by norm_num)] at hr
        exact zero_ne_one hr
      · exact ε.injective (by rw [h, map_one])
    subst hr1
    ext i j
    rw [← hA]
    simp
  · rintro rfl
    exact ⟨1, by simp, by simp⟩


open CFSG.ASVolI.ChF.ClassicalRoots in
theorem burnsideF4c_scalars_bot (K : Type) [Field K] (ε : K ≃+* ZMod 2) :
    (StatedScalars (Fin 3) K).subgroupOf (StatedSL 3 K) = ⊥ := by
  rw [← CFSG.Assembly.LowTwoRank.map_center_eq_statedScalars 3 K, burnsideF4c_center_bot K ε,
    Subgroup.map_bot]

end Iso0

open CFSG.ASVolI.ChF.ClassicalRoots in
theorem burnsideF4c_part0 {E : Type} [Group E] {M₁ M₂ : Subgroup E}
    (hyp : HypF_4_4 GLKind.L3 2 1 ⊤ M₁ M₂) :
    ∃ θ : burnsideF4c_SL ≃* E, M₁ = burnsideF4c_P.map θ.toMonoidHom ∧
      M₂ = burnsideF4c_L.map θ.toMonoidHom := by
  obtain ⟨marking, h1, h2⟩ := burnsideF4c_marking hyp.toHypF_4_4g
  have hcard : Nat.card marking.field = 2 := by
    have := marking.field_card
    simpa using this
  have hbasis : marking.basis = 1 := marking.basis_compatible
  let ε : marking.field ≃+* ZMod 2 := burnsideF4c_ringEquiv marking.field hcard
  let f1 := burnsideF4c_slEquiv marking.field ε.symm
  let f2 : Matrix.SpecialLinearGroup (Fin 3) marking.field ≃*
      ↥(nativeGroup .L3 (2 ^ 1) marking.field) :=
    CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 3 marking.field
  have hbot : (StatedScalars (Coord .L3) marking.field).subgroupOf
      (nativeGroup .L3 (2 ^ 1) marking.field) = ⊥ := burnsideF4c_scalars_bot marking.field ε
  let g : ↥(nativeGroup .L3 (2 ^ 1) marking.field) ≃*
      StatedProj (nativeGroup .L3 (2 ^ 1) marking.field) :=
    MulEquiv.ofBijective (projectiveMap .L3 (2 ^ 1) marking.field) ⟨by
      rw [← MonoidHom.ker_eq_bot_iff]
      exact (QuotientGroup.ker_mk' _).trans hbot, QuotientGroup.mk'_surjective _⟩
  let θ₀ : burnsideF4c_SL ≃* ↥(⊤ : Subgroup E) := f1.trans (f2.trans (g.trans marking.identification))
  have hθ₀ : θ₀.toMonoidHom = marking.transport.comp (f2.toMonoidHom.comp f1.toMonoidHom) :=
    MonoidHom.ext fun _ => rfl
  have hent : ∀ (x : burnsideF4c_SL) (i j : Fin 3),
      (((f2 (f1 x) : ↥(nativeGroup .L3 (2 ^ 1) marking.field)) : GL (Fin 3) marking.field) :
        Matrix (Fin 3) (Fin 3) marking.field) i j =
      ε.symm ((x : Matrix (Fin 3) (Fin 3) (ZMod 2)) i j) := by
    intro x i j
    exact burnsideF4c_slEquiv_coe marking.field ε.symm x i j
  have hmemP : ∀ x : burnsideF4c_SL,
      f2 (f1 x) ∈ nativeParabolic .L3 (2 ^ 1) marking.field marking.basis false ↔
        x ∈ burnsideF4c_P := by
    intro x
    show ((f2 (f1 x) : ↥(nativeGroup .L3 (2 ^ 1) marking.field)) : GL (Fin 3) marking.field) ∈
      rawStabilizer ((fun vector => ((marking.basis : GL (Fin 3) marking.field) :
        Matrix (Fin 3) (Fin 3) marking.field).mulVec vector) '' coordinateSpace (flagOne .L3)) ↔ _
    rw [hbasis, burnsideF4c_flag_one, hent, hent]
    show ε.symm _ = 0 ∧ ε.symm _ = 0 ↔ burnsideF4c_inP x
    rw [map_eq_zero_iff _ ε.symm.injective, map_eq_zero_iff _ ε.symm.injective]
    exact Iff.rfl
  have hmemL : ∀ x : burnsideF4c_SL,
      f2 (f1 x) ∈ nativeParabolic .L3 (2 ^ 1) marking.field marking.basis true ↔
        x ∈ burnsideF4c_L := by
    intro x
    show ((f2 (f1 x) : ↥(nativeGroup .L3 (2 ^ 1) marking.field)) : GL (Fin 3) marking.field) ∈
      rawStabilizer ((fun vector => ((marking.basis : GL (Fin 3) marking.field) :
        Matrix (Fin 3) (Fin 3) marking.field).mulVec vector) '' coordinateSpace (flagTwo .L3)) ↔ _
    rw [hbasis, burnsideF4c_flag_two, hent, hent]
    show ε.symm _ = 0 ∧ ε.symm _ = 0 ↔ burnsideF4c_inL x
    rw [map_eq_zero_iff _ ε.symm.injective, map_eq_zero_iff _ ε.symm.injective]
    exact Iff.rfl
  have hsurj : Function.Surjective (f2.toMonoidHom.comp f1.toMonoidHom) := by
    intro y
    obtain ⟨a, rfl⟩ := f2.surjective y
    obtain ⟨x, rfl⟩ := f1.surjective a
    exact ⟨x, rfl⟩
  have hinj : Function.Injective (f2.toMonoidHom.comp f1.toMonoidHom) :=
    f2.injective.comp f1.injective
  have hmapP : burnsideF4c_P.map (f2.toMonoidHom.comp f1.toMonoidHom) =
      nativeParabolic .L3 (2 ^ 1) marking.field marking.basis false := by
    ext y
    obtain ⟨x, rfl⟩ := hsurj y
    rw [Subgroup.mem_map_iff_mem hinj]
    exact (hmemP x).symm
  have hmapL : burnsideF4c_L.map (f2.toMonoidHom.comp f1.toMonoidHom) =
      nativeParabolic .L3 (2 ^ 1) marking.field marking.basis true := by
    ext y
    obtain ⟨x, rfl⟩ := hsurj y
    rw [Subgroup.mem_map_iff_mem hinj]
    exact (hmemL x).symm
  have hP : burnsideF4c_P.map θ₀.toMonoidHom = M₁.subgroupOf ⊤ := by
    rw [h1, hθ₀, ← Subgroup.map_map, hmapP]
    rfl
  have hL : burnsideF4c_L.map θ₀.toMonoidHom = M₂.subgroupOf ⊤ := by
    rw [h2, hθ₀, ← Subgroup.map_map, hmapL]
    rfl
  refine ⟨θ₀.trans Subgroup.topEquiv, ?_, ?_⟩
  · have e : (θ₀.trans Subgroup.topEquiv).toMonoidHom =
        (⊤ : Subgroup E).subtype.comp θ₀.toMonoidHom := MonoidHom.ext fun _ => rfl
    rw [e, ← Subgroup.map_map, hP, Subgroup.map_subgroupOf_eq_of_le le_top]
  · have e : (θ₀.trans Subgroup.topEquiv).toMonoidHom =
        (⊤ : Subgroup E).subtype.comp θ₀.toMonoidHom := MonoidHom.ext fun _ => rfl
    rw [e, ← Subgroup.map_map, hL, Subgroup.map_subgroupOf_eq_of_le le_top]

end CFSG.ASVolI.ChF

namespace CFSG.ASVolI

open CFSG.Open

section


open CFSG.ASVolI.ChF in
theorem as_F_4_25 : F_4_25 := by
  intro p f E _ Gp M₁ M₂ hyp hGp s hs hs2
  obtain ⟨hp2, hf1, -⟩ := hyp.model
  subst hp2
  obtain ⟨chart, hmatch⟩ := hyp.lie_amalgam
  have hle : M₁ ≤ Gp := by rw [hGp]; exact le_top
  have hM1 : M₁ = chart.points := by
    rw [← hmatch.2.1]; exact (inf_eq_right.2 hle).symm
  rcases chart.coordinates with ⟨c, hk, -⟩ | ⟨hk, -⟩ |
      ⟨-, -, -, K, fK, finK, hcard, marking, h1, h2', h3, h4, h5⟩ | ⟨hk, -⟩ |
      ⟨-, e, K', fK', finK', charK', scope, hcase⟩
  · cases c <;> exact absurd hk (by decide)
  · exact absurd hk (by decide)
  · haveI := finK
    haveI := Fintype.ofFinite K
    haveI : CharP K 2 := charP_of_card_eq_prime (p := 2)
      (by rw [← Nat.card_eq_fintype_card, hcard])
    have h2eq : (2 : K) = 0 := CFSG.Quasithin.two_eq_zero_of_card_two hcard
    have hk2 := CFSG.Quasithin.eq_zero_or_eq_one_of_card_two hcard
    obtain ⟨ψ, hψ, heq⟩ := burnsideF4c_points_eq hcard h2eq hk2 marking (G2Native.pointParabolic K)
    have hI := burnsideF4c_InvolInCore_map ψ hψ (burnsideF4c_Pg_invol hcard h2eq hk2)
    have hM : M₁ = ((G2Native.pointParabolic K).comap (CFSG.Quasithin.g2HomC h2eq)).map ψ := by
      rw [hM1, h2', heq]
    rw [hM] at hs ⊢
    exact burnsideF4c_involInCore_pCoreOf hI s hs hs2
  · exact absurd hk (by decide)
  · rcases hcase with ⟨hk, -⟩ | ⟨hk, -⟩ <;> exact absurd hk (by decide)

end


open CFSG.ASVolI.ChF in
theorem as_F_4_9 : F_4_9 := by
  intro E _ Gp M₁ M₂ hyp hGp
  subst hGp
  obtain ⟨θ, rfl, rfl⟩ := burnsideF4c_part0 hyp
  exact ⟨burnsideF4c_partA_of_iface (burnsideF4c_iface_map θ burnsideF4c_iface_concrete),
    burnsideF4c_partB_map θ⟩

end CFSG.ASVolI
