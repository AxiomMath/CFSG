module

public import CFSG.RankThree.PartTwo.Sec19.KF1923ParO8Core
public import CFSG.RankThree.PartTwo.Sec19.KF1923ParO8Layer
import CFSG.LocalAnalysis.ComponentInitial.OrthogonalTailMaxBorel
import CFSG.LocalAnalysis.ComponentInitial.OrthogonalTailSylow
import CFSG.LocalAnalysis.ComponentInitial.OrthogonalTailUnipotentGroup
import CFSG.LocalAnalysis.ComponentInitial.OrthogonalTailWeylLift
import CFSG.RankThree.PartTwo.Sec4.RonanK429RowFOm8Model
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasFive
import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasSix
import CFSG.LocalAnalysis.ComponentInitial.OrthogonalReflectionSplitting
import CFSG.LocalAnalysis.ComponentInitial.OrthogonalTailPolar

public section

namespace CFSG.RankThree.PartTwo.Late

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.OrthogonalTail
open QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.RankThree.PartTwo.Sec4.RonanK429F
open CFSG.ABGLocalTools (IsSylowOf)
open scoped Pointwise

local notation "𝔽₂" => GaloisField 2 1
local notation "𝕍" => (Fin 3 ⊕ Fin 3 → GaloisField 2 1) × (Fin 2 → GaloisField 2 1)

theorem kfO8_polar_form_tail (v : 𝕍) (a : Fin 2 → 𝔽₂) :
    polar kfO8Form v (0, a) = polar kfO8Tail v.2 a := by
  rw [kfO8Form, polar_quadTail]
  simp

theorem kfO8_polar_form_hyp (v : 𝕍) (c : Fin 3 ⊕ Fin 3) :
    polar kfO8Form v (hypVec 𝔽₂ (Fin 2 → 𝔽₂) c) = v.1 c.swap := by
  rw [kfO8Form, polar_hypVec]

theorem kfO8_polar_tail_formula (α β : Fin 2 → 𝔽₂) :
    polar kfO8Tail α β = α 0 * β 1 + α 1 * β 0 := by
  have h2 := kfO8_gf2_two
  simp only [kfO8Tail, polar, minusTailForm_apply, Pi.add_apply]
  linear_combination (α 0 * β 0 + α 1 * β 1) * h2

theorem kfO8_tail_apply (a : Fin 2 → 𝔽₂) : kfO8Tail a = a 0 ^ 2 + a 0 * a 1 + a 1 ^ 2 := by
  simp [kfO8Tail, minusTailForm_apply]

abbrev KFO8State := 𝔽₂ × 𝔽₂ × (Fin 2 → 𝔽₂)

def kfO8Upd (X : Fin 3 ⊕ Fin 3 → 𝔽₂) (x y : 𝔽₂) : Fin 3 ⊕ Fin 3 → 𝔽₂ :=
  Function.update (Function.update X (Sum.inl 2) x) (Sum.inr 2) y

def kfO8BkOf (X : Fin 3 ⊕ Fin 3 → 𝔽₂) (s : KFO8State) : 𝕍 := (kfO8Upd X s.1 s.2.1, s.2.2)

def kfO8Bk (T : KFO8State → KFO8State) (v : 𝕍) : 𝕍 :=
  kfO8BkOf v.1 (T (v.1 (Sum.inl 2), v.1 (Sum.inr 2), v.2))

theorem kfO8Upd_inl (X : Fin 3 ⊕ Fin 3 → 𝔽₂) (x y : 𝔽₂) : kfO8Upd X x y (Sum.inl 2) = x := by
  simp [kfO8Upd, Function.update_apply]

theorem kfO8Upd_inr (X : Fin 3 ⊕ Fin 3 → 𝔽₂) (x y : 𝔽₂) : kfO8Upd X x y (Sum.inr 2) = y := by
  simp [kfO8Upd]

theorem kfO8Upd_upd (X : Fin 3 ⊕ Fin 3 → 𝔽₂) (x y x' y' : 𝔽₂) :
    kfO8Upd (kfO8Upd X x y) x' y' = kfO8Upd X x' y' := by
  funext c
  simp only [kfO8Upd, Function.update_apply]
  split_ifs <;> simp_all

theorem kfO8Bk_comp (T T' : KFO8State → KFO8State) (v : 𝕍) :
    kfO8Bk T' (kfO8Bk T v) = kfO8Bk (T' ∘ T) v := by
  simp only [kfO8Bk, kfO8BkOf, kfO8Upd_inl, kfO8Upd_inr, kfO8Upd_upd, Function.comp]

theorem kfO8Bk_id (v : 𝕍) : kfO8Bk id v = v := by
  refine Prod.ext ?_ rfl
  funext c
  simp only [kfO8Bk, kfO8BkOf, id, kfO8Upd, Function.update_apply]
  split_ifs with h1 h2 <;> simp_all

noncomputable def kfO8TE (a : Fin 2 → 𝔽₂) (s : KFO8State) : KFO8State :=
  (s.1 - (polar kfO8Tail s.2.2 a + kfO8Tail a * s.2.1), s.2.1, s.2.2 + s.2.1 • a)

noncomputable def kfO8TF (a : Fin 2 → 𝔽₂) (s : KFO8State) : KFO8State :=
  (s.1, s.2.1 - (polar kfO8Tail s.2.2 a + kfO8Tail a * s.1), s.2.2 + s.1 • a)

theorem kfO8_hypVec_form_zero (c : Fin 3 ⊕ Fin 3) : kfO8Form (hypVec 𝔽₂ (Fin 2 → 𝔽₂) c) = 0 :=
  quadTail_hypVec c

theorem kfO8_polar_hyp_tail (c : Fin 3 ⊕ Fin 3) (a : Fin 2 → 𝔽₂) :
    polar kfO8Form (hypVec 𝔽₂ (Fin 2 → 𝔽₂) c) (0, a) = 0 :=
  polar_hypVec_tail c a

theorem kfO8_eichlerE_eq (a : Fin 2 → 𝔽₂) (v : 𝕍) :
    eichler kfO8Form (hypVec 𝔽₂ (Fin 2 → 𝔽₂) (Sum.inl 2)) (0, a) v = kfO8Bk (kfO8TE a) v := by
  rw [eichler_apply (kfO8_hypVec_form_zero _) (kfO8_polar_hyp_tail _ a), kfO8_polar_form_hyp,
    kfO8_polar_form_tail,
    kfO8Form, quadTail_tail]
  refine Prod.ext ?_ ?_
  · funext c
    simp only [kfO8Bk, kfO8BkOf, kfO8TE, kfO8Upd, Function.update_apply, hypVec]
    rcases c with i | i
    · by_cases hi : i = 2
      · subst hi; simp
      · simp [hi, Pi.single_apply]
    · by_cases hi : i = 2
      · subst hi; simp
      · simp [hi, Pi.single_apply]
  · simp [kfO8Bk, kfO8BkOf, kfO8TE, hypVec]

theorem kfO8_eichlerF_eq (a : Fin 2 → 𝔽₂) (v : 𝕍) :
    eichler kfO8Form (hypVec 𝔽₂ (Fin 2 → 𝔽₂) (Sum.inr 2)) (0, a) v = kfO8Bk (kfO8TF a) v := by
  rw [eichler_apply (kfO8_hypVec_form_zero _) (kfO8_polar_hyp_tail _ a), kfO8_polar_form_hyp,
    kfO8_polar_form_tail,
    kfO8Form, quadTail_tail]
  refine Prod.ext ?_ ?_
  · funext c
    simp only [kfO8Bk, kfO8BkOf, kfO8TF, kfO8Upd, Function.update_apply, hypVec]
    rcases c with i | i
    · by_cases hi : i = 2
      · subst hi; simp
      · simp [hi, Pi.single_apply]
    · by_cases hi : i = 2
      · subst hi; simp
      · simp [hi, Pi.single_apply]
  · simp [kfO8Bk, kfO8BkOf, kfO8TF, hypVec]

noncomputable def kfO8a0 : Fin 2 → 𝔽₂ := ![1, 0]

noncomputable def kfO8a1 : Fin 2 → 𝔽₂ := ![0, 1]

noncomputable def kfO8Tg : KFO8State → KFO8State :=
  kfO8TE kfO8a0 ∘ kfO8TF kfO8a0 ∘ kfO8TE kfO8a0 ∘ kfO8TE kfO8a1

noncomputable def kfO8Tg' (s : KFO8State) : KFO8State :=
  (s.2.1, s.1 + s.2.2 0 + s.2.1, ![s.2.2 0 + s.2.2 1 + s.2.1, s.2.2 1 + s.2.1])

theorem kfO8Tg_eq (s : KFO8State) : kfO8Tg s = kfO8Tg' s := by
  obtain ⟨x, y, α⟩ := s
  obtain ⟨p, q, rfl⟩ : ∃ p q : 𝔽₂, α = ![p, q] :=
    ⟨α 0, α 1, by ext i; fin_cases i <;> rfl⟩
  rcases gf2_eq_zero_or_one x with rfl | rfl <;> rcases gf2_eq_zero_or_one y with rfl | rfl <;>
  rcases gf2_eq_zero_or_one p with rfl | rfl <;> rcases gf2_eq_zero_or_one q with rfl | rfl <;>
  simp [kfO8Tg, kfO8Tg', kfO8TE, kfO8TF, kfO8a0, kfO8a1, kfO8_polar_tail_formula,
    kfO8_tail_apply, gf2_one_add_one,
    kfO8_gf2_two, CharTwo.sub_eq_add]

theorem kfO8Tg'_iter (s : KFO8State) : kfO8Tg'^[5] s = s := by
  obtain ⟨x, y, α⟩ := s
  obtain ⟨p, q, rfl⟩ : ∃ p q : 𝔽₂, α = ![p, q] :=
    ⟨α 0, α 1, by ext i; fin_cases i <;> rfl⟩
  rcases gf2_eq_zero_or_one x with rfl | rfl <;> rcases gf2_eq_zero_or_one y with rfl | rfl <;>
  rcases gf2_eq_zero_or_one p with rfl | rfl <;> rcases gf2_eq_zero_or_one q with rfl | rfl <;>
  simp [kfO8Tg', gf2_one_add_one, kfO8_gf2_two]

noncomputable def kfO8RE (a : Fin 2 → 𝔽₂) : 𝕍 ≃ₗ[𝔽₂] 𝕍 :=
  eichler (quadTail 3 kfO8Tail) (hypVec 𝔽₂ (Fin 2 → 𝔽₂) (Sum.inl 2)) (0, a)

noncomputable def kfO8RF (a : Fin 2 → 𝔽₂) : 𝕍 ≃ₗ[𝔽₂] 𝕍 :=
  eichler (quadTail 3 kfO8Tail) (hypVec 𝔽₂ (Fin 2 → 𝔽₂) (Sum.inr 2)) (0, a)

noncomputable def kfO8N3 : 𝕍 ≃ₗ[𝔽₂] 𝕍 := tailWeylElt 3 kfO8Tail kfO8a0 2

theorem kfO8RE_apply (a : Fin 2 → 𝔽₂) (v : 𝕍) : kfO8RE a v = kfO8Bk (kfO8TE a) v :=
  kfO8_eichlerE_eq a v

theorem kfO8RF_apply (a : Fin 2 → 𝔽₂) (v : 𝕍) : kfO8RF a v = kfO8Bk (kfO8TF a) v :=
  kfO8_eichlerF_eq a v

theorem kfO8N3_apply (v : 𝕍) :
    kfO8N3 v = kfO8Bk (kfO8TE kfO8a0 ∘ kfO8TF kfO8a0 ∘ kfO8TE kfO8a0) v := by
  have h1 : kfO8Tail kfO8a0 = 1 := by simp [kfO8_tail_apply, kfO8a0]
  have h2 : (kfO8Tail kfO8a0)⁻¹ • kfO8a0 = kfO8a0 := by rw [h1]; simp
  rw [kfO8N3, tailWeylElt, if_neg (by decide)]
  simp only [LinearEquiv.mul_apply]
  rw [h2]
  change kfO8RE kfO8a0 (kfO8RF kfO8a0 (kfO8RE kfO8a0 v)) = _
  rw [kfO8RE_apply, kfO8RF_apply, kfO8RE_apply, kfO8Bk_comp, kfO8Bk_comp]
  simp only [Function.comp_assoc]

noncomputable def kfO8G5 : 𝕍 ≃ₗ[𝔽₂] 𝕍 := kfO8N3 * kfO8RE kfO8a1

theorem kfO8G5_apply_a (v : 𝕍) : kfO8G5 v = kfO8N3 (kfO8RE kfO8a1 v) := by
  rw [kfO8G5, LinearEquiv.mul_apply]

theorem kfO8G5_apply_b (v : 𝕍) : kfO8N3 (kfO8RE kfO8a1 v) =
    kfO8Bk (kfO8TE kfO8a0 ∘ kfO8TF kfO8a0 ∘ kfO8TE kfO8a0) (kfO8Bk (kfO8TE kfO8a1) v) := by
  rw [kfO8RE_apply, kfO8N3_apply]

theorem kfO8G5_apply_c :
    kfO8Tg = (kfO8TE kfO8a0 ∘ kfO8TF kfO8a0 ∘ kfO8TE kfO8a0) ∘ kfO8TE kfO8a1 := by
  funext s
  simp only [kfO8Tg, Function.comp_apply]

theorem kfO8G5_apply (v : 𝕍) : kfO8G5 v = kfO8Bk kfO8Tg v := by
  rw [kfO8G5_apply_a, kfO8G5_apply_b, kfO8Bk_comp, kfO8G5_apply_c]

theorem kfO8G5_pow (n : ℕ) (v : 𝕍) : (kfO8G5 ^ n) v = kfO8Bk (kfO8Tg^[n]) v := by
  induction n with
  | zero => simp [kfO8Bk_id]
  | succ n ih =>
    rw [pow_succ', LinearEquiv.mul_apply, ih, kfO8G5_apply, kfO8Bk_comp, Function.iterate_succ']

theorem kfO8G5_pow_five : kfO8G5 ^ 5 = 1 := by
  apply LinearEquiv.ext
  intro v
  rw [kfO8G5_pow]
  have : kfO8Tg^[5] = id := by
    have h : kfO8Tg = kfO8Tg' := funext kfO8Tg_eq
    rw [h]
    exact funext kfO8Tg'_iter
  rw [this, kfO8Bk_id]
  rfl

theorem kfO8G5_ne_one : kfO8G5 ≠ 1 := by
  intro h
  have h0 : kfO8G5 (hypVec 𝔽₂ (Fin 2 → 𝔽₂) (Sum.inl 2)) = hypVec 𝔽₂ (Fin 2 → 𝔽₂) (Sum.inl 2) := by
    rw [h]; rfl
  have h1 := congrArg (fun v : 𝕍 => v.1 (Sum.inl 2)) h0
  simp only [kfO8G5_apply, kfO8Bk, kfO8BkOf, kfO8Upd_inl, kfO8Tg_eq, kfO8Tg'] at h1
  simp [hypVec] at h1

theorem kfO8G5_orderOf : orderOf kfO8G5 = 5 := by
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  exact orderOf_eq_prime kfO8G5_pow_five kfO8G5_ne_one

theorem kfO8_hirr : ∀ s : 𝔽₂, s ^ 2 + 1 * s + 1 ≠ 0 := by
  intro s
  rcases gf2_eq_zero_or_one s with rfl | rfl
  · simp
  · rw [one_pow, one_mul, gf2_one_add_one, zero_add]; exact one_ne_zero

theorem kfO8_hani : kfO8Tail.Anisotropic := anisotropic_minusTailForm kfO8_hirr

theorem kfO8_hreg : (polarBilin kfO8Tail).Nondegenerate := nondegenerate_minusTailForm kfO8_hirr

theorem kfO8a0_ne_zero : kfO8a0 ≠ 0 := by
  intro h
  have := congrFun h 0
  simp [kfO8a0] at this

@[expose] noncomputable def kfO8G0 : Subgroup (𝕍 ≃ₗ[𝔽₂] 𝕍) :=
  orthElementaryGroup (quadTail 3 kfO8Tail)

theorem kfO8_le_Gam_of_smul {g : 𝕍 ≃ₗ[𝔽₂] 𝕍} (hg : g ∈ kfO8G0)
    (h : g • kfO8Flag = kfO8Flag) : g ∈ kfO8Gam :=
  mem_kfO8Gam.2 ⟨orthElementaryGroup_le _ hg, h⟩

theorem kfO8_borel_le_Gam : tailBorel 3 kfO8Tail ≤ kfO8Gam := by
  intro b hb
  obtain ⟨hbG, hbF⟩ := mem_tailBorel.1 hb
  exact mem_kfO8Gam.2 ⟨orthElementaryGroup_le _ hbG, hbF 3 (by norm_num) (by norm_num)⟩

theorem kfO8_le_Gam_of_not_mem {M : Subgroup (𝕍 ≃ₗ[𝔽₂] 𝕍)} (hMG : M ≤ kfO8G0)
    (hBM : tailBorel 3 kfO8Tail ≤ M) (h2 : kfO8N3 ∉ M) : M ≤ kfO8Gam := by
  have hgen := eq_closure_of_tailBorel_le kfO8_hani kfO8a0_ne_zero hMG hBM
  rw [hgen, Subgroup.closure_le]
  rintro _ (hb | ⟨j, hj, rfl⟩)
  · exact kfO8_borel_le_Gam hb
  · refine kfO8_le_Gam_of_smul (tailWeylElt_mem kfO8a0 j) ?_
    have := (tailWeylElt_smul_tailFlag kfO8_hani kfO8a0_ne_zero (r := 3) (qA := kfO8Tail) 2 j).2
      (by rintro rfl; exact h2 hj)
    exact this

theorem kfO8RE_mem_borel (a : Fin 2 → 𝔽₂) : kfO8RE a ∈ tailBorel 3 kfO8Tail := by
  have h : kfO8RE a ∈ tailRootGroup 3 kfO8Tail (OrthogonalSplit.eps 3 2) :=
    mem_tailRootGroup_eps.2 ⟨a, rfl⟩
  exact tailUnipotent_le_tailBorel kfO8_hani
    (tailRootGroup_le_tailUnipotent (eps_mem_posRootsB 2) h)

theorem kfO8_five_dvd {D : Subgroup (𝕍 ≃ₗ[𝔽₂] 𝕍)} (hBD : tailBorel 3 kfO8Tail ≤ D)
    (h2 : kfO8N3 ∈ D) : 5 ∣ Nat.card D := by
  have hg : kfO8G5 ∈ D := D.mul_mem h2 (hBD (kfO8RE_mem_borel kfO8a1))
  have := orderOf_dvd_natCard (⟨kfO8G5, hg⟩ : D)
  rwa [Subgroup.orderOf_mk, kfO8G5_orderOf] at this

instance kfO8_finiteW : Finite (𝕍 ≃ₗ[𝔽₂] 𝕍) :=
  Finite.of_injective (fun g : 𝕍 ≃ₗ[𝔽₂] 𝕍 => (g : 𝕍 → 𝕍)) DFunLike.coe_injective

@[expose] noncomputable def kfO8U : Subgroup ↥kfO8G0 :=
  (tailUnipotent 3 kfO8Tail).subgroupOf kfO8G0

@[expose] noncomputable def kfO8B : Subgroup ↥kfO8G0 :=
  (tailBorel 3 kfO8Tail).subgroupOf kfO8G0

theorem kfO8_sylow : IsSylowOf 2 kfO8U ⊤ ∧ Subgroup.normalizer (kfO8U : Set ↥kfO8G0) = kfO8B := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP 𝔽₂ 2 := inferInstance
  obtain ⟨⟨S, hS⟩, hN, -⟩ := orthogonal_geometry_tail_Sylow_flag_normalizer (p := 2) (K := 𝔽₂)
    (r := 3) (qA := kfO8Tail) (by norm_num) kfO8_hani kfO8_hreg (Or.inr finrank_fin_two_fun)
  refine ⟨?_, hN⟩
  rw [CFSG.ABGLocalTools.isSylowOf_iff]
  refine ⟨le_top, ?_, ?_⟩
  · have := S.isPGroup'
    rwa [hS] at this
  · rw [Subgroup.relIndex_top_right]
    have := S.not_dvd_index
    rwa [hS] at this

theorem kfO8_card_gf2 : Nat.card 𝔽₂ = 2 := by
  rw [GaloisField.card 2 1 one_ne_zero]; simp

theorem kfO8_card_U : Nat.card (tailUnipotent 3 kfO8Tail) = 2 ^ 12 := by
  rw [card_tailUnipotent kfO8_hani, kfO8_card_gf2, finrank_fin_two_fun]

theorem kfO8_tailDiag_one :
    tailDiag 3 (1 : Fin 3 → 𝔽₂ˣ) (1 : (Fin 2 → 𝔽₂) ≃ₗ[𝔽₂] (Fin 2 → 𝔽₂)) = 1 :=
  LinearEquiv.ext fun v => by rw [tailDiag_apply, map_one]; rfl

noncomputable def kfO8Theta :
    (Fin 3 → 𝔽₂ˣ) × ((Fin 2 → 𝔽₂) ≃ₗ[𝔽₂] (Fin 2 → 𝔽₂)) →* (𝕍 ≃ₗ[𝔽₂] 𝕍) where
  toFun p := tailDiag 3 p.1 p.2
  map_one' := kfO8_tailDiag_one
  map_mul' p q := (tailDiag_mul p.1 q.1 p.2 q.2).symm

theorem kfO8_card_aut : Nat.card ((Fin 2 → 𝔽₂) ≃ₗ[𝔽₂] (Fin 2 → 𝔽₂)) = 6 := by
  have h := Nat.card_congr
    ((Matrix.GeneralLinearGroup.toLin.trans
      (LinearMap.GeneralLinearGroup.generalLinearEquiv 𝔽₂ (Fin 2 → 𝔽₂))).toEquiv)
  rw [← h, kfO8_card_GL]
  decide

theorem kfO8_card_torus_dvd : Nat.card (tailTorus 3 kfO8Tail) ∣ 6 := by
  have hle : tailTorus 3 kfO8Tail ≤ kfO8Theta.range := by
    rintro g ⟨-, t, h, -, rfl⟩
    exact ⟨(t, h), rfl⟩
  haveI := subsingleton_units_gf2
  have h1 : Nat.card (Fin 3 → 𝔽₂ˣ) = 1 := by
    haveI : Unique (Fin 3 → 𝔽₂ˣ) := uniqueOfSubsingleton 1
    exact Nat.card_unique
  have h2 : Nat.card ((Fin 3 → 𝔽₂ˣ) × ((Fin 2 → 𝔽₂) ≃ₗ[𝔽₂] (Fin 2 → 𝔽₂))) = 6 := by
    rw [Nat.card_prod, h1, kfO8_card_aut, one_mul]
  exact h2 ▸ (Subgroup.card_dvd_of_le hle).trans (Subgroup.card_range_dvd kfO8Theta)

theorem kfO8_card_B0 :
    Nat.card (tailBorel 3 kfO8Tail) = 2 ^ 12 * Nat.card (tailTorus 3 kfO8Tail) := by
  haveI := tailUnipotent_normal kfO8_hani (r := 3) (qA := kfO8Tail)
  obtain ⟨e⟩ := nonempty_quotient_mulEquiv_tailTorus kfO8_hani (r := 3) (qA := kfO8Tail)
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup
    ((tailUnipotent 3 kfO8Tail).subgroupOf (tailBorel 3 kfO8Tail))
  have h2 : Nat.card ((tailUnipotent 3 kfO8Tail).subgroupOf (tailBorel 3 kfO8Tail)) = 2 ^ 12 := by
    rw [← kfO8_card_U]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (tailUnipotent_le_tailBorel kfO8_hani)).toEquiv
  rw [h1, h2, Nat.card_congr e.toEquiv, mul_comm]

theorem kfO8_not_five_dvd_B : ¬ 5 ∣ Nat.card kfO8B := by
  have h : Nat.card kfO8B = Nat.card (tailBorel 3 kfO8Tail) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe tailBorel_le).toEquiv
  rw [h, kfO8_card_B0]
  intro h5
  rcases (Nat.Prime.dvd_mul Nat.prime_five).1 h5 with h | h
  · have := Nat.Prime.dvd_of_dvd_pow Nat.prime_five h
    omega
  · have := h.trans kfO8_card_torus_dvd
    omega

theorem kfO8_hH (D E : Subgroup ↥kfO8G0) (hND : Subgroup.normalizer (kfO8U : Set ↥kfO8G0) ≤ D)
    (hD5 : ¬ 5 ∣ Nat.card D) (hED : E ≤ D) (hE3 : ∀ e ∈ E, e ^ 3 = 1) (hE9 : Nat.card E = 9)
    (t : ↥kfO8G0) (htU : t ∈ kfO8U) (htN : ∀ e ∈ E, t * e * t⁻¹ ∈ E) :
    ¬ ∀ e ∈ E, t ^ 2 * e * (t ^ 2)⁻¹ = e⁻¹ := by
  intro hinv
  have hB : kfO8B ≤ D := (kfO8_sylow.2 ▸ hND)
  set D' : Subgroup (𝕍 ≃ₗ[𝔽₂] 𝕍) := D.map kfO8G0.subtype with hD'
  have hBD' : tailBorel 3 kfO8Tail ≤ D' := fun b hb =>
    ⟨⟨b, tailBorel_le hb⟩, hB (Subgroup.mem_subgroupOf.2 hb), rfl⟩
  have hDG : D' ≤ kfO8G0 := Subgroup.map_subtype_le D
  have hn3 : kfO8N3 ∉ D' := fun h => hD5 (by
    rw [← Subgroup.card_map_of_injective kfO8G0.subtype_injective]
    exact kfO8_five_dvd hBD' h)
  have hle : D' ≤ kfO8Gam := kfO8_le_Gam_of_not_mem hDG hBD' hn3
  have htΓ : (t : 𝕍 ≃ₗ[𝔽₂] 𝕍) ∈ kfO8Gam :=
    kfO8_borel_le_Gam (tailUnipotent_le_tailBorel kfO8_hani (Subgroup.mem_subgroupOf.1 htU))
  refine kfO8_layer (E.map kfO8G0.subtype) (le_trans (Subgroup.map_mono hED) hle) ?_ ?_ t htΓ
    ?_ ?_
  · rintro _ ⟨e, he, rfl⟩
    have := hE3 e he
    simpa using congrArg (fun x : ↥kfO8G0 => (x : 𝕍 ≃ₗ[𝔽₂] 𝕍)) this
  · rwa [Subgroup.card_map_of_injective kfO8G0.subtype_injective]
  · rintro _ ⟨e, he, rfl⟩
    exact ⟨t * e * t⁻¹, htN e he, by simp⟩
  · rintro _ ⟨e, he, rfl⟩
    have := hinv e he
    simpa using congrArg (fun x : ↥kfO8G0 => (x : 𝕍 ≃ₗ[𝔽₂] 𝕍)) this

theorem kfO8_data : KFParO8Data ↥kfO8G0 :=
  KFParO8Data.of_std kfO8_sylow.1 (by rw [kfO8_sylow.2]; exact kfO8_not_five_dvd_B)
    (fun D E h1 h2 h3 h4 h5 t ht h6 => kfO8_hH D E h1 h2 h3 h4 h5 t ht h6)

theorem kfO8_two_pow_dvd : 2 ^ 12 ∣ Nat.card ↥kfO8G0 := by
  have h : Nat.card kfO8U = 2 ^ 12 := by
    rw [← kfO8_card_U]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (tailUnipotent_le_tailBorel kfO8_hani |>.trans tailBorel_le)).toEquiv
  exact h ▸ Subgroup.card_subgroup_dvd_card kfO8U

end CFSG.RankThree.PartTwo.Late
