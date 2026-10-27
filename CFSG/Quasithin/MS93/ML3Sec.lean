module

public import CFSG.Quasithin.MS93.ML3Stmt
public import CFSG.Quasithin.MS93.ML3Facts

public section

namespace CFSG.Quasithin.MS93

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique Matrix
open scoped commutatorElement

variable {F : Type} [Field F]

theorem mulVec_e0 (A : Matrix (Fin 3) (Fin 3) F) : A *ᵥ ![1, 0, 0] = fun i => A i 0 := by
  funext i
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three]

theorem mem_ptStab {g : SL3 F} :
    g ∈ (ptStab : Subgroup (SL3 F)) ↔ ((g : SL3 F) : Matrix (Fin 3) (Fin 3) F) 1 0 = 0 ∧
      ((g : SL3 F) : Matrix (Fin 3) (Fin 3) F) 2 0 = 0 :=
  Iff.rfl

theorem mem_ptStab_iff_mulVec_e0 {g : SL3 F} :
    g ∈ (ptStab : Subgroup (SL3 F)) ↔
      ((g : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ ![1, 0, 0] ∈ pt0 := by
  rw [mem_ptStab, mulVec_e0, mem_pt0]

theorem rootGroup_le_ptLevi {i j : Fin 3} (h : (i = 0 ∧ j = 1) ∨ (i = 0 ∧ j = 2) ∨
    (i = 1 ∧ j = 2) ∨ (i = 2 ∧ j = 1)) : rootGroup i j ≤ (ptLevi : Subgroup (SL3 F)) := by
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact le_sup_left.trans (le_sup_left.trans le_sup_left)
  · exact le_sup_right.trans (le_sup_left.trans le_sup_left)
  · exact le_sup_right.trans le_sup_left
  · exact le_sup_right

theorem ptLevi_le_ptStab : (ptLevi : Subgroup (SL3 F)) ≤ ptStab := by
  have h : ∀ i j : Fin 3, j ≠ 0 → i ≠ j → rootGroup i j ≤ (ptStab : Subgroup (SL3 F)) := by
    rintro i j hj hij _ ⟨c, rfl⟩
    rw [mem_ptStab_iff_mulVec_e0, rootElt_mulVec hij, mem_pt0]
    fin_cases j
    · exact absurd rfl hj
    all_goals simp
  exact sup_le (sup_le (sup_le (h 0 1 (by decide) (by decide)) (h 0 2 (by decide) (by decide)))
    (h 1 2 (by decide) (by decide))) (h 2 1 (by decide) (by decide))

theorem mulVec_of_mem_ptLevi {g : SL3 F} (hg : g ∈ (ptLevi : Subgroup (SL3 F))) {y : Fin 3 → F}
    (hy : y ∈ pt0) : ((g : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ y = y := by
  have h : y ∈ fixN (ptLevi : Subgroup (SL3 F)) := by
    rw [ptLevi, fixN_ptLevi]
    exact hy
  exact h g hg

theorem eq_smul_e0_of_mem_pt0 {y : Fin 3 → F} (hy : y ∈ pt0) : y = y 0 • ![1, 0, 0] := by
  rw [mem_pt0] at hy
  funext k
  fin_cases k <;> simp [hy.1, hy.2]

theorem exists_mulVec_e0_eq {v : Fin 3 → F} (hv : v ≠ 0) :
    ∃ g : SL3 F, ((g : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ ![1, 0, 0] = v := by
  by_cases h0 : v 0 = 0
  · by_cases h1 : v 1 = 0
    · have h2 : v 2 ≠ 0 := by
        intro h2
        apply hv
        funext k
        fin_cases k
        · exact h0
        · exact h1
        · exact h2
      refine ⟨⟨!![0, 1, 0; 0, 0, (v 2)⁻¹; v 2, 0, 0], ?_⟩, ?_⟩
      · rw [Matrix.det_fin_three]
        simp [h2]
      · rw [mulVec_e0]
        funext k
        fin_cases k <;> simp [h0, h1]
    · refine ⟨⟨!![0, -(v 1)⁻¹, 0; v 1, 0, 0; v 2, 0, 1], ?_⟩, ?_⟩
      · rw [Matrix.det_fin_three]
        simp [h1]
      · rw [mulVec_e0]
        funext k
        fin_cases k <;> simp [h0]
  · refine ⟨⟨!![v 0, 0, 0; v 1, (v 0)⁻¹, 0; v 2, 0, 1], ?_⟩, ?_⟩
    · rw [Matrix.det_fin_three]
      simp [h0]
    · rw [mulVec_e0]
      funext k
      fin_cases k <;> simp

theorem eq_top_of_ptLevi_le {K : Subgroup (SL3 F)} (hK : K.Normal)
    (h : (ptLevi : Subgroup (SL3 F)) ≤ K) : K = ⊤ := by
  have hcyc : ∀ i j : Fin 3, (∀ c : F, rootElt i j c ∈ K) →
      ∀ c : F, rootElt (i + 1) (j + 1) c ∈ K := fun i j hij c => by
    rw [← cyc_conj_rootElt]
    exact hK.conj_mem _ (hij c) cyc
  have h01 : ∀ c : F, rootElt 0 1 c ∈ K := fun c =>
    h (rootGroup_le_ptLevi (Or.inl ⟨rfl, rfl⟩) (rootElt_mem_rootGroup 0 1 c))
  have h02 : ∀ c : F, rootElt 0 2 c ∈ K := fun c =>
    h (rootGroup_le_ptLevi (Or.inr (Or.inl ⟨rfl, rfl⟩)) (rootElt_mem_rootGroup 0 2 c))
  have h12 := hcyc 0 1 h01
  have h20 := hcyc 1 2 h12
  have h10 := hcyc 0 2 h02
  have h21 := hcyc 1 0 h10
  apply eq_top_of_rootElt_mem
  intro i j c hij
  fin_cases i <;> fin_cases j
  · exact absurd rfl hij
  · exact h01 c
  · exact h02 c
  · exact h10 c
  · exact absurd rfl hij
  · exact h12 c
  · exact h20 c
  · exact h21 c
  · exact absurd rfl hij

theorem ptLevi_invariant_cases (S : AddSubgroup (Fin 3 → F))
    (hS : ∀ g ∈ (ptLevi : Subgroup (SL3 F)), ∀ x ∈ S,
      ((g : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ x ∈ S) :
    (∀ x ∈ S, x ∈ pt0) ∨ ∀ x, x ∈ S := by
  by_cases h : ∀ x ∈ S, x ∈ pt0
  · exact Or.inl h
  right
  push Not at h
  obtain ⟨x, hx, hx0⟩ := h
  have hsingle : ∀ i j : Fin 3, i ≠ j → rootGroup i j ≤ (ptLevi : Subgroup (SL3 F)) →
      ∀ y ∈ S, y j ≠ 0 → ∀ d : F, Pi.single i d ∈ S := fun i j hij hle y hy hyj d => by
    have := S.sub_mem (hS _ (hle (rootElt_mem_rootGroup i j (d / y j))) y hy) hy
    rwa [rootElt_mulVec hij, add_sub_cancel_left, div_mul_cancel₀ d hyj] at this
  have l01 := rootGroup_le_ptLevi (F := F) (i := 0) (j := 1) (Or.inl ⟨rfl, rfl⟩)
  have l02 := rootGroup_le_ptLevi (F := F) (i := 0) (j := 2) (Or.inr (Or.inl ⟨rfl, rfl⟩))
  have l12 := rootGroup_le_ptLevi (F := F) (i := 1) (j := 2)
    (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)))
  have l21 := rootGroup_le_ptLevi (F := F) (i := 2) (j := 1)
    (Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩)))
  have hall : ∀ k : Fin 3, ∀ d : F, Pi.single k d ∈ S := by
    rw [mem_pt0, not_and_or] at hx0
    rcases hx0 with h1 | h2
    · have s0 := hsingle 0 1 (by decide) l01 x hx h1
      have s2 := hsingle 2 1 (by decide) l21 x hx h1
      have s1 : ∀ d : F, Pi.single 1 d ∈ S :=
        hsingle 1 2 (by decide) l12 (Pi.single 2 1) (s2 1) (by simp)
      intro k
      fin_cases k
      · exact s0
      · exact s1
      · exact s2
    · have s0 := hsingle 0 2 (by decide) l02 x hx h2
      have s1 := hsingle 1 2 (by decide) l12 x hx h2
      have s2 : ∀ d : F, Pi.single 2 d ∈ S :=
        hsingle 2 1 (by decide) l21 (Pi.single 1 1) (s1 1) (by simp)
      intro k
      fin_cases k
      · exact s0
      · exact s1
      · exact s2
  intro z
  have hz : z = Pi.single 0 (z 0) + Pi.single 1 (z 1) + Pi.single 2 (z 2) := by
    funext k
    fin_cases k <;> simp
  rw [hz]
  exact S.add_mem (S.add_mem (hall 0 _) (hall 1 _)) (hall 2 _)

theorem dualMat_mul (g h : SL3 F) : dualMat (g * h) = dualMat g * dualMat h := by
  rw [dualMat, dualMat, dualMat, _root_.mul_inv_rev, coe_mul_SL3, Matrix.transpose_mul]

theorem dualMat_one : dualMat (1 : SL3 F) = 1 := by
  rw [dualMat, inv_one, coe_one_SL3, Matrix.transpose_one]

theorem dualMat_mulVec_dotProduct (g : SL3 F) (y x : Fin 3 → F) :
    (dualMat g *ᵥ y) ⬝ᵥ (((g : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ x) = y ⬝ᵥ x := by
  rw [dualMat, Matrix.mulVec_transpose, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul,
    ← coe_mul_SL3, inv_mul_cancel, coe_one_SL3, Matrix.vecMul_one]

theorem diagPt_mul_inv (t : F) (ht : t ≠ 0) : diagPt t ht * diagPt t⁻¹ (inv_ne_zero ht) = 1 := by
  apply Subtype.ext
  change ((diagPt t ht : SL3 F) : Matrix (Fin 3) (Fin 3) F) *
    ((diagPt t⁻¹ (inv_ne_zero ht) : SL3 F) : Matrix (Fin 3) (Fin 3) F) =
      ((1 : SL3 F) : Matrix (Fin 3) (Fin 3) F)
  rw [coe_one_SL3, diagPt, diagPt, SpecialLinearGroup.diag2n_coe, SpecialLinearGroup.diag2n_coe,
    Matrix.diagonal_mul_diagonal]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [ht]

theorem dualMat_diagPt_mulVec (t : F) (ht : t ≠ 0) (y : Fin 3 → F) :
    dualMat (diagPt t ht) *ᵥ y = ![t⁻¹ * y 0, t * y 1, y 2] := by
  rw [dualMat, inv_eq_of_mul_eq_one_right (diagPt_mul_inv t ht), diagPt,
    SpecialLinearGroup.diag2n_coe, Matrix.diagonal_transpose]
  funext k
  fin_cases k <;> simp [Matrix.mulVec_diagonal]

theorem diagPt_mem_ptStab (t : F) (ht : t ≠ 0) : diagPt t ht ∈ (ptStab : Subgroup (SL3 F)) := by
  rw [mem_ptStab_iff_mulVec_e0, diagPt_mulVec, mem_pt0]
  simp

theorem ptStab_dual_invariant_cases (S : AddSubgroup (Fin 3 → F))
    (hS : ∀ g ∈ (ptStab : Subgroup (SL3 F)), ∀ y ∈ S, dualMat g *ᵥ y ∈ S) :
    (∀ y ∈ S, y 0 = 0) ∨ ∀ y, y ∈ S := by
  by_cases h : ∀ y ∈ S, y 0 = 0
  · exact Or.inl h
  right
  push Not at h
  obtain ⟨y, hy, hy0⟩ := h
  have hroot : ∀ j : Fin 3, j ≠ 0 → ∀ d : F, Pi.single j d ∈ S := fun j hj d => by
    have hle : rootGroup 0 j ≤ (ptLevi : Subgroup (SL3 F)) := by
      apply rootGroup_le_ptLevi
      fin_cases j
      · exact absurd rfl hj
      · exact Or.inl ⟨rfl, rfl⟩
      · exact Or.inr (Or.inl ⟨rfl, rfl⟩)
    have hmem := ptLevi_le_ptStab (hle (rootElt_mem_rootGroup 0 j (-(d / y 0))))
    have := S.sub_mem (hS _ hmem y hy) hy
    rwa [dualMat_rootElt_mulVec hj.symm, add_sub_cancel_left, neg_neg,
      div_mul_cancel₀ d hy0] at this
  have h0 : Pi.single 0 (y 0) ∈ S := by
    have h1 := S.sub_mem (S.sub_mem hy (hroot 1 (by decide) (y 1))) (hroot 2 (by decide) (y 2))
    have he : y - Pi.single 1 (y 1) - Pi.single 2 (y 2) = Pi.single 0 (y 0) := by
      funext k
      fin_cases k <;> simp
    rwa [he] at h1
  have hall : ∀ k : Fin 3, ∀ d : F, Pi.single k d ∈ S := by
    intro k d
    fin_cases k
    · by_cases hd : d = 0
      · rw [hd, Pi.single_zero]
        exact S.zero_mem
      have ht : y 0 / d ≠ 0 := div_ne_zero hy0 hd
      have := hS _ (diagPt_mem_ptStab _ ht) _ h0
      have he : dualMat (diagPt (y 0 / d) ht) *ᵥ Pi.single 0 (y 0) = Pi.single 0 d := by
        rw [dualMat_diagPt_mulVec]
        funext k
        fin_cases k <;> simp [hy0]
      rwa [he] at this
    · exact hroot 1 (by decide) d
    · exact hroot 2 (by decide) d
  intro z
  have hz : z = Pi.single 0 (z 0) + Pi.single 1 (z 1) + Pi.single 2 (z 2) := by
    funext k
    fin_cases k <;> simp
  rw [hz]
  exact S.add_mem (S.add_mem (hall 0 _) (hall 1 _)) (hall 2 _)

@[expose] def natAct (dual : Bool) (g : SL3 F) : Matrix (Fin 3) (Fin 3) F :=
  if dual then dualMat g else ((g : SL3 F) : Matrix (Fin 3) (Fin 3) F)

theorem natAct_false (g : SL3 F) :
    natAct false g = ((g : SL3 F) : Matrix (Fin 3) (Fin 3) F) :=
  rfl

theorem natAct_true (g : SL3 F) : natAct true g = dualMat g :=
  rfl

theorem mem_of_natAct_invariant (dual : Bool) (S : AddSubgroup (Fin 3 → F))
    (hS : ∀ (g : SL3 F), ∀ y ∈ S, natAct dual g *ᵥ y ∈ S) {y : Fin 3 → F} (hy : y ∈ S)
    (hy0 : y ≠ 0) (z : Fin 3 → F) : z ∈ S := by
  cases dual
  · exact mem_of_invariant S (fun g x hx => hS g x hx) hy hy0 z
  · refine mem_of_invariant S (fun g x hx => ?_) hy hy0 z
    let gT : SL3 F := ⟨((g : SL3 F) : Matrix (Fin 3) (Fin 3) F)ᵀ, by
      rw [Matrix.det_transpose]
      exact g.2⟩
    have hg : dualMat gT⁻¹ = ((g : SL3 F) : Matrix (Fin 3) (Fin 3) F) := by
      rw [dualMat, inv_inv]
      exact Matrix.transpose_transpose _
    have := hS gT⁻¹ x hx
    rwa [natAct_true, hg] at this

section Sec

variable {𝔾 : Type} [Group 𝔾] {L : Subgroup 𝔾}

structure NatSec (L V K : Subgroup 𝔾) (α : ↥L →* ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 F))
    (dual : Bool) where
  norm : L ≤ Subgroup.normalizer (V : Set 𝔾)
  le : K ≤ V
  β : ↥V →* Multiplicative (Fin 3 → F)
  surj : Function.Surjective β
  ker : ∀ v : ↥V, β v = 1 ↔ (v : 𝔾) ∈ K
  equiv : ∀ (l : ↥L) (u v : ↥V), (v : 𝔾) = l * u * l⁻¹ →
    Multiplicative.toAdd (β v) = natAct dual (toSL3 α l) *ᵥ Multiplicative.toAdd (β u)

variable {V K : Subgroup 𝔾} {α : ↥L →* ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 F)} {dual : Bool}

theorem moduleAct_eq_natAct (dual : Bool) (l : ↥L) :
    moduleAct dual (α l : Matrix.GeneralLinearGroup (Fin 3) F) = natAct dual (toSL3 α l) := by
  cases dual
  · rw [natAct_false, coe_toSL3]
    rfl
  · rw [natAct_true, dualMat, ← map_inv, coe_toSL3, map_inv]
    rfl

noncomputable def NatSec.ofIsSum (h : IsSumOfNaturalModulesVia L V K α dual 1) :
    NatSec L V K α dual where
  norm := h.1
  le := h.2.1
  β := (AddEquiv.toMultiplicative (AddEquiv.funUnique (Fin 1) (Fin 3 → F))).toMonoidHom.comp
    (Classical.choose h.2.2)
  surj := (AddEquiv.toMultiplicative (AddEquiv.funUnique (Fin 1) (Fin 3 → F))).surjective.comp
    (Classical.choose_spec h.2.2).1
  ker v := by
    rw [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.map_eq_one_iff,
      ← MonoidHom.mem_ker, (Classical.choose_spec h.2.2).2.1, Subgroup.mem_subgroupOf]
  equiv l u v huv := by
    have := (Classical.choose_spec h.2.2).2.2 l u v huv 0
    rw [moduleAct_eq_natAct] at this
    exact this

namespace NatSec

variable (N : NatSec L V K α dual)
include N

open Classical in
noncomputable def coord (v : 𝔾) : Fin 3 → F :=
  if h : v ∈ V then Multiplicative.toAdd (N.β ⟨v, h⟩) else 0

theorem coord_of_mem {v : 𝔾} (hv : v ∈ V) :
    N.coord v = Multiplicative.toAdd (N.β ⟨v, hv⟩) :=
  dite_eq_left hv

theorem coord_one : N.coord 1 = 0 := by
  rw [N.coord_of_mem V.one_mem]
  exact congrArg Multiplicative.toAdd (map_one N.β)

theorem coord_mul {v w : 𝔾} (hv : v ∈ V) (hw : w ∈ V) :
    N.coord (v * w) = N.coord v + N.coord w := by
  rw [N.coord_of_mem (V.mul_mem hv hw), N.coord_of_mem hv, N.coord_of_mem hw]
  exact congrArg Multiplicative.toAdd (map_mul N.β ⟨v, hv⟩ ⟨w, hw⟩)

theorem coord_inv {v : 𝔾} (hv : v ∈ V) : N.coord v⁻¹ = -N.coord v := by
  rw [N.coord_of_mem (V.inv_mem hv), N.coord_of_mem hv]
  exact congrArg Multiplicative.toAdd (map_inv N.β ⟨v, hv⟩)

theorem coord_eq_zero_iff {v : 𝔾} (hv : v ∈ V) : N.coord v = 0 ↔ v ∈ K := by
  rw [N.coord_of_mem hv, ← N.ker ⟨v, hv⟩]
  constructor
  · intro h
    rw [← ofAdd_toAdd (N.β _), h, ofAdd_zero]
  · intro h
    rw [h, toAdd_one]

theorem conj_mem (l : ↥L) {v : 𝔾} (hv : v ∈ V) : (l : 𝔾) * v * (l : 𝔾)⁻¹ ∈ V :=
  (Subgroup.mem_normalizer_iff.mp (N.norm l.2) v).mp hv

theorem coord_conj (l : ↥L) {v : 𝔾} (hv : v ∈ V) :
    N.coord ((l : 𝔾) * v * (l : 𝔾)⁻¹) = natAct dual (toSL3 α l) *ᵥ N.coord v := by
  rw [N.coord_of_mem (N.conj_mem l hv), N.coord_of_mem hv]
  exact N.equiv l ⟨v, hv⟩ ⟨_, N.conj_mem l hv⟩ rfl

theorem exists_coord_eq (y : Fin 3 → F) : ∃ v ∈ V, N.coord v = y := by
  obtain ⟨v, hv⟩ := N.surj (Multiplicative.ofAdd y)
  refine ⟨v, v.2, ?_⟩
  rw [N.coord_of_mem v.2, Subtype.coe_eta, hv, toAdd_ofAdd]

theorem inv_mul_mem_of_coord_eq {v w : 𝔾} (hv : v ∈ V) (hw : w ∈ V)
    (h : N.coord v = N.coord w) : v⁻¹ * w ∈ K := by
  rw [← N.coord_eq_zero_iff (V.mul_mem (V.inv_mem hv) hw), N.coord_mul (V.inv_mem hv) hw,
    N.coord_inv hv, h, neg_add_cancel]

noncomputable def img (H : Subgroup 𝔾) : AddSubgroup (Fin 3 → F) where
  carrier := {y | ∃ v ∈ H, v ∈ V ∧ N.coord v = y}
  zero_mem' := ⟨1, H.one_mem, V.one_mem, N.coord_one⟩
  add_mem' := by
    rintro _ _ ⟨v, hvH, hv, rfl⟩ ⟨w, hwH, hw, rfl⟩
    exact ⟨v * w, H.mul_mem hvH hwH, V.mul_mem hv hw, N.coord_mul hv hw⟩
  neg_mem' := by
    rintro _ ⟨v, hvH, hv, rfl⟩
    exact ⟨v⁻¹, H.inv_mem hvH, V.inv_mem hv, N.coord_inv hv⟩

theorem mem_img {H : Subgroup 𝔾} {y : Fin 3 → F} :
    y ∈ N.img H ↔ ∃ v ∈ H, v ∈ V ∧ N.coord v = y :=
  Iff.rfl

noncomputable def pre (S : AddSubgroup (Fin 3 → F)) : Subgroup 𝔾 where
  carrier := {v | v ∈ V ∧ N.coord v ∈ S}
  one_mem' := ⟨V.one_mem, by rw [N.coord_one]; exact S.zero_mem⟩
  mul_mem' := fun {v w} hv hw =>
    ⟨V.mul_mem hv.1 hw.1, by rw [N.coord_mul hv.1 hw.1]; exact S.add_mem hv.2 hw.2⟩
  inv_mem' := fun {v} hv => ⟨V.inv_mem hv.1, by rw [N.coord_inv hv.1]; exact S.neg_mem hv.2⟩

theorem mem_pre {S : AddSubgroup (Fin 3 → F)} {v : 𝔾} : v ∈ N.pre S ↔ v ∈ V ∧ N.coord v ∈ S :=
  Iff.rfl

theorem exists_inv_mul_mem_of_invariant (hα : Function.Surjective α) {H : Subgroup 𝔾}
    (hHL : ∀ l : ↥L, ∀ h ∈ H, (l : 𝔾) * h * (l : 𝔾)⁻¹ ∈ H) {h : 𝔾} (hhH : h ∈ H) (hhV : h ∈ V)
    (hhK : h ∉ K) {v : 𝔾} (hv : v ∈ V) : ∃ w ∈ H, w ∈ V ∧ w⁻¹ * v ∈ K := by
  have hS : ∀ g : SL3 F, ∀ y ∈ N.img H, natAct dual g *ᵥ y ∈ N.img H := by
    rintro g _ ⟨u, huH, hu, rfl⟩
    obtain ⟨l, rfl⟩ := toSL3_surjective hα g
    exact ⟨_, hHL l u huH, N.conj_mem l hu, N.coord_conj l hu⟩
  have hy0 : N.coord h ≠ 0 := by
    rw [Ne, N.coord_eq_zero_iff hhV]
    exact hhK
  obtain ⟨w, hwH, hw, hwv⟩ :=
    mem_of_natAct_invariant dual _ hS ⟨h, hhH, hhV, rfl⟩ hy0 (N.coord v)
  exact ⟨w, hwH, hw, N.inv_mul_mem_of_coord_eq hw hv hwv⟩

end NatSec

namespace NatSec

variable (N : NatSec L V ⊥ α dual)
include N

theorem eq_of_coord_eq {v w : 𝔾} (hv : v ∈ V) (hw : w ∈ V) (h : N.coord v = N.coord w) :
    v = w := by
  have := N.inv_mul_mem_of_coord_eq hv hw h
  rw [Subgroup.mem_bot, inv_mul_eq_one] at this
  exact this

theorem eq_one_of_coord_eq_zero {v : 𝔾} (hv : v ∈ V) (h : N.coord v = 0) : v = 1 := by
  rw [N.coord_eq_zero_iff hv, Subgroup.mem_bot] at h
  exact h

theorem le_of_invariant (hα : Function.Surjective α) {H : Subgroup 𝔾}
    (hHL : ∀ l : ↥L, ∀ h ∈ H, (l : 𝔾) * h * (l : 𝔾)⁻¹ ∈ H) {h : 𝔾} (hhH : h ∈ H) (hhV : h ∈ V)
    (h1 : h ≠ 1) : V ≤ H := by
  intro v hv
  obtain ⟨w, hwH, -, hwv⟩ := N.exists_inv_mul_mem_of_invariant hα hHL hhH hhV
    (by rw [Subgroup.mem_bot]; exact h1) hv
  rw [Subgroup.mem_bot, inv_mul_eq_one] at hwv
  exact hwv ▸ hwH

theorem card_eq [Finite F] : Nat.card ↥V = Nat.card F ^ 3 := by
  have hinj : Function.Injective N.β := by
    intro v w hvw
    apply Subtype.ext
    apply N.eq_of_coord_eq v.2 w.2
    rw [N.coord_of_mem v.2, N.coord_of_mem w.2]
    exact congrArg Multiplicative.toAdd hvw
  rw [Nat.card_congr (Equiv.ofBijective N.β ⟨hinj, N.surj⟩), card_natMod]

end NatSec

namespace ML3

theorem commute_of_commutator_eq_bot {A B : Subgroup 𝔾} (h : ⁅A, B⁆ = ⊥) {a b : 𝔾} (ha : a ∈ A)
    (hb : b ∈ B) : a * b = b * a := by
  have := Subgroup.commutator_mem_commutator ha hb
  rwa [h, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at this

theorem conj_commutatorElement (g a b : 𝔾) : g * ⁅a, b⁆ * g⁻¹ = ⁅g * a * g⁻¹, g * b * g⁻¹⁆ := by
  simp only [commutatorElement_def]
  group

theorem conj_mem_closure {S : Set 𝔾} {g : 𝔾} (hS : ∀ s ∈ S, g * s * g⁻¹ ∈ Subgroup.closure S)
    {h : 𝔾} (hh : h ∈ Subgroup.closure S) : g * h * g⁻¹ ∈ Subgroup.closure S := by
  induction hh using Subgroup.closure_induction with
  | mem x hx => exact hS x hx
  | one => simp
  | mul x y _ _ hx hy =>
    have he : g * (x * y) * g⁻¹ = (g * x * g⁻¹) * (g * y * g⁻¹) := by group
    rw [he]
    exact Subgroup.mul_mem _ hx hy
  | inv x _ hx =>
    have he : g * x⁻¹ * g⁻¹ = (g * x * g⁻¹)⁻¹ := by group
    rw [he]
    exact Subgroup.inv_mem _ hx

theorem conj_mem_commutator {A B : Subgroup 𝔾} {g : 𝔾} (hA : ∀ a ∈ A, g * a * g⁻¹ ∈ A)
    (hB : ∀ b ∈ B, g * b * g⁻¹ ∈ B) {h : 𝔾} (hh : h ∈ ⁅A, B⁆) : g * h * g⁻¹ ∈ ⁅A, B⁆ := by
  rw [Subgroup.commutator_def] at hh ⊢
  refine conj_mem_closure (fun s hs => ?_) hh
  obtain ⟨a, ha, b, hb, rfl⟩ := hs
  rw [conj_commutatorElement]
  exact Subgroup.subset_closure ⟨_, hA a ha, _, hB b hb, rfl⟩

section Pairing

variable {Z U W : Subgroup 𝔾}

theorem comm_mul_left (hZU : ⁅Z, U⁆ = ⊥) (hUW : ⁅U, W⁆ ≤ Z) {u u' w : 𝔾} (hu : u ∈ U)
    (hu' : u' ∈ U) (hw : w ∈ W) : ⁅u * u', w⁆ = ⁅u', w⁆ * ⁅u, w⁆ := by
  have ha : ⁅u', w⁆ * u = u * ⁅u', w⁆ :=
    commute_of_commutator_eq_bot hZU (hUW (Subgroup.commutator_mem_commutator hu' hw)) hu
  calc ⁅u * u', w⁆ = u * ⁅u', w⁆ * w * u⁻¹ * w⁻¹ := by
        simp only [commutatorElement_def]
        group
    _ = ⁅u', w⁆ * u * w * u⁻¹ * w⁻¹ := by rw [ha]
    _ = ⁅u', w⁆ * ⁅u, w⁆ := by
        simp only [commutatorElement_def]
        group

theorem comm_mul_right (hZW : ⁅Z, W⁆ = ⊥) (hUW : ⁅U, W⁆ ≤ Z) {u w w' : 𝔾} (hu : u ∈ U)
    (hw : w ∈ W) (hw' : w' ∈ W) : ⁅u, w * w'⁆ = ⁅u, w⁆ * ⁅u, w'⁆ := by
  have hb : ⁅u, w'⁆ * w = w * ⁅u, w'⁆ :=
    commute_of_commutator_eq_bot hZW (hUW (Subgroup.commutator_mem_commutator hu hw')) hw
  calc ⁅u, w * w'⁆ = u * w * u⁻¹ * w⁻¹ * (w * ⁅u, w'⁆) * w⁻¹ := by
        simp only [commutatorElement_def]
        group
    _ = u * w * u⁻¹ * w⁻¹ * (⁅u, w'⁆ * w) * w⁻¹ := by rw [hb]
    _ = ⁅u, w⁆ * ⁅u, w'⁆ := by
        simp only [commutatorElement_def]
        group

theorem comm_inv_left (hZU : ⁅Z, U⁆ = ⊥) (hUW : ⁅U, W⁆ ≤ Z) {u w : 𝔾} (hu : u ∈ U)
    (hw : w ∈ W) : ⁅u⁻¹, w⁆ = ⁅u, w⁆⁻¹ := by
  have h := comm_mul_left hZU hUW (U.inv_mem hu) hu hw
  rw [inv_mul_cancel, commutatorElement_one_left] at h
  exact (eq_inv_of_mul_eq_one_right h.symm)

theorem comm_mem_of_closure (hZU : ⁅Z, U⁆ = ⊥) (hUW : ⁅U, W⁆ ≤ Z) {T : Set 𝔾}
    (hT : U = Subgroup.closure T) {w : 𝔾} (hw : w ∈ W) {H : Subgroup 𝔾}
    (hTH : ∀ t ∈ T, ⁅t, w⁆ ∈ H) {u : 𝔾} (hu : u ∈ U) : ⁅u, w⁆ ∈ H := by
  let P : Subgroup 𝔾 :=
    { carrier := {u | u ∈ U ∧ ⁅u, w⁆ ∈ H}
      one_mem' := ⟨U.one_mem, by rw [commutatorElement_one_left]; exact H.one_mem⟩
      mul_mem' := fun {a b} ha hb => ⟨U.mul_mem ha.1 hb.1, by
        rw [comm_mul_left hZU hUW ha.1 hb.1 hw]
        exact H.mul_mem hb.2 ha.2⟩
      inv_mem' := fun {a} ha => ⟨U.inv_mem ha.1, by
        rw [comm_inv_left hZU hUW ha.1 hw]
        exact H.inv_mem ha.2⟩ }
  have hle : U ≤ P := by
    rw [hT, Subgroup.closure_le]
    intro t ht
    exact ⟨hT ▸ Subgroup.subset_closure ht, hTH t ht⟩
  exact (hle hu).2

end Pairing

end ML3

end Sec

end CFSG.Quasithin.MS93
