module

public import CFSG.Timmesfeld.LieEmbed.C3Roots
import CFSG.ClassicalGroups.Symplectic.Model
public import CFSG.LieType.Steinberg.Adjoint.Presentation

public noncomputable section

namespace CFSG.Timmesfeld.LieEmbed

open CFSG.Blueprint.Chevalley CFSG.LieType CFSG.LieType.Steinberg CFSG.LieType.Universal
open CFSG.LieType.Universal.Symplectic CFSG.LieType.RootSystem CFSG.LieType.Chevalley
open CFSG.Assembly.LowTwoRank
open scoped commutatorElement

variable (K : Type) [Field K]

abbrev spF4Par (γ : Fin 3 → ℤ) (c : K) : ↥(adjointGroup .F4 K) :=
  Adjoint.f4Par K (c3ToF4 γ) c

variable {K}

theorem spF4Par_of_not {γ : Fin 3 → ℤ} (hγ : γ ∉ roots (isFiniteType_cartanC 3) ∅) (c : K) :
    spF4Par K γ c = 1 :=
  Adjoint.xPar_of_not_isRoot (fun h => hγ (isRoot_c3ToF4_iff.1 h)) c

section Comm

open Adjoint

variable [CharP K 2]

theorem spF4Par_pair {α β : Fin 3 → ℤ} (hα : α ∈ roots (isFiniteType_cartanC 3) ∅)
    (hβ : β ∈ roots (isFiniteType_cartanC 3) ∅) (hne : α ≠ β) (hαβ : α + β ≠ 0)
    {i j : ℕ} (hp : (i, j) ∈ pairs₀) (c d : K) :
    spF4Par K (i • α + j • β) ((Sp.commC α β (i, j) : K) * c ^ i * d ^ j) =
      xPar (rootOperatorFamily .F4) (i • c3ToF4 α + j • c3ToF4 β)
        ((Adjoint.commC (rootOperatorFamily .F4) f4Data_valid (c3ToF4 α) (c3ToF4 β) (i, j) :
          K) * c ^ i * d ^ j) := by
  have hv : c3ToF4 (i • α + j • β) = i • c3ToF4 α + j • c3ToF4 β := by
    rw [map_add, map_nsmul, map_nsmul]
  by_cases hr : i • α + j • β ∈ roots (isFiniteType_cartanC 3) ∅
  · rw [spF4Par, f4Par, hv, cast_commC_eq hα hβ hne hαβ hp hr]
  · rw [spF4Par_of_not hr, xPar_of_not_isRoot]
    rwa [← hv, isRoot_c3ToF4_iff]

theorem commutator_spF4Par (O : CommOrder (Sp.Φ 3 K)) {α β : Fin 3 → ℤ}
    (hα : α ∈ roots (isFiniteType_cartanC 3) ∅) (hβ : β ∈ roots (isFiniteType_cartanC 3) ∅)
    (hαβ : α + β ≠ 0) (c d : K) :
    ⁅spF4Par K α c, spF4Par K β d⁆ =
      ((O.list α β).map fun p => spF4Par K (p.1 • α + p.2 • β)
        ((Sp.commC α β p : K) * c ^ p.1 * d ^ p.2)).prod := by
  classical
  by_cases hne : α = β
  · subst hne
    have hnil : O.list α α = [] := List.eq_nil_iff_forall_not_mem.2 fun p hp => by
      obtain ⟨h1, h2, h3⟩ := (O.mem_iff α hα α hα hαβ p).1 hp
      rw [← add_nsmul] at h3
      have := eq_one_of_nsmul_mem_roots h3
      omega
    rw [hnil, List.map_nil, List.prod_nil, commutatorElement_eq_one_iff_commute, Commute,
      SemiconjBy, spF4Par, f4Par, ← xPar_add, ← xPar_add, add_comm]
  have hne' : α ≠ -β := fun h => hαβ (by rw [h, neg_add_cancel])
  have hα' := isRoot_c3ToF4 hα
  have hβ' := isRoot_c3ToF4 hβ
  have hne₁ : c3ToF4 α ≠ c3ToF4 β := fun h => hne (c3ToF4_injective h)
  have hne₂ : c3ToF4 α ≠ -c3ToF4 β := fun h => hne' (c3ToF4_injective (by rw [h, map_neg]))
  have hsum : c3ToF4 α + c3ToF4 β ≠ 0 := fun h => hne₂ (eq_neg_of_add_eq_zero_left h)
  have hperm : (O.list α β).Perm (pairs₀.filter fun p =>
      decide (p.1 • α + p.2 • β ∈ roots (isFiniteType_cartanC 3) ∅)) := by
    refine (List.perm_ext_iff_of_nodup (O.nodup α β) ((by decide : pairs₀.Nodup).filter _)).2
      fun p => ?_
    rw [O.mem_iff α hα β hβ hαβ, Sp.mem_expPairs_iff hα hβ hαβ]
    simp only [List.mem_filter, decide_eq_true_eq, pairs₀, Sp.expS, Finset.mem_insert,
      Finset.mem_singleton, List.mem_cons, List.not_mem_nil, or_false]
    tauto
  have hcomm : ∀ p ∈ O.list α β, ∀ q ∈ O.list α β,
      Commute (spF4Par K (p.1 • α + p.2 • β) ((Sp.commC α β p : K) * c ^ p.1 * d ^ p.2))
        (spF4Par K (q.1 • α + q.2 • β) ((Sp.commC α β q : K) * c ^ q.1 * d ^ q.2)) := by
    intro p hp q hq
    obtain ⟨hp1, hp2, -⟩ := (O.mem_iff α hα β hβ hαβ p).1 hp
    obtain ⟨hq1, hq2, -⟩ := (O.mem_iff α hα β hβ hαβ q).1 hq
    simp only [spF4Par, f4Par, map_add, map_nsmul]
    exact commute_xPar_pairs f4Data_valid noG2_F4 hα' hβ' hne₁ hne₂ hp1 hp2 hq1 hq2 _ _
  rw [(hperm.map _).prod_eq' (List.pairwise_map.2 (List.pairwise_of_forall_mem_list hcomm)),
    prod_map_filter_of_eq_one _ _ _ fun p _ hp => spF4Par_of_not (by simpa using hp) _]
  simp only [pairs₀, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
  rw [spF4Par_pair (i := 1) (j := 1) hα hβ hne hαβ (by simp [pairs₀]),
    spF4Par_pair (i := 1) (j := 2) hα hβ hne hαβ (by simp [pairs₀]),
    spF4Par_pair (i := 2) (j := 1) hα hβ hne hαβ (by simp [pairs₀]), spF4Par, spF4Par, f4Par,
    commutator_xPar f4Data_valid noG2_F4 hα' hβ' hne₁ hne₂, commC_11 hα' hβ' hsum,
    commC_12 hα' hβ' hsum, commC_21 hα' hβ' hsum]
  simp only [one_smul, pow_one, mul_assoc]

theorem spF4_rels (O : CommOrder (Sp.Φ 3 K)) :
    ∀ r ∈ relA (Sp.Φ 3 K) K ∪ relB (Sp.Φ 3 K) K O Sp.commC,
      FreeGroup.lift (chevEval (spF4Par K)) r = 1 := by
  have hof : ∀ γ (hγ : γ ∈ (Sp.Φ 3 K).roots) (c : K),
      FreeGroup.lift (chevEval (spF4Par K)) (chevOf (Φ := Sp.Φ 3 K) γ c) = spF4Par K γ c := by
    intro γ hγ c
    rw [chevOf, dite_eq_left hγ, FreeGroup.lift_apply_of]
    rfl
  rintro r (⟨γ, hγ, c, d, rfl⟩ | ⟨α, hα, β, hβ, hαβ, c, d, rfl⟩)
  · rw [map_mul, map_mul, map_inv, hof γ hγ, hof γ hγ, hof γ hγ, mul_inv_eq_one]
    simp only [spF4Par, f4Par, xPar_add]
  · rw [map_mul, map_inv, map_commutatorElement, hof α hα, hof β hβ, map_list_prod,
      List.map_map, commutator_spF4Par O hα hβ hαβ c d, mul_inv_eq_one]
    refine congrArg List.prod (List.map_congr_left fun p hp => ?_)
    rw [Function.comp_apply, hof _ ((O.mem_iff α hα β hβ hαβ p).1 hp).2.2]

end Comm

theorem center_statedSp_eq_bot [CharP K 2] : Subgroup.center (StatedSp 3 K) = ⊥ := by
  rw [eq_bot_iff]
  intro g hg
  rw [Symplectic.center_eq, Subgroup.mem_subgroupOf, StatedScalars, MonoidHom.mem_range] at hg
  obtain ⟨u, hu⟩ := hg
  have hsp := TauCeti.GLSymplectic.mem_iff.1
    ((Subgroup.ext_iff.1 CFSG.ClassicalGroups.Symplectic.statedSp_eq_GLSymplectic _).1 g.2)
  rw [← hu, Matrix.GeneralLinearGroup.coe_scalar] at hsp
  have hJ : (Matrix.scalar (Fin 3 ⊕ Fin 3) (u : K)) * Matrix.J (Fin 3) K *
      (Matrix.scalar (Fin 3 ⊕ Fin 3) (u : K)).transpose = ((u : K) * u) • Matrix.J (Fin 3) K := by
    simp only [Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal, Matrix.smul_mul,
      Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one, Matrix.transpose_smul,
      Matrix.transpose_one, smul_smul]
  rw [hJ] at hsp
  have h1 := congrFun (congrFun hsp (Sum.inl 0)) (Sum.inr 0)
  simp only [Matrix.smul_apply, Matrix.J, Matrix.fromBlocks_apply₁₂, Matrix.neg_apply,
    Matrix.one_apply_eq, smul_eq_mul, mul_neg, mul_one, neg_inj] at h1
  have hu2 : ((u : K) + 1) * ((u : K) + 1) = 0 := by
    linear_combination h1 + ((u : K) + 1) * (CharTwo.two_eq_zero : (2 : K) = 0)
  have hu1 : (u : K) = 1 := by
    rw [mul_self_eq_zero, add_eq_zero_iff_eq_neg, CharTwo.neg_eq] at hu2
    exact hu2
  rw [Subgroup.mem_bot]
  refine Subtype.ext (Units.ext ?_)
  rw [Subgroup.coe_one, Units.val_one, ← hu, Matrix.GeneralLinearGroup.coe_scalar, hu1,
    Matrix.scalar_apply, Matrix.diagonal_one]

variable [Finite K] [CharP K 2]

theorem exists_hom_spToF4 : ∃ ι : ↥(StatedSp 3 K) →* ↥(adjointGroup .F4 K),
    ∀ γ c, ι (Sp.x 3 K γ c) = Adjoint.f4Par K (c3ToF4 γ) c := by
  obtain ⟨O⟩ := nonempty_commOrder_ofCartan (Symplectic.rootDatum 3 K).isFiniteType
    (Dv := (Symplectic.rootDatum 3 K).divisible) rfl
  obtain ⟨hrel, hbij⟩ :=
    (Sp.presentationB (n := 3) (F := K) (by norm_num) O).2 Sp.commC (Sp.commutatorFormula O)
  set e := MulEquiv.ofBijective (PresentedGroup.toGroup hrel) hbij
  refine ⟨(PresentedGroup.toGroup (spF4_rels O)).comp e.symm.toMonoidHom, fun γ c => ?_⟩
  by_cases hγ : γ ∈ roots (isFiniteType_cartanC 3) ∅
  · have he : e.symm (Sp.x 3 K γ c) = PresentedGroup.of (⟨γ, hγ⟩, c) := by
      rw [MulEquiv.symm_apply_eq]
      change Sp.x 3 K γ c = PresentedGroup.toGroup hrel (PresentedGroup.of (⟨γ, hγ⟩, c))
      rw [PresentedGroup.toGroup.of]
      rfl
    rw [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, he, PresentedGroup.toGroup.of]
    rfl
  · rw [Sp.x_of_not (fun ⟨r, hr⟩ => hγ (SpExtras.mem_roots_of_stdVec hr)), map_one]
    exact (spF4Par_of_not hγ c).symm

theorem exists_spToF4 : ∃ ι : ↥(StatedSp 3 K) →* ↥(adjointGroup .F4 K), Function.Injective ι ∧
    ∀ γ c, ι (Sp.x 3 K γ c) = Adjoint.f4Par K (c3ToF4 γ) c := by
  obtain ⟨ι, hι⟩ := exists_hom_spToF4 (K := K)
  refine ⟨ι, ?_, hι⟩
  have hcard : 2 ≤ Nat.card K := Finite.one_lt_card
  have hq : IsQuasisimple (StatedSp 3 K) := Symplectic.isQuasisimple 3 K (by norm_num) (by
    rcases (show Nat.card K = 2 ∨ Nat.card K = 3 ∨ 4 ≤ Nat.card K by omega) with h | h | h
    · exact Or.inr (Or.inr ⟨h, le_rfl⟩)
    · exact Or.inr (Or.inl ⟨h, by norm_num⟩)
    · exact Or.inl (Or.inr h))
  have hsimple : (Pi.single 0 1 : Fin 3 → ℤ) ∈ roots (isFiniteType_cartanC 3) ∅ :=
    mem_roots_of_mem_c3Roots (by decide)
  have hnt : ∃ g, ι g ≠ 1 := ⟨Sp.x 3 K (Pi.single 0 1) 1, by
    rw [hι, Adjoint.f4Par, ← Adjoint.xPar_zero (F := rootOperatorFamily .F4) (c3ToF4 _)]
    exact fun h => one_ne_zero (Adjoint.xPar_injective (isRoot_c3ToF4 hsimple) h)⟩
  rw [injective_iff_map_eq_one]
  intro g hg
  have hc := CurtisTits.ker_le_center_of_isQuasisimple hq hnt hg
  rw [center_statedSp_eq_bot, Subgroup.mem_bot] at hc
  exact hc

omit [Finite K] [CharP K 2] in
theorem image_rootGroup_spToF4 {ι : ↥(StatedSp 3 K) →* ↥(adjointGroup .F4 K)}
    (hι : ∀ γ c, ι (Sp.x 3 K γ c) = Adjoint.f4Par K (c3ToF4 γ) c) {γ : Fin 3 → ℤ}
    (hγ : γ ∈ roots (isFiniteType_cartanC 3) ∅) :
    ((Adjoint.f4Datum K).rootGroup (c3ToF4 γ) : Set ↥(adjointGroup .F4 K)) =
      ι '' ((Symplectic.rootDatum 3 K).rootGroup γ : Set ↥(StatedSp 3 K)) := by
  ext g
  simp only [SetLike.mem_coe, Set.mem_image]
  rw [Adjoint.mem_rootGroup_iff (isRoot_c3ToF4 hγ)]
  constructor
  · rintro ⟨c, rfl⟩
    exact ⟨Sp.x 3 K γ c, ((Sp.isParametrization γ hγ).1 _).2 ⟨c, rfl⟩, hι γ c⟩
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨c, rfl⟩ := ((Sp.isParametrization γ hγ).1 x).1 hx
    exact ⟨c, (hι γ c).symm⟩

end CFSG.Timmesfeld.LieEmbed
