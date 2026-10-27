module

public import CFSG.Quasithin.SteinbergCBDeletedStabilizers
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.SL2ModulesAlt
public import CFSG.LieType.SteinbergBRMulEquivCores
public import CFSG.Quasithin.H13.NQTermInternalModule
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.Quasithin.H13.NQSetup

open Subgroup CFSG.Open Equiv Equiv.Perm
open CFSG.QuasithinUnique.Setup.SL2Modules (evenWeight permAct)

@[expose] def altStab {Ω : Type*} [Fintype Ω] [DecidableEq Ω] (v : Ω → ZMod 2) :
    Subgroup (alternatingGroup Ω) where
  carrier := {g | permAct (g : Perm Ω) v = v}
  one_mem' := rfl
  mul_mem' {a b} ha hb := by
    funext i
    have ha' : permAct (a : Perm Ω) v = v := ha
    have hb' : permAct (b : Perm Ω) v = v := hb
    calc v (((a * b : alternatingGroup Ω) : Perm Ω).symm i)
        = v ((b : Perm Ω).symm ((a : Perm Ω).symm i)) := rfl
      _ = v ((a : Perm Ω).symm i) := congrFun hb' _
      _ = v i := congrFun ha' i
  inv_mem' {a} ha := by
    funext i
    have ha' : permAct (a : Perm Ω) v = v := ha
    calc v (((a⁻¹ : alternatingGroup Ω) : Perm Ω).symm i) = v ((a : Perm Ω) i) := rfl
      _ = v ((a : Perm Ω).symm ((a : Perm Ω) i)) := (congrFun ha' _).symm
      _ = v i := by rw [Equiv.symm_apply_apply]

theorem mem_altStab_iff {Ω : Type*} [Fintype Ω] [DecidableEq Ω] {v : Ω → ZMod 2}
    {g : alternatingGroup Ω} : g ∈ altStab v ↔ permAct (g : Perm Ω) v = v := Iff.rfl

theorem card_filter_fix_twoVecFive :
    (Finset.univ.filter fun g : alternatingGroup (Fin 5) =>
      ∀ i, SteinbergCB.twoVecFive ((g : Perm (Fin 5))⁻¹ i) = SteinbergCB.twoVecFive i).card =
      6 := by
  decide +kernel

theorem eq_one_of_ne_zero_zmod_two : ∀ a : ZMod 2, a ≠ 0 → a = 1 := by
  decide

theorem card_altStab_weight_two {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (hΩ : Fintype.card Ω = 5) (v : Ω → ZMod 2)
    (hv : (Finset.univ.filter fun ω => v ω ≠ 0).card = 2) : Nat.card (altStab v) = 6 := by
  classical
  have hweight : ∀ e : Fin 5 ≃ Ω, (Finset.univ.filter fun i => v (e i) ≠ 0).card = 2 := by
    intro e
    refine Eq.trans ?_ hv
    refine Finset.card_bij (fun i _ => e i) (fun i hi => ?_) (fun _ _ _ _ h => e.injective h)
      (fun ω hω => ⟨e.symm ω, ?_, by simp⟩)
    · simpa using hi
    · simpa using hω
  have hsum : ∑ ω, v ω = 0 := by
    rw [← Finset.sum_filter_ne_zero]
    have h1 : ∑ ω ∈ Finset.univ.filter (fun ω => v ω ≠ 0), v ω =
        ∑ ω ∈ Finset.univ.filter (fun ω => v ω ≠ 0), (1 : ZMod 2) :=
      Finset.sum_congr rfl fun ω hω => eq_one_of_ne_zero_zmod_two _ (Finset.mem_filter.mp hω).2
    rw [h1, Finset.sum_const, hv]
    decide
  set e₁ : Ω ≃ Fin 5 := Fintype.equivFinOfCardEq hΩ
  obtain ⟨σ, hσ⟩ := SteinbergCB.exists_perm_evenWeight_five (fun i => v (e₁.symm i))
    (by rw [Equiv.sum_comp e₁.symm v]; exact hsum)
  set e : Fin 5 ≃ Ω := σ.trans e₁.symm with he
  have hev : ∀ i, v (e i) = v (e₁.symm (σ i)) := fun i => rfl
  rcases hσ with h0 | h4 | h2
  · exfalso
    have := hweight e
    simp [hev, h0] at this
  · exfalso
    have := hweight e
    simp only [hev, h4] at this
    revert this
    decide
  · have hve : ∀ i, v (e i) = SteinbergCB.twoVecFive i := fun i => (hev i).trans (h2 i)
    let A : alternatingGroup Ω ≃ alternatingGroup (Fin 5) :=
      (e.symm.permCongr).subtypeEquiv fun g => by
        rw [mem_alternatingGroup, mem_alternatingGroup, sign_permCongr]
    have hA : ∀ (g : alternatingGroup Ω) (i : Fin 5),
        ((A g : alternatingGroup (Fin 5)) : Perm (Fin 5))⁻¹ i =
          e.symm ((g : Perm Ω)⁻¹ (e i)) := by
      intro g i
      rw [Perm.inv_eq_iff_eq]
      change i = e.symm ((g : Perm Ω) (e (e.symm ((g : Perm Ω)⁻¹ (e i)))))
      simp
    let F : altStab v ≃
        {g : alternatingGroup (Fin 5) // ∀ i, SteinbergCB.twoVecFive ((g : Perm (Fin 5))⁻¹ i) =
          SteinbergCB.twoVecFive i} :=
      A.subtypeEquiv fun g => by
        rw [mem_altStab_iff]
        simp only [hA, ← hve, Equiv.apply_symm_apply]
        constructor
        · intro hg i
          exact congrFun hg (e i)
        · intro hg
          funext ω
          have := hg (e.symm ω)
          rwa [Equiv.apply_symm_apply] at this
    rw [Nat.card_congr F, Nat.card_eq_fintype_card, Fintype.card_subtype]
    convert card_filter_fix_twoVecFive

theorem two_dvd_card_altStab {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (hΩ : Fintype.card Ω = 5) (v : Ω → ZMod 2) (hv : ∑ ω, v ω = 0) :
    2 ∣ Nat.card (altStab v) := by
  obtain ⟨hK, -⟩ := SteinbergCB.nq_alternating_five_deleted_module_stabilizers hΩ v hv
  have hle : ∀ K : Subgroup (Perm Ω), K ≤ alternatingGroup Ω →
      (∀ g ∈ K, LinearMap.funLeft (ZMod 2) (ZMod 2) ⇑g⁻¹ v = v) →
      Nat.card K ∣ Nat.card (altStab v) := by
    intro K hKA hKv
    have h1 : K.subgroupOf (alternatingGroup Ω) ≤ altStab v := fun g hg => by
      rw [mem_altStab_iff]
      exact hKv _ (mem_subgroupOf.mp hg)
    rw [← Nat.card_congr (subgroupOfEquivOfLe hKA).toEquiv]
    exact card_dvd_of_le h1
  rcases hK with ⟨K, hKA, hKv, -, hK4⟩ | ⟨K, hKA, hKv, ⟨eK⟩⟩
  · exact (show 2 ∣ Nat.card K by rw [hK4]; norm_num).trans (hle K hKA hKv)
  · refine (show 2 ∣ Nat.card K from ?_).trans (hle K hKA hKv)
    rw [Nat.card_congr eK.toEquiv, Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin]
    decide

theorem map_centralizer_eq_comap_altStab {G : Type} [Group G] [Finite G] {T L M : Subgroup G}
    (h : QTNQ T L M) {Ω : Type} [Fintype Ω] [DecidableEq Ω]
    (β : (L ⧸ CFSG.solvableRadical L) ≃* alternatingGroup Ω)
    (θ : qtnqU L M → Ω → ZMod 2) (hθi : Function.Injective θ)
    (hθ : ∀ (l : L) (x y : qtnqU L M), (y : G) = (l : G) * x * (l : G)⁻¹ →
      θ y = permAct (β (l : L ⧸ CFSG.solvableRadical L) : Perm Ω) (θ x))
    {u : G} (hu : u ∈ qtnqU L M) :
    ((centralizer ({u} : Set G)).subgroupOf L).map
        (QuotientGroup.mk' (CFSG.solvableRadical L)) =
      (altStab (θ ⟨u, hu⟩)).comap β.toMonoidHom := by
  obtain ⟨-, -, -, -, ⟨-, hUM, hUn, -⟩, -⟩ :=
    NQTerm.nonquasisimple_normalizer_internal_module_properties h
  have hUnorm : M ≤ normalizer (qtnqU L M : Set G) :=
    (normal_subgroupOf_iff_le_normalizer hUM).mp hUn
  ext q
  obtain ⟨l, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.solvableRadical L) q
  rw [mem_comap, MulEquiv.coe_toMonoidHom, mem_altStab_iff]
  constructor
  · rintro ⟨l', hl', hll'⟩
    have hl'u : (l' : G) * u * (l' : G)⁻¹ = u := by
      rw [SetLike.mem_coe, mem_subgroupOf, mem_centralizer_singleton_iff] at hl'
      rw [hl', mul_inv_cancel_right]
    have h1 := hθ l' ⟨u, hu⟩ ⟨u, hu⟩ hl'u.symm
    have hll'' : ((l' : L) : L ⧸ CFSG.solvableRadical L) = ((l : L) : L ⧸ CFSG.solvableRadical L) :=
      hll'
    rw [hll''] at h1
    exact h1.symm
  · intro hfix
    have hconj : (l : G) * u * (l : G)⁻¹ ∈ qtnqU L M :=
      (mem_normalizer_iff.mp (hUnorm (h.l_le l.2)) u).mp hu
    have h1 := hθ l ⟨u, hu⟩ ⟨_, hconj⟩ rfl
    have h4 : (l : G) * u * (l : G)⁻¹ = u :=
      congrArg Subtype.val (hθi (h1.trans hfix))
    refine ⟨l, ?_, rfl⟩
    rw [SetLike.mem_coe, mem_subgroupOf, mem_centralizer_singleton_iff]
    calc (l : G) * u = (l : G) * u * (l : G)⁻¹ * l := by group
      _ = u * l := by rw [h4]

theorem card_map_centralizer_eq_card_altStab {G : Type} [Group G] [Finite G]
    {T L M : Subgroup G} (h : QTNQ T L M) {Ω : Type} [Fintype Ω] [DecidableEq Ω]
    (β : (L ⧸ CFSG.solvableRadical L) ≃* alternatingGroup Ω)
    (θ : qtnqU L M → Ω → ZMod 2) (hθi : Function.Injective θ)
    (hθ : ∀ (l : L) (x y : qtnqU L M), (y : G) = (l : G) * x * (l : G)⁻¹ →
      θ y = permAct (β (l : L ⧸ CFSG.solvableRadical L) : Perm Ω) (θ x))
    {u : G} (hu : u ∈ qtnqU L M) :
    Nat.card (((centralizer ({u} : Set G)).subgroupOf L).map
        (QuotientGroup.mk' (CFSG.solvableRadical L))) = Nat.card (altStab (θ ⟨u, hu⟩)) := by
  rw [map_centralizer_eq_comap_altStab h β θ hθi hθ hu]
  exact Nat.card_congr (β.toEquiv.subtypeEquiv fun _ => Iff.rfl)

end CFSG.Quasithin.H13.NQSetup
