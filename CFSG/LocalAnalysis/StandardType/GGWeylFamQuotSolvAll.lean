module

public import CFSG.LocalAnalysis.StandardType.GGExcToralSylowLayer
public import CFSG.Monster.B.TwoA.Unitary.Orbit1408Points
public import CFSG.Monster.B.TwoA.Unitary.Semilinear

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Universal
  CFSG.LieType.RootSystem CFSG.Assembly.LowTwoRank CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.RankThree.PartOne.KE8F

namespace LayerExc

variable {τ : Tag} {K : Type} [Field K]

section Toral

open CFSG.LieType.Steinberg.Adjoint RootSpace CFSG.RankThree.PartOne.KE in
open CFSG.RankThree.E6 (charVal charVal_neg) in
theorem le_famReflectionGroup_of_coprime [Finite K] {p : ℕ} (hp : p.Prime)
    (F : Set (Fin τ.rank → Kˣ)) (hF : ∀ a ∈ F, ∃ n : ℕ, a ^ p ^ n = 1)
    (U : Subgroup (WeylGroup τ)) (hUF : U ≤ famStabilizerSubgroup F)
    (hW : ¬ p ∣ Nat.card U) :
    U ≤ famReflectionGroup F := by
  classical
  have : Fintype F := Fintype.ofFinite F
  obtain ⟨N, hN⟩ : ∃ N : ℕ, ∀ a ∈ F, a ^ p ^ N = 1 := by
    choose! n hn using hF
    refine ⟨∑ b : F, n b.1, fun a ha => ?_⟩
    obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le (Finset.single_le_sum
      (f := fun b : F => n b.1) (fun _ _ => Nat.zero_le _) (Finset.mem_univ ⟨a, ha⟩))
    rw [hd, pow_add, pow_mul, hn a ha, one_pow]
  obtain ⟨ζ', hζ'⟩ := IsCyclic.exists_generator (α := rootsOfUnity (p ^ N) K)
  have hmM : orderOf (ζ' : Kˣ) ∣ p ^ N :=
    orderOf_dvd_of_pow_eq_one ((mem_rootsOfUnity _ _).1 ζ'.2)
  have : Fintype U := Fintype.ofFinite U
  have hcop : IsCoprime (orderOf (ζ' : Kˣ) : ℤ) (Fintype.card U : ℤ) := by
    rw [Nat.isCoprime_iff_coprime]
    refine Nat.Coprime.coprime_dvd_left hmM (Nat.Coprime.pow_left N ?_)
    rw [Nat.Prime.coprime_iff_not_dvd hp, ← Nat.card_eq_fintype_card]
    exact hW
  have hexp : ∀ a ∈ F, ∀ i, ∃ e : ℕ, a i = (ζ' : Kˣ) ^ e := by
    intro a ha i
    have hmem : a i ∈ rootsOfUnity (p ^ N) K := by
      rw [mem_rootsOfUnity]
      have h := congrFun (hN a ha) i
      simpa only [Pi.pow_apply, Pi.one_apply] using h
    obtain ⟨k, hk⟩ := mem_powers_iff_mem_zpowers.2 (hζ' ⟨a i, hmem⟩)
    refine ⟨k, ?_⟩
    have h := congrArg Subtype.val hk
    rw [Subgroup.coe_pow] at h
    exact h.symm
  choose! e he using hexp
  have hchar : ∀ a ∈ F, ∀ l,
      rootChar a l = (ζ' : Kˣ) ^ charVal (fun i => (e a i : ℤ)) l := by
    intro a ha l
    rw [rootChar_eq_zpow (e a) a (he a ha), charVal_int_eq]
    exact congrArg _ (Finset.sum_congr rfl fun i _ => mul_comm _ _)
  have hrinv : ∀ a : F, ∀ w ∈ U, ∀ x,
      charVal (avgColumn U (fun i => (e a.1 i : ℤ))) (w • x) =
        charVal (avgColumn U (fun i => (e a.1 i : ℤ))) x :=
    fun a w hw x => charVal_avgColumn_smul _ hw x
  have hrcong : ∀ a : F, ∀ x, (orderOf (ζ' : Kˣ) : ℤ) ∣
      charVal (avgColumn U (fun i => (e a.1 i : ℤ))) x -
        (Fintype.card U : ℤ) * charVal (fun i => (e a.1 i : ℤ)) x := by
    intro a x
    have e1 : charVal (avgColumn U (fun i => (e a.1 i : ℤ))) x -
        (Fintype.card U : ℤ) * charVal (fun i => (e a.1 i : ℤ)) x =
          ∑ u : U, (charVal (fun i => (e a.1 i : ℤ)) ((u : WeylGroup τ) • x) -
            charVal (fun i => (e a.1 i : ℤ)) x) := by
      rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
        charVal_avgColumn]
    rw [e1]
    refine Finset.dvd_sum fun u _ => ?_
    have h := hUF u.2 a.1 a.2 x
    rw [hchar a.1 a.2, hchar a.1 a.2, zpow_eq_zpow_iff_modEq] at h
    exact h.symm.dvd
  have hker : ∀ α, IsRoot τ α →
      ((∀ a : F, charVal (avgColumn U (fun i => (e a.1 i : ℤ))) α = 0) → α ∈ famKernel F) := by
    intro α hα h
    refine ⟨hα, fun a ha => ?_⟩
    have h1 := hrcong ⟨a, ha⟩ α
    rw [h ⟨a, ha⟩, zero_sub, dvd_neg] at h1
    rw [hchar a ha]
    exact orderOf_dvd_iff_zpow_eq_one.1 (hcop.dvd_of_dvd_mul_left h1)
  have hrootfin : Finite {α : Fin τ.rank → ℤ // IsRoot τ α} := (finite_setOf_isRoot τ).to_subtype
  obtain ⟨M, hM⟩ := Finite.exists_le
    (fun x : {α : Fin τ.rank → ℤ // IsRoot τ α} × F =>
      (charVal (avgColumn U (fun i => (e x.2.1 i : ℤ))) x.1.1).natAbs)
  set Nb : ℤ := 2 * (M : ℤ) + 1 with hNb
  have hNpos : 0 < Nb := by omega
  set ι := Fintype.equivFin F with hι
  set R : Fin τ.rank → ℤ := ∑ a : F, Nb ^ ((ι a : Fin (Fintype.card F)) : ℕ) •
    avgColumn U (fun i => (e a.1 i : ℤ)) with hR
  have hRval : ∀ x, charVal R x = ∑ a : F, Nb ^ ((ι a : Fin (Fintype.card F)) : ℕ) *
      charVal (avgColumn U (fun i => (e a.1 i : ℤ))) x := fun x => charVal_sum_smul _ _ x
  have hRinv : ∀ w ∈ U, ∀ x, charVal R (w • x) = charVal R x := fun w hw x => by
    rw [hRval, hRval]
    exact Finset.sum_congr rfl fun a _ => by rw [hrinv a w hw]
  have hRker : ∀ α, IsRoot τ α → (charVal R α = 0 → α ∈ famKernel F) := by
    intro α hα h
    refine hker α hα ?_
    have hsum : ∑ k : Fin (Fintype.card F), Nb ^ (k : ℕ) *
        charVal (avgColumn U (fun i => (e (ι.symm k).1 i : ℤ))) α = 0 := by
      rw [← h, hRval]
      exact Fintype.sum_equiv ι.symm _ _ fun k => by simp
    have hd := digits_eq_zero
      (fun k => charVal (avgColumn U (fun i => (e (ι.symm k).1 i : ℤ))) α) hNpos (fun k => by
        have := hM (⟨α, hα⟩, ι.symm k)
        simp only at this ⊢
        rw [Int.abs_eq_natAbs]
        omega) hsum
    intro a
    have := hd (ι a)
    simpa using this
  intro w hw
  have hfix : w ∈ weylStabilizer τ (dualVector R) :=
    weylAct_dualVector_eq fun v => hRinv w⁻¹ (U.inv_mem hw) v
  rw [(exceptional_Lang_Weyl_chamber_point_stabilizers τ).2.2.2.2.2 (dualVector R)] at hfix
  refine Subgroup.closure_mono ?_ hfix
  rintro _ ⟨α, hα, h0, rfl⟩
  rw [inner_ofLattice_dualVector, Int.cast_eq_zero] at h0
  exact ⟨α, hRker α hα h0, rfl⟩

theorem rootReflection_mem_famStabilizerSubgroup {F : Set (Fin τ.rank → Kˣ)}
    {α : Fin τ.rank → ℤ} (hα : α ∈ famKernel F) :
    rootReflection α ∈ famStabilizerSubgroup F := by
  show ∀ a ∈ F, ∀ v, rootChar a (rootReflection α • v) = rootChar a v
  intro a ha v
  rw [rootReflection_smul hα.1, sub_eq_add_neg, ← neg_smul, rootChar_add, rootChar_zsmul,
    hα.2 a ha, one_zpow, mul_one]

theorem famReflectionGroup_le_famStabilizerSubgroup (F : Set (Fin τ.rank → Kˣ)) :
    famReflectionGroup F ≤ famStabilizerSubgroup F := by
  refine (Subgroup.closure_le _).2 ?_
  rintro _ ⟨α, hα, rfl⟩
  exact rootReflection_mem_famStabilizerSubgroup hα

theorem conj_mem_famReflectionGroup {F : Set (Fin τ.rank → Kˣ)} {w s : WeylGroup τ}
    (hw : w ∈ famStabilizerSubgroup F) (hs : s ∈ famReflectionGroup F) :
    w * s * w⁻¹ ∈ famReflectionGroup F := by
  have hw' : w ∈ famStabilizer F := hw
  induction hs using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨α, hα, rfl⟩ := hx
    have hα' : w • α ∈ famKernel F :=
      (image_famKernel hw').subset (Set.mem_image_of_mem _ hα)
    have hrefl : rootReflection (w • α) = w * rootReflection α * w⁻¹ :=
      rootReflection_smul_root w hα.1
    rw [← hrefl]
    exact Subgroup.subset_closure ⟨w • α, hα', rfl⟩
  | one => simpa using Subgroup.one_mem _
  | mul x y _ _ hx hy =>
    have : w * (x * y) * w⁻¹ = (w * x * w⁻¹) * (w * y * w⁻¹) := by group
    rw [this]
    exact Subgroup.mul_mem _ hx hy
  | inv x _ hx =>
    have : w * x⁻¹ * w⁻¹ = (w * x * w⁻¹)⁻¹ := by group
    rw [this]
    exact Subgroup.inv_mem _ hx

theorem mem_famReflectionGroup_of_coprime_orderOf [Finite K] {p : ℕ} (hp : p.Prime)
    (F : Set (Fin τ.rank → Kˣ)) (hF : ∀ a ∈ F, ∃ n : ℕ, a ^ p ^ n = 1)
    {w : WeylGroup τ} (hw : w ∈ famStabilizerSubgroup F) (hcop : Nat.Coprime (orderOf w) p) :
    w ∈ famReflectionGroup F := by
  have hle : Subgroup.zpowers w ≤ famStabilizerSubgroup F := Subgroup.zpowers_le.2 hw
  have hnd : ¬ p ∣ Nat.card (Subgroup.zpowers w) := by
    rw [Nat.card_zpowers]
    exact (Nat.Prime.coprime_iff_not_dvd hp).1 hcop.symm
  exact le_famReflectionGroup_of_coprime hp F hF _ hle hnd (Subgroup.mem_zpowers w)

theorem exists_ggDer_famStabilizerSubgroup_le_reflection [Finite K] {p : ℕ} (hp : p.Prime)
    (F : Set (Fin τ.rank → Kˣ)) (hF : ∀ a ∈ F, ∃ n : ℕ, a ^ p ^ n = 1) :
    ∃ k, LayerFacts.ggDer (famStabilizerSubgroup F) k ≤ famReflectionGroup F := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  set H := famStabilizerSubgroup F with hH
  set N : Subgroup H := (famReflectionGroup F).subgroupOf H with hN
  haveI hNn : N.Normal := ⟨fun n hn h => by
    show ((h * n * h⁻¹ : H) : WeylGroup τ) ∈ famReflectionGroup F
    exact conj_mem_famReflectionGroup h.2 hn⟩
  have hP : IsPGroup p (H ⧸ N) := by
    intro x
    obtain ⟨h, rfl⟩ := QuotientGroup.mk_surjective x
    obtain ⟨e, m, hm, hem⟩ := Nat.exists_eq_pow_mul_and_not_dvd (orderOf_pos h).ne' p hp.ne_one
    refine ⟨e, ?_⟩
    have hpe : p ^ e ≠ 0 := pow_ne_zero _ hp.ne_zero
    have hord : orderOf (h ^ p ^ e) = m := by
      rw [orderOf_pow_of_dvd hpe (by rw [hem]; exact dvd_mul_right _ _), hem,
        Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero hpe)]
    have hmem : (((h ^ p ^ e : H)) : WeylGroup τ) ∈ famReflectionGroup F := by
      refine mem_famReflectionGroup_of_coprime_orderOf hp F hF (h ^ p ^ e).2 ?_
      rw [Subgroup.orderOf_coe, hord]
      exact ((Nat.Prime.coprime_iff_not_dvd hp).2 hm).symm
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
    exact hmem
  haveI : Group.IsNilpotent (H ⧸ N) := hP.isNilpotent
  haveI : Group.IsSolvable (H ⧸ N) := inferInstance
  obtain ⟨k, hk⟩ := (inferInstance : Group.IsSolvable (H ⧸ N)).solvable
  refine ⟨k, ?_⟩
  rw [LayerCores.ggDer_eq_map_derivedSeries]
  rintro _ ⟨x, hx, rfl⟩
  have hx' : QuotientGroup.mk' N x ∈ derivedSeries (H ⧸ N) k := by
    rw [← map_derivedSeries_eq (QuotientGroup.mk'_surjective N) k]
    exact Subgroup.mem_map_of_mem _ hx
  rw [hk, Subgroup.mem_bot] at hx'
  exact (QuotientGroup.eq_one_iff x).1 hx'

end Toral

end LayerExc

section Final

theorem ggWeylFamQuotSolvInput_all (τ : Tag) : GGWeylFamQuotSolvInput τ :=
  fun _ _ _ _ _ hp _ F hF _ =>
    LayerExc.exists_ggDer_famStabilizerSubgroup_le_reflection hp F hF

end Final

section Bundle

@[expose] def GGLayerTagsPilotRestSixSylowCores : Prop :=
  GGExcAdjCoreNonToralSylowRestInput .F4 ∧ GGExcAdjCoreNonToralSylowRestInput .E7 ∧
    GGExcAdjCoreNonToralSylowRestInput .E8 ∧ GGE6InndiagCoreNonToralSylowRestInput ∧
    GGTwE6InndiagCoreRestInput

theorem ggLayerTagsPilotRestSixSylow_of_nonToral
    (h4 : GGExcAdjCoreNonToralSylowRestInput .F4) (h7 : GGExcAdjCoreNonToralSylowRestInput .E7)
    (h8 : GGExcAdjCoreNonToralSylowRestInput .E8) (h6 : GGE6InndiagCoreNonToralSylowRestInput)
    (hT : GGTwE6InndiagCoreRestInput) : GGLayerTagsPilotRestSixSylow :=
  ⟨h4, ⟨ggWeylFamQuotSolvInput_all _, h7⟩, ⟨ggWeylFamQuotSolvInput_all _, h8⟩,
    ⟨ggWeylFamQuotSolvInput_all _, h6⟩, hT⟩

theorem ggLayerTagsPilotRestSixSylow_of_cores (h : GGLayerTagsPilotRestSixSylowCores) :
    GGLayerTagsPilotRestSixSylow :=
  ggLayerTagsPilotRestSixSylow_of_nonToral h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2

theorem ggLayerTagsPilotRestSixSylowCores_of_rest (h : GGLayerTagsPilotRestSixSylow) :
    GGLayerTagsPilotRestSixSylowCores :=
  ⟨h.1, h.2.1.2, h.2.2.1.2, h.2.2.2.1.2, h.2.2.2.2⟩

end Bundle

end CFSG.StandardType
