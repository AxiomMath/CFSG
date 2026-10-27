module

public import CFSG.LocalAnalysis.StandardType.GGSixLayerFactsExcPilotToral
public import CFSG.LocalAnalysis.StandardType.GGSixLayerFactsExc
public import CFSG.CharacterTheory.Burnside

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Universal
  CFSG.LieType.RootSystem CFSG.Assembly.LowTwoRank CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.RankThree.PartOne.KE8F

namespace LayerExc

variable {τ : Tag} {K : Type} [Field K]

theorem isSolvable_weylGroup_F4 :
    Group.IsSolvable (WeylGroup .F4) := by
  classical
  have : Fintype (WeylGroup .F4) := Fintype.ofFinite _
  have h : Fintype.card (WeylGroup .F4) = 1152 := by
    rw [← Nat.card_eq_fintype_card]
    exact CFSG.Monster.B.Geometry.card_f4WeylGroup
  exact CFSG.Burnside.finite_group_isSolvable_of_card_eq_prime_pow_mul_prime_pow (a := 7) (b := 2)
    Nat.prime_two Nat.prime_three (by norm_num) (h.trans (by norm_num))

theorem exists_ggDer_famStabilizerSubgroup_le_of_isSolvable (hW : Group.IsSolvable (WeylGroup τ))
    (F : Set (Fin τ.rank → Kˣ)) :
    ∃ k, LayerFacts.ggDer (famStabilizerSubgroup F) k ≤ famReflectionGroup F := by
  obtain ⟨k, hk⟩ := hW.solvable
  refine ⟨k, ?_⟩
  have h := LayerFacts.ggDer_mono (le_top : famStabilizerSubgroup F ≤ ⊤) k
  rw [LayerFacts.ggDer_top, hk] at h
  exact h.trans bot_le

section Toral


theorem pow_eq_one_of_coe_eq_rootDiagUnit {y : ↥(adjointGroup τ K)} {a : Fin τ.rank → Kˣ}
    (hya : (y : ModGL τ K) = rootDiagUnit τ a) {m : ℕ} (hm : y ^ m = 1) : a ^ m = 1 := by
  apply rootDiagUnit_injective
  rw [rootDiagUnit_one]
  change rootDiagUnitHom τ K (a ^ m) = 1
  rw [map_pow]
  change rootDiagUnit τ a ^ m = 1
  rw [← hya]
  have h2 := congrArg (fun z : ↥(adjointGroup τ K) => (z : ModGL τ K)) hm
  simpa only [Subgroup.coe_pow, Subgroup.coe_one] using h2

theorem pow_eq_one_of_coe_eq_rootDiagUnit' {y : ↥(adjointGroup τ K)} {a : Fin τ.rank → Kˣ}
    (hya : (y : ModGL τ K) = rootDiagUnit τ a) {m : ℕ} (hm : a ^ m = 1) : y ^ m = 1 := by
  refine Subtype.ext ?_
  rw [Subgroup.coe_pow, hya, Subgroup.coe_one]
  change rootDiagUnitHom τ K a ^ m = 1
  rw [← map_pow, hm, map_one]

open CFSG.LieType.Steinberg.Adjoint RootSpace CFSG.RankThree.PartOne.KE in
open CFSG.RankThree.E6 (charVal charVal_neg) in
theorem famStabilizer_subset_closure_of_coprime [Finite K] {p : ℕ} (hp : p.Prime)
    (F : Set (Fin τ.rank → Kˣ)) (hF : ∀ a ∈ F, ∃ n : ℕ, a ^ p ^ n = 1)
    (hW : ¬ p ∣ Nat.card (famStabilizerSubgroup F)) :
    famStabilizer F ⊆ (famReflectionGroup F : Set (WeylGroup τ)) := by
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
  set U := famStabilizerSubgroup F with hU
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
    have h := u.2 a.1 a.2 x
    rw [hchar a.1 a.2, hchar a.1 a.2, zpow_eq_zpow_iff_modEq] at h
    exact h.symm.dvd
  have hrefl : ∀ α ∈ famKernel F, rootReflection α ∈ U := by
    intro α hα
    show ∀ a ∈ F, ∀ v, rootChar a (rootReflection α • v) = rootChar a v
    intro a ha v
    rw [rootReflection_smul hα.1, sub_eq_add_neg, ← neg_smul, rootChar_add, rootChar_zsmul,
      hα.2 a ha, one_zpow, mul_one]
  have hker : ∀ α, IsRoot τ α →
      ((∀ a : F, charVal (avgColumn U (fun i => (e a.1 i : ℤ))) α = 0) ↔ α ∈ famKernel F) := by
    intro α hα
    constructor
    · intro h
      refine ⟨hα, fun a ha => ?_⟩
      have h1 := hrcong ⟨a, ha⟩ α
      rw [h ⟨a, ha⟩, zero_sub, dvd_neg] at h1
      rw [hchar a ha]
      exact orderOf_dvd_iff_zpow_eq_one.1 (hcop.dvd_of_dvd_mul_left h1)
    · intro hαk a
      have h1 := hrinv a _ (hrefl α hαk) α
      rw [rootReflection_smul_self hα, charVal_neg] at h1
      omega
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
    rw [← hker α hα]
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

end Toral

section Conj



theorem exists_subCoreFamily_centralizer_of_conj_toral [Finite K] [CharP K 2]
    (A : Subgroup ↥(adjointGroup τ K)) (hA1 : A ≠ ⊥) (g : ↥(adjointGroup τ K))
    (hg : ∀ x ∈ A, ((g * x * g⁻¹ : ↥(adjointGroup τ K)) : ModGL τ K) ∈ torusGroup τ K)
    (hW : ∃ k, LayerFacts.ggDer (famStabilizerSubgroup
      (torusTuples (A.map (MulAut.conj g).toMonoidHom))) k ≤
        famReflectionGroup (torusTuples (A.map (MulAut.conj g).toMonoidHom))) :
    ∃ (β : Type) (S : β → Subgroup ↥(adjointGroup τ K)),
      LayerCores.IsSubCoreFamily (Subgroup.centralizer (A : Set ↥(adjointGroup τ K))) S := by
  refine exists_subCoreFamily_centralizer_of_conj g A ?_
  refine exists_subCoreFamily_centralizer_of_toral _ ?_ ?_ hW
  · rintro _ ⟨x, hx, rfl⟩
    exact hg x hx
  · rw [Ne, Subgroup.map_eq_bot_iff_of_injective _ (MulAut.conj g).injective]
    exact hA1

end Conj

end LayerExc

section Defs

@[expose] def GGExcToral (τ : Tag)
    (K : Type) [Field K] (A : Subgroup ↥(adjointGroup τ K)) : Prop :=
  ∃ g : ↥(adjointGroup τ K), ∀ x ∈ A,
    ((g * x * g⁻¹ : ↥(adjointGroup τ K)) : ModGL τ K) ∈ torusGroup τ K

@[expose] def GGWeylFamQuotSolvInput (τ : Tag) : Prop :=
  ∀ (K : Type) [Field K] [Finite K] [CharP K 2] (p : ℕ), p.Prime → p ≠ 2 →
    ∀ F : Set (Fin τ.rank → Kˣ), (∀ a ∈ F, ∃ n : ℕ, a ^ p ^ n = 1) →
      p ∣ Nat.card (LayerExc.famStabilizerSubgroup F) →
        ∃ k, LayerFacts.ggDer (LayerExc.famStabilizerSubgroup F) k ≤
          LayerExc.famReflectionGroup F

theorem ggWeylFamQuotSolvInput_F4 :
    GGWeylFamQuotSolvInput .F4 := fun _ _ _ _ _ _ _ F _ _ =>
  LayerExc.exists_ggDer_famStabilizerSubgroup_le_of_isSolvable LayerExc.isSolvable_weylGroup_F4 F

end Defs

section Tags

@[expose] def GGExcAdjCoreNonToralInput (τ : Tag) : Prop :=
  ∀ (K : Type) [Field K] [Finite K] [CharP K 2] (p : ℕ), p.Prime → p ≠ 2 →
    ∀ A : Subgroup ↥(adjointGroup τ K), IsPGroup p A → (∀ a ∈ A, ∀ b ∈ A, a * b = b * a) →
      ¬ GGExcToral τ K A →
        ∃ (β : Type) (S : β → Subgroup ↥(adjointGroup τ K)),
          LayerCores.IsSubCoreFamily (Subgroup.centralizer (A : Set ↥(adjointGroup τ K))) S

theorem ggExcAdjCoreRestInput_of_nonToral {τ : Tag} (hW : GGWeylFamQuotSolvInput τ)
    (hN : GGExcAdjCoreNonToralInput τ) : GGExcAdjCoreRestInput τ := by
  intro K _ _ _ p hp hp2 A hA hAc hs
  by_cases ht : GGExcToral τ K A
  · obtain ⟨g, hg⟩ := ht
    have hA1 : A ≠ ⊥ := fun h => hs (Or.inl h)
    have hpow : ∀ a ∈ LayerExc.torusTuples (A.map (MulAut.conj g).toMonoidHom),
        ∃ n : ℕ, a ^ p ^ n = 1 := by
      rintro a ⟨_, ⟨x, hx, rfl⟩, hxa⟩
      obtain ⟨n, hn⟩ := hA ⟨x, hx⟩
      have hxn : x ^ p ^ n = 1 := by
        have h1 := congrArg Subtype.val hn
        simpa only [Subgroup.coe_pow, Subgroup.coe_one] using h1
      refine ⟨n, LayerExc.pow_eq_one_of_coe_eq_rootDiagUnit hxa ?_⟩
      change (g * x * g⁻¹) ^ p ^ n = 1
      rw [conj_pow, hxn, mul_one, mul_inv_cancel]
    by_cases hcase : p ∣ Nat.card (LayerExc.famStabilizerSubgroup
        (LayerExc.torusTuples (A.map (MulAut.conj g).toMonoidHom)))
    · exact LayerExc.exists_subCoreFamily_centralizer_of_conj_toral A hA1 g hg
        (hW K p hp hp2 _ hpow hcase)
    · exact LayerExc.exists_subCoreFamily_centralizer_of_conj_toral A hA1 g hg
        ⟨0, LayerExc.famStabilizer_subset_closure_of_coprime hp _ hpow hcase⟩
  · exact hN K p hp hp2 A hA hAc ht

theorem ggExcAdjCoreRestInput_F4_of_nonToral (h : GGExcAdjCoreNonToralInput .F4) :
    GGExcAdjCoreRestInput .F4 :=
  ggExcAdjCoreRestInput_of_nonToral ggWeylFamQuotSolvInput_F4 h

theorem ggLayerTags_F4_of_nonToral (h : GGExcAdjCoreNonToralInput .F4) :
    GGLayerCentreOddTag .F4 ∧ GGLayerPerfectTag .F4 :=
  ggLayerTags_F4_of_rest (ggExcAdjCoreRestInput_F4_of_nonToral h)

theorem ggLayerTags_E7_of_nonToral (hW : GGWeylFamQuotSolvInput .E7)
    (h : GGExcAdjCoreNonToralInput .E7) : GGLayerCentreOddTag .E7 ∧ GGLayerPerfectTag .E7 :=
  ggLayerTags_E7_of_rest (ggExcAdjCoreRestInput_of_nonToral hW h)

theorem ggLayerTags_E8_of_nonToral (hW : GGWeylFamQuotSolvInput .E8)
    (h : GGExcAdjCoreNonToralInput .E8) : GGLayerCentreOddTag .E8 ∧ GGLayerPerfectTag .E8 :=
  ggLayerTags_E8_of_rest (ggExcAdjCoreRestInput_of_nonToral hW h)

end Tags

end CFSG.StandardType
