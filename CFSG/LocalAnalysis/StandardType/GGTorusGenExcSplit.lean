module

public import CFSG.LocalAnalysis.StandardType.GGTorusGenHomocyclic
public import CFSG.LocalAnalysis.StandardType.GGSixLayerPDivExcToral
public import CFSG.LocalAnalysis.StandardType.GGSixOrderPAutInnerExc
public import CFSG.LocalAnalysis.StandardType.GGKGForkExcCent
public import CFSG.LocalAnalysis.StandardType.GGL45NtExcG2Three
public import CFSG.LocalAnalysis.StandardType.GGTorusGenRTransfer
public import CFSG.LocalAnalysis.StandardType.GGTorusGenSLTransfer
public import CFSG.LocalAnalysis.StandardType.GGTableBExcCoverRows
public import CFSG.LocalAnalysis.StandardType.GGTableBExcSplitLLineE6
public import CFSG.LieType.Chevalley.ParabolicSylowSubsystem

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly TableB

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley in
theorem TableBExc.adjointGroup_inf_centralizer_torusPow_of_ne_two
    {τ : Tag} {k : Type} [Field k] [Finite k] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpk : p ∣ Nat.card kˣ)
    (hfullp : ∀ a : Fin τ.rank → kˣ, (∀ i, a i ^ p = 1) → rootDiagUnit τ a ∈ torusGroup τ k) :
    adjointGroup τ k ⊓
        Subgroup.centralizer {h : ModGL τ k | h ∈ torusGroup τ k ∧ h ^ p = 1} =
      torusGroup τ k := by
  have : Fact p.Prime := ⟨hp⟩
  have hTcomm := (triangular_borel_structure.{0, 0} τ k).1
  refine le_antisymm (fun z hz => ?_) (le_inf
    CFSG.LieType.AlgebraicGroups.torusGroup_le_adjointGroup fun h hh =>
      Subgroup.mem_centralizer_iff.2 fun x hx => hTcomm _ hx.1 _ hh)
  obtain ⟨hzC, hzV⟩ := Subgroup.mem_inf.1 hz
  obtain ⟨ζ, hζo⟩ := exists_prime_orderOf_dvd_card' p hpk
  have hζp : ζ ^ p = 1 := hζo ▸ pow_orderOf_eq_one ζ
  let a : Fin τ.rank → Fin τ.rank → kˣ :=
    fun i => Pi.mulSingle (M := fun _ => kˣ) i ζ
  have hap : ∀ i, a i ^ p = 1 := fun i => by
    show Pi.mulSingle (M := fun _ => kˣ) i ζ ^ p = 1
    rw [← Pi.mulSingle_pow, hζp, Pi.mulSingle_one]
  have hbV : ∀ i, rootDiagUnit τ (a i) ∈
      {h : ModGL τ k | h ∈ torusGroup τ k ∧ h ^ p = 1} := fun i =>
    ⟨hfullp (a i) (fun j => by simpa using congrFun (hap i) j), by
      have h1 : rootDiagUnit τ (a i) ^ p = rootDiagUnit τ (a i ^ p) :=
        ExcSplitL.rootDiagUnit_pow' (a i) p
      rw [h1, hap i, rootDiagUnit_one]⟩
  have hfam : z ∈ CFSG.HardMathSupport.Timmesfeld.Torality.familyCentralizer τ k a := by
    refine CFSG.HardMathSupport.Timmesfeld.Torality.mem_familyCentralizer.2
      ⟨hzC, fun i => ?_⟩
    rw [Subgroup.mem_centralizer_iff.1 hzV _ (hbV i), mul_inv_cancel_right]
  have hker : CFSG.HardMathSupport.Timmesfeld.Torality.familyKernel a = ∅ := by
    refine Set.eq_empty_iff_forall_notMem.2 fun α hα => ?_
    obtain ⟨hαroot, hαtriv⟩ := hα
    have hpu : ¬ IsUnit (p : ℤ) := (Nat.prime_iff_prime_int.mp hp).not_unit
    have hnot : ¬ ∀ j, (p : ℤ) ∣ α j :=
      CFSG.HardMathSupport.C14G2Three.not_forall_dvd_of_isRoot hαroot hpu
    push Not at hnot
    obtain ⟨j, hj⟩ := hnot
    have h1 : rootChar (a j) α = 1 := hαtriv j
    dsimp only [a] at h1
    rw [ExcSplitL.rootChar_mulSingle] at h1
    have h2 : (p : ℤ) ∣ α j := by
      rw [← hζo]
      exact orderOf_dvd_iff_zpow_eq_one.2 h1
    exact hj h2
  have hstab : CFSG.HardMathSupport.Timmesfeld.Torality.familyStabilizer a = {1} := by
    refine Set.eq_singleton_iff_unique_mem.2 ⟨fun i v => by simp [a], fun w hw => ?_⟩
    exact ExcSplitL.eq_one_of_mem_rootCharStabilizer hp2 hζo fun i => hw i
  exact ggKGEx_familyCentralizer_le_torus a hker hstab hfam

namespace TableBExc

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

variable
  {K : Type} [Field K] [Finite K] [CharP K 2]

theorem ggTorusGenR_adjoint_of_split {τ : Tag} {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ∣ Nat.card K - 1)
    (hfullp : ∀ a : Fin τ.rank → Kˣ, (∀ i, a i ^ p = 1) → rootDiagUnit τ a ∈ torusGroup τ K)
    (hV : Nat.card (torusPow τ K p) = p ^ τ.rank) (hT : GGExcToralRankInput τ K p)
    (hrefl : GGTorusReflElt p τ.rank (adjointGroup τ K)) (hr3 : 3 ≤ τ.rank) :
    GGTorusGenR p τ.rank (adjointGroup τ K) := by
  have : Fact p.Prime := ⟨hp⟩
  set A : Subgroup (adjointGroup τ K) := torusPow τ K p with hA
  set T : Subgroup (adjointGroup τ K) :=
    (torusGroup τ K).comap (adjointGroup τ K).subtype with hTdef
  have hTcomm := (triangular_borel_structure.{0, 0} τ K).1
  have hpk : p ∣ Nat.card Kˣ := by rwa [Nat.card_units]
  obtain ⟨d, e, c, nrefl, hrange, -, hn, hirrRefl⟩ :=
    hrefl A (hA.symm ▸ OrdPInnerExc.isElemAbelian_torusPow τ K p)
      (by rw [hA, hV]) (by rw [hA, hV]; exact pow_le_pow_right₀ hp.one_lt.le hr3)
  have hTab : ∀ x ∈ T, ∀ y ∈ T, x * y = y * x := by
    intro x hx y hy
    exact Subtype.ext (hTcomm _ hx _ hy)
  have hAT : A ≤ T := by
    intro x hx
    rw [hA] at hx
    exact (TableBExc.mem_torusPow.1 hx).1
  have hcent : Subgroup.centralizer (A : Set (adjointGroup τ K)) ≤ T := by
    intro z hz
    have hzC : (z : ModGL τ K) ∈ Subgroup.centralizer
        {h : ModGL τ K | h ∈ torusGroup τ K ∧ h ^ p = 1} := by
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      have hhA : (⟨h, CFSG.LieType.AlgebraicGroups.torusGroup_le_adjointGroup hh.1⟩ :
          adjointGroup τ K) ∈ A := by
        rw [hA, TableBExc.mem_torusPow]
        exact ⟨hh.1, Subtype.ext hh.2⟩
      exact congrArg Subtype.val (Subgroup.mem_centralizer_iff.1 hz _ hhA)
    have hmem : (z : ModGL τ K) ∈ adjointGroup τ K ⊓
        Subgroup.centralizer {h : ModGL τ K | h ∈ torusGroup τ K ∧ h ^ p = 1} :=
      ⟨z.2, hzC⟩
    rw [TableBExc.adjointGroup_inf_centralizer_torusPow_of_ne_two hp hp2 hpk hfullp] at hmem
    exact hmem
  have hNA : Subgroup.closure (Set.range nrefl) ≤
      Subgroup.normalizer (A : Set (adjointGroup τ K)) := by
    refine (Subgroup.closure_le (Subgroup.normalizer (A : Set (adjointGroup τ K)))).2 ?_
    rintro _ ⟨i, rfl⟩
    change nrefl i ∈ Subgroup.normalizer (A : Set (adjointGroup τ K))
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    refine Subgroup.eq_of_le_of_card_ge ?_ ?_
    · rintro x ⟨y, hy, rfl⟩
      rw [← hrange] at hy
      obtain ⟨v, rfl⟩ := hy
      show nrefl i * e v * (nrefl i)⁻¹ ∈ A
      have hv : Multiplicative.ofAdd (Multiplicative.toAdd v) = v := rfl
      have hstep : nrefl i * e v * (nrefl i)⁻¹ =
          e (.ofAdd (Multiplicative.toAdd v - c i (Multiplicative.toAdd v) •
            Pi.single i 1)) := by
        rw [← hv]
        exact hn i (Multiplicative.toAdd v)
      rw [hstep, ← hrange]
      exact ⟨_, rfl⟩
    · rw [Subgroup.card_map_of_injective (MulAut.conj (nrefl i)).injective]
  have htors : ∀ y ∈ T, y ^ p = 1 → y ∈ A := by
    intro y hy hyp
    rw [hA]
    exact TableBExc.mem_torusPow.2 ⟨hy, hyp⟩
  have hirr : ∀ Q : Subgroup (adjointGroup τ K), Q ≤ A →
      Subgroup.closure (Set.range nrefl) ≤
        Subgroup.normalizer (Q : Set (adjointGroup τ K)) → Q = ⊥ ∨ Q = A := by
    intro Q hQ hNQ
    exact hirrRefl Q hQ fun i x hx =>
      (Subgroup.mem_normalizer_iff.1 (hNQ (Subgroup.subset_closure ⟨i, rfl⟩)) x).1 hx
  have hAcard : Nat.card A = p ^ τ.rank := by rw [hA, hV]
  have hn : Nat.card K - 1 ≠ 0 := by
    have : 2 ≤ Nat.card K := Finite.one_lt_card
    omega
  have hexp : (∃ s ∈ T, orderOf s = p ^ (Nat.card K - 1).factorization p) →
      ∀ y ∈ T, (∃ k : ℕ, y ^ p ^ k = 1) →
        y ^ p ^ (Nat.card K - 1).factorization p = 1 := by
    intro _ y hy hk
    obtain ⟨k, hk⟩ := hk
    have hyT : ((y : adjointGroup τ K) : ModGL τ K) ∈ torusGroup τ K := hy
    have h1 : y ^ Nat.card Kˣ = 1 := by
      refine Subtype.ext ?_
      simpa using CFSG.LieType.Chevalley.ParSylow.torusGroup_pow_card_units hyT
    have hordN : orderOf y ∣ Nat.card K - 1 := by
      rw [← Nat.card_units]
      exact orderOf_dvd_of_pow_eq_one h1
    have hordp : orderOf y ∣ p ^ k := orderOf_dvd_of_pow_eq_one hk
    obtain ⟨j, -, hjeq⟩ := (Nat.dvd_prime_pow hp).1 hordp
    have hjp : p ^ j ∣ Nat.card K - 1 := hjeq ▸ hordN
    rw [← orderOf_dvd_iff_pow_eq_one, hjeq]
    exact pow_dvd_pow p ((hp.pow_dvd_iff_le_factorization hn).1 hjp)
  have hU : ∀ E : Subgroup (adjointGroup τ K), IsElemAbelian p E →
      p ^ τ.rank ≤ Nat.card E →
      (∀ g : adjointGroup τ K, (∀ x ∈ E, g * x = x * g) → g ^ p = 1 → g ∈ E) →
      ∃ c : adjointGroup τ K, E = A.map (MulAut.conj c).toMonoidHom := by
    intro E hE hcard _
    obtain ⟨g, hg⟩ := hT E hE hcard
    have hconj : (MulAut.conj g⁻¹).toMonoidHom.comp (MulAut.conj g).toMonoidHom =
        MonoidHom.id (adjointGroup τ K) := by
      ext x
      simp only [MonoidHom.comp_apply, MonoidHom.id_apply, MulEquiv.coe_toMonoidHom,
        MulAut.conj_apply, inv_inv]
      group
    refine ⟨g⁻¹, ?_⟩
    have h1 := congrArg (Subgroup.map (MulAut.conj g⁻¹).toMonoidHom) hg
    rw [Subgroup.map_map, hconj, Subgroup.map_id] at h1
    rw [hA]
    exact h1
  have hcomp : ∀ x ∈ A, x ≠ 1 → ∀ J : Subgroup (adjointGroup τ K),
      IsComponentOf J (Subgroup.centralizer {x}) →
      ∃ s ∈ J, s ∈ T ∧ orderOf s = p ^ (Nat.card K - 1).factorization p := by
    intro x hxA _ J hJ
    have he : p ^ (Nat.card K - 1).factorization p ∣ Nat.card Kˣ := by
      rw [Nat.card_units]
      exact Nat.ordProj_dvd _ _
    obtain ⟨S, hS⟩ := Sylow.exists_subgroup_card_pow_prime (G := Kˣ) p he
    obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := S)
    have hgo : orderOf (g : Kˣ) = p ^ (Nat.card K - 1).factorization p := by
      rw [Subgroup.orderOf_coe, hg, hS]
    have hodd : Odd (orderOf (g : Kˣ)) := by
      rw [hgo]
      exact (hp.odd_of_ne_two hp2).pow
    have hxA' : x ∈ torusPow τ K p := hA ▸ hxA
    have hxp : x ^ p ^ 1 = 1 := by
      rw [pow_one]
      exact (TableBExc.mem_torusPow.1 hxA').2
    obtain ⟨s, hsJ, hsT, hso⟩ :=
      CFSG.StandardType.LayerPDivExc.exists_mem_torusGroup_orderOf_of_isComponentOf
        (τ := τ) (K := K) hp (n := 1) (b := x) (TableBExc.mem_torusPow.1 hxA').1 hxp hJ hodd
    exact ⟨s, hsJ, hsT, by rw [hso, hgo]⟩
  exact ggTorusGenR_of_torusIrred (r := τ.rank) (n := τ.rank)
    (e := (Nat.card K - 1).factorization p) hTab hAT hcent hNA htors hirr hAcard hexp hU hcomp

theorem ggTorusGenR_E8 {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ Nat.card K - 1) :
    GGTorusGenR p 8 (RecipeGroup .E8 K) :=
  ggTorusGenR_of_mulEquiv (recipeEquiv .E8 K)
    (ggTorusGenR_adjoint_of_split (τ := .E8) hp hp2 hpq (fun a _ => full_of_E7_E8 (Or.inr rfl) a)
      (card_torusPow_E8 hp hpq) (IOneRest.ggExcToralRankInput_E7E8 (Or.inr rfl) hp hp2 hpq)
      (NbrInnerRest.ggTorusReflElt_adjoint (τ := .E8) hp hpq
        (isUnit_det_cartan_of_eq hp CFSG.LieType.Chevalley.det_cartan_E8 (Nat.coprime_one_left p))
        (NbrInnerRest.cartanE_connected (by decide))
        (fun i j h => NbrInnerRest.cartanE_entry_ne_zero hp hp2 i j h)
        (card_torusPow_E8 hp hpq)
        (IOneRest.ggExcToralRankInput_E7E8 (Or.inr rfl) hp hp2 hpq)) (by decide))

theorem ggTorusGenR_E7 {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ Nat.card K - 1) :
    GGTorusGenR p 7 (RecipeGroup .E7 K) :=
  ggTorusGenR_of_mulEquiv (recipeEquiv .E7 K)
    (ggTorusGenR_adjoint_of_split (τ := .E7) hp hp2 hpq (fun a _ => full_of_E7_E8 (Or.inl rfl) a)
      (card_torusPow_E7 hp hpq) (IOneRest.ggExcToralRankInput_E7E8 (Or.inl rfl) hp hp2 hpq)
      (NbrInnerRest.ggTorusReflElt_adjoint (τ := .E7) hp hpq
        (isUnit_det_cartan_of_eq hp CFSG.LieType.Chevalley.det_cartan_E7
          ((Nat.coprime_primes Nat.prime_two hp).2 (Ne.symm hp2)))
        (NbrInnerRest.cartanE_connected (by decide))
        (fun i j h => NbrInnerRest.cartanE_entry_ne_zero hp hp2 i j h)
        (card_torusPow_E7 hp hpq)
        (IOneRest.ggExcToralRankInput_E7E8 (Or.inl rfl) hp hp2 hpq)) (by decide))

theorem ggTorusGenR_E6 {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3)
    (hpq : p ∣ Nat.card K - 1) : GGTorusGenR p 6 (RecipeGroup .E6 K) :=
  ggTorusGenR_of_mulEquiv (recipeEquiv .E6 K)
    (ggTorusGenR_adjoint_of_split (τ := .E6) hp hp2 hpq
      (fullp_E6 hp.one_lt ((Nat.coprime_primes Nat.prime_three hp).2 (Ne.symm hp3)))
      (card_torusPow_E6 hp hp3 hpq) (ggExcToralRankInput_E6_of_ne_three hp hp2 hp3 hpq)
      (NbrInnerRest.ggTorusReflElt_adjoint (τ := .E6) hp hpq
        (isUnit_det_cartan_of_eq hp CFSG.LieType.Chevalley.det_cartan_E6
          ((Nat.coprime_primes Nat.prime_three hp).2 (Ne.symm hp3)))
        (NbrInnerRest.cartanE_connected (by decide))
        (fun i j h => NbrInnerRest.cartanE_entry_ne_zero hp hp2 i j h)
        (card_torusPow_E6 hp hp3 hpq)
        (ggExcToralRankInput_E6_of_ne_three hp hp2 hp3 hpq)) (by decide))

end TableBExc

namespace TableBF4

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.RankThree.Chevalley

variable
  {K : Type} [Field K] [Finite K] [CharP K 2]

theorem ggTorusGenR_F4 {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ Nat.card K - 1) :
    GGTorusGenR p 4 (RecipeGroup K) :=
  have hT : GGF4ToralRankInput K p :=
    ggF4ToralRankInput_of_three hp hp2 hpq fun _ => ggF4ThreeRankInput_holds
  ggTorusGenR_of_mulEquiv (recipeEquiv K)
    (TableBExc.ggTorusGenR_adjoint_of_split (τ := .F4) hp hp2 hpq
      (fun a _ => F4_rootDiagUnit_mem_torusGroup a) (card_torusPow hp hpq) hT
      (ggTorusReflElt_adjointF4 hp hp2 hpq hT) (by decide))

end TableBF4

section Recipe

variable
  {K : Type} [Field K] [Finite K] [CharP K 2]

theorem ggTorusGenTableB_recipe_E8
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ∣ Nat.card K - 1) :
    GGTorusGenTableB p (TableBExc.RecipeGroup .E8 K) (TableBExc.RecipeID .E8 K) :=
  ggTorusGenTableB_of_rk (r := 9) hp (by norm_num) (TableBExc.ggTorusLift_E8 hp hp2 hpq)
    (ggTorusGenTableBRk_of_torusGenR (r := 8) hp
      (fun _ hφ _ => TableBExc.idImage_subset_inn_E8 K hφ)
      (TableBExc.center_recipeGroup_eq_bot .E8 K) (ExcSplitL.ggCenterPrime_recipe_E8 hp hp2)
      (TableBExc.ggTorusGenR_E8 hp hp2 hpq))

theorem ggTorusGenTableB_recipe_E7
    {f : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = 2 ^ f) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ Nat.card K - 1) :
    GGTorusGenTableB p (TableBExc.RecipeGroup .E7 K) (TableBExc.RecipeID .E7 K) :=
  ggTorusGenTableB_of_rk (r := 8) hp (by norm_num) (TableBExc.ggTorusLift_E7 hp hp2 hpq)
    (ggTorusGenTableBRk_of_torusGenR (r := 7) hp
      (fun _ hφ _ => TableBExc.idImage_subset_inn_E7 K hφ)
      (TableBExc.center_recipeGroup_eq_bot .E7 K) (ExcSplitL.ggCenterPrime_recipe_E7 hf hK hp hp2)
      (TableBExc.ggTorusGenR_E7 hp hp2 hpq))

theorem ggTorusGenTableB_recipe_E6
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3)
    (hpq : p ∣ Nat.card K - 1) :
    GGTorusGenTableB p (TableBExc.RecipeGroup .E6 K) (TableBExc.RecipeID .E6 K) :=
  ggTorusGenTableB_of_rk (r := 7) hp (by norm_num) (TableBExc.ggTorusLift_E6 hp hp2 hp3 hpq)
    (ggTorusGenTableBRk_of_torusGenR (r := 6) hp (TableBExc.ggOutdiagPrime_E6 hp hp3)
      (TableBExc.center_recipeGroup_eq_bot .E6 K) (ExcSplitL.ggCenterPrime_recipe_E6 hp hp2 hp3)
      (TableBExc.ggTorusGenR_E6 hp hp2 hp3 hpq))

theorem ggTorusGenTableB_recipe_F4
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ∣ Nat.card K - 1) :
    GGTorusGenTableB p (TableBF4.RecipeGroup K) (TableBF4.RecipeID K) :=
  ggTorusGenTableB_of_rk (r := 5) hp (by norm_num) (TableBF4.ggTorusLift_F4 hp hp2 hpq)
    (ggTorusGenTableBRk_of_torusGenR (r := 4) hp
      (fun _ hφ _ => TableBF4.idImage_subset_inn K hφ)
      (TableBF4.center_recipeGroup_eq_bot K) (ExcSplitL.ggCenterPrime_recipe_F4 hp hp2)
      (TableBF4.ggTorusGenR_F4 hp hp2 hpq))

end Recipe

section Label


theorem largeEvenLabelAll_torusGenTableB_excInn
    {p : ℕ} (hp : p.Prime) {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab)
    (hrow : GGL48TBExcInnRow p lab) :
    LargeEvenLabelAll lab fun R _ I _ => GGTorusGenTableB p R I := by
  obtain ⟨t, l, n⟩ := lab
  obtain ⟨htag, hpn⟩ := hrow
  have hn : 1 ≤ n := hlab.1
  dsimp only at htag hpn hn
  have hp2 : p ≠ 2 := ne_two_of_dvd_two_pow_sub_one hn hpn
  rcases htag with rfl | rfl | rfl
  · intro Q hQ
    dsimp only [LargeEvenRawDatum] at hQ ⊢
    refine recipeChevalley_and (fun K _ _ hK => ?_) hQ
    have : CharP K 2 := charP_two_of_card hK
    have hpq : p ∣ Nat.card K - 1 := by rw [hK]; exact hpn
    exact ggTorusGenTableB_recipe_E7 hn hK hp hp2 hpq
  · intro Q hQ
    dsimp only [LargeEvenRawDatum] at hQ ⊢
    refine recipeChevalley_and (fun K _ _ hK => ?_) hQ
    have : CharP K 2 := charP_two_of_card hK
    have hpq : p ∣ Nat.card K - 1 := by rw [hK]; exact hpn
    exact ggTorusGenTableB_recipe_E8 hp hp2 hpq
  · intro Q hQ
    dsimp only [LargeEvenRawDatum] at hQ ⊢
    refine recipeChevalley_and (fun K _ _ hK => ?_) hQ
    have : CharP K 2 := charP_two_of_card hK
    have hpq : p ∣ Nat.card K - 1 := by rw [hK]; exact hpn
    exact ggTorusGenTableB_recipe_F4 hp hp2 hpq

theorem largeEvenLabelAll_torusGenTableB_E6
    {p : ℕ} (hp : p.Prime) (hp3 : p ≠ 3) {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab)
    (hrow : GGL48TBE6Row p lab) :
    LargeEvenLabelAll lab fun R _ I _ => GGTorusGenTableB p R I := by
  obtain ⟨t, l, n⟩ := lab
  obtain ⟨htag, hpn⟩ := hrow
  have hn : 1 ≤ n := hlab.1
  dsimp only at htag hpn hn
  have hp2 : p ≠ 2 := ne_two_of_dvd_two_pow_sub_one hn hpn
  subst htag
  intro Q hQ
  dsimp only [LargeEvenRawDatum] at hQ ⊢
  refine recipeChevalley_and (fun K _ _ hK => ?_) hQ
  have : CharP K 2 := charP_two_of_card hK
  have hpq : p ∣ Nat.card K - 1 := by rw [hK]; exact hpn
  exact ggTorusGenTableB_recipe_E6 hp hp2 hp3 hpq

end Label

end CFSG.StandardType
