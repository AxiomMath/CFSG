module

public import CFSG.LocalAnalysis.StandardType.GGSixStepTwoToralRestTagsSplit
public import CFSG.LocalAnalysis.StandardType.GGSixBstarExcFramesWeyl
public import CFSG.LocalAnalysis.StandardType.GGSixLayerPDivExcToral
public import CFSG.LieType.Chevalley.OrthogonalSemilinearFixedCells
public import CFSG.RankThree.PartOne.K133H.F4Weyl
public import CFSG.RankThree.Chevalley.SteinbergCAF4SplitPrimeTorus
public import CFSG.LocalAnalysis.StandardType.GGTableBExcE6Basic
public import CFSG.LieType.Chevalley.LangRootArithmeticDet

public section

namespace CFSG.StandardType

namespace StepTwoToralExc

open CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.RankThree.PartOne.KE8F LayerExc LayerSixE

section Automizer

variable {τ : Tag} {K : Type} [Field K] [Finite K] {p : ℕ} [Fact p.Prime]


omit [Finite K] [Fact p.Prime]
  in
theorem frameDiag_mem_torusGroup [NeZero p]
    (hfullp : ∀ a : Fin τ.rank → Kˣ, (∀ i, a i ^ p = 1) → rootDiagUnit τ a ∈ torusGroup τ K)
    (ζ : Kˣ) (hζ : ζ ^ p = 1) (s : Fin τ.rank → ZMod p) :
    ExcFrames.frameDiag ζ hζ s ∈ torusGroup τ K := by
  refine hfullp _ fun i => ?_
  rw [TableBExc.E6Three.zetaVec_apply, ← pow_mul, mul_comm, pow_mul, hζ, one_pow]

omit [Finite K] [Fact p.Prime]
  in
theorem frameDiag_mem_splitPow [NeZero p]
    (hfullp : ∀ a : Fin τ.rank → Kˣ, (∀ i, a i ^ p = 1) → rootDiagUnit τ a ∈ torusGroup τ K)
    (ζ : Kˣ) (hζ : ζ ^ p = 1) (s : Fin τ.rank → ZMod p) :
    ExcFrames.frameDiag ζ hζ s ∈ ExcFrames.splitPow τ K p :=
  ⟨frameDiag_mem_torusGroup hfullp ζ hζ s, ExcFrames.frameDiag_pow ζ hζ s⟩

omit [Finite K] in
theorem pow_card_weyl_eq_one_of_mem_ggAutomizer
    (hfullp : ∀ a : Fin τ.rank → Kˣ, (∀ i, a i ^ p = 1) → rootDiagUnit τ a ∈ torusGroup τ K)
    (hdet : IsUnit ((τ.symmetrizedCartan.det : ℤ) : ZMod p)) {ζ : Kˣ} (hζo : orderOf ζ = p)
    {φ : MulAut ↥(TableBExc.torusPow τ K p)}
    (hφ : φ ∈ ggAutomizer ⊤ (TableBExc.torusPow τ K p)) :
    φ ^ Nat.card (WeylGroup τ) = 1 := by
  have : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  have hζ : ζ ^ p = 1 := hζo ▸ pow_orderOf_eq_one ζ
  obtain ⟨g, -, hgN, hgφ⟩ := mem_ggAutomizer_iff.mp hφ
  have hnorm : ∀ x : adjointGroup τ K, x ∈ TableBExc.torusPow τ K p ↔
      g * x * g⁻¹ ∈ TableBExc.torusPow τ K p := fun x => Subgroup.mem_normalizer_iff.mp hgN x
  obtain ⟨w, hw⟩ := ExcFrames.exists_weyl_of_normalizes hnorm
  set t : (Fin τ.rank → ZMod p) → ↥(TableBExc.torusPow τ K p) := fun s =>
    ⟨⟨ExcFrames.frameDiag ζ hζ s, CFSG.RankThree.CentralCover.torusGroup_le_adjointGroup
        (frameDiag_mem_torusGroup hfullp ζ hζ s)⟩,
      ExcFrames.mem_torusPow_iff_coe.mpr (frameDiag_mem_splitPow hfullp ζ hζ s)⟩ with ht
  have hφt : ∀ s, φ (t s) = t (TableBExc.torusAct τ p w s) := by
    intro s
    have h1 : ((φ (t s) : adjointGroup τ K) : ModGL τ K) =
        (g : ModGL τ K) * ExcFrames.frameDiag ζ hζ s * (g : ModGL τ K)⁻¹ := by
      rw [hgφ (t s)]
      rfl
    rw [hw _ (frameDiag_mem_splitPow hfullp ζ hζ s), ExcFrames.canonicalRep_conj_frameDiag] at h1
    exact Subtype.ext (Subtype.ext h1)
  have hpow : ∀ k : ℕ, ∀ s, (φ ^ k) (t s) = t (TableBExc.torusAct τ p (w ^ k) s) := by
    intro k
    induction k with
    | zero => intro s; rw [pow_zero, pow_zero, TableBExc.torusAct_one]; rfl
    | succ k ih =>
      intro s
      rw [pow_succ, MulAut.mul_apply, hφt, ih, pow_succ, TableBExc.torusAct_mul]
  refine MulEquiv.ext fun x => ?_
  obtain ⟨s, hs⟩ := ExcFrames.exists_frameDiag_of_mem hζo hζ hdet
    (ExcFrames.mem_torusPow_iff_coe.mp x.2)
  have hx : x = t s := Subtype.ext (Subtype.ext hs.symm)
  rw [hx, hpow, pow_card_eq_one', TableBExc.torusAct_one, MulAut.one_apply]

theorem coprime_card_ggAutomizer_torusPow
    (hfullp : ∀ a : Fin τ.rank → Kˣ, (∀ i, a i ^ p = 1) → rootDiagUnit τ a ∈ torusGroup τ K)
    (hdet : IsUnit ((τ.symmetrizedCartan.det : ℤ) : ZMod p)) {ζ : Kˣ} (hζo : orderOf ζ = p)
    (hW : ¬ p ∣ Nat.card (WeylGroup τ)) :
    Nat.Coprime p (Nat.card (ggAutomizer ⊤ (TableBExc.torusPow τ K p))) := by
  have : Finite (adjointGroup τ K) := generated_group_finite τ K
  rw [Nat.Prime.coprime_iff_not_dvd Fact.out]
  intro hdvd
  obtain ⟨φ, hφ⟩ := exists_prime_orderOf_dvd_card' p hdvd
  apply hW
  rw [← hφ]
  refine orderOf_dvd_of_pow_eq_one (Subtype.ext ?_)
  rw [Subgroup.coe_pow]
  exact pow_card_weyl_eq_one_of_mem_ggAutomizer hfullp hdet hζo φ.2

end Automizer

section Components

variable {τ : Tag} {K : Type} [Field K]


theorem rootChar_pow_eq_one {p : ℕ} {b : Fin τ.rank → Kˣ} (hb : ∀ j, b j ^ p = 1)
    (u : Fin τ.rank → ℤ) : rootChar b u ^ p = 1 := by
  rw [rootChar, ← Finset.prod_pow]
  refine Finset.prod_eq_one fun j _ => ?_
  rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hb, one_zpow]

theorem exists_eq_of_isComponentOf_subCoreFamily {L : Type} [Group L] [Finite L]
    {H : Subgroup L} {β : Type} {S : β → Subgroup L} (hS : LayerCores.IsSubCoreFamily H S)
    {X : Subgroup L} (hX : IsComponentOf X H) : ∃ c, X = S c := by
  have hmap : H.map (MonoidHom.id L) = H := Subgroup.map_id H
  obtain ⟨c, hc⟩ := LayerPDiv.exists_eq_map_of_isComponentOf_sub (MonoidHom.id L)
    (by rw [MonoidHom.ker_id]; exact bot_le) hmap.le
    (by rw [hmap, Subgroup.subgroupOf_self]; infer_instance)
    (by rw [hmap]; exact Subgroup.commutator_le_self H) hS hX
  exact ⟨c, by rw [hc, Subgroup.map_id]⟩

theorem neg_mem_componentRoots' {M : Type*} [CommGroup M]
    {χ : Multiplicative (Fin τ.rank → ℤ) →* M} {i : KernelComponent χ} {α : Fin τ.rank → ℤ}
    (hα : α ∈ componentRoots χ i) : -α ∈ componentRoots χ i := by
  obtain ⟨hα', rfl⟩ := hα
  have hneg : -α ∈ kernelRoots χ := ⟨IsRoot.neg hα'.1, chi_neg hα'.2⟩
  refine ⟨hneg, (mk_eq_of_iform_ne_zero (α := ⟨α, hα'⟩) (β := ⟨-α, hneg⟩) ?_).symm⟩
  change CFSG.LieType.Steinberg.Adjoint.iform α (-α) ≠ 0
  have e : CFSG.LieType.Steinberg.Adjoint.iform α (-α) =
      -CFSG.LieType.Steinberg.Adjoint.iform α α := by
    simp [CFSG.LieType.Steinberg.Adjoint.iform, Finset.sum_neg_distrib]
  rw [e]
  exact neg_ne_zero.2 (iform_self_pos_of_isRoot hα'.1).ne'

theorem torusPow_le_normalizer_comap_componentRootSpan {M : Type*} [CommGroup M]
    (χ : Multiplicative (Fin τ.rank → ℤ) →* M) (i : KernelComponent χ) (p : ℕ) :
    TableBExc.torusPow τ K p ≤ Subgroup.normalizer
      (((componentRootSpan K χ i).comap (adjointGroup τ K).subtype :
        Subgroup (adjointGroup τ K)) : Set (adjointGroup τ K)) := by
  intro u hu
  have hN := CFSG.LieType.Chevalley.torusGroup_le_normalizer_rootSpan (K := K)
    (S := componentRoots χ i) (fun α hα => isRoot_of_mem_componentRoots hα) hu.1
  rw [Subgroup.mem_normalizer_iff] at hN ⊢
  intro x
  exact hN x

theorem rootWeylOne_mem_componentRootSpan {M : Type*} [CommGroup M]
    {χ : Multiplicative (Fin τ.rank → ℤ) →* M} {i : KernelComponent χ} {α : Fin τ.rank → ℤ}
    (hα : α ∈ componentRoots χ i) : rootWeylOne τ K α ∈ componentRootSpan K χ i := by
  have h := (rootWeylOne_spec (K := K) (isRoot_of_mem_componentRoots hα)).1
  have h1 : CFSG.Blueprint.Chevalley.rootSubgroup τ K α ≤ componentRootSpan K χ i := by
    show CFSG.Blueprint.Chevalley.rootSubgroup τ K α ≤ rootSpan τ K (componentRoots χ i)
    exact le_iSup₂_of_le α hα le_rfl
  have h2 : CFSG.Blueprint.Chevalley.rootSubgroup τ K (-α) ≤ componentRootSpan K χ i := by
    show CFSG.Blueprint.Chevalley.rootSubgroup τ K (-α) ≤ rootSpan τ K (componentRoots χ i)
    exact le_iSup₂_of_le (-α) (neg_mem_componentRoots' hα) le_rfl
  exact sup_le h1 h2 h

theorem rootChar_eq_one_of_commute_rootWeylOne [CharP K 2] {a : Fin τ.rank → Kˣ}
    {α : Fin τ.rank → ℤ} (hα : IsRoot τ α)
    (hc : rootWeylOne τ K α * rootDiagUnit τ a = rootDiagUnit τ a * rootWeylOne τ K α) :
    rootChar a α = 1 := by
  obtain ⟨-, hmon, hmaps⟩ := rootWeylOne_spec (K := K) hα
  have h1 := TableBExc.E6Three.monomial_conj_rootDiagUnit_weylTuple hmon hmaps a
  rw [hc, mul_inv_cancel_right] at h1
  have h2 : weylTuple (rootReflection α) a = a := (rootDiagUnit_injective h1).symm
  have h4 := rootChar_weylTuple (rootReflection α) a α
  rw [h2, rootReflection_inv hα, rootReflection_smul_self hα] at h4
  have h5 : rootChar a α * rootChar a (-α) = 1 := by
    rw [← rootChar_add, add_neg_cancel, rootChar_zero]
  rw [← h4] at h5
  have h6 : ((rootChar a α : Kˣ) : K) ^ 2 = 1 := by
    have h7 := congrArg (fun u : Kˣ => (u : K)) h5
    simpa [sq] using h7
  have h8 : (2 : K) = 0 := CharP.cast_eq_zero K 2
  have h9 : ((rootChar a α : Kˣ) : K) - 1 = 0 := by
    have h10 : (((rootChar a α : Kˣ) : K) - 1) ^ 2 = 0 := by
      linear_combination h6 + (1 - ((rootChar a α : Kˣ) : K)) * h8
    exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h10
  exact Units.ext (by simpa [sub_eq_zero] using h9)

theorem mem_centralizer_componentRootSpan {M : Type*} [CommGroup M]
    {χ : Multiplicative (Fin τ.rank → ℤ) →* M} {i : KernelComponent χ} {a : Fin τ.rank → Kˣ}
    (ha : ∀ α ∈ componentRoots χ i, rootChar a α = 1) {y : ModGL τ K}
    (hy : y ∈ componentRootSpan K χ i) : y * rootDiagUnit τ a = rootDiagUnit τ a * y := by
  have hle : componentRootSpan K χ i ≤
      Subgroup.centralizer ({rootDiagUnit τ a} : Set (ModGL τ K)) := by
    show rootSpan τ K (componentRoots χ i) ≤ _
    refine iSup₂_le fun α hα => (Subgroup.closure_le _).2 ?_
    rintro _ ⟨c, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
    have h1 := rootDiagUnit_conj_pinnedX a (isRoot_of_mem_componentRoots hα) c
    rw [ha α hα, Units.val_one, one_mul] at h1
    calc pinnedX τ K α c * rootDiagUnit τ a =
          rootDiagUnit τ a * pinnedX τ K α c * (rootDiagUnit τ a)⁻¹ * rootDiagUnit τ a := by
          rw [h1]
      _ = rootDiagUnit τ a * pinnedX τ K α c := by group
  exact Subgroup.mem_centralizer_singleton_iff.mp (hle hy)

theorem conj_mem_torusPow_of_monomial
    {p : ℕ} (hfullp : ∀ a : Fin τ.rank → Kˣ, (∀ i, a i ^ p = 1) → rootDiagUnit τ a ∈ torusGroup τ K)
    {x : adjointGroup τ K} (hx : (x : ModGL τ K) ∈ monomialSubgroup τ K) {w : WeylGroup τ}
    (hxw : MapsRootLines (x : ModGL τ K) w) {h : adjointGroup τ K}
    (hh : h ∈ TableBExc.torusPow τ K p) : x * h * x⁻¹ ∈ TableBExc.torusPow τ K p := by
  rw [TableBExc.mem_torusPow] at hh ⊢
  obtain ⟨b, hb⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hh.1
  refine ⟨?_, by rw [conj_pow, hh.2, mul_one, mul_inv_cancel]⟩
  have e : ((x * h * x⁻¹ : adjointGroup τ K) : ModGL τ K) =
      (x : ModGL τ K) * rootDiagUnit τ b * (x : ModGL τ K)⁻¹ := by
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, hb]
  rw [e, TableBExc.E6Three.monomial_conj_rootDiagUnit_weylTuple hx hxw b]
  have hbp : ∀ j, b j ^ p = 1 := by
    have h1 : rootDiagUnit τ (b ^ p) = rootDiagUnit τ 1 := by
      rw [← rootDiagUnit_pow, ← hb, rootDiagUnit_one]
      have h2 := congrArg (fun z : adjointGroup τ K => (z : ModGL τ K)) hh.2
      simpa only [Subgroup.coe_pow, Subgroup.coe_one] using h2
    intro j
    simpa only [Pi.pow_apply, Pi.one_apply] using congrFun (rootDiagUnit_injective h1) j
  exact hfullp _ fun i => rootChar_pow_eq_one hbp _

theorem mem_normalizer_torusPow_of_monomial
    {p : ℕ} (hfullp : ∀ a : Fin τ.rank → Kˣ, (∀ i, a i ^ p = 1) → rootDiagUnit τ a ∈ torusGroup τ K)
    {x : adjointGroup τ K} (hx : (x : ModGL τ K) ∈ monomialSubgroup τ K) {w : WeylGroup τ}
    (hxw : MapsRootLines (x : ModGL τ K) w) :
    x ∈ Subgroup.normalizer (TableBExc.torusPow τ K p : Set (adjointGroup τ K)) := by
  rw [Subgroup.mem_normalizer_iff]
  intro h
  refine ⟨conj_mem_torusPow_of_monomial hfullp hx hxw, fun hh => ?_⟩
  have hx' : ((x⁻¹ : adjointGroup τ K) : ModGL τ K) ∈ monomialSubgroup τ K := by
    rw [Subgroup.coe_inv]
    exact inv_mem hx
  have hxw' : MapsRootLines ((x⁻¹ : adjointGroup τ K) : ModGL τ K) w⁻¹ := by
    rw [Subgroup.coe_inv]
    exact hxw.inv
  have h1 := conj_mem_torusPow_of_monomial hfullp hx' hxw' hh
  rwa [show x⁻¹ * (x * h * x⁻¹) * x⁻¹⁻¹ = h by group] at h1

theorem exists_eq_comap_componentRootSpan [Finite K] [CharP K 2] {p : ℕ} (hp : p.Prime)
    (hW : ¬ p ∣ Nat.card (WeylGroup τ)) {l : Fin τ.rank → Kˣ} (hl : l ^ p = 1) (hl1 : l ≠ 1)
    {v : adjointGroup τ K} (hv : (v : ModGL τ K) = rootDiagUnit τ l)
    {L : Subgroup (adjointGroup τ K)} (hL : IsComponentOf L (Subgroup.centralizer {v})) :
    ∃ i : KernelComponent (famChar ({l} : Set (Fin τ.rank → Kˣ))),
      L = (componentRootSpan K (famChar ({l} : Set (Fin τ.rank → Kˣ))) i).comap
        (adjointGroup τ K).subtype := by
  classical
  have : Finite (adjointGroup τ K) := generated_group_finite τ K
  obtain ⟨j, hj⟩ : ∃ j, l j ≠ 1 := by
    by_contra h
    push Not at h
    exact hl1 (funext h)
  have ht : ((l j : Kˣ) : K) ^ 2 ≠ 1 := by
    intro h
    have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
    have h3 : ((l j : K) - 1) ^ 2 = 0 := by linear_combination h + (1 - (l j : K)) * h2
    exact hj (Units.ext (by simpa [sub_eq_zero] using h3))
  have hF : ∀ b ∈ ({l} : Set (Fin τ.rank → Kˣ)), ∃ n : ℕ, b ^ p ^ n = 1 := fun b hb =>
    ⟨1, by rw [pow_one, Set.mem_singleton_iff.mp hb]; exact hl⟩
  have hd : ¬ p ∣ Nat.card (famStabilizerSubgroup ({l} : Set (Fin τ.rank → Kˣ))) :=
    fun h => hW (h.trans (Subgroup.card_subgroup_dvd_card _))
  have hW' : ∃ k, LayerFacts.ggDer (famStabilizerSubgroup ({l} : Set (Fin τ.rank → Kˣ))) k ≤
      famReflectionGroup ({l} : Set (Fin τ.rank → Kˣ)) :=
    ⟨0, famStabilizer_subset_closure_of_coprime hp _ hF hd⟩
  rw [LayerPDivExc.centralizer_singleton_eq_famCentralizer hv] at hL
  exact exists_eq_of_isComponentOf_subCoreFamily
    (LayerPDivExc.isSubCoreFamily_famCentralizer _ ht hW') hL

end Components

section Data

variable {τ : Tag} {K : Type} [Field K]


theorem splitWeyl_component_data [Finite K] [CharP K 2] {p : ℕ} (hp : p.Prime)
    (hW : ¬ p ∣ Nat.card (WeylGroup τ))
    (hfullp : ∀ a : Fin τ.rank → Kˣ, (∀ i, a i ^ p = 1) → rootDiagUnit τ a ∈ torusGroup τ K)
    {v : adjointGroup τ K} (hv : v ∈ TableBExc.torusPow τ K p) (hv1 : v ≠ 1)
    {L : Subgroup (adjointGroup τ K)} (hL : IsComponentOf L (Subgroup.centralizer {v})) :
    TableBExc.torusPow τ K p ≤ Subgroup.normalizer (L : Set (adjointGroup τ K)) ∧
      ∃ Q : Subgroup (adjointGroup τ K), Q ≤ L ∧
        Q ≤ Subgroup.normalizer (TableBExc.torusPow τ K p : Set (adjointGroup τ K)) ∧
          TableBExc.torusPow τ K p ⊓ Subgroup.centralizer (Q : Set (adjointGroup τ K)) ≤
            Subgroup.centralizer (L : Set (adjointGroup τ K)) := by
  obtain ⟨l, hl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hv.1
  have hlp : l ^ p = 1 := by
    refine rootDiagUnit_injective ?_
    rw [← rootDiagUnit_pow, ← hl, rootDiagUnit_one]
    have h := congrArg (fun z : adjointGroup τ K => (z : ModGL τ K)) hv.2
    simpa only [Subgroup.coe_pow, Subgroup.coe_one] using h
  have hl1 : l ≠ 1 := by
    rintro rfl
    apply hv1
    refine Subtype.ext ?_
    rw [hl, rootDiagUnit_one]
    rfl
  obtain ⟨i, rfl⟩ := exists_eq_comap_componentRootSpan hp hW hlp hl1 hl hL
  refine ⟨torusPow_le_normalizer_comap_componentRootSpan _ i p,
    (componentRootSpan K (famChar ({l} : Set (Fin τ.rank → Kˣ))) i).comap
      (adjointGroup τ K).subtype ⊓
        Subgroup.normalizer (TableBExc.torusPow τ K p : Set (adjointGroup τ K)),
    inf_le_left, inf_le_right, ?_⟩
  rintro u ⟨huV, huQ⟩
  obtain ⟨a, ha⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup huV.1
  have hroot : ∀ α ∈ componentRoots (famChar ({l} : Set (Fin τ.rank → Kˣ))) i,
      rootChar a α = 1 := by
    intro α hα
    have hαr := isRoot_of_mem_componentRoots hα
    have hmem := rootWeylOne_mem_componentRootSpan (K := K) hα
    obtain ⟨-, hmon, hmaps⟩ := rootWeylOne_spec (K := K) hαr
    have hnQ : (⟨rootWeylOne τ K α, rootSpan_le_adjointGroup K _ hmem⟩ : adjointGroup τ K) ∈
        (componentRootSpan K (famChar ({l} : Set (Fin τ.rank → Kˣ))) i).comap
          (adjointGroup τ K).subtype ⊓
            Subgroup.normalizer (TableBExc.torusPow τ K p : Set (adjointGroup τ K)) :=
      ⟨hmem, mem_normalizer_torusPow_of_monomial hfullp hmon hmaps⟩
    have hc := congrArg (fun z : adjointGroup τ K => (z : ModGL τ K))
      (Subgroup.mem_centralizer_iff.mp huQ _ hnQ)
    simp only [Subgroup.coe_mul] at hc
    rw [ha] at hc
    exact rootChar_eq_one_of_commute_rootWeylOne hαr hc
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  refine Subtype.ext ?_
  rw [Subgroup.coe_mul, Subgroup.coe_mul, ha]
  exact mem_centralizer_componentRootSpan hroot hy

theorem ggExcSplitWeylAdjAt_of_coprime [Finite K] [CharP K 2] {p : ℕ} (hp : p.Prime)
    (hW : ¬ p ∣ Nat.card (WeylGroup τ))
    (hfullp : ∀ a : Fin τ.rank → Kˣ, (∀ i, a i ^ p = 1) → rootDiagUnit τ a ∈ torusGroup τ K)
    (hdet : IsUnit ((τ.symmetrizedCartan.det : ℤ) : ZMod p)) (hpq : p ∣ Nat.card K - 1) :
    StepTwoSplit.GGExcSplitWeylAdjAt τ K p := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨ζ, hζo⟩ := exists_prime_orderOf_dvd_card' (G := Kˣ) p (by rw [Nat.card_units]; exact hpq)
  exact ⟨coprime_card_ggAutomizer_torusPow hfullp hdet hζo hW,
    fun v hv hv1 L hL => splitWeyl_component_data hp hW hfullp hv hv1 hL⟩

end Data

theorem le_seven_of_dvd_smooth {p : ℕ} (hp : p.Prime) {a b c d : ℕ}
    (h : p ∣ 2 ^ a * 3 ^ b * 5 ^ c * 7 ^ d) : p ≤ 7 := by
  rcases (Nat.Prime.dvd_mul hp).mp h with h | h7
  · rcases (Nat.Prime.dvd_mul hp).mp h with h | h5
    · rcases (Nat.Prime.dvd_mul hp).mp h with h2 | h3
      · have := Nat.le_of_dvd (by norm_num) (hp.dvd_of_dvd_pow h2)
        omega
      · have := Nat.le_of_dvd (by norm_num) (hp.dvd_of_dvd_pow h3)
        omega
    · have := Nat.le_of_dvd (by norm_num) (hp.dvd_of_dvd_pow h5)
      omega
  · have := Nat.le_of_dvd (by norm_num) (hp.dvd_of_dvd_pow h7)
    omega

theorem not_dvd_card_weyl_F4
    {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) : ¬ p ∣ Nat.card (WeylGroup .F4) := by
  rw [CFSG.RankThree.PartOne.K133H.card_weylGroup_F4]
  intro h
  have h' : p ∣ 2 ^ 7 * 3 ^ 2 * 5 ^ 0 * 7 ^ 0 := by norm_num; exact h
  have := le_seven_of_dvd_smooth hp h'
  rcases (show p = 5 ∨ p = 7 by
    interval_cases p <;> first | (left; rfl) | (right; rfl) | exact absurd hp (by norm_num))
    with rfl | rfl <;> norm_num at h

theorem not_dvd_card_weyl_E7
    {p : ℕ} (hp : p.Prime) (hp11 : 11 ≤ p) :
    ¬ p ∣ Nat.card (WeylGroup .E7) := by
  rw [NoOffExc.card_weyl_E7]
  intro h
  have h' : p ∣ 2 ^ 10 * 3 ^ 4 * 5 ^ 1 * 7 ^ 1 := by norm_num; exact h
  have := le_seven_of_dvd_smooth hp h'
  omega

theorem not_dvd_card_weyl_E8
    {p : ℕ} (hp : p.Prime) (hp11 : 11 ≤ p) :
    ¬ p ∣ Nat.card (WeylGroup .E8) := by
  rw [NoOffExc.card_weyl_E8]
  intro h
  have h' : p ∣ 2 ^ 14 * 3 ^ 5 * 5 ^ 2 * 7 ^ 1 := by norm_num; exact h
  have := le_seven_of_dvd_smooth hp h'
  omega

theorem le_five_of_dvd_smooth {p : ℕ} (hp : p.Prime) {a b c : ℕ}
    (h : p ∣ 2 ^ a * 3 ^ b * 5 ^ c) : p ≤ 5 := by
  rcases (Nat.Prime.dvd_mul hp).mp h with h | h5
  · rcases (Nat.Prime.dvd_mul hp).mp h with h2 | h3
    · have := Nat.le_of_dvd (by norm_num) (hp.dvd_of_dvd_pow h2)
      omega
    · have := Nat.le_of_dvd (by norm_num) (hp.dvd_of_dvd_pow h3)
      omega
  · have := Nat.le_of_dvd (by norm_num) (hp.dvd_of_dvd_pow h5)
    omega

theorem not_dvd_card_weyl_E6
    {p : ℕ} (hp : p.Prime) (hp7 : 7 ≤ p) : ¬ p ∣ Nat.card (WeylGroup .E6) := by
  rw [NoOffExc.card_weyl_E6]
  intro h
  have h' : p ∣ 2 ^ 7 * 3 ^ 4 * 5 ^ 1 := by norm_num; exact h
  have := le_five_of_dvd_smooth hp h'
  omega

theorem det_symmetrizedCartan_E6 : Tag.E6.symmetrizedCartan.det = 3 := by
  rw [Tag.symmetrizedCartan, Matrix.det_mul, det_cartan_E6]
  change (1 : Matrix (Fin 6) (Fin 6) ℤ).det * 3 = 3
  rw [Matrix.det_one, one_mul]

theorem isUnit_det_symmetrizedCartan_E6 {p : ℕ} [Fact p.Prime] (hp3 : p ≠ 3) :
    IsUnit ((Tag.E6.symmetrizedCartan.det : ℤ) : ZMod p) := by
  rw [det_symmetrizedCartan_E6, isUnit_iff_ne_zero, Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]
  intro h
  have h' : p ∣ 3 := by exact_mod_cast h
  exact hp3 ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_three).1 h')

section Tags


theorem ggExcSplitWeylF4Input_holds : GGExcSplitWeylF4Input := by
  intro K _ _ _ p hp hp5 hpq
  have : Fact p.Prime := ⟨hp⟩
  exact ggExcSplitWeylAdjAt_of_coprime hp (not_dvd_card_weyl_F4 hp hp5)
    (fun a _ => CFSG.RankThree.Chevalley.F4_rootDiagUnit_mem_torusGroup a)
    (ExcFrames.isUnit_det_symmetrizedCartan (Or.inl rfl) (by omega)) hpq

theorem ggExcSplitWeylE8Input_holds : GGExcSplitWeylE8Input := by
  intro K _ _ _ p hp hp11 hpq
  have : Fact p.Prime := ⟨hp⟩
  exact ggExcSplitWeylAdjAt_of_coprime hp (not_dvd_card_weyl_E8 hp hp11)
    (fun a _ => TableBExc.full_of_E7_E8 (Or.inr rfl) a)
    (ExcFrames.isUnit_det_symmetrizedCartan (Or.inr (Or.inr rfl)) (by omega)) hpq

theorem ggExcSplitWeylAdjAt_E7 {K : Type} [Field K] [Finite K] [CharP K 2] {p : ℕ}
    (hp : p.Prime) (hp11 : 11 ≤ p) (hpq : p ∣ Nat.card K - 1) :
    StepTwoSplit.GGExcSplitWeylAdjAt .E7 K p := by
  have : Fact p.Prime := ⟨hp⟩
  exact ggExcSplitWeylAdjAt_of_coprime hp (not_dvd_card_weyl_E7 hp hp11)
    (fun a _ => TableBExc.full_of_E7_E8 (Or.inl rfl) a)
    (ExcFrames.isUnit_det_symmetrizedCartan (Or.inr (Or.inl rfl)) (by omega)) hpq

theorem ggExcSplitWeylAdjAt_E6 {K : Type} [Field K] [Finite K] [CharP K 2] {p : ℕ}
    (hp : p.Prime) (hp7 : 7 ≤ p) (hpq : p ∣ Nat.card K - 1) :
    StepTwoSplit.GGExcSplitWeylAdjAt .E6 K p := by
  have : Fact p.Prime := ⟨hp⟩
  have hp3 : Nat.Coprime 3 p := (Nat.coprime_primes Nat.prime_three hp).2 (by omega)
  exact ggExcSplitWeylAdjAt_of_coprime hp (not_dvd_card_weyl_E6 hp hp7)
    (fun a ha => TableBExc.fullp_E6 hp.one_lt hp3 a ha)
    (isUnit_det_symmetrizedCartan_E6 (by omega)) hpq

end Tags

end StepTwoToralExc

end CFSG.StandardType
