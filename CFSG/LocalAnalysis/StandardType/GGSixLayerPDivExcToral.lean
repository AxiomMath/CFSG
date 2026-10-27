module

public import CFSG.LocalAnalysis.StandardType.GGSixLayerFactsExcSixEToral
public import CFSG.LocalAnalysis.StandardType.GGSixLayerPDivOmega
public import CFSG.LocalAnalysis.StandardType.GGWeylFamQuotSolvAll
public import CFSG.LieType.Chevalley.G2FieldFourEvenSimplePairs

public section

namespace CFSG.StandardType

namespace LayerPDivExc

open CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.RankThree.PartOne.KE8F LayerExc LayerSixE

section Group

theorem exists_eq_of_isComponentOf_of_subCoreFamily {L : Type} [Group L] [Finite L]
    {H : Subgroup L} {β : Type} {S : β → Subgroup L} (hS : LayerCores.IsSubCoreFamily H S)
    {X : Subgroup L} (hX : IsComponentOf X H) : ∃ c, X = S c := by
  have hmap : H.map (MonoidHom.id L) = H := Subgroup.map_id H
  obtain ⟨c, hc⟩ := LayerPDiv.exists_eq_map_of_isComponentOf_sub (MonoidHom.id L)
    (by rw [MonoidHom.ker_id]; exact bot_le) hmap.le
    (by rw [hmap, Subgroup.subgroupOf_self]; infer_instance)
    (by rw [hmap]; exact Subgroup.commutator_le_self H) hS hX
  exact ⟨c, by rw [hc, Subgroup.map_id]⟩

theorem dvd_card_of_isComponentOf_of_subCoreFamily {L : Type} [Group L] [Finite L]
    {H : Subgroup L} {β : Type} {S : β → Subgroup L} (hS : LayerCores.IsSubCoreFamily H S)
    {p : ℕ} (hp : ∀ c, p ∣ Nat.card (S c)) {X : Subgroup L} (hX : IsComponentOf X H) :
    p ∣ Nat.card X := by
  obtain ⟨c, rfl⟩ := exists_eq_of_isComponentOf_of_subCoreFamily hS hX
  exact hp c

theorem isSubCoreFamily_top {L : Type} [Group L] (hL : CFSG.IsQuasisimple L)
    (hZ : Subgroup.center L = ⊥) :
    LayerCores.IsSubCoreFamily (⊤ : Subgroup L) (fun _ : Unit => ⊤) := by
  refine ⟨fun _ => le_rfl, fun _ => IsSubnormal.refl _, fun _ => ?_, ⟨0, ?_⟩, ?_⟩
  · exact CFSG.LocalCores.isQuasisimple_of_mulEquiv Subgroup.topEquiv.symm hL
  · rw [LayerFacts.ggDer_zero]
    exact le_iSup (fun _ : Unit => (⊤ : Subgroup L)) ()
  · intro z _ hz _
    have hzZ : z ∈ Subgroup.center L :=
      Subgroup.mem_center_iff.mpr fun y => (hz y (Subgroup.mem_iSup_of_mem () trivial)).symm
    rw [hZ, Subgroup.mem_bot] at hzZ
    exact hzZ

theorem isComponentOf_map {G G' : Type*} [Group G] [Group G'] {f : G →* G'}
    (hf : Function.Injective f) {X H : Subgroup G} (h : IsComponentOf X H) :
    IsComponentOf (X.map f) (H.map f) :=
  ⟨Subgroup.map_mono h.1, LayerCores.ggSubnormal_map f h.2.1,
    (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native _).mpr
      (CFSG.LocalCores.isQuasisimple_of_mulEquiv (X.equivMapOfInjective f hf)
        ((CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native _).mp
          h.2.2))⟩

theorem isComponentOf_comap {G G' : Type*} [Group G] [Group G'] {f : G →* G'}
    (hf : Function.Injective f) {K : Subgroup G'} {H : Subgroup G}
    (h : IsComponentOf K (H.map f)) : IsComponentOf (K.comap f) H := by
  have hKr : K ≤ f.range := h.1.trans (Subgroup.map_le_range f H)
  have hKeq : (K.comap f).map f = K := Subgroup.map_comap_eq_self hKr
  have hsn := LayerCores.ggSubnormal_comap f h.2.1
  rw [Subgroup.comap_map_eq_self_of_injective hf] at hsn
  refine ⟨LayerCores.ggSubnormal_le hsn, hsn,
    (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native _).mpr ?_⟩
  exact CFSG.LocalCores.isQuasisimple_of_mulEquiv
    (((K.comap f).equivMapOfInjective f hf).trans (MulEquiv.subgroupCongr hKeq)).symm
    ((CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native _).mp h.2.2)

theorem map_centralizer_singleton {L L' : Type*} [Group L] [Group L'] (e : L ≃* L') (a : L) :
    (Subgroup.centralizer {a}).map e.toMonoidHom = Subgroup.centralizer {e a} := by
  ext x
  simp only [Subgroup.mem_map, Subgroup.mem_centralizer_iff, Set.mem_singleton_iff, forall_eq,
    MulEquiv.coe_toMonoidHom]
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [← map_mul, ← map_mul, hy]
  · intro hx
    refine ⟨e.symm x, e.injective ?_, e.apply_symm_apply x⟩
    rw [map_mul, map_mul, e.apply_symm_apply, hx]

theorem dvd_card_of_isComponentOf_of_mulEquiv {L L' : Type*} [Group L] [Group L'] (e : L ≃* L')
    {p : ℕ} {a : L}
    (h : ∀ X : Subgroup L', IsComponentOf X (Subgroup.centralizer {e a}) → p ∣ Nat.card X)
    {X : Subgroup L} (hX : IsComponentOf X (Subgroup.centralizer {a})) : p ∣ Nat.card X := by
  have hX' := isComponentOf_map (f := e.toMonoidHom) e.injective hX
  rw [map_centralizer_singleton] at hX'
  rw [← Subgroup.card_map_of_injective (f := e.toMonoidHom) e.injective]
  exact h _ hX'

end Group

section Orders


variable {τ : Tag} {K : Type} [Field K]

theorem exists_mem_componentRootSpan_torusGroup_orderOf {M : Type*} [CommGroup M]
    {χ : Multiplicative (Fin τ.rank → ℤ) →* M} {ζ : Kˣ} (hζ : Odd (orderOf ζ))
    (i : KernelComponent χ) :
    ∃ h ∈ componentRootSpan K χ i, h ∈ torusGroup τ K ∧ orderOf h = orderOf ζ := by
  obtain ⟨⟨α, hα⟩, rfl⟩ := Quotient.exists_rep i
  have hαΨ : α ∈ componentRoots χ ⟦⟨α, hα⟩⟧ := ⟨hα, rfl⟩
  have hαr := isRoot_of_mem_componentRoots hαΨ
  obtain ⟨w, k, hwk⟩ := isRoot_iff_exists_smul_single.1 hαr
  have hhT := canonicalRep_conj_torusElt_mem (K := K) (by rw [hwk]; exact hαΨ) ζ
  have hm : ∑ l, τ.cartan k l * (w⁻¹ • α) l = 2 := by
    rw [← corootPair_smul_single, hwk, corootPair]
    exact Int.mul_ediv_cancel _ (iform_self_pos_of_isRoot hαr).ne'
  set h := canonicalRep (coxeterSystem τ) K w * torusElt τ K k ζ *
    (canonicalRep (coxeterSystem τ) K w)⁻¹ with hh_def
  have hh : h ∈ componentRootSpan K χ ⟦⟨α, hα⟩⟧ :=
    componentTorus_le_componentRootSpan K χ _ hhT
  have hmemT : h ∈ torusGroup τ K := componentTorus_le_torusGroup K χ _ hhT
  have hconj1 : ∀ d, h * pinnedX τ K α d * h⁻¹ = pinnedX τ K α (((ζ ^ 2 : Kˣ) : K) * d) :=
    fun d => by
      rw [hh_def, canonicalRep_conj_torusElt_conj_pinnedX w k ζ hαr d, hm]
      norm_cast
  have hconj : ∀ (n : ℕ) (d : K),
      h ^ n * pinnedX τ K α d * (h ^ n)⁻¹ = pinnedX τ K α ((((ζ ^ 2) ^ n : Kˣ) : K) * d) := by
    intro n
    induction n with
    | zero => intro d; simp
    | succ n ih =>
      intro d
      calc h ^ (n + 1) * pinnedX τ K α d * (h ^ (n + 1))⁻¹ =
            h ^ n * (h * pinnedX τ K α d * h⁻¹) * (h ^ n)⁻¹ := by group
        _ = pinnedX τ K α ((((ζ ^ 2) ^ (n + 1) : Kˣ) : K) * d) := by
          rw [hconj1, ih]
          congr 1
          push_cast
          ring
  have hdvd1 : orderOf h ∣ orderOf ζ := by
    rw [hh_def, ← SemiconjBy.orderOf_eq _ (SemiconjBy.conj_mk _ _)]
    exact orderOf_map_dvd (torusEltHom τ K k) ζ
  have hsq : orderOf (ζ ^ 2) = orderOf ζ := hζ.coprime_two_right.orderOf_pow
  have hdvd2 : orderOf (ζ ^ 2) ∣ orderOf h := by
    refine orderOf_dvd_of_pow_eq_one (Units.ext ?_)
    have h1 := hconj (orderOf h) 1
    rw [pow_orderOf_eq_one, one_mul, inv_one, mul_one, mul_one] at h1
    have h2 := pinnedX_injective τ K α h1
    rw [Units.val_one]
    exact h2.symm
  refine ⟨h, hh, hmemT, Nat.dvd_antisymm hdvd1 ?_⟩
  rw [← hsq]
  exact hdvd2

theorem dvd_card_componentRootSpan {M : Type*} [CommGroup M]
    {χ : Multiplicative (Fin τ.rank → ℤ) →* M} {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {ζ : Kˣ}
    (hζ : orderOf ζ = p) (i : KernelComponent χ) :
    p ∣ Nat.card (componentRootSpan K χ i) := by
  have hodd : Odd (orderOf ζ) := hζ.symm ▸ hp.odd_of_ne_two hp2
  obtain ⟨h, hh, -, hord⟩ := exists_mem_componentRootSpan_torusGroup_orderOf hodd i
  rw [← hζ, ← hord]
  exact Subgroup.orderOf_dvd_natCard _ hh

theorem dvd_card_adjointGroup [Finite K] [CharP K 2] {p : ℕ} (hpK : p ∣ Nat.card K ^ 2 - 1) :
    p ∣ Nat.card (adjointGroup τ K) := by
  have hinj := rankOneRep_injective_of_charTwo (τ := τ) (K := K) ⟨0, τ.rank_pos⟩
  have h := Subgroup.card_subgroup_dvd_card (rankOneRep τ K ⟨0, τ.rank_pos⟩).range
  rw [← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv] at h
  exact hpK.trans ((LayerPDiv.sq_sub_one_dvd_card_SL (D := K) (d := 2) le_rfl).trans h)

end Orders

section Toral


variable {τ : Tag} {K : Type} [Field K]

theorem isSubCoreFamily_famCentralizer [Finite K] [CharP K 2] (F : Set (Fin τ.rank → Kˣ))
    {t : Kˣ} (ht : (t : K) ^ 2 ≠ 1)
    (hW : ∃ k, LayerFacts.ggDer (famStabilizerSubgroup F) k ≤ famReflectionGroup F) :
    LayerCores.IsSubCoreFamily (famCentralizer F)
      (fun i => (componentRootSpan K (famChar F) i).comap (adjointGroup τ K).subtype) := by
  classical
  obtain ⟨k, hk⟩ := hW
  have hHQM := torus_sup_rootSpan_le_map_famCentralizer (K := K) F
  have hYN := map_famWeylReps_le_normalizer (K := K) F
  have hMle := map_famCentralizer_le_sup (K := K) F
  have hMN : (famCentralizer F).map (adjointGroup τ K).subtype ≤ Subgroup.normalizer
      ((torusGroup τ K ⊔ rootSpan τ K (famKernel F) : Subgroup (ModGL τ K)) :
        Set (ModGL τ K)) :=
    hMle.trans (sup_le Subgroup.le_normalizer hYN)
  have hder : LayerFacts.ggDer ((famCentralizer F).map (adjointGroup τ K).subtype) (k + 1) ≤
      rootSpan τ K (famKernel F) := by
    rw [LayerFacts.ggDer_succ]
    have h1 := (LayerFacts.ggDer_mono hMle k).trans ((ggDer_sup_le_of_le_normalizer hYN k).trans
      (sup_le le_rfl (ggDer_map_famWeylReps_le hk)))
    exact (Subgroup.commutator_mono h1 h1).trans
      (commutator_torus_sup_rootSpan_le fun α hα => hα.1)
  have hsup : ⨆ i, componentRootSpan K (famChar F) i = rootSpan τ K (famKernel F) := by
    rw [iSup_componentRootSpan, kernelRoots_famChar]
  have hfam := isSubCoreFamily_of_le_of_normal (isSubCoreFamily_torus_sup_rootSpan F ht) hHQM
    (fun u hu s hs => (Subgroup.mem_normalizer_iff.1 (hMN hu) s).1 hs)
    ⟨k + 1, by rw [hsup]; exact hder⟩
  have h := hfam.comap (adjointGroup τ K).subtype (adjointGroup τ K).subtype_injective (by
    rintro _ ⟨g, -, rfl⟩
    exact ⟨g, rfl⟩)
  rwa [Subgroup.comap_map_eq_self_of_injective (adjointGroup τ K).subtype_injective] at h

theorem dvd_card_of_isComponentOf_famCentralizer [Finite K] [CharP K 2]
    (hq : CFSG.IsQuasisimple (adjointGroup τ K)) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpK : p ∣ Nat.card K ^ 2 - 1) (F : Set (Fin τ.rank → Kˣ)) (hF : ∀ a ∈ F, a ^ p = 1)
    (hW : p ∣ Nat.card (famStabilizerSubgroup F) →
      ∃ k, LayerFacts.ggDer (famStabilizerSubgroup F) k ≤ famReflectionGroup F)
    {X : Subgroup (adjointGroup τ K)} (hX : IsComponentOf X (famCentralizer F)) :
    p ∣ Nat.card X := by
  by_cases hF1 : ∃ a ∈ F, a ≠ 1
  · obtain ⟨a, haF, ha1⟩ := hF1
    obtain ⟨j, hj⟩ : ∃ j, a j ≠ 1 := by
      by_contra h
      push Not at h
      exact ha1 (funext h)
    have hζp : a j ^ p = 1 := by
      have h := congrFun (hF a haF) j
      simpa only [Pi.pow_apply, Pi.one_apply] using h
    have hζ : orderOf (a j) = p := by
      have : Fact p.Prime := ⟨hp⟩
      exact orderOf_eq_prime hζp hj
    have ht : ((a j : Kˣ) : K) ^ 2 ≠ 1 := by
      intro h
      have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
      have h3 : ((a j : K) - 1) ^ 2 = 0 := by linear_combination h + (1 - (a j : K)) * h2
      exact hj (Units.ext (by simpa [sub_eq_zero] using h3))
    have hW' : ∃ k, LayerFacts.ggDer (famStabilizerSubgroup F) k ≤ famReflectionGroup F := by
      by_cases hd : p ∣ Nat.card (famStabilizerSubgroup F)
      · exact hW hd
      · exact ⟨0, famStabilizer_subset_closure_of_coprime hp F
          (fun b hb => ⟨1, by rw [pow_one]; exact hF b hb⟩) hd⟩
    refine dvd_card_of_isComponentOf_of_subCoreFamily (isSubCoreFamily_famCentralizer F ht hW')
      (fun i => ?_) hX
    rw [LayerPDiv.card_comap_of_le_range (adjointGroup τ K).subtype_injective (by
      rw [Subgroup.range_subtype]
      exact rootSpan_le_adjointGroup K _)]
    exact dvd_card_componentRootSpan hp hp2 hζ i
  · push Not at hF1
    have htop : famCentralizer F = ⊤ := by
      rw [eq_top_iff]
      intro g _ a ha
      rw [hF1 a ha, rootDiagUnit_one, one_mul, inv_one, mul_one]
    rw [htop] at hX
    refine dvd_card_of_isComponentOf_of_subCoreFamily (isSubCoreFamily_top hq
      center_adjointGroup_eq_bot) (fun _ => ?_) hX
    rw [Subgroup.card_top]
    exact dvd_card_adjointGroup hpK

theorem centralizer_singleton_eq_famCentralizer {b : adjointGroup τ K}
    {l : Fin τ.rank → Kˣ} (hb : (b : ModGL τ K) = rootDiagUnit τ l) :
    Subgroup.centralizer {b} = famCentralizer {l} := by
  ext g
  simp only [Subgroup.mem_centralizer_iff, Set.mem_singleton_iff, forall_eq, mem_famCentralizer]
  constructor
  · intro h
    have h' := congrArg (fun z : adjointGroup τ K => (z : ModGL τ K)) h
    simp only [Subgroup.coe_mul, hb] at h'
    rw [h', mul_inv_cancel_right]
  · intro h
    refine Subtype.ext ?_
    simp only [Subgroup.coe_mul, hb]
    calc rootDiagUnit τ l * (g : ModGL τ K) =
          rootDiagUnit τ l * g * (rootDiagUnit τ l)⁻¹ * rootDiagUnit τ l := by group
      _ = g * rootDiagUnit τ l := by rw [h]

theorem dvd_card_of_isComponentOf_centralizer_toral [Finite K] [CharP K 2]
    (hq : CFSG.IsQuasisimple (adjointGroup τ K)) (hWq : GGWeylFamQuotSolvInput τ) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hpK : p ∣ Nat.card K ^ 2 - 1) {a : adjointGroup τ K}
    (ha : a ^ p = 1) (ht : GGExcToral τ K (Subgroup.zpowers a)) {X : Subgroup (adjointGroup τ K)}
    (hX : IsComponentOf X (Subgroup.centralizer {a})) : p ∣ Nat.card X := by
  obtain ⟨g, hg⟩ := ht
  obtain ⟨l, hl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup (hg a (Subgroup.mem_zpowers a))
  have hlp : l ^ p = 1 := pow_eq_one_of_coe_eq_rootDiagUnit hl
    (by rw [conj_pow, ha, mul_one, mul_inv_cancel])
  have hX' := isComponentOf_map (f := (MulAut.conj g).toMonoidHom) (MulAut.conj g).injective hX
  rw [map_centralizer_singleton, MulAut.conj_apply,
    centralizer_singleton_eq_famCentralizer hl] at hX'
  rw [← Subgroup.card_map_of_injective (f := (MulAut.conj g).toMonoidHom)
    (MulAut.conj g).injective]
  have hF : ∀ b ∈ ({l} : Set (Fin τ.rank → Kˣ)), b ^ p = 1 := fun b hb => by
    rw [Set.mem_singleton_iff.mp hb]
    exact hlp
  exact dvd_card_of_isComponentOf_famCentralizer hq hp hp2 hpK {l} hF
    (fun hd => hWq K p hp hp2 {l} (fun b hb => ⟨1, by rw [pow_one]; exact hF b hb⟩) hd) hX'

theorem exists_mem_torusGroup_orderOf_of_isComponentOf [Finite K] [CharP K 2] {p n : ℕ}
    (hp : p.Prime) {b : adjointGroup τ K} (hb : (b : ModGL τ K) ∈ torusGroup τ K)
    (hbp : b ^ p ^ n = 1) {X : Subgroup (adjointGroup τ K)}
    (hX : IsComponentOf X (Subgroup.centralizer {b})) {ζ : Kˣ} (hζ : Odd (orderOf ζ)) :
    ∃ s ∈ X, (s : ModGL τ K) ∈ torusGroup τ K ∧ orderOf s = orderOf ζ := by
  by_cases h1 : orderOf ζ = 1
  · refine ⟨1, X.one_mem, (torusGroup τ K).one_mem, ?_⟩
    rw [orderOf_one, h1]
  · have ht : ((ζ : K) ^ 2) ≠ 1 := fun h => h1 <| by
      rw [← hζ.coprime_two_right.orderOf_pow, show ζ ^ 2 = 1 from Units.ext (by simpa using h),
        orderOf_one]
    obtain ⟨l, hl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hb
    have hlp : l ^ p ^ n = 1 := pow_eq_one_of_coe_eq_rootDiagUnit hl hbp
    have hF : ∀ a ∈ ({l} : Set (Fin τ.rank → Kˣ)), ∃ m : ℕ, a ^ p ^ m = 1 :=
      fun a ha => ⟨n, by rw [Set.mem_singleton_iff.mp ha]; exact hlp⟩
    have hW := LayerExc.exists_ggDer_famStabilizerSubgroup_le_reflection hp {l} hF
    rw [centralizer_singleton_eq_famCentralizer hl] at hX
    obtain ⟨i, rfl⟩ := exists_eq_of_isComponentOf_of_subCoreFamily
      (isSubCoreFamily_famCentralizer {l} (t := ζ) ht hW) hX
    obtain ⟨h, hh, hht, hord⟩ := exists_mem_componentRootSpan_torusGroup_orderOf hζ i
    let t : adjointGroup τ K := ⟨h, rootSpan_le_adjointGroup K _ hh⟩
    refine ⟨t, hh, hht, ?_⟩
    exact (Subgroup.orderOf_mk h _).trans hord

theorem dvd_card_of_isComponentOf_autFix_toral [Finite K] [CharP K 2]
    (hq : CFSG.IsQuasisimple (adjointGroup τ K)) (hWq : GGWeylFamQuotSolvInput τ) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hpK : p ∣ Nat.card K ^ 2 - 1)
    {A : Subgroup (MulAut (adjointGroup τ K))} (hA : ∀ α ∈ A, α ^ p = 1)
    (ht : GGInndiagToral τ K A) {X : Subgroup (adjointGroup τ K)}
    (hX : IsComponentOf X (autFix A)) : p ∣ Nat.card X := by
  obtain ⟨c, hc⟩ := ht
  rw [autFix_eq_comap_famCentralizer A c hc] at hX
  have hX' := isComponentOf_map (f := (MulAut.conj c).toMonoidHom) (MulAut.conj c).injective hX
  rw [Subgroup.map_comap_eq_self_of_surjective (MulAut.conj c).surjective] at hX'
  have hF : ∀ a ∈ conjTuples A c, a ^ p = 1 := by
    rintro a ⟨α, hα, hαa⟩
    refine rootDiagAutHom_injective ?_
    rw [map_pow, hαa, map_one, conj_pow, hA α hα, mul_one, mul_inv_cancel]
  rw [← Subgroup.card_map_of_injective (f := (MulAut.conj c).toMonoidHom)
    (MulAut.conj c).injective]
  exact dvd_card_of_isComponentOf_famCentralizer hq hp hp2 hpK _ hF
    (fun hd => hWq K p hp hp2 _ (fun a ha => ⟨1, by rw [pow_one]; exact hF a ha⟩) hd) hX'

end Toral

end LayerPDivExc

end CFSG.StandardType
