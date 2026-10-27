module

public import CFSG.LocalAnalysis.StandardType.GGLayerCenterCyclicRootCartan
public import CFSG.LocalAnalysis.StandardType.GGLayerCenterCyclicModelToral
public import CFSG.HardMathSupport.Timmesfeld.RootAut.Count

public section

namespace CFSG.StandardType

namespace LayerCycRoot

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint

variable {τ : Tag}

section Coroot


theorem corootPair_sub_smul {δ : Fin τ.rank → ℤ} (hδ : IsRoot τ δ) (u w : Fin τ.rank → ℤ)
    (c : ℤ) : corootPair δ (u - c • w) = corootPair δ u - c * corootPair δ w := by
  have hp := iform_self_pos_of_isRoot hδ
  apply mul_right_cancel₀ hp.ne'
  rw [corootPair_mul hδ, sub_mul, mul_assoc, corootPair_mul hδ, corootPair_mul hδ,
    iform_sub_right, iform_smul_right]
  ring

theorem corootPair_smul_smul (w : WeylGroup τ) (δ v : Fin τ.rank → ℤ) :
    corootPair (w • δ) (w • v) = corootPair δ v := by
  simp only [corootPair, iform_smul]

theorem corootPair_rootReflection_smul {β δ : Fin τ.rank → ℤ} (hβ : IsRoot τ β)
    (hδ : IsRoot τ δ) (v : Fin τ.rank → ℤ) :
    corootPair (rootReflection β • δ) v = corootPair δ v - corootPair β v * corootPair δ β := by
  have h1 : v = rootReflection β • (rootReflection β • v) := by
    rw [← mul_smul, rootReflection_mul_self hβ, one_smul]
  conv_lhs => rw [h1]
  rw [corootPair_smul_smul, rootReflection_smul hβ, corootPair_sub_smul hδ]

variable {Ψ : Set (Fin τ.rank → ℤ)}

theorem exists_corootPair_rootReflection_smul {β : Fin τ.rank → ℤ} (hβ : β ∈ simpleRoots Ψ)
    {δ : Fin τ.rank → ℤ} (hδ : IsRoot τ δ) {c : simpleRoots Ψ → ℤ}
    (hc : ∀ v, corootPair δ v = ∑ γ, c γ * corootPair (γ : Fin τ.rank → ℤ) v) :
    ∃ c' : simpleRoots Ψ → ℤ, ∀ v, corootPair (rootReflection β • δ) v =
      ∑ γ, c' γ * corootPair (γ : Fin τ.rank → ℤ) v := by
  classical
  refine ⟨c - Pi.single ⟨β, hβ⟩ (corootPair δ β), fun v => ?_⟩
  rw [corootPair_rootReflection_smul (simpleRoots_isRoot hβ) hδ, hc v]
  simp only [Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]
  congr 1
  rw [Finset.sum_eq_single ⟨β, hβ⟩ (fun γ _ hγ => by rw [Pi.single_eq_of_ne hγ, zero_mul])
    (fun h => absurd (Finset.mem_univ _) h), Pi.single_eq_same, mul_comm]

theorem exists_corootPair_eq_sum_of_mem {u : WeylGroup τ} (hu : u ∈ componentWeylGroup Ψ)
    {β' : Fin τ.rank → ℤ} (hβ' : β' ∈ simpleRoots Ψ) :
    ∃ c : simpleRoots Ψ → ℤ, ∀ v, corootPair (u • β') v =
      ∑ γ, c γ * corootPair (γ : Fin τ.rank → ℤ) v := by
  classical
  induction hu using Subgroup.closure_induction_left with
  | one =>
    refine ⟨Pi.single ⟨β', hβ'⟩ 1, fun v => ?_⟩
    rw [one_smul, Finset.sum_eq_single ⟨β', hβ'⟩
      (fun γ _ hγ => by rw [Pi.single_eq_of_ne hγ, zero_mul])
      (fun h => absurd (Finset.mem_univ _) h), Pi.single_eq_same, one_mul]
  | mul_left x hx y hy ih =>
    obtain ⟨β, hβ, rfl⟩ := hx
    obtain ⟨c, hc⟩ := ih
    rw [mul_smul]
    exact exists_corootPair_rootReflection_smul hβ (IsRoot.smul (simpleRoots_isRoot hβ') y) hc
  | inv_mul_cancel x hx y hy ih =>
    obtain ⟨β, hβ, rfl⟩ := hx
    obtain ⟨c, hc⟩ := ih
    rw [rootReflection_inv (simpleRoots_isRoot hβ), mul_smul]
    exact exists_corootPair_rootReflection_smul hβ (IsRoot.smul (simpleRoots_isRoot hβ') y) hc

theorem exists_corootPair_eq_sum (hΨ : IsRootComponent Ψ) {γ : Fin τ.rank → ℤ} (hγ : γ ∈ Ψ) :
    ∃ c : simpleRoots Ψ → ℤ, ∀ v, corootPair γ v =
      ∑ β, c β * corootPair (β : Fin τ.rank → ℤ) v := by
  obtain ⟨u, hu, β', hβ', rfl⟩ := exists_smul_simpleRoot hΨ hγ
  exact exists_corootPair_eq_sum_of_mem hu hβ'

theorem corootPair_eq_sum_single {β : Fin τ.rank → ℤ} (hβ : IsRoot τ β) (v : Fin τ.rank → ℤ) :
    corootPair β v = ∑ j, v j * corootPair β (Pi.single j 1) := by
  have hv : v = ∑ j, v j • (Pi.single j 1 : Fin τ.rank → ℤ) := by
    funext k
    simp [Finset.sum_apply, Pi.single_apply]
  conv_lhs => rw [hv]
  exact CFSG.HardMathSupport.Timmesfeld.RootAut.corootPair_sum hβ _ _ _

end Coroot

section Torus

open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

variable (K : Type) [Field K]

@[expose] noncomputable def torusDiagHom :
    (Fin τ.rank → Kˣ) →* (Module.End K (RootModule τ K))ˣ where
  toFun := rootDiagUnit τ
  map_one' := rootDiagUnit_one
  map_mul' := rootDiagUnit_mul

variable {K} (Ψ : Set (Fin τ.rank → ℤ))

@[expose] noncomputable def simpleCorootHom : (simpleRoots Ψ → Kˣ) →* (Fin τ.rank → Kˣ) where
  toFun x j := ∏ β, x β ^ corootPair (β : Fin τ.rank → ℤ) (Pi.single j 1)
  map_one' := by funext j; simp
  map_mul' x y := by funext j; simp [mul_zpow, Finset.prod_mul_distrib]

@[expose] noncomputable def cartanHom : (simpleRoots Ψ → Kˣ) →* (simpleRoots Ψ → Kˣ) where
  toFun x α := ∏ β, x β ^ corootPair (β : Fin τ.rank → ℤ) α
  map_one' := by funext α; simp
  map_mul' x y := by funext α; simp [mul_zpow, Finset.prod_mul_distrib]

theorem simpleCorootHom_apply (x : simpleRoots Ψ → Kˣ) (j : Fin τ.rank) :
    simpleCorootHom Ψ x j = ∏ β, x β ^ corootPair (β : Fin τ.rank → ℤ) (Pi.single j 1) := rfl

theorem cartanHom_apply (x : simpleRoots Ψ → Kˣ) (α : simpleRoots Ψ) :
    cartanHom Ψ x α = ∏ β, x β ^ corootPair (β : Fin τ.rank → ℤ) α := rfl

theorem rootChar_simpleCorootHom
    (x : simpleRoots Ψ → Kˣ) (v : Fin τ.rank → ℤ) :
    rootChar (simpleCorootHom Ψ x) v = ∏ β, x β ^ corootPair (β : Fin τ.rank → ℤ) v := by
  have hβ : ∀ β : simpleRoots Ψ, corootPair (β : Fin τ.rank → ℤ) v =
      ∑ j, corootPair (β : Fin τ.rank → ℤ) (Pi.single j 1) * v j := fun β => by
    rw [corootPair_eq_sum_single (simpleRoots_isRoot β.2)]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  calc rootChar (simpleCorootHom Ψ x) v
      = ∏ j, ∏ β, x β ^ (corootPair (β : Fin τ.rank → ℤ) (Pi.single j 1) * v j) := by
        simp only [rootChar, simpleCorootHom_apply, ← Finset.prod_zpow, zpow_mul]
    _ = ∏ β, ∏ j, x β ^ (corootPair (β : Fin τ.rank → ℤ) (Pi.single j 1) * v j) :=
        Finset.prod_comm
    _ = ∏ β, x β ^ corootPair (β : Fin τ.rank → ℤ) v := by
        simp only [LayerCycCoroot.prod_zpow_eq_zpow_sum, hβ]

end Torus

section Center

open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley LayerCycCoroot


variable {K : Type} [Field K] {M : Type*} [CommGroup M]
  {χ : Multiplicative (Fin τ.rank → ℤ) →* M}

theorem componentCorootTorus_le_range (i : KernelComponent χ) :
    componentCorootTorus K χ i ≤
      ((torusDiagHom K).comp (simpleCorootHom (componentRoots χ i))).range := by
  refine (Subgroup.closure_le _).2 ?_
  rintro _ ⟨w, k, t, hw, rfl⟩
  obtain ⟨c, hc⟩ := exists_corootPair_eq_sum (isRootComponent_componentRoots i) hw
  have hx : canonicalRep (coxeterSystem τ) K w * torusElt τ K k t *
      (canonicalRep (coxeterSystem τ) K w)⁻¹ ∈ torusGroup τ K :=
    componentTorus_le_torusGroup K χ i (canonicalRep_conj_torusElt_mem hw t)
  have hfun : simpleCorootHom (componentRoots χ i) (fun β => t ^ c β) = torusTuple ⟨_, hx⟩ := by
    funext j
    rw [torusTuple_corootElt w k t hx j, hc, simpleCorootHom_apply]
    simp only [← zpow_mul, LayerCycCoroot.prod_zpow_eq_zpow_sum]
  refine ⟨fun β => t ^ c β, ?_⟩
  change rootDiagUnit τ (simpleCorootHom (componentRoots χ i) (fun β => t ^ c β)) = _
  rw [hfun]
  exact rootDiagUnit_torusTuple ⟨_, hx⟩

theorem exists_mem_ker_of_mem_center [CharP K 2] {i : KernelComponent χ}
    {z : componentRootSpan K χ i} (hz : z ∈ Subgroup.center (componentRootSpan K χ i)) :
    ∃ x ∈ (cartanHom (K := K) (componentRoots χ i)).ker,
      (torusDiagHom K).comp (simpleCorootHom (componentRoots χ i)) x =
        (z : (Module.End K (RootModule τ K))ˣ) := by
  obtain ⟨x, hx⟩ := componentCorootTorus_le_range i (coe_mem_componentCorootTorus_of_mem_center hz)
  refine ⟨x, ?_, hx⟩
  rw [MonoidHom.mem_ker]
  funext α
  rw [cartanHom_apply, Pi.one_apply]
  have hαΨ : (α : Fin τ.rank → ℤ) ∈ componentRoots χ i := simpleRoots_subset α.2
  have hmem : pinnedX τ K (α : Fin τ.rank → ℤ) 1 ∈ componentRootSpan K χ i :=
    pinnedX_mem_rootSpan hαΨ 1
  have hc := congrArg Subtype.val (Subgroup.mem_center_iff.1 hz ⟨_, hmem⟩)
  simp only [Subgroup.coe_mul] at hc
  rw [← hx] at hc
  change pinnedX τ K _ 1 * rootDiagUnit τ (simpleCorootHom _ x) =
    rootDiagUnit τ (simpleCorootHom _ x) * pinnedX τ K _ 1 at hc
  have h1 : rootDiagUnit τ (simpleCorootHom (componentRoots χ i) x) *
      pinnedX τ K (α : Fin τ.rank → ℤ) 1 *
        (rootDiagUnit τ (simpleCorootHom (componentRoots χ i) x))⁻¹ =
      pinnedX τ K (α : Fin τ.rank → ℤ) 1 := by
    rw [← hc, mul_inv_cancel_right]
  rw [rootDiagUnit_conj_pinnedX _ (simpleRoots_isRoot α.2)] at h1
  have h2 := pinnedX_injective τ K _ h1
  rw [mul_one] at h2
  have h3 : rootChar (simpleCorootHom (componentRoots χ i) x) α = 1 := Units.ext h2
  rwa [rootChar_simpleCorootHom] at h3

end Center

section Cyclic

variable {K : Type} [Field K]

theorem eq_one_of_kerDetect [Finite K] {p : ℕ} [Fact p.Prime] {Ψ : Set (Fin τ.rank → ℤ)}
    {β₀ : simpleRoots Ψ}
    (hdet : KerDetect (Matrix.of fun β γ : simpleRoots Ψ =>
      corootPair (β : Fin τ.rank → ℤ) γ) p β₀)
    {x : simpleRoots Ψ → Kˣ} (hx : cartanHom Ψ x = 1)
    (hxP : x ^ (p ^ (Nat.card Kˣ).factorization p) = 1) (h0 : x β₀ = 1) : x = 1 := by
  classical
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Kˣ)
  set N := Nat.card Kˣ with hN
  set a := N.factorization p with ha
  set N' := ordCompl[p] N with hN'
  have hNpos : 0 < N := Nat.card_pos
  have hNP : p ^ a * N' = N := Nat.ordProj_mul_ordCompl_eq_self N p
  have hN'0 : N' ≠ 0 := by intro h; rw [h, mul_zero] at hNP; omega
  have hP0 : p ^ a ≠ 0 := by intro h; rw [h, zero_mul] at hNP; omega
  have hog : orderOf g = N := orderOf_eq_card_of_forall_mem_zpowers hg
  set ζ := g ^ N' with hζ
  have hoζ : orderOf ζ = p ^ a := by
    rw [hζ, orderOf_pow_of_dvd hN'0 (by rw [hog, ← hNP]; exact dvd_mul_left _ _), hog, ← hNP,
      Nat.mul_div_cancel _ (Nat.pos_of_ne_zero hN'0)]
  have hcoord : ∀ β, ∃ n : ℤ, x β = ζ ^ n := by
    intro β
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 (hg (x β))
    have h1 : g ^ (k * ((p ^ a : ℕ) : ℤ)) = 1 := by
      rw [zpow_mul, hk, zpow_natCast]
      simpa using congrFun hxP β
    have h2 : (N : ℤ) ∣ k * ((p ^ a : ℕ) : ℤ) := by
      rw [← hog]
      exact orderOf_dvd_iff_zpow_eq_one.2 h1
    have h3 : (N' : ℤ) ∣ k := by
      rw [← hNP, Nat.cast_mul, mul_comm k] at h2
      exact (mul_dvd_mul_iff_left (by exact_mod_cast hP0)).1 h2
    obtain ⟨n, hn⟩ := h3
    exact ⟨n, by rw [← hk, hn, zpow_mul, hζ, zpow_natCast]⟩
  choose n hn using hcoord
  have hdiv := dvd_of_kerDetect hdet a n (fun α => by
      have hα := congrFun hx α
      rw [cartanHom_apply, Pi.one_apply] at hα
      simp only [hn, ← zpow_mul, LayerCycCoroot.prod_zpow_eq_zpow_sum] at hα
      have h := orderOf_dvd_iff_zpow_eq_one.2 hα
      rw [hoζ] at h
      simpa [Matrix.of_apply] using h)
    (by
      have h := orderOf_dvd_iff_zpow_eq_one.2 ((hn β₀).symm.trans h0)
      rw [hoζ] at h
      simpa using h)
  funext β
  obtain ⟨d, hd⟩ := hdiv β
  have hd' : n β = ((p ^ a : ℕ) : ℤ) * d := by rw [hd]; push_cast; ring
  rw [hn β, hd', zpow_mul, zpow_natCast, ← hoζ, pow_orderOf_eq_one, one_zpow, Pi.one_apply]

open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley LayerCycCoroot


variable {M : Type*} [CommGroup M] {χ : Multiplicative (Fin τ.rank → ℤ) →* M}

theorem isCyclic_of_le_center [Finite K] [CharP K 2] {i : KernelComponent χ} {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) {T : Subgroup (componentRootSpan K χ i)}
    (hT : T ≤ Subgroup.center (componentRootSpan K χ i)) (hTp : IsPGroup p T) : IsCyclic T := by
  classical
  have := Fact.mk hp
  have hΨ := isRootComponent_componentRoots i
  have hne : (componentRoots χ i).Nonempty := by
    obtain ⟨⟨α, hα⟩, h⟩ := Quotient.exists_rep i
    exact ⟨α, hα, h⟩
  obtain ⟨β₀, hdet⟩ := exists_kerDetect_simpleRoots hΨ hne
    (show 2 < p by have := hp.two_le; omega)
  set N := Nat.card Kˣ with hN
  set a := N.factorization p with ha
  set N' := ordCompl[p] N with hN'
  have hNpos : 0 < N := Nat.card_pos
  have hNP : p ^ a * N' = N := Nat.ordProj_mul_ordCompl_eq_self N p
  have hcop : Nat.Coprime N' (p ^ a) :=
    ((Nat.coprime_ordCompl hp hNpos.ne').symm).pow_right a
  set m := N' ^ Nat.totient (p ^ a) with hm
  have hmmod : m ≡ 1 [MOD p ^ a] := Nat.ModEq.pow_totient hcop
  have hNm : N ∣ m * p ^ a := by
    rw [← hNP, mul_comm (p ^ a) N']
    refine mul_dvd_mul_right (dvd_pow_self N' ?_) _
    exact (Nat.totient_pos.2 (pow_pos hp.pos a)).ne'
  have hxN : ∀ x : simpleRoots (componentRoots χ i) → Kˣ, x ^ N = 1 := fun x => by
    funext β
    simp only [Pi.pow_apply, Pi.one_apply]
    exact pow_card_eq_one'
  set B : Subgroup (simpleRoots (componentRoots χ i) → Kˣ) :=
    (cartanHom (K := K) (componentRoots χ i)).ker ⊓ (powMonoidHom (p ^ a)).ker with hB
  set ev : B →* Kˣ := (Pi.evalMonoidHom (fun _ => Kˣ) β₀).comp B.subtype with hev
  have hevinj : Function.Injective ev := by
    rw [injective_iff_map_eq_one]
    intro x hx1
    have hxB := Subgroup.mem_inf.1 x.2
    exact Subtype.ext (eq_one_of_kerDetect hdet (MonoidHom.mem_ker.1 hxB.1)
      (MonoidHom.mem_ker.1 hxB.2) hx1)
  have hBcyc : IsCyclic B := isCyclic_of_injective ev hevinj
  set f := (torusDiagHom K).comp (simpleCorootHom (componentRoots χ i)) with hf
  have hGcyc : IsCyclic (B.map f) := isCyclic_of_surjective _ (f.subgroupMap_surjective B)
  have hle : T.map (componentRootSpan K χ i).subtype ≤ B.map f := by
    rintro _ ⟨z, hzT, rfl⟩
    obtain ⟨x, hxker, hxz⟩ := exists_mem_ker_of_mem_center (hT hzT)
    have hzN : (z : (Module.End K (RootModule τ K))ˣ) ^ N = 1 := by
      rw [← hxz, ← map_pow, hxN x, map_one]
    obtain ⟨e, he⟩ := (IsPGroup.iff_orderOf.mp hTp) ⟨z, hzT⟩
    have hoz : orderOf (z : (Module.End K (RootModule τ K))ˣ) ∣ p ^ a := by
      have h1 : orderOf (z : (Module.End K (RootModule τ K))ˣ) = p ^ e := by
        rw [← he, Subgroup.orderOf_mk, Subgroup.orderOf_coe]
      rw [h1]
      have h2 : p ^ e ∣ N := h1 ▸ orderOf_dvd_of_pow_eq_one hzN
      exact pow_dvd_pow p ((hp.pow_dvd_iff_le_factorization hNpos.ne').1 h2)
    refine ⟨x ^ m, ?_, ?_⟩
    · obtain ⟨d, hd⟩ := hNm
      refine Subgroup.mem_inf.2 ⟨MonoidHom.mem_ker.2 ?_, MonoidHom.mem_ker.2 ?_⟩
      · rw [map_pow, (MonoidHom.mem_ker).1 hxker, one_pow]
      · rw [powMonoidHom_apply, ← pow_mul, hd, pow_mul, hxN x, one_pow]
    · rw [map_pow, hxz, Subgroup.coe_subtype]
      calc (z : (Module.End K (RootModule τ K))ˣ) ^ m =
          (z : (Module.End K (RootModule τ K))ˣ) ^ 1 :=
            pow_eq_pow_iff_modEq.2 (hmmod.of_dvd hoz)
        _ = z := pow_one _
  have hTm : IsCyclic (T.map (componentRootSpan K χ i).subtype) :=
    isCyclic_of_surjective _ (Subgroup.subgroupOfEquivOfLe hle).surjective
  exact isCyclic_of_surjective _
    (T.equivMapOfInjective _ (Subgroup.subtype_injective _)).symm.surjective

end Cyclic

end LayerCycRoot

open CFSG.Blueprint.Chevalley

section Input


theorem ggRootCompCenterCycInput_holds (τ : Tag) : GGRootCompCenterCycInput τ :=
  fun _ _ _ _ _ _ _ hp hp2 _ _ _ hT hTp => LayerCycRoot.isCyclic_of_le_center hp hp2 hT hTp

end Input

@[expose] def GGLayerCenterCyclicModelRestTwo :
    Prop :=
  (GGExcAdjLayerCycNonToralInput .G2 2 5 ∧ GGExcAdjLayerCycNonToralInput .F4 1 5 ∧
      GGE6AdjLayerCycNonToralInput ∧ GGExcAdjLayerCycNonToralInput .E7 1 11 ∧
      GGExcAdjLayerCycNonToralInput .E8 1 11) ∧
    GGLayerInnerModelOn (fun lab => lab.tag = .triD4 ∨ lab.tag = .twF4) ∧
    GGLayerCenterCyclicExcSixRestInput

section Bundle


theorem ggLayerCenterCyclicModelRest_of_restTwo (h : GGLayerCenterCyclicModelRestTwo) :
    GGLayerCenterCyclicModelRest :=
  ⟨⟨ggRootCompCenterCycInput_holds _, ggRootCompCenterCycInput_holds _,
    ggRootCompCenterCycInput_holds _, ggRootCompCenterCycInput_holds _,
    ggRootCompCenterCycInput_holds _⟩, h⟩

theorem ggLayerCenterCyclicExcRest_of_modelRestTwo (hlay : GGLayerTagsPilotRestSix)
    (h : GGLayerCenterCyclicModelRestTwo) : GGLayerCenterCyclicExcRest :=
  ggLayerCenterCyclicExcRest_of_modelRest hlay (ggLayerCenterCyclicModelRest_of_restTwo h)

end Bundle

section BundleInput

theorem ggLayerCenterCyclicExcInput_of_modelRestTwo (hlay : GGLayerTagsPilotRestSix)
    (h : GGLayerCenterCyclicModelRestTwo) : GGLayerCenterCyclicExcInput :=
  ggLayerCenterCyclicExcInput_of_modelRest hlay (ggLayerCenterCyclicModelRest_of_restTwo h)

end BundleInput

end CFSG.StandardType

end
