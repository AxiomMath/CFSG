module

public import CFSG.LocalAnalysis.StandardType.GGSixFieldFiveTagsOmComp
public import CFSG.LocalAnalysis.StandardType.GGSixFieldFiveTagsOmCent

public section

namespace CFSG.StandardType

namespace FieldFiveOm

open CFSG.Assembly QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Universal.Spin
  LayerCores LayerFacts OmNonsplit

section Conj

variable {L : Type*} [Group L] {G : Type*} [Group G]

@[expose] def conjOf (ψ : L →* G) (D : Subgroup G) : Subgroup L :=
  ((D.prod ⊤) ⊓ ggConjPairs ψ).map (MonoidHom.snd G L)

theorem mem_conjOf {ψ : L →* G} {D : Subgroup G} {s : L} :
    s ∈ conjOf ψ D ↔ ∃ e ∈ D, (e, s) ∈ ggConjPairs ψ := by
  constructor
  · rintro ⟨q, hq, rfl⟩
    exact ⟨q.1, (Subgroup.mem_prod.mp (Subgroup.mem_inf.mp hq).1).1, (Subgroup.mem_inf.mp hq).2⟩
  · rintro ⟨e, he, h⟩
    exact ⟨(e, s), Subgroup.mem_inf.mpr ⟨Subgroup.mem_prod.mpr ⟨he, Subgroup.mem_top s⟩, h⟩, rfl⟩

theorem range_inf_centralizer_eq_conjOf {ψ : L →* G} (hinj : Function.Injective ψ)
    {D : Subgroup G} (hDs : ∀ e ∈ D, ∃ s, (e, s) ∈ ggConjPairs ψ) :
    ψ.range ⊓ Subgroup.centralizer (D : Set G) =
      (Subgroup.centralizer (conjOf ψ D : Set L)).map ψ := by
  apply le_antisymm
  · rintro _ ⟨⟨u, rfl⟩, hu⟩
    refine ⟨u, Subgroup.mem_centralizer_iff.mpr fun g hg => ?_, rfl⟩
    obtain ⟨e, he, heg⟩ := mem_conjOf.mp hg
    have hxu : e * ψ u = ψ u * e := (Subgroup.mem_centralizer_iff.mp hu e he)
    have h1 : g * u * g⁻¹ = u := hinj (by
      rw [heg u]
      calc e * ψ u * e⁻¹ = ψ u * e * e⁻¹ := by rw [hxu]
        _ = ψ u := by group)
    calc g * u = g * u * g⁻¹ * g := by group
      _ = u * g := by rw [h1]
  · rintro _ ⟨u, hu, rfl⟩
    refine Subgroup.mem_inf.mpr ⟨⟨u, rfl⟩, Subgroup.mem_centralizer_iff.mpr fun e he => ?_⟩
    obtain ⟨g, hg⟩ := hDs e he
    have hsu : g * u = u * g :=
      Subgroup.mem_centralizer_iff.mp hu g (mem_conjOf.mpr ⟨e, he, hg⟩)
    have h1 : g * u * g⁻¹ = u := by rw [hsu]; group
    have h2 := hg u
    rw [h1] at h2
    calc e * ψ u = e * ψ u * e⁻¹ * e := by group
      _ = ψ u * e := by rw [← h2]

end Conj

section Main

variable {K : Type} [Field K] [Finite K] [CharP K 2] {V : Type} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V}

theorem fieldFive_om (hQ : (polarBilin Q).Nondegenerate) (hK : Nat.card K = 2)
    (hinj : Function.Injective (spinAction Q))
    (hrange : (spinAction Q).range = ⁅TauCeti.QuadraticMap.orthogonalGroup Q,
      TauCeti.QuadraticMap.orthogonalGroup Q⁆)
    (hZ : Subgroup.center (spinGroup Q) = ⊥)
    {G : Type} [Group G] [Finite G] {ψ : spinGroup Q →* G} (hψ : Function.Injective ψ)
    {D : Subgroup G} (hDel : IsElemAbelian 5 D) (hDcard : Nat.card D = 5 ^ 2)
    (hDs : ∀ e ∈ D, ∃ s, (e, s) ∈ ggConjPairs ψ) {x : G} (hxD : x ∈ D) {L : Subgroup G}
    (hL : IsComponentOf L (ψ.range ⊓ Subgroup.centralizer {x}))
    (hLmark : GGNbrClauseFiveMarking 5 x L)
    {J : Subgroup G} (hJ : IsComponentOf J (L ⊓ Subgroup.centralizer (D : Set G))) :
    ∃ y ∈ D, y ≠ 1 ∧ ∃ K' : Subgroup G,
      IsComponentOf K' (ψ.range ⊓ Subgroup.centralizer {y}) ∧ J ≤ K' ∧ 5 ∣ Nat.card K' ∧
      x ∉ Subgroup.centralizer (K' : Set G) ∧ ¬ GGNbrClauseFiveMarking 5 x K' := by
  classical
  have := finite_linearEquiv (K := K) (V := V)
  have : Finite (spinGroup Q) := Finite.of_injective _ hinj
  have hσO : ∀ u, spinAction Q u ∈ TauCeti.QuadraticMap.orthogonalGroup Q := fun u =>
    TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr fun v => map_spinAction Q u v
  have hker : ψ.ker ≤ Subgroup.center (spinGroup Q) := by
    rw [(MonoidHom.ker_eq_bot_iff ψ).mpr hψ]
    exact bot_le
  have hZ1 : ∀ g : spinGroup Q, ((1 : G), g) ∈ ggConjPairs ψ → g = 1 := fun g hg => by
    have h := mem_center_of_mem_ggConjPairs_one hψ hg
    rwa [hZ, Subgroup.mem_bot] at h
  have hpow : ∀ e ∈ D, ∀ s : spinGroup Q, (e, s) ∈ ggConjPairs ψ → s ^ 5 = 1 := by
    intro e he s hs
    refine hZ1 _ ?_
    have h := (ggConjPairs ψ).pow_mem hs 5
    rwa [Prod.pow_mk, hDel.2 e he] at h
  have hcomm : ∀ e ∈ D, ∀ e' ∈ D, ∀ s s' : spinGroup Q, (e, s) ∈ ggConjPairs ψ →
      (e', s') ∈ ggConjPairs ψ → s * s' = s' * s := by
    intro e he e' he' s s' hs hs'
    have hee : e * e' = e' * e :=
      congrArg Subtype.val (hDel.1.is_comm.comm (⟨e, he⟩ : ↥D) ⟨e', he'⟩)
    have h := (ggConjPairs ψ).mul_mem ((ggConjPairs ψ).mul_mem hs hs')
      ((ggConjPairs ψ).inv_mem ((ggConjPairs ψ).mul_mem hs' hs))
    rw [Prod.mk_mul_mk, Prod.mk_mul_mk, Prod.inv_mk, Prod.mk_mul_mk, hee, mul_inv_cancel] at h
    have h1 := hZ1 _ h
    calc s * s' = s * s' * (s' * s)⁻¹ * (s' * s) := by group
      _ = s' * s := by rw [h1, one_mul]
  have hJq : CFSG.IsQuasisimple J :=
    (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native J).mp hJ.2.2
  have hJL : J ≤ L := hJ.1.trans inf_le_left
  have hJr : J ≤ ψ.range := hJL.trans (hL.1.trans inf_le_left)
  obtain ⟨sx, hsx⟩ := hDs x hxD
  have hsx5 := hpow x hxD sx hsx
  have hclaim : ∀ S : Subgroup (V ≃ₗ[K] V), CFSG.IsQuasisimple S →
      S ≤ TauCeti.QuadraticMap.orthogonalGroup Q → (S.comap (spinAction Q)).map ψ = J →
      ¬ ∀ M ∈ S, ∀ v, M (spinAction Q sx v - v) = spinAction Q sx v - v := by
    intro S hSq hSO hSJ hfix
    obtain ⟨Kx, hKx, hJKx, hKxw⟩ :=
      exists_fixedCore_component_om hQ hK hinj hrange hψ hsx hsx5 hSq hSO hfix
    rw [hSJ] at hJKx
    obtain rfl := eq_of_isComponentOf_of_le hL hKx hJq hJL hJKx
    exact (hKxw x sx hsx hsx5 rfl).1 hLmark
  obtain ⟨S, hSq, hSO, hSJ, y, hyD, hy1, t, hyt, hSt⟩ : ∃ S : Subgroup (V ≃ₗ[K] V),
      CFSG.IsQuasisimple S ∧ S ≤ TauCeti.QuadraticMap.orthogonalGroup Q ∧
      (S.comap (spinAction Q)).map ψ = J ∧ ∃ y ∈ D, y ≠ 1 ∧ ∃ t : spinGroup Q,
        (y, t) ∈ ggConjPairs ψ ∧ ∀ M ∈ S, ∀ v, M (spinAction Q t v - v) = spinAction Q t v - v := by
    by_cases hc : ∃ y ∈ D, y ≠ 1 ∧ (y, (1 : spinGroup Q)) ∈ ggConjPairs ψ
    ·
      obtain ⟨y, hyD, hy1, hy⟩ := hc
      let e1 : ↥(J.comap ψ) ≃* ↥J := ((J.comap ψ).equivMapOfInjective ψ hψ).trans
        (MulEquiv.subgroupCongr (Subgroup.map_comap_eq_self hJr))
      refine ⟨(J.comap ψ).map (spinAction Q), CFSG.LocalCores.isQuasisimple_of_mulEquiv
        (e1.symm.trans ((J.comap ψ).equivMapOfInjective _ hinj)) hJq, ?_, ?_, y, hyD, hy1, 1,
        hy, fun M _ v => by simp⟩
      · rintro _ ⟨u, -, rfl⟩
        exact hσO u
      · rw [Subgroup.comap_map_eq_self_of_injective hinj, Subgroup.map_comap_eq_self hJr]
    push Not at hc
    have hADO : (conjOf ψ D).map (spinAction Q) ≤ TauCeti.QuadraticMap.orthogonalGroup Q := by
      rintro _ ⟨s, -, rfl⟩
      exact hσO s
    have hADc : ∀ g ∈ (conjOf ψ D).map (spinAction Q),
        ∀ h ∈ (conjOf ψ D).map (spinAction Q), g * h = h * g := by
      rintro _ ⟨s, hs, rfl⟩ _ ⟨s', hs', rfl⟩
      obtain ⟨e, he, hes⟩ := mem_conjOf.mp hs
      obtain ⟨e', he', hes'⟩ := mem_conjOf.mp hs'
      rw [← map_mul, ← map_mul, hcomm e he e' he' s s' hes hes']
    have hAD5 : ∀ g ∈ (conjOf ψ D).map (spinAction Q), g ^ 5 = 1 := by
      rintro _ ⟨s, hs, rfl⟩
      obtain ⟨e, he, hes⟩ := mem_conjOf.mp hs
      rw [← map_pow, hpow e he s hes, map_one]
    have hAD25 : 5 < Nat.card ((conjOf ψ D).map (spinAction Q)) := by
      choose f hf using hDs
      let g : D → (conjOf ψ D).map (spinAction Q) := fun e =>
        ⟨spinAction Q (f e e.2), ⟨f e e.2, mem_conjOf.mpr ⟨e, e.2, hf e e.2⟩, rfl⟩⟩
      have hg : Function.Injective g := by
        intro e e' hee
        have h1 : f e e.2 = f e' e'.2 := hinj (congrArg Subtype.val hee)
        by_contra hne
        have hne' : (e : G) * (e' : G)⁻¹ ≠ 1 := fun h => hne (Subtype.ext (mul_inv_eq_one.mp h))
        apply hc _ (D.mul_mem e.2 (D.inv_mem e'.2)) hne'
        have h2 := (ggConjPairs ψ).mul_mem (hf e e.2) ((ggConjPairs ψ).inv_mem (hf e' e'.2))
        rwa [Prod.inv_mk, Prod.mk_mul_mk, h1, mul_inv_cancel] at h2
      have h1 := Nat.card_le_card_of_injective g hg
      rw [hDcard] at h1
      omega
    obtain ⟨β, Sf, hS, hST⟩ := exists_subCoreFamily_orthCent_fix hQ hADO hADc hAD5 hAD25
    have hSinf := hS.inf_of_commutator_le (N := ⁅TauCeti.QuadraticMap.orthogonalGroup Q,
      TauCeti.QuadraticMap.orthogonalGroup Q⁆) (Subgroup.commutator_mono inf_le_right inf_le_right)
    have hS' := hSinf.comap (spinAction Q) hinj (by rw [hrange]; exact inf_le_right)
    rw [comap_spinAction_centralizer hinj hrange (conjOf ψ D)] at hS'
    have hJG : IsComponentOf J ((Subgroup.centralizer (conjOf ψ D : Set (spinGroup Q))).map ψ) := by
      have h1 := CFSG.LocalAnalysis.ComponentInitial.assembly_isSubnormal_inf hL.2.1
        (Subgroup.centralizer (D : Set G))
      have h2 : ψ.range ⊓ Subgroup.centralizer {x} ⊓ Subgroup.centralizer (D : Set G) =
          ψ.range ⊓ Subgroup.centralizer (D : Set G) := by
        rw [inf_assoc, inf_eq_right.mpr
          (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hxD))]
      rw [h2, range_inf_centralizer_eq_conjOf hψ hDs] at h1
      exact isComponentOf_of_isSubnormal_of_isComponentOf hJ h1
    obtain ⟨c, hJc⟩ := LayerPDiv.exists_eq_map_of_isComponentOf_sub ψ hker le_rfl
      (by rw [Subgroup.subgroupOf_self]; infer_instance) (ggCommutator_self_le _) hS' hJG
    obtain ⟨T, hTA, hT1, hTfix⟩ := hST c
    obtain ⟨t, htD, rfl⟩ := hTA
    obtain ⟨y, hyD, hyt⟩ := mem_conjOf.mp htD
    refine ⟨Sf c, hS.2.2.1 c, (hS.1 c).trans inf_le_right, hJc.symm, y, hyD, ?_, t, hyt, hTfix⟩
    rintro rfl
    exact hT1 (by rw [hZ1 t hyt, map_one])
  obtain ⟨K', hK', hJK', hK'w⟩ :=
    exists_fixedCore_component_om hQ hK hinj hrange hψ hyt (hpow y hyD t hyt) hSq hSO hSt
  rw [hSJ] at hJK'
  obtain ⟨hnm, hfix | ⟨h5, hxK⟩⟩ := hK'w x sx hsx hsx5 (hcomm x hxD y hyD sx t hsx hyt)
  · exact absurd (fun M hM v => (hfix M hM).2 v) (hclaim S hSq hSO hSJ)
  · exact ⟨y, hyD, hy1, K', hK', hJK', h5, hxK, hnm⟩

end Main

end FieldFiveOm

end CFSG.StandardType
