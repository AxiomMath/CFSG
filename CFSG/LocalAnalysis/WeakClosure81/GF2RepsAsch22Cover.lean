module

public import CFSG.Open.Defs
import CFSG.RankThree.Coprime.LocalPrimeSectionCover
import CFSG.RankThree.GroupTheory.SteinbergBKMinimalCoverPerfect

namespace CFSG.LocalAnalysis.WeakClosure81.Asch22

theorem eq_top_of_map_quotient_of_le_map_ker {X S : Type*} [Group X] [Group S]
    (ρ : X →* S) (hρ : Function.Surjective ρ) (D : Subgroup X) [D.Normal]
    (P : Subgroup (X ⧸ D)) [P.Normal] (hP : P ≤ ρ.ker.map (QuotientGroup.mk' D))
    (hD : D ≤ ρ.ker) (hmin : ∀ M : Subgroup X, M.map ρ = ⊤ → M = ⊤) :
    ∀ M : Subgroup (X ⧸ D), M.map (QuotientGroup.mk' P) = ⊤ → M = ⊤ := by
  intro M hM
  let f : X →* X ⧸ D := QuotientGroup.mk' D
  let M' : Subgroup X := M.comap f
  have hM'map : M'.map f = M :=
    Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective D) M
  have hMP : M ⊔ P = ⊤ := by
    have h1 : (M.map (QuotientGroup.mk' P)).comap (QuotientGroup.mk' P) = ⊤ := by
      rw [hM, Subgroup.comap_top]
    rwa [Subgroup.comap_map_eq, QuotientGroup.ker_mk'] at h1
  have hMPker : M ⊔ ρ.ker.map f = ⊤ := by
    refine top_unique ?_
    rw [← hMP]
    exact sup_le_sup_left hP M
  have hVmap : (M' ⊔ ρ.ker).map f = ⊤ := by
    rw [Subgroup.map_sup, hM'map]
    exact hMPker
  have hVtop : M' ⊔ ρ.ker = ⊤ := by
    have hcomap : ((M' ⊔ ρ.ker).map f).comap f = ⊤ := by
      rw [hVmap, Subgroup.comap_top]
    rwa [Subgroup.comap_map_eq, QuotientGroup.ker_mk',
      sup_eq_left.2 (hD.trans le_sup_right)] at hcomap
  have hM'ρ : M'.map ρ = ⊤ := by
    have htop : (M' ⊔ ρ.ker).map ρ = ⊤ := by
      rw [hVtop, Subgroup.map_top_of_surjective ρ hρ]
    have hbot : (ρ.ker).map ρ = ⊥ := (Subgroup.map_eq_bot_iff _).mpr le_rfl
    rwa [Subgroup.map_sup, hbot, sup_bot_eq] at htop
  have hM'top : M' = ⊤ := hmin M' hM'ρ
  calc M = M'.map f := hM'map.symm
    _ = ⊤ := by
      rw [hM'top, Subgroup.map_top_of_surjective f (QuotientGroup.mk'_surjective D)]

instance instNormalMapPPrimeCore {U : Type*} [Group U] {p : ℕ} (K : Subgroup U) [K.Normal] :
    ((CFSG.pPrimeCore p K).map K.subtype).Normal :=
  @ConjAct.normal_of_characteristic_of_normal U _ K _ (CFSG.pPrimeCore p K)
    CFSG.pPrimeCore_characteristic

instance instNormalMapQuotientMk {U : Type*} [Group U] (D : Subgroup U) [D.Normal]
    (K : Subgroup U) [K.Normal] :
    (K.map (QuotientGroup.mk' D)).Normal :=
  (inferInstance : K.Normal).map (QuotientGroup.mk' D) (QuotientGroup.mk'_surjective D)

end CFSG.LocalAnalysis.WeakClosure81.Asch22

public section

namespace CFSG.LocalAnalysis.WeakClosure81.Asch22

theorem exists_perfect_pCover_of_surjective {G : Type} [Group G] [Finite G] {p : ℕ}
    (hp : p.Prime) (H : Subgroup G) {S : Type} [Group S] [Group.IsPerfect S] (π : H →* S)
    (hπ : Function.Surjective π) :
    ∃ (Y : Type) (_ : Group Y) (_ : Finite Y) (P : Subgroup Y) (_ : P.Normal),
      Group.IsPerfect Y ∧ IsPGroup p P ∧ Nonempty (Y ⧸ P ≃* S) ∧
      (∀ M : Subgroup Y, M.map (QuotientGroup.mk' P) = ⊤ → M = ⊤) ∧
      CFSG.Open.pRank p (⊤ : Subgroup Y) ≤ CFSG.Open.pRank p (⊤ : Subgroup G) ∧
      (CFSG.Open.IsKGroup G → CFSG.Open.IsKGroup Y) := by
  classical
  have hSperf : Group.IsPerfect (⊤ : Subgroup S) :=
    Group.IsPerfect.top_iff.mpr inferInstance
  have hΓS : Group.IsSolvable (S ⧸ (⊤ : Subgroup S)) :=
    @Group.instIsSolvableOfSubsingleton _ _ QuotientGroup.subsingleton_quotient_top
  obtain ⟨U, hU, hmin⟩ :=
    CFSG.RankThree.GroupTheory.SteinbergBK.exists_minimal_cover π hπ
  obtain ⟨hNnil, -, -, hRperf, hRmap, -, -, -⟩ :=
    CFSG.RankThree.GroupTheory.SteinbergBK.minimal_cover_properties π ⊤ hSperf hΓS U hU hmin
  let f : U →* S := π.comp U.subtype
  have hf : Function.Surjective f := by
    rw [← MonoidHom.range_eq_top, MonoidHom.range_comp, Subgroup.range_subtype, hU]
  let K : Subgroup U := f.ker
  let R : Subgroup U := perfectResidual U
  have hUperf : Group.IsPerfect U := by
    have hRtop : R = ⊤ := by
      have h1 : R.map U.subtype = U :=
        hmin (R.map U.subtype) (Subgroup.map_subtype_le R) (by
          rw [Subgroup.map_map]
          exact hRmap)
      apply Subgroup.map_injective U.subtype_injective
      rw [h1, Subgroup.map_top, Subgroup.range_subtype]
    let e : ↥R ≃* U := (MulEquiv.subgroupCongr hRtop).trans Subgroup.topEquiv
    exact Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective
  let D : Subgroup U := (CFSG.pPrimeCore p K).map K.subtype
  have hDnormal : D.Normal :=
    @ConjAct.normal_of_characteristic_of_normal U _ K _ (CFSG.pPrimeCore p K)
      CFSG.pPrimeCore_characteristic
  have hDle : D ≤ K := Subgroup.map_subtype_le _
  have hDcop : ¬ p ∣ Nat.card D := by
    rw [show Nat.card D = Nat.card (CFSG.pPrimeCore p K) from
      Subgroup.card_map_of_injective K.subtype_injective]
    exact (Nat.Prime.coprime_iff_not_dvd hp).1
      (@CFSG.pPrimeCore_coprime_card p K _ _ ⟨hp⟩)
  let Y := U ⧸ D
  let P : Subgroup Y := K.map (QuotientGroup.mk' D)
  have hPnormal : P.Normal :=
    (inferInstance : K.Normal).map (QuotientGroup.mk' D) (QuotientGroup.mk'_surjective D)
  have hPp : IsPGroup p P := by
    simpa [P, D] using
      @CFSG.RankThree.Coprime.isPGroup_map_quotient_pPrimeCore U _ _ p ⟨hp⟩ K _ hNnil
  have hminU : ∀ V : Subgroup U, V.map f = ⊤ → V = ⊤ := by
    intro V hV
    have h1 := hmin (V.map U.subtype) (Subgroup.map_subtype_le V) (by
      rw [Subgroup.map_map]
      exact hV)
    rw [eq_top_iff]
    intro x _
    have hx : (x : H) ∈ V.map U.subtype := h1.symm ▸ x.2
    obtain ⟨y, hy, hyx⟩ := hx
    rwa [show y = x from Subtype.ext hyx] at hy
  have hnoProper : ∀ M : Subgroup Y, M.map (QuotientGroup.mk' P) = ⊤ → M = ⊤ :=
    eq_top_of_map_quotient_of_le_map_ker f hf D P le_rfl hDle hminU
  let e3 : Y ⧸ P ≃* U ⧸ K := QuotientGroup.quotientQuotientEquivQuotient D K hDle
  let e2 : U ⧸ K ≃* S := QuotientGroup.quotientKerEquivOfSurjective f hf
  have hYperf : Group.IsPerfect Y := inferInstance
  have hrank : CFSG.Open.pRank p (⊤ : Subgroup Y) ≤ CFSG.Open.pRank p (⊤ : Subgroup G) := by
    calc
      CFSG.Open.pRank p (⊤ : Subgroup Y)
          = CFSG.Open.pRank p (⊤ : Subgroup U) :=
            @CFSG.SectionRank.pRank_quotient_eq U _ _ p ⟨hp⟩ D _ hDcop
      _ ≤ CFSG.Open.pRank p (⊤ : Subgroup H) :=
            CFSG.SectionRank.pRank_top_le_of_injective hp.one_lt U.subtype
              U.subtype_injective
      _ ≤ CFSG.Open.pRank p (⊤ : Subgroup G) :=
            CFSG.SectionRank.pRank_top_le_of_injective hp.one_lt H.subtype
              H.subtype_injective
  have hKtoY : CFSG.Open.IsKGroup G → CFSG.Open.IsKGroup Y := fun hG =>
    (hG.subgroup H).subgroup U |>.quotient D
  exact ⟨Y, inferInstance, inferInstance, P, hPnormal, hYperf, hPp, ⟨e3.trans e2⟩,
    hnoProper, hrank, hKtoY⟩

theorem exists_perfect_pCover {G : Type} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    (H : Subgroup G) (N : Subgroup H) [N.Normal] [Group.IsPerfect (H ⧸ N)] :
    ∃ (Y : Type) (_ : Group Y) (_ : Finite Y) (P : Subgroup Y) (_ : P.Normal),
      Group.IsPerfect Y ∧ IsPGroup p P ∧ Nonempty (Y ⧸ P ≃* H ⧸ N) ∧
      (∀ M : Subgroup Y, M.map (QuotientGroup.mk' P) = ⊤ → M = ⊤) ∧
      CFSG.Open.pRank p (⊤ : Subgroup Y) ≤ CFSG.Open.pRank p (⊤ : Subgroup G) := by
  obtain ⟨Y, hGY, hFinY, P, hPN, hperf, hPp, he, hmin, hrank, _⟩ :=
    exists_perfect_pCover_of_surjective hp H (QuotientGroup.mk' N)
      (QuotientGroup.mk'_surjective N)
  exact ⟨Y, hGY, hFinY, P, hPN, hperf, hPp, he, hmin, hrank⟩

end CFSG.LocalAnalysis.WeakClosure81.Asch22
