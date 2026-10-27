module

public import CFSG.RankThree.PartOne.KC.OrthogonalInnerPlane
public import CFSG.RankThree.PartOne.KC.OrthogonalD4WitnessDefs
public import CFSG.RankThree.PartOne.KC.OrthogonalD4WitnessLayer

public section

namespace CFSG.RankThree.PartOne.KCOrthogonalD4

open Module QuadraticMap CFSG.RankThree.Classical2 CFSG.RankThree.PartOne.KCOrthogonal
  CFSG.ComponentClassification CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear

section Basic

variable {K : Type} [Field K] [Finite K] {d : ℕ} (Q : QuadraticForm K (Fin d → K))

theorem center_projOrthDerived_eq_bot (hnd : (polarBilin Q).Nondegenerate)
    (hT : ∃ S : Submodule K (Fin d → K), finrank K S = 3 ∧ ∀ v ∈ S, Q v = 0) :
    Subgroup.center (ProjOrthDerived Q) = ⊥ := by
  obtain ⟨-, -, -, hsimple, hnonab, -⟩ :=
    CFSG.RankThree.Classical.orthogonal_high_Witt_derived_quotient_and_odd_lifts hnd hT
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center (ProjOrthDerived Q)) with h | h
  · exact h
  · exfalso
    obtain ⟨c, e, hce⟩ := hnonab
    exact hce (Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top e) c)

theorem conj_injective_projOrthDerived (hnd : (polarBilin Q).Nondegenerate)
    (hT : ∃ S : Submodule K (Fin d → K), finrank K S = 3 ∧ ∀ v ∈ S, Q v = 0) :
    Function.Injective (MulAut.conj : ProjOrthDerived Q →* MulAut (ProjOrthDerived Q)) :=
  conj_injective_of_trivial_center (center_projOrthDerived_eq_bot Q hnd hT)

theorem conj_injective_matrixProjectiveDerived (hd : 0 < d) (hnd : (polarBilin Q).Nondegenerate)
    (hT : ∃ S : Submodule K (Fin d → K), finrank K S = 3 ∧ ∀ v ∈ S, Q v = 0) :
    Function.Injective
      (MulAut.conj : matrixProjectiveDerived Q →* MulAut (matrixProjectiveDerived Q)) := by
  intro g g' h
  have h1 := congrArg (MulAut.congr (bridgeEquiv Q hd)) h
  rw [OuterAutomorphisms.congr_conj, OuterAutomorphisms.congr_conj] at h1
  exact (bridgeEquiv Q hd).injective (conj_injective_projOrthDerived Q hnd hT h1)

end Basic

section Lift

variable {K : Type} [Field K] {d : ℕ} (Q : QuadraticForm K (Fin d → K))

@[expose] noncomputable def liftConj (hd : 0 < d) :
    ProjOrthDerived Q →* MulAut (matrixProjectiveDerived Q) :=
  (MulAut.conj : matrixProjectiveDerived Q →* MulAut (matrixProjectiveDerived Q)).comp
    (bridgeEquiv Q hd).symm.toMonoidHom

theorem liftConj_apply (hd : 0 < d) (c : ProjOrthDerived Q) :
    liftConj Q hd c = MulAut.conj ((bridgeEquiv Q hd).symm c) := rfl

theorem congr_liftConj (hd : 0 < d) (c : ProjOrthDerived Q) :
    MulAut.congr (bridgeEquiv Q hd) (liftConj Q hd c) = MulAut.conj c := by
  rw [liftConj_apply, OuterAutomorphisms.congr_conj, MulEquiv.apply_symm_apply]

end Lift

section Groups

theorem eq_of_isSimpleGroup_of_sup_eq {G : Type*} [Group G] {X Y J : Subgroup G}
    (hJ : X ⊔ Y = J) [IsSimpleGroup ↥J] (hX : X ≠ ⊥)
    (hcomm : ∀ u ∈ X, ∀ v ∈ Y, u * v = v * u) : X = J := by
  have hXJ : X ≤ J := hJ ▸ le_sup_left
  have hnorm : (X.subgroupOf J).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hXJ, ← hJ]
    refine sup_le Subgroup.le_normalizer fun y hy => ?_
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · intro hh
      have : y * h * y⁻¹ = h := by rw [← hcomm h hh y hy]; group
      rw [this]
      exact hh
    · intro hh
      have h2 := hcomm _ hh y⁻¹ (inv_mem hy)
      have : h = y * h * y⁻¹ := by
        calc h = y⁻¹ * (y * h * y⁻¹) * y := by group
          _ = (y * h * y⁻¹) * y⁻¹ * y := by rw [← h2]
          _ = y * h * y⁻¹ := by group
      rw [this]
      exact hh
  have := hnorm
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (X.subgroupOf J) with h | h
  · exact absurd ((Subgroup.subgroupOf_eq_bot.mp h).eq_bot_of_le hXJ) hX
  · exact le_antisymm hXJ (Subgroup.subgroupOf_eq_top.mp h)

end Groups

section Fixed

variable {K : Type} [Field K] [Finite K] {d : ℕ} {Q : QuadraticForm K (Fin d → K)}

omit [Finite K] in
theorem fixedLayerListed_of_odd {V : Type*} [AddCommGroup V] [Module K V]
    (hodd : Odd (Nat.card K)) (Q : QuadraticForm K V) (xe : V ≃ₗ[K] V)
    (h4 : 4 ≤ finrank K (fixedSpace xe))
    (hq3 : Nat.card K = 3 → ¬ IsSplitFourSpace (Q.comp (fixedSpace xe).subtype)) :
    FixedLayerListed Q xe := by
  refine ⟨by omega, ?_⟩
  rintro (⟨h3, -⟩ | ⟨hsplit, hq⟩)
  · omega
  · rcases hq with hq2 | hq3'
    · rw [hq2] at hodd
      exact absurd hodd (by decide)
    · exact hq3 hq3' hsplit

omit [Finite K] in
theorem fixedLayerListed_of_nonsplit_four {V : Type*} [AddCommGroup V] [Module K V]
    (Q : QuadraticForm K V) (xe : V ≃ₗ[K] V) (hdim : finrank K (fixedSpace xe) = 4)
    (hW2 : ∀ S : Submodule K (fixedSpace xe), finrank K S = 2 → ∃ s ∈ S, Q (s : V) ≠ 0) :
    FixedLayerListed Q xe := by
  refine ⟨by omega, ?_⟩
  rintro (⟨h3, -⟩ | ⟨⟨-, S, hS2, hS0⟩, -⟩)
  · omega
  · obtain ⟨s, hs, hne⟩ := hW2 S hS2
    exact hne (hS0 s hs)

theorem oddOrderIsometry_matrix (hnd : (polarBilin Q).Nondegenerate) {p : ℕ} (hp : p.Prime)
    (hpl : p ≠ ringChar K) (x : matrixDerived Q) (hxp : orderOf x = p) :
    OddOrderIsometry Q p (matrixLinearIso x.val) :=
  oddOrderIsometry_of_orthDerived hp hpl hnd (derivedEquiv Q x)
    (by rw [MulEquiv.orderOf_eq]; exact hxp)

omit [Finite K] in
theorem supportedMatrix_le_matrixDerived {p : ℕ} {x : matrixDerived Q}
    (hx : OddOrderIsometry Q p (matrixLinearIso x.val)) :
    supportedMatrix Q (matrixFixedSpace x.val) ≤ matrixDerived Q := by
  intro A hA
  rw [mem_matrixDerived_iff_linear]
  have h1 : matrixLinearIso A ∈ supportedOrthDerived Q (fixedSpace (matrixLinearIso x.val)) := hA
  rw [supportedOrthDerived_fixedSpace hx] at h1
  exact hx.supportedFixedDerived_le_orthDerived h1

omit [Finite K] in
theorem supportedInner_eq_map (hd : 0 < d) {p : ℕ} {x : matrixDerived Q}
    (hx : OddOrderIsometry Q p (matrixLinearIso x.val)) :
    supportedInner Q (matrixFixedSpace x.val) =
      (fixedComponentImage Q (matrixLinearIso x.val)).map (liftConj Q hd) := by
  have hS := supportedOrthDerived_fixedSpace hx
  ext c
  rw [mem_supportedInner, fixedComponentImage, Subgroup.map_map]
  constructor
  · rintro ⟨g, hg, rfl⟩
    have hgS : (derivedEquiv Q g : (Fin d → K) ≃ₗ[K] (Fin d → K)) ∈
        supportedFixedDerived Q (matrixLinearIso x.val) := by
      rw [← hS]
      exact hg
    refine Subgroup.mem_map.mpr ⟨derivedEquiv Q g, Subgroup.mem_subgroupOf.mpr hgS, ?_⟩
    · change liftConj Q hd (QuotientGroup.mk (derivedEquiv Q g)) = _
      rw [liftConj_apply, ← bridgeEquiv_projection Q hd g, MulEquiv.symm_apply_apply]
  · intro hc
    obtain ⟨X, hX, rfl⟩ := Subgroup.mem_map.mp hc
    have hXS : (X : (Fin d → K) ≃ₗ[K] (Fin d → K)) ∈ supportedFixedDerived Q
        (matrixLinearIso x.val) := hX
    refine ⟨(derivedEquiv Q).symm X, ?_, ?_⟩
    · change matrixLinearIso ((derivedEquiv Q).symm X).val ∈
        supportedOrthDerived Q (fixedSpace (matrixLinearIso x.val))
      have : matrixLinearIso ((derivedEquiv Q).symm X).val = (X : _ ≃ₗ[K] _) := by
        have := derivedEquiv_val Q ((derivedEquiv Q).symm X)
        rw [MulEquiv.apply_symm_apply] at this
        exact this.symm
      rw [this, hS]
      exact hXS
    · change MulAut.conj (matrixProjectiveProjection Q ((derivedEquiv Q).symm X)) =
        liftConj Q hd (QuotientGroup.mk X)
      rw [liftConj_apply]
      congr 1
      apply (bridgeEquiv Q hd).injective
      rw [bridgeEquiv_projection, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply]

end Fixed

section Simple

variable {K : Type} [Field K] {V : Type*} [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}
  {xe : V ≃ₗ[K] V}

theorem isSimpleGroup_fixedComponentImage (hS : IsSimpleGroup ↥(supportedFixedDerived Q xe))
    (hSΩ : supportedFixedDerived Q xe ≤ orthDerived Q)
    (hne : fixedComponentImage Q xe ≠ ⊥) : IsSimpleGroup ↥(fixedComponentImage Q xe) := by
  let Φ : ↥(supportedFixedDerived Q xe) →* ProjOrthDerived Q :=
    (QuotientGroup.mk' ((CFSG.ClassicalGroups.Orthogonal.scalars K V).subgroupOf
      (orthDerived Q))).comp (Subgroup.inclusion hSΩ)
  have hrange : Φ.range = fixedComponentImage Q xe := by
    ext c
    constructor
    · rintro ⟨s, rfl⟩
      exact Subgroup.mem_map.mpr ⟨Subgroup.inclusion hSΩ s, s.2, rfl⟩
    · intro hc
      obtain ⟨X, hX, rfl⟩ := Subgroup.mem_map.mp hc
      exact ⟨⟨X, hX⟩, rfl⟩
  have : Nontrivial ↥Φ.range := by
    rw [hrange]
    exact (Subgroup.nontrivial_iff_ne_bot _).mpr hne
  have hsimple : IsSimpleGroup ↥Φ.range :=
    IsSimpleGroup.isSimpleGroup_of_surjective Φ.rangeRestrict Φ.rangeRestrict_surjective
  rw [hrange] at hsimple
  exact hsimple

end Simple

section KC

variable {K : Type} [Field K] [Finite K] {d : ℕ} {Q : QuadraticForm K (Fin d → K)}

theorem kc_apply (hd : 0 < d) (hnd : (polarBilin Q).Nondegenerate)
    (hT : ∃ S : Submodule K (Fin d → K), finrank K S = 3 ∧ ∀ v ∈ S, Q v = 0)
    {p : ℕ} (hp : p.Prime) (hp3 : 3 < p) (hpl : p ≠ ringChar K)
    (A : Subgroup (MulAut (matrixProjectiveDerived Q)))
    (hAH : A ≤ OuterAutomorphisms.inner (matrixProjectiveDerived Q))
    (hAe : CFSG.IsElementaryAbelian p A) (hAcard : Nat.card A = p ^ 2)
    {a : MulAut (matrixProjectiveDerived Q)} (haA : a ∈ A) (ha1 : a ≠ 1)
    {x : matrixDerived Q} (hxp : orderOf x = p)
    (hxa : MulAut.conj (matrixProjectiveProjection Q x) = a)
    (D : Subgroup (MulAut (matrixProjectiveDerived Q)))
    (hD : OuterAutomorphisms.inner (matrixProjectiveDerived Q) ≤ D)
    (hlist : FixedLayerListed Q (matrixLinearIso x.val)) :
    ∃ (n : ℕ) (C : Fin n → Subgroup (ProjOrthDerived Q)), 1 ≤ n ∧ n ≤ 2 ∧
      (⨆ i, C i) = fixedComponentImage Q (matrixLinearIso x.val) ∧
      (∀ i, C i ≠ ⊥ ∧ CFSG.IsQuasisimple ↥(C i) ∧
        (C i).map (liftConj Q hd) ≤
          D ⊓ Subgroup.centralizer ({a} : Set (MulAut (matrixProjectiveDerived Q))) ∧
        CFSG.IsComponent (((C i).map (liftConj Q hd)).subgroupOf
          (D ⊓ Subgroup.centralizer ({a} : Set (MulAut (matrixProjectiveDerived Q)))))) ∧
      ∀ i j, i ≠ j → ∀ u ∈ C i, ∀ v ∈ C j, u * v = v * u := by
  classical
  have := hAe
  set e := bridgeEquiv Q hd with he
  set ε : MulAut (matrixProjectiveDerived Q) ≃* MulAut (ProjOrthDerived Q) := MulAut.congr e
    with hε
  set xC : orthDerived Q := derivedEquiv Q x with hxC
  set aC : ProjOrthDerived Q := QuotientGroup.mk xC with haC
  have hinjP := conj_injective_matrixProjectiveDerived Q hd hnd hT
  have heπ : e (matrixProjectiveProjection Q x) = aC := bridgeEquiv_projection Q hd x
  have hεa : ε a = MulAut.conj aC := by
    rw [← hxa, hε, OuterAutomorphisms.congr_conj, heπ]
  set κ := liftConj Q hd with hκ
  have hκinj : Function.Injective κ := fun c c' h => e.symm.injective (hinjP h)
  have hκinner : ∀ c, κ c ∈ OuterAutomorphisms.inner (matrixProjectiveDerived Q) := fun c =>
    ⟨e.symm c, rfl⟩
  have hAκ : A ≤ κ.range := fun z hz => by
    obtain ⟨t, rfl⟩ := hAH hz
    exact ⟨e t, by rw [hκ, liftConj_apply, MulEquiv.symm_apply_apply]⟩
  have hκa : κ aC = a := by
    rw [hκ, liftConj_apply, ← heπ, MulEquiv.symm_apply_apply, hxa]
  have hAC : CFSG.Assembly.IsElemAbelian p (A.comap κ) := by
    refine ⟨⟨⟨fun u v => ?_⟩⟩, fun y hy => ?_⟩
    · apply Subtype.ext
      apply hκinj
      rw [Subgroup.coe_mul, Subgroup.coe_mul, map_mul, map_mul]
      have hu : κ (u : ProjOrthDerived Q) ∈ A := u.2
      have hv : κ (v : ProjOrthDerived Q) ∈ A := v.2
      exact congrArg Subtype.val
        ((isMulCommutative_iff.mp inferInstance) (⟨κ u, hu⟩ : A) ⟨κ v, hv⟩)
    · apply hκinj
      rw [map_pow, map_one]
      exact CFSG.elemPow_eq_one_of_isElementaryAbelian (κ y) hy
  have hAcard' : Nat.card (A.comap κ) = p ^ 2 := by
    rw [← hAcard]
    have h1 : (A.comap κ).map κ = A := Subgroup.map_comap_eq_self hAκ
    have h2 := Nat.card_congr (Subgroup.equivMapOfInjective (A.comap κ) κ hκinj).toEquiv
    rw [h1] at h2
    exact h2
  have haCA : aC ∈ A.comap κ := by
    rw [Subgroup.mem_comap, hκa]
    exact haA
  have haC1 : aC ≠ 1 := fun h => ha1 (by rw [← hκa, h, map_one])
  set B : Subgroup (MulAut (ProjOrthDerived Q)) := D.map ε.toMonoidHom with hB
  have hBle : (MulAut.conj : ProjOrthDerived Q →* MulAut (ProjOrthDerived Q)).range ≤ B := by
    rintro _ ⟨c, rfl⟩
    exact ⟨κ c, hD (hκinner c), congr_liftConj Q hd c⟩
  have hlist' : FixedLayerListed Q (xC : (Fin d → K) ≃ₗ[K] (Fin d → K)) := hlist
  obtain ⟨-, n, C, hn1, hn2, hsup, hC, hcomm⟩ :=
    (orthogonal_inner_plane_local_core_centralization hnd hT hp hp3 hpl B hBle (A.comap κ) hAC
      hAcard' aC haCA haC1 xC rfl (by rw [hxC, MulEquiv.orderOf_eq]; exact hxp)).1 hlist'
  refine ⟨n, C, hn1, hn2, hsup, fun i => ?_, hcomm⟩
  obtain ⟨hne, hq, hCa, -, hcB⟩ := hC i
  have hLmap : ((C i).map κ).map ε.toMonoidHom =
      (C i).map (MulAut.conj : ProjOrthDerived Q →* MulAut (ProjOrthDerived Q)) := by
    rw [Subgroup.map_map]
    congr 1
    exact MonoidHom.ext fun c => congr_liftConj Q hd c
  have hLle : (C i).map κ ≤
      D ⊓ Subgroup.centralizer ({a} : Set (MulAut (matrixProjectiveDerived Q))) := by
    rintro _ ⟨c, hc, rfl⟩
    refine Subgroup.mem_inf.mpr ⟨hD (hκinner c), Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
    have h1 : c * aC = aC * c := Subgroup.mem_centralizer_singleton_iff.mp (hCa hc)
    have h2 : e.symm c * matrixProjectiveProjection Q x =
        matrixProjectiveProjection Q x * e.symm c := by
      have := congrArg e.symm h1
      rw [map_mul, map_mul, ← heπ, MulEquiv.symm_apply_apply] at this
      exact this
    rw [hκ, liftConj_apply, ← hxa, ← map_mul, ← map_mul, h2]
  refine ⟨hne, hq, hLle, ?_⟩
  rw [isComponent_map_iff e D a ((C i).map κ), hLmap, hεa]
  exact hcB

theorem supportedInner_le_layerCentralizer (hd : 0 < d) (hnd : (polarBilin Q).Nondegenerate)
    (hT : ∃ S : Submodule K (Fin d → K), finrank K S = 3 ∧ ∀ v ∈ S, Q v = 0)
    {p : ℕ} (hp : p.Prime) (hp3 : 3 < p) (hpl : p ≠ ringChar K)
    (A : Subgroup (MulAut (matrixProjectiveDerived Q)))
    (hAH : A ≤ OuterAutomorphisms.inner (matrixProjectiveDerived Q))
    (hAe : CFSG.IsElementaryAbelian p A) (hAcard : Nat.card A = p ^ 2)
    {a : MulAut (matrixProjectiveDerived Q)} (haA : a ∈ A) (ha1 : a ≠ 1)
    {x : matrixDerived Q} (hxp : orderOf x = p)
    (hxa : MulAut.conj (matrixProjectiveProjection Q x) = a)
    (D : Subgroup (MulAut (matrixProjectiveDerived Q)))
    (hD : OuterAutomorphisms.inner (matrixProjectiveDerived Q) ≤ D)
    (hlist : FixedLayerListed Q (matrixLinearIso x.val)) :
    supportedInner Q (matrixFixedSpace x.val) ≤ layerCentralizer D a := by
  obtain ⟨n, C, -, -, hsup, hC, -⟩ :=
    kc_apply hd hnd hT hp hp3 hpl A hAH hAe hAcard haA ha1 hxp hxa D hD hlist
  have hx := oddOrderIsometry_matrix hnd hp hpl x hxp
  rw [supportedInner_eq_map hd hx, ← hsup, Subgroup.map_iSup]
  exact iSup_le fun i => le_layerCentralizer_of_isComponent (hC i).2.2.1 (hC i).2.2.2

theorem supportedInner_isComponent (hd : 0 < d) (hnd : (polarBilin Q).Nondegenerate)
    (hT : ∃ S : Submodule K (Fin d → K), finrank K S = 3 ∧ ∀ v ∈ S, Q v = 0)
    {p : ℕ} (hp : p.Prime) (hp3 : 3 < p) (hpl : p ≠ ringChar K)
    (A : Subgroup (MulAut (matrixProjectiveDerived Q)))
    (hAH : A ≤ OuterAutomorphisms.inner (matrixProjectiveDerived Q))
    (hAe : CFSG.IsElementaryAbelian p A) (hAcard : Nat.card A = p ^ 2)
    {a : MulAut (matrixProjectiveDerived Q)} (haA : a ∈ A) (ha1 : a ≠ 1)
    {x : matrixDerived Q} (hxp : orderOf x = p)
    (hxa : MulAut.conj (matrixProjectiveProjection Q x) = a)
    (hS : IsSimpleGroup ↥(supportedFixedDerived Q (matrixLinearIso x.val)))
    (D : Subgroup (MulAut (matrixProjectiveDerived Q)))
    (hD : OuterAutomorphisms.inner (matrixProjectiveDerived Q) ≤ D)
    (hlist : FixedLayerListed Q (matrixLinearIso x.val)) :
    supportedInner Q (matrixFixedSpace x.val) ≤
        D ⊓ Subgroup.centralizer ({a} : Set (MulAut (matrixProjectiveDerived Q))) ∧
      CFSG.IsComponent ((supportedInner Q (matrixFixedSpace x.val)).subgroupOf
        (D ⊓ Subgroup.centralizer ({a} : Set (MulAut (matrixProjectiveDerived Q))))) := by
  obtain ⟨n, C, hn1, hn2, hsup, hC, hcomm⟩ :=
    kc_apply hd hnd hT hp hp3 hpl A hAH hAe hAcard haA ha1 hxp hxa D hD hlist
  have hx := oddOrderIsometry_matrix hnd hp hpl x hxp
  rcases (show n = 1 ∨ n = 2 by omega) with rfl | rfl
  · have hJ : fixedComponentImage Q (matrixLinearIso x.val) = C 0 := by
      rw [← hsup]
      exact (iSup_unique C).trans (congrArg C (Subsingleton.elim _ _))
    rw [supportedInner_eq_map hd hx, hJ]
    exact ⟨(hC 0).2.2.1, (hC 0).2.2.2⟩
  · exfalso
    have hne : fixedComponentImage Q (matrixLinearIso x.val) ≠ ⊥ := by
      intro h
      apply (hC 0).1
      rw [eq_bot_iff, ← h, ← hsup]
      exact le_iSup C 0
    have : IsSimpleGroup ↥(fixedComponentImage Q (matrixLinearIso x.val)) :=
      isSimpleGroup_fixedComponentImage hS hx.supportedFixedDerived_le_orthDerived hne
    have hsup2 : C 0 ⊔ C 1 = fixedComponentImage Q (matrixLinearIso x.val) := by
      rw [← hsup]
      refine le_antisymm (sup_le (le_iSup C 0) (le_iSup C 1)) (iSup_le fun i => ?_)
      fin_cases i
      · exact le_sup_left
      · exact le_sup_right
    have hX := eq_of_isSimpleGroup_of_sup_eq hsup2 (hC 0).1
      (fun u hu v hv => hcomm 0 1 (by decide) u hu v hv)
    have hY := eq_of_isSimpleGroup_of_sup_eq (sup_comm (C 0) (C 1) ▸ hsup2) (hC 1).1
      (fun u hu v hv => hcomm 1 0 (by decide) u hu v hv)
    have hcomm0 : ∀ u ∈ C 0, ∀ v ∈ C 0, u * v = v * u := fun u hu v hv =>
      hcomm 0 1 (by decide) u hu v (hY.trans hX.symm ▸ hv)
    have : Group.IsPerfect ↥(C 0) := (hC 0).2.1.1
    have : Nontrivial ↥(C 0) := (Subgroup.nontrivial_iff_ne_bot _).mpr (hC 0).1
    have : IsMulCommutative ↥(C 0) :=
      isMulCommutative_iff.mpr fun u v => Subtype.ext (hcomm0 u u.2 v v.2)
    exact Group.IsPerfect.not_isMulCommutative ↥(C 0) ‹_›

end KC

section Lift'

variable {K : Type} [Field K] [Finite K] {d : ℕ} {Q : QuadraticForm K (Fin d → K)}

theorem existsUnique_lift (hd : 0 < d) (hnd : (polarBilin Q).Nondegenerate)
    (hT : ∃ S : Submodule K (Fin d → K), finrank K S = 3 ∧ ∀ v ∈ S, Q v = 0)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {A : Subgroup (MulAut (matrixProjectiveDerived Q))}
    (hAH : A ≤ OuterAutomorphisms.inner (matrixProjectiveDerived Q))
    (hAe : CFSG.IsElementaryAbelian p A) {a : MulAut (matrixProjectiveDerived Q)} (haA : a ∈ A)
    (ha1 : a ≠ 1) :
    ∃! x : matrixDerived Q, orderOf x = p ∧ MulAut.conj (matrixProjectiveProjection Q x) = a := by
  have := hAe
  have : Fact p.Prime := ⟨hp⟩
  have hinj := conj_injective_matrixProjectiveDerived Q hd hnd hT
  obtain ⟨a', ha'⟩ := hAH haA
  have hap : orderOf a = p :=
    orderOf_eq_prime (CFSG.elemPow_eq_one_of_isElementaryAbelian a haA) ha1
  have hord' : orderOf a' = p := by
    rw [← hap, ← ha']
    exact (orderOf_injective _ hinj a').symm
  have hord : orderOf (bridgeEquiv Q hd a') = p := by
    rw [MulEquiv.orderOf_eq]
    exact hord'
  obtain ⟨-, -, -, -, -, -, -, -, hlift⟩ :=
    CFSG.RankThree.Classical.orthogonal_high_Witt_derived_quotient_and_odd_lifts hnd hT
  obtain ⟨x₀, ⟨hx₀a, hx₀p⟩, huniq, -⟩ := hlift p hp hp2 _ hord
  refine ⟨(derivedEquiv Q).symm x₀, ⟨?_, ?_⟩, ?_⟩
  · rw [MulEquiv.orderOf_eq]
    exact hx₀p
  · have : matrixProjectiveProjection Q ((derivedEquiv Q).symm x₀) = a' := by
      apply (bridgeEquiv Q hd).injective
      rw [bridgeEquiv_projection, MulEquiv.apply_symm_apply, hx₀a]
    rw [this]
    exact ha'
  · rintro y ⟨hyp, hya⟩
    have hπ : matrixProjectiveProjection Q y = a' := hinj (hya.trans ha'.symm)
    have : derivedEquiv Q y = x₀ :=
      huniq _ (by rw [← bridgeEquiv_projection Q hd y, hπ]) (by rw [MulEquiv.orderOf_eq]; exact hyp)
    exact (derivedEquiv Q).injective (by rw [this, MulEquiv.apply_symm_apply])

end Lift'

end CFSG.RankThree.PartOne.KCOrthogonalD4
