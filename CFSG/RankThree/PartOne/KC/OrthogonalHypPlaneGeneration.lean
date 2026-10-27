module

public import CFSG.RankThree.PartOne.KC.OrthogonalAnchoredGeneration

public section

namespace CFSG.RankThree.PartOne.KCOrthogonal

open Module QuadraticMap CFSG.RankThree.Classical2 CFSG.ClassicalGroups.Orthogonal
  CFSG.LieType.SeitzGeneration CFSG.LocalAnalysis.ComponentInitial

variable {K : Type} [Field K] [Finite K] [CharP K 2] {V : Type} [AddCommGroup V]
  [Module K V] [FiniteDimensional K V] {Q : QuadraticForm K V}

omit [Finite K] [FiniteDimensional K V] in
private theorem nondegenerate_hypPlane (P : HypPair Q) :
    (polarBilin (Q.comp (Submodule.span K {P.e, P.f}).subtype)).Nondegenerate :=
  CFSG.RankThree.PartOne.K159.nondegenerate_of_regOn
    (polarNondegOn_span_pair_of_polar_eq_one P.polar_ef)

omit [CharP K 2] [FiniteDimensional K V] in
private theorem nondegenerate_anisotropic_plane {A : Submodule K V}
    (hAdim : finrank K A = 2) (hAaniso : ∀ u ∈ A, Q u = 0 → u = 0) :
    (polarBilin (Q.comp A.subtype)).Nondegenerate := by
  refine CFSG.LocalAnalysis.ComponentInitial.finite_anisotropic_plane_regular ?_ ?_
  · rw [hAdim]
  · intro x hx hQx
    exact hx (Subtype.ext (hAaniso x x.2 hQx))

omit [CharP K 2] [FiniteDimensional K V] in
private theorem nondegenerate_anisotropic_sup {A B : Submodule K V}
    (hAdim : finrank K A = 2) (hBdim : finrank K B = 2)
    (hAaniso : ∀ u ∈ A, Q u = 0 → u = 0) (hBaniso : ∀ u ∈ B, Q u = 0 → u = 0)
    (hAB : ∀ u ∈ A, ∀ v ∈ B, polar Q u v = 0) :
    (polarBilin (Q.comp (A ⊔ B).subtype)).Nondegenerate := by
  refine CFSG.RankThree.PartOne.K159.nondegenerate_of_regOn ?_
  refine CFSG.LieType.SeitzGeneration.OrthBlk.polarNondegOn_sup
    (polarNondegOn_of_nondegenerate (nondegenerate_anisotropic_plane hAdim hAaniso))
    (polarNondegOn_of_nondegenerate (nondegenerate_anisotropic_plane hBdim hBaniso)) ?_
  intro u hu v hv
  exact hAB u hu v hv

omit [FiniteDimensional K V] in
private theorem nondegenerate_hypPlane_sup_sup (P : HypPair Q) {A B : Submodule K V}
    (hAdim : finrank K A = 2) (hBdim : finrank K B = 2)
    (hAaniso : ∀ u ∈ A, Q u = 0 → u = 0) (hBaniso : ∀ u ∈ B, Q u = 0 → u = 0)
    (hHA : ∀ w ∈ Submodule.span K {P.e, P.f}, ∀ u ∈ A, polar Q w u = 0)
    (hHB : ∀ w ∈ Submodule.span K {P.e, P.f}, ∀ u ∈ B, polar Q w u = 0)
    (hAB : ∀ u ∈ A, ∀ v ∈ B, polar Q u v = 0) :
    (polarBilin (Q.comp (Submodule.span K {P.e, P.f} ⊔ (A ⊔ B)).subtype)).Nondegenerate := by
  refine CFSG.RankThree.PartOne.K159.nondegenerate_of_regOn ?_
  have hABpoly : PolarNondegOn Q (A ⊔ B) :=
    polarNondegOn_of_nondegenerate
      (nondegenerate_anisotropic_sup hAdim hBdim hAaniso hBaniso hAB)
  refine CFSG.LieType.SeitzGeneration.OrthBlk.polarNondegOn_sup
    (polarNondegOn_of_nondegenerate (nondegenerate_hypPlane P)) hABpoly ?_
  intro w hw x hx
  obtain ⟨u, hu, v, hv, rfl⟩ := Submodule.mem_sup.mp hx
  rw [polar_add_right, hHA w hw u hu, hHB w hw v hv, add_zero]

omit [FiniteDimensional K V] in
private theorem nondegenerate_hypPlane_sup (P : HypPair Q) {A : Submodule K V}
    (hAdim : finrank K A = 2) (hAaniso : ∀ u ∈ A, Q u = 0 → u = 0)
    (hHA : ∀ w ∈ Submodule.span K {P.e, P.f}, ∀ u ∈ A, polar Q w u = 0) :
    (polarBilin (Q.comp (Submodule.span K {P.e, P.f} ⊔ A).subtype)).Nondegenerate := by
  refine CFSG.RankThree.PartOne.K159.nondegenerate_of_regOn ?_
  refine CFSG.LieType.SeitzGeneration.OrthBlk.polarNondegOn_sup
    (polarNondegOn_of_nondegenerate (nondegenerate_hypPlane P))
    (polarNondegOn_of_nondegenerate (nondegenerate_anisotropic_plane hAdim hAaniso)) ?_
  intro w hw u hu
  exact hHA w hw u hu

omit [Finite K] [CharP K 2] [FiniteDimensional K V] in
private theorem comap_span_eq_span (P : HypPair Q) {H S : Submodule K V} (hHS : H ≤ S)
    (hH : H = Submodule.span K {P.e, P.f}) (Ps : HypPair (Q.comp S.subtype))
    (he : (Ps.e : V) = P.e) (hf : (Ps.f : V) = P.f) :
    H.comap S.subtype = Submodule.span K {Ps.e, Ps.f} ∧
      (H.comap S.subtype).map S.subtype = H := by
  constructor
  · apply Submodule.map_injective_of_injective S.subtype_injective
    rw [Submodule.map_comap_subtype, inf_eq_right.mpr hHS, Submodule.map_span, Set.image_pair]
    simp [hH, he, hf]
  · rw [Submodule.map_comap_subtype, inf_eq_right.mpr hHS]

omit [Finite K] [CharP K 2] [FiniteDimensional K V] in
private theorem comap_plane_map_finrank {A B S : Submodule K V} (hAS : A ≤ S) (hBS : B ≤ S)
    (hAdim : finrank K A = 2) (hBdim : finrank K B = 2) :
    (∀ k : Fin 2,
        ((![A.comap S.subtype, B.comap S.subtype] : Fin 2 → Submodule K S) k).map
            S.subtype = ![A, B] k) ∧
      ∀ k : Fin 2,
        finrank K ((![A.comap S.subtype, B.comap S.subtype] : Fin 2 → Submodule K S) k) = 2 := by
  constructor
  · intro k
    fin_cases k
    · change (A.comap S.subtype).map S.subtype = A
      rw [Submodule.map_comap_subtype, inf_eq_right.mpr hAS]
    · change (B.comap S.subtype).map S.subtype = B
      rw [Submodule.map_comap_subtype, inf_eq_right.mpr hBS]
  · intro k
    fin_cases k
    · exact (Submodule.comapSubtypeEquivOfLe hAS).finrank_eq.trans hAdim
    · exact (Submodule.comapSubtypeEquivOfLe hBS).finrank_eq.trans hBdim

omit [Finite K] [CharP K 2] [FiniteDimensional K V] in
private theorem comap_plane_aniso_orthogonal (P : HypPair Q) {A B S : Submodule K V}
    (hAaniso : ∀ u ∈ A, Q u = 0 → u = 0) (hBaniso : ∀ u ∈ B, Q u = 0 → u = 0)
    (hHA : ∀ w ∈ Submodule.span K {P.e, P.f}, ∀ u ∈ A, polar Q w u = 0)
    (hHB : ∀ w ∈ Submodule.span K {P.e, P.f}, ∀ u ∈ B, polar Q w u = 0)
    (hAB : ∀ u ∈ A, ∀ v ∈ B, polar Q u v = 0) :
    (∀ k : Fin 2,
        ∀ u ∈ (![A.comap S.subtype, B.comap S.subtype] : Fin 2 → Submodule K S) k,
          (Q.comp S.subtype) u = 0 → u = 0) ∧
      (∀ k : Fin 2, ∀ w ∈ (Submodule.span K {P.e, P.f}).comap S.subtype,
        ∀ u ∈ (![A.comap S.subtype, B.comap S.subtype] : Fin 2 → Submodule K S) k,
          polar (Q.comp S.subtype) w u = 0) ∧
      (∀ k l : Fin 2, k ≠ l →
        ∀ u ∈ (![A.comap S.subtype, B.comap S.subtype] : Fin 2 → Submodule K S) k,
          ∀ v ∈ (![A.comap S.subtype, B.comap S.subtype] : Fin 2 → Submodule K S) l,
            polar (Q.comp S.subtype) u v = 0) := by
  refine ⟨?_, ?_, ?_⟩
  · intro k u hu hQu
    fin_cases k
    · exact Subtype.ext (hAaniso (u : V) (Submodule.mem_comap.mp hu) (by simpa using hQu))
    · exact Subtype.ext (hBaniso (u : V) (Submodule.mem_comap.mp hu) (by simpa using hQu))
  · intro k w hw u hu
    rw [polar_comp_subtype_eq]
    fin_cases k
    · exact hHA (w : V) (Submodule.mem_comap.mp hw) (u : V) (Submodule.mem_comap.mp hu)
    · exact hHB (w : V) (Submodule.mem_comap.mp hw) (u : V) (Submodule.mem_comap.mp hu)
  · intro k l hkl u hu v hv
    rw [polar_comp_subtype_eq]
    fin_cases k <;> fin_cases l
    · exact absurd rfl hkl
    · exact hAB (u : V) (Submodule.mem_comap.mp hu) (v : V) (Submodule.mem_comap.mp hv)
    · rw [polar_comm]
      exact hAB (v : V) (Submodule.mem_comap.mp hv) (u : V) (Submodule.mem_comap.mp hu)
    · exact absurd rfl hkl

omit [Finite K] [CharP K 2] [FiniteDimensional K V] in
private theorem comap_span_sup_eq_top (P : HypPair Q) {A B S : Submodule K V}
    (hS : S = Submodule.span K {P.e, P.f} ⊔ (A ⊔ B))
    (hHsMap : ((Submodule.span K {P.e, P.f}).comap S.subtype).map S.subtype =
      Submodule.span K {P.e, P.f})
    (hUsMap : ∀ k : Fin 2,
      ((![A.comap S.subtype, B.comap S.subtype] : Fin 2 → Submodule K S) k).map S.subtype =
        ![A, B] k) :
    (Submodule.span K {P.e, P.f}).comap S.subtype ⊔
        ⨆ k : Fin 2, (![A.comap S.subtype, B.comap S.subtype] : Fin 2 → Submodule K S) k = ⊤ := by
  apply Submodule.map_injective_of_injective S.subtype_injective
  rw [Submodule.map_sup, Submodule.map_iSup, Submodule.map_top, Submodule.range_subtype,
    hHsMap]
  have hUsup : (⨆ k : Fin 2,
      ((![A.comap S.subtype, B.comap S.subtype] : Fin 2 → Submodule K S) k).map S.subtype) =
      A ⊔ B := by
    have hsup : (Finset.univ : Finset (Fin 2)).sup
        (fun k =>
          ((![A.comap S.subtype, B.comap S.subtype] : Fin 2 → Submodule K S) k).map S.subtype) =
        ⨆ k : Fin 2,
          ((![A.comap S.subtype, B.comap S.subtype] : Fin 2 → Submodule K S) k).map S.subtype := by
      rw [Finset.sup_eq_iSup]
      simp
    rw [← hsup, show (Finset.univ : Finset (Fin 2)) = {0, 1} from by decide]
    simp [hUsMap]
  rw [hUsup, ← hS]

private theorem iSup_map_supportedDerived_pullback_eq (P : HypPair Q) {A B S : Submodule K V}
    (hHS : (Submodule.span K {P.e, P.f}) ≤ S) (hAS : A ≤ S) (hBS : B ≤ S)
    (hAdim : finrank K A = 2) (hBdim : finrank K B = 2)
    (hAaniso : ∀ u ∈ A, Q u = 0 → u = 0) (hBaniso : ∀ u ∈ B, Q u = 0 → u = 0)
    (hHA : ∀ w ∈ Submodule.span K {P.e, P.f}, ∀ u ∈ A, polar Q w u = 0)
    (hHB : ∀ w ∈ Submodule.span K {P.e, P.f}, ∀ u ∈ B, polar Q w u = 0)
    (hSreg : (polarBilin (Q.comp S.subtype)).Nondegenerate)
    (Hs : Submodule K S)
    (hHsMap : Hs.map S.subtype = Submodule.span K {P.e, P.f})
    (Us : Fin 2 → Submodule K S) (hUsMap : ∀ k : Fin 2, (Us k).map S.subtype = ![A, B] k) :
    (⨆ k : Fin 2,
        (supportedDerived (Q.comp S.subtype) (Hs ⊔ Us k)).map
          (orthExtend (isCompl_suppPerp (polarNondegOn_of_nondegenerate hSreg)))) =
      ⨆ k : Fin 2, supportedDerived Q (Submodule.span K {P.e, P.f} ⊔ ![A, B] k) := by
  have hsup_le : ∀ k : Fin 2, Submodule.span K {P.e, P.f} ⊔ ![A, B] k ≤ S := by
    intro k
    fin_cases k
    · exact sup_le hHS hAS
    · exact sup_le hHS hBS
  have hcomap : ∀ k : Fin 2,
      (Submodule.span K {P.e, P.f} ⊔ ![A, B] k).comap S.subtype = Hs ⊔ Us k := by
    intro k
    apply Submodule.map_injective_of_injective S.subtype_injective
    rw [Submodule.map_comap_subtype, inf_eq_right.mpr (hsup_le k), Submodule.map_sup,
      hHsMap, hUsMap k]
  have htermreg : ∀ k : Fin 2,
      (polarBilin (Q.comp (Submodule.span K {P.e, P.f} ⊔ ![A, B] k).subtype)).Nondegenerate := by
    intro k
    fin_cases k
    · exact nondegenerate_hypPlane_sup P hAdim hAaniso hHA
    · exact nondegenerate_hypPlane_sup P hBdim hBaniso hHB
  refine iSup_congr fun k => ?_
  rw [← hcomap k]
  exact map_supportedDerived_comap_subtype_eq_supportedDerived
    (hsup_le k) (htermreg k) hSreg

private theorem supportedDerived_hypPlane_sup_sup_eq_iSup (P : HypPair Q) {A B : Submodule K V}
    (hAdim : Module.finrank K A = 2) (hBdim : Module.finrank K B = 2)
    (hAaniso : ∀ u ∈ A, Q u = 0 → u = 0) (hBaniso : ∀ u ∈ B, Q u = 0 → u = 0)
    (hHA : ∀ w ∈ Submodule.span K {P.e, P.f}, ∀ u ∈ A, polar Q w u = 0)
    (hHB : ∀ w ∈ Submodule.span K {P.e, P.f}, ∀ u ∈ B, polar Q w u = 0)
    (hAB : ∀ u ∈ A, ∀ v ∈ B, polar Q u v = 0) :
    supportedDerived Q (Submodule.span K {P.e, P.f} ⊔ (A ⊔ B)) =
      ⨆ k : Fin 2, supportedDerived Q (Submodule.span K {P.e, P.f} ⊔ ![A, B] k) := by
  classical
  let H : Submodule K V := Submodule.span K {P.e, P.f}
  let S : Submodule K V := H ⊔ (A ⊔ B)
  have hHS : H ≤ S := le_sup_left
  have hAS : A ≤ S := le_sup_left.trans le_sup_right
  have hBS : B ≤ S := le_sup_right.trans le_sup_right
  have hSreg : (polarBilin (Q.comp S.subtype)).Nondegenerate :=
    nondegenerate_hypPlane_sup_sup P hAdim hBdim hAaniso hBaniso hHA hHB hAB
  let Us : Fin 2 → Submodule K S := ![A.comap S.subtype, B.comap S.subtype]
  let Hs : Submodule K S := H.comap S.subtype
  let Ps : HypPair (Q.comp S.subtype) :=
    { e := ⟨P.e, hHS (Submodule.subset_span (by simp))⟩
      f := ⟨P.f, hHS (Submodule.subset_span (by simp))⟩
      Q_e := P.Q_e
      Q_f := P.Q_f
      polar_ef := by rw [polar_comp_subtype_eq]; exact P.polar_ef }
  obtain ⟨hHs, hHsMap⟩ := comap_span_eq_span P hHS rfl Ps rfl rfl
  obtain ⟨hUsMap, hUsdim⟩ := comap_plane_map_finrank hAS hBS hAdim hBdim
  obtain ⟨hUsaniso, hUsHU, hUsUU⟩ :=
    comap_plane_aniso_orthogonal P hAaniso hBaniso hHA hHB hAB
  have hspan := comap_span_sup_eq_top P rfl hHsMap hUsMap
  have hgen := orthDerived_eq_iSup_supportedDerived_of_hypPair
    (Q := Q.comp S.subtype) (P := Ps) (W := Hs) (U := Us) (m := 2)
    (by norm_num) hHs hUsdim hUsaniso hUsHU hUsUU hspan
  let ext := orthExtend (isCompl_suppPerp (polarNondegOn_of_nondegenerate hSreg))
  have hmap := congrArg (Subgroup.map ext) hgen
  rw [map_orthDerived_orthExtend_eq_supportedDerived_of_regular hSreg,
    Subgroup.map_iSup] at hmap
  exact hmap.trans (iSup_map_supportedDerived_pullback_eq P hHS hAS hBS hAdim hBdim
    hAaniso hBaniso hHA hHB hSreg Hs hHsMap Us hUsMap)

omit [Finite K] [CharP K 2] [FiniteDimensional K V] in
private theorem iSup_fin_two_hypPlane (P : HypPair Q) (A B : Submodule K V) :
    (⨆ k : Fin 2, supportedDerived Q (Submodule.span K {P.e, P.f} ⊔ ![A, B] k)) =
      supportedDerived Q (Submodule.span K {P.e, P.f} ⊔ A) ⊔
        supportedDerived Q (Submodule.span K {P.e, P.f} ⊔ B) := by
  have hsup : (Finset.univ : Finset (Fin 2)).sup
      (fun k => supportedDerived Q (Submodule.span K {P.e, P.f} ⊔ ![A, B] k)) =
      ⨆ k : Fin 2, supportedDerived Q (Submodule.span K {P.e, P.f} ⊔ ![A, B] k) := by
    rw [Finset.sup_eq_iSup]
    simp
  rw [← hsup, show (Finset.univ : Finset (Fin 2)) = {0, 1} from by decide]
  simp

theorem supportedDerived_hypPlane_sup_sup_eq (P : HypPair Q) {A B : Submodule K V}
    (hAdim : Module.finrank K A = 2) (hBdim : Module.finrank K B = 2)
    (hAaniso : ∀ u ∈ A, Q u = 0 → u = 0) (hBaniso : ∀ u ∈ B, Q u = 0 → u = 0)
    (hHA : ∀ w ∈ Submodule.span K {P.e, P.f}, ∀ u ∈ A, polar Q w u = 0)
    (hHB : ∀ w ∈ Submodule.span K {P.e, P.f}, ∀ u ∈ B, polar Q w u = 0)
    (hAB : ∀ u ∈ A, ∀ v ∈ B, polar Q u v = 0) :
    supportedDerived Q (Submodule.span K {P.e, P.f} ⊔ (A ⊔ B)) =
      supportedDerived Q (Submodule.span K {P.e, P.f} ⊔ A) ⊔
        supportedDerived Q (Submodule.span K {P.e, P.f} ⊔ B) :=
  (supportedDerived_hypPlane_sup_sup_eq_iSup P hAdim hBdim hAaniso hBaniso hHA hHB hAB).trans
    (iSup_fin_two_hypPlane P A B)

theorem supportedDerived_hypPlane_sup_le (P : HypPair Q) {A B : Submodule K V}
    (hAdim : Module.finrank K A = 2) (hBdim : Module.finrank K B = 2)
    (hAaniso : ∀ u ∈ A, Q u = 0 → u = 0) (hBaniso : ∀ u ∈ B, Q u = 0 → u = 0)
    (hHA : ∀ w ∈ Submodule.span K {P.e, P.f}, ∀ u ∈ A, polar Q w u = 0)
    (hHB : ∀ w ∈ Submodule.span K {P.e, P.f}, ∀ u ∈ B, polar Q w u = 0)
    (hAB : ∀ u ∈ A, ∀ v ∈ B, polar Q u v = 0) {g : V ≃ₗ[K] V}
    (hg : g ∈ supportedDerived Q (A ⊔ B))
    (hgH : ∀ w ∈ Submodule.span K {P.e, P.f}, g w = w) (hgA : A.map g.toLinearMap = B) :
    supportedDerived Q (Submodule.span K {P.e, P.f} ⊔ (A ⊔ B)) ≤
      supportedDerived Q (Submodule.span K {P.e, P.f} ⊔ A) ⊔ supportedDerived Q (A ⊔ B) := by
  classical
  let H : Submodule K V := Submodule.span K {P.e, P.f}
  let X : Subgroup (V ≃ₗ[K] V) := supportedDerived Q (H ⊔ A)
  let Y : Subgroup (V ≃ₗ[K] V) := supportedDerived Q (H ⊔ B)
  let Z : Subgroup (V ≃ₗ[K] V) := supportedDerived Q (A ⊔ B)
  have hEq : supportedDerived Q (H ⊔ (A ⊔ B)) = X ⊔ Y :=
    supportedDerived_hypPlane_sup_sup_eq P hAdim hBdim hAaniso hBaniso hHA hHB hAB
  have hHmap : H.map g.toLinearMap = H := by
    apply le_antisymm
    · rintro x ⟨w, hw, rfl⟩
      change g w ∈ H
      rw [hgH w hw]
      exact hw
    · intro x hx
      exact ⟨x, hx, by simpa using hgH x hx⟩
  have hR : (H ⊔ A).map g.toLinearMap = H ⊔ B := by
    rw [Submodule.map_sup, hHmap, hgA]
  have hZreg : (polarBilin (Q.comp (A ⊔ B).subtype)).Nondegenerate :=
    nondegenerate_anisotropic_sup hAdim hBdim hAaniso hBaniso hAB
  have hgO : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
    supportedDerived_le_orthogonalGroup (polarNondegOn_of_nondegenerate hZreg) hg
  have hconj : (supportedDerived Q (H ⊔ A)).map (MulAut.conj g).toMonoidHom =
      supportedDerived Q (H ⊔ B) :=
    map_supportedDerived_conj_of_map_eq g hgO hR
  have hYle : Y ≤ X ⊔ Z := by
    change supportedDerived Q (H ⊔ B) ≤ X ⊔ Z
    rw [← hconj]
    rintro y ⟨x, hx, rfl⟩
    have hxX : x ∈ X ⊔ Z := Subgroup.mem_sup_left hx
    have hgX : g ∈ X ⊔ Z := Subgroup.mem_sup_right hg
    have hmem : g * x * g⁻¹ ∈ X ⊔ Z := mul_mem (mul_mem hgX hxX) (inv_mem hgX)
    simpa [MulAut.conj_apply] using hmem
  calc
    supportedDerived Q (H ⊔ (A ⊔ B)) = X ⊔ Y := hEq
    _ ≤ X ⊔ Z := sup_le le_sup_left hYle

end CFSG.RankThree.PartOne.KCOrthogonal
