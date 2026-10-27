module

public import CFSG.LocalAnalysis.StandardType.GGSixE6TwoModel
import CFSG.Assembly.Subnormal

public section

namespace CFSG.StandardType.GGSixE6Two

open CFSG.Open

private theorem centralizer_map_mulEquiv {E E' : Type} [Group E] [Group E'] (θ : E ≃* E')
    (S : Set E) :
    (Subgroup.centralizer S).map θ.toMonoidHom =
      Subgroup.centralizer (θ.toMonoidHom '' S) := by
  apply le_antisymm
  · exact Subgroup.map_centralizer_le_centralizer_image S θ.toMonoidHom
  · have h := Subgroup.map_centralizer_le_centralizer_image (θ.toMonoidHom '' S)
      θ.symm.toMonoidHom
    have himg : θ.symm.toMonoidHom '' (θ.toMonoidHom '' S) = S := by
      ext x
      constructor
      · rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩
        simpa using hz
      · intro hx
        exact ⟨θ x, ⟨x, hx, rfl⟩, by simp⟩
    rw [himg] at h
    have h2 := Subgroup.map_mono (f := θ.toMonoidHom) h
    rwa [GGRootNorm.map_map_symm θ (Subgroup.centralizer (θ.toMonoidHom '' S))] at h2

private theorem centralizer_map_singleton {E E' : Type} [Group E] [Group E'] (θ : E ≃* E')
    (x : E) :
    (Subgroup.centralizer ({x} : Set E)).map θ.toMonoidHom =
      Subgroup.centralizer ({θ x} : Set E') := by
  rw [centralizer_map_mulEquiv, Set.image_singleton]
  rfl

private theorem centralizer_map_subgroup {E E' : Type} [Group E] [Group E'] (θ : E ≃* E')
    (J : Subgroup E) :
    (Subgroup.centralizer (J : Set E)).map θ.toMonoidHom =
      Subgroup.centralizer (J.map θ.toMonoidHom : Set E') := by
  rw [centralizer_map_mulEquiv]
  rfl

private theorem center_map_subtype_mulEquiv {E E' : Type} [Group E] [Group E'] (θ : E ≃* E')
    (Q : Subgroup E) :
    (Subgroup.center ↥(Q.map θ.toMonoidHom)).map (Q.map θ.toMonoidHom).subtype =
      ((Subgroup.center ↥Q).map Q.subtype).map θ.toMonoidHom := by
  let eQ : ↥Q ≃* ↥(Q.map θ.toMonoidHom) :=
    Q.equivMapOfInjective θ.toMonoidHom θ.injective
  have hfg : (Q.map θ.toMonoidHom).subtype.comp eQ.toMonoidHom =
      θ.toMonoidHom.comp Q.subtype := by
    ext x
    exact Subgroup.coe_equivMapOfInjective_apply Q θ.toMonoidHom θ.injective x
  have hcenter : (Subgroup.center ↥Q).map eQ.toMonoidHom =
      Subgroup.center ↥(Q.map θ.toMonoidHom) := Subgroup.map_center_eq eQ
  calc
    (Subgroup.center ↥(Q.map θ.toMonoidHom)).map (Q.map θ.toMonoidHom).subtype
        = ((Subgroup.center ↥Q).map eQ.toMonoidHom).map
            (Q.map θ.toMonoidHom).subtype := by
          rw [hcenter]
    _ = (Subgroup.center ↥Q).map ((Q.map θ.toMonoidHom).subtype.comp eQ.toMonoidHom) := by
          rw [Subgroup.map_map]
    _ = (Subgroup.center ↥Q).map (θ.toMonoidHom.comp Q.subtype) := by rw [hfg]
    _ = ((Subgroup.center ↥Q).map Q.subtype).map θ.toMonoidHom := by
          rw [← Subgroup.map_map]

private theorem map_mem_normalizer_of_mem_map_eq {E E' : Type} [Group E] [Group E']
    (θ : E ≃* E') {A : Subgroup E} {A' : Subgroup E'} (hA : A.map θ.toMonoidHom = A') {x : E}
    (hx : x ∈ Subgroup.normalizer (A : Set E)) :
    θ x ∈ Subgroup.normalizer (A' : Set E') := by
  subst hA
  rw [GGRootNorm.normalizer_map_mulEquiv θ A, Subgroup.mem_map]
  exact ⟨x, hx, rfl⟩

private theorem isComponentOf_map_mulEquiv_local {X Y : Type*} [Group X] [Group Y]
    (e : X ≃* Y) {J H : Subgroup X} (h : CFSG.Assembly.IsComponentOf J H) :
    CFSG.Assembly.IsComponentOf (J.map e.toMonoidHom) (H.map e.toMonoidHom) := by
  refine ⟨Subgroup.map_mono h.1, CFSG.Assembly.IsSubnormal.map e.toMonoidHom h.2.1, ?_⟩
  exact CFSG.Assembly.IsQuasisimple.of_mulEquiv
    (Subgroup.equivMapOfInjective J e.toMonoidHom e.injective).symm h.2.2

private theorem uclause_map_mulEquiv {E E' : Type} [Group E] [Group E'] (θ : E ≃* E')
    {R' J' : Subgroup E}
    (h : ∀ Q : Subgroup E, Q = pCoreOf 2 (Subgroup.normalizer (R' : Set E)) →
      ∀ U : Subgroup E, (Subgroup.center ↥Q).map Q.subtype ≤ U → U ≤ Q →
        U ≠ (Subgroup.center ↥Q).map Q.subtype → U ≠ Q →
        Subgroup.normalizer (R' : Set E) ≤ Subgroup.normalizer (U : Set E) →
        J' ⊔ U = ⊤) :
    ∀ Q'' : Subgroup E',
      Q'' = pCoreOf 2 (Subgroup.normalizer (R'.map θ.toMonoidHom : Set E')) →
      ∀ U'' : Subgroup E', (Subgroup.center ↥Q'').map Q''.subtype ≤ U'' → U'' ≤ Q'' →
        U'' ≠ (Subgroup.center ↥Q'').map Q''.subtype → U'' ≠ Q'' →
        Subgroup.normalizer (R'.map θ.toMonoidHom : Set E') ≤
          Subgroup.normalizer (U'' : Set E') →
        (J'.map θ.toMonoidHom) ⊔ U'' = ⊤ := by
  intro Q'' hQ'' U'' hcU hUQ hne1 hne2 hnorm
  let Q : Subgroup E := pCoreOf 2 (Subgroup.normalizer (R' : Set E))
  let U : Subgroup E := U''.map θ.symm.toMonoidHom
  have hUU : U.map θ.toMonoidHom = U'' := by
    dsimp only [U]
    exact GGRootNorm.map_map_symm θ U''
  have hQmap : Q.map θ.toMonoidHom = Q'' := by
    dsimp only [Q]
    rw [← GGRootNorm.pCoreOf_map_mulEquiv θ (Subgroup.normalizer (R' : Set E)),
      ← GGRootNorm.normalizer_map_mulEquiv θ R']
    exact hQ''.symm
  have hcenter : (Subgroup.center ↥Q'').map Q''.subtype =
      ((Subgroup.center ↥Q).map Q.subtype).map θ.toMonoidHom := by
    rw [← hQmap]
    exact center_map_subtype_mulEquiv θ Q
  have hcU' : (Subgroup.center ↥Q).map Q.subtype ≤ U := by
    have h1 := Subgroup.map_mono (f := θ.symm.toMonoidHom) hcU
    rw [hcenter] at h1
    rw [GGRootNorm.map_symm_map θ ((Subgroup.center ↥Q).map Q.subtype)] at h1
    exact h1
  have hUQ' : U ≤ Q := by
    have h1 := Subgroup.map_mono (f := θ.symm.toMonoidHom) hUQ
    rw [← hQmap, GGRootNorm.map_symm_map θ Q] at h1
    exact h1
  have hne1' : U ≠ (Subgroup.center ↥Q).map Q.subtype := by
    intro hU
    apply hne1
    calc U'' = U.map θ.toMonoidHom := hUU.symm
      _ = ((Subgroup.center ↥Q).map Q.subtype).map θ.toMonoidHom := by rw [hU]
      _ = (Subgroup.center ↥Q'').map Q''.subtype := hcenter.symm
  have hne2' : U ≠ Q := by
    intro hU
    apply hne2
    calc U'' = U.map θ.toMonoidHom := hUU.symm
      _ = Q.map θ.toMonoidHom := by rw [hU]
      _ = Q'' := hQmap
  have hnorm' : Subgroup.normalizer (R' : Set E) ≤ Subgroup.normalizer (U : Set E) := by
    have h1 := Subgroup.map_mono (f := θ.symm.toMonoidHom) hnorm
    rw [← GGRootNorm.normalizer_map_mulEquiv θ.symm (R'.map θ.toMonoidHom),
      GGRootNorm.map_symm_map θ R',
      ← GGRootNorm.normalizer_map_mulEquiv θ.symm U''] at h1
    exact h1
  have hres := h Q rfl U hcU' hUQ' hne1' hne2' hnorm'
  have hmap := congrArg (Subgroup.map θ.toMonoidHom) hres
  rw [Subgroup.map_sup, hUU,
    Subgroup.map_top_of_surjective θ.toMonoidHom θ.surjective] at hmap
  exact hmap

private theorem concl_of_centralizer_eq {E : Type} [Group E] {x y : E}
    (hxy : Subgroup.centralizer ({x} : Set E) = Subgroup.centralizer ({y} : Set E))
    {J' : Subgroup E} (h : GGSixE6A24Concl x J') : GGSixE6A24Concl y J' := by
  obtain ⟨R', J₀', hRJ, hRne, hRp, hJ0J, htop, hU, hinner, hlast⟩ := h
  refine ⟨R', J₀', hRJ, hRne, hRp, hJ0J, htop, hU, hinner, ?_⟩
  intro g hg3 hgne hgy hgJ K' hJK' hcomp
  have hgx : g ∈ Subgroup.centralizer ({x} : Set E) := by
    rw [hxy]
    exact hgy
  exact hlast g hg3 hgne hgx hgJ K' hJK' hcomp

theorem GGSixE6A24Concl.map_mulEquiv {E E' : Type} [Group E] [Group E'] (θ : E ≃* E') {x₀ : E}
    {J' : Subgroup E} (h : GGSixE6A24Concl x₀ J') :
    GGSixE6A24Concl (θ x₀) (J'.map θ.toMonoidHom) := by
  obtain ⟨R', J₀', hRJ, hRne, hRp, hJ0J, htop, hU, hinner, hlast⟩ := h
  refine ⟨R'.map θ.toMonoidHom, J₀'.map θ.toMonoidHom, Subgroup.map_mono hRJ, ?_, ?_,
    Subgroup.map_mono hJ0J, ?_, uclause_map_mulEquiv θ hU, ?_, ?_⟩
  · exact fun hbot =>
      hRne ((Subgroup.map_eq_bot_iff_of_injective R' θ.injective).mp hbot)
  · exact hRp.map θ.toMonoidHom
  · rw [GGRootNorm.normalizer_map_mulEquiv θ R',
      GGRootNorm.pCoreOf_map_mulEquiv θ (Subgroup.normalizer (R' : Set E)),
      ← Subgroup.map_sup, htop,
      Subgroup.map_top_of_surjective θ.toMonoidHom θ.surjective]
  · exact ggRootNormInner_map_mulEquiv θ hinner
  · intro g'' hg''3 hg''ne hg''x hg''J K'' hJK'' hcomp''
    let g : E := θ.symm g''
    let K' : Subgroup E := K''.map θ.symm.toMonoidHom
    have hg3 : g ^ 3 = 1 := by
      dsimp only [g]
      rw [← map_pow θ.symm g'' 3, hg''3, map_one]
    have hgne : g ≠ 1 := by
      intro hg1
      apply hg''ne
      have hgg : θ g = g'' := by
        dsimp only [g]
        simp
      rw [← hgg, hg1, map_one]
    have hx0 : (Subgroup.centralizer ({θ x₀} : Set E')).map θ.symm.toMonoidHom =
        Subgroup.centralizer ({x₀} : Set E) := by
      rw [centralizer_map_singleton]
      rw [show θ.symm (θ x₀) = x₀ by simp]
    have hgx : g ∈ Subgroup.centralizer ({x₀} : Set E) := by
      show θ.symm g'' ∈ Subgroup.centralizer ({x₀} : Set E)
      rw [← hx0, Subgroup.mem_map]
      exact ⟨g'', hg''x, rfl⟩
    have hJmap : (Subgroup.centralizer
          ((J'.map θ.toMonoidHom : Subgroup E') : Set E')).map θ.symm.toMonoidHom =
        Subgroup.centralizer (J' : Set E) := by
      rw [centralizer_map_subgroup, GGRootNorm.map_symm_map θ J']
    have hgJ : g ∈ Subgroup.centralizer (J' : Set E) := by
      show θ.symm g'' ∈ Subgroup.centralizer (J' : Set E)
      rw [← hJmap, Subgroup.mem_map]
      exact ⟨g'', hg''J, rfl⟩
    have hJK' : J' ≤ K' := by
      have h1 := Subgroup.map_mono (f := θ.symm.toMonoidHom) hJK''
      rw [GGRootNorm.map_symm_map θ J'] at h1
      exact h1
    have hcomp' : CFSG.Assembly.IsComponentOf K'
        (Subgroup.centralizer ({g} : Set E)) := by
      have h1 := isComponentOf_map_mulEquiv_local θ.symm hcomp''
      rw [centralizer_map_singleton] at h1
      simpa only [K', g] using h1
    obtain ⟨hNC, hrest⟩ := hlast g hg3 hgne hgx hgJ K' hJK' hcomp'
    refine ⟨?_, ?_⟩
    · exact ggRootNormNoCentral_of_map_injective θ.toMonoidHom θ.injective
        (K' := K') (R' := R') (K := K'') (R := R'.map θ.toMonoidHom)
        (GGRootNorm.map_map_symm θ K'') rfl hNC
    · rcases hrest with hI | hD
      · exact Or.inl (ggRootNormInner_of_map_injective θ.toMonoidHom θ.injective
          (K' := K') (R' := R') (K := K'') (R := R'.map θ.toMonoidHom)
          (GGRootNorm.map_map_symm θ K'') rfl hI)
      · obtain ⟨δ, hδg, hδR, hδdiag⟩ := hD
        refine Or.inr ⟨⟨θ (δ : E), map_mem_normalizer_of_mem_map_eq θ
          (GGRootNorm.map_map_symm θ K'') δ.2⟩, ?_, ?_, ?_⟩
        · rw [Subgroup.mem_centralizer_singleton_iff]
          have h1 : (δ : E) * g = g * (δ : E) :=
            (Subgroup.mem_centralizer_singleton_iff).mp hδg
          have h2 := congrArg θ h1
          rw [map_mul, map_mul] at h2
          rwa [show θ g = g'' by dsimp only [g]; simp] at h2
        · exact map_mem_normalizer_of_mem_map_eq θ rfl hδR
        · exact ggRootNormInnerDiag_of_map_injective θ.toMonoidHom θ.injective
            (K' := K') (R' := R') (K := K'') (R := R'.map θ.toMonoidHom)
            (GGRootNorm.map_map_symm θ K'') rfl rfl hδdiag

theorem GGSixE6A24Concl.congr_centralizer {E : Type} [Group E] {x y : E}
    (hxy : Subgroup.centralizer ({x} : Set E) = Subgroup.centralizer ({y} : Set E))
    {J' : Subgroup E} : GGSixE6A24Concl x J' ↔ GGSixE6A24Concl y J' :=
  ⟨concl_of_centralizer_eq hxy, concl_of_centralizer_eq hxy.symm⟩

end CFSG.StandardType.GGSixE6Two
