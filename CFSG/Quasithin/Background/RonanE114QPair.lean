module

public import CFSG.Quasithin.Background.RonanE114Cov

public section

namespace CFSG.Quasithin.RonanE114

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup.X6

@[expose] def HasQuotPair (X : Type) [Group X] (U : Subgroup X) (n : ℕ) : Prop :=
  ∃ (ι : Type) (P : ι → Subgroup X),
    (∀ α : MulAut X, U.map α.toMonoidHom = U → ∀ j, (P j).map α.toMonoidHom = P j) ∧
    (⨆ j, perfectCore (P j)) ⊔ U = ⊤ ∧
    ∀ j, ∃ (Y : Type) (_ : Group Y) (φ : ↥(perfectCore (P j)) →* Y),
      Rk1 n Y ∧ Function.Surjective φ ∧ IsPGroup 2 φ.ker

theorem HasQuotPair.map {X X' : Type} [Group X] [Group X'] [Finite X] [Finite X']
    {U : Subgroup X} {n : ℕ} (h : HasQuotPair X U n) (e : X ≃* X') :
    HasQuotPair X' (U.map e.toMonoidHom) n := by
  obtain ⟨ι, P, hinv, hgen, hφ⟩ := h
  refine ⟨ι, fun j => (P j).map e.toMonoidHom, ?_, ?_, ?_⟩
  · intro α' hα' j
    set α : MulAut X := e.trans (α'.trans e.symm) with hα
    have hαU : U.map α.toMonoidHom = U := by
      have h := hα'
      rw [map_comm_equiv] at h
      exact Subgroup.map_injective (f := e.toMonoidHom) e.injective h
    show ((P j).map e.toMonoidHom).map α'.toMonoidHom = (P j).map e.toMonoidHom
    rw [map_comm_equiv, ← hα, hinv α hαU j]
  · have h1 : ((⨆ j, perfectCore (P j)) ⊔ U).map e.toMonoidHom = ⊤ := by
      rw [hgen]
      exact Subgroup.map_top_of_surjective _ e.surjective
    rw [Subgroup.map_sup, Subgroup.map_iSup] at h1
    simp only [map_perfectCore] at h1
    exact h1
  · intro j
    obtain ⟨Y, _, φ, hY, hs, hk⟩ := hφ j
    let eP : ↥(perfectCore ((P j).map e.toMonoidHom)) ≃* ↥(perfectCore (P j)) :=
      (MulEquiv.subgroupCongr (map_perfectCore e.toMonoidHom (P j))).symm.trans
        ((perfectCore (P j)).equivMapOfInjective e.toMonoidHom e.injective).symm
    exact ⟨Y, inferInstance, φ.comp eP.toMonoidHom, hY, hs.comp eP.surjective,
      isPGroup_ker_comp φ eP hk⟩

theorem HasQuotPair.of_isSylow {X : Type} [Group X] [Finite X] {U₀ U : Subgroup X} {n : ℕ}
    (h₀ : HasQuotPair X U₀ n) (hU₀ : IsSylowTwoOf U₀ ⊤) (hU : IsSylowTwoOf U ⊤) :
    HasQuotPair X U n := by
  obtain ⟨k, -, hk⟩ := (isSylowTwoOf_iff_isSylowOf.1 hU₀).exists_mem_conj
    (isSylowTwoOf_iff_isSylowOf.1 hU)
  have hconj : U₀.map (MulAut.conj k).toMonoidHom = U := by
    ext x
    rw [Subgroup.mem_map_equiv]
    simp only [MulAut.conj_symm_apply]
    exact (hk x).symm
  have := h₀.map (MulAut.conj k)
  rwa [hconj] at this

variable {G : Type} [Group G] [Finite G]

theorem inEFor_of_hasQuotPair {L T : Subgroup G} (hLn : L.Normal) (hT : IsSylowIn 2 T ⊤)
    (hLT : L ⊔ T = ⊤) {X : Type} [Group X] (e : ↥L ≃* X) {U₀ : Subgroup X}
    (hU₀ : IsSylowTwoOf U₀ ⊤) {n : ℕ} (hP : HasQuotPair X U₀ n) : E1.InEFor n ⊤ T := by
  have : Finite X := Finite.of_equiv ↥L e.toEquiv
  have hTL : IsSylowTwoOf (T ⊓ L) L :=
    B6.isSylowTwoOf_inf_normal (⟨hT.1, hT.2.1, hT.2.2⟩ : IsSylowTwoOf T ⊤) le_top
      (by rw [Subgroup.normalizer_eq_top_iff.mpr hLn])
  have hSL : IsSylowTwoOf ((T ⊓ L).subgroupOf L) ⊤ := isSylowTwoOf_subgroupOf_top hTL
  set S : Subgroup X := ((T ⊓ L).subgroupOf L).map e.toMonoidHom with hSdef
  have hSX : IsSylowTwoOf S ⊤ := by
    refine isSylowTwoOf_iff_isSylowOf.2 ?_
    have := isSylowOf_map_injective (p := 2) e.toMonoidHom e.injective
      (isSylowTwoOf_iff_isSylowOf.1 hSL)
    rwa [Subgroup.map_top_of_surjective _ e.surjective] at this
  obtain ⟨ι, P, hinv, hgen, hφ⟩ := hP.of_isSylow hU₀ hSX
  let φ₀ : X →* G := L.subtype.comp e.symm.toMonoidHom
  have hφ₀ : Function.Injective φ₀ := Subtype.val_injective.comp e.symm.injective
  have hrange : φ₀.range = L := by
    ext g
    constructor
    · rintro ⟨x, rfl⟩
      exact (e.symm x).2
    · intro hg
      exact ⟨e ⟨g, hg⟩, by simp [φ₀]⟩
  have hxS : ∀ x : X, x ∈ S ↔ ((e.symm x : ↥L) : G) ∈ T := by
    intro x
    rw [hSdef, Subgroup.mem_map_equiv]
    constructor
    · intro h; exact h.1
    · intro h; exact ⟨h, (e.symm x).2⟩
  have hTN : T ≤ Subgroup.normalizer (L : Set G) := by
    rw [Subgroup.normalizer_eq_top_iff.mpr hLn]
    exact le_top
  have hinvT : ∀ r ∈ T, ∀ Q : Subgroup X,
      (∀ α : MulAut X, S.map α.toMonoidHom = S → Q.map α.toMonoidHom = Q) →
      r ∈ Subgroup.normalizer ((Q.map φ₀ : Subgroup G) : Set G) := by
    intro r hr Q hQ
    let ψ : MulAut ↥L := L.normalizerMonoidHom ⟨r, hTN hr⟩
    let α : MulAut X := e.symm.trans (ψ.trans e)
    have hψ : ∀ y : ↥L, ((ψ y : ↥L) : G) = r * (y : G) * r⁻¹ := fun y =>
      Subgroup.normalizerMonoidHom_apply_apply_coe L ⟨r, hTN hr⟩ y
    have hφα : ∀ x, φ₀ (α x) = r * φ₀ x * r⁻¹ := by
      intro x
      show (((e.symm (e (ψ (e.symm x)))) : ↥L) : G) = r * ((e.symm x : ↥L) : G) * r⁻¹
      rw [MulEquiv.symm_apply_apply]
      exact hψ _
    have hαx : ∀ x : X, α x ∈ S ↔ x ∈ S := by
      intro x
      rw [hxS, hxS]
      have : ((e.symm (α x) : ↥L) : G) = r * ((e.symm x : ↥L) : G) * r⁻¹ := hφα x
      rw [this]
      constructor
      · intro h
        have h1 : r⁻¹ * (r * ((e.symm x : ↥L) : G) * r⁻¹) * r ∈ T :=
          T.mul_mem (T.mul_mem (T.inv_mem hr) h) hr
        simpa [mul_assoc] using h1
      · intro h
        exact T.mul_mem (T.mul_mem hr h) (T.inv_mem hr)
    have hαS : S.map α.toMonoidHom = S := by
      ext y
      rw [Subgroup.mem_map_equiv]
      obtain ⟨x, rfl⟩ := α.surjective y
      rw [MulEquiv.symm_apply_apply]
      exact (hαx x).symm
    have hQα := hQ α hαS
    rw [Subgroup.mem_normalizer_iff_map_conj_eq, Subgroup.map_map]
    have hcomp : ((MulAut.conj r : MulAut G) : G →* G).comp φ₀ = φ₀.comp α.toMonoidHom := by
      ext x
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
      exact (hφα x).symm
    rw [hcomp, ← Subgroup.map_map, hQα]
  set Xs : ι → Subgroup G := fun j => (perfectCore (P j)).map φ₀ with hXs
  have hX : ∀ j, Xs j = perfectCore ((P j).map φ₀) := fun j => map_perfectCore φ₀ (P j)
  have hTX : ∀ j, T ≤ Subgroup.normalizer (Xs j : Set G) := fun j t ht => by
    have h1 : t ∈ Subgroup.normalizer (((P j).map φ₀ : Subgroup G) : Set G) :=
      hinvT t ht (P j) (fun α hα => hinv α hα j)
    have h2 := (normalizer_le_normalizer_perfectCore ((P j).map φ₀)) h1
    rwa [← hX j] at h2
  have hφX : ∀ j, ∃ (Y : Type) (_ : Group Y) (ψ : ↥(Xs j) →* Y), Rk1 n Y ∧
      Function.Surjective ψ ∧ IsPGroup 2 ψ.ker := by
    intro j
    obtain ⟨Y, _, φ, hY, hs, hk⟩ := hφ j
    let eP : ↥(Xs j) ≃* ↥(perfectCore (P j)) :=
      ((perfectCore (P j)).equivMapOfInjective φ₀ hφ₀).symm
    exact ⟨Y, inferInstance, φ.comp eP.toMonoidHom, hY, hs.comp eP.surjective,
      isPGroup_ker_comp φ eP hk⟩
  have hSmap : S.map φ₀ = T ⊓ L := by
    rw [hSdef, Subgroup.map_map]
    have : φ₀.comp e.toMonoidHom = L.subtype := by
      ext x
      simp [φ₀]
    rw [this, Subgroup.subgroupOf_map_subtype, inf_assoc, inf_idem]
  have hgenG : (⨆ j, Xs j) ⊔ T = ⊤ := by
    have h2 := congrArg (Subgroup.map φ₀) hgen
    rw [Subgroup.map_sup, Subgroup.map_iSup, ← MonoidHom.range_eq_map, hrange, hSmap] at h2
    rw [eq_top_iff, ← hLT]
    exact sup_le (h2.symm.le.trans (sup_le le_sup_left (inf_le_left.trans le_sup_right)))
      le_sup_right
  exact inEFor_top_of_quot_gen Xs hT hTX hφX hgenG

end CFSG.Quasithin.RonanE114
