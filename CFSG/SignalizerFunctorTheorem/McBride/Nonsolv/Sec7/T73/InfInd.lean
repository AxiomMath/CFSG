module

public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Sec7.T73.Basic
public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Sec7.T73.InfLines
public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Sec7.T73.InfSylow

public section

open CFSG.Open

universe u

namespace CFSG.SignalizerFunctorTheorem.McBride.Nonsolv

namespace T73Inf

variable {p : ℕ} {G : Type u} [Group G] [Finite G] {A : Subgroup G} {θ : G → Subgroup G}
  {r : ℕ} {S : Subgroup G} {E K : Subgroup G}

theorem exists_lcal_of_mem_ind_plane
    (h : Counterexample p A θ) (hB : TypeBCore p A θ E K)
    {F : Subgroup G} (hF : F ∈ signalizerFunctorEk p 1 A) (hFE : F ≠ E) {P : Subgroup G}
    (hP : P ∈ Ind (thetaOf θ (E ⊔ F))) :
    ∃ R ∈ lcal (thetaOf θ F), P = R ⊓ Subgroup.centralizer (E : Set G) ∧
      sSup (Ind (thetaOf θ (E ⊔ F)) \ {P}) ≤ sSup (lcal (thetaOf θ F) \ {R}) := by
  have hind := Counterexample.ind_plane_eq_inf_centralizer_of_typeB h hB hF hFE
  have hP' := hP
  rw [hind] at hP'
  obtain ⟨R, hR, rfl⟩ := hP'
  refine ⟨R, hR, rfl, sSup_le ?_⟩
  rintro Q ⟨hQ, hQne⟩
  rw [hind] at hQ
  obtain ⟨R', hR', rfl⟩ := hQ
  have hRR' : R' ≠ R := fun heq => hQne (by rw [heq]; rfl)
  exact inf_le_left.trans (le_sSup ⟨hR', hRR'⟩)

theorem mem_zOf_inf_centralizer_of_mul_eq
    (h : Counterexample p A θ) (hr : InPiTheta A θ r)
    (hS : IsSr p A θ r S) (hB : TypeBCore p A θ E K) {F : Subgroup G}
    (hF : F ∈ signalizerFunctorEk p 1 A) (hFE : F ≠ E) {P : Subgroup G}
    (hP : P ∈ Ind (thetaOf θ (E ⊔ F))) {y t l : G}
    (hy : y ∈ zOf (S ⊓ Subgroup.centralizer (F : Set G))) (ht : t ∈ P)
    (hl : l ∈ sSup (Ind (thetaOf θ (E ⊔ F)) \ {P})) (hytl : t * l = y) :
    t ∈ zOf (S ⊓ Subgroup.centralizer (F : Set G)) ⊓ Subgroup.centralizer (E : Set G) := by
  obtain ⟨R, hR, rfl, hsub⟩ := exists_lcal_of_mem_ind_plane h hB hF hFE hP
  obtain ⟨hle, hp, hidx, -⟩ := Counterexample.T73a.sylow_line h hr hS hF
  have hΩ := (Counterexample.isRegFam_line_of_typeB h hB hF hFE).isDirectProduct
  obtain ⟨htR, htE⟩ := Subgroup.mem_inf.mp ht
  exact Subgroup.mem_inf.mpr
    ⟨mem_zOf_of_mul_eq hΩ hr.1 hle hp hidx hR hy htR (hsub hl) hytl, htE⟩

theorem inf_inf_le_projIn
    (h : Counterexample p A θ) (hr : InPiTheta A θ r)
    (hS : IsSr p A θ r S) (hB : TypeBCore p A θ E K) {F K' : Subgroup G}
    (hF : F ∈ signalizerFunctorEk p 1 A) (hFE : F ≠ E) (hK' : K' ∈ signalizerFunctorEk p 1 A)
    (hK'F : (E ⊔ F) ⊓ K' = ⊥) {P : Subgroup G} (hP : P ∈ Ind (thetaOf θ (E ⊔ F))) :
    zOf (S ⊓ Subgroup.centralizer (E : Set G)) ⊓ zOf (S ⊓ Subgroup.centralizer (F : Set G)) ⊓ P ≤
      projIn (Ind (thetaOf θ (E ⊔ F))) P (zOf S ⊓ Subgroup.centralizer (A : Set G)) := by
  have hπ := h.sup_mem_E2_of_ne hB.mem hF hFE.symm
  have hΩ := Counterexample.isRegFam_ind_plane_of_typeB h hB hF hFE
  have hnorm := le_normalizer_inf_zOf h hS hB.mem.1 hF.1
  refine le_projIn_of_smear_le hΩ.isDirectProduct
    (fun a ha J hJ => hΩ.map_conj_mem a (hK'.1 ha) J hJ) ?_ ?_ hP inf_le_right ?_
  · intro a ha ha1 J hJ
    refine hΩ.map_conj_ne (hK'.1 ha) (fun haN => ha1 ?_) hJ
    have h1 : a ∈ (E ⊔ F) ⊓ K' := Subgroup.mem_inf.mpr ⟨haN, ha⟩
    rw [hK'F] at h1
    exact Subgroup.mem_bot.mp h1
  · exact le_inf (zOf_inf_centralizer_le_thetaOf h hS hπ.1 (h.ne_bot_of_mem_E2 hπ))
      (inf_le_right.trans (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hK'.1)))
  · refine (inf_le_inf_right _ (orbitClosure_le (L := zOf (S ⊓ Subgroup.centralizer
      (E : Set G)) ⊓ zOf (S ⊓ Subgroup.centralizer (F : Set G))) fun a ha => ?_)).trans ?_
    · have h1 := Subgroup.mem_normalizer_iff_map_conj_eq.mp (hnorm (hK'.1 ha))
      exact (Subgroup.map_mono inf_le_left).trans h1.le
    · exact inf_zOf_inf_centralizer_le h hr hS hB hF hFE hK' hK'F

theorem inf_zOf_le_iSup_projIn
    (h : Counterexample p A θ) (hr : InPiTheta A θ r)
    (hS : IsSr p A θ r S) (hB : TypeBCore p A θ E K) {F : Subgroup G}
    (hF : F ∈ signalizerFunctorEk p 1 A) (hFE : F ≠ E) :
    zOf (S ⊓ Subgroup.centralizer (E : Set G)) ⊓ zOf (S ⊓ Subgroup.centralizer (F : Set G)) ≤
      ⨆ P ∈ Ind (thetaOf θ (E ⊔ F)),
        projIn (Ind (thetaOf θ (E ⊔ F))) P (zOf S ⊓ Subgroup.centralizer (A : Set G)) := by
  have hπ := h.sup_mem_E2_of_ne hB.mem hF hFE.symm
  have hΩ := Counterexample.isRegFam_ind_plane_of_typeB h hB hF hFE
  obtain ⟨K', hK', hπK', -⟩ := exists_line_inf_eq_bot h hπ
  intro x hx
  obtain ⟨hxE, hxF⟩ := Subgroup.mem_inf.mp hx
  have hxH : x ∈ thetaOf θ (E ⊔ F) := by
    refine Counterexample.inf_centralizer_le_thetaOf_of_isSr h hS hπ.1 (h.ne_bot_of_mem_E2 hπ)
      (Subgroup.mem_inf.mpr ⟨(zOf_le _ hxF).1, ?_⟩)
    rw [centralizer_sup]
    exact Subgroup.mem_inf.mpr ⟨(zOf_le _ hxE).2, (zOf_le _ hxF).2⟩
  refine hΩ.isDirectProduct.mem_of_coord_mem hxH fun P hP => ?_
  have hdp := hΩ.isDirectProduct.isDirectPair hP
  have hxPl : x ∈ P ⊔ sSup (Ind (thetaOf θ (E ⊔ F)) \ {P}) := by
    rw [hdp.sup_eq]
    exact hxH
  obtain ⟨j, hj, l, hl, hjl⟩ := (mem_sup_iff_of_commute hdp.commute).mp hxPl
  have hcoord : ((hΩ.isDirectProduct.coord hP ⟨x, hxH⟩ : P) : G) = j := by
    subst hjl
    exact hΩ.isDirectProduct.coord_mul hP hj hl
  rw [hcoord]
  have hjZ := mem_zOf_inf_centralizer_of_mul_eq h hr hS hB hF hFE hP hxF hj hl hjl
  have hjY : j ∈ zOf (S ⊓ Subgroup.centralizer (E : Set G)) ⊓
      zOf (S ⊓ Subgroup.centralizer (F : Set G)) ⊓ P :=
    Subgroup.mem_inf.mpr ⟨Subgroup.mem_inf.mpr ⟨Counterexample.zOf_inf_centralizer_le h hr hS hB
      hF hFE (Subgroup.mem_inf.mpr ⟨hjZ.1, hjZ.2⟩), hjZ.1⟩, hj⟩
  exact Subgroup.mem_iSup_of_mem P (Subgroup.mem_iSup_of_mem hP
    (inf_inf_le_projIn h hr hS hB hF hFE hK' hπK' hP hjY))

theorem iSup_projIn_le_inf_zOf
    (h : Counterexample p A θ) (hr : InPiTheta A θ r)
    (hS : IsSr p A θ r S) (hB : TypeBCore p A θ E K) {F : Subgroup G}
    (hF : F ∈ signalizerFunctorEk p 1 A) (hFE : F ≠ E) :
    (⨆ P ∈ Ind (thetaOf θ (E ⊔ F)),
        projIn (Ind (thetaOf θ (E ⊔ F))) P (zOf S ⊓ Subgroup.centralizer (A : Set G))) ≤
      zOf (S ⊓ Subgroup.centralizer (E : Set G)) ⊓ zOf (S ⊓ Subgroup.centralizer (F : Set G)) := by
  have hΩ := Counterexample.isRegFam_ind_plane_of_typeB h hB hF hFE
  refine iSup₂_le fun P hP t ht => ?_
  obtain ⟨htP, l, hl, hV⟩ := (mem_proj_iff (hΩ.isDirectProduct.commute_sSup_diff hP)).mp ht
  have hy : t * l ∈ zOf (S ⊓ Subgroup.centralizer (F : Set G)) :=
    zOf_inf_centralizer_le_zOf_inf hF.1 hV
  have htZ := mem_zOf_inf_centralizer_of_mul_eq h hr hS hB hF hFE hP hy htP hl rfl
  exact Subgroup.mem_inf.mpr ⟨Counterexample.zOf_inf_centralizer_le h hr hS hB hF hFE
    (Subgroup.mem_inf.mpr ⟨htZ.1, htZ.2⟩), htZ.1⟩

end T73Inf

end CFSG.SignalizerFunctorTheorem.McBride.Nonsolv
