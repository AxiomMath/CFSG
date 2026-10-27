module

public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Sec8.T85.Hat
public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Sec7.StructB

public section

open CFSG.Open

universe u

namespace CFSG.SignalizerFunctorTheorem.McBride.Nonsolv

namespace T85

variable {p : ℕ} {G : Type u} [Group G] [Finite G] {A : Subgroup G} {θ : G → Subgroup G}
  {E K : Subgroup G}

theorem map_conj_mem_ind_E
    (h : Counterexample p A θ) (hB : TypeBCore p A θ E K) {F : Subgroup G}
    (hFA : F ≤ A) : ∀ f ∈ F, ∀ J ∈ Ind (thetaOf θ E),
      J.map (MulAut.conj f).toMonoidHom ∈ Ind (thetaOf θ E) :=
  fun f hf J hJ => (Counterexample.isRegFam_ind_E_of_typeB h hB).map_conj_mem f (hFA hf) J hJ

theorem map_conj_ne_ind_E
    (h : Counterexample p A θ) (hB : TypeBCore p A θ E K) {F : Subgroup G}
    (hF : F ∈ signalizerFunctorEk p 1 A) (hFE : F ≠ E) :
    ∀ f ∈ F, f ≠ 1 → ∀ J ∈ Ind (thetaOf θ E), J.map (MulAut.conj f).toMonoidHom ≠ J := by
  intro f hf hf1 J hJ
  refine (Counterexample.isRegFam_ind_E_of_typeB h hB).map_conj_ne (hF.1 hf) (fun hfE => hf1 ?_) hJ
  have h1 : f ∈ F ⊓ E := Subgroup.mem_inf.mpr ⟨hf, hfE⟩
  rw [Counterexample.inf_line_eq_bot_of_typeB h hB hF hFE] at h1
  exact Subgroup.mem_bot.mp h1

theorem exists_mem_ind_E_ge
    (h : Counterexample p A θ) (hB : TypeBCore p A θ E K)
    {R : Subgroup G} (hR : R ∈ lcal (thetaOf θ E)) : ∃ Q ∈ Ind (thetaOf θ E), R ≤ Q := by
  rw [Counterexample.lcal_E_eq_of_typeB h hB] at hR
  obtain ⟨Q, hQ, rfl⟩ := hR
  refine ⟨Q, hQ, lcal_le ?_⟩
  rw [Counterexample.lcal_of_mem_ind_E_of_typeB h hB hQ]
  exact Set.mem_singleton _

theorem exists_le_of_mem_ind_E
    (h : Counterexample p A θ) (hB : TypeBCore p A θ E K)
    {Q : Subgroup G} (hQ : Q ∈ Ind (thetaOf θ E)) : ∃ R ∈ lcal (thetaOf θ E), R ≤ Q := by
  refine ⟨CFSG.inSubgroup CFSG.generalizedFitting Q, ?_, lcal_le ?_⟩
  · rw [Counterexample.lcal_E_eq_of_typeB h hB]
    exact ⟨Q, hQ, rfl⟩
  · rw [Counterexample.lcal_of_mem_ind_E_of_typeB h hB hQ]
    exact Set.mem_singleton _

theorem inf_centralizer_mem_ind_plane
    (h : Counterexample p A θ) (hB : TypeBCore p A θ E K)
    {F : Subgroup G} (hF : F ∈ signalizerFunctorEk p 1 A) (hFE : F ≠ E) {K' : Subgroup G}
    (hK' : K' ∈ lcal (thetaOf θ F)) :
    K' ⊓ Subgroup.centralizer (E : Set G) ∈ Ind (thetaOf θ (E ⊔ F)) := by
  rw [Counterexample.ind_plane_eq_inf_centralizer_of_typeB h hB hF hFE]
  exact ⟨K', hK', rfl⟩

theorem exists_smear_eq
    (h : Counterexample p A θ) (hB : TypeBCore p A θ E K) {F : Subgroup G}
    (hF : F ∈ signalizerFunctorEk p 1 A) (hFE : F ≠ E) {K' : Subgroup G}
    (hK' : K' ∈ lcal (thetaOf θ F)) :
    ∃ Q ∈ Ind (thetaOf θ E), K' ⊓ Subgroup.centralizer (E : Set G) = smear Q F := by
  have h1 := inf_centralizer_mem_ind_plane h hB hF hFE hK'
  rw [Counterexample.ind_plane_eq_smear_of_typeB h hB hF hFE] at h1
  exact h1

theorem exists_inf_centralizer_eq_smear
    (h : Counterexample p A θ) (hB : TypeBCore p A θ E K)
    {F : Subgroup G} (hF : F ∈ signalizerFunctorEk p 1 A) (hFE : F ≠ E) {Q : Subgroup G}
    (hQ : Q ∈ Ind (thetaOf θ E)) :
    ∃ K' ∈ lcal (thetaOf θ F), K' ⊓ Subgroup.centralizer (E : Set G) = smear Q F := by
  have h1 : smear Q F ∈ Ind (thetaOf θ (E ⊔ F)) := by
    rw [Counterexample.ind_plane_eq_smear_of_typeB h hB hF hFE]
    exact ⟨Q, hQ, rfl⟩
  rw [Counterexample.ind_plane_eq_inf_centralizer_of_typeB h hB hF hFE] at h1
  obtain ⟨K', hK', hK'e⟩ := h1
  exact ⟨K', hK', hK'e.symm⟩

theorem inf_centralizer_ne
    (h : Counterexample p A θ) (hB : TypeBCore p A θ E K) {F : Subgroup G}
    (hF : F ∈ signalizerFunctorEk p 1 A) (hFE : F ≠ E) {K₁ K₂ : Subgroup G}
    (h₁ : K₁ ∈ lcal (thetaOf θ F)) (h₂ : K₂ ∈ lcal (thetaOf θ F)) (hne : K₁ ≠ K₂) :
    K₁ ⊓ Subgroup.centralizer (E : Set G) ≠ K₂ ⊓ Subgroup.centralizer (E : Set G) := by
  intro heq
  have hdisj : Disjoint K₁ K₂ :=
    (Counterexample.isRegFam_line_of_typeB h hB hF hFE).isDirectProduct.indep.pairwiseDisjoint
      h₁ h₂ hne
  have hbot : K₁ ⊓ Subgroup.centralizer (E : Set G) = ⊥ :=
    disjoint_self.mp (hdisj.mono inf_le_left (heq.le.trans inf_le_left))
  exact (inf_centralizer_mem_ind_plane h hB hF hFE h₁).1 hbot

theorem lHat_le_orbitClosure
    (h : Counterexample p A θ) (hB : TypeBCore p A θ E K)
    {F : Subgroup G} (hF : F ∈ signalizerFunctorEk p 1 A) {K' Q₁ : Subgroup G}
    (hQ₁ : Q₁ ∈ Ind (thetaOf θ E))
    (heq : K' ⊓ Subgroup.centralizer (E : Set G) = smear Q₁ F) :
    lHat (thetaOf θ E) (K' ⊓ Subgroup.centralizer (E : Set G)) ≤ orbitClosure Q₁ F := by
  rw [heq]
  exact lHat_smear_le_orbitClosure (Counterexample.isRegFam_ind_E_of_typeB h hB).isDirectProduct
    (map_conj_mem_ind_E h hB hF.1) (fun R hR => exists_mem_ind_E_ge h hB hR) hQ₁

theorem le_lHat_of_mem_conjOrbit
    (h : Counterexample p A θ) (hB : TypeBCore p A θ E K)
    {F : Subgroup G} (hF : F ∈ signalizerFunctorEk p 1 A) (hFE : F ≠ E) {K' Q₁ : Subgroup G}
    (hQ₁ : Q₁ ∈ Ind (thetaOf θ E))
    (heq : K' ⊓ Subgroup.centralizer (E : Set G) = smear Q₁ F) {Q : Subgroup G}
    (hQ : Q ∈ RegFam.conjOrbit Q₁ F) {R : Subgroup G} (hR : R ∈ lcal (thetaOf θ E))
    (hRQ : R ≤ Q) : R ≤ lHat (thetaOf θ E) (K' ⊓ Subgroup.centralizer (E : Set G)) := by
  rw [heq]
  exact le_lHat_smear (Counterexample.isRegFam_ind_E_of_typeB h hB).isDirectProduct
    (map_conj_mem_ind_E h hB hF.1) (map_conj_ne_ind_E h hB hF hFE) hQ₁ hQ hR hRQ

theorem commute_lHat
    (h : Counterexample p A θ) (hB : TypeBCore p A θ E K) {F : Subgroup G}
    (hF : F ∈ signalizerFunctorEk p 1 A) (hFE : F ≠ E) {K₁ K₂ : Subgroup G}
    (h₁ : K₁ ∈ lcal (thetaOf θ F)) (h₂ : K₂ ∈ lcal (thetaOf θ F)) (hne : K₁ ≠ K₂) :
    ∀ x ∈ lHat (thetaOf θ E) (K₁ ⊓ Subgroup.centralizer (E : Set G)),
      ∀ y ∈ lHat (thetaOf θ E) (K₂ ⊓ Subgroup.centralizer (E : Set G)), Commute x y := by
  obtain ⟨Q₁, hQ₁, heq₁⟩ := exists_smear_eq h hB hF hFE h₁
  obtain ⟨Q₂, hQ₂, heq₂⟩ := exists_smear_eq h hB hF hFE h₂
  have hnot : Q₂ ∉ RegFam.conjOrbit Q₁ F := by
    rintro ⟨f, hf, rfl⟩
    refine inf_centralizer_ne h hB hF hFE h₁ h₂ hne ?_
    rw [heq₁, heq₂]
    unfold smear
    rw [Near.Lemma212.orbitClosure_map_conj_of_mem Q₁ hf]
  exact fun x hx y hy => RegFam.commute_orbitClosure
    (Counterexample.isRegFam_ind_E_of_typeB h hB).isDirectProduct (map_conj_mem_ind_E h hB hF.1)
    hQ₁ hQ₂ hnot x (lHat_le_orbitClosure h hB hF hQ₁ heq₁ hx) y
    (lHat_le_orbitClosure h hB hF hQ₂ heq₂ hy)

end T85

end CFSG.SignalizerFunctorTheorem.McBride.Nonsolv
