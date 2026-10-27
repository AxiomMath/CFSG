module

public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Sec8.T81.Defs
public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Sec8.T81.Plane
public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Sec6.L612
public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Sec7.L74

public section

open CFSG.Open

universe u

namespace CFSG.SignalizerFunctorTheorem.McBride.Nonsolv

namespace T81

variable {p : ℕ} {G : Type u} [Group G] [Finite G] {A : Subgroup G} {θ : G → Subgroup G}
  {r : ℕ} {S : Subgroup G}

theorem inf_zOf_le_mAll
    (h : Counterexample p A θ) (hA : TypeA p A θ) (hr : InPiTheta A θ r)
    (hS : IsSr p A θ r S) {B : Subgroup G} (hB : B ∈ signalizerFunctorEk p 2 A) {a : G}
    (ha : a ∈ B) (ha1 : a ≠ 1) : zOf S ⊓ θ a ≤ mAll θ (zOf S) B := by
  obtain ⟨b, hb, hba⟩ := exists_mem_not_mem_zpowers h hB ha ha1
  have ha' : a ∈ A := hB.1 ha
  have hE := h.zpowers_mem_E1 ha' ha1
  have hind : Ind (θ a) = lcal (θ a) := by
    have := h.ind_eq_lcal_line_of_typeA hA hE
    rwa [h.isFunctor.thetaOf_zpowers ha' ha1] at this
  have hdp := h.lemma_7_4_c hr hS ha' ha1 (Or.inl hA)
  rw [← hdp.sSup_eq]
  refine sSup_le ?_
  rintro _ ⟨L', hL', rfl⟩
  rw [hind] at hL'
  have hL := smear_mem_lcal_plane h hA hB ha ha1 hb hba hL'
  refine le_trans ?_ ((zL_le_mL θ (zOf S) B _).trans (mL_le_mAll hL))
  intro z hz
  rw [Subgroup.mem_inf] at hz
  refine mem_zL_iff.mpr ⟨hz.1, fun K hK hne y hy => ?_⟩
  exact (commute_of_mem_lcal_plane h hA hB ha ha1 hb hba hL' hK hne y hy z hz.2).symm

theorem thetaOf_le_mAll
    (h : Counterexample p A θ) (hA : TypeA p A θ) (Z : Subgroup G)
    {B : Subgroup G} (hB : B ∈ signalizerFunctorEk p 2 A) : thetaOf θ B ≤ mAll θ Z B := by
  rw [← (h.isRegFam_plane_of_typeA hA hB).isDirectProduct.sSup_eq]
  exact sSup_le fun L hL => (le_mL θ Z B L).trans (mL_le_mAll hL)

theorem apply_le_mAll
    (h : Counterexample p A θ) (hA : TypeA p A θ) (hr : InPiTheta A θ r)
    (hS : IsSr p A θ r S) {B : Subgroup G} (hB : B ∈ signalizerFunctorEk p 2 A) {a : G}
    (ha : a ∈ B) (ha1 : a ≠ 1) : θ a ≤ mAll θ (zOf S) B := by
  obtain ⟨b, hb, hba⟩ := exists_mem_not_mem_zpowers h hB ha ha1
  have ha' : a ∈ A := hB.1 ha
  have hb1 : b ≠ 1 := fun hb1 => hba (hb1 ▸ one_mem _)
  have hE := h.zpowers_mem_E1 ha' ha1
  have hFA : Subgroup.zpowers b ≤ A := Subgroup.zpowers_le.mpr (hB.1 hb)
  have hind : Ind (θ a) = lcal (θ a) := by
    have := h.ind_eq_lcal_line_of_typeA hA hE
    rwa [h.isFunctor.thetaOf_zpowers ha' ha1] at this
  have hΩ := h.isRegFam_line_of_typeA hA hE
  rw [h.isFunctor.thetaOf_zpowers ha' ha1] at hΩ
  have hsol : sol (θ a) = ⊥ := by
    have := h.sol_thetaOf (Subgroup.zpowers_le.mpr ha') (h.ne_bot_of_mem_E1 hE)
    rwa [h.isFunctor.thetaOf_zpowers ha' ha1] at this
  have hk : kOf (θ a) = θ a := by
    have := hA.kOf_eq a ha' ha1
    rwa [h.isFunctor.thetaOf_zpowers ha' ha1] at this
  have hK : IsSemisimple (θ a) := by
    have := isSemisimple_kOf hsol
    rwa [hk] at this
  have hY : thetaOf θ B ⊔ (zOf S ⊓ θ a) ≤ mAll θ (zOf S) B :=
    sup_le (thetaOf_le_mAll h hA _ hB) (inf_zOf_le_mAll h hA hr hS hB ha ha1)
  have hYK : thetaOf θ B ⊔ (zOf S ⊓ θ a) ≤ θ a :=
    sup_le (thetaOf_le_apply ha ha1) inf_le_right
  have hperm : ∀ f ∈ Subgroup.zpowers b, ∀ J ∈ lcal (θ a),
      J.map (MulAut.conj f).toMonoidHom ∈ lcal (θ a) := fun f hf J hJ =>
    hΩ.map_conj_mem f (hFA hf) J hJ
  have hHB : θ a ⊓ Subgroup.centralizer ((Subgroup.zpowers b : Subgroup G) : Set G) =
      thetaOf θ B := by
    rw [centralizer_zpowers_eq_singleton]
    exact (thetaOf_plane_eq h hB ha ha1 hb hba).symm
  have hproj : ∀ J ∈ lcal (θ a), projIn (lcal (θ a)) J (thetaOf θ B ⊔ (zOf S ⊓ θ a)) = J := by
    intro J hJ
    refine le_antisymm (projIn_le _ _) ?_
    have h1 := projIn_centralizer_eq hΩ.isDirectProduct hperm hJ
    rw [hHB] at h1
    have hfree : Subgroup.zpowers b ⊓ Subgroup.normalizer (J : Set G) = ⊥ := by
      refine eq_bot_iff.mpr fun x hx => ?_
      obtain ⟨hxb, hxN⟩ := Subgroup.mem_inf.mp hx
      have hxa : x ∈ Subgroup.zpowers a := by
        rw [← hΩ.stabilizer J hJ]
        exact Subgroup.mem_inf.mpr ⟨hFA hxb, hxN⟩
      have hxab : x ∈ Subgroup.zpowers b ⊓ Subgroup.zpowers a := Subgroup.mem_inf.mpr ⟨hxb, hxa⟩
      have hdisj : Subgroup.zpowers b ⊓ Subgroup.zpowers a = ⊥ := by
        rw [inf_comm]
        exact inf_eq_bot_of_not_le h.prime (h.card_zpowers (hB.1 hb) hb1)
          (fun hle => hba (hle (Subgroup.mem_zpowers b)))
      rwa [hdisj] at hxab
    rw [hfree] at h1
    have h2 : J ⊓ Subgroup.centralizer (((⊥ : Subgroup G) : Subgroup G) : Set G) = J := by
      refine inf_eq_left.mpr fun x _ => ?_
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      rw [SetLike.mem_coe, Subgroup.mem_bot] at hy
      rw [hy, one_mul, mul_one]
    rw [h2] at h1
    exact h1.ge.trans (proj_mono le_sup_left)
  have hint : ∀ J ∈ lcal (θ a), (thetaOf θ B ⊔ (zOf S ⊓ θ a)) ⊓ J ≠ ⊥ := by
    intro J hJ hbot
    apply h.lemma_7_4_b hr hS ha' ha1 (Or.inl hA) (hind ▸ hJ)
    rw [eq_bot_iff, ← hbot]
    exact le_inf (le_trans (inf_le_inf_left _ (lcal_le hJ)) le_sup_right) inf_le_right
  have hEq := eq_of_projIn_eq_of_inf_ne_bot hK hYK hproj hint
  rw [← hEq]
  exact hY

theorem mAll_eq_sSup_msig
    (h : Counterexample p A θ) (hA : TypeA p A θ) (hr : InPiTheta A θ r)
    (hS : IsSr p A θ r S) {B : Subgroup G} (hB : B ∈ signalizerFunctorEk p 2 A) :
    mAll θ (zOf S) B = sSup (Msig p A θ) := by
  have hle1 : mAll θ (zOf S) B ≤ sSup (Msig p A θ) := by
    refine iSup₂_le fun L hL => sup_le ?_ ?_
    · exact (lcal_le hL).trans (le_sSup (h.thetaOf_mem_msig hB.1 (h.ne_bot_of_mem_E2 hB)))
    · exact (zL_le θ (zOf S) B L).trans ((zOf_le S).trans (le_sSup hS.1.1))
  refine le_antisymm hle1 ?_
  set T : Set (Subgroup G) := {Y | ∃ a ∈ B, a ≠ 1 ∧ Y = θ a} with hT
  have hTM : T ⊆ Msig p A θ := by
    rintro _ ⟨a, ha, ha1, rfl⟩
    exact h.apply_mem_msig (hB.1 ha) ha1
  rcases h.lemma_6_12 ⟨T, hTM, rfl⟩ with ⟨hall, -⟩ | ⟨-, hB'⟩
  · refine (sSup_le hall).trans (sSup_le ?_)
    rintro _ ⟨a, ha, ha1, rfl⟩
    exact apply_le_mAll h hA hr hS hB ha ha1
  · obtain ⟨a, ha, ha1, hnle⟩ := hB' B hB
    exact absurd (le_sSup (show θ a ∈ T from ⟨a, ha, ha1, rfl⟩)) hnle

end T81

end CFSG.SignalizerFunctorTheorem.McBride.Nonsolv
