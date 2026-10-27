module

public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec3.IntrThm33aAux6
public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec2.Lemma216

public section

open CFSG.Open

universe u

namespace CFSG.SignalizerFunctorTheorem.McBride.Near.Thm33b

open Thm33a

variable {Γ : Type u} [Group Γ] [Finite Γ] {p : ℕ} {A X Y X₁ X₂ : Subgroup Γ}

theorem sol_eq_bot_of_key (h : NearAsolvAction p A X) (hP : (X₁, X₂) ∈ iPairsY A X Y)
    (key : ∀ N : Subgroup Γ, N ≤ X → Admits X N → Admits A N →
      N ⊓ cenIn X (A : Set Γ) ≤ Y → N = ⊥) : sol X = ⊥ := by
  have hHsol : Admits (X₁ ⊔ cenIn X (A : Set Γ) ⊔ A) (sol X) :=
    sup_le (sup_le ((pair_le hP).trans (Nonsolv.SolQuot.le_nrm_sol X))
      (inf_le_left.trans (Nonsolv.SolQuot.le_nrm_sol X)))
      (h.admits.trans (Nonsolv.SolQuot.normalizer_le_nrm_sol X))
  have hle : sol X ⊓ X₁ ≤ X₂ :=
    le_of_solvable hP inf_le_right (Admits.inf hHsol (pair_admits_H hP))
      (Thm211.isSolvable_of_le inf_le_left (isSolvable_sol X))
  exact key (sol X) (sol_le X) (Nonsolv.SolQuot.le_nrm_sol X)
    (h.admits.trans (Nonsolv.SolQuot.normalizer_le_nrm_sol X))
    (inf_dsub_le hP (Nonsolv.SolQuot.le_nrm_sol X) hle)

theorem isGreatest_scalJoin
    (h : NearAsolvAction p A X) :
    IsGreatest {Z : Subgroup Γ | Z ≤ X ∧ Admits (cenIn X (A : Set Γ) ⊔ A) Z ∧
      Group.IsSolvable ↥Z} (scalJoin X A (cenIn X (A : Set Γ))) := by
  have hD : cenIn X (A : Set Γ) ≤ X := inf_le_left
  have hXadm : Admits (cenIn X (A : Set Γ) ⊔ A) X :=
    sup_le (hD.trans Subgroup.le_normalizer) h.admits
  have hXD : X ⊓ cenIn X (A : Set Γ) = cenIn X (A : Set Γ) := inf_eq_right.mpr hD
  refine ⟨⟨Thm211.scalJoin_le_left X A _, ?_, (thm211b h le_rfl hXadm).2⟩, ?_⟩
  · unfold scalJoin
    refine Admits.iSup fun S => Admits.iSup fun hS => ?_
    have := hS.2.1
    rwa [hXD] at this
  · rintro Z ⟨hZX, hZadm, hZs⟩
    exact Thm211.le_scalJoin ⟨hZX, by rwa [hXD], hZs⟩

theorem le_kOf_of_inf_dsub_eq_bot
    (h : NearAsolvAction p A X) (hsol : sol X = ⊥) (hXne : X ≠ ⊥)
    {Z : Subgroup Γ} (hZX : Z ≤ X) (hZ : Admits (cenIn X (A : Set Γ) ⊔ A) Z)
    (hZD : Z ⊓ cenIn X (A : Set Γ) = ⊥) : Z ≤ kOf X ∧ Group.IsSolvable ↥Z := by
  have hS := isGreatest_scalJoin h
  have h1 := lemma216d h hsol hXne hS hZX hZ (by
    refine eq_bot_iff.mpr fun x hx => ?_
    have : x ∈ Z ⊓ cenIn X (A : Set Γ) := Subgroup.mem_inf.mpr ⟨hx.1.1, hx.2⟩
    rwa [hZD] at this)
  have hle : s1 X (scalJoin X A (cenIn X (A : Set Γ))) ≤ kOf X :=
    (Subgroup.map_subtype_le _).trans (inf_le_right : s0 X (scalJoin X A (cenIn X (A : Set Γ))) ≤ _)
  refine ⟨h1.trans hle, ?_⟩
  have hnil : Group.IsNilpotent ↥(s1 X (scalJoin X A (cenIn X (A : Set Γ)))) :=
    Thm210.isNilpotent_fittingSubgroupOf (s0 X (scalJoin X A (cenIn X (A : Set Γ))))
  exact Thm211.isSolvable_of_le h1 inferInstance

theorem pair_rigid
    (h : NearAsolvAction p A X) (hsol : sol X = ⊥) (hXne : X ≠ ⊥)
    (hXe : X = kOf X ⊔ iThetaU A X Y)
    (key : ∀ N : Subgroup Γ, N ≤ X → Admits X N → Admits A N →
      N ⊓ cenIn X (A : Set Γ) ≤ Y → N = ⊥)
    (hP : (X₁, X₂) ∈ iPairsY A X Y) (hX₂sol : Group.IsSolvable ↥X₂) :
    ∃ W : Subgroup Γ, W ≤ kOf X ⊓ X₁ ∧ Group.IsPerfect ↥W ∧
      Admits (X₁ ⊔ cenIn X (A : Set Γ) ⊔ A) W ∧ W ⊔ X₂ = X₁ ∧ W ⊓ X₂ = ⊥ ∧
      k1 X W = ⊥ ∧ cenIn X (W : Set Γ) = ⊥ ∧ Y = ⊥ := by
  have hKX : kOf X ≤ X := kOf_le X
  have hXK : Admits X (kOf X) :=
    Subgroup.le_normalizer.trans (Thm211.normalizer_le_normalizer_kOf X)
  have hAK : Admits A (kOf X) := h.admits.trans (Thm211.normalizer_le_normalizer_kOf X)
  have hKX₁ : ¬ (kOf X ⊓ X₁ ≤ X₂) := fun hle =>
    Thm211.kOf_ne_bot hsol hXne (key (kOf X) hKX hXK hAK (inf_dsub_le hP hXK hle))
  obtain ⟨W, hWB, hWperf, hWadm, hWX, hWinf⟩ := exists_perfect_sup h hsol hXne hP hX₂sol hKX₁
  have hWK : W ≤ kOf X := hWB.trans inf_le_left
  have hWX₁ : W ≤ X₁ := hWB.trans inf_le_right
  have hDAH : cenIn X (A : Set Γ) ⊔ A ≤ X₁ ⊔ cenIn X (A : Set Γ) ⊔ A :=
    sup_le dsub_le_H le_sup_right
  have hWDA : Admits (cenIn X (A : Set Γ) ⊔ A) W := hDAH.trans hWadm
  have hWX₁adm : Admits X₁ W := le_H.trans hWadm
  have hX₂adm : Admits X₁ X₂ := le_H.trans (pair_admits_H₂ hP)
  have hcomm : ∀ w ∈ W, ∀ x ∈ X₂, w * x = x * w := fun w hw x hx =>
    (commute_of_inf_eq_bot hWX₁adm hX₂adm hWX₁ (pair_le₂ hP) hWinf hw hx).eq
  have hZ : ∀ Z ∈ iUset A X Y, Admits Z (k1 X W) := by
    intro Z hZ
    have hYZ : Y ≤ Z := (pair_Y_le hP).trans hZ.2.1
    refine lemma213d h hsol hXne hWK hWDA hWperf (Z₀ := orbitClosure Y Z) hZ.1.1
      ⟨orbitClosure_le_of_admits hYZ Subgroup.le_normalizer,
        Nonsolv.SolQuot.le_normalizer_orbitClosure Y Z⟩
      (admits_orbitClosure (pair_admits_Y hP) hZ.1.2) hZ.1.2 ?_
    ext x
    simp only [cenIn, k1, Subgroup.mem_inf]
    constructor
    · rintro ⟨⟨hxZ₀, hxK⟩, hxX, hxA⟩
      have hxY : x ∈ Y := by
        rw [← hZ.2.2]
        exact Subgroup.mem_inf.mpr ⟨hxZ₀, hxX, hxA⟩
      exact ⟨⟨hxK, Subgroup.mem_centralizer_iff.mpr fun w hw =>
        hcomm w hw x (pair_Y_le₂ hP hxY)⟩, hxA⟩
    · rintro ⟨⟨hxK, hxC⟩, hxA⟩
      have hxD : x ∈ cenIn X (A : Set Γ) := Subgroup.mem_inf.mpr ⟨hKX hxK, hxA⟩
      have hxY : x ∈ Y := mem_Y_of_commute hP hWX₁ hWX hxD
        (fun w hw => Subgroup.mem_centralizer_iff.mp hxC w hw)
      exact ⟨⟨le_orbitClosure Y Z hxY, hxK⟩, hKX hxK, hxA⟩
  have hdp := lemma213a h hsol hXne hWK hWDA hWperf
  have hKk1 : Admits (kOf X) (k1 X W) := by
    rw [← hdp.sup_eq]
    refine sup_le Subgroup.le_normalizer ?_
    refine Thm211.admits_iff.mpr fun y hy x hx => ?_
    have hc : Commute x y := hdp.commute x hx y hy
    have : y * x * y⁻¹ = x := by
      rw [← hc.eq]
      group
    rw [this]
    exact hx
  have hXk1 : Admits X (k1 X W) :=
    hXe.le.trans (sup_le hKk1 (iThetaU_le_of hZ))
  have hWA : Admits A W := le_sup_right.trans hWadm
  have hAk1 : Admits A (k1 X W) :=
    Admits.inf hAK (hWA.trans (Thm211.normalizer_le_normalizer_centralizer W))
  have hk1X : k1 X W ≤ X := inf_le_left.trans hKX
  have hk1D : k1 X W ⊓ cenIn X (A : Set Γ) ≤ Y := by
    intro x hx
    obtain ⟨hxk, hxD⟩ := Subgroup.mem_inf.mp hx
    exact mem_Y_of_commute hP hWX₁ hWX hxD
      (fun w hw => Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hxk).2 w hw)
  have hk1bot : k1 X W = ⊥ := key (k1 X W) hk1X hXk1 hAk1 hk1D
  have hcen : cenIn X (W : Set Γ) = ⊥ := lemma213c h hsol hXne hWK hWDA hWperf hk1bot
  refine ⟨W, hWB, hWperf, hWadm, hWX, hWinf, hk1bot, hcen, ?_⟩
  refine eq_bot_iff.mpr fun y hy => ?_
  have hyD : y ∈ cenIn X (A : Set Γ) := pair_Y_le hP hy
  have hy1 : y ∈ cenIn X (W : Set Γ) :=
    Subgroup.mem_inf.mpr ⟨hyD.1, Subgroup.mem_centralizer_iff.mpr fun w hw =>
      hcomm w hw y (pair_Y_le₂ hP hy)⟩
  rw [hcen] at hy1
  exact hy1

end CFSG.SignalizerFunctorTheorem.McBride.Near.Thm33b
