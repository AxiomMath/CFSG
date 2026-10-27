module

public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec3.IntrThm33bAux3
public import CFSG.SignalizerFunctorTheorem.McBride.Prelim.SemisimpleCommutator

public section

open CFSG.Open
open scoped commutatorElement

universe u

namespace CFSG.SignalizerFunctorTheorem.McBride.Near.Thm33b

open Thm33a

variable {Γ : Type u} [Group Γ] [Finite Γ] {p : ℕ} {A X X₁ X₂ : Subgroup Γ}

omit [Finite Γ] in
theorem admits_bot (Q : Subgroup Γ) : Admits Q (⊥ : Subgroup Γ) :=
  Thm211.admits_iff.mpr fun q _ x hx => by
    rw [Subgroup.mem_bot.mp hx]
    simp

theorem pair_eq_of_Y_bot
    (h : NearAsolvAction p A X) (hsol : sol X = ⊥) (hXne : X ≠ ⊥)
    (hXe : X = kOf X ⊔ iThetaU A X ⊥)
    (key : ∀ N : Subgroup Γ, N ≤ X → Admits X N → Admits A N →
      N ⊓ cenIn X (A : Set Γ) ≤ ⊥ → N = ⊥)
    (hP : (X₁, X₂) ∈ iPairsY A X ⊥) :
    X₂ = ⊥ ∧ X₁ ≤ kOf X ∧ Group.IsPerfect ↥X₁ ∧ cenIn X (X₁ : Set Γ) = ⊥ := by
  have hX₂X : X₂ ≤ X := (pair_le₂ hP).trans (pair_le hP)
  obtain ⟨hX₂K, hX₂sol⟩ := le_kOf_of_inf_dsub_eq_bot h hsol hXne hX₂X (pair_admits_DA₂ hP)
    (pair_inf hP)
  obtain ⟨W, hWB, hWperf, hWadm, hWX, hWinf, hk1, hcen, -⟩ :=
    pair_rigid h hsol hXne hXe key hP hX₂sol
  have hWX₁ : W ≤ X₁ := hWB.trans inf_le_right
  have hWX₁adm : Admits X₁ W := le_H.trans hWadm
  have hX₂adm : Admits X₁ X₂ := le_H.trans (pair_admits_H₂ hP)
  have hX₂bot : X₂ = ⊥ := by
    refine eq_bot_iff.mpr fun x hx => ?_
    have hxk : x ∈ k1 X W := Subgroup.mem_inf.mpr ⟨hX₂K hx, Subgroup.mem_centralizer_iff.mpr
      fun w hw => (commute_of_inf_eq_bot hWX₁adm hX₂adm hWX₁ (pair_le₂ hP) hWinf hw hx).eq⟩
    rw [hk1] at hxk
    exact hxk
  have hX₁W : X₁ = W := by
    rw [← hWX, hX₂bot, sup_bot_eq]
  subst hX₁W
  exact ⟨hX₂bot, hWB.trans inf_le_left, hWperf, hcen⟩

theorem exists_lcal_le_of_ne_bot (hsol : sol X = ⊥) {V : Subgroup Γ} (hVK : V ≤ kOf X)
    (hV : Admits (kOf X) V) (hne : V ≠ ⊥) : ∃ J ∈ lcal (kOf X), J ≤ V := by
  have hK := isSemisimple_kOf hsol
  have hnc : ∃ J ∈ lcal (kOf X), ¬ J ≤ Subgroup.centralizer (V : Set Γ) := by
    by_contra hcon
    push Not at hcon
    apply hne
    have hKC : kOf X ≤ Subgroup.centralizer (V : Set Γ) := by
      rw [← hK.isDirectProduct_lcal.sSup_eq]
      exact sSup_le hcon
    have h1 : V ≤ X ⊓ Subgroup.centralizer ((kOf X : Subgroup Γ) : Set Γ) :=
      le_inf (hVK.trans (kOf_le X)) fun v hv => Subgroup.mem_centralizer_iff.mpr fun k hk =>
        (Subgroup.mem_centralizer_iff.mp (hKC hk) v hv).symm
    rw [centralizer_kOf_eq_bot hsol] at h1
    exact le_bot_iff.mp h1
  obtain ⟨J, hJ, hJC⟩ := hnc
  refine ⟨J, hJ, ?_⟩
  have h1 : ⁅kOf X, V⁆ = sSup {J | J ∈ lcal (kOf X) ∧ ¬ J ≤ Subgroup.centralizer (V : Set Γ)} :=
    commutator_eq_sSup_not_centralized hK (hVK.trans Subgroup.le_normalizer)
  have h2 : ⁅kOf X, V⁆ ≤ V := Subgroup.commutator_le.mpr fun k hk v hv => by
    rw [commutatorElement_def]
    exact mul_mem ((Subgroup.mem_normalizer_iff.mp (hV hk) v).mp hv) (inv_mem hv)
  have hmem : J ∈ {J | J ∈ lcal (kOf X) ∧ ¬ J ≤ Subgroup.centralizer (V : Set Γ)} := ⟨hJ, hJC⟩
  exact (le_sSup hmem).trans (h1.symm.le.trans h2)

theorem isPerfect_projIn {S : Set (Subgroup Γ)} {K W J : Subgroup Γ} (hK : IsDirectProduct S K)
    (hJ : J ∈ S) (hWK : W ≤ K) (hperf : Group.IsPerfect ↥W) :
    Group.IsPerfect ↥(projIn S J W) := by
  have hQeq : projIn S J W = (W.subgroupOf K).map (J.subtype.comp (hK.coord hJ)) := by
    ext z
    rw [IsDirectProduct.mem_projIn_iff hK hJ, Subgroup.mem_map]
    constructor
    · rintro ⟨y, hyW, rfl⟩
      exact ⟨y, Subgroup.mem_subgroupOf.mpr hyW, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y, Subgroup.mem_subgroupOf.mp hy, rfl⟩
  have hWperf' : Group.IsPerfect ↥(W.subgroupOf K) := by
    rw [Subgroup.isPerfect_iff]
    apply Subgroup.map_injective K.subtype_injective
    rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hWK]
    exact Subgroup.isPerfect_iff.mp hperf
  rw [hQeq]
  exact Group.IsPerfect.map _

theorem eq_bot_or_eq_kOf
    (h : NearAsolvAction p A X) (hsol : sol X = ⊥) (hXne : X ≠ ⊥)
    (hP : (X₁, ⊥) ∈ iPairsY A X ⊥) (hX₁K : X₁ ≤ kOf X) (hperf : Group.IsPerfect ↥X₁)
    (hcen : cenIn X (X₁ : Set Γ) = ⊥) {V : Subgroup Γ} (hVK : V ≤ kOf X)
    (hV : Admits (kOf X ⊔ cenIn X (A : Set Γ) ⊔ A) V) : V = ⊥ ∨ V = kOf X := by
  by_cases hVbot : V = ⊥
  · exact Or.inl hVbot
  refine Or.inr ?_
  have hss := semisimpleAction_kOf h hsol hXne
  have hKV : Admits (kOf X) V := le_sup_left.trans (le_sup_left.trans hV)
  have hH₁ : X₁ ⊔ cenIn X (A : Set Γ) ⊔ A ≤ kOf X ⊔ cenIn X (A : Set Γ) ⊔ A :=
    sup_le_sup_right (sup_le_sup_right hX₁K _) _
  have hHV : Admits (X₁ ⊔ cenIn X (A : Set Γ) ⊔ A) V := hH₁.trans hV
  have hMadm : Admits (X₁ ⊔ cenIn X (A : Set Γ) ⊔ A) (V ⊓ X₁) :=
    hHV.inf (pair_admits_H hP)
  have hX₁V : X₁ ≤ V := by
    rcases chief_dichotomy (pair_chief hP) hMadm inf_le_right with h1 | h1
    · exfalso
      have hVX₁ : V ⊓ X₁ = ⊥ := le_bot_iff.mp h1
      obtain ⟨J, hJ, hJV⟩ := exists_lcal_le_of_ne_bot hsol hVK hKV hVbot
      have hG := hss.isDirectProduct_lcal
      have hns : ¬ Group.IsSolvable ↥(projIn (lcal (kOf X)) J X₁) := by
        intro hsolv
        have hperfQ := isPerfect_projIn hG hJ hX₁K hperf
        have hQbot : projIn (lcal (kOf X)) J X₁ = ⊥ := by
          by_contra hne
          have : Nontrivial ↥(projIn (lcal (kOf X)) J X₁) :=
            (Subgroup.nontrivial_iff_ne_bot _).mpr hne
          exact Group.IsPerfect.not_isSolvable _ hsolv
        have hJC : J ≤ cenIn X (X₁ : Set Γ) := by
          intro j hj
          refine Subgroup.mem_inf.mpr ⟨kOf_le X (lcal_le hJ hj),
            Subgroup.mem_centralizer_iff.mpr fun x hx => ?_⟩
          have hxK : x ∈ kOf X := hX₁K hx
          have hmem : ((hG.coord hJ ⟨x, hxK⟩ : J) : Γ) ∈ projIn (lcal (kOf X)) J X₁ :=
            (IsDirectProduct.mem_projIn_iff hG hJ).mpr ⟨⟨x, hxK⟩, hx, rfl⟩
          rw [hQbot, Subgroup.mem_bot] at hmem
          have h2 : x ∈ sSup (lcal (kOf X) \ {J}) :=
            (hG.coord_eq_one_iff hJ ⟨x, hxK⟩).mp (Subtype.ext hmem)
          exact (hG.commute_sSup_diff hJ j hj x h2).eq.symm
        rw [hcen, le_bot_iff] at hJC
        obtain ⟨-, -, -, hnc⟩ := mem_lcal_iff.mp hJ
        rw [hJC] at hnc
        exact hnc inferInstance
      have hX₁DA : Admits (cenIn (kOf X) (A : Set Γ) ⊔ A) X₁ :=
        (sup_le_sup_right (inf_le_inf_right _ (kOf_le X)) A).trans (pair_admits_left hP)
      obtain ⟨-, hsm⟩ := thm210g hss hX₁K hX₁DA hJ hns
      have hsV : smear J A ≤ V :=
        (smear_le_orbitClosure J A).trans (orbitClosure_le_of_admits hJV (le_sup_right.trans hV))
      have hsb : smear J A = ⊥ := le_bot_iff.mp (hVX₁ ▸ le_inf hsV hsm)
      apply hss.fittingSubgroupOf_smear_ne_bot hJ
      exact le_bot_iff.mp ((Subgroup.map_subtype_le _).trans hsb.le)
    · rw [sup_bot_eq] at h1
      exact h1.symm.le.trans inf_le_left
  have hVn : (V.subgroupOf (kOf X)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hVK).mpr hKV
  have hdp := hss.semisimple.isDirectPair_of_normal hVK hVn
  have hC : kOf X ⊓ Subgroup.centralizer (V : Set Γ) = ⊥ := by
    refine eq_bot_iff.mpr fun x hx => ?_
    have : x ∈ cenIn X (X₁ : Set Γ) := Subgroup.mem_inf.mpr ⟨kOf_le X hx.1,
      Subgroup.mem_centralizer_iff.mpr fun y hy => Subgroup.mem_centralizer_iff.mp hx.2 y (hX₁V hy)⟩
    rwa [hcen] at this
  have := hdp.sup_eq
  rw [hC, sup_bot_eq] at this
  exact this

end CFSG.SignalizerFunctorTheorem.McBride.Near.Thm33b
