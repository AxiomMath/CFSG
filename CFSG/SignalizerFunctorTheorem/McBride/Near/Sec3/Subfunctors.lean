module

public import CFSG.SignalizerFunctorTheorem.McBride.Near.GlaubermanUniv
public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec3.ExistsSolvablePair
public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec3.Thm33Transport
public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec3.FittingMinimalNormal
public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec3.ExistsComplementB

public section

open CFSG.Open

namespace CFSG.SignalizerFunctorTheorem.McBride.Near

variable {G : Type*} [Group G] [Finite G] {p : ℕ} {A : Subgroup G} {θ : G → Subgroup G}

section Lemma31

omit [Finite G] in
theorem thetaSol_le (X : Subgroup G) : thetaSol p A θ X ≤ X :=
  iSup₂_le fun _ hZ => hZ.2.1

omit [Finite G] in
theorem admits_thetaSol (X : Subgroup G) : Admits (dsub A θ ⊔ A) (thetaSol p A θ X) :=
  Admits.iSup fun _ => Admits.iSup fun hZ => sup_le hZ.1.2 hZ.1.1.1

variable (hθ : NearFunctor p A θ)

include hθ

theorem thetaSol_eq_scalJoin {X : Subgroup G} (hX : X ∈ mtil p A θ) :
    thetaSol p A θ X = scalJoin X A (dsub A θ) := by
  have hDX : X ⊓ dsub A θ = dsub A θ := inf_eq_right.mpr hX.2
  have hset : {Z | Z ∈ mhat p A θ ∧ Z ≤ X ∧ Group.IsSolvable Z} =
      scalSet X A (dsub A θ) := by
    refine Set.ext fun Z => ⟨?_, ?_⟩
    · rintro ⟨hZ, hZX, hZs⟩
      refine ⟨hZX, ?_, hZs⟩
      rw [hDX]
      exact sup_le hZ.2 hZ.1.1
    · rintro ⟨hZX, hZadm, hZs⟩
      rw [hDX] at hZadm
      exact ⟨mem_mhat_of_le_mtil hθ.prime hX hZX hZadm, hZX, hZs⟩
  unfold thetaSol scalJoin
  rw [hset]

theorem isSolvable_thetaSol_apply
    {a : G} (ha : a ∈ A) (ha1 : a ≠ 1) :
    Group.IsSolvable (thetaSol p A θ (θ a)) := by
  have hXm : θ a ∈ mtil p A θ := apply_mem_mtil hθ ha ha1
  rw [thetaSol_eq_scalJoin hθ hXm]
  have hnear := hθ.near a ha ha1
  have hact : NearAsolvAction p A (θ a) :=
    { prime := hθ.prime
      odd := hθ.odd
      elemAbelian := hθ.elemAbelian
      admits := hXm.1.1
      nearPSolvable := hnear.1
      solvable_cen := hnear.2 }
  have hD : cenIn (θ a) A = dsub A θ := cenIn_eq_dsub hθ hXm
  have := (thm211b hact (X := θ a) le_rfl (by
    rw [hD]; exact sup_le (admits_dsub_of_le hXm.2) hXm.1.1)).2
  rwa [hD] at this

end Lemma31

theorem thetaSolFun_isFunctor
    (hθ : NearFunctor p A θ) :
    IsFunctor p A (thetaSolFun p A θ) where
  le_centralizer a ha ha1 :=
    (thetaSol_le (θ a)).trans (hθ.isFunctor.le_centralizer a ha ha1)
  coprime a ha ha1 := (hθ.isFunctor.coprime a ha ha1).coprime_dvd_right
    (Subgroup.card_dvd_of_le (thetaSol_le (θ a)))
  normalized a _ _ := (admits_thetaSol (θ a)).mono_left le_sup_right
  balance a ha ha1 b hb hb1 := by
    have hsol := isSolvable_thetaSol_apply hθ ha ha1
    have hDb : dsub A θ ≤ Subgroup.centralizer {b} :=
      (dsub_le_centralizer hθ).trans (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hb))
    have hAb : A ≤ Subgroup.centralizer {b} := fun g hg =>
      Subgroup.mem_centralizer_singleton_iff.mpr (commute_of_mem hθ.elemAbelian.1 hg hb)
    have hadm : Admits (dsub A θ ⊔ A) (thetaSol p A θ (θ a) ⊓ Subgroup.centralizer {b}) :=
      (admits_thetaSol (θ a)).inf (admits_centralizer_singleton (sup_le hDb hAb))
    have hle : thetaSol p A θ (θ a) ⊓ Subgroup.centralizer {b} ≤ θ b :=
      (inf_le_inf_right _ (thetaSol_le (θ a))).trans (hθ.isFunctor.balance a ha ha1 b hb hb1)
    have hmem : thetaSol p A θ (θ a) ⊓ Subgroup.centralizer {b} ∈
        {Z | Z ∈ mhat p A θ ∧ Z ≤ θ b ∧ Group.IsSolvable Z} :=
      ⟨⟨mem_assoc_of_le hθ.prime (apply_mem_assoc hθ ha ha1)
          (inf_le_left.trans (thetaSol_le (θ a))) (hadm.mono_left le_sup_right),
        hadm.mono_left le_sup_left⟩, hle,
        Group.isSolvable_of_isSolvable_injective
          (Subgroup.inclusion_injective (inf_le_left :
            thetaSol p A θ (θ a) ⊓ Subgroup.centralizer {b} ≤ thetaSol p A θ (θ a)))⟩
    exact le_iSup₂ (f := fun Z (_ : Z ∈ {Z | Z ∈ mhat p A θ ∧ Z ≤ θ b ∧
      Group.IsSolvable Z}) => Z) _ hmem

theorem thetaSolFun_solvable
    (hθ : NearFunctor p A θ) :
    ∀ a ∈ A, a ≠ 1 → Group.IsSolvable (thetaSolFun p A θ a) :=
  fun _ ha ha1 => isSolvable_thetaSol_apply hθ ha ha1

theorem thetaSolFun_complete
    (hθ : NearFunctor p A θ) (hrank : p ^ 3 ≤ Nat.card A) :
    ∃ S ∈ signalizers p A (thetaSolFun p A θ) (NearASolvable p A),
      (∀ X ∈ signalizers p A (thetaSolFun p A θ) (NearASolvable p A), X ≤ S) ∧
        Group.IsSolvable S := by
  obtain ⟨W, hWsol, hWA, hWcop, hWfix, hWmax⟩ := exists_greatest_signalizer_of_isFunctor
    hθ.prime hθ.elemAbelian hrank (thetaSolFun_isFunctor hθ) (thetaSolFun_solvable hθ)
  exact ⟨W, ⟨hWA, hWcop, fun a ha ha1 => (hWfix a ha ha1).le,
    nearASolvable_of_isSolvable hWsol hWcop⟩,
    fun X hX => hWmax X hX.1 hX.2.1 hX.2.2.1, hWsol⟩

theorem exists_solvable_pair
    (hθ : NearFunctor p A θ) {Y : Subgroup G} (hY : Y ∈ dset p A θ)
    {X₁ X₂ : Subgroup G} (h : (X₁, X₂) ∈ pairsY p A θ Y) :
    ∃ Z₁ Z₂ : Subgroup G, Z₁ ≤ X₁ ∧ Z₂ ≤ X₂ ∧ (Z₁, Z₂) ∈ pairsY p A θ Y ∧
      Group.IsSolvable Z₂ ∧ CyclicMod A (secCenIn A Z₁ Z₂) :=
  exists_solvable_pair' hθ hY h

section Thm33

variable {Y X Z : Subgroup G}

theorem thetaU_mem_usetX
    (hθ : NearFunctor p A θ) (hY : Y ∈ dset p A θ)
    (hX : X ∈ cset p A θ Y) : thetaU p A θ Y X ∈ usetX p A θ Y X :=
  thetaU_mem_usetX' hθ hY hX

theorem thetaM_thetaL_mem_pairsYX
    (hθ : NearFunctor p A θ) (hY : Y ∈ dset p A θ)
    (hX : X ∈ cset p A θ Y) :
    (thetaM p A θ Y X, thetaL p A θ Y X) ∈ pairsYX p A θ Y X :=
  thetaM_thetaL_mem_pairsYX' hθ hY hX

theorem kOf_le_thetaM
    (hθ : NearFunctor p A θ) (hY : Y ∈ dset p A θ)
    (hX : X ∈ cset p A θ Y) : kOf X ≤ thetaM p A θ Y X :=
  kOf_le_thetaM' hθ hY hX

theorem thetaY_mem_esetX
    (hθ : NearFunctor p A θ) (hY : Y ∈ dset p A θ)
    (hX : X ∈ cset p A θ Y) : thetaY p A θ Y X ∈ esetX p A θ Y X :=
  thetaY_mem_esetX' hθ hY hX

theorem thetaL_le_thetaY (hθ : NearFunctor p A θ) (hY : Y ∈ dset p A θ)
    (hX : X ∈ cset p A θ Y) : thetaL p A θ Y X ≤ thetaY p A θ Y X :=
  thetaL_le_thetaY' hθ hY hX

theorem thetaY_le_thetaM
    (hθ : NearFunctor p A θ) (hY : Y ∈ dset p A θ)
    (hX : X ∈ cset p A θ Y) : thetaY p A θ Y X ≤ thetaM p A θ Y X :=
  thetaY_le_thetaM' hθ hY hX

theorem thetaM_le_thetaU (hθ : NearFunctor p A θ) (hY : Y ∈ dset p A θ)
    (hX : X ∈ cset p A θ Y) : thetaM p A θ Y X ≤ thetaU p A θ Y X :=
  thetaM_le_thetaU' hθ hY hX

theorem thetaU_inf
    (hθ : NearFunctor p A θ) (hY : Y ∈ dset p A θ)
    (hX : X ∈ cset p A θ Y) (hZ : Z ∈ cset p A θ Y) :
    thetaU p A θ Y X ⊓ Z = X ⊓ thetaU p A θ Y Z :=
  thetaU_inf' hθ hY hX hZ

theorem thetaY_inf
    (hθ : NearFunctor p A θ) (hY : Y ∈ dset p A θ)
    (hX : X ∈ cset p A θ Y) (hZ : Z ∈ cset p A θ Y) :
    thetaY p A θ Y X ⊓ Z = X ⊓ thetaY p A θ Y Z :=
  thetaY_inf' hθ hY hX hZ

end Thm33

theorem fitting_minimal_normal
    (hθ : NearFunctor p A θ) {X₁ X₂ : Subgroup G}
    (h : (X₁, X₂) ∈ pairsP p A θ)
    [((dsub A θ ⊓ X₂).subgroupOf (dsub A θ)).Normal]
    [((dsub A θ ⊓ X₂).subgroupOf (dsub A θ ⊓ X₁)).Normal] :
    fittingPre (dsub A θ ⊓ X₁) (dsub A θ ⊓ X₂) = fittingPre (dsub A θ) (dsub A θ ⊓ X₂) ∧
    IsChiefFactorOf (dsub A θ) (fittingPre (dsub A θ) (dsub A θ ⊓ X₂)) (dsub A θ ⊓ X₂) ∧
    ∀ M : Subgroup G, IsChiefFactorOf (dsub A θ) M (dsub A θ ⊓ X₂) →
      M = fittingPre (dsub A θ) (dsub A θ ⊓ X₂) :=
  fitting_minimal_normal' hθ h

theorem exists_complement_B
    (hθ : NearFunctor p A θ) {D₂ : Subgroup G}
    (hD₂ : D₂ ∈ dset p A θ) {X : Subgroup G} (hX : X ∈ cset p A θ D₂)
    [(D₂.subgroupOf (dsub A θ)).Normal] {N L R : Subgroup G}
    (hN : N ≤ X) (hL : L ≤ X) (hR : R ≤ X)
    (ha : IsNormalIn N (R ⊔ dsub A θ ⊔ A) ∧ IsNormalIn L (R ⊔ dsub A θ ⊔ A) ∧
      IsNormalIn R (R ⊔ dsub A θ ⊔ A))
    (hb : IsChiefFactorOf (R ⊔ dsub A θ ⊔ A) L N ∧ L ≤ R)
    (hc : A ⊔ R ≤ secCenIn (R ⊔ dsub A θ ⊔ A) L N)
    (hd : R ⊓ dsub A θ = fittingPre (dsub A θ) D₂ ∧ dsub A θ ⊓ N ≤ D₂ ∧
      IsDirectProductMod N (fittingPre (dsub A θ) D₂ ⊔ N) (D₂ ⊔ N) L) :
    ∃ B : Subgroup G, B ≤ R ∧ IsNormalIn B (R ⊔ dsub A θ ⊔ A) ∧ B ⊓ dsub A θ = D₂ ∧
      R = B ⊔ fittingPre (dsub A θ) D₂ :=
  exists_complement_B' hθ hD₂ hX hN hL hR ha hb hc hd

end CFSG.SignalizerFunctorTheorem.McBride.Near
