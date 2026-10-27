module

public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec3.Thm310
public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec3.Thm311b

public section

open CFSG.Open

namespace CFSG.SignalizerFunctorTheorem.McBride.Near

variable {G : Type*} [Group G] [Finite G] {p : ℕ} {A : Subgroup G} {θ : G → Subgroup G}

omit [Finite G] in
theorem thetaY_le (Y X : Subgroup G) : thetaY p A θ Y X ≤ X :=
  iSup₂_le fun _ hZ => hZ.2

theorem thetaY_mem_signalizers (hθ : NearFunctor p A θ) {Y X : Subgroup G}
    (hE : thetaY p A θ Y X ∈ esetX p A θ Y X) :
    thetaY p A θ Y X ∈ signalizers p A (thetaYFun p A θ Y) (NearASolvable p A) := by
  have hT : thetaY p A θ Y X ∈ mhat p A θ := hE.1.1
  obtain ⟨⟨hAT, hcop, hfix, hnear⟩, hDT⟩ := hT
  refine ⟨hAT, hcop, fun a ha ha1 => ?_, hnear⟩
  have hDa : dsub A θ ≤ Subgroup.centralizer {a} :=
    (dsub_le_centralizer hθ).trans (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr ha))
  have hAa : A ≤ Subgroup.centralizer {a} ⊔ A := le_sup_right
  have hC : thetaY p A θ Y X ⊓ Subgroup.centralizer {a} ∈ esetX p A θ Y (θ a) := by
    have hadm : Admits (dsub A θ ⊔ A) (thetaY p A θ Y X ⊓ Subgroup.centralizer {a}) := by
      refine sup_le ?_ ?_
      · exact fun d hd => Subgroup.inf_normalizer_le_normalizer_inf
          ⟨hDT hd, admits_centralizer_singleton hDa hd⟩
      · intro g hg
        refine Subgroup.inf_normalizer_le_normalizer_inf ⟨hAT hg, ?_⟩
        refine admits_centralizer_singleton (Q := Subgroup.zpowers g) ?_ ?_
        · rw [Subgroup.zpowers_le]
          exact Subgroup.mem_centralizer_singleton_iff.mpr (commute_of_mem hθ.elemAbelian.1 hg ha)
        · exact Subgroup.mem_zpowers g
    refine ⟨⟨mem_mhat_of_le_mhat hθ.prime hE.1.1 inf_le_left hadm, ?_⟩, ?_⟩
    · rw [inf_assoc, inf_eq_right.mpr hDa]
      exact hE.1.2
    · exact hfix a ha ha1
  exact le_iSup₂ (f := fun Z (_ : Z ∈ esetX p A θ Y (θ a)) => Z) _ hC

theorem thetaY_mem_esetX_of_rank
    (hθ : NearFunctor p A θ) (hrank : p ^ 3 ≤ Nat.card A)
    {Y : Subgroup G} (hY : Y ∈ dset p A θ) {a : G} (ha : a ∈ A) (ha1 : a ≠ 1) :
    thetaY p A θ Y (θ a) ∈ esetX p A θ Y (θ a) :=
  thetaY_mem_esetX_of_rank' hθ hrank hY ha ha1

theorem thetaY_isFunctor
    (hθ : NearFunctor p A θ) (hrank : p ^ 3 ≤ Nat.card A)
    {Y : Subgroup G} (hY : Y ∈ dset p A θ) : IsFunctor p A (thetaYFun p A θ Y) :=
  thetaY_isFunctor' hθ hrank hY

theorem thetaLG_mem_assoc
    (hθ : NearFunctor p A θ)
    {Y : Subgroup G} (hY : Y ∈ dset p A θ)
    (hc : IsCompleteIn (signalizers p A (thetaYFun p A θ Y) (NearASolvable p A))) :
    thetaLG p A θ Y ∈ assoc p A θ := by
  obtain ⟨W', hW', hmax⟩ := hc
  have hle : thetaLG p A θ Y ≤ W' := by
    refine iSup₂_le fun X hX => ?_
    exact (thetaL_le_thetaY hθ hY hX).trans
      (hmax _ (thetaY_mem_signalizers hθ (thetaY_mem_esetX hθ hY hX)))
  have hW'θ : W' ∈ assoc p A θ :=
    signalizers_mono_functor (fun a _ _ => thetaY_le Y (θ a)) hW'
  have hadm : Admits A (thetaLG p A θ Y) := by
    refine Admits.iSup fun X => Admits.iSup fun _ => ?_
    refine Admits.iSup fun P => Admits.iSup fun hP => ?_
    exact hP.1.1.2.1.1.1
  exact mem_assoc_of_le hθ.prime hW'θ hle hadm

theorem thetaMG_le_normalizer_thetaLG
    (hθ : NearFunctor p A θ) (hrank : Nat.card A = p ^ 3)
    {Y : Subgroup G} (hY : Y ∈ dset p A θ)
    (hc : IsCompleteIn (signalizers p A (thetaYFun p A θ Y) (NearASolvable p A))) :
    thetaMG p A θ Y ≤ Subgroup.normalizer (thetaLG p A θ Y : Set G) :=
  thetaMG_le_normalizer_thetaLG' hθ hrank hY hc

end CFSG.SignalizerFunctorTheorem.McBride.Near
