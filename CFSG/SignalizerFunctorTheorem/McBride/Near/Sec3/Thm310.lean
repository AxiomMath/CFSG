module

public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec3.Subfunctors
public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec3.HypA39
public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec3.Thm36
public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec3.Thm310Aux2

public section

open CFSG.Open

universe u

namespace CFSG.SignalizerFunctorTheorem.McBride.Near

variable {G : Type u} [Group G] [Finite G] {p : ℕ} {A : Subgroup G} {θ : G → Subgroup G}

namespace Thm310

theorem mem_esetX_iff (hθ : NearFunctor p A θ) {Y X : Subgroup G} (hX : X ∈ mtil p A θ)
    {Z : Subgroup G} : Z ∈ esetX p A θ Y X ↔ Z ∈ ssSet X A (dsub A θ) Y := by
  constructor
  · rintro ⟨⟨hZm, hZY⟩, hZX⟩
    exact ⟨hZX, sup_le hZm.2 hZm.1.1, hZY⟩
  · rintro ⟨hZX, hZa, hZY⟩
    exact ⟨⟨mem_mhat_of_le_mtil hθ.prime hX hZX hZa, hZY⟩, hZX⟩

theorem mem_esetX_of_pair
    (hθ : NearFunctor p A θ) (hrank : p ^ 3 ≤ Nat.card A)
    {Z₁ Z₂ : Subgroup G} (hZP : (Z₁, Z₂) ∈ pairsP p A θ)
    (hcyc : CyclicMod A (secCenIn A Z₁ Z₂)) (hY : dsub A θ ⊓ Z₂ ∈ dset p A θ)
    {X : Subgroup G} (hX : X ∈ mtil p A θ) (hXc : X ∉ cset p A θ (dsub A θ ⊓ Z₂)) :
    thetaY p A θ (dsub A θ ⊓ Z₂) X ∈ esetX p A θ (dsub A θ ⊓ Z₂) X := by
  have hZm₁ : Z₁ ∈ mhat p A θ := hZP.1
  have hZch : IsChiefFactorOf (Z₁ ⊔ dsub A θ ⊔ A) Z₁ Z₂ := hZP.2.2.1
  have hZ₂Z₁ : Z₂ ≤ Z₁ := hZch.2.2.1.le
  have hZY : (Z₁, Z₂) ∈ pairsY p A θ (dsub A θ ⊓ Z₂) := ⟨hZP, inf_comm _ _⟩
  have hZU : Z₁ ⊔ dsub A θ ∈ mtil p A θ := sup_dsub_mem_mtil hθ hZm₁
  have hZiY : (Z₁, Z₂) ∈ iPairsY A (Z₁ ⊔ dsub A θ) (dsub A θ ⊓ Z₂) := by
    rw [← pairsYX_eq_iPairsY hθ hZU]
    exact ⟨hZY, le_sup_left⟩
  have hcenU : cenIn (Z₁ ⊔ dsub A θ) (A : Set G) = dsub A θ := cenIn_eq_dsub hθ hZU
  have hact : NearAsolvAction p A (Z₁ ⊔ dsub A θ) := Thm33a.nearAsolvAction_of_mem_mtil hθ hZU
  have hCA : secCenIn A Z₁ Z₂ ≤ A := inf_le_left
  obtain ⟨E, hEC, hEcard⟩ := exists_card_sq_le hθ.prime hθ.elemAbelian hrank hCA hcyc
  have hEA : E ≤ A := hEC.trans hCA
  have hpairE := cenIn_mem_iPairsY hact hZiY hEA hEC
  obtain ⟨hYD, hYadm⟩ := Thm36.dset_le_admits hθ hY
  have hYN : ((dsub A θ ⊓ Z₂).subgroupOf (dsub A θ)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hYD).mpr (le_sup_left.trans hYadm)
  have hYN₁ : ((dsub A θ ⊓ Z₂).subgroupOf (dsub A θ ⊓ Z₁)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (inf_le_inf_left _ hZ₂Z₁)).mpr
      (inf_le_left.trans (le_sup_left.trans hYadm))
  obtain ⟨-, hF2, hF3⟩ := fitting_minimal_normal hθ hZP
  have h15 : HypA15 p X A (dsub A θ) (fittingPre (dsub A θ) (dsub A θ ⊓ Z₂))
      (dsub A θ ⊓ Z₂) :=
    { prime := hθ.prime
      odd := hθ.odd
      a1_elemAbelian := hθ.elemAbelian
      a1_admits := hX.1.1
      a1_near := hX.1.2.2.2
      a3 := (cenIn_eq_dsub hθ hX).symm
      a4_chief := hF2
      a4_unique := hF3
      a4c := secCenIn_fittingPre (isSolvable_dsub hθ) hF2
      a5 := fun X₁ X₂ h₁ h₂ hd₁ hd₂ hc hns hX₂ =>
        inf_le_of_not_mem_cset hθ hrank hX h₁ h₂ hd₁ hd₂ hc hns hY hX₂ hXc }
  have h6 : ∀ e ∈ E, e ≠ 1 → HypA6 (X ⊓ Subgroup.centralizer {e}) A (dsub A θ)
      (fittingPre (dsub A θ) (dsub A θ ⊓ Z₂)) (dsub A θ ⊓ Z₂) := by
    intro e he he1
    have heA : e ∈ A := hEA he
    have hθe : θ e ∈ mtil p A θ := apply_mem_mtil hθ heA he1
    have hcenθe : cenIn (θ e) (A : Set G) = dsub A θ := cenIn_eq_dsub hθ hθe
    have hnear : NearAsolvAction p A (θ e) := Thm33a.nearAsolvAction_of_mem_mtil hθ hθe
    have hZ₁e : Z₁ ⊓ Subgroup.centralizer {e} ≤ θ e := hZm₁.1.2.2.1 e heA he1
    have hZ₂e : Z₂ ⊓ Subgroup.centralizer {e} ≤ θ e := hZP.2.1.1.2.2.1 e heA he1
    have hEe : Subgroup.centralizer (E : Set G) ≤ Subgroup.centralizer {e} :=
      Subgroup.centralizer_le (Set.singleton_subset_iff.mpr he)
    have hpairθ : (cenIn Z₁ (E : Set G), cenIn Z₂ (E : Set G)) ∈
        iPairsY A (θ e) (dsub A θ ⊓ Z₂) :=
      mem_iPairsY_of_le (hcenθe.trans hcenU.symm) hpairE
        ((inf_le_inf_left _ hEe).trans hZ₁e) ((inf_le_inf_left _ hEe).trans hZ₂e)
    exact (hypA6_of_iPairsY hnear hcenθe ⟨_, hpairθ⟩).mono (hX.1.2.2.1 e heA he1)
  have h5 : p = 3 → ∀ x ∈ fittingPre (dsub A θ) (dsub A θ ⊓ Z₂),
      ∃ k : ℕ, x ^ (5 ^ k) ∈ dsub A θ ⊓ Z₂ := fun hp3 x hx =>
    ⟨1, by simpa using pow_five_mem_of_mem_fittingPre hp3 hact hcenU hZiY x hx⟩
  have hH : HypA p X A (dsub A θ) (fittingPre (dsub A θ) (dsub A θ ⊓ Z₂)) (dsub A θ ⊓ Z₂) :=
    ⟨h15, hypA6_of_centralizers h15 hEA hEcard h6 h5⟩
  obtain ⟨M₀, hM₀, hmax⟩ := exists_max_ssSet hH
  have hM₀e : M₀ ∈ esetX p A θ (dsub A θ ⊓ Z₂) X := (mem_esetX_iff hθ hX).mpr hM₀
  have heq : thetaY p A θ (dsub A θ ⊓ Z₂) X = M₀ :=
    le_antisymm (iSup₂_le fun Z hZ => hmax Z ((mem_esetX_iff hθ hX).mp hZ))
      (le_iSup₂ (f := fun Z (_ : Z ∈ esetX p A θ (dsub A θ ⊓ Z₂) X) => Z) M₀ hM₀e)
  rw [heq]
  exact hM₀e

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

end Thm310

theorem thetaY_mem_esetX_of_rank'
    (hθ : NearFunctor p A θ) (hrank : p ^ 3 ≤ Nat.card A)
    {Y : Subgroup G} (hY : Y ∈ dset p A θ) {a : G} (ha : a ∈ A) (ha1 : a ≠ 1) :
    thetaY p A θ Y (θ a) ∈ esetX p A θ Y (θ a) := by
  have hX : θ a ∈ mtil p A θ := apply_mem_mtil hθ ha ha1
  by_cases hXc : θ a ∈ cset p A θ Y
  · exact thetaY_mem_esetX hθ hY hXc
  · obtain ⟨P, hP, hYP⟩ : ∃ P ∈ pairsP p A θ, Y = dsub A θ ⊓ P.2 := id hY
    have hPY : (P.1, P.2) ∈ pairsY p A θ Y := ⟨hP, by rw [hYP, inf_comm]⟩
    obtain ⟨Z₁, Z₂, -, -, hZ, -, hcyc⟩ := exists_solvable_pair hθ hY hPY
    have hYD : Y = dsub A θ ⊓ Z₂ := by rw [← hZ.2, inf_comm]
    subst hYD
    exact Thm310.mem_esetX_of_pair hθ hrank hZ.1 hcyc hY hX hXc

theorem thetaY_isFunctor'
    (hθ : NearFunctor p A θ) (hrank : p ^ 3 ≤ Nat.card A)
    {Y : Subgroup G} (hY : Y ∈ dset p A θ) : IsFunctor p A (thetaYFun p A θ Y) where
  le_centralizer a ha ha1 :=
    (Thm310.thetaY_le Y (θ a)).trans (hθ.isFunctor.le_centralizer a ha ha1)
  coprime a ha ha1 := (hθ.isFunctor.coprime a ha ha1).coprime_dvd_right
    (Subgroup.card_dvd_of_le (Thm310.thetaY_le Y (θ a)))
  normalized _ ha ha1 :=
    (Thm310.thetaY_mem_signalizers hθ (thetaY_mem_esetX_of_rank' hθ hrank hY ha ha1)).1
  balance _ ha ha1 b hb hb1 :=
    (Thm310.thetaY_mem_signalizers hθ (thetaY_mem_esetX_of_rank' hθ hrank hY ha ha1)).2.2.1 b hb hb1

end CFSG.SignalizerFunctorTheorem.McBride.Near
