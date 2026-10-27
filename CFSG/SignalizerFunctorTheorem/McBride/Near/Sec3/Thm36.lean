module

public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec3.ThetaUMem
public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec3.Thm36Aux6
public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec3.Thm36Aux5

public section

open CFSG.Open
open scoped commutatorElement

universe u

namespace CFSG.SignalizerFunctorTheorem.McBride.Near

variable {G : Type u} [Group G] [Finite G] {p : ℕ} {A : Subgroup G} {θ : G → Subgroup G}

namespace Thm36

variable (hθ : NearFunctor p A θ)

include hθ

omit [Finite G] in
theorem dset_le_admits {Y : Subgroup G} (hY : Y ∈ dset p A θ) :
    Y ≤ dsub A θ ∧ Admits (dsub A θ ⊔ A) Y := by
  obtain ⟨P, hP, rfl⟩ := hY
  refine ⟨inf_le_left, Admits.inf (sup_le Subgroup.le_normalizer (admits_dsub hθ)) ?_⟩
  exact sup_le hP.2.1.2 hP.2.1.1.1

theorem mem_cset_of_not_inf_le
    (hrank : p ^ 3 ≤ Nat.card A) {X : Subgroup G}
    (hX : X ∈ mtil p A θ) {X₁ X₂ : Subgroup G} (h₁ : X₁ ≤ X) (h₂ : X₂ ≤ X)
    (hd₁ : Admits (dsub A θ ⊔ A) X₁) (hd₂ : Admits (dsub A θ ⊔ A) X₂)
    (hc : IsChiefFactorOf (X₁ ⊔ dsub A θ ⊔ A) X₁ X₂) (hns : ¬ IsSolvableSection X₁ X₂)
    {Y : Subgroup G} (hY : Y ∈ dset p A θ) (hX₂ : X₂ ⊓ dsub A θ ≤ Y)
    (hfa : ¬ X₁ ⊓ dsub A θ ≤ Y) : X ∈ cset p A θ Y := by
  have hXD : cenIn X (A : Set G) = dsub A θ := cenIn_eq_dsub hθ hX
  have hnear : NearAsolvAction p A X := Thm33a.nearAsolvAction_of_mem_mtil hθ hX
  obtain ⟨hYD, hYadm⟩ := dset_le_admits hθ hY
  set D : Subgroup G := dsub A θ with hDdef
  have hDX : D ≤ X := hX.2
  have hDcen : D ≤ Subgroup.centralizer (A : Set G) := dsub_le_centralizer hθ
  have hDnA : A ≤ Subgroup.normalizer (D : Set G) := admits_dsub hθ
  have hDDA : Admits (D ⊔ A) D := sup_le Subgroup.le_normalizer hDnA
  have hX₂X₁ : X₂ ≤ X₁ := hc.2.2.1.le
  have hX₁n₂ : X₁ ≤ Subgroup.normalizer (X₂ : Set G) := (le_sup_left.trans le_sup_left).trans hc.1.2
  obtain ⟨P, hP, hYP⟩ := hY
  have hPY : P ∈ pairsY p A θ Y := ⟨hP, by rw [hYP, inf_comm]⟩
  have hUm : P.1 ⊔ D ∈ mtil p A θ := sup_dsub_mem_mtil hθ hP.1
  have hPU : P ∈ pairsYX p A θ Y (P.1 ⊔ D) := ⟨hPY, le_sup_left⟩
  have hUnear : NearAsolvAction p A (P.1 ⊔ D) := Thm33a.nearAsolvAction_of_mem_mtil hθ hUm
  have hPi : (P.1, P.2) ∈ iPairsY A (P.1 ⊔ D) Y := by
    rw [← pairsYX_eq_iPairsY hθ hUm]
    exact hPU
  obtain ⟨B₁, hB₁A, hB₁c, hB₁pair⟩ := Thm32.exists_cen_pair hUnear hPi
  set C : Subgroup G := secCenIn D X₁ X₂ with hCdef
  have hCD : C ≤ D := inf_le_left
  have hCadm : Admits (D ⊔ A) C := admits_secCenIn hDDA hd₁ hd₂
  have hX₁' : IsDAIn A X X₁ := ⟨h₁, by rw [hXD]; exact hd₁⟩
  have hX₂' : IsDAIn A X X₂ := ⟨h₂, by rw [hXD]; exact hd₂⟩
  have hc' : IsChiefFactorOf (X₁ ⊔ cenIn X (A : Set G) ⊔ A) X₁ X₂ := by
    rw [hXD]
    exact hc
  have hX₂C : X₂ ⊓ D ≤ C := fun x hx =>
    Subgroup.mem_inf.mpr ⟨(Subgroup.mem_inf.mp hx).2, le_sectionCentralizer hX₂X₁ hX₁n₂ hx.1⟩
  have hCpair : (X₁ ⊔ C, X₂ ⊔ C) ∈ iPairsY A X C :=
    pairs_of_secCen hnear hX₁' hX₂' hc' hns (by rw [hXD]; exact hX₂C)
      (by rw [hXD]; exact hCadm) (by rw [hXD]; exact hCD) (by rw [hXD])
  obtain ⟨B, hBA, hBc, hBpair⟩ := Thm32.exists_cen_pair hnear hCpair
  set X₁' : Subgroup G := cenIn X₁ (B : Set G) with hX₁'def
  set X₂' : Subgroup G := cenIn X₂ (B : Set G) with hX₂'def
  have hCB : C ≤ Subgroup.centralizer (B : Set G) :=
    hCD.trans (hDcen.trans (Subgroup.centralizer_le hBA))
  have hCn₁ : C ≤ Subgroup.normalizer (X₁ : Set G) := hCD.trans (le_sup_left.trans hd₁)
  have hCn₂ : C ≤ Subgroup.normalizer (X₂ : Set G) := hCD.trans (le_sup_left.trans hd₂)
  rw [cenIn_sup_eq hCn₁ hCB, cenIn_sup_eq hCn₂ hCB] at hBpair
  have hX₁'X : X₁' ≤ X := inf_le_left.trans h₁
  have hX₂'X₁' : X₂' ≤ X₁' := inf_le_inf_right _ hX₂X₁
  have hDB : D ≤ Subgroup.centralizer (B : Set G) := hDcen.trans (Subgroup.centralizer_le hBA)
  have hAB : A ≤ Subgroup.centralizer (B : Set G) := by
    have := hθ.elemAbelian.1
    intro a ha
    exact Subgroup.mem_centralizer_iff.mpr fun b hb =>
      congrArg Subtype.val (mul_comm' (⟨b, hBA hb⟩ : A) ⟨a, ha⟩)
  have hDAcenB : Admits (D ⊔ A) (Subgroup.centralizer (B : Set G)) :=
    (sup_le hDB hAB).trans Subgroup.le_normalizer
  have hDA₁' : Admits (D ⊔ A) X₁' := Admits.inf hd₁ hDAcenB
  have hDA₂' : Admits (D ⊔ A) X₂' := Admits.inf hd₂ hDAcenB
  have hCn₂' : C ≤ Subgroup.normalizer (X₂' : Set G) := hCD.trans (le_sup_left.trans hDA₂')
  have hCX₁' : X₁' ⊓ C ≤ X₂' := by
    intro c hc1
    obtain ⟨hcX₁', hcC⟩ := Subgroup.mem_inf.mp hc1
    have hcomm : ∀ y ∈ X₁, ⁅c, y⁆ ∈ X₂ := fun y hy =>
      (mem_sectionCentralizer_iff.mp (Subgroup.mem_inf.mp hcC).2).2.2 y hy
    exact Subgroup.mem_inf.mpr ⟨mem_of_forall_commutator_mem hc hns (Subgroup.mem_inf.mp hcX₁').1
      hcomm, (Subgroup.mem_inf.mp hcX₁').2⟩
  have hinfeq : X₁' ⊓ (X₂' ⊔ C) = X₂' := by
    refine le_antisymm (fun x hx => ?_) (le_inf hX₂'X₁' le_sup_left)
    obtain ⟨hxX₁', hxS⟩ := Subgroup.mem_inf.mp hx
    obtain ⟨r, hr, c, hc', rfl⟩ := (Thm32.mem_sup_iff_mul hCn₂').mp hxS
    have hcX₁' : c ∈ X₁' := by
      have := mul_mem (inv_mem (hX₂'X₁' hr)) hxX₁'
      simpa using this
    exact mul_mem hr (hCX₁' ⟨hcX₁', hc'⟩)
  have hBchief := Thm33a.pair_chief hBpair
  rw [hXD] at hBchief
  have hsup : X₁' ⊔ (X₂' ⊔ C) = X₁' ⊔ C :=
    le_antisymm (sup_le le_sup_left (sup_le (hX₂'X₁'.trans le_sup_left) le_sup_right))
      (sup_le_sup_left le_sup_right _)
  have hchief' : IsChiefFactorOf (X₁' ⊔ D ⊔ A) X₁' X₂' := by
    have := isChiefFactorOf_subpair hBchief (le_sup_left : X₁' ≤ X₁' ⊔ C) hDA₁' hsup
    rwa [hinfeq] at this
  have hns' : ¬ IsSolvableSection X₁' X₂' := by
    intro hs
    rw [← hinfeq] at hs
    have hnor : Admits (X₁' ⊔ C) (X₂' ⊔ C) := by
      have := Thm33a.le_H.trans (Thm33a.pair_admits_H₂ hBpair)
      exact this
    exact Thm33a.not_isSolvableSection_of_mem_iPairs hBpair.1
      (isSolvableSection_of_subpair hnor le_sup_left hsup hs)
  have hX₂'Y : X₂' ⊓ D ≤ Y := (inf_le_inf_right _ inf_le_left).trans hX₂
  set E : Subgroup G := B ⊓ B₁ with hEdef
  have hE1 : E ≠ ⊥ := inf_ne_bot_of_cyclicMod hθ.prime hθ.elemAbelian hrank hBA hB₁A hBc hB₁c
  have hEA : E ≤ A := inf_le_left.trans hBA
  have hWm : thetaOf θ E ∈ mtil p A θ := thetaOf_mem_mtil hθ hEA hE1
  set W : Subgroup G := thetaOf θ E with hWdef
  have hXassoc : ∀ a ∈ A, a ≠ 1 → X ⊓ Subgroup.centralizer {a} ≤ θ a := hX.1.2.2.1
  have hX₁'W : X₁' ≤ W :=
    le_thetaOf hXassoc hX₁'X hEA
      (inf_le_right.trans (Subgroup.centralizer_le (inf_le_left : E ≤ B)))
  have hX₂'W : X₂' ≤ W := hX₂'X₁'.trans hX₁'W
  have hUassoc : ∀ a ∈ A, a ≠ 1 → (P.1 ⊔ D) ⊓ Subgroup.centralizer {a} ≤ θ a := hUm.1.2.2.1
  have hZ'pair : (cenIn P.1 (B₁ : Set G), cenIn P.2 (B₁ : Set G)) ∈
      pairsYX p A θ Y (P.1 ⊔ D) := by
    rw [pairsYX_eq_iPairsY hθ hUm]
    exact hB₁pair
  have hZ₁'W : cenIn P.1 (B₁ : Set G) ≤ W :=
    le_thetaOf hUassoc (inf_le_left.trans le_sup_left) hEA
      (inf_le_right.trans (Subgroup.centralizer_le (inf_le_right : E ≤ B₁)))
  have hWY : (iPairsY A W Y).Nonempty := by
    rw [← pairsYX_eq_iPairsY hθ hWm]
    exact ⟨_, hZ'pair.1, hZ₁'W⟩
  have hWnear : NearAsolvAction p A W := Thm33a.nearAsolvAction_of_mem_mtil hθ hWm
  have hWD : cenIn W (A : Set G) = D := cenIn_eq_dsub hθ hWm
  have hX₁W : IsDAIn A W X₁' := ⟨hX₁'W, by rw [hWD]; exact hDA₁'⟩
  have hX₂W : IsDAIn A W X₂' := ⟨hX₂'W, by rw [hWD]; exact hDA₂'⟩
  have hcW : IsChiefFactorOf (X₁' ⊔ cenIn W (A : Set G) ⊔ A) X₁' X₂' := by
    rw [hWD]
    exact hchief'
  have hX₂'YW : X₂' ⊓ cenIn W (A : Set G) ≤ Y := by
    rw [hWD]
    exact hX₂'Y
  rcases iThm36 hWnear hWY hX₁W hX₂W hcW hns' hX₂'YW with h1 | h1
  · exfalso
    apply hfa
    intro x hx
    obtain ⟨hxX₁, hxD⟩ := Subgroup.mem_inf.mp hx
    rw [hWD] at h1
    exact h1 ⟨Subgroup.mem_inf.mpr ⟨hxX₁, hDB hxD⟩, hxD⟩
  · rw [hWD] at h1
    have hP2 := pairs_of_secCen hWnear hX₁W hX₂W hcW hns' hX₂'YW (by rw [hWD]; exact hYadm)
      (by rw [hWD]; exact hYD) (by rw [hWD]; exact h1)
    rw [← pairsYX_eq_iPairsY hθ hWm] at hP2
    exact ⟨hX, _, hP2.1, sup_le hX₁'X (hYD.trans hDX)⟩

end Thm36

theorem thm36'
    (hθ : NearFunctor p A θ) (hrank : p ^ 3 ≤ Nat.card A) {X : Subgroup G}
    (hX : X ∈ mtil p A θ) {X₁ X₂ : Subgroup G} (h₁ : X₁ ≤ X) (h₂ : X₂ ≤ X)
    (hd₁ : Admits (dsub A θ ⊔ A) X₁) (hd₂ : Admits (dsub A θ ⊔ A) X₂)
    (hc : IsChiefFactorOf (X₁ ⊔ dsub A θ ⊔ A) X₁ X₂) (hns : ¬ IsSolvableSection X₁ X₂)
    {Y : Subgroup G} (hY : Y ∈ dset p A θ) (hX₂ : X₂ ⊓ dsub A θ ≤ Y) :
    X₁ ⊓ dsub A θ ≤ Y ∨ (X₁ ⊔ Y, X₂ ⊔ Y) ∈ pairsY p A θ Y := by
  have hXD : cenIn X (A : Set G) = dsub A θ := cenIn_eq_dsub hθ hX
  have hnear : NearAsolvAction p A X := Thm33a.nearAsolvAction_of_mem_mtil hθ hX
  obtain ⟨hYD, hYadm⟩ := Thm36.dset_le_admits hθ hY
  by_cases hXc : X ∈ cset p A θ Y
  · have hX₁' : IsDAIn A X X₁ := ⟨h₁, by rw [hXD]; exact hd₁⟩
    have hX₂' : IsDAIn A X X₂ := ⟨h₂, by rw [hXD]; exact hd₂⟩
    have hc' : IsChiefFactorOf (X₁ ⊔ cenIn X (A : Set G) ⊔ A) X₁ X₂ := by
      rw [hXD]
      exact hc
    have hX₂Y : X₂ ⊓ cenIn X (A : Set G) ≤ Y := by
      rw [hXD]
      exact hX₂
    have hne : (iPairsY A X Y).Nonempty := by
      rw [← pairsYX_eq_iPairsY hθ hX]
      exact hXc.2
    rcases Thm36.iThm36 hnear hne hX₁' hX₂' hc' hns hX₂Y with h1 | h1
    · left
      rwa [hXD] at h1
    · right
      rw [hXD] at h1
      have hP := Thm36.pairs_of_secCen hnear hX₁' hX₂' hc' hns hX₂Y (by rw [hXD]; exact hYadm)
        (by rw [hXD]; exact hYD) (by rw [hXD]; exact h1)
      rw [← pairsYX_eq_iPairsY hθ hX] at hP
      exact hP.1
  · left
    by_contra hfa
    exact hXc (Thm36.mem_cset_of_not_inf_le hθ hrank hX h₁ h₂ hd₁ hd₂ hc hns hY hX₂ hfa)

theorem inf_le_of_not_mem_cset
    (hθ : NearFunctor p A θ) (hrank : p ^ 3 ≤ Nat.card A)
    {X : Subgroup G} (hX : X ∈ mtil p A θ) {X₁ X₂ : Subgroup G} (h₁ : X₁ ≤ X) (h₂ : X₂ ≤ X)
    (hd₁ : Admits (dsub A θ ⊔ A) X₁) (hd₂ : Admits (dsub A θ ⊔ A) X₂)
    (hc : IsChiefFactorOf (X₁ ⊔ dsub A θ ⊔ A) X₁ X₂) (hns : ¬ IsSolvableSection X₁ X₂)
    {Y : Subgroup G} (hY : Y ∈ dset p A θ) (hX₂ : X₂ ⊓ dsub A θ ≤ Y)
    (hXc : X ∉ cset p A θ Y) : X₁ ⊓ dsub A θ ≤ Y := by
  by_contra hfa
  exact hXc (Thm36.mem_cset_of_not_inf_le hθ hrank hX h₁ h₂ hd₁ hd₂ hc hns hY hX₂ hfa)

end CFSG.SignalizerFunctorTheorem.McBride.Near
