module

public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec3.Subfunctors

public section

open CFSG.Open

universe u

namespace CFSG.SignalizerFunctorTheorem.McBride.Near

namespace Thm53A

variable {G : Type u} [Group G] [Finite G] {p : ℕ} {A : Subgroup G} {θ : G → Subgroup G}

theorem card_le_of_cyclicMod (hA : IsElemAbelian p A) (hp : p.Prime) {B : Subgroup G}
    (hBA : B ≤ A) (hcyc : CyclicMod A B) : Nat.card A ≤ Nat.card B * p := by
  obtain ⟨a, haA, hle⟩ := hcyc
  have hza : Subgroup.zpowers a ≤ A := Subgroup.zpowers_le.mpr haA
  have hsup : B ⊔ Subgroup.zpowers a = A := le_antisymm (sup_le hBA hza) hle
  have hadm : Admits (Subgroup.zpowers a) B := fun x hx =>
    Subgroup.centralizer_le_normalizer (B : Set G) (Subgroup.mem_centralizer_iff.mpr fun b hb =>
      (commute_of_mem hA.1 (hBA hb) (hza hx)).eq)
  have h1 := AssocSup.card_sup_dvd_mul hadm
  rw [hsup] at h1
  have h2 : Nat.card (Subgroup.zpowers a) ≤ p := by
    rw [Nat.card_zpowers]
    exact Nat.le_of_dvd hp.pos (orderOf_dvd_of_pow_eq_one (hA.2 a haA))
  calc Nat.card A ≤ Nat.card B * Nat.card (Subgroup.zpowers a) :=
        Nat.le_of_dvd (Nat.mul_pos Nat.card_pos Nat.card_pos) h1
    _ ≤ Nat.card B * p := Nat.mul_le_mul_left _ h2

theorem exists_pair_centralized
    (hθ : NearFunctor p A θ) {Y : Subgroup G} (hY : Y ∈ dset p A θ) :
    ∃ Z₁ Z₂ B : Subgroup G, (Z₁, Z₂) ∈ pairsY p A θ Y ∧ B ≤ A ∧ CyclicMod A B ∧
      Z₁ ≤ Subgroup.centralizer (B : Set G) := by
  obtain ⟨P, hP, rfl⟩ := hY
  have hPY : P ∈ pairsY p A θ (dsub A θ ⊓ P.2) := ⟨hP, inf_comm _ _⟩
  have hXm : P.1 ⊔ dsub A θ ∈ mtil p A θ := sup_dsub_mem_mtil hθ hP.1
  have hact : NearAsolvAction p A (P.1 ⊔ dsub A θ) :=
    { prime := hθ.prime
      odd := hθ.odd
      elemAbelian := hθ.elemAbelian
      admits := hXm.1.1
      nearPSolvable := hXm.1.2.2.2.1
      solvable_cen := hXm.1.2.2.2.2 }
  have heq := pairsYX_eq_iPairsY (Y := dsub A θ ⊓ P.2) hθ hXm
  have hP' : (P.1, P.2) ∈ iPairsY A (P.1 ⊔ dsub A θ) (dsub A θ ⊓ P.2) := by
    rw [← heq]
    exact ⟨hPY, le_sup_left⟩
  obtain ⟨W₁, W₂, hW₁, hW₂, hW, -⟩ := Thm32.exists_solvable_of_pair hact hP'
  obtain ⟨B, hBA, hcyc, hpair⟩ := Thm32.exists_cen_pair hact hW
  rw [← heq] at hpair
  exact ⟨cenIn W₁ (B : Set G), cenIn W₂ (B : Set G), B, hpair.1, hBA, hcyc, inf_le_right⟩

theorem le_thetaMG_of_mem_mhat
    (hθ : NearFunctor p A θ) (hcard : Nat.card A = p ^ 3)
    {Y : Subgroup G} (hY : Y ∈ dset p A θ) {Q : Subgroup G} (hQ : Q ∈ mhat p A θ)
    (hQD : Q ⊓ dsub A θ = Y) : Q ≤ thetaMG p A θ Y := by
  obtain ⟨Z₁, Z₂, B, hZ, hBA, hcyc, hZB⟩ := exists_pair_centralized hθ hY
  have hBcard : p ^ 2 ≤ Nat.card B := by
    have h1 := card_le_of_cyclicMod hθ.elemAbelian hθ.prime hBA hcyc
    rw [hcard] at h1
    have h2 : p ^ 3 = p ^ 2 * p := pow_succ p 2
    rw [h2] at h1
    exact Nat.le_of_mul_le_mul_right h1 hθ.prime.pos
  have hBel : IsElemAbelian p B := Thm32.isElemAbelian_of_le hθ.elemAbelian hBA
  have hgen := CFSG.SignalizerFunctorTheorem.McBride.iSup_centralizer_nonidentity hθ.prime hBel
    hBcard (hBA.trans hQ.1.1) hQ.1.2.1
  rw [← hgen]
  refine iSup₂_le fun b hb => iSup_le fun hb1 => ?_
  have hbA : b ∈ A := hBA hb
  have hθb : θ b ∈ mtil p A θ := apply_mem_mtil hθ hbA hb1
  have hZ1b : Z₁ ≤ θ b := by
    have := hZ.1.1.1.2.2.1 b hbA hb1
    exact fun z hz => this ⟨hz, Subgroup.mem_centralizer_singleton_iff.mpr
      (Subgroup.mem_centralizer_iff.mp (hZB hz) b hb |>.symm)⟩
  have hcb : θ b ∈ cset p A θ Y := ⟨hθb, (Z₁, Z₂), hZ, hZ1b⟩
  have hDc : dsub A θ ≤ Subgroup.centralizer {b} :=
    (dsub_le_centralizer hθ).trans (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hbA))
  have hAc : A ≤ Subgroup.centralizer {b} := fun g hg =>
    Subgroup.mem_centralizer_singleton_iff.mpr (commute_of_mem hθ.elemAbelian.1 hg hbA)
  have hadm : Admits (dsub A θ ⊔ A) (Q ⊓ Subgroup.centralizer {b}) :=
    Admits.inf (sup_le hQ.2 hQ.1.1)
      (admits_centralizer_singleton (sup_le hDc hAc))
  have hEb : Q ⊓ Subgroup.centralizer {b} ∈ esetX p A θ Y (θ b) := by
    refine ⟨⟨mem_mhat_of_le_mhat hθ.prime hQ inf_le_left hadm, ?_⟩, ?_⟩
    · rw [inf_assoc, inf_eq_right.mpr hDc]
      exact hQD
    · exact hQ.1.2.2.1 b hbA hb1
  calc Q ⊓ Subgroup.centralizer {b}
      ≤ thetaY p A θ Y (θ b) := le_iSup₂ (f := fun Z (_ : Z ∈ esetX p A θ Y (θ b)) => Z) _ hEb
    _ ≤ thetaM p A θ Y (θ b) := thetaY_le_thetaM hθ hY hcb
    _ ≤ thetaMG p A θ Y :=
        le_iSup₂ (f := fun X (_ : X ∈ cset p A θ Y) => thetaM p A θ Y X) (θ b) hcb

end Thm53A

end CFSG.SignalizerFunctorTheorem.McBride.Near
