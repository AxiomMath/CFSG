module

public import CFSG.RankThree.PartOne.TCX.Tri.LayerField
public import CFSG.RankThree.PartOne.TCX.A1Layer
public import CFSG.RankThree.PartOne.TCX.Tri.E2Frame
public import CFSG.RankThree.PartOne.TCX.Tri.Setup
public import CFSG.RankThree.PartOne.TCX.Tri.Skeleton

public section

namespace CFSG.RankThree.PartOne.TCX.Tri

open Subgroup Matrix CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.RankThree.Chevalley CFSG.RankThree.Chevalley.TrialityFold CFSG.RankThree.PartOne
  CFSG.RankThree.PartOne.KE CFSG.RankThree.PartOne.KGD CFSG.RankThree.PartOne.KLCE
open CFSG.RankThree.PartOne.TCX.F4 (LayerClaimsF4)

open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.LocalAnalysis.ComponentInitial (sl2_closure_upper_lower)

open CFSG.RankThree.PartOne.TCX
open scoped MatrixGroups

section Root

variable {L : Type} [Field L] [CharP L 2]

theorem triP_conj_pinnedX {α : Fin TwistTag.D4.tag.rank → ℤ} (hα : IsRoot TwistTag.D4.tag α)
    (c : L) :
    triP L * pinnedX TwistTag.D4.tag L α c * (triP L)⁻¹ =
      pinnedX TwistTag.D4.tag L (permLattice TwistTag.D4.perm α) c := by
  have h2 : (2 : L) = 0 := by exact_mod_cast CharP.cast_eq_zero L 2
  have h := twistHom_id_pinnedX (t := TwistTag.D4) h2 hα c
  rw [twistHom_apply] at h
  have h1 : Units.map (entrywiseHom (RingHom.id L)) (pinnedX TwistTag.D4.tag L α c) =
      pinnedX TwistTag.D4.tag L α c := Units.ext (entrywise_id _)
  rw [h1] at h
  exact h

theorem triP_conj_rootSL2 {θ : Fin TwistTag.D4.tag.rank → ℤ} (hθ : IsRoot TwistTag.D4.tag θ)
    (hρ : permLattice TwistTag.D4.perm θ = θ) (B : SL(2, L)) :
    triP L * rootSL2 TwistTag.D4.tag L θ B * (triP L)⁻¹ = rootSL2 TwistTag.D4.tag L θ B := by
  have hρ' : permLattice TwistTag.D4.perm (-θ) = -θ := by
    rw [show permLattice TwistTag.D4.perm (-θ) = -permLattice TwistTag.D4.perm θ from by
      funext i
      simp [permLattice], hρ]
  let f : SL(2, L) →* ModGL TwistTag.D4.tag L :=
    (MulAut.conj (triP L)).toMonoidHom.comp (rootSL2 TwistTag.D4.tag L θ)
  have hfg : f = rootSL2 TwistTag.D4.tag L θ := by
    refine MonoidHom.eq_of_eqOn_dense (sl2_closure_upper_lower (K := L)) ?_
    rintro _ (⟨c, rfl⟩ | ⟨c, rfl⟩)
    · change triP L * rootSL2 TwistTag.D4.tag L θ (uSL c) * (triP L)⁻¹ =
        rootSL2 TwistTag.D4.tag L θ (uSL c)
      rw [rootSL2_uSL_of_charTwo hθ, triP_conj_pinnedX hθ, hρ]
    · change triP L * rootSL2 TwistTag.D4.tag L θ (vSL c) * (triP L)⁻¹ =
        rootSL2 TwistTag.D4.tag L θ (vSL c)
      rw [rootSL2_vSL_of_charTwo hθ, triP_conj_pinnedX (IsRoot.neg hθ), hρ']
  exact DFunLike.congr_fun hfg B

theorem triF0_rootSL2 {θ : Fin TwistTag.D4.tag.rank → ℤ} (hθ : IsRoot TwistTag.D4.tag θ)
    (hρ : permLattice TwistTag.D4.perm θ = θ) (f₀ : ℕ) (B : SL(2, L)) :
    triF0 L f₀ (rootSL2 TwistTag.D4.tag L θ B) =
      Units.map (entrywiseHom (iterateFrobenius L 2 f₀)) (rootSL2 TwistTag.D4.tag L θ B) := by
  rw [triF0_apply, entrywise_rootSL2_of_field, triP_conj_rootSL2 hθ hρ]

end Root

section Layer

variable {C : Type} [Group C] [Finite C] {L : Type} [Field L] [CharP L 2] [IsAlgClosed L]
  {p f₀ : ℕ} {ι : C →* ModGL TwistTag.D4.tag L} {α₀ : MulAut C}

theorem tri_a1_layer (h : IsShintani p ι (triF0 L f₀) (triPhi L p f₀) α₀) (hp : p.Prime)
    (hp5 : 5 ≤ p) (hf₀ : 1 ≤ f₀)
    (hodd : ∀ t ∈ torusGroup TwistTag.D4.tag L, ∃ m : ℕ, Odd m ∧ t ^ m = 1)
    {g₀ : ModGL TwistTag.D4.tag L} (hg₀C : g₀ ∈ adjointGroup TwistTag.D4.tag L)
    (hg₀ : triF0 L f₀ g₀ = g₀ * triNeg L)
    {θ : Fin TwistTag.D4.tag.rank → ℤ} (hθ : IsRoot TwistTag.D4.tag θ)
    (hρθ : permLattice TwistTag.D4.perm θ = θ)
    {x : C} (hx : orderOf x = p) {c : C} (hcα : α₀ c = c)
    {b : Fin TwistTag.D4.tag.rank → Lˣ}
    (hb : rootDiagUnit TwistTag.D4.tag b = g₀⁻¹ * ι (c * x * c⁻¹) * g₀)
    (hbT : rootDiagUnit TwistTag.D4.tag b ∈ twistedTorusOf (triNeg L) (triF0 L f₀))
    (hbS : rootCharKernel b ⊆ ({θ, -θ} : Set (Fin TwistTag.D4.tag.rank → ℤ)))
    (hbc : rootDiagUnit TwistTag.D4.tag b ∈ Subgroup.centralizer
      (rootSpan TwistTag.D4.tag L ({θ, -θ} : Set (Fin TwistTag.D4.tag.rank → ℤ)) :
        Set (ModGL TwistTag.D4.tag L))) :
    SingleLayerData p α₀ (Subgroup.centralizer ({x} : Set C)) := by
  classical
  have hp3 : 3 < p := by omega
  have hpo : Odd p := hp.odd_of_ne_two (by omega)
  have : Fact p.Prime := ⟨hp⟩
  set Φ₀ : L →+* L := iterateFrobenius L 2 f₀ with hΦ₀def
  set Fr : L →+* L := iterateFrobenius L 2 (f₀ * p) with hFrdef
  have hΦ₀c : ∀ c, Φ₀ c = c ^ 2 ^ f₀ := fun c => iterateFrobenius_def 2 f₀ c
  obtain ⟨k₀, _, _, _, hk₀⟩ := exists_finite_field_into 2 f₀ hf₀ L
  obtain ⟨kQ, _, _, _, σQ, hkQ, hσQord, hσQ⟩ := exists_layer_field (L := L) hp hf₀ 1 le_rfl
  simp only [one_mul] at hkQ hσQ
  have : CharP kQ 2 := ⟨fun x => by
    rw [← (algebraMap kQ L).injective.eq_iff, map_natCast, map_zero]
    exact CharP.cast_eq_zero_iff L 2 x⟩
  have hσQ1 : σQ ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hσQord
    exact hp.one_lt.ne hσQord
  have hFrc : ∀ c, Fr c = c ^ Nat.card kQ := fun c => by
    rw [hkQ, mul_comm p f₀]
    exact iterateFrobenius_def 2 (f₀ * p) c
  have hK4 : 4 ≤ Nat.card kQ := by
    rw [hkQ]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (p * f₀) := Nat.pow_le_pow_right (by norm_num)
        (by nlinarith [Nat.mul_pos (by omega : 0 < p) hf₀])
  set n₀ : ModGL TwistTag.D4.tag L := triNeg L with hn₀def
  have hn₀F : triF0 L f₀ n₀ = n₀ := triNeg_twistHom Φ₀
  have hn₀J : ∀ B : SL(2, L), n₀ * rootSL2 TwistTag.D4.tag L θ B * n₀⁻¹ =
      rootSL2 TwistTag.D4.tag L θ (WSL * B * WSL⁻¹) :=
    conj_rootSL2_of_neg_rep (fun α hα c => triNeg_conj_pinnedX hα c) hθ
  have hJpow : ∀ J : SL(2, L), J * J = 1 → J ^ p = J := fun J hJ => by
    obtain ⟨m, hm⟩ := hpo
    rw [hm, pow_succ, pow_mul, pow_two, hJ, one_pow, one_mul]
  have hNJ : ∀ B : SL(2, L), n₀ ^ p * rootSL2 TwistTag.D4.tag L θ B * (n₀ ^ p)⁻¹ =
      rootSL2 TwistTag.D4.tag L θ (WSL * B * WSL⁻¹) := fun B => by
    rw [pow_conj_rootSL2 hn₀J p B, hJpow WSL wsl_mul_self]
  have hPp : ∀ B : SL(2, L), triP L ^ p * rootSL2 TwistTag.D4.tag L θ B * (triP L ^ p)⁻¹ =
      rootSL2 TwistTag.D4.tag L θ B := fun B => by
    have := pow_conj_rootSL2 (n := triP L) (J₀ := 1)
      (fun B => by rw [triP_conj_rootSL2 hθ hρθ, one_mul, inv_one, mul_one]) p B
    simpa using this
  set M : ModGL TwistTag.D4.tag L := n₀ ^ p * triP L ^ p with hMdef
  have hMJ : ∀ B : SL(2, L), M * rootSL2 TwistTag.D4.tag L θ B * M⁻¹ =
      rootSL2 TwistTag.D4.tag L θ (WSL * B * WSL⁻¹) := fun B => by
    calc M * rootSL2 TwistTag.D4.tag L θ B * M⁻¹
        = n₀ ^ p * (triP L ^ p * rootSL2 TwistTag.D4.tag L θ B * (triP L ^ p)⁻¹) * (n₀ ^ p)⁻¹ := by
          rw [hMdef]
          group
      _ = _ := by rw [hPp, hNJ]
  obtain ⟨P₀, hP₀⟩ := exists_P0_wsl (K := k₀) Φ₀ (fun c => by rw [hk₀]; exact hΦ₀c c)
  have hJGL : Matrix.GeneralLinearGroup.map Φ₀ (Matrix.SpecialLinearGroup.toGL
      (WSL : SL(2, L))) = Matrix.SpecialLinearGroup.toGL (WSL : SL(2, L)) := by
    have h2 : Matrix.GeneralLinearGroup.map Φ₀ (Matrix.SpecialLinearGroup.toGL
        (WSL : SL(2, L))) = Matrix.SpecialLinearGroup.toGL
          (Matrix.SpecialLinearGroup.map Φ₀ (WSL : SL(2, L))) := by
      ext i j
      rfl
    rw [h2, map_wsl]
  have hPK : P₀ * Matrix.GeneralLinearGroup.map Fr P₀⁻¹ =
      Matrix.SpecialLinearGroup.toGL (WSL : SL(2, L)) := by
    have h1 := P_frobenius_pow hJGL hP₀ p
    rw [hFrdef, h1]
    have hsq : Matrix.SpecialLinearGroup.toGL (WSL : SL(2, L)) *
        Matrix.SpecialLinearGroup.toGL (WSL : SL(2, L)) = 1 := by
      rw [← map_mul, wsl_mul_self, map_one]
    obtain ⟨m, hm⟩ := hpo
    rw [hm, pow_succ, pow_mul, pow_two, hsq, one_pow, one_mul]
  have hX := a1_hX_of_J hMJ Fr hPK
  obtain ⟨P, hfam, hP'⟩ := a1_sigma_family_of_action (K := kQ) hK4 hθ Fr hFrc P₀ hX
  have hNeq : nseq n₀ (triF0 L f₀) p = n₀ ^ p := nseq_eq_pow hn₀F p
  have hfam' : IsSigmaFamilyΦ (nseq n₀ (triF0 L f₀) p) (triPhi L p f₀) {θ, -θ} P := by
    rw [hNeq]
    exact isSigmaFamilyΦ_twPhi (n₀ ^ p) (triP L ^ p) Fr {θ, -θ} P hfam
  have hjoin : rootSpan TwistTag.D4.tag L ({θ, -θ} : Set (Fin TwistTag.D4.tag.rank → ℤ)) ⊓
      twistedFixedPoints (nseq n₀ (triF0 L f₀) p) (triPhi L p f₀) ≤ P () := by
    rw [hNeq]
    change rootSpan TwistTag.D4.tag L ({θ, -θ} : Set (Fin TwistTag.D4.tag.rank → ℤ)) ⊓
      twistedFixedPoints (n₀ ^ p) (twPhi (triP L ^ p) Fr) ≤ P ()
    rw [twistedFixedPoints_twPhi, hP', a1_fixed_range_of_action hθ Fr hFrc P₀ hX]
  have hσQ' : ∀ c : kQ, Φ₀ (algebraMap kQ L c) = algebraMap kQ L (σQ c) := hσQ
  obtain ⟨D, hD, ρ', τ', hρ'inj, hρ'range, hρ'compat, hclaims⟩ :=
    a1_layer_of_frame (K := kQ) hp5 hf₀ hkQ hσQ1 hn₀J hσQ' hP₀
  have hrr : ρ'.range = P () := by rw [hρ'range, hP']
  have hcompat : ∀ d, n₀ * triF0 L f₀ (ρ' d) * n₀⁻¹ = ρ' (τ' d) := fun d => by
    have hmem : ρ' d ∈ (a1HomConj TwistTag.D4.tag kQ L θ P₀).range := hρ'range ▸ ⟨d, rfl⟩
    obtain ⟨X, hXd⟩ := hmem
    have h1 := hρ'compat d
    rw [← hXd, a1HomConj_apply] at h1
    rw [← hXd, a1HomConj_apply, triF0_rootSL2 hθ hρθ f₀]
    exact h1
  have hS : ∀ α ∈ ({θ, -θ} : Set (Fin TwistTag.D4.tag.rank → ℤ)), IsRoot TwistTag.D4.tag α := by
    intro α hα
    rcases hα with rfl | rfl
    exacts [hθ, IsRoot.neg hθ]
  have hSn : ∀ α ∈ ({θ, -θ} : Set (Fin TwistTag.D4.tag.rank → ℤ)), -α ∈ ({θ, -θ} :
      Set (Fin TwistTag.D4.tag.rank → ℤ)) := by
    intro α hα
    rcases hα with rfl | rfl
    · exact Or.inr rfl
    · rw [neg_neg]
      exact Or.inl rfl
  exact tri_layer_of_frame h hp hp3 hodd hg₀C hg₀ hS hSn P hfam' hjoin hx hcα hb hbT hbS hbc
    ⟨D, hD, ρ', τ', hρ'inj, hrr, hcompat, hclaims⟩

end Layer

end CFSG.RankThree.PartOne.TCX.Tri
