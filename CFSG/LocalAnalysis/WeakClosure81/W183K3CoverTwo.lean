module

public import CFSG.LocalAnalysis.WeakClosure81.W183K3Leaves
public import CFSG.LocalAnalysis.WeakClosure81.W183K3Master2Aux
public import CFSG.LocalAnalysis.WeakClosure81.W183K3CoreSetting
import CFSG.LocalAnalysis.WeakClosure81.W183Br1OddAux1
public import CFSG.LocalAnalysis.WeakClosure81.W183B2Inner
public import CFSG.LocalAnalysis.WeakClosure81.W18T189FourBridge

public section

namespace CFSG.LocalAnalysis.WeakClosure81

namespace W183K3

open CFSG.SignalizerFunctorTheorem.Quadratic CFSG.Quasithin CFSG.Open Subgroup
open CFSG.Blueprint (LieModel)

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]

theorem br3_cover_core_sub (h65o : Asch6_5Odd) {R L : Subgroup (LGL 2 V)}
    (hZ : Odd (Nat.card (Subgroup.center ↥L))) (hLR : L ≤ R)
    (hnorm : ∀ y ∈ R, ∀ l ∈ L, y * l * y⁻¹ ∈ L) (hq : CFSG.Open.IsQuasisimple ↥L)
    (hshape : ∃ p : ℕ, p.Prime ∧ 5 ≤ p ∧ (LieModel (↥L ⧸ Subgroup.center ↥L) .PSL 3 p 1 ∨
      LieModel (↥L ⧸ Subgroup.center ↥L) .PSU 3 p 1))
    {A : Subgroup (LGL 2 V)} (hAR : A ≤ R) (hcard : Nat.card ↥A = 4) (hel : IsElemAbelian 2 A)
    (hquad : CFSG.Quasithin.G11.commSpace A
      (CFSG.SignalizerFunctorTheorem.Quadratic.commSub A) = ⊥)
    (hker : A ⊓ Subgroup.centralizer (L : Set (LGL 2 V)) = ⊥) : False := by
  classical
  haveI : Finite (LGL 2 V) := w183_finite_lgl
  haveI : Finite ↥R := Finite.of_injective (fun r : ↥R => (r : LGL 2 V)) Subtype.val_injective
  let Y₀ : Type := ↥L ⧸ Subgroup.center ↥L
  have hsub : IsSubnormal (L.subgroupOf R) ⊤ := by
    refine IsSubnormal.step le_top ?_ (IsSubnormal.refl ⊤)
    rw [Subgroup.normal_subgroupOf_iff le_top]
    intro a b ha _
    rw [Subgroup.mem_subgroupOf] at ha ⊢
    simpa using hnorm (b : LGL 2 V) b.2 (a : LGL 2 V) ha
  have hquasi' : CFSG.Open.IsQuasisimple ↥(L.subgroupOf R) :=
    CFSG.Open.IsQuasisimple.of_mulEquiv (Subgroup.subgroupOfEquivOfLe hLR) hq
  have hcomp : IsComponentOf (L.subgroupOf R) ⊤ := ⟨le_top, hsub, hquasi'⟩
  have hcov : CFSG.LocalAnalysis.UniquenessCase.UC22.CoverOf ↥(L.subgroupOf R) Y₀ := by
    refine ⟨hquasi', ?_⟩
    exact ⟨QuotientGroup.congr (Subgroup.center ↥(L.subgroupOf R)) (Subgroup.center ↥L)
      (Subgroup.subgroupOfEquivOfLe hLR)
      (Subgroup.map_center_eq (Subgroup.subgroupOfEquivOfLe hLR))⟩
  have hAcard : Nat.card ↥(A.subgroupOf R) = 4 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAR).toEquiv, hcard]
  have hel' : IsElemAbelian 2 (A.subgroupOf R) := hel.subgroupOf R
  have hquadOn : IsQuadraticOn (actOnMul R) (A.subgroupOf R) :=
    isQuadraticOn_actOnMul (R := R) hquad
  have hALc : A.subgroupOf R ⊓
      Subgroup.centralizer ((L.subgroupOf R : Subgroup ↥R) : Set ↥R) = ⊥ := by
    rw [eq_bot_iff]
    intro y hy
    obtain ⟨hyA, hyC⟩ := Subgroup.mem_inf.mp hy
    have hyA' : (y : LGL 2 V) ∈ A := Subgroup.mem_subgroupOf.mp hyA
    have hycent : (y : LGL 2 V) ∈ Subgroup.centralizer (L : Set (LGL 2 V)) := by
      rw [Subgroup.mem_centralizer_iff]
      intro l hl
      have hmem := (Subgroup.mem_centralizer_iff.mp hyC) (⟨l, hLR hl⟩ : ↥R)
        (Subgroup.mem_subgroupOf.mpr hl)
      exact congrArg Subtype.val hmem
    have hmem : (y : LGL 2 V) ∈ A ⊓ Subgroup.centralizer (L : Set (LGL 2 V)) :=
      ⟨hyA', hycent⟩
    rw [hker, Subgroup.mem_bot] at hmem
    exact Subtype.ext hmem
  have hL_normal : (L.subgroupOf R).Normal := by
    rw [Subgroup.normal_subgroupOf_iff hLR]
    intro h k hh hk
    exact hnorm k hk h hh
  have hAnorm : A.subgroupOf R ≤ Subgroup.normalizer (L.subgroupOf R : Set ↥R) := by
    rw [Subgroup.normalizer_eq_top_iff.mpr hL_normal]
    exact le_top
  have hodd_sub : Odd (Nat.card ↥(Subgroup.center ↥(L.subgroupOf R))) := by
    have hmap : (Subgroup.center ↥(L.subgroupOf R)).map
        (Subgroup.subgroupOfEquivOfLe hLR).toMonoidHom = Subgroup.center ↥L :=
      Subgroup.map_center_eq (Subgroup.subgroupOfEquivOfLe hLR)
    have h2 : Nat.card ↥(Subgroup.center ↥(L.subgroupOf R)) =
        Nat.card ↥(Subgroup.center ↥L) := by
      rw [← hmap, Subgroup.card_map_of_injective (Subgroup.subgroupOfEquivOfLe hLR).injective]
    rw [h2]
    exact hZ
  rcases hshape with ⟨p, hp, hp5, hmodel⟩
  have hp2 : p ≠ 2 := by omega
  have h3p : 3 < p ^ 1 := by
    rw [pow_one]
    omega
  have hY : (Odd 1 ∧ LieModel Y₀ .PSL 3 p 1) ∨ LieModel Y₀ .PSU 3 p 1 := by
    rcases hmodel with h | h
    · exact Or.inl ⟨odd_one, h⟩
    · exact Or.inr h
  exact h65o ↥R (Multiplicative V) (multiplicative_sq_eq_one (W := V)) (actOnMul R)
    (actOnMul_injective (R := R)) (L.subgroupOf R) (A.subgroupOf R) hcomp hodd_sub hAnorm
    hAcard hel' hquadOn hALc p 1 Y₀ (inferInstance : Group Y₀) hp hp2 h3p hY hcov

theorem w183k3_cover_shape_swap {Y T L₁ L₂ : Subgroup (LGL 2 V)} (htwo : Br3TwoComp Y T L₁ L₂)
    (h : ∃ p : ℕ, p.Prime ∧ 5 ≤ p ∧ (LieModel (↥L₁ ⧸ Subgroup.center ↥L₁) .PSL 3 p 1 ∨
      LieModel (↥L₁ ⧸ Subgroup.center ↥L₁) .PSU 3 p 1)) :
    ∃ p : ℕ, p.Prime ∧ 5 ≤ p ∧ (LieModel (↥L₂ ⧸ Subgroup.center ↥L₂) .PSL 3 p 1 ∨
      LieModel (↥L₂ ⧸ Subgroup.center ↥L₂) .PSU 3 p 1) := by
  obtain ⟨p, hp, hp5, hmodel⟩ := h
  let e := htwo.swapEquiv
  let eq : ↥L₁ ⧸ Subgroup.center ↥L₁ ≃* ↥L₂ ⧸ Subgroup.center ↥L₂ :=
    QuotientGroup.congr (Subgroup.center ↥L₁) (Subgroup.center ↥L₂) e
      (Subgroup.map_center_eq e)
  exact ⟨p, hp, hp5,
    hmodel.elim (fun hm => Or.inl (CFSG.Blueprint.LieModel.of_mulEquiv eq hm))
      (fun hm => Or.inr (CFSG.Blueprint.LieModel.of_mulEquiv eq hm))⟩

theorem br3CoverTwo_holds : Br3CoverTwo := by
  intro rows V _ _ _ Y T L₁ L₂ Γ VA 𝒢 Zs m i₀ δ hc htwo hshape hne hall
  classical
  haveI : Finite (LGL 2 V) := w183_finite_lgl
  obtain ⟨A, hA⟩ := hne
  have h4 : 4 ≤ Nat.card ↥A := w183k3m2_four_le_card_of_two_le_mRank (hall A hA)
  have hAY : A ≤ Y := hc.h131.le_G A hA
  have hel : IsElemAbelian 2 A := hc.h131.isElemAb A hA
  have hqA : CFSG.Quasithin.G11.commSpace A
      (CFSG.SignalizerFunctorTheorem.Quadratic.commSub A) = ⊥ :=
    hc.h131.quadratic A hA
  have hAN := w183k3m2_mem_normalizer hc htwo hall hA
  have hAn₁ : ∀ a ∈ A, ∀ l ∈ L₁, a * l * a⁻¹ ∈ L₁ := fun a ha l hl =>
    (Subgroup.mem_normalizer_iff.mp (hAN.1 ha) l).mp hl
  have hAn₂ : ∀ a ∈ A, ∀ l ∈ L₂, a * l * a⁻¹ ∈ L₂ := fun a ha l hl =>
    (Subgroup.mem_normalizer_iff.mp (hAN.2 ha) l).mp hl
  let D : Subgroup (LGL 2 V) := A ⊓ Subgroup.centralizer (L₁ : Set (LGL 2 V))
  let F : Subgroup (LGL 2 V) := A ⊓ Subgroup.centralizer (L₂ : Set (LGL 2 V))
  have hDA : D ≤ A := inf_le_left
  have hFA : F ≤ A := inf_le_left
  have hDF : D ⊓ F = ⊥ := by
    rw [eq_bot_iff]
    intro y hy
    rw [Subgroup.mem_bot]
    obtain ⟨hyD, hyF⟩ := Subgroup.mem_inf.mp hy
    obtain ⟨hyA, hyC₁⟩ := Subgroup.mem_inf.mp hyD
    obtain ⟨-, hyC₂⟩ := Subgroup.mem_inf.mp hyF
    exact htwo.eq_one_of_isPGroup_cent (hAY hyA) (k := 1)
      (by simpa using hel.2 y hyA)
      (fun l hl => (Subgroup.mem_centralizer_iff.mp hyC₁ l hl).symm)
      (fun l hl => (Subgroup.mem_centralizer_iff.mp hyC₂ l hl).symm)
  by_cases hD2 : 2 ≤ mOf A D
  ·
    obtain ⟨B, hBA, hBcard, hBD⟩ := w183odd_exists_card_four_inf_eq_bot hel hDA hD2
    have hBel : IsElemAbelian 2 B := hel.mono hBA
    have hBq : CFSG.Quasithin.G11.commSpace B
        (CFSG.SignalizerFunctorTheorem.Quadratic.commSub B) = ⊥ :=
      le_bot_iff.mp ((CFSG.Quasithin.G11.commSpace_mono hBA
        (CFSG.SignalizerFunctorTheorem.Quadratic.commSub_mono B A hBA)).trans (le_of_eq hqA))
    have hnorm : ∀ y ∈ B ⊔ L₁, ∀ l ∈ L₁, y * l * y⁻¹ ∈ L₁ := by
      intro y hy l hl
      have hBN : B ≤ Subgroup.normalizer (L₁ : Set (LGL 2 V)) := hBA.trans hAN.1
      exact (Subgroup.mem_normalizer_iff.mp ((sup_le hBN Subgroup.le_normalizer) hy) l).mp hl
    have hBker : B ⊓ Subgroup.centralizer (L₁ : Set (LGL 2 V)) = ⊥ := by
      rw [eq_bot_iff]
      intro y hy
      have hle : B ⊓ Subgroup.centralizer (L₁ : Set (LGL 2 V)) ≤ D :=
        le_inf (inf_le_left.trans hBA) inf_le_right
      have hle2 : B ⊓ Subgroup.centralizer (L₁ : Set (LGL 2 V)) ≤ B ⊓ D :=
        le_inf inf_le_left hle
      exact (hle2.trans (le_of_eq hBD)) hy
    exact br3_cover_core_sub (R := B ⊔ L₁) (L := L₁) (A := B) rows.h65o htwo.odd₁
      le_sup_right hnorm htwo.quasi₁ hshape le_sup_left hBcard hBel hBq hBker
  · have hD1 : mOf A D ≤ 1 := not_lt.1 hD2
    by_cases hF2 : 2 ≤ mOf A F
    ·
      obtain ⟨B, hBA, hBcard, hBF⟩ := w183odd_exists_card_four_inf_eq_bot hel hFA hF2
      have hBel : IsElemAbelian 2 B := hel.mono hBA
      have hBshape := w183k3_cover_shape_swap htwo hshape
      have hBq : CFSG.Quasithin.G11.commSpace B
          (CFSG.SignalizerFunctorTheorem.Quadratic.commSub B) = ⊥ :=
        le_bot_iff.mp ((CFSG.Quasithin.G11.commSpace_mono hBA
          (CFSG.SignalizerFunctorTheorem.Quadratic.commSub_mono B A hBA)).trans
            (le_of_eq hqA))
      have hnorm : ∀ y ∈ B ⊔ L₂, ∀ l ∈ L₂, y * l * y⁻¹ ∈ L₂ := by
        intro y hy l hl
        have hBN : B ≤ Subgroup.normalizer (L₂ : Set (LGL 2 V)) := hBA.trans hAN.2
        exact (Subgroup.mem_normalizer_iff.mp ((sup_le hBN Subgroup.le_normalizer) hy) l).mp hl
      have hBker : B ⊓ Subgroup.centralizer (L₂ : Set (LGL 2 V)) = ⊥ := by
        rw [eq_bot_iff]
        intro y hy
        have hle : B ⊓ Subgroup.centralizer (L₂ : Set (LGL 2 V)) ≤ F :=
          le_inf (inf_le_left.trans hBA) inf_le_right
        have hle2 : B ⊓ Subgroup.centralizer (L₂ : Set (LGL 2 V)) ≤ B ⊓ F :=
          le_inf inf_le_left hle
        exact (hle2.trans (le_of_eq hBF)) hy
      exact br3_cover_core_sub (R := B ⊔ L₂) (L := L₂) (A := B) rows.h65o htwo.odd₂
        le_sup_right hnorm htwo.quasi₂ hBshape le_sup_left hBcard hBel hBq hBker
    ·
      have hF1 : mOf A F ≤ 1 := not_lt.1 hF2
      have hDF' : F ⊓ D = ⊥ := by rw [inf_comm]; exact hDF
      have hDle2 : Nat.card ↥D ≤ 2 :=
        w183odd_card_le_two_of_mOf_le_one (D := D) (F := F) hel hDA hFA hDF hF1
      have hFle2 : Nat.card ↥F ≤ 2 :=
        w183odd_card_le_two_of_mOf_le_one (D := F) (F := D) hel hFA hDA hDF' hD1
      have hAeqD : Nat.card ↥A = 2 ^ mOf A D * Nat.card ↥D := by
        rw [← Subgroup.index_mul_card (D.subgroupOf A),
          w183odd_index_eq_pow_mOf hel hDA,
          Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDA).toEquiv]
      have hAeqF : Nat.card ↥A = 2 ^ mOf A F * Nat.card ↥F := by
        rw [← Subgroup.index_mul_card (F.subgroupOf A),
          w183odd_index_eq_pow_mOf hel hFA,
          Nat.card_congr (Subgroup.subgroupOfEquivOfLe hFA).toEquiv]
      have hpowD : 2 ^ mOf A D ≤ 2 := by
        calc 2 ^ mOf A D ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) hD1
          _ = 2 := by norm_num
      have hpowF : 2 ^ mOf A F ≤ 2 := by
        calc 2 ^ mOf A F ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) hF1
          _ = 2 := by norm_num
      have hA4 : Nat.card ↥A = 4 := by
        have hAle : Nat.card ↥A ≤ 4 := by
          calc Nat.card ↥A = 2 ^ mOf A D * Nat.card ↥D := hAeqD
            _ ≤ 2 * 2 := Nat.mul_le_mul hpowD hDle2
            _ = 4 := by norm_num
        omega
      have hDge2 : 2 ≤ Nat.card ↥D := by
        have hle : Nat.card ↥A ≤ 2 * Nat.card ↥D := by
          calc Nat.card ↥A = 2 ^ mOf A D * Nat.card ↥D := hAeqD
            _ ≤ 2 * Nat.card ↥D := Nat.mul_le_mul_right _ hpowD
        rw [hA4] at hle
        omega
      have hFge2 : 2 ≤ Nat.card ↥F := by
        have hle : Nat.card ↥A ≤ 2 * Nat.card ↥F := by
          calc Nat.card ↥A = 2 ^ mOf A F * Nat.card ↥F := hAeqF
            _ ≤ 2 * Nat.card ↥F := Nat.mul_le_mul_right _ hpowF
        rw [hA4] at hle
        omega
      have hD0 : D ≠ ⊥ := by
        intro hbot
        rw [hbot, Subgroup.card_bot] at hDge2
        omega
      have hF0 : F ≠ ⊥ := by
        intro hbot
        rw [hbot, Subgroup.card_bot] at hFge2
        omega
      have hrank : mOf A D ≤ m - i₀ - 1 := by
        have := hc.hmi
        omega
      exact hc.h131.false_of_two_kernels_quasi hA htwo.le₁ htwo.le₂ htwo.quasi₁ htwo.quasi₂
        htwo.odd₁ htwo.odd₂ htwo.comm hAn₁ hAn₂ rfl rfl hD0 hF0 hDF hrank

end W183K3

end CFSG.LocalAnalysis.WeakClosure81

end
