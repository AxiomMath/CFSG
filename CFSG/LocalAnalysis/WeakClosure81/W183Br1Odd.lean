module

public import CFSG.LocalAnalysis.WeakClosure81.W183Abs2
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps6Props
public import CFSG.LocalAnalysis.WeakClosure81.W183L39Main
import CFSG.LocalAnalysis.WeakClosure81.W183Br1OddAux1
import CFSG.LocalAnalysis.WeakClosure81.W18T189FourBridge
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.Quasithin.EmptyFaithful.S1422Basic

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.SignalizerFunctorTheorem.Quadratic CFSG.Quasithin.G11 CFSG.Quasithin CFSG.Open
  CFSG.QuasithinUnique Subgroup
open CFSG.LocalAnalysis.UniquenessCase.UC22 (IsL2 IsL3 IsU3 IsSp4 IsAlt Bar2 CoverOf)
open CFSG.Blueprint (LieModel)

@[expose] def OddShape (X : Type) [Group X] : Prop :=
  (∃ p e : ℕ, p.Prime ∧ p ≠ 2 ∧ 9 < p ^ e ∧ CFSG.Quasithin.F6.IsL2 p e X) ∨
    (∃ p : ℕ, p.Prime ∧ 5 ≤ p ∧
      ((p % 4 = 3 ∧ LieModel X .PSL 3 p 1) ∨ (p % 4 = 1 ∧ LieModel X .PSU 3 p 1)))

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
  {Y T L L₁ L₂ A : Subgroup (LGL 2 V)} {Γ : Set (Subgroup (LGL 2 V))}
  {VA : Subgroup (LGL 2 V) → Submodule (ZMod 2) V} {i : ℕ}

private theorem w183odd_oddShape_of_mulEquiv {X Z : Type} [Group X] [Group Z] (e : X ≃* Z)
    (h : OddShape X) : OddShape Z := by
  rcases h with ⟨p, f, hp, hp2, h9, hL2⟩ | ⟨p, hp, hp5, hL3 | hU3⟩
  · exact Or.inl ⟨p, f, hp, hp2, h9,
      CFSG.Open.StatedAPI.statedClassicalModel_of_mulEquiv e hL2⟩
  · exact Or.inr ⟨p, hp, hp5,
      Or.inl ⟨hL3.1, CFSG.Blueprint.LieModel.of_mulEquiv e hL3.2⟩⟩
  · exact Or.inr ⟨p, hp, hp5,
      Or.inr ⟨hU3.1, CFSG.Blueprint.LieModel.of_mulEquiv e hU3.2⟩⟩

private noncomputable def w183odd_swapEquiv {Y T L₁ L₂ : Subgroup (LGL 2 V)}
    (hL : Br2TwoComp Y T L₁ L₂) : ↥L₁ ≃* ↥L₂ :=
  (Subgroup.equivMapOfInjective L₁ (MulAut.conj (Classical.choose hL.swap)).toMonoidHom
      (MulAut.conj (Classical.choose hL.swap)).injective).trans
    (MulEquiv.subgroupCongr
      (show L₁.map (MulAut.conj (Classical.choose hL.swap)).toMonoidHom = L₂ from
        (Classical.choose_spec hL.swap).2))

theorem br1_odd_core (h64o : Asch6_4Odd) (h65o : Asch6_5Odd) (hsimple : IsSimpleGroup ↥L)
    (hnab : ∃ a ∈ L, ∃ b ∈ L, a * b ≠ b * a)
    (hn : ∀ a ∈ A, ∀ l ∈ L, a * l * a⁻¹ ∈ L) (hcard : Nat.card ↥A = 4)
    (hel : IsElemAbelian 2 A) (hq : commSpace A (commSub A) = ⊥)
    (hker : A ⊓ Subgroup.centralizer (L : Set (LGL 2 V)) = ⊥) (hshape : OddShape ↥L) : False := by
  classical
  haveI : Finite (LGL 2 V) := w183_finite_lgl
  let Y' : Subgroup (LGL 2 V) := A ⊔ L
  have hLY' : L ≤ Y' := le_sup_right
  have hAY' : A ≤ Y' := le_sup_left
  have hAn : A ≤ Subgroup.normalizer (L : Set (LGL 2 V)) := by
    intro a ha
    rw [Subgroup.mem_normalizer_iff]
    intro l
    constructor
    · intro hl
      exact hn a ha l hl
    · intro hl
      have hmem : a⁻¹ * (a * l * a⁻¹) * (a⁻¹)⁻¹ ∈ L :=
        hn a⁻¹ (A.inv_mem ha) (a * l * a⁻¹) hl
      have heq : a⁻¹ * (a * l * a⁻¹) * (a⁻¹)⁻¹ = l := by group
      rwa [heq] at hmem
  have hY'N : Y' ≤ Subgroup.normalizer (L : Set (LGL 2 V)) :=
    sup_le hAn Subgroup.le_normalizer
  have hLn' : ∀ y ∈ Y', ∀ l ∈ L, y * l * y⁻¹ ∈ L := by
    intro y hy l hl
    exact (Subgroup.mem_normalizer_iff.mp (hY'N hy) l).mp hl
  have hN : (L.subgroupOf Y').Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    exact hLn' g.1 g.2 n.1 hn
  have hAnorm : A.subgroupOf Y' ≤ Subgroup.normalizer (L.subgroupOf Y' : Set ↥Y') := by
    rw [Subgroup.normalizer_eq_top_iff.mpr hN]
    exact le_top
  have hnabL : ∃ a b : ↥L, a * b ≠ b * a := by
    obtain ⟨a, ha, b, hb, hab⟩ := hnab
    exact ⟨⟨a, ha⟩, ⟨b, hb⟩, fun h => hab (by simpa using congrArg Subtype.val h)⟩
  have hcomp := w183odd_component_cover_of_simple hLY' hN hsimple hnabL
  have hcard' : Nat.card ↥(A.subgroupOf Y') = 4 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAY').toEquiv, hcard]
  have hel' : IsElemAbelian 2 (A.subgroupOf Y') := hel.subgroupOf Y'
  have hquad : IsQuadraticOn (repOf Y') (A.subgroupOf Y') :=
    isQuadraticOn_lglRep (Y := Y') hq
  have hALc : A.subgroupOf Y' ⊓
      Subgroup.centralizer ((L.subgroupOf Y' : Subgroup ↥Y') : Set ↥Y') = ⊥ := by
    rw [eq_bot_iff]
    intro y hy
    obtain ⟨hyA, hyC⟩ := Subgroup.mem_inf.mp hy
    have hyA' : (y : LGL 2 V) ∈ A := Subgroup.mem_subgroupOf.mp hyA
    have hyC' : (y : LGL 2 V) ∈ Subgroup.centralizer (L : Set (LGL 2 V)) := by
      rw [Subgroup.mem_centralizer_iff]
      intro l hl
      have hmem := (Subgroup.mem_centralizer_iff.mp hyC)
        (⟨l, hLY' hl⟩ : ↥Y') (Subgroup.mem_subgroupOf.mpr hl)
      exact congrArg Subtype.val hmem
    have hmem : (y : LGL 2 V) ∈ A ⊓ Subgroup.centralizer (L : Set (LGL 2 V)) :=
      ⟨hyA', hyC'⟩
    rw [hker, Subgroup.mem_bot] at hmem
    exact Subtype.ext hmem
  have hsimple' : IsSimpleGroup ↥(L.subgroupOf Y') :=
    (Subgroup.subgroupOfEquivOfLe hLY').isSimpleGroup
  have hnab' : ∃ a b : ↥(L.subgroupOf Y'), a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hnabL
    refine ⟨(Subgroup.subgroupOfEquivOfLe hLY').symm a,
      (Subgroup.subgroupOfEquivOfLe hLY').symm b, ?_⟩
    intro h
    exact hab (by simpa using congrArg (Subgroup.subgroupOfEquivOfLe hLY') h)
  rcases hshape with ⟨p, e, hp, hp2, h9, hL2⟩ | ⟨p, hp, hp5, hL3 | hU3⟩
  ·
    have hL2' : CFSG.Quasithin.F6.IsL2 p e ↥(L.subgroupOf Y') :=
      CFSG.Open.StatedAPI.statedClassicalModel_of_mulEquiv
        (Subgroup.subgroupOfEquivOfLe hLY').symm hL2
    exact h64o ↥Y' (Multiplicative V) (multiplicative_sq_eq_one (W := V)) (repOf Y')
      (repOf_injective Y') (L.subgroupOf Y') (A.subgroupOf Y') hcomp.1 hAnorm hcard' hel'
      hquad hALc p e hp hp2 (by omega) hL2'
  ·
    have hp2 : p ≠ 2 := by
      rintro rfl
      exact absurd hL3.1 (by decide)
    have h3p : 3 < p ^ 1 := by
      rw [pow_one]
      omega
    have hodd : Odd (Nat.card ↥(Subgroup.center ↥(L.subgroupOf Y'))) := by
      have hcenter : Subgroup.center ↥(L.subgroupOf Y') = ⊥ :=
        w183_center_eq_bot_of_simple hsimple' hnab'
      rw [hcenter, Subgroup.card_bot]
      norm_num
    exact h65o ↥Y' (Multiplicative V) (multiplicative_sq_eq_one (W := V)) (repOf Y')
      (repOf_injective Y') (L.subgroupOf Y') (A.subgroupOf Y') hcomp.1 hodd hAnorm hcard'
      hel' hquad hALc p 1 ↥L (inferInstance : Group ↥L) hp hp2 h3p
      (Or.inl ⟨odd_one, hL3.2⟩) hcomp.2
  ·
    have hp2 : p ≠ 2 := by
      rintro rfl
      exact absurd hU3.1 (by decide)
    have h3p : 3 < p ^ 1 := by
      rw [pow_one]
      omega
    have hodd : Odd (Nat.card ↥(Subgroup.center ↥(L.subgroupOf Y'))) := by
      have hcenter : Subgroup.center ↥(L.subgroupOf Y') = ⊥ :=
        w183_center_eq_bot_of_simple hsimple' hnab'
      rw [hcenter, Subgroup.card_bot]
      norm_num
    exact h65o ↥Y' (Multiplicative V) (multiplicative_sq_eq_one (W := V)) (repOf Y')
      (repOf_injective Y') (L.subgroupOf Y') (A.subgroupOf Y') hcomp.1 hodd hAnorm hcard'
      hel' hquad hALc p 1 ↥L (inferInstance : Group ↥L) hp hp2 h3p (Or.inr hU3.2) hcomp.2

theorem br1_odd_false_one (h64o : Asch6_4Odd) (h65o : Asch6_5Odd) (h : Assumption131 Y Γ VA i)
    (hLY : L ≤ Y) (hLn : ∀ y ∈ Y, ∀ l ∈ L, y * l * y⁻¹ ∈ L)
    (hcent : ∀ y ∈ Y, (∀ l ∈ L, y * l = l * y) → y = 1) (hsimple : IsSimpleGroup ↥L)
    (hnab : ∃ a ∈ L, ∃ b ∈ L, a * b ≠ b * a) (hshape : OddShape ↥L) (hA : A ∈ Γ)
    (h4 : 4 ≤ Nat.card ↥A) : False := by
  classical
  haveI : Finite (LGL 2 V) := w183_finite_lgl
  have hAY : A ≤ Y := h.le_G A hA
  have hel : IsElemAbelian 2 A := h.isElemAb A hA
  have hq : commSpace A (commSub A) = ⊥ := h.quadratic A hA
  obtain ⟨B, hBA, hBcard⟩ := exists_subgroup_card_four (A := A) hel.isPGroup h4
  have hBY : B ≤ Y := hBA.trans hAY
  have hBel : IsElemAbelian 2 B := hel.mono hBA
  have hBq : commSpace B (commSub B) = ⊥ :=
    le_bot_iff.mp ((commSpace_mono hBA
      (CFSG.SignalizerFunctorTheorem.Quadratic.commSub_mono B A hBA)).trans (le_of_eq hq))
  have hBn : ∀ a ∈ B, ∀ l ∈ L, a * l * a⁻¹ ∈ L := fun a ha l hl => hLn a (hBY ha) l hl
  have hBker : B ⊓ Subgroup.centralizer (L : Set (LGL 2 V)) = ⊥ := by
    rw [eq_bot_iff]
    intro y hy
    obtain ⟨hyB, hyC⟩ := Subgroup.mem_inf.mp hy
    rw [Subgroup.mem_bot]
    exact hcent y (hBY hyB)
      (fun l hl => (Subgroup.mem_centralizer_iff.mp hyC l hl).symm)
  exact br1_odd_core (A := B) h64o h65o hsimple hnab hBn hBcard hBel hBq hBker hshape

theorem br1_odd_false_two (h64o : Asch6_4Odd) (h65o : Asch6_5Odd) {𝒢 : Set (Subgroup (LGL 2 V))}
    {Zs : Submodule (ZMod 2) V} {m i₀ : ℕ} {δ : Subgroup (LGL 2 V) → ℕ}
    (hB : Br2Common Y Γ VA T 𝒢 Zs m i₀ δ) (htwo : Br2TwoComp Y T L₁ L₂)
    (hshape : OddShape ↥L₁) (hA : A ∈ Γ) (h4 : 4 ≤ Nat.card ↥A) : False := by
  classical
  haveI : Finite (LGL 2 V) := w183_finite_lgl
  have hAY : A ≤ Y := hB.h131.le_G A hA
  have hel : IsElemAbelian 2 A := hB.h131.isElemAb A hA
  have hqA : commSpace A (commSub A) = ⊥ := hB.h131.quadratic A hA
  have hAn₁ : ∀ a ∈ A, ∀ l ∈ L₁, a * l * a⁻¹ ∈ L₁ := by
    intro a ha l hl
    rcases htwo.perm a (hAY ha) with ⟨h1, -⟩ | ⟨h1, -⟩
    · have hmem : (MulAut.conj a) l ∈ cj a L₁ := Subgroup.mem_map.mpr ⟨l, hl, rfl⟩
      rw [h1] at hmem
      simpa [MulAut.conj_apply] using hmem
    · exact (w183l39_false_of_swap_common hB htwo hA h4 ha h1).elim
  have hAn₂ : ∀ a ∈ A, ∀ l ∈ L₂, a * l * a⁻¹ ∈ L₂ := by
    intro a ha l hl
    rcases htwo.perm a (hAY ha) with ⟨-, h2⟩ | ⟨h1, -⟩
    · have hmem : (MulAut.conj a) l ∈ cj a L₂ := Subgroup.mem_map.mpr ⟨l, hl, rfl⟩
      rw [h2] at hmem
      simpa [MulAut.conj_apply] using hmem
    · exact (w183l39_false_of_swap_common hB htwo hA h4 ha h1).elim
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
    exact htwo.cent y (hAY hyA)
      (fun l hl => (Subgroup.mem_centralizer_iff.mp hyC₁ l hl).symm)
      (fun l hl => (Subgroup.mem_centralizer_iff.mp hyC₂ l hl).symm)
  by_cases hD2 : 2 ≤ mOf A D
  ·
    obtain ⟨B, hBA, hBcard, hBD⟩ := w183odd_exists_card_four_inf_eq_bot hel hDA hD2
    have hBel : IsElemAbelian 2 B := hel.mono hBA
    have hBq : commSpace B (commSub B) = ⊥ :=
      le_bot_iff.mp ((commSpace_mono hBA
        (CFSG.SignalizerFunctorTheorem.Quadratic.commSub_mono B A hBA)).trans (le_of_eq hqA))
    have hBn : ∀ a ∈ B, ∀ l ∈ L₁, a * l * a⁻¹ ∈ L₁ := fun a ha l hl => hAn₁ a (hBA ha) l hl
    have hBker : B ⊓ Subgroup.centralizer (L₁ : Set (LGL 2 V)) = ⊥ := by
      rw [eq_bot_iff]
      intro y hy
      have hle : B ⊓ Subgroup.centralizer (L₁ : Set (LGL 2 V)) ≤ D :=
        le_inf (inf_le_left.trans hBA) inf_le_right
      have hle2 : B ⊓ Subgroup.centralizer (L₁ : Set (LGL 2 V)) ≤ B ⊓ D :=
        le_inf inf_le_left hle
      exact (hle2.trans (le_of_eq hBD)) hy
    exact br1_odd_core (A := B) h64o h65o htwo.simple₁ htwo.nonab₁ hBn hBcard hBel hBq hBker
      hshape
  · have hD1 : mOf A D ≤ 1 := not_lt.1 hD2
    by_cases hF2 : 2 ≤ mOf A F
    ·
      obtain ⟨B, hBA, hBcard, hBF⟩ := w183odd_exists_card_four_inf_eq_bot hel hFA hF2
      have hBshape : OddShape ↥L₂ :=
        w183odd_oddShape_of_mulEquiv (w183odd_swapEquiv htwo) hshape
      have hBel : IsElemAbelian 2 B := hel.mono hBA
      have hBq : commSpace B (commSub B) = ⊥ :=
        le_bot_iff.mp ((commSpace_mono hBA
        (CFSG.SignalizerFunctorTheorem.Quadratic.commSub_mono B A hBA)).trans (le_of_eq hqA))
      have hBn : ∀ a ∈ B, ∀ l ∈ L₂, a * l * a⁻¹ ∈ L₂ := fun a ha l hl => hAn₂ a (hBA ha) l hl
      have hBker : B ⊓ Subgroup.centralizer (L₂ : Set (LGL 2 V)) = ⊥ := by
        rw [eq_bot_iff]
        intro y hy
        have hle : B ⊓ Subgroup.centralizer (L₂ : Set (LGL 2 V)) ≤ F :=
          le_inf (inf_le_left.trans hBA) inf_le_right
        have hle2 : B ⊓ Subgroup.centralizer (L₂ : Set (LGL 2 V)) ≤ B ⊓ F :=
          le_inf inf_le_left hle
        exact (hle2.trans (le_of_eq hBF)) hy
      exact br1_odd_core (A := B) h64o h65o htwo.simple₂ htwo.nonab₂ hBn hBcard hBel hBq hBker
        hBshape
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
        have := hB.hmi
        omega
      haveI := htwo.simple₁
      haveI := htwo.simple₂
      exact Assumption131.false_of_two_kernels hB.h131 hA htwo.le₁ htwo.le₂ htwo.nonab₁
        htwo.nonab₂ htwo.comm hAn₁ hAn₂ rfl rfl hD0 hF0 hDF hrank

end CFSG.LocalAnalysis.WeakClosure81

end
