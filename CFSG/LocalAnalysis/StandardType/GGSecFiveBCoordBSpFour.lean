module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveBCoordBSpFourDefs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveBSpCoordFrameDefs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveBCoordBSpSp
import CFSG.LocalAnalysis.StandardType.GGSecFiveBCoordBSpSpSplit
import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermSpEquiv
import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermSpKFrame
import CFSG.LocalAnalysis.StandardType.GGSecFiveBCoordBSpField
import CFSG.LocalAnalysis.StandardType.GGSecFiveBSpCoordFrameFacts
import CFSG.LocalAnalysis.StandardType.GGSecFiveTier1OfPrim
import CFSG.ClassicalInvolution.Models.SymplecticPairs.ShortRoot

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.LieType.Universal
open CFSG.ClassicalInvolution.Models.SymplecticPairs (longBlock shortBlock
  commute_shortBlock_shortBlock commute_shortBlock_longBlock)
open scoped MatrixGroups

variable {G : Type} [Group G]

private theorem spFour_commute_of_map {A B C : Subgroup G} {g : G}
    (hA : A.map (MulAut.conj g).toMonoidHom = A) (hB : B.map (MulAut.conj g).toMonoidHom = C)
    (hAC : ∀ a ∈ A, ∀ c ∈ C, a * c = c * a) : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a := by
  intro a ha b hb
  have ha' : g * a * g⁻¹ ∈ A := by
    rw [← hA]
    exact Subgroup.mem_map_of_mem _ ha
  have hb' : g * b * g⁻¹ ∈ C := by
    rw [← hB]
    exact Subgroup.mem_map_of_mem _ hb
  have h := hAC _ ha' _ hb'
  have h2 : g * (a * b) * g⁻¹ = g * (b * a) * g⁻¹ := by
    calc g * (a * b) * g⁻¹ = (g * a * g⁻¹) * (g * b * g⁻¹) := by group
      _ = (g * b * g⁻¹) * (g * a * g⁻¹) := h
      _ = g * (b * a) * g⁻¹ := by group
  simpa only [mul_left_inj, mul_right_inj] using h2

private theorem spFour_commute_range {H S : Type} [Group H] [Group S] (κ : H →* G)
    {X Y : S →* H} (h : ∀ A B, Commute (X A) (Y B)) :
    ∀ a ∈ (κ.comp X).range, ∀ b ∈ (κ.comp Y).range, a * b = b * a := by
  rintro _ ⟨A, rfl⟩ _ ⟨B, rfl⟩
  simp only [MonoidHom.comp_apply]
  rw [← map_mul, ← map_mul, (h A B).eq]

private theorem spFour_exists_order {s : ℕ} {i0 j : Fin (s + 3)} (hij : j ≠ i0) :
    ∃ β : Fin (s + 3) ≃ Fin (s + 3), β 0 = j ∧ β (Fin.last (s + 2)) = i0 := by
  set τ₁ : Equiv.Perm (Fin (s + 3)) := Equiv.swap 0 j with hτ₁
  have h0l : (0 : Fin (s + 3)) ≠ Fin.last (s + 2) := by
    simp only [ne_eq, Fin.ext_iff, Fin.val_zero, Fin.val_last]
    omega
  have hi0' : τ₁ i0 ≠ 0 := by
    intro h
    apply hij
    have h' := congrArg τ₁ h
    rw [hτ₁, Equiv.swap_apply_self, Equiv.swap_apply_left] at h'
    exact h'.symm
  refine ⟨(Equiv.swap (Fin.last (s + 2)) (τ₁ i0)).trans τ₁, ?_, ?_⟩
  · rw [Equiv.trans_apply, Equiv.swap_apply_of_ne_of_ne h0l hi0'.symm, hτ₁,
      Equiv.swap_apply_left]
  · rw [Equiv.trans_apply, Equiv.swap_apply_left, hτ₁, Equiv.swap_apply_self]

private theorem spFour_rotate {s : ℕ} (β : Fin (s + 3) ≃ Fin (s + 3)) :
    ((finRotate (s + 3)).symm.trans β) 0 = β (Fin.last (s + 2)) ∧
      ∀ m : Fin (s + 2), ((finRotate (s + 3)).symm.trans β) m.succ = β m.castSucc := by
  refine ⟨?_, fun m => ?_⟩
  · rw [Equiv.trans_apply]
    congr 1
  · rw [Equiv.trans_apply]
    all_goals
      congr 1
      rw [Equiv.symm_apply_eq]
      ext
      rw [coe_finRotate, if_neg (Fin.castSucc_lt_last m).ne, Fin.val_succ, Fin.coe_castSucc]

private theorem spFour_agree {p s f : ℕ} {Bs : Subgroup G}
    {eta : ↥Bs ≃* (Fin (s + 3) → Multiplicative (ZMod p))}
    {β : Fin (s + 3) ≃ Fin (s + 3)}
    {κ₁ κ₂ : StatedSp (s + 2) (GaloisField 2 f) →* G}
    (hS₁ : ∀ (a b : Fin (s + 2)) (hab : a ≠ b),
      ⁅Subgroup.centralizer (ggBsCoordEq Bs eta (β a.castSucc) (β b.castSucc) : Set G), Bs⁆ =
        (κ₁.comp (shortBlock (GaloisField 2 f) hab)).range)
    (hS₂ : ∀ (a b : Fin (s + 2)) (hab : a ≠ b),
      ⁅Subgroup.centralizer (ggBsCoordEq Bs eta (β a.succ) (β b.succ) : Set G), Bs⁆ =
        (κ₂.comp (shortBlock (GaloisField 2 f) hab)).range)
    (hL₁ : ∀ a : Fin (s + 2),
      ⁅Subgroup.centralizer (ggBsCoordZero Bs eta (β a.castSucc) : Set G), Bs⁆ =
        (κ₁.comp (longBlock (GaloisField 2 f) (s + 2) a)).range)
    (hL₂ : ∀ a : Fin (s + 2),
      ⁅Subgroup.centralizer (ggBsCoordZero Bs eta (β a.succ) : Set G), Bs⁆ =
        (κ₂.comp (longBlock (GaloisField 2 f) (s + 2) a)).range) :
    (∀ k : Fin s,
      (κ₁.comp (shortBlock (GaloisField 2 f) (Fin.castSucc_lt_succ (i := k.succ)).ne)).range =
        (κ₂.comp (shortBlock (GaloisField 2 f)
          (Fin.castSucc_lt_succ (i := k.castSucc)).ne)).range) ∧
      (κ₁.comp (longBlock (GaloisField 2 f) (s + 2) (Fin.last (s + 1)))).range =
        (κ₂.comp (longBlock (GaloisField 2 f) (s + 2) (Fin.last s).castSucc)).range := by
  refine ⟨fun k => ?_, ?_⟩
  · rw [← hS₁, ← hS₂]
    all_goals congr 4
  · rw [← hL₁, ← hL₂]
    all_goals congr 4

private theorem spFour_crosses {p s f : ℕ} (hs : 1 ≤ s) {Bs : Subgroup G}
    {eta : ↥Bs ≃* (Fin (s + 3) → Multiplicative (ZMod p))} {i0 j : Fin (s + 3)}
    {β : Fin (s + 3) ≃ Fin (s + 3)} {c : Fin (s + 3)}
    {κ₁ κ₂ : StatedSp (s + 2) (GaloisField 2 f) →* G} {g : G} {φ : MulAut ↥Bs}
    (hβ0 : β 0 = j) (hβl : β (Fin.last (s + 2)) = i0) (hc : c = β ⟨2, by omega⟩)
    (hwcoord : ∀ (b : ↥Bs) (i : Fin (s + 3)), eta (φ b) (Equiv.swap i0 c i) = eta b i)
    (hgconj : ∀ b : ↥Bs, ((φ b : ↥Bs) : G) = g * b * g⁻¹)
    (hAfix : (κ₁.comp (shortBlock (GaloisField 2 f)
        (Fin.castSucc_lt_succ (i := (0 : Fin (s + 1)))).ne)).range.map
        (MulAut.conj g).toMonoidHom =
      (κ₁.comp (shortBlock (GaloisField 2 f)
        (Fin.castSucc_lt_succ (i := (0 : Fin (s + 1)))).ne)).range)
    (hS₁ : ∀ (a b : Fin (s + 2)) (hab : a ≠ b),
      ⁅Subgroup.centralizer (ggBsCoordEq Bs eta (β a.castSucc) (β b.castSucc) : Set G), Bs⁆ =
        (κ₁.comp (shortBlock (GaloisField 2 f) hab)).range)
    (hS₂ : ∀ (a b : Fin (s + 2)) (hab : a ≠ b),
      ⁅Subgroup.centralizer (ggBsCoordEq Bs eta (β a.succ) (β b.succ) : Set G), Bs⁆ =
        (κ₂.comp (shortBlock (GaloisField 2 f) hab)).range)
    (hL₁ : ∀ a : Fin (s + 2),
      ⁅Subgroup.centralizer (ggBsCoordZero Bs eta (β a.castSucc) : Set G), Bs⁆ =
        (κ₁.comp (longBlock (GaloisField 2 f) (s + 2) a)).range)
    (hL₂ : ∀ a : Fin (s + 2),
      ⁅Subgroup.centralizer (ggBsCoordZero Bs eta (β a.succ) : Set G), Bs⁆ =
        (κ₂.comp (longBlock (GaloisField 2 f) (s + 2) a)).range)
    (hX : ∀ u v : Fin (s + 3), j ≠ u → j ≠ v → u ≠ v → u ≠ i0 → v ≠ i0 →
      ∀ a ∈ ⁅Subgroup.centralizer (ggBsCoordEq Bs eta j u : Set G), Bs⁆,
      ∀ b ∈ ⁅Subgroup.centralizer (ggBsCoordEq Bs eta v i0 : Set G), Bs⁆, a * b = b * a) :
    (∀ a ∈ (κ₁.comp (shortBlock (GaloisField 2 f)
        (Fin.castSucc_lt_succ (i := (0 : Fin (s + 1)))).ne)).range,
      ∀ b ∈ (κ₂.comp (shortBlock (GaloisField 2 f)
        (Fin.castSucc_lt_succ (i := Fin.last s)).ne)).range, a * b = b * a) ∧
      ∀ a ∈ (κ₁.comp (shortBlock (GaloisField 2 f)
          (Fin.castSucc_lt_succ (i := (0 : Fin (s + 1)))).ne)).range,
        ∀ b ∈ (κ₂.comp (longBlock (GaloisField 2 f) (s + 2) (Fin.last (s + 1)))).range,
          a * b = b * a := by
  have hβne : ∀ a b : Fin (s + 3), a.val ≠ b.val → β a ≠ β b := fun a b h hab =>
    h (congrArg Fin.val (β.injective hab))
  have hi0 : Equiv.swap i0 c (β (Fin.last (s + 2))) = c := by
    rw [hβl, Equiv.swap_apply_left]
  refine ⟨?_, ?_⟩
  · have h1 := hS₁ ((0 : Fin (s + 1)).castSucc) ((0 : Fin (s + 1)).succ)
      (Fin.castSucc_lt_succ (i := (0 : Fin (s + 1)))).ne
    have h2 := hS₂ (Fin.last s).castSucc (Fin.last s).succ
      (Fin.castSucc_lt_succ (i := Fin.last s)).ne
    rw [← h1, ← h2,
      show (0 : Fin (s + 1)).castSucc.castSucc = (0 : Fin (s + 3)) from rfl,
      show (0 : Fin (s + 1)).succ.castSucc = (⟨1, by omega⟩ : Fin (s + 3)) from rfl,
      show (Fin.last s).castSucc.succ = (⟨s + 1, by omega⟩ : Fin (s + 3)) from rfl,
      show (Fin.last s).succ.succ = Fin.last (s + 2) from rfl,
      hβ0, hβl]
    exact hX _ _
      (hβ0 ▸ hβne (0 : Fin (s + 3)) ⟨1, by omega⟩ (by simp))
      (hβ0 ▸ hβne (0 : Fin (s + 3)) ⟨s + 1, by omega⟩
        (by simp only [Fin.val_mk, Fin.val_zero]; omega))
      (hβne ⟨1, by omega⟩ ⟨s + 1, by omega⟩ (by simp only [Fin.val_mk]; omega))
      (hβl ▸ hβne ⟨1, by omega⟩ (Fin.last (s + 2))
        (by simp only [Fin.val_mk, Fin.val_last]; omega))
      (hβl ▸ hβne ⟨s + 1, by omega⟩ (Fin.last (s + 2))
        (by simp only [Fin.val_mk, Fin.val_last]; omega))
  · have hB : (κ₂.comp (longBlock (GaloisField 2 f) (s + 2) (Fin.last (s + 1)))).range.map
          (MulAut.conj g).toMonoidHom =
        (κ₁.comp (longBlock (GaloisField 2 f) (s + 2) (⟨2, by omega⟩ : Fin (s + 2)))).range := by
      have h2 : (⟨2, by omega⟩ : Fin (s + 3)) = (⟨2, by omega⟩ : Fin (s + 2)).castSucc :=
        Fin.ext rfl
      rw [← hL₂, ← hL₁, ggSingletonComm_map_conj hgconj hwcoord,
        show β (Fin.last (s + 1)).succ = β (Fin.last (s + 2)) from rfl, hi0, hc, h2]
    refine spFour_commute_of_map hAfix hB (spFour_commute_range κ₁ fun A B => ?_)
    refine commute_shortBlock_longBlock _ ?_ ?_ A B <;>
      simp only [ne_eq, Fin.ext_iff, Fin.coe_castSucc, Fin.val_succ, Fin.val_zero] <;>
      omega

theorem ggSecFiveBCoordBSpSp_charts_of_frames_of_cross {p s f : ℕ} (hs : 1 ≤ s)
    {Bs L K : Subgroup G}
    {eta : ↥Bs ≃* (Fin (s + 3) → Multiplicative (ZMod p))} {i0 j : Fin (s + 3)} (hij : j ≠ i0)
    (hKeta : (ggAutomizer K Bs).map (MulAut.congr eta).toMonoidHom =
      bCoordinateBlock (s + 3) p j)
    (hLF : ∃ (π : Fin (s + 3) ≃ Fin (s + 3)) (κ : StatedSp (s + 2) (GaloisField 2 f) →* G)
      (χ : Multiplicative (ZMod p) →* (GaloisField 2 f)ˣ), π 0 = i0 ∧
        GGSecFiveBPermSpKFrame (r := s + 1) Bs L eta π κ χ)
    (hKF : ∃ (π : Fin (s + 3) ≃ Fin (s + 3)) (κ : StatedSp (s + 2) (GaloisField 2 f) →* G)
      (χ : Multiplicative (ZMod p) →* (GaloisField 2 f)ˣ), π 0 = j ∧
        GGSecFiveBPermSpKFrame (r := s + 1) Bs K eta π κ χ)
    (hLs : ∀ (π : Fin (s + 3) ≃ Fin (s + 3)) (κ : StatedSp (s + 2) (GaloisField 2 f) →* G)
      (χ : Multiplicative (ZMod p) →* (GaloisField 2 f)ˣ),
      GGSecFiveBPermSpKFrame (r := s + 1) Bs L eta π κ χ → ∀ (a b : Fin (s + 2)) (hab : a ≠ b),
        ⁅Subgroup.centralizer (ggBsCoordEq Bs eta (π a.succ) (π b.succ) : Set G), Bs⁆ =
          (κ.comp (shortBlock (GaloisField 2 f) hab)).range)
    (hLl : ∀ (π : Fin (s + 3) ≃ Fin (s + 3)) (κ : StatedSp (s + 2) (GaloisField 2 f) →* G)
      (χ : Multiplicative (ZMod p) →* (GaloisField 2 f)ˣ),
      GGSecFiveBPermSpKFrame (r := s + 1) Bs L eta π κ χ → ∀ a : Fin (s + 2),
        ⁅Subgroup.centralizer (ggBsCoordZero Bs eta (π a.succ) : Set G), Bs⁆ =
          (κ.comp (longBlock (GaloisField 2 f) (s + 2) a)).range)
    (hKs : ∀ (π : Fin (s + 3) ≃ Fin (s + 3)) (κ : StatedSp (s + 2) (GaloisField 2 f) →* G)
      (χ : Multiplicative (ZMod p) →* (GaloisField 2 f)ˣ),
      GGSecFiveBPermSpKFrame (r := s + 1) Bs K eta π κ χ → ∀ (a b : Fin (s + 2)) (hab : a ≠ b),
        ⁅Subgroup.centralizer (ggBsCoordEq Bs eta (π a.succ) (π b.succ) : Set G), Bs⁆ =
          (κ.comp (shortBlock (GaloisField 2 f) hab)).range)
    (hKl : ∀ (π : Fin (s + 3) ≃ Fin (s + 3)) (κ : StatedSp (s + 2) (GaloisField 2 f) →* G)
      (χ : Multiplicative (ZMod p) →* (GaloisField 2 f)ˣ),
      GGSecFiveBPermSpKFrame (r := s + 1) Bs K eta π κ χ → ∀ a : Fin (s + 2),
        ⁅Subgroup.centralizer (ggBsCoordZero Bs eta (π a.succ) : Set G), Bs⁆ =
          (κ.comp (longBlock (GaloisField 2 f) (s + 2) a)).range)
    (hX : ∀ u v : Fin (s + 3), j ≠ u → j ≠ v → u ≠ v → u ≠ i0 → v ≠ i0 →
      ∀ a ∈ ⁅Subgroup.centralizer (ggBsCoordEq Bs eta j u : Set G), Bs⁆,
      ∀ b ∈ ⁅Subgroup.centralizer (ggBsCoordEq Bs eta v i0 : Set G), Bs⁆, a * b = b * a) :
    ∃ κ₁ κ₂ : StatedSp (s + 2) (GaloisField 2 f) →* G,
      Function.Injective κ₁ ∧ κ₁.range = L ∧ Function.Injective κ₂ ∧ κ₂.range = K ∧
      (∀ k : Fin s,
        (κ₁.comp (shortBlock (GaloisField 2 f) (Fin.castSucc_lt_succ (i := k.succ)).ne)).range =
          (κ₂.comp (shortBlock (GaloisField 2 f)
            (Fin.castSucc_lt_succ (i := k.castSucc)).ne)).range) ∧
      (κ₁.comp (longBlock (GaloisField 2 f) (s + 2) (Fin.last (s + 1)))).range =
        (κ₂.comp (longBlock (GaloisField 2 f) (s + 2) (Fin.last s).castSucc)).range ∧
      (∀ a ∈ (κ₁.comp (shortBlock (GaloisField 2 f)
          (Fin.castSucc_lt_succ (i := (0 : Fin (s + 1)))).ne)).range,
        ∀ b ∈ (κ₂.comp (shortBlock (GaloisField 2 f)
          (Fin.castSucc_lt_succ (i := Fin.last s)).ne)).range, a * b = b * a) ∧
      ∀ a ∈ (κ₁.comp (shortBlock (GaloisField 2 f)
          (Fin.castSucc_lt_succ (i := (0 : Fin (s + 1)))).ne)).range,
        ∀ b ∈ (κ₂.comp (longBlock (GaloisField 2 f) (s + 2) (Fin.last (s + 1)))).range,
          a * b = b * a := by
  obtain ⟨β, hβ0, hβl⟩ := spFour_exists_order hij
  obtain ⟨hπ₁0, hπ₁s⟩ := spFour_rotate β
  obtain ⟨π, κ, χ, hπ0, hF⟩ := hLF
  obtain ⟨κ₁, hF₁⟩ := hF.exists_reindex ((finRotate (s + 3)).symm.trans β)
    (by rw [hπ₁0, hβl, hπ0])
  obtain ⟨π', κ', χ', hπ'0, hF'⟩ := hKF
  obtain ⟨κ₂, hF₂⟩ := hF'.exists_reindex β (by rw [hβ0, hπ'0])
  have hβne : ∀ a b : Fin (s + 3), a.val ≠ b.val → β a ≠ β b := fun a b h hab =>
    h (congrArg Fin.val (β.injective hab))
  have hS₁ : ∀ (a b : Fin (s + 2)) (hab : a ≠ b),
      ⁅Subgroup.centralizer (ggBsCoordEq Bs eta (β a.castSucc) (β b.castSucc) : Set G), Bs⁆ =
        (κ₁.comp (shortBlock (GaloisField 2 f) hab)).range := by
    intro a b hab
    rw [← hLs _ _ _ hF₁ a b hab, hπ₁s, hπ₁s]
  have hS₂ : ∀ (a b : Fin (s + 2)) (hab : a ≠ b),
      ⁅Subgroup.centralizer (ggBsCoordEq Bs eta (β a.succ) (β b.succ) : Set G), Bs⁆ =
        (κ₂.comp (shortBlock (GaloisField 2 f) hab)).range := hKs _ _ _ hF₂
  have hL₁ : ∀ a : Fin (s + 2),
      ⁅Subgroup.centralizer (ggBsCoordZero Bs eta (β a.castSucc) : Set G), Bs⁆ =
        (κ₁.comp (longBlock (GaloisField 2 f) (s + 2) a)).range := by
    intro a
    rw [← hLl _ _ _ hF₁ a, hπ₁s]
  have hL₂ : ∀ a : Fin (s + 2),
      ⁅Subgroup.centralizer (ggBsCoordZero Bs eta (β a.succ) : Set G), Bs⁆ =
        (κ₂.comp (longBlock (GaloisField 2 f) (s + 2) a)).range := hKl _ _ _ hF₂
  set c : Fin (s + 3) := β ⟨2, by omega⟩ with hc
  have hi0c : i0 ≠ c := by
    rw [← hβl, hc]
    exact hβne _ _ (by simp only [Fin.val_last]; omega)
  have hcj : c ≠ j := by
    rw [← hβ0, hc]
    exact hβne _ _ (by simp only [Fin.val_zero]; omega)
  obtain ⟨φ, g, hwcoord, hgconj⟩ := exists_conj_swap_of_bCoordinateBlock hKeta hi0c hij.symm hcj
  have hfix : ∀ a : Fin (s + 3), a.val ≠ s + 2 → a.val ≠ 2 → Equiv.swap i0 c (β a) = β a := by
    intro a ha2 ha
    refine Equiv.swap_apply_of_ne_of_ne ?_ ?_
    · rw [← hβl]
      exact hβne _ _ (by simp only [Fin.val_last]; exact ha2)
    · rw [hc]
      exact hβne _ _ ha
  have hAfix : (κ₁.comp (shortBlock (GaloisField 2 f)
        (Fin.castSucc_lt_succ (i := (0 : Fin (s + 1)))).ne)).range.map
        (MulAut.conj g).toMonoidHom =
      (κ₁.comp (shortBlock (GaloisField 2 f)
        (Fin.castSucc_lt_succ (i := (0 : Fin (s + 1)))).ne)).range := by
    rw [← hS₁, ggReflComm_map_conj hgconj hwcoord,
      hfix _ (by simp only [Fin.coe_castSucc, Fin.val_zero]; omega)
        (by simp only [Fin.coe_castSucc, Fin.val_zero]; omega),
      hfix _ (by simp only [Fin.coe_castSucc, Fin.val_succ, Fin.val_zero]; omega)
        (by simp only [Fin.coe_castSucc, Fin.val_succ, Fin.val_zero]; omega)]
  obtain ⟨hagree, hlong⟩ := spFour_agree hS₁ hS₂ hL₁ hL₂
  obtain ⟨hcross₁, hcross₂⟩ :=
    spFour_crosses hs hβ0 hβl hc hwcoord hgconj hAfix hS₁ hS₂ hL₁ hL₂ hX
  exact ⟨κ₁, κ₂, hF₁.1, hF₁.2.1, hF₂.1, hF₂.2.1, hagree, hlong, hcross₁, hcross₂⟩

theorem GGSecFiveBCoordBSpFourCell.ggG0_eq (hJ : BMaxJoinInput) [Finite G]
    {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)}
    (hR : GGSecFiveRouteCfg p B Bs x L D J 𝒦) {n : ℕ}
    (e : (CoxeterMatrix.B n).Group ≃* ↥(ggAutomizerJoin L Bs 𝒦))
    (hP : GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) (CoxeterMatrix.B n) e)
    {eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p))} {i0 : Fin n}
    (h𝒦 : (ggAutomizerJoin L Bs 𝒦).map (MulAut.congr eta).toMonoidHom = bSignedFull n p)
    (hLeta : (ggAutomizer L Bs).map (MulAut.congr eta).toMonoidHom = bCoordinateBlock n p i0)
    (hRM : ∀ (y : G) (K : Subgroup G), GGNbr p B x D J y K →
      ggAutomizer K Bs ≤ ggAutomizerJoin L Bs 𝒦)
    {f : ℕ} {K : Subgroup G} (hc : GGSecFiveBCoordBSpFourCell p Bs L 𝒦 n eta f K i0) :
    ggG0 p B x L D J = L ⊔ K := by
  obtain ⟨-, hn, hK, -, -, j, hj, hKeta⟩ := hc
  exact ggG0_eq_sup_of_bCoordinateBlocks hJ hR e hP (by omega) h𝒦 hLeta hRM hK hj hKeta

theorem GGSecFiveBCoordBSpFourCell.dvd_two_pow_sub_one {p n f : ℕ}
    {Bs L K : Subgroup G} {𝒦 : Finset (Subgroup G)}
    {eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p))} {i0 : Fin n}
    (hcell : GGSecFiveBCoordBSpFourCell p Bs L 𝒦 n eta f K i0)
    (hL : GGInnerDiagOnLabel (fun p lab => GGSecFiveBCoordBLabel n p lab) p Bs L)
    (hRig : GGLabelRigidInput) : p ∣ 2 ^ f - 1 := by
  obtain ⟨hf, hn, -, ⟨eL⟩, -⟩ := hcell
  exact hL.bCoordB_dvd_two_pow_sub_one hRig (by omega) hf eL

section Data


theorem ggSecFiveBCoordBSpFourInput_of_cross (hfr : GGSecFiveBSpCoordFrameInput)
    (hRig : GGLabelRigidInput) (hX : GGSecFiveBCoordBSpFourCrossInput) (hJ : BMaxJoinInput) :
    GGSecFiveBCoordBSpFourInput := by
  intro G _ _ p B Bs x L D J 𝒦 hR hT1 n e hpres h4 eta i0 hBfull hLeta hLab hBB hnbr hG0
    f K hcell
  obtain ⟨hp, hp2⟩ := ggRouteCfg_prime hR
  haveI : Fact p.Prime := ⟨hp⟩
  have hLK : ggG0 p B x L D J = L ⊔ K := hcell.ggG0_eq hJ hR e hpres hBfull hLeta hnbr
  have hdvd : p ∣ 2 ^ f - 1 := hcell.dvd_two_pow_sub_one hLab hRig
  have hcell' := hcell
  obtain ⟨hf, hn4, hK𝒦, ⟨eL⟩, ⟨eK⟩, j, hji, hKeta⟩ := hcell
  obtain ⟨s, hs⟩ : ∃ s, n = s + 3 := ⟨n - 3, by omega⟩
  have hs1 : s = 1 := by omega
  subst hs1
  rw [show 1 + 3 = 4 from rfl] at hs
  subst hs
  obtain ⟨-, hBs, hxBs, -, -⟩ := hR.1.1.tableB_facts
  have hBc : ∀ a ∈ Bs, ∀ b ∈ Bs, a * b = b * a :=
    fun a ha b hb => CFSG.Open.IsElemAbelian.comm hBs ha hb
  have hBsmax : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs :=
    hR.1.1.2.1.2.2.2
  obtain ⟨y, hNy⟩ := hR.2.2.2.1.2 K hK𝒦
  have hyBs : y ∈ Bs := hR.1.1.2.1.1 hNy.1.2.1
  have hKcomp : LargeEvenPComponent p (Subgroup.centralizer ({y} : Set G)) K :=
    hNy.1.2.2.2.2.1
  have hLF := hfr G p hp hp2 2 f (by omega) hf hdvd B Bs L hR.1.1.2.1
    hR.1.2.2.1.1 ⟨eL⟩ eta i0 hLeta
  have hKF := hfr G p hp hp2 2 f (by omega) hf hdvd B Bs K hR.1.1.2.1
    (hR.1.2.2.1.2 y K hNy) ⟨eK⟩ eta j hKeta
  have hLcomp : LargeEvenPComponent p (Subgroup.centralizer ({x} : Set G)) L := by
    obtain ⟨πL, κL, χL, hπL, hFL⟩ := hLF
    exact hR.largeEvenPComponent_L (GGSecFiveBPermSpKFrame.prime_dvd_card hp hFL)
  obtain ⟨κ₁, κ₂, hκ₁, hκ₁L, hκ₂, hκ₂K, hagree, hlong, hcross₁, hcross₂⟩ :=
    ggSecFiveBCoordBSpSp_charts_of_frames_of_cross (s := 1) le_rfl hji hKeta hLF hKF
      (fun π κ χ hF a b hab =>
        ggSecFiveBPermSp_reflComm_K (r := 2) hp2 hf (by omega) hBc hBsmax hxBs hLcomp hF hab)
      (fun π κ χ hF a =>
        ggSecFiveBPermSp_singletonComm_K (r := 2) hp2 hf (by omega) hBc hBsmax hxBs hLcomp hF a)
      (fun π κ χ hF a b hab =>
        ggSecFiveBPermSp_reflComm_K (r := 2) hp2 hf (by omega) hBc hBsmax hyBs hKcomp hF hab)
      (fun π κ χ hF a =>
        ggSecFiveBPermSp_singletonComm_K (r := 2) hp2 hf (by omega) hBc hBsmax hyBs hKcomp hF a)
      (fun u v h1 h2 h3 h4 h5 =>
        hX G p B Bs x L D J 𝒦 hR hT1 4 e hpres (le_refl 4) eta i0 hBfull hLeta hLab hBB hnbr
          hG0 f K hcell' j hji hKeta u v h1 h2 h3 h4 h5)
  exact ggSecFiveData_of_spSpCharts (s := 1) le_rfl hf κ₁ κ₂ hκ₁ hκ₂ hagree hlong hcross₁
    hcross₂ (by rw [hLK, hκ₁L, hκ₂K])

end Data

end CFSG.StandardType

end
