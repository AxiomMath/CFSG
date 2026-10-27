module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermSpPlaneFrameDefs
import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermSpPlaneBlocks
import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermUniBlocks
import CFSG.LocalAnalysis.StandardType.GGQTwoSpSmallBlocks
import CFSG.ClassicalInvolution.Models.SymplecticPairs.EmbedCommute
public import CFSG.ClassicalInvolution.Models.SymplecticPairs.ShortRoot
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentySpCoord
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyAut
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotLeviFact

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.LieType.Universal
open CFSG.ClassicalInvolution.Models.SymplecticPairs (spEmbed longBlock spIncl spEmbedMat
  spIncl_apply spEmbedMat_apply_image spEmbedMat_apply_of_not_mem range_spEmbed suppGroup
  suppGroup_mono commute_suppGroup_compl spEmbed_longBlock spEmbed_injective mat_spEmbed pairMap
  pairMap_zero pairMap_one pairMap_injective longBlock_surjective_one
  commute_spEmbed_of_disjoint)
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_injective)
open scoped MatrixGroups

variable {G : Type} [Group G]

variable {F₀ : Type} [Field F₀] {m n l : ℕ}

private theorem spIncl_comp {σ : Fin m → Fin n} {τ : Fin n → Fin l} :
    spIncl (K := F₀) (τ ∘ σ) = spIncl (K := F₀) τ * spIncl (K := F₀) σ := by
  have h : ∀ b : Fin m ⊕ Fin m,
      Sum.map (τ ∘ σ) (τ ∘ σ) b = Sum.map τ τ (Sum.map σ σ b) := fun b => by
    cases b <;> rfl
  ext a b
  simp only [Matrix.mul_apply, spIncl_apply, h, mul_one]
  rw [Finset.sum_eq_single (Sum.map σ σ b)]
  · simp
  · intro c _ hc
    rw [if_neg hc, mul_zero]
  · intro h'
    exact absurd (Finset.mem_univ (Sum.map σ σ b)) h'

private theorem spEmbedMat_comp {σ : Fin m → Fin n} {τ : Fin n → Fin l}
    (M : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) F₀) :
    spEmbedMat τ (spEmbedMat σ M) = spEmbedMat (τ ∘ σ) M := by
  simp only [spEmbedMat, spIncl_comp, Matrix.transpose_mul, Matrix.mul_assoc,
    add_sub_cancel_left]

private theorem spEmbed_comp {σ : Fin m → Fin n} {τ : Fin n → Fin l}
    (hσ : Function.Injective σ) (hτ : Function.Injective τ) (x : StatedSp m F₀) :
    spEmbed τ hτ (spEmbed σ hσ x) = spEmbed (τ ∘ σ) (hτ.comp hσ) x := by
  refine mat_injective ?_
  rw [mat_spEmbed, mat_spEmbed, mat_spEmbed]
  exact spEmbedMat_comp _

private theorem spIncl_id : spIncl (K := F₀) (id : Fin m → Fin m) = 1 := by
  ext a b
  rw [spIncl_apply]
  cases a <;> cases b <;> simp [Matrix.one_apply]

private theorem spEmbedMat_id (M : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) F₀) :
    spEmbedMat (id : Fin m → Fin m) M = M := by
  rw [spEmbedMat, spIncl_id, Matrix.transpose_one, Matrix.one_mul, Matrix.mul_one]
  abel

private theorem spEmbed_id (x : StatedSp m F₀) :
    spEmbed (id : Fin m → Fin m) Function.injective_id x = x := by
  refine mat_injective ?_
  rw [mat_spEmbed, spEmbedMat_id]

private theorem spEmbed_congr {σ τ : Fin m → Fin n} (h : σ = τ)
    (hσ : Function.Injective σ) (hτ : Function.Injective τ) (x : StatedSp m F₀) :
    spEmbed σ hσ x = spEmbed τ hτ x := by
  subst h
  rfl

private theorem spEmbed_surjective_perm (ρ : Equiv.Perm (Fin m)) :
    Function.Surjective (spEmbed (K := F₀) ρ ρ.injective) := by
  intro x
  refine ⟨spEmbed ρ.symm ρ.symm.injective x, ?_⟩
  have h : (⇑ρ) ∘ (⇑ρ.symm) = (id : Fin m → Fin m) := by funext i; simp
  calc spEmbed (K := F₀) ρ ρ.injective (spEmbed ρ.symm ρ.symm.injective x)
      = spEmbed (K := F₀) (⇑ρ ∘ ⇑ρ.symm) (ρ.injective.comp ρ.symm.injective) x :=
        spEmbed_comp (hσ := ρ.symm.injective) (hτ := ρ.injective) x
    _ = spEmbed (K := F₀) (id : Fin m → Fin m) Function.injective_id x :=
        spEmbed_congr h _ _ x
    _ = x := spEmbed_id x

private theorem spEmbed_range_perm (ρ : Equiv.Perm (Fin m)) :
    (spEmbed (K := F₀) ρ ρ.injective).range = ⊤ :=
  MonoidHom.range_eq_top.2 (spEmbed_surjective_perm ρ)

private theorem block_range_eq [Finite G] {p n s : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    {F : Type} [Field F] [Finite F] [CharP F 2]
    {Bs K : Subgroup G} {y : G}
    (hBs : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs)
    (hyB : y ∈ Bs) (hK : CFSG.Open.IsComponentOf K (Subgroup.centralizer ({y} : Set G)))
    {eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p))} {π : Fin (s + 3) ≃ Fin n}
    {κ : StatedSp (s + 2) F →* G} {ζ : Multiplicative (ZMod p) →* SL(2, F)}
    (hκ : GGSecFiveBPermSpPlaneFrame Bs K eta π κ ζ)
    {k : ℕ} (hF : 4 ≤ Nat.card F ∨ 3 ≤ k + 1) (σ : Fin (k + 1) → Fin (s + 2))
    (hσ : Function.Injective σ) (hσs : ¬ Function.Surjective σ) :
    (κ.comp (spEmbed σ hσ)).range =
      ggBlockComm Bs eta (Set.range fun l => π (σ l).succ) :=
  (ggSecFiveBPermZeta_commutator_centralizer_eq_of_or (r := s + 1) hp2 hF hBs hyB hK hκ
    σ hσ hσs).symm

private theorem set_range_fin_two {α : Type} (g : Fin 2 → α) : Set.range g = {g 0, g 1} := by
  ext x
  constructor
  · rintro ⟨i, rfl⟩
    fin_cases i <;> simp
  · rintro (rfl | rfl)
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩

private theorem set_range_fin_one {α : Type} (c : α) : Set.range (fun _ : Fin 1 => c) = {c} := by
  ext x
  constructor
  · rintro ⟨l, rfl⟩
    exact Set.mem_singleton c
  · intro hx
    rw [Set.mem_singleton_iff] at hx
    subst hx
    exact ⟨0, rfl⟩

private theorem image_swap_image {m n : ℕ} (π : Fin m ≃ Fin n) (a b : Fin m)
    (T : Set (Fin m)) :
    (Equiv.swap (π a) (π b)) '' (π '' T) = π '' ((Equiv.swap a b) '' T) := by
  have h : (fun x => Equiv.swap (π a) (π b) (π x)) = fun x => π (Equiv.swap a b x) := by
    funext x
    by_cases h1 : x = a
    · subst h1; simp
    · by_cases h2 : x = b
      · subst h2; simp
      · have h1' : π x ≠ π a := fun h => h1 (π.injective h)
        have h2' : π x ≠ π b := fun h => h2 (π.injective h)
        rw [Equiv.swap_apply_of_ne_of_ne h1' h2', Equiv.swap_apply_of_ne_of_ne h1 h2]
  rw [← Set.image_comp, ← Set.image_comp]
  show (fun x => Equiv.swap (π a) (π b) (π x)) '' T = (fun x => π (Equiv.swap a b x)) '' T
  rw [h]

private theorem fin_one_eq {N : ℕ} [NeZero N] (hN : 1 < N) :
    (⟨1, hN⟩ : Fin N) = (1 : Fin N) := by
  apply Fin.ext
  rw [Fin.val_one', Nat.mod_eq_of_lt hN]

private theorem fin_three_eq {N : ℕ} [NeZero N] (hN : 3 < N) :
    (⟨3, hN⟩ : Fin N) = (3 : Fin N) := by
  apply Fin.ext
  rw [Fin.coe_ofNat_eq_mod, Nat.mod_eq_of_lt hN]

private theorem swap01_fix {N : ℕ} [NeZero N] (hN : 1 < N) {x : Fin N} (h : 2 ≤ x.val) :
    (Equiv.swap (0 : Fin N) 1) x = x := by
  apply Equiv.swap_apply_of_ne_of_ne
  · intro hx
    have h2 : x.val = 0 := by simpa using congrArg Fin.val hx
    omega
  · intro hx
    rw [← fin_one_eq hN] at hx
    have h2 : x.val = 1 := by simpa using congrArg Fin.val hx
    omega

private theorem swap03_fix {N : ℕ} [NeZero N] (hN : 3 < N) {x : Fin N}
    (h0 : x.val ≠ 0) (h3 : x.val ≠ 3) : (Equiv.swap (0 : Fin N) 3) x = x := by
  apply Equiv.swap_apply_of_ne_of_ne
  · intro hx
    exact h0 (by simpa using congrArg Fin.val hx)
  · intro hx
    rw [← fin_three_eq hN] at hx
    exact h3 (by simpa using congrArg Fin.val hx)

private theorem swap01_one {N : ℕ} [NeZero N] (hN : 1 < N) :
    (Equiv.swap (0 : Fin N) 1) (⟨1, hN⟩ : Fin N) = 0 := by
  rw [fin_one_eq hN]
  exact Equiv.swap_apply_right _ _

private theorem swap03_zero {N : ℕ} [NeZero N] (hN : 3 < N) :
    (Equiv.swap (0 : Fin N) 3) (0 : Fin N) = (⟨3, hN⟩ : Fin N) := by
  rw [← fin_three_eq hN]
  exact Equiv.swap_apply_left _ _

private theorem swap_pi_image_range_succ {n s : ℕ} (π : Fin (s + 3) ≃ Fin n) :
    (Equiv.swap (π 0) (π 1)) '' (Set.range fun l : Fin (s + 1) => π ((Fin.succ l).succ)) =
      Set.range fun l : Fin (s + 1) => π ((Fin.succ l).succ) := by
  have hS : (Set.range fun l : Fin (s + 1) => π ((Fin.succ l).succ)) =
      π '' (Set.range fun l : Fin (s + 1) => ((Fin.succ l).succ : Fin (s + 3))) :=
    Set.range_comp' ..
  have hfix : ∀ x ∈ (Set.range fun l : Fin (s + 1) => ((Fin.succ l).succ : Fin (s + 3))),
      (Equiv.swap (0 : Fin (s + 3)) 1) x = x := by
    rintro x ⟨l, rfl⟩
    exact swap01_fix (N := s + 3) (by omega) (by rw [Fin.val_succ, Fin.val_succ]; omega)
  have hT : (Equiv.swap (0 : Fin (s + 3)) 1) '' (Set.range fun l : Fin (s + 1) =>
      ((Fin.succ l).succ : Fin (s + 3))) = Set.range fun l : Fin (s + 1) =>
      ((Fin.succ l).succ : Fin (s + 3)) := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      rwa [hfix y hy]
    · intro hx
      exact ⟨x, hx, hfix x hx⟩
  have step1 : (Equiv.swap (π 0) (π 1)) ''
      (Set.range fun l : Fin (s + 1) => π ((Fin.succ l).succ)) =
      π '' ((Equiv.swap (0 : Fin (s + 3)) 1) ''
        (Set.range fun l : Fin (s + 1) => ((Fin.succ l).succ : Fin (s + 3)))) := by
    rw [hS, image_swap_image]
  rw [step1, hT, ← hS]

private theorem swap_pi_image_range_last {n s : ℕ} (hs : 2 ≤ s) (π : Fin (s + 3) ≃ Fin n) :
    (Equiv.swap (π 0) (π 1)) ''
      (Set.range fun l : Fin 1 => π ((fun _ : Fin 1 => Fin.last (s + 1)) l).succ) =
      Set.range fun l : Fin 1 => π ((fun _ : Fin 1 => Fin.last (s + 1)) l).succ := by
  have hS : (Set.range fun l : Fin 1 => π ((fun _ : Fin 1 => Fin.last (s + 1)) l).succ) =
      π '' ({(⟨s + 2, by omega⟩ : Fin (s + 3))} : Set (Fin (s + 3))) := by
    rw [Set.range_comp', set_range_fin_one]
    congr 1
  have hfix : (Equiv.swap (0 : Fin (s + 3)) 1) (⟨s + 2, by omega⟩ : Fin (s + 3)) =
      ⟨s + 2, by omega⟩ :=
    swap01_fix (N := s + 3) (by omega) (by simp only [Fin.val_mk]; omega)
  have hT : (Equiv.swap (0 : Fin (s + 3)) 1) ''
      ({(⟨s + 2, by omega⟩ : Fin (s + 3))} : Set (Fin (s + 3))) =
      {(⟨s + 2, by omega⟩ : Fin (s + 3))} := by
    rw [Set.image_singleton, hfix]
  have step1 : (Equiv.swap (π 0) (π 1)) ''
      (Set.range fun l : Fin 1 => π ((fun _ : Fin 1 => Fin.last (s + 1)) l).succ) =
      π '' ((Equiv.swap (0 : Fin (s + 3)) 1) ''
        ({(⟨s + 2, by omega⟩ : Fin (s + 3))} : Set (Fin (s + 3)))) := by
    rw [hS, image_swap_image]
  rw [step1, hT, ← hS]

private theorem swap_pi_image_planes_zero_one {n s : ℕ} (hs : 2 ≤ s) (π : Fin (s + 3) ≃ Fin n) :
    (Equiv.swap (π 0) (π 3)) ''
      (Set.range fun l : Fin 2 => π (((Fin.castLE (Nat.le_add_left 2 s)) l).succ)) =
      Set.range fun l : Fin 2 => π (((Fin.castLE (Nat.le_add_left 2 s)) l).succ) := by
  have hS : (Set.range fun l : Fin 2 => π (((Fin.castLE (Nat.le_add_left 2 s)) l).succ)) =
      π '' ({(⟨1, by omega⟩ : Fin (s + 3)),
        (⟨2, by omega⟩ : Fin (s + 3))} : Set (Fin (s + 3))) := by
    rw [Set.range_comp', set_range_fin_two]
    congr 1
  have hfix1 : (Equiv.swap (0 : Fin (s + 3)) 3) (⟨1, by omega⟩ : Fin (s + 3)) =
      ⟨1, by omega⟩ :=
    swap03_fix (N := s + 3) (by omega) (by simp only [Fin.val_mk]; omega)
      (by simp only [Fin.val_mk]; omega)
  have hfix2 : (Equiv.swap (0 : Fin (s + 3)) 3) (⟨2, by omega⟩ : Fin (s + 3)) =
      ⟨2, by omega⟩ :=
    swap03_fix (N := s + 3) (by omega) (by simp only [Fin.val_mk]; omega)
      (by simp only [Fin.val_mk]; omega)
  have hT : (Equiv.swap (0 : Fin (s + 3)) 3) ''
      ({(⟨1, by omega⟩ : Fin (s + 3)),
        (⟨2, by omega⟩ : Fin (s + 3))} : Set (Fin (s + 3))) =
      ({(⟨1, by omega⟩ : Fin (s + 3)),
        (⟨2, by omega⟩ : Fin (s + 3))} : Set (Fin (s + 3))) := by
    rw [Set.image_pair, hfix1, hfix2]
  have step1 : (Equiv.swap (π 0) (π 3)) ''
      (Set.range fun l : Fin 2 => π (((Fin.castLE (Nat.le_add_left 2 s)) l).succ)) =
      π '' ((Equiv.swap (0 : Fin (s + 3)) 3) ''
        ({(⟨1, by omega⟩ : Fin (s + 3)),
          (⟨2, by omega⟩ : Fin (s + 3))} : Set (Fin (s + 3)))) := by
    rw [hS, image_swap_image]
  rw [step1, hT, ← hS]

private theorem swap01_pi_image_planes_last_zero {n s : ℕ} (hs : 2 ≤ s)
    (π : Fin (s + 3) ≃ Fin n) :
    (Equiv.swap (π 0) (π 1)) ''
      (Set.range fun l : Fin 2 => π ((pairMap (Fin.last (s + 1)) 0) l).succ) =
      π '' ({(⟨s + 2, by omega⟩ : Fin (s + 3)),
        (0 : Fin (s + 3))} : Set (Fin (s + 3))) := by
  have hC : (Set.range fun l : Fin 2 => π ((pairMap (Fin.last (s + 1)) 0) l).succ) =
      π '' ({(⟨s + 2, by omega⟩ : Fin (s + 3)),
        (⟨1, by omega⟩ : Fin (s + 3))} : Set (Fin (s + 3))) := by
    rw [Set.range_comp', set_range_fin_two]
    congr 1
  have hfix_s : (Equiv.swap (0 : Fin (s + 3)) 1) (⟨s + 2, by omega⟩ : Fin (s + 3)) =
      ⟨s + 2, by omega⟩ :=
    swap01_fix (N := s + 3) (by omega) (by simp only [Fin.val_mk]; omega)
  have hfix_1 : (Equiv.swap (0 : Fin (s + 3)) 1) (⟨1, by omega⟩ : Fin (s + 3)) =
      (0 : Fin (s + 3)) :=
    swap01_one (N := s + 3) (by omega)
  have hstep : (Equiv.swap (0 : Fin (s + 3)) 1) ''
      ({(⟨s + 2, by omega⟩ : Fin (s + 3)),
        (⟨1, by omega⟩ : Fin (s + 3))} : Set (Fin (s + 3))) =
      ({(⟨s + 2, by omega⟩ : Fin (s + 3)), (0 : Fin (s + 3))} : Set (Fin (s + 3))) := by
    rw [Set.image_pair, hfix_s, hfix_1]
  rw [hC, image_swap_image, hstep]

private theorem swap03_pi_image_planes_last_zero {n s : ℕ} (hs : 2 ≤ s)
    (π : Fin (s + 3) ≃ Fin n) :
    (Equiv.swap (π 0) (π 3)) ''
      (π '' ({(⟨s + 2, by omega⟩ : Fin (s + 3)),
        (0 : Fin (s + 3))} : Set (Fin (s + 3)))) =
      Set.range fun l : Fin 2 =>
        π ((pairMap (Fin.last (s + 1)) (⟨2, by omega⟩ : Fin (s + 2))) l).succ := by
  have hE : (Set.range fun l : Fin 2 =>
      π ((pairMap (Fin.last (s + 1)) (⟨2, by omega⟩ : Fin (s + 2))) l).succ) =
      π '' ({(⟨s + 2, by omega⟩ : Fin (s + 3)),
        (⟨3, by omega⟩ : Fin (s + 3))} : Set (Fin (s + 3))) := by
    rw [Set.range_comp', set_range_fin_two]
    congr 1
  have hfix_s : (Equiv.swap (0 : Fin (s + 3)) 3) (⟨s + 2, by omega⟩ : Fin (s + 3)) =
      ⟨s + 2, by omega⟩ :=
    swap03_fix (N := s + 3) (by omega) (by simp only [Fin.val_mk]; omega)
      (by simp only [Fin.val_mk]; omega)
  have hfix_0 : (Equiv.swap (0 : Fin (s + 3)) 3) (0 : Fin (s + 3)) =
      (⟨3, by omega⟩ : Fin (s + 3)) :=
    swap03_zero (N := s + 3) (by omega)
  have hstep : (Equiv.swap (0 : Fin (s + 3)) 3) ''
      ({(⟨s + 2, by omega⟩ : Fin (s + 3)), (0 : Fin (s + 3))} : Set (Fin (s + 3))) =
      ({(⟨s + 2, by omega⟩ : Fin (s + 3)),
        (⟨3, by omega⟩ : Fin (s + 3))} : Set (Fin (s + 3))) := by
    rw [Set.image_pair, hfix_s, hfix_0]
  rw [image_swap_image, hstep, ← hE]

private theorem swap_swap_pi_image_planes {n s : ℕ} (hs : 2 ≤ s) (π : Fin (s + 3) ≃ Fin n) :
    (Equiv.swap (π 0) (π 3)) '' ((Equiv.swap (π 0) (π 1)) ''
      (Set.range fun l : Fin 2 => π ((pairMap (Fin.last (s + 1)) 0) l).succ)) =
      Set.range fun l : Fin 2 =>
        π ((pairMap (Fin.last (s + 1)) (⟨2, by omega⟩ : Fin (s + 2))) l).succ := by
  rw [swap01_pi_image_planes_last_zero hs, swap03_pi_image_planes_last_zero hs]

private theorem last_injective {s : ℕ} :
    Function.Injective (fun _ : Fin 1 => Fin.last (s + 1)) := by
  intro a b _
  have ha := a.isLt
  have hb := b.isLt
  ext
  omega

private theorem not_surjective_castLE {s : ℕ} (hs : 2 ≤ s) :
    ¬ Function.Surjective (Fin.castLE (Nat.le_add_left 2 s) : Fin 2 → Fin (s + 2)) := by
  intro hsurj
  obtain ⟨l, hl⟩ := hsurj (Fin.last (s + 1))
  have h2 : l.val = s + 1 := congrArg Fin.val hl
  omega

private theorem not_surjective_succ {s : ℕ} :
    ¬ Function.Surjective (Fin.succ : Fin (s + 1) → Fin (s + 2)) := by
  intro hsurj
  obtain ⟨l, hl⟩ := hsurj (⟨0, by omega⟩ : Fin (s + 2))
  have h2 : l.val + 1 = 0 := congrArg Fin.val hl
  omega

private theorem not_surjective_last {s : ℕ} :
    ¬ Function.Surjective (fun _ : Fin 1 => Fin.last (s + 1)) := by
  intro hsurj
  obtain ⟨l, hl⟩ := hsurj (⟨0, by omega⟩ : Fin (s + 2))
  have h2 : s + 1 = 0 := by simpa using congrArg Fin.val hl
  omega

private theorem not_surjective_pairMap_zero {s : ℕ} (hs : 2 ≤ s) :
    ¬ Function.Surjective (pairMap (Fin.last (s + 1)) (0 : Fin (s + 2))) := by
  intro hsurj
  obtain ⟨l, hl⟩ := hsurj (⟨1, by omega⟩ : Fin (s + 2))
  fin_cases l
  · have h2 : s + 1 = 1 := by simpa [pairMap_zero] using congrArg Fin.val hl
    omega
  · have h2 : (0 : ℕ) = 1 := by simpa [pairMap_one] using congrArg Fin.val hl
    omega

private theorem not_surjective_pairMap_two {s : ℕ} (hs : 2 ≤ s) :
    ¬ Function.Surjective (pairMap (Fin.last (s + 1)) (⟨2, by omega⟩ : Fin (s + 2))) := by
  intro hsurj
  obtain ⟨l, hl⟩ := hsurj (⟨0, by omega⟩ : Fin (s + 2))
  fin_cases l
  · have h2 : s + 1 = 0 := by simpa [pairMap_zero] using congrArg Fin.val hl
    omega
  · have h2 : (2 : ℕ) = 0 := by simpa [pairMap_one] using congrArg Fin.val hl
    omega

private theorem pairMap_last_zero_injective {s : ℕ} :
    Function.Injective (pairMap (Fin.last (s + 1)) (0 : Fin (s + 2))) :=
  pairMap_injective (by intro h; have := congrArg Fin.val h; simp at this)

private theorem pairMap_last_two_injective {s : ℕ} (hs : 2 ≤ s) :
    Function.Injective (pairMap (Fin.last (s + 1)) (⟨2, by omega⟩ : Fin (s + 2))) :=
  pairMap_injective (by intro h; have := congrArg Fin.val h; simp at this; omega)

private theorem spEmbed_rot_comp_castSucc {F : Type} [Field F] {s : ℕ} :
    (spEmbed (K := F) (finRotate (s + 2)) (finRotate (s + 2)).injective).comp
        (spEmbed Fin.castSucc (Fin.castSucc_injective (s + 1))) =
      spEmbed Fin.succ (Fin.succ_injective (s + 1)) := by
  refine MonoidHom.ext fun x => ?_
  have hfun : (fun l : Fin (s + 1) => (finRotate (s + 2)) (Fin.castSucc l)) =
      fun l => Fin.succ l := by
    funext l
    rw [finRotate_succ_apply]
    apply Fin.ext
    simp
  rw [MonoidHom.comp_apply, spEmbed_comp]
  exact spEmbed_congr hfun _ _ x

private theorem spEmbed_rot_comp_natAdd {F : Type} [Field F] {s : ℕ} :
    (spEmbed (K := F) (finRotate (s + 2)) (finRotate (s + 2)).injective).comp
        (spEmbed (Fin.natAdd s) (Fin.natAdd_injective 2 s)) =
      spEmbed (pairMap (Fin.last (s + 1)) (0 : Fin (s + 2)))
        pairMap_last_zero_injective := by
  refine MonoidHom.ext fun x => ?_
  have hfun : (fun l : Fin 2 => (finRotate (s + 2)) (Fin.natAdd s l)) =
      fun l => pairMap (Fin.last (s + 1)) 0 l := by
    funext l
    fin_cases l
    · show (finRotate (s + 2)) (Fin.natAdd s (0 : Fin 2)) =
        pairMap (Fin.last (s + 1)) 0 (0 : Fin 2)
      rw [pairMap_zero]
      show (finRotate (s + 2)) (⟨s, by omega⟩ : Fin (s + 2)) = Fin.last (s + 1)
      rw [finRotate_succ_apply]
      apply Fin.ext
      show (s + 1) % (s + 2) = s + 1
      rw [Nat.mod_eq_of_lt (by omega)]
    · show (finRotate (s + 2)) (Fin.natAdd s (1 : Fin 2)) =
        pairMap (Fin.last (s + 1)) 0 (1 : Fin 2)
      rw [pairMap_one]
      show (finRotate (s + 2)) (⟨s + 1, by omega⟩ : Fin (s + 2)) = 0
      rw [show (⟨s + 1, by omega⟩ : Fin (s + 2)) = Fin.last (s + 1) from rfl,
        finRotate_last]
  rw [MonoidHom.comp_apply, spEmbed_comp]
  exact spEmbed_congr hfun _ _ x

private theorem spEmbed_rot_comp_longBlock {F : Type} [Field F] {s : ℕ} :
    (spEmbed (K := F) (finRotate (s + 2)) (finRotate (s + 2)).injective).comp
        (longBlock F (s + 2) (Fin.last s).castSucc) =
      longBlock F (s + 2) (Fin.last (s + 1)) := by
  refine MonoidHom.ext fun A => ?_
  rw [MonoidHom.comp_apply, spEmbed_longBlock]
  have h : (finRotate (s + 2)) ((Fin.last s).castSucc) = Fin.last (s + 1) := by
    rw [finRotate_succ_apply]
    apply Fin.ext
    simp
  rw [h]

private theorem range_conj_comp {F : Type} [Field F] {s : ℕ} {M : Type} [Group M]
    (c : G →* G) (κ : StatedSp (s + 2) F →* G)
    (p : StatedSp (s + 2) F →* StatedSp (s + 2) F) (f : M →* StatedSp (s + 2) F) :
    ((c.comp (κ.comp p)).comp f).range = ((((p.comp f).range).map κ).map c) := by
  rw [MonoidHom.comp_assoc, MonoidHom.range_comp, MonoidHom.comp_assoc,
    MonoidHom.range_comp]

private theorem disjoint_castLE_pairMap_two {s : ℕ} (hs : 2 ≤ s) :
    Disjoint (Set.range (Fin.castLE (Nat.le_add_left 2 s) : Fin 2 → Fin (s + 2)))
      (Set.range (pairMap (Fin.last (s + 1)) (⟨2, by omega⟩ : Fin (s + 2)))) := by
  rw [Set.disjoint_left]
  rintro y ⟨i, rfl⟩ ⟨j, hj⟩
  have h1 : (Fin.castLE (Nat.le_add_left 2 s) i).val ≤ 1 := by
    show i.val ≤ 1
    omega
  have h2 : 2 ≤ (pairMap (Fin.last (s + 1)) (⟨2, by omega⟩ : Fin (s + 2)) j).val := by
    fin_cases j
    · show 2 ≤ (Fin.last (s + 1)).val
      simp only [Fin.val_last]
      omega
    · show 2 ≤ (⟨2, by omega⟩ : Fin (s + 2)).val
      simp only [Fin.val_mk]
      omega
  have h3 : (pairMap (Fin.last (s + 1)) (⟨2, by omega⟩ : Fin (s + 2)) j).val =
      (Fin.castLE (Nat.le_add_left 2 s) i).val := congrArg Fin.val hj
  omega

private theorem conj_w_mem_block_zero_one [Finite G] {p n s : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    {F : Type} [Field F] [Finite F] [CharP F 2] (hF : 4 ≤ Nat.card F) (hs : 2 ≤ s)
    {Bs K : Subgroup G} {y : G}
    (hBs : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs)
    (hyB : y ∈ Bs) (hK : CFSG.Open.IsComponentOf K (Subgroup.centralizer ({y} : Set G)))
    {eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p))} {π : Fin (s + 3) ≃ Fin n}
    {κ : StatedSp (s + 2) F →* G} {ζ : Multiplicative (ZMod p) →* SL(2, F)}
    (hκ : GGSecFiveBPermSpPlaneFrame Bs K eta π κ ζ)
    {w : G} (hw : w ∈ Subgroup.normalizer (Bs : Set G))
    (hwη : MulAut.congr eta (ggConjAut Bs hw) = SpCoord.permAut (Equiv.swap (π 0) (π 3)))
    {a : G}
    (ha : a ∈ (κ.comp (spEmbed (Fin.castLE (Nat.le_add_left 2 s) : Fin 2 → Fin (s + 2))
      (Fin.castLE_injective _))).range) :
    (MulAut.conj w) a ∈ (κ.comp (spEmbed (Fin.castLE (Nat.le_add_left 2 s) :
      Fin 2 → Fin (s + 2)) (Fin.castLE_injective _))).range := by
  have hnsA := not_surjective_castLE (s := s) hs
  set S : Set (Fin n) :=
    Set.range (fun l : Fin 2 => π (((Fin.castLE (Nat.le_add_left 2 s)) l).succ)) with hS
  rw [block_range_eq hp2 hBs hyB hK hκ (Or.inl hF)
    (Fin.castLE (Nat.le_add_left 2 s) : Fin 2 → Fin (s + 2))
    (Fin.castLE_injective _) hnsA] at ha ⊢
  have h1 : (MulAut.conj w) a ∈ (ggBlockComm Bs eta S).map
      (MulAut.conj w).toMonoidHom := Subgroup.mem_map_of_mem _ ha
  rw [ggBlockComm_map_conj hw hwη, hS,
    swap_pi_image_planes_zero_one hs, ← hS] at h1
  exact h1

private theorem conj_w_mem_block_last_two [Finite G] {p n s : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    {F : Type} [Field F] [Finite F] [CharP F 2] (hF : 4 ≤ Nat.card F) (hs : 2 ≤ s)
    {Bs K : Subgroup G} {y : G}
    (hBs : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs)
    (hyB : y ∈ Bs) (hK : CFSG.Open.IsComponentOf K (Subgroup.centralizer ({y} : Set G)))
    {eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p))} {π : Fin (s + 3) ≃ Fin n}
    {κ : StatedSp (s + 2) F →* G} {ζ : Multiplicative (ZMod p) →* SL(2, F)}
    (hκ : GGSecFiveBPermSpPlaneFrame Bs K eta π κ ζ)
    {g w : G} (hg : g ∈ Subgroup.normalizer (Bs : Set G))
    (hgη : MulAut.congr eta (ggConjAut Bs hg) = SpCoord.permAut (Equiv.swap (π 0) (π 1)))
    (hw : w ∈ Subgroup.normalizer (Bs : Set G))
    (hwη : MulAut.congr eta (ggConjAut Bs hw) = SpCoord.permAut (Equiv.swap (π 0) (π 3)))
    {x : G}
    (hx : x ∈ (κ.comp (spEmbed (pairMap (Fin.last (s + 1)) (0 : Fin (s + 2)))
      pairMap_last_zero_injective)).range) :
    (MulAut.conj w) ((MulAut.conj g) x) ∈ (κ.comp (spEmbed
      (pairMap (Fin.last (s + 1)) (⟨2, by omega⟩ : Fin (s + 2)))
      (pairMap_last_two_injective hs))).range := by
  have hnsC := not_surjective_pairMap_zero (s := s) hs
  have hnsE := not_surjective_pairMap_two (s := s) hs
  set SC : Set (Fin n) :=
    Set.range (fun l : Fin 2 => π ((pairMap (Fin.last (s + 1)) 0) l).succ) with hSC
  set SE : Set (Fin n) :=
    Set.range (fun l : Fin 2 =>
      π ((pairMap (Fin.last (s + 1)) (⟨2, by omega⟩ : Fin (s + 2))) l).succ) with hSE
  rw [block_range_eq hp2 hBs hyB hK hκ (Or.inl hF)
    (pairMap (Fin.last (s + 1)) (0 : Fin (s + 2))) pairMap_last_zero_injective hnsC,
    ← hSC] at hx
  have h1 : (MulAut.conj g) x ∈ (ggBlockComm Bs eta SC).map
      (MulAut.conj g).toMonoidHom := Subgroup.mem_map_of_mem _ hx
  rw [ggBlockComm_map_conj hg hgη] at h1
  have h2 := Subgroup.mem_map_of_mem (f := (MulAut.conj w).toMonoidHom) h1
  rw [ggBlockComm_map_conj hw hwη, hSC, swap_swap_pi_image_planes hs, ← hSE] at h2
  rw [block_range_eq hp2 hBs hyB hK hκ (Or.inl hF)
    (pairMap (Fin.last (s + 1)) (⟨2, by omega⟩ : Fin (s + 2)))
    (pairMap_last_two_injective hs) hnsE, ← hSE]
  exact h2

private theorem spEmbed_last_range {F : Type} [Field F] {s : ℕ} :
    (spEmbed (K := F) (fun _ : Fin 1 => Fin.last (s + 1)) last_injective).range =
      (longBlock F (s + 2) (Fin.last (s + 1))).range := by
  have hcomp : ((spEmbed (K := F) (fun _ : Fin 1 => Fin.last (s + 1)) last_injective).comp
        (longBlock F 1 0)) = longBlock F (s + 2) (Fin.last (s + 1)) := by
    refine MonoidHom.ext fun A => ?_
    rw [MonoidHom.comp_apply, spEmbed_longBlock]
  calc (spEmbed (K := F) (fun _ : Fin 1 => Fin.last (s + 1)) last_injective).range
      = (((spEmbed (K := F) (fun _ : Fin 1 => Fin.last (s + 1)) last_injective).comp
          (longBlock F 1 0)).range) := by
        rw [MonoidHom.range_comp, MonoidHom.range_eq_top.2 longBlock_surjective_one,
          Subgroup.map_top]
    _ = (longBlock F (s + 2) (Fin.last (s + 1))).range := by rw [hcomp]

private theorem block_succ_map_conj [Finite G] {p n s : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    {F : Type} [Field F] [Finite F] [CharP F 2] (hs : 2 ≤ s)
    {Bs K : Subgroup G} {y : G}
    (hBs : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs)
    (hyB : y ∈ Bs) (hK : CFSG.Open.IsComponentOf K (Subgroup.centralizer ({y} : Set G)))
    {eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p))} {π : Fin (s + 3) ≃ Fin n}
    {κ : StatedSp (s + 2) F →* G} {ζ : Multiplicative (ZMod p) →* SL(2, F)}
    (hκ : GGSecFiveBPermSpPlaneFrame Bs K eta π κ ζ)
    {g : G} (hg : g ∈ Subgroup.normalizer (Bs : Set G))
    (hgη : MulAut.congr eta (ggConjAut Bs hg) = SpCoord.permAut (Equiv.swap (π 0) (π 1))) :
    (κ.comp (spEmbed Fin.succ (Fin.succ_injective (s + 1)))).range.map
        (MulAut.conj g).toMonoidHom =
      (κ.comp (spEmbed Fin.succ (Fin.succ_injective (s + 1)))).range := by
  rw [block_range_eq hp2 hBs hyB hK hκ (Or.inr (by omega)) (Fin.succ : Fin (s + 1) → Fin (s + 2))
    (Fin.succ_injective (s + 1)) (not_surjective_succ (s := s))]
  rw [ggBlockComm_map_conj hg hgη, swap_pi_image_range_succ]

private theorem block_long_map_conj [Finite G] {p n s : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    {F : Type} [Field F] [Finite F] [CharP F 2] (hF : 4 ≤ Nat.card F) (hs : 2 ≤ s)
    {Bs K : Subgroup G} {y : G}
    (hBs : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs)
    (hyB : y ∈ Bs) (hK : CFSG.Open.IsComponentOf K (Subgroup.centralizer ({y} : Set G)))
    {eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p))} {π : Fin (s + 3) ≃ Fin n}
    {κ : StatedSp (s + 2) F →* G} {ζ : Multiplicative (ZMod p) →* SL(2, F)}
    (hκ : GGSecFiveBPermSpPlaneFrame Bs K eta π κ ζ)
    {g : G} (hg : g ∈ Subgroup.normalizer (Bs : Set G))
    (hgη : MulAut.congr eta (ggConjAut Bs hg) = SpCoord.permAut (Equiv.swap (π 0) (π 1))) :
    (κ.comp (longBlock F (s + 2) (Fin.last (s + 1)))).range.map
        (MulAut.conj g).toMonoidHom =
      (κ.comp (longBlock F (s + 2) (Fin.last (s + 1)))).range := by
  have hlong_eq : (κ.comp (longBlock F (s + 2) (Fin.last (s + 1)))).range =
      (κ.comp (spEmbed (fun _ : Fin 1 => Fin.last (s + 1)) last_injective)).range := by
    rw [MonoidHom.range_comp, MonoidHom.range_comp, spEmbed_last_range]
  rw [hlong_eq]
  rw [block_range_eq hp2 hBs hyB hK hκ (Or.inl hF) (fun _ : Fin 1 => Fin.last (s + 1))
    last_injective (not_surjective_last (s := s))]
  rw [ggBlockComm_map_conj hg hgη, swap_pi_image_range_last hs]

private theorem mem_second_block {F : Type} [Field F] {s : ℕ}
    (κ : StatedSp (s + 2) F →* G) (g : G) {κ₂ : StatedSp (s + 2) F →* G}
    (hκ₂ : κ₂ = (MulAut.conj g).toMonoidHom.comp (κ.comp (spEmbed (finRotate (s + 2))
      (finRotate (s + 2)).injective)))
    {b : G} (hb : b ∈ (κ₂.comp (spEmbed (Fin.natAdd s : Fin 2 → Fin (s + 2))
      (Fin.natAdd_injective 2 s))).range) :
    ∃ x ∈ (κ.comp (spEmbed (pairMap (Fin.last (s + 1)) (0 : Fin (s + 2)))
      pairMap_last_zero_injective)).range, (MulAut.conj g) x = b := by
  have hB : (κ₂.comp (spEmbed (Fin.natAdd s : Fin 2 → Fin (s + 2))
        (Fin.natAdd_injective 2 s))).range =
      (κ.comp (spEmbed (pairMap (Fin.last (s + 1)) (0 : Fin (s + 2)))
        pairMap_last_zero_injective)).range.map (MulAut.conj g).toMonoidHom := by
    rw [hκ₂, range_conj_comp (MulAut.conj g).toMonoidHom κ (spEmbed (finRotate (s + 2))
        (finRotate (s + 2)).injective) (spEmbed (Fin.natAdd s) (Fin.natAdd_injective 2 s)),
      spEmbed_rot_comp_natAdd, MonoidHom.range_comp]
  rw [hB] at hb
  exact Subgroup.mem_map.mp hb

private theorem commute_blocks_of_charts {F : Type} [Field F] {s : ℕ} (hs : 2 ≤ s)
    {κ : StatedSp (s + 2) F →* G} {g w : G}
    (h01 : ∀ a ∈ (κ.comp (spEmbed (Fin.castLE (Nat.le_add_left 2 s) : Fin 2 → Fin (s + 2))
        (Fin.castLE_injective _))).range,
      (MulAut.conj w) a ∈ (κ.comp (spEmbed (Fin.castLE (Nat.le_add_left 2 s) :
        Fin 2 → Fin (s + 2)) (Fin.castLE_injective _))).range)
    (hlast : ∀ x ∈ (κ.comp (spEmbed (pairMap (Fin.last (s + 1)) (0 : Fin (s + 2)))
        pairMap_last_zero_injective)).range,
      (MulAut.conj w) ((MulAut.conj g) x) ∈ (κ.comp (spEmbed
        (pairMap (Fin.last (s + 1)) (⟨2, by omega⟩ : Fin (s + 2)))
        (pairMap_last_two_injective hs))).range)
    {κ₂ : StatedSp (s + 2) F →* G}
    (hκ₂ : κ₂ = (MulAut.conj g).toMonoidHom.comp (κ.comp (spEmbed (finRotate (s + 2))
      (finRotate (s + 2)).injective))) :
    ∀ a ∈ (κ.comp (spEmbed (Fin.castLE (Nat.le_add_left 2 s) : Fin 2 → Fin (s + 2))
        (Fin.castLE_injective _))).range,
      ∀ b ∈ (κ₂.comp (spEmbed (Fin.natAdd s : Fin 2 → Fin (s + 2))
        (Fin.natAdd_injective 2 s))).range, a * b = b * a := by
  intro a ha b hb
  obtain ⟨x, hx, rfl⟩ := mem_second_block κ g hκ₂ hb
  have hwa := h01 a ha
  have hwb := hlast x hx
  obtain ⟨u, hu⟩ := MonoidHom.mem_range.mp hwa
  obtain ⟨v, hv⟩ := MonoidHom.mem_range.mp hwb
  have hcomm : Commute ((MulAut.conj w) a) ((MulAut.conj w) ((MulAut.conj g) x)) := by
    have h1 : Commute (spEmbed (Fin.castLE (Nat.le_add_left 2 s) :
        Fin 2 → Fin (s + 2)) (Fin.castLE_injective _) u)
        (spEmbed (pairMap (Fin.last (s + 1)) (⟨2, by omega⟩ : Fin (s + 2)))
          (pairMap_last_two_injective hs) v) :=
      commute_spEmbed_of_disjoint (Fin.castLE_injective _) (pairMap_last_two_injective hs)
        (disjoint_castLE_pairMap_two hs) u v
    have h2 := h1.map κ
    have hu' : κ (spEmbed (Fin.castLE (Nat.le_add_left 2 s) : Fin 2 → Fin (s + 2))
        (Fin.castLE_injective _) u) = (MulAut.conj w) a := hu
    have hv' : κ (spEmbed (pairMap (Fin.last (s + 1)) (⟨2, by omega⟩ : Fin (s + 2)))
        (pairMap_last_two_injective hs) v) = (MulAut.conj w) ((MulAut.conj g) x) := hv
    rwa [hu', hv'] at h2
  have hconj : Commute a ((MulAut.conj g) x) := by
    simp only [Commute, MulAut.conj_apply] at hcomm ⊢
    have h2 := congrArg (fun z => w⁻¹ * z * w) hcomm
    calc a * (g * x * g⁻¹) =
          w⁻¹ * (w * a * w⁻¹ * (w * (g * x * g⁻¹) * w⁻¹)) * w := by group
      _ = w⁻¹ * (w * (g * x * g⁻¹) * w⁻¹ * (w * a * w⁻¹)) * w := h2
      _ = (g * x * g⁻¹) * a := by group
  exact hconj

open CFSG.SeitzReduction.SymplecticPilot (spBlock planeCoords_singleton
  range_sumMap_eq_planeCoords)

private theorem spBlock_eq_range_spEmbed_of_range {F : Type} [Field F] {m l : ℕ}
    {σ : Fin l → Fin m} (hσ : Function.Injective σ) {N : Finset (Fin m)}
    (hN : Set.range σ = N) : spBlock F N = (spEmbed (K := F) σ hσ).range := by
  rw [range_spEmbed, range_sumMap_eq_planeCoords hN, spBlock]

private theorem range_pairMap {m : ℕ} (a b : Fin m) :
    Set.range (pairMap a b) = ((({a, b} : Finset (Fin m))) : Set (Fin m)) := by
  rw [set_range_fin_two, pairMap_zero, pairMap_one, Finset.coe_pair]

private theorem map_spBlock_last {F : Type} [Field F] {s : ℕ} (κ : StatedSp (s + 2) F →* G) :
    (spBlock F {Fin.last (s + 1)}).map κ =
      (κ.comp (longBlock F (s + 2) (Fin.last (s + 1)))).range := by
  rw [MonoidHom.range_comp, spBlock, planeCoords_singleton,
    CFSG.ClassicalInvolution.Models.SymplecticPairs.range_longBlock]

private theorem map_spBlock_zero_one {F : Type} [Field F] {s : ℕ}
    (κ : StatedSp (s + 2) F →* G) :
    (spBlock F {0, 1}).map κ = (κ.comp (spEmbed (Fin.castLE (Nat.le_add_left 2 s) :
      Fin 2 → Fin (s + 2)) (Fin.castLE_injective _))).range := by
  have h : Set.range (Fin.castLE (Nat.le_add_left 2 s) : Fin 2 → Fin (s + 2)) =
      ((({0, 1} : Finset (Fin (s + 2)))) : Set (Fin (s + 2))) := by
    rw [set_range_fin_two, Finset.coe_pair]
    congr 2
  rw [MonoidHom.range_comp, spBlock_eq_range_spEmbed_of_range (Fin.castLE_injective _) h]

private theorem map_spBlock_last_zero {F : Type} [Field F] {s : ℕ}
    (κ : StatedSp (s + 2) F →* G) :
    (spBlock F {Fin.last (s + 1), 0}).map κ =
      (κ.comp (spEmbed (pairMap (Fin.last (s + 1)) (0 : Fin (s + 2)))
        pairMap_last_zero_injective)).range := by
  rw [MonoidHom.range_comp,
    spBlock_eq_range_spEmbed_of_range pairMap_last_zero_injective (range_pairMap _ _)]

private theorem map_spBlock_last_two {F : Type} [Field F] {s : ℕ} (hs : 2 ≤ s)
    (κ : StatedSp (s + 2) F →* G) :
    (spBlock F {Fin.last (s + 1), ⟨2, by omega⟩}).map κ =
      (κ.comp (spEmbed (pairMap (Fin.last (s + 1)) (⟨2, by omega⟩ : Fin (s + 2)))
        (pairMap_last_two_injective hs))).range := by
  rw [MonoidHom.range_comp,
    spBlock_eq_range_spEmbed_of_range (pairMap_last_two_injective hs) (range_pairMap _ _)]

theorem ggSecFiveBPermZeta_overlap_of_swap_of_blocks [Finite G] {p n s : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) {F : Type} [Field F] [Finite F] [CharP F 2] (hs : 2 ≤ s)
    {Bs K : Subgroup G} {y : G}
    (hBs : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs)
    (hyB : y ∈ Bs) (hK : CFSG.Open.IsComponentOf K (Subgroup.centralizer ({y} : Set G)))
    {eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p))} {π : Fin (s + 3) ≃ Fin n}
    {κ : StatedSp (s + 2) F →* G} {ζ : Multiplicative (ZMod p) →* SL(2, F)}
    (hκ : GGSecFiveBPermSpPlaneFrame Bs K eta π κ ζ)
    {g w : G} (hg : g ∈ Subgroup.normalizer (Bs : Set G))
    (hgη : MulAut.congr eta (ggConjAut Bs hg) = SpCoord.permAut (Equiv.swap (π 0) (π 1)))
    (hlong : ((spBlock F {Fin.last (s + 1)}).map κ).map (MulAut.conj g).toMonoidHom =
      (spBlock F {Fin.last (s + 1)}).map κ)
    (h01 : ((spBlock F {0, 1}).map κ).map (MulAut.conj w).toMonoidHom ≤
      (spBlock F {0, 1}).map κ)
    (hlast : (((spBlock F {Fin.last (s + 1), 0}).map κ).map (MulAut.conj g).toMonoidHom).map
        (MulAut.conj w).toMonoidHom ≤ (spBlock F {Fin.last (s + 1), ⟨2, by omega⟩}).map κ) :
    ∃ κ₂ : StatedSp (s + 2) F →* G, Function.Injective κ₂ ∧
      κ₂.range = K.map (MulAut.conj g).toMonoidHom ∧
      (κ.comp (spEmbed Fin.succ (Fin.succ_injective (s + 1)))).range =
        (κ₂.comp (spEmbed Fin.castSucc (Fin.castSucc_injective (s + 1)))).range ∧
      (κ.comp (longBlock F (s + 2) (Fin.last (s + 1)))).range =
        (κ₂.comp (longBlock F (s + 2) (Fin.last s).castSucc)).range ∧
      ∀ a ∈ (κ.comp (spEmbed (Fin.castLE (Nat.le_add_left 2 s) : Fin 2 → Fin (s + 2))
          (Fin.castLE_injective _))).range,
        ∀ b ∈ (κ₂.comp (spEmbed (Fin.natAdd s : Fin 2 → Fin (s + 2))
          (Fin.natAdd_injective 2 s))).range, a * b = b * a := by
  have hκinj : Function.Injective κ := hκ.1
  have hκrange : κ.range = K := hκ.2.1
  rw [map_spBlock_last] at hlong
  rw [map_spBlock_zero_one] at h01
  rw [map_spBlock_last_zero, map_spBlock_last_two hs] at hlast
  let κ₂ : StatedSp (s + 2) F →* G :=
    (MulAut.conj g).toMonoidHom.comp (κ.comp (spEmbed (finRotate (s + 2))
      (finRotate (s + 2)).injective))
  have hκ₂ : κ₂ = (MulAut.conj g).toMonoidHom.comp (κ.comp (spEmbed (finRotate (s + 2))
      (finRotate (s + 2)).injective)) := rfl
  refine ⟨κ₂, ?_, ?_, ?_, ?_, ?_⟩
  · exact (MulAut.conj g).injective.comp
      (hκinj.comp (spEmbed_injective (finRotate (s + 2)).injective))
  · rw [hκ₂, MonoidHom.range_comp, MonoidHom.range_comp,
      spEmbed_range_perm (finRotate (s + 2)), Subgroup.map_top, hκrange]
  · rw [hκ₂, range_conj_comp (MulAut.conj g).toMonoidHom κ (spEmbed (finRotate (s + 2))
      (finRotate (s + 2)).injective) (spEmbed Fin.castSucc (Fin.castSucc_injective (s + 1))),
      spEmbed_rot_comp_castSucc, ← MonoidHom.range_comp]
    exact (block_succ_map_conj hp2 hs hBs hyB hK hκ hg hgη).symm
  · rw [hκ₂, range_conj_comp (MulAut.conj g).toMonoidHom κ (spEmbed (finRotate (s + 2))
      (finRotate (s + 2)).injective) (longBlock F (s + 2) (Fin.last s).castSucc),
      spEmbed_rot_comp_longBlock, ← MonoidHom.range_comp]
    exact hlong.symm
  · exact commute_blocks_of_charts hs (fun a ha => h01 (Subgroup.mem_map_of_mem _ ha))
      (fun x hx => hlast (Subgroup.mem_map_of_mem _ (Subgroup.mem_map_of_mem _ hx))) hκ₂

theorem ggSecFiveBPermZeta_overlap_of_swap [Finite G] {p n s : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    {F : Type} [Field F] [Finite F] [CharP F 2] (hF : 4 ≤ Nat.card F) (hs : 2 ≤ s)
    {Bs K : Subgroup G} {y : G}
    (hBs : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs)
    (hyB : y ∈ Bs) (hK : CFSG.Open.IsComponentOf K (Subgroup.centralizer ({y} : Set G)))
    {eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p))} {π : Fin (s + 3) ≃ Fin n}
    {κ : StatedSp (s + 2) F →* G} {ζ : Multiplicative (ZMod p) →* SL(2, F)}
    (hκ : GGSecFiveBPermSpPlaneFrame Bs K eta π κ ζ)
    {g w : G} (hg : g ∈ Subgroup.normalizer (Bs : Set G))
    (hgη : MulAut.congr eta (ggConjAut Bs hg) = SpCoord.permAut (Equiv.swap (π 0) (π 1)))
    (hw : w ∈ Subgroup.normalizer (Bs : Set G))
    (hwη : MulAut.congr eta (ggConjAut Bs hw) = SpCoord.permAut (Equiv.swap (π 0) (π 3))) :
    ∃ κ₂ : StatedSp (s + 2) F →* G, Function.Injective κ₂ ∧
      κ₂.range = K.map (MulAut.conj g).toMonoidHom ∧
      (κ.comp (spEmbed Fin.succ (Fin.succ_injective (s + 1)))).range =
        (κ₂.comp (spEmbed Fin.castSucc (Fin.castSucc_injective (s + 1)))).range ∧
      (κ.comp (longBlock F (s + 2) (Fin.last (s + 1)))).range =
        (κ₂.comp (longBlock F (s + 2) (Fin.last s).castSucc)).range ∧
      ∀ a ∈ (κ.comp (spEmbed (Fin.castLE (Nat.le_add_left 2 s) : Fin 2 → Fin (s + 2))
          (Fin.castLE_injective _))).range,
        ∀ b ∈ (κ₂.comp (spEmbed (Fin.natAdd s : Fin 2 → Fin (s + 2))
          (Fin.natAdd_injective 2 s))).range, a * b = b * a := by
  refine ggSecFiveBPermZeta_overlap_of_swap_of_blocks (w := w) hp2 hs hBs hyB hK hκ hg hgη
    ?_ ?_ ?_
  · rw [map_spBlock_last]
    exact block_long_map_conj hp2 hF hs hBs hyB hK hκ hg hgη
  · rw [map_spBlock_zero_one]
    rintro _ ⟨a, ha, rfl⟩
    exact conj_w_mem_block_zero_one hp2 hF hs hBs hyB hK hκ hw hwη ha
  · rw [map_spBlock_last_zero, map_spBlock_last_two hs]
    rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    exact conj_w_mem_block_last_two hp2 hF hs hBs hyB hK hκ hg hgη hw hwη hx

private theorem swap_image_planes_of_forall_ne {n s : ℕ} (π : Fin (s + 3) ≃ Fin n)
    {a b : Fin (s + 3)} {N : Set (Fin (s + 2))} (ha : ∀ m ∈ N, m.succ ≠ a)
    (hb : ∀ m ∈ N, m.succ ≠ b) :
    (Equiv.swap (π a) (π b)) '' ((fun m => π m.succ) '' N) = (fun m => π m.succ) '' N := by
  rw [Set.image_image]
  exact Set.image_congr fun m hm =>
    Equiv.swap_apply_of_ne_of_ne (π.injective.ne (ha m hm)) (π.injective.ne (hb m hm))

private theorem three_eq_succ_two {s : ℕ} (hs : 2 ≤ s) :
    (3 : Fin (s + 3)) = (⟨2, by omega⟩ : Fin (s + 2)).succ := by
  ext
  simp only [Fin.val_succ]
  rw [Fin.coe_ofNat_eq_mod, Nat.mod_eq_of_lt (by omega)]

private theorem one_eq_succ_zero {s : ℕ} : (1 : Fin (s + 3)) = (0 : Fin (s + 2)).succ :=
  Fin.succ_zero_eq_one.symm

private theorem image_planes_pair {n s : ℕ} (π : Fin (s + 3) ≃ Fin n) (a b : Fin (s + 2)) :
    (fun m => π m.succ) '' ((({a, b} : Finset (Fin (s + 2)))) : Set (Fin (s + 2))) =
      {π a.succ, π b.succ} := by
  rw [Finset.coe_pair, Set.image_insert_eq, Set.image_singleton]

private theorem image_planes_triple {n s : ℕ} (π : Fin (s + 3) ≃ Fin n) (a b c : Fin (s + 2)) :
    (fun m => π m.succ) '' ((({a, b, c} : Finset (Fin (s + 2)))) : Set (Fin (s + 2))) =
      {π a.succ, π b.succ, π c.succ} := by
  rw [Finset.coe_insert, Finset.coe_pair, Set.image_insert_eq, Set.image_insert_eq,
    Set.image_singleton]

private theorem swap_swap_image_last_zero {n s : ℕ} (hs : 2 ≤ s) (π : Fin (s + 3) ≃ Fin n) :
    (Equiv.swap (π 0) (π 3)) '' ((Equiv.swap (π 0) (π 1)) ''
        ((fun m => π m.succ) '' ((({Fin.last (s + 1), 0} : Finset (Fin (s + 2)))) :
          Set (Fin (s + 2))))) =
      (fun m => π m.succ) '' ((({Fin.last (s + 1), ⟨2, by omega⟩} : Finset (Fin (s + 2)))) :
        Set (Fin (s + 2))) ∧
    (Equiv.swap (π 0) (π 3)) '' ((Equiv.swap (π 0) (π 1)) ''
        ((fun m => π m.succ) '' ((({Fin.last (s + 1), 0, 1} : Finset (Fin (s + 2)))) :
          Set (Fin (s + 2))))) =
      (fun m => π m.succ) '' ((({Fin.last (s + 1), ⟨2, by omega⟩, 1} : Finset (Fin (s + 2)))) :
        Set (Fin (s + 2))) := by
  have h3 := three_eq_succ_two hs
  have h1 : (1 : Fin (s + 3)) = (0 : Fin (s + 2)).succ := one_eq_succ_zero
  have hL0 : (Fin.last (s + 1)).succ ≠ 0 := Fin.succ_ne_zero _
  have hL1 : (Fin.last (s + 1)).succ ≠ 1 := by
    rw [h1]; exact fun h => absurd (Fin.succ_injective _ h) (by simp [Fin.ext_iff])
  have hL3 : (Fin.last (s + 1)).succ ≠ 3 := by
    rw [h3]; intro h; have := congrArg Fin.val (Fin.succ_injective _ h); simp at this; omega
  have h2_0 : ((1 : Fin (s + 2))).succ ≠ 0 := Fin.succ_ne_zero _
  have h2_1 : ((1 : Fin (s + 2))).succ ≠ 1 := by
    rw [h1]; exact fun h => absurd (Fin.succ_injective _ h) (by simp)
  have h2_3 : ((1 : Fin (s + 2))).succ ≠ 3 := by
    rw [h3]; intro h; have := congrArg Fin.val (Fin.succ_injective _ h)
    rw [Fin.val_one] at this; simp at this
  have eL : (Equiv.swap (π 0) (π 3)) ((Equiv.swap (π 0) (π 1)) (π (Fin.last (s + 1)).succ)) =
      π (Fin.last (s + 1)).succ := by
    rw [Equiv.swap_apply_of_ne_of_ne (π.injective.ne hL0) (π.injective.ne hL1),
      Equiv.swap_apply_of_ne_of_ne (π.injective.ne hL0) (π.injective.ne hL3)]
  have e0 : (Equiv.swap (π 0) (π 3)) ((Equiv.swap (π 0) (π 1)) (π (0 : Fin (s + 2)).succ)) =
      π (⟨2, by omega⟩ : Fin (s + 2)).succ := by
    rw [← h1, Equiv.swap_apply_right, Equiv.swap_apply_left, h3]
  have e1 : (Equiv.swap (π 0) (π 3)) ((Equiv.swap (π 0) (π 1)) (π (1 : Fin (s + 2)).succ)) =
      π (1 : Fin (s + 2)).succ := by
    rw [Equiv.swap_apply_of_ne_of_ne (π.injective.ne h2_0) (π.injective.ne h2_1),
      Equiv.swap_apply_of_ne_of_ne (π.injective.ne h2_0) (π.injective.ne h2_3)]
  constructor
  · simp only [image_planes_pair, Set.image_insert_eq, Set.image_singleton]
    rw [eL, e0]
  · simp only [image_planes_triple, Set.image_insert_eq, Set.image_singleton]
    rw [eL, e0, e1]

private theorem card_triple {m : ℕ} {a b c : Fin m} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    ({a, b, c} : Finset (Fin m)).card = 3 :=
  Finset.card_eq_three.mpr ⟨a, b, c, hab, hac, hbc, rfl⟩

private theorem blocks_of_family [Finite G] {p n s : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    {F : Type} [Field F] [Finite F] [CharP F 2] (hs : 2 ≤ s)
    {Bs K : Subgroup G} {y : G}
    (hBs : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs)
    (hyB : y ∈ Bs) (hK : CFSG.Open.IsComponentOf K (Subgroup.centralizer ({y} : Set G)))
    {eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p))} {π : Fin (s + 3) ≃ Fin n}
    {κ : StatedSp (s + 2) F →* G} {ζ : Multiplicative (ZMod p) →* SL(2, F)}
    (hκ : GGSecFiveBPermSpPlaneFrame Bs K eta π κ ζ)
    (X : Set (Fin n) → Set (Fin n) → Subgroup G)
    (hX : ∀ I N : Finset (Fin (s + 2)), I ⊆ N → N.card = 3 → I.Nonempty → I.card ≤ 2 →
      ggBlockComm Bs eta ((fun m => π m.succ) '' (N : Set (Fin (s + 2)))) = (spBlock F N).map κ →
      X ((fun m => π m.succ) '' (I : Set (Fin (s + 2))))
        ((fun m => π m.succ) '' (N : Set (Fin (s + 2)))) = (spBlock F I).map κ)
    (hXc : ∀ (c : G) (hc : c ∈ Subgroup.normalizer (Bs : Set G)) (τ : Equiv.Perm (Fin n)),
      MulAut.congr eta (ggConjAut Bs hc) = SpCoord.permAut τ →
      ∀ S T, (X S T).map (MulAut.conj c).toMonoidHom = X (τ '' S) (τ '' T))
    {g w : G} (hg : g ∈ Subgroup.normalizer (Bs : Set G))
    (hgη : MulAut.congr eta (ggConjAut Bs hg) = SpCoord.permAut (Equiv.swap (π 0) (π 1)))
    (hw : w ∈ Subgroup.normalizer (Bs : Set G))
    (hwη : MulAut.congr eta (ggConjAut Bs hw) = SpCoord.permAut (Equiv.swap (π 0) (π 3))) :
    ((spBlock F {Fin.last (s + 1)}).map κ).map (MulAut.conj g).toMonoidHom =
        (spBlock F {Fin.last (s + 1)}).map κ ∧
      ((spBlock F {0, 1}).map κ).map (MulAut.conj w).toMonoidHom ≤ (spBlock F {0, 1}).map κ ∧
      (((spBlock F {Fin.last (s + 1), 0}).map κ).map (MulAut.conj g).toMonoidHom).map
        (MulAut.conj w).toMonoidHom ≤ (spBlock F {Fin.last (s + 1), ⟨2, by omega⟩}).map κ := by
  set L : Fin (s + 2) := Fin.last (s + 1) with hL
  have hval : ∀ {a b : Fin (s + 2)}, a.val ≠ b.val → a ≠ b := fun h e => h (congrArg Fin.val e)
  have hL0 : L ≠ 0 := hval (by simp [hL])
  have hL1 : L ≠ 1 := hval (by simp [hL]; omega)
  have hL2 : L ≠ ⟨2, by omega⟩ := hval (by simp [hL]; omega)
  have h01 : (0 : Fin (s + 2)) ≠ 1 := hval (by simp)
  have h12 : (1 : Fin (s + 2)) ≠ ⟨2, by omega⟩ := hval (by simp)
  have h03 : (0 : Fin (s + 2)) ≠ ⟨3, by omega⟩ := hval (by simp)
  have h13 : (1 : Fin (s + 2)) ≠ ⟨3, by omega⟩ := hval (by simp)
  have hnu : ∀ N : Finset (Fin (s + 2)), N.card = 3 → N ≠ Finset.univ := by
    intro N hN h
    have := congrArg Finset.card h
    rw [hN, Finset.card_univ, Fintype.card_fin] at this
    omega
  have hCT : ∀ N : Finset (Fin (s + 2)), N.card = 3 →
      ggBlockComm Bs eta ((fun m => π m.succ) '' (N : Set (Fin (s + 2)))) =
        (spBlock F N).map κ := fun N hN =>
    hκ.ggBlockComm_image_succ_eq_map_spBlock_of_or hp2 hBs hyB hK (Or.inr hN.ge)
      (Finset.card_pos.mp (by omega)) (hnu N hN)
  have hfixg : ∀ N : Set (Fin (s + 2)), (0 : Fin (s + 2)) ∉ N →
      (Equiv.swap (π 0) (π 1)) '' ((fun m => π m.succ) '' N) = (fun m => π m.succ) '' N := by
    intro N h0
    refine swap_image_planes_of_forall_ne π (fun m _ => Fin.succ_ne_zero m) fun m hm hm1 => ?_
    rw [one_eq_succ_zero] at hm1
    exact h0 (Fin.succ_injective _ hm1 ▸ hm)
  have hfixw : ∀ N : Set (Fin (s + 2)), (⟨2, by omega⟩ : Fin (s + 2)) ∉ N →
      (Equiv.swap (π 0) (π 3)) '' ((fun m => π m.succ) '' N) = (fun m => π m.succ) '' N := by
    intro N h2
    refine swap_image_planes_of_forall_ne π (fun m _ => Fin.succ_ne_zero m) fun m hm hm3 => ?_
    rw [three_eq_succ_two hs] at hm3
    exact h2 (Fin.succ_injective _ hm3 ▸ hm)
  refine ⟨?_, ?_, ?_⟩
  ·
    have hN : ({L, 1, ⟨2, by omega⟩} : Finset (Fin (s + 2))).card = 3 := card_triple hL1 hL2 h12
    have hI := hX {L} {L, 1, ⟨2, by omega⟩} (by simp) hN (Finset.singleton_nonempty _) (by simp)
      (hCT _ hN)
    rw [← hI, hXc g hg _ hgη, hfixg _ (by simp [hL0.symm]), hfixg _ (by simp [hL0.symm, h01])]
  ·
    have hN : ({0, 1, ⟨3, by omega⟩} : Finset (Fin (s + 2))).card = 3 := card_triple h01 h03 h13
    have hI := hX {0, 1} {0, 1, ⟨3, by omega⟩} (by intro x; simp; tauto) hN
      (Finset.insert_nonempty _ _) Finset.card_le_two (hCT _ hN)
    rw [← hI, hXc w hw _ hwη, hfixw _ (by simp [Fin.ext_iff]), hfixw _ (by simp [Fin.ext_iff])]
  ·
    have hN : ({L, 0, 1} : Finset (Fin (s + 2))).card = 3 := card_triple hL0 hL1 h01
    have hN' : ({L, ⟨2, by omega⟩, 1} : Finset (Fin (s + 2))).card = 3 :=
      card_triple hL2 hL1 h12.symm
    have hI := hX {L, 0} {L, 0, 1} (by intro x; simp; tauto) hN (Finset.insert_nonempty _ _)
      Finset.card_le_two (hCT _ hN)
    have hI' := hX {L, ⟨2, by omega⟩} {L, ⟨2, by omega⟩, 1} (by intro x; simp; tauto) hN'
      (Finset.insert_nonempty _ _) Finset.card_le_two (hCT _ hN')
    obtain ⟨hS, hT⟩ := swap_swap_image_last_zero hs π
    rw [← hI, hXc g hg _ hgη, hXc w hw _ hwη, hS, hT, hI']

theorem ggSecFiveBPermZeta_overlap_of_swap_of_family [Finite G] {p n s : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) {F : Type} [Field F] [Finite F] [CharP F 2] (hs : 2 ≤ s)
    {Bs K : Subgroup G} {y : G}
    (hBs : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs)
    (hyB : y ∈ Bs) (hK : CFSG.Open.IsComponentOf K (Subgroup.centralizer ({y} : Set G)))
    {eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p))} {π : Fin (s + 3) ≃ Fin n}
    {κ : StatedSp (s + 2) F →* G} {ζ : Multiplicative (ZMod p) →* SL(2, F)}
    (hκ : GGSecFiveBPermSpPlaneFrame Bs K eta π κ ζ)
    (X : Set (Fin n) → Set (Fin n) → Subgroup G)
    (hX : ∀ I N : Finset (Fin (s + 2)), I ⊆ N → N.card = 3 → I.Nonempty → I.card ≤ 2 →
      ggBlockComm Bs eta ((fun m => π m.succ) '' (N : Set (Fin (s + 2)))) = (spBlock F N).map κ →
      X ((fun m => π m.succ) '' (I : Set (Fin (s + 2))))
        ((fun m => π m.succ) '' (N : Set (Fin (s + 2)))) = (spBlock F I).map κ)
    (hXc : ∀ (c : G) (hc : c ∈ Subgroup.normalizer (Bs : Set G)) (τ : Equiv.Perm (Fin n)),
      MulAut.congr eta (ggConjAut Bs hc) = SpCoord.permAut τ →
      ∀ S T, (X S T).map (MulAut.conj c).toMonoidHom = X (τ '' S) (τ '' T))
    {g w : G} (hg : g ∈ Subgroup.normalizer (Bs : Set G))
    (hgη : MulAut.congr eta (ggConjAut Bs hg) = SpCoord.permAut (Equiv.swap (π 0) (π 1)))
    (hw : w ∈ Subgroup.normalizer (Bs : Set G))
    (hwη : MulAut.congr eta (ggConjAut Bs hw) = SpCoord.permAut (Equiv.swap (π 0) (π 3))) :
    ∃ κ₂ : StatedSp (s + 2) F →* G, Function.Injective κ₂ ∧
      κ₂.range = K.map (MulAut.conj g).toMonoidHom ∧
      (κ.comp (spEmbed Fin.succ (Fin.succ_injective (s + 1)))).range =
        (κ₂.comp (spEmbed Fin.castSucc (Fin.castSucc_injective (s + 1)))).range ∧
      (κ.comp (longBlock F (s + 2) (Fin.last (s + 1)))).range =
        (κ₂.comp (longBlock F (s + 2) (Fin.last s).castSucc)).range ∧
      ∀ a ∈ (κ.comp (spEmbed (Fin.castLE (Nat.le_add_left 2 s) : Fin 2 → Fin (s + 2))
          (Fin.castLE_injective _))).range,
        ∀ b ∈ (κ₂.comp (spEmbed (Fin.natAdd s : Fin 2 → Fin (s + 2))
          (Fin.natAdd_injective 2 s))).range, a * b = b * a := by
  obtain ⟨hlong, h01, hlast⟩ :=
    blocks_of_family hp2 hs hBs hyB hK hκ X hX hXc hg hgη hw hwη
  exact ggSecFiveBPermZeta_overlap_of_swap_of_blocks hp2 hs hBs hyB hK hκ hg hgη hlong h01 hlast

theorem ggSecFiveBPermZeta_overlap_of_swap_charTwo [Finite G] {p n s : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) {F : Type} [Field F] [Finite F] [CharP F 2] (hs : 2 ≤ s)
    {Bs K : Subgroup G} {y : G}
    (hBs : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs)
    (hyB : y ∈ Bs) (hK : CFSG.Open.IsComponentOf K (Subgroup.centralizer ({y} : Set G)))
    {eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p))} {π : Fin (s + 3) ≃ Fin n}
    {κ : StatedSp (s + 2) F →* G} {ζ : Multiplicative (ZMod p) →* SL(2, F)}
    (hκ : GGSecFiveBPermSpPlaneFrame Bs K eta π κ ζ)
    {g w : G} (hg : g ∈ Subgroup.normalizer (Bs : Set G))
    (hgη : MulAut.congr eta (ggConjAut Bs hg) = SpCoord.permAut (Equiv.swap (π 0) (π 1)))
    (hw : w ∈ Subgroup.normalizer (Bs : Set G))
    (hwη : MulAut.congr eta (ggConjAut Bs hw) = SpCoord.permAut (Equiv.swap (π 0) (π 3))) :
    ∃ κ₂ : StatedSp (s + 2) F →* G, Function.Injective κ₂ ∧
      κ₂.range = K.map (MulAut.conj g).toMonoidHom ∧
      (κ.comp (spEmbed Fin.succ (Fin.succ_injective (s + 1)))).range =
        (κ₂.comp (spEmbed Fin.castSucc (Fin.castSucc_injective (s + 1)))).range ∧
      (κ.comp (longBlock F (s + 2) (Fin.last (s + 1)))).range =
        (κ₂.comp (longBlock F (s + 2) (Fin.last s).castSucc)).range ∧
      ∀ a ∈ (κ.comp (spEmbed (Fin.castLE (Nat.le_add_left 2 s) : Fin 2 → Fin (s + 2))
          (Fin.castLE_injective _))).range,
        ∀ b ∈ (κ₂.comp (spEmbed (Fin.natAdd s : Fin 2 → Fin (s + 2))
          (Fin.natAdd_injective 2 s))).range, a * b = b * a :=
  ggSecFiveBPermZeta_overlap_of_swap_of_family hp2 hs hBs hyB hK hκ (ggQTwoSmallBlock Bs eta)
    (fun _ _ hIN _ _ hI hY => hκ.ggQTwoSmallBlock_eq_map_spBlock hp2 hIN hI hY)
    (fun _ hc _ hτ S T => ggQTwoSmallBlock_map_conj hc hτ S T) hg hgη hw hwη

end CFSG.StandardType

end
