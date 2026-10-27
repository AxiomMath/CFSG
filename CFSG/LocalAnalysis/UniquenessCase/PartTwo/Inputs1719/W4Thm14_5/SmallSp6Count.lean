module

public import CFSG.ClassicalInvolution.Models.SymplecticPairs.Complement
public import CFSG.LieType.Universal.SymplecticExtras.TorusWeyl
import TauCeti.LinearAlgebra.Eigenspace.JointEigenvector.Basic

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_5

open Module

section Abstract

variable {G N : Type*} [Group G] [Group N] {k V : Type*} [Field k] [AddCommGroup V]
  [Module k V] [FiniteDimensional k V]

theorem card_le_finrank_range_sub_one [IsSimpleGroup N] (ρ : Representation k G V)
    (ι : N →* G) {A : Type*} (τ : A → G) (hτ : ∀ a g, τ a * ι g = ι g * τ a) {z : N}
    (hz : z ≠ 1) {m : ℕ} (b : Fin m → A → k) (hb : Function.Injective b) (v : Fin m → V)
    (hv : ∀ j a, ρ (τ a) (v j) = b j a • v j) (hmove : ∀ j, ∃ g, ρ (ι g) (v j) ≠ v j) :
    m ≤ finrank k (LinearMap.range (ρ (ι z) - 1)) := by
  classical
  set E : (A → k) → Submodule k V := fun χ => ⨅ a, Module.End.eigenspace (ρ (τ a)) (χ a)
    with hE
  have hmemE : ∀ χ w, w ∈ E χ ↔ ∀ a, ρ (τ a) w = χ a • w := by
    intro χ w
    simp only [hE, Submodule.mem_iInf, Module.End.mem_eigenspace_iff]
  have hρmul : ∀ g g' w, ρ (g * g') w = ρ g (ρ g' w) := fun g g' w => by
    rw [map_mul, Module.End.mul_apply]
  have hstab : ∀ χ g w, w ∈ E χ → ρ (ι g) w ∈ E χ := by
    intro χ g w hw
    rw [hmemE] at hw ⊢
    intro a
    rw [← hρmul, hτ, hρmul, hw a, map_smul]
  have hne : ∀ j, ∃ w ∈ E (b j), ρ (ι z) w - w ≠ 0 := by
    intro j
    by_contra hcon
    push Not at hcon
    let H : Subgroup N :=
      { carrier := {g | ∀ w ∈ E (b j), ρ (ι g) w = w}
        one_mem' := fun w _ => by rw [map_one, map_one, Module.End.one_apply]
        mul_mem' := fun {g g'} hg hg' w hw => by
          rw [map_mul, hρmul, hg' w hw, hg w hw]
        inv_mem' := fun {g} hg w hw => by
          have h1 := hg _ (hstab (b j) g⁻¹ w hw)
          rw [← hρmul, ← map_mul, mul_inv_cancel, map_one, map_one, Module.End.one_apply] at h1
          exact h1.symm }
    have hHn : H.Normal := ⟨fun g hg h w hw => by
      have h1 : ρ (ι h⁻¹) w ∈ E (b j) := hstab _ _ _ hw
      change ρ (ι (h * g * h⁻¹)) w = w
      simp only [map_mul, Module.End.mul_apply]
      rw [hg _ h1, ← Module.End.mul_apply, ← map_mul, ← map_mul, mul_inv_cancel, map_one, map_one,
        Module.End.one_apply]⟩
    have hzH : z ∈ H := fun w hw => sub_eq_zero.mp (hcon w hw)
    have := hHn
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal H with h | h
    · exact hz ((Subgroup.mem_bot).mp (h ▸ hzH))
    · obtain ⟨g, hg⟩ := hmove j
      have hgH : g ∈ H := h ▸ Subgroup.mem_top g
      exact hg (hgH (v j) ((hmemE _ _).mpr (hv j)))
  choose w hwE hw using hne
  have hind := (TauCeti.iSupIndep_iInf_eigenspace (fun a => ρ (τ a))).comp hb
  have hli : LinearIndependent k (fun j => ρ (ι z) (w j) - w j) :=
    iSupIndep.linearIndependent _ hind
      (fun j => Submodule.sub_mem _ (hstab _ _ _ (hwE j)) (hwE j)) hw
  have hli' : LinearIndependent k (fun j => (⟨ρ (ι z) (w j) - w j, w j, by
      rw [LinearMap.sub_apply, Module.End.one_apply]⟩ : LinearMap.range (ρ (ι z) - 1))) :=
    LinearIndependent.of_comp (LinearMap.range (ρ (ι z) - 1)).subtype hli
  simpa using hli'.fintype_card_le_finrank

end Abstract

section Levi

open CFSG.LieType.Universal.Symplectic CFSG.LieType.Universal.Symplectic.SpExtras CFSG.Open
  CFSG.ClassicalInvolution.Models.SymplecticPairs

variable {n : ℕ} {K : Type} [Field K]

theorem mat_diagHom (t : Fin n → Kˣ) :
    mat n K (diagHom n K t) =
      Matrix.diagonal (Sum.elim (fun i => (t i : K)) (fun i => (((t i)⁻¹ : Kˣ) : K))) :=
  mat_equiv_diagonal t

theorem diagHom_mulSingle_mem_suppGroup (a : Kˣ) :
    diagHom 3 K (Pi.mulSingle 0 a) ∈ suppGroup (coords (0 : Fin 3)) := by
  change IsSupp (coords 0) (mat 3 K (diagHom 3 K (Pi.mulSingle 0 a)))
  rw [mat_diagHom]
  intro r t hrt
  by_cases hrt' : r = t
  · subst hrt'
    have hr : r ∉ coords (0 : Fin 3) := fun h => hrt ⟨h, h⟩
    rw [Matrix.diagonal_apply_eq, Matrix.one_apply_eq]
    rcases r with i | i
    · have hi : i ≠ 0 := fun h => hr (by rw [h]; exact inl_mem_coords 0)
      simp [Pi.mulSingle_apply, hi]
    · have hi : i ≠ 0 := fun h => hr (mem_coords.2 (Or.inr (by rw [h])))
      simp [Pi.mulSingle_apply, hi]
  · rw [Matrix.diagonal_apply_ne _ hrt', Matrix.one_apply_ne hrt']

theorem spEmbed_succ_mem_suppGroup (g : StatedSp 2 K) :
    spEmbed Fin.succ (Fin.succ_injective 2) g ∈ suppGroup (coords (0 : Fin 3))ᶜ := by
  have h := isSupp_spEmbed (K := K) (Fin.succ_injective 2) g
  rw [← range_succAbove (0 : Fin 3), Fin.succAbove_zero]
  exact h

theorem diagHom_mulSingle_commute_spEmbed (a : Kˣ) (g : StatedSp 2 K) :
    diagHom 3 K (Pi.mulSingle 0 a) * spEmbed Fin.succ (Fin.succ_injective 2) g =
      spEmbed Fin.succ (Fin.succ_injective 2) g * diagHom 3 K (Pi.mulSingle 0 a) :=
  commute_suppGroup_compl (diagHom_mulSingle_mem_suppGroup a) (spEmbed_succ_mem_suppGroup g)

theorem diagHom_cons_one (t : Fin 2 → Kˣ) :
    diagHom 3 K (Fin.cons 1 t : Fin 3 → Kˣ) =
      spEmbed Fin.succ (Fin.succ_injective 2) (diagHom 2 K t) := by
  classical
  apply mat_injective
  rw [mat_spEmbed, mat_diagHom, mat_diagHom]
  have hinj : Function.Injective (Sum.map Fin.succ Fin.succ : Fin 2 ⊕ Fin 2 → Fin 3 ⊕ Fin 3) :=
    Sum.map_injective.2 ⟨Fin.succ_injective 2, Fin.succ_injective 2⟩
  ext r c
  by_cases h : r ∈ Set.range (Sum.map Fin.succ Fin.succ) ∧
      c ∈ Set.range (Sum.map Fin.succ Fin.succ)
  · obtain ⟨⟨x, rfl⟩, ⟨y, rfl⟩⟩ := h
    rw [spEmbedMat_apply_image (Fin.succ_injective 2)]
    by_cases hxy : x = y
    · subst hxy
      rw [Matrix.diagonal_apply_eq, Matrix.diagonal_apply_eq]
      rcases x with i | i <;> simp
    · rw [Matrix.diagonal_apply_ne _ hxy, Matrix.diagonal_apply_ne _ (hinj.ne hxy)]
  · rw [spEmbedMat_apply_of_not_mem _ h]
    by_cases hrc : r = c
    · subst hrc
      have hr : r ∉ Set.range (Sum.map Fin.succ Fin.succ) := fun h' => h ⟨h', h'⟩
      rw [Matrix.diagonal_apply_eq, Matrix.one_apply_eq]
      rcases r with i | i
      · have hi : i = 0 := by
          by_contra hi
          exact hr ⟨Sum.inl (i.pred hi), by simp⟩
        subst hi
        simp
      · have hi : i = 0 := by
          by_contra hi
          exact hr ⟨Sum.inr (i.pred hi), by simp⟩
        subst hi
        simp
    · rw [Matrix.diagonal_apply_ne _ hrc, Matrix.one_apply_ne hrc]

end Levi

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_5
