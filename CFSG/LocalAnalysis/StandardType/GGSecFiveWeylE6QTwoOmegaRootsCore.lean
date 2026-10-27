module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylE6QTwoOmegaRoots
public import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylE6QTwoOmegaRootsCoreAux

public section

namespace CFSG.StandardType.E6QTwo

open Module CFSG.Assembly

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [Finite V]
  {h : Fin 6 → V} {α : Fin 6 → Dual (ZMod 3) V} {B : LinearMap.BilinForm (ZMod 3) V}

theorem rootRefl_mem_of_six_le (hP : ∀ i j, α i (h j) = (CartanMatrix.E 6 i j : ZMod 3))
    (hV : Nat.card V = 3 ^ 5) (hB : ∀ i v, B (h i) v = α i v) (hα : ∀ i, α i (h i) = 2)
    {K : Subgroup (V ≃ₗ[ZMod 3] V)} {x y : V} (hx : B x x = 1) (hyx : ∀ a : ZMod 3, y ≠ a • x)
    (h6 : 6 ≤ Set.ncard {r : V ≃ₗ[ZMod 3] V | r ∈ K ∧ ∃ v : V, ∃ hv : B v v = 2,
      B v x = 0 ∧ B v y = 0 ∧ r = rootRefl (B := B) v hv}) :
    12 ≤ Set.ncard {v : V | B v v = 2 ∧ B v x = 0 ∧ B v y = 0} ∧
      ∀ (v : V) (hv : B v v = 2), B v x = 0 → B v y = 0 → rootRefl (B := B) v hv ∈ K := by
  classical
  let Φ : Set V := {v : V | B v v = 2 ∧ B v x = 0 ∧ B v y = 0}
  let RS : Set (V ≃ₗ[ZMod 3] V) := {r : V ≃ₗ[ZMod 3] V | r ∈ K ∧ ∃ v : V, ∃ hv : B v v = 2,
      B v x = 0 ∧ B v y = 0 ∧ r = rootRefl (B := B) v hv}
  have h6' : 6 ≤ Set.ncard RS := h6
  let vf : RS → V := fun r => Classical.choose r.2.2
  have hvf_spec : ∀ r : RS, ∃ hv : B (vf r) (vf r) = 2,
      B (vf r) x = 0 ∧ B (vf r) y = 0 ∧
        (r : V ≃ₗ[ZMod 3] V) = rootRefl (B := B) (vf r) hv :=
    fun r => Classical.choose_spec r.2.2
  let hvf : ∀ r : RS, B (vf r) (vf r) = 2 := fun r => Classical.choose (hvf_spec r)
  have hvf_props : ∀ r : RS, B (vf r) x = 0 ∧ B (vf r) y = 0 ∧
      (r : V ≃ₗ[ZMod 3] V) = rootRefl (B := B) (vf r) (hvf r) :=
    fun r => Classical.choose_spec (hvf_spec r)
  let f : RS × Fin 2 → V := fun p => Fin.cases (vf p.1) (fun _ => -vf p.1) p.2
  let T : Set V := f '' Set.univ
  have hTΦ : T ⊆ Φ := by
    rintro z ⟨p, -, rfl⟩
    rcases p with ⟨r, i⟩
    fin_cases i
    · change B (vf r) (vf r) = 2 ∧ B (vf r) x = 0 ∧ B (vf r) y = 0
      exact ⟨hvf r, (hvf_props r).1, (hvf_props r).2.1⟩
    · change B (-vf r) (-vf r) = 2 ∧ B (-vf r) x = 0 ∧ B (-vf r) y = 0
      refine ⟨?_, ?_, ?_⟩
      · rw [LinearMap.BilinForm.neg_left, LinearMap.BilinForm.neg_right, neg_neg]
        exact hvf r
      · rw [LinearMap.BilinForm.neg_left]
        exact neg_eq_zero.mpr (hvf_props r).1
      · rw [LinearMap.BilinForm.neg_left]
        exact neg_eq_zero.mpr (hvf_props r).2.1
  have hf_inj : Function.Injective f := by
    rintro ⟨r, i⟩ ⟨s, j⟩ hij
    fin_cases i <;> fin_cases j
    · change vf r = vf s at hij
      have hrs : r = s := by
        refine Subtype.ext ?_
        rw [(hvf_props r).2.2, (hvf_props s).2.2]
        exact (rootRefl_eq_iff (hvf r) (hvf s)).mpr (Or.inl hij)
      exact Prod.ext hrs rfl
    · change vf r = -vf s at hij
      have hrs : r = s := by
        refine Subtype.ext ?_
        rw [(hvf_props r).2.2, (hvf_props s).2.2]
        exact (rootRefl_eq_iff (hvf r) (hvf s)).mpr (Or.inr hij)
      rw [hrs] at hij
      exact absurd hij (root_ne_neg_self (hvf s))
    · change -vf r = vf s at hij
      have hrs : r = s := by
        refine Subtype.ext ?_
        rw [(hvf_props r).2.2, (hvf_props s).2.2]
        exact (rootRefl_eq_iff (hvf r) (hvf s)).mpr (Or.inr (by simpa using congrArg Neg.neg hij))
      rw [hrs] at hij
      exact absurd hij.symm (root_ne_neg_self (hvf s))
    · change -vf r = -vf s at hij
      have hrs : r = s := by
        refine Subtype.ext ?_
        rw [(hvf_props r).2.2, (hvf_props s).2.2]
        exact (rootRefl_eq_iff (hvf r) (hvf s)).mpr (Or.inl (neg_inj.mp hij))
      exact Prod.ext hrs rfl
  have hTcard : T.ncard = Nat.card (RS × Fin 2) := by
    have h := Set.ncard_image_of_injective (f := f) Set.univ hf_inj
    rwa [Set.ncard_univ] at h
  have hT12 : 12 ≤ T.ncard := by
    rw [hTcard, Nat.card_prod, Nat.card_fin, Nat.card_coe_set_eq]
    have := h6'
    nlinarith
  have h12Φ : 12 ≤ Φ.ncard := hT12.trans (Set.ncard_mono hTΦ)
  obtain ⟨hΦ12, -, -, -⟩ := phiD_facts hP hV hB hα hx hyx h12Φ
  have hT12' : T.ncard = 12 := le_antisymm (hΦ12 ▸ Set.ncard_mono hTΦ) hT12
  have hTΦeq : T = Φ :=
    Set.eq_of_subset_of_ncard_le hTΦ (by rw [hT12', hΦ12]) (Set.toFinite Φ)
  refine ⟨h12Φ, ?_⟩
  intro v hv hvx hvy
  have hvΦ : v ∈ Φ := ⟨hv, hvx, hvy⟩
  rw [← hTΦeq] at hvΦ
  obtain ⟨p, -, hp⟩ := hvΦ
  rcases p with ⟨r, i⟩
  have hfv : B (f (r, i)) (f (r, i)) = 2 := by rw [hp]; exact hv
  have h1 : rootRefl (B := B) v hv = rootRefl (B := B) (f (r, i)) hfv :=
    (rootRefl_eq_iff hv hfv).mpr (Or.inl hp.symm)
  have hroot : rootRefl (B := B) (f (r, i)) hfv = (r : V ≃ₗ[ZMod 3] V) := by
    fin_cases i
    · change B (vf r) (vf r) = 2 at hfv
      change rootRefl (vf r) hfv = (r : V ≃ₗ[ZMod 3] V)
      exact ((hvf_props r).2.2).symm
    · change B (-vf r) (-vf r) = 2 at hfv
      change rootRefl (-vf r) hfv = (r : V ≃ₗ[ZMod 3] V)
      rw [rootRefl_neg]
      exact ((hvf_props r).2.2).symm
  rw [h1, hroot]
  exact r.2.1

theorem rootRefl_mem_of_dich (hP : ∀ i j, α i (h j) = (CartanMatrix.E 6 i j : ZMod 3))
    (hV : Nat.card V = 3 ^ 5) (hB : ∀ i v, B (h i) v = α i v) (hα : ∀ i, α i (h i) = 2)
    {K : Subgroup (V ≃ₗ[ZMod 3] V)} {x y : V} (hx : B x x = 1) (hy : B y y = 2)
    (hyx : ∀ a : ZMod 3, y ≠ a • x)
    (h12 : 12 ≤ Set.ncard {v : V | B v v = 2 ∧ B v x = 0 ∧ B v y = 0})
    (hK : ∀ (v : V) (hv : B v v = 2), B v x = 0 → B v y = 0 → rootRefl (B := B) v hv ∈ K)
    (hN : ∀ ψ ∈ e6Weyl hα, ψ y = y → (∀ a ∈ K, ψ * a * ψ⁻¹ ∈ K) ∨
      ∀ a ∈ K, ∀ b ∈ K, a * (ψ * b * ψ⁻¹) = ψ * b * ψ⁻¹ * a) :
    ∀ (w : V) (hw : B w w = 2), B w y = 0 → rootRefl (B := B) w hw ∈ K := by
  classical
  let Φ : Set V := {v : V | B v v = 2 ∧ B v x = 0 ∧ B v y = 0}
  have hnorm : ∀ ψ ∈ e6Weyl hα, ψ y = y → ∀ a ∈ K, ψ * a * ψ⁻¹ ∈ K := by
    intro ψ hψ hyψ a ha
    rcases hN ψ hψ hyψ with h1 | h2
    · exact h1 a ha
    · exact (rootRefl_noComm hP hV hB hα hx hyx h12 hK hψ h2).elim
  let S : Set (V ≃ₗ[ZMod 3] V) := {r : V ≃ₗ[ZMod 3] V | ∃ u : V, ∃ hu : B u u = 2,
    B u y = 0 ∧ r = rootRefl (B := B) u hu}
  let C : Subgroup (V ≃ₗ[ZMod 3] V) := Subgroup.closure S
  have hCe6 : C ≤ e6Weyl hα := by
    change Subgroup.closure S ≤ e6Weyl hα
    rw [Subgroup.closure_le]
    rintro r ⟨u, hu, huy, rfl⟩
    exact rootRefl_mem_e6Weyl hP hV hB hα hu
  have hCnorm : C ≤ Subgroup.normalizer K := by
    change Subgroup.closure S ≤ Subgroup.normalizer K
    rw [Subgroup.closure_le]
    rintro r ⟨u, hu, huy, rfl⟩
    refine (Subgroup.mem_set_normalizer_iff (S := (K : Set (V ≃ₗ[ZMod 3] V)))).mpr ?_
    intro h
    constructor
    · intro hh
      exact hnorm (rootRefl (B := B) u hu) (rootRefl_mem_e6Weyl hP hV hB hα hu)
        ((rootRefl_fix_iff hu y).mpr huy) h hh
    · intro hh
      have h1 := hnorm (rootRefl (B := B) u hu) (rootRefl_mem_e6Weyl hP hV hB hα hu)
        ((rootRefl_fix_iff hu y).mpr huy) (rootRefl (B := B) u hu * h * (rootRefl (B := B) u hu)⁻¹) hh
      have hrr : rootRefl (B := B) u hu * rootRefl (B := B) u hu = 1 := by
        apply LinearEquiv.ext
        intro z
        rw [LinearEquiv.mul_apply]
        exact rootRefl_involutive u hu z
      have hinv : (rootRefl (B := B) u hu)⁻¹ = rootRefl (B := B) u hu :=
        inv_eq_of_mul_eq_one_right hrr
      have heq : rootRefl (B := B) u hu *
          (rootRefl (B := B) u hu * h * (rootRefl (B := B) u hu)⁻¹) *
          (rootRefl (B := B) u hu)⁻¹ = h := by
        rw [hinv]
        calc rootRefl (B := B) u hu * (rootRefl (B := B) u hu * h * rootRefl (B := B) u hu) *
              rootRefl (B := B) u hu
            = (rootRefl (B := B) u hu * rootRefl (B := B) u hu) * h *
              (rootRefl (B := B) u hu * rootRefl (B := B) u hu) := by group
          _ = h := by rw [hrr]; simp
      rwa [heq] at h1
  have h12' : 12 ≤ Φ.ncard := h12
  have hΦne : Φ.Nonempty := Set.nonempty_of_ncard_ne_zero (by omega)
  obtain ⟨v₀, hv₀⟩ := hΦne
  intro w hw hwy
  obtain ⟨g, hgC, hgw⟩ := exists_mem_closure_rootRefl_apply_eq hP hV hB hα hy hv₀.1 hw hv₀.2.2 hwy
  have hgW : g ∈ e6Weyl hα := hCe6 hgC
  have hgnorm : g ∈ Subgroup.normalizer K := hCnorm hgC
  have hgiso : ∀ a b : V, B (g a) (g b) = B a b := fun a b =>
    bilinForm_apply_e6Weyl hP hV hB hα hgW a b
  have hconj := rootRefl_conj_iso (B := B) (g := g) hgiso hv₀.1
  have hKv₀ : rootRefl (B := B) v₀ hv₀.1 ∈ K := hK v₀ hv₀.1 hv₀.2.1 hv₀.2.2
  have hconjK : g * rootRefl (B := B) v₀ hv₀.1 * g⁻¹ ∈ K :=
    (Subgroup.mem_normalizer_iff.mp hgnorm (rootRefl (B := B) v₀ hv₀.1)).mp hKv₀
  rw [hconj] at hconjK
  have hgv : B (g v₀) (g v₀) = 2 := by rw [hgiso, hv₀.1]
  have hroot_eq : rootRefl (B := B) (g v₀) hgv = rootRefl (B := B) w hw :=
    (rootRefl_eq_iff hgv hw).mpr (Or.inl hgw)
  rwa [hroot_eq] at hconjK

end CFSG.StandardType.E6QTwo

end
