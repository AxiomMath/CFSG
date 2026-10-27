module

public import CFSG.LocalAnalysis.StandardType.GGTwE6EndNodeThreeCoroot

public section

namespace CFSG.StandardType.TwE6Cube

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.StandardType.TwE6EndNode3

@[expose] def crl (γ : Fin 6 → ℤ) : Fin 6 → ℤ :=
  ![2 * γ 0 - γ 2, 2 * γ 1 - γ 3, 2 * γ 2 - γ 0 - γ 3, 2 * γ 3 - γ 1 - γ 2 - γ 4,
    2 * γ 4 - γ 3 - γ 5, 2 * γ 5 - γ 4]

@[expose] def form6 (g b : Fin 6 → ℤ) : ℤ :=
  g 0 * crl b 0 + g 1 * crl b 1 + g 2 * crl b 2 + g 3 * crl b 3 + g 4 * crl b 4 + g 5 * crl b 5

theorem cartan_sum (γ : Fin 6 → ℤ) (k : Fin 6) :
    ∑ l : Fin 6, Tag.E6.cartan k l * γ l = crl γ k := by
  fin_cases k <;> simp [Fin.sum_univ_six, Tag.cartan, Tag.cartanE, crl] <;> ring

theorem corootVec_eq (γ : Fin 6 → ℤ) : corootVec γ = fun k => ((crl γ k : ℤ) : ZMod 3) :=
  funext fun k => congrArg Int.cast (cartan_sum γ k)

theorem iform_eq (g b : Fin 6 → ℤ) : iform (τ := Tag.E6) g b = form6 g b := by
  have hS : Tag.E6.symmetrizedCartan = Tag.E6.cartan := by
    rw [Tag.symmetrizedCartan, show Tag.E6.symmetrizer = 1 from rfl, Matrix.one_mul]
  have h1 : iform (τ := Tag.E6) g b = ∑ i : Fin 6, g i * crl b i := by
    unfold iform
    rw [hS]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← cartan_sum b i, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [h1, Fin.sum_univ_six]
  rfl

@[expose] def rts : List (Fin 6 → ℤ) := Tag.E6.artifactRoots.map fun r i => r.getD i 0

@[expose] def KerP (v : Fin 6 → ZMod 3) (α : Fin 6 → ℤ) : Prop :=
  ∑ i, v i * (α i : ZMod 3) = 0

@[expose] def kerB (v : Fin 6 → ZMod 3) (α : Fin 6 → ℤ) : Bool :=
  v 0 * (α 0 : ZMod 3) + v 1 * (α 1 : ZMod 3) + v 2 * (α 2 : ZMod 3) + v 3 * (α 3 : ZMod 3) +
    v 4 * (α 4 : ZMod 3) + v 5 * (α 5 : ZMod 3) == 0

theorem kerB_iff (v : Fin 6 → ZMod 3) (α : Fin 6 → ℤ) : kerB v α = true ↔ KerP v α := by
  simp [kerB, KerP, Fin.sum_univ_six]

@[expose] def kerL (v : Fin 6 → ZMod 3) : List (Fin 6 → ℤ) := rts.filter (kerB v)

@[expose] def isCorB (v : Fin 6 → ZMod 3) : Bool :=
  rts.any fun γ => (crl γ 0 : ZMod 3) == v 0 && (crl γ 1 : ZMod 3) == v 1 &&
    (crl γ 2 : ZMod 3) == v 2 && (crl γ 3 : ZMod 3) == v 3 && (crl γ 4 : ZMod 3) == v 4 &&
    (crl γ 5 : ZMod 3) == v 5

@[expose] def zs : List (ZMod 3) := [0, 1, 2]

@[expose] def annB (v : Fin 6 → ZMod 3) (K : List (Fin 6 → ℤ)) : Bool :=
  zs.any fun a => zs.any fun b => zs.any fun c => zs.any fun d => zs.any fun e => zs.any fun f =>
    K.all (kerB ![a, b, c, d, e, f]) &&
      (a != 0 || b != 0 || c != 0 || d != 0 || e != 0 || f != 0) &&
      !(a == v 0 && b == v 1 && c == v 2 && d == v 3 && e == v 4 && f == v 5) &&
      !(a == -v 0 && b == -v 1 && c == -v 2 && d == -v 3 && e == -v 4 && f == -v 5)

@[expose] def splitB (K : List (Fin 6 → ℤ)) : Bool :=
  K.any fun g => K.any (fun b => form6 g b == 0) &&
    (K.filter fun b => form6 g b == 0).all fun b =>
      (K.filter fun d => form6 g d != 0).all fun d => form6 b d == 0

@[expose] def goodB (v : Fin 6 → ZMod 3) : Bool :=
  (v 0 == 0 && v 1 == 0 && v 2 == 0 && v 3 == 0 && v 4 == 0 && v 5 == 0) || isCorB v ||
    (kerL v).length == 40 || splitB (kerL v) || annB v (kerL v)

set_option maxRecDepth 100000 in
theorem all_good : ∀ a b c d e f : ZMod 3, goodB ![a, b, c, d, e, f] = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cor_not_ker : ∀ γ ∈ rts, kerB (fun k => ((crl γ k : ℤ) : ZMod 3)) γ = false := by
  decide +kernel

theorem isCorB_sound {v : Fin 6 → ZMod 3} (h : isCorB v = true) :
    ∃ γ ∈ rts, corootVec γ = v := by
  simp only [isCorB, List.any_eq_true, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨γ, hγ, ⟨⟨⟨⟨⟨h0, h1⟩, h2⟩, h3⟩, h4⟩, h5⟩⟩ := h
  refine ⟨γ, hγ, ?_⟩
  rw [corootVec_eq]
  funext k
  fin_cases k <;> assumption

theorem annB_sound {v : Fin 6 → ZMod 3} {K : List (Fin 6 → ℤ)} (h : annB v K = true) :
    ∃ u : Fin 6 → ZMod 3, u ≠ 0 ∧ u ≠ v ∧ u ≠ -v ∧ ∀ α ∈ K, KerP u α := by
  simp only [annB, List.any_eq_true] at h
  obtain ⟨a, -, b, -, c, -, d, -, e, -, f, -, h⟩ := h
  simp only [Bool.and_eq_true, Bool.not_eq_true', List.all_eq_true, Bool.or_eq_true, bne_iff_ne,
    ne_eq] at h
  obtain ⟨⟨⟨hK, hne⟩, huv⟩, hun⟩ := h
  refine ⟨![a, b, c, d, e, f], ?_, ?_, ?_, fun α hα => (kerB_iff _ _).1 (hK α hα)⟩
  · intro h0
    have h0' := fun i => congrFun h0 i
    rcases hne with ((((ha | hb) | hc) | hd) | he) | hf
    · exact ha (by simpa using h0' 0)
    · exact hb (by simpa using h0' 1)
    · exact hc (by simpa using h0' 2)
    · exact hd (by simpa using h0' 3)
    · exact he (by simpa using h0' 4)
    · exact hf (by simpa using h0' 5)
  · intro h1
    have e0 : a = v 0 := by simpa using congrFun h1 0
    have e1 : b = v 1 := by simpa using congrFun h1 1
    have e2 : c = v 2 := by simpa using congrFun h1 2
    have e3 : d = v 3 := by simpa using congrFun h1 3
    have e4 : e = v 4 := by simpa using congrFun h1 4
    have e5 : f = v 5 := by simpa using congrFun h1 5
    simp [e0, e1, e2, e3, e4, e5] at huv
  · intro h1
    have e0 : a = -v 0 := by simpa using congrFun h1 0
    have e1 : b = -v 1 := by simpa using congrFun h1 1
    have e2 : c = -v 2 := by simpa using congrFun h1 2
    have e3 : d = -v 3 := by simpa using congrFun h1 3
    have e4 : e = -v 4 := by simpa using congrFun h1 4
    have e5 : f = -v 5 := by simpa using congrFun h1 5
    simp [e0, e1, e2, e3, e4, e5] at hun

theorem splitB_sound {K : List (Fin 6 → ℤ)} (h : splitB K = true) :
    ∃ g ∈ K, ∃ b ∈ K, iform (τ := Tag.E6) g b = 0 ∧ ∀ b' ∈ K, ∀ d ∈ K,
      iform (τ := Tag.E6) g b' = 0 → iform (τ := Tag.E6) g d ≠ 0 →
        iform (τ := Tag.E6) b' d = 0 := by
  simp only [splitB, List.any_eq_true, Bool.and_eq_true, List.all_eq_true, List.mem_filter,
    beq_iff_eq, bne_iff_ne, ne_eq, and_imp, iform_eq] at h ⊢
  obtain ⟨g, hg, ⟨b, hb, hgb⟩, hall⟩ := h
  exact ⟨g, hg, b, hb, hgb, fun b' hb' d hd h1 h2 => hall b' hb' h1 d hd h2⟩

theorem dichotomy_rts {v : Fin 6 → ZMod 3} (hv : v ≠ 0) :
    (∃ γ ∈ rts, corootVec γ = v) ∨ (kerL v).length = 40 ∨
    (∃ g ∈ kerL v, ∃ b ∈ kerL v, iform (τ := Tag.E6) g b = 0 ∧ ∀ b' ∈ kerL v, ∀ d ∈ kerL v,
      iform (τ := Tag.E6) g b' = 0 → iform (τ := Tag.E6) g d ≠ 0 →
        iform (τ := Tag.E6) b' d = 0) ∨
    (∃ u : Fin 6 → ZMod 3, u ≠ 0 ∧ u ≠ v ∧ u ≠ -v ∧ ∀ α ∈ kerL v, KerP u α) := by
  have hv' : v = ![v 0, v 1, v 2, v 3, v 4, v 5] := by
    funext i
    fin_cases i <;> rfl
  have h := all_good (v 0) (v 1) (v 2) (v 3) (v 4) (v 5)
  rw [← hv'] at h
  simp only [goodB, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at h
  rcases h with (((h | h) | h) | h) | h
  · obtain ⟨⟨⟨⟨⟨h0, h1⟩, h2⟩, h3⟩, h4⟩, h5⟩ := h
    exact absurd (funext fun i => by fin_cases i <;> assumption) hv
  · exact Or.inl (isCorB_sound h)
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl (splitB_sound h)))
  · exact Or.inr (Or.inr (Or.inr (annB_sound h)))

end CFSG.StandardType.TwE6Cube

end
