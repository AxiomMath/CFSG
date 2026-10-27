module

public import CFSG.RankThree.PartOne.K159W.CoverWeyl
public import CFSG.RankThree.PartOne.K159.CoverPSL

public section

namespace CFSG.RankThree.PartOne.K159W

open Matrix CFSG.RankThree.Classical2 CFSG.RankThree.Classical CFSG.SectionRank.OddCover
  CFSG.RankThree.CentralCover CFSG.RankThree.PartOne.K159
open scoped MatrixGroups

@[expose] def c3 : Equiv.Perm (Fin 5) := Equiv.swap 0 1 * Equiv.swap 1 2

@[expose] def c5 : Equiv.Perm (Fin 5) := finRotate 5

theorem c3_sign : Equiv.Perm.sign c3 = 1 := by decide
theorem c5_sign : Equiv.Perm.sign c5 = 1 := by decide
theorem c3_pow : c3 ^ 3 = 1 := by decide
theorem c5_pow : c5 ^ 5 = 1 := by decide

@[expose] def conjVec (σ : Equiv.Perm (Fin 5)) (a : Fin 4 → ZMod 5) : Fin 4 → ZMod 5 :=
  fun i => torusExp a (σ.symm i.castSucc)

theorem c3_ne : ¬ ∀ i i' : Fin 5, torusExp (conjVec c3 (Pi.single 0 1) - Pi.single 0 1) i =
    torusExp (conjVec c3 (Pi.single 0 1) - Pi.single 0 1) i' := by decide +kernel

theorem c5_ne : ¬ ∀ i i' : Fin 5, torusExp (conjVec c5 (Pi.single 0 1) - Pi.single 0 1) i =
    torusExp (conjVec c5 (Pi.single 0 1) - Pi.single 0 1) i' := by decide +kernel

theorem torusExp_conjVec (σ : Equiv.Perm (Fin 5)) (a : Fin 4 → ZMod 5) :
    torusExp (conjVec σ a) = torusExp a ∘ σ.symm := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · rw [torusExp_last]
    have h2 : ∑ i : Fin 5, torusExp a (σ.symm i) = 0 := by
      rw [Equiv.sum_comp σ.symm (torusExp a)]
      exact sum_torusExp a
    rw [Fin.sum_univ_castSucc] at h2
    simp only [Function.comp_apply, conjVec]
    linear_combination -h2
  · rw [torusExp_castSucc]
    rfl

theorem torusEntries_comp_perm {k : Type} [Field k] (ζ : kˣ) (hζ : ζ ^ 5 = 1)
    (σ : Equiv.Perm (Fin 5)) (a : Fin 4 → ZMod 5) :
    torusEntries ζ hζ a ∘ σ.symm = torusEntries ζ hζ (conjVec σ a) := by
  funext i
  simp only [torusEntries, Function.comp_apply, torusExp_conjVec]

section Perm

variable {k : Type} [Field k]

@[expose] noncomputable def permSL (σ : Equiv.Perm (Fin 5)) (hσ : Equiv.Perm.sign σ = 1) :
    SL(5, k) :=
  ⟨((permGL σ : GL (Fin 5) k) : Matrix (Fin 5) (Fin 5) k), by
    rw [det_permGL, hσ]
    simp⟩

theorem toGL_permSL (σ : Equiv.Perm (Fin 5)) (hσ : Equiv.Perm.sign σ = 1) :
    Matrix.SpecialLinearGroup.toGL (permSL (k := k) σ hσ) = permGL σ := Units.ext rfl

theorem permSL_inv (σ : Equiv.Perm (Fin 5)) (hσ : Equiv.Perm.sign σ = 1)
    (hσ' : Equiv.Perm.sign σ⁻¹ = 1) :
    (permSL (k := k) σ hσ)⁻¹ = permSL σ⁻¹ hσ' := by
  apply Matrix.SpecialLinearGroup.toGL_injective
  rw [map_inv, toGL_permSL, toGL_permSL, map_inv]

theorem permSL_pow (σ : Equiv.Perm (Fin 5)) (hσ : Equiv.Perm.sign σ = 1) {n : ℕ}
    (hn : σ ^ n = 1) : (permSL (k := k) σ hσ) ^ n = 1 := by
  apply Matrix.SpecialLinearGroup.toGL_injective
  rw [map_pow, toGL_permSL, ← map_pow, hn, map_one, map_one]

theorem permSL_conj_torusElem (ζ : kˣ) (hζ : ζ ^ 5 = 1) (σ : Equiv.Perm (Fin 5))
    (hσ : Equiv.Perm.sign σ = 1) (a : Fin 4 → ZMod 5) :
    permSL σ hσ * torusElem ζ hζ a * (permSL σ hσ)⁻¹ = torusElem ζ hζ (conjVec σ a) := by
  apply Matrix.SpecialLinearGroup.toGL_injective
  rw [map_mul, map_mul, map_inv, toGL_permSL, toGL_torusElem, toGL_torusElem,
    permGL_mul_diagHom_mul_inv]
  congr 1
  exact torusEntries_comp_perm ζ hζ σ a

theorem mk_permSL_conj_torusPSL (ζ : kˣ) (hζ : ζ ^ 5 = 1) (σ : Equiv.Perm (Fin 5))
    (hσ : Equiv.Perm.sign σ = 1) (a : Multiplicative (Fin 4 → ZMod 5)) :
    QuotientGroup.mk' (Subgroup.center SL(5, k)) (permSL σ hσ) * torusPSL ζ hζ 4 a *
        (QuotientGroup.mk' (Subgroup.center SL(5, k)) (permSL σ hσ))⁻¹ =
      torusPSL ζ hζ 4 (Multiplicative.ofAdd (conjVec σ (Multiplicative.toAdd a))) := by
  show QuotientGroup.mk' (Subgroup.center SL(5, k)) (permSL σ hσ) *
      QuotientGroup.mk' (Subgroup.center SL(5, k)) (torusElem ζ hζ (Multiplicative.toAdd a)) *
      (QuotientGroup.mk' (Subgroup.center SL(5, k)) (permSL σ hσ))⁻¹ =
    QuotientGroup.mk' (Subgroup.center SL(5, k)) (torusElem ζ hζ (conjVec σ (Multiplicative.toAdd a)))
  rw [← map_inv, ← map_mul, ← map_mul, permSL_conj_torusElem]

theorem mk_permSL_conj_gen_ne {ζ : kˣ} (hζo : orderOf ζ = 5) (hζ : ζ ^ 5 = 1)
    {σ : Equiv.Perm (Fin 5)} (hσ : Equiv.Perm.sign σ = 1)
    (hne : ¬ ∀ i i' : Fin 5, torusExp (conjVec σ (Pi.single 0 1) - Pi.single 0 1) i =
      torusExp (conjVec σ (Pi.single 0 1) - Pi.single 0 1) i') :
    QuotientGroup.mk' (Subgroup.center SL(5, k)) (permSL σ hσ) *
        torusPSL ζ hζ 4 (Multiplicative.ofAdd (Pi.single 0 1)) *
        (QuotientGroup.mk' (Subgroup.center SL(5, k)) (permSL σ hσ))⁻¹ ≠
      torusPSL ζ hζ 4 (Multiplicative.ofAdd (Pi.single 0 1)) := by
  intro h
  rw [mk_permSL_conj_torusPSL, toAdd_ofAdd] at h
  apply hne
  intro i i'
  have hker : Multiplicative.ofAdd (conjVec σ (Pi.single 0 1)) *
      (Multiplicative.ofAdd (Pi.single 0 1 : Fin 4 → ZMod 5))⁻¹ ∈ (torusPSL ζ hζ 4).ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, h, mul_inv_cancel]
  have := torusExp_eq_of_mem_ker hζo hζ hker i i'
  simpa [sub_eq_add_neg] using this

end Perm

section Main

variable {K : Type} [Group K] {k : Type} [Field k]

theorem weylFive_psl [Finite K] {ζ : kˣ} (hζo : orderOf ζ = 5) (hζ : ζ ^ 5 = 1)
    {φ : K →* PSL(5, k)} (hφ : Function.Surjective φ) (hker : φ.ker ≤ Subgroup.center K)
    (hodd : Odd (Nat.card φ.ker)) {z : K} (hz : z ∈ φ.ker) (hz1 : z ≠ 1) (hzp : z ^ 5 = 1) :
    WeylFive K := by
  classical
  have : NeZero 5 := ⟨by norm_num⟩
  obtain ⟨hDp, hF, hDcard⟩ := torusPSL_package (p := 5) (k := k) Nat.prime_five (by norm_num) hζo
    hζ (m := 4) (by norm_num) hφ hker
  set θ := torusPSL ζ hζ 4 with hθ
  set S : Set PSL(5, k) :=
    Set.range fun j : Fin 4 => θ (Multiplicative.ofAdd (Pi.single j 1)) with hS
  have hcl : Subgroup.closure S = θ.range := by
    have h1 : (Subgroup.closure (Set.range fun j : Fin 4 =>
        (Multiplicative.ofAdd (Pi.single j (1 : ZMod 5)) :
          Multiplicative (Fin 4 → ZMod 5)))).map θ = Subgroup.closure S := by
      rw [MonoidHom.map_closure, hS, ← Set.range_comp]
      rfl
    rw [← h1, closure_range_ofAdd_single, ← MonoidHom.range_eq_map]
  have hSp : ∀ s ∈ S, s ^ 5 = 1 := fun s hs => hDp s (by
    rw [← hcl]
    exact Subgroup.subset_closure hs)
  have hSinv : ∀ s ∈ S, ∃ g : PSL(5, k), g * s * g⁻¹ = s⁻¹ := by
    rintro _ ⟨j, rfl⟩
    refine ⟨QuotientGroup.mk' _ (invElem j), ?_⟩
    have h1 : θ (Multiplicative.ofAdd (Pi.single j 1)) =
        QuotientGroup.mk' (Subgroup.center SL(4 + 1, k)) (torusElem ζ hζ (Pi.single j 1)) := rfl
    show QuotientGroup.mk' _ (invElem j) * θ (Multiplicative.ofAdd (Pi.single j 1)) *
      (QuotientGroup.mk' _ (invElem j))⁻¹ = (θ (Multiplicative.ofAdd (Pi.single j 1)))⁻¹
    rw [h1, ← map_inv, ← map_inv, ← map_mul, ← map_mul, invElem_conj ζ hζ j]
  have hF' : ∀ x ∈ (Subgroup.closure S).comap φ, ∀ y ∈ (Subgroup.closure S).comap φ,
      x * y = y * x := by
    rw [hcl]
    exact hF
  have hcard : 5 ^ 3 ≤ Nat.card (Subgroup.closure S) := by
    rw [hcl]
    simpa using hDcard
  have hnorm : ∀ (σ : Equiv.Perm (Fin 5)) (hσ : Equiv.Perm.sign σ = 1),
      ∀ d ∈ Subgroup.closure S,
        QuotientGroup.mk' (Subgroup.center SL(5, k)) (permSL σ hσ) * d *
          (QuotientGroup.mk' (Subgroup.center SL(5, k)) (permSL σ hσ))⁻¹ ∈ Subgroup.closure S := by
    intro σ hσ d hd
    rw [hcl] at hd ⊢
    obtain ⟨a, rfl⟩ := hd
    rw [mk_permSL_conj_torusPSL]
    exact ⟨_, rfl⟩
  have hnorm' : ∀ (σ : Equiv.Perm (Fin 5)) (hσ : Equiv.Perm.sign σ = 1)
      (hσ' : Equiv.Perm.sign σ⁻¹ = 1), ∀ d ∈ Subgroup.closure S,
        (QuotientGroup.mk' (Subgroup.center SL(5, k)) (permSL σ hσ))⁻¹ * d *
          QuotientGroup.mk' (Subgroup.center SL(5, k)) (permSL σ hσ) ∈ Subgroup.closure S := by
    intro σ hσ hσ' d hd
    have := hnorm σ⁻¹ hσ' d hd
    rwa [← permSL_inv σ hσ hσ', map_inv, inv_inv] at this
  have hs₀ : θ (Multiplicative.ofAdd (Pi.single 0 1)) ∈ S := ⟨0, rfl⟩
  have hc3' : Equiv.Perm.sign c3⁻¹ = 1 := by rw [Equiv.Perm.sign_inv, c3_sign]
  have hc5' : Equiv.Perm.sign c5⁻¹ = 1 := by rw [Equiv.Perm.sign_inv, c5_sign]
  refine weylFive_of_cover hφ hker hodd hz hz1 hzp S hSp hSinv hF' hcard
    (w₃ := QuotientGroup.mk' (Subgroup.center SL(5, k)) (permSL c3 c3_sign))
    (hnorm c3 c3_sign) (hnorm' c3 c3_sign hc3')
    (by rw [← map_pow, permSL_pow c3 c3_sign c3_pow, map_one]) hs₀
    (mk_permSL_conj_gen_ne hζo hζ c3_sign c3_ne)
    (w₅ := QuotientGroup.mk' (Subgroup.center SL(5, k)) (permSL c5 c5_sign))
    (hnorm c5 c5_sign) (hnorm' c5 c5_sign hc5')
    (by rw [← map_pow, permSL_pow c5 c5_sign c5_pow, map_one]) hs₀
    (mk_permSL_conj_gen_ne hζo hζ c5_sign c5_ne)

end Main

end CFSG.RankThree.PartOne.K159W
