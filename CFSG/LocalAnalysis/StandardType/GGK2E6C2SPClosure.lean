module

public import CFSG.LocalAnalysis.StandardType.GGK2E6C2SPFromMonomial
public import CFSG.LocalAnalysis.StandardType.GGResExactTwoOrthSmall

public section

namespace CFSG.StandardType

open Module CFSG.StandardType.HdRo7C

private lemma c2sp_sq_pm (x : ZMod 3) (h : x = 1 ∨ x = -1) : x * x = 1 := by
  rcases h with h | h <;> rw [h] <;> decide

@[expose] noncomputable def c2spSubgroup {V : Type} [AddCommGroup V] [Module (ZMod 3) V] {n : ℕ}
    (b : Module.Basis (Fin (n + 1)) (ZMod 3) V) : Subgroup (V ≃ₗ[ZMod 3] V) where
  carrier := {s | C2SP 3 b s}
  mul_mem' := by
    intro s t hs ht
    obtain ⟨σ, c, hσ0, hc0, hc, hs⟩ := hs
    obtain ⟨τ, d, hτ0, hd0, hd, ht⟩ := ht
    refine ⟨σ * τ, fun i => d i * c (τ i), ?_, ?_, ?_, ?_⟩
    · rw [Equiv.Perm.mul_apply, hτ0, hσ0]
    · show d 0 * c (τ 0) = 1
      rw [hd0, hτ0, hc0, mul_one]
    · intro i
      change d i * c (τ i) = 1 ∨ d i * c (τ i) = -1
      rcases hd i with h | h <;> rcases hc (τ i) with h' | h' <;> rw [h, h'] <;> decide
    · intro i
      calc (s * t) (b i) = s (t (b i)) := LinearEquiv.mul_apply s t (b i)
        _ = s (d i • b (τ i)) := by rw [ht i]
        _ = d i • s (b (τ i)) := by rw [map_smul]
        _ = d i • (c (τ i) • b (σ (τ i))) := by rw [hs (τ i)]
        _ = (d i * c (τ i)) • b ((σ * τ) i) := by rw [← mul_smul, Equiv.Perm.mul_apply]
  one_mem' := ⟨1, fun _ => 1, rfl, rfl, fun _ => Or.inl rfl, fun i => by simp⟩
  inv_mem' := by
    intro s hs
    obtain ⟨σ, c, hσ0, hc0, hc, hs⟩ := hs
    have hσinv0 : σ.symm 0 = 0 := (Equiv.symm_apply_eq σ).mpr hσ0.symm
    refine ⟨σ.symm, fun j => c (σ.symm j), hσinv0, ?_, ?_, ?_⟩
    · change c (σ.symm 0) = 1
      rw [hσinv0]
      exact hc0
    · intro j
      exact hc (σ.symm j)
    · intro j
      change s.symm (b j) = c (σ.symm j) • b (σ.symm j)
      rw [LinearEquiv.symm_apply_eq]
      calc b j = (c (σ.symm j) * c (σ.symm j)) • b j := by
              rw [c2sp_sq_pm (c (σ.symm j)) (hc (σ.symm j)), one_smul]
        _ = c (σ.symm j) • (c (σ.symm j) • b (σ (σ.symm j))) := by
              rw [← mul_smul, Equiv.apply_symm_apply σ j]
        _ = c (σ.symm j) • s (b (σ.symm j)) := by rw [hs]
        _ = s (c (σ.symm j) • b (σ.symm j)) := by rw [map_smul]

private def addEquivAdditiveMultiplicative (V : Type) [AddCommGroup V] :
    Additive (Multiplicative V) ≃+ V where
  toFun x := x
  invFun x := x
  left_inv x := rfl
  right_inv x := rfl
  map_add' x y := rfl

private noncomputable def c2spLinToMulAut (V : Type) [AddCommGroup V] [Module (ZMod 3) V] :
    (V ≃ₗ[ZMod 3] V) →* MulAut (Multiplicative V) where
  toFun e := AddEquiv.toMultiplicative e.toAddEquiv
  map_one' := by ext x; rfl
  map_mul' e f := by ext x; rfl

private lemma ggLin_c2spLinToMulAut {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    (e : V ≃ₗ[ZMod 3] V) :
    ggLin (p := 3) (addEquivAdditiveMultiplicative V)
        (c2spLinToMulAut V e) = e := by
  ext v
  change e v = e v
  rfl

private lemma c2spLinToMulAut_injective {V : Type} [AddCommGroup V] [Module (ZMod 3) V] :
    Function.Injective (c2spLinToMulAut V) := by
  intro e f h
  ext v
  have hv := congrArg (fun g : MulAut (Multiplicative V) =>
    (g (Multiplicative.ofAdd v) : Multiplicative V)) h
  simpa [c2spLinToMulAut] using hv

theorem card_c2spSubgroup_le {V : Type} [AddCommGroup V] [Module (ZMod 3) V] {n : ℕ}
    (b : Module.Basis (Fin (n + 1)) (ZMod 3) V) :
    Nat.card (c2spSubgroup b) ≤ 2 ^ n * n.factorial := by
  classical
  let f := c2spLinToMulAut V
  let A : Subgroup (MulAut (Multiplicative V)) := (c2spSubgroup b).map f
  have hA : ∀ a ∈ A, C2SP 3 b (ggLin (p := 3)
      (addEquivAdditiveMultiplicative V) a) := by
    intro a ha
    obtain ⟨e, he, rfl⟩ := Subgroup.mem_map.mp ha
    rw [ggLin_c2spLinToMulAut]
    exact he
  have hle := ggResX2Aux_card_le_of_c2sp (p := 3) rfl b
    (addEquivAdditiveMultiplicative V) A hA
  have hcard : Nat.card A = Nat.card (c2spSubgroup b) :=
    Subgroup.card_map_of_injective (c2spLinToMulAut_injective)
  rw [← hcard]
  exact hle

theorem c2spSubgroup_eq_of_closure_card {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    [Finite V] {E : Type} [Group E] {b : Module.Basis (Fin 6) (ZMod 3) V}
    (ι : Additive E ≃+ V) {A : Subgroup (MulAut E)} {g : Fin 5 → MulAut E}
    (hclos : A = Subgroup.closure (Set.range g))
    (hg : ∀ i, C2SP 3 b (ggLin (p := 3) ι (g i)))
    (hcardA : Nat.card A = 3840) :
    A.map (ggLin (p := 3) ι) = c2spSubgroup b := by
  classical
  have hle : A.map (ggLin (p := 3) ι) ≤ c2spSubgroup b := by
    rw [hclos, MonoidHom.map_closure]
    rw [Subgroup.closure_le]
    rintro x ⟨i, hi, hx⟩
    obtain ⟨j, rfl⟩ := hi
    rw [← hx]
    exact hg j
  have hcardImg : Nat.card (A.map (ggLin (p := 3) ι)) = Nat.card A :=
    Subgroup.card_map_of_injective (ggLin_injective ι)
  haveI : Finite (V ≃ₗ[ZMod 3] V) := by
    refine Finite.of_injective (fun e : V ≃ₗ[ZMod 3] V => (e : V → V)) ?_
    intro e f h
    ext v
    exact congrFun h v
  haveI : Finite (c2spSubgroup b) := Subtype.finite
  have hC := card_c2spSubgroup_le (n := 5) b
  norm_num at hC
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  rw [hcardImg, hcardA]
  exact hC

end CFSG.StandardType

end
