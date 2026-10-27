module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylE6QTwoOmegaWeylAux3
public import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylE6QTwoOrbit
public import CFSG.LocalAnalysis.StandardType.GGE6IsoOrbit
public import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylE6QTwoModelAux

public section

namespace CFSG.StandardType.E6QTwo

open Module CFSG.Assembly CFSG.Blueprint.Chevalley

private theorem exists_e6LinearModel' {G : Type} [Group G] [Finite G] {Bs : Subgroup G}
    (hBs : IsElemAbelian 3 Bs) (hcard : Nat.card Bs = 3 ^ 5)
    (hNT : GGNoTransvection 3 Bs) {A : Subgroup (MulAut ↥Bs)}
    (hW : GGWeylOfType 3 CoxeterMatrix.E₆ A)
    (hA : ∀ φ ∈ A, φ ∈ ggInduced ⊤ Bs) (hWcard : Nat.card CoxeterMatrix.E₆.Group = 51840) :
    ∃ (V : Type) (_ : AddCommGroup V) (_ : Module (ZMod 3) V) (ι : Additive ↥Bs ≃+ V)
      (h : Fin 6 → V) (α : Fin 6 → Dual (ZMod 3) V) (hα : ∀ i, α i (h i) = 2)
      (β : LinearMap.BilinForm (ZMod 3) V),
      Nat.card V = 3 ^ 5 ∧ A.map (ggLin (p := 3) ι) = e6Weyl hα ∧
        Nat.card (e6Weyl hα) = 51840 ∧
        (∀ i j, α i (h j) = (CartanMatrix.E 6 i j : ZMod 3)) ∧
        (∀ i v, β (h i) v = α i v) := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨V, hVadd, hVmod, ⟨ι⟩⟩ := CFSG.StandardType.exists_ggLinData (p := 3) hBs
  letI := hVadd
  letI := hVmod
  have hVcard : Nat.card V = 3 ^ 5 := by
    rw [← CFSG.StandardType.card_eq_of_ggLin ι]
    exact hcard
  haveI : Finite V := Nat.finite_of_card_ne_zero (by rw [hVcard]; norm_num)
  obtain ⟨e, h, α, hα, he, hP⟩ := exists_cartan_pairing_E6 hNT hW hA ι
  obtain ⟨β, hβ⟩ := exists_bilinForm hP hVcard
  have hmapA : A.map (ggLin (p := 3) ι) = e6Weyl hα :=
    map_ggLin_eq_e6Weyl ι e hα he
  have hWcard' : Nat.card (e6Weyl hα) = 51840 := by
    rw [card_e6Weyl_eq ι e hα he,
      show Nat.card A = Nat.card (CoxeterMatrix.E₆).Group from (Nat.card_congr e.toEquiv).symm,
      hWcard]
  exact ⟨V, hVadd, hVmod, ι, h, α, hα, β, hVcard, hmapA, hWcard', hP, hβ⟩

variable {G : Type} [Group G] [Finite G] {Bs : Subgroup G}

theorem norm_eq_one_of_card_192
    (hBs : IsElemAbelian 3 Bs) (hNT : GGNoTransvection 3 Bs) (hcard : Nat.card Bs = 3 ^ 5)
    (hWcard : Nat.card CoxeterMatrix.E₆.Group = 51840) {A : Subgroup (MulAut ↥Bs)}
    (hind : ∀ φ ∈ A, φ ∈ ggInduced ⊤ Bs) (hW : GGWeylOfType 3 CoxeterMatrix.E₆ A)
    {AL : Subgroup (MulAut ↥Bs)} (hALA : AL ≤ A) (hALcard : Nat.card AL = 192)
    {x : ↥Bs} (hx : x ≠ 1) (hALx : ∀ φ ∈ AL, φ x = x) :
    ∃ (V : Type) (_ : AddCommGroup V) (_ : Module (ZMod 3) V) (ι : Additive ↥Bs ≃+ V)
      (h : Fin 6 → V) (α : Fin 6 → Dual (ZMod 3) V) (hα : ∀ i, α i (h i) = 2)
      (β : LinearMap.BilinForm (ZMod 3) V),
      Nat.card V = 3 ^ 5 ∧ A.map (ggLin (p := 3) ι) = e6Weyl hα ∧
        Nat.card (e6Weyl hα) = 51840 ∧
        (∀ i j, α i (h j) = (CartanMatrix.E 6 i j : ZMod 3)) ∧
        (∀ i v, β (h i) v = α i v) ∧
        β (ι (Additive.ofMul x)) (ι (Additive.ofMul x)) = 1 := by
  classical
  obtain ⟨V, hVadd, hVmod, ι, h, α, hα, β, hVcard, hmapA, hWcard', hP, hB⟩ :=
    exists_e6LinearModel' hBs hcard hNT hW hind hWcard
  letI := hVadd
  letI := hVmod
  haveI : Finite V := Nat.finite_of_card_ne_zero (by rw [hVcard]; norm_num)
  haveI : Finite (V ≃ₗ[ZMod 3] V) :=
    Finite.of_injective ((↑) : (V ≃ₗ[ZMod 3] V) → V → V) DFunLike.coe_injective
  set vx : V := ι (Additive.ofMul x) with hvxdef
  have hvx : vx ≠ 0 := by
    intro h0
    apply hx
    have h1 : Additive.ofMul x = 0 := ι.injective (by rw [← hvxdef, h0, map_zero])
    exact Additive.ofMul.injective (by simpa using h1)
  have hALle : AL.map (ggLin (p := 3) ι) ≤ e6Weyl hα := by
    rw [← hmapA]
    exact Subgroup.map_mono hALA
  have hcardALmap : Nat.card (AL.map (ggLin (p := 3) ι)) = 192 := by
    rw [Subgroup.card_map_of_injective (ggLin_injective (p := 3) ι), hALcard]
  let S' : Subgroup (V ≃ₗ[ZMod 3] V) :=
    (MulAction.stabilizer (e6Weyl hα) vx).map (Subgroup.subtype (e6Weyl hα))
  have hcardS' : Nat.card S' = Nat.card (MulAction.stabilizer (e6Weyl hα) vx) :=
    Subgroup.card_map_of_injective (Subgroup.subtype_injective (e6Weyl hα))
  have hstab : AL.map (ggLin (p := 3) ι) ≤ S' := by
    intro g hg
    obtain ⟨φ, hφ, rfl⟩ := Subgroup.mem_map.mp hg
    refine Subgroup.mem_map.mpr ⟨⟨_, hALle hg⟩, ?_, rfl⟩
    rw [MulAction.mem_stabilizer_iff]
    change (ggLin (p := 3) ι φ) (ι (Additive.ofMul x)) = ι (Additive.ofMul x)
    rw [ggLin_apply_ofMul, hALx φ hφ]
  have hdvd : 192 ∣ Nat.card (MulAction.stabilizer (e6Weyl hα) vx) := by
    rw [← hcardS', ← hcardALmap]
    exact Subgroup.card_dvd_of_le hstab
  have hcases := stabilizer_cases hP hVcard hB hα hWcard' hvx
  have hnorm : β vx vx = 1 := by
    rcases hcases with ⟨-, h720⟩ | ⟨-, h648⟩ | ⟨h1, -⟩
    · rw [h720] at hdvd
      exact absurd hdvd (by norm_num)
    · rw [h648] at hdvd
      exact absurd hdvd (by norm_num)
    · exact h1
  exact ⟨V, hVadd, hVmod, ι, h, α, hα, β, hVcard, hmapA, hWcard', hP, hB, hnorm⟩

end CFSG.StandardType.E6QTwo

end
