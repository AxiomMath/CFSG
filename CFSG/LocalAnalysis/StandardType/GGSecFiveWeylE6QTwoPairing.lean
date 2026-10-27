module

public import CFSG.LocalAnalysis.StandardType.GGSpJoinReflPairing
public import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylE6QTwoCartan
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyAut

public section

namespace CFSG.StandardType.E6QTwo

open Module CFSG.Assembly

variable {G : Type} [Group G] {Bs : Subgroup G} {V : Type} [AddCommGroup V] [Module (ZMod 3) V]

theorem exists_cartan_pairing_E6 [Finite G] (hNT : GGNoTransvection 3 Bs)
    {A : Subgroup (MulAut ↥Bs)} (hW : GGWeylOfType 3 CoxeterMatrix.E₆ A)
    (hA : ∀ φ ∈ A, φ ∈ ggInduced ⊤ Bs) (ι : Additive ↥Bs ≃+ V) :
    ∃ (e : CoxeterMatrix.E₆.Group ≃* ↥A) (h : Fin 6 → V) (α : Fin 6 → Dual (ZMod 3) V)
      (hα : ∀ i, α i (h i) = 2),
      (∀ i, ggLin (p := 3) ι ((e (CoxeterMatrix.E₆.simple i) : ↥A) : MulAut ↥Bs) =
        reflection (hα i)) ∧
      ∀ i j, α i (h j) = (CartanMatrix.E 6 i j : ZMod 3) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let par : Fin 6 → Fin 6 := ![0, 3, 0, 2, 3, 4]
  let depth : Fin 6 → ℕ := ![0, 3, 1, 2, 3, 4]
  have hsl : ∀ i j : Fin 6, i ≠ j →
      CartanMatrix.E 6 i j = 0 ∨ CartanMatrix.E 6 i j = -1 := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> first | exact absurd rfl hij | decide
  have hpar : ∀ i j : Fin 6, i ≠ j →
      (CartanMatrix.E 6 i j = -1 ↔
        ((i ≠ 0 ∧ par i = j) ∨ (j ≠ 0 ∧ par j = i))) := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> first | exact absurd rfl hij | decide
  have hdepth : ∀ i : Fin 6, i ≠ 0 → depth (par i) < depth i := by
    decide
  exact CFSG.StandardType.SpJoinRefl.exists_cartan_pairing_of_weylOfType
    (p := 3) (M := CoxeterMatrix.E₆) (C := CartanMatrix.E 6)
    (by norm_num) hNT ggIntCartan_E₆ hsl par 0 depth hpar hdepth hW hA ι

theorem three_pow_five_le_card [Finite G] (hBs : IsElemAbelian 3 Bs)
    (hNT : GGNoTransvection 3 Bs) {A : Subgroup (MulAut ↥Bs)}
    (hA : ∀ φ ∈ A, φ ∈ ggInduced ⊤ Bs) (hW : GGWeylOfType 3 CoxeterMatrix.E₆ A) :
    3 ^ 5 ≤ Nat.card Bs := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨V, hVadd, hVmod, ⟨ι⟩⟩ := CFSG.StandardType.exists_ggLinData (p := 3) hBs
  letI : AddCommGroup V := hVadd
  letI : Module (ZMod 3) V := hVmod
  haveI : Finite V := Finite.of_equiv _ ι.toEquiv
  obtain ⟨e, h, α, hα, hrefl, hP⟩ := exists_cartan_pairing_E6 hNT hW hA ι
  haveI : Fintype V := Fintype.ofFinite V
  have h5 := five_le_finrank_span hP
  have hle : finrank (ZMod 3) (Submodule.span (ZMod 3) (Set.range h)) ≤ finrank (ZMod 3) V :=
    Submodule.finrank_le _
  have hV : Nat.card V = 3 ^ finrank (ZMod 3) V := by
    rw [Nat.card_eq_fintype_card, Module.card_eq_pow_finrank (K := ZMod 3), ZMod.card]
  rw [CFSG.StandardType.card_eq_of_ggLin ι, hV]
  exact Nat.pow_le_pow_right (by norm_num) (h5.trans hle)

theorem eq_one_of_forall_fixed_of_card [Finite G] (hBs : IsElemAbelian 3 Bs)
    (hNT : GGNoTransvection 3 Bs) {A : Subgroup (MulAut ↥Bs)}
    (hA : ∀ φ ∈ A, φ ∈ ggInduced ⊤ Bs) (hW : GGWeylOfType 3 CoxeterMatrix.E₆ A)
    (hcard : Nat.card Bs = 3 ^ 5) {b : ↥Bs} (hb : ∀ ψ ∈ A, ψ b = b) : b = 1 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨V, hVadd, hVmod, ⟨ι⟩⟩ := CFSG.StandardType.exists_ggLinData (p := 3) hBs
  letI : AddCommGroup V := hVadd
  letI : Module (ZMod 3) V := hVmod
  haveI : Finite V := Finite.of_equiv _ ι.toEquiv
  obtain ⟨e, h, α, hα, hrefl, hP⟩ := exists_cartan_pairing_E6 hNT hW hA ι
  have hV : Nat.card V = 3 ^ 5 := by
    rw [← CFSG.StandardType.card_eq_of_ggLin ι]
    exact hcard
  set v : V := ι (Additive.ofMul b) with hvdef
  have hv : ∀ i : Fin 6, α i v = 0 := by
    intro i
    let φ : MulAut ↥Bs := ((e (CoxeterMatrix.E₆.simple i) : ↥A) : MulAut ↥Bs)
    have hφA : φ ∈ A := (e (CoxeterMatrix.E₆.simple i)).2
    have hfixv : ggLin (p := 3) ι φ v = v := (ggLin_fix_iff ι φ b).mp (hb φ hφA)
    have h2 : v - (α i v) • h i = v := by
      have h3 : ggLin (p := 3) ι φ v = v - (α i v) • h i := by
        rw [hrefl i, reflection_apply]
      rw [← h3]
      exact hfixv
    have h3 : (α i v) • h i = 0 := sub_eq_self.mp h2
    have hhi : h i ≠ 0 := (ne_zero_of_apply_eq_two (p := 3) (by norm_num) (hα i)).1
    exact (smul_eq_zero.mp h3).resolve_right hhi
  have hv0 : v = 0 := eq_zero_of_forall_apply_eq_zero hP hV hv
  have h1 : Additive.ofMul b = 0 := by
    apply ι.injective
    rw [map_zero]
    rwa [← hvdef]
  have h2 : Additive.ofMul b = Additive.ofMul (1 : ↥Bs) := by
    rw [h1, ofMul_one]
  exact Additive.ofMul.injective h2

theorem le_sup_of_weylOfType_E6 [Finite G] (hBs : IsElemAbelian 3 Bs)
    (hNT : GGNoTransvection 3 Bs) {L K : Subgroup G}
    (hL : Bs ≤ Subgroup.normalizer (L : Set G)) (hK : Bs ≤ Subgroup.normalizer (K : Set G))
    (hW : GGWeylOfType 3 CoxeterMatrix.E₆ (ggAutomizer L Bs ⊔ ggAutomizer K Bs))
    (hcard : Nat.card Bs = 3 ^ 5) : Bs ≤ L ⊔ K := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hAle : ggAutomizer L Bs ⊔ ggAutomizer K Bs ≤ ggAutomizer (L ⊔ K) Bs :=
    sup_le (CFSG.StandardType.ggAutomizer_mono Bs le_sup_left)
      (CFSG.StandardType.ggAutomizer_mono Bs le_sup_right)
  have hAind : ∀ φ ∈ ggAutomizer L Bs ⊔ ggAutomizer K Bs, φ ∈ ggInduced ⊤ Bs := by
    intro φ hφ
    obtain ⟨g, -, hgN, hg⟩ := CFSG.StandardType.mem_ggAutomizer_iff.mp (hAle hφ)
    exact ⟨g, Subgroup.mem_top g, hgN, hg⟩
  have hstep : ∀ ψ ∈ ggAutomizer L Bs ⊔ ggAutomizer K Bs, ∀ b : ↥Bs,
      (((ψ b : ↥Bs) : G) * (b : G)⁻¹) ∈ L ⊔ K := by
    intro ψ hψ b
    obtain ⟨g, hgLK, hgN, hg⟩ := CFSG.StandardType.mem_ggAutomizer_iff.mp (hAle hψ)
    have hbnorm : (b : G) ∈ Subgroup.normalizer ((L ⊔ K : Subgroup G) : Set G) :=
      Subgroup.normalizer_inf_normalizer_le_normalizer_sup L K ⟨hL b.2, hK b.2⟩
    have hmem : (b : G) * g⁻¹ * (b : G)⁻¹ ∈ L ⊔ K :=
      (Subgroup.mem_normalizer_iff.mp hbnorm g⁻¹).mp (Subgroup.inv_mem _ hgLK)
    have heq : ((ψ b : ↥Bs) : G) * (b : G)⁻¹ = g * ((b : G) * g⁻¹ * (b : G)⁻¹) := by
      rw [hg b]; group
    rw [heq]
    exact (L ⊔ K).mul_mem hgLK hmem
  obtain ⟨V, hVadd, hVmod, ⟨ι⟩⟩ := CFSG.StandardType.exists_ggLinData (p := 3) hBs
  letI : AddCommGroup V := hVadd
  letI : Module (ZMod 3) V := hVmod
  haveI : Finite V := Finite.of_equiv _ ι.toEquiv
  obtain ⟨e, h, α, hα, hrefl, hP⟩ := exists_cartan_pairing_E6 hNT hW hAind ι
  have hV : Nat.card V = 3 ^ 5 := by
    rw [← CFSG.StandardType.card_eq_of_ggLin ι]
    exact hcard
  let U : AddSubgroup V :=
    { carrier := {v | ((Additive.toMul (ι.symm v) : ↥Bs) : G) ∈ L ⊔ K}
      zero_mem' := by
        show ((Additive.toMul (ι.symm (0 : V)) : ↥Bs) : G) ∈ L ⊔ K
        rw [map_zero, toMul_zero]
        exact (L ⊔ K).one_mem
      add_mem' := by
        intro v w hv hw
        show ((Additive.toMul (ι.symm (v + w)) : ↥Bs) : G) ∈ L ⊔ K
        rw [map_add, toMul_add, Subgroup.coe_mul]
        exact (L ⊔ K).mul_mem hv hw
      neg_mem' := by
        intro v hv
        show ((Additive.toMul (ι.symm (-v)) : ↥Bs) : G) ∈ L ⊔ K
        rw [map_neg, toMul_neg, Subgroup.coe_inv]
        exact (L ⊔ K).inv_mem hv }
  have hhU : ∀ i : Fin 6, h i ∈ U := by
    intro i
    have hαne : α i ≠ 0 := by
      intro h0
      have h2 := hα i
      rw [h0] at h2
      exact zmod_two_ne_zero (by norm_num) h2.symm
    have hmem1 : (1 : ZMod 3) ∈ LinearMap.range (α i) := by
      rw [Module.Dual.range_eq_top_of_ne_zero hαne]
      exact Submodule.mem_top
    obtain ⟨v, hv⟩ := hmem1
    set φ : MulAut ↥Bs :=
      ((e (CoxeterMatrix.E₆.simple i) : ↥(ggAutomizer L Bs ⊔ ggAutomizer K Bs)) : MulAut ↥Bs)
      with hφdef
    have hφA : φ ∈ ggAutomizer L Bs ⊔ ggAutomizer K Bs := by
      rw [hφdef]; exact (e (CoxeterMatrix.E₆.simple i)).2
    have hreflφ : ggLin (p := 3) ι φ = reflection (hα i) := by
      rw [hφdef]; exact hrefl i
    let b : ↥Bs := Additive.toMul (ι.symm v)
    have hbvec : ι (Additive.ofMul b) = v := by
      simp [b]
    have hlin : ggLin (p := 3) ι φ v = ι (Additive.ofMul (φ b)) := by
      rw [← hbvec, ggLin_apply_ofMul]
    have hhi : h i = ι (Additive.ofMul (b * (φ b)⁻¹)) := by
      have hmove : h i = v - ggLin (p := 3) ι φ v := by
        rw [hreflφ, reflection_apply, hv, one_smul]
        abel
      rw [hmove, hlin, ← hbvec, ← map_sub]
      congr 1
      rw [ofMul_mul, ofMul_inv, sub_eq_add_neg]
    have hmem : ((b * (φ b)⁻¹ : ↥Bs) : G) ∈ L ⊔ K := by
      have hφb : (((φ b : ↥Bs) : G) * (b : G)⁻¹) ∈ L ⊔ K := hstep φ hφA b
      have hcoe : ((b * (φ b)⁻¹ : ↥Bs) : G) = (((φ b : ↥Bs) : G) * (b : G)⁻¹)⁻¹ := by
        rw [Subgroup.coe_mul, Subgroup.coe_inv]
        group
      rw [hcoe]
      exact (L ⊔ K).inv_mem hφb
    rw [hhi]
    show ((Additive.toMul (ι.symm (ι (Additive.ofMul (b * (φ b)⁻¹)))) : ↥Bs) : G) ∈ L ⊔ K
    simpa using hmem
  have hspan := span_eq_top_of_card hP hV
  have hspan_le : Submodule.span (ZMod 3) (Set.range h) ≤
      AddSubgroup.toZModSubmodule (n := 3) U := by
    rw [Submodule.span_le]
    rintro v ⟨i, rfl⟩
    exact (AddSubgroup.mem_toZModSubmodule (n := 3) (S := U)).mpr (hhU i)
  have htop : AddSubgroup.toZModSubmodule (n := 3) U = ⊤ := by
    rw [eq_top_iff, ← hspan]
    exact hspan_le
  intro b hb
  have hbv : ι (Additive.ofMul (⟨b, hb⟩ : ↥Bs)) ∈
      AddSubgroup.toZModSubmodule (n := 3) U := by
    rw [htop]
    exact Submodule.mem_top
  have hbU := (AddSubgroup.mem_toZModSubmodule (n := 3) (S := U)).mp hbv
  simpa [U] using hbU

theorem not_le_of_weylOfType_E6 [Finite G] (hBs : IsElemAbelian 3 Bs)
    (hNT : GGNoTransvection 3 Bs) {L K : Subgroup G} {x : G} (hx : x ∈ Bs) (hx1 : x ≠ 1)
    (hLx : L ≤ Subgroup.centralizer {x})
    (hW : GGWeylOfType 3 CoxeterMatrix.E₆ (ggAutomizer L Bs ⊔ ggAutomizer K Bs))
    (hcard : Nat.card Bs = 3 ^ 5) : ¬ K ≤ L := by
  intro hKL
  have hsup : ggAutomizer L Bs ⊔ ggAutomizer K Bs = ggAutomizer L Bs :=
    sup_eq_left.mpr (CFSG.StandardType.ggAutomizer_mono Bs hKL)
  rw [hsup] at hW
  have hAind : ∀ φ ∈ ggAutomizer L Bs, φ ∈ ggInduced ⊤ Bs := by
    intro φ hφ
    obtain ⟨g, -, hgN, hg⟩ := CFSG.StandardType.mem_ggAutomizer_iff.mp hφ
    exact ⟨g, Subgroup.mem_top g, hgN, hg⟩
  have hfix : ∀ ψ ∈ ggAutomizer L Bs, ψ ⟨x, hx⟩ = ⟨x, hx⟩ := by
    intro ψ hψ
    obtain ⟨g, hgL, hgN, hg⟩ := CFSG.StandardType.mem_ggAutomizer_iff.mp hψ
    refine Subtype.ext ?_
    rw [hg ⟨x, hx⟩]
    have hc : g * x = x * g := Subgroup.mem_centralizer_singleton_iff.mp (hLx hgL)
    rw [hc]
    group
  have hb1 : (⟨x, hx⟩ : ↥Bs) = 1 :=
    eq_one_of_forall_fixed_of_card hBs hNT hAind hW hcard (b := ⟨x, hx⟩) hfix
  exact hx1 (by simpa using congrArg Subtype.val hb1)

end CFSG.StandardType.E6QTwo

end
