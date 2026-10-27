module

public import CFSG.LocalAnalysis.StandardType.GGUSixTwoTorus
public import CFSG.LocalAnalysis.StandardType.GGOneFiveDefs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveRest
public import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylE6QTwoTransfer
public import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylE6QTwoPairing
public import CFSG.LocalAnalysis.StandardType.GGCoxeterLabelTypeAAssembly
public import CFSG.LocalAnalysis.StandardType.GGCoxeterLabelTypeABridge
public import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylE6QTwoCoverAux

public section

namespace CFSG.StandardType.E6QTwo

open CFSG.Assembly

variable {G : Type} [Group G] [Finite G] {K : Type} [Field K] [Finite K]

theorem le_closure_inv_of_not_isPGroup
    (hK : Nat.card K = 4)
    {Bs L : Subgroup G} {x : G}
    (θ : L ⧸ Subgroup.center L ≃* LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1)))
    (hperf : commutator ↥L = ⊤) (hBs : IsElemAbelian 3 Bs) (hcard : Nat.card Bs = 3 ^ 5)
    (hx : x ∈ Bs) (hx1 : x ≠ 1)
    (hBL : Bs ⊓ Subgroup.centralizer (L : Set G) = Subgroup.zpowers x)
    (hstar : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ 3 = 1 → g ∈ Bs)
    (hNL : Bs ≤ Subgroup.normalizer (L : Set G))
    (hI : ∀ b ∈ Bs, ∃ ψ ∈ LargeEvenMatConjImage
        (LargeEvenProjMk (LargeEvenSUGroup (Fin 6) K (2 ^ 1))) (LargeEvenGUSet (Fin 6) K (2 ^ 1)),
      LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) ψ)
    (hZ : ¬ IsPGroup 2 (Subgroup.center L)) :
    Bs ≤ Subgroup.closure
      {b | b ∈ Bs ∧ ∃ l ∈ L, l ∈ Subgroup.normalizer (Bs : Set G) ∧ l * b * l⁻¹ = b⁻¹} := by
  exact le_closure_inv_aux hK θ hperf hBs hcard hx hx1 hBL hstar hNL hI hZ

theorem eq_one_of_le_closure_inv {Bs : Subgroup G} (hBs : IsElemAbelian 3 Bs)
    (hNT : GGNoTransvection 3 Bs) {L K' : Subgroup G} {x : G} (hx : x ∈ Bs)
    (hLx : L ≤ Subgroup.centralizer {x})
    (hW : GGWeylOfType 3 CoxeterMatrix.E₆ (ggAutomizer L Bs ⊔ ggAutomizer K' Bs))
    (hcard : Nat.card Bs = 3 ^ 5)
    (hgen : Bs ≤ Subgroup.closure
      {b | b ∈ Bs ∧ ∃ l ∈ L, l ∈ Subgroup.normalizer (Bs : Set G) ∧ l * b * l⁻¹ = b⁻¹}) :
    x = 1 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨V, hVadd, hVmod, ⟨ι⟩⟩ := exists_ggLinData (p := 3) hBs
  letI : AddCommGroup V := hVadd
  letI : Module (ZMod 3) V := hVmod
  have hVcard : Nat.card V = 3 ^ 5 := by
    rw [← card_eq_of_ggLin ι]
    exact hcard
  haveI : Finite V := Nat.finite_of_card_ne_zero (by rw [hVcard]; norm_num)
  let A₀ : Subgroup (MulAut ↥Bs) := ggAutomizer L Bs ⊔ ggAutomizer K' Bs
  have hWeylA : GGWeylOfType 3 CoxeterMatrix.E₆ A₀ := hW
  have hA : ∀ ψ ∈ A₀, ψ ∈ ggInduced ⊤ Bs := by
    intro ψ hψ
    exact mem_ggInduced_top_of_mem_ggAutomizer
      (sup_le (ggAutomizer_mono Bs le_top) (ggAutomizer_mono Bs le_top) hψ)
  obtain ⟨e, h, α, hα, he, hP⟩ := exists_cartan_pairing_E6 hNT hWeylA hA ι
  obtain ⟨β, hβ⟩ := exists_bilinForm hP hVcard
  let vx : V := ι (Additive.ofMul (⟨x, hx⟩ : ↥Bs))
  have hvxdef : vx = ι (Additive.ofMul (⟨x, hx⟩ : ↥Bs)) := rfl
  have hiso : ∀ ψ ∈ ggAutomizer L Bs, ∀ u v : V,
      β (ggLin (p := 3) ι ψ u) (ggLin (p := 3) ι ψ v) = β u v := by
    intro ψ hψ
    have hψe6 : ggLin (p := 3) ι ψ ∈ e6Weyl hα := by
      rw [← map_ggLin_eq_e6Weyl ι e hα he]
      exact Subgroup.mem_map_of_mem _ ((le_sup_left : ggAutomizer L Bs ≤ A₀) hψ)
    exact bilinForm_apply_e6Weyl hP hVcard hβ hα hψe6
  have hfixv : ∀ ψ ∈ ggAutomizer L Bs, ggLin (p := 3) ι ψ vx = vx := by
    intro ψ hψ
    rw [hvxdef, ggLin_apply_ofMul]
    congr 1
    exact ggAutomizer_apply_eq_of_le_centralizer hLx hψ
  let F : ↥Bs →* Multiplicative (ZMod 3) :=
    { toFun := fun b => Multiplicative.ofAdd (β vx (ι (Additive.ofMul b)))
      map_one' := by simp
      map_mul' := fun a b => by simp [map_add] }
  have hkilled : ∀ y ∈ {b | b ∈ Bs ∧ ∃ l ∈ L,
      l ∈ Subgroup.normalizer (Bs : Set G) ∧ l * b * l⁻¹ = b⁻¹},
      ∀ hy : y ∈ Bs, F ⟨y, hy⟩ = 1 := by
    rintro y ⟨hyB, l, hlL, hlN, hlinv⟩ hy
    let ψ : MulAut ↥Bs := ggConjAut Bs hlN
    have hψAL : ψ ∈ ggAutomizer L Bs := ggConjAut_mem_ggAutomizer hlL hlN
    have hψy : ψ ⟨y, hy⟩ = (⟨y, hy⟩ : ↥Bs)⁻¹ := by
      refine Subtype.ext ?_
      rw [ggConjAut_apply]
      exact hlinv
    have h1 : ggLin (p := 3) ι ψ (ι (Additive.ofMul (⟨y, hy⟩ : ↥Bs))) =
        -ι (Additive.ofMul (⟨y, hy⟩ : ↥Bs)) :=
      (ggLin_inv_iff ι ψ ⟨y, hy⟩).mp hψy
    have h2 : β vx (ι (Additive.ofMul (⟨y, hy⟩ : ↥Bs))) = 0 := by
      have his := hiso ψ hψAL vx (ι (Additive.ofMul (⟨y, hy⟩ : ↥Bs)))
      rw [hfixv ψ hψAL, h1, map_neg] at his
      have h3 : β vx (ι (Additive.ofMul (⟨y, hy⟩ : ↥Bs))) +
          β vx (ι (Additive.ofMul (⟨y, hy⟩ : ↥Bs))) = 0 :=
        neg_eq_iff_add_eq_zero.mp his
      have h4 : (2 : ZMod 3) * β vx (ι (Additive.ofMul (⟨y, hy⟩ : ↥Bs))) = 0 := by
        rw [two_mul]
        exact h3
      have h2ne : (2 : ZMod 3) ≠ 0 := CFSG.StandardType.zmod_two_ne_zero (p := 3) (by norm_num)
      exact (mul_eq_zero.mp h4).resolve_left h2ne
    simpa [F] using h2
  have hclosure : ∀ y ∈ Subgroup.closure {b | b ∈ Bs ∧ ∃ l ∈ L,
      l ∈ Subgroup.normalizer (Bs : Set G) ∧ l * b * l⁻¹ = b⁻¹},
      ∀ hy : y ∈ Bs, F ⟨y, hy⟩ = 1 := by
    intro y hy
    refine Subgroup.closure_induction (p := fun z _ => ∀ hz : z ∈ Bs, F ⟨z, hz⟩ = 1)
      ?_ ?_ ?_ ?_ hy
    · exact hkilled
    · intro hz
      have hz1 : (⟨1, hz⟩ : ↥Bs) = 1 := Subtype.ext rfl
      rw [hz1, map_one]
    · intro a b ha hb haB hbB
      have haBs : a ∈ Bs := (Subgroup.closure_le (K := Bs)).mpr (fun s hs => hs.1) ha
      have hbBs : b ∈ Bs := (Subgroup.closure_le (K := Bs)).mpr (fun s hs => hs.1) hb
      intro hz
      rw [show (⟨a * b, hz⟩ : ↥Bs) = ⟨a, haBs⟩ * ⟨b, hbBs⟩ from rfl, map_mul,
        haB haBs, hbB hbBs, mul_one]
    · intro a ha haB
      have haBs : a ∈ Bs := (Subgroup.closure_le (K := Bs)).mpr (fun s hs => hs.1) ha
      intro hz
      rw [show (⟨a⁻¹, hz⟩ : ↥Bs) = (⟨a, haBs⟩ : ↥Bs)⁻¹ from rfl, map_inv, haB haBs]
      exact inv_one
  have hall : ∀ v : V, β vx v = 0 := by
    intro v
    obtain ⟨b, rfl⟩ : ∃ b : ↥Bs, ι (Additive.ofMul b) = v :=
      ⟨Additive.toMul (ι.symm v), by simp⟩
    have h1 := hclosure (b : G) (hgen b.2) b.2
    simpa [F] using h1
  have hzero : vx = 0 := bilinForm_nondegenerate hP hVcard hβ (u := vx) hall
  rw [hvxdef] at hzero
  have h1 : Additive.ofMul (⟨x, hx⟩ : ↥Bs) = 0 := ι.injective (by rw [hzero, map_zero])
  have h2 : (⟨x, hx⟩ : ↥Bs) = 1 := by simpa using congrArg Additive.toMul h1
  exact by simpa using congrArg Subtype.val h2

theorem isPGroup_two_center
    (hK : Nat.card K = 4) {Bs L K' : Subgroup G} {x : G}
    (θ : L ⧸ Subgroup.center L ≃* LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1)))
    (hperf : commutator ↥L = ⊤) (hBs : IsElemAbelian 3 Bs) (hNT : GGNoTransvection 3 Bs)
    (hcard : Nat.card Bs = 3 ^ 5) (hx : x ∈ Bs) (hx1 : x ≠ 1)
    (hLx : L ≤ Subgroup.centralizer {x})
    (hBL : Bs ⊓ Subgroup.centralizer (L : Set G) = Subgroup.zpowers x)
    (hstar : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ 3 = 1 → g ∈ Bs)
    (hNL : Bs ≤ Subgroup.normalizer (L : Set G))
    (hI : ∀ b ∈ Bs, ∃ ψ ∈ LargeEvenMatConjImage
        (LargeEvenProjMk (LargeEvenSUGroup (Fin 6) K (2 ^ 1))) (LargeEvenGUSet (Fin 6) K (2 ^ 1)),
      LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) ψ)
    (hW : GGWeylOfType 3 CoxeterMatrix.E₆ (ggAutomizer L Bs ⊔ ggAutomizer K' Bs)) :
    IsPGroup 2 (Subgroup.center L) := by
  by_contra hZ
  exact hx1 (eq_one_of_le_closure_inv (Bs := Bs) hBs hNT (L := L) (K' := K') hx hLx hW hcard
    (le_closure_inv_of_not_isPGroup hK θ hperf hBs hcard hx hx1 hBL hstar hNL hI hZ))

end CFSG.StandardType.E6QTwo

end
