module

public import CFSG.LocalAnalysis.StandardType.GGCoxeterLabelCLLWeyl
public import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylE6QTwoAux
public import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylE6QTwoDefs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylE6QTwoCover
public import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylE6QTwoCoverTwo
public import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylE6QTwoInnerQ
public import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylE6QTwoLocal
public import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylE6QTwoOrbit
public import CFSG.LocalAnalysis.StandardType.GGSixBstarNoOffenderExcWeyl

public section

namespace CFSG.StandardType

open CFSG.Assembly

variable {G : Type} [Group G]

section Config

variable [Finite G]

theorem e6QTwo_config_facts
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hC : GGSecFiveE6QTwoCfg 3 B Bs x L D J) :
    GGSecFiveRestHyp 3 B Bs x L D J ∧ IsCharTwoType G ∧ LargeEvenSStar 3 B x L ∧
      IsElemAbelian 3 Bs ∧ x ∈ Bs ∧ x ≠ 1 ∧ orderOf x = 3 ∧
      L ≤ Subgroup.centralizer ({x} : Set G) ∧
      (∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ 3 = 1 → g ∈ Bs) ∧
      (∀ S : Subgroup G, IsPGroup 3 S → S ≤ Subgroup.centralizer (L : Set G) →
        IsCyclic S) ∧
      GGNoTransvection 3 Bs := by
  obtain ⟨𝒦, hRoute, -⟩ := hC
  have hRest : GGSecFiveRestHyp 3 B Bs x L D J := hRoute.1
  have hcfg : GGConfig 3 B Bs x L D J := hRest.1
  have hNT : GGNoTransvection 3 Bs := hRest.2.2.2.1
  have hS : LargeEvenSStar 3 B x L := hcfg.1.2.2.2.2.2.2.1
  obtain ⟨-, hBs, hxB, hLx, -⟩ := hcfg.tableB_facts
  have hx1 : x ≠ 1 := hS.2.2.1
  have horderx : orderOf x = 3 := orderOf_eq_prime (hBs.2 x hxB) hx1
  have hstar : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ 3 = 1 → g ∈ Bs :=
    hcfg.2.1.2.2.2
  have hcyc : ∀ S : Subgroup G, IsPGroup 3 S → S ≤ Subgroup.centralizer (L : Set G) →
      IsCyclic S := fun S hSp hSL => hcfg.1.2.2.2.2.2.2.1.2.2.2.2 S hSL hSp
  exact ⟨hRest, hcfg.1.2.2.2.1, hS, hBs, hxB, hx1, horderx, hLx, hstar, hcyc, hNT⟩

end Config

theorem exists_unitaryDatum_of_innerDiagOnLabel_twA5 {Bs L : Subgroup G}
    (hlab : GGInnerDiagOnLabel (fun _ lab => lab.tag = .twA ∧ lab.rank = 5 ∧ lab.n = 1)
      3 Bs L) :
    commutator ↥L = ⊤ ∧
      ∃ (K : Type) (_ : Field K) (_ : Finite K)
        (θ : L ⧸ Subgroup.center L ≃*
          LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1))),
        Nat.card K = 4 ∧ Bs ≤ Subgroup.normalizer (L : Set G) ∧
          (∀ b ∈ Bs, ∃ ψ ∈ LargeEvenMatConjImage
            (LargeEvenProjMk (LargeEvenSUGroup (Fin 6) K (2 ^ 1)))
            (LargeEvenGUSet (Fin 6) K (2 ^ 1)),
            LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) ψ) := by
  obtain ⟨hperf, lab, -, hraw⟩ := hlab
  obtain ⟨t, r, n⟩ := lab
  obtain ⟨R₀, _, I₀, F₀, -, -, -, hlabS, -⟩ := largeEvenRawDatum_exists hraw
  obtain ⟨rfl, rfl, rfl⟩ := hlabS
  dsimp only [LargeEvenRawDatumLegacy, LargeEvenRecipeUnitary] at hraw
  obtain ⟨K, hfieldK, hfiniteK, hKcard, hQ⟩ := hraw
  obtain ⟨-, -, θ, -, hBsN, hI⟩ := hQ
  exact ⟨hperf, K, hfieldK, hfiniteK, θ, by rw [hKcard]; norm_num, hBsN, hI⟩

theorem not_mem_of_isPGroup_two_center {L : Subgroup G} {x : G}
    (hZ2 : IsPGroup 2 (Subgroup.center L)) (horderx : orderOf x = 3)
    (hLx : L ≤ Subgroup.centralizer ({x} : Set G)) : x ∉ L := by
  intro hxL
  have hxZ : (⟨x, hxL⟩ : ↥L) ∈ Subgroup.center ↥L := by
    rw [Subgroup.mem_center_iff]
    intro l
    exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp (hLx l.2))
  let e : ↥(Subgroup.center L) := ⟨⟨x, hxL⟩, hxZ⟩
  have he3 : orderOf e = 3 := by
    have h1 := orderOf_injective (Subgroup.center L).subtype
      (Subgroup.center L).subtype_injective e
    have h2 := orderOf_injective L.subtype L.subtype_injective
      ((Subgroup.center L).subtype e)
    rw [← h1, ← h2]
    exact horderx
  have hcop : (orderOf e).Coprime (orderOf e) :=
    hZ2.orderOf_coprime (n := orderOf e) (by rw [he3]; norm_num) e
  have he1 : e = 1 := orderOf_eq_one_iff.mp ((Nat.coprime_self (orderOf e)).mp hcop)
  have hxone : x = 1 := congrArg (fun t : ↥(Subgroup.center L) => ((t : ↥L) : G)) he1
  rw [hxone] at horderx
  simp at horderx

section Conjugate

variable [Finite G] {K : Type} [Field K] [Finite K]

theorem exists_mem_normalizer_conj_eq_threeA (hK : Nat.card K = 4) {ω : K}
    (hω : ω ^ 2 + ω + 1 = 0) {Bs L K' : Subgroup G} {x : G}
    (θ : L ⧸ Subgroup.center L ≃* LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1)))
    (hZ2 : IsPGroup 2 (Subgroup.center L))
    (hmap : ((Bs ⊓ L).subgroupOf L).map
      (θ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center L))) = USixTwo.torU K)
    (hBs : IsElemAbelian 3 Bs) (hNT : GGNoTransvection 3 Bs)
    (hcard : Nat.card Bs = 3 ^ 5) (hx : x ∈ Bs) (hxL : x ∉ L)
    (hLx : L ≤ Subgroup.centralizer {x})
    (hW : GGWeylOfType 3 CoxeterMatrix.E₆ (ggAutomizer L Bs ⊔ ggAutomizer K' Bs))
    (hWcard : Nat.card CoxeterMatrix.E₆.Group = 51840) :
    ∃ n ∈ Subgroup.normalizer (Bs : Set G), ∃ h : n * x * n⁻¹ ∈ L,
      θ (QuotientGroup.mk (⟨n * x * n⁻¹, h⟩ : L)) = USixTwo.threeA hω := by
  obtain ⟨ψ, hψA, hψxL, hθψ⟩ :=
    E6QTwo.exists_mem_sup_apply_eq_threeA hK hω θ hZ2 hmap hBs hNT hcard hx hxL hLx hW
      hWcard
  have hψtop : ψ ∈ ggInduced ⊤ Bs :=
    mem_ggInduced_top_of_mem_ggAutomizer
      (sup_le (ggAutomizer_mono Bs le_top) (ggAutomizer_mono Bs le_top) hψA)
  obtain ⟨n, -, hnN, hnψ⟩ := hψtop
  have hmem : n * x * n⁻¹ ∈ L := by
    rw [← hnψ ⟨x, hx⟩]
    exact hψxL
  refine ⟨n, hnN, hmem, ?_⟩
  have hL : (⟨n * x * n⁻¹, hmem⟩ : L) = ⟨((ψ ⟨x, hx⟩ : ↥Bs) : G), hψxL⟩ :=
    Subtype.ext (hnψ ⟨x, hx⟩).symm
  rw [hL]
  exact hθψ

end Conjugate

end CFSG.StandardType

end
