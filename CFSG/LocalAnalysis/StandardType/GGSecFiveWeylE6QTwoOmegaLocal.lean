module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylE6QTwoUnitaryAux
public import CFSG.LocalAnalysis.StandardType.GGCorFourTwoOrthNsLabels
public import CFSG.LocalAnalysis.StandardType.GGTableBOrthRestBstar
public import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylE6QTwoOmegaLocalCardAux
public import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylE6QTwoOmegaLocalSubAux
public import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylE6QTwoOmegaLocalAutAux
public import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylE6QTwoOmegaLocalAutAux2
public import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylE6QTwoOmegaLocalAutAux3
public import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylE6QTwoOmegaLocalAutAux4
public import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylE6QTwoOmegaLocalAutAux5
public import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylE6QTwoOmegaLocalAutAux6
public import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylE6QTwoOmegaLocalAutAux7
public import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylE6QTwoOmegaLocalJ
public import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylE6QTwoOmegaLocalRefl

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Open

variable {G : Type} [Group G]

theorem exists_omegaPlusDatum_of_innerDiagOnLabel_D4 {p : ℕ} {Bs L : Subgroup G}
    (hlab : GGInnerDiagOnLabel (fun _ lab => lab.tag = .D ∧ lab.rank = 4 ∧ lab.n = 1)
      p Bs L) :
    commutator ↥L = ⊤ ∧
      ∃ (K : Type) (_ : Field K) (_ : Finite K)
        (θ : L ⧸ Subgroup.center L ≃* OrthRest.RPlus K 4),
        Nat.card K = 2 ∧ Bs ≤ Subgroup.normalizer (L : Set G) ∧
          ∀ b ∈ Bs, ∃ φ ∈ LargeEvenInnSet (OrthRest.RPlus K 4),
            LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) φ := by
  obtain ⟨hperf, lab, -, hraw⟩ := hlab
  obtain ⟨t, r, n⟩ := lab
  obtain ⟨R₀, _, I₀, F₀, -, -, -, hlabS, -⟩ := largeEvenRawDatum_exists hraw
  obtain ⟨rfl, rfl, rfl⟩ := hlabS
  dsimp only [LargeEvenRawDatumLegacy, LargeEvenRecipeOmegaPlus] at hraw
  obtain ⟨K, hfieldK, hfiniteK, hKcard, hQ⟩ := hraw
  obtain ⟨-, -, θ, -, hBsN, hI⟩ := hQ
  exact ⟨hperf, K, hfieldK, hfiniteK, θ, by rw [hKcard]; norm_num, hBsN, hI⟩

theorem E6QTwo.isPGroup_two_center_of_omegaPlus
    [Finite G] {K : Type} [Field K]
    [Finite K] (hK : Nat.card K = 2) {L : Subgroup G}
    (θ : L ⧸ Subgroup.center L ≃* OrthRest.RPlus K 4) (hperf : commutator ↥L = ⊤) :
    IsPGroup 2 (Subgroup.center L) := by
  haveI : CharP K 2 := CFSG.TauCetiBridge.charP_two_of_card_eq_two_pow (f := 1) (by rw [hK]; rfl)
  let ψ : ↥L →* OrthRest.RPlus K 4 :=
    θ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center L))
  have hψ : Function.Surjective ψ :=
    θ.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : ψ.ker ≤ Subgroup.center ↥L := by
    intro l hl
    have h1 : θ (QuotientGroup.mk' (Subgroup.center L) l) = 1 := hl
    rw [map_eq_one_iff _ θ.injective, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    exact h1
  have hodd : ∀ q : ℕ, q.Prime → q ∣ Nat.card (Subgroup.center L) → q = 2 := by
    intro q hq hdvd
    by_contra hq2
    exact (OrthNs.center_data_omegaPlus (K := K) hq hq2 (by norm_num : 3 ≤ 4)).2 ↥L ψ hψ hker
      hperf hdvd
  have hpos : Nat.card (Subgroup.center L) ≠ 0 := Nat.card_pos.ne'
  exact IsPGroup.of_card (Nat.eq_prime_pow_of_unique_prime_dvd hpos fun hq hdvd => hodd _ hq hdvd)

section Leaves

variable [Finite G] {K : Type} [Field K] [Finite K]

theorem E6QTwo.hasLabel_and_ggAutomizer_of_omegaPlus (hK : Nat.card K = 2) {Bs L : Subgroup G}
    {x : G} (θ : L ⧸ Subgroup.center L ≃* OrthRest.RPlus K 4) (hperf : commutator ↥L = ⊤)
    (hZ2 : IsPGroup 2 (Subgroup.center L)) (hBs : IsElemAbelian 3 Bs)
    (hcard : Nat.card Bs = 3 ^ 5) (hcardE : Nat.card ↥(Bs ⊓ L) = 3 ^ 4) (hx1 : x ≠ 1)
    (hLx : L ≤ Subgroup.centralizer {x})
    (hBL : Bs ⊓ Subgroup.centralizer (L : Set G) = Subgroup.zpowers x)
    (hstar : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ 3 = 1 → g ∈ Bs)
    (hBsN : Bs ≤ Subgroup.normalizer (L : Set G))
    (hI : ∀ b ∈ Bs, ∃ φ ∈ LargeEvenInnSet (OrthRest.RPlus K 4),
      LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) φ)
    {D J : Subgroup G} (hDB : D ≤ Bs) (hDcard : Nat.card D = 3 ^ 2) (hxD : x ∈ D)
    (hJ : CFSG.Assembly.IsComponentOf J (L ⊓ Subgroup.centralizer (D : Set G))) :
    GGHasLabel ⟨.twA, 3, 1⟩ (J ⧸ Subgroup.center J) ∧
      (∀ ψ ∈ ggAutomizer L Bs, (∀ d : ↥Bs, (d : G) ∈ D → ψ d = d) → ψ ∈ ggAutomizer J Bs) ∧
      6 ≤ Set.ncard {r : MulAut ↥Bs | r ∈ ggAutomizer L Bs ∧ GGIsReflection 3 r ∧
        ∀ d : ↥Bs, (d : G) ∈ D → r d = d} := by
  refine ⟨exists_label_of_component_omegaPlus hK θ hperf hZ2 hBs hcard hcardE hx1 hLx hBL hstar
    hBsN hI hDB hDcard hxD hJ, E6QTwo.mem_ggAutomizer_of_fix_omegaPlus hK θ hperf hZ2 hBs hcard
    hcardE hx1 hLx hBL hstar hBsN hI hDB hDcard hxD hJ, ?_⟩
  obtain ⟨e, heD, heL, he1, hDe⟩ :=
    E6QTwo.exists_mem_inf_eq_sup_of_omegaPlus hZ2 hBs hcard hcardE hx1 hLx hBL hDB hDcard hxD
  have heBs : e ∈ Bs := hDB heD
  have hxBs : x ∈ Bs := hDB hxD
  refine (E6QTwo.six_le_ncard_isReflection_fix_of_omegaPlus hK θ hZ2 hBs hcard hcardE hx1
    hLx hBL hstar heBs heL (E6QTwo.finrank_fixedSpace_omPlusLin_of_component hK θ hperf
      hZ2 hBs hcard hcardE hx1 hLx hBL hstar hBsN hI hDB hDcard hxD hJ heD heL he1)).trans
    (Set.ncard_le_ncard ?_ (Set.toFinite _))
  rintro r ⟨hrL, hr, hre⟩
  refine ⟨hrL, hr, fun d hd => ?_⟩
  have hrx : r ⟨x, hxBs⟩ = ⟨x, hxBs⟩ := ggAutomizer_apply_eq_of_le_centralizer hLx hrL
  have hle : D.subgroupOf Bs ≤ (Subgroup.zpowers (⟨x, hxBs⟩ : ↥Bs) ⊔
      Subgroup.zpowers (⟨e, heBs⟩ : ↥Bs)) := by
    intro b hb
    rw [Subgroup.mem_subgroupOf, hDe] at hb
    have hmap : (Subgroup.zpowers (⟨x, hxBs⟩ : ↥Bs) ⊔ Subgroup.zpowers (⟨e, heBs⟩ : ↥Bs)).map
        Bs.subtype = Subgroup.zpowers x ⊔ Subgroup.zpowers e := by
      rw [Subgroup.map_sup, MonoidHom.map_zpowers, MonoidHom.map_zpowers]
      rfl
    rw [← hmap] at hb
    obtain ⟨b', hb', hbb'⟩ := hb
    rwa [Subtype.ext hbb'] at hb'
  have hfix : Subgroup.zpowers (⟨x, hxBs⟩ : ↥Bs) ⊔ Subgroup.zpowers (⟨e, heBs⟩ : ↥Bs) ≤
      (r.toMonoidHom).eqLocus (MonoidHom.id ↥Bs) :=
    sup_le (Subgroup.zpowers_le.mpr hrx) (Subgroup.zpowers_le.mpr hre)
  exact hfix (hle (Subgroup.mem_subgroupOf.mpr hd))

end Leaves

end CFSG.StandardType

end
