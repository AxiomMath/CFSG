module

public import CFSG.Quasithin.Background.A3Structure39Aut
public import CFSG.Quasithin.Background.A3Structure39Odd
public import CFSG.Quasithin.Background.A3Structure38Part3

public section

namespace CFSG.Quasithin

namespace A38

open CFSG.Open CFSG.SectionRank
open scoped commutatorElement

variable {G : Type} [Group G]

theorem perfectCore_le_normalizer [Finite G] (h37 : A37Statement G) (h38 : A38Part3 G)
    {L : Subgroup G} (hL : L ∈ cComp (⊤ : Subgroup G)) :
    perfectCore (⊤ : Subgroup G) ≤ Subgroup.normalizer (L : Set G) := by
  rcases (h38 L hL).1 with hnorm | ⟨-, t, ht, -, -, hcl⟩
  · rw [Subgroup.normalizer_eq_top_iff.mpr hnorm]
    exact le_top
  · have hconj : ∀ g : G, L.map (MulAut.conj g).toMonoidHom = L ∨
        L.map (MulAut.conj g).toMonoidHom = L.map (MulAut.conj t).toMonoidHom := by
      intro g
      refine eq_or_eq_of_le_sup h37 (cComp_conj hL) hL (cComp_conj hL) ?_
      refine le_trans ?_ hcl.le
      rintro _ ⟨z, hz, rfl⟩
      simpa [MulAut.conj_apply] using mem_conjClosure (Subgroup.mem_top g) hz
    have h2 := index_normalizer_eq_two hconj ht
    have hNn : (Subgroup.normalizer (L : Set G)).Normal := Subgroup.normal_of_index_eq_two h2
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hcyc : IsCyclic (G ⧸ Subgroup.normalizer (L : Set G)) :=
      isCyclic_of_prime_card (p := 2) h2
    have hcomm : ∀ a b : G ⧸ Subgroup.normalizer (L : Set G), a * b = b * a := fun a b =>
      (IsCyclic.commGroup : CommGroup (G ⧸ Subgroup.normalizer (L : Set G))).mul_comm a b
    have hcom : ⁅(⊤ : Subgroup G), (⊤ : Subgroup G)⁆ ≤ Subgroup.normalizer (L : Set G) := by
      refine Subgroup.commutator_le.mpr fun g _ h _ => ?_
      have key : (((⁅g, h⁆ : G) : G ⧸ Subgroup.normalizer (L : Set G))) = 1 := by
        rw [commutatorElement_def, QuotientGroup.mk_mul, QuotientGroup.mk_mul,
          QuotientGroup.mk_mul, QuotientGroup.mk_inv, QuotientGroup.mk_inv,
          hcomm (g : G ⧸ Subgroup.normalizer (L : Set G))
            (h : G ⧸ Subgroup.normalizer (L : Set G))]
        group
      exact (QuotientGroup.eq_one_iff _).mp key
    refine (perfectCore_le_derivedSeriesOf (⊤ : Subgroup G) 1).trans ?_
    rw [derivedSeriesOf_succ, derivedSeriesOf_zero]
    exact hcom

theorem map_normalizer_le {Q : Type} [Group Q] (f : G →* Q) (H : Subgroup G) :
    (Subgroup.normalizer (H : Set G)).map f ≤
      Subgroup.normalizer ((H.map f : Subgroup Q) : Set Q) := by
  rintro _ ⟨g, hg, rfl⟩
  have hg' : ∀ x : G, x ∈ H ↔ g * x * g⁻¹ ∈ H := Subgroup.mem_normalizer_iff.mp hg
  have hginv : ∀ x : G, x ∈ H ↔ g⁻¹ * x * g ∈ H := by
    intro x
    have := hg' (g⁻¹ * x * g)
    simpa [mul_assoc] using this.symm
  show f g ∈ Subgroup.normalizer ((H.map f : Subgroup Q) : Set Q)
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact ⟨g * z * g⁻¹, (hg' z).mp hz, by simp⟩
  · rintro ⟨z', hz', hy⟩
    refine ⟨g⁻¹ * z' * g, (hginv z').mp hz', ?_⟩
    have h2 : f (g⁻¹ * z' * g) = (f g)⁻¹ * f z' * f g := by simp
    rw [h2, hy]
    group

theorem isQuasisimple_quot_oddCore_of_mulEquiv {A B : Type*} [Group A] [Group B] (e : A ≃* B)
    (h : CFSG.IsQuasisimple (A ⧸ CFSG.oddCore A)) : CFSG.IsQuasisimple (B ⧸ CFSG.oddCore B) := by
  have hmap : (CFSG.oddCore A).map e.toMonoidHom = CFSG.oddCore B := by
    rw [oddCore_eq_pPrimeCore_two, oddCore_eq_pPrimeCore_two]
    exact CFSG.pPrimeCore_map_iso 2 e
  exact CFSG.LocalCores.isQuasisimple_of_mulEquiv (QuotientGroup.congr _ _ e hmap) h

theorem a39_part1 (hF : A39Facts) {G : Type} [Group G] (hG : SQTKHyp G)
    (h37 : A37Statement G) (h38 : A38Part3 G) :
    cCompSpan (⊤ : Subgroup G) = perfectCore (⊤ : Subgroup G) := by
  have := hG.finite
  refine le_antisymm (le_perfectCore_of_perfect le_top cCompSpan_perfect) ?_
  rw [(cComp_part_five (G := G)).2]
  refine le_perfectCore_of_perfect ?_ (perfectCore_perfect _)
  show perfectCore (⊤ : Subgroup G) ≤
    (CFSG.layer (G ⧸ CFSG.solvableRadical G)).comap (QuotientGroup.mk' _)
  rw [← Subgroup.map_le_iff_le_comap, map_perfectCore,
    Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)]
  have hRs : Group.IsSolvable (CFSG.solvableRadical G) := A3.solvableRadical_isSolvable
  have hqK : CFSG.SectionRank.IsKGroupCat (G ⧸ CFSG.solvableRadical G) :=
    kGroup_quotient hG.kgroup _
  refine perfectCore_le_layer (A3.solvableRadical_quotient_eq_bot G) ?_ ?_
  · intro K hK
    have hKc : K ∈ cComp (⊤ : Subgroup (G ⧸ CFSG.solvableRadical G)) :=
      mem_cComp_top_of_isComponent hK
    rw [← image_cComp_quotient (CFSG.solvableRadical G) hRs] at hKc
    obtain ⟨L, hL, rfl⟩ := hKc
    have h1 := perfectCore_le_normalizer h37 h38 hL
    have h2 := Subgroup.map_mono (f := QuotientGroup.mk' (CFSG.solvableRadical G)) h1
    rw [map_perfectCore, Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)] at h2
    exact h2.trans (map_normalizer_le _ _)
  · intro K hK
    exact hF ↥K hK.1 (kGroup_subgroup hqK K)

theorem a39_part2 {G : Type} [Group G] (hG : SQTKHyp G) (h36 : A36Statement G) :
    CFSG.layer (↥(cCompSpan (⊤ : Subgroup G)) ⧸ CFSG.oddCore ↥(cCompSpan (⊤ : Subgroup G))) =
      ⊤ := by
  have := hG.finite
  set H := cCompSpan (⊤ : Subgroup G) with hH
  let ρ : ↥H →* ↥H ⧸ CFSG.oddCore ↥H := QuotientGroup.mk' (CFSG.oddCore ↥H)
  have hcomp : ∀ L ∈ cComp (⊤ : Subgroup G), CFSG.IsComponent ((L.subgroupOf H).map ρ) := by
    intro L hL
    obtain ⟨hLH, hLn⟩ := cComp_normal_span hL
    have hq : CFSG.IsQuasisimple (↥(L.subgroupOf H) ⧸ CFSG.oddCore ↥(L.subgroupOf H)) := by
      obtain ⟨hFO, hqs, -⟩ := (h36 L hL).2.1
      have hqs' : CFSG.IsQuasisimple (↥L ⧸ CFSG.oddCore ↥L) :=
        CFSG.LocalCores.isQuasisimple_of_mulEquiv (QuotientGroup.quotientMulEquivOfEq hFO) hqs
      exact isQuasisimple_quot_oddCore_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hLH).symm hqs'
    exact ⟨isQuasisimple_map_oddCore (L.subgroupOf H) hq,
      (Subgroup.Normal.map hLn ρ (QuotientGroup.mk'_surjective _)).isSubnormal⟩
  have hgen : (⨆ L ∈ cComp (⊤ : Subgroup G), L.subgroupOf H) = ⊤ := by
    apply Subgroup.map_injective H.subtype_injective
    rw [Subgroup.map_iSup]
    simp_rw [Subgroup.map_iSup]
    have h1 : ∀ L ∈ cComp (⊤ : Subgroup G), (L.subgroupOf H).map H.subtype = L :=
      fun L hL => Subgroup.map_subgroupOf_eq_of_le (cComp_normal_span hL).1
    have h2 : (⨆ L ∈ cComp (⊤ : Subgroup G), ((L.subgroupOf H).map H.subtype)) = H := by
      calc (⨆ L ∈ cComp (⊤ : Subgroup G), ((L.subgroupOf H).map H.subtype))
          = ⨆ L ∈ cComp (⊤ : Subgroup G), L := by
            refine iSup_congr fun L => iSup_congr fun hL => h1 L hL
        _ = H := (sSup_eq_iSup).symm
    rw [h2, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  rw [eq_top_iff]
  calc (⊤ : Subgroup (↥H ⧸ CFSG.oddCore ↥H)) = (⊤ : Subgroup ↥H).map ρ :=
        (Subgroup.map_top_of_surjective ρ (QuotientGroup.mk'_surjective _)).symm
    _ = (⨆ L ∈ cComp (⊤ : Subgroup G), L.subgroupOf H).map ρ := by rw [hgen]
    _ ≤ CFSG.layer (↥H ⧸ CFSG.oddCore ↥H) := by
        rw [Subgroup.map_iSup]
        refine iSup_le fun L => ?_
        rw [Subgroup.map_iSup]
        exact iSup_le fun hL => le_sSup (hcomp L hL)

theorem a39 (hF : A39Facts) {G : Type} [Group G] (hG : SQTKHyp G) (h36 : A36Statement G)
    (h37 : A37Statement G) (h38 : A38Part3 G) : A39Statement G :=
  ⟨a39_part1 hF hG h37 h38, a39_part2 hG h36⟩

end A38

end CFSG.Quasithin
