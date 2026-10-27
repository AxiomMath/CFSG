module

public import CFSG.RankThree.Coprime.EvenCenterSectionCover
public import CFSG.Foundations.Catalog
import CFSG.RankThree.PartTwo.Setup
import CFSG.RankThree.OddKernel.ThreeComplementQuotient
import CFSG.RankThree.PartOne.S10.EmbeddingTransport
import CFSG.RankThree.PartOne.N143.CaseB1Theta

public section

namespace CFSG.RankThree.PartOne.N143

open Subgroup CFSG
open CFSG.Assembly.RankThreeEven (localRank)

theorem section_cover_central_of_high_two_rank {G : Type} [Group G] [Finite G] (m : ℕ)
    (he : CFSG.Assembly.evenRank G ≤ m) (hKG : CFSG.IsKGroup G)
    {M : Type} [Group M] [Finite M] (hM : CFSG.IsQuasisimple M)
    (hS : ∃ U : Subgroup (M ⧸ center M), IsElementaryAbelian 2 U ∧ Nat.card U = 2 ^ (m + 2))
    (H : Subgroup G) (π : H →* M) (hπ : Function.Surjective π) :
    ∃ (Y : Type) (_ : Group Y) (_ : Finite Y) (φ : Y →* M ⧸ center M),
      Group.IsPerfect Y ∧ CFSG.IsKGroup Y ∧ CFSG.Assembly.evenRank Y ≤ m ∧
        Function.Surjective φ ∧ φ.ker ≤ center Y ∧ Odd (Nat.card φ.ker) ∧
        ∀ ℓ : ℕ, ℓ.Prime → ℓ ≠ 2 → ℓ ∣ Nat.card (center M) → ℓ ∣ Nat.card φ.ker := by
  classical
  obtain ⟨K, -, hKmin⟩ := Finite.exists_le_minimal (p := fun K : Subgroup H => K.map π = ⊤)
    (a := ⊤) (by rw [Subgroup.map_top_of_surjective π hπ])
  set πK : K →* M := π.comp K.subtype with hπK
  have hπKs : Function.Surjective πK := by
    intro x
    have hx : x ∈ K.map π := by
      rw [hKmin.prop]
      exact mem_top x
    obtain ⟨k, hk, rfl⟩ := hx
    exact ⟨⟨k, hk⟩, rfl⟩
  have hmin : ∀ Y : Subgroup K, Y ≠ ⊤ → Y.map πK ≠ ⊤ := by
    intro Y hY hYmap
    apply hY
    have h1 : (Y.map K.subtype).map π = ⊤ := by
      rw [Subgroup.map_map]
      exact hYmap
    have h2 := hKmin.le_of_le h1 (Subgroup.map_subtype_le Y)
    rw [eq_top_iff]
    intro y _
    obtain ⟨y', hy', hyy⟩ := h2 y.2
    rwa [show y' = y from Subtype.ext hyy] at hy'
  obtain ⟨hKperf, hCn, hCnil, hCsyl, -, -, -, -, -⟩ :=
    CFSG.SectionRank.minimal_semisimple_cover
      (CFSG.RankThree.Coprime.layer_eq_top_of_isQuasisimple hM) πK hπKs hmin
  set C : Subgroup K := (center M).comap πK with hC
  have hCZ : Function.Surjective ((πK.comp C.subtype).codRestrict (center M)
      (fun x => x.2)) := by
    intro z
    obtain ⟨k, hk⟩ := hπKs z
    exact ⟨⟨k, show πK k ∈ center M by rw [hk]; exact z.2⟩, Subtype.ext hk⟩
  have hZC : Nat.card (center M) ∣ Nat.card C := Subgroup.card_dvd_of_surjective hCZ
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set T : Sylow 2 C := default with hT
  set R : Subgroup K := (T : Subgroup C).map C.subtype with hR
  have hRn : R.Normal := hCsyl 2 T
  have hRp : IsPGroup 2 R := T.isPGroup'.map _
  have hRC : R ≤ C := Subgroup.map_subtype_le _
  have hRr : ∀ r : ℕ, r.Prime → r ≠ 2 → ¬ r ∣ Nat.card R := by
    intro r hr hr2 hdvd
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hRp
    rw [hk] at hdvd
    exact hr2 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).mp (hr.dvd_of_dvd_pow hdvd))
  have hYe : CFSG.Assembly.evenRank (K ⧸ R) ≤ m := by
    refine CFSG.RankThree.OddKernel.evenRank_le_of_localRank_le fun r hr hr2 => ?_
    calc localRank r (K ⧸ R) ≤ localRank r K :=
          CFSG.RankThree.Classical2.localRank_quotient_le hr hr2 R (hRr r hr hr2)
      _ ≤ localRank r H := CFSG.RankThree.PartTwo.localRank_subgroup_le hr K
      _ ≤ localRank r G := CFSG.RankThree.PartTwo.localRank_subgroup_le hr H
      _ ≤ CFSG.Assembly.evenRank G := CFSG.RankThree.OddKernel.localRank_le_evenRank hr hr2
      _ ≤ m := he
  have hRker : R ≤ ((QuotientGroup.mk' (center M)).comp πK).ker := by
    intro x hx
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff]
    exact hRC hx
  set φ : K ⧸ R →* M ⧸ center M :=
    QuotientGroup.lift R ((QuotientGroup.mk' (center M)).comp πK) hRker with hφ
  have hφs : Function.Surjective φ := by
    intro q
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (center M) q
    obtain ⟨k, rfl⟩ := hπKs x
    exact ⟨QuotientGroup.mk k, rfl⟩
  have hφker : φ.ker = C.map (QuotientGroup.mk' R) := by
    rw [hφ, QuotientGroup.ker_lift, ← MonoidHom.comap_ker, QuotientGroup.ker_mk']
  have hkernil : Group.IsNilpotent φ.ker := by
    rw [hφker]
    exact Group.nilpotent_of_surjective _ ((QuotientGroup.mk' R).subgroupMap_surjective C)
  have hsub : R.subgroupOf C = (T : Subgroup C) := by
    rw [hR, subgroupOf, comap_map_eq_self_of_injective C.subtype_injective]
  have hkerodd : Odd (Nat.card φ.ker) := by
    rw [hφker, CFSG.natCard_map_mk'_eq, hsub, ← Subgroup.index_eq_card]
    exact Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp T.not_dvd_index)
  have hCcard : Nat.card C = Nat.card φ.ker * Nat.card R := by
    have h1 : Nat.card (R.subgroupOf C) = Nat.card R := by
      rw [hsub, hR, Subgroup.card_map_of_injective C.subtype_injective]
    have h2 : Nat.card φ.ker = (R.subgroupOf C).index := by
      rw [hφker, CFSG.natCard_map_mk'_eq, Subgroup.index_eq_card]
    rw [h2, ← h1, mul_comm]
    exact (Subgroup.card_mul_index _).symm
  have hYperf : Group.IsPerfect (K ⧸ R) := inferInstance
  have : IsSimpleGroup (M ⧸ center M) := hM.2.1
  set iso := QuotientGroup.quotientKerEquivOfSurjective φ hφs with hiso
  have hsimple : IsSimpleGroup ((K ⧸ R) ⧸ φ.ker) := iso.isSimpleGroup
  have hnonab : ∃ a b : (K ⧸ R) ⧸ φ.ker, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hM.2.2
    refine ⟨iso.symm a, iso.symm b, fun h => hab ?_⟩
    have := congrArg iso h
    simpa using this
  obtain ⟨U, hU, hUcard⟩ := hS
  obtain ⟨hU', hUcard'⟩ := CFSG.RankThree.Coprime.isElementaryAbelian_map_mulEquiv iso.symm hU
  have hcent : φ.ker ≤ center (K ⧸ R) :=
    CFSG.RankThree.Coprime.high_two_rank_simple_odd_kernel_centralization m hYperf hYe φ.ker
      hkernil hkerodd hsimple hnonab ⟨_, hU', hUcard'.trans hUcard⟩
  have hYK : CFSG.IsKGroup (K ⧸ R) :=
    CFSG.RankThree.PartOne.EmbeddingTransport.isKGroup_quotient (isKGroup_subgroup (isKGroup_subgroup hKG H) K) R
  refine ⟨K ⧸ R, inferInstance, inferInstance, φ, hYperf, hYK, hYe, hφs, hcent, hkerodd, ?_⟩
  intro ℓ hℓ hℓ2 hℓZ
  have h1 : ℓ ∣ Nat.card φ.ker * Nat.card R := hCcard ▸ hℓZ.trans hZC
  exact (hℓ.dvd_mul.mp h1).resolve_right (hRr ℓ hℓ hℓ2)

end CFSG.RankThree.PartOne.N143
