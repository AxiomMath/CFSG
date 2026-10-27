module

public import CFSG.LocalAnalysis.StandardType.GGOneFiveNormalizer
public import CFSG.LocalAnalysis.StandardType.GGUSixTwoModuleTorus

public section

namespace CFSG.StandardType.E6QTwo

open CFSG.Assembly CFSG.Open

variable {G : Type} [Group G] [Finite G]

private theorem isPGroup_torU {K : Type} [Field K] [Finite K] (hK : Nat.card K = 4) :
    IsPGroup 3 (USixTwo.torU K) := by
  obtain ⟨ω, hω⟩ := USixTwo.exists_root_omega hK
  rw [isPGroup_iff_pow_pow_eq_one]
  intro x
  exact ⟨1, Subtype.ext (by
    simpa using congrArg Subtype.val (USixTwo.ModuleProof.torU_pow_three hK hω x))⟩

private theorem not_isCyclic_torU {K : Type} [Field K] [Finite K] (hK : Nat.card K = 4) :
    ¬ IsCyclic (USixTwo.torU K) := by
  intro hcyc
  haveI := hcyc
  obtain ⟨ω, hω⟩ := USixTwo.exists_root_omega hK
  have hdvd : Monoid.exponent ↥(USixTwo.torU K) ∣ 3 :=
    Monoid.exponent_dvd_of_forall_pow_eq_one fun g =>
      USixTwo.ModuleProof.torU_pow_three hK hω g
  rw [IsCyclic.exponent_eq_card, USixTwo.card_torU hK] at hdvd
  have hle : 3 ^ 4 ≤ 3 := Nat.le_of_dvd (by norm_num) hdvd
  norm_num at hle

theorem exists_noncyclic_of_marking_twA5 {L : Subgroup G}
    (hlab : LargeEvenMarking L (fun lab _ _ _ _ _ => lab.tag = .twA ∧ lab.rank = 5 ∧ lab.n = 1)) :
    ∃ S : Subgroup G, S ≤ L ∧ IsPGroup 3 S ∧ ¬ IsCyclic S := by
  classical
  unfold LargeEvenMarking at hlab
  obtain ⟨-, lab, -, hraw⟩ := hlab
  obtain ⟨R₀, _, I₀, F₀, hQ₀⟩ := CFSG.StandardType.Canonical.largeEvenRawDatum_exists hraw
  obtain ⟨-, -, -, hP₀⟩ := hQ₀
  obtain ⟨htag, hrank, hn⟩ := hP₀
  obtain ⟨tag, rank, n⟩ := lab
  obtain rfl : tag = .twA := htag
  obtain rfl : rank = 5 := hrank
  obtain rfl : n = 1 := hn
  dsimp only [LargeEvenRawDatum, LargeEvenRecipeUnitary] at hraw
  obtain ⟨K, hKf, hKfin, hKcard, hQ⟩ := hraw
  obtain ⟨-, -, θ, -⟩ := hQ
  have hK4 : Nat.card K = 4 := by
    rw [hKcard]
    norm_num
  let π : ↥L →* LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1)) :=
    θ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center ↥L))
  have hπ : Function.Surjective π :=
    θ.surjective.comp (QuotientGroup.mk'_surjective _)
  have hnc : ∃ Q : Subgroup ↥L, IsPGroup 3 Q ∧ ¬ IsCyclic Q := by
    haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    let P : Subgroup ↥L := (USixTwo.torU K).comap π
    have hPmap : P.map π = USixTwo.torU K := by
      rw [Subgroup.map_comap_eq, MonoidHom.range_eq_top.mpr hπ, top_inf_eq]
    let φ : ↥P →* ↥(USixTwo.torU K) :=
      (π.comp P.subtype).codRestrict (USixTwo.torU K) (by
        intro x
        show π (P.subtype x) ∈ USixTwo.torU K
        rw [← hPmap]
        exact ⟨(x : ↥L), x.2, rfl⟩)
    have hφ : Function.Surjective φ := by
      intro e
      have he : (e : LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1))) ∈ P.map π := by
        rw [hPmap]
        exact e.2
      obtain ⟨p, hp, hpe⟩ := Subgroup.mem_map.mp he
      exact ⟨⟨p, hp⟩, Subtype.ext hpe⟩
    obtain ⟨Q⟩ := (inferInstance : Nonempty (Sylow 3 ↥P))
    have hQtop : ((Sylow.mapSurjective (f := φ) hφ Q : Sylow 3 ↥(USixTwo.torU K)) :
        Subgroup ↥(USixTwo.torU K)) = ⊤ := by
      refine ((Sylow.mapSurjective (f := φ) hφ Q).is_maximal' (Q := ⊤) ?_ le_top).symm
      exact IsPGroup.to_subgroup (isPGroup_torU hK4) ⊤
    have hQmap : (Q : Subgroup ↥P).map φ = ⊤ := by
      rw [← Sylow.coe_mapSurjective (f := φ) hφ Q]
      exact hQtop
    refine ⟨(Q : Subgroup ↥P).map P.subtype, Q.isPGroup'.map P.subtype, ?_⟩
    intro hScyc
    haveI : IsCyclic ((Q : Subgroup ↥P).map P.subtype) := hScyc
    have hQcyc : IsCyclic ↥Q :=
      isCyclic_of_injective
        (Subgroup.equivMapOfInjective (Q : Subgroup ↥P) P.subtype
          (Subgroup.subtype_injective P)).toMonoidHom
        (Subgroup.equivMapOfInjective (Q : Subgroup ↥P) P.subtype
          (Subgroup.subtype_injective P)).injective
    haveI : IsCyclic ↥Q := hQcyc
    let ψ : ↥Q →* ↥(USixTwo.torU K) := φ.comp (Q : Subgroup ↥P).subtype
    have hψ : Function.Surjective ψ := by
      intro e
      have he : e ∈ (Q : Subgroup ↥P).map φ := by rw [hQmap]; exact Subgroup.mem_top e
      obtain ⟨q, hq, hqe⟩ := Subgroup.mem_map.mp he
      exact ⟨⟨q, hq⟩, hqe⟩
    exact (not_isCyclic_torU hK4) (isCyclic_of_surjective ψ hψ)
  obtain ⟨Q, hQp, hQnc⟩ := hnc
  refine ⟨Q.map L.subtype, Subgroup.map_subtype_le Q, hQp.map L.subtype, ?_⟩
  intro hcyc
  haveI : IsCyclic (Q.map L.subtype) := hcyc
  exact hQnc (isCyclic_of_injective
    (Subgroup.equivMapOfInjective Q L.subtype (Subgroup.subtype_injective L)).toMonoidHom
    (Subgroup.equivMapOfInjective Q L.subtype (Subgroup.subtype_injective L)).injective)

theorem normal_of_sStar_of_marking_twA5 {B : Subgroup G} {x : G} {L : Subgroup G}
    (hS : LargeEvenSStar 3 B x L)
    (hlab : LargeEvenMarking L (fun lab _ _ _ _ _ => lab.tag = .twA ∧ lab.rank = 5 ∧ lab.n = 1)) :
    (L.subgroupOf (Subgroup.centralizer {x})).Normal := by
  have hnc := exists_noncyclic_of_marking_twA5 hlab
  have hLle : L ≤ Subgroup.centralizer ({x} : Set G) := hS.2.2.2.1.1
  rw [Subgroup.normal_subgroupOf_iff_le_normalizer hLle]
  intro g hg
  exact mem_normalizer_of_sstar hS hnc hg

end CFSG.StandardType.E6QTwo

end
