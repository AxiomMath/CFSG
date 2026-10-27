module

public import CFSG.LocalAnalysis.StandardType.GGRemTableBLLineUCoverOdd
public import CFSG.LocalAnalysis.StandardType.GGTableBRank
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowY1OutUniRank
public import CFSG.LocalAnalysis.GLTheoremA.CatB.I1015SU6

public section

namespace CFSG.StandardType.TCResidual

open CFSG.Assembly CFSG.Blueprint CFSG.Assembly.LowTwoRank

private theorem ggU62_isElemAbelian_range {A J : Type*} [Group A] [Group J] (Φ : A →* J)
    (hcomm : ∀ x y : A, x * y = y * x) (hexp : ∀ x : A, x ^ 3 = 1) :
    CFSG.Open.IsElemAbelian 3 Φ.range := by
  refine ⟨⟨⟨fun a b => ?_⟩⟩, ?_⟩
  · obtain ⟨x, hx⟩ := MonoidHom.mem_range.mp a.2
    obtain ⟨y, hy⟩ := MonoidHom.mem_range.mp b.2
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, ← hx, ← hy, ← map_mul, ← map_mul, hcomm x y]
  · intro z hz
    obtain ⟨x, rfl⟩ := MonoidHom.mem_range.mp hz
    rw [← map_pow, hexp x, map_one]

private theorem ggU62_mu3_pow_three (K : Type) [Field K]
    (x : Fin 4 → CFSG.LocalAnalysis.GLTheoremA.KD264Lie.kdY1Mu3 K) : x ^ 3 = 1 := by
  funext i
  have h3 : ((x i : CFSG.LocalAnalysis.GLTheoremA.KD264Lie.kdY1Mu3 K) : Kˣ) ^ 3 = 1 :=
    (mem_rootsOfUnity 3 _).mp (x i).2
  apply Subtype.ext
  simpa using h3

section Certificates


theorem ggU62_facts {G : Type} [Group G] [Finite G] {L : Subgroup G} (hperf : commutator ↥L = ⊤)
    (hodd : Odd (Nat.card (Subgroup.center ↥L)))
    (hmod : LieModel (↥L ⧸ Subgroup.center ↥L) .PSU 6 2 1) :
    (∃ E ≤ L, IsElemAbelian 3 E ∧ Nat.card E = 3 ^ 4 ∧
      E ⊓ Subgroup.centralizer (L : Set G) = ⊥) ∧
    (∃ y ∈ L, y ^ 3 = 1 ∧ y ∉ Subgroup.centralizer (L : Set G) ∧
      ∃ s ∈ L, s ≠ 1 ∧ s ^ 2 = 1 ∧ y * s = s * y) := by
  classical
  obtain ⟨-, K, _, _, hK, ⟨θ⟩⟩ := hmod.statedClassicalModel (by decide)
  have hK4 : Nat.card K = 4 := by rw [hK]; norm_num
  have hU : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 2 1 K :=
    ⟨Nat.prime_two, le_rfl, by norm_num [hK4]⟩
  haveI : CharP K 2 := hU.charP
  have hdiv : 3 ∣ 2 ^ 1 + 1 := by norm_num
  have hn : 6 ≤ 6 := le_rfl
  have hcov := LineU.unitaryCoverOddAt_six_two K hK4
  have hker : (ggQuotHom θ).ker = Subgroup.center ↥L := ker_ggQuotHom θ
  obtain ⟨φ, hφ⟩ := hcov.2 ↥L (ggQuotHom θ) (ggQuotHom_surjective θ)
    (le_of_eq hker) hperf (by rw [hker]; exact hodd)
  refine ⟨?_, ?_⟩
  ·
    let g : (Fin 4 → CFSG.LocalAnalysis.GLTheoremA.KD264Lie.kdY1Mu3 K) →*
        ↥(CFSG.ClassicalGroups.UnitaryFlag.unitarySU 2 1 K 6) :=
      CFSG.LocalAnalysis.GLTheoremA.KD264Lie.kdY1UGS hU hdiv (by norm_num : 5 ≤ 6)
    let c : (Fin 4 → CFSG.LocalAnalysis.GLTheoremA.KD264Lie.kdY1Mu3 K) →* G :=
      L.subtype.comp (φ.comp g)
    have hc_inj : Function.Injective c := by
      intro y y' hy
      have h1 : φ (g y) = φ (g y') := Subtype.ext hy
      have h2 : CFSG.LocalAnalysis.GLTheoremA.KD264Lie.kdY1UPhi hU hdiv hn y =
          CFSG.LocalAnalysis.GLTheoremA.KD264Lie.kdY1UPhi hU hdiv hn y' := by
        have hthis := congrArg (ggQuotHom θ) h1
        rw [hφ (g y), hφ (g y')] at hthis
        show LargeEvenProjMk (CFSG.ClassicalGroups.UnitaryFlag.unitarySU 2 1 K 6) (g y) =
          LargeEvenProjMk (CFSG.ClassicalGroups.UnitaryFlag.unitarySU 2 1 K 6) (g y')
        exact hthis
      exact CFSG.LocalAnalysis.GLTheoremA.KD264Lie.kdY1UPhi_injective hU hdiv hn h2
    refine ⟨c.range, ?_, ?_, ?_, ?_⟩
    ·
      rintro x ⟨y, rfl⟩
      exact (φ (g y)).2
    ·
      exact ggU62_isElemAbelian_range c (fun x y => mul_comm x y)
        (fun x => ggU62_mu3_pow_three K x)
    ·
      have h1 : Nat.card c.range =
          Nat.card (Fin 4 → CFSG.LocalAnalysis.GLTheoremA.KD264Lie.kdY1Mu3 K) :=
        Nat.card_range_of_injective hc_inj
      have h2 : Nat.card (Fin 4 → CFSG.LocalAnalysis.GLTheoremA.KD264Lie.kdY1Mu3 K) =
          Nat.card (CFSG.LocalAnalysis.GLTheoremA.KD264Lie.kdY1UPhi hU hdiv hn).range :=
        (Nat.card_range_of_injective
          (CFSG.LocalAnalysis.GLTheoremA.KD264Lie.kdY1UPhi_injective hU hdiv hn)).symm
      rw [h1, h2, CFSG.LocalAnalysis.GLTheoremA.KD264Lie.kdY1UPhi_card hU hdiv hn]
    ·
      rw [eq_bot_iff]
      rintro x ⟨⟨y, rfl⟩, hxc⟩
      have hcy : c y = ((φ (g y) : ↥L) : G) := rfl
      rw [hcy] at hxc
      have hcen : (φ (g y) : ↥L) ∈ Subgroup.center ↥L := by
        rw [Subgroup.mem_center_iff]
        intro l
        apply Subtype.ext
        exact Subgroup.mem_centralizer_iff.mp hxc (l : G) l.2
      have hψ0 : (ggQuotHom θ) (φ (g y)) = 1 := by
        rw [← MonoidHom.mem_ker, hker]
        exact hcen
      have hphi0 : CFSG.LocalAnalysis.GLTheoremA.KD264Lie.kdY1UPhi hU hdiv hn y = 1 := by
        have hthis := hφ (g y)
        rw [hψ0] at hthis
        show LargeEvenProjMk (CFSG.ClassicalGroups.UnitaryFlag.unitarySU 2 1 K 6) (g y) = 1
        exact hthis.symm
      have hy1 : y = 1 :=
        CFSG.LocalAnalysis.GLTheoremA.KD264Lie.kdY1UPhi_injective hU hdiv hn
          (by rw [hphi0, map_one])
      rw [hy1, map_one]
      exact Subgroup.one_mem ⊥
  ·
    obtain ⟨E', s₀, hE'ab, hE'card, hE'bot, -, hs₀2, hs₀not, hs₀comm⟩ :=
      CFSG.LocalAnalysis.GLTheoremA.CatB.I1015.su6_data hK hdiv
    have hE'ne : E' ≠ ⊥ := by
      intro h
      rw [h, Subgroup.card_bot] at hE'card
      norm_num at hE'card
    obtain ⟨⟨y₀, hy₀E'⟩, hy₀ne⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hE'ne
    have hy₀1 : y₀ ≠ 1 := fun h => hy₀ne (Subtype.ext h)
    have hy₀3 : y₀ ^ 3 = 1 := hE'ab.2 y₀ hy₀E'
    have hy₀notscalar : y₀ ∉
        (StatedScalars (Fin 6) K).subgroupOf (StatedSU 6 (2 ^ 1) K) := by
      intro h
      have hmem : y₀ ∈ E' ⊓ (StatedScalars (Fin 6) K).subgroupOf (StatedSU 6 (2 ^ 1) K) :=
        ⟨hy₀E', h⟩
      rw [hE'bot] at hmem
      exact hy₀1 (Subgroup.mem_bot.mp hmem)
    refine ⟨((φ y₀ : ↥L) : G), (φ y₀).2, ?_, ?_,
      ((φ s₀ : ↥L) : G), (φ s₀).2, ?_, ?_, ?_⟩
    ·
      have h1 : (φ y₀ : ↥L) ^ 3 = 1 := by rw [← map_pow, hy₀3, map_one]
      exact congrArg (fun z : ↥L => (z : G)) h1
    ·
      intro hyc
      have hcen : (φ y₀ : ↥L) ∈ Subgroup.center ↥L := by
        rw [Subgroup.mem_center_iff]
        intro l
        apply Subtype.ext
        exact Subgroup.mem_centralizer_iff.mp hyc (l : G) l.2
      have hψ0 : (ggQuotHom θ) (φ y₀) = 1 := by
        rw [← MonoidHom.mem_ker, hker]
        exact hcen
      have hscalar : (QuotientGroup.mk'
          ((StatedScalars (Fin 6) K).subgroupOf (StatedSU 6 (2 ^ 1) K)) y₀ :
            StatedProj (StatedSU 6 (2 ^ 1) K)) = 1 := by
        have hthis := hφ y₀
        rw [hψ0] at hthis
        show LargeEvenProjMk (CFSG.ClassicalGroups.UnitaryFlag.unitarySU 2 1 K 6) y₀ = 1
        exact hthis.symm
      exact hy₀notscalar ((QuotientGroup.eq_one_iff y₀).mp hscalar)
    ·
      intro hs
      have hφs : φ s₀ = 1 := Subtype.ext hs
      have hscalar : (QuotientGroup.mk'
          ((StatedScalars (Fin 6) K).subgroupOf (StatedSU 6 (2 ^ 1) K)) s₀ :
            StatedProj (StatedSU 6 (2 ^ 1) K)) = 1 := by
        have hthis := hφ s₀
        rw [hφs, map_one] at hthis
        show LargeEvenProjMk (CFSG.ClassicalGroups.UnitaryFlag.unitarySU 2 1 K 6) s₀ = 1
        exact hthis.symm
      exact hs₀not ((QuotientGroup.eq_one_iff s₀).mp hscalar)
    ·
      have h1 : (φ s₀ : ↥L) ^ 2 = 1 := by rw [pow_two, ← map_mul, hs₀2, map_one]
      exact congrArg (fun z : ↥L => (z : G)) h1
    ·
      have h1 : (φ y₀ : ↥L) * φ s₀ = φ s₀ * φ y₀ := by
        rw [← map_mul, ← map_mul, hs₀comm y₀ hy₀E']
      exact congrArg (fun z : ↥L => (z : G)) h1

end Certificates

end CFSG.StandardType.TCResidual

end
