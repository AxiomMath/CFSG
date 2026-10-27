module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection6.PFsection6_4
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection5.PFsection5_6
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection5.PFsection5_7
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection1.PFsection1_6
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection1.PFsection1_7_Core
import CFSG.ThirdParty.QiuzhenCFSG.Theory.Character.DegreeBounds
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection6.PFsection6_5_a
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection6.PFsection6_5_b
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection6.PFsection6_5_c

namespace CFSG
end CFSG
open CFSG

noncomputable section

open scoped Classical commutatorElement

attribute [local instance] Fintype.ofFinite

namespace CFSG.Section6

universe u v
open Section1 Section2 Section3 Section4

@[expose] public def theorem_6_6_statement
    {L : Type u} [Group L] [Finite L]
    {G : Type u} [Group G] [Finite G]
    (K H1 Z : Subgroup L)
    (S SZ Xset : Finset (Section1.ClassFunction L))
    (T : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G) : Prop :=
  hypothesis_6_4_statement K ⊥ H1 S T →
    Z ≠ ⊥ →
      Z ≤ centerIn K →
        Z.Normal →
          inducedKernelFamily K Z SZ →
            Xset = S \ SZ →
              (∀ χ : Section1.ClassFunction L, χ ∈ Xset →
                Section1.IsIrreducibleCharacterOnGroup χ) →
                (∀ χ : Section1.ClassFunction L, χ ∈ Xset ↔
                  Section1.IsIrreducibleCharacterOnGroup χ ∧
                    ¬ Section1.subgroupInKernel' χ Z) ∧
                  coherentFamily Xset T

/-- Peterfalvi `(6.7)`. -/
@[expose] public def theorem_6_7_base_hypothesis
    {G : Type u} [Group G] [Finite G]
    (p : ℕ) [Fact p.Prime]
    (P : Sylow p G) (L Z : Subgroup G) : Prop :=
  L = Subgroup.normalizer (((P : Subgroup G) : Set G)) ∧
    Odd (Nat.card L) ∧
      Section2.IsTISubsetWithNormalizer
          ({g : G | g ∈ (P : Subgroup G) ∧ g ≠ 1}) L ∧
        Z ≠ ⊥ ∧
          Z ≤ centerIn (P : Subgroup G) ∧
            (∃ _hZL : Z ≤ L, (Z.subgroupOf L).Normal) ∧
              constantCentralizerOrderOnNonidentity Z L

@[expose] public def theorem_6_7_hypothesis
    {G : Type u} [Group G] [Finite G]
    (p : ℕ) [Fact p.Prime]
    (P : Sylow p G) (L Z : Subgroup G)
    (ψ : Section1.ClassFunction G) : Prop :=
  theorem_6_7_base_hypothesis p P L Z ∧
    Section1.IsIrreducibleCharacterOnGroup ψ ∧
      constantOnNonidentitySubgroup Z ψ

/-- Peterfalvi `(6.7.1)`. -/
@[expose] public def theorem_6_7_1_statement
    {G : Type u} [Group G] [Finite G]
    (p : ℕ) [Fact p.Prime]
    (P : Sylow p G) (L Z : Subgroup G)
    (a : ConjClasses G → ConjClasses G → ConjClasses G → ℕ) : Prop :=
  theorem_6_7_base_hypothesis p P L Z →
    classProductCoefficientData a →
      ∀ i j s : ConjClasses G,
        conjugacyClassMeetsPuncturedSubgroup i Z →
          conjugacyClassMeetsPuncturedSubgroup j Z →
            conjugacyClassDisjointFromSubgroup s Z →
              algebraicIntegerCongruentModNat (Nat.card (P : Subgroup G))
                ((a i j s * Nat.card s.carrier : ℕ) : ℂ) 0

/-- Peterfalvi `(6.7.2)`. -/
@[expose] public def theorem_6_7_2_statement
    {G : Type u} [Group G] [Finite G]
    (p : ℕ) [Fact p.Prime]
    (P : Sylow p G) (L Z : Subgroup G)
    (ψ : Section1.ClassFunction G)
    (a : ConjClasses G → ConjClasses G → ConjClasses G → ℕ)
    (α : ℂ) : Prop :=
  theorem_6_7_hypothesis p P L Z ψ →
    classProductCoefficientData a →
      theorem_6_7_alphaData Z ψ α →
        ∀ i j : ConjClasses G,
          conjugacyClassMeetsPuncturedSubgroup i Z →
            conjugacyClassMeetsPuncturedSubgroup j Z →
              algebraicIntegerCongruentModNat (Nat.card (P : Subgroup G))
                (ψ 1 * α ^ 2)
                (ψ 1 * ((a i j (ConjClasses.mk (1 : G)) : ℂ) +
                  (theorem_6_7_aij Z a i j : ℂ) * α))

/-- Peterfalvi `(6.7.3)`. -/
@[expose] public def theorem_6_7_3_statement
    {G : Type u} [Group G] [Finite G]
    (p : ℕ) [Fact p.Prime]
    (P : Sylow p G) (L Z : Subgroup G)
    (ψ : Section1.ClassFunction G) : Prop :=
  theorem_6_7_hypothesis p P L Z ψ →
    ∀ z : Z, z ≠ 1 →
      algebraicIntegerCongruentModNat (Nat.card (P : Subgroup G)) (ψ z) (ψ 1)

/-- Peterfalvi `(6.7)`. -/


theorem theorem_6_6_centerIn_le
    {L : Type u} [Group L] {K Z : Subgroup L}
    (hZcenter : Z ≤ centerIn K) :
    Z ≤ K := by
  intro z hz
  exact (show z ∈ K ∧ z ∈ Subgroup.centralizer (K : Set L) from by
    simpa [centerIn] using hZcenter hz).1

public theorem theorem_6_6_mem_SZ_subgroupInKernel
    {L : Type u} [Group L] [Finite L]
    {K Z : Subgroup L} [K.Normal]
    {SZ : Finset (Section1.ClassFunction L)}
    (hZnorm : Z.Normal) (hZleK : Z ≤ K)
    (hSZ : inducedKernelFamily K Z SZ)
    {χ : Section1.ClassFunction L}
    (hχSZ : χ ∈ SZ) :
    Section1.subgroupInKernel' χ Z := by
  classical
  rcases (hSZ.2 χ).mp hχSZ with ⟨θ, hθirr, hθker, _hθne, hχeq⟩
  rcases hθirr with ⟨n, ρ, hρirr, hθeq⟩
  have : Z.Normal := hZnorm
  have hχker : Section1.subgroupInKernel' (Section1.inducedCF K ρ.character) Z :=
    (Section1.proposition_1_6_a K Z hZleK ρ).mp (by
      simpa [hθeq] using hθker)
  simpa [hχeq, hθeq] using hχker

theorem theorem_6_6_mem_diff_not_subgroupInKernel
    {L : Type u} [Group L] [Finite L]
    {K Z : Subgroup L} [K.Normal]
    {S SZ : Finset (Section1.ClassFunction L)}
    (hZnorm : Z.Normal) (hZleK : Z ≤ K)
    (hS : inducedKernelFamily K ⊥ S)
    (hSZ : inducedKernelFamily K Z SZ)
    {χ : Section1.ClassFunction L}
    (hχS : χ ∈ S) (hχnotSZ : χ ∉ SZ) :
    ¬ Section1.subgroupInKernel' χ Z := by
  classical
  intro hχZ
  rcases (hS.2 χ).mp hχS with ⟨θ, hθirr, _hθbot, hθne, hχeq⟩
  rcases hθirr with ⟨n, ρ, hρirr, hθeq⟩
  have : Z.Normal := hZnorm
  have hθkerZ : Section1.subgroupInKernel' θ (Z.subgroupOf K) := by
    rw [hθeq]
    apply (Section1.proposition_1_6_a K Z hZleK ρ).mpr
    simpa [hχeq, hθeq] using hχZ
  exact hχnotSZ ((hSZ.2 χ).mpr ⟨θ, ⟨n, ρ, hρirr, hθeq⟩, hθkerZ, hθne, hχeq⟩)

public theorem theorem_6_6_diff_conjugate_closed
    {L : Type u} [Group L] [Finite L]
    {K Z : Subgroup L} [K.Normal]
    {S SZ Xset : Finset (Section1.ClassFunction L)}
    (hS : inducedKernelFamily K ⊥ S)
    (hSZ : inducedKernelFamily K Z SZ)
    (hXeq : Xset = S \ SZ) :
    ∀ χ : Section1.ClassFunction L, χ ∈ Xset →
      Section1.conjugateCharacter χ ∈ Xset := by
  intro χ hχX
  have hχdiff : χ ∈ S \ SZ := by
    simpa [hXeq] using hχX
  have hχS : χ ∈ S := (Finset.mem_sdiff.mp hχdiff).1
  have hχnotSZ : χ ∉ SZ := (Finset.mem_sdiff.mp hχdiff).2
  have hbarS : Section1.conjugateCharacter χ ∈ S :=
    inducedKernelFamily_conjugate_mem hS hχS
  have hbarNotSZ : Section1.conjugateCharacter χ ∉ SZ := by
    intro hbarSZ
    have hback : Section1.conjugateCharacter (Section1.conjugateCharacter χ) ∈ SZ :=
      inducedKernelFamily_conjugate_mem hSZ hbarSZ
    have hcc : Section1.conjugateCharacter (Section1.conjugateCharacter χ) = χ := by
      ext g
      simp [Section1.conjugateCharacter]
    exact hχnotSZ (by simpa [hcc] using hback)
  simpa [hXeq] using Finset.mem_sdiff.mpr ⟨hbarS, hbarNotSZ⟩

public theorem theorem_6_6_mem_Xset_of_mem_S_not_subgroupInKernel
    {L : Type u} [Group L] [Finite L]
    {K Z : Subgroup L} [K.Normal]
    {S SZ Xset : Finset (Section1.ClassFunction L)}
    (hZnorm : Z.Normal) (hZleK : Z ≤ K)
    (hSZ : inducedKernelFamily K Z SZ)
    (hXeq : Xset = S \ SZ)
    {χ : Section1.ClassFunction L}
    (hχS : χ ∈ S) (hχnotker : ¬ Section1.subgroupInKernel' χ Z) :
    χ ∈ Xset := by
  have hχnotSZ : χ ∉ SZ := by
    intro hχSZ
    exact hχnotker
      (theorem_6_6_mem_SZ_subgroupInKernel hZnorm hZleK hSZ hχSZ)
  simpa [hXeq, hχnotSZ] using hχS

theorem theorem_6_6_isClassFunction_of_irreducibleCharacterOnGroup
    {L : Type u} [Group L] [Finite L]
    {χ : Section1.ClassFunction L}
    (hχ : Section1.IsIrreducibleCharacterOnGroup χ) :
    Section1.IsClassFunction χ := by
  rcases hχ with ⟨n, ρ, _hρirr, rfl⟩
  intro x g
  simpa [mul_assoc] using Representation.char_conj (ρ := ρ) g x

theorem theorem_6_6_scalarProduct_irreducible_ne
    {L : Type u} [Group L] [Finite L]
    {φ ψ : Section1.ClassFunction L}
    (hφ : Section1.IsIrreducibleCharacterOnGroup φ)
    (hψ : Section1.IsIrreducibleCharacterOnGroup ψ)
    (hne : φ ≠ ψ) :
    Section1.scalarProduct L φ ψ = 0 := by
  rcases hφ with ⟨nφ, ρφ, hρφ, hφchar⟩
  rcases hψ with ⟨nψ, ρψ, hρψ, hψchar⟩
  exact Section1.scalarProduct_irreducible_representationCharacter_eq_zero_of_ne
    φ ψ ρφ ρψ hφchar hψchar hρφ hρψ hne

theorem theorem_6_6_scalarProduct_self_irreducible
    {L : Type u} [Group L] [Finite L]
    {χ : Section1.ClassFunction L}
    (hχ : Section1.IsIrreducibleCharacterOnGroup χ) :
    Section1.scalarProduct L χ χ = 1 := by
  rcases hχ with ⟨_n, ρ, hρirr, hχchar⟩
  rw [hχchar]
  exact (Theory.Character.irreducible_iff_character_norm_one (ρ := ρ)).1 hρirr

theorem theorem_6_6_cfNormSq_irreducible
    {L : Type u} [Group L] [Finite L]
    {χ : Section1.ClassFunction L}
    (hχ : Section1.IsIrreducibleCharacterOnGroup χ) :
    Section5.cfNormSq χ = 1 := by
  unfold Section5.cfNormSq
  rw [theorem_6_6_scalarProduct_self_irreducible hχ]
  simp

public theorem theorem_6_6_positive_degree_nat_of_irreducible
    {L : Type u} [Group L] [Finite L]
    {χ : Section1.ClassFunction L}
    (hχ : Section1.IsIrreducibleCharacterOnGroup χ) :
    ∃ d : ℕ, 0 < d ∧ Section1.degree χ = (d : ℂ) := by
  rcases hχ with ⟨n, ρ, hρirr, hχchar⟩
  refine ⟨n, ?_, ?_⟩
  · by_contra hn
    have hn0 : n = 0 := Nat.eq_zero_of_not_pos hn
    have hdeg : Section1.degree χ = 0 := by
      simp [hχchar, Section1.degree_representation_character ρ, hn0]
    exact
      (Section3.degree_ne_zero_of_isIrreducibleCharacterOnGroup χ
        ⟨n, ρ, hρirr, hχchar⟩) hdeg
  · rw [hχchar]
    simpa using Section1.degree_representation_character ρ

public theorem theorem_6_6_isPGroup_of_nonabelianPQuotient_bot
    {L : Type u} [Group L] [Finite L]
    {K : Subgroup L} {p : ℕ}
    (hpQ : nonabelianPQuotient (⊥ : Subgroup L) K p) :
    IsPGroup p K := by
  rcases hpQ with
    ⟨_hbotK, _hbotnormK, _hbotnorm, _hKnorm, hpprime, hQp, _hnoncomm⟩
  have : Fact p.Prime := ⟨hpprime⟩
  have hbot_sub : (⊥ : Subgroup L).subgroupOf K = (⊥ : Subgroup K) := by
    ext x
    simp
  let e : K ⧸ (⊥ : Subgroup L).subgroupOf K ≃* K :=
    (QuotientGroup.quotientMulEquivOfEq hbot_sub).trans QuotientGroup.quotientBot
  exact hQp.of_equiv e

-- Keep `Z` in the public signature for compatibility with existing named calls.
set_option linter.unusedVariables false in
public theorem theorem_6_6_degree_eq_relIndex_mul_prime_power
    {L : Type u} [Group L] [Finite L]
    {K Z : Subgroup L}
    {S SZ Xset : Finset (Section1.ClassFunction L)}
    (hSbot : inducedKernelFamily K ⊥ S)
    (hXeq : Xset = S \ SZ)
    {p : ℕ}
    (hpQ : nonabelianPQuotient (⊥ : Subgroup L) K p)
    {χ : Section1.ClassFunction L} (hχX : χ ∈ Xset) :
  ∃ a dχ : ℕ,
      Section1.degree χ = (dχ : ℂ) ∧
        dχ = K.relIndex (⊤ : Subgroup L) * p ^ a := by
  classical
  rcases hpQ with
    ⟨_hbotK, _hbotnormK, _hbotnorm, _hKnorm, hpprime, hQp, _hnoncomm⟩
  have : Fact p.Prime := ⟨hpprime⟩
  have hKp : IsPGroup p K := by
    exact theorem_6_6_isPGroup_of_nonabelianPQuotient_bot
      (K := K)
      ⟨_hbotK, _hbotnormK, _hbotnorm, _hKnorm, hpprime, hQp, _hnoncomm⟩
  rcases hKp.exists_card_eq with ⟨m, hKcard⟩
  have hχS : χ ∈ S := by
    have hχdiff : χ ∈ S \ SZ := by
      simpa [hXeq] using hχX
    exact (Finset.mem_sdiff.mp hχdiff).1
  rcases (hSbot.2 χ).mp hχS with ⟨θ, hθirr, _hθker, _hθne, hχeq⟩
  rcases hθirr with ⟨dθ, ρ, hρirr, hθeq⟩
  have hdθ_dvd : dθ ∣ Nat.card K := by
    let : Representation.IsIrreducible ρ := hρirr
    simpa using Theory.Character.irreducible_dimension_dvd_group_order ρ
  have hKcardF : Fintype.card K = p ^ m := by
    simpa [Nat.card_eq_fintype_card] using hKcard
  have hdθ_dvd_pow : dθ ∣ p ^ m := by
    simpa [hKcardF, Nat.card_eq_fintype_card] using hdθ_dvd
  rcases (Nat.dvd_prime_pow hpprime).1 hdθ_dvd_pow with
    ⟨a, _ham, hdθ⟩
  refine ⟨a, K.relIndex (⊤ : Subgroup L) * p ^ a, ?_, rfl⟩
  rw [hχeq, Section1.degree_inducedClassFunction K θ]
  rw [hθeq, Section1.degree_representation_character]
  simp [Subgroup.relIndex_top_right, Nat.cast_mul, hdθ]

theorem theorem_6_6_centralModulo_bot_of_centerIn
    {L : Type u} [Group L] {K Z : Subgroup L}
    (hZcenter : Z ≤ centerIn K) :
    Theory.Character.IsCentralModulo (⊥ : Subgroup K) (Z.subgroupOf K) := by
  intro d hd c
  change ⁅d, c⁆ = 1
  apply Subtype.ext
  change ⁅(d : L), (c : L)⁆ = 1
  have hcent := (hZcenter (show (d : L) ∈ Z from hd)).2
  have hcomm : (d : L) * (c : L) = (c : L) * (d : L) := by
    exact (Subgroup.mem_centralizer_iff.mp hcent (c : L) c.2).symm
  rw [commutatorElement_eq_one_iff_commute]
  exact hcomm

theorem theorem_6_6_degree_eq_relIndex_mul_prime_power_sq_dvd_Zrel
    {L : Type u} [Group L] [Finite L]
    {K Z : Subgroup L}
    {S SZ Xset : Finset (Section1.ClassFunction L)}
    (hSbot : inducedKernelFamily K ⊥ S)
    (hXeq : Xset = S \ SZ)
    (hZnorm : Z.Normal) (hZcenter : Z ≤ centerIn K)
    {p : ℕ}
    (hpQ : nonabelianPQuotient (⊥ : Subgroup L) K p)
    {χ : Section1.ClassFunction L} (hχX : χ ∈ Xset) :
    ∃ a dχ : ℕ,
      Section1.degree χ = (dχ : ℂ) ∧
        dχ = K.relIndex (⊤ : Subgroup L) * p ^ a ∧
          p ^ (2 * a) ∣ Z.relIndex K := by
  classical
  rcases hpQ with
    ⟨_hbotK, _hbotnormK, _hbotnorm, _hKnorm, hpprime, hQp, _hnoncomm⟩
  have : Fact p.Prime := ⟨hpprime⟩
  have hKp : IsPGroup p K := by
    exact theorem_6_6_isPGroup_of_nonabelianPQuotient_bot
      (K := K)
      ⟨_hbotK, _hbotnormK, _hbotnorm, _hKnorm, hpprime, hQp, _hnoncomm⟩
  have hχS : χ ∈ S := by
    have hχdiff : χ ∈ S \ SZ := by
      simpa [hXeq] using hχX
    exact (Finset.mem_sdiff.mp hχdiff).1
  rcases (hSbot.2 χ).mp hχS with ⟨θ, hθirr, _hθker, _hθne, hχeq⟩
  rcases hθirr with ⟨dθ, ρ, hρirr, hθeq⟩
  have hdθ_dvd : dθ ∣ Nat.card K := by
    let : Representation.IsIrreducible ρ := hρirr
    simpa using Theory.Character.irreducible_dimension_dvd_group_order ρ
  rcases hKp.exists_card_eq with ⟨mK, hKcard⟩
  have hKcardF : Fintype.card K = p ^ mK := by
    simpa [Nat.card_eq_fintype_card] using hKcard
  have hdθ_dvd_pow : dθ ∣ p ^ mK := by
    simpa [hKcardF, Nat.card_eq_fintype_card] using hdθ_dvd
  rcases (Nat.dvd_prime_pow hpprime).1 hdθ_dvd_pow with
    ⟨a, _ham, hdθ⟩
  let dχ : ℕ := K.relIndex (⊤ : Subgroup L) * p ^ a
  have hχdeg : Section1.degree χ = (dχ : ℂ) := by
    rw [hχeq, Section1.degree_inducedClassFunction K θ]
    rw [hθeq, Section1.degree_representation_character]
    simp [dχ, Subgroup.relIndex_top_right, Nat.cast_mul, hdθ]
  have hdim_bound : dθ ^ (2 : ℕ) ≤ Z.relIndex K := by
    let : Representation.IsIrreducible ρ := hρirr
    have hcentral :
        Theory.Character.IsCentralModulo (⊥ : Subgroup K) (Z.subgroupOf K) :=
      theorem_6_6_centralModulo_bot_of_centerIn hZcenter
    have hBker : ∀ b : (⊥ : Subgroup K),
        ρ b = (1 : Module.End ℂ (Fin dθ → ℂ)) := by
      intro b
      have hb : (b : K) = 1 := Subgroup.mem_bot.mp b.2
      ext v i
      simp [hb]
    change dθ ^ (2 : ℕ) ≤ (Z.subgroupOf K).index
    have hfinrank : Module.finrank ℂ (Fin dθ → ℂ) = dθ := by simp
    rw [← hfinrank]
    exact Theory.Character.irreducible_finrank_sq_le_index_of_centralModulo_kernel
      (ρ := ρ) (⊥ : Subgroup K) (Z.subgroupOf K) hBker hcentral
  have hpale : p ^ (2 * a) ≤ Z.relIndex K := by
    calc
      p ^ (2 * a) = (p ^ a) ^ (2 : ℕ) := by
        rw [← pow_mul]
        ring_nf
      _ = dθ ^ (2 : ℕ) := by rw [← hdθ]
      _ ≤ Z.relIndex K := hdim_bound
  have : (Z.subgroupOf K).Normal := hZnorm.subgroupOf K
  have hQZp : IsPGroup p (K ⧸ Z.subgroupOf K) :=
    hKp.to_quotient (Z.subgroupOf K)
  rcases hQZp.exists_card_eq with ⟨mZ, hZcard⟩
  have hZrel : Z.relIndex K = p ^ mZ := by
    rw [← hZcard]
    rw [← Subgroup.index_eq_card (Z.subgroupOf K)]
    rfl
  have hpowle : p ^ (2 * a) ≤ p ^ mZ := by
    simpa [hZrel] using hpale
  have hexp : 2 * a ≤ mZ :=
    (Nat.pow_le_pow_iff_right hpprime.one_lt).1 hpowle
  have hdvd : p ^ (2 * a) ∣ Z.relIndex K := by
    rw [hZrel]
    exact Nat.pow_dvd_pow p hexp
  exact ⟨a, dχ, hχdeg, rfl, hdvd⟩

public theorem theorem_6_6_relIndex_top_coprime_prime_of_nonabelianPQuotient
    {L : Type u} [Group L] [Finite L]
    {G : Type u} [Group G] [Finite G]
    {K H1 : Subgroup L}
    {S : Finset (Section1.ClassFunction L)}
    {T : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
    (h64 : hypothesis_6_4_statement K ⊥ H1 S T)
    {p : ℕ}
    (hpQ : nonabelianPQuotient (⊥ : Subgroup L) K p) :
    Nat.Coprime (K.relIndex (⊤ : Subgroup L)) p := by
  classical
  rcases h64 with ⟨_h61, _hoddL, _hbotH1, _hbotK, _hnil, _hcomm, hfrob⟩
  rcases hpQ with
    ⟨_hbotKp, _hbotnormK, _hbotnorm, _hKnorm, hpprime, hQp, _hnoncomm⟩
  have : Fact p.Prime := ⟨hpprime⟩
  have hKp : IsPGroup p K := by
    exact theorem_6_6_isPGroup_of_nonabelianPQuotient_bot
      (K := K)
      ⟨_hbotKp, _hbotnormK, _hbotnorm, _hKnorm, hpprime, hQp, _hnoncomm⟩
  rcases hfrob with
    ⟨hH1norm, hH1K, _hKnormFrob, R, hcomp, hKbar_ne_bot, _hR_ne_bot, hcent⟩
  have : H1.Normal := hH1norm
  let q : L →* L ⧸ H1 := QuotientGroup.mk' H1
  let Kbar : Subgroup (L ⧸ H1) := K.map q
  have hcardR : Nat.card R = K.relIndex (⊤ : Subgroup L) :=
    theorem_6_5_a_complement_card_eq_relIndex_top hH1norm hH1K hcomp
  have hdiv_card : Nat.card R ∣ Nat.card Kbar - 1 := by
    have : Kbar.Normal := by
      dsimp [Kbar, q]
      infer_instance
    exact frobeniusComplement_card_dvd_normal_subgroup_card_sub_one
      (K := Kbar) (R := R) (N := Kbar) le_rfl
      (by simpa [Kbar, q] using hcent)
  have : (H1.subgroupOf K).Normal := hH1norm.subgroupOf K
  have hKquotP : IsPGroup p (K ⧸ H1.subgroupOf K) :=
    hKp.to_quotient (H1.subgroupOf K)
  rcases hKquotP.exists_card_eq with ⟨m, hcardQ⟩
  have hcardKbar_rel : Nat.card Kbar = H1.relIndex K := by
    simpa [Kbar, q] using theorem_6_5_a_map_card_eq_relIndex (N := K) hH1norm
  have hcardQ_rel : Nat.card (K ⧸ H1.subgroupOf K) = H1.relIndex K := by
    rw [← Subgroup.index_eq_card (H1.subgroupOf K)]
    rfl
  have hcardKbar : Nat.card Kbar = p ^ m := by
    rw [hcardKbar_rel, ← hcardQ_rel, hcardQ]
  have hdiv : K.relIndex (⊤ : Subgroup L) ∣ p ^ m - 1 := by
    rw [hcardR, hcardKbar] at hdiv_card
    simpa [Subgroup.relIndex_top_right] using hdiv_card
  have hKbar_gt : 1 < Nat.card Kbar :=
    (Finite.one_lt_card_iff_nontrivial).2
      ((Subgroup.nontrivial_iff_ne_bot Kbar).2 hKbar_ne_bot)
  have hmpos : 0 < m := by
    by_contra hm
    have hm0 : m = 0 := Nat.eq_zero_of_not_pos hm
    have : Nat.card Kbar = 1 := by
      calc
        Nat.card Kbar = p ^ m := hcardKbar
        _ = 1 := by
          rw [hm0]
          simp
    omega
  have hp_not_dvd_pow_sub_one : ¬ p ∣ p ^ m - 1 := by
    intro hd
    have hp_dvd_pow : p ∣ p ^ m := dvd_pow_self p (Nat.ne_of_gt hmpos)
    have hone : p ∣ 1 := by
      have h := Nat.dvd_sub hp_dvd_pow hd
      have hpos : 0 < p ^ m := pow_pos hpprime.pos _
      convert h using 1
      omega
    exact hpprime.not_dvd_one hone
  have hnot_p_dvd_rel : ¬ p ∣ K.relIndex (⊤ : Subgroup L) := by
    intro hpdiv
    exact hp_not_dvd_pow_sub_one (hpdiv.trans hdiv)
  have hpcop : Nat.Coprime p (K.relIndex (⊤ : Subgroup L)) :=
    (hpprime.coprime_iff_not_dvd).2 hnot_p_dvd_rel
  exact hpcop.symm

theorem theorem_6_6_prime_gt_two_of_nonabelianPQuotient_odd
    {L : Type u} [Group L] [Finite L]
    {K : Subgroup L} {p : ℕ}
    (hoddL : Odd (Nat.card L))
    (hpQ : nonabelianPQuotient (⊥ : Subgroup L) K p) :
    2 < p := by
  classical
  rcases hpQ with
    ⟨_hbotK, _hbotnormK, _hbotnorm, _hKnorm, hpprime, hQp, hnoncomm⟩
  have : Fact p.Prime := ⟨hpprime⟩
  let Q := K ⧸ (⊥ : Subgroup L).subgroupOf K
  have hQ_nontrivial : Nontrivial Q := by
    by_contra hnot
    have hsub : Subsingleton Q := not_nontrivial_iff_subsingleton.mp hnot
    apply hnoncomm
    exact ⟨⟨fun (a b : Q) => Subsingleton.elim (a * b) (b * a)⟩⟩
  have hQ_card_gt : 1 < Nat.card Q :=
    (Finite.one_lt_card_iff_nontrivial (α := Q)).2 hQ_nontrivial
  have hp_dvd_Q : p ∣ Nat.card Q := by
    rcases hQp.card_eq_or_dvd with hcard | hdvd
    · have : ¬ Nat.card Q = 1 := by omega
      exact False.elim (this hcard)
    · exact hdvd
  have hQ_dvd_K : Nat.card Q ∣ Nat.card K := by
    simpa [Q] using
      Subgroup.card_quotient_dvd_card (s := (⊥ : Subgroup L).subgroupOf K)
  have hK_dvd_L : Nat.card K ∣ Nat.card L := Subgroup.card_subgroup_dvd_card K
  have hp_dvd_L : p ∣ Nat.card L := hp_dvd_Q.trans (hQ_dvd_K.trans hK_dvd_L)
  have hp_ne_two : p ≠ 2 := hoddL.ne_two_of_dvd_nat hp_dvd_L
  have hp_two_le : 2 ≤ p := hpprime.two_le
  omega

theorem theorem_6_6_two_mul_min_degree_lt_square_of_p_power_step
    {p n a0 a d0 dX : ℕ}
    (hpgt : 2 < p) (hnpos : 0 < n)
    (hd0eq : d0 = n * p ^ a0)
    (hdXeq : dX = n * p ^ a)
    (hdlt : d0 < dX) :
    2 * (dX : ℝ) * (d0 : ℝ) < (dX : ℝ) ^ (2 : ℕ) := by
  have hprod_lt : n * p ^ a0 < n * p ^ a := by
    simpa [hd0eq, hdXeq] using hdlt
  have hpow_lt : p ^ a0 < p ^ a := Nat.lt_of_mul_lt_mul_left hprod_lt
  have hp_one : 1 < p := by omega
  have ha_lt : a0 < a := (Nat.pow_lt_pow_iff_right hp_one).1 hpow_lt
  have ha_succ : a0 + 1 ≤ a := Nat.succ_le_of_lt ha_lt
  have hp_le : 1 ≤ p := Nat.le_of_lt hp_one
  have hpow_ge : p * p ^ a0 ≤ p ^ a := by
    calc
      p * p ^ a0 = p ^ (a0 + 1) := by rw [pow_succ']
      _ ≤ p ^ a := Nat.pow_le_pow_right hp_le ha_succ
  have hnat_ge : p * d0 ≤ dX := by
    rw [hd0eq, hdXeq]
    calc
      p * (n * p ^ a0) = n * (p * p ^ a0) := by ring
      _ ≤ n * p ^ a := Nat.mul_le_mul_left n hpow_ge
  have hd0_pos : 0 < d0 := by
    rw [hd0eq]
    positivity
  have hdX_pos : 0 < dX := by omega
  have htwo_d0_lt : (2 : ℝ) * (d0 : ℝ) < (dX : ℝ) := by
    have hp_real : (2 : ℝ) < (p : ℝ) := by exact_mod_cast hpgt
    have hd0_pos_real : (0 : ℝ) < (d0 : ℝ) := by exact_mod_cast hd0_pos
    have hle_real : (p : ℝ) * (d0 : ℝ) ≤ (dX : ℝ) := by
      exact_mod_cast hnat_ge
    calc
      (2 : ℝ) * (d0 : ℝ) < (p : ℝ) * (d0 : ℝ) :=
        mul_lt_mul_of_pos_right hp_real hd0_pos_real
      _ ≤ (dX : ℝ) := hle_real
  have hdX_pos_real : (0 : ℝ) < (dX : ℝ) := by exact_mod_cast hdX_pos
  nlinarith [mul_lt_mul_of_pos_left htwo_d0_lt hdX_pos_real]

theorem theorem_6_6_pairExtension_inequality_of_square_lower
    {L : Type u} [Group L] [Finite L]
    {S1 : Finset (Section1.ClassFunction L)}
    (dS1 : S1 → ℕ) {dX d0 : ℕ}
    (hcf : ∀ Y : S1, Section5.cfNormSq (Y : Section1.ClassFunction L) = 1)
    (hstrict : 2 * (dX : ℝ) * (d0 : ℝ) < (dX : ℝ) ^ (2 : ℕ))
    (hsq : (dX : ℝ) ^ (2 : ℕ) ≤ ∑ Y : S1, (dS1 Y : ℝ) ^ (2 : ℕ)) :
    2 * (dX : ℝ) * (d0 : ℝ) <
      ∑ Y : S1,
        (((dS1 Y : ℝ) ^ (2 : ℕ)) /
          Section5.cfNormSq (Y : Section1.ClassFunction L)) := by
  calc
    2 * (dX : ℝ) * (d0 : ℝ) < (dX : ℝ) ^ (2 : ℕ) := hstrict
    _ ≤ ∑ Y : S1, (dS1 Y : ℝ) ^ (2 : ℕ) := hsq
    _ = ∑ Y : S1,
        (((dS1 Y : ℝ) ^ (2 : ℕ)) /
          Section5.cfNormSq (Y : Section1.ClassFunction L)) := by
        refine (Finset.sum_congr rfl ?_).symm
        intro Y _hY
        rw [hcf Y]
        simp

theorem theorem_6_6_square_lower_of_nat_dvd_sum
    {ι : Type*} [Fintype ι] (f : ι → ℕ) {d : ℕ}
    (hdvd : d ^ (2 : ℕ) ∣ ∑ i, f i ^ (2 : ℕ))
    (hsumpos : 0 < ∑ i, f i ^ (2 : ℕ)) :
    (d : ℝ) ^ (2 : ℕ) ≤ ∑ i, (f i : ℝ) ^ (2 : ℕ) := by
  have hnat : d ^ (2 : ℕ) ≤ ∑ i, f i ^ (2 : ℕ) :=
    Nat.le_of_dvd hsumpos hdvd
  exact_mod_cast hnat

theorem theorem_6_6_sq_dvd_sum_of_dvd
    {ι : Type*} [Fintype ι] {n : ℕ} (f : ι → ℕ)
    (h : ∀ i, n ∣ f i) :
    n ^ (2 : ℕ) ∣ ∑ i, f i ^ (2 : ℕ) := by
  apply Finset.dvd_sum
  intro i _hi
  rcases h i with ⟨k, hk⟩
  rw [hk]
  use k ^ (2 : ℕ)
  ring

theorem theorem_6_6_prime_pow_sq_dvd_of_le_exponent
    {n p a b d : ℕ}
    (hd : d = n * p ^ b) (hab : a ≤ b) :
    p ^ (2 * a) ∣ d ^ (2 : ℕ) := by
  have h2ab : 2 * a ≤ 2 * b := Nat.mul_le_mul_left 2 hab
  have hdiv : p ^ (2 * a) ∣ p ^ (2 * b) := Nat.pow_dvd_pow p h2ab
  rw [hd]
  have htarget : p ^ (2 * a) ∣ n ^ (2 : ℕ) * p ^ (2 * b) :=
    dvd_mul_of_dvd_right hdiv _
  convert htarget using 1
  ring_nf

theorem theorem_6_6_mul_prime_pow_sq_dvd_of_coprime
    {n p a sum : ℕ}
    (hcop : Nat.Coprime n p)
    (hn : n ^ (2 : ℕ) ∣ sum)
    (hp : p ^ (2 * a) ∣ sum) :
    (n * p ^ a) ^ (2 : ℕ) ∣ sum := by
  have hcop' : Nat.Coprime (n ^ (2 : ℕ)) (p ^ (2 * a)) := by
    exact (hcop.pow_left 2).pow_right (2 * a)
  have hmul : n ^ (2 : ℕ) * p ^ (2 * a) ∣ sum :=
    hcop'.mul_dvd_of_dvd_of_dvd hn hp
  convert hmul using 1
  ring

theorem theorem_6_6_dvd_card_sub_quotient_of_dvd_relIndex
    {L : Type u} [Group L] [Finite L]
    {K Z : Subgroup L} [Z.Normal] (hZleK : Z ≤ K)
    {d : ℕ} (hdvd : d ∣ Z.relIndex K) :
    d ∣ Nat.card L - Nat.card (L ⧸ Z) := by
  have hrel_top : d ∣ Z.relIndex (⊤ : Subgroup L) := by
    have hindex : d ∣ Z.index :=
      hdvd.trans (Subgroup.relIndex_dvd_index_of_le hZleK)
    simpa [Subgroup.relIndex_top_right] using hindex
  have hquot : d ∣ Nat.card (L ⧸ Z) := by
    simpa [Subgroup.relIndex_top_right, Subgroup.index_eq_card] using hrel_top
  have hcard : d ∣ Nat.card L := hquot.trans (Subgroup.card_quotient_dvd_card (s := Z))
  exact Nat.dvd_sub hcard hquot

theorem theorem_6_6_sum_sdiff_subtype_add_sum_subtype
    {α : Type*} [DecidableEq α] {X S : Finset α} (hS : S ⊆ X)
    (f : X → ℕ) :
    (∑ y : {a // a ∈ X \ S}, f ⟨(y : α), (Finset.mem_sdiff.mp y.2).1⟩) +
      (∑ y : S, f ⟨(y : α), hS y.2⟩) = ∑ x : X, f x := by
  classical
  let F : α → ℕ := fun a => if h : a ∈ X then f ⟨a, h⟩ else 0
  have hcomp : ∑ y : {a // a ∈ X \ S},
      f ⟨(y : α), (Finset.mem_sdiff.mp y.2).1⟩ =
        ∑ a ∈ X \ S, F a := by
    calc
      ∑ y : {a // a ∈ X \ S},
          f ⟨(y : α), (Finset.mem_sdiff.mp y.2).1⟩
          = ∑ y : {a // a ∈ X \ S}, F y := by
            refine Finset.sum_congr rfl ?_
            intro y _hy
            have hyX : (y : α) ∈ X := (Finset.mem_sdiff.mp y.2).1
            simp [F, hyX]
      _ = ∑ a ∈ X \ S, F a := by
            exact (Finset.sum_subtype (X \ S) (by intro a; rfl) F).symm
  have hprefix : ∑ y : S, f ⟨(y : α), hS y.2⟩ = ∑ a ∈ S, F a := by
    calc
      ∑ y : S, f ⟨(y : α), hS y.2⟩ = ∑ y : S, F y := by
            refine Finset.sum_congr rfl ?_
            intro y _hy
            have hyX : (y : α) ∈ X := hS y.2
            simp [F, hyX]
      _ = ∑ a ∈ S, F a := by
            exact (Finset.sum_subtype S (by intro a; rfl) F).symm
  have htotal : ∑ x : X, f x = ∑ a ∈ X, F a := by
    calc
      ∑ x : X, f x = ∑ x : X, F x := by
            refine Finset.sum_congr rfl ?_
            intro x _hx
            have hxX : (x : α) ∈ X := x.2
            simp [F, hxX]
      _ = ∑ a ∈ X, F a := by
            exact (Finset.sum_subtype X (by intro a; rfl) F).symm
  rw [hcomp, hprefix, htotal]
  exact Finset.sum_sdiff hS

public theorem theorem_6_6_complete_sum_degree_normSq
    {G : Type u} [Group G] [Finite G]
    {ι : Type v} [Fintype ι]
    (χ : ι → Theory.Character.ConjClassFunction G)
    (hχ : Theory.Character.IsCompleteIrreducibleCharacterFamily χ) :
    ∑ i : ι, Complex.normSq (χ i (ConjClasses.mk (1 : G))) =
      (Nat.card G : ℝ) := by
  classical
  rcases Theory.Character.exists_completeIrreducibleCharacterFamily_sum_degree_normSq
      (G := G) with
    ⟨κ, hκ, η, hη, hsumη⟩
  let : Fintype κ := hκ
  let f : ι → κ := fun i => Classical.choose (hη.2.1 (χ i) (hχ.1 i))
  have hf_spec : ∀ i, η (f i) = χ i := by
    intro i
    exact Classical.choose_spec (hη.2.1 (χ i) (hχ.1 i))
  have hf_inj : Function.Injective f := by
    intro i j hij
    apply hχ.2.2
    rw [← hf_spec i, ← hf_spec j, hij]
  have hf_surj : Function.Surjective f := by
    intro k
    rcases hχ.2.1 (η k) (hη.1 k) with ⟨i, hi⟩
    refine ⟨i, ?_⟩
    apply hη.2.2
    rw [hf_spec i, hi]
  have hbij : Function.Bijective f := ⟨hf_inj, hf_surj⟩
  have hsum_eq :
      (∑ i : ι, Complex.normSq (χ i (ConjClasses.mk (1 : G)))) =
        ∑ k : κ, Complex.normSq (η k (ConjClasses.mk (1 : G))) := by
    simpa using
      (Fintype.sum_bijective f hbij
        (fun i => Complex.normSq (χ i (ConjClasses.mk (1 : G))))
        (fun k => Complex.normSq (η k (ConjClasses.mk (1 : G))))
        (by
          intro i
          rw [hf_spec i]))
  exact hsum_eq.trans hsumη

theorem theorem_6_6_toConjClassFunction_irreducible
    {G : Type u} [Group G] [Finite G]
    {χ : Section1.ClassFunction G}
    (hχ : Section1.IsIrreducibleCharacterOnGroup χ) :
    Theory.Character.IsIrreducibleConjCharacter
      (Section1.toConjClassFunction χ
        (theorem_6_6_isClassFunction_of_irreducibleCharacterOnGroup hχ)) := by
  rcases hχ with ⟨n, ρ, hρirr, hχeq⟩
  let hχclass := theorem_6_6_isClassFunction_of_irreducibleCharacterOnGroup
    ⟨n, ρ, hρirr, hχeq⟩
  have htoeq :
      Section1.toConjClassFunction χ hχclass =
        Theory.Character.characterClassFunction ρ := by
    apply Section1.toConjClassFunction_eq_of_apply
    intro g
    rw [hχeq]
    rfl
  refine ⟨⟨n, ρ, htoeq⟩, ?_⟩
  rw [htoeq]
  exact (Theory.Character.irreducible_iff_character_norm_one (ρ := ρ)).1 hρirr

theorem theorem_6_6_ofConjClassFunction_irreducibleOnGroup
    {G : Type u} [Group G] [Finite G]
    {Φ : Theory.Character.ConjClassFunction G}
    (hΦ : Theory.Character.IsIrreducibleConjCharacter Φ) :
    Section1.IsIrreducibleCharacterOnGroup (Section1.ofConjClassFunction Φ) := by
  rcases hΦ with ⟨hchar, hnormΦ⟩
  rcases hchar with ⟨n, ρ, hΦeq⟩
  have hnormρ : Theory.Character.classFunctionInner
      (Theory.Character.characterClassFunction ρ)
      (Theory.Character.characterClassFunction ρ) = 1 := by
    simpa [hΦeq] using hnormΦ
  have hρirr : Representation.IsIrreducible ρ :=
    (Theory.Character.irreducible_iff_character_norm_one (ρ := ρ)).2 hnormρ
  refine ⟨n, ρ, hρirr, ?_⟩
  rw [hΦeq]
  exact Section1.ofConjClassFunction_characterClassFunction ρ

noncomputable def theorem_6_6_quotientInflationConj
    {L : Type u} [Group L] {Z : Subgroup L} [Z.Normal]
    (Φ : Theory.Character.ConjClassFunction (L ⧸ Z)) :
    Theory.Character.ConjClassFunction L :=
  Section1.toConjClassFunction
    (fun g : L => Φ (ConjClasses.mk (QuotientGroup.mk' Z g)))
    (by
      intro x g
      change Φ (ConjClasses.mk (QuotientGroup.mk' Z (x * g * x⁻¹))) =
        Φ (ConjClasses.mk (QuotientGroup.mk' Z g))
      congr 1
      apply ConjClasses.mk_eq_mk_iff_isConj.mpr
      apply isConj_iff.mpr
      refine ⟨QuotientGroup.mk' Z x⁻¹, ?_⟩
      simp [map_mul, mul_assoc])

theorem theorem_6_6_quotientInflationConj_kernel
    {L : Type u} [Group L] {Z : Subgroup L} [Z.Normal]
    (Φ : Theory.Character.ConjClassFunction (L ⧸ Z)) :
    Section1.subgroupInKernel'
      (Section1.ofConjClassFunction
        (theorem_6_6_quotientInflationConj (Z := Z) Φ)) Z := by
  intro z
  change theorem_6_6_quotientInflationConj (Z := Z) Φ (ConjClasses.mk (z : L)) =
    Section1.degree
      (Section1.ofConjClassFunction
        (theorem_6_6_quotientInflationConj (Z := Z) Φ))
  rw [Section1.degree]
  change theorem_6_6_quotientInflationConj (Z := Z) Φ (ConjClasses.mk (z : L)) =
    theorem_6_6_quotientInflationConj (Z := Z) Φ (ConjClasses.mk (1 : L))
  change Φ (ConjClasses.mk (QuotientGroup.mk' Z (z : L))) =
    Φ (ConjClasses.mk (QuotientGroup.mk' Z (1 : L)))
  have hz : QuotientGroup.mk' Z (z : L) = 1 :=
    (QuotientGroup.eq_one_iff (N := Z) (x := (z : L))).2 z.2
  simp [hz]

theorem theorem_6_6_quotientInflationConj_irreducible
    {L : Type u} [Group L] [Finite L] {Z : Subgroup L} [Z.Normal]
    {Φ : Theory.Character.ConjClassFunction (L ⧸ Z)}
    (hΦ : Theory.Character.IsIrreducibleConjCharacter Φ) :
    Theory.Character.IsIrreducibleConjCharacter
      (theorem_6_6_quotientInflationConj (Z := Z) Φ) := by
  rcases hΦ with ⟨hchar, hnormΦ⟩
  rcases hchar with ⟨n, ρ, hΦeq⟩
  let q : L →* L ⧸ Z := QuotientGroup.mk' Z
  let ρL : Representation ℂ L (Fin n → ℂ) := ρ.comp q
  have hnormρ : Theory.Character.classFunctionInner
      (Theory.Character.characterClassFunction ρ)
      (Theory.Character.characterClassFunction ρ) = 1 := by
    simpa [hΦeq] using hnormΦ
  have hρirr : Representation.IsIrreducible ρ :=
    (Theory.Character.irreducible_iff_character_norm_one (ρ := ρ)).2 hnormρ
  have hρcompirr : Representation.IsIrreducible ρL := by
    exact representation_isIrreducible_comp_surjective ρ q
      (QuotientGroup.mk'_surjective Z) hρirr
  have hchar_eq : theorem_6_6_quotientInflationConj (Z := Z) Φ =
      Theory.Character.characterClassFunction ρL := by
    ext c
    rcases ConjClasses.exists_rep c with ⟨g, rfl⟩
    change Φ (ConjClasses.mk (q g)) = ρL.character g
    rw [hΦeq]
    rfl
  refine ⟨?_, ?_⟩
  · exact ⟨n, ρL, hchar_eq⟩
  · have hnorm :=
      (Theory.Character.irreducible_iff_character_norm_one (ρ := ρL)).1 hρcompirr
    simpa [hchar_eq] using hnorm

theorem theorem_6_6_completeFamily_with_nonkernel
    {L : Type u} [Group L] [Finite L]
    {Z : Subgroup L} [Z.Normal]
    {Xset : Finset (Section1.ClassFunction L)}
    (hXchar : ∀ χ : Section1.ClassFunction L, χ ∈ Xset ↔
      Section1.IsIrreducibleCharacterOnGroup χ ∧
        ¬ Section1.subgroupInKernel' χ Z) :
    ∃ (κ : Type) (_ : Fintype κ) (η : κ → Theory.Character.ConjClassFunction (L ⧸ Z)),
      Theory.Character.IsCompleteIrreducibleCharacterFamily η ∧
        let fam : Sum Xset κ → Theory.Character.ConjClassFunction L := fun s =>
          match s with
          | Sum.inl X =>
              Section1.toConjClassFunction (X : Section1.ClassFunction L)
                (theorem_6_6_isClassFunction_of_irreducibleCharacterOnGroup
                  ((hXchar (X : Section1.ClassFunction L)).1 X.2).1)
          | Sum.inr k => theorem_6_6_quotientInflationConj (Z := Z) (η k)
        Theory.Character.IsCompleteIrreducibleCharacterFamily fam := by
  classical
  rcases Theory.Character.exists_completeIrreducibleCharacterFamily_sum_degree_normSq
      (G := L ⧸ Z) with
    ⟨κ, hκ, η, hη, _hsumη⟩
  let : Fintype κ := hκ
  refine ⟨κ, hκ, η, hη, ?_⟩
  let fam : Sum Xset κ → Theory.Character.ConjClassFunction L := fun s =>
    match s with
    | Sum.inl X =>
        Section1.toConjClassFunction (X : Section1.ClassFunction L)
          (theorem_6_6_isClassFunction_of_irreducibleCharacterOnGroup
            ((hXchar (X : Section1.ClassFunction L)).1 X.2).1)
    | Sum.inr k => theorem_6_6_quotientInflationConj (Z := Z) (η k)
  change Theory.Character.IsCompleteIrreducibleCharacterFamily fam
  refine ⟨?_, ?_, ?_⟩
  · intro s
    cases s with
    | inl X =>
        exact theorem_6_6_toConjClassFunction_irreducible
          ((hXchar (X : Section1.ClassFunction L)).1 X.2).1
    | inr k =>
        exact theorem_6_6_quotientInflationConj_irreducible (hη.1 k)
  · intro Φ hΦ
    let φ : Section1.ClassFunction L := Section1.ofConjClassFunction Φ
    have hφirr : Section1.IsIrreducibleCharacterOnGroup φ :=
      theorem_6_6_ofConjClassFunction_irreducibleOnGroup hΦ
    by_cases hker : Section1.subgroupInKernel' φ Z
    · rcases hφirr with ⟨n, ρ, hρirr, hφeq⟩
      have hkerρ : Section1.subgroupInKernel' ρ.character Z := by
        simpa [hφeq] using hker
      have hrepker : Section1.subgroupInRepresentationKernel ρ Z :=
        (Section1.subgroupInKernel'_character_iff_subgroupInRepresentationKernel
          ρ Z).mp hkerρ
      let q : L →* L ⧸ Z := QuotientGroup.mk' Z
      let ρq : Representation ℂ (L ⧸ Z) (Fin n → ℂ) :=
        Section1.quotientRepresentationOfKernelSubgroup ρ Z hrepker
      have hcomp_eq : ρq.comp q = ρ := by
        apply MonoidHom.ext
        intro g
        exact Section1.quotientRepresentationOfKernelSubgroup_mk
          ρ Z hrepker g
      have hρqirr : Representation.IsIrreducible ρq := by
        apply representation_isIrreducible_of_comp_surjective ρq q
          (QuotientGroup.mk'_surjective Z)
        simpa [hcomp_eq] using hρirr
      have hρqChar : Theory.Character.IsIrreducibleConjCharacter
          (Theory.Character.characterClassFunction ρq) := by
        refine ⟨⟨n, ρq, rfl⟩, ?_⟩
        exact
          (Theory.Character.irreducible_iff_character_norm_one (ρ := ρq)).1 hρqirr
      rcases hη.2.1 (Theory.Character.characterClassFunction ρq) hρqChar with
        ⟨k, hk⟩
      refine ⟨Sum.inr k, ?_⟩
      dsimp [fam]
      ext c
      rcases ConjClasses.exists_rep c with ⟨g, rfl⟩
      change η k (ConjClasses.mk (q g)) = Φ (ConjClasses.mk g)
      rw [hk]
      change ρq.character (q g) = Φ (ConjClasses.mk g)
      change ((show Representation ℂ L (Fin n → ℂ) from ρq.comp q).character g) =
        Φ (ConjClasses.mk g)
      rw [hcomp_eq]
      rw [← hφeq]
      rfl
    · have hφX : φ ∈ Xset := (hXchar φ).2 ⟨hφirr, hker⟩
      refine ⟨Sum.inl ⟨φ, hφX⟩, ?_⟩
      dsimp [fam]
      exact Section1.toConjClassFunction_ofConjClassFunction Φ
  · intro a b h
    cases a with
    | inl X =>
        cases b with
        | inl Y =>
            have hXY : X = Y := by
              apply Subtype.ext
              ext g
              have hv := congrFun h (ConjClasses.mk g)
              simpa [fam, Section1.toConjClassFunction_apply] using hv
            subst hXY
            rfl
        | inr k =>
            exfalso
            have hnotker := ((hXchar (X : Section1.ClassFunction L)).1 X.2).2
            apply hnotker
            have hXeq : (X : Section1.ClassFunction L) =
                Section1.ofConjClassFunction
                  (theorem_6_6_quotientInflationConj (Z := Z) (η k)) := by
              ext g
              have hv := congrFun h (ConjClasses.mk g)
              simpa [fam, Section1.toConjClassFunction_apply,
                Section1.ofConjClassFunction_apply] using hv
            simpa [hXeq] using
              theorem_6_6_quotientInflationConj_kernel (Z := Z) (η k)
    | inr k =>
        cases b with
        | inl X =>
            exfalso
            have hnotker := ((hXchar (X : Section1.ClassFunction L)).1 X.2).2
            apply hnotker
            have hXeq : (X : Section1.ClassFunction L) =
                Section1.ofConjClassFunction
                  (theorem_6_6_quotientInflationConj (Z := Z) (η k)) := by
              ext g
              have hv := congrFun h.symm (ConjClasses.mk g)
              simpa [fam, Section1.toConjClassFunction_apply,
                Section1.ofConjClassFunction_apply] using hv
            simpa [hXeq] using
              theorem_6_6_quotientInflationConj_kernel (Z := Z) (η k)
        | inr l =>
            have hkl : k = l := by
              apply hη.2.2
              ext c
              rcases ConjClasses.exists_rep c with ⟨qg, rfl⟩
              rcases QuotientGroup.mk'_surjective Z qg with ⟨g, hg⟩
              have hv := congrFun h (ConjClasses.mk g)
              change η k (ConjClasses.mk (QuotientGroup.mk' Z g)) =
                η l (ConjClasses.mk (QuotientGroup.mk' Z g)) at hv
              simpa [hg] using hv
            subst hkl
            rfl

public theorem theorem_6_6_regularCharacter_isClassFunction
    {G : Type u} [Group G] [Finite G] :
    Section1.IsClassFunction (regularCharacter G) := by
  intro x g
  by_cases hg : g = 1
  · subst g
    simp [regularCharacter]
  · have hconj_ne : x * g * x⁻¹ ≠ 1 := by
      intro h
      apply hg
      have h' := congrArg (fun y => x⁻¹ * y * x) h
      simpa [mul_assoc] using h'
    simp [regularCharacter, hg, hconj_ne]

theorem theorem_6_6_scalarProduct_regularCharacter_left_of_value_one
    {G : Type u} [Group G] [Finite G]
    {χ : Section1.ClassFunction G} {d : ℂ}
    (hχ : χ 1 = d) :
    Section1.scalarProduct G (regularCharacter G) χ = star d := by
  classical
  let : Fintype G := Fintype.ofFinite G
  unfold Section1.scalarProduct regularCharacter
  rw [Finset.sum_eq_single (1 : G)]
  · simp only [if_true]
    rw [hχ]
    have hcard : (Fintype.card G : ℂ) ≠ 0 := by
      exact_mod_cast (Fintype.card_ne_zero : Fintype.card G ≠ 0)
    field_simp [hcard, Nat.card_eq_fintype_card]
  · intro g _hg hgne
    simp [hgne]
  · intro hone
    simp at hone

set_option backward.isDefEq.respectTransparency false in
theorem theorem_6_6_classFunctionInner_regularCharacter_left
    {G : Type u} [Group G] [Finite G]
    {Χ : Theory.Character.ConjClassFunction G} {d : ℂ}
    (hΧ : Χ (ConjClasses.mk (1 : G)) = d) :
    Theory.Character.classFunctionInner
        (Section1.toConjClassFunction (regularCharacter G)
          (theorem_6_6_regularCharacter_isClassFunction (G := G))) Χ =
      star d := by
  rw [← Section1.toConjClassFunction_ofConjClassFunction Χ]
  rw [Section1.classFunctionInner_toConjClassFunction]
  exact theorem_6_6_scalarProduct_regularCharacter_left_of_value_one
    (G := G) (χ := Section1.ofConjClassFunction Χ) hΧ

public theorem theorem_6_6_completeFamily_weighted_sum_eq_regular
    {G : Type u} [Group G] [Finite G]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {χ : ι → Theory.Character.ConjClassFunction G}
    (hχ : Theory.Character.IsCompleteIrreducibleCharacterFamily χ)
    (deg : ι → ℂ)
    (hdeg : ∀ i, χ i (ConjClasses.mk (1 : G)) = deg i)
    (g : G) :
    regularCharacter G g =
      ∑ i : ι, star (deg i) * χ i (ConjClasses.mk g) := by
  classical
  let Ρ : Theory.Character.ConjClassFunction G :=
    Section1.toConjClassFunction (regularCharacter G)
      (theorem_6_6_regularCharacter_isClassFunction (G := G))
  have h := Theory.Character.completeFamily_apply_eq_sum_inner hχ Ρ (ConjClasses.mk g)
  change regularCharacter G g =
      ∑ i : ι, Theory.Character.classFunctionInner Ρ (χ i) *
        χ i (ConjClasses.mk g) at h
  calc
    regularCharacter G g =
        ∑ i : ι, Theory.Character.classFunctionInner Ρ (χ i) *
          χ i (ConjClasses.mk g) := h
    _ = ∑ i : ι, star (deg i) * χ i (ConjClasses.mk g) := by
      refine Finset.sum_congr rfl ?_
      intro i _hi
      rw [theorem_6_6_classFunctionInner_regularCharacter_left
        (G := G) (Χ := χ i) (hdeg i)]

public theorem theorem_6_6_Xset_sum_degree_sq_add_quotient_card
    {L : Type u} [Group L] [Finite L]
    {Z : Subgroup L} [Z.Normal]
    {Xset : Finset (Section1.ClassFunction L)}
    (hXchar : ∀ χ : Section1.ClassFunction L, χ ∈ Xset ↔
      Section1.IsIrreducibleCharacterOnGroup χ ∧
        ¬ Section1.subgroupInKernel' χ Z)
    (degX : Xset → ℕ)
    (hdegX : ∀ X : Xset,
      Section1.degree (X : Section1.ClassFunction L) = (degX X : ℂ)) :
    (∑ X : Xset, degX X ^ (2 : ℕ)) + Nat.card (L ⧸ Z) = Nat.card L := by
  classical
  rcases theorem_6_6_completeFamily_with_nonkernel
      (Z := Z) (Xset := Xset) hXchar with
    ⟨κ, hκ, η, hη, hfam⟩
  let : Fintype κ := hκ
  let fam : Sum Xset κ → Theory.Character.ConjClassFunction L := fun s =>
    match s with
    | Sum.inl X =>
        Section1.toConjClassFunction (X : Section1.ClassFunction L)
          (theorem_6_6_isClassFunction_of_irreducibleCharacterOnGroup
            ((hXchar (X : Section1.ClassFunction L)).1 X.2).1)
    | Sum.inr k => theorem_6_6_quotientInflationConj (Z := Z) (η k)
  have hsumFam : ∑ s : Sum Xset κ,
      Complex.normSq (fam s (ConjClasses.mk (1 : L))) = (Nat.card L : ℝ) := by
    exact theorem_6_6_complete_sum_degree_normSq fam hfam
  have hsumEta : ∑ k : κ,
      Complex.normSq (η k (ConjClasses.mk (1 : L ⧸ Z))) =
        (Nat.card (L ⧸ Z) : ℝ) := by
    exact theorem_6_6_complete_sum_degree_normSq η hη
  have hleft : ∑ X : Xset,
      Complex.normSq (fam (Sum.inl X) (ConjClasses.mk (1 : L))) =
        ∑ X : Xset, (degX X : ℝ) ^ (2 : ℕ) := by
    refine Finset.sum_congr rfl ?_
    intro X _hX
    dsimp [fam]
    rw [Section1.toConjClassFunction_apply]
    change Complex.normSq (Section1.degree (X : Section1.ClassFunction L)) =
      (degX X : ℝ) ^ (2 : ℕ)
    rw [hdegX X]
    rw [← Complex.ofReal_natCast, Complex.normSq_ofReal]
    ring
  have hright : ∑ k : κ,
      Complex.normSq (fam (Sum.inr k) (ConjClasses.mk (1 : L))) =
        (Nat.card (L ⧸ Z) : ℝ) := by
    calc
      ∑ k : κ, Complex.normSq (fam (Sum.inr k) (ConjClasses.mk (1 : L)))
          = ∑ k : κ, Complex.normSq (η k (ConjClasses.mk (1 : L ⧸ Z))) := by
            refine Finset.sum_congr rfl ?_
            intro k _hk
            dsimp [fam, theorem_6_6_quotientInflationConj]
            rfl
      _ = (Nat.card (L ⧸ Z) : ℝ) := hsumEta
  have hreal :
      ((∑ X : Xset, degX X ^ (2 : ℕ)) + Nat.card (L ⧸ Z) : ℝ) =
        (Nat.card L : ℝ) := by
    calc
      ((∑ X : Xset, degX X ^ (2 : ℕ)) + Nat.card (L ⧸ Z) : ℝ)
          = (∑ X : Xset, (degX X : ℝ) ^ (2 : ℕ)) +
              (Nat.card (L ⧸ Z) : ℝ) := by
            norm_cast
      _ = (∑ X : Xset,
            Complex.normSq (fam (Sum.inl X) (ConjClasses.mk (1 : L)))) +
            ∑ k : κ, Complex.normSq (fam (Sum.inr k) (ConjClasses.mk (1 : L))) := by
            rw [hleft, hright]
      _ = ∑ s : Sum Xset κ,
            Complex.normSq (fam s (ConjClasses.mk (1 : L))) := by
            rw [Fintype.sum_sum_type]
      _ = (Nat.card L : ℝ) := hsumFam
  exact_mod_cast hreal

public theorem theorem_6_6_complete_nonkernel_degree_data
    {L : Type u} [Group L] [Finite L]
    {Z : Subgroup L} [Z.Normal] :
    ∃ Xset : Finset (Section1.ClassFunction L),
      (∀ χ : Section1.ClassFunction L, χ ∈ Xset ↔
        Section1.IsIrreducibleCharacterOnGroup χ ∧
          ¬ Section1.subgroupInKernel' χ Z) ∧
        ∃ degX : Xset → ℕ,
          (∀ X : Xset,
            Section1.degree (X : Section1.ClassFunction L) = (degX X : ℂ)) ∧
            (∑ X : Xset, degX X ^ (2 : ℕ)) + Nat.card (L ⧸ Z) =
              Nat.card L := by
  classical
  rcases Theory.Character.exists_completeIrreducibleCharacterFamily_sum_degree_normSq
      (G := L) with
    ⟨ι, hι, χ, hχ, _hsumχ⟩
  let : Fintype ι := hι
  let : DecidableEq ι := Classical.decEq ι
  let θ : ι → Section1.ClassFunction L :=
    fun i => Section1.ofConjClassFunction (χ i)
  let Xset : Finset (Section1.ClassFunction L) :=
    (Finset.univ.filter fun i : ι =>
      ¬ Section1.subgroupInKernel' (θ i) Z).image θ
  have hθirr : ∀ i, Section1.IsIrreducibleCharacterOnGroup (θ i) := by
    intro i
    exact theorem_6_6_ofConjClassFunction_irreducibleOnGroup (hχ.1 i)
  have hXchar : ∀ χ0 : Section1.ClassFunction L, χ0 ∈ Xset ↔
      Section1.IsIrreducibleCharacterOnGroup χ0 ∧
        ¬ Section1.subgroupInKernel' χ0 Z := by
    intro χ0
    constructor
    · intro hχ0
      rcases Finset.mem_image.mp hχ0 with ⟨i, hi, hiχ⟩
      have hi_not :
          ¬ Section1.subgroupInKernel' (θ i) Z := (Finset.mem_filter.mp hi).2
      constructor
      · simpa [hiχ] using hθirr i
      · intro hker
        exact hi_not (by simpa [hiχ] using hker)
    · intro hχ0
      have hχ0class : Section1.IsClassFunction χ0 := by
        rcases hχ0.1 with ⟨_n, ρ, _hρirr, hχ0eq⟩
        intro x g
        rw [hχ0eq]
        simpa [mul_assoc] using Representation.char_conj (ρ := ρ) g x
      have hχ0rep :
          Theory.Character.IsIrreducibleConjCharacter
            (Section1.toConjClassFunction χ0 hχ0class) := by
        rcases hχ0.1 with ⟨n, ρ, hρirr, hχ0eq⟩
        have htoeq :
            Section1.toConjClassFunction χ0 hχ0class =
              Theory.Character.characterClassFunction ρ := by
          apply Section1.toConjClassFunction_eq_of_apply
          intro g
          rw [hχ0eq]
          rfl
        refine ⟨⟨n, ρ, htoeq⟩, ?_⟩
        rw [htoeq]
        exact (Theory.Character.irreducible_iff_character_norm_one (ρ := ρ)).1 hρirr
      rcases hχ.2.1 (Section1.toConjClassFunction χ0 hχ0class) hχ0rep with
        ⟨i, hi⟩
      have hiχ : θ i = χ0 := by
        dsimp [θ]
        rw [hi]
        ext g
        rfl
      refine Finset.mem_image.mpr ⟨i, ?_, hiχ⟩
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_univ i, by simpa [hiχ] using hχ0.2⟩
  have hXdeg_exists :
      ∀ X : Xset,
        ∃ dX : ℕ,
          Section1.degree (X : Section1.ClassFunction L) = (dX : ℂ) := by
    intro X
    rcases ((hXchar (X : Section1.ClassFunction L)).mp X.2).1 with
      ⟨dX, ρ, _hρirr, hXeq⟩
    refine ⟨dX, ?_⟩
    rw [hXeq, Section1.degree_representation_character]
    simp
  let degX : Xset → ℕ := fun X => Classical.choose (hXdeg_exists X)
  have hdegX : ∀ X : Xset,
      Section1.degree (X : Section1.ClassFunction L) = (degX X : ℂ) := by
    intro X
    exact Classical.choose_spec (hXdeg_exists X)
  refine ⟨Xset, hXchar, degX, hdegX, ?_⟩
  exact theorem_6_6_Xset_sum_degree_sq_add_quotient_card hXchar degX hdegX

public theorem theorem_6_6_Xset_weighted_degree_sum_eq_card_sub_quotient_at_one
    {L : Type u} [Group L] [Finite L]
    {Z : Subgroup L} [Z.Normal]
    {Xset : Finset (Section1.ClassFunction L)}
    (hXchar : ∀ χ : Section1.ClassFunction L, χ ∈ Xset ↔
      Section1.IsIrreducibleCharacterOnGroup χ ∧
        ¬ Section1.subgroupInKernel' χ Z)
    (degX : Xset → ℕ)
    (hdegX : ∀ X : Xset,
      Section1.degree (X : Section1.ClassFunction L) = (degX X : ℂ)) :
    (∑ X : Xset, (degX X : ℂ) * (X : Section1.ClassFunction L) (1 : L)) =
      (Nat.card L : ℂ) - (Nat.card (L ⧸ Z) : ℂ) := by
  classical
  rcases theorem_6_6_completeFamily_with_nonkernel
      (Z := Z) (Xset := Xset) hXchar with
    ⟨κ, hκ, η, hη, hfam⟩
  let : Fintype κ := hκ
  let fam : Sum Xset κ → Theory.Character.ConjClassFunction L := fun s =>
    match s with
    | Sum.inl X =>
        Section1.toConjClassFunction (X : Section1.ClassFunction L)
          (theorem_6_6_isClassFunction_of_irreducibleCharacterOnGroup
            ((hXchar (X : Section1.ClassFunction L)).1 X.2).1)
    | Sum.inr k => theorem_6_6_quotientInflationConj (Z := Z) (η k)
  let degFam : Sum Xset κ → ℂ := fun s =>
    match s with
    | Sum.inl X => (degX X : ℂ)
    | Sum.inr k => η k (ConjClasses.mk (1 : L ⧸ Z))
  have hdegFam :
      ∀ s : Sum Xset κ, fam s (ConjClasses.mk (1 : L)) = degFam s := by
    intro s
    cases s with
    | inl X =>
        dsimp [fam, degFam]
        rw [Section1.toConjClassFunction_apply]
        exact hdegX X
    | inr k =>
        dsimp [fam, degFam, theorem_6_6_quotientInflationConj]
        rfl
  have hreg :=
    theorem_6_6_completeFamily_weighted_sum_eq_regular
      (G := L) hfam degFam hdegFam (1 : L)
  have hquot : (∑ k : κ,
      star (η k (ConjClasses.mk (1 : L ⧸ Z))) *
        η k (ConjClasses.mk (1 : L ⧸ Z))) =
        (Nat.card (L ⧸ Z) : ℂ) := by
    have hsumEta : ∑ k : κ,
        Complex.normSq (η k (ConjClasses.mk (1 : L ⧸ Z))) =
          (Nat.card (L ⧸ Z) : ℝ) := by
      exact theorem_6_6_complete_sum_degree_normSq η hη
    calc
      (∑ k : κ,
          star (η k (ConjClasses.mk (1 : L ⧸ Z))) *
            η k (ConjClasses.mk (1 : L ⧸ Z))) =
          ∑ k : κ,
            ((Complex.normSq (η k (ConjClasses.mk (1 : L ⧸ Z))) : ℝ) : ℂ) := by
            refine Finset.sum_congr rfl ?_
            intro k _hk
            rw [Complex.normSq_eq_conj_mul_self]
            rfl
      _ = ((∑ k : κ,
            Complex.normSq (η k (ConjClasses.mk (1 : L ⧸ Z))) : ℝ) : ℂ) := by
            simp
      _ = (Nat.card (L ⧸ Z) : ℂ) := by
            rw [hsumEta]
            norm_num
  have hleft : ∑ X : Xset,
      star (degFam (Sum.inl X)) * fam (Sum.inl X) (ConjClasses.mk (1 : L)) =
      ∑ X : Xset,
        (degX X : ℂ) * (X : Section1.ClassFunction L) (1 : L) := by
    refine Finset.sum_congr rfl ?_
    intro X _hX
    dsimp [fam, degFam]
    rw [Section1.toConjClassFunction_apply]
    simp
  have hright : ∑ k : κ,
      star (degFam (Sum.inr k)) * fam (Sum.inr k) (ConjClasses.mk (1 : L)) =
      (Nat.card (L ⧸ Z) : ℂ) := by
    calc
      ∑ k : κ,
          star (degFam (Sum.inr k)) * fam (Sum.inr k) (ConjClasses.mk (1 : L)) =
          ∑ k : κ,
            star (η k (ConjClasses.mk (1 : L ⧸ Z))) *
              η k (ConjClasses.mk (1 : L ⧸ Z)) := by
            refine Finset.sum_congr rfl ?_
            intro k _hk
            dsimp [fam, degFam, theorem_6_6_quotientInflationConj]
            rfl
      _ = (Nat.card (L ⧸ Z) : ℂ) := hquot
  have htotal :
      (Nat.card L : ℂ) =
        (∑ X : Xset,
            (degX X : ℂ) * (X : Section1.ClassFunction L) (1 : L)) +
          (Nat.card (L ⧸ Z) : ℂ) := by
    rw [Fintype.sum_sum_type] at hreg
    rw [hleft, hright] at hreg
    simpa [regularCharacter] using hreg
  calc
    (∑ X : Xset, (degX X : ℂ) * (X : Section1.ClassFunction L) (1 : L)) =
        ((∑ X : Xset,
            (degX X : ℂ) * (X : Section1.ClassFunction L) (1 : L)) +
          (Nat.card (L ⧸ Z) : ℂ)) - (Nat.card (L ⧸ Z) : ℂ) := by ring
    _ = (Nat.card L : ℂ) - (Nat.card (L ⧸ Z) : ℂ) := by
      rw [← htotal]

public theorem theorem_6_6_Xset_weighted_degree_sum_eq_neg_quotient_card_of_mem_Z_ne_one
    {L : Type u} [Group L] [Finite L]
    {Z : Subgroup L} [Z.Normal]
    {Xset : Finset (Section1.ClassFunction L)}
    (hXchar : ∀ χ : Section1.ClassFunction L, χ ∈ Xset ↔
      Section1.IsIrreducibleCharacterOnGroup χ ∧
        ¬ Section1.subgroupInKernel' χ Z)
    (degX : Xset → ℕ)
    (hdegX : ∀ X : Xset,
      Section1.degree (X : Section1.ClassFunction L) = (degX X : ℂ))
    (z : Z) (hz : z ≠ 1) :
    (∑ X : Xset, (degX X : ℂ) * (X : Section1.ClassFunction L) (z : L)) =
      - (Nat.card (L ⧸ Z) : ℂ) := by
  classical
  rcases theorem_6_6_completeFamily_with_nonkernel
      (Z := Z) (Xset := Xset) hXchar with
    ⟨κ, hκ, η, hη, hfam⟩
  let : Fintype κ := hκ
  let fam : Sum Xset κ → Theory.Character.ConjClassFunction L := fun s =>
    match s with
    | Sum.inl X =>
        Section1.toConjClassFunction (X : Section1.ClassFunction L)
          (theorem_6_6_isClassFunction_of_irreducibleCharacterOnGroup
            ((hXchar (X : Section1.ClassFunction L)).1 X.2).1)
    | Sum.inr k => theorem_6_6_quotientInflationConj (Z := Z) (η k)
  let degFam : Sum Xset κ → ℂ := fun s =>
    match s with
    | Sum.inl X => (degX X : ℂ)
    | Sum.inr k => η k (ConjClasses.mk (1 : L ⧸ Z))
  have hdegFam :
      ∀ s : Sum Xset κ, fam s (ConjClasses.mk (1 : L)) = degFam s := by
    intro s
    cases s with
    | inl X =>
        dsimp [fam, degFam]
        rw [Section1.toConjClassFunction_apply]
        exact hdegX X
    | inr k =>
        dsimp [fam, degFam, theorem_6_6_quotientInflationConj]
        rfl
  have hreg :=
    theorem_6_6_completeFamily_weighted_sum_eq_regular
      (G := L) hfam degFam hdegFam (z : L)
  have hzq : QuotientGroup.mk' Z (z : L) = 1 :=
    (QuotientGroup.eq_one_iff (N := Z) (x := (z : L))).2 z.2
  have hquot : (∑ k : κ,
      star (η k (ConjClasses.mk (1 : L ⧸ Z))) *
        η k (ConjClasses.mk (QuotientGroup.mk' Z (z : L)))) =
        (Nat.card (L ⧸ Z) : ℂ) := by
    have hsumEta : ∑ k : κ,
        Complex.normSq (η k (ConjClasses.mk (1 : L ⧸ Z))) =
          (Nat.card (L ⧸ Z) : ℝ) := by
      exact theorem_6_6_complete_sum_degree_normSq η hη
    calc
      (∑ k : κ,
          star (η k (ConjClasses.mk (1 : L ⧸ Z))) *
            η k (ConjClasses.mk (QuotientGroup.mk' Z (z : L)))) =
          ∑ k : κ,
            star (η k (ConjClasses.mk (1 : L ⧸ Z))) *
              η k (ConjClasses.mk (1 : L ⧸ Z)) := by
            refine Finset.sum_congr rfl ?_
            intro k _hk
            rw [hzq]
      _ = ∑ k : κ,
            ((Complex.normSq (η k (ConjClasses.mk (1 : L ⧸ Z))) : ℝ) : ℂ) := by
            refine Finset.sum_congr rfl ?_
            intro k _hk
            rw [Complex.normSq_eq_conj_mul_self]
            rfl
      _ = ((∑ k : κ,
            Complex.normSq (η k (ConjClasses.mk (1 : L ⧸ Z))) : ℝ) : ℂ) := by
            simp
      _ = (Nat.card (L ⧸ Z) : ℂ) := by
            rw [hsumEta]
            norm_num
  have hleft : ∑ X : Xset,
      star (degFam (Sum.inl X)) * fam (Sum.inl X) (ConjClasses.mk (z : L)) =
      ∑ X : Xset, (degX X : ℂ) * (X : Section1.ClassFunction L) (z : L) := by
    refine Finset.sum_congr rfl ?_
    intro X _hX
    dsimp [fam, degFam]
    rw [Section1.toConjClassFunction_apply]
    simp
  have hright : ∑ k : κ,
      star (degFam (Sum.inr k)) * fam (Sum.inr k) (ConjClasses.mk (z : L)) =
      (Nat.card (L ⧸ Z) : ℂ) := by
    calc
      ∑ k : κ, star (degFam (Sum.inr k)) * fam (Sum.inr k) (ConjClasses.mk (z : L)) =
          ∑ k : κ,
            star (η k (ConjClasses.mk (1 : L ⧸ Z))) *
              η k (ConjClasses.mk (QuotientGroup.mk' Z (z : L))) := by
            refine Finset.sum_congr rfl ?_
            intro k _hk
            dsimp [fam, degFam, theorem_6_6_quotientInflationConj]
            rfl
      _ = (Nat.card (L ⧸ Z) : ℂ) := hquot
  have hzL : (z : L) ≠ 1 := by
    intro hzL
    exact hz (Subtype.ext hzL)
  have htotal :
      0 =
        (∑ X : Xset,
            (degX X : ℂ) * (X : Section1.ClassFunction L) (z : L)) +
          (Nat.card (L ⧸ Z) : ℂ) := by
    rw [Fintype.sum_sum_type] at hreg
    rw [hleft, hright] at hreg
    simpa [regularCharacter, hzL] using hreg
  calc
    (∑ X : Xset, (degX X : ℂ) * (X : Section1.ClassFunction L) (z : L)) =
        ((∑ X : Xset,
            (degX X : ℂ) * (X : Section1.ClassFunction L) (z : L)) +
          (Nat.card (L ⧸ Z) : ℂ)) - (Nat.card (L ⧸ Z) : ℂ) := by ring
    _ = - (Nat.card (L ⧸ Z) : ℂ) := by
      rw [← htotal]
      ring

public theorem theorem_6_6_orthogonal_Xset_complement_subgroupInKernel
    {L : Type u} [Group L] [Finite L]
    {Z : Subgroup L} [Z.Normal]
    {Xset : Finset (Section1.ClassFunction L)}
    (hXchar : ∀ χ : Section1.ClassFunction L, χ ∈ Xset ↔
      Section1.IsIrreducibleCharacterOnGroup χ ∧
        ¬ Section1.subgroupInKernel' χ Z)
    {φ : Section1.ClassFunction L}
    (hφclass : Section1.IsClassFunction φ)
    (horth : ∀ χ : Xset,
      Section1.scalarProduct L φ (χ : Section1.ClassFunction L) = 0) :
    Section1.subgroupInKernel' φ Z := by
  classical
  rcases theorem_6_6_completeFamily_with_nonkernel
      (Z := Z) (Xset := Xset) hXchar with
    ⟨κ, hκ, η, hη, hfam⟩
  let : Fintype κ := hκ
  let fam : Sum Xset κ → Theory.Character.ConjClassFunction L := fun s =>
    match s with
    | Sum.inl X =>
        Section1.toConjClassFunction (X : Section1.ClassFunction L)
          (theorem_6_6_isClassFunction_of_irreducibleCharacterOnGroup
            ((hXchar (X : Section1.ClassFunction L)).1 X.2).1)
    | Sum.inr k => theorem_6_6_quotientInflationConj (Z := Z) (η k)
  let Φ : Theory.Character.ConjClassFunction L :=
    Section1.toConjClassFunction φ hφclass
  intro z
  have hsum_eq :
      (∑ s : Sum Xset κ,
          Theory.Character.classFunctionInner Φ (fam s) *
            fam s (ConjClasses.mk (z : L))) =
        (∑ s : Sum Xset κ,
          Theory.Character.classFunctionInner Φ (fam s) *
            fam s (ConjClasses.mk (1 : L))) := by
    refine Finset.sum_congr rfl ?_
    intro s _hs
    cases s with
    | inl X =>
        have hinner :
            Theory.Character.classFunctionInner Φ (fam (Sum.inl X)) = 0 := by
          dsimp [Φ, fam]
          rw [Section1.classFunctionInner_toConjClassFunction]
          exact horth X
        simp [hinner]
    | inr k =>
        have heval :
            fam (Sum.inr k) (ConjClasses.mk (z : L)) =
              fam (Sum.inr k) (ConjClasses.mk (1 : L)) := by
          dsimp [fam, theorem_6_6_quotientInflationConj]
          have hzq : QuotientGroup.mk' Z (z : L) =
              QuotientGroup.mk' Z (1 : L) := by
            have hzq1 : QuotientGroup.mk' Z (z : L) = 1 :=
              (QuotientGroup.eq_one_iff (N := Z) (x := (z : L))).2 z.2
            have h1q : QuotientGroup.mk' Z (1 : L) = 1 := by simp
            rw [hzq1, h1q]
          change η k (ConjClasses.mk (QuotientGroup.mk' Z (z : L))) =
            η k (ConjClasses.mk (QuotientGroup.mk' Z (1 : L)))
          rw [hzq]
        rw [heval]
  have hz :
      Φ (ConjClasses.mk (z : L)) =
        ∑ s : Sum Xset κ,
          Theory.Character.classFunctionInner Φ (fam s) *
            fam s (ConjClasses.mk (z : L)) := by
    simpa [fam] using
      (Theory.Character.completeFamily_apply_eq_sum_inner hfam Φ
        (ConjClasses.mk (z : L)))
  have h1 :
      Φ (ConjClasses.mk (1 : L)) =
        ∑ s : Sum Xset κ,
          Theory.Character.classFunctionInner Φ (fam s) *
            fam s (ConjClasses.mk (1 : L)) := by
    simpa [fam] using
      (Theory.Character.completeFamily_apply_eq_sum_inner hfam Φ
        (ConjClasses.mk (1 : L)))
  calc
    φ (z : L) = Φ (ConjClasses.mk (z : L)) := rfl
    _ = ∑ s : Sum Xset κ,
          Theory.Character.classFunctionInner Φ (fam s) *
            fam s (ConjClasses.mk (z : L)) := hz
    _ = ∑ s : Sum Xset κ,
          Theory.Character.classFunctionInner Φ (fam s) *
            fam s (ConjClasses.mk (1 : L)) := hsum_eq
    _ = Φ (ConjClasses.mk (1 : L)) := h1.symm
    _ = Section1.degree φ := by rfl

def theorem_6_6_pairExtensionDegreeData
    {L : Type u} [Group L] [Finite L]
    (S1 : Finset (Section1.ClassFunction L))
    (X1 : S1)
    (X : Section1.ClassFunction L) : Prop :=
  ∃ d1 dX : ℕ,
    Section1.degree (X1 : Section1.ClassFunction L) = (d1 : ℂ) ∧
      Section1.degree X = (dX : ℂ) ∧
        d1 ∣ dX ∧
          ∃ dS1 : S1 → ℕ,
            (∀ Y : S1,
              Section1.degree (Y : Section1.ClassFunction L) = (dS1 Y : ℂ)) ∧
              2 * (dX : ℝ) * (d1 : ℝ) <
                ∑ Y : S1,
                  (((dS1 Y : ℝ) ^ (2 : ℕ)) /
                    Section5.cfNormSq (Y : Section1.ClassFunction L))

def theorem_6_6_pairExtensionStepData
    {L : Type u} [Group L] [Finite L]
    (S S1 : Finset (Section1.ClassFunction L)) : Prop :=
  ∃ X : S,
    Section1.conjugateCharacter (X : Section1.ClassFunction L) ∉ S1 ∧
      ∃ X1 : S1,
        theorem_6_6_pairExtensionDegreeData S1 X1 (X : Section1.ClassFunction L)

theorem theorem_6_6_conjugateCharacter_involutive
    {L : Type u} [Group L]
    (χ : Section1.ClassFunction L) :
    Section1.conjugateCharacter (Section1.conjugateCharacter χ) = χ := by
  ext g
  simp [Section1.conjugateCharacter]

theorem theorem_6_6_coherent_of_pair_extension_steps
    {L : Type u} [Group L] [Finite L]
    {G : Type u} [Group G] [Finite G]
    (S0 S : Finset (Section1.ClassFunction L))
    (T : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G)
    (h52 : Section5.hypothesis_5_2_statement S T)
    (hS0S : S0 ⊆ S)
    (hS0closed : ∀ χ : Section1.ClassFunction L, χ ∈ S0 →
      Section1.conjugateCharacter χ ∈ S0)
    (hS0coherent : coherentFamily S0 T)
    (hstep : ∀ S1 : Finset (Section1.ClassFunction L),
      S0 ⊆ S1 →
        S1 ⊆ S →
          (∀ χ : Section1.ClassFunction L, χ ∈ S1 →
            Section1.conjugateCharacter χ ∈ S1) →
            coherentFamily S1 T →
              S1 ≠ S →
                theorem_6_6_pairExtensionStepData S S1) :
    coherentFamily S T := by
  classical
  rcases h52 with ⟨hsetup, R, h52a, h52b, h52c, h52d, h52e⟩
  let Q : ℕ → Prop := fun n =>
    ∀ S1 : Finset (Section1.ClassFunction L),
      (S \ S1).card = n →
        S0 ⊆ S1 →
          S1 ⊆ S →
            (∀ χ : Section1.ClassFunction L, χ ∈ S1 →
              Section1.conjugateCharacter χ ∈ S1) →
              coherentFamily S1 T →
                coherentFamily S T
  have hQ : ∀ n, Q n := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
        intro S1 hcard hS0S1 hS1S hS1closed hS1coherent
        by_cases hS1eq : S1 = S
        · simpa [hS1eq] using hS1coherent
        · rcases hstep S1 hS0S1 hS1S hS1closed hS1coherent hS1eq with
            ⟨X, hXbarNotin, X1, hdegData⟩
          let pair : Finset (Section1.ClassFunction L) :=
            {(X : Section1.ClassFunction L),
              Section1.conjugateCharacter (X : Section1.ClassFunction L)}
          let Snew : Finset (Section1.ClassFunction L) := S1 ∪ pair
          have hS1Snew : S1 ⊆ Snew := by
            intro χ hχ
            exact Finset.mem_union_left pair hχ
          have hSnewS : Snew ⊆ S := by
            intro χ hχ
            simp only [Snew, pair, Finset.mem_union, Finset.mem_insert,
              Finset.mem_singleton] at hχ
            rcases hχ with hχ | hχ | hχ
            · exact hS1S hχ
            · subst χ
              exact X.property
            · subst χ
              exact (h52a X).1
          have hSnewClosed : ∀ χ : Section1.ClassFunction L, χ ∈ Snew →
              Section1.conjugateCharacter χ ∈ Snew := by
            intro χ hχ
            simp only [Snew, pair, Finset.mem_union, Finset.mem_insert,
              Finset.mem_singleton] at hχ ⊢
            rcases hχ with hχ | hχ | hχ
            · exact Or.inl (hS1closed χ hχ)
            · subst hχ
              exact Or.inr (Or.inr rfl)
            · subst hχ
              exact Or.inr (Or.inl
                (theorem_6_6_conjugateCharacter_involutive
                  (X : Section1.ClassFunction L)))
          have hSnewCoherent : coherentFamily Snew T := by
            have hdef :=
              Section5.theorem_5_6 S T R hsetup h52a h52b h52c h52d h52e
                S1 hS1S hS1closed X hXbarNotin X1
                (by simpa [coherentFamily] using hS1coherent)
                hdegData
            simpa [coherentFamily, Snew, pair] using hdef
          have hdiffStrict : S \ Snew ⊂ S \ S1 := by
            refine (Finset.ssubset_iff_of_subset ?_).2 ?_
            · intro χ hχ
              rw [Finset.mem_sdiff] at hχ ⊢
              exact ⟨hχ.1, fun hχS1 => hχ.2 (hS1Snew hχS1)⟩
            · refine ⟨Section1.conjugateCharacter
                  (X : Section1.ClassFunction L), ?_, ?_⟩
              · rw [Finset.mem_sdiff]
                exact ⟨(h52a X).1, hXbarNotin⟩
              · rw [Finset.mem_sdiff]
                intro hbad
                exact hbad.2 (by
                  simp only [Snew, pair, Finset.mem_union, Finset.mem_insert,
                    Finset.mem_singleton]
                  exact Or.inr (Or.inr trivial))
          have hmeasure :
              (S \ Snew).card < (S \ S1).card :=
            Finset.card_lt_card hdiffStrict
          exact ih (S \ Snew).card (by simpa [hcard] using hmeasure)
            Snew rfl (fun χ hχ => hS1Snew (hS0S1 hχ)) hSnewS hSnewClosed
            hSnewCoherent
  exact hQ (S \ S0).card S0 rfl (fun _ hχ => hχ) hS0S hS0closed hS0coherent

theorem theorem_6_6_subset_base
    {L : Type u} [Group L] [Finite L]
    {S SZ Xset : Finset (Section1.ClassFunction L)}
    (hXeq : Xset = S \ SZ) :
    Xset ⊆ S := by
  intro χ hχ
  have hdiff : χ ∈ S \ SZ := by
    simpa [hXeq] using hχ
  exact (Finset.mem_sdiff.mp hdiff).1

theorem theorem_6_6_hypothesis_5_2_Xset
    {L : Type u} [Group L] [Finite L]
    {G : Type u} [Group G] [Finite G]
    {K : Subgroup L}
    {S SZ Xset : Finset (Section1.ClassFunction L)}
    {T : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
    (h61 : hypothesis_6_1_statement K S T)
    (hXeq : Xset = S \ SZ)
    (hXnonempty : Xset.Nonempty)
    (hXclosed : ∀ χ : Section1.ClassFunction L, χ ∈ Xset →
      Section1.conjugateCharacter χ ∈ Xset) :
    Section5.hypothesis_5_2_statement Xset T := by
  exact Section5.hypothesis_5_2_statement_subset
    (theorem_6_6_subset_base hXeq) hXnonempty hXclosed
    (hypothesis_6_1_hypothesis_5_2 h61)

theorem theorem_6_6_integerSpanOnNonempty_Xset_of_mem
    {L : Type u} [Group L] [Finite L]
    {G : Type u} [Group G] [Finite G]
    {K : Subgroup L}
    {S SZ Xset : Finset (Section1.ClassFunction L)}
    {T : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
    (h61 : hypothesis_6_1_statement K S T)
    (hXeq : Xset = S \ SZ)
    (hXclosed : ∀ χ : Section1.ClassFunction L, χ ∈ Xset →
      Section1.conjugateCharacter χ ∈ Xset)
    {χ : Section1.ClassFunction L}
    (hχX : χ ∈ Xset) :
    Section5.integerSpanOnNonempty Xset Section5.puncturedSet := by
  have h52X : Section5.hypothesis_5_2_statement Xset T :=
    theorem_6_6_hypothesis_5_2_Xset h61 hXeq ⟨χ, hχX⟩ hXclosed
  rcases h52X with ⟨hsetup, _R, h52a, _h52b, _h52c, _h52d, _h52e⟩
  let X : Xset := ⟨χ, hχX⟩
  exact Section5.integerSpanOnNonempty_of_conjugate_pair
    hχX (hXclosed χ hχX) (h52a X).2 (hsetup.2 X)

theorem theorem_6_6_coherent_Xset_of_coherent_base
    {L : Type u} [Group L] [Finite L]
    {G : Type u} [Group G] [Finite G]
    {K : Subgroup L}
    {S SZ Xset : Finset (Section1.ClassFunction L)}
    {T : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
    (h61 : hypothesis_6_1_statement K S T)
    (hXeq : Xset = S \ SZ)
    (hXclosed : ∀ χ : Section1.ClassFunction L, χ ∈ Xset →
      Section1.conjugateCharacter χ ∈ Xset)
    (hXnonempty : Xset.Nonempty)
    (hcohS : coherentFamily S T) :
    coherentFamily Xset T := by
  rcases hXnonempty with ⟨χ, hχX⟩
  exact coherentFamily_mono (theorem_6_6_subset_base hXeq)
    (theorem_6_6_integerSpanOnNonempty_Xset_of_mem
      h61 hXeq hXclosed hχX)
    hcohS

theorem theorem_6_6_not_coherent_base_of_not_coherent_Xset
    {L : Type u} [Group L] [Finite L]
    {G : Type u} [Group G] [Finite G]
    {K : Subgroup L}
    {S SZ Xset : Finset (Section1.ClassFunction L)}
    {T : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
    (h61 : hypothesis_6_1_statement K S T)
    (hXeq : Xset = S \ SZ)
    (hXclosed : ∀ χ : Section1.ClassFunction L, χ ∈ Xset →
      Section1.conjugateCharacter χ ∈ Xset)
    (hXnonempty : Xset.Nonempty)
    (hnotX : ¬ coherentFamily Xset T) :
    ¬ coherentFamily S T := by
  intro hcohS
  exact hnotX
    (theorem_6_6_coherent_Xset_of_coherent_base
      h61 hXeq hXclosed hXnonempty hcohS)

def theorem_6_6_degreeSubfamily
    {L : Type u} [Group L] [Finite L]
    (S : Finset (Section1.ClassFunction L))
    (d : ℕ) : Finset (Section1.ClassFunction L) :=
  S.filter fun χ => Section1.degree χ = (d : ℂ)

theorem theorem_6_6_degreeSubfamily_subset
    {L : Type u} [Group L] [Finite L]
    (S : Finset (Section1.ClassFunction L))
    (d : ℕ) :
    theorem_6_6_degreeSubfamily S d ⊆ S := by
  intro χ hχ
  exact (Finset.mem_filter.mp hχ).1

theorem theorem_6_6_degreeSubfamily_degree
    {L : Type u} [Group L] [Finite L]
    {S : Finset (Section1.ClassFunction L)}
    {d : ℕ}
    {χ : Section1.ClassFunction L}
    (hχ : χ ∈ theorem_6_6_degreeSubfamily S d) :
    Section1.degree χ = (d : ℂ) :=
  (Finset.mem_filter.mp hχ).2

theorem theorem_6_6_degree_eq_nat_of_isCharacter
    {L : Type u} [Group L] [Finite L]
    {χ : Section1.ClassFunction L}
    (hχ : Section1.IsCharacter χ) :
    ∃ d : ℕ, Section1.degree χ = (d : ℂ) := by
  rcases hχ with ⟨V, _hadd, _hmod, _hfd, ρ, rfl⟩
  exact ⟨Module.finrank ℂ V, Section1.degree_representation_character ρ⟩

theorem theorem_6_6_degree_conjugateCharacter_eq_of_isCharacter
    {L : Type u} [Group L] [Finite L]
    {χ : Section1.ClassFunction L}
    (hχ : Section1.IsCharacter χ) :
    Section1.degree (Section1.conjugateCharacter χ) = Section1.degree χ := by
  rcases theorem_6_6_degree_eq_nat_of_isCharacter hχ with ⟨d, hd⟩
  calc
    Section1.degree (Section1.conjugateCharacter χ) = star (Section1.degree χ) := by
      simp [Section1.degree, Section1.conjugateCharacter]
    _ = Section1.degree χ := by
      rw [hd]
      simp

theorem theorem_6_6_degreeSubfamily_conjugate_closed
    {L : Type u} [Group L] [Finite L]
    {G : Type u} [Group G] [Finite G]
    {S : Finset (Section1.ClassFunction L)}
    {T : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
    (h52 : Section5.hypothesis_5_2_statement S T)
    (d : ℕ) :
    ∀ χ : Section1.ClassFunction L,
      χ ∈ theorem_6_6_degreeSubfamily S d →
        Section1.conjugateCharacter χ ∈ theorem_6_6_degreeSubfamily S d := by
  rcases h52 with ⟨hsetup, _R, h52a, _h52b, _h52c, _h52d, _h52e⟩
  intro χ hχ
  rw [theorem_6_6_degreeSubfamily, Finset.mem_filter] at hχ ⊢
  exact ⟨(h52a ⟨χ, hχ.1⟩).1, by
    rw [theorem_6_6_degree_conjugateCharacter_eq_of_isCharacter
      (hsetup.2 ⟨χ, hχ.1⟩), hχ.2]⟩

theorem theorem_6_6_coherent_degreeSubfamily
    {L : Type u} [Group L] [Finite L]
    {G : Type u} [Group G] [Finite G]
    (S : Finset (Section1.ClassFunction L))
    (T : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G)
    (d : ℕ)
    (h52 : Section5.hypothesis_5_2_statement S T)
    (hne : (theorem_6_6_degreeSubfamily S d).Nonempty) :
    coherentFamily (theorem_6_6_degreeSubfamily S d) T := by
  classical
  let S0 : Finset (Section1.ClassFunction L) := theorem_6_6_degreeSubfamily S d
  have hclosed : ∀ χ : Section1.ClassFunction L, χ ∈ S0 →
      Section1.conjugateCharacter χ ∈ S0 := by
    simpa [S0] using theorem_6_6_degreeSubfamily_conjugate_closed h52 d
  have h52S0 : Section5.hypothesis_5_2_statement S0 T :=
    Section5.hypothesis_5_2_statement_subset
      (by simpa [S0] using theorem_6_6_degreeSubfamily_subset S d)
      (by simpa [S0] using hne) hclosed h52
  rcases h52S0 with ⟨hsetup, R, h52a, h52b, h52c, h52d, h52e⟩
  have hdeg : ∀ X Y : S0,
      Section1.degree (X : Section1.ClassFunction L) =
        Section1.degree (Y : Section1.ClassFunction L) := by
    intro X Y
    have hX : Section1.degree (X : Section1.ClassFunction L) = (d : ℂ) := by
      exact theorem_6_6_degreeSubfamily_degree (S := S) (d := d) X.2
    have hY : Section1.degree (Y : Section1.ClassFunction L) = (d : ℂ) := by
      exact theorem_6_6_degreeSubfamily_degree (S := S) (d := d) Y.2
    exact hX.trans hY.symm
  simpa [coherentFamily, S0] using
    (Section5.theorem_5_7 S0 T R hsetup h52a h52b h52c h52d h52e hdeg)

theorem theorem_6_6_exists_nonabelianPQuotient_of_not_coherent_Xset
    {L : Type u} [Group L] [Finite L]
    {G : Type u} [Group G] [Finite G]
    {K H1 : Subgroup L}
    {S SZ Xset : Finset (Section1.ClassFunction L)}
    {T : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
    (h64 : hypothesis_6_4_statement K ⊥ H1 S T)
    (hSbot : inducedKernelFamily K ⊥ S)
    (hXeq : Xset = S \ SZ)
    (hXclosed : ∀ χ : Section1.ClassFunction L, χ ∈ Xset →
      Section1.conjugateCharacter χ ∈ Xset)
    (hXnonempty : Xset.Nonempty)
    (hnotX : ¬ coherentFamily Xset T) :
    ∃ p : ℕ, nonabelianPQuotient (⊥ : Subgroup L) K p := by
  rcases h64 with ⟨h61, hoddL, hbotH1, hbotK, hnil, hcomm, hfrob⟩
  have hnotS : ¬ coherentFamily S T :=
    theorem_6_6_not_coherent_base_of_not_coherent_Xset
      h61 hXeq hXclosed hXnonempty hnotX
  exact theorem_6_5_b K ⊥ H1 S S T
    ⟨h61, hoddL, hbotH1, hbotK, hnil, hcomm, hfrob⟩ hSbot hnotS

theorem theorem_6_6_exists_irreducible_not_subgroupInKernel
    {L : Type u} [Group L] [Finite L]
    {Z : Subgroup L} (hZne : Z ≠ ⊥) :
    ∃ χ : Section1.ClassFunction L,
      Section1.IsIrreducibleCharacterOnGroup χ ∧
        ¬ Section1.subgroupInKernel' χ Z := by
  classical
  obtain ⟨z, hz_ne⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hZne
  rcases Theory.Character.second_orthogonality (G := L) with ⟨ι, hι, χ, hχ, horth⟩
  let : Fintype ι := hι
  by_contra hnone
  push Not at hnone
  have hall : ∀ i : ι,
      χ i (ConjClasses.mk (z : L)) = χ i (ConjClasses.mk (1 : L)) := by
    intro i
    have hbook :
        Section1.IsBookIrreducibleCharacter
          (Section1.ofConjClassFunction (χ i)) :=
      Section1.isBookIrreducibleCharacter_of_representation_irreducible
        (χ i) (hχ.1 i)
    have hon :
        Section1.IsIrreducibleCharacterOnGroup
          (Section1.ofConjClassFunction (χ i)) := by
      rcases Section1.isBookIrreducibleCharacter_representation_witness_irreducible
          (Section1.ofConjClassFunction (χ i)) hbook with
        ⟨V, _hadd, _hmod, _hfd, ρ, hρchar, hρirr⟩
      refine ⟨Module.finrank ℂ V, Section1.standardizeRepresentation ρ,
        Section1.standardizeRepresentation_irreducible ρ hρirr, ?_⟩
      ext g
      rw [hρchar]
      exact (Section1.standardizeRepresentation_character ρ g).symm
    have hker :
        Section1.subgroupInKernel' (Section1.ofConjClassFunction (χ i)) Z :=
      hnone (Section1.ofConjClassFunction (χ i)) hon
    have hval := hker z
    simpa [Section1.ofConjClassFunction_apply, Section1.degree] using hval
  have hsum_zero :
      ∑ i : ι, χ i (ConjClasses.mk (z : L)) *
          star (χ i (ConjClasses.mk (1 : L))) = 0 := by
    exact (horth (z : L) (1 : L)).2 (by
      intro hmk
      have hconj : IsConj (z : L) (1 : L) :=
        ConjClasses.mk_eq_mk_iff_isConj.mp hmk
      rcases isConj_iff.mp hconj with ⟨_g, hg⟩
      have hz1 : (z : L) = 1 := by simpa using hg
      exact hz_ne (Subtype.ext hz1))
  have hsum_card :
      ∑ i : ι, χ i (ConjClasses.mk (1 : L)) *
          star (χ i (ConjClasses.mk (1 : L))) = (Nat.card L : ℂ) := by
    have h := (horth (1 : L) (1 : L)).1 rfl
    have hcard : Nat.card { x : L // x * 1 = 1 * x } = Nat.card L := by
      exact Nat.card_congr
        { toFun := fun x => x.1
          invFun := fun x => ⟨x, by simp⟩
          left_inv := by intro x; cases x; rfl
          right_inv := by intro x; rfl }
    simpa [hcard] using h
  have hsum_eq :
      ∑ i : ι, χ i (ConjClasses.mk (z : L)) *
          star (χ i (ConjClasses.mk (1 : L))) =
        ∑ i : ι, χ i (ConjClasses.mk (1 : L)) *
          star (χ i (ConjClasses.mk (1 : L))) := by
    refine Finset.sum_congr rfl ?_
    intro i _hi
    rw [hall i]
  have hcard_zero : (Nat.card L : ℂ) = 0 := by
    rw [← hsum_card, ← hsum_eq]
    exact hsum_zero
  exact (Nat.cast_ne_zero.mpr (Nat.card_pos (α := L)).ne') hcard_zero

theorem theorem_6_6_Xset_nonempty
    {L : Type u} [Group L] [Finite L]
    {Z : Subgroup L} {Xset : Finset (Section1.ClassFunction L)}
    (hZne : Z ≠ ⊥)
    (hXchar : ∀ χ : Section1.ClassFunction L, χ ∈ Xset ↔
      Section1.IsIrreducibleCharacterOnGroup χ ∧
        ¬ Section1.subgroupInKernel' χ Z) :
    Xset.Nonempty := by
  rcases theorem_6_6_exists_irreducible_not_subgroupInKernel
      (L := L) (Z := Z) hZne with
    ⟨χ, hχ⟩
  exact ⟨χ, (hXchar χ).2 hχ⟩

theorem theorem_6_6_ordered_degree_divisibility
    {L : Type u} [Group L] [Finite L]
    {G : Type u} [Group G] [Finite G]
    {K H1 Z : Subgroup L}
    {S SZ Xset : Finset (Section1.ClassFunction L)}
    {T : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
    (h64 : hypothesis_6_4_statement K ⊥ H1 S T)
    (hSbot : inducedKernelFamily K ⊥ S)
    (_hZne : Z ≠ ⊥) (hZcenter : Z ≤ centerIn K) (hZnorm : Z.Normal)
    (_hSZ : inducedKernelFamily K Z SZ)
    (hXeq : Xset = S \ SZ)
    (hXchar : ∀ χ : Section1.ClassFunction L, χ ∈ Xset ↔
      Section1.IsIrreducibleCharacterOnGroup χ ∧
        ¬ Section1.subgroupInKernel' χ Z)
    (hXirr : ∀ χ : Section1.ClassFunction L, χ ∈ Xset →
      Section1.IsIrreducibleCharacterOnGroup χ)
    (hXclosed : ∀ χ : Section1.ClassFunction L, χ ∈ Xset →
      Section1.conjugateCharacter χ ∈ Xset)
    (hXnonempty : Xset.Nonempty)
    {p : ℕ}
    (hpQ : nonabelianPQuotient (⊥ : Subgroup L) K p)
    (hnotX : ¬ coherentFamily Xset T) :
    K.relIndex (⊤ : Subgroup L) ∣ p - 1 := by
  classical
  exfalso
  rcases h64 with ⟨h61, _hoddL, _hbotH1, _hbotK, _hnil, _hcomm, _hfrob⟩
  have h52X : Section5.hypothesis_5_2_statement Xset T :=
    theorem_6_6_hypothesis_5_2_Xset h61 hXeq hXnonempty hXclosed
  let degX : Xset → ℕ := fun X =>
    Classical.choose (theorem_6_6_positive_degree_nat_of_irreducible
      (hXirr (X : Section1.ClassFunction L) X.2))
  have hdegX_spec : ∀ X : Xset,
      0 < degX X ∧
        Section1.degree (X : Section1.ClassFunction L) = (degX X : ℂ) := by
    intro X
    exact Classical.choose_spec
      (theorem_6_6_positive_degree_nat_of_irreducible
        (hXirr (X : Section1.ClassFunction L) X.2))
  have huniv_nonempty : (Finset.univ : Finset Xset).Nonempty := by
    rcases hXnonempty with ⟨χ, hχX⟩
    exact ⟨⟨χ, hχX⟩, by simp⟩
  rcases Finset.exists_min_image (Finset.univ : Finset Xset) degX huniv_nonempty with
    ⟨X0, _hX0univ, hX0min⟩
  let d0 : ℕ := degX X0
  let S0 : Finset (Section1.ClassFunction L) := theorem_6_6_degreeSubfamily Xset d0
  have hS0subset : S0 ⊆ Xset := by
    simpa [S0] using theorem_6_6_degreeSubfamily_subset Xset d0
  have hX0S0 : (X0 : Section1.ClassFunction L) ∈ S0 := by
    change (X0 : Section1.ClassFunction L) ∈ theorem_6_6_degreeSubfamily Xset d0
    rw [theorem_6_6_degreeSubfamily, Finset.mem_filter]
    exact ⟨X0.2, (hdegX_spec X0).2⟩
  have hS0nonempty : S0.Nonempty := ⟨X0, hX0S0⟩
  have hS0closed : ∀ χ : Section1.ClassFunction L, χ ∈ S0 →
      Section1.conjugateCharacter χ ∈ S0 := by
    simpa [S0] using theorem_6_6_degreeSubfamily_conjugate_closed h52X d0
  have hS0coherent : coherentFamily S0 T := by
    simpa [S0] using theorem_6_6_coherent_degreeSubfamily Xset T d0 h52X hS0nonempty
  have hstep : ∀ S1 : Finset (Section1.ClassFunction L),
      S0 ⊆ S1 →
        S1 ⊆ Xset →
          (∀ χ : Section1.ClassFunction L, χ ∈ S1 →
            Section1.conjugateCharacter χ ∈ S1) →
            coherentFamily S1 T →
              S1 ≠ Xset →
                theorem_6_6_pairExtensionStepData Xset S1 := by
    intro S1 hS0S1 hS1X hS1closed hS1coh hS1ne
    have hcomp_nonempty : (Xset \ S1).Nonempty := by
      rw [Finset.sdiff_nonempty]
      intro hXsubset
      apply hS1ne
      exact Finset.Subset.antisymm hS1X hXsubset
    let C : Finset (Section1.ClassFunction L) := Xset \ S1
    let degC : C → ℕ := fun X =>
      degX ⟨(X : Section1.ClassFunction L), (Finset.mem_sdiff.mp X.2).1⟩
    have hCuniv_nonempty : (Finset.univ : Finset C).Nonempty := by
      rcases hcomp_nonempty with ⟨χ, hχC⟩
      exact ⟨⟨χ, hχC⟩, by simp⟩
    rcases Finset.exists_min_image (Finset.univ : Finset C) degC hCuniv_nonempty with
      ⟨Xmin, _hXmin_univ, hXmin_min⟩
    let X : Xset :=
      ⟨(Xmin : Section1.ClassFunction L), (Finset.mem_sdiff.mp Xmin.2).1⟩
    have hXnotS1 : (X : Section1.ClassFunction L) ∉ S1 :=
      (Finset.mem_sdiff.mp Xmin.2).2
    have hXbarNotS1 :
        Section1.conjugateCharacter (X : Section1.ClassFunction L) ∉ S1 := by
      intro hbar
      have hbarbar :
          Section1.conjugateCharacter
              (Section1.conjugateCharacter (X : Section1.ClassFunction L)) ∈ S1 :=
        hS1closed _ hbar
      exact hXnotS1 (by
        simpa [theorem_6_6_conjugateCharacter_involutive
          (X : Section1.ClassFunction L)] using hbarbar)
    let X1 : S1 := ⟨(X0 : Section1.ClassFunction L), hS0S1 hX0S0⟩
    refine ⟨X, hXbarNotS1, X1, ?_⟩
    let dS1 : S1 → ℕ := fun Y =>
      degX ⟨(Y : Section1.ClassFunction L), hS1X Y.2⟩
    have hX1deg :
        Section1.degree (X1 : Section1.ClassFunction L) = (d0 : ℂ) := by
      change Section1.degree (X0 : Section1.ClassFunction L) = (d0 : ℂ)
      exact (hdegX_spec X0).2
    have hXdeg :
        Section1.degree (X : Section1.ClassFunction L) = (degX X : ℂ) :=
      (hdegX_spec X).2
    have hdS1 : ∀ Y : S1,
        Section1.degree (Y : Section1.ClassFunction L) = (dS1 Y : ℂ) := by
      intro Y
      exact (hdegX_spec ⟨(Y : Section1.ClassFunction L), hS1X Y.2⟩).2
    refine ⟨d0, degX X, hX1deg, hXdeg, ?_, dS1, hdS1, ?_⟩
    · rcases theorem_6_6_degree_eq_relIndex_mul_prime_power
          (K := K) (Z := Z) (S := S) (SZ := SZ) (Xset := Xset)
          hSbot hXeq hpQ X0.2 with
        ⟨a0, dχ0, hχ0deg, hχ0eq⟩
      rcases theorem_6_6_degree_eq_relIndex_mul_prime_power
          (K := K) (Z := Z) (S := S) (SZ := SZ) (Xset := Xset)
          hSbot hXeq hpQ X.2 with
        ⟨a, dχ, hχdeg, hχeq⟩
      have hd0_eq_dχ0 : d0 = dχ0 := by
        have hcast : (d0 : ℂ) = (dχ0 : ℂ) := by
          rw [← (hdegX_spec X0).2, hχ0deg]
        exact_mod_cast hcast
      have hdX_eq_dχ : degX X = dχ := by
        have hcast : (degX X : ℂ) = (dχ : ℂ) := by
          rw [← (hdegX_spec X).2, hχdeg]
        exact_mod_cast hcast
      have hd0_eq : d0 = K.relIndex (⊤ : Subgroup L) * p ^ a0 := by
        simpa [hχ0eq] using hd0_eq_dχ0
      have hdX_eq : degX X = K.relIndex (⊤ : Subgroup L) * p ^ a := by
        simpa [hχeq] using hdX_eq_dχ
      have hn_pos : 0 < K.relIndex (⊤ : Subgroup L) := by
        rw [Subgroup.relIndex_top_right]
        exact Nat.pos_of_ne_zero (Subgroup.index_ne_zero_of_finite (H := K))
      have hpprime : Nat.Prime p := by
        rcases hpQ with ⟨_hbotK, _hbotnormK, _hbotnorm, _hKnorm, hpprime, _hQp, _hnoncomm⟩
        exact hpprime
      have hprod_le :
          K.relIndex (⊤ : Subgroup L) * p ^ a0 ≤
            K.relIndex (⊤ : Subgroup L) * p ^ a := by
        simpa [d0, hd0_eq, hdX_eq] using hX0min X (by simp)
      have hpow_le : p ^ a0 ≤ p ^ a :=
        Nat.le_of_mul_le_mul_left hprod_le hn_pos
      have ha_le : a0 ≤ a :=
        (Nat.pow_le_pow_iff_right hpprime.one_lt).1 hpow_le
      have hpow_dvd : p ^ a0 ∣ p ^ a := Nat.pow_dvd_pow p ha_le
      have hprod_dvd :
          K.relIndex (⊤ : Subgroup L) * p ^ a0 ∣
            K.relIndex (⊤ : Subgroup L) * p ^ a :=
        Nat.mul_dvd_mul_left (K.relIndex (⊤ : Subgroup L)) hpow_dvd
      simpa [hd0_eq, hdX_eq] using hprod_dvd
    · have hcfS1 : ∀ Y : S1,
        Section5.cfNormSq (Y : Section1.ClassFunction L) = 1 := by
        intro Y
        exact theorem_6_6_cfNormSq_irreducible
          (hXirr (Y : Section1.ClassFunction L) (hS1X Y.2))
      rcases theorem_6_6_degree_eq_relIndex_mul_prime_power
          (K := K) (Z := Z) (S := S) (SZ := SZ) (Xset := Xset)
          hSbot hXeq hpQ X0.2 with
        ⟨a0, dχ0, hχ0deg, hχ0eq⟩
      rcases theorem_6_6_degree_eq_relIndex_mul_prime_power_sq_dvd_Zrel
          (K := K) (Z := Z) (S := S) (SZ := SZ) (Xset := Xset)
          hSbot hXeq hZnorm hZcenter hpQ X.2 with
        ⟨a, dχ, hχdeg, hχeq, hp2a_dvd_Zrel⟩
      have hd0_eq_dχ0 : d0 = dχ0 := by
        have hcast : (d0 : ℂ) = (dχ0 : ℂ) := by
          rw [← (hdegX_spec X0).2, hχ0deg]
        exact_mod_cast hcast
      have hdX_eq_dχ : degX X = dχ := by
        have hcast : (degX X : ℂ) = (dχ : ℂ) := by
          rw [← (hdegX_spec X).2, hχdeg]
        exact_mod_cast hcast
      have hd0_eq : d0 = K.relIndex (⊤ : Subgroup L) * p ^ a0 := by
        simpa [hχ0eq] using hd0_eq_dχ0
      have hdX_eq : degX X = K.relIndex (⊤ : Subgroup L) * p ^ a := by
        simpa [hχeq] using hdX_eq_dχ
      have hn_pos : 0 < K.relIndex (⊤ : Subgroup L) := by
        rw [Subgroup.relIndex_top_right]
        exact Nat.pos_of_ne_zero (Subgroup.index_ne_zero_of_finite (H := K))
      have hd0_le_dX : d0 ≤ degX X := by
        simpa [d0] using hX0min X (by simp)
      have hd0_ne_dX : d0 ≠ degX X := by
        intro hEq
        apply hXnotS1
        apply hS0S1
        change (X : Section1.ClassFunction L) ∈ theorem_6_6_degreeSubfamily Xset d0
        rw [theorem_6_6_degreeSubfamily, Finset.mem_filter]
        exact ⟨X.2, by rw [(hdegX_spec X).2, ← hEq]⟩
      have hd0_lt_dX : d0 < degX X := lt_of_le_of_ne hd0_le_dX hd0_ne_dX
      have hpgt : 2 < p :=
        theorem_6_6_prime_gt_two_of_nonabelianPQuotient_odd _hoddL hpQ
      have hstrict :
          2 * (degX X : ℝ) * (d0 : ℝ) < (degX X : ℝ) ^ (2 : ℕ) :=
        theorem_6_6_two_mul_min_degree_lt_square_of_p_power_step
          hpgt hn_pos hd0_eq hdX_eq hd0_lt_dX
      have hdS1X1 : dS1 X1 = d0 := by
        have hcast : (dS1 X1 : ℂ) = (d0 : ℂ) := by
          rw [← hdS1 X1, hX1deg]
        exact_mod_cast hcast
      have hsumpos : 0 < ∑ Y : S1, dS1 Y ^ (2 : ℕ) := by
        have hd0_pos : 0 < d0 := (hdegX_spec X0).1
        have hterm_pos : 0 < dS1 X1 ^ (2 : ℕ) := by
          rw [hdS1X1]
          exact pow_pos hd0_pos _
        have hle : dS1 X1 ^ (2 : ℕ) ≤ ∑ Y : S1, dS1 Y ^ (2 : ℕ) := by
          simpa using (Finset.single_le_sum
            (s := (Finset.univ : Finset S1))
            (f := fun Y => dS1 Y ^ (2 : ℕ))
            (by intro y _hy; exact Nat.zero_le _)
            (by simp : X1 ∈ (Finset.univ : Finset S1)))
        exact lt_of_lt_of_le hterm_pos hle
      have hprefix_dvd :
          (degX X) ^ (2 : ℕ) ∣ ∑ Y : S1, dS1 Y ^ (2 : ℕ) := by
        have hpprime : Nat.Prime p := by
          rcases hpQ with
            ⟨_hbotK, _hbotnormK, _hbotnorm, _hKnorm, hpprime, _hQp,
              _hnoncomm⟩
          exact hpprime
        have hn_sq_dvd :
            (K.relIndex (⊤ : Subgroup L)) ^ (2 : ℕ) ∣
              ∑ Y : S1, dS1 Y ^ (2 : ℕ) := by
          apply theorem_6_6_sq_dvd_sum_of_dvd
          intro Y
          rcases theorem_6_6_degree_eq_relIndex_mul_prime_power
              (K := K) (Z := Z) (S := S) (SZ := SZ) (Xset := Xset)
              hSbot hXeq hpQ (hS1X Y.2) with
            ⟨b, dY, hYdeg, hYeq⟩
          have hcast : (dS1 Y : ℂ) = (dY : ℂ) := by
            rw [← hdS1 Y, hYdeg]
          have hdS1_eq : dS1 Y = dY := by
            exact_mod_cast hcast
          rw [hdS1_eq, hYeq]
          exact dvd_mul_right (K.relIndex (⊤ : Subgroup L)) (p ^ b)
        let : Z.Normal := hZnorm
        have hp_total :
            p ^ (2 * a) ∣ ∑ X' : Xset, degX X' ^ (2 : ℕ) := by
          have hZleK : Z ≤ K := theorem_6_6_centerIn_le hZcenter
          have hp_diff :
              p ^ (2 * a) ∣ Nat.card L - Nat.card (L ⧸ Z) :=
            theorem_6_6_dvd_card_sub_quotient_of_dvd_relIndex
              hZleK hp2a_dvd_Zrel
          have htotal_add :
              (∑ X' : Xset, degX X' ^ (2 : ℕ)) +
                  Nat.card (L ⧸ Z) = Nat.card L :=
            theorem_6_6_Xset_sum_degree_sq_add_quotient_card
              hXchar degX (fun X' => (hdegX_spec X').2)
          have htotal_eq :
              ∑ X' : Xset, degX X' ^ (2 : ℕ) =
                Nat.card L - Nat.card (L ⧸ Z) :=
            Nat.eq_sub_of_add_eq htotal_add
          rw [htotal_eq]
          exact hp_diff
        have hp_comp :
            p ^ (2 * a) ∣ ∑ Y : C, degC Y ^ (2 : ℕ) := by
          apply Finset.dvd_sum
          intro Y _hY
          have hYX : (Y : Section1.ClassFunction L) ∈ Xset :=
            (Finset.mem_sdiff.mp Y.2).1
          let Yx : Xset := ⟨(Y : Section1.ClassFunction L), hYX⟩
          rcases theorem_6_6_degree_eq_relIndex_mul_prime_power
              (K := K) (Z := Z) (S := S) (SZ := SZ) (Xset := Xset)
              hSbot hXeq hpQ Yx.2 with
            ⟨b, dY, hYdeg, hYeq⟩
          have hdegY_eq : degX Yx = dY := by
            have hcast : (degX Yx : ℂ) = (dY : ℂ) := by
              rw [← (hdegX_spec Yx).2, hYdeg]
            exact_mod_cast hcast
          have hdegC_eq : degC Y = dY := by
            simpa [degC, Yx] using hdegY_eq
          have hmin_deg : degX X ≤ degX Yx := by
            simpa [X, Yx, degC] using hXmin_min Y (by simp)
          have hprod_le :
              K.relIndex (⊤ : Subgroup L) * p ^ a ≤
                K.relIndex (⊤ : Subgroup L) * p ^ b := by
            simpa [hdX_eq, hdegY_eq, hYeq] using hmin_deg
          have hpow_le : p ^ a ≤ p ^ b :=
            Nat.le_of_mul_le_mul_left hprod_le hn_pos
          have ha_le : a ≤ b :=
            (Nat.pow_le_pow_iff_right hpprime.one_lt).1 hpow_le
          have hterm : p ^ (2 * a) ∣ dY ^ (2 : ℕ) :=
            theorem_6_6_prime_pow_sq_dvd_of_le_exponent hYeq ha_le
          simpa [hdegC_eq] using hterm
        have hpartition :
            (∑ Y : C, degC Y ^ (2 : ℕ)) +
                (∑ Y : S1, dS1 Y ^ (2 : ℕ)) =
              ∑ X' : Xset, degX X' ^ (2 : ℕ) := by
          simpa [C, degC, dS1] using
            theorem_6_6_sum_sdiff_subtype_add_sum_subtype
              (X := Xset) (S := S1) hS1X
              (fun X' : Xset => degX X' ^ (2 : ℕ))
        have hp_partitioned :
            p ^ (2 * a) ∣
              (∑ Y : C, degC Y ^ (2 : ℕ)) +
                (∑ Y : S1, dS1 Y ^ (2 : ℕ)) := by
          rw [hpartition]
          exact hp_total
        have hp_prefix :
            p ^ (2 * a) ∣ ∑ Y : S1, dS1 Y ^ (2 : ℕ) :=
          (Nat.dvd_add_iff_right hp_comp).2 hp_partitioned
        have hcop_np :
            Nat.Coprime (K.relIndex (⊤ : Subgroup L)) p :=
          have h64' : hypothesis_6_4_statement K ⊥ H1 S T :=
            ⟨h61, _hoddL, _hbotH1, _hbotK, _hnil, _hcomm, _hfrob⟩
          theorem_6_6_relIndex_top_coprime_prime_of_nonabelianPQuotient
            h64' hpQ
        have hcombined :
            (K.relIndex (⊤ : Subgroup L) * p ^ a) ^ (2 : ℕ) ∣
              ∑ Y : S1, dS1 Y ^ (2 : ℕ) :=
          theorem_6_6_mul_prime_pow_sq_dvd_of_coprime
            hcop_np hn_sq_dvd hp_prefix
        simpa [hdX_eq] using hcombined
      have hsq :
          (degX X : ℝ) ^ (2 : ℕ) ≤
            ∑ Y : S1, (dS1 Y : ℝ) ^ (2 : ℕ) :=
        theorem_6_6_square_lower_of_nat_dvd_sum dS1 hprefix_dvd hsumpos
      exact theorem_6_6_pairExtension_inequality_of_square_lower
        dS1 hcfS1 hstrict hsq
  have hcohX : coherentFamily Xset T :=
    theorem_6_6_coherent_of_pair_extension_steps S0 Xset T h52X hS0subset
      hS0closed hS0coherent hstep
  exact hnotX hcohX

theorem theorem_6_6_coherent_of_ordered_degree_divisibility
    {L : Type u} [Group L] [Finite L]
    {G : Type u} [Group G] [Finite G]
    {K H1 : Subgroup L}
    {S SZ Xset : Finset (Section1.ClassFunction L)}
    {T : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
    (h64 : hypothesis_6_4_statement K ⊥ H1 S T)
    (hSbot : inducedKernelFamily K ⊥ S)
    (hXeq : Xset = S \ SZ)
    (hXclosed : ∀ χ : Section1.ClassFunction L, χ ∈ Xset →
      Section1.conjugateCharacter χ ∈ Xset)
    (hXnonempty : Xset.Nonempty)
    (hdiv : ∀ {p : ℕ},
      nonabelianPQuotient (⊥ : Subgroup L) K p →
        ¬ coherentFamily Xset T →
          K.relIndex (⊤ : Subgroup L) ∣ p - 1) :
    coherentFamily Xset T := by
  classical
  by_contra hnotX
  rcases h64 with ⟨h61, hoddL, hbotH1, hbotK, hnil, hcomm, hfrob⟩
  have h64' : hypothesis_6_4_statement K ⊥ H1 S T :=
    ⟨h61, hoddL, hbotH1, hbotK, hnil, hcomm, hfrob⟩
  have hnotS : ¬ coherentFamily S T :=
    theorem_6_6_not_coherent_base_of_not_coherent_Xset
      h61 hXeq hXclosed hXnonempty hnotX
  rcases theorem_6_6_exists_nonabelianPQuotient_of_not_coherent_Xset
      h64' hSbot hXeq hXclosed hXnonempty hnotX with
    ⟨p, hpQ⟩
  exact theorem_6_5_c K ⊥ H1 S S T h64' hSbot hnotS
    p hpQ (hdiv hpQ hnotX)

theorem theorem_6_6_exists_irreducible_constituent_of_subgroupRestriction
    {L : Type u} [Group L] [Finite L]
    (K : Subgroup L)
    {χ : Section1.ClassFunction L}
    (hχ : Section1.IsIrreducibleCharacterOnGroup χ) :
    ∃ θ : Section1.ClassFunction K,
      Section1.IsIrreducibleCharacterOnGroup θ ∧
        Section1.scalarProduct K θ (Section1.subgroupRestriction K χ) ≠ 0 := by
  rcases hχ with ⟨n, ρ, hρirr, hρchar⟩
  let ρK : Representation ℂ K (Fin n → ℂ) := ρ.comp K.subtype
  let : Nontrivial (Fin n → ℂ) := Subrepresentation.irreducible_module_nontrivial ρ
  obtain ⟨φ, hφirr⟩ := Subrepresentation.irreducible_subrepresentation_of_finite_dimensional ρK
  let : Nontrivial φ.toSubmodule :=
    Subrepresentation.irreducible_module_nontrivial φ.toRepresentation
  let incl : Theory.Representation.RepMap φ.toRepresentation ρK := by
    refine Theory.Representation.RepMap.mk φ.toSubmodule.subtype ?_
    intro k
    ext v
    rfl
  have hincl_ne : incl ≠ 0 := by
    intro hzero
    obtain ⟨v, hv⟩ := exists_ne (0 : φ.toSubmodule)
    have hval : incl v = 0 := by
      simpa using congrArg (fun f : Theory.Representation.RepMap φ.toRepresentation ρK => f v) hzero
    have hsub : v = 0 := by
      apply Subtype.ext
      simpa [incl] using hval
    exact hv hsub
  have hinner_res :
      Section1.scalarProduct K ρK.character φ.toRepresentation.character ≠ 0 := by
    have hfinpos :
        0 < Module.finrank ℂ (Representation.IntertwiningMap φ.toRepresentation ρK) := by
      rw [Module.finrank_pos_iff_exists_ne_zero]
      exact ⟨incl, hincl_ne⟩
    rw [Section1.scalarProduct_representation_char_eq_finrank]
    exact_mod_cast (Nat.ne_of_gt hfinpos)
  have hresChar :
      Section1.subgroupRestriction K χ = ρK.character := by
    ext k
    simp [ρK, Section1.subgroupRestriction, hρchar, Representation.character]
  refine ⟨φ.toRepresentation.character, ?_, ?_⟩
  · refine ⟨Module.finrank ℂ φ.toSubmodule,
      Section1.standardizeRepresentation φ.toRepresentation, ?_, ?_⟩
    · exact Section1.standardizeRepresentation_irreducible φ.toRepresentation hφirr
    · ext k
      symm
      exact Section1.standardizeRepresentation_character φ.toRepresentation k
  · have hinner_res' :
        Section1.scalarProduct K (Section1.subgroupRestriction K χ)
          φ.toRepresentation.character ≠ 0 := by
      simpa [hresChar] using hinner_res
    exact
      (Section1.scalarProduct_ne_zero_swap
        φ.toRepresentation.character (Section1.subgroupRestriction K χ)).2 hinner_res'

theorem theorem_6_6_constituent_not_subgroupInKernel
    {L : Type u} [Group L] [Finite L]
    {K Z : Subgroup L} [K.Normal]
    (hZnorm : Z.Normal) (_hZcenter : Z ≤ centerIn K) (hZleK : Z ≤ K)
    {χ : Section1.ClassFunction L}
    (hχirr : Section1.IsIrreducibleCharacterOnGroup χ)
    (hχnotker : ¬ Section1.subgroupInKernel' χ Z)
    {θ : Section1.ClassFunction K}
    (hθirr : Section1.IsIrreducibleCharacterOnGroup θ)
    (hθinner :
      Section1.scalarProduct K θ (Section1.subgroupRestriction K χ) ≠ 0) :
    ¬ Section1.subgroupInKernel' θ (Z.subgroupOf K) := by
  classical
  intro hθker
  rcases hχirr with ⟨nχ, ρχ, hρχirr, hχeq⟩
  rcases hθirr with ⟨nθ, ρθ, _hρθirr, hθeq⟩
  let indρθ : Representation ℂ L (Representation.IndV K.subtype ρθ) :=
    Representation.ind K.subtype ρθ
  have : FiniteDimensional ℂ (Representation.IndV K.subtype ρθ) :=
    Theory.Representation.finiteDimensional_ind K ρθ
  have : Z.Normal := hZnorm
  have hIndCharKer :
      Section1.subgroupInKernel' (Section1.inducedCF K ρθ.character) Z :=
    (Section1.proposition_1_6_a K Z hZleK ρθ).mp
      (by simpa [hθeq] using hθker)
  have hIndRepKer : Section1.subgroupInRepresentationKernel indρθ Z :=
    (Section1.subgroupInKernel'_character_iff_subgroupInRepresentationKernel
      indρθ Z).mp (by
        simpa [indρθ, Section1.inducedCF_eq_representation_character K ρθ]
          using hIndCharKer)
  have hχclass : Section1.IsClassFunction χ :=
    theorem_6_6_isClassFunction_of_irreducibleCharacterOnGroup
      ⟨nχ, ρχ, hρχirr, hχeq⟩
  have hIndInner :
      Section1.scalarProduct L (Section1.inducedCF K θ) χ ≠ 0 := by
    rw [Section1.scalarProduct_inducedCF_left K θ χ hχclass]
    exact hθinner
  have hIndInnerRep :
      Section1.scalarProduct L indρθ.character ρχ.character ≠ 0 := by
    simpa [indρθ, hχeq, hθeq,
      Section1.inducedCF_eq_representation_character K ρθ] using hIndInner
  have hfinrank_ne :
      (Module.finrank ℂ (Representation.IntertwiningMap ρχ indρθ) : ℂ) ≠ 0 := by
    simpa [Section1.scalarProduct_representation_char_eq_finrank ρχ indρθ] using hIndInnerRep
  have hfinrank_nat_ne :
      Module.finrank ℂ (Representation.IntertwiningMap ρχ indρθ) ≠ 0 := by
    intro hzero
    apply hfinrank_ne
    simp [hzero]
  have hfinrank_pos :
      0 < Module.finrank ℂ (Representation.IntertwiningMap ρχ indρθ) :=
    Nat.pos_of_ne_zero hfinrank_nat_ne
  rw [Module.finrank_pos_iff_exists_ne_zero] at hfinrank_pos
  rcases hfinrank_pos with ⟨f, hf⟩
  have hχRepKer : Section1.subgroupInRepresentationKernel ρχ Z :=
    by
      let : Representation.IsIrreducible ρχ := hρχirr
      have hf_inj : Function.Injective f := by
        rcases (Representation.IsIrreducible.injective_or_eq_zero
            (ρ := ρχ) (σ := indρθ) f) with hinj | hzero
        · exact hinj
        · exact (hf hzero).elim
      intro z
      apply LinearMap.ext
      intro v
      apply hf_inj
      calc
        f (ρχ (z : L) v) = indρθ (z : L) (f v) := by
          exact Representation.IntertwiningMap.isIntertwining ρχ indρθ f (z : L) v
        _ = f v := by
          rw [hIndRepKer z]
          simp
  have hχker : Section1.subgroupInKernel' ρχ.character Z :=
    (Section1.subgroupInKernel'_character_iff_subgroupInRepresentationKernel
      ρχ Z).mpr hχRepKer
  exact hχnotker (by simpa [hχeq] using hχker)

theorem theorem_6_6_mem_S_of_irreducible_not_subgroupInKernel
    {L : Type u} [Group L] [Finite L]
    {K Z : Subgroup L} [K.Normal]
    {S SZ Xset : Finset (Section1.ClassFunction L)}
    (hZnorm : Z.Normal) (hZcenter : Z ≤ centerIn K) (hZleK : Z ≤ K)
    (hS : inducedKernelFamily K ⊥ S)
    (hSZ : inducedKernelFamily K Z SZ)
    (hXeq : Xset = S \ SZ)
    (hXirr : ∀ χ : Section1.ClassFunction L, χ ∈ Xset →
      Section1.IsIrreducibleCharacterOnGroup χ)
    {χ : Section1.ClassFunction L}
    (hχirr : Section1.IsIrreducibleCharacterOnGroup χ)
    (hχnotker : ¬ Section1.subgroupInKernel' χ Z) :
    χ ∈ S := by
  classical
  obtain ⟨θ, hθirr, hθinner⟩ :=
    theorem_6_6_exists_irreducible_constituent_of_subgroupRestriction K hχirr
  have hθnotker : ¬ Section1.subgroupInKernel' θ (Z.subgroupOf K) :=
    theorem_6_6_constituent_not_subgroupInKernel
      hZnorm hZcenter hZleK hχirr hχnotker hθirr hθinner
  have hθne : θ ≠ Section1.principalCharacter K := by
    intro hθprin
    apply hθnotker
    intro z
    simp [hθprin, Section1.degree]
  have hθbot : Section1.subgroupInKernel' θ ((⊥ : Subgroup L).subgroupOf K) := by
    intro a
    have haL : (((a : (⊥ : Subgroup L).subgroupOf K) : K) : L) = 1 := by
      have hmem : (((a : (⊥ : Subgroup L).subgroupOf K) : K) : L) ∈ (⊥ : Subgroup L) :=
        Subgroup.mem_subgroupOf.mp a.2
      simpa using hmem
    have haK : (a : K) = 1 := Subtype.ext haL
    simp [Section1.degree, haK]
  have hIndS : Section1.inducedCF K θ ∈ S :=
    (hS.2 (Section1.inducedCF K θ)).mpr
      ⟨θ, hθirr, hθbot, hθne, rfl⟩
  have hIndNotker : ¬ Section1.subgroupInKernel' (Section1.inducedCF K θ) Z := by
    intro hIndKer
    apply hθnotker
    rcases hθirr with ⟨n, ρ, _hρirr, hθeq⟩
    have : Z.Normal := hZnorm
    have hρIndKer :
        Section1.subgroupInKernel' (Section1.inducedCF K ρ.character) Z := by
      simpa [hθeq] using hIndKer
    have hρker : Section1.subgroupInKernel' ρ.character (Z.subgroupOf K) :=
      (Section1.proposition_1_6_a K Z hZleK ρ).mpr hρIndKer
    simpa [hθeq] using hρker
  have hIndX : Section1.inducedCF K θ ∈ Xset :=
    theorem_6_6_mem_Xset_of_mem_S_not_subgroupInKernel
      hZnorm hZleK hSZ hXeq hIndS hIndNotker
  have hIndIrr : Section1.IsIrreducibleCharacterOnGroup (Section1.inducedCF K θ) :=
    hXirr (Section1.inducedCF K θ) hIndX
  have hχclass : Section1.IsClassFunction χ :=
    theorem_6_6_isClassFunction_of_irreducibleCharacterOnGroup hχirr
  have hIndInner : Section1.scalarProduct L (Section1.inducedCF K θ) χ ≠ 0 := by
    rw [Section1.scalarProduct_inducedCF_left K θ χ hχclass]
    exact hθinner
  have hEq : Section1.inducedCF K θ = χ := by
    by_contra hne
    exact hIndInner
      (theorem_6_6_scalarProduct_irreducible_ne hIndIrr hχirr hne)
  simpa [hEq] using hIndS

public theorem theorem_6_6
    {L : Type u} [Group L] [Finite L]
    {G : Type u} [Group G] [Finite G]
    (K H1 Z : Subgroup L)
    (S SZ Xset : Finset (Section1.ClassFunction L))
    (T : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G) :
    theorem_6_6_statement K H1 Z S SZ Xset T := by
  classical
  unfold theorem_6_6_statement
  intro h64 _hZne hZcenter hZnorm hSZ hXeq hXirr
  rcases h64 with ⟨h61, hoddL, hbotH1, hbotK, hnil, hcomm, hfrob⟩
  have h64' : hypothesis_6_4_statement K ⊥ H1 S T :=
    ⟨h61, hoddL, hbotH1, hbotK, hnil, hcomm, hfrob⟩
  have : K.Normal := h61.2.1
  have hSbot : inducedKernelFamily K ⊥ S :=
    hypothesis_6_1_inducedKernelFamily_bot h61
  have hZleK : Z ≤ K := theorem_6_6_centerIn_le hZcenter
  have hXclosed : ∀ χ : Section1.ClassFunction L, χ ∈ Xset →
      Section1.conjugateCharacter χ ∈ Xset :=
    theorem_6_6_diff_conjugate_closed hSbot hSZ hXeq
  have hXchar : ∀ χ : Section1.ClassFunction L, χ ∈ Xset ↔
      Section1.IsIrreducibleCharacterOnGroup χ ∧
        ¬ Section1.subgroupInKernel' χ Z := by
    intro χ
    constructor
    · intro hχX
      have hχdiff : χ ∈ S \ SZ := by
        simpa [hXeq] using hχX
      have hχS : χ ∈ S := (Finset.mem_sdiff.mp hχdiff).1
      have hχnotSZ : χ ∉ SZ := (Finset.mem_sdiff.mp hχdiff).2
      exact ⟨hXirr χ hχX,
        theorem_6_6_mem_diff_not_subgroupInKernel
          hZnorm hZleK hSbot hSZ hχS hχnotSZ⟩
    · intro hχ
      have hχS : χ ∈ S := by
        exact theorem_6_6_mem_S_of_irreducible_not_subgroupInKernel
          hZnorm hZcenter hZleK hSbot hSZ hXeq hXirr hχ.1 hχ.2
      exact theorem_6_6_mem_Xset_of_mem_S_not_subgroupInKernel
        hZnorm hZleK hSZ hXeq hχS hχ.2
  have hXnonempty : Xset.Nonempty :=
    theorem_6_6_Xset_nonempty _hZne hXchar
  refine ⟨hXchar, ?_⟩
  exact theorem_6_6_coherent_of_ordered_degree_divisibility
    h64' hSbot hXeq hXclosed hXnonempty (fun {p} hpQ hnotX =>
      theorem_6_6_ordered_degree_divisibility h64' hSbot _hZne hZcenter hZnorm
        hSZ hXeq hXchar hXirr hXclosed hXnonempty hpQ hnotX)

end CFSG.Section6
