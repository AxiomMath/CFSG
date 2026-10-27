module

public import CFSG.Sporadic.HNOddCore.FourPair
public import CFSG.LocalAnalysis.ComponentClassification.OutcomeLocalCTIBasic
public import CFSG.GroupTheory.SubnormalJoin
public import Certificates.Certificate2083
public import Certificates.Certificate2084
public import Certificates.Certificate2087
public import Certificates.Certificate2089
public import Certificates.Certificate2091
public import Certificates.Certificate2094
public import Certificates.Certificate2096
public import Certificates.Certificate2099
public import Certificates.Certificate2100
public import Certificates.Certificate2102
public import Certificates.Certificate2104
public import Certificates.Certificate2107

public noncomputable section

namespace CFSG.Sporadic.HNOddCore

open CFSG.Sporadic.HNSchreier CFSG.Sporadic.HNSchreier.Native CFSG.LocalCores

theorem jR_range_normal :
    jR.range.Normal := by
  refine ⟨fun n hn x => ?_⟩
  obtain ⟨h, rfl⟩ := hn
  rcases exists_jR_or x with ⟨g, rfl⟩ | ⟨g, rfl⟩
  · exact ⟨g * h * g⁻¹, by rw [map_mul, map_mul, map_inv]⟩
  · refine ⟨g * conjC h * g⁻¹, ?_⟩
    rw [map_mul, map_mul, map_inv, ← cR_conj_jR, mul_inv_rev]
    simp only [mul_assoc]

abbrev C4J :
    Subgroup C4 := jR.range.subgroupOf C4

theorem C4J_normal :
    C4J.Normal := by
  have := jR_range_normal
  infer_instance

theorem jR_comm_t4_iff
    (g : JH) : jR g ∈ C4 ↔ g ∈ Subgroup.centralizer {t4J} := by
  constructor
  · intro h
    rcases (mem_centralizer_t4_iff _).1 h with ⟨g', hg', e⟩ | ⟨g', -, e⟩
    · rwa [jR_injective e]
    · exfalso
      apply cR_ne_jR (g'⁻¹ * g)
      rw [map_mul, e, map_inv, inv_mul_cancel_left]
  · exact jR_mem_C4

@[expose] def cjHom :
    Subgroup.centralizer {t4J} →* C4J :=
  ((jR.comp (Subgroup.centralizer {t4J}).subtype).codRestrict C4
    fun g => jR_mem_C4 g.2).codRestrict C4J fun g => ⟨g, rfl⟩

theorem cjHom_bijective :
    Function.Bijective cjHom := by
  constructor
  · intro a b h
    have := congrArg (fun y : C4J => ((y : C4) : RH)) h
    exact Subtype.ext (jR_injective this)
  · rintro ⟨⟨r, hr⟩, ⟨g, hg⟩⟩
    have hg' : jR g ∈ C4 := by
      have e : jR g = r := hg
      rw [e]
      exact hr
    refine ⟨⟨g, (jR_comm_t4_iff g).1 hg'⟩, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    exact hg

theorem not_isComponent_of_mulEquiv_normal {G M : Type*} [Group G] [Group M] {N : Subgroup M}
    (hN : N.Normal) (e : G ≃* N) (hM : ∀ K : Subgroup M, ¬ CFSG.IsComponent K)
    (K : Subgroup G) : ¬ CFSG.IsComponent K := by
  intro hK
  have h2 := isComponent_map_mulEquiv e hK
  apply hM ((K.map e.toMonoidHom).map N.subtype)
  exact ⟨isQuasisimple_of_mulEquiv (Subgroup.equivMapOfInjective _ _ N.subtype_injective) h2.1,
    CFSG.GroupTheory.isSubnormal_map_subtype h2.2 hN.isSubnormal⟩

theorem cti_hn_four_pair_centralizer_has_no_components :
    (∀ K : Subgroup (Subgroup.centralizer {jR t4J} : Subgroup RH), ¬ CFSG.IsComponent K) ∧
    ∀ K : Subgroup (Subgroup.centralizer {t4J} : Subgroup JH), ¬ CFSG.IsComponent K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h1 : ∀ K : Subgroup C4, ¬ CFSG.IsComponent K := fun K =>
    CFSG.ComponentClassification.OutcomeLocal.not_isComponent_of_selfCentralizing Q4_normal
      Q4_isPGroup centralizer_Q4_le K
  exact ⟨h1, @not_isComponent_of_mulEquiv_normal _ _ (Subgroup.toGroup _) (Subgroup.toGroup _) C4J
    C4J_normal (MulEquiv.ofBijective cjHom cjHom_bijective) h1⟩

end CFSG.Sporadic.HNOddCore
