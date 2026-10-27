module

public import CFSG.Quasithin.EmptyFaithful.E22PL2Psl
public import CFSG.Quasithin.EmptyFaithful.E22PL2PglA
public import CFSG.Quasithin.EmptyFaithful.E22PL2Pgl
public import CFSG.Quasithin.EmptyFaithful.E22PL2Sev
public import CFSG.Quasithin.EmptyFaithful.E22PL2Sevb
public import CFSG.Quasithin.EmptyFaithful.E22PTr
public import CFSG.Quasithin.Background.E1ElevenIso

public section

namespace CFSG.Quasithin.E22L2

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.E1 CFSG.Quasithin.A1b CFSG.GorensteinWalter

theorem e22pl2_le_of_ne_seven {p : ℕ} [Fact p.Prime] (hp8 : p % 8 = 1 ∨ p % 8 = 7) (hp7 : 7 ≤ p)
    (h7 : p ≠ 7) : 17 ≤ p := by
  by_contra hlt
  have hp : p.Prime := Fact.out
  have h : p = 9 ∨ p = 15 := by omega
  rcases h with rfl | rfl <;> norm_num at hp

theorem nParam_pgl2_prime_le_one {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Finite K]
    (hp8 : p % 8 = 1 ∨ p % 8 = 7) (hp17 : 17 ≤ p) (hK : Nat.card K = p) :
    nParam (⊤ : Subgroup (PGL2 K)) ≤ 1 := by
  have := e22pl2pgl_finite K
  obtain ⟨T, hT⟩ := exists_isSylowIn_two (⊤ : Subgroup (PGL2 K))
  have h := (nParam_le_iff (H := (⊤ : Subgroup (PGL2 K))) (n := 1) one_pos).mpr
    ((inE_iff_inEFor hT).mpr (inEFor_pgl2_prime hp8 hp17 hK hT))
  simpa using h

theorem nParam_psl2_seven_le_one {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 7) : nParam (⊤ : Subgroup (PSL2 K)) ≤ 1 := by
  obtain ⟨T, hT⟩ := exists_isSylowIn_two (⊤ : Subgroup (PSL2 K))
  have h := (nParam_le_iff (H := (⊤ : Subgroup (PSL2 K))) (n := 1) one_pos).mpr
    ((inE_iff_inEFor hT).mpr (inEFor_psl2_seven hK hT))
  simpa using h

theorem nParam_pgl2_seven_le_one {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 7) : nParam (⊤ : Subgroup (PGL2 K)) ≤ 1 := by
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have := e22pl2pgl_finite K
  obtain ⟨T, hT⟩ := exists_isSylowIn_two (⊤ : Subgroup (PGL2 K))
  have hcoat : ∀ {z : PGL2 K}, orderOf z = 2 → z ∈ commutator (PGL2 K) →
      IsCoatom (Subgroup.centralizer ({z} : Set (PGL2 K))) := fun hz hzJ =>
    pgl2_centralizer_inner_involution_isCoatom_seven hK hz hzJ
  have h := (nParam_le_iff (H := (⊤ : Subgroup (PGL2 K))) (n := 1) one_pos).mpr
    ((inE_iff_inEFor hT).mpr
      (inEFor_pgl2_of_coatom (by omega) le_rfl hK hT hcoat))
  simpa using h

theorem nParam_le_one_of_psl2_prime {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (hp8 : p % 8 = 1 ∨ p % 8 = 7) (hp7 : 7 ≤ p) (hF : IsPSL 2 p 1 ↥(CFSG.generalizedFitting G)) :
    nParam (⊤ : Subgroup G) ≤ 1 := by
  have hK : Nat.card (ZMod p) = p := Nat.card_zmod p
  rcases psl2_prime_transport hp7 hF with ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩
  · rw [E1.Eleven.nParam_top_mulEquiv e]
    by_cases h7 : p = 7
    · subst h7
      exact nParam_psl2_seven_le_one hK
    · exact nParam_psl2_prime_le_one hp8 (e22pl2_le_of_ne_seven hp8 hp7 h7) hK
  · have := e22pl2pgl_finite (ZMod p)
    rw [E1.Eleven.nParam_top_mulEquiv e]
    by_cases h7 : p = 7
    · subst h7
      exact nParam_pgl2_seven_le_one hK
    · exact nParam_pgl2_prime_le_one hp8 (e22pl2_le_of_ne_seven hp8 hp7 h7) hK

end CFSG.Quasithin.E22L2
