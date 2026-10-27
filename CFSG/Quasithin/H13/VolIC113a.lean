module

public import CFSG.Quasithin.H13.VolIC113
public import CFSG.LocalAnalysis.QuasithinUnique.EscapingLocalAux

public section

namespace CFSG.Quasithin.H13.VolI

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

section General

variable {G : Type} [Group G]

theorem pow_two_mem_centralizer_of_commutator_mem {L : Subgroup G} {q : G}
    (hcomm : ∀ l ∈ L, q * (q * l * q⁻¹ * l⁻¹) = (q * l * q⁻¹ * l⁻¹) * q)
    (hsq : ∀ l ∈ L, (q * l * q⁻¹ * l⁻¹) ^ 2 = 1) :
    q ^ 2 ∈ Subgroup.centralizer (L : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  intro l hl
  set w := q * l * q⁻¹ * l⁻¹ with hwdef
  have hwq : q * w = w * q := hcomm l hl
  have hw2 : w * w = 1 := by
    have := hsq l hl
    rwa [pow_two] at this
  have hwl : q * l * q⁻¹ = w * l := by rw [hwdef]; group
  have key : q ^ 2 * l = l * q ^ 2 := by
    calc q ^ 2 * l = q * (q * l * q⁻¹) * q := by rw [pow_two]; group
      _ = q * (w * l) * q := by rw [hwl]
      _ = (q * w) * l * q := by group
      _ = (w * q) * l * q := by rw [hwq]
      _ = w * (q * l * q⁻¹) * q * q := by group
      _ = w * (w * l) * q * q := by rw [hwl]
      _ = (w * w) * l * q * q := by group
      _ = l * q ^ 2 := by rw [hw2, pow_two]; group
  exact key.symm

theorem frattini_le_of_sq_mem_of_isPGroup [Finite G] {R K : Subgroup G} (hR : IsPGroup 2 R)
    (hsq : ∀ x ∈ R, x ^ 2 ∈ K) : (frattini R).map R.subtype ≤ K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (IsPGroup 2 R) := ⟨hR⟩
  rw [Subgroup.map_le_iff_le_comap, CFSG.frattini_eq_closure_commutator_union_powers (p := 2),
    Subgroup.closure_le]
  have hcomm : _root_.commutator R ≤ K.comap R.subtype := by
    rw [_root_.commutator_def, Subgroup.commutator_le]
    intro x _ y _
    rw [Subgroup.mem_comap, commutatorElement_def]
    simp only [Subgroup.coe_subtype, Subgroup.coe_mul, Subgroup.coe_inv]
    have e : (x : G) * y * (x : G)⁻¹ * (y : G)⁻¹ =
        ((x : G) * x) * (((x : G)⁻¹ * y) * ((x : G)⁻¹ * y)) * ((y : G)⁻¹ * (y : G)⁻¹) := by
      group
    rw [e, ← sq, ← sq, ← sq]
    exact K.mul_mem (K.mul_mem (hsq _ x.2) (hsq _ (R.mul_mem (R.inv_mem x.2) y.2)))
      (hsq _ (R.inv_mem y.2))
  rintro x (hx | ⟨y, rfl⟩)
  · exact hcomm hx
  · rw [SetLike.mem_coe, Subgroup.mem_comap]
    simpa using hsq _ y.2

end General

variable {G : Type} [Group G] [Finite G] {L T : Subgroup G}

theorem sq_mem_inf_centralizer (hT : IsSylowTwoOf T (L ⊔ T))
    (hTN : T ≤ Subgroup.normalizer (L : Set G)) (hL : IsShort2 L) {q : G}
    (hq : q ∈ pCoreOf 2 (L ⊔ T)) : q ^ 2 ∈ T ⊓ Subgroup.centralizer (L : Set G) := by
  have hqT : q ∈ T := EscapingLocal.pCoreOf_le_of_isSylowTwoOf hT hq
  refine ⟨T.pow_mem hqT 2, pow_two_mem_centralizer_of_commutator_mem (fun l hl => ?_)
    (fun l hl => C1.blockU_sq hL _ (commutator_mem_blockU hL hTN hq hl))⟩
  exact pCoreOf_comm_blockU hL hT hTN hq (commutator_mem_blockU hL hTN hq hl)

theorem frattini_pCoreOf_le (hT : IsSylowTwoOf T (L ⊔ T))
    (hTN : T ≤ Subgroup.normalizer (L : Set G)) (hL : IsShort2 L) :
    (frattini ↥(pCoreOf 2 (L ⊔ T))).map (pCoreOf 2 (L ⊔ T)).subtype ≤
      T ⊓ Subgroup.centralizer (L : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact frattini_le_of_sq_mem_of_isPGroup
    (CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 _)
    fun q hq => sq_mem_inf_centralizer hT hTN hL hq

end CFSG.Quasithin.H13.VolI
