module

public import CFSG.Quasithin.Background.A1cTransfer
public import CFSG.Quasithin.Vol2.GoldschmidtF431U42Equiv
public import CFSG.Quasithin.Background.A4Defs

public section

namespace CFSG.Quasithin.H13.F431.U42Aut

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Open

variable {G : Type*} [Group G] [Finite G]

theorem pResidual_two_eq_top (hG : IsSimpleGroup G) (hnab : ∃ a b : G, a * b ≠ b * a) :
    pResidual 2 G = ⊤ := by
  have := hG
  refine eq_top_iff.2 ?_
  unfold pResidual
  refine le_iInf fun N => le_iInf fun hN => le_iInf fun h => ?_
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal N with h0 | h1
  · exfalso
    have hp : IsPGroup 2 G := fun x => by
      obtain ⟨k, hk⟩ := h x
      rw [h0] at hk
      exact ⟨k, Subgroup.mem_bot.1 hk⟩
    obtain ⟨a, b, hab⟩ := hnab
    have : Nontrivial G := ⟨⟨a, b, fun h => hab (by rw [h])⟩⟩
    have hc := hp.center_nontrivial
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center G) with h3 | h3
    · exact (Subgroup.nontrivial_iff_ne_bot _).1 hc h3
    · have : b ∈ Subgroup.center G := h3 ▸ Subgroup.mem_top b
      exact hab (Subgroup.mem_center_iff.1 this a)
  · rw [h1]

theorem exists_conj_mem_of_thompson_of_res (hres : pResidual 2 G = ⊤)
    {T S : Subgroup G} (hT : IsSylowTwoOf T ⊤) (hST : S ≤ T) (hidx : S.relIndex T = 2) {u : G}
    (hu : orderOf u = 2) : ∃ x : G, x⁻¹ * u * x ∈ S := by
  by_contra hcon
  push Not at hcon
  have hidx' : ¬ 2 ∣ T.index := by
    have e : (T.subgroupOf ⊤).index = T.index := Subgroup.relIndex_top_right T
    have := hT.2.2
    rwa [e] at this
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let P : Sylow 2 G := hT.2.1.toSylow hidx'
  have h := thompson_transfer_lemma P (Q := S) hST hidx hu hcon
  rw [hres] at h
  exact h (Subgroup.mem_top u)

theorem pCoreOf_le_of_isSylowTwoOf {B T : Subgroup G} (hT : IsSylowTwoOf T B) :
    pCoreOf 2 B ≤ T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro g hg
  obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.1 hg
  have hnormal : (pCore 2 ↥B).Normal := CFSG.LieType.BorelTits.pCore_normal 2
  have hp : IsPGroup 2 (pCore 2 ↥B) := CFSG.LieType.BorelTits.pCore_isPGroup 2
  have hle := hp.le_sylow_of_normal (A4.toSylow hT)
  exact Subgroup.mem_subgroupOf.1 (hle hx)

omit [Finite G] in
theorem twoPart_centralizer_conj (f h : G) :
    twoPart (Subgroup.centralizer ({h * f * h⁻¹} : Set G)) =
      twoPart (Subgroup.centralizer ({f} : Set G)) := by
  have e := U42.centralizer_map (MulAut.conj h) f
  have h1 : Nat.card ↥(Subgroup.centralizer ({h * f * h⁻¹} : Set G)) =
      Nat.card ↥(Subgroup.centralizer ({f} : Set G)) := by
    rw [show h * f * h⁻¹ = (MulAut.conj h) f from rfl, e]
    exact Subgroup.card_map_of_injective (MulAut.conj h).injective
  unfold twoPart
  rw [h1]

end CFSG.Quasithin.H13.F431.U42Aut
