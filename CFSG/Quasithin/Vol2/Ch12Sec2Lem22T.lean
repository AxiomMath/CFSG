module

public import CFSG.Quasithin.Vol2.Ch12Sec2Lem22O

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique
open scoped IsMulCommutative

namespace Lem22

variable {G : Type} [Group G] [Finite G]

namespace Extra3

variable {T L V H P U I : Subgroup G} {h : G}

theorem QL_facts (h1222 : Stmt12_2_2) (e : Extra3 T L V H P U I h) :
    pCoreOf 2 L ≤ T ∧ V ≤ pCoreOf 2 L ∧ L ≤ Subgroup.normalizer (pCoreOf 2 L : Set G) ∧
      T ≤ Subgroup.normalizer (pCoreOf 2 L : Set G) ∧
      (frattini ↥P).map P.subtype ≤ Subgroup.normalizer (pCoreOf 2 L : Set G) := by
  obtain ⟨-, -, -, -, -, -, -, -, hPΦ, -⟩ := e.pre
  obtain ⟨-, -, hall⟩ := ((h1222 G T e.hyp.simple e.hyp.nonabelian e.hyp.qtke
    e.hyp.sylow).resolve_left e.hyp.notAlt) L e.hyp.maximal e.hyp.faithful e.hyp.quasisimple
  obtain ⟨⟨hVT, -, hred, -⟩, -, -, -, -⟩ := hall V e.hyp.irrPlus
  have hV2' := sq_eq_one_of_hyp1223 e.hyp hred
  have hV2 : ∀ x ∈ V, x ^ 2 = 1 := fun x hx => by simpa using congrArg Subtype.val (hV2' ⟨x, hx⟩)
  have hLN := CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 L
  have hNN := CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 L
  have hTN : T ≤ Subgroup.normalizer (pCoreOf 2 L : Set G) := e.hyp.normalizes.trans hNN
  have hTLT : IsSylowTwoOf T (L ⊔ T) :=
    isSylowTwoOf_of_quasithinIsSylowTwo e.hyp.sylow le_sup_right
  have h1 : pCoreOf 2 L ≤ pCoreOf 2 (L ⊔ T) :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
      ((CFSG.LieType.BorelTits.pCoreOf_le 2 L).trans le_sup_left) (sup_le hLN hTN)
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L)
  have hΦM : (frattini ↥P).map P.subtype ≤ Subgroup.normalizer (L : Set G) := by
    rw [← hPΦ]
    exact inf_le_right
  exact ⟨h1.trans (pCoreOf_two_le_of_isSylowTwoOf hTLT), le_pCoreOf_L e.hyp hVT hV2, hLN, hTN,
    hΦM.trans hNN⟩

theorem zpowers_eq (e : Extra3 T L V H P U I h) {g : G} (hg : g ∈ (frattini ↥P).map P.subtype)
    (hg1 : g ≠ 1) : Subgroup.zpowers g = (frattini ↥P).map P.subtype := by
  refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hg) ?_
  rw [e.cardΦ, Nat.card_zpowers]
  have h3 : orderOf g ∣ 3 := orderOf_dvd_of_pow_eq_one (e.exp g (frattini_map_le P hg))
  rcases (Nat.dvd_prime Nat.prime_three).mp h3 with h4 | h4
  · exact absurd (orderOf_eq_one_iff.mp h4) hg1
  · rw [h4]

theorem eq_one_of_comm_inf (e : Extra3 T L V H P U I h) {g : G}
    (hg : g ∈ (frattini ↥P).map P.subtype)
    (hgc : ∀ u ∈ V ⊓ pCoreOf 2 H, g * u = u * g) : g = 1 := by
  by_contra hg1
  have hzp := e.zpowers_eq hg hg1
  obtain ⟨-, -, hV₀C⟩ := e.eq_inf
  have hV₀1 : V ⊓ pCoreOf 2 H ≠ ⊥ := fun h0 => by
    have h1 := e.card_inf
    rw [h0, Subgroup.card_bot] at h1
    exact absurd h1 (by norm_num)
  obtain ⟨⟨u, hu⟩, hu1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hV₀1
  have hu1' : u ≠ 1 := fun h0 => hu1 (Subtype.ext h0)
  have huC : u ∈ (V ⊓ pCoreOf 2 H) ⊓
      Subgroup.centralizer (((frattini ↥P).map P.subtype : Subgroup G) : Set G) := by
    refine ⟨hu, Subgroup.mem_centralizer_iff.mpr fun f hf => ?_⟩
    rw [← hzp] at hf
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hf
    exact (Commute.zpow_left (hgc u hu) k)
  rw [hV₀C, Subgroup.mem_bot] at huC
  exact hu1' huC

end Extra3

end Lem22

end CFSG.Quasithin.H13
