module

public import CFSG.Quasithin.EmptyFaithful.E22NW
public import CFSG.Quasithin.H13.NQCoreAlt6Lift

public section

namespace CFSG.Quasithin.E2.E22N

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.Vol2.Ch11.SecB

theorem nParam_le_one_of_alt6 {G : Type} [Group G] [Finite G]
    (hA6 : IsAlt 6 (ASInputs.FStar G)) : E1.nParam (⊤ : Subgroup G) ≤ 1 := by
  have h := (E1.nParam_le_iff (H := (⊤ : Subgroup G)) (n := 1) one_pos).mpr ?_
  · simpa using h
  intro T hT
  set Y : Subgroup G := CFSG.generalizedFitting G with hY
  obtain ⟨-, hYn⟩ := CFSG.LocalCores.generalized_fitting_characteristic (G := G)
  obtain ⟨e⟩ := hA6
  have hs6 : IsSimpleGroup (alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
  have hcard : Nat.card ↥Y = 360 := by
    rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, card_alternatingGroup]
    simp [Nat.factorial]
  have hsY : IsSimpleGroup ↥Y := e.isSimpleGroup
  have hnaY : ∃ a b : ↥Y, a * b ≠ b * a := by
    by_contra hcomm
    push Not at hcomm
    have : IsMulCommutative ↥Y := ⟨⟨fun a b => hcomm a b⟩⟩
    have hp := Group.is_simple_iff_prime_card.1 hsY
    rw [hcard] at hp
    norm_num at hp
  have hperf : ⁅Y, Y⁆ = Y := Subgroup.isPerfect_iff.mp
    (CFSG.TwoRankLowerBound.Helpers.perfect_of_nonabelian_simple (↥Y) hnaY)
  have hZ : Subgroup.center ↥Y = ⊥ :=
    CFSG.TwoRankLowerBound.Helpers.center_eq_bot_of_nonabelian_simple (↥Y) hnaY
  have hCG : Subgroup.centralizer (Y : Set G) = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have hxY : x ∈ Y := CFSG.centralizer_generalizedFitting_le G hx
    have hxc : (⟨x, hxY⟩ : ↥Y) ∈ Subgroup.center ↥Y := by
      rw [Subgroup.mem_center_iff]
      intro y
      exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hx y y.2)
    rw [hZ, Subgroup.mem_bot] at hxc
    rw [Subgroup.mem_bot]
    exact congrArg Subtype.val hxc
  have hO2G : CFSG.Open.pCore 2 G = ⊥ := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    set P := CFSG.Open.pCore 2 G with hP
    have hPY : P ≤ Y := by
      have h1 := CFSG.pCore_le_fitting G 2
      exact h1.trans le_sup_left
    have hPn : P.Normal := CFSG.LieType.BorelTits.pCore_normal 2
    have hPsn : (P.subgroupOf Y).Normal := hPn.subgroupOf Y
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (P.subgroupOf Y) with h | h
    · rw [← Subgroup.map_subgroupOf_eq_of_le hPY, h, Subgroup.map_bot]
    · exfalso
      have hYP : Y ≤ P := Subgroup.subgroupOf_eq_top.mp h
      have hP2 : IsPGroup 2 ↥P := CFSG.LieType.BorelTits.pCore_isPGroup 2
      have h2 : IsPGroup 2 ↥Y :=
        hP2.of_injective (Subgroup.inclusion hYP) (Subgroup.inclusion_injective hYP)
      obtain ⟨k, hk⟩ := h2.exists_card_eq
      rw [hcard] at hk
      have h3 : 3 ∣ 2 ^ k := hk ▸ (by norm_num : 3 ∣ 360)
      exact absurd (Nat.prime_three.dvd_of_dvd_pow h3) (by norm_num)
  have hinj : Function.Injective (QuotientGroup.mk' (⊥ : Subgroup G)) :=
    (MonoidHom.ker_eq_bot_iff _).mp (QuotientGroup.ker_mk' (⊥ : Subgroup G))
  set π := QuotientGroup.mk' (⊥ : Subgroup G) with hπ
  have : Y.Normal := hYn
  refine H13.NQCore.inEFor_one_of_alt6_quotient (J := ⊥) (Y := Y) hT ?_ ?_ hperf ?_ ?_ ?_
  · exact bot_le
  · intro c hc y _
    rw [Subgroup.mem_inf, Subgroup.mem_bot] at hc
    rw [hc.2]
    simp only [commutatorElement_def, one_mul, inv_one, mul_one, mul_inv_cancel]
    exact Subgroup.one_mem _
  · exact ⟨(Subgroup.equivMapOfInjective Y π hinj).symm.trans e⟩
  · rw [eq_bot_iff]
    intro x hx
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective (⊥ : Subgroup G) x
    have hg : g ∈ Subgroup.centralizer (Y : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      have := Subgroup.mem_centralizer_iff.mp hx (π y) ⟨y, hy, rfl⟩
      exact hinj (by rw [map_mul, map_mul]; exact this)
    rw [hCG, Subgroup.mem_bot] at hg
    rw [hg, Subgroup.mem_bot, map_one]
  · rw [E1.pCoreOf_top_eq]
    have := CFSG.LieType.BorelTits.map_pCore_mulEquiv 2 (QuotientGroup.quotientBot (G := G)).symm
    rw [hO2G, Subgroup.map_bot] at this
    exact this.symm

@[expose] def TypeOneNoA6 (Y : Type) [Group Y] : Prop :=
  IsPSL 3 2 1 Y ∨ (∃ p e : ℕ, p.Prime ∧ p ≠ 2 ∧ 5 < p ^ e ∧ IsPSL 2 p e Y) ∨
    ∃ (s : Bool) (p : ℕ), p.Prime ∧ p ≠ 2 ∧ IsPSLEps3 s p 1 Y

@[expose] def E114OneNoA6 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T : Subgroup G), SQTKGroup G →
    IsSimpleGroup (ASInputs.FStar G) → quasithinIsSylowTwo T →
    CFSG.generalizedFitting G ⊔ T = ⊤ →
      TypeOneNoA6 (ASInputs.FStar G) → E1.nParam (⊤ : Subgroup G) ≤ 1

theorem e114One_of_noA6 (h : E114OneNoA6) : E114One := by
  intro G _ _ T hSQ hFs hT hFT hty
  rcases hty with h1 | h6 | h2 | h3
  · exact h G T hSQ hFs hT hFT (Or.inl h1)
  · exact nParam_le_one_of_alt6 h6
  · exact h G T hSQ hFs hT hFT (Or.inr (Or.inl h2))
  · exact h G T hSQ hFs hT hFT (Or.inr (Or.inr h3))

end CFSG.Quasithin.E2.E22N
