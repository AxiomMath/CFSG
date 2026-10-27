module

public import CFSG.Quasithin.Vol2.Ch11SecSCartanL2
public import CFSG.Quasithin.Vol2.Ch11SecSCartanT5
public import CFSG.Quasithin.Vol2.Ch11SecQ9aCartF
public import CFSG.Quasithin.Vol2.Ch11SecQ9aS4G
public import CFSG.Quasithin.Vol2.Ch11G2Q8CartanW
public import CFSG.Quasithin.Vol2.Ch11SecA11Setup
public import CFSG.Quasithin.Vol2.Ch11SecDSetup

public section

namespace CFSG.Quasithin.Vol2.Ch11.O10

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.Quasithin.H13
open scoped IsMulCommutative

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem mem_normalizer_sup' {A B : Subgroup G} {x : G} (hA : x ∈ Subgroup.normalizer (A : Set G))
    (hB : x ∈ Subgroup.normalizer (B : Set G)) :
    x ∈ Subgroup.normalizer ((A ⊔ B : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq] at hA hB ⊢
  rw [Subgroup.map_sup, hA, hB]

omit [Finite G] in
theorem T_le_normalizer_TL {T L : Subgroup G} (hTL : T ≤ Subgroup.normalizer (L : Set G)) :
    T ≤ Subgroup.normalizer (TL T L : Set G) := fun _ ht =>
  SecD.mem_normalizer_inf (Subgroup.le_normalizer ht)
    (mem_normalizer_sup' (hTL ht)
      ((le_sup_right.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (L ⊔ T))) ht))

theorem rOf_eq_pCoreOf_sup {T L I : Subgroup G} {n : ℕ} (h : Hyp11 G T L I n) {U : Subgroup G}
    (hTU : T ≤ Subgroup.normalizer (U : Set G)) (hR : ROf T L U ≤ TL T L) :
    ROf T L U = pCoreOf 2 (LOf L U ⊔ TL T L) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hle : LOf L U ⊔ TL T L ≤ LOf L U ⊔ T := sup_le_sup_left inf_le_left _
  have hTN : T ≤ Subgroup.normalizer ((LOf L U ⊔ TL T L : Subgroup G) : Set G) := fun t ht =>
    mem_normalizer_sup' (SecA.T_le_normalizer_lOf h.normal hTU ht) (T_le_normalizer_TL h.normal ht)
  refine le_antisymm ?_ ?_
  · exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 (hR.trans le_sup_right)
      (hle.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _))
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _)
  · exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
      ((CFSG.LieType.BorelTits.pCoreOf_le 2 _).trans hle)
      (sup_le (le_sup_left.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _))
        (hTN.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 _)))
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _)

theorem cartan_le_normalizer_rOf_of_le (hN : SecA.NatFacts) (h1102 : Stmt11_0_2)
    {T L I : Subgroup G} {n : ℕ} (h : Hyp11 G T L I n) {i : ℕ} (hi : i = 1 ∨ i = 2)
    {U X : Subgroup G} (hU : IsVi T L I n i U) (hX : IsCartanX T L X)
    (hR : ROf T L U ≤ TL T L) : X ≤ Subgroup.normalizer (ROf T L U : Set G) := by
  rw [rOf_eq_pCoreOf_sup h (SecA.IsVi.le_normalizer hU) hR]
  intro x hx
  exact CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 _
    (mem_normalizer_sup' (SecS.cartan_le_normalizer_lOf hN h1102 h hi hU hX hx) (hX.1 hx).2)

theorem card_xOne_two (hN : SecA.NatFacts) (h1102 : Stmt11_0_2) {T L I : Subgroup G} {n : ℕ}
    (h : Hyp11 G T L I n) {V₁ V₂ X : Subgroup G} (hV₁ : IsVi T L I n 1 V₁)
    (hV₂ : IsVi T L I n 2 V₂) (hX : IsCartanX T L X) :
    Nat.card ↥(SecA.xOne X (LOf L V₂)) = 2 ^ n - 1 := by
  have d := SecS.transportData hN h1102 h hV₁ hV₂ hX
  have hsq : ∀ w : ↥(fsuV T I), w ^ 2 = 1 := fun w =>
    Subtype.ext (by simpa using (SecA.isElemAbelian_fsuV h).2 w w.2)
  have hP := SecA.isSylowTwoOf_P h
  have hU₁ := SecA.isFlagW_of_isVi h hV₁
  have hU₂ := SecA.isFlagW_of_isVi h hV₂
  have hD := SecS.isHall_autOn_cartan h1102 h hX
  have hn : 2 ≤ n := h.one_lt
  rw [← d.card (inf_le_left : SecA.xOne X (LOf L V₂) ≤ X), d.f₂]
  obtain ⟨_, -, -, -, hk⟩ := h1102 G T L I n h
  rcases hk with ⟨K, _, _, hK, -, π, hπ, -⟩ | ⟨K, _, _, hK, -, π, hπ, -⟩ | ⟨K, _, _, hK, -, hnat⟩
  · exact (SecS.factCartanSL3_holds K n hn hK _ hsq _ _ π hπ _ hP _ _ hU₁ hU₂ _ hD).2.2.2.2.2.2
  · exact (SecS.factCartanSp4_holds K n hn hK _ hsq _ _ π hπ _ hP _ _ hU₁ hU₂ _ hD).1.2.2.2.2.2.2
  · obtain ⟨K', _, _, hK', π, hπ⟩ := hnat
    exact (G2Q8.factCartanG2_holds K' n hn hK' _ hsq _ _ π hπ _ hP _ _ hU₁ hU₂ _ hD).1.2.2.2.2.2.2

theorem exists_mem_xOne_two (hN : SecA.NatFacts) (h1102 : Stmt11_0_2) {T L I : Subgroup G}
    {n : ℕ} (h : Hyp11 G T L I n) {V₁ V₂ X : Subgroup G} (hV₁ : IsVi T L I n 1 V₁)
    (hV₂ : IsVi T L I n 2 V₂) (hX : IsCartanX T L X) :
    ∃ c ∈ SecA.xOne X (LOf L V₂), (orderOf c).Prime ∧ orderOf c ∣ 2 ^ n - 1 := by
  have hcard := card_xOne_two hN h1102 h hV₁ hV₂ hX
  have hn : 2 ≤ n := h.one_lt
  have h4 : 4 ≤ 2 ^ n :=
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have hpp : (2 ^ n - 1).minFac.Prime := Nat.minFac_prime (by omega)
  have : Fact (2 ^ n - 1).minFac.Prime := ⟨hpp⟩
  have hpd : (2 ^ n - 1).minFac ∣ Nat.card ↥(SecA.xOne X (LOf L V₂)) := by
    rw [hcard]
    exact Nat.minFac_dvd _
  obtain ⟨c, hc⟩ := exists_prime_orderOf_dvd_card' _ hpd
  refine ⟨c, c.2, ?_, ?_⟩
  · rw [Subgroup.orderOf_coe, hc]
    exact hpp
  · rw [Subgroup.orderOf_coe, hc]
    exact Nat.minFac_dvd _

end CFSG.Quasithin.Vol2.Ch11.O10
