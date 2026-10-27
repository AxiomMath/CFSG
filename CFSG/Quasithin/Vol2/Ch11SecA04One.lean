module

public import CFSG.Quasithin.Vol2.Ch11SecA04Star
public import CFSG.Quasithin.Background.A3Structure319
public import CFSG.Quasithin.Vol2.Ch11SecA04Glue
public import CFSG.Quasithin.Vol2.Ch11SecAFacts04
public import CFSG.Quasithin.Vol2.Ch1Inputs

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecA

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13
open CFSG.Assembly.LowTwoRank (StatedSL StatedSp)

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G} {n : ℕ}

theorem starData (hF : Facts04) (h1102 : Stmt11_0_2) (h : Hyp11 G T L I n)
    (hk : KindSp4 L (fsuV T I) n ∨ KindG2 L (fsuV T I) n) :
    ∃ (S : Type) (_ : Group S) (_ : Finite S), Nonempty (↥L ⧸ CFSG.pCore 2 ↥L ≃* S) ∧
      Subgroup.center S = ⊥ ∧ 2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup S) ∧
      ∀ (X : Type) [Group X] (s : Bool) (r e : ℕ), IsPSLEps3 s r e X →
        ∀ f : X →* S, ¬ Function.Surjective f := by
  obtain ⟨_, -, -, ⟨e⟩, -⟩ := h1102 G T L I n h
  have hn : 2 ≤ n := h.one_lt
  have h3 : 3 ∣ 2 ^ (2 * n) - 1 := A319.three_dvd_two_pow_sub_one ⟨n, by ring⟩
  rcases hk with ⟨K, _, _, hK, ⟨e'⟩⟩ | ⟨K, _, _, hK, ⟨e'⟩⟩
  · obtain ⟨hZ, -, hS⟩ := hF.excl.1 K n hn hK
    exact ⟨↥(StatedSp 2 K), inferInstance, inferInstance, ⟨e.trans e'⟩, hZ,
      ((hF.torus K n hn hK 3 Nat.prime_three).2 h3).1, fun X _ s r e hX => (hS X s r e hX).1⟩
  · obtain ⟨-, hZ, hS⟩ := hF.excl.1 K n hn hK
    exact ⟨↥⁅quasithinG2 K, quasithinG2 K⁆, inferInstance, inferInstance, ⟨e.trans e'⟩, hZ,
      ((hF.torus K n hn hK 3 Nat.prime_three).2 h3).2, fun X _ s r e hX => (hS X s r e hX).2⟩

theorem not_case2_case3 (hF : Facts04) (h1102 : Stmt11_0_2) (h : Hyp11 G T L I n)
    (hk : KindSp4 L (fsuV T I) n ∨ KindG2 L (fsuV T I) n) {H : Subgroup G} (hLH : L ≤ H) :
    ¬ A318Case2 (starImage 3 (L.subgroupOf H)) ∧
      ¬ A318Case3Group ↥(starImage 3 (L.subgroupOf H)) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨S, _, _, ⟨eS⟩, hZ, hr, hS⟩ := starData hF h1102 h hk
  obtain ⟨e₀⟩ := quotPCore_subgroupOf_equiv (L := L) hLH
  set e := e₀.trans eS
  have hQ := isQuasisimple_subgroupOf h hLH
  have hZ' : Subgroup.center (↥(L.subgroupOf H) ⧸ CFSG.pCore 2 ↥(L.subgroupOf H)) = ⊥ := by
    have h1 := Subgroup.map_center_eq e
    rw [hZ] at h1
    exact (Subgroup.map_eq_bot_iff_of_injective _ e.injective).mp h1
  have h3 : 3 ∣ Nat.card (↥(L.subgroupOf H) ⧸ CFSG.pCore 2 ↥(L.subgroupOf H)) := by
    obtain ⟨E, -, -, hE⟩ := CFSG.SectionRank.exists_pRank (p := 3) (by norm_num)
      (⊤ : Subgroup S)
    rw [Nat.card_congr e.toEquiv]
    refine dvd_trans ?_ (Subgroup.card_subgroup_dvd_card E)
    rw [hE]
    exact dvd_pow_self 3 (by omega)
  obtain ⟨ψ, hψ, hψk⟩ := exists_starHom hQ hZ' h3
  set ψ' := e.toMonoidHom.comp ψ with hψ'
  have hψ's : Function.Surjective ψ' := e.surjective.comp hψ
  refine ⟨fun h2 => ?_, fun h3' => ?_⟩
  · obtain ⟨s, q, -, ⟨r, k, -, -, -, hPSL⟩, -⟩ := h2
    exact hS _ s r k hPSL ψ' hψ's
  · have hc := hF.excl.2 _ h3'
    obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := ↥(Subgroup.center
      ↥(starImage 3 (L.subgroupOf H)))) 3 (by rw [hc])
    have hzc : ψ' (z : ↥(starImage 3 (L.subgroupOf H))) ∈ Subgroup.center S :=
      Subgroup.map_center_le_center hψ's ⟨_, z.2, rfl⟩
    rw [hZ, Subgroup.mem_bot] at hzc
    have h1 : ψ z = 1 := by
      have := congrArg e.symm hzc
      rwa [hψ', MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply,
        map_one] at this
    obtain ⟨k, hk⟩ := hψk _ h1
    have h2 : orderOf (z : ↥(starImage 3 (L.subgroupOf H))) ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk
    rw [Subgroup.orderOf_coe, hz] at h2
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).mp
      (Nat.prime_three.dvd_of_dvd_pow h2)
    omega

theorem one_lt_pRank_subgroupOf (hF : Facts04) (h1102 : Stmt11_0_2) (h : Hyp11 G T L I n)
    {H : Subgroup G} (hLH : L ≤ H) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hcond : (KindSp4 L (fsuV T I) n ∨ KindG2 L (fsuV T I) n) ∧ p ∣ 2 ^ (2 * n) - 1 ∨
      KindSL3 L (fsuV T I) n ∧ p ∣ 2 ^ n - 1 ∧ 3 < p) :
    1 < CFSG.Open.pRank p (L.subgroupOf H) := by
  rw [pRank_subgroupOf_eq hLH hp hp2]
  obtain ⟨_, -, -, ⟨e⟩, -⟩ := h1102 G T L I n h
  have hn : 2 ≤ n := h.one_lt
  have key : ∀ (S : Type) [Group S] [Finite S], (↥L ⧸ CFSG.pCore 2 ↥L ≃* S) →
      2 ≤ CFSG.Open.pRank p (⊤ : Subgroup S) →
        1 < CFSG.Open.pRank p (⊤ : Subgroup (↥L ⧸ CFSG.pCore 2 ↥L)) := by
    intro S _ _ e' h2
    rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv hp.one_lt e']
    omega
  rcases hcond with ⟨⟨K, _, _, hK, ⟨e'⟩⟩ | ⟨K, _, _, hK, ⟨e'⟩⟩, hpd⟩ |
    ⟨⟨K, _, _, hK, ⟨e'⟩⟩, hpd, -⟩
  · exact key _ (e.trans e') ((hF.torus K n hn hK p hp).2 hpd).1
  · exact key _ (e.trans e') ((hF.torus K n hn hK p hp).2 hpd).2
  · exact key _ (e.trans e') ((hF.torus K n hn hK p hp).1 hpd)

theorem oPrimeResidualOf_eq_of_le (hF : Facts04) (h318 : A318Facts) (h36 : A36ForSQTK)
    (h38 : A38ForSQTK) (h331 : Stmt3_3_1) (h1102 : Stmt11_0_2) (h : Hyp11 G T L I n)
    {H : Subgroup G} (hLT : L ⊔ T ≤ H) (hHL : H ≤ Subgroup.normalizer (L : Set G)) {p : ℕ}
    (hp : p.Prime)
    (hcond : (KindSp4 L (fsuV T I) n ∨ KindG2 L (fsuV T I) n) ∧ p ∣ 2 ^ (2 * n) - 1 ∨
      KindSL3 L (fsuV T I) n ∧ p ∣ 2 ^ n - 1 ∧ 3 < p) :
    oPrimeResidualOf p H = L := by
  have hLH : L ≤ H := le_sup_left.trans hLT
  have hp2 : p ≠ 2 := by
    rintro rfl
    have hodd : ∀ m : ℕ, 1 ≤ m → ¬ 2 ∣ 2 ^ m - 1 := fun m hm hd =>
      (Nat.not_even_iff_odd.mpr (odd_two_pow_sub_one hm)) (even_iff_two_dvd.mpr hd)
    have hn : 2 ≤ n := h.one_lt
    rcases hcond with ⟨-, hd⟩ | ⟨-, hd, -⟩
    · exact hodd (2 * n) (by omega) hd
    · exact hodd n (by omega) hd
  have hS := sqtkGroup_of_le_normalizer h331 h hHL
  have hSQ := SQTKHyp.of_sqtkGroup ↥H hS
  have hLc := subgroupOf_mem_cComp (mem_cComp_of_le h hLT hHL)
  have hconc := a318 h318 hS (h36 _ hSQ) (h38 _ hSQ) hLc (isQuasisimple_subgroupOf h hLH) hp
    hp2 (one_lt_pRank_subgroupOf hF h1102 h hLH hp hp2 hcond)
  rcases hconc with h1 | ⟨hp3, h2⟩ | ⟨hp3, h3, -⟩
  · rw [← map_oPrimeResidualOf_top, ← h1, Subgroup.map_subgroupOf_eq_of_le hLH]
  · subst hp3
    rcases hcond with ⟨hk, -⟩ | ⟨-, -, h3p⟩
    · exact absurd h2 (not_case2_case3 hF h1102 h hk hLH).1
    · omega
  · subst hp3
    rcases hcond with ⟨hk, -⟩ | ⟨-, -, h3p⟩
    · exact absurd h3 (not_case2_case3 hF h1102 h hk hLH).2
    · omega

end CFSG.Quasithin.Vol2.Ch11.SecA
