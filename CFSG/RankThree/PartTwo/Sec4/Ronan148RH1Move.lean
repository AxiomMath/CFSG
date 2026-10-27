module

public import CFSG.RankThree.PartTwo.Sec4.Ronan148RH1E9
public import CFSG.RankThree.Asc83Table.M23
public import CFSG.RankThree.Asc83Table.HS

public section

namespace CFSG.RankThree.PartTwo.Sec4.Ronan148R

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open CFSG.RankThree.PartTwo.Sec4.RonanK429 CFSG.RankThree.PartTwo.Sec4.RonanK429H
open CFSG.RankThree.PartTwo.Sec4.Ronan148S
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

section Move

variable {S : Type} [Group S] [Finite S]

theorem exists_move_of_card_automizer {B : Subgroup S}
    (hB : CFSG.Assembly.IsElemAbelian 3 B) (hB9 : Nat.card B = 9)
    (hA : 12 < Nat.card (CFSG.RankThree.Asc83Table.Automizer B))
    {s : S} (hs : s ∈ B) (hs1 : s ≠ 1) :
    ∃ n ∈ Subgroup.normalizer (B : Set S), n ∉ Subgroup.normalizer (Subgroup.zpowers s : Set S) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  by_contra hcon
  push Not at hcon
  have hs3 : s ^ 3 = 1 := hB.2 s hs
  have hord : Nat.card (Subgroup.zpowers s) = 3 := by
    rw [Nat.card_zpowers, orderOf_eq_prime hs3 hs1]
  obtain ⟨t, ht, htn⟩ : ∃ t ∈ B, t ∉ Subgroup.zpowers s := by
    by_contra h
    push Not at h
    have hle : B ≤ Subgroup.zpowers s := fun x hx => h x hx
    have := Subgroup.card_le_of_le hle
    omega
  have hgen : B ≤ Subgroup.closure ({s, t} : Set S) := by
    have hHB : Subgroup.closure ({s, t} : Set S) ≤ B := by
      rw [Subgroup.closure_le]
      intro x hx
      rcases hx with h | h
      · rw [h]; exact hs
      · rw [Set.mem_singleton_iff] at h; rw [h]; exact ht
    have hsH : Subgroup.zpowers s ≤ Subgroup.closure ({s, t} : Set S) :=
      Subgroup.zpowers_le.2 (Subgroup.subset_closure (by simp))
    have htH : t ∈ Subgroup.closure ({s, t} : Set S) := Subgroup.subset_closure (by simp)
    have hd1 : Nat.card (Subgroup.closure ({s, t} : Set S)) ∣ 9 := by
      have := Subgroup.card_dvd_of_le hHB
      rwa [hB9] at this
    have hd3 : 3 ∣ Nat.card (Subgroup.closure ({s, t} : Set S)) := by
      have := Subgroup.card_dvd_of_le hsH
      rwa [hord] at this
    have hne3 : Nat.card (Subgroup.closure ({s, t} : Set S)) ≠ 3 := by
      intro h3
      apply htn
      have heq : Subgroup.zpowers s = Subgroup.closure ({s, t} : Set S) :=
        Subgroup.eq_of_le_of_card_ge hsH (by rw [h3, hord])
      rw [heq]
      exact htH
    have hH9 : Nat.card (Subgroup.closure ({s, t} : Set S)) = 9 := by
      generalize Nat.card (Subgroup.closure ({s, t} : Set S)) = n at hd1 hd3 hne3 ⊢
      have hn : n ≤ 9 := Nat.le_of_dvd (by norm_num) hd1
      interval_cases n <;> omega
    exact (Subgroup.eq_of_le_of_card_ge hHB (by omega)).symm.le
  set ψ : Subgroup.normalizer (B : Set S) →* MulAut B := Subgroup.normalizerMonoidHom B with hψ
  have hkerψ : ψ.ker =
      (Subgroup.centralizer (B : Set S)).subgroupOf (Subgroup.normalizer (B : Set S)) :=
    Subgroup.normalizerMonoidHom_ker B
  have hcardA : Nat.card ψ.range = Nat.card (CFSG.RankThree.Asc83Table.Automizer B) := by
    have e1 : CFSG.RankThree.Asc83Table.Automizer B ≃* ψ.range :=
      (QuotientGroup.quotientMulEquivOfEq hkerψ.symm).trans (QuotientGroup.quotientKerEquivRange ψ)
    exact (Nat.card_congr e1.toEquiv).symm
  have hψapp : ∀ (n : Subgroup.normalizer (B : Set S)) (b : B),
      ((ψ n b : B) : S) = (n : S) * (b : S) * (n : S)⁻¹ :=
    fun n b => rfl
  set X : Set S := (Subgroup.zpowers s : Set S) \ {1} with hX
  set Y : Set S := (B : Set S) \ (Subgroup.zpowers s : Set S) with hY
  have hzB : (Subgroup.zpowers s : Set S) ⊆ (B : Set S) := by
    intro x hx
    exact (Subgroup.zpowers_le.mpr hs) hx
  have hXc : X.ncard = 2 := by
    rw [hX, Set.ncard_diff_singleton_of_mem (Subgroup.one_mem _), ← Nat.card_coe_set_eq]
    change Nat.card (Subgroup.zpowers s) - 1 = 2
    rw [hord]
  have hYc : Y.ncard = 6 := by
    rw [hY, Set.ncard_diff hzB, ← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq]
    change Nat.card B - Nat.card (Subgroup.zpowers s) = 6
    rw [hB9, hord]
  have hmemX : ∀ n : Subgroup.normalizer (B : Set S), ((ψ n ⟨s, hs⟩ : B) : S) ∈ X := by
    intro n
    refine ⟨?_, ?_⟩
    · have h1 : (n : S) ∈ Subgroup.normalizer (Subgroup.zpowers s : Set S) := hcon (n : S) n.2
      exact (Subgroup.mem_normalizer_iff.mp h1 s).mp (Subgroup.mem_zpowers s)
    · intro h1
      apply hs1
      rw [Set.mem_singleton_iff, hψapp] at h1
      calc s = (n : S)⁻¹ * ((n : S) * s * (n : S)⁻¹) * n := by group
        _ = 1 := by rw [h1]; group
  have hmemY : ∀ n : Subgroup.normalizer (B : Set S), ((ψ n ⟨t, ht⟩ : B) : S) ∈ Y := by
    intro n
    refine ⟨(ψ n ⟨t, ht⟩).2, fun h1 => htn ?_⟩
    have h2 : (n : S)⁻¹ ∈ Subgroup.normalizer (Subgroup.zpowers s : Set S) :=
      Subgroup.inv_mem _ (hcon (n : S) n.2)
    have h3 := (Subgroup.mem_normalizer_iff.mp h2 _).mp h1
    rw [hψapp] at h3
    have : (n : S)⁻¹ * ((n : S) * t * (n : S)⁻¹) * (n : S)⁻¹⁻¹ = t := by group
    rwa [this] at h3
  have hkey : ∀ n m : Subgroup.normalizer (B : Set S),
      (n : S) * s * (n : S)⁻¹ = (m : S) * s * (m : S)⁻¹ →
      (n : S) * t * (n : S)⁻¹ = (m : S) * t * (m : S)⁻¹ → ψ n = ψ m := by
    intro n m h1 h2
    have hdN : (m : S)⁻¹ * (n : S) ∈ Subgroup.normalizer (B : Set S) :=
      Subgroup.mul_mem _ (Subgroup.inv_mem _ m.2) n.2
    have hds : ((m : S)⁻¹ * (n : S)) * s = s * ((m : S)⁻¹ * (n : S)) := by
      calc ((m : S)⁻¹ * (n : S)) * s = (m : S)⁻¹ * ((n : S) * s * (n : S)⁻¹) * (n : S) := by
            group
        _ = (m : S)⁻¹ * ((m : S) * s * (m : S)⁻¹) * (n : S) := by rw [h1]
        _ = s * ((m : S)⁻¹ * (n : S)) := by group
    have hdt : ((m : S)⁻¹ * (n : S)) * t = t * ((m : S)⁻¹ * (n : S)) := by
      calc ((m : S)⁻¹ * (n : S)) * t = (m : S)⁻¹ * ((n : S) * t * (n : S)⁻¹) * (n : S) := by
            group
        _ = (m : S)⁻¹ * ((m : S) * t * (m : S)⁻¹) * (n : S) := by rw [h2]
        _ = t * ((m : S)⁻¹ * (n : S)) := by group
    have hclos : Subgroup.closure ({s, t} : Set S) ≤
        Subgroup.centralizer ({(m : S)⁻¹ * (n : S)} : Set S) := by
      rw [Subgroup.closure_le]
      intro y hy
      rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
      intro g hg
      rw [Set.mem_singleton_iff] at hg
      rw [hg]
      rcases hy with h | h
      · rw [h]; exact hds
      · rw [Set.mem_singleton_iff] at h; rw [h]; exact hdt
    have hdC : (m : S)⁻¹ * (n : S) ∈ Subgroup.centralizer (B : Set S) := by
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      have hx' := hclos (hgen hx)
      rw [Subgroup.mem_centralizer_iff] at hx'
      exact (hx' _ (Set.mem_singleton _)).symm
    have hker1 : (⟨(m : S)⁻¹ * (n : S), hdN⟩ : Subgroup.normalizer (B : Set S)) ∈ ψ.ker := by
      rw [hkerψ, Subgroup.mem_subgroupOf]
      exact hdC
    have hone : ψ ⟨(m : S)⁻¹ * (n : S), hdN⟩ = 1 := MonoidHom.mem_ker.mp hker1
    have hnm : n = m * ⟨(m : S)⁻¹ * (n : S), hdN⟩ := Subtype.ext (by simp)
    calc ψ n = ψ (m * ⟨(m : S)⁻¹ * (n : S), hdN⟩) := congrArg ψ hnm
      _ = ψ m := by rw [map_mul, hone, mul_one]
  let F : ψ.range → ↥(X ×ˢ Y) := fun φ' => ⟨(((φ'.1 ⟨s, hs⟩ : B) : S), ((φ'.1 ⟨t, ht⟩ : B) : S)),
    by
      obtain ⟨φ', n, rfl⟩ := φ'
      exact ⟨hmemX n, hmemY n⟩⟩
  have hF : Function.Injective F := by
    rintro ⟨φ', hφ'⟩ ⟨φ'', hφ''⟩ h
    obtain ⟨n, rfl⟩ := hφ'
    obtain ⟨m, rfl⟩ := hφ''
    simp only [F, Subtype.mk.injEq, Prod.mk.injEq] at h
    obtain ⟨h1, h2⟩ := h
    have h1' : (n : S) * s * (n : S)⁻¹ = (m : S) * s * (m : S)⁻¹ :=
      ((hψapp n ⟨s, hs⟩).symm.trans h1).trans (hψapp m ⟨s, hs⟩)
    have h2' : (n : S) * t * (n : S)⁻¹ = (m : S) * t * (m : S)⁻¹ :=
      ((hψapp n ⟨t, ht⟩).symm.trans h2).trans (hψapp m ⟨t, ht⟩)
    exact Subtype.ext (hkey n m h1' h2')
  have hle : Nat.card ψ.range ≤ Nat.card ↥(X ×ˢ Y) := Nat.card_le_card_of_injective F hF
  rw [Nat.card_coe_set_eq, Set.ncard_prod, hXc, hYc, hcardA] at hle
  omega

theorem card_semidihedralGroup_four : Nat.card (CFSG.Open.SemidihedralGroup 4) = 16 := by
  rw [CFSG.Semidihedral.card 4 (by norm_num)]
  norm_num

theorem e9Move_of_sd16
    (h : ∀ B : Subgroup S, Nat.card B = 9 →
      Nonempty (CFSG.RankThree.Asc83Table.Automizer B ≃* CFSG.Open.SemidihedralGroup 4)) :
    E9Move S := by
  intro E hE hE9 s hs hs1
  obtain ⟨φ⟩ := h E hE9
  refine exists_move_of_card_automizer hE hE9 ?_ hs hs1
  rw [Nat.card_congr φ.toEquiv, card_semidihedralGroup_four]
  norm_num

end Move

section M23


theorem automizer_m23_all {L : Type} [Group L] (e : L ≃* Blueprint.NativeSporadic.M23) :
    ∀ B : Subgroup L, Nat.card B = 9 →
      Nonempty (CFSG.RankThree.Asc83Table.Automizer B ≃* CFSG.Open.SemidihedralGroup 4) := by
  obtain ⟨-, -, h₃⟩ := CFSG.RankThree.Asc83Table.e9_transport CFSG.RankThree.Asc83Table.M23.E
    CFSG.RankThree.Asc83Table.M23.factorization_card e
  obtain ⟨q⟩ := CFSG.RankThree.Asc83Table.M23.automizer_P0
  intro B hB
  obtain ⟨f⟩ := h₃ B hB
  exact ⟨f.trans q⟩

theorem rankTwo_spor_m23 : RankTwoData (Spor .M23) := by
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.M23.nonempty_mulEquiv
  have b' : Blueprint.NativeSporadic.M23 ≃* Spor .M23 := b
  haveI : Finite (Spor .M23) := Finite.of_equiv _ b'.toEquiv
  have hrank : CFSG.pRank 3 (Spor .M23) = 2 :=
    (CFSG.RankThree.Asc83Table.e9_transport CFSG.RankThree.Asc83Table.M23.E
      CFSG.RankThree.Asc83Table.M23.factorization_card b'.symm).2.1
  refine ⟨cubeInner_of_not_three_dvd_card_outer spor_m23.1, fun E hE => ?_, ?_⟩
  · have h2 : CFSG.Open.pRank 3 (⊤ : Subgroup (Spor .M23)) ≤ 2 := by
      rw [← CFSG.SectionRank.pRank_eq_open_pRank_top 3 (Spor .M23)]
      exact hrank.le
    exact (card_le_of_pRank_le h2 hE).trans (by norm_num)
  · exact exists_e9_of_pRank_eq_two
      ((CFSG.SectionRank.pRank_eq_open_pRank_top 3 (Spor .M23)).symm.trans hrank)

theorem m23_orderChecks :
    (∀ q, 2 ≤ q → q ^ 3 ∣ 10200960 →
      10200960 * Nat.gcd 3 (q - 1) ≠ q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 - 1))) ∧
    (∀ q, 2 ≤ q → q ^ 3 ∣ 10200960 →
      10200960 * Nat.gcd 3 (q + 1) ≠ q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 + 1))) :=
  orderChecks_of_bound (B := 10) (by norm_num) (by decide +kernel)

end M23

section HS


theorem automizer_hs_all {L : Type} [Group L] (e : L ≃* Blueprint.NativeSporadic.HS) :
    ∀ B : Subgroup L, Nat.card B = 9 →
      Nonempty (CFSG.RankThree.Asc83Table.Automizer B ≃* CFSG.Open.SemidihedralGroup 4) := by
  obtain ⟨-, -, h₃⟩ := CFSG.RankThree.Asc83Table.e9_transport CFSG.RankThree.Asc83Table.HS.E
    CFSG.RankThree.Asc83Table.HS.factorization_card e
  obtain ⟨q⟩ := CFSG.RankThree.Asc83Table.HS.automizer_P0
  intro B hB
  obtain ⟨f⟩ := h₃ B hB
  exact ⟨f.trans q⟩

theorem rankTwo_spor_hs : RankTwoData (Spor .HS) := by
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.HS.nonempty_mulEquiv
  have b' : Blueprint.NativeSporadic.HS ≃* Spor .HS := b
  haveI : Finite (Blueprint.NativeSporadic.HS) := Nat.finite_of_card_ne_zero (by
    rw [CFSG.Sporadic.HS.card_HS]; norm_num)
  haveI : Finite (Spor .HS) := Finite.of_equiv _ b'.toEquiv
  have hrank : CFSG.pRank 3 (Spor .HS) = 2 :=
    (CFSG.RankThree.Asc83Table.e9_transport CFSG.RankThree.Asc83Table.HS.E
      CFSG.RankThree.Asc83Table.HS.factorization_card b'.symm).2.1
  refine ⟨cubeInner_of_not_three_dvd_card_outer spor_hs.1, fun E hE => ?_, ?_⟩
  · have h2 : CFSG.Open.pRank 3 (⊤ : Subgroup (Spor .HS)) ≤ 2 := by
      rw [← CFSG.SectionRank.pRank_eq_open_pRank_top 3 (Spor .HS)]
      exact hrank.le
    exact (card_le_of_pRank_le h2 hE).trans (by norm_num)
  · exact exists_e9_of_pRank_eq_two
      ((CFSG.SectionRank.pRank_eq_open_pRank_top 3 (Spor .HS)).symm.trans hrank)

theorem hs_orderChecks :
    (∀ q, 2 ≤ q → q ^ 3 ∣ 44352000 →
      44352000 * Nat.gcd 3 (q - 1) ≠ q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 - 1))) ∧
    (∀ q, 2 ≤ q → q ^ 3 ∣ 44352000 →
      44352000 * Nat.gcd 3 (q + 1) ≠ q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 + 1))) :=
  orderChecks_of_bound (B := 12) (by norm_num) (by decide +kernel)

end HS

section Rows


section M23Row


theorem rowOf427_m23
    : RowOf427 (Spor .M23) := by
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.M23.nonempty_mulEquiv
  have b' : Blueprint.NativeSporadic.M23 ≃* Spor .M23 := b
  have hcard : Nat.card (Spor .M23) = 10200960 := by
    rw [← Nat.card_congr b'.toEquiv, CFSG.Sporadic.Schreier.m23_card]
  haveI : Finite (Spor .M23) := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  refine rowOf427_of_e9Move ?_ rankTwo_spor_m23
    (fun S _ _ ⟨e⟩ => e9Move_of_sd16 (automizer_m23_all (e.trans b'.symm)))
    (by rw [hcard]; norm_num)
  intro L _ _ hSL hL hZ3 ⟨e'⟩
  exact center_eq_bot_of_card hSL hL hZ3 ((Nat.card_congr e'.toEquiv).trans hcard)
    m23_orderChecks.1 m23_orderChecks.2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end M23Row

section HSRow


theorem rowOf427_hs
    : RowOf427 (Spor .HS) := by
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.HS.nonempty_mulEquiv
  have b' : Blueprint.NativeSporadic.HS ≃* Spor .HS := b
  have hcard : Nat.card (Spor .HS) = 44352000 := by
    rw [← Nat.card_congr b'.toEquiv, CFSG.Sporadic.HS.card_HS]
  haveI : Finite (Spor .HS) := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  refine rowOf427_of_e9Move ?_ rankTwo_spor_hs
    (fun S _ _ ⟨e⟩ => e9Move_of_sd16 (automizer_hs_all (e.trans b'.symm)))
    (by rw [hcard]; norm_num)
  intro L _ _ hSL hL hZ3 ⟨e'⟩
  exact center_eq_bot_of_card hSL hL hZ3 ((Nat.card_congr e'.toEquiv).trans hcard)
    hs_orderChecks.1 hs_orderChecks.2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end HSRow

end Rows

end CFSG.RankThree.PartTwo.Sec4.Ronan148R

end
