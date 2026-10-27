module

public import CFSG.LocalAnalysis.StandardType.GGB36Defs
public import CFSG.LocalAnalysis.StandardType.UnitaryTwoLocalRankLower
public import CFSG.LocalAnalysis.StandardType.GGNbrLangTorARankBound

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

private theorem ltqRc_add_eps_le_twoLocalRank_of_torusLift {X R : Type} [Group X] [Finite X]
    [Group R] {r : ℕ} (hT : GGTorusLift 3 r R) (e : X ⧸ Subgroup.center X ≃* R)
    (hcomm : commutator X = ⊤) :
    r + (if 3 ∣ Nat.card (Subgroup.center X) then 1 else 0) ≤ LargeEvenTwoLocalRank 3 X := by
  classical
  let ψ : X →* R := e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center X))
  have hψs : Function.Surjective ψ := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker_eq : ψ.ker = Subgroup.center X := by
    ext x
    rw [MonoidHom.mem_ker]
    constructor
    · intro hx
      change e (QuotientGroup.mk' (Subgroup.center X) x) = 1 at hx
      rw [QuotientGroup.mk'_apply] at hx
      have h1 : QuotientGroup.mk x = 1 := e.injective (by rw [hx, map_one])
      rwa [QuotientGroup.eq_one_iff] at h1
    · intro hx
      have h1 : QuotientGroup.mk' (Subgroup.center X) x = 1 := by
        rwa [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      show e (QuotientGroup.mk' (Subgroup.center X) x) = 1
      rw [h1, map_one]
  have hker : ψ.ker ≤ Subgroup.center X := hker_eq.le
  obtain ⟨U, E, hUne, hU2, hEU, hEab, hEcard, hEker⟩ := hT X ψ hψs hker hcomm
  have hle : r ≤ LargeEvenTwoLocalRank 3 X :=
    TableB.le_twoLocalRank (p := 3) (by norm_num) ⟨U, hUne, hU2, rfl⟩
      (TableB.le_pRank_of_le (by norm_num) hEU hEab hEcard)
  by_cases h3 : 3 ∣ Nat.card (Subgroup.center X)
  · rw [if_pos h3]
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    obtain ⟨x0, hx0⟩ := exists_prime_orderOf_dvd_card' (G := Subgroup.center X) 3 h3
    let x : X := (x0 : X)
    have hxcent : x ∈ Subgroup.center X := x0.2
    have hxord : orderOf x = 3 := by
      show orderOf (x0 : X) = 3
      rw [Subgroup.orderOf_coe, hx0]
    have hx3 : x ^ 3 = 1 := by rw [← hxord]; exact pow_orderOf_eq_one x
    have hx1 : x ≠ 1 := by
      intro h1
      rw [h1, orderOf_one] at hxord
      exact absurd hxord (by norm_num)
    have hxker : x ∈ ψ.ker := by rw [hker_eq]; exact hxcent
    have hzpk : Subgroup.zpowers x ≤ ψ.ker := Subgroup.zpowers_le.mpr hxker
    have hzpcent : Subgroup.zpowers x ≤ Subgroup.center X := Subgroup.zpowers_le.mpr hxcent
    have hdisj : Disjoint E (Subgroup.zpowers x) := by
      rw [Subgroup.disjoint_def]
      intro y hyE hyZ
      have hy : y ∈ E ⊓ ψ.ker := ⟨hyE, hzpk hyZ⟩
      rwa [hEker, Subgroup.mem_bot] at hy
    have hNX : Subgroup.zpowers x ≤ Subgroup.normalizer (E : Set X) :=
      hzpcent.trans (Subgroup.center_le_normalizer (E : Set X))
    have hcommxE : ∀ a ∈ E, ∀ c ∈ Subgroup.zpowers x, a * c = c * a := by
      intro a ha c hc
      exact Subgroup.mem_center_iff.mp (hzpcent hc) a
    have hzab : IsElemAbelian 3 (Subgroup.zpowers x) := by
      refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, ?_⟩
      · obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp a.2
        obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp b.2
        show (a : X) * b = b * a
        rw [← hi, ← hj, ← zpow_add, ← zpow_add, add_comm]
      · intro y hy
        obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
        rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hx3, one_zpow]
    have hE'ab : IsElemAbelian 3 (E ⊔ Subgroup.zpowers x) :=
      TableB.isElemAbelian_sup hEab hzab hcommxE
    have hE'card : Nat.card (E ⊔ Subgroup.zpowers x : Subgroup X) = 3 ^ (r + 1) := by
      have hcard := CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer E
        (Subgroup.zpowers x) hNX hdisj
      rw [hcard, hEcard, Nat.card_zpowers, hxord, pow_succ]
    have hE'N : E ⊔ Subgroup.zpowers x ≤ Subgroup.normalizer (U : Set X) :=
      sup_le hEU (hzpcent.trans (Subgroup.center_le_normalizer (U : Set X)))
    exact TableB.le_twoLocalRank (p := 3) (by norm_num) ⟨U, hUne, hU2, rfl⟩
      (TableB.le_pRank_of_le (by norm_num) hE'N hE'ab hE'card)
  · rw [if_neg h3, Nat.add_zero]
    exact hle

theorem ggALocalRankSubThree_holds
    (X : Type) [Group X] [Finite X] (lab : LargeEvenLabel)
    (hlab : LargeEvenInLambda2 lab)
    (hsplit : (lab.tag = .A ∧ 3 ∣ 2 ^ lab.n - 1) ∨ (lab.tag = .twA ∧ 3 ∣ 2 ^ lab.n + 1))
    (h3dvd : 3 ∣ lab.rank + 1) (h9 : 9 ≤ lab.rank + 1)
    (hHas : GGHasLabel lab (X ⧸ Subgroup.center X)) (hcomm : commutator X = ⊤) :
    (lab.rank + 1 - 3) + (if 3 ∣ Nat.card (Subgroup.center X) then 1 else 0) ≤
      LargeEvenTwoLocalRank 3 X := by
  rcases hsplit with ⟨htag, hpq⟩ | ⟨htag, hpq⟩
  ·
    obtain ⟨t, l, n⟩ := lab
    dsimp only at htag hpq h3dvd h9 hlab ⊢
    subst htag
    have hl4 : 4 ≤ l := by omega
    have hall := largeEvenLabelAll_torusLift_typeA (p := 3) (lab := ⟨.A, l, n⟩)
      Nat.prime_three rfl hl4 hpq
    have hRaw := hall (fun R _ _ _ => Nonempty (X ⧸ Subgroup.center X ≃* R)) hHas
    dsimp only [LargeEvenRawDatum] at hRaw
    obtain ⟨K, _, _, hK, hP⟩ := hRaw
    obtain ⟨⟨e⟩, hT⟩ := hP
    have h := ltqRc_add_eps_le_twoLocalRank_of_torusLift hT e hcomm
    have h6 : (l + 1 - 3) + (if 3 ∣ Nat.card (Subgroup.center X) then 1 else 0) ≤
        (l + 1 - 2) + (if 3 ∣ Nat.card (Subgroup.center X) then 1 else 0) := by omega
    exact h6.trans h
  ·
    obtain ⟨t, l, n⟩ := lab
    dsimp only at htag hpq h3dvd h9 hlab ⊢
    subst htag
    have hall := largeEvenLabelAll_torusLift_twA (lab := ⟨.twA, l, n⟩)
      hlab rfl Nat.prime_three hpq
    have hRaw := hall (fun R _ _ _ => Nonempty (X ⧸ Subgroup.center X ≃* R)) hHas
    dsimp only [LargeEvenRawDatum] at hRaw
    obtain ⟨K, _, _, hK, hP⟩ := hRaw
    obtain ⟨⟨e⟩, hT⟩ := hP
    have hT' := by
      simpa only [ggUnitaryTorusRank, h3dvd, ↓reduceIte] using hT
    exact ltqRc_add_eps_le_twoLocalRank_of_torusLift hT' e hcomm

theorem ggALocalRankThree_holds :
    ∀ (X : Type) [Group X] [Finite X] (lab : LargeEvenLabel), LargeEvenInLambda2 lab →
      ((lab.tag = .A ∧ 3 ∣ 2 ^ lab.n - 1) ∨ (lab.tag = .twA ∧ 3 ∣ 2 ^ lab.n + 1)) → 3 ∣ lab.rank + 1 → 9 ≤ lab.rank + 1 →
      GGHasLabel lab (X ⧸ Subgroup.center X) → commutator X = ⊤ →
      6 + (if 3 ∣ Nat.card (Subgroup.center X) then 1 else 0) ≤ LargeEvenTwoLocalRank 3 X := by
  intro X _ _ lab hlab hsplit h3dvd h9 hHas hcomm
  exact le_trans (by omega) (ggALocalRankSubThree_holds X lab hlab hsplit h3dvd h9 hHas hcomm)

end CFSG.StandardType

end
