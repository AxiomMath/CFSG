module

public import CFSG.Quasithin.Background.A318PC3
public import CFSG.Quasithin.Background.A318PC12
public import CFSG.Quasithin.Background.A318PC13

public section

namespace CFSG.Quasithin

namespace A318P

open CFSG.RankThree.PartTwo.Sec4

section Residual

variable {X : Type} [Group X] [Finite X] {S : Subgroup X} [hSn : S.Normal]

omit hSn in
theorem le_oPrimeResidualOf_of_quasisimple (hQ : CFSG.IsQuasisimple ↥S)
    (hZ : Nat.card (Subgroup.center ↥S) = 3) (hS2 : 2 ≤ CFSG.Open.pRank 3 S) :
    S ≤ oPrimeResidualOf 3 (⊤ : Subgroup X) := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : IsSimpleGroup (↥S ⧸ Subgroup.center ↥S) := hQ.2.1
  obtain ⟨E, hES, hEel, hEcard⟩ := CFSG.SectionRank.exists_pRank Nat.prime_three.one_lt S
  set Z' : Subgroup X := (Subgroup.center ↥S).map S.subtype with hZ'
  have hZ'card : Nat.card Z' = 3 := by
    rw [hZ', Subgroup.card_map_of_injective S.subtype_injective, hZ]
  obtain ⟨y, hyE, hyZ⟩ : ∃ y ∈ E, y ∉ Z' := by
    by_contra hcon
    push Not at hcon
    have hle : E ≤ Z' := fun y hy => hcon y hy
    have h1 := Subgroup.card_le_of_le hle
    rw [hEcard, hZ'card] at h1
    have h3 : 3 ^ 2 ≤ 3 ^ CFSG.Open.pRank 3 S := Nat.pow_le_pow_right (by norm_num) hS2
    omega
  have hyS : y ∈ S := hES hyE
  have hy3 : y ^ 3 = 1 := hEel.2 y hyE
  have hy1 : y ≠ 1 := fun h => hyZ (h ▸ Z'.one_mem)
  have hyord : orderOf y = 3 := orderOf_eq_prime hy3 hy1
  set y' : ↥S := ⟨y, hyS⟩ with hy'
  have hy'ord : orderOf y' = 3 := by
    rw [← Subgroup.orderOf_coe]
    exact hyord
  have hy'Z : y' ∉ Subgroup.center ↥S := fun h => hyZ ⟨y', h, rfl⟩
  set Nbig : Subgroup ↥S := (oPrimeResidualOf 3 (⊤ : Subgroup X)).comap S.subtype with hNbig
  have hNle : Subgroup.normalClosure ({y'} : Set ↥S) ≤ Nbig := by
    rw [Subgroup.normalClosure]
    refine (Subgroup.closure_le _).2 ?_
    intro z hz
    obtain ⟨a, ha, hconj⟩ := Group.mem_conjugatesOfSet_iff.1 hz
    obtain ⟨c, hc⟩ := isConj_iff.1 hconj
    rw [Set.mem_singleton_iff] at ha
    have hao : orderOf a = 3 := by rw [ha]; exact hy'ord
    have hz' : (S.subtype z : X) = (c : X) * (a : X) * (c : X)⁻¹ := by
      rw [← hc]
      simp
    have hord : orderOf (S.subtype z) = 3 := by
      have h := orderOf_injective (MulAut.conj (c : X)).toMonoidHom
        (MulAut.conj (c : X)).injective (a : X)
      rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at h
      rw [hz', h, Subgroup.orderOf_coe, hao]
    exact Subgroup.subset_closure ⟨Subgroup.mem_top _, 1, by rw [hord, pow_one]⟩
  have hZle : ∀ z ∈ Subgroup.center ↥S, z ∈ Nbig := by
    intro z hz
    have hz3 : z ^ 3 = 1 := by
      have := pow_card_eq_one' (G := Subgroup.center ↥S) (x := ⟨z, hz⟩)
      rw [hZ] at this
      exact congrArg Subtype.val this
    have hdvd : orderOf (S.subtype z) ∣ 3 := by
      change orderOf (z : X) ∣ 3
      rw [Subgroup.orderOf_coe]
      exact orderOf_dvd_of_pow_eq_one hz3
    rcases (Nat.dvd_prime Nat.prime_three).1 hdvd with h | h
    · exact Subgroup.subset_closure ⟨Subgroup.mem_top _, 0, by rw [h, pow_zero]⟩
    · exact Subgroup.subset_closure ⟨Subgroup.mem_top _, 1, by rw [h, pow_one]⟩
  intro s hs
  have hnorm : (Subgroup.normalClosure ({y'} : Set ↥S)).map
      (QuotientGroup.mk' (Subgroup.center ↥S)) |>.Normal :=
    Subgroup.Normal.map inferInstance _ (QuotientGroup.mk'_surjective _)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
    ((Subgroup.normalClosure ({y'} : Set ↥S)).map (QuotientGroup.mk' (Subgroup.center ↥S)))
    with h | h
  · exfalso
    have hmem : (QuotientGroup.mk' (Subgroup.center ↥S)) y' ∈
        (Subgroup.normalClosure ({y'} : Set ↥S)).map (QuotientGroup.mk' (Subgroup.center ↥S)) :=
      Subgroup.mem_map_of_mem _ (Subgroup.subset_normalClosure rfl)
    rw [h, Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hmem
    exact hy'Z hmem
  · have hmem : (QuotientGroup.mk' (Subgroup.center ↥S)) ⟨s, hs⟩ ∈
        (Subgroup.normalClosure ({y'} : Set ↥S)).map (QuotientGroup.mk' (Subgroup.center ↥S)) := by
      rw [h]
      exact Subgroup.mem_top _
    obtain ⟨n, hn, hns⟩ := Subgroup.mem_map.1 hmem
    have hzc : n⁻¹ * ⟨s, hs⟩ ∈ Subgroup.center ↥S := by
      rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply] at hns
      exact QuotientGroup.eq.1 hns
    have hs' : (⟨s, hs⟩ : ↥S) = n * (n⁻¹ * ⟨s, hs⟩) := by group
    have : (⟨s, hs⟩ : ↥S) ∈ Nbig := by
      rw [hs']
      exact mul_mem (hNle hn) (hZle _ hzc)
    exact this

omit hSn in
theorem oPrimeResidualOf_eq_sup (hQ : CFSG.IsQuasisimple ↥S)
    (hZ : Nat.card (Subgroup.center ↥S) = 3) (hS2 : 2 ≤ CFSG.Open.pRank 3 S) {x : X}
    (hx : orderOf x = 3)
    (hA : ∀ g : X, (∃ k : ℕ, orderOf g = 3 ^ k) → g ∈ S ⊔ Subgroup.zpowers x) :
    oPrimeResidualOf 3 (⊤ : Subgroup X) = S ⊔ Subgroup.zpowers x := by
  refine le_antisymm ((Subgroup.closure_le _).2 ?_)
    (sup_le (le_oPrimeResidualOf_of_quasisimple hQ hZ hS2) ?_)
  · rintro g ⟨-, k, hk⟩
    exact hA g ⟨k, hk⟩
  · rw [Subgroup.zpowers_le]
    exact Subgroup.subset_closure ⟨Subgroup.mem_top x, 1, by rw [hx, pow_one]⟩

end Residual

theorem qCentralTail_native
    : QCentralTail := by
  intro X _ _ S _ hQ hZ s q hSL hmod hP hS2 hX x hx hxS
  have hSLpi : IsSLThreePi ↥S := by
    refine ⟨q, ?_⟩
    cases s
    · obtain ⟨K, hKf, hKfin, hKcard, ⟨e⟩⟩ := hSL
      refine ⟨K, hKf, hKfin, Or.inr ⟨hKcard, ?_, ⟨e⟩⟩⟩
      simp only [Bool.false_eq_true, ↓reduceIte] at hmod
      unfold Int.ModEq at hmod
      omega
    · obtain ⟨K, hKf, hKfin, hKcard, ⟨e⟩⟩ := hSL
      refine ⟨K, hKf, hKfin, Or.inl ⟨hKcard, ?_, ⟨e⟩⟩⟩
      simp only [↓reduceIte] at hmod
      unfold Int.ModEq at hmod
      omega
  obtain ⟨π, p, f, K, hKf, hK, hq, hq2, ⟨e⟩⟩ := exists_slPi_model hSLpi hQ
  have hA : ∀ g : X, (∃ k : ℕ, orderOf g = 3 ^ k) → g ∈ S ⊔ Subgroup.zpowers x := by
    cases π
    · exact three_elements_mem_sup_unitary hQ hS2 hX hK hq hq2 e hZ hP hx hxS
    · exact three_elements_mem_sup_linear hQ hS2 hX hK hq hq2 e hZ hP hx hxS
  exact oPrimeResidualOf_eq_sup hQ hZ hS2 hx hA

theorem a318CentralFact_native
    : A318CentralFact := a318CentralFact_of_tail qCentralTail_native

end A318P

end CFSG.Quasithin
