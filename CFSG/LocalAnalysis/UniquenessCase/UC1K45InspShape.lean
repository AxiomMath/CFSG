module

public import CFSG.LocalAnalysis.UniquenessCase.UC1K45W
public import CFSG.LocalAnalysis.UniquenessCase.UC1K45InspGrp
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.S3AmalgamBound.OvergroupConj
public import CFSG.RankThree.PartTwo.Sec4.RonanK432Transfer
public import Certificates.Data.A5

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UCK.InspPS

open CFSG.LocalAnalysis.UniquenessCase.UCK
open Subgroup
open scoped commutatorElement

theorem alt5_pow_fifteen :
    ∀ σ : alternatingGroup (Fin 5), σ ^ 15 = 1 → σ ^ 3 = 1 ∨ σ ^ 5 = 1 := by
  decide +kernel

theorem card_alt5 : Nat.card (alternatingGroup (Fin 5)) = 60 := by
  rw [Nat.card_eq_fintype_card, card_alternatingGroup]
  decide

theorem alt5_orderOf_odd (σ : alternatingGroup (Fin 5)) (h : Odd (orderOf σ)) :
    orderOf σ = 1 ∨ orderOf σ = 3 ∨ orderOf σ = 5 := by
  have h60 : orderOf σ ∣ 60 := card_alt5 ▸ orderOf_dvd_natCard σ
  have hc : Nat.Coprime (orderOf σ) 4 := by
    simpa using (Nat.coprime_two_right.2 h).pow_right 2
  have h15 : orderOf σ ∣ 15 :=
    Nat.Coprime.dvd_of_dvd_mul_left hc (by simpa using h60)
  rcases alt5_pow_fifteen σ (orderOf_dvd_iff_pow_eq_one.1 h15) with h3 | h5
  · rcases (Nat.dvd_prime Nat.prime_three).1 (orderOf_dvd_of_pow_eq_one h3) with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  · rcases (Nat.dvd_prime Nat.prime_five).1 (orderOf_dvd_of_pow_eq_one h5) with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inr h)

theorem z3E9A5Mod2_unfold {H : Type} [Group H] {Y : Subgroup H} (h : Z3E9A5Mod2 Y) :
    ∃ (N : Subgroup ↥Y) (_ : N.Normal), IsPGroup 2 N ∧
      ((IsCyclic (↥Y ⧸ N) ∧ Nat.card (↥Y ⧸ N) = 3) ∨
        (Nat.card (↥Y ⧸ N) = 9 ∧ IsMulCommutative (↥Y ⧸ N)) ∨
        CFSG.Quasithin.IsAlt 5 (↥Y ⧸ N)) := by
  have hN : (CFSG.Open.pCoreOf 2 Y).subgroupOf Y = CFSG.pCore 2 ↥Y :=
    CFSG.openPCoreOf_subgroupOf 2 Y
  haveI : ((CFSG.Open.pCoreOf 2 Y).subgroupOf Y).Normal := by
    rw [hN]; exact CFSG.pCore_normal
  refine ⟨(CFSG.Open.pCoreOf 2 Y).subgroupOf Y, inferInstance, ?_, h _ rfl⟩
  rw [hN]
  exact CFSG.pCore_isPGroup

theorem not_z3E9A5Mod2_of_odd_card {H : Type} [Group H] [Finite H] {Y : Subgroup H}
    (hodd : Odd (Nat.card Y)) (h3 : Nat.card Y ≠ 3) (h9 : Nat.card Y ≠ 9) :
    ¬ Z3E9A5Mod2 Y := by
  intro h
  obtain ⟨N, hN, hNp, hcases⟩ := z3E9A5Mod2_unfold h
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := hNp.exists_card_eq
  have hNY : Nat.card N ∣ Nat.card Y := Subgroup.card_subgroup_dvd_card N
  have hk0 : k = 0 := by
    by_contra hk0
    have h2 : 2 ∣ Nat.card N := by
      rw [hk]; exact dvd_pow_self 2 hk0
    exact (Nat.not_even_iff_odd.2 hodd) (even_iff_two_dvd.2 (h2.trans hNY))
  have hN1 : Nat.card N = 1 := by rw [hk, hk0, pow_zero]
  have hQ : Nat.card (↥Y ⧸ N) = Nat.card Y := by
    have := Subgroup.card_eq_card_quotient_mul_card_subgroup N
    rwa [hN1, mul_one, eq_comm] at this
  rcases hcases with ⟨-, hc⟩ | ⟨hc, -⟩ | ⟨⟨e⟩⟩
  · exact h3 (hQ ▸ hc)
  · exact h9 (hQ ▸ hc)
  · have h60 : Nat.card (↥Y ⧸ N) = 60 := by
      rw [Nat.card_congr e.toEquiv, card_alt5]
    rw [← hQ, h60] at hodd
    exact absurd hodd (by decide)

theorem orderOf_quot_eq_of_odd {H : Type} [Group H] {Y : Subgroup H} {N : Subgroup ↥Y} [N.Normal]
    (hNp : IsPGroup 2 N) {x : H} (hx : x ∈ Y) (hodd : Odd (orderOf x)) :
    orderOf (QuotientGroup.mk (⟨x, hx⟩ : ↥Y) : ↥Y ⧸ N) = orderOf x := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set y : ↥Y := ⟨x, hx⟩ with hydef
  have hy : orderOf y = orderOf x := Subgroup.orderOf_mk x hx
  apply Nat.dvd_antisymm
  · rw [← hy]; exact orderOf_map_dvd (QuotientGroup.mk' N) y
  · set n := orderOf (QuotientGroup.mk y : ↥Y ⧸ N) with hn
    have hmem : y ^ n ∈ N := by
      have : (QuotientGroup.mk (y ^ n) : ↥Y ⧸ N) = 1 := by
        rw [QuotientGroup.mk_pow]; exact pow_orderOf_eq_one _
      exact (QuotientGroup.eq_one_iff _).1 this
    obtain ⟨j, hj⟩ := (IsPGroup.iff_orderOf.1 hNp) ⟨y ^ n, hmem⟩
    have hj' : orderOf (y ^ n) = 2 ^ j := by
      rw [← hj]; exact (Subgroup.orderOf_mk (y ^ n) hmem).symm
    have hdvd : orderOf (y ^ n) ∣ orderOf x := hy ▸ orderOf_pow_dvd n
    have hj0 : j = 0 := by
      by_contra hj0
      have h2 : 2 ∣ orderOf x := (dvd_pow_self 2 hj0).trans (hj' ▸ hdvd)
      exact (Nat.not_even_iff_odd.2 hodd) (even_iff_two_dvd.2 h2)
    rw [hj0, pow_zero, orderOf_eq_one_iff] at hj'
    rw [← hy]
    exact orderOf_dvd_of_pow_eq_one hj'

theorem not_z3E9A5Mod2_of_odd_orderOf {H : Type} [Group H] [Finite H] {Y : Subgroup H} {x : H}
    (hx : x ∈ Y) (hodd : Odd (orderOf x)) (h1 : orderOf x ≠ 1) (h3 : orderOf x ≠ 3)
    (h5 : orderOf x ≠ 5) (h9 : orderOf x ≠ 9) : ¬ Z3E9A5Mod2 Y := by
  intro h
  obtain ⟨N, hN, hNp, hcases⟩ := z3E9A5Mod2_unfold h
  have hq := orderOf_quot_eq_of_odd (N := N) hNp hx hodd
  set q : ↥Y ⧸ N := QuotientGroup.mk (⟨x, hx⟩ : ↥Y)
  rcases hcases with ⟨-, hc⟩ | ⟨hc, -⟩ | ⟨⟨e⟩⟩
  · have hd : orderOf x ∣ 3 := hq ▸ hc ▸ orderOf_dvd_natCard q
    rcases (Nat.dvd_prime Nat.prime_three).1 hd with h | h
    · exact h1 h
    · exact h3 h
  · have hd : orderOf x ∣ 3 ^ 2 := hq ▸ (by simpa using hc ▸ orderOf_dvd_natCard q)
    obtain ⟨i, hi, hi'⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 hd
    interval_cases i
    · exact h1 (by simpa using hi')
    · exact h3 (by simpa using hi')
    · exact h9 (by simpa using hi')
  · have ho : orderOf (e q) = orderOf x := by rw [MulEquiv.orderOf_eq, hq]
    rcases alt5_orderOf_odd (e q) (ho ▸ hodd) with h | h | h
    · exact h1 (ho ▸ h)
    · exact h3 (ho ▸ h)
    · exact h5 (ho ▸ h)

theorem exists_bad_of_conj {S : Type} [Group S]
    (hconj : ∀ A B : Subgroup S, Nat.card A = 3 → Nat.card B = 3 →
      ∃ g : S, B.map (MulAut.conj g).toMonoidHom = A)
    {D₀ D₁ : Subgroup S} (hD₀ : Nat.card D₀ = 3) (hD₁ : Nat.card D₁ = 3)
    (hbad : ¬ Z3E9A5Mod2 (D₀ ⊔ D₁)) (D : Subgroup S) (hD : Nat.card D = 3) :
    ∃ g : S, ¬ Z3E9A5Mod2 (D ⊔ D.map (MulAut.conj g).toMonoidHom) := by
  obtain ⟨h, hh⟩ := hconj D D₀ hD hD₀
  obtain ⟨k, hk⟩ := hconj D D₁ hD hD₁
  refine ⟨h * k⁻¹, fun hZ => hbad ?_⟩
  have hcomp : (MulAut.conj (h * k⁻¹)).toMonoidHom.comp (MulAut.conj k).toMonoidHom =
      (MulAut.conj h).toMonoidHom := by
    ext x
    simp [MulAut.conj_apply, mul_assoc]
  have hmap : (D₀ ⊔ D₁).map (MulAut.conj h).toMonoidHom =
      D ⊔ D.map (MulAut.conj (h * k⁻¹)).toMonoidHom := by
    rw [Subgroup.map_sup, hh, ← hcomp, ← Subgroup.map_map, hk]
  exact UC46.z3E9A5Mod2_of_map (MulAut.conj h).toMonoidHom (MulAut.conj h).injective _
    (hmap ▸ hZ)

theorem bad_pair_of_mulEquiv {S P : Type} [Group S] [Group P] (e : S ≃* P) {D₀ D₁ : Subgroup P}
    (hbad : ¬ Z3E9A5Mod2 (D₀ ⊔ D₁)) :
    ¬ Z3E9A5Mod2 (D₀.map e.symm.toMonoidHom ⊔ D₁.map e.symm.toMonoidHom) := by
  intro h
  rw [← Subgroup.map_sup] at h
  exact hbad (UC46.z3E9A5Mod2_of_map e.symm.toMonoidHom e.symm.injective _ h)

theorem exists_bad_of_normalizes {S : Type} [Group S] [Finite S] {D R : Subgroup S} {ℓ : ℕ}
    (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) (hℓ3 : ℓ ≠ 3) (hD : Nat.card D = 3) (hR : IsPGroup ℓ R)
    (hDR : D ≤ normalizer (R : Set S)) (hc : ⁅D, R⁆ ≠ ⊥) :
    ∃ g : S, ¬ Z3E9A5Mod2 (D ⊔ D.map (MulAut.conj g).toMonoidHom) := by
  obtain ⟨g, h1, h2, h3⟩ := exists_pair_card_odd hℓ hℓ2 hℓ3 hD hR hDR hc
  exact ⟨g, not_z3E9A5Mod2_of_odd_card h1 h2 h3⟩

theorem bad_pair_of_prod {P : Type} [Group P] [Finite P] {x y : P} (hx : orderOf x = 3)
    (hy : orderOf y = 3) (hodd : Odd (orderOf (x * y))) (h1 : orderOf (x * y) ≠ 1)
    (h3 : orderOf (x * y) ≠ 3) (h5 : orderOf (x * y) ≠ 5) (h9 : orderOf (x * y) ≠ 9) :
    ∃ D₀ D₁ : Subgroup P, Nat.card D₀ = 3 ∧ Nat.card D₁ = 3 ∧ ¬ Z3E9A5Mod2 (D₀ ⊔ D₁) := by
  refine ⟨Subgroup.zpowers x, Subgroup.zpowers y, by rw [Nat.card_zpowers, hx],
    by rw [Nat.card_zpowers, hy], ?_⟩
  exact not_z3E9A5Mod2_of_odd_orderOf
    (Subgroup.mul_mem_sup (Subgroup.mem_zpowers x) (Subgroup.mem_zpowers y)) hodd h1 h3 h5 h9

theorem exists_bad_of_rank_one {S : Type} [Group S] [Finite S]
    (hrk : CFSG.Open.pRank 3 (⊤ : Subgroup S) ≤ 1)
    (hbad : ∃ D₀ D₁ : Subgroup S, Nat.card D₀ = 3 ∧ Nat.card D₁ = 3 ∧ ¬ Z3E9A5Mod2 (D₀ ⊔ D₁))
    (D : Subgroup S) (hD : Nat.card D = 3) :
    ∃ g : S, ¬ Z3E9A5Mod2 (D ⊔ D.map (MulAut.conj g).toMonoidHom) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨D₀, D₁, h0, h1, hb⟩ := hbad
  refine exists_bad_of_conj (fun A B hA hB => ?_) h0 h1 hb D hD
  exact CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound.OvergroupConj.exists_conj_eq_of_card_three
    (fun X hX => CFSG.RankThree.PartTwo.Sec4.RonanK432.Helpers.isCyclic_of_pRank_le_one hrk hX)
    hA hB

end CFSG.LocalAnalysis.UniquenessCase.UCK.InspPS
