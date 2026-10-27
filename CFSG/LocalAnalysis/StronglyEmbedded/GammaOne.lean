module

public import CFSG.LocalAnalysis.StronglyEmbedded.WeaklyClosed
import CFSG.GroupTheory.ElemAbelianClosure
import CFSG.HardMathSupport.Solomon.Proving.GLBCoreNormalizer
public import CFSG.LocalAnalysis.SectionRank.PRank

public section

namespace CFSG.RankThree.PartOne

open Subgroup
open CFSG.Open

variable {G : Type} [Group G] [Finite G]

private theorem one_le_pRank_zpowers_of_prime_order {q : ℕ} [Fact q.Prime] {a : G}
    (haq : a ^ q = 1) (ha1 : a ≠ 1) :
    1 ≤ CFSG.Open.pRank q (Subgroup.zpowers a) := by
  have hel : CFSG.Open.IsElemAbelian q (Subgroup.zpowers a) :=
    CFSG.Open.isElemAbelian_zpowers haq
  have hcard : Nat.card (Subgroup.zpowers a) = q ^ 1 := by
    rw [Nat.card_zpowers, orderOf_eq_prime haq ha1, pow_one]
  exact CFSG.SectionRank.le_pRank (Fact.out : q.Prime).one_lt le_rfl hel hcard

theorem centralizer_le_of_rankThreeGamma_le {q : ℕ} [Fact q.Prime] {A M : Subgroup G}
    (h : CFSG.Open.rankThreeGamma 1 q A ≤ M) {a : G} (ha : a ∈ A) (hao : orderOf a = q) :
    Subgroup.centralizer ({a} : Set G) ≤ M := by
  have haq : a ^ q = 1 := by
    rw [← hao]
    exact pow_orderOf_eq_one a
  have ha1 : a ≠ 1 := by
    rintro rfl
    have hq := (Fact.out : q.Prime).one_lt
    simp only [orderOf_one] at hao
    omega
  have hzA : Subgroup.zpowers a ≤ A := Subgroup.zpowers_le.mpr ha
  have hN : Subgroup.normalizer ((Subgroup.zpowers a : Subgroup G) : Set G) ≤
      CFSG.Open.rankThreeGamma 1 q A :=
    CFSG.HardMathSupport.Solomon.Proving.normalizer_le_glbCore hzA
      (one_le_pRank_zpowers_of_prime_order haq ha1)
  have hcent : Subgroup.centralizer ({a} : Set G) =
      Subgroup.centralizer ((Subgroup.zpowers a : Subgroup G) : Set G) := by
    rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
  rw [hcent]
  exact (Subgroup.centralizer_le_normalizer _).trans (hN.trans h)

theorem IsStronglyPEmbedded.rankThreeGamma_one_le {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    {M A : Subgroup G} (hM : IsStronglyPEmbedded p M) (hA : IsPGroup q A)
    (hX : ∀ X : Subgroup G, X ≤ A → Nat.card X = q →
      Subgroup.normalizer (X : Set G) ≤ M ∧ p ∣ Nat.card (Subgroup.normalizer (X : Set G))) :
    CFSG.Open.rankThreeGamma 1 q A ≤ M := by
  classical
  refine CFSG.HardMathSupport.Solomon.Proving.GLBCore_le_of_forall ?_
  intro B hBA hB
  have hqB : q ∣ Nat.card B := by
    obtain ⟨E, hEB, -, hEcard⟩ :=
      CFSG.SectionRank.exists_pRank (p := q) (Fact.out : q.Prime).one_lt B
    have hqE : q ∣ Nat.card E := by
      rw [hEcard]
      exact dvd_pow_self q (by omega)
    exact hqE.trans (Subgroup.card_dvd_of_le hEB)
  obtain ⟨x, hxord⟩ := exists_prime_orderOf_dvd_card' (G := ↥B) q hqB
  let X : Subgroup G := Subgroup.zpowers (x : G)
  have hXB : X ≤ B := Subgroup.zpowers_le.mpr x.2
  have hXcard : Nat.card X = q := by
    show Nat.card (Subgroup.zpowers (x : G)) = q
    rw [Nat.card_zpowers, Subgroup.orderOf_coe, hxord]
  have hXA : X ≤ A := hXB.trans hBA
  obtain ⟨hNX, hpNX⟩ := hX X hXA hXcard
  intro n hn
  by_contra hnM
  have hnB : B.map (MulAut.conj n).toMonoidHom = B :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp hn
  let X' : Subgroup G := X.map (MulAut.conj n).toMonoidHom
  have hX'B : X' ≤ B := by
    show X.map (MulAut.conj n).toMonoidHom ≤ B
    calc X.map (MulAut.conj n).toMonoidHom ≤ B.map (MulAut.conj n).toMonoidHom :=
          Subgroup.map_mono hXB
      _ = B := hnB
  have hX'card : Nat.card X' = q := by
    show Nat.card (X.map (MulAut.conj n).toMonoidHom) = q
    rw [Subgroup.card_map_of_injective (MulAut.conj n).injective, hXcard]
  obtain ⟨hNX', hpNX'⟩ := hX X' (hX'B.trans hBA) hX'card
  have hmapN : (Subgroup.normalizer (X : Set G)).map (MulAut.conj n).toMonoidHom =
      Subgroup.normalizer (X' : Set G) := by
    simpa [X'] using Subgroup.map_equiv_normalizer_eq X (MulAut.conj n)
  have hle : Subgroup.normalizer (X' : Set G) ≤
      M ⊓ M.map (MulAut.conj n).toMonoidHom := by
    refine le_inf hNX' ?_
    rw [← hmapN]
    exact Subgroup.map_mono hNX
  exact hM.2.2 n hnM (hpNX'.trans (Subgroup.card_dvd_of_le hle))

theorem map_conj_eq_of_forall_isElemAbelian_eq {q : ℕ} {P A : Subgroup G}
    (hA : CFSG.Open.IsElemAbelian q A)
    (huniq : ∀ B : Subgroup G, B ≤ P → CFSG.Open.IsElemAbelian q B →
      Nat.card B = Nat.card A → B = A)
    (g : G) (hg : A.map (MulAut.conj g).toMonoidHom ≤ P) :
    A.map (MulAut.conj g).toMonoidHom = A :=
  huniq _ hg (CFSG.Open.IsElemAbelian.map hA (MulAut.conj g).toMonoidHom)
    (Subgroup.card_map_of_injective (MulAut.conj g).injective)

theorem isStronglyPEmbedded_of_rankThreeGamma_le {q : ℕ} [Fact q.Prime] {M P A : Subgroup G}
    (hM : M ≠ ⊤) (hPM : CFSG.ABGLocalTools.IsSylowOf q P M) (hAP : A ≤ P)
    (hA : CFSG.Open.IsElemAbelian q A) (hA1 : A ≠ ⊥)
    (huniq : ∀ B : Subgroup G, B ≤ P → CFSG.Open.IsElemAbelian q B →
      Nat.card B = Nat.card A → B = A)
    (hcover : ∀ x ∈ M, orderOf x = q → ∃ m ∈ M, m * x * m⁻¹ ∈ A)
    (hΓ : CFSG.Open.rankThreeGamma 1 q A ≤ M) :
    IsStronglyPEmbedded q M := by
  have hAr : 1 ≤ CFSG.Open.pRank q A := by
    obtain ⟨a, ha1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hA1
    have haA : (a : G) ∈ A := a.2
    have haq : (a : G) ^ q = 1 := hA.2 _ haA
    have ha1' : (a : G) ≠ 1 := fun h => ha1 (Subtype.ext h)
    have hzA : Subgroup.zpowers (a : G) ≤ A := Subgroup.zpowers_le.mpr haA
    exact CFSG.SectionRank.le_pRank (p := q) (Fact.out : q.Prime).one_lt hzA
      (CFSG.Open.isElemAbelian_zpowers haq)
      (by rw [Nat.card_zpowers, orderOf_eq_prime haq ha1', pow_one])
  have hN : Subgroup.normalizer (A : Set G) ≤ M :=
    (CFSG.HardMathSupport.Solomon.Proving.normalizer_le_glbCore (le_refl A) hAr).trans hΓ
  exact CFSG.LocalAnalysis.StronglyEmbedded.isStronglyPEmbedded_of_weaklyClosed hM hPM hAP
    hA1 (fun a ha b hb => CFSG.Open.IsElemAbelian.comm hA ha hb)
    (fun g hg => map_conj_eq_of_forall_isElemAbelian_eq hA huniq g hg)
    hcover
    (fun a ha hao => centralizer_le_of_rankThreeGamma_le hΓ ha hao)
    hN

end CFSG.RankThree.PartOne
