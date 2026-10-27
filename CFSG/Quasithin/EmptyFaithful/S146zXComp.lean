module

public import CFSG.Quasithin.EmptyFaithful.Der6DAux

public section

namespace CFSG.Quasithin.S146zX

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

theorem conjClosure_eq_of_invariant' {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {Mc K L P : Subgroup G}
    (hLc : L ∈ cComp Mc) (hLn : Mc ≤ Subgroup.normalizer (L : Set G)) (hKL : K ≤ L)
    (hq : CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L))
    (hZ : Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L) = ⊥) (hPK : P ≤ K) (hPp : IsPGroup p P)
    (hPne : P ≠ ⊥) : conjClosure K Mc = L := by
  have hLMc : L ≤ Mc := le_of_mem_cComp hLc
  have hle : conjClosure K Mc ≤ L := conjClosure_le fun g hg k hk =>
    (Subgroup.mem_normalizer_iff.mp (hLn hg) k).mp (hKL hk)
  refine Der6D.eq_of_normal_of_not_le_pCoreOf (perfect_of_mem_cComp hLc) hq hZ hle
    (fun l hl n hn =>
      (Subgroup.mem_normalizer_iff.mp (le_normalizer_conjClosure K Mc (hLMc hl)) n).mp hn) ?_
  intro hQ
  obtain ⟨y, hy1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hPne
  have hyL : (y : G) ∈ pCoreOf 2 L := hQ (le_conjClosure K Mc (hPK y.2))
  have hdis := IsPGroup.disjoint_of_ne p 2 hp2 P (pCoreOf 2 L) hPp (pCoreOf_isPGroup 2 L)
  have hy : (y : G) ∈ P ⊓ pCoreOf 2 L := ⟨y.2, hyL⟩
  rw [hdis.eq_bot, Subgroup.mem_bot] at hy
  exact hy1 (Subtype.ext hy)

theorem conjClosure_eq_sup_of_pair' {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    {Mc T K L P : Subgroup G} {t' : G}
    (hLc : L ∈ cComp Mc) (hTMc : T ≤ Mc) (ht'T : t' ∈ T)
    (hY : conjClosure L Mc = L ⊔ conjByElt t' L) (hKY : K ≤ conjClosure L T)
    (hq : CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L))
    (hZ : Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L) = ⊥) (hPK : P ≤ K) (hPp : IsPGroup p P)
    (hPL : P ⊓ L ≠ ⊥) : conjClosure K Mc = L ⊔ conjByElt t' L := by
  have hLMc : L ≤ Mc := le_of_mem_cComp hLc
  have hKY' : K ≤ conjClosure L Mc := hKY.trans (conjClosure_mono le_rfl hTMc)
  have hLK : L ≤ conjClosure K Mc := by
    have h := Der6D.eq_of_normal_of_not_le_pCoreOf (perfect_of_mem_cComp hLc) hq hZ
      (inf_le_left : L ⊓ conjClosure K Mc ≤ L)
      (fun l hl n hn => ⟨L.mul_mem (L.mul_mem hl hn.1) (L.inv_mem hl),
        (Subgroup.mem_normalizer_iff.mp (le_normalizer_conjClosure K Mc (hLMc hl)) n).mp hn.2⟩)
      (by
        intro hQ
        obtain ⟨y, hy1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hPL
        have hyL : (y : G) ∈ pCoreOf 2 L := hQ ⟨y.2.2, le_conjClosure K Mc (hPK y.2.1)⟩
        have hdis := IsPGroup.disjoint_of_ne p 2 hp2 P (pCoreOf 2 L) hPp
          (pCoreOf_isPGroup 2 L)
        have hy : (y : G) ∈ P ⊓ pCoreOf 2 L := ⟨y.2.1, hyL⟩
        rw [hdis.eq_bot, Subgroup.mem_bot] at hy
        exact hy1 (Subtype.ext hy))
    exact inf_eq_left.mp h
  refine le_antisymm (conjClosure_le fun g hg k hk => ?_) (sup_le hLK ?_)
  · rw [← hY]
    exact (Subgroup.mem_normalizer_iff.mp (le_normalizer_conjClosure L Mc hg) k).mp (hKY' hk)
  · rintro _ ⟨z, hz, rfl⟩
    exact (Subgroup.mem_normalizer_iff.mp (le_normalizer_conjClosure K Mc (hTMc ht'T)) z).mp
      (hLK hz)

theorem dvd_card_kbar_of_inf_ne_bot {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {L P : Subgroup G}
    (hPp : IsPGroup p P) (hPL : P ⊓ L ≠ ⊥) : p ∣ Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hN : IsPGroup p ↥(P ⊓ L) := hPp.to_le inf_le_left
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card).1 hN
  have hn0 : n ≠ 0 := by
    rintro rfl
    apply hPL
    rw [pow_zero, Subgroup.card_eq_one] at hn
    exact hn
  have h1 : p ∣ Nat.card ↥(P ⊓ L) := by
    rw [hn]
    exact dvd_pow_self p hn0
  have h2 : p ∣ Nat.card ↥L := h1.trans (Subgroup.card_dvd_of_le inf_le_right)
  have h3 := Subgroup.card_eq_card_quotient_mul_card_subgroup (CFSG.pCore 2 ↥L)
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card).1 (CFSG.pCore_isPGroup (p := 2) (G := ↥L))
  rw [h3, hk] at h2
  have hcop : Nat.Coprime p (2 ^ k) :=
    Nat.Coprime.pow_right k ((Nat.coprime_primes (Fact.out) Nat.prime_two).mpr hp2)
  exact hcop.dvd_of_dvd_mul_right h2

end CFSG.Quasithin.S146zX
