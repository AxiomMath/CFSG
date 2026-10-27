module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.H13.L32ACSkPfB

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open Subgroup
open CFSG.QuasithinUnique (IsSylowTwoOf)

structure TorusFacts218 (Y : Type) [Group Y] [Finite Y] (n : ℕ) (Tor Out : ℕ → Prop) : Prop where
  tor_of_dvd : ∀ {s r : ℕ}, Odd s → s ∣ n → r.Prime → r ∣ 2 ^ s - 1 → Tor r
  pRank_eq_two : ∀ {s r : ℕ}, Odd s → s ∣ n → r.Prime → r ∣ 2 ^ s - 1 →
    CFSG.Open.pRank r (⊤ : Subgroup Y) = 2
  not_dvd_card_sylow : ∀ {s r : ℕ}, Odd s → s ∣ n → r.Prime → r ∣ 2 ^ s - 1 →
    ¬ r ∣ Nat.card (Sylow 2 Y)
  pow_action : ∀ {U : Subgroup Y}, IsSylowTwoOf U ⊤ → ∀ {α : MulAut Y},
    U.map α.toMonoidHom = U → ∀ {m : ℕ}, Odd m → α ^ m = 1 →
      ∃ k : ℕ, ∀ b ∈ normalizer (U : Set Y), α b * (b ^ k)⁻¹ ∈ U
  exists_mem_centMod : ∀ {s : ℕ} {U : Subgroup Y}, IsSylowTwoOf U ⊤ → Odd s → s ∣ n →
    ∃ d : Y, orderOf d = 2 ^ s - 1 ∧ ∀ α : MulAut Y, (∃ e : ℕ, α ^ 2 ^ e = 1) →
      U.map α.toMonoidHom = U → d ∈ CFSG.Quasithin.H13.L32A.C.SkPf.centMod U α
  exists_pair : ∀ {s r p : ℕ}, Odd s → s ∣ n → r.Prime → r ∣ 2 ^ s - 1 → p.Prime → Tor p →
    p ≠ r → ∃ E Q : Subgroup Y, IsElemAbelian r E ∧ Nat.card E = r ^ 2 ∧ IsElemAbelian p Q ∧
      Nat.card Q = p ^ 2 ∧ ∀ x ∈ Q, ∃ k : ℕ, ∀ e ∈ E, x * e * x⁻¹ = e ^ k
  eq_one_of_pow_eq_one : ∀ {p : ℕ}, p.Prime → p ≠ 2 → Out p → ∀ {U : Subgroup Y},
    IsSylowTwoOf U ⊤ → ∀ {b : Y}, b ∈ normalizer (U : Set Y) → b ^ p = 1 → b = 1
  pRank_le_two : ∀ {p : ℕ}, p.Prime → p ≠ 2 → Out p → CFSG.Open.pRank p (⊤ : Subgroup Y) ≤ 2

end CFSG.LocalAnalysis.UniquenessCase.UC22
