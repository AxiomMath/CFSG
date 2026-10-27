module

public import CFSG.Quasithin.Background.B1MoreElevenA
public import CFSG.Quasithin.Background.A1cModuleDefs
public import CFSG.LocalAnalysis.ComponentClassification.Quasisimple

public section

namespace CFSG.Quasithin

open CFSG.Open

section Schur

variable {R : Type} [CommGroup R]

theorem suzb4_invol_eq_one (hexp : ∀ r : R, r ^ 2 = 1) {L : Subgroup (MulAut R)}
    (hirr : XMod.IsIrrSec ↥L (⊥ : Subgroup R) ⊤) {q : MulAut R} (hq2 : q ^ 2 = 1)
    (hc : ∀ l ∈ L, q * l = l * q) : q = 1 := by
  have hqq : ∀ r : R, q (q r) = r := by
    intro r
    have h := congrArg (fun φ : MulAut R => φ r) hq2
    simpa [pow_two] using h
  let K : Subgroup R :=
    { carrier := {r | q r = r}
      one_mem' := map_one q
      mul_mem' := fun {a b} ha hb => by
        show q (a * b) = a * b
        rw [map_mul, show q a = a from ha, show q b = b from hb]
      inv_mem' := fun {a} ha => by
        show q a⁻¹ = a⁻¹
        rw [map_inv, show q a = a from ha] }
  have hKinv : XMod.IsInv ↥L K := by
    intro a r hr
    have hr' : q r = r := hr
    show q ((a : MulAut R) r) = (a : MulAut R) r
    have h1 : q ((a : MulAut R) r) = (a : MulAut R) (q r) :=
      congrArg (fun φ : MulAut R => φ r) (hc a a.2)
    rw [h1, hr']
  rcases hirr.2 K hKinv bot_le le_top with hK | hK
  · exfalso
    have hall : ∀ r : R, r = 1 := by
      intro r
      have h1 : r * q r ∈ K := by
        show q (r * q r) = r * q r
        rw [map_mul, hqq, mul_comm]
      rw [hK] at h1
      have h2 : r * q r = 1 := h1
      have h3 : q r = r := by
        have h4 : q r = r⁻¹ := by
          rw [eq_inv_iff_mul_eq_one, mul_comm]; exact h2
        rw [h4, inv_eq_iff_mul_eq_one, ← pow_two]; exact hexp r
      have h5 : r ∈ K := h3
      rw [hK] at h5
      exact h5
    obtain ⟨r, -, hr⟩ := IsConcreteLE.exists_of_lt hirr.1
    exact hr (hall r)
  · refine MulEquiv.ext fun r => ?_
    have : r ∈ K := by rw [hK]; trivial
    exact this

end Schur

section Abstract

variable {Ω : Type*} [Group Ω] [Finite Ω]

theorem suzb4_pCoreOf_eq_bot {L Y : Subgroup Ω} (hLY : L ≤ Y) (hq : CFSG.Open.IsQuasisimple ↥L)
    (hn : ∀ y ∈ Y, ∀ l ∈ L, y * l * y⁻¹ ∈ L)
    (hd : ∀ x ∈ Y, x ^ 2 = 1 → (∀ l ∈ L, x * l = l * x) → x = 1) : pCoreOf 2 Y = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set N := pCoreOf 2 Y with hNdef
  have hN2 : IsPGroup 2 ↥N := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 Y
  have hNY : N ≤ Y := CFSG.LieType.BorelTits.pCoreOf_le 2 Y
  have hNn : ∀ y ∈ Y, ∀ n ∈ N, y * n * y⁻¹ ∈ N := fun y hy n hn =>
    (Subgroup.mem_normalizer_iff.mp (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 Y hy) n).mp hn
  have hLn : ∀ l ∈ L, ∀ n ∈ N, l * n * l⁻¹ ∈ N := fun l hl n hn => hNn l (hLY hl) n hn
  have hnotle : ¬ L ≤ N := by
    intro hLN
    have hnt : Nontrivial ↥L := CFSG.ComponentClassification.Quasisimple.nontrivial hq
    have hperf : Group.IsPerfect ↥L := ⟨hq.1⟩
    exact Group.IsPerfect.not_isNilpotent ↥L (hN2.to_le hLN).isNilpotent
  have hcomm : ∀ n ∈ N, ∀ l ∈ L, n * l = l * n :=
    B1Red.commute_of_normal_not_le hq (fun n hn' l hl => hn n (hNY hn') l hl) hLn hnotle
  by_contra hne
  have hne' : Nat.card ↥N ≠ 1 := fun h => hne (Subgroup.card_eq_one.1 h)
  have hdvd : 2 ∣ Nat.card ↥N := by
    rcases hN2.card_eq_or_dvd with h | h
    · exact absurd h hne'
    · exact h
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' 2 hdvd
  have hy2 : y ^ 2 = 1 := by rw [← hy]; exact pow_orderOf_eq_one y
  have hy1 : y ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hy
    exact absurd hy (by norm_num)
  have hyN : (y : Ω) ∈ N := y.2
  have := hd (y : Ω) (hNY hyN) (by rw [← Subgroup.coe_pow, hy2]; rfl) (hcomm _ hyN)
  exact hy1 (Subtype.ext this)

end Abstract

end CFSG.Quasithin
