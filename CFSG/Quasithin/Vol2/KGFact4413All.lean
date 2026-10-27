module

public import CFSG.Quasithin.Vol2.KGFact4413L3K3
public import CFSG.Quasithin.Vol2.KGFact4413Borel
public import CFSG.Quasithin.Vol2.KGFact4413Bridge
public import CFSG.Quasithin.Vol2.KGFact4413Sp
public import CFSG.Quasithin.Vol2.KGFact4413U3

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin
open scoped Pointwise

namespace Ch4

theorem lemma4413NALie_holds : Lemma4413NALie := by
  intro G _ _ H S MH hs hnab hK hO hL hS hU B hBM hBo hBi p A hp hAB hAel hAS
  have hMH : MH ≤ H := (isUniqueMaxOver_iff.mp hU).1.le
  by_cases hp2 : p = 2
  ·
    subst hp2
    have hA1 : A = ⊥ := by
      rw [eq_bot_iff]
      intro a ha
      have ho : Odd (orderOf a) := by
        have h1 := orderOf_dvd_natCard (⟨a, hAB ha⟩ : B)
        rw [Subgroup.orderOf_mk] at h1
        exact hBo.of_dvd_nat h1
      have h2 : orderOf a ∣ 2 := orderOf_dvd_of_pow_eq_one (hAel.2 a ha)
      rcases (Nat.dvd_prime Nat.prime_two).mp h2 with h | h
      · exact Subgroup.mem_bot.mpr (orderOf_eq_one_iff.mp h)
      · rw [h] at ho
        exact absurd ho (by decide)
    rw [hA1]
    intro hle
    apply (isUniqueMaxOver_iff.mp hU).1.1.ne
    apply le_antisymm hMH
    intro h hh
    refine hle ⟨hh, A4.mem_normalizer_of_conj_mem fun x hx => ?_⟩
    rw [Subgroup.mem_bot] at hx ⊢
    rw [hx, mul_one, mul_inv_cancel]
  obtain ⟨K, hKc, hHK, hLc⟩ := hL
  have hmin : MinParabolic H S MH := KG4413.minParabolic_of_cComp hS hU hKc
  have hA : ∀ a ∈ A, a ^ p = 1 := hAel.2
  have hTor : E2.E22TorusCover := E2.e22TorusCover_of_facts e22TorusFacts_holds
  dsimp only [E2.E22LieCases] at hLc
  rcases hLc with ⟨hJ, t, ht, -, hMeq, n, hn, hty, hB⟩ |
      ⟨hTK, hJ, ⟨n, hBen, hB⟩ | ⟨n, hn, hty, hDg, hB⟩⟩
  · exact KG4413.not_le_of_case_one hmin hKc hHK hJ ht hMeq hn hty hB hBM hBo hAB
  · obtain ⟨-, R, hRS, -, hMR, -, hall⟩ :=
      E2.BorelLift.lift_two hTor hmin hKc hHK hTK hJ hBen.1 (Or.inl hBen) hB
    obtain ⟨-, hBR, hBab, -⟩ := hall B hBM hBo hBi
    have hW : KG4413.CartanWeyl ↥(E2.star MH H K) n := by
      rcases hBen.2 with h | h | h
      · exact KG4413.cartanWeyl_of_isPSL2 (by have := hBen.1; omega) h
      · exact KG4413.cartanWeyl_of_isSz h
      · exact KG4413.cartanWeyl_of_isPSU3 hBen.1 h
    exact KG4413.not_le_of_case_two hmin hKc hHK hTK hJ hB hW hRS hMR hBM hBo hBR hBab hp hp2
      hAB hA
  · obtain ⟨-, R, hRS, -, hMR, -, hall⟩ :=
      E2.BorelLift.lift_two hTor hmin hKc hHK hTK hJ hn (Or.inr hty) hB
    obtain ⟨-, hBR, hBab, -⟩ := hall B hBM hBo hBi
    rcases hty with h | h
    · by_cases hp3 : p = 3
      · subst hp3
        exact KG4413.not_le_of_case_psl3_three hmin hKc hHK hTK hJ hB hn h hDg hRS hMR hBM hBo
          hBR hBab hAB hA hAS
      · have hp3' : 3 < p := by
          have h2 := hp.two_le
          omega
        exact KG4413.not_le_of_case_psl3 hmin hKc hHK hTK hJ hB h hDg hRS hMR hBM hBo hBR hBab hp
          hp3' hAB hA hAS
    · exact KG4413.not_le_of_case_two hmin hKc hHK hTK hJ hB
        (KG4413.cartanWeyl_of_isPSp4 (by omega) h) hRS hMR hBM hBo hBR hBab hp hp2 hAB hA

end Ch4

open Ch4 in
theorem stmt4_4_13Lie_holds : Stmt4_4_13Lie :=
  stmt4_4_13Lie_of e22BorelFactsLie_holds lemma4413NALie_holds

theorem stmt4_4_13_of (hC : E2.E22StatementC) : Stmt4_4_13 :=
  stmt4_4_13_of_lie hC stmt4_4_13Lie_holds

end CFSG.Quasithin.H13
