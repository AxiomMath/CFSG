module

public import CFSG.RankThree.PartOne.KE.CTMain
public import CFSG.RankThree.PartOne.KE.CTConclusion
public import CFSG.RankThree.PartOne.KE.CTCasesE7Sev
public import CFSG.RankThree.PartOne.KE.CTCasesF4
public import CFSG.RankThree.PartOne.KE.NativeCyclicFamilies
public import CFSG.RankThree.PartOne.KE.NativeCyclicF4
public import CFSG.RankThree.PartOne.KE.CTCasesE8Coxeter
public import CFSG.RankThree.PartOne.KE.CTCasesE8Explicit

public section

namespace CFSG.RankThree.PartOne.KE

open CFSG CFSG.Blueprint.Chevalley
open CFSG.RankThree.Chevalley (exhaustionPhi)

theorem oddEndpoint_E7_phi7Phi14 : OddEndpoint .E7 fun p ℓ f =>
    7 < p ∧ ((p : ℤ) ∣ cycloVal 7 ℓ f ∨ (p : ℤ) ∣ cycloVal 14 ℓ f) :=
  oddEndpoint_E7_of_cyclic fun K _ _ p ℓ f hp _ _ _ _ hK hc => by
    obtain ⟨hp7, hc | hc⟩ := hc
    · have hpf : (p : ℤ) ∣ (exhaustionPhi 7).eval (Nat.card K : ℤ) := by
        rw [hK]
        exact hc
      have h := (E7_seven_cyclic_sylow cyclic_torus_prime_centralizers K hp hp7 hpf).2
      exact ⟨CyclicSylowConclusion'.pgroups_cyclic h, CyclicSylowConclusion'.centralizer_cyclic h⟩
    · have hpf : (p : ℤ) ∣ (exhaustionPhi 14).eval (Nat.card K : ℤ) := by
        rw [hK]
        exact hc
      have h := (E7_fourteen_cyclic_sylow cyclic_torus_prime_centralizers K hp hp7 hpf).2
      exact ⟨CyclicSylowConclusion'.pgroups_cyclic h, CyclicSylowConclusion'.centralizer_cyclic h⟩

theorem oddEndpoint_E8_phi15Phi30 : OddEndpoint .E8 fun p ℓ f =>
    (p : ℤ) ∣ cycloVal 15 ℓ f ∨ (p : ℤ) ∣ cycloVal 30 ℓ f :=
  oddEndpoint_E8_of_cyclic fun K _ _ p ℓ f hp hp3 _ _ _ hK hc => by
    rcases hc with hc | hc
    · have hpf : (p : ℤ) ∣ (exhaustionPhi 15).eval (Nat.card K : ℤ) := by
        rw [hK]
        exact hc
      have h := (E8_fifteen_cyclic_sylow cyclic_torus_prime_centralizers K hp hp3 hpf).2.2
      exact ⟨CyclicSylowConclusion'.pgroups_cyclic h, CyclicSylowConclusion'.centralizer_cyclic h⟩
    · have hpf : (p : ℤ) ∣ (exhaustionPhi 30).eval (Nat.card K : ℤ) := by
        rw [hK]
        exact hc
      have h := (E8_thirty_cyclic_sylow cyclic_torus_prime_centralizers K hp hp3 hpf).2.2
      exact ⟨CyclicSylowConclusion'.pgroups_cyclic h, CyclicSylowConclusion'.centralizer_cyclic h⟩

theorem oddEndpoint_E8_phi20Phi24 : OddEndpoint .E8 fun p ℓ f =>
    (p : ℤ) ∣ cycloVal 24 ℓ f ∨ (5 < p ∧ (p : ℤ) ∣ cycloVal 20 ℓ f) :=
  oddEndpoint_E8_of_cyclic fun K _ _ p ℓ f hp hp3 _ _ _ hK hc => by
    rcases hc with hc | ⟨hp5, hc⟩
    · have hpf : (p : ℤ) ∣ (exhaustionPhi 24).eval (Nat.card K : ℤ) := by
        rw [hK]
        exact hc
      have h := (E8_twentyfour_cyclic_sylow cyclic_torus_prime_centralizers K hp hp3 hpf).2.2
      exact ⟨CyclicSylowConclusion'.pgroups_cyclic h, CyclicSylowConclusion'.centralizer_cyclic h⟩
    · have hpf : (p : ℤ) ∣ (exhaustionPhi 20).eval (Nat.card K : ℤ) := by
        rw [hK]
        exact hc
      have h := (E8_twenty_cyclic_sylow cyclic_torus_prime_centralizers K hp hp5 hpf).2.2
      exact ⟨CyclicSylowConclusion'.pgroups_cyclic h, CyclicSylowConclusion'.centralizer_cyclic h⟩

theorem oddEndpoint_F4_phi8Phi12 : OddEndpoint .F4 fun p ℓ f =>
    (p : ℤ) ∣ cycloVal 8 ℓ f ∨ (p : ℤ) ∣ cycloVal 12 ℓ f :=
  oddEndpoint_F4_of_cyclic fun K _ _ p ℓ f hp hp3 _ _ _ hK hc => by
    rcases hc with hc | hc
    · have hpf : (p : ℤ) ∣ (exhaustionPhi 8).eval (Nat.card K : ℤ) := by
        rw [hK]
        exact hc
      have h := (F4_eight_cyclic_sylow cyclic_torus_prime_centralizers_F4 K hp hp3 hpf).2.2
      exact ⟨CyclicSylowConclusion'.pgroups_cyclic h, CyclicSylowConclusion'.centralizer_cyclic h⟩
    · have hpf : (p : ℤ) ∣ (exhaustionPhi 12).eval (Nat.card K : ℤ) := by
        rw [hK]
        exact hc
      have h := (F4_twelve_cyclic_sylow cyclic_torus_prime_centralizers_F4 K hp hp3 hpf).2.2
      exact ⟨CyclicSylowConclusion'.pgroups_cyclic h, CyclicSylowConclusion'.centralizer_cyclic h⟩

end CFSG.RankThree.PartOne.KE
