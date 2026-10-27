module

public import CFSG.RankThree.PartOne.KE.CTMain
public import CFSG.RankThree.PartOne.KE.CTConclusion
public import CFSG.RankThree.PartOne.KE.NativeCyclicFamilies
public import CFSG.RankThree.PartOne.KE.CTCasesE6Eight
public import CFSG.RankThree.PartOne.KE.CTCasesE6Nine
public import CFSG.RankThree.PartOne.KE.CTCasesE6Twelve
public import CFSG.RankThree.PartOne.KE.CTCasesE7CoxEighteen
public import CFSG.RankThree.PartOne.KE.CTCasesE7CoxNine

public section

namespace CFSG.RankThree.PartOne.KE

open CFSG CFSG.Blueprint.Chevalley
open CFSG.RankThree.Chevalley (exhaustionPhi)

theorem oddEndpoint_E6_phi8 : OddEndpoint .E6 fun p ℓ f => (p : ℤ) ∣ cycloVal 8 ℓ f :=
  oddEndpoint_E6_of_cyclic fun K _ _ p ℓ f hp hp3 _ _ _ hK hc => by
    have hpf : (p : ℤ) ∣ (exhaustionPhi 8).eval (Nat.card K : ℤ) := by
      rw [hK]
      exact hc
    have h := (E6_eight_cyclic_sylow cyclic_torus_prime_centralizers K hp hp3 hpf).2.2
    exact ⟨CyclicSylowConclusion'.pgroups_cyclic h, CyclicSylowConclusion'.centralizer_cyclic h⟩

theorem oddEndpoint_E6_phi9 : OddEndpoint .E6 fun p ℓ f => (p : ℤ) ∣ cycloVal 9 ℓ f :=
  oddEndpoint_E6_of_cyclic fun K _ _ p ℓ f hp hp3 _ _ _ hK hc => by
    have hpf : (p : ℤ) ∣ (exhaustionPhi 9).eval (Nat.card K : ℤ) := by
      rw [hK]
      exact hc
    have h := (E6_nine_cyclic_sylow cyclic_torus_prime_centralizers K hp hp3 hpf).2.2
    exact ⟨CyclicSylowConclusion'.pgroups_cyclic h, CyclicSylowConclusion'.centralizer_cyclic h⟩

theorem oddEndpoint_E6_phi12 : OddEndpoint .E6 fun p ℓ f => (p : ℤ) ∣ cycloVal 12 ℓ f :=
  oddEndpoint_E6_of_cyclic fun K _ _ p ℓ f hp hp3 _ _ _ hK hc => by
    have hpf : (p : ℤ) ∣ (exhaustionPhi 12).eval (Nat.card K : ℤ) := by
      rw [hK]
      exact hc
    have h := (E6_twelve_cyclic_sylow cyclic_torus_prime_centralizers K hp hp3 hpf).2.2
    exact ⟨CyclicSylowConclusion'.pgroups_cyclic h, CyclicSylowConclusion'.centralizer_cyclic h⟩

theorem oddEndpoint_E7_coxeter :
    OddEndpoint .E7 fun p ℓ f => (p : ℤ) ∣ cycloVal 9 ℓ f ∨ (p : ℤ) ∣ cycloVal 18 ℓ f :=
  oddEndpoint_E7_of_cyclic fun K _ _ p ℓ f hp hp3 _ _ _ hK hc => by
    rcases hc with hc | hc
    · have hpf : (p : ℤ) ∣ (exhaustionPhi 9).eval (Nat.card K : ℤ) := by
        rw [hK]
        exact hc
      have h := (E7_nine_cyclic_sylow cyclic_torus_prime_centralizers K hp hp3 hpf).2.2
      exact ⟨CyclicSylowConclusion'.pgroups_cyclic h, CyclicSylowConclusion'.centralizer_cyclic h⟩
    · have hpf : (p : ℤ) ∣ (exhaustionPhi 18).eval (Nat.card K : ℤ) := by
        rw [hK]
        exact hc
      have h := (E7_eighteen_cyclic_sylow cyclic_torus_prime_centralizers K hp hp3 hpf).2.2
      exact ⟨CyclicSylowConclusion'.pgroups_cyclic h, CyclicSylowConclusion'.centralizer_cyclic h⟩

end CFSG.RankThree.PartOne.KE
