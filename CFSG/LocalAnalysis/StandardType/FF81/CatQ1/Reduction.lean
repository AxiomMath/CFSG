module

public import CFSG.LocalAnalysis.StandardType.FF81.CatalogueQ1Defs
public import CFSG.LocalAnalysis.StandardType.FF81.CatQ1.Defs
public import CFSG.LocalAnalysis.StandardType.FF81.CatQ1.Product
public import CFSG.LocalAnalysis.StandardType.FF81.CatQ1.InnerCase
public import CFSG.LocalAnalysis.StandardType.FF81.CatQ1.TrivialCase
public import CFSG.LocalAnalysis.StandardType.FF81.CatQ1.NonLie
public import CFSG.LocalAnalysis.StandardType.FF81.CatQ1.Transport

public section

namespace CFSG.StandardType.FF81.CatQ1

open CFSG.Assembly CFSG.Open CFSG.HardMathSupport.Timmesfeld.Coordinator

theorem catalogueQ1_of_clauses (hsp : SporadicOuterLeTwo)
    (hLie : OuterThreeBigAt (fun _ => True)) : CFSG.StandardType.FF81.CatalogueQ1 := by
  unfold CFSG.StandardType.FF81.CatalogueQ1
  intro K _ _ _ hnab hcat h4 β hβ O J hfix hdisj hcomm hO hJ
  rcases hcat with ⟨i, ⟨e⟩⟩
  by_cases hinner : ∃ k : K, β = MulAut.conj k
  · obtain ⟨k, rfl⟩ := hinner
    by_cases hk : k = 1
    · subst hk
      exact false_of_one_of_product h4 O J (by simpa using hfix) hcomm hJ
    · exact false_of_conj_of_product hnab k hk hβ O J hfix hdisj hcomm hO hJ
  · have hout : ∀ k : K, β ≠ MulAut.conj k := fun k hk => hinner ⟨k, hk⟩
    cases i with
    | cyclic p hp =>
        obtain ⟨x, y, hxy⟩ := hnab
        exact hxy (e.injective (by simp [map_mul, mul_comm]))
    | alternating n hn =>
        obtain ⟨k, hk⟩ := exists_conj_of_alternating hn e β hβ
        exact hout k hk
    | sporadic s =>
        obtain ⟨k, hk⟩ := exists_conj_of_sporadic hsp hnab e β hβ
        exact hout k hk
    | lie d =>
        have hbig : FixedTooBig β := OuterThreeBigAt.of_all hLie K d ⟨e⟩ h4 β hβ hout
        exact not_fixedTooBig_of_product β O J hfix hdisj hcomm hO hJ hbig

end CFSG.StandardType.FF81.CatQ1
