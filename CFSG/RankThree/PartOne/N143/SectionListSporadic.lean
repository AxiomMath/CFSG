module

public import CFSG.RankThree.PartOne.N143.SectionListProof
public import CFSG.RankThree.PartOne.S11d.OutPCyclicThetaClosed
public import CFSG.RankThree.PartOne.S11c.Co1Cover

public section

namespace CFSG.RankThree.PartOne.N143

open CFSG CFSG.Assembly TauCeti Subgroup
open CFSG.Blueprint.NativeSporadic (Carrier)

theorem oddCentralCoverList3For_sporadic :
    OddCentralCoverList3For IsSporadicIndex := by
  intro Y _ _ hK hperf he S _ _ _ hnonab φ hφ hcent h3 h3dvd ⟨i, hi, ⟨e⟩⟩
  cases i with
  | cyclic p hp => exact absurd hi (by simp [IsSporadicIndex])
  | alternating n hn => exact absurd hi (by simp [IsSporadicIndex])
  | lie d => exact absurd hi (by simp [IsSporadicIndex])
  | sporadic s =>
    by_cases hs : s ∈ Census3.sporadicsThm3
    · exact Census3.TheoremThreeList.of_sporadic hs e
    · exfalso
      obtain ⟨c⟩ := TCB.nonempty_carrier_mulEquiv_group s
      let e2 : S ≃* Carrier s := e.trans c.symm
      let ψ : (⊤ : Subgroup Y) →* Carrier s :=
        (e2 : S →* Carrier s).comp (φ.comp (Subgroup.topEquiv : (⊤ : Subgroup Y) ≃* Y).toMonoidHom)
      have hψs : Function.Surjective ψ :=
        e2.surjective.comp (hφ.comp (Subgroup.topEquiv : (⊤ : Subgroup Y) ≃* Y).surjective)
      let iso : ((⊤ : Subgroup Y) ⧸ ψ.ker) ≃* Carrier s :=
        QuotientGroup.quotientKerEquivOfSurjective ψ hψs
      have hoff : s = .Co1 ∨ s = .Fi22 ∨ s = .Fi23 ∨ s = .Fi24Prime ∨ s = .B ∨ s = .M := by
        cases s <;> simp [Census3.sporadicsThm3] at hs ⊢
      have hsec := sporadicSectionCases_closed
      have he' : CFSG.twoLocalOddRank Y ≤ 3 := by
        rw [← CFSG.RankThree.OddKernel.evenRank_eq_twoLocalOddRank]
        exact he
      have he4 : 4 ≤ CFSG.Assembly.evenRank Y → False := fun h => by omega
      rcases hoff with rfl | rfl | rfl | rfl | rfl | rfl
      · have hker : (φ.comp (Subgroup.topEquiv : (⊤ : Subgroup Y) ≃* Y).toMonoidHom).ker ≤
            center (⊤ : Subgroup Y) := by
          intro x hx
          have hx' : (x : Y) ∈ φ.ker := hx
          have := hcent hx'
          rw [Subgroup.mem_center_iff] at this ⊢
          intro g
          exact Subtype.ext (this g)
        have := co1ActualArbitraryCentralCoversForceTwoLocalRankFour Y ⊤ S
          (φ.comp (Subgroup.topEquiv : (⊤ : Subgroup Y) ≃* Y).toMonoidHom)
          (hφ.comp (Subgroup.topEquiv : (⊤ : Subgroup Y) ≃* Y).surjective) ⟨e2⟩ hker
        omega
      · exact he4 (hsec.fi22 Y ⊤ ψ.ker ⟨iso⟩)
      · exact he4 (hsec.fi23 Y ⊤ ψ.ker ⟨iso⟩)
      · exact he4 (hsec.fi24 Y ⊤ ψ.ker ⟨iso⟩)
      · exact he4 (hsec.b Y ⊤ ψ.ker ⟨iso⟩)
      · exact he4 (hsec.m Y ⊤ ψ.ker S hnonab ⟨iso.trans e2.symm⟩ ⟨e2⟩)

end CFSG.RankThree.PartOne.N143
