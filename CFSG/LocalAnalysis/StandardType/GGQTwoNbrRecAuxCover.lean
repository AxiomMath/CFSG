module

public import CFSG.LocalAnalysis.StandardType.GGStdSubSmallRestUnitaryCenter

public section

namespace CFSG.StandardType.QTwo

open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial CFSG.Assembly
open CFSG.StandardType

theorem qTwoNbrRec_hsplit
    {F : Type} [Field F] [Finite F] {n d : ℕ}
    (hK : Nat.card F = (2 ^ n) ^ 2) (hn : 1 ≤ n) (hd : 3 ≤ d) (hdq : (d, 2 ^ n) ≠ (3, 2)) :
    ∀ (E : Type) [Group E] [Finite E] (π : E →* LargeEvenSUGroup (Fin d) F (2 ^ n)),
      Function.Surjective π → π.ker ≤ Subgroup.center E → Nat.Coprime 2 (Nat.card π.ker) →
        ∃ s : LargeEvenSUGroup (Fin d) F (2 ^ n) →* E, ∀ h, π (s h) = h := by
  have h := TableBU.unitaryFieldData_of_card hK hn
  have : CharP F 2 := h.charP
  intro E _ _ π hπ hcen hC
  by_cases he : Even d
  · exact CFSG.LieType.Steinberg.CentralExt.SUClosed.statedSU_exists_section_of_coprime
      (F := F) (p := 2) (f := n) hK he (by omega) E π hπ hcen hC
  · exact CFSG.LieType.Steinberg.CentralExt.SUOdd.statedSU_odd_exists_section_of_central
      (F := F) (p := 2) (f := n) hK hn hd he hdq hπ hcen

theorem qTwoNbrRec_cover_odd
    {F : Type} [Field F] [Finite F] {n d : ℕ}
    (hK : Nat.card F = (2 ^ n) ^ 2) (hn : 1 ≤ n) (hd : 3 ≤ d) (hdq : (d, 2 ^ n) ≠ (3, 2))
    {L' : Type} [Group L'] [Finite L']
    {ψ : L' →* LargeEvenProj (LargeEvenSUGroup (Fin d) F (2 ^ n))} (hψ : Function.Surjective ψ)
    (hker : ψ.ker ≤ Subgroup.center L') (hperf : commutator L' = ⊤)
    (hodd : ∀ y ∈ ψ.ker, y ^ 2 = 1 → y = 1) :
    ∃ φ : LargeEvenSUGroup (Fin d) F (2 ^ n) →* L', Function.Surjective φ ∧
      ∀ s, ψ (φ s) = LargeEvenProjMk (LargeEvenSUGroup (Fin d) F (2 ^ n)) s := by
  have : Finite (LargeEvenSUGroup (Fin d) F (2 ^ n)) := Finite.of_injective
    (fun x : LargeEvenSUGroup (Fin d) F (2 ^ n) =>
      ((x : GL (Fin d) F) : Matrix (Fin d) (Fin d) F))
    (fun x y hxy => Subtype.ext (Units.ext hxy))
  obtain ⟨α, hα, hαs⟩ := StdSubRestU.exists_surjective_of_oddKernel
    (q := LargeEvenProjMk (LargeEvenSUGroup (Fin d) F (2 ^ n)))
    (QuotientGroup.mk'_surjective _) (qTwoNbrRec_hsplit hK hn hd hdq) hψ hker hperf hodd
  exact ⟨α, hαs, hα⟩

end CFSG.StandardType.QTwo

end
