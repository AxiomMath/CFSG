module

public import CFSG.LocalAnalysis.StandardType.GGNbrBalancePumpup
public import CFSG.LocalAnalysis.StandardType.GGTypeAFarPComp

public section

namespace CFSG.StandardType

open CFSG.Assembly

variable {G : Type} [Group G] [Finite G]

theorem ggNbr_of_pumpup_conj (hPU : GGPumpupInput) {p : ℕ} {B : Subgroup G} {x : G}
    {L D J : Subgroup G} (hI : GGThmIHyp p B x L) (hDJ : LargeEvenStdSub p B x L D J)
    (hpJ : p ∣ Nat.card J) {d : G} (hD : D = Subgroup.closure {x, d}) {n : G}
    (hnd : n * d * n⁻¹ = d) (hxnB : n * x * n⁻¹ ∈ B) (hxnD : n * x * n⁻¹ ∉ D)
    {P : Subgroup G} (hPJ : P ≤ J) (hPn : P ≤ J.map (MulAut.conj n).toMonoidHom)
    (hperf : P ≤ ⁅P, P⁆) {g : G} (hg : g ∈ P) (hg1 : g ≠ 1) (hgp : g ^ p = 1) :
    GGNbr p B x D J d (ggLayerClosure p (Subgroup.centralizer ({d} : Set G)) J) ∧
      (ggLayerClosure p (Subgroup.centralizer ({d} : Set G)) J).map (MulAut.conj n).toMonoidHom =
        ggLayerClosure p (Subgroup.centralizer ({d} : Set G)) J ∧
      J ≤ ggLayerClosure p (Subgroup.centralizer ({d} : Set G)) J ∧
      LargeEvenPComponent p (Subgroup.centralizer ({d} : Set G))
        (ggLayerClosure p (Subgroup.centralizer ({d} : Set G)) J) := by
  set A := ggLayerClosure p (Subgroup.centralizer ({d} : Set G)) J with hAdef
  have hp : p.Prime := hI.2.2.2.2.2.1.1
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨hA, hJA, -, hor⟩ := pumpup_of_stdSub hPU hI hDJ hpJ hD
  have hAn : A.map (MulAut.conj n).toMonoidHom = A := by
    have h := largeEvenPComponent_conj_centralizer_singleton hA n
    rw [hnd] at h
    exact eq_of_pComponents_of_perfect_common h hA (hPn.trans (Subgroup.map_mono hJA))
      (hPJ.trans hJA) hperf hg hg1 hgp
  refine ⟨?_, hAn, hJA, hA⟩
  rcases hor with h | hc
  · exact h
  · exfalso
    apply hxnD
    set O := LargeEvenPPrimeCoreOf p A with hOdef
    have hS : LargeEvenSStar p B x L := hI.2.2.2.2.2.2.1
    have hcn : (⁅A, Subgroup.zpowers (n * x * n⁻¹)⁆ : Subgroup G) ≤ O := by
      have h := Subgroup.map_mono (f := (MulAut.conj n).toMonoidHom) hc
      rw [Subgroup.map_commutator, hAn, MonoidHom.map_zpowers, hOdef,
        ← largeEvenPPrimeCoreOf_map_conj, hAn] at h
      simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] using h
    have hOcop : Nat.Coprime p (Nat.card O) := by
      rw [hOdef, LargeEvenPPrimeCoreOf, Subgroup.card_map_of_injective A.subtype_injective]
      exact CFSG.pPrimeCore_coprime_card
    have hJN : B ≤ Subgroup.normalizer (J : Set G) :=
      le_normalizer_of_stdSub hS hI.2.2.2.2.2.2.2 hDJ.1
    have hbJ : n * x * n⁻¹ ∈ Subgroup.centralizer (J : Set G) :=
      mem_centralizer_of_commutator_le_coprime hp hDJ.1.2.2.2.2.2.1.2.2 hpJ hOcop
        (fun j hj => mem_normalizer_largeEvenPPrimeCoreOf (Subgroup.le_normalizer (hJA hj)))
        (hJN hxnB) ((Subgroup.commutator_mono hJA le_rfl).trans hcn)
    rw [hDJ.1.2.2.2.2.2.2]
    exact ⟨hxnB, hbJ⟩

end CFSG.StandardType

end
