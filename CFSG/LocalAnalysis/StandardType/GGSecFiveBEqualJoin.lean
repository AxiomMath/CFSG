module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveBJoinDefs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveBPositionDefs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveRestOriginalWeyl
import CFSG.LocalAnalysis.StandardType.GGSecFiveBJoinCore
import CFSG.LocalAnalysis.StandardType.GGSecFiveBNbrType
import CFSG.LocalAnalysis.StandardType.GGSecFiveBPosition
import CFSG.LocalAnalysis.StandardType.GGSecFiveBPositionFrame

public section

namespace CFSG.StandardType

open CFSG.Assembly

private theorem eq_one_of_mul_self_eq_one_of_odd {G : Type*} [Group G] {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) {b : G} (hb : b ^ p = 1) (h2 : b * b = 1) : b = 1 := by
  have h2' : b ^ 2 = 1 := by simpa [pow_two] using h2
  have hdvd : orderOf b ∣ Nat.gcd p 2 :=
    Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hb) (orderOf_dvd_of_pow_eq_one h2')
  have hcop : Nat.Coprime p 2 := (Nat.coprime_primes hp Nat.prime_two).mpr hp2
  rw [hcop.gcd_eq_one, Nat.dvd_one, orderOf_eq_one_iff] at hdvd
  exact hdvd

theorem GGSecFiveRouteCfg.ggG0_eq_of_forall_le {G : Type} [Group G] [Finite G] {p : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)}
    (hR : GGSecFiveRouteCfg p B Bs x L D J 𝒦)
    (hle : ∀ y K, GGNbr p B x D J y K → K ≤ L ⊔ ⨆ K' ∈ 𝒦, K') :
    ggG0 p B x L D J = L ⊔ ⨆ K ∈ 𝒦, K := by
  refine le_antisymm ?_ (sup_le (le_ggG0_left p B x L D J) (iSup₂_le fun K hK' => ?_))
  · unfold ggG0
    exact sup_le le_sup_left (iSup_le fun y => iSup_le fun K => iSup_le fun h => hle y K h)
  · obtain ⟨y, hy⟩ := hR.2.2.2.1.2 K hK'
    exact le_ggG0_of_ggNbr hy

theorem bEqualMaxJoinInput_of_inputs (hTBF : GGTBFixInput) (hWI : GGNbrInnerWeylInput)
    (hX : GGResXDichotomyInput) (hTCJ : GGTCJKnown) (hRig : GGLabelRigidInput)
    (hTPn : GGNbrTablePNbrInputNarrow) (hA8 : GGForkA8NotReflInput)
    (hraw : GGRawInnFieldInput) (hiso : GGRawInndiagIsoInput)
    (hFC : GGResNbrFixCentralizesInput) :
    ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
      (𝒦 : Finset (Subgroup G)), GGSecFiveRouteCfg p B Bs x L D J 𝒦 → B = Bs →
        ∀ (ι : Type) (M : CoxeterMatrix ι) (e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)),
          GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) M e → GGIsWeylMatrixB M →
            (∀ y K, GGNbr p B x D J y K → ggAutomizer K Bs ≤ ggAutomizerJoin L Bs 𝒦) →
              ggG0 p B x L D J = L ⊔ ⨆ K ∈ 𝒦, K := by
  intro G _ _ p B Bs x L D J 𝒦 hR hB ι M e hP hM hK
  obtain ⟨n, e', hn, rfl⟩ := hM
  have hPE : GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) (CoxeterMatrix.B n)
      (((CoxeterMatrix.B n).reindexGroupEquiv e').symm.trans e) :=
    GGCoxeterPres.of_reindex_B (A := ggAutomizerJoin L Bs 𝒦) hn hP
  obtain ⟨h4, eta, i0, hjoin, hLpos⟩ :=
    bOriginalPositionTheoryInput_holds hTBF hWI hX hTCJ hRig G p B Bs x L D J 𝒦 hR n hn
      (((CoxeterMatrix.B n).reindexGroupEquiv e').symm.trans e) hPE
  obtain ⟨hp, hp2, -⟩ := (hR.1.1.1.2.2.2.2.2.1 : p ∈ CFSG.Assembly.LargeEvenBeta 4 G)
  obtain ⟨-, hElem, -, -, -⟩ := hR.1.1.tableB_facts
  have hnoinv : ∀ b ∈ Bs, b * b = 1 → b = 1 := fun b hb h2 =>
    eq_one_of_mul_self_eq_one_of_odd hp hp2 (hElem.2 b hb) h2
  have hL : GGFixLineComp Bs x L := hR.1.fixLineComp_L hTBF hR.2.1
  have hst : LargeEvenStandardType p B x L := hR.1.1.1.2.2.2.2.2.2.2
  have hDJ : LargeEvenStdSub p B x L D J := hR.1.1.2.2
  have h𝒦 : ∀ K ∈ 𝒦, ∃ y, GGNbr p B x D J y K := fun K hK' => hR.2.2.2.1.2 K hK'
  have hfix : ∀ y K, GGNbr p B x D J y K → GGFixLineComp Bs y K :=
    fun y K hn' => hR.1.fixLineComp_nbr hFC hR.2.1 hB hn'
  have hnorm : ∀ y K, GGNbr p B x D J y K → Bs ≤ Subgroup.normalizer (K : Set G) :=
    fun y K hn' =>
      hB ▸ (isComponentOf_of_isNeighborOf hst (isNeighborOf_of_ggNbr hDJ hn')).2
  have htype : ∀ y K, GGNbr p B x D J y K →
      (∃ j : Fin n,
          (ggAutomizer K Bs).map (MulAut.congr eta).toMonoidHom = bCoordinateBlock n p j ∨
          (ggAutomizer K Bs).map (MulAut.congr eta).toMonoidHom = dCoordinateBlock n p j) ∨
        ∃ δ ∈ bSignedFull n p, (ggAutomizer K Bs).map (MulAut.congr eta).toMonoidHom =
          (aPermutationFull n p).map (MulAut.conj δ).toMonoidHom :=
    fun y K hn' => GGSecFiveRouteCfg.nbr_coordType hX hTCJ hRig hTPn hA8 hraw hiso hFC
      hR hB eta hjoin hn' (hK y K hn')
  exact hR.ggG0_eq_of_forall_le fun y K hn' =>
    le_join_of_signedCoordPosition (Nb := fun y K => GGNbr p B x D J y K) hp hp2 h4 eta hnoinv
      hL hLpos hjoin h𝒦 hfix hnorm htype (fun y K y₀ K₀ hn' hn₀ => hn'.mem_closure_pair hn₀)
      (fun y K hn' => GGConfig.not_mem_zpowers_of_ggNbr hR.1.1 hn') hn'

end CFSG.StandardType

end
