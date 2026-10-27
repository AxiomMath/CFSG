module

public import CFSG.LocalAnalysis.StandardType.GGNbrLangFNIUniBlock
public import CFSG.LocalAnalysis.StandardType.GGNbrLangFNIOne
public import CFSG.LocalAnalysis.StandardType.GGNbrLangFNIRows
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GInnUniData

public section

namespace CFSG.StandardType

open CFSG.Open CFSG.Assembly CFSG.RankThree.PartOne.KCUnitaryModel
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.HardMathSupport.Solomon.Coordinator CFSG.LocalAnalysis.GLTheoremA.K155X
  CFSG.LieType.SemisimpleCentralizers.HeldLang CFSG.LocalAnalysis.GLTheoremA.Y10GInnUni
  CFSG.LocalAnalysis.GLTheoremA.Y10GFldUniMark
open CFSG.LieType.SemisimpleCentralizers.Held (heldGU mem_heldGU)


theorem kgFieldRestriction_unitaryRecipe {d n : ℕ} {K : Type} [Field K] [Finite K] (hn : 1 ≤ n)
    (hd : 3 ≤ d) (hdq : ¬(d = 3 ∧ 2 ^ n = 2)) (hK : Nat.card K = (2 ^ n) ^ 2) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) :
    KGFieldRestrictionCont p (LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n)))
      (LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSUGroup (Fin d) K (2 ^ n)))
        (LargeEvenGUSet (Fin d) K (2 ^ n)))
      (LargeEvenMatFieldImage (LargeEvenProjMk (LargeEvenSUGroup (Fin d) K (2 ^ n)))) := by
  intro f hf hord u hu hup _ J₀ hJ₀ f' hf'
  classical
  obtain ⟨τ, hτq, hτ⟩ := exists_frob_equiv hK
  let h : UnitaryFieldData 2 n K := unitaryFieldData_of_card hn hK
  obtain ⟨σ, hσ⟩ := hf
  obtain ⟨A₀, hA₀, hA₀u⟩ := hu
  obtain ⟨A, hA, hAeq⟩ := exists_heldGU_of_GUSet hτq hK hτ A₀ hA₀
  have hσmem : ∀ g ∈ StatedSU d (2 ^ n) K, glMap σ g ∈ StatedSU d (2 ^ n) K :=
    fun g hg => glMap_mem_statedSU hτ hτq σ hg
  have hfσ : ∀ g g' : ↥(StatedSU d (2 ^ n) K),
      (g' : GL (Fin d) K) = glMap σ (g : GL (Fin d) K) →
        f (LargeEvenProjMk (StatedSU d (2 ^ n) K) g) =
          LargeEvenProjMk (StatedSU d (2 ^ n) K) g' :=
    fun g g' hg => hσ g g' (by beta_reduce; rw [hg]; rfl)
  have huA : ∀ g g' : ↥(StatedSU d (2 ^ n) K),
      (g' : GL (Fin d) K) = A * (g : GL (Fin d) K) * A⁻¹ →
        u (LargeEvenProjMk (StatedSU d (2 ^ n) K) g) =
          LargeEvenProjMk (StatedSU d (2 ^ n) K) g' :=
    fun g g' hg => hA₀u g g' (by beta_reduce; rw [hg, hAeq])
  have hdq' : ((d, 2 ^ n) : ℕ × ℕ) ≠ (3, 2) := fun h32 =>
    hdq ⟨congrArg Prod.fst h32, congrArg Prod.snd h32⟩
  obtain ⟨c, hAc⟩ := l154_uni_pow_scalar hτ hτq hK hd hdq' A hA u huA hup
  have hτbar : ∀ x, h.bar x = τ x := fun x => by rw [UnitaryFieldData.bar_apply, hτq]
  have hAmem : A ∈ primeFormUnitary h (idGram K d) := by
    rw [mem_primeFormUnitary]
    simp only [idGram, Units.val_one, Matrix.mul_one]
    have : (⇑h.bar : K → K) = ⇑τ := funext hτbar
    rw [this]
    exact mem_heldGU.1 hA
  have hJP : CFSG.Open.IsComponentOf J₀ (fixSubgroup u) := isComponentOf_iff_open.mp hJ₀
  have hperf : commutator ↥J₀ = ⊤ := hJP.2.2.1
  obtain ⟨c₁, hc₁, hσc⟩ := fniUni_exists_moved h σ hσmem hfσ hp hp2 hord
  apply kgFieldRestriction_of_oneMarking f'
  rcases fniUni_block_data hn hd h hp hp2 A hAmem hAc u huA J₀ hJP with hSU | hSL | hSL2
  · exact fniUni_neg_su h σ hσmem hfσ hperf f' hf' hc₁ hσc hSU
  · exact fniUni_neg_sl h σ hσmem hfσ hperf f' hf' hc₁ hσc hSL
  · exact fniUni_neg_sl2 h σ hσmem hfσ hperf f' hf' hc₁ hσc hSL2

theorem kgFieldRestrictionOn_unitaryLabel :
    KGFieldRestrictionOn fun _ lab => GGInndiagUnitaryLabel lab :=
  fun _ _ hp hp2 hlab _ hS => largeEvenLabelAll_unitary hlab hS fun _ _ _ _ _ hn hd hq hK =>
    kgFieldRestriction_unitaryRecipe hn hd hq hK hp hp2

theorem kgFieldRestrictionOn_unitary : KGFieldRestrictionOn (kgfniRow .unitary) :=
  fun p lab hp hp2 hlab ht3 hrow =>
    kgFieldRestrictionOn_unitaryLabel p lab hp hp2 hlab ht3 (Or.inl hrow.1)

end CFSG.StandardType
