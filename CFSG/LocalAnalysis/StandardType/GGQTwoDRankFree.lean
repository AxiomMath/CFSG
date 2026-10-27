module

public import CFSG.LocalAnalysis.StandardType.GGQTwoDInputs
import CFSG.LocalAnalysis.StandardType.GGQTwoDLocalComm
import CFSG.LocalAnalysis.StandardType.GGQTwoPThree
import CFSG.LocalAnalysis.StandardType.GGAutomizerJoinInduced
import CFSG.LocalAnalysis.StandardType.GGSimplyLacedWeyl

public section

namespace CFSG.StandardType.QTwo

open CFSG.Assembly CFSG.ClassicalInvolution.Phan


theorem ggQTwoRankFreeInput_holds :
    ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
      (𝒦 : Finset (Subgroup G)) (ι : Type) (M : CoxeterMatrix ι)
      (e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)), GGQTwoDCfg p B Bs x L D J 𝒦 M e →
        ∀ (m : ℕ) (e' : Fin m ≃ ι), 4 ≤ m → M = (ggCoxeterMatrixD m).reindex e' →
          (∀ i, Nat.card ↥(qtwoNode Bs (qtwoRefl e e') i) = 6) →
          (∀ i j, ggCoxeterMatrixD m i j = 3 →
            UnitaryBlockStandardPair (GaloisField 2 2) 2 1 (qtwoW Bs (qtwoRefl e e') i j)
              (qtwoNode Bs (qtwoRefl e e') i) (qtwoNode Bs (qtwoRefl e e') j)) →
            (∀ i j, ggCoxeterMatrixD m i j = 2 →
              ∀ x ∈ qtwoNode Bs (qtwoRefl e e') i, ∀ y ∈ qtwoNode Bs (qtwoRefl e e') j,
                x * y = y * x) ∧
            (∀ i j k, ggCoxeterMatrixD m j k = 3 → ggCoxeterMatrixD m i j = 2 →
              ggCoxeterMatrixD m i k = 2 →
              ∀ x ∈ qtwoNode Bs (qtwoRefl e e') i, ∀ y ∈ qtwoW Bs (qtwoRefl e e') j k,
                x * y = y * x) := by
  intro G _ _ p B Bs x L D J 𝒦 ι M e hcfg m e' hm hM h6 hpair
  obtain ⟨r₀, hr₀, hrc₀, h6₀⟩ := hcfg.2.2.2.2
  have hp : p = 3 :=
    CFSG.StandardType.ggQTwo_p_eq_three hcfg.1 M e hcfg.2.2.2.1 hr₀ hrc₀ h6₀
  subst p
  have hBstar : GGBstar 3 B Bs := hcfg.1.1.1.2.1
  have hBs : IsElemAbelian 3 Bs := hBstar.2.1
  have hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ 3 = 1 → g ∈ Bs := hBstar.2.2.2
  have hNT : GGNoTransvection 3 Bs := hcfg.1.1.2.2.2.1
  have hpres : GGCoxeterPres 3 (ggAutomizerJoin L Bs 𝒦) M e := hcfg.2.2.2.1
  have hlabel (i j : Fin m) : M.M (e' i) (e' j) = ggCoxeterMatrixD m i j := by
    rw [hM, CoxeterMatrix.reindex_apply, Equiv.symm_apply_apply, Equiv.symm_apply_apply]
  have hSLM : GGSimplyLaced M := by
    intro a b hab
    have hlab : M.M a b = ggCoxeterMatrixD m (e'.symm a) (e'.symm b) := by
      calc M.M a b = M.M (e' (e'.symm a)) (e' (e'.symm b)) := by
            rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]
        _ = ggCoxeterMatrixD m (e'.symm a) (e'.symm b) := hlabel _ _
    rw [hlab]
    exact ggSimplyLaced_D m _ _ (fun h => hab (by simpa using congrArg e' h))
  have hFin : Finite ι := Finite.of_injective e'.symm e'.symm.injective
  have hinjSimple : Function.Injective M.simple :=
    @ggSimplyLaced_simple_injective ι hFin M hSLM
  have hinj : Function.Injective (qtwoRefl e e') := by
    intro i j h
    apply e'.injective
    apply hinjSimple
    apply e.injective
    exact Subtype.ext h
  have hne2 : ∀ {i j : Fin m}, ggCoxeterMatrixD m i j = 2 → i ≠ j := by
    intro i j hij
    rintro rfl
    rw [CoxeterMatrix.diagonal] at hij
    norm_num at hij
  have hne3 : ∀ {i j : Fin m}, ggCoxeterMatrixD m i j = 3 → i ≠ j := by
    intro i j hij
    rintro rfl
    rw [CoxeterMatrix.diagonal] at hij
    norm_num at hij
  have hrne2 : ∀ {i j : Fin m}, ggCoxeterMatrixD m i j = 2 →
      qtwoRefl e e' i ≠ qtwoRefl e e' j :=
    fun {i j} hij h => hne2 hij (hinj h)
  have hrne3 : ∀ {i j : Fin m}, ggCoxeterMatrixD m i j = 3 →
      qtwoRefl e e' i ≠ qtwoRefl e e' j :=
    fun {i j} hij h => hne3 hij (hinj h)
  have hrefl : ∀ i : Fin m, GGIsReflection 3 (qtwoRefl e e' i) :=
    fun i => hpres.2 (e' i)
  have hmem : ∀ i : Fin m, qtwoRefl e e' i ∈ ggInduced ⊤ Bs :=
    fun i => ggAutomizerJoin_le_ggInduced_top L 𝒦 (e (M.simple (e' i))).2
  have hcard : ∀ i : Fin m, Nat.card (ggRankOne Bs (qtwoRefl e e' i)) = 6 :=
    fun i => h6 i
  have hcomm2 : ∀ i j : Fin m, ggCoxeterMatrixD m i j = 2 →
      qtwoRefl e e' i * qtwoRefl e e' j = qtwoRefl e e' j * qtwoRefl e e' i := by
    intro i j hij
    have hMij : M.M (e' i) (e' j) = 2 := by rw [hlabel i j, hij]
    have hs := ggSimplyLaced_simple_comm (M := M) hMij
    have he := congrArg (fun z : M.Group => e z) hs
    simpa [qtwoRefl, map_mul, Subgroup.coe_mul] using congrArg (Subtype.val) he
  refine ⟨?_, ?_⟩
  · intro i j hij x hx y hy
    exact ggRankOne_commute_ggRankOne hBs hSC (hrefl i) (hrefl j) (hmem i) (hmem j)
      (hcard i) (hcard j) (hcomm2 i j hij) (hrne2 hij) x hx y hy
  · intro i j k hjk hij hik x hx y hy
    have hpairjk := hpair j k hjk
    rw [qtwoW_of_edge (qtwoRefl e e') hjk] at hpairjk hy
    exact ggRankOne_commute_ggRankTwo (K := GaloisField 2 2)
      (natCard_galoisField_two_two) hBs hSC hNT
      (hrefl i) (hrefl j) (hrefl k) (hmem i) (hmem j) (hmem k)
      (hcard i) (hcard j) (hcard k) (hcomm2 i j hij) (hcomm2 i k hik)
      (hrne2 hij) (hrne2 hik) (hrne3 hjk) hpairjk x hx y hy

end CFSG.StandardType.QTwo

end
