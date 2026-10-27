module

public import CFSG.LocalAnalysis.StandardType.GGTBE6IndSplit
public import CFSG.LocalAnalysis.StandardType.GGTBE6IndTwistAlign
public import CFSG.LocalAnalysis.StandardType.GGTBTorRelE6Split
public import CFSG.LocalAnalysis.StandardType.GGTBTorE7
public import CFSG.LocalAnalysis.StandardType.GGTBE6Witness
public import CFSG.LocalAnalysis.StandardType.GGTBE6Cover
public import CFSG.LocalAnalysis.StandardType.GGE6ThreeModelKGFrameE
public import CFSG.LocalAnalysis.StandardType.GGTableBThreeTBE6
public import CFSG.LocalAnalysis.StandardType.GGTableBOrthRestTorus
public import CFSG.LocalAnalysis.StandardType.GGTDLabels
public import CFSG.LocalAnalysis.StandardType.GGTBXPlumb
public import CFSG.LocalAnalysis.StandardType.GGTBTorE8Split
public import CFSG.LocalAnalysis.StandardType.GGTBTorAIndUFourTwo
public import CFSG.LocalAnalysis.StandardType.GGTBTorG2Holds
public import CFSG.LocalAnalysis.StandardType.GGTBTorF4
public import CFSG.LocalAnalysis.StandardType.GGTBTorD
public import CFSG.LocalAnalysis.StandardType.GGTBTorCHolds
public import CFSG.LocalAnalysis.StandardType.GGTBTorRelA5Holds
public import CFSG.LocalAnalysis.StandardType.GGTBTorRelDHolds

public noncomputable section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Minuscule CFSG.LieType.Steinberg.Isogeny
  CFSG.LieType.Steinberg.CentralExt.MinusculeClosed
  CFSG.StandardType.E6ThreeModel CFSG.StandardType.TableBExc.E6Three
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LocalAnalysis.StandardType.GGTBE6Cover


private def unitsEquiv (K : Type) [Field K] [Finite K] :
    Kˣ ≃* Multiplicative (ZMod (Nat.card K - 1)) := by
  have hc : Nat.card Kˣ = Nat.card K - 1 := Nat.card_units K
  exact hc ▸ (zmodCyclicMulEquiv (inferInstance : IsCyclic Kˣ)).symm

private theorem nm_pow_two (K : Type) [Field K] [CharP K 2] (i : Fin Tag.E6.rank) :
    e6Data_valid.nm K i ^ 2 = 1 := by
  rw [e6Data_valid.nm_sq K i]
  have h1 : (-1 : Kˣ) = 1 := Units.ext (CharTwo.neg_eq (1 : K))
  rw [h1, e6Data_valid.hm_one]

private theorem weyl_eq_of_lift {K L : Type} [Field K] [Finite K] [CharP K 2]
    [Group L] (ψ : L →* adjointGroup .E6 K)
    (hker : ψ.ker ≤ Subgroup.center L) (hc : Nat.card ψ.ker ∣ 3)
    (φ : e6Data_valid.minGroup K →* L) (hφ : ∀ x, ψ (φ x) = e6Isogeny K x)
    {ζ : Kˣ} (hζ : ζ ^ 3 = 1) {n : L} (i : Fin Tag.E6.rank)
    (hn : ψ n = (eFrame K ζ hζ).nb i) (hn2 : n * n = 1) :
    n = φ (e6Data_valid.nm K i) := by
  have hc2 : Nat.Coprime 2 (Nat.card ψ.ker) :=
    (by decide : Nat.Coprime 2 3).of_dvd_right hc
  refine OrthRest.eq_of_lift_of_coprime hker hc2 ?_ (by simpa [pow_two] using hn2) ?_
  · rw [hφ, hn]
    apply Subtype.ext
    change weylElt .E6 K i 1 = (e6Isogeny K (e6Data_valid.nt K i 1) : ModGL .E6 K)
    rw [CFSG.HardMathSupport.Timmesfeld.CrossChar.e6Isogeny_nt_eq]
  · rw [← map_pow, nm_pow_two, map_one]

theorem ggTorusTorW_adjoint_E6_three {K : Type} [Field K] [Finite K] [CharP K 2]
    (h3 : 3 ∣ Nat.card K - 1) :
    GGTorusTorW 3 5 (Nat.card K - 1) 6 CartanMatrix.E₆ CoxeterMatrix.E₆
      (adjointGroup .E6 K) ((hatAut .E6 K).range : Set _) := by
  intro L _ _ ψ A hTB
  obtain ⟨hψ, hker, hperf, hA, hAI, h5, -, hsc⟩ := hTB
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let : Fintype K := Fintype.ofFinite K
  obtain ⟨f, -, hKf⟩ := FiniteField.card K 2
  have hf : 1 ≤ (f : ℕ) := f.pos
  have hK : Nat.card K = 2 ^ (f : ℕ) := by rw [Nat.card_eq_fintype_card, hKf]
  let ψr : L →* TableBExc.RecipeGroup .E6 K :=
    (TableBExc.recipeEquiv .E6 K).symm.toMonoidHom.comp ψ
  have hψr : Function.Surjective ψr := (TableBExc.recipeEquiv .E6 K).symm.surjective.comp hψ
  have hkerEq : ψr.ker = ψ.ker := by
    ext x
    simp [ψr, MonoidHom.mem_ker]
  have hc : Nat.card ψ.ker ∣ 3 := by
    rw [← hkerEq]
    exact card_ker_dvd_three_e6 hf hK hψr (by rw [hkerEq]; exact hker) hperf
  have hc' : Nat.card ψ.ker = 1 ∨ Nat.card ψ.ker = 3 :=
    (Nat.dvd_prime Nat.prime_three).1 hc
  obtain ⟨ζ, hζo⟩ := TableBSymp.exists_orderOf_eq_of_dvd (K := K) h3
  have hζ : ζ ^ 3 = 1 := by rw [← hζo]; exact pow_orderOf_eq_one ζ
  let D := eFrame K ζ hζ
  have hD : D.Good := eFrame_good hζo hζ
  have hZ : ψ.ker = Subgroup.center L := BstarDesc.ker_eq_center hψ hker hD.center
  let ρ := BstarDesc.descAut hψ hZ
  have hρ : ∀ a l, ρ a (ψ l) = ψ (a l) := BstarDesc.descAut_apply hψ hZ
  have hρi : Function.Injective ρ := BstarDesc.descAut_injective hψ hZ hperf
  have hAH : ∀ a ∈ A, ρ a ∈ D.H := by
    intro a ha
    obtain ⟨b, hb, hba⟩ := hAI a ha
    have heq : ρ a = b := by
      apply MulEquiv.ext
      intro x
      obtain ⟨l, rfl⟩ := hψ x
      rw [hρ, hba]
    rw [heq]
    exact hb
  obtain ⟨γ, -, hγ⟩ := exists_align D hD.shape hρi hA h5 hAH
  let ψ' : L →* adjointGroup .E6 K := γ.toMonoidHom.comp ψ
  have hψ' : Function.Surjective ψ' := γ.surjective.comp hψ
  have hker' : ψ'.ker = ψ.ker := by
    ext x
    simp [ψ', MonoidHom.mem_ker]
  let ρ' : MulAut L →* MulAut (adjointGroup .E6 K) :=
    (MulAut.conj γ).toMonoidHom.comp ρ
  have hρ' : ∀ a l, ρ' a (ψ' l) = ψ' (a l) := by
    intro a l
    change (MulAut.conj γ (ρ a)) (γ (ψ l)) = γ (ψ (a l))
    rw [MulAut.conj_apply]
    simp only [MulAut.mul_apply, MulAut.inv_apply_self]
    rw [hρ]
  have hρ'i : Function.Injective ρ' := (MulAut.conj γ).injective.comp hρi
  have hal : ∀ a ∈ A, ρ' a ∈ D.diag.range := by
    intro a ha
    exact hγ a ha
  have hkc : ψ'.ker ≤ Subgroup.center L := by rw [hker']; exact hker
  have hc'' : Nat.card ψ'.ker = 1 ∨ Nat.card ψ'.ker = 3 := by rw [hker']; exact hc'
  obtain ⟨Φ, hΦ, T, n, ⟨hbody, -⟩, hnb⟩ :=
    model_odd_of_good_diag D ggAbelianLift hD hψ' hkc hc'' hρ' hρ'i hA hsc hal
  have hd : GGE6ThreeData ψ'.ker A Φ T n := by
    obtain ⟨h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11,h12⟩ := hbody
    exact ⟨h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11,h12⟩
  obtain ⟨φ, δ, hφs, hφ, hφker, hδi, hδ, hδfix, hδT, hδn⟩ :=
    exists_cover_and_diagonal_lift K L ψ' hψ' hkc hperf
  let e := unitsEquiv K
  have hρδ : ∀ b, ρ' (δ b) = rootDiagAutHom .E6 K b := by
    intro b
    apply MulEquiv.ext
    intro x
    obtain ⟨l, rfl⟩ := hψ' x
    rw [hρ', hδ]
    rfl
  have hτδ : ∀ (τ : MulAut L) (b : Fin Tag.E6.rank → Kˣ),
      ρ' τ = rootDiagAutHom .E6 K b → τ = δ b := by
    intro τ b hb
    apply hρ'i
    rw [hb, hρδ]
  exact TBE6.torData_of_aligned ρ' e φ n hd.conj_w_mem_normalizer ψ' hψ' hρ' hρ'i
    hφ hφs hA hζ hζo hd hΦ
    (fun τ hτ i s => by
      obtain ⟨b, hb⟩ := hτ
      rw [hτδ τ b hb.symm]
      exact hδfix b i s)
    (fun τ hτ i => by
      obtain ⟨b, hb⟩ := hτ
      have hnφ : n i = φ (e6Data_valid.nm K i) :=
        weyl_eq_of_lift ψ' hkc (by rw [hker']; exact hc) φ hφ hζ i (hnb i)
          ((hd.odd (by
          rw [hker']
          rcases hc' with h | h <;> rw [h] <;> decide)).1 i)
      rw [hnφ, hτδ τ b hb.symm, hδn b i,
        TBE6.root_apply ρ' e i (hρδ b)]
      change φ (e6Data_valid.nm K i) *
          (φ (e6Data_valid.hm K i (b i)) * φ (e6Data_valid.nm K i))⁻¹ =
        (φ (e6Data_valid.hm K i (e.symm (e (b i)))))⁻¹
      rw [e.symm_apply_apply]
      group)

theorem ggTorusTorW_recipe_E6_three {K : Type} [Field K] [Finite K] [CharP K 2]
    (h3 : 3 ∣ Nat.card K - 1) :
    GGTorusTorW 3 5 (Nat.card K - 1) 6 CartanMatrix.E₆ CoxeterMatrix.E₆
      (TableBExc.RecipeGroup .E6 K) (TableBExc.RecipeID .E6 K) := by
  intro L _ _ ψ A hTB
  obtain ⟨hψ, hker, hperf, hA, hAI, h5, h3A, hsc⟩ := hTB
  let ε := TableBExc.recipeEquiv .E6 K
  let ψ' := ε.toMonoidHom.comp ψ
  have hψ' : Function.Surjective ψ' := ε.surjective.comp hψ
  have hk : ψ'.ker = ψ.ker := by
    ext x
    simp [ψ', MonoidHom.mem_ker]
  have hAI' : ∀ a ∈ A, ∃ b ∈ (hatAut .E6 K).range, ∀ l, b (ψ' l) = ψ' (a l) := by
    intro a ha
    obtain ⟨b, hb, hbl⟩ := hAI a ha
    refine ⟨MulAut.congr ε b, (E6ThreeModel.recipeID_iff_hatAut b).1 hb, ?_⟩
    intro l
    change ε (b (ε.symm (ε (ψ l)))) = ε (ψ (a l))
    rw [ε.symm_apply_apply, hbl]
  exact ggTorusTorW_adjoint_E6_three h3 L ψ' A
    ⟨hψ', by rw [hk]; exact hker, hperf, hA, hAI', h5, h3A, hsc⟩

theorem ggTBTorE6_holds : GGTBTorE6 := by
  intro lab hlab htag h3
  obtain ⟨t, l, f⟩ := lab
  have hf : 1 ≤ f := hlab.1
  dsimp only at htag hf h3 ⊢
  subst htag
  have hm : ggTorM ⟨.E6, l, f⟩ = 2 ^ f - 1 := by simp [ggTorM]
  have h3' : 3 ∣ 2 ^ f - 1 := hm ▸ h3
  intro Q hQ
  dsimp only [LargeEvenRawDatum] at hQ ⊢
  obtain ⟨K, _, _, hK, hQK, -⟩ := TableBExc.recipeChevalleyE6_torusLift_three h3' hQ
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let : Fintype K := Fintype.ofFinite K
  have : CharP K 2 := charP_of_card_eq_prime_pow (f := f)
    (by rw [← Nat.card_eq_fintype_card, hK])
  refine ⟨K, inferInstance, inferInstance, hK, hQK, ?_⟩
  have hwm : ggTorM ⟨.E6, l, f⟩ = Nat.card K - 1 := by rw [hm, hK]
  rw [hwm]
  exact ggTorusTorW_recipe_E6_three (by rw [hK]; exact h3')


theorem ggTBTorAll_of_remaining
    (_h : GGTBTorRemaining) : GGTBTorAll := by
  exact ⟨ggTBTorA_holds, ggTBTorE6_holds, ggTBTorE8_holds, ggTBTorAInd_holds, ggTBTorC_holds,
    ggTBTorD_holds,
    TBE6Ind.ggTBTorE6Ind_of_twist TBE6IndTwist.ggTBTorE6IndTwist_holds,
    ggTBTorE7_holds, ggTBTorE8Ind_holds, ggTBTorF4_holds,
    ggTBTorG2_holds, ggTBTorRelD_holds, ggTBTorRelE6_holds, ggTBTorRelA5_holds⟩


end CFSG.StandardType
