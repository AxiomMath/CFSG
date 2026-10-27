module

public import CFSG.LocalAnalysis.StandardType.GGRealKGThree
public import CFSG.LocalAnalysis.StandardType.GGRootSL2CoverTorus
public import CFSG.LocalAnalysis.StandardType.GGE6ThreeRootGenKG
public import CFSG.LocalAnalysis.StandardType.GGKGWeylReflOn
import CFSG.LocalAnalysis.StandardType.GGTableBExcE6Three

public section

namespace CFSG.StandardType.E6ThreeRootGen

open CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley TableBExc.E6Three

section Row


theorem ggTorusRootSL2_E6Three {K : Type} [Field K] [Finite K] [CharP K 2]
    (h3 : 3 ∣ Nat.card K - 1) :
    GGTorusRootSL2 3 5 (TableBExc.RecipeGroup .E6 K) (TableBExc.RecipeID .E6 K) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨n, -, hKcard⟩ := FiniteField.card K 2
  have hn : 1 ≤ (n : ℕ) := n.pos
  have hK : Nat.card K = 2 ^ (n : ℕ) := by
    rw [Nat.card_eq_fintype_card, hKcard]
  obtain ⟨ζ, hζo⟩ := TableBSymp.exists_orderOf_eq_of_dvd (K := K) (p := 3) h3
  have hζ : ζ ^ 3 = 1 := hζo ▸ pow_orderOf_eq_one ζ
  let e := TableBExc.recipeEquiv .E6 K
  refine ggTorusRootSL2_of_mulEquiv e
    (I' := (MulAut.congr e) '' TableBExc.RecipeID .E6 K)
    (fun φ hφ => ⟨φ, hφ, rfl⟩) ?_
  intro L' _ _ ψ A hTB
  obtain ⟨hψ, hker, hperf, hA, hAI, h5, -, hsc⟩ := hTB
  have hAH : ∀ a ∈ A, ∃ φ ∈ (TableBExc.E6Three.hatAut .E6 K).range,
      ∀ l, φ (ψ l) = ψ (a l) := by
    intro a ha
    obtain ⟨φ, ⟨φ₀, hφ₀, rfl⟩, hφ⟩ := hAI a ha
    exact ⟨MulAut.congr e φ₀, (E6ThreeModel.recipeID_iff_hatAut φ₀).1 hφ₀, hφ⟩
  let ψr : L' →* TableBExc.RecipeGroup .E6 K := e.symm.toMonoidHom.comp ψ
  have hψr : Function.Surjective ψr := e.symm.surjective.comp hψ
  have hkereq : ψr.ker = ψ.ker :=
    MonoidHom.ker_comp_of_injective ψ e.symm.toMonoidHom e.symm.injective
  have hcard : Nat.card ψ.ker ∣ 3 := by
    rw [← hkereq]
    exact TableBExc.E6Three.card_ker_dvd_three_e6 (n := (n : ℕ)) hn hK hψr
      (by rw [hkereq]; exact hker) hperf
  have hodd : ∀ z ∈ ψ.ker, Odd (orderOf z) := by
    intro z hz
    have hz3 : orderOf z ∣ 3 := (Subgroup.orderOf_dvd_natCard ψ.ker hz).trans hcard
    rcases (Nat.dvd_prime Nat.prime_three).1 hz3 with h | h
    · rw [h]; exact ⟨0, rfl⟩
    · rw [h]; exact ⟨1, rfl⟩
  have hkerp : ∀ z ∈ ψ.ker, z ^ 3 = 1 := by
    intro z hz
    have hz3 : orderOf z ∣ 3 := (Subgroup.orderOf_dvd_natCard ψ.ker hz).trans hcard
    exact orderOf_dvd_iff_pow_eq_one.1 hz3
  obtain ⟨g, κ, T, hg, hκinj, hκrange, hreal, hkerT_odd, hTA, hH, hinner⟩ :=
    exists_frame_torus_E (ζ := ζ) hζ hζo hψ hker hperf hcard hA hAH h5 hsc
  let V : Set (Fin Tag.E6.rank → ZMod 3) := {x | Multiplicative.ofAdd x ∈ κ.range}
  have hVmem : ∀ x, Multiplicative.ofAdd x ∈ κ.range ↔ x ∈ V := fun _ => Iff.rfl
  have hV : V = Set.univ ∨ V = (NoOffRest.hypE6 : Set (Fin Tag.E6.rank → ZMod 3)) :=
    TwE6ThreeRootGen.coordSet_eq_univ_or_hypE6 hκrange
  let ι := {γ : Fin Tag.E6.rank → ℤ // IsRoot .E6 γ}
  let s : ι → (Fin Tag.E6.rank → ZMod 3) → Fin Tag.E6.rank → ZMod 3 :=
    fun i => ExcSplitRootGen.excRefl (p := 3) i.1
  let τ : (Fin Tag.E6.rank → ZMod 3) → ModGL .E6 K :=
    fun x => g * rootDiagUnit .E6 (TableBExc.E6Three.zetaVec ζ hζ x) * g⁻¹
  let r : ι → adjointGroup .E6 K :=
    fun i => ⟨g, hg⟩ * ExcSplitRootGen.excWeyl (K := K) i * ⟨g, hg⟩⁻¹
  let S : ι → Subgroup (adjointGroup .E6 K) :=
    fun i => (ExcSplitRootGen.excComp (K := K) i.1).map
      (MulAut.conj (⟨g, hg⟩ : adjointGroup .E6 K)).toMonoidHom
  have : Finite ↥(adjointGroup .E6 K) := Finite.of_surjective ψ hψ
  have hR := LayerCores.adjointGroup_isSimple_nonabelian (τ := .E6) (Or.inr (Or.inl rfl)) K
  refine ggTorusRootSL2At_of_coverTorus_chev (p := 3) (k := Tag.E6.rank) (L' := L')
    (R := ↥(adjointGroup .E6 K)) (G := ModGL .E6 K)
    (ψ := ψ) (A := A) (Φ := κ) (τ := τ) (T := T) (ι := ι) (s := s) (r := r) (S := S)
    (ι₀ := (adjointGroup .E6 K).subtype)
    hψ hker ?_ hkerp ?_ hκinj ?_ ?_ hTA ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hR.1 hR.2
    (LayerCores.isChevSimple_adjointGroup_charTwo (τ := .E6) (Or.inr (Or.inl rfl)) K)
    Nat.prime_three (by norm_num) (fun a ha => hA.2 a ha) ?_ ?_
  · exact center_adjointGroup_eq_bot (τ := Tag.E6) (K := K)
  · exact Subgroup.subtype_injective _
  · intro x y
    change g * rootDiagUnit .E6 (TableBExc.E6Three.zetaVec (τ := Tag.E6) ζ hζ
        (x + y)) * g⁻¹ =
      (g * rootDiagUnit .E6 (TableBExc.E6Three.zetaVec (τ := Tag.E6) ζ hζ x) * g⁻¹) *
        (g * rootDiagUnit .E6 (TableBExc.E6Three.zetaVec (τ := Tag.E6) ζ hζ y) * g⁻¹)
    rw [ExcFrames.zetaVec_add (τ := Tag.E6) ζ hζ (x := x) (y := y), rootDiagUnit_mul]
    group
  · exact hreal
  · intro z hz
    exact hkerT_odd z hz (hodd z hz)
  · intro i x
    change (g * (ExcSplitRootGen.excWeyl (K := K) i : ModGL .E6 K) * g⁻¹) *
        (g * rootDiagUnit .E6 (TableBExc.E6Three.zetaVec ζ hζ x) * g⁻¹) *
        (g * (ExcSplitRootGen.excWeyl (K := K) i : ModGL .E6 K) * g⁻¹)⁻¹ =
      g * rootDiagUnit .E6 (TableBExc.E6Three.zetaVec ζ hζ
        (ExcSplitRootGen.excRefl (p := 3) i.1 x)) * g⁻¹
    calc (g * (ExcSplitRootGen.excWeyl (K := K) i : ModGL .E6 K) * g⁻¹) *
          (g * rootDiagUnit .E6 (TableBExc.E6Three.zetaVec ζ hζ x) * g⁻¹) *
          (g * (ExcSplitRootGen.excWeyl (K := K) i : ModGL .E6 K) * g⁻¹)⁻¹
        = g * ((ExcSplitRootGen.excWeyl (K := K) i : ModGL .E6 K) *
            rootDiagUnit .E6 (TableBExc.E6Three.zetaVec ζ hζ x) *
            (ExcSplitRootGen.excWeyl (K := K) i : ModGL .E6 K)⁻¹) * g⁻¹ := by group
      _ = g * rootDiagUnit .E6 (TableBExc.E6Three.zetaVec ζ hζ
            (ExcSplitRootGen.excRefl (p := 3) i.1 x)) * g⁻¹ := by
          rw [excWeyl_conj_rootDiagUnit (τ := Tag.E6) (K := K) (p := 3) hζ i x]
  · intro i a
    exact ExcSplitRootGen.excRefl_excRefl (τ := Tag.E6) (p := 3) i.2 _
  · intro i
    exact TwE6ThreeRootGen.card_fix_excRefl_toAdd_mul_three (κ := κ) hκinj hVmem hV i.2
  · intro i a
    exact hH _ (TwE6ThreeRootGen.excRefl_sub_mem_hypE6 _ _)
  · intro i
    refine Subgroup.mem_map.mpr ⟨ExcSplitRootGen.excWeyl (K := K) i,
      ExcSplitRootGen.excWeyl_mem_excComp i, ?_⟩
    rfl
  · intro i
    exact isComponentOf_excComp_map_conj_e6 (g := g) hg hζo hζ hVmem hV i
  · intro i
    exact dvd_card_excComp_map_conj_e6 (g := g) hg hζo i
  · intro a ha
    obtain ⟨φ, -, hφ⟩ := hAI a ha
    exact ⟨φ, hφ⟩
  · intro φ hφ hφr
    exact exists_root_of_isReflection_frame hκinj hVmem hV hinner hφ hφr

end Row

end CFSG.StandardType.E6ThreeRootGen

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley


theorem ggRealKGThreeRow_e6Split : GGRealKGThreeRow .e6Split := by
  intro p lab hp hlab _ hs Q hQ
  obtain ⟨hp3, ⟨htag, hpn⟩, -⟩ := hs
  subst hp3
  obtain ⟨t, l, n⟩ := lab
  dsimp only at htag hpn
  subst htag
  have hQ' : LargeEvenRecipeChevalley (LargeEvenCartanE 6) (2 ^ n) false Q := hQ
  obtain ⟨K, _, _, hK, hQK⟩ := hQ'
  have : CharP K 2 := charP_two_of_card hK
  have h3 : 3 ∣ Nat.card K - 1 := by rw [hK]; exact hpn
  show LargeEvenRecipeChevalley (LargeEvenCartanE 6) (2 ^ n) false fun R _ I F =>
    Q R I F ∧ ∃ r, GGTorusLift 3 r R ∧ GGTorusRootSL2 3 r R I
  exact ⟨K, inferInstance, inferInstance, hK, hQK, 5, TableBExc.ggTorusLift_E6_three h3,
    E6ThreeRootGen.ggTorusRootSL2_E6Three h3⟩

end CFSG.StandardType

end
