module

public import CFSG.LocalAnalysis.StandardType.GGTorusScalar
public import CFSG.LocalAnalysis.StandardType.GGTBTorF4Cover
public import CFSG.LocalAnalysis.StandardType.GGTBTorF4SplitFrame
public import CFSG.LocalAnalysis.StandardType.GGTBTorF4NonsplitFrame
public import CFSG.LocalAnalysis.StandardType.GGTorusWeylFrame
public import CFSG.LocalAnalysis.StandardType.GGTorusE8Scalar
public import CFSG.LocalAnalysis.StandardType.GGFrameRouteA4F4
public import CFSG.LocalAnalysis.StandardType.GGTBTorRest

public noncomputable section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.RankThree.Chevalley CFSG.LieType.RootSystem
  CFSG.HardMathSupport.Timmesfeld.CrossChar
open CFSG.Open (IsElemAbelian)


variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem ggTorusTorData_F4_split_standard {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpK : p ∣ Nat.card K - 1) :
    GGTorusTorData (Nat.card K - 1) 4 CartanMatrix.F₄ CoxeterMatrix.F₄
      (adjointGroup .F4 K) (scalarA (TableBF4.torusPow K p)) := by
  obtain ⟨l⟩ := F4SplitTorus.exists_unitValue_equiv (K := K)
  let φ : (Fin Tag.F4.rank → Kˣ) →* adjointGroup .F4 K := F4SplitTorus.coordHom
  let E := TableBF4.torusPow K p
  let n : Fin Tag.F4.rank → adjointGroup .F4 K := fun k =>
    ⟨canonicalRep (coxeterSystem .F4) K (simple .F4 k), canonicalRep_mem_adjointGroup _ _ _⟩
  have hnE : ∀ k, n k ∈ Subgroup.normalizer (E : Set (adjointGroup .F4 K)) :=
    fun k => F4AutWeyl.canonicalRep_mem_normalizer_torusPow_F4 K p (simple .F4 k)
  obtain ⟨eW, heW⟩ := standard_split_markedWeyl hp hp2 hpK
  obtain ⟨hnA, eA, heA⟩ := markedWeyl_innerImage E mulAut_conj_injective_adjointGroup n hnE eW heW
  let A := scalarA E
  let ρ : WeylGroup .F4 →* MulAut ↥A :=
    (ggAutomizer (MulAut.conj : adjointGroup .F4 K →* MulAut (adjointGroup .F4 K)).range A).subtype.comp
      eA.toMonoidHom
  have hρ : Function.Injective ρ := Subtype.val_injective.comp eA.injective
  have hρrange : ρ.range =
      ggAutomizer (MulAut.conj : adjointGroup .F4 K →* MulAut (adjointGroup .F4 K)).range A := by
    ext x
    constructor
    · rintro ⟨g, rfl⟩
      exact (eA g).2
    · intro hx
      obtain ⟨g, hg⟩ := eA.surjective ⟨x, hx⟩
      exact ⟨g, congrArg Subtype.val hg⟩
  have hρsimple : ∀ k (a : ↥A), ((ρ (simple .F4 k) a : ↥A) : MulAut (adjointGroup .F4 K)) =
      MulAut.conj (n k) * (a : MulAut (adjointGroup .F4 K)) * (MulAut.conj (n k))⁻¹ := by
    intro k a
    change (((eA (simple .F4 k) : MulAut ↥A) a : ↥A) : MulAut (adjointGroup .F4 K)) = _
    have heAk : (eA (simple .F4 k) : MulAut ↥A) = ggConjAut A (hnA k) := heA k
    rw [heAk, ggConjAut_apply]
  obtain ⟨ζ, hζo⟩ := exists_units_orderOf_eq_of_dvd_card_sub_one hp hpK
  have hζp : ζ ^ p = 1 := by rw [← hζo]; exact pow_orderOf_eq_one ζ
  have hζ1 : ζ ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hζo
    exact hp.ne_one hζo.symm
  have hFormula : ∀ k (a : Fin Tag.F4.rank → Kˣ),
      n k * φ a * (n k)⁻¹ = φ a * (φ (corTuple Tag.F4.cartan k (a k)))⁻¹ := by
    intro k a
    apply Subtype.ext
    change canonicalRep (coxeterSystem .F4) K (simple .F4 k) *
        (φ a : ModGL .F4 K) * (canonicalRep (coxeterSystem .F4) K (simple .F4 k))⁻¹ = _
    rw [canonicalRep_simple]
    have h := F4SplitTorus.simple_conj_coordHom k a
    have hcor : F4SplitTorus.corootHom k (a k) = φ (corTuple Tag.F4.cartan k (a k)) := by
      change φ (F4SplitTorus.corootTupleHom k (a k)) =
        φ (corTuple Tag.F4.cartan k (a k))
      apply congrArg φ
      funext i
      have hC : Tag.F4.cartan k i = CartanMatrix.F₄ i k := by
        fin_cases i <;> fin_cases k <;> rfl
      simp only [F4SplitTorus.corootTupleHom, MonoidHom.coe_mk, OneHom.coe_mk, corTuple, hC]
    rw [hcor] at h
    exact h
  have hEiff : ∀ g, g ∈ E ↔ g ^ p = 1 ∧ g ∈ φ.range := fun g =>
    (F4SplitTorus.mem_torusPow_iff g p).trans and_comm
  have hAB : Tag.F4.cartan * cartanInvF4 = 1 := cartan_mul_cartanInv_F4
  have hBA : cartanInvF4 * Tag.F4.cartan = 1 :=
    (Matrix.mul_eq_one_comm_of_equiv (Equiv.refl (Fin Tag.F4.rank))).mp hAB
  have hCB : Tag.F4.cartan.transpose * cartanInvF4.transpose = 1 := by
    simpa only [Matrix.transpose_mul, Matrix.transpose_one] using congrArg Matrix.transpose hBA
  have hBC : cartanInvF4.transpose * Tag.F4.cartan.transpose = 1 := by
    simpa only [Matrix.transpose_mul, Matrix.transpose_one] using congrArg Matrix.transpose hAB
  have hFormulaColumn : ∀ k (a : Fin Tag.F4.rank → Kˣ),
      n k * φ a * (n k)⁻¹ =
        φ a * (φ (corTuple Tag.F4.cartan.transpose.transpose k (a k)))⁻¹ := by
    simpa only [Matrix.transpose_transpose] using hFormula
  have h := ggTorusTorData_of_scalarRootCoordinates_columns l φ F4SplitTorus.coordHom_injective
    Tag.F4.cartan.transpose cartanInvF4.transpose hCB hBC center_adjointGroup_eq_bot E hEiff
    ζ hζp hζ1 n hnA hFormulaColumn (centralizer_torusPow_le_coordHom_range hp hp2 hpK)
    (coxeterMatrix (CFSG.LieType.Chevalley.isFiniteType_cartan .F4)) ρ hρ hρrange hρsimple
  have hC : Tag.F4.cartan.transpose = CartanMatrix.F₄ := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hM : coxeterMatrix (CFSG.LieType.Chevalley.isFiniteType_cartan .F4) = CoxeterMatrix.F₄ :=
    FrameRoute.coxeterF4_eq.symm
  rw [hM] at h
  change GGTorusTorData (Nat.card K - 1) Tag.F4.rank CartanMatrix.F₄ CoxeterMatrix.F₄
    (adjointGroup .F4 K) (scalarA E)
  rw [← hC]
  exact h

theorem ggTorusTorData_F4_split {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpK : p ∣ Nat.card K - 1) (E : Subgroup (adjointGroup .F4 K))
    (hE : IsElemAbelian p E) (hcard : p ^ 4 ≤ Nat.card E) :
    GGTorusTorData (Nat.card K - 1) 4 CartanMatrix.F₄ CoxeterMatrix.F₄
      (adjointGroup .F4 K) (scalarA E) := by
  obtain ⟨g, hg⟩ := exists_conjugator_torusPow hp hp2 hpK hE hcard
  let e : adjointGroup .F4 K ≃* adjointGroup .F4 K := MulAut.conj g
  have hA : (E.map (MulAut.conj : adjointGroup .F4 K →* MulAut (adjointGroup .F4 K))).map
      (MulAut.congr e).toMonoidHom =
      (TableBF4.torusPow K p).map (MulAut.conj : adjointGroup .F4 K →* MulAut (adjointGroup .F4 K)) := by
    rw [Subgroup.map_map, ← hg, Subgroup.map_map]
    congr 1
  exact torData_of_f4_model e hA (ggTorusTorData_F4_split_standard hp hp2 hpK)

theorem ggTorusTorData_F4_plus {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hpK : p ∣ Nat.card K + 1) (E : Subgroup (adjointGroup .F4 K))
    (hE : IsElemAbelian p E)
    (hSC : ∀ g ∈ Subgroup.centralizer (E : Set (adjointGroup .F4 K)), g ^ p = 1 → g ∈ E) :
    GGTorusTorData (Nat.card K + 1) 4 CartanMatrix.F₄ CoxeterMatrix.F₄
      (adjointGroup .F4 K) (scalarA E) := by
  have : Fact p.Prime := ⟨hp⟩
  have : NeZero p := ⟨hp.ne_zero⟩
  obtain ⟨Fr, g0, ζ, hζ, D, φ, n, ι, hFr, hg0C, hg0, hΦ, hn, hw, hζo, hι, hrange,
    hbase, hD, hφbase, hφ, hφrange, hnb, hact, hnorm, hEiff, hcent, hFormula⟩ :=
    F4NonsplitFrame.exists_nonsplit_frame_data hp5 hpK hE hSC
  obtain ⟨l⟩ := E8ScalarTorus.exists_rootValue_equiv (K := K)
  have hζm : ζ ^ (Nat.card K + 1) = 1 := by
    obtain ⟨d, hd⟩ := hpK
    rw [hd, pow_mul, hζ, one_pow]
  let z : rootsOfUnity (Nat.card K + 1) (AlgebraicClosure K) :=
    ⟨ζ, (mem_rootsOfUnity _ _).mpr hζm⟩
  have hz : z ^ p = 1 := Subtype.ext hζ
  have hz1 : z ≠ 1 := by
    intro h
    have h1 : ζ = 1 := congrArg Subtype.val h
    rw [h1, orderOf_one] at hζo
    exact hp.ne_one hζo.symm
  have hpodd : Odd p := hp.odd_of_ne_two (by omega)
  obtain ⟨hnE, -, eW, heW⟩ := exists_markedWeyl_ggAutomizer hpodd E ι hι hrange n hact hnorm
  obtain ⟨hnA, eA, heA⟩ := markedWeyl_innerImage E mulAut_conj_injective_adjointGroup n hnE eW heW
  let A := scalarA E
  let ρ : WeylGroup .F4 →* MulAut ↥A :=
    (ggAutomizer (MulAut.conj : adjointGroup .F4 K →* MulAut (adjointGroup .F4 K)).range A).subtype.comp
      eA.toMonoidHom
  have hρ : Function.Injective ρ := Subtype.val_injective.comp eA.injective
  have hρrange : ρ.range =
      ggAutomizer (MulAut.conj : adjointGroup .F4 K →* MulAut (adjointGroup .F4 K)).range A := by
    ext x
    constructor
    · rintro ⟨g, rfl⟩
      exact (eA g).2
    · intro hx
      obtain ⟨g, hg⟩ := eA.surjective ⟨x, hx⟩
      exact ⟨g, congrArg Subtype.val hg⟩
  have hρsimple : ∀ k (a : ↥A), ((ρ (simple .F4 k) a : ↥A) : MulAut (adjointGroup .F4 K)) =
      MulAut.conj (n k) * (a : MulAut (adjointGroup .F4 K)) * (MulAut.conj (n k))⁻¹ := by
    intro k a
    change (((eA (simple .F4 k) : MulAut ↥A) a : ↥A) : MulAut (adjointGroup .F4 K)) = _
    have heAk : (eA (simple .F4 k) : MulAut ↥A) = ggConjAut A (hnA k) := heA k
    rw [heAk, ggConjAut_apply]
  have hCor : ∀ k (a : Fin Tag.F4.rank → rootsOfUnity (Nat.card K + 1) (AlgebraicClosure K)),
      F4ScalarTorus.corootHom D Fr hFr hΦ hn hw k (a k) =
        φ (corTuple Tag.F4.cartan k (a k)) := by
    intro k a
    apply Subtype.ext
    apply baseChangeGL_injective (algebraMap K (AlgebraicClosure K))
    rw [F4ScalarTorus.baseChange_corootHom, hφbase, hD]
    change g0 * torusElt .F4 (AlgebraicClosure K) k (a k : (AlgebraicClosure K)ˣ) * g0⁻¹ = _
    rw [torusElt_eq_rootDiagUnit]
    rfl
  have hFormula' : ∀ k (a : Fin Tag.F4.rank → rootsOfUnity (Nat.card K + 1) (AlgebraicClosure K)),
      n k * φ a * (n k)⁻¹ = φ a * (φ (corTuple Tag.F4.cartan k (a k)))⁻¹ := by
    intro k a
    rw [← hCor k a]
    exact hFormula k a
  have hAB : Tag.F4.cartan * cartanInvF4 = 1 := cartan_mul_cartanInv_F4
  have hBA : cartanInvF4 * Tag.F4.cartan = 1 :=
    (Matrix.mul_eq_one_comm_of_equiv (Equiv.refl (Fin Tag.F4.rank))).mp hAB
  have hCB : Tag.F4.cartan.transpose * cartanInvF4.transpose = 1 := by
    simpa only [Matrix.transpose_mul, Matrix.transpose_one] using congrArg Matrix.transpose hBA
  have hBC : cartanInvF4.transpose * Tag.F4.cartan.transpose = 1 := by
    simpa only [Matrix.transpose_mul, Matrix.transpose_one] using congrArg Matrix.transpose hAB
  have hFormulaColumn : ∀ k (a : Fin Tag.F4.rank → rootsOfUnity (Nat.card K + 1) (AlgebraicClosure K)),
      n k * φ a * (n k)⁻¹ =
        φ a * (φ (corTuple Tag.F4.cartan.transpose.transpose k (a k)))⁻¹ := by
    simpa only [Matrix.transpose_transpose] using hFormula'
  have h := ggTorusTorData_of_scalarRootCoordinates_columns l φ hφ Tag.F4.cartan.transpose cartanInvF4.transpose hCB hBC
    center_adjointGroup_eq_bot E hEiff z hz hz1 n hnA hFormulaColumn hcent
    (coxeterMatrix (CFSG.LieType.Chevalley.isFiniteType_cartan .F4)) ρ hρ hρrange hρsimple
  have hC : Tag.F4.cartan.transpose = CartanMatrix.F₄ := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hM : coxeterMatrix (CFSG.LieType.Chevalley.isFiniteType_cartan .F4) = CoxeterMatrix.F₄ :=
    FrameRoute.coxeterF4_eq.symm
  rw [hM] at h
  change GGTorusTorData (Nat.card K + 1) Tag.F4.rank CartanMatrix.F₄ CoxeterMatrix.F₄
    (adjointGroup .F4 K) (scalarA E)
  rw [← hC]
  exact h



theorem ggTorusTorW_recipe_F4_split {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hK2 : Nat.card K ≠ 2) (hpK : p ∣ Nat.card K - 1) :
    GGTorusTorW p 4 (Nat.card K - 1) 4 CartanMatrix.F₄ CoxeterMatrix.F₄
      (TableBF4.RecipeGroup K) (TableBF4.RecipeID K) := by
  intro L _ _ ψ A hTB
  obtain ⟨e, -, E, hE, hcard, -, hA⟩ := exists_f4_model_of_tbGroup hK2 ψ A hTB
  have hr : p ^ 4 ≤ Nat.card E := by rw [hcard]; exact hTB.2.2.2.2.2.1
  exact torData_of_f4_model e hA (ggTorusTorData_F4_split hp hp2 hpK E hE hr)

theorem ggTorusTorW_recipe_F4_plus {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hK2 : Nat.card K ≠ 2) (hpK : p ∣ Nat.card K + 1) :
    GGTorusTorW p 3 (Nat.card K + 1) 4 CartanMatrix.F₄ CoxeterMatrix.F₄
      (TableBF4.RecipeGroup K) (TableBF4.RecipeID K) := by
  intro L _ _ ψ A hTB
  obtain ⟨e, -, E, hE, -, hSC, hA⟩ := exists_f4_model_of_tbGroup hK2 ψ A hTB
  have hSC' : ∀ g ∈ Subgroup.centralizer (E : Set (adjointGroup .F4 K)), g ^ p = 1 → g ∈ E := by
    intro g hg hgp
    exact hSC g (fun x hx => (Subgroup.mem_centralizer_iff.mp hg x hx).symm) hgp
  exact torData_of_f4_model e hA (ggTorusTorData_F4_plus hp hp5 hpK E hE hSC')

theorem ggTBTorF4_holds : GGTBTorF4 := by
  intro p hp hp2 lab _ htag hdiv hex
  have hq2 := f4_two_pow_ne_two_of_scalar_prime hp hdiv hex
  have hpos : 1 ≤ 2 ^ lab.n := Nat.one_le_two_pow
  rcases hp.dvd_mul.mp hdiv with hMinus | hPlusDiv
  · have hNotPlus : ¬ p ∣ 2 ^ lab.n + 1 := by
      intro h
      have hd : p ∣ (2 ^ lab.n + 1) - (2 ^ lab.n - 1) := Nat.dvd_sub h hMinus
      have heq : (2 ^ lab.n + 1) - (2 ^ lab.n - 1) = 2 := by omega
      rw [heq] at hd
      exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp hd)
    have hEnn : 4 - ggTorEnn p lab = 4 := by simp [ggTorEnn, hNotPlus]
    have hm : ggTorMpm p lab = 2 ^ lab.n - 1 := by simp [ggTorMpm, hMinus]
    rw [hEnn, hm]
    obtain ⟨t, r, n⟩ := lab
    dsimp only at htag hMinus hq2
    subst htag
    intro Q hQ
    obtain ⟨K, _, _, hK, hQ⟩ := hQ
    have : CharP K 2 := charP_two_of_card hK
    have hK2 : Nat.card K ≠ 2 := by rwa [hK]
    have hd : p ∣ Nat.card K - 1 := by rwa [hK]
    refine ⟨K, inferInstance, inferInstance, hK, hQ, ?_⟩
    simpa only [hK] using ggTorusTorW_recipe_F4_split hp hp2 hK2 hd
  · have hp3 : p ≠ 3 := fun h => hex ⟨h, hPlusDiv⟩
    have hp5 : 5 ≤ p := by
      have hle : 2 ≤ p := hp.two_le
      have h4 : p ≠ 4 := by rintro rfl; norm_num at hp
      omega
    have hNotMinus : ¬ p ∣ 2 ^ lab.n - 1 := by
      intro h
      have hd : p ∣ (2 ^ lab.n + 1) - (2 ^ lab.n - 1) := Nat.dvd_sub hPlusDiv h
      have heq : (2 ^ lab.n + 1) - (2 ^ lab.n - 1) = 2 := by omega
      rw [heq] at hd
      exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp hd)
    have hEnn : 4 - ggTorEnn p lab = 3 := by simp [ggTorEnn, hPlusDiv]
    have hm : ggTorMpm p lab = 2 ^ lab.n + 1 := by simp [ggTorMpm, hNotMinus]
    rw [hEnn, hm]
    obtain ⟨t, r, n⟩ := lab
    dsimp only at htag hPlusDiv hq2
    subst htag
    intro Q hQ
    obtain ⟨K, _, _, hK, hQ⟩ := hQ
    have : CharP K 2 := charP_two_of_card hK
    have hK2 : Nat.card K ≠ 2 := by rwa [hK]
    have hd : p ∣ Nat.card K + 1 := by rwa [hK]
    refine ⟨K, inferInstance, inferInstance, hK, hQ, ?_⟩
    simpa only [hK] using ggTorusTorW_recipe_F4_plus hp hp5 hK2 hd


end CFSG.StandardType
