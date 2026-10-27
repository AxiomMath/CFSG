module

public import CFSG.LocalAnalysis.StandardType.GGTBTorE8Plus
public import CFSG.LocalAnalysis.StandardType.GGTBTorRest
public import CFSG.LocalAnalysis.StandardType.GGTableBExcThreeE8
public import CFSG.LocalAnalysis.StandardType.GGTorusGenExcSplit
public import CFSG.RankThree.PartOne.KE.E8RootCharacterTorus

public noncomputable section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.RankThree.PartOne.KE
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.LieType.RootSystem

namespace E8SplitTorus

variable {K : Type} [Field K]

@[expose] def coordHom : (Fin Tag.E8.rank → Kˣ) →* adjointGroup .E8 K :=
  (rootDiagUnitHom .E8 K).codRestrict (adjointGroup .E8 K)
    rootDiagUnit_E8_mem_adjointGroup

@[simp] theorem coe_coordHom (a : Fin Tag.E8.rank → Kˣ) :
    (coordHom a : ModGL .E8 K) = rootDiagUnit .E8 a := rfl

theorem coordHom_injective : Function.Injective (coordHom (K := K)) := by
  intro a b h
  exact CFSG.LieType.Chevalley.rootDiagUnit_injective (congrArg Subtype.val h)

theorem mem_range_coordHom_iff (g : adjointGroup .E8 K) :
    g ∈ (coordHom (K := K)).range ↔ (g : ModGL .E8 K) ∈ torusGroup .E8 K := by
  constructor
  · rintro ⟨a, rfl⟩
    exact rootDiagUnit_E8_mem_torusGroup a
  · intro hg
    obtain ⟨a, ha⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hg
    exact ⟨a, Subtype.ext ha.symm⟩

theorem mem_torusPow_iff {p : ℕ} (g : adjointGroup .E8 K) :
    g ∈ TableBExc.torusPow .E8 K p ↔ g ^ p = 1 ∧ g ∈ (coordHom (K := K)).range := by
  rw [TableBExc.mem_torusPow, mem_range_coordHom_iff]
  exact and_comm

theorem exists_rootValue_equiv [Finite K] : Nonempty (Kˣ ≃* Multiplicative (ZMod (Nat.card K - 1))) := by
  have he : Kˣ ≃* Multiplicative (ZMod (Nat.card Kˣ)) := (zmodCyclicMulEquiv inferInstance).symm
  rw [Nat.card_units] at he
  exact ⟨he⟩

@[expose] def simpleRep (k : Fin Tag.E8.rank) : adjointGroup .E8 K :=
  ⟨canonicalRep (coxeterSystem .E8) K (simple .E8 k),
    canonicalRep_mem_adjointGroup (coxeterSystem .E8) K (simple .E8 k)⟩

theorem simple_conj_coordHom (k : Fin Tag.E8.rank) (a : Fin Tag.E8.rank → Kˣ) :
    simpleRep k * coordHom a * (simpleRep k)⁻¹ =
      coordHom a * (coordHom (corTuple Tag.E8.cartan k (a k)))⁻¹ := by
  apply Subtype.ext
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, coe_coordHom, simpleRep]
  rw [canonicalRep_simple]
  have h := weylElt_conj_rootDiagUnit (τ := .E8) a k
  rw [h]
  rw [rootDiagUnit_inv, ← rootDiagUnit_mul]
  congr 1
  funext j
  simp only [Pi.mul_apply, Pi.inv_apply, corTuple, zpow_neg]

variable
  [Finite K]

theorem centralizer_le_range {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hq : p ∣ Nat.card K - 1) :
    Subgroup.centralizer ((TableBExc.torusPow .E8 K p) : Set (adjointGroup .E8 K)) ≤
      (coordHom (K := K)).range := by
  intro g hg
  apply (mem_range_coordHom_iff g).mpr
  have hpk : p ∣ Nat.card Kˣ := by rwa [Nat.card_units]
  have hCG := TableBExc.adjointGroup_inf_centralizer_torusPow_of_ne_two
    (τ := .E8) hp hp2 hpk
    (fun a _ => rootDiagUnit_E8_mem_torusGroup a)
  rw [← hCG]
  refine ⟨g.2, Subgroup.mem_centralizer_iff.mpr ?_⟩
  intro x hx
  have hxC : x ∈ adjointGroup .E8 K := torusGroup_le_adjointGroup' hx.1
  have hxV : (⟨x, hxC⟩ : adjointGroup .E8 K) ∈ TableBExc.torusPow .E8 K p :=
    ExcFrames.mem_torusPow_iff_coe.mpr hx
  exact congrArg Subtype.val ((Subgroup.mem_centralizer_iff.mp hg) ⟨x, hxC⟩ hxV)

theorem exists_frame {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2) (hq : p ∣ Nat.card K - 1) :
    ∃ (ζ : Kˣ) (_hζ : ζ ^ p = 1)
      (ι : Multiplicative (Fin Tag.E8.rank → ZMod p) →* adjointGroup .E8 K),
      orderOf ζ = p ∧ Function.Injective ι ∧ ι.range = TableBExc.torusPow .E8 K p ∧
      (∀ k s, simpleRep k * ι (Multiplicative.ofAdd s) * (simpleRep k)⁻¹ =
        ι (Multiplicative.ofAdd (TableBExc.torusAct .E8 p (simple .E8 k) s))) ∧
      (∀ g ∈ Subgroup.normalizer ((TableBExc.torusPow .E8 K p) : Set (adjointGroup .E8 K)),
        ∃ w : WeylGroup .E8, ∀ s, g * ι (Multiplicative.ofAdd s) * g⁻¹ =
          ι (Multiplicative.ofAdd (TableBExc.torusAct .E8 p w s))) := by
  have : Fact (Nat.Prime p) := ⟨hp⟩
  have : NeZero p := ⟨hp.ne_zero⟩
  have hpk : p ∣ Nat.card Kˣ := by rwa [Nat.card_units]
  obtain ⟨ζ, hζo⟩ := exists_prime_orderOf_dvd_card' p hpk
  have hζ : ζ ^ p = 1 := hζo ▸ pow_orderOf_eq_one ζ
  have hfull : ∀ a : Fin Tag.E8.rank → Kˣ, rootDiagUnit .E8 a ∈ torusGroup .E8 K :=
    rootDiagUnit_E8_mem_torusGroup
  let ι := ExcFrames.frameHom hfull ζ hζ (1 : adjointGroup .E8 K)
  have hιcoe : ∀ s : Fin Tag.E8.rank → ZMod p,
      (ι (Multiplicative.ofAdd s) : ModGL .E8 K) = ExcFrames.frameDiag ζ hζ s := by
    intro s
    simp only [ι, ExcFrames.coe_frameHom, Subgroup.coe_one, inv_one, one_mul, mul_one]
  have hdet : IsUnit ((Tag.E8.symmetrizedCartan.det : ℤ) : ZMod p) :=
    ExcFrames.isUnit_det_symmetrizedCartan (Or.inr (Or.inr rfl)) hp2
  have hι : Function.Injective ι := by
    intro s t h
    have hco := congrArg Subtype.val h
    rw [← ofAdd_toAdd s, ← ofAdd_toAdd t, hιcoe, hιcoe] at hco
    exact Multiplicative.toAdd.injective (ExcFrames.frameDiag_injective hζo hζ hdet hco)
  have hrange : ι.range = TableBExc.torusPow .E8 K p := by
    ext g
    constructor
    · rintro ⟨s, rfl⟩
      apply ExcFrames.mem_torusPow_iff_coe.mpr
      rw [← ofAdd_toAdd s, hιcoe]
      exact ExcFrames.frameDiag_mem hfull ζ hζ _
    · intro hg
      obtain ⟨s, hs⟩ := ExcFrames.exists_frameDiag_of_mem hζo hζ hdet
        (ExcFrames.mem_torusPow_iff_coe.mp hg)
      exact ⟨Multiplicative.ofAdd s, Subtype.ext ((hιcoe s).trans hs)⟩
  have hsimple : ∀ k s, simpleRep k * ι (Multiplicative.ofAdd s) * (simpleRep k)⁻¹ =
      ι (Multiplicative.ofAdd (TableBExc.torusAct .E8 p (simple .E8 k) s)) := by
    intro k s
    apply Subtype.ext
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, hιcoe, simpleRep]
    exact ExcFrames.canonicalRep_conj_frameDiag ζ hζ (simple .E8 k) s
  refine ⟨ζ, hζ, ι, hζo, hι, hrange, hsimple, ?_⟩
  intro g hg
  obtain ⟨w, hw⟩ := ExcFrames.exists_weyl_of_normalizes (Subgroup.mem_normalizer_iff.mp hg)
  refine ⟨w, fun s => ?_⟩
  apply Subtype.ext
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, hιcoe]
  rw [hw _ (ExcFrames.frameDiag_mem hfull ζ hζ s)]
  exact ExcFrames.canonicalRep_conj_frameDiag ζ hζ w s

end E8SplitTorus

theorem ggTorusTorData_E8_split_standard {K : Type} [Field K] [Finite K] [CharP K 2]
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hq : p ∣ Nat.card K - 1) :
    GGTorusTorData (Nat.card K - 1) 8 CartanMatrix.E₈ CoxeterMatrix.E₈
      (adjointGroup .E8 K) ((TableBExc.torusPow .E8 K p).map
        (MulAut.conj : adjointGroup .E8 K →* MulAut (adjointGroup .E8 K))) := by
  have : Fact (Nat.Prime p) := ⟨hp⟩
  have : NeZero p := ⟨hp.ne_zero⟩
  obtain ⟨ζ, hζ, ι, hζo, hι, hrange, hact, hnorm⟩ := E8SplitTorus.exists_frame hp hp2 hq
  let E := TableBExc.torusPow .E8 K p
  let φ := E8SplitTorus.coordHom (K := K)
  let n := E8SplitTorus.simpleRep (K := K)
  obtain ⟨l⟩ := E8SplitTorus.exists_rootValue_equiv (K := K)
  have hζ1 : ζ ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hζo
    exact hp.ne_one hζo.symm
  have hC : Tag.E8.cartan = CartanMatrix.E₈ := cartanE_eq 8
  have hM : coxeterMatrix (CFSG.LieType.Chevalley.isFiniteType_cartan .E8) = CoxeterMatrix.E₈ :=
    FrameRoute.coxeterE8_eq.symm
  suffices h : GGTorusTorData (Nat.card K - 1) Tag.E8.rank Tag.E8.cartan
      (coxeterMatrix (CFSG.LieType.Chevalley.isFiniteType_cartan .E8))
      (adjointGroup .E8 K) (E.map
        (MulAut.conj : adjointGroup .E8 K →* MulAut (adjointGroup .E8 K))) by
    rw [hM] at h
    simpa only [hC, Tag.rank] using h
  have hBC : cartanInvE8 * Tag.E8.cartan = 1 := cartanInvE8_mul
  have hCB : Tag.E8.cartan * cartanInvE8 = 1 :=
    (Matrix.mul_eq_one_comm_of_equiv (Equiv.refl (Fin Tag.E8.rank))).mp hBC
  have hCsymm : (Tag.E8.cartan).IsSymm := hC.symm ▸ CartanMatrix.E_isSymm 8
  obtain ⟨hnA, ρ, hρ, hρrange, hρsimple⟩ := exists_markedWeyl_innerHom
    (hp.odd_of_ne_two hp2) E mulAut_conj_injective_adjointGroup ι hι hrange n hact hnorm

  exact ggTorusTorData_of_scalarRootCoordinates l φ E8SplitTorus.coordHom_injective
    Tag.E8.cartan cartanInvE8 hCB hBC hCsymm center_adjointGroup_eq_bot E
    E8SplitTorus.mem_torusPow_iff ζ hζ hζ1 n hnA E8SplitTorus.simple_conj_coordHom
    (E8SplitTorus.centralizer_le_range hp hp2 hq)
    (coxeterMatrix (CFSG.LieType.Chevalley.isFiniteType_cartan .E8)) ρ hρ hρrange hρsimple

theorem ggTorusTorData_E8_split {K : Type} [Field K] [Finite K] [CharP K 2]
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hq : p ∣ Nat.card K - 1) (E : Subgroup (adjointGroup .E8 K))
    (hE : IsElemAbelian p E) (hcard : p ^ 8 ≤ Nat.card E) :
    GGTorusTorData (Nat.card K - 1) 8 CartanMatrix.E₈ CoxeterMatrix.E₈
      (adjointGroup .E8 K) (E.map
        (MulAut.conj : adjointGroup .E8 K →* MulAut (adjointGroup .E8 K))) := by
  have hT : GGExcToralRankInput .E8 K p := by
    by_cases hp3 : p = 3
    · subst hp3
      exact ggE8ThreeToralRankInput_holds K hq
    · exact ggExcToralRankInput_E8_of_ne_three hp hp2 hp3 hq
  obtain ⟨g, hg⟩ := hT E hE (by simpa only [Tag.rank] using hcard)
  let e : adjointGroup .E8 K ≃* adjointGroup .E8 K := MulAut.conj g
  have hA : (E.map (MulAut.conj : adjointGroup .E8 K →* MulAut (adjointGroup .E8 K))).map
      (MulAut.congr e).toMonoidHom = (TableBExc.torusPow .E8 K p).map
        (MulAut.conj : adjointGroup .E8 K →* MulAut (adjointGroup .E8 K)) := by
    rw [Subgroup.map_map, ← hg, Subgroup.map_map]
    exact congrArg (fun f => E.map f) (by
      apply MonoidHom.ext
      intro x
      exact congr_conj e x)
  exact torData_of_e8_model e hA (ggTorusTorData_E8_split_standard hp hp2 hq)

theorem ggTorusTorW_recipe_E8_split {K : Type} [Field K] [Finite K] [CharP K 2]
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hq : p ∣ Nat.card K - 1) :
    GGTorusTorW p 8 (Nat.card K - 1) 8 CartanMatrix.E₈ CoxeterMatrix.E₈
      (TableBExc.RecipeGroup .E8 K) (TableBExc.RecipeID .E8 K) := by
  intro L _ _ ψ A hTB
  obtain ⟨e, -, E, hE, hcard, -, hA⟩ := exists_e8_model_of_tableB ψ A hTB
  have hr : p ^ 8 ≤ Nat.card E := by rw [hcard]; exact hTB.2.2.2.2.2.1
  exact torData_of_e8_model e hA (ggTorusTorData_E8_split hp hp2 hq E hE hr)

theorem ggTorusTorW_recipe_E8_three_split {K : Type} [Field K] [Finite K] [CharP K 2]
    (hq : 3 ∣ Nat.card K - 1) :
    GGTorusTorW 3 8 (Nat.card K - 1) 8 CartanMatrix.E₈ CoxeterMatrix.E₈
      (TableBExc.RecipeGroup .E8 K) (TableBExc.RecipeID .E8 K) := by
  exact ggTorusTorW_recipe_E8_split Nat.prime_three (by norm_num) hq

theorem ggTBTorE8_holds : GGTBTorE8 := by
  intro lab _ htag
  obtain ⟨t, l, n⟩ := lab
  dsimp only at htag
  subst htag
  by_cases hminus : 3 ∣ 2 ^ n - 1
  · have hqpos : 0 < 2 ^ n := by positivity
    have hplus : ¬ 3 ∣ 2 ^ n + 1 := by omega
    simp only [ggTorEnn, ggTorME8, hplus, hminus, ↓reduceIte, Nat.sub_zero]
    intro Q hQ
    obtain ⟨K, i1, i2, hK, hQ'⟩ := hQ
    have : CharP K 2 := charP_two_of_card hK
    have hq : 3 ∣ Nat.card K - 1 := by rwa [hK]
    refine ⟨K, i1, i2, hK, hQ', ?_⟩
    change GGTorusTorW 3 8 (2 ^ n - 1) 8 CartanMatrix.E₈ CoxeterMatrix.E₈
      (TableBExc.RecipeGroup .E8 K) (TableBExc.RecipeID .E8 K)
    rw [← hK]
    exact ggTorusTorW_recipe_E8_three_split hq
  · have htwo : ¬ 3 ∣ 2 ^ n := fun h => by
      have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h
      omega
    have hplus : 3 ∣ 2 ^ n + 1 := by omega
    simp only [ggTorEnn, ggTorME8, hplus, hminus, ↓reduceIte]
    intro Q hQ
    obtain ⟨K, i1, i2, hK, hQ'⟩ := hQ
    have : CharP K 2 := charP_two_of_card hK
    have hq : 3 ∣ Nat.card K + 1 := by rwa [hK]
    refine ⟨K, i1, i2, hK, hQ', ?_⟩
    change GGTorusTorW 3 7 (2 ^ n + 1) 8 CartanMatrix.E₈ CoxeterMatrix.E₈
      (TableBExc.RecipeGroup .E8 K) (TableBExc.RecipeID .E8 K)
    rw [← hK]
    exact ggTorusTorW_recipe_E8_three_plus hq

theorem ggTBTorE8Ind_holds : GGTBTorE8Ind := by
  intro p hp hp2 _ lab _ htag hpm
  obtain ⟨t, l, n⟩ := lab
  dsimp only at htag hpm
  subst htag
  by_cases hminus : p ∣ 2 ^ n - 1
  · have hqpos : 1 ≤ 2 ^ n := Nat.one_le_two_pow
    have hplus : ¬ p ∣ 2 ^ n + 1 := by
      intro h
      have htwo : p ∣ 2 := by
        have := Nat.dvd_sub h hminus
        convert this using 1; omega
      exact hp2 ((Nat.prime_two.dvd_iff_eq hp.ne_one).mp htwo).symm
    simp only [ggTorEnn, ggTorMpm, hplus, hminus, ↓reduceIte, Nat.sub_zero]
    intro Q hQ
    obtain ⟨K, i1, i2, hK, hQ'⟩ := hQ
    have : CharP K 2 := charP_two_of_card hK
    have hq : p ∣ Nat.card K - 1 := by rwa [hK]
    refine ⟨K, i1, i2, hK, hQ', ?_⟩
    change GGTorusTorW p 8 (2 ^ n - 1) 8 CartanMatrix.E₈ CoxeterMatrix.E₈
      (TableBExc.RecipeGroup .E8 K) (TableBExc.RecipeID .E8 K)
    rw [← hK]
    exact ggTorusTorW_recipe_E8_split hp hp2 hq
  · have hplus : p ∣ 2 ^ n + 1 := (hp.dvd_mul.mp hpm).resolve_left hminus
    simp only [ggTorEnn, ggTorMpm, hplus, hminus, ↓reduceIte]
    intro Q hQ
    obtain ⟨K, i1, i2, hK, hQ'⟩ := hQ
    have : CharP K 2 := charP_two_of_card hK
    have hq : p ∣ Nat.card K + 1 := by rwa [hK]
    refine ⟨K, i1, i2, hK, hQ', ?_⟩
    change GGTorusTorW p 7 (2 ^ n + 1) 8 CartanMatrix.E₈ CoxeterMatrix.E₈
      (TableBExc.RecipeGroup .E8 K) (TableBExc.RecipeID .E8 K)
    rw [← hK]
    exact ggTorusTorW_recipe_E8_plus hp hp2 hq

end CFSG.StandardType
