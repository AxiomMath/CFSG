module

public import CFSG.LocalAnalysis.StandardType.GGTBJE8LeviEnnFrame
public import CFSG.LocalAnalysis.StandardType.GGTorusLangCoordinates
public import CFSG.LocalAnalysis.StandardType.GGTBTorE7
public import CFSG.RankThree.PartOne.KE.EvenE7E8QPlusTorus
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.TwCompSUE7

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.AlgebraicGroups

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem e7Enn_frame
    {K : Type} [Field K] [Finite K] [CharP K 2]
    {p : ℕ} [Fact p.Prime] [NeZero p] (hp2 : p ≠ 2) (hq : p ∣ Nat.card K + 1)
    (E : Subgroup (adjointGroup .E7 K)) (hE : IsElemAbelian p E) (hcard : p ^ 6 ≤ Nat.card E)
    (hSC : ∀ g : adjointGroup .E7 K, (∀ x ∈ E, g * x = x * g) → g ^ p = 1 → g ∈ E) :
    ∃ (ζ : (AlgebraicClosure K)ˣ) (hζ : ζ ^ p = 1)
      (ι₀ : Multiplicative (Fin Tag.E7.rank → ZMod p) →* adjointGroup .E7 K)
      (n : Fin Tag.E7.rank → adjointGroup .E7 K)
      (S : LangSetup .E7 (AlgebraicClosure K) 5)
      (ι : adjointGroup .E7 K →* ModGL .E7 (AlgebraicClosure K)),
      orderOf ζ = p ∧ Function.Injective ι₀ ∧ ι₀.range = E ∧
      (∀ k s, n k * ι₀ (Multiplicative.ofAdd s) * (n k)⁻¹ =
        ι₀ (Multiplicative.ofAdd (TableBExc.torusAct .E7 p (simple .E7 k) s))) ∧
      (∀ g ∈ Subgroup.normalizer (E : Set (adjointGroup .E7 K)),
        ∃ v : WeylGroup .E7, ∀ s,
          g * ι₀ (Multiplicative.ofAdd s) * g⁻¹ =
            ι₀ (Multiplicative.ofAdd (TableBExc.torusAct .E7 p v s))) ∧
      S.D.q = Nat.card K ∧ Function.Injective ι ∧ ι.range = S.Γ ∧
      (∀ s, ι (ι₀ (Multiplicative.ofAdd s)) = ExcFrames.frameDiag ζ hζ s) ∧
      (∀ s, ExcFrames.frameDiag ζ hζ s ∈ S.D.torus) ∧
      (∀ γ, IsRoot .E7 γ → S.ρ γ = -γ) ∧
      ∃ wt : GGTorusTorWit (Nat.card K + 1) 7 (adjointGroup .E7 K)
          (E.map (MulAut.conj : adjointGroup .E7 K →* MulAut (adjointGroup .E7 K))),
        (∀ k, wt.n k = n k) ∧ wt.Holds CartanMatrix.E₇ CoxeterMatrix.E₇ := by
  classical
  have hp : p.Prime := Fact.out
  obtain ⟨F, Fr, ζ, hζ, ι₀, n, hFr, hΦ, hw, hζo, hι₀, hrange, hbase, hnb, hact, hnorm⟩ :=
    exists_e7_scalar_frame hp hp2 hq E hE hcard hSC
  have hg0C : F.D.g0 ∈ adjointGroup .E7 (AlgebraicClosure K) := F.D.g0_mem
  have hg0 : Units.map (entrywiseHom Fr) F.D.g0 =
      F.D.g0 * canonicalRep (coxeterSystem .E7) (AlgebraicClosure K) F.w := by
    rw [← hΦ, ← F.n_eq]
    exact F.D.lang
  obtain ⟨S, ι, hSΦ, hSq, hSn, hι, hιrange, hιframe, hιtorus⟩ :=
    ExcMinusField.exists_langSetup_of_langFrame (Or.inl rfl) hFr hg0C hg0 hbase
  have hFrq : ∀ c, Fr c = c ^ S.D.q := fun c => by rw [hSq]; exact hFr c
  have hρroot : ∀ γ, IsRoot .E7 γ → S.ρ γ = -γ := by
    intro γ hγ
    rw [S.rho_eq_smul_of_frob hFrq hSΦ hSn hγ, hw]
  let μ := rootsOfUnity (Nat.card K + 1) (AlgebraicClosure K)
  have hrat : ∀ X : Subgroup (ModGL .E7 (AlgebraicClosure K)), Finite X →
      X ≤ adjointGroup .E7 (AlgebraicClosure K) →
      (∀ x ∈ X, Units.map (entrywiseHom Fr) x = x) →
        X ≤ (adjointGroup .E7 K).map (baseChangeGL (algebraMap K (AlgebraicClosure K))) :=
    fun X hfin hXC hXF => by
      let : Finite X := hfin
      exact finite_fixed_le_map_adjointGroup_E7 Fr hFr X hXC hXF
  let φ := ScalarLangTorus.coordHom F.D Fr hFr hΦ F.n_eq hw hrat
  have hφ : Function.Injective φ :=
    ScalarLangTorus.coordHom_injective F.D Fr hFr hΦ F.n_eq hw hrat
  obtain ⟨l⟩ := ScalarLangTorus.exists_rootValue_equiv (K := K)
  have hζm : ζ ^ (Nat.card K + 1) = 1 := by
    obtain ⟨k, hk⟩ := hq
    rw [hk, pow_mul, hζ, one_pow]
  let z : μ := ⟨ζ, (mem_rootsOfUnity _ _).mpr hζm⟩
  have hz : z ^ p = 1 := Subtype.ext hζ
  have hz1 : z ≠ 1 := by
    intro h
    have hζ1 : ζ = 1 := congrArg Subtype.val h
    rw [hζ1, orderOf_one] at hζo
    exact hp.ne_one hζo.symm
  have hC : Tag.E7.cartan = CartanMatrix.E 7 := cartanE_eq 7
  have hM : CFSG.LieType.RootSystem.coxeterMatrix
      (CFSG.LieType.Chevalley.isFiniteType_cartan .E7) = CoxeterMatrix.E₇ :=
    FrameRoute.coxeterE7_eq.symm
  have hm : Odd (Nat.card K + 1) := by
    let : Fintype K := Fintype.ofFinite K
    have hEven : Even (Nat.card K) := by
      rw [Nat.even_iff, Nat.card_eq_fintype_card]
      exact FiniteField.even_card_of_char_two (ringChar.eq K 2)
    exact hEven.add_one
  have hdet : IsUnit ((Tag.E7.cartan.det : ℤ) : ZMod (Nat.card K + 1)) := by
    rw [det_cartan_E7]
    simpa using (ZMod.isUnit_iff_coprime 2 (Nat.card K + 1)).mpr
      (Nat.coprime_two_left.mpr hm)
  obtain ⟨B, hCB', hBC'⟩ := exists_int_matrix_inverse_mod_of_isUnit_det Tag.E7.cartan hdet
  have hCsymm : (Tag.E7.cartan).IsSymm := hC.symm ▸ CartanMatrix.E_isSymm 7
  obtain ⟨hnA, ρ, hρ, hρrange, hρsimple⟩ := exists_markedWeyl_innerHom
    (hp.odd_of_ne_two hp2) E mulAut_conj_injective_adjointGroup ι₀ hι₀ hrange n hact hnorm
  have hnformula : ∀ k (a : Fin Tag.E7.rank → μ),
      n k * φ a * (n k)⁻¹ =
        φ a * (φ (corTuple Tag.E7.cartan.transpose k (a k)))⁻¹ := by
    intro k a
    rw [hCsymm.eq]
    exact ScalarLangTorus.simple_conj_coordHom F.D Fr hFr hΦ F.n_eq hw hrat k (n k) (hnb k) a
  have hcent : Subgroup.centralizer (E : Set (adjointGroup .E7 K)) ≤ φ.range := by
    have hlong : ExcIsLongest .E7 F.w := by
      intro α hα hpos i
      rw [hw, Pi.neg_apply]
      exact neg_nonpos.mpr (hpos i)
    exact e7_scalar_centralizer_le_coordinates hp hp2 F Fr hFr hΦ hq hlong hw
  obtain ⟨w, -, -, -, hwn, hwh⟩ :=
    exists_ggTorusTorWit_of_scalarRootCoordinates_columns_mod l φ hφ Tag.E7.cartan B hCB' hBC'
      center_adjointGroup_eq_bot E
      (fun g => e7_scalar_mem_iff_coordinates F Fr hFr hΦ hw g) z hz hz1 n hnA
      hnformula hcent
      (CFSG.LieType.RootSystem.coxeterMatrix
        (CFSG.LieType.Chevalley.isFiniteType_cartan .E7)) ρ hρ hρrange hρsimple
  have hwh' : w.Holds CartanMatrix.E₇ CoxeterMatrix.E₇ := by
    rw [hM] at hwh
    simpa only [hC] using hwh
  exact ⟨ζ, hζ, ι₀, n, S, ι, hζo, hι₀, hrange, hact, hnorm, hSq, hι, hιrange,
    hιframe, hιtorus, hρroot, w, hwn, hwh'⟩

end CFSG.StandardType

end
