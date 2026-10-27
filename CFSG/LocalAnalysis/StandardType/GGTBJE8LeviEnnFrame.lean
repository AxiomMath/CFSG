module

public import CFSG.LocalAnalysis.StandardType.GGTorusE8Scalar
public import CFSG.LocalAnalysis.StandardType.GGExcMinusCompField
public import CFSG.LocalAnalysis.StandardType.GGTBTorE8Plus
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.ExcRoots

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.AlgebraicGroups

theorem e8Enn_frame
    {K : Type} [Field K] [Finite K] [CharP K 2]
    {p : ℕ} [Fact p.Prime] [NeZero p] (hp2 : p ≠ 2) (hq : p ∣ Nat.card K + 1)
    (E : Subgroup (adjointGroup .E8 K)) (hE : IsElemAbelian p E) (hcard : p ^ 7 ≤ Nat.card E)
    (hSC : ∀ g : adjointGroup .E8 K, (∀ x ∈ E, g * x = x * g) → g ^ p = 1 → g ∈ E) :
    ∃ (ζ : (AlgebraicClosure K)ˣ) (hζ : ζ ^ p = 1)
      (ι₀ : Multiplicative (Fin Tag.E8.rank → ZMod p) →* adjointGroup .E8 K)
      (n : Fin Tag.E8.rank → adjointGroup .E8 K)
      (S : LangSetup .E8 (AlgebraicClosure K) 5)
      (ι : adjointGroup .E8 K →* ModGL .E8 (AlgebraicClosure K)),
      orderOf ζ = p ∧ Function.Injective ι₀ ∧ ι₀.range = E ∧
      (∀ k s, n k * ι₀ (Multiplicative.ofAdd s) * (n k)⁻¹ =
        ι₀ (Multiplicative.ofAdd (TableBExc.torusAct .E8 p (simple .E8 k) s))) ∧
      (∀ g ∈ Subgroup.normalizer (E : Set (adjointGroup .E8 K)),
        ∃ v : WeylGroup .E8, ∀ s,
          g * ι₀ (Multiplicative.ofAdd s) * g⁻¹ =
            ι₀ (Multiplicative.ofAdd (TableBExc.torusAct .E8 p v s))) ∧
      S.D.q = Nat.card K ∧ Function.Injective ι ∧ ι.range = S.Γ ∧
      (∀ s, ι (ι₀ (Multiplicative.ofAdd s)) = ExcFrames.frameDiag ζ hζ s) ∧
      (∀ s, ExcFrames.frameDiag ζ hζ s ∈ S.D.torus) ∧
      (∀ γ, IsRoot .E8 γ → S.ρ γ = -γ) ∧
      ∃ wt : GGTorusTorWit (Nat.card K + 1) 8 (adjointGroup .E8 K)
          (E.map (MulAut.conj : adjointGroup .E8 K →* MulAut (adjointGroup .E8 K))),
        (∀ k, wt.n k = n k) ∧ wt.Holds CartanMatrix.E₈ CoxeterMatrix.E₈ := by
  classical
  have hp : p.Prime := Fact.out
  obtain ⟨F, Fr, ζ, hζ, ι₀, n, hFr, hΦ, hw, hζo, hι₀, hrange, hbase, hnb, hact, hnorm⟩ :=
    E8ScalarTorus.exists_frame_of_selfCentralizing hp hp2 hq E hE hcard hSC
  have hg0C : F.D.g0 ∈ adjointGroup .E8 (AlgebraicClosure K) := F.D.g0_mem
  have hg0 : Units.map (entrywiseHom Fr) F.D.g0 =
      F.D.g0 * canonicalRep (coxeterSystem .E8) (AlgebraicClosure K) F.w := by
    rw [← hΦ, ← F.n_eq]
    exact F.D.lang
  obtain ⟨S, ι, hSΦ, hSq, hSn, hι, hιrange, hιframe, hιtorus⟩ :=
    ExcMinusField.exists_langSetup_of_langFrame (Or.inr rfl) hFr hg0C hg0 hbase
  have hFrq : ∀ c, Fr c = c ^ S.D.q := fun c => by rw [hSq]; exact hFr c
  have hρroot : ∀ γ, IsRoot .E8 γ → S.ρ γ = -γ := by
    intro γ hγ
    rw [S.rho_eq_smul_of_frob hFrq hSΦ hSn hγ, hw]
  let μ := rootsOfUnity (Nat.card K + 1) (AlgebraicClosure K)
  let φ := E8ScalarTorus.coordHom F.D Fr hFr hΦ F.n_eq hw
  have hφ : Function.Injective φ :=
    E8ScalarTorus.coordHom_injective F.D Fr hFr hΦ F.n_eq hw
  obtain ⟨l⟩ := E8ScalarTorus.exists_rootValue_equiv (K := K)
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
  have hC : Tag.E8.cartan = CartanMatrix.E₈ := cartanE_eq 8
  have hgg : GGIntCartan CoxeterMatrix.E₈ (Tag.cartan .E8) := by
    rw [show Tag.cartan .E8 = CartanMatrix.E 8 from cartanE_eq 8]
    exact ggIntCartan_E₈
  have hM : CFSG.LieType.RootSystem.coxeterMatrix
      (CFSG.LieType.Chevalley.isFiniteType_cartan .E8) = CoxeterMatrix.E₈ :=
    coxeterMatrix_eq_of_ggIntCartan (isFiniteType_cartan .E8) hgg
  have hBC : CFSG.RankThree.PartOne.KE.cartanInvE8 * Tag.E8.cartan = 1 :=
    CFSG.RankThree.PartOne.KE.cartanInvE8_mul
  have hCB : Tag.E8.cartan * CFSG.RankThree.PartOne.KE.cartanInvE8 = 1 :=
    (Matrix.mul_eq_one_comm_of_equiv (Equiv.refl (Fin Tag.E8.rank))).mp hBC
  have hCsymm : (Tag.E8.cartan).IsSymm := hC.symm ▸ CartanMatrix.E_isSymm 8
  obtain ⟨hnA, ρ, hρ, hρrange, hρsimple⟩ := exists_markedWeyl_innerHom
    (hp.odd_of_ne_two hp2) E mulAut_conj_injective_adjointGroup ι₀ hι₀ hrange n hact hnorm
  have hnformula : ∀ k (a : Fin Tag.E8.rank → μ),
      n k * φ a * (n k)⁻¹ =
        φ a * (φ (corTuple Tag.E8.cartan.transpose k (a k)))⁻¹ := by
    intro k a
    have h := E8ScalarTorus.simple_conj_coordHom F.D Fr hFr hΦ F.n_eq hw k (n k) (hnb k) a
    change n k * φ a * (n k)⁻¹ = φ a * (φ (corTuple Tag.E8.cartan.transpose k (a k)))⁻¹
    rw [hCsymm.eq]
    have hcor : E8ScalarTorus.corootHom F.D Fr hFr hΦ F.n_eq hw k (a k) =
        φ (corTuple Tag.E8.cartan k (a k)) := rfl
    rw [hcor] at h
    exact h
  have hcent : Subgroup.centralizer (E : Set (adjointGroup .E8 K)) ≤ φ.range := by
    have hlong : ExcIsLongest .E8 F.w := by
      intro α hα hpos i
      rw [hw, Pi.neg_apply]
      exact neg_nonpos.mpr (hpos i)
    exact E8ScalarTorus.centralizer_le_range hp hp2 F Fr hFr hΦ hq hlong hw
  obtain ⟨w, -, -, -, hwn, hwh⟩ :=
    exists_ggTorusTorWit_of_scalarRootCoordinates_columns_mod l φ hφ Tag.E8.cartan
      CFSG.RankThree.PartOne.KE.cartanInvE8 (by rw [hCB, map_one]) (by rw [hBC, map_one])
      center_adjointGroup_eq_bot E
      (fun g => E8ScalarTorus.mem_primeSubgroup_iff F Fr hFr hΦ hw g) z hz hz1 n hnA
      hnformula hcent
      (CFSG.LieType.RootSystem.coxeterMatrix
        (CFSG.LieType.Chevalley.isFiniteType_cartan .E8)) ρ hρ hρrange hρsimple
  have hwh' : w.Holds CartanMatrix.E₈ CoxeterMatrix.E₈ := by
    rw [hM] at hwh
    simpa only [hC] using hwh
  exact ⟨ζ, hζ, ι₀, n, S, ι, hζo, hι₀, hrange, hact, hnorm, hSq, hι, hιrange,
    hιframe, hιtorus, hρroot, w, hwn, hwh'⟩

end CFSG.StandardType

end
