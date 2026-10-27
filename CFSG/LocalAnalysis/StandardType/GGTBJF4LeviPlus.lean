module

public import CFSG.LocalAnalysis.StandardType.GGTBJF4LeviSplit
public import CFSG.LocalAnalysis.StandardType.GGLangRootSL2Rational
public import CFSG.LocalAnalysis.StandardType.GGExcMinusCompField
public import CFSG.LocalAnalysis.StandardType.GGNbrInnerWeylExcPlusLift
public import CFSG.LocalAnalysis.StandardType.GGTBJETypeCells
import CFSG.LocalAnalysis.StandardType.GGPhiTwoRootGenF4ThreeFrame
import CFSG.LocalAnalysis.StandardType.GGF4ThreeSCCube
import CFSG.LocalAnalysis.StandardType.GGF4ThreeSCCubeHolds

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.AlgebraicGroups

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem langDescent_F4
    {K : Type} [Field K] [Finite K] {L : Type} [Field L] [IsAlgClosed L] [Algebra K L]
    {Fr : L →+* L} (hFr : ∀ c, Fr c = c ^ Nat.card K) (D : LangDatum .F4 L)
    (hΦ : D.Φ = Units.map (entrywiseHom Fr)) (p : ℕ) :
    LangDescent D p ((baseChangeGL (algebraMap K L)).comp (adjointGroup .F4 K).subtype) := by
  classical
  have hfix : D.fix = (adjointGroup .F4 K).map (baseChangeGL (algebraMap K L)) := by
    rw [← CFSG.LieType.Chevalley.F4_frobenius_fixed_eq_map Fr hFr, LangDatum.fix, hΦ]
  have hrange : ((baseChangeGL (algebraMap K L)).comp (adjointGroup .F4 K).subtype).range =
      (adjointGroup .F4 K).map (baseChangeGL (algebraMap K L)) := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  haveI : Finite (ModGL .F4 K) := finite_modGL
  haveI : Group.IsPerfect ↥(adjointGroup .F4 K) := CFSG.LieType.Steinberg.Adjoint.isPerfect_f4 K
  refine ⟨?_, by rw [hrange, hfix], fun P hP _ => by rw [hrange, ← hfix]; exact hP, ?_⟩
  · rw [hfix]
    exact Finite.of_surjective
      (fun x : ↥(adjointGroup .F4 K) =>
        (⟨baseChangeGL (algebraMap K L) x, x, x.2, rfl⟩ :
          ↥((adjointGroup .F4 K).map (baseChangeGL (algebraMap K L)))))
      (by
        rintro ⟨_, x, hx, rfl⟩
        exact ⟨⟨x, hx⟩, rfl⟩)
  · have hperf : ⁅adjointGroup .F4 K, adjointGroup .F4 K⁆ = adjointGroup .F4 K := by
      rw [← Subgroup.map_subtype_commutator, Group.IsPerfect.commutator_eq_top,
        ← MonoidHom.range_eq_map, Subgroup.range_subtype]
    rw [hfix, hrange, ← Subgroup.map_commutator, hperf]

private theorem f4lp_two_le {p n : ℕ} (hp5 : 5 ≤ p) (hpn : p ∣ 2 ^ n + 1) : 2 ≤ n := by
  by_contra h
  have hle := Nat.le_of_dvd (by positivity) hpn
  interval_cases n <;> omega

private theorem f4lp_langFrame
    {K : Type} [Field K] [Finite K] [CharP K 2] {p : ℕ} [Fact p.Prime]
    (hq : p ∣ Nat.card K + 1) {E : Subgroup (adjointGroup .F4 K)} (hE : IsElemAbelian p E)
    (hSC : ∀ x ∈ Subgroup.centralizer (E : Set (adjointGroup .F4 K)), x ^ p = 1 → x ∈ E)
    (hpE : 5 ≤ p ∨ (p = 3 ∧ 3 ^ 4 ≤ Nat.card E)) :
    ∃ (Fr : AlgebraicClosure K →+* AlgebraicClosure K) (g0 : ModGL .F4 (AlgebraicClosure K))
      (ζ : (AlgebraicClosure K)ˣ) (hζ : ζ ^ p = 1)
      (ι₀ : Multiplicative (Fin Tag.F4.rank → ZMod p) →* adjointGroup .F4 K),
      (∀ c, Fr c = c ^ Nat.card K) ∧ g0 ∈ adjointGroup .F4 (AlgebraicClosure K) ∧
      Units.map (entrywiseHom Fr) g0 = g0 * canonicalRep (coxeterSystem .F4)
        (AlgebraicClosure K) CFSG.HardMathSupport.Timmesfeld.CrossChar.f4Neg ∧
      orderOf ζ = p ∧ Function.Injective ι₀ ∧ ι₀.range = E ∧
      ∀ s : Fin Tag.F4.rank → ZMod p,
        baseChangeGL (algebraMap K (AlgebraicClosure K))
            ((ι₀ (Multiplicative.ofAdd s) : adjointGroup .F4 K) : ModGL .F4 K) =
          g0 * ExcFrames.frameDiag ζ hζ s * g0⁻¹ := by
  rcases hpE with hp5 | ⟨rfl, h4⟩
  · exact exists_langFrame_F4_of_sc hp5 hq hE hSC
  · exact exists_langFrame_F4_three hq hE h4 hSC

theorem f4Enn_frame
    {K : Type} [Field K] [Finite K] [CharP K 2]
    {p : ℕ} [Fact p.Prime] [NeZero p] (hq : p ∣ Nat.card K + 1)
    (E : Subgroup (adjointGroup .F4 K)) (hE : IsElemAbelian p E)
    (hSC : ∀ g : adjointGroup .F4 K, (∀ x ∈ E, g * x = x * g) → g ^ p = 1 → g ∈ E)
    (hpE : 5 ≤ p ∨ (p = 3 ∧ 3 ^ 4 ≤ Nat.card E)) :
    ∃ (ζ : (AlgebraicClosure K)ˣ) (hζ : ζ ^ p = 1)
      (ι₀ : Multiplicative (Fin Tag.F4.rank → ZMod p) →* adjointGroup .F4 K)
      (n : Fin Tag.F4.rank → adjointGroup .F4 K)
      (S : LangSetup .F4 (AlgebraicClosure K) 5)
      (ι : adjointGroup .F4 K →* ModGL .F4 (AlgebraicClosure K)),
      orderOf ζ = p ∧ Function.Injective ι₀ ∧ ι₀.range = E ∧
      (∀ k s, n k * ι₀ (Multiplicative.ofAdd s) * (n k)⁻¹ =
        ι₀ (Multiplicative.ofAdd (TableBExc.torusAct .F4 p (simple .F4 k) s))) ∧
      S.D.q = Nat.card K ∧ Function.Injective ι ∧ ι.range = S.Γ ∧
      (∀ s, ι (ι₀ (Multiplicative.ofAdd s)) = ExcFrames.frameDiag ζ hζ s) ∧
      (∀ s, ExcFrames.frameDiag ζ hζ s ∈ S.D.torus) ∧
      (∀ γ, IsRoot .F4 γ → S.ρ γ = -γ) ∧
      ∃ wt : GGTorusTorWit (Nat.card K + 1) 4 (adjointGroup .F4 K)
          (E.map (MulAut.conj : adjointGroup .F4 K →* MulAut (adjointGroup .F4 K))),
        (∀ k, wt.n k = n k) ∧ wt.Holds CartanMatrix.F₄ CoxeterMatrix.F₄ := by
  classical
  have hp : p.Prime := Fact.out
  have hSC' : ∀ x ∈ Subgroup.centralizer (E : Set (adjointGroup .F4 K)), x ^ p = 1 → x ∈ E :=
    fun x hx hxp => hSC x (fun c hc => (Subgroup.mem_centralizer_iff.mp hx c hc).symm) hxp
  have hp2 : p ≠ 2 := by rcases hpE with h | ⟨h, -⟩ <;> omega
  obtain ⟨Fr, g0, ζ, hζ, D, φ, n, ι₀, hFr, hg0C, hg0, hΦ, hn, hw, hζo, hι₀, hrange,
    hbase, hD, hφbase, hφ, hφrange, hnb, hact, hnorm, hEiff, hcent, hFormula⟩ :=
    F4NonsplitFrame.exists_nonsplit_frame_data_of_langFrame
      (by rcases hpE with h | ⟨h, -⟩ <;> omega) hq hE hSC' (f4lp_langFrame hq hE hSC' hpE)
  obtain ⟨S, ι, hSΦ, hSq, hSn, hι, hιrange, hιframe, hιtorus⟩ :=
    ExcMinusField.exists_langSetup_of_langFrame_of_descent hFr hg0C hg0 hbase
      (fun a => CFSG.RankThree.Chevalley.F4_rootDiagUnit_mem_torusGroup a)
      (fun D' hΦ' => langDescent_F4 hFr D' hΦ' 7)
  have hFrq : ∀ c, Fr c = c ^ S.D.q := fun c => by rw [hSq]; exact hFr c
  have hρroot : ∀ γ, IsRoot .F4 γ → S.ρ γ = -γ := by
    intro γ hγ
    rw [S.rho_eq_smul_of_frob hFrq hSΦ hSn hγ, hw]
  obtain ⟨l⟩ := E8ScalarTorus.exists_rootValue_equiv (K := K)
  have hζm : ζ ^ (Nat.card K + 1) = 1 := by
    obtain ⟨d, hd⟩ := hq
    rw [hd, pow_mul, hζ, one_pow]
  let z : rootsOfUnity (Nat.card K + 1) (AlgebraicClosure K) :=
    ⟨ζ, (mem_rootsOfUnity _ _).mpr hζm⟩
  have hz : z ^ p = 1 := Subtype.ext hζ
  have hz1 : z ≠ 1 := by
    intro h
    have h1 : ζ = 1 := congrArg Subtype.val h
    rw [h1, orderOf_one] at hζo
    exact hp.ne_one hζo.symm
  obtain ⟨hnA, ρ, hρ, hρrange, hρsimple⟩ := exists_markedWeyl_innerHom
    (hp.odd_of_ne_two hp2) E mulAut_conj_injective_adjointGroup ι₀ hι₀ hrange n hact hnorm
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
  have hFormulaColumn : ∀ k
      (a : Fin Tag.F4.rank → rootsOfUnity (Nat.card K + 1) (AlgebraicClosure K)),
      n k * φ a * (n k)⁻¹ =
        φ a * (φ (corTuple Tag.F4.cartan.transpose.transpose k (a k)))⁻¹ := by
    simpa only [Matrix.transpose_transpose] using hFormula'
  obtain ⟨w, -, -, -, hwn, hwh⟩ :=
    exists_ggTorusTorWit_of_scalarRootCoordinates_columns_mod l φ hφ Tag.F4.cartan.transpose
      cartanInvF4.transpose (by rw [hCB, map_one]) (by rw [hBC, map_one])
      center_adjointGroup_eq_bot E hEiff z hz hz1 n hnA hFormulaColumn hcent
      (CFSG.LieType.RootSystem.coxeterMatrix
        (CFSG.LieType.Chevalley.isFiniteType_cartan .F4)) ρ hρ hρrange hρsimple
  have hC : Tag.F4.cartan.transpose = CartanMatrix.F₄ := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hM : CFSG.LieType.RootSystem.coxeterMatrix
      (CFSG.LieType.Chevalley.isFiniteType_cartan .F4) = CoxeterMatrix.F₄ :=
    FrameRoute.coxeterF4_eq.symm
  rw [hM, hC] at hwh
  exact ⟨ζ, hζ, ι₀, n, S, ι, hζo, hι₀, hrange, hact, hSq, hι, hιrange, hιframe, hιtorus,
    hρroot, w, hwn, hwh⟩

theorem f4Enn_leviFrame
    {K : Type} [Field K] [Finite K] [CharP K 2] {p : ℕ} [Fact p.Prime]
    {n : ℕ} (hn2 : 2 ≤ n) (hq : Nat.card K = 2 ^ n) (hpn : p ∣ 2 ^ n + 1)
    (E : Subgroup (adjointGroup .F4 K)) (hE : IsElemAbelian p E)
    (hSC : ∀ g : adjointGroup .F4 K, (∀ c ∈ E, g * c = c * g) → g ^ p = 1 → g ∈ E)
    (hpE : 5 ≤ p ∨ (p = 3 ∧ 3 ^ 4 ≤ Nat.card E)) :
    GGF4LeviFrame p E := by
  have hp2 : p ≠ 2 := by rcases hpE with h | ⟨h, -⟩ <;> omega
  have hpK : p ∣ Nat.card K + 1 := by rw [hq]; exact hpn
  obtain ⟨ζ, hζ, ιT, nk, S, ι, hζo, hιTinj, hιTrange, hact, hSq, hιinj, hιrange, hιιT, hT, hρ,
    wt, hwn, hwt⟩ := f4Enn_frame (K := K) hpK E hE hSC hpE
  have hq2 : S.D.q = 2 ^ n := by rw [hSq, hq]
  refine ⟨AlgebraicClosure K, inferInstance, ζ, hζ, ιT, nk, _, wt, hζo, hιTinj, hιTrange, hact,
    hwn, hwt, fun t ht Y hY => ?_⟩
  obtain ⟨i, hi, hCENT⟩ := e8Enn_class (K := K) hp2 S ι hιinj hιrange hιιT hT
    (fun γ hγ => Or.inr (hρ γ hγ)) ht hY
  exact ⟨i, hCENT, fun _ _ _ _ => LangRat.rationalComponent_realizes_rootReflection S ι hιinj
    hιιT hn2 hq2 i (fun γ hγ => hρ γ ((isRootComponent_componentRoots i).isRoot γ hγ)) hi⟩

theorem ggF4Enn_model_L
    (hRig : GGLabelRigidInput) {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K) {n : ℕ}
    (hΛ : LargeEvenInLambda2 (⟨.F4, 0, n⟩ : LargeEvenLabel))
    (hL : GGHasLabel (⟨.F4, 0, n⟩ : LargeEvenLabel) (↥L ⧸ Subgroup.center ↥L))
    (hp5 : 5 ≤ p) (hpn : p ∣ 2 ^ n + 1) :
    ∃ (hN : Bs ≤ Subgroup.normalizer (L : Set G)) (Fq : Type) (_ : Field Fq) (_ : Finite Fq)
      (_ : CharP Fq 2), Nat.card Fq = 2 ^ n ∧
      ∃ (e : ↥L ≃* adjointGroup .F4 Fq) (E : Subgroup (adjointGroup .F4 Fq)),
        IsElemAbelian p E ∧
        (∀ g : adjointGroup .F4 Fq, (∀ c ∈ E, g * c = c * g) → g ^ p = 1 → g ∈ E) ∧
        (ggGamma L hN).range.map (MulAut.congr e).toMonoidHom =
          E.map (MulAut.conj : adjointGroup .F4 Fq →* MulAut (adjointGroup .F4 Fq)) := by
  classical
  have hp : p.Prime := Fact.out
  have hp2 : p ≠ 2 := by omega
  have hml : LargeEvenMarking ↥L (fun _ _ _ I _ θ => Bs ≤ Subgroup.normalizer (L : Set G) ∧
      ∀ b ∈ Bs, ∃ φ ∈ I, LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) φ) :=
    hH.2.2.1.1
  obtain ⟨hLperf, _lab', R, _instR, _I, _F, θ, _hlab', hmark⟩ :=
    largeEvenMarking_exists' hml
  obtain ⟨hNmark, _hind⟩ := hmark
  obtain ⟨R₀, _instR₀, _finR₀, _hR₀card, ⟨⟨θ₀⟩, hlift₀⟩⟩ :=
    (largeEvenLabelAll_torusLift_excPlus (p := p) (lab := (⟨.F4, 0, n⟩ : LargeEvenLabel))
      hp hp2 ⟨Or.inr (Or.inr rfl), hpn⟩) _ hL
  have hlift : GGTorusLift p 3 R :=
    TableBF4.ggTorusLift_of_mulEquiv (θ.symm.trans θ₀) hlift₀
  have hlb : p ^ 3 ≤ Nat.card (ggGamma L hNmark).range :=
    (card_range_ggGamma_bstar_ge hH.1 hLperf θ hNmark hlift).1
  obtain ⟨Fq, _instFq, _instFin, _instChar, hFqcard, e, hZL, _hN', hinner⟩ :=
    ggF4_model hRig (f4lp_two_le hp5 hpn) hΛ hH.2.2.1.1 hL
  obtain ⟨E, hEel, -, hEsc, hArange⟩ :=
    e8Enn_adjointModel hH.1.2.1.2.1 hH.1.2.1.2.2.2 e hZL hinner hNmark hlb
  exact ⟨hNmark, Fq, inferInstance, inferInstance, inferInstance, hFqcard, e, E,
    hEel, hEsc, hArange⟩

theorem ggF4Enn_model_K
    (hRig : GGLabelRigidInput) {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K) {n : ℕ}
    (hΛ : LargeEvenInLambda2 (⟨.F4, 0, n⟩ : LargeEvenLabel))
    (hK : GGHasLabel (⟨.F4, 0, n⟩ : LargeEvenLabel) (↥K ⧸ Subgroup.center ↥K))
    (hp5 : 5 ≤ p) (hpn : p ∣ 2 ^ n + 1) :
    ∃ (hN : Bs ≤ Subgroup.normalizer (K : Set G)) (Fq : Type) (_ : Field Fq) (_ : Finite Fq)
      (_ : CharP Fq 2), Nat.card Fq = 2 ^ n ∧
      ∃ (e : ↥K ≃* adjointGroup .F4 Fq) (E : Subgroup (adjointGroup .F4 Fq)),
        IsElemAbelian p E ∧
        (∀ g : adjointGroup .F4 Fq, (∀ c ∈ E, g * c = c * g) → g ^ p = 1 → g ∈ E) ∧
        (ggGamma K hN).range.map (MulAut.congr e).toMonoidHom =
          E.map (MulAut.conj : adjointGroup .F4 Fq →* MulAut (adjointGroup .F4 Fq)) := by
  classical
  have hp : p.Prime := Fact.out
  have hp2 : p ≠ 2 := by omega
  have hnb : GGNbr p B x D J y K := hH.2.2.2.2.1
  have hmk : LargeEvenMarking ↥K (fun _ _ _ I _ θ => Bs ≤ Subgroup.normalizer (K : Set G) ∧
      ∀ b ∈ Bs, ∃ φ ∈ I, LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) φ) :=
    hH.2.2.1.2 y K hnb
  obtain ⟨hKperf, _lab', R, _instR, _I, _F, θ, _hlab', hmark⟩ :=
    largeEvenMarking_exists' hmk
  obtain ⟨hNmark, _hind⟩ := hmark
  obtain ⟨R₀, _instR₀, _finR₀, _hR₀card, ⟨⟨θ₀⟩, hlift₀⟩⟩ :=
    (largeEvenLabelAll_torusLift_excPlus (p := p) (lab := (⟨.F4, 0, n⟩ : LargeEvenLabel))
      hp hp2 ⟨Or.inr (Or.inr rfl), hpn⟩) _ hK
  have hlift : GGTorusLift p 3 R :=
    TableBF4.ggTorusLift_of_mulEquiv (θ.symm.trans θ₀) hlift₀
  have hlb : p ^ 3 ≤ Nat.card (ggGamma K hNmark).range :=
    pow_le_card_range_ggGamma_bstar_of_torusLift hH.1 hnb hKperf θ hNmark hlift
  obtain ⟨Fq, _instFq, _instFin, _instChar, hFqcard, e, hZL, _hN', hinner⟩ :=
    ggF4_model hRig (f4lp_two_le hp5 hpn) hΛ (hH.2.2.1.2 y K hnb) hK
  obtain ⟨E, hEel, -, hEsc, hArange⟩ :=
    e8Enn_adjointModel hH.1.2.1.2.1 hH.1.2.1.2.2.2 e hZL hinner hNmark hlb
  exact ⟨hNmark, Fq, inferInstance, inferInstance, inferInstance, hFqcard, e, E,
    hEel, hEsc, hArange⟩

theorem ggF4Enn_leviModel_L
    (hRig : GGLabelRigidInput) {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K) {n : ℕ}
    (hΛ : LargeEvenInLambda2 (⟨.F4, 0, n⟩ : LargeEvenLabel))
    (hL : GGHasLabel (⟨.F4, 0, n⟩ : LargeEvenLabel) (↥L ⧸ Subgroup.center ↥L))
    (hp5 : 5 ≤ p) (hpn : p ∣ 2 ^ n + 1) :
    GGF4LeviModel p Bs L := by
  obtain ⟨hN, Fq, _, _, _, hFqcard, e, E, hE, hEself, hA⟩ :=
    ggF4Enn_model_L hRig hH hΛ hL hp5 hpn
  exact ⟨hN, adjointGroup .F4 Fq, inferInstance, center_adjointGroup_eq_bot, e, E, hA,
    f4Enn_leviFrame (f4lp_two_le hp5 hpn) hFqcard hpn E hE hEself (Or.inl hp5)⟩

theorem ggF4Enn_leviModel_K
    (hRig : GGLabelRigidInput) {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K) {n : ℕ}
    (hΛ : LargeEvenInLambda2 (⟨.F4, 0, n⟩ : LargeEvenLabel))
    (hK : GGHasLabel (⟨.F4, 0, n⟩ : LargeEvenLabel) (↥K ⧸ Subgroup.center ↥K))
    (hp5 : 5 ≤ p) (hpn : p ∣ 2 ^ n + 1) :
    GGF4LeviModel p Bs K := by
  obtain ⟨hN, Fq, _, _, _, hFqcard, e, E, hE, hEself, hA⟩ :=
    ggF4Enn_model_K hRig hH hΛ hK hp5 hpn
  exact ⟨hN, adjointGroup .F4 Fq, inferInstance, center_adjointGroup_eq_bot, e, E, hA,
    f4Enn_leviFrame (f4lp_two_le hp5 hpn) hFqcard hpn E hE hEself (Or.inl hp5)⟩

theorem ggTBJF4LeviL_plus
    (hRig : GGLabelRigidInput) {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K) {n : ℕ}
    (hΛ : LargeEvenInLambda2 (⟨.F4, 0, n⟩ : LargeEvenLabel))
    (hL : GGHasLabel (⟨.F4, 0, n⟩ : LargeEvenLabel) (↥L ⧸ Subgroup.center ↥L))
    (hp5 : 5 ≤ p) (hpn : p ∣ 2 ^ n + 1) :
    GGResSideDatum p Bs L J ∨ GGResLeviSideDatumLE3 p Bs L J :=
  ggTBJF4LeviL_of_model hH (ggF4Enn_leviModel_L hRig hH hΛ hL hp5 hpn)

theorem ggTBJF4LeviK_plus
    (hRig : GGLabelRigidInput) {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K) (hJK : J ≤ K) {n : ℕ}
    (hΛ : LargeEvenInLambda2 (⟨.F4, 0, n⟩ : LargeEvenLabel))
    (hK : GGHasLabel (⟨.F4, 0, n⟩ : LargeEvenLabel) (↥K ⧸ Subgroup.center ↥K))
    (hp5 : 5 ≤ p) (hpn : p ∣ 2 ^ n + 1) :
    GGResSideDatum p Bs K J ∨ GGResLeviSideDatumLE3 p Bs K J :=
  ggTBJF4LeviK_of_model hH hJK (ggF4Enn_leviModel_K hRig hH hΛ hK hp5 hpn)

private theorem f4lp_threeMarking (hRig : GGLabelRigidInput) {G : Type} [Group G]
    {Bs X : Subgroup G} (hinn : GGInnerDiagOn Bs X) {n : ℕ}
    (hΛ : LargeEvenInLambda2 (⟨.F4, 0, n⟩ : LargeEvenLabel))
    (hX : GGHasLabel (⟨.F4, 0, n⟩ : LargeEvenLabel) (↥X ⧸ Subgroup.center ↥X))
    (hpn : 3 ∣ 2 ^ n + 1) : GGF4ThreeMarking Bs X :=
  largeEvenMarking_mono (fun lab _ _ _ _ _ ⟨hl, hN, hind⟩ =>
    ⟨by subst hl; exact ⟨rfl, rfl, hpn⟩, hN, hind⟩) (ggInnerDiagOn_relabel hRig hinn hΛ hX)

theorem ggF4Three_rank_of_res
    (hRig : GGLabelRigidInput) {G : Type} [Group G] [Finite G]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp 3 B Bs x L D J y K) {X : Subgroup G} (hinn : GGInnerDiagOn Bs X) {n : ℕ}
    (hΛ : LargeEvenInLambda2 (⟨.F4, 0, n⟩ : LargeEvenLabel))
    (hX : GGHasLabel (⟨.F4, 0, n⟩ : LargeEvenLabel) (↥X ⧸ Subgroup.center ↥X))
    (hpn : 3 ∣ 2 ^ n + 1) (hN : Bs ≤ Subgroup.normalizer (X : Set G)) :
    3 ^ 4 ≤ Nat.card (ggGamma X hN).range :=
  ggF4Three_rank_of_marking (ggF4ThreeSCTransvInput_of_cube ggF4ThreeSCCubeInput_holds) hH.1
    hH.2.2.2.1 (f4lp_threeMarking hRig hinn hΛ hX hpn) hN

theorem ggF4Three_model_L
    (hRig : GGLabelRigidInput) {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K) {n : ℕ}
    (hΛ : LargeEvenInLambda2 (⟨.F4, 0, n⟩ : LargeEvenLabel))
    (hL : GGHasLabel (⟨.F4, 0, n⟩ : LargeEvenLabel) (↥L ⧸ Subgroup.center ↥L))
    (hp3 : p = 3) (hpn : p ∣ 2 ^ n + 1) (hn2 : 2 ≤ n) :
    ∃ (hN : Bs ≤ Subgroup.normalizer (L : Set G)) (Fq : Type) (_ : Field Fq) (_ : Finite Fq)
      (_ : CharP Fq 2), Nat.card Fq = 2 ^ n ∧
      ∃ (e : ↥L ≃* adjointGroup .F4 Fq) (E : Subgroup (adjointGroup .F4 Fq)),
        IsElemAbelian p E ∧ 3 ^ 4 ≤ Nat.card E ∧
        (∀ g : adjointGroup .F4 Fq, (∀ c ∈ E, g * c = c * g) → g ^ p = 1 → g ∈ E) ∧
        (ggGamma L hN).range.map (MulAut.congr e).toMonoidHom =
          E.map (MulAut.conj : adjointGroup .F4 Fq →* MulAut (adjointGroup .F4 Fq)) := by
  classical
  subst hp3
  obtain ⟨Fq, _instFq, _instFin, _instChar, hFqcard, e, hZL, hN, hinner⟩ :=
    ggF4_model hRig hn2 hΛ hH.2.2.1.1 hL
  have hlb : 3 ^ 4 ≤ Nat.card (ggGamma L hN).range :=
    ggF4Three_rank_of_res hRig hH hH.2.2.1.1 hΛ hL hpn hN
  obtain ⟨E, hEel, hEcard, hEsc, hArange⟩ :=
    e8Enn_adjointModel hH.1.2.1.2.1 hH.1.2.1.2.2.2 e hZL hinner hN hlb
  exact ⟨hN, Fq, inferInstance, inferInstance, inferInstance, hFqcard, e, E, hEel, hEcard,
    hEsc, hArange⟩

theorem ggF4Three_model_K
    (hRig : GGLabelRigidInput) {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K) {n : ℕ}
    (hΛ : LargeEvenInLambda2 (⟨.F4, 0, n⟩ : LargeEvenLabel))
    (hK : GGHasLabel (⟨.F4, 0, n⟩ : LargeEvenLabel) (↥K ⧸ Subgroup.center ↥K))
    (hp3 : p = 3) (hpn : p ∣ 2 ^ n + 1) (hn2 : 2 ≤ n) :
    ∃ (hN : Bs ≤ Subgroup.normalizer (K : Set G)) (Fq : Type) (_ : Field Fq) (_ : Finite Fq)
      (_ : CharP Fq 2), Nat.card Fq = 2 ^ n ∧
      ∃ (e : ↥K ≃* adjointGroup .F4 Fq) (E : Subgroup (adjointGroup .F4 Fq)),
        IsElemAbelian p E ∧ 3 ^ 4 ≤ Nat.card E ∧
        (∀ g : adjointGroup .F4 Fq, (∀ c ∈ E, g * c = c * g) → g ^ p = 1 → g ∈ E) ∧
        (ggGamma K hN).range.map (MulAut.congr e).toMonoidHom =
          E.map (MulAut.conj : adjointGroup .F4 Fq →* MulAut (adjointGroup .F4 Fq)) := by
  classical
  subst hp3
  have hinn : GGInnerDiagOn Bs K := hH.2.2.1.2 y K hH.2.2.2.2.1
  obtain ⟨Fq, _instFq, _instFin, _instChar, hFqcard, e, hZK, hN, hinner⟩ :=
    ggF4_model hRig hn2 hΛ hinn hK
  have hlb : 3 ^ 4 ≤ Nat.card (ggGamma K hN).range :=
    ggF4Three_rank_of_res hRig hH hinn hΛ hK hpn hN
  obtain ⟨E, hEel, hEcard, hEsc, hArange⟩ :=
    e8Enn_adjointModel hH.1.2.1.2.1 hH.1.2.1.2.2.2 e hZK hinner hN hlb
  exact ⟨hN, Fq, inferInstance, inferInstance, inferInstance, hFqcard, e, E, hEel, hEcard,
    hEsc, hArange⟩

theorem ggF4Three_leviModel_L
    (hRig : GGLabelRigidInput) {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K) {n : ℕ}
    (hΛ : LargeEvenInLambda2 (⟨.F4, 0, n⟩ : LargeEvenLabel))
    (hL : GGHasLabel (⟨.F4, 0, n⟩ : LargeEvenLabel) (↥L ⧸ Subgroup.center ↥L))
    (hp3 : p = 3) (hpn : p ∣ 2 ^ n + 1) (hn2 : 2 ≤ n) :
    GGF4LeviModel p Bs L := by
  obtain ⟨hN, Fq, _, _, _, hFqcard, e, E, hE, hE4, hEself, hA⟩ :=
    ggF4Three_model_L hRig hH hΛ hL hp3 hpn hn2
  exact ⟨hN, adjointGroup .F4 Fq, inferInstance, center_adjointGroup_eq_bot, e, E, hA,
    f4Enn_leviFrame hn2 hFqcard hpn E hE hEself (Or.inr ⟨hp3, hE4⟩)⟩

theorem ggF4Three_leviModel_K
    (hRig : GGLabelRigidInput) {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K) {n : ℕ}
    (hΛ : LargeEvenInLambda2 (⟨.F4, 0, n⟩ : LargeEvenLabel))
    (hK : GGHasLabel (⟨.F4, 0, n⟩ : LargeEvenLabel) (↥K ⧸ Subgroup.center ↥K))
    (hp3 : p = 3) (hpn : p ∣ 2 ^ n + 1) (hn2 : 2 ≤ n) :
    GGF4LeviModel p Bs K := by
  obtain ⟨hN, Fq, _, _, _, hFqcard, e, E, hE, hE4, hEself, hA⟩ :=
    ggF4Three_model_K hRig hH hΛ hK hp3 hpn hn2
  exact ⟨hN, adjointGroup .F4 Fq, inferInstance, center_adjointGroup_eq_bot, e, E, hA,
    f4Enn_leviFrame hn2 hFqcard hpn E hE hEself (Or.inr ⟨hp3, hE4⟩)⟩

theorem ggTBJF4LeviL_three
    (hRig : GGLabelRigidInput) {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K) {n : ℕ}
    (hΛ : LargeEvenInLambda2 (⟨.F4, 0, n⟩ : LargeEvenLabel))
    (hL : GGHasLabel (⟨.F4, 0, n⟩ : LargeEvenLabel) (↥L ⧸ Subgroup.center ↥L))
    (hp3 : p = 3) (hpn : p ∣ 2 ^ n + 1) (hn2 : 2 ≤ n) :
    GGResSideDatum p Bs L J ∨ GGResLeviSideDatumLE3 p Bs L J :=
  ggTBJF4LeviL_of_model hH (ggF4Three_leviModel_L hRig hH hΛ hL hp3 hpn hn2)

theorem ggTBJF4LeviK_three
    (hRig : GGLabelRigidInput) {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K) (hJK : J ≤ K) {n : ℕ}
    (hΛ : LargeEvenInLambda2 (⟨.F4, 0, n⟩ : LargeEvenLabel))
    (hK : GGHasLabel (⟨.F4, 0, n⟩ : LargeEvenLabel) (↥K ⧸ Subgroup.center ↥K))
    (hp3 : p = 3) (hpn : p ∣ 2 ^ n + 1) (hn2 : 2 ≤ n) :
    GGResSideDatum p Bs K J ∨ GGResLeviSideDatumLE3 p Bs K J :=
  ggTBJF4LeviK_of_model hH hJK (ggF4Three_leviModel_K hRig hH hΛ hK hp3 hpn hn2)

@[expose] def GGTBJF4LeviLThreePlus : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (y : G) (K : Subgroup G), GGResHyp p B Bs x L D J y K → ∀ [Fact p.Prime],
    GGInnerDiagOnLabel (fun _ lab => lab.tag = .F4) p Bs L → GGResXDatum p Bs L →
    ∀ n : ℕ, LargeEvenInLambda2 (⟨.F4, 0, n⟩ : LargeEvenLabel) →
      GGHasLabel (⟨.F4, 0, n⟩ : LargeEvenLabel) (↥L ⧸ Subgroup.center ↥L) →
      p = 3 → p ∣ 2 ^ n + 1 →
      ∀ labJ : LargeEvenLabel, LargeEvenInLambda2 labJ →
        GGHasLabel labJ (↥J ⧸ Subgroup.center ↥J) → n ∣ labJ.n →
          GGResSideDatum p Bs L J ∨ GGResLeviSideDatumLE3 p Bs L J

@[expose] def GGTBJF4LeviKThreePlus : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (y : G) (K : Subgroup G), GGResHyp p B Bs x L D J y K → J ≤ K → ∀ [Fact p.Prime],
    GGInnerDiagOnLabel (fun _ lab => lab.tag = .F4) p Bs K → GGResXDatum p Bs K →
    ∀ n : ℕ, LargeEvenInLambda2 (⟨.F4, 0, n⟩ : LargeEvenLabel) →
      GGHasLabel (⟨.F4, 0, n⟩ : LargeEvenLabel) (↥K ⧸ Subgroup.center ↥K) →
      p = 3 → p ∣ 2 ^ n + 1 →
      ∀ labJ : LargeEvenLabel, LargeEvenInLambda2 labJ →
        GGHasLabel labJ (↥J ⧸ Subgroup.center ↥J) → n ∣ labJ.n →
          GGResSideDatum p Bs K J ∨ GGResLeviSideDatumLE3 p Bs K J

@[expose] def GGTBJF4LeviLThreeTwo : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (y : G) (K : Subgroup G), GGResHyp p B Bs x L D J y K → ∀ [Fact p.Prime],
    GGInnerDiagOnLabel (fun _ lab => lab.tag = .F4) p Bs L → GGResXDatum p Bs L →
    GGHasLabel (⟨.F4, 0, 1⟩ : LargeEvenLabel) (↥L ⧸ Subgroup.center ↥L) → p = 3 →
      ∀ labJ : LargeEvenLabel, LargeEvenInLambda2 labJ →
        GGHasLabel labJ (↥J ⧸ Subgroup.center ↥J) →
          GGResSideDatum p Bs L J ∨ GGResLeviSideDatumLE3 p Bs L J

@[expose] def GGTBJF4LeviKThreeTwo : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (y : G) (K : Subgroup G), GGResHyp p B Bs x L D J y K → J ≤ K → ∀ [Fact p.Prime],
    GGInnerDiagOnLabel (fun _ lab => lab.tag = .F4) p Bs K → GGResXDatum p Bs K →
    GGHasLabel (⟨.F4, 0, 1⟩ : LargeEvenLabel) (↥K ⧸ Subgroup.center ↥K) → p = 3 →
      ∀ labJ : LargeEvenLabel, LargeEvenInLambda2 labJ →
        GGHasLabel labJ (↥J ⧸ Subgroup.center ↥J) →
          GGResSideDatum p Bs K J ∨ GGResLeviSideDatumLE3 p Bs K J

theorem ggTBJF4LeviLThreePlus_of_two
    (hRig : GGLabelRigidInput) (h2 : GGTBJF4LeviLThreeTwo) : GGTBJF4LeviLThreePlus := by
  intro G _ _ p B Bs x L D J y K hH _ hL hX n hΛ hhas hp3 hpn labJ hΛJ hhasJ _
  by_cases hn : n = 1
  · subst hn
    exact h2 G p B Bs x L D J y K hH hL hX hhas hp3 labJ hΛJ hhasJ
  · exact ggTBJF4LeviL_three hRig hH hΛ hhas hp3 hpn (by have h1 : 1 ≤ n := hΛ.1; omega)

theorem ggTBJF4LeviKThreePlus_of_two
    (hRig : GGLabelRigidInput) (h2 : GGTBJF4LeviKThreeTwo) : GGTBJF4LeviKThreePlus := by
  intro G _ _ p B Bs x L D J y K hH hJK _ hK hX n hΛ hhas hp3 hpn labJ hΛJ hhasJ _
  by_cases hn : n = 1
  · subst hn
    exact h2 G p B Bs x L D J y K hH hJK hK hX hhas hp3 labJ hΛJ hhasJ
  · exact ggTBJF4LeviK_three hRig hH hJK hΛ hhas hp3 hpn (by have h1 : 1 ≤ n := hΛ.1; omega)

private theorem f4lp_five_le {p n : ℕ} (hp : p.Prime) (hn : 1 ≤ n) (hpn : p ∣ 2 ^ n + 1)
    (h3 : p ≠ 3) : 5 ≤ p := by
  have h2 : p ≠ 2 := by
    rintro rfl
    have hev : 2 ∣ 2 ^ n := dvd_pow_self 2 (by omega)
    omega
  have h4 : p ≠ 4 := by
    rintro rfl
    norm_num at hp
  have := hp.two_le
  omega

theorem ggTBJF4LeviL_of_threePlus
    (hRig : GGLabelRigidInput) (h3 : GGTBJF4LeviLThreePlus) : GGTBJF4LeviL := by
  intro G _ _ p B Bs x L D J y K hH hp hL hX n hΛ hhas hreg labJ hΛJ hhasJ hdvd _
  rcases hreg with hm | hpl
  · exact ggTBJF4LeviL_minus hRig hH hΛ hhas hm
  · by_cases hp3 : p = 3
    · exact h3 G p B Bs x L D J y K hH hL hX n hΛ hhas hp3 hpl labJ hΛJ hhasJ hdvd
    · exact ggTBJF4LeviL_plus hRig hH hΛ hhas
        (f4lp_five_le hp.out hΛ.1 hpl hp3) hpl

theorem ggTBJF4LeviK_of_threePlus
    (hRig : GGLabelRigidInput) (h3 : GGTBJF4LeviKThreePlus) : GGTBJF4LeviK := by
  intro G _ _ p B Bs x L D J y K hH hJK hp hK hX n hΛ hhas hreg labJ hΛJ hhasJ hdvd _
  rcases hreg with hm | hpl
  · exact ggTBJF4LeviK_minus hRig hH hJK hΛ hhas hm
  · by_cases hp3 : p = 3
    · exact h3 G p B Bs x L D J y K hH hJK hK hX n hΛ hhas hp3 hpl labJ hΛJ hhasJ hdvd
    · exact ggTBJF4LeviK_plus hRig hH hJK hΛ hhas
        (f4lp_five_le hp.out hΛ.1 hpl hp3) hpl

theorem ggTBJLeftOn_F4_neTwoThree
    (hTCJ : GGTCJKnown) (hRig : GGLabelRigidInput) : GGTBJLeftOn ggTBJF4LabelNeTwoThree := by
  refine GGTBJLeftOnLab.toLeftOn hTCJ ?_
  intro G _ _ p B Bs x L D J y K hH hp _ _ lab labJ hΛ _ hS hhas _ _
  obtain ⟨t, r, n⟩ := lab
  obtain ⟨⟨ht, hphi⟩, hne⟩ := hS
  have ht' : t = .F4 := ht
  subst ht'
  have hr : r = 0 := hΛ.2
  subst hr
  rcases ggLabPhiOneTwo_dvd hp.out hphi with hm | hpl
  · exact (ggTBJF4LeviL_minus hRig hH hΛ hhas hm).imp id Or.inl
  · by_cases hp3 : p = 3
    · have hn1 : n ≠ 1 := fun h => hne ⟨hp3, h⟩
      have hn2 : 2 ≤ n := by have h1 : 1 ≤ n := hΛ.1; omega
      exact (ggTBJF4LeviL_three hRig hH hΛ hhas hp3 hpl hn2).imp id Or.inl
    · exact (ggTBJF4LeviL_plus hRig hH hΛ hhas
        (f4lp_five_le hp.out hΛ.1 hpl hp3) hpl).imp id Or.inl

theorem ggTBJNbrOn_F4_neTwoThree
    (hTCJ : GGTCJKnown) (hI3 : GGNbrSubcomponentInput) (hRig : GGLabelRigidInput) :
    GGTBJNbrOn ggTBJF4LabelNeTwoThree := by
  refine GGTBJNbrOnLab.toNbrOn hTCJ hI3 ?_
  intro G _ _ p B Bs x L D J y K hH hp _ _ lab labJ hΛ _ hS hhas _ _
  obtain ⟨t, r, n⟩ := lab
  obtain ⟨⟨ht, hphi⟩, hne⟩ := hS
  have ht' : t = .F4 := ht
  subst ht'
  have hr : r = 0 := hΛ.2
  subst hr
  have hJK : J ≤ K := hI3 G p B x L D J hH.1.1 hH.1.2.2 y K hH.2.2.2.2.1
  rcases ggLabPhiOneTwo_dvd hp.out hphi with hm | hpl
  · exact (ggTBJF4LeviK_minus hRig hH hJK hΛ hhas hm).imp id Or.inl
  · by_cases hp3 : p = 3
    · have hn1 : n ≠ 1 := fun h => hne ⟨hp3, h⟩
      have hn2 : 2 ≤ n := by have h1 : 1 ≤ n := hΛ.1; omega
      exact (ggTBJF4LeviK_three hRig hH hJK hΛ hhas hp3 hpl hn2).imp id Or.inl
    · exact (ggTBJF4LeviK_plus hRig hH hJK hΛ hhas
        (f4lp_five_le hp.out hΛ.1 hpl hp3) hpl).imp id Or.inl

theorem GGTBJOrdinaryOutside.of_F4_neTwoThree
    {E : ℕ → LargeEvenLabel → Prop} (hTCJ : GGTCJKnown) (hI3 : GGNbrSubcomponentInput)
    (hRig : GGLabelRigidInput)
    (h : GGTBJOrdinaryOutside fun p lab => E p lab ∨ ggTBJF4LabelNeTwoThree p lab) :
    GGTBJOrdinaryOutside E :=
  GGTBJOrdinaryOutside.of_proved (ggTBJLeftOn_F4_neTwoThree hTCJ hRig)
    (ggTBJNbrOn_F4_neTwoThree hTCJ hI3 hRig) h

end CFSG.StandardType

end
