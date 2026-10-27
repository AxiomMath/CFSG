module

public import CFSG.LocalAnalysis.StandardType.GGTorusGenExcTwoSetup
public import Certificates.Certificate1952
public import Certificates.Certificate13659
public import Certificates.Certificate13660
import CFSG.LocalAnalysis.StandardType.GGLangExhaust
import CFSG.LocalAnalysis.StandardType.GGLangOrbitTorus
import CFSG.LocalAnalysis.StandardType.GGTwE6RootKernelCount
import CFSG.LocalAnalysis.ComponentInitial.BlockCentralQuotient
import CFSG.HardMathSupport.Timmesfeld.LangTorus.RigidDescent
import CFSG.HardMathSupport.Timmesfeld.LangTorus.ExcRoots

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly TableB CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.AlgebraicGroups

namespace ExcTwoGen

theorem map_centralizer_singleton {G H : Type*} [Group G] [Group H]
    (β : G →* H) (hβ : Function.Injective β) (x : G) :
    (Subgroup.centralizer ({x} : Set G)).map β =
      β.range ⊓ Subgroup.centralizer ({β x} : Set H) := by
  ext z
  constructor
  · rintro ⟨y, hy, rfl⟩
    refine Subgroup.mem_inf.2 ⟨⟨y, rfl⟩, ?_⟩
    have hy' : y ∈ Subgroup.centralizer ({x} : Set G) := hy
    rw [Subgroup.mem_centralizer_singleton_iff] at hy'
    rw [Subgroup.mem_centralizer_singleton_iff]
    rw [← map_mul, ← map_mul, hy']
  · rintro ⟨⟨y, rfl⟩, hz⟩
    refine ⟨y, ?_, rfl⟩
    have hz' : β y ∈ Subgroup.centralizer ({β x} : Set H) := hz
    rw [Subgroup.mem_centralizer_singleton_iff] at hz'
    change y ∈ Subgroup.centralizer ({x} : Set G)
    rw [Subgroup.mem_centralizer_singleton_iff]
    apply hβ
    rw [map_mul, map_mul]
    exact hz'

private theorem rootChar_latCorootZ_symmetrizedCartan
    {τ : Tag} {L : Type} [Field L] {α : Fin τ.rank → ℤ}
    (hα : IsRoot τ α) (ζ : Lˣ) :
    CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley.rootChar
      (fun j => ζ ^ latCorootZ τ.symmetrizedCartan α j) α = ζ ^ 2 := by
  have hcor : ∀ j, latCorootZ τ.symmetrizedCartan α j = corootPair α (Pi.single j 1) := by
    intro j
    rw [show τ.symmetrizedCartan = (1 : ℤ) • τ.symmetrizedCartan from (one_smul _ _).symm]
    exact congrFun (CFSG.StandardType.StepTwoToralIndex.latCorootZ_smul_symmetrizedCartan τ
      (by norm_num) α) j
  rw [CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley.rootChar]
  simp only [hcor]
  rw [show (∏ i, (ζ ^ corootPair α (Pi.single i 1)) ^ α i) =
      ζ ^ (∑ i, α i * corootPair α (Pi.single i 1)) from by
    rw [← Finset.prod_zpow_eq_zpow_sum]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [← zpow_mul, mul_comm]]
  rw [CFSG.StandardType.StepTwoToralIndex.sum_mul_corootPair_single hα]
  rfl

theorem commute_of_map_eq_rootDiagUnit {τ : Tag} {K : Type} [Field K] {L : Type}
    [Field L] {ι : adjointGroup τ K →* ModGL τ L} (hιinj : Function.Injective ι)
    {E : Subgroup (adjointGroup τ K)}
    (hE : ∀ z ∈ E, ∃ c : Fin τ.rank → Lˣ, ι z = rootDiagUnit τ c)
    {b : Fin τ.rank → Lˣ} {w' : adjointGroup τ K} (hιw' : ι w' = rootDiagUnit τ b) :
    ∀ z ∈ E, w' * z = z * w' := by
  intro z hz
  obtain ⟨c, hc⟩ := hE z hz
  apply hιinj
  rw [map_mul, map_mul, hιw', hc, ← rootDiagUnit_mul, ← rootDiagUnit_mul]
  congr 1
  exact mul_comm _ _

private theorem pow_three_of_map_eq_rootDiagUnit {τ : Tag} {K : Type} [Field K] {L : Type}
    [Field L] {ι : adjointGroup τ K →* ModGL τ L} (hιinj : Function.Injective ι)
    {w' : adjointGroup τ K} {α : Fin τ.rank → ℤ} {ζ : Lˣ} (hζ : ζ ^ 3 = 1)
    (hιw' : ι w' = rootDiagUnit τ (fun j => ζ ^ latCorootZ τ.symmetrizedCartan α j)) :
    w' ^ 3 = 1 := by
  have hb3 : (fun j => ζ ^ latCorootZ τ.symmetrizedCartan α j) ^ 3 = 1 := by
    funext j
    simp only [Pi.pow_apply]
    exact CFSG.StandardType.TwE6RootKill.zpow_pow_eq_one_rk (p := 3) hζ _
  apply hιinj
  rw [map_pow, map_one, hιw', rootDiagUnit_pow, hb3, rootDiagUnit_one]

private theorem ne_one_of_map_eq_rootDiagUnit_latCorootZ
    {τ : Tag} {K : Type} [Field K] {L : Type} [Field L]
    {ι : adjointGroup τ K →* ModGL τ L} (hιinj : Function.Injective ι)
    {w' : adjointGroup τ K} {α : Fin τ.rank → ℤ} (hα : IsRoot τ α) {ζ : Lˣ}
    (hζo : orderOf ζ = 3)
    (hιw' : ι w' = rootDiagUnit τ (fun j => ζ ^ latCorootZ τ.symmetrizedCartan α j)) :
    w' ≠ 1 := by
  intro hw1
  have hb1 : (fun j => ζ ^ latCorootZ τ.symmetrizedCartan α j) = 1 := by
    apply CFSG.LieType.Chevalley.rootDiagUnit_injective
    rw [rootDiagUnit_one, ← hιw', hw1, map_one]
  have hchar2 : rootChar (fun j => ζ ^ latCorootZ τ.symmetrizedCartan α j) α = ζ ^ 2 :=
    rootChar_latCorootZ_symmetrizedCartan hα ζ
  have hchar1 : rootChar (fun j => ζ ^ latCorootZ τ.symmetrizedCartan α j) α = 1 := by
    rw [hb1]
    simp [rootChar]
  have h2 : ζ ^ 2 = 1 := by rw [← hchar2, hchar1]
  have h2' : ζ ^ (2 : ℕ) = 1 := by
    rw [← zpow_natCast]
    exact h2
  have hdvd : orderOf ζ ∣ 2 := orderOf_dvd_iff_pow_eq_one.2 h2'
  rw [hζo] at hdvd
  norm_num at hdvd

theorem exists_rationalComponent_and_root
    {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ}
    (S : LangSetup τ L p₀) (hτ : τ ≠ .G2) (hpL : ((3 : ℕ) : L) ≠ 0)
    {a : Fin τ.rank → Lˣ} (hT : rootDiagUnit τ a ∈ S.D.torus) (hap : ∀ i, a i ^ 3 = 1)
    (h1 : rootDiagUnit τ a ≠ 1) {K : Subgroup (ModGL τ L)}
    (hK : CFSG.Open.IsComponentOf K (S.Γ ⊓ Subgroup.centralizer {rootDiagUnit τ a})) :
    ∃ (i : KernelComponent (rootCharHom a)) (α : Fin τ.rank → ℤ),
      K = rationalComponent S.ρ S.Γ (rootCharHom a) i ∧
        α ∈ componentRoots (rootCharHom a) i := by
  obtain ⟨i, -, hEq⟩ :=
    CFSG.StandardType.LangRat.exists_rationalComponent_eq_of_isComponentOf_of_ne_G2 S hτ
      Nat.prime_three hpL hT hap h1 hK
  obtain ⟨b, hb⟩ := Quotient.exists_rep i
  exact ⟨i, b.1, hEq, b.2, hb⟩

private theorem exists_frameDiagData
    {τ : Tag} (hτ : τ = .E7 ∨ τ = .E8) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 2) {E : Subgroup (adjointGroup τ K)}
    (hF : Irred937.LangFrameData τ 3 K E) {x : adjointGroup τ K} (hx : x ∈ E) (hx1 : x ≠ 1) :
    ∃ (S : LangSetup τ (AlgebraicClosure K) 5)
      (ι : adjointGroup τ K →* ModGL τ (AlgebraicClosure K))
      (a : Fin τ.rank → (AlgebraicClosure K)ˣ)
      (Fr : AlgebraicClosure K →+* AlgebraicClosure K) (w : WeylGroup τ)
      (ζ : (AlgebraicClosure K)ˣ) (hζ : ζ ^ 3 = 1) (hζo : orderOf ζ = 3),
      Function.Injective ι ∧ ι.range = S.Γ ∧ ι x = rootDiagUnit τ a ∧
        (∀ z ∈ E, ∃ c : Fin τ.rank → (AlgebraicClosure K)ˣ, ι z = rootDiagUnit τ c) ∧
        (∀ k, a k ^ 3 = 1) ∧ rootDiagUnit τ a ≠ 1 ∧ rootDiagUnit τ a ∈ S.D.torus ∧
        S.D.q = 2 ^ 1 ∧ S.IsAlgebraic ∧ S.D.Φ = Units.map (entrywiseHom Fr) ∧
        S.D.n = canonicalRep (coxeterSystem τ) (AlgebraicClosure K) w ∧
        (∀ c, Fr c = c ^ S.D.q) ∧ (∀ v : Fin τ.rank → ℤ, w • v = -v) ∧
        Units.map Fr.toMonoidHom ζ = ζ⁻¹ ∧ ((3 : ℕ) : AlgebraicClosure K) ≠ 0 ∧
        (τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) := by
  classical
  obtain ⟨w, Fr, g0, ζ, hζ, ι₀, hFr, hg0C, hg0, hwc, hζo, hinj, hrange, hbase⟩ := hF
  obtain ⟨S, ι, hSΦ, hSq, hSn, hιinj, hιrange, hιframe, hιtorus⟩ :=
    exists_langSetup_of_langFrame_two hτ hK hFr hg0C hg0 hζo hbase hinj
  obtain ⟨s, hs⟩ : ∃ s, ι₀ s = x := by rw [← hrange] at hx; exact hx
  set t : Fin τ.rank → ZMod 3 := Multiplicative.toAdd s with htdef
  set a : Fin τ.rank → (AlgebraicClosure K)ˣ :=
    TableBExc.E6Three.zetaVec ζ hζ (ExcFrames.frameCoord τ 3 t) with hadef
  have hx' : x = ι₀ (Multiplicative.ofAdd t) := by rw [← hs]; rfl
  have hιx : ι x = rootDiagUnit τ a := by rw [hx', hιframe, hadef]; rfl
  have hap : ∀ k, a k ^ 3 = 1 := by
    intro k
    rw [hadef, TableBExc.E6Three.zetaVec_apply]
    exact CFSG.StandardType.TwE6RootKill.zpow_pow_eq_one_rk (p := 3) hζ
      ((ExcFrames.frameCoord τ 3 t k).val : ℤ)
  have h1 : rootDiagUnit τ a ≠ 1 := fun ha1 =>
    hx1 (hιinj (by rw [hιx, ha1, map_one]))
  have hT : rootDiagUnit τ a ∈ S.D.torus := hιtorus t
  have hq2 : S.D.q = 2 ^ 1 := by rw [hSq, hK]; norm_num
  have hAlg : S.IsAlgebraic := S.isAlgebraic_of_algebraic K 1 (by rw [hSq, pow_one])
  have hpL : ((3 : ℕ) : AlgebraicClosure K) ≠ 0 := by
    have h2 : ((2 : ℕ) : AlgebraicClosure K) = 0 := by
      rw [show (2 : ℕ) = S.D.q from by rw [hq2]; norm_num]; exact S.hqpow.2
    rw [show ((3 : ℕ) : AlgebraicClosure K) = ((2 : ℕ) : AlgebraicClosure K) + 1 by norm_num,
      h2, zero_add]
    exact one_ne_zero
  have hw : ∀ v : Fin τ.rank → ℤ, w • v = -v :=
    smul_eq_neg_of_langFrame_two hτ hK hFr hg0 hζo hζ hbase
  have hτ4 : τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8 := by
    rcases hτ with rfl | rfl <;> simp
  have hFrq : ∀ c, Fr c = c ^ S.D.q := fun c => by rw [hSq]; exact hFr c
  have ht : Units.map Fr.toMonoidHom ζ = ζ⁻¹ := by
    have h2 : ζ ^ 2 = ζ⁻¹ := by rw [eq_inv_iff_mul_eq_one, ← pow_succ, hζ]
    rw [← h2]
    apply Units.ext
    change Fr (ζ : AlgebraicClosure K) = ((ζ : AlgebraicClosure K)) ^ 2
    rw [hFr, hK]
  have hE : ∀ z ∈ E, ∃ c : Fin τ.rank → (AlgebraicClosure K)ˣ, ι z = rootDiagUnit τ c := by
    intro z hz
    rw [← hrange] at hz
    obtain ⟨s', hs'⟩ := hz
    refine ⟨TableBExc.E6Three.zetaVec ζ hζ
      (ExcFrames.frameCoord τ 3 (Multiplicative.toAdd s')), ?_⟩
    rw [show z = ι₀ (Multiplicative.ofAdd (Multiplicative.toAdd s')) from by rw [← hs']; rfl,
      hιframe]
    rfl
  exact ⟨S, ι, a, Fr, w, ζ, hζ, hζo, hιinj, hιrange, hιx, hE, hap, h1, hT, hq2, hAlg, hSΦ,
    hSn, hFrq, hw, ht, hpL, hτ4⟩

theorem exists_mem_ne_one_of_isComponentOf_of_langFrame_two
    {τ : Tag} (hτ : τ = .E7 ∨ τ = .E8)
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2) {E : Subgroup (adjointGroup τ K)}
    (hSC : ∀ g : adjointGroup τ K, (∀ e ∈ E, g * e = e * g) → g ^ 3 = 1 → g ∈ E)
    (hF : Irred937.LangFrameData τ 3 K E) {x : adjointGroup τ K} (hx : x ∈ E) (hx1 : x ≠ 1)
    {J : Subgroup (adjointGroup τ K)} (hJ : IsComponentOf J (Subgroup.centralizer {x})) :
    ∃ w ∈ J, w ∈ E ∧ w ≠ 1 := by
  classical
  obtain ⟨S, ι, a, Fr, w, ζ, hζ, hζo, hιinj, hιrange, hιx, hE, hap, h1, hT, hq2, hAlg,
    hΦ, hn, hFrq, hw, ht, hpL, hτ4⟩ := exists_frameDiagData hτ hK hF hx hx1
  have hJ' : CFSG.Open.IsComponentOf (J.map ι)
      (S.Γ ⊓ Subgroup.centralizer {rootDiagUnit τ a}) := by
    have h := CFSG.LocalAnalysis.ComponentInitial.isComponentOf_map_of_injective hJ ι hιinj
    rw [map_centralizer_singleton ι hιinj x, hιrange, hιx] at h
    exact CFSG.Assembly.isComponentOf_iff_open.1 h
  have hτ' : τ ≠ .G2 := by rcases hτ with rfl | rfl <;> decide
  obtain ⟨i, α, hJeq, hα⟩ := exists_rationalComponent_and_root S hτ' hpL hT hap h1 hJ'
  have hαroot : IsRoot τ α :=
    (CFSG.LieType.Chevalley.isRootComponent_componentRoots (χ := rootCharHom a) i).isRoot α hα
  have hρα : S.ρ α = α ∨ S.ρ α = -α := by
    right
    rw [S.rho_eq_smul_of_frob hFrq hΦ hn hαroot, hw α]
  set b : Fin τ.rank → (AlgebraicClosure K)ˣ :=
    fun j => ζ ^ latCorootZ τ.symmetrizedCartan α j with hb
  have hy : rootDiagUnit τ b ∈ rationalComponent S.ρ S.Γ (rootCharHom a) i := by
    rw [hb]
    exact rootDiagUnit_latCorootZ_mem_rationalComponent S hτ4 hq2 hAlg hΦ hn hw i hα hρα
      1 one_ne_zero τ.symmetrizedCartan (by simp) ht (m := 3) (by decide) hζ
  have hyJ : rootDiagUnit τ b ∈ J.map ι := by rw [hJeq]; exact hy
  obtain ⟨w', hw'J, hιw'⟩ := Subgroup.mem_map.1 hyJ
  have hιw'' : ι w' = rootDiagUnit τ (fun j => ζ ^ latCorootZ τ.symmetrizedCartan α j) := by
    rw [hιw', hb]
  have hcomm : ∀ z ∈ E, w' * z = z * w' :=
    commute_of_map_eq_rootDiagUnit hιinj hE hιw''
  have hw'3 : w' ^ 3 = 1 := pow_three_of_map_eq_rootDiagUnit hιinj hζ hιw''
  exact ⟨w', hw'J, hSC w' hcomm hw'3,
    ne_one_of_map_eq_rootDiagUnit_latCorootZ hιinj hαroot hζo hιw''⟩

end ExcTwoGen

end CFSG.StandardType
