module

public import CFSG.LocalAnalysis.StandardType.GGTorusGenE6TwoSetup
public import CFSG.LocalAnalysis.StandardType.GGTorusGenE6TwoDiag
public import CFSG.LocalAnalysis.StandardType.GGTorusGenE6TwoCoroot
public import CFSG.LocalAnalysis.StandardType.GGTorusGenExcTwoComp
import CFSG.LocalAnalysis.ComponentInitial.BlockCentralQuotient

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly TableB CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus
open TableBExc.E6Three CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

namespace E6TwoGen


private theorem exists_e6Two_diagData {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 2) (h2 : (2 : K) = 0) {E : Subgroup (adjointGroup .E6 K)}
    {g : adjointGroup .E6 K}
    (hEg : E.map (MulAut.conj g).toMonoidHom = (torusE6Two h2).range) :
    ∃ (S : LangSetup .E6 (AlgebraicClosure K) 5)
      (ι' : adjointGroup .E6 K →* ModGL .E6 (AlgebraicClosure K))
      (Fr : AlgebraicClosure K →+* AlgebraicClosure K) (ω : (AlgebraicClosure K)ˣ),
      Function.Injective ι' ∧ ι'.range = S.Γ ∧ S.D.Φ = Units.map (entrywiseHom Fr) ∧
        S.D.q = 2 ∧ S.D.n = canonicalRep (coxeterSystem .E6) (AlgebraicClosure K) wE6Two ∧
        (∀ c, Fr c = c ^ S.D.q) ∧ S.IsAlgebraic ∧ orderOf ω = 3 ∧
        Units.map Fr.toMonoidHom ω = ω⁻¹ ∧
        (∀ z ∈ E, ∃ c : Fin Tag.E6.rank → (AlgebraicClosure K)ˣ,
          ι' z = rootDiagUnit .E6 c ∧ ∀ k, c k ^ 3 = 1) ∧
        (∀ (z : adjointGroup .E6 K) (a : Fin Tag.E6.rank → (AlgebraicClosure K)ˣ),
          ι' z = rootDiagUnit .E6 a → rootDiagUnit .E6 a ∈ S.D.torus) := by
  obtain ⟨S, ι, Fr, ω, hΦ, hq, hn, hFrq, hAlg, hιinj, hιrange, hωo, hωF, hιu, hT⟩ :=
    exists_langSetup_e6Two hK
  have hω : ω ^ 3 = 1 := by
    rw [← hωo]
    exact pow_orderOf_eq_one ω
  let ι' : adjointGroup .E6 K →* ModGL .E6 (AlgebraicClosure K) :=
    ι.comp (MulAut.conj g).toMonoidHom
  have hι'inj : Function.Injective ι' := by
    intro p q hpq
    exact (MulAut.conj g).injective (hιinj hpq)
  have hconj : (MulAut.conj g).toMonoidHom.range = ⊤ :=
    MonoidHom.range_eq_top_of_surjective _ (MulAut.conj g).surjective
  have hι'range : ι'.range = S.Γ := by
    rw [show ι' = ι.comp (MulAut.conj g).toMonoidHom from rfl, MonoidHom.range_comp, hconj,
      Subgroup.map_top, hιrange]
  have hEfull : ∀ z ∈ E, ∃ c : Fin Tag.E6.rank → (AlgebraicClosure K)ˣ,
      ι' z = rootDiagUnit .E6 c ∧ ∀ k, c k ^ 3 = 1 := by
    intro z hz
    have hz' : (MulAut.conj g) z ∈ (torusE6Two h2).range := by
      rw [← hEg]
      exact Subgroup.mem_map.mpr ⟨z, hz, rfl⟩
    obtain ⟨c, hc, hc3⟩ :=
      exists_map_eq_rootDiagUnit_of_mem_range_torusE6Two h2 ι hω hιu hz'
    exact ⟨c, hc, hc3⟩
  have hT' : ∀ (z : adjointGroup .E6 K) (a : Fin Tag.E6.rank → (AlgebraicClosure K)ˣ),
      ι' z = rootDiagUnit .E6 a → rootDiagUnit .E6 a ∈ S.D.torus :=
    fun z a h => hT ((MulAut.conj g) z) a h
  exact ⟨S, ι', Fr, ω, hι'inj, hι'range, hΦ, hq, hn, hFrq, hAlg, hωo, hωF, hEfull, hT'⟩

theorem exists_mem_ne_one_of_isComponentOf_e6Two {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 2) (h2 : (2 : K) = 0) {E : Subgroup (adjointGroup .E6 K)}
    {g : adjointGroup .E6 K} (hEg : E.map (MulAut.conj g).toMonoidHom = (torusE6Two h2).range)
    (hSC : ∀ y : adjointGroup .E6 K, (∀ e ∈ E, y * e = e * y) → y ^ 3 = 1 → y ∈ E)
    {x : adjointGroup .E6 K} (hx : x ∈ E) (hx1 : x ≠ 1) {J : Subgroup (adjointGroup .E6 K)}
    (hJ : IsComponentOf J (Subgroup.centralizer {x})) :
    ∃ y ∈ J, y ∈ E ∧ y ≠ 1 := by
  classical
  haveI : Fintype K := Fintype.ofFinite K
  haveI : CharP K 2 := charP_of_card_eq_prime_pow (p := 2) (f := 1) (by
    rw [← Nat.card_eq_fintype_card, hK]
    norm_num)
  haveI : CharP (AlgebraicClosure K) 2 :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective 2
  obtain ⟨S, ι', Fr, ω, hι'inj, hι'range, hΦ, hq, hn, hFrq, hAlg, hωo, hωF, hEfull, hT'⟩ :=
    exists_e6Two_diagData hK h2 hEg
  obtain ⟨a, hι'x, hap⟩ := hEfull x hx
  have h1 : rootDiagUnit .E6 a ≠ 1 := by
    intro h
    apply hx1
    apply hι'inj
    rw [hι'x, h, map_one]
  have hTa : rootDiagUnit .E6 a ∈ S.D.torus := hT' x a hι'x
  have hJ' : CFSG.Open.IsComponentOf (J.map ι')
      (S.Γ ⊓ Subgroup.centralizer {rootDiagUnit .E6 a}) := by
    have h := CFSG.LocalAnalysis.ComponentInitial.isComponentOf_map_of_injective hJ ι' hι'inj
    rw [ExcTwoGen.map_centralizer_singleton ι' hι'inj x, hι'range, hι'x] at h
    exact CFSG.Assembly.isComponentOf_iff_open.1 h
  have hpL : ((3 : ℕ) : AlgebraicClosure K) ≠ 0 := by
    have h2L : ((2 : ℕ) : AlgebraicClosure K) = 0 := CharP.cast_eq_zero _ 2
    rw [show ((3 : ℕ) : AlgebraicClosure K) = ((2 : ℕ) : AlgebraicClosure K) + 1 by norm_num,
      h2L, zero_add]
    exact one_ne_zero
  obtain ⟨i, α, hJeq, hα⟩ :=
    ExcTwoGen.exists_rationalComponent_and_root S (by decide : Tag.E6 ≠ .G2) hpL hTa hap h1 hJ'
  obtain ⟨b, hbR, hb3, hb1⟩ :=
    exists_rootDiagUnit_mem_rationalComponent_e6Two S hΦ hq hn hFrq hAlg hωo hωF i hα
  have hyJ : rootDiagUnit .E6 b ∈ J.map ι' := by
    rw [hJeq]
    exact hbR
  obtain ⟨y, hyJmem, hι'y⟩ := Subgroup.mem_map.1 hyJ
  have hE' : ∀ z ∈ E, ∃ c : Fin Tag.E6.rank → (AlgebraicClosure K)ˣ,
      ι' z = rootDiagUnit .E6 c := fun z hz => (hEfull z hz).imp fun _ h => h.1
  have hcomm : ∀ z ∈ E, y * z = z * y :=
    ExcTwoGen.commute_of_map_eq_rootDiagUnit hι'inj hE' hι'y
  have hb3' : b ^ 3 = 1 := by
    funext k
    simpa using hb3 k
  have hy3 : y ^ 3 = 1 := by
    apply hι'inj
    rw [map_pow, map_one, hι'y, rootDiagUnit_pow, hb3', rootDiagUnit_one]
  have hy1 : y ≠ 1 := by
    intro hy
    apply hb1
    rw [← hι'y, hy, map_one]
  exact ⟨y, hyJmem, hSC y hcomm hy3, hy1⟩

end E6TwoGen

end CFSG.StandardType
