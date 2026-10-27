module

public import Certificates.Certificate13605
public import Certificates.Certificate13721
public import Certificates.Certificate13723
public import CFSG.LocalAnalysis.StandardType.GGTBJE8LeviEnnola
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.TwCompSUE7
public import CFSG.HardMathSupport.Meierfrankenfeld.Proving.E7Curtis.E7Arith
public import CFSG.LocalAnalysis.StandardType.GGTBJE7LeviCore
public import CFSG.LocalAnalysis.StandardType.GGTBJE7Levi
public import CFSG.LocalAnalysis.StandardType.GGTBJE7LeviEnnFrame
public import CFSG.LocalAnalysis.StandardType.GGTBJE7LeviEnnComp
public import CFSG.LocalAnalysis.StandardType.GGTBJE7LeviEnnModel

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.AlgebraicGroups

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem e7Enn_leviFrame
    {K : Type} [Field K] [Finite K] [CharP K 2] {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    {n : ℕ} (hq : Nat.card K = 2 ^ n) (hpn : p ∣ 2 ^ n + 1)
    (E : Subgroup (adjointGroup .E7 K)) (hE : IsElemAbelian p E) (hcard : p ^ 6 ≤ Nat.card E)
    (hSC : ∀ g : adjointGroup .E7 K, (∀ c ∈ E, g * c = c * g) → g ^ p = 1 → g ∈ E) :
    GGE7LeviFrame p E := by
  have hp : p.Prime := Fact.out
  have hpK : p ∣ Nat.card K + 1 := by rw [hq]; exact hpn
  obtain ⟨ζ, hζ, ιT, nk, S, ι, hζo, hιTinj, hιTrange, hact, -, hSq, hιinj, hιrange, hιιT, hT,
    hρ, wt, hwn, hwt⟩ := e7Enn_frame (K := K) hp2 hpK E hE hcard hSC
  have hnpos : 0 < n := by
    by_contra h
    have hn0 : n = 0 := by omega
    subst hn0
    norm_num at hpn
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp hpn)
  have hq2 : S.D.q = 2 ^ n := by rw [hSq, hq]
  refine ⟨AlgebraicClosure K, inferInstance, ζ, hζ, ιT, nk, _, wt, hζo, hιTinj, hιTrange, hact,
    hwn, hwt, fun t ht Y hY => ?_⟩
  obtain ⟨i, hi, hCENT⟩ := e7Enn_class (K := K) hp2 S ι hιinj hιrange hιιT hT
    (fun γ hγ => Or.inr (hρ γ hγ)) ht hY
  exact ⟨i, hCENT, fun v Sd hSd hΨ =>
    e7Enn_lower (K := K) (p := p) S ι hιinj hιιT hρ hnpos hq2 i hi hSd hΨ⟩

theorem ggE7Enn_leviModel_L
    (hRig : GGLabelRigidInput) {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K) {n : ℕ}
    (hΛ : LargeEvenInLambda2 (⟨.E7, 0, n⟩ : LargeEvenLabel))
    (hL : GGHasLabel (⟨.E7, 0, n⟩ : LargeEvenLabel) (↥L ⧸ Subgroup.center ↥L))
    (hpn : p ∣ 2 ^ n + 1) :
    GGE7LeviModel p Bs L := by
  obtain ⟨hN, Fq, _, _, _, hFqcard, e, E, hE, hEcard, hEself, hA⟩ :=
    ggE7Enn_model_L hRig hH hΛ hL hpn
  exact ⟨hN, Fq, inferInstance, inferInstance, inferInstance, e, E, hA,
    e7Enn_leviFrame hH.1.1.2.2.2.2.2.1.2.1 hFqcard hpn E hE hEcard hEself⟩

theorem ggE7Enn_leviModel_K
    (hRig : GGLabelRigidInput) {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K) {n : ℕ}
    (hΛ : LargeEvenInLambda2 (⟨.E7, 0, n⟩ : LargeEvenLabel))
    (hK : GGHasLabel (⟨.E7, 0, n⟩ : LargeEvenLabel) (↥K ⧸ Subgroup.center ↥K))
    (hpn : p ∣ 2 ^ n + 1) :
    GGE7LeviModel p Bs K := by
  obtain ⟨hN, Fq, _, _, _, hFqcard, e, E, hE, hEcard, hEself, hA⟩ :=
    ggE7Enn_model_K hRig hH hΛ hK hpn
  exact ⟨hN, Fq, inferInstance, inferInstance, inferInstance, e, E, hA,
    e7Enn_leviFrame hH.1.1.2.2.2.2.2.1.2.1 hFqcard hpn E hE hEcard hEself⟩

end CFSG.StandardType

end
