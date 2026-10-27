module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveKGCentDefs
public import CFSG.LieType.Steinberg.Isogeny.E6
public import CFSG.LocalAnalysis.StandardType.GGSixLayerFactsExcSixEReduce
public import CFSG.RankThree.PartOne.KE8F.FamBruhat
public import CFSG.LieType.Chevalley.RootCharacterConjugation
import CFSG.LocalAnalysis.StandardType.GGSecFiveKGCentRank
import CFSG.LocalAnalysis.StandardType.GGSecFiveKGCentCorank
import CFSG.LocalAnalysis.StandardType.GGSecFiveKGCentE6FamKernel
import CFSG.LocalAnalysis.StandardType.GGSecFiveKGCentE6TorusChar
import CFSG.LocalAnalysis.StandardType.GGSecFiveJRootCoreE6Char
import CFSG.LocalAnalysis.StandardType.GGSixLayerFactsExcSixEMain
import CFSG.LieType.Steinberg.CentralExt.MinusculeCenter
public import CFSG.Monster.B.Geometry.CoxeterWords
public import CFSG.RankThree.PartOne.KE.A1SL2
public import CFSG.RankThree.PartOne.KE.A1Torus
public import CFSG.RankThree.PartOne.KE.SigmaUntwisted
public import CFSG.RankThree.PartOne.KE.StabGeneral

public section

namespace CFSG.StandardType

namespace KGCentE6

open CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Universal
  CFSG.LieType.Steinberg CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.RankThree.PartOne.KE8F

theorem ggKGCent_keyHyps_E6
    (ha₀ : GGLNoncyclicInput) (hL : GGLBalanceInput)
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)} (hcfg : GGSecFiveRouteCfg p B Bs x L D J 𝒦)
    {r : MulAut ↥Bs} (hr : r ∈ ggAutomizer J Bs) (hrefl : GGIsReflection p r)
    {X : Subgroup G} (hX : X = L ∨ X ∈ 𝒦) {n f : ℕ} {ψ : (ggU .E6 n f).K →* G}
    (hloc : GGKGPosLocalHyp p Bs X .E6 n f ψ) (hstd : GGKGPosStdPos (ggU .E6 n f).D ψ Bs)
    {F : Set (Fin Tag.E6.rank → (GaloisField 2 f)ˣ)}
    (hFD : F = {a | ∃ d ∈ D, LayerSixE.GGInduces (Isogeny.e6Isogeny (GaloisField 2 f)) ψ d
      (rootDiagAutHom .E6 (GaloisField 2 f) a)}) :
    2 ≤ f ∧ p.Prime ∧ p ≠ 2 ∧ p ∣ Nat.card (GaloisField 2 f)ˣ ∧ (∀ a ∈ F, ∀ i, a i ^ p = 1) ∧
      (famKernel F).Nonempty ∧ (∃ z ∈ F, famKernel F = famKernel {z}) ∧
      (p ≠ 3 → Set.ncard {b : Fin Tag.E6.rank → (GaloisField 2 f)ˣ | (∀ i, b i ^ p = 1) ∧
        ∀ β ∈ famKernel F, rootChar b β = 1} ≤ p) := by
  have hp : p.Prime := hloc.1.1
  have hpf : p ∣ 2 ^ f - 1 := hloc.2.1.2.2.2
  have hf : 2 ≤ f := by
    have h1 : 1 ≤ f := hloc.1.2.2.1.2.1
    by_contra h
    have h2 : 2 ^ f - 1 = 1 := by
      rw [show f = 1 by omega]
      norm_num
    rw [h2, Nat.dvd_one] at hpf
    exact hp.ne_one hpf
  have hq : Nat.card (GaloisField 2 f) = 2 ^ f := GaloisField.card 2 f (by omega)
  have hpK : p ∣ Nat.card (GaloisField 2 f)ˣ := by
    rw [Nat.card_units, hq]
    exact hpf
  have hker : ψ.ker ≤ Subgroup.center (ggU .E6 n f).K := hloc.2.1.1
  have hkπ := LayerSixE.ker_le_ker_e6Isogeny (k := GaloisField 2 f) hker
  have hπ := Isogeny.e6Isogeny_surjective (GaloisField 2 f)
  have hDBs : D ≤ Bs := hcfg.1.1.2.2.1.1.trans hcfg.1.1.2.1.1
  have hDN : D ≤ Subgroup.normalizer (ψ.range : Set G) := by
    rw [hloc.2.1.2.1]
    exact hDBs.trans hloc.2.2.1.2.1
  have hD : CFSG.Open.IsElemAbelian p D := hcfg.1.1.2.2.1.2.1
  have hDa : ∀ d ∈ D, ∃ a : Fin Tag.E6.rank → (GaloisField 2 f)ˣ, a ^ p = 1 ∧
      LayerSixE.GGInduces (Isogeny.e6Isogeny (GaloisField 2 f)) ψ d
        (rootDiagAutHom .E6 (GaloisField 2 f) a) := fun d hd =>
    JCoreE6.exists_induces_rootDiag_E6 (k := GaloisField 2 f) ψ hker (hDN hd) (hD.2 d hd)
      (hstd d (hDBs hd))
  have hroot : ∀ β ∈ ggKGCentRoots (ggU .E6 n f).D ψ D, IsRoot .E6 β := fun β hβ =>
    (Minuscule.e6Data_valid.mem_minDatum_roots Minuscule.isFiniteType_cartan_E6
      (GaloisField 2 f)).1 hβ.1
  have hΦ : ggKGCentRoots (ggU .E6 n f).D ψ D ⊆ famKernel F := by
    intro β hβ
    refine ⟨hroot β hβ, ?_⟩
    rw [hFD]
    rintro a ⟨d, hd, had⟩
    have hz := Subgroup.mem_comap.1
      (hβ.2 (Minuscule.e6Data_valid.xm_mem_rootGroup (GaloisField 2 f) β 1))
    exact rootChar_eq_one_of_commute_E6 had (hroot β hβ)
      (Subgroup.mem_centralizer_iff.1 hz d hd)
  have hXe' : ∀ e : G, X ≤ Subgroup.centralizer ({e} : Set G) →
      ψ.range ≤ Subgroup.centralizer ({e} : Set G) := fun e he => by
    rw [hloc.2.1.2.1]
    exact he
  obtain ⟨β, hβ, -⟩ := ggKGCent_exists_root_add ha₀ hL hcfg hr hrefl hX hloc hstd
  obtain ⟨e, heD, he, hXe⟩ := exists_ne_one_le_centralizer_of_routeCfg hcfg hX
  refine ⟨hf, hp, hloc.1.2.1, hpK, ?_, ⟨β, hΦ hβ⟩, exists_famKernel_eq_singleton hπ hkπ hp
    hcfg.1.1.2.2.1.2.2.1 hDN (fun d hd => (hDa d hd).imp fun _ h => h.2) heD he (hD.2 e heD)
    (ggInduces_one_of_le_centralizer hkπ (hXe' e hXe)) hFD, fun hp3 => ?_⟩
  · rw [hFD]
    rintro a ⟨d, hd, had⟩ i
    obtain ⟨a', ha'p, ha'⟩ := hDa d hd
    rw [rootDiagAutHom_injective (had.unique hπ (hDN hd) ha')]
    exact congrFun ha'p i
  · have hZ : ¬ p ∣ Nat.card (Subgroup.center (ggU .E6 n f).K) := by
      intro h
      have h3 : p ∣ Nat.gcd 3 (Nat.card (GaloisField 2 f) - 1) := by
        rw [← (CentralExt.MinusculeClosed.card_center_e6 (GaloisField 2 f)).1]
        exact h
      exact hp3 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1
        (h3.trans (Nat.gcd_dvd_left 3 _)))
    calc Set.ncard {b : Fin Tag.E6.rank → (GaloisField 2 f)ˣ | (∀ i, b i ^ p = 1) ∧
          ∀ β ∈ famKernel F, rootChar b β = 1}
        ≤ Set.ncard {b : Fin Tag.E6.rank → (GaloisField 2 f)ˣ | (∀ i, b i ^ p = 1) ∧
          ∀ β ∈ ggKGCentRoots (ggU .E6 n f).D ψ D, rootChar b β = 1} :=
          Set.ncard_le_ncard fun b hb => ⟨hb.1, fun β hβ => hb.2 β (hΦ hβ)⟩
      _ ≤ _ := ncard_rootChar_le_ncard_torus_E6 hp hp3
      _ ≤ p := ggKGCent_card_torus_le ha₀ hL hcfg hr hrefl hX hloc hstd hZ

end KGCentE6

end CFSG.StandardType

end
