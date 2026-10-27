module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveJoinPrimed
public import CFSG.LocalAnalysis.StandardType.GGSecFiveKGPosPrimed
import CFSG.LocalAnalysis.StandardType.GGKGPosGenCox
import CFSG.LocalAnalysis.StandardType.GGSecFiveRk1OfKGPos
import CFSG.LocalAnalysis.StandardType.GGCoxReflConv
import CFSG.LocalAnalysis.StandardType.GGKGPosTagWeyl
import CFSG.Quasithin.Vol2.Ch10SecHeLMain
import CFSG.LocalAnalysis.ComponentInitial.CommutingBlock
import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115Reduce
import CFSG.Quasithin.Background.A3Structure312Facts
import CFSG.Quasithin.Background.A3Structure36A
import CFSG.Quasithin.Background.A3Structure36BBase
import CFSG.Quasithin.Background.A3Structure36BPrimeDataBase
import CFSG.Quasithin.Background.B1More13A
import CFSG.Quasithin.Background.B1More13Defs
import CFSG.Quasithin.Background.B1MoreEleven
import CFSG.Quasithin.Background.B5CompA
import CFSG.Quasithin.Background.B5CompB
import CFSG.Quasithin.Background.B5FinOut
import CFSG.Quasithin.Background.B6
import CFSG.Quasithin.Background.B6Example
import CFSG.Quasithin.Background.E2Hyp
import CFSG.Quasithin.Background.E2SolvTwo
import CFSG.Quasithin.Background.F9FiveStruct
import CFSG.Quasithin.Background.F9G2
import CFSG.Quasithin.Background.F9Geometry
import CFSG.Quasithin.Background.InternalSecAutOn
import CFSG.Quasithin.Background.InternalSecB4
import CFSG.Quasithin.EmptyFaithful.GoldschmidtF112ListC
import CFSG.Quasithin.EmptyFaithful.S142Statements
import CFSG.Quasithin.H13.A5S1326
import CFSG.Quasithin.H13.A5Top
import CFSG.Quasithin.Vol2.Ch11StatementsB
import CFSG.Quasithin.Vol2.Ch11StatementsC
import CFSG.Quasithin.Vol2.Ch12Sec2Statements
import CFSG.Quasithin.Vol2.Ch1Faithful
import CFSG.Quasithin.Vol2.Ch3Sec3StatementsB
import Certificates.Certificate8026Base

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.LieType.Universal
  CFSG.LieType.RootSystem CFSG.ClassicalInvolution.WeakCT CFSG.LieType.Steinberg

section Defs

@[expose] def GGSecFiveJReflInput'
    : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (𝒦 : Finset (Subgroup G)), GGSecFiveRouteCfg' p B Bs x L D J 𝒦 → GGSplitLie p L →
      ∃ r ∈ ggAutomizer J Bs, GGIsReflection p r

end Defs

section Lemmas

theorem s2jn_exists_weylAction_of_mem_roots
    {U : Type*} [Group U] (D : UniversalRootDatum U)
    (hdiv : D.divisible = ∅) {γ : Fin D.rank → ℤ} (hγ : γ ∈ D.roots) :
    ∃ (w : (coxeterMatrix D.isFiniteType).Group) (i : Fin D.rank),
      γ = weylAction D.isFiniteType w (Pi.single i 1) := by
  change γ ∈ roots D.isFiniteType D.divisible at hγ
  rw [roots, Set.mem_union, Set.mem_setOf_eq, Set.mem_setOf_eq] at hγ
  rcases hγ with ⟨w, i, rfl⟩ | ⟨w, i, hi, rfl⟩
  · exact ⟨w, i, rfl⟩
  · rw [hdiv] at hi
    simp at hi

theorem s2jn_ggU_divisible_eq_empty
    {t : StatedLieTag} {n f : ℕ}
    (ht : t = .PSL ∨ t = .POmegaPlus ∨ t = .E6 ∨ t = .E7 ∨ t = .E8) :
    (ggU t n f).D.divisible = ∅ := by
  rcases ht with rfl | rfl | rfl | rfl | rfl
  · cases n with
    | zero => simp only [ggU, lieUniversal]; rfl
    | succ m => simp only [ggU, lieUniversal]; rfl
  · by_cases hn : 3 ≤ n
    · have e : ggU .POmegaPlus n f =
          ⟨↥(spinGroup (Spin.quadPlus n (GaloisField 2 f))),
            Spin.plusDatum n (GaloisField 2 f) hn⟩ := by
        simp only [ggU, lieUniversal, hn, ↓reduceDIte]
      rw [e]
      rfl
    · have e : ggU .POmegaPlus n f = trivialUniversal := by
        simp only [ggU, lieUniversal, hn, ↓reduceDIte]
      rw [e]
      rfl
  · simp only [ggU, lieUniversal]
    rfl
  · simp only [ggU, lieUniversal]
    rfl
  · simp only [ggU, lieUniversal]
    rfl

end Lemmas

@[expose] def GGJRootCoreInput
    : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (Bs L J : Subgroup G) (t : StatedLieTag) (n f : ℕ)
    (ψ : (ggU t n f).K →* G) (y : G), GGKGPosLocalHyp p Bs L t n f ψ →
      GGKGPosStdPos (ggU t n f).D ψ Bs → y ∈ Bs →
      CFSG.Assembly.IsComponentOf J (L ⊓ Subgroup.centralizer ({y} : Set G)) →
      ∃ γ ∈ (ggU t n f).D.roots, (ggRootLevi (ggU t n f).D γ).map ψ ≤ J

section Main2

theorem s2jn_ggSecFiveJReflInput'_of_core
    (hcore : GGJRootCoreInput) :
    GGSecFiveJReflInput' := by
  intro G _ _ p B Bs x L D J 𝒦 hcfg hL
  obtain ⟨t, n, f, ψ, hloc, hstd, hTB⟩ := s2jn_exists_tableBFrame G p B Bs x L D J 𝒦 hcfg hL
  have hC : GGConfig p B Bs x L D J := hcfg.1.1
  have hS : LargeEvenSStar p B x L := hcfg.1.1.1.2.2.2.2.2.2.1
  have hLc : CFSG.Assembly.IsComponentOf L (Subgroup.centralizer ({x} : Set G)) := hS.2.2.2.1
  have hxne : x ≠ 1 := hS.2.2.1
  have hDx : x ∈ D := hC.2.2.1.2.2.2.1
  have hDB : D ≤ B := hC.2.2.1.1
  have hBBs : B ≤ Bs := hC.2.1.1
  have hDel : IsElemAbelian p D := hC.2.2.1.2.1
  have hDcard : Nat.card D = p ^ 2 := hC.2.2.1.2.2.1
  have hJcomp : CFSG.Assembly.IsComponentOf J (L ⊓ Subgroup.centralizer (D : Set G)) :=
    hC.2.2.1.2.2.2.2.2.1
  have hloc' := hloc
  obtain ⟨⟨hp, hp2, hadm, h3t⟩, ⟨hker, hrange, ht, hpf⟩, -, -⟩ := hloc
  haveI := Fact.mk hp
  have hxp : x ^ p = 1 := hDel.2 x hDx
  have hz : Nat.card (Subgroup.zpowers x) = p := by
    rw [Nat.card_zpowers]; exact orderOf_eq_prime hxp hxne
  obtain ⟨y, hyD, hyz⟩ : ∃ y ∈ D, y ∉ Subgroup.zpowers x := by
    by_contra h
    push Not at h
    have hle : D ≤ Subgroup.zpowers x := fun y hy => h y hy
    have := Subgroup.card_le_of_le hle
    rw [hDcard, hz] at this
    have h2 := hp.two_le
    nlinarith
  set H : Subgroup G := Subgroup.closure {x, y} with hH
  have hHD : H ≤ D := (Subgroup.closure_le _).mpr (by
    intro g hg
    rcases hg with rfl | rfl
    · exact hDx
    · exact hyD)
  have hzH : Subgroup.zpowers x ≤ H :=
    Subgroup.zpowers_le.mpr (Subgroup.subset_closure (by simp))
  have hyH : y ∈ H := Subgroup.subset_closure (by simp)
  have hHD' : H = D := by
    apply Subgroup.eq_of_le_of_card_ge hHD
    have hdvd : Nat.card H ∣ p ^ 2 := by
      rw [← hDcard]; exact Subgroup.card_dvd_of_le hHD
    obtain ⟨k, hk, hkH⟩ := (Nat.dvd_prime_pow hp).mp hdvd
    have hpH : p ∣ Nat.card H := by rw [← hz]; exact Subgroup.card_dvd_of_le hzH
    interval_cases k
    · rw [pow_zero] at hkH
      rw [hkH] at hpH
      exact absurd (Nat.le_of_dvd one_pos hpH) (by have := hp.two_le; omega)
    · exfalso
      rw [pow_one] at hkH
      have : Subgroup.zpowers x = H :=
        Subgroup.eq_of_le_of_card_ge hzH (by rw [hz, hkH])
      exact hyz (this ▸ hyH)
    · rw [hkH, hDcard]
  have hcent : L ⊓ Subgroup.centralizer (D : Set G) = L ⊓ Subgroup.centralizer ({y} : Set G) := by
    apply le_antisymm
    · exact inf_le_inf_left _ (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hyD))
    · rintro g ⟨hgL, hgy⟩
      refine ⟨hgL, ?_⟩
      show g ∈ Subgroup.centralizer (D : Set G)
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      have hh' : h ∈ H := by rw [hHD']; exact hh
      refine Subgroup.closure_induction (p := fun h _ => h * g = g * h) ?_ ?_ ?_ ?_ hh'
      · intro a ha
        rcases ha with rfl | rfl
        · exact (Subgroup.mem_centralizer_iff.mp (hLc.1 hgL)) a rfl
        · exact (Subgroup.mem_centralizer_iff.mp hgy) a rfl
      · simp
      · intro a b _ _ ha hb
        rw [mul_assoc, hb, ← mul_assoc, ha, mul_assoc]
      · intro a _ ha
        calc a⁻¹ * g = a⁻¹ * (g * a) * a⁻¹ := by group
          _ = a⁻¹ * (a * g) * a⁻¹ := by rw [← ha]
          _ = g * a⁻¹ := by group
  rw [hcent] at hJcomp
  have hyBs : y ∈ Bs := hBBs (hDB hyD)
  obtain ⟨γ, hγ, hγJ⟩ := hcore G p Bs L J t n f ψ y hloc' hstd hyBs hJcomp
  obtain ⟨ε, hεrefl, hεlevi, -⟩ := hTB
  have hdiv : (ggU t n f).D.divisible = ∅ := s2jn_ggU_divisible_eq_empty ht
  obtain ⟨w, i, rfl⟩ := s2jn_exists_weylAction_of_mem_roots (ggU t n f).D hdiv hγ
  set r : MulAut ↥Bs := ((ε (w * (coxeterMatrix (ggU t n f).D.isFiniteType).simple i * w⁻¹) : ↥(ggAutomizer L Bs)) : MulAut ↥Bs) with hr
  have hrA : r ∈ ggAutomizer L Bs := (ε (w * (coxeterMatrix (ggU t n f).D.isFiniteType).simple i * w⁻¹)).2
  have hr' : r = ((ε w : ↥(ggAutomizer L Bs)) : MulAut ↥Bs) *
      ((ε ((coxeterMatrix (ggU t n f).D.isFiniteType).simple i) : ↥(ggAutomizer L Bs)) : MulAut ↥Bs) *
      ((ε w : ↥(ggAutomizer L Bs)) : MulAut ↥Bs)⁻¹ := by
    rw [hr, map_mul, map_mul, map_inv]
    rfl
  have hrefl : GGIsReflection p r := by
    rw [hr']
    exact GGIsReflection.conj' (hεrefl i) ((ε w : ↥(ggAutomizer L Bs)) : MulAut ↥Bs)
  have hr2 : r * r = 1 := by simpa [sq] using hrefl.1
  have hlev : ggRankOneIn L Bs r ≤ J := by
    have := hεlevi w i
    rw [this]
    exact hγJ
  obtain ⟨m, hmR, hmN, hm⟩ := ggExists_weylElt_of_mem_ggAutomizer hrA hr2
  exact ⟨r, mem_ggAutomizer_iff.mpr ⟨m, hlev hmR, hmN, hm⟩, hrefl⟩

end Main2

end CFSG.StandardType
