module

public import CFSG.LocalAnalysis.StandardType.GGTPDefs
public import CFSG.LocalAnalysis.StandardType.GGKGAdjDefs
public import CFSG.LocalAnalysis.StandardType.GGKGAutDict
public import CFSG.LocalAnalysis.StandardType.GGKGWeylRootFacts
public import CFSG.LocalAnalysis.StandardType.GGKGLayersE6
public import CFSG.LocalAnalysis.StandardType.GGKGLayersTheta
public import CFSG.LocalAnalysis.StandardType.GGE6DepBlockLift
public import CFSG.LocalAnalysis.StandardType.GGTwE6D4RootFacts
public import CFSG.LocalAnalysis.StandardType.GGE6ThreeModelKGFrameE

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Adjoint CFSG.StandardType.TableBExc CFSG.RankThree.PartOne.KE8F CFSG.StandardType.TableBExc.E6Three
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.StandardType.NoOffRest

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private def ggTP_coord {L' : Type} [Group L'] {A : Subgroup (MulAut L')}
    (κ : A →* Multiplicative (Fin 6 → ZMod 3)) (a : A) : Fin Tag.E6.rank → ZMod 3 :=
  Multiplicative.toAdd (κ a)

theorem ggTPReflIn_E6 {K : Type} [Field K] [Finite K] {n : ℕ} (hn : 1 ≤ n)
    (hK : Nat.card K = 2 ^ n) (h3 : 3 ∣ 2 ^ n - 1) {L' : Type} [Group L'] [Finite L']
    (ψ : L' →* RecipeGroup Tag.E6 K) (A : Subgroup (MulAut L'))
    (hTB : GGTorusTBGroup 3 5 (RecipeGroup Tag.E6 K) (RecipeID Tag.E6 K) L' ψ A)
    (hA : Nat.card A = 3 ^ 5) {c : ↥A} (hc : GGCorootPt 3 (ggTorusAut A) c) {J : Subgroup L'}
    (hJ : IsComponentOf J (ggFix (c : MulAut L'))) :
    ∃ (κ : A →* Multiplicative (Fin 6 → ZMod 3)) (β : Fin Tag.E6.rank → ℤ),
      KGL.KGAutFrame A κ ∧ IsRoot Tag.E6 β ∧ Multiplicative.toAdd (κ c) = KGL.kgExpVec β ∧
        ∀ γ : Fin Tag.E6.rank → ℤ, IsRoot Tag.E6 γ → iform γ β = 0 →
          ∃ m ∈ J, MulAut.conj m ∈ Subgroup.normalizer (A : Set (MulAut L')) ∧
            ∀ a b : ↥A, (b : MulAut L') = MulAut.conj m * (a : MulAut L') * (MulAut.conj m)⁻¹ →
              Multiplicative.toAdd (κ b) = KGL.rootRefl γ (Multiplicative.toAdd (κ a)) := by
  classical
  haveI : Fintype K := Fintype.ofFinite K
  have hchar : ringChar K = 2 := by
    obtain ⟨m, hprime, hm⟩ := FiniteField.card K (ringChar K)
    have hcard : Fintype.card K = 2 ^ n := by
      rw [← Nat.card_eq_fintype_card]; exact hK
    rw [hcard] at hm
    have hdvd : ringChar K ∣ 2 ^ n := by
      rw [hm]
      exact dvd_pow_self _ m.pos.ne'
    exact (Nat.prime_dvd_prime_iff_eq hprime Nat.prime_two).mp
      (Nat.Prime.dvd_of_dvd_pow hprime hdvd)
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcardu : Nat.card Kˣ = 2 ^ n - 1 := by rw [Nat.card_units, hK]
  have h3u : 3 ∣ Nat.card Kˣ := by rw [hcardu]; exact h3
  obtain ⟨ζ, hζo⟩ := exists_prime_orderOf_dvd_card' 3 h3u
  have hζ : ζ ^ 3 = 1 := by rw [← hζo]; exact pow_orderOf_eq_one ζ
  obtain ⟨g, κ, hg, hκinj, hκrange, hconj, hweyl, hsimple⟩ :=
    KGL.kgFrameE6_holds K n hn hK h3 ζ hζ hζo L' ψ A hTB hA
  have hF : KGL.KGAutFrame A κ := ⟨hA, hκinj, hκrange, hweyl, hsimple⟩
  have hconjΘ : ∀ (a : A) (l : L'), KGL.kgThetaHom g (ψ ((a : MulAut L') l)) =
      rootDiagUnit Tag.E6 (zetaVec ζ hζ (ggTP_coord κ a)) *
        KGL.kgThetaHom g (ψ l) *
        (rootDiagUnit Tag.E6 (zetaVec ζ hζ (ggTP_coord κ a)))⁻¹ :=
    KGL.kgThetaHom_conj g (L' := L') (A := A) ψ
      (fun a => rootDiagUnit Tag.E6 (zetaVec ζ hζ (ggTP_coord κ a))) hconj
  obtain ⟨β, hβ, hκc⟩ := hF.corootPt hc
  have hκc' : ggTP_coord κ c = KGL.kgExpVec β := hκc
  let ER : Subgroup (RecipeGroup Tag.E6 K) :=
    (rootSpan Tag.E6 K (famKernel {zetaVec ζ hζ (ggTP_coord κ c)})).comap
      (KGL.kgThetaHom g)
  have hER : GGLayerOf (ggRFix ψ {(c : MulAut L')}) ER := by
    have h1' := KGL.kgAdjL1 K hchar ζ hζ hζo β hβ
    rw [← hκc'] at h1'
    exact KGL.layer_of_famCentralizer ψ hTB.1 (KGL.kgThetaHom g) (KGL.kgThetaHom_injective g)
      (KGL.kgThetaHom_range g hg) {(c : MulAut L')}
      {zetaVec ζ hζ (ggTP_coord κ c)}
      (by
        rintro f hf
        rw [Set.mem_singleton_iff] at hf
        subst hf
        exact ⟨zetaVec ζ hζ (ggTP_coord κ c), by simp, fun l => hconjΘ c l⟩)
      (by
        rintro a ha
        rw [Set.mem_singleton_iff] at ha
        subst ha
        exact ⟨(c : MulAut L'), by simp, fun l => hconjΘ c l⟩)
      h1'
  have hFc : ∀ f ∈ ({(c : MulAut L')} : Set (MulAut L')),
      ∃ φ : MulAut (RecipeGroup Tag.E6 K), ∀ l : L', φ (ψ l) = ψ (f l) := by
    intro f hf
    rw [Set.mem_singleton_iff] at hf
    subst hf
    obtain ⟨φ, -, hφ⟩ := hTB.2.2.2.2.1 c c.2
    exact ⟨φ, hφ⟩
  have hC : ∀ l : L', l ∈ ggFix (c : MulAut L') ↔
      ∀ f ∈ ({(c : MulAut L')} : Set (MulAut L')), f l = l := by
    intro l
    rw [mem_ggFix]
    constructor
    · intro h f hf
      rw [Set.mem_singleton_iff] at hf
      subst hf
      exact h
    · intro h
      exact h c (by simp)
  obtain ⟨E, hEcomp, huniq, hmaxC, hmap⟩ :=
    ggLayerOf_lift ψ hTB.1 hTB.2.1 ({(c : MulAut L')} : Set (MulAut L')) hFc
      (ggFix (c : MulAut L')) hC hER
  have hJE : J = E := huniq J hJ
  refine ⟨κ, β, hF, hβ, hκc, ?_⟩
  rintro γ hγ hγβ
  have hspec := rootWeylOne_spec (τ := Tag.E6) (K := K) hγ
  have hmono : rootWeylOne Tag.E6 K γ ∈ monomialSubgroup Tag.E6 K := hspec.2.1
  have hmaps : MapsRootLines (rootWeylOne Tag.E6 K γ) (rootReflection γ) := hspec.2.2
  have hγS : γ ∈ famKernel {zetaVec ζ hζ (ggTP_coord κ c)} := by
    rw [hκc', KGL.famKernel_kgExpVec_single hζo hζ hβ]
    exact ⟨hγ, hγβ⟩
  have hnegS : -γ ∈ famKernel {zetaVec ζ hζ (ggTP_coord κ c)} := by
    rw [hκc', KGL.famKernel_kgExpVec_single hζo hζ hβ]
    refine ⟨IsRoot.neg hγ, ?_⟩
    rw [iform_neg_left, hγβ, neg_zero]
  have hspan : rootWeylOne Tag.E6 K γ ∈
      rootSpan Tag.E6 K (famKernel {zetaVec ζ hζ (ggTP_coord κ c)}) :=
    (sup_le (rootSubgroup_le_rootSpan hγS) (rootSubgroup_le_rootSpan hnegS)) hspec.1
  have hspan_adj : rootWeylOne Tag.E6 K γ ∈ adjointGroup Tag.E6 K :=
    rootSpan_le_adjointGroup K _ hspan
  obtain ⟨n, hn⟩ := show rootWeylOne Tag.E6 K γ ∈ (KGL.kgThetaHom g).range from by
    rw [KGL.kgThetaHom_range g hg]; exact hspan_adj
  have hnER : n ∈ ER := by
    change KGL.kgThetaHom g n ∈
      rootSpan Tag.E6 K (famKernel {zetaVec ζ hζ (ggTP_coord κ c)})
    rw [hn]; exact hspan
  have hnEmap : n ∈ E.map ψ := by rw [hmap]; exact hnER
  obtain ⟨l, hlE, hlψ⟩ := Subgroup.mem_map.mp hnEmap
  have hlJ : l ∈ J := by rw [hJE]; exact hlE
  have hDl : KGL.kgThetaHom g (ψ l) = rootWeylOne Tag.E6 K γ := by rw [hlψ, hn]
  have hD : ∀ a₁ : A, ∃ a₂ : A,
      (a₂ : MulAut L') = MulAut.conj l * (a₁ : MulAut L') * (MulAut.conj l)⁻¹ ∧
      ggTP_coord κ a₂ = KGL.rootRefl γ (ggTP_coord κ a₁) := by
    intro a₁
    have hx := hF.toAdd_mem_hypE6 a₁
    have hx' := KGL.rootRefl_mem_hypE6 hγ hx
    obtain ⟨a₂, ha₂⟩ := hF.exists_of_mem_hypE6 hx'
    have ha₂' : ggTP_coord κ a₂ = KGL.rootRefl γ (ggTP_coord κ a₁) := ha₂
    have hkey : rootDiagUnit Tag.E6 (zetaVec ζ hζ (ggTP_coord κ a₂)) =
        KGL.kgThetaHom g (ψ l) *
          rootDiagUnit Tag.E6 (zetaVec ζ hζ (ggTP_coord κ a₁)) *
          (KGL.kgThetaHom g (ψ l))⁻¹ := by
      rw [ha₂', hDl]
      rw [KGL.TwLayer.monomial_conj_rootDiagUnit_zetaVec hζ hmono hmaps (ggTP_coord κ a₁),
        KGL.adAct_rootReflection_eq_rootRefl hγ]
    refine ⟨a₂, ?_, ha₂'⟩
    refine KGL.mulAut_eq_of_comp_eq ψ hTB.2.1 hTB.2.2.1 (fun z => ?_)
    apply KGL.kgThetaHom_injective g
    rw [KGL.kgThetaHom_conjAut_apply g ψ _ hconjΘ l a₁ z (Dl := KGL.kgThetaHom g (ψ l)) rfl,
      hconjΘ a₂ z, hkey]
  choose f hf using hD
  have hfeq : ∀ a : A, (f a : MulAut L') =
      MulAut.conj l * (a : MulAut L') * (MulAut.conj l)⁻¹ := fun a => (hf a).1
  have hfcoord : ∀ a : A, ggTP_coord κ (f a) = KGL.rootRefl γ (ggTP_coord κ a) :=
    fun a => (hf a).2
  have hfinj : Function.Injective f := by
    intro a₁ a₂ h
    have h1 : (MulAut.conj l * (a₁ : MulAut L') * (MulAut.conj l)⁻¹) =
        (MulAut.conj l * (a₂ : MulAut L') * (MulAut.conj l)⁻¹) := by
      rw [← hfeq a₁, ← hfeq a₂, h]
    exact Subtype.ext (by
      have := congrArg (fun m : MulAut L' => (MulAut.conj l)⁻¹ * m * MulAut.conj l) h1
      simpa [mul_assoc] using this)
  have hfsurj : Function.Surjective f := (Function.Injective.bijective_of_finite hfinj).2
  have hnorm : MulAut.conj l ∈ Subgroup.normalizer (A : Set (MulAut L')) := by
    rw [Subgroup.mem_normalizer_iff]
    intro a₁
    constructor
    · intro ha₁
      rw [← hfeq ⟨a₁, ha₁⟩]
      exact (f ⟨a₁, ha₁⟩).2
    · intro hb
      obtain ⟨a', ha'⟩ := hfsurj ⟨MulAut.conj l * a₁ * (MulAut.conj l)⁻¹, hb⟩
      have h1 : (MulAut.conj l * (a' : MulAut L') * (MulAut.conj l)⁻¹) =
          MulAut.conj l * a₁ * (MulAut.conj l)⁻¹ := by
        rw [← hfeq a', ha']
      have h2 : (a' : MulAut L') = a₁ := by
        have := congrArg (fun m : MulAut L' => (MulAut.conj l)⁻¹ * m * MulAut.conj l) h1
        simpa [mul_assoc] using this
      rw [← h2]
      exact a'.2
  refine ⟨l, hlJ, hnorm, ?_⟩
  intro a b hb
  change ggTP_coord κ b = KGL.rootRefl γ (ggTP_coord κ a)
  have hbeq : b = f a := Subtype.ext (by rw [hb, hfeq a])
  rw [hbeq, hfcoord a]

end CFSG.StandardType

end
