module

public import CFSG.LocalAnalysis.StandardType.GGXInLCommTwE6
public import CFSG.LocalAnalysis.StandardType.GGXInLE6Sylow
public import CFSG.LocalAnalysis.StandardType.GGXInLE6Frame
public import CFSG.LocalAnalysis.StandardType.GGXInLUCover
public import CFSG.LocalAnalysis.StandardType.GGXInLE6
public import CFSG.LocalAnalysis.StandardType.GGXInLUDefs
public import CFSG.LocalAnalysis.StandardType.GGXInLQuot
public import CFSG.LocalAnalysis.StandardType.GGTwE6ThreeRootGenFrame
public import CFSG.LocalAnalysis.StandardType.GGTableBUnit63Desc
public import CFSG.LocalAnalysis.StandardType.GGTwE6R4CoverNine
public import CFSG.LocalAnalysis.StandardType.GGE6ThreeModelFrameMap
public import CFSG.LocalAnalysis.StandardType.GGTableBTwE6DeltaOutdiag
public import CFSG.LocalAnalysis.StandardType.GGTableBNbrInner937TwE6Center
public import CFSG.LocalAnalysis.StandardType.GGE6ThreeModelModuleMT
public import CFSG.LocalAnalysis.StandardType.GGCoverRkTwE6Frame
public import CFSG.LocalAnalysis.StandardType.GGBstarLemmaCNoTwoSub
public import CFSG.LocalAnalysis.StandardType.GGNbrLangQ1TwE6Three

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.LieType.Chevalley

open scoped Pointwise

attribute [local instance] commutatorElement

namespace GGXInLE6Assembly

variable {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G}
  {L D J : Subgroup G}

private theorem twE6_transport_quotient
    (hS : GGQTwoSetting p B Bs x L D J) (hxL : x ∈ L) (hp : p = 3)
    (N : Subgroup ↥(L ⊔ Bs)) [N.Normal] (hNL : N ≤ L.subgroupOf (L ⊔ Bs))
    (hNcop : Nat.Coprime 3 (Nat.card N))
    {E0 L0 T Nsub : Subgroup (↥(L ⊔ Bs) ⧸ N)} {z : (↥(L ⊔ Bs) ⧸ N)}
    (hE0 : E0 = Subgroup.map (QuotientGroup.mk' N) (Bs.subgroupOf (L ⊔ Bs)))
    (hL0 : L0 = Subgroup.map (QuotientGroup.mk' N) (L.subgroupOf (L ⊔ Bs)))
    (hF : GGXInL.lup8f_QuotFrame (↥(L ⊔ Bs) ⧸ N) E0 L0 T Nsub z)
    (hz : z = QuotientGroup.mk' N (⟨x, Subgroup.mem_sup_left hxL⟩ : ↥(L ⊔ Bs))) :
    x ∈ ⁅Bs, L ⊓ Subgroup.normalizer (Bs : Set G)⁆ := by
  classical
  have hSStar : LargeEvenSStar p B x L := hS.1.1.1.2.2.2.2.2.2.1
  have hxBs : x ∈ Bs := hS.1.1.2.1.1 hSStar.2.1
  have hEbs : IsPGroup p Bs := by
    intro g
    exact ⟨1, Subtype.ext (by simpa using hS.1.1.2.1.2.1.2 (g : G) g.2)⟩
  have hEp : IsPGroup p (Bs.subgroupOf (L ⊔ Bs)) := hEbs.comap_subtype
  have hEp3 : IsPGroup 3 (Bs.subgroupOf (L ⊔ Bs)) := hp ▸ hEp
  rw [GGXInL.lup8f_mem_commutator_sup hxL]
  exact (GGXInL.mem_commutator_iff_map_quotient (L.subgroupOf (L ⊔ Bs))
    (Bs.subgroupOf (L ⊔ Bs)) N hNL hNcop hEp3
    (Subgroup.mem_subgroupOf.mpr hxBs)).mpr (by
      have h := GGXInL.lup8f_commutator_of_frame hF
      rw [hz] at h
      rwa [hE0, hL0] at h)

end GGXInLE6Assembly


private theorem twE6_literal_data
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G}
    (hS : GGQTwoSetting p B Bs x L D J) (hxL : x ∈ L) (hp : p = 3)
    (hE6 : GGInnerDiagOnLabel
      (fun p lab => GGLabQTwo p lab ∧ lab.tag = CFSG.Assembly.LargeEvenLieTag.twE6) p Bs L) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (σ : K ≃+* K)
      (θ : ↥L ⧸ Subgroup.center ↥L ≃* ↥(twistedE6RootGroup K σ))
      (θr : ↥L ⧸ Subgroup.center ↥L ≃* TwE6Delta.RecipeR K 1),
      Nat.card K = 4 ∧ (∀ c, σ c = c ^ 2) ∧
        Bs ≤ Subgroup.normalizer (L : Set G) ∧
        (∀ b ∈ Bs, ∃ φ ∈ (RecipeExcLang.twConj K σ).range,
          LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) φ) ∧
        (∀ b ∈ Bs, ∃ φ ∈ TwE6Delta.RecipeI K 1,
          LargeEvenInduces θr (fun l l' => (l' : G) = b⁻¹ * l * b) φ) := by
  classical
  obtain ⟨hperf, lab, hlab, hraw⟩ := hE6
  obtain ⟨Rg, instRg, Ig, Fg, hQg⟩ := largeEvenRawDatum_exists hraw
  letI : Group Rg := instRg
  obtain ⟨-, -, θg, hP⟩ := hQg
  obtain ⟨⟨hQ2, htag⟩, hBsN, hact⟩ := hP
  have hlab_eq : lab = (⟨CFSG.Assembly.LargeEvenLieTag.twE6, 0, 1⟩ : LargeEvenLabel) := by
    obtain ⟨tag, rank, n⟩ := lab
    have htag' : tag = CFSG.Assembly.LargeEvenLieTag.twE6 := htag
    subst tag
    have hn1 : n = 1 := by
      have h1 : 1 ≤ n := hlab.1
      have h2 : n < 2 := hQ2
      omega
    subst n
    have hr0 : rank = 0 := by
      simpa using hlab.2
    subst rank
    rfl
  subst hlab_eq
  dsimp only [LargeEvenRawDatum, LargeEvenRecipeTwisted] at hraw
  obtain ⟨K, instF, instFin, hK, hQ⟩ := hraw
  letI : Field K := instF
  letI : Finite K := instFin
  obtain ⟨-, -, θr, hP'⟩ := hQ
  obtain ⟨⟨-, -⟩, hBsN', hact'⟩ := hP' 
  have hK4 : Nat.card K = 4 := by simpa using hK
  haveI : CharP K 2 := charP_two_of_card (m := 2) (by simpa using hK4)
  let σ : K ≃+* K := frobeniusEquiv K 2
  have hσ : ∀ c, σ c = c ^ 2 := by
    intro c
    rw [frobeniusEquiv_apply, frobenius_def]
  obtain ⟨ε, hε⟩ := TwE6DD2.exists_recipeEquiv (n := 1) (by norm_num) (K := K) hK σ hσ
  let θ : ↥L ⧸ Subgroup.center ↥L ≃* ↥(twistedE6RootGroup K σ) := θr.trans ε.symm
  refine ⟨K, instF, instFin, σ, θ, θr, hK4, hσ, hBsN', ?_, ?_⟩
  · intro b hb
    obtain ⟨φ, hφI, hφ⟩ := hact' b hb
    have hφI' : φ ∈ TwE6Delta.RecipeI K 1 := hφI
    refine ⟨MulAut.congr ε.symm φ, ?_, ?_⟩
    · have h := hε (MulAut.congr ε.symm φ)
      have hc : MulAut.congr ε (MulAut.congr ε.symm φ) = φ := by
        ext x
        simp only [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.symm_symm,
          MulEquiv.apply_symm_apply]
      rw [hc] at h
      exact h.1 hφI'
    · intro l l' hrel
      have hl : b⁻¹ * (l : G) * b ∈ L := hrel ▸ l'.2
      have hl' : l' = (⟨b⁻¹ * (l : G) * b, hl⟩ : ↥L) := Subtype.ext hrel
      subst hl'
      have hφl := hφ l (⟨b⁻¹ * (l : G) * b, hl⟩ : ↥L) rfl
      change (MulAut.congr ε.symm φ) (θ (QuotientGroup.mk l)) =
        θ (QuotientGroup.mk (⟨b⁻¹ * (l : G) * b, hl⟩ : ↥L))
      rw [show θ (QuotientGroup.mk l) = ε.symm (θr (QuotientGroup.mk l)) from rfl,
        show θ (QuotientGroup.mk (⟨b⁻¹ * (l : G) * b, hl⟩ : ↥L)) =
          ε.symm (θr (QuotientGroup.mk (⟨b⁻¹ * (l : G) * b, hl⟩ : ↥L))) from rfl]
      change ε.symm (φ (ε (ε.symm (θr (QuotientGroup.mk l))))) =
        ε.symm (θr (QuotientGroup.mk (⟨b⁻¹ * (l : G) * b, hl⟩ : ↥L)))
      rw [MulEquiv.apply_symm_apply]
      exact congrArg ε.symm hφl
  · intro b hb
    obtain ⟨φ, hφI, hφ⟩ := hact' b hb
    exact ⟨φ, hφI, fun l l' hrel => by
      have hl : b⁻¹ * (l : G) * b ∈ L := hrel ▸ l'.2
      have hl' : l' = (⟨b⁻¹ * (l : G) * b, hl⟩ : ↥L) := Subtype.ext hrel
      subst hl'
      exact hφ l (⟨b⁻¹ * (l : G) * b, hl⟩ : ↥L) rfl⟩

private theorem twE6_canonical_frame
    {K : Type} [Field K] [Finite K] (hK4 : Nat.card K = 4)
    (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ 2) :
    ∃ D : E6ThreeModel.FrameData ↥(twistedE6RootGroup K σ),
      D.Good ∧ D.H = (RecipeExcLang.twConj K σ).range ∧
        (∀ t ∈ D.Tor, t ^ 3 = 1) ∧
          ¬ 3 ^ 10 ∣ Nat.card ↥(twistedE6RootGroup K σ) := by
  classical
  have hK : Nat.card K = (2 ^ 1) ^ 2 := by simpa using hK4
  haveI : CharP K 2 := charP_two_of_card (m := 2) (by simpa using hK4)
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP (AlgebraicClosure K) 2 :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective 2
  haveI : IsAlgClosed (AlgebraicClosure K) := AlgebraicClosure.isAlgClosed K
  let Fr : AlgebraicClosure K →+* AlgebraicClosure K :=
    iterateFrobenius (AlgebraicClosure K) 2 1
  have hFr : ∀ c, Fr c = c ^ 2 ^ 1 := fun c => iterateFrobenius_def 2 1 c
  have h3 : 3 ∣ 2 ^ 1 + 1 := by norm_num
  have h30 : (3 : AlgebraicClosure K) ≠ 0 :=
    CFSG.HardMathSupport.Lang.E6Descent.three_ne_zero_of_dvd_card_add_one (ℓ := 2)
      (by norm_num) h3
  obtain ⟨ζ, hζ, hζo⟩ := CFSG.HardMathSupport.Lang.E6Descent.TwistedDiag.exists_cube_root
    (Ω := AlgebraicClosure K) h30
  obtain ⟨g, D, hL, hTSpec, hgood⟩ :=
    TwE6ThreeRootGen.exists_lang_frame (n := 1) (by norm_num) (K := K) hK σ hσ h3
      (Fr := Fr) hFr (ζ := ζ) hζ hζo
  have hTexp : ∀ t ∈ D.Tor, t ^ 3 = 1 := by
    obtain ⟨G⟩ := E6ThreeModel.tFrame_cartanGen (n := 1) (by norm_num) (K := K) hK σ hσ
      (Ω := AlgebraicClosure K) Fr hFr h3 hL hζ hζo hTSpec
    intro t ht
    have hmem : t ∈ ⨆ j, (G.d j).range := by
      rw [← G.tor_eq]
      exact ht
    have hC : ∀ x ∈ ⨆ j, (G.d j).range, x ∈ D.Tor ∧ x ^ 3 = 1 := by
      intro x hx
      refine Subgroup.iSup_induction (C := fun z => z ∈ D.Tor ∧ z ^ 3 = 1)
        (fun j => (G.d j).range) hx ?_ ?_ ?_
      · intro j y hy
        obtain ⟨s, hs⟩ := hy
        rw [← hs]
        refine ⟨?_, ?_⟩
        · rw [G.tor_eq]
          exact Subgroup.mem_iSup_of_mem j (MonoidHom.mem_range.mpr ⟨s, rfl⟩)
        · rw [← map_pow]
          have hs : (s : (AlgebraicClosure K)ˣ) ^ (2 ^ 1 + 1) = 1 :=
            (mem_rootsOfUnity (2 ^ 1 + 1) (s : (AlgebraicClosure K)ˣ)).1 s.2
          have hs3 : (s : rootsOfUnity (2 ^ 1 + 1) (AlgebraicClosure K)) ^ 3 = 1 := by
            apply Subtype.ext
            simpa using hs
          rw [hs3, map_one]
      · exact ⟨D.Tor.one_mem, by norm_num⟩
      · intro x y hx hy
        refine ⟨D.Tor.mul_mem hx.1 hy.1, ?_⟩
        have hcomm : Commute x y := hgood.torus.1 x hx.1 y hy.1
        rw [hcomm.mul_pow, hx.2, hy.2, one_mul]
    exact (hC t hmem).2
  have h3R : ¬ 3 ^ 10 ∣ Nat.card ↥(twistedE6RootGroup K σ) := by
    intro h10
    obtain ⟨ε, -⟩ := TwE6DD2.exists_recipeEquiv (n := 1) (by norm_num) (K := K) hK σ hσ
    obtain ⟨D₀, X, hD₀good, hHI, hDHcard, hD3card, hrest⟩ :=
      exists_langFrame_recipeR (K := K) 1 (by norm_num) hK h3
    have hcard : Nat.card (TwE6Delta.RecipeR K 1) =
        Nat.card ↥(twistedE6RootGroup K σ) := (Nat.card_congr ε.toEquiv).symm
    have hnum : CFSG.SeitzReduction.E6Pilot.numTwistedE6 (2 ^ 1) =
        3 * Nat.card ↥(twistedE6RootGroup K σ) := by
      rw [← hDHcard, hD3card, hcard]
    have h11 : (2 ^ 1 + 1) ^ 6 * 3 ^ 5 ∣
        CFSG.SeitzReduction.E6Pilot.numTwistedE6 (2 ^ 1) := by
      rw [hnum]
      have h11' : (2 ^ 1 + 1) ^ 6 * 3 ^ 5 = 3 * 3 ^ 10 := by norm_num
      rw [h11']
      exact Nat.mul_dvd_mul_left 3 h10
    exact E6ThreeModel.not_dvd_numTwistedE6 (q := 2 ^ 1) (by norm_num) (by norm_num) h11
  exact ⟨D, hgood, hTSpec.H_eq, hTexp, h3R⟩


private theorem twE6_transfer_frame_data
    {K : Type} [Field K] [Finite K] (hK4 : Nat.card K = 4)
    (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ 2)
    {L' : Type} [Group L'] [Finite L']
    {ψ : L' →* ↥(twistedE6RootGroup K σ)} (hψ : Function.Surjective ψ)
    (hker : ψ.ker ≤ Subgroup.center L') (hperf : commutator L' = ⊤)
    (hcard : Nat.card ψ.ker = 3)
    {A : Subgroup (MulAut L')} (hA : CFSG.Open.IsElemAbelian 3 A)
    (hsc : GGTorusSelfCent 3 A) (h5 : 3 ^ 5 ≤ Nat.card A)
    (hAH : ∀ a ∈ A, ∃ φ ∈ (RecipeExcLang.twConj K σ).range,
      ∀ l : L', φ (ψ l) = ψ (a l)) :
    ∃ (T N : Subgroup L') (hn : (T.subgroupOf N).Normal), T ≤ N ∧ ψ.ker ≤ T ∧
      (∀ s ∈ T, ∀ t ∈ T, s * t = t * s) ∧ (∀ t ∈ T, t ^ 3 = 1) ∧
      (∀ a ∈ A, ∀ t ∈ T, a t = t) ∧ (∀ n ∈ N, ∀ a ∈ A, n * (a n)⁻¹ ∈ T) ∧
      (haveI := hn; Nonempty (CoxeterSystem CoxeterMatrix.E₆ (N ⧸ T.subgroupOf N))) ∧
      ¬ 3 ∣ N.index := by
  obtain ⟨D, hgood, hH, hTexp, h3R⟩ := twE6_canonical_frame hK4 σ hσ
  obtain ⟨γ, ψ', ρ', -, hψ', hkerEq, hker', hρinj, hρ', hal, -⟩ :=
    TwE6ThreeRootGen.align_data (K := K) σ hψ hker hperf hA hAH h5
      D hH hgood
  have hcard' : Nat.card ψ'.ker = 3 := by rw [hkerEq]; exact hcard
  simpa only [hkerEq] using
    (CFSG.StandardType.GGXInL.e6_transfer_frame D ggAbelianLift hgood hTexp h3R hperf hψ' hker'
      hcard' hρ' hρinj hA hsc hal)


private theorem twE6_two_kernel_data
    {L R : Type} [Group L] [Finite L] [Group R] {ψ : L →* R}
    (hψ : Function.Surjective ψ) (hker : ψ.ker ≤ Subgroup.center L)
    (hperf : commutator L = ⊤) :
    let N₂ : Subgroup L := U63TB.twoSub ψ.ker hker
    N₂.Normal ∧ N₂ ≤ Subgroup.center L ∧ IsPGroup 2 N₂ ∧
      Nat.Coprime 3 (Nat.card N₂) ∧ commutator (L ⧸ N₂) = ⊤ ∧
      Function.Surjective (U63TB.psi1 hker) ∧
      (U63TB.psi1 hker).ker ≤ Subgroup.center (L ⧸ N₂) ∧
      Odd (Nat.card (U63TB.psi1 hker).ker) := by
  classical
  dsimp only
  haveI : (U63TB.twoSub ψ.ker hker).Normal := U63TB.twoSub_normal hker
  refine ⟨inferInstance, U63TB.twoSub_le_center hker, U63TB.isPGroup_twoSub hker, ?_,
    U63TB.commutator_quot hker hperf, U63TB.psi1_surjective hker hψ,
    U63TB.psi1_ker_central hker, U63TB.odd_card_ker_psi1 hker⟩
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card (p := 2) (G := ↥(U63TB.twoSub ψ.ker hker))).mp
    (U63TB.isPGroup_twoSub hker)
  rw [hk]
  exact Nat.Coprime.pow_right k (by norm_num : Nat.Coprime 3 2)

private theorem twE6_cover_kernel_card
    {K : Type} [Field K] [Finite K] {n : ℕ} (hn : 1 ≤ n)
    (hK : Nat.card K = (2 ^ n) ^ 2)
    {L' : Type} [Group L'] [Finite L']
    {ψ : L' →* TwE6Delta.RecipeR K n} (hψ : Function.Surjective ψ)
    (hker : ψ.ker ≤ Subgroup.center L') (hperf : commutator L' = ⊤)
    (hodd : Odd (Nat.card ψ.ker)) (hne : ψ.ker ≠ ⊥) :
    Nat.card ψ.ker = 3 := by
  have hd : Nat.card ψ.ker ∣ 3 :=
    TwE6R4.card_ker_dvd_three hn hK hψ hker hperf hodd
  have hne1 : Nat.card ψ.ker ≠ 1 := by
    intro h1
    exact hne (Subgroup.eq_bot_of_card_eq (H := ψ.ker) h1)
  rcases (Nat.dvd_prime Nat.prime_three).mp hd with h | h
  · exact absurd h hne1
  · exact h


private theorem twE6_redSub_data
    {L R : Type} [Group L] [Finite L] [Group R] {ψ : L →* R}
    (hker : ψ.ker ≤ Subgroup.center L) {S : Subgroup (MulAut L)}
    (hS : S ≤ U63TB.presZ (U63TB.twoSub ψ.ker hker))
    (hperf : commutator L = ⊤) (hA : CFSG.Open.IsElemAbelian 3 S)
    (hsc : GGTorusSelfCent 3 S) (hr : 3 ^ 5 ≤ Nat.card S) :
    CFSG.Open.IsElemAbelian 3 (U63TB.redSub hker hS).range ∧
      GGTorusSelfCent 3 (U63TB.redSub hker hS).range ∧
      3 ^ 5 ≤ Nat.card (U63TB.redSub hker hS).range := by
  refine ⟨U63TB.isElemAbelian_range_redSub hker hS hA, U63TB.selfCent_quot hker hA hS hsc, ?_⟩
  rw [U63TB.card_range_redSub hker hS hperf]
  exact hr


private theorem twE6_cover_kernel_card'
    {K : Type} [Field K] [Finite K] (hK4 : Nat.card K = 4)
    (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ 2)
    {L' : Type} [Group L'] [Finite L']
    {ψ : L' →* ↥(twistedE6RootGroup K σ)} (hψ : Function.Surjective ψ)
    (hker : ψ.ker ≤ Subgroup.center L') (hperf : commutator L' = ⊤)
    (hodd : Odd (Nat.card ψ.ker)) (hne : ψ.ker ≠ ⊥) :
    Nat.card ψ.ker = 3 := by
  have hK : Nat.card K = (2 ^ 1) ^ 2 := by simpa using hK4
  obtain ⟨ε, -⟩ := TwE6DD2.exists_recipeEquiv (n := 1) (by norm_num) (K := K) hK σ hσ
  let ψ' : L' →* TwE6Delta.RecipeR K 1 := (ε : _ ≃* _).toMonoidHom.comp ψ
  have hkerEq : ψ'.ker = ψ.ker := by
    ext l
    simp only [ψ', MonoidHom.mem_ker, MonoidHom.coe_comp, Function.comp_apply,
      MulEquiv.coe_toMonoidHom]
    exact map_eq_one_iff ε ε.injective
  have h := twE6_cover_kernel_card (n := 1) (by norm_num) hK (ψ := ψ') (ε.surjective.comp hψ)
    (by rw [hkerEq]; exact hker) hperf (by rw [hkerEq]; exact hodd) (by rw [hkerEq]; exact hne)
  rwa [hkerEq] at h

private theorem twE6_twisted_arm
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G}
    (hS : GGQTwoSetting p B Bs x L D J) (hxL : x ∈ L) (hp : p = 3)
    (hE6 : GGInnerDiagOnLabel
      (fun p lab => GGLabQTwo p lab ∧ lab.tag = CFSG.Assembly.LargeEvenLieTag.twE6) p Bs L) :
    x ∈ ⁅Bs, L ⊓ Subgroup.normalizer (Bs : Set G)⁆ := by
  classical
  subst hp
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcfg : GGConfig 3 B Bs x L D J := hS.1.1
  obtain ⟨-, hBsAb, hxBs, hLx, -⟩ := hcfg.tableB_facts
  have hSStar : LargeEvenSStar 3 B x L := hcfg.1.2.2.2.2.2.2.1
  have hx3 : x ^ 3 = 1 := hSStar.1.1.2 x hSStar.2.1
  have hx1 : x ≠ 1 := hSStar.2.2.1
  have hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ 3 = 1 → g ∈ Bs := hcfg.2.1.2.2.2
  have hperf : commutator ↥L = ⊤ := GGXInL.lup8f_L_perfect hS
  obtain ⟨K, instF, instFin, σ, θ, θr, hK4, hσ, hBsN, hact, hactr⟩ :=
    twE6_literal_data hS hxL rfl hE6
  letI := instF
  letI := instFin
  have hK : Nat.card K = (2 ^ 1) ^ 2 := by simpa using hK4
  haveI : CharP K 2 := charP_two_of_card (m := 2) (by simpa using hK4)
  have hψs : Function.Surjective (ggQuotHom θ) := ggQuotHom_surjective θ
  have hkerψ : (ggQuotHom θ).ker = Subgroup.center ↥L := ker_ggQuotHom θ
  have hker : (ggQuotHom θ).ker ≤ Subgroup.center ↥L := hkerψ.le
  obtain ⟨hN₂n, hN₂c, hN₂p, hN₂cop, hperf₁, hψ₁s, hker₁, hodd₁⟩ :=
    twE6_two_kernel_data hψs hker hperf
  have hxZ : (⟨x, hxL⟩ : ↥L) ∈ Subgroup.center ↥L := by
    rw [Subgroup.mem_center_iff]
    intro l
    exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp (hLx l.2))
  have hxx3 : (⟨x, hxL⟩ : ↥L) ^ 3 = 1 := Subtype.ext (by simpa using hx3)
  have hxx1 : (⟨x, hxL⟩ : ↥L) ≠ 1 := fun h => hx1 (congrArg Subtype.val h)
  have hz₁k : (QuotientGroup.mk (⟨x, hxL⟩ : ↥L) : ↥L ⧸ U63TB.twoSub (ggQuotHom θ).ker hker) ∈
      (U63TB.psi1 hker).ker :=
    (U63TB.mem_ker_psi1 hker).mpr (by rw [hkerψ]; exact hxZ)
  have hz₁ne : (QuotientGroup.mk (⟨x, hxL⟩ : ↥L) :
      ↥L ⧸ U63TB.twoSub (ggQuotHom θ).ker hker) ≠ 1 := by
    intro h
    have hmem : (⟨x, hxL⟩ : ↥L) ∈ U63TB.twoSub (ggQuotHom θ).ker hker :=
      (QuotientGroup.eq_one_iff _).mp h
    have h2 : (⟨x, hxL⟩ : ↥L) ^ (2 ^ Nat.card ↥L) = 1 := hmem.2
    have hord : orderOf (⟨x, hxL⟩ : ↥L) = 3 := orderOf_eq_prime hxx3 hxx1
    have h3 : 3 ∣ 2 ^ Nat.card ↥L := hord ▸ orderOf_dvd_of_pow_eq_one h2
    have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3
    omega
  have hz₁o : orderOf (QuotientGroup.mk (⟨x, hxL⟩ : ↥L) :
      ↥L ⧸ U63TB.twoSub (ggQuotHom θ).ker hker) = 3 := by
    refine orderOf_eq_prime ?_ hz₁ne
    rw [← QuotientGroup.mk_pow, hxx3]
    exact QuotientGroup.mk_one _
  have hne : (U63TB.psi1 hker).ker ≠ ⊥ := fun h => hz₁ne (by
    have := hz₁k
    rw [h] at this
    exact Subgroup.mem_bot.mp this)
  have hcard₁ : Nat.card (U63TB.psi1 hker).ker = 3 :=
    twE6_cover_kernel_card' hK4 σ hσ hψ₁s hker₁ hperf₁ hodd₁ hne
  obtain ⟨hA₀ab, hA₀I, hA₀sc⟩ := ggGamma_range_hypsKG hcfg θ hBsN hact
  have h5 : 3 ^ 5 ≤ Nat.card (ggGamma L hBsN).range :=
    q1TwE6Three_rank_of_recipe (n := 1) le_rfl hK (by norm_num) hcfg θr hBsN hactr
  have hA₀le : (ggGamma L hBsN).range ≤ U63TB.presZ (U63TB.twoSub (ggQuotHom θ).ker hker) :=
    fun a ha => U63TB.mem_presZ_of_ker hker (fun z hz => U63TB.preserves_ker (hA₀I a ha) hz)
  obtain ⟨hA₁ab, hA₁sc, h5₁⟩ := twE6_redSub_data hker hA₀le hperf hA₀ab hA₀sc h5
  have hAH₁ := U63TB.redSub_hAI hker hA₀le hA₀I
  obtain ⟨T₁, N₁, hn₁, hTN₁, hkerT₁, -, hTexp₁, hfix₁, hN₁, hcox₁, hidx₁⟩ :=
    twE6_transfer_frame_data hK4 σ hσ hψ₁s hker₁ hperf₁ hcard₁ hA₁ab hA₁sc h5₁ hAH₁
  let C := GGXInL.lup8f_central_cover_of_normalizes hBsN
  haveI hCN : C.N.Normal := C.normal
  let ι₀ : ↥L →* (↥(L ⊔ Bs) ⧸ C.N) :=
    (QuotientGroup.mk' C.N).comp (Subgroup.inclusion (le_sup_left : L ≤ L ⊔ Bs))
  have hN₂ker : U63TB.twoSub (ggQuotHom θ).ker hker ≤ ι₀.ker := by
    intro z hz
    rw [MonoidHom.mem_ker]
    show ((Subgroup.inclusion (le_sup_left : L ≤ L ⊔ Bs) z : ↥(L ⊔ Bs)) : ↥(L ⊔ Bs) ⧸ C.N) = 1
    refine (QuotientGroup.eq_one_iff _).mpr ?_
    have hzc : z ∈ Subgroup.center ↥L := U63TB.twoSub_le_center hker hz
    have hpow : (Subgroup.inclusion (le_sup_left : L ≤ L ⊔ Bs) z) ^ (2 ^ Nat.card ↥L) = 1 := by
      rw [← map_pow, hz.2, map_one]
    refine C.contains_two _ (Subgroup.mem_subgroupOf.mpr z.2) ?_ ?_
    · intro l hl
      have hlL : (l : G) ∈ L := Subgroup.mem_subgroupOf.mp hl
      have h := Subgroup.mem_center_iff.mp hzc ⟨(l : G), hlL⟩
      have h' := congrArg (Subgroup.inclusion (le_sup_left : L ≤ L ⊔ Bs)) h
      rw [map_mul, map_mul] at h'
      exact h'
    · obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hpow)
      exact IsPGroup.of_card (n := k) (by rw [Nat.card_zpowers]; exact hk)
  let ι : (↥L ⧸ U63TB.twoSub (ggQuotHom θ).ker hker) →* (↥(L ⊔ Bs) ⧸ C.N) :=
    QuotientGroup.lift _ ι₀ hN₂ker
  have hι : Function.Injective ι := by
    rw [injective_iff_map_eq_one]
    intro a ha
    obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective a
    have hl : ι₀ l = 1 := ha
    have hmemN : Subgroup.inclusion (le_sup_left : L ≤ L ⊔ Bs) l ∈ C.N :=
      (QuotientGroup.eq_one_iff _).mp hl
    rw [QuotientGroup.eq_one_iff]
    refine ⟨?_, ?_⟩
    · rw [hkerψ, Subgroup.mem_center_iff]
      intro l'
      have h := C.central _ hmemN (Subgroup.inclusion (le_sup_left : L ≤ L ⊔ Bs) l')
        (Subgroup.mem_subgroupOf.mpr l'.2)
      exact Subgroup.inclusion_injective (le_sup_left : L ≤ L ⊔ Bs)
        (by rw [map_mul, map_mul]; exact h)
    · obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.mp C.two_group ⟨_, hmemN⟩
      have hk' : orderOf l = 2 ^ k := by
        rw [← orderOf_injective (Subgroup.inclusion (le_sup_left : L ≤ L ⊔ Bs))
          (Subgroup.inclusion_injective _) l, ← Subgroup.orderOf_mk _ hmemN]
        exact hk
      have hdvd : 2 ^ k ∣ Nat.card ↥L := hk' ▸ orderOf_dvd_natCard l
      have hle : 2 ^ k ≤ Nat.card ↥L := Nat.le_of_dvd Nat.card_pos hdvd
      have hk2 : k ≤ Nat.card ↥L := (Nat.lt_two_pow_self.le).trans hle
      exact orderOf_dvd_iff_pow_eq_one.mp (hk' ▸ pow_dvd_pow 2 hk2)
  have hrange : ι.range = (L.subgroupOf (L ⊔ Bs)).map (QuotientGroup.mk' C.N) := by
    ext q
    constructor
    · rintro ⟨a, rfl⟩
      obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective a
      exact ⟨Subgroup.inclusion (le_sup_left : L ≤ L ⊔ Bs) l, Subgroup.mem_subgroupOf.mpr l.2, rfl⟩
    · rintro ⟨h, hh, rfl⟩
      exact ⟨QuotientGroup.mk ⟨(h : G), Subgroup.mem_subgroupOf.mp hh⟩, rfl⟩
  let E0 : Subgroup (↥(L ⊔ Bs) ⧸ C.N) := (Bs.subgroupOf (L ⊔ Bs)).map (QuotientGroup.mk' C.N)
  have hind : ∀ e ∈ E0, ∃ a ∈ (U63TB.redSub hker hA₀le).range,
      ∀ l₁, ι (a l₁) = e * ι l₁ * e⁻¹ := by
    rintro e ⟨h, hh, rfl⟩
    have hhB : (h : G) ∈ Bs := Subgroup.mem_subgroupOf.mp hh
    refine ⟨U63TB.redSub hker hA₀le ⟨ggGamma L hBsN ⟨(h : G), hhB⟩, ⟨_, rfl⟩⟩, ⟨_, rfl⟩, ?_⟩
    intro l₁
    obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective l₁
    rw [U63TB.redSub_mk]
    show QuotientGroup.mk' C.N (Subgroup.inclusion (le_sup_left : L ≤ L ⊔ Bs)
        (ggGamma L hBsN ⟨(h : G), hhB⟩ l)) =
      QuotientGroup.mk' C.N h * QuotientGroup.mk' C.N
        (Subgroup.inclusion (le_sup_left : L ≤ L ⊔ Bs) l) * (QuotientGroup.mk' C.N h)⁻¹
    rw [← map_inv, ← map_mul, ← map_mul]
    congr 1
  have hsc0 : ∀ g : ↥(L ⊔ Bs) ⧸ C.N, (∀ e ∈ E0, g * e = e * g) → g ^ 3 = 1 → g ∈ E0 := by
    intro g hcomm hg3
    refine GGXInLE6Frame.mem_image_of_commute C.N (Bs.subgroupOf (L ⊔ Bs)) C.two_group ?_ ?_ ?_
      hg3 hcomm
    · intro e he
      exact Subtype.ext (by simpa using hBsAb.2 _ (Subgroup.mem_subgroupOf.mp he))
    · intro a ha b hb
      exact Subtype.ext (CFSG.Open.IsElemAbelian.comm hBsAb (Subgroup.mem_subgroupOf.mp ha)
        (Subgroup.mem_subgroupOf.mp hb))
    · intro g hcomm hg3
      refine Subgroup.mem_subgroupOf.mpr (hSC (g : G) ?_ ?_)
      · rw [Subgroup.mem_centralizer_iff]
        intro b hb
        have := hcomm ⟨b, Subgroup.mem_sup_right hb⟩ (Subgroup.mem_subgroupOf.mpr hb)
        exact (congrArg Subtype.val this).symm
      · simpa using congrArg Subtype.val hg3
  have hF := GGXInLE6Frame.quotFrame_of_transfer ι hι (E0 := E0) hsc0
    (A := (U63TB.redSub hker hA₀le).range) hind hn₁ hTN₁ hTexp₁ hfix₁ hN₁ hcox₁ hidx₁ hperf₁
    (hkerT₁ hz₁k) (hker₁ hz₁k) hz₁o
  exact GGXInLE6Assembly.twE6_transport_quotient hS hxL rfl C.N C.le_L C.coprime rfl hrange hF rfl

theorem ggQ2XInLCommTwE6_holds
    : GGQ2XInLCommTwE6 := by
  intro G _ _ p B Bs x L D J hS hxL hE6
  obtain ⟨hp, hUnit | hTw⟩ := GGXInL.lup8g_dispatch_label hS hxL
  · obtain ⟨⟨n, K, _, _, ⟨M⟩, hdvd, hn⟩, _⟩ := hUnit
    exact GGXInL.lup8f_mem_commutator_unitary hS hxL M hp hdvd hn
  · exact twE6_twisted_arm hS hxL hp hTw

end CFSG.StandardType

end
