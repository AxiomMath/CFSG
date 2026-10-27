module

public import CFSG.LocalAnalysis.WeakClosure81.InFGroupSwapSp4Setting
public import CFSG.LocalAnalysis.WeakClosure81.InFGroupSwapSp4ModelPar
public import CFSG.LocalAnalysis.WeakClosure81.InFGroupSwapSp4ModelW
public import CFSG.LocalAnalysis.WeakClosure81.InFGroupSwapSp4ModelOut
public import CFSG.LocalAnalysis.WeakClosure81.InFGroupSwapSp4ModelSz
public import CFSG.Quasithin.EmptyFaithful.T1521SSp4Coord
import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch5ASIn
import CFSG.LocalAnalysis.UniquenessCase.UC22P22a
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.J3InvolveCore
public import CFSG.LocalAnalysis.QuasithinUnique.K1.EvenClassicalSymplecticAut

public section

namespace CFSG.LocalAnalysis.WeakClosure81.SwapSp4

open Subgroup CFSG.Open CFSG.Quasithin
open CFSG.LocalAnalysis.UniquenessCase.UC22 (Fstar IsSp4)
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17 (SwapsParabolics)
open CFSG.Quasithin.H13.Ch4 CFSG.Quasithin.H13.Ch4.L436
open CFSG.QuasithinUnique
open CFSG.QuasithinUnique.Setup.X7a (Q2)
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag (unipotent projUnipotent proj)
open CFSG.LocalAnalysis.ComponentInitial.SymplecticCoverFour (tauS)

variable {Q : Type} [Group Q] [Finite Q] {L T : Subgroup Q} {n : ℕ}

private lemma normal_of_fstar_eq (hF : Fstar (⊤ : Subgroup Q) = L) : L.Normal := by
  have hgf : CFSG.generalizedFitting Q = L := by
    rw [← CFSG.LocalAnalysis.WeakClosure81.fstar_top_eq_generalizedFitting Q]
    exact hF
  rw [← hgf]
  exact (CFSG.LocalCores.generalized_fitting_characteristic (G := Q)).2

private lemma centralizer_eq_bot_of_fstar_eq (hF : Fstar (⊤ : Subgroup Q) = L)
    (hsimple : IsSimpleGroup ↥L) (hnab : ∃ a b : ↥L, a * b ≠ b * a) :
    centralizer (L : Set Q) = ⊥ := by
  have hgf : CFSG.generalizedFitting Q = L := by
    rw [← CFSG.LocalAnalysis.WeakClosure81.fstar_top_eq_generalizedFitting Q]
    exact hF
  have hle : centralizer (L : Set Q) ≤ L := by
    rw [← hgf]
    exact CFSG.centralizer_generalizedFitting_le Q
  have hZ : Subgroup.center ↥L = ⊥ :=
    CFSG.AGLEmbedding.center_eq_bot_of_isSimpleGroup_nonabelian hnab
  rw [eq_bot_iff]
  intro x hx
  have hxL : x ∈ L := hle hx
  have hxZ : (⟨x, hxL⟩ : ↥L) ∈ Subgroup.center ↥L := by
    rw [Subgroup.mem_center_iff]
    intro y
    exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hx (y : Q) y.2)
  rw [hZ, Subgroup.mem_bot] at hxZ
  exact Subtype.ext_iff.mp hxZ

private lemma sylowTwoOf_inf_of_isSylowIn (hT : IsSylowIn 2 T ⊤) (hL : L.Normal) :
    IsSylowTwoOf (T ⊓ L) L :=
  CFSG.Quasithin.A4.isSylowTwoOf_inf_normal (CFSG.Quasithin.E1.isSylowIn_two_iff.mp hT) le_top
    (by rw [Subgroup.normalizer_eq_top_iff.mpr hL])

private lemma range_comp {K : Type} [Field K]
    (φ : ↥L ≃* StatedProj (StatedSp 2 K))
    (ψ : StatedSp 2 K ≃* StatedProj (StatedSp 2 K)) :
    (L.subtype.comp (ψ.trans φ.symm).toMonoidHom).range = L := by
  ext x
  constructor
  · rintro ⟨s, rfl⟩
    exact (φ.symm (ψ s)).2
  · intro hx
    exact ⟨ψ.symm (φ ⟨x, hx⟩), by simp⟩

private lemma vW_eq_tauS {K : Type} [Field K]
    (φ : ↥L ≃* StatedProj (StatedSp 2 K))
    (ψ : StatedSp 2 K ≃* StatedProj (StatedSp 2 K))
    (hψ : ∀ s, ψ s = proj 2 K s)
    (ι : StatedSp 2 K →* Q) (hιeq : ∀ s, ι s = ((φ.symm (ψ s) : ↥L) : Q)) (x : K × K) :
    Sp4.vW φ x = ι (tauS x.1 x.2 0) := by
  rw [Sp4.vW_apply, hιeq, hψ]
  rfl

private lemma map_unipotent_eq {K : Type} [Field K] [CharP K 2]
    (φ : ↥L ≃* StatedProj (StatedSp 2 K))
    (hφ : ∀ x : ↥L, (x : Q) ∈ T ⊓ L ↔ φ x ∈ projUnipotent 2 K)
    (ψ : StatedSp 2 K ≃* StatedProj (StatedSp 2 K))
    (hψ : ∀ s, ψ s = proj 2 K s)
    (ι : StatedSp 2 K →* Q) (hιeq : ∀ s, ι s = ((φ.symm (ψ s) : ↥L) : Q)) :
    (unipotent 2 K).map ι = T ⊓ L := by
  ext x
  constructor
  · rintro ⟨u, hu, rfl⟩
    have hψu : ψ u ∈ projUnipotent 2 K := by
      rw [hψ]
      exact Subgroup.mem_map_of_mem (proj 2 K) hu
    have hR : ((φ.symm (ψ u) : ↥L) : Q) ∈ T ⊓ L :=
      (hφ _).mpr (by simpa using hψu)
    simpa [hιeq] using hR
  · rintro ⟨hxT, hxL⟩
    have hmem : φ ⟨x, hxL⟩ ∈ projUnipotent 2 K := (hφ ⟨x, hxL⟩).mp ⟨hxT, hxL⟩
    rw [projUnipotent, Subgroup.mem_map] at hmem
    obtain ⟨u, hu, huy⟩ := hmem
    refine ⟨u, hu, ?_⟩
    rw [hιeq, hψ, huy]
    simp

private lemma sp4C_map_Q2 {K : Type} [Field K] [Finite K]
    (ι : StatedSp 2 K →* Q) (hι : Function.Injective ι) (j : Fin 2) :
    (sp4C (Q2 K j) (pCoreOf 2 (perfectCore (Q2 K j)))).map ι =
      sp4C ((Q2 K j).map ι) (pCoreOf 2 (perfectCore ((Q2 K j).map ι))) := by
  rw [L436.map_sp4C ι hι, ← CFSG.Quasithin.Lie2Parabolic.pCoreOf_map_of_injective ι hι,
    map_perfectCore ι (Q2 K j)]

private lemma action_coordinates {K : Type} [Field K] [CharP K 2] [Finite K]
    (φ : ↥L ≃* StatedProj (StatedSp 2 K))
    (hφ : ∀ x : ↥L, (x : Q) ∈ T ⊓ L ↔ φ x ∈ projUnipotent 2 K)
    (hcard : Nat.card K = 2 ^ n) (hn : 1 ≤ n)
    (hC : centralizer (L : Set Q) = ⊥) (hL : L.Normal) {x : Q} (hxT : x ∈ T) :
    ∃ (l₁ l₂ : K) (σ : K ≃+* K) (ε : Bool), l₁ ≠ 0 ∧ l₂ ≠ 0 ∧
      (∀ v : K × K, x * Sp4.vW φ v * x⁻¹ = Sp4.vW φ (Sp4.vAct l₁ l₂ σ ε v)) ∧
      ((∀ v : K × K, Sp4.vAct l₁ l₂ σ ε v = v) → x ∈ L) := by
  have hxN : x ∈ Subgroup.normalizer (L : Set Q) := by
    rw [Subgroup.normalizer_eq_top_iff.mpr hL]
    exact Subgroup.mem_top x
  have hxR : ∀ y ∈ L, (y ∈ T ⊓ L ↔ x * y * x⁻¹ ∈ T ⊓ L) := by
    intro y hy
    constructor
    · rintro ⟨hyT, hyL⟩
      exact ⟨T.mul_mem (T.mul_mem hxT hyT) (T.inv_mem hxT), hL.conj_mem y hyL x⟩
    · rintro ⟨hyT, hyL⟩
      have hxy : x⁻¹ * (x * y * x⁻¹) * x = y := by group
      refine ⟨?_, ?_⟩
      · rw [← hxy]
        exact T.mul_mem (T.mul_mem (T.inv_mem hxT) hyT) hxT
      · rw [← hxy]
        simpa using hL.conj_mem (x * y * x⁻¹) hyL x⁻¹
  obtain ⟨l₁, l₂, σ, ε, h1, h2, hact, hinner⟩ :=
    Sp4.exists_vAct_conj (φ := φ) hn hcard hφ hxN hxR
  refine ⟨l₁, l₂, σ, ε, h1, h2, hact, fun hv => ?_⟩
  obtain ⟨l, hlR, hlc⟩ := hinner hv
  have hl1 : (l : Q)⁻¹ * x = 1 := by
    have := hlc
    rw [hC, Subgroup.mem_bot] at this
    exact this
  have hx_eq : x = (l : Q) := by
    calc x = (l : Q) * ((l : Q)⁻¹ * x) := by group
      _ = (l : Q) * 1 := by rw [hl1]
      _ = (l : Q) := mul_one _
  rw [hx_eq]
  exact hlR.2

private lemma setting_of_model {K : Type} [Field K] [Finite K]
    [CharP K 2]
    (φ : ↥L ≃* StatedProj (StatedSp 2 K))
    (hφ : ∀ x : ↥L, (x : Q) ∈ T ⊓ L ↔ φ x ∈ projUnipotent 2 K)
    (hcard : Nat.card K = 2 ^ n) (hL : L.Normal) (hsimple : IsSimpleGroup ↥L)
    (hnab : ∃ a b : ↥L, a * b ≠ b * a) (hC : centralizer (L : Set Q) = ⊥)
    (hSp : IsSp4 ↥L n) (hn : 2 ≤ n) (hT : IsSylowIn 2 T ⊤) (hLT : L ⊔ T = ⊤)
    (hsw : SwapsParabolics T L)
    (ι : StatedSp 2 K →* Q) (hι : Function.Injective ι) (hrange : ι.range = L)
    (hmapU : (unipotent 2 K).map ι = T ⊓ L)
    (P₀ P₁ : Subgroup Q) (hP₀ : P₀ = (Q2 K 0).map ι) (hP₁ : P₁ = (Q2 K 1).map ι)
    (w : K × K → Q) (hw : w = Sp4.vW φ)
    (hw_tau : ∀ x : K × K, w x = ι (tauS x.1 x.2 0))
    (hC₀ : (sp4C (Q2 K 0) (pCoreOf 2 (perfectCore (Q2 K 0)))).map ι =
      sp4C P₀ (pCoreOf 2 (perfectCore P₀)))
    (hC₁ : (sp4C (Q2 K 1) (pCoreOf 2 (perfectCore (Q2 K 1)))).map ι =
      sp4C P₁ (pCoreOf 2 (perfectCore P₁))) :
    Setting L T P₀ P₁ n w := by
  subst hP₀ hP₁
  refine
    { normal := hL, simple := hsimple, nonabelian := hnab, centralizer_eq := hC
      two_le := hn, sylow := hT, sup_eq := hLT
      par₀ := by simpa [hrange, hmapU] using Model.isMaxParabolicOver_map_Q2 hι 0
      par₁ := by simpa [hrange, hmapU] using Model.isMaxParabolicOver_map_Q2 hι 1
      par_ne := Model.map_Q2_zero_ne_one hι
      le_or_le := by
        intro Y hUY hY
        exact Model.le_or_le_map_Q2 hι (by simpa [hmapU] using hUY) (by simpa [hrange] using hY)
      inf_le := by simpa [hmapU] using Model.map_Q2_inf_le hι
      swaps := hsw
      concl₀ := by simpa [hrange, hmapU] using Model.sp4ParConcl_map_Q2 hn hcard hι 0
      concl₁ := by simpa [hrange, hmapU] using Model.sp4ParConcl_map_Q2 hn hcard hι 1
      k₂₀ := by simpa [hrange, hmapU] using Model.sp4K₂_map_Q2_zero hn hcard hι
      k₂₁ := by simpa [hrange, hmapU] using Model.sp4K₂_map_Q2_one hn hcard hι
      card_F := hcard
      w_injective := by rw [hw]; exact Sp4.vW_injective φ
      w_add := by intro x y; rw [hw]; exact (Sp4.vW_mul φ x y).symm
      w_fst := by
        intro b
        have hb : ι (tauS b 0 0) ∈ sp4C ((Q2 K 0).map ι)
            (pCoreOf 2 (perfectCore ((Q2 K 0).map ι))) :=
          hC₀ ▸ Subgroup.mem_map_of_mem ι (Model.tauS_fst_mem_sp4C hn hcard b)
        simpa [hw_tau (b, 0)] using hb
      w_snd := by
        intro c
        have hb : ι (tauS 0 c 0) ∈ sp4C ((Q2 K 1).map ι)
            (pCoreOf 2 (perfectCore ((Q2 K 1).map ι))) :=
          hC₁ ▸ Subgroup.mem_map_of_mem ι (Model.tauS_snd_mem_sp4C hn hcard c)
        simpa [hw_tau (0, c)] using hb
      act := by
        intro x hxT
        rw [hw]
        exact action_coordinates φ hφ hcard (by omega) hC hL hxT
      out := fun A _ hA => Model.card_le_two_mul_card_inf hn hL hSp hC hA
      index_odd := fun hodd => Model.index_le_two hn hL hSp hC hodd hT hLT
      suzuki := fun hodd a _ haL ha => Model.suzuki_of_odd hn hL hSp hC hodd haL ha }

theorem exists_setting (hF : Fstar (⊤ : Subgroup Q) = L)
    (hsimple : IsSimpleGroup ↥L) (hSp : IsSp4 ↥L n) (hn : 2 ≤ n) (hT : IsSylowIn 2 T ⊤)
    (hLT : L ⊔ T = ⊤) (hsw : SwapsParabolics T L) :
    ∃ (P₀ P₁ : Subgroup Q) (F : Type) (_ : Field F) (_ : Finite F) (w : F × F → Q),
      Setting L T P₀ P₁ n w := by
  have hL : L.Normal := normal_of_fstar_eq hF
  have hnab : ∃ a b : ↥L, a * b ≠ b * a :=
    (CFSG.LocalAnalysis.UniquenessCase.UC22.uc22p22a_sp4_simple ↥L n hSp).2
  have hC : centralizer (L : Set Q) = ⊥ := centralizer_eq_bot_of_fstar_eq hF hsimple hnab
  have hP4 : IsPSp4 2 n ↥L :=
    CFSG.Blueprint.LieModel.statedClassicalModel_of_ne_zero (by norm_num : (2 : ℕ) ≠ 0) hSp
  have hR : IsSylowTwoOf (T ⊓ L) L := sylowTwoOf_inf_of_isSylowIn hT hL
  obtain ⟨K, hKf, hKfin, φ, hcard, hφ⟩ :=
    CFSG.Quasithin.Sp4.exists_equiv_projUnipotent hn hP4 hR
  letI : Field K := hKf
  letI : Finite K := hKfin
  haveI hchar : CharP K 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
      Nat.prime_two (by omega) hcard
  let ψ : StatedSp 2 K ≃* StatedProj (StatedSp 2 K) :=
    MulEquiv.ofBijective (proj 2 K)
      ⟨CFSG.QuasithinUnique.K1.proj_injective_charTwo,
        fun x => QuotientGroup.mk'_surjective _ x⟩
  have hψ : ∀ s, ψ s = proj 2 K s := fun s => rfl
  let ι : StatedSp 2 K →* Q := L.subtype.comp (ψ.trans φ.symm).toMonoidHom
  have hιeq : ∀ s, ι s = ((φ.symm (ψ s) : ↥L) : Q) := fun s => rfl
  have hι : Function.Injective ι := by
    intro a b hab
    exact (ψ.trans φ.symm).injective (Subtype.ext hab)
  have hrange : ι.range = L := range_comp φ ψ
  have hmapU : (unipotent 2 K).map ι = T ⊓ L := map_unipotent_eq φ hφ ψ hψ ι hιeq
  let P₀ : Subgroup Q := (Q2 K 0).map ι
  let P₁ : Subgroup Q := (Q2 K 1).map ι
  let w : K × K → Q := Sp4.vW φ
  have hw : w = Sp4.vW φ := rfl
  have hw_tau : ∀ x : K × K, w x = ι (tauS x.1 x.2 0) :=
    fun x => vW_eq_tauS φ ψ hψ ι hιeq x
  have hC₀ : (sp4C (Q2 K 0) (pCoreOf 2 (perfectCore (Q2 K 0)))).map ι =
      sp4C P₀ (pCoreOf 2 (perfectCore P₀)) := by
    simpa [P₀] using sp4C_map_Q2 ι hι 0
  have hC₁ : (sp4C (Q2 K 1) (pCoreOf 2 (perfectCore (Q2 K 1)))).map ι =
      sp4C P₁ (pCoreOf 2 (perfectCore P₁)) := by
    simpa [P₁] using sp4C_map_Q2 ι hι 1
  refine ⟨P₀, P₁, K, hKf, hKfin, w, ?_⟩
  exact setting_of_model φ hφ hcard hL hsimple hnab hC hSp hn hT hLT hsw ι hι hrange
    hmapU P₀ P₁ rfl rfl w hw hw_tau hC₀ hC₁

end CFSG.LocalAnalysis.WeakClosure81.SwapSp4
