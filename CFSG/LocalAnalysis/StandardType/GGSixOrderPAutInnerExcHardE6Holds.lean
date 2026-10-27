module

public import CFSG.LocalAnalysis.StandardType.GGSixOrderPAutInnerExcHardE6
public import CFSG.LocalAnalysis.StandardType.GGSixOrderPAutInnerExcHardF4
public import Certificates.Certificate1952
public import Certificates.Certificate3951
public import Certificates.Certificate13604
public import Certificates.Certificate13724
import CFSG.GroupTheory.ElemAbelianClosure
import CFSG.LocalAnalysis.StandardType.GGOrdPToralLang
import CFSG.LocalAnalysis.StandardType.GGExcElemToralE6
import CFSG.LocalAnalysis.StandardType.GGExcFieldRankE6
import CFSG.LocalAnalysis.StandardType.GGTableBExcE6Basic
import CFSG.LieType.SeitzGeneration.ExcHighThree.E6InF4Assemble
public import CFSG.Quasithin.Vol2.KGFactC31RuRef
public import CFSG.Quasithin.Vol2.KGFactC31RuRefBase
public import CFSG.Sporadic.HeldB.Common
public import CFSG.Sporadic.Schreier.RuPair
public import CFSG.Sporadic.Schreier.RuSylow
public import Certificates.Certificate7233Base
import CFSG.ClassicalInvolution.ModelFacts.PairFrameExcE8Rank1
import CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Detect.E8.MPart
import CFSG.HardMathSupport.Lang.AnisoE6.CatBridge
import CFSG.RankThree.Chevalley.SteinbergBNNoninnerComponentNodes
import CFSG.RankThree.Chevalley.SteinbergCFOddE7E8NoninnerComponent
import CFSG.RankThree.PartOne.KE.Basic
import CFSG.RankThree.PartOne.KE.D4LayerAlgebraic
import CFSG.RankThree.PartOne.KE.E8NineData
import CFSG.RankThree.PartOne.KE.NativeCyclicMain
import CFSG.RankThree.PartOne.KF4.EvenDescent

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Universal
  CFSG.LieType.RootSystem CFSG.LieType.Chevalley CFSG.LieType.SeitzGeneration
  CFSG.LieType.Steinberg.Exceptional CFSG.LieType.Steinberg.Isogeny

namespace OrdPInnerExc

theorem exists_isElemAbelian_card_eq_of_conj_into_range {F C : Type*} [Group F] [Group C]
    {p : ℕ} {φ : F →* C} (hφ : Function.Injective φ) {A : Subgroup C} (hA : IsElemAbelian p A)
    {g : C} (hg : ∀ x ∈ A, g * x * g⁻¹ ∈ φ.range) :
    ∃ B : Subgroup F, IsElemAbelian p B ∧ Nat.card B = Nat.card A := by
  set A' : Subgroup C := A.map (MulAut.conj g).toMonoidHom with hA'map
  have hAel : IsElemAbelian p A' := isElemAbelian_map _ hA
  have hle : A' ≤ φ.range := by
    rintro _ ⟨x, hx, rfl⟩
    exact hg x hx
  refine ⟨A'.comap φ, CFSG.Open.IsElemAbelian.comap hAel hφ, ?_⟩
  · rw [← Subgroup.card_map_of_injective hφ (K := A'.comap φ),
      Subgroup.map_comap_eq_self hle]
    exact Subgroup.card_map_of_injective (MulAut.conj g).injective

theorem ggOrdPToralMax_of_conj_into_range {F C : Type*} [Group F] [Group C] {p : ℕ}
    {φ : F →* C} (hφ : Function.Injective φ)
    (hconj : ∀ A : Subgroup C, IsElemAbelian p A → ∃ g : C, ∀ x ∈ A, g * x * g⁻¹ ∈ φ.range)
    (h : GGOrdPToralMax F p) : GGOrdPToralMax C p := by
  intro u hu
  obtain ⟨g, hg⟩ := hconj (Subgroup.zpowers u) (isElemAbelian_zpowers hu)
  obtain ⟨v, hv, hvp⟩ : ∃ v : F, φ v = g * u * g⁻¹ ∧ v ^ p = 1 := by
    have hmem : g * u * g⁻¹ ∈ φ.range := hg u (Subgroup.mem_zpowers u)
    obtain ⟨v, hv⟩ := hmem
    refine ⟨v, hv, ?_⟩
    apply hφ
    rw [map_pow, hv, conj_pow, hu, map_one]
    group
  obtain ⟨E, hEel, hvE, hEmax⟩ := h v hvp
  have hEcard : Nat.card (E.map φ) = Nat.card E :=
    Subgroup.card_map_of_injective hφ
  refine ⟨(E.map φ).map (MulAut.conj g⁻¹).toMonoidHom,
    isElemAbelian_map _ (isElemAbelian_map _ hEel), ⟨_, ⟨v, hvE, hv⟩, ?_⟩, ?_⟩
  · simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    group
  · intro A hA
    obtain ⟨g', hg'⟩ := hconj A hA
    obtain ⟨B, hBel, hBcard⟩ :=
      exists_isElemAbelian_card_eq_of_conj_into_range hφ hA hg'
    rw [Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective,
      hEcard, ← hBcard]
    exact hEmax B hBel

end OrdPInnerExc

theorem ggOrdPToralMax_adjointE6_five
    {K : Type} [Field K] [Finite K] [CharP K 2] (h5 : 5 ∣ Nat.card K - 1) :
    GGOrdPToralMax (adjointGroup .E6 K) 5 := by
  have hmax : ∀ A : Subgroup (adjointGroup .E6 K), IsElemAbelian 5 A →
      Nat.card A ≤ Nat.card (TableBExc.torusPow .E6 K 5) := by
    intro A hA
    have he : orderOf ((Nat.card K : ℕ) : ZMod 5) = 1 := by
      rw [orderOf_eq_one_iff, TableBExc.cast_eq_one_of_dvd_sub_one (Nat.card_pos) h5]
    have hrank := rankLE_E6 (K := K) (p := 5) (e := 1) Nat.prime_five (by norm_num) he
    have hdeg : degCount .E6 1 = 6 := by decide
    have hVcard : Nat.card (TableBExc.torusPow .E6 K 5) = 5 ^ 6 :=
      TableBExc.card_torusPow_E6 (K := K) Nat.prime_five (by norm_num) h5
    calc Nat.card A ≤ 5 ^ degCount .E6 1 := hrank A hA
      _ = Nat.card (TableBExc.torusPow .E6 K 5) := by rw [hdeg, hVcard]
  refine OrdPToralLang.ggOrdPToralMax_of_conj_mem
    (OrdPInnerExc.isElemAbelian_torusPow .E6 K 5) ?_ hmax
  intro u hu
  obtain ⟨g, hg⟩ := ggE6ElemToralFiveInput_holds (K := K) h5 u hu
  refine ⟨g, ?_⟩
  rw [TableBExc.mem_torusPow]
  exact ⟨hg u (Subgroup.mem_zpowers u), by rw [conj_pow, hu]; group⟩

theorem ggOrdPToralMax_adjointE6_three_of_F4
    {K : Type} [Field K] [Finite K] (hK : Nat.card K % 3 = 2)
    (hF4 : GGOrdPToralMax (adjointGroup .F4 K) 3) : GGOrdPToralMax (adjointGroup .E6 K) 3 := by
  refine OrdPInnerExc.ggOrdPToralMax_of_conj_into_range
    (ExcHighThree.embE6F4_injective K) ?_ hF4
  intro A hA
  exact ExcHighThree.conj_into_fixE6_two K hK (fun x hx => hA.2 x hx)

theorem ggOrdPToralE6RestHard_of_F4
    (hF4 : GGOrdPToralF4RestHard) : GGOrdPToralE6RestHard := by
  intro f p hf hp hcase hA
  have hK : Nat.card (GaloisField 2 f) = 2 ^ f := GaloisField.card 2 f (by omega)
  haveI : Finite (adjointGroup .E6 (GaloisField 2 f)) := generated_group_finite .E6 _
  have hker := CFSG.ClassicalInvolution.ModelFacts.ChevAut.e6Isogeny_ker_le_center
    (GaloisField 2 f)
  have hcop5 : Nat.Coprime (Nat.card (e6Isogeny (GaloisField 2 f)).ker) 5 :=
    Nat.Coprime.coprime_dvd_left (Subgroup.card_dvd_of_le hker)
      (OrdPInnerExc.coprime_card_center_E6 (k := GaloisField 2 f) Nat.prime_five
        (Or.inl (by norm_num)))
  by_cases hp5 : p = 5
  · subst hp5
    rcases hcase with ⟨h53, -⟩ | ⟨-, h5div⟩
    · omega
    · have h5' : 5 ∣ Nat.card (GaloisField 2 f) - 1 := by rw [hK]; exact h5div
      exact OrdPInnerExc.ggOrdPToralMax_of_surjective Nat.prime_five
        (e6Isogeny_surjective (GaloisField 2 f)) hker hcop5
        (ggOrdPToralMax_adjointE6_five (K := GaloisField 2 f) h5')
  · have hp3 : p = 3 := by
      rcases hcase with ⟨h, -⟩ | ⟨h, -⟩
      · exact h
      · exact absurd h hp5
    subst hp3
    have h3div : 3 ∣ 2 ^ f + 1 := by
      rcases hcase with ⟨-, h⟩ | ⟨h, -⟩
      · exact h
      · omega
    have h3mod : 2 ^ f % 3 = 2 := by
      have h : (2 ^ f + 1) % 3 = 0 := Nat.dvd_iff_mod_eq_zero.mp h3div
      omega
    have hK3 : Nat.card (GaloisField 2 f) % 3 = 2 := by rw [hK]; exact h3mod
    have h3ndiv : ¬ 3 ∣ Nat.card (GaloisField 2 f) - 1 := by
      rw [hK, Nat.dvd_iff_mod_eq_zero]
      omega
    have hcop3 : Nat.Coprime (Nat.card (e6Isogeny (GaloisField 2 f)).ker) 3 :=
      Nat.Coprime.coprime_dvd_left (Subgroup.card_dvd_of_le hker)
        (OrdPInnerExc.coprime_card_center_E6 (k := GaloisField 2 f) Nat.prime_three
          (Or.inr h3ndiv))
    have hex : ∃ B : Subgroup (adjointGroup .F4 (GaloisField 2 f)),
        IsElemAbelian 3 B ∧ 3 ^ 4 ≤ Nat.card B := by
      by_contra hno
      have hlt : ∀ A' : Subgroup (adjointGroup .E6 (GaloisField 2 f)),
          IsElemAbelian 3 A' → Nat.card A' < 3 ^ 4 := by
        intro A' hA'
        obtain ⟨g, hg⟩ := ExcHighThree.conj_into_fixE6_two (GaloisField 2 f) hK3
          (fun x hx => hA'.2 x hx)
        obtain ⟨B, hBel, hBcard⟩ :=
          OrdPInnerExc.exists_isElemAbelian_card_eq_of_conj_into_range
            (ExcHighThree.embE6F4_injective (GaloisField 2 f)) hA' hg
        rw [← hBcard]
        exact not_le.mp fun hle => hno ⟨B, hBel, hle⟩
      obtain ⟨A, hAel, hAc⟩ := hA
      exact absurd hAc (Nat.not_le_of_gt (OrdPInnerExc.card_lt_of_card_lt_map hcop3 hlt hAel))
    exact OrdPInnerExc.ggOrdPToralMax_of_surjective Nat.prime_three
      (e6Isogeny_surjective (GaloisField 2 f)) hker hcop3
      (ggOrdPToralMax_adjointE6_three_of_F4 hK3 (hF4 f hf hex))

end CFSG.StandardType
