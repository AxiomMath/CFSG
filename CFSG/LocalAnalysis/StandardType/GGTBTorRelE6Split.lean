module

public import CFSG.LocalAnalysis.StandardType.GGTBTorRelE6Cover
public import CFSG.LocalAnalysis.StandardType.GGTorusE6RelativeLang
public import CFSG.LocalAnalysis.StandardType.GGTorusE6RelativeLangWeyl
public import CFSG.LocalAnalysis.StandardType.GGTorusCentralLift
public import CFSG.LocalAnalysis.StandardType.GGKGForkExcE6PlusSylow
public import CFSG.LocalAnalysis.StandardType.GGTBTorRel
public import CFSG.LocalAnalysis.StandardType.GGTBTorRelE6Twisted

public noncomputable section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley TableBExc


theorem exists_aligned_LangFrame_E6_relative {K : Type} [Field K] [Finite K] [CharP K 2]
    {n p r : ℕ} (hn : 1 ≤ n) (hK : Nat.card K = 2 ^ n)
    (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3) (hpq : p ∣ 2 ^ n + 1)
    {L : Type} [Group L] [Finite L] (ψ : L →* RecipeGroup .E6 K)
    (A : Subgroup (MulAut L))
    (hA : GGTorusTBGroup p r (RecipeGroup .E6 K) (RecipeID .E6 K) L ψ A) :
    ∃ (ψ0 : L →* adjointGroup .E6 K) (Λ0 : adjointGroup .E6 K →* MulAut L)
      (E : Subgroup (adjointGroup .E6 K)) (F : ExcFrame .E6 K p E),
      Function.Surjective ψ0 ∧ ψ0.ker = ψ.ker ∧
      Function.Injective Λ0 ∧ (∀ x : L, Λ0 (ψ0 x) = MulAut.conj x) ∧
      E.map Λ0 = A ∧ ExcIsLongest .E6 F.w := by
  classical
  obtain ⟨hψ, hker, hperf, hAab, hAI, _hAr, _hA3, hAsc⟩ := hA
  let : Fact p.Prime := ⟨hp⟩
  have hp5 : 5 ≤ p := by
    have hp4 : p ≠ 4 := by rintro rfl; norm_num at hp
    have hpge := hp.two_le
    omega
  obtain ⟨Λ, hΛ, hΛi, -, -, hEab, hEcard, hEA, hEsc⟩ :=
    exists_innerModel_recipe_E6 hp (ggOutdiagPrime_E6 hp hp3)
      (ExcSplitL.ggCenterPrime_recipe_E6 hp hp2 hp3) ψ hψ hker hperf hAab hAI hAsc
  let e := recipeEquiv .E6 K
  let E : Subgroup (adjointGroup .E6 K) := (A.comap Λ).map e.toMonoidHom
  let ψ0 : L →* adjointGroup .E6 K := e.toMonoidHom.comp ψ
  let Λ0 : adjointGroup .E6 K →* MulAut L := Λ.comp e.symm.toMonoidHom
  have hψ0 : Function.Surjective ψ0 := e.surjective.comp hψ
  have hk0 : ψ0.ker = ψ.ker := MonoidHom.ker_mulEquiv_comp ψ e
  have hΛ0 : Function.Injective Λ0 := hΛi.comp e.symm.injective
  have hΛψ0 : ∀ x : L, Λ0 (ψ0 x) = MulAut.conj x := by
    intro x
    change Λ (e.symm (e (ψ x))) = MulAut.conj x
    rw [e.symm_apply_apply]
    exact hΛ rfl
  have hEcard0 : Nat.card E = Nat.card A := by
    rw [Subgroup.card_map_of_injective e.injective]
    exact hEcard
  have hEab0 : IsElemAbelian p E := hEab.map e.toMonoidHom
  have hEsc0 : ∀ g : adjointGroup .E6 K, (∀ t ∈ E, g * t = t * g) → g ^ p = 1 → g ∈ E := by
    intro g hg hgp
    have h1 : e.symm g ∈ A.comap Λ := by
      apply hEsc (e.symm g)
      · intro t ht
        apply e.injective
        rw [map_mul, map_mul, e.apply_symm_apply]
        exact hg (e t) ⟨t, ht, rfl⟩
      · rw [← map_pow, hgp, map_one]
    exact ⟨e.symm g, h1, e.apply_symm_apply g⟩
  have hpq0 : p ∣ Nat.card K + 1 := by rw [hK]; exact hpq
  obtain ⟨F, hlong0⟩ :=
    ExcE6Plus.exists_excFrame_of_selfCentralizing hp hp5 hpq0 E hEab0 hEsc0
  have hAout : E.map Λ0 = A := by
    change ((A.comap Λ).map e.toMonoidHom).map (Λ.comp e.symm.toMonoidHom) = A
    rw [Subgroup.map_map]
    have hcomp : (Λ.comp e.symm.toMonoidHom).comp e.toMonoidHom = Λ := by
      ext x y
      change Λ (e.symm (e x)) y = Λ x y
      rw [e.symm_apply_apply]
    rw [hcomp]
    exact hEA
  exact ⟨ψ0, Λ0, E, F, hψ0, hk0, hΛ0, hΛψ0, hAout, hlong0⟩

theorem ggTorusTorW_recipe_E6_relative {K : Type} [Field K] [Finite K] [CharP K 2]
    {n p r : ℕ} (hn : 1 ≤ n) (hK : Nat.card K = 2 ^ n)
    (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3) (hpq : p ∣ 2 ^ n + 1) :
    GGTorusTorW p r (2 ^ n + 1) 4 CartanMatrix.F₄ CoxeterMatrix.F₄
      (RecipeGroup .E6 K) (RecipeID .E6 K) := by
  classical
  intro L _ _ ψ A hA
  obtain ⟨ψ0, Λ0, E, F, hψ0, hk0, hΛ0, hΛψ0, hAout, hlong⟩ :=
    exists_aligned_LangFrame_E6_relative hn hK hp hp2 hp3 hpq ψ A hA
  obtain ⟨hψ, hker, hperf, -, -, -, -, -⟩ := hA
  letI : Fact p.Prime := ⟨hp⟩
  have hp5 : 5 ≤ p := by
    have hp4 : p ≠ 4 := by rintro rfl; norm_num at hp
    have hpge := hp.two_le
    omega
  have hpq0 : p ∣ Nat.card K + 1 := by rw [hK]; exact hpq
  have hm : 1 < 2 ^ n + 1 := by
    have hpow : 0 < 2 ^ n := Nat.pow_pos (by norm_num)
    omega
  obtain ⟨nn, ζ, hζo, hζp, hFormula, hnN, eW, heW⟩ :=
    E6RelativeLangWeyl.exists_markedWeyl_qplusLang F hp hp5 hpq0 hlong
  let μ := rootsOfUnity (Nat.card K + 1) (AlgebraicClosure K)
  obtain ⟨l⟩ := ScalarLangTorus.exists_rootValue_equiv (K := K)
  have hζm : ζ ^ (Nat.card K + 1) = 1 := by
    obtain ⟨k, hk⟩ := hpq0
    rw [hk, pow_mul, hζp, one_pow]
  let z : μ := ⟨ζ, (mem_rootsOfUnity _ _).mpr hζm⟩
  have hzp : z ^ p = 1 := Subtype.ext hζp
  have hz1 : z ≠ 1 := by
    intro h
    have h1 : ζ = 1 := congrArg Subtype.val h
    rw [h1, orderOf_one] at hζo
    exact hp.ne_one hζo.symm
  obtain ⟨B, hCB, hBC⟩ := exists_int_matrix_inverse_mod_of_isUnit_det
    (m := Nat.card K + 1) CartanMatrix.F₄ (by
      have hdet : CartanMatrix.F₄.det = 1 := by decide +kernel
      rw [hdet]
      simpa using (isUnit_one : IsUnit (1 : ZMod (Nat.card K + 1))))
  let φ := E6RelativeLang.phi F hlong
  let S := E6RelativeLang.fullTorus F
  have hE : ∀ x, x ∈ E ↔ x ^ p = 1 ∧ x ∈ φ.range :=
    fun x => E6RelativeLang.mem_E_iff_pow_p_mem_phi_range F hlong hpq0
  have hcent : Subgroup.centralizer (E : Set (adjointGroup .E6 K)) ≤ S :=
    fun _ hx => E6RelativeLang.centralizer_le_fullTorus F hlong hp hp5 hpq0 hx
  have hcomm : ∀ a : Fin 4 → μ, ∀ t ∈ S, Commute (φ a) t :=
    fun a _ ht => E6RelativeLang.fullTorus_commute_phi F hlong a ht
  have htors : ∀ t ∈ S, t ^ (Nat.card K + 1) = 1 → t ∈ φ.range := by
    intro t ht hpow
    apply (E6RelativeLang.mem_fullTorus_pow_iff_mem_phi_range F hlong).mp
    exact ⟨ht, hpow⟩
  rw [← hAout]
  have hdata := ggTorusTorData_of_centralLift_rootCoordinates ψ0 hψ0
    (by rw [hk0]; exact hker) (by rw [hK]; exact hm)
    (by rw [hk0, hK]; exact coprime_card_ker_recipe_E6_relative hn hK ψ hψ hker hperf)
    l φ (E6RelativeLang.phi_injective F hlong) CartanMatrix.F₄ B hCB hBC
    Λ0 hΛ0 hΛψ0 E hE z hzp hz1 nn hnN hFormula S center_adjointGroup_eq_bot
    hcent hcomm htors CoxeterMatrix.F₄ eW heW
  simpa only [hK] using hdata

theorem ggTorusTorW_label_E6_relative {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3)
    {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab) (htag : lab.tag = .E6)
    (hpq : p ∣ 2 ^ lab.n + 1) :
    LargeEvenLabelAll lab fun R _ I _ =>
      GGTorusTorW p 4 (ggTorMpm p lab) 4 CartanMatrix.F₄ CoxeterMatrix.F₄ R I := by
  obtain ⟨t, r, n⟩ := lab
  have hn : 1 ≤ n := hlab.1
  dsimp only at htag hn hpq ⊢
  subst htag
  intro Q hQ
  dsimp only [LargeEvenRawDatum] at hQ ⊢
  obtain ⟨K, i1, i2, hK, hQK⟩ := hQ
  letI : CharP K 2 := charP_two_of_card hK
  refine ⟨K, i1, i2, hK, hQK, ?_⟩
  have hpminus : ¬ p ∣ 2 ^ n - 1 := by
    intro hd
    have hdiv : p ∣ (2 ^ n + 1) - (2 ^ n - 1) := Nat.dvd_sub hpq hd
    have hpow : 1 ≤ 2 ^ n := Nat.one_le_pow _ _ (by decide)
    have hsub : (2 ^ n + 1) - (2 ^ n - 1) = 2 := by omega
    rw [hsub] at hdiv
    exact hp2 ((Nat.dvd_prime Nat.prime_two).mp hdiv |>.resolve_left hp.ne_one)
  have hm : ggTorMpm p ⟨.E6, r, n⟩ = 2 ^ n + 1 := by
    simp [ggTorMpm, hpminus]
  rw [hm]
  exact ggTorusTorW_recipe_E6_relative hn hK hp hp2 hp3 hpq

theorem ggTBTorRelE6Split_holds : GGTBTorRelE6Split := by
  intro p hp hp2 hp3 lab hlab htag hpq
  exact ggTorusTorW_label_E6_relative hp hp2 hp3 hlab htag hpq

theorem ggTBTorRelE6_holds : GGTBTorRelE6 :=
  ggTBTorRelE6_of_split ggTBTorRelE6Split_holds

end CFSG.StandardType
