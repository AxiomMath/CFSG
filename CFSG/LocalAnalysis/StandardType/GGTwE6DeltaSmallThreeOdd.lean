module

public import CFSG.LocalAnalysis.StandardType.GGUSixTwoTransfer
public import CFSG.LocalAnalysis.StandardType.GGTwE6DeltaThreeSix
public import CFSG.LocalAnalysis.StandardType.GGTwE6DeltaThreePure
import CFSG.LocalAnalysis.StandardType.GGTwE6DD2Cover
import CFSG.LocalAnalysis.StandardType.GGTwE6LangThree
import CFSG.LocalAnalysis.StandardType.GGTwE6DeltaThreeInn

public section

namespace CFSG.StandardType.SmallExc

open CFSG.Assembly

theorem ggStdSubTwoTorusDeltaSmall_three_of_odd {r : ℕ} {R : Type} [Group R]
    {I : Set (MulAut R)} (hcenR : Subgroup.center R = ⊥)
    (h : ∀ (L' : Type) [Group L'] [Finite L'] (ψ : L' →* R), Function.Surjective ψ →
      ψ.ker ≤ Subgroup.center L' → commutator L' = ⊤ → Odd (Nat.card ψ.ker) →
      ∀ A : Subgroup (MulAut L'), IsElemAbelian 3 A →
        (∀ a ∈ A, ∃ φ ∈ I, ∀ l : L', φ (ψ l) = ψ (a l)) →
        3 ^ r ≤ Nat.card A → 3 ^ 3 ≤ Nat.card A → GGDeltaAdm 3 L' A →
        ∀ a ∈ A, a ≠ 1 → IsComponentOf (LargeEvenLayer (ggFix a)) (ggFix a) →
          (∀ a' ∈ A, ((∀ j ∈ LargeEvenLayer (ggFix a), a' j = j) ↔ a' ∈ Subgroup.zpowers a)) →
          GGStdSubSmallHyp 3 A a → GGStdSubTwoTorusConcl 3 A a) :
    GGStdSubTwoTorusDeltaSmall 3 r R I := by
  intro L' _ _ ψ hψ hker hperf A hA hAI hr h3 hadm a ha ha1 hcomp hcent hsm
  have hZ2 : USixTwo.zTwo L' ≤ ψ.ker := USixTwo.zTwo_le_ker hψ hcenR
  have hinj := USixTwo.qAutHom_injective hperf
  have hcard : Nat.card (A.map (USixTwo.qAutHom L')) = Nat.card A :=
    Subgroup.card_map_of_injective hinj
  have hAb : IsElemAbelian 3 (A.map (USixTwo.qAutHom L')) := TableB.isElemAbelian_map hA _
  refine USixTwo.concl_up hperf hA ha (h (USixTwo.Qt L') (USixTwo.qLift ψ hZ2)
    (USixTwo.qLift_surjective hZ2 hψ) (USixTwo.qLift_ker_le_center hZ2 hker)
    (USixTwo.qmk_perfect hperf) (USixTwo.qLift_odd_ker hZ2 hker) (A.map (USixTwo.qAutHom L'))
    hAb ?_ (by rw [hcard]; exact hr) (by rw [hcard]; exact h3)
    (USixTwo.ggDeltaAdm_descent hperf hA hadm) _ ⟨a, ha, rfl⟩ ?_
    (USixTwo.isComponentOf_layer_down USixTwo.qmk_surjective USixTwo.qmk_ker_le_center
      (USixTwo.qAutHom_compat a) hcomp) ?_ (USixTwo.smallHyp_down hperf hA ha hsm))
  · rintro _ ⟨a', ha', rfl⟩
    obtain ⟨φ, hφ, hφa⟩ := hAI a' ha'
    exact ⟨φ, hφ, USixTwo.qLift_qAut hZ2 a' φ hφa⟩
  · intro h1
    exact ha1 (hinj (by rw [h1, map_one]))
  · rintro _ ⟨a', ha', rfl⟩
    exact (USixTwo.cent_iff hperf a a').mp (hcent a' ha')

theorem card_le_card_center_mul_card_map {L' R : Type} [Group L'] [Finite L'] [Group R]
    {ψ : L' →* R} (hkc : ψ.ker = Subgroup.center L') (E : Subgroup L') :
    Nat.card E ≤ Nat.card (Subgroup.center L') * Nat.card (E.map ψ) := by
  set f : E →* R := ψ.comp E.subtype with hf
  have h1 : Nat.card f.ker * Nat.card f.range = Nat.card E := Subgroup.card_ker_mul_card_range f
  have h2 : f.range = E.map ψ := by rw [hf, MonoidHom.range_comp, Subgroup.range_subtype]
  have h3 : Nat.card f.ker ≤ Nat.card (Subgroup.center L') := by
    refine Nat.card_le_card_of_injective
      (fun k => (⟨((k : E) : L'), by rw [← hkc]; exact k.2⟩ : Subgroup.center L'))
      fun x y hxy => Subtype.ext (Subtype.ext (congrArg Subtype.val hxy :))
  rw [← h1, h2]
  exact Nat.mul_le_mul_right _ h3

theorem card_comap_conj {R : Type} [Group R]
    (hc : Function.Injective (MulAut.conj : R →* MulAut R)) (Y : Subgroup (MulAut R)) :
    Nat.card (Y.comap (MulAut.conj : R →* MulAut R)) =
      Nat.card (Y ⊓ (MulAut.conj : R →* MulAut R).range : Subgroup (MulAut R)) := by
  rw [← Subgroup.card_map_of_injective hc, Subgroup.map_comap_eq, inf_comm]

namespace TwE6DS3


variable {K : Type} [Field K] [Finite K] {n : ℕ} {L' : Type} [Group L'] [Finite L']
  {ψ : L' →* TwE6Delta.RecipeR K n}

theorem card_center_eq_one_or_three (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 2)
    (hψ : Function.Surjective ψ) (hker : ψ.ker ≤ Subgroup.center L') (hperf : commutator L' = ⊤)
    (hodd : Odd (Nat.card ψ.ker)) :
    Nat.card (Subgroup.center L') = 1 ∨ Nat.card (Subgroup.center L') = 3 := by
  obtain ⟨hexp, hcyc⟩ := TwE6DD2.center_facts hn hK hψ hker hperf
  rw [BstarDesc.ker_eq_center hψ hker (TwE6Delta.center_recipeR_eq_bot hn hK)] at hodd
  have hcop : (Nat.card (Subgroup.center L')).Coprime (4 ^ Nat.card L') := by
    have h2 : (Nat.card (Subgroup.center L')).Coprime 2 := Nat.coprime_two_right.mpr hodd
    have h4 : (Nat.card (Subgroup.center L')).Coprime 4 := by
      simpa using Nat.Coprime.pow_right 2 h2
    exact Nat.Coprime.pow_right _ h4
  have hcube : ∀ z ∈ Subgroup.center L', z ^ 3 = 1 := by
    intro z hz
    obtain ⟨z', hz'⟩ := (Nat.Coprime.pow_left_bijective hcop).2 ⟨z, hz⟩
    have h1 := hexp z' z'.2
    have h2 : (z' : L') ^ 4 ^ Nat.card L' = z := congrArg Subtype.val hz'
    rwa [h2] at h1
  rcases Subgroup.bot_or_exists_ne_one (Subgroup.center L') with hbot | ⟨z₀, hz₀, hz₀1⟩
  · left
    rw [hbot]
    exact Subgroup.card_bot
  · right
    have ho : orderOf z₀ = 3 := by
      have hd : orderOf z₀ ∣ 3 := orderOf_dvd_of_pow_eq_one (hcube z₀ hz₀)
      rcases (Nat.dvd_prime Nat.prime_three).1 hd with h1 | h3
      · exact absurd (orderOf_eq_one_iff.1 h1) hz₀1
      · exact h3
    have hle : Subgroup.center L' ≤ Subgroup.zpowers z₀ := fun z hz =>
      hcyc z₀ hz₀ z hz ho (hcube z hz)
    have h1 : Nat.card (Subgroup.center L') ≤ Nat.card (Subgroup.zpowers z₀) :=
      Subgroup.card_le_of_le hle
    rw [Nat.card_zpowers, ho] at h1
    have h2 : 3 ∣ Nat.card (Subgroup.center L') := ho ▸ Subgroup.orderOf_dvd_natCard _ hz₀
    have h3 : 0 < Nat.card (Subgroup.center L') := Nat.card_pos
    omega

theorem five_le_card (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 2) (h3 : 3 ∣ 2 ^ n + 1)
    (hψ : Function.Surjective ψ) (hker : ψ.ker ≤ Subgroup.center L') (hperf : commutator L' = ⊤)
    {A : Subgroup (MulAut L')} (hadm : GGDeltaAdm 3 L' A) : 3 ^ 5 ≤ Nat.card A := by
  obtain ⟨⟨E5, hE5, hE5c⟩, hC6⟩ :=
    ggTwE6ThreeCoverRankInput_holds K n hn hK h3 L' ψ hψ hker hperf
  rcases hadm.2 with ⟨-, hb⟩ | ⟨hz, hb, -⟩
  · exact hE5c.trans (hb E5 hE5)
  · obtain ⟨E6, hE6, hE6c⟩ := hC6 (Or.inr hz)
    refine Nat.le_of_mul_le_mul_left ?_ (by norm_num : 0 < 3)
    calc 3 * 3 ^ 5 = 3 ^ 6 := by norm_num
      _ ≤ Nat.card E6 := hE6c
      _ ≤ 3 * Nat.card A := hb E6 hE6

theorem exists_fixed (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 2) (h3 : 3 ∣ 2 ^ n + 1)
    (hψ : Function.Surjective ψ) (hker : ψ.ker ≤ Subgroup.center L') (hperf : commutator L' = ⊤)
    (hodd : Odd (Nat.card ψ.ker)) {A : Subgroup (MulAut L')} (hA : IsElemAbelian 3 A)
    (h5 : 3 ^ 5 ≤ Nat.card A)
    (hAI : ∀ a ∈ A, ∃ φ ∈ TwE6Delta.RecipeI K n, ∀ l : L', φ (ψ l) = ψ (a l))
    {Y : Subgroup (MulAut (TwE6Delta.RecipeR K n))} (hY : IsElemAbelian 3 Y)
    (hYI : (Y : Set (MulAut (TwE6Delta.RecipeR K n))) ⊆ TwE6Delta.RecipeI K n)
    (hYc : Nat.card Y = 3 ^ 6) (hAY : ∀ a ∈ A, ∃ y ∈ Y, ∀ l : L', y (ψ l) = ψ (a l)) :
    ∃ E : Subgroup L', IsElemAbelian 3 E ∧ Subgroup.center L' ≤ E ∧
      Nat.card (Subgroup.center L') * 3 ^ 5 ≤ Nat.card E ∧ ∀ a ∈ A, ∀ e ∈ E, a e = e := by
  classical
  rcases card_center_eq_one_or_three hn hK hψ hker hperf hodd with hZ1 | hZ3
  ·
    haveI := TwE6Delta.finite_recipeR hK
    have hZbot : Subgroup.center L' = ⊥ := Subgroup.card_eq_one.1 hZ1
    have hψinj : Function.Injective ψ :=
      (MonoidHom.ker_eq_bot_iff ψ).1 (le_bot_iff.1 (hZbot ▸ hker))
    have hcinj : Function.Injective
        (MulAut.conj : TwE6Delta.RecipeR K n →* MulAut (TwE6Delta.RecipeR K n)) :=
      TwE6D3.conj_injective_of_center_card_eq_one
        (by rw [TwE6Delta.center_recipeR_eq_bot hn hK]; exact Subgroup.card_bot)
    have hERc : 3 ^ 5 ≤ Nat.card (Y.comap
        (MulAut.conj : TwE6Delta.RecipeR K n →* MulAut (TwE6Delta.RecipeR K n))) := by
      have h1 := TwE6D3.recipe_inn_index hn hK hYI
      rw [card_comap_conj hcinj]
      rw [hYc] at h1
      norm_num at h1 ⊢
      omega
    refine ⟨(Y.comap (MulAut.conj : TwE6Delta.RecipeR K n →* MulAut (TwE6Delta.RecipeR K n))).comap
      ψ, (hY.comap hcinj).comap hψinj, by rw [hZbot]; exact bot_le, ?_, ?_⟩
    · rw [hZ1, one_mul, ← Subgroup.card_map_of_injective hψinj,
        Subgroup.map_comap_eq_self_of_surjective hψ]
      exact hERc
    · intro a ha e he
      obtain ⟨y, hy, hya⟩ := hAY a ha
      have he' : MulAut.conj (ψ e) ∈ Y := he
      have hfix : y (ψ e) = ψ e := hcinj (by
        rw [TwE6D3.conj_apply_aut, hY.comm hy he', mul_inv_cancel_right])
      exact hψinj (by rw [← hya, hfix])
  ·
    obtain ⟨E, hE, hEc, hEfix⟩ :=
      TwE6D3.torusLiftInput_holds K n hn hK h3 L' ψ hψ hker hperf hZ3 A hA h5 hAI
    have hZel : IsElemAbelian 3 (Subgroup.center L') := by
      refine ⟨⟨⟨fun x y => Subtype.ext (Subgroup.mem_center_iff.mp y.2 x)⟩⟩, fun z hz => ?_⟩
      have h1 : (⟨z, hz⟩ : Subgroup.center L') ^ 3 = 1 := by
        rw [← hZ3]
        exact pow_card_eq_one'
      simpa using congrArg Subtype.val h1
    refine ⟨E ⊔ Subgroup.center L', hE.sup_of_commute hZel fun x _ z hz =>
      Subgroup.mem_center_iff.mp hz x, le_sup_right, ?_, fun a ha => ?_⟩
    · rw [hZ3]
      calc 3 * 3 ^ 5 = 3 ^ 6 := by norm_num
        _ ≤ Nat.card E := hEc
        _ ≤ Nat.card (E ⊔ Subgroup.center L' : Subgroup L') := Subgroup.card_le_of_le le_sup_left
    · have hle : E ⊔ Subgroup.center L' ≤ ggFix a := sup_le
        (fun e he => mem_ggFix.2 (hEfix a ha e he)) fun z hz => mem_ggFix.2
          (CFSG.RankThree.PartTwo.Sec14.Res148.fix_center_of_pow_three a (hA.2 a ha) hZ3 z hz)
      exact fun e he => mem_ggFix.1 (hle he)

end TwE6DS3

end CFSG.StandardType.SmallExc

end
