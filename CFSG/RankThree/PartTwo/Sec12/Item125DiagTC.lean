module

public import CFSG.RankThree.PartTwo.Sec12.Item125DiagBasic
import CFSG.RankThree.PartTwo.KFacts.KS12ClassOut
import CFSG.RankThree.PartTwo.KFacts.KS12ClassExp
import CFSG.RankThree.PartTwo.Sec13.Item13Theta

public section

namespace CFSG.RankThree.PartTwo.Sec12.Item125Diag

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.ABGLocalTools (IsSylowOf)

variable {G : Type} [Group G] [Finite G]

theorem le_of_isSylowOf_of_le_normalizer {p : ℕ} [Fact p.Prime] {P K E : Subgroup G}
    (hP : IsSylowOf p P K) (hEK : E ≤ K) (hKE : K ≤ Subgroup.normalizer (E : Set G))
    (hE : IsPGroup p E) : E ≤ P := by
  have hPE : IsPGroup p (P ⊔ E : Subgroup G) :=
    IsPGroup.to_sup_of_normal_right' hP.isPGroup hE (hP.le.trans hKE)
  have h := hP.eq_of_le le_sup_left (sup_le hP.le hEK) hPE
  rw [← h]
  exact le_sup_right

omit [Finite G] in
theorem ker_conj_eq_center (X : Type*) [Group X] :
    (MulAut.conj : X →* MulAut X).ker = Subgroup.center X := by
  ext x
  rw [MonoidHom.mem_ker]
  exact ⟨mem_center_of_conj_eq_one, conj_eq_one_of_mem_center⟩

omit [Finite G] in
theorem card_range_conj_mul (X : Type*) [Group X] [Finite X] :
    Nat.card (MulAut.conj : X →* MulAut X).range * Nat.card (Subgroup.center X) =
      Nat.card X := by
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center X)]
  congr 1
  rw [← ker_conj_eq_center]
  exact (Nat.card_congr (QuotientGroup.quotientKerEquivRange _).toEquiv).symm

theorem autIn_le_transvectionGroup_of_tc
    {c : G} {L E : Subgroup G} (hD : DiagHyp c L E)
    (hty : Sec4.IsTripleCover (L ⧸ aschbacherSolvableCore 3 L) (alternatingGroup (Fin 6)) ∨
      Sec4.IsTripleCover (L ⧸ aschbacherSolvableCore 3 L) (alternatingGroup (Fin 7)) ∨
      Sec4.IsTripleCover (L ⧸ aschbacherSolvableCore 3 L) CFSG.Blueprint.NativeSporadic.M22)
    {P : Subgroup G} (hP3 : IsPGroup 3 P) (hPN : P ≤ Subgroup.normalizer (L : Set G))
    (hEP : E ≤ P) (hPW : P ≤ Subgroup.normalizer (E : Set G)) :
    Sec4.autIn P E ≤ transvectionGroup E ⟨c, hD.mem_E⟩ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set R : Subgroup (MulAut (L ⧸ aschbacherSolvableCore 3 L)) :=
    (P.subgroupOf (Subgroup.normalizer (L : Set G))).map (thetaBarAct L) with hR
  have hR3 : IsPGroup 3 R :=
    (hP3.of_equiv (Subgroup.subgroupOfEquivOfLe hPN).symm).map _
  have hmemR : ∀ g (hg : g ∈ P), thetaBarAct L ⟨g, hPN hg⟩ ∈ R := fun g hg =>
    ⟨⟨g, hPN hg⟩, Subgroup.mem_subgroupOf.mpr hg, rfl⟩
  have hq := isQuasisimple_thetaQuot_of_mem hD.mem_thetaComponentsAt
  have hinner : R ≤ (MulAut.conj : (L ⧸ aschbacherSolvableCore 3 L) →* MulAut _).range := by
    intro σ hσ
    obtain ⟨k, hk⟩ := hR3 ⟨σ, hσ⟩
    have hk' : σ ^ 3 ^ k = 1 := by simpa using congrArg Subtype.val hk
    obtain ⟨x, hx⟩ := KFacts.ks12OutInner _ hq hty σ ⟨k, hk'⟩
    exact ⟨x, hx.symm⟩
  obtain ⟨m, hm3, hm⟩ := KFacts.exists_card_eq_of_isTripleCover hty
  have hInn : Nat.card (MulAut.conj : (L ⧸ aschbacherSolvableCore 3 L) →* MulAut _).range =
      9 * m := by
    have h := card_range_conj_mul (L ⧸ aschbacherSolvableCore 3 L)
    rw [hD.card_center, hm] at h
    omega
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hR3
  have hR9 : Nat.card R ∣ 9 := by
    have hdvd := Subgroup.card_dvd_of_le hinner
    rw [hInn, hk] at hdvd
    rw [hk]
    exact (Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr
      hm3)).dvd_of_dvd_mul_right hdvd
  obtain ⟨e₁, he₁, e₂, he₂, h₁, h₂⟩ := hD.exists_basis
  set ρ₁ := thetaBarAct L ⟨e₁, hPN (hEP he₁)⟩ with hρ₁
  set ρ₂ := thetaBarAct L ⟨e₂, hPN (hEP he₂)⟩ with hρ₂
  have hρ₁1 : ρ₁ ≠ 1 := fun h => h₁ (hD.mem_zpowers_of_thetaBarAct he₁ h)
  have hρ₁3 : ρ₁ ^ 3 = 1 := by
    rw [hρ₁, ← map_pow]
    have h3 : (⟨e₁, hPN (hEP he₁)⟩ : Subgroup.normalizer (L : Set G)) ^ 3 = 1 :=
      Subtype.ext (by simpa using hD.pow_three he₁)
    rw [h3, map_one]
  have hρ₁o : orderOf ρ₁ = 3 := orderOf_eq_prime hρ₁3 hρ₁1
  have hρ₂n : ρ₂ ∉ Subgroup.zpowers ρ₁ := by
    intro h
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp h
    have hmem : e₂ * e₁ ^ (-n) ∈ E := E.mul_mem he₂ (E.zpow_mem he₁ _)
    have h1 : thetaBarAct L ⟨e₂ * e₁ ^ (-n), hD.le_normalizer hmem⟩ = 1 := by
      have e1 : (⟨e₂ * e₁ ^ (-n), hD.le_normalizer hmem⟩ : Subgroup.normalizer (L : Set G)) =
          ⟨e₂, hPN (hEP he₂)⟩ * (⟨e₁, hPN (hEP he₁)⟩) ^ (-n) := by
        apply Subtype.ext
        simp
      rw [e1, map_mul, map_zpow, ← hρ₁, ← hρ₂, ← hn, ← zpow_add, add_neg_cancel, zpow_zero]
    have h2 := hD.mem_zpowers_of_thetaBarAct hmem h1
    apply h₂
    have e2 : e₂ = (e₂ * e₁ ^ (-n)) * e₁ ^ n := by group
    rw [e2]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left h2)
      (Subgroup.mem_sup_right (Subgroup.zpow_mem _ (Subgroup.mem_zpowers e₁) n))
  have hRcard : Nat.card R = 3 ^ 2 := by
    have hle : Subgroup.zpowers ρ₁ ≤ R := Subgroup.zpowers_le.mpr (hmemR e₁ (hEP he₁))
    have h9 : Nat.card R ≤ 9 := Nat.le_of_dvd (by norm_num) hR9
    have h3 : 3 ∣ Nat.card R := by
      have h := Subgroup.card_dvd_of_le hle
      rwa [Nat.card_zpowers, hρ₁o] at h
    rw [hk] at hR9 h3 h9 ⊢
    have hk2 : k ≤ 2 := (Nat.pow_dvd_pow_iff_le_right (by norm_num : 1 < 3)).mp
      (by rw [show (3 : ℕ) ^ 2 = 9 by norm_num]; exact hR9)
    interval_cases k
    · norm_num at h3
    · exfalso
      have hYeq : Subgroup.zpowers ρ₁ = R := Subgroup.eq_of_le_of_card_ge hle (by
        rw [hk, Nat.card_zpowers, hρ₁o, pow_one])
      exact hρ₂n (hYeq ▸ hmemR e₂ (hEP he₂))
    · rfl
  have hRc : IsMulCommutative R := IsPGroup.isMulCommutative_of_card_eq_prime_sq hRcard
  have hcomm : ∀ g (hg : g ∈ P), ∀ a ∈ E, g * a * g⁻¹ * a⁻¹ ∈ Subgroup.zpowers c := by
    intro g hg a ha
    have hga : g * a * g⁻¹ ∈ E := (Subgroup.mem_normalizer_iff.mp (hPW hg) a).mp ha
    have hmem : g * a * g⁻¹ * a⁻¹ ∈ E := E.mul_mem hga (E.inv_mem ha)
    refine hD.mem_zpowers_of_thetaBarAct hmem ?_
    have h1 : (⟨_, hD.le_normalizer hmem⟩ : Subgroup.normalizer (L : Set G)) =
        ⟨g, hPN hg⟩ * ⟨a, hPN (hEP ha)⟩ * (⟨g, hPN hg⟩)⁻¹ * (⟨a, hPN (hEP ha)⟩)⁻¹ := rfl
    have h2 := hRc.is_comm.comm ⟨_, hmemR g hg⟩ ⟨_, hmemR a (hEP ha)⟩
    have h3 : thetaBarAct L ⟨g, hPN hg⟩ * thetaBarAct L ⟨a, hPN (hEP ha)⟩ =
        thetaBarAct L ⟨a, hPN (hEP ha)⟩ * thetaBarAct L ⟨g, hPN hg⟩ :=
      congrArg Subtype.val h2
    rw [h1, map_mul, map_mul, map_mul, map_inv, map_inv, h3]
    group
  intro σ hσ
  obtain ⟨g, hgN, hgP, rfl⟩ := Sec4.mem_autIn_iff.mp hσ
  have hgc : g * c * g⁻¹ = c := by
    have h1 := hcomm g hgP c hD.mem_E
    have h2 : g * c * g⁻¹ ∈ Subgroup.zpowers c := by
      have e1 : g * c * g⁻¹ = (g * c * g⁻¹ * c⁻¹) * c := by group
      rw [e1]
      exact Subgroup.mul_mem _ h1 (Subgroup.mem_zpowers c)
    obtain ⟨j, hj⟩ := hP3 ⟨g, hgP⟩
    have hj' : g ^ 3 ^ j = 1 := by simpa using congrArg Subtype.val hj
    rw [commute_of_conj_mem_zpowers hD.orderOf_c h2 hj', mul_inv_cancel_right]
  refine ⟨Subtype.ext ?_, fun a => ?_⟩
  · rw [Sec4.normalizerMonoidHom_apply_coe]
    exact hgc
  · rw [mem_zpowers_subtype_iff, Subgroup.coe_mul, Sec4.normalizerMonoidHom_apply_coe,
      Subgroup.coe_inv]
    exact hcomm g hgP a a.2

theorem DiagHyp.closure_eq {c : G} {L E : Subgroup G} (hD : DiagHyp c L E) {e₁ e₂ : G}
    (he₁ : e₁ ∈ E) (he₂ : e₂ ∈ E) (h₁ : e₁ ∉ Subgroup.zpowers c)
    (h₂ : e₂ ∉ Subgroup.zpowers c ⊔ Subgroup.zpowers e₁) :
    Subgroup.closure ({c, e₁, e₂} : Set G) = E := by
  apply le_antisymm
  · rw [Subgroup.closure_le]
    rintro x (rfl | rfl | rfl)
    · exact hD.mem_E
    · exact he₁
    · exact he₂
  · rw [← hD.eq_sup_of_not_mem he₁ he₂ h₁ h₂]
    refine sup_le (sup_le ?_ ?_) ?_ <;> rw [Subgroup.zpowers_le] <;>
      exact Subgroup.subset_closure (by simp)

theorem normalizer_le_of_tc
    (h45 : Sec4.Item4_5)
    {A L : Subgroup G} {c : G} (h : Sec12StdBar G A c L)
    (hty : Sec4.IsTripleCover (L ⧸ aschbacherSolvableCore 3 L) (alternatingGroup (Fin 6)) ∨
      Sec4.IsTripleCover (L ⧸ aschbacherSolvableCore 3 L) (alternatingGroup (Fin 7)) ∨
      Sec4.IsTripleCover (L ⧸ aschbacherSolvableCore 3 L) CFSG.Blueprint.NativeSporadic.M22)
    {E : Subgroup G} (hD : DiagHyp c L E) :
    Subgroup.normalizer (E : Set G) ≤ Subgroup.normalizer (Subgroup.zpowers c : Set G) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hL := hD.mem_thetaComponentsAt
  have hc3 := hD.orderOf_c
  obtain ⟨P, hP⟩ := CFSG.ABGLocalTools.exists_isSylowOf 3
    (Subgroup.normalizer (E : Set G) ⊓ Subgroup.normalizer (Subgroup.zpowers c : Set G))
  have hPW : P ≤ Subgroup.normalizer (E : Set G) := hP.le.trans inf_le_left
  have hPN : P ≤ Subgroup.normalizer (L : Set G) :=
    le_normalizer_of_mem_thetaComponentsAt h45 h.toTheoremFourHyp hc3 hL hP.isPGroup
      (hP.le.trans inf_le_right)
  have hEH : E ≤ Subgroup.normalizer (Subgroup.zpowers c : Set G) := fun e he =>
    Sec13.centralizer_le_normalizer_zpowers c
      (Subgroup.mem_centralizer_singleton_iff.mpr (hD.comm he hD.mem_E))
  have hEP : E ≤ P := le_of_isSylowOf_of_le_normalizer hP (le_inf Subgroup.le_normalizer hEH)
    inf_le_left hD.isPGroup
  have hperf : commutator (L ⧸ aschbacherSolvableCore 3 L) = ⊤ := by
    have h1 := (isQuasisimple_thetaQuot_of_mem hL).1
    rwa [Group.isPerfect_def] at h1
  have hev := KFacts.two_dvd_card_of_item122_type (Or.inr hty)
  have hup := autIn_le_transvectionGroup_of_tc hD hty hP.isPGroup hPN hEP hPW
  have hlow := hD.nine_le_card_autIn h.partTwoF_eq hperf hev hP
  obtain ⟨e₁, he₁, e₂, he₂, h₁, h₂⟩ := hD.exists_basis
  have hT := card_transvectionGroup_le hD.mem_E he₁ he₂ (hD.closure_eq he₁ he₂ h₁ h₂) hc3
  have hPaut : Sec4.autIn P E = transvectionGroup E ⟨c, hD.mem_E⟩ :=
    Subgroup.eq_of_le_of_card_ge hup (hT.trans hlow)
  have hP9 : Nat.card (Sec4.autIn P E) = 9 :=
    le_antisymm ((Subgroup.card_le_of_le hup).trans hT) hlow
  have hE27 : Nat.card E = 3 ^ 3 := by rw [hD.isE27.2]; norm_num
  obtain ⟨V, _, _, hV, ⟨f⟩⟩ := exists_coords_module hD.isE27.1 hE27
  exact normalizer_le_of_autIn_eq hD.mem_E hD.ne_one hP hPaut hP9 hV f

end CFSG.RankThree.PartTwo.Sec12.Item125Diag
