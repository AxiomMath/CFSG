module

public import CFSG.Quasithin.Vol2.Ch12Sec6P31WXG

public section

open scoped Pointwise

namespace CFSG.Quasithin.H13.P31X

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique CFSG.LieType.BorelTits S126 S126P31 Equiv
open scoped IsMulCommutative Pointwise

variable {G : Type} [Group G] [Finite G] {T V L V₁ Vp H K : Subgroup G} [IsMulCommutative ↥V]

omit [IsMulCommutative ↥V] in
theorem conjSub_mem_pair_gen (hH : Hyp126 G T L V) (h918 : HypF918 T V L V₁ Vp H K)
    (hP : StarProps (star H K)) {t₀ : G} (ht₀ : t₀ ∈ T)
    (ht₀K : t₀ ∉ Subgroup.normalizer (K : Set G)) {t : G} (ht : t ∈ T) :
    conjSub t K = K ∨ conjSub t K = conjSub t₀ K := by
  have h := h918.toHypF98.toHypF91
  have hTH : T ≤ H := h.T_le_H
  have hKc : K ∈ cComp H := h918.K_cComp
  have hK₂c : conjSub t₀ K ∈ cComp H := L1233.conjSub_mem_cComp hKc (hTH ht₀)
  have hXc : conjSub t K ∈ cComp H := L1233.conjSub_mem_cComp hKc (hTH ht)
  by_contra hne
  push Not at hne
  obtain ⟨hne1, hne2⟩ := hne
  have hsK : IsSimpleGroup ↥(star H K) := hP.simple
  have hsK₂ : IsSimpleGroup ↥(star H (conjSub t₀ K)) := (starProps_conjSub hP (hTH ht₀)).simple
  have hsX : IsSimpleGroup ↥(star H (conjSub t K)) := (starProps_conjSub hP (hTH ht)).simple
  have hKK₂ : K ≠ conjSub t₀ K := fun he =>
    ht₀K (L1233.mem_normalizer_of_conjSub_eq he.symm)
  have hc12 := L1233.commute_star hKc hK₂c hKK₂ hsK hsK₂
  have hcX1 := L1233.commute_star hXc hKc hne1 hsX hsK
  have hcX2 := L1233.commute_star hXc hK₂c hne2 hsX hsK₂
  obtain ⟨A, hAK, hA⟩ := exists_card_three_of_dvd hP.three
  obtain ⟨B, hBK, hB⟩ := exists_card_three_of_dvd (starProps_conjSub hP (hTH ht₀)).three
  obtain ⟨C, hCX, hC⟩ := exists_card_three_of_dvd (starProps_conjSub hP (hTH ht)).three
  have hAB : A ≤ Subgroup.centralizer (B : Set (HStar H)) := fun a ha =>
    Subgroup.mem_centralizer_iff.2 fun b hb => (hc12 a (hAK ha) b (hBK hb)).symm
  have hAC : A ≤ Subgroup.centralizer (C : Set (HStar H)) := fun a ha =>
    Subgroup.mem_centralizer_iff.2 fun c hc => hcX1 c (hCX hc) a (hAK ha)
  have hBC : B ≤ Subgroup.centralizer (C : Set (HStar H)) := fun b hb =>
    Subgroup.mem_centralizer_iff.2 fun c hc => hcX2 c (hCX hc) b (hBK hb)
  have hi12 : star H K ⊓ star H (conjSub t₀ K) = ⊥ :=
    inf_eq_bot_of_commute hsK hP.nonab hc12
  have hsupC : star H K ⊔ star H (conjSub t₀ K) ≤
      Subgroup.centralizer (star H (conjSub t K) : Set (HStar H)) :=
    sup_le (fun a ha => Subgroup.mem_centralizer_iff.2 fun x hx => hcX1 x hx a ha)
      (fun b hb => Subgroup.mem_centralizer_iff.2 fun x hx => hcX2 x hx b hb)
  have hiX : star H (conjSub t K) ⊓ (star H K ⊔ star H (conjSub t₀ K)) = ⊥ :=
    inf_eq_bot_of_commute hsX (starProps_conjSub hP (hTH ht)).nonab
      fun x hx y hy => Subgroup.mem_centralizer_iff.1 (hsupC hy) x hx
  have hi : A ⊓ B = ⊥ := le_bot_iff.1 (hi12 ▸ inf_le_inf hAK hBK)
  have hi' : (A ⊔ B) ⊓ C = ⊥ := by
    refine le_bot_iff.1 (hiX ▸ ?_)
    rw [inf_comm]
    exact inf_le_inf hCX (sup_le_sup hAK hBK)
  exact false_of_three hH (pCoreOf_ne_bot h) hA hB hC hAB hAC hBC hi hi'

omit [IsMulCommutative ↥V] in
theorem commute_pair_gen (h918 : HypF918 T V L V₁ Vp H K) (hP : StarProps (star H K)) {t₀ : G}
    (ht₀ : t₀ ∈ T) (ht₀K : t₀ ∉ Subgroup.normalizer (K : Set G)) :
    (∀ x ∈ star H K, ∀ y ∈ star H (conjSub t₀ K), x * y = y * x) ∧
      star H K ⊓ star H (conjSub t₀ K) = ⊥ := by
  have hTH : T ≤ H := h918.toHypF98.toHypF91.T_le_H
  have hsK : IsSimpleGroup ↥(star H K) := hP.simple
  have hKK₂ : K ≠ conjSub t₀ K := fun he =>
    ht₀K (L1233.mem_normalizer_of_conjSub_eq he.symm)
  have hc := L1233.commute_star h918.K_cComp (L1233.conjSub_mem_cComp h918.K_cComp (hTH ht₀))
    hKK₂ hsK (starProps_conjSub hP (hTH ht₀)).simple
  exact ⟨hc, inf_eq_bot_of_commute hsK hP.nonab hc⟩

omit [IsMulCommutative ↥V] in
theorem conjClosure_eq_sup_gen (hH : Hyp126 G T L V) (h918 : HypF918 T V L V₁ Vp H K)
    (hP : StarProps (star H K)) {t₀ : G} (ht₀ : t₀ ∈ T)
    (ht₀K : t₀ ∉ Subgroup.normalizer (K : Set G)) : conjClosure K T = K ⊔ conjSub t₀ K := by
  apply le_antisymm
  · refine conjClosure_le fun t ht k hk => ?_
    have hm : t * k * t⁻¹ ∈ conjSub t K := mul_mem_conjSub hk
    rcases conjSub_mem_pair_gen hH h918 hP ht₀ ht₀K ht with h | h
    · rw [h] at hm
      exact Subgroup.mem_sup_left hm
    · rw [h] at hm
      exact Subgroup.mem_sup_right hm
  · refine sup_le (le_conjClosure K T) fun x hx => ?_
    have h2 := mem_conjClosure ht₀ (mem_conjSub.1 hx)
    simpa [mul_assoc] using h2

omit [IsMulCommutative ↥V] in
theorem star_conjClosure_eq_sup_gen (hH : Hyp126 G T L V) (h918 : HypF918 T V L V₁ Vp H K)
    (hP : StarProps (star H K)) {t₀ : G} (ht₀ : t₀ ∈ T)
    (ht₀K : t₀ ∉ Subgroup.normalizer (K : Set G)) :
    star H (conjClosure K T) = star H K ⊔ star H (conjSub t₀ K) := by
  have hTH : T ≤ H := h918.toHypF98.toHypF91.T_le_H
  rw [conjClosure_eq_sup_gen hH h918 hP ht₀ ht₀K, star_sup (le_of_mem_cComp h918.K_cComp)
    (le_of_mem_cComp (L1233.conjSub_mem_cComp h918.K_cComp (hTH ht₀)))]

end CFSG.Quasithin.H13.P31X
