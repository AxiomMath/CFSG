module

public import CFSG.Quasithin.Vol2.GoldschmidtF431U42AutP5bE16
public import CFSG.Quasithin.Vol2.GoldschmidtF431U42AutP5bVA

public section

namespace CFSG.Quasithin.H13.F431.U42Aut

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Open U42F431
open CFSG.Quasithin.H13.F431.U42 (P45)

theorem e16_good {K : Subgroup Ah}
    (hKT : K ≤ That) (hcard : 16 ≤ Nat.card K) (hab : ∀ a ∈ K, ∀ b ∈ K, a * b = b * a)
    (hsq : ∀ a ∈ K, a * a = 1) (hKV : ¬ K ≤ VA) : ∃ r ∈ K, IsGoodInv r := by
  by_contra hno
  push Not at hno
  have hsq' : ∀ a ∈ K, ∀ {l : PL}, RepL l (a : P45) → comp l l = idL := by
    intro a ha l hl
    refine repL_unique (repL_mul hl hl) ?_
    have : (a : P45) * (a : P45) = 1 := congrArg Subtype.val (hsq a ha)
    rw [this]
    exact repL_one 45
  by_cases hS : K ≤ TAh
  · obtain ⟨a, haK, haV⟩ : ∃ a ∈ K, a ∉ VA := by
      by_contra h
      push Not at h
      exact hKV fun a ha => h a ha
    obtain ⟨la, hla, hrepa⟩ := exists_Tl_of_mem_TAh (hS haK)
    have hlaV : la ∉ Vl := fun h => haV ((mem_VA_iff a).2 ⟨la, h, hrepa⟩)
    have hlt := e1_check la hla (hsq' a haK hrepa) hlaV
    have hle : Nat.card K ≤
        (Tl.filter fun m => comp m m == idL && comp m la == comp la m).length := by
      refine card_le_length_of_reps K fun k hk => ?_
      obtain ⟨lk, hlk, hrepk⟩ := exists_Tl_of_mem_TAh (hS hk)
      refine ⟨lk, List.mem_filter.2 ⟨hlk, ?_⟩, hrepk⟩
      have hc : comp lk la = comp la lk := by
        have h1 := repL_mul hrepk hrepa
        have h2 := repL_mul hrepa hrepk
        have : ((k : Ah) : P45) * (a : P45) = (a : P45) * ((k : Ah) : P45) :=
          congrArg Subtype.val (hab k hk a haK)
        rw [this] at h1
        exact (repL_unique h2 h1).symm
      simp only [Bool.and_eq_true, beq_iff_eq]
      exact ⟨hsq' k hk hrepk, hc⟩
    omega
  · obtain ⟨w, hwK, hwS⟩ : ∃ w ∈ K, w ∉ TAh := by
      by_contra h
      push Not at h
      exact hS fun a ha => h a ha
    have hwT : w ∈ That := hKT hwK
    have hwY : w ∉ Yh := fun h => hwS ⟨hwT, h⟩
    have hw1 : w ≠ 1 := fun h => hwY (h ▸ Yh.one_mem)
    rcases outer_inv_type hwT (hsq w hwK) hw1 hwY with hgood | ⟨k, hk, hrepw, hk3⟩
    · exact hno w hwK hgood
    have hlw : invL k ∈ El := mem_El hk hk3
    have hsw : signA w = -1 := (signA_eq_neg_one_iff w).2 hwY
    have : Yh.Normal := Yh_normal
    have hL8 : 8 ≤ Nat.card (Yh ⊓ K : Subgroup Ah) := by
      have h := Subgroup.relIndex_mul_card (H := Yh) (K := K)
      have hdvd : Yh.relIndex K ∣ Yh.index := Subgroup.relIndex_dvd_index_of_normal Yh K
      rw [index_Yh] at hdvd
      have : Yh.relIndex K ≤ 2 := Nat.le_of_dvd (by norm_num) hdvd
      by_contra hlt
      push Not at hlt
      have : Yh.relIndex K * Nat.card (Yh ⊓ K : Subgroup Ah) ≤ 2 * 7 :=
        Nat.mul_le_mul this (by omega)
      omega
    have hsub : ∀ s ∈ (Yh ⊓ K : Subgroup Ah), ∃ l ∈ Xw (invL k), RepL l (s : P45) := by
      rintro s ⟨hsY, hsK⟩
      obtain ⟨ls, hls, hreps⟩ := exists_Tl_of_mem_TAh (⟨hKT hsK, hsY⟩ : s ∈ TAh)
      refine ⟨ls, List.mem_filter.2 ⟨hls, ?_⟩, hreps⟩
      have hc : comp ls (invL k) = comp (invL k) ls := by
        have h1 := repL_mul hreps hrepw
        have h2 := repL_mul hrepw hreps
        have : ((s : Ah) : P45) * (w : P45) = (w : P45) * ((s : Ah) : P45) :=
          congrArg Subtype.val (hab s hsK w hwK)
        rw [this] at h1
        exact (repL_unique h2 h1).symm
      have hsK1 : signA s = 1 := (signA_eq_one_iff s).2 hsY
      have hu : s * w ∈ K := K.mul_mem hsK hwK
      have hsu : signA (s * w) = -1 := by rw [map_mul, hsK1, hsw]; simp
      have huY : s * w ∉ Yh := fun h => by
        have := (signA_eq_one_iff _).2 h
        rw [hsu] at this
        exact absurd this (by decide)
      have hu1 : s * w ≠ 1 := fun h => huY (h ▸ Yh.one_mem)
      rcases outer_inv_type (hKT hu) (hsq _ hu) hu1 huY with hg | ⟨k', hk', hrep', hk3'⟩
      · exact absurd hg (hno _ hu)
      have hEl : comp ls (invL k) ∈ El := by
        have := mem_El hk' hk3'
        rwa [repL_unique hrep' (repL_mul hreps hrepw)] at this
      simp only [Bool.and_eq_true, beq_iff_eq]
      exact ⟨⟨hsq' s hsK hreps, hc⟩, List.elem_eq_true_of_mem hEl⟩
    obtain ⟨hlen, a, ha, b, hb, hnc⟩ := e2_check (invL k) hlw
    have hnd : (Xw (invL k)).Nodup := Tl_nodup.filter _
    have hclosed := closed_of_card_ge (Yh ⊓ K : Subgroup Ah) hnd hsub (by omega)
    exact hnc (hclosed a ha b hb)

end CFSG.Quasithin.H13.F431.U42Aut
