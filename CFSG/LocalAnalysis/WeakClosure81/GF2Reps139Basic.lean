module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps139Defs

public section

namespace CFSG.LocalAnalysis.WeakClosure81.GF2Reps139

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
open CFSG.Blueprint (LieModel)
open scoped commutatorElement Pointwise Matrix

variable {W : Type} [CommGroup W] [Finite W] {G X D : Subgroup (MulAut W)} {s : MulAut W}
  {Y : Subgroup W} {n : ℕ}

theorem Std139.exists_gen (hw2 : ∀ w : W, w ^ 2 = 1) (S : Std139 G X D s Y n) :
    ∃ x : MulAut W, X = Subgroup.zpowers x ∧ x ^ 3 = 1 ∧ x ≠ 1 ∧ fixV X = ⊥ ∧
      s * x * s⁻¹ = x⁻¹ := by
  have hXne : X ≠ ⊥ := by
    intro hbot
    have hXc := S.Xcard
    rw [hbot, Subgroup.card_bot] at hXc
    omega
  have hfixX : fixV X = ⊥ := fixV_eq_bot_of_irreducible S.irr S.XG S.Xnorm hXne
  have hXcard' : Nat.card ↥X = 3 := S.Xcard
  letI : Fintype ↥X := Fintype.ofFinite _
  have hXcardF : Fintype.card ↥X = 3 := by
    rw [← Nat.card_eq_fintype_card, hXcard']
  obtain ⟨xX, hxXne⟩ : ∃ xX : ↥X, xX ≠ 1 := by
    refine Fintype.exists_ne_of_one_lt_card ?_ (1 : ↥X)
    rw [hXcardF]
    norm_num
  let x : MulAut W := xX
  have hxX : x ∈ X := xX.2
  have hx_ne : x ≠ 1 := by
    intro h
    exact hxXne (Subtype.ext h)
  have hx_ord_dvd : orderOf x ∣ 3 := by
    have h : orderOf xX ∣ 3 := by
      have h2 := orderOf_dvd_natCard xX
      rwa [Nat.card_eq_fintype_card, hXcardF] at h2
    rwa [← Subgroup.orderOf_coe xX] at h
  have hx_ord3 : orderOf x = 3 := by
    rcases (by norm_num : Nat.Prime 3).eq_one_or_self_of_dvd (orderOf x) hx_ord_dvd with
      h1 | h3
    · exact absurd (orderOf_eq_one_iff.mp h1) hx_ne
    · exact h3
  have hx3 : x ^ 3 = 1 := by
    rw [← hx_ord3]
    exact pow_orderOf_eq_one x
  have hxgen : X = Subgroup.zpowers x := by
    symm
    refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hxX) ?_
    rw [Nat.card_zpowers, hx_ord3, S.Xcard]
  have hmem : s * x * s⁻¹ ∈ X := S.Xnorm s S.sG x hxX
  have hsx : s * x * s⁻¹ ≠ x := by
    intro hconj
    exact S.s_not_cent
      (CFSG.LocalAnalysis.WeakClosure81.mem_centralizer_of_conj_eq_self hxgen hconj)
  have hsq : s * x * s⁻¹ = x ^ 2 :=
    CFSG.LocalAnalysis.WeakClosure81.conj_eq_sq_of_zpowers_three_of_mem hxgen hx_ord3 hmem hsx
  have hx2inv : x ^ 2 = x⁻¹ := by
    have h : x ^ 2 * x = 1 := by
      calc x ^ 2 * x = x ^ 3 := by group
        _ = 1 := hx3
    exact mul_eq_one_iff_eq_inv.mp h
  exact ⟨x, hxgen, hx3, hx_ne, hfixX, hsq.trans hx2inv⟩

theorem xstable_two_le_rk (hw2 : ∀ w : W, w ^ 2 = 1) {X : Subgroup (MulAut W)}
    (hfix : fixV X = ⊥) {A : Subgroup W} (hA : StableUnder X A) (hA0 : A ≠ ⊥) :
    2 ≤ rk ↥A := by
  by_contra h
  have hlt : rk ↥A < 2 := not_le.1 h
  have hrk0 : rk ↥A ≠ 0 := by
    intro h0
    exact hA0 ((rk_eq_zero_iff hw2).mp h0)
  have hrk1 : rk ↥A = 1 := by omega
  have hcard : Nat.card ↥A = 2 := by
    rw [card_eq_two_pow hw2 A, hrk1, pow_one]
  obtain ⟨a, ha1, huniq⟩ := (Nat.card_eq_two_iff' (1 : ↥A)).mp hcard
  have hfix_a : (a : W) ∈ fixV X := by
    rw [mem_fixV]
    intro x hx
    have hmem : x (a : W) ∈ A := hA x hx a a.2
    have hne : (⟨x (a : W), hmem⟩ : ↥A) ≠ 1 := by
      intro hh
      have hxa : x (a : W) = 1 := congrArg Subtype.val hh
      have h1 : (a : W) = 1 := x.injective (by rw [hxa, map_one])
      exact ha1 (Subtype.ext h1)
    exact congrArg Subtype.val (huniq ⟨x (a : W), hmem⟩ hne)
  rw [hfix] at hfix_a
  exact ha1 (Subtype.ext (Subgroup.mem_bot.mp hfix_a))

theorem xstable_two_le_mQuot (hw2 : ∀ w : W, w ^ 2 = 1) {X : Subgroup (MulAut W)}
    (hX : Nat.card X = 3) (hfix : fixV X = ⊥)
    {A B : Subgroup W} (hA : StableUnder X A) (hB : StableUnder X B) (hBA : B < A) :
    2 ≤ E3.mQuot A B := by
  by_contra h
  have hmq_lt : E3.mQuot A B < 2 := not_le.1 h
  have hV : IsPGroup 2 A := (isPGroup_two_of_sq_eq_one hw2).to_subgroup A
  have hmq0 : E3.mQuot A B ≠ 0 := by
    intro h0
    exact (ne_of_lt hBA) ((E3.mQuot_eq_zero_iff hV hBA.le).mp h0)
  have hmq1 : E3.mQuot A B = 1 := by omega
  have hrel : B.relIndex A = 2 := by
    rw [E3.relIndex_eq_two_pow hV B, hmq1]
    norm_num
  have hI : (B.subgroupOf A).index = 2 := hrel
  have hnot_le : ¬ (A : Set W) ⊆ (B : Set W) := by
    intro hsub
    exact (ne_of_lt hBA) (le_antisymm hBA.le hsub)
  obtain ⟨a, haA, ha_notB⟩ := Set.not_subset.mp hnot_le
  have hXcard' : Nat.card ↥X = 3 := hX
  letI : Fintype ↥X := Fintype.ofFinite _
  have hXcardF : Fintype.card ↥X = 3 := by
    rw [← Nat.card_eq_fintype_card, hXcard']
  obtain ⟨xX, hxXne⟩ : ∃ xX : ↥X, xX ≠ 1 := by
    refine Fintype.exists_ne_of_one_lt_card ?_ (1 : ↥X)
    rw [hXcardF]
    norm_num
  let x : MulAut W := xX
  have hxX : x ∈ X := xX.2
  have hx_ne : x ≠ 1 := by
    intro hx1
    exact hxXne (Subtype.ext hx1)
  have hx_ord_dvd : orderOf x ∣ 3 := by
    have h2 : orderOf xX ∣ 3 := by
      have h3 := orderOf_dvd_natCard xX
      rwa [Nat.card_eq_fintype_card, hXcardF] at h3
    rwa [← Subgroup.orderOf_coe xX] at h2
  have hx_ord3 : orderOf x = 3 := by
    rcases (by norm_num : Nat.Prime 3).eq_one_or_self_of_dvd (orderOf x) hx_ord_dvd with
      h1 | h3
    · exact absurd (orderOf_eq_one_iff.mp h1) hx_ne
    · exact h3
  have hx3 : x ^ 3 = 1 := by
    rw [← hx_ord3]
    exact pow_orderOf_eq_one x
  have hxgen : X = Subgroup.zpowers x := by
    symm
    refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hxX) ?_
    rw [Nat.card_zpowers, hx_ord3, hX]
  have hya1 : x a ∉ B := by
    intro hb
    have h := hB x⁻¹ (X.inv_mem hxX) (x a) hb
    exact ha_notB (by simpa [MulAut.inv_apply_self] using h)
  have hya2 : (x ^ 2) a ∉ B := by
    intro hb
    have h := hB (x ^ 2)⁻¹ (X.inv_mem (X.pow_mem hxX 2)) ((x ^ 2) a) hb
    exact ha_notB (by simpa [MulAut.inv_apply_self] using h)
  have hcoset : ∀ y ∈ X, y a ∉ B → y a * a⁻¹ ∈ B := by
    intro y hy hya
    have hyA : y a ∈ A := hA y hy a haA
    have hu : (⟨y a, hyA⟩ : ↥A) ∉ B.subgroupOf A := fun hh => hya hh
    have hv : (⟨a, haA⟩ : ↥A) ∉ B.subgroupOf A := fun hh => ha_notB hh
    have hmem : (⟨y a, hyA⟩ : ↥A) * (⟨a, haA⟩ : ↥A)⁻¹ ∈ B.subgroupOf A := by
      rw [Subgroup.mul_mem_iff_of_index_two hI]
      constructor
      · intro hh
        exact absurd hh hu
      · intro hh
        exact absurd (inv_mem_iff.mp hh) hv
    exact hmem
  have hb1 : x a * a⁻¹ ∈ B := hcoset x hxX hya1
  have hb2 : x (x a) * a⁻¹ ∈ B := by
    have h := hcoset (x ^ 2) (X.pow_mem hxX 2) hya2
    simpa [pow_two, MulAut.mul_apply] using h
  have ha2B : a * a ∈ B := by
    have h := Subgroup.mul_self_mem_of_index_two hI (⟨a, haA⟩ : ↥A)
    exact h
  set c : W := a * x a * x (x a) with hc
  have hx3a : x (x (x a)) = a := by
    have h := congrArg (fun f : MulAut W => f a) hx3
    simpa [pow_succ, pow_two, MulAut.mul_apply] using h
  have hxc : x c = c := by
    simp only [hc, map_mul]
    rw [hx3a]
    ac_rfl
  have hcfix : c ∈ fixV X := by
    rw [hxgen]
    exact mem_fixV_zpowers_iff.mpr hxc
  have hc1 : c = 1 := by
    have h := hcfix
    rw [hfix] at h
    exact Subgroup.mem_bot.mp h
  have hcB : c * a⁻¹ ∈ B := by
    have halg : c * a⁻¹ = (a * a) * (x a * a⁻¹) * (x (x a) * a⁻¹) := by
      rw [inv_eq_self_of_sq_eq_one hw2 a]
      have haa : a * a = 1 := by
        have h := hw2 a
        rwa [pow_two] at h
      rw [hc, haa]
      simp only [one_mul]
      ac_rfl
    rw [halg]
    exact B.mul_mem (B.mul_mem ha2B hb1) hb2
  have ha_invB : a⁻¹ ∈ B := by
    have h := hcB
    rwa [hc1, one_mul] at h
  exact ha_notB (by simpa using B.inv_mem ha_invB)

theorem Std139.fixV_eq_axis (hw2 : ∀ w : W, w ^ 2 = 1) (S : Std139 G X D s Y n) {e : MulAut W}
    (he : e ∈ D) (he1 : e ≠ 1) : fixV (Subgroup.zpowers e) = Y := by
  have hYC : Y ≤ fixV (Subgroup.zpowers e) := by
    intro y hy
    exact mem_fixV_zpowers_iff.mpr (mem_fixV.mp (S.YD hy) e he)
  have hCne : fixV (Subgroup.zpowers e) ≠ ⊤ := by
    intro htop
    apply he1
    ext w
    have hw : w ∈ fixV (Subgroup.zpowers e) := by
      rw [htop]
      exact Subgroup.mem_top w
    exact mem_fixV_zpowers_iff.mp hw
  have hCinv : StableUnder X (fixV (Subgroup.zpowers e)) := by
    intro y hy c hc
    rw [mem_fixV_zpowers_iff] at hc ⊢
    calc e (y c) = (e * y) c := rfl
      _ = (y * e) c := by rw [S.DX e he y hy]
      _ = y (e c) := rfl
      _ = y c := by rw [hc]
  by_cases hlt : Y < fixV (Subgroup.zpowers e)
  · exfalso
    have hXne : X ≠ ⊥ := by
      intro hbot
      have hXc := S.Xcard
      rw [hbot, Subgroup.card_bot] at hXc
      omega
    have hfixX : fixV X = ⊥ := fixV_eq_bot_of_irreducible S.irr S.XG S.Xnorm hXne
    have hmqCY : 2 ≤ E3.mQuot (fixV (Subgroup.zpowers e)) Y :=
      xstable_two_le_mQuot hw2 S.Xcard hfixX hCinv S.Yinv hlt
    have hV : IsPGroup 2 (⊤ : Subgroup W) := (isPGroup_two_of_sq_eq_one hw2).to_subgroup ⊤
    have hmqWC : 1 ≤ E3.mQuot ⊤ (fixV (Subgroup.zpowers e)) := by
      have hne0 : E3.mQuot ⊤ (fixV (Subgroup.zpowers e)) ≠ 0 := by
        intro h0
        exact hCne ((E3.mQuot_eq_zero_iff hV le_top).mp h0)
      omega
    have hadd : E3.mQuot ⊤ Y =
        E3.mQuot (fixV (Subgroup.zpowers e)) Y + E3.mQuot ⊤ (fixV (Subgroup.zpowers e)) :=
      E3.mQuot_add hlt.le le_top
    have hYrk : rkIdx Y = E3.mQuot ⊤ Y := by
      rw [E3.mQuot, rkIdx, Subgroup.relIndex_top_right]
    have hY2 : rkIdx Y = 2 := S.Yrk
    omega
  · by_contra hne
    exact hlt (lt_of_le_of_ne hYC (Ne.symm hne))

theorem Std139.commSub_axis (hw2 : ∀ w : W, w ^ 2 = 1) (S : Std139 G X D s Y n) {e : MulAut W}
    (he : e ∈ D) (he1 : e ≠ 1) :
    rk ↥(commSub ⊤ (Subgroup.zpowers e)) = 2 ∧ commSub ⊤ (Subgroup.zpowers e) ≤ Y ∧
      StableUnder X (commSub ⊤ (Subgroup.zpowers e)) := by
  have he2 : e ^ 2 = 1 := S.elem.2 e he
  refine ⟨?_, ?_, ?_⟩
  · rw [← commV_eq_commSub, ← rkIdx_fixV_zpowers e, Std139.fixV_eq_axis hw2 S he he1, S.Yrk]
  · have h := commSub_zpowers_le_inf_fixV hw2 he2 (W := ⊤)
      (fun _ _ w _ => Subgroup.mem_top w)
    rw [top_inf_eq, Std139.fixV_eq_axis hw2 S he he1] at h
    exact h
  · have hcommY : ∀ y ∈ Subgroup.zpowers e, ∀ b ∈ X, y * b = b * y := by
      have heC : e ∈ Subgroup.centralizer (X : Set (MulAut W)) := by
        rw [Subgroup.mem_centralizer_iff]
        intro b hb
        exact (S.DX e he b hb).symm
      have hle : Subgroup.zpowers e ≤ Subgroup.centralizer (X : Set (MulAut W)) :=
        Subgroup.zpowers_le.mpr heC
      intro y hy b hb
      exact ((Subgroup.mem_centralizer_iff.mp (hle hy)) b hb).symm
    exact B1.commSub_invariant_of_commute (V := W) (Y := Subgroup.zpowers e) (B := X) (M := ⊤)
      hcommY (fun b _ m _ => Subgroup.mem_top m)

end CFSG.LocalAnalysis.WeakClosure81.GF2Reps139
