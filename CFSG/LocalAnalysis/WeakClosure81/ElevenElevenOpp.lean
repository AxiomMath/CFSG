module

public import CFSG.LocalAnalysis.WeakClosure81.ElevenTenDecomp
public import CFSG.LocalAnalysis.WeakClosure81.ElevenElevenLin

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Quasithin.E3 CFSG.Open CFSG.LocalAnalysis.UniquenessCase.PartTwo
  CFSG.LocalAnalysis.UniquenessCase.UC22 CFSG.RankThree.PartOne CFSG.CGT.PushingUp
  CFSG.CGT.PushingUpLit Subgroup
open scoped commutatorElement Pointwise
open CFSG.QuasithinUnique.Lin2 (IsHallTwoPrimeOf ActsRegularlyOn nonIdentity)

variable {G : Type} [Group G] [Finite G]

theorem opp_le_centralizer_of_no_involution {M V W : Subgroup G} (hV : IsElemAbelian 2 V)
    (hMV : M ≤ Subgroup.normalizer (V : Set G))
    (h : ∀ t ∈ autI hV M, orderOf t = 2 → ∃ w : IntMod V hV, w.val ∈ W ∧ t w ≠ w) :
    Opp 2 (M ⊓ Subgroup.centralizer (W : Set G)) ≤ Subgroup.centralizer (V : Set G) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  unfold Opp
  rw [pElementSubgroup, Subgroup.closure_le]
  rintro x ⟨hxMW, k, hk⟩
  obtain ⟨hxM, hxW⟩ := Subgroup.mem_inf.1 hxMW
  by_cases hxc : x ∈ Subgroup.centralizer (V : Set G)
  · exact hxc
  · exfalso
    have hxN : x ∈ Subgroup.normalizer (V : Set G) := hMV hxM
    set φ : MulAut (IntMod V hV) := convI hV ⟨x, hxN⟩ with hφdef
    have hφM : φ ∈ autI hV M := convI_mem_autI hV hxM hxN
    have hφ1 : φ ≠ 1 := by
      intro h1
      exact hxc ((convI_eq_one_iff hV ⟨x, hxN⟩).1 h1)
    have hord_dvd : orderOf φ ∣ 2 ^ k := by
      have h1 := orderOf_map_dvd (convI hV) (⟨x, hxN⟩ : Subgroup.normalizer (V : Set G))
      have hg_ord : orderOf (⟨x, hxN⟩ : Subgroup.normalizer (V : Set G)) = orderOf x :=
        (Subgroup.orderOf_coe (⟨x, hxN⟩ : Subgroup.normalizer (V : Set G))).symm
      rwa [hg_ord, hk] at h1
    obtain ⟨j, hj, hjeq⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hord_dvd
    have hj0 : j ≠ 0 := by
      rintro rfl
      rw [pow_zero] at hjeq
      exact hφ1 (orderOf_eq_one_iff.1 hjeq)
    have hev : Even (orderOf φ) := by
      rw [hjeq]
      exact (Nat.even_pow.2 ⟨even_two, hj0⟩)
    have hord0 : orderOf φ ≠ 0 := (orderOf_pos φ).ne'
    set t := φ ^ (orderOf φ / 2) with htdef
    have ht2 : orderOf t = 2 := orderOf_pow_orderOf_div hord0 (even_iff_two_dvd.1 hev)
    have htM : t ∈ autI hV M := Subgroup.pow_mem _ hφM _
    obtain ⟨w, hwW, hw⟩ := h t htM ht2
    apply hw
    have hφw : φ w = w := by
      apply IntMod.val_injective
      rw [hφdef, convI_apply_val]
      have := Subgroup.mem_centralizer_iff.1 hxW w.val hwW
      calc x * w.val * x⁻¹ = (w.val * x) * x⁻¹ := by rw [this]
        _ = w.val := mul_inv_cancel_right _ _
    have hpow : ∀ m : ℕ, (φ ^ m) w = w := by
      intro m
      induction m with
      | zero => simp
      | succ m ih => rw [pow_succ, MulAut.mul_apply, hφw, ih]
    exact hpow _


theorem odd_card_autI_of_opp_le {M V : Subgroup G} (hV : IsElemAbelian 2 V)
    (hMV : M ≤ Subgroup.normalizer (V : Set G))
    (h : Opp 2 M ≤ Subgroup.centralizer (V : Set G)) : Odd (Nat.card (autI hV M)) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hodd
  rw [Nat.not_odd_iff_even] at hodd
  have : Finite (MulAut (IntMod V hV)) := Finite.of_injective
    (fun φ : MulAut (IntMod V hV) => (φ : IntMod V hV → IntMod V hV)) DFunLike.coe_injective
  obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' (G := autI hV M) 2 (even_iff_two_dvd.1 hodd)
  have ht' : orderOf (t : MulAut (IntMod V hV)) = 2 := by rw [Subgroup.orderOf_coe]; exact ht
  obtain ⟨g, hgM, hg⟩ := (mem_autI hV).1 t.2
  have hg0 : orderOf g ≠ 0 := (orderOf_pos g).ne'
  obtain ⟨a, b, hb, hab⟩ := Nat.exists_eq_two_pow_mul_odd hg0
  have hbne : b ≠ 0 := by
    rintro rfl
    have := Nat.odd_iff.1 hb
    omega
  have hgb : orderOf (g ^ b) = 2 ^ a := by
    rw [orderOf_pow_of_dvd hbne (by rw [hab]; exact Dvd.intro_left _ rfl), hab]
    rw [Nat.mul_div_cancel _ (Nat.pos_of_ne_zero hbne)]
  have hmem : ((g ^ b : Subgroup.normalizer (V : Set G)) : G) ∈ Opp 2 M := by
    unfold Opp
    rw [pElementSubgroup]
    refine Subgroup.subset_closure ⟨?_, a, ?_⟩
    · exact (Subgroup.pow_mem M hgM b)
    · rw [← Subgroup.orderOf_coe] at hgb
      exact hgb
  have h1 : convI hV (g ^ b) = 1 := (convI_eq_one_iff hV _).2 (h hmem)
  rw [map_pow, hg] at h1
  obtain ⟨c, hc⟩ := hb
  have htb : (t : MulAut (IntMod V hV)) ^ b = t := by
    have ht2 : (t : MulAut (IntMod V hV)) ^ 2 = 1 := by rw [← ht']; exact pow_orderOf_eq_one _
    rw [hc, pow_succ, pow_mul, ht2, one_pow, one_mul]
  rw [htb] at h1
  have : orderOf (t : MulAut (IntMod V hV)) = 1 := by rw [h1]; exact orderOf_one
  omega


theorem exists_conj_index {M V Q U L X : Subgroup G} (hV : IsElemAbelian 2 V)
    (hd : Eleven11Data M V Q U L X) {s : ℕ} {Y : Fin s → Subgroup (MulAut (IntMod V hV))}
    {Vs : Fin s → Subgroup (IntMod V hV)} {i₀ : Fin s}
    (hdec : Eleven11Decomp hV M X U s Y Vs i₀) {g : G} (hgM : g ∈ M)
    (hgY : ¬ autI hV X = Y i₀ →
      (Y i₀).map (MulAut.conj (convI hV ⟨g, hd.setting.normal hgM⟩)).toMonoidHom = Y i₀) :
    ∃ j₀ : Fin s,
      (Y i₀).map (MulAut.conj (convI hV ⟨g, hd.setting.normal hgM⟩)⁻¹).toMonoidHom = Y j₀ ∧
        (¬ autI hV X = Y i₀ → j₀ = i₀) := by
  obtain ⟨⟨hYsup, hYind, hcommY⟩, -, ⟨hVsup, hVind, hVi⟩, ⟨hperm, htrans⟩, -⟩ := hdec.body
  have hgN := hd.setting.normal hgM
  have hφ : convI hV ⟨g, hgN⟩ ∈ autI hV M := convI_mem_autI hV hgM hgN
  obtain ⟨j₀, hj₀⟩ := hperm _ ((autI hV M).inv_mem hφ) i₀
  refine ⟨j₀, hj₀, fun hX => ?_⟩
  have h1 := hgY hX
  have h2 : (Y i₀).map (MulAut.conj (convI hV ⟨g, hgN⟩)⁻¹).toMonoidHom = Y i₀ := by
    conv_lhs => rw [← h1]
    rw [Subgroup.map_map]
    have : (MulAut.conj (convI hV ⟨g, hgN⟩)⁻¹).toMonoidHom.comp
        (MulAut.conj (convI hV ⟨g, hgN⟩)).toMonoidHom = MonoidHom.id _ := by
      ext x
      simp [MulAut.conj_apply, mul_assoc]
    rw [this, Subgroup.map_id]
  rw [h2] at hj₀
  exact (hYind.injective hdec.Y_ne_bot hj₀).symm


theorem vs_val_mem_inf {M V Q U L X : Subgroup G} (hV : IsElemAbelian 2 V)
    (hd : Eleven11Data M V Q U L X) {s : ℕ} {Y : Fin s → Subgroup (MulAut (IntMod V hV))}
    {Vs : Fin s → Subgroup (IntMod V hV)} {i₀ : Fin s}
    (hdec : Eleven11Decomp hV M X U s Y Vs i₀) {g : G} (hgM : g ∈ M) {j₀ : Fin s}
    (hj₀ : (Y i₀).map (MulAut.conj (convI hV ⟨g, hd.setting.normal hgM⟩)⁻¹).toMonoidHom = Y j₀)
    {k : Fin s} (hk₁ : k ≠ i₀) (hk₂ : k ≠ j₀) {v : IntMod V hV} (hv : v ∈ Vs k) :
    v.val ∈ U ⊓ conjSubgroup U g := by
  obtain ⟨⟨hYsup, hYind, hcommY⟩, -, ⟨hVsup, hVind, hVi⟩, ⟨hperm, htrans⟩, -⟩ := hdec.body
  have hgN := hd.setting.normal hgM
  set φ := convI hV ⟨g, hgN⟩ with hφdef
  have hXle : autI hV X ≤ Y i₀ := by
    rcases hdec.case with h | ⟨-, h, -⟩
    · exact h.le
    · exact h
  have h1 : Vs k ≤ fixV (Y i₀) := vs_le_fixV_of_ne hVind (fun i => (hVi i).1) hcommY hk₁.symm
  have h3 : Vs k ≤ fixV (Y j₀) := vs_le_fixV_of_ne hVind (fun i => (hVi i).1) hcommY hk₂.symm
  refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
  · have hvfix : v ∈ fixV (autI hV X) :=
      mem_fixV.2 fun x hx => mem_fixV.1 (h1 hv) x (hXle hx)
    rw [← hdec.fixV_map]
    exact ⟨v, hvfix, E3.valHom_apply hV v⟩
  · rw [mem_conjSubgroup_iff]
    have hφvfix : φ v ∈ fixV (autI hV X) := by
      refine mem_fixV.2 fun ξ hξ => ?_
      have hmem : φ⁻¹ * ξ * φ⁻¹⁻¹ ∈ Y j₀ := by
        rw [← hj₀]
        exact ⟨ξ, hXle hξ, rfl⟩
      have h2 := mem_fixV.1 (h3 hv) _ hmem
      rw [inv_inv, MulAut.mul_apply, MulAut.mul_apply] at h2
      have h4 := congrArg (fun w => φ w) h2
      simp only [MulAut.apply_inv_self] at h4
      exact h4
    have hval : g * v.val * g⁻¹ = (φ v).val := by rw [hφdef, convI_apply_val]
    rw [hval, ← hdec.fixV_map]
    exact ⟨φ v, hφvfix, E3.valHom_apply hV _⟩


theorem eleven_eleven_opp {M V Q U L X : Subgroup G} (hV : IsElemAbelian 2 V)
    (hd : Eleven11Data M V Q U L X) {s : ℕ} {Y : Fin s → Subgroup (MulAut (IntMod V hV))}
    {Vs : Fin s → Subgroup (IntMod V hV)} {i₀ : Fin s}
    (hdec : Eleven11Decomp hV M X U s Y Vs i₀) {g : G} (hgM : g ∈ M)
    (hgY : ¬ autI hV X = Y i₀ →
      (Y i₀).map (MulAut.conj (convI hV ⟨g, hd.setting.normal hgM⟩)).toMonoidHom = Y i₀) :
    Opp 2 (M ⊓ Subgroup.centralizer ((U ⊓ conjSubgroup U g : Subgroup G) : Set G)) ≤
      Subgroup.centralizer (V : Set G) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine opp_le_centralizer_of_no_involution hV hd.setting.normal ?_
  intro t ht ht2
  by_contra hcon
  have hfixall : ∀ w : IntMod V hV, w.val ∈ U ⊓ conjSubgroup U g → t w = w := by
    intro w hw
    by_contra hne
    exact hcon ⟨w, hw, hne⟩
  obtain ⟨j₀, hj₀, hj₀'⟩ := exists_conj_index hV hd hdec hgM hgY
  obtain ⟨⟨hYsup, hYind, hcommY⟩, -, ⟨hVsup, hVind, hVi⟩, ⟨hperm, htrans⟩, -⟩ := hdec.body
  have hrk := rkIdx_fixV_le_of_fixes_rest (IntMod.sq_eq_one) hVind hdec.vs_sup hdec.vs_ne_bot
    (fun i => (hVi i).1) hperm ht ht2
    (fun k hk1 hk2 w hw => hfixall w (vs_val_mem_inf hV hd hdec hgM hj₀ hk1 hk2 hw))
  have hA : E3.mParam (autI hV M) ≤ rkIdx (fixV (Subgroup.zpowers t)) := by
    have hApg : IsPGroup 2 (Subgroup.zpowers t) :=
      IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, ht2]; norm_num)
    have hA1 : Subgroup.zpowers t ≠ ⊥ :=
      Subgroup.zpowers_ne_bot.2 (by intro h1; rw [h1, orderOf_one] at ht2; omega)
    exact E3.mParam_le_rkIdx_fixV (Subgroup.zpowers_le.2 ht) hApg hA1
  have hlt := eleven_mQuot_lt_mParam hV hd
  have hsupadd := rk_sup_add_rk_inf (Vs i₀) (Vs j₀)
  by_cases hX : autI hV X = Y i₀
  · have hv : ∀ i, rk (Vs i) = E3.mQuot V U := by
      intro i
      unfold rk
      rw [hdec.card_vs hX i, padicValNat.prime_pow]
    have := hv i₀
    have := hv j₀
    omega
  · obtain ⟨h3, -, -, -, h8⟩ : Nat.card (autI hV X) = 3 ∧ autI hV X ≤ Y i₀ ∧
        Nat.card (Y i₀) = 21 ∧ (∃ a ∈ Y i₀, ∃ b ∈ Y i₀, a * b ≠ b * a) ∧
        ∀ j, Nat.card (Vs j) = 8 := by
      rcases hdec.case with h | h
      · exact absurd h hX
      · exact h
    have hj : j₀ = i₀ := hj₀' hX
    have hn2 : E3.mQuot V U = 2 := by
      have := hdec.card_X
      rw [h3] at this
      have h4 : 2 ^ E3.mQuot V U = 2 ^ 2 := by omega
      exact Nat.pow_right_injective (le_refl 2) h4
    have hrk8 : rk (Vs i₀) = 3 := by
      unfold rk
      rw [h8 i₀, show (8 : ℕ) = 2 ^ 3 by norm_num, padicValNat.prime_pow]
    subst hj
    rw [sup_idem, hrk8] at hrk
    omega


end CFSG.LocalAnalysis.WeakClosure81
