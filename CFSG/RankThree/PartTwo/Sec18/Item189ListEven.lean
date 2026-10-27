module

public import CFSG.RankThree.PartTwo.Sec18.Item189ListParityInst
public import CFSG.RankThree.PartTwo.Sec4.Item47Unitary
public import CFSG.RankThree.PartOne.KC.EvenSymplecticSL2Automorphisms

public section

namespace CFSG.RankThree.PartTwo.Sec18

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projSL projSU)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

section Abstract

variable {Y : Type} [Group Y] {X Q : Subgroup Y} {Γ : Subgroup (MulAut Y)} {x : Y}

theorem absOutOrder_dvd_card_outer [Finite Y] (hX : X.Normal) :
    absOutOrder189 X ∣ Nat.card (Outer ↥X) := by
  haveI := hX
  haveI : Finite (MulAut ↥X) :=
    Finite.of_injective (fun f : MulAut ↥X => (f : ↥X → ↥X)) DFunLike.coe_injective
  let φ : Y →* Outer ↥X :=
    (QuotientGroup.mk' (CFSG.ComponentClassification.OuterAutomorphisms.inner ↥X)).comp
      MulAut.conjNormal
  have hker : φ.ker = X ⊔ Subgroup.centralizer (X : Set Y) := by
    apply le_antisymm
    · intro y hy
      have h1 : (MulAut.conjNormal y : MulAut ↥X) ∈
          CFSG.ComponentClassification.OuterAutomorphisms.inner ↥X :=
        (QuotientGroup.eq_one_iff _).mp hy
      obtain ⟨g, hg⟩ := MonoidHom.mem_range.mp h1
      have hc : (g : Y)⁻¹ * y ∈ Subgroup.centralizer (X : Set Y) := by
        rw [Subgroup.mem_centralizer_iff]
        intro a ha
        have h2 := congrArg (fun ψ : MulAut ↥X => ((ψ ⟨a, ha⟩ : ↥X) : Y)) hg
        simp only [MulAut.conjNormal_apply, MulAut.conj_apply] at h2
        have h2' : (g : Y) * a * (g : Y)⁻¹ = y * a * y⁻¹ := by simpa using h2
        calc a * ((g : Y)⁻¹ * y) = (g : Y)⁻¹ * ((g : Y) * a * (g : Y)⁻¹) * y := by group
          _ = (g : Y)⁻¹ * (y * a * y⁻¹) * y := by rw [h2']
          _ = ((g : Y)⁻¹ * y) * a := by group
      have : y = (g : Y) * ((g : Y)⁻¹ * y) := by group
      rw [this]
      exact Subgroup.mul_mem_sup g.2 hc
    · refine sup_le (fun a ha => ?_) (fun c hc => ?_)
      · rw [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
          QuotientGroup.eq_one_iff]
        exact ⟨⟨a, ha⟩, by
          ext b
          simp [MulAut.conjNormal_apply, MulAut.conj_apply]⟩
      · rw [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
          QuotientGroup.eq_one_iff]
        refine ⟨1, ?_⟩
        ext b
        have hcb : (b : Y) * c = c * (b : Y) := (Subgroup.mem_centralizer_iff.mp hc) b b.2
        have : c * (b : Y) * c⁻¹ = (b : Y) := by
          calc c * (b : Y) * c⁻¹ = (b : Y) * c * c⁻¹ := by rw [← hcb]
            _ = (b : Y) := by group
        simp [MulAut.conjNormal_apply, this]
  have h1 : (X ⊔ Subgroup.centralizer (X : Set Y)).index = Nat.card φ.range := by
    rw [← hker]
    exact Subgroup.index_ker φ
  unfold absOutOrder189
  rw [h1]
  exact Subgroup.card_subgroup_dvd_card φ.range

theorem ListData189.card_dvd_two_pow [Finite Y] (h : ListData189 X Q Γ x) (hR : Q ⊓ X = ⊥)
    {N k m : ℕ} (hN : Nat.card (Outer ↥X) ∣ N) (hNk : N = 2 ^ k * m) (hm : Odd m) :
    Nat.card Q ∣ 2 ^ k := by
  have h1 := h.card_inf_mul_outOrder
  rw [hR, Subgroup.card_bot, one_mul] at h1
  have hd : Nat.card Q ∣ 2 ^ k * m := by
    rw [← h1, ← hNk]
    exact (absOutOrder_dvd_card_outer h.normal).trans hN
  obtain ⟨j, hj⟩ := h.isPGroup.exists_card_eq
  rw [hj] at hd ⊢
  exact Nat.Coprime.dvd_of_dvd_mul_right (Nat.Coprime.pow_left j (Nat.coprime_two_left.mpr hm)) hd

theorem ListData189.absOutOrder_eq_of_pair [Finite Y] (h : ListData189 X Q Γ x)
    (hR : Q ⊓ X = ⊥) {k : ℕ} (hdvd : Nat.card Q ∣ 2 ^ k)
    (hpair : ∃ U U' : Subgroup Y, U ≠ U' ∧ CFSG.ABGLocalTools.IsSylowOf 2 U X ∧
      CFSG.ABGLocalTools.IsSylowOf 2 U' X ∧ x ∈ Subgroup.normalizer (U : Set Y) ∧
      x ∈ Subgroup.normalizer (U' : Set Y) ∧
      ∀ V : Subgroup Y, CFSG.ABGLocalTools.IsSylowOf 2 V X →
        x ∈ Subgroup.normalizer (V : Set Y) → V = U ∨ V = U')
    (hpar : ∀ {σ : Y}, σ * x = x * σ → ∀ {U U' : Subgroup Y},
      CFSG.ABGLocalTools.IsSylowOf 2 U X → CFSG.ABGLocalTools.IsSylowOf 2 U' X → U ≠ U' →
      x ∈ Subgroup.normalizer (U : Set Y) → x ∈ Subgroup.normalizer (U' : Set Y) →
      U.map (MulAut.conj σ).toMonoidHom = U' → 2 ^ k ∣ orderOf σ) :
    absOutOrder189 X = 2 ^ k := by
  obtain ⟨U, U', hne, hU, hU', hxU, hxU', hfix⟩ := hpair
  obtain ⟨σ, hσQ, hσ⟩ := h.exists_swap hR hU hU' hne hxU hxU' hfix
  exact h.absOutOrder_eq hR hdvd hσQ (hpar (h.comm_of_inf_eq_bot hR hσQ) hU hU' hne hxU hxU' hσ)

end Abstract

theorem card_outer_projSL_two {n : ℕ} (hn : 1 ≤ n) :
    Nat.card (Outer ↥(projSL 2 (GaloisField 2 n))) = n := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let φ := (Sec4.projSLEquivPSL (GaloisField 2 n)).trans
    (CFSG.RankThree.PartOne.KCRootAxis.slEquivPSL (K := GaloisField 2 n)).symm
  rw [Nat.card_congr (CFSG.ComponentClassification.OuterAutomorphisms.equivalence φ).toEquiv]
  exact CFSG.RankThree.PartOne.KCRootAxis.natCard_out_sl2 hn (GaloisField.card 2 n (by omega))

theorem exists_fixed_pair_psl2 {Y : Type} [Group Y] [Finite Y]
    {X : Subgroup Y} {n : ℕ} (hn : Even n) (hn2 : 2 ≤ n)
    (e : Nonempty (↥X ≃* projSL 2 (GaloisField 2 n))) {x : Y} (hx : x ∈ X)
    (hx3 : orderOf x = 3) :
    ∃ U U' : Subgroup Y, U ≠ U' ∧ CFSG.ABGLocalTools.IsSylowOf 2 U X ∧
      CFSG.ABGLocalTools.IsSylowOf 2 U' X ∧ x ∈ Subgroup.normalizer (U : Set Y) ∧
      x ∈ Subgroup.normalizer (U' : Set Y) ∧
      ∀ V : Subgroup Y, CFSG.ABGLocalTools.IsSylowOf 2 V X →
        x ∈ Subgroup.normalizer (V : Set Y) → V = U ∨ V = U' := by
  obtain ⟨ex⟩ := e
  obtain ⟨hB, hcard⟩ := borelOrderThree_projSL_two189 hn hn2 ex
  exact exists_fixed_pair_of_borel189 hB hcard hx hx3

theorem two_pow_dvd_orderOf_of_swap_psl2 {Y : Type} [Group Y]
    [Finite Y] {X : Subgroup Y} (hX : X.Normal) {n e m : ℕ} (he : 1 ≤ e) (hm : Odd m)
    (hn : n = 2 ^ e * m) (e₀ : Nonempty (↥X ≃* projSL 2 (GaloisField 2 n))) {x σ : Y}
    (hx : x ∈ X) (hx3 : orderOf x = 3) (hσx : σ * x = x * σ) {U U' : Subgroup Y}
    (hU : CFSG.ABGLocalTools.IsSylowOf 2 U X) (hU' : CFSG.ABGLocalTools.IsSylowOf 2 U' X)
    (hne : U ≠ U') (hxU : x ∈ Subgroup.normalizer (U : Set Y))
    (hxU' : x ∈ Subgroup.normalizer (U' : Set Y))
    (hswap : U.map (MulAut.conj σ).toMonoidHom = U') : 2 ^ e ∣ orderOf σ := by
  haveI := hX
  obtain ⟨ex⟩ := e₀
  have hn2 : 2 ≤ n := by
    have h1 : 2 ^ 1 ≤ 2 ^ e := Nat.pow_le_pow_right (by norm_num) he
    have h2 := hm.pos
    rw [hn]
    nlinarith
  have hev : Even n := by
    rw [hn]
    exact Nat.even_mul.mpr (Or.inl (Nat.even_pow.mpr ⟨even_two, by omega⟩))
  obtain ⟨hB, hcard⟩ := borelOrderThree_projSL_two189 hev hn2 ex
  obtain ⟨Z, _, _, Λ, hΛ, hZ, hinn, hker⟩ :=
    exists_hom_of_outShape189 (outShape_projSL_two189 hn hn2 ex)
  exact two_pow_dvd_orderOf_of_swap_of_borel189 hB hcard Λ hΛ hm hZ hinn hker hx hx3 hσx hU hU'
    hne hxU hxU' hswap

theorem ListData189.false_of_projSL_two_odd {Y : Type} [Group Y] [Finite Y] {X Q : Subgroup Y}
    {Γ : Subgroup (MulAut Y)} {x : Y} (h : ListData189 X Q Γ x) (hR : Q ⊓ X = ⊥) {n : ℕ}
    (hn : Odd n) (e : ↥X ≃* projSL 2 (GaloisField 2 n)) : False := by
  have hout : Nat.card (Outer ↥X) ∣ n := by
    rw [Nat.card_congr (CFSG.ComponentClassification.OuterAutomorphisms.equivalence e).toEquiv,
      card_outer_projSL_two hn.pos]
  have hd := h.card_dvd_two_pow hR hout (by rw [pow_zero, one_mul]) hn
  rw [pow_zero, Nat.dvd_one] at hd
  exact h.ne_bot (Subgroup.card_eq_one.mp hd)

theorem list189L2Even_of : List189L2Even := by
  intro Y _ _ X Q Γ x n h hn ⟨e⟩
  have hTI : UniqueSylowOver189 X :=
    uniqueSylowOver189_of_isBender (fusionIsBenderGroup_of_projSL_two hn e)
  by_cases hR : Q ⊓ X = ⊥
  · by_cases hev : Even n
    swap
    · exact (h.false_of_projSL_two_odd hR (Nat.not_even_iff_odd.mp hev) e).elim
    right; left
    obtain ⟨k, m, hm, hnkm⟩ := Nat.exists_eq_two_pow_mul_odd (show n ≠ 0 by omega)
    have hk : 1 ≤ k := by
      rcases Nat.eq_zero_or_pos k with rfl | hk
      · rw [pow_zero, one_mul] at hnkm
        subst hnkm
        exact absurd hev (Nat.not_even_iff_odd.mpr hm)
      · exact hk
    have hout : Nat.card (Outer ↥X) = n := by
      rw [Nat.card_congr (CFSG.ComponentClassification.OuterAutomorphisms.equivalence e).toEquiv]
      exact card_outer_projSL_two (by omega)
    refine ⟨n, k, m, hk, hm, hnkm, h.absInnerFree_iff.mpr hR, Or.inl ⟨⟨e⟩, ?_⟩⟩
    exact h.absOutOrder_eq_of_pair hR (h.card_dvd_two_pow hR (hout ▸ dvd_rfl) hnkm hm)
      (exists_fixed_pair_psl2 hev hn ⟨e⟩ h.mem h.orderOf_eq)
      (fun hσx _ _ hU hU' hne hxU hxU' hsw =>
        two_pow_dvd_orderOf_of_swap_psl2 h.normal hk hm hnkm ⟨e⟩ h.mem h.orderOf_eq hσx hU hU'
          hne hxU hxU' hsw)
  · left
    exact h.isSylowOf_top_of_inf_ne_bot hTI hR

theorem card_outer_projSU_three_dvd {n : ℕ} (hn : 2 ≤ n) :
    Nat.card (Outer ↥(projSU 3 2 n)) ∣ 2 * n * (2 ^ n + 1) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := Sec4.card_outer_projSU_dvd 3 2 n (by omega) le_rfl (by
    rintro ⟨-, h⟩
    have : 2 ^ 2 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
    omega)
  simpa using h

theorem exists_fixed_pair_psu3 {Y : Type} [Group Y] [Finite Y]
    {X : Subgroup Y} {n : ℕ} (hn : Even n) (hn2 : 2 ≤ n)
    (e : Nonempty (↥X ≃* projSU 3 2 n)) {x : Y} (hx : x ∈ X) (hx3 : orderOf x = 3) :
    ∃ U U' : Subgroup Y, U ≠ U' ∧ CFSG.ABGLocalTools.IsSylowOf 2 U X ∧
      CFSG.ABGLocalTools.IsSylowOf 2 U' X ∧ x ∈ Subgroup.normalizer (U : Set Y) ∧
      x ∈ Subgroup.normalizer (U' : Set Y) ∧
      ∀ V : Subgroup Y, CFSG.ABGLocalTools.IsSylowOf 2 V X →
        x ∈ Subgroup.normalizer (V : Set Y) → V = U ∨ V = U' := by
  obtain ⟨ex⟩ := e
  obtain ⟨hB, hcard⟩ := borelOrderThree_projSU_three189 hn hn2 ex
  exact exists_fixed_pair_of_borel189 hB hcard hx hx3

theorem two_pow_dvd_orderOf_of_swap_psu3 {Y : Type} [Group Y]
    [Finite Y] {X : Subgroup Y} (hX : X.Normal) {n e m : ℕ} (he : 1 ≤ e) (hm : Odd m)
    (hn : n = 2 ^ e * m) (e₀ : Nonempty (↥X ≃* projSU 3 2 n)) {x σ : Y} (hx : x ∈ X)
    (hx3 : orderOf x = 3) (hσx : σ * x = x * σ) {U U' : Subgroup Y}
    (hU : CFSG.ABGLocalTools.IsSylowOf 2 U X) (hU' : CFSG.ABGLocalTools.IsSylowOf 2 U' X)
    (hne : U ≠ U') (hxU : x ∈ Subgroup.normalizer (U : Set Y))
    (hxU' : x ∈ Subgroup.normalizer (U' : Set Y))
    (hswap : U.map (MulAut.conj σ).toMonoidHom = U') : 2 ^ (e + 1) ∣ orderOf σ := by
  haveI := hX
  obtain ⟨ex⟩ := e₀
  have hn2 : 2 ≤ n := by
    have h1 : 2 ^ 1 ≤ 2 ^ e := Nat.pow_le_pow_right (by norm_num) he
    have h2 := hm.pos
    rw [hn]
    nlinarith
  have hev : Even n := by
    rw [hn]
    exact Nat.even_mul.mpr (Or.inl (Nat.even_pow.mpr ⟨even_two, by omega⟩))
  obtain ⟨hB, hcard⟩ := borelOrderThree_projSU_three189 hev hn2 ex
  obtain ⟨Z, _, _, Λ, hΛ, hZ, hinn, hker⟩ :=
    exists_hom_of_outShape189 (outShape_projSU_three189 hn hn2 ex)
  exact two_pow_dvd_orderOf_of_swap_of_borel189 hB hcard Λ hΛ hm hZ hinn hker hx hx3 hσx hU hU'
    hne hxU hxU' hswap

theorem list189U3Even_of : List189U3Even := by
  intro Y _ _ X Q Γ x n h hev hn ⟨e⟩
  have hTI : UniqueSylowOver189 X :=
    uniqueSylowOver189_of_isBender (fusionIsBenderGroup_of_projSU_three hn e)
  by_cases hR : Q ⊓ X = ⊥
  · right; left
    obtain ⟨k, m, hm, hnkm⟩ := Nat.exists_eq_two_pow_mul_odd (show n ≠ 0 by omega)
    have hk : 1 ≤ k := by
      rcases Nat.eq_zero_or_pos k with rfl | hk
      · rw [pow_zero, one_mul] at hnkm
        subst hnkm
        exact absurd hev (Nat.not_even_iff_odd.mpr hm)
      · exact hk
    have hout : Nat.card (Outer ↥X) ∣ 2 ^ (k + 1) * (m * (2 ^ n + 1)) := by
      rw [Nat.card_congr (CFSG.ComponentClassification.OuterAutomorphisms.equivalence e).toEquiv]
      refine (card_outer_projSU_three_dvd (by omega)).trans (dvd_of_eq ?_)
      rw [hnkm]
      ring_nf
    have hodd : Odd (m * (2 ^ n + 1)) := by
      refine hm.mul ?_
      exact (Nat.even_pow.mpr ⟨even_two, by omega⟩).add_one
    refine ⟨n, k, m, hk, hm, hnkm, h.absInnerFree_iff.mpr hR, Or.inr ⟨⟨e⟩, ?_⟩⟩
    exact h.absOutOrder_eq_of_pair hR (h.card_dvd_two_pow hR hout rfl hodd)
      (exists_fixed_pair_psu3 hev hn ⟨e⟩ h.mem h.orderOf_eq)
      (fun hσx _ _ hU hU' hne hxU hxU' hsw =>
        two_pow_dvd_orderOf_of_swap_psu3 h.normal hk hm hnkm ⟨e⟩ h.mem h.orderOf_eq hσx hU hU'
          hne hxU hxU' hsw)
  · left
    exact h.isSylowOf_top_of_inf_ne_bot hTI hR

end CFSG.RankThree.PartTwo.Sec18
