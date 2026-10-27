module

public import CFSG.LocalAnalysis.StandardType.GGF4QGeFourPlusFrame
public import CFSG.LocalAnalysis.StandardType.GGOTwoPrimeMap
public import CFSG.LocalAnalysis.StandardType.GGSixSeventeenWitOmSmallBlock
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.Orth3Local
public import CFSG.RankThree.PartOne.S11d.OrthCaseN
public import CFSG.RankThree.PartOne.KC.OrthogonalEvenMinusExtraction
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.SLOrder

public section

namespace CFSG.StandardType

namespace OmPlusFrame

open Module Multiplicative QuadraticMap Polynomial
open CFSG.RankThree.Classical2 (orthDerived)
open CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne.KCOrthogonal
  CFSG.RankThree.OrthogonalInvolutions CFSG.GroupTheory.WeirSylow

section OTwo

variable {X : Type} [Group X]

theorem ggOTwoPrime_eq_of_le {C S : Subgroup X} (hSC : S ≤ C)
    (hgen : S ≤ Subgroup.closure {g | g ∈ S ∧ ∃ k : ℕ, g ^ (2 ^ k) = 1})
    (h2 : ∀ g ∈ C, ∀ k : ℕ, g ^ (2 ^ k) = 1 → g ∈ S) : ggOTwoPrime C = S := by
  apply le_antisymm
  · rw [ggOTwoPrime, Subgroup.closure_le]
    rintro g ⟨hg, k, hk⟩
    exact h2 g hg k hk
  · refine hgen.trans (Subgroup.closure_mono ?_)
    rintro g ⟨hg, k, hk⟩
    exact ⟨hSC hg, k, hk⟩

theorem le_closure_two_of_isSimpleGroup {S : Subgroup X} (hS : IsSimpleGroup S) {s : X}
    (hs : s ∈ S) (hs1 : s ≠ 1) (hs2 : s ^ 2 = 1) :
    S ≤ Subgroup.closure {g | g ∈ S ∧ ∃ k : ℕ, g ^ (2 ^ k) = 1} := by
  have hN : Subgroup.normalClosure {t : S | ∃ k : ℕ, t ^ (2 ^ k) = 1} = ⊤ := by
    haveI := hS
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
      (Subgroup.normalClosure {t : S | ∃ k : ℕ, t ^ (2 ^ k) = 1}) with h | h
    · exfalso
      have hmem : (⟨s, hs⟩ : S) ∈ Subgroup.normalClosure {t : S | ∃ k : ℕ, t ^ (2 ^ k) = 1} :=
        Subgroup.subset_normalClosure ⟨1, Subtype.ext (by simpa using hs2)⟩
      rw [h, Subgroup.mem_bot] at hmem
      exact hs1 (congrArg Subtype.val hmem)
    · exact h
  intro g hg
  have hgN : (⟨g, hg⟩ : S) ∈ Subgroup.normalClosure {t : S | ∃ k : ℕ, t ^ (2 ^ k) = 1} :=
    hN ▸ Subgroup.mem_top _
  rw [Subgroup.normalClosure] at hgN
  have h1 := Subgroup.mem_map_of_mem S.subtype hgN
  rw [MonoidHom.map_closure] at h1
  refine Subgroup.closure_mono ?_ h1
  rintro _ ⟨t, ht, rfl⟩
  obtain ⟨b, ⟨k, hk⟩, hbt⟩ := Group.mem_conjugatesOfSet_iff.mp ht
  obtain ⟨c, rfl⟩ := isConj_iff.mp hbt
  refine ⟨(c * b * c⁻¹).2, k, ?_⟩
  have : (c * b * c⁻¹) ^ (2 ^ k) = 1 := by rw [conj_pow, hk, mul_one, mul_inv_cancel]
  simpa using congrArg Subtype.val this

end OTwo

section Spaces

variable {K : Type} [Field K] {V : Type} [AddCommGroup V] [Module K V]

theorem commSpace_mul_le (a b : V ≃ₗ[K] V) :
    CFSG.RankThree.PartOne.LIT.commSpace (a * b) ≤
      CFSG.RankThree.PartOne.LIT.commSpace a ⊔ CFSG.RankThree.PartOne.LIT.commSpace b := by
  intro v hv
  obtain ⟨y, rfl⟩ := CFSG.RankThree.PartOne.LIT.mem_commSpace.mp hv
  have h : (a * b) y - y = (a (b y) - b y) + (b y - y) := by
    rw [LinearEquiv.mul_apply]
    abel
  rw [h]
  exact Submodule.add_mem_sup (CFSG.RankThree.PartOne.LIT.mem_commSpace.mpr ⟨b y, rfl⟩)
    (CFSG.RankThree.PartOne.LIT.mem_commSpace.mpr ⟨y, rfl⟩)

variable [FiniteDimensional K V]

theorem le_commSpace_mul {r : ℕ} (hr : (r : K) ≠ 0) {a b : V ≃ₗ[K] V} (har : a ^ r = 1)
    (hb : ∀ v ∈ CFSG.RankThree.PartOne.LIT.commSpace a, b v = v) :
    CFSG.RankThree.PartOne.LIT.commSpace a ≤ CFSG.RankThree.PartOne.LIT.commSpace (a * b) := by
  intro v hv
  obtain ⟨y, rfl⟩ := CFSG.RankThree.PartOne.LIT.mem_commSpace.mp hv
  have hc := CFSG.RankThree.PartOne.LIT.isCompl_fixedSpace_commSpace hr har
  have hy : y ∈ CFSG.RankThree.PartOne.LIT.fixedSpace a ⊔
      CFSG.RankThree.PartOne.LIT.commSpace a := by
    rw [hc.sup_eq_top]
    exact Submodule.mem_top
  obtain ⟨y₀, hy₀, y₁, hy₁, rfl⟩ := Submodule.mem_sup.mp hy
  refine CFSG.RankThree.PartOne.LIT.mem_commSpace.mpr ⟨y₁, ?_⟩
  rw [LinearEquiv.mul_apply, hb y₁ hy₁, map_add, CFSG.RankThree.PartOne.LIT.mem_fixedSpace.mp hy₀]
  abel

theorem commute_of_isCompl {W M : Submodule K V} (hWM : IsCompl W M) {g a : V ≃ₗ[K] V}
    (hgM : ∀ v ∈ M, g v = v) (hgW : ∀ v ∈ W, g v ∈ W) (haW : ∀ v ∈ W, a v = v)
    (haM : ∀ v ∈ M, a v ∈ M) : g * a = a * g := by
  apply LinearEquiv.ext
  intro v
  have hv : v ∈ W ⊔ M := by rw [hWM.sup_eq_top]; exact Submodule.mem_top
  obtain ⟨w, hw, m, hm, rfl⟩ := Submodule.mem_sup.mp hv
  have h1 : a (w + m) = w + a m := by rw [map_add, haW w hw]
  have h2 : g (w + m) = g w + m := by rw [map_add, hgM m hm]
  rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, h1, h2, map_add, map_add, hgM _ (haM m hm),
    haW _ (hgW w hw)]

theorem sub_one_pow_two_pow' {R : Type*} [Ring R] (h2 : (2 : R) = 0) (y : R) (k : ℕ) :
    (y - 1) ^ (2 ^ k) = y ^ (2 ^ k) - 1 := by
  have key : ∀ z : R, (z - 1) ^ 2 = z ^ 2 - 1 := fun z => by
    have h : (z - 1) ^ 2 - (z ^ 2 - 1) = (2 : R) * (1 - z) := by noncomm_ring
    rw [h2, zero_mul, sub_eq_zero] at h
    exact h
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ, pow_mul, ih, key, ← pow_mul]

theorem sub_one_pow_two_pow [CharP K 2] (g : Module.End K V) (k : ℕ) :
    (g - 1) ^ (2 ^ k) = g ^ (2 ^ k) - 1 := by
  have h2 : (2 : Module.End K V) = 0 := by
    have := congrArg (algebraMap K (Module.End K V)) (CharTwo.two_eq_zero (R := K))
    rwa [map_ofNat, map_zero] at this
  exact sub_one_pow_two_pow' h2 g k

theorem eq_one_of_two_pow_of_isCompl [CharP K 2] {M W : Submodule K V} (hMW : IsCompl M W)
    (hW2 : finrank K W = 2) {g : V ≃ₗ[K] V} (hgM : ∀ v ∈ M, g v = v)
    (hgW : ∀ v ∈ W, g v ∈ W) {k : ℕ} (hgk : g ^ (2 ^ k) = 1)
    (hev : Even (finrank K (CFSG.RankThree.OrthogonalInvolutions.commSpace g))) : g = 1 := by
  set N : Module.End K V := (g : V →ₗ[K] V) - 1 with hN
  have hNM : ∀ v ∈ M, N v = 0 := fun v hv => by
    simp [hN, hgM v hv]
  have hNv : ∀ v : V, ∃ w ∈ W, N v = N w := fun v => by
    have hv : v ∈ M ⊔ W := by rw [hMW.sup_eq_top]; exact Submodule.mem_top
    obtain ⟨m, hm, w, hw, rfl⟩ := Submodule.mem_sup.mp hv
    exact ⟨w, hw, by rw [map_add, hNM m hm, zero_add]⟩
  have hNW : ∀ w ∈ W, N w ∈ W := fun w hw => by
    simp only [hN, LinearMap.sub_apply, LinearEquiv.coe_coe, Module.End.one_apply]
    exact W.sub_mem (hgW w hw) hw
  have hrange : LinearMap.range N ≤ W := by
    rintro _ ⟨v, rfl⟩
    obtain ⟨w, hw, hvw⟩ := hNv v
    rw [hvw]
    exact hNW w hw
  have hle2 : finrank K (LinearMap.range N) ≤ 2 := hW2 ▸ Submodule.finrank_mono hrange
  have hpow : N ^ (2 ^ k) = 0 := by
    rw [hN, sub_one_pow_two_pow]
    have : (g : V →ₗ[K] V) ^ (2 ^ k) = 1 := by
      rw [← CFSG.RankThree.PartOne.LIT.coe_pow_eq, hgk]
      rfl
    rw [this, sub_self]
  change Even (finrank K (LinearMap.range N)) at hev
  rcases (show finrank K (LinearMap.range N) = 0 ∨ finrank K (LinearMap.range N) = 2 by
    obtain ⟨m, hm⟩ := hev
    omega) with h0 | h2
  · rw [Submodule.finrank_eq_zero] at h0
    apply LinearEquiv.ext
    intro v
    have hv : N v = 0 := by
      have : N v ∈ LinearMap.range N := LinearMap.mem_range_self N v
      rw [h0] at this
      exact this
    simpa [hN, sub_eq_zero] using hv
  · exfalso
    have heq : LinearMap.range N = W :=
      Submodule.eq_of_le_of_finrank_eq hrange (by rw [h2, hW2])
    have hsurj : ∀ w ∈ W, ∃ w' ∈ W, N w' = w := fun w hw => by
      rw [← heq] at hw
      obtain ⟨v, rfl⟩ := hw
      obtain ⟨w', hw', h⟩ := hNv v
      exact ⟨w', hw', h.symm⟩
    have hall : ∀ n : ℕ, ∀ w ∈ W, ∃ w' ∈ W, (N ^ n) w' = w := by
      intro n
      induction n with
      | zero => intro w hw; exact ⟨w, hw, by simp⟩
      | succ n ih =>
        intro w hw
        obtain ⟨w₁, hw₁, h₁⟩ := ih w hw
        obtain ⟨w₂, hw₂, h₂⟩ := hsurj w₁ hw₁
        exact ⟨w₂, hw₂, by rw [pow_succ, Module.End.mul_apply, h₂, h₁]⟩
    have hWne : W ≠ ⊥ := by
      intro h
      rw [h, finrank_bot] at hW2
      omega
    obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hWne
    obtain ⟨w', -, hw'⟩ := hall (2 ^ k) w hw
    rw [hpow, LinearMap.zero_apply] at hw'
    exact hw0 hw'.symm

end Spaces

section Odd

variable {K : Type} [Field K] [Finite K] [CharP K 2] {V : Type} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V}

theorem othersSpace_eq_commSpace {p : ℕ} {x : V ≃ₗ[K] V} (hx : OddOrderIsometry Q p x) :
    othersSpace x.toLinearMap (X - 1) = CFSG.RankThree.PartOne.LIT.commSpace x := by
  have hle : othersSpace x.toLinearMap (X - 1) ≤ CFSG.RankThree.PartOne.LIT.commSpace x := by
    unfold othersSpace
    refine iSup_le fun k => iSup_le fun hk => ?_
    exact OrthRestOdd.primaryComponent_le_commSpace hx hk.1 hk.2.1
  apply Submodule.eq_of_le_of_finrank_eq hle
  have h1 := Submodule.finrank_add_eq_of_isCompl hx.fixed_others.1
  have h2 := Submodule.finrank_add_eq_of_isCompl
    (CFSG.RankThree.PartOne.LIT.isCompl_fixedSpace_commSpace hx.cast_ne_zero hx.pow_eq_one)
  rw [← OrthRestOdd.fixedSpace_eq_lit] at h2
  omega

theorem apply_eq_of_two_pow_commSpace (hQ : (polarBilin Q).Nondegenerate) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hK1 : ∀ c : K, c ^ p = 1 → c = 1) {t : V ≃ₗ[K] V}
    (ht : t ∈ orthDerived Q) (htp : t ^ p = 1)
    (ht2 : finrank K (CFSG.RankThree.PartOne.LIT.commSpace t) = 2) {g : V ≃ₗ[K] V}
    (hgt : t * g = g * t) {k : ℕ} (hgk : g ^ (2 ^ k) = 1) :
    ∀ v ∈ CFSG.RankThree.PartOne.LIT.commSpace t, g v = v := by
  have hx : OddOrderIsometry Q p t :=
    oddOrderIsometry_of_orthDerived hQ hp hp2 (t := ⟨t, ht⟩) (Subtype.ext (by simpa using htp))
  have hmult : ∀ h ∈ primaryFactors t.toLinearMap, h ≠ X - 1 →
      primaryMultiplicity t.toLinearMap h ≤ 1 := fun h hh hne =>
    (OrthRestOdd.primaryMultiplicity_eq_one hx hK1 ht2 hh hne).le
  have hgC : g ∈ Subgroup.centralizer ({t} : Set (V ≃ₗ[K] V)) :=
    Subgroup.mem_centralizer_singleton_iff.mpr hgt.symm
  have hgR := hx.apply_eq_of_two_pow hmult hgC hgk
  rw [othersSpace_eq_commSpace hx] at hgR
  exact hgR

theorem fixed_of_fixed_mul {a b : V ≃ₗ[K] V}
    (hdisj : CFSG.RankThree.PartOne.LIT.commSpace a ⊓ CFSG.RankThree.PartOne.LIT.commSpace b = ⊥)
    (hab' : ∀ v ∈ CFSG.RankThree.PartOne.LIT.commSpace b, a v = v) {v : V}
    (hv : (a * b) v = v) : a v = v ∧ b v = v := by
  have hy : a v - v ∈ CFSG.RankThree.PartOne.LIT.commSpace a :=
    CFSG.RankThree.PartOne.LIT.mem_commSpace.mpr ⟨v, rfl⟩
  have hz : b v - v ∈ CFSG.RankThree.PartOne.LIT.commSpace b :=
    CFSG.RankThree.PartOne.LIT.mem_commSpace.mpr ⟨v, rfl⟩
  have h1 : a (b v) = a v + (b v - v) := by
    rw [show b v = v + (b v - v) by abel, map_add, hab' _ hz]
    abel
  have hsum : (a v - v) + (b v - v) = 0 := by
    have h2 : a (b v) = v := hv
    rw [h2] at h1
    rw [show (a v - v) + (b v - v) = (a v + (b v - v)) - v by abel, ← h1, sub_self]
  have hyb : a v - v ∈ CFSG.RankThree.PartOne.LIT.commSpace b := by
    rw [eq_neg_of_add_eq_zero_left hsum]
    exact Submodule.neg_mem _ hz
  have hy0 : a v - v = 0 := by
    have : a v - v ∈ CFSG.RankThree.PartOne.LIT.commSpace a ⊓
        CFSG.RankThree.PartOne.LIT.commSpace b := ⟨hy, hyb⟩
    rw [hdisj] at this
    exact this
  rw [hy0, zero_add] at hsum
  exact ⟨sub_eq_zero.mp hy0, sub_eq_zero.mp hsum⟩

end Odd

section Sign

variable {K : Type} [Field K] [Finite K] [CharP K 2] {V : Type} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V}

theorem sign_rankOne (hQ : (polarBilin Q).Nondegenerate) (hdim : finrank K V = 8)
    (hminus : ¬ IsPlusType Q) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ∣ Nat.card K + 1) {a b : V ≃ₗ[K] V} (ha : a ∈ orthDerived Q)
    (hb : b ∈ orthDerived Q) (hab : a * b = b * a) (hap : a ^ p = 1) (hbp : b ^ p = 1)
    (ha2 : finrank K (CFSG.RankThree.PartOne.LIT.commSpace a) = 2)
    (hb2 : finrank K (CFSG.RankThree.PartOne.LIT.commSpace b) = 2)
    (hba : ∀ v ∈ CFSG.RankThree.PartOne.LIT.commSpace a, b v = v)
    (hab' : ∀ v ∈ CFSG.RankThree.PartOne.LIT.commSpace b, a v = v) :
    ggOTwoPrime (orthDerived Q ⊓ Subgroup.centralizer ({a, b} : Set (V ≃ₗ[K] V))) =
        supportedFixedDerived Q (a * b) ∧
      IsSimpleGroup ↥(supportedFixedDerived Q (a * b)) ∧
      (∃ g h : ↥(supportedFixedDerived Q (a * b)), g * h ≠ h * g) ∧
      Nat.card ↥(supportedFixedDerived Q (a * b)) = Nat.card K ^ 2 * (Nat.card K ^ 4 - 1) := by
  classical
  have hK1 := eq_one_of_pow_eq_one_of_dvd_add_one (K := K) hp hp2 hpq
  set x := a * b with hxdef
  have hxΩ : x ∈ orthDerived Q := mul_mem ha hb
  have hxp : x ^ p = 1 := by
    rw [hxdef, (show Commute a b from hab).mul_pow, hap, hbp, one_mul]
  have hx : OddOrderIsometry Q p x :=
    oddOrderIsometry_of_orthDerived hQ hp hp2 (t := ⟨x, hxΩ⟩) (Subtype.ext (by simpa using hxp))
  have hpK : (p : K) ≠ 0 := hx.cast_ne_zero
  have hdisj : CFSG.RankThree.PartOne.LIT.commSpace a ⊓
      CFSG.RankThree.PartOne.LIT.commSpace b = ⊥ := by
    rw [eq_bot_iff]
    rintro v ⟨hva, hvb⟩
    have hc := (CFSG.RankThree.PartOne.LIT.isCompl_fixedSpace_commSpace hpK hbp).inf_eq_bot
    have : v ∈ CFSG.RankThree.PartOne.LIT.fixedSpace b ⊓
        CFSG.RankThree.PartOne.LIT.commSpace b :=
      ⟨CFSG.RankThree.PartOne.LIT.mem_fixedSpace.mpr (hba v hva), hvb⟩
    rw [hc] at this
    exact this
  have hcx : CFSG.RankThree.PartOne.LIT.commSpace x =
      CFSG.RankThree.PartOne.LIT.commSpace a ⊔ CFSG.RankThree.PartOne.LIT.commSpace b := by
    apply le_antisymm (commSpace_mul_le a b)
    apply sup_le (le_commSpace_mul hpK hap hba)
    exact (le_commSpace_mul hpK hbp hab').trans (le_of_eq (congrArg _ hab.symm))
  have hcx4 : finrank K (CFSG.RankThree.PartOne.LIT.commSpace x) = 4 := by
    have := Submodule.finrank_sup_add_finrank_inf_eq (CFSG.RankThree.PartOne.LIT.commSpace a)
      (CFSG.RankThree.PartOne.LIT.commSpace b)
    rw [hdisj, finrank_bot, add_zero, ← hcx, ha2, hb2] at this
    omega
  have hcompl := CFSG.RankThree.PartOne.LIT.isCompl_fixedSpace_commSpace hpK hxp
  have hsumx := Submodule.finrank_add_eq_of_isCompl hcompl
  have hfx4 : finrank K (fixedSpace x) = 4 := by
    rw [OrthRestOdd.fixedSpace_eq_lit]
    omega
  have hothers := othersSpace_eq_commSpace hx
  obtain ⟨s, k, hs, hk, hsk, htype⟩ :=
    CFSG.HardMathSupport.Dickson.Bal207.OrthFix.fixed_type' hx hp hp2 hpq (n := 4) hdim
  have hk2 : k = 2 := by
    rw [hothers, hcx4] at hk
    omega
  have hRminus : ¬ IsPlusType (Q.comp (fixedSpace x).subtype) := by
    rw [htype (by omega)]
    intro h
    exact hminus (h.mpr (by rw [hk2]; decide))
  have hRnd : (polarBilin (Q.comp (fixedSpace x).subtype)).Nondegenerate :=
    hx.polarBilin_fixed_nondegenerate
  have hts : ∀ U : Submodule K (fixedSpace x), finrank K U = finrank K (fixedSpace x) / 2 →
      ∃ u ∈ U, (Q.comp (fixedSpace x).subtype) u ≠ 0 := by
    intro U hU
    by_contra hn
    push Not at hn
    exact hRminus ⟨U, by omega, hn⟩
  obtain ⟨-, hDD⟩ := CFSG.RankThree.PartOne.nonsplit_quasisimple_dicksonDerived
    (Q.comp (fixedSpace x).subtype) hRnd (Or.inl hfx4) hts
  obtain ⟨hsimp, -, hnab, -, -, h4, -⟩ :=
    CFSG.RankThree.PartOne.even_minus_four_six_actual_derived_extraction
      (Q.comp (fixedSpace x).subtype) hRnd (Or.inl hfx4) hts
  obtain ⟨E, _, _, D, ψ, ρ, -, -, hρinj, hρrange, hρcard⟩ := h4 hfx4
  let e := supportedFixedDerivedEquiv hx
  have hS : IsSimpleGroup ↥(supportedFixedDerived Q x) := by
    haveI := hsimp
    haveI : Nontrivial ↥(supportedFixedDerived Q x) := e.toEquiv.nontrivial
    exact IsSimpleGroup.isSimpleGroup_of_surjective e.symm.toMonoidHom e.symm.surjective
  have hnab' : ∃ g h : ↥(supportedFixedDerived Q x), g * h ≠ h * g := by
    by_contra hc
    push Not at hc
    apply hnab
    intro y z
    apply e.symm.injective
    rw [map_mul, map_mul, hc]
  have hcard : Nat.card ↥(supportedFixedDerived Q x) = Nat.card K ^ 2 * (Nat.card K ^ 4 - 1) := by
    rw [Nat.card_congr e.toEquiv, ← hρcard, hρrange]
  refine ⟨?_, hS, hnab', hcard⟩
  have h2el : ∀ g ∈ orthDerived Q ⊓ Subgroup.centralizer ({a, b} : Set (V ≃ₗ[K] V)),
      ∀ k : ℕ, g ^ (2 ^ k) = 1 → g ∈ supportedFixedDerived Q x := by
    rintro g ⟨hgΩ, hgC⟩ k hgk
    have hag : a * g = g * a := Subgroup.mem_centralizer_iff.mp hgC a (by simp)
    have hbg : b * g = g * b := Subgroup.mem_centralizer_iff.mp hgC b (by simp)
    have hgA := apply_eq_of_two_pow_commSpace hQ hp hp2 hK1 ha hap ha2 hag hgk
    have hgB := apply_eq_of_two_pow_commSpace hQ hp hp2 hK1 hb hbp hb2 hbg hgk
    have hgX : ∀ v ∈ CFSG.RankThree.PartOne.LIT.commSpace x, g v = v := by
      intro v hv
      rw [hcx] at hv
      obtain ⟨v₁, hv₁, v₂, hv₂, rfl⟩ := Submodule.mem_sup.mp hv
      rw [map_add, hgA v₁ hv₁, hgB v₂ hv₂]
    have hxg : x * g = g * x := by
      rw [hxdef, mul_assoc, hbg, ← mul_assoc, hag, mul_assoc]
    have hgM : g ∈ isometryCentralizer Q x :=
      Subgroup.mem_inf.mpr ⟨orthDerived_le_orthogonalGroup hgΩ,
        Subgroup.mem_centralizer_singleton_iff.mpr hxg.symm⟩
    have hblock : g ∈ supportedBlock Q x (X - 1) :=
      mem_supportedBlock.mpr ⟨hgM, fun v hv => hgX v (hothers ▸ hv)⟩
    have hr : (X - 1 : K[X]) ∈ primaryFactors x.toLinearMap := by
      by_contra hnot
      have hbot := fixedSpace_eq_bot_of_not_mem hnot
      rw [hbot, finrank_bot] at hfx4
      omega
    have hdick := dicksonHom_apply_orthDerived_eq_one hQ hgΩ
    rw [hx.dicksonHom_eq_restrict_of_mem_supportedBlock (hp.odd_of_ne_two hp2) hQ hr hblock]
      at hdick
    exact mem_supportedFixedDerived.mpr ⟨hblock, hDD _ hdick⟩
  have hSC : supportedFixedDerived Q x ≤
      orthDerived Q ⊓ Subgroup.centralizer ({a, b} : Set (V ≃ₗ[K] V)) := by
    intro g hg
    refine ⟨hx.supportedFixedDerived_le_orthDerived hg, ?_⟩
    obtain ⟨hgM, hgO⟩ := mem_supportedBlock.mp (supportedFixedDerived_le_supportedBlock hg)
    have hxg : x * g = g * x :=
      (Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp hgM).2).symm
    have hgM' : ∀ v ∈ CFSG.RankThree.PartOne.LIT.commSpace x, g v = v := fun v hv =>
      hgO v (hothers.symm ▸ hv)
    have hgW : ∀ v ∈ CFSG.RankThree.PartOne.LIT.fixedSpace x,
        g v ∈ CFSG.RankThree.PartOne.LIT.fixedSpace x := fun v hv => by
      rw [CFSG.RankThree.PartOne.LIT.mem_fixedSpace] at hv ⊢
      rw [← LinearEquiv.mul_apply, hxg, LinearEquiv.mul_apply, hv]
    have hpres : ∀ y : V ≃ₗ[K] V, y * x = x * y →
        ∀ v ∈ CFSG.RankThree.PartOne.LIT.commSpace x,
          y v ∈ CFSG.RankThree.PartOne.LIT.commSpace x := by
      intro y hy v hv
      obtain ⟨w, rfl⟩ := CFSG.RankThree.PartOne.LIT.mem_commSpace.mp hv
      refine CFSG.RankThree.PartOne.LIT.mem_commSpace.mpr ⟨y w, ?_⟩
      rw [map_sub, ← LinearEquiv.mul_apply, ← LinearEquiv.mul_apply, hy]
    have hax : a * x = x * a := by rw [hxdef, mul_assoc, ← hab]
    have hbx : b * x = x * b := by rw [hxdef, ← mul_assoc, ← hab]
    have hfix : ∀ v ∈ CFSG.RankThree.PartOne.LIT.fixedSpace x, a v = v ∧ b v = v :=
      fun v hv => fixed_of_fixed_mul hdisj hab' (CFSG.RankThree.PartOne.LIT.mem_fixedSpace.mp hv)
    show g ∈ Subgroup.centralizer ({a, b} : Set (V ≃ₗ[K] V))
    rw [Subgroup.mem_centralizer_iff]
    rintro y (rfl | rfl)
    · exact (commute_of_isCompl hcompl hgM' hgW (fun v hv => (hfix v hv).1)
        (hpres y hax)).symm
    · exact (commute_of_isCompl hcompl hgM' hgW (fun v hv => (hfix v hv).2)
        (hpres y hbx)).symm
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h2dvd : 2 ∣ Nat.card ↥(supportedFixedDerived Q x) := by
    rw [hcard]
    haveI := Fintype.ofFinite K
    have h2K : 2 ∣ Nat.card K := by
      rw [Nat.card_eq_fintype_card]
      exact (CharP.cast_eq_zero_iff K 2 _).mp (FiniteField.cast_card_eq_zero K)
    exact Dvd.dvd.mul_right (dvd_pow h2K two_ne_zero) _
  obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' 2 h2dvd
  have ht1 : (t : V ≃ₗ[K] V) ≠ 1 := by
    intro h
    have : t = 1 := Subtype.ext h
    rw [this, orderOf_one] at ht
    omega
  have ht2 : (t : V ≃ₗ[K] V) ^ 2 = 1 := by
    rw [← Subgroup.coe_pow, ← ht, pow_orderOf_eq_one, Subgroup.coe_one]
  exact ggOTwoPrime_eq_of_le hSC (le_closure_two_of_isSimpleGroup hS t.2 ht1 ht2) h2el

end Sign

section Transp

theorem sl2_closure_sq_eq_one {E : Type} [Field E] (h2 : (2 : E) = 0) :
    Subgroup.closure {g : Matrix.SpecialLinearGroup (Fin 2) E | g ^ 2 = 1} = ⊤ := by
  rw [eq_top_iff]
  rw [← Matrix.SpecialLinearGroup.closure_range_toSpecialLinearGroup_eq_top_of_field
    (K := E) (ι := Fin 2)]
  refine Subgroup.closure_mono ?_
  rintro g ⟨t, rfl⟩
  obtain ⟨i, j, hij, c⟩ := t
  rw [Matrix.TransvectionStruct.toSpecialLinearGroup_mk]
  change (Matrix.SpecialLinearGroup.transvection hij c) ^ 2 = 1
  have h := Matrix.SpecialLinearGroup.transvection_add (F := E) hij c c
  rw [show c + c = 0 by rw [← two_mul, h2, zero_mul],
    Matrix.SpecialLinearGroup.transvection_coeff_zero] at h
  rw [pow_two]
  exact h.symm

theorem le_closure_two_of_mulEquiv {X H : Type} [Group X] [Group H] {S : Subgroup X}
    (e : ↥S ≃* H) (hH : Subgroup.closure {h : H | h ^ 2 = 1} = ⊤) :
    S ≤ Subgroup.closure {g | g ∈ S ∧ ∃ k : ℕ, g ^ (2 ^ k) = 1} := by
  intro g hg
  have h1 : e ⟨g, hg⟩ ∈ Subgroup.closure {h : H | h ^ 2 = 1} := hH ▸ Subgroup.mem_top _
  have h2 := Subgroup.mem_map_of_mem (S.subtype.comp e.symm.toMonoidHom) h1
  rw [MonoidHom.map_closure] at h2
  have h3 : (S.subtype.comp e.symm.toMonoidHom) (e ⟨g, hg⟩) = g := by simp
  rw [h3] at h2
  refine Subgroup.closure_mono ?_ h2
  rintro _ ⟨h, hh, rfl⟩
  refine ⟨(e.symm h).2, 1, ?_⟩
  have hh' : h ^ 2 = 1 := hh
  have : (e.symm h) ^ 2 = 1 := by rw [← map_pow, hh', map_one]
  simpa using congrArg Subtype.val this

variable {K : Type} [Field K] [Finite K] [CharP K 2] {V : Type} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V}

theorem transp_rankOne (hQ : (polarBilin Q).Nondegenerate) (hdim : finrank K V = 8) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ Nat.card K + 1) (hK4 : 4 ≤ Nat.card K)
    {a s : V ≃ₗ[K] V} (ha : a ∈ orthDerived Q) (hs : s ∈ orthDerived Q) (has : a * s = s * a)
    (hap : a ^ p = 1) (hsp : s ^ p = 1)
    (ha2 : finrank K (CFSG.RankThree.PartOne.LIT.commSpace a) = 2)
    (hs4 : finrank K (CFSG.RankThree.PartOne.LIT.commSpace s) = 4)
    (hsa : ∀ v ∈ CFSG.RankThree.PartOne.LIT.commSpace a, s v = v)
    (has' : ∀ v ∈ CFSG.RankThree.PartOne.LIT.commSpace s, a v = v)
    {h : K[X]} (hh : h ∈ primaryFactors s.toLinearMap) (hne : h ≠ X - 1)
    (hm : primaryMultiplicity s.toLinearMap h = 2)
    (hVh : primaryComponent s.toLinearMap h = CFSG.RankThree.PartOne.LIT.commSpace s) :
    ggOTwoPrime (orthDerived Q ⊓ Subgroup.centralizer ({a, s} : Set (V ≃ₗ[K] V))) =
        specialBlock Q s h ∧
      ∃ (E : Type) (_ : Field E) (_ : Finite E), Nat.card E = Nat.card K ∧
        Nonempty (↥(specialBlock Q s h) ≃* Matrix.SpecialLinearGroup (Fin 2) E) := by
  classical
  have hK1 := eq_one_of_pow_eq_one_of_dvd_add_one (K := K) hp hp2 hpq
  have hx : OddOrderIsometry Q p s :=
    oddOrderIsometry_of_orthDerived hQ hp hp2 (t := ⟨s, hs⟩) (Subtype.ext (by simpa using hsp))
  have hpK : (p : K) ≠ 0 := hx.cast_ne_zero
  have hself : h = reciprocalPolynomial h :=
    (hx.reciprocal_eq_of_dvd_card_succ hp hpq hh hne).symm
  obtain ⟨E, hEf, hEfin, hEcard, ⟨eE⟩⟩ := SevOmSmall.exists_specialBlock_equiv_SL2 hx hp hp2 hpq hh hne hm
  refine ⟨?_, E, hEf, hEfin, hEcard, ⟨eE⟩⟩
  have hcompl_s := CFSG.RankThree.PartOne.LIT.isCompl_fixedSpace_commSpace hpK hsp
  have hcompl_a := CFSG.RankThree.PartOne.LIT.isCompl_fixedSpace_commSpace hpK hap
  have hsum_s := Submodule.finrank_add_eq_of_isCompl hcompl_s
  have hsum_a := Submodule.finrank_add_eq_of_isCompl hcompl_a
  have hX1 : (X - 1 : K[X]) ∈ primaryFactors s.toLinearMap := by
    by_contra hnot
    have hbot := fixedSpace_eq_bot_of_not_mem hnot
    rw [← OrthRestOdd.fixedSpace_eq_lit, hbot, finrank_bot, hs4, hdim] at hsum_s
    omega
  have hXh : (X - 1 : K[X]) ≠ h := fun e => hne e.symm
  have hXh' : (X - 1 : K[X]) ≠ reciprocalPolynomial h := by
    rw [← hself]
    exact hXh
  have hfixP : ∀ v ∈ CFSG.RankThree.PartOne.LIT.fixedSpace s,
      v ∈ primaryComponent s.toLinearMap (X - 1) := by
    intro v hv
    rw [← fixedSpace_eq_primaryComponent, OrthRestOdd.fixedSpace_eq_lit]
    exact hv
  have hblockFix : ∀ g ∈ supportedBlock Q s h,
      ∀ v ∈ CFSG.RankThree.PartOne.LIT.fixedSpace s, g v = v := by
    intro g hg v hv
    exact (mem_supportedBlock.mp hg).2 v (Submodule.mem_iSup_of_mem (X - 1)
      (Submodule.mem_iSup_of_mem ⟨hX1, hXh, hXh'⟩ (hfixP v hv)))
  have hcs : ∀ g ∈ supportedBlock Q s h, g * s = s * g := fun g hg =>
    Subgroup.mem_centralizer_singleton_iff.mp
      (Subgroup.mem_inf.mp (mem_supportedBlock.mp hg).1).2
  have hpresC : ∀ y : V ≃ₗ[K] V, y * s = s * y → ∀ v ∈ CFSG.RankThree.PartOne.LIT.commSpace s,
      y v ∈ CFSG.RankThree.PartOne.LIT.commSpace s := by
    intro y hy v hv
    obtain ⟨w, rfl⟩ := CFSG.RankThree.PartOne.LIT.mem_commSpace.mp hv
    refine CFSG.RankThree.PartOne.LIT.mem_commSpace.mpr ⟨y w, ?_⟩
    rw [map_sub, ← LinearEquiv.mul_apply, ← LinearEquiv.mul_apply, hy]
  have hpresF : ∀ y : V ≃ₗ[K] V, y * s = s * y → ∀ v ∈ CFSG.RankThree.PartOne.LIT.fixedSpace s,
      y v ∈ CFSG.RankThree.PartOne.LIT.fixedSpace s := by
    intro y hy v hv
    rw [CFSG.RankThree.PartOne.LIT.mem_fixedSpace] at hv ⊢
    rw [← LinearEquiv.mul_apply, ← hy, LinearEquiv.mul_apply, hv]
  have hFa : ∀ g ∈ supportedBlock Q s h, a * g = g * a := fun g hg =>
    (commute_of_isCompl hcompl_s.symm (hblockFix g hg) (hpresC g (hcs g hg)) has'
      (hpresF a has)).symm
  have hSC : specialBlock Q s h ≤
      orthDerived Q ⊓ Subgroup.centralizer ({a, s} : Set (V ≃ₗ[K] V)) := by
    intro g hg
    have hgB := specialBlock_le_supportedBlock h hg
    refine ⟨CFSG.HardMathSupport.Timmesfeld.CrossChar.orth3_specialBlock_le_orthDerived hx hp hp2 hK4 hh hne (by omega) hg, ?_⟩
    show g ∈ Subgroup.centralizer ({a, s} : Set (V ≃ₗ[K] V))
    rw [Subgroup.mem_centralizer_iff]
    rintro y (rfl | rfl)
    · exact hFa g hgB
    · exact (hcs g hgB).symm
  have hdisj : CFSG.RankThree.PartOne.LIT.commSpace a ⊓
      CFSG.RankThree.PartOne.LIT.commSpace s = ⊥ := by
    rw [eq_bot_iff]
    rintro v ⟨hva, hvs⟩
    have : v ∈ CFSG.RankThree.PartOne.LIT.fixedSpace s ⊓
        CFSG.RankThree.PartOne.LIT.commSpace s :=
      ⟨CFSG.RankThree.PartOne.LIT.mem_fixedSpace.mpr (hsa v hva), hvs⟩
    rw [hcompl_s.inf_eq_bot] at this
    exact this
  have hdimM : finrank K ↥(CFSG.RankThree.PartOne.LIT.commSpace a ⊔
      CFSG.RankThree.PartOne.LIT.commSpace s) = 6 := by
    have := Submodule.finrank_sup_add_finrank_inf_eq (CFSG.RankThree.PartOne.LIT.commSpace a)
      (CFSG.RankThree.PartOne.LIT.commSpace s)
    rw [hdisj, finrank_bot, add_zero, ha2, hs4] at this
    omega
  have hMW : IsCompl (CFSG.RankThree.PartOne.LIT.commSpace a ⊔
      CFSG.RankThree.PartOne.LIT.commSpace s)
      (CFSG.RankThree.PartOne.LIT.fixedSpace a ⊓ CFSG.RankThree.PartOne.LIT.fixedSpace s) := by
    have hW : 2 ≤ finrank K ↥(CFSG.RankThree.PartOne.LIT.fixedSpace a ⊓
        CFSG.RankThree.PartOne.LIT.fixedSpace s) := by
      have := Submodule.finrank_sup_add_finrank_inf_eq (CFSG.RankThree.PartOne.LIT.fixedSpace a)
        (CFSG.RankThree.PartOne.LIT.fixedSpace s)
      have hle := Submodule.finrank_le (CFSG.RankThree.PartOne.LIT.fixedSpace a ⊔
        CFSG.RankThree.PartOne.LIT.fixedSpace s)
      omega
    rw [Submodule.isCompl_iff_disjoint _ _ (by omega), Submodule.disjoint_def]
    intro v hvM hvW
    obtain ⟨v₁, hv₁, v₂, hv₂, rfl⟩ := Submodule.mem_sup.mp hvM
    have hav := CFSG.RankThree.PartOne.LIT.mem_fixedSpace.mp (Submodule.mem_inf.mp hvW).1
    have hsv := CFSG.RankThree.PartOne.LIT.mem_fixedSpace.mp (Submodule.mem_inf.mp hvW).2
    rw [map_add, has' v₂ hv₂] at hav
    rw [map_add, hsa v₁ hv₁] at hsv
    have h1 : a v₁ = v₁ := add_right_cancel hav
    have h2 : s v₂ = v₂ := add_left_cancel hsv
    have h1' : v₁ ∈ CFSG.RankThree.PartOne.LIT.fixedSpace a ⊓
        CFSG.RankThree.PartOne.LIT.commSpace a :=
      ⟨CFSG.RankThree.PartOne.LIT.mem_fixedSpace.mpr h1, hv₁⟩
    have h2' : v₂ ∈ CFSG.RankThree.PartOne.LIT.fixedSpace s ⊓
        CFSG.RankThree.PartOne.LIT.commSpace s :=
      ⟨CFSG.RankThree.PartOne.LIT.mem_fixedSpace.mpr h2, hv₂⟩
    rw [hcompl_a.inf_eq_bot, Submodule.mem_bot] at h1'
    rw [hcompl_s.inf_eq_bot, Submodule.mem_bot] at h2'
    rw [h1', h2', add_zero]
  have hW2 : finrank K ↥(CFSG.RankThree.PartOne.LIT.fixedSpace a ⊓
      CFSG.RankThree.PartOne.LIT.fixedSpace s) = 2 := by
    have := Submodule.finrank_add_eq_of_isCompl hMW
    rw [hdimM, hdim] at this
    omega
  have h2el : ∀ g ∈ orthDerived Q ⊓ Subgroup.centralizer ({a, s} : Set (V ≃ₗ[K] V)),
      ∀ k : ℕ, g ^ (2 ^ k) = 1 → g ∈ specialBlock Q s h := by
    rintro g ⟨hgΩ, hgC⟩ k hgk
    have hag : a * g = g * a := Subgroup.mem_centralizer_iff.mp hgC a (by simp)
    have hsg : s * g = g * s := Subgroup.mem_centralizer_iff.mp hgC s (by simp)
    have hgA := apply_eq_of_two_pow_commSpace hQ hp hp2 hK1 ha hap ha2 hag hgk
    have hgCs : g ∈ Subgroup.centralizer ({s} : Set (V ≃ₗ[K] V)) :=
      Subgroup.mem_centralizer_singleton_iff.mpr hsg.symm
    have hgM : g ∈ isometryCentralizer Q s :=
      Subgroup.mem_inf.mpr ⟨orthDerived_le_orthogonalGroup hgΩ, hgCs⟩
    obtain ⟨gh, hghdef⟩ : ∃ gh : V ≃ₗ[K] V, gh = (CFSG.RankThree.PartOne.KCOrthogonal.blockComponent hx ⟨g, hgCs⟩ h).1 :=
      ⟨_, rfl⟩
    have hghB : gh ∈ supportedBlock Q s h := hghdef ▸ hx.blockComponent_mem hgM hh
    have hgh_h : ∀ v ∈ CFSG.RankThree.PartOne.LIT.commSpace s, gh v = g v := by
      intro v hv
      rw [← hVh] at hv
      rw [hghdef, CFSG.RankThree.PartOne.KCOrthogonal.blockComponent_apply_of_mem hx _ h hh hv]
      simp
    have hgh_1 : ∀ v ∈ CFSG.RankThree.PartOne.LIT.fixedSpace s, gh v = v := hblockFix gh hghB
    have hgs : g * s = s * g := hsg.symm
    have hdec : ∀ v : V, ∃ v₀ ∈ CFSG.RankThree.PartOne.LIT.fixedSpace s,
        ∃ v₁ ∈ CFSG.RankThree.PartOne.LIT.commSpace s, v = v₀ + v₁ := by
      intro v
      have hv : v ∈ CFSG.RankThree.PartOne.LIT.fixedSpace s ⊔
          CFSG.RankThree.PartOne.LIT.commSpace s := by
        rw [hcompl_s.sup_eq_top]
        exact Submodule.mem_top
      obtain ⟨v₀, hv₀, v₁, hv₁, rfl⟩ := Submodule.mem_sup.mp hv
      exact ⟨v₀, hv₀, v₁, hv₁, rfl⟩
    have hcommg : g * gh = gh * g := by
      apply LinearEquiv.ext
      intro v
      obtain ⟨v₀, hv₀, v₁, hv₁, rfl⟩ := hdec v
      simp only [LinearEquiv.mul_apply, map_add]
      rw [hgh_1 v₀ hv₀, hgh_h v₁ hv₁, hgh_1 _ (hpresF g hgs v₀ hv₀),
        hgh_h _ (hpresC g hgs v₁ hv₁)]
    have hghpow : ∀ n : ℕ, ∀ v ∈ CFSG.RankThree.PartOne.LIT.commSpace s,
        (gh ^ n) v = (g ^ n) v := by
      intro n
      induction n with
      | zero => intro v _; rfl
      | succ n ih =>
        intro v hv
        rw [pow_succ, pow_succ, LinearEquiv.mul_apply, LinearEquiv.mul_apply, hgh_h v hv,
          ih _ (hpresC g hgs v hv)]
    have hghfix : ∀ n : ℕ, ∀ v ∈ CFSG.RankThree.PartOne.LIT.fixedSpace s, (gh ^ n) v = v := by
      intro n
      induction n with
      | zero => intro v _; rfl
      | succ n ih =>
        intro v hv
        rw [pow_succ, LinearEquiv.mul_apply, hgh_1 v hv, ih v hv]
    have hghk : gh ^ (2 ^ k) = 1 := by
      apply LinearEquiv.ext
      intro v
      obtain ⟨v₀, hv₀, v₁, hv₁, rfl⟩ := hdec v
      rw [map_add, hghfix _ v₀ hv₀, hghpow _ v₁ hv₁, hgk]
      simp
    haveI : Fact (Irreducible h) := ⟨irreducible_of_mem_primaryFactors hh⟩
    have hdet : blockDet Q s h ⟨gh, hghB⟩ = 1 := by
      have h2E : (2 : AdjoinRoot h) = 0 := by
        rw [← map_ofNat (algebraMap K (AdjoinRoot h)) 2, CharTwo.two_eq_zero, map_zero]
      have hpow : (blockDet Q s h ⟨gh, hghB⟩) ^ (2 ^ k) = 1 := by
        rw [← map_pow]
        have : (⟨gh, hghB⟩ : ↥(supportedBlock Q s h)) ^ (2 ^ k) = 1 :=
          Subtype.ext (by simpa using hghk)
        rw [this, map_one]
      have h0 : (blockDet Q s h ⟨gh, hghB⟩ - 1) ^ (2 ^ k) = 0 := by
        rw [sub_one_pow_two_pow' h2E, hpow, sub_self]
      exact sub_eq_zero.mp ((pow_eq_zero_iff (by positivity)).mp h0)
    have hghF : gh ∈ specialBlock Q s h := mem_specialBlock.mpr ⟨hghB, hdet⟩
    have hghΩ : gh ∈ orthDerived Q :=
      CFSG.HardMathSupport.Timmesfeld.CrossChar.orth3_specialBlock_le_orthDerived hx hp hp2 hK4 hh hne (by omega) hghF
    have hinv_cancel : ∀ u : V, gh⁻¹ (gh u) = u := fun u => by
      rw [← LinearEquiv.mul_apply, inv_mul_cancel]
      rfl
    have hg'C : ∀ v ∈ CFSG.RankThree.PartOne.LIT.commSpace s, (g * gh⁻¹) v = v := by
      intro v hv
      have hgi : g⁻¹ * s = s * g⁻¹ := (show Commute g s from hgs).inv_left
      have hu := hpresC g⁻¹ hgi v hv
      have hv' : gh (g⁻¹ v) = v := by
        rw [hgh_h _ hu, ← LinearEquiv.mul_apply, mul_inv_cancel]
        rfl
      rw [LinearEquiv.mul_apply, ← hv', hinv_cancel, hgh_h _ hu]
    have hg'A : ∀ v ∈ CFSG.RankThree.PartOne.LIT.commSpace a, (g * gh⁻¹) v = v := by
      intro v hv
      have hvF : v ∈ CFSG.RankThree.PartOne.LIT.fixedSpace s :=
        CFSG.RankThree.PartOne.LIT.mem_fixedSpace.mpr (hsa v hv)
      have h1 : gh⁻¹ v = v := by
        conv_lhs => rw [← hgh_1 v hvF]
        exact hinv_cancel v
      rw [LinearEquiv.mul_apply, h1, hgA v hv]
    have hcga : Commute a (g * gh⁻¹) :=
      (show Commute a g from hag).mul_right (show Commute a gh from hFa gh hghB).inv_right
    have hcgs : Commute s (g * gh⁻¹) :=
      (show Commute s g from hsg).mul_right (show Commute s gh from (hcs gh hghB).symm).inv_right
    have hg'W : ∀ v ∈ CFSG.RankThree.PartOne.LIT.fixedSpace a ⊓
        CFSG.RankThree.PartOne.LIT.fixedSpace s, (g * gh⁻¹) v ∈
          CFSG.RankThree.PartOne.LIT.fixedSpace a ⊓ CFSG.RankThree.PartOne.LIT.fixedSpace s := by
      intro v hv
      obtain ⟨hva, hvs⟩ := Submodule.mem_inf.mp hv
      rw [CFSG.RankThree.PartOne.LIT.mem_fixedSpace] at hva hvs
      refine Submodule.mem_inf.mpr ⟨?_, ?_⟩
      · rw [CFSG.RankThree.PartOne.LIT.mem_fixedSpace, ← LinearEquiv.mul_apply, hcga.eq,
          LinearEquiv.mul_apply, hva]
      · rw [CFSG.RankThree.PartOne.LIT.mem_fixedSpace, ← LinearEquiv.mul_apply, hcgs.eq,
          LinearEquiv.mul_apply, hvs]
    have hg'M : ∀ v ∈ CFSG.RankThree.PartOne.LIT.commSpace a ⊔
        CFSG.RankThree.PartOne.LIT.commSpace s, (g * gh⁻¹) v = v := by
      intro v hv
      obtain ⟨v₁, hv₁, v₂, hv₂, rfl⟩ := Submodule.mem_sup.mp hv
      rw [map_add, hg'A v₁ hv₁, hg'C v₂ hv₂]
    have hg'k : (g * gh⁻¹) ^ (2 ^ k) = 1 := by
      rw [(show Commute g gh⁻¹ from (show Commute g gh from hcommg).inv_right).mul_pow, hgk,
        inv_pow, hghk, inv_one, one_mul]
    have hg'Ω : g * gh⁻¹ ∈ orthDerived Q := mul_mem hgΩ (inv_mem hghΩ)
    have hev : Even (finrank K (CFSG.RankThree.OrthogonalInvolutions.commSpace (g * gh⁻¹))) :=
      (mem_omegaGroup.mp (CFSG.RankThree.PartOne.FieldFix.orthDerived_le_omegaGroup hQ hg'Ω)).2
    have hg'1 : g * gh⁻¹ = 1 := eq_one_of_two_pow_of_isCompl hMW hW2 hg'M hg'W hg'k hev
    have hggh : g = gh := by
      have := congrArg (· * gh) hg'1
      simpa using this
    rw [hggh]
    exact hghF
  have hE2 : (2 : E) = 0 := by
    haveI := Fintype.ofFinite K
    haveI := Fintype.ofFinite E
    obtain ⟨n, -, hn⟩ := FiniteField.card K 2
    have hcE : (Fintype.card E : E) = 0 := FiniteField.cast_card_eq_zero E
    rw [← Nat.card_eq_fintype_card, hEcard, Nat.card_eq_fintype_card, hn, Nat.cast_pow,
      Nat.cast_ofNat] at hcE
    exact (pow_eq_zero_iff (by positivity)).mp hcE
  exact ggOTwoPrime_eq_of_le hSC (le_closure_two_of_mulEquiv eE (sl2_closure_sq_eq_one hE2)) h2el

end Transp

section Pieces

variable {K : Type} [Field K] [Finite K] [CharP K 2] {V : Type} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V}

theorem minpoly_plane {D : Type} [AddCommGroup D] [Module K D] [FiniteDimensional K D]
    (hD : finrank K D = 2) {p : ℕ} (hK1 : ∀ c : K, c ^ p = 1 → c = 1) {c : D ≃ₗ[K] D}
    (hcp : c ^ p = 1) (hcfix : ∀ u, c u = u → u = 0) :
    Irreducible (minpoly K (c : Module.End K D)) ∧
      (minpoly K (c : Module.End K D)).natDegree = 2 ∧
      ∀ μ : K, ¬ (minpoly K (c : Module.End K D)).IsRoot μ := by
  have hnoroot : ∀ μ : K, ¬ (minpoly K (c : Module.End K D)).IsRoot μ := by
    intro μ hμ
    have hev : Module.End.HasEigenvalue (c : Module.End K D) μ :=
      Module.End.hasEigenvalue_iff_isRoot.mpr hμ
    obtain ⟨d, hd⟩ := hev.exists_hasEigenvector
    have hcd : c d = μ • d := hd.apply_eq_smul
    have hpow : ∀ n : ℕ, (c ^ n) d = μ ^ n • d := by
      intro n
      induction n with
      | zero => simp
      | succ n ih =>
        rw [pow_succ, LinearEquiv.mul_apply, hcd, map_smul, ih, smul_smul, pow_succ, mul_comm]
    have h1 : μ ^ p • d = d := by rw [← hpow p, hcp]; rfl
    have hμp : μ ^ p = 1 := by
      by_contra hne
      have : (μ ^ p - 1) • d = 0 := by rw [sub_smul, h1, one_smul, sub_self]
      exact hd.2 ((smul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr hne))
    rw [hK1 μ hμp, one_smul] at hcd
    exact hd.2 (hcfix d hcd)
  have hint : IsIntegral K (c : Module.End K D) := Algebra.IsIntegral.isIntegral _
  have hle : (minpoly K (c : Module.End K D)).natDegree ≤ 2 := by
    have := Polynomial.natDegree_le_of_dvd (LinearMap.minpoly_dvd_charpoly (c : Module.End K D))
      (LinearMap.charpoly_monic _).ne_zero
    rwa [LinearMap.charpoly_natDegree, hD] at this
  have hpos : 0 < (minpoly K (c : Module.End K D)).natDegree := by
    haveI : Nontrivial D := Module.nontrivial_of_finrank_pos (R := K) (by omega)
    exact minpoly.natDegree_pos hint
  have h2 : (minpoly K (c : Module.End K D)).natDegree = 2 := by
    by_contra hne
    have h1 : (minpoly K (c : Module.End K D)).natDegree = 1 := by omega
    obtain ⟨μ, hμ⟩ := Polynomial.exists_root_of_degree_eq_one
      ((Polynomial.degree_eq_iff_natDegree_eq_of_pos one_pos).mpr h1)
    exact hnoroot μ hμ
  exact ⟨Polynomial.irreducible_of_degree_le_three_of_not_isRoot (by rw [h2]; decide) hnoroot,
    h2, hnoroot⟩

theorem aeval_apply_of_intertwine {D : Type} [AddCommGroup D] [Module K D] (θ : D →ₗ[K] V)
    (T : Module.End K V) (c : Module.End K D) (hθ : ∀ d, T (θ d) = θ (c d)) (f : K[X])
    (d : D) : aeval T f (θ d) = θ (aeval c f d) := by
  revert d
  refine Polynomial.induction_on f (fun a d => ?_) (fun f g hf hg d => ?_) (fun n a ih d => ?_)
  · simp only [Polynomial.aeval_C, Algebra.algebraMap_eq_smul_one, LinearMap.smul_apply,
      Module.End.one_apply, map_smul]
  · simp only [map_add, LinearMap.add_apply, hf, hg]
  · have h : (Polynomial.C a * X ^ (n + 1) : K[X]) = Polynomial.C a * X ^ n * X := by ring
    have hT : aeval T (Polynomial.C a * X ^ n * X) = aeval T (Polynomial.C a * X ^ n) * T := by
      rw [map_mul, aeval_X]
    have hc : aeval c (Polynomial.C a * X ^ n * X) = aeval c (Polynomial.C a * X ^ n) * c := by
      rw [map_mul, aeval_X]
    rw [h, hT, hc, Module.End.mul_apply, Module.End.mul_apply, hθ, ih]

theorem primary_of_pair (hQ : (polarBilin Q).Nondegenerate) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hK1 : ∀ c : K, c ^ p = 1 → c = 1) {E : Subgroup (V ≃ₗ[K] V)}
    (hEΩ : E ≤ orthDerived Q) (hpowE : ∀ a ∈ E, a ^ p = 1)
    {τ : (Fin 3 → Multiplicative (ZMod p)) →* (V ≃ₗ[K] V)} (hτrange : τ.range = E)
    {F : SevOm.Frame Q p E 3} (hτ : ∀ f, τ f = F.ι (OrthTorus.piMul 3 p f))
    {D : Type} [AddCommGroup D] [Module K D] [FiniteDimensional K D] {c : D ≃ₗ[K] D}
    {θ : Fin 3 → D →ₗ[K] V} (hD2 : finrank K D = 2) (hcp : c ^ p = 1)
    (hcfix : ∀ u, c u = u → u = 0) (hctw : ∃ T : D ≃ₗ[K] D, T * c * T⁻¹ = c⁻¹)
    (hθinj : ∀ j, Function.Injective (θ j)) (hθrange : ∀ j, LinearMap.range (θ j) = F.U j)
    (hθact : ∀ (s : Multiplicative (Fin 3 → ZMod p)) (j : Fin 3) (d : D),
      F.ι s (θ j d) = θ j ((c ^ (toAdd s j).val) d))
    (hU2 : ∀ j, finrank K (F.U j) = 2)
    (hcU : ∀ (j : Fin 3) (a : ZMod p), a ≠ 0 →
      CFSG.RankThree.PartOne.LIT.commSpace (τ (Pi.mulSingle j (ofAdd a))) = F.U j)
    {k l : Fin 3} (hkl : k ≠ l) {η : ZMod p} (hη : η = 1 ∨ η = -1) :
    CFSG.RankThree.PartOne.LIT.commSpace
        (τ (Pi.mulSingle k (ofAdd 1) * Pi.mulSingle l (ofAdd η))) = F.U k ⊔ F.U l ∧
      finrank K (CFSG.RankThree.PartOne.LIT.commSpace
        (τ (Pi.mulSingle k (ofAdd 1) * Pi.mulSingle l (ofAdd η)))) = 4 ∧
      ∃ h : K[X],
        h ∈ primaryFactors (τ (Pi.mulSingle k (ofAdd 1) * Pi.mulSingle l (ofAdd η))).toLinearMap ∧
        h ≠ X - 1 ∧
        primaryMultiplicity
          (τ (Pi.mulSingle k (ofAdd 1) * Pi.mulSingle l (ofAdd η))).toLinearMap h = 2 ∧
        primaryComponent (τ (Pi.mulSingle k (ofAdd 1) * Pi.mulSingle l (ofAdd η))).toLinearMap h =
          CFSG.RankThree.PartOne.LIT.commSpace
            (τ (Pi.mulSingle k (ofAdd 1) * Pi.mulSingle l (ofAdd η))) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  set f : Fin 3 → Multiplicative (ZMod p) := Pi.mulSingle k (ofAdd 1) * Pi.mulSingle l (ofAdd η)
    with hfdef
  set s := τ f with hsdef
  have hη0 : η ≠ 0 := by
    rcases hη with rfl | rfl
    · exact one_ne_zero
    · exact neg_ne_zero.mpr one_ne_zero
  have hpK : (p : K) ≠ 0 := OrthRestOdd.natCast_ne_zero_of_odd hp hp2
  have hmemE : ∀ g, τ g ∈ E := fun g => hτrange ▸ ⟨g, rfl⟩
  have hsx : OddOrderIsometry Q p s :=
    oddOrderIsometry_of_orthDerived hQ hp hp2 (t := ⟨s, hEΩ (hmemE f)⟩)
      (Subtype.ext (by simpa using hpowE _ (hmemE f)))
  have htriv : ∀ (g : Fin 3 → Multiplicative (ZMod p)) (m : Fin 3), g m = 1 →
      ∀ u ∈ F.U m, τ g u = u := by
    intro g m hgm u hu
    rw [hτ]
    refine F.triv _ m ?_ u hu
    rw [OrthTorus.piMul_apply, toAdd_ofAdd]
    simp [hgm]
  set a := τ (Pi.mulSingle k (ofAdd 1)) with hadef
  set b := τ (Pi.mulSingle l (ofAdd η)) with hbdef
  have hsab : s = a * b := by rw [hsdef, hfdef, map_mul]
  have ha : CFSG.RankThree.PartOne.LIT.commSpace a = F.U k := hcU k 1 one_ne_zero
  have hb : CFSG.RankThree.PartOne.LIT.commSpace b = F.U l := hcU l η hη0
  have hba : ∀ v ∈ CFSG.RankThree.PartOne.LIT.commSpace a, b v = v := by
    rw [ha]
    exact htriv _ k (Pi.mulSingle_eq_of_ne hkl _)
  have hab' : ∀ v ∈ CFSG.RankThree.PartOne.LIT.commSpace b, a v = v := by
    rw [hb]
    exact htriv _ l (Pi.mulSingle_eq_of_ne (Ne.symm hkl) _)
  have hap : a ^ p = 1 := hpowE _ (hmemE _)
  have hbp : b ^ p = 1 := hpowE _ (hmemE _)
  have habc : a * b = b * a := by
    rw [hadef, hbdef, ← map_mul, ← map_mul, mul_comm]
  have hcs : CFSG.RankThree.PartOne.LIT.commSpace s = F.U k ⊔ F.U l := by
    rw [hsab, ← ha, ← hb]
    apply le_antisymm (commSpace_mul_le a b)
    apply sup_le (le_commSpace_mul hpK hap hba)
    rw [habc]
    exact le_commSpace_mul hpK hbp hab'
  have hdisj : F.U k ⊓ F.U l = ⊥ := by
    rw [← ha, ← hb, eq_bot_iff]
    rintro v ⟨hva, hvb⟩
    have hc := (CFSG.RankThree.PartOne.LIT.isCompl_fixedSpace_commSpace hpK hbp).inf_eq_bot
    have : v ∈ CFSG.RankThree.PartOne.LIT.fixedSpace b ⊓
        CFSG.RankThree.PartOne.LIT.commSpace b :=
      ⟨CFSG.RankThree.PartOne.LIT.mem_fixedSpace.mpr (hba v hva), hvb⟩
    rw [hc] at this
    exact this
  have h4 := Submodule.finrank_sup_add_finrank_inf_eq (F.U k) (F.U l)
  rw [hdisj, finrank_bot, add_zero, hU2, hU2] at h4
  have hcs4 : finrank K (CFSG.RankThree.PartOne.LIT.commSpace s) = 4 := by
    rw [hcs]
    omega
  refine ⟨hcs, hcs4, ?_⟩
  obtain ⟨hirr, hdeg, hnoroot⟩ := minpoly_plane hD2 hK1 hcp hcfix
  set h := minpoly K (c : Module.End K D) with hhdef
  have hch : aeval (c : Module.End K D) h = 0 := minpoly.aeval K _
  have hcinv : aeval ((c⁻¹ : D ≃ₗ[K] D) : Module.End K D) h = 0 := by
    obtain ⟨T, hT⟩ := hctw
    have hTc : ∀ d, ((c⁻¹ : D ≃ₗ[K] D) : Module.End K D) ((T : D →ₗ[K] D) d) =
        (T : D →ₗ[K] D) ((c : Module.End K D) d) := by
      intro d
      have := congrArg (fun z : D ≃ₗ[K] D => z (T d)) hT
      simp only [LinearEquiv.mul_apply] at this
      rw [LinearEquiv.coe_coe, LinearEquiv.coe_coe, LinearEquiv.coe_coe, ← this]
      congr 2
      rw [← LinearEquiv.mul_apply, inv_mul_cancel]
      rfl
    apply LinearMap.ext
    intro d
    obtain ⟨d', rfl⟩ := T.surjective d
    have := aeval_apply_of_intertwine (V := D) (T : D →ₗ[K] D) _ _ hTc h d'
    rw [LinearEquiv.coe_coe] at this
    rw [this, hch, LinearMap.zero_apply, map_zero, LinearMap.zero_apply]
  have hval1 : (1 : ZMod p).val = 1 := ZMod.val_one'' hp.ne_one
  have hsk : ∀ d, (s : Module.End K V) (θ k d) = θ k ((c : Module.End K D) d) := by
    intro d
    rw [LinearEquiv.coe_coe, hsdef, hτ, hθact]
    congr 2
    rw [OrthTorus.piMul_apply, toAdd_ofAdd]
    simp [hfdef, Pi.mulSingle_eq_of_ne hkl, hval1]
  have hcη : aeval ((c ^ (toAdd (f l)).val : D ≃ₗ[K] D) : Module.End K D) h = 0 := by
    have hfl : toAdd (f l) = η := by
      simp [hfdef, Pi.mulSingle_eq_of_ne (Ne.symm hkl)]
    rw [hfl]
    rcases hη with rfl | rfl
    · rw [hval1, pow_one]
      exact hch
    · have hcp' : c ^ ((-1 : ZMod p).val) = c⁻¹ := by
        have hv : (-1 : ZMod p).val = p - 1 := by
          rw [ZMod.val_neg_of_ne_zero, ZMod.val_one'' hp.ne_one]
        rw [hv, eq_inv_iff_mul_eq_one, ← pow_succ, Nat.sub_add_cancel hp.one_le, hcp]
      rw [hcp']
      exact hcinv
  have hsl : ∀ d, (s : Module.End K V) (θ l d) =
      θ l (((c ^ (toAdd (f l)).val : D ≃ₗ[K] D) : Module.End K D) d) := by
    intro d
    rw [LinearEquiv.coe_coe, hsdef, hτ, hθact]
    congr 2
  have hkill : ∀ (j : Fin 3) (cj : Module.End K D), aeval cj h = 0 →
      (∀ d, (s : Module.End K V) (θ j d) = θ j (cj d)) →
      F.U j ≤ primaryComponent s.toLinearMap h := by
    intro j cj hcj hsj v hv
    rw [← hθrange j] at hv
    obtain ⟨d, rfl⟩ := hv
    rw [mem_primaryComponent]
    have := aeval_apply_of_intertwine (θ j) (s : Module.End K V) cj hsj h d
    rw [show s.toLinearMap = (s : Module.End K V) from rfl, this, hcj, LinearMap.zero_apply,
      map_zero]
  have hle : F.U k ⊔ F.U l ≤ primaryComponent s.toLinearMap h :=
    sup_le (hkill k _ hch hsk) (hkill l _ hcη hsl)
  have hdvd : h ∣ minpoly K s.toLinearMap := by
    apply minpoly.dvd
    apply LinearMap.ext
    intro d
    apply hθinj k
    rw [LinearMap.zero_apply, map_zero]
    have := aeval_apply_of_intertwine (θ k) (s : Module.End K V) _ hsk
      (minpoly K s.toLinearMap) d
    rw [← this]
    have h0 := minpoly.aeval K s.toLinearMap
    rw [show s.toLinearMap = (s : Module.End K V) from rfl] at h0
    rw [h0, LinearMap.zero_apply]
  have hh : h ∈ primaryFactors s.toLinearMap :=
    mem_primaryFactors.mpr ⟨hirr, minpoly.monic (Algebra.IsIntegral.isIntegral _), hdvd⟩
  have hne : h ≠ X - 1 := by
    intro he
    apply hnoroot 1
    rw [he]
    simp
  have hVh : primaryComponent s.toLinearMap h = CFSG.RankThree.PartOne.LIT.commSpace s := by
    apply le_antisymm (OrthRestOdd.primaryComponent_le_commSpace hsx hh hne)
    rw [hcs]
    exact hle
  refine ⟨h, hh, hne, ?_, hVh⟩
  haveI : Fact (Irreducible h) := ⟨hirr⟩
  have h4' : finrank K ↥(primaryComponent s.toLinearMap h) = 4 := by
    rw [hVh]
    exact hcs4
  have hfin := finrank_primaryComponent (x := s.toLinearMap) (a := h)
  rw [h4', hdeg] at hfin
  change 4 = 2 * primaryMultiplicity s.toLinearMap h at hfin
  omega

end Pieces

section Refl

variable {p : ℕ}

theorem spAct_reflection_cases [Fact p.Prime] (hp2 : p ≠ 2) {π : Equiv.Perm (Fin 3)}
    {ε : Fin 3 → ZMod p} (hε : ∀ i, ε i = 1 ∨ ε i = -1)
    (h2 : ∀ v, spAct π ε (spAct π ε v) = v)
    (hcard : Nat.card {v : Fin 3 → ZMod p // spAct π ε v = v} = p ^ 2) :
    (π = 1 ∧ ∃ j, ε j = -1 ∧ ∀ i, i ≠ j → ε i = 1) ∨
      ∃ i j k : Fin 3, i ≠ j ∧ i ≠ k ∧ j ≠ k ∧ π i = i ∧ π j = k ∧ π k = j ∧ ε j = ε k ∧
        ε i = 1 := by
  classical
  have hp : p.Prime := Fact.out
  have h2p : (2 : ZMod p) ≠ 0 := two_ne_zero_zmod hp2
  have hneg : ∀ a : ZMod p, -a = a → a = 0 := fun a h => by
    have h' : 2 * a = 0 := by linear_combination -h
    exact (mul_eq_zero.mp h').resolve_left h2p
  have hone : (1 : ZMod p) ≠ -1 := fun h => one_ne_zero (hneg 1 h.symm)
  have hsmall : ∀ m : Fin 3, (∀ v w : Fin 3 → ZMod p, spAct π ε v = v → spAct π ε w = w →
      v m = w m → v = w) → False := by
    intro m hdet
    have hinj : Function.Injective
        (fun v : {v : Fin 3 → ZMod p // spAct π ε v = v} => v.1 m) := fun v w h =>
      Subtype.ext (hdet v.1 w.1 v.2 w.2 h)
    have hle := Nat.card_le_card_of_injective _ hinj
    rw [hcard, Nat.card_zmod] at hle
    have hp2' : 2 ≤ p := hp.two_le
    nlinarith
  have hππ : π * π = 1 := perm_eq_one_of_spAct ⟨fun i => ε (π i) * ε i, fun v => by
    rw [← spAct_spAct]
    exact h2 v⟩
  by_cases hπ1 : π = 1
  · subst hπ1
    left
    refine ⟨rfl, ?_⟩
    have hfix : ∀ v : Fin 3 → ZMod p, spAct 1 ε v = v → ∀ k, ε k = -1 → v k = 0 := by
      intro v hv k hk
      have := congrFun hv k
      rw [spAct_one_apply, hk, neg_one_mul] at this
      exact hneg _ this
    by_cases hall : ∀ k, ε k = 1
    · exfalso
      have heq : ∀ v : Fin 3 → ZMod p, spAct 1 ε v = v := fun v => by
        funext k
        rw [spAct_one_apply, hall k, one_mul]
      have hc : Nat.card {v : Fin 3 → ZMod p // spAct 1 ε v = v} = p ^ 3 := by
        rw [Nat.card_congr (Equiv.subtypeUnivEquiv heq), Nat.card_fun, Nat.card_zmod,
          Nat.card_fin]
      rw [hc] at hcard
      have := Nat.pow_right_injective hp.two_le hcard
      omega
    · push Not at hall
      obtain ⟨j, hj⟩ := hall
      have hj' : ε j = -1 := (hε j).resolve_left hj
      refine ⟨j, hj', fun i hij => ?_⟩
      by_contra hi
      have hi' : ε i = -1 := (hε i).resolve_left hi
      obtain ⟨m, hmi, hmj⟩ : ∃ m : Fin 3, m ≠ i ∧ m ≠ j :=
        (by decide : ∀ i j : Fin 3, i ≠ j → ∃ m : Fin 3, m ≠ i ∧ m ≠ j) i j hij
      apply hsmall m
      intro v w hv hw hvw
      funext l
      rcases fin_three_cases hij hmi.symm hmj.symm l with rfl | rfl | rfl
      · rw [hfix v hv _ hi', hfix w hw _ hi']
      · rw [hfix v hv _ hj', hfix w hw _ hj']
      · exact hvw
  · right
    obtain ⟨i, j, k, hij, hik, hjk, hi, hj, hk⟩ := perm_three_swap π hππ hπ1
    have hcoord : ∀ v : Fin 3 → ZMod p, spAct π ε v k = ε j * v j ∧
        spAct π ε v j = ε k * v k ∧ spAct π ε v i = ε i * v i := fun v =>
      ⟨spAct_apply_of_eq hj ε v, spAct_apply_of_eq hk ε v, spAct_apply_of_eq hi ε v⟩
    have hεjk : ε j = ε k := by
      have h := congrFun (h2 (Pi.single j 1)) j
      rw [(hcoord _).2.1, (hcoord _).1, Pi.single_eq_same, mul_one] at h
      rcases hε j with h1 | h1 <;> rcases hε k with h3 | h3 <;> rw [h1, h3] at h ⊢
      all_goals first | rfl | exact absurd (by linear_combination -h) hone
    have hεi : ε i = 1 := by
      by_contra hne
      have hi' : ε i = -1 := (hε i).resolve_left hne
      apply hsmall j
      intro v w hv hw hvw
      have hvi : v i = 0 := hneg _ (by
        have := congrFun hv i
        rwa [(hcoord v).2.2, hi', neg_one_mul] at this)
      have hwi : w i = 0 := hneg _ (by
        have := congrFun hw i
        rwa [(hcoord w).2.2, hi', neg_one_mul] at this)
      have hvk : v k = ε j * v j := by
        have := congrFun hv k
        rw [(hcoord v).1] at this
        exact this.symm
      have hwk : w k = ε j * w j := by
        have := congrFun hw k
        rw [(hcoord w).1] at this
        exact this.symm
      funext l
      rcases fin_three_cases hij hik hjk l with rfl | rfl | rfl
      · rw [hvi, hwi]
      · exact hvw
      · rw [hvk, hwk, hvw]
    exact ⟨i, j, k, hij, hik, hjk, hi, hj, hk, hεjk, hεi⟩

end Refl

section Orders

variable {p : ℕ}

@[expose] def IsSign (ε : Fin 3 → ZMod p) : Prop := ∀ i, ε i = 1 ∨ ε i = -1

theorem isSign_comp {π : Equiv.Perm (Fin 3)} {ε ε' : Fin 3 → ZMod p} (hε : IsSign ε)
    (hε' : IsSign ε') : IsSign (fun i => ε (π i) * ε' i) := by
  intro i
  show ε (π i) * ε' i = 1 ∨ ε (π i) * ε' i = -1
  rcases hε (π i) with h | h <;> rcases hε' i with h' | h' <;> rw [h, h'] <;> simp

theorem spAct_one_one {θ : Fin 3 → ZMod p} (hθ : IsSign θ) (v : Fin 3 → ZMod p) :
    spAct 1 θ (spAct 1 θ v) = v := by
  funext k
  rw [spAct_one_apply, spAct_one_apply, ← mul_assoc]
  rcases hθ k with h | h <;> rw [h] <;> ring

theorem spAct_sq_of_diag {ε ε' : Fin 3 → ZMod p} (hε : IsSign ε) (hε' : IsSign ε')
    (v : Fin 3 → ZMod p) :
    spAct 1 ε (spAct 1 ε' (spAct 1 ε (spAct 1 ε' v))) = v := by
  have h : ∀ w, spAct 1 ε (spAct 1 ε' w) = spAct 1 (fun i => ε i * ε' i) w := by
    intro w
    rw [spAct_spAct, one_mul]
    rfl
  rw [h, h]
  exact spAct_one_one (isSign_comp (π := 1) hε hε') v

theorem spAct_four_of_diag {π' : Equiv.Perm (Fin 3)} {ε ε' : Fin 3 → ZMod p} (hε : IsSign ε)
    (hε' : IsSign ε') (hπ' : π' * π' = 1) (v : Fin 3 → ZMod p) :
    spAct 1 ε (spAct π' ε' (spAct 1 ε (spAct π' ε' (spAct 1 ε (spAct π' ε'
      (spAct 1 ε (spAct π' ε' v))))))) = v := by
  set η : Fin 3 → ZMod p := fun i => ε (π' i) * ε' i with hη
  have hηs : IsSign η := isSign_comp hε hε'
  have h1 : ∀ w, spAct 1 ε (spAct π' ε' w) = spAct π' η w := by
    intro w
    rw [spAct_spAct, one_mul]
  have h2 : ∀ w, spAct π' η (spAct π' η w) = spAct 1 (fun i => η (π' i) * η i) w := by
    intro w
    rw [spAct_spAct, hπ']
  rw [h1, h1, h1, h1, h2, h2]
  exact spAct_one_one (isSign_comp hηs hηs) v

theorem perm_three_cube : ∀ π π' : Equiv.Perm (Fin 3), π * π = 1 → π ≠ 1 → π' * π' = 1 →
    π' ≠ 1 → (π * π') ^ 3 = 1 := by
  decide

theorem spAct_six_of_swaps {π π' : Equiv.Perm (Fin 3)} {ε ε' : Fin 3 → ZMod p}
    (hε : IsSign ε) (hε' : IsSign ε') (hπ : π * π = 1) (hπ1 : π ≠ 1) (hπ' : π' * π' = 1)
    (hπ'1 : π' ≠ 1) (v : Fin 3 → ZMod p) :
    (fun w => spAct π ε (spAct π' ε' w))^[6] v = v := by
  set ρ := π * π' with hρ
  set η : Fin 3 → ZMod p := fun i => ε (π' i) * ε' i with hη
  have hηs : IsSign η := isSign_comp hε hε'
  have h1 : ∀ w, spAct π ε (spAct π' ε' w) = spAct ρ η w := fun w => spAct_spAct _ _ _ _ _
  have hρ3 : ρ ^ 3 = 1 := perm_three_cube π π' hπ hπ1 hπ' hπ'1
  set θ : Fin 3 → ZMod p := fun i => η (ρ (ρ i)) * η (ρ i) * η i with hθ
  have hθs : IsSign θ := fun i => by
    show η (ρ (ρ i)) * η (ρ i) * η i = 1 ∨ η (ρ (ρ i)) * η (ρ i) * η i = -1
    rcases hηs (ρ (ρ i)) with h1 | h1 <;> rcases hηs (ρ i) with h2 | h2 <;>
      rcases hηs i with h3 | h3 <;> simp [h1, h2, h3]
  have h3 : ∀ w, spAct ρ η (spAct ρ η (spAct ρ η w)) = spAct 1 θ w := by
    intro w
    rw [spAct_spAct, spAct_spAct]
    have hρ3' : ρ * ρ * ρ = 1 := by rw [← pow_three', hρ3]
    rw [hρ3']
  simp only [Function.iterate_succ, Function.iterate_zero, Function.comp_apply, id_eq, h1]
  rw [h3, h3]
  exact spAct_one_one hθs v

end Orders

end OmPlusFrame

end CFSG.StandardType

end
