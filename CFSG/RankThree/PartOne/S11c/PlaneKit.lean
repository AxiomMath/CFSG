module

public import CFSG.RankThree.PartOne.S11.CatalogLeaves
public import CFSG.RankThree.GroupTheory.SteinbergBMMovingPlaneTwoSubgroupObstruction

public section

namespace CFSG.RankThree.PartOne

open Subgroup CFSG CFSG.RankThree.GroupTheory

@[expose] def PlaneRBoundMove (T : Type) [Group T] (p k : ℕ) : Prop :=
  ∀ b f : T, orderOf b = p → orderOf f = p → b * f = f * b → f ∉ Subgroup.zpowers b →
    ∀ R : Subgroup T, IsPGroup 2 R → R ≤ centralizer ({b} : Set T) →
      (∀ r ∈ R, f * r * f⁻¹ ∈ R) → (∃ r ∈ R, f * r * f⁻¹ ≠ r) →
      (p = 7 → Nat.card R = 8 → IsElementaryAbelian 2 R) → Nat.card R ≤ k

theorem isElementaryAbelian_of_card_frattini_quotient {U : Type*} [Group U] [Finite U]
    (R : Subgroup U) (hVel : IsElementaryAbelian 2 (R ⧸ frattini R))
    (hcard : Nat.card (R ⧸ frattini R) = Nat.card R) : IsElementaryAbelian 2 R := by
  have hF : frattini R = ⊥ := by
    have h := card_eq_card_quotient_mul_card_subgroup (frattini R)
    rw [hcard] at h
    have h1 : Nat.card (frattini R) = 1 := by
      have := Nat.eq_of_mul_eq_mul_left (Nat.card_pos (α := R)) (h.symm.trans (mul_one _).symm)
      exact this
    exact card_eq_one.mp h1
  have hcommR : ∀ x y : R, x * y = y * x := by
    intro x y
    have h := hVel.toIsMulCommutative.is_comm.comm (x : R ⧸ frattini R) y
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq, hF, mem_bot] at h
    exact inv_mul_eq_one.mp h
  have hsq : ∀ x : R, x ^ 2 = 1 := by
    intro x
    have h := Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p 2 (R ⧸ frattini R)) (x : R ⧸ frattini R)
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, hF, mem_bot] at h
    exact h
  exact { toIsMulCommutative := ⟨⟨hcommR⟩⟩
          exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one hsq }

@[expose] def CentralizerTwoPartLe (T : Type) [Group T] (p k : ℕ) : Prop :=
  ∀ b : T, orderOf b = p → ∀ R : Subgroup T, IsPGroup 2 R → R ≤ centralizer ({b} : Set T) →
    Nat.card R ≤ k

theorem planeCentralizes_of_planeRBoundMove {T : Type} [Group T] [Finite T]
    (hcenter : Subgroup.center T = ⊥) {p k : ℕ}
    (hk : (p = 5 ∧ k < 16) ∨ (p = 7 ∧ k < 8) ∨ (p = 11 ∧ k < 1024))
    (hinner : ∀ α : MulAut T, α ^ p = 1 → ∃ b : T, MulAut.conj b = α)
    (hbound : PlaneRBoundMove T p k) {E : Subgroup (MulAut T)} {U : Subgroup T}
    (hpl : PlaneOn p E U) : PlaneCentralizes E U := by
  classical
  have hp : p.Prime := hpl.prime
  have hp2 : p ≠ 2 := by
    have := hpl.three_lt
    omega
  have : Fact p.Prime := ⟨hp⟩
  have hEel : IsElementaryAbelian p E := hpl.elementary
  have hEcard : Nat.card E = p ^ 2 := hpl.card
  have hU2 : IsPGroup 2 U := hpl.two_group
  have hEU := hpl.normalized
  have hconj_inj : Function.Injective (MulAut.conj : T →* MulAut T) := by
    intro a c hac
    have hz : c⁻¹ * a ∈ Subgroup.center T := by
      rw [Subgroup.mem_center_iff]
      intro x
      have h : a * x * a⁻¹ = c * x * c⁻¹ := by
        simpa only [MulAut.conj_apply] using congrArg (fun φ : MulAut T => φ x) hac
      calc x * (c⁻¹ * a) = c⁻¹ * (c * x * c⁻¹) * a := by group
        _ = c⁻¹ * (a * x * a⁻¹) * a := by rw [h]
        _ = c⁻¹ * a * x := by group
    rw [hcenter, Subgroup.mem_bot, inv_mul_eq_one] at hz
    exact hz.symm
  intro e0 he0 u0 hu0
  by_contra hne
  have hinv : CFSG.IsInvariant E T U :=
    ⟨fun a g => ⟨fun hg => hEU a a.2 g hg, fun hg => by
      have h1 := hEU (a⁻¹ : E) (a⁻¹).2 ((a : MulAut T) g) hg
      have h2 : ((a⁻¹ : E) : MulAut T) ((a : MulAut T) g) = g := by
        change ((a : MulAut T)⁻¹ * (a : MulAut T)) g = g
        rw [inv_mul_cancel]
        rfl
      rwa [h2] at h1⟩⟩
  have hcomm : commutatorAction ↥E ↥U ≠ ⊥ := by
    intro h0
    have hmem : (⟨u0, hu0⟩ : U)⁻¹ * ((⟨e0, he0⟩ : E) • (⟨u0, hu0⟩ : U)) ∈
        commutatorAction ↥E ↥U :=
      Subgroup.subset_closure ⟨⟨e0, he0⟩, ⟨u0, hu0⟩, Subgroup.mem_top _, rfl⟩
    rw [h0, Subgroup.mem_bot, inv_mul_eq_one] at hmem
    exact hne (congrArg Subtype.val hmem.symm)
  obtain ⟨R, hR, D, hDcard, -, hRne, -, ⟨-, hVel, -⟩, ⟨d, hd⟩, hGL, h5, h7, h11, -, hβfix,
      hγmove⟩ :=
    SteinbergBM.moving_large_prime_plane_two_subgroup_fixed_line_and_small_order_obstruction hp hp2
      hEcard hU2 hcomm
  have hRlow : k < Nat.card R := by
    rcases hk with ⟨h, hk⟩ | ⟨h, hk⟩ | ⟨h, hk⟩
    · exact lt_of_lt_of_le hk (h5 h)
    · exact lt_of_lt_of_le hk (h7 h)
    · exact lt_of_lt_of_le hk (h11 h)
  obtain ⟨β, hβD, hβ1⟩ : ∃ b ∈ D, b ≠ 1 := by
    by_contra h
    push Not at h
    have hD : D = ⊥ := (Subgroup.eq_bot_iff_forall D).mpr h
    rw [hD, Subgroup.card_bot] at hDcard
    exact hp.one_lt.ne hDcard
  obtain ⟨γ, hγD⟩ : ∃ γ : E, γ ∉ D := by
    by_contra h
    push Not at h
    have hle : Nat.card E ≤ Nat.card D := by
      have : (⊤ : Subgroup E) ≤ D := fun x _ => h x
      have h2 := Subgroup.card_le_of_le this
      rwa [Subgroup.card_top] at h2
    rw [hEcard, hDcard] at hle
    have : p < p ^ 2 := by nlinarith [hp.two_le]
    omega
  have hβp : (β : MulAut T) ^ p = 1 := elemPow_eq_one_of_isElementaryAbelian _ β.2
  have hγp : (γ : MulAut T) ^ p = 1 := elemPow_eq_one_of_isElementaryAbelian _ γ.2
  obtain ⟨b, hb⟩ := hinner (β : MulAut T) hβp
  obtain ⟨f, hf⟩ := hinner (γ : MulAut T) hγp
  have hord : ∀ (x : T) (e : E), MulAut.conj x = (e : MulAut T) → e ≠ 1 → e ^ p = 1 →
      orderOf x = p := by
    intro x e hx he1 hep
    have hxp : x ^ p = 1 := by
      apply hconj_inj
      rw [map_pow, hx, map_one]
      exact congrArg Subtype.val hep
    rcases (Nat.dvd_prime hp).mp (orderOf_dvd_of_pow_eq_one hxp) with h | h
    · exfalso
      apply he1
      apply Subtype.ext
      rw [← hx, orderOf_eq_one_iff.mp h, map_one]
      rfl
    · exact h
  have hβpE : β ^ p = 1 := Subtype.ext hβp
  have hγpE : γ ^ p = 1 := Subtype.ext hγp
  have hγ1 : γ ≠ 1 := fun h => hγD (h ▸ D.one_mem)
  have hbord : orderOf b = p := hord b β hb hβ1 hβpE
  have hford : orderOf f = p := hord f γ hf hγ1 hγpE
  have hbf : b * f = f * b := by
    apply hconj_inj
    rw [map_mul, map_mul, hb, hf]
    have := hEel.is_comm.comm β γ
    exact congrArg Subtype.val this
  have hfb : f ∉ Subgroup.zpowers b := by
    rintro ⟨i, hi⟩
    apply hγD
    have h1 : (γ : MulAut T) = (β : MulAut T) ^ i := by
      rw [← hf, ← hb, ← hi, map_zpow]
    have h2 : γ = β ^ i := Subtype.ext (by simpa using h1)
    rw [h2]
    exact D.zpow_mem hβD i
  set R' : Subgroup T := R.map U.subtype with hR'
  have hR'2 : IsPGroup 2 R' := hU2.to_le (Subgroup.map_subtype_le R)
  have hcardR' : Nat.card R' = Nat.card R := Subgroup.card_map_of_injective U.subtype_injective
  have hbR : ∀ u ∈ R', b * u * b⁻¹ = u := by
    intro u hu
    have h1 : (β : MulAut T) u = u := by
      obtain ⟨r, hr, rfl⟩ := hu
      exact congrArg Subtype.val (hβfix β hβD hβ1 r hr)
    rw [← hb, MulAut.conj_apply] at h1
    exact h1
  have hRC : R' ≤ centralizer ({b} : Set T) := by
    intro u hu
    rw [Subgroup.mem_centralizer_singleton_iff]
    have := hbR u hu
    rw [mul_inv_eq_iff_eq_mul] at this
    exact this.symm
  have hfR : ∀ r ∈ R', f * r * f⁻¹ ∈ R' := by
    rintro _ ⟨r, hr, rfl⟩
    have h1 : (γ : MulAut T) (r : T) = f * (r : T) * f⁻¹ := by
      rw [← hf, MulAut.conj_apply]
    show f * (r : T) * f⁻¹ ∈ R'
    rw [← h1]
    exact ⟨γ • r, hR γ r hr, rfl⟩
  have hmove : ∃ r ∈ R', f * r * f⁻¹ ≠ r := by
    obtain ⟨r, hr, hne⟩ := hγmove γ hγD
    refine ⟨(r : T), ⟨r, hr, rfl⟩, fun h => hne (Subtype.ext ?_)⟩
    have h1 : ((γ • r : U) : T) = f * (r : T) * f⁻¹ := by
      show (γ : MulAut T) (r : T) = _
      rw [← hf, MulAut.conj_apply]
    rw [h1]
    exact h
  have hel : p = 7 → Nat.card R' = 8 → IsElementaryAbelian 2 R' := by
    intro hp7 hR'8
    subst hp7
    have hR8 : Nat.card R = 8 := hcardR'.symm.trans hR'8
    have hdvdGL := hGL d hd
    have h3 := SteinbergBM.three_le_of_seven_dvd_card_GL_two hdvdGL
    have hdle : 2 ^ d ≤ Nat.card R := by
      rw [← hd]
      exact Nat.le_of_dvd Nat.card_pos (card_quotient_dvd_card _)
    have hd3 : d = 3 := by
      have : 2 ^ d ≤ 2 ^ 3 := by rw [hR8] at hdle; simpa using hdle
      exact le_antisymm ((Nat.pow_le_pow_iff_right (by norm_num)).mp this) h3
    have hE : IsElementaryAbelian 2 R :=
      isElementaryAbelian_of_card_frattini_quotient R hVel (by rw [hd, hd3, hR8]; norm_num)
    exact IsElementaryAbelian.map_subtype (H := R) (K := U)
  have := hbound b f hbord hford hbf hfb R' hR'2 hRC hfR hmove hel
  omega

end CFSG.RankThree.PartOne
