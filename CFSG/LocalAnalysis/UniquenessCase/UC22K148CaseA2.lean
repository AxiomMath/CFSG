module

public import CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.CommLemmas
import CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.RGroupExclusionGL
import CFSG.HardMathSupport.U4FF.SmallGL
import CFSG.CGT.PushingUpLit.BHS.ThreeConj

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.K148

open CFSG.RankThree.FFModules CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF

variable {G : Type} [Group G] {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
variable {ρ : Representation (ZMod 2) G V}

theorem apply_eq_self_of_odd_of_fixes_sub {s : G} (hs : Odd (orderOf s)) {v : V}
    (h : ρ s (ρ s v - v) = ρ s v - v) : ρ s v = v := by
  set x := ρ s v - v with hx
  have hpow : ∀ k : ℕ, ρ (s ^ k) v = v + k • x := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ', map_mul, Module.End.mul_apply, ih, map_add, map_nsmul, h, succ_nsmul, hx]
      abel
  have h1 := hpow (orderOf s)
  rw [pow_orderOf_eq_one, map_one, Module.End.one_apply, left_eq_add] at h1
  obtain ⟨j, hj⟩ := hs
  rw [hj, add_nsmul, one_nsmul, two_mul, add_nsmul, ← nsmul_add, two_nsmul_eq_zero', nsmul_zero,
    zero_add] at h1
  rw [← sub_eq_zero]
  exact h1

theorem eq_one_of_fixes_commOn (hρ : Function.Injective ρ) {X : Subgroup G} {x : G} (hx : x ∈ X)
    (hodd : Odd (orderOf x)) (hfix : ∀ w ∈ commOn ρ X ⊤, ρ x w = w) : x = 1 := by
  apply hρ
  rw [map_one]
  refine LinearMap.ext fun v => ?_
  rw [Module.End.one_apply]
  exact apply_eq_self_of_odd_of_fixes_sub hodd (hfix _ (sub_mem_commOn hx Submodule.mem_top))

theorem commOn_sup_top_le (X Y : Subgroup G) :
    commOn ρ (X ⊔ Y) ⊤ ≤ commOn ρ X ⊤ ⊔ commOn ρ Y ⊤ := by
  have key : ∀ g ∈ X ⊔ Y, ∀ v, ρ g v - v ∈ commOn ρ X ⊤ ⊔ commOn ρ Y ⊤ := by
    intro g hg
    rw [Subgroup.sup_eq_closure] at hg
    induction hg using Subgroup.closure_induction with
    | mem x hx =>
      intro v
      rcases hx with hx | hx
      · exact Submodule.mem_sup_left (sub_mem_commOn hx Submodule.mem_top)
      · exact Submodule.mem_sup_right (sub_mem_commOn hx Submodule.mem_top)
    | one => intro v; simp
    | mul x y _ _ hx hy =>
      intro v
      have e : ρ (x * y) v - v = (ρ x (ρ y v) - ρ y v) + (ρ y v - v) := by
        rw [map_mul, Module.End.mul_apply]
        abel
      rw [e]
      exact add_mem (hx _) (hy _)
    | inv x _ hx =>
      intro v
      have e : ρ x⁻¹ v - v = -(ρ x (ρ x⁻¹ v) - ρ x⁻¹ v) := by
        rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
        abel
      rw [e]
      exact neg_mem (hx _)
  refine Submodule.span_le.2 ?_
  rintro _ ⟨g, hg, v, -, rfl⟩
  exact key g hg v

theorem card_dvd_card_linearEquiv_commOn [Finite V] (hρ : Function.Injective ρ) {T : Subgroup G}
    (hodd : ∀ t ∈ T, Odd (orderOf t)) :
    Nat.card ↥T ∣ Nat.card (↥(commOn ρ T ⊤) ≃ₗ[ZMod 2] ↥(commOn ρ T ⊤)) := by
  have hinv : CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant ρ T (commOn ρ T ⊤) :=
    (invariant_commOn_top (A := T) Subgroup.le_normalizer).1
  have hcen : cenOn ρ T (commOn ρ T ⊤) = ⊥ :=
    (Subgroup.eq_bot_iff_forall _).2 fun t ht => eq_one_of_fixes_commOn hρ ht.1 (hodd t ht.1) ht.2
  have h := card_imgGL_mul_card_cenOn (hU := hinv) (le_refl T)
  rw [hcen, Subgroup.card_bot, mul_one] at h
  rw [← h]
  exact Subgroup.card_subgroup_dvd_card _

theorem commute_of_rank_two [Finite G] [Finite V] (hρ : Function.Injective ρ)
    {S Q₁ Q₂ : Subgroup G} (hS : IsPGroup 3 ↥S) (h₁ : Q₁ ≤ S) (h₂ : Q₂ ≤ S)
    (hc₁ : Nat.card ↥Q₁ = 3) (hc₂ : Nat.card ↥Q₂ = 3)
    (hr₁ : Module.finrank (ZMod 2) ↥(commOn ρ Q₁ ⊤) = 2)
    (hr₂ : Module.finrank (ZMod 2) ↥(commOn ρ Q₂ ⊤) = 2) (hne : Q₁ ≠ Q₂) :
    (∀ x ∈ Q₁, ∀ y ∈ Q₂, x * y = y * x) ∧ commOn ρ Q₁ ⊤ ⊓ commOn ρ Q₂ ⊤ = ⊥ ∧
      commOn ρ Q₁ ⊤ ≤ fixSub ρ Q₂ := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hTp : IsPGroup 3 ↥(Q₁ ⊔ Q₂) := hS.to_le (sup_le h₁ h₂)
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 hTp
  have hodd : ∀ t ∈ Q₁ ⊔ Q₂, Odd (orderOf t) := fun t ht =>
    Odd.of_dvd_nat (hn ▸ Odd.pow (by decide)) (Subgroup.orderOf_dvd_natCard _ ht)
  have hdvd := card_dvd_card_linearEquiv_commOn hρ hodd
  have hle : commOn ρ (Q₁ ⊔ Q₂) ⊤ ≤ commOn ρ Q₁ ⊤ ⊔ commOn ρ Q₂ ⊤ := commOn_sup_top_le Q₁ Q₂
  have hsup : Module.finrank (ZMod 2) ↥(commOn ρ Q₁ ⊤ ⊔ commOn ρ Q₂ ⊤) ≤ 4 := by
    have := Submodule.finrank_add_le_finrank_add_finrank (commOn ρ Q₁ ⊤) (commOn ρ Q₂ ⊤)
    omega
  have hr : Module.finrank (ZMod 2) ↥(commOn ρ (Q₁ ⊔ Q₂) ⊤) ≤ 4 :=
    (Submodule.finrank_mono hle).trans hsup
  rw [CFSG.HardMathSupport.U4FF.card_linearEquiv_eq_prod rfl, hn] at hdvd
  obtain ⟨h9, h3⟩ := CFSG.CGT.PushingUpLit.BHS.three_pow_dvd_of_dvd_card_gl hr hdvd
  have hsmall : ¬ 3 ^ n ∣ 3 := by
    intro h
    rw [← hn] at h
    have hle3 := Nat.le_of_dvd (by norm_num) h
    have e₁ := Subgroup.eq_of_le_of_card_ge (le_sup_left : Q₁ ≤ Q₁ ⊔ Q₂) (by rw [hc₁]; exact hle3)
    have e₂ := Subgroup.eq_of_le_of_card_ge (le_sup_right : Q₂ ≤ Q₁ ⊔ Q₂) (by rw [hc₂]; exact hle3)
    exact hne (e₁.trans e₂.symm)
  have hr4 : Module.finrank (ZMod 2) ↥(commOn ρ (Q₁ ⊔ Q₂) ⊤) = 4 := by
    by_contra h4
    exact hsmall (h3 (by omega))
  have hinf : commOn ρ Q₁ ⊤ ⊓ commOn ρ Q₂ ⊤ = ⊥ := by
    have h4 := Submodule.finrank_mono hle
    have := Submodule.finrank_sup_add_finrank_inf_eq (commOn ρ Q₁ ⊤) (commOn ρ Q₂ ⊤)
    exact Submodule.finrank_eq_zero.1 (by omega)
  have hn2 : n = 2 := by
    have h2 : n ≤ 2 :=
      (Nat.pow_dvd_pow_iff_le_right (by norm_num : 1 < 3)).1 (show 3 ^ n ∣ 3 ^ 2 from h9)
    have h0 : n ≠ 0 := by rintro rfl; exact hsmall (by norm_num)
    have h1 : n ≠ 1 := by rintro rfl; exact hsmall (by norm_num)
    omega
  have hcomm := IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 3) (hn.trans (by rw [hn2]))
  have hxy : ∀ x ∈ Q₁, ∀ y ∈ Q₂, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hcomm.is_comm.comm (⟨x, Subgroup.mem_sup_left hx⟩ : ↥(Q₁ ⊔ Q₂))
      ⟨y, Subgroup.mem_sup_right hy⟩)
  refine ⟨hxy, hinf, Submodule.span_le.2 ?_⟩
  rintro _ ⟨x, hx, v, -, rfl⟩
  rw [SetLike.mem_coe, mem_fixSub]
  intro y hy
  have h1 : ρ y (ρ x v - v) - (ρ x v - v) ∈ commOn ρ Q₁ ⊤ := by
    have e : ρ y (ρ x v - v) - (ρ x v - v) = (ρ x (ρ y v) - ρ y v) - (ρ x v - v) := by
      rw [map_sub, ← Module.End.mul_apply (ρ y), ← map_mul, ← hxy x hx y hy, map_mul,
        Module.End.mul_apply]
    rw [e]
    exact sub_mem (sub_mem_commOn hx Submodule.mem_top) (sub_mem_commOn hx Submodule.mem_top)
  have h2 : ρ y (ρ x v - v) - (ρ x v - v) ∈ commOn ρ Q₂ ⊤ := sub_mem_commOn hy Submodule.mem_top
  have h3 : ρ y (ρ x v - v) - (ρ x v - v) ∈ commOn ρ Q₁ ⊤ ⊓ commOn ρ Q₂ ⊤ := ⟨h1, h2⟩
  rw [hinf, Submodule.mem_bot, sub_eq_zero] at h3
  exact h3

theorem finrank_commOn_conj (Q : Subgroup G) (d : G) :
    Module.finrank (ZMod 2) ↥(commOn ρ (Q.map (MulAut.conj d).toMonoidHom) ⊤) =
      Module.finrank (ZMod 2) ↥(commOn ρ Q ⊤) := by
  have hinj : Function.Injective (ρ d) := fun v w h => by
    have := congrArg (ρ d⁻¹) h
    rwa [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply,
      ← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply] at this
  have e : commOn ρ (Q.map (MulAut.conj d).toMonoidHom) ⊤ = (commOn ρ Q ⊤).map (ρ d) := by
    simp only [commOn]
    rw [Submodule.map_span]
    congr 1
    ext w
    constructor
    · rintro ⟨_, ⟨q, hq, rfl⟩, u, -, rfl⟩
      refine ⟨ρ q (ρ d⁻¹ u) - ρ d⁻¹ u, ⟨q, hq, ρ d⁻¹ u, Submodule.mem_top, rfl⟩, ?_⟩
      change ρ d (ρ q (ρ d⁻¹ u) - ρ d⁻¹ u) = ρ (d * q * d⁻¹) u - u
      rw [map_sub, map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply,
        ← Module.End.mul_apply (ρ d) (ρ d⁻¹), ← map_mul, mul_inv_cancel, map_one,
        Module.End.one_apply]
    · rintro ⟨_, ⟨q, hq, u, -, rfl⟩, rfl⟩
      refine ⟨_, ⟨q, hq, rfl⟩, ρ d u, Submodule.mem_top, ?_⟩
      change ρ d (ρ q u - u) = ρ (d * q * d⁻¹) (ρ d u) - ρ d u
      rw [map_sub, map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply,
        ← Module.End.mul_apply (ρ d⁻¹) (ρ d), ← map_mul, inv_mul_cancel, map_one,
        Module.End.one_apply]
  rw [e]
  exact (Submodule.equivMapOfInjective (ρ d) hinj (commOn ρ Q ⊤)).finrank_eq.symm

theorem eq_conj_of_rank_two [Finite G] [Finite V] (hρ : Function.Injective ρ)
    {S Q D X : Subgroup G} (hS : IsPGroup 3 ↥S) (hQS : Q ≤ S)
    (hDS : D ≤ Subgroup.normalizer (S : Set G))
    (hQ3 : Nat.card ↥Q = 3) (hQV : Module.finrank (ZMod 2) ↥(commOn ρ Q ⊤) = 2)
    (hXY : X ≤ ⨆ d ∈ D, Q.map (MulAut.conj d).toMonoidHom) (hX3 : Nat.card ↥X = 3)
    (hXV : Module.finrank (ZMod 2) ↥(commOn ρ X ⊤) = 2) :
    ∃ d ∈ D, X = Q.map (MulAut.conj d).toMonoidHom := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hconjS : ∀ d ∈ D, Q.map (MulAut.conj d).toMonoidHom ≤ S := fun d hd => by
    rw [Subgroup.map_le_iff_le_comap]
    intro q hq
    exact (Subgroup.mem_normalizer_iff.1 (hDS hd) q).1 (hQS hq)
  have hconj3 : ∀ d : G, Nat.card ↥(Q.map (MulAut.conj d).toMonoidHom) = 3 := fun d => by
    rw [Subgroup.card_map_of_injective (MulAut.conj d).injective]
    exact hQ3
  have hXS : X ≤ S := hXY.trans (iSup₂_le hconjS)
  by_contra hne
  push Not at hne
  have hfix : ∀ d ∈ D, Q.map (MulAut.conj d).toMonoidHom ≤ cenOn ρ ⊤ (commOn ρ X ⊤) := by
    intro d hd y hy
    have hpair := (commute_of_rank_two hρ hS hXS (hconjS d hd) hX3 (hconj3 d) hXV
      ((finrank_commOn_conj Q d).trans hQV) (hne d hd)).2.2
    exact ⟨Subgroup.mem_top y, fun w hw => hpair hw y hy⟩
  have hXc : X ≤ cenOn ρ ⊤ (commOn ρ X ⊤) := hXY.trans (iSup₂_le hfix)
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 hS
  have hbot : X = ⊥ := (Subgroup.eq_bot_iff_forall X).2 fun x hx =>
    eq_one_of_fixes_commOn hρ hx
      (Odd.of_dvd_nat (hn ▸ Odd.pow (by decide)) (Subgroup.orderOf_dvd_natCard S (hXS hx)))
      (hXc hx).2
  rw [hbot, Subgroup.card_bot] at hX3
  omega

end CFSG.LocalAnalysis.UniquenessCase.UC22.K148
