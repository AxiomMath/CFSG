module

public import Mathlib.GroupTheory.PGroup
import CFSG.LocalAnalysis.ComponentClassification.CoprimeAutomorphisms
import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKFactDihedralTypeFrattini
import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.OutQ8Basic

public section

namespace CFSG.RankThree.PartTwo.Sec15.Sylow155R3

open Subgroup

private theorem res3L125W_sup_eq_top {R : Type*} [Group R] {M N : Subgroup R}
    (hM : M.index = 2) (h : ¬ N ≤ M) : M ⊔ N = ⊤ := by
  obtain ⟨b, hbN, hbM⟩ := SetLike.not_le_iff_exists.mp h
  refine eq_top_iff.mpr fun x _ => ?_
  by_cases hx : x ∈ M
  · exact mem_sup_left hx
  · have h1 : b⁻¹ * x ∈ M := by
      rw [mul_mem_iff_of_index_two hM, inv_mem_iff]
      exact iff_of_false hbM hx
    have h2 : b * (b⁻¹ * x) ∈ M ⊔ N := mul_mem (mem_sup_right hbN) (mem_sup_left h1)
    simpa using h2

private theorem res3L125W_comm_mem {R : Type*} [Group R] {M : Subgroup R} (hM : M.index = 2)
    (x y : R) : (x * y)⁻¹ * (y * x) ∈ M := by
  simp only [mul_mem_iff_of_index_two hM, inv_mem_iff]
  tauto

private theorem res3L125W_center_le {R : Type*} [Group R] {M : Subgroup R}
    (hM : ∀ a ∈ M, ∀ b ∈ M, a * b = b * a) (hidx : M.index = 2)
    (hnc : ¬ ∀ a b : R, a * b = b * a) : center R ≤ M := by
  intro z hz
  by_contra hzM
  apply hnc
  have hsup : M ⊔ zpowers z = ⊤ :=
    res3L125W_sup_eq_top hidx fun h => hzM (h (mem_zpowers z))
  have hMc : ∀ m ∈ M, m ∈ center R := by
    intro m hm
    rw [mem_center_iff]
    intro g
    have hle : M ⊔ zpowers z ≤ centralizer {m} := by
      refine sup_le (fun x hx => ?_) (zpowers_le.mpr ?_)
      · rw [mem_centralizer_iff]
        rintro _ rfl
        exact hM _ hm x hx
      · rw [mem_centralizer_iff]
        intro h hh
        rw [Set.mem_singleton_iff.mp hh]
        exact mem_center_iff.mp hz m
    have hg : g ∈ centralizer {m} := hle (hsup ▸ mem_top g)
    exact (mem_centralizer_iff.mp hg m rfl).symm
  intro a b
  have hle : M ⊔ zpowers z ≤ center R := sup_le hMc (zpowers_le.mpr hz)
  exact mem_center_iff.mp (hle (hsup ▸ mem_top b)) a

private theorem res3L125W_abelian {H : Type} [Group H] [Finite H] (hH : IsPGroup 2 H)
    (hc : ∀ a b : H, a * b = b * a)
    (hE : ∀ E : Subgroup H, (∀ a ∈ E, a ^ 2 = 1) → Nat.card E ≤ 4)
    {τ : MulAut H} {m : ℕ} (hm : Nat.Coprime m 6) (hτ : τ ^ m = 1) : τ = 1 := by
  let E : Subgroup H :=
    { carrier := {x | x ^ 2 = 1}
      mul_mem' := fun {x y} hx hy => by
        have hx2 : x ^ 2 = 1 := hx
        have hy2 : y ^ 2 = 1 := hy
        show (x * y) ^ 2 = 1
        rw [(show Commute x y from hc x y).mul_pow, hx2, hy2, one_mul]
      one_mem' := one_pow 2
      inv_mem' := fun {x} hx => by
        have hx2 : x ^ 2 = 1 := hx
        show x⁻¹ ^ 2 = 1
        rw [inv_pow, hx2, inv_one] }
  have hE4 : Nat.card E ≤ 4 := hE E fun a ha => ha
  have hle : Nat.card (H ⧸ frattini H) ≤ 4 := by
    have h := CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KDType.card_frattini_quotient_le hH ⊤
      (fun a _ b _ => hc a b) (E : Set H) fun x _ hx => hx
    rw [Subgroup.index_top, one_mul] at h
    exact h.trans hE4
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp (hH.to_quotient (frattini H))
  have hn2 : n ≤ 2 := by
    by_contra hcon
    have h8 : 2 ^ 3 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [hn] at hle
    omega
  obtain ⟨-, hcomm, hpow, -, -⟩ := CFSG.GroupTheory.frattini_elementary_quotient hH
  have h6 : Nat.card (MulAut (H ⧸ frattini H)) ∣ 6 :=
    CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KDType.card_mulAut_dvd_six
      (fun a b => hcomm.is_comm.comm a b) hpow hn hn2
  set τ' := CFSG.OrderReductions.FrattiniAutomorphisms.quotientAutomorphism (frattini H) τ
    with hτ'
  have h1 : orderOf τ' ∣ 6 := (_root_.orderOf_dvd_natCard _).trans h6
  have h2 : orderOf τ' ∣ m := by
    apply orderOf_dvd_of_pow_eq_one
    rw [hτ', ← map_pow, hτ, map_one]
  have h3 : τ' = 1 := orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hm h2 h1)
  have hfr : ∀ g : H, g⁻¹ * τ g ∈ frattini H := by
    intro g
    have h := CFSG.OrderReductions.FrattiniAutomorphisms.quotientAutomorphism_apply
      (frattini H) τ g
    rw [← hτ', h3] at h
    exact QuotientGroup.eq.mp h
  exact CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.OutQ8.aut_eq_one_of_frattini hH τ m hτ
    (hm.coprime_dvd_right (by norm_num : 2 ∣ 6)) hfr

private theorem res3L125W_map_le {R : Type} [Group R] [Finite R] (hR : IsPGroup 2 R)
    {A : Subgroup R} (hA : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) (hidx : A.index = 2)
    (hnc : ¬ ∀ a b : R, a * b = b * a) {β : MulAut R} (hβ : Nat.Coprime (orderOf β) 6) :
    A.map β.toMonoidHom ≤ A := by
  by_contra hBA
  set B : Subgroup R := A.map β.toMonoidHom with hB
  have hBidx : B.index = 2 := by
    rw [hB]
    exact (index_map_equiv (H := A) β).trans hidx
  have hBab : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [← map_mul, ← map_mul, hA x hx y hy]
  have hsup : A ⊔ B = ⊤ := res3L125W_sup_eq_top hidx hBA
  have hZ : center R = A ⊓ B := by
    refine le_antisymm (le_inf (res3L125W_center_le hA hidx hnc)
      (res3L125W_center_le hBab hBidx hnc)) fun z hz => ?_
    rw [mem_center_iff]
    intro g
    have hle : A ⊔ B ≤ centralizer {z} := by
      refine sup_le (fun x hx => ?_) (fun x hx => ?_)
      · rw [mem_centralizer_iff]
        rintro _ rfl
        exact hA _ hz.1 x hx
      · rw [mem_centralizer_iff]
        rintro _ rfl
        exact hBab _ hz.2 x hx
    have hg : g ∈ centralizer {z} := hle (hsup ▸ mem_top g)
    exact (mem_centralizer_iff.mp hg z rfl).symm
  have hZidx : (center R).index ≤ 4 := by
    rw [hZ]
    calc (A ⊓ B).index ≤ A.index * B.index := index_inf_le
      _ = 4 := by rw [hidx, hBidx]
  have hWcomm : ∀ v w : R ⧸ center R, v * w = w * v := by
    intro v w
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective v
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective w
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq, hZ]
    exact ⟨res3L125W_comm_mem hidx x y, res3L125W_comm_mem hBidx x y⟩
  have hWpow : ∀ w : R ⧸ center R, w ^ 2 = 1 := by
    intro w
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective w
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, hZ]
    exact ⟨sq_mem_of_index_two hidx x, sq_mem_of_index_two hBidx x⟩
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp (hR.to_quotient (center R))
  have hn2 : n ≤ 2 := by
    by_contra hcon
    have h8 : 2 ^ 3 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h4 : Nat.card (R ⧸ center R) ≤ 4 := hZidx
    omega
  have h6 : Nat.card (MulAut (R ⧸ center R)) ∣ 6 :=
    CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KDType.card_mulAut_dvd_six hWcomm hWpow hn hn2
  set β' := CFSG.OrderReductions.FrattiniAutomorphisms.quotientAutomorphism (center R) β
    with hβ'
  have h1 : orderOf β' ∣ 6 := (_root_.orderOf_dvd_natCard _).trans h6
  have h2 : orderOf β' ∣ orderOf β := orderOf_map_dvd _ _
  have h3 : β' = 1 := orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hβ h2 h1)
  have hdisp : ∀ x : R, x⁻¹ * β x ∈ center R := by
    intro x
    have h := CFSG.OrderReductions.FrattiniAutomorphisms.quotientAutomorphism_apply
      (center R) β x
    rw [← hβ', h3] at h
    exact QuotientGroup.eq.mp h
  apply hBA
  rintro _ ⟨a, ha, rfl⟩
  have h5 : a * (a⁻¹ * β a) ∈ A := mul_mem ha (res3L125W_center_le hA hidx hnc (hdisp a))
  simpa using h5

private theorem res3L125W_main {R : Type} [Group R] [Finite R] (hR : IsPGroup 2 R)
    {A : Subgroup R} (hA : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) (hidx : A.index ≤ 2)
    (hE : ∀ E : Subgroup R, (∀ a ∈ E, ∀ b ∈ E, a * b = b * a) → (∀ a ∈ E, a ^ 2 = 1) →
      Nat.card E ≤ 4)
    {β : MulAut R} (hβ : Nat.Coprime (orderOf β) 6) : β = 1 := by
  by_cases hab : ∀ a b : R, a * b = b * a
  · exact res3L125W_abelian hR hab (fun E hE2 => hE E (fun a _ b _ => hab a b) hE2) hβ
      (pow_orderOf_eq_one β)
  have hidx2 : A.index = 2 := by
    have h0 : A.index ≠ 0 := Subgroup.index_ne_zero_of_finite
    have h1 : A.index ≠ 1 := fun h1 => by
      rw [index_eq_one] at h1
      exact hab fun a b => hA a (h1 ▸ mem_top a) b (h1 ▸ mem_top b)
    omega
  have hle := res3L125W_map_le hR hA hidx2 hab hβ
  have hmap : A.map β.toMonoidHom = A :=
    eq_of_le_of_card_ge hle (card_map_of_injective β.injective).ge
  let βA : MulAut A := (β.subgroupMap A).trans (MulEquiv.subgroupCongr hmap)
  have hpowA : ∀ (n : ℕ) (a : A), ((βA ^ n) a : R) = (β ^ n) a := by
    intro n
    induction n with
    | zero => intro a; rfl
    | succ n ih =>
      intro a
      rw [pow_succ', MulAut.mul_apply, pow_succ', MulAut.mul_apply, ← ih a]
      rfl
  have hpow1 : βA ^ orderOf β = 1 := by
    ext a
    rw [hpowA, pow_orderOf_eq_one]
    rfl
  have hAp : IsPGroup 2 A := hR.to_subgroup A
  have hEA : ∀ E : Subgroup A, (∀ a ∈ E, a ^ 2 = 1) → Nat.card E ≤ 4 := by
    intro E hE2
    have h := hE (E.map A.subtype) ?_ ?_
    · rwa [card_map_of_injective A.subtype_injective] at h
    · rintro _ ⟨a, -, rfl⟩ _ ⟨b, -, rfl⟩
      exact hA a a.2 b b.2
    · rintro _ ⟨a, ha, rfl⟩
      rw [← map_pow, hE2 a ha, map_one]
  have hβA1 : βA = 1 :=
    res3L125W_abelian hAp (fun a b => Subtype.ext (hA a a.2 b b.2)) hEA hβ hpow1
  have hfix : ∀ a ∈ A, β a = a := by
    intro a ha
    exact congrArg (fun f : MulAut A => (f ⟨a, ha⟩ : R)) hβA1
  have hdisp : ∀ x : R, x⁻¹ * β x ∈ A := by
    intro x
    rw [mul_mem_iff_of_index_two hidx2, inv_mem_iff]
    constructor
    · intro hx
      exact hle ⟨x, hx, rfl⟩
    · intro hbx
      have h : β x ∈ A.map β.toMonoidHom := by
        rw [hmap]
        exact hbx
      obtain ⟨a, ha, hax⟩ := h
      exact (β.injective hax) ▸ ha
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hAp
  have hcop : Nat.Coprime (orderOf β) (Nat.card A) := by
    rw [hk]
    exact Nat.Coprime.pow_right k (hβ.coprime_dvd_right (by norm_num : 2 ∣ 6))
  exact CFSG.ComponentClassification.CoprimeAutomorphisms.eq_one_of_fixed_displacement A β
    (orderOf β) (pow_orderOf_eq_one β) hcop hfix hdisp

theorem res3L125_eq_one_of_coprime_six {R : Type*} [Group R] [Finite R] (hR : IsPGroup 2 R)
    {A : Subgroup R} (hA : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) (hidx : A.index ≤ 2)
    (hE : ∀ E : Subgroup R, (∀ a ∈ E, ∀ b ∈ E, a * b = b * a) → (∀ a ∈ E, a ^ 2 = 1) →
      Nat.card E ≤ 4)
    {β : MulAut R} (hβ : Nat.Coprime (orderOf β) 6) : β = 1 := by
  haveI : Small.{0} R := small_map (Finite.equivFin R)
  let e : Shrink.{0} R ≃* R := Shrink.mulEquiv
  haveI : Finite (Shrink.{0} R) := Finite.of_equiv R e.symm.toEquiv
  have hR' : IsPGroup 2 (Shrink.{0} R) := hR.of_injective e.toMonoidHom e.injective
  have hA' : ∀ a ∈ A.comap e.toMonoidHom, ∀ b ∈ A.comap e.toMonoidHom, a * b = b * a := by
    intro a ha b hb
    apply e.injective
    rw [map_mul, map_mul]
    exact hA _ ha _ hb
  have hidx' : (A.comap e.toMonoidHom).index ≤ 2 := by
    rw [index_comap_of_surjective A (f := e.toMonoidHom) e.surjective]
    exact hidx
  have hE' : ∀ E : Subgroup (Shrink.{0} R), (∀ a ∈ E, ∀ b ∈ E, a * b = b * a) →
      (∀ a ∈ E, a ^ 2 = 1) → Nat.card E ≤ 4 := by
    intro E hc hp
    have h := hE (E.map e.toMonoidHom) ?_ ?_
    · rwa [card_map_of_injective e.injective] at h
    · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
      rw [← map_mul, ← map_mul, hc a ha b hb]
    · rintro _ ⟨a, ha, rfl⟩
      rw [← map_pow, hp a ha, map_one]
  have hβ' : Nat.Coprime (orderOf (MulAut.congr e.symm β)) 6 := by
    rwa [MulEquiv.orderOf_eq]
  exact ((MulAut.congr e.symm).map_eq_one_iff).mp (res3L125W_main hR' hA' hidx' hE' hβ')

end CFSG.RankThree.PartTwo.Sec15.Sylow155R3
