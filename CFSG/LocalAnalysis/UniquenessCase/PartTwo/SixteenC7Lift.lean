module

public import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.DefsModule

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

theorem le_centralizer_of_isPGroup_of_card_lt {p : ℕ} (hp : p.Prime) {B V₀ : Subgroup G}
    (hB : IsPGroup p B) (hN : B ≤ normalizer (V₀ : Set G)) (hcard : Nat.card V₀ < p) :
    B ≤ centralizer (V₀ : Set G) := by
  haveI : Fact p.Prime := ⟨hp⟩
  letI : MulAction B ↥V₀ := MulAction.compHom ↥V₀ (Subgroup.inclusion hN)
  have hmod := hB.card_modEq_card_fixedPoints ↥V₀
  have hle : Nat.card (MulAction.fixedPoints B ↥V₀) ≤ Nat.card ↥V₀ :=
    Nat.card_le_card_of_injective (fun x : ↥(MulAction.fixedPoints B ↥V₀) => (x.1 : ↥V₀))
      (fun _ _ h => Subtype.ext h)
  have hlt : Nat.card (MulAction.fixedPoints B ↥V₀) < p := lt_of_le_of_lt hle hcard
  have huniv : MulAction.fixedPoints B ↥V₀ = Set.univ :=
    (Set.eq_univ_iff_ncard _).2 (hmod.eq_of_lt_of_lt hcard hlt).symm
  intro b hb
  rw [Subgroup.mem_centralizer_iff]
  intro v hv
  have hfix : (⟨v, hv⟩ : ↥V₀) ∈ MulAction.fixedPoints B ↥V₀ := by
    rw [huniv]
    exact Set.mem_univ _
  have hbv : (⟨b, hb⟩ : B) • (⟨v, hv⟩ : ↥V₀) = ⟨v, hv⟩ :=
    MulAction.mem_fixedPoints.1 hfix ⟨b, hb⟩
  have hval : b * v * b⁻¹ = v := by
    have h1 : (Subgroup.inclusion hN ⟨b, hb⟩ : ↥(normalizer (V₀ : Set G))) •
        (⟨v, hv⟩ : ↥V₀) = ⟨v, hv⟩ := by
      simpa only [MulAction.compHom_smul_def] using hbv
    have h2 : (Subgroup.normalizerMonoidHom V₀ (Subgroup.inclusion hN ⟨b, hb⟩))
        ⟨v, hv⟩ = ⟨v, hv⟩ := h1
    have h3 := congrArg Subtype.val h2
    rw [Subgroup.normalizerMonoidHom_apply_apply_coe] at h3
    simpa using h3
  calc v * b = b * v * b⁻¹ * b := by rw [hval]
    _ = b * v := by group

theorem le_centralizer_of_mSub_le_two {p : ℕ} (hp : p.Prime) (hp3 : 3 < p) {B V₀ : Subgroup G}
    (hV₀ : IsElemAbelian 2 V₀) (hm : mSub V₀ ≤ 2) (hB : IsPGroup p B)
    (hN : B ≤ normalizer (V₀ : Set G)) : B ≤ centralizer (V₀ : Set G) := by
  refine le_centralizer_of_isPGroup_of_card_lt hp hB hN ?_
  have hp5 : 5 ≤ p := by
    by_contra h
    have h4 : p = 4 := by omega
    rw [h4] at hp
    exact absurd hp (by norm_num)
  have h1 : Nat.card V₀ = 2 ^ mSub V₀ := card_eq_two_pow_mSub hV₀.isPGroup
  have h2 : 2 ^ mSub V₀ ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) hm
  omega

theorem exists_lift_of_mem_fixV_barSub {V₀ V B : Subgroup G} (hV : IsElemAbelian 2 V)
    (hB : B ≤ stabTil V₀ V) (hodd : Odd (Nat.card B)) {q : Vtil V₀ V hV}
    (hq : q ∈ fixV (barSub V₀ V hV B)) :
    ∃ x : IntMod V hV, x.val ∈ centralizer (B : Set G) ∧ mkTil V₀ V hV x = q := by
  letI : Fintype B := Fintype.ofFinite B
  obtain ⟨x₀, hx₀⟩ := mkTil_surjective V₀ V hV q
  let F : B → IntMod V hV := fun b => actStab V₀ V hV ⟨(b : G), hB b.2⟩ x₀
  let x : IntMod V hV := ∏ b : B, F b
  have hfix : ∀ b : B, actTil V₀ V hV ⟨(b : G), hB b.2⟩ q = q := fun b =>
    (mem_fixV.1 hq) _ (actTil_mem_barSub V₀ V hV b.2 (hB b.2))
  have hmul : ∀ (c : B) (b : B),
      actStab V₀ V hV ⟨(c : G), hB c.2⟩ (F b) = F (c * b) := by
    intro c b
    change actStab V₀ V hV ⟨(c : G), hB c.2⟩
        (actStab V₀ V hV ⟨(b : G), hB b.2⟩ x₀) =
      actStab V₀ V hV ⟨((c * b : B) : G), hB (c * b).2⟩ x₀
    have hg : (⟨((c * b : B) : G), hB (c * b).2⟩ : stabTil V₀ V) =
        (⟨(c : G), hB c.2⟩ : stabTil V₀ V) * ⟨(b : G), hB b.2⟩ := Subtype.ext rfl
    rw [hg, map_mul, MulAut.mul_apply]
  have hx_fixed : ∀ c : B, actStab V₀ V hV ⟨(c : G), hB c.2⟩ x = x := by
    intro c
    show actStab V₀ V hV ⟨(c : G), hB c.2⟩ (∏ b : B, F b) = ∏ b : B, F b
    rw [map_prod (actStab V₀ V hV ⟨(c : G), hB c.2⟩) F Finset.univ]
    exact Fintype.prod_equiv (Equiv.mulLeft c)
      (fun b : B => actStab V₀ V hV ⟨(c : G), hB c.2⟩ (F b)) F (fun b => hmul c b)
  refine ⟨x, ?_, ?_⟩
  · rw [Subgroup.mem_centralizer_iff]
    intro c hc
    have hval := congrArg IntMod.val (hx_fixed ⟨c, hc⟩)
    rw [actStab_apply_val] at hval
    calc c * x.val = c * x.val * c⁻¹ * c := by group
      _ = x.val * c := by rw [hval]
  · have hmkTil : mkTil V₀ V hV x = q ^ Nat.card B := by
      show mkTil V₀ V hV (∏ b : B, F b) = q ^ Nat.card B
      rw [map_prod (mkTil V₀ V hV) F Finset.univ]
      have hterm : ∀ b : B, mkTil V₀ V hV (F b) = q := by
        intro b
        change mkTil V₀ V hV (actStab V₀ V hV ⟨(b : G), hB b.2⟩ x₀) = q
        rw [← actTil_mk, hx₀, hfix b]
      rw [Finset.prod_congr rfl (fun b _ => hterm b), Finset.prod_const, Finset.card_univ,
        Nat.card_eq_fintype_card]
    rw [hmkTil]
    obtain ⟨k, hk⟩ := hodd
    have hq2 : q ^ 2 = 1 := by
      obtain ⟨y, hy⟩ := mkTil_surjective V₀ V hV q
      rw [← hy, ← map_pow, IntMod.sq_eq_one, map_one]
    rw [hk, pow_succ, pow_mul, hq2, one_pow, one_mul]

theorem card_mul_card_fixV_barSub_le {V₀ V B : Subgroup G} (hV : IsElemAbelian 2 V)
    (hV₀V : V₀ ≤ V) (hB : B ≤ stabTil V₀ V) (hodd : Odd (Nat.card B))
    (hV₀B : V₀ ≤ centralizer (B : Set G)) :
    Nat.card V₀ * Nat.card (fixV (barSub V₀ V hV B)) ≤
      Nat.card ↥(V ⊓ centralizer (B : Set G)) := by
  classical
  choose s hs using fun q : ↥(fixV (barSub V₀ V hV B)) =>
    exists_lift_of_mem_fixV_barSub hV hB hodd q.2
  let Φ : ↥V₀ × ↥(fixV (barSub V₀ V hV B)) → ↥(V ⊓ centralizer (B : Set G)) :=
    fun p => ⟨p.1.1 * (s p.2).val, by
      refine ⟨?_, ?_⟩
      · exact V.mul_mem (hV₀V p.1.2) (s p.2).val_mem
      · exact (centralizer (B : Set G)).mul_mem (hV₀B p.1.2) (hs p.2).1⟩
  have hΦ : Function.Injective Φ := by
    rintro ⟨v, q⟩ ⟨v', q'⟩ heq
    have hval : v.1 * (s q).val = v'.1 * (s q').val := congrArg Subtype.val heq
    have hEq : IntMod.mk hV ⟨v.1, hV₀V v.2⟩ * s q =
        IntMod.mk hV ⟨v'.1, hV₀V v'.2⟩ * s q' :=
      IntMod.val_injective hval
    have hmk : q.val = q'.val := by
      have h2 := congrArg (mkTil V₀ V hV) hEq
      simp only [map_mul] at h2
      have hq1 : mkTil V₀ V hV (IntMod.mk hV ⟨v.1, hV₀V v.2⟩) = 1 :=
        (QuotientGroup.eq_one_iff (IntMod.mk hV ⟨v.1, hV₀V v.2⟩)).2
          ((mem_modNull V₀ V hV _).2 v.2)
      have hq2 : mkTil V₀ V hV (IntMod.mk hV ⟨v'.1, hV₀V v'.2⟩) = 1 :=
        (QuotientGroup.eq_one_iff (IntMod.mk hV ⟨v'.1, hV₀V v'.2⟩)).2
          ((mem_modNull V₀ V hV _).2 v'.2)
      rw [hq1, hq2, one_mul, one_mul, (hs q).2, (hs q').2] at h2
      exact h2
    have hq : q = q' := Subtype.ext hmk
    have hv : v = v' := by
      have h3 := hval
      rw [hq] at h3
      exact Subtype.ext (mul_right_cancel h3)
    exact Prod.ext hv hq
  have hcard := Nat.card_le_card_of_injective Φ hΦ
  rw [Nat.card_prod] at hcard
  exact hcard

theorem rk_add_rk_fixV_barSub_le {V₀ V B : Subgroup G} (hV : IsElemAbelian 2 V) (hV₀V : V₀ ≤ V)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hBp : IsPGroup p B) (hB : B ≤ stabTil V₀ V)
    (hV₀B : V₀ ≤ centralizer (B : Set G)) :
    rk ↥V₀ + rk ↥(fixV (barSub V₀ V hV B)) ≤ rk ↥(V ⊓ centralizer (B : Set G)) := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨n, hn⟩ := hBp.exists_card_eq
  have hodd : Odd (Nat.card B) := by
    rw [hn]
    exact (hp.eq_two_or_odd'.resolve_left hp2).pow
  have h := card_mul_card_fixV_barSub_le hV hV₀V hB hodd hV₀B
  have hV₀2 : IsPGroup 2 ↥V₀ := hV.isPGroup.to_le hV₀V
  have hC2 : IsPGroup 2 ↥(V ⊓ centralizer (B : Set G)) := hV.isPGroup.to_le inf_le_left
  have hF2 : IsPGroup 2 ↥(fixV (barSub V₀ V hV B)) :=
    (isPGroup_two_of_sq_eq_one (V := Vtil V₀ V hV) fun q => by
      obtain ⟨x, rfl⟩ := mkTil_surjective V₀ V hV q
      rw [← map_pow, IntMod.sq_eq_one, map_one]).to_subgroup _
  rw [card_eq_two_pow_of_isPGroup hV₀2, card_eq_two_pow_of_isPGroup hF2,
    card_eq_two_pow_of_isPGroup hC2, ← pow_add] at h
  exact (Nat.pow_le_pow_iff_right (by norm_num)).1 h

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
