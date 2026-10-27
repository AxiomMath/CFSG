module

public import CFSG.Quasithin.Background.HA7Alpha
public import CFSG.Quasithin.Background.HA7RowData

public section

namespace CFSG.Quasithin

namespace H

namespace A7

open CFSG.Open CFSG.Assembly.LowTwoRank Matrix Equiv PairG
open scoped Matrix

variable (α : ↥(alternatingGroup (Fin 8)) ≃* GL (Fin 4) (ZMod 2))

theorem card_fix_natAut_le_of_odd
    {γ : Γ α} (h1 : γ ≠ 1) (hodd : Odd (orderOf γ)) :
    Nat.card {v : StdMod (Fin 4) (ZMod 2) // natAut (Γ α) γ v = v} ≤ 4 := by
  classical
  set M := ((γ : GL (Fin 4) (ZMod 2)) : Matrix (Fin 4) (Fin 4) (ZMod 2)) with hM
  let F₀ : Submodule (ZMod 2) (Fin 4 → ZMod 2) :=
    { carrier := {v | M *ᵥ v = v}
      add_mem' := fun {v w} hv hw => by
        change M *ᵥ (v + w) = v + w
        rw [Matrix.mulVec_add, hv, hw]
      zero_mem' := Matrix.mulVec_zero M
      smul_mem' := fun c v hv => by
        change M *ᵥ (c • v) = c • v
        rw [Matrix.mulVec_smul, hv] }
  let F : AddSubgroup (Fin 4 → ZMod 2) := F₀.toAddSubgroup
  have hcard : Nat.card {v : StdMod (Fin 4) (ZMod 2) // natAut (Γ α) γ v = v} = Nat.card F :=
    Nat.card_congr
      { toFun := fun v => ⟨Multiplicative.toAdd v.1, congrArg Multiplicative.toAdd v.2⟩
        invFun := fun v => ⟨Multiplicative.ofAdd v.1, congrArg Multiplicative.ofAdd v.2⟩
        left_inv := fun v => rfl
        right_inv := fun v => rfl }
  have hdvd : Nat.card F ∣ 2 ^ 4 := by
    have := AddSubgroup.card_addSubgroup_dvd_card F
    rwa [card_fin_four_fun] at this
  obtain ⟨k, hk, hFk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
  rw [hcard, hFk]
  by_contra hcon
  push Not at hcon
  have h3 : 3 ≤ k := by
    by_contra h
    push Not at h
    have : 2 ^ k ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have h8 : 8 ≤ (Finset.univ.filter fun v : Fin 4 → ZMod 2 => M *ᵥ v = v).card := by
    have e : (Finset.univ.filter fun v : Fin 4 → ZMod 2 => M *ᵥ v = v).card = Nat.card F := by
      rw [← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
      rfl
    rw [e, hFk]
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) h3
  have hsq : γ * γ = 1 := by
    rcases sq_eq_of_card_fix M h8 with h | h
    · exact Subtype.ext (Units.ext h)
    · have h' : (γ : GL (Fin 4) (ZMod 2)) * γ = (γ : GL (Fin 4) (ZMod 2)) * 1 := by
        rw [mul_one]
        exact Units.ext h
      exact absurd (Subtype.ext (mul_left_cancel h')) h1
  have hdvd : orderOf γ ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [sq]; exact hsq)
  rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
  · exact h1 (orderOf_eq_one_iff.mp h)
  · rw [h] at hodd
    exact absurd hodd (by decide)

theorem map_V₁_eq_or'
    {x : MulAut (PairMod (Fin 4) (ZMod 2))} (hx : x ∈ pairNormA7 α) :
    (V₁ (Fin 4) (ZMod 2)).map x.toMonoidHom = V₁ (Fin 4) (ZMod 2) ∨
      (V₁ (Fin 4) (ZMod 2)).map x.toMonoidHom = V₂ (Fin 4) (ZMod 2) :=
  map_V₁_eq_or (isNatIrr α) (θ_surjective α) (not_isoMod α) hx

theorem mul_self_mem_pairA7
    {x : MulAut (PairMod (Fin 4) (ZMod 2))} (hx : x ∈ pairNormA7 α) :
    x * x ∈ pairA7 α := by
  have hcomp : ∀ y z : MulAut (PairMod (Fin 4) (ZMod 2)),
      (y * z).toMonoidHom = y.toMonoidHom.comp z.toMonoidHom := fun _ _ => rfl
  apply mem_pairA7_of_map α (Subgroup.mul_mem _ hx hx)
  rw [hcomp, ← Subgroup.map_map]
  rcases map_V₁_eq_or' α hx with h | h
  · rw [h, h]
  · have hid : x.toMonoidHom.comp x⁻¹.toMonoidHom = MonoidHom.id _ :=
      MonoidHom.ext fun v => x.apply_symm_apply v
    have hback : ((V₁ (Fin 4) (ZMod 2)).map x⁻¹.toMonoidHom).map x.toMonoidHom =
        V₁ (Fin 4) (ZMod 2) := by
      rw [Subgroup.map_map, hid, Subgroup.map_id]
    rcases map_V₁_eq_or' α (Subgroup.inv_mem _ hx) with h' | h'
    · exfalso
      apply V₁_ne_V₂ (ι := Fin 4) (K := ZMod 2)
      calc V₁ (Fin 4) (ZMod 2)
          = ((V₁ (Fin 4) (ZMod 2)).map x⁻¹.toMonoidHom).map x.toMonoidHom := hback.symm
        _ = (V₁ (Fin 4) (ZMod 2)).map x.toMonoidHom := by rw [h']
        _ = V₂ (Fin 4) (ZMod 2) := h
    · rw [h, ← h', hback]

theorem mem_pairA7_of_odd
    {x : MulAut (PairMod (Fin 4) (ZMod 2))} (hx : x ∈ pairNormA7 α)
    (hodd : Odd (orderOf x)) : x ∈ pairA7 α := by
  obtain ⟨k, hk⟩ := hodd
  have hx' : x = (x * x) ^ (k + 1) := by
    rw [← sq, ← pow_mul, show 2 * (k + 1) = orderOf x + 1 by omega, pow_succ,
      pow_orderOf_eq_one, one_mul]
  rw [hx']
  exact Subgroup.pow_mem _ (mul_self_mem_pairA7 α hx) _

theorem card_V₁ : Nat.card (V₁ (Fin 4) (ZMod 2)) = 16 := by
  rw [← card_stdMod_four]
  exact Nat.card_congr
    { toFun := fun w => (w : PairMod (Fin 4) (ZMod 2)).1
      invFun := fun x => ⟨(x, 1), mem_V₁.mpr rfl⟩
      left_inv := fun w => Subtype.ext (Prod.ext rfl (mem_V₁.mp w.2).symm)
      right_inv := fun x => rfl }

theorem card_le_two_mul_inf
    {A : Subgroup (MulAut (PairMod (Fin 4) (ZMod 2)))}
    (hAN : A ≤ pairNormA7 α) (hsq : ∀ x ∈ A, x * x = 1) :
    Nat.card A ≤ 2 * Nat.card ↥(A ⊓ pairA7 α) := by
  have : Finite (MulAut (PairMod (Fin 4) (ZMod 2))) := MulEquiv.finite_left
  have hmem : ∀ x ∈ A, x ∈ pairA7 α ↔
      (V₁ (Fin 4) (ZMod 2)).map x.toMonoidHom = V₁ (Fin 4) (ZMod 2) := by
    intro x hx
    constructor
    · rintro ⟨γ, rfl⟩
      exact map_V₁_pairAut _ _
    · exact mem_pairA7_of_map α (hAN hx)
  refine Sp4.card_le_two_mul_of_mul_mem inf_le_left fun x hx z hz hx' hz' =>
    ⟨A.mul_mem hx hz, ?_⟩
  have hx1 : x ∉ pairA7 α := fun h => hx' ⟨hx, h⟩
  have hz1 : z ∉ pairA7 α := fun h => hz' ⟨hz, h⟩
  have hxV := (map_V₁_eq_or' α (hAN hx)).resolve_left fun h => hx1 ((hmem x hx).mpr h)
  have hzV := (map_V₁_eq_or' α (hAN hz)).resolve_left fun h => hz1 ((hmem z hz).mpr h)
  have hxV2 : (V₂ (Fin 4) (ZMod 2)).map x.toMonoidHom = V₁ (Fin 4) (ZMod 2) := by
    rw [← hxV, Subgroup.map_map]
    have : x.toMonoidHom.comp x.toMonoidHom = MonoidHom.id _ := by
      refine MonoidHom.ext fun v => ?_
      change (x * x) v = v
      rw [hsq x hx]
      rfl
    rw [this, Subgroup.map_id]
  refine (hmem _ (A.mul_mem hx hz)).mpr ?_
  have : (x * z).toMonoidHom = x.toMonoidHom.comp z.toMonoidHom := rfl
  rw [this, ← Subgroup.map_map, hzV, hxV2]

theorem card_le_eight
    {A : Subgroup (MulAut (PairMod (Fin 4) (ZMod 2)))}
    (hAN : A ≤ pairNormA7 α) (hsq : ∀ x ∈ A, x * x = 1) : Nat.card A ≤ 8 := by
  have h1 := card_le_two_mul_inf α hAN hsq
  have h2 := card_le_four_of_le α (inf_le_right : A ⊓ pairA7 α ≤ pairA7 α)
    fun x hx => hsq x hx.1
  omega

theorem pRank_le
    {X : Subgroup (MulAut (PairMod (Fin 4) (ZMod 2)))} (hXN : X ≤ pairNormA7 α) :
    CFSG.Open.pRank 2 X ≤ 3 := by
  have : Finite (MulAut (PairMod (Fin 4) (ZMod 2))) := MulEquiv.finite_left
  obtain ⟨E, hEX, hE, hEc⟩ := exists_isElemAbelian_card_pRank X
  have hE2 : IsElemAbelian2 E := isElemAbelian2_iff.mpr hE
  have h8 := card_le_eight α (hEX.trans hXN) fun x hx => by rw [← sq]; exact hE2.2 x hx
  rw [hEc] at h8
  by_contra h
  push Not at h
  have : 2 ^ 4 ≤ 2 ^ CFSG.Open.pRank 2 X := Nat.pow_le_pow_right (by norm_num) h
  omega

theorem four_le_rkIdx_fix
    {t : MulAut (PairMod (Fin 4) (ZMod 2))} (ht : t ∈ pairNormA7 α)
    (ht2 : orderOf t = 2) : 4 ≤ rkIdx (fixV (Subgroup.zpowers t)) := by
  have htt : t * t = 1 := by
    have h := pow_orderOf_eq_one t
    rw [ht2, sq] at h
    exact h
  have ht1 : t ≠ 1 := fun h => by rw [h, orderOf_one] at ht2; omega
  have hfix : Nat.card ↥(fixV (Subgroup.zpowers t)) ≤ 16 := by
    rcases map_V₁_eq_or' α ht with h | h
    · obtain ⟨γ, rfl⟩ := mem_pairA7_of_map α ht h
      have hγ1 : γ ≠ 1 := fun h => ht1 (by rw [h, map_one])
      have hγ2 : γ * γ = 1 := pairHom_injective α (by rw [map_mul, htt, map_one])
      have hθ2 : θ α γ * θ α γ = 1 := by rw [← map_mul, hγ2, map_one]
      have hθ1 : θ α γ ≠ 1 := fun h => hγ1 ((θ α).injective (by rw [h, map_one]))
      calc Nat.card ↥(fixV (Subgroup.zpowers (pairHom (Γ α) (θ α).toMonoidHom γ)))
          ≤ Nat.card {x : PairMod (Fin 4) (ZMod 2) //
            pairAut (natAut (Γ α) γ) (natAut (Γ α) (θ α γ)) x = x} :=
            Nat.card_le_card_of_injective (fun v => ⟨v, v.2 _ (Subgroup.mem_zpowers _)⟩)
              fun v w h => Subtype.ext (congrArg Subtype.val h :)
        _ = Nat.card {v : StdMod (Fin 4) (ZMod 2) // natAut (Γ α) γ v = v} *
            Nat.card {w : StdMod (Fin 4) (ZMod 2) // natAut (Γ α) (θ α γ) w = w} :=
            card_fix_pairAut _ _
        _ ≤ 4 * 4 :=
            Nat.mul_le_mul (card_fix_natAut_le α hγ2 hγ1) (card_fix_natAut_le α hθ2 hθ1)
    · rw [← card_stdMod_four]
      exact Nat.card_le_card_of_injective (fun v => (v : PairMod (Fin 4) (ZMod 2)).1)
        fun v w hvw => fst_injective_of_swap (Subgroup.mem_zpowers t) htt h hvw
  refine SL3Pair.le_rkIdx_of_card_mul_le card_pairMod_four _ ?_
  calc Nat.card ↥(fixV (Subgroup.zpowers t)) * 2 ^ 4 ≤ 16 * 2 ^ 4 := Nat.mul_le_mul_right _ hfix
    _ = 2 ^ 8 := by norm_num

theorem le_mParam
    {X : Subgroup (MulAut (PairMod (Fin 4) (ZMod 2)))} (hXN : X ≤ pairNormA7 α) :
    4 ≤ E3.mParam X := by
  classical
  have : Finite (MulAut (PairMod (Fin 4) (ZMod 2))) := MulEquiv.finite_left
  unfold E3.mParam
  split_ifs with hev
  · have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' (G := ↥X) 2 (even_iff_two_dvd.mp hev)
    refine le_csInf ⟨_, (t : MulAut (PairMod (Fin 4) (ZMod 2))), t.2,
      (Subgroup.orderOf_coe t).trans ht, rfl⟩ ?_
    rintro n ⟨s, hsX, hs2, rfl⟩
    exact four_le_rkIdx_fix α (hXN hsX) hs2
  · rw [rk, card_pairMod_four]
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    rw [padicValNat.prime_pow]
    norm_num

theorem exists_fix_ne_one {V : Type*} [CommGroup V] [Finite V] {P : Subgroup (MulAut V)}
    {p : ℕ} [Fact p.Prime] (hP : IsPGroup p P) {W : Subgroup V}
    (hW : ∀ g ∈ P, ∀ w ∈ W, g w ∈ W) (hp : p ∣ Nat.card W) :
    ∃ w ∈ W, w ≠ 1 ∧ w ∈ fixV P := by
  have hmod := Sp4.card_modEq_card_inf_fixV hP hW
  have h1 : p ∣ Nat.card ↥(W ⊓ fixV P) :=
    Nat.modEq_zero_iff_dvd.mp (hmod.symm.trans (Nat.modEq_zero_iff_dvd.mpr hp))
  have hne : W ⊓ fixV P ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at h1
    exact (Fact.out : p.Prime).one_lt.ne' (Nat.dvd_one.mp h1)
  obtain ⟨⟨w, hw⟩, hw1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hne
  exact ⟨w, hw.1, fun h => hw1 (Subtype.ext h), hw.2⟩

theorem not_mem_aSet
    {X : Subgroup (MulAut (PairMod (Fin 4) (ZMod 2)))} (hXN : X ≤ pairNormA7 α)
    {k : ℕ} (hk : 3 ≤ k) {A : Subgroup (MulAut (PairMod (Fin 4) (ZMod 2)))} :
    A ∉ E3.aSet k X := by
  rintro ⟨hAX, hA1, hA2, hB⟩
  have : Finite (MulAut (PairMod (Fin 4) (ZMod 2))) := MulEquiv.finite_left
  have hB' : ∀ B : Subgroup (MulAut (PairMod (Fin 4) (ZMod 2))), B ≤ A →
      E3.mQuot A B < k → fixV B = fixV A := hB
  have hA1' : A ≠ (⊥ : Subgroup (MulAut (PairMod (Fin 4) (ZMod 2)))) := hA1
  have hAN : A ≤ pairNormA7 α := hAX.trans hXN
  have hsq : ∀ x ∈ A, x * x = 1 := fun x hx => by rw [← sq]; exact hA2.2 x hx
  have hpg : IsPGroup 2 ↥A := E3.isPGroup_of_isElemAbelian2 hA2
  have h8 := card_le_eight α hAN hsq
  by_cases h4 : Nat.card A ≤ 4
  ·
    have hrk : rk ↥A ≤ 2 := by
      have hAc : Nat.card A = 2 ^ rk ↥A := card_eq_two_pow_of_isPGroup hpg
      rw [hAc] at h4
      by_contra h
      push Not at h
      have : 2 ^ 3 ≤ 2 ^ rk ↥A := Nat.pow_le_pow_right (by norm_num) h
      omega
    have h1 := hB' ⊥ bot_le (by rw [mQuot_bot_eq_rk]; omega)
    refine hA1' ((Subgroup.eq_bot_iff_forall A).mpr fun a ha => MulEquiv.ext fun v => ?_)
    have hv0 : v ∈ fixV (⊥ : Subgroup (MulAut (PairMod (Fin 4) (ZMod 2)))) := fun x hx => by
      rw [Subgroup.mem_bot.mp hx]
      rfl
    rw [h1] at hv0
    exact hv0 a ha
  ·
    push Not at h4
    have hA₀4 : Nat.card ↥(A ⊓ pairA7 α) ≤ 4 :=
      card_le_four_of_le α inf_le_right fun x hx => hsq x hx.1
    have h2 := card_le_two_mul_inf α hAN hsq
    have hm := E3.card_eq_two_pow_mul hpg (inf_le_left : A ⊓ pairA7 α ≤ A)
    have hA₀pos : 0 < Nat.card ↥(A ⊓ pairA7 α) := Nat.card_pos
    have hm1 : E3.mQuot A (A ⊓ pairA7 α) = 1 := by
      rcases Nat.lt_or_ge (E3.mQuot A (A ⊓ pairA7 α)) 1 with h | h
      · have h0 : E3.mQuot A (A ⊓ pairA7 α) = 0 := by omega
        rw [h0, pow_zero, one_mul] at hm
        omega
      · rcases Nat.lt_or_ge (E3.mQuot A (A ⊓ pairA7 α)) 2 with h' | h'
        · omega
        · have h3 : 4 ≤ 2 ^ E3.mQuot A (A ⊓ pairA7 α) :=
            calc 4 = 2 ^ 2 := by norm_num
              _ ≤ 2 ^ E3.mQuot A (A ⊓ pairA7 α) := Nat.pow_le_pow_right (by norm_num) h'
          have h5 : 4 * Nat.card ↥(A ⊓ pairA7 α) ≤ Nat.card A := by
            rw [hm]
            exact Nat.mul_le_mul_right _ h3
          omega
    have hfix := hB' (A ⊓ pairA7 α) inf_le_left (by rw [hm1]; omega)
    obtain ⟨y, hyA, hy⟩ : ∃ y ∈ A, y ∉ pairA7 α := by
      by_contra h
      push Not at h
      have hle : A ≤ A ⊓ pairA7 α := fun x hx => ⟨hx, h x hx⟩
      have := Subgroup.card_le_of_le hle
      omega
    have hy2 : (V₁ (Fin 4) (ZMod 2)).map y.toMonoidHom = V₂ (Fin 4) (ZMod 2) :=
      (map_V₁_eq_or' α (hAN hyA)).resolve_left fun h => hy (mem_pairA7_of_map α (hAN hyA) h)
    have hA₀p : IsPGroup 2 ↥(A ⊓ pairA7 α) := hpg.to_le inf_le_left
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have h16 : 2 * 8 = Nat.card ↥(V₁ (Fin 4) (ZMod 2)) := by rw [card_V₁]
    obtain ⟨v, hvV, hv1, hvfix⟩ := exists_fix_ne_one hA₀p (W := V₁ (Fin 4) (ZMod 2))
      (fun g hg w hw => by
        obtain ⟨γ, rfl⟩ := hg.2
        have hw' : w.2 = 1 := mem_V₁.mp hw
        exact mem_V₁.mpr (show (pairHom (Γ α) (θ α).toMonoidHom γ w).2 = 1 by
          rw [pairHom_apply, pairAut_apply, hw', map_one]))
      (Dvd.intro 8 h16)
    have hvA : v ∈ fixV A := by rw [← hfix]; exact hvfix
    exact hv1 (eq_one_of_fix_of_map_V₂ hy2 hvV (hvA y hyA))

theorem aParam_le
    {X : Subgroup (MulAut (PairMod (Fin 4) (ZMod 2)))} (hXN : X ≤ pairNormA7 α) :
    E3.aParam X ≤ 2 := by
  unfold E3.aParam
  split_ifs
  · apply csSup_le'
    rintro k ⟨-, A, hA⟩
    by_contra hk
    push Not at hk
    exact not_mem_aSet α hXN hk hA
  · norm_num

theorem le_betaH
    {X : Subgroup (MulAut (PairMod (Fin 4) (ZMod 2)))} (hXN : X ≤ pairNormA7 α) :
    (4 : ℕ∞) ≤ betaH X := by
  refine le_betaH_iff_isPGroup.mpr fun U _ hnp => ?_
  obtain ⟨p, hp, hp2, hpdvd⟩ : ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ p ∣ Nat.card ↥(X ⊓ centSub U) := by
    by_contra h
    push Not at h
    apply hnp
    refine IsPGroup.of_card (Nat.eq_prime_pow_of_unique_prime_dvd Nat.card_pos.ne' ?_)
    intro d hd hdd
    by_contra hd2
    exact h d hd hd2 hdd
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := ↥(X ⊓ centSub U)) p hpdvd
  have hyo : orderOf (y : MulAut (PairMod (Fin 4) (ZMod 2))) = p := by
    rw [Subgroup.orderOf_coe, hy]
  have hodd : Odd p := hp.odd_of_ne_two hp2
  have hyU : ∀ u ∈ U, (y : MulAut (PairMod (Fin 4) (ZMod 2))) u = u := mem_centSub.mp y.2.2
  obtain ⟨γ, hγ⟩ := mem_pairA7_of_odd α (hXN y.2.1) (hyo ▸ hodd)
  have hγo : orderOf γ = p := by
    rw [← orderOf_injective _ (pairHom_injective α) γ, hγ, hyo]
  have hθo : orderOf (θ α γ) = p := by rw [MulEquiv.orderOf_eq, hγo]
  have hγ1 : γ ≠ 1 := fun h => by
    rw [h, orderOf_one] at hγo
    exact hp.one_lt.ne hγo
  have hθ1 : θ α γ ≠ 1 := fun h => by
    rw [h, orderOf_one] at hθo
    exact hp.one_lt.ne hθo
  have hcard : Nat.card U ≤ 16 := by
    rw [← hγ] at hyU
    calc Nat.card U ≤ Nat.card {x : PairMod (Fin 4) (ZMod 2) //
          pairAut (natAut (Γ α) γ) (natAut (Γ α) (θ α γ)) x = x} :=
          Nat.card_le_card_of_injective (fun u => ⟨u, hyU u u.2⟩)
            fun u w h => Subtype.ext (congrArg Subtype.val h :)
      _ = Nat.card {v : StdMod (Fin 4) (ZMod 2) // natAut (Γ α) γ v = v} *
          Nat.card {w : StdMod (Fin 4) (ZMod 2) // natAut (Γ α) (θ α γ) w = w} :=
          card_fix_pairAut _ _
      _ ≤ 4 * 4 := Nat.mul_le_mul (card_fix_natAut_le_of_odd α hγ1 (hγo ▸ hodd))
          (card_fix_natAut_le_of_odd α hθ1 (hθo ▸ hodd))
  have h4 : 4 ≤ rkIdx U := by
    refine SL3Pair.le_rkIdx_of_card_mul_le card_pairMod_four U ?_
    calc Nat.card U * 2 ^ 4 ≤ 16 * 2 ^ 4 := Nat.mul_le_mul_right _ hcard
      _ = 2 ^ 8 := by norm_num
  exact_mod_cast h4

theorem H8_A7Pair_params
    {V : Type*} [CommGroup V] [Finite V] {H M : Subgroup (MulAut V)}
    {V₁ : Subgroup V} (hreal : A7Four H V₁ ⊥) {φ : MulAut V}
    (hφ : φ ∈ Subgroup.normalizer (H : Set (MulAut V)))
    (hinf : V₁ ⊓ V₁.map φ.toMonoidHom = ⊥) (hsup : V₁ ⊔ V₁.map φ.toMonoidHom = ⊤)
    (hniso : ¬ Pair.IsoMod H V₁ (V₁.map φ.toMonoidHom))
    (hMN : M ≤ Subgroup.normalizer (H : Set (MulAut V))) :
    E3.aParam M ≤ 2 ∧ 4 ≤ E3.mParam M ∧ CFSG.Open.pRank 2 M ≤ 3 ∧ (4 : ℕ∞) ≤ betaH M ∧
      alphaH M = 1 := by
  obtain ⟨α', e, h2⟩ := exists_model hreal hφ hinf hsup hniso hMN
  refine ⟨?_, ?_, ?_, ?_, (H8_A7Pair_alpha hreal hφ hinf hsup hniso hMN).2.1⟩
  · rw [← aParam_map_congrHom e]
    exact aParam_le α' h2
  · rw [← mParam_map_congrHom e]
    exact le_mParam α' h2
  · rw [← pRank_two_map_congrHom e]
    exact pRank_le α' h2
  · rw [← betaH_map_congrHom e]
    exact le_betaH α' h2

end A7

end H

end CFSG.Quasithin
