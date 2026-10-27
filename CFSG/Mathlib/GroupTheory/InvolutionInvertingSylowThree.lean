module

public import CFSG.Open.LocalVocabulary
public import CFSG.Open.StatedDefs
import CFSG.Adapters.StatedSLTwoField
import CFSG.Adapters.StatedClassicalSmallOrders

@[expose] public section

namespace CFSG.InvolutionInvertingSylowThree

open CFSG.Open (StatedClassicalModel)

private theorem invSyl3_finite_sylow {X : Type} [Group X] [Finite X] :
    Finite (Sylow 3 X) :=
  Finite.of_injective (fun P : Sylow 3 X => (P : Set X))
    (fun P Q h => Sylow.ext (SetLike.coe_injective h))

private theorem invSyl3_closure_pair {X : Type} [Group X] {a b t : X}
    (ha : a ^ 3 = 1) (hb : b ^ 3 = 1) (hab : a * b = b * a)
    (hta : t * a * t⁻¹ = a⁻¹) (htb : t * b * t⁻¹ = b⁻¹) :
    IsPGroup 3 (Subgroup.closure ({a, b} : Set X)) ∧
      ∀ y ∈ Subgroup.closure ({a, b} : Set X), t * y * t⁻¹ = y⁻¹ := by
  let Y : Subgroup X := Subgroup.closure ({a, b} : Set X)
  have hpair : ({a, b} : Set X).Pairwise Commute := by
    intro x hx y hy hxy
    have hx' : x = a ∨ x = b := by simpa using hx
    have hy' : y = a ∨ y = b := by simpa using hy
    rcases hx' with hx' | hx' <;> rcases hy' with hy' | hy'
    · rw [hx', hy']
    · rw [hx', hy']; exact hab
    · rw [hx', hy']; exact hab.symm
    · rw [hx', hy']
  haveI hcomm : IsMulCommutative Y := Subgroup.isMulCommutative_closure hpair
  have hcommY : ∀ x y : X, x ∈ Y → y ∈ Y → Commute x y :=
    fun x y hx hy => setLike_mul_comm hx hy
  have key : ∀ y ∈ Y, y ^ 3 = 1 ∧ t * y * t⁻¹ = y⁻¹ := by
    intro y hy
    refine Subgroup.closure_induction (k := ({a, b} : Set X)) ?_ ?_ ?_ ?_ hy
    · intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl
      · exact ⟨ha, hta⟩
      · exact ⟨hb, htb⟩
    · refine ⟨by simp, ?_⟩
      simp
    · intro x y hx hy ihx ihy
      refine ⟨?_, ?_⟩
      · rw [(hcommY x y hx hy).mul_pow 3, ihx.1, ihy.1, mul_one]
      · calc
          t * (x * y) * t⁻¹ = (t * x * t⁻¹) * (t * y * t⁻¹) := by group
          _ = x⁻¹ * y⁻¹ := by rw [ihx.2, ihy.2]
          _ = (x * y)⁻¹ := by
            rw [_root_.mul_inv_rev]
            exact (hcommY x y hx hy).inv_inv.eq
    · intro x hx ihx
      refine ⟨?_, ?_⟩
      · rw [inv_pow, ihx.1, inv_one]
      · calc
          t * x⁻¹ * t⁻¹ = (t * x * t⁻¹)⁻¹ := by group
          _ = (x⁻¹)⁻¹ := by rw [ihx.2]
  refine ⟨fun y => ⟨1, ?_⟩, fun y hy => (key y hy).2⟩
  rw [pow_one]
  exact Subtype.ext (key (y : X) y.2).1

private theorem invSyl3_closure_card {X : Type} [Group X] [Finite X]
    (a b : X) (hb : b ^ 3 = 1) (hb1 : b ≠ 1) (hne : a ∉ Subgroup.zpowers b)
    (hX3 : Nat.factorization (Nat.card X) 3 = 2)
    (hY3 : IsPGroup 3 (Subgroup.closure ({a, b} : Set X))) :
    Nat.card (Subgroup.closure ({a, b} : Set X)) = 9 := by
  let Y : Subgroup X := Subgroup.closure ({a, b} : Set X)
  have hb3 : orderOf b = 3 := orderOf_eq_prime hb hb1
  have hzcard : Nat.card (Subgroup.zpowers b) = 3 := by rw [Nat.card_zpowers, hb3]
  have hzY : Subgroup.zpowers b ≤ Y :=
    Subgroup.zpowers_le.mpr (Subgroup.subset_closure (by simp))
  have hlt : 3 < Nat.card Y := by
    have hge : 3 ≤ Nat.card Y := by
      rw [← hzcard]
      exact Subgroup.card_le_of_le hzY
    have hne3 : Nat.card Y ≠ 3 := by
      intro h3
      have heq : Subgroup.zpowers b = Y := by
        apply Subgroup.eq_of_le_of_card_ge hzY
        rw [h3, hzcard]
      exact hne (heq ▸ Subgroup.subset_closure (by simp : a ∈ ({a, b} : Set X)))
    omega
  obtain ⟨P, hP⟩ := IsPGroup.exists_le_sylow hY3
  have hPcard : Nat.card P = 9 := by
    rw [Sylow.card_eq_multiplicity, hX3]
    norm_num
  have hdvd : Nat.card Y ∣ 9 := by
    have h := Subgroup.card_subgroup_dvd_card (Y.subgroupOf P)
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hP).toEquiv, hPcard] at h
    exact h
  have hle9 : Nat.card Y ≤ 9 := Nat.le_of_dvd (by norm_num) hdvd
  interval_cases Nat.card Y <;> norm_num at hdvd
  rfl

private theorem invSyl3_sylow_of_pair {X : Type} [Group X] [Finite X]
    (hX3 : Nat.factorization (Nat.card X) 3 = 2)
    (a b t : X) (ha : a ^ 3 = 1) (hb : b ^ 3 = 1) (hab : a * b = b * a)
    (hb1 : b ≠ 1) (hne : a ∉ Subgroup.zpowers b)
    (ht : t ^ 2 = 1) (hta : t * a * t⁻¹ = a⁻¹) (htb : t * b * t⁻¹ = b⁻¹) :
    ∃ P : Sylow 3 X, t ^ 2 = 1 ∧ ∀ y ∈ P, t * y * t⁻¹ = y⁻¹ := by
  have hcl := invSyl3_closure_pair ha hb hab hta htb
  have hcard := invSyl3_closure_card a b hb hb1 hne hX3 hcl.1
  let P : Sylow 3 X :=
    Sylow.ofCard (Subgroup.closure ({a, b} : Set X)) (by rw [hcard, hX3]; norm_num)
  exact ⟨P, ht, fun y hy => hcl.2 y hy⟩

private theorem invSyl3_inverting_of_sylow {X : Type} [Group X] [Finite X]
    (P : Sylow 3 X) (t₀ : X) (ht₀ : t₀ ^ 2 = 1)
    (hinv : ∀ y ∈ P, t₀ * y * t₀⁻¹ = y⁻¹) (Q : Sylow 3 X) :
    ∃ t : X, t ^ 2 = 1 ∧ ∀ y ∈ Q, t * y * t⁻¹ = y⁻¹ := by
  haveI : Finite (Sylow 3 X) := invSyl3_finite_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq X P Q
  refine ⟨g * t₀ * g⁻¹, ?_, ?_⟩
  · have ht : t₀ * t₀ = 1 := by rw [← pow_two]; exact ht₀
    rw [pow_two]
    calc
      (g * t₀ * g⁻¹) * (g * t₀ * g⁻¹) = g * (t₀ * t₀) * g⁻¹ := by group
      _ = g * 1 * g⁻¹ := by rw [ht]
      _ = 1 := by group
  · intro y hy
    have hy' : y ∈ ((g • P : Sylow 3 X) : Subgroup X) := by rw [hg]; exact hy
    rw [Sylow.coe_subgroup_smul] at hy'
    obtain ⟨p, hp, hgp⟩ :=
      (Subgroup.mem_smul_pointwise_iff_exists (m := y) (a := MulAut.conj g)
        (S := (P : Subgroup X))).mp hy'
    rw [MulAut.smul_def, MulAut.conj_apply] at hgp
    calc
      (g * t₀ * g⁻¹) * y * (g * t₀ * g⁻¹)⁻¹ = g * (t₀ * p * t₀⁻¹) * g⁻¹ := by
        rw [← hgp]; group
      _ = g * p⁻¹ * g⁻¹ := by rw [hinv p hp]
      _ = y⁻¹ := by rw [← hgp]; group

private theorem invSyl3_sylow_subgroupOf {G : Type} [Group G] {J Y : Subgroup G}
    (hYJ : Y ≤ J) (hY : IsPGroup 3 Y)
    (hmax : ∀ P : Subgroup G, P ≤ J → IsPGroup 3 P → Y ≤ P → P = Y) :
    IsPGroup 3 (Y.subgroupOf J) ∧
      ∀ Q : Subgroup ↥J, IsPGroup 3 Q → Y.subgroupOf J ≤ Q → Q = Y.subgroupOf J := by
  constructor
  · exact hY.comap_of_injective J.subtype Subtype.coe_injective
  · intro Q hQ hle
    have hQmap : IsPGroup 3 (Q.map J.subtype) := hQ.map J.subtype
    have hQJ : Q.map J.subtype ≤ J := by
      rintro x ⟨q, -, rfl⟩
      exact q.2
    have hYle : Y ≤ Q.map J.subtype := by
      rw [← Subgroup.map_subgroupOf_eq_of_le hYJ]
      exact Subgroup.map_mono hle
    have hEq : Q.map J.subtype = Y := hmax _ hQJ hQmap hYle
    rw [← hEq]
    exact (Subgroup.comap_map_eq_self_of_injective J.subtype_injective Q).symm

private theorem invSyl3_inverts_of_equiv {G : Type} [Group G] {J : Subgroup G} [Finite J]
    {X : Type} [Group X] [Finite X] (e : J ≃* X)
    (Y : Subgroup J) (hY : IsPGroup 3 Y)
    (hmax : ∀ Q : Subgroup J, IsPGroup 3 Q → Y ≤ Q → Q = Y)
    {P : Sylow 3 X} {t₀ : X} (ht₀ : t₀ ^ 2 = 1)
    (hinv : ∀ y ∈ P, t₀ * y * t₀⁻¹ = y⁻¹) :
    ∃ t : J, t ^ 2 = 1 ∧ ∀ y ∈ Y, t * y * t⁻¹ = y⁻¹ := by
  let Y' : Sylow 3 J :=
    { toSubgroup := Y
      isPGroup' := hY
      is_maximal' := fun hQ hle => hmax _ hQ hle }
  let PJ : Sylow 3 J :=
    P.mapSurjective (f := (e.symm : X →* J)) (fun y => ⟨e y, by simp⟩)
  have hPJ : (PJ : Subgroup J) = P.map (e.symm : X →* J) := rfl
  let t₀J : J := e.symm t₀
  have ht₀J : t₀J ^ 2 = 1 := by
    change (e.symm t₀) ^ 2 = 1
    rw [← map_pow, ht₀, map_one]
  have hinvJ : ∀ y ∈ PJ, t₀J * y * t₀J⁻¹ = y⁻¹ := by
    intro y hy
    have hy' : y ∈ (PJ : Subgroup J) := hy
    rw [hPJ, Subgroup.mem_map] at hy'
    obtain ⟨p, hp, hpy⟩ := hy'
    rw [← hpy]
    change e.symm t₀ * e.symm p * (e.symm t₀)⁻¹ = (e.symm p)⁻¹
    simpa only [map_mul, map_inv] using congrArg (⇑e.symm) (hinv p hp)
  exact invSyl3_inverting_of_sylow PJ t₀J ht₀J hinvJ Y'

private def invSyl3_a4 : Matrix.SpecialLinearGroup (Fin 4) (ZMod 2) :=
  ⟨!![0, 1, 0, 0; 1, 1, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1], by decide +kernel⟩

private def invSyl3_b4 : Matrix.SpecialLinearGroup (Fin 4) (ZMod 2) :=
  ⟨!![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 0, 1; 0, 0, 1, 1], by decide +kernel⟩

private def invSyl3_t4 : Matrix.SpecialLinearGroup (Fin 4) (ZMod 2) :=
  ⟨!![0, 1, 0, 0; 1, 0, 0, 0; 0, 0, 0, 1; 0, 0, 1, 0], by decide +kernel⟩

private def invSyl3_a5 : Matrix.SpecialLinearGroup (Fin 5) (ZMod 2) :=
  ⟨!![0, 1, 0, 0, 0; 1, 1, 0, 0, 0; 0, 0, 1, 0, 0; 0, 0, 0, 1, 0;
     0, 0, 0, 0, 1], by decide +kernel⟩

private def invSyl3_b5 : Matrix.SpecialLinearGroup (Fin 5) (ZMod 2) :=
  ⟨!![1, 0, 0, 0, 0; 0, 1, 0, 0, 0; 0, 0, 0, 1, 0; 0, 0, 1, 1, 0;
     0, 0, 0, 0, 1], by decide +kernel⟩

private def invSyl3_t5 : Matrix.SpecialLinearGroup (Fin 5) (ZMod 2) :=
  ⟨!![0, 1, 0, 0, 0; 1, 0, 0, 0, 0; 0, 0, 0, 1, 0; 0, 0, 1, 0, 0;
     0, 0, 0, 0, 1], by decide +kernel⟩

private theorem invSyl3_data_four
    (hX3 : Nat.factorization
      (Nat.card (Matrix.SpecialLinearGroup (Fin 4) (ZMod 2))) 3 = 2) :
    ∃ P : Sylow 3 (Matrix.SpecialLinearGroup (Fin 4) (ZMod 2)),
      ∃ t : Matrix.SpecialLinearGroup (Fin 4) (ZMod 2),
        t ^ 2 = 1 ∧ ∀ y ∈ P, t * y * t⁻¹ = y⁻¹ := by
  have ha : invSyl3_a4 ^ 3 = 1 := by decide +kernel
  have hb : invSyl3_b4 ^ 3 = 1 := by decide +kernel
  have hab : invSyl3_a4 * invSyl3_b4 = invSyl3_b4 * invSyl3_a4 := by decide +kernel
  have hb1 : invSyl3_b4 ≠ 1 := by decide +kernel
  have hne : invSyl3_a4 ∉ Subgroup.zpowers invSyl3_b4 := by
    have hb3 : orderOf invSyl3_b4 = 3 := orderOf_eq_prime hb hb1
    rw [IsOfFinOrder.mem_zpowers_iff_mem_range_orderOf
      (isOfFinOrder_of_finite invSyl3_b4), hb3]
    decide +kernel
  have ht : invSyl3_t4 ^ 2 = 1 := by decide +kernel
  have ht1 : invSyl3_t4 * invSyl3_t4 = 1 := by rw [← pow_two]; exact ht
  have htinv : invSyl3_t4⁻¹ = invSyl3_t4 := inv_eq_of_mul_eq_one_right ht1
  have hainv : invSyl3_a4⁻¹ = invSyl3_a4 * invSyl3_a4 := by
    refine inv_eq_of_mul_eq_one_right ?_
    rw [← pow_three]
    exact ha
  have hbinv : invSyl3_b4⁻¹ = invSyl3_b4 * invSyl3_b4 := by
    refine inv_eq_of_mul_eq_one_right ?_
    rw [← pow_three]
    exact hb
  have hta : invSyl3_t4 * invSyl3_a4 * invSyl3_t4⁻¹ = invSyl3_a4⁻¹ := by
    rw [htinv, hainv]
    decide +kernel
  have htb : invSyl3_t4 * invSyl3_b4 * invSyl3_t4⁻¹ = invSyl3_b4⁻¹ := by
    rw [htinv, hbinv]
    decide +kernel
  obtain ⟨P, ht', hinv⟩ :=
    invSyl3_sylow_of_pair hX3 invSyl3_a4 invSyl3_b4 invSyl3_t4 ha hb hab hb1 hne ht hta htb
  exact ⟨P, invSyl3_t4, ht', hinv⟩

private theorem invSyl3_data_five
    (hX3 : Nat.factorization
      (Nat.card (Matrix.SpecialLinearGroup (Fin 5) (ZMod 2))) 3 = 2) :
    ∃ P : Sylow 3 (Matrix.SpecialLinearGroup (Fin 5) (ZMod 2)),
      ∃ t : Matrix.SpecialLinearGroup (Fin 5) (ZMod 2),
        t ^ 2 = 1 ∧ ∀ y ∈ P, t * y * t⁻¹ = y⁻¹ := by
  have ha : invSyl3_a5 ^ 3 = 1 := by decide +kernel
  have hb : invSyl3_b5 ^ 3 = 1 := by decide +kernel
  have hab : invSyl3_a5 * invSyl3_b5 = invSyl3_b5 * invSyl3_a5 := by decide +kernel
  have hb1 : invSyl3_b5 ≠ 1 := by decide +kernel
  have hne : invSyl3_a5 ∉ Subgroup.zpowers invSyl3_b5 := by
    have hb3 : orderOf invSyl3_b5 = 3 := orderOf_eq_prime hb hb1
    rw [IsOfFinOrder.mem_zpowers_iff_mem_range_orderOf
      (isOfFinOrder_of_finite invSyl3_b5), hb3]
    decide +kernel
  have ht : invSyl3_t5 ^ 2 = 1 := by decide +kernel
  have ht1 : invSyl3_t5 * invSyl3_t5 = 1 := by rw [← pow_two]; exact ht
  have htinv : invSyl3_t5⁻¹ = invSyl3_t5 := inv_eq_of_mul_eq_one_right ht1
  have hainv : invSyl3_a5⁻¹ = invSyl3_a5 * invSyl3_a5 := by
    refine inv_eq_of_mul_eq_one_right ?_
    rw [← pow_three]
    exact ha
  have hbinv : invSyl3_b5⁻¹ = invSyl3_b5 * invSyl3_b5 := by
    refine inv_eq_of_mul_eq_one_right ?_
    rw [← pow_three]
    exact hb
  have hta : invSyl3_t5 * invSyl3_a5 * invSyl3_t5⁻¹ = invSyl3_a5⁻¹ := by
    rw [htinv, hainv]
    decide +kernel
  have htb : invSyl3_t5 * invSyl3_b5 * invSyl3_t5⁻¹ = invSyl3_b5⁻¹ := by
    rw [htinv, hbinv]
    decide +kernel
  obtain ⟨P, ht', hinv⟩ :=
    invSyl3_sylow_of_pair hX3 invSyl3_a5 invSyl3_b5 invSyl3_t5 ha hb hab hb1 hne ht hta htb
  exact ⟨P, invSyl3_t5, ht', hinv⟩

theorem exists_inverting_involution {G : Type} [Group G] {J Y : Subgroup G} {m : ℕ}
    (hm : m = 4 ∨ m = 5) (hJ : StatedClassicalModel ↥J .PSL m 2 1) (hYJ : Y ≤ J)
    (hY : IsPGroup 3 Y)
    (hmax : ∀ P : Subgroup G, P ≤ J → IsPGroup 3 P → Y ≤ P → P = Y) :
    ∃ t ∈ J, t ^ 2 = 1 ∧ ∀ y ∈ Y, t * y * t⁻¹ = y⁻¹ := by
  obtain rfl | rfl := hm
  · obtain ⟨e⟩ := CFSG.Open.StatedAPI.nonempty_mulEquiv_specialLinear_zmod_two_of_psl hJ
    have hcardJ : Nat.card ↥J = 20160 :=
      CFSG.Open.StatedAPI.card_of_statedClassicalModel_psl_four_two hJ
    haveI : Finite ↥J := Nat.finite_of_card_ne_zero (by rw [hcardJ]; norm_num)
    have hcardX : Nat.card (Matrix.SpecialLinearGroup (Fin 4) (ZMod 2)) = 20160 :=
      (Nat.card_congr e.toEquiv).symm.trans hcardJ
    have hX3 : Nat.factorization
        (Nat.card (Matrix.SpecialLinearGroup (Fin 4) (ZMod 2))) 3 = 2 := by
      rw [hcardX]
      decide +kernel
    obtain ⟨hYs, hmaxs⟩ := invSyl3_sylow_subgroupOf hYJ hY hmax
    obtain ⟨P, t₀, ht₀, hinv₀⟩ := invSyl3_data_four hX3
    obtain ⟨t, ht, hinv⟩ :=
      invSyl3_inverts_of_equiv e (Y.subgroupOf J) hYs hmaxs ht₀ hinv₀
    refine ⟨(t : G), t.2, ?_, ?_⟩
    · simpa using congrArg Subtype.val ht
    · intro y hy
      have hy' : (⟨y, hYJ hy⟩ : ↥J) ∈ Y.subgroupOf J := hy
      have h := hinv ⟨y, hYJ hy⟩ hy'
      simpa using congrArg Subtype.val h
  · obtain ⟨e⟩ := CFSG.Open.StatedAPI.nonempty_mulEquiv_specialLinear_zmod_two_of_psl hJ
    have hcardJ : Nat.card ↥J = 9999360 :=
      CFSG.Open.StatedAPI.card_of_statedClassicalModel_psl_five_two hJ
    haveI : Finite ↥J := Nat.finite_of_card_ne_zero (by rw [hcardJ]; norm_num)
    have hcardX : Nat.card (Matrix.SpecialLinearGroup (Fin 5) (ZMod 2)) = 9999360 :=
      (Nat.card_congr e.toEquiv).symm.trans hcardJ
    have hX3 : Nat.factorization
        (Nat.card (Matrix.SpecialLinearGroup (Fin 5) (ZMod 2))) 3 = 2 := by
      rw [hcardX]
      decide +kernel
    obtain ⟨hYs, hmaxs⟩ := invSyl3_sylow_subgroupOf hYJ hY hmax
    obtain ⟨P, t₀, ht₀, hinv₀⟩ := invSyl3_data_five hX3
    obtain ⟨t, ht, hinv⟩ :=
      invSyl3_inverts_of_equiv e (Y.subgroupOf J) hYs hmaxs ht₀ hinv₀
    refine ⟨(t : G), t.2, ?_, ?_⟩
    · simpa using congrArg Subtype.val ht
    · intro y hy
      have hy' : (⟨y, hYJ hy⟩ : ↥J) ∈ Y.subgroupOf J := hy
      have h := hinv ⟨y, hYJ hy⟩ hy'
      simpa using congrArg Subtype.val h

end CFSG.InvolutionInvertingSylowThree

end
