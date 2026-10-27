module

public import CFSG.Timmesfeld.ARS.CaseHCount

public section

namespace CFSG.Timmesfeld.ARS

open scoped commutatorElement Pointwise

variable {G : Type*} [Group G] {R : Set (Subgroup G)}

namespace CaseH

theorem sq_mem_of_mem_M (h : Hyp G R) {A : Subgroup G} (hA : A ∈ R) {m : G} (hm : m ∈ M R A) :
    m * m ∈ A := by
  have hR := h.root
  obtain ⟨-, -, hMM, -, -⟩ := Q_eq_M h hA
  let S : Subgroup G :=
    { carrier := {x | x ∈ M R A ∧ x * x ∈ A}
      mul_mem' := by
        rintro x y ⟨hx, hxx⟩ ⟨hy, hyy⟩
        refine ⟨(M R A).mul_mem hx hy, ?_⟩
        have hc : ⁅x⁻¹, y⁆ ∈ A := by
          rw [← hMM]
          exact Subgroup.commutator_mem_commutator ((M R A).inv_mem hx) hy
        have e : x * y * (x * y) = (x * x) * ⁅x⁻¹, y⁆ * (y * y) := by
          rw [commutatorElement_def]
          group
        rw [e]
        exact A.mul_mem (A.mul_mem hxx hc) hyy
      one_mem' := ⟨(M R A).one_mem, by rw [mul_one]; exact A.one_mem⟩
      inv_mem' := by
        rintro x ⟨hx, hxx⟩
        refine ⟨(M R A).inv_mem hx, ?_⟩
        rw [← mul_inv_rev]
        exact A.inv_mem hxx }
  have hle : M R A ≤ S := by
    refine sup_le (fun a ha => ⟨QD.le_M_self ha, A.mul_mem ha ha⟩) (iSup₂_le fun B hB b hb => ?_)
    exact ⟨QD.le_M hB hb, by rw [hR.mul_self B hB.1.1 b hb]; exact A.one_mem⟩
  exact (hle hm).2

theorem commuting_of_commute_of_card_eq_two [Finite G] {X Y : Subgroup G} (hX : Nat.card X = 2)
    (hY : Nat.card Y = 2) {x y : G} (hx : x ∈ X) (hx1 : x ≠ 1) (hy : y ∈ Y) (hy1 : y ≠ 1)
    (hxy : Commute x y) : Commuting X Y := by
  intro x' hx' y' hy'
  rcases eq_or_ne x' 1 with rfl | hx'1
  · exact Commute.one_left _
  rcases eq_or_ne y' 1 with rfl | hy'1
  · exact Commute.one_right _
  rw [eq_of_mem_of_card_eq_two hX hx hx1 hx' hx'1, eq_of_mem_of_card_eq_two hY hy hy1 hy' hy'1]
  exact hxy

section Order

variable (h : Hyp G R) (hH : SigmaEqLambda R)
include h hH

omit hH in
theorem sixteen_le_card_M {A : Subgroup G} (hA : A ∈ R) (hq : Nat.card A = 2)
    (hL : (linesThrough R A).ncard = 3) : 16 ≤ Nat.card (M R A) := by
  have := h.finite
  have hR := h.root
  have hiso := h.noIsolated
  obtain ⟨-, hpts, hMM, -, hMp⟩ := Q_eq_M h hA
  set S := insert A (lambdaSet R A) with hS
  have hSR : ∀ X ∈ S, X ∈ R := by
    rintro X (rfl | hX)
    · exact hA
    · exact hX.1.1
  have hSM : ∀ X ∈ S, X ≤ M R A := by
    rintro X (rfl | hX)
    · exact QD.le_M_self
    · exact QD.le_M hX
  have hS7 : S.ncard = 7 := by
    rw [hS, Set.ncard_insert_of_notMem (fun hl => hl.1.2.1 rfl) (Set.toFinite _),
      ncard_lambdaSet h hA, hL, hq]
  classical
  let f : Subgroup G → G := fun X => if hX : X ∈ R then (hR.exists_ne_one hX).choose else 1
  have hf : ∀ X ∈ R, f X ∈ X ∧ f X ≠ 1 := fun X hX => by
    simp only [f, hX, ↓reduceDIte]
    exact (hR.exists_ne_one hX).choose_spec
  have hfinj : Set.InjOn f S := by
    intro X hX Y hY hXY
    by_contra hne
    have hmem : f X ∈ X ⊓ Y := ⟨(hf X (hSR X hX)).1, hXY ▸ (hf Y (hSR Y hY)).1⟩
    rw [inf_eq_bot hR hiso (hSR X hX) (hSR Y hY) hne, Subgroup.mem_bot] at hmem
    exact (hf X (hSR X hX)).2 hmem
  set T : Set G := {x | x ∈ M R A ∧ x ≠ 1} with hT
  have hfT : f '' S ⊆ T := by
    rintro _ ⟨X, hX, rfl⟩
    exact ⟨hSM X hX (hf X (hSR X hX)).1, (hf X (hSR X hX)).2⟩
  have hTcard : T.ncard = Nat.card (M R A) - 1 := by
    rw [← Nat.card_coe_set_eq]
    exact Plane.card_subtype_mem_ne_one (M R A)
  have h7 : 7 ≤ T.ncard := by
    rw [← hS7, ← hfinj.ncard_image]
    exact Set.ncard_le_ncard hfT (Set.toFinite _)
  have hne8 : Nat.card (M R A) ≠ 8 := by
    intro h8
    have heq : f '' S = T := Set.eq_of_subset_of_ncard_le hfT
      (by rw [hfinj.ncard_image, hS7, hTcard, h8]) (Set.toFinite _)
    have hsq : ∀ x ∈ M R A, x * x = 1 := by
      intro x hx
      by_cases hx1 : x = 1
      · rw [hx1, mul_one]
      obtain ⟨X, hX, rfl⟩ := heq.symm ▸ (show x ∈ T from ⟨hx, hx1⟩)
      exact hR.mul_self X (hSR X hX) _ (hf X (hSR X hX)).1
    have hbot : ⁅M R A, M R A⁆ = ⊥ := by
      rw [eq_bot_iff, Subgroup.commutator_le]
      intro x hx y hy
      rw [Subgroup.mem_bot, commutatorElement_def]
      have hxi : x⁻¹ = x := inv_eq_of_mul_eq_one_right (hsq x hx)
      have hyi : y⁻¹ = y := inv_eq_of_mul_eq_one_right (hsq y hy)
      rw [hxi, hyi]
      exact hsq _ ((M R A).mul_mem hx hy) ▸ by group
    rw [hMM] at hbot
    exact hR.ne_bot A hA hbot
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 hMp
  rw [hk] at hTcard hne8 ⊢
  have h8 : 8 ≤ 2 ^ k := by omega
  have hk3 : 3 ≤ k := by
    by_contra hk3
    push Not at hk3
    have : 2 ^ k ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hk4 : 4 ≤ k := by
    rcases eq_or_lt_of_le hk3 with e | e
    · exact absurd (by rw [← e]; norm_num) hne8
    · omega
  calc 16 = 2 ^ 4 := by norm_num
    _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk4

theorem exists_mem_normalizer_notMem_M {A : Subgroup G} (hA : A ∈ R) (hq : Nat.card A = 2)
    (hL : (linesThrough R A).ncard = 3) :
    ∃ x ∈ Subgroup.normalizer (A : Set G), x ∉ M R A := by
  have := h.finite
  have hR := h.root
  have hiso := h.noIsolated
  have hcard : ∀ X ∈ R, Nat.card X = 2 := fun X hX => (hR.card_eq hX hA).trans hq
  obtain ⟨E, hE⟩ := lambdaSet_nonempty hR hiso h.nondeg hA
  have hER : E ∈ R := hE.1.1
  have hAE : A ∈ lambdaSet R E := mem_lambdaSet_comm hA hE
  have h4 : (lambdaSet R E \ pointsOn R (E ⊔ A)).ncard = 4 := by
    rw [ncard_lambdaSet_diff_pointsOn' h hER hAE, ncard_lambdaSet h hER,
      ncard_linesThrough_eq h hA hER, hL, hcard E hER]
  obtain ⟨D, hD, hDV⟩ : (lambdaSet R E \ pointsOn R (E ⊔ A)).Nonempty := by
    rw [← Set.ncard_pos (Set.toFinite _), h4]
    norm_num
  have hDR : D ∈ R := hD.1.1
  have hED : E ∈ lambdaSet R D := mem_lambdaSet_comm hER hD
  obtain ⟨D', ⟨hD', hD'V⟩, hD'W⟩ :
      ((lambdaSet R E \ pointsOn R (E ⊔ A)) \ pointsOn R (E ⊔ D)).Nonempty := by
    rw [Set.nonempty_iff_ne_empty, Ne, Set.sdiff_eq_empty]
    intro hsub
    have hsub' : lambdaSet R E \ pointsOn R (E ⊔ A) ⊆ lambdaSet R E ∩ pointsOn R (D ⊔ E) :=
      fun X hX => ⟨hX.1, by rw [sup_comm]; exact hsub hX⟩
    rw [lambdaSet_inter_pointsOn h hDR hED] at hsub'
    have := Set.ncard_le_ncard hsub' (Set.toFinite _)
    have hEW : E ∈ pointsOn R (D ⊔ E) := ⟨hER, le_sup_right⟩
    rw [h4, Set.ncard_sdiff_singleton_of_mem hEW, ncard_pointsOn h hDR hED, hcard D hDR] at this
    omega
  have hD'R : D' ∈ R := hD'.1.1
  have hnc : ∀ {X : Subgroup G}, X ∈ lambdaSet R E → X ∉ pointsOn R (E ⊔ A) →
      ¬ Commuting X A := by
    intro X hX hXV hXA
    apply hXV
    refine ⟨hX.1.1, ?_⟩
    rw [sup_comm]
    exact le_line h hH hA hE hA le_sup_left hER le_sup_right hE.1.2.1.symm hX.1.1 hXA
      hX.1.2.2.symm
  obtain ⟨-, hDA⟩ := special_of_mem_lambdaSet_of_mem_lambdaSet h hER hD hAE (hnc hD hDV)
  obtain ⟨-, hD'A⟩ := special_of_mem_lambdaSet_of_mem_lambdaSet h hER hD' hAE (hnc hD' hD'V)
  have hDD' : ¬ Commuting D D' := fun hc => hD'W ⟨hD'R, le_line h hH hER hD hER le_sup_left
    hDR le_sup_right hD.1.2.1.symm hD'R hD'.1.2.2.symm hc.symm⟩
  obtain ⟨-, hDD'E⟩ := special_of_mem_lambdaSet_of_mem_lambdaSet h hER hD hD' hDD'
  obtain ⟨a, ha, ha1⟩ := hR.exists_ne_one hA
  obtain ⟨e, he, he1⟩ := hR.exists_ne_one hER
  obtain ⟨d, hd, hd1⟩ := hR.exists_ne_one hDR
  obtain ⟨d', hd', hd'1⟩ := hR.exists_ne_one hD'R
  have hdd : d * d = 1 := hR.mul_self D hDR d hd
  have hd'd' : d' * d' = 1 := hR.mul_self D' hD'R d' hd'
  have hee : e * e = 1 := hR.mul_self E hER e he
  have hcomm : ∀ {X : Subgroup G} {x : G}, X ∈ R → x ∈ X → x ≠ 1 → ⁅X, A⁆ = E →
      ¬ Commuting X A → ⁅x, a⁆ = e := by
    intro X x hX hx hx1 hXA hnXA
    have hmem : ⁅x, a⁆ ∈ E := hXA ▸ Subgroup.commutator_mem_commutator hx ha
    refine eq_of_mem_of_card_eq_two (hcard E hER) he he1 hmem fun h1 => hnXA ?_
    exact commuting_of_commute_of_card_eq_two (hcard X hX) hq hx hx1 ha ha1
      (commutatorElement_eq_one_iff_commute.mp h1)
  have hda := hcomm hDR hd hd1 hDA (hnc hD hDV)
  have hd'a := hcomm hD'R hd' hd'1 hD'A (hnc hD' hD'V)
  have hde : Commute d e := (hD.1.2.2 e he d hd).symm
  set x := d * d' with hx
  have hxa : x * a * x⁻¹ = a := by
    have h1 : d' * a * d'⁻¹ = e * a := by rw [← hd'a, conj_eq_commutator_mul]
    have h2 : d * a * d⁻¹ = e * a := by rw [← hda, conj_eq_commutator_mul]
    calc x * a * x⁻¹ = d * (d' * a * d'⁻¹) * d⁻¹ := by rw [hx]; group
      _ = (d * e * d⁻¹) * (d * a * d⁻¹) := by rw [h1]; group
      _ = e * (e * a) := by rw [h2, hde.eq, mul_inv_cancel_right]
      _ = a := by rw [← mul_assoc, hee, one_mul]
  have hxN : x ∈ Subgroup.normalizer (A : Set G) := by
    refine Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.2 fun y hy => ?_)
    rcases eq_or_ne y 1 with rfl | hy1
    · rw [one_mul, mul_one]
    rw [eq_of_mem_of_card_eq_two hq ha ha1 hy hy1]
    calc a * x = (x * a * x⁻¹) * x := by rw [hxa]
      _ = x * a := by group
  refine ⟨x, hxN, fun hxM => ?_⟩
  have hsq := sq_mem_of_mem_M h hA hxM
  have hxx : x * x = ⁅d, d'⁆ := by
    rw [commutatorElement_def, inv_eq_of_mul_eq_one_right hdd, inv_eq_of_mul_eq_one_right hd'd',
      hx]
    group
  have hxE : x * x ∈ E := hxx ▸ hDD'E ▸ Subgroup.commutator_mem_commutator hd hd'
  have hxne : x * x ≠ 1 := by
    rw [hxx]
    intro h1
    exact hDD' (commuting_of_commute_of_card_eq_two (hcard D hDR) (hcard D' hD'R) hd hd1 hd'
      hd'1 (commutatorElement_eq_one_iff_commute.mp h1))
  have hmem : x * x ∈ A ⊓ E := ⟨hsq, hxE⟩
  rw [inf_eq_bot hR hiso hA hER hE.1.2.1.symm, Subgroup.mem_bot] at hmem
  exact hxne hmem

theorem thirty_two_le_card_normalizer {A : Subgroup G} (hA : A ∈ R) (hq : Nat.card A = 2)
    (hL : (linesThrough R A).ncard = 3) :
    32 ≤ Nat.card (Subgroup.normalizer (A : Set G)) := by
  have := h.finite
  obtain ⟨x, hxN, hxM⟩ := exists_mem_normalizer_notMem_M h hH hA hq hL
  set K := M R A ⊔ Subgroup.zpowers x with hK
  have hMK : M R A ≤ K := le_sup_left
  have hKN : K ≤ Subgroup.normalizer (A : Set G) :=
    sup_le (isPGroup_M h.root hA).2.1 ((Subgroup.zpowers_le).2 hxN)
  have hne : Nat.card (M R A) ≠ Nat.card K := by
    intro e
    exact hxM ((Subgroup.eq_of_le_of_card_ge hMK e.symm.le).symm ▸
      (le_sup_right : Subgroup.zpowers x ≤ K) (Subgroup.mem_zpowers x))
  obtain ⟨c, hc⟩ := Subgroup.card_dvd_of_le hMK
  have h16 := sixteen_le_card_M h hA hq hL
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hc
    exact absurd hc Nat.card_pos.ne'
  have hc1 : c ≠ 1 := by
    rintro rfl
    rw [mul_one] at hc
    exact hne hc.symm
  have hc2 : 2 ≤ c := by omega
  calc 32 = 16 * 2 := by norm_num
    _ ≤ Nat.card (M R A) * c := Nat.mul_le_mul h16 hc2
    _ = Nat.card K := hc.symm
    _ ≤ _ := Subgroup.card_le_of_le hKN

end Order

theorem card_eq_ncard_mul_card_normalizer (hR : IsRootClass R) [Finite G] {A : Subgroup G}
    (hA : A ∈ R) : Nat.card G = R.ncard * Nat.card (Subgroup.normalizer (A : Set G)) := by
  set st := MulAction.stabilizer (ConjAct G) A with hst
  have horb : MulAction.orbit (ConjAct G) A = R := by
    ext B
    constructor
    · rintro ⟨c, rfl⟩
      exact hR.conjSub_mem hA (ConjAct.ofConjAct c)
    · intro hB
      obtain ⟨g, rfl⟩ := hR.exists_conjSub_eq hA hB
      exact ⟨ConjAct.toConjAct g, rfl⟩
  have hmem : ∀ g : G, ConjAct.toConjAct g ∈ st ↔ g ∈ Subgroup.normalizer (A : Set G) := by
    intro g
    rw [MulAction.mem_stabilizer_iff, ← conjSub_eq_self_iff]
    rfl
  have hcard : Nat.card st = Nat.card (Subgroup.normalizer (A : Set G)) := by
    refine Nat.card_congr
      { toFun := fun c => ⟨ConjAct.ofConjAct c.1, (hmem _).1 c.2⟩
        invFun := fun n => ⟨ConjAct.toConjAct n.1, (hmem _).2 n.2⟩
        left_inv := fun c => rfl
        right_inv := fun n => rfl }
  have h1 := st.card_mul_index
  rw [MulAction.index_stabilizer, horb, hcard] at h1
  rw [mul_comm, h1]
  exact (Nat.card_congr ConjAct.ofConjAct.toEquiv).symm

theorem two_thousand_sixteen_le_card (h : Hyp G R) (hH : SigmaEqLambda R) {A : Subgroup G}
    (hA : A ∈ R) (hq : Nat.card A = 2) (hL : (linesThrough R A).ncard = 3) :
    2016 ≤ Nat.card G := by
  have := h.finite
  rw [card_eq_ncard_mul_card_normalizer h.root hA, ncard_eq h hH hA hq hL]
  have := thirty_two_le_card_normalizer h hH hA hq hL
  norm_num
  omega

end CaseH

end CFSG.Timmesfeld.ARS
