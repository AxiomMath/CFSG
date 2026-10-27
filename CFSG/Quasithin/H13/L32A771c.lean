module

public import CFSG.Quasithin.H13.L32A712
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.Quasithin.H13.L32A

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.RuType
open scoped MatrixGroups

@[expose] def trF4 (x : F4) : ZMod 2 := if x.code.val < 2 then 0 else 1

@[expose] def stB (w v : Fin 2 → F4) : ZMod 2 := trF4 (w 0 * v 1 + w 1 * v 0)

@[expose] def stE (i : Fin 4) : Fin 2 → F4 :=
  ![![1, 0], ![F4.ω, 0], ![0, 1], ![0, F4.ω]] i

@[expose] def f4Of (a b : ZMod 2) : F4 :=
  ⟨if a = 0 then (if b = 0 then 0 else 1) else (if b = 0 then 3 else 2)⟩

@[expose] def stDual (a : Fin 4 → ZMod 2) : Fin 2 → F4 := ![f4Of (a 2) (a 3), f4Of (a 0) (a 1)]

@[expose] def smF4 (c : ZMod 2) (x : Fin 2 → F4) : Fin 2 → F4 := if c = 0 then 0 else x

@[expose] def stCoord (v : Fin 2 → F4) (i : Fin 4) : ZMod 2 :=
  ![(((v 0).code.val % 2 : ℕ) : ZMod 2), (((v 0).code.val / 2 : ℕ) : ZMod 2),
    (((v 1).code.val % 2 : ℕ) : ZMod 2), (((v 1).code.val / 2 : ℕ) : ZMod 2)] i

theorem stB_stDual : ∀ (a : Fin 4 → ZMod 2) (i : Fin 4), stB (stDual a) (stE i) = a i := by
  decide

theorem stB_add_right : ∀ w v v' : Fin 2 → F4, stB w (v + v') = stB w v + stB w v' := by
  decide

theorem stB_smF4 : ∀ (w : Fin 2 → F4) (c : ZMod 2) (x : Fin 2 → F4),
    stB w (smF4 c x) = c * stB w x := by
  decide

theorem stDual_add : ∀ a b : Fin 4 → ZMod 2, stDual (a + b) = stDual a + stDual b := by
  decide

theorem stB_ext : ∀ w w' : Fin 2 → F4, (∀ i, stB w (stE i) = stB w' (stE i)) → w = w' := by
  decide

theorem stB_mulVec : ∀ (A : SL(2, F4)) (w : Fin 2 → F4) (i : Fin 4),
    stB ((A : Matrix (Fin 2) (Fin 2) F4).mulVec w) (stE i) =
      stB w (((A⁻¹ : SL(2, F4)) : Matrix (Fin 2) (Fin 2) F4).mulVec (stE i)) := by
  decide +kernel

theorem eq_sum_stE : ∀ v : Fin 2 → F4, v = smF4 (stCoord v 0) (stE 0) + smF4 (stCoord v 1) (stE 1) +
    smF4 (stCoord v 2) (stE 2) + smF4 (stCoord v 3) (stE 3) := by
  decide

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
open Classical in
theorem ite_mul_of_card_two {V₁ : Subgroup G} (hV1 : Nat.card ↥V₁ = 2) {a b : G} (ha : a ∈ V₁)
    (hb : b ∈ V₁) : (if a * b = 1 then (0 : ZMod 2) else 1) =
      (if a = 1 then 0 else 1) + (if b = 1 then 0 else 1) := by
  obtain ⟨z, hzV, hz1, hgen⟩ := exists_gen_of_card_two hV1
  have hzz : z * z = 1 := by
    rcases hgen _ (mul_mem hzV hzV) with h | h
    · exact h
    · exfalso
      apply hz1
      calc z = z⁻¹ * (z * z) := by group
        _ = 1 := by rw [h, inv_mul_cancel]
  rcases hgen a ha with rfl | rfl <;> rcases hgen b hb with rfl | rfl
  · simp
  · simp [hz1]
  · simp [hz1]
  · rw [hzz]
    simp [hz1]
    decide

omit [Finite G] in
theorem isL24Section_dual {K Q U V₁ : Subgroup G} (hU : IsL24Section K U V₁)
    (hUc : ∀ a ∈ U, ∀ b ∈ U, a * b = b * a) (hV1 : Nat.card ↥V₁ = 2) (hV1U : V₁ ≤ U)
    (hQV : Q ≤ Subgroup.centralizer (V₁ : Set G)) (hKV : K ≤ Subgroup.centralizer (V₁ : Set G))
    (hKQ : K ≤ Subgroup.normalizer (Q : Set G))
    (hQU : ∀ q ∈ Q, ∀ u ∈ U, q * u * q⁻¹ * u⁻¹ ∈ V₁)
    (hrel : (Q ⊓ Subgroup.centralizer (U : Set G)).relIndex Q = 16) :
    IsL24Section K Q (Q ⊓ Subgroup.centralizer (U : Set G)) := by
  classical
  obtain ⟨hKU, π, β₀, hπs, hπk, hβs, hβk, hβe⟩ := hU
  set ε : G → ZMod 2 := fun g => if g = 1 then 0 else 1 with hε
  have hεmul : ∀ {a b : G}, a ∈ V₁ → b ∈ V₁ → ε (a * b) = ε a + ε b := fun ha hb =>
    ite_mul_of_card_two hV1 ha hb
  have hε0 : ∀ {a : G}, a ∈ V₁ → ε a = 0 → a = 1 := fun {a} _ h => by
    by_contra h1
    simp [hε, h1] at h
  have hcomm_right : ∀ q ∈ Q, ∀ u ∈ U, ∀ u' ∈ U, q * (u * u') * q⁻¹ * (u * u')⁻¹ =
      (q * u * q⁻¹ * u⁻¹) * (q * u' * q⁻¹ * u'⁻¹) := by
    intro q hq u hu u' hu'
    have hc : u * (q * u' * q⁻¹ * u'⁻¹) = (q * u' * q⁻¹ * u'⁻¹) * u :=
      hUc _ hu _ (hV1U (hQU q hq u' hu'))
    calc q * (u * u') * q⁻¹ * (u * u')⁻¹ =
        (q * u * q⁻¹ * u⁻¹) * (u * (q * u' * q⁻¹ * u'⁻¹)) * u⁻¹ := by group
      _ = (q * u * q⁻¹ * u⁻¹) * (q * u' * q⁻¹ * u'⁻¹) := by rw [hc]; group
  have hcomm_left : ∀ q ∈ Q, ∀ q' ∈ Q, ∀ u ∈ U, q * q' * u * (q * q')⁻¹ * u⁻¹ =
      (q * u * q⁻¹ * u⁻¹) * (q' * u * q'⁻¹ * u⁻¹) := by
    intro q hq q' hq' u hu
    have hc := Subgroup.mem_centralizer_iff.mp (hQV hq) _ (hQU q' hq' u hu)
    have hc' : (q * u * q⁻¹ * u⁻¹) * (q' * u * q'⁻¹ * u⁻¹) =
        (q' * u * q'⁻¹ * u⁻¹) * (q * u * q⁻¹ * u⁻¹) :=
      hUc _ (hV1U (hQU q hq u hu)) _ (hV1U (hQU q' hq' u hu))
    rw [hc']
    calc q * q' * u * (q * q')⁻¹ * u⁻¹ =
        q * (q' * u * q'⁻¹ * u⁻¹) * q⁻¹ * (q * u * q⁻¹ * u⁻¹) := by group
      _ = (q' * u * q'⁻¹ * u⁻¹) * (q * u * q⁻¹ * u⁻¹) := by
          rw [show q * (q' * u * q'⁻¹ * u⁻¹) * q⁻¹ =
            (q * (q' * u * q'⁻¹ * u⁻¹)) * q⁻¹ by group, ← hc]
          group
  have hcomm_one : ∀ q ∈ Q, ∀ v ∈ V₁, q * v * q⁻¹ * v⁻¹ = 1 := by
    intro q hq v hv
    rw [← Subgroup.mem_centralizer_iff.mp (hQV hq) v hv]
    group
  choose u hu using fun i : Fin 4 => hβs (Multiplicative.ofAdd (stE i))
  set a : G → Fin 4 → ZMod 2 := fun q i => ε (q * (u i : G) * q⁻¹ * (u i : G)⁻¹) with ha
  have hpw : ∀ (c : ZMod 2) (w : ↥U), ∃ w' : ↥U, β₀ w' =
      Multiplicative.ofAdd (smF4 c (Multiplicative.toAdd (β₀ w))) ∧
      ∀ q ∈ Q, ε (q * (w' : G) * q⁻¹ * (w' : G)⁻¹) = c * ε (q * (w : G) * q⁻¹ * (w : G)⁻¹) := by
    intro c w
    by_cases hc : c = 0
    · refine ⟨1, ?_, fun q _ => ?_⟩
      · rw [map_one, hc]
        rfl
      · simp [hc, hε]
    · have hc1 : c = 1 := by
        revert hc
        decide +revert
      refine ⟨w, ?_, fun q _ => by rw [hc1, one_mul]⟩
      simp [smF4, hc]
  have hkey : ∀ q ∈ Q, ∀ w : ↥U,
      stB (stDual (a q)) (Multiplicative.toAdd (β₀ w)) = ε (q * (w : G) * q⁻¹ * (w : G)⁻¹) := by
    intro q hq w
    set v := Multiplicative.toAdd (β₀ w) with hv
    obtain ⟨w0, hw0, hε0'⟩ := hpw (stCoord v 0) (u 0)
    obtain ⟨w1, hw1, hε1'⟩ := hpw (stCoord v 1) (u 1)
    obtain ⟨w2, hw2, hε2'⟩ := hpw (stCoord v 2) (u 2)
    obtain ⟨w3, hw3, hε3'⟩ := hpw (stCoord v 3) (u 3)
    set w' := w0 * w1 * w2 * w3 with hw'
    have hβw' : β₀ w' = β₀ w := by
      rw [hw', map_mul, map_mul, map_mul, hw0, hw1, hw2, hw3, hu, hu, hu, hu]
      apply Multiplicative.toAdd.injective
      simp only [toAdd_mul, toAdd_ofAdd]
      exact (eq_sum_stE v).symm
    have hww : ((w⁻¹ * w' : ↥U) : G) ∈ V₁ := by
      have h1 : w⁻¹ * w' ∈ β₀.ker := by
        rw [MonoidHom.mem_ker, map_mul, map_inv, hβw', inv_mul_cancel]
      rw [hβk, Subgroup.mem_subgroupOf] at h1
      exact h1
    have e1 : ε (q * (w : G) * q⁻¹ * (w : G)⁻¹) = ε (q * (w' : G) * q⁻¹ * (w' : G)⁻¹) := by
      have h1 := hcomm_right q hq w w.2 (w⁻¹ * w' : ↥U) (w⁻¹ * w').2
      rw [hcomm_one q hq _ hww, mul_one] at h1
      have e : (w : G) * ((w⁻¹ * w' : ↥U) : G) = w' := by simp
      rw [e] at h1
      rw [h1]
    have e2 : ε (q * (w' : G) * q⁻¹ * (w' : G)⁻¹) =
        ε (q * (w0 : G) * q⁻¹ * (w0 : G)⁻¹) + ε (q * (w1 : G) * q⁻¹ * (w1 : G)⁻¹) +
          ε (q * (w2 : G) * q⁻¹ * (w2 : G)⁻¹) + ε (q * (w3 : G) * q⁻¹ * (w3 : G)⁻¹) := by
      have hcm : ∀ x y : ↥U, ε (q * ((x * y : ↥U) : G) * q⁻¹ * ((x * y : ↥U) : G)⁻¹) =
          ε (q * (x : G) * q⁻¹ * (x : G)⁻¹) + ε (q * (y : G) * q⁻¹ * (y : G)⁻¹) := by
        intro x y
        rw [Subgroup.coe_mul, hcomm_right q hq x x.2 y y.2]
        exact hεmul (hQU q hq x x.2) (hQU q hq y y.2)
      rw [hw', hcm, hcm, hcm]
    rw [e1, e2, hε0' q hq, hε1' q hq, hε2' q hq, hε3' q hq]
    conv_lhs => rw [eq_sum_stE v]
    rw [stB_add_right, stB_add_right, stB_add_right, stB_smF4, stB_smF4, stB_smF4, stB_smF4,
      stB_stDual, stB_stDual, stB_stDual, stB_stDual]
  have hamul : ∀ q ∈ Q, ∀ q' ∈ Q, a (q * q') = a q + a q' := by
    intro q hq q' hq'
    funext i
    simp only [ha, Pi.add_apply]
    rw [hcomm_left q hq q' hq' (u i) (u i).2]
    exact hεmul (hQU q hq _ (u i).2) (hQU q' hq' _ (u i).2)
  let β : ↥Q →* Multiplicative (Fin 2 → F4) :=
    { toFun := fun q => Multiplicative.ofAdd (stDual (a q))
      map_one' := by
        show Multiplicative.ofAdd (stDual (a ((1 : ↥Q) : G))) = 1
        have h0 : a ((1 : ↥Q) : G) = 0 := by
          funext i
          simp [ha, hε]
        rw [h0]
        apply Multiplicative.toAdd.injective
        rw [toAdd_ofAdd, toAdd_one]
        decide
      map_mul' := fun q q' => by
        simp only [Subgroup.coe_mul]
        rw [hamul q q.2 q' q'.2, stDual_add]
        rfl }
  have hβapp : ∀ q : ↥Q, β q = Multiplicative.ofAdd (stDual (a q)) := fun _ => rfl
  have hβker : β.ker = (Q ⊓ Subgroup.centralizer (U : Set G)).subgroupOf Q := by
    ext q
    rw [MonoidHom.mem_ker, hβapp, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    constructor
    · intro h0
      have h1 : stDual (a q) = 0 := by
        have := congrArg Multiplicative.toAdd h0
        rwa [toAdd_ofAdd, toAdd_one] at this
      refine ⟨q.2, Subgroup.mem_centralizer_iff.mpr fun w hw => ?_⟩
      have h2 := hkey q q.2 ⟨w, hw⟩
      rw [h1] at h2
      have h3 : stB 0 (Multiplicative.toAdd (β₀ ⟨w, hw⟩)) = 0 := by
        generalize Multiplicative.toAdd (β₀ ⟨w, hw⟩) = v
        revert v
        decide
      rw [h3] at h2
      have h4 := hε0 (hQU q q.2 w hw) h2.symm
      calc w * q = (q * w * (q : G)⁻¹ * w⁻¹)⁻¹ * (q * w) := by group
        _ = (q : G) * w := by rw [h4]; group
    · rintro ⟨-, hqC⟩
      have h1 : a q = 0 := by
        funext i
        simp only [ha, Pi.zero_apply]
        rw [show (q : G) * (u i : G) * (q : G)⁻¹ * (u i : G)⁻¹ = 1 by
          rw [← Subgroup.mem_centralizer_iff.mp hqC _ (u i).2]
          group]
        simp [hε]
      rw [h1]
      apply Multiplicative.toAdd.injective
      rw [toAdd_ofAdd, toAdd_one]
      decide
  have hβs' : Function.Surjective β := by
    rw [← MonoidHom.range_eq_top]
    have h1 := Subgroup.index_ker β
    rw [hβker] at h1
    have h2 : Nat.card (Multiplicative (Fin 2 → F4)) = 16 := by
      rw [Nat.card_eq_fintype_card]
      rfl
    exact Subgroup.eq_top_of_card_eq _ (by rw [← h1, h2]; exact hrel)
  refine ⟨hKQ, π, β, hπs, hπk, hβs', hβker, fun k q q' hq' => ?_⟩
  rw [hβapp, hβapp]
  congr 1
  apply stB_ext
  intro i
  rw [stB_mulVec, stB_stDual]
  have hku : (k : G)⁻¹ * (u i : G) * k ∈ U := by
    have := (Subgroup.mem_normalizer_iff.mp (hKU (inv_mem k.2)) (u i)).mp (u i).2
    rwa [inv_inv] at this
  have hβk' := hβe k⁻¹ (u i) ⟨_, hku⟩ (by simp)
  rw [hu, toAdd_ofAdd, map_inv] at hβk'
  rw [toAdd_ofAdd]
  rw [show (((π k)⁻¹ : SL(2, F4)) : Matrix (Fin 2) (Fin 2) F4).mulVec (stE i) =
    Multiplicative.toAdd (β₀ ⟨_, hku⟩) by rw [hβk', toAdd_ofAdd]]
  rw [hkey q q.2 ⟨_, hku⟩]
  simp only [ha]
  congr 1
  have hc := hQU _ q'.2 _ (u i).2
  have hkc := Subgroup.mem_centralizer_iff.mp (hKV k.2) _ hc
  rw [hq'] at hkc ⊢
  symm
  calc (q : G) * ((k : G)⁻¹ * (u i : G) * k) * (q : G)⁻¹ * ((k : G)⁻¹ * (u i : G) * k)⁻¹ =
      (k : G)⁻¹ * (((k : G) * q * (k : G)⁻¹) * (u i : G) * ((k : G) * q * (k : G)⁻¹)⁻¹ *
        (u i : G)⁻¹ * k) := by group
    _ = ((k : G) * q * (k : G)⁻¹) * (u i : G) * ((k : G) * q * (k : G)⁻¹)⁻¹ * (u i : G)⁻¹ := by
        rw [hkc]
        group

end CFSG.Quasithin.H13.L32A
