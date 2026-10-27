module

public import CFSG.RankThree.GF2n.Smith81.OrthCountAct

public section

namespace CFSG.RankThree.GF2n.Smith81.Smith216Odd

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Stroth80
  CFSG.RankThree.GF2n.Smith81

variable {G : Type} [Group G] [Finite G] {M Q Z : Subgroup G}

theorem eq_one_of_sq_mem {P : Subgroup G} (hP : IsPGroup 2 P) {g : G} (hg : g * g ∈ P)
    (hodd : Odd (orderOf g)) : g = 1 := by
  obtain ⟨k, hk⟩ := hP ⟨g * g, hg⟩
  have h1 : g ^ (2 ^ (k + 1)) = 1 := by
    have : (g * g) ^ (2 ^ k) = 1 := by
      have := congrArg Subtype.val hk
      simpa using this
    rw [pow_succ', pow_mul, pow_two]
    exact this
  have hdvd : orderOf g ∣ 2 ^ (k + 1) := orderOf_dvd_of_pow_eq_one h1
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
  have hj0 : j = 0 := by
    rcases j with _ | j
    · rfl
    · exfalso
      rw [hj, pow_succ] at hodd
      exact (Nat.not_even_iff_odd.mpr hodd) (even_two.mul_left _)
  rw [hj0, pow_zero] at hj
  exact orderOf_eq_one_iff.mp hj

theorem commute_conj {a b : G} (c : G) (h : Commute a b) :
    Commute (c * a * c⁻¹) (c * b * c⁻¹) := by
  have := h.map (MulAut.conj c).toMonoidHom
  simpa [MulAut.conj_apply] using this

section Core

variable (H : StrothHyp M Q Z) {z : G} (hz : z ∈ Z) (hz1 : z ≠ 1)
  (h212 : ∀ x : G, x ∈ M → x ∉ Q → IsConj z x → ∀ y ∈ cosetSet x Z, IsConj z y → y = x)
  (h213 : Timmesfeld.IsRootInvolutionSet (conjClassSet z ∩ (M : Set G)))
  (hCount : ∀ A C : Subgroup G, IsZConjugate Z A → IsZConjugate Z C → A ≠ C → C ≤ QB A →
    ∃ S : Subgroup G, S ≤ QB A ⊓ QB C ∧ (∀ s ∈ S, s ≠ 1 → IsConj z s) ∧
      Nat.card Z ^ 2 < Nat.card S)
  (h28 : ∀ (X : Subgroup G) (x : G), Sit M Q Z X x → ∃ v : G, IsConj x v ∧ v ∈ Q ∧ v ∈ QB X)
include H hz hz1 h212 h213 hCount h28

theorem odd_reduce_Z {x w y : G} (hx : IsConj z x) (hw : IsConj z w) (hy : IsConj z y)
    (hxz : Commute x z) (hzw : Commute z w) (hwy : Commute w y) (hxw : ¬ Commute x w)
    (hodd : Odd (orderOf (x * w))) : ∃ v : G, IsConj z v ∧ Commute x v ∧ Commute v y := by
  have hxx := mul_self_eq_one_of_isConj_Z H hz hx
  have hww := mul_self_eq_one_of_isConj_Z H hz hw
  have hxM : x ∈ M := mem_M_of_commute_Z H hz hz1 hxz.eq
  have hwM : w ∈ M := mem_M_of_commute_Z H hz hz1 hzw.symm.eq
  have hwinv : w⁻¹ = w := inv_eq_of_mul_eq_one_right hww
  have hxQ : x ∉ Q := by
    intro hxQ
    have hsq : x * w * (x * w) ∈ Q := by
      have h1 : w * x * w⁻¹ ∈ Q := conj_mem_Q H hwM hxQ
      have e : x * w * (x * w) = x * (w * x * w⁻¹) * (w * w) := by group
      rw [e, hww, mul_one]
      exact Q.mul_mem hxQ h1
    have h1 := eq_one_of_sq_mem (isPGroup_Q' H) hsq hodd
    apply hxw
    have : w = x⁻¹ := (eq_inv_of_mul_eq_one_right h1)
    rw [this]
    exact (Commute.refl x).inv_right
  obtain ⟨X, hX, hxX⟩ := exists_isZConjugate_mem hz hx
  have hs : Sit M Q Z X x := ⟨H, hX, hxX, ne_one_of_isConj_Z hz1 hx, hxM, hxQ⟩
  obtain ⟨t, hxt, htQ, htX⟩ := h28 X x hs
  have ht : IsConj z t := hx.trans hxt
  have ht1 : t ≠ 1 := ne_one_of_isConj_Z hz1 ht
  obtain ⟨A, hA, htA⟩ := exists_isZConjugate_mem hz ht
  have hAX : A ≤ QB X := hX.le_QB_of_mem H hA ht1 htA htX
  have hXA : X ≤ QB A := (hA.le_QB_iff H hX).mpr hAX
  have hxA : x ∈ QB A := hXA hxX
  have htz : Commute t z := by
    have := (IsZConjugate.self Z).central_QB H hz (show t ∈ QB Z by rw [H.QB_Z]; exact htQ)
    exact this.symm
  have hxt' : Commute x t := hX.central_QB H hxX htX
  obtain ⟨v₁, hv₁, htv, hvy⟩ : ∃ v : G, IsConj z v ∧ Commute t v ∧ Commute v y := by
    by_cases htw : Commute t w
    · exact ⟨w, hw, htw, hwy⟩
    have hord := (local_of_global_M H hz hz1 h213 (IsConj.refl z) ht hw htz hzw.symm).1
    rcases hord with h | h | h
    · exact absurd (commute_of_orderOf_mul_eq_two (mul_self_eq_one_of_isConj_Z H hz ht) hww h) htw
    · exact path_reduce_of_four H hz hz1 h212 h213 hCount ht hw hy hwy h
    · exfalso
      have hsq : t * w * (t * w) ∈ Q := by
        have h1 : w * t * w⁻¹ ∈ Q := conj_mem_Q H hwM htQ
        have e : t * w * (t * w) = t * (w * t * w⁻¹) * (w * w) := by group
        rw [e, hww, mul_one]
        exact Q.mul_mem htQ h1
      have h1 := eq_one_of_sq_mem (isPGroup_Q' H) hsq h
      apply htw
      rw [eq_inv_of_mul_eq_one_right h1]
      exact (Commute.refl t).inv_right
  have hvv := mul_self_eq_one_of_isConj_Z H hz hv₁
  have hvinv : v₁⁻¹ = v₁ := inv_eq_of_mul_eq_one_right hvv
  by_cases hxv : Commute x v₁
  · exact ⟨v₁, hv₁, hxv, hvy⟩
  have hvN : v₁ ∈ Subgroup.normalizer (A : Set G) :=
    hA.mem_normalizer_of_commute H ht1 htA htv.symm
  have hord := (local_of_global_M H hz hz1 h213 ht hx hv₁ hxt' htv.symm).1
  rcases hord with h | h | h
  · exact absurd (commute_of_orderOf_mul_eq_two hxx hvv h) hxv
  · exact path_reduce_of_four H hz hz1 h212 h213 hCount hx hv₁ hy hvy h
  · exfalso
    have hsq : x * v₁ * (x * v₁) ∈ QB A := by
      have h1 : v₁ * x * v₁⁻¹ ∈ QB A := hA.conj_mem_QB H hvN hxA
      have e : x * v₁ * (x * v₁) = x * (v₁ * x * v₁⁻¹) * (v₁ * v₁) := by group
      rw [e, hvv, mul_one]
      exact (QB A).mul_mem hxA h1
    have h1 := eq_one_of_sq_mem (hA.isPGroup_QB H) hsq h
    apply hxv
    rw [eq_inv_of_mul_eq_one_right h1]
    exact (Commute.refl x).inv_right

theorem odd_reduce {x z' w y : G} (hx : IsConj z x) (hz' : IsConj z z') (hw : IsConj z w)
    (hy : IsConj z y) (hxz : Commute x z') (hzw : Commute z' w) (hwy : Commute w y)
    (hxw : ¬ Commute x w) (hodd : Odd (orderOf (x * w))) :
    ∃ v : G, IsConj z v ∧ Commute x v ∧ Commute v y := by
  obtain ⟨c, hc⟩ := isConj_iff.mp hz'
  have hcc : ∀ a : G, IsConj z a → IsConj z (c⁻¹ * a * c) := fun a ha =>
    ha.trans (isConj_iff.mpr ⟨c⁻¹, by group⟩)
  have hzc : c⁻¹ * z' * c = z := by rw [← hc]; group
  have key := fun (a b : G) (h : Commute a b) => by
    simpa using commute_conj c⁻¹ h
  have h1 : Commute (c⁻¹ * x * c) z := by rw [← hzc]; exact key _ _ hxz
  have h2 : Commute z (c⁻¹ * w * c) := by rw [← hzc]; exact key _ _ hzw
  have h3 := key _ _ hwy
  have h4 : ¬ Commute (c⁻¹ * x * c) (c⁻¹ * w * c) := by
    intro h
    apply hxw
    have := commute_conj c h
    simpa [mul_assoc] using this
  have h5 : Odd (orderOf (c⁻¹ * x * c * (c⁻¹ * w * c))) := by
    have e : c⁻¹ * x * c * (c⁻¹ * w * c) = c⁻¹ * (x * w) * c⁻¹⁻¹ := by group
    rw [e, CFSG.Timmesfeld.CorB.orderOf_conj]
    exact hodd
  obtain ⟨v, hv, hxv, hvy⟩ := odd_reduce_Z H hz hz1 h212 h213 hCount h28 (hcc x hx) (hcc w hw)
    (hcc y hy) h1 h2 (by simpa [mul_assoc] using h3) h4 h5
  refine ⟨c * v * c⁻¹, hv.trans (isConj_iff.mpr ⟨c, rfl⟩), ?_, ?_⟩
  · have := commute_conj c hxv
    simpa [mul_assoc] using this
  · have := commute_conj c hvy
    simpa [mul_assoc] using this

end Core

theorem smith216OrthOdd_of_28 (h28 : Smith28OrthStatement) (h212 : Smith212OrthCoreStatement)
    (h213 : Smith213OrthStatement) (hCount : Smith216OrthCountStatement) :
    Smith216OrthOddStatement := by
  intro G _ _ M Q Z B hc z hz hz1 x z' w y hx hz' hw hy hxz hzw hwy hxw _ ho1 _
  have H := hc.ctx.hyp
  refine odd_reduce H hz hz1 ?_ (h213 G M Q Z B hc z hz hz1) ?_
    (fun X x' hs => h28 G M Q Z B hc X x' hs)
    hx hz' hw hy hxz hzw hwy hxw ho1
  · intro x' hxM hxQ hxc y' hy'cos hy'c
    have h1 := (h212 G M Q Z B hc z hz hz1 x' hxM hxQ hxc).1
    have hmem : y' ∈ conjClassSet z ∩ cosetSet x' Z := ⟨hy'c, hy'cos⟩
    rw [h1] at hmem
    exact hmem
  · exact fun A C hA hC hAC hCA => hCount G M Q Z B hc z hz hz1 A C hA hC hAC hCA

theorem smith216Orth_of_28 (h28 : Smith28OrthStatement) (h212 : Smith212OrthCoreStatement)
    (h213 : Smith213OrthStatement) (hCount : Smith216OrthCountStatement) :
    Smith216OrthStatement :=
  smith216Orth_of_statements h212 h213 hCount (smith216OrthOdd_of_28 h28 h212 h213 hCount)

theorem smith_2_16_of_28 (H : StrothHyp M Q Z) {z : G} (hz : z ∈ Z) (hz1 : z ≠ 1)
    (h212 : ∀ x : G, x ∈ M → x ∉ Q → IsConj z x → ∀ y ∈ cosetSet x Z, IsConj z y → y = x)
    (h213 : Timmesfeld.IsRootInvolutionSet (conjClassSet z ∩ (M : Set G)))
    (hCount : ∀ A C : Subgroup G, IsZConjugate Z A → IsZConjugate Z C → A ≠ C → C ≤ QB A →
      ∃ S : Subgroup G, S ≤ QB A ⊓ QB C ∧ (∀ s ∈ S, s ≠ 1 → IsConj z s) ∧
        Nat.card Z ^ 2 < Nat.card S)
    (h28 : ∀ (X : Subgroup G) (x : G), Sit M Q Z X x → ∃ v : G, IsConj x v ∧ v ∈ Q ∧ v ∈ QB X)
    {x z' w y : G} (hx : IsConj z x) (hz' : IsConj z z') (hw : IsConj z w) (hy : IsConj z y)
    (hxz : Commute x z') (hzw : Commute z' w) (hwy : Commute w y) :
    ∃ v : G, IsConj z v ∧ Commute x v ∧ Commute v y :=
  smith_2_16 H hz hz1 h212 h213 hCount
    (fun _ _ _ _ hx hz' hw hy hxz hzw hwy hxw _ ho1 _ =>
      odd_reduce H hz hz1 h212 h213 hCount h28 hx hz' hw hy hxz hzw hwy hxw ho1)
    hx hz' hw hy hxz hzw hwy

theorem smithLaneOrth_of_28 (hT : TimmesfeldOutcomeStatement) (h28 : Smith28OrthStatement)
    (h212 : Smith212OrthCoreStatement) (h213 : Smith213OrthStatement)
    (h24 : Smith24ActStatement) (h52 : Smith52ActStatement) (h217 : Smith217Statement)
    (hInsp : Smith219OrthInspectionStatement) : LaneOrthStep :=
  smithLaneOrth_of_section5Act hT h212 h213 h24 h52
    (smith216OrthOdd_of_28 h28 h212 h213 (smith216OrthCount_of_52Act h24 h52)) h217 hInsp

end CFSG.RankThree.GF2n.Smith81.Smith216Odd
