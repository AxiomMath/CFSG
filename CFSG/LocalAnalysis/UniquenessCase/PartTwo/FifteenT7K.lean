module

public import CFSG.Quasithin.EmptyFaithfulMultiple.Lemma15412Module
public import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs
public import CFSG.Quasithin.Background.E3Defs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

section Z3

variable {W : Type} [CommGroup W] [Finite W]

theorem s15_T7_transv_struct (hW : ∀ w : W, w ^ 2 = 1) {Hy : Subgroup W}
    (hHy : E3.mQuot ⊤ Hy ≤ 1) {q : MulAut W} (hq : ∀ h ∈ Hy, q h = h) (hq1 : q ≠ 1) :
    ∃ c : W, c ∈ Hy ∧ c ≠ 1 ∧ (∀ w : W, q w = w ↔ w ∈ Hy) ∧
      ∀ w : W, w ∉ Hy → q w = w * c := by
  have hW2 : IsPGroup 2 W := isPGroup_two_of_sq_eq_one hW
  have hU2 : IsPGroup 2 (⊤ : Subgroup W) := hW2.to_subgroup ⊤
  obtain ⟨w₀, hw₀⟩ : ∃ w, q w ≠ w := by
    by_contra hcon
    push Not at hcon
    exact hq1 (MulEquiv.ext hcon)
  have hw₀Hy : w₀ ∉ Hy := fun h => hw₀ (hq w₀ h)
  have hmq : E3.mQuot ⊤ Hy = 1 := by
    have h0 : E3.mQuot ⊤ Hy ≠ 0 := fun h => hw₀Hy (by
      have := (E3.mQuot_eq_zero_iff hU2 le_top).1 h
      rw [this]
      exact Subgroup.mem_top w₀)
    omega
  have hidx : Hy.index = 2 := by
    have := E3.relIndex_eq_two_pow hU2 Hy
    rw [hmq, Subgroup.relIndex_top_right] at this
    simpa using this
  have hqw₀ : q w₀ ∉ Hy := fun h => hw₀ (q.injective (hq _ h))
  have hw₀inv : w₀⁻¹ ∉ Hy := fun h => hw₀Hy (inv_mem_iff.1 h)
  have hcHy : q w₀ * w₀⁻¹ ∈ Hy :=
    (Subgroup.mul_mem_iff_of_index_two hidx).2 (iff_of_false hqw₀ hw₀inv)
  have hc1 : q w₀ * w₀⁻¹ ≠ 1 := fun h => hw₀ (mul_inv_eq_one.1 h)
  have hact : ∀ w : W, w ∉ Hy → q w = w * (q w₀ * w₀⁻¹) := by
    intro w hw
    have h1 : w * w₀⁻¹ ∈ Hy :=
      (Subgroup.mul_mem_iff_of_index_two hidx).2 (iff_of_false hw hw₀inv)
    have h2 := hq _ h1
    rw [map_mul, map_inv] at h2
    have h3 : q w = w * w₀⁻¹ * q w₀ := by
      rw [← h2]
      simp
    rw [h3, mul_assoc, mul_comm w₀⁻¹]
  refine ⟨q w₀ * w₀⁻¹, hcHy, hc1, fun w => ⟨fun hw => ?_, hq w⟩, hact⟩
  by_contra hn
  have h4 := hact w hn
  rw [hw] at h4
  exact hc1 (by simpa using h4.symm)

theorem s15_T7_fixV_eq_bot (hW : ∀ w : W, w ^ 2 = 1) {E : Subgroup (MulAut W)}
    (hE : IsElemAbelian 3 E) (hc : commSub (⊤ : Subgroup W) E = ⊤) : fixV E = ⊥ := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hodd : Odd (Nat.card E) := by
    obtain ⟨n, hn⟩ := hE.isPGroup.exists_card_eq
    rw [hn]
    exact Odd.pow (by decide)
  have := CFSG.Quasithin.EmptyFaithfulMultiple.L15412.fixV_inf_commSub_eq_bot hW hodd
  rwa [hc, inf_top_eq] at this

theorem s15_T7_commSub_stable {X : Subgroup (MulAut W)} {g : MulAut W}
    (hg : ∀ θ ∈ X, g * θ * g⁻¹ ∈ X) {r : W} (hr : r ∈ commSub (⊤ : Subgroup W) X) :
    g r ∈ commSub (⊤ : Subgroup W) X := by
  induction hr using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨θ, hθ, w, -, rfl⟩ := hx
    refine Subgroup.subset_closure ⟨g * θ * g⁻¹, hg θ hθ, g w, Subgroup.mem_top _, ?_⟩
    simp [MulAut.mul_apply]
  | one => simp
  | mul x y _ _ hx hy =>
    rw [map_mul]
    exact mul_mem hx hy
  | inv x _ hx =>
    rw [map_inv]
    exact inv_mem hx

theorem s15_T7_not_centralize (hW : ∀ w : W, w ^ 2 = 1) {E : Subgroup (MulAut W)}
    (hE : IsElemAbelian 3 E) (hc : commSub (⊤ : Subgroup W) E = ⊤) {Hy : Subgroup W}
    (hHy : E3.mQuot ⊤ Hy ≤ 1) {q : MulAut W} (hq : ∀ h ∈ Hy, q h = h) (hq1 : q ≠ 1) :
    ∃ e ∈ E, q * e * q⁻¹ ≠ e := by
  by_contra hcon
  push Not at hcon
  obtain ⟨c, hcHy, hc1, hfix, hact⟩ := s15_T7_transv_struct hW hHy hq hq1
  obtain ⟨w₀, hw₀⟩ : ∃ w, w ∉ Hy := by
    by_contra hall
    push Not at hall
    exact hq1 (MulEquiv.ext fun w => hq w (hall w))
  have hqw₀ : q w₀ = w₀ * c := hact w₀ hw₀
  have hcE : c ∈ fixV E := by
    intro e he
    have hcomm : ∀ w, q (e w) = e (q w) := fun w => by
      have h1 : q * e = e * q := mul_inv_eq_iff_eq_mul.1 (hcon e he)
      exact congrArg (fun f : MulAut W => f w) h1
    by_cases hew : e w₀ ∈ Hy
    · exfalso
      have h1 : e (q w₀) = e w₀ := by rw [← hcomm, hq _ hew]
      rw [hqw₀, map_mul] at h1
      exact hc1 (e.injective (by simpa using h1))
    · have h1 := hact _ hew
      rw [hcomm, hqw₀, map_mul] at h1
      exact mul_left_cancel h1
  rw [s15_T7_fixV_eq_bot hW hE hc] at hcE
  exact hc1 hcE

theorem s15_T7_commSub_zpowers_stable {e g : MulAut W} (hg : g * e * g⁻¹ ∈ Subgroup.zpowers e)
    {r : W} (hr : r ∈ commSub (⊤ : Subgroup W) (Subgroup.zpowers e)) :
    g r ∈ commSub (⊤ : Subgroup W) (Subgroup.zpowers e) := by
  refine s15_T7_commSub_stable (fun θ hθ => ?_) hr
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hθ
  rw [← conj_zpow]
  exact Subgroup.zpow_mem _ hg k

theorem s15_T7_no_mixed (hW : ∀ w : W, w ^ 2 = 1) {Hy : Subgroup W}
    (hHy : E3.mQuot ⊤ Hy ≤ 1) {a b : MulAut W} (ha : ∀ h ∈ Hy, a h = h) (ha1 : a ≠ 1)
    (hb : ∀ h ∈ Hy, b h = h) {e : MulAut W} (he1 : e ≠ 1) (he3 : e ^ 3 = 1)
    (hae : a * e * a⁻¹ = e) (hbe : b * e * b⁻¹ = e⁻¹) : False := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨c, hcHy, hc1, hfixa, hacts⟩ := s15_T7_transv_struct hW hHy ha ha1
  have hord : orderOf e = 3 := orderOf_eq_prime he3 he1
  have hodd : Odd (Nat.card (Subgroup.zpowers e)) := by
    rw [Nat.card_zpowers, hord]
    decide
  have hcop := CFSG.Quasithin.EmptyFaithfulMultiple.L15412.fixV_inf_commSub_eq_bot hW hodd
  have hR0 : ∀ r ∈ commSub (⊤ : Subgroup W) (Subgroup.zpowers e), e r = r → r = 1 := by
    intro r hr hre
    have : r ∈ fixV (Subgroup.zpowers e) ⊓ commSub (⊤ : Subgroup W) (Subgroup.zpowers e) :=
      ⟨mem_fixV_zpowers_iff_apply.2 hre, hr⟩
    rw [hcop] at this
    exact this
  have hRe : ∀ r ∈ commSub (⊤ : Subgroup W) (Subgroup.zpowers e),
      e r ∈ commSub (⊤ : Subgroup W) (Subgroup.zpowers e) := fun r hr =>
    s15_T7_commSub_zpowers_stable (by simpa using Subgroup.mem_zpowers e) hr
  have hRa : ∀ r ∈ commSub (⊤ : Subgroup W) (Subgroup.zpowers e),
      a r ∈ commSub (⊤ : Subgroup W) (Subgroup.zpowers e) := fun r hr =>
    s15_T7_commSub_zpowers_stable (by rw [hae]; exact Subgroup.mem_zpowers e) hr
  have hcomm : ∀ w, e (a w) = a (e w) := fun w => by
    have h1 : a * e = e * a := mul_inv_eq_iff_eq_mul.1 hae
    exact (congrArg (fun f : MulAut W => f w) h1).symm
  have hRa_fix : ∀ r ∈ commSub (⊤ : Subgroup W) (Subgroup.zpowers e), a r = r := by
    intro r hr
    by_contra hne
    have hr_not : r ∉ Hy := fun h => hne (ha r h)
    have h1 : a r = r * c := hacts r hr_not
    have hcR : c ∈ commSub (⊤ : Subgroup W) (Subgroup.zpowers e) := by
      have : c = a r * r⁻¹ := by
        rw [h1]
        simp
      rw [this]
      exact mul_mem (hRa r hr) (inv_mem hr)
    have hec : e c = c := by
      by_cases h : e r ∈ Hy
      · exfalso
        apply hne
        have h2 : e (a r) = e r := by rw [hcomm, ha _ h]
        exact e.injective h2
      · have h2 := hacts _ h
        rw [← hcomm, h1, map_mul] at h2
        exact mul_left_cancel h2
    exact hc1 (hR0 c hcR hec)
  have hRfix : ∀ r ∈ commSub (⊤ : Subgroup W) (Subgroup.zpowers e), e r = r := by
    intro r hr
    have hrHy : r ∈ Hy := (hfixa r).1 (hRa_fix r hr)
    have her : e r ∈ commSub (⊤ : Subgroup W) (Subgroup.zpowers e) := hRe r hr
    have herHy : e r ∈ Hy := (hfixa _).1 (hRa_fix _ her)
    have h1 : b (e r) = e⁻¹ (b r) := by
      have : b * e = e⁻¹ * b := by
        rw [← hbe]
        group
      exact congrArg (fun f : MulAut W => f r) this
    rw [hb _ herHy, hb _ hrHy] at h1
    have h2 : e (e r) = r := by
      have := congrArg e h1
      simpa using this
    have h3 : e (e (e r)) = r := by
      have : e * (e * e) = 1 := by simpa [pow_succ, mul_assoc] using he3
      exact congrArg (fun f : MulAut W => f r) this
    rw [h2] at h3
    exact h3
  apply he1
  refine MulEquiv.ext fun w => ?_
  have hgen : e w * w⁻¹ ∈ commSub (⊤ : Subgroup W) (Subgroup.zpowers e) :=
    Subgroup.subset_closure ⟨e, Subgroup.mem_zpowers e, w, Subgroup.mem_top w, rfl⟩
  have h1 := hR0 _ hgen (hRfix _ hgen)
  exact mul_inv_eq_one.1 h1

theorem s15_T7_transv_sq (hW : ∀ w : W, w ^ 2 = 1) {Hy : Subgroup W}
    (hHy : E3.mQuot ⊤ Hy ≤ 1) {q : MulAut W} (hq : ∀ h ∈ Hy, q h = h) : q * q = 1 := by
  by_cases hq1 : q = 1
  · simp [hq1]
  obtain ⟨c, hcHy, hc1, hfix, hact⟩ := s15_T7_transv_struct hW hHy hq hq1
  refine MulEquiv.ext fun w => ?_
  by_cases hw : w ∈ Hy
  · simp [MulAut.mul_apply, hq w hw]
  · show q (q w) = w
    rw [hact w hw, map_mul, hq c hcHy, hact w hw, mul_assoc, ← sq, hW c, mul_one]

theorem s15_T7_transv_comm (hW : ∀ w : W, w ^ 2 = 1) {Hy : Subgroup W}
    (hHy : E3.mQuot ⊤ Hy ≤ 1) {q q' : MulAut W} (hq : ∀ h ∈ Hy, q h = h)
    (hq' : ∀ h ∈ Hy, q' h = h) : q * q' = q' * q := by
  by_cases hq1 : q = 1
  · simp [hq1]
  by_cases hq1' : q' = 1
  · simp [hq1']
  obtain ⟨c, hcHy, hc1, hfix, hact⟩ := s15_T7_transv_struct hW hHy hq hq1
  obtain ⟨c', hc'Hy, hc1', hfix', hact'⟩ := s15_T7_transv_struct hW hHy hq' hq1'
  refine MulEquiv.ext fun w => ?_
  by_cases hw : w ∈ Hy
  · simp [MulAut.mul_apply, hq w hw, hq' w hw]
  · have h1 : q (q' w) = w * c * c' := by
      rw [hact' w hw, map_mul, hq c' hc'Hy, hact w hw]
    have h2 : q' (q w) = w * c' * c := by
      rw [hact w hw, map_mul, hq' c hcHy, hact' w hw]
    show q (q' w) = q' (q w)
    rw [h1, h2, mul_right_comm]

theorem s15_T7_conj_invol_mul {A : Type*} [Group A] {q : A} (hqq : q * q = 1) (x y : A) :
    q * (x * y) * q = (q * x * q) * (q * y * q) := by
  calc q * (x * y) * q = q * x * (q * q) * y * q := by rw [hqq]; group
    _ = (q * x * q) * (q * y * q) := by group

theorem s15_T7_conj_invol_inv {A : Type*} [Group A] {q : A} (hqq : q * q = 1) (x : A) :
    q * x⁻¹ * q = (q * x * q)⁻¹ := by
  have hqi : q⁻¹ = q := inv_eq_of_mul_eq_one_right hqq
  rw [mul_inv_rev, mul_inv_rev, hqi]
  group

theorem s15_T7_conj_invol_invol {A : Type*} [Group A] {q : A} (hqq : q * q = 1) (x : A) :
    q * (q * x * q) * q = x := by
  calc q * (q * x * q) * q = (q * q) * x * (q * q) := by group
    _ = x := by rw [hqq]; group

theorem s15_T7_no_two_transvections (hW : ∀ w : W, w ^ 2 = 1) {E : Subgroup (MulAut W)}
    (hE : IsElemAbelian 3 E) (hc : commSub (⊤ : Subgroup W) E = ⊤) {Hy : Subgroup W}
    (hHy : E3.mQuot ⊤ Hy ≤ 1) {q q' : MulAut W} (hqN : q ∈ normalizer (E : Set (MulAut W)))
    (hq'N : q' ∈ normalizer (E : Set (MulAut W))) (hq : ∀ h ∈ Hy, q h = h)
    (hq' : ∀ h ∈ Hy, q' h = h) (hq1 : q ≠ 1) (hq1' : q' ≠ 1) (hne : q ≠ q') : False := by
  have hqq : q * q = 1 := s15_T7_transv_sq hW hHy hq
  have hq'q' : q' * q' = 1 := s15_T7_transv_sq hW hHy hq'
  have hcomm : q * q' = q' * q := s15_T7_transv_comm hW hHy hq hq'
  have hqi : q⁻¹ = q := inv_eq_of_mul_eq_one_right hqq
  have hq'i : q'⁻¹ = q' := inv_eq_of_mul_eq_one_right hq'q'
  have hEc : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hE.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hE3 : ∀ x ∈ E, x ^ 3 = 1 := hE.2
  have hqE : ∀ x ∈ E, q * x * q ∈ E := fun x hx => by
    have := (Subgroup.mem_normalizer_iff.1 hqN x).1 hx
    rwa [hqi] at this
  have hq'E : ∀ x ∈ E, q' * x * q' ∈ E := fun x hx => by
    have := (Subgroup.mem_normalizer_iff.1 hq'N x).1 hx
    rwa [hq'i] at this
  obtain ⟨e₀, he₀, hne₀⟩ := s15_T7_not_centralize hW hE hc hHy hq hq1
  rw [hqi] at hne₀
  obtain ⟨e₁, he₁⟩ : ∃ x : MulAut W, x = q * e₀ * q := ⟨_, rfl⟩
  have he₁E : e₁ ∈ E := he₁ ▸ hqE e₀ he₀
  have hqe₁ : q * e₁ * q = e₀ := by rw [he₁, s15_T7_conj_invol_invol hqq]
  obtain ⟨e, hedef⟩ : ∃ x : MulAut W, x = e₀ * e₁⁻¹ := ⟨_, rfl⟩
  have heE : e ∈ E := hedef ▸ mul_mem he₀ (inv_mem he₁E)
  have he1 : e ≠ 1 := fun h => hne₀ (by
    rw [hedef, mul_inv_eq_one] at h
    rw [← he₁, h])
  have heq : q * e * q = e⁻¹ := by
    rw [hedef, s15_T7_conj_invol_mul hqq, s15_T7_conj_invol_inv hqq, hqe₁, ← he₁]
    simp
  obtain ⟨f, hfdef⟩ : ∃ x : MulAut W, x = q' * e * q' := ⟨_, rfl⟩
  have hfE : f ∈ E := hfdef ▸ hq'E e heE
  have hq'f : q' * f * q' = e := by rw [hfdef, s15_T7_conj_invol_invol hq'q']
  have hqf : q * f * q = f⁻¹ := by
    rw [hfdef]
    calc q * (q' * e * q') * q = (q * q') * e * (q' * q) := by group
      _ = (q' * q) * e * (q * q') := by rw [hcomm]
      _ = q' * (q * e * q) * q' := by group
      _ = (q' * e * q')⁻¹ := by rw [heq, s15_T7_conj_invol_inv hq'q']
  have hef : e * f = f * e := hEc e heE f hfE
  have hprod : (e * f) * (e * f⁻¹) = e * e := by
    calc (e * f) * (e * f⁻¹) = e * (f * e) * f⁻¹ := by group
      _ = e * (e * f) * f⁻¹ := by rw [hef]
      _ = e * e := by group
  have hesq : e * e ≠ 1 := by
    intro h
    apply he1
    have h3 := hE3 e heE
    have : e = e ^ 3 * (e * e)⁻¹ := by group
    rw [this, h3, h]
    simp
  by_cases h' : e * f = 1
  swap
  ·
    refine s15_T7_no_mixed hW hHy (a := q') (b := q) hq' hq1' hq (e := e * f) h'
      (hE3 _ (mul_mem heE hfE)) ?_ ?_
    · rw [hq'i, s15_T7_conj_invol_mul hq'q', ← hfdef, hq'f, hef]
    · rw [hqi, s15_T7_conj_invol_mul hqq, heq, hqf, ← mul_inv_rev, ← hef]
  ·
    have h'' : e * f⁻¹ ≠ 1 := fun h => hesq (by rw [← hprod, h', h]; simp)
    have hq'2 : q' * (e * f⁻¹) * q' = (e * f⁻¹)⁻¹ := by
      rw [s15_T7_conj_invol_mul hq'q', s15_T7_conj_invol_inv hq'q', ← hfdef, hq'f]
      simp
    have hq2 : q * (e * f⁻¹) * q = (e * f⁻¹)⁻¹ := by
      rw [s15_T7_conj_invol_mul hqq, s15_T7_conj_invol_inv hqq, heq, hqf]
      simp only [inv_inv, mul_inv_rev]
      exact hEc _ (inv_mem heE) _ hfE
    refine s15_T7_no_mixed hW hHy (a := q * q') (b := q) (fun h hh => ?_) ?_ hq
      (e := e * f⁻¹) h'' (hE3 _ (mul_mem heE (inv_mem hfE))) ?_ ?_
    · rw [MulAut.mul_apply, hq' h hh, hq h hh]
    · intro h
      exact hne (by rw [← hqi, mul_eq_one_iff_eq_inv.1 h, inv_inv])
    · rw [mul_inv_rev, hqi, hq'i]
      calc q * q' * (e * f⁻¹) * (q' * q) = q * (q' * (e * f⁻¹) * q') * q := by group
        _ = q * (e * f⁻¹)⁻¹ * q := by rw [hq'2]
        _ = (q * (e * f⁻¹) * q)⁻¹ := s15_T7_conj_invol_inv hqq _
        _ = e * f⁻¹ := by rw [hq2, inv_inv]
    · rw [hqi, hq2]

theorem s15_T7_card_le_two_of_unique {A : Type*} [Group A] {Q : Subgroup A} {q₀ : A}
    (hall : ∀ q ∈ Q, q = 1 ∨ q = q₀) (hq₀ : q₀ ≠ 1) : Nat.card ↥Q ≤ 2 := by
  classical
  have hinj : Function.Injective (fun q : ↥Q => decide ((q : A) = 1)) := by
    intro x y hxy
    simp only [decide_eq_decide] at hxy
    apply Subtype.ext
    by_cases hx1 : (x : A) = 1
    · rw [hx1, hxy.1 hx1]
    · have hy1 : (y : A) ≠ 1 := fun h => hx1 (hxy.2 h)
      rcases hall x x.2 with h | h
      · exact absurd h hx1
      rcases hall y y.2 with h' | h'
      · exact absurd h' hy1
      rw [h, h']
  calc Nat.card ↥Q ≤ Nat.card Bool := Nat.card_le_card_of_injective _ hinj
    _ = 2 := by simp

theorem s15_T7_Z3_card_le_two (hW : ∀ w : W, w ^ 2 = 1) {E : Subgroup (MulAut W)}
    (hE : IsElemAbelian 3 E) (hc : commSub (⊤ : Subgroup W) E = ⊤) {Q : Subgroup (MulAut W)}
    (hQN : Q ≤ normalizer (E : Set (MulAut W))) {Hy : Subgroup W} (hHy : E3.mQuot ⊤ Hy ≤ 1)
    (hQ : ∀ q ∈ Q, ∀ h ∈ Hy, q h = h) : Nat.card ↥Q ≤ 2 := by
  by_cases hall1 : ∀ q ∈ Q, q = 1
  · have : Q = ⊥ := (Subgroup.eq_bot_iff_forall Q).2 hall1
    rw [this]
    simp
  · push Not at hall1
    obtain ⟨q₀, hq₀, hq₀1⟩ := hall1
    refine s15_T7_card_le_two_of_unique (q₀ := q₀) (fun q hq => ?_) hq₀1
    by_cases hq1 : q = 1
    · exact Or.inl hq1
    · refine Or.inr (by_contra fun hne => ?_)
      exact s15_T7_no_two_transvections hW hE hc hHy (hQN hq) (hQN hq₀) (hQ q hq) (hQ q₀ hq₀)
        hq1 hq₀1 hne

end Z3

theorem s15_T7_mQuot_top_subgroupOf {A : Type*} [Group A] (U B : Subgroup A) :
    E3.mQuot (⊤ : Subgroup ↥U) (B.subgroupOf U) = E3.mQuot U B := by
  unfold E3.mQuot
  rw [Subgroup.relIndex_top_right]
  rfl

theorem s15_T7_rk_le_one_of_card_le_two {X : Type*} [Group X] [Finite X]
    (h : Nat.card X ≤ 2) : rk X ≤ 1 := by
  have h1 : 0 < Nat.card X := Nat.card_pos
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  unfold rk
  interval_cases hX : Nat.card X
  · simp
  · simp

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
