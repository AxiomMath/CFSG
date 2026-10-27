module

public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC6

open Subgroup

section CharTwo

theorem add_self_eq_zero_uc6 {V : Type} [AddCommGroup V] [Module (ZMod 2) V] (v : V) : v + v = 0 := by
  have h : v + v = (1 + 1 : ZMod 2) • v := by rw [add_smul, one_smul]
  have h2 : (1 + 1 : ZMod 2) = 0 := by decide
  rw [h, h2, zero_smul]

theorem odd_nsmul_eq_uc6 {A : Type*} [AddCommGroup A] (h : ∀ a : A, a + a = 0) {n : ℕ}
    (hn : Odd n) (a : A) : n • a = a := by
  obtain ⟨m, rfl⟩ := hn
  induction m with
  | zero => simp
  | succ m ih =>
    have e : 2 * (m + 1) + 1 = (2 * m + 1) + 2 := by ring
    rw [e, add_nsmul, ih, two_nsmul, h a, add_zero]

theorem end_add_self_eq_zero_uc6 {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
    (a : Module.End (ZMod 2) V) : a + a = 0 :=
  LinearMap.ext fun v => by simp [add_self_eq_zero_uc6]

theorem odd_nsmul_end_uc6 {V : Type} [AddCommGroup V] [Module (ZMod 2) V] {n : ℕ} (hn : Odd n)
    (a : Module.End (ZMod 2) V) : n • a = a :=
  odd_nsmul_eq_uc6 end_add_self_eq_zero_uc6 hn a

theorem odd_nsmul_vec_uc6 {V : Type} [AddCommGroup V] [Module (ZMod 2) V] {n : ℕ} (hn : Odd n)
    (v : V) : n • v = v :=
  odd_nsmul_eq_uc6 add_self_eq_zero_uc6 hn v

end CharTwo

section Norm

variable {E : Type} [Group E] {V : Type} [AddCommGroup V] [Module (ZMod 2) V]

@[expose] noncomputable def nrmOp (σ : E →* Module.End (ZMod 2) V) (K : Subgroup E) :
    Module.End (ZMod 2) V :=
  ∑ᶠ s : ↥K, σ (s : E)

theorem nrmOp_eq_sum_uc6 (σ : E →* Module.End (ZMod 2) V) (K : Subgroup E) [Fintype ↥K] :
    nrmOp σ K = ∑ s : ↥K, σ (s : E) :=
  finsum_eq_sum_of_fintype _

@[expose] noncomputable def nrmAll (σ : E →* Module.End (ZMod 2) V) : Module.End (ZMod 2) V :=
  ∑ᶠ e : E, σ e

theorem nrmAll_eq_sum_uc6 (σ : E →* Module.End (ZMod 2) V) [Fintype E] :
    nrmAll σ = ∑ e : E, σ e :=
  finsum_eq_sum_of_fintype _

variable [Finite E]

theorem σ_mul_nrmOp_uc6 (σ : E →* Module.End (ZMod 2) V) (K : Subgroup E) {g : E} (hg : g ∈ K) :
    σ g * nrmOp σ K = nrmOp σ K := by
  haveI : Fintype ↥K := Fintype.ofFinite _
  rw [nrmOp_eq_sum_uc6, Finset.mul_sum]
  let g' : ↥K := ⟨g, hg⟩
  have := Fintype.sum_equiv (Equiv.mulLeft g') (fun s : ↥K => σ (g' * s : ↥K)) (fun s : ↥K => σ s)
    (fun s => rfl)
  rw [← this]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [← map_mul]
  rfl

theorem nrmOp_mul_σ_uc6 (σ : E →* Module.End (ZMod 2) V) (K : Subgroup E) {g : E} (hg : g ∈ K) :
    nrmOp σ K * σ g = nrmOp σ K := by
  haveI : Fintype ↥K := Fintype.ofFinite _
  rw [nrmOp_eq_sum_uc6, Finset.sum_mul]
  let g' : ↥K := ⟨g, hg⟩
  have := Fintype.sum_equiv (Equiv.mulRight g') (fun s : ↥K => σ (s * g' : ↥K)) (fun s : ↥K => σ s)
    (fun s => rfl)
  rw [← this]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [← map_mul]
  rfl

theorem nrmOp_mul_nrmOp_uc6 (σ : E →* Module.End (ZMod 2) V) (K : Subgroup E)
    (hK : Odd (Nat.card K)) : nrmOp σ K * nrmOp σ K = nrmOp σ K := by
  haveI : Fintype ↥K := Fintype.ofFinite _
  have h1 : nrmOp σ K * nrmOp σ K = nrmOp σ K * ∑ s : ↥K, σ (s : E) := by
    rw [← nrmOp_eq_sum_uc6 σ K]
  rw [h1, Finset.mul_sum]
  have h : ∀ s : ↥K, nrmOp σ K * σ (s : E) = nrmOp σ K := fun s => nrmOp_mul_σ_uc6 σ K s.2
  simp only [h, Finset.sum_const, Finset.card_univ]
  rw [← Nat.card_eq_fintype_card]
  exact odd_nsmul_end_uc6 hK _

theorem nrmOp_fixed_uc6 (σ : E →* Module.End (ZMod 2) V) (K : Subgroup E) (hK : Odd (Nat.card K))
    {v : V} (hv : ∀ s ∈ K, σ s v = v) : nrmOp σ K v = v := by
  haveI : Fintype ↥K := Fintype.ofFinite _
  rw [nrmOp_eq_sum_uc6]
  have h : ∀ s : ↥K, σ (s : E) v = v := fun s => hv s s.2
  simp only [LinearMap.sum_apply, h, Finset.sum_const, Finset.card_univ]
  rw [← Nat.card_eq_fintype_card]
  exact odd_nsmul_vec_uc6 hK v

end Norm

section PowAction

variable {E : Type} [Group E] {V : Type} [AddCommGroup V] [Module (ZMod 2) V]

theorem pow_mul_σ_uc6 (σ : E →* Module.End (ZMod 2) V) (T : Module.End (ZMod 2) V) (α : MulAut E)
    (hTα : ∀ e, T * σ e = σ (α e) * T) (i : ℕ) (e : E) :
    T ^ i * σ e = σ ((α ^ i) e) * T ^ i := by
  induction i generalizing e with
  | zero => simp
  | succ i ih =>
    have e1 : (α ^ (i + 1)) e = α ((α ^ i) e) := by rw [pow_succ']; rfl
    calc T ^ (i + 1) * σ e = T * (T ^ i * σ e) := by rw [pow_succ', mul_assoc]
      _ = T * (σ ((α ^ i) e) * T ^ i) := by rw [ih]
      _ = (T * σ ((α ^ i) e)) * T ^ i := by rw [mul_assoc]
      _ = (σ (α ((α ^ i) e)) * T) * T ^ i := by rw [hTα]
      _ = σ (α ((α ^ i) e)) * T ^ (i + 1) := by rw [mul_assoc, pow_succ']
      _ = σ ((α ^ (i + 1)) e) * T ^ (i + 1) := by rw [e1]

end PowAction

section Frobenius

variable {E : Type} [CommGroup E] [Finite E] {V : Type} [AddCommGroup V] [Module (ZMod 2) V]

theorem bijective_div_uc6 (β : MulAut E) (hβ : ∀ y, β y = y → y = 1) :
    Function.Bijective (fun y : E => y * (β y)⁻¹) := by
  rw [← Finite.injective_iff_bijective]
  intro y z h
  have h1 : y / β y = z / β z := by simpa [div_eq_mul_inv] using h
  have h2 : y / z = β y / β z := div_eq_div_iff_div_eq_div.1 h1
  have h3 : β (y / z) = y / z := by rw [map_div]; exact h2.symm
  exact div_eq_one.1 (hβ _ h3)

end Frobenius

section Frobenius2

variable {E : Type} [CommGroup E] [Fintype E] {V : Type} [AddCommGroup V] [Module (ZMod 2) V]

theorem frobenius_identity_uc6 (σ : E →* Module.End (ZMod 2) V) (hE : Odd (Nat.card E))
    (T : Module.End (ZMod 2) V) (α : MulAut E) (r : ℕ) (hr : 0 < r)
    (hTα : ∀ e, T * σ e = σ (α e) * T)
    (hfix : ∀ i, 0 < i → i < r → ∀ y, (α ^ i) y = y → y = 1) :
    ∑ y : E, σ y * (∑ i ∈ Finset.range r, T ^ i) * σ y⁻¹ =
      1 + nrmAll σ * (∑ i ∈ Finset.range r, T ^ i - 1) := by
  have hA : ∀ y : E, σ y * (∑ i ∈ Finset.range r, T ^ i) * σ y⁻¹ =
      ∑ i ∈ Finset.range r, σ (y * ((α ^ i) y)⁻¹) * T ^ i := by
    intro y
    rw [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    calc σ y * T ^ i * σ y⁻¹ = σ y * (T ^ i * σ y⁻¹) := by rw [mul_assoc]
      _ = σ y * (σ ((α ^ i) y⁻¹) * T ^ i) := by rw [pow_mul_σ_uc6 σ T α hTα i y⁻¹]
      _ = σ (y * ((α ^ i) y)⁻¹) * T ^ i := by
        rw [map_inv (α ^ i) y, ← mul_assoc, ← map_mul]
  have hsum : ∑ y : E, σ y * (∑ i ∈ Finset.range r, T ^ i) * σ y⁻¹ =
      ∑ i ∈ Finset.range r, ∑ y : E, σ (y * ((α ^ i) y)⁻¹) * T ^ i := by
    rw [Finset.sum_congr rfl (fun y _ => hA y), Finset.sum_comm]
  have hB : ∀ i ∈ Finset.range r, ∑ y : E, σ (y * ((α ^ i) y)⁻¹) * T ^ i =
      if i = 0 then (1 : Module.End (ZMod 2) V) else nrmAll σ * T ^ i := by
    intro i hi
    rw [← Finset.sum_mul]
    split_ifs with h0
    · subst h0
      simp only [pow_zero, MulAut.one_apply, mul_inv_cancel, map_one, mul_one, Finset.sum_const,
        Finset.card_univ]
      rw [← Nat.card_eq_fintype_card]
      exact odd_nsmul_end_uc6 hE _
    · have hbij := bijective_div_uc6 (α ^ i) (hfix i (Nat.pos_of_ne_zero h0) (Finset.mem_range.1 hi))
      rw [Function.Bijective.sum_comp hbij (fun u => σ u), nrmAll_eq_sum_uc6]
  rw [hsum, Finset.sum_congr rfl hB]
  obtain ⟨r', rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
  rw [Finset.sum_range_succ' (fun i => if i = 0 then (1 : Module.End (ZMod 2) V)
      else nrmAll σ * T ^ i), Finset.sum_range_succ' (fun i => T ^ i)]
  simp only [Nat.succ_ne_zero, if_false, if_true, pow_zero, add_sub_cancel_right]
  rw [Finset.mul_sum, add_comm]

theorem T_mul_sum_uc6 (T : Module.End (ZMod 2) V) (r : ℕ) (hTr : T ^ r = 1) :
    T * ∑ i ∈ Finset.range r, T ^ i = ∑ i ∈ Finset.range r, T ^ i := by
  have h1 : T * ∑ i ∈ Finset.range r, T ^ i = ∑ i ∈ Finset.range r, T ^ (i + 1) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => (pow_succ' T i).symm
  have h2 := Finset.sum_range_succ (fun i => T ^ i) r
  have h3 := Finset.sum_range_succ' (fun i => T ^ i) r
  rw [hTr] at h2
  simp only [pow_zero] at h3
  rw [h1]
  exact (add_right_cancel (h2.symm.trans h3)).symm

theorem exists_fixed_vector_uc6 (σ : E →* Module.End (ZMod 2) V) (hE : Odd (Nat.card E))
    (T : Module.End (ZMod 2) V) (α : MulAut E) (r : ℕ) (hr : 0 < r) (hTr : T ^ r = 1)
    (hTα : ∀ e, T * σ e = σ (α e) * T)
    (hfix : ∀ i, 0 < i → i < r → ∀ y, (α ^ i) y = y → y = 1)
    (W : Submodule (ZMod 2) V) (hWσ : ∀ e, ∀ w ∈ W, σ e w ∈ W) (hWT : ∀ w ∈ W, T w ∈ W)
    (hW0 : ∀ w ∈ W, nrmAll σ w = 0) (hne : W ≠ ⊥) : ∃ a ∈ W, a ≠ 0 ∧ T a = a := by
  obtain ⟨w, hwW, hw0⟩ := (Submodule.ne_bot_iff W).1 hne
  obtain ⟨ND, hND⟩ : ∃ ND : Module.End (ZMod 2) V, ND = ∑ i ∈ Finset.range r, T ^ i := ⟨_, rfl⟩
  have hmemT : ∀ i : ℕ, ∀ v ∈ W, (T ^ i) v ∈ W := by
    intro i
    induction i with
    | zero => intro v hv; simpa using hv
    | succ i ih =>
      intro v hv
      rw [pow_succ', Module.End.mul_apply]
      exact hWT _ (ih v hv)
  have hNDW : ∀ v ∈ W, ND v ∈ W := by
    intro v hv
    rw [hND, LinearMap.sum_apply]
    exact W.sum_mem fun i _ => hmemT i v hv
  have hTND : ∀ v, T (ND v) = ND v := by
    intro v
    have := congrArg (fun f : Module.End (ZMod 2) V => f v) (T_mul_sum_uc6 T r hTr)
    rw [← hND] at this
    simpa using this
  have hid := congrArg (fun f : Module.End (ZMod 2) V => f w)
    (frobenius_identity_uc6 σ hE T α r hr hTα hfix)
  rw [← hND] at hid
  simp only [LinearMap.sum_apply, Module.End.mul_apply, LinearMap.add_apply, Module.End.one_apply,
    LinearMap.sub_apply] at hid
  have hzero : nrmAll σ (ND w - w) = 0 := hW0 _ (W.sub_mem (hNDW w hwW) hwW)
  rw [hzero, add_zero] at hid
  by_contra hcon
  push Not at hcon
  have hall : ∀ y : E, σ y (ND (σ y⁻¹ w)) = 0 := by
    intro y
    have hmem : ND (σ y⁻¹ w) ∈ W := hNDW _ (hWσ _ w hwW)
    have h0 : ND (σ y⁻¹ w) = 0 := by
      by_contra hne0
      exact hcon _ hmem hne0 (hTND _)
    rw [h0, map_zero]
  simp only [hall, Finset.sum_const_zero] at hid
  exact hw0 hid.symm

theorem nrmOp_eq_zero_of_fixed_uc6 (σ : E →* Module.End (ZMod 2) V) {q : ℕ} (hq : q.Prime)
    (hq2 : q ≠ 2) (hexp : ∀ e : E, e ^ q = 1)
    (K : Subgroup E) (hK : K.index = q) {y : E} (hy : y ∉ K) {u : V} (hyu : σ y u = u)
    (hu : nrmAll σ u = 0) : nrmOp σ K u = 0 := by
  haveI : Fact q.Prime := ⟨hq⟩
  have hy1 : y ≠ 1 := fun h => hy (h ▸ K.one_mem)
  have hord : orderOf y = q := orderOf_eq_prime (hexp y) hy1
  have hYcard : Nat.card (Subgroup.zpowers y) = q := by rw [Nat.card_zpowers, hord]
  have hdisj : Disjoint K (Subgroup.zpowers y) := by
    have hdvd : Nat.card ↥(K ⊓ Subgroup.zpowers y) ∣ q :=
      hYcard ▸ Subgroup.card_dvd_of_le inf_le_right
    rcases (Nat.dvd_prime hq).1 hdvd with h1 | h1
    · exact disjoint_iff.2 (Subgroup.card_eq_one.1 h1)
    · exfalso
      have hJY : K ⊓ Subgroup.zpowers y = Subgroup.zpowers y :=
        Subgroup.eq_of_le_of_card_ge inf_le_right (by rw [h1, hYcard])
      have hyJ : y ∈ K ⊓ Subgroup.zpowers y := by
        rw [hJY]
        exact Subgroup.mem_zpowers y
      exact hy hyJ.1
  have hcardmul : Nat.card K * Nat.card (Subgroup.zpowers y) = Nat.card E := by
    rw [hYcard, ← hK]
    exact Subgroup.card_mul_index K
  have hcomp : K.IsComplement' (Subgroup.zpowers y) :=
    Subgroup.isComplement'_of_card_mul_and_disjoint hcardmul hdisj
  have hbij : Function.Bijective
      (fun x : ↥K × ↥(Subgroup.zpowers y) => (x.1 : E) * (x.2 : E)) :=
    (Subgroup.isComplement_iff_bijective K (Subgroup.zpowers y)).1 hcomp
  have hfixY : ∀ t ∈ Subgroup.zpowers y, σ t u = u := by
    intro t ht
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 ht
    clear ht
    induction n using Int.induction_on with
    | zero => simp
    | succ i ih =>
      rw [zpow_add_one, map_mul, Module.End.mul_apply, hyu, ih]
    | pred i ih =>
      have hinv : σ y⁻¹ u = u := by
        have := congrArg (σ y⁻¹) hyu
        rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one] at this
        simpa using this.symm
      rw [zpow_sub_one, map_mul, Module.End.mul_apply, hinv, ih]
  haveI : Fintype ↥K := Fintype.ofFinite _
  haveI : Fintype ↥(Subgroup.zpowers y) := Fintype.ofFinite _
  have h1 : nrmAll σ u = q • nrmOp σ K u := by
    rw [nrmAll_eq_sum_uc6, LinearMap.sum_apply,
      ← Function.Bijective.sum_comp hbij (fun e => σ e u)]
    have hx : ∀ x : ↥K × ↥(Subgroup.zpowers y), σ ((x.1 : E) * (x.2 : E)) u = σ (x.1 : E) u := by
      intro x
      rw [map_mul, Module.End.mul_apply, hfixY x.2 x.2.2]
    simp only [hx]
    rw [Fintype.sum_prod_type, nrmOp_eq_sum_uc6, LinearMap.sum_apply]
    simp only [Finset.sum_const, Finset.card_univ]
    rw [← Nat.card_eq_fintype_card, hYcard, Finset.smul_sum]
  rw [h1] at hu
  rwa [odd_nsmul_vec_uc6 (hq.odd_of_ne_two hq2)] at hu

end Frobenius2

end CFSG.LocalAnalysis.UniquenessCase.UC6
