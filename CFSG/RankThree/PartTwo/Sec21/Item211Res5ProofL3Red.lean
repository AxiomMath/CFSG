module

public import CFSG.RankThree.PartTwo.Sec21.Item211Lie3ProofU3Inn

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG
open CFSG.Assembly (IsElemAbelian)
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag (projectiveSL)
open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial

namespace Item211Res5Proof

open Item211Lie2Proof

section Abstract

variable {M : Type*} [Group M]

@[expose] def threeClosureIn (I T : Subgroup M) : Subgroup M :=
  Subgroup.closure {τ | τ ∈ I ⊓ Subgroup.centralizer (T : Set M) ∧ τ ^ 3 = 1}

theorem conj_mem_closure_of_gen {s : Set M} {g : M} (hs : ∀ x ∈ s, g * x * g⁻¹ ∈ s)
    {y : M} (hy : y ∈ Subgroup.closure s) : g * y * g⁻¹ ∈ Subgroup.closure s := by
  have hle : Subgroup.closure s ≤ (Subgroup.closure s).comap (MulAut.conj g).toMonoidHom :=
    (Subgroup.closure_le _).mpr fun x hx => Subgroup.subset_closure (hs x hx)
  exact hle hy

theorem eq_one_of_mem_two_of_cube' {Q : Subgroup M} (hQ : IsPGroup 2 Q) {x : M} (hx : x ∈ Q)
    (h3 : x ^ 3 = 1) : x = 1 := by
  obtain ⟨e, he⟩ := hQ ⟨x, hx⟩
  have he' : x ^ 2 ^ e = 1 := by simpa using congrArg Subtype.val he
  have h1 := orderOf_dvd_of_pow_eq_one he'
  have h2 := orderOf_dvd_of_pow_eq_one h3
  have hcop : Nat.Coprime (2 ^ e) 3 := Nat.Coprime.pow_left e (by norm_num)
  rw [← orderOf_eq_one_iff]
  exact Nat.eq_one_of_dvd_coprimes hcop h1 h2

theorem conj_mem_range_conj' {X : Type*} [Group X] (τ : MulAut X) {x : MulAut X}
    (hx : x ∈ (MulAut.conj : X →* MulAut X).range) :
    τ * x * τ⁻¹ ∈ (MulAut.conj : X →* MulAut X).range := by
  obtain ⟨y, rfl⟩ := hx
  refine ⟨τ y, ?_⟩
  ext m
  simp [MulAut.mul_apply, map_mul, map_inv]

theorem eq_of_sq_eq_one_of_isCyclic {α : Type*} [Group α] [Finite α] [IsCyclic α] {x y : α}
    (hx : x ^ 2 = 1) (hy : y ^ 2 = 1) (hx1 : x ≠ 1) (hy1 : y ≠ 1) : x = y := by
  classical
  have := Fintype.ofFinite α
  have h := IsCyclic.card_pow_eq_one_le (α := α) (n := 2) (by norm_num)
  by_contra hxy
  have hsub : ({1, x, y} : Finset α) ⊆ Finset.univ.filter (fun a : α => a ^ 2 = 1) := by
    intro a ha
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl | rfl <;> simp [*]
  have hcard : ({1, x, y} : Finset α).card = 3 := by
    rw [Finset.card_insert_of_notMem, Finset.card_pair hxy]
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨Ne.symm hx1, Ne.symm hy1⟩
  have := Finset.card_le_card hsub
  omega

theorem eq_bot_of_threeClosure [Finite M] {I D T V W : Subgroup M}
    (hI : ∀ g x : M, x ∈ I → g * x * g⁻¹ ∈ I) (hDodd : Odd (Nat.card D)) (hVi : V ≤ I)
    (hV2 : IsPGroup 2 V) (hDV : D ≤ Subgroup.normalizer (V : Set M)) (hVD : ⁅V, D⁆ = V)
    (hVT : V ≤ Subgroup.centralizer (T : Set M)) (hW2 : IsPGroup 2 W) (hVW : V ≤ W)
    (hWT : W ≤ Subgroup.centralizer (T : Set M))
    (hτ : ∀ τ ∈ I ⊓ Subgroup.centralizer (T : Set M), τ ^ 3 = 1 →
      τ ∈ Subgroup.normalizer (W : Set M))
    (ha : ∀ P : Subgroup M, P ≤ threeClosureIn I T → IsPGroup 2 P →
      threeClosureIn I T ≤ Subgroup.normalizer (P : Set M) →
        ∀ x ∈ P, ∀ n ∈ threeClosureIn I T, x * n = n * x)
    (hb : ∀ P : Subgroup M, P ≤ I ⊓ Subgroup.centralizer (T : Set M) ⊓
      Subgroup.centralizer (threeClosureIn I T : Set M) → IsPGroup 2 P → IsCyclic P) :
    V = ⊥ := by
  classical
  set N := threeClosureIn I T with hN
  set s := {τ | τ ∈ I ⊓ Subgroup.centralizer (T : Set M) ∧ τ ^ 3 = 1} with hs
  have hNW : N ≤ Subgroup.normalizer (W : Set M) :=
    (Subgroup.closure_le _).mpr fun τ hτs => hτ τ hτs.1 hτs.2
  have hgen : ∀ w ∈ W, ∀ x ∈ s, w * x * w⁻¹ ∈ s := by
    intro w hw x hx
    obtain ⟨hxI, hxT⟩ := Subgroup.mem_inf.mp hx.1
    refine ⟨Subgroup.mem_inf.mpr ⟨hI w x hxI, ?_⟩, ?_⟩
    · rw [Subgroup.mem_centralizer_iff]
      intro t ht
      have h1 := Subgroup.mem_centralizer_iff.mp (hWT hw) t ht
      have h2 := Subgroup.mem_centralizer_iff.mp hxT t ht
      have h3 : t * w⁻¹ = w⁻¹ * t := (show Commute t w from h1).inv_right
      calc t * (w * x * w⁻¹) = (t * w) * x * w⁻¹ := by group
        _ = w * (t * x) * w⁻¹ := by rw [h1]; group
        _ = w * (x * t) * w⁻¹ := by rw [h2]
        _ = w * x * (t * w⁻¹) := by group
        _ = w * x * w⁻¹ * t := by rw [h3]; group
    · rw [conj_pow, hx.2, mul_one, mul_inv_cancel]
  have hWN : ∀ w ∈ W, ∀ y ∈ N, w * y * w⁻¹ ∈ N := fun w hw y hy =>
    conj_mem_closure_of_gen (hgen w hw) hy
  have hP₀N : N ≤ Subgroup.normalizer ((W ⊓ N : Subgroup M) : Set M) := fun n hn =>
    CFSG.RankThree.GroupTheory.SteinbergBY.mem_normalizer_inf (hNW hn) (Subgroup.le_normalizer hn)
  have hcen := ha (W ⊓ N) inf_le_right (hW2.to_le inf_le_left) hP₀N
  have hWC : W ≤ Subgroup.centralizer (N : Set M) := by
    intro w hw
    rw [Subgroup.mem_centralizer_iff]
    have hle : N ≤ Subgroup.centralizer ({w} : Set M) := by
      refine (Subgroup.closure_le _).mpr fun τ hτs => ?_
      rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
      have hτN : τ ∈ N := Subgroup.subset_closure hτs
      set c := w * τ * w⁻¹ * τ⁻¹ with hc
      have hcW : c ∈ W := by
        have h1 : τ * w⁻¹ * τ⁻¹ ∈ W :=
          (Subgroup.mem_normalizer_iff.mp (hNW hτN) _).mp (W.inv_mem hw)
        have e : c = w * (τ * w⁻¹ * τ⁻¹) := by rw [hc]; group
        rw [e]
        exact W.mul_mem hw h1
      have hcN : c ∈ N := N.mul_mem (hWN w hw τ hτN) (N.inv_mem hτN)
      have hcτ : c * τ = τ * c := hcen c ⟨hcW, hcN⟩ τ hτN
      have h3 : c ^ 3 = 1 := by
        have h4 : (w * τ * w⁻¹) ^ 3 = 1 := by rw [conj_pow, hτs.2, mul_one, mul_inv_cancel]
        have e : w * τ * w⁻¹ = c * τ := by rw [hc]; group
        rw [e, (show Commute c τ from hcτ).mul_pow, hτs.2, mul_one] at h4
        exact h4
      have hc1 : c = 1 := eq_one_of_mem_two_of_cube' hW2 hcW h3
      have e : w * τ * w⁻¹ = τ := by
        calc w * τ * w⁻¹ = c * τ := by rw [hc]; group
          _ = τ := by rw [hc1, one_mul]
      exact (by calc w * τ = w * τ * w⁻¹ * w := by group
        _ = τ * w := by rw [e] : w * τ = τ * w).symm
    intro n hn
    exact (Subgroup.mem_centralizer_singleton_iff.mp (hle hn))
  have hVC : V ≤ I ⊓ Subgroup.centralizer (T : Set M) ⊓
      Subgroup.centralizer (N : Set M) := fun v hv =>
    Subgroup.mem_inf.mpr ⟨Subgroup.mem_inf.mpr ⟨hVi hv, hVT hv⟩, hWC (hVW hv)⟩
  have hVcyc : IsCyclic V := hb V hVC hV2
  have : Finite V := inferInstance
  have : Finite D := inferInstance
  have hVcomm : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hVcyc.commGroup.mul_comm ⟨a, ha⟩ ⟨b, hb⟩)
  refine eq_bot_of_comm_of_fixed hVcomm hDodd hV2 hDV hVD fun v hv hv2 d hd => ?_
  by_cases hv1 : v = 1
  · rw [hv1, mul_one, one_mul]
  have hdv : d * v * d⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.mp (hDV hd) v).mp hv
  have hdv2 : (d * v * d⁻¹) ^ 2 = 1 := by rw [conj_pow, hv2, mul_one, mul_inv_cancel]
  have hdv1 : d * v * d⁻¹ ≠ 1 := by
    intro h
    apply hv1
    calc v = d⁻¹ * (d * v * d⁻¹) * d := by group
      _ = 1 := by rw [h]; group
  have heq : (⟨d * v * d⁻¹, hdv⟩ : V) = ⟨v, hv⟩ :=
    eq_of_sq_eq_one_of_isCyclic (Subtype.ext hdv2) (Subtype.ext hv2)
      (fun h => hdv1 (congrArg Subtype.val h)) (fun h => hv1 (congrArg Subtype.val h))
  have e : d * v * d⁻¹ = v := congrArg Subtype.val heq
  calc d * v = d * v * d⁻¹ * d := by group
    _ = v * d := by rw [e]

end Abstract

section Structure

variable {Y : Type*} [Group Y]

@[expose] def L3OuterCentFor (Y : Type*) [Group Y] : Prop :=
  ∀ D T : Subgroup (MulAut Y), IsElemAbelian 3 D → Nat.card D = 9 → IsPGroup 2 T →
    T ≠ ⊥ → T ≤ Subgroup.centralizer (D : Set (MulAut Y)) →
    ¬ (∀ a ∈ (MulAut.conj : Y →* MulAut Y).range ⊓ Subgroup.centralizer
        ((T ⊓ (MulAut.conj : Y →* MulAut Y).range : Subgroup (MulAut Y)) : Set (MulAut Y)),
      ∀ b ∈ (MulAut.conj : Y →* MulAut Y).range ⊓ Subgroup.centralizer
        ((T ⊓ (MulAut.conj : Y →* MulAut Y).range : Subgroup (MulAut Y)) : Set (MulAut Y)),
      a * b = b * a) →
    ¬ T ≤ (MulAut.conj : Y →* MulAut Y).range →
    (∀ P : Subgroup (MulAut Y), P ≤ threeClosureIn (MulAut.conj : Y →* MulAut Y).range T →
      IsPGroup 2 P → threeClosureIn (MulAut.conj : Y →* MulAut Y).range T ≤
        Subgroup.normalizer (P : Set (MulAut Y)) →
      ∀ x ∈ P, ∀ n ∈ threeClosureIn (MulAut.conj : Y →* MulAut Y).range T, x * n = n * x) ∧
    ∀ P : Subgroup (MulAut Y), P ≤ (MulAut.conj : Y →* MulAut Y).range ⊓
      Subgroup.centralizer (T : Set (MulAut Y)) ⊓ Subgroup.centralizer
        (threeClosureIn (MulAut.conj : Y →* MulAut Y).range T : Set (MulAut Y)) →
      IsPGroup 2 P → IsCyclic P

theorem l3PlusOuterFor_of_cent [Finite Y] (h : L3OuterCentFor Y) : L3PlusOuterFor Y := by
  intro D T V W hDe hD9 hT2 hT1 hTD hnab hTi hVi hV2 hDV hVD hVT hW2 hVW hWT hτ
  have : Finite (MulAut Y) :=
    Finite.of_injective (fun σ : MulAut Y => (σ : Y → Y)) (fun a b h => MulEquiv.ext (congrFun h))
  obtain ⟨ha, hb⟩ := h D T hDe hD9 hT2 hT1 hTD hnab hTi
  exact eq_bot_of_threeClosure (I := (MulAut.conj : Y →* MulAut Y).range)
    (fun g x hx => conj_mem_range_conj' g hx) (by rw [hD9]; decide) hVi hV2 hDV
    hVD hVT hW2 hVW hWT hτ ha hb

end Structure

end Item211Res5Proof

open Item211Res5Proof Item211Lie2Proof

@[expose] def KS211L3OuterCentLinear : Prop :=
  ∀ (K : Type) [Field K] [Finite K] (p : ℕ) [Fact p.Prime] [CharP K p], 3 < p →
    Nat.card K % 3 = 1 → L3OuterCentFor (projectiveSL 3 K)

@[expose] def KS211L3OuterCentUnitary : Prop :=
  ∀ (p f : ℕ) (K : Type) [Field K] (h : UnitaryFieldData p f K), 3 < p → p ^ f % 3 = 2 →
    L3OuterCentFor (unitaryPSU h 3)

theorem ks211L3PlusLinearOuter_of_cent (h : KS211L3OuterCentLinear) : KS211L3PlusLinearOuter := by
  intro K _ _ p _ _ hp3 hK
  have : Finite (projectiveSL 3 K) := by
    unfold projectiveSL
    infer_instance
  exact l3PlusOuterFor_of_cent (h K p hp3 hK)

theorem ks211L3PlusUnitaryOuter_of_cent (h : KS211L3OuterCentUnitary) :
    KS211L3PlusUnitaryOuter := by
  intro p f K _ hU hp3 hq
  have := hU.finite
  have : Finite (unitaryPSU hU 3) := by
    unfold unitaryPSU
    infer_instance
  exact l3PlusOuterFor_of_cent (h p f K hU hp3 hq)

end CFSG.RankThree.PartTwo.Sec21
