module

public import CFSG.LinearAlgebra.SL2MinimalFaithfulMatrix
public import CFSG.Quasithin.Vol2.Ch11G2Q8InvLong

public section

namespace CFSG.Quasithin.Vol2.Ch11.G2Q8

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall
  CFSG.Quasithin.Vol2.KGNat Matrix
open CFSG.ClassicalInvolution.ModelFacts.OddCover (uSL uSL_mul uSL_inv)

variable {F : Type} [Field F] [CharP F 2]

theorem card_le_card_inf_mul {G M : Type*} [Group G] [Group M] [Finite G] {Γ K : Subgroup G}
    (φ : ↥Γ →* M) (hker : ∀ g : ↥Γ, φ g = 1 ↔ (g : G) ∈ K) :
    Nat.card ↥Γ ≤ Nat.card ↥(Γ ⊓ K) * Nat.card ↥φ.range := by
  have h1 : Nat.card ↥Γ = Nat.card ↥φ.range * Nat.card ↥φ.ker := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup φ.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv]
  have h2 : Nat.card ↥φ.ker = Nat.card ↥(Γ ⊓ K) := Nat.card_congr
    { toFun := fun g => ⟨g.1.1, g.1.2, (hker g.1).mp g.2⟩
      invFun := fun g => ⟨⟨g.1, g.2.1⟩, (hker ⟨g.1, g.2.1⟩).mpr g.2.2⟩
      left_inv := fun g => rfl
      right_inv := fun g => rfl }
  rw [h1, h2, mul_comm]

theorem card_le_mul_card_inf_R1 [Finite F] {n : ℕ} (hF : Nat.card F = 2 ^ n) (hn : 1 ≤ n)
    {Γ : Subgroup ↥(cayleyGroup F)} (hΓS : Γ ≤ stabV0 F) (hΓ1 : ∀ γ ∈ Γ, γ * γ = 1) :
    Nat.card ↥Γ ≤ Nat.card F * Nat.card ↥(Γ ⊓ pCoreOf 2 (stabV0 F)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := finite_cayleyGroup (F := F)
  let φ : ↥Γ →* SpecialLinearGroup (Fin 2) F := (levi1 (F := F)).comp (Subgroup.inclusion hΓS)
  have hker : ∀ g : ↥Γ, φ g = 1 ↔ (g : ↥(cayleyGroup F)) ∈ pCoreOf 2 (stabV0 F) := by
    intro g
    rw [mem_pCoreOf_stabV0_iff]
    constructor
    · intro h
      refine ⟨hΓS g.2, ?_⟩
      have h1 := congrArg (fun N : SpecialLinearGroup (Fin 2) F =>
        (N : Matrix (Fin 2) (Fin 2) F)) h
      exact h1
    · rintro ⟨-, h⟩
      exact Subtype.ext h
  have h1 := card_le_card_inf_mul φ hker
  have h2 : Nat.card ↥φ.range ≤ Nat.card F := by
    have hp : IsPGroup 2 ↥φ.range := by
      rintro ⟨_, g, rfl⟩
      refine ⟨1, Subtype.ext ?_⟩
      rw [pow_one, Subgroup.coe_pow, sq, ← map_mul, show g * g = 1 from Subtype.ext
        (hΓ1 g g.2), map_one, Subgroup.coe_one]
    obtain ⟨k, hk⟩ := (IsPGroup.iff_card).mp hp
    have hdvd : 2 ^ k ∣ Nat.card F * (Nat.card F ^ 2 - 1) := by
      rw [← hk, ← CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two F]
      exact Subgroup.card_subgroup_dvd_card _
    have hodd : Odd (Nat.card F ^ 2 - 1) := by
      have h4 : 1 ≤ Nat.card F ^ 2 := Nat.one_le_pow _ _ (by rw [hF]; positivity)
      exact Nat.Even.sub_odd h4 (by rw [hF, ← pow_mul]; exact (Nat.even_pow.mpr
        ⟨even_two, by omega⟩)) odd_one
    have hcop : Nat.Coprime (2 ^ k) (Nat.card F ^ 2 - 1) :=
      Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr hodd)
    rw [hk]
    exact Nat.le_of_dvd (by rw [hF]; positivity) (hcop.dvd_of_dvd_mul_right hdvd)
  calc Nat.card ↥Γ ≤ Nat.card ↥(Γ ⊓ pCoreOf 2 (stabV0 F)) * Nat.card ↥φ.range := h1
    _ ≤ Nat.card ↥(Γ ⊓ pCoreOf 2 (stabV0 F)) * Nat.card F := Nat.mul_le_mul_left _ h2
    _ = _ := mul_comm _ _

@[expose] def A1 (F : Type) [Field F] [CharP F 2] : Subgroup ↥(cayleyGroup F) where
  carrier := {g | ∀ w ∈ stdF F 3, g2Act g w = w}
  one_mem' := fun w _ => by
    rw [map_one]
    rfl
  mul_mem' := fun {a b} ha hb w hw => by rw [g2Act_mul_apply, hb w hw, ha w hw]
  inv_mem' := fun {a} ha w hw => by
    have h1 := congrArg (g2Act a⁻¹) (ha w hw)
    rwa [g2Act_inv_apply, eq_comm] at h1

theorem mem_A1 {g : ↥(cayleyGroup F)} : g ∈ A1 F ↔ ∀ w ∈ stdF F 3, g2Act g w = w := Iff.rfl

theorem kerElt_mem_A1 (α p q' : F) :
    g2X ![α, 0, 0] * g2Y ![0, 0, 0] * g2A (uSL p q' 0) ∈ A1 F := by
  intro w hw
  obtain ⟨h1, h2, h3⟩ := mem_stdF_three.mp hw
  have hw' : w = q6 (w (.inl 0)) 0 0 0 (w (.inr 1)) (w (.inr 2)) := by
    conv_lhs => rw [q6_eta w]
    rw [h1, h2, h3]
  rw [hw', g2Act_kerElt]
  refine q6_congr ?_ ?_ ?_ ?_ ?_ ?_ <;> ring

theorem exists_eq_of_mem_A1 {g : ↥(cayleyGroup F)} (hg : g ∈ A1 F) :
    ∃ α p q' : F, g = g2X ![α, 0, 0] * g2Y ![0, 0, 0] * g2A (uSL p q' 0) := by
  have hu : eu (0 : Fin 3) (1 : F) ∈ stdF F 3 := mem_stdF_three.mpr ⟨rfl, rfl, rfl⟩
  have hS : g ∈ stabV0 F := hg _ hu
  have hM : levi1Mat g = 1 := by
    ext i j
    have hmem : q6 (0 : F) 0 0 0 (if j = 0 then 1 else 0) (if j = 1 then 1 else 0) ∈
        stdF F 3 := mem_stdF_three.mpr ⟨rfl, rfl, rfl⟩
    rw [levi1Mat_apply, hg _ hmem]
    fin_cases i <;> fin_cases j <;> simp [vpart, q6]
  obtain ⟨α, β, γ, p, q', rfl⟩ := eq_of_levi1Mat_eq_one hS hM
  have e1 := hg (q6 0 0 0 0 1 0) (mem_stdF_three.mpr ⟨rfl, rfl, rfl⟩)
  have e2 := hg (q6 0 0 0 0 0 1) (mem_stdF_three.mpr ⟨rfl, rfl, rfl⟩)
  rw [g2Act_kerElt] at e1 e2
  obtain ⟨e10, -⟩ := q6_inj e1
  obtain ⟨e20, -⟩ := q6_inj e2
  have hγ : γ = 0 := by linear_combination e10
  have hβ : β = 0 := by linear_combination e20
  subst hβ hγ
  exact ⟨α, p, q', rfl⟩

theorem card_A1_le [Finite F] : Nat.card ↥(A1 F) ≤ Nat.card F ^ 3 := by
  have hs : Function.Surjective (fun t : Fin 3 → F =>
      (⟨g2X ![t 0, 0, 0] * g2Y ![0, 0, 0] * g2A (uSL (t 1) (t 2) 0), kerElt_mem_A1 _ _ _⟩ :
        ↥(A1 F))) := by
    rintro ⟨g, hg⟩
    obtain ⟨α, p, q', rfl⟩ := exists_eq_of_mem_A1 hg
    exact ⟨![α, p, q'], rfl⟩
  have h1 := Nat.card_le_card_of_surjective _ hs
  rwa [Nat.card_fun, Nat.card_fin] at h1

theorem g2Act_A1 (α p q' a b c d e f : F) :
    g2Act (g2X ![α, 0, 0] * g2Y ![0, 0, 0] * g2A (uSL p q' 0)) (q6 a b c d e f) =
      q6 (a + p * b + q' * c + α * α * d) b c d (e + p * d + α * c) (f + q' * d + α * b) := by
  rw [g2Act_kerElt]
  refine q6_congr ?_ ?_ ?_ ?_ ?_ ?_ <;> ring

@[expose] def OnLine : Option F → F × F → Prop
  | none, v => v.1 = 0
  | some s, v => v.2 = s * v.1

@[expose] def rootD (d : Option F) : Subgroup ↥(cayleyGroup F) where
  carrier := {g | ∃ v : F × F, OnLine d v ∧ g = g2A (uSL v.1 v.2 0)}
  one_mem' := ⟨(0, 0), by cases d <;> simp [OnLine],
    by rw [CFSG.ClassicalInvolution.ModelFacts.OddCover.uSL_zero, map_one]⟩
  mul_mem' := by
    rintro _ _ ⟨v, hv, rfl⟩ ⟨w, hw, rfl⟩
    refine ⟨v + w, ?_, ?_⟩
    · cases d with
      | none => simp only [OnLine, Prod.fst_add] at hv hw ⊢; rw [hv, hw, add_zero]
      | some s => simp only [OnLine, Prod.fst_add, Prod.snd_add] at hv hw ⊢; rw [hv, hw]; ring
    · rw [← map_mul, uSL_mul]
      simp
  inv_mem' := by
    rintro _ ⟨v, hv, rfl⟩
    refine ⟨-v, ?_, ?_⟩
    · cases d with
      | none => simp only [OnLine, Prod.fst_neg] at hv ⊢; rw [hv, neg_zero]
      | some s => simp only [OnLine, Prod.fst_neg, Prod.snd_neg] at hv ⊢; rw [hv]; ring
    · rw [← map_inv, uSL_inv]
      simp

@[expose] def rootW : Option F → (Ix3 → F)
  | none => q6 0 1 0 0 0 0
  | some s => q6 0 s 1 0 0 0

omit [CharP F 2] in
theorem rootW_not_mem (d : Option F) : rootW d ∉ stdF F 3 := by
  intro h
  obtain ⟨h1, h2, -⟩ := mem_stdF_three.mp h
  cases d with
  | none => simp [rootW, q6] at h1
  | some s => simp [rootW, q6] at h2

theorem rootD_fix (d : Option F) {g : ↥(cayleyGroup F)} (hg : g ∈ rootD d) :
    g2Act g (rootW d) = rootW d := by
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  obtain ⟨v, hv, rfl⟩ := hg
  cases d with
  | none =>
    simp only [OnLine] at hv
    rw [rootW, g2Act_g2A_uSL]
    funext j
    rcases j with j | j <;> fin_cases j <;> simp [q6, hv]
  | some s =>
    simp only [OnLine] at hv
    rw [rootW, g2Act_g2A_uSL]
    funext j
    rcases j with j | j <;> fin_cases j <;> simp [q6, hv]
    linear_combination s * v.1 * h2

theorem rootD_le_A1 (d : Option F) : rootD d ≤ A1 F := by
  rintro _ ⟨v, -, rfl⟩
  have h := kerElt_mem_A1 (0 : F) v.1 v.2
  rwa [show (![(0 : F), 0, 0] : Fin 3 → F) = 0 from funext fun i => by fin_cases i <;> rfl,
    g2X_zero, g2Y_zero, one_mul, one_mul] at h

@[expose] def Z1 (F : Type) [Field F] [CharP F 2] : Subgroup ↥(cayleyGroup F) where
  carrier := {g | ∃ v : F × F, g = g2A (uSL v.1 v.2 0)}
  one_mem' := ⟨(0, 0), by rw [CFSG.ClassicalInvolution.ModelFacts.OddCover.uSL_zero, map_one]⟩
  mul_mem' := by
    rintro _ _ ⟨v, rfl⟩ ⟨w, rfl⟩
    exact ⟨v + w, by rw [← map_mul, uSL_mul]; simp⟩
  inv_mem' := by
    rintro _ ⟨v, rfl⟩
    exact ⟨-v, by rw [← map_inv, uSL_inv]; simp⟩

theorem g2Act_uSL_v0 (a b : F) : g2Act (g2A (uSL a b 0)) (q6 0 0 0 1 0 0) = q6 0 0 0 1 a b := by
  rw [g2Act_g2A_uSL]
  refine q6_congr ?_ ?_ ?_ ?_ ?_ ?_ <;> simp [q6]

theorem g2A_uSL_injective {v w : F × F} (h : g2A (uSL v.1 v.2 0) = g2A (uSL w.1 w.2 0)) :
    v = w := by
  have h1 := congrArg (fun g => g2Act g (q6 (0 : F) 0 0 1 0 0)) h
  simp only [g2Act_uSL_v0] at h1
  obtain ⟨-, -, -, -, e1, e2⟩ := q6_inj h1
  exact Prod.ext e1 e2

@[expose] def FixStable (k : ℕ) (Γ : Subgroup ↥(cayleyGroup F)) : Prop :=
  ∀ B ≤ Γ, Nat.card ↥Γ < k * Nat.card ↥B → ∀ w, (∀ b ∈ B, g2Act b w = w) →
    ∀ γ ∈ Γ, g2Act γ w = w

theorem card_le_mul_card_inf_Z1 [Finite F] {Γ : Subgroup ↥(cayleyGroup F)} (hΓ : Γ ≤ A1 F) :
    Nat.card ↥Γ ≤ Nat.card ↥(Γ ⊓ Z1 F) * Nat.card F := by
  have := finite_cayleyGroup (F := F)
  have hval : ∀ g : ↥Γ, ∃ α p q' : F, (g : ↥(cayleyGroup F)) =
      g2X ![α, 0, 0] * g2Y ![0, 0, 0] * g2A (uSL p q' 0) := fun g =>
    exists_eq_of_mem_A1 (hΓ g.2)
  let ψ : ↥Γ →* Multiplicative F :=
    { toFun := fun g =>
        Multiplicative.ofAdd (g2Act (g : ↥(cayleyGroup F)) (q6 0 0 0 1 0 0) (.inl 0))
      map_one' := by
        simp only [OneMemClass.coe_one, map_one]
        rfl
      map_mul' := fun g h => by
        obtain ⟨α, p, q', hg⟩ := hval g
        obtain ⟨α', p', q'', hh⟩ := hval h
        rw [Subgroup.coe_mul, g2Act_mul_apply, hg, hh, g2Act_A1, g2Act_A1, g2Act_A1]
        simp only [q6_apply_inl0, ← ofAdd_add]
        congr 1
        ring }
  have hker : ∀ g : ↥Γ, ψ g = 1 ↔ (g : ↥(cayleyGroup F)) ∈ Z1 F := by
    intro g
    obtain ⟨α, p, q', hg⟩ := hval g
    change Multiplicative.ofAdd _ = 1 ↔ _
    rw [hg, g2Act_A1, q6_apply_inl0, ← ofAdd_zero, EmbeddingLike.apply_eq_iff_eq]
    constructor
    · intro h0
      have hα : α = 0 := mul_self_eq_zero.mp (by linear_combination h0)
      subst hα
      refine ⟨(p, q'), ?_⟩
      rw [show (![(0 : F), 0, 0] : Fin 3 → F) = 0 from funext fun i => by fin_cases i <;> rfl,
        g2X_zero, g2Y_zero, one_mul, one_mul]
    · rintro ⟨v, hv⟩
      have h1 := congrArg (fun g => g2Act g (q6 (0 : F) 0 0 1 0 0)) hv
      simp only [g2Act_A1, g2Act_uSL_v0] at h1
      obtain ⟨e, -⟩ := q6_inj h1
      linear_combination e
  have h1 := card_le_card_inf_mul ψ hker
  have h2 : Nat.card ↥ψ.range ≤ Nat.card F :=
    (Nat.card_le_card_of_injective _ Subtype.val_injective).trans_eq (Nat.card_congr
      Multiplicative.toAdd)
  exact h1.trans (Nat.mul_le_mul_left _ h2)

theorem eq_A1_of_le [Finite F] {Γ : Subgroup ↥(cayleyGroup F)} (hΓ : Γ ≤ A1 F)
    (hfix : ∀ w, (∀ γ ∈ Γ, g2Act γ w = w) → w ∈ stdF F 3)
    (hP : FixStable (Nat.card F ^ 2) Γ) : Γ = A1 F := by
  classical
  have := Fintype.ofFinite F
  have := finite_cayleyGroup (F := F)
  have hq : 1 < Nat.card F := Finite.one_lt_card
  have hD : ∀ d : Option F, Nat.card F ^ 2 * Nat.card ↥(Γ ⊓ rootD d) ≤ Nat.card ↥Γ := by
    intro d
    by_contra h
    exact rootW_not_mem d (hfix _ (hP (Γ ⊓ rootD d) inf_le_left (not_le.mp h) (rootW d)
      fun b hb => rootD_fix d hb.2))
  obtain ⟨T, hTdef⟩ : ∃ T : Finset (F × F),
      T = Finset.univ.filter fun v => g2A (uSL v.1 v.2 0) ∈ Γ := ⟨_, rfl⟩
  obtain ⟨L, hLdef⟩ : ∃ L : Option F → Finset (F × F),
      L = fun d => Finset.univ.filter fun v => OnLine d v := ⟨_, rfl⟩
  have hmemT : ∀ v, v ∈ T ↔ g2A (uSL v.1 v.2 0) ∈ Γ := fun v => by
    rw [hTdef, Finset.mem_filter]
    exact and_iff_right (Finset.mem_univ v)
  have hmemL : ∀ d v, v ∈ L d ↔ OnLine d v := fun d v => by
    rw [hLdef, Finset.mem_filter]
    exact and_iff_right (Finset.mem_univ v)
  have hTL : ∀ d, (T ∩ L d).card ≤ Nat.card ↥(Γ ⊓ rootD d) := by
    intro d
    have hinj : Function.Injective (fun v : ↥(T ∩ L d) =>
        (⟨g2A (uSL v.1.1 v.1.2 0), by
          have hv := Finset.mem_inter.mp v.2
          exact ⟨(hmemT _).mp hv.1, v.1, (hmemL _ _).mp hv.2, rfl⟩⟩ : ↥(Γ ⊓ rootD d))) := by
      intro v w h
      exact Subtype.ext (g2A_uSL_injective (congrArg Subtype.val h))
    have h1 := Nat.card_le_card_of_injective _ hinj
    rwa [Nat.card_eq_finsetCard] at h1
  have hZT : Nat.card ↥(Γ ⊓ Z1 F) ≤ T.card := by
    have hinj : Function.Injective (fun g : ↥(Γ ⊓ Z1 F) =>
        (⟨(g2Act (g : ↥(cayleyGroup F)) (q6 0 0 0 1 0 0) (.inr 1),
          g2Act (g : ↥(cayleyGroup F)) (q6 0 0 0 1 0 0) (.inr 2)), by
          obtain ⟨v, hv⟩ := g.2.2
          rw [hmemT, hv, g2Act_uSL_v0]
          simp only [q6_apply_inr1, q6_apply_inr2]
          rw [← hv]
          exact g.2.1⟩ : ↥T)) := by
      rintro ⟨g, hgΓ, v, hv⟩ ⟨g', hg'Γ, v', hv'⟩ h
      simp only [Subtype.mk.injEq, Prod.mk.injEq] at h
      rw [hv, hv', g2Act_uSL_v0, g2Act_uSL_v0] at h
      simp only [q6_apply_inr1, q6_apply_inr2] at h
      apply Subtype.ext
      change g = g'
      rw [hv, hv', show v = v' from Prod.ext h.1 h.2]
    have h1 := Nat.card_le_card_of_injective _ hinj
    rwa [Nat.card_eq_finsetCard] at h1
  have hT0 : (0 : F × F) ∈ T := by
    rw [hmemT, Prod.fst_zero, Prod.snd_zero,
      CFSG.ClassicalInvolution.ModelFacts.OddCover.uSL_zero, map_one]
    exact Γ.one_mem
  have hΓT : Nat.card ↥Γ ≤ T.card * Nat.card F :=
    (card_le_mul_card_inf_Z1 hΓ).trans (Nat.mul_le_mul_right _ hZT)
  have hline : ∀ d, Nat.card F * (T ∩ L d).card ≤ T.card := by
    intro d
    have h1 := (Nat.mul_le_mul_left (Nat.card F ^ 2) (hTL d)).trans ((hD d).trans hΓT)
    rw [sq, mul_assoc, mul_comm (T.card)] at h1
    exact Nat.le_of_mul_le_mul_left h1 (by omega)
  have hcover : T.erase 0 ⊆ Finset.univ.biUnion fun d => (T ∩ L d).erase 0 := by
    intro v hv
    rw [Finset.mem_erase] at hv
    rw [Finset.mem_biUnion]
    by_cases h1 : v.1 = 0
    · refine ⟨none, Finset.mem_univ _, Finset.mem_erase.mpr ⟨hv.1, ?_⟩⟩
      exact Finset.mem_inter.mpr ⟨hv.2, (hmemL _ _).mpr h1⟩
    · refine ⟨some (v.2 / v.1), Finset.mem_univ _, Finset.mem_erase.mpr ⟨hv.1, ?_⟩⟩
      refine Finset.mem_inter.mpr ⟨hv.2, (hmemL _ _).mpr ?_⟩
      show v.2 = v.2 / v.1 * v.1
      field_simp
  have hsum := (Finset.card_le_card hcover).trans Finset.card_biUnion_le
  have hcardO : (Finset.univ : Finset (Option F)).card = Nat.card F + 1 := by
    rw [Finset.card_univ, Fintype.card_option, Nat.card_eq_fintype_card]
  have hmem0 : ∀ d, (0 : F × F) ∈ T ∩ L d := fun d => by
    refine Finset.mem_inter.mpr ⟨hT0, (hmemL _ _).mpr ?_⟩
    cases d with
    | none => rfl
    | some s => exact (mul_zero s).symm
  have hT : Nat.card F ^ 2 ≤ T.card := by
    have h1 : ∀ d ∈ (Finset.univ : Finset (Option F)),
        Nat.card F * (((T ∩ L d).erase 0).card + 1) ≤ T.card := by
      intro d _
      rw [Finset.card_erase_add_one (hmem0 d)]
      exact hline d
    have h3 := Finset.sum_le_card_nsmul _ _ _ h1
    rw [hcardO, smul_eq_mul, ← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_const,
      hcardO, smul_eq_mul, mul_one] at h3
    have h4 := Finset.card_erase_add_one hT0
    have h5 := Nat.mul_le_mul_left (Nat.card F) hsum
    have h6 : Nat.card F * T.card + Nat.card F * Nat.card F ≤ Nat.card F * T.card + T.card := by
      calc Nat.card F * T.card + Nat.card F * Nat.card F
          = Nat.card F * (T.erase 0).card + Nat.card F * Nat.card F + Nat.card F := by
            rw [← h4]; ring
        _ ≤ Nat.card F * (∑ a, ((T ∩ L a).erase 0).card) + Nat.card F * Nat.card F +
            Nat.card F := Nat.add_le_add_right (Nat.add_le_add_right h5 _) _
        _ = Nat.card F * (∑ a, ((T ∩ L a).erase 0).card + (Nat.card F + 1)) := by ring
        _ ≤ (Nat.card F + 1) * T.card := h3
        _ = Nat.card F * T.card + T.card := by ring
    rw [sq]
    exact Nat.le_of_add_le_add_left h6
  have hcardFF : (Finset.univ : Finset (F × F)).card = Nat.card F ^ 2 := by
    rw [Finset.card_univ, Fintype.card_prod, ← Nat.card_eq_fintype_card, sq]
  have hTall : T = Finset.univ :=
    Finset.eq_univ_of_card _ (le_antisymm (Finset.card_le_univ _)
      (by rw [← Finset.card_univ, hcardFF]; exact hT))
  have hDinf : Nat.card F ≤ Nat.card ↥(Γ ⊓ rootD (none : Option F)) := by
    have h1 := hTL none
    have h3 : (Finset.univ : Finset F).card ≤ (T ∩ L none).card := by
      refine Finset.card_le_card_of_injOn (fun t => ((0 : F), t)) (fun t _ => ?_)
        (fun a _ b _ h => (Prod.mk.inj h).2)
      rw [Finset.mem_coe, hTall, Finset.univ_inter, hmemL]
      rfl
    rw [Finset.card_univ, ← Nat.card_eq_fintype_card] at h3
    exact h3.trans h1
  have h1 := (Nat.mul_le_mul_left (Nat.card F ^ 2) hDinf).trans (hD none)
  have h3 : Nat.card ↥(A1 F) ≤ Nat.card ↥Γ := by
    calc Nat.card ↥(A1 F) ≤ Nat.card F ^ 3 := card_A1_le
      _ = Nat.card F ^ 2 * Nat.card F := by ring
      _ ≤ Nat.card ↥Γ := h1
  exact Subgroup.eq_of_le_of_card_ge hΓ h3

end CFSG.Quasithin.Vol2.Ch11.G2Q8
