module

public import CFSG.Quasithin.Background.GoldschmidtAmalgamL3dGens
public import CFSG.Assembly.QuasithinDefs
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.SectionRank.SQT
public import CFSG.Quasithin.Background.F1Lemma10
public import CFSG.Quasithin.Background.F2Equiv
public import CFSG.Quasithin.Background.F6SolvableQuotient
public import CFSG.Quasithin.Background.F9Dual
public import CFSG.Quasithin.Background.F9Fourteen
public import CFSG.Quasithin.Background.GoldschmidtAmalgamL1Large
public import CFSG.Quasithin.Background.GoldschmidtAmalgamL3Red
public import CFSG.Quasithin.Background.GoldschmidtAmalgamL3Weak
public import CFSG.Quasithin.Background.GoldschmidtAmalgamSplit
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.FinalTheorem

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.F7
  CFSG.Quasithin.CosetGeom CFSG.Quasithin.F6.GoldAmL

namespace F6

namespace GoldAmL3

variable {D : Type*} [Group D] [Finite D] {A B : Subgroup D} {z : D} {V : Subgroup D}

structure Crit (A B : Subgroup D) (z : D) (V : Subgroup D) : Type _ where
  k : D
  u : D
  mem_A : k ∈ A
  cube : k * k * k = 1
  not_mem_T : k ∉ A ⊓ B
  sq_not_mem_T : k * k ∉ A ⊓ B
  mem_U : u ∈ conjClosure V B
  not_mem_Q : k * u * k⁻¹ ∉ pCoreOf 2 B

namespace Crit

variable (c : Crit A B z V)

@[expose] def z' : D := c.k * c.u * c.k⁻¹

end Crit

namespace GoldHyp3

variable (h : GoldHyp3 A B z V)

include h

theorem nonempty_crit (hb : ¬ 4 ≤ critDist (A ⊔ B) A B V) : Nonempty (Crit A B z V) := by
  rw [h.four_le_critDist_iff] at hb
  have hex : ∃ k₁ ∈ A, ∃ u ∈ conjClosure V B, k₁ * u * k₁⁻¹ ∉ pCoreOf 2 B := by
    by_contra hcon
    push Not at hcon
    exact hb (conjClosure_le fun k hk u hu => hcon k hk u hu)
  obtain ⟨k₁, hk₁, u₁, hu₁, hk₁u₁⟩ := hex
  obtain ⟨y, hyA, hy3⟩ := h.gold.vertex_left.exists_order_three
  have hyT := h.gold.vertex_left.not_mem_of_orderOf hy3
  have hy2T := h.gold.vertex_left.sq_not_mem_of_orderOf hy3
  have hy3' : y * y * y = 1 := by
    have := pow_orderOf_eq_one y
    rwa [hy3, pow_three'] at this
  have hTU : ∀ t ∈ A ⊓ B, ∀ w ∈ conjClosure V B, t * w * t⁻¹ ∈ conjClosure V B := fun t ht w hw =>
    (Subgroup.mem_normalizer_iff.mp (le_normalizer_conjClosure V B ht.2) w).mp hw
  rcases coset_decomp h.gold.relIndex_left hyA hyT hy2T hk₁ with hT | ⟨t, htT, rfl⟩ |
      ⟨t, htT, rfl⟩
  · exact absurd (h.conjClosure_le_pCoreOf_right (hTU k₁ hT u₁ hu₁)) hk₁u₁
  · refine ⟨⟨y, t * u₁ * t⁻¹, hyA, hy3', hyT, hy2T, hTU t htT u₁ hu₁, ?_⟩⟩
    have e : y * t * u₁ * (y * t)⁻¹ = y * (t * u₁ * t⁻¹) * y⁻¹ := by group
    rw [e] at hk₁u₁
    exact hk₁u₁
  · have hyy3 : (y * y) * (y * y) * (y * y) = 1 := by
      calc (y * y) * (y * y) * (y * y) = (y * y * y) * (y * y * y) := by group
        _ = 1 := by rw [hy3', one_mul]
    have hyyy : (y * y) * (y * y) = y := by
      calc (y * y) * (y * y) = (y * y * y) * y := by group
        _ = y := by rw [hy3', one_mul]
    refine ⟨⟨y * y, t * u₁ * t⁻¹, A.mul_mem hyA hyA, hyy3, hy2T, by rw [hyyy]; exact hyT,
      hTU t htT u₁ hu₁, ?_⟩⟩
    have e : y * y * t * u₁ * (y * y * t)⁻¹ = y * y * (t * u₁ * t⁻¹) * (y * y)⁻¹ := by group
    rw [e] at hk₁u₁
    exact hk₁u₁

end GoldHyp3

namespace Crit

variable (c : Crit A B z V) (h : GoldHyp3 A B z V)

include h

theorem z'_mem_QA : c.z' ∈ pCoreOf 2 A :=
  (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 A c.mem_A) c.u).mp
    (h.conjClosure_le_pCoreOf_left c.mem_U)

theorem z'_mem_T : c.z' ∈ A ⊓ B := h.gold.pCoreOf_left_le (c.z'_mem_QA h)

omit [Finite D] h in
theorem z'_not_mem_QB : c.z' ∉ pCoreOf 2 B := c.not_mem_Q

end Crit

namespace Crit

variable (cr : Crit A B z V) (g : Gens A B z V) (h : GoldHyp3 A B z V)

include h

theorem z'_swap (hU : Nat.card (conjClosure V B) = 16) :
    (cr.z' * g.a₂ * cr.z'⁻¹ = g.a₃ ∨ cr.z' * g.a₂ * cr.z'⁻¹ = z * g.a₃) ∧
      (cr.z' * g.a₃ * cr.z'⁻¹ = g.a₂ ∨ cr.z' * g.a₃ * cr.z'⁻¹ = z * g.a₂) := by
  rcases g.T_fix_or_swap h hU (cr.z'_mem_T h) with ⟨h2, h3⟩ | hs
  · exact absurd (g.mem_pCoreOf_of_fix h (cr.z'_mem_T h) h2 h3) (cr.z'_not_mem_QB)
  · exact hs

theorem a₂_conj_z'_mem : g.a₂ * cr.z' * g.a₂⁻¹ ∈ conjSub cr.k (conjClosure V B) := by
  rw [mem_conjSub]
  have hq : cr.k⁻¹ * g.a₂ * cr.k ∈ pCoreOf 2 A := by
    have := (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 A (A.inv_mem cr.mem_A))
      g.a₂).mp (h.conjClosure_le_pCoreOf_left (g.a₂_mem_U))
    simpa using this
  have hqT : cr.k⁻¹ * g.a₂ * cr.k ∈ A ⊓ B := h.gold.pCoreOf_left_le hq
  have e : cr.k⁻¹ * (g.a₂ * cr.z' * g.a₂⁻¹) * cr.k =
      (cr.k⁻¹ * g.a₂ * cr.k) * cr.u * (cr.k⁻¹ * g.a₂ * cr.k)⁻¹ := by
    unfold Crit.z'; group
  rw [e]
  exact T_conj_U hqT cr.mem_U

theorem c₂_mem_conjSub : g.a₂ * (cr.z' * g.a₂ * cr.z'⁻¹) ∈ conjSub cr.k (conjClosure V B) := by
  have h1 := cr.a₂_conj_z'_mem g h
  have h2 : cr.z'⁻¹ ∈ conjSub cr.k (conjClosure V B) :=
    Subgroup.inv_mem _ (mul_mem_conjSub cr.mem_U)
  have h3 := Subgroup.mul_mem _ h1 h2
  have hinv : g.a₂⁻¹ = g.a₂ := inv_eq_of_mul_eq_one_left (h.U_sq (g.a₂_mem_U))
  have e : g.a₂ * cr.z' * g.a₂⁻¹ * cr.z'⁻¹ = g.a₂ * (cr.z' * g.a₂ * cr.z'⁻¹) := by
    rw [hinv]; group
  rwa [e] at h3

omit [Finite D] in
theorem z_mem_conjSub : z ∈ conjSub cr.k (conjClosure V B) := by
  rw [mem_conjSub]
  have : cr.k⁻¹ * z * cr.k ∈ V := by
    have := (Subgroup.mem_normalizer_iff.mp (h.natural.reduced.2.1 (A.inv_mem cr.mem_A)) z).mp
      h.natural.z_mem_V
    simpa using this
  exact le_conjClosure V B this

theorem c₂₃_mem_conjSub (hU : Nat.card (conjClosure V B) = 16) :
    g.c₂₃ ∈ conjSub cr.k (conjClosure V B) := by
  have hc₂ := cr.c₂_mem_conjSub g h
  have hzk := cr.z_mem_conjSub h
  obtain ⟨hs2, -⟩ := cr.z'_swap g h hU
  rcases hs2 with e | e
  · rw [e] at hc₂
    exact hc₂
  · rw [e] at hc₂
    have hzz : z * z = 1 := by
      have := h.natural.z_sq
      rwa [pow_two] at this
    have hza : z * g.a₂ = g.a₂ * z := h.U_comm h.z_mem_U (g.a₂_mem_U)
    have e2 : g.a₂ * g.a₃ = z * (g.a₂ * (z * g.a₃)) := by
      calc g.a₂ * g.a₃ = (z * z) * (g.a₂ * g.a₃) := by rw [hzz, one_mul]
        _ = z * (z * g.a₂) * g.a₃ := by group
        _ = z * (g.a₂ * z) * g.a₃ := by rw [hza]
        _ = z * (g.a₂ * (z * g.a₃)) := by group
    show g.a₂ * g.a₃ ∈ _
    rw [e2]
    exact Subgroup.mul_mem _ hzk hc₂

theorem exists_swap : ∃ τ ∈ A ⊓ B, ∃ t' ∈ A ⊓ B, τ * cr.k = cr.k * cr.k * t' := by
  by_contra hcon
  push Not at hcon
  have hconj : ∀ τ ∈ A ⊓ B, cr.k⁻¹ * τ * cr.k ∈ A ⊓ B := by
    intro τ hτ
    have hτk : τ * cr.k ∈ A := A.mul_mem hτ.1 cr.mem_A
    rcases coset_decomp h.gold.relIndex_left cr.mem_A cr.not_mem_T cr.sq_not_mem_T hτk with
      hT | ⟨t', ht', e⟩ | ⟨t', ht', e⟩
    · exfalso
      apply cr.not_mem_T
      have : cr.k = τ⁻¹ * (τ * cr.k) := by group
      rw [this]
      exact (A ⊓ B).mul_mem ((A ⊓ B).inv_mem hτ) hT
    · have : cr.k⁻¹ * τ * cr.k = t' := by
        calc cr.k⁻¹ * τ * cr.k = cr.k⁻¹ * (τ * cr.k) := by group
          _ = cr.k⁻¹ * (cr.k * t') := by rw [e]
          _ = t' := by group
      rw [this]; exact ht'
    · exact absurd e (hcon τ hτ t' ht')
  have hle : A ⊓ B ≤ conjSub cr.k (A ⊓ B) := fun τ hτ => by
    rw [mem_conjSub]; exact hconj τ hτ
  have heq : A ⊓ B = conjSub cr.k (A ⊓ B) :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [card_conjSub])
  have hkN : cr.k ∈ Subgroup.normalizer ((A ⊓ B : Subgroup D) : Set D) :=
    mem_normalizer_of_conjSub_eq heq.symm
  have hAN : A ≤ Subgroup.normalizer ((A ⊓ B : Subgroup D) : Set D) := by
    intro a ha
    rcases coset_decomp h.gold.relIndex_left cr.mem_A cr.not_mem_T cr.sq_not_mem_T ha with
      hT | ⟨t, htT, rfl⟩ | ⟨t, htT, rfl⟩
    · exact Subgroup.le_normalizer hT
    · exact Subgroup.mul_mem _ hkN (Subgroup.le_normalizer htT)
    · exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hkN hkN) (Subgroup.le_normalizer htT)
  have hTQ : A ⊓ B ≤ pCoreOf 2 A :=
    le_pCoreOf_of_le_normalizer 2 inf_le_left hAN (h.gold.isSylowTwoOf_left.2.1.to_le le_rfl)
  have h1 : (pCoreOf 2 A).relIndex (A ⊓ B) = 1 := Subgroup.relIndex_eq_one.mpr hTQ
  have h2 := h.gold.relIndex_pCoreOf_T_left
  omega

theorem c₂₃_mem_conjSub_kk (hU : Nat.card (conjClosure V B) = 16) :
    g.c₂₃ ∈ conjSub (cr.k * cr.k) (conjClosure V B) := by
  obtain ⟨τ, hτ, t', ht', hτk⟩ := cr.exists_swap h
  have hk1 := cr.c₂₃_mem_conjSub g h hU
  have hzk := cr.z_mem_conjSub h
  have h1 : conjSub (cr.k * cr.k) (conjClosure V B) =
      conjSub τ (conjSub cr.k (conjClosure V B)) := by
    have e1 : conjSub t' (conjClosure V B) = conjClosure V B :=
      F7.conjSub_eq_of_mem_normalizer (le_normalizer_conjClosure V B ht'.2)
    calc conjSub (cr.k * cr.k) (conjClosure V B)
        = conjSub (cr.k * cr.k) (conjSub t' (conjClosure V B)) := by rw [e1]
      _ = conjSub (cr.k * cr.k * t') (conjClosure V B) := (conjSub_mul _ _ _).symm
      _ = conjSub (τ * cr.k) (conjClosure V B) := by rw [hτk]
      _ = conjSub τ (conjSub cr.k (conjClosure V B)) := conjSub_mul _ _ _
  rw [h1, mem_conjSub]
  have := g.T_conj_mul h hU ((A ⊓ B).inv_mem hτ)
  simp only [inv_inv] at this
  show τ⁻¹ * (g.a₂ * g.a₃) * τ ∈ _
  rcases this with e | e
  · rw [e]; exact hk1
  · rw [e]; exact Subgroup.mul_mem _ hzk hk1

end Crit

namespace Crit

omit [Finite D] in
theorem orderOf_k (cr : Crit A B z V) : orderOf cr.k = 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine orderOf_eq_prime ?_ ?_
  · rw [pow_three']; exact cr.cube
  · intro h1
    apply cr.not_mem_T
    rw [h1]
    exact (A ⊓ B).one_mem

theorem c₂₃_mem_core (cr : Crit A B z V) (g : Gens A B z V) (h : GoldHyp3 A B z V)
    (hU : Nat.card (conjClosure V B) = 16) : g.c₂₃ ∈ coreIn (conjClosure V B) A := by
  have hcU : g.c₂₃ ∈ conjClosure V B := g.c₂₃_mem_U
  have hk1 := cr.c₂₃_mem_conjSub g h hU
  have hk2 := cr.c₂₃_mem_conjSub_kk g h hU
  refine ⟨pCoreOf_le 2 A (h.conjClosure_le_pCoreOf_left hcU), fun a ha => ?_⟩
  rcases coset_decomp h.gold.relIndex_left cr.mem_A cr.not_mem_T cr.sq_not_mem_T ha with
    hT | ⟨t, htT, rfl⟩ | ⟨t, htT, rfl⟩
  · have := T_conj_U ((A ⊓ B).inv_mem hT) hcU
    simpa using this
  · rw [mem_conjSub] at hk1
    have := T_conj_U ((A ⊓ B).inv_mem htT) hk1
    have e : (cr.k * t)⁻¹ * g.c₂₃ * (cr.k * t) = t⁻¹ * (cr.k⁻¹ * g.c₂₃ * cr.k) * t⁻¹⁻¹ := by
      group
    rw [e]; exact this
  · rw [mem_conjSub] at hk2
    have := T_conj_U ((A ⊓ B).inv_mem htT) hk2
    have e : (cr.k * cr.k * t)⁻¹ * g.c₂₃ * (cr.k * cr.k * t) =
        t⁻¹ * ((cr.k * cr.k)⁻¹ * g.c₂₃ * (cr.k * cr.k)) * t⁻¹⁻¹ := by group
    rw [e]; exact this

theorem core_ne_U (cr : Crit A B z V) (h : GoldHyp3 A B z V) :
    coreIn (conjClosure V B) A ≠ conjClosure V B := by
  intro heq
  have hkN : cr.k ∈ Subgroup.normalizer
      ((coreIn (conjClosure V B) A : Subgroup D) : Set D) := le_normalizer_coreIn _ _ cr.mem_A
  rw [heq] at hkN
  exact h.not_mem_normalizer_conjClosure cr.mem_A (cr.orderOf_k) hkN

theorem card_core (cr : Crit A B z V) (g : Gens A B z V) (h : GoldHyp3 A B z V)
    (hU : Nat.card (conjClosure V B) = 16) :
    Nat.card ↥(coreIn (conjClosure V B) A) = 8 := by
  have hIU : coreIn (conjClosure V B) A ≤ conjClosure V B := coreIn_le_right _ _
  have hne := cr.core_ne_U h
  have hlt : Nat.card ↥(coreIn (conjClosure V B) A) < Nat.card ↥(conjClosure V B) :=
    lt_of_le_of_ne (Subgroup.card_le_of_le hIU) fun heq =>
      hne (Subgroup.eq_of_le_of_card_ge hIU (le_of_eq heq.symm))
  have hdvd := Subgroup.card_dvd_of_le hIU
  rw [hU] at hlt hdvd
  have hVI : V ≤ coreIn (conjClosure V B) A := h.V_le_core
  have hV4 : Nat.card V = 4 := h.natural.card_eq
  have hVdvd := Subgroup.card_dvd_of_le hVI
  rw [hV4] at hVdvd
  have hcI := cr.c₂₃_mem_core g h hU
  have hcV := g.a₂_mul_a₃_not_mem_V h hU
  have hgt : 4 < Nat.card ↥(coreIn (conjClosure V B) A) := by
    by_contra hcon
    push Not at hcon
    have heq := Subgroup.eq_of_le_of_card_ge hVI (by rw [hV4]; exact hcon)
    rw [← heq] at hcI
    exact hcV hcI
  have h16 : Nat.card ↥(coreIn (conjClosure V B) A) ≤ 16 := by omega
  generalize Nat.card ↥(coreIn (conjClosure V B) A) = n at *
  interval_cases n <;> omega

end Crit

namespace Crit

theorem a_conj_c₂₃_mem (cr : Crit A B z V) (g : Gens A B z V) (h : GoldHyp3 A B z V)
    (hU : Nat.card (conjClosure V B) = 16) {a : D} (ha : a ∈ A) :
    a * g.c₂₃ * a⁻¹ * g.c₂₃⁻¹ ∈ V := by
  have hcI : g.c₂₃ ∈ coreIn (conjClosure V B) A := cr.c₂₃_mem_core g h hU
  have hxI : a * g.c₂₃ * a⁻¹ ∈ coreIn (conjClosure V B) A :=
    (Subgroup.mem_normalizer_iff.mp (le_normalizer_coreIn _ _ ha) _).mp hcI
  have hcV : g.c₂₃ ∉ V := g.a₂_mul_a₃_not_mem_V h hU
  have hxV : a * g.c₂₃ * a⁻¹ ∉ V := by
    intro hx
    apply hcV
    have := (Subgroup.mem_normalizer_iff.mp (h.natural.reduced.2.1 (A.inv_mem ha)) _).mp hx
    simpa [mul_assoc] using this
  have hVI : V ≤ coreIn (conjClosure V B) A := h.V_le_core
  have hrel : V.relIndex (coreIn (conjClosure V B) A) = 2 := by
    have := Subgroup.relIndex_mul_card V (coreIn (conjClosure V B) A)
    rw [inf_eq_left.mpr hVI, cr.card_core g h hU, h.natural.card_eq] at this
    omega
  exact mul_inv_mem_of_relIndex_two hrel hxI hcI hxV hcV

end Crit

namespace Crit

theorem q_conj_c₂₃ (cr : Crit A B z V) (g : Gens A B z V) (h : GoldHyp3 A B z V)
    (hU : Nat.card (conjClosure V B) = 16) {q : D} (hq : q ∈ pCoreOf 2 A) :
    q * g.c₂₃ * q⁻¹ = g.c₂₃ := by
  have hqT : q ∈ A ⊓ B := h.gold.pCoreOf_left_le hq
  rcases g.T_conj_c₂₃ h hU hqT with e | e
  · exact e
  · exfalso
    apply h.natural.not_normalizes
    intro a ha
    apply mem_normalizer_zpowers_of_mul_comm
    have hcU : g.c₂₃ ∈ conjClosure V B := g.c₂₃_mem_U
    have hzc : z * g.c₂₃ = g.c₂₃ * z := h.U_comm h.z_mem_U hcU
    have hq' : a * q * a⁻¹ ∈ pCoreOf 2 A :=
      (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 A ha) q).mp hq
    have hq'T : a * q * a⁻¹ ∈ A ⊓ B := h.gold.pCoreOf_left_le hq'
    have hv' : a⁻¹ * g.c₂₃ * a * g.c₂₃⁻¹ ∈ V := by
      have := cr.a_conj_c₂₃_mem g h hU (A.inv_mem ha)
      simpa [mul_assoc] using this
    have hqv' : q * (a⁻¹ * g.c₂₃ * a * g.c₂₃⁻¹) * q⁻¹ = a⁻¹ * g.c₂₃ * a * g.c₂₃⁻¹ := by
      have := Subgroup.mem_centralizer_iff.mp (h.natural.le_center hv').2 q hq
      calc q * (a⁻¹ * g.c₂₃ * a * g.c₂₃⁻¹) * q⁻¹
          = (a⁻¹ * g.c₂₃ * a * g.c₂₃⁻¹) * q * q⁻¹ := by rw [this]
        _ = a⁻¹ * g.c₂₃ * a * g.c₂₃⁻¹ := by group
    have hcz : g.c₂₃⁻¹ * z * g.c₂₃ = z := by
      calc g.c₂₃⁻¹ * z * g.c₂₃ = g.c₂₃⁻¹ * (z * g.c₂₃) := by group
        _ = g.c₂₃⁻¹ * (g.c₂₃ * z) := by rw [hzc]
        _ = z := by group
    have hqy : q * (a⁻¹ * g.c₂₃ * a) * q⁻¹ = (a⁻¹ * g.c₂₃ * a) * z := by
      have h1 : q * (a⁻¹ * g.c₂₃ * a) * q⁻¹ =
          (q * (a⁻¹ * g.c₂₃ * a * g.c₂₃⁻¹) * q⁻¹) * (q * g.c₂₃ * q⁻¹) := by group
      rw [h1, hqv', e]
      calc a⁻¹ * g.c₂₃ * a * g.c₂₃⁻¹ * (z * g.c₂₃)
          = a⁻¹ * g.c₂₃ * a * (g.c₂₃⁻¹ * z * g.c₂₃) := by group
        _ = a⁻¹ * g.c₂₃ * a * z := by rw [hcz]
    have h2 : (a * q * a⁻¹) * g.c₂₃ * (a * q * a⁻¹)⁻¹ = g.c₂₃ * (a * z * a⁻¹) := by
      calc (a * q * a⁻¹) * g.c₂₃ * (a * q * a⁻¹)⁻¹
          = a * (q * (a⁻¹ * g.c₂₃ * a) * q⁻¹) * a⁻¹ := by group
        _ = a * ((a⁻¹ * g.c₂₃ * a) * z) * a⁻¹ := by rw [hqy]
        _ = g.c₂₃ * (a * z * a⁻¹) := by group
    rcases g.T_conj_c₂₃ h hU hq'T with e3 | e3
    · rw [h2] at e3
      have h3 : a * z * a⁻¹ = 1 := by
        have : g.c₂₃ * (a * z * a⁻¹) = g.c₂₃ * 1 := by rw [e3, mul_one]
        exact mul_left_cancel this
      exfalso
      apply h.natural.z_ne
      have : z = a⁻¹ * (a * z * a⁻¹) * a := by group
      rw [this, h3]; group
    · rw [h2] at e3
      have h3 : a * z * a⁻¹ = z := by
        calc a * z * a⁻¹ = g.c₂₃⁻¹ * (g.c₂₃ * (a * z * a⁻¹)) := by group
          _ = g.c₂₃⁻¹ * (z * g.c₂₃) := by rw [e3]
          _ = z := by rw [← mul_assoc, hcz]
      exact mul_eq_of_conj_eq h3

end Crit

end GoldAmL3

end F6

end CFSG.Quasithin
