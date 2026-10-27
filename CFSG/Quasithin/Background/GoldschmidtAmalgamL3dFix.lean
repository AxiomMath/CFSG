module

public import CFSG.Quasithin.Background.GoldschmidtAmalgamL3dCrit

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.F7
  CFSG.Quasithin.CosetGeom CFSG.Quasithin.F6.GoldAmL

namespace F6

namespace GoldAmL3

variable {D : Type*} [Group D] [Finite D] {A B : Subgroup D} {z : D} {V : Subgroup D}

namespace Crit

theorem exists_T_fixed (cr : Crit A B z V) (g : Gens A B z V) (h : GoldHyp3 A B z V)
    (hU : Nat.card (conjClosure V B) = 16) :
    ∃ ω : D, (ω = g.c₂₃ ∨ ω = g.c₂₃ * g.a) ∧ ∀ t ∈ A ⊓ B, t * ω * t⁻¹ = ω := by
  by_cases hcase : ∃ τ ∈ A ⊓ B, τ ∉ pCoreOf 2 A ∧ τ * g.c₂₃ * τ⁻¹ = g.c₂₃
  · obtain ⟨τ, hτ, hτQ, hτc⟩ := hcase
    refine ⟨g.c₂₃, Or.inl rfl, fun t ht => ?_⟩
    by_cases htQ : t ∈ pCoreOf 2 A
    · exact cr.q_conj_c₂₃ g h hU htQ
    · have h1 : t * τ⁻¹ ∈ pCoreOf 2 A :=
        mul_inv_mem_of_relIndex_two h.gold.relIndex_pCoreOf_T_left ht hτ htQ hτQ
      calc t * g.c₂₃ * t⁻¹ = (t * τ⁻¹) * (τ * g.c₂₃ * τ⁻¹) * (t * τ⁻¹)⁻¹ := by group
        _ = (t * τ⁻¹) * g.c₂₃ * (t * τ⁻¹)⁻¹ := by rw [hτc]
        _ = g.c₂₃ := cr.q_conj_c₂₃ g h hU h1
  · push Not at hcase
    refine ⟨g.c₂₃ * g.a, Or.inr rfl, fun t ht => ?_⟩
    have hprod : t * (g.c₂₃ * g.a) * t⁻¹ = (t * g.c₂₃ * t⁻¹) * (t * g.a * t⁻¹) := by group
    rw [hprod]
    by_cases htQ : t ∈ pCoreOf 2 A
    · have hta : t * g.a * t⁻¹ = g.a := by
        have := Subgroup.mem_centralizer_iff.mp (h.natural.le_center g.mem_V).2 t htQ
        calc t * g.a * t⁻¹ = g.a * t * t⁻¹ := by rw [this]
          _ = g.a := by group
      rw [hta, cr.q_conj_c₂₃ g h hU htQ]
    · have hne := hcase t ht htQ
      have hzc : t * g.c₂₃ * t⁻¹ = z * g.c₂₃ := by
        rcases g.T_conj_c₂₃ h hU ht with e | e
        · exact absurd e hne
        · exact e
      rw [hzc, g.T_conj_a_of_not_mem h ht htQ]
      exact h.z_mul_mul_z_mul (g.c₂₃_mem_U)

end Crit

namespace Crit

theorem exists_A_fixed (g : Gens A B z V) (h : GoldHyp3 A B z V) {ω : D}
    (hωU : ω ∈ conjClosure V B) (hωT : ∀ t ∈ A ⊓ B, t * ω * t⁻¹ = ω)
    (hωA : ∀ a ∈ A, a * ω * a⁻¹ * ω⁻¹ ∈ V) :
    ∃ ε : D, (ε = ω ∨ ε = ω * z) ∧ ∀ a ∈ A, a * ε * a⁻¹ = ε := by
  obtain ⟨y, hyA, hy3⟩ := h.gold.vertex_left.exists_order_three
  have hyT := h.gold.vertex_left.not_mem_of_orderOf hy3
  have hy2T := h.gold.vertex_left.sq_not_mem_of_orderOf hy3
  have hy3' : y * y * y = 1 := by
    have := pow_orderOf_eq_one y
    rwa [hy3, pow_three'] at this
  have hyyA : y * y ∈ A := A.mul_mem hyA hyA
  have hyyT : y * y ∉ A ⊓ B := hy2T
  have key : ∀ ε : D, (∀ t ∈ A ⊓ B, t * ε * t⁻¹ = ε) → y * ε * y⁻¹ = ε →
      ∀ a ∈ A, a * ε * a⁻¹ = ε := by
    intro ε hεT hεy a ha
    rcases coset_decomp h.gold.relIndex_left hyA hyT hy2T ha with
      hT | ⟨t, htT, rfl⟩ | ⟨t, htT, rfl⟩
    · exact hεT a hT
    · calc y * t * ε * (y * t)⁻¹ = y * (t * ε * t⁻¹) * y⁻¹ := by group
        _ = ε := by rw [hεT t htT, hεy]
    · calc y * y * t * ε * (y * y * t)⁻¹ = y * (y * (t * ε * t⁻¹) * y⁻¹) * y⁻¹ := by group
        _ = ε := by rw [hεT t htT, hεy, hεy]
  by_cases hy : y * ω * y⁻¹ = ω
  · exact ⟨ω, Or.inl rfl, key ω hωT hy⟩
  have hω1A := hωA y hyA
  have hω2A := hωA (y * y) hyyA
  obtain ⟨ω₁, hω₁⟩ : ∃ ω₁, ω₁ = y * ω * y⁻¹ := ⟨_, rfl⟩
  obtain ⟨ω₂, hω₂⟩ : ∃ ω₂, ω₂ = y * y * ω * (y * y)⁻¹ := ⟨_, rfl⟩
  have hω₁U : ω₁ ∈ conjClosure V B := by
    have : ω₁ = (y * ω * y⁻¹ * ω⁻¹) * ω := by rw [hω₁]; group
    rw [this]; exact Subgroup.mul_mem _ (le_conjClosure V B hω1A) hωU
  have hω₂U : ω₂ ∈ conjClosure V B := by
    have : ω₂ = (y * y * ω * (y * y)⁻¹ * ω⁻¹) * ω := by rw [hω₂]; group
    rw [this]; exact Subgroup.mul_mem _ (le_conjClosure V B hω2A) hωU
  have hc01 : ω * ω₁ = ω₁ * ω := h.U_comm hωU hω₁U
  have hc02 : ω * ω₂ = ω₂ * ω := h.U_comm hωU hω₂U
  have hc12 : ω₁ * ω₂ = ω₂ * ω₁ := h.U_comm hω₁U hω₂U
  have hωsq : ω * ω = 1 := h.U_sq hωU
  have hyω₁ : y * ω₁ * y⁻¹ = ω₂ := by rw [hω₁, hω₂]; group
  have hyω₂ : y * ω₂ * y⁻¹ = ω := by
    calc y * ω₂ * y⁻¹ = (y * y * y) * ω * (y * y * y)⁻¹ := by rw [hω₂]; group
      _ = ω := by rw [hy3']; group
  have hne12 : ω₁ ≠ ω₂ := by
    intro heq
    apply hy
    have h1 : y⁻¹ * ω₁ * y = y⁻¹ * ω₂ * y := by rw [heq]
    have e1 : y⁻¹ * ω₁ * y = ω := by rw [hω₁]; group
    have e2 : y⁻¹ * ω₂ * y = ω₁ := by rw [hω₂, hω₁]; group
    rw [e1, e2] at h1
    rw [← hω₁]
    exact h1.symm
  have hT₁ : ∀ t ∈ A ⊓ B, t * ω₁ * t⁻¹ = ω₁ ∨ t * ω₁ * t⁻¹ = ω₂ := by
    intro t ht
    have htyA : t * y ∈ A := A.mul_mem ht.1 hyA
    rcases coset_decomp h.gold.relIndex_left hyA hyT hy2T htyA with
      hT | ⟨t', ht', e⟩ | ⟨t', ht', e⟩
    · exfalso
      apply hyT
      have : y = t⁻¹ * (t * y) := by group
      rw [this]
      exact (A ⊓ B).mul_mem ((A ⊓ B).inv_mem ht) hT
    · left
      calc t * ω₁ * t⁻¹ = (t * y) * ω * (t * y)⁻¹ := by rw [hω₁]; group
        _ = (y * t') * ω * (y * t')⁻¹ := by rw [e]
        _ = y * (t' * ω * t'⁻¹) * y⁻¹ := by group
        _ = ω₁ := by rw [hωT t' ht', hω₁]
    · right
      calc t * ω₁ * t⁻¹ = (t * y) * ω * (t * y)⁻¹ := by rw [hω₁]; group
        _ = (y * y * t') * ω * (y * y * t')⁻¹ := by rw [e]
        _ = y * y * (t' * ω * t'⁻¹) * (y * y)⁻¹ := by group
        _ = ω₂ := by rw [hωT t' ht', hω₂]
  have hT₂ : ∀ t ∈ A ⊓ B, t * ω₂ * t⁻¹ = ω₁ ∨ t * ω₂ * t⁻¹ = ω₂ := by
    intro t ht
    have htyA : t * (y * y) ∈ A := A.mul_mem ht.1 hyyA
    rcases coset_decomp h.gold.relIndex_left hyA hyT hy2T htyA with
      hT | ⟨t', ht', e⟩ | ⟨t', ht', e⟩
    · exfalso
      apply hyyT
      have : y * y = t⁻¹ * (t * (y * y)) := by group
      rw [this]
      exact (A ⊓ B).mul_mem ((A ⊓ B).inv_mem ht) hT
    · left
      calc t * ω₂ * t⁻¹ = (t * (y * y)) * ω * (t * (y * y))⁻¹ := by rw [hω₂]; group
        _ = (y * t') * ω * (y * t')⁻¹ := by rw [e]
        _ = y * (t' * ω * t'⁻¹) * y⁻¹ := by group
        _ = ω₁ := by rw [hωT t' ht', hω₁]
    · right
      calc t * ω₂ * t⁻¹ = (t * (y * y)) * ω * (t * (y * y))⁻¹ := by rw [hω₂]; group
        _ = (y * y * t') * ω * (y * y * t')⁻¹ := by rw [e]
        _ = y * y * (t' * ω * t'⁻¹) * (y * y)⁻¹ := by group
        _ = ω₂ := by rw [hωT t' ht', hω₂]
  have hne : ∀ t ∈ A ⊓ B, t * ω₁ * t⁻¹ ≠ t * ω₂ * t⁻¹ := by
    intro t _ heq
    apply hne12
    have := congrArg (fun w => t⁻¹ * w * t) heq
    simpa [mul_assoc] using this
  have hεT : ∀ t ∈ A ⊓ B, t * (ω * ω₁ * ω₂) * t⁻¹ = ω * ω₁ * ω₂ := by
    intro t ht
    have hprod : t * (ω * ω₁ * ω₂) * t⁻¹ =
        (t * ω * t⁻¹) * (t * ω₁ * t⁻¹) * (t * ω₂ * t⁻¹) := by group
    rw [hprod, hωT t ht]
    rcases hT₁ t ht with e1 | e1 <;> rcases hT₂ t ht with e2 | e2
    · exact absurd (e1.trans e2.symm) (hne t ht)
    · rw [e1, e2]
    · rw [e1, e2]
      calc ω * ω₂ * ω₁ = ω * (ω₂ * ω₁) := by group
        _ = ω * (ω₁ * ω₂) := by rw [hc12]
        _ = ω * ω₁ * ω₂ := by group
    · exact absurd (e1.trans e2.symm) (hne t ht)
  have hεy : y * (ω * ω₁ * ω₂) * y⁻¹ = ω * ω₁ * ω₂ := by
    have hprod : y * (ω * ω₁ * ω₂) * y⁻¹ = (y * ω * y⁻¹) * (y * ω₁ * y⁻¹) * (y * ω₂ * y⁻¹) := by
      group
    rw [hprod, hyω₁, hyω₂, ← hω₁]
    calc ω₁ * ω₂ * ω = ω₁ * (ω₂ * ω) := by group
      _ = ω₁ * (ω * ω₂) := by rw [hc02]
      _ = (ω₁ * ω) * ω₂ := by group
      _ = (ω * ω₁) * ω₂ := by rw [hc01]
  have hεA := key _ hεT hεy
  refine ⟨ω * ω₁ * ω₂, ?_, hεA⟩
  have hv₁ : ω₁ * ω⁻¹ ∈ V := by rw [hω₁]; exact hω1A
  have hv₂ : ω₂ * ω⁻¹ ∈ V := by rw [hω₂]; exact hω2A
  have hinv : ω⁻¹ = ω := inv_eq_of_mul_eq_one_left hωsq
  have hcomm12 : ω * (ω₁ * ω₂) = (ω₁ * ω₂) * ω := by
    calc ω * (ω₁ * ω₂) = (ω * ω₁) * ω₂ := by group
      _ = (ω₁ * ω) * ω₂ := by rw [hc01]
      _ = ω₁ * (ω * ω₂) := by group
      _ = ω₁ * (ω₂ * ω) := by rw [hc02]
      _ = (ω₁ * ω₂) * ω := by group
  have hv : (ω * ω₁ * ω₂) * ω⁻¹ ∈ V := by
    have e : (ω * ω₁ * ω₂) * ω⁻¹ = (ω₁ * ω⁻¹) * (ω₂ * ω⁻¹) := by
      have e1 : (ω * ω₁ * ω₂) * ω⁻¹ = ω₁ * ω₂ := by
        calc (ω * ω₁ * ω₂) * ω⁻¹ = ω * (ω₁ * ω₂) * ω := by rw [hinv]; group
          _ = (ω₁ * ω₂) * ω * ω := by rw [hcomm12]
          _ = (ω₁ * ω₂) * (ω * ω) := by group
          _ = ω₁ * ω₂ := by rw [hωsq, mul_one]
      have e2 : (ω₁ * ω⁻¹) * (ω₂ * ω⁻¹) = ω₁ * ω₂ := by
        calc (ω₁ * ω⁻¹) * (ω₂ * ω⁻¹) = ω₁ * (ω * ω₂) * ω := by rw [hinv]; group
          _ = ω₁ * (ω₂ * ω) * ω := by rw [hc02]
          _ = ω₁ * ω₂ * (ω * ω) := by group
          _ = ω₁ * ω₂ := by rw [hωsq, mul_one]
      rw [e1, e2]
    rw [e]; exact V.mul_mem hv₁ hv₂
  have hvT : ∀ t ∈ A ⊓ B, t * ((ω * ω₁ * ω₂) * ω⁻¹) * t⁻¹ = (ω * ω₁ * ω₂) * ω⁻¹ := by
    intro t ht
    have : t * ((ω * ω₁ * ω₂) * ω⁻¹) * t⁻¹ =
        (t * (ω * ω₁ * ω₂) * t⁻¹) * (t * ω * t⁻¹)⁻¹ := by group
    rw [this, hεT t ht, hωT t ht]
  obtain ⟨τ, hτ, hτQ⟩ := h.exists_T_not_mem_QA
  have hτa := g.T_conj_a_of_not_mem h hτ hτQ
  have hεv : ω * ω₁ * ω₂ = ((ω * ω₁ * ω₂) * ω⁻¹) * ω := by group
  have hvmem : (ω * ω₁ * ω₂) * ω⁻¹ ∈ (V : Set D) := hv
  rw [g.V_eq] at hvmem
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hvmem
  rcases hvmem with e | e | e | e
  · left
    rw [hεv, e, one_mul]
  · right
    rw [hεv, e]
    exact h.U_comm h.z_mem_U hωU
  · exfalso
    have h1 := hvT τ hτ
    rw [e, hτa] at h1
    have : z * g.a = 1 * g.a := by rw [one_mul]; exact h1
    exact h.natural.z_ne (mul_right_cancel this)
  · exfalso
    have h1 := hvT τ hτ
    rw [e] at h1
    have e1 : τ * (z * g.a) * τ⁻¹ = (τ * z * τ⁻¹) * (τ * g.a * τ⁻¹) := by group
    rw [e1, h.T_conj_z hτ, hτa] at h1
    have : z * (z * g.a) = 1 * (z * g.a) := by rw [one_mul]; exact h1
    exact h.natural.z_ne (mul_right_cancel this)

end Crit

namespace Crit

theorem false_of_B_fixed (g : Gens A B z V) (h : GoldHyp3 A B z V) {ω : D}
    (hωU : ω ∈ conjClosure V B) (hωV : ω ∉ V) (hωT : ∀ t ∈ A ⊓ B, t * ω * t⁻¹ = ω)
    (hωA : ∀ a ∈ A, a * ω * a⁻¹ * ω⁻¹ ∈ V) (hωB : ∀ b ∈ B, b * ω * b⁻¹ = ω) : False := by
  obtain ⟨ε, hε, hεA⟩ := exists_A_fixed g h hωU hωT hωA
  have hεB : ∀ b ∈ B, b * ε * b⁻¹ = ε := by
    intro b hb
    rcases hε with rfl | rfl
    · exact hωB b hb
    · have hbz : b * z * b⁻¹ = z := h.central b hb
      calc b * (ω * z) * b⁻¹ = (b * ω * b⁻¹) * (b * z * b⁻¹) := by group
        _ = ω * z := by rw [hωB b hb, hbz]
  have hεU : ε ∈ conjClosure V B := by
    rcases hε with rfl | rfl
    · exact hωU
    · exact Subgroup.mul_mem _ hωU h.z_mem_U
  have hN : Subgroup.zpowers ε ≤ A ⊓ B := by
    refine Subgroup.zpowers_le.mpr ?_
    exact h.gold.pCoreOf_left_le (h.conjClosure_le_pCoreOf_left hεU)
  have hAN : A ≤ Subgroup.normalizer (Subgroup.zpowers ε : Set D) := fun a ha =>
    mem_normalizer_zpowers_of_mul_comm (mul_eq_of_conj_eq (hεA a ha))
  have hBN : B ≤ Subgroup.normalizer (Subgroup.zpowers ε : Set D) := fun b hb =>
    mem_normalizer_zpowers_of_mul_comm (mul_eq_of_conj_eq (hεB b hb))
  have hbot := h.gold.eq_bot_of_normalizes hAN hBN hN
  have hε1 : ε = 1 := by
    have : ε ∈ Subgroup.zpowers ε := Subgroup.mem_zpowers ε
    rw [hbot] at this
    exact Subgroup.mem_bot.mp this
  apply hωV
  rcases hε with rfl | rfl
  · rw [hε1]; exact V.one_mem
  · have : ω = z⁻¹ := by
      have h2 : ω * z = 1 := hε1
      exact eq_inv_of_mul_eq_one_left h2
    rw [this]
    exact V.inv_mem h.natural.z_mem_V

end Crit

namespace Crit

theorem T_fixed_c₂₃ (cr : Crit A B z V) (g : Gens A B z V) (h : GoldHyp3 A B z V)
    (hU : Nat.card (conjClosure V B) = 16) : ∀ t ∈ A ⊓ B, t * g.c₂₃ * t⁻¹ = g.c₂₃ := by
  obtain ⟨ω, hω, hωT⟩ := cr.exists_T_fixed g h hU
  rcases hω with rfl | rfl
  · exact hωT
  · exfalso
    have hcU := g.c₂₃_mem_U
    have hωU : g.c₂₃ * g.a ∈ conjClosure V B := Subgroup.mul_mem _ hcU (g.a_mem_U)
    have hωV : g.c₂₃ * g.a ∉ V := by
      intro hmem
      apply g.a₂_mul_a₃_not_mem_V h hU
      have : g.c₂₃ = (g.c₂₃ * g.a) * g.a⁻¹ := by group
      show g.c₂₃ ∈ V
      rw [this]
      exact V.mul_mem hmem (V.inv_mem g.mem_V)
    have hωA : ∀ a ∈ A, a * (g.c₂₃ * g.a) * a⁻¹ * (g.c₂₃ * g.a)⁻¹ ∈ V := by
      intro a' ha'
      have hp := cr.a_conj_c₂₃_mem g h hU ha'
      have hq : a' * g.a * a'⁻¹ * g.a⁻¹ ∈ V := by
        have h1 : a' * g.a * a'⁻¹ ∈ V :=
          (Subgroup.mem_normalizer_iff.mp (h.natural.reduced.2.1 ha') g.a).mp g.mem_V
        exact V.mul_mem h1 (V.inv_mem g.mem_V)
      have e : a' * (g.c₂₃ * g.a) * a'⁻¹ * (g.c₂₃ * g.a)⁻¹ =
          (a' * g.c₂₃ * a'⁻¹ * g.c₂₃⁻¹) * (g.c₂₃ * (a' * g.a * a'⁻¹ * g.a⁻¹) * g.c₂₃⁻¹) := by
        group
      rw [e]
      have hcomm : g.c₂₃ * (a' * g.a * a'⁻¹ * g.a⁻¹) * g.c₂₃⁻¹ = a' * g.a * a'⁻¹ * g.a⁻¹ := by
        have := h.U_comm hcU (le_conjClosure V B hq)
        calc g.c₂₃ * (a' * g.a * a'⁻¹ * g.a⁻¹) * g.c₂₃⁻¹
            = (a' * g.a * a'⁻¹ * g.a⁻¹) * g.c₂₃ * g.c₂₃⁻¹ := by rw [this]
          _ = a' * g.a * a'⁻¹ * g.a⁻¹ := by group
      rw [hcomm]
      exact V.mul_mem hp hq
    have hωB : ∀ b ∈ B, b * (g.c₂₃ * g.a) * b⁻¹ = g.c₂₃ * g.a :=
      g.B_fixed_of h hωT (g.x_conj_c₂₃_mul_a h)
    exact Crit.false_of_B_fixed g h hωU hωV hωT hωA hωB

end Crit

end GoldAmL3

end F6

end CFSG.Quasithin
