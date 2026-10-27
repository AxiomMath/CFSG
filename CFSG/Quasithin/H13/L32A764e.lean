module

public import CFSG.Quasithin.H13.L32A764d
public import CFSG.Quasithin.H13.L32A770k

public section

namespace CFSG.Quasithin.H13.L32A

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.RuType
open CFSG.Quasithin.CosetGeom
open scoped MatrixGroups commutatorElement

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G}

namespace Ctx764

variable (C : Ctx764 G T L V)
include C

theorem R1_le_normalizer_Q :
    pCoreOf 2 (L₁Of L (fsuV1 T V) ⊔ T) ≤ Subgroup.normalizer (pCoreOf 2 (hz T V) : Set G) :=
  C.R1_le_H.trans (le_normalizer_pCoreOf 2 _)

theorem card_quot_R1 : Nat.card (↥(pCoreOf 2 (L₁Of L (fsuV1 T V) ⊔ T)) ⧸
    (pCoreOf 2 (hz T V)).subgroupOf (pCoreOf 2 (L₁Of L (fsuV1 T V) ⊔ T))) = 4 := by
  have S0 : Setting147 G T L V (hz T V) := ⟨C.hyp, C.hyp.isHzOne_hz C.h63⟩
  obtain ⟨-, hR4⟩ := R1_le_kz_sup S0 C.hF C.h63 C.h1222 C.h1332 C.h1334
  rw [← Subgroup.index_eq_card]
  exact hR4

theorem exists_other {s : G} (hs : s ∈ pCoreOf 2 (L₁Of L (fsuV1 T V) ⊔ T)) :
    ∃ r ∈ pCoreOf 2 (L₁Of L (fsuV1 T V) ⊔ T), r ∉ pCoreOf 2 (hz T V) ∧
      s⁻¹ * r ∉ pCoreOf 2 (hz T V) := by
  set R := pCoreOf 2 (L₁Of L (fsuV1 T V) ⊔ T) with hR
  set Q := pCoreOf 2 (hz T V) with hQ
  have hQn : (Q.subgroupOf R).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer C.R1_le_normalizer_Q
  have hcard := C.card_quot_R1
  by_contra hno
  push Not at hno
  let f : Bool → ↥R ⧸ Q.subgroupOf R := fun b =>
    if b then QuotientGroup.mk ⟨s, hs⟩ else 1
  have hf : Function.Surjective f := by
    intro x
    obtain ⟨r, rfl⟩ := QuotientGroup.mk_surjective x
    by_cases hr : (r : G) ∈ Q
    · refine ⟨false, ?_⟩
      show (1 : ↥R ⧸ Q.subgroupOf R) = QuotientGroup.mk r
      rw [eq_comm, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
      exact hr
    · refine ⟨true, ?_⟩
      show QuotientGroup.mk ⟨s, hs⟩ = (QuotientGroup.mk r : ↥R ⧸ Q.subgroupOf R)
      rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
      simpa using hno r r.2 hr
  have hle := Nat.card_le_card_of_surjective f hf
  rw [hcard, Nat.card_eq_fintype_card, Fintype.card_bool] at hle
  omega

theorem mem_cosets {s₁ s₂ : G} (hs₁ : s₁ ∈ pCoreOf 2 (L₁Of L (fsuV1 T V) ⊔ T))
    (hs₁Q : s₁ ∉ pCoreOf 2 (hz T V)) (hs₂ : s₂ ∈ pCoreOf 2 (L₁Of L (fsuV1 T V) ⊔ T))
    (hs₂Q : s₂ ∉ pCoreOf 2 (hz T V)) (h12 : s₁⁻¹ * s₂ ∉ pCoreOf 2 (hz T V)) {r : G}
    (hr : r ∈ pCoreOf 2 (L₁Of L (fsuV1 T V) ⊔ T)) :
    r ∈ pCoreOf 2 (hz T V) ∨ s₁⁻¹ * r ∈ pCoreOf 2 (hz T V) ∨ s₂⁻¹ * r ∈ pCoreOf 2 (hz T V) ∨
      (s₁ * s₂)⁻¹ * r ∈ pCoreOf 2 (hz T V) := by
  classical
  set R := pCoreOf 2 (L₁Of L (fsuV1 T V) ⊔ T) with hR
  set Q := pCoreOf 2 (hz T V) with hQ
  have hQn : (Q.subgroupOf R).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer C.R1_le_normalizer_Q
  have hcard := C.card_quot_R1
  have : Fintype (↥R ⧸ Q.subgroupOf R) := Fintype.ofFinite _
  set π := QuotientGroup.mk' (Q.subgroupOf R) with hπ
  have hπeq : ∀ a b : ↥R, π a = π b ↔ (a : G)⁻¹ * b ∈ Q := fun a b => by
    rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq,
      Subgroup.mem_subgroupOf]
    simp
  have hπ1 : ∀ a : ↥R, π a = 1 ↔ (a : G) ∈ Q := fun a => by
    rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
  set a := π ⟨s₁, hs₁⟩
  set b := π ⟨s₂, hs₂⟩
  have hsq : ∀ x : ↥R ⧸ Q.subgroupOf R, x * x = 1 := by
    intro x
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (Q.subgroupOf R) x
    rw [← map_mul, hπ1]
    exact C.sq_mem_Q y.2
  have ha1 : a ≠ 1 := fun h => hs₁Q ((hπ1 _).mp h)
  have hb1 : b ≠ 1 := fun h => hs₂Q ((hπ1 _).mp h)
  have hab : a ≠ b := fun h => h12 ((hπeq _ _).mp h)
  have hab1 : a * b ≠ 1 := by
    intro h
    apply hab
    calc a = a * (b * b) := by rw [hsq b, mul_one]
      _ = (a * b) * b := by rw [mul_assoc]
      _ = b := by rw [h, one_mul]
  have haba : a * b ≠ a := fun h => hb1 (by simpa using h)
  have habb : a * b ≠ b := fun h => ha1 (by simpa using h)
  have huniv : ({1, a, b, a * b} : Finset (↥R ⧸ Q.subgroupOf R)) = Finset.univ := by
    apply Finset.eq_univ_of_card
    rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_pair habb.symm,
      ← Nat.card_eq_fintype_card, hcard]
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨hab, fun e => haba e.symm⟩
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨fun e => ha1 e.symm, fun e => hb1 e.symm, fun e => hab1 e.symm⟩
  have hmem : π ⟨r, hr⟩ ∈ ({1, a, b, a * b} : Finset (↥R ⧸ Q.subgroupOf R)) := by
    rw [huniv]
    exact Finset.mem_univ _
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
  rcases hmem with h | h | h | h
  · exact Or.inl ((hπ1 _).mp h)
  · exact Or.inr (Or.inl ((hπeq _ _).mp h.symm))
  · exact Or.inr (Or.inr (Or.inl ((hπeq _ _).mp h.symm)))
  · refine Or.inr (Or.inr (Or.inr ?_))
    have : π ⟨s₁ * s₂, mul_mem hs₁ hs₂⟩ = π ⟨r, hr⟩ := by
      rw [h]
      exact map_mul π ⟨s₁, hs₁⟩ ⟨s₂, hs₂⟩
    exact (hπeq _ _).mp this

theorem dS_mul_le_sup {s₁ s₂ : G} (hs₁ : s₁ ∈ pCoreOf 2 (L₁Of L (fsuV1 T V) ⊔ T))
    (hs₂ : s₂ ∈ pCoreOf 2 (L₁Of L (fsuV1 T V) ⊔ T)) :
    dS T V (s₁ * s₂) ≤ dS T V s₁ ⊔ dS T V s₂ := by
  refine sup_le ((Subgroup.closure_le _).mpr ?_) (le_sup_right.trans le_sup_left)
  rintro _ ⟨u, hu, rfl⟩
  have hc₂ : u * s₂ * u⁻¹ * s₂⁻¹ ∈ V ⊔ u0 T V :=
    commutator_le_sup_u0 C.hyp C.hMod C.h63 C.hF C.h1222 C.h1332 C.h1334
      (Subgroup.commutator_mem_commutator hu hs₂)
  have h1 := comm_mem_of_R1_sup C.hyp C.hMod C.h63 C.hF C.h1222 C.h1332 C.h1334 hs₁ hc₂
  have e : u * (s₁ * s₂) * u⁻¹ * (s₁ * s₂)⁻¹ = (u * s₁ * u⁻¹ * s₁⁻¹) *
      ((s₁ * (u * s₂ * u⁻¹ * s₂⁻¹) * s₁⁻¹ * (u * s₂ * u⁻¹ * s₂⁻¹)⁻¹) *
        (u * s₂ * u⁻¹ * s₂⁻¹)) := by group
  rw [e]
  refine mul_mem (Subgroup.mem_sup_left (Subgroup.mem_sup_left
    (Subgroup.subset_closure ⟨u, hu, rfl⟩))) (mul_mem ?_ ?_)
  · exact Subgroup.mem_sup_left (Subgroup.mem_sup_right h1)
  · exact Subgroup.mem_sup_right (Subgroup.mem_sup_left (Subgroup.subset_closure ⟨u, hu, rfl⟩))

theorem comm_le_dS_sup {s₁ s₂ : G} (hs₁ : s₁ ∈ pCoreOf 2 (L₁Of L (fsuV1 T V) ⊔ T))
    (hs₁Q : s₁ ∉ pCoreOf 2 (hz T V)) (hs₂ : s₂ ∈ pCoreOf 2 (L₁Of L (fsuV1 T V) ⊔ T))
    (hs₂Q : s₂ ∉ pCoreOf 2 (hz T V)) (h12 : s₁⁻¹ * s₂ ∉ pCoreOf 2 (hz T V)) :
    ⁅fsuU T V, pCoreOf 2 (L₁Of L (fsuV1 T V) ⊔ T)⁆ ⊔ fsuV1 T V ≤ dS T V s₁ ⊔ dS T V s₂ := by
  refine sup_le ?_ (le_sup_right.trans le_sup_left)
  rw [Subgroup.commutator_le]
  intro u hu r hr
  rw [commutatorElement_def]
  have hgen : ∀ {s : G}, s ∈ pCoreOf 2 (L₁Of L (fsuV1 T V) ⊔ T) → ∀ q ∈ pCoreOf 2 (hz T V),
      r = s * q → u * r * u⁻¹ * r⁻¹ ∈ dS T V s := by
    intro s hs q hq hrq
    rw [hrq]
    exact C.dS_mul_le hs hq (Subgroup.mem_sup_left (Subgroup.subset_closure ⟨u, hu, rfl⟩))
  rcases C.mem_cosets hs₁ hs₁Q hs₂ hs₂Q h12 hr with h | h | h | h
  · have h1 := inv_mem (C.comm_Q h hu)
    rw [show (r * u * r⁻¹ * u⁻¹)⁻¹ = u * r * u⁻¹ * r⁻¹ by group] at h1
    exact Subgroup.mem_sup_left (Subgroup.mem_sup_right h1)
  · exact Subgroup.mem_sup_left (hgen hs₁ _ h (by group))
  · exact Subgroup.mem_sup_right (hgen hs₂ _ h (by group))
  · exact C.dS_mul_le_sup hs₁ hs₂ (hgen (mul_mem hs₁ hs₂) _ h (by group))

theorem dS_sup_eq {s₁ s₂ : G} (hs₁ : s₁ ∈ pCoreOf 2 (L₁Of L (fsuV1 T V) ⊔ T))
    (hs₁Q : s₁ ∉ pCoreOf 2 (hz T V)) (hs₂ : s₂ ∈ pCoreOf 2 (L₁Of L (fsuV1 T V) ⊔ T))
    (hs₂Q : s₂ ∉ pCoreOf 2 (hz T V)) (h12 : s₁⁻¹ * s₂ ∉ pCoreOf 2 (hz T V)) :
    dS T V s₁ ⊔ dS T V s₂ = V ⊔ u0 T V := by
  refine le_antisymm (sup_le (C.dS_le hs₁) (C.dS_le hs₂)) ?_
  rw [← C.comm_sup_eq]
  exact C.comm_le_dS_sup hs₁ hs₁Q hs₂ hs₂Q h12

theorem card_sup_u0 : Nat.card ↥(V ⊔ u0 T V) = 4 * Nat.card ↥(u0 T V) := by
  have h4 := (relIndex_sup_u0 C.hyp C.hMod C.h63 C.hF).1
  have h2 := Subgroup.relIndex_mul_card (u0 T V) (V ⊔ u0 T V)
  rw [inf_eq_left.mpr le_sup_right, h4] at h2
  exact h2.symm

theorem card_u0_le : Nat.card ↥(u0 T V) ≤ 8 := by
  obtain ⟨s₁, hs₁, hs₁Q, s₂, hs₂, hs₂Q, h12⟩ := C.exists_two
  have heq := C.dS_sup_eq hs₁ hs₁Q hs₂ hs₂Q h12
  have hN : dS T V s₁ ≤ Subgroup.normalizer (dS T V s₂ : Set G) := by
    intro d hd
    refine mem_normalizer_of_forall_conj_mem fun e he => ?_
    rw [C.hUc d (C.dS_le_U hs₁ hd) e (C.dS_le_U hs₂ he), mul_inv_cancel_right]
    exact he
  have h1 := L32NSet14.card_sup_mul_card_inf hN
  rw [heq, C.card_dS hs₁ hs₁Q, C.card_dS hs₂ hs₂Q, C.card_sup_u0] at h1
  have h2 : 2 ≤ Nat.card ↥(dS T V s₁ ⊓ dS T V s₂) := by
    have := Subgroup.card_le_of_le (le_inf (le_sup_right : fsuV1 T V ≤ dS T V s₁)
      (le_sup_right : fsuV1 T V ≤ dS T V s₂))
    rwa [C.hF.card_V₁] at this
  nlinarith

theorem conj_dS_eq {s x : G} (hx : x ∈ hz T V) (hs : s ∈ pCoreOf 2 (L₁Of L (fsuV1 T V) ⊔ T))
    (hsQ : s ∉ pCoreOf 2 (hz T V)) (hs' : x * s * x⁻¹ ∈ pCoreOf 2 (L₁Of L (fsuV1 T V) ⊔ T))
    (hs'Q : x * s * x⁻¹ ∉ pCoreOf 2 (hz T V)) :
    conjSub x (dS T V s) = dS T V (x * s * x⁻¹) := by
  have hle : conjSub x (dS T V s) ≤ dS T V (x * s * x⁻¹) := by
    intro y hy
    rw [mem_conjSub] at hy
    have := C.conj_mem_dS hx hy
    rwa [show x * (x⁻¹ * y * x) * x⁻¹ = y by group] at this
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  rw [C.card_dS hs' hs'Q, card_conjSub, C.card_dS hs hsQ]

theorem exists_fpf : ∃ x ∈ L₁Of L (fsuV1 T V), x ^ 3 = 1 ∧
    (∀ v ∈ V, x * v * x⁻¹ * v⁻¹ ∈ fsuV1 T V → v ∈ fsuV1 T V) ∧
    ∀ s ∈ pCoreOf 2 (L₁Of L (fsuV1 T V) ⊔ T), s ∉ pCoreOf 2 (hz T V) →
      s⁻¹ * (x * s * x⁻¹) ∉ pCoreOf 2 (hz T V) := by
  obtain ⟨x, hxL1, hx3, hfpf⟩ := exists_l1_fpf C.hyp C.hMod C.h1222 C.h1332 C.h1334
  have hx1 : x ≠ 1 := by
    intro h1
    obtain ⟨-, hV8, -, -, -⟩ := C.hMod G T L V C.hyp.hyp C.hyp.fsu
    obtain ⟨v, hv, hv1⟩ : ∃ v ∈ V, v ∉ fsuV1 T V := by
      by_contra hno
      push Not at hno
      have := Subgroup.card_le_of_le (show V ≤ fsuV1 T V from hno)
      rw [hV8, C.hF.card_V₁] at this
      omega
    exact hv1 (hfpf v hv (by rw [h1]; simp))
  refine ⟨x, hxL1, hx3, hfpf, fun s hs hsQ => ?_⟩
  intro hfix
  obtain ⟨r, hr, hrQ, hsr⟩ := C.exists_other hs
  obtain ⟨i, hi, hri⟩ := exists_pow_conj_mem C.hyp C.hMod C.h63 C.hF C.h1222 C.h1332 C.h1334
    hxL1 hx3 hx1 hs hsQ hr hrQ
  have hQn : ∀ g ∈ hz T V, ∀ q ∈ pCoreOf 2 (hz T V), g * q * g⁻¹ ∈ pCoreOf 2 (hz T V) :=
    fun g hg q hq => (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 _ hg) q).mp hq
  have hxH : x ∈ hz T V := C.hF.L₁T_le_H (Subgroup.mem_sup_left hxL1)
  have hpow : ∀ n : ℕ, s⁻¹ * (x ^ n * s * (x ^ n)⁻¹) ∈ pCoreOf 2 (hz T V) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have hxn : x ^ n ∈ hz T V := pow_mem hxH n
      have h1 := hQn _ hxn _ hfix
      rw [show x ^ (n + 1) * s * (x ^ (n + 1))⁻¹ = x ^ n * (x * s * x⁻¹) * (x ^ n)⁻¹ by
        rw [pow_succ]; group]
      rw [show s⁻¹ * (x ^ n * (x * s * x⁻¹) * (x ^ n)⁻¹) =
        (s⁻¹ * (x ^ n * s * (x ^ n)⁻¹)) * (x ^ n * (s⁻¹ * (x * s * x⁻¹)) * (x ^ n)⁻¹) by group]
      exact mul_mem ih h1
  apply hsr
  have h1 := hpow i
  rw [show s⁻¹ * r = (s⁻¹ * (x ^ i * s * (x ^ i)⁻¹)) * (r⁻¹ * (x ^ i * s * (x ^ i)⁻¹))⁻¹ by group]
  exact mul_mem h1 (inv_mem hri)

end Ctx764

end CFSG.Quasithin.H13.L32A
