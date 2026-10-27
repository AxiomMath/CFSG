module

public import CFSG.Quasithin.Recognition.Kleidman.ThreeLocalCentralizerAnalysis.BetaLift
public import CFSG.Quasithin.Recognition.Kleidman.ThreeLocalCentralizerAnalysis.CentralizerK

public section

namespace CFSG.Quasithin.Kleidman.ThreeLocal

open Subgroup

@[expose] def normSubgroup {X : Type*} [Group X] [Fintype X] [DecidableEq X] (c t : X)
    (hmul : ∀ x ∈ normSet c t, ∀ y ∈ normSet c t, x * y ∈ normSet c t)
    (hinv : ∀ x ∈ normSet c t, x⁻¹ ∈ normSet c t) : Subgroup X where
  carrier := ↑(normSet c t)
  mul_mem' := fun {a b} ha hb => hmul a ha b hb
  one_mem' := Finset.mem_coe.mpr (Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun v hv => by
    simpa using hv⟩)
  inv_mem' := fun {a} ha => hinv a ha

theorem card_normSubgroup {X : Type*} [Group X] [Fintype X] [DecidableEq X] {c t : X}
    {hmul : ∀ x ∈ normSet c t, ∀ y ∈ normSet c t, x * y ∈ normSet c t}
    {hinv : ∀ x ∈ normSet c t, x⁻¹ ∈ normSet c t} :
    Nat.card (normSubgroup c t hmul hinv) = (normSet c t).card := by
  rw [← Nat.card_eq_finsetCard]
  exact Nat.card_congr (Equiv.subtypeEquivRight fun x => Iff.rfl)

theorem pow_three_eq_one_of_mem_NY {G : Type} [Group G] {y : G} (hy3 : orderOf y = 3)
    {n : ↥(CK y)} (hn : n ∈ NY y) : n ^ 3 = 1 := by
  have := pow_card_eq_one' (G := NY y) (x := ⟨n, hn⟩)
  rw [NY_card hy3] at this
  exact congrArg Subtype.val this

theorem exists_beta_of_check {G : Type} [Group G] [Finite G] {y : G} (hy3 : orderOf y = 3)
    {X : Type} [Group X] [Fintype X] [DecidableEq X] {c0 : X} (hc : BetaCheck X c0)
    (ψ : (↥(CK y) ⧸ NY y) ≃* X) {e : Fin 7 → G} (he0 : e 0 = y)
    (hD8 : ∀ r ∈ d8Rels, evalWord e r = 1) (hz : e 3 ≠ 1) :
    ∃ β ∈ CK y, ∀ r ∈ a2Rels, evalWord (Function.update e 6 β) r = 1 := by
  obtain ⟨hc2, hc1, hcls, hcheck⟩ := hc
  obtain ⟨f2, f3, f4, f111, f24, f34, f10, f20, f30⟩ := d8_facts hD8
  have hmem : ∀ i : Fin 7, i.val ≤ 3 → e i ∈ CK y := by
    intro i hi
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hi' : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
    rcases hi' with rfl | rfl | rfl | rfl
    · rw [he0]
    · rw [← he0]; exact f10
    · rw [← he0]; exact f20
    · rw [← he0]; exact f30
  let τ : Fin 7 → ↥(CK y) := fun i => if h : i.val ≤ 3 then ⟨e i, hmem i h⟩ else 1
  have hτe : ∀ i : Fin 7, i.val ≤ 3 → ((τ i : ↥(CK y)) : G) = e i := fun i h => by simp [τ, h]
  have hDK : ∀ r ∈ d8Rels, evalWord τ r = 1 := by
    intro r hr
    apply (CK y).subtype_injective
    rw [map_one, evalWord_map]
    rw [← hD8 r hr]
    apply evalWord_congr
    intro x hx
    exact hτe x.1 (d8Rels_letters r hr x hx)
  have hτ0 : τ 0 = ⟨y, mem_CK_self y⟩ := by
    apply Subtype.ext
    simp [τ, he0]
  have hyNY : (⟨y, mem_CK_self y⟩ : ↥(CK y)) ∈ NY y := Subgroup.mem_zpowers _
  obtain ⟨k2, k3, k4, -, k24, k34, -, -, -⟩ := d8_facts hDK
  let κ0 : ↥(CK y) →* X := ψ.toMonoidHom.comp (QuotientGroup.mk' (NY y))
  have hκ0k : ∀ k : ↥(CK y), κ0 k = 1 ↔ k ∈ NY y := by
    intro k
    show ψ (QuotientGroup.mk' (NY y) k) = 1 ↔ _
    rw [map_eq_one_iff ψ ψ.injective]
    exact QuotientGroup.eq_one_iff k
  have hκ0s : Function.Surjective κ0 := ψ.surjective.comp (QuotientGroup.mk'_surjective _)
  have h4 : κ0 (τ 3) ≠ 1 := by
    intro h
    have hNY := (hκ0k _).mp h
    have h3 := pow_three_eq_one_of_mem_NY hy3 hNY
    have h1 : τ 3 = 1 := by
      calc τ 3 = τ 3 ^ 3 * (τ 3 * τ 3)⁻¹ := by group
        _ = 1 := by rw [h3, k4]; simp
    apply hz
    rw [← hτe 3 (by decide), h1]
    rfl
  have h4sq : κ0 (τ 3) * κ0 (τ 3) = 1 := by rw [← map_mul, k4, map_one]
  obtain ⟨g, hg⟩ := hcls (κ0 (τ 3)) h4sq h4
  let κ : ↥(CK y) →* X := (MulAut.conj g⁻¹).toMonoidHom.comp κ0
  have hκ : ∀ k, κ k = g⁻¹ * κ0 k * g := fun k => by simp [κ]
  have hκk : κ.ker = NY y := by
    ext k
    rw [MonoidHom.mem_ker, hκ, ← hκ0k]
    constructor
    · intro h
      have : κ0 k = g * 1 * g⁻¹ := by
        calc κ0 k = g * (g⁻¹ * κ0 k * g) * g⁻¹ := by group
          _ = g * 1 * g⁻¹ := by rw [h]
      simpa using this
    · intro h; rw [h]; group
  have hκs : Function.Surjective κ := by
    intro x
    obtain ⟨k, hk⟩ := hκ0s (g * x * g⁻¹)
    refine ⟨k, ?_⟩
    rw [hκ, hk]; group
  have hκ3 : κ (τ 3) = c0 := by
    rw [hκ, ← hg]; group
  have hκτ0 : κ (τ 0) = 1 := by
    rw [← MonoidHom.mem_ker, hκk, hτ0]; exact hyNY
  have hrelκ : ∀ r ∈ d8Rels, evalWord (fun i => κ (τ i)) r = 1 := by
    intro r hr
    rw [← evalWord_map, hDK r hr, map_one]
  obtain ⟨-, -, -, -, b24, b34, -, -, -⟩ := d8_facts hrelκ
  have ha2 : κ (τ 1) ∈ centSet c0 :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, by rw [← hκ3]; exact b24⟩
  have ha3 : κ (τ 2) ∈ centSet c0 :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, by rw [← hκ3]; exact b34⟩
  have hbet : ∀ (s' : X) (i : Fin 7), i.val ≤ 3 →
      betaTup (κ (τ 1)) (κ (τ 2)) c0 s' i = κ (τ i) := by
    intro s' i hi
    have hi' : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
    rcases hi' with rfl | rfl | rfl | rfl
    · simp [betaTup, hκτ0]
    · simp [betaTup]
    · simp [betaTup]
    · simp [betaTup, hκ3]
  have hrel' : ∀ r ∈ d8Rels, evalWord (betaTup (κ (τ 1)) (κ (τ 2)) c0 1) r = 1 := by
    intro r hr
    refine (evalWord_congr ?_).trans (hrelκ r hr)
    intro x hx
    exact hbet 1 x.1 (d8Rels_letters r hr x hx)
  obtain ⟨t, ht2, htc, ht1, htc0, hcard24, hmul, hinv, ha2m, ha3m, hc0m, hreal3, s, hs, hrel⟩ :=
    hcheck (κ (τ 1)) ha2 (κ (τ 2)) ha3 hrel'
  let 𝒮 : Subgroup X := normSubgroup c0 t hmul hinv
  have h𝒮 : Nat.card 𝒮 = 24 := by
    rw [card_normSubgroup, hcard24]
  have hτ𝒮 : ∀ i : Fin 7, i.val ≤ 3 → κ (τ i) ∈ 𝒮 := by
    intro i hi
    have hi' : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
    rcases hi' with rfl | rfl | rfl | rfl
    · rw [hκτ0]; exact 𝒮.one_mem
    · exact ha2m
    · exact ha3m
    · rw [hκ3]; exact hc0m
  have hτsq : ∀ i : Fin 7, 1 ≤ i.val → i.val ≤ 3 → τ i * τ i = 1 := by
    intro i h1 h3
    have hi' : i = 1 ∨ i = 2 ∨ i = 3 := by omega
    rcases hi' with rfl | rfl | rfl
    · exact k2
    · exact k3
    · exact k4
  have hyc : (⟨y, mem_CK_self y⟩ : ↥(CK y)) ∈ center ↥(CK y) := NY_le_center y hyNY
  have hy3K : orderOf (⟨y, mem_CK_self y⟩ : ↥(CK y)) = 3 := by
    rw [Subgroup.orderOf_mk]; exact hy3
  have hκk' : κ.ker = zpowers (⟨y, mem_CK_self y⟩ : ↥(CK y)) := hκk
  have hrelκ' : ∀ r ∈ a2Rels, evalWord (fun i => if i = 6 then s else κ (τ i)) r = 1 := by
    intro r hr
    rw [← hrel r hr]
    apply evalWord_congr
    intro x hx
    by_cases h6 : x.1 = 6
    · simp [h6, betaTup]
    · have h3 : x.1.val ≤ 3 := by
        rcases a2Rels_letters r hr x hx with h | h
        · exact h
        · exact absurd (Fin.ext h) h6
      simp only [h6, if_false]
      exact (hbet s x.1 h3).symm
  obtain ⟨β0, hβ0⟩ := exists_lift_beta hyc hy3K κ hκs hκk' 𝒮 h𝒮
    (fun x hx h3 h1 => hreal3 x hx h3 h1) τ hτ0 hτ𝒮 hτsq hs hrelκ'
  refine ⟨(β0 : G), β0.2, fun r hr => ?_⟩
  have h := congrArg (CK y).subtype (hβ0 r hr)
  rw [evalWord_map, map_one] at h
  rw [← h]
  apply evalWord_congr
  intro x hx
  by_cases h6 : x.1 = 6
  · simp [h6]
  · have h3 : x.1.val ≤ 3 := by
      rcases a2Rels_letters r hr x hx with h' | h'
      · exact h'
      · exact absurd (Fin.ext h') h6
    simp only [Function.update_of_ne h6]
    exact (hτe x.1 h3).symm

end CFSG.Quasithin.Kleidman.ThreeLocal
