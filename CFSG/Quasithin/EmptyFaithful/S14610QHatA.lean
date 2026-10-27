module

public import Mathlib.GroupTheory.SpecificGroups.Alternating
public import Mathlib.GroupTheory.IsPerfect

public section

namespace CFSG.Quasithin

open scoped commutatorElement

private theorem qhatA_normal_eq_top
    {Q : Type} [Group Q] (hperf : Group.IsPerfect Q)
    (hsimple : IsSimpleGroup (Q ⧸ Subgroup.center Q))
    (N : Subgroup Q) [hNn : N.Normal] (hN : ¬ N ≤ Subgroup.center Q) : N = ⊤ := by
  have := hsimple
  have hmap : (N.map (QuotientGroup.mk' (Subgroup.center Q))).Normal :=
    Subgroup.Normal.map hNn _ (QuotientGroup.mk'_surjective _)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (N.map (QuotientGroup.mk' (Subgroup.center Q)))
    with h | h
  · exact absurd (by simpa [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] using h) hN
  · have hdecomp : ∀ g : Q, ∃ n ∈ N, ∃ c ∈ Subgroup.center Q, g = n * c := by
      intro g
      have hg : QuotientGroup.mk' (Subgroup.center Q) g ∈
          N.map (QuotientGroup.mk' (Subgroup.center Q)) := by
        rw [h]; trivial
      obtain ⟨n, hn, hng⟩ := hg
      refine ⟨n, hn, n⁻¹ * g, ?_, by simp⟩
      rw [← QuotientGroup.ker_mk' (Subgroup.center Q), MonoidHom.mem_ker, map_mul, map_inv, hng]
      simp
    have hcomm : commutator Q ≤ N := by
      rw [commutator_def, Subgroup.commutator_le]
      intro g₁ _ g₂ _
      obtain ⟨n₁, hn₁, c₁, hc₁, rfl⟩ := hdecomp g₁
      obtain ⟨n₂, hn₂, c₂, hc₂, rfl⟩ := hdecomp g₂
      rw [Subgroup.mem_center_iff] at hc₁ hc₂
      have h1 : ∀ y : Q, ⁅c₁, y⁆ = 1 := fun y =>
        (commutatorElement_eq_one_iff_mul_comm).2 (hc₁ y).symm
      have h2 : ∀ x : Q, ⁅x, c₂⁆ = 1 := fun x =>
        (commutatorElement_eq_one_iff_mul_comm).2 (hc₂ x)
      have : ⁅n₁ * c₁, n₂ * c₂⁆ = ⁅n₁, n₂⁆ := by
        simp [commutatorElement_mul_left_eq_conj_mul, commutatorElement_mul_right_eq_mul_conj,
          h1, h2]
      rw [this, commutatorElement_def]
      exact N.mul_mem (N.mul_mem (N.mul_mem hn₁ hn₂) (N.inv_mem hn₁)) (N.inv_mem hn₂)
    rw [hperf.commutator_eq_top] at hcomm
    exact top_le_iff.mp hcomm

private theorem qhatA_index_ge_six
    {Q : Type} [Group Q] [Finite Q] (hperf : Group.IsPerfect Q)
    (hsimple : IsSimpleGroup (Q ⧸ Subgroup.center Q))
    (hZ : Nat.card (Subgroup.center Q) = 3) (hQ : Nat.card Q = 1080)
    (H : Subgroup Q) (hH : H.index ≠ 1) : 6 ≤ H.index := by
  by_contra hlt
  have hlt : H.index < 6 := not_le.mp hlt
  by_cases hle : H.normalCore ≤ Subgroup.center Q
  · have h1 : Nat.card H.normalCore ≤ 3 := hZ ▸ Subgroup.card_le_of_le hle
    have h2 : H.normalCore.index ≤ Nat.factorial H.index :=
      Subgroup.index_normalCore_le_factorial_index H
    have h3 : Nat.factorial H.index ≤ 120 :=
      calc Nat.factorial H.index ≤ Nat.factorial 5 := Nat.factorial_le (by omega)
        _ = 120 := by decide
    have h4 := Subgroup.index_mul_card H.normalCore
    rw [hQ] at h4
    have h5 := Nat.mul_le_mul (h2.trans h3) h1
    omega
  · have htop := qhatA_normal_eq_top hperf hsimple H.normalCore hle
    have hH' : H = ⊤ := top_le_iff.mp (htop ▸ Subgroup.normalCore_le H)
    exact hH (Subgroup.index_eq_one.mpr hH')

private theorem qhatA_stabilizer_index_ge
    {Q : Type} [Group Q] [Finite Q] (hperf : Group.IsPerfect Q)
    (hsimple : IsSimpleGroup (Q ⧸ Subgroup.center Q))
    (hZ : Nat.card (Subgroup.center Q) = 3) (hQ : Nat.card Q = 1080)
    {X : Type*} [MulAction Q X] {z : Q} (hz : z ∈ Subgroup.center Q) {x : X}
    (hzx : z • x ≠ x) : 18 ≤ (MulAction.stabilizer Q x).index := by
  set H := MulAction.stabilizer Q x with hHdef
  have hzH : z ∉ H := fun h => hzx (MulAction.mem_stabilizer_iff.1 h)
  have hinf : H ⊓ Subgroup.center Q = ⊥ := by
    have hdvd : Nat.card (H ⊓ Subgroup.center Q : Subgroup Q) ∣ 3 :=
      hZ ▸ Subgroup.card_dvd_of_le inf_le_right
    rcases (Nat.dvd_prime Nat.prime_three).1 hdvd with h1 | h3
    · exact Subgroup.card_eq_one.1 h1
    · exfalso
      have heq : H ⊓ Subgroup.center Q = Subgroup.center Q :=
        Subgroup.eq_of_le_of_card_ge inf_le_right (by rw [hZ, h3])
      have hzmem : z ∈ H ⊓ Subgroup.center Q := by rw [heq]; exact hz
      exact hzH hzmem.1
  have hrel : (Subgroup.center Q).relIndex (H ⊔ Subgroup.center Q) = Nat.card H := by
    rw [Subgroup.relIndex_sup_right, ← Subgroup.inf_relIndex_right (Subgroup.center Q) H,
      inf_comm, hinf, Subgroup.relIndex_bot_left]
  have hZidx : (Subgroup.center Q).index = 360 := by
    have := Subgroup.index_mul_card (Subgroup.center Q)
    rw [hZ, hQ] at this
    omega
  have hmul1 : Nat.card H * (H ⊔ Subgroup.center Q).index = 360 := by
    have := Subgroup.relIndex_mul_index (le_sup_right : Subgroup.center Q ≤ H ⊔ Subgroup.center Q)
    rw [hrel, hZidx] at this
    exact this
  have hmul2 : Nat.card H * H.index = 1080 := by
    have := Subgroup.card_mul_index H
    rwa [hQ] at this
  have hpos : 0 < Nat.card H := Nat.card_pos
  have hidx : H.index = 3 * (H ⊔ Subgroup.center Q).index := by
    have : Nat.card H * H.index = Nat.card H * (3 * (H ⊔ Subgroup.center Q).index) := by
      rw [hmul2, mul_left_comm, hmul1]
      norm_num
    exact Nat.eq_of_mul_eq_mul_left hpos this
  have h1 := qhatA_index_ge_six hperf hsimple hZ hQ H
  have h2 := qhatA_index_ge_six hperf hsimple hZ hQ (H ⊔ Subgroup.center Q)
  have hne : H.index ≠ 0 := Subgroup.index_ne_zero_of_finite
  by_cases ha : (H ⊔ Subgroup.center Q).index = 1
  · have h3 : H.index = 3 := by omega
    have := h1 (by omega)
    omega
  · have := h2 ha
    omega

private theorem qhatA_card_modEq_one
    {Q : Type} [Group Q] (hZ : Nat.card (Subgroup.center Q) = 3)
    {E : Type} [Group E] [Finite E] (φ : Q →* MulAut E) {z : Q} (hz : z ∈ Subgroup.center Q)
    (hfpf : ∀ e : E, φ z e = e → e = 1) : Nat.card E ≡ 1 [MOD 3] := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let _ : MulAction (Subgroup.center Q) E :=
    MulAction.compHom E (φ.comp (Subgroup.center Q).subtype)
  have hp : IsPGroup 3 (Subgroup.center Q) := IsPGroup.of_card (n := 1) (by simpa using hZ)
  have hmod := hp.card_modEq_card_fixedPoints E
  have hfix : MulAction.fixedPoints (Subgroup.center Q) E = {1} := by
    ext e
    simp only [MulAction.mem_fixedPoints, Set.mem_singleton_iff]
    constructor
    · intro h
      exact hfpf e (h ⟨z, hz⟩)
    · rintro rfl c
      exact map_one (φ (c : Q))
  rw [hfix] at hmod
  simpa using hmod

theorem hatA6_no_small_fpf_action
    {Q : Type} [Group Q] [Finite Q]
    (hperf : Group.IsPerfect Q) (hsimple : IsSimpleGroup (Q ⧸ Subgroup.center Q))
    (hZ : Nat.card (Subgroup.center Q) = 3)
    (hA : Nonempty (Q ⧸ Subgroup.center Q ≃* alternatingGroup (Fin 6)))
    {E : Type} [Group E] [Finite E] [Nontrivial E]
    (hpow : ∃ d : ℕ, Nat.card E = 2 ^ d) (hE : Nat.card E ≤ 2 ^ 5)
    (φ : Q →* MulAut E) {z : Q} (hz : z ∈ Subgroup.center Q) (hz1 : z ≠ 1)
    (hfpf : ∀ e : E, φ z e = e → e = 1) : False := by
  have _ := hz1
  have hQA : Nat.card (Q ⧸ Subgroup.center Q) = 360 := by
    obtain ⟨e⟩ := hA
    rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup]
    simp [Nat.factorial]
  have hQ : Nat.card Q = 1080 := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center Q), hQA, hZ]
  let _ : MulAction Q E := MulAction.compHom E φ
  obtain ⟨e, he⟩ := exists_ne (1 : E)
  have hzx : z • e ≠ e := fun h => he (hfpf e h)
  have h18 := qhatA_stabilizer_index_ge hperf hsimple hZ hQ hz hzx
  rw [MulAction.index_stabilizer] at h18
  have hsub : MulAction.orbit Q e ⊆ (Set.univ : Set E) \ {1} := by
    rintro y ⟨g, rfl⟩
    refine ⟨Set.mem_univ _, ?_⟩
    intro h
    exact he ((MulEquiv.map_eq_one_iff (φ g)).1 h)
  have hle : (MulAction.orbit Q e).ncard ≤ Nat.card E - 1 :=
    calc (MulAction.orbit Q e).ncard ≤ ((Set.univ : Set E) \ {1}).ncard :=
          Set.ncard_le_ncard hsub
      _ = Nat.card E - 1 := by
          rw [Set.ncard_sdiff_singleton_of_mem (Set.mem_univ _), Set.ncard_univ]
  have hmod := qhatA_card_modEq_one hZ φ hz hfpf
  obtain ⟨d, hd⟩ := hpow
  rw [hd] at hmod hle hE
  have hd5 : d ≤ 5 := by
    by_contra h
    have : 2 ^ 6 ≤ 2 ^ d := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  unfold Nat.ModEq at hmod
  interval_cases d <;> omega

end CFSG.Quasithin
