module

public import CFSG.LocalAnalysis.QuasithinUnique.Defs
public import CFSG.GroupTheory.ABGLocalTools.PStabilitySignalizer

public section

namespace CFSG.Quasithin.H13.S3320

open CFSG.QuasithinUnique

theorem perm3_eq_top_of_normal {N : Subgroup (Equiv.Perm (Fin 3))} (hN : N.Normal)
    {τ : Equiv.Perm (Fin 3)} (hτ : τ ∈ N) (h1 : τ ≠ 1) (h2 : τ ^ 2 = 1) : N = ⊤ := by
  have key : ∀ τ x : Equiv.Perm (Fin 3), τ ≠ 1 → τ ^ 2 = 1 →
      (∃ g : Equiv.Perm (Fin 3), x = g * τ * g⁻¹) ∨
        ∃ g₁ g₂ : Equiv.Perm (Fin 3), x = g₁ * τ * g₁⁻¹ * (g₂ * τ * g₂⁻¹) := by
    decide
  rw [eq_top_iff]
  intro x _
  rcases key τ x h1 h2 with ⟨g, rfl⟩ | ⟨g₁, g₂, rfl⟩
  · exact hN.conj_mem τ hτ g
  · exact N.mul_mem (hN.conj_mem τ hτ g₁) (hN.conj_mem τ hτ g₂)

theorem perm3_inv : ∀ τ ρ : Equiv.Perm (Fin 3), τ ≠ 1 → τ ^ 2 = 1 → ρ ≠ 1 → ρ ^ 3 = 1 →
    τ * ρ * τ⁻¹ * ρ = 1 := by
  decide

theorem perm3_sq_eq_one_of_pow (x : Equiv.Perm (Fin 3)) {b : ℕ} (hx : x ^ 2 ^ b = 1) :
    x ^ 2 = 1 := by
  have h1 : orderOf x ∣ 2 ^ b := orderOf_dvd_of_pow_eq_one hx
  have h6 : orderOf x ∣ 6 := by
    have := orderOf_dvd_natCard x
    rwa [Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin] at this
  obtain ⟨c, -, hc⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h1
  have hc1 : c ≤ 1 := by
    by_contra hc1
    have h4 : 4 ∣ orderOf x := hc ▸ pow_dvd_pow 2 (by omega : 2 ≤ c)
    exact absurd (h4.trans h6) (by decide)
  apply orderOf_dvd_iff_pow_eq_one.mp
  rw [hc]
  exact pow_dvd_pow 2 hc1

variable {Q : Type} [Group Q] [Finite Q] {S H : Subgroup Q}

omit [Finite Q] in
theorem mem_of_congr_conjNormal_eq {Y : Subgroup Q} [Y.Normal]
    (hC : Subgroup.centralizer (Y : Set Q) = ⊥) {G : Type*} [Group G] (eG : ↥Y ≃* G) {x : Q}
    {g : G} (hg : MulAut.congr eG (MulAut.conjNormal x) = MulAut.conj g) : x ∈ Y := by
  set y : ↥Y := eG.symm g with hy
  have hcomm : (y : Q)⁻¹ * x ∈ Subgroup.centralizer (Y : Set Q) := by
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    have h2 : MulAut.conjNormal x ⟨z, hz⟩ = y * ⟨z, hz⟩ * y⁻¹ := by
      apply eG.injective
      have h1 := congrArg (fun φ : MulAut G => φ (eG ⟨z, hz⟩)) hg
      simp only [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply,
        MulAut.conj_apply] at h1
      rw [h1, map_mul, map_mul, map_inv, hy, MulEquiv.apply_symm_apply]
    have h3 := congrArg Subtype.val h2
    simp only [MulAut.conjNormal_apply, Subgroup.coe_mul, Subgroup.coe_inv] at h3
    calc z * ((y : Q)⁻¹ * x) = (y : Q)⁻¹ * ((y : Q) * z * (y : Q)⁻¹) * x := by group
      _ = (y : Q)⁻¹ * (x * z * x⁻¹) * x := by rw [h3]
      _ = (y : Q)⁻¹ * x * z := by group
  rw [hC, Subgroup.mem_bot, inv_mul_eq_one] at hcomm
  rw [← hcomm]
  exact y.2

theorem relIndex_dvd_index_of_normal' {Y : Subgroup Q} [Y.Normal] (S : Subgroup Q) :
    S.relIndex Y ∣ S.index := by
  have h1 := Subgroup.relIndex_inf_mul_relIndex S Y ⊤
  rw [inf_top_eq, Subgroup.relIndex_top_right, Subgroup.relIndex_top_right,
    ← Subgroup.relIndex_mul_index (inf_le_left : S ⊓ Y ≤ S), Subgroup.inf_relIndex_left] at h1
  obtain ⟨m, hm⟩ := Subgroup.relIndex_dvd_index_of_normal Y S
  rw [hm] at h1
  have h0 : Y.relIndex S ≠ 0 := Subgroup.index_ne_zero_of_finite
  refine ⟨m, ?_⟩
  apply Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero h0)
  rw [← h1]
  ring

theorem card_inf_normal {Y : Subgroup Q} [Y.Normal] (hS : IsSylowTwoOf S ⊤) :
    Nat.card ↥(S ⊓ Y) = 2 ^ (Nat.card Y).factorization 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, hS2, hSodd⟩ := hS
  have h3 : (S.subgroupOf ⊤).index = S.index := Subgroup.relIndex_top_right S
  rw [h3] at hSodd
  have hT : IsPGroup 2 (S.subgroupOf Y) :=
    hS2.comap_of_injective Y.subtype Y.subtype_injective
  have hTidx : ¬ 2 ∣ (S.subgroupOf Y).index :=
    fun h => hSodd (h.trans (relIndex_dvd_index_of_normal' S))
  have h1 := Sylow.card_eq_multiplicity (hT.toSylow hTidx)
  rw [IsPGroup.toSylow_coe] at h1
  rw [← h1, ← Subgroup.subgroupOf_map_subtype, Subgroup.card_map_of_injective Y.subtype_injective]

theorem o2_facts (hS : IsSylowTwoOf S ⊤) (hab : ∀ a ∈ S, ∀ b ∈ S, a * b = b * a)
    (hSH : S ≤ H) (e : ↥H ⧸ CFSG.pCore 2 ↥H ≃* Equiv.Perm (Fin 3)) :
    ∃ W : Subgroup Q, W ≤ S ∧ IsPGroup 2 W ∧ (∀ w ∈ W, ∀ x ∈ H, x * w = w * x) ∧
      Nat.card H = 6 * Nat.card W ∧ Nat.card S = 2 * Nat.card W ∧
      ∃ h₀ ∈ H, orderOf h₀ = 3 ∧ ∃ s ∈ S, s * h₀ * s⁻¹ * h₀ ∈ W := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set O : Subgroup ↥H := CFSG.pCore 2 ↥H with hO
  have hOn : O.Normal := CFSG.pCore_normal
  have hO2 : IsPGroup 2 O := CFSG.pCore_isPGroup
  obtain ⟨-, hS2, hSodd⟩ := hS
  set S' : Subgroup ↥H := S.subgroupOf H with hS'
  have hS'S : Nat.card S' = Nat.card S := Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSH).toEquiv
  have hS'2 : IsPGroup 2 S' := hS2.of_equiv (Subgroup.subgroupOfEquivOfLe hSH).symm
  have hS'odd : ¬ 2 ∣ S'.index := by
    intro h2
    apply hSodd
    have h1 : S.relIndex H ∣ S.index := Subgroup.relIndex_dvd_index_of_le hSH
    have h3 : (S.subgroupOf ⊤).index = S.index := Subgroup.relIndex_top_right S
    rw [h3]
    exact h2.trans h1
  have hOS' : O ≤ S' := CFSG.ABGLocalTools.pCore_le_of_not_dvd_index hS'odd
  set φ : ↥H →* Equiv.Perm (Fin 3) := e.toMonoidHom.comp (QuotientGroup.mk' O) with hφ
  have hφker : ∀ x : ↥H, φ x = 1 ↔ x ∈ O := fun x => by
    rw [hφ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.map_eq_one_iff,
      QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  have hφs : Function.Surjective φ := e.surjective.comp (QuotientGroup.mk'_surjective O)
  have hOidx : O.index = 6 := by
    rw [Subgroup.index, Nat.card_congr e.toEquiv, Nat.card_perm, Nat.card_eq_fintype_card,
      Fintype.card_fin]
    rfl
  have hrel : O.relIndex S' * S'.index = 6 := by
    rw [Subgroup.relIndex_mul_index hOS', hOidx]
  obtain ⟨b, hb⟩ := hS'2.exists_card_eq
  have hreldvd : O.relIndex S' ∣ 2 ^ b := hb ▸ Subgroup.relIndex_dvd_card O S'
  obtain ⟨c, -, hc⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hreldvd
  have hrel2 : O.relIndex S' = 2 := by
    rw [hc] at hrel ⊢
    have hc2 : c ≤ 2 := by
      by_contra hc2
      have h8 : 8 ∣ 2 ^ c := by
        have := pow_dvd_pow 2 (by omega : 3 ≤ c)
        simpa using this
      have := Nat.le_of_dvd (by norm_num) (h8.trans (Dvd.intro _ hrel))
      omega
    interval_cases c
    · rw [pow_zero, one_mul] at hrel
      exact absurd ⟨3, by omega⟩ hS'odd
    · rfl
    · omega
  have hcardS' : Nat.card S' = 2 * Nat.card O := by
    have h1 := Subgroup.card_mul_index (O.subgroupOf S')
    have h2 : Nat.card (O.subgroupOf S') = Nat.card O :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hOS').toEquiv
    have h3 : (O.subgroupOf S').index = 2 := hrel2
    rw [h2, h3] at h1
    rw [← h1, mul_comm]
  have hcardH : Nat.card ↥H = 6 * Nat.card O := by
    rw [← hOidx, mul_comm]
    exact (Subgroup.card_mul_index O).symm
  obtain ⟨s, hsS', hsO⟩ : ∃ s ∈ S', s ∉ O := by
    by_contra hall
    push Not at hall
    have : O.relIndex S' = 1 := Subgroup.relIndex_eq_one.mpr hall
    omega
  have hφs1 : φ s ≠ 1 := fun h => hsO ((hφker s).mp h)
  have hφs2 : φ s ^ 2 = 1 := by
    have hsb : (⟨s, hsS'⟩ : ↥S') ^ 2 ^ b = 1 := by
      rw [← hb]
      exact pow_card_eq_one'
    have h1 : s ^ 2 ^ b = 1 := by
      have := congrArg Subtype.val hsb
      simpa using this
    apply perm3_sq_eq_one_of_pow (φ s) (b := b)
    rw [← map_pow, h1, map_one]
  have hOab : ∀ a ∈ O, ∀ b ∈ O, a * b = b * a := by
    intro a ha b' hb'
    apply Subtype.ext
    exact hab _ (hOS' ha) _ (hOS' hb')
  have hS'C : S' ≤ Subgroup.centralizer (O : Set ↥H) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro o ho
    apply Subtype.ext
    exact hab _ (hOS' ho) _ hx
  have hCtop : (Subgroup.centralizer (O : Set ↥H)).map φ = ⊤ := by
    have hn : ((Subgroup.centralizer (O : Set ↥H)).map φ).Normal :=
      Subgroup.Normal.map (Subgroup.normal_centralizer (H := O)) φ hφs
    exact perm3_eq_top_of_normal hn ⟨s, hS'C hsS', rfl⟩ hφs1 hφs2
  have hcent : ∀ w ∈ O, ∀ x : ↥H, x * w = w * x := by
    intro w hw x
    obtain ⟨c', hc', hcx⟩ := (Subgroup.mem_map.mp (hCtop ▸ Subgroup.mem_top (φ x)))
    have ho : c'⁻¹ * x ∈ O := by
      rw [← hφker, map_mul, map_inv, hcx, inv_mul_cancel]
    have hx : x = c' * (c'⁻¹ * x) := by group
    rw [hx]
    have h1 := (Subgroup.mem_centralizer_iff.mp hc') w hw
    rw [mul_assoc, ← hOab _ hw _ ho, ← mul_assoc, ← h1, mul_assoc]
  have h3dvd : 3 ∣ Nat.card ↥H := by
    rw [hcardH]
    exact Dvd.dvd.mul_right (by norm_num) _
  obtain ⟨h, hh⟩ := exists_prime_orderOf_dvd_card' 3 h3dvd
  have hhO : h ∉ O := by
    intro hmem
    obtain ⟨k, hk⟩ := hO2 ⟨h, hmem⟩
    have h1 : h ^ 2 ^ k = 1 := by
      have := congrArg Subtype.val hk
      simpa using this
    have h2 : 3 ∣ 2 ^ k := hh ▸ orderOf_dvd_of_pow_eq_one h1
    have h3 : 3 ∣ 2 := (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h2)
    omega
  have hφh1 : φ h ≠ 1 := fun hh1 => hhO ((hφker h).mp hh1)
  have hh3 : h ^ 3 = 1 := by
    rw [← hh]
    exact pow_orderOf_eq_one h
  have hφh3 : φ h ^ 3 = 1 := by
    rw [← map_pow, hh3, map_one]
  have hinv : s * h * s⁻¹ * h ∈ O := by
    rw [← hφker]
    simp only [map_mul, map_inv]
    exact perm3_inv _ _ hφs1 hφs2 hφh1 hφh3
  refine ⟨O.map H.subtype, ?_, ?_, ?_, ?_, ?_, ⟨(h : Q), h.2, ?_, (s : Q), hsS', ?_⟩⟩
  · intro x hx
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
    exact hOS' hy
  · exact hO2.map H.subtype
  · intro w hw x hx
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hw
    have := congrArg Subtype.val (hcent y hy ⟨x, hx⟩)
    simpa using this
  · rw [hcardH, Subgroup.card_map_of_injective H.subtype_injective]
  · rw [← hS'S, hcardS', Subgroup.card_map_of_injective H.subtype_injective]
  · rw [Subgroup.orderOf_coe, hh]
  · exact ⟨_, hinv, by simp⟩

end CFSG.Quasithin.H13.S3320
