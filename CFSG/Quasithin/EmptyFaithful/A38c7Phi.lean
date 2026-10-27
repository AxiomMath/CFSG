module

public import CFSG.Quasithin.Background.A1bPGroups
public import CFSG.Quasithin.Background.B2FactorizationResidual

public section

namespace CFSG.Quasithin.A38c7

open CFSG.Open

private theorem perm3_cube_inv_mul {σ τ : Equiv.Perm (Fin 3)} (hσ : σ ^ 3 = 1) (hτ : τ ^ 3 = 1) :
    (σ⁻¹ * τ) ^ 3 = 1 := by
  revert σ τ
  decide

private theorem prod_cube_inv_mul {a u : Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3)}
    (ha : a ^ 3 = 1) (hu : u ^ 3 = 1) : (a⁻¹ * u) ^ 3 = 1 := by
  obtain ⟨ha₁, ha₂⟩ := Prod.ext_iff.1 ha
  obtain ⟨hu₁, hu₂⟩ := Prod.ext_iff.1 hu
  exact Prod.ext (perm3_cube_inv_mul ha₁ hu₁) (perm3_cube_inv_mul ha₂ hu₂)

private theorem card_cube_perm3 : Nat.card {σ : Equiv.Perm (Fin 3) // σ ^ 3 = 1} = 3 := by
  rw [Nat.card_eq_fintype_card]
  decide

private theorem eq_one_of_pow_three_of_pow_two_pow {P : Type*} [Group P] {x : P}
    (h₃ : x ^ 3 = 1) {k : ℕ} (h₂ : x ^ 2 ^ k = 1) : x = 1 := by
  have hdvd : orderOf x ∣ Nat.gcd 3 (2 ^ k) :=
    Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one h₃) (orderOf_dvd_of_pow_eq_one h₂)
  have hcop : Nat.gcd 3 (2 ^ k) = 1 := Nat.Coprime.pow_right k (by norm_num)
  rw [hcop] at hdvd
  exact orderOf_eq_one_iff.1 (Nat.dvd_one.1 hdvd)

private theorem exists_mul_of_mem_sup_of_conj {G : Type*} [Group G] {L S : Subgroup G}
    (hn : ∀ s ∈ S, ∀ l ∈ L, s * l * s⁻¹ ∈ L) :
    ∀ x ∈ L ⊔ S, ∃ l ∈ L, ∃ s ∈ S, x = l * s := by
  let LS : Subgroup G :=
    { carrier := {x | ∃ l ∈ L, ∃ s ∈ S, x = l * s}
      one_mem' := ⟨1, L.one_mem, 1, S.one_mem, by simp⟩
      mul_mem' := by
        rintro _ _ ⟨l, hl, s, hs, rfl⟩ ⟨l', hl', s', hs', rfl⟩
        refine ⟨l * (s * l' * s⁻¹), L.mul_mem hl (hn s hs l' hl'), s * s', S.mul_mem hs hs', ?_⟩
        group
      inv_mem' := by
        rintro _ ⟨l, hl, s, hs, rfl⟩
        refine ⟨s⁻¹ * l⁻¹ * s⁻¹⁻¹, ?_, s⁻¹, S.inv_mem hs, ?_⟩
        · exact hn s⁻¹ (S.inv_mem hs) l⁻¹ (L.inv_mem hl)
        · group }
  have hle : L ⊔ S ≤ LS :=
    sup_le (fun l hl => ⟨l, hl, 1, S.one_mem, by simp⟩)
      (fun s hs => ⟨1, L.one_mem, s, hs, by simp⟩)
  intro x hx
  exact hle hx

private theorem cube_mem_pCore_and_card {H : Type*} [Group H] [Finite H]
    (hE : IsElemAbelianOfRank 3 2 (H ⧸ CFSG.Open.pCore 2 H)) :
    (∀ y : H, y ^ 3 ∈ CFSG.Open.pCore 2 H) ∧ ∃ c : ℕ, Nat.card H = 2 ^ c * 9 := by
  obtain ⟨e⟩ := hE
  refine ⟨fun y => ?_, ?_⟩
  · have hq : ∀ q : H ⧸ CFSG.Open.pCore 2 H, q ^ 3 = 1 := by
      intro q
      apply e.injective
      rw [map_pow, map_one]
      refine Multiplicative.toAdd.injective ?_
      funext i
      simp only [toAdd_pow, toAdd_one, Pi.smul_apply, Pi.zero_apply]
      generalize Multiplicative.toAdd (e q) i = z
      revert z
      decide
    have h := hq (QuotientGroup.mk y)
    rw [← QuotientGroup.mk_pow] at h
    exact (QuotientGroup.eq_one_iff _).1 h
  · obtain ⟨c, hc⟩ := (IsPGroup.iff_card (p := 2)).1
      (CFSG.LieType.BorelTits.pCore_isPGroup (G := H) 2)
    refine ⟨c, ?_⟩
    have h₉ : Nat.card (Multiplicative (Fin 2 → ZMod 3)) = 9 := by simp
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (CFSG.Open.pCore 2 H), hc,
      Nat.card_congr e.toEquiv, h₉, mul_comm]

private theorem map_inclusion_eq_one_of_mem_pCore {G : Type*} [Group G] [Finite G]
    {Yp S : Subgroup G} (hSY : ∀ s ∈ S, ∀ y ∈ Yp, s * y * s⁻¹ ∈ Yp) {Q : Type*} [Group Q]
    (φ : ↥(Yp ⊔ S) →* Q) (hker : φ.ker = (oTwoPhi (Yp ⊔ S)).subgroupOf (Yp ⊔ S))
    {z : ↥Yp} (hz : z ∈ CFSG.Open.pCore 2 ↥Yp) :
    φ (Subgroup.inclusion le_sup_left z) = 1 := by
  have hS : S ≤ Subgroup.normalizer (Yp : Set G) := fun s hs =>
    Subgroup.mem_normalizer_iff.2 fun y =>
      ⟨hSY s hs y, fun hy => by
        have h := hSY s⁻¹ (S.inv_mem hs) _ hy
        have e : s⁻¹ * (s * y * s⁻¹) * s⁻¹⁻¹ = y := by group
        rwa [e] at h⟩
  have hX : Yp ⊔ S ≤ Subgroup.normalizer (Yp : Set G) := sup_le Subgroup.le_normalizer hS
  have hO : pCoreOf 2 Yp ≤ pCoreOf 2 (Yp ⊔ S) :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
      ((CFSG.LieType.BorelTits.pCoreOf_le 2 Yp).trans le_sup_left)
      (hX.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 Yp))
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 Yp)
  have hzO : (z : G) ∈ pCoreOf 2 Yp := Subgroup.mem_map.2 ⟨z, hz, rfl⟩
  obtain ⟨w, hw, hwz⟩ := Subgroup.mem_map.1 (hO hzO)
  have hwe : w = Subgroup.inclusion le_sup_left z := Subtype.ext hwz
  rw [← hwe]
  have hmem : (w : G) ∈ oTwoPhi (Yp ⊔ S) := by
    refine Subgroup.mem_map.2 ⟨w, ?_, rfl⟩
    rw [Subgroup.mem_comap]
    change (↑w : ↥(Yp ⊔ S) ⧸ CFSG.Open.pCore 2 ↥(Yp ⊔ S)) ∈ _
    rw [(QuotientGroup.eq_one_iff w).2 hw]
    exact Subgroup.one_mem _
  have hmem' : w ∈ φ.ker := by
    rw [hker, Subgroup.mem_subgroupOf]
    exact hmem
  exact hmem'

private theorem card_range_of_cube {H : Type*} [Group H] (f : H →* Equiv.Perm (Fin 3))
    (h₁ : ∀ y, f y ^ 3 = 1) (h₂ : ∀ σ : Equiv.Perm (Fin 3), σ ^ 3 = 1 → ∃ y, f y = σ) :
    Nat.card f.range = 3 := by
  have hset : ∀ σ : Equiv.Perm (Fin 3), σ ∈ f.range ↔ σ ^ 3 = 1 := by
    intro σ
    constructor
    · rintro ⟨y, rfl⟩
      exact h₁ y
    · intro h
      exact h₂ σ h
  exact (Nat.card_congr (Equiv.subtypeEquivRight hset)).trans card_cube_perm3

private theorem exists_two_kernels {H : Type*} [Group H] [Finite H]
    (ψ : H →* Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3)) (h₁ : ∀ y, ψ y ^ 3 = 1)
    (h₂ : ∀ u, u ^ 3 = 1 → ∃ y, ψ y = u) :
    ∃ K₁ K₂ : Subgroup H, (∀ y, y ∈ K₁ ↔ (ψ y).2 = 1) ∧ (∀ y, y ∈ K₂ ↔ (ψ y).1 = 1) ∧
      K₁ ⊔ K₂ = ⊤ ∧ Nat.card K₁ * 3 = Nat.card H ∧ Nat.card K₂ * 3 = Nat.card H := by
  set ψ₁ : H →* Equiv.Perm (Fin 3) := (MonoidHom.fst _ _).comp ψ with hψ₁
  set ψ₂ : H →* Equiv.Perm (Fin 3) := (MonoidHom.snd _ _).comp ψ with hψ₂
  have hcard₁ : Nat.card ψ₁.range = 3 := by
    refine card_range_of_cube ψ₁ (fun y => (Prod.ext_iff.1 (h₁ y)).1) fun σ hσ => ?_
    obtain ⟨y, hy⟩ := h₂ (σ, 1) (Prod.ext (by simpa using hσ) (by simp))
    exact ⟨y, by simp [hψ₁, hy]⟩
  have hcard₂ : Nat.card ψ₂.range = 3 := by
    refine card_range_of_cube ψ₂ (fun y => (Prod.ext_iff.1 (h₁ y)).2) fun σ hσ => ?_
    obtain ⟨y, hy⟩ := h₂ (1, σ) (Prod.ext (by simp) (by simpa using hσ))
    exact ⟨y, by simp [hψ₂, hy]⟩
  refine ⟨ψ₂.ker, ψ₁.ker, fun y => by simp [hψ₂], fun y => by simp [hψ₁], ?_, ?_, ?_⟩
  · refine eq_top_iff.2 fun y _ => ?_
    obtain ⟨hy₁, hy₂⟩ := Prod.ext_iff.1 (h₁ y)
    obtain ⟨y₁, hy₁'⟩ := h₂ ((ψ y).1, 1) (Prod.ext (by simpa using hy₁) (by simp))
    obtain ⟨y₂, hy₂'⟩ := h₂ (1, (ψ y).2) (Prod.ext (by simp) (by simpa using hy₂))
    have hk : y * y₂⁻¹ * y₁⁻¹ ∈ ψ₂.ker := by
      simp [hψ₂, hy₁', hy₂']
    have hy₁m : y₁ ∈ ψ₂.ker := by
      simp [hψ₂, hy₁']
    have hy₂m : y₂ ∈ ψ₁.ker := by
      simp [hψ₁, hy₂']
    have hyy : y = (y * y₂⁻¹ * y₁⁻¹ * y₁) * y₂ := by group
    rw [hyy]
    exact Subgroup.mul_mem_sup (ψ₂.ker.mul_mem hk hy₁m) hy₂m
  · rw [← Subgroup.card_ker_mul_card_range ψ₂, hcard₂]
  · rw [← Subgroup.card_ker_mul_card_range ψ₁, hcard₁]

private theorem conj_mem_map_subtype {G : Type*} [Group G] {Yp S : Subgroup G}
    (hSY : ∀ s ∈ S, ∀ y ∈ Yp, s * y * s⁻¹ ∈ Yp) {P Q : Type*} [Group P] [Group Q]
    (φ : ↥(Yp ⊔ S) →* P) (π : P →* Q) (K : Subgroup ↥Yp)
    (hK : ∀ y : ↥Yp, y ∈ K ↔ π (φ (Subgroup.inclusion le_sup_left y)) = 1) :
    ∀ s ∈ S, ∀ y ∈ K.map Yp.subtype, s * y * s⁻¹ ∈ K.map Yp.subtype := by
  intro s hs y hy
  obtain ⟨k, hk, rfl⟩ := Subgroup.mem_map.1 hy
  have hk' : s * (k : G) * s⁻¹ ∈ Yp := hSY s hs k k.2
  refine Subgroup.mem_map.2 ⟨⟨_, hk'⟩, ?_, rfl⟩
  rw [hK] at hk ⊢
  have hconj : Subgroup.inclusion le_sup_left (⟨s * (k : G) * s⁻¹, hk'⟩ : ↥Yp) =
      (⟨s, (le_sup_right : S ≤ Yp ⊔ S) hs⟩ : ↥(Yp ⊔ S)) * Subgroup.inclusion le_sup_left k *
        (⟨s, (le_sup_right : S ≤ Yp ⊔ S) hs⟩ : ↥(Yp ⊔ S))⁻¹ := rfl
  rw [hconj, map_mul, map_mul, map_inv, map_mul, map_mul, map_inv, hk, mul_one, mul_inv_cancel]

theorem exists_two_factors {G : Type} [Group G] [Finite G] {Yp S : Subgroup G}
    (hS2 : IsPGroup 2 S) (hSY : ∀ s ∈ S, ∀ y ∈ Yp, s * y * s⁻¹ ∈ Yp)
    (hE : IsElemAbelianOfRank 3 2 (↥Yp ⧸ CFSG.Open.pCore 2 ↥Yp))
    (φ : ↥(Yp ⊔ S) →* Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3)) (hφ : Function.Surjective φ)
    (hker : φ.ker = (oTwoPhi (Yp ⊔ S)).subgroupOf (Yp ⊔ S)) :
    ∃ Y₁ Y₂ : Subgroup G, Y₁ ≤ Yp ∧ Y₂ ≤ Yp ∧ Yp ≤ Y₁ ⊔ Y₂ ∧
      (∀ s ∈ S, ∀ y ∈ Y₁, s * y * s⁻¹ ∈ Y₁) ∧ (∀ s ∈ S, ∀ y ∈ Y₂, s * y * s⁻¹ ∈ Y₂) ∧
      (∃ a, Nat.card Y₁ = 2 ^ a * 3) ∧ (∃ a, Nat.card Y₂ = 2 ^ a * 3) := by
  have hXY : Yp ≤ Yp ⊔ S := le_sup_left
  have hXS : S ≤ Yp ⊔ S := le_sup_right
  set ψ : ↥Yp →* Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3) :=
    φ.comp (Subgroup.inclusion hXY) with hψ
  obtain ⟨hcube, c, hc⟩ := cube_mem_pCore_and_card hE
  have h₁ : ∀ y : ↥Yp, ψ y ^ 3 = 1 := by
    intro y
    rw [← map_pow]
    exact map_inclusion_eq_one_of_mem_pCore hSY φ hker (hcube y)
  have h₂ : ∀ u : Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3), u ^ 3 = 1 → ∃ y : ↥Yp, ψ y = u := by
    intro u hu
    obtain ⟨x, rfl⟩ := hφ u
    obtain ⟨y, hy, s, hs, hxys⟩ := exists_mul_of_mem_sup_of_conj hSY x.1 x.2
    have hx : x = Subgroup.inclusion hXY ⟨y, hy⟩ * Subgroup.inclusion hXS ⟨s, hs⟩ :=
      Subtype.ext hxys
    refine ⟨⟨y, hy⟩, ?_⟩
    have hs3 : (φ (Subgroup.inclusion hXS ⟨s, hs⟩)) ^ 3 = 1 := by
      have e : φ (Subgroup.inclusion hXS ⟨s, hs⟩) = (ψ ⟨y, hy⟩)⁻¹ * φ x := by
        rw [hx, map_mul]
        simp [hψ]
      rw [e]
      exact prod_cube_inv_mul (h₁ _) hu
    obtain ⟨k, hk⟩ := hS2 ⟨s, hs⟩
    have hs2 : (φ (Subgroup.inclusion hXS ⟨s, hs⟩)) ^ 2 ^ k = 1 := by
      rw [← map_pow, ← map_pow, hk, map_one, map_one]
    have hφs := eq_one_of_pow_three_of_pow_two_pow hs3 hs2
    rw [hx, map_mul, hφs, mul_one]
    rfl
  obtain ⟨K₁, K₂, hK₁, hK₂, hsup, hcard₁, hcard₂⟩ := exists_two_kernels ψ h₁ h₂
  refine ⟨K₁.map Yp.subtype, K₂.map Yp.subtype, Subgroup.map_subtype_le _,
    Subgroup.map_subtype_le _, ?_, ?_, ?_, ⟨c, ?_⟩, ⟨c, ?_⟩⟩
  · rw [← Subgroup.map_sup, hsup, Subgroup.map_top, Subgroup.range_subtype]
  · exact conj_mem_map_subtype hSY φ (MonoidHom.snd _ _) K₁ hK₁
  · exact conj_mem_map_subtype hSY φ (MonoidHom.fst _ _) K₂ hK₂
  · rw [Subgroup.card_subtype]
    omega
  · rw [Subgroup.card_subtype]
    omega

end CFSG.Quasithin.A38c7
