module

public import CFSG.Quasithin.Vol2.Ch10SecFAct
public import CFSG.Quasithin.Vol2.Ch10SecABasicV
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecF

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.H13 CFSG.QuasithinUnique Equiv
open CFSG.QuasithinUnique.A5.Delta5 (pact isEven vact)

set_option synthInstance.maxHeartbeats 400000 in
set_option synthInstance.maxSize 4000 in
theorem stab_three : ∀ q : Perm (Fin 5), q ^ 3 = 1 → ∀ w : Fin 5 → ZMod 2, isEven w →
    pact q w ≠ w → ∀ σ : Perm (Fin 5), pact σ w = w → pact σ (pact q w) = pact q w →
    pact σ (pact q (pact q w)) = pact q (pact q w) → σ * q = q * σ ∧ σ * σ = 1 := by
  decide +kernel

theorem alt_pow_four : ∀ g : Perm (Fin 5), Perm.sign g = 1 → g ^ 4 = 1 → g * g = 1 := by
  decide +kernel

set_option synthInstance.maxHeartbeats 400000 in
set_option synthInstance.maxSize 4000 in
theorem false_of_two_inv : ∀ q : Perm (Fin 5), q ^ 3 = 1 → q ≠ 1 →
    ∀ a : Perm (Fin 5), Perm.sign a = 1 → a ≠ 1 → a * a = 1 →
      (a * q * a⁻¹ = 1 ∨ a * q * a⁻¹ = q ∨ a * q * a⁻¹ = q * q) →
    ∀ b : Perm (Fin 5), Perm.sign b = 1 → b ≠ 1 → b ≠ a → b * b = 1 → a * b = b * a →
      (b * q * b⁻¹ = 1 ∨ b * q * b⁻¹ = q ∨ b * q * b⁻¹ = q * q) → False := by
  decide +kernel

set_option maxRecDepth 10000 in
theorem perm_five_pow_nine : ∀ σ : Perm (Fin 5), σ ^ 9 = 1 → σ ^ 3 = 1 := by
  decide +kernel

theorem perm_five_pow_three_pow (σ : Perm (Fin 5)) (k : ℕ) (h : σ ^ 3 ^ k = 1) : σ ^ 3 = 1 := by
  induction k with
  | zero => rw [pow_zero, pow_one] at h; rw [h, one_pow]
  | succ k ih =>
    rcases k with _ | k
    · simpa using h
    · apply ih
      have h9 : (σ ^ 3 ^ k) ^ 9 = 1 := by
        rw [← pow_mul, show 3 ^ k * 9 = 3 ^ (k + 1 + 1) by ring]
        exact h
      have := perm_five_pow_nine _ h9
      rw [← pow_mul] at this
      rw [show 3 ^ (k + 1) = 3 ^ k * 3 by ring]
      exact this

variable {G : Type} [Group G]

theorem exists_pi_normalizer {L : Subgroup G} (hA : IsAltType L 5) (hZ : blockZ L = ⊥) :
    ∃ (c : G → Fin 5 → ZMod 2) (π : G → Perm (Fin 5)),
      (∀ u ∈ blockU L, ∀ u' ∈ blockU L, c u = c u' → u = u') ∧
      (∀ u ∈ blockU L, isEven (c u)) ∧
      (∀ y ∈ Subgroup.normalizer (L : Set G), ∀ u ∈ blockU L,
        c (y * u * y⁻¹) = pact (π y) (c u)) ∧
      (∀ y ∈ Subgroup.normalizer (L : Set G), ∀ z ∈ Subgroup.normalizer (L : Set G),
        π (y * z) = π y * π z) ∧
      ∃ α : ↥L →* alternatingGroup (Fin 5), Function.Surjective α ∧
        α.ker = CFSG.pCore 2 ↥L ∧
          ∀ ℓ : ↥L, π ℓ = ((α ℓ : alternatingGroup (Fin 5)) : Perm (Fin 5)) := by
  classical
  obtain ⟨α, hαs, hαk, β, hβs, hβk, hβe⟩ := hA
  set Nn := Subgroup.normalizer (L : Set G) with hNn
  have hLN : L ≤ Nn := Subgroup.le_normalizer
  have hKN : pCoreOf 2 L ≤ Nn := (CFSG.LieType.BorelTits.pCoreOf_le 2 L).trans hLN
  have hNK : Nn ≤ Subgroup.normalizer (pCoreOf 2 L : Set G) :=
    CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 L
  have hUL : blockU L ≤ L :=
    (Subgroup.commutator_mono (CFSG.LieType.BorelTits.pCoreOf_le 2 L) le_rfl).trans
      (Subgroup.le_normalizer_iff_commutator_le_left.mp Subgroup.le_normalizer)
  have hUN : blockU L ≤ Nn := hUL.trans hLN
  have hNU : Nn ≤ Subgroup.normalizer (blockU L : Set G) := SecA.le_normalizer_commutator hNK le_rfl
  have : (L.subgroupOf Nn).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hLN).mpr le_rfl
  have : ((pCoreOf 2 L).subgroupOf Nn).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKN).mpr hNK
  have : ((blockU L).subgroupOf Nn).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hUN).mpr hNU
  set eL : ↥(L.subgroupOf Nn) ≃* ↥L := Subgroup.subgroupOfEquivOfLe hLN
  set α' : ↥(L.subgroupOf Nn) →* alternatingGroup (Fin 5) := α.comp eL.toMonoidHom
  have hβinj : Function.Injective β := by
    rw [← MonoidHom.ker_eq_bot_iff, hβk, hZ, Subgroup.bot_subgroupOf]
  set β₀ : ↥(blockU L) ≃* Multiplicative (evenWeight 5) := MulEquiv.ofBijective β ⟨hβinj, hβs⟩
  set eU : ↥((blockU L).subgroupOf Nn) ≃* ↥(blockU L) := Subgroup.subgroupOfEquivOfLe hUN
  set β' := eU.trans β₀
  have hα' : Function.Surjective α' := hαs.comp eL.surjective
  have hker' : ∀ ℓ : ↥(L.subgroupOf Nn), α' ℓ = 1 ↔ (ℓ : ↥Nn) ∈ (pCoreOf 2 L).subgroupOf Nn := by
    intro ℓ
    rw [Subgroup.mem_subgroupOf]
    show α (eL ℓ) = 1 ↔ _
    rw [← MonoidHom.mem_ker, hαk]
    constructor
    · intro h
      exact ⟨eL ℓ, h, rfl⟩
    · rintro ⟨m, hm, hme⟩
      have : m = eL ℓ := Subtype.ext hme
      rwa [← this]
  have hβ' : ∀ (ℓ : ↥(L.subgroupOf Nn)) (u u' : ↥((blockU L).subgroupOf Nn)),
      (u' : ↥Nn) = (ℓ : ↥Nn) * (u : ↥Nn) * (ℓ : ↥Nn)⁻¹ →
      Multiplicative.toAdd (β' u') = vact ((α' ℓ : alternatingGroup (Fin 5)) : Perm (Fin 5))
        (Multiplicative.toAdd (β' u)) := by
    intro ℓ u u' h
    apply Subtype.ext
    funext i
    exact hβe (eL ℓ) (eU u) (eU u') (by
      have := congrArg Subtype.val h
      show ((u' : ↥Nn) : G) = ((ℓ : ↥Nn) : G) * ((u : ↥Nn) : G) * ((ℓ : ↥Nn) : G)⁻¹
      simpa using this) i
  obtain ⟨π, hπ1, hπ2⟩ := exists_pi_gen (L.subgroupOf Nn) ((pCoreOf 2 L).subgroupOf Nn)
    ((blockU L).subgroupOf Nn) α' hα' hker' β' hβ'
  refine ⟨fun u => if hu : u ∈ blockU L then
      ((Multiplicative.toAdd (β₀ ⟨u, hu⟩) : evenWeight 5) : Fin 5 → ZMod 2) else 0,
    fun y => if hy : y ∈ Nn then π ⟨y, hy⟩ else 1, ?_, ?_, ?_, ?_, α, hαs, hαk, ?_⟩
  · intro u hu u' hu' h
    simp only [hu, hu', dite_true] at h
    have h1 : β₀ ⟨u, hu⟩ = β₀ ⟨u', hu'⟩ :=
      Multiplicative.toAdd.injective (Subtype.ext h)
    exact congrArg Subtype.val (β₀.injective h1)
  · intro u hu
    simp only [hu, dite_true]
    exact (Multiplicative.toAdd (β₀ ⟨u, hu⟩)).2
  · intro y hy u hu
    have hu' : y * u * y⁻¹ ∈ blockU L := (Subgroup.mem_normalizer_iff.mp (hNU hy) u).mp hu
    simp only [hu, hu', hy, dite_true]
    have h1 := hπ1 ⟨y, hy⟩ ⟨⟨u, hUN hu⟩, hu⟩ ⟨⟨y * u * y⁻¹, hUN hu'⟩, hu'⟩ rfl
    exact congrArg Subtype.val h1
  · intro y hy z hz
    simp only [hy, hz, Nn.mul_mem hy hz, dite_true]
    rw [← map_mul]
    rfl
  · intro ℓ
    simp only [hLN ℓ.2, dite_true]
    have := hπ2 ⟨⟨ℓ, hLN ℓ.2⟩, ℓ.2⟩
    rw [this]
    rfl

end CFSG.Quasithin.Vol2.Ch10.SecF
