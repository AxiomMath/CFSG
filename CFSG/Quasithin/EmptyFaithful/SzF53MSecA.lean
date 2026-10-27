module

public import CFSG.Quasithin.EmptyFaithful.SzF53MDefs
public import CFSG.Quasithin.Recognition.F112WChief

public section

namespace CFSG.Quasithin.F53Mod

open CFSG.Open CFSG.LieType.BorelTits

variable {G : Type} [Group G]

theorem mem_cSecIn_iff {F L N : Subgroup G} (hFL : F ≤ Subgroup.normalizer (L : Set G)) {f : G} :
    f ∈ cSecIn F L N ↔ f ∈ F ∧ ∀ x ∈ N, f * x * f⁻¹ * x⁻¹ ∈ L := by
  refine ⟨fun hf => ?_, fun h => Subgroup.subset_closure h⟩
  induction hf using Subgroup.closure_induction with
  | mem f hf => exact hf
  | one => exact ⟨F.one_mem, fun x _ => by simp⟩
  | mul f g _ _ hf hg =>
    refine ⟨F.mul_mem hf.1 hg.1, fun x hx => ?_⟩
    have e : f * g * x * (f * g)⁻¹ * x⁻¹ =
        (f * (g * x * g⁻¹ * x⁻¹) * f⁻¹) * (f * x * f⁻¹ * x⁻¹) := by group
    rw [e]
    exact L.mul_mem ((Subgroup.mem_normalizer_iff.mp (hFL hf.1) _).mp (hg.2 x hx)) (hf.2 x hx)
  | inv f _ hf =>
    refine ⟨F.inv_mem hf.1, fun x hx => ?_⟩
    have e : f⁻¹ * x * f⁻¹⁻¹ * x⁻¹ = f⁻¹ * (f * x * f⁻¹ * x⁻¹)⁻¹ * f⁻¹⁻¹ := by group
    rw [e]
    exact (Subgroup.mem_normalizer_iff.mp (hFL (F.inv_mem hf.1)) _).mp (L.inv_mem (hf.2 x hx))

theorem mem_fixSecIn_iff {A L N : Subgroup G} (hNL : N ≤ Subgroup.normalizer (L : Set G)) {x : G} :
    x ∈ fixSecIn A L N ↔ x ∈ N ∧ ∀ a ∈ A, a * x * a⁻¹ * x⁻¹ ∈ L := by
  refine ⟨fun hx => ?_, fun h => Subgroup.subset_closure h⟩
  induction hx using Subgroup.closure_induction with
  | mem x hx => exact hx
  | one => exact ⟨N.one_mem, fun a _ => by simp⟩
  | mul x y _ _ hx hy =>
    refine ⟨N.mul_mem hx.1 hy.1, fun a ha => ?_⟩
    have e : a * (x * y) * a⁻¹ * (x * y)⁻¹ =
        (a * x * a⁻¹ * x⁻¹) * (x * (a * y * a⁻¹ * y⁻¹) * x⁻¹) := by group
    rw [e]
    exact L.mul_mem (hx.2 a ha) ((Subgroup.mem_normalizer_iff.mp (hNL hx.1) _).mp (hy.2 a ha))
  | inv x _ hx =>
    refine ⟨N.inv_mem hx.1, fun a ha => ?_⟩
    have e : a * x⁻¹ * a⁻¹ * x⁻¹⁻¹ = x⁻¹ * (a * x * a⁻¹ * x⁻¹)⁻¹ * x⁻¹⁻¹ := by group
    rw [e]
    exact (Subgroup.mem_normalizer_iff.mp (hNL (N.inv_mem hx.1)) _).mp (L.inv_mem (hx.2 a ha))

def fixer (L : Subgroup G) (x : G) : Subgroup G where
  carrier := {s | s ∈ Subgroup.normalizer (L : Set G) ∧ s * x * s⁻¹ * x⁻¹ ∈ L}
  one_mem' := ⟨Subgroup.one_mem _, by simp⟩
  mul_mem' := fun {s t} hs ht => by
    refine ⟨Subgroup.mul_mem _ hs.1 ht.1, ?_⟩
    have e : s * t * x * (s * t)⁻¹ * x⁻¹ =
        (s * (t * x * t⁻¹ * x⁻¹) * s⁻¹) * (s * x * s⁻¹ * x⁻¹) := by group
    rw [e]
    exact L.mul_mem ((Subgroup.mem_normalizer_iff.mp hs.1 _).mp ht.2) hs.2
  inv_mem' := fun {s} hs => by
    refine ⟨Subgroup.inv_mem _ hs.1, ?_⟩
    have e : s⁻¹ * x * s⁻¹⁻¹ * x⁻¹ = s⁻¹ * (s * x * s⁻¹ * x⁻¹)⁻¹ * s⁻¹⁻¹ := by group
    rw [e]
    exact (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hs.1) _).mp (L.inv_mem hs.2)

theorem mem_fixer_iff {L : Subgroup G} {x s : G} :
    s ∈ fixer L x ↔ s ∈ Subgroup.normalizer (L : Set G) ∧ s * x * s⁻¹ * x⁻¹ ∈ L := Iff.rfl

theorem mem_fixSecIn_zpowers_iff {A B : Subgroup G} (hBA : B ≤ Subgroup.normalizer (A : Set G))
    {a : G} (ha : a ∈ Subgroup.normalizer (A : Set G)) {x : G} :
    x ∈ fixSecIn (Subgroup.zpowers a) A B ↔ x ∈ B ∧ a * x * a⁻¹ * x⁻¹ ∈ A := by
  rw [mem_fixSecIn_iff hBA]
  refine and_congr_right fun _ => ⟨fun h => h a (Subgroup.mem_zpowers a), fun h s hs => ?_⟩
  exact ((Subgroup.zpowers_le.mpr ⟨ha, h⟩ : Subgroup.zpowers a ≤ fixer A x) hs).2

theorem normalizer_left {H U L N : Subgroup G} (hs : IsChiefStep H U L N) :
    H ≤ Subgroup.normalizer (L : Set G) := D14.le_normalizer_of_isNormalIn hs.2.1

theorem normalizer_right {H U L N : Subgroup G} (hs : IsChiefStep H U L N) :
    H ≤ Subgroup.normalizer (N : Set G) := D14.le_normalizer_of_isNormalIn hs.1

variable [Finite G]

theorem isSec_of_chiefStep {H U L N : Subgroup G} (hUH : U ≤ H) (hUQ : U ≤ pCoreOf 2 H)
    (hs : IsChiefStep H U L N) : IsSec H L N := by
  have hHL := normalizer_left hs
  have hHN := normalizer_right hs
  have hNU : N ≤ U := hs.1.1
  have hLN : L ≤ N := hs.2.2.1.le
  have hN2 : IsPGroup 2 N := (pCoreOf_isPGroup 2 H).to_le (hNU.trans hUQ)
  have hNL : ∀ x ∈ N, ∀ y ∈ L, x * y * x⁻¹ ∈ L := fun x hx y hy =>
    (Subgroup.mem_normalizer_iff.mp (hHL (hUH (hNU hx))) y).mp hy
  have hcomm : ∀ x ∈ N, ∀ y ∈ N, x * y * x⁻¹ * y⁻¹ ∈ L := by
    have h := F112W.commutator_le_of_isChiefStep hN2 (hNU.trans hUH) hHN hs le_rfl
    exact fun x hx y hy => h (Subgroup.commutator_mem_commutator hx hy)
  refine ⟨hLN, hHN, hHL, hcomm, ?_⟩
  let M : Subgroup G :=
    { carrier := {x | x ∈ N ∧ x ^ 2 ∈ L}
      one_mem' := ⟨N.one_mem, by simp⟩
      mul_mem' := fun {x y} hx hy => by
        refine ⟨N.mul_mem hx.1 hy.1, ?_⟩
        have e : (x * y) ^ 2 = (x * y * x⁻¹ * y⁻¹) * (y * x ^ 2 * y⁻¹) * y ^ 2 := by
          simp only [pow_two]; group
        rw [e]
        exact L.mul_mem (L.mul_mem (hcomm x hx.1 y hy.1) (hNL y hy.1 _ hx.2)) hy.2
      inv_mem' := fun {x} hx => by
        refine ⟨N.inv_mem hx.1, ?_⟩
        have e : x⁻¹ ^ 2 = (x ^ 2)⁻¹ := by simp only [pow_two]; group
        rw [e]
        exact L.inv_mem hx.2 }
  have hMN : M ≤ N := fun x hx => hx.1
  have hLM : L ≤ M := fun x hx => ⟨hLN hx, by simpa [pow_two] using L.mul_mem hx hx⟩
  have hMn : IsNormalIn H U M := by
    refine ⟨hMN.trans hNU, fun g hg x hx => ⟨hs.1.2 g hg x hx.1, ?_⟩⟩
    have e : (g * x * g⁻¹) ^ 2 = g * x ^ 2 * g⁻¹ := by simp only [pow_two]; group
    rw [e]
    exact hs.2.1.2 g hg _ hx.2
  rcases hs.2.2.2 M hMn hLM hMN with hML | hMN'
  · exfalso
    have key : ∀ k : ℕ, ∀ y ∈ N, y ^ 2 ^ k ∈ L → y ∈ L := by
      intro k
      induction k with
      | zero => intro y _ hy; simpa using hy
      | succ k ih =>
        intro y hy hyk
        have hz : y ^ 2 ^ k ∈ N := N.pow_mem hy _
        have hz2 : (y ^ 2 ^ k) ^ 2 ∈ L := by rwa [← pow_mul, ← pow_succ]
        exact ih y hy (hML ▸ (show y ^ 2 ^ k ∈ M from ⟨hz, hz2⟩))
    have hNL' : N ≤ L := by
      intro x hx
      obtain ⟨k, hk⟩ := hN2 ⟨x, hx⟩
      refine key k x hx ?_
      have h1 : x ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
      rw [h1]
      exact L.one_mem
    exact absurd hNL' (not_le_of_gt hs.2.2.1)
  · intro x hx
    exact (hMN' ▸ hx : x ∈ M).2

theorem pCoreOf_le_cSecIn_of_chiefStep {H U L N : Subgroup G} (_hUH : U ≤ H)
    (hUQ : U ≤ pCoreOf 2 H) (hs : IsChiefStep H U L N) : pCoreOf 2 H ≤ cSecIn H L N := by
  have h := F112W.commutator_le_of_isChiefStep (pCoreOf_isPGroup 2 H) (pCoreOf_le 2 H)
    (le_normalizer_pCoreOf 2 H) hs (hs.1.1.trans hUQ)
  intro q hq
  refine Subgroup.subset_closure ⟨pCoreOf_le 2 H hq, fun x hx => ?_⟩
  have h1 : x * q * x⁻¹ * q⁻¹ ∈ L := h (Subgroup.commutator_mem_commutator hx hq)
  have e : q * x * q⁻¹ * x⁻¹ = (x * q * x⁻¹ * q⁻¹)⁻¹ := by group
  rw [e]
  exact L.inv_mem h1

end CFSG.Quasithin.F53Mod
