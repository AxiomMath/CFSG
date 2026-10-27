module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.DefsModule
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Basic

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.LocalAnalysis.UniquenessCase.PartTwo

theorem w135c2_fixV_eq_bot {W : Type} [CommGroup W] {L : Subgroup (MulAut W)}
    (hirr : IsIrrOn L ⊤ ⊥) (hL : L ≠ ⊥) : fixV L = ⊥ := by
  obtain ⟨-, -, -, hJ⟩ := hirr
  have hst : StableUnder L (fixV L) := fun x hx u hu => by
    rw [hu x hx]; exact hu
  rcases hJ (fixV L) hst bot_le le_top with h | h
  · exact h
  · exfalso
    apply hL
    rw [eq_bot_iff]
    intro g hg
    have : ∀ w, g w = w := fun w => by
      have : w ∈ fixV L := by rw [h]; trivial
      exact this g hg
    rw [Subgroup.mem_bot]
    ext w
    simpa using this w

theorem w135c2_card_le_of_generation (W : Type) [CommGroup W] [Finite W]
    (h2 : ∀ w : W, w ^ 2 = 1) (L : Subgroup (MulAut W)) (hirr : IsIrrOn L ⊤ ⊥) (hL : L ≠ ⊥)
    (T : Finset (MulAut W)) (hT : L ≤ Subgroup.closure (T : Set (MulAut W))) (c : ℕ)
    (hc : ∀ x ∈ T, E3.mQuot ⊤ (fixV (Subgroup.zpowers x)) ≤ c) :
    Nat.card W ≤ 2 ^ (T.card * c) := by
  have hp : IsPGroup 2 W := fun g => ⟨1, by simpa using h2 g⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hidx : ∀ x ∈ T, (fixV (Subgroup.zpowers x)).index ≤ 2 ^ c := by
    intro x hx
    have hd : (fixV (Subgroup.zpowers x)).index ∣ Nat.card W := Subgroup.index_dvd_card _
    obtain ⟨k, hk⟩ := (IsPGroup.iff_card.1 hp)
    rw [hk] at hd
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hd
    have := hc x hx
    simp only [E3.mQuot, Subgroup.relIndex_top_right, hj, padicValNat.prime_pow] at this
    rw [hj]
    exact Nat.pow_le_pow_right (by norm_num) this
  let f : T → Subgroup W := fun x => fixV (Subgroup.zpowers x.1)
  have hbot : (⨅ x : T, f x) = ⊥ := by
    rw [eq_bot_iff, ← w135c2_fixV_eq_bot hirr hL]
    intro v hv g hg
    have hv' : ∀ x : T, x.1 v = v := fun x => by
      have := (Subgroup.mem_iInf.1 hv) x
      exact this x.1 (Subgroup.mem_zpowers _)
    have hmem : g ∈ MulAction.stabilizer (MulAut W) v := by
      have := hT hg
      refine (Subgroup.closure_le (MulAction.stabilizer (MulAut W) v)).2 ?_ this
      intro x hx
      exact hv' ⟨x, hx⟩
    exact hmem
  have h1 : Nat.card W = (⨅ x : T, f x).index := by
    rw [hbot, Subgroup.index_bot]
  calc Nat.card W = (⨅ x : T, f x).index := h1
    _ ≤ ∏ x : T, (f x).index := Subgroup.index_iInf_le f
    _ ≤ (2 ^ c) ^ (Finset.univ : Finset T).card :=
        Finset.prod_le_pow_card _ _ _ fun x _ => hidx x.1 x.2
    _ = 2 ^ (T.card * c) := by
        rw [Finset.card_univ, Fintype.card_coe, ← pow_mul, mul_comm]

theorem w135c2_rk_le_of_generation (W : Type) [CommGroup W] [Finite W]
    (h2 : ∀ w : W, w ^ 2 = 1) (L : Subgroup (MulAut W)) (hirr : IsIrrOn L ⊤ ⊥) (hL : L ≠ ⊥)
    (T : Finset (MulAut W)) (hT : L ≤ Subgroup.closure (T : Set (MulAut W))) (c : ℕ)
    (hc : ∀ x ∈ T, E3.mQuot ⊤ (fixV (Subgroup.zpowers x)) ≤ c) :
    rk W ≤ T.card * c := by
  have hp : IsPGroup 2 W := fun g => ⟨1, by simpa using h2 g⟩
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card.1 hp)
  have hle := w135c2_card_le_of_generation W h2 L hirr hL T hT c hc
  rw [hk] at hle
  have hk' : k ≤ T.card * c := (Nat.pow_le_pow_iff_right (by norm_num)).1 hle
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  simpa [rk, hk] using hk'

private theorem w135c2_fixV_conj {W : Type} [CommGroup W] (g x : MulAut W) :
    fixV (Subgroup.zpowers (g * x * g⁻¹)) =
      (fixV (Subgroup.zpowers x)).map (g : W →* W) := by
  ext v
  rw [Subgroup.mem_map]
  have key : ∀ (u : W) (t : MulAut W), u ∈ fixV (Subgroup.zpowers t) ↔ t u = u := by
    intro u t
    rw [show u ∈ fixV (Subgroup.zpowers t) ↔
        Subgroup.zpowers t ≤ MulAction.stabilizer (MulAut W) u by
      simp only [mem_fixV, SetLike.le_def, MulAction.mem_stabilizer_iff, MulAut.smul_def]]
    rw [Subgroup.zpowers_le, MulAction.mem_stabilizer_iff, MulAut.smul_def]
  constructor
  · intro hv
    refine ⟨g⁻¹ v, ?_, by simp⟩
    rw [key]
    have h2 := congrArg (fun w => g⁻¹ w) ((key v (g * x * g⁻¹)).1 hv)
    simpa using h2
  · rintro ⟨u, hu, rfl⟩
    rw [key]
    have h2 := congrArg g ((key u x).1 hu)
    simpa using h2

theorem w135c2_mQuot_conj {W : Type} [CommGroup W] [Finite W] (g x : MulAut W) :
    E3.mQuot ⊤ (fixV (Subgroup.zpowers (g * x * g⁻¹))) =
      E3.mQuot ⊤ (fixV (Subgroup.zpowers x)) := by
  rw [w135c2_fixV_conj g x]
  simp only [E3.mQuot, Subgroup.relIndex_top_right]
  rw [Subgroup.index_map_equiv]

theorem w135c2_rk_le_mul_of_conj_gen {W : Type} [CommGroup W] [Finite W] {L : Subgroup (MulAut W)}
    {t : MulAut W} (hW : ∀ w : W, w ^ 2 = 1) (hirr : IsIrrOn L ⊤ ⊥) (hL : L ≠ ⊥)
    (T : Finset (MulAut W)) (hT : ∀ x ∈ T, ∃ g ∈ L, x = g * t * g⁻¹)
    (hgen : L ≤ Subgroup.closure (T : Set (MulAut W))) {A : ℕ} (hA : T.card ≤ A) :
    rk W ≤ A * E3.mQuot ⊤ (fixV (Subgroup.zpowers t)) := by
  let c := E3.mQuot ⊤ (fixV (Subgroup.zpowers t))
  have hc : ∀ x ∈ T, E3.mQuot ⊤ (fixV (Subgroup.zpowers x)) ≤ c := by
    intro x hx
    obtain ⟨g, -, rfl⟩ := hT x hx
    rw [w135c2_mQuot_conj g t]
  have hle := w135c2_rk_le_of_generation W hW L hirr hL T hgen c hc
  calc rk W ≤ T.card * c := hle
    _ ≤ A * c := Nat.mul_le_mul_right c hA

end CFSG.LocalAnalysis.WeakClosure81
