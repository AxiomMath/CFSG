module

public import CFSG.Quasithin.Vol2.Ch10SecKRSzg

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecC.KRS

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.H13 CFSG.QuasithinUnique C10P4F
open scoped Matrix

theorem trvE1_mem_X2 (b : Fin 5) (hb : 2 ≤ (b : ℕ)) (h : (1 : Fin 5) ≠ b) : trvE 1 b h ∈ X2 := by
  fin_cases b
  · simp at hb
  · simp at hb
  · exact ⟨by unfold PresStd; decide +revert, by decide +revert⟩
  · exact ⟨by unfold PresStd; decide +revert, by decide +revert⟩
  · exact ⟨by unfold PresStd; decide +revert, by decide +revert⟩

theorem row_eq_zero_of_two {B : Matrix (Fin 5) (Fin 5) (ZMod 2)} {b : Fin 5}
    (h0 : (0 : Fin 5) ≠ b) (h1 : (1 : Fin 5) ≠ b)
    (hB0 : (trvE 0 b h0 : Matrix (Fin 5) (Fin 5) (ZMod 2)) * B *
      (trvE 0 b h0 : Matrix (Fin 5) (Fin 5) (ZMod 2))ᵀ = B)
    (hB1 : (trvE 1 b h1 : Matrix (Fin 5) (Fin 5) (ZMod 2)) * B *
      (trvE 1 b h1 : Matrix (Fin 5) (Fin 5) (ZMod 2))ᵀ = B) (c : Fin 5) : B b c = 0 := by
  by_cases hc : c = 0
  · subst hc
    exact row_eq_zero_of_trvE h1 hB1 (by decide)
  · exact row_eq_zero_of_trvE h0 hB0 hc

theorem alt_eq_of_entries {B B' : Matrix (Fin 5) (Fin 5) (ZMod 2)} (hB : B ∈ altMat 5)
    (hB' : B' ∈ altMat 5)
    (hP : ∀ a b : Fin 5, 1 ≤ (a : ℕ) → 1 ≤ (b : ℕ) → ¬ ((a : ℕ) + b = 3) → B a b = 0)
    (hP' : ∀ a b : Fin 5, 1 ≤ (a : ℕ) → 1 ≤ (b : ℕ) → ¬ ((a : ℕ) + b = 3) → B' a b = 0)
    (h10 : B 1 0 = B' 1 0) (h20 : B 2 0 = B' 2 0) (h21 : B 2 1 = B' 2 1) (h30 : B 3 0 = B' 3 0)
    (h40 : B 4 0 = B' 4 0) : B = B' := by
  obtain ⟨hs, hd⟩ := mem_altMat.mp hB
  obtain ⟨hs', hd'⟩ := mem_altMat.mp hB'
  have hsym : ∀ a b, B a b = B b a := fun a b => by
    have := congrFun (congrFun hs b) a
    simpa using this
  have hsym' : ∀ a b, B' a b = B' b a := fun a b => by
    have := congrFun (congrFun hs' b) a
    simpa using this
  ext a b
  fin_cases a <;> fin_cases b <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk] <;>
    first
      | rw [hd, hd']
      | exact h10 | exact h20 | exact h21 | exact h30 | exact h40
      | rw [hsym, hsym' 0]; first | exact h10 | exact h20 | exact h30 | exact h40
      | rw [hsym, hsym' 1]; exact h21
      | rw [hP _ _ (by decide) (by decide) (by decide), hP' _ _ (by decide) (by decide) (by decide)]

theorem alt_eq_B0_or_zero {B : Matrix (Fin 5) (Fin 5) (ZMod 2)} (hB : B ∈ altMat 5)
    (hrow : ∀ b : Fin 5, 2 ≤ (b : ℕ) → ∀ c, B b c = 0) : B = 0 ∨ B = B0 := by
  obtain ⟨hs, hd⟩ := mem_altMat.mp hB
  have hsym : ∀ a b, B a b = B b a := fun a b => by
    have := congrFun (congrFun hs b) a
    simpa using this
  have r2 := hrow 2 (by norm_num)
  have r3 := hrow 3 (by norm_num)
  have r4 := hrow 4 (by norm_num)
  have e01 := hsym 0 1
  rcases zmod2_cases (B 1 0) with h0 | h0
  · left
    ext a b
    fin_cases a <;> fin_cases b <;> simp [r2, r3, r4, h0, e01, hd, hsym 0 2, hsym 0 3, hsym 0 4,
      hsym 1 2, hsym 1 3, hsym 1 4]
  · right
    ext a b
    fin_cases a <;> fin_cases b <;> simp [r2, r3, r4, h0, e01, hd, hsym 0 2, hsym 0 3, hsym 0 4,
      hsym 1 2, hsym 1 3, hsym 1 4, B0]

variable {G : Type} [Group G] [Finite G] {T L I J : Subgroup G} {t w : G}

theorem Conf.false_of_alt_triv (c : Conf T L I t w J) (C : AltCoord J (VI T L I J w))
    (hV1W : fsuUL T L I ≤ VI T L I J w)
    (hS : ∀ v ∈ fsuUL T L I, ∀ l ∈ L, C.E (l * v * l⁻¹) = C.E v) : False := by
  have hbot : fsuUL T L I ≤ ⊥ := by
    rw [← commutator_fsuUL_eq c.hyp, Subgroup.commutator_le]
    intro v hv l hl
    have hvW := hV1W hv
    have hlv : l * v * l⁻¹ ∈ VI T L I J w :=
      (Subgroup.mem_normalizer_iff.mp (C.le (c.le hl)) v).mp hvW
    have h1 : l * v * l⁻¹ = v := C.inj _ hlv v hvW (hS v hv l hl)
    rw [Subgroup.mem_bot, commutatorElement_def,
      show v * l * v⁻¹ * l⁻¹ = v * (l * v * l⁻¹)⁻¹ by group, h1, mul_inv_cancel]
  exact Conf.u_ne_one c (Subgroup.mem_bot.mp (hbot (Conf.u_mem_fsuUL c)))

theorem Conf.alt_fix_of_lift (c : Conf T L I t w J) (C : AltCoord J (VI T L I J w))
    (hV1W : fsuUL T L I ≤ VI T L I J w) {l : ↥L}
    (hl : (l : G) ∈ Subgroup.centralizer (fsuUL T L I : Set G)) {v : G} (hv : v ∈ fsuUL T L I) :
    (C.ρ ⟨l, c.le l.2⟩ : Matrix (Fin 5) (Fin 5) (ZMod 2)) * C.E v *
      (C.ρ ⟨l, c.le l.2⟩ : Matrix (Fin 5) (Fin 5) (ZMod 2))ᵀ = C.E v := by
  rw [← C.conj ⟨l, c.le l.2⟩ v (hV1W hv)]
  exact congrArg C.E (conj_eq_of_mem_centralizer hl hv)

theorem Conf.false_of_alt_E2 (c : Conf T L I t w J) (h1011 : Stmt10_1_1)
    (C : AltCoord J (VI T L I J w)) (hV1W : fsuUL T L I ≤ VI T L I J w)
    (hker : ∀ j : ↥J, C.ρ j = 1 → ∃ m : ℕ, (j : G) ^ 2 ^ m = 1)
    (h2 : InvStd (piL C.ρ c.le).range 2)
    (htriv : ∀ x ∈ (piL C.ρ c.le).range, ∀ v ∈ stdE 5 2, x • v = v)
    (hX : (piL C.ρ c.le).range = X2) : False := by
  have hrow : ∀ v ∈ fsuUL T L I, ∀ b : Fin 5, 2 ≤ (b : ℕ) → ∀ c', C.E v b c' = 0 := by
    intro v hv b hb c'
    have hb0 : (0 : Fin 5) ≠ b := fun h => by rw [← h] at hb; simp at hb
    have hb1 : (1 : Fin 5) ≠ b := fun h => by rw [← h] at hb; simp at hb
    obtain ⟨l₀, hl₀ρ, hl₀C⟩ := Conf.lift_trvE c h1011 C.ρ hker h2 hb0 (by norm_num) hb
      (by rw [hX]; exact trvE_mem_X2 b hb hb0)
    obtain ⟨l₁, hl₁ρ, hl₁C⟩ := Conf.lift_trvE c h1011 C.ρ hker h2 hb1 (by norm_num) hb
      (by rw [hX]; exact trvE1_mem_X2 b hb hb1)
    have e0 := Conf.alt_fix_of_lift c C hV1W hl₀C hv
    have e1 := Conf.alt_fix_of_lift c C hV1W hl₁C hv
    rw [show C.ρ ⟨l₀, c.le l₀.2⟩ = trvE 0 b hb0 from hl₀ρ] at e0
    rw [show C.ρ ⟨l₁, c.le l₁.2⟩ = trvE 1 b hb1 from hl₁ρ] at e1
    exact row_eq_zero_of_two hb0 hb1 e0 e1 c'
  refine Conf.false_of_alt_triv c C hV1W fun v hv l hl => ?_
  have hlX : C.ρ ⟨l, c.le hl⟩ ∈ (piL C.ρ c.le).range := ⟨⟨l, hl⟩, rfl⟩
  rw [show l * v * l⁻¹ = ((⟨l, c.le hl⟩ : ↥J) : G) * v * ((⟨l, c.le hl⟩ : ↥J) : G)⁻¹ from rfl,
    C.conj _ v (hV1W hv)]
  have hx : ∀ (a : Fin 5) (b : Fin 5), (b : ℕ) < 2 →
      (C.ρ ⟨l, c.le hl⟩ : Matrix (Fin 5) (Fin 5) (ZMod 2)) a b = if a = b then 1 else 0 :=
    fun a b hb => by
      rw [entry_eq_smul, htriv _ hlX _ (single_mem_stdE hb), Pi.single_apply]
  rcases alt_eq_B0_or_zero (C.mem v) (hrow v hv) with h | h <;> rw [h]
  · simp
  · ext a b
    rw [conj_B0_apply, hx a 0 (by norm_num), hx a 1 (by norm_num), hx b 0 (by norm_num),
      hx b 1 (by norm_num)]
    fin_cases a <;> fin_cases b <;> rfl

theorem Conf.false_of_alt_five (c : Conf T L I t w J) (h5 : Case10_1_1Five T L I)
    (C : AltCoord J (VI T L I J w)) (hV1W : fsuUL T L I ≤ VI T L I J w)
    (hP : ∀ v ∈ fsuUL T L I, ∀ a b : Fin 5, 1 ≤ (a : ℕ) → 1 ≤ (b : ℕ) → ¬ ((a : ℕ) + b = 3) →
      C.E v a b = 0) : False := by
  have h64 := card_fsuUL_of_case5 c.hyp h5
  let f : ↥(fsuUL T L I) → (Fin 5 → ZMod 2) := fun v =>
    ![C.E v 1 0, C.E v 2 0, C.E v 2 1, C.E v 3 0, C.E v 4 0]
  have hf : Function.Injective f := fun v v' h => by
    have h' := fun i => congrFun h i
    exact Subtype.ext (C.inj _ (hV1W v.2) _ (hV1W v'.2) (alt_eq_of_entries (C.mem v) (C.mem v')
      (hP v v.2) (hP v' v'.2) (h' 0) (h' 1) (h' 2) (h' 3) (h' 4)))
  have h1 := Nat.card_le_card_of_injective f hf
  rw [h64, Nat.card_eq_fintype_card] at h1
  simp at h1

end CFSG.Quasithin.Vol2.Ch10.SecC.KRS
