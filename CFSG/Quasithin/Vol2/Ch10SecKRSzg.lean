module

public import CFSG.Quasithin.Vol2.Ch10SecKRSzf
public import CFSG.Quasithin.Vol2.Ch10SecKRSze

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecC.KRS

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.H13 CFSG.QuasithinUnique C10P4F
open scoped Matrix

theorem transpose_mulVec_eq {M : Matrix (Fin 5) (Fin 5) (ZMod 2)} {w : Fin 5 → ZMod 2}
    {S : Fin 5 → Prop} [DecidablePred S] (hM : ∀ a c, S a → M a c = if a = c then 1 else 0)
    (hw : ∀ a, ¬ S a → w a = 0) : Mᵀ *ᵥ w = w := by
  funext c
  rw [Matrix.mulVec, dotProduct, Finset.sum_eq_single c]
  · by_cases hc : S c
    · rw [Matrix.transpose_apply, hM c c hc, ite_eq_left rfl, one_mul]
    · rw [hw c hc, mul_zero]
  · intro a _ hac
    by_cases ha : S a
    · rw [Matrix.transpose_apply, hM a c ha, ite_eq_right hac, zero_mul]
    · rw [hw a ha, mul_zero]
  · simp

theorem entry_eq_smul (g : SL5) (a c : Fin 5) :
    (g : Matrix (Fin 5) (Fin 5) (ZMod 2)) a c = (g • (Pi.single c 1 : Fin 5 → ZMod 2)) a := by
  rw [smul_eq_mulVec', Matrix.mulVec_single_one]
  rfl

theorem trvE_mem_X2 (b : Fin 5) (hb : 2 ≤ (b : ℕ)) (h : (0 : Fin 5) ≠ b) : trvE 0 b h ∈ X2 := by
  fin_cases b
  · simp at hb
  · simp at hb
  · exact ⟨by unfold PresStd; decide +revert, by decide +revert⟩
  · exact ⟨by unfold PresStd; decide +revert, by decide +revert⟩
  · exact ⟨by unfold PresStd; decide +revert, by decide +revert⟩

theorem trvE_mem_X3 (a : Fin 5) (ha : (a : ℕ) < 3) (h : a ≠ 3) : trvE a 3 h ∈ X3 := by
  fin_cases a
  · exact ⟨by unfold PresStd; decide +revert, by decide +revert⟩
  · exact ⟨by unfold PresStd; decide +revert, by decide +revert⟩
  · exact ⟨by unfold PresStd; decide +revert, by decide +revert⟩
  · simp at ha
  · simp at ha

theorem trvE_mem_X14_left (b : Fin 5) (h : (0 : Fin 5) ≠ b) : trvE 0 b h ∈ X14 := by
  fin_cases b
  · exact absurd rfl h
  all_goals exact mem_X14_of (by unfold PresStd; decide +revert) (by unfold PresStd; decide +revert)

theorem trvE_mem_X14_right (a : Fin 5) (h : a ≠ 4) : trvE a 4 h ∈ X14 := by
  fin_cases a
  · exact mem_X14_of (by unfold PresStd; decide +revert) (by unfold PresStd; decide +revert)
  · exact mem_X14_of (by unfold PresStd; decide +revert) (by unfold PresStd; decide +revert)
  · exact mem_X14_of (by unfold PresStd; decide +revert) (by unfold PresStd; decide +revert)
  · exact mem_X14_of (by unfold PresStd; decide +revert) (by unfold PresStd; decide +revert)
  · exact absurd rfl h

theorem smul_single_four {X : Subgroup SL5} (hX4 : InvStd X 4) {y : SL5} (hy : y ∈ X)
    (c : Fin 5) :
    (y • (Pi.single c 1 : Fin 5 → ZMod 2)) 4 = if (4 : Fin 5) = c then 1 else 0 := by
  by_cases hc : (4 : Fin 5) = c
  · subst hc
    rw [ite_eq_left rfl]
    by_contra h0
    have h0' : (y • (Pi.single 4 1 : Fin 5 → ZMod 2)) 4 = 0 := by
      rcases zmod2_cases ((y • (Pi.single 4 1 : Fin 5 → ZMod 2)) 4) with h | h
      · exact h
      · exact absurd h h0
    have hm : y • (Pi.single 4 1 : Fin 5 → ZMod 2) ∈ stdE 5 4 := fun i hi => by
      have : i = 4 := Fin.ext (by have := i.2; omega)
      rw [this]
      exact h0'
    have hm' := hX4 _ (X.inv_mem hy) _ hm
    rw [inv_smul_smul] at hm'
    have := hm' 4 le_rfl
    simp at this
  · rw [ite_eq_right hc]
    have hm : (Pi.single c 1 : Fin 5 → ZMod 2) ∈ stdE 5 4 := single_mem_stdE (by
      have := c.2
      have : (c : ℕ) ≠ 4 := fun h => hc (Fin.ext h.symm)
      omega)
    exact hX4 y hy _ hm 4 le_rfl

variable {G : Type} [Group G] [Finite G] {T L I J : Subgroup G} {t w : G}

theorem Conf.lift_trvE (c : Conf T L I t w J) (h1011 : Stmt10_1_1) (ρ : ↥J →* SL5)
    (hker : ∀ j : ↥J, ρ j = 1 → ∃ m : ℕ, (j : G) ^ 2 ^ m = 1) {m : ℕ}
    (hX : InvStd (piL ρ c.le).range m) {a b : Fin 5} (hab : a ≠ b) (ha : (a : ℕ) < m)
    (hb : m ≤ (b : ℕ)) (hmem : trvE a b hab ∈ (piL ρ c.le).range) :
    ∃ l : ↥L, piL ρ c.le l = trvE a b hab ∧
      (l : G) ∈ Subgroup.centralizer (fsuUL T L I : Set G) := by
  refine Conf.exists_lift_of_rad c h1011 ρ hker (N := (piL ρ c.le).range ⊓ radE m) inf_le_left
    (fun x hx => mem_normalizer_of_conj_mem fun n hn =>
      ⟨Subgroup.mul_mem _ (Subgroup.mul_mem _ hx hn.1) (Subgroup.inv_mem _ hx),
        conj_mem_radE hX hx hn.2⟩) (fun n => ⟨1, Subtype.ext ?_⟩) ⟨hmem, trvE_mem_radE hab ha hb⟩
  rw [pow_one, pow_two]
  exact mul_self_of_mem_radE n.2.2

theorem Conf.lift_trvE14 (c : Conf T L I t w J) (h1011 : Stmt10_1_1) (ρ : ↥J →* SL5)
    (hker : ∀ j : ↥J, ρ j = 1 → ∃ m : ℕ, (j : G) ^ 2 ^ m = 1)
    (h1 : InvStd (piL ρ c.le).range 1) (h4 : InvStd (piL ρ c.le).range 4) {g : SL5}
    (hg : g ∈ rad14) (hmem : g ∈ (piL ρ c.le).range) :
    ∃ l : ↥L, piL ρ c.le l = g ∧ (l : G) ∈ Subgroup.centralizer (fsuUL T L I : Set G) := by
  refine Conf.exists_lift_of_rad c h1011 ρ hker (N := (piL ρ c.le).range ⊓ rad14) inf_le_left
    (fun x hx => mem_normalizer_of_conj_mem fun n hn =>
      ⟨Subgroup.mul_mem _ (Subgroup.mul_mem _ hx hn.1) (Subgroup.inv_mem _ hx),
        conj_mem_rad14 h1 h4 hx hn.2⟩) (fun n => ⟨2, Subtype.ext ?_⟩) ⟨hmem, hg⟩
  exact pow_four_of_mem_rad14 n.2.2

omit [Finite G] in
theorem conj_eq_of_mem_centralizer {X : Subgroup G} {l v : G}
    (hl : l ∈ Subgroup.centralizer (X : Set G)) (hv : v ∈ X) : l * v * l⁻¹ = v := by
  rw [← Subgroup.mem_centralizer_iff.mp hl v hv, mul_inv_cancel_right]

theorem Conf.false_of_multi_E2 (c : Conf T L I t w J) (h1011 : Stmt10_1_1) {k : ℕ}
    (C : MultiCoord J (VI T L I J w) k) (hV1W : fsuUL T L I ≤ VI T L I J w)
    (hker : ∀ j : ↥J, C.ρ j = 1 → ∃ m : ℕ, (j : G) ^ 2 ^ m = 1)
    (h2 : InvStd (piL C.ρ c.le).range 2)
    (htriv : ∀ x ∈ (piL C.ρ c.le).range, ∀ v ∈ stdE 5 2, x • v = v)
    (hX : (piL C.ρ c.le).range = X2) {i₀ : Fin k} (hi₀ : C.dual i₀ = false) : False := by
  have hE2 : ∀ v ∈ fsuUL T L I, ∀ i, C.dual i = false → C.E v i ∈ stdE 5 2 := by
    intro v hv i hi b hb
    have hb0 : (0 : Fin 5) ≠ b := fun h => by rw [← h] at hb; simp at hb
    obtain ⟨l, hlρ, hlC⟩ := Conf.lift_trvE c h1011 C.ρ hker h2 hb0 (by norm_num) hb
      (by rw [hX]; exact trvE_mem_X2 b hb hb0)
    exact C.comp_eq_zero_nat (hV1W hv) (j := ⟨l, c.le l.2⟩)
      (conj_eq_of_mem_centralizer hlC hv) hb0 hlρ hi
  refine Conf.false_of_multi_triv c C hV1W (fun i => C.dual i = false) hi₀
    fun v hv l hl i hi => ?_
  rw [show l * v * l⁻¹ = ((⟨l, c.le hl⟩ : ↥J) : G) * v * ((⟨l, c.le hl⟩ : ↥J) : G)⁻¹ from rfl,
    C.conj _ v (hV1W hv) i, hi, tw_false, ← smul_eq_mulVec']
  exact htriv _ ⟨⟨l, hl⟩, rfl⟩ _ (hE2 v hv i hi)

theorem Conf.false_of_multi_flag (c : Conf T L I t w J) (h1011 : Stmt10_1_1) {k : ℕ}
    (C : MultiCoord J (VI T L I J w) k) (hV1W : fsuUL T L I ≤ VI T L I J w)
    (hker : ∀ j : ↥J, C.ρ j = 1 → ∃ m : ℕ, (j : G) ^ 2 ^ m = 1)
    (h1 : InvStd (piL C.ρ c.le).range 1) (h4 : InvStd (piL C.ρ c.le).range 4)
    (hfix : fixN (piL C.ρ c.le).range = stdE 5 1) (hX : (piL C.ρ c.le).range = X14)
    (i₀ : Fin k) : False := by
  have hnat : ∀ v ∈ fsuUL T L I, ∀ i, C.dual i = false → C.E v i ∈ stdE 5 1 := by
    intro v hv i hi b hb
    have hb0 : (0 : Fin 5) ≠ b := fun h => by rw [← h] at hb; simp at hb
    obtain ⟨l, hlρ, hlC⟩ := Conf.lift_trvE14 c h1011 C.ρ hker h1 h4 (trvE_mem_rad14_left hb0)
      (by rw [hX]; exact trvE_mem_X14_left b hb0)
    exact C.comp_eq_zero_nat (hV1W hv) (j := ⟨l, c.le l.2⟩)
      (conj_eq_of_mem_centralizer hlC hv) hb0 hlρ hi
  have hdual : ∀ v ∈ fsuUL T L I, ∀ i, C.dual i = true → ∀ a : Fin 5, a ≠ 4 →
      C.E v i a = 0 := by
    intro v hv i hi a ha
    obtain ⟨l, hlρ, hlC⟩ := Conf.lift_trvE14 c h1011 C.ρ hker h1 h4 (trvE_mem_rad14_right ha)
      (by rw [hX]; exact trvE_mem_X14_right a ha)
    exact C.comp_eq_zero_dual (hV1W hv) (j := ⟨l, c.le l.2⟩)
      (conj_eq_of_mem_centralizer hlC hv) ha hlρ hi
  refine Conf.false_of_multi_triv c C hV1W (fun _ => True) (i₀ := i₀) trivial
    fun v hv l hl i _ => ?_
  have hlX : C.ρ ⟨l, c.le hl⟩ ∈ (piL C.ρ c.le).range := ⟨⟨l, hl⟩, rfl⟩
  rw [show l * v * l⁻¹ = ((⟨l, c.le hl⟩ : ↥J) : G) * v * ((⟨l, c.le hl⟩ : ↥J) : G)⁻¹ from rfl,
    C.conj _ v (hV1W hv) i]
  cases hi : C.dual i
  · rw [tw_false, ← smul_eq_mulVec']
    have hm : C.E v i ∈ fixN (piL C.ρ c.le).range := by rw [hfix]; exact hnat v hv i hi
    exact hm _ hlX
  · rw [tw_true]
    refine transpose_mulVec_eq (S := fun a => a = 4) (fun a c' ha => ?_)
      (fun a ha => hdual v hv i hi a ha)
    subst ha
    rw [entry_eq_smul, smul_single_four h4 (Subgroup.inv_mem _ hlX)]

theorem Conf.false_of_multi_E3_dual (c : Conf T L I t w J) (h1011 : Stmt10_1_1) {k : ℕ}
    (C : MultiCoord J (VI T L I J w) k) (hV1W : fsuUL T L I ≤ VI T L I J w)
    (hker : ∀ j : ↥J, C.ρ j = 1 → ∃ m : ℕ, (j : G) ^ 2 ^ m = 1)
    (h3 : InvStd (piL C.ρ c.le).range 3)
    (htriv : ∀ x ∈ (piL C.ρ c.le).range, ∀ v, x • v + v ∈ stdE 5 3)
    (hX : (piL C.ρ c.le).range = X3) {i₀ : Fin k} (hi₀ : C.dual i₀ = true) : False := by
  have hdual : ∀ v ∈ fsuUL T L I, ∀ i, C.dual i = true → ∀ a : Fin 5, (a : ℕ) < 3 →
      C.E v i a = 0 := by
    intro v hv i hi a ha
    have ha3 : a ≠ 3 := fun h => by rw [h] at ha; simp at ha
    obtain ⟨l, hlρ, hlC⟩ := Conf.lift_trvE c h1011 C.ρ hker h3 ha3 ha (by simp)
      (by rw [hX]; exact trvE_mem_X3 a ha ha3)
    exact C.comp_eq_zero_dual (hV1W hv) (j := ⟨l, c.le l.2⟩)
      (conj_eq_of_mem_centralizer hlC hv) ha3 hlρ hi
  refine Conf.false_of_multi_triv c C hV1W (fun i => C.dual i = true) hi₀
    fun v hv l hl i hi => ?_
  have hlX : C.ρ ⟨l, c.le hl⟩ ∈ (piL C.ρ c.le).range := ⟨⟨l, hl⟩, rfl⟩
  rw [show l * v * l⁻¹ = ((⟨l, c.le hl⟩ : ↥J) : G) * v * ((⟨l, c.le hl⟩ : ↥J) : G)⁻¹ from rfl,
    C.conj _ v (hV1W hv) i, hi, tw_true]
  refine transpose_mulVec_eq (S := fun a => 3 ≤ (a : ℕ)) (fun a c' ha => ?_)
    (fun a ha => hdual v hv i hi a (by simp only [not_le] at ha; exact ha))
  rw [entry_eq_smul]
  have h1 := htriv _ (Subgroup.inv_mem _ hlX) (Pi.single c' 1) a ha
  rw [Pi.add_apply, Pi.single_apply] at h1
  have key : ∀ x y : ZMod 2, x + y = 0 → x = y := by decide
  rw [key _ _ h1]

end CFSG.Quasithin.Vol2.Ch10.SecC.KRS
