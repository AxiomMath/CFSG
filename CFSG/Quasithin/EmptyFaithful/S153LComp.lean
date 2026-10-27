module

public import CFSG.Quasithin.EmptyFaithful.SBc3List
public import CFSG.Quasithin.EmptyFaithful.T1515dB
public import CFSG.LocalAnalysis.ComponentInitial.TwoPrimeSolvable

public section

namespace CFSG.Quasithin

open CFSG.Open hiding StatedSL StatedClassicalModel StatedProj StatedLieTag StatedLieAdmissible
open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Assembly.LowTwoRank
open scoped commutatorElement IsMulCommutative

namespace S153L

section Commuting

variable {Ω : Type*} [Group Ω]

theorem comp_comm_mul {x₁ y₁ x₂ y₂ : Ω} (h₁₁ : Commute x₁ y₁) (h₁₂ : Commute x₁ y₂)
    (h₂₁ : Commute x₂ y₁) (h₂₂ : Commute x₂ y₂) :
    ⁅x₁ * y₁, x₂ * y₂⁆ = ⁅x₁, x₂⁆ * ⁅y₁, y₂⁆ := by
  have c1 : Commute x₁⁻¹ (y₁ * y₂ * y₁⁻¹) :=
    (h₁₁.inv_left.mul_right h₁₂.inv_left).mul_right h₁₁.inv_left.inv_right
  have c2 : Commute x₂⁻¹ (y₁ * y₂ * y₁⁻¹ * y₂⁻¹) :=
    ((h₂₁.inv_left.mul_right h₂₂.inv_left).mul_right h₂₁.inv_left.inv_right).mul_right
      h₂₂.inv_left.inv_right
  have e0 : y₁ * x₂ = x₂ * y₁ := h₂₁.symm.eq
  simp only [commutatorElement_def, mul_inv_rev]
  calc x₁ * y₁ * (x₂ * y₂) * (y₁⁻¹ * x₁⁻¹) * (y₂⁻¹ * x₂⁻¹)
      = x₁ * (y₁ * x₂) * y₂ * y₁⁻¹ * x₁⁻¹ * y₂⁻¹ * x₂⁻¹ := by group
    _ = x₁ * (x₂ * y₁) * y₂ * y₁⁻¹ * x₁⁻¹ * y₂⁻¹ * x₂⁻¹ := by rw [e0]
    _ = x₁ * x₂ * ((y₁ * y₂ * y₁⁻¹) * x₁⁻¹) * y₂⁻¹ * x₂⁻¹ := by group
    _ = x₁ * x₂ * (x₁⁻¹ * (y₁ * y₂ * y₁⁻¹)) * y₂⁻¹ * x₂⁻¹ := by rw [c1.eq.symm]
    _ = x₁ * x₂ * x₁⁻¹ * ((y₁ * y₂ * y₁⁻¹ * y₂⁻¹) * x₂⁻¹) := by group
    _ = x₁ * x₂ * x₁⁻¹ * (x₂⁻¹ * (y₁ * y₂ * y₁⁻¹ * y₂⁻¹)) := by rw [c2.eq.symm]
    _ = x₁ * x₂ * x₁⁻¹ * x₂⁻¹ * (y₁ * y₂ * y₁⁻¹ * y₂⁻¹) := by group

theorem comp_exists_mul {A B : Subgroup Ω} (hc : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) {g : Ω}
    (hg : g ∈ A ⊔ B) : ∃ a ∈ A, ∃ b ∈ B, g = a * b := by
  let S : Subgroup Ω :=
    { carrier := {g | ∃ a ∈ A, ∃ b ∈ B, g = a * b}
      one_mem' := ⟨1, A.one_mem, 1, B.one_mem, by simp⟩
      mul_mem' := by
        rintro _ _ ⟨a, ha, b, hb, rfl⟩ ⟨a', ha', b', hb', rfl⟩
        refine ⟨a * a', A.mul_mem ha ha', b * b', B.mul_mem hb hb', ?_⟩
        have e : b * a' = a' * b := (hc a' ha' b hb).symm
        calc a * b * (a' * b') = a * (b * a') * b' := by group
          _ = a * (a' * b) * b' := by rw [e]
          _ = a * a' * (b * b') := by group
      inv_mem' := by
        rintro _ ⟨a, ha, b, hb, rfl⟩
        refine ⟨a⁻¹, A.inv_mem ha, b⁻¹, B.inv_mem hb, ?_⟩
        have e : b⁻¹ * a⁻¹ = a⁻¹ * b⁻¹ := by
          have := hc a⁻¹ (A.inv_mem ha) b⁻¹ (B.inv_mem hb)
          exact this.symm
        calc (a * b)⁻¹ = b⁻¹ * a⁻¹ := by group
          _ = a⁻¹ * b⁻¹ := e }
  have hle : A ⊔ B ≤ S := sup_le (fun a ha => ⟨a, ha, 1, B.one_mem, by simp⟩)
    (fun b hb => ⟨1, A.one_mem, b, hb, by simp⟩)
  exact hle hg

theorem comp_commutator_sup_le {X Y : Subgroup Ω} (hc : ∀ a ∈ X, ∀ b ∈ Y, a * b = b * a) :
    ⁅X ⊔ Y, X ⊔ Y⁆ ≤ ⁅X, X⁆ ⊔ ⁅Y, Y⁆ := by
  refine Subgroup.commutator_le.mpr fun g hg h hh => ?_
  obtain ⟨x₁, hx₁, y₁, hy₁, rfl⟩ := comp_exists_mul hc hg
  obtain ⟨x₂, hx₂, y₂, hy₂, rfl⟩ := comp_exists_mul hc hh
  rw [comp_comm_mul (hc x₁ hx₁ y₁ hy₁) (hc x₁ hx₁ y₂ hy₂) (hc x₂ hx₂ y₁ hy₁) (hc x₂ hx₂ y₂ hy₂)]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (Subgroup.commutator_mem_commutator hx₁ hx₂))
    (Subgroup.mem_sup_right (Subgroup.commutator_mem_commutator hy₁ hy₂))

end Commuting

section Perfect

variable {Ω : Type} [Group Ω] [Finite Ω]

omit [Finite Ω] in
theorem comp_derived_sup_le {A B : Subgroup Ω} (hc : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) (n : ℕ) :
    derivedSeriesOf (A ⊔ B) n ≤ derivedSeriesOf A n ⊔ derivedSeriesOf B n := by
  induction n with
  | zero => exact le_rfl
  | succ n ih =>
    rw [derivedSeriesOf_succ, derivedSeriesOf_succ, derivedSeriesOf_succ]
    refine (Subgroup.commutator_mono ih ih).trans ?_
    exact comp_commutator_sup_le fun a ha b hb =>
      hc a (derivedSeriesOf_le A n ha) b (derivedSeriesOf_le B n hb)

theorem comp_perfectCore_sup_le {A B : Subgroup Ω} (hc : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) :
    perfectCore (A ⊔ B) ≤ perfectCore A ⊔ perfectCore B := by
  obtain ⟨n₁, h₁⟩ := exists_perfectCore_eq A
  obtain ⟨n₂, h₂⟩ := exists_perfectCore_eq B
  have := (perfectCore_le_derivedSeriesOf (A ⊔ B) (max n₁ n₂)).trans
    (comp_derived_sup_le hc (max n₁ n₂))
  rwa [← h₁ _ (le_max_left _ _), ← h₂ _ (le_max_right _ _)] at this

theorem perfect_le_sup_of_commute {G₁ G₂ N₁ N₂ P : Subgroup Ω}
    (hc : ∀ a ∈ G₁, ∀ b ∈ G₂, a * b = b * a)
    (h₁ : ∀ Q ≤ G₁, ⁅Q, Q⁆ = Q → Q ≤ N₁) (h₂ : ∀ Q ≤ G₂, ⁅Q, Q⁆ = Q → Q ≤ N₂)
    (hP : P ≤ G₁ ⊔ G₂) (hPp : ⁅P, P⁆ = P) : P ≤ N₁ ⊔ N₂ :=
  (le_perfectCore_of_perfect hP hPp).trans ((comp_perfectCore_sup_le hc).trans
    (sup_le_sup (h₁ _ (perfectCore_le _) (perfectCore_perfect _))
      (h₂ _ (perfectCore_le _) (perfectCore_perfect _))))

omit [Finite Ω] in
theorem comp_perfect_of_isQuasisimple {N : Subgroup Ω} (hq : CFSG.IsQuasisimple ↥N) : ⁅N, N⁆ = N :=
  le_antisymm (A3.commutator_self_le N) (InternalSec.le_commutator_of_perfect le_rfl hq.1)

omit [Finite Ω] in
theorem comp_isComponentOf {J N : Subgroup Ω} (hNJ : N ≤ J)
    (hn : ∀ x ∈ J, ∀ n ∈ N, x * n * x⁻¹ ∈ N) (hq : CFSG.IsQuasisimple ↥N) :
    CFSG.GorensteinWalter.IsComponentOf N J :=
  ⟨hNJ, SBc3.isSubnormal_subgroupOf
    (A3.subnormal_of_normal hNJ ((Subgroup.normal_subgroupOf_iff hNJ).2 fun h k hh hk => hn k hk h hh)),
    SBc3.gwQuasisimple hq⟩

theorem comp_dichotomy {J N K : Subgroup Ω} (hK : K ∈ cComp J) (hNJ : N ≤ J)
    (hn : ∀ x ∈ J, ∀ n ∈ N, x * n * x⁻¹ ∈ N) (hq : N = ⊥ ∨ CFSG.IsQuasisimple ↥N) :
    K = N ∨ ⁅N, K⁆ = ⊥ := by
  rcases hq with rfl | hq
  · exact Or.inr (Subgroup.commutator_bot_left K)
  · have hcomp := comp_isComponentOf hNJ hn hq
    have hKJ : K ≤ J := le_of_mem_cComp hK
    rcases CFSG.GorensteinWalter.fstar_component_le_or_commutator_eq_bot_of_subnormal_subgroupOf
      hKJ (SBc3.isSubnormal_subgroupOf (subnormal_of_mem_cComp hK)) hcomp with hNK | hc
    · left
      by_contra hne
      refine not_subnormal_of_mem_cComp hK (lt_of_le_of_ne hNK (Ne.symm hne))
        (SBc3.ne_bot_of_isQuasisimple hq) (comp_perfect_of_isQuasisimple hq) ?_
      exact A3.subnormal_of_normal hNJ ((Subgroup.normal_subgroupOf_iff hNJ).2 fun h k hh hk => hn k hk h hh)
    · exact Or.inr hc

theorem comp_cq {J N₁ N₂ K : Subgroup Ω} (hK : K ∈ cComp J) (hKN : K ≤ N₁ ⊔ N₂)
    (hN₁J : N₁ ≤ J) (hn₁ : ∀ x ∈ J, ∀ n ∈ N₁, x * n * x⁻¹ ∈ N₁)
    (hq₁ : N₁ = ⊥ ∨ CFSG.IsQuasisimple ↥N₁)
    (hN₂J : N₂ ≤ J) (hn₂ : ∀ x ∈ J, ∀ n ∈ N₂, x * n * x⁻¹ ∈ N₂)
    (hq₂ : N₂ = ⊥ ∨ CFSG.IsQuasisimple ↥N₂) : K = N₁ ∨ K = N₂ := by
  by_contra hne
  push Not at hne
  have h1 : ⁅N₁, K⁆ = ⊥ := (comp_dichotomy hK hN₁J hn₁ hq₁).resolve_left hne.1
  have h2 : ⁅N₂, K⁆ = ⊥ := (comp_dichotomy hK hN₂J hn₂ hq₂).resolve_left hne.2
  have hc1 : N₁ ≤ Subgroup.centralizer (K : Set Ω) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp h1
  have hc2 : N₂ ≤ Subgroup.centralizer (K : Set Ω) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp h2
  have hKc : K ≤ Subgroup.centralizer (K : Set Ω) := hKN.trans (sup_le hc1 hc2)
  have hKK : ⁅K, K⁆ = ⊥ := Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hKc
  have hperf := perfect_of_mem_cComp hK
  rw [hKK] at hperf
  exact ne_bot_of_mem_cComp hK hperf.symm

end Perfect

section Factors

variable {Ω : Type} [Group Ω] [Finite Ω]

@[expose] def FactorN (G N : Subgroup Ω) : Prop :=
  N ≤ G ∧ (∀ g ∈ G, ∀ n ∈ N, g * n * g⁻¹ ∈ N) ∧ (N = ⊥ ∨ CFSG.IsQuasisimple ↥N) ∧
    ∀ Q ≤ G, ⁅Q, Q⁆ = Q → Q ≤ N

omit [Finite Ω] in
theorem factorN_of_quasisimple {G : Subgroup Ω} (hq : CFSG.IsQuasisimple ↥G) : FactorN G G :=
  ⟨le_rfl, fun _ hg _ hn => G.mul_mem (G.mul_mem hg hn) (G.inv_mem hg), Or.inr hq, fun _ h _ => h⟩

theorem factorN_of_solvable {G : Subgroup Ω} (hs : Group.IsSolvable ↥G) : FactorN G ⊥ := by
  refine ⟨bot_le, fun _ _ _ hn => ?_, Or.inl rfl, fun Q hQG hQ => ?_⟩
  · rw [Subgroup.mem_bot] at hn ⊢
    simp [hn]
  · have hQs : Group.IsSolvable ↥Q :=
      Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hQG)
        (Subgroup.inclusion_injective hQG)
    have h1 := (isSolvable_iff_perfectCore_eq_bot Q).mp hQs
    rw [perfectCore_eq_self_of_perfect hQ] at h1
    rw [h1]

theorem comp_solvable_of_card_six {X : Type} [Group X] [Finite X] (h : Nat.card X = 6) :
    Group.IsSolvable X := by
  refine CFSG.LocalAnalysis.ComponentInitial.isSolvable_of_card_primeFactors_le_two ?_
  have h6 : Nat.primeFactors 6 = {2, 3} := by
    rw [show (6 : ℕ) = 2 * 3 by norm_num, Nat.primeFactors_mul (by norm_num) (by norm_num),
      Nat.Prime.primeFactors Nat.prime_two, Nat.Prime.primeFactors Nat.prime_three]
    rfl
  rw [h, h6]
  decide

theorem comp_quasisimple_of_simple {X : Type*} [Group X] [Finite X] (hs : IsSimpleGroup X)
    (hn : ¬ (Nat.card X).Prime) : CFSG.IsQuasisimple X := by
  have hnc : ∃ a b : X, a * b ≠ b * a := by
    by_contra hcon
    push Not at hcon
    have : IsMulCommutative X := ⟨⟨fun a b => hcon a b⟩⟩
    exact hn (IsSimpleGroup.prime_card (α := X))
  have hperf : Group.IsPerfect X := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator X) with h0 | h1
    · exfalso
      obtain ⟨a, b, hab⟩ := hnc
      have : ⁅a, b⁆ ∈ commutator X :=
        Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b)
      rw [h0, Subgroup.mem_bot, commutatorElement_def] at this
      exact hab (mul_inv_eq_iff_eq_mul.mp (mul_inv_eq_one.mp this))
    · exact ⟨h1⟩
  have hZ : Subgroup.center X = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center X) with h | h
    · exact h
    · exfalso
      obtain ⟨a, b, hab⟩ := hnc
      exact hab (Subgroup.mem_center_iff.1 (h ▸ Subgroup.mem_top b) a)
  let e : (X ⧸ Subgroup.center X) ≃* X :=
    (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
  refine ⟨hperf, ?_, ?_⟩
  · exact MulEquiv.isSimpleGroup e
  · obtain ⟨a, b, hab⟩ := hnc
    exact ⟨e.symm a, e.symm b, fun h => hab (by
      have := congrArg e h
      simpa using this)⟩

end Factors

section Producers

variable {Ω : Type} [Group Ω] [Finite Ω]

theorem comp_not_prime_of_four_dvd {N : ℕ} (h : 4 ∣ N) : ¬ N.Prime := by
  intro hp
  have h2 : 2 ∣ N := (by norm_num : 2 ∣ 4).trans h
  have := (Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp h2
  subst this
  omega

theorem factorN_of_simple {G : Subgroup Ω} (hs : IsSimpleGroup ↥G) (hn : ¬ (Nat.card ↥G).Prime) :
    FactorN G G ∧ G ≠ ⊥ :=
  ⟨factorN_of_quasisimple (comp_quasisimple_of_simple hs hn),
    (Subgroup.nontrivial_iff_ne_bot G).mp hs.toNontrivial⟩

private noncomputable def compTU (F : Type) [Field F] : Matrix.GeneralLinearGroup (Fin 2) F :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![1, 1; 0, 1] (by simp)

private noncomputable def compTL (F : Type) [Field F] : Matrix.GeneralLinearGroup (Fin 2) F :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![1, 0; 1, 1] (by simp)

private theorem compTU_mem (F : Type) [Field F] : compTU F ∈ StatedSL 2 F :=
  Subgroup.subset_closure (by simp [compTU, Matrix.GeneralLinearGroup.mkOfDetNeZero])

private theorem compTL_mem (F : Type) [Field F] : compTL F ∈ StatedSL 2 F :=
  Subgroup.subset_closure (by simp [compTL, Matrix.GeneralLinearGroup.mkOfDetNeZero])

theorem comp_noncomm_sl2 (F : Type) [Field F] : ∃ u v : ↥(StatedSL 2 F), u * v ≠ v * u := by
  refine ⟨⟨compTU F, compTU_mem F⟩, ⟨compTL F, compTL_mem F⟩, fun h => ?_⟩
  have h1 := congrArg (fun g : ↥(StatedSL 2 F) => (g : Matrix.GeneralLinearGroup (Fin 2) F)) h
  have h2 := congrArg (fun g : Matrix.GeneralLinearGroup (Fin 2) F =>
    (g : Matrix (Fin 2) (Fin 2) F) 0 0) h1
  simp [compTU, compTL, Matrix.GeneralLinearGroup.mkOfDetNeZero, Matrix.mul_apply,
    Fin.sum_univ_two] at h2

omit [Finite Ω] in
theorem comp_noncomm_of_equiv {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y)
    (h : ∃ a b : Y, a * b ≠ b * a) : ∃ a b : X, a * b ≠ b * a := by
  obtain ⟨a, b, hab⟩ := h
  exact ⟨e.symm a, e.symm b, fun hh => hab (by
    have := congrArg e hh
    simpa using this)⟩

theorem factor_sl2 {G : Subgroup Ω} {n : ℕ} {F : Type} [Field F] [Finite F] (hn : 1 ≤ n)
    (hF : Nat.card F = 2 ^ n) (e : ↥G ≃* ↥(StatedSL 2 F)) :
    (Nat.card ↥G = 6 ∧ (∃ a b : ↥G, a * b ≠ b * a) ∧ FactorN G ⊥) ∨ (FactorN G G ∧ G ≠ ⊥) := by
  have hcard : Nat.card ↥G = 2 ^ n * (4 ^ n - 1) := by
    rw [Nat.card_congr e.toEquiv, R3c.card_statedSL_two_pow hF]
  rcases Nat.lt_or_ge 1 n with h2 | h1
  · right
    have hchar : CharP F 2 := R3c.charP_two_of_natCard_eq_two_pow hF
    have h4 : 4 ≤ Nat.card F := by
      rw [hF]
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) h2
    have hs : IsSimpleGroup ↥G := by
      have := CFSG.Quasithin.H13.NQRigid.isSimpleGroup_statedSL_two_charTwo h4
      exact e.isSimpleGroup
    refine factorN_of_simple hs (comp_not_prime_of_four_dvd ?_)
    rw [hcard]
    exact Dvd.dvd.mul_right ((pow_dvd_pow 2 h2 : 2 ^ 2 ∣ 2 ^ n)) _
  · left
    have hn1 : n = 1 := le_antisymm h1 hn
    subst hn1
    have h6 : Nat.card ↥G = 6 := by rw [hcard]; norm_num
    exact ⟨h6, comp_noncomm_of_equiv e (comp_noncomm_sl2 F),
      factorN_of_solvable (comp_solvable_of_card_six h6)⟩

theorem factor_sl3 {G : Subgroup Ω} {m : ℕ} {F : Type} [Field F] [Finite F] (hm : Odd m)
    (hF : Nat.card F = 2 ^ m) (hm1 : 1 ≤ m) (e : ↥G ≃* ↥(StatedSL 3 F)) :
    FactorN G G ∧ G ≠ ⊥ := by
  have hs : IsSimpleGroup ↥G := by
    have := CFSG.Quasithin.H13.NQRigid.isSimpleGroup_statedSL_three_odd hF hm
    exact e.isSimpleGroup
  refine factorN_of_simple hs (comp_not_prime_of_four_dvd ?_)
  rw [Nat.card_congr e.toEquiv, card_statedSL_three1527d, hF, ← pow_mul]
  have h4 : 2 ^ 2 ∣ 2 ^ (m * 3) := pow_dvd_pow 2 (by omega)
  exact Dvd.dvd.mul_right h4 _

theorem factor_perm_five {G : Subgroup Ω} (e : ↥G ≃* Equiv.Perm (Fin 5)) :
    ∃ N : Subgroup Ω, N ≠ ⊥ ∧ FactorN G N := by
  have hC : ⁅G, G⁆ = (commutator ↥G).map G.subtype := by
    rw [_root_.commutator_def, Subgroup.map_commutator, Subgroup.map_top, Subgroup.range_subtype]
  have hCe : (commutator ↥G).map e.toMonoidHom = alternatingGroup (Fin 5) := by
    rw [_root_.commutator_def, Subgroup.map_commutator,
      Subgroup.map_top_of_surjective _ e.surjective, ← _root_.commutator_def]
    exact alternatingGroup.commutator_perm_eq (by simp)
  let eN : ↥⁅G, G⁆ ≃* ↥(alternatingGroup (Fin 5)) :=
    (MulEquiv.subgroupCongr hC).trans
      ((Subgroup.equivMapOfInjective _ G.subtype G.subtype_injective).symm.trans
        ((Subgroup.equivMapOfInjective _ e.toMonoidHom e.injective).trans
          (MulEquiv.subgroupCongr hCe)))
  have hs : IsSimpleGroup ↥⁅G, G⁆ := by
    have : IsSimpleGroup ↥(alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup (by simp)
    exact eN.isSimpleGroup
  have hnp : ¬ (Nat.card ↥⁅G, G⁆).Prime := by
    rw [Nat.card_congr eN.toEquiv, card_alternatingGroup1527d 5 (by norm_num)]
    norm_num [Nat.factorial]
  refine ⟨⁅G, G⁆, (Subgroup.nontrivial_iff_ne_bot _).mp hs.toNontrivial, A3.commutator_self_le G,
    fun g hg n hn => (Subgroup.mem_normalizer_iff.mp (A3.le_normalizer_commutator_left G G hg) n).mp hn,
    Or.inr (comp_quasisimple_of_simple hs hnp), fun Q hQG hQ => ?_⟩
  have := Subgroup.commutator_mono hQG hQG
  rwa [hQ] at this

theorem factor_alt6 {G : Subgroup Ω} (e : ↥G ≃* alternatingGroup (Fin 6)) :
    FactorN G G ∧ G ≠ ⊥ := by
  have hs : IsSimpleGroup ↥G := by
    have : IsSimpleGroup ↥(alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
    exact e.isSimpleGroup
  refine factorN_of_simple hs ?_
  rw [Nat.card_congr e.toEquiv, card_alternatingGroup1527d 6 (by norm_num)]
  norm_num [Nat.factorial]

theorem factor_card_three {G : Subgroup Ω} (h : Nat.card ↥G = 3) : FactorN G ⊥ := by
  refine factorN_of_solvable ?_
  refine CFSG.LocalAnalysis.ComponentInitial.isSolvable_of_card_primeFactors_le_two ?_
  rw [h, Nat.Prime.primeFactors Nat.prime_three]
  decide

theorem factor_image_sl2 {G : Subgroup Ω} {n : ℕ} {F : Type} [Field F] [Finite F]
    (hF : Nat.card F = 2 ^ n) (π : ↥(StatedSL 2 F) →* ↥G) (hπ : Function.Surjective π) :
    ∃ N : Subgroup Ω, FactorN G N := by
  have hn : 1 ≤ n := by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · have := Finite.one_lt_card_iff_nontrivial.2 (inferInstance : Nontrivial F)
      simp [hF] at this
    · exact hn
  have hcard : Nat.card ↥(StatedSL 2 F) = 2 ^ n * (4 ^ n - 1) := R3c.card_statedSL_two_pow hF
  rcases Nat.lt_or_ge 1 n with h2 | h1
  · have hchar : CharP F 2 := R3c.charP_two_of_natCard_eq_two_pow hF
    have h4 : 4 ≤ Nat.card F := by
      rw [hF]
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) h2
    have hsimple : IsSimpleGroup ↥(StatedSL 2 F) :=
      CFSG.Quasithin.H13.NQRigid.isSimpleGroup_statedSL_two_charTwo h4
    rcases hsimple.eq_bot_or_eq_top_of_normal π.ker with hker | hker
    · have hinj : Function.Injective π := (MonoidHom.ker_eq_bot_iff π).1 hker
      let e : ↥(StatedSL 2 F) ≃* ↥G := MulEquiv.ofBijective π ⟨hinj, hπ⟩
      have hs : IsSimpleGroup ↥G := e.symm.isSimpleGroup
      have hcardG : Nat.card ↥G = 2 ^ n * (4 ^ n - 1) := by
        rw [← Nat.card_congr e.toEquiv, hcard]
      exact ⟨G, (factorN_of_simple hs (comp_not_prime_of_four_dvd (by
        rw [hcardG]
        exact Dvd.dvd.mul_right ((pow_dvd_pow 2 h2 : 2 ^ 2 ∣ 2 ^ n)) _))).1⟩
    · have hsub : Subsingleton ↥G := by
        refine ⟨fun a b => ?_⟩
        obtain ⟨x, rfl⟩ := hπ a
        obtain ⟨y, rfl⟩ := hπ b
        have hx : x ∈ π.ker := hker ▸ Subgroup.mem_top x
        have hy : y ∈ π.ker := hker ▸ Subgroup.mem_top y
        rw [MonoidHom.mem_ker] at hx hy
        rw [hx, hy]
      exact ⟨⊥, factorN_of_solvable (Group.isSolvable_of_comm (fun a b => Subsingleton.elim _ _))⟩
  · have hn1 : n = 1 := le_antisymm h1 hn
    subst hn1
    have h6 : Nat.card ↥(StatedSL 2 F) = 6 := by rw [hcard]; norm_num
    have : Group.IsSolvable ↥(StatedSL 2 F) := comp_solvable_of_card_six h6
    exact ⟨⊥, factorN_of_solvable (Group.isSolvable_of_surjective hπ)⟩

theorem factor_of_list {V : Type} [CommGroup V] [Finite V] {G : Subgroup (MulAut V)}
    (h : B56FactorList ↥G) :
    (Nat.card ↥G = 6 ∧ (∃ a b : ↥G, a * b ≠ b * a) ∧ FactorN G ⊥) ∨ ∃ N, N ≠ ⊥ ∧ FactorN G N := by
  rcases h with ⟨n, F, _, _, hn, hF, ⟨e⟩⟩ | ⟨⟨e⟩⟩ | ⟨m, F, _, _, hm1, hm, hF, ⟨e⟩⟩
  · rcases factor_sl2 hn hF e with h6 | ⟨hN, hne⟩
    · exact Or.inl h6
    · exact Or.inr ⟨G, hne, hN⟩
  · obtain ⟨N, hN, hFN⟩ := factor_perm_five e
    exact Or.inr ⟨N, hN, hFN⟩
  · obtain ⟨hN, hne⟩ := factor_sl3 hm hF hm1 e
    exact Or.inr ⟨G, hne, hN⟩

end Producers

section Main

variable {V : Type} [CommGroup V] [Finite V]

omit [Finite V] in
theorem comp_normal_in_join {G₁ G₂ J N : Subgroup (MulAut V)} (hJ : G₁ ⊔ G₂ = J)
    (hc : ∀ a ∈ G₁, ∀ b ∈ G₂, a * b = b * a) (hN : N ≤ G₁)
    (hn : ∀ g ∈ G₁, ∀ n ∈ N, g * n * g⁻¹ ∈ N) : ∀ x ∈ J, ∀ n ∈ N, x * n * x⁻¹ ∈ N := by
  intro x hx n hn'
  rw [← hJ] at hx
  obtain ⟨g₁, hg₁, g₂, hg₂, rfl⟩ := comp_exists_mul hc hx
  have e : g₂ * n * g₂⁻¹ = n := by
    have := hc n (hN hn') g₂ hg₂
    rw [mul_inv_eq_iff_eq_mul, this]
  have : g₁ * g₂ * n * (g₁ * g₂)⁻¹ = g₁ * (g₂ * n * g₂⁻¹) * g₁⁻¹ := by group
  rw [this, e]
  exact hn g₁ hg₁ n hn'

theorem components_of_factors {J G₁ G₂ N₁ N₂ : Subgroup (MulAut V)} (hG₁J : G₁ ≤ J) (hG₂J : G₂ ≤ J)
    (h₁ : FactorN G₁ N₁) (h₂ : FactorN G₂ N₂)
    (hc : ∀ a ∈ G₁, ∀ b ∈ G₂, a * b = b * a)
    (hn₁ : ∀ x ∈ J, ∀ n ∈ N₁, x * n * x⁻¹ ∈ N₁) (hn₂ : ∀ x ∈ J, ∀ n ∈ N₂, x * n * x⁻¹ ∈ N₂)
    (hKP : ∀ K ∈ cComp J, K ≤ G₁ ⊔ G₂)
    (hcases : B56Case1 J ∨ B56Case2 J ∨ B56Case3 J ∨ B56Case4 J ∨ B56Case5 J) :
    N₁ ≤ J ∧ N₂ ≤ J ∧ (∀ x ∈ J, ∀ n ∈ N₁, x * n * x⁻¹ ∈ N₁) ∧
      (∀ x ∈ J, ∀ n ∈ N₂, x * n * x⁻¹ ∈ N₂) ∧
      (N₁ = ⊥ ∨ (CFSG.IsQuasisimple ↥N₁ ∧ B56QuasisimpleList ↥N₁)) ∧
      (N₂ = ⊥ ∨ (CFSG.IsQuasisimple ↥N₂ ∧ B56QuasisimpleList ↥N₂)) ∧
      ∀ K ∈ cComp J, K = N₁ ∨ K = N₂ := by
  have hN₁J : N₁ ≤ J := h₁.1.trans hG₁J
  have hN₂J : N₂ ≤ J := h₂.1.trans hG₂J
  have hlist : ∀ N : Subgroup (MulAut V), N ≤ J → (∀ x ∈ J, ∀ n ∈ N, x * n * x⁻¹ ∈ N) →
      (N = ⊥ ∨ CFSG.IsQuasisimple ↥N) → (N = ⊥ ∨ (CFSG.IsQuasisimple ↥N ∧ B56QuasisimpleList ↥N)) := by
    intro N hNJ hn hq
    rcases hq with h | h
    · exact Or.inl h
    · exact Or.inr ⟨h, SBc3.b56QL_of_subnormal hNJ
        (A3.subnormal_of_normal hNJ ((Subgroup.normal_subgroupOf_iff hNJ).2
          fun h' k hh hk => hn k hk h' hh)) h hcases⟩
  refine ⟨hN₁J, hN₂J, hn₁, hn₂, hlist N₁ hN₁J hn₁ h₁.2.2.1, hlist N₂ hN₂J hn₂ h₂.2.2.1, ?_⟩
  intro K hK
  have hKN : K ≤ N₁ ⊔ N₂ :=
    perfect_le_sup_of_commute hc h₁.2.2.2 h₂.2.2.2 (hKP K hK) (perfect_of_mem_cComp hK)
  exact comp_cq hK hKN hN₁J hn₁ h₁.2.2.1 hN₂J hn₂ h₂.2.2.1

theorem b56_components {J : Subgroup (MulAut V)}
    (hcases : B56Case1 J ∨ B56Case2 J ∨ B56Case3 J ∨ B56Case4 J ∨ B56Case5 J) :
    (Nat.card ↥J = 6 ∧ ∃ a b : ↥J, a * b ≠ b * a) ∨
    (∃ G₁ G₂ : Subgroup (MulAut V), G₁ ⊔ G₂ = J ∧ G₁ ⊓ G₂ = ⊥ ∧
        (∀ a ∈ G₁, ∀ b ∈ G₂, a * b = b * a) ∧ (Nat.card ↥G₁ = 6 ∧ ∃ a b : ↥G₁, a * b ≠ b * a) ∧
        (Nat.card ↥G₂ = 6 ∧ ∃ a b : ↥G₂, a * b ≠ b * a)) ∨
    ∃ N₁ N₂ : Subgroup (MulAut V), (N₁ ≠ ⊥ ∨ N₂ ≠ ⊥) ∧ N₁ ≤ J ∧ N₂ ≤ J ∧
      (∀ x ∈ J, ∀ n ∈ N₁, x * n * x⁻¹ ∈ N₁) ∧ (∀ x ∈ J, ∀ n ∈ N₂, x * n * x⁻¹ ∈ N₂) ∧
      (N₁ = ⊥ ∨ (CFSG.IsQuasisimple ↥N₁ ∧ B56QuasisimpleList ↥N₁)) ∧
      (N₂ = ⊥ ∨ (CFSG.IsQuasisimple ↥N₂ ∧ B56QuasisimpleList ↥N₂)) ∧
      ∀ K ∈ cComp J, K = N₁ ∨ K = N₂ := by
  have hcases' := hcases
  rcases hcases with h1 | ⟨⟨e⟩, -⟩ | ⟨G₁, G₂, hsup, hinf, hc, hf₁, hf₂, -⟩ |
      ⟨G₁, G₂, t, hJt, -, hc, ⟨e₁⟩, hc₂, -, -, -, -, -, ht₁, ht₂, -⟩ |
      ⟨G₁, G₂, hsup, -, hc, -, ⟨e₁⟩, -, -, h₂⟩
  ·
    obtain ⟨hq, -, hlist⟩ := h1
    have hFJ : quasithinGenFitting J ≤ J := quasithinGenFitting_le J
    have hFn : ∀ x ∈ J, ∀ n ∈ quasithinGenFitting J, x * n * x⁻¹ ∈ quasithinGenFitting J :=
      fun x hx n hn =>
        (Subgroup.mem_normalizer_iff.mp (le_normalizer_quasithinGenFitting J hx) n).mp hn
    have hbotn : ∀ x ∈ J, ∀ n ∈ (⊥ : Subgroup (MulAut V)), x * n * x⁻¹ ∈ (⊥ : Subgroup (MulAut V)) :=
      fun x _ n hn => by rw [Subgroup.mem_bot] at hn ⊢; simp [hn]
    refine Or.inr (Or.inr ⟨quasithinGenFitting J, ⊥, Or.inl (SBc3.ne_bot_of_isQuasisimple hq), hFJ,
      bot_le, hFn, hbotn, Or.inr ⟨hq, hlist⟩, Or.inl rfl, ?_⟩)
    intro K hK
    left
    rcases comp_dichotomy hK hFJ hFn (Or.inr hq) with h | hc
    · exact h
    · have hKc : K ≤ Subgroup.centralizer (quasithinGenFitting J : Set (MulAut V)) :=
        Subgroup.commutator_eq_bot_iff_le_centralizer.mp (by rw [Subgroup.commutator_comm]; exact hc)
      have hKF : K ≤ quasithinGenFitting J := fun x hx =>
        centralizer_quasithinGenFitting_le J ⟨le_of_mem_cComp hK hx, hKc hx⟩
      rcases comp_cq hK (by rwa [sup_bot_eq]) hFJ hFn (Or.inr hq) bot_le hbotn (Or.inl rfl) with h | h
      · exact h
      · exact absurd h (ne_bot_of_mem_cComp hK)
  ·
    left
    refine ⟨?_, comp_noncomm_of_equiv e ⟨Equiv.swap 0 1, Equiv.swap 1 2, by decide⟩⟩
    rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
    rfl
  ·
    have hG₁J : G₁ ≤ J := hsup ▸ le_sup_left
    have hG₂J : G₂ ≤ J := hsup ▸ le_sup_right
    have hsup' : G₂ ⊔ G₁ = J := by rw [sup_comm]; exact hsup
    have hc' : ∀ a ∈ G₂, ∀ b ∈ G₁, a * b = b * a := fun a ha b hb => (hc b hb a ha).symm
    have hKP : ∀ K ∈ cComp J, K ≤ G₁ ⊔ G₂ := fun K hK => by
      rw [hsup]; exact le_of_mem_cComp hK
    have third : ∀ N₁ N₂ : Subgroup (MulAut V), FactorN G₁ N₁ → FactorN G₂ N₂ → (N₁ ≠ ⊥ ∨ N₂ ≠ ⊥) →
        ∃ N₁ N₂ : Subgroup (MulAut V), (N₁ ≠ ⊥ ∨ N₂ ≠ ⊥) ∧ N₁ ≤ J ∧ N₂ ≤ J ∧
          (∀ x ∈ J, ∀ n ∈ N₁, x * n * x⁻¹ ∈ N₁) ∧ (∀ x ∈ J, ∀ n ∈ N₂, x * n * x⁻¹ ∈ N₂) ∧
          (N₁ = ⊥ ∨ (CFSG.IsQuasisimple ↥N₁ ∧ B56QuasisimpleList ↥N₁)) ∧
          (N₂ = ⊥ ∨ (CFSG.IsQuasisimple ↥N₂ ∧ B56QuasisimpleList ↥N₂)) ∧
          ∀ K ∈ cComp J, K = N₁ ∨ K = N₂ := by
      intro N₁ N₂ h₁ h₂ hne
      exact ⟨N₁, N₂, hne, components_of_factors hG₁J hG₂J h₁ h₂ hc
        (comp_normal_in_join hsup hc h₁.1 h₁.2.1) (comp_normal_in_join hsup' hc' h₂.1 h₂.2.1)
        hKP hcases'⟩
    right
    rcases factor_of_list hf₁ with ⟨h6₁, nc₁, hN₁⟩ | ⟨N₁, hN₁ne, hN₁⟩ <;>
      rcases factor_of_list hf₂ with ⟨h6₂, nc₂, hN₂⟩ | ⟨N₂, hN₂ne, hN₂⟩
    · exact Or.inl ⟨G₁, G₂, hsup, hinf, hc, ⟨h6₁, nc₁⟩, ⟨h6₂, nc₂⟩⟩
    · exact Or.inr (third ⊥ N₂ hN₁ hN₂ (Or.inr hN₂ne))
    · exact Or.inr (third N₁ ⊥ hN₁ hN₂ (Or.inl hN₁ne))
    · exact Or.inr (third N₁ N₂ hN₁ hN₂ (Or.inl hN₁ne))
  ·
    have hG₁J : G₁ ≤ J := by rw [hJt]; exact le_sup_left.trans le_sup_left
    have hG₂J : G₂ ≤ J := by rw [hJt]; exact le_sup_right.trans le_sup_left
    obtain ⟨hN₁, hne₁⟩ := factor_alt6 e₁
    have hN₂ := factor_card_three hc₂
    have hA : G₁ ⊔ G₂ ≤ J := sup_le hG₁J hG₂J
    have hnorm : J ≤ Subgroup.normalizer ((G₁ ⊔ G₂ : Subgroup (MulAut V)) : Set (MulAut V)) := by
      rw [hJt]
      exact sup_le Subgroup.le_normalizer
        (Subgroup.zpowers_le.2 (InternalSec.mem_normalizer_sup ht₁ ht₂))
    have hAn : ((G₁ ⊔ G₂).subgroupOf J).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hA).mpr hnorm
    have hB : Group.IsSolvable ↥(Subgroup.zpowers t) := inferInstance
    have hKP : ∀ K ∈ cComp J, K ≤ G₁ ⊔ G₂ := fun K hK =>
      (le_perfectCore_of_perfect (le_of_mem_cComp hK) (perfect_of_mem_cComp hK)).trans
        (perfectCore_le_of_sup_solvable hA hAn hJt hB)
    have hn₁ : ∀ x ∈ J, ∀ n ∈ G₁, x * n * x⁻¹ ∈ G₁ := fun x hx n hn => by
      rw [hJt] at hx
      exact SBc3.conj_mem_of_mem_sup_zpowers hc ht₁ ht₂ x hx n hn
    have hbotn : ∀ x ∈ J, ∀ n ∈ (⊥ : Subgroup (MulAut V)), x * n * x⁻¹ ∈ (⊥ : Subgroup (MulAut V)) :=
      fun x _ n hn => by rw [Subgroup.mem_bot] at hn ⊢; simp [hn]
    exact Or.inr (Or.inr ⟨G₁, ⊥, Or.inl hne₁, components_of_factors hG₁J hG₂J hN₁ hN₂ hc hn₁ hbotn
      hKP hcases'⟩)
  ·
    have hG₁J : G₁ ≤ J := hsup ▸ le_sup_left
    have hG₂J : G₂ ≤ J := hsup ▸ le_sup_right
    have hsup' : G₂ ⊔ G₁ = J := by rw [sup_comm]; exact hsup
    have hc' : ∀ a ∈ G₂, ∀ b ∈ G₁, a * b = b * a := fun a ha b hb => (hc b hb a ha).symm
    have hKP : ∀ K ∈ cComp J, K ≤ G₁ ⊔ G₂ := fun K hK => by
      rw [hsup]; exact le_of_mem_cComp hK
    obtain ⟨hN₁, hne₁⟩ := factor_sl3 (m := 1) (F := ZMod 2) odd_one (by simp) le_rfl e₁
    obtain ⟨N₂, hN₂⟩ : ∃ N₂, FactorN G₂ N₂ := by
      rcases h₂ with ⟨⟨e₂⟩, -⟩ | ⟨n, F, _, _, hF, π, hR⟩
      · exact ⟨G₂, (factor_sl3 (m := 1) (F := ZMod 2) odd_one (by simp) le_rfl e₂).1⟩
      · exact factor_image_sl2 hF π hR.1
    exact Or.inr (Or.inr ⟨G₁, N₂, Or.inl hne₁, components_of_factors hG₁J hG₂J hN₁ hN₂ hc
      (comp_normal_in_join hsup hc hN₁.1 hN₁.2.1) (comp_normal_in_join hsup' hc' hN₂.1 hN₂.2.1)
      hKP hcases'⟩)

end Main

end S153L

end CFSG.Quasithin
