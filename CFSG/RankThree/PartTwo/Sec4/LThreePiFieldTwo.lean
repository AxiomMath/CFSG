module

public import CFSG.RankThree.PartTwo.Sec4.LThreePiFieldB

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.LocalAnalysis.ComponentInitial CFSG.Assembly.LowTwoRank
open Matrix

section Groups

variable {G : Type} [Group G] [Finite G]

theorem false_of_le_normalizer (hG : SectionFourHyp G) {P : Subgroup G} (hP1 : P ≠ ⊥)
    (hP2 : IsPGroup 2 P) {E : Subgroup G} (hE : CFSG.Assembly.IsElemAbelian 3 E)
    (hE81 : Nat.card E = 81) (hEP : E ≤ Subgroup.normalizer (P : Set G)) : False := by
  have h1 : 4 ≤ CFSG.Assembly.pRank 3 (Subgroup.normalizer (P : Set G)) :=
    le_csSup (CFSG.RankThreeEvenClassification.Helpers.pRank_bddAbove 3 Nat.prime_three _)
      ⟨E, hEP, hE, by rw [hE81]; norm_num⟩
  have h2 : CFSG.Assembly.pRank 3 (Subgroup.normalizer (P : Set G)) ≤
      CFSG.Assembly.evenRank G :=
    CFSG.RankThreeEvenClassification.Helpers.pRank_le_evenRank 3 Nat.prime_three (by norm_num)
      _ ⟨P, hP1, hP2, rfl⟩
  have h3 := hG.evenRank_le
  omega

theorem mem_normalizer_of_conj_mem {P : Subgroup G} {a : G}
    (h : ∀ x ∈ P, a * x * a⁻¹ ∈ P) : a ∈ Subgroup.normalizer (P : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨h x, fun hx => ?_⟩
  let F : P → P := fun y => ⟨a * y * a⁻¹, h y y.2⟩
  have hF : Function.Injective F := by
    intro y y' hyy'
    have := congrArg Subtype.val hyy'
    simp only [F] at this
    exact Subtype.ext (by simpa using this)
  obtain ⟨y, hy⟩ := (Finite.injective_iff_surjective.mp hF) ⟨_, hx⟩
  have := congrArg Subtype.val hy
  simp only [F] at this
  have hxy : x = y := by
    have h2 : a * (y : G) * a⁻¹ = a * x * a⁻¹ := this
    simpa using h2.symm
  rw [hxy]
  exact y.2

omit [Finite G] in
theorem isElemAbelian_sup_zpowers {E : Subgroup G} (hE : CFSG.Assembly.IsElemAbelian 3 E)
    {x : G} (hx3 : x ^ 3 = 1) (hxE : ∀ a ∈ E, a * x = x * a) :
    CFSG.Assembly.IsElemAbelian 3 (E ⊔ Subgroup.zpowers x) := by
  have hEcomm : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hE.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hxk : ∀ a ∈ E, ∀ k : ℤ, a * x ^ k = x ^ k * a := fun a ha k =>
    (Commute.zpow_right (hxE a ha) k).eq
  let P : Subgroup G :=
    { carrier := {g | ∃ a ∈ E, ∃ k : ℤ, g = a * x ^ k}
      mul_mem' := by
        rintro _ _ ⟨a, ha, k, rfl⟩ ⟨a', ha', k', rfl⟩
        refine ⟨a * a', E.mul_mem ha ha', k + k', ?_⟩
        rw [_root_.zpow_add]
        calc a * x ^ k * (a' * x ^ k') = a * (x ^ k * a') * x ^ k' := by group
          _ = a * (a' * x ^ k) * x ^ k' := by rw [hxk a' ha' k]
          _ = a * a' * (x ^ k * x ^ k') := by group
      one_mem' := ⟨1, E.one_mem, 0, by simp⟩
      inv_mem' := by
        rintro _ ⟨a, ha, k, rfl⟩
        refine ⟨a⁻¹, E.inv_mem ha, -k, ?_⟩
        rw [_root_.mul_inv_rev, ← _root_.zpow_neg]
        exact (hxk a⁻¹ (E.inv_mem ha) (-k)).symm }
  have hPeq : E ⊔ Subgroup.zpowers x = P := by
    apply le_antisymm
    · exact sup_le (fun a ha => ⟨a, ha, 0, by simp⟩)
        (Subgroup.zpowers_le.mpr ⟨1, E.one_mem, 1, by simp⟩)
    · rintro _ ⟨a, ha, k, rfl⟩
      exact mul_mem (Subgroup.mem_sup_left ha)
        (Subgroup.mem_sup_right (Subgroup.zpow_mem_zpowers x k))
  have hPcomm : ∀ g ∈ P, ∀ h ∈ P, g * h = h * g := by
    rintro _ ⟨a, ha, k, rfl⟩ _ ⟨a', ha', k', rfl⟩
    calc a * x ^ k * (a' * x ^ k') = a * (x ^ k * a') * x ^ k' := by group
      _ = a * (a' * x ^ k) * x ^ k' := by rw [hxk a' ha' k]
      _ = (a * a') * (x ^ k * x ^ k') := by group
      _ = (a' * a) * (x ^ k' * x ^ k) := by
          rw [hEcomm a ha a' ha', ← _root_.zpow_add, ← _root_.zpow_add, add_comm]
      _ = a' * (a * x ^ k') * x ^ k := by group
      _ = a' * (x ^ k' * a) * x ^ k := by rw [hxk a ha k']
      _ = a' * x ^ k' * (a * x ^ k) := by group
  have hP3 : ∀ g ∈ P, g ^ 3 = 1 := by
    rintro _ ⟨a, ha, k, rfl⟩
    rw [(Commute.zpow_right (hxE a ha) k).mul_pow, hE.2 a ha, one_mul, ← zpow_natCast,
      ← _root_.zpow_mul, mul_comm, _root_.zpow_mul, zpow_natCast, hx3, _root_.one_zpow]
  rw [hPeq]
  exact ⟨⟨⟨fun g h => Subtype.ext (hPcomm g g.2 h h.2)⟩⟩, hP3⟩

theorem card_sup_zpowers_of_not_mem {E : Subgroup G} {x : G} (hx3 : x ^ 3 = 1)
    (hxE : ∀ a ∈ E, a * x = x * a) (hxn : x ∉ E) :
    Nat.card (E ⊔ Subgroup.zpowers x : Subgroup G) = Nat.card E * 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hxo : orderOf x = 3 := orderOf_eq_prime hx3 (fun h => hxn (h ▸ E.one_mem))
  have hc : ∀ a ∈ E, ∀ b ∈ Subgroup.zpowers x, a * b = b * a := by
    rintro a ha _ ⟨k, rfl⟩
    exact (Commute.zpow_right (hxE a ha) k).eq
  have h := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute _ _ hc).1
  rw [inf_zpowers_eq_bot hx3 hxn, Subgroup.card_bot, mul_one, Nat.card_zpowers, hxo] at h
  exact h

omit [Finite G] in
theorem commute_sup_of_commute {H₁ H₂ : Subgroup G} {x : G}
    (h₁ : ∀ a ∈ H₁, a * x = x * a) (h₂ : ∀ a ∈ H₂, a * x = x * a) :
    ∀ a ∈ H₁ ⊔ H₂, a * x = x * a := by
  have hle : H₁ ⊔ H₂ ≤ Subgroup.centralizer {x} := by
    refine sup_le (fun a ha => ?_) (fun a ha => ?_) <;>
      rw [Subgroup.mem_centralizer_singleton_iff]
    · exact h₁ a ha
    · exact h₂ a ha
  intro a ha
  exact Subgroup.mem_centralizer_singleton_iff.mp (hle ha)

end Groups

theorem odd_of_two_pow_mod_three {n : ℕ} (h : 2 ^ n % 3 = 2) : Odd n := by
  by_contra hn
  obtain ⟨k, rfl⟩ := Nat.not_odd_iff_even.mp hn
  rw [← two_mul, pow_mul, Nat.pow_mod] at h
  norm_num at h

section Matrices

variable {K : Type} [Field K] {p f : ℕ} {π : Bool}

theorem neg_one_mem_rootsOfUnity (hK : PiField π p f K) :
    (-1 : Kˣ) ∈ rootsOfUnity (qSubPi π (p ^ f)) K := by
  rw [mem_rootsOfUnity]
  by_cases hp2 : p = 2
  · subst hp2
    have := hK.charP
    have h1 : (-1 : Kˣ) = 1 := Units.ext (by simp [CharTwo.neg_eq])
    rw [h1, one_pow]
  · have hodd : Odd (p ^ f) := (hK.prime.odd_of_ne_two hp2).pow
    have heven : Even (qSubPi π (p ^ f)) := by
      obtain ⟨k, hk⟩ := hodd
      cases π
      · exact ⟨k + 1, by change p ^ f + 1 = _; omega⟩
      · exact ⟨k, by change p ^ f - 1 = _; omega⟩
    exact heven.neg_one_pow

@[expose] noncomputable def tStd (K : Type) [Field K] : GL (Fin 3) K := diagUnits (-1) (-1) 1

theorem coe_tStd : ((tStd K : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
    diagonal ![-1, -1, 1] := by
  rw [tStd, coe_diagUnits]
  simp

theorem tStd_mem_slPi (hK : PiField π p f K) : tStd K ∈ slPi π 3 (p ^ f) K := by
  have hπ : π = false → UnitaryFieldData p f K := fun h => by subst h; exact hK.unitary
  rw [mem_slPi_iff hπ]
  refine ⟨diagUnits_mem_glPi hK (neg_one_mem_rootsOfUnity hK) (neg_one_mem_rootsOfUnity hK)
    (one_mem _), ?_⟩
  rw [coe_tStd, det_diagonal, Fin.prod_univ_three]
  simp

theorem tStd_sq : tStd K * tStd K = 1 := by
  apply Units.ext
  rw [Units.val_mul, coe_tStd, diagonal_mul_diagonal, Units.val_one, ← diagonal_one]
  congr 1
  funext i
  fin_cases i <;> simp

theorem tStd_ne_one (hK : PiField π p f K) (hp2 : p ≠ 2) : tStd K ≠ 1 := by
  have := hK.charP
  intro h
  have h00 := congrArg (fun M : GL (Fin 3) K => (M : Matrix (Fin 3) (Fin 3) K) 0 0) h
  simp only [coe_tStd, diagonal_apply_eq, Units.val_one, one_apply_eq] at h00
  have h2 : (2 : K) = 0 := by
    have : (-1 : K) + 1 = 0 := neg_add_cancel 1
    rw [show (-1 : K) = 1 from by simpa using h00] at this
    rw [← this]
    norm_num
  have hp : p ∣ 2 := (CharP.cast_eq_zero_iff K p 2).mp (by exact_mod_cast h2)
  exact hp2 ((Nat.prime_dvd_prime_iff_eq hK.prime Nat.prime_two).mp hp)

theorem tStd_commute_of_diag {D : GL (Fin 3) K}
    (hD : ∀ i j, i ≠ j → (D : Matrix (Fin 3) (Fin 3) K) i j = 0) :
    D * tStd K = tStd K * D := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, coe_tStd]
  ext i j
  rw [mul_diagonal, diagonal_mul]
  by_cases hij : i = j
  · subst hij
    ring
  · rw [hD i j hij, zero_mul, mul_zero]

theorem frobGL_tStd (ψ : K ≃+* K) : frobGL ψ (tStd K) = tStd K := by
  apply Units.ext
  rw [coe_frobGL, coe_tStd, diagonal_map (map_zero _)]
  congr 1
  funext i
  fin_cases i <;> simp

@[expose] noncomputable def rootGL (K : Type) [Field K] : Subgroup (GL (Fin 3) K) where
  carrier := {M | ∃ a : K, (M : Matrix (Fin 3) (Fin 3) K) = transvection 0 1 a}
  mul_mem' := by
    rintro M N ⟨a, ha⟩ ⟨b, hb⟩
    exact ⟨a + b, by rw [Units.val_mul, ha, hb, transvection_mul_transvection_same _ _
      (by decide)]⟩
  one_mem' := ⟨0, by rw [Units.val_one, transvection_zero]⟩
  inv_mem' := by
    rintro M ⟨a, ha⟩
    refine ⟨-a, ?_⟩
    rw [Matrix.coe_units_inv, ha]
    apply Matrix.inv_eq_right_inv
    rw [transvection_mul_transvection_same _ _ (by decide), add_neg_cancel, transvection_zero]

theorem rootGL_le_slPi (q : ℕ) : rootGL K ≤ slPi true 3 q K := by
  rintro M ⟨a, ha⟩
  rw [mem_slPi_true, ha]
  exact det_transvection_of_ne _ _ (by decide) a

theorem conj_mem_rootGL_of_diag {D : GL (Fin 3) K}
    (hD : ∀ i j, i ≠ j → (D : Matrix (Fin 3) (Fin 3) K) i j = 0) {M : GL (Fin 3) K}
    (hM : M ∈ rootGL K) : D * M * D⁻¹ ∈ rootGL K := by
  obtain ⟨a, ha⟩ := hM
  set d : Fin 3 → K := fun i => (D : Matrix (Fin 3) (Fin 3) K) i i with hd
  have hDd : (D : Matrix (Fin 3) (Fin 3) K) = diagonal d := by
    ext i j
    by_cases hij : i = j
    · subst hij
      rw [diagonal_apply_eq]
    · rw [hD i j hij, diagonal_apply_ne _ hij]
  have hd0 : ∀ i, d i ≠ 0 := by
    intro i h0
    have hdet := D.isUnit.map (Matrix.detMonoidHom : Matrix (Fin 3) (Fin 3) K →* K)
    change IsUnit (D : Matrix (Fin 3) (Fin 3) K).det at hdet
    rw [hDd, det_diagonal] at hdet
    exact hdet.ne_zero (Finset.prod_eq_zero (Finset.mem_univ i) h0)
  have hDi : ((D⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = diagonal fun i => (d i)⁻¹ := by
    rw [Matrix.coe_units_inv, hDd]
    apply Matrix.inv_eq_right_inv
    rw [diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    funext i
    exact mul_inv_cancel₀ (hd0 i)
  refine ⟨d 0 * a * (d 1)⁻¹, ?_⟩
  rw [Units.val_mul, Units.val_mul, ha, hDi, hDd]
  have h0 := hd0 0
  have h1 := hd0 1
  have h2 := hd0 2
  ext i j
  rw [mul_diagonal, diagonal_mul]
  simp only [transvection, Matrix.add_apply, Matrix.one_apply, Matrix.single_apply]
  fin_cases i <;> fin_cases j <;> simp [h0, h1, h2]

theorem frobGL_mem_rootGL (ψ : K ≃+* K) {M : GL (Fin 3) K} (hM : M ∈ rootGL K) :
    frobGL ψ M ∈ rootGL K := by
  obtain ⟨a, ha⟩ := hM
  refine ⟨ψ a, ?_⟩
  rw [coe_frobGL, ha]
  ext i j
  simp only [Matrix.map_apply, transvection, Matrix.add_apply, Matrix.one_apply,
    Matrix.single_apply]
  fin_cases i <;> fin_cases j <;> simp

theorem rootGL_sq [CharP K 2] {M : GL (Fin 3) K} (hM : M ∈ rootGL K) : M ^ 2 = 1 := by
  obtain ⟨a, ha⟩ := hM
  apply Units.ext
  rw [Units.val_pow_eq_pow_val, ha, pow_two, transvection_mul_transvection_same _ _ (by decide),
    CharTwo.add_self_eq_zero, transvection_zero, Units.val_one]

theorem rootGL_ne_bot : rootGL K ≠ ⊥ := by
  intro h
  have hmem : (⟨transvection 0 1 1, transvection 0 1 (-1), by
      rw [transvection_mul_transvection_same _ _ (by decide), add_neg_cancel, transvection_zero],
      by rw [transvection_mul_transvection_same _ _ (by decide), neg_add_cancel,
        transvection_zero]⟩ : GL (Fin 3) K) ∈ rootGL K := ⟨1, rfl⟩
  rw [h, Subgroup.mem_bot] at hmem
  have := congrArg (fun M : GL (Fin 3) K => (M : Matrix (Fin 3) (Fin 3) K) 0 1) hmem
  simp [transvection] at this

end Matrices

section Pull

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} [hLn : L.Normal]
  {K : Type} [Field K] {p f : ℕ} {π : Bool}

@[expose] noncomputable def pullSL (e : L ≃* slPi π 3 (p ^ f) K)
    (X : Subgroup (GL (Fin 3) K)) : Subgroup G :=
  ((X.subgroupOf (slPi π 3 (p ^ f) K)).map e.symm.toMonoidHom).map L.subtype

omit [Finite G] hLn in
theorem mem_pullSL {e : L ≃* slPi π 3 (p ^ f) K} {X : Subgroup (GL (Fin 3) K)} {g : G} :
    g ∈ pullSL e X ↔ ∃ hg : g ∈ L, ((e ⟨g, hg⟩ : slPi π 3 (p ^ f) K) : GL (Fin 3) K) ∈ X := by
  constructor
  · rintro ⟨_, ⟨s, hs, rfl⟩, rfl⟩
    refine ⟨(e.symm s).2, ?_⟩
    show ((e (e.symm s) : slPi π 3 (p ^ f) K) : GL (Fin 3) K) ∈ X
    rw [MulEquiv.apply_symm_apply]
    exact Subgroup.mem_subgroupOf.mp hs
  · rintro ⟨hg, hX⟩
    exact ⟨⟨g, hg⟩, ⟨e ⟨g, hg⟩, hX, by simp⟩, rfl⟩

theorem mem_normalizer_pullSL {e : L ≃* slPi π 3 (p ^ f) K} {X : Subgroup (GL (Fin 3) K)}
    {a : G} (ha : ∀ s : slPi π 3 (p ^ f) K, (s : GL (Fin 3) K) ∈ X →
      ((slAct e ⟨a, mem_normalizer_of_normal a⟩ s : slPi π 3 (p ^ f) K) : GL (Fin 3) K) ∈ X) :
    a ∈ Subgroup.normalizer (pullSL e X : Set G) := by
  apply mem_normalizer_of_conj_mem
  intro x hx
  obtain ⟨hxL, hxX⟩ := mem_pullSL.mp hx
  refine mem_pullSL.mpr ⟨hLn.conj_mem x hxL a, ?_⟩
  have h1 := ha (e ⟨x, hxL⟩) hxX
  rw [coe_slAct_eq, MulEquiv.symm_apply_apply] at h1
  exact h1

omit [Finite G] hLn in
theorem pullSL_ne_bot {e : L ≃* slPi π 3 (p ^ f) K} {X : Subgroup (GL (Fin 3) K)}
    (hX : X ≤ slPi π 3 (p ^ f) K) (hX1 : X ≠ ⊥) : pullSL e X ≠ ⊥ := by
  obtain ⟨M, hM1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hX1
  intro h
  have hmem : ((e.symm ⟨M, hX M.2⟩ : L) : G) ∈ pullSL e X := by
    refine mem_pullSL.mpr ⟨(e.symm _).2, ?_⟩
    have : (⟨((e.symm ⟨M, hX M.2⟩ : L) : G), (e.symm _).2⟩ : L) = e.symm ⟨M, hX M.2⟩ := rfl
    rw [this, MulEquiv.apply_symm_apply]
    exact M.2
  rw [h, Subgroup.mem_bot] at hmem
  apply hM1
  have h2 : e.symm ⟨M, hX M.2⟩ = 1 := Subtype.ext hmem
  have h3 := congrArg e h2
  rw [MulEquiv.apply_symm_apply, map_one] at h3
  exact Subtype.ext (show (M : GL (Fin 3) K) = 1 from congrArg Subtype.val h3)

omit [Finite G] hLn in
theorem pullSL_sq {e : L ≃* slPi π 3 (p ^ f) K} {X : Subgroup (GL (Fin 3) K)}
    (hX2 : ∀ M ∈ X, M ^ 2 = 1) {g : G} (hg : g ∈ pullSL e X) : g ^ 2 = 1 := by
  obtain ⟨hgL, hgX⟩ := mem_pullSL.mp hg
  have h1 := hX2 _ hgX
  have h2 : e ⟨g, hgL⟩ ^ 2 = 1 := Subtype.ext (by rw [Subgroup.coe_pow, h1]; rfl)
  rw [← map_pow, map_eq_one_iff] at h2
  · exact congrArg Subtype.val h2
  · exact e.injective

end Pull

section RankFour

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} [hLn : L.Normal]
  {K : Type} [Field K] {p f : ℕ} {π : Bool}

@[expose] def diagOrFrob (e : L ≃* slPi π 3 (p ^ f) K) (σ : G) : Set G :=
  {x | ∃ D : GL (Fin 3) K, IsPGLAt e x D ∧
    ∀ i j, i ≠ j → (D : Matrix (Fin 3) (Fin 3) K) i j = 0} ∪ {σ}

theorem two_and_unitary_of_rank_four (hG : SectionFourHyp G) (hK : PiField π p f K)
    (e : L ≃* slPi π 3 (p ^ f) K) {ψ : K ≃+* K} {σ : G}
    (hσψ : ∀ s : slPi π 3 (p ^ f) K,
      ((slAct e ⟨σ, mem_normalizer_of_normal σ⟩ s : slPi π 3 (p ^ f) K) : GL (Fin 3) K) =
        frobGL ψ s)
    {E : Subgroup G} (hE : CFSG.Assembly.IsElemAbelian 3 E) (hE81 : Nat.card E = 81)
    (hEgen : E ≤ Subgroup.closure (diagOrFrob e σ)) : p = 2 ∧ π = false := by
  have hπ : π = false → UnitaryFieldData p f K := fun h => by subst h; exact hK.unitary
  have hp2 : p = 2 := by
    by_contra hp2
    obtain ⟨t, ht⟩ : ∃ t : L, t = e.symm ⟨tStd K, tStd_mem_slPi hK⟩ := ⟨_, rfl⟩
    have het : ((e t : slPi π 3 (p ^ f) K) : GL (Fin 3) K) = tStd K := by
      rw [ht, MulEquiv.apply_symm_apply]
    have ht1 : (t : G) ≠ 1 := by
      intro h
      apply tStd_ne_one hK hp2
      rw [← het, show t = 1 from Subtype.ext h, map_one]
      rfl
    have ht2 : (t : G) ^ 2 = 1 := by
      have : e t ^ 2 = 1 := Subtype.ext (by rw [Subgroup.coe_pow, het, pow_two, tStd_sq]; rfl)
      rw [← map_pow, map_eq_one_iff _ e.injective] at this
      exact congrArg Subtype.val this
    have hcomm : ∀ x ∈ diagOrFrob e σ, x * (t : G) = t * x := by
      rintro x (⟨D, hD, hDd⟩ | hx)
      · rw [ht]
        apply commute_of_slAct_eq
        apply Subtype.ext
        rw [hD.2]
        change D * tStd K * D⁻¹ = tStd K
        rw [tStd_commute_of_diag hDd, mul_inv_cancel_right]
      · rw [Set.mem_singleton_iff.mp hx, ht]
        apply commute_of_slAct_eq
        apply Subtype.ext
        rw [hσψ]
        exact frobGL_tStd ψ
    have hle : E ≤ Subgroup.normalizer (Subgroup.zpowers (t : G) : Set G) := by
      refine hEgen.trans ((Subgroup.closure_le _).mpr fun x hx => ?_)
      apply mem_normalizer_of_conj_mem
      rintro _ ⟨k, rfl⟩
      have : x * (t : G) ^ k * x⁻¹ = (t : G) ^ k := by
        rw [(Commute.zpow_right (hcomm x hx) k).eq, mul_inv_cancel_right]
      rw [this]
      exact Subgroup.zpow_mem_zpowers _ k
    refine false_of_le_normalizer hG ?_ ?_ hE hE81 hle
    · intro h
      apply ht1
      have : (t : G) ∈ Subgroup.zpowers (t : G) := Subgroup.mem_zpowers _
      rw [h, Subgroup.mem_bot] at this
      exact this
    · intro g
      refine ⟨1, Subtype.ext ?_⟩
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp g.2
      rw [pow_one, Subgroup.coe_pow, ← hk, ← zpow_natCast, ← _root_.zpow_mul, mul_comm,
        _root_.zpow_mul, zpow_natCast, ht2, _root_.one_zpow]
      rfl
  refine ⟨hp2, ?_⟩
  subst hp2
  cases π
  · rfl
  · exfalso
    have := hK.charP
    have hle : E ≤ Subgroup.normalizer (pullSL e (rootGL K) : Set G) := by
      refine hEgen.trans ((Subgroup.closure_le _).mpr fun x hx => ?_)
      apply mem_normalizer_pullSL
      intro s hs
      rcases hx with ⟨D, hD, hDd⟩ | hx
      · rw [hD.2]
        exact conj_mem_rootGL_of_diag hDd hs
      · rw [Set.mem_singleton_iff.mp hx, hσψ]
        exact frobGL_mem_rootGL ψ hs
    refine false_of_le_normalizer hG (pullSL_ne_bot (rootGL_le_slPi _) rootGL_ne_bot) ?_ hE
      hE81 hle
    intro g
    refine ⟨1, Subtype.ext ?_⟩
    rw [pow_one, Subgroup.coe_pow]
    exact pullSL_sq (fun M hM => rootGL_sq hM) g.2

end RankFour

end CFSG.RankThree.PartTwo.Sec4
