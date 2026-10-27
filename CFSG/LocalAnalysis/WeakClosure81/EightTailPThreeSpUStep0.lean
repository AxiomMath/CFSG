module

public import CFSG.LocalAnalysis.WeakClosure81.EightTailPShape
import CFSG.LocalAnalysis.WeakClosure81.EightTailPThreeSpUUnique
import CFSG.LocalAnalysis.WeakClosure81.EightTailPThreeSymA
import CFSG.LocalAnalysis.WeakClosure81.EightTailPThreeSymSimple
import CFSG.LocalAnalysis.WeakClosure81.SymSixSpFour
import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.CSideOdd
public import CFSG.CharacterTheory.Semidihedral.CyclicPairFrattini
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpOuter

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique Subgroup
open CFSG.LocalAnalysis.WeakClosure81.SevenK

variable {G : Type} [Group G] [Finite G] {V H T : Subgroup G}
  {X : Type} [Group X] {φ : ↥(kGenIn V H) →* X}

private def wc85s0_root (X : Type) [Group X] (m n : ℕ) (W : Subgroup X) : Prop :=
  (IsSpGp (X ⧸ Subgroup.center X) m n ∧ IsSymplecticRootGroup X m n W) ∨
    (IsPSUGp (X ⧸ Subgroup.center X) m n ∧ IsUnitaryRootGroup X m n W)

private theorem wc85s0_exists_ne_one_of_one_lt_card {S : Subgroup X}
    (h : 1 < Nat.card S) : ∃ s ∈ S, s ≠ 1 := by
  by_contra hc
  push Not at hc
  have hbot : S = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    exact hc
  rw [hbot, Subgroup.card_bot] at h
  exact lt_irrefl 1 h

private theorem wc85s0_eq_of_ne_one {S : Subgroup X} (hS : Nat.card S = 2)
    {s : X} (hs : s ∈ S) (hs1 : s ≠ 1) {w : X} (hw : w ∈ S) (hw1 : w ≠ 1) :
    w = s := by
  rw [Nat.card_eq_two_iff' (1 : S)] at hS
  obtain ⟨y, -, huniq⟩ := hS
  have h1 : (⟨w, hw⟩ : S) = y := huniq _ fun h => hw1 (congrArg Subtype.val h)
  have h2 : (⟨s, hs⟩ : S) = y := huniq _ fun h => hs1 (congrArg Subtype.val h)
  exact congrArg Subtype.val (h1.trans h2.symm)

private theorem wc85s0_subsingleton_statedSp_zero {F : Type} [Field F] :
    Subsingleton (StatedSp 0 F) := by
  haveI : IsEmpty (Fin 0 ⊕ Fin 0) := inferInstance
  haveI : Subsingleton (Matrix (Fin 0 ⊕ Fin 0) (Fin 0 ⊕ Fin 0) F) := inferInstance
  haveI : Subsingleton (GL (Fin 0 ⊕ Fin 0) F) :=
    Subsingleton.units_of_isUnit (fun a _ => Subsingleton.elim a 1)
  infer_instance

private theorem wc85s0_not_transvection_zero {F : Type} [Field F]
    (g : ↥(StatedSp 0 F)) : ¬ IsSymplecticTransvectionIn 0 g := by
  intro h
  unfold IsSymplecticTransvectionIn at h
  have h0 : (((g : GL (Fin 0 ⊕ Fin 0) F) :
      Matrix (Fin 0 ⊕ Fin 0) (Fin 0 ⊕ Fin 0) F) - 1) = 0 := Subsingleton.elim _ _
  rw [h0] at h
  simpa using h

private theorem wc85s0_subsingleton_of_isSpGp_zero {Y : Type} [Group Y] {n : ℕ}
    (h : IsSpGp Y 0 n) : Subsingleton Y := by
  obtain ⟨k, hk, F, hFld, hFin, hFcard, ⟨e⟩⟩ := h
  have hk0 : k = 0 := by omega
  subst hk0
  haveI : Subsingleton (StatedSp 0 F) := wc85s0_subsingleton_statedSp_zero
  exact e.toEquiv.subsingleton

private theorem wc85s0_sympRoot_of_card_two_transvection {m : ℕ}
    (hS2 : Nat.card (barSub (kGenIn V H) φ V) = 2)
    (htr : ∀ s ∈ barSub (kGenIn V H) φ V, s ≠ 1 → IsSymplecticTransvection X m 1 s) :
    IsSymplecticRootGroup X m 1 (barSub (kGenIn V H) φ V) := by
  obtain ⟨s, hs, hs1⟩ := wc85s0_exists_ne_one_of_one_lt_card (by rw [hS2]; norm_num)
  obtain ⟨k, hk, F, hFld, hFin, hFcard, e, htrs⟩ := htr s hs hs1
  refine ⟨by rw [pow_one]; exact hS2, k, hk, F, hFld, hFin, hFcard, e, ?_⟩
  intro w hw hw1
  rw [wc85s0_eq_of_ne_one hS2 hs hs1 hw hw1]
  exact htrs

private theorem wc85s0_unitRoot_of_card_two_transvection {m : ℕ}
    (hS2 : Nat.card (barSub (kGenIn V H) φ V) = 2)
    (htr : ∀ s ∈ barSub (kGenIn V H) φ V, s ≠ 1 → IsUnitaryTransvection X m 1 s) :
    IsUnitaryRootGroup X m 1 (barSub (kGenIn V H) φ V) := by
  obtain ⟨s, hs, hs1⟩ := wc85s0_exists_ne_one_of_one_lt_card (by rw [hS2]; norm_num)
  obtain ⟨F, hFld, hFin, hFcard, e, htrs⟩ := htr s hs hs1
  refine ⟨by rw [pow_one]; exact hS2, F, hFld, hFin, hFcard, e, ?_⟩
  intro w hw hw1
  rw [wc85s0_eq_of_ne_one hS2 hs hs1 hw hw1]
  exact htrs

private theorem wc85s0_false_of_sympRoot_zero {n n' : ℕ}
    (hcardV : Nat.card (barSub (kGenIn V H) φ V) = 2 ^ n) (hn1 : 1 ≤ n)
    (hroot : IsSymplecticRootGroup X 0 n' (barSub (kGenIn V H) φ V)) : False := by
  obtain ⟨-, k, hk, F, hFld, hFin, hFcard, e, htr⟩ := hroot
  have hk0 : k = 0 := by omega
  subst hk0
  have hlt : 1 < Nat.card (barSub (kGenIn V H) φ V) := by
    rw [hcardV]
    exact Nat.one_lt_two_pow_iff.mpr (by omega : n ≠ 0)
  obtain ⟨w, hw, hw1⟩ := wc85s0_exists_ne_one_of_one_lt_card hlt
  exact wc85s0_not_transvection_zero (e (QuotientGroup.mk w)) (htr w hw hw1)

private theorem wc85s0_ordBC_two_pow (k n : ℕ) (hn : 1 ≤ n) :
    ordBC k (2 ^ n) = 2 ^ (n * k ^ 2) * ∏ i ∈ Finset.Icc 1 k, (2 ^ (2 * i * n) - 1) := by
  have hgcd : Nat.gcd 2 (2 ^ n - 1) = 1 :=
    Nat.coprime_two_left.mpr (CFSG.Timmesfeld.Orders.odd_two_pow_sub_one hn)
  rw [ordBC, hgcd, Nat.div_one]
  have h1 : (2 ^ n) ^ (k * k) = 2 ^ (n * k ^ 2) := by
    rw [← pow_mul]; ring_nf
  have h2 : (∏ i ∈ Finset.Icc 1 k, ((2 ^ n) ^ (2 * i) - 1)) =
      ∏ i ∈ Finset.Icc 1 k, (2 ^ (2 * i * n) - 1) := by
    apply Finset.prod_congr rfl
    intro i _
    rw [← pow_mul, show n * (2 * i) = 2 * i * n by ring]
  rw [h1, h2]

private theorem wc85s0_card_of_isSpGp {Y : Type} [Group Y] {k n : ℕ} (hk : 2 ≤ k)
    (h : IsSpGp Y (2 * k) n) : Nat.card Y = ordBC k (2 ^ n) := by
  obtain ⟨k', hk', F, hFld, hFin, hFcard, ⟨e⟩⟩ := h
  haveI := hFld
  haveI := hFin
  have hn1 : 1 ≤ n := by
    have h2 : 1 < 2 ^ n := by rw [← hFcard]; exact Finite.one_lt_card
    rcases Nat.eq_zero_or_pos n with rfl | h
    · simp at h2
    · exact h
  have hk'k : k' = k := by omega
  rw [hk'k] at e
  rw [Nat.card_congr e.toEquiv,
    @CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.card_statedSp F hFld hFin k, hFcard,
    wc85s0_ordBC_two_pow k n hn1]
  have h1 : (2 ^ n) ^ (k ^ 2) = 2 ^ (n * k ^ 2) := by rw [← pow_mul]
  have h2 : (∏ j ∈ Finset.Icc 1 k, ((2 ^ n) ^ (2 * j) - 1)) =
      ∏ i ∈ Finset.Icc 1 k, (2 ^ (2 * i * n) - 1) := by
    apply Finset.prod_congr rfl
    intro i _
    rw [← pow_mul, show n * (2 * i) = 2 * i * n by ring]
  rw [h1, h2]

private theorem wc85s0_card_of_isPSUGp {Y : Type} [Group Y] {m n : ℕ} (h : IsPSUGp Y m n) :
    Nat.card Y = ordTwistedA (m - 1) (2 ^ n) := by
  have h1 := CFSG.Blueprint.LieModel.admissible h
  obtain ⟨-, hf, hm3, -⟩ := h1
  obtain ⟨⟨-, -, -, -⟩, K, _, _, hK, ⟨e⟩⟩ :=
    CFSG.Blueprint.LieModel.statedClassicalModel_of_ne_zero (by omega) h
  rw [Nat.card_congr e.toEquiv,
    CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedSU Nat.prime_two hf hK
      (by omega : 2 ≤ m),
    ordTwistedA, Nat.sub_add_cancel (by omega : 1 ≤ m), mul_comm (m - 1) m]

private theorem wc85s0_not_isSpGp_isPSUGp {Y : Type} [Group Y] {m n : ℕ} (hm : 3 < m)
    (hSp : IsSpGp Y m n) (hPSU : IsPSUGp Y m n) : False := by
  have hSpCopy := hSp
  obtain ⟨k, hk, -⟩ := hSp
  have hk2 : 2 ≤ k := by omega
  have hn1 : 1 ≤ n := one_le_of_isSpGp hSpCopy
  have hSp' : IsSpGp Y (2 * k) n := by simpa [hk] using hSpCopy
  have hcardSp := wc85s0_card_of_isSpGp hk2 hSp'
  have hcardPSU := wc85s0_card_of_isPSUGp hPSU
  rcases Nat.lt_or_ge k 3 with hk3 | hk3
  · have hk2' : k = 2 := by omega
    subst hk2'
    exact (CFSG.RankThree.PartOne.S12K.ordTwistedA_ne_ordBC_two (u := m - 1) (f := n) (g := n)
      (by omega) hn1 hn1) (hcardPSU.symm.trans hcardSp)
  · exact (CFSG.Timmesfeld.Orders.ordBC_ne_ordTwistedA (n := k) (f := n) (u := m - 1) (g := n)
      hk3 hn1 (by omega) hn1) (hcardSp.symm.trans hcardPSU)

private theorem wc85s0_sp_of_shape {m n m' n' : ℕ}
    (hcardV : Nat.card (barSub (kGenIn V H) φ V) = 2 ^ n) (hm : 3 < m) (hn1 : 1 ≤ n)
    (h : IsSpGp (X ⧸ Subgroup.center X) m n ∨ IsPSUGp (X ⧸ Subgroup.center X) m n)
    (hSp' : IsSpGp (X ⧸ Subgroup.center X) m' n') (hm' : 3 < m')
    (hroot' : IsSymplecticRootGroup X m' n' (barSub (kGenIn V H) φ V)) :
    wc85s0_root X m n (barSub (kGenIn V H) φ V) := by
  have hSp'0 := hSp'
  rcases h with hSp | hPSU
  · obtain ⟨hmn, hnn, -⟩ :=
      spPSU_unique (m := m') (n := n') (m' := m) (n' := n) hm' hm (Or.inl hSp'0) (Or.inl hSp)
    subst hmn; subst hnn
    exact Or.inl ⟨hSp, hroot'⟩
  · obtain ⟨hmn, hnn, -⟩ :=
      spPSU_unique (m := m') (n := n') (m' := m) (n' := n) hm' hm (Or.inl hSp'0) (Or.inr hPSU)
    subst hmn; subst hnn
    exact (wc85s0_not_isSpGp_isPSUGp hm hSp'0 hPSU).elim

private theorem wc85s0_sp_small_of_shape {m n m' n' : ℕ}
    (hcardV : Nat.card (barSub (kGenIn V H) φ V) = 2 ^ n) (hm : 3 < m) (hn1 : 1 ≤ n)
    (h : IsSpGp (X ⧸ Subgroup.center X) m n ∨ IsPSUGp (X ⧸ Subgroup.center X) m n)
    (hSp' : IsSpGp (X ⧸ Subgroup.center X) m' n') (hm' : m' ≤ 3)
    (hroot' : IsSymplecticRootGroup X m' n' (barSub (kGenIn V H) φ V)) :
    wc85s0_root X m n (barSub (kGenIn V H) φ V) := by
  have hSp'0 := hSp'
  obtain ⟨k, hk, -⟩ := hSp'
  have hk01 : k = 0 ∨ k = 1 := by omega
  rcases hk01 with hk0 | hk1
  · have hm'0 : m' = 0 := by omega
    subst hm'0
    exact (wc85s0_false_of_sympRoot_zero hcardV hn1 hroot').elim
  · have hm'2 : m' = 2 := by omega
    subst hm'2
    exact (notSpPSU_of_isSpGp_two (by simpa using hSp'0) ⟨m, n, hm, h⟩).elim

private theorem wc85s0_psu_of_shape {m n m' n' : ℕ} (hm : 3 < m)
    (h : IsSpGp (X ⧸ Subgroup.center X) m n ∨ IsPSUGp (X ⧸ Subgroup.center X) m n)
    (hPSU' : IsPSUGp (X ⧸ Subgroup.center X) m' n')
    (hroot' : IsUnitaryRootGroup X m' n' (barSub (kGenIn V H) φ V)) :
    wc85s0_root X m n (barSub (kGenIn V H) φ V) := by
  have hm'3 : 3 ≤ m' := (three_le_of_isPSUGp hPSU').1
  by_cases hm3 : m' = 3
  · subst hm3
    exact (notSpPSU_of_isPSUGp_three hPSU' ⟨m, n, hm, h⟩).elim
  · have hm' : 3 < m' := by omega
    rcases h with hSp | hPSU
    · obtain ⟨hmn, hnn, -⟩ :=
        spPSU_unique (m := m') (n := n') (m' := m) (n' := n) hm' hm (Or.inr hPSU') (Or.inl hSp)
      subst hmn; subst hnn
      exact (wc85s0_not_isSpGp_isPSUGp hm hSp hPSU').elim
    · obtain ⟨hmn, hnn, -⟩ :=
        spPSU_unique (m := m') (n := n') (m' := m) (n' := n) hm' hm (Or.inr hPSU') (Or.inr hPSU)
      subst hmn; subst hnn
      exact Or.inr ⟨hPSU, hroot'⟩

private theorem wc85s0_sp_of_transvection {m n m' n' : ℕ}
    (hcardV : Nat.card (barSub (kGenIn V H) φ V) = 2 ^ n) (hm : 3 < m)
    (hS2 : Nat.card (barSub (kGenIn V H) φ V) = 2)
    (h : IsSpGp (X ⧸ Subgroup.center X) m n ∨ IsPSUGp (X ⧸ Subgroup.center X) m n)
    (hSp' : IsSpGp (X ⧸ Subgroup.center X) m' n') (hm' : 3 < m')
    (htr : ∀ s ∈ barSub (kGenIn V H) φ V, s ≠ 1 → IsSymplecticTransvection X m' n' s) :
    wc85s0_root X m n (barSub (kGenIn V H) φ V) := by
  have hSp'0 := hSp'
  obtain ⟨k, hk, -⟩ := hSp'
  have hn1 : n = 1 := by
    have h2 : 2 ^ n = 2 ^ 1 := by rw [← hcardV, hS2]; norm_num
    exact Nat.pow_right_injective (le_refl 2) h2
  subst hn1
  have hk2 : 2 ≤ k := by omega
  rcases h with hSp | hPSU
  · obtain ⟨hmn, hnn, -⟩ :=
      spPSU_unique (m := m') (n := n') (m' := m) (n' := 1) hm' hm (Or.inl hSp'0) (Or.inl hSp)
    subst hmn; subst hnn
    exact Or.inl ⟨hSp, wc85s0_sympRoot_of_card_two_transvection hS2 htr⟩
  · obtain ⟨hmn, hnn, -⟩ :=
      spPSU_unique (m := m') (n := n') (m' := m) (n' := 1) hm' hm (Or.inl hSp'0) (Or.inr hPSU)
    subst hmn; subst hnn
    exact (wc85s0_not_isSpGp_isPSUGp hm hSp'0 hPSU).elim

private theorem wc85s0_sp_small_of_transvection {m n m' n' : ℕ}
    (hm : 3 < m) (hS2 : Nat.card (barSub (kGenIn V H) φ V) = 2)
    (h : IsSpGp (X ⧸ Subgroup.center X) m n ∨ IsPSUGp (X ⧸ Subgroup.center X) m n)
    (hSp' : IsSpGp (X ⧸ Subgroup.center X) m' n') (hm' : m' ≤ 3)
    (htr : ∀ s ∈ barSub (kGenIn V H) φ V, s ≠ 1 → IsSymplecticTransvection X m' n' s) :
    wc85s0_root X m n (barSub (kGenIn V H) φ V) := by
  have hSp'0 := hSp'
  obtain ⟨k, hk, -⟩ := hSp'
  have hk01 : k = 0 ∨ k = 1 := by omega
  rcases hk01 with hk0 | hk1
  · have hm'0 : m' = 0 := by omega
    subst hm'0
    obtain ⟨s, hs, hs1⟩ := wc85s0_exists_ne_one_of_one_lt_card (by rw [hS2]; norm_num)
    obtain ⟨k₀, hk₀, F, hFld, hFin, hFcard, e, htrs⟩ := htr s hs hs1
    have hk₀0 : k₀ = 0 := by omega
    subst hk₀0
    exact (wc85s0_not_transvection_zero (e (QuotientGroup.mk s)) htrs).elim
  · have hm'2 : m' = 2 := by omega
    subst hm'2
    exact (notSpPSU_of_isSpGp_two (by simpa using hSp'0) ⟨m, n, hm, h⟩).elim

private theorem wc85s0_psu_of_transvection {m n m' n' : ℕ}
    (hcardV : Nat.card (barSub (kGenIn V H) φ V) = 2 ^ n) (hm : 3 < m)
    (hS2 : Nat.card (barSub (kGenIn V H) φ V) = 2)
    (h : IsSpGp (X ⧸ Subgroup.center X) m n ∨ IsPSUGp (X ⧸ Subgroup.center X) m n)
    (hPSU' : IsPSUGp (X ⧸ Subgroup.center X) m' n')
    (htr : ∀ s ∈ barSub (kGenIn V H) φ V, s ≠ 1 → IsUnitaryTransvection X m' n' s) :
    wc85s0_root X m n (barSub (kGenIn V H) φ V) := by
  have hm'3 : 3 ≤ m' := (three_le_of_isPSUGp hPSU').1
  by_cases hm3 : m' = 3
  · subst hm3
    exact (notSpPSU_of_isPSUGp_three hPSU' ⟨m, n, hm, h⟩).elim
  · have hn1 : n = 1 := by
      have h2 : 2 ^ n = 2 ^ 1 := by rw [← hcardV, hS2]; norm_num
      exact Nat.pow_right_injective (le_refl 2) h2
    subst hn1
    have hm' : 3 < m' := by omega
    rcases h with hSp | hPSU
    · obtain ⟨hmn, hnn, -⟩ :=
        spPSU_unique (m := m') (n := n') (m' := m) (n' := 1) hm' hm (Or.inr hPSU') (Or.inl hSp)
      subst hmn; subst hnn
      exact (wc85s0_not_isSpGp_isPSUGp hm hSp hPSU').elim
    · obtain ⟨hmn, hnn, -⟩ :=
        spPSU_unique (m := m') (n := n') (m' := m) (n' := 1) hm' hm (Or.inr hPSU') (Or.inr hPSU)
      subst hmn; subst hnn
      exact Or.inr ⟨hPSU, wc85s0_unitRoot_of_card_two_transvection hS2 htr⟩

section SwapTransvection

open CFSG.Quasithin.RonanE68 CFSG.ComponentClassification.UnbalancedCatalog.SpChain Matrix

private theorem wc85s0_rank_sub_one_conj {ι : Type} [Fintype ι] [DecidableEq ι] {F : Type}
    [Field F] {H : Subgroup (GL ι F)} (g h : ↥H) :
    Matrix.rank (((↑(h * g * h⁻¹) : GL ι F) : Matrix ι ι F) - 1) =
      Matrix.rank (((g : GL ι F) : Matrix ι ι F) - 1) := by
  set A : Matrix ι ι F := ((h : GL ι F) : Matrix ι ι F) with hA
  set B : Matrix ι ι F := ((g : GL ι F) : Matrix ι ι F) with hB
  have hcoe : ((↑(h * g * h⁻¹) : GL ι F) : Matrix ι ι F) = A * B * A⁻¹ := by
    rw [hA, hB, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv,
      Matrix.GeneralLinearGroup.coe_mul, Matrix.GeneralLinearGroup.coe_mul,
      Matrix.GeneralLinearGroup.coe_inv]
  have hAC : A * A⁻¹ = 1 := by
    rw [hA, ← Matrix.GeneralLinearGroup.coe_inv, ← Matrix.GeneralLinearGroup.coe_mul,
      mul_inv_cancel, Matrix.GeneralLinearGroup.coe_one]
  have hdetA : IsUnit A.det := by
    rw [hA, ← Matrix.GeneralLinearGroup.val_det_apply]
    exact (Matrix.GeneralLinearGroup.det (h : GL ι F)).isUnit
  have hdetC : IsUnit A⁻¹.det := by
    rw [hA, ← Matrix.GeneralLinearGroup.coe_inv, ← Matrix.GeneralLinearGroup.val_det_apply]
    exact (Matrix.GeneralLinearGroup.det ((h⁻¹ : ↥H) : GL ι F)).isUnit
  have hsub : A * B * A⁻¹ - 1 = A * (B - 1) * A⁻¹ := by
    rw [Matrix.mul_sub, Matrix.mul_one, Matrix.sub_mul, hAC]
  rw [hcoe, hsub, Matrix.rank_mul_eq_left_of_isUnit_det A⁻¹ (A * (B - 1)) hdetC,
    Matrix.rank_mul_eq_right_of_isUnit_det A (B - 1) hdetA]

private theorem wc85s0_isSymplecticTransvectionIn_conj {k : ℕ} {F : Type} [Field F]
    {g : ↥(StatedSp k F)} (hg : IsSymplecticTransvectionIn k g) (h : ↥(StatedSp k F)) :
    IsSymplecticTransvectionIn k (h * g * h⁻¹) := by
  unfold IsSymplecticTransvectionIn at hg ⊢
  rw [wc85s0_rank_sub_one_conj (H := StatedSp k F) g h]
  exact hg

private theorem wc85s0_rank_longRoot (c : ZMod 2) (hc : c ≠ 0) :
    Matrix.rank ((1 + Matrix.of (fun a b : Fin 2 ⊕ Fin 2 =>
      if a = Sum.inl 0 ∧ b = Sum.inr 0 then c else 0) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) (ZMod 2)) - 1) = 1 := by
  have e : ((1 + Matrix.of (fun a b : Fin 2 ⊕ Fin 2 =>
      if a = Sum.inl 0 ∧ b = Sum.inr 0 then c else 0) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) (ZMod 2)) - 1) =
      Matrix.vecMulVec (Pi.single (Sum.inl 0) c) (Pi.single (Sum.inr 0) 1) := by
    ext a b
    simp only [add_sub_cancel_left, Matrix.of_apply, vecMulVec_apply, Pi.single_apply]
    by_cases ha : a = Sum.inl 0 <;> by_cases hb : b = Sum.inr 0 <;> simp [ha, hb]
  rw [e]
  refine le_antisymm (Matrix.rank_vecMulVec_le _ _) ?_
  rw [Nat.one_le_iff_ne_zero]
  intro h0
  rw [Matrix.rank, Submodule.finrank_eq_zero, LinearMap.range_eq_bot] at h0
  have := congrFun (congrArg (fun f => f (Pi.single (Sum.inr 0) 1)) h0) (Sum.inl 0)
  simp [Matrix.mulVecLin_apply, mulVec_single_one, vecMulVec_apply] at this
  exact hc this

private abbrev wc85s0_antiSpU01 : ↥(antiSp (ZMod 2)) :=
  @uElt (ZMod 2) (ZMod.instField 2) (ZMod.charP 2) 0 0 1 0

private abbrev wc85s0_spU01 : ↥(StatedSp 2 (ZMod 2)) :=
  @antiSpEquiv (ZMod 2) (ZMod.instField 2) (ZMod.charP 2) wc85s0_antiSpU01

private theorem wc85s0_symplecticTransvectionIn_longRoot :
    IsSymplecticTransvectionIn 2 wc85s0_spU01 := by
  rw [IsSymplecticTransvectionIn]
  rw [show (((wc85s0_spU01 : StatedSp 2 (ZMod 2)) : GL (Fin 2 ⊕ Fin 2) (ZMod 2)) :
        Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) (ZMod 2)) =
      (glMat wc85s0_antiSpU01).submatrix antiIdx antiIdx from rfl,
    longMat_eq]
  have h2 : (Matrix.of fun row col : Fin 2 ⊕ Fin 2 =>
        (if row = col then (1 : ZMod 2) else 0) +
          (if row = Sum.inl 0 ∧ col = Sum.inr 0 then (1 : ZMod 2) else 0)) =
      1 + Matrix.of (fun a b : Fin 2 ⊕ Fin 2 =>
        if a = Sum.inl 0 ∧ b = Sum.inr 0 then (1 : ZMod 2) else 0) := by
    ext a b
    simp only [Matrix.of_apply, Matrix.add_apply, Matrix.one_apply]
  rw [h2]
  exact wc85s0_rank_longRoot 1 (by norm_num)

end SwapTransvection

theorem wc85s0_swap_transvection :
    ∃ θ : Equiv.Perm (Fin 6) ≃* ↥(StatedSp 2 (ZMod 2)),
      ∀ i j : Fin 6, i ≠ j → IsSymplecticTransvectionIn 2 (θ (Equiv.swap i j)) := by
  refine ⟨CFSG.Quasithin.RonanE68.Psi.symm, fun i j hij => ?_⟩
  have hbase0 : CFSG.Quasithin.RonanE68.Psi.symm (Equiv.swap 0 1) = wc85s0_spU01 := by
    rw [← show CFSG.Quasithin.RonanE68.Psi wc85s0_spU01 = Equiv.swap 0 1 from
        CFSG.Quasithin.RonanE68.Psi_long, MulEquiv.symm_apply_apply]
  have hbase : IsSymplecticTransvectionIn 2
      (CFSG.Quasithin.RonanE68.Psi.symm (Equiv.swap 0 1)) := by
    rw [hbase0]
    exact wc85s0_symplecticTransvectionIn_longRoot
  obtain ⟨σ, hσ⟩ := isConj_iff.mp (Equiv.Perm.isConj_swap (show (0 : Fin 6) ≠ 1 by decide) hij)
  have hconj : CFSG.Quasithin.RonanE68.Psi.symm (Equiv.swap i j) =
      CFSG.Quasithin.RonanE68.Psi.symm σ *
        CFSG.Quasithin.RonanE68.Psi.symm (Equiv.swap 0 1) *
        (CFSG.Quasithin.RonanE68.Psi.symm σ)⁻¹ := by
    rw [← hσ, map_mul, map_mul, map_inv]
  rw [hconj]
  exact wc85s0_isSymplecticTransvectionIn_conj hbase (CFSG.Quasithin.RonanE68.Psi.symm σ)

theorem wc85s0_symGp_case {m n n' : ℕ} (d : ShapeData V H T φ)
    (hcardV : Nat.card (barSub (kGenIn V H) φ V) = 2 ^ n) (hm : 3 < m)
    (h : IsSpGp (X ⧸ Subgroup.center X) m n ∨ IsPSUGp (X ⧸ Subgroup.center X) m n)
    (hS2 : Nat.card (barSub (kGenIn V H) φ V) = 2)
    (h5 : IsSymGp (X ⧸ fusionOddCore X) n') :
    (IsSpGp (X ⧸ Subgroup.center X) m n ∧
        IsSymplecticRootGroup X m n (barSub (kGenIn V H) φ V)) ∨
      (IsPSUGp (X ⧸ Subgroup.center X) m n ∧
        IsUnitaryRootGroup X m n (barSub (kGenIn V H) φ V)) := by
  haveI := d.finite
  change wc85s0_root X m n (barSub (kGenIn V H) φ V)
  obtain ⟨t, ht2, ht1, hSt, hD⟩ :=
    barSituation_map_two d.situation hS2 (MonoidHom.id X) Function.surjective_id (by simp)
  have htS : t ∈ barSub (kGenIn V H) φ V := by
    have h1 : barSub (kGenIn V H) φ V = Subgroup.zpowers t := by simpa using hSt
    rw [h1]
    exact Subgroup.mem_zpowers t
  have hn'4 : 4 ≤ n' := by
    by_contra hlt
    have hn'3 : n' ≤ 3 := by omega
    exact (notSpPSU_of_symGp_le_three hn'3 d.odd_card_center h5) ⟨m, n, hm, h⟩
  have h4 : IsSpGp (X ⧸ Subgroup.center X) 4 1 :=
    isSpGp_four_one_of_isSymGp_of_spPSU hn'4 d.odd_card_center h5 hm h
  obtain ⟨e₁⟩ := isSymGp_six_of_isSpGp_four_one h4
  have hOZ : fusionOddCore X = Subgroup.center X := by
    have hperm6 : fusionOddCore (Equiv.Perm (Fin 6)) = ⊥ :=
      CFSG.EvenSporadicStandard.M24Std.perm6_normal_odd _ inferInstance
        (CFSG.EvenSporadicStandard.Fin76b.odd_natCard_fusionOddCore (Equiv.Perm (Fin 6)))
    have hXZ : fusionOddCore (X ⧸ Subgroup.center X) = ⊥ :=
      CFSG.EvenSporadicStandard.Fin76b.fusionOddCore_eq_bot_of_mulEquiv e₁ hperm6
    refine le_antisymm ?_ (CFSG.EvenSporadicStandard.Fin76b.le_fusionOddCore d.odd_card_center)
    intro x hx
    haveI : ((fusionOddCore X).map (QuotientGroup.mk' (Subgroup.center X))).Normal :=
      Subgroup.Normal.map inferInstance (QuotientGroup.mk' _) (QuotientGroup.mk'_surjective _)
    have hodd : Odd
        (Nat.card ((fusionOddCore X).map (QuotientGroup.mk' (Subgroup.center X)))) :=
      Odd.of_dvd_nat (CFSG.EvenSporadicStandard.Fin76b.odd_natCard_fusionOddCore X)
        (Subgroup.card_map_dvd (H := fusionOddCore X)
          (QuotientGroup.mk' (Subgroup.center X)))
    have hle := CFSG.EvenSporadicStandard.Fin76b.le_fusionOddCore hodd
    rw [hXZ] at hle
    have hx' : (QuotientGroup.mk' (Subgroup.center X)) x ∈
        (fusionOddCore X).map (QuotientGroup.mk' (Subgroup.center X)) :=
      Subgroup.mem_map_of_mem _ hx
    have hx1 : (QuotientGroup.mk' (Subgroup.center X)) x = 1 := Subgroup.mem_bot.mp (hle hx')
    have hxker : x ∈ (QuotientGroup.mk' (Subgroup.center X)).ker := MonoidHom.mem_ker.mpr hx1
    rwa [QuotientGroup.ker_mk'] at hxker
  obtain ⟨e₀⟩ := h5
  have e₁' : X ⧸ fusionOddCore X ≃* Equiv.Perm (Fin 6) :=
    (QuotientGroup.quotientMulEquivOfEq hOZ).trans e₁
  have hn'6 : n' = 6 := by
    have hcard : Nat.card (Equiv.Perm (Fin n')) = Nat.card (Equiv.Perm (Fin 6)) :=
      Nat.card_congr (e₀.symm.trans e₁').toEquiv
    have hnf : Nat.factorial n' = 720 := by
      have hc := hcard
      rw [Nat.card_perm, Nat.card_perm, Nat.card_fin, Nat.card_fin] at hc
      norm_num at hc
      exact hc
    have hn5 : ¬ n' ≤ 5 := by
      intro h5
      have h8 : Nat.factorial n' ≤ Nat.factorial 5 := Nat.factorial_le h5
      rw [hnf] at h8
      norm_num at h8
    have hn7 : ¬ 7 ≤ n' := by
      intro h7
      have h8 : Nat.factorial 7 ≤ Nat.factorial n' := Nat.factorial_le h7
      rw [hnf] at h8
      norm_num at h8
    omega
  subst hn'6
  obtain ⟨e₂, he₂⟩ := w85g_exists_equiv_isSwap le_rfl e₀ ht2 hD
  obtain ⟨i, j, hij, hswap⟩ := he₂
  have hswap' : e₂ (QuotientGroup.mk t) = Equiv.swap i j := hswap
  obtain ⟨θ, hθ⟩ := wc85s0_swap_transvection
  let q : (X ⧸ Subgroup.center X) ≃* (X ⧸ fusionOddCore X) :=
    (QuotientGroup.quotientMulEquivOfEq hOZ).symm
  have hq : q (QuotientGroup.mk t) = QuotientGroup.mk t := by
    change (QuotientGroup.quotientMulEquivOfEq hOZ).symm (QuotientGroup.mk t) =
      QuotientGroup.mk t
    exact (QuotientGroup.quotientMulEquivOfEq hOZ).symm_apply_eq.mpr
      (QuotientGroup.quotientMulEquivOfEq_mk hOZ t).symm
  let e : (X ⧸ Subgroup.center X) ≃* ↥(StatedSp 2 (ZMod 2)) := q.trans (e₂.trans θ)
  have htr : IsSymplecticTransvectionIn 2 (e (QuotientGroup.mk t)) := by
    change IsSymplecticTransvectionIn 2 (θ (e₂ (q (QuotientGroup.mk t))))
    rw [hq, hswap']
    exact hθ i j hij
  obtain ⟨hm4, hn1, -⟩ :=
    spPSU_unique (m := 4) (n := 1) (m' := m) (n' := n) (by norm_num) hm (Or.inl h4) h
  subst hm4; subst hn1
  refine Or.inl ⟨h4, ?_⟩
  refine ⟨by rw [pow_one]; exact hS2, 2, by norm_num, ZMod 2, inferInstance, inferInstance,
    by norm_num, e, ?_⟩
  intro w hw hw1
  have hwt : w = t := wc85s0_eq_of_ne_one hS2 htS ht1 hw hw1
  rw [hwt]
  exact htr

theorem step0_root (g4 : W3Lem85TwoGap4)
    (g6 : W3Lem85TwoGap6) (d : ShapeData V H T φ)
    (halt : SevenElevenAlt X (barSub (kGenIn V H) φ V)) {m n : ℕ} (hm : 3 < m)
    (hr : rankBarV V H T = n)
    (h : IsSpGp (X ⧸ Subgroup.center X) m n ∨ IsPSUGp (X ⧸ Subgroup.center X) m n) :
    (IsSpGp (X ⧸ Subgroup.center X) m n ∧
        IsSymplecticRootGroup X m n (barSub (kGenIn V H) φ V)) ∨
      (IsPSUGp (X ⧸ Subgroup.center X) m n ∧
        IsUnitaryRootGroup X m n (barSub (kGenIn V H) φ V)) := by
  haveI := d.finite
  change wc85s0_root X m n (barSub (kGenIn V H) φ V)
  have hcardV : Nat.card (barSub (kGenIn V H) φ V) = 2 ^ n := by
    rw [← hr]
    exact d.hyp83.card_barSub_eq_two_pow_rankBarV d.eq_sup d.bar
  have hn1 : 1 ≤ n := by
    rcases h with hSp | hPSU
    · exact one_le_of_isSpGp hSp
    · exact (three_le_of_isPSUGp hPSU).2
  rcases halt with ⟨⟨n', h1⟩, -⟩ | h2 | ⟨-, h3⟩ | ⟨hS2, m', n', h4⟩ | ⟨hS2, n', h5⟩ |
    ⟨hS2, h6⟩
  · rcases h1 with ⟨m', hSp', hroot'⟩ | ⟨m', hPSU', hroot'⟩ | ⟨hSz, -⟩
    · by_cases hm' : 3 < m'
      · exact wc85s0_sp_of_shape hcardV hm hn1 h hSp' hm' hroot'
      · exact wc85s0_sp_small_of_shape hcardV hm hn1 h hSp' (by omega) hroot'
    · exact wc85s0_psu_of_shape hm h hPSU' hroot'
    · exact (notSpPSU_of_isSzGp hSz ⟨m, n, hm, h⟩).elim
  · obtain ⟨m', n', hm', hL, -, -⟩ := h2
    exact (notSpPSU_of_linear hm' hL ⟨m, n, hm, h⟩).elim
  · exact (notSpPSU_of_alt6 h3.1 ⟨m, n, hm, h⟩).elim
  · rcases h4 with ⟨hSp', htr⟩ | ⟨hPSU', htr⟩ | hOrth | hWr
    · by_cases hm' : 3 < m'
      · exact wc85s0_sp_of_transvection hcardV hm hS2 h hSp' hm' htr
      · exact wc85s0_sp_small_of_transvection hm hS2 h hSp' (by omega) htr
    · exact wc85s0_psu_of_transvection hcardV hm hS2 h hPSU' htr
    · exact (g4 X _ d.situation hS2 (Or.inl ⟨m', n', hOrth⟩) (d.central hS2)).elim
    · by_cases hm2 : 2 ≤ m'
      · exact (g4 X _ d.situation hS2 (Or.inr ⟨n', m', hm2, hWr⟩) (d.central hS2)).elim
      · have hm1 : m' ≤ 1 := by omega
        have hSp2 : IsSpGp (X ⧸ Subgroup.center X) (2 * m') n' :=
          isSpGp_of_isL2WrSymGp_le_one hm1 hWr
        have hm'01 : m' = 0 ∨ m' = 1 := by omega
        rcases hm'01 with hm'0 | hm'1
        · subst hm'0
          have h0 : IsSpGp (X ⧸ Subgroup.center X) 0 n' := by simpa using hSp2
          have hsub := wc85s0_subsingleton_of_isSpGp_zero h0
          have hbot := eq_bot_of_subsingleton_quot d.situation hsub
          rw [hbot, Subgroup.card_bot] at hS2
          norm_num at hS2
        · subst hm'1
          have h2' : IsSpGp (X ⧸ Subgroup.center X) 2 n' := by simpa using hSp2
          exact (notSpPSU_of_isSpGp_two h2' ⟨m, n, hm, h⟩).elim
  · change wc85s0_root X m n (barSub (kGenIn V H) φ V)
    exact wc85s0_symGp_case d hcardV hm h hS2 h5
  · exact (g6 X _ d.situation hS2 h6 (d.central hS2)).elim

end CFSG.LocalAnalysis.WeakClosure81

end
