module

public import CFSG.Quasithin.Background.F1Amalgam
public import CFSG.Quasithin.Background.A3ComponentsBasic

public section

namespace CFSG.Quasithin.H13.U4Par

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

variable {Y : Type} [Group Y]

@[expose] def IsMaxIn (A Y₀ : Subgroup Y) : Prop :=
  A < Y₀ ∧ ∀ A' : Subgroup Y, A ≤ A' → A' ≤ Y₀ → A' = A ∨ A' = Y₀

theorem map_conj_eq_of_mem_normalizer {H : Subgroup Y} {x : Y}
    (hx : x ∈ Subgroup.normalizer (H : Set Y)) : H.map (MulAut.conj x).toMonoidHom = H := by
  ext y
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact (Subgroup.mem_normalizer_iff.mp hx z).mp hz
  · intro hy
    refine ⟨x⁻¹ * y * x, ?_, by simp [mul_assoc]⟩
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hx) y).mp hy
    simpa [mul_assoc] using this

theorem map_conj_inv_map_conj (H : Subgroup Y) (x : Y) :
    (H.map (MulAut.conj x).toMonoidHom).map (MulAut.conj x⁻¹).toMonoidHom = H := by
  rw [Subgroup.map_map]
  convert Subgroup.map_id H
  ext y
  simp [mul_assoc]

theorem mem_normalizer_of_map_conj_eq {H : Subgroup Y} {x : Y}
    (hx : H.map (MulAut.conj x).toMonoidHom = H) : x ∈ Subgroup.normalizer (H : Set Y) := by
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · intro hy
    rw [← hx]
    exact ⟨y, hy, rfl⟩
  · intro hy
    rw [← hx] at hy
    obtain ⟨z, hz, hzy⟩ := hy
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hzy
    have : z = y := by
      have := congrArg (fun w => x⁻¹ * w * x) hzy
      simpa [mul_assoc] using this
    rwa [← this]

theorem IsMaxIn.map_conj {A Y₀ : Subgroup Y} (hA : IsMaxIn A Y₀) {x : Y}
    (hx : x ∈ Subgroup.normalizer (Y₀ : Set Y)) :
    IsMaxIn (A.map (MulAut.conj x).toMonoidHom) Y₀ := by
  set e := MulEquiv.mapSubgroup (MulAut.conj x)
  have he : ∀ H : Subgroup Y, H.map (MulAut.conj x).toMonoidHom = e H := fun H => rfl
  have hY : e Y₀ = Y₀ := map_conj_eq_of_mem_normalizer hx
  rw [he]
  refine ⟨lt_of_lt_of_eq (e.strictMono hA.1) hY, fun A' hA' hA'Y => ?_⟩
  have h1 : A ≤ e.symm A' := by
    rw [← e.le_iff_le, OrderIso.apply_symm_apply]
    exact hA'
  have h2 : e.symm A' ≤ Y₀ := by
    rw [← e.le_iff_le, OrderIso.apply_symm_apply, hY]
    exact hA'Y
  have h3 : A' = e (e.symm A') := (OrderIso.apply_symm_apply e A').symm
  rcases hA.2 _ h1 h2 with h | h
  · left
    rw [h3, h]
  · right
    rw [h3, h, hY]

theorem mem_normalizer_inf {T Y₀ : Subgroup Y} [Y₀.Normal] {x : Y}
    (hx : x ∈ Subgroup.normalizer (T : Set Y)) :
    x ∈ Subgroup.normalizer ((T ⊓ Y₀ : Subgroup Y) : Set Y) := by
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · rintro ⟨hyT, hyY⟩
    exact ⟨(Subgroup.mem_normalizer_iff.mp hx y).mp hyT, ‹Y₀.Normal›.conj_mem y hyY x⟩
  · rintro ⟨hyT, hyY⟩
    refine ⟨(Subgroup.mem_normalizer_iff.mp hx y).mpr hyT, ?_⟩
    have := ‹Y₀.Normal›.conj_mem _ hyY x⁻¹
    simpa [mul_assoc] using this

theorem mem_normalizer_inf_normalizer {H Y₀ : Subgroup Y} [Y₀.Normal] {x : Y}
    (hx : x ∈ Subgroup.normalizer (H : Set Y)) :
    x ∈ Subgroup.normalizer ((Y₀ ⊓ Subgroup.normalizer (H : Set Y) : Subgroup Y) : Set Y) := by
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · rintro ⟨hyY, hyN⟩
    exact ⟨‹Y₀.Normal›.conj_mem y hyY x, Subgroup.mul_mem _ (Subgroup.mul_mem _ hx hyN)
      (Subgroup.inv_mem _ hx)⟩
  · rintro ⟨hyY, hyN⟩
    have h1 := ‹Y₀.Normal›.conj_mem _ hyY x⁻¹
    have h2 := Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hx) hyN) hx
    simp only [inv_inv, ← mul_assoc, inv_mul_cancel, one_mul] at h1 h2
    simp only [mul_assoc, inv_mul_cancel, mul_one] at h1 h2
    exact ⟨h1, h2⟩

theorem commutator_le_of_index_le_two [Finite Y] {Y₀ : Subgroup Y} (hidx : Y₀.index ≤ 2) :
    ⁅(⊤ : Subgroup Y), (⊤ : Subgroup Y)⁆ ≤ Y₀ := by
  have hpos : Y₀.index ≠ 0 := Subgroup.index_ne_zero_of_finite
  rcases (by omega : Y₀.index = 1 ∨ Y₀.index = 2) with h1 | h2
  · rw [Subgroup.index_eq_one.mp h1]
    exact le_top
  · rw [Subgroup.commutator_le]
    intro a _ b _
    rw [commutatorElement_def, mul_assoc, ← mul_inv_rev,
      Subgroup.mul_mem_iff_of_index_two h2, Subgroup.inv_mem_iff,
      Subgroup.mul_mem_iff_of_index_two h2, Subgroup.mul_mem_iff_of_index_two h2]
    tauto

theorem perfectCore_eq_of_index_le_two [Finite Y] {Y₀ M P : Subgroup Y} (hidx : Y₀.index ≤ 2)
    (hPM : P ≤ M) (hMP : M ⊓ Y₀ ≤ P) : perfectCore M = perfectCore P := by
  refine le_antisymm ?_ (perfectCore_mono hPM)
  have h1 : ⁅M, M⁆ ≤ P := by
    refine le_trans (le_inf (Subgroup.commutator_le_self M) ?_) hMP
    exact (Subgroup.commutator_mono le_top le_top).trans (commutator_le_of_index_le_two hidx)
  have key : ∀ n, derivedSeriesOf M (n + 1) ≤ derivedSeriesOf P n := by
    intro n
    induction n with
    | zero => exact h1
    | succ n ih =>
      rw [derivedSeriesOf_succ, derivedSeriesOf_succ]
      exact Subgroup.commutator_mono ih ih
  exact le_iInf fun n => (perfectCore_le_derivedSeriesOf M (n + 1)).trans (key n)

theorem eq_normalizer_of_isYAmalgamPair [Finite Y] {Y₀ : Subgroup Y} [Y₀.Normal]
    (hidx : Y₀.index ≤ 2)
    (hsimple : ∀ N : Subgroup Y, N ≤ Y₀ → Y₀ ≤ Subgroup.normalizer (N : Set Y) →
      N = ⊥ ∨ N = Y₀)
    (hnot2 : ¬ IsPGroup 2 Y₀)
    {T M₁ M : Subgroup Y} (hpair : IsYAmalgamPair T M₁ M) (P : Fin 2 → Subgroup Y)
    (hBP : ∀ i, Y₀ ⊓ Subgroup.normalizer ((T ⊓ Y₀ : Subgroup Y) : Set Y) ≤ P i)
    (hPmax : ∀ i, IsMaxIn (P i) Y₀)
    (hPuniq : ∀ A : Subgroup Y, IsMaxIn A Y₀ →
      Y₀ ⊓ Subgroup.normalizer ((T ⊓ Y₀ : Subgroup Y) : Set Y) ≤ A → ∃ i, A = P i)
    (hne : P 0 ≠ P 1) (hO : ∀ i, CFSG.Open.pCoreOf 2 (P i) ≠ ⊥)
    (hswap : ∀ x : Y, (P 0).map (MulAut.conj x).toMonoidHom ≠ P 1) :
    ∃ i, M = Subgroup.normalizer ((P i : Subgroup Y) : Set Y) ∧ M ⊓ Y₀ = P i ∧
      perfectCore M = perfectCore (P i) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hY₀n := ‹Y₀.Normal›
  have hnormY : ∀ x : Y, x ∈ Subgroup.normalizer (Y₀ : Set Y) := fun x =>
    Subgroup.mem_normalizer_iff.mpr fun y => ⟨fun hy => hY₀n.conj_mem y hy x, fun hy => by
      have := hY₀n.conj_mem _ hy x⁻¹
      simpa [mul_assoc] using this⟩
  have hR : ∀ R : Subgroup Y, R ≠ ⊥ → IsPGroup 2 R →
      ¬ Y₀ ≤ Subgroup.normalizer (R : Set Y) := by
    intro R hR1 hR2 hRY
    have h0 : R ⊓ Y₀ = ⊥ := by
      have hnorm : Y₀ ≤ Subgroup.normalizer ((R ⊓ Y₀ : Subgroup Y) : Set Y) := fun y hy =>
        mem_normalizer_inf (Y₀ := Y₀) (hRY hy)
      rcases hsimple (R ⊓ Y₀) inf_le_right hnorm with h | h
      · exact h
      · exfalso
        exact hnot2 (hR2.to_le (h ▸ inf_le_left))
    have hpos : Y₀.index ≠ 0 := Subgroup.index_ne_zero_of_finite
    have htop : Subgroup.normalizer (R : Set Y) = ⊤ := by
      rcases (by omega : Y₀.index = 1 ∨ Y₀.index = 2) with h1 | h2
      · exfalso
        rw [Subgroup.index_eq_one.mp h1, inf_top_eq] at h0
        exact hR1 h0
      · obtain ⟨t, ht1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hR1
        have htY : (t : Y) ∉ Y₀ := fun h => ht1 (Subtype.ext (by
          have : (t : Y) ∈ R ⊓ Y₀ := ⟨t.2, h⟩
          rw [h0, Subgroup.mem_bot] at this
          exact this))
        rw [eq_top_iff]
        intro y _
        by_cases hy : y ∈ Y₀
        · exact hRY hy
        · have hyt : y * (t : Y)⁻¹ ∈ Y₀ := by
            rw [Subgroup.mul_mem_iff_of_index_two h2, Subgroup.inv_mem_iff]
            tauto
          have : y = (y * (t : Y)⁻¹) * t := by group
          rw [this]
          exact Subgroup.mul_mem _ (hRY hyt) (Subgroup.le_normalizer t.2)
    have hloc : IsTwoLocal (⊤ : Subgroup Y) := ⟨R, hR1, hR2, htop.symm⟩
    have hM1 := ((hpair.2.2 M₁).mpr (Or.inl rfl)).1
    have hM := ((hpair.2.2 M).mpr (Or.inr rfl)).1
    have e1 := hM1.2 ⊤ hloc le_top
    have e2 := hM.2 ⊤ hloc le_top
    exact hpair.2.1 (e1.symm.trans e2)
  have hP0 : ∀ i, P i ≠ ⊥ := fun i hb => hO i (by
    rw [eq_bot_iff]
    exact (CFSG.LieType.BorelTits.pCoreOf_le 2 (P i)).trans hb.le)
  have hNP : ∀ i, Y₀ ⊓ Subgroup.normalizer ((P i : Subgroup Y) : Set Y) = P i := by
    intro i
    rcases (hPmax i).2 _ (le_inf (hPmax i).1.le Subgroup.le_normalizer) inf_le_left with h | h
    · exact h
    · exfalso
      have hn : Y₀ ≤ Subgroup.normalizer ((P i : Subgroup Y) : Set Y) := by
        rw [← h]; exact inf_le_right
      rcases hsimple (P i) (hPmax i).1.le hn with h' | h'
      · exact hP0 i h'
      · exact (hPmax i).1.ne h'
  have hNO : ∀ i, Subgroup.normalizer ((P i : Subgroup Y) : Set Y) =
      Subgroup.normalizer ((CFSG.Open.pCoreOf 2 (P i) : Subgroup Y) : Set Y) := by
    intro i
    apply le_antisymm (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 _)
    intro x hx
    have hYO : Y₀ ⊓ Subgroup.normalizer ((CFSG.Open.pCoreOf 2 (P i) : Subgroup Y) : Set Y) =
        P i := by
      rcases (hPmax i).2 _ (le_inf (hPmax i).1.le
        (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (P i))) inf_le_left with h | h
      · exact h
      · exfalso
        have hn : Y₀ ≤ Subgroup.normalizer
            ((CFSG.Open.pCoreOf 2 (P i) : Subgroup Y) : Set Y) := by
          rw [← h]; exact inf_le_right
        rcases hsimple _ ((CFSG.LieType.BorelTits.pCoreOf_le 2 (P i)).trans (hPmax i).1.le) hn
          with h' | h'
        · exact hO i h'
        · have := (CFSG.LieType.BorelTits.pCoreOf_le 2 (P i)).trans_lt (hPmax i).1
          rw [h'] at this
          exact lt_irrefl _ this
    rw [← hYO]
    exact mem_normalizer_inf_normalizer (Y₀ := Y₀) hx
  have hmax : ∀ i, IsMaximalTwoLocal (Subgroup.normalizer ((P i : Subgroup Y) : Set Y)) := by
    intro i
    refine ⟨⟨CFSG.Open.pCoreOf 2 (P i), hO i, CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _,
      hNO i⟩, ?_⟩
    rintro _ ⟨R, hR1, hR2, rfl⟩ hle
    have hPR : P i ≤ Y₀ ⊓ Subgroup.normalizer (R : Set Y) :=
      le_inf (hPmax i).1.le (Subgroup.le_normalizer.trans hle)
    rcases (hPmax i).2 _ hPR inf_le_left with h | h
    · apply le_antisymm _ hle
      intro x hx
      rw [← h]
      exact mem_normalizer_inf_normalizer (Y₀ := Y₀) hx
    · exfalso
      exact hR R hR1 hR2 (by rw [← h]; exact inf_le_right)
  have hNT : ∀ i, Subgroup.normalizer (T : Set Y) ≤
      Subgroup.normalizer ((P i : Subgroup Y) : Set Y) := by
    intro i x hx
    have hxB : x ∈ Subgroup.normalizer
        ((Y₀ ⊓ Subgroup.normalizer ((T ⊓ Y₀ : Subgroup Y) : Set Y) : Subgroup Y) : Set Y) :=
      mem_normalizer_inf_normalizer (Y₀ := Y₀) (mem_normalizer_inf (Y₀ := Y₀) hx)
    have hBx := map_conj_eq_of_mem_normalizer hxB
    have hmaxx := (hPmax i).map_conj (hnormY x)
    obtain ⟨j, hj⟩ := hPuniq _ hmaxx (by rw [← hBx]; exact Subgroup.map_mono (hBP i))
    by_cases hij : i = j
    · subst hij
      exact mem_normalizer_of_map_conj_eq hj
    · exfalso
      have hcases : (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0) := by
        fin_cases i <;> fin_cases j <;> simp_all
      rcases hcases with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact hswap x hj
      · apply hswap x⁻¹
        rw [← hj]
        exact map_conj_inv_map_conj _ x
  have hLne : Subgroup.normalizer ((P 0 : Subgroup Y) : Set Y) ≠
      Subgroup.normalizer ((P 1 : Subgroup Y) : Set Y) := by
    intro h
    apply hne
    rw [← hNP 0, ← hNP 1, h]
  have hL : ∀ i, Subgroup.normalizer ((P i : Subgroup Y) : Set Y) = M₁ ∨
      Subgroup.normalizer ((P i : Subgroup Y) : Set Y) = M := fun i =>
    (hpair.2.2 _).mp ⟨hmax i, hNT i⟩
  obtain ⟨i, hi⟩ : ∃ i, M = Subgroup.normalizer ((P i : Subgroup Y) : Set Y) := by
    rcases hL 0 with h0 | h0
    · rcases hL 1 with h1 | h1
      · exact absurd (h0.trans h1.symm) hLne
      · exact ⟨1, h1.symm⟩
    · exact ⟨0, h0.symm⟩
  have hMY : M ⊓ Y₀ = P i := by rw [hi, inf_comm, hNP i]
  refine ⟨i, hi, hMY, perfectCore_eq_of_index_le_two hidx ?_ hMY.le⟩
  rw [hi]
  exact Subgroup.le_normalizer

end CFSG.Quasithin.H13.U4Par
