module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.AppEPerm
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBGeneralLinearSmall
public import CFSG.Quasithin.Vol2.Ch10SecAShape
public import CFSG.Quasithin.Background.F1Models
public import CFSG.Quasithin.Vol2.Ch10SecKGA318

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecB.SL2Inv

open CFSG.Quasithin

variable {Kt : Type} [Group Kt]

theorem subsingleton_of_perfect_of_solvable {R : Type*} [Group R] [hs : Group.IsSolvable R]
    (hR : ⁅(⊤ : Subgroup R), (⊤ : Subgroup R)⁆ = ⊤) : Subsingleton R := by
  obtain ⟨n, hn⟩ := hs.solvable
  have h : ∀ k, derivedSeries R k = ⊤ := by
    intro k
    induction k with
    | zero => exact derivedSeries_zero R
    | succ k ih => rw [derivedSeries_succ, ih, hR]
  rw [h n] at hn
  constructor
  intro a b
  have ha : a ∈ (⊥ : Subgroup R) := hn ▸ Subgroup.mem_top a
  have hb : b ∈ (⊥ : Subgroup R) := hn ▸ Subgroup.mem_top b
  rw [Subgroup.mem_bot] at ha hb
  rw [ha, hb]

theorem two_le_of_perfect (hKp : ⁅(⊤ : Subgroup Kt), (⊤ : Subgroup Kt)⁆ = ⊤) {F : Type} [Field F]
    [Finite F] {m : ℕ} (hF : Nat.card F = 2 ^ m)
    (e : Kt ⧸ CFSG.pCore 2 Kt ≃* Matrix.SpecialLinearGroup (Fin 2) F) : 2 ≤ m := by
  by_contra hm
  have hF1 : 1 < Nat.card F := Finite.one_lt_card
  have hm1 : m = 1 := by
    rcases Nat.lt_or_ge m 1 with h | h
    · have : m = 0 := by omega
      subst this
      rw [pow_zero] at hF
      omega
    · omega
  subst hm1
  have : Group.IsSolvable (Matrix.GeneralLinearGroup (Fin 2) F) :=
    CFSG.ComponentClassification.CatalogueBGeneralLinear.generalLinear_two_small_solvable F
      (Or.inl (by rw [hF, pow_one]))
  have : Group.IsSolvable (Matrix.SpecialLinearGroup (Fin 2) F) :=
    Group.isSolvable_of_isSolvable_injective Matrix.SpecialLinearGroup.toGL_injective
  have hsol : Group.IsSolvable (Kt ⧸ CFSG.pCore 2 Kt) :=
    Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective
  have hperf : ⁅(⊤ : Subgroup (Kt ⧸ CFSG.pCore 2 Kt)), (⊤ : Subgroup (Kt ⧸ CFSG.pCore 2 Kt))⁆ =
      ⊤ := by
    have h := Subgroup.map_commutator (⊤ : Subgroup Kt) ⊤ (QuotientGroup.mk' (CFSG.pCore 2 Kt))
    rw [hKp, Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)] at h
    exact h.symm
  have hsub := subsingleton_of_perfect_of_solvable hperf
  let u : Matrix.SpecialLinearGroup (Fin 2) F := ⟨!![1, 1; 0, 1], by simp [Matrix.det_fin_two]⟩
  have hu : u ≠ 1 := by
    intro h
    have h' := congrArg (fun A : Matrix.SpecialLinearGroup (Fin 2) F =>
      (A : Matrix (Fin 2) (Fin 2) F) 0 1) h
    simp [u] at h'
  exact hu (e.symm.injective (Subsingleton.elim _ _))

theorem isSimpleGroup_quot (hKp : ⁅(⊤ : Subgroup Kt), (⊤ : Subgroup Kt)⁆ = ⊤) {F : Type} [Field F]
    [Finite F] {m : ℕ} (hF : Nat.card F = 2 ^ m)
    (e : Kt ⧸ CFSG.pCore 2 Kt ≃* Matrix.SpecialLinearGroup (Fin 2) F) :
    IsSimpleGroup (Kt ⧸ CFSG.pCore 2 Kt) := by
  have : Fintype F := Fintype.ofFinite F
  have hs : IsSimpleGroup (Matrix.SpecialLinearGroup (Fin 2) F) :=
    CFSG.QuasithinUnique.AppE.sl2_isSimpleGroup (two_le_of_perfect hKp hF e)
      (by rw [← Nat.card_eq_fintype_card, hF])
  exact e.isSimpleGroup

theorem two_dvd_card_quot (hKp : ⁅(⊤ : Subgroup Kt), (⊤ : Subgroup Kt)⁆ = ⊤) {F : Type} [Field F]
    [Finite F] {m : ℕ} (hF : Nat.card F = 2 ^ m)
    (e : Kt ⧸ CFSG.pCore 2 Kt ≃* Matrix.SpecialLinearGroup (Fin 2) F) :
    2 ∣ Nat.card (Kt ⧸ CFSG.pCore 2 Kt) := by
  have hm := two_le_of_perfect hKp hF e
  rw [Nat.card_congr e.toEquiv, SecA.card_SL_two_pow hF]
  exact Dvd.dvd.mul_right (dvd_pow_self 2 (by omega)) _

variable [Finite Kt]

theorem range_inf_eq_bot {Y : Type} [Group Y] [Finite Y] (τ : Kt →* Y)
    (hker : IsPGroup 2 ↥τ.ker) (hsimp : IsSimpleGroup (Kt ⧸ CFSG.pCore 2 Kt))
    (heven : 2 ∣ Nat.card (Kt ⧸ CFSG.pCore 2 Kt)) {F : Subgroup Y} [hFn : F.Normal]
    (hFodd : Odd (Nat.card F)) : τ.range ⊓ F = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hkerN : τ.ker ≤ CFSG.pCore 2 Kt := le_sSup ⟨τ.normal_ker, hker⟩
  set A := (τ.range ⊓ F).comap τ with hA
  have hAn : A.Normal := by
    constructor
    intro a ha g
    simp only [hA, Subgroup.mem_comap, map_mul, map_inv] at ha ⊢
    exact ⟨τ.range.mul_mem (τ.range.mul_mem ⟨g, rfl⟩ ha.1) (τ.range.inv_mem ⟨g, rfl⟩),
      hFn.conj_mem _ ha.2 _⟩
  have hAm : (A.map (QuotientGroup.mk' (CFSG.pCore 2 Kt))).Normal :=
    hAn.map _ (QuotientGroup.mk'_surjective _)
  rcases @IsSimpleGroup.eq_bot_or_eq_top_of_normal _ _ hsimp _ hAm with hbot | htop
  ·
    refine (Subgroup.eq_bot_iff_forall _).mpr fun y hy => ?_
    obtain ⟨a, rfl⟩ := hy.1
    have haA : a ∈ A := hy
    have haN : a ∈ CFSG.pCore 2 Kt := by
      have h : QuotientGroup.mk' (CFSG.pCore 2 Kt) a ∈ A.map (QuotientGroup.mk' _) :=
        ⟨a, haA, rfl⟩
      rw [hbot, Subgroup.mem_bot] at h
      exact (QuotientGroup.eq_one_iff a).mp h
    obtain ⟨k, hk⟩ := CFSG.pCore_isPGroup (p := 2) (G := Kt) ⟨a, haN⟩
    have h1 : orderOf (τ a) ∣ 2 ^ k := by
      refine orderOf_dvd_of_pow_eq_one ?_
      rw [← map_pow]
      have : a ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
      rw [this, map_one]
    have h2 : Odd (orderOf (τ a)) := hFodd.of_dvd_nat (Subgroup.orderOf_dvd_natCard F hy.2)
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h1
    rcases j with _ | j
    · rw [pow_zero] at hj
      exact orderOf_eq_one_iff.mp hj
    · exfalso
      rw [hj] at h2
      exact (Nat.not_even_iff_odd.mpr h2) (Nat.even_pow.mpr ⟨even_two, by omega⟩)
  ·
    exfalso
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 2 heven
    have hxA : x ∈ A.map (QuotientGroup.mk' (CFSG.pCore 2 Kt)) := by
      rw [htop]
      exact Subgroup.mem_top x
    obtain ⟨a, haA, rfl⟩ := hxA
    have ho : Odd (orderOf (τ a)) := hFodd.of_dvd_nat (Subgroup.orderOf_dvd_natCard F haA.2)
    have hao : a ^ orderOf (τ a) ∈ τ.ker := by
      rw [MonoidHom.mem_ker, map_pow, pow_orderOf_eq_one]
    have hmk : (QuotientGroup.mk' (CFSG.pCore 2 Kt) a) ^ orderOf (τ a) = 1 := by
      rw [← map_pow]
      exact (QuotientGroup.eq_one_iff _).mpr (hkerN hao)
    have h := orderOf_dvd_of_pow_eq_one hmk
    rw [hx] at h
    exact (Nat.not_even_iff_odd.mpr ho) (even_iff_two_dvd.mpr h)

end CFSG.Quasithin.Vol2.Ch10.SecB.SL2Inv
