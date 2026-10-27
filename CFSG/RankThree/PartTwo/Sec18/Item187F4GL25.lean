module

public import CFSG.Quasithin.EmptyFaithful.SBc16FDec
public import Mathlib.GroupTheory.SpecificGroups.Quaternion
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.SubgroupConj

public section

namespace CFSG.RankThree.PartTwo.Sec18.Item187Proof

open CFSG.Quasithin.SBc16 (GL25)
open scoped commutatorElement Pointwise

instance fact_prime_five_F4a : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩

private theorem core_order3 : ∀ a b c d : ZMod 5,
    (!![a, b; c, d] : Matrix (Fin 2) (Fin 2) (ZMod 5)) ^ 3 = 1 →
    (!![a, b; c, d] : Matrix (Fin 2) (Fin 2) (ZMod 5)) ≠ 1 →
    (!![a, b; c, d] : Matrix (Fin 2) (Fin 2) (ZMod 5)) * !![a, b; c, d] + !![a, b; c, d] + 1 = 0 := by
  decide +kernel

theorem gl25_order_three_charpoly (g : GL25) (h3 : g ^ 3 = 1) (h1 : g ≠ 1) :
    ((g : Matrix (Fin 2) (Fin 2) (ZMod 5)) * g + g + 1 = 0) := by
  have hM3 : (g : Matrix (Fin 2) (Fin 2) (ZMod 5)) ^ 3 = 1 := by
    have := congrArg Units.val h3
    simpa using this
  have hM1 : (g : Matrix (Fin 2) (Fin 2) (ZMod 5)) ≠ 1 := fun h => h1 (Units.ext h)
  have hE := Matrix.eta_fin_two (g : Matrix (Fin 2) (Fin 2) (ZMod 5))
  rw [hE] at hM3 hM1 ⊢
  exact core_order3 _ _ _ _ hM3 hM1

section Commutators

variable {G : Type} [Group G]

theorem le_normalizer_commutator_left (P X : Subgroup G) :
    P ≤ Subgroup.normalizer ((⁅P, X⁆ : Subgroup G) : Set G) := by
  have key : ∀ h ∈ P, ∀ y ∈ ⁅P, X⁆, h * y * h⁻¹ ∈ ⁅P, X⁆ := by
    intro h hh y hy
    have hle : ⁅P, X⁆ ≤ (⁅P, X⁆ : Subgroup G).comap (MulAut.conj h).toMonoidHom := by
      rw [Subgroup.commutator_le]
      intro a ha x hx
      show h * ⁅a, x⁆ * h⁻¹ ∈ ⁅P, X⁆
      rw [show h * ⁅a, x⁆ * h⁻¹ = ⁅h * a, x⁆ * ⁅h, x⁆⁻¹ by
        simp only [commutatorElement_def]; group]
      exact Subgroup.mul_mem _ (Subgroup.commutator_mem_commutator (P.mul_mem hh ha) hx)
        (Subgroup.inv_mem _ (Subgroup.commutator_mem_commutator hh hx))
    exact hle hy
  intro h hh
  rw [Subgroup.mem_normalizer_iff]
  intro y
  refine ⟨key h hh y, fun hy => ?_⟩
  have := key h⁻¹ (P.inv_mem hh) _ hy
  simpa [mul_assoc] using this

theorem le_normalizer_commutator_right' (P X : Subgroup G) :
    X ≤ Subgroup.normalizer ((⁅P, X⁆ : Subgroup G) : Set G) := by
  have key : ∀ x ∈ X, ∀ y ∈ ⁅P, X⁆, x * y * x⁻¹ ∈ ⁅P, X⁆ := by
    intro x hx y hy
    have hle : ⁅P, X⁆ ≤ (⁅P, X⁆ : Subgroup G).comap (MulAut.conj x).toMonoidHom := by
      rw [Subgroup.commutator_le]
      intro a ha b hb
      show x * ⁅a, b⁆ * x⁻¹ ∈ ⁅P, X⁆
      rw [show x * ⁅a, b⁆ * x⁻¹ = ⁅a, x⁆⁻¹ * ⁅a, x * b⁆ by
        simp only [commutatorElement_def]; group]
      exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.commutator_mem_commutator ha hx))
        (Subgroup.commutator_mem_commutator ha (X.mul_mem hx hb))
    exact hle hy
  intro x hx
  rw [Subgroup.mem_normalizer_iff]
  intro y
  refine ⟨key x hx y, fun hy => ?_⟩
  have := key x⁻¹ (X.inv_mem hx) _ hy
  simpa [mul_assoc] using this

theorem coprime_commutator_commutator_eq' {P X : Subgroup G}
    (hXP : X ≤ Subgroup.normalizer (P : Set G)) (hcop : Nat.Coprime (Nat.card X) (Nat.card P)) :
    ⁅⁅P, X⁆, X⁆ = ⁅P, X⁆ := by
  classical
  have : Subgroup.Normalizes X P := ⟨hXP⟩
  have h2 : CFSG.commutatorAction₂ (A := ↥X) (G := ↥P) =
      CFSG.commutatorAction (A := ↥X) (G := ↥P) :=
    CFSG.commutatorAction₂_eq_commutatorAction_of_coprime (G := ↥P) (A := ↥X) hcop
  have hmap : (CFSG.commutatorAction (A := ↥X) (G := ↥P)).map P.subtype = ⁅P, X⁆ :=
    CFSG.commutatorAction_subgroup_conj_map_eq_commutator P X hXP
  have hmap2 : (CFSG.commutatorAction₂ (A := ↥X) (G := ↥P)).map P.subtype ≤ ⁅⁅P, X⁆, X⁆ := by
    let C : Subgroup ↥P := CFSG.commutatorAction (A := ↥X) (G := ↥P)
    let S : Set ↥P := {x : ↥P | ∃ a : ↥X, ∃ h : ↥P, h ∈ C ∧ x = h⁻¹ * (a • h)}
    calc (CFSG.commutatorAction₂ (A := ↥X) (G := ↥P)).map P.subtype =
          (Subgroup.closure S).map P.subtype := rfl
      _ = Subgroup.closure (P.subtype '' S) := by
        simpa using (MonoidHom.map_closure (f := P.subtype) S)
      _ ≤ ⁅⁅P, X⁆, X⁆ := by
        refine (Subgroup.closure_le (K := ⁅⁅P, X⁆, X⁆)).2 ?_
        rintro _ ⟨y, hy, rfl⟩
        rcases hy with ⟨a, h, hhC, rfl⟩
        have hhcomm : (h : G) ∈ ⁅P, X⁆ := by
          rw [← hmap]
          exact Subgroup.mem_map_of_mem P.subtype hhC
        have hcomm : ⁅(h : G)⁻¹, (a : G)⁆ ∈ ⁅⁅P, X⁆, X⁆ :=
          Subgroup.commutator_mem_commutator ((⁅P, X⁆ : Subgroup G).inv_mem hhcomm) a.2
        simpa [commutatorElement_def, Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe,
          hXP, mul_assoc] using hcomm
  refine le_antisymm ?_ fun x hx => ?_
  · exact (Subgroup.le_normalizer_iff_commutator_le_left).mp (le_normalizer_commutator_right' P X)
  · rw [← hmap, ← h2] at hx
    exact hmap2 hx

end Commutators

private theorem rel_entries {M : Matrix (Fin 2) (Fin 2) (ZMod 5)} (hR : M * M + M + 1 = 0) :
    M 0 1 ≠ 0 ∧ M 0 0 + M 1 1 + 1 = 0 ∧ M 0 0 * M 1 1 - M 0 1 * M 1 0 - 1 = 0 := by
  have e00 : M 0 0 * M 0 0 + M 0 1 * M 1 0 + M 0 0 + 1 = 0 := by
    simpa [Matrix.mul_apply, Fin.sum_univ_two] using congrFun (congrFun hR 0) 0
  have e01 : M 0 0 * M 0 1 + M 0 1 * M 1 1 + M 0 1 = 0 := by
    simpa [Matrix.mul_apply, Fin.sum_univ_two] using congrFun (congrFun hR 0) 1
  have hq : M 0 1 ≠ 0 := by
    intro h0
    have h := e00
    rw [h0, zero_mul, add_zero] at h
    have key : ∀ p : ZMod 5, p * p + p + 1 ≠ 0 := by decide
    exact key _ h
  have hA : M 0 0 + M 1 1 + 1 = 0 := by
    have h : M 0 1 * (M 0 0 + M 1 1 + 1) = 0 := by linear_combination e01
    exact (mul_eq_zero.1 h).resolve_left hq
  refine ⟨hq, hA, ?_⟩
  linear_combination M 0 0 * hA - e00

private theorem comm_e01 {R : Type*} [CommRing R] (x u m : R) (hu : u * m = 1) : x = x * u * m := by
  linear_combination (-x) * hu

private theorem comm_e10 {R : Type*} [CommRing R] (x01 x10 u m01 m10 : R) (E1 : x01 * m10 = m01 * x10)
    (hu : u * m01 = 1) : x10 = x01 * u * m10 := by
  linear_combination (-u) * E1 - x10 * hu

private theorem comm_e11 {R : Type*} [CommRing R] (x00 x01 x11 u m00 m01 m11 : R)
    (E2 : x00 * m01 + x01 * m11 = m00 * x01 + m01 * x11) (hu : u * m01 = 1) :
    x11 = (x00 - x01 * u * m00) * 1 + x01 * u * m11 := by
  linear_combination (-u) * E2 - (x11 - x00) * hu

private theorem commutant_form {M X : Matrix (Fin 2) (Fin 2) (ZMod 5)} (hq : M 0 1 ≠ 0)
    (hX : X * M = M * X) :
    ∃ a b : ZMod 5, X = a • (1 : Matrix (Fin 2) (Fin 2) (ZMod 5)) + b • M := by
  obtain ⟨u, hu⟩ : ∃ u : ZMod 5, u * M 0 1 = 1 := ⟨(M 0 1)⁻¹, inv_mul_cancel₀ hq⟩
  have E1 : X 0 1 * M 1 0 = M 0 1 * X 1 0 := by
    have h := congrFun (congrFun hX 0) 0
    simp only [Matrix.mul_apply, Fin.sum_univ_two] at h
    linear_combination h
  have E2 : X 0 0 * M 0 1 + X 0 1 * M 1 1 = M 0 0 * X 0 1 + M 0 1 * X 1 1 := by
    have h := congrFun (congrFun hX 0) 1
    simp only [Matrix.mul_apply, Fin.sum_univ_two] at h
    linear_combination h
  refine ⟨X 0 0 - X 0 1 * u * M 0 0, X 0 1 * u, ?_⟩
  refine Matrix.ext (Fin.forall_fin_two.2 ⟨Fin.forall_fin_two.2 ⟨?_, ?_⟩, Fin.forall_fin_two.2 ⟨?_, ?_⟩⟩)
  · show X 0 0 = ((X 0 0 - X 0 1 * u * M 0 0) • (1 : Matrix (Fin 2) (Fin 2) (ZMod 5)) +
      (X 0 1 * u) • M) 0 0
    simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul]
    ring
  · show X 0 1 = ((X 0 0 - X 0 1 * u * M 0 0) • (1 : Matrix (Fin 2) (Fin 2) (ZMod 5)) +
      (X 0 1 * u) • M) 0 1
    simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply_ne (show (0 : Fin 2) ≠ 1 by decide),
      smul_eq_mul, mul_zero, zero_add]
    exact comm_e01 _ _ _ hu
  · show X 1 0 = ((X 0 0 - X 0 1 * u * M 0 0) • (1 : Matrix (Fin 2) (Fin 2) (ZMod 5)) +
      (X 0 1 * u) • M) 1 0
    simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply_ne (show (1 : Fin 2) ≠ 0 by decide),
      smul_eq_mul, mul_zero, zero_add]
    exact comm_e10 _ _ _ _ _ E1 hu
  · show X 1 1 = ((X 0 0 - X 0 1 * u * M 0 0) • (1 : Matrix (Fin 2) (Fin 2) (ZMod 5)) +
      (X 0 1 * u) • M) 1 1
    simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul]
    exact comm_e11 _ _ _ _ _ _ _ E2 hu

private def pwF : ℕ → ZMod 5 × ZMod 5
  | 0 => (1, 0)
  | k + 1 => (2 * (pwF k).1 - (pwF k).2, (pwF k).1 + (pwF k).2)

private theorem pwF_surj : ∀ a b : ZMod 5, ¬ (a = 0 ∧ b = 0) → ∃ k < 24, pwF k = (a, b) := by
  decide +kernel

private theorem pwF_spec {M : Matrix (Fin 2) (Fin 2) (ZMod 5)} (hM2 : M * M = -M - 1) (k : ℕ) :
    ((2 : ZMod 5) • (1 : Matrix (Fin 2) (Fin 2) (ZMod 5)) + M) ^ k =
      (pwF k).1 • (1 : Matrix (Fin 2) (Fin 2) (ZMod 5)) + (pwF k).2 • M := by
  induction k with
  | zero => simp [pwF]
  | succ k ih =>
    rw [pow_succ, ih]
    have step : ((pwF k).1 • (1 : Matrix (Fin 2) (Fin 2) (ZMod 5)) + (pwF k).2 • M) *
        ((2 : ZMod 5) • (1 : Matrix (Fin 2) (Fin 2) (ZMod 5)) + M) =
        (2 * (pwF k).1 - (pwF k).2) • (1 : Matrix (Fin 2) (Fin 2) (ZMod 5)) +
          ((pwF k).1 + (pwF k).2) • M := by
      simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, one_mul, mul_one, hM2]
      module
    rw [step]
    rfl

theorem gl25_centralizer_cyclic (g : GL25) (hg : orderOf g = 3) :
    IsCyclic ↥(Subgroup.centralizer ({g} : Set GL25)) := by
  have h3 : g ^ 3 = 1 := by rw [← hg]; exact pow_orderOf_eq_one g
  have h1 : g ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hg
    omega
  set M : Matrix (Fin 2) (Fin 2) (ZMod 5) := (g : Matrix (Fin 2) (Fin 2) (ZMod 5)) with hMdef
  have hR : M * M + M + 1 = 0 := gl25_order_three_charpoly g h3 h1
  obtain ⟨hq, hA, hB⟩ := rel_entries hR
  have hM2 : M * M = -M - 1 := by
    calc M * M = (M * M + M + 1) - M - 1 := by abel
      _ = -M - 1 := by rw [hR]; abel
  have hdetN : ((2 : ZMod 5) • (1 : Matrix (Fin 2) (Fin 2) (ZMod 5)) + M).det = 3 := by
    rw [Matrix.det_fin_two]
    simp
    linear_combination 2 * hA + hB
  have hunit : IsUnit ((2 : ZMod 5) • (1 : Matrix (Fin 2) (Fin 2) (ZMod 5)) + M) := by
    rw [Matrix.isUnit_iff_isUnit_det, hdetN]
    exact isUnit_iff_ne_zero.2 (by decide : (3 : ZMod 5) ≠ 0)
  let c0 : GL25 := hunit.unit
  have hc0 : (c0 : Matrix (Fin 2) (Fin 2) (ZMod 5)) =
      (2 : ZMod 5) • (1 : Matrix (Fin 2) (Fin 2) (ZMod 5)) + M :=
    hunit.unit_spec
  have hcomm : c0 ∈ Subgroup.centralizer ({g} : Set GL25) := by
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff.1 hh]
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, hc0]
    show M * ((2 : ZMod 5) • (1 : Matrix (Fin 2) (Fin 2) (ZMod 5)) + M) =
      ((2 : ZMod 5) • (1 : Matrix (Fin 2) (Fin 2) (ZMod 5)) + M) * M
    simp [mul_add, add_mul]
  rw [isCyclic_iff_exists_zpowers_eq_top]
  refine ⟨⟨c0, hcomm⟩, ?_⟩
  rw [eq_top_iff]
  rintro y -
  have hyc : g * (y : GL25) = (y : GL25) * g :=
    Subgroup.mem_centralizer_iff.1 y.2 g (Set.mem_singleton g)
  have hmat : ((y : GL25) : Matrix (Fin 2) (Fin 2) (ZMod 5)) * M = M * ((y : GL25) : Matrix (Fin 2) (Fin 2) (ZMod 5)) := by
    have h := congrArg Units.val hyc
    rw [Units.val_mul, Units.val_mul] at h
    exact h.symm
  obtain ⟨a, b, hab⟩ := commutant_form hq hmat
  have hnz : ¬ (a = 0 ∧ b = 0) := by
    rintro ⟨rfl, rfl⟩
    apply Units.ne_zero (y : GL25)
    rw [hab]
    simp
  obtain ⟨k, -, hk⟩ := pwF_surj a b hnz
  refine Subgroup.mem_zpowers_iff.2 ⟨k, ?_⟩
  apply Subtype.ext
  rw [zpow_natCast, Subgroup.coe_pow]
  show c0 ^ k = (y : GL25)
  apply Units.ext
  rw [Units.val_pow_eq_pow_val, hc0, pwF_spec hM2 k, hk, hab]

def SL25 : Subgroup GL25 := (Matrix.GeneralLinearGroup.det : GL25 →* (ZMod 5)ˣ).ker

theorem mem_SL25 {g : GL25} : g ∈ SL25 ↔ Matrix.GeneralLinearGroup.det g = 1 :=
  MonoidHom.mem_ker

theorem card_SL25 : Nat.card SL25 = 120 := by
  have hidx : SL25.index = 4 := by
    rw [SL25, Subgroup.index_ker,
      MonoidHom.range_eq_top.2 (Matrix.GeneralLinearGroup.det_surjective (n := Fin 2) (R := ZMod 5)),
      Subgroup.card_top, Nat.card_eq_fintype_card, ZMod.card_units]
  have h := Subgroup.card_mul_index SL25
  rw [hidx, CFSG.Quasithin.SBc16.card_GL25] at h
  omega

private def iG : GL25 := Units.mk (!![2, 0; 0, 3] : Matrix (Fin 2) (Fin 2) (ZMod 5)) !![3, 0; 0, 2]
  (by decide) (by decide)

private def jG : GL25 := Units.mk (!![0, 1; 4, 0] : Matrix (Fin 2) (Fin 2) (ZMod 5)) !![0, 4; 1, 0]
  (by decide) (by decide)

private def qFun : QuaternionGroup 2 → GL25
  | .a i => iG ^ i.val
  | .xa i => jG * iG ^ i.val

private theorem qFun_mul : ∀ x y : QuaternionGroup 2, qFun (x * y) = qFun x * qFun y := by decide

private theorem qFun_one : qFun 1 = 1 := by decide

private theorem qFun_inj : ∀ x y : QuaternionGroup 2, qFun x = qFun y → x = y := by decide

private theorem qFun_det : ∀ x : QuaternionGroup 2, Matrix.GeneralLinearGroup.det (qFun x) = 1 := by decide

private def qHom : QuaternionGroup 2 →* GL25 where
  toFun := qFun
  map_one' := qFun_one
  map_mul' := qFun_mul

private def Q0 : Subgroup GL25 := qHom.range

private theorem Q0_le_SL25 : Q0 ≤ SL25 := by
  rintro _ ⟨x, rfl⟩
  exact mem_SL25.2 (qFun_det x)

private theorem card_Q0 : Nat.card Q0 = 8 := by
  have hinj : Function.Injective qHom := fun x y h => qFun_inj x y h
  have e := MonoidHom.ofInjective hinj
  rw [Q0, ← Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card]

private theorem sq_eq_one_mat : ∀ M : Matrix (Fin 2) (Fin 2) (ZMod 5),
    M.det = 1 → M * M = 1 → M = 1 ∨ M = -1 := by
  decide +kernel

private theorem sq_eq_one_SL {x : GL25} (hx : x ∈ SL25) (h2 : x * x = 1) : x = 1 ∨ x = -1 := by
  have h1 := congrArg Units.val (mem_SL25.1 hx)
  rw [Matrix.GeneralLinearGroup.val_det_apply, Units.val_one] at h1
  have hM : (x : Matrix (Fin 2) (Fin 2) (ZMod 5)) * (x : Matrix (Fin 2) (Fin 2) (ZMod 5)) = 1 := by
    rw [← Units.val_mul, h2, Units.val_one]
  rcases sq_eq_one_mat _ h1 hM with h | h
  · exact Or.inl (Units.ext (by rw [h, Units.val_one]))
  · exact Or.inr (Units.ext h)

private theorem cyclic_of_card_four {T : Subgroup GL25} (hT : T ≤ SL25) (hcard : Nat.card T = 4) :
    IsCyclic T := by
  have hex : ∃ x ∈ T, x * x ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have hsub : (T : Set GL25) ⊆ ({1, -1} : Set GL25) := by
      intro x hx
      rcases sq_eq_one_SL (hT hx) (hcon x hx) with h | h
      · exact Or.inl h
      · exact Or.inr h
    have h2 : (T : Set GL25).ncard ≤ 2 := by
      refine (Set.ncard_le_ncard hsub (Set.toFinite _)).trans ?_
      refine (Set.ncard_insert_le _ _).trans ?_
      rw [Set.ncard_singleton]
    have hc : Nat.card (T : Set GL25) = 4 := hcard
    rw [Nat.card_coe_set_eq] at hc
    omega
  obtain ⟨x, hxT, hx2⟩ := hex
  let x' : T := ⟨x, hxT⟩
  have hx2' : x' * x' ≠ 1 := fun h => hx2 (congrArg Subtype.val h)
  have hx4 : x' ^ 4 = 1 := by
    have := pow_card_eq_one' (x := x')
    rwa [hcard] at this
  have hdvd : orderOf x' ∣ 2 ^ 2 := by
    rw [← orderOf_dvd_iff_pow_eq_one] at hx4
    simpa using hx4
  obtain ⟨m, hm, hmeq⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
  have hord : orderOf x' = 4 := by
    interval_cases m
    · have h1 : x' = 1 := orderOf_eq_one_iff.1 (by simpa using hmeq)
      exact absurd (by rw [h1, one_mul]) hx2'
    · have h2' : x' ^ 2 = 1 := orderOf_dvd_iff_pow_eq_one.1 (by rw [hmeq]; norm_num)
      exact absurd (by rw [← pow_two]; exact h2') hx2'
    · rw [hmeq]; norm_num
  have hcardZ : Nat.card (Subgroup.zpowers x') = Nat.card T := by
    rw [Nat.card_zpowers, hord, hcard]
  exact isCyclic_iff_exists_zpowers_eq_top.2 ⟨x', Subgroup.eq_top_of_card_eq _ hcardZ⟩

private abbrev M2 : Type := Matrix (Fin 2) (Fin 2) (ZMod 5)

private def iM : M2 := !![2, 0; 0, 3]

private def jM : M2 := !![0, 1; 4, 0]

private def kM : M2 := iM * jM

private def Q0M : List M2 := [1, -1, iM, -iM, jM, -jM, kM, -kM]

private def NormB (M : M2) : Bool :=
  decide (M 0 0 * M 1 1 - M 0 1 * M 1 0 ≠ 0) &&
  (Q0M.any fun w => decide (w * w = -1) && decide (M * iM = w * M)) &&
  (Q0M.any fun w => decide (w * w = -1) && decide (M * jM = w * M))

private def InQZB (M : M2) : Bool :=
  Q0M.any fun q => ([1, 2, 3, 4] : List (ZMod 5)).any fun a =>
    decide (M = q * Matrix.scalar (Fin 2) a)

private theorem finite_pow96 : ∀ M : M2, NormB M = true → M ^ 96 = 1 := by decide +kernel

private theorem finite_pow8 : ∀ M : M2, NormB M = true → M ^ 32 = 1 → M ^ 8 = 1 := by decide +kernel

private theorem finite_core : ∀ g : M2, NormB g = true → g ^ 3 = 1 → g ≠ 1 →
    ∀ t : M2, NormB t = true → t ^ 8 = 1 → (t * (g * t * g ^ 2)) ^ 8 = 1 → InQZB t = true := by
  decide +kernel

private theorem Q0M_mem : ∀ x : QuaternionGroup 2, ((qFun x : GL25) : M2) ∈ Q0M := by decide

private theorem Q0M_surj : ∀ q ∈ Q0M, ∃ x : QuaternionGroup 2, ((qFun x : GL25) : M2) = q := by
  decide +kernel

private theorem scalar_ne_zero_of_mem : ∀ a ∈ ([1, 2, 3, 4] : List (ZMod 5)), a ≠ 0 := by decide

private theorem Q0M_of_mem {w : GL25} (hw : w ∈ Q0) : (w : M2) ∈ Q0M := by
  obtain ⟨y, rfl⟩ := hw
  exact Q0M_mem y

private theorem qHom_a_one : qHom (QuaternionGroup.a 1) = iG := by decide

private theorem qHom_xa_zero : qHom (QuaternionGroup.xa 0) = jG := by decide

private theorem iG_mul_iG : iG * iG = -1 := by decide

private theorem qHom_a_one_sq : qHom (QuaternionGroup.a 1) * qHom (QuaternionGroup.a 1) = -1 := by
  rw [qHom_a_one]; exact iG_mul_iG

private theorem normB_of_normalizer {x : GL25} (hx : x ∈ Subgroup.normalizer (Q0 : Set GL25)) :
    NormB (x : M2) = true := by
  have hfwd : ∀ q ∈ Q0, x * q * x⁻¹ ∈ Q0 := fun q hq => (Subgroup.mem_normalizer_iff.1 hx q).1 hq
  have hdet : (x : M2) 0 0 * (x : M2) 1 1 - (x : M2) 0 1 * (x : M2) 1 0 ≠ 0 := by
    rw [← Matrix.det_fin_two]
    exact ((Matrix.isUnit_iff_isUnit_det _).1 x.isUnit).ne_zero
  have hA1 : qHom (QuaternionGroup.a 1) ∈ Q0 := ⟨_, rfl⟩
  have hB0 : qHom (QuaternionGroup.xa 0) ∈ Q0 := ⟨_, rfl⟩
  have hw1 : x * qHom (QuaternionGroup.a 1) * x⁻¹ ∈ Q0 := hfwd _ hA1
  have hw2 : x * qHom (QuaternionGroup.xa 0) * x⁻¹ ∈ Q0 := hfwd _ hB0
  have sq1 : x * qHom (QuaternionGroup.a 1) * x⁻¹ * (x * qHom (QuaternionGroup.a 1) * x⁻¹) = -1 := by
    have e : x * qHom (QuaternionGroup.a 1) * x⁻¹ * (x * qHom (QuaternionGroup.a 1) * x⁻¹) =
        x * (qHom (QuaternionGroup.a 1) * qHom (QuaternionGroup.a 1)) * x⁻¹ := by group
    rw [e, qHom_a_one_sq, mul_neg_one, neg_mul, mul_inv_cancel]
  have sq2 : x * qHom (QuaternionGroup.xa 0) * x⁻¹ * (x * qHom (QuaternionGroup.xa 0) * x⁻¹) = -1 := by
    have hB0sq : qHom (QuaternionGroup.xa 0) * qHom (QuaternionGroup.xa 0) = -1 := by decide
    have e : x * qHom (QuaternionGroup.xa 0) * x⁻¹ * (x * qHom (QuaternionGroup.xa 0) * x⁻¹) =
        x * (qHom (QuaternionGroup.xa 0) * qHom (QuaternionGroup.xa 0)) * x⁻¹ := by group
    rw [e, hB0sq, mul_neg_one, neg_mul, mul_inv_cancel]
  have c1 : x * qHom (QuaternionGroup.a 1) = (x * qHom (QuaternionGroup.a 1) * x⁻¹) * x := by group
  have c2 : x * qHom (QuaternionGroup.xa 0) = (x * qHom (QuaternionGroup.xa 0) * x⁻¹) * x := by group
  have c1M : (x : M2) * iM = ((x * qHom (QuaternionGroup.a 1) * x⁻¹ : GL25) : M2) * (x : M2) := by
    have := congrArg Units.val c1
    rw [Units.val_mul, Units.val_mul, qHom_a_one] at this
    exact this
  have c2M : (x : M2) * jM = ((x * qHom (QuaternionGroup.xa 0) * x⁻¹ : GL25) : M2) * (x : M2) := by
    have := congrArg Units.val c2
    rw [Units.val_mul, Units.val_mul, qHom_xa_zero] at this
    exact this
  have sq1M : ((x * qHom (QuaternionGroup.a 1) * x⁻¹ : GL25) : M2) *
      ((x * qHom (QuaternionGroup.a 1) * x⁻¹ : GL25) : M2) = -1 := by
    rw [← Units.val_mul, sq1]; rfl
  have sq2M : ((x * qHom (QuaternionGroup.xa 0) * x⁻¹ : GL25) : M2) *
      ((x * qHom (QuaternionGroup.xa 0) * x⁻¹ : GL25) : M2) = -1 := by
    rw [← Units.val_mul, sq2]; rfl
  simp only [NormB, Bool.and_eq_true, List.any_eq_true, decide_eq_true_eq]
  exact ⟨⟨hdet, _, Q0M_of_mem hw1, sq1M, c1M⟩, _, Q0M_of_mem hw2, sq2M, c2M⟩

private theorem pow96_of_normalizer {x : GL25} (hx : x ∈ Subgroup.normalizer (Q0 : Set GL25)) :
    x ^ 96 = 1 := by
  apply Units.ext
  rw [Units.val_pow_eq_pow_val, Units.val_one]
  exact finite_pow96 _ (normB_of_normalizer hx)

private theorem pow32_of_two_pow {x : GL25} (hx : x ∈ Subgroup.normalizer (Q0 : Set GL25)) {k : ℕ}
    (hk : x ^ 2 ^ k = 1) : x ^ 32 = 1 := by
  have h96 := pow96_of_normalizer hx
  have h1 : orderOf x ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk
  have h2 : orderOf x ∣ 96 := orderOf_dvd_of_pow_eq_one h96
  obtain ⟨j, hj, hjeq⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 h1
  have hj5 : j ≤ 5 := by
    by_contra hcon
    have h6 : 2 ^ 6 ∣ 2 ^ j := pow_dvd_pow 2 (by omega)
    rw [← hjeq] at h6
    have := h6.trans h2
    norm_num at this
  have h32 : orderOf x ∣ 32 := by
    rw [hjeq]
    exact (pow_dvd_pow 2 hj5).trans (by norm_num)
  exact orderOf_dvd_iff_pow_eq_one.1 h32

private theorem pow8_of_two_pow {x : GL25} (hx : x ∈ Subgroup.normalizer (Q0 : Set GL25)) {k : ℕ}
    (hk : x ^ 2 ^ k = 1) : x ^ 8 = 1 := by
  apply Units.ext
  rw [Units.val_pow_eq_pow_val, Units.val_one]
  apply finite_pow8 _ (normB_of_normalizer hx)
  have := congrArg Units.val (pow32_of_two_pow hx hk)
  rwa [Units.val_pow_eq_pow_val, Units.val_one] at this

private theorem exists_two_pow_of_mem {T : Subgroup GL25} (hT : IsPGroup 2 T) {t : GL25} (ht : t ∈ T) :
    ∃ k : ℕ, t ^ 2 ^ k = 1 := by
  obtain ⟨k, hk⟩ := hT ⟨t, ht⟩
  exact ⟨k, by simpa using congrArg Subtype.val hk⟩

private theorem core_elem {t g : GL25} (hg3 : g ^ 3 = 1) (hg1 : g ≠ 1)
    (hgN : g ∈ Subgroup.normalizer (Q0 : Set GL25)) (htN : t ∈ Subgroup.normalizer (Q0 : Set GL25))
    (ht : ∃ k : ℕ, t ^ 2 ^ k = 1) (hu : ∃ k : ℕ, (t * (g * t * g⁻¹)) ^ 2 ^ k = 1) :
    ∃ q ∈ Q0, ∃ a : (ZMod 5)ˣ, (t : M2) = (q : M2) * Matrix.scalar (Fin 2) (a : ZMod 5) := by
  have hginv : g⁻¹ = g ^ 2 := inv_eq_of_mul_eq_one_right (by rw [← pow_succ']; exact hg3)
  have huN : t * (g * t * g⁻¹) ∈ Subgroup.normalizer (Q0 : Set GL25) :=
    mul_mem htN (mul_mem (mul_mem hgN htN) (inv_mem hgN))
  obtain ⟨k, hk⟩ := ht
  obtain ⟨l, hl⟩ := hu
  have ht8 : t ^ 8 = 1 := pow8_of_two_pow htN hk
  have hu8 : (t * (g * t * g⁻¹)) ^ 8 = 1 := pow8_of_two_pow huN hl
  have hM := finite_core (g : M2) (normB_of_normalizer hgN)
    (by have := congrArg Units.val hg3; rwa [Units.val_pow_eq_pow_val, Units.val_one] at this)
    (fun h => hg1 (Units.ext h))
    (t : M2) (normB_of_normalizer htN)
    (by have := congrArg Units.val ht8; rwa [Units.val_pow_eq_pow_val, Units.val_one] at this)
    (by
      have := congrArg Units.val hu8
      rw [Units.val_pow_eq_pow_val, Units.val_one, hginv] at this
      simpa [Units.val_mul, Matrix.mul_assoc] using this)
  unfold InQZB at hM
  simp only [List.any_eq_true, decide_eq_true_eq] at hM
  obtain ⟨q, hqL, a, haL, hEq⟩ := hM
  obtain ⟨y, hy⟩ := Q0M_surj q hqL
  have ha0 : a ≠ 0 := scalar_ne_zero_of_mem a haL
  refine ⟨qFun y, ⟨y, rfl⟩, Units.mk0 a ha0, ?_⟩
  rw [Units.val_mk0, hy, hEq]

private theorem SL25_conj_mem {x t : GL25} (hx : x ∈ SL25) : t * x * t⁻¹ ∈ SL25 := by
  rw [mem_SL25] at hx ⊢
  simp [hx]

private theorem sylow2_of_card_eight (H : Subgroup SL25) (hc : Nat.card H = 8) :
    IsPGroup 2 H ∧ ∀ {K : Subgroup SL25}, IsPGroup 2 K → H ≤ K → H = K := by
  refine ⟨IsPGroup.of_card (p := 2) (n := 3) (by rw [hc]; norm_num), fun {K} hK hHK => ?_⟩
  obtain ⟨b, hb⟩ := hK.exists_card_eq
  have hdvd : Nat.card K ∣ 120 := by
    rw [← card_SL25]; exact Subgroup.card_subgroup_dvd_card K
  have hHK' : Nat.card H ∣ Nat.card K := Subgroup.card_dvd_of_le hHK
  rw [hb] at hdvd
  rw [hb, hc] at hHK'
  have hb3 : b = 3 := by
    have hb7 : b < 7 := by
      by_contra hcon
      have h1 : 2 ^ 7 ≤ 2 ^ b := Nat.pow_le_pow_right (by norm_num) (by omega)
      have h2 : 2 ^ b ≤ 120 := Nat.le_of_dvd (by norm_num) hdvd
      omega
    interval_cases b <;> revert hdvd hHK' <;> norm_num
  subst hb3
  apply Subgroup.eq_of_le_of_card_ge hHK
  rw [hb, hc]; norm_num

private def sylowEight (H : Subgroup SL25) (hc : Nat.card H = 8) : Sylow 2 ↥SL25 where
  toSubgroup := H
  isPGroup' := (sylow2_of_card_eight H hc).1
  is_maximal' := by
    intro K hK hHK
    exact ((sylow2_of_card_eight H hc).2 hK hHK).symm

private theorem exists_conj_eight {Q : Subgroup GL25} (hQ : Q ≤ SL25) (hc : Nat.card Q = 8) :
    ∃ h ∈ SL25, ∀ x ∈ SL25, x ∈ Q ↔ h⁻¹ * x * h ∈ Q0 := by
  have hc0 : Nat.card (Q0.subgroupOf SL25) = 8 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe Q0_le_SL25).toEquiv, card_Q0]
  have hcQ : Nat.card (Q.subgroupOf SL25) = 8 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQ).toEquiv, hc]
  obtain ⟨m, hm⟩ := MulAction.exists_smul_eq ↥SL25 (sylowEight (Q0.subgroupOf SL25) hc0)
    (sylowEight (Q.subgroupOf SL25) hcQ)
  have hsub : MulAut.conj m • (Q0.subgroupOf SL25) = Q.subgroupOf SL25 := by
    have h2 := congrArg Sylow.toSubgroup hm
    rw [Sylow.coe_subgroup_smul] at h2
    exact h2
  have hmem : ∀ y : ↥SL25, y ∈ Q.subgroupOf SL25 ↔ m⁻¹ * y * m ∈ Q0.subgroupOf SL25 := by
    intro y
    rw [← hsub, Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
    simp [MulAut.smul_def, MulAut.conj_inv_apply]
  refine ⟨(m : GL25), m.2, fun x hx => ?_⟩
  have hy := hmem ⟨x, hx⟩
  simpa [Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv] using hy

private theorem conj_normalizer_of {Q : Subgroup GL25} (hQ : Q ≤ SL25) {h : GL25} (hhSL : h ∈ SL25)
    (hiff : ∀ x ∈ SL25, x ∈ Q ↔ h⁻¹ * x * h ∈ Q0) {t : GL25}
    (ht : t ∈ Subgroup.normalizer (Q : Set GL25)) :
    h⁻¹ * t * h ∈ Subgroup.normalizer (Q0 : Set GL25) := by
  rw [Subgroup.mem_normalizer_iff]
  intro q
  have ht' := Subgroup.mem_normalizer_iff.1 ht
  by_cases hq : q ∈ SL25
  · have hy : h * q * h⁻¹ ∈ SL25 := SL25.mul_mem (SL25.mul_mem hhSL hq) (SL25.inv_mem hhSL)
    have e1 := hiff (h * q * h⁻¹) hy
    rw [show h⁻¹ * (h * q * h⁻¹) * h = q by group] at e1
    have e2 := hiff (t * (h * q * h⁻¹) * t⁻¹) (SL25_conj_mem hy)
    rw [show h⁻¹ * (t * (h * q * h⁻¹) * t⁻¹) * h = (h⁻¹ * t * h) * q * (h⁻¹ * t * h)⁻¹ by group]
      at e2
    exact e1.symm.trans ((ht' (h * q * h⁻¹)).trans e2)
  · have hq0 : q ∉ Q0 := fun hq0 => hq (Q0_le_SL25 hq0)
    have hconj : (h⁻¹ * t * h) * q * (h⁻¹ * t * h)⁻¹ ∉ Q0 := by
      intro hc0
      apply hq
      have h1 : (h⁻¹ * t * h) * q * (h⁻¹ * t * h)⁻¹ ∈ SL25 := Q0_le_SL25 hc0
      rw [mem_SL25] at h1 ⊢
      simpa using h1
    exact ⟨fun h1 => absurd h1 hq0, fun h1 => absurd h1 hconj⟩

private theorem comm_of_isCyclic {Q : Subgroup GL25} (hcyc : IsCyclic Q) (hQ2 : IsPGroup 2 Q) {g : GL25}
    (hg3 : g ^ 3 = 1) (hgQ : g ∈ Subgroup.normalizer (Q : Set GL25)) :
    ∀ q ∈ Q, g * q * g⁻¹ = q := by
  obtain ⟨c, hc⟩ := IsCyclic.exists_generator (α := ↥Q)
  have hpow : ∀ q ∈ Q, ∃ n : ℤ, (c : GL25) ^ n = q := by
    intro q hq
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 (hc ⟨q, hq⟩)
    exact ⟨n, by simpa using congrArg Subtype.val hn⟩
  have hc' : (c : GL25) ∈ Q := c.2
  obtain ⟨k, hk⟩ := hpow _ ((Subgroup.mem_normalizer_iff.1 hgQ _).1 hc')
  have hconj : ∀ n : ℤ, g * (c : GL25) ^ n * g⁻¹ = (c : GL25) ^ (k * n) := by
    intro n
    rw [← conj_zpow, ← hk, ← zpow_mul]
  have hk3 : (c : GL25) ^ (k * k * k) = c := by
    have e1 : g * (g * (c : GL25) * g⁻¹) * g⁻¹ = (c : GL25) ^ (k * k) := by
      rw [← hk]; exact hconj k
    have e2 : g * (g * (g * (c : GL25) * g⁻¹) * g⁻¹) * g⁻¹ = (c : GL25) ^ (k * k * k) := by
      rw [e1, hconj (k * k), show k * (k * k) = k * k * k by ring]
    have e3 : g * (g * (g * (c : GL25) * g⁻¹) * g⁻¹) * g⁻¹ = (c : GL25) := by
      have hgg : g * g * g = 1 := (pow_three' g).symm.trans hg3
      have : g * (g * (g * (c : GL25) * g⁻¹) * g⁻¹) * g⁻¹ = (g * g * g) * c * (g * g * g)⁻¹ := by
        group
      rw [this, hgg, one_mul, inv_one, mul_one]
    exact e2.symm.trans e3
  have hk31 : (c : GL25) ^ (k * k * k - 1) = 1 := by
    rw [zpow_sub, hk3, zpow_one, mul_inv_cancel]
  have hzp : Subgroup.zpowers (c : GL25) = Q := by
    apply le_antisymm
    · exact Subgroup.zpowers_le.2 hc'
    · intro q hq
      obtain ⟨n, hn⟩ := hpow q hq
      exact Subgroup.mem_zpowers_iff.2 ⟨n, hn⟩
  have hord : orderOf (c : GL25) = Nat.card Q := by
    rw [← Nat.card_zpowers, hzp]
  obtain ⟨n2, hn2⟩ := hQ2.exists_card_eq
  have hordZ : (orderOf (c : GL25) : ℤ) = 2 ^ n2 := by
    rw [hord, hn2]; push_cast; rfl
  have hdvd : (orderOf (c : GL25) : ℤ) ∣ k * k * k - 1 := orderOf_dvd_iff_zpow_eq_one.2 hk31
  have hodd : IsCoprime (2 : ℤ) (k * k + k + 1) := by
    obtain ⟨w, hw⟩ := Int.even_mul_succ_self k
    exact ⟨-w, 1, by linear_combination hw⟩
  have hcop2 : IsCoprime ((2 : ℤ) ^ n2) (k * k + k + 1) := hodd.pow_left
  have hmul : (2 : ℤ) ^ n2 ∣ (k - 1) * (k * k + k + 1) := by
    have e : (k - 1) * (k * k + k + 1) = k * k * k - 1 := by ring
    rw [e, ← hordZ]; exact hdvd
  have hk1 : (2 : ℤ) ^ n2 ∣ k - 1 := hcop2.dvd_of_dvd_mul_right hmul
  have hk1' : (c : GL25) ^ (k - 1) = 1 := by
    apply orderOf_dvd_iff_zpow_eq_one.1
    rw [hordZ]; exact hk1
  have hck : (c : GL25) ^ k = c := by
    have e : k = (k - 1) + 1 := by ring
    rw [e, zpow_add, hk1', one_mul, zpow_one]
  intro q hq
  obtain ⟨n, rfl⟩ := hpow q hq
  rw [hconj n, zpow_mul, hck]

private theorem isPGroup_of_le' {T Q : Subgroup GL25} (hT : IsPGroup 2 T) (hQ : Q ≤ T) :
    IsPGroup 2 Q := by
  intro x
  obtain ⟨k, hk⟩ := hT ⟨x.1, hQ x.2⟩
  exact ⟨k, Subtype.ext (by simpa using congrArg Subtype.val hk)⟩

private theorem conj_pow_eq {h t : GL25} (n : ℕ) : (h⁻¹ * t * h) ^ n = h⁻¹ * t ^ n * h := by
  have := conj_pow (a := h⁻¹) (b := t) (i := n)
  rwa [inv_inv] at this

private theorem mul_scalar_mid (A B C S : M2) (hS : S * C = C * S) :
    A * (B * S) * C = A * B * C * S := by
  simp only [mul_assoc, hS]

theorem gl25_isCyclic_or_quaternion {T : Subgroup GL25} (hT : IsPGroup 2 T)
    (hdet : ∀ t ∈ T, t.det = 1) : IsCyclic T ∨ Nonempty (↥T ≃* QuaternionGroup 2) := by
  have hle : T ≤ SL25 := fun t ht => mem_SL25.2 (hdet t ht)
  obtain ⟨a, ha⟩ := hT.exists_card_eq
  have hdvd : 2 ^ a ∣ 120 := by
    rw [← ha, ← card_SL25]; exact Subgroup.card_dvd_of_le hle
  have ha7 : a < 7 := by
    by_contra hcon
    have h1 : 2 ^ 7 ≤ 2 ^ a := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h2 : 2 ^ a ≤ 120 := Nat.le_of_dvd (by norm_num) hdvd
    omega
  interval_cases a
  · left
    have h1 : Nat.card T = 1 := by simpa using ha
    haveI : Subsingleton T := (Nat.card_eq_one_iff_unique.1 h1).1
    infer_instance
  · left
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact isCyclic_of_prime_card (p := 2) (by simpa using ha)
  · left
    exact cyclic_of_card_four hle (by simpa using ha)
  · right
    have h8 : Nat.card T = 8 := by simpa using ha
    obtain ⟨h, hhSL, hiff⟩ := exists_conj_eight hle h8
    have hxSL : ∀ x : QuaternionGroup 2, h * qFun x * h⁻¹ ∈ SL25 := fun x =>
      SL25.mul_mem (SL25.mul_mem hhSL (Q0_le_SL25 ⟨x, rfl⟩)) (SL25.inv_mem hhSL)
    have hψmem : ∀ x : QuaternionGroup 2, h * qFun x * h⁻¹ ∈ T := fun x => by
      rw [hiff _ (hxSL x), show h⁻¹ * (h * qFun x * h⁻¹) * h = qFun x by group]
      exact ⟨x, rfl⟩
    let ψ : QuaternionGroup 2 →* ↥T :=
      { toFun := fun x => ⟨h * qFun x * h⁻¹, hψmem x⟩
        map_one' := by ext; simp [qFun_one]
        map_mul' := fun x y => by ext; simp [qFun_mul, mul_assoc] }
    have hinj : Function.Injective ψ := by
      intro x y hxy
      have h1 : h * qFun x * h⁻¹ = h * qFun y * h⁻¹ := congrArg Subtype.val hxy
      have h2 : qFun x = qFun y := by simpa using h1
      exact qFun_inj x y h2
    have hsurj : Function.Surjective ψ := by
      rintro ⟨t, ht⟩
      obtain ⟨x, hx⟩ := (hiff t (hle ht)).1 ht
      refine ⟨x, Subtype.ext ?_⟩
      show h * qFun x * h⁻¹ = t
      have hx' : qFun x = h⁻¹ * t * h := hx
      rw [hx']
      group
    exact ⟨(MulEquiv.ofBijective ψ ⟨hinj, hsurj⟩).symm⟩
  all_goals (norm_num at hdvd)

theorem gl25_two_subgroup_normalized {T : Subgroup GL25} (hT : IsPGroup 2 T) {g : GL25}
    (hg : orderOf g = 3) (hgT : g ∈ Subgroup.normalizer (T : Set GL25))
    (hnc : ¬ ∀ t ∈ T, g * t * g⁻¹ = t) :
    ∃ Q ≤ T, Nonempty (↥Q ≃* QuaternionGroup 2) ∧ ⁅T, Subgroup.zpowers g⁆ = Q ∧
      ∀ t ∈ T, ∃ q ∈ Q, ∃ a : (ZMod 5)ˣ,
        (t : Matrix (Fin 2) (Fin 2) (ZMod 5)) =
          (q : Matrix (Fin 2) (Fin 2) (ZMod 5)) * Matrix.scalar (Fin 2) (a : ZMod 5) := by
  have hg3 : g ^ 3 = 1 := by rw [← hg]; exact pow_orderOf_eq_one g
  have hg1 : g ≠ 1 := by
    intro h1; rw [h1, orderOf_one] at hg; omega
  have hXT : Subgroup.zpowers g ≤ Subgroup.normalizer (T : Set GL25) := Subgroup.zpowers_le.2 hgT
  obtain ⟨Q, hQ⟩ : ∃ Q : Subgroup GL25, Q = ⁅T, Subgroup.zpowers g⁆ := ⟨_, rfl⟩
  rw [← hQ]
  have hQT : Q ≤ T := by
    rw [hQ]
    refine Subgroup.commutator_le.2 fun a ha b hb => ?_
    have hb' : b * a⁻¹ * b⁻¹ ∈ T :=
      (Subgroup.mem_normalizer_iff.1 (hXT hb) a⁻¹).1 (T.inv_mem ha)
    rw [commutatorElement_def]
    simpa [mul_assoc] using T.mul_mem ha hb'
  have hQSL : Q ≤ SL25 := by
    rw [hQ]
    refine Subgroup.commutator_le.2 fun a _ b _ => ?_
    rw [mem_SL25, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact mul_comm _ _
  have hQ2 : IsPGroup 2 Q := isPGroup_of_le' hT hQT
  have hcardX : Nat.card (Subgroup.zpowers g) = 3 := by rw [Nat.card_zpowers, hg]
  obtain ⟨n, hn⟩ := hT.exists_card_eq
  have hcop : Nat.Coprime (Nat.card (Subgroup.zpowers g)) (Nat.card T) := by
    rw [hcardX, hn]; exact Nat.Coprime.pow_right _ (by norm_num)
  have hcomm : ⁅Q, Subgroup.zpowers g⁆ = Q := by
    have := coprime_commutator_commutator_eq' hXT hcop
    rw [← hQ] at this
    exact this
  have hQne : Q ≠ ⊥ := by
    intro hbot
    apply hnc
    intro t ht
    have hTc : T ≤ Subgroup.centralizer (Subgroup.zpowers g : Set GL25) := by
      rw [hQ] at hbot
      exact Subgroup.commutator_eq_bot_iff_le_centralizer.1 hbot
    have hgt := Subgroup.mem_centralizer_iff.1 (hTc ht) g (Subgroup.mem_zpowers g)
    rw [hgt, mul_assoc, mul_inv_cancel, mul_one]
  have hgQ : g ∈ Subgroup.normalizer (Q : Set GL25) := by
    rw [hQ]; exact le_normalizer_commutator_right' T _ (Subgroup.mem_zpowers g)
  have hcyc : ¬ IsCyclic Q := by
    intro hcycQ
    have hcent := comm_of_isCyclic hcycQ hQ2 hg3 hgQ
    have hbot : ⁅Q, Subgroup.zpowers g⁆ = ⊥ := by
      rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
      intro q hq
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
      have hgq : Commute g q := (mul_inv_eq_iff_eq_mul).1 (hcent q hq)
      exact hgq.zpow_left m
    exact hQne (hcomm.symm.trans hbot)
  have hdetQ : ∀ t ∈ Q, t.det = 1 := fun t ht => mem_SL25.1 (hQSL ht)
  have hQ8 : Nonempty (↥Q ≃* QuaternionGroup 2) :=
    (gl25_isCyclic_or_quaternion hQ2 hdetQ).resolve_left hcyc
  obtain ⟨φ⟩ := hQ8
  have hcardQ : Nat.card Q = 8 := by
    rw [Nat.card_congr φ.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card]
  obtain ⟨h, hhSL, hiff⟩ := exists_conj_eight hQSL hcardQ
  refine ⟨Q, hQT, ⟨φ⟩, rfl, ?_⟩
  intro t ht
  have htQ : t ∈ Subgroup.normalizer (Q : Set GL25) := by
    rw [hQ]; exact le_normalizer_commutator_left T _ ht
  have ht' := conj_normalizer_of hQSL hhSL hiff htQ
  have hg' := conj_normalizer_of hQSL hhSL hiff hgQ
  have hgpow : (h⁻¹ * g * h) ^ 3 = 1 := by
    rw [conj_pow_eq, hg3, mul_one, inv_mul_cancel]
  have hg1' : h⁻¹ * g * h ≠ 1 := by
    intro h1
    apply hg1
    have e : g = h * (h⁻¹ * g * h) * h⁻¹ := by group
    rw [e, h1]; group
  obtain ⟨k, hk⟩ := exists_two_pow_of_mem hT ht
  have huT : t * (g * t * g⁻¹) ∈ T :=
    T.mul_mem ht ((Subgroup.mem_normalizer_iff.1 hgT t).1 ht)
  obtain ⟨l, hl⟩ := exists_two_pow_of_mem hT huT
  have hkpow : ∃ m : ℕ, (h⁻¹ * t * h) ^ 2 ^ m = 1 :=
    ⟨k, by rw [conj_pow_eq, hk, mul_one, inv_mul_cancel]⟩
  have hue : (h⁻¹ * t * h) * ((h⁻¹ * g * h) * (h⁻¹ * t * h) * (h⁻¹ * g * h)⁻¹) =
      h⁻¹ * (t * (g * t * g⁻¹)) * h := by group
  have hupow : ∃ m : ℕ,
      ((h⁻¹ * t * h) * ((h⁻¹ * g * h) * (h⁻¹ * t * h) * (h⁻¹ * g * h)⁻¹)) ^ 2 ^ m = 1 :=
    ⟨l, by rw [hue, conj_pow_eq, hl, mul_one, inv_mul_cancel]⟩
  obtain ⟨q', hq'Q0, a, hEq⟩ := core_elem hgpow hg1' hg' ht' hkpow hupow
  have hq'SL : h * q' * h⁻¹ ∈ SL25 :=
    SL25.mul_mem (SL25.mul_mem hhSL (Q0_le_SL25 hq'Q0)) (SL25.inv_mem hhSL)
  refine ⟨h * q' * h⁻¹, ?_, a, ?_⟩
  · rw [hiff _ hq'SL, show h⁻¹ * (h * q' * h⁻¹) * h = q' by group]
    exact hq'Q0
  · have ht_eq : t = h * (h⁻¹ * t * h) * h⁻¹ := by group
    have e := congrArg Units.val ht_eq
    rw [Units.val_mul, Units.val_mul, hEq] at e
    rw [e, Units.val_mul, Units.val_mul]
    exact mul_scalar_mid _ _ _ _ (Matrix.scalar_commute _ (fun r => Commute.all _ _) _)

end CFSG.RankThree.PartTwo.Sec18.Item187Proof
