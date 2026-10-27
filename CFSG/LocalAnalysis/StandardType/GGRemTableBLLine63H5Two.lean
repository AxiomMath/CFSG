module

public import CFSG.LocalAnalysis.StandardType.GGRemTableBLLine63H5Lift
public import CFSG.LocalAnalysis.StandardType.GGRemTableBLLine63H5Torus
public import CFSG.LocalAnalysis.StandardType.GGRemTableBLLine63H5StepOne
public import CFSG.LocalAnalysis.StandardType.GGRemTableBLLine63H5Inner
public import CFSG.LocalAnalysis.StandardType.GGTableBUnitaryEndNodeThree
public import CFSG.LocalAnalysis.StandardType.GGTableBUnitaryDvdCodimOne

public section

namespace CFSG.StandardType.Line63.H5

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.SectionRank.OddCover
  CFSG.RankThree.Classical2 CFSG.RankThree.Classical CFSG.RankThree.PartOne.KCUnitaryModel
  CFSG.StandardType.TableBU CFSG.Assembly

variable {K : Type} [Field K] {n : ℕ}

theorem diagHom_mem_normalizer (hKd : UnitaryFieldData 2 n K) {t : Fin 6 → Kˣ}
    (ht : ∀ i, (t i : K) ^ (2 ^ n + 1) = 1) :
    (diagHom 6 t : GL (Fin 6) K) ∈
      Subgroup.normalizer (unitarySU 2 n K 6 : Set (GL (Fin 6) K)) := by
  have hP : (diagHom 6 t : GL (Fin 6) K) ∈ primeFormUnitary hKd (idGram K 6) := by
    rw [mem_primeFormUnitary]
    simp only [idGram, Units.val_one, Matrix.mul_one]
    exact diagHom_unitary hKd ht
  exact TableBUE.gu_subset_normalizer (d := 6) hKd
    (TableBUD.mem_guSet_of_mem_primeFormUnitary hKd hP)

@[expose] def gen4 (ζ : Kˣ) : Fin 4 → Fin 6 → Kˣ :=
  ![![ζ, ζ, 1, 1, 1, 1], ![1, 1, ζ, 1, 1, 1], ![1, 1, 1, ζ, 1, 1], ![1, 1, 1, 1, ζ, 1]]

theorem exists_twoLocal_four_of_range [Finite K] {H : Type} [Group H] [Finite H]
    (hKd : UnitaryFieldData 2 n K) (hpq : 3 ∣ 2 ^ n + 1)
    (π : H →* MulAut (LargeEvenProj (unitarySU 2 n K 6))) (hN : IsPGroup 2 π.ker)
    (hrange : ∀ M : ↥(Subgroup.normalizer (unitarySU 2 n K 6 : Set (GL (Fin 6) K))),
      (∃ t : Fin 6 → Kˣ, (M : GL (Fin 6) K) = diagHom 6 t ∧ t 0 = t 1 ∧ ∀ i, t i ^ 3 = 1) →
        TableB.projConj (unitarySU 2 n K 6) M ∈ π.range)
    (hw : TableB.projConj (unitarySU 2 n K 6)
        ⟨(swapSU hKd : GL (Fin 6) K), Subgroup.le_normalizer (swapSU hKd).2⟩ ∈ π.range) :
    ∃ U E : Subgroup H, U ≠ ⊥ ∧ IsPGroup 2 U ∧ E ≤ Subgroup.normalizer (U : Set H) ∧
      CFSG.Open.IsElemAbelian 3 E ∧ Nat.card E = 3 ^ 4 := by
  classical
  have := Fact.mk Nat.prime_three
  have : NeZero 3 := ⟨by norm_num⟩
  have hn : 1 ≤ n := hKd.one_le
  have hKc : Nat.card K = (2 ^ n) ^ 2 := by rw [hKd.card, ← pow_mul, mul_comm]
  have hdq : ((6 : ℕ), 2 ^ n) ≠ (3, 2) := fun he => by
    have := congrArg Prod.fst he
    simp only at this
    omega
  obtain ⟨ζ, hζo, hζq⟩ := exists_orderOf_eq_norm_one hKd Nat.prime_three hpq
  have hζ3 : ζ ^ 3 = 1 := hζo ▸ pow_orderOf_eq_one ζ
  have hζ1 : ζ ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hζo
    omega
  set c := gen4 ζ with hc
  have hcp : ∀ j i, c j i ^ 3 = 1 := by
    intro j i
    fin_cases j <;> fin_cases i <;> simp [hc, gen4, hζ3]
  have hcnorm : ∀ j i, c j i ^ (2 ^ n + 1) = 1 := by
    intro j i
    fin_cases j <;> fin_cases i <;> simp [hc, gen4, hζq]
  have hpriv : ∀ j, ∃ i, (∀ j', j' ≠ j → c j' i = 1) ∧ orderOf (c j i) = 3 := by
    intro j
    fin_cases j
    · exact ⟨0, fun j' hj' => by fin_cases j' <;> simp_all [hc, gen4], by simp [hc, gen4, hζo]⟩
    · exact ⟨2, fun j' hj' => by fin_cases j' <;> simp_all [hc, gen4], by simp [hc, gen4, hζo]⟩
    · exact ⟨3, fun j' hj' => by fin_cases j' <;> simp_all [hc, gen4], by simp [hc, gen4, hζo]⟩
    · exact ⟨4, fun j' hj' => by fin_cases j' <;> simp_all [hc, gen4], by simp [hc, gen4, hζo]⟩
  have hexpinj := expHom_injective c hcp hpriv
  have hmem : ∀ a, (diagHom 6 (expHom c hcp a) : GL (Fin 6) K) ∈
      Subgroup.normalizer (unitarySU 2 n K 6 : Set (GL (Fin 6) K)) := by
    intro a
    refine diagHom_mem_normalizer hKd fun i => ?_
    rw [← Units.val_pow_eq_pow_val, expHom_apply, ← Finset.prod_pow]
    simp_rw [← pow_mul, mul_comm _ (2 ^ n + 1), pow_mul, hcnorm, one_pow, Finset.prod_const_one,
      Units.val_one]
  set ψ : Multiplicative (Fin 4 → ZMod 3) →*
      ↥(Subgroup.normalizer (unitarySU 2 n K 6 : Set (GL (Fin 6) K))) :=
    ((diagHom 6).comp (expHom c hcp)).codRestrict _ hmem with hψ
  set χ := (TableB.projConj (unitarySU 2 n K 6)).comp ψ with hχ
  have hapow : ∀ a : Multiplicative (Fin 4 → ZMod 3), a ^ 3 = 1 := by
    intro a
    rw [← toAdd_eq_zero, toAdd_pow]
    funext i
    have h3 : (3 : ZMod 3) = 0 := by exact_mod_cast ZMod.natCast_self 3
    simp [Pi.smul_apply, nsmul_eq_mul, h3]
  have hψ5 : ∀ a, expHom c hcp a 5 = 1 := by
    intro a
    rw [expHom_apply]
    exact Finset.prod_eq_one fun j _ => by
      have h1 : c j 5 = 1 := by fin_cases j <;> simp [hc, gen4]
      rw [h1, one_pow]
  have hχinj : Function.Injective χ := by
    rw [injective_iff_map_eq_one]
    intro a ha
    have hsc := TableBUE.mem_scalars_of_projConj_eq_one hKd hKc (by norm_num) hdq
      Nat.prime_three hpq (M := ψ a) ha
    rw [largeEvenScalars_def] at hsc
    obtain ⟨z, hz⟩ := hsc
    have key : ((ψ a : ↥(Subgroup.normalizer (unitarySU 2 n K 6 : Set (GL (Fin 6) K)))) :
        GL (Fin 6) K) = diagHom 6 (expHom c hcp a) := rfl
    rw [key] at hz
    have hz5 := congrFun (congrFun (congrArg (fun g : GL (Fin 6) K =>
      (g : Matrix (Fin 6) (Fin 6) K)) hz) 5) 5
    simp only [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.diagonal_apply_eq,
      coe_diagHom, hψ5 a, Units.val_one] at hz5
    have hz1 : z = 1 := Units.ext hz5
    rw [hz1, map_one] at hz
    have h1 : expHom c hcp a = 1 := diagHom_injective 6 (by rw [← hz, map_one])
    exact hexpinj (by rw [h1, map_one])
  have hE₀ab : CFSG.Open.IsElemAbelian 3 χ.range :=
    isElemAbelian_range (fun a b => mul_comm a b) hapow χ
  have hE₀card : Nat.card χ.range = 3 ^ 4 := by
    rw [Nat.card_congr (MonoidHom.ofInjective hχinj).toEquiv.symm,
      Nat.card_congr Multiplicative.toAdd, Nat.card_fun, Nat.card_zmod, Nat.card_eq_fintype_card,
      Fintype.card_fin]
  set w : ↥(unitarySU 2 n K 6) := swapSU hKd with hw'
  set cw := TableB.projConj (unitarySU 2 n K 6)
    ⟨(w : GL (Fin 6) K), Subgroup.le_normalizer w.2⟩ with hcw
  have hcw2 : cw ^ 2 = 1 := by
    rw [hcw, ← map_pow]
    have : (⟨(w : GL (Fin 6) K), Subgroup.le_normalizer w.2⟩ :
        ↥(Subgroup.normalizer (unitarySU 2 n K 6 : Set (GL (Fin 6) K)))) ^ 2 = 1 :=
      Subtype.ext (by
        have h2 := congrArg Subtype.val (swapSU_sq hKd)
        simpa using h2)
    rw [this, map_one]
  have hcw1 : cw ≠ 1 := by
    intro h1
    have hsc := TableBUE.mem_scalars_of_projConj_eq_one hKd hKc (by norm_num) hdq
      Nat.prime_three hpq (M := ⟨(w : GL (Fin 6) K), Subgroup.le_normalizer w.2⟩) h1
    rw [largeEvenScalars_def, ← Matrix.GeneralLinearGroup.center_eq_range_scalar] at hsc
    exact permGL_swap_not_mem_center (K := K) (d := 6) (i := 0) (j := 1)
      (by simp [Fin.ext_iff]) hζ1 hsc
  set U₀ := Subgroup.zpowers cw with hU₀def
  have hU₀ : IsPGroup 2 U₀ := by
    refine IsPGroup.of_card_dvd_pow (n := 1) ?_
    rw [hU₀def, Nat.card_zpowers]
    exact orderOf_dvd_of_pow_eq_one (by simpa using hcw2)
  have hU₀r : U₀ ≤ π.range := (Subgroup.zpowers_le).mpr hw
  have hU₀1 : U₀ ≠ ⊥ := by
    rw [hU₀def, Ne, Subgroup.zpowers_eq_bot]
    exact hcw1
  have hE₀r : χ.range ≤ π.range := by
    rintro _ ⟨a, rfl⟩
    refine hrange (ψ a) ⟨expHom c hcp a, rfl, ?_, ?_⟩
    · have h01 : ∀ j, c j 0 = c j 1 := by
        intro j
        fin_cases j <;> simp [hc, gen4]
      rw [expHom_apply, expHom_apply]
      exact Finset.prod_congr rfl fun j _ => by rw [h01 j]
    · intro i
      have h1 : expHom c hcp a ^ 3 = 1 := by rw [← map_pow, hapow, map_one]
      exact congrFun h1 i
  have hEU : χ.range ≤ Subgroup.normalizer (U₀ : Set (MulAut (LargeEvenProj
      (unitarySU 2 n K 6)))) := by
    rintro _ ⟨a, rfl⟩
    have h01 : expHom c hcp a 0 = expHom c hcp a 1 := by
      have h01 : ∀ j, c j 0 = c j 1 := by
        intro j
        fin_cases j <;> simp [hc, gen4]
      rw [expHom_apply, expHom_apply]
      exact Finset.prod_congr rfl fun j _ => by rw [h01 j]
    have hcomm : Commute (ψ a) (⟨(w : GL (Fin 6) K), Subgroup.le_normalizer w.2⟩ :
        ↥(Subgroup.normalizer (unitarySU 2 n K 6 : Set (GL (Fin 6) K)))) := by
      apply Subtype.ext
      show (diagHom 6 (expHom c hcp a) : GL (Fin 6) K) * permGL (Equiv.swap (0 : Fin 6) 1) =
        permGL (Equiv.swap (0 : Fin 6) 1) * diagHom 6 (expHom c hcp a)
      exact (swap_commute_diagHom h01).eq.symm
    have hcomm' : Commute (χ a) cw := hcomm.map (TableB.projConj (unitarySU 2 n K 6))
    refine Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr fun h hh => ?_)
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hh
    exact (Commute.zpow_left hcomm'.symm k).eq
  obtain ⟨U, E, hU, hU2, hEU', hE, hcard⟩ :=
    exists_lift_of_ker_two π hN hE₀ab hE₀r hU₀ hU₀r hU₀1 hEU
  exact ⟨U, E, hU, hU2, hEU', hE, hcard.trans hE₀card⟩

theorem succ_le_twoLocalRank_of_outside {G : Type} [Group G] [Finite G] {H : Subgroup G} {x : G}
    (hx3 : x ^ 3 = 1) (hx1 : x ≠ 1) (hxH : x ∉ H) (hxC : ∀ h ∈ H, x * h = h * x)
    {U E : Subgroup H} (hU : U ≠ ⊥) (hU2 : IsPGroup 2 U) (hEU : E ≤ Subgroup.normalizer (U : Set H))
    (hE : CFSG.Open.IsElemAbelian 3 E) {r : ℕ} (hr : Nat.card E = 3 ^ r) :
    r + 1 ≤ LargeEvenTwoLocalRank 3 G := by
  classical
  have hxcomm : ∀ g ∈ H, g * x = x * g := fun g hg => (hxC g hg).symm
  set E' : Subgroup G := E.map H.subtype with hE'
  set U' : Subgroup G := U.map H.subtype with hU'
  have hE'ab : CFSG.Open.IsElemAbelian 3 E' := CFSG.StandardType.TableB.isElemAbelian_map hE _
  have hE'H : E' ≤ H := Subgroup.map_subtype_le E
  have hX : CFSG.Open.IsElemAbelian 3 (Subgroup.zpowers x) := isElemAbelian_zpowers hx3
  have hcomm : ∀ a ∈ E', ∀ b ∈ Subgroup.zpowers x, a * b = b * a := by
    intro a ha b hb
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
    exact (Commute.zpow_right (show Commute a x from hxcomm a (hE'H ha)) k).eq
  have hdisj : Disjoint E' (Subgroup.zpowers x) := by
    rw [Subgroup.disjoint_def]
    intro y hy hyx
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hyx
    have hyord : orderOf x = 3 := orderOf_eq_prime hx3 hx1
    have hmod : x ^ (k % 3) = x ^ k := by
      have := zpow_mod_orderOf x k
      rwa [hyord, Nat.cast_ofNat] at this
    rw [← hmod] at hy ⊢
    have hk : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 := by omega
    rcases hk with hk | hk | hk
    · rw [hk]
      simp
    · rw [hk] at hy
      exact absurd (hE'H (by simpa using hy)) hxH
    · rw [hk] at hy
      have hx' : x ^ 2 ∈ E' := by simpa using hy
      have h4 : x ^ 4 = x := by rw [show 4 = 3 + 1 by rfl, pow_succ, hx3, one_mul]
      have h2 : (x ^ 2) ^ 2 = x := by rw [← pow_mul]; exact h4
      exact absurd (hE'H (h2 ▸ E'.pow_mem hx' 2)) hxH
  have hXN : Subgroup.zpowers x ≤ Subgroup.normalizer (E' : Set G) := by
    intro b hb
    refine Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr fun g hg => ?_)
    exact hcomm g hg b hb
  have hxord : Nat.card (Subgroup.zpowers x) = 3 := by
    rw [Nat.card_zpowers, orderOf_eq_prime hx3 hx1]
  have hcard : Nat.card (E' ⊔ Subgroup.zpowers x : Subgroup G) = 3 ^ (r + 1) := by
    rw [CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer _ _ hXN hdisj,
      ← Nat.card_congr (E.equivMapOfInjective _ H.subtype_injective).toEquiv, hr, hxord,
      pow_succ]
  have hUne : U' ≠ ⊥ := by
    rw [hU', Ne, Subgroup.map_eq_bot_iff_of_injective _ H.subtype_injective]
    exact hU
  have hTL : IsTwoLocal (Subgroup.normalizer (U' : Set G)) := ⟨U', hUne, hU2.map _, rfl⟩
  have hle : E' ⊔ Subgroup.zpowers x ≤ Subgroup.normalizer (U' : Set G) := by
    refine sup_le ((Subgroup.map_mono hEU).trans (Subgroup.le_normalizer_map _)) ?_
    intro y hy
    refine Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr fun g hg => ?_)
    obtain ⟨u, -, rfl⟩ := hg
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    exact ((Commute.zpow_right (show Commute (u : G) x from hxcomm u u.2) k)).eq
  have h := CFSG.StandardType.TableB.card_le_of_twoLocal Nat.prime_three hTL hle
    (CFSG.StandardType.TableB.isElemAbelian_sup hE'ab hX hcomm)
  rw [hcard] at h
  exact (Nat.pow_le_pow_iff_right (by norm_num)).mp h

theorem diagHom_mem_primeFormUnitary (hKd : UnitaryFieldData 2 n K) {t : Fin 6 → Kˣ}
    (ht : ∀ i, (t i : K) ^ (2 ^ n + 1) = 1) :
    (diagHom 6 t : GL (Fin 6) K) ∈ primeFormUnitary hKd (idGram K 6) := by
  rw [mem_primeFormUnitary]
  simp only [idGram, Units.val_one, Matrix.mul_one]
  exact diagHom_unitary hKd ht

theorem five_le_twoLocalRank_of_range [Finite K] {G : Type} [Group G] [Finite G] {H : Subgroup G}
    {x : G} (hKd : UnitaryFieldData 2 n K) (hpq : 3 ∣ 2 ^ n + 1) (hx3 : x ^ 3 = 1) (hx1 : x ≠ 1)
    (hxH : x ∉ H) (hxC : ∀ h ∈ H, x * h = h * x)
    (π : ↥H →* MulAut (LargeEvenProj (unitarySU 2 n K 6))) (hN : IsPGroup 2 π.ker)
    (hrange : ∀ M : ↥(Subgroup.normalizer (unitarySU 2 n K 6 : Set (GL (Fin 6) K))),
      (∃ t : Fin 6 → Kˣ, (M : GL (Fin 6) K) = diagHom 6 t ∧ t 0 = t 1 ∧ ∀ i, t i ^ 3 = 1) →
        TableB.projConj (unitarySU 2 n K 6) M ∈ π.range)
    (hw : TableB.projConj (unitarySU 2 n K 6)
        ⟨(swapSU hKd : GL (Fin 6) K), Subgroup.le_normalizer (swapSU hKd).2⟩ ∈ π.range) :
    5 ≤ LargeEvenTwoLocalRank 3 G := by
  obtain ⟨U, E, hU, hU2, hEU, hE, hcard⟩ := exists_twoLocal_four_of_range hKd hpq π hN hrange hw
  exact succ_le_twoLocalRank_of_outside hx3 hx1 hxH hxC hU hU2 hEU hE hcard

theorem det_not_mem_range_sixth [Finite K] (hKd : UnitaryFieldData 2 n K) (hpq : 3 ∣ 2 ^ n + 1)
    {U : GL (Fin 6) K} (hU : U ∈ primeFormUnitary hKd (idGram K 6)) (hn : ¬ IsInner n U) :
    GeneralLinearGroup.det U ∉ (powMonoidHom 6 : Kˣ →* Kˣ).range := by
  rintro ⟨t, ht⟩
  apply hn
  refine isInner_of_det_eq_pow_six hKd hpq hU (t := t) ?_
  rw [← Matrix.GeneralLinearGroup.val_det_apply, ← ht]
  simp

theorem projConj_mem_range_of_inner_outer [Finite K] {H : Type} [Group H]
    (hKd : UnitaryFieldData 2 n K) (hpq : 3 ∣ 2 ^ n + 1)
    (π : H →* MulAut (LargeEvenProj (unitarySU 2 n K 6)))
    (hinn : ∀ s : ↥(unitarySU 2 n K 6),
      TableB.projConj (unitarySU 2 n K 6) ⟨(s : GL (Fin 6) K), Subgroup.le_normalizer s.2⟩ ∈
        π.range)
    {g : GL (Fin 6) K} (hgU : g ∈ primeFormUnitary hKd (idGram K 6)) (hgn : ¬ IsInner n g)
    (hgr : TableB.projConj (unitarySU 2 n K 6)
      ⟨g, TableBUE.gu_subset_normalizer (d := 6) hKd
        (TableBUD.mem_guSet_of_mem_primeFormUnitary hKd hgU)⟩ ∈ π.range)
    (M : ↥(Subgroup.normalizer (unitarySU 2 n K 6 : Set (GL (Fin 6) K))))
    (hM : ∃ t : Fin 6 → Kˣ, (M : GL (Fin 6) K) = diagHom 6 t ∧ ∀ i, t i ^ 3 = 1) :
    TableB.projConj (unitarySU 2 n K 6) M ∈ π.range := by
  obtain ⟨t, hMt, ht3⟩ := hM
  have htn : ∀ i, (t i : K) ^ (2 ^ n + 1) = 1 := fun i => by
    rw [← Units.val_pow_eq_pow_val, pow_norm_eq_one_of_pow_three (ht3 i) hpq]
    simp
  have hMU : (M : GL (Fin 6) K) ∈ primeFormUnitary hKd (idGram K 6) := by
    rw [hMt]
    exact diagHom_mem_primeFormUnitary hKd htn
  have hgN : g ∈ Subgroup.normalizer (unitarySU 2 n K 6 : Set (GL (Fin 6) K)) :=
    TableBUE.gu_subset_normalizer (d := 6) hKd
      (TableBUD.mem_guSet_of_mem_primeFormUnitary hKd hgU)
  by_cases hMi : IsInner n (M : GL (Fin 6) K)
  · obtain ⟨u, s, hs⟩ := hMi
    have hu : GeneralLinearGroup.scalar (Fin 6) u ∈ LargeEvenScalars (Fin 6) K := ⟨u, rfl⟩
    have hM' : M = ⟨GeneralLinearGroup.scalar (Fin 6) u, TableB.scalar_mem_normalizer _ hu⟩ *
        ⟨(s : GL (Fin 6) K), Subgroup.le_normalizer s.2⟩ := Subtype.ext hs
    rw [hM', map_mul, TableB.projConj_of_scalar _ hu, one_mul]
    exact hinn s
  · obtain ⟨h3, h2⟩ := card_units_dvd_odd hKd hpq
    obtain ⟨ε, -, t', ht'⟩ := exists_pow_mul_mem_range_sixth h3 h2
      (u := GeneralLinearGroup.det g) (v := GeneralLinearGroup.det (M : GL (Fin 6) K))
      (det_not_mem_range_sixth hKd hpq hgU hgn) (det_not_mem_range_sixth hKd hpq hMU hMi)
    have hUε : (M : GL (Fin 6) K) * g ^ ε ∈ primeFormUnitary hKd (idGram K 6) :=
      Subgroup.mul_mem _ hMU (Subgroup.pow_mem _ hgU ε)
    have ht'' : t' ^ 6 = GeneralLinearGroup.det (M : GL (Fin 6) K) *
        GeneralLinearGroup.det g ^ ε := ht'
    have hdet : (((M : GL (Fin 6) K) * g ^ ε : GL (Fin 6) K) :
        Matrix (Fin 6) (Fin 6) K).det = (t' : K) ^ 6 := by
      rw [← Matrix.GeneralLinearGroup.val_det_apply, map_mul, map_pow, ← ht'',
        Units.val_pow_eq_pow_val]
    obtain ⟨u, s, hs⟩ := isInner_of_det_eq_pow_six hKd hpq hUε hdet
    have hu : GeneralLinearGroup.scalar (Fin 6) u ∈ LargeEvenScalars (Fin 6) K := ⟨u, rfl⟩
    have hNN : M * (⟨g, hgN⟩ : ↥(Subgroup.normalizer (unitarySU 2 n K 6 :
        Set (GL (Fin 6) K)))) ^ ε =
        ⟨GeneralLinearGroup.scalar (Fin 6) u, TableB.scalar_mem_normalizer _ hu⟩ *
        ⟨(s : GL (Fin 6) K), Subgroup.le_normalizer s.2⟩ := Subtype.ext (by simpa using hs)
    have h1 : TableB.projConj (unitarySU 2 n K 6) M *
        TableB.projConj (unitarySU 2 n K 6) ⟨g, hgN⟩ ^ ε =
        TableB.projConj (unitarySU 2 n K 6) ⟨(s : GL (Fin 6) K), Subgroup.le_normalizer s.2⟩ := by
      rw [← map_pow, ← map_mul, hNN, map_mul, TableB.projConj_of_scalar _ hu, one_mul]
    have h2' : TableB.projConj (unitarySU 2 n K 6) M =
        TableB.projConj (unitarySU 2 n K 6) ⟨(s : GL (Fin 6) K), Subgroup.le_normalizer s.2⟩ *
          (TableB.projConj (unitarySU 2 n K 6) ⟨g, hgN⟩ ^ ε)⁻¹ := eq_mul_inv_of_mul_eq h1
    rw [h2']
    exact Subgroup.mul_mem _ (hinn s) (Subgroup.inv_mem _ (Subgroup.pow_mem _ hgr ε))

theorem five_le_twoLocalRank_of_inner_outer [Finite K] {G : Type} [Group G] [Finite G]
    {H : Subgroup G} {x : G} (hKd : UnitaryFieldData 2 n K) (hpq : 3 ∣ 2 ^ n + 1)
    (hx3 : x ^ 3 = 1) (hx1 : x ≠ 1) (hxH : x ∉ H) (hxC : ∀ h ∈ H, x * h = h * x)
    (π : ↥H →* MulAut (LargeEvenProj (unitarySU 2 n K 6))) (hN : IsPGroup 2 π.ker)
    (hinn : ∀ s : ↥(unitarySU 2 n K 6),
      TableB.projConj (unitarySU 2 n K 6) ⟨(s : GL (Fin 6) K), Subgroup.le_normalizer s.2⟩ ∈
        π.range)
    {g : GL (Fin 6) K} (hgU : g ∈ primeFormUnitary hKd (idGram K 6)) (hgn : ¬ IsInner n g)
    (hgr : TableB.projConj (unitarySU 2 n K 6)
      ⟨g, TableBUE.gu_subset_normalizer (d := 6) hKd
        (TableBUD.mem_guSet_of_mem_primeFormUnitary hKd hgU)⟩ ∈ π.range) :
    5 ≤ LargeEvenTwoLocalRank 3 G :=
  five_le_twoLocalRank_of_range hKd hpq hx3 hx1 hxH hxC π hN
    (fun M ⟨t, hMt, _, ht3⟩ =>
      projConj_mem_range_of_inner_outer hKd hpq π hinn hgU hgn hgr M ⟨t, hMt, ht3⟩)
    (hinn (swapSU hKd))

end CFSG.StandardType.Line63.H5

end
