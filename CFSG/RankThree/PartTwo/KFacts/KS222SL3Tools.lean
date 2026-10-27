module

public import CFSG.RankThree.PartTwo.Sec21.Item22Statements
public import CFSG.RankThree.PartTwo.Sec4.LThreePiDiag
public import CFSG.RankThree.PartOne.KF.LayerCover
public import CFSG.RankThree.PartOne.KF.UnitaryTorus
import CFSG.RankThree.SubgroupLists.SL3Involutions
import CFSG.Timmesfeld.Orders.Distinct
import CFSG.RankThree.SteinbergR3ECALinearSplitBlocks
import CFSG.RankThree.PartOne.KF.R9Perm

public section

namespace CFSG.RankThree.PartTwo.Sec21.SL3Lines

open Matrix CFSG CFSG.RankThree CFSG.Assembly.LowTwoRank
open CFSG.RankThree.PartTwo.Sec4 (PiField ModThree piCard slPi glPi diagUnits coe_diagUnits
  diagE coe_diagE blockHom blockHom_injective centralizer_diagE_eq mem_slPi_true mem_slPi_iff
  mem_glPi_true entry_eq_zero_of_commute_diagonal commute_of_mem_statedScalars)
open CFSG.RankThree.PartOne.KFU (permGL permGL_conj_diagU diagU diagU_val)

theorem exists_elemAbelian_two_SL3 (F : Type) [Field F] [Finite F] [CharP F 2] :
    ∃ E : Subgroup (SpecialLinearGroup (Fin 3) F), (∀ x ∈ E, x * x = 1) ∧
      Nat.card E = Nat.card F ^ 2 := by
  let m : F × F → Matrix (Fin 3) (Fin 3) F := fun v => !![1, 0, v.1; 0, 1, v.2; 0, 0, 1]
  have hm0 : m 0 = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [m]
  have hmm : ∀ v w : F × F, m (v + w) = m v * m w := by
    intro v w
    ext i j
    fin_cases i <;> fin_cases j <;> simp [m, Matrix.mul_apply, Fin.sum_univ_three, add_comm]
  have hdet : ∀ v : F × F, (m v).det = 1 := fun v => by simp [m, Matrix.det_fin_three]
  let ψ : Multiplicative (F × F) →* SpecialLinearGroup (Fin 3) F :=
    { toFun := fun v => ⟨m (Multiplicative.toAdd v), hdet _⟩
      map_one' := Subtype.ext (show m (Multiplicative.toAdd 1) = 1 by rw [toAdd_one, hm0])
      map_mul' := fun v w => Subtype.ext (show m (Multiplicative.toAdd (v * w)) =
        m (Multiplicative.toAdd v) * m (Multiplicative.toAdd w) by rw [toAdd_mul, hmm]) }
  have hψ : Function.Injective ψ := by
    intro v w h
    have h1 := congrArg
      (fun x : SpecialLinearGroup (Fin 3) F => (x : Matrix (Fin 3) (Fin 3) F) 0 2) h
    have h2 := congrArg
      (fun x : SpecialLinearGroup (Fin 3) F => (x : Matrix (Fin 3) (Fin 3) F) 1 2) h
    simp [ψ, m] at h1 h2
    exact Multiplicative.toAdd.injective (Prod.ext h1 h2)
  refine ⟨ψ.range, ?_, ?_⟩
  · rintro _ ⟨v, rfl⟩
    rw [← map_mul]
    have hv : v * v = 1 := by
      apply Multiplicative.toAdd.injective
      rw [toAdd_mul, toAdd_one]
      exact Prod.ext (CharTwo.add_self_eq_zero _) (CharTwo.add_self_eq_zero _)
    rw [hv, map_one]
  · rw [← Nat.card_congr (MonoidHom.ofInjective hψ).toEquiv]
    change Nat.card (F × F) = _
    rw [Nat.card_prod, sq]

theorem two_eq_zero_of_mulEquiv {n : ℕ} (hn : 2 ≤ n) {K : Type} [Field K]
    {Y : Subgroup (GL (Fin 3) K)} (hdet : ∀ x ∈ Y, (x : Matrix (Fin 3) (Fin 3) K).det = 1)
    (ε : SL3 n ≃* Y) : (2 : K) = 0 := by
  by_contra h2
  obtain ⟨E, hE2, hEc⟩ := exists_elemAbelian_two_SL3 (GaloisField 2 n)
  set φ : SL3 n →* GL (Fin 3) K := Y.subtype.comp ε.toMonoidHom with hφdef
  have hφ : Function.Injective φ := Y.subtype_injective.comp ε.injective
  have hle := CFSG.RankThree.SubgroupLists.card_le_four_of_sq_eq_one_sl3 h2 (E.map φ)
    (by
      rintro _ ⟨x, hx, rfl⟩
      rw [← map_mul, hE2 x hx, map_one])
    (by
      rintro _ ⟨x, -, rfl⟩
      exact hdet _ (ε x).2)
  rw [Subgroup.card_map_of_injective hφ, hEc, GaloisField.card 2 n (by omega)] at hle
  have h4 : 2 ^ 2 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have h16 : 4 ^ 2 ≤ (2 ^ n) ^ 2 := Nat.pow_le_pow_left (by simpa using h4) 2
  omega

theorem card_SL3_eq (n : ℕ) (hn : 0 < n) :
    Nat.card (SL3 n) = 2 ^ (n * 3) * (((2 ^ n) ^ 2 - 1) * ((2 ^ n) ^ 3 - 1)) := by
  rw [Nat.card_congr (specialLinearGroupEquivStatedSL 3 (GaloisField 2 n)).toEquiv,
    CFSG.SectionRank.OddCover.card_statedSL_three, GaloisField.card 2 n hn.ne', pow_mul,
    mul_assoc]

theorem odd_pow_sub_one_add_one {m a : ℕ} (hm : 1 ≤ m) (ha : 1 ≤ a) :
    Odd ((2 ^ m) ^ a - 1) ∧ Odd ((2 ^ m) ^ a + 1) := by
  have h : 2 ∣ (2 ^ m) ^ a := dvd_pow (dvd_pow_self 2 (by omega)) (by omega)
  have h1 : 1 ≤ (2 ^ m) ^ a := Nat.one_le_pow _ _ (by positivity)
  constructor <;> rw [Nat.odd_iff] <;> omega

theorem params_eq {n : ℕ} (hn : 0 < n) (he : Even n) {π : Bool} {p f : ℕ} {K : Type} [Field K]
    (hPi : PiField π p f K) (hmod : ModThree π (p ^ f)) (ε : SL3 n ≃* slPi π 3 (p ^ f) K) :
    p = 2 ∧ π = true ∧ f = n := by
  have := hPi.finite
  have hn2 : 2 ≤ n := by obtain ⟨k, hk⟩ := he; omega
  have hπ : π = false → CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData p f K :=
    fun h => by subst h; exact hPi.unitary
  have h2 : (2 : K) = 0 :=
    two_eq_zero_of_mulEquiv hn2 (fun x hx => ((mem_slPi_iff hπ).mp hx).2) ε
  have hchar : CharP K 2 := (CharP.charP_iff_prime_eq_zero Nat.prime_two).mpr (by exact_mod_cast h2)
  have hp2 : p = 2 := by
    have := Fintype.ofFinite K
    obtain ⟨m, -, hm⟩ := FiniteField.card K 2
    have hc := hPi.card
    rw [Nat.card_eq_fintype_card, hm] at hc
    have h2d : 2 ∣ piCard π (p ^ f) := by
      rw [← hc]
      exact dvd_pow_self 2 m.ne_zero
    have h2p : 2 ∣ p := by
      cases π
      · exact Nat.prime_two.dvd_of_dvd_pow (Nat.prime_two.dvd_of_dvd_pow h2d)
      · exact Nat.prime_two.dvd_of_dvd_pow h2d
    exact ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hPi.prime).mp h2p).symm
  subst hp2
  have hf1 := hPi.one_le
  have hL := card_SL3_eq n hn
  have hε := Nat.card_congr ε.toEquiv
  obtain ⟨o2, -⟩ := odd_pow_sub_one_add_one (m := n) (a := 2) (by omega) (by norm_num)
  obtain ⟨o3, -⟩ := odd_pow_sub_one_add_one (m := n) (a := 3) (by omega) (by norm_num)
  obtain ⟨o2', -⟩ := odd_pow_sub_one_add_one (m := f) (a := 2) hf1 (by norm_num)
  obtain ⟨o3', o3''⟩ := odd_pow_sub_one_add_one (m := f) (a := 3) hf1 (by norm_num)
  cases π
  ·
    exfalso
    have hK : Nat.card K = (2 ^ f) ^ 2 := hPi.card
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hc : Nat.card (slPi false 3 (2 ^ f) K) =
        (2 ^ f) ^ 3 * ((2 ^ f) ^ 2 - 1) * ((2 ^ f) ^ 3 + 1) :=
      CFSG.SectionRank.OddCover.card_statedSU_three hK
    rw [hL, hc] at hε
    have hε' : 2 ^ (n * 3) * (((2 ^ n) ^ 2 - 1) * ((2 ^ n) ^ 3 - 1)) =
        2 ^ (f * 3) * (((2 ^ f) ^ 2 - 1) * ((2 ^ f) ^ 3 + 1)) := by
      rw [hε, pow_mul, mul_assoc]
    have hnf := CFSG.Timmesfeld.Orders.eq_of_two_pow_mul_odd (o2.mul o3) (o2'.mul o3'') hε'
    have hfn : f = n := by omega
    subst hfn
    obtain ⟨k, hk⟩ := he
    have h3 : (2 : ℕ) ^ f % 3 = 1 := by
      rw [hk, ← two_mul, pow_mul, Nat.pow_mod]
      norm_num
    change (2 : ℕ) ^ f % 3 = 2 at hmod
    omega
  · refine ⟨rfl, rfl, ?_⟩
    have hK : Nat.card K = 2 ^ f := hPi.card
    have hc : Nat.card (slPi true 3 (2 ^ f) K) =
        Nat.card K ^ 3 * (Nat.card K ^ 2 - 1) * (Nat.card K ^ 3 - 1) :=
      CFSG.SectionRank.OddCover.card_statedSL_three
    rw [hK] at hc
    rw [hL, hc] at hε
    have hε' : 2 ^ (n * 3) * (((2 ^ n) ^ 2 - 1) * ((2 ^ n) ^ 3 - 1)) =
        2 ^ (f * 3) * (((2 ^ f) ^ 2 - 1) * ((2 ^ f) ^ 3 - 1)) := by
      rw [hε, pow_mul, mul_assoc]
    have hnf := CFSG.Timmesfeld.Orders.eq_of_two_pow_mul_odd (o2.mul o3) (o2'.mul o3') hε'
    omega

section Centralizers

variable {K : Type} [Field K]

theorem scalar_mul_comm (l : Kˣ) (M : GL (Fin 3) K) :
    GeneralLinearGroup.scalar (Fin 3) l * M = M * GeneralLinearGroup.scalar (Fin 3) l :=
  (commute_of_mem_statedScalars ⟨l, rfl⟩ M).symm

theorem det_conj (w M : GL (Fin 3) K) :
    ((w * M * w⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).det =
      (M : Matrix (Fin 3) (Fin 3) K).det := by
  rw [Units.val_mul, Units.val_mul, Matrix.det_mul, Matrix.det_mul, mul_comm, ← mul_assoc,
    ← Matrix.det_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.det_one, one_mul]

theorem inf_centralizer_conj (q : ℕ) (w z : GL (Fin 3) K) (l : Kˣ) :
    slPi true 3 q K ⊓ Subgroup.centralizer
        {w * (GeneralLinearGroup.scalar (Fin 3) l * z) * w⁻¹} =
      (slPi true 3 q K ⊓ Subgroup.centralizer {z}).map (MulAut.conj w).toMonoidHom := by
  set S := GeneralLinearGroup.scalar (Fin 3) l with hS
  have key : ∀ N : GL (Fin 3) K, N * (S * z) = (S * z) * N ↔ N * z = z * N := by
    intro N
    constructor
    · intro h
      apply mul_left_cancel (a := S)
      calc S * (N * z) = N * (S * z) := by rw [← mul_assoc, scalar_mul_comm, mul_assoc]
        _ = (S * z) * N := h
        _ = S * (z * N) := mul_assoc _ _ _
    · intro h
      calc N * (S * z) = S * (N * z) := by rw [← mul_assoc, ← scalar_mul_comm, mul_assoc]
        _ = S * (z * N) := by rw [h]
        _ = (S * z) * N := (mul_assoc _ _ _).symm
  ext M
  simp only [Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_map,
    mem_slPi_true, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  constructor
  · rintro ⟨hM, hMc⟩
    refine ⟨w⁻¹ * M * w, ⟨?_, ?_⟩, by group⟩
    · have := det_conj w⁻¹ M
      rw [inv_inv] at this
      rw [this, hM]
    · rw [← key]
      calc w⁻¹ * M * w * (S * z) = w⁻¹ * (M * (w * (S * z) * w⁻¹)) * w := by group
        _ = w⁻¹ * ((w * (S * z) * w⁻¹) * M) * w := by rw [hMc]
        _ = S * z * (w⁻¹ * M * w) := by group
  · rintro ⟨N, ⟨hN, hNc⟩, rfl⟩
    refine ⟨by rw [det_conj, hN], ?_⟩
    have h := (key N).mpr hNc
    calc w * N * w⁻¹ * (w * (S * z) * w⁻¹) = w * (N * (S * z)) * w⁻¹ := by group
      _ = w * ((S * z) * N) * w⁻¹ := by rw [h]
      _ = w * (S * z) * w⁻¹ * (w * N * w⁻¹) := by group

noncomputable def perfectResidualConjEquiv [Finite K] (w : GL (Fin 3) K)
    (X : Subgroup (GL (Fin 3) K)) :
    inSubgroup perfectResidual (X.map (MulAut.conj w).toMonoidHom) ≃*
      inSubgroup perfectResidual X :=
  (MulEquiv.subgroupCongr
    (GroupTheory.SteinbergBY.map_inSubgroup_perfectResidual_of_injective _
      (MulAut.conj w).injective X).symm).trans
    (Subgroup.equivMapOfInjective _ _ (MulAut.conj w).injective).symm

theorem diagUnits_eq_diagU (a b c : Kˣ) : diagUnits a b c = diagU ![a, b, c] := by
  apply Units.ext
  rw [coe_diagUnits, diagU_val]
  congr 1
  funext i
  fin_cases i <;> rfl

theorem perfectResidual_centralizer_diagE [Finite K] {n : ℕ} (hPi : PiField true 2 n K)
    (hK4 : 4 ≤ Nat.card K) {e : Kˣ} (he : e ≠ 1) :
    Nonempty (inSubgroup perfectResidual (slPi true 3 (2 ^ n) K ⊓
      Subgroup.centralizer {diagE e}) ≃* SpecialLinearGroup (Fin 2) K) := by
  rw [centralizer_diagE_eq hPi he]
  set C := (glPi true 2 (2 ^ n) K).map blockHom with hC
  set ι : SpecialLinearGroup (Fin 2) K →* GL (Fin 3) K :=
    blockHom.comp (SpecialLinearGroup.toGL : SpecialLinearGroup (Fin 2) K →* GL (Fin 2) K)
    with hι
  have hιinj : Function.Injective ι :=
    blockHom_injective.comp SpecialLinearGroup.toGL_injective
  set B := ι.range with hB
  have hBC : B ≤ C := by
    rintro _ ⟨A, rfl⟩
    exact ⟨_, mem_glPi_true _ _, rfl⟩
  have hq := CFSG.RankThree.CALinearPlane.isQuasisimple_SL_of_two_le (k := K) (m := 2) le_rfl hK4
  have hperf : Group.IsPerfect ↥B := by
    have := hq.1
    exact Group.IsPerfect.ofSurjective (f := (MonoidHom.ofInjective hιinj).toMonoidHom)
      (MonoidHom.ofInjective hιinj).surjective
  set eC := (glPi true 2 (2 ^ n) K).equivMapOfInjective blockHom blockHom_injective with heC
  set Φ : ↥C →* Kˣ := GeneralLinearGroup.det.comp
    ((glPi true 2 (2 ^ n) K).subtype.comp eC.symm.toMonoidHom) with hΦ
  have hker : Φ.ker = B.subgroupOf C := by
    ext c
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    constructor
    · intro h
      set B₀ := eC.symm c with hB₀
      have hdet : ((B₀ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).det = 1 := by
        rw [← GeneralLinearGroup.val_det_apply]
        exact congrArg Units.val h
      have hc : (c : GL (Fin 3) K) = blockHom (B₀ : GL (Fin 2) K) := by
        have := congrArg Subtype.val (eC.apply_symm_apply c)
        rw [← this]
        rfl
      refine ⟨⟨(B₀ : GL (Fin 2) K), hdet⟩, ?_⟩
      rw [hc]
      show blockHom (SpecialLinearGroup.toGL ⟨_, hdet⟩) = _
      congr 1
      exact Units.ext rfl
    · rintro ⟨A, hA⟩
      have hc : eC.symm c = ⟨SpecialLinearGroup.toGL A, mem_glPi_true _ _⟩ := by
        apply eC.injective
        rw [eC.apply_symm_apply]
        exact Subtype.ext hA.symm
      show GeneralLinearGroup.det ((eC.symm c : GL (Fin 2) K)) = 1
      rw [hc]
      apply Units.ext
      rw [GeneralLinearGroup.val_det_apply]
      exact A.2
  rw [CFSG.RankThree.PartOne.KFU.inSubgroup_perfectResidual_eq_of_ker hBC hperf Φ hker]
  exact ⟨(MonoidHom.ofInjective hιinj).symm⟩

theorem diagUnits_one_one_one : diagUnits (1 : Kˣ) 1 1 = 1 := by
  apply Units.ext
  rw [Units.val_one, coe_diagUnits, ← diagonal_one]
  congr 1
  funext i
  fin_cases i <;> simp

theorem eq_one_of_mul_self_eq_one [CharP K 2] {a : K} (h : a * a = 1) : a = 1 := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have h3 : (a - 1) ^ 2 = 0 := by linear_combination h - (a - 1) * h2
  exact sub_eq_zero.mp (pow_eq_zero_iff (by norm_num) |>.mp h3)

theorem perfectResidual_centralizer_of_conj [Finite K] [CharP K 2] {n : ℕ}
    (hPi : PiField true 2 n K) (hK4 : 4 ≤ Nat.card K) {y g : GL (Fin 3) K} {l s t : Kˣ}
    (hy : g⁻¹ * y * g = GeneralLinearGroup.scalar (Fin 3) l * diagUnits 1 s t)
    (hnc : ∃ M ∈ slPi true 3 (2 ^ n) K, M * y ≠ y * M)
    (hev : Even (Nat.card ↥(slPi true 3 (2 ^ n) K ⊓ Subgroup.centralizer {y}))) :
    Nonempty (inSubgroup perfectResidual (slPi true 3 (2 ^ n) K ⊓ Subgroup.centralizer {y}) ≃*
      SpecialLinearGroup (Fin 2) K) := by
  have hyg : y = g * (GeneralLinearGroup.scalar (Fin 3) l * diagUnits 1 s t) * g⁻¹ := by
    rw [← hy]
    group
  have hX : slPi true 3 (2 ^ n) K ⊓ Subgroup.centralizer {y} =
      (slPi true 3 (2 ^ n) K ⊓ Subgroup.centralizer {diagUnits 1 s t}).map
        (MulAut.conj g).toMonoidHom := by
    rw [hyg]
    exact inf_centralizer_conj _ g _ l
  have hst : ¬ (s = 1 ∧ t = 1) := by
    rintro ⟨rfl, rfl⟩
    obtain ⟨M, -, hM⟩ := hnc
    apply hM
    have hgS : g * GeneralLinearGroup.scalar (Fin 3) l * g⁻¹ =
        GeneralLinearGroup.scalar (Fin 3) l := by
      rw [← scalar_mul_comm, mul_assoc, mul_inv_cancel, mul_one]
    rw [hyg, diagUnits_one_one_one, mul_one, hgS, scalar_mul_comm]
  have hnd : ¬ (s ≠ 1 ∧ t ≠ 1 ∧ s ≠ t) := by
    rintro ⟨hs1, ht1, hst'⟩
    have h1s : (1 : K) ≠ (s : K) := fun h => hs1 (Units.ext h.symm)
    have h1t : (1 : K) ≠ (t : K) := fun h => ht1 (Units.ext h.symm)
    have hst2 : (s : K) ≠ (t : K) := fun h => hst' (Units.ext h)
    have hd : ∀ M ∈ slPi true 3 (2 ^ n) K ⊓ Subgroup.centralizer {diagUnits 1 s t},
        ∀ i j : Fin 3, i ≠ j → (M : Matrix (Fin 3) (Fin 3) K) i j = 0 := by
      intro M hM i j hij
      have hc := Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp hM).2
      have hc' := congrArg (fun x : GL (Fin 3) K => (x : Matrix (Fin 3) (Fin 3) K)) hc
      simp only [Units.val_mul, coe_diagUnits] at hc'
      apply entry_eq_zero_of_commute_diagonal hc'
      fin_cases i <;> fin_cases j <;> simp at hij ⊢ <;>
        first | exact h1s | exact h1s.symm | exact h1t | exact h1t.symm | exact hst2 |
          exact hst2.symm | exact hs1 | exact ht1
    have h2 : ¬ 2 ∣ Nat.card ↥(slPi true 3 (2 ^ n) K ⊓ Subgroup.centralizer {y}) := by
      rw [hX, Subgroup.card_map_of_injective (MulAut.conj g).injective]
      intro hdvd
      have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 2 hdvd
      have hxx : x * x = 1 := by
        have h := pow_orderOf_eq_one x
        rw [hx, sq] at h
        exact h
      have hxm := congrArg (fun z : ↥(slPi true 3 (2 ^ n) K ⊓
        Subgroup.centralizer {diagUnits 1 s t}) =>
          (((z : GL (Fin 3) K)) : Matrix (Fin 3) (Fin 3) K)) hxx
      simp only [Subgroup.coe_mul, Units.val_mul, Subgroup.coe_one, Units.val_one] at hxm
      have hz := hd x x.2
      have hd0 : ((x : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 0 0 = 1 := by
        apply eq_one_of_mul_self_eq_one
        have e := congrFun (congrFun hxm 0) 0
        rw [Matrix.mul_apply, Fin.sum_univ_three, Matrix.one_apply_eq, hz 0 1 (by decide),
          hz 0 2 (by decide)] at e
        simpa using e
      have hd1 : ((x : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 1 1 = 1 := by
        apply eq_one_of_mul_self_eq_one
        have e := congrFun (congrFun hxm 1) 1
        rw [Matrix.mul_apply, Fin.sum_univ_three, Matrix.one_apply_eq, hz 1 0 (by decide),
          hz 1 2 (by decide)] at e
        simpa using e
      have hd2 : ((x : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 2 2 = 1 := by
        apply eq_one_of_mul_self_eq_one
        have e := congrFun (congrFun hxm 2) 2
        rw [Matrix.mul_apply, Fin.sum_univ_three, Matrix.one_apply_eq, hz 2 0 (by decide),
          hz 2 1 (by decide)] at e
        simpa using e
      have hdiag : ∀ i, ((x : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) i i = 1 := by
        intro i
        fin_cases i
        exacts [hd0, hd1, hd2]
      have hx1 : x = 1 := by
        apply Subtype.ext
        apply Units.ext
        ext i j
        by_cases hij : i = j
        · subst hij
          rw [hdiag, Subgroup.coe_one, Units.val_one, Matrix.one_apply_eq]
        · rw [hz i j hij, Subgroup.coe_one, Units.val_one, Matrix.one_apply_ne hij]
      rw [hx1, orderOf_one] at hx
      norm_num at hx
    exact h2 (even_iff_two_dvd.mp hev)
  obtain ⟨w, l', e, he, hw⟩ : ∃ (w : GL (Fin 3) K) (l' e : Kˣ), e ≠ 1 ∧
      diagUnits 1 s t = w * (GeneralLinearGroup.scalar (Fin 3) l' * diagE e) * w⁻¹ := by
    by_cases hs1 : s = 1
    · subst hs1
      have ht1 : t ≠ 1 := fun h => hst ⟨rfl, h⟩
      refine ⟨permGL (Equiv.swap 0 2), 1, t, ht1, ?_⟩
      rw [map_one, one_mul, diagE, diagUnits_eq_diagU, diagUnits_eq_diagU, permGL_conj_diagU]
      congr 1
      funext i
      fin_cases i <;> rfl
    · by_cases ht1 : t = 1
      · subst ht1
        refine ⟨permGL (Equiv.swap 0 1), 1, s, hs1, ?_⟩
        rw [map_one, one_mul, diagE, diagUnits_eq_diagU, diagUnits_eq_diagU, permGL_conj_diagU]
        congr 1
        funext i
        fin_cases i <;> rfl
      · have hst2 : s = t := by
          by_contra h
          exact hnd ⟨hs1, ht1, h⟩
        subst hst2
        refine ⟨1, s, s⁻¹, inv_ne_one.mpr hs1, ?_⟩
        rw [one_mul, inv_one, mul_one]
        apply Units.ext
        rw [Units.val_mul, GeneralLinearGroup.coe_scalar, coe_diagE, coe_diagUnits,
          Matrix.scalar_apply, diagonal_mul_diagonal]
        congr 1
        funext i
        fin_cases i <;> simp
  have hX' : slPi true 3 (2 ^ n) K ⊓ Subgroup.centralizer {diagUnits 1 s t} =
      (slPi true 3 (2 ^ n) K ⊓ Subgroup.centralizer {diagE e}).map
        (MulAut.conj w).toMonoidHom := by
    rw [hw]
    exact inf_centralizer_conj _ w _ l'
  obtain ⟨e₀⟩ := perfectResidual_centralizer_diagE hPi hK4 he
  rw [hX, hX']
  exact ⟨(perfectResidualConjEquiv g _).trans ((perfectResidualConjEquiv w _).trans e₀)⟩

end Centralizers

end CFSG.RankThree.PartTwo.Sec21.SL3Lines
