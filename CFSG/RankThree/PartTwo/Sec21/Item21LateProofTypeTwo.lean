module

public import CFSG.RankThree.PartTwo.Sec21.Item21LateProof2118
public import CFSG.RankThree.PartTwo.Sec6.Statements
import CFSG.RankThree.PartTwo.KFacts.KS222SL3Bar
import CFSG.RankThree.PartTwo.Sec6.Item612
import CFSG.RankThree.PartTwo.Sec6.Item68
import CFSG.RankThree.PartOne.KF.R9Perm
import CFSG.RankThree.SteinbergR3ECALinearSplitBlocks

public section

namespace CFSG.RankThree.PartTwo.Sec21.Item21LateProof

open Matrix CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly (IsElemAbelian)
open CFSG.Assembly.LowTwoRank (StatedScalars)
open CFSG.RankThree.PartTwo.Sec4 (blockHom coe_blockHom diagE coe_diagE diagUnits coe_diagUnits
  slPi glPi)
open CFSG.RankThree.PartOne.KFU (permGL permGL_conj_diagU diagU diagU_val)

section Matrices

variable {K : Type} [Field K]

theorem blockHom_zero_zero (B : GL (Fin 2) K) :
    ((blockHom B : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 0 0 =
      (((GeneralLinearGroup.det B)⁻¹ : Kˣ) : K) := by
  rw [coe_blockHom]
  rfl

theorem commutator_blockHom_range_le {M : GL (Fin 3) K}
    (hM : M ∈ ⁅(⊤ : Subgroup (GL (Fin 2) K)).map blockHom,
      (⊤ : Subgroup (GL (Fin 2) K)).map blockHom⁆) :
    (M : Matrix (Fin 3) (Fin 3) K) 0 0 = 1 := by
  rw [← Subgroup.map_commutator] at hM
  obtain ⟨B, hB, rfl⟩ := hM
  have hdet : GeneralLinearGroup.det B = 1 :=
    Abelianization.commutator_subset_ker (GeneralLinearGroup.det : GL (Fin 2) K →* Kˣ) hB
  rw [blockHom_zero_zero, hdet, inv_one, Units.val_one]

theorem blockHom_mem_commutator [Finite K] (hK4 : 4 ≤ Nat.card K) {B : GL (Fin 2) K}
    (hB : GeneralLinearGroup.det B = 1) :
    blockHom B ∈ ⁅(⊤ : Subgroup (GL (Fin 2) K)).map blockHom,
      (⊤ : Subgroup (GL (Fin 2) K)).map blockHom⁆ := by
  rw [← Subgroup.map_commutator]
  refine ⟨B, ?_, rfl⟩
  have hq := CALinearPlane.isQuasisimple_SL_of_two_le (k := K) (m := 2) le_rfl hK4
  have hperf : commutator (SpecialLinearGroup (Fin 2) K) = ⊤ := hq.1.commutator_eq_top
  have hB' : (B : Matrix (Fin 2) (Fin 2) K).det = 1 := by
    rw [← GeneralLinearGroup.val_det_apply, hB, Units.val_one]
  set S : SpecialLinearGroup (Fin 2) K := ⟨B, hB'⟩ with hS
  have hS1 : S ∈ commutator (SpecialLinearGroup (Fin 2) K) := by rw [hperf]; trivial
  have h1 : (SpecialLinearGroup.toGL : SpecialLinearGroup (Fin 2) K →* GL (Fin 2) K) S ∈
      (commutator (SpecialLinearGroup (Fin 2) K)).map SpecialLinearGroup.toGL := ⟨S, hS1, rfl⟩
  rw [commutator_def, Subgroup.map_commutator] at h1
  have h2 := Subgroup.commutator_mono le_top le_top h1
  have hSB : (SpecialLinearGroup.toGL : SpecialLinearGroup (Fin 2) K →* GL (Fin 2) K) S = B :=
    Units.ext rfl
  rw [hSB] at h2
  exact h2

theorem mem_commutator_map_conj_iff [Finite K] (hK4 : 4 ≤ Nat.card K) (w : GL (Fin 3) K)
    {M : GL (Fin 3) K}
    (hM : M ∈ ((⊤ : Subgroup (GL (Fin 2) K)).map blockHom).map (MulAut.conj w).toMonoidHom) :
    M ∈ ⁅((⊤ : Subgroup (GL (Fin 2) K)).map blockHom).map (MulAut.conj w).toMonoidHom,
        ((⊤ : Subgroup (GL (Fin 2) K)).map blockHom).map (MulAut.conj w).toMonoidHom⁆ ↔
      ((w⁻¹ * M * w : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 0 0 = 1 := by
  rw [← Subgroup.map_commutator, Subgroup.mem_map_equiv, MulAut.conj_symm_apply]
  rw [Subgroup.mem_map_equiv, MulAut.conj_symm_apply] at hM
  obtain ⟨B, -, hB⟩ := hM
  rw [← hB]
  constructor
  · exact commutator_blockHom_range_le
  · intro h
    apply blockHom_mem_commutator hK4
    rw [blockHom_zero_zero] at h
    have h' : (GeneralLinearGroup.det B)⁻¹ = 1 := Units.ext h
    exact inv_eq_one.mp h'

theorem exists_centralizer_eq_map_blockHom {n : ℕ} (hPi : Sec4.PiField true 2 n K)
    {y g : GL (Fin 3) K} {l s t : Kˣ}
    (hy : g⁻¹ * y * g = GeneralLinearGroup.scalar (Fin 3) l * diagUnits 1 s t)
    (hst : ¬ (s = 1 ∧ t = 1)) (hnd : ¬ (s ≠ 1 ∧ t ≠ 1 ∧ s ≠ t)) :
    ∃ w : GL (Fin 3) K, slPi true 3 (2 ^ n) K ⊓ Subgroup.centralizer {y} =
      ((⊤ : Subgroup (GL (Fin 2) K)).map blockHom).map (MulAut.conj w).toMonoidHom := by
  have hyg : y = g * (GeneralLinearGroup.scalar (Fin 3) l * diagUnits 1 s t) * g⁻¹ := by
    rw [← hy]
    group
  obtain ⟨w, l', e, he, hw⟩ : ∃ (w : GL (Fin 3) K) (l' e : Kˣ), e ≠ 1 ∧
      diagUnits 1 s t = w * (GeneralLinearGroup.scalar (Fin 3) l' * diagE e) * w⁻¹ := by
    by_cases hs1 : s = 1
    · subst hs1
      have ht1 : t ≠ 1 := fun h => hst ⟨rfl, h⟩
      refine ⟨permGL (Equiv.swap 0 2), 1, t, ht1, ?_⟩
      rw [map_one, one_mul, diagE, SL3Lines.diagUnits_eq_diagU, SL3Lines.diagUnits_eq_diagU,
        permGL_conj_diagU]
      congr 1
      funext i
      fin_cases i <;> rfl
    · by_cases ht1 : t = 1
      · subst ht1
        refine ⟨permGL (Equiv.swap 0 1), 1, s, hs1, ?_⟩
        rw [map_one, one_mul, diagE, SL3Lines.diagUnits_eq_diagU, SL3Lines.diagUnits_eq_diagU,
          permGL_conj_diagU]
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
  refine ⟨g * w, ?_⟩
  have hX : slPi true 3 (2 ^ n) K ⊓ Subgroup.centralizer {y} =
      (slPi true 3 (2 ^ n) K ⊓ Subgroup.centralizer {diagUnits 1 s t}).map
        (MulAut.conj g).toMonoidHom := by
    rw [hyg]
    exact SL3Lines.inf_centralizer_conj _ g _ l
  have hX' : slPi true 3 (2 ^ n) K ⊓ Subgroup.centralizer {diagUnits 1 s t} =
      (slPi true 3 (2 ^ n) K ⊓ Subgroup.centralizer {diagE e}).map
        (MulAut.conj w).toMonoidHom := by
    rw [hw]
    exact SL3Lines.inf_centralizer_conj _ w _ l'
  rw [hX, hX', Sec4.centralizer_diagE_eq hPi he, Subgroup.map_map, Subgroup.map_map,
    Subgroup.map_map]
  have hcomp : ((MulAut.conj g).toMonoidHom.comp (MulAut.conj w).toMonoidHom).comp blockHom =
      (MulAut.conj (g * w)).toMonoidHom.comp (blockHom (K := K)) := by
    ext B : 1
    simp only [MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom,
      MulAut.conj_apply]
    group
  rw [hcomp]
  rfl

theorem scalar_mul_diagUnits_pow (l s t : Kˣ) (k : ℕ) :
    (GeneralLinearGroup.scalar (Fin 3) l * diagUnits 1 s t) ^ k =
      GeneralLinearGroup.scalar (Fin 3) (l ^ k) * diagUnits 1 (s ^ k) (t ^ k) := by
  induction k with
  | zero => simp [SL3Lines.diagUnits_one_one_one]
  | succ k ih => rw [pow_succ, ih, Sec4.scalar_diagUnits_mul, pow_succ, pow_succ, pow_succ]

theorem scalar_apply_self (l : Kˣ) (i : Fin 3) :
    ((GeneralLinearGroup.scalar (Fin 3) l : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) i i = l := by
  rw [GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.diagonal_apply_eq]

theorem mul_scalar_apply (M : GL (Fin 3) K) (l : Kˣ) (i j : Fin 3) :
    ((M * GeneralLinearGroup.scalar (Fin 3) l : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) i j =
      (M : Matrix (Fin 3) (Fin 3) K) i j * l := by
  rw [Units.val_mul, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.mul_diagonal]

theorem conj_scalar (w : GL (Fin 3) K) (l : Kˣ) :
    w * GeneralLinearGroup.scalar (Fin 3) l * w⁻¹ = GeneralLinearGroup.scalar (Fin 3) l := by
  rw [← SL3Lines.scalar_mul_comm, mul_inv_cancel_right]

theorem distinct_of_conj_diag {M g : GL (Fin 3) K} {μ s t : Kˣ} (hs : s ^ 3 = 1)
    (ht : t ^ 3 = 1)
    (hM : g⁻¹ * M * g = GeneralLinearGroup.scalar (Fin 3) μ * diagUnits 1 s t)
    (hdet : (M : Matrix (Fin 3) (Fin 3) K).det = 1) (h3 : M ^ 3 = 1)
    (hns : ¬ (s = 1 ∧ t = 1)) : s ≠ 1 ∧ t ≠ 1 ∧ s ≠ t := by
  have hμ : (μ : K) ^ 3 = 1 := by
    have h1 : (g⁻¹ * M * g) ^ 3 = 1 := by
      have := conj_pow (a := g⁻¹) (b := M) (i := 3)
      rw [inv_inv] at this
      rw [this, h3, mul_one, inv_mul_cancel]
    rw [hM, scalar_mul_diagUnits_pow, hs, ht, SL3Lines.diagUnits_one_one_one, mul_one] at h1
    have h2 := congrArg (fun X : GL (Fin 3) K => (X : Matrix (Fin 3) (Fin 3) K) 0 0) h1
    simp only [scalar_apply_self, Units.val_one, Matrix.one_apply_eq] at h2
    rw [← Units.val_pow_eq_pow_val, h2]
  have hst : s * t = 1 := by
    have h1 : ((g⁻¹ * M * g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).det = 1 := by
      rw [Units.val_mul, Units.val_mul, Matrix.det_mul, Matrix.det_mul, hdet, mul_one,
        ← Matrix.det_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.det_one]
    rw [hM, Sec4.scalar_mul_diagUnits_eq, Sec4.coe_diagHom, Matrix.det_diagonal,
      Fin.prod_univ_three] at h1
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons, Units.val_mul] at h1
    apply Units.ext
    rw [Units.val_mul, Units.val_one]
    linear_combination h1 - (s : K) * t * hμ
  refine ⟨fun hs1 => hns ⟨hs1, ?_⟩, fun ht1 => hns ⟨?_, ht1⟩, fun hst' => hns ⟨?_, ?_⟩⟩
  · rw [hs1, one_mul] at hst
    exact hst
  · rw [ht1, mul_one] at hst
    exact hst
  · rw [← hst'] at hst
    have : s ^ 3 = s := by rw [pow_three, hst, mul_one]
    rw [hs] at this
    exact this.symm
  · rw [← hst'] at hst ⊢
    have : s ^ 3 = s := by rw [pow_three, hst, mul_one]
    rw [hs] at this
    exact this.symm

theorem pair_cases {s t s' t' : Kˣ} (hs : s ^ 3 = 1) (ht : t ^ 3 = 1) (hs' : s' ^ 3 = 1)
    (ht' : t' ^ 3 = 1) (h : s ≠ 1 ∧ t ≠ 1 ∧ s ≠ t) (h' : s' ≠ 1 ∧ t' ≠ 1 ∧ s' ≠ t') :
    (s' = s ∧ t' = t) ∨ (s' = s ^ 2 ∧ t' = t ^ 2) := by
  obtain ⟨hs1, ht1, hst⟩ := h
  obtain ⟨hs1', ht1', hst'⟩ := h'
  have v : ∀ {u : Kˣ}, u ^ 3 = 1 → (u : K) ^ 3 = 1 := fun hu => by
    rw [← Units.val_pow_eq_pow_val, hu, Units.val_one]
  have hsK : (s : K) ≠ 1 := fun h => hs1 (Units.ext h)
  have cases : ∀ {u : Kˣ}, u ^ 3 = 1 → u = 1 ∨ u = s ∨ u = s ^ 2 := fun {u} hu => by
    rcases Sec4.cube_root_cases (v hs) hsK (v hu) with h | h | h
    · exact Or.inl (Units.ext h)
    · exact Or.inr (Or.inl (Units.ext h))
    · exact Or.inr (Or.inr (Units.ext (by rw [h, Units.val_pow_eq_pow_val])))
  have hts : t = s ^ 2 := by
    rcases cases ht with h | h | h
    · exact absurd h ht1
    · exact absurd h.symm hst
    · exact h
  have hs4 : (s ^ 2) ^ 2 = s := by
    rw [← pow_mul, show 2 * 2 = 3 + 1 from rfl, pow_succ, hs, one_mul]
  rcases cases hs' with h1 | h1 | h1
  · exact absurd h1 hs1'
  · left
    refine ⟨h1, ?_⟩
    rcases cases ht' with h2 | h2 | h2
    · exact absurd h2 ht1'
    · exact absurd (h1.trans h2.symm) hst'
    · rw [h2, hts]
  · right
    refine ⟨h1, ?_⟩
    rcases cases ht' with h2 | h2 | h2
    · exact absurd h2 ht1'
    · rw [h2, hts, hs4]
    · exact absurd (h1.trans h2.symm) hst'

theorem eq_scalar_mul_of_conj {y M g : GL (Fin 3) K} {l μ s t : Kˣ}
    (hy : g⁻¹ * y * g = GeneralLinearGroup.scalar (Fin 3) l * diagUnits 1 s t)
    (hM : g⁻¹ * M * g = GeneralLinearGroup.scalar (Fin 3) μ * diagUnits 1 s t) :
    y = GeneralLinearGroup.scalar (Fin 3) (l * μ⁻¹) * M := by
  have h1 : g⁻¹ * y * g = GeneralLinearGroup.scalar (Fin 3) (l * μ⁻¹) * (g⁻¹ * M * g) := by
    rw [hy, hM, ← mul_assoc, ← map_mul, mul_assoc l, inv_mul_cancel, mul_one]
  calc y = g * (g⁻¹ * y * g) * g⁻¹ := by group
    _ = g * (GeneralLinearGroup.scalar (Fin 3) (l * μ⁻¹) * (g⁻¹ * M * g)) * g⁻¹ := by rw [h1]
    _ = g * GeneralLinearGroup.scalar (Fin 3) (l * μ⁻¹) * g⁻¹ * M := by group
    _ = GeneralLinearGroup.scalar (Fin 3) (l * μ⁻¹) * M := by rw [conj_scalar]

end Matrices

section Groups

variable {G : Type} [Group G]

theorem eq_one_of_conj_eq_sq {x b : G} (hx : IsPGroup 3 (Subgroup.zpowers x)) (hb : b ^ 3 = 1)
    (h : x * b * x⁻¹ = b ^ 2) : b = 1 := by
  have h2 : x ^ 2 * b * (x ^ 2)⁻¹ = b := by
    have e1 : x ^ 2 * b * (x ^ 2)⁻¹ = x * (x * b * x⁻¹) * x⁻¹ := by
      rw [pow_two]
      group
    rw [e1, h, ← MulAut.conj_apply, map_pow, MulAut.conj_apply, h, ← pow_mul,
      show 2 * 2 = 3 + 1 from rfl, pow_succ, hb, one_mul]
  obtain ⟨r, hr⟩ := hx ⟨x, Subgroup.mem_zpowers x⟩
  have hr' : x ^ 3 ^ r = 1 := by simpa using congrArg Subtype.val hr
  obtain ⟨s, hs⟩ : Odd (3 ^ r) := Odd.pow (by decide)
  have hxx : x = (x ^ 2) ^ (s + 1) := by
    rw [← pow_mul, show 2 * (s + 1) = 3 ^ r + 1 by omega, pow_succ, hr', one_mul]
  have hfix : ∀ j : ℕ, ((MulAut.conj (x ^ 2)) ^ j) b = b := by
    intro j
    induction j with
    | zero => rfl
    | succ j ih => rw [pow_succ, MulAut.mul_apply, MulAut.conj_apply, h2, ih]
  have hxb : x * b * x⁻¹ = b := by
    rw [hxx, ← MulAut.conj_apply, map_pow]
    exact hfix (s + 1)
  rw [hxb] at h
  have h' : b * 1 = b * b := by rw [mul_one, ← pow_two, ← h]
  exact (mul_left_cancel h').symm

variable [Finite G]

theorem le_normalizer_of_isPGroup_centralizer (h45 : Sec4.Item4_5) (hG : TheoremFourHyp G)
    {c : G} (hc3 : c ^ 3 = 1) (hc1 : c ≠ 1) {Q : Subgroup G} (hQ : IsPGroup 3 Q)
    (hQC : Q ≤ Subgroup.centralizer ({c} : Set G)) :
    ∀ L ∈ thetaComponentsAt 3 c, Q ≤ Subgroup.normalizer (L : Set G) := by
  set C := Subgroup.centralizer ({c} : Set G) with hCdef
  have hC4 : SectionFourHyp C := hG.sectionFourHyp (Sec6.centralizer_ne_top_of_ne_one hG hc1)
  have hQ' : IsPGroup 3 (Q.subgroupOf C) := hQ.comap_subtype
  have hcC : c ∈ C := Subgroup.mem_centralizer_singleton_iff.mpr rfl
  have hcore : CFSG.pCore 3 C ≠ ⊥ := by
    set c' : C := ⟨c, hcC⟩
    have hc'3 : orderOf c' = 3 := by
      rw [Subgroup.orderOf_mk]
      exact orderOf_eq_prime hc3 hc1
    have hZn : (Subgroup.zpowers c').Normal := by
      constructor
      intro n hn g
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hn
      have hgc : g * c' = c' * g := Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp g.2)
      have : g * c' ^ k * g⁻¹ = c' ^ k := by
        rw [(Commute.zpow_right hgc k).eq, mul_assoc, mul_inv_cancel, mul_one]
      rw [this]
      exact Subgroup.zpow_mem_zpowers c' k
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have hZ3 : IsPGroup 3 (Subgroup.zpowers c') :=
      IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hc'3, pow_one])
    have hZle : Subgroup.zpowers c' ≤ CFSG.pCore 3 C := le_sSup ⟨hZn, hZ3⟩
    intro hbot
    have hc'1 : c' = 1 := by
      have := hZle (Subgroup.mem_zpowers c')
      rwa [hbot, Subgroup.mem_bot] at this
    exact hc1 (congrArg Subtype.val hc'1)
  intro L hL
  obtain ⟨L', hL', rfl⟩ := hL
  have hN := Sec6.item45_of_item4_5 h45 C hC4 (Q.subgroupOf C) hQ' (Or.inl hcore) L' hL'
  intro q hq
  have hqN : (⟨q, hQC hq⟩ : C) ∈ Subgroup.normalizer (L' : Set C) :=
    hN (Subgroup.mem_subgroupOf.mpr hq)
  rw [Subgroup.mem_normalizer_iff] at hqN ⊢
  intro x
  constructor
  · rintro ⟨x', hx', rfl⟩
    exact ⟨_, (hqN x').mp hx', rfl⟩
  · rintro ⟨y, hy, hyx⟩
    have hyx' : (y : G) = q * x * q⁻¹ := hyx
    have hxC : x ∈ C := by
      have hx' : x = q⁻¹ * (y : G) * q := by
        rw [hyx']
        group
      rw [hx']
      exact C.mul_mem (C.mul_mem (C.inv_mem (hQC hq)) y.2) (hQC hq)
    refine ⟨⟨x, hxC⟩, (hqN ⟨x, hxC⟩).mpr ?_, rfl⟩
    have : (⟨q, hQC hq⟩ : C) * ⟨x, hxC⟩ * (⟨q, hQC hq⟩ : C)⁻¹ = y := Subtype.ext hyx'.symm
    rw [this]
    exact hy

end Groups


theorem item2118TypeTwo_of (h45 : Sec4.Item4_5) (h66 : Sec6.Item6_6) : Item2118TypeTwo := by
  intro G _ _ A E U c L hpair hnL hC _ _ hcL hB9 e heA heL x hxN hx3 hxc hxe
  obtain ⟨n, hn, hev, ⟨eL⟩⟩ := hnL
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hpairs := mem_lThreeStarPairs_iff.mp hpair.mem_pair
  have hAe : IsElemAbelian 3 A := hpair.mem_S.1.1
  have hcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hAe.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have h3 : ∀ a ∈ A, a ^ 3 = 1 := hAe.2
  have hcA : c ∈ A := hpair.mem_E.2 hpairs.1.1
  have hc1 : c ≠ 1 := hpairs.2.1
  have hc3 : orderOf c = 3 := orderOf_eq_prime (h3 c hcA) hc1
  have hLc : L ∈ thetaComponentsAt 3 c := lZeroStarAt_subset A c hpairs.2.2.1
  have hLC : L ≤ Subgroup.centralizer ({c} : Set G) :=
    Sec6.le_centralizer_of_mem_thetaComponentsAt hLc
  have hG4 := hpair.standing.toTheoremFourHyp
  have hAL : A ≤ Subgroup.normalizer (L : Set G) :=
    Sec6.le_normalizer_of_mem_thetaComponentsAt h45 hG4 hAe hcA hc1 L hLc
  have hxc' : x * c = c * x := by
    calc x * c = x * c * x⁻¹ * x := by group
      _ = c * x := by rw [hxc]
  have hxL : x ∈ Subgroup.normalizer (L : Set G) :=
    le_normalizer_of_isPGroup_centralizer h45 hG4 (h3 c hcA) hc1 hx3
      (Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr hxc')) L hLc
      (Subgroup.mem_zpowers x)
  have hLs : L ∈ lStar A :=
    lZeroStar_subset_lStar A (lZeroStarAt_subset_lZeroStar A c hpairs.2.2.1)
  have hCA : A ⊓ Sec4.thetaQuotCentralizer L = Subgroup.zpowers c := by
    symm
    refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr
      ⟨hcA, Sec6.mem_thetaQuotCentralizer_of_mem_thetaComponentsAt hLc⟩) ?_
    rw [Nat.card_zpowers, hc3]
    exact Sec6.card_le_three_of_isCyclic (h66 G hpair.standing A hpair.mem_S L hLs)
      fun y hy => h3 y hy.1
  have hcZL : Subgroup.zpowers c ≤ L := Subgroup.zpowers_le.mpr hcL
  set T : Subgroup.normalizer (L : Set G) →* MulAut (lBar L) :=
    (Sec4.thetaQuotMulAut L).comp L.normalizerMonoidHom with hT
  have hTmk : ∀ (g : G) (hg : g ∈ Subgroup.normalizer (L : Set G)) (l : G) (hl : l ∈ L),
      T ⟨g, hg⟩ ((⟨l, hl⟩ : L) : lBar L) =
        ((⟨g * l * g⁻¹, (Subgroup.mem_normalizer_iff.mp hg l).mp hl⟩ : L) : lBar L) :=
    fun _ _ _ _ => rfl
  have hTinner : ∀ (l₀ : G) (hl₀ : l₀ ∈ L) (z : lBar L),
      T ⟨l₀, Subgroup.le_normalizer hl₀⟩ z =
        ((⟨l₀, hl₀⟩ : L) : lBar L) * z * ((⟨l₀, hl₀⟩ : L) : lBar L)⁻¹ := by
    intro l₀ hl₀ z
    induction z using QuotientGroup.induction_on with
    | H l => rfl
  have hT1 : ∀ (a : G) (ha : a ∈ A), T ⟨a, hAL ha⟩ = 1 → a ∈ Subgroup.zpowers c := by
    intro a ha h
    rw [← hCA]
    exact ⟨ha, ⟨a, hAL ha⟩, h, rfl⟩
  have hTeq : ∀ (a : G) (ha : a ∈ A) (a' : G) (ha' : a' ∈ A),
      T ⟨a, hAL ha⟩ = T ⟨a', hAL ha'⟩ → a * a'⁻¹ ∈ Subgroup.zpowers c := by
    intro a ha a' ha' h
    apply hT1 _ (A.mul_mem ha (A.inv_mem ha'))
    have : (⟨a * a'⁻¹, hAL (A.mul_mem ha (A.inv_mem ha'))⟩ :
        Subgroup.normalizer (L : Set G)) = ⟨a, hAL ha⟩ * (⟨a', hAL ha'⟩)⁻¹ := rfl
    rw [this, map_mul, map_inv, h, mul_inv_cancel]
  obtain ⟨π, p, f, K, _, hPi, hmod, ε, D, hD, hconj, -⟩ := hC
  obtain ⟨rfl, rfl, rfl⟩ := SL3Lines.params_eq hn hev hPi hmod (eL.symm.trans ε)
  have := hPi.finite
  have hf2 : 2 ≤ f := by obtain ⟨k, hk⟩ := hev; omega
  have hK : Nat.card K = 2 ^ f := hPi.card
  have hK4 : 4 ≤ Nat.card K := by
    rw [hK]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf2
  obtain ⟨τ₀, hτ₀, hτ₀1⟩ := Sec4.exists_tau hPi hmod
  set ψ : lBar L →* GL (Fin 3) K :=
    (slPi true 3 (2 ^ f) K).subtype.comp ε.toMonoidHom with hψ
  have hψinj : Function.Injective ψ :=
    (slPi true 3 (2 ^ f) K).subtype_injective.comp ε.injective
  have hscal : ∀ N : GL (Fin 3) K, (∀ z, N * ψ z = ψ z * N) → N ∈ StatedScalars (Fin 3) K := by
    intro N hN
    refine Sec4.mem_statedScalars_of_commute (π := true) (p := 2) (f := f)
      (fun h => absurd h (by decide)) (fun h => absurd h (by decide)) hτ₀ hτ₀1 fun M hM => ?_
    have := hN (ε.symm ⟨M, hM⟩)
    simpa [hψ] using this
  have hTone : ∀ (a : G) (ha : a ∈ Subgroup.normalizer (L : Set G)) (N : GL (Fin 3) K),
      N ∈ StatedScalars (Fin 3) K → (∀ z, ψ (T ⟨a, ha⟩ z) = N * ψ z * N⁻¹) →
        T ⟨a, ha⟩ = 1 := by
    intro a ha N hNs hN
    ext z
    apply hψinj
    rw [hN, MulAut.one_apply, ← Sec4.commute_of_mem_statedScalars hNs (ψ z),
      mul_inv_cancel_right]
  have hyA : ∀ (a : G) (ha : a ∈ A), ∃ y ∈ D, ∀ z, ψ (T ⟨a, hAL ha⟩ z) = y * ψ z * y⁻¹ := by
    intro a ha
    obtain ⟨y, hyD, hy⟩ := hconj _ (Sec4.mem_autThetaQuot_iff.mpr ⟨a, hAL ha, ha, rfl⟩)
    exact ⟨y, hyD, fun z => hy z⟩
  obtain ⟨g, -, hdiag, -⟩ := Sec4.isTypeC_conj_std hPi hmod hD
  set cb : lBar L := ((⟨c, hcL⟩ : L) : lBar L) with hcb
  have hcbcent : ∀ z : lBar L, cb * z = z * cb := by
    intro z
    induction z using QuotientGroup.induction_on with
    | H l =>
      rw [hcb, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
      congr 1
      apply Subtype.ext
      exact (Subgroup.mem_centralizer_singleton_iff.mp (hLC l.2)).symm
  obtain ⟨ζ, hζ⟩ := hscal (ψ cb) fun z => by rw [← map_mul, ← map_mul, hcbcent z]
  have hζ3 : (ζ : K) ^ 3 = 1 := by
    have h1 : ψ cb ^ 3 = 1 := by
      have hc3' : cb ^ 3 = 1 := by
        rw [hcb, ← QuotientGroup.mk_pow]
        have : (⟨c, hcL⟩ : L) ^ 3 = 1 := Subtype.ext (by simpa using h3 c hcA)
        rw [this, QuotientGroup.mk_one]
      rw [← map_pow, hc3', map_one]
    rw [← hζ, ← map_pow] at h1
    have h2 := congrArg (fun X : GL (Fin 3) K => (X : Matrix (Fin 3) (Fin 3) K) 0 0) h1
    simp only [scalar_apply_self, Units.val_one, Matrix.one_apply_eq] at h2
    rw [← Units.val_pow_eq_pow_val, h2]
  have hζ1 : (ζ : K) ≠ 1 := by
    intro h
    have hζ' : ζ = 1 := Units.ext h
    rw [hζ', map_one] at hζ
    have hcb1 : cb = 1 := hψinj (hζ.symm.trans (map_one ψ).symm)
    rw [hcb, QuotientGroup.eq_one_iff] at hcb1
    obtain ⟨-, -, hT3, -⟩ :=
      solvable_prime_complement_core_characterization (H := L) Nat.prime_three
    apply hT3
    have h := orderOf_dvd_natCard (⟨⟨c, hcL⟩, hcb1⟩ : aschbacherSolvableCore 3 L)
    rwa [Subgroup.orderOf_mk, Subgroup.orderOf_mk, hc3] at h
  obtain ⟨b₀, hb₀, hb₀c⟩ : ∃ b₀ ∈ A ⊓ L, b₀ ∉ Subgroup.zpowers c := by
    by_contra hno
    push Not at hno
    have hle := Subgroup.card_le_of_le
      (show A ⊓ L ≤ Subgroup.zpowers c from fun b hb => hno b hb)
    rw [hB9, Nat.card_zpowers, hc3] at hle
    omega
  set bb : lBar L := ((⟨b₀, hb₀.2⟩ : L) : lBar L) with hbb
  have hbbT : ∀ z, ψ (T ⟨b₀, hAL hb₀.1⟩ z) = ψ bb * ψ z * (ψ bb)⁻¹ := by
    intro z
    have : T ⟨b₀, hAL hb₀.1⟩ z = bb * z * bb⁻¹ := hTinner b₀ hb₀.2 z
    rw [this, map_mul, map_mul, map_inv]
  obtain ⟨yb, hybD, hyb⟩ := hyA b₀ hb₀.1
  obtain ⟨lam, hlam⟩ := hscal (yb⁻¹ * ψ bb) fun z => by
    calc yb⁻¹ * ψ bb * ψ z = yb⁻¹ * (ψ bb * ψ z * (ψ bb)⁻¹) * ψ bb := by group
      _ = yb⁻¹ * (yb * ψ z * yb⁻¹) * ψ bb := by rw [← hbbT z, hyb z]
      _ = ψ z * (yb⁻¹ * ψ bb) := by group
  obtain ⟨lb, sb, tb, hsb, htb, hybg⟩ := hdiag yb hybD
  have hsb3 : sb ^ 3 = 1 := (mem_rootsOfUnity _ _).mp hsb
  have htb3 : tb ^ 3 = 1 := (mem_rootsOfUnity _ _).mp htb
  have hMb : g⁻¹ * ψ bb * g =
      GeneralLinearGroup.scalar (Fin 3) (lb * lam) * diagUnits 1 sb tb := by
    have h1 : ψ bb = yb * GeneralLinearGroup.scalar (Fin 3) lam := by
      rw [hlam]
      group
    calc g⁻¹ * ψ bb * g = g⁻¹ * yb * g * GeneralLinearGroup.scalar (Fin 3) lam := by
          rw [h1]
          calc g⁻¹ * (yb * GeneralLinearGroup.scalar (Fin 3) lam) * g
              = g⁻¹ * yb * (GeneralLinearGroup.scalar (Fin 3) lam * g) := by group
            _ = g⁻¹ * yb * (g * GeneralLinearGroup.scalar (Fin 3) lam) := by
              rw [SL3Lines.scalar_mul_comm]
            _ = g⁻¹ * yb * g * GeneralLinearGroup.scalar (Fin 3) lam := by group
      _ = GeneralLinearGroup.scalar (Fin 3) lb * diagUnits 1 sb tb *
          GeneralLinearGroup.scalar (Fin 3) lam := by rw [hybg]
      _ = GeneralLinearGroup.scalar (Fin 3) (lb * lam) * diagUnits 1 sb tb := by
          rw [mul_assoc, ← SL3Lines.scalar_mul_comm lam, ← mul_assoc, ← map_mul]
  have hbb3 : ψ bb ^ 3 = 1 := by
    have : bb ^ 3 = 1 := by
      rw [hbb, ← QuotientGroup.mk_pow]
      have : (⟨b₀, hb₀.2⟩ : L) ^ 3 = 1 := Subtype.ext (by simpa using h3 b₀ hb₀.1)
      rw [this, QuotientGroup.mk_one]
    rw [← map_pow, this, map_one]
  have hbbdet : ((ψ bb : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).det = 1 :=
    (Sec4.mem_slPi_true _).mp (ε bb).2
  have hnsb : ¬ (sb = 1 ∧ tb = 1) := by
    rintro ⟨rfl, rfl⟩
    rw [SL3Lines.diagUnits_one_one_one, mul_one] at hMb
    have hbbS : ψ bb = GeneralLinearGroup.scalar (Fin 3) (lb * lam) := by
      calc ψ bb = g * (g⁻¹ * ψ bb * g) * g⁻¹ := by group
        _ = GeneralLinearGroup.scalar (Fin 3) (lb * lam) := by rw [hMb, conj_scalar]
    exact hb₀c (hT1 b₀ hb₀.1 (hTone b₀ (hAL hb₀.1) (ψ bb) ⟨lb * lam, hbbS.symm⟩ hbbT))
  obtain ⟨hsb1, htb1, hsbtb⟩ := distinct_of_conj_diag hsb3 htb3 hMb hbbdet hbb3 hnsb
  obtain ⟨ye, hyeD, hye⟩ := hyA e heA
  obtain ⟨le, se, te, hse, hte, hyeg⟩ := hdiag ye hyeD
  have hse3 : se ^ 3 = 1 := (mem_rootsOfUnity _ _).mp hse
  have hte3 : te ^ 3 = 1 := (mem_rootsOfUnity _ _).mp hte
  have hnse : ¬ (se = 1 ∧ te = 1) := by
    rintro ⟨rfl, rfl⟩
    rw [SL3Lines.diagUnits_one_one_one, mul_one] at hyeg
    have hyeS : ye = GeneralLinearGroup.scalar (Fin 3) le := by
      calc ye = g * (g⁻¹ * ye * g) * g⁻¹ := by group
        _ = GeneralLinearGroup.scalar (Fin 3) le := by rw [hyeg, conj_scalar]
    exact heL (hcZL (hT1 e heA (hTone e (hAL heA) ye ⟨le, hyeS.symm⟩ hye)))
  have hnde : ¬ (se ≠ 1 ∧ te ≠ 1 ∧ se ≠ te) := by
    intro hd
    apply heL
    obtain ⟨k, ν, hk⟩ : ∃ (k : ℕ) (ν : Kˣ),
        ye = GeneralLinearGroup.scalar (Fin 3) ν * ψ bb ^ k := by
      rcases pair_cases hsb3 htb3 hse3 hte3 ⟨hsb1, htb1, hsbtb⟩ hd with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact ⟨1, le * (lb * lam)⁻¹, by rw [pow_one]; exact eq_scalar_mul_of_conj hyeg hMb⟩
      · refine ⟨2, le * ((lb * lam) ^ 2)⁻¹, eq_scalar_mul_of_conj hyeg ?_⟩
        have := conj_pow (a := g⁻¹) (b := ψ bb) (i := 2)
        rw [inv_inv] at this
        rw [← this, hMb, scalar_mul_diagUnits_pow]
    have hbk : b₀ ^ k ∈ A ⊓ L := (A ⊓ L).pow_mem hb₀ k
    have hTk : T ⟨e, hAL heA⟩ = T ⟨b₀ ^ k, hAL hbk.1⟩ := by
      ext z
      apply hψinj
      have h1 : T ⟨b₀ ^ k, hAL hbk.1⟩ z = bb ^ k * z * (bb ^ k)⁻¹ := by
        have hpow : ((⟨b₀ ^ k, hbk.2⟩ : L) : lBar L) = bb ^ k := by
          rw [hbb, ← QuotientGroup.mk_pow]
          congr 1
        rw [← hpow]
        exact hTinner (b₀ ^ k) hbk.2 z
      rw [hye z, hk, h1, map_mul, map_mul, map_inv, map_pow]
      calc GeneralLinearGroup.scalar (Fin 3) ν * ψ bb ^ k * ψ z *
            (GeneralLinearGroup.scalar (Fin 3) ν * ψ bb ^ k)⁻¹ =
          GeneralLinearGroup.scalar (Fin 3) ν * (ψ bb ^ k * ψ z * (ψ bb ^ k)⁻¹) *
            (GeneralLinearGroup.scalar (Fin 3) ν)⁻¹ := by group
        _ = ψ bb ^ k * ψ z * (ψ bb ^ k)⁻¹ := by
          rw [SL3Lines.scalar_mul_comm, mul_inv_cancel_right]
    have hm := hTeq e heA (b₀ ^ k) hbk.1 hTk
    have := L.mul_mem (hcZL hm) hbk.2
    rwa [inv_mul_cancel_right] at this
  obtain ⟨w, hw⟩ := exists_centralizer_eq_map_blockHom hPi hyeg hnse hnde
  set τe : MulAut (lBar L) := T ⟨e, hAL heA⟩ with hτe
  set Cb := fixedSubgroupOf τe with hCb
  set X₀ : Subgroup (GL (Fin 3) K) := (⊤ : Subgroup (GL (Fin 2) K)).map blockHom with hX₀
  have hmapX : Cb.map ψ = X₀.map (MulAut.conj w).toMonoidHom :=
    (SL3Lines.map_fixedSubgroupOf_eq_of_conj ε hye).trans hw
  have hQmap : (⁅Cb, Cb⁆).map ψ =
      ⁅X₀.map (MulAut.conj w).toMonoidHom, X₀.map (MulAut.conj w).toMonoidHom⁆ := by
    rw [Subgroup.map_commutator, hmapX]
  have hcrit : ∀ z ∈ Cb, z ∈ ⁅Cb, Cb⁆ ↔
      ((w⁻¹ * ψ z * w : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 0 0 = 1 := by
    intro z hz
    have hzX : ψ z ∈ X₀.map (MulAut.conj w).toMonoidHom := by
      rw [← hmapX]
      exact ⟨z, hz, rfl⟩
    rw [← mem_commutator_map_conj_iff hK4 w hzX, ← hQmap]
    constructor
    · intro h
      exact ⟨z, h, rfl⟩
    · rintro ⟨z', hz', hz'z⟩
      rwa [← hψinj hz'z]
  have hfixA : ∀ (a : G) (ha : a ∈ A) (haL : a ∈ L), ((⟨a, haL⟩ : L) : lBar L) ∈ Cb := by
    intro a ha haL
    rw [hCb, mem_fixedSubgroupOf, hτe, hTmk]
    congr 1
    apply Subtype.ext
    show e * a * e⁻¹ = a
    rw [hcomm e heA a ha, mul_inv_cancel_right]
  have hcQ : ∀ i : ℕ, cb ^ i ∈ ⁅Cb, Cb⁆ → (ζ : K) ^ i = 1 := by
    intro i hi
    have hci : cb ^ i ∈ Cb := Cb.pow_mem (hfixA c hcA hcL) i
    rw [hcrit _ hci, map_pow, ← hζ, ← map_pow, mul_assoc, SL3Lines.scalar_mul_comm,
      ← mul_assoc, inv_mul_cancel, one_mul, scalar_apply_self] at hi
    rw [← Units.val_pow_eq_pow_val, hi]
  have hbbX : w⁻¹ * ψ bb * w ∈ X₀ := by
    have h1 : ψ bb ∈ X₀.map (MulAut.conj w).toMonoidHom := by
      rw [← hmapX]
      exact ⟨bb, hfixA b₀ hb₀.1 hb₀.2, rfl⟩
    rw [Subgroup.mem_map_equiv, MulAut.conj_symm_apply] at h1
    exact h1
  obtain ⟨B, -, hB⟩ := hbbX
  have hα3 : (((GeneralLinearGroup.det B)⁻¹ : Kˣ) : K) ^ 3 = 1 := by
    have h1 : blockHom (B ^ 3) = 1 := by
      rw [map_pow, hB]
      have := conj_pow (a := w⁻¹) (b := ψ bb) (i := 3)
      rw [inv_inv] at this
      rw [this, hbb3, mul_one, inv_mul_cancel]
    have h2 : B ^ 3 = 1 := Sec4.blockHom_injective (by rw [h1, map_one])
    rw [← Units.val_pow_eq_pow_val, inv_pow, ← map_pow, h2, map_one, inv_one, Units.val_one]
  obtain ⟨m, hm⟩ : ∃ m : ℕ, (((GeneralLinearGroup.det B)⁻¹ : Kˣ) : K) * (ζ : K) ^ m = 1 := by
    rcases Sec4.cube_root_cases hζ3 hζ1 hα3 with h | h | h
    · exact ⟨0, by rw [h, pow_zero, mul_one]⟩
    · exact ⟨2, by rw [h]; linear_combination hζ3⟩
    · exact ⟨1, by rw [h]; linear_combination hζ3⟩
  set b' := b₀ * c ^ m with hb'
  have hb'AL : b' ∈ A ⊓ L := (A ⊓ L).mul_mem hb₀ ((A ⊓ L).pow_mem ⟨hcA, hcL⟩ m)
  have hb'c : b' ∉ Subgroup.zpowers c := by
    intro h
    apply hb₀c
    have : b₀ = b' * (c ^ m)⁻¹ := by rw [hb', mul_inv_cancel_right]
    rw [this]
    exact (Subgroup.zpowers c).mul_mem h
      ((Subgroup.zpowers c).inv_mem ((Subgroup.zpowers c).pow_mem (Subgroup.mem_zpowers c) m))
  set bb' : lBar L := ((⟨b', hb'AL.2⟩ : L) : lBar L) with hbb'
  have hbb'eq : bb' = bb * cb ^ m := by
    rw [hbb', hbb, hcb, ← QuotientGroup.mk_pow, ← QuotientGroup.mk_mul]
    rfl
  have hbb'Q : bb' ∈ ⁅Cb, Cb⁆ := by
    rw [hcrit bb' (hfixA b' hb'AL.1 hb'AL.2), hbb'eq, map_mul, map_pow, ← hζ, ← map_pow]
    have e1 : w⁻¹ * (ψ bb * GeneralLinearGroup.scalar (Fin 3) (ζ ^ m)) * w =
        w⁻¹ * ψ bb * w * GeneralLinearGroup.scalar (Fin 3) (ζ ^ m) := by
      calc w⁻¹ * (ψ bb * GeneralLinearGroup.scalar (Fin 3) (ζ ^ m)) * w =
          w⁻¹ * ψ bb * (GeneralLinearGroup.scalar (Fin 3) (ζ ^ m) * w) := by group
        _ = w⁻¹ * ψ bb * (w * GeneralLinearGroup.scalar (Fin 3) (ζ ^ m)) := by
          rw [SL3Lines.scalar_mul_comm]
        _ = w⁻¹ * ψ bb * w * GeneralLinearGroup.scalar (Fin 3) (ζ ^ m) := by group
    rw [e1, mul_scalar_apply, ← hB, blockHom_zero_zero, Units.val_pow_eq_pow_val]
    exact hm
  set τx : MulAut (lBar L) := T ⟨x, hxL⟩ with hτx
  have hτxe : τx * τe = τe * τx := by
    rw [hτx, hτe, ← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    show x * e = e * x
    calc x * e = x * e * x⁻¹ * x := by group
      _ = e * x := by rw [hxe]
  have hτxC : ∀ z ∈ Cb, τx z ∈ Cb := by
    intro z hz
    rw [hCb, mem_fixedSubgroupOf] at hz ⊢
    rw [← MulAut.mul_apply, ← hτxe, MulAut.mul_apply, hz]
  have hτxQ : ∀ z ∈ ⁅Cb, Cb⁆, τx z ∈ ⁅Cb, Cb⁆ := by
    intro z hz
    have h2 : Cb.map τx.toMonoidHom ≤ Cb := by
      rintro _ ⟨y, hy, rfl⟩
      exact hτxC y hy
    have h1 : (⁅Cb, Cb⁆).map τx.toMonoidHom ≤ ⁅Cb, Cb⁆ := by
      rw [Subgroup.map_commutator]
      exact Subgroup.commutator_mono h2 h2
    exact h1 ⟨z, hz, rfl⟩
  have hxb'Q : τx bb' ∈ ⁅Cb, Cb⁆ := hτxQ bb' hbb'Q
  have hxb'A : x * b' * x⁻¹ ∈ A := (Subgroup.mem_normalizer_iff.mp hxN b').mp hb'AL.1
  have hxb'L : x * b' * x⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp hxL b').mp hb'AL.2
  have hcommAL : ∀ y ∈ A ⊓ L, ∀ y' ∈ A ⊓ L, y * y' = y' * y :=
    fun y hy y' hy' => hcomm y hy.1 y' hy'.1
  have h3AL : ∀ y ∈ A ⊓ L, y ^ 3 = 1 := fun y hy => h3 y hy.1
  have hcAL : Subgroup.zpowers c ≤ A ⊓ L := Subgroup.zpowers_le.mpr ⟨hcA, hcL⟩
  have hcard : Nat.card (A ⊓ L : Subgroup G) = 3 * Nat.card (Subgroup.zpowers c) := by
    rw [hB9, Nat.card_zpowers, hc3]
  have hdec := exists_pow_mul_of_card hcommAL h3AL hcAL hcard hb'AL hb'c
  obtain ⟨k, hk3, y, hy, hxy⟩ := hdec _ ⟨hxb'A, hxb'L⟩
  obtain ⟨i, hi3, rfl⟩ := exists_pow_lt_three_of_mem_zpowers (h3 c hcA) hy
  have hτxbb' : τx bb' = bb' ^ k * cb ^ i := by
    rw [hτx, hbb', hTmk, hcb, ← QuotientGroup.mk_pow, ← QuotientGroup.mk_pow,
      ← QuotientGroup.mk_mul]
    congr 1
    apply Subtype.ext
    simpa using hxy
  have hci : cb ^ i ∈ ⁅Cb, Cb⁆ := by
    have h1 : (bb' ^ k)⁻¹ * τx bb' ∈ ⁅Cb, Cb⁆ :=
      (⁅Cb, Cb⁆).mul_mem ((⁅Cb, Cb⁆).inv_mem ((⁅Cb, Cb⁆).pow_mem hbb'Q k)) hxb'Q
    rwa [hτxbb', inv_mul_cancel_left] at h1
  have hi0 : i = 0 := by
    have h1 := hcQ i hci
    interval_cases i
    · rfl
    · exact absurd (by rwa [pow_one] at h1) hζ1
    · exfalso
      apply hζ1
      linear_combination hζ3 - (ζ : K) * h1
  subst hi0
  rw [pow_zero, mul_one] at hxy
  have hb'1 : b' ≠ 1 := fun h => hb'c (h ▸ Subgroup.one_mem _)
  have hxb' : x * b' * x⁻¹ = b' := by
    interval_cases k
    · exfalso
      apply hb'1
      rw [pow_zero] at hxy
      calc b' = x⁻¹ * (x * b' * x⁻¹) * x := by group
        _ = 1 := by rw [hxy]; group
    · rwa [pow_one] at hxy
    · exact absurd (eq_one_of_conj_eq_sq hx3 (h3 b' hb'AL.1) hxy) hb'1
  intro b hb
  obtain ⟨k', -, y', hy', rfl⟩ := hdec b hb
  obtain ⟨i', -, rfl⟩ := exists_pow_lt_three_of_mem_zpowers (h3 c hcA) hy'
  rw [← MulAut.conj_apply, map_mul, map_pow, map_pow, MulAut.conj_apply, MulAut.conj_apply, hxb',
    hxc]

end CFSG.RankThree.PartTwo.Sec21.Item21LateProof
