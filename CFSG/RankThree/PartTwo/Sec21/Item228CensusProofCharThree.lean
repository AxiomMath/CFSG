module

public import CFSG.RankThree.PartTwo.Sec21.Item22Res4ProofNarrow
public import CFSG.RankThree.PartTwo.Sec21.Item228CensusProofCyc5
public import CFSG.RankThree.PartTwo.Sec21.Item223CensusResProofCharThree
public import CFSG.RankThree.SubgroupLists.SL3Involutions
import CFSG.RankThree.PartTwo.Sec21.Item223CensusProofA9
import CFSG.RankThree.PartTwo.Sec19.Step1914Tri
import CFSG.RankThree.PartTwo.KFacts.KSListsProofCard
import CFSG.Models.PGLSimple
import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projSL projSU projImage)
open CFSG.Assembly.LowTwoRank (StatedClassicalModel)
open CFSG.LieType.Multipliers.U43 (F9)
open Matrix

namespace Item228CensusProof

open Item223CensusResProof

theorem cyc5_map {R S : Type*} [Semiring R] [Semiring S] (f : R →+* S) (t : R) :
    f (cyc5 t) = cyc5 (f t) := by
  simp [cyc5, map_sum, map_pow]

theorem cyc5Rem_map {K L : Type*} [CommRing K] [CommRing L] (f : K →+* L) (a b : K) :
    cyc5Rem (f a) (f b) = (f (cyc5Rem a b).1, f (cyc5Rem a b).2) := by
  simp only [cyc5Rem, remSeq_map]
  refine Prod.ext ?_ ?_ <;> simp [Prod.fst_sum, Prod.snd_sum, map_sum]

theorem cyc5_ne_zero_F9 : ∀ t : F9, cyc5 t ≠ 0 := by
  intro t
  rw [cyc5_eq]
  revert t
  decide

theorem cyc5_ne_zero_zmod3 : ∀ t : ZMod 3, cyc5 t ≠ 0 := by
  intro t
  rw [cyc5_eq]
  revert t
  decide

theorem cyc5Rem_ne_zero_zmod3 : ∀ a b : ZMod 3, cyc5Rem a b ≠ 0 := by
  intro a b
  rw [cyc5Rem_eq]
  revert a b
  decide

theorem cyc5_ne_zero_of_ringEquiv {K L : Type*} [Field K] [Field L] (e : K ≃+* L)
    (h : ∀ t : K, cyc5 t ≠ 0) : ∀ t : L, cyc5 t ≠ 0 := by
  intro t ht
  apply h (e.symm t)
  apply e.injective
  rw [map_zero, ← ht, ← RingEquiv.coe_toRingHom, cyc5_map, RingEquiv.coe_toRingHom,
    RingEquiv.apply_symm_apply]

theorem cyc5Rem_ne_zero_of_ringEquiv {K L : Type*} [Field K] [Field L] (e : K ≃+* L)
    (h : ∀ a b : K, cyc5Rem a b ≠ 0) : ∀ a b : L, cyc5Rem a b ≠ 0 := by
  intro a b hab
  apply h (e.symm a) (e.symm b)
  have h1 := cyc5Rem_map e.symm.toRingHom a b
  simp only [RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom] at h1
  rw [h1, hab]
  simp

theorem five_ne_zero_of_charThree {K : Type*} [Field K] [CharP K 3] : (5 : K) ≠ 0 := by
  intro h
  have h' : ((5 : ℕ) : K) = 0 := by exact_mod_cast h
  rw [CharP.cast_eq_zero_iff K 3] at h'
  norm_num at h'

theorem two_ne_zero_of_charThree {K : Type*} [Field K] [CharP K 3] : (2 : K) ≠ 0 := by
  intro h
  have h' : ((2 : ℕ) : K) = 0 := by exact_mod_cast h
  rw [CharP.cast_eq_zero_iff K 3] at h'
  norm_num at h'

theorem pow_five_or_pow_three_of_pow_fifteen {K : Type} [Field K] [CharP K 3] {n : ℕ}
    [NeZero n] (hP1 : ∀ t : K, cyc5 t ≠ 0) (hdim : n ≤ 3 ∨ (n ≤ 4 ∧ ∀ a b : K, cyc5Rem a b ≠ 0))
    {B : GL (Fin n) K} (h15 : B ^ 15 = 1) : B ^ 5 = 1 ∨ B ^ 3 = 1 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  by_contra hne
  push Not at hne
  obtain ⟨h5', h3'⟩ := hne
  set c : Matrix (Fin n) (Fin n) K := ((B ^ 3 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)
  set M : Matrix (Fin n) (Fin n) K := ((B ^ 5 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)
  have hc5 : c ^ 5 = 1 := by
    rw [← Units.val_pow_eq_pow_val, ← pow_mul, h15, Units.val_one]
  have hc1 : c ≠ 1 := fun h => h3' (Units.ext h)
  have hMc : M * c = c * M := by
    rw [← Units.val_mul, ← Units.val_mul, ← pow_add, ← pow_add, add_comm]
  have hN3 : (M - 1) ^ 3 = 0 := by
    rw [sub_pow_char_of_commute 3 (Commute.one_right M), one_pow, ← Units.val_pow_eq_pow_val,
      ← pow_mul, h15, Units.val_one, sub_self]
  have hNc : (M - 1) * c = c * (M - 1) := by
    rw [sub_mul, mul_sub, hMc, one_mul, mul_one]
  have hdim' : Module.finrank K (Fin n → K) ≤ 3 ∨
      (Module.finrank K (Fin n → K) ≤ 4 ∧ ∀ a b : K, cyc5Rem a b ≠ 0) := by
    rw [Module.finrank_fin_fun]
    exact hdim
  have h := eq_zero_of_commute_cyc5 (V := Fin n → K) five_ne_zero_of_charThree hP1 hdim'
    (c := Matrix.toLinAlgEquiv' c) (N := Matrix.toLinAlgEquiv' (M - 1))
    (by rw [← map_pow, hc5, map_one])
    (fun h => hc1 (Matrix.toLinAlgEquiv'.injective (by rw [h, map_one])))
    (by rw [← map_mul, hNc, map_mul]) (by rw [← map_pow, hN3, map_zero])
  have h0 : M - 1 = 0 := Matrix.toLinAlgEquiv'.injective (by rw [h, map_zero])
  exact h5' (Units.ext (sub_eq_zero.mp h0))

theorem fintype_card_galoisField_three_two' [Fintype (GaloisField 3 2)] :
    Fintype.card (GaloisField 3 2) = 9 := by
  rw [← Nat.card_eq_fintype_card, GaloisField.card 3 2 (by norm_num)]
  norm_num

theorem cyc5_ne_zero_galoisField_three_two : ∀ t : GaloisField 3 2, cyc5 t ≠ 0 := by
  have : Fintype (GaloisField 3 2) := Fintype.ofFinite _
  exact cyc5_ne_zero_of_ringEquiv (FiniteField.ringEquivOfCardEq
    (by rw [fintype_card_galoisField_three_two']; rfl)) cyc5_ne_zero_F9

noncomputable abbrev fieldEquivThree : GaloisField 3 1 ≃+* ZMod 3 :=
  (GaloisField.equivZmodP 3).toRingEquiv

theorem cyc5_ne_zero_galoisField_three_one : ∀ t : GaloisField 3 1, cyc5 t ≠ 0 :=
  cyc5_ne_zero_of_ringEquiv fieldEquivThree.symm cyc5_ne_zero_zmod3

theorem cyc5Rem_ne_zero_galoisField_three_one : ∀ a b : GaloisField 3 1, cyc5Rem a b ≠ 0 :=
  cyc5Rem_ne_zero_of_ringEquiv fieldEquivThree.symm cyc5Rem_ne_zero_zmod3

theorem orderOf_ne_fifteen_projSL_three_nine (s : projSL 3 (GaloisField 3 2)) :
    orderOf s ≠ 15 := by
  have : Fintype (GaloisField 3 2) := Fintype.ofFinite _
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  intro hs
  obtain ⟨A, hA, hAs⟩ := s.2
  have hdet : Matrix.GeneralLinearGroup.det A = 1 := MonoidHom.mem_ker.mp hA
  have hmk : ∀ k : ℕ, s ^ k = 1 ↔ A ^ k ∈ Subgroup.center (GL (Fin 3) (GaloisField 3 2)) := by
    intro k
    rw [← OneMemClass.coe_eq_one, Subgroup.coe_pow, ← hAs, ← map_pow,
      Matrix.ProjGenLinGroup.mk_eq_one]
  have h15 : A ^ 15 = 1 := by
    have hc := (hmk 15).mp (hs ▸ pow_orderOf_eq_one s)
    rw [Matrix.GeneralLinearGroup.center_eq_range_scalar] at hc
    obtain ⟨l, hl⟩ := hc
    have hl3 : l ^ 3 = 1 := by
      have h1 := congrArg Matrix.GeneralLinearGroup.det hl
      rw [Matrix.GeneralLinearGroup.det_scalar, Fintype.card_fin, map_pow, hdet, one_pow] at h1
      exact h1
    have hl1 : l = 1 := Units.ext (eq_one_of_pow_three_eq_one (by
      rw [← Units.val_pow_eq_pow_val, hl3, Units.val_one]))
    rw [← hl, hl1, map_one]
  have hcent : ∀ k : ℕ, A ^ k = 1 → s ^ k = 1 := fun k h =>
    (hmk k).mpr (h ▸ Subgroup.one_mem _)
  rcases pow_five_or_pow_three_of_pow_fifteen cyc5_ne_zero_galoisField_three_two
    (Or.inl le_rfl) h15 with h | h
  · have := orderOf_dvd_of_pow_eq_one (hcent 5 h)
    rw [hs] at this
    norm_num at this
  · have := orderOf_dvd_of_pow_eq_one (hcent 3 h)
    rw [hs] at this
    norm_num at this

theorem orderOf_ne_fifteen_projSL_four_three (s : projSL 4 (GaloisField 3 1)) :
    orderOf s ≠ 15 := by
  have : Fintype (GaloisField 3 1) := Fintype.ofFinite _
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  intro hs
  obtain ⟨A, hA, hAs⟩ := s.2
  have hdet : Matrix.GeneralLinearGroup.det A = 1 := MonoidHom.mem_ker.mp hA
  have hmk : ∀ k : ℕ, s ^ k = 1 ↔ A ^ k ∈ Subgroup.center (GL (Fin 4) (GaloisField 3 1)) := by
    intro k
    rw [← OneMemClass.coe_eq_one, Subgroup.coe_pow, ← hAs, ← map_pow,
      Matrix.ProjGenLinGroup.mk_eq_one]
  have h15 : (A ^ 16) ^ 15 = 1 := by
    have hc := (hmk 15).mp (hs ▸ pow_orderOf_eq_one s)
    rw [Matrix.GeneralLinearGroup.center_eq_range_scalar] at hc
    obtain ⟨l, hl⟩ := hc
    have hl4 : l ^ 4 = 1 := by
      have h1 := congrArg Matrix.GeneralLinearGroup.det hl
      rw [Matrix.GeneralLinearGroup.det_scalar, Fintype.card_fin, map_pow, hdet, one_pow] at h1
      exact h1
    rw [← pow_mul, show 16 * 15 = 15 * 16 from rfl, pow_mul, ← hl, ← map_pow,
      show 16 = 4 * 4 from rfl, pow_mul, hl4, one_pow, map_one]
  have hcent : ∀ k : ℕ, (A ^ 16) ^ k = 1 → s ^ (16 * k) = 1 := fun k h =>
    (hmk (16 * k)).mpr (by rw [pow_mul, h]; exact Subgroup.one_mem _)
  rcases pow_five_or_pow_three_of_pow_fifteen cyc5_ne_zero_galoisField_three_one
    (Or.inr ⟨le_rfl, cyc5Rem_ne_zero_galoisField_three_one⟩) h15 with h | h
  · have := orderOf_dvd_of_pow_eq_one (hcent 5 h)
    rw [hs] at this
    norm_num at this
  · have := orderOf_dvd_of_pow_eq_one (hcent 3 h)
    rw [hs] at this
    norm_num at this

theorem eq_zero_of_commute_involution_two {K : Type*} [Field K] [CharP K 3]
    {s N : Matrix (Fin 2) (Fin 2) K} (hs : s * s = 1) (hs1 : s ≠ 1) (hsn : s ≠ -1)
    (hNs : N * s = s * N) (hN3 : N ^ 3 = 0) : N = 0 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h2 : (2 : K) ≠ 0 := two_ne_zero_of_charThree
  obtain ⟨α, l, hNeq⟩ : ∃ α l : K, N = α • (1 : Matrix (Fin 2) (Fin 2) K) + l • s := by
    obtain ⟨a, b, c, d, rfl⟩ : ∃ a b c d : K, s = !![a, b; c, d] := ⟨_, _, _, _, s.eta_fin_two⟩
    obtain ⟨w, x, y, z, rfl⟩ : ∃ w x y z : K, N = !![w, x; y, z] := ⟨_, _, _, _, N.eta_fin_two⟩
    have hn : ∀ p q r t : K, -!![p, q; r, t] = !![-p, -q; -r, -t] := by
      intro p q r t
      ext i j
      fin_cases i <;> fin_cases j <;> rfl
    simp only [Matrix.mul_fin_two, Matrix.one_fin_two, hn] at hs hNs hs1 hsn
    rw [← Matrix.ext_iff] at hs hNs
    simp [Fin.forall_fin_two] at hs hNs hs1 hsn
    obtain ⟨⟨s00, s01⟩, s10, s11⟩ := hs
    obtain ⟨⟨c00, c01⟩, c10, -⟩ := hNs
    have hsq : ∀ v : K, v * v = 1 → v = 1 ∨ v = -1 := fun v hv => mul_self_eq_one_iff.mp hv
    have had : a + d = 0 := by
      by_contra hne
      have hb : b = 0 := by
        have : b * (a + d) = 0 := by linear_combination s01
        exact (mul_eq_zero.mp this).resolve_right hne
      have hc : c = 0 := by
        have : c * (a + d) = 0 := by linear_combination s10
        exact (mul_eq_zero.mp this).resolve_right hne
      subst hb hc
      rcases hsq a (by linear_combination s00) with ha | ha <;>
        rcases hsq d (by linear_combination s11) with hd | hd
      · exact hs1 ha rfl rfl hd
      · exact hne (by rw [ha, hd]; ring)
      · exact hne (by rw [ha, hd]; ring)
      · exact hsn ha rfl rfl hd
    have hd : d = -a := by linear_combination had
    subst hd
    set u := (w - z) / 2 with hu
    have hw : w = (w + z) / 2 + u := by rw [hu]; field_simp; ring
    have hz : z = (w + z) / 2 - u := by rw [hu]; field_simp; ring
    have e1 : b * u = a * x := by
      have : (2 : K) * (b * u - a * x) = 0 := by rw [hu]; field_simp; linear_combination c01
      linear_combination (mul_eq_zero.mp this).resolve_left h2
    have e2 : c * u = a * y := by
      have : (2 : K) * (c * u - a * y) = 0 := by rw [hu]; field_simp; linear_combination -c10
      linear_combination (mul_eq_zero.mp this).resolve_left h2
    have e3 : c * x = b * y := by linear_combination c00
    obtain ⟨l, hl1, hl2, hl3⟩ : ∃ l : K, u = l * a ∧ x = l * b ∧ y = l * c := by
      by_cases ha0 : a = 0
      · subst ha0
        have hbc : b * c = 1 := by linear_combination s00
        have hb0 : b ≠ 0 := left_ne_zero_of_mul_eq_one hbc
        refine ⟨x / b, ?_, by field_simp, ?_⟩
        · simp only [mul_zero]
          simpa [hb0] using e1
        · field_simp
          linear_combination -e3
      · refine ⟨u / a, by field_simp, ?_, ?_⟩
        · field_simp
          linear_combination -e1
        · field_simp
          linear_combination -e2
    refine ⟨(w + z) / 2, l, ?_⟩
    ext i j
    fin_cases i <;> fin_cases j <;> simp
    · linear_combination hw + hl1
    · linear_combination hl2
    · linear_combination hl3
    · linear_combination hz - hl1
  have hs3 : s ^ 3 = s := by rw [pow_succ, pow_two, hs, one_mul]
  have hcube : N ^ 3 = α ^ 3 • (1 : Matrix (Fin 2) (Fin 2) K) + l ^ 3 • s := by
    rw [hNeq, add_pow_char_of_commute 3 ((Commute.one_left s).smul_left α |>.smul_right l),
      smul_pow, smul_pow, one_pow, hs3]
  rw [hN3] at hcube
  have e := fun i j => congrFun (congrFun hcube i) j
  have e00 := e 0 0
  have e11 := e 1 1
  have e01 := e 0 1
  have e10 := e 1 0
  simp at e00 e11 e01 e10
  have hss := fun i j => congrFun (congrFun hs i) j
  have hs00 := hss 0 0
  have hs01 := hss 0 1
  have hs10 := hss 1 0
  have hs11 := hss 1 1
  simp [Matrix.mul_apply, Fin.sum_univ_two] at hs00 hs01 hs10 hs11
  have hα : α = 0 := by
    have h3a : (2 : K) * α ^ 3 = -(l ^ 3 * (s 0 0 + s 1 1)) := by
      linear_combination -e00 - e11
    have htr : s 0 0 + s 1 1 = 0 := by
      by_contra htr
      have hb : s 0 1 = 0 := by
        have : s 0 1 * (s 0 0 + s 1 1) = 0 := by linear_combination hs01
        exact (mul_eq_zero.mp this).resolve_right htr
      have hc : s 1 0 = 0 := by
        have : s 1 0 * (s 0 0 + s 1 1) = 0 := by linear_combination hs10
        exact (mul_eq_zero.mp this).resolve_right htr
      have ha := mul_self_eq_one_iff.mp (show s 0 0 * s 0 0 = 1 by
        linear_combination hs00 - s 0 1 * hc)
      have hd := mul_self_eq_one_iff.mp (show s 1 1 * s 1 1 = 1 by
        linear_combination hs11 - s 1 0 * hb)
      rcases ha with ha | ha <;> rcases hd with hd | hd
      · exact hs1 (by ext i j; fin_cases i <;> fin_cases j <;> simp [ha, hb, hc, hd])
      · exact htr (by rw [ha, hd]; ring)
      · exact htr (by rw [ha, hd]; ring)
      · exact hsn (by ext i j; fin_cases i <;> fin_cases j <;> simp [ha, hb, hc, hd])
    rw [htr, mul_zero, neg_zero] at h3a
    exact pow_eq_zero_iff (n := 3) (by norm_num) |>.mp
      ((mul_eq_zero.mp h3a).resolve_left h2)
  have hl : l = 0 := by
    by_contra hl0
    have hl3 : l ^ 3 ≠ 0 := pow_ne_zero 3 hl0
    rw [hα] at e00
    have ha : s 0 0 = 0 := by
      have : l ^ 3 * s 0 0 = 0 := by linear_combination -e00
      exact (mul_eq_zero.mp this).resolve_left hl3
    have hb : s 0 1 = 0 := e01.resolve_left hl0
    rw [ha, hb] at hs00
    simp at hs00
  rw [hNeq, hα, hl, zero_smul, zero_smul, add_zero]

theorem eq_one_of_commute_fourGroup {K : Type*} [Field K] [CharP K 3] {a b u : GL (Fin 3) K}
    (ha : a * a = 1) (hb : b * b = 1) (hab : a * b = b * a) (ha1 : a ≠ 1) (hb1 : b ≠ 1)
    (hba : b ≠ a) (hda : (a : Matrix (Fin 3) (Fin 3) K).det = 1)
    (hdb : (b : Matrix (Fin 3) (Fin 3) K).det = 1) (hdu : (u : Matrix (Fin 3) (Fin 3) K).det = 1)
    (hua : u * a = a * u) (hub : u * b = b * u) (hu3 : u ^ 3 = 1) : u = 1 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h2 : (2 : K) ≠ 0 := two_ne_zero_of_charThree
  set X : Subgroup (GL (Fin 3) K) := Subgroup.closure {a, b, u} with hXdef
  have haX : a ∈ X := Subgroup.subset_closure (by simp)
  have hbX : b ∈ X := Subgroup.subset_closure (by simp)
  have huX : u ∈ X := Subgroup.subset_closure (by simp)
  have hX : ∀ x ∈ X, x * a = a * x := by
    have hle : X ≤ Subgroup.centralizer {a} := by
      rw [hXdef, Subgroup.closure_le]
      intro g hg
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
      rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
      rcases hg with rfl | rfl | rfl
      · rfl
      · exact hab.symm
      · exact hua
    intro x hx
    exact Subgroup.mem_centralizer_singleton_iff.mp (hle hx)
  have hXdet : ∀ x ∈ X, (x : Matrix (Fin 3) (Fin 3) K).det = 1 := by
    have hle : X ≤ (Matrix.GeneralLinearGroup.det : GL (Fin 3) K →* Kˣ).ker := by
      rw [hXdef, Subgroup.closure_le]
      intro g hg
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
      rw [SetLike.mem_coe, MonoidHom.mem_ker]
      rcases hg with rfl | rfl | rfl <;> apply Units.ext <;>
        simp [Matrix.GeneralLinearGroup.val_det_apply, hda, hdb, hdu]
    intro x hx
    have := congrArg Units.val (MonoidHom.mem_ker.mp (hle hx))
    rwa [Matrix.GeneralLinearGroup.val_det_apply] at this
  obtain ⟨ρ, hρ, hρa⟩ := SubgroupLists.exists_injective_gl2_of_commute h2 ha ha1 hda X hX hXdet
  set S : GL (Fin 2) K := ρ ⟨b, hbX⟩
  set U : GL (Fin 2) K := ρ ⟨u, huX⟩
  have hρa' : ρ ⟨a, haX⟩ = -1 := hρa ⟨a, haX⟩ rfl
  have hSS : (S : Matrix (Fin 2) (Fin 2) K) * S = 1 := by
    rw [← Units.val_mul, ← map_mul]
    have : (⟨b, hbX⟩ : X) * ⟨b, hbX⟩ = 1 := Subtype.ext hb
    rw [this, map_one, Units.val_one]
  have hS1 : (S : Matrix (Fin 2) (Fin 2) K) ≠ 1 := by
    intro h
    have h' : S = 1 := Units.ext h
    rw [← map_one ρ] at h'
    exact hb1 (congrArg Subtype.val (hρ h'))
  have hSn : (S : Matrix (Fin 2) (Fin 2) K) ≠ -1 := by
    intro h
    have h' : S = -1 := Units.ext (by rw [h, Units.val_neg, Units.val_one])
    rw [← hρa'] at h'
    exact hba (congrArg Subtype.val (hρ h'))
  have hUS : (U : Matrix (Fin 2) (Fin 2) K) * S = S * U := by
    rw [← Units.val_mul, ← Units.val_mul, ← map_mul, ← map_mul]
    congr 2
    exact Subtype.ext hub
  have hU3 : (U : Matrix (Fin 2) (Fin 2) K) ^ 3 = 1 := by
    rw [← Units.val_pow_eq_pow_val, ← map_pow]
    have : (⟨u, huX⟩ : X) ^ 3 = 1 := Subtype.ext hu3
    rw [this, map_one, Units.val_one]
  have hN := eq_zero_of_commute_involution_two hSS hS1 hSn
    (N := (U : Matrix (Fin 2) (Fin 2) K) - 1)
    (by rw [sub_mul, mul_sub, hUS, one_mul, mul_one])
    (by rw [sub_pow_char_of_commute 3 (Commute.one_right _), one_pow, hU3, sub_self])
  have hU1 : U = 1 := Units.ext (sub_eq_zero.mp hN)
  rw [← map_one ρ] at hU1
  exact congrArg Subtype.val (hρ hU1)

theorem eq_one_of_mk_eq_one {K : Type*} [Field K] [CharP K 3] {A : GL (Fin 3) K}
    (hdet : (A : Matrix (Fin 3) (Fin 3) K).det = 1) (h : Matrix.ProjGenLinGroup.mk A = 1) :
    A = 1 := by
  rw [Matrix.ProjGenLinGroup.mk_eq_one, Matrix.GeneralLinearGroup.center_eq_range_scalar] at h
  obtain ⟨l, rfl⟩ := h
  have hl3 : l ^ 3 = 1 := by
    have h1 := Matrix.GeneralLinearGroup.det_scalar (n := Fin 3) l
    rw [Fintype.card_fin] at h1
    rw [← h1]
    exact Units.ext (by rw [Matrix.GeneralLinearGroup.val_det_apply, hdet, Units.val_one])
  have hl1 : l = 1 := Units.ext (eq_one_of_pow_three_eq_one (by
    rw [← Units.val_pow_eq_pow_val, hl3, Units.val_one]))
  rw [hl1, map_one]

abbrev su39Gens : Set (GL (Fin 3) (GaloisField 3 (2 * 2))) :=
  {A : GL (Fin 3) (GaloisField 3 (2 * 2)) | Matrix.GeneralLinearGroup.det A = 1 ∧
    ((A : Matrix (Fin 3) (Fin 3) (GaloisField 3 (2 * 2))).map (· ^ (3 ^ 2)))ᵀ *
      (A : Matrix (Fin 3) (Fin 3) (GaloisField 3 (2 * 2))) = 1}

noncomputable def su39Equiv : Subgroup.closure su39Gens ≃* projSU 3 3 2 :=
  (MonoidHom.ofInjective (f := (Matrix.ProjGenLinGroup.mk : GL (Fin 3) (GaloisField 3 (2 * 2)) →*
      Matrix.ProjGenLinGroup (Fin 3) (GaloisField 3 (2 * 2))).comp
      (Subgroup.closure su39Gens).subtype) (by
    rw [injective_iff_map_eq_one]
    intro A hA
    exact Subtype.ext (eq_one_of_mk_eq_one (Sec4.det_of_mem_closure_su _ A.2) hA))).trans
    (MulEquiv.subgroupCongr (by
      rw [MonoidHom.range_comp, Subgroup.range_subtype]
      rfl))

theorem not_prime_card_projSU_three_three_two : ¬ (Nat.card (projSU 3 3 2)).Prime := by
  have h := KFacts.KS14.card_projSU_three_mul_gcd 3 2 (by norm_num)
  norm_num at h
  rw [h]
  norm_num

theorem finite_projSU_three_three_two : Finite (projSU 3 3 2) := by
  have h := KFacts.KS14.card_projSU_three_mul_gcd 3 2 (by norm_num)
  norm_num at h
  exact Nat.finite_of_card_ne_zero (by rw [h]; norm_num)

theorem noL2Normal228_projSU_three_three_two : NoL2Normal228 (projSU 3 3 2) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  intro y N Kb m hyZ hy3 hcomm _ hKbN ⟨eK⟩ hm he _
  have : IsSimpleGroup (projSU 3 3 2) :=
    Sec19.Step1914TriProof.isSimpleGroup_projSU_three_of_ne_two 3 2 (by norm_num) (by norm_num)
  have hZ : Subgroup.center (projSU 3 3 2) = ⊥ :=
    Item223CensusProof.center_eq_bot_of_isSimpleGroup not_prime_card_projSU_three_three_two
  rw [hZ, Subgroup.mem_bot] at hyZ hy3
  have : Finite (projSU 3 3 2) := finite_projSU_three_three_two
  have hm2 : 2 ≤ m := by
    obtain ⟨r, hr⟩ := he
    omega
  obtain ⟨E, hEK, hE, hE4⟩ := Commute33Steps.exists_fourGroup_of_mulEquiv_projSL hm2 eK
  have hne : E ≠ ⊥ := fun h => by
    rw [h, Subgroup.card_bot] at hE4
    omega
  obtain ⟨⟨a, haE⟩, ha1'⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
  have ha1 : a ≠ 1 := fun h => ha1' (Subtype.ext h)
  obtain ⟨b, hbE, hba⟩ : ∃ b ∈ E, b ∉ Subgroup.zpowers a := by
    by_contra h
    push Not at h
    have hle := Subgroup.card_le_of_le (show E ≤ Subgroup.zpowers a from h)
    rw [hE4, Nat.card_zpowers, orderOf_eq_prime (hE.2 a haE) ha1] at hle
    omega
  have hb1 : b ≠ 1 := fun h => hba (h ▸ Subgroup.one_mem _)
  have hba' : b ≠ a := fun h => hba (h ▸ Subgroup.mem_zpowers a)
  have hab : a * b = b * a := by
    have := hE.1.is_comm.comm (⟨a, haE⟩ : E) ⟨b, hbE⟩
    exact congrArg Subtype.val this
  have hya : y * a = a * y := hcomm a (hKbN (hEK haE))
  have hyb : y * b = b * y := hcomm b (hKbN (hEK hbE))
  set A : Subgroup.closure su39Gens := su39Equiv.symm a with hAdef
  set B : Subgroup.closure su39Gens := su39Equiv.symm b with hBdef
  set U : Subgroup.closure su39Gens := su39Equiv.symm y with hUdef
  have hAA : A * A = 1 := by rw [hAdef, ← map_mul, ← pow_two a, hE.2 a haE, map_one]
  have hBB : B * B = 1 := by rw [hBdef, ← map_mul, ← pow_two b, hE.2 b hbE, map_one]
  have hAB : A * B = B * A := by rw [hAdef, hBdef, ← map_mul, ← map_mul, hab]
  have hUA : U * A = A * U := by rw [hAdef, hUdef, ← map_mul, ← map_mul, hya]
  have hUB : U * B = B * U := by rw [hBdef, hUdef, ← map_mul, ← map_mul, hyb]
  have hU3 : U ^ 3 = 1 := by rw [hUdef, ← map_pow, hy3, map_one]
  have hA1 : A ≠ 1 := fun h => ha1 (su39Equiv.symm.injective (h.trans (map_one _).symm))
  have hB1 : B ≠ 1 := fun h => hb1 (su39Equiv.symm.injective (h.trans (map_one _).symm))
  have hBA : B ≠ A := fun h => hba' (su39Equiv.symm.injective h)
  have hdet : ∀ g : Subgroup.closure su39Gens,
      ((g : GL (Fin 3) (GaloisField 3 (2 * 2))) :
        Matrix (Fin 3) (Fin 3) (GaloisField 3 (2 * 2))).det = 1 :=
    fun g => Sec4.det_of_mem_closure_su _ g.2
  have key := eq_one_of_commute_fourGroup (K := GaloisField 3 (2 * 2))
    (a := (A : GL (Fin 3) (GaloisField 3 (2 * 2))))
    (b := (B : GL (Fin 3) (GaloisField 3 (2 * 2))))
    (u := (U : GL (Fin 3) (GaloisField 3 (2 * 2))))
    (by rw [← Subgroup.coe_mul, hAA, Subgroup.coe_one])
    (by rw [← Subgroup.coe_mul, hBB, Subgroup.coe_one])
    (by rw [← Subgroup.coe_mul, ← Subgroup.coe_mul, hAB])
    (fun h => hA1 (Subtype.ext h)) (fun h => hB1 (Subtype.ext h))
    (fun h => hBA (Subtype.ext h)) (hdet A) (hdet B) (hdet U)
    (by rw [← Subgroup.coe_mul, ← Subgroup.coe_mul, hUA])
    (by rw [← Subgroup.coe_mul, ← Subgroup.coe_mul, hUB])
    (by rw [← Subgroup.coe_pow, hU3, Subgroup.coe_one])
  have hU1 : U = 1 := Subtype.ext key
  exact hyZ (su39Equiv.symm.injective (hU1.trans (map_one _).symm))

theorem noL2Normal228_of_mulEquiv {Y S : Type} [Group Y] [Group S] (e : Y ≃* S)
    (hS : NoL2Normal228 S) : NoL2Normal228 Y := by
  intro y N Kb m hyZ hy3 hcomm hnorm hKbN ⟨eK⟩ hm he hU
  have hZ := Sec4.map_center_mulEquiv e
  have hmemZ : ∀ z : Y, e z ∈ Subgroup.center S ↔ z ∈ Subgroup.center Y := fun z => by
    rw [← hZ]
    exact ⟨fun ⟨w, hw, hwz⟩ => (e.injective hwz) ▸ hw, fun hz => ⟨z, hz, rfl⟩⟩
  refine hS (e y) (N.map e.toMonoidHom) (Kb.map e.toMonoidHom) m
    (fun h1 => hyZ ((hmemZ y).mp h1))
    (by rw [← map_pow]; exact (hmemZ _).mpr hy3) ?_ ?_
    (Subgroup.map_mono hKbN)
    ⟨(Kb.equivMapOfInjective e.toMonoidHom e.injective).symm.trans eK⟩ hm he ?_
  · rintro _ ⟨k, hk, rfl⟩
    change e y * e k = e k * e y
    rw [← map_mul, ← map_mul, hcomm k hk]
  · rintro g hg _ ⟨k, hk, rfl⟩
    obtain ⟨g', rfl⟩ := e.surjective g
    have hg' : g' * y = y * g' := e.injective (by rw [map_mul, map_mul]; exact hg)
    refine ⟨g' * k * g'⁻¹, hnorm g' hg' k hk, ?_⟩
    change e (g' * k * g'⁻¹) = e g' * e k * (e g')⁻¹
    rw [map_mul, map_mul, map_inv]
  · rcases hU with heq | hU
    · exact Or.inl (by rw [heq])
    · exact Or.inr (CFSG.SectionRank.statedClassicalModel_of_mulEquiv
        (N.equivMapOfInjective e.toMonoidHom e.injective).symm hU)

theorem noL2Normal228_of_no15 {S : Type} [Group S] [Finite S] [IsSimpleGroup S]
    (hnp : ¬ (Nat.card S).Prime) (h15 : ∀ g : S, orderOf g ≠ 15) : NoL2Normal228 S := by
  have hZ := Item223CensusProof.center_eq_bot_of_isSimpleGroup hnp
  refine Item22Res4Proof.noL2Normal228_of_hom (MonoidHom.id S)
    (by rw [MonoidHom.ker_id, hZ]) ?_
    fun x hx => Item22Res4Proof.not_five_dvd_centralizer_of_no15 h15 hx
  rw [hZ, Subgroup.card_bot]
  norm_num

theorem not_prime_card_projSL_three_nine : ¬ (Nat.card (projSL 3 (GaloisField 3 2))).Prime := by
  have h := KFacts.KS14.card_projSL_three_mul_gcd (GaloisField 3 2)
  rw [GaloisField.card 3 2 (by norm_num)] at h
  norm_num at h
  rw [h]
  norm_num

theorem isSimpleGroup_projSL_four_three : IsSimpleGroup (projSL 4 (GaloisField 3 1)) :=
  CFSG.PGLModel.isSimpleGroup_projSL_of_two_le _ (by norm_num) (Or.inl (by norm_num)) (Or.inl (by norm_num))

theorem finite_projSL_three_nine : Finite (projSL 3 (GaloisField 3 2)) := by
  have h := KFacts.KS14.card_projSL_three_mul_gcd (GaloisField 3 2)
  rw [GaloisField.card 3 2 (by norm_num)] at h
  norm_num at h
  exact Nat.finite_of_card_ne_zero (by rw [h]; norm_num)

theorem finite_projSL_four_three : Finite (projSL 4 (GaloisField 3 1)) := by
  have h := Sec11.KSListsProof.card_projSL_four_mul (GaloisField 3 1)
  rw [GaloisField.card 3 1 (by norm_num)] at h
  norm_num at h
  exact Nat.finite_of_card_ne_zero (by omega)

theorem not_prime_card_projSL_four_three : ¬ (Nat.card (projSL 4 (GaloisField 3 1))).Prime := by
  have h := Sec11.KSListsProof.card_projSL_four_mul (GaloisField 3 1)
  rw [GaloisField.card 3 1 (by norm_num)] at h
  norm_num at h
  have h' : Nat.card (projSL 4 (GaloisField 3 1)) = 6065280 := by omega
  rw [h']
  norm_num

end Item228CensusProof

open Item228CensusProof

theorem census228CharThreeLin_holds : Census228CharThreeLin := by
  intro Y _ _ hY
  right
  rcases hY with h1 | h2 | h3
  · obtain ⟨e⟩ := h1
    have : IsSimpleGroup (projSL 3 (GaloisField 3 2)) :=
      Sec19.Step1914TriProof.isSimpleGroup_projSL_three_of_field _
    have : Finite (projSL 3 (GaloisField 3 2)) := finite_projSL_three_nine
    exact noL2Normal228_of_mulEquiv e (noL2Normal228_of_no15 not_prime_card_projSL_three_nine
      orderOf_ne_fifteen_projSL_three_nine)
  · obtain ⟨e⟩ := h2
    exact noL2Normal228_of_mulEquiv e noL2Normal228_projSU_three_three_two
  · obtain ⟨e⟩ := h3
    have : IsSimpleGroup (projSL 4 (GaloisField 3 1)) := isSimpleGroup_projSL_four_three
    have : Finite (projSL 4 (GaloisField 3 1)) := finite_projSL_four_three
    exact noL2Normal228_of_mulEquiv e (noL2Normal228_of_no15 not_prime_card_projSL_four_three
      orderOf_ne_fifteen_projSL_four_three)

end CFSG.RankThree.PartTwo.Sec21
