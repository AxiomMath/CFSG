module

public import CFSG.RankThree.PartTwo.Census.Carrier.Sp6TwoCert
public import CFSG.RankThree.PartTwo.Census.Carrier.G2Three
public import CFSG.RankThree.PartTwo.Census.Carrier.SpinBBridge
public import CFSG.RankThree.PartTwo.Census.OddClassical.UnitaryFourThree
public import CFSG.RankThree.PartTwo.Census.Criteria
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeylMatrices
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticFlagOrder
import CFSG.Adapters.LinearFieldTransport
import CFSG.Adapters.RankTwoModelTransports
import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import Certificates.Certificate8151
public import CFSG.Foundations
public import CFSG.GroupTheory.HallHigmanPiCore
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.LocalAnalysis.SectionRank.SQT
public import CFSG.RankThree.PartTwo.Sec4.Census.Interface
public import TauCeti.GroupTheory.SpecificGroups.CFSG.TypeC.Agreement

public noncomputable section

namespace CFSG.RankThree.PartTwo.Census.Carrier.Sp6Two

open CFSG.Assembly CFSG.Assembly.RankThreeEven CFSG.Assembly.LowTwoRank CFSG.Quasithin.G2U

section Abstract

variable {H : Type} [Group H] [Finite H]

theorem exists_conj_of_sylow_classes {k : ℕ} {t : Fin k → H} {S : Subgroup H}
    (hS2 : IsPGroup 2 S) (hSi : ¬ 2 ∣ S.index)
    (hSinv : ∀ u ∈ S, orderOf u = 2 → ∃ i g, u = g * t i * g⁻¹) {s : H}
    (hs : orderOf s = 2) : ∃ i g, s = g * t i * g⁻¹ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hz : IsPGroup 2 (Subgroup.zpowers s) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hs, pow_one])
  obtain ⟨Q, hQ⟩ := hz.exists_le_sylow
  let SS : Sylow 2 H := hS2.toSylow hSi
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq H SS Q
  have hQeq : (Q : Subgroup H) = S.map (MulAut.conj g).toMonoidHom := by
    have h1 : ((g • SS : Sylow 2 H) : Subgroup H) = (Q : Subgroup H) := by rw [hg]
    rw [Sylow.coe_subgroup_smul, IsPGroup.toSylow_coe] at h1
    exact h1.symm
  have hsQ : s ∈ (Q : Subgroup H) := hQ (Subgroup.mem_zpowers s)
  rw [hQeq] at hsQ
  obtain ⟨u, huS, rfl⟩ := hsQ
  have hu2 : orderOf u = 2 := by
    rw [← hs]
    exact (orderOf_injective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective u).symm
  obtain ⟨i, g', hg'⟩ := hSinv u huS hu2
  refine ⟨i, g * g', ?_⟩
  rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, hg']
  group

theorem exists_conj_of_card_nine_of_not_dvd {X P P₁ : Subgroup H} (hX : ¬ 27 ∣ Nat.card X)
    (hPX : P ≤ X) (hP : Nat.card P = 9) (hP₁X : P₁ ≤ X) (hP₁ : Nat.card P₁ = 9) :
    ∃ y ∈ X, ∀ p ∈ P, y * p * y⁻¹ ∈ P₁ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hsyl : ∀ P' : Subgroup H, P' ≤ X → Nat.card P' = 9 →
      IsPGroup 3 (P'.subgroupOf X) ∧ ¬ 3 ∣ (P'.subgroupOf X).index := by
    intro P' hP' hc
    have hc' : Nat.card (P'.subgroupOf X) = 9 := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hP').toEquiv, hc]
    refine ⟨IsPGroup.of_card (n := 2) (hc'.trans (by norm_num)), fun h3 => hX ?_⟩
    have h := Subgroup.card_mul_index (P'.subgroupOf X)
    rw [hc'] at h
    rw [← h]
    exact mul_dvd_mul_left 9 h3
  obtain ⟨h1a, h1b⟩ := hsyl P₁ hP₁X hP₁
  obtain ⟨h9a, h9b⟩ := hsyl P hPX hP
  obtain ⟨x, hx⟩ := MulAction.exists_smul_eq X (h9a.toSylow h9b) (h1a.toSylow h1b)
  have hPeq : P₁.subgroupOf X = (P.subgroupOf X).map (MulAut.conj x).toMonoidHom := by
    have h1 : ((x • h9a.toSylow h9b : Sylow 3 X) : Subgroup X) =
        (h1a.toSylow h1b : Subgroup X) := by rw [hx]
    rw [Sylow.coe_subgroup_smul, IsPGroup.toSylow_coe, IsPGroup.toSylow_coe] at h1
    exact h1.symm
  refine ⟨x, x.2, fun p hp => ?_⟩
  have hmem : (MulAut.conj x).toMonoidHom ⟨p, hPX hp⟩ ∈ P₁.subgroupOf X := by
    rw [hPeq]
    exact Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hp)
  exact Subgroup.mem_subgroupOf.mp hmem

theorem localRank_three_le_two_of_classes {k : ℕ} (t : Fin k → H) (X P : Fin k → Subgroup H)
    (o : Fin k → ℕ) (hcard : ∀ i, o i * Nat.card (X i) = Nat.card H)
    (hXt : ∀ i, X i ≤ Subgroup.centralizer {t i}) (f : ∀ i, Fin (o i) → H)
    (hf : ∀ i, Function.Injective (f i)) (hft : ∀ i j, ∃ g, f i j = g * t i * g⁻¹)
    {S : Subgroup H} (hS2 : IsPGroup 2 S) (hSi : ¬ 2 ∣ S.index)
    (hSinv : ∀ u ∈ S, orderOf u = 2 → ∃ i g, u = g * t i * g⁻¹)
    (h27 : ∀ i, ¬ 27 ∣ Nat.card (X i))
    (hPX : ∀ i, 9 ∣ Nat.card (X i) → P i ≤ Subgroup.centralizer {t i})
    (hP : ∀ i, 9 ∣ Nat.card (X i) → Nat.card (P i) = 9)
    (hPc : ∀ i, 9 ∣ Nat.card (X i) → ∀ q ∈ X i, (∀ p ∈ P i, q * p = p * q) →
      (∃ m, q ^ 2 ^ m = 1) → q = 1 ∨ q = t i) :
    localRank 3 H ≤ 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hCX : ∀ i, Subgroup.centralizer {t i} = X i := by
    intro i
    refine (Subgroup.eq_of_le_of_card_ge (hXt i) ?_).symm
    have h := G2Three.card_centralizer_mul_le (f i) (hf i) (hft i)
    rw [← hcard i] at h
    have ho : 0 < o i := by
      rcases Nat.eq_zero_or_pos (o i) with h0 | h0
      · have := hcard i
        rw [h0, zero_mul] at this
        exact absurd this.symm Nat.card_pos.ne'
      · exact h0
    rw [mul_comm (o i)] at h
    exact Nat.le_of_mul_le_mul_right h ho
  have hconj := fun s (hs : orderOf s = 2) => exists_conj_of_sylow_classes hS2 hSi hSinv hs
  refine UnitaryFourThree.localRank_three_le_two_of (fun s hs R hR h27' => ?_)
    (fun K hK Q hQ hQK => ?_)
  · obtain ⟨i, g, rfl⟩ := hconj s hs
    have h1 := G2Three.map_conj_le_centralizer hR
    have h2 : Nat.card (R.map (MulAut.conj g⁻¹).toMonoidHom) = Nat.card R :=
      Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective
    have h3 := Subgroup.card_dvd_of_le h1
    rw [h2, hCX i] at h3
    exact h27 i (h27'.trans h3)
  · by_cases hQ1 : Q = ⊥
    · rw [hQ1, Subgroup.card_bot]
      omega
    have : Nontrivial Q := (Subgroup.nontrivial_iff_ne_bot Q).mpr hQ1
    have hZ2 : 2 ∣ Nat.card (Subgroup.center Q) := by
      have hZp : IsPGroup 2 (Subgroup.center Q) := hQ.to_subgroup _
      have := hQ.center_nontrivial
      obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hZp
      rcases k with _ | k
      · rw [pow_zero] at hk
        exact absurd hk Finite.one_lt_card.ne'
      · rw [hk, pow_succ]
        exact dvd_mul_left 2 _
    obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' 2 hZ2
    set s : H := (((z : Subgroup.center Q) : Q) : H)
    have hsQ : s ∈ Q := ((z : Subgroup.center Q) : Q).2
    have hs2 : orderOf s = 2 := by
      rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe, hz]
    have hsc : ∀ q ∈ Q, q * s = s * q := fun q hq =>
      congrArg Subtype.val (Subgroup.mem_center_iff.mp z.2 ⟨q, hq⟩)
    obtain ⟨i, g, hg⟩ := hconj s hs2
    set c : H →* H := (MulAut.conj g⁻¹).toMonoidHom with hc_def
    have hcinj : Function.Injective c := (MulAut.conj g⁻¹).injective
    have hcs : c s = t i := by
      rw [hg, hc_def, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
    have hQ₁X : Q.map c ≤ X i := by
      rw [← hCX i]
      rintro _ ⟨q, hq, rfl⟩
      rw [Subgroup.mem_centralizer_singleton_iff, ← hcs, ← map_mul, ← map_mul, hsc q hq]
    have hK₁X : K.map c ≤ X i := by
      rw [← hCX i]
      rintro _ ⟨k, hk, rfl⟩
      rw [Subgroup.mem_centralizer_singleton_iff, ← hcs, ← map_mul, ← map_mul]
      exact congrArg c (Subgroup.mem_centralizer_iff.mp (hQK hsQ) k hk)
    have hQ₁K₁ : ∀ q ∈ Q.map c, ∀ k ∈ K.map c, q * k = k * q := by
      rintro _ ⟨q, hq, rfl⟩ _ ⟨k, hk, rfl⟩
      rw [← map_mul, ← map_mul, (Subgroup.mem_centralizer_iff.mp (hQK hq) k hk)]
    have hK₁ : Nat.card (K.map c) = Nat.card K := Subgroup.card_map_of_injective hcinj
    have h9X : 9 ∣ Nat.card (X i) := by
      have := Subgroup.card_dvd_of_le hK₁X
      rw [hK₁] at this
      exact hK.trans this
    obtain ⟨P₁', hP₁'⟩ := Sylow.exists_subgroup_card_pow_prime (G := K.map c) 3 (n := 2)
      (by rw [hK₁]; exact hK)
    have hP₁K : P₁'.map (K.map c).subtype ≤ K.map c := Subgroup.map_subtype_le _
    have hcardP₁ : Nat.card (P₁'.map (K.map c).subtype) = 9 := by
      rw [Subgroup.card_map_of_injective (K.map c).subtype_injective, hP₁']
      norm_num
    obtain ⟨y, hyX, hy⟩ := exists_conj_of_card_nine_of_not_dvd (h27 i)
      ((hPX i h9X).trans (hCX i).le) (hP i h9X) (hP₁K.trans hK₁X) hcardP₁
    have hQ2 : ∀ q ∈ (Q.map c).map (MulAut.conj y⁻¹).toMonoidHom, q = 1 ∨ q = t i := by
      rintro _ ⟨q, hq, rfl⟩
      rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
      have hqX : y⁻¹ * q * y ∈ X i := mul_mem (mul_mem (inv_mem hyX) (hQ₁X hq)) hyX
      have hcomm : ∀ p ∈ P i, (y⁻¹ * q * y) * p = p * (y⁻¹ * q * y) := by
        intro p hp
        have h := hQ₁K₁ q hq _ (hP₁K (hy p hp))
        calc (y⁻¹ * q * y) * p = y⁻¹ * (q * (y * p * y⁻¹)) * y := by group
          _ = y⁻¹ * ((y * p * y⁻¹) * q) * y := by rw [h]
          _ = p * (y⁻¹ * q * y) := by group
      obtain ⟨q₀, hq₀, rfl⟩ := hq
      obtain ⟨k, hk⟩ := hQ ⟨q₀, hq₀⟩
      have hk₀ : q₀ ^ 2 ^ k = 1 := congrArg Subtype.val hk
      have hk' : (y⁻¹ * c q₀ * y) ^ 2 ^ k = 1 := by
        have e := map_pow (MulAut.conj y⁻¹) (c q₀) (2 ^ k)
        rw [MulAut.conj_apply, inv_inv, MulAut.conj_apply, inv_inv] at e
        rw [← e, ← map_pow, hk₀, map_one, mul_one, inv_mul_cancel]
      exact hPc i h9X _ hqX hcomm ⟨k, hk'⟩
    have hle := G2Three.card_le_two_of_forall hQ2
    rwa [Subgroup.card_map_of_injective (MulAut.conj y⁻¹).injective,
      Subgroup.card_map_of_injective hcinj] at hle

end Abstract

abbrev H6 : Type :=
  ↥(StatedSp 3 (ZMod 2))

abbrev ε6 : Fin 6 ≃ Fin 3 ⊕ Fin 3 :=
  (finSumFinEquiv (m := 3) (n := 3)).symm

@[expose] def mat6 : H6 →* Matrix (Fin 6) (Fin 6) (ZMod 2) where
  toFun g := ((g : GL (Fin 3 ⊕ Fin 3) (ZMod 2)) :
    Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) (ZMod 2)).submatrix ε6 ε6
  map_one' := by
    simp only [OneMemClass.coe_one, Units.val_one]
    exact Matrix.submatrix_one_equiv ε6
  map_mul' g h := by
    simp only [Subgroup.coe_mul, Units.val_mul]
    exact (Matrix.submatrix_mul_equiv _ _ _ ε6 _).symm

theorem mat6_apply (g : H6) : mat6 g = ((g : GL (Fin 3 ⊕ Fin 3) (ZMod 2)) :
    Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) (ZMod 2)).submatrix ε6 ε6 :=
  rfl

theorem submatrix_ε6_symm {α : Type*} (M : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) α) :
    (M.submatrix ε6 ε6).submatrix ε6.symm ε6.symm = M := by
  rw [Matrix.submatrix_submatrix, Equiv.self_comp_symm, Matrix.submatrix_id_id]

theorem mat6_injective : Function.Injective mat6 := by
  intro g h e
  apply Subtype.ext
  apply Units.ext
  rw [← submatrix_ε6_symm ((g : GL (Fin 3 ⊕ Fin 3) (ZMod 2)) : Matrix _ _ (ZMod 2)),
    ← submatrix_ε6_symm ((h : GL (Fin 3 ⊕ Fin 3) (ZMod 2)) : Matrix _ _ (ZMod 2))]
  exact congrArg (fun M => Matrix.submatrix M ε6.symm ε6.symm) e

theorem dec6_j6C : dec6 j6C = (Matrix.fromBlocks 0 1 (-1) 0 :
    Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) (ZMod 2)).submatrix ε6 ε6 := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem pairCheck_spec {cc : List ℕ × List ℕ} (h : pairCheck cc = true) :
    canon6 cc.1 = true ∧ dec6 cc.1 * dec6 cc.2 = 1 ∧ dec6 cc.2 * dec6 cc.1 = 1 ∧
      (dec6 cc.1).transpose * dec6 j6C * dec6 cc.1 = dec6 j6C := by
  simp only [pairCheck, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨h1, -⟩, h3⟩, h4⟩, h5⟩ := h
  refine ⟨h1, ?_, ?_, ?_⟩
  · rw [← dec6_mul6, h3, dec6_one6]
  · rw [← dec6_mul6, h4, dec6_one6]
  · rw [← dec6_tr6, ← dec6_mul6, ← dec6_mul6, h5]

@[expose] def ofCode (cc : List ℕ × List ℕ) (h : pairCheck cc = true) : H6 :=
  ⟨⟨(dec6 cc.1).submatrix ε6.symm ε6.symm, (dec6 cc.2).submatrix ε6.symm ε6.symm, by
      rw [Matrix.submatrix_mul_equiv, (pairCheck_spec h).2.1, Matrix.submatrix_one_equiv], by
      rw [Matrix.submatrix_mul_equiv, (pairCheck_spec h).2.2.1, Matrix.submatrix_one_equiv]⟩, by
    rw [CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl.mem_statedSp_iff]
    have h5 := (pairCheck_spec h).2.2.2
    rw [dec6_j6C] at h5
    have key : ((dec6 cc.1).transpose * (Matrix.fromBlocks 0 1 (-1) 0 :
        Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) (ZMod 2)).submatrix ε6 ε6 *
          dec6 cc.1).submatrix ε6.symm ε6.symm = Matrix.fromBlocks 0 1 (-1) 0 := by
      rw [h5, submatrix_ε6_symm]
    rw [← Matrix.submatrix_mul_equiv _ _ _ ε6.symm _,
      ← Matrix.submatrix_mul_equiv _ _ _ ε6.symm _, submatrix_ε6_symm,
      ← Matrix.transpose_submatrix] at key
    exact key⟩

theorem mat6_ofCode (cc : List ℕ × List ℕ) (h : pairCheck cc = true) :
    mat6 (ofCode cc h) = dec6 cc.1 := by
  rw [mat6_apply]
  show ((dec6 cc.1).submatrix ε6.symm ε6.symm).submatrix ε6 ε6 = dec6 cc.1
  rw [Matrix.submatrix_submatrix, Equiv.symm_comp_self, Matrix.submatrix_id_id]

theorem mat6_ofCode_inv (cc : List ℕ × List ℕ) (h : pairCheck cc = true) :
    mat6 (ofCode cc h)⁻¹ = dec6 cc.2 := by
  rw [mat6_apply]
  show ((dec6 cc.2).submatrix ε6.symm ε6.symm).submatrix ε6 ε6 = dec6 cc.2
  rw [Matrix.submatrix_submatrix, Equiv.symm_comp_self, Matrix.submatrix_id_id]

theorem card_H6 : Nat.card H6 = 1451520 := by
  rw [CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.card_statedSp, Nat.card_zmod]
  decide

theorem cert_parts : pairsOK = true ∧ invsOK = true ∧ commOK = true ∧ orbitsOK = true ∧
    centsOK = true ∧ psOK = true ∧ sylowOK = true ∧ twoOK = true := by
  have h := cert
  simp only [certAll, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩

theorem pairs_parts : genP.all pairCheck = true ∧ tP.all pairCheck = true ∧
    cent0P.all pairCheck = true ∧ cent1P.all pairCheck = true ∧
    cent2P.all pairCheck = true ∧ cent3P.all pairCheck = true ∧ p0P.all pairCheck = true ∧
    p1P.all pairCheck = true ∧ sylowP.all pairCheck = true := by
  have h := cert_parts.1
  simp only [pairsOK, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩

@[expose] def genSet (l : List (List ℕ × List ℕ)) (h : l.all pairCheck = true) : Set H6 :=
  {g | ∃ cc, ∃ hm : cc ∈ l, g = ofCode cc (List.all_eq_true.mp h cc hm)}

theorem image_genSet (l : List (List ℕ × List ℕ)) (h : l.all pairCheck = true) :
    mat6 '' genSet l h = {y | ∃ c ∈ l.map Prod.fst, dec6 c = y} := by
  ext y
  constructor
  · rintro ⟨g, ⟨cc, hm, rfl⟩, rfl⟩
    exact ⟨cc.1, List.mem_map_of_mem hm, (mat6_ofCode _ _).symm⟩
  · rintro ⟨c, hc, rfl⟩
    obtain ⟨cc, hm, rfl⟩ := List.mem_map.mp hc
    exact ⟨_, ⟨cc, hm, rfl⟩, mat6_ofCode _ _⟩

theorem ofCode_mem_closure {l : List (List ℕ × List ℕ)} (h : l.all pairCheck = true)
    {cc : List ℕ × List ℕ} (hm : cc ∈ l) :
    ofCode cc (List.all_eq_true.mp h cc hm) ∈ Subgroup.closure (genSet l h) :=
  Subgroup.subset_closure ⟨cc, hm, rfl⟩

theorem card_closure_genSet (l : List (List ℕ × List ℕ)) (h : l.all pairCheck = true) (n : ℕ)
    (hok : closureOK (l.map Prod.fst) (closureT (l.map Prod.fst)) n = true) :
    Nat.card (Subgroup.closure (genSet l h)) = n := by
  simp only [closureOK, Bool.and_eq_true, beq_iff_eq] at hok
  obtain ⟨⟨⟨hsize, hclosed⟩, hdist⟩, hcanon⟩ := hok
  rw [← hsize]
  exact card_closure_eq dec6 one6 mul6 (l.map Prod.fst) mat6 mat6_injective dec6_one6 dec6_mul6
    (genSet l h) (image_genSet l h) _ hclosed hdist
    (fun t ht t' ht' e => dec6_injective (allCheck_spec hcanon ht) (allCheck_spec hcanon ht') e)

theorem exists_code_closure (l : List (List ℕ × List ℕ)) (h : l.all pairCheck = true) (n : ℕ)
    (hok : closureOK (l.map Prod.fst) (closureT (l.map Prod.fst)) n = true) {g : H6}
    (hg : g ∈ Subgroup.closure (genSet l h)) :
    ∃ t < (closureT (l.map Prod.fst)).size,
      dec6 ((closureT (l.map Prod.fst)).getD t []) = mat6 g ∧
        canon6 ((closureT (l.map Prod.fst)).getD t []) = true := by
  simp only [closureOK, Bool.and_eq_true, beq_iff_eq] at hok
  obtain ⟨⟨⟨-, hclosed⟩, -⟩, hcanon⟩ := hok
  have himg := image_closure_eq dec6 one6 mul6 (l.map Prod.fst) mat6 dec6_one6 dec6_mul6
    (genSet l h) (image_genSet l h) _ hclosed
  have hmem : mat6 g ∈ mat6 '' (Subgroup.closure (genSet l h) : Set H6) := ⟨g, hg, rfl⟩
  rw [himg] at hmem
  obtain ⟨t, ht, e⟩ := hmem
  exact ⟨t, ht, e, allCheck_spec hcanon ht⟩


theorem commute_of_commutes6 {g h : H6} {c d : List ℕ} (hg : mat6 g = dec6 c)
    (hh : mat6 h = dec6 d) (hc : commutes6 c d = true) : g * h = h * g := by
  apply mat6_injective
  rw [map_mul, map_mul, hg, hh, ← dec6_mul6, ← dec6_mul6]
  simp only [commutes6, beq_iff_eq] at hc
  rw [hc]

theorem commutes6_of_commute {g h : H6} {c d : List ℕ} (hg : mat6 g = dec6 c)
    (hh : mat6 h = dec6 d) (hc : g * h = h * g) : commutes6 c d = true := by
  simp only [commutes6, beq_iff_eq]
  refine dec6_injective (canon6_mul6 _ _) (canon6_mul6 _ _) ?_
  rw [dec6_mul6, dec6_mul6, ← hg, ← hh, ← map_mul, ← map_mul, hc]

theorem pow512_eq_mul6 (x : List ℕ) : ∃ y, pow512 x = mul6 y y := by
  refine ⟨(List.range 8).foldl (fun y _ => mul6 y y) x, ?_⟩
  rw [pow512, show (9 : ℕ) = 8 + 1 from rfl, List.range_succ, List.foldl_append]
  rfl

theorem dec6_pow512 (x : List ℕ) : dec6 (pow512 x) = dec6 x ^ 512 := by
  have key : ∀ n : ℕ, dec6 ((List.range n).foldl (fun y _ => mul6 y y) x) = dec6 x ^ 2 ^ n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, dec6_mul6, ih,
        ← pow_add, ← two_mul, pow_succ, mul_comm]
  rw [pow512, key]
  norm_num

@[expose] def tPair : Fin 4 → List ℕ × List ℕ :=
  ![(t0C, t0I), (t1C, t1I), (t2C, t2I), (t3C, t3I)]

theorem tPair_check (i : Fin 4) : pairCheck (tPair i) = true := by
  have h := pairs_parts.2.1
  simp only [tP, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true] at h
  fin_cases i
  · exact h.1
  · exact h.2.1
  · exact h.2.2.1
  · exact h.2.2.2

@[expose] def tH (i : Fin 4) : H6 :=
  ofCode (tPair i) (tPair_check i)

@[expose] def centP : Fin 4 → List (List ℕ × List ℕ) :=
  ![cent0P, cent1P, cent2P, cent3P]

theorem centP_check (i : Fin 4) : (centP i).all pairCheck = true := by
  fin_cases i
  · exact pairs_parts.2.2.1
  · exact pairs_parts.2.2.2.1
  · exact pairs_parts.2.2.2.2.1
  · exact pairs_parts.2.2.2.2.2.1

@[expose] def XH (i : Fin 4) : Subgroup H6 :=
  Subgroup.closure (genSet (centP i) (centP_check i))

@[expose] def orbSize : Fin 4 → ℕ :=
  ![63, 315, 945, 3780]

@[expose] def centSize : Fin 4 → ℕ :=
  ![23040, 4608, 1536, 384]

theorem centsOK_parts (i : Fin 4) :
    closureOK ((centP i).map Prod.fst) (closureT ((centP i).map Prod.fst)) (centSize i) =
      true := by
  have h := cert_parts.2.2.2.2.1
  simp only [centsOK, Bool.and_eq_true] at h
  fin_cases i
  · exact h.1.1.1
  · exact h.1.1.2
  · exact h.1.2
  · exact h.2

theorem card_XH (i : Fin 4) : Nat.card (XH i) = centSize i :=
  card_closure_genSet _ _ _ (centsOK_parts i)

theorem commOK_cent (i : Fin 4) : ∀ cc ∈ centP i, commutes6 cc.1 (tPair i).1 = true := by
  have h := cert_parts.2.2.1
  simp only [commOK, Bool.and_eq_true, List.all_eq_true] at h
  fin_cases i
  · exact fun cc hc => h.1.1.1 cc (List.mem_append_left _ hc)
  · exact fun cc hc => h.1.1.2 cc (List.mem_append_left _ hc)
  · exact h.1.2
  · exact h.2

theorem XH_le_centralizer (i : Fin 4) : XH i ≤ Subgroup.centralizer {tH i} := by
  rw [XH, Subgroup.closure_le]
  rintro _ ⟨cc, hm, rfl⟩
  rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
  exact commute_of_commutes6 (mat6_ofCode _ _) (mat6_ofCode _ _) (commOK_cent i cc hm)

@[expose] def orbTab (i : Fin 4) : Array (List ℕ) :=
  orbitT (tPair i).1

theorem orbTab_eq (i : Fin 4) : orbTab i = orbitT (tPair i).1 :=
  rfl

theorem orbitsOK_parts (i : Fin 4) : orbitOK (orbTab i) (orbSize i) = true := by
  have h := cert_parts.2.2.2.1
  simp only [orbitsOK, Bool.and_eq_true] at h
  fin_cases i
  · exact h.1.1.1
  · exact h.1.1.2
  · exact h.1.2
  · exact h.2

theorem gpsH_spec :
    ∀ gp ∈ gpsH, ∃ g : H6, dec6 (gp.take 36) = mat6 g ∧ dec6 (gp.drop 36) = mat6 g⁻¹ := by
  have hg := List.all_eq_true.mp pairs_parts.1
  intro gp hgp
  simp only [gpsH, List.mem_cons, List.not_mem_nil, or_false] at hgp
  rcases hgp with rfl | rfl
  · refine ⟨ofCode (aC, aI) (hg _ (List.mem_cons_self ..)), ?_, ?_⟩
    · rw [List.take_left' (by rfl), mat6_ofCode]
    · rw [List.drop_left' (by rfl), mat6_ofCode_inv]
  · refine ⟨ofCode (bC, bI) (hg _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))), ?_, ?_⟩
    · rw [List.take_left' (by rfl), mat6_ofCode]
    · rw [List.drop_left' (by rfl), mat6_ofCode_inv]

theorem exists_conj_of_orbit (i : Fin 4) {k : ℕ} (hk : k < (orbTab i).size) :
    ∃ g : H6, dec6 ((orbTab i).getD k []) = mat6 (g * tH i * g⁻¹) := by
  have hx : (orbTab i).getD k [] ∈ orbTab i := by
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hk, Option.getD_some]
    exact Array.getElem_mem hk
  rw [orbTab_eq] at hx ⊢
  exact orbitBuild6_spec mat6 (mat6_ofCode _ _).symm gpsH gpsH_spec _ _ hx

noncomputable def orbConj (i : Fin 4) (k : Fin (orbSize i)) : H6 :=
  if hk : (k : ℕ) < (orbTab i).size then (exists_conj_of_orbit i hk).choose else 1

noncomputable def orbElt (i : Fin 4) (k : Fin (orbSize i)) : H6 :=
  orbConj i k * tH i * (orbConj i k)⁻¹

theorem orbElt_conj (i : Fin 4) (k : Fin (orbSize i)) : ∃ g, orbElt i k = g * tH i * g⁻¹ :=
  ⟨orbConj i k, rfl⟩

theorem mat6_orbElt (i : Fin 4) {k : Fin (orbSize i)} (hk : (k : ℕ) < (orbTab i).size) :
    mat6 (orbElt i k) = dec6 ((orbTab i).getD k []) := by
  rw [orbElt, orbConj, dite_eq_left hk]
  exact (exists_conj_of_orbit i hk).choose_spec.symm

theorem orbElt_injective (i : Fin 4) : Function.Injective (orbElt i) := by
  have h := orbitsOK_parts i
  simp only [orbitOK, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨hsize, hdist⟩, hcanon⟩ := h
  intro k k' e
  have hk : (k : ℕ) < (orbTab i).size := by rw [hsize]; exact k.2
  have hk' : (k' : ℕ) < (orbTab i).size := by rw [hsize]; exact k'.2
  have e' := congrArg mat6 e
  rw [mat6_orbElt i hk, mat6_orbElt i hk'] at e'
  exact Fin.ext (distinctCheck_spec hdist hk hk'
    (dec6_injective (allCheck_spec hcanon hk) (allCheck_spec hcanon hk') e'))

theorem sylowP_check : sylowP.all pairCheck = true :=
  pairs_parts.2.2.2.2.2.2.2.2

@[expose] def SH : Subgroup H6 :=
  Subgroup.closure (genSet sylowP sylowP_check)

theorem sylowOK_parts : closureOK (sylowP.map Prod.fst) sylowT 512 = true ∧
    allCheck (invP (indexMap orbit0) (indexMap orbit1) (indexMap orbit2) (indexMap orbit3))
      sylowT = true := by
  have h := cert_parts.2.2.2.2.2.2.1
  simp only [sylowOK, Bool.and_eq_true] at h
  exact h

theorem card_SH : Nat.card SH = 512 :=
  card_closure_genSet _ _ _ sylowOK_parts.1

theorem SH_isPGroup : IsPGroup 2 SH :=
  IsPGroup.of_card (n := 9) (card_SH.trans (by norm_num))

theorem SH_index : ¬ 2 ∣ SH.index := by
  have h := Subgroup.card_mul_index SH
  rw [card_SH, card_H6] at h
  have : SH.index = 2835 := by omega
  rw [this]
  decide

theorem eq_conj_of_found (i : Fin 4) {c : List ℕ} {u : H6} (hc : mat6 u = dec6 c)
    (h : found (orbTab i) (indexMap (orbTab i)) c = true) : ∃ g, u = g * tH i * g⁻¹ := by
  obtain ⟨k, hk, hck⟩ := found_spec h
  obtain ⟨g, hg⟩ := exists_conj_of_orbit i hk
  refine ⟨g, mat6_injective ?_⟩
  rw [hc, ← hck, hg]

theorem exists_conj_of_mem_SH (u : H6) (hu : u ∈ SH) (hu2 : orderOf u = 2) :
    ∃ i g, u = g * tH i * g⁻¹ := by
  obtain ⟨k, hk, hcode, hcan⟩ := exists_code_closure sylowP sylowP_check 512 sylowOK_parts.1 hu
  have hcheck := allCheck_spec sylowOK_parts.2 hk
  set c := (closureT (sylowP.map Prod.fst)).getD k []
  have hu1 : u ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hu2
    omega
  have hsq : u * u = 1 := by
    have h := pow_orderOf_eq_one u
    rw [hu2, pow_two] at h
    exact h
  have hcsq : mul6 c c = one6 := by
    refine dec6_injective (canon6_mul6 _ _) canon6_one6 ?_
    rw [dec6_mul6, hcode, ← map_mul, hsq, map_one, dec6_one6]
  have hc1 : c ≠ one6 := by
    intro h
    apply hu1
    apply mat6_injective
    rw [← hcode, h, dec6_one6, map_one]
  change invP (indexMap orbit0) (indexMap orbit1) (indexMap orbit2) (indexMap orbit3) c = true
    at hcheck
  simp only [invP, hcsq, beq_self_eq_true, Bool.not_true, Bool.false_or, Bool.or_eq_true,
    beq_iff_eq] at hcheck
  rcases hcheck with (((h | h) | h) | h) | h
  · exact absurd h hc1
  · exact ⟨0, eq_conj_of_found 0 hcode.symm h⟩
  · exact ⟨1, eq_conj_of_found 1 hcode.symm h⟩
  · exact ⟨2, eq_conj_of_found 2 hcode.symm h⟩
  · exact ⟨3, eq_conj_of_found 3 hcode.symm h⟩

theorem p0P_check : p0P.all pairCheck = true :=
  pairs_parts.2.2.2.2.2.2.1

theorem p1P_check : p1P.all pairCheck = true :=
  pairs_parts.2.2.2.2.2.2.2.1

@[expose] def PH : Fin 4 → Subgroup H6 :=
  ![Subgroup.closure (genSet p0P p0P_check), Subgroup.closure (genSet p1P p1P_check), ⊥, ⊥]

theorem psOK_parts : closureOK (p0P.map Prod.fst) pT0 9 = true ∧
    closureOK (p1P.map Prod.fst) pT1 9 = true := by
  have h := cert_parts.2.2.2.2.2.1
  simp only [psOK, Bool.and_eq_true] at h
  exact h

theorem commOK_p (i : Fin 4) (hi : i = 0 ∨ i = 1) :
    ∀ cc ∈ (![p0P, p1P, [], []] : Fin 4 → List (List ℕ × List ℕ)) i,
      commutes6 cc.1 (tPair i).1 = true := by
  have h := cert_parts.2.2.1
  simp only [commOK, Bool.and_eq_true, List.all_eq_true] at h
  rcases hi with rfl | rfl
  · exact fun cc hc => h.1.1.1 cc (List.mem_append_right _ hc)
  · exact fun cc hc => h.1.1.2 cc (List.mem_append_right _ hc)

theorem not_nine_dvd (i : Fin 4) (h9 : 9 ∣ Nat.card (XH i)) : i = 0 ∨ i = 1 := by
  rw [card_XH] at h9
  fin_cases i
  · exact Or.inl rfl
  · exact Or.inr rfl
  · exact absurd h9 (by decide)
  · exact absurd h9 (by decide)

theorem PH_le_centralizer (i : Fin 4) (h9 : 9 ∣ Nat.card (XH i)) :
    PH i ≤ Subgroup.centralizer {tH i} := by
  rcases not_nine_dvd i h9 with rfl | rfl
  · show Subgroup.closure (genSet p0P p0P_check) ≤ _
    rw [Subgroup.closure_le]
    rintro _ ⟨cc, hm, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
    exact commute_of_commutes6 (mat6_ofCode _ _) (mat6_ofCode _ _) (commOK_p 0 (Or.inl rfl) cc hm)
  · show Subgroup.closure (genSet p1P p1P_check) ≤ _
    rw [Subgroup.closure_le]
    rintro _ ⟨cc, hm, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
    exact commute_of_commutes6 (mat6_ofCode _ _) (mat6_ofCode _ _) (commOK_p 1 (Or.inr rfl) cc hm)

theorem card_PH (i : Fin 4) (h9 : 9 ∣ Nat.card (XH i)) : Nat.card (PH i) = 9 := by
  rcases not_nine_dvd i h9 with rfl | rfl
  · exact card_closure_genSet _ _ _ psOK_parts.1
  · exact card_closure_genSet _ _ _ psOK_parts.2

theorem pow_512_eq_one {q : H6} {m : ℕ} (hq : q ^ 2 ^ m = 1) : q ^ 512 = 1 := by
  have h1 : orderOf q ∣ 2 ^ m := orderOf_dvd_of_pow_eq_one hq
  obtain ⟨j, -, hjq⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h1
  have h2 : orderOf q ∣ 1451520 := by
    rw [← card_H6]
    exact orderOf_dvd_natCard q
  rw [hjq] at h2
  have hj9 : j ≤ 9 := by
    by_contra hlt
    have : 2 ^ 10 ∣ 1451520 := (pow_dvd_pow 2 (by omega)).trans h2
    norm_num at this
  rw [← orderOf_dvd_iff_pow_eq_one, hjq]
  exact pow_dvd_pow 2 hj9

theorem twoOK_parts : allCheck (centralP t0C p0aC p0bC) cent0 = true ∧
    allCheck (centralP t1C p1aC p1bC) cent1 = true := by
  have h := cert_parts.2.2.2.2.2.2.2
  simp only [twoOK, Bool.and_eq_true] at h
  exact h

theorem eq_one_or_eq_of_centralP (i : Fin 4) {pa pb : List ℕ × List ℕ}
    (hpa : pairCheck pa = true) (hpb : pairCheck pb = true)
    (hcheck : allCheck (centralP (tPair i).1 pa.1 pb.1)
      (closureT ((centP i).map Prod.fst)) = true)
    {q : H6} (hq : q ∈ XH i) (h1 : q * ofCode pa hpa = ofCode pa hpa * q)
    (h2 : q * ofCode pb hpb = ofCode pb hpb * q) (h512 : q ^ 512 = 1) : q = 1 ∨ q = tH i := by
  obtain ⟨k, hk, hcode, hcan⟩ := exists_code_closure _ _ _ (centsOK_parts i) hq
  have hc := allCheck_spec hcheck hk
  set c := (closureT ((centP i).map Prod.fst)).getD k []
  have hc1 := commutes6_of_commute hcode.symm (mat6_ofCode _ _) h1
  have hc2 := commutes6_of_commute hcode.symm (mat6_ofCode _ _) h2
  have hc3 : pow512 c = one6 := by
    obtain ⟨y, hy⟩ := pow512_eq_mul6 c
    refine dec6_injective (by rw [hy]; exact canon6_mul6 _ _) canon6_one6 ?_
    rw [dec6_pow512, hcode, ← map_pow, h512, map_one, dec6_one6]
  simp only [centralP, hc1, hc2, hc3, beq_self_eq_true, Bool.and_self, Bool.not_true,
    Bool.false_or, Bool.or_eq_true, beq_iff_eq] at hc
  rcases hc with h | h
  · left
    apply mat6_injective
    rw [← hcode, h, dec6_one6, map_one]
  · right
    apply mat6_injective
    rw [← hcode, h, tH, mat6_ofCode]

theorem hPc_classes (i : Fin 4) (h9 : 9 ∣ Nat.card (XH i)) (q : H6) (hq : q ∈ XH i)
    (hc : ∀ p ∈ PH i, q * p = p * q) (h2 : ∃ m, q ^ 2 ^ m = 1) : q = 1 ∨ q = tH i := by
  obtain ⟨m, hm⟩ := h2
  have h512 := pow_512_eq_one hm
  have hpg := fun l (hl : l.all pairCheck = true) cc (hm : cc ∈ l) =>
    List.all_eq_true.mp hl cc hm
  rcases not_nine_dvd i h9 with rfl | rfl
  · exact eq_one_or_eq_of_centralP 0 (hpg _ p0P_check _ (List.mem_cons_self ..))
      (hpg _ p0P_check _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))) twoOK_parts.1 hq
      (hc _ (ofCode_mem_closure p0P_check (List.mem_cons_self ..)))
      (hc _ (ofCode_mem_closure p0P_check (List.mem_cons_of_mem _ (List.mem_cons_self ..))))
      h512
  · exact eq_one_or_eq_of_centralP 1 (hpg _ p1P_check _ (List.mem_cons_self ..))
      (hpg _ p1P_check _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))) twoOK_parts.2 hq
      (hc _ (ofCode_mem_closure p1P_check (List.mem_cons_self ..)))
      (hc _ (ofCode_mem_closure p1P_check (List.mem_cons_of_mem _ (List.mem_cons_self ..))))
      h512

theorem localRank_three_sp6 : localRank 3 H6 ≤ 2 := by
  refine localRank_three_le_two_of_classes tH XH PH orbSize (fun i => ?_) XH_le_centralizer
    orbElt orbElt_injective orbElt_conj SH_isPGroup SH_index exists_conj_of_mem_SH
    (fun i => ?_) PH_le_centralizer card_PH hPc_classes
  · rw [card_XH, card_H6]
    fin_cases i <;> rfl
  · rw [card_XH]
    fin_cases i <;> decide

end CFSG.RankThree.PartTwo.Census.Carrier.Sp6Two

namespace CFSG.RankThree.PartTwo.Census

open TauCeti CFSG.Assembly.LowTwoRank
open CFSG.Adapters.RankTwoModelTransports (glCongr glCongr_statedScalars statedProjCongr)

theorem statedScalars_subgroupOf_sp6 :
    (StatedScalars (Fin 3 ⊕ Fin 3) (ZMod 2)).subgroupOf (StatedSp 3 (ZMod 2)) = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  rw [Subgroup.mem_subgroupOf, StatedScalars, MonoidHom.mem_range] at hx
  obtain ⟨u, hu⟩ := hx
  have hall : ∀ v : (ZMod 2)ˣ, v = 1 := by decide
  have hu1 : u = 1 := hall u
  rw [Subgroup.mem_bot]
  apply Subtype.ext
  rw [← hu, hu1, map_one, OneMemClass.coe_one]

theorem nonempty_typeBGroupEquiv_sp6 (q : PrimePower) (hv : (LieTypeIndex.B 3 q).Valid)
    (hp : q.p = 2) (he : q.exponent = 1) :
    Nonempty (ValidLieTypeIndex.Group ⟨.B 3 q, hv⟩ ≃* Carrier.Sp6Two.H6) := by
  have := CFSG.QuasithinUnique.SQTK.finite_validIndex_fixedField ⟨.B 3 q, hv⟩
  have hfact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcard : Nat.card ↥(ValidLieTypeIndex.fixedField ⟨.B 3 q, hv⟩) = 2 ^ 1 := by
    rw [ValidLieTypeIndex.card_fixedField, ValidLieTypeIndex.fieldOrder_eq_characteristic_pow,
      show ValidLieTypeIndex.characteristic ⟨.B 3 q, hv⟩ = q.p from
        LieTypeIndex.characteristic_B 3 q,
      show ValidLieTypeIndex.fieldExponent ⟨.B 3 q, hv⟩ = q.exponent from
        LieTypeIndex.fieldExponent_B 3 q, hp, he]
  let φ : ↥(ValidLieTypeIndex.fixedField ⟨.B 3 q, hv⟩) ≃+* ZMod 2 :=
    (CFSG.ClassicalModels.finiteFieldEquivGaloisField _ 2 1 one_pos hcard).trans
      (GaloisField.equivZmodP 2).toRingEquiv
  exact ⟨(Carrier.SpinB.typeBGroupEquivStatedProj 3 q hv hp le_rfl).trans
    ((statedProjCongr (glCongr φ) (CFSG.ClassicalInvolution.Upgrade.glCongr_statedSp φ 3)
      (glCongr_statedScalars φ)).trans
      ((QuotientGroup.quotientMulEquivOfEq statedScalars_subgroupOf_sp6).trans
        QuotientGroup.quotientBot))⟩

theorem excluded433_B_three_two (q : PrimePower) (hv : (LieTypeIndex.B 3 q).Valid)
    (hp : q.p = 2) (he : q.exponent = 1) : Excluded433 (.lie ⟨.B 3 q, hv⟩) := by
  intro G _ _ hG e
  obtain ⟨φ⟩ := nonempty_typeBGroupEquiv_sp6 q hv hp he
  exact hG.false_of_localRank_three_le_two (e.trans φ) Carrier.Sp6Two.localRank_three_sp6

end CFSG.RankThree.PartTwo.Census
