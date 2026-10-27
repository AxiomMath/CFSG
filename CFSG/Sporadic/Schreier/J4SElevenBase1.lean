
module

public import CFSG.Sporadic.Schreier.J4SElevenBase

public import CFSG.Sporadic.Schreier.J4SElevenCheck
public import CFSG.Sporadic.Schreier.J4SFiveBase1
public import CFSG.Sporadic.Schreier.J4SForm
public import CFSG.Sporadic.Schreier.J4SRankBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.LocalWitness
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.Frattini.Core
public import CFSG.Sporadic.Schreier.J4SNative
public import CFSG.Sporadic.Schreier.J4SCols
public import CFSG.Sporadic.Schreier.J4SElevenData
public import CFSG.Sporadic.Schreier.J4SPrimes
public meta import CFSG.Sporadic.Schreier.J4SPrimes
public import CFSG.Sporadic.J4.Local
public import CFSG.Sporadic.Schreier.J4SOrbits
public meta import CFSG.Sporadic.Schreier.J4SOrbits

@[expose] public noncomputable section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Sporadic.J4Schreier

open CFSG.Sporadic.J4 CFSG.Sporadic.GLQ CFSG.SectionRank CFSG.SectionRank.Native
open CFSG.Sporadic.SmallF2 CFSG.Sporadic.SmallF2.Native
open scoped Matrix commutatorElement

theorem regsRep_max7 :
    RegsRep Sp φ 7 (runProg (initRegs a b) max7Prog) max7Regs :=
  regsRep_runProg max7Prog max7Prog_lt (regsRep_initRegs (rep_a matFacts) (rep_b matFacts))

theorem rep_nrm₁ :
    Rep Sp φ nrm₁ H1n := regsRep_max7.2 1 (by norm_num)

theorem rep_nrm₂ :
    Rep Sp φ nrm₂ H2n := regsRep_max7.2 2 (by norm_num)

theorem rep_qs :
    Rep Sp φ qs S5n := rep_powP rep_nrm₂ 8

theorem rep_qx₀ : Rep Sp φ qx₀ X0n :=
  rep_mulP (rep_mulP (rep_mulP rep_qs (rep_invP rep_nrm₁)) (rep_invP rep_qs)) rep_nrm₁

theorem rep_qy₀ :
    Rep Sp φ qy₀ Y0n := rep_commP rep_qs (rep_mulP rep_nrm₁ rep_nrm₂)

theorem rep_qx :
    Rep Sp φ qx QXn := rep_mulP rep_qx₀ (rep_powP rep_qy₀ 7)

theorem rep_qy :
    Rep Sp φ qy QYn := rep_powP rep_qy₀ 3

theorem rep_qz :
    Rep Sp φ qz QZn := rep_commP rep_qx rep_qy

theorem rep_qu :
    Rep Sp φ qu U8n := rep_powP rep_nrm₂ 5

theorem rep_qw : Rep Sp φ qw W2n :=
  rep_mulP (rep_mulP (rep_mulP (rep_powP rep_qx 3) (rep_powP rep_qy 9)) rep_qz)
    (rep_wordP rep_nrm₁ rep_nrm₂ _)

theorem rep_qWord
    (i j k : ℕ) : Rep Sp φ (qx ^ i * qy ^ j * qz ^ k) (qWord i j k) :=
  rep_mulP (rep_mulP (rep_powP rep_qx i) (rep_powP rep_qy j)) (rep_powP rep_qz k)

theorem rep_q23 : Rep Sp φ q23Elt C23n :=
  rep_powP (rep_wordP (rep_x matFacts) (rep_y matFacts) [1, 2]) 10644480

theorem qz_mul_qx :
    qz * qx = qx * qz :=
  eq_of_rep_check (rep_mulP rep_qz rep_qx) (rep_mulP rep_qx rep_qz) q11_basic.1

theorem qz_mul_qy :
    qz * qy = qy * qz :=
  eq_of_rep_check (rep_mulP rep_qz rep_qy) (rep_mulP rep_qy rep_qz) q11_basic.2.1

theorem qz_ne_one : qz ≠ 1 := by
  intro h
  apply Sp.toVec_ne q11_basic.2.2
  rw [Sp.toVec_vmul (Sp.unit_wf _) rep_qz.1, rep_qz.2.2.1, h, map_one, Matrix.vecMul_one]

theorem qWord_pow_eleven
    {i j k : ℕ} (hi : i < 11) (hj : j < 11) (hk : k < 11) :
    (qx ^ i * qy ^ j * qz ^ k) ^ 11 = 1 := by
  have h := q11_exp
  unfold expOK at h
  have h1 := List.all_eq_true.1 h (i + 11 * (j + 11 * k)) (List.mem_range.2 (by omega))
  have e1 : (i + 11 * (j + 11 * k)) % 11 = i := by omega
  have e2 : (i + 11 * (j + 11 * k)) / 11 % 11 = j := by omega
  have e3 : (i + 11 * (j + 11 * k)) / 121 % 11 = k := by omega
  rw [e1, e2, e3] at h1
  exact pow_eq_one_of_rep_check (rep_qWord i j k) h1

theorem qx_pow_eleven :
    qx ^ 11 = 1 := by
  have h := qWord_pow_eleven (i := 1) (j := 0) (k := 0) (by norm_num) (by norm_num) (by norm_num)
  rwa [pow_one, pow_zero, pow_zero, mul_one, mul_one] at h

theorem qy_pow_eleven :
    qy ^ 11 = 1 := by
  have h := qWord_pow_eleven (i := 0) (j := 1) (k := 0) (by norm_num) (by norm_num) (by norm_num)
  rwa [pow_one, pow_zero, pow_zero, one_mul, mul_one] at h

theorem qz_pow_eleven :
    qz ^ 11 = 1 := by
  have h := qWord_pow_eleven (i := 0) (j := 0) (k := 1) (by norm_num) (by norm_num) (by norm_num)
  rwa [pow_one, pow_zero, pow_zero, one_mul, one_mul] at h

theorem commute_qz_qx :
    Commute ⁅qx, qy⁆ qx := qz_mul_qx

theorem commute_qz_qy :
    Commute ⁅qx, qy⁆ qy := qz_mul_qy

theorem q11_inj :
    Function.Injective fun t : Fin 11 × Fin 11 × Fin 11 =>
    qx ^ (t.1 : ℕ) * qy ^ (t.2.1 : ℕ) * ⁅qx, qy⁆ ^ (t.2.2 : ℕ) := by
  rintro ⟨i, j, k⟩ ⟨i', j', k'⟩ hijk
  dsimp only at hijk
  have hm := congrArg φ hijk
  rw [map_mul, map_mul, map_pow, map_pow, map_pow, map_mul, map_mul, map_pow, map_pow,
    map_pow] at hm
  have hnf := q11_normalForm
  unfold Ops.normalFormOK at hnf
  have hsz : (Array.ofFn (n := 11 ^ [QXn.1, QYn.1, QZn.1].length) fun n =>
      O.appBase 11 [QXn.1, QYn.1, QZn.1] n.val (O.unit 0)).size = 1331 := by
    simp
  have hvs : ∀ n < 1331, Sp.toVec (Array.ofFn (n := 11 ^ [QXn.1, QYn.1, QZn.1].length) fun n =>
      O.appBase 11 [QXn.1, QYn.1, QZn.1] n.val (O.unit 0))[n]! = Sp.toVec (O.unit 0) ᵥ*
        (Sp.toMat QXn.1 ^ (n % 11) * Sp.toMat QYn.1 ^ (n / 11 % 11) *
          Sp.toMat QZn.1 ^ (n / 11 / 11 % 11)) := by
    intro n hn
    rw [getElem!_pos _ n (by rw [hsz]; exact hn), Array.getElem_ofFn]
    exact Sp.appBase_three rep_qx.1 rep_qy.1 rep_qz.1 11 n (Sp.unit_wf 0)
  have hcode : ∀ (i j k : Fin 11), (i + 11 * (j + 11 * k) : ℕ) < 1331 ∧
      (i + 11 * (j + 11 * k) : ℕ) % 11 = i ∧ (i + 11 * (j + 11 * k) : ℕ) / 11 % 11 = j ∧
      (i + 11 * (j + 11 * k) : ℕ) / 11 / 11 % 11 = k := by
    intro i j k
    have := i.isLt
    have := j.isLt
    have := k.isLt
    omega
  obtain ⟨c1, c2, c3, c4⟩ := hcode i j k
  obtain ⟨c1', c2', c3', c4'⟩ := hcode i' j' k'
  by_contra hne
  have hcne : (i + 11 * (j + 11 * k) : ℕ) ≠ i' + 11 * (j' + 11 * k') := by
    intro hc
    apply hne
    have e1 : (i : ℕ) = i' := by rw [← c2, ← c2', hc]
    have e2 : (j : ℕ) = j' := by rw [← c3, ← c3', hc]
    have e3 : (k : ℕ) = k' := by rw [← c4, ← c4', hc]
    exact Prod.ext (Fin.ext e1) (Prod.ext (Fin.ext e2) (Fin.ext e3))
  apply Sp.toVec_ne_of_distinctOK hnf (by rw [hsz]; exact c1) (by rw [hsz]; exact c1') hcne
  rw [hvs _ c1, hvs _ c1', c2, c3, c4, c2', c3', c4', rep_qx.2.2.1, rep_qy.2.2.1, rep_qz.2.2.1]
  exact congrArg (fun M => Sp.toVec (O.unit 0) ᵥ* M) hm

theorem card_Q11 :
    Nat.card Q11 = 11 ^ 3 :=
  @LocalWitness.card_closure_eq_cube J (Subgroup.toGroup J) qx qy 11 (by norm_num) qx_pow_eleven
    qy_pow_eleven commute_qz_qx commute_qz_qy q11_inj

theorem mem_Q11_iff {g : J} :
    g ∈ Q11 ↔ ∃ i j k : ℕ, i < 11 ∧ j < 11 ∧ k < 11 ∧ g = qx ^ i * qy ^ j * qz ^ k := by
  constructor
  · intro hg
    exact @LocalWitness.mem_closure_normalForm J (Subgroup.toGroup J) qx qy 11 (by norm_num)
      qx_pow_eleven qy_pow_eleven commute_qz_qx commute_qz_qy g hg
  · rintro ⟨i, j, k, -, -, -, rfl⟩
    exact Q11.mul_mem (Q11.mul_mem (Q11.pow_mem qx_mem i) (Q11.pow_mem qy_mem j))
      (Q11.pow_mem qz_mem k)

theorem pow_eleven_of_mem
    {g : J} (hg : g ∈ Q11) : g ^ 11 = 1 := by
  obtain ⟨i, j, k, hi, hj, hk, rfl⟩ := mem_Q11_iff.1 hg
  exact qWord_pow_eleven hi hj hk

theorem qz_commute_of_mem
    {g : J} (hg : g ∈ Q11) : g * qz = qz * g := by
  have h : Q11 ≤ Subgroup.centralizer ({qz} : Set J) := by
    rw [Q11, Subgroup.closure_le]
    rintro _ (rfl | rfl)
    · rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
      exact qz_mul_qx.symm
    · rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
      exact qz_mul_qy.symm
  have h2 := h hg
  rw [Subgroup.mem_centralizer_singleton_iff] at h2
  exact h2

theorem not_commute_qx_qy
    {i j : ℕ} (hi : i < 11) (hj : j < 11) (hij : i ≠ 0 ∨ j ≠ 0)
    (hx : qx ^ i * qy ^ j * qx = qx * (qx ^ i * qy ^ j))
    (hy : qx ^ i * qy ^ j * qy = qy * (qx ^ i * qy ^ j)) : False := by
  have h := q11_center
  unfold centerOK at h
  have h1 := List.all_eq_true.1 h (i + 11 * j - 1) (List.mem_range.2 (by omega))
  dsimp only at h1
  have e1 : (i + 11 * j - 1 + 1) % 11 = i := by omega
  have e2 : (i + 11 * j - 1 + 1) / 11 % 11 = j := by omega
  rw [e1, e2, Bool.or_eq_true] at h1
  have rA : Rep Sp φ (qx ^ i * qy ^ j) (mulP (powP QXn i) (powP QYn j)) :=
    rep_mulP (rep_powP rep_qx i) (rep_powP rep_qy j)
  rcases h1 with h1 | h1
  · have r1 := rep_mulP rA rep_qx
    have r2 := rep_mulP rep_qx rA
    refine ne_of_rowsDiffer r1.1 r2.1 h1 ?_
    rw [r1.2.2.1, r2.2.2.1, hx]
  · have r1 := rep_mulP rA rep_qy
    have r2 := rep_mulP rep_qy rA
    refine ne_of_rowsDiffer r1.1 r2.1 h1 ?_
    rw [r1.2.2.1, r2.2.2.1, hy]

theorem eq_pow_of_commute
    {g : J} (hg : g ∈ Q11) (hc : g * qx = qx * g) (hc' : g * qy = qy * g) :
    ∃ k : ℕ, g = qz ^ k := by
  obtain ⟨i, j, k, hi, hj, hk, rfl⟩ := mem_Q11_iff.1 hg
  have hcx : qz ^ k * qx = qx * qz ^ k := commute_pow_qz qz_mul_qx k
  have hcy : qz ^ k * qy = qy * qz ^ k := commute_pow_qz qz_mul_qy k
  have hx : qx ^ i * qy ^ j * qx = qx * (qx ^ i * qy ^ j) := by
    refine mul_right_cancel (b := qz ^ k) ?_
    rw [mul_assoc (qx ^ i * qy ^ j) qx, ← hcx, ← mul_assoc, hc, mul_assoc qx]
  have hy : qx ^ i * qy ^ j * qy = qy * (qx ^ i * qy ^ j) := by
    refine mul_right_cancel (b := qz ^ k) ?_
    rw [mul_assoc (qx ^ i * qy ^ j) qy, ← hcy, ← mul_assoc, hc', mul_assoc qy]
  by_cases h0 : i = 0 ∧ j = 0
  · obtain ⟨rfl, rfl⟩ := h0
    exact ⟨k, by rw [pow_zero, pow_zero, one_mul, one_mul]⟩
  · exact (not_commute_qx_qy hi hj (by omega) hx hy).elim

theorem center_Q11 :
    (Subgroup.center Q11).map Q11.subtype = Subgroup.zpowers qz := by
  ext g
  constructor
  · rintro ⟨⟨g, hg⟩, hc, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_center_iff] at hc
    have hcx := Subtype.ext_iff.1 (hc ⟨qx, qx_mem⟩)
    have hcy := Subtype.ext_iff.1 (hc ⟨qy, qy_mem⟩)
    rw [Subgroup.coe_mul, Subgroup.coe_mul] at hcx hcy
    obtain ⟨k, hk⟩ := eq_pow_of_commute hg hcx.symm hcy.symm
    refine ⟨(k : ℤ), ?_⟩
    simp only [zpow_natCast]
    exact hk.symm
  · intro hg
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hg
    refine ⟨⟨qz ^ k, Q11.zpow_mem qz_mem k⟩, ?_, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_center_iff]
    intro h
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul]
    exact (@Commute.zpow_right J (Subgroup.toGroup J) _ _ (qz_commute_of_mem h.2) k).eq

theorem orderOf_qz :
    orderOf qz = 11 := by
  have : Fact (Nat.Prime 11) := ⟨by norm_num⟩
  exact orderOf_eq_prime qz_pow_eleven qz_ne_one

theorem card_center_Q11 :
    Nat.card (Subgroup.center Q11) = 11 := by
  rw [← Subgroup.card_map_of_injective Q11.subtype_injective, center_Q11, Nat.card_zpowers,
    orderOf_qz]

theorem center_Q11_eq :
    Subgroup.center Q11 = Subgroup.zpowers ⟨qz, qz_mem⟩ := by
  apply Subgroup.map_injective Q11.subtype_injective
  rw [center_Q11, MonoidHom.map_zpowers]
  rfl

theorem isPGroup_Q11 :
    IsPGroup 11 Q11 := IsPGroup.of_card card_Q11

theorem pow_eleven_Q11
    (g : Q11) : g ^ 11 = 1 :=
  Subtype.ext (by rw [Subgroup.coe_pow, pow_eleven_of_mem g.2, Subgroup.coe_one])

theorem exponent_Q11 :
    Monoid.exponent Q11 = 11 := by
  have : Fact (Nat.Prime 11) := ⟨by norm_num⟩
  have hdvd : Monoid.exponent Q11 ∣ 11 := Monoid.exponent_dvd_of_forall_pow_eq_one pow_eleven_Q11
  rcases (Nat.dvd_prime (Fact.out : Nat.Prime 11)).1 hdvd with h | h
  · exfalso
    rw [Monoid.exp_eq_one_iff] at h
    have h1 := Finite.card_le_one_iff_subsingleton.2 h
    rw [card_Q11] at h1
    norm_num at h1
  · exact h

theorem commutator_Q11 :
    commutator Q11 = Subgroup.center Q11 := by
  have : Fact (Nat.Prime 11) := ⟨by norm_num⟩
  apply le_antisymm
  · have hq : Nat.card (Q11 ⧸ Subgroup.center Q11) = 11 ^ 2 := by
      have h := Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center Q11)
      rw [card_Q11, card_center_Q11] at h
      omega
    exact Subgroup.Normal.quotient_commutative_iff_commutator_le.1
      (IsPGroup.isMulCommutative_of_card_eq_prime_sq hq)
  · rw [center_Q11_eq, Subgroup.zpowers_le, commutator_def]
    have e : (⟨qz, qz_mem⟩ : Q11) = ⁅(⟨qx, qx_mem⟩ : Q11), ⟨qy, qy_mem⟩⁆ := Subtype.ext rfl
    rw [e]
    exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)

theorem frattini_Q11 :
    frattini Q11 = Subgroup.center Q11 := by
  have : Fact (Nat.Prime 11) := ⟨by norm_num⟩
  have : Fact (IsPGroup 11 Q11) := ⟨isPGroup_Q11⟩
  rw [CFSG.frattini_eq_closure_commutator_union_powers (p := 11), ← commutator_Q11]
  have hpow : Set.range (fun x : Q11 => x ^ 11) = {1} := by
    ext g
    simp only [Set.mem_range, Set.mem_singleton_iff]
    constructor
    · rintro ⟨x, rfl⟩
      exact pow_eleven_Q11 x
    · rintro rfl
      exact ⟨1, one_pow 11⟩
  rw [hpow, Set.union_eq_left.2 (Set.singleton_subset_iff.2 (commutator Q11).one_mem),
    Subgroup.closure_eq]

theorem isExtraspecial_Q11 :
    IsExtraspecialPGroup 11 Q11 :=
  ⟨isPGroup_Q11, commutator_Q11, frattini_Q11, card_center_Q11⟩

theorem nrm₁_qx :
    nrm₁ * qx * nrm₁⁻¹ = qx ^ 7 * qy ^ 3 * qz ^ 2 :=
  conj_of_rep_check rep_nrm₁ rep_qx (rep_qWord 7 3 2) q11_conj.1

theorem nrm₁_qy :
    nrm₁ * qy * nrm₁⁻¹ = qx ^ 3 * qy ^ 3 * qz ^ 9 :=
  conj_of_rep_check rep_nrm₁ rep_qy (rep_qWord 3 3 9) q11_conj.2.1

theorem nrm₁_qz :
    nrm₁ * qz * nrm₁⁻¹ = qz :=
  conj_of_rep_check rep_nrm₁ rep_qz rep_qz q11_conj.2.2.1

theorem nrm₂_qx :
    nrm₂ * qx * nrm₂⁻¹ = qx ^ 8 * qy ^ 6 * qz ^ 3 :=
  conj_of_rep_check rep_nrm₂ rep_qx (rep_qWord 8 6 3) q11_conj.2.2.2.1

theorem nrm₂_qy :
    nrm₂ * qy * nrm₂⁻¹ = qx ^ 10 * qy ^ 5 * qz ^ 8 :=
  conj_of_rep_check rep_nrm₂ rep_qy (rep_qWord 10 5 8) q11_conj.2.2.2.2.1

theorem nrm₂_qz :
    nrm₂ * qz * nrm₂⁻¹ = qz ^ 2 :=
  conj_of_rep_check rep_nrm₂ rep_qz (rep_powP rep_qz 2) q11_conj.2.2.2.2.2

theorem nrm₁_mem_normalizer :
    nrm₁ ∈ Subgroup.normalizer (Q11 : Set J) :=
  mem_normalizer_Q11 (by rw [nrm₁_qx]; exact qWord_mem _ _ _)
    (by rw [nrm₁_qy]; exact qWord_mem _ _ _)

theorem nrm₂_mem_normalizer :
    nrm₂ ∈ Subgroup.normalizer (Q11 : Set J) :=
  mem_normalizer_Q11 (by rw [nrm₂_qx]; exact qWord_mem _ _ _)
    (by rw [nrm₂_qy]; exact qWord_mem _ _ _)

theorem finrank_rowFix_qx :
    Module.finrank (ZMod 2) (rowFix (φ qx)) = 12 :=
  finrank_rowFix_of_ok (by norm_num) rep_qx.2.2.1 q11_fix.1

theorem finrank_rowFix_qy :
    Module.finrank (ZMod 2) (rowFix (φ qy)) = 12 :=
  finrank_rowFix_of_ok (by norm_num) rep_qy.2.2.1 q11_fix.2.1

theorem finrank_rowFix_qz :
    Module.finrank (ZMod 2) (rowFix (φ qz)) = 2 :=
  finrank_rowFix_of_ok (by norm_num) rep_qz.2.2.1 q11_fix.2.2

theorem finrank_rowFix_q23 :
    Module.finrank (ZMod 2) (rowFix (φ q23Elt)) = 2 :=
  finrank_rowFix_of_ok (by norm_num) rep_q23.2.2.1 c23_fix

end CFSG.Sporadic.J4Schreier
