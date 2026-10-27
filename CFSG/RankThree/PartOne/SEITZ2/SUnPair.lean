module

public import CFSG.RankThree.PartOne.SEITZ2.SUnTop
public import CFSG.RankThree.PartOne.SEITZ2.SU3Pair

public section

namespace CFSG.RankThree.PartOne.SEITZ2

open Matrix CFSG.ClassicalGroups.Unitary CFSG.LieType.Universal.Unitary
open CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag
open CFSG.RankThree.PartOne.CTP CFSG.RankThree.Classical
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.LieType.BorelTits (unitaryInvolution unitaryInvolution_apply)

section Quad

theorem mem_of_pow_card_eq_self {F : Type} [Field F] [Finite F] {k : Subfield F} {r : ℕ}
    (hr : 1 < r) (hk : Nat.card k = r) {a : F} (ha : a ^ r = a) : a ∈ k := by
  classical
  have : Fintype F := Fintype.ofFinite F
  have : Fintype k := Fintype.ofFinite k
  have hck : ∀ c : k, (c : F) ^ r = c := by
    intro c
    have h := FiniteField.pow_card c
    rw [← Nat.card_eq_fintype_card, hk] at h
    have h' := congrArg (fun z : k => (z : F)) h
    simpa using h'
  set P : Polynomial F := Polynomial.X ^ r - Polynomial.X with hP
  have hdeg : P.natDegree = r := FiniteField.X_pow_card_sub_X_natDegree_eq F hr
  have hP0 : P ≠ 0 := Polynomial.ne_zero_of_natDegree_gt (n := 0) (by omega)
  have hS : P.roots.toFinset.card ≤ r :=
    (Multiset.toFinset_card_le _).trans (hdeg ▸ Polynomial.card_roots' P)
  set T : Finset F := Finset.univ.map ⟨((↑) : k → F), Subtype.val_injective⟩ with hT
  have hTcard : T.card = r := by
    rw [hT, Finset.card_map, Finset.card_univ, ← Nat.card_eq_fintype_card, hk]
  have hTS : T ⊆ P.roots.toFinset := by
    intro z hz
    obtain ⟨c, -, rfl⟩ := Finset.mem_map.1 hz
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hP0]
    simp [hP, hck c]
  have hEq : T = P.roots.toFinset := Finset.eq_of_subset_of_card_le hTS (hTcard ▸ hS)
  have haS : a ∈ P.roots.toFinset := by
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hP0]
    simp [hP, ha]
  rw [← hEq] at haS
  obtain ⟨c, -, hc⟩ := Finset.mem_map.1 haS
  exact hc ▸ c.2

variable {f f₀ : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]

theorem quad_mem_of_fixed (h : UnitaryFieldData 2 f K) {k : Subfield K}
    (h₀ : UnitaryFieldData 2 f₀ k) (hbar : ∀ c : k, (h₀.bar c : K) = h.bar c) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hf : f = p * f₀) (hf₀ : 1 ≤ f₀) :
    ∀ z s t : K, unitaryInvolution K 2 f z = z → s ∈ k → t ∈ k →
      unitaryInvolution K 2 f s = s → unitaryInvolution K 2 f t = t → z ^ 2 + s * z + t = 0 →
      z ∈ k := by
  have : Finite k := h₀.finite
  have : CharP k 2 := h₀.charP
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  intro z s t hz hs ht hσs hσt hq
  set q₀ : ℕ := 2 ^ f₀ with hq₀
  have hfixk : ∀ x : K, x ∈ k → unitaryInvolution K 2 f x = x → x ^ q₀ = x := by
    intro x hx hσx
    have hσk : unitaryInvolution K 2 f x = ((unitaryInvolution k 2 f₀ ⟨x, hx⟩ : k) : K) := by
      rw [unitaryInvolution_eq_bar h, unitaryInvolution_eq_bar h₀, hbar]
    rw [hσx, unitaryInvolution_apply] at hσk
    simpa [hq₀] using hσk.symm
  have hs1 : s ^ q₀ = s := hfixk s hs hσs
  have ht1 : t ^ q₀ = t := hfixk t ht hσt
  let φ : K →+* K := iterateFrobenius K 2 f₀
  have hφx : ∀ x : K, φ x = x ^ q₀ := fun x => iterateFrobenius_def 2 f₀ x
  have hφs : φ s = s := by rw [hφx]; exact hs1
  have hφt : φ t = t := by rw [hφx]; exact ht1
  have hφz : (φ z) ^ 2 + s * φ z + t = 0 := by
    have := congrArg φ hq
    rw [map_add, map_add, map_pow, map_mul, hφs, hφt, map_zero] at this
    exact this
  have hroots : φ z = z ∨ φ z = z + s := by
    have hprod : (φ z + z) * (φ z + z + s) = 0 := by
      linear_combination hφz + hq + (φ z * z - t) * h2
    rcases mul_eq_zero.1 hprod with h1 | h1
    · exact Or.inl (by linear_combination h1 - z * h2)
    · exact Or.inr (by linear_combination h1 - (z + s) * h2)
  have hφφ : φ (φ z) = z := by
    rcases hroots with h1 | h1
    · rw [h1, h1]
    · rw [h1, map_add, h1, hφs]
      linear_combination s * h2
  have hz2 : z ^ (q₀ ^ 2) = z := by
    have := hφφ
    rw [hφx, hφx, ← pow_mul, ← sq] at this
    exact this
  have hzm : ∀ m : ℕ, z ^ ((q₀ ^ 2) ^ m) = z := by
    intro m
    induction m with
    | zero => simp
    | succ m ih => rw [pow_succ, pow_mul, ih, hz2]
  obtain ⟨m, hm⟩ := hp.odd_of_ne_two hp2
  have hzq : z ^ q₀ = z := by
    have h3 : z ^ (q₀ ^ p) = z := by
      have := hz
      rw [unitaryInvolution_apply, hf, mul_comm, pow_mul] at this
      exact this
    have h4 : q₀ ^ p = q₀ * (q₀ ^ 2) ^ m := by
      rw [hm, pow_succ, pow_mul, mul_comm]
    rw [h4, mul_comm, pow_mul, hzm m] at h3
    exact h3
  have hcard : Nat.card k = q₀ ^ 2 := by
    rw [h₀.card, hq₀, ← pow_mul, mul_comm]
  refine mem_of_pow_card_eq_self ?_ hcard hz2
  have : 2 ≤ q₀ := by
    rw [hq₀]
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ f₀ := Nat.pow_le_pow_right (by norm_num) hf₀
  nlinarith

end Quad

section Case

open CFSG.RankThree.PartOne.KFU CFSG.RankThree.PartOne.KCUnitaryCoord

@[expose] def SubfieldPairSUCaseOn (D : ℕ → Prop) (n : ℕ) (P : ℕ → Prop) : Prop :=
  ∀ (f f₀ : ℕ) (K : Type) [Field K] (h : UnitaryFieldData 2 f K) (k : Subfield K)
    (h₀ : UnitaryFieldData 2 f₀ k) (hbar : ∀ c : k, (h₀.bar c : K) = h.bar c) (p : ℕ),
    p.Prime → D p → f = p * f₀ → P f₀ →
    ∀ A : primeFormUnitary h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K),
      (suSub h h₀ hbar n).map (primeFormConjSU h _ A).toMonoidHom ≠ suSub h h₀ hbar n →
      Subgroup.closure ((suSub h h₀ hbar n : Set (gramSU h
          ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))) ∪
        ((suSub h h₀ hbar n).map (primeFormConjSU h _ A).toMonoidHom : Set (gramSU h
          ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)))) = ⊤

theorem SubfieldPairSUCaseOn.mono {D D' : ℕ → Prop} (hD : ∀ p, p.Prime → D' p → D p) {n : ℕ}
    {P : ℕ → Prop} (h : SubfieldPairSUCaseOn D n P) : SubfieldPairSUCaseOn D' n P :=
  fun f f₀ K _ hK k h₀ hbar p hp hp' => h f f₀ K hK k h₀ hbar p hp (hD p hp hp')

@[expose] def SubfieldPairSUCase (n : ℕ) (P : ℕ → Prop) : Prop :=
  SubfieldPairSUCaseOn (5 ≤ ·) n P

private theorem closure_eq_top_of_involution_pair {m f f₀ : ℕ} {K : Type} [Field K] [Finite K]
    [CharP K 2] (h : UnitaryFieldData 2 f K) {k : Subfield K} [Finite k] [CharP k 2]
    (h₀ : UnitaryFieldData 2 f₀ k)
    (hbar : ∀ c : k, (h₀.bar c : K) = h.bar c) {p : ℕ} (hf : f = p * f₀)
    (A : primeFormUnitary h ((1 : GL (Fin (m + 1)) K) : Matrix (Fin (m + 1)) (Fin (m + 1)) K))
    (hne : (suSub h h₀ hbar (m + 1)).map (primeFormConjSU h _ A).toMonoidHom ≠
      suSub h h₀ hbar (m + 1))
    (hgen : ∀ hσk : ∀ c : k, unitaryInvolution K 2 f (c : K) =
        ((unitaryInvolution k 2 f₀ c : k) : K),
      Nat.card (fixSub (unitaryInvolution K 2 f)) =
          Nat.card (ratFix (unitaryInvolution K 2 f) k) ^ p →
        Nat.card (ratFix (unitaryInvolution K 2 f) k) = 2 ^ f₀ →
        ∀ ω : K, ω ∈ k → ω ≠ 1 → unitaryInvolution K 2 f ω * ω = 1 →
        ∀ (A' : GL (Fin (m + 1)) K)
          (hA : conjTr (unitaryInvolution K 2 f) (A' : Matrix (Fin (m + 1)) (Fin (m + 1)) K) *
            (A' : Matrix (Fin (m + 1)) (Fin (m + 1)) K) = 1),
          (phiN (n := m + 1) hσk).range.map (conjU A' hA) ≠ (phiN hσk).range →
          (phiN (n := m + 1) hσk).range ⊔ (phiN hσk).range.map (conjU A' hA) = ⊤) :
    Subgroup.closure ((suSub h h₀ hbar (m + 1) : Set (gramSU h
        ((1 : GL (Fin (m + 1)) K) : Matrix (Fin (m + 1)) (Fin (m + 1)) K))) ∪
      ((suSub h h₀ hbar (m + 1)).map (primeFormConjSU h _ A).toMonoidHom : Set (gramSU h
        ((1 : GL (Fin (m + 1)) K) : Matrix (Fin (m + 1)) (Fin (m + 1)) K)))) = ⊤ := by
  classical
  have hσ₀ : IsUnitaryInvolution (unitaryInvolution k 2 f₀) :=
    isUnitaryInvolution_unitaryInvolution h₀.card_eq_sq
  set σ := unitaryInvolution K 2 f with hσdef
  set σ₀ := unitaryInvolution k 2 f₀ with hσ₀def
  have hσbar : ∀ c : K, σ c = h.bar c := fun c => unitaryInvolution_eq_bar h c
  have hσ₀bar : ∀ c : k, σ₀ c = h₀.bar c := fun c => unitaryInvolution_eq_bar h₀ c
  have hσk : ∀ c : k, σ (c : K) = ((σ₀ c : k) : K) := fun c => by
    rw [hσbar, ← hbar, hσ₀bar]
  have hfix : fixSub σ = h.fixedField := by
    ext c
    rw [mem_fixSub, UnitaryFieldData.mem_fixedField, hσbar]
  have hcardF : Nat.card (fixSub σ) = 2 ^ f := by
    rw [hfix]
    exact h.card_fixedField
  have hcardk0 : Nat.card (ratFix σ k) = 2 ^ f₀ := by
    rw [← h₀.card_fixedField]
    apply Nat.card_congr
    refine ⟨fun c => ⟨⟨c.1.1, c.2⟩, ?_⟩, fun d => ⟨⟨(d.1 : K), ?_⟩, d.1.2⟩, ?_, ?_⟩
    · apply Subtype.ext
      change ((h₀.bar ⟨c.1.1, c.2⟩ : k) : K) = c.1.1
      rw [hbar]
      have := c.1.2
      rw [mem_fixSub, hσbar] at this
      exact this
    · rw [mem_fixSub, hσbar, ← hbar]
      have := d.2
      rw [UnitaryFieldData.mem_fixedField] at this
      exact congrArg (fun z : k => (z : K)) this
    · intro c
      rfl
    · intro d
      rfl
  have hK : Nat.card (fixSub σ) = Nat.card (ratFix σ k) ^ p := by
    rw [hcardF, hcardk0, ← pow_mul, hf, mul_comm]
  obtain ⟨ω₀, hω₀n, hω₀1⟩ := hσ₀.exists_norm_one_ne_one
  have hωk : (ω₀ : K) ∈ k := ω₀.2
  have hω1 : (ω₀ : K) ≠ 1 := fun h1 => hω₀1 (Subtype.ext h1)
  have hωn : σ (ω₀ : K) * ω₀ = 1 := by
    rw [hσk]
    exact congrArg (fun z : k => (z : K)) hω₀n
  obtain ⟨A', hA'⟩ := A
  have hfun : (⇑σ : K → K) = ⇑h.bar := funext hσbar
  have hA : conjTr σ (A' : Matrix (Fin (m + 1)) (Fin (m + 1)) K) *
      (A' : Matrix (Fin (m + 1)) (Fin (m + 1)) K) = 1 := by
    have := mem_primeFormUnitary.1 hA'
    show ((A' : Matrix (Fin (m + 1)) (Fin (m + 1)) K).map σ)ᵀ *
      (A' : Matrix (Fin (m + 1)) (Fin (m + 1)) K) = 1
    rw [hfun]
    simpa using this
  have hUK : SUid σ (m + 1) = unitarySU 2 f K (m + 1) := SUid_eq_unitarySU h (m + 1)
  have hUk : SUid σ₀ (m + 1) = unitarySU 2 f₀ k (m + 1) := SUid_eq_unitarySU h₀ (m + 1)
  set N := gramSU h ((1 : GL (Fin (m + 1)) K) : Matrix (Fin (m + 1)) (Fin (m + 1)) K)
    with hNdef
  set Rgl : Subgroup (GL (Fin (m + 1)) K) :=
    (unitarySU 2 f₀ k (m + 1)).map (subfieldGL k (m + 1)) with hRgl
  have hS1 : (suSub h h₀ hbar (m + 1)).map N.subtype = Rgl := by
    ext x
    constructor
    · rintro ⟨_, ⟨g, rfl⟩, rfl⟩
      refine ⟨g.1, ?_, rfl⟩
      rw [unitarySU_eq_gramSU h₀ (m + 1)]
      exact g.2
    · rintro ⟨g', hg', rfl⟩
      rw [unitarySU_eq_gramSU h₀ (m + 1)] at hg'
      exact ⟨_, ⟨⟨g', hg'⟩, rfl⟩, rfl⟩
  have hS2 : (phiN (n := m + 1) hσk).range.map (SUid σ (m + 1)).subtype = Rgl := by
    ext x
    constructor
    · rintro ⟨_, ⟨g, rfl⟩, rfl⟩
      refine ⟨g.1, ?_, rfl⟩
      rw [← hUk]
      exact g.2
    · rintro ⟨g', hg', rfl⟩
      rw [← hUk] at hg'
      exact ⟨_, ⟨⟨g', hg'⟩, rfl⟩, rfl⟩
  have hconjN : ∀ S : Subgroup N,
      (S.map (primeFormConjSU h _ ⟨A', hA'⟩).toMonoidHom).map N.subtype =
        (S.map N.subtype).map (MulAut.conj A').toMonoidHom := by
    intro S
    rw [Subgroup.map_map, Subgroup.map_map]
    congr 1
  have hconjG : ∀ S : Subgroup (SUid σ (m + 1)),
      (S.map (conjU A' hA)).map (SUid σ (m + 1)).subtype =
        (S.map (SUid σ (m + 1)).subtype).map (MulAut.conj A').toMonoidHom := by
    intro S
    rw [Subgroup.map_map, Subgroup.map_map]
    congr 1
  have hneG : (phiN (n := m + 1) hσk).range.map (conjU A' hA) ≠ (phiN hσk).range := by
    intro heq
    apply hne
    apply Subgroup.map_injective (f := N.subtype) N.subtype_injective
    rw [hconjN, hS1]
    have := congrArg (Subgroup.map (SUid σ (m + 1)).subtype) heq
    rwa [hconjG, hS2] at this
  have hsupG := hgen hσk hK hcardk0 (ω₀ : K) hωk hω1 hωn A' hA hneG
  have hsupGL : Rgl ⊔ Rgl.map (MulAut.conj A').toMonoidHom = unitarySU 2 f K (m + 1) := by
    have := congrArg (Subgroup.map (SUid σ (m + 1)).subtype) hsupG
    rw [Subgroup.map_sup, hS2, hconjG, hS2, ← MonoidHom.range_eq_map, Subgroup.range_subtype,
      hUK] at this
    exact this
  have htop : (⊤ : Subgroup N).map N.subtype = unitarySU 2 f K (m + 1) := by
    rw [← MonoidHom.range_eq_map, Subgroup.range_subtype, unitarySU_eq_gramSU h (m + 1)]
    rfl
  have hsup : suSub h h₀ hbar (m + 1) ⊔
      (suSub h h₀ hbar (m + 1)).map (primeFormConjSU h _ ⟨A', hA'⟩).toMonoidHom = ⊤ := by
    apply Subgroup.map_injective (f := N.subtype) N.subtype_injective
    rw [Subgroup.map_sup, hconjN, hS1, htop]
    exact hsupGL
  rw [Subgroup.closure_union, Subgroup.closure_eq, Subgroup.closure_eq]
  exact hsup

theorem subfieldPairSUBig {n : ℕ} (hn : 3 ≤ n) :
    SubfieldPairSUCase n (fun f₀ => 2 ≤ f₀) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  intro f f₀ K _ h k h₀ hbar p hp hp5 hf hf₀ A hne
  have : Finite K := h.finite
  have : CharP K 2 := h.charP
  have : Finite k := h₀.finite
  have : CharP k 2 := h₀.charP
  have hf2 : 2 ≤ f := by rw [hf]; nlinarith [hp.two_le]
  have hp2 : p ≠ 2 := by omega
  have hσ : IsUnitaryInvolution (unitaryInvolution K 2 f) :=
    isUnitaryInvolution_unitaryInvolution h.card_eq_sq
  have hσ₀ : IsUnitaryInvolution (unitaryInvolution k 2 f₀) :=
    isUnitaryInvolution_unitaryInvolution h₀.card_eq_sq
  have hquad := quad_mem_of_fixed h h₀ hbar hp hp2 hf (by omega : 1 ≤ f₀)
  have hq2 : 2 ^ f ≠ 2 := by
    have : 2 ^ 2 ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf2
    omega
  have hq : ∃ s : k, s ≠ 0 ∧ unitaryInvolution k 2 f₀ s * s ≠ 1 :=
    exists_norm_ne_one h₀.card_eq_sq (by
      have : 2 ^ 2 ≤ 2 ^ f₀ := Nat.pow_le_pow_right (by norm_num) hf₀
      omega)
  refine closure_eq_top_of_involution_pair h h₀ hbar hf A hne
    fun hσk hK hcardk0 ω hωk hω1 hωn A' hA hneG => ?_
  have hk4 : 4 ∣ Nat.card (ratFix (unitaryInvolution K 2 f) k) := by
    rw [hcardk0]
    have : (4 : ℕ) = 2 ^ 2 := by norm_num
    rw [this]
    exact pow_dvd_pow 2 hf₀
  exact su_pair_top hσ hσ₀ hσk hp hp2 hK hk4 hq hωk hω1 hωn hquad h.card_eq_sq hq2 hn A' hA hneG

@[expose] def SubfieldPairSUF2 (n : ℕ) : Prop := SubfieldPairSUCase n (fun f₀ => f₀ = 1)

@[expose] def SubfieldPairSUF2Odd (n : ℕ) : Prop :=
  SubfieldPairSUCaseOn (· ≠ 2) n (fun f₀ => f₀ = 1)

theorem SubfieldPairSUF2Odd.subfieldPairSUF2 {n : ℕ} (h : SubfieldPairSUF2Odd n) :
    SubfieldPairSUF2 n :=
  SubfieldPairSUCaseOn.mono (fun _ _ hp => by omega) h

theorem subfieldPairSU_of_f2 {n : ℕ} (hn : 3 ≤ n)
    (h2 : SubfieldPairSUF2 n) : SubfieldPairSU n := by
  intro f f₀ K _ h k h₀ hbar p hp hp5 hf hnot A hne
  have h1 := h₀.one_le
  rcases Nat.lt_or_ge f₀ 2 with hlt | hge
  · exact h2 f f₀ K h k h₀ hbar p hp hp5 hf (by omega) A hne
  · exact subfieldPairSUBig hn f f₀ K h k h₀ hbar p hp hp5 hf hge A hne

end Case

end CFSG.RankThree.PartOne.SEITZ2
