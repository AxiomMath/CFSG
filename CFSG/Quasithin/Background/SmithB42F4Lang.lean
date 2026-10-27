module

public import CFSG.Quasithin.Background.SmithB42F4Base
public import CFSG.RankThree.PartOne.K128.ReeSector
public import CFSG.RankThree.PartOne.KLR.TwistPerm
public import CFSG.RankThree.Chevalley.SteinbergCEF4EvenQPlusWeyl
public import CFSG.RankThree.PartOne.K128.ReeTori

public section

namespace CFSG.Quasithin.B42F4

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
  CFSG.LieType.Ree.ReeTag CFSG.LieType.Ree.LargeReeInvolution CFSG.RankThree.Lattice
  CFSG.RankThree.PartOne.KE CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley


section Weyl


theorem wordProd_eq_of_lword_eq {l l' : List (Fin ReeTag.F4.tag.rank)}
    (h : lword ReeTag.F4.tag.rank (cartanList ReeTag.F4.tag) (l.map Fin.val) =
      lword ReeTag.F4.tag.rank (cartanList ReeTag.F4.tag) (l'.map Fin.val)) :
    (coxeterSystem ReeTag.F4.tag).wordProd l = (coxeterSystem ReeTag.F4.tag).wordProd l' := by
  have hm : wordMat ReeTag.F4.tag l = wordMat ReeTag.F4.tag l' := by
    rw [← toMat_lword ReeTag.F4.tag (toMat_cartanList ReeTag.F4.tag),
      ← toMat_lword ReeTag.F4.tag (toMat_cartanList ReeTag.F4.tag), h]
  refine ext_single fun i => ?_
  rw [wordProd_smul_eq_wordMat_mulVec, wordProd_smul_eq_wordMat_mulVec, hm]

theorem map_perm_eq (l : List (Fin ReeTag.F4.tag.rank)) :
    l.map ReeTag.F4.perm = l.map ![3, 2, 1, 0] :=
  List.map_congr_left fun k _ => CFSG.RankThree.PartOne.KLR.perm_vec k

@[expose] noncomputable def w0 : WeylGroup ReeTag.F4.tag :=
  (coxeterSystem ReeTag.F4.tag).wordProd
    [0, 1, 0, 2, 1, 0, 2, 1, 2, 3, 2, 1, 0, 2, 1, 2, 3, 2, 1, 0, 2, 1, 2, 3]

theorem w0_smul (v : Fin ReeTag.F4.tag.rank → ℤ) : w0 • v = -v := by
  have h : wordMat ReeTag.F4.tag
      [0, 1, 0, 2, 1, 0, 2, 1, 2, 3, 2, 1, 0, 2, 1, 2, 3, 2, 1, 0, 2, 1, 2, 3] =
      toMat ReeTag.F4.tag.rank [[-1, 0, 0, 0], [0, -1, 0, 0], [0, 0, -1, 0], [0, 0, 0, -1]] :=
    wordMat_eq_toMat .F4 _ (by decide +kernel)
  have h1 : toMat ReeTag.F4.tag.rank [[-1, 0, 0, 0], [0, -1, 0, 0], [0, 0, -1, 0], [0, 0, 0, -1]] =
      -1 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [w0, wordProd_smul_eq_wordMat_mulVec, h, h1, Matrix.neg_mulVec, Matrix.one_mulVec]

theorem w0_mul_comm (w : WeylGroup ReeTag.F4.tag) : w * w0 = w0 * w :=
  ext_single fun i => by rw [mul_smul, mul_smul, w0_smul, w0_smul, smul_neg]

theorem w0_mul_self : w0 * w0 = 1 :=
  ext_single fun i => by rw [mul_smul, w0_smul, w0_smul, neg_neg, one_smul]

theorem weylPerm_w0 : ReeTag.F4.weylPerm w0 = w0 := by
  rw [w0, weylPerm_wordProd, map_perm_eq]
  exact wordProd_eq_of_lword_eq (by decide +kernel)

theorem w0_twisted (w : WeylGroup ReeTag.F4.tag) : w * ReeTag.F4.weylPerm w0 * w⁻¹ = w0 := by
  rw [weylPerm_w0, w0_mul_comm, mul_assoc, mul_inv_cancel, mul_one]

@[expose] noncomputable def v3p : WeylGroup ReeTag.F4.tag :=
  (coxeterSystem ReeTag.F4.tag).wordProd [0, 1, 0, 2, 1, 0, 2, 3, 2, 1, 0, 2, 1, 2, 3, 2]

@[expose] noncomputable def v3m : WeylGroup ReeTag.F4.tag :=
  (coxeterSystem ReeTag.F4.tag).wordProd [0, 2, 1, 3, 2, 1, 0, 2, 1, 2, 3, 2, 1, 0, 2, 1]

theorem v3p_twisted :
    CFSG.RankThree.PartOne.K128.wPhi12p * ReeTag.F4.weylPerm v3p *
      CFSG.RankThree.PartOne.K128.wPhi12p⁻¹ = v3p := by
  rw [mul_inv_eq_iff_eq_mul, CFSG.RankThree.PartOne.K128.wPhi12p, v3p, weylPerm_wordProd,
    map_perm_eq, ← CoxeterSystem.wordProd_append, ← CoxeterSystem.wordProd_append]
  exact wordProd_eq_of_lword_eq (by decide +kernel)

theorem v3m_twisted :
    CFSG.RankThree.PartOne.K128.wPhi12m * ReeTag.F4.weylPerm v3m *
      CFSG.RankThree.PartOne.K128.wPhi12m⁻¹ = v3m := by
  rw [mul_inv_eq_iff_eq_mul, CFSG.RankThree.PartOne.K128.wPhi12m, v3m, weylPerm_wordProd,
    map_perm_eq, ← CoxeterSystem.wordProd_append, ← CoxeterSystem.wordProd_append]
  exact wordProd_eq_of_lword_eq (by decide +kernel)

theorem v3p_pow_three : v3p ^ 3 = 1 := by
  rw [pow_succ, pow_two, v3p, ← CoxeterSystem.wordProd_append, ← CoxeterSystem.wordProd_append,
    ← CoxeterSystem.wordProd_nil (coxeterSystem ReeTag.F4.tag)]
  exact wordProd_eq_of_lword_eq (by decide +kernel)

theorem v3m_pow_three : v3m ^ 3 = 1 := by
  rw [pow_succ, pow_two, v3m, ← CoxeterSystem.wordProd_append, ← CoxeterSystem.wordProd_append,
    ← CoxeterSystem.wordProd_nil (coxeterSystem ReeTag.F4.tag)]
  exact wordProd_eq_of_lword_eq (by decide +kernel)

theorem wordProd_ne_one_of_lget {l : List (Fin ReeTag.F4.tag.rank)} {M : List (List ℤ)}
    (h : lword ReeTag.F4.tag.rank (cartanList ReeTag.F4.tag) (l.map Fin.val) = M)
    (i k : Fin ReeTag.F4.tag.rank)
    (hne : lget M i k ≠ (Pi.single k 1 : Fin ReeTag.F4.tag.rank → ℤ) i) :
    (coxeterSystem ReeTag.F4.tag).wordProd l ≠ 1 := by
  intro h1
  have hm := CFSG.RankThree.PartOne.KLR.smul_single_eq_lget l M (wordMat_eq_toMat .F4 l h) k i
  rw [h1, one_smul] at hm
  exact hne hm.symm

theorem v3p_ne_one : v3p ≠ 1 :=
  wordProd_ne_one_of_lget (M := lword 4 (cartanList ReeTag.F4.tag)
    [0, 1, 0, 2, 1, 0, 2, 3, 2, 1, 0, 2, 1, 2, 3, 2]) rfl 1 0 (by decide +kernel)

theorem v3m_ne_one : v3m ≠ 1 :=
  wordProd_ne_one_of_lget (M := lword 4 (cartanList ReeTag.F4.tag)
    [0, 2, 1, 3, 2, 1, 0, 2, 1, 2, 3, 2, 1, 0, 2, 1]) rfl 1 0 (by decide +kernel)

end Weyl

section Closure

variable {L : Type} [Field L] [CharP L 2] {a : ℕ}
  {F : MulAut (adjointGroup ReeTag.F4.tag L)}

theorem canonicalRep_mem_twistedFixed (hF : CFSG.RankThree.PartOne.KLR.IsReeFrob a F)
    {w v : WeylGroup ReeTag.F4.tag} (hv : w * ReeTag.F4.weylPerm v * w⁻¹ = v) :
    canonicalRep (coxeterSystem ReeTag.F4.tag) L v ∈
      CFSG.RankThree.PartOne.KLR.twistedFixed F
        (canonicalRep (coxeterSystem ReeTag.F4.tag) L w) := by
  refine ⟨canonicalRep_mem_adjointGroup _ L v, ?_⟩
  rw [hF.fext_canonicalRep, CFSG.RankThree.Chevalley.EvenF4QPlus.canonicalRep_inv_of_charTwo,
    ← CFSG.RankThree.Chevalley.EvenF4QPlus.canonicalRep_mul_of_charTwo,
    ← CFSG.RankThree.Chevalley.EvenF4QPlus.canonicalRep_mul_of_charTwo, hv]

omit [CharP L 2] in
theorem canonicalRep_w0_conj_torus {h : ModGL ReeTag.F4.tag L}
    (hh : h ∈ torusGroup ReeTag.F4.tag L) :
    canonicalRep (coxeterSystem ReeTag.F4.tag) L w0 * h *
      (canonicalRep (coxeterSystem ReeTag.F4.tag) L w0)⁻¹ = h⁻¹ := by
  obtain ⟨l, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hh
  rw [CFSG.LieType.Chevalley.rootDiagUnit_inv]
  refine ((rootDiagUnit_eq_conj_canonicalRep_iff l⁻¹ l w0).2 fun v => ?_).symm
  rw [w0_smul, rootChar, rootChar]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [Pi.inv_apply, Pi.neg_apply, zpow_neg, inv_zpow, inv_inv]

end Closure

theorem dvd_phi12_factor {a ℓ : ℕ} (hℓ : ℓ.Prime)
    (hord : orderOf (2 : ZMod ℓ) = 12 * (2 * a + 1)) :
    (ℓ : ℤ) ∣ (2 ^ (2 * a + 1)) ^ 2 + 2 ^ (2 * a + 1) + 1 +
        2 ^ (a + 1) * (2 ^ (2 * a + 1) + 1) ∨
      (ℓ : ℤ) ∣ (2 ^ (2 * a + 1)) ^ 2 + 2 ^ (2 * a + 1) + 1 -
        2 ^ (a + 1) * (2 ^ (2 * a + 1) + 1) := by
  have := Fact.mk hℓ
  have hpow : ∀ k : ℕ, 0 < k → k < 12 * (2 * a + 1) → (2 : ZMod ℓ) ^ k ≠ 1 :=
    fun k hk hlt => pow_ne_one_of_lt_orderOf hk.ne' (by rw [hord]; exact hlt)
  set x : ZMod ℓ := 2 ^ (2 * a + 1) with hx
  set s : ZMod ℓ := 2 ^ (a + 1) with hs'
  have hs : s ^ 2 = 2 * x := by rw [hs', hx]; ring
  have h12 : x ^ 12 = 1 := by
    rw [hx, ← pow_mul, show (2 * a + 1) * 12 = 12 * (2 * a + 1) by ring, ← hord,
      pow_orderOf_eq_one]
  have h6 : x ^ 6 ≠ 1 := by
    rw [hx, ← pow_mul]
    exact hpow _ (by positivity) (by omega)
  have h4 : x ^ 4 ≠ 1 := by
    rw [hx, ← pow_mul]
    exact hpow _ (by positivity) (by omega)
  have hx2 : x ^ 2 + 1 ≠ 0 := by
    intro h
    apply h4
    have e : x ^ 4 - 1 = (x ^ 2 - 1) * (x ^ 2 + 1) := by ring
    rw [← sub_eq_zero, e, h, mul_zero]
  have hphi : x ^ 4 - x ^ 2 + 1 = 0 := by
    have h0 : (x ^ 4 - x ^ 2 + 1) * ((x ^ 6 - 1) * (x ^ 2 + 1)) = 0 := by
      have e : (x ^ 4 - x ^ 2 + 1) * ((x ^ 6 - 1) * (x ^ 2 + 1)) = x ^ 12 - 1 := by ring
      rw [e, h12, sub_self]
    rcases mul_eq_zero.1 h0 with h | h
    · exact h
    · exact absurd h (mul_ne_zero (sub_ne_zero.2 h6) hx2)
  have hprod : (x ^ 2 + x + 1 + s * (x + 1)) * (x ^ 2 + x + 1 - s * (x + 1)) = 0 := by
    have e : (x ^ 2 + x + 1 + s * (x + 1)) * (x ^ 2 + x + 1 - s * (x + 1)) =
        (x ^ 4 - x ^ 2 + 1) + (2 * x - s ^ 2) * (x + 1) ^ 2 := by ring
    rw [e, hphi, hs, sub_self, zero_mul, add_zero]
  rcases mul_eq_zero.1 hprod with h | h
  · left
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    exact h
  · right
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    exact h

section Lang

variable {K : Type} [Field K] [Finite K] [CharP K F4.prime] {a : ℕ}

theorem w0_ne_one : w0 ≠ 1 := by
  intro h
  have h1 := w0_smul (Pi.single 0 1 : Fin ReeTag.F4.tag.rank → ℤ)
  rw [h, one_smul] at h1
  have h2 := congrFun h1 0
  simp at h2

theorem exists_inverting_data (hK : Nat.card K = 2 ^ (2 * a + 1)) {ℓ : ℕ} (hℓ : ℓ.Prime)
    (hℓ2 : ℓ ≠ 2)
    (hdvd : (ℓ : ℤ) ∣ (2 ^ (2 * a + 1)) ^ 2 + 2 ^ (2 * a + 1) + 1 +
        2 ^ (a + 1) * (2 ^ (2 * a + 1) + 1) ∨
      (ℓ : ℤ) ∣ (2 ^ (2 * a + 1)) ^ 2 + 2 ^ (2 * a + 1) + 1 -
        2 ^ (a + 1) * (2 ^ (2 * a + 1) + 1)) :
    ∃ y c u : F4.reeGamma K a, y * y = 1 ∧ y ≠ 1 ∧ y * c * y⁻¹ = c⁻¹ ∧ orderOf c = ℓ ∧
      u ^ 3 = 1 ∧ u ≠ 1 ∧ y * u = u * y := by
  classical
  let L := AlgebraicClosure K
  have : CharP K 2 := ‹CharP K F4.prime›
  have : CharP L 2 := charP_of_injective_algebraMap (algebraMap K L).injective 2
  obtain ⟨D⟩ := CFSG.RankThree.PartOne.KLR.reeFrameData_nonempty (L := L) hK
  have hF := D.isFrob
  obtain ⟨w, v, hv, hv3, hv1, Φ, hΦ, hΦT, hΦF⟩ : ∃ (w v : WeylGroup ReeTag.F4.tag),
      w * ReeTag.F4.weylPerm v * w⁻¹ = v ∧ v ^ 3 = 1 ∧ v ≠ 1 ∧
      ∃ Φ : rootsOfUnity ℓ L →* ModGL ReeTag.F4.tag L, Function.Injective Φ ∧
        Φ.range ≤ torusGroup ReeTag.F4.tag L ∧
        Φ.range ≤ CFSG.RankThree.PartOne.KLR.twistedFixed D.F
          (canonicalRep (coxeterSystem ReeTag.F4.tag) L w) := by
    rcases hdvd with h | h
    · exact ⟨_, _, v3p_twisted, v3p_pow_three, v3p_ne_one,
        CFSG.RankThree.PartOne.K128.torus_hom_m_phi12p hF h⟩
    · exact ⟨_, _, v3m_twisted, v3m_pow_three, v3m_ne_one,
        CFSG.RankThree.PartOne.K128.torus_hom_m_phi12m hF h⟩
  set n₀ := canonicalRep (coxeterSystem ReeTag.F4.tag) L w0 with hn₀
  set n₃ := canonicalRep (coxeterSystem ReeTag.F4.tag) L v with hn₃
  set S : Subgroup (ModGL ReeTag.F4.tag L) := Subgroup.closure ({n₀, n₃} ∪ Set.range Φ) with hS
  have hSF : S ≤ CFSG.RankThree.PartOne.KLR.twistedFixed D.F
      (canonicalRep (coxeterSystem ReeTag.F4.tag) L w) := by
    rw [hS, Subgroup.closure_le]
    rintro g (hg | ⟨z, rfl⟩)
    · rcases hg with rfl | rfl
      · exact canonicalRep_mem_twistedFixed hF (w0_twisted w)
      · exact canonicalRep_mem_twistedFixed hF hv
    · exact hΦF ⟨z, rfl⟩
  obtain ⟨Ψ, hΨ⟩ := CFSG.RankThree.PartOne.K128.exists_hom_reeGamma D w S.subtype
    S.subtype_injective (by rw [Subgroup.range_subtype]; exact hSF)
  have hmem₀ : n₀ ∈ S := Subgroup.subset_closure (Or.inl (Set.mem_insert _ _))
  have hmem₃ : n₃ ∈ S := Subgroup.subset_closure (Or.inl (Set.mem_insert_of_mem _ rfl))
  have hℓ0 : (ℓ : L) ≠ 0 := by
    intro h0
    have h2 : (2 : ℕ) ∣ ℓ := (CharP.cast_eq_zero_iff L 2 ℓ).1 h0
    exact hℓ2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hℓ).1 h2).symm
  have : NeZero (ℓ : L) := ⟨hℓ0⟩
  have : NeZero ℓ := ⟨hℓ.ne_zero⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot L ℓ
  set z : rootsOfUnity ℓ L := ⟨hζ.toRootsOfUnity, by simp⟩ with hz
  have hzord : orderOf z = ℓ := by
    have : Fact ℓ.Prime := ⟨hℓ⟩
    refine orderOf_eq_prime ?_ ?_
    · exact Subtype.ext (Units.ext (by simp [hz, hζ.pow_eq_one]))
    · intro h1
      have := congrArg (fun y : rootsOfUnity ℓ L => ((y : Lˣ) : L)) h1
      simp only [hz] at this
      exact hζ.ne_one hℓ.one_lt (by simpa using this)
  have hmemc : Φ z ∈ S := Subgroup.subset_closure (Or.inr ⟨z, rfl⟩)
  refine ⟨Ψ ⟨n₀, hmem₀⟩, Ψ ⟨Φ z, hmemc⟩, Ψ ⟨n₃, hmem₃⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← map_mul]
    have : (⟨n₀, hmem₀⟩ * ⟨n₀, hmem₀⟩ : S) = 1 := Subtype.ext (by
      change n₀ * n₀ = 1
      rw [hn₀, ← CFSG.RankThree.Chevalley.EvenF4QPlus.canonicalRep_mul_of_charTwo, w0_mul_self,
        canonicalRep_one])
    rw [this, map_one]
  · intro h1
    have h2 := hΨ (h1.trans (map_one Ψ).symm)
    have h3 : n₀ = 1 := congrArg Subtype.val h2
    apply w0_ne_one
    apply CFSG.RankThree.Chevalley.EvenF4QPlus.canonicalRep_injective ReeTag.F4.tag L
    rw [← hn₀, h3, canonicalRep_one]
  · rw [← map_inv, ← map_mul, ← map_mul, ← map_inv]
    congr 1
    refine Subtype.ext ?_
    change n₀ * Φ z * n₀⁻¹ = (Φ z)⁻¹
    exact canonicalRep_w0_conj_torus (hΦT ⟨z, rfl⟩)
  · rw [orderOf_injective Ψ hΨ, Subgroup.orderOf_mk, orderOf_injective Φ hΦ, hzord]
  · rw [← map_pow]
    have : (⟨n₃, hmem₃⟩ : S) ^ 3 = 1 := Subtype.ext (by
      change n₃ ^ 3 = 1
      rw [hn₃, pow_succ, pow_two,
        ← CFSG.RankThree.Chevalley.EvenF4QPlus.canonicalRep_mul_of_charTwo,
        ← CFSG.RankThree.Chevalley.EvenF4QPlus.canonicalRep_mul_of_charTwo, ← pow_two,
        ← pow_succ, hv3, canonicalRep_one])
    rw [this, map_one]
  · intro h1
    have h2 := hΨ (h1.trans (map_one Ψ).symm)
    have h3 : n₃ = 1 := congrArg Subtype.val h2
    apply hv1
    apply CFSG.RankThree.Chevalley.EvenF4QPlus.canonicalRep_injective ReeTag.F4.tag L
    rw [← hn₃, h3, canonicalRep_one]
  · rw [← map_mul, ← map_mul]
    congr 1
    refine Subtype.ext ?_
    change n₀ * n₃ = n₃ * n₀
    rw [hn₀, hn₃, ← CFSG.RankThree.Chevalley.EvenF4QPlus.canonicalRep_mul_of_charTwo,
      ← CFSG.RankThree.Chevalley.EvenF4QPlus.canonicalRep_mul_of_charTwo, w0_mul_comm]

end Lang

theorem not_three_dvd_card_centralizer (a : ℕ) :
    ¬ 3 ∣ (2 ^ (2 * a + 1)) ^ 12 * (2 ^ (2 * a + 1) - 1) * ((2 ^ (2 * a + 1)) ^ 2 + 1) := by
  intro h
  have h' := (ZMod.natCast_eq_zero_iff _ 3).2 h
  have h2 : (2 : ZMod 3) ^ (2 * a + 1) = 2 := by
    rw [pow_succ, pow_mul, show (2 : ZMod 3) ^ 2 = 1 by decide, one_pow, one_mul]
  push_cast [Nat.cast_sub Nat.one_le_two_pow] at h'
  rw [h2] at h'
  exact absurd h' (by decide)

section Identify

variable {K : Type}
  [Field K] [Finite K] [CharP K F4.prime] {a : ℕ}

theorem isTConj_of_commute_order_three (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1))
    {y u : ModGL F4.tag K} (hy : y ∈ F4.reeGamma K a) (hu : u ∈ F4.reeGamma K a)
    (hy2 : y ^ 2 = 1) (hy1 : y ≠ 1) (hu3 : u ^ 3 = 1) (hu1 : u ≠ 1) (hyu : y * u = u * y) :
    IsTConj a K y := by
  rcases isZConj_or_isTConj ha hK hy hy2 hy1 with hz | ht
  · exfalso
    obtain ⟨g, hg, hgy⟩ := hz
    have hmem : g * u * g⁻¹ ∈ F4.reeGamma K a ⊓ Subgroup.centralizer {centralZ K a 1} := by
      refine Subgroup.mem_inf.2 ⟨mul_mem (mul_mem hg hu) (inv_mem hg), ?_⟩
      rw [Subgroup.mem_centralizer_singleton_iff, ← sylowH_zero_eq_centralZ, ← hgy]
      calc g * u * g⁻¹ * (g * y * g⁻¹) = g * (u * y) * g⁻¹ := by group
        _ = g * (y * u) * g⁻¹ := by rw [hyu]
        _ = g * y * g⁻¹ * (g * u * g⁻¹) := by group
    have hord : orderOf (g * u * g⁻¹) = 3 := by
      have := Fact.mk Nat.prime_three
      refine orderOf_eq_prime ?_ ?_
      · rw [conj_pow, hu3]
        group
      · intro h1
        apply hu1
        calc u = g⁻¹ * (g * u * g⁻¹) * g := by group
          _ = 1 := by rw [h1]; group
    have hdvd := Subgroup.orderOf_dvd_natCard _ hmem
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hcard, -⟩ :=
      large_Ree_two_involution_centralizers a ha K hK
    rw [hord, hcard] at hdvd
    exact not_three_dvd_card_centralizer a hdvd
  · exact ht

theorem exists_inverted_by_tOne (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1)) {ℓ : ℕ}
    (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) (hord : orderOf (2 : ZMod ℓ) = 12 * (2 * a + 1)) :
    ∃ c ∈ F4.reeGamma K a, orderOf c = ℓ ∧ sylowL a K 1 * c * (sylowL a K 1)⁻¹ = c⁻¹ := by
  obtain ⟨y, c, u, hy2, hy1, hyc, hcord, hu3, hu1, hyu⟩ :=
    exists_inverting_data hK hℓ hℓ2 (dvd_phi12_factor hℓ hord)
  have ht : IsTConj a K (y : ModGL F4.tag K) := by
    refine isTConj_of_commute_order_three ha hK y.2 u.2 ?_ ?_ ?_ ?_ ?_
    · rw [sq, ← Subgroup.coe_mul, hy2, Subgroup.coe_one]
    · exact fun h => hy1 (Subtype.ext h)
    · rw [← Subgroup.coe_pow, hu3, Subgroup.coe_one]
    · exact fun h => hu1 (Subtype.ext h)
    · rw [← Subgroup.coe_mul, ← Subgroup.coe_mul, hyu]
  obtain ⟨g, hg, hgy⟩ := ht
  have hyc' : (y : ModGL F4.tag K) * c * (y : ModGL F4.tag K)⁻¹ = (c : ModGL F4.tag K)⁻¹ := by
    rw [← Subgroup.coe_inv, ← Subgroup.coe_mul, ← Subgroup.coe_mul, hyc, Subgroup.coe_inv]
  refine ⟨g * c * g⁻¹, mul_mem (mul_mem hg c.2) (inv_mem hg), ?_, ?_⟩
  · rw [← MulAut.conj_apply, MulEquiv.orderOf_eq, Subgroup.orderOf_coe, hcord]
  · rw [← hgy]
    calc g * y * g⁻¹ * (g * c * g⁻¹) * (g * y * g⁻¹)⁻¹ =
        g * ((y : ModGL F4.tag K) * c * (y : ModGL F4.tag K)⁻¹) * g⁻¹ := by group
      _ = (g * c * g⁻¹)⁻¹ := by rw [hyc']; group

end Identify

end CFSG.Quasithin.B42F4
