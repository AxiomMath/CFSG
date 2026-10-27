module

public import CFSG.RankThree.Chevalley.SteinbergCAG2ToralPrimePlane
public import CFSG.LieType.Chevalley.G2ThreeAutomorphismNormalForm
public import CFSG.LieType.Ree.FixedMonomialQuotient

public noncomputable section

namespace CFSG.RankThree.Chevalley

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.ComponentClassification.UnbalancedCatalog CFSG.LieType.Ree

theorem G2_smul_g2a_ia_ne_zero (w : WeylGroup .G2) :
    (w • g2a) g2ia ≠ 0 ∧ ((w • g2a) g2ia).natAbs ≤ 2 := by
  rcases g2_weyl_cases w with ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ |
    ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩
  all_goals rw [h1]; decide

theorem pow_eq_self_of_natCast_eq_one {G : Type*} [Monoid G] {x : G} {p N : ℕ} (hp : 1 < p)
    (hx : x ^ p = 1) (hN : (N : ZMod p) = 1) : x ^ N = x := by
  have h1 : N % p = 1 := by
    have := (ZMod.natCast_eq_natCast_iff' N 1 p).1 (by rw [hN, Nat.cast_one])
    rwa [Nat.one_mod_eq_one.2 hp.ne'] at this
  rw [← Nat.div_add_mod N p, h1, pow_add, pow_mul, hx, one_pow, one_mul, pow_one]

section Torus

variable (K : Type) [Field K] [Finite K] [CharP K ReeTag.G2.prime]

private def g2ExceptionalAut : MulAut (adjointGroup Tag.G2 K) :=
  ReeTag.G2.finiteExceptionalAut K

variable {K}

private theorem g2ExceptionalAut_xElement_ia (c : K) :
    g2ExceptionalAut K (xElement g2ia c) = xElement g2ir c := by
  have h := ReeTag.finiteExceptionalAut_xElement (t := ReeTag.G2) (K := K) g2ia c
  rw [show ReeTag.G2.perm g2ia = g2ir from rfl, show ReeTag.G2.exponent g2ia = 1 from rfl,
    pow_one] at h
  exact h

private theorem g2ExceptionalAut_xElement_ir (c : K) :
    g2ExceptionalAut K (xElement g2ir c) = xElement g2ia (c ^ 3) := by
  have h := ReeTag.finiteExceptionalAut_xElement (t := ReeTag.G2) (K := K) g2ir c
  rw [show ReeTag.G2.perm g2ir = g2ia from rfl, show ReeTag.G2.exponent g2ir = 3 from rfl] at h
  exact h

private theorem g2ExceptionalAut_mem_torusGroup {x : adjointGroup .G2 K}
    (hx : (x : ModGL .G2 K) ∈ torusGroup .G2 K) :
    ((g2ExceptionalAut K x : adjointGroup .G2 K) : ModGL .G2 K) ∈ torusGroup .G2 K := by
  have := ReeTag.finiteReeAut_mem_torusGroup (t := ReeTag.G2) (K := K) (a := 0) hx x.2
  rw [ReeTag.finiteReeAut, pow_zero, mul_one] at this
  exact this

private theorem g2ExceptionalAut_pow_two_mul_eq_one {f : ℕ} (hK : Nat.card K = 3 ^ f) :
    g2ExceptionalAut K ^ (2 * f) = 1 := by
  have h : ReeTag.G2.finiteExceptionalAut K ^ (2 * f) = 1 := by
    rw [finiteExceptionalAut_pow_two_mul]
    exact finiteFrobeniusAut_pow_card ReeTag.G2 hK
  exact h

private theorem g2ExceptionalAut_rootDiagUnit (b : Fin Tag.G2.rank → Kˣ)
    (hb : rootDiagUnit .G2 b ∈ adjointGroup .G2 K) :
    ((g2ExceptionalAut K ⟨rootDiagUnit .G2 b, hb⟩ : adjointGroup .G2 K) : ModGL .G2 K) =
      rootDiagUnit .G2 (g2PairTuple Kˣ (b g2ir ^ 3, b g2ia)) := by
  obtain ⟨b', hb'⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup
    (g2ExceptionalAut_mem_torusGroup (x := ⟨rootDiagUnit .G2 b, hb⟩)
      (rootDiagUnit_mem_torusGroup_G2 b))
  have hconj : ∀ (i : Fin Tag.G2.rank) (c : K),
      (⟨rootDiagUnit .G2 b, hb⟩ : adjointGroup .G2 K) * xElement i c *
        (⟨rootDiagUnit .G2 b, hb⟩ : adjointGroup .G2 K)⁻¹ = xElement i ((b i : K) * c) :=
    fun i c => Subtype.ext (by
      rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
      exact (root_diagonal_conjugation _ K b).1 i c)
  have himage : ∀ (i j : Fin Tag.G2.rank) (c : K) (e : ℕ),
      (∀ d : K, g2ExceptionalAut K (xElement i d) = xElement j (d ^ e)) →
        (b' j : K) * c ^ e = ((b i : K) * c) ^ e := by
    intro i j c e hφ
    have h2 := congrArg (fun g => ((g2ExceptionalAut K g : adjointGroup .G2 K) : ModGL .G2 K))
      (hconj i c)
    simp only [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv, hφ] at h2
    rw [hb'] at h2
    have h4 : xUnit .G2 K j ((b' j : K) * c ^ e) = xUnit .G2 K j (((b i : K) * c) ^ e) :=
      ((root_diagonal_conjugation .G2 K b').1 j (c ^ e)).symm.trans h2
    exact xOp_injective _ (congrArg Units.val h4)
  have h1 := himage g2ia g2ir 1 1 fun d => by rw [g2ExceptionalAut_xElement_ia, pow_one]
  have h2 := himage g2ir g2ia 1 3 g2ExceptionalAut_xElement_ir
  rw [one_pow, mul_one, mul_one, pow_one] at h1
  rw [one_pow, mul_one, mul_one] at h2
  rw [hb']
  refine congrArg (rootDiagUnit .G2) (funext fun j => ?_)
  rcases fin_G2_cases j with rfl | rfl
  · rw [g2PairTuple_ia]
    exact Units.ext (h2.trans (Units.val_pow_eq_pow_val _ _).symm)
  · rw [g2PairTuple_ir]
    exact Units.ext h1

private theorem g2ExceptionalAut_sq_apply {x : adjointGroup .G2 K}
    (hx : (x : ModGL .G2 K) ∈ torusGroup .G2 K) :
    (((g2ExceptionalAut K ^ 2) x : adjointGroup .G2 K) : ModGL .G2 K) =
      (x : ModGL .G2 K) ^ 3 := by
  obtain ⟨b, hb⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hx
  have hbC : rootDiagUnit .G2 b ∈ adjointGroup .G2 K := hb ▸ x.2
  obtain rfl : x = ⟨_, hbC⟩ := Subtype.ext hb
  have h1 := g2ExceptionalAut_rootDiagUnit b hbC
  have hbC1 : rootDiagUnit .G2 (g2PairTuple Kˣ (b g2ir ^ 3, b g2ia)) ∈ adjointGroup .G2 K :=
    h1 ▸ (g2ExceptionalAut K ⟨_, hbC⟩).2
  have h1' : g2ExceptionalAut K ⟨_, hbC⟩ = ⟨_, hbC1⟩ := Subtype.ext h1
  change _ = rootDiagUnit .G2 b ^ 3
  rw [sq, MulAut.mul_apply, h1', g2ExceptionalAut_rootDiagUnit, rootDiagUnit_pow]
  refine congrArg (rootDiagUnit .G2) (funext fun j => ?_)
  rcases fin_G2_cases j with rfl | rfl
  · simp only [g2PairTuple_ia, g2PairTuple_ir, Pi.pow_apply]
  · simp only [g2PairTuple_ia, g2PairTuple_ir, Pi.pow_apply]

private theorem g2ExceptionalAut_pow_two_mul_apply (j : ℕ) {x : adjointGroup .G2 K}
    (hx : (x : ModGL .G2 K) ∈ torusGroup .G2 K) :
    (((g2ExceptionalAut K ^ (2 * j)) x : adjointGroup .G2 K) : ModGL .G2 K) =
      (x : ModGL .G2 K) ^ 3 ^ j := by
  induction j with
  | zero => rw [mul_zero, pow_zero, pow_zero, pow_one, MulAut.one_apply]
  | succ j ih =>
    have hT : (((g2ExceptionalAut K ^ (2 * j)) x : adjointGroup .G2 K) : ModGL .G2 K) ∈
        torusGroup .G2 K := by
      rw [ih]
      exact pow_mem hx _
    rw [show 2 * (j + 1) = 2 + 2 * j by ring, pow_add, MulAut.mul_apply,
      g2ExceptionalAut_sq_apply hT, ih, ← pow_mul, ← pow_succ]

private theorem g2ExceptionalAut_pow_mem_torusTorsion {p : ℕ} (n : ℕ)
    {x : adjointGroup .G2 K} (hx : (x : ModGL .G2 K) ∈ torusTorsion K p) :
    (((g2ExceptionalAut K ^ n) x : adjointGroup .G2 K) : ModGL .G2 K) ∈ torusTorsion K p := by
  induction n with
  | zero => rwa [pow_zero, MulAut.one_apply]
  | succ n ih =>
    rw [pow_succ', MulAut.mul_apply]
    rw [mem_torusTorsion_iff] at ih ⊢
    refine ⟨g2ExceptionalAut_mem_torusGroup ih.1, ?_⟩
    have hy : ((g2ExceptionalAut K ^ n) x) ^ p = 1 :=
      Subtype.ext (by rw [SubgroupClass.coe_pow, ih.2, OneMemClass.coe_one])
    rw [← SubgroupClass.coe_pow, ← map_pow, hy, map_one, OneMemClass.coe_one]

private theorem G2_three_eq_two_mul_of_fix_torusTorsion {f : ℕ} (hK : Nat.card K = 3 ^ f)
    {p : ℕ} (hp : p.Prime) (hp3 : 3 < p) (hpq : p ∣ Nat.card K - 1) (y : adjointGroup .G2 K)
    (a : ℕ) (hfix : ∀ x : adjointGroup .G2 K, (x : ModGL .G2 K) ∈
      torusTorsion K p → (MulAut.conj y * g2ExceptionalAut K ^ a) x = x) :
    ∃ j, a = 2 * j ∧ ∃ h ∈ torusGroup .G2 K, ∃ w : WeylGroup .G2,
      (y : ModGL .G2 K) = h * canonicalRep (coxeterSystem .G2) K w ∧
      ((w = 1 ∧ (3 : ZMod p) ^ j = 1) ∨
        ((∀ v : Fin Tag.G2.rank → ℤ, w • v = -v) ∧ (3 : ZMod p) ^ j = -1)) := by
  have : Fact p.Prime := ⟨hp⟩
  have hTcomm := (triangular_borel_structure.{0, 0} .G2 K).1
  have hf : 1 ≤ f := by
    rcases Nat.eq_zero_or_pos f with rfl | h
    · have := Finite.one_lt_card (α := K)
      rw [hK, pow_zero] at this
      omega
    · exact h
  have hφ2f : g2ExceptionalAut K ^ (2 * f) = 1 := g2ExceptionalAut_pow_two_mul_eq_one hK
  have hVC : ∀ z ∈ torusTorsion K p, z ∈ adjointGroup .G2 K := fun z hz =>
    torusGroup_le_adjointGroup_G2 (torusTorsion_le_torusGroup p hz)
  have hfix' : ∀ x : adjointGroup .G2 K, (x : ModGL .G2 K) ∈ torusTorsion K p →
      (y : ModGL .G2 K) * ((g2ExceptionalAut K ^ a) x :
        ModGL .G2 K) * (y : ModGL .G2 K)⁻¹ = x := fun x hx => by
    have := congrArg Subtype.val (hfix x hx)
    rwa [MulAut.mul_apply, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_mul,
      Subgroup.coe_inv] at this
  have hconjV : ∀ z ∈ torusTorsion K p,
      (y : ModGL .G2 K) * z * (y : ModGL .G2 K)⁻¹ ∈ torusTorsion K p := by
    intro z hz
    obtain ⟨z', hz'⟩ : ∃ z', z' = (g2ExceptionalAut K ^ ((2 * f - 1) * a))
        ⟨z, hVC z hz⟩ := ⟨_, rfl⟩
    have hz'V : (z' : ModGL .G2 K) ∈ torusTorsion K p := by
      rw [hz']
      exact g2ExceptionalAut_pow_mem_torusTorsion _ hz
    have hzz : (g2ExceptionalAut K ^ a) z' = ⟨z, hVC z hz⟩ := by
      have e : a + (2 * f - 1) * a = 2 * f * a := by
        have h2f : 2 * f = (2 * f - 1) + 1 := by omega
        calc a + (2 * f - 1) * a = ((2 * f - 1) + 1) * a := by ring
          _ = 2 * f * a := by rw [← h2f]
      rw [hz', ← MulAut.mul_apply, ← pow_add, e, pow_mul, hφ2f, one_pow, MulAut.one_apply]
    have h1 := hfix' z' hz'V
    rw [hzz] at h1
    rw [h1]
    exact hz'V
  have hyN : (y : ModGL .G2 K) ∈
      adjointGroup .G2 K ⊓ Subgroup.normalizer (torusTorsion K p : Set (ModGL .G2 K)) := by
    refine Subgroup.mem_inf.2 ⟨y.2, Subgroup.mem_normalizer_iff.2 fun z => ⟨hconjV z, fun hz => ?_⟩⟩
    have hzC := hVC _ hz
    have h1 : (y : ModGL .G2 K) * ((g2ExceptionalAut K ^ a) ⟨_, hzC⟩ : ModGL .G2 K) *
        (y : ModGL .G2 K)⁻¹ = (y : ModGL .G2 K) * z * (y : ModGL .G2 K)⁻¹ := hfix' ⟨_, hzC⟩ hz
    rw [← mul_left_cancel (mul_right_cancel h1)]
    exact g2ExceptionalAut_pow_mem_torusTorsion (x := ⟨_, hzC⟩) a hz
  obtain ⟨h, hh, w, hyw⟩ := G2_exists_eq_mul_canonicalRep_of_mem_normalizer hp hp3 hpq hyN
  have hnN := canonicalRep_mem_normalizer (R := K) w
  obtain ⟨n, hn⟩ : ∃ n, canonicalRep (coxeterSystem .G2) K w = n := ⟨_, rfl⟩
  rw [hn] at hnN hyw
  have hact : ∀ x : adjointGroup .G2 K, (x : ModGL .G2 K) ∈ torusTorsion K p →
      (x : ModGL .G2 K) = n * ((g2ExceptionalAut K ^ a) x : ModGL .G2 K) * n⁻¹ := by
    intro x hx
    have h1 := hfix' x hx
    rw [hyw] at h1
    have hT : n * ((g2ExceptionalAut K ^ a) x : ModGL .G2 K) * n⁻¹ ∈
        torusGroup .G2 K := (Subgroup.mem_normalizer_iff.1 hnN _).1
      (torusTorsion_le_torusGroup p (g2ExceptionalAut_pow_mem_torusTorsion a hx))
    rw [← h1]
    calc h * n * ((g2ExceptionalAut K ^ a) x : ModGL .G2 K) * (h * n)⁻¹ =
        h * (n * ((g2ExceptionalAut K ^ a) x : ModGL .G2 K) * n⁻¹) * h⁻¹ := by
          group
      _ = _ := by rw [hTcomm h hh _ hT, mul_inv_cancel_right]
  obtain ⟨ζ, hζ⟩ := exists_units_orderOf_eq_of_dvd_card_sub_one hp hpq
  rcases Nat.even_or_odd' a with ⟨j, rfl | rfl⟩
  ·
    refine ⟨j, rfl, h, hh, w, by rw [hyw, hn], ?_⟩
    have h3 : ((3 : ZMod p) ^ j) ≠ 0 := pow_ne_zero _ (by
      have : ((3 : ℕ) : ZMod p) ≠ 0 := by
        rw [Ne, ZMod.natCast_eq_zero_iff]
        exact fun h => by have := Nat.le_of_dvd (by norm_num) h; omega
      exact_mod_cast this)
    set m : ZMod p := ((3 : ZMod p) ^ j)⁻¹ with hm
    have hconj : ∀ x ∈ torusTorsion K p, h * canonicalRep (coxeterSystem .G2) K w * x *
        (h * canonicalRep (coxeterSystem .G2) K w)⁻¹ = x ^ m.val := by
      intro x hx
      rw [hn]
      have hzV : x ^ m.val ∈ torusTorsion K p := pow_mem hx _
      have h1 := hact ⟨_, hVC _ hzV⟩ hzV
      rw [g2ExceptionalAut_pow_two_mul_apply j (torusTorsion_le_torusGroup p hzV)] at h1
      have e : (x ^ m.val) ^ 3 ^ j = x := by
        rw [← pow_mul]
        refine pow_eq_self_of_natCast_eq_one hp.one_lt (mem_torusTorsion_iff.1 hx).2 ?_
        rw [Nat.cast_mul, ZMod.natCast_zmod_val, Nat.cast_pow, hm, Nat.cast_ofNat,
          inv_mul_cancel₀ h3]
      change x ^ m.val = n * (x ^ m.val) ^ 3 ^ j * n⁻¹ at h1
      rw [e] at h1
      have hT : n * x * n⁻¹ ∈ torusGroup .G2 K :=
        (Subgroup.mem_normalizer_iff.1 hnN _).1 (torusTorsion_le_torusGroup p hx)
      rw [h1]
      calc h * n * x * (h * n)⁻¹ = h * (n * x * n⁻¹) * h⁻¹ := by group
        _ = n * x * n⁻¹ := by rw [hTcomm h hh _ hT, mul_inv_cancel_right]
    rcases G2_weyl_eq_one_or_neg_of_conj_eq_pow hp hp3 hpq hh w m hconj with
      ⟨hw, hm1⟩ | ⟨hw, hm1⟩
    · exact Or.inl ⟨hw, inv_eq_one.1 (hm ▸ hm1)⟩
    · exact Or.inr ⟨hw, by rw [← inv_inv ((3 : ZMod p) ^ j), ← hm, hm1, inv_neg_one]⟩
  ·
    exfalso
    have hxV := rootDiagUnit_mulSingle_mem_torusTorsion (k := K) hζ g2ia
    have h1 := hact ⟨_, hVC _ hxV⟩ hxV
    have hb : (Pi.mulSingle g2ia ζ : Fin Tag.G2.rank → Kˣ) ^ 3 ^ j =
        Pi.mulSingle g2ia (ζ ^ 3 ^ j) := (Pi.mulSingle_pow _ _ _).symm
    have h2j := g2ExceptionalAut_pow_two_mul_apply j
      (x := ⟨_, hVC _ hxV⟩) (torusTorsion_le_torusGroup p hxV)
    change _ = rootDiagUnit .G2 (Pi.mulSingle g2ia ζ) ^ 3 ^ j at h2j
    rw [rootDiagUnit_pow, hb] at h2j
    have hbC : rootDiagUnit .G2 (Pi.mulSingle g2ia (ζ ^ 3 ^ j)) ∈
        adjointGroup .G2 K := h2j ▸ ((g2ExceptionalAut K ^ (2 * j))
          ⟨_, hVC _ hxV⟩).2
    have h2j' : (g2ExceptionalAut K ^ (2 * j)) ⟨_, hVC _ hxV⟩ = ⟨_, hbC⟩ :=
      Subtype.ext h2j
    have hA := g2ExceptionalAut_rootDiagUnit (Pi.mulSingle g2ia (ζ ^ 3 ^ j)) hbC
    rw [pow_succ', MulAut.mul_apply, h2j', hA] at h1
    have h3 := (rootDiagUnit_eq_conj_canonicalRep_iff (τ := .G2) (K := K) _ _ w).1
      (by rw [hn]; exact h1) g2a
    rw [rootChar_mulSingle_eq_zpow, rootChar_G2, g2PairTuple_ia, g2PairTuple_ir,
      Pi.mulSingle_eq_of_ne (by decide), Pi.mulSingle_eq_same, one_pow, g2a_ia, g2a_ir, one_zpow,
      zpow_zero, mul_one, ← orderOf_dvd_iff_zpow_eq_one, hζ] at h3
    obtain ⟨h0, h2⟩ := G2_smul_g2a_ia_ne_zero w
    exact not_dvd_of_natAbs_lt h0 (by omega) h3

end Torus

theorem three_G2_toral_prime_plane_excludes_exceptional_odd_powers {f : ℕ} (K : Type) [Field K]
    [Finite K] [CharP K ReeTag.G2.prime] (hK : Nat.card K = 3 ^ f) {p : ℕ} (hp : p.Prime)
    (hp3 : 3 < p) (hpq : p ∣ Nat.card K - 1) :
    (∀ (η : MulAut (adjointGroup ReeTag.G2.tag K)) (y : adjointGroup ReeTag.G2.tag K) (a : ℕ),
      a < 2 * f → η = MulAut.conj y * ReeTag.G2.finiteExceptionalAut K ^ a →
      (∀ x : adjointGroup ReeTag.G2.tag K, (x : ModGL ReeTag.G2.tag K) ∈ torusTorsion K p →
        η x = x) →
      ∃ j, a = 2 * j ∧ j < f ∧
        ReeTag.G2.finiteExceptionalAut K ^ a = ReeTag.G2.finiteFrobeniusAut K ^ j ∧
        ∃ h ∈ torusGroup .G2 K, ∃ w : WeylGroup .G2,
          ((y : ModGL ReeTag.G2.tag K) : ModGL .G2 K) =
            h * canonicalRep (coxeterSystem .G2) K w ∧
          ((w = 1 ∧ (3 : ZMod p) ^ j = 1) ∨
            ((∀ v : Fin Tag.G2.rank → ℤ, w • v = -v) ∧ (3 : ZMod p) ^ j = -1))) ∧
    ∀ (y : adjointGroup ReeTag.G2.tag K) (a : ℕ), Odd a →
      ¬ ∀ x : adjointGroup ReeTag.G2.tag K, (x : ModGL ReeTag.G2.tag K) ∈ torusTorsion K p →
        (MulAut.conj y * ReeTag.G2.finiteExceptionalAut K ^ a) x = x := by
  refine ⟨fun η y a ha hη hfix => ?_, fun y a ha hfix => ?_⟩
  · subst hη
    obtain ⟨j, rfl, h, hh, w, hyw, hw⟩ := G2_three_eq_two_mul_of_fix_torusTorsion hK hp hp3 hpq y _
      hfix
    exact ⟨j, rfl, by omega, finiteExceptionalAut_pow_two_mul ReeTag.G2 j, h, hh, w, hyw, hw⟩
  · obtain ⟨j, rfl, -⟩ := G2_three_eq_two_mul_of_fix_torusTorsion hK hp hp3 hpq y a hfix
    exact Nat.not_odd_iff_even.2 (even_two_mul j) ha

end CFSG.RankThree.Chevalley
