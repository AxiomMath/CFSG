module

public import CFSG.RankThree.PartOne.KGD.D4Frame
public import CFSG.RankThree.PartOne.KGD.D4Weyl
public import CFSG.RankThree.Chevalley.SteinbergCFTrialityToralRoots
public import CFSG.RankThree.Chevalley.SteinbergCBTrialityOpposition
public import CFSG.RankThree.PartOne.KE.CTTwistedArith
public import Certificates.Certificate45
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate49
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate53
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate59
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate68
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate72
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate117
public import CFSG.LieType.Ree.LargeReeSylowOpposition
public import CFSG.Monster.B.Geometry.CoxeterWords
public import CFSG.RankThree.PartOne.KE.A1Action
public import CFSG.RankThree.PartOne.KE.A1Levi
public import CFSG.RankThree.PartOne.KE.A1Torus
public import CFSG.RankThree.PartOne.KE.A1TwistedE6
public import CFSG.RankThree.PartOne.KE.SigmaPerX
public import CFSG.RankThree.PartOne.KE.SigmaUntwisted

public noncomputable section

namespace CFSG.RankThree.PartOne.KGD

open CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.RankThree.Chevalley CFSG.RankThree.PartOne.KE
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open scoped Matrix Polynomial

section Torus

variable {L : Type} [Field L]

@[expose] def d4QM : Matrix (Fin TwistTag.D4.tag.rank) (Fin TwistTag.D4.tag.rank) ℤ :=
  Matrix.of fun i j => if TwistTag.D4.perm.symm i = j then -1 else 0

theorem d4QM_mulVec (y : Fin TwistTag.D4.tag.rank → ℤ) (i : Fin TwistTag.D4.tag.rank) :
    (d4QM *ᵥ y) i = -y (TwistTag.D4.perm.symm i) := by
  simp [d4QM, Matrix.mulVec, dotProduct, Finset.sum_ite_eq]

theorem d4QM_mulVec_permLattice (x : Fin TwistTag.D4.tag.rank → ℤ) :
    d4QM *ᵥ permLattice TwistTag.D4.perm.symm x = -x := by
  funext i
  rw [d4QM_mulVec]
  simp [permLattice]

theorem d4QM_mulVec_single (j : Fin TwistTag.D4.tag.rank) :
    d4QM *ᵥ (Pi.single j 1 : Fin TwistTag.D4.tag.rank → ℤ) =
      -(Pi.single (TwistTag.D4.perm j) 1 : Fin TwistTag.D4.tag.rank → ℤ) := by
  funext i
  rw [d4QM_mulVec]
  simp only [Pi.neg_apply, Pi.single_apply, Equiv.symm_apply_eq]

theorem d4Q_weylImage (x : Fin TwistTag.D4.tag.rank → ℤ) :
    weylQuotientHom TwistTag.D4.tag L ⟨trialityOpposition L, trialityOpposition_mem_monomialSubgroup⟩ •
        x = d4QM *ᵥ permLattice TwistTag.D4.perm.symm x := by
  rw [d4QM_mulVec_permLattice]
  exact weylQuotientHom_trialityOpposition_smul x

variable {Fr : L →+* L} {q : ℕ}

theorem d4Q_rootChar_neg (a : Fin TwistTag.D4.tag.rank → Lˣ) (β : Fin TwistTag.D4.tag.rank → ℤ) :
    rootChar a (-β) = (rootChar a β)⁻¹ := by
  rw [eq_inv_iff_mul_eq_one, ← rootChar_add, neg_add_cancel, rootChar_zero]

theorem mem_fixedCharTuples_d4QM (hFr : ∀ c, Fr c = c ^ q) (a : Fin TwistTag.D4.tag.rank → Lˣ) :
    a ∈ fixedCharTuples d4QM Fr ↔ ∀ j, a (TwistTag.D4.perm j) = (a j ^ q)⁻¹ := by
  rw [mem_fixedCharTuples_iff]
  constructor
  · intro h j
    have h1 := h (Pi.single j 1)
    rw [d4QM_mulVec_single, d4Q_rootChar_neg, CTTorus.rootChar_single, CTTorus.rootChar_single,
      CTTorus.map_units_eq_pow hFr] at h1
    exact inv_eq_iff_eq_inv.1 h1
  · intro h u
    have e1 : rootChar a (d4QM *ᵥ u) = ∏ j, (a (TwistTag.D4.perm j) ^ (-u j)) := by
      rw [rootChar]
      refine (Equiv.prod_comp TwistTag.D4.perm
        (fun i => a i ^ (d4QM *ᵥ u) i)).symm.trans ?_
      refine Finset.prod_congr rfl fun j _ => ?_
      simp only [d4QM_mulVec, Equiv.symm_apply_apply]
    have e2 : Units.map Fr.toMonoidHom (rootChar a u) = ∏ j, (a j ^ (u j)) ^ q := by
      rw [CTTorus.map_units_eq_pow hFr, rootChar, Finset.prod_pow]
    rw [e1, e2]
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [h j, _root_.inv_zpow', neg_neg, ← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul,
      mul_comm]

end Torus

section Card

open CFSG.RankThree.Chevalley.TrialityFold

variable {L : Type} [Field L] {Fr : L →+* L} {q : ℕ}

@[expose] def d4QCoord : (Fin TwistTag.D4.tag.rank → Lˣ) →* (Fin 2 → Lˣ) where
  toFun a := ![a i0, a i2]
  map_one' := by
    funext k
    fin_cases k <;> rfl
  map_mul' a b := by
    funext k
    fin_cases k <;> rfl

theorem d4QCoord_apply (a : Fin TwistTag.D4.tag.rank → Lˣ) : d4QCoord a = ![a i0, a i2] := rfl

theorem perm_i2 : TwistTag.D4.perm i2 = i2 :=
  ((Equiv.symm_apply_eq _).1 perm_symm_i2).symm

theorem perm_i3 : TwistTag.D4.perm i3 = i0 :=
  ((Equiv.symm_apply_eq _).1 perm_symm_i0).symm

section Tuple

variable (hFr : ∀ c, Fr c = c ^ q) {a : Fin TwistTag.D4.tag.rank → Lˣ}
  (ha : a ∈ fixedCharTuples d4QM Fr)
include hFr ha

theorem d4Q_a1 : a i1 = (a i0 ^ q)⁻¹ := by
  have := (mem_fixedCharTuples_d4QM hFr a).1 ha i0
  rwa [perm_i0] at this

theorem d4Q_a3 : a i3 = (a i1 ^ q)⁻¹ := by
  have := (mem_fixedCharTuples_d4QM hFr a).1 ha i1
  rwa [perm_i1] at this

theorem d4Q_a0 : a i0 = (a i3 ^ q)⁻¹ := by
  have := (mem_fixedCharTuples_d4QM hFr a).1 ha i3
  rwa [perm_i3] at this

theorem d4Q_a2 : a i2 = (a i2 ^ q)⁻¹ := by
  have := (mem_fixedCharTuples_d4QM hFr a).1 ha i2
  rwa [perm_i2] at this

theorem d4Q_pow2 : a i2 ^ (q + 1) = 1 := by
  rw [pow_succ']
  nth_rewrite 1 [d4Q_a2 hFr ha]
  exact inv_mul_cancel _

theorem d4Q_pow0 : a i0 ^ (q ^ 3 + 1) = 1 := by
  have h3 : a i3 = a i0 ^ (q * q) := by
    rw [d4Q_a3 hFr ha, d4Q_a1 hFr ha, inv_pow, ← pow_mul, inv_inv]
  have h0 : a i0 = (a i0 ^ (q * q * q))⁻¹ := by
    nth_rewrite 1 [d4Q_a0 hFr ha]
    rw [h3, ← pow_mul]
  rw [pow_succ']
  have : q ^ 3 = q * q * q := by ring
  rw [this]
  nth_rewrite 1 [h0]
  exact inv_mul_cancel _

end Tuple

theorem eq_of_d4QCoord_eq (hFr : ∀ c, Fr c = c ^ q) {a b : Fin TwistTag.D4.tag.rank → Lˣ}
    (ha : a ∈ fixedCharTuples d4QM Fr) (hb : b ∈ fixedCharTuples d4QM Fr)
    (h : d4QCoord a = d4QCoord b) : a = b := by
  rw [d4QCoord_apply, d4QCoord_apply] at h
  have h0 : a i0 = b i0 := congrFun h 0
  have h2 : a i2 = b i2 := congrFun h 1
  have h1 : a i1 = b i1 := by rw [d4Q_a1 hFr ha, d4Q_a1 hFr hb, h0]
  have h3 : a i3 = b i3 := by rw [d4Q_a3 hFr ha, d4Q_a3 hFr hb, h1]
  funext j
  rcases fin_cases j with rfl | rfl | rfl | rfl <;> assumption

@[expose] def d4QTuple (q : ℕ) (b c : Lˣ) : Fin TwistTag.D4.tag.rank → Lˣ :=
  CFSG.LieType.Chevalley.d4Tuple c (c ^ q)⁻¹ b (c ^ (q * q))

theorem d4QTuple_mem (hFr : ∀ c, Fr c = c ^ q) {b c : Lˣ} (hb : b ^ (q + 1) = 1)
    (hc : c ^ (q ^ 3 + 1) = 1) : d4QTuple q b c ∈ fixedCharTuples d4QM Fr := by
  rw [mem_fixedCharTuples_d4QM hFr]
  intro j
  rcases fin_cases j with rfl | rfl | rfl | rfl
  · rw [perm_i0]; rfl
  · rw [perm_i1]
    change c ^ (q * q) = (((c ^ q)⁻¹) ^ q)⁻¹
    rw [inv_pow, ← pow_mul, inv_inv]
  · rw [perm_i2]
    change b = (b ^ q)⁻¹
    rw [eq_inv_iff_mul_eq_one, ← pow_succ']
    exact hb
  · rw [perm_i3]
    change c = ((c ^ (q * q)) ^ q)⁻¹
    rw [← pow_mul, eq_inv_iff_mul_eq_one, ← pow_succ']
    have : q * q * q + 1 = q ^ 3 + 1 := by ring
    rw [this]
    exact hc

theorem d4QTuple_coord (b c : Lˣ) : d4QCoord (d4QTuple q b c) = ![c, b] := by
  rw [d4QCoord_apply]
  rfl

theorem d4Q_card [IsAlgClosed L] {ℓ : ℕ} [CharP L ℓ] (hℓq : ℓ ∣ q)
    (hFr : ∀ c, Fr c = c ^ q) :
    Nat.card (fixedCharTuples d4QM Fr) = (q + 1) * (q ^ 3 + 1) := by
  have hq0 : (q : L) = 0 := (CharP.cast_eq_zero_iff L ℓ q).2 hℓq
  have : NeZero (((q + 1 : ℕ)) : L) := ⟨by push_cast; rw [hq0]; simp⟩
  have : NeZero (((q ^ 3 + 1 : ℕ)) : L) := ⟨by push_cast; rw [hq0]; simp⟩
  let φ₁ : fixedCharTuples d4QM Fr →* rootsOfUnity (q + 1) L :=
    ((Pi.evalMonoidHom (fun _ => Lˣ) i2).comp (fixedCharTuples d4QM Fr).subtype).codRestrict _
      fun a => by
        rw [mem_rootsOfUnity]
        exact d4Q_pow2 hFr a.2
  let φ₂ : fixedCharTuples d4QM Fr →* rootsOfUnity (q ^ 3 + 1) L :=
    ((Pi.evalMonoidHom (fun _ => Lˣ) i0).comp (fixedCharTuples d4QM Fr).subtype).codRestrict _
      fun a => by
        rw [mem_rootsOfUnity]
        exact d4Q_pow0 hFr a.2
  have hbij : Function.Bijective (φ₁.prod φ₂) := by
    constructor
    · intro a a' h
      have h1 := congrArg (fun z => ((z.1 : Lˣ))) h
      have h2 := congrArg (fun z => ((z.2 : Lˣ))) h
      refine Subtype.ext (eq_of_d4QCoord_eq hFr a.2 a'.2 ?_)
      rw [d4QCoord_apply, d4QCoord_apply]
      funext k
      fin_cases k
      · exact h2
      · exact h1
    · rintro ⟨⟨b, hb⟩, ⟨c, hc⟩⟩
      rw [mem_rootsOfUnity] at hb hc
      exact ⟨⟨d4QTuple q b c, d4QTuple_mem hFr hb hc⟩, rfl⟩
  rw [Nat.card_congr (Equiv.ofBijective _ hbij), Nat.card_prod,
    HasEnoughRootsOfUnity.natCard_rootsOfUnity L (q + 1),
    HasEnoughRootsOfUnity.natCard_rootsOfUnity L (q ^ 3 + 1)]

theorem d4Q_eq_of_pow_eq_one (hFr : ∀ c, Fr c = c ^ q) {p : ℕ} (hpq : p ∣ q + 1)
    {a : Fin TwistTag.D4.tag.rank → Lˣ} (ha : a ∈ fixedCharTuples d4QM Fr)
    (hap : ∀ i, a i ^ p = 1) : a i1 = a i0 ∧ a i3 = a i0 := by
  have hinv : ∀ i, (a i ^ q)⁻¹ = a i := fun i => by
    have h1 : a i ^ (q + 1) = 1 := by
      obtain ⟨k, hk⟩ := hpq
      rw [hk, pow_mul, hap i, one_pow]
    rw [inv_eq_iff_eq_inv, eq_inv_iff_mul_eq_one, ← pow_succ]
    exact h1
  have h1 : a i1 = a i0 := by rw [d4Q_a1 hFr ha, hinv]
  exact ⟨h1, by rw [d4Q_a3 hFr ha, hinv, h1]⟩

end Card

theorem d4Q_ordProj {p q : ℕ} (hp : p.Prime) (hp3 : 3 < p) (hq : 2 ≤ q)
    (hpq : (p : ℤ) ∣ (q : ℤ) + 1) :
    p ^ (q ^ 12 * (q ^ 2 - 1) * (q ^ 6 - 1) * (q ^ 8 + q ^ 4 + 1)).factorization p =
      p ^ ((q + 1) * (q ^ 3 + 1)).factorization p := by
  have hn₀ : (q + 1) * (q ^ 3 + 1) ≠ 0 := by positivity
  have hcof := CTTw.ordProj_eq_of_int_cofactor (p := p)
    (N := q ^ 12 * (q ^ 2 - 1) * (q ^ 6 - 1) * (q ^ 8 + q ^ 4 + 1))
    (n := (q + 1) * (q ^ 3 + 1)) hn₀
    (R := (q : ℤ) ^ 12 * ((q : ℤ) - 1) * ((q : ℤ) ^ 3 - 1) * ((q : ℤ) ^ 8 + (q : ℤ) ^ 4 + 1))
    (by
      simp only [Nat.cast_mul, CTTw.cast_pow_sub_one (by omega : 1 ≤ q), Nat.cast_add,
        Nat.cast_pow, Nat.cast_one]
      ring)
    (by
      intro hdvd
      have hfac : (q : ℤ) ^ 12 * ((q : ℤ) - 1) * ((q : ℤ) ^ 3 - 1) *
          ((q : ℤ) ^ 8 + (q : ℤ) ^ 4 + 1) - 12 = ((q : ℤ) + 1) *
          ((q : ℤ) ^ 23 - 2 * (q : ℤ) ^ 22 + 2 * (q : ℤ) ^ 21 - 3 * (q : ℤ) ^ 20 +
            5 * (q : ℤ) ^ 19 - 6 * (q : ℤ) ^ 18 + 6 * (q : ℤ) ^ 17 - 7 * (q : ℤ) ^ 16 +
            9 * (q : ℤ) ^ 15 - 10 * (q : ℤ) ^ 14 + 10 * (q : ℤ) ^ 13 - 11 * (q : ℤ) ^ 12 +
            12 * (q : ℤ) ^ 11 - 12 * (q : ℤ) ^ 10 + 12 * (q : ℤ) ^ 9 - 12 * (q : ℤ) ^ 8 +
            12 * (q : ℤ) ^ 7 - 12 * (q : ℤ) ^ 6 + 12 * (q : ℤ) ^ 5 - 12 * (q : ℤ) ^ 4 +
            12 * (q : ℤ) ^ 3 - 12 * (q : ℤ) ^ 2 + 12 * (q : ℤ) - 12) := by ring
      have h1 := dvd_sub hdvd (hfac ▸ dvd_mul_of_dvd_left hpq _)
      rw [sub_sub_cancel] at h1
      have hd12 : p ∣ 12 := Int.natCast_dvd_natCast.1 (by exact_mod_cast h1)
      have hle := Nat.le_of_dvd (by norm_num) hd12
      interval_cases p <;> first | omega | norm_num at hp)
  exact hcof

end CFSG.RankThree.PartOne.KGD
