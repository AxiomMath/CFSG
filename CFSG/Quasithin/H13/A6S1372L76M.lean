module

public import CFSG.Quasithin.H13.A6S1372L76L

public section

namespace CFSG.Quasithin.H13.A6

open Equiv CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open CFSG.QuasithinUnique.Bridge
open scoped Pointwise IsMulCommutative

namespace A6L76M

variable {F : Type} [Field F] {n : ℕ}

theorem add_self_eq (h2 : (2 : F) = 0) (a : F) : a + a = 0 := by
  rw [← two_mul, h2, zero_mul]

theorem mat_ext {M N : Matrix (Fin n) (Fin n) F} (h : ∀ v, M.mulVec v = N.mulVec v) : M = N :=
  Matrix.toLin'.injective (LinearMap.ext fun v => by
    rw [Matrix.toLin'_apply, Matrix.toLin'_apply]
    exact h v)

theorem transvection_mulVec (i j : Fin n) (c : F) (v : Fin n → F) :
    (Matrix.transvection i j c).mulVec v = Function.update v i (v i + c * v j) := by
  rw [Matrix.transvection, Matrix.add_mulVec, Matrix.one_mulVec, Matrix.single_mulVec]
  funext k
  by_cases hk : k = i
  · subst hk
    simp
  · simp [hk]

@[expose] def rot (p q : Fin n) : Matrix (Fin n) (Fin n) F :=
  Matrix.transvection p q 1 * Matrix.transvection q p 1

theorem det_rot {p q : Fin n} (h : p ≠ q) : (rot p q : Matrix (Fin n) (Fin n) F).det = 1 := by
  rw [rot, Matrix.det_mul, Matrix.det_transvection_of_ne _ _ h,
    Matrix.det_transvection_of_ne _ _ (Ne.symm h), one_mul]

@[expose] def rotF (p q : Fin n) (v : Fin n → F) : Fin n → F :=
  Function.update (Function.update v q (v p + v q)) p (v q)

theorem rotF_p (p q : Fin n) (v : Fin n → F) : rotF p q v p = v q := by
  simp [rotF]

theorem rotF_q {p q : Fin n} (h : p ≠ q) (v : Fin n → F) : rotF p q v q = v p + v q := by
  simp [rotF, Function.update_of_ne (Ne.symm h)]

theorem rotF_other {p q k : Fin n} (hkp : k ≠ p) (hkq : k ≠ q) (v : Fin n → F) :
    rotF p q v k = v k := by
  simp [rotF, Function.update_of_ne hkp, Function.update_of_ne hkq]

theorem rot_mulVec (h2 : (2 : F) = 0) {p q : Fin n} (h : p ≠ q) (v : Fin n → F) :
    (rot p q).mulVec v = rotF p q v := by
  rw [rot, ← Matrix.mulVec_mulVec, transvection_mulVec, transvection_mulVec]
  funext k
  by_cases hkp : k = p
  · subst hkp
    rw [rotF_p, Function.update_self, Function.update_of_ne h, Function.update_self, one_mul,
      one_mul]
    linear_combination (v k) * h2
  · by_cases hkq : k = q
    · subst hkq
      rw [rotF_q h, Function.update_of_ne hkp, Function.update_self, one_mul, add_comm]
    · rw [rotF_other hkp hkq, Function.update_of_ne hkp, Function.update_of_ne hkq]

theorem rotF_three (h2 : (2 : F) = 0) {p q : Fin n} (h : p ≠ q) (v : Fin n → F) :
    rotF p q (rotF p q (rotF p q v)) = v := by
  funext k
  by_cases hkp : k = p
  · subst hkp
    rw [rotF_p, rotF_q h, rotF_p, rotF_q h]
    linear_combination (v q) * h2
  · by_cases hkq : k = q
    · subst hkq
      rw [rotF_q h, rotF_p, rotF_q h, rotF_q h, rotF_p, rotF_q h]
      linear_combination (v p + v k) * h2
    · rw [rotF_other hkp hkq, rotF_other hkp hkq, rotF_other hkp hkq]

theorem rotF_comm {p q r s : Fin n} (hpq : p ≠ q) (hrs : r ≠ s) (hpr : p ≠ r) (hps : p ≠ s)
    (hqr : q ≠ r) (hqs : q ≠ s) (v : Fin n → F) :
    rotF p q (rotF r s v) = rotF r s (rotF p q v) := by
  funext k
  by_cases hkp : k = p
  · subst hkp
    rw [rotF_p, rotF_other hqr hqs, rotF_other hpr hps, rotF_p]
  · by_cases hkq : k = q
    · subst hkq
      rw [rotF_q hpq, rotF_other hpr hps, rotF_other hqr hqs, rotF_other hqr hqs, rotF_q hpq]
    · by_cases hkr : k = r
      · subst hkr
        rw [rotF_other hkp hkq, rotF_p, rotF_p, rotF_other (Ne.symm hps) (Ne.symm hqs)]
      · by_cases hks : k = s
        · subst hks
          rw [rotF_other hkp hkq, rotF_q hrs, rotF_q hrs, rotF_other (Ne.symm hpr) (Ne.symm hqr),
            rotF_other hkp hkq]
        · rw [rotF_other hkp hkq, rotF_other hkr hks, rotF_other hkr hks, rotF_other hkp hkq]

theorem rotF_single_of_ne {p q k : Fin n} (hkp : k ≠ p) (hkq : k ≠ q) :
    rotF p q (Pi.single k (1 : F)) = Pi.single k 1 := by
  funext j
  by_cases hjp : j = p
  · subst hjp
    rw [rotF_p, Pi.single_eq_of_ne (Ne.symm hkq), Pi.single_eq_of_ne (Ne.symm hkp)]
  · by_cases hjq : j = q
    · subst hjq
      rw [rotF_q (Ne.symm hjp), Pi.single_eq_of_ne (Ne.symm hkp),
        Pi.single_eq_of_ne (Ne.symm hkq), add_zero]
    · rw [rotF_other hjp hjq]

@[expose] noncomputable def slOf (M : Matrix (Fin n) (Fin n) F) (hM : M.det = 1) :
    ↥(CFSG.Assembly.LowTwoRank.StatedSL n F) :=
  ⟨Matrix.SpecialLinearGroup.toGL ⟨M, hM⟩, Subgroup.subset_closure
    (show (Matrix.SpecialLinearGroup.toGL ⟨M, hM⟩ : GL (Fin n) F) ∈
      {A : GL (Fin n) F | (A : Matrix (Fin n) (Fin n) F).det = 1} from hM)⟩

theorem slOf_val (M : Matrix (Fin n) (Fin n) F) (hM : M.det = 1) :
    (((slOf M hM : ↥(CFSG.Assembly.LowTwoRank.StatedSL n F)) : GL (Fin n) F) :
      Matrix (Fin n) (Fin n) F) = M := rfl

theorem val_mul (a b : ↥(CFSG.Assembly.LowTwoRank.StatedSL n F)) :
    (((a * b : ↥(CFSG.Assembly.LowTwoRank.StatedSL n F)) : GL (Fin n) F) :
      Matrix (Fin n) (Fin n) F) = ((a : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) *
        ((b : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) := rfl

theorem ext_val {a b : ↥(CFSG.Assembly.LowTwoRank.StatedSL n F)}
    (h : ∀ v, ((a : GL (Fin n) F) : Matrix (Fin n) (Fin n) F).mulVec v =
      ((b : GL (Fin n) F) : Matrix (Fin n) (Fin n) F).mulVec v) : a = b :=
  Subtype.ext (Units.ext (mat_ext h))

theorem e9_rot (h2 : (2 : F) = 0) {p q r s : Fin n} (hpq : p ≠ q) (hrs : r ≠ s) (hpr : p ≠ r)
    (hps : p ≠ s) (hqr : q ≠ r) (hqs : q ≠ s) :
    A6L76B.E9Pair (slOf (rot p q : Matrix (Fin n) (Fin n) F) (det_rot hpq))
      (slOf (rot r s : Matrix (Fin n) (Fin n) F) (det_rot hrs)) := by
  have ha : ∀ v, (rot p q : Matrix (Fin n) (Fin n) F).mulVec v = rotF p q v := rot_mulVec h2 hpq
  have hb : ∀ v, (rot r s : Matrix (Fin n) (Fin n) F).mulVec v = rotF r s v := rot_mulVec h2 hrs
  have hcube : ∀ (x : ↥(CFSG.Assembly.LowTwoRank.StatedSL n F)) (f : (Fin n → F) → Fin n → F),
      (∀ v, ((x : GL (Fin n) F) : Matrix (Fin n) (Fin n) F).mulVec v = f v) →
      (∀ v, f (f (f v)) = v) → x ^ 3 = 1 := by
    intro x f hx hf
    refine ext_val fun v => ?_
    rw [pow_three, val_mul, val_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hx, hx, hx,
      hf]
    exact (Matrix.one_mulVec v).symm
  have hp1 : (Pi.single p (1 : F) : Fin n → F) p ≠ (Pi.single p (1 : F) : Fin n → F) q := by
    rw [Pi.single_eq_same, Pi.single_eq_of_ne (Ne.symm hpq)]
    exact one_ne_zero
  refine ⟨ext_val fun v => ?_, hcube _ _ ha (rotF_three h2 hpq),
    hcube _ _ hb (rotF_three h2 hrs), fun e => ?_, fun e => ?_, fun e => ?_, fun e => ?_⟩
  · rw [val_mul, val_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    simp only [slOf_val, ha, hb]
    exact rotF_comm hpq hrs hpr hps hqr hqs v
  · have h1 := congrArg (fun x : ↥(CFSG.Assembly.LowTwoRank.StatedSL n F) =>
      ((x : GL (Fin n) F) : Matrix (Fin n) (Fin n) F).mulVec (Pi.single p 1) p) e
    simp only [slOf_val, ha, OneMemClass.coe_one, Units.val_one, Matrix.one_mulVec,
      rotF_p] at h1
    exact hp1 h1.symm
  · have h1 := congrArg (fun x : ↥(CFSG.Assembly.LowTwoRank.StatedSL n F) =>
      ((x : GL (Fin n) F) : Matrix (Fin n) (Fin n) F).mulVec (Pi.single r 1) r) e
    simp only [slOf_val, hb, OneMemClass.coe_one, Units.val_one, Matrix.one_mulVec,
      rotF_p] at h1
    rw [Pi.single_eq_same, Pi.single_eq_of_ne (Ne.symm hrs)] at h1
    exact zero_ne_one h1
  · have h1 := congrArg (fun x : ↥(CFSG.Assembly.LowTwoRank.StatedSL n F) =>
      ((x : GL (Fin n) F) : Matrix (Fin n) (Fin n) F).mulVec (Pi.single p 1) p) e
    simp only [slOf_val, ha, hb, rotF_single_of_ne hpr hps, rotF_p] at h1
    exact hp1 h1
  · have h1 := congrArg (fun x : ↥(CFSG.Assembly.LowTwoRank.StatedSL n F) =>
      ((x : GL (Fin n) F) : Matrix (Fin n) (Fin n) F).mulVec (Pi.single p 1) q) e
    simp only [val_mul, ← Matrix.mulVec_mulVec, slOf_val, ha, hb, rotF_single_of_ne hpr hps,
      rotF_q hpq, rotF_p] at h1
    rw [Pi.single_eq_same, Pi.single_eq_of_ne (Ne.symm hpq)] at h1
    norm_num at h1

theorem det_updateCol_one (i₀ : Fin n) (x : Fin n → F) :
    (Matrix.updateCol (1 : Matrix (Fin n) (Fin n) F) i₀ x).det = x i₀ := by
  rw [← Matrix.cramer_apply, Matrix.cramer_one]
  rfl

theorem updateCol_one_mulVec_single (i₀ : Fin n) (x : Fin n → F) :
    (Matrix.updateCol (1 : Matrix (Fin n) (Fin n) F) i₀ x).mulVec (Pi.single i₀ 1) = x := by
  funext k
  simp [Matrix.mulVec, dotProduct, Matrix.updateCol_apply, Pi.single_apply]

theorem eq_one_of_ne_zero (hF : Nat.card F = 2) [Finite F] {a : F} (ha : a ≠ 0) : a = 1 := by
  have := Fintype.ofFinite F
  have h := FiniteField.pow_card_sub_one_eq_one a ha
  rwa [Fintype.card_eq_nat_card, hF, show 2 - 1 = 1 from rfl, pow_one] at h

theorem two_eq_zero (hF : Nat.card F = 2) [Finite F] : (2 : F) = 0 := by
  have := Fintype.ofFinite F
  have h := FiniteField.cast_card_eq_zero F
  rwa [Fintype.card_eq_nat_card, hF, Nat.cast_ofNat] at h

theorem exists_e9_fix [Finite F] (hF : Nat.card F = 2) (hn : 5 ≤ n) (x : Fin n → F)
    (hx : x ≠ 0) : ∃ a b : ↥(CFSG.Assembly.LowTwoRank.StatedSL n F), A6L76B.E9Pair a b ∧
      ((a : GL (Fin n) F) : Matrix (Fin n) (Fin n) F).mulVec x = x ∧
      ((b : GL (Fin n) F) : Matrix (Fin n) (Fin n) F).mulVec x = x := by
  have h2 := two_eq_zero hF
  obtain ⟨i₀, hi₀⟩ : ∃ i, x i ≠ 0 := Function.ne_iff.1 hx
  have hx1 : x i₀ = 1 := eq_one_of_ne_zero hF hi₀
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  let e : Fin 4 → Fin (m + 1) := fun k => i₀.succAbove (Fin.castLE (by omega) k)
  have he : Function.Injective e := fun a b h =>
    Fin.castLE_injective _ (Fin.succAbove_right_injective h)
  have hne : ∀ k, e k ≠ i₀ := fun k => Fin.succAbove_ne _ _
  have h01 : e 0 ≠ e 1 := fun h => absurd (he h) (by decide)
  have h23 : e 2 ≠ e 3 := fun h => absurd (he h) (by decide)
  have h02 : e 0 ≠ e 2 := fun h => absurd (he h) (by decide)
  have h03 : e 0 ≠ e 3 := fun h => absurd (he h) (by decide)
  have h12 : e 1 ≠ e 2 := fun h => absurd (he h) (by decide)
  have h13 : e 1 ≠ e 3 := fun h => absurd (he h) (by decide)
  have hQ : (Matrix.updateCol (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) F) i₀ x).det = 1 := by
    rw [det_updateCol_one, hx1]
  set q := slOf _ hQ with hq
  have hqx : ((q : GL (Fin (m + 1)) F) : Matrix (Fin (m + 1)) (Fin (m + 1)) F).mulVec
      (Pi.single i₀ 1) = x := updateCol_one_mulVec_single i₀ x
  have hqi : ((q⁻¹ : ↥(CFSG.Assembly.LowTwoRank.StatedSL (m + 1) F)) :
      GL (Fin (m + 1)) F).val.mulVec x = Pi.single i₀ 1 := by
    rw [← hqx, Matrix.mulVec_mulVec]
    have : ((q⁻¹ : ↥(CFSG.Assembly.LowTwoRank.StatedSL (m + 1) F)) : GL (Fin (m + 1)) F).val *
        ((q : GL (Fin (m + 1)) F) : Matrix (Fin (m + 1)) (Fin (m + 1)) F) = 1 := by
      rw [← val_mul, inv_mul_cancel]
      rfl
    rw [this, Matrix.one_mulVec]
  have hE := (e9_rot h2 h01 h23 h02 h03 h12 h13).map (MulAut.conj q).toMonoidHom
    (MulAut.conj q).injective
  refine ⟨_, _, hE, ?_, ?_⟩
  · show ((q * slOf (rot (e 0) (e 1)) (det_rot h01) * q⁻¹ :
      ↥(CFSG.Assembly.LowTwoRank.StatedSL (m + 1) F)) : GL (Fin (m + 1)) F).val.mulVec x = x
    rw [val_mul, val_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hqi,
      slOf_val (rot (e 0) (e 1) : Matrix (Fin (m + 1)) (Fin (m + 1)) F) (det_rot h01),
      rot_mulVec h2 h01, rotF_single_of_ne (Ne.symm (hne 0)) (Ne.symm (hne 1))]
    exact hqx
  · show ((q * slOf (rot (e 2) (e 3)) (det_rot h23) * q⁻¹ :
      ↥(CFSG.Assembly.LowTwoRank.StatedSL (m + 1) F)) : GL (Fin (m + 1)) F).val.mulVec x = x
    rw [val_mul, val_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hqi,
      slOf_val (rot (e 2) (e 3) : Matrix (Fin (m + 1)) (Fin (m + 1)) F) (det_rot h23),
      rot_mulVec h2 h23, rotF_single_of_ne (Ne.symm (hne 2)) (Ne.symm (hne 3))]
    exact hqx

end A6L76M

namespace Setting4

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} (S : Setting4 G T L V)
include S

theorem exists_ctx (h37 : A37ForSQTK) (h38 : A38ForSQTK)
    (h13315 : Stmt13_3_15) (h1356two : Input1356Two) (hNS : ¬ LieModel G .PSp 3 2 1)
    {H : Subgroup G} (hH : H ∈ S.Hz) (hab : IsElemAbelian 2 (conjClosure S.V3 H))
    [IsMulCommutative ↥(conjClosure S.V3 H)] {K : Subgroup G} (hK : K ∈ cComp H)
    (hL1K : S.L1 ≤ K) {D : FFModel} [IsSimpleGroup D.Gam] (hD : ¬ Group.IsSolvable D.Gam)
    (hR : D.Realizes (autSec (autOn K (conjClosure S.V3 H)) ⊤
        ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)))
      (commV (autSec (autOn K (conjClosure S.V3 H)) ⊤
        ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))))
      (fixV (autSec (autOn K (conjClosure S.V3 H)) ⊤
          ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))) ⊓
        commV (autSec (autOn K (conjClosure S.V3 H)) ⊤
          ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))))) :
    Nonempty (S.Ctx76 H K D) := by
  obtain ⟨π, β, hR⟩ := (CFSG.Quasithin.H.Mathieu.realizes_iff _ _ _ _).1 hR
  have hKH : K ≤ H := le_of_mem_cComp hK
  have := S.nontrivial_tilde_of_L1_le hH hKH hL1K
  have hπ := A6L76L.injective_of_simple π hR.1
  have hrad := A6L76A.rad_eq_bot_of_surjective hD π hR.1
  have hHK := S.le_normalizer_of_L1_le hH h37 h38 hK hL1K hrad
  have hUK := S.commutator_UH_eq_of_L1_le hKH hHK hL1K
  exact ⟨⟨hNS, h13315, h1356two, hH, hab, hK, hL1K, hHK, hUK, π, β, hR, hπ⟩⟩

variable {S}

namespace Ctx76

variable {H K : Subgroup G} [IsMulCommutative ↥(conjClosure S.V3 H)]

theorem false_nat_ge_five (h13314 : Stmt13_3_14) {F : Type}
    [Field F] [Finite F] (hF : Nat.card F = 2) {n : ℕ} (hn : 5 ≤ n)
    (C : S.Ctx76 H K (FFModel.nat (CFSG.Assembly.LowTwoRank.StatedSL n F))) : False := by
  obtain ⟨m, hxm⟩ := QuotientGroup.mk_surjective (C.βU ⟨S.v2, S.v2_mem_UH H⟩)
  set x : Fin n → F := Multiplicative.toAdd (show Multiplicative (Fin n → F) from m.1) with hx
  have hm1 : x ≠ 0 := by
    intro h
    apply C.βU_v2_ne_one
    have : m = 1 := Subtype.ext
      (show (show Multiplicative (Fin n → F) from m.1) = 1 from toAdd_eq_zero.1 h)
    rw [← hxm, this, QuotientGroup.mk_one]
  obtain ⟨a, b, hE, ha, hb⟩ := A6L76M.exists_e9_fix hF hn x hm1
  have hfix : ∀ g : ↥(CFSG.Assembly.LowTwoRank.StatedSL n F),
      ((g : GL (Fin n) F) : Matrix (Fin n) (Fin n) F).mulVec x = x →
      (FFModel.nat (CFSG.Assembly.LowTwoRank.StatedSL n F)).act g m.1 * m.1⁻¹ ∈
        (FFModel.nat (CFSG.Assembly.LowTwoRank.StatedSL n F)).ker := by
    intro g hg
    show natAct _ g m.1 * (show Multiplicative (Fin n → F) from m.1)⁻¹ ∈
      (⊥ : Subgroup (Multiplicative (Fin n → F)))
    rw [Subgroup.mem_bot, mul_inv_eq_one]
    show Multiplicative.ofAdd (((g : GL (Fin n) F) : Matrix (Fin n) (Fin n) F).mulVec x) = m.1
    rw [hg]
    rfl
  exact C.not_e9 h13314 m.2 hxm.symm hE (hfix a ha) (hfix b hb)

end Ctx76

end Setting4

end CFSG.Quasithin.H13.A6
