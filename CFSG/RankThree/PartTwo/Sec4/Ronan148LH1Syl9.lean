module

public import CFSG.RankThree.PartTwo.Sec4.Ronan148LH1Inner
public import CFSG.RankThree.PartTwo.Sec4.Ronan148LT2Tor

public section

namespace CFSG.RankThree.PartTwo.Sec4.Ronan148L

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec4 CFSG.RankThree.PartTwo.Sec4.Ronan148S
open CFSG.HardMathSupport.Solomon.Coordinator.LieComp (NoThreeCover)
open CFSG.Open (StatedProj StatedSL StatedSp StatedScalars StatedClassicalModel)
open Matrix

section Hom33

variable {X : Type} [Group X]

@[expose] def hom33 (g h : X) (hg : g ^ 3 = 1) (hh : h ^ 3 = 1) (hgh : g * h = h * g) :
    Multiplicative (ZMod 3 × ZMod 3) →* X where
  toFun v := g ^ (Multiplicative.toAdd v).1.val * h ^ (Multiplicative.toAdd v).2.val
  map_one' := by simp
  map_mul' v w := by
    simp only [toAdd_mul, Prod.fst_add, Prod.snd_add, ZMod.val_add]
    rw [← pow_eq_pow_mod _ hg, ← pow_eq_pow_mod _ hh, pow_add, pow_add]
    have hc : h ^ (Multiplicative.toAdd v).2.val * g ^ (Multiplicative.toAdd w).1.val =
        g ^ (Multiplicative.toAdd w).1.val * h ^ (Multiplicative.toAdd v).2.val :=
      (Commute.pow_pow (show Commute g h from hgh) _ _).eq.symm
    calc g ^ (Multiplicative.toAdd v).1.val * g ^ (Multiplicative.toAdd w).1.val *
          (h ^ (Multiplicative.toAdd v).2.val * h ^ (Multiplicative.toAdd w).2.val)
        = g ^ (Multiplicative.toAdd v).1.val * (g ^ (Multiplicative.toAdd w).1.val *
          h ^ (Multiplicative.toAdd v).2.val) * h ^ (Multiplicative.toAdd w).2.val := by
          simp only [mul_assoc]
      _ = g ^ (Multiplicative.toAdd v).1.val * (h ^ (Multiplicative.toAdd v).2.val *
          g ^ (Multiplicative.toAdd w).1.val) * h ^ (Multiplicative.toAdd w).2.val := by rw [hc]
      _ = _ := by simp only [mul_assoc]

theorem hom33_ofAdd (g h : X) (hg : g ^ 3 = 1) (hh : h ^ 3 = 1) (hgh : g * h = h * g)
    (a b : ZMod 3) : hom33 g h hg hh hgh (Multiplicative.ofAdd (a, b)) = g ^ a.val * h ^ b.val :=
  rfl

theorem map_conj_range_eq {V : Type} [Group V] (ψ : V →* X) (n : X) (f : V → V)
    (hf : Function.Surjective f) (h : ∀ v, n * ψ v * n⁻¹ = ψ (f v)) :
    ψ.range.map (MulAut.conj n).toMonoidHom = ψ.range := by
  ext x
  constructor
  · rintro ⟨_, ⟨v, rfl⟩, rfl⟩
    exact ⟨f v, (h v).symm⟩
  · rintro ⟨v, rfl⟩
    obtain ⟨u, rfl⟩ := hf v
    exact ⟨ψ u, ⟨u, rfl⟩, h u⟩

theorem move33 : ∀ a b : ZMod 3, (a, b) ≠ 0 →
    ((a = 0 ∨ b = 0) → ∀ c : ZMod 3, (c * a, c * b) ≠ (b, a)) ∧
    (a ≠ 0 → b ≠ 0 → ∀ c : ZMod 3, (c * a, c * b) ≠ (2 * a, b)) := by
  decide

theorem sylNineMove_of_elements [Finite X] {g h t σ w : X}
    (hg3 : g ^ 3 = 1) (hh3 : h ^ 3 = 1) (hgh : g * h = h * g)
    (hinj : ∀ a b : ZMod 3, g ^ a.val * h ^ b.val = 1 → a = 0 ∧ b = 0)
    (htg : t * g = g * t) (hth : t * h = h * t) (ht2 : t ^ 2 = 1) (ht1 : t ≠ 1)
    (hσg : σ * g = h * σ) (hσh : σ * h = g * σ)
    (hwg : w * g = g ^ 2 * w) (hwh : w * h = h * w)
    (h27 : ¬ 27 ∣ Nat.card X) : SylNineMove X := by
  set ψ := hom33 g h hg3 hh3 hgh with hψ
  have hψa : ∀ a b : ZMod 3, ψ (Multiplicative.ofAdd (a, b)) = g ^ a.val * h ^ b.val :=
    fun _ _ => rfl
  have hsplit : ∀ v : Multiplicative (ZMod 3 × ZMod 3),
      ∃ a b : ZMod 3, v = Multiplicative.ofAdd (a, b) :=
    fun v => ⟨(Multiplicative.toAdd v).1, (Multiplicative.toAdd v).2, rfl⟩
  have hψinj : Function.Injective ψ := by
    rw [injective_iff_map_eq_one]
    intro v hv
    obtain ⟨a, b, rfl⟩ := hsplit v
    rw [hψa] at hv
    obtain ⟨rfl, rfl⟩ := hinj a b hv
    rfl
  have h3 : ∀ a b : ZMod 3, (3 • (a, b) : ZMod 3 × ZMod 3) = 0 := by decide
  have hTop : CFSG.Assembly.IsElemAbelian 3 (⊤ : Subgroup (Multiplicative (ZMod 3 × ZMod 3))) := by
    refine ⟨⟨⟨fun x y => Subtype.ext (mul_comm _ _)⟩⟩, fun x _ => ?_⟩
    obtain ⟨a, b, rfl⟩ := hsplit x
    rw [← ofAdd_nsmul, h3, ofAdd_zero]
  have hE₀ : CFSG.Assembly.IsElemAbelian 3 ψ.range := by
    rw [MonoidHom.range_eq_map]
    exact isElemAbelian_map ψ hTop
  have hE₀9 : Nat.card ψ.range = 9 := by
    rw [← Nat.card_congr (MonoidHom.ofInjective hψinj).toEquiv,
      Nat.card_congr (Multiplicative.toAdd : Multiplicative (ZMod 3 × ZMod 3) ≃ ZMod 3 × ZMod 3),
      Nat.card_prod, Nat.card_zmod]
  have hσg' : σ * g * σ⁻¹ = h := by rw [hσg, mul_inv_cancel_right]
  have hσh' : σ * h * σ⁻¹ = g := by rw [hσh, mul_inv_cancel_right]
  have hwg' : w * g * w⁻¹ = g ^ 2 := by rw [hwg, mul_inv_cancel_right]
  have hwh' : w * h * w⁻¹ = h := by rw [hwh, mul_inv_cancel_right]
  have hconj : ∀ (n x y : X) (i j : ℕ), n * (x ^ i * y ^ j) * n⁻¹ =
      (n * x * n⁻¹) ^ i * (n * y * n⁻¹) ^ j := by
    intro n x y i j
    rw [conj_pow, conj_pow]
    group
  have hσψ : ∀ v, σ * ψ v * σ⁻¹ =
      ψ (Multiplicative.ofAdd ((Multiplicative.toAdd v).2, (Multiplicative.toAdd v).1)) := by
    intro v
    obtain ⟨a, b, rfl⟩ := hsplit v
    rw [hψa, hψa, hconj, hσg', hσh']
    exact (Commute.pow_pow (show Commute g h from hgh) _ _).eq.symm
  have h2val : ∀ a : ZMod 3, g ^ (2 * a.val) = g ^ (2 * a).val := by
    intro a
    rw [ZMod.val_mul, pow_eq_pow_mod (2 * a.val) hg3]
    rfl
  have hwψ : ∀ v, w * ψ v * w⁻¹ =
      ψ (Multiplicative.ofAdd (2 * (Multiplicative.toAdd v).1, (Multiplicative.toAdd v).2)) := by
    intro v
    obtain ⟨a, b, rfl⟩ := hsplit v
    rw [hψa, hψa, hconj, hwg', hwh', ← pow_mul]
    exact congrArg (· * h ^ b.val) (h2val a)
  have hσsurj : Function.Surjective (fun v : Multiplicative (ZMod 3 × ZMod 3) =>
      Multiplicative.ofAdd ((Multiplicative.toAdd v).2, (Multiplicative.toAdd v).1)) := by
    intro v
    obtain ⟨a, b, rfl⟩ := hsplit v
    exact ⟨Multiplicative.ofAdd (b, a), rfl⟩
  have hwsurj : Function.Surjective (fun v : Multiplicative (ZMod 3 × ZMod 3) =>
      Multiplicative.ofAdd (2 * (Multiplicative.toAdd v).1, (Multiplicative.toAdd v).2)) := by
    intro v
    obtain ⟨a, b, rfl⟩ := hsplit v
    refine ⟨Multiplicative.ofAdd (2 * a, b), ?_⟩
    have h4 : (2 : ZMod 3) * (2 * a) = a := by
      rw [← mul_assoc]
      have : (2 : ZMod 3) * 2 = 1 := by decide
      rw [this, one_mul]
    simp only [toAdd_ofAdd, h4]
  have hmapσ := map_conj_range_eq ψ σ _ hσsurj hσψ
  have hmapw := map_conj_range_eq ψ w _ hwsurj hwψ
  have hzp : ∀ a b a' b' : ZMod 3, ψ (Multiplicative.ofAdd (a', b')) ∈
      Subgroup.zpowers (ψ (Multiplicative.ofAdd (a, b))) →
      ∃ c : ZMod 3, (c * a, c * b) = (a', b') := by
    intro a b a' b' hz
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hz
    rw [← map_zpow] at hk
    have hk' := congrArg Multiplicative.toAdd (hψinj hk)
    rw [toAdd_zpow, toAdd_ofAdd, toAdd_ofAdd] at hk'
    refine ⟨(k : ZMod 3), ?_⟩
    rw [← hk', Prod.smul_mk, zsmul_eq_mul, zsmul_eq_mul]
  refine ⟨ψ.range, hE₀, hE₀9, h27, ⟨t, ht1, ht2, ?_⟩, ?_⟩
  · rintro _ ⟨v, rfl⟩
    obtain ⟨a, b, rfl⟩ := hsplit v
    rw [hψa]
    exact ((Commute.pow_right (show Commute t g from htg) a.val).mul_right
      (Commute.pow_right (show Commute t h from hth) b.val)).eq
  · rintro _ ⟨v, rfl⟩ hs1
    obtain ⟨a, b, rfl⟩ := hsplit v
    have hab : (a, b) ≠ 0 := by
      intro h0
      apply hs1
      rw [h0, ofAdd_zero, map_one]
    obtain ⟨hm1, hm2⟩ := move33 a b hab
    by_cases h0 : a = 0 ∨ b = 0
    · have hs : σ * ψ (Multiplicative.ofAdd (a, b)) * σ⁻¹ ∉
          Subgroup.zpowers (ψ (Multiplicative.ofAdd (a, b))) := by
        intro hz
        rw [hσψ, toAdd_ofAdd] at hz
        obtain ⟨c, hc⟩ := hzp a b b a hz
        exact hm1 h0 c hc
      obtain ⟨h1, h2⟩ := mover_of_conj hmapσ hs
      exact ⟨σ, h1, h2⟩
    · push Not at h0
      have hs : w * ψ (Multiplicative.ofAdd (a, b)) * w⁻¹ ∉
          Subgroup.zpowers (ψ (Multiplicative.ofAdd (a, b))) := by
        intro hz
        rw [hwψ, toAdd_ofAdd] at hz
        obtain ⟨c, hc⟩ := hzp a b (2 * a) b hz
        exact hm2 h0.1 h0.2 c hc
      obtain ⟨h1, h2⟩ := mover_of_conj hmapw hs
      exact ⟨w, h1, h2⟩

end Hom33

theorem exists_diagonal_of_mk_eq_one {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
    {H : Subgroup (GL ι K)} {y : H} (hy : (QuotientGroup.mk y : StatedProj H) = 1) :
    ∃ c : K, ((y : GL ι K) : Matrix ι ι K) = Matrix.diagonal (fun _ => c) := by
  rw [QuotientGroup.eq_one_iff] at hy
  obtain ⟨c, hc⟩ := hy
  have hc' : (y : GL ι K) = Matrix.GeneralLinearGroup.scalar ι c := hc.symm
  refine ⟨(c : K), ?_⟩
  rw [hc', Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply]

section Mat

variable {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K] {H : Subgroup (GL ι K)}

theorem matVal_mul (a b : H) : (((a * b : H) : GL ι K) : Matrix ι ι K) =
    ((a : GL ι K) : Matrix ι ι K) * ((b : GL ι K) : Matrix ι ι K) := by
  rw [Subgroup.coe_mul, Units.val_mul]

theorem matVal_pow (a : H) (n : ℕ) : (((a ^ n : H) : GL ι K) : Matrix ι ι K) =
    ((a : GL ι K) : Matrix ι ι K) ^ n := by
  rw [Subgroup.coe_pow, Units.val_pow_eq_pow_val]

theorem matVal_one : (((1 : H) : GL ι K) : Matrix ι ι K) = 1 := by
  rw [Subgroup.coe_one, Units.val_one]

theorem mk_eq_of_matVal {a b : H}
    (h : ((a : GL ι K) : Matrix ι ι K) = ((b : GL ι K) : Matrix ι ι K)) :
    (QuotientGroup.mk a : StatedProj H) = QuotientGroup.mk b :=
  congrArg _ (Subtype.ext (Units.ext h))

end Mat

noncomputable def gf51Equiv : GaloisField 5 1 ≃+* ZMod 5 := by
  letI : Fintype (GaloisField 5 1) := Fintype.ofFinite _
  exact (ZMod.ringEquivOfPrime (GaloisField 5 1) (p := 5) (by norm_num)
    (by rw [Fintype.card_eq_nat_card, GaloisField.card 5 1 (by norm_num)]; norm_num)).symm

namespace L45

def mU1 : Matrix (Fin 4) (Fin 4) (ZMod 5) := !![0, 4, 0, 0; 1, 4, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1]
def mU2 : Matrix (Fin 4) (Fin 4) (ZMod 5) := !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 0, 4; 0, 0, 1, 4]
def mT : Matrix (Fin 4) (Fin 4) (ZMod 5) := !![4, 0, 0, 0; 0, 4, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1]
def mS : Matrix (Fin 4) (Fin 4) (ZMod 5) := !![0, 0, 1, 0; 0, 0, 0, 1; 1, 0, 0, 0; 0, 1, 0, 0]
def mW : Matrix (Fin 4) (Fin 4) (ZMod 5) := !![0, 2, 0, 0; 2, 0, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1]
def mWi : Matrix (Fin 4) (Fin 4) (ZMod 5) := !![0, 3, 0, 0; 3, 0, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1]

theorem rels : mU1 * mU2 = mU2 * mU1 ∧ mU1 ^ 3 = 1 ∧ mU2 ^ 3 = 1 ∧
    mT * mU1 = mU1 * mT ∧ mT * mU2 = mU2 * mT ∧ mT ^ 2 = 1 ∧
    mS * mU1 = mU2 * mS ∧ mS * mU2 = mU1 * mS ∧ mW * mU1 = mU1 ^ 2 * mW ∧
    mW * mU2 = mU2 * mW := by
  decide

theorem inj : ∀ a b : ZMod 3, ∀ c : ZMod 5,
    mU1 ^ a.val * mU2 ^ b.val = diagonal (fun _ => c) → a = 0 ∧ b = 0 := by
  decide

theorem t_ne : ∀ c : ZMod 5, mT ≠ diagonal (fun _ => c) := by
  decide

def gU1 : GL (Fin 4) (ZMod 5) := ⟨mU1, mU1 * mU1, by decide, by decide⟩
def gU2 : GL (Fin 4) (ZMod 5) := ⟨mU2, mU2 * mU2, by decide, by decide⟩
def gT : GL (Fin 4) (ZMod 5) := ⟨mT, mT, by decide, by decide⟩
def gS : GL (Fin 4) (ZMod 5) := ⟨mS, mS, by decide, by decide⟩
def gW : GL (Fin 4) (ZMod 5) := ⟨mW, mWi, by decide, by decide⟩

theorem det_U1 : mU1.det = 1 := by
  simp [mU1, Matrix.det_succ_row_zero, Fin.sum_univ_succ]
  decide

theorem det_U2 : mU2.det = 1 := by
  simp [mU2, Matrix.det_succ_row_zero, Fin.sum_univ_succ]
  decide

theorem det_T : mT.det = 1 := by
  simp [mT, Matrix.det_succ_row_zero, Fin.sum_univ_succ]
  decide

theorem det_S : mS.det = 1 := by
  simp [mS, Matrix.det_succ_row_zero, Fin.sum_univ_succ]
  decide

theorem det_W : mW.det = 1 := by
  simp [mW, Matrix.det_succ_row_zero, Fin.sum_univ_succ]
  decide

def yU1 : StatedSL 4 (ZMod 5) := ⟨gU1, CFSG.Open.StatedAPI.mem_statedSL_of_det det_U1⟩
def yU2 : StatedSL 4 (ZMod 5) := ⟨gU2, CFSG.Open.StatedAPI.mem_statedSL_of_det det_U2⟩
def yT : StatedSL 4 (ZMod 5) := ⟨gT, CFSG.Open.StatedAPI.mem_statedSL_of_det det_T⟩
def yS : StatedSL 4 (ZMod 5) := ⟨gS, CFSG.Open.StatedAPI.mem_statedSL_of_det det_S⟩
def yW : StatedSL 4 (ZMod 5) := ⟨gW, CFSG.Open.StatedAPI.mem_statedSL_of_det det_W⟩

theorem sylNineMove_stated (h27 : ¬ 27 ∣ Nat.card (StatedProj (StatedSL 4 (ZMod 5)))) :
    SylNineMove (StatedProj (StatedSL 4 (ZMod 5))) := by
  obtain ⟨r1, r2, r3, r4, r5, r6, r7, r8, r9, r10⟩ := rels
  set π : StatedSL 4 (ZMod 5) →* StatedProj (StatedSL 4 (ZMod 5)) :=
    QuotientGroup.mk' ((StatedScalars (Fin 4) (ZMod 5)).subgroupOf (StatedSL 4 (ZMod 5)))
    with hπ
  have hU1 : ((yU1 : GL (Fin 4) (ZMod 5)) : Matrix (Fin 4) (Fin 4) (ZMod 5)) = mU1 := rfl
  have hU2 : ((yU2 : GL (Fin 4) (ZMod 5)) : Matrix (Fin 4) (Fin 4) (ZMod 5)) = mU2 := rfl
  have hT : ((yT : GL (Fin 4) (ZMod 5)) : Matrix (Fin 4) (Fin 4) (ZMod 5)) = mT := rfl
  have hS : ((yS : GL (Fin 4) (ZMod 5)) : Matrix (Fin 4) (Fin 4) (ZMod 5)) = mS := rfl
  have hW : ((yW : GL (Fin 4) (ZMod 5)) : Matrix (Fin 4) (Fin 4) (ZMod 5)) = mW := rfl
  refine sylNineMove_of_elements (g := π yU1) (h := π yU2) (t := π yT) (σ := π yS)
    (w := π yW) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ h27
  · rw [← map_pow, ← map_one π]
    exact mk_eq_of_matVal (by rw [matVal_pow, matVal_one, hU1]; exact r2)
  · rw [← map_pow, ← map_one π]
    exact mk_eq_of_matVal (by rw [matVal_pow, matVal_one, hU2]; exact r3)
  · rw [← map_mul, ← map_mul]
    exact mk_eq_of_matVal (by rw [matVal_mul, matVal_mul, hU1, hU2]; exact r1)
  · intro a b hab
    rw [← map_pow, ← map_pow, ← map_mul] at hab
    obtain ⟨c, hc⟩ := exists_diagonal_of_mk_eq_one hab
    rw [matVal_mul, matVal_pow, matVal_pow, hU1, hU2] at hc
    exact inj a b c hc
  · rw [← map_mul, ← map_mul]
    exact mk_eq_of_matVal (by rw [matVal_mul, matVal_mul, hT, hU1]; exact r4)
  · rw [← map_mul, ← map_mul]
    exact mk_eq_of_matVal (by rw [matVal_mul, matVal_mul, hT, hU2]; exact r5)
  · rw [← map_pow, ← map_one π]
    exact mk_eq_of_matVal (by rw [matVal_pow, matVal_one, hT]; exact r6)
  · intro h1
    obtain ⟨c, hc⟩ := exists_diagonal_of_mk_eq_one h1
    exact t_ne c (by rw [← hT]; exact hc)
  · rw [← map_mul, ← map_mul]
    exact mk_eq_of_matVal (by rw [matVal_mul, matVal_mul, hS, hU1, hU2]; exact r7)
  · rw [← map_mul, ← map_mul]
    exact mk_eq_of_matVal (by rw [matVal_mul, matVal_mul, hS, hU1, hU2]; exact r8)
  · rw [← map_pow, ← map_mul, ← map_mul]
    exact mk_eq_of_matVal (by rw [matVal_mul, matVal_mul, matVal_pow, hW, hU1]; exact r9)
  · rw [← map_mul, ← map_mul]
    exact mk_eq_of_matVal (by rw [matVal_mul, matVal_mul, hW, hU2]; exact r10)

end L45

namespace Sp45

def mU1 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) (ZMod 5) :=
  fromBlocks !![0, 0; 0, 1] !![4, 0; 0, 0] !![1, 0; 0, 0] !![4, 0; 0, 1]
def mU2 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) (ZMod 5) :=
  fromBlocks !![1, 0; 0, 0] !![0, 0; 0, 4] !![0, 0; 0, 1] !![1, 0; 0, 4]
def mT : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) (ZMod 5) :=
  fromBlocks !![4, 0; 0, 1] 0 0 !![4, 0; 0, 1]
def mS : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) (ZMod 5) :=
  fromBlocks !![0, 1; 1, 0] 0 0 !![0, 1; 1, 0]
def mW : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) (ZMod 5) :=
  fromBlocks !![0, 0; 0, 1] !![2, 0; 0, 0] !![2, 0; 0, 0] !![0, 0; 0, 1]
def mWi : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) (ZMod 5) :=
  fromBlocks !![0, 0; 0, 1] !![3, 0; 0, 0] !![3, 0; 0, 0] !![0, 0; 0, 1]

theorem rels : mU1 * mU2 = mU2 * mU1 ∧ mU1 ^ 3 = 1 ∧ mU2 ^ 3 = 1 ∧
    mT * mU1 = mU1 * mT ∧ mT * mU2 = mU2 * mT ∧ mT ^ 2 = 1 ∧
    mS * mU1 = mU2 * mS ∧ mS * mU2 = mU1 * mS ∧ mW * mU1 = mU1 ^ 2 * mW ∧
    mW * mU2 = mU2 * mW := by
  decide

theorem inj : ∀ a b : ZMod 3, ∀ c : ZMod 5,
    mU1 ^ a.val * mU2 ^ b.val = diagonal (fun _ => c) → a = 0 ∧ b = 0 := by
  decide

theorem t_ne : ∀ c : ZMod 5, mT ≠ diagonal (fun _ => c) := by
  decide

theorem symp : mU1ᵀ * fromBlocks 0 1 (-1) 0 * mU1 = fromBlocks 0 1 (-1) 0 ∧
    mU2ᵀ * fromBlocks 0 1 (-1) 0 * mU2 = fromBlocks 0 1 (-1) 0 ∧
    mTᵀ * fromBlocks 0 1 (-1) 0 * mT = fromBlocks 0 1 (-1) 0 ∧
    mSᵀ * fromBlocks 0 1 (-1) 0 * mS = fromBlocks 0 1 (-1) 0 ∧
    mWᵀ * fromBlocks 0 1 (-1) 0 * mW = fromBlocks 0 1 (-1) 0 := by
  decide

def gU1 : GL (Fin 2 ⊕ Fin 2) (ZMod 5) := ⟨mU1, mU1 * mU1, by decide, by decide⟩
def gU2 : GL (Fin 2 ⊕ Fin 2) (ZMod 5) := ⟨mU2, mU2 * mU2, by decide, by decide⟩
def gT : GL (Fin 2 ⊕ Fin 2) (ZMod 5) := ⟨mT, mT, by decide, by decide⟩
def gS : GL (Fin 2 ⊕ Fin 2) (ZMod 5) := ⟨mS, mS, by decide, by decide⟩
def gW : GL (Fin 2 ⊕ Fin 2) (ZMod 5) := ⟨mW, mWi, by decide, by decide⟩

def yU1 : StatedSp 2 (ZMod 5) := ⟨gU1, CFSG.Open.StatedAPI.mem_statedSp_iff.mpr symp.1⟩
def yU2 : StatedSp 2 (ZMod 5) := ⟨gU2, CFSG.Open.StatedAPI.mem_statedSp_iff.mpr symp.2.1⟩
def yT : StatedSp 2 (ZMod 5) := ⟨gT, CFSG.Open.StatedAPI.mem_statedSp_iff.mpr symp.2.2.1⟩
def yS : StatedSp 2 (ZMod 5) := ⟨gS, CFSG.Open.StatedAPI.mem_statedSp_iff.mpr symp.2.2.2.1⟩
def yW : StatedSp 2 (ZMod 5) := ⟨gW, CFSG.Open.StatedAPI.mem_statedSp_iff.mpr symp.2.2.2.2⟩

theorem sylNineMove_stated (h27 : ¬ 27 ∣ Nat.card (StatedProj (StatedSp 2 (ZMod 5)))) :
    SylNineMove (StatedProj (StatedSp 2 (ZMod 5))) := by
  obtain ⟨r1, r2, r3, r4, r5, r6, r7, r8, r9, r10⟩ := rels
  set π : StatedSp 2 (ZMod 5) →* StatedProj (StatedSp 2 (ZMod 5)) :=
    QuotientGroup.mk' ((StatedScalars (Fin 2 ⊕ Fin 2) (ZMod 5)).subgroupOf (StatedSp 2 (ZMod 5)))
    with hπ
  have hU1 : ((yU1 : GL (Fin 2 ⊕ Fin 2) (ZMod 5)) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2)
    (ZMod 5)) = mU1 := rfl
  have hU2 : ((yU2 : GL (Fin 2 ⊕ Fin 2) (ZMod 5)) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2)
    (ZMod 5)) = mU2 := rfl
  have hT : ((yT : GL (Fin 2 ⊕ Fin 2) (ZMod 5)) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2)
    (ZMod 5)) = mT := rfl
  have hS : ((yS : GL (Fin 2 ⊕ Fin 2) (ZMod 5)) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2)
    (ZMod 5)) = mS := rfl
  have hW : ((yW : GL (Fin 2 ⊕ Fin 2) (ZMod 5)) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2)
    (ZMod 5)) = mW := rfl
  refine sylNineMove_of_elements (g := π yU1) (h := π yU2) (t := π yT) (σ := π yS)
    (w := π yW) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ h27
  · rw [← map_pow, ← map_one π]
    exact mk_eq_of_matVal (by rw [matVal_pow, matVal_one, hU1]; exact r2)
  · rw [← map_pow, ← map_one π]
    exact mk_eq_of_matVal (by rw [matVal_pow, matVal_one, hU2]; exact r3)
  · rw [← map_mul, ← map_mul]
    exact mk_eq_of_matVal (by rw [matVal_mul, matVal_mul, hU1, hU2]; exact r1)
  · intro a b hab
    rw [← map_pow, ← map_pow, ← map_mul] at hab
    obtain ⟨c, hc⟩ := exists_diagonal_of_mk_eq_one hab
    rw [matVal_mul, matVal_pow, matVal_pow, hU1, hU2] at hc
    exact inj a b c hc
  · rw [← map_mul, ← map_mul]
    exact mk_eq_of_matVal (by rw [matVal_mul, matVal_mul, hT, hU1]; exact r4)
  · rw [← map_mul, ← map_mul]
    exact mk_eq_of_matVal (by rw [matVal_mul, matVal_mul, hT, hU2]; exact r5)
  · rw [← map_pow, ← map_one π]
    exact mk_eq_of_matVal (by rw [matVal_pow, matVal_one, hT]; exact r6)
  · intro h1
    obtain ⟨c, hc⟩ := exists_diagonal_of_mk_eq_one h1
    exact t_ne c (by rw [← hT]; exact hc)
  · rw [← map_mul, ← map_mul]
    exact mk_eq_of_matVal (by rw [matVal_mul, matVal_mul, hS, hU1, hU2]; exact r7)
  · rw [← map_mul, ← map_mul]
    exact mk_eq_of_matVal (by rw [matVal_mul, matVal_mul, hS, hU1, hU2]; exact r8)
  · rw [← map_pow, ← map_mul, ← map_mul]
    exact mk_eq_of_matVal (by rw [matVal_mul, matVal_mul, matVal_pow, hW, hU1]; exact r9)
  · rw [← map_mul, ← map_mul]
    exact mk_eq_of_matVal (by rw [matVal_mul, matVal_mul, hW, hU2]; exact r10)

end Sp45

noncomputable def equivL45 : CFSG.Assembly.RankThreeEven.projSL 4 (GaloisField 5 1) ≃*
    StatedProj (StatedSL 4 (ZMod 5)) :=
  ((Adapters.RankTwoModelTransports.statedProjEquivMapMk _).trans
      (MulEquiv.subgroupCongr
        (CFSG.RankThree.PartOne.projImage_statedSL_eq_projSL 4 (GaloisField 5 1)))).symm.trans
    (Adapters.RankTwoModelTransports.statedProjCongr
      (Adapters.RankTwoModelTransports.glCongr gf51Equiv)
      (Adapters.RankTwoModelTransports.glCongr_statedSL gf51Equiv 4)
      (Adapters.RankTwoModelTransports.glCongr_statedScalars gf51Equiv))

noncomputable def equivSp45 : CFSG.Assembly.RankThreeEven.projSp 2 (GaloisField 5 1) ≃*
    StatedProj (StatedSp 2 (ZMod 5)) :=
  ((Adapters.RankTwoModelTransports.statedProjEquivMapMk _).trans
      (MulEquiv.subgroupCongr
        (CFSG.RankThree.PartOne.projImage_statedSp_eq_projSp 2 (GaloisField 5 1)))).symm.trans
    (Adapters.RankTwoModelTransports.statedProjCongr
      (Adapters.RankTwoModelTransports.glCongr gf51Equiv)
      (Adapters.RankTwoModelTransports.glCongr_statedSp gf51Equiv 2)
      (Adapters.RankTwoModelTransports.glCongr_statedScalars gf51Equiv))

theorem card_projSL45 :
    Nat.card (CFSG.Assembly.RankThreeEven.projSL 4 (GaloisField 5 1)) = 7254000000 := by
  have hc := CFSG.RankThree.PartTwo.Sec11.KSListsProof.card_projSL_four_mul (GaloisField 5 1)
  rw [GaloisField.card 5 1 (by norm_num)] at hc
  norm_num at hc
  omega

theorem card_projSp45 :
    Nat.card (CFSG.Assembly.RankThreeEven.projSp 2 (GaloisField 5 1)) = 4680000 := by
  have h2 : (2 : GaloisField 5 1) ≠ 0 := by
    intro h
    have h5 : (5 : GaloisField 5 1) = 0 := by
      exact_mod_cast CharP.cast_eq_zero (GaloisField 5 1) 5
    have : (1 : GaloisField 5 1) = 0 := by linear_combination h5 - 2 * h
    exact one_ne_zero this
  have hc := CFSG.RankThree.PartTwo.Sec11.KSListsProof.card_projSp_two_mul (GaloisField 5 1) h2
  rw [GaloisField.card 5 1 (by norm_num)] at hc
  norm_num at hc
  omega

theorem sylNineMove_projSL45 :
    SylNineMove (CFSG.Assembly.RankThreeEven.projSL 4 (GaloisField 5 1)) :=
  SylNineMove.of_mulEquiv equivL45 (L45.sylNineMove_stated (by
    rw [← Nat.card_congr equivL45.toEquiv, card_projSL45]
    norm_num))

theorem sylNineMove_projSp45 :
    SylNineMove (CFSG.Assembly.RankThreeEven.projSp 2 (GaloisField 5 1)) :=
  SylNineMove.of_mulEquiv equivSp45 (Sp45.sylNineMove_stated (by
    rw [← Nat.card_congr equivSp45.toEquiv, card_projSp45]
    norm_num))

section Cover

open CFSG.Blueprint.Multiplier (generic exceptional genericOrders exceptionalOrders)


theorem noThreeCover_projSp45 :
    NoThreeCover (CFSG.Assembly.RankThreeEven.projSp 2 (GaloisField 5 1)) := by
  have e₀ : CFSG.Assembly.RankThreeEven.projSp 2 (GaloisField 5 1) ≃*
      StatedProj (StatedSp 2 (GaloisField 5 1)) :=
    ((Adapters.RankTwoModelTransports.statedProjEquivMapMk _).trans
      (MulEquiv.subgroupCongr
        (CFSG.RankThree.PartOne.projImage_statedSp_eq_projSp 2 (GaloisField 5 1)))).symm
  have hSp : StatedClassicalModel (CFSG.Assembly.RankThreeEven.projSp 2 (GaloisField 5 1))
      .PSp 2 5 1 :=
    ⟨⟨by norm_num, by norm_num, by norm_num, by decide⟩, GaloisField 5 1, inferInstance,
      inferInstance, GaloisField.card 5 1 (by norm_num), ⟨e₀⟩⟩
  obtain ⟨e⟩ := (CFSG.LieType.Steinberg.CentralExt.GriessClassical.psp_row hSp
    (Or.inl (by norm_num))).2
  have hcard : Nat.card (generic .PSp 2 5 1 × exceptional .PSp 2 5 1) = 2 := by
    simp only [generic, exceptional, Nat.card_prod, card_multiplicative_zmod]
    simp [genericOrders, exceptionalOrders]
  haveI : Finite (generic .PSp 2 5 1 × exceptional .PSp 2 5 1) :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  exact noThreeCover_of_hopf e (by rw [hcard]; norm_num)


theorem noThreeCover_projSL45 :
    NoThreeCover (CFSG.Assembly.RankThreeEven.projSL 4 (GaloisField 5 1)) := by
  have e₀ : CFSG.Assembly.RankThreeEven.projSL 4 (GaloisField 5 1) ≃*
      StatedProj (StatedSL 4 (GaloisField 5 1)) :=
    ((Adapters.RankTwoModelTransports.statedProjEquivMapMk _).trans
      (MulEquiv.subgroupCongr
        (CFSG.RankThree.PartOne.projImage_statedSL_eq_projSL 4 (GaloisField 5 1)))).symm
  have hSL : StatedClassicalModel (CFSG.Assembly.RankThreeEven.projSL 4 (GaloisField 5 1))
      .PSL 4 5 1 :=
    ⟨⟨by norm_num, by norm_num, by norm_num, by decide, by decide⟩, GaloisField 5 1,
      inferInstance, inferInstance, GaloisField.card 5 1 (by norm_num), ⟨e₀⟩⟩
  obtain ⟨e⟩ := (CFSG.LieType.Steinberg.CentralExt.GriessClassical.psl_row hSL).2
  have hcard : Nat.card (generic .PSL 4 5 1 × exceptional .PSL 4 5 1) = 4 := by
    simp only [generic, exceptional, Nat.card_prod, card_multiplicative_zmod]
    simp [genericOrders, exceptionalOrders]
  haveI : Finite (generic .PSL 4 5 1 × exceptional .PSL 4 5 1) :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  exact noThreeCover_of_hopf e (by rw [hcard]; norm_num)

end Cover

theorem not_three_dvd_card_outer_projSL45 :
    ¬ 3 ∣ Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer
      (CFSG.Assembly.RankThreeEven.projSL 4 (GaloisField 5 1))) := by
  have hd := CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.higher_linear_outer_order_divides_field_gcd_bound
    (k := GaloisField 5 1) (p := 5) (f := 1) (n := 4) (by norm_num) le_rfl (by norm_num)
    (GaloisField.card 5 1 (by norm_num))
  rw [← Nat.card_congr (CFSG.ComponentClassification.OuterAutomorphisms.equivalence
    (projSLEquivProjectiveSL 4 (GaloisField 5 1))).toEquiv] at hd
  intro h3
  have h3' := h3.trans hd
  norm_num at h3'

theorem not_three_dvd_card_outer_projSp45 :
    ¬ 3 ∣ Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer
      (CFSG.Assembly.RankThreeEven.projSp 2 (GaloisField 5 1))) := by
  have hK : Nat.card (GaloisField 5 1) = 5 := by
    rw [GaloisField.card 5 1 (by norm_num)]; norm_num
  have e₀ : CFSG.Assembly.RankThreeEven.projSp 2 (GaloisField 5 1) ≃*
      CFSG.Open.StatedProj (CFSG.Open.StatedSp 2 (GaloisField 5 1)) :=
    ((CFSG.RankThree.PartTwo.Census.statedProjEquivProjImage _).trans
      (MulEquiv.subgroupCongr
        (CFSG.RankThree.PartOne.projImage_statedSp_eq_projSp 2 (GaloisField 5 1)))).symm
  have hodd : ringChar (GaloisField 5 1) ≠ 2 := by
    rw [ringChar.eq (GaloisField 5 1) 5]
    norm_num
  have h := Item49OddChar.not_three_dvd_card_outer_psp4 hodd
    (Item49OddChar.subsingleton_ringAut_of_card_prime (by norm_num) hK)
  rwa [← Nat.card_congr (CFSG.ComponentClassification.OuterAutomorphisms.equivalence
    e₀).toEquiv] at h

section Rows

theorem kH1_four_Sp_five
    :
    RowOf427 (CFSG.Assembly.RankThreeEven.projSp 2 (GaloisField 5 1)) :=
  kH1_four_Sp_five_of_cent (rowOf427Cent_of_sylNineMove noThreeCover_projSp45
    (cubeInner_of_not_three_dvd_card_outer not_three_dvd_card_outer_projSp45)
    sylNineMove_projSp45)


theorem kH1_four_SL_five
    :
    RowOf427 (CFSG.Assembly.RankThreeEven.projSL 4 (GaloisField 5 1)) :=
  kH1_four_SL_five_of_cent (rowOf427Cent_of_sylNineMove noThreeCover_projSL45
    (cubeInner_of_not_three_dvd_card_outer not_three_dvd_card_outer_projSL45)
    sylNineMove_projSL45)

end Rows

end CFSG.RankThree.PartTwo.Sec4.Ronan148L
