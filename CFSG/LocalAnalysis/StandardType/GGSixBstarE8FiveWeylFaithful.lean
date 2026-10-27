module

public import CFSG.LocalAnalysis.StandardType.GGSixBstarE8FiveIsotropic

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
open Module

namespace NoOffE8Five

local instance noOffE8FiveFactFiveW : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩

local instance noOffE8FiveNeZeroRankW : NeZero Tag.E8.rank := ⟨by decide⟩

section TorusActLinear

variable {τ : Tag} {p : ℕ}

theorem torusAct_add [NeZero p] (u : WeylGroup τ) (x y : Fin τ.rank → ZMod p) :
    TableBExc.torusAct τ p u (x + y) =
      TableBExc.torusAct τ p u x + TableBExc.torusAct τ p u y := by
  rw [← NoOffRest.torusLin_apply, ← NoOffRest.torusLin_apply, ← NoOffRest.torusLin_apply,
    map_add]

theorem torusAct_sub [NeZero p] (u : WeylGroup τ) (x y : Fin τ.rank → ZMod p) :
    TableBExc.torusAct τ p u (x - y) =
      TableBExc.torusAct τ p u x - TableBExc.torusAct τ p u y := by
  rw [← NoOffRest.torusLin_apply, ← NoOffRest.torusLin_apply, ← NoOffRest.torusLin_apply,
    map_sub]

theorem torusAct_smul [NeZero p] (u : WeylGroup τ) (c : ZMod p)
    (x : Fin τ.rank → ZMod p) :
    TableBExc.torusAct τ p u (c • x) = c • TableBExc.torusAct τ p u x := by
  rw [← NoOffRest.torusLin_apply, ← NoOffRest.torusLin_apply]
  exact map_smul _ _ _

theorem torusAct_nsmul [NeZero p] (u : WeylGroup τ) (n : ℕ) (x : Fin τ.rank → ZMod p) :
    TableBExc.torusAct τ p u (n • x) = n • TableBExc.torusAct τ p u x := by
  rw [← NoOffRest.torusLin_apply, ← NoOffRest.torusLin_apply]
  exact map_nsmul _ _ _

theorem torusAct_conj [NeZero p] (g u : WeylGroup τ) (z : Fin τ.rank → ZMod p) :
    TableBExc.torusAct τ p (g * u * g⁻¹) z =
      TableBExc.torusAct τ p g (TableBExc.torusAct τ p u (TableBExc.torusAct τ p g⁻¹ z)) := by
  rw [TableBExc.torusAct_mul, TableBExc.torusAct_mul]

theorem torusAct_inv_apply [NeZero p] (g : WeylGroup τ) (z : Fin τ.rank → ZMod p) :
    TableBExc.torusAct τ p g⁻¹ (TableBExc.torusAct τ p g z) = z := by
  rw [← TableBExc.torusAct_mul, inv_mul_cancel, TableBExc.torusAct_one]

theorem torusAct_mul_inv_apply [NeZero p] (g : WeylGroup τ) (z : Fin τ.rank → ZMod p) :
    TableBExc.torusAct τ p g (TableBExc.torusAct τ p g⁻¹ z) = z := by
  rw [← TableBExc.torusAct_mul, mul_inv_cancel, TableBExc.torusAct_one]

end TorusActLinear

abbrev SqZero (u : WeylGroup .E8) : Prop :=
  ∀ x : Fin Tag.E8.rank → ZMod 5,
    TableBExc.torusAct .E8 5 u (TableBExc.torusAct .E8 5 u x - x) =
      TableBExc.torusAct .E8 5 u x - x

theorem sqZero_pow_act {u : WeylGroup .E8} (hu : SqZero u) (k : ℕ)
    (x : Fin Tag.E8.rank → ZMod 5) :
    TableBExc.torusAct .E8 5 (u ^ k) x =
      x + k • (TableBExc.torusAct .E8 5 u x - x) := by
  induction k with
  | zero => simp [TableBExc.torusAct_one]
  | succ k ih =>
    rw [pow_succ', TableBExc.torusAct_mul, ih]
    have hlin : TableBExc.torusAct .E8 5 u
          (x + k • (TableBExc.torusAct .E8 5 u x - x)) =
        TableBExc.torusAct .E8 5 u x + k • (TableBExc.torusAct .E8 5 u x - x) := by
      rw [torusAct_add, torusAct_nsmul, hu x]
    rw [hlin, succ_nsmul]
    abel

theorem sqZero_fix_nsmul {u : WeylGroup .E8} (hu : SqZero u) (k : ℕ)
    (x : Fin Tag.E8.rank → ZMod 5) :
    TableBExc.torusAct .E8 5 (u ^ k) (TableBExc.torusAct .E8 5 u x - x) =
      TableBExc.torusAct .E8 5 u x - x := by
  have h1 := sqZero_pow_act hu k (TableBExc.torusAct .E8 5 u x - x)
  have h2 : TableBExc.torusAct .E8 5 u (TableBExc.torusAct .E8 5 u x - x) -
      (TableBExc.torusAct .E8 5 u x - x) = 0 := by
    rw [hu x, sub_self]
  rw [h2, nsmul_zero, add_zero] at h1
  exact h1

theorem sqZero_pow {u : WeylGroup .E8} (hu : SqZero u) (k : ℕ) : SqZero (u ^ k) := by
  intro x
  have hx := sqZero_pow_act hu k x
  have hfix := sqZero_fix_nsmul hu k x
  rw [hx]
  have hsub : x + k • (TableBExc.torusAct .E8 5 u x - x) - x =
      k • (TableBExc.torusAct .E8 5 u x - x) := by abel
  rw [hsub, torusAct_nsmul, hfix]

theorem sqZero_conj {u : WeylGroup .E8} (hu : SqZero u) (g : WeylGroup .E8) :
    SqZero (g * u * g⁻¹) := by
  intro x
  set y := TableBExc.torusAct .E8 5 g⁻¹ x with hy
  have hx : x = TableBExc.torusAct .E8 5 g y := by
    rw [hy, torusAct_mul_inv_apply]
  have hconjx : TableBExc.torusAct .E8 5 (g * u * g⁻¹) x =
      TableBExc.torusAct .E8 5 g (TableBExc.torusAct .E8 5 u y) := by
    rw [torusAct_conj, ← hy]
  have hconjN : TableBExc.torusAct .E8 5 (g * u * g⁻¹)
        (TableBExc.torusAct .E8 5 g (TableBExc.torusAct .E8 5 u y - y)) =
      TableBExc.torusAct .E8 5 g
        (TableBExc.torusAct .E8 5 u (TableBExc.torusAct .E8 5 u y - y)) := by
    rw [torusAct_conj, torusAct_inv_apply]
  have hN : TableBExc.torusAct .E8 5 (g * u * g⁻¹) x - x =
      TableBExc.torusAct .E8 5 g (TableBExc.torusAct .E8 5 u y - y) := by
    rw [hconjx, hx, ← torusAct_sub]
  rw [hN, hconjN, hu y]

theorem torusAct_wordE8B (x : Fin Tag.E8.rank → ZMod 5) :
    TableBExc.torusAct .E8 5 TableBExc.weylE8B x =
      TableBExc.torusWord .E8 5 TableBExc.wordE8B x := by
  change TableBExc.torusAct .E8 5 ((coxeterSystem .E8).wordProd TableBExc.wordE8B) x =
    TableBExc.torusWord .E8 5 TableBExc.wordE8B x
  rw [← TableBExc.torusWord_eq_torusAct TableBExc.Three.cartan_symm_E8]

theorem torusAct_wordE8AB (c : ℕ) (x : Fin Tag.E8.rank → ZMod 5) :
    TableBExc.torusAct .E8 5 (TableBExc.weylE8A * TableBExc.weylE8B ^ c) x =
      TableBExc.torusWord .E8 5 (TableBExc.wordE8AB c) x := by
  rw [← TableBExc.wordProd_wordE8AB c]
  change TableBExc.torusAct .E8 5
      ((coxeterSystem .E8).wordProd (TableBExc.wordE8AB c)) x =
    TableBExc.torusWord .E8 5 (TableBExc.wordE8AB c) x
  rw [← TableBExc.torusWord_eq_torusAct TableBExc.Three.cartan_symm_E8]

theorem exists_not_fix_sq_wordE8B :
    ∃ j : Fin Tag.E8.rank,
      TableBExc.torusWord .E8 5 TableBExc.wordE8B
          (TableBExc.torusWord .E8 5 TableBExc.wordE8B (Pi.single j 1) - Pi.single j 1) ≠
        TableBExc.torusWord .E8 5 TableBExc.wordE8B (Pi.single j 1) - Pi.single j 1 := by
  decide +kernel

theorem exists_not_fix_sq_wordE8AB :
    ∀ c : Fin 5, ∃ j : Fin Tag.E8.rank,
      TableBExc.torusWord .E8 5 (TableBExc.wordE8AB (c : ℕ))
          (TableBExc.torusWord .E8 5 (TableBExc.wordE8AB (c : ℕ)) (Pi.single j 1) -
            Pi.single j 1) ≠
        TableBExc.torusWord .E8 5 (TableBExc.wordE8AB (c : ℕ)) (Pi.single j 1) -
          Pi.single j 1 := by
  decide +kernel

theorem not_sqZero_weylE8B : ¬ SqZero TableBExc.weylE8B := by
  intro h
  obtain ⟨j, hj⟩ := exists_not_fix_sq_wordE8B
  apply hj
  have h' := h (Pi.single j 1)
  simpa only [torusAct_wordE8B] using h'

theorem not_sqZero_weylE8AB {c : ℕ} (hc : c < 5) :
    ¬ SqZero (TableBExc.weylE8A * TableBExc.weylE8B ^ c) := by
  intro h
  obtain ⟨j, hj⟩ := exists_not_fix_sq_wordE8AB ⟨c, hc⟩
  simp only [Fin.val_mk] at hj
  apply hj
  have h' := h (Pi.single j 1)
  simpa only [torusAct_wordE8AB] using h'

section WeylFaithful


theorem weylE8_eq_one_of_sq_zero {u : WeylGroup .E8}
    (hu : ∀ x : Fin Tag.E8.rank → ZMod 5,
      TableBExc.torusAct .E8 5 u (TableBExc.torusAct .E8 5 u x - x) =
        TableBExc.torusAct .E8 5 u x - x) : u = 1 := by
  have hu' : SqZero u := hu
  by_contra hu1
  have hpow5 : u ^ 5 = 1 := by
    apply NoOffExc.eq_one_of_torusAct (p := 5) (by norm_num)
    intro x
    rw [sqZero_pow_act hu' 5 x,
      show (5 : ℕ) • (TableBExc.torusAct .E8 5 u x - x) = 0 by
        rw [← Nat.cast_smul_eq_nsmul (R := ZMod 5) 5,
          show ((5 : ℕ) : ZMod 5) = 0 by decide, zero_smul]]
    exact add_zero x
  have hord : orderOf u = 5 := orderOf_eq_prime hpow5 hu1
  have hidx : ¬ 5 ∣ TableBExc.weylE8S.index := by
    rw [NoOffExc.index_eq_of_card TableBExc.card_weylE8S NoOffExc.card_weyl_E8
      (show 25 * 27869184 = 696729600 by norm_num) (by norm_num)]
    norm_num
  have hP : IsPGroup 5 (Subgroup.zpowers u) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hord]; norm_num)
  obtain ⟨g, hg⟩ := TableBF4.exists_conj_le_of_not_dvd_index Nat.prime_five hidx hP
  have hs_mem : g * u * g⁻¹ ∈ TableBExc.weylE8S := by
    have hmem : (MulAut.conj g).toMonoidHom u ∈
        (Subgroup.zpowers u).map (MulAut.conj g).toMonoidHom :=
      Subgroup.mem_map_of_mem (MulAut.conj g).toMonoidHom (Subgroup.mem_zpowers u)
    have := hg hmem
    rwa [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at this
  have hs1 : g * u * g⁻¹ ≠ 1 := by
    intro h
    apply hu1
    have h2 : g⁻¹ * (g * u * g⁻¹) * g = 1 := by rw [h]; group
    rwa [show g⁻¹ * (g * u * g⁻¹) * g = u by group] at h2
  have hsP : SqZero (g * u * g⁻¹) := sqZero_conj hu' g
  obtain ⟨k, hk | ⟨c, hc, hk⟩⟩ := TableBExc.exists_pow_eq_rep hs_mem hs1
  · exact not_sqZero_weylE8B (hk ▸ sqZero_pow hsP k)
  · exact not_sqZero_weylE8AB hc (hk ▸ sqZero_pow hsP k)

theorem weylE8_eq_one_of_forall_fix_eigE8 {lam : ZMod 5} (hlam : lam * lam = -1)
    {u : WeylGroup .E8}
    (hu : ∀ x ∈ NoOffRest.eigE8 5 lam, TableBExc.torusAct .E8 5 u x = x) : u = 1 := by
  apply weylE8_eq_one_of_sq_zero
  intro x
  have hx : TableBExc.torusAct .E8 5 u x - x ∈ NoOffRest.eigE8 5 lam := by
    apply mem_eigE8_of_forall_bform_eq_zero hlam
    intro y hy
    rw [map_sub]
    have h1 : NoOffRest.bform .E8 5 y (TableBExc.torusAct .E8 5 u x) =
        NoOffRest.bform .E8 5 y x :=
      calc NoOffRest.bform .E8 5 y (TableBExc.torusAct .E8 5 u x)
          = NoOffRest.bform .E8 5 (TableBExc.torusAct .E8 5 u x) y :=
            NoOffRest.bform_comm y (TableBExc.torusAct .E8 5 u x)
        _ = NoOffRest.bform .E8 5 (TableBExc.torusAct .E8 5 u x)
              (TableBExc.torusAct .E8 5 u y) := by rw [hu y hy]
        _ = NoOffRest.bform .E8 5 x y := NoOffRest.bform_torusAct u x y
        _ = NoOffRest.bform .E8 5 y x := NoOffRest.bform_comm x y
    rw [h1]
    abel
  exact hu (TableBExc.torusAct .E8 5 u x - x) hx

theorem mem_centE8W_of_torusAct_mem_eigE8 {lam : ZMod 5} (hlam : lam * lam = -1)
    {u : WeylGroup .E8}
    (hu : ∀ x ∈ NoOffRest.eigE8 5 lam, TableBExc.torusAct .E8 5 u x ∈ NoOffRest.eigE8 5 lam) :
    u ∈ NoOffRest.centE8W := by
  change u ∈ Subgroup.centralizer {NoOffRest.weylE8W}
  rw [Subgroup.mem_centralizer_singleton_iff]
  set w := NoOffRest.weylE8W with hw
  have hlam0 : lam ≠ 0 := by
    rintro rfl
    have : (0 : ZMod 5) ≠ -1 := by decide
    exact this hlam
  have huinv_mem : ∀ x ∈ NoOffRest.eigE8 5 lam,
      TableBExc.torusAct .E8 5 u⁻¹ x ∈ NoOffRest.eigE8 5 lam := by
    intro x hx
    let φ : NoOffRest.eigE8 5 lam →ₗ[ZMod 5] NoOffRest.eigE8 5 lam :=
      (NoOffRest.torusLin .E8 5 u).restrict (fun y hy => hu y hy)
    have hlinj : Function.Injective (NoOffRest.torusLin .E8 5 u) := by
      intro a b hab
      exact (TableBExc.torusPerm .E8 5 u).injective (by
        simpa only [TableBExc.torusPerm_apply, NoOffRest.torusLin_apply] using hab)
    have hinj : Function.Injective φ := by
      intro a b hab
      exact Subtype.ext (hlinj (congrArg Subtype.val hab))
    have hsurj : Function.Surjective φ := Finite.injective_iff_surjective.mp hinj
    obtain ⟨y, hy⟩ := hsurj ⟨x, hx⟩
    have hy' : TableBExc.torusAct .E8 5 u y = x := congrArg Subtype.val hy
    rw [← hy', ← TableBExc.torusAct_mul, inv_mul_cancel, TableBExc.torusAct_one]
    exact y.2
  have hwmem : ∀ y ∈ NoOffRest.eigE8 5 lam, TableBExc.torusAct .E8 5 w y = lam • y := by
    intro y hy
    rw [NoOffRest.eigE8, NoOffRest.mem_eigSp] at hy
    rw [← NoOffRest.torusLin_apply, hw]
    exact hy
  have hwEinv : ∀ x ∈ NoOffRest.eigE8 5 lam, TableBExc.torusAct .E8 5 w⁻¹ x = lam⁻¹ • x := by
    intro x hx
    have h1 : TableBExc.torusAct .E8 5 w (lam⁻¹ • x) = x := by
      rw [hwmem (lam⁻¹ • x) (Submodule.smul_mem _ _ hx), smul_smul, mul_inv_cancel₀ hlam0,
        one_smul]
    calc TableBExc.torusAct .E8 5 w⁻¹ x
        = TableBExc.torusAct .E8 5 w⁻¹ (TableBExc.torusAct .E8 5 w (lam⁻¹ • x)) := by
          rw [h1]
      _ = TableBExc.torusAct .E8 5 (w⁻¹ * w) (lam⁻¹ • x) := by rw [← TableBExc.torusAct_mul]
      _ = lam⁻¹ • x := by rw [inv_mul_cancel, TableBExc.torusAct_one]
  have hfix : ∀ x ∈ NoOffRest.eigE8 5 lam,
      TableBExc.torusAct .E8 5 (u * w * u⁻¹ * w⁻¹) x = x := by
    intro x hx
    have hux : TableBExc.torusAct .E8 5 u⁻¹ x ∈ NoOffRest.eigE8 5 lam := huinv_mem x hx
    calc TableBExc.torusAct .E8 5 (u * w * u⁻¹ * w⁻¹) x
        = TableBExc.torusAct .E8 5 u (TableBExc.torusAct .E8 5 w
            (TableBExc.torusAct .E8 5 u⁻¹ (TableBExc.torusAct .E8 5 w⁻¹ x))) := by
          rw [TableBExc.torusAct_mul, TableBExc.torusAct_mul, TableBExc.torusAct_mul]
      _ = TableBExc.torusAct .E8 5 u (TableBExc.torusAct .E8 5 w
            (TableBExc.torusAct .E8 5 u⁻¹ (lam⁻¹ • x))) := by rw [hwEinv x hx]
      _ = TableBExc.torusAct .E8 5 u (TableBExc.torusAct .E8 5 w
            (lam⁻¹ • TableBExc.torusAct .E8 5 u⁻¹ x)) := by rw [torusAct_smul]
      _ = TableBExc.torusAct .E8 5 u (TableBExc.torusAct .E8 5 u⁻¹ x) := by
          rw [hwmem (lam⁻¹ • TableBExc.torusAct .E8 5 u⁻¹ x)
              (Submodule.smul_mem _ _ hux), smul_smul, mul_inv_cancel₀ hlam0, one_smul]
      _ = x := by rw [← TableBExc.torusAct_mul, mul_inv_cancel, TableBExc.torusAct_one]
  have hc1 : u * w * u⁻¹ * w⁻¹ = 1 := weylE8_eq_one_of_forall_fix_eigE8 hlam hfix
  have h1 : u * w * u⁻¹ = w := by
    have := congrArg (· * w) hc1
    simpa [mul_assoc] using this
  have h2 : u * w = w * u := by
    have := congrArg (· * u) h1
    simpa [mul_assoc] using this
  exact h2

end WeylFaithful

end NoOffE8Five

end CFSG.StandardType
