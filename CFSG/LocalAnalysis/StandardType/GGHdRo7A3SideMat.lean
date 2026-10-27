module

public import CFSG.LocalAnalysis.StandardType.GGHdRo7A3SideDefs
import CFSG.LocalAnalysis.StandardType.GGHdRo7A3Basic
import CFSG.LocalAnalysis.StandardType.GGTableBUnitActCore
import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyUDefs
import CFSG.LocalAnalysis.StandardType.GGCoxeterLabelAut
import CFSG.RankThree.PartOne.KF.UnitaryDiag

public section

namespace CFSG.StandardType.HdRo7A3

open CFSG.Assembly CFSG.ClassicalGroups.UnitaryFlag
open CFSG.SectionRank.OddCover (diagHom coe_diagHom diagHom_injective)

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

section Coord

variable {F : Type} [Field F] {m : ℕ}

private noncomputable def hdRo7A3SMAux_auxHom (m : ℕ) :
    Multiplicative ↥(a3Aug 3 m) →* (Fin m → Multiplicative (ZMod 3)) where
  toFun x i := Multiplicative.ofAdd ((Multiplicative.toAdd x).1 i)
  map_one' := by
    funext i
    rfl
  map_mul' x y := by
    funext i
    exact ofAdd_add ..

variable (u : Fˣ)

private noncomputable def hdRo7A3SMAux_dvec (hu : u ^ 3 = 1) :
    Multiplicative ↥(a3Aug 3 m) →* (Fin m → Fˣ) :=
  (MonoidHom.compLeft (TableBSymp.zmodPowHom hu) (Fin m)).comp
    (hdRo7A3SMAux_auxHom m)

private theorem hdRo7A3SMAux_dvec_apply (hu : u ^ 3 = 1) (x : Multiplicative ↥(a3Aug 3 m))
    (i : Fin m) :
    hdRo7A3SMAux_dvec u hu x i = u ^ ((Multiplicative.toAdd x).1 i).val := by
  simp [hdRo7A3SMAux_dvec, hdRo7A3SMAux_auxHom, TableBSymp.zmodPowHom_apply]

private theorem hdRo7A3SMAux_dvec_pow (hu : u ^ 3 = 1) (x : Multiplicative ↥(a3Aug 3 m))
    (i : Fin m) : hdRo7A3SMAux_dvec u hu x i ^ 3 = 1 := by
  rw [hdRo7A3SMAux_dvec_apply, ← pow_mul, mul_comm, pow_mul, hu, one_pow]

private theorem hdRo7A3SMAux_dvec_prod (hu : u ^ 3 = 1)
    (x : Multiplicative ↥(a3Aug 3 m)) : ∏ i, hdRo7A3SMAux_dvec u hu x i = 1 := by
  have hsum : ∑ i, (Multiplicative.toAdd x).1 i = 0 :=
    (Multiplicative.toAdd x).2
  have hz : (((∑ i, ((Multiplicative.toAdd x).1 i).val) : ℕ) : ZMod 3) = 0 := by
    rw [Nat.cast_sum]
    simpa only [ZMod.natCast_zmod_val] using hsum
  have hdvd : 3 ∣ ∑ i, ((Multiplicative.toAdd x).1 i).val :=
    (ZMod.natCast_eq_zero_iff _ 3).mp hz
  calc ∏ i, hdRo7A3SMAux_dvec u hu x i
      = ∏ i, u ^ ((Multiplicative.toAdd x).1 i).val := by
        exact Finset.prod_congr rfl (fun i _ => hdRo7A3SMAux_dvec_apply u hu x i)
    _ = u ^ ∑ i, ((Multiplicative.toAdd x).1 i).val :=
        Finset.prod_pow_eq_pow_sum _ _ _
    _ = 1 := by
        obtain ⟨k, hk⟩ := hdvd
        rw [hk, pow_mul, hu, one_pow]

private theorem hdRo7A3SMAux_dvec_injective (hu : u ^ 3 = 1) (hune : u ≠ 1) :
    Function.Injective (hdRo7A3SMAux_dvec (m := m) u hu) := by
  have hfact : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have huord : orderOf u = 3 := orderOf_eq_prime (p := 3) hu hune
  intro x y hxy
  have hcoord : ∀ i, ((Multiplicative.toAdd x).1 i) =
      ((Multiplicative.toAdd y).1 i) := by
    intro i
    have h := congrFun hxy i
    rw [hdRo7A3SMAux_dvec_apply, hdRo7A3SMAux_dvec_apply] at h
    have h2 := (pow_inj_mod (x := u)).mp h
    rw [huord, Nat.mod_eq_of_lt (ZMod.val_lt _), Nat.mod_eq_of_lt (ZMod.val_lt _)] at h2
    exact ZMod.val_injective 3 h2
  apply Multiplicative.toAdd.injective
  exact Subtype.ext (funext hcoord)

end Coord

section Torus

variable {G : Type} [Group G] {p : ℕ} {B Bs X : Subgroup G}
  {F : Type} [Field F] {m : ℕ}
  {φ : ↥(unitarySU 2 1 F m) →* ↥X}

private theorem hdRo7A3SMAux_dvec_pow_fun (u : Fˣ) (hu : u ^ 3 = 1)
    (x : Multiplicative ↥(a3Aug 3 m)) :
    hdRo7A3SMAux_dvec (m := m) u hu x ^ 3 = 1 := by
  funext i
  rw [Pi.pow_apply, hdRo7A3SMAux_dvec_pow u hu x i]
  rfl

private noncomputable def hdRo7A3SMAux_dSU (u : Fˣ) (hu : u ^ 3 = 1)
    (hM : UnitTB.Model φ) :
    Multiplicative ↥(a3Aug 3 m) →* ↥(unitarySU 2 1 F m) where
  toFun x := ⟨diagHom m (hdRo7A3SMAux_dvec (m := m) u hu x), by
    refine TableBUE.diagHom_mem_unitarySU hM.field ?_ ?_
    · intro k
      simpa using hdRo7A3SMAux_dvec_pow u hu x k
    · exact hdRo7A3SMAux_dvec_prod u hu x⟩
  map_one' := by apply Subtype.ext; simp
  map_mul' x y := by apply Subtype.ext; simp

private theorem hdRo7A3SMAux_dSU_pow_three (u : Fˣ) (hu : u ^ 3 = 1)
    (hM : UnitTB.Model φ) (x : Multiplicative ↥(a3Aug 3 m)) :
    hdRo7A3SMAux_dSU u hu hM x ^ 3 = 1 := by
  apply Subtype.ext
  rw [Subgroup.coe_pow, Subgroup.coe_one]
  show ((diagHom m (hdRo7A3SMAux_dvec (m := m) u hu x)) ^ 3 : GL (Fin m) F) = 1
  rw [← map_pow, hdRo7A3SMAux_dvec_pow_fun u hu x, map_one]

private noncomputable def hdRo7A3SMAux_tor (u : Fˣ) (hu : u ^ 3 = 1)
    (hM : UnitTB.Model φ) :
    Multiplicative ↥(a3Aug 3 m) →* ↥X :=
  φ.comp (hdRo7A3SMAux_dSU u hu hM)

private theorem hdRo7A3SMAux_tor_apply (u : Fˣ) (hu : u ^ 3 = 1)
    (hM : UnitTB.Model φ) (x : Multiplicative ↥(a3Aug 3 m)) :
    hdRo7A3SMAux_tor u hu hM x = φ (hdRo7A3SMAux_dSU u hu hM x) := rfl

private theorem hdRo7A3SMAux_tor_pow_three (u : Fˣ) (hu : u ^ 3 = 1)
    (hM : UnitTB.Model φ) (x : Multiplicative ↥(a3Aug 3 m)) :
    hdRo7A3SMAux_tor u hu hM x ^ 3 = 1 := by
  rw [hdRo7A3SMAux_tor_apply, ← map_pow, hdRo7A3SMAux_dSU_pow_three u hu hM x, map_one]

private theorem hdRo7A3SMAux_tor_fix
    (hN : Bs ≤ Subgroup.normalizer (X : Set G)) (u : Fˣ) (hu : u ^ 3 = 1)
    (hM : UnitTB.Model φ)
    (hdiag : ∀ b : ↥Bs, ∃ t : Fin m → F, LineU.ActsDiagU φ (ggGamma X hN b) t)
    (x : Multiplicative ↥(a3Aug 3 m)) (b : ↥Bs) :
    ggGamma X hN b (hdRo7A3SMAux_tor u hu hM x) = hdRo7A3SMAux_tor u hu hM x := by
  obtain ⟨t, ht⟩ := hdiag b
  refine ht.fix_of_diagonal (hdRo7A3SMAux_dSU u hu hM x)
    (v := fun i => (hdRo7A3SMAux_dvec (m := m) u hu x i : F)) ?_
  rw [← coe_diagHom]
  rfl

private theorem hdRo7A3SMAux_tor_centralizes
    (hN : Bs ≤ Subgroup.normalizer (X : Set G)) (u : Fˣ) (hu : u ^ 3 = 1)
    (hM : UnitTB.Model φ)
    (hdiag : ∀ b : ↥Bs, ∃ t : Fin m → F, LineU.ActsDiagU φ (ggGamma X hN b) t)
    (x : Multiplicative ↥(a3Aug 3 m)) :
    ((hdRo7A3SMAux_tor u hu hM x : ↥X) : G) ∈ Subgroup.centralizer (Bs : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  intro b hb
  have hfix := hdRo7A3SMAux_tor_fix hN u hu hM hdiag x ⟨b, hb⟩
  have h1 : b * ((hdRo7A3SMAux_tor u hu hM x : ↥X) : G) * b⁻¹ =
      ((hdRo7A3SMAux_tor u hu hM x : ↥X) : G) := by
    have h2 := congrArg (fun y : ↥X => (y : G)) hfix
    rwa [ggGamma_coe] at h2
  calc b * ((hdRo7A3SMAux_tor u hu hM x : ↥X) : G)
      = (b * ((hdRo7A3SMAux_tor u hu hM x : ↥X) : G) * b⁻¹) * b := by group
    _ = ((hdRo7A3SMAux_tor u hu hM x : ↥X) : G) * b := by rw [h1]

private theorem hdRo7A3SMAux_tor_mem_Bs
    (hN : Bs ≤ Subgroup.normalizer (X : Set G)) (u : Fˣ) (hu : u ^ 3 = 1)
    (hp3 : p = 3) (hBs : GGBstar p B Bs) (hM : UnitTB.Model φ)
    (hdiag : ∀ b : ↥Bs, ∃ t : Fin m → F, LineU.ActsDiagU φ (ggGamma X hN b) t)
    (x : Multiplicative ↥(a3Aug 3 m)) :
    ((hdRo7A3SMAux_tor u hu hM x : ↥X) : G) ∈ Bs := by
  refine hBs.2.2.2 _ (hdRo7A3SMAux_tor_centralizes hN u hu hM hdiag x) ?_
  rw [hp3]
  simpa using congrArg (fun y : ↥X => (y : G))
    (hdRo7A3SMAux_tor_pow_three u hu hM x)

private noncomputable def hdRo7A3SMAux_torB
    (hN : Bs ≤ Subgroup.normalizer (X : Set G)) (u : Fˣ) (hu : u ^ 3 = 1)
    (hp3 : p = 3) (hBs : GGBstar p B Bs) (hM : UnitTB.Model φ)
    (hdiag : ∀ b : ↥Bs, ∃ t : Fin m → F, LineU.ActsDiagU φ (ggGamma X hN b) t) :
    Multiplicative ↥(a3Aug 3 m) →* ↥Bs where
  toFun x := ⟨((hdRo7A3SMAux_tor u hu hM x : ↥X) : G),
    hdRo7A3SMAux_tor_mem_Bs hN u hu hp3 hBs hM hdiag x⟩
  map_one' := by apply Subtype.ext; simp [hdRo7A3SMAux_tor]
  map_mul' x y := by apply Subtype.ext; simp [hdRo7A3SMAux_tor]

private theorem hdRo7A3SMAux_torB_coe
    (hN : Bs ≤ Subgroup.normalizer (X : Set G)) (u : Fˣ) (hu : u ^ 3 = 1)
    (hp3 : p = 3) (hBs : GGBstar p B Bs) (hM : UnitTB.Model φ)
    (hdiag : ∀ b : ↥Bs, ∃ t : Fin m → F, LineU.ActsDiagU φ (ggGamma X hN b) t)
    (x : Multiplicative ↥(a3Aug 3 m)) :
    ((hdRo7A3SMAux_torB hN u hu hp3 hBs hM hdiag x : ↥Bs) : G) =
      ((hdRo7A3SMAux_tor u hu hM x : ↥X) : G) := rfl

end Torus

section Kernel

variable {G : Type} [Group G] {p : ℕ} {B Bs X : Subgroup G}
  {F : Type} [Field F] {m : ℕ} {φ : ↥(unitarySU 2 1 F m) →* ↥X}

private theorem hdRo7A3SMAux_units_card (hF : Nat.card F = 4) : Nat.card Fˣ = 3 := by
  rw [Nat.card_units, hF]

private theorem hdRo7A3SMAux_pow_val_eq (u : Fˣ) {a b : ℕ} (huord : orderOf u = 3)
    (h : u ^ a = u ^ b) (ha : a < 3) (hb : b < 3) : a = b := by
  have h2 := (pow_inj_mod (x := u)).mp h
  rw [huord, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at h2
  exact h2

private def hdRo7A3SMAux_ones (h3m : 3 ∣ m) : ↥(a3Aug 3 m) :=
  ⟨fun _ => 1, a3_const_mem h3m 1⟩

private theorem hdRo7A3SMAux_ones_val (h3m : 3 ∣ m) (i : Fin m) :
    ((hdRo7A3SMAux_ones (m := m) h3m : ↥(a3Aug 3 m)) : Fin m → ZMod 3) i = 1 := rfl

private noncomputable def hdRo7A3SMAux_gOne (h3m : 3 ∣ m) :
    Multiplicative ↥(a3Aug 3 m) :=
  Multiplicative.ofAdd (hdRo7A3SMAux_ones (m := m) h3m)

private theorem hdRo7A3SMAux_gOne_pow_val (h3m : 3 ∣ m) (k : ℕ) (i : Fin m) :
    (Multiplicative.toAdd (hdRo7A3SMAux_gOne (m := m) h3m ^ k)).1 i = (k : ZMod 3) := by
  have hkg : hdRo7A3SMAux_gOne (m := m) h3m ^ k =
      Multiplicative.ofAdd (k • hdRo7A3SMAux_ones (m := m) h3m) := ofAdd_nsmul k _
  rw [hkg]
  change (k • ((hdRo7A3SMAux_ones (m := m) h3m : ↥(a3Aug 3 m)) : Fin m → ZMod 3)) i =
    (k : ZMod 3)
  rw [Pi.smul_apply, hdRo7A3SMAux_ones_val, nsmul_eq_mul, mul_one]

private theorem hdRo7A3SMAux_eq_gOne_pow_of_const (h3m : 3 ∣ m)
    {x : Multiplicative ↥(a3Aug 3 m)} {c : ZMod 3}
    (hc : ∀ i, (Multiplicative.toAdd x).1 i = c) :
    x = hdRo7A3SMAux_gOne (m := m) h3m ^ c.val := by
  apply Multiplicative.toAdd.injective
  apply Subtype.ext
  funext i
  rw [hdRo7A3SMAux_gOne_pow_val, hc i, ZMod.natCast_zmod_val]

private theorem hdRo7A3SMAux_const_of_eq_gOne_pow (h3m : 3 ∣ m) (k : ℕ) :
    ∃ c : ZMod 3, ∀ i,
      (Multiplicative.toAdd (hdRo7A3SMAux_gOne (m := m) h3m ^ k)).1 i = c :=
  ⟨(k : ZMod 3), fun i => hdRo7A3SMAux_gOne_pow_val h3m k i⟩

private theorem hdRo7A3SMAux_orderOf_gOne (h3m : 3 ∣ m) (hm : 1 ≤ m) :
    orderOf (hdRo7A3SMAux_gOne (m := m) h3m) = 3 := by
  have hfact : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine orderOf_eq_prime (p := 3) ?_ ?_
  · rw [show hdRo7A3SMAux_gOne (m := m) h3m ^ 3 =
      Multiplicative.ofAdd (3 • hdRo7A3SMAux_ones (m := m) h3m) from ofAdd_nsmul 3 _]
    rw [show (3 : ℕ) • hdRo7A3SMAux_ones (m := m) h3m = 0 from ?_]
    · rfl
    · apply Subtype.ext
      funext i
      change (3 • ((hdRo7A3SMAux_ones (m := m) h3m : ↥(a3Aug 3 m)) : Fin m → ZMod 3)) i =
        (0 : ZMod 3)
      rw [Pi.smul_apply, hdRo7A3SMAux_ones_val, nsmul_eq_mul, mul_one]
      exact CharP.cast_eq_zero (ZMod 3) 3
  · intro h
    have h1 := hdRo7A3SMAux_gOne_pow_val (m := m) h3m 1 ⟨0, hm⟩
    rw [pow_one, h] at h1
    rw [show (Multiplicative.toAdd (1 : Multiplicative ↥(a3Aug 3 m))).1 ⟨0, hm⟩ = 0 from rfl]
      at h1
    exact one_ne_zero h1.symm

private theorem hdRo7A3SMAux_const_of_tor_eq_one (u : Fˣ) (hu : u ^ 3 = 1)
    (huord : orderOf u = 3) (hM : UnitTB.Model φ) (hm : 1 ≤ m)
    (x : Multiplicative ↥(a3Aug 3 m)) (hx : hdRo7A3SMAux_tor u hu hM x = 1) :
    ∃ c : ZMod 3, ∀ i, (Multiplicative.toAdd x).1 i = c := by
  have h1 : φ (hdRo7A3SMAux_dSU u hu hM x) = 1 := by
    rw [← hdRo7A3SMAux_tor_apply]
    exact hx
  obtain ⟨c, hc⟩ := hM.ker (hdRo7A3SMAux_dSU u hu hM x) h1
  have hc' : (Matrix.diagonal fun i => (hdRo7A3SMAux_dvec (m := m) u hu x i : F)) =
      Matrix.diagonal (fun _ => c) := by
    rw [← coe_diagHom]
    exact hc
  have hfun : (fun i => (hdRo7A3SMAux_dvec (m := m) u hu x i : F)) = fun _ => c :=
    Matrix.diagonal_injective hc'
  have hunit : ∀ i, hdRo7A3SMAux_dvec (m := m) u hu x i =
      hdRo7A3SMAux_dvec (m := m) u hu x ⟨0, hm⟩ := by
    intro i
    apply Units.ext
    rw [congrFun hfun i, congrFun hfun ⟨0, hm⟩]
  refine ⟨(Multiplicative.toAdd x).1 ⟨0, hm⟩, fun i => ?_⟩
  have hu2 : u ^ ((Multiplicative.toAdd x).1 i).val =
      u ^ ((Multiplicative.toAdd x).1 ⟨0, hm⟩).val := by
    have h := congrArg Units.val (hunit i)
    rw [hdRo7A3SMAux_dvec_apply, hdRo7A3SMAux_dvec_apply] at h
    exact Units.ext h
  exact ZMod.val_injective 3
    (hdRo7A3SMAux_pow_val_eq u huord hu2 (ZMod.val_lt _) (ZMod.val_lt _))

private theorem hdRo7A3SMAux_tor_eq_one_iff_const (u : Fˣ) (hu : u ^ 3 = 1)
    (huord : orderOf u = 3) (hM : UnitTB.Model φ) (h3m : 3 ∣ m) (hm : 1 ≤ m)
    (hMone : φ (hdRo7A3SMAux_dSU u hu hM (hdRo7A3SMAux_gOne (m := m) h3m)) = 1)
    (x : Multiplicative ↥(a3Aug 3 m)) :
    hdRo7A3SMAux_tor u hu hM x = 1 ↔
      ∃ c : ZMod 3, ∀ i, (Multiplicative.toAdd x).1 i = c := by
  constructor
  · intro hx
    exact hdRo7A3SMAux_const_of_tor_eq_one u hu huord hM hm x hx
  · rintro ⟨c, hc⟩
    rw [hdRo7A3SMAux_eq_gOne_pow_of_const h3m hc, map_pow, hdRo7A3SMAux_tor_apply, hMone,
      one_pow]

private theorem hdRo7A3SMAux_tor_eq_one_iff_one (u : Fˣ) (hu : u ^ 3 = 1)
    (huord : orderOf u = 3) (hM : UnitTB.Model φ) (h3m : 3 ∣ m) (hm : 1 ≤ m)
    (hU : φ (hdRo7A3SMAux_dSU u hu hM (hdRo7A3SMAux_gOne (m := m) h3m)) ≠ 1)
    (x : Multiplicative ↥(a3Aug 3 m)) :
    hdRo7A3SMAux_tor u hu hM x = 1 ↔ x = 1 := by
  constructor
  · intro hx
    obtain ⟨c, hc⟩ := hdRo7A3SMAux_const_of_tor_eq_one u hu huord hM hm x hx
    have hxc : x = hdRo7A3SMAux_gOne (m := m) h3m ^ c.val :=
      hdRo7A3SMAux_eq_gOne_pow_of_const h3m hc
    have hpow : (φ (hdRo7A3SMAux_dSU u hu hM (hdRo7A3SMAux_gOne (m := m) h3m))) ^ c.val = 1 := by
      rw [hxc, map_pow, hdRo7A3SMAux_tor_apply] at hx
      exact hx
    have hord : orderOf (φ (hdRo7A3SMAux_dSU u hu hM (hdRo7A3SMAux_gOne (m := m) h3m))) = 3 := by
      have hfact : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
      refine orderOf_eq_prime (p := 3) ?_ hU
      rw [← map_pow, hdRo7A3SMAux_dSU_pow_three u hu hM, map_one]
    have h3c : 3 ∣ c.val := by
      have h := orderOf_dvd_iff_pow_eq_one.mpr hpow
      rwa [hord] at h
    have hc0 : c = 0 := by
      apply ZMod.val_injective 3
      rw [ZMod.val_zero]
      exact Nat.eq_zero_of_dvd_of_lt h3c (ZMod.val_lt c)
    rw [hxc, hc0, ZMod.val_zero, pow_zero]
  · intro hx
    rw [hx, map_one]

private theorem hdRo7A3SMAux_const_of_mem_centralizer (u : Fˣ) (hu : u ^ 3 = 1)
    (huord : orderOf u = 3) (hM : UnitTB.Model φ) (hm : 3 ≤ m)
    (x : Multiplicative ↥(a3Aug 3 m))
    (hx : ((hdRo7A3SMAux_tor u hu hM x : ↥X) : G) ∈ Subgroup.centralizer (X : Set G)) :
    ∃ c : ZMod 3, ∀ i, (Multiplicative.toAdd x).1 i = c := by
  have hDt : ((hdRo7A3SMAux_dSU u hu hM x : ↥(unitarySU 2 1 F m)) : GL (Fin m) F) =
      Matrix.diagonal (fun i => (hdRo7A3SMAux_dvec (m := m) u hu x i : F)) := coe_diagHom _
  have hact : LineU.ActsDiagU φ (MulAut.conj (φ (hdRo7A3SMAux_dSU u hu hM x)))
      (fun i => (hdRo7A3SMAux_dvec (m := m) u hu x i : F)) := UnitTB.actsDiagU_conj hDt
  have hconj : MulAut.conj (φ (hdRo7A3SMAux_dSU u hu hM x)) = 1 := by
    refine MulEquiv.ext (fun y => ?_)
    apply Subtype.ext
    have hy := Subgroup.mem_centralizer_iff.mp hx (y : G) y.2
    rw [MulAut.conj_apply, MulAut.one_apply]
    change ((hdRo7A3SMAux_tor u hu hM x : ↥X) : G) * (y : G) *
      (((hdRo7A3SMAux_tor u hu hM x : ↥X) : G))⁻¹ = (y : G)
    calc ((hdRo7A3SMAux_tor u hu hM x : ↥X) : G) * (y : G) *
          (((hdRo7A3SMAux_tor u hu hM x : ↥X) : G))⁻¹
        = (y : G) * ((hdRo7A3SMAux_tor u hu hM x : ↥X) : G) *
          (((hdRo7A3SMAux_tor u hu hM x : ↥X) : G))⁻¹ := by rw [hy]
      _ = (y : G) := by group
  have h1 : LineU.ActsDiagU φ 1 (fun i => (hdRo7A3SMAux_dvec (m := m) u hu x i : F)) := by
    rw [hconj] at hact
    exact hact
  have h2 := LineU.ActsDiagU.ratio_eq hM.field hm hM.ker h1 (LineU.actsDiagU_one φ)
  have hti : ∀ i j, (hdRo7A3SMAux_dvec (m := m) u hu x i : F) =
      (hdRo7A3SMAux_dvec (m := m) u hu x j : F) := by
    intro i j
    have h := h2 i j
    simp only [inv_one, mul_one] at h
    exact (mul_inv_eq_one₀ (h1.ne_zero j)).mp h
  have h0m : 0 < m := by omega
  have hunit : ∀ i, hdRo7A3SMAux_dvec (m := m) u hu x i =
      hdRo7A3SMAux_dvec (m := m) u hu x ⟨0, h0m⟩ := by
    intro i
    apply Units.ext
    rw [hti i ⟨0, h0m⟩]
  refine ⟨(Multiplicative.toAdd x).1 ⟨0, h0m⟩, fun i => ?_⟩
  have hu2 : u ^ ((Multiplicative.toAdd x).1 i).val =
      u ^ ((Multiplicative.toAdd x).1 ⟨0, h0m⟩).val := by
    have h := congrArg Units.val (hunit i)
    rw [hdRo7A3SMAux_dvec_apply, hdRo7A3SMAux_dvec_apply] at h
    exact Units.ext h
  exact ZMod.val_injective 3
    (hdRo7A3SMAux_pow_val_eq u huord hu2 (ZMod.val_lt _) (ZMod.val_lt _))

private theorem hdRo7A3SMAux_card_aug {m : ℕ} (hm : 1 ≤ m) :
    Nat.card ↥(a3Aug 3 m) = 3 ^ (m - 1) := by
  let s : (Fin m → ZMod 3) →+ ZMod 3 :=
    ∑ i : Fin m, Pi.evalAddMonoidHom (fun _ : Fin m => ZMod 3) i
  have hs : Function.Surjective s := by
    intro c
    refine ⟨Pi.single ⟨0, hm⟩ c, ?_⟩
    have h := Fintype.sum_pi_single (M := fun _ : Fin m => ZMod 3) ⟨0, hm⟩ (fun _ => c)
    simpa [s, Pi.single_apply, eq_comm] using h
  have hker : s.ker = (a3Aug 3 m).toAddSubgroup := by
    ext u
    simp [s, a3Aug, AddMonoidHom.mem_ker]
  have h := AddSubgroup.card_ker_mul_card_of_surjective (f := s) hs
  rw [hker, Nat.card_zmod] at h
  have hc : Nat.card (Fin m → ZMod 3) = 3 ^ m := by
    simp
  rw [hc] at h
  have hpow : 3 ^ m = 3 ^ (m - 1) * 3 := by
    conv_lhs => rw [show m = (m - 1) + 1 by omega]
    rw [pow_succ]
  rw [hpow] at h
  exact Nat.eq_of_mul_eq_mul_right (by norm_num) h

end Kernel

section Shapes

variable {G : Type} [Group G] {p : ℕ} {B Bs X : Subgroup G}
  {F : Type} [Field F] {m : ℕ} {φ : ↥(unitarySU 2 1 F m) →* ↥X}

private theorem hdRo7A3SMAux_torB_eq_one_iff
    (hN : Bs ≤ Subgroup.normalizer (X : Set G)) (u : Fˣ) (hu : u ^ 3 = 1)
    (hp3 : p = 3) (hBs : GGBstar p B Bs) (hM : UnitTB.Model φ)
    (hdiag : ∀ b : ↥Bs, ∃ t : Fin m → F, LineU.ActsDiagU φ (ggGamma X hN b) t)
    (x : Multiplicative ↥(a3Aug 3 m)) :
    hdRo7A3SMAux_torB hN u hu hp3 hBs hM hdiag x = 1 ↔
      hdRo7A3SMAux_tor u hu hM x = 1 := by
  constructor
  · intro h
    have h2 : ((hdRo7A3SMAux_tor u hu hM x : ↥X) : G) = 1 := by
      rw [← hdRo7A3SMAux_torB_coe hN u hu hp3 hBs hM hdiag x, h]
      rfl
    exact Subtype.ext (by simpa using h2)
  · intro h
    apply Subtype.ext
    rw [hdRo7A3SMAux_torB_coe hN u hu hp3 hBs hM hdiag x, h]
    rfl

private noncomputable def hdRo7A3SMAux_kerEquivM (u : Fˣ) (hu : u ^ 3 = 1)
    (huord : orderOf u = 3) (hM : UnitTB.Model φ) (h3m : 3 ∣ m) (hm : 1 ≤ m)
    (hMone : φ (hdRo7A3SMAux_dSU u hu hM (hdRo7A3SMAux_gOne (m := m) h3m)) = 1) :
    ZMod 3 ≃ ↥(hdRo7A3SMAux_tor u hu hM).ker where
  toFun c := ⟨hdRo7A3SMAux_gOne (m := m) h3m ^ c.val, by
    rw [MonoidHom.mem_ker, map_pow, hdRo7A3SMAux_tor_apply, hMone, one_pow]⟩
  invFun y := (Multiplicative.toAdd (y.1)).1 ⟨0, hm⟩
  left_inv c := by
    show (Multiplicative.toAdd (hdRo7A3SMAux_gOne (m := m) h3m ^ c.val)).1 ⟨0, hm⟩ = c
    rw [hdRo7A3SMAux_gOne_pow_val, ZMod.natCast_zmod_val]
  right_inv y := by
    obtain ⟨c, hc⟩ := hdRo7A3SMAux_const_of_tor_eq_one u hu huord hM hm y.1
      (MonoidHom.mem_ker.mp y.2)
    have hc0 : (Multiplicative.toAdd y.1).1 ⟨0, hm⟩ = c := hc ⟨0, hm⟩
    apply Subtype.ext
    rw [hdRo7A3SMAux_eq_gOne_pow_of_const h3m hc, ← hc0]

private theorem hdRo7A3SMAux_ker_cardM (u : Fˣ) (hu : u ^ 3 = 1)
    (huord : orderOf u = 3) (hM : UnitTB.Model φ) (h3m : 3 ∣ m) (hm : 1 ≤ m)
    (hMone : φ (hdRo7A3SMAux_dSU u hu hM (hdRo7A3SMAux_gOne (m := m) h3m)) = 1) :
    Nat.card ↥(hdRo7A3SMAux_tor u hu hM).ker = 3 := by
  rw [← Nat.card_congr (hdRo7A3SMAux_kerEquivM u hu huord hM h3m hm hMone)]
  rw [Nat.card_zmod]

private theorem hdRo7A3SMAux_ker_cardU (u : Fˣ) (hu : u ^ 3 = 1)
    (huord : orderOf u = 3) (hM : UnitTB.Model φ) (h3m : 3 ∣ m) (hm : 1 ≤ m)
    (hU : φ (hdRo7A3SMAux_dSU u hu hM (hdRo7A3SMAux_gOne (m := m) h3m)) ≠ 1) :
    Nat.card ↥(hdRo7A3SMAux_tor u hu hM).ker = 1 := by
  have hbot : (hdRo7A3SMAux_tor u hu hM).ker = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro x hx
    rw [MonoidHom.mem_ker] at hx
    exact (hdRo7A3SMAux_tor_eq_one_iff_one u hu huord hM h3m hm hU x).mp hx
  rw [hbot]
  simp

private theorem hdRo7A3SMAux_kerB_card_eq
    (hN : Bs ≤ Subgroup.normalizer (X : Set G)) (u : Fˣ) (hu : u ^ 3 = 1)
    (hp3 : p = 3) (hBs : GGBstar p B Bs) (hM : UnitTB.Model φ)
    (hdiag : ∀ b : ↥Bs, ∃ t : Fin m → F, LineU.ActsDiagU φ (ggGamma X hN b) t) :
    Nat.card ↥(hdRo7A3SMAux_torB hN u hu hp3 hBs hM hdiag).ker =
      Nat.card ↥(hdRo7A3SMAux_tor u hu hM).ker := by
  exact Nat.card_congr (Equiv.subtypeEquivRight (fun x => by
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker]
    exact hdRo7A3SMAux_torB_eq_one_iff hN u hu hp3 hBs hM hdiag x))

private theorem hdRo7A3SMAux_range_cardM
    (hN : Bs ≤ Subgroup.normalizer (X : Set G)) (u : Fˣ) (hu : u ^ 3 = 1)
    (huord : orderOf u = 3) (hp3 : p = 3) (hBs : GGBstar p B Bs)
    (hM : UnitTB.Model φ)
    (hdiag : ∀ b : ↥Bs, ∃ t : Fin m → F, LineU.ActsDiagU φ (ggGamma X hN b) t)
    (h3m : 3 ∣ m) (hm : 2 ≤ m)
    (hMone : φ (hdRo7A3SMAux_dSU u hu hM (hdRo7A3SMAux_gOne (m := m) h3m)) = 1) :
    Nat.card ↥(hdRo7A3SMAux_torB hN u hu hp3 hBs hM hdiag).range = 3 ^ (m - 2) := by
  have hcard := Subgroup.card_ker_mul_card_range
    (hdRo7A3SMAux_torB hN u hu hp3 hBs hM hdiag)
  rw [hdRo7A3SMAux_kerB_card_eq hN u hu hp3 hBs hM hdiag,
    hdRo7A3SMAux_ker_cardM u hu huord hM h3m (by omega) hMone,
    Nat.card_congr (Multiplicative.toAdd (α := ↥(a3Aug 3 m))),
    hdRo7A3SMAux_card_aug (m := m) (by omega)] at hcard
  have hpow : 3 ^ (m - 1) = 3 * 3 ^ (m - 2) := by
    conv_lhs => rw [show m - 1 = (m - 2) + 1 by omega]
    rw [pow_succ]
    ring
  rw [hpow] at hcard
  exact Nat.eq_of_mul_eq_mul_left (by norm_num) hcard

private theorem hdRo7A3SMAux_range_cardU
    (hN : Bs ≤ Subgroup.normalizer (X : Set G)) (u : Fˣ) (hu : u ^ 3 = 1)
    (huord : orderOf u = 3) (hp3 : p = 3) (hBs : GGBstar p B Bs)
    (hM : UnitTB.Model φ)
    (hdiag : ∀ b : ↥Bs, ∃ t : Fin m → F, LineU.ActsDiagU φ (ggGamma X hN b) t)
    (h3m : 3 ∣ m) (hm : 1 ≤ m)
    (hU : φ (hdRo7A3SMAux_dSU u hu hM (hdRo7A3SMAux_gOne (m := m) h3m)) ≠ 1) :
    Nat.card ↥(hdRo7A3SMAux_torB hN u hu hp3 hBs hM hdiag).range = 3 ^ (m - 1) := by
  have hcard := Subgroup.card_ker_mul_card_range
    (hdRo7A3SMAux_torB hN u hu hp3 hBs hM hdiag)
  rw [hdRo7A3SMAux_kerB_card_eq hN u hu hp3 hBs hM hdiag,
    hdRo7A3SMAux_ker_cardU u hu huord hM h3m hm hU,
    Nat.card_congr (Multiplicative.toAdd (α := ↥(a3Aug 3 m))),
    hdRo7A3SMAux_card_aug (m := m) hm] at hcard
  simpa using hcard

private theorem hdRo7A3SMAux_range_eq_topU
    [Finite G]
    (hN : Bs ≤ Subgroup.normalizer (X : Set G)) (u : Fˣ) (hu : u ^ 3 = 1)
    (huord : orderOf u = 3) (hp3 : p = 3) (hBs : GGBstar p B Bs)
    (hM : UnitTB.Model φ)
    (hdiag : ∀ b : ↥Bs, ∃ t : Fin m → F, LineU.ActsDiagU φ (ggGamma X hN b) t)
    (h3m : 3 ∣ m) (hm : 1 ≤ m)
    (hU : φ (hdRo7A3SMAux_dSU u hu hM (hdRo7A3SMAux_gOne (m := m) h3m)) ≠ 1)
    (hcardBs : Nat.card ↥Bs ≤ 3 ^ (m - 1)) :
    (hdRo7A3SMAux_torB hN u hu hp3 hBs hM hdiag).range = ⊤ := by
  have hrange := hdRo7A3SMAux_range_cardU hN u hu huord hp3 hBs hM hdiag h3m hm hU
  have hle : Nat.card ↥(hdRo7A3SMAux_torB hN u hu hp3 hBs hM hdiag).range ≤
      Nat.card ↥Bs :=
    Nat.card_le_card_of_injective (fun x => (x.1 : ↥Bs))
      (fun x y h => Subtype.ext (by simpa using h))
  have heq : Nat.card ↥(hdRo7A3SMAux_torB hN u hu hp3 hBs hM hdiag).range =
      Nat.card ↥Bs := le_antisymm hle (by rw [hrange]; exact hcardBs)
  exact Subgroup.eq_top_of_card_eq _ heq

private theorem hdRo7A3SMAux_z_notMem_rangeM
    (hN : Bs ≤ Subgroup.normalizer (X : Set G)) (u : Fˣ) (hu : u ^ 3 = 1)
    (huord : orderOf u = 3) (hp3 : p = 3) (hBs : GGBstar p B Bs)
    (hM : UnitTB.Model φ)
    (hdiag : ∀ b : ↥Bs, ∃ t : Fin m → F, LineU.ActsDiagU φ (ggGamma X hN b) t)
    (h3m : 3 ∣ m) (hm : 3 ≤ m)
    (hMone : φ (hdRo7A3SMAux_dSU u hu hM (hdRo7A3SMAux_gOne (m := m) h3m)) = 1)
    {z : G} (hzB : z ∈ Bs) (hz1 : z ≠ 1)
    (hzC : z ∈ Subgroup.centralizer (X : Set G)) :
    (⟨z, hzB⟩ : ↥Bs) ∉ (hdRo7A3SMAux_torB hN u hu hp3 hBs hM hdiag).range := by
  rintro ⟨x, hx⟩
  have hxG : ((hdRo7A3SMAux_tor u hu hM x : ↥X) : G) = z := by
    rw [← hdRo7A3SMAux_torB_coe hN u hu hp3 hBs hM hdiag x, hx]
  have hxZ : ((hdRo7A3SMAux_tor u hu hM x : ↥X) : G) ∈
      Subgroup.centralizer (X : Set G) := by
    rw [hxG]
    exact hzC
  obtain ⟨c, hc⟩ := hdRo7A3SMAux_const_of_mem_centralizer u hu huord hM hm x hxZ
  have hxc : x = hdRo7A3SMAux_gOne (m := m) h3m ^ c.val :=
    hdRo7A3SMAux_eq_gOne_pow_of_const h3m hc
  have h1 : hdRo7A3SMAux_tor u hu hM x = 1 := by
    rw [hxc, map_pow, hdRo7A3SMAux_tor_apply, hMone, one_pow]
  have h2 : ((hdRo7A3SMAux_tor u hu hM x : ↥X) : G) = 1 := by
    rw [h1]
    rfl
  rw [h2] at hxG
  exact hz1 hxG.symm

private theorem hdRo7A3SMAux_decompM
    [Finite G]
    (hN : Bs ≤ Subgroup.normalizer (X : Set G)) (u : Fˣ) (hu : u ^ 3 = 1)
    (huord : orderOf u = 3) (hp3 : p = 3) (hBs : GGBstar p B Bs)
    (hM : UnitTB.Model φ)
    (hdiag : ∀ b : ↥Bs, ∃ t : Fin m → F, LineU.ActsDiagU φ (ggGamma X hN b) t)
    (h3m : 3 ∣ m) (hm : 2 ≤ m)
    (hMone : φ (hdRo7A3SMAux_dSU u hu hM (hdRo7A3SMAux_gOne (m := m) h3m)) = 1)
    {z : G} (hzB : z ∈ Bs) (hz1 : z ≠ 1) (hzp : z ^ p = 1)
    (hzC : z ∈ Subgroup.centralizer (X : Set G))
    (hcardBs : Nat.card ↥Bs ≤ 3 ^ (m - 1)) :
    ∀ b : ↥Bs, ∃ w : Multiplicative ↥(a3Aug 3 m), ∃ k : ℕ,
      b = hdRo7A3SMAux_torB hN u hu hp3 hBs hM hdiag w * (⟨z, hzB⟩ : ↥Bs) ^ k := by
  classical
  set zB : ↥Bs := ⟨z, hzB⟩ with hzBdef
  have hz3 : zB ^ 3 = 1 := by
    apply Subtype.ext
    rw [Subgroup.coe_pow, Subgroup.coe_one]
    rw [hp3] at hzp
    exact hzp
  set Z : Subgroup ↥Bs := Subgroup.zpowers zB with hZdef
  have hzBne : zB ≠ 1 := fun h => hz1 (by
    have := congrArg Subtype.val h
    simpa [hzBdef] using this)
  have hzord : orderOf zB = 3 := orderOf_eq_prime hz3 hzBne
  have hZcard : Nat.card ↥Z = 3 := by
    rw [hZdef, Nat.card_zpowers, hzord]
  set R : Subgroup ↥Bs := (hdRo7A3SMAux_torB hN u hu hp3 hBs hM hdiag).range with hRdef
  have hcardR := hdRo7A3SMAux_range_cardM hN u hu huord hp3 hBs hM hdiag h3m hm hMone
  have hRinfZ : R ⊓ Z = ⊥ := by
    let he : ↥((R ⊓ Z).subgroupOf Z) ≃ ↥(R ⊓ Z) :=
      { toFun := fun x => ⟨x.1.1, Subgroup.mem_subgroupOf.mp x.2⟩
        invFun := fun x => ⟨⟨x.1, x.2.2⟩, Subgroup.mem_subgroupOf.mpr x.2⟩
        left_inv := fun x => Subtype.ext (Subtype.ext rfl)
        right_inv := fun x => Subtype.ext rfl }
    have hdvd : Nat.card ↥(R ⊓ Z) ∣ 3 := by
      have h := Subgroup.card_subgroup_dvd_card ((R ⊓ Z).subgroupOf Z)
      rwa [Nat.card_congr he, hZcard] at h
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h3
    · exact Subgroup.eq_bot_of_card_eq _ h1
    · exfalso
      have hZle : Z ≤ R := by
        have heq : R ⊓ Z = Z :=
          Subgroup.eq_of_le_of_card_ge inf_le_right (by rw [h3, hZcard])
        rw [← heq]
        exact inf_le_left
      exact hdRo7A3SMAux_z_notMem_rangeM hN u hu huord hp3 hBs hM hdiag h3m (by omega)
        hMone hzB hz1 hzC (hZle (Subgroup.mem_zpowers zB))
  have hinj : Function.Injective
      (fun q : ↥R × ↥Z => (q.1.1 * q.2.1 : ↥Bs)) := by
    rintro ⟨⟨r1, hr1⟩, ⟨z1, hz1r⟩⟩ ⟨⟨r2, hr2⟩, ⟨z2, hz2r⟩⟩ h
    have h1 : r1 * z1 = r2 * z2 := h
    have h2 : r2⁻¹ * r1 = z2 * z1⁻¹ := by
      apply mul_left_cancel (a := r2)
      rw [mul_inv_cancel_left]
      calc r1 = (r1 * z1) * z1⁻¹ := by group
        _ = (r2 * z2) * z1⁻¹ := by rw [h1]
        _ = r2 * (z2 * z1⁻¹) := by group
    have hRmem : r2⁻¹ * r1 ∈ R := R.mul_mem (R.inv_mem hr2) hr1
    have hZmem : z2 * z1⁻¹ ∈ Z := Z.mul_mem hz2r (Z.inv_mem hz1r)
    have hmem : r2⁻¹ * r1 ∈ R ⊓ Z := Subgroup.mem_inf.mpr ⟨hRmem, h2 ▸ hZmem⟩
    rw [hRinfZ, Subgroup.mem_bot] at hmem
    have hr : r1 = r2 := by
      have := congrArg (fun y => r2 * y) hmem
      simpa [mul_assoc] using this
    have hz : z1 = z2 := by
      have h3 : z2 * z1⁻¹ = 1 := by
        rw [← h2]
        exact hmem
      exact (mul_inv_eq_one.mp h3).symm
    refine Prod.ext (Subtype.ext hr) (Subtype.ext hz)
  have hcarddom : Nat.card (↥R × ↥Z) = 3 ^ (m - 1) := by
    rw [Nat.card_prod, hcardR, hZcard]
    have hpow : 3 ^ (m - 1) = 3 ^ (m - 2) * 3 := by
      conv_lhs => rw [show m - 1 = (m - 2) + 1 by omega]
      rw [pow_succ]
    rw [hpow]
  have hle : Nat.card (↥R × ↥Z) ≤ Nat.card ↥Bs :=
    Nat.card_le_card_of_injective _ hinj
  have hcardBs_eq : Nat.card ↥Bs = 3 ^ (m - 1) := by
    refine le_antisymm hcardBs ?_
    rw [← hcarddom]
    exact hle
  have hbij : Function.Bijective (fun q : ↥R × ↥Z => (q.1.1 * q.2.1 : ↥Bs)) := by
    refine (Nat.bijective_iff_injective_and_card _).mpr ⟨hinj, ?_⟩
    rw [hcarddom, hcardBs_eq]
  have hfin : IsOfFinOrder zB :=
    isOfFinOrder_iff_pow_eq_one.mpr ⟨3, by norm_num, hz3⟩
  intro b
  obtain ⟨q, hq⟩ := hbij.surjective b
  obtain ⟨w, hw⟩ := q.1.2
  have hpow : q.2.1 ∈ Submonoid.powers zB :=
    (hfin.mem_powers_iff_mem_zpowers).mpr q.2.2
  obtain ⟨k, hk⟩ := (Submonoid.mem_powers_iff _ _).mp hpow
  refine ⟨w, k, ?_⟩
  calc b = q.1.1 * q.2.1 := hq.symm
    _ = hdRo7A3SMAux_torB hN u hu hp3 hBs hM hdiag w * zB ^ k := by rw [← hw, ← hk]

end Shapes

section Theta

variable {G : Type} [Group G] {p : ℕ} {B Bs X : Subgroup G}
  {F : Type} [Field F] {m : ℕ} {φ : ↥(unitarySU 2 1 F m) →* ↥X}

private instance hdRo7A3SMAux_instAddCommGroup {Bs : Subgroup G} [IsMulCommutative ↥Bs] :
    AddCommGroup (Additive ↥Bs) :=
  { (inferInstance : AddGroup (Additive ↥Bs)) with
    add_comm := fun a b => congrArg Additive.ofMul
      (IsMulCommutative.is_comm.comm (Additive.toMul a) (Additive.toMul b)) }

private instance hdRo7A3SMAux_instModule {Bs : Subgroup G} [IsMulCommutative ↥Bs]
    [Fact (∀ b : ↥Bs, b ^ 3 = 1)] : Module (ZMod 3) (Additive ↥Bs) :=
  letI := hdRo7A3SMAux_instAddCommGroup (Bs := Bs)
  AddCommGroup.zmodModule (n := 3) fun a => by
    have h : (Additive.toMul a) ^ 3 = 1 :=
      (Fact.out : ∀ b : ↥Bs, b ^ 3 = 1) (Additive.toMul a)
    rw [← ofMul_toMul a, ← ofMul_pow, h, ofMul_one]

private theorem hdRo7A3SMAux_mul_pow_comm {M : Type} [Monoid M]
    (hcomm : ∀ a b : M, a * b = b * a) (a b : M) (n : ℕ) :
    (a * b) ^ n = a ^ n * b ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, ih, pow_succ, pow_succ]
    calc a ^ n * b ^ n * (a * b) = a ^ n * (b ^ n * a) * b := by group
      _ = a ^ n * (a * b ^ n) * b := by rw [hcomm (b ^ n) a]
      _ = a ^ n * a * (b ^ n * b) := by group

private theorem hdRo7A3SMAux_smul_eq_nsmul {A : Type} [AddCommGroup A] [Module (ZMod 3) A]
    (c : ZMod 3) (a : A) : c • a = c.val • a := by
  rw [← Nat.cast_smul_eq_nsmul (ZMod 3) c.val a, ZMod.natCast_zmod_val]

private noncomputable def hdRo7A3SMAux_proj (i0 : Fin m) :
    (Fin m → ZMod 3) →ₗ[ZMod 3] ↥(a3Aug 3 m) where
  toFun v := ⟨v - (∑ i, v i) • (Pi.single i0 (1 : ZMod 3)), by
    rw [mem_a3Aug]
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
    have hs : (∑ i : Fin m, (Pi.single i0 (1 : ZMod 3) : Fin m → ZMod 3) i) = 1 := by
      have h := Fintype.sum_pi_single (M := fun _ : Fin m => ZMod 3) i0 (fun _ => (1 : ZMod 3))
      simpa [Pi.single_apply, eq_comm] using h
    rw [hs, mul_one, sub_self]⟩
  map_add' v w := by
    apply Subtype.ext
    funext i
    show v i + w i - (∑ x, (v + w) x) • (Pi.single i0 (1 : ZMod 3) : Fin m → ZMod 3) i =
      (v i - (∑ x, v x) • (Pi.single i0 (1 : ZMod 3) : Fin m → ZMod 3) i) +
      (w i - (∑ x, w x) • (Pi.single i0 (1 : ZMod 3) : Fin m → ZMod 3) i)
    simp only [Pi.add_apply, smul_eq_mul]
    rw [Finset.sum_add_distrib]
    ring
  map_smul' c v := by
    apply Subtype.ext
    funext i
    show c * v i - (∑ x, c * v x) • (Pi.single i0 (1 : ZMod 3) : Fin m → ZMod 3) i =
      c * (v i - (∑ x, v x) • (Pi.single i0 (1 : ZMod 3) : Fin m → ZMod 3) i)
    rw [← Finset.mul_sum]
    simp only [smul_eq_mul]
    ring

private theorem hdRo7A3SMAux_proj_apply {i0 : Fin m} {v : Fin m → ZMod 3}
    (hv : v ∈ a3Aug 3 m) :
    ((hdRo7A3SMAux_proj (m := m) i0 v : ↥(a3Aug 3 m)) : Fin m → ZMod 3) = v := by
  funext i
  show v i - (∑ j, v j) • (Pi.single i0 (1 : ZMod 3) : Fin m → ZMod 3) i = v i
  rw [mem_a3Aug] at hv
  rw [hv]
  simp

private noncomputable def hdRo7A3SMAux_sumHom (m : ℕ) :
    (Fin m → ZMod 3) →+ ZMod 3 :=
  ∑ i : Fin m, Pi.evalAddMonoidHom (fun _ : Fin m => ZMod 3) i

section ThetaDef

variable (hN : Bs ≤ Subgroup.normalizer (X : Set G)) (uF : Fˣ) (hu : uF ^ 3 = 1)
  (hp3 : p = 3) (hBs : GGBstar p B Bs) (hM : UnitTB.Model φ)
  (hdiag : ∀ b : ↥Bs, ∃ t : Fin m → F, LineU.ActsDiagU φ (ggGamma X hN b) t)
  (i0 : Fin m) (κ : ZMod 3) {z : G} (hzB : z ∈ Bs)
  (hz3 : (⟨z, hzB⟩ : ↥Bs) ^ 3 = 1)
  [IsMulCommutative ↥Bs] [Fact (∀ b : ↥Bs, b ^ 3 = 1)]

private noncomputable def hdRo7A3SMAux_thetaT (v : Fin m → ZMod 3) : ↥Bs :=
  hdRo7A3SMAux_torB hN uF hu hp3 hBs hM hdiag
    (Multiplicative.ofAdd (κ • hdRo7A3SMAux_proj (m := m) i0 v))

private noncomputable def hdRo7A3SMAux_thetaS (v : Fin m → ZMod 3) : ↥Bs :=
  TableBSymp.zmodPowHom hz3 (Multiplicative.ofAdd (∑ i, v i))

omit [IsMulCommutative ↥Bs] [Fact (∀ (b : ↥Bs), b ^ 3 = 1)] in
private theorem hdRo7A3SMAux_thetaT_add (v w : Fin m → ZMod 3) :
    hdRo7A3SMAux_thetaT hN uF hu hp3 hBs hM hdiag i0 κ (v + w) =
      hdRo7A3SMAux_thetaT hN uF hu hp3 hBs hM hdiag i0 κ v *
        hdRo7A3SMAux_thetaT hN uF hu hp3 hBs hM hdiag i0 κ w := by
  show hdRo7A3SMAux_torB hN uF hu hp3 hBs hM hdiag
      (Multiplicative.ofAdd (κ • hdRo7A3SMAux_proj (m := m) i0 (v + w))) =
    hdRo7A3SMAux_torB hN uF hu hp3 hBs hM hdiag
        (Multiplicative.ofAdd (κ • hdRo7A3SMAux_proj (m := m) i0 v)) *
      hdRo7A3SMAux_torB hN uF hu hp3 hBs hM hdiag
        (Multiplicative.ofAdd (κ • hdRo7A3SMAux_proj (m := m) i0 w))
  rw [map_add (hdRo7A3SMAux_proj (m := m) i0) v w, smul_add, ofAdd_add, map_mul]

omit [IsMulCommutative ↥Bs] [Fact (∀ (b : ↥Bs), b ^ 3 = 1)] in
private theorem hdRo7A3SMAux_thetaS_add (v w : Fin m → ZMod 3) :
    hdRo7A3SMAux_thetaS hzB hz3 (v + w) =
      hdRo7A3SMAux_thetaS hzB hz3 v * hdRo7A3SMAux_thetaS hzB hz3 w := by
  show TableBSymp.zmodPowHom hz3 (Multiplicative.ofAdd (∑ i, (v + w) i)) =
    TableBSymp.zmodPowHom hz3 (Multiplicative.ofAdd (∑ i, v i)) *
      TableBSymp.zmodPowHom hz3 (Multiplicative.ofAdd (∑ i, w i))
  simp only [Pi.add_apply]
  rw [Finset.sum_add_distrib, ofAdd_add, map_mul]

omit [IsMulCommutative ↥Bs] [Fact (∀ (b : ↥Bs), b ^ 3 = 1)] in
private theorem hdRo7A3SMAux_thetaT_smul (c : ZMod 3) (v : Fin m → ZMod 3) :
    hdRo7A3SMAux_thetaT hN uF hu hp3 hBs hM hdiag i0 κ (c • v) =
      hdRo7A3SMAux_thetaT hN uF hu hp3 hBs hM hdiag i0 κ v ^ c.val := by
  show hdRo7A3SMAux_torB hN uF hu hp3 hBs hM hdiag
      (Multiplicative.ofAdd (κ • hdRo7A3SMAux_proj (m := m) i0 (c • v))) =
    (hdRo7A3SMAux_torB hN uF hu hp3 hBs hM hdiag
      (Multiplicative.ofAdd (κ • hdRo7A3SMAux_proj (m := m) i0 v))) ^ c.val
  rw [map_smul (hdRo7A3SMAux_proj (m := m) i0) c v,
    smul_comm κ c (hdRo7A3SMAux_proj (m := m) i0 v),
    hdRo7A3SMAux_smul_eq_nsmul c (κ • hdRo7A3SMAux_proj (m := m) i0 v),
    ofAdd_nsmul, map_pow]

omit [IsMulCommutative ↥Bs] [Fact (∀ (b : ↥Bs), b ^ 3 = 1)] in
private theorem hdRo7A3SMAux_thetaS_smul (c : ZMod 3) (v : Fin m → ZMod 3) :
    hdRo7A3SMAux_thetaS hzB hz3 (c • v) = hdRo7A3SMAux_thetaS hzB hz3 v ^ c.val := by
  show TableBSymp.zmodPowHom hz3 (Multiplicative.ofAdd (∑ i, (c • v) i)) =
    (TableBSymp.zmodPowHom hz3 (Multiplicative.ofAdd (∑ i, v i))) ^ c.val
  simp only [Pi.smul_apply]
  rw [← map_pow, ← ofAdd_nsmul, ← hdRo7A3SMAux_smul_eq_nsmul c (∑ i, v i), Finset.smul_sum]

private noncomputable def hdRo7A3SMAux_theta :
    (Fin m → ZMod 3) →ₗ[ZMod 3] Additive ↥Bs where
  toFun v := Additive.ofMul
    (hdRo7A3SMAux_thetaT hN uF hu hp3 hBs hM hdiag i0 κ v *
      hdRo7A3SMAux_thetaS hzB hz3 v)
  map_add' v w := by
    calc Additive.ofMul
          (hdRo7A3SMAux_thetaT hN uF hu hp3 hBs hM hdiag i0 κ (v + w) *
            hdRo7A3SMAux_thetaS hzB hz3 (v + w))
        = Additive.ofMul
          ((hdRo7A3SMAux_thetaT hN uF hu hp3 hBs hM hdiag i0 κ v *
            hdRo7A3SMAux_thetaT hN uF hu hp3 hBs hM hdiag i0 κ w) *
          (hdRo7A3SMAux_thetaS hzB hz3 v * hdRo7A3SMAux_thetaS hzB hz3 w)) := by
          rw [hdRo7A3SMAux_thetaT_add, hdRo7A3SMAux_thetaS_add]
      _ = Additive.ofMul
          ((hdRo7A3SMAux_thetaT hN uF hu hp3 hBs hM hdiag i0 κ v *
            hdRo7A3SMAux_thetaS hzB hz3 v) *
          (hdRo7A3SMAux_thetaT hN uF hu hp3 hBs hM hdiag i0 κ w *
            hdRo7A3SMAux_thetaS hzB hz3 w)) := by
          congr 1
          calc hdRo7A3SMAux_thetaT hN uF hu hp3 hBs hM hdiag i0 κ v *
                hdRo7A3SMAux_thetaT hN uF hu hp3 hBs hM hdiag i0 κ w *
                (hdRo7A3SMAux_thetaS hzB hz3 v * hdRo7A3SMAux_thetaS hzB hz3 w) =
              hdRo7A3SMAux_thetaT hN uF hu hp3 hBs hM hdiag i0 κ v *
                (hdRo7A3SMAux_thetaT hN uF hu hp3 hBs hM hdiag i0 κ w *
                  hdRo7A3SMAux_thetaS hzB hz3 v) * hdRo7A3SMAux_thetaS hzB hz3 w := by
                group
            _ = hdRo7A3SMAux_thetaT hN uF hu hp3 hBs hM hdiag i0 κ v *
                (hdRo7A3SMAux_thetaS hzB hz3 v *
                  hdRo7A3SMAux_thetaT hN uF hu hp3 hBs hM hdiag i0 κ w) *
                hdRo7A3SMAux_thetaS hzB hz3 w := by
                rw [IsMulCommutative.is_comm.comm
                  (hdRo7A3SMAux_thetaT hN uF hu hp3 hBs hM hdiag i0 κ w)
                  (hdRo7A3SMAux_thetaS hzB hz3 v)]
            _ = (hdRo7A3SMAux_thetaT hN uF hu hp3 hBs hM hdiag i0 κ v *
                  hdRo7A3SMAux_thetaS hzB hz3 v) *
                (hdRo7A3SMAux_thetaT hN uF hu hp3 hBs hM hdiag i0 κ w *
                  hdRo7A3SMAux_thetaS hzB hz3 w) := by
                group
      _ = Additive.ofMul
          (hdRo7A3SMAux_thetaT hN uF hu hp3 hBs hM hdiag i0 κ v *
            hdRo7A3SMAux_thetaS hzB hz3 v) +
          Additive.ofMul
            (hdRo7A3SMAux_thetaT hN uF hu hp3 hBs hM hdiag i0 κ w *
              hdRo7A3SMAux_thetaS hzB hz3 w) := by
          rw [ofMul_mul]
  map_smul' c v := by
    calc Additive.ofMul
          (hdRo7A3SMAux_thetaT hN uF hu hp3 hBs hM hdiag i0 κ (c • v) *
            hdRo7A3SMAux_thetaS hzB hz3 (c • v))
        = Additive.ofMul
          ((hdRo7A3SMAux_thetaT hN uF hu hp3 hBs hM hdiag i0 κ v) ^ c.val *
            (hdRo7A3SMAux_thetaS hzB hz3 v) ^ c.val) := by
          rw [hdRo7A3SMAux_thetaT_smul, hdRo7A3SMAux_thetaS_smul]
      _ = Additive.ofMul
          ((hdRo7A3SMAux_thetaT hN uF hu hp3 hBs hM hdiag i0 κ v *
            hdRo7A3SMAux_thetaS hzB hz3 v) ^ c.val) := by
          congr 1
          exact (hdRo7A3SMAux_mul_pow_comm
            (fun a b => IsMulCommutative.is_comm.comm a b)
            (hdRo7A3SMAux_thetaT hN uF hu hp3 hBs hM hdiag i0 κ v)
            (hdRo7A3SMAux_thetaS hzB hz3 v) c.val).symm
      _ = c • Additive.ofMul
          (hdRo7A3SMAux_thetaT hN uF hu hp3 hBs hM hdiag i0 κ v *
            hdRo7A3SMAux_thetaS hzB hz3 v) := by
          rw [hdRo7A3SMAux_smul_eq_nsmul c, ofMul_pow]

private theorem hdRo7A3SMAux_theta_apply (v : Fin m → ZMod 3) :
    hdRo7A3SMAux_theta hN uF hu hp3 hBs hM hdiag i0 κ hzB hz3 v =
      Additive.ofMul
        (hdRo7A3SMAux_thetaT hN uF hu hp3 hBs hM hdiag i0 κ v *
          hdRo7A3SMAux_thetaS hzB hz3 v) := rfl

private theorem hdRo7A3SMAux_theta_apply_aug {v : Fin m → ZMod 3}
    (hv : v ∈ a3Aug 3 m) :
    hdRo7A3SMAux_theta hN uF hu hp3 hBs hM hdiag i0 κ hzB hz3 v =
      Additive.ofMul (hdRo7A3SMAux_torB hN uF hu hp3 hBs hM hdiag
        (Multiplicative.ofAdd (κ • (⟨v, hv⟩ : ↥(a3Aug 3 m))))) := by
  rw [hdRo7A3SMAux_theta_apply]
  simp only [hdRo7A3SMAux_thetaT, hdRo7A3SMAux_thetaS]
  have hproj : hdRo7A3SMAux_proj (m := m) i0 v = ⟨v, hv⟩ :=
    Subtype.ext (hdRo7A3SMAux_proj_apply hv)
  have hsum : (∑ i, v i) = 0 := hv
  rw [hproj, hsum]
  simp

end ThetaDef

end Theta

section Frame

variable {G : Type} [Group G] {p : ℕ} {B Bs X : Subgroup G}
  {F : Type} [Field F] {m : ℕ} {φ : ↥(unitarySU 2 1 F m) →* ↥X}

private theorem hdRo7A3SMAux_kappaU
    [Finite G]
    (hN : Bs ≤ Subgroup.normalizer (X : Set G)) (uF : Fˣ) (hu : uF ^ 3 = 1)
    (huord : orderOf uF = 3) (hp3 : p = 3) (hBs : GGBstar p B Bs) (hM : UnitTB.Model φ)
    (hdiag : ∀ b : ↥Bs, ∃ t : Fin m → F, LineU.ActsDiagU φ (ggGamma X hN b) t)
    (h3m : 3 ∣ m) (hm2 : 2 ≤ m) {z : G} (hzB : z ∈ Bs) (hz1 : z ≠ 1)
    (hzC : z ∈ Subgroup.centralizer (X : Set G))
    (hcardBs : Nat.card ↥Bs ≤ 3 ^ (m - 1))
    (hU : φ (hdRo7A3SMAux_dSU uF hu hM (hdRo7A3SMAux_gOne (m := m) h3m)) ≠ 1) :
    ∃ κ : ZMod 3, κ ≠ 0 ∧
      (⟨z, hzB⟩ : ↥Bs) = hdRo7A3SMAux_torB hN uF hu hp3 hBs hM hdiag
        (Multiplicative.ofAdd (κ • hdRo7A3SMAux_ones (m := m) h3m)) := by
  set zB : ↥Bs := ⟨z, hzB⟩ with hzBdef
  have htop := hdRo7A3SMAux_range_eq_topU hN uF hu huord hp3 hBs hM hdiag h3m
    (by omega) hU hcardBs
  have hzrange : zB ∈ (hdRo7A3SMAux_torB hN uF hu hp3 hBs hM hdiag).range := by
    rw [htop]
    exact Subgroup.mem_top _
  obtain ⟨w, hw⟩ := hzrange
  have hzC' : ((hdRo7A3SMAux_tor uF hu hM w : ↥X) : G) ∈
      Subgroup.centralizer (X : Set G) := by
    rw [← hdRo7A3SMAux_torB_coe hN uF hu hp3 hBs hM hdiag w, hw]
    exact hzC
  obtain ⟨c, hc⟩ := hdRo7A3SMAux_const_of_mem_centralizer uF hu huord hM
    (Nat.le_of_dvd (by omega) h3m) w hzC'
  refine ⟨c, ?_, ?_⟩
  · intro hc0
    have hw1 : w = 1 := by
      rw [hdRo7A3SMAux_eq_gOne_pow_of_const h3m hc, hc0, ZMod.val_zero, pow_zero]
    have hz1' : zB = 1 := by rw [← hw, hw1, map_one]
    exact hz1 (by
      have h2 : ((zB : ↥Bs) : G) = 1 := by rw [hz1']; rfl
      exact h2)
  · rw [← hw, hdRo7A3SMAux_eq_gOne_pow_of_const h3m hc]
    show (hdRo7A3SMAux_torB hN uF hu hp3 hBs hM hdiag)
        (Multiplicative.ofAdd (hdRo7A3SMAux_ones (m := m) h3m) ^ c.val) =
      (hdRo7A3SMAux_torB hN uF hu hp3 hBs hM hdiag)
        (Multiplicative.ofAdd (c • hdRo7A3SMAux_ones (m := m) h3m))
    rw [← ofAdd_nsmul, hdRo7A3SMAux_smul_eq_nsmul c (hdRo7A3SMAux_ones (m := m) h3m)]

private theorem hdRo7A3SMAux_frameU
    [Finite G]
    [IsMulCommutative ↥Bs] [Fact (∀ b : ↥Bs, b ^ 3 = 1)]
    (hN : Bs ≤ Subgroup.normalizer (X : Set G)) (uF : Fˣ) (hu : uF ^ 3 = 1)
    (huord : orderOf uF = 3) (hp3 : p = 3) (hBs : GGBstar p B Bs) (hM : UnitTB.Model φ)
    (hdiag : ∀ b : ↥Bs, ∃ t : Fin m → F, LineU.ActsDiagU φ (ggGamma X hN b) t)
    (h3m : 3 ∣ m) (hm2 : 2 ≤ m) {z : G} (hzB : z ∈ Bs)
    (hz3 : (⟨z, hzB⟩ : ↥Bs) ^ 3 = 1) (hz1 : z ≠ 1)
    (_hzC : z ∈ Subgroup.centralizer (X : Set G))
    (hcardBs : Nat.card ↥Bs ≤ 3 ^ (m - 1)) (i0 : Fin m)
    (hU : φ (hdRo7A3SMAux_dSU uF hu hM (hdRo7A3SMAux_gOne (m := m) h3m)) ≠ 1)
    (κ : ZMod 3) (hκ : κ ≠ 0)
    (hzκ : (⟨z, hzB⟩ : ↥Bs) = hdRo7A3SMAux_torB hN uF hu hp3 hBs hM hdiag
      (Multiplicative.ofAdd (κ • hdRo7A3SMAux_ones (m := m) h3m))) :
    A3Frame 3 m (hdRo7A3SMAux_theta hN uF hu hp3 hBs hM hdiag i0 κ hzB hz3)
      (Additive.ofMul (⟨z, hzB⟩ : ↥Bs)) := by
  have htop := hdRo7A3SMAux_range_eq_topU hN uF hu huord hp3 hBs hM hdiag h3m
    (by omega) hU hcardBs
  refine ⟨?_, ?_, Or.inl ⟨?_, ?_⟩⟩
  · intro v hv hzero
    rw [hdRo7A3SMAux_theta_apply_aug hN uF hu hp3 hBs hM hdiag i0 κ hzB hz3 hv] at hzero
    have h1 : hdRo7A3SMAux_torB hN uF hu hp3 hBs hM hdiag
        (Multiplicative.ofAdd (κ • (⟨v, hv⟩ : ↥(a3Aug 3 m)))) = 1 := by
      have := congrArg Additive.toMul hzero
      simpa using this
    have h2 : hdRo7A3SMAux_tor uF hu hM
        (Multiplicative.ofAdd (κ • (⟨v, hv⟩ : ↥(a3Aug 3 m)))) = 1 :=
      (hdRo7A3SMAux_torB_eq_one_iff hN uF hu hp3 hBs hM hdiag _).mp h1
    have h3 : Multiplicative.ofAdd (κ • (⟨v, hv⟩ : ↥(a3Aug 3 m))) = 1 :=
      (hdRo7A3SMAux_tor_eq_one_iff_one uF hu huord hM h3m (by omega) hU _).mp h2
    have h4 : κ • (⟨v, hv⟩ : ↥(a3Aug 3 m)) = 0 := by
      simpa using congrArg Multiplicative.toAdd h3
    have h5 : (⟨v, hv⟩ : ↥(a3Aug 3 m)) = 0 := by
      have h := congrArg (fun x => κ⁻¹ • x) h4
      rwa [smul_smul, inv_mul_cancel₀ hκ, one_smul, smul_zero] at h
    refine ⟨0, ?_⟩
    funext i
    have := congrArg (fun x : ↥(a3Aug 3 m) => (x : Fin m → ZMod 3) i) h5
    simpa using this
  · intro v
    have hv : Additive.toMul v ∈ (hdRo7A3SMAux_torB hN uF hu hp3 hBs hM hdiag).range := by
      rw [htop]
      exact Subgroup.mem_top _
    obtain ⟨w, hw⟩ := hv
    set xx : ↥(a3Aug 3 m) := Multiplicative.toAdd w with hxdef
    set x : Fin m → ZMod 3 := (xx : Fin m → ZMod 3) with hxdef'
    have hw2 : (Multiplicative.toAdd w).1 ∈ a3Aug 3 m := w.2
    rw [mem_a3Aug] at hw2
    have hxsum : (∑ i, x i) = 0 := by
      have h : (∑ i, (Multiplicative.toAdd w).1 i) = 0 := hw2
      simpa [xx, hxdef', hxdef] using h
    have hxmem : (κ⁻¹ • x) ∈ a3Aug 3 m := by
      rw [mem_a3Aug]
      simp only [Pi.smul_apply]
      rw [← Finset.smul_sum, hxsum, smul_zero]
    refine ⟨κ⁻¹ • x, hxmem, 0, ?_⟩
    rw [zero_smul, add_zero]
    rw [hdRo7A3SMAux_theta_apply_aug hN uF hu hp3 hBs hM hdiag i0 κ hzB hz3 hxmem]
    rw [← ofMul_toMul v, ← hw]
    have harg : w = Multiplicative.ofAdd
        (κ • (⟨κ⁻¹ • x, hxmem⟩ : ↥(a3Aug 3 m))) := by
      apply Multiplicative.toAdd.injective
      apply Subtype.ext
      funext i
      show x i = (κ • (κ⁻¹ • x)) i
      rw [Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul, ← mul_assoc,
        mul_inv_cancel₀ hκ, one_mul]
    rw [harg]
  · have hv1 : (fun _ => (1 : ZMod 3)) ∈ a3Aug 3 m :=
      (hdRo7A3SMAux_ones (m := m) h3m).2
    rw [hdRo7A3SMAux_theta_apply_aug hN uF hu hp3 hBs hM hdiag i0 κ hzB hz3 hv1]
    have hsub : (⟨fun _ => (1 : ZMod 3), hv1⟩ : ↥(a3Aug 3 m)) =
        hdRo7A3SMAux_ones (m := m) h3m := rfl
    rw [hsub, ← hzκ]
  · intro h
    have h1 : (⟨z, hzB⟩ : ↥Bs) = 1 := by
      have := congrArg Additive.toMul h
      simpa using this
    exact hz1 (by
      have h2 := congrArg (fun b : ↥Bs => (b : G)) h1
      simpa using h2)

private theorem hdRo7A3SMAux_frameM
    [Finite G]
    [IsMulCommutative ↥Bs] [Fact (∀ b : ↥Bs, b ^ 3 = 1)]
    (hN : Bs ≤ Subgroup.normalizer (X : Set G)) (uF : Fˣ) (hu : uF ^ 3 = 1)
    (huord : orderOf uF = 3) (hp3 : p = 3) (hBs : GGBstar p B Bs) (hM : UnitTB.Model φ)
    (hdiag : ∀ b : ↥Bs, ∃ t : Fin m → F, LineU.ActsDiagU φ (ggGamma X hN b) t)
    (h3m : 3 ∣ m) (hm2 : 2 ≤ m) {z : G} (hzB : z ∈ Bs)
    (hz3 : (⟨z, hzB⟩ : ↥Bs) ^ 3 = 1) (hz1 : z ≠ 1)
    (hzC : z ∈ Subgroup.centralizer (X : Set G))
    (hcardBs : Nat.card ↥Bs ≤ 3 ^ (m - 1)) (i0 : Fin m)
    (hMone : φ (hdRo7A3SMAux_dSU uF hu hM (hdRo7A3SMAux_gOne (m := m) h3m)) = 1) :
    A3Frame 3 m (hdRo7A3SMAux_theta hN uF hu hp3 hBs hM hdiag i0 1 hzB hz3)
      (Additive.ofMul (⟨z, hzB⟩ : ↥Bs)) := by
  have htorOne : hdRo7A3SMAux_tor uF hu hM (hdRo7A3SMAux_gOne (m := m) h3m) = 1 := by
    rw [hdRo7A3SMAux_tor_apply, hMone]
  refine ⟨?_, ?_, Or.inr ⟨?_, ?_⟩⟩
  · intro v hv hzero
    rw [hdRo7A3SMAux_theta_apply_aug hN uF hu hp3 hBs hM hdiag i0 1 hzB hz3 hv] at hzero
    rw [one_smul] at hzero
    have h1' : hdRo7A3SMAux_torB hN uF hu hp3 hBs hM hdiag
        (Multiplicative.ofAdd (⟨v, hv⟩ : ↥(a3Aug 3 m))) = 1 := by
      have := congrArg Additive.toMul hzero
      simpa using this
    have h2 : hdRo7A3SMAux_tor uF hu hM
        (Multiplicative.ofAdd (⟨v, hv⟩ : ↥(a3Aug 3 m))) = 1 :=
      (hdRo7A3SMAux_torB_eq_one_iff hN uF hu hp3 hBs hM hdiag _).mp h1'
    obtain ⟨c, hc⟩ :=
      (hdRo7A3SMAux_tor_eq_one_iff_const uF hu huord hM h3m (by omega) hMone _).mp h2
    exact ⟨c, by funext i; exact hc i⟩
  · intro v
    set b : ↥Bs := Additive.toMul v with hb
    obtain ⟨w, k, hk⟩ :=
      hdRo7A3SMAux_decompM hN uF hu huord hp3 hBs hM hdiag h3m hm2 hMone hzB hz1
        (hBs.2.1.2 z hzB) hzC hcardBs b
    set xv : ↥(a3Aug 3 m) := Multiplicative.toAdd w with hxv
    have hw_eq : (Multiplicative.ofAdd xv : Multiplicative ↥(a3Aug 3 m)) = w := by
      rw [hxv]
      rfl
    refine ⟨(xv : Fin m → ZMod 3), xv.2, (k : ZMod 3), ?_⟩
    change v = hdRo7A3SMAux_theta hN uF hu hp3 hBs hM hdiag i0 1 hzB hz3
      (xv : Fin m → ZMod 3) + (k : ZMod 3) • Additive.ofMul (⟨z, hzB⟩ : ↥Bs)
    rw [hdRo7A3SMAux_theta_apply_aug hN uF hu hp3 hBs hM hdiag i0 1 hzB hz3 xv.2]
    rw [show (⟨(xv : Fin m → ZMod 3), xv.2⟩ : ↥(a3Aug 3 m)) = xv from rfl, one_smul, hw_eq]
    rw [← ofMul_toMul v, ← hb, hk, ofMul_mul, ofMul_pow, Nat.cast_smul_eq_nsmul]
  · have hv1 : (fun _ => (1 : ZMod 3)) ∈ a3Aug 3 m :=
      (hdRo7A3SMAux_ones (m := m) h3m).2
    rw [hdRo7A3SMAux_theta_apply_aug hN uF hu hp3 hBs hM hdiag i0 1 hzB hz3 hv1]
    have hsub : (⟨fun _ => (1 : ZMod 3), hv1⟩ : ↥(a3Aug 3 m)) =
        hdRo7A3SMAux_ones (m := m) h3m := rfl
    rw [hsub, one_smul]
    have hg : Multiplicative.ofAdd (hdRo7A3SMAux_ones (m := m) h3m) =
        hdRo7A3SMAux_gOne (m := m) h3m := rfl
    rw [hg]
    have htorB1 : hdRo7A3SMAux_torB hN uF hu hp3 hBs hM hdiag
        (hdRo7A3SMAux_gOne (m := m) h3m) = 1 := by
      apply Subtype.ext
      rw [hdRo7A3SMAux_torB_coe, htorOne]
      rfl
    rw [htorB1]
    rfl
  · intro u hu_mem hzu
    rw [hdRo7A3SMAux_theta_apply_aug hN uF hu hp3 hBs hM hdiag i0 1 hzB hz3 hu_mem] at hzu
    rw [one_smul] at hzu
    have h1 : hdRo7A3SMAux_torB hN uF hu hp3 hBs hM hdiag
        (Multiplicative.ofAdd (⟨u, hu_mem⟩ : ↥(a3Aug 3 m))) = (⟨z, hzB⟩ : ↥Bs) := by
      have := congrArg Additive.toMul hzu
      simpa using this
    exact hdRo7A3SMAux_z_notMem_rangeM hN uF hu huord hp3 hBs hM hdiag h3m
      (by omega) hMone hzB hz1 hzC ⟨_, h1⟩

end Frame

section Automizer

variable {G : Type} [Group G] {p : ℕ} {B Bs X : Subgroup G}
  {F : Type} [Field F] {m : ℕ} {φ : ↥(unitarySU 2 1 F m) →* ↥X}
  {z : G}

private theorem hdRo7A3SMAux_range_elemAbelian
    (hN : Bs ≤ Subgroup.normalizer (X : Set G)) (hp3 : p = 3) (hBs : GGBstar p B Bs) :
    IsElemAbelian 3 (ggGamma X hN).range := by
  subst hp3
  have hcommBs : IsMulCommutative ↥Bs := hBs.2.1.1
  have hcommr : IsMulCommutative (ggGamma X hN).range := by
    rw [MonoidHom.range_eq_map]
    exact Subgroup.map_isMulCommutative (f := ggGamma X hN) (H := ⊤)
  refine ⟨hcommr, ?_⟩
  intro x hx
  obtain ⟨b, rfl⟩ := MonoidHom.mem_range.mp hx
  rw [← map_pow]
  have hb3 : b ^ 3 = 1 := by
    apply Subtype.ext
    simpa using hBs.2.1.2 (b : G) b.2
  rw [hb3, map_one]

private theorem hdRo7A3SMAux_range_diag
    (hN : Bs ≤ Subgroup.normalizer (X : Set G))
    (hdiag : ∀ b : ↥Bs, ∃ t : Fin m → F, LineU.ActsDiagU φ (ggGamma X hN b) t) :
    ∀ a ∈ (ggGamma X hN).range, ∃ t : Fin m → F, LineU.ActsDiagU φ a t := by
  rintro a ha
  obtain ⟨b, rfl⟩ := MonoidHom.mem_range.mp ha
  exact hdiag b

private theorem hdRo7A3SMAux_conj_eq_normalizerHom {s : G} (hsX : s ∈ X) :
    MulAut.conj (⟨s, hsX⟩ : ↥X) =
      X.normalizerMonoidHom ⟨s, Subgroup.le_normalizer hsX⟩ := by
  ext l
  rw [MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv,
    Subgroup.normalizerMonoidHom_apply_apply_coe]

private theorem hdRo7A3SMAux_conj_mem_normalizer
    (hN : Bs ≤ Subgroup.normalizer (X : Set G))
    {s : G} (hsX : s ∈ X) (hsN : s ∈ Subgroup.normalizer (Bs : Set G)) :
    MulAut.conj (⟨s, hsX⟩ : ↥X) ∈
      Subgroup.normalizer ((ggGamma X hN).range : Set (MulAut ↥X)) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · rintro ⟨b, rfl⟩
    have hgb : s * (b : G) * s⁻¹ ∈ Bs := (Subgroup.mem_normalizer_iff.mp hsN (b : G)).mp b.2
    refine ⟨⟨s * (b : G) * s⁻¹, hgb⟩, ?_⟩
    rw [hdRo7A3SMAux_conj_eq_normalizerHom hsX,
      ggGamma_conj_normalizer X hN ⟨s, Subgroup.le_normalizer hsX⟩ b hgb]
  · rintro ⟨b, hb⟩
    have hs'invN : s⁻¹ ∈ Subgroup.normalizer (Bs : Set G) := Subgroup.inv_mem _ hsN
    have hgb' : s⁻¹ * (b : G) * (s⁻¹)⁻¹ ∈ Bs :=
      (Subgroup.mem_normalizer_iff.mp hs'invN (b : G)).mp b.2
    refine ⟨⟨s⁻¹ * (b : G) * (s⁻¹)⁻¹, hgb'⟩, ?_⟩
    have hsinv : MulAut.conj (⟨s⁻¹, X.inv_mem hsX⟩ : ↥X) =
        (MulAut.conj (⟨s, hsX⟩ : ↥X))⁻¹ := by
      ext l
      rw [MulAut.conj_apply, MulAut.conj_inv_apply]
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      group
    have hconj' : MulAut.conj (⟨s⁻¹, X.inv_mem hsX⟩ : ↥X) * ggGamma X hN b *
        (MulAut.conj (⟨s⁻¹, X.inv_mem hsX⟩ : ↥X))⁻¹ =
        ggGamma X hN ⟨s⁻¹ * (b : G) * (s⁻¹)⁻¹, hgb'⟩ := by
      rw [hdRo7A3SMAux_conj_eq_normalizerHom (X.inv_mem hsX),
        ggGamma_conj_normalizer X hN ⟨s⁻¹, Subgroup.le_normalizer (X.inv_mem hsX)⟩ b hgb']
    rw [← hconj']
    calc MulAut.conj (⟨s⁻¹, X.inv_mem hsX⟩ : ↥X) * ggGamma X hN b *
          (MulAut.conj (⟨s⁻¹, X.inv_mem hsX⟩ : ↥X))⁻¹
        = (MulAut.conj (⟨s, hsX⟩ : ↥X))⁻¹ *
          (MulAut.conj (⟨s, hsX⟩ : ↥X) * x * (MulAut.conj (⟨s, hsX⟩ : ↥X))⁻¹) *
          MulAut.conj (⟨s, hsX⟩ : ↥X) := by rw [hsinv, hb]; group
      _ = x := by group

private theorem hdRo7A3SMAux_conj_tor
    (hM : UnitTB.Model φ) (uF : Fˣ) (hu : uF ^ 3 = 1)
    (gU : ↥(unitarySU 2 1 F m)) (π : Equiv.Perm (Fin m))
    (x : Multiplicative ↥(a3Aug 3 m))
    (hperm : ((gU : GL (Fin m) F) : Matrix (Fin m) (Fin m) F) *
        Matrix.diagonal (fun i => ((hdRo7A3SMAux_dvec (m := m) uF hu x i : Fˣ) : F)) =
      Matrix.diagonal ((fun i => ((hdRo7A3SMAux_dvec (m := m) uF hu x i : Fˣ) : F)) ∘ π) *
        ((gU : GL (Fin m) F) : Matrix (Fin m) (Fin m) F)) :
    φ gU * hdRo7A3SMAux_tor uF hu hM x * (φ gU)⁻¹ =
      hdRo7A3SMAux_tor uF hu hM
        (Multiplicative.ofAdd (⟨fun i => (Multiplicative.toAdd x).1 (π i),
          a3Aug_perm (Multiplicative.toAdd x).2 π⟩ : ↥(a3Aug 3 m))) := by
  classical
  set v : Fin m → F := fun i => ((hdRo7A3SMAux_dvec (m := m) uF hu x i : Fˣ) : F) with hv
  set w : Fin m → F := v ∘ π with hw
  have hwpow : ∀ i, w i ^ 3 = 1 := by
    intro i
    have h := hdRo7A3SMAux_dvec_pow uF hu x (π i)
    have h2 : w i = ((hdRo7A3SMAux_dvec uF hu x (π i) : Fˣ) : F) := rfl
    rw [h2, ← Units.val_pow_eq_pow_val, h, Units.val_one]
  have hwprod : ∏ i, w i = 1 := by
    have h : ∏ i, w i = ((∏ i, hdRo7A3SMAux_dvec (m := m) uF hu x i : Fˣ) : F) := by
      show (∏ i, v (π i)) = _
      rw [Equiv.prod_comp]
      rw [hv, Units.coe_prod]
    rw [h, hdRo7A3SMAux_dvec_prod, Units.val_one]
  obtain ⟨D', hD'⟩ := UnitTB.exists_diagSU (n := 1) (d := m) (p := 3) hM.field (by norm_num)
    hwpow hwprod
  have hpermu : ((gU : GL (Fin m) F) : Matrix (Fin m) (Fin m) F) * Matrix.diagonal v =
      Matrix.diagonal w * ((gU : GL (Fin m) F) : Matrix (Fin m) (Fin m) F) := hperm
  have hDv : ((hdRo7A3SMAux_dSU uF hu hM x : GL (Fin m) F) : Matrix (Fin m) (Fin m) F) =
      Matrix.diagonal v := rfl
  have hGL : (gU : GL (Fin m) F) * (hdRo7A3SMAux_dSU uF hu hM x : GL (Fin m) F) *
      (gU : GL (Fin m) F)⁻¹ = (D' : GL (Fin m) F) := by
    have key : (gU : GL (Fin m) F) * (hdRo7A3SMAux_dSU uF hu hM x : GL (Fin m) F) =
        (D' : GL (Fin m) F) * (gU : GL (Fin m) F) := by
      apply Units.ext
      rw [Units.val_mul, Units.val_mul, hDv, hD']
      exact hpermu
    rw [key, mul_assoc, mul_inv_cancel, mul_one]
  have hSU : (gU * hdRo7A3SMAux_dSU uF hu hM x * gU⁻¹ : ↥(unitarySU 2 1 F m)) = D' := by
    apply Subtype.ext
    exact hGL
  have hDSU : hdRo7A3SMAux_dSU uF hu hM
      (Multiplicative.ofAdd (⟨fun i => (Multiplicative.toAdd x).1 (π i),
        a3Aug_perm (Multiplicative.toAdd x).2 π⟩ : ↥(a3Aug 3 m))) = D' := by
    apply Subtype.ext
    apply Units.ext
    rw [hD']
    rfl
  have hφeq : φ gU * hdRo7A3SMAux_tor uF hu hM x * (φ gU)⁻¹ = φ D' := by
    have h := congrArg φ hSU
    rwa [map_mul, map_mul, map_inv] at h
  have htor : hdRo7A3SMAux_tor uF hu hM
      (Multiplicative.ofAdd (⟨fun i => (Multiplicative.toAdd x).1 (π i),
        a3Aug_perm (Multiplicative.toAdd x).2 π⟩ : ↥(a3Aug 3 m))) = φ D' := by
    show φ (hdRo7A3SMAux_dSU uF hu hM _) = φ D'
    rw [hDSU]
  rw [htor]
  exact hφeq

private theorem hdRo7A3SMAux_conj_torB_val
    (hN : Bs ≤ Subgroup.normalizer (X : Set G)) (uF : Fˣ) (hu : uF ^ 3 = 1)
    (hp3 : p = 3) (hBs : GGBstar p B Bs) (hM : UnitTB.Model φ)
    (hdiag : ∀ b : ↥Bs, ∃ t : Fin m → F, LineU.ActsDiagU φ (ggGamma X hN b) t)
    (gU : ↥(unitarySU 2 1 F m)) (π : Equiv.Perm (Fin m))
    (x : Multiplicative ↥(a3Aug 3 m))
    (hperm : ((gU : GL (Fin m) F) : Matrix (Fin m) (Fin m) F) *
        Matrix.diagonal (fun i => ((hdRo7A3SMAux_dvec (m := m) uF hu x i : Fˣ) : F)) =
      Matrix.diagonal ((fun i => ((hdRo7A3SMAux_dvec (m := m) uF hu x i : Fˣ) : F)) ∘ π) *
        ((gU : GL (Fin m) F) : Matrix (Fin m) (Fin m) F)) :
    ((φ gU : ↥X) : G) * ((hdRo7A3SMAux_torB hN uF hu hp3 hBs hM hdiag x : ↥Bs) : G) *
        ((φ gU : ↥X) : G)⁻¹ =
      ((hdRo7A3SMAux_torB hN uF hu hp3 hBs hM hdiag
        (Multiplicative.ofAdd (⟨fun i => (Multiplicative.toAdd x).1 (π i),
          a3Aug_perm (Multiplicative.toAdd x).2 π⟩ : ↥(a3Aug 3 m))) : ↥Bs) : G) := by
  rw [hdRo7A3SMAux_torB_coe, hdRo7A3SMAux_torB_coe]
  have h := hdRo7A3SMAux_conj_tor hM uF hu gU π x hperm
  calc ((φ gU : ↥X) : G) * ((hdRo7A3SMAux_tor uF hu hM x : ↥X) : G) * ((φ gU : ↥X) : G)⁻¹
      = ((φ gU * hdRo7A3SMAux_tor uF hu hM x * (φ gU)⁻¹ : ↥X) : G) := by
        simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    _ = ((hdRo7A3SMAux_tor uF hu hM _ : ↥X) : G) := by rw [h]

private theorem hdRo7A3SMAux_conjAut_torB
    (hN : Bs ≤ Subgroup.normalizer (X : Set G)) (uF : Fˣ) (hu : uF ^ 3 = 1)
    (hp3 : p = 3) (hBs : GGBstar p B Bs) (hM : UnitTB.Model φ)
    (hdiag : ∀ b : ↥Bs, ∃ t : Fin m → F, LineU.ActsDiagU φ (ggGamma X hN b) t)
    (φaut : MulAut ↥Bs) (gU : ↥(unitarySU 2 1 F m)) (π : Equiv.Perm (Fin m))
    (hconj : ∀ b : ↥Bs, ((φaut b : ↥Bs) : G) =
      ((φ gU : ↥X) : G) * (b : G) * ((φ gU : ↥X) : G)⁻¹)
    (x : Multiplicative ↥(a3Aug 3 m))
    (hperm : ((gU : GL (Fin m) F) : Matrix (Fin m) (Fin m) F) *
        Matrix.diagonal (fun i => ((hdRo7A3SMAux_dvec (m := m) uF hu x i : Fˣ) : F)) =
      Matrix.diagonal ((fun i => ((hdRo7A3SMAux_dvec (m := m) uF hu x i : Fˣ) : F)) ∘ π) *
        ((gU : GL (Fin m) F) : Matrix (Fin m) (Fin m) F)) :
    φaut (hdRo7A3SMAux_torB hN uF hu hp3 hBs hM hdiag x) =
      hdRo7A3SMAux_torB hN uF hu hp3 hBs hM hdiag
        (Multiplicative.ofAdd (⟨fun i => (Multiplicative.toAdd x).1 (π i),
          a3Aug_perm (Multiplicative.toAdd x).2 π⟩ : ↥(a3Aug 3 m))) := by
  apply Subtype.ext
  rw [hconj]
  exact hdRo7A3SMAux_conj_torB_val hN uF hu hp3 hBs hM hdiag gU π x hperm

private theorem hdRo7A3SMAux_a3P_of_perm
    [IsMulCommutative ↥Bs] [Fact (∀ b : ↥Bs, b ^ 3 = 1)]
    (hN : Bs ≤ Subgroup.normalizer (X : Set G)) (uF : Fˣ) (hu : uF ^ 3 = 1)
    (hp3 : p = 3) (hBs : GGBstar p B Bs) (hM : UnitTB.Model φ)
    (hdiag : ∀ b : ↥Bs, ∃ t : Fin m → F, LineU.ActsDiagU φ (ggGamma X hN b) t)
    (i0 : Fin m) (κ : ZMod 3) {z : G} (hzB : z ∈ Bs)
    (hz3 : (⟨z, hzB⟩ : ↥Bs) ^ 3 = 1)
    (φaut : MulAut ↥Bs) (gU : ↥(unitarySU 2 1 F m)) (π : Equiv.Perm (Fin m))
    (hconj : ∀ b : ↥Bs, ((φaut b : ↥Bs) : G) =
      ((φ gU : ↥X) : G) * (b : G) * ((φ gU : ↥X) : G)⁻¹)
    (hperm : ∀ u : Fin m → F,
      ((gU : GL (Fin m) F) : Matrix (Fin m) (Fin m) F) * Matrix.diagonal u =
        Matrix.diagonal (u ∘ π) * ((gU : GL (Fin m) F) : Matrix (Fin m) (Fin m) F))
    (hzfix : ((φ gU : ↥X) : G) * z * ((φ gU : ↥X) : G)⁻¹ = z) :
    A3P 3 m (hdRo7A3SMAux_theta hN uF hu hp3 hBs hM hdiag i0 κ hzB hz3)
      (Additive.ofMul (⟨z, hzB⟩ : ↥Bs))
      (ggLin (p := 3) (AddEquiv.refl (Additive ↥Bs)) φaut) := by
  classical
  have hzBfix : φaut (⟨z, hzB⟩ : ↥Bs) = ⟨z, hzB⟩ := by
    apply Subtype.ext
    rw [hconj]
    exact hzfix
  refine ⟨π⁻¹, ?_, ?_⟩
  · intro u huaug
    have htor := hdRo7A3SMAux_conjAut_torB hN uF hu hp3 hBs hM hdiag φaut gU π hconj
      (x := Multiplicative.ofAdd (κ • (⟨u, huaug⟩ : ↥(a3Aug 3 m)))) (hperm _)
    rw [hdRo7A3SMAux_theta_apply_aug hN uF hu hp3 hBs hM hdiag i0 κ hzB hz3 huaug]
    change Additive.ofMul (φaut (hdRo7A3SMAux_torB hN uF hu hp3 hBs hM hdiag
        (Multiplicative.ofAdd (κ • (⟨u, huaug⟩ : ↥(a3Aug 3 m)))))) =
      (hdRo7A3SMAux_theta hN uF hu hp3 hBs hM hdiag i0 κ hzB hz3) (fun i => u ((π⁻¹).symm i))
    rw [htor]
    rw [show (fun i => u ((π⁻¹).symm i)) = (fun i => u (π i)) from rfl]
    rw [hdRo7A3SMAux_theta_apply_aug hN uF hu hp3 hBs hM hdiag i0 κ hzB hz3
      (a3Aug_perm huaug π)]
    rfl
  · change Additive.ofMul (φaut (⟨z, hzB⟩ : ↥Bs)) = Additive.ofMul (⟨z, hzB⟩ : ↥Bs)
    rw [hzBfix]

private theorem hdRo7A3SMAux_permSU_perm
    (hM : UnitTB.Model φ) (uF : Fˣ) (hu : uF ^ 3 = 1) (σ : Equiv.Perm (Fin m))
    (x : Multiplicative ↥(a3Aug 3 m)) :
    ((LineU.permSU hM.field σ : GL (Fin m) F) : Matrix (Fin m) (Fin m) F) *
        Matrix.diagonal (fun i => ((hdRo7A3SMAux_dvec (m := m) uF hu x i : Fˣ) : F)) =
      Matrix.diagonal
          ((fun i => ((hdRo7A3SMAux_dvec (m := m) uF hu x i : Fˣ) : F)) ∘ σ.symm) *
        ((LineU.permSU hM.field σ : GL (Fin m) F) : Matrix (Fin m) (Fin m) F) := by
  set v : Fin m → F := fun i => ((hdRo7A3SMAux_dvec (m := m) uF hu x i : Fˣ) : F) with hv
  have hD : ((hdRo7A3SMAux_dSU uF hu hM x : GL (Fin m) F) : Matrix (Fin m) (Fin m) F) =
      Matrix.diagonal v := rfl
  have hvw : ∀ i, (v ∘ σ.symm) i ^ 3 = 1 := by
    intro i
    have h := hdRo7A3SMAux_dvec_pow uF hu x (σ.symm i)
    have h2 : (v ∘ σ.symm) i = ((hdRo7A3SMAux_dvec uF hu x (σ.symm i) : Fˣ) : F) := rfl
    rw [h2, ← Units.val_pow_eq_pow_val, h, Units.val_one]
  have hprod : ∏ i, (v ∘ σ.symm) i = 1 := by
    have h1 : (∏ i, v (σ.symm i)) = ∏ i, v i := Equiv.prod_comp σ.symm v
    have h2 : (∏ i, v i) = ((∏ i, hdRo7A3SMAux_dvec (m := m) uF hu x i : Fˣ) : F) := by
      rw [Units.coe_prod]
    have h3 : (∏ i, hdRo7A3SMAux_dvec (m := m) uF hu x i : Fˣ) = 1 :=
      hdRo7A3SMAux_dvec_prod uF hu x
    calc (∏ i, (v ∘ σ.symm) i) = ∏ i, v (σ.symm i) := rfl
      _ = ∏ i, v i := h1
      _ = ((∏ i, hdRo7A3SMAux_dvec (m := m) uF hu x i : Fˣ) : F) := h2
      _ = 1 := by rw [h3, Units.val_one]
  obtain ⟨D', hD'⟩ := UnitTB.exists_diagSU (n := 1) (d := m) (p := 3) hM.field (by norm_num)
    hvw hprod
  have hSU : (LineU.permSU hM.field σ * hdRo7A3SMAux_dSU uF hu hM x *
      (LineU.permSU hM.field σ)⁻¹ : ↥(unitarySU 2 1 F m)) = D' := by
    apply Subtype.ext
    apply Units.ext
    rw [hD']
    exact UnitAct.coe_permSU_conj hM.field hD σ
  have hGL : (LineU.permSU hM.field σ : GL (Fin m) F) *
      (hdRo7A3SMAux_dSU uF hu hM x : GL (Fin m) F) *
      (LineU.permSU hM.field σ : GL (Fin m) F)⁻¹ = (D' : GL (Fin m) F) :=
    congrArg (fun u : ↥(unitarySU 2 1 F m) => (u : GL (Fin m) F)) hSU
  have key : (LineU.permSU hM.field σ : GL (Fin m) F) *
      (hdRo7A3SMAux_dSU uF hu hM x : GL (Fin m) F) =
      (D' : GL (Fin m) F) * (LineU.permSU hM.field σ : GL (Fin m) F) := by
    calc (LineU.permSU hM.field σ : GL (Fin m) F) *
          (hdRo7A3SMAux_dSU uF hu hM x : GL (Fin m) F)
        = ((LineU.permSU hM.field σ : GL (Fin m) F) *
            (hdRo7A3SMAux_dSU uF hu hM x : GL (Fin m) F) *
            (LineU.permSU hM.field σ : GL (Fin m) F)⁻¹) *
            (LineU.permSU hM.field σ : GL (Fin m) F) := by group
      _ = (D' : GL (Fin m) F) * (LineU.permSU hM.field σ : GL (Fin m) F) := by rw [hGL]
  have keym := congrArg (fun u : GL (Fin m) F => (u : Matrix (Fin m) (Fin m) F)) key
  simpa only [Units.val_mul, hD, hD'] using keym

private theorem hdRo7A3SMAux_conj_mem_Bs_of_dec
    (hN : Bs ≤ Subgroup.normalizer (X : Set G)) (uF : Fˣ) (hu : uF ^ 3 = 1)
    (hp3 : p = 3) (hBs : GGBstar p B Bs) (hM : UnitTB.Model φ)
    (hdiag : ∀ b : ↥Bs, ∃ t : Fin m → F, LineU.ActsDiagU φ (ggGamma X hN b) t)
    {z : G} (hzB : z ∈ Bs)
    (hdec : ∀ b : ↥Bs, ∃ (w : Multiplicative ↥(a3Aug 3 m)) (k : ℕ),
      b = hdRo7A3SMAux_torB hN uF hu hp3 hBs hM hdiag w * (⟨z, hzB⟩ : ↥Bs) ^ k)
    (gU : ↥(unitarySU 2 1 F m)) (π : Equiv.Perm (Fin m))
    (hperm : ∀ x : Multiplicative ↥(a3Aug 3 m),
      ((gU : GL (Fin m) F) : Matrix (Fin m) (Fin m) F) *
        Matrix.diagonal (fun i => ((hdRo7A3SMAux_dvec (m := m) uF hu x i : Fˣ) : F)) =
      Matrix.diagonal ((fun i => ((hdRo7A3SMAux_dvec (m := m) uF hu x i : Fˣ) : F)) ∘ π) *
        ((gU : GL (Fin m) F) : Matrix (Fin m) (Fin m) F))
    (hzfix : ((φ gU : ↥X) : G) * z * ((φ gU : ↥X) : G)⁻¹ = z) :
    ∀ b : ↥Bs, ((φ gU : ↥X) : G) * (b : G) * ((φ gU : ↥X) : G)⁻¹ ∈ Bs := by
  intro b
  obtain ⟨w, k, hw⟩ := hdec b
  have hzpow : ((φ gU : ↥X) : G) * (((⟨z, hzB⟩ : ↥Bs) : G) ^ k) *
      ((φ gU : ↥X) : G)⁻¹ = ((⟨z, hzB⟩ : ↥Bs) : G) ^ k := by
    have h := map_pow (MulAut.conj ((φ gU : ↥X) : G)) ((⟨z, hzB⟩ : ↥Bs) : G) k
    rw [MulAut.conj_apply] at h
    have h2 : (MulAut.conj ((φ gU : ↥X) : G)) ((⟨z, hzB⟩ : ↥Bs) : G) = ((⟨z, hzB⟩ : ↥Bs) : G) := by
      rw [MulAut.conj_apply]
      exact hzfix
    rw [h2] at h
    exact h
  have htor := hdRo7A3SMAux_conj_torB_val hN uF hu hp3 hBs hM hdiag gU π w (hperm w)
  rw [hw, Subgroup.coe_mul, Subgroup.coe_pow]
  have heq : ((φ gU : ↥X) : G) *
        (((hdRo7A3SMAux_torB hN uF hu hp3 hBs hM hdiag w : ↥Bs) : G) *
          ((⟨z, hzB⟩ : ↥Bs) : G) ^ k) * ((φ gU : ↥X) : G)⁻¹ =
      ((hdRo7A3SMAux_torB hN uF hu hp3 hBs hM hdiag
          (Multiplicative.ofAdd (⟨fun i => (Multiplicative.toAdd w).1 (π i),
            a3Aug_perm (Multiplicative.toAdd w).2 π⟩ : ↥(a3Aug 3 m))) *
        (⟨z, hzB⟩ : ↥Bs) ^ k : ↥Bs) : G) := by
    rw [Subgroup.coe_mul, Subgroup.coe_pow]
    calc ((φ gU : ↥X) : G) *
          (((hdRo7A3SMAux_torB hN uF hu hp3 hBs hM hdiag w : ↥Bs) : G) *
            ((⟨z, hzB⟩ : ↥Bs) : G) ^ k) * ((φ gU : ↥X) : G)⁻¹
        = (((φ gU : ↥X) : G) * ((hdRo7A3SMAux_torB hN uF hu hp3 hBs hM hdiag w : ↥Bs) : G) *
            ((φ gU : ↥X) : G)⁻¹) *
          (((φ gU : ↥X) : G) * ((⟨z, hzB⟩ : ↥Bs) : G) ^ k * ((φ gU : ↥X) : G)⁻¹) := by
            group
      _ = ((hdRo7A3SMAux_torB hN uF hu hp3 hBs hM hdiag
            (Multiplicative.ofAdd (⟨fun i => (Multiplicative.toAdd w).1 (π i),
              a3Aug_perm (Multiplicative.toAdd w).2 π⟩ : ↥(a3Aug 3 m))) : ↥Bs) : G) *
          ((⟨z, hzB⟩ : ↥Bs) : G) ^ k := by rw [htor, hzpow]
      _ = ((hdRo7A3SMAux_torB hN uF hu hp3 hBs hM hdiag
            (Multiplicative.ofAdd (⟨fun i => (Multiplicative.toAdd w).1 (π i),
              a3Aug_perm (Multiplicative.toAdd w).2 π⟩ : ↥(a3Aug 3 m))) *
            (⟨z, hzB⟩ : ↥Bs) ^ k : ↥Bs) : G) := by rw [Subgroup.coe_mul, Subgroup.coe_pow]
  rw [heq]
  exact Subgroup.mul_mem _ (hdRo7A3SMAux_torB hN uF hu hp3 hBs hM hdiag _).2
    (Subgroup.pow_mem _ (⟨z, hzB⟩ : ↥Bs).2 k)

private theorem hdRo7A3SMAux_mem_normalizer_of_conj {s : G}
    (h1 : ∀ b : ↥Bs, s * (b : G) * s⁻¹ ∈ Bs)
    (h2 : ∀ b : ↥Bs, s⁻¹ * (b : G) * s ∈ Bs) :
    s ∈ Subgroup.normalizer (Bs : Set G) := by
  rw [Subgroup.mem_normalizer_iff'']
  intro h
  constructor
  · intro hmem
    exact h2 ⟨h, hmem⟩
  · intro hmem
    have h3 := h1 ⟨s⁻¹ * h * s, hmem⟩
    have heq : s * (s⁻¹ * h * s) * s⁻¹ = h := by group
    rwa [heq] at h3

private theorem hdRo7A3SMAux_mem_map_of_a3P
    [IsMulCommutative ↥Bs] [Fact (∀ b : ↥Bs, b ^ 3 = 1)]
    (hN : Bs ≤ Subgroup.normalizer (X : Set G)) (uF : Fˣ) (hu : uF ^ 3 = 1)
    (hp3 : p = 3) (hBs : GGBstar p B Bs) (hM : UnitTB.Model φ)
    (hdiag : ∀ b : ↥Bs, ∃ t : Fin m → F, LineU.ActsDiagU φ (ggGamma X hN b) t)
    (i0 : Fin m) (κ : ZMod 3) {z : G} (hzB : z ∈ Bs)
    (hz3 : (⟨z, hzB⟩ : ↥Bs) ^ 3 = 1)
    (hzC : z ∈ Subgroup.centralizer (X : Set G))
    (hdec : ∀ b : ↥Bs, ∃ (w : Multiplicative ↥(a3Aug 3 m)) (k : ℕ),
      b = hdRo7A3SMAux_torB hN uF hu hp3 hBs hM hdiag w * (⟨z, hzB⟩ : ↥Bs) ^ k)
    (hfr : A3Frame 3 m (hdRo7A3SMAux_theta hN uF hu hp3 hBs hM hdiag i0 κ hzB hz3)
      (Additive.ofMul (⟨z, hzB⟩ : ↥Bs)))
    {g : Additive ↥Bs ≃ₗ[ZMod 3] Additive ↥Bs}
    (hg : A3P 3 m (hdRo7A3SMAux_theta hN uF hu hp3 hBs hM hdiag i0 κ hzB hz3)
      (Additive.ofMul (⟨z, hzB⟩ : ↥Bs)) g) :
    g ∈ (ggAutomizer X Bs).map (ggLin (p := 3) (AddEquiv.refl (Additive ↥Bs))) := by
  classical
  obtain ⟨σ, hσu, hσz⟩ := hg
  have hzfix_s : ((φ (LineU.permSU hM.field σ) : ↥X) : G) * z *
      ((φ (LineU.permSU hM.field σ) : ↥X) : G)⁻¹ = z := by
    have h := (Subgroup.mem_centralizer_iff.mp hzC) _ (φ (LineU.permSU hM.field σ)).2
    calc ((φ (LineU.permSU hM.field σ) : ↥X) : G) * z *
          ((φ (LineU.permSU hM.field σ) : ↥X) : G)⁻¹
        = z * ((φ (LineU.permSU hM.field σ) : ↥X) : G) *
          ((φ (LineU.permSU hM.field σ) : ↥X) : G)⁻¹ := by rw [h]
      _ = z := by group
  have hzfix_sinv : ((φ (LineU.permSU hM.field σ.symm) : ↥X) : G) * z *
      ((φ (LineU.permSU hM.field σ.symm) : ↥X) : G)⁻¹ = z := by
    have h := (Subgroup.mem_centralizer_iff.mp hzC) _ (φ (LineU.permSU hM.field σ.symm)).2
    calc ((φ (LineU.permSU hM.field σ.symm) : ↥X) : G) * z *
          ((φ (LineU.permSU hM.field σ.symm) : ↥X) : G)⁻¹
        = z * ((φ (LineU.permSU hM.field σ.symm) : ↥X) : G) *
          ((φ (LineU.permSU hM.field σ.symm) : ↥X) : G)⁻¹ := by rw [h]
      _ = z := by group
  have hperm_s : ∀ x : Multiplicative ↥(a3Aug 3 m),
      ((LineU.permSU hM.field σ : GL (Fin m) F) : Matrix (Fin m) (Fin m) F) *
        Matrix.diagonal (fun i => ((hdRo7A3SMAux_dvec (m := m) uF hu x i : Fˣ) : F)) =
      Matrix.diagonal ((fun i => ((hdRo7A3SMAux_dvec (m := m) uF hu x i : Fˣ) : F)) ∘ σ.symm) *
        ((LineU.permSU hM.field σ : GL (Fin m) F) : Matrix (Fin m) (Fin m) F) :=
    fun x => hdRo7A3SMAux_permSU_perm hM uF hu σ x
  have hperm_sinv : ∀ x : Multiplicative ↥(a3Aug 3 m),
      ((LineU.permSU hM.field σ.symm : GL (Fin m) F) : Matrix (Fin m) (Fin m) F) *
        Matrix.diagonal (fun i => ((hdRo7A3SMAux_dvec (m := m) uF hu x i : Fˣ) : F)) =
      Matrix.diagonal ((fun i => ((hdRo7A3SMAux_dvec (m := m) uF hu x i : Fˣ) : F)) ∘ σ) *
        ((LineU.permSU hM.field σ.symm : GL (Fin m) F) : Matrix (Fin m) (Fin m) F) :=
    fun x => hdRo7A3SMAux_permSU_perm hM uF hu σ.symm x
  have hmem_s := hdRo7A3SMAux_conj_mem_Bs_of_dec hN uF hu hp3 hBs hM hdiag hzB hdec
    (LineU.permSU hM.field σ) σ.symm hperm_s hzfix_s
  have hmem_sinv := hdRo7A3SMAux_conj_mem_Bs_of_dec hN uF hu hp3 hBs hM hdiag hzB hdec
    (LineU.permSU hM.field σ.symm) σ hperm_sinv hzfix_sinv
  have hs_inv : ((φ (LineU.permSU hM.field σ) : ↥X) : G)⁻¹ =
      ((φ (LineU.permSU hM.field σ.symm) : ↥X) : G) := by
    have h1 : (φ (LineU.permSU hM.field σ))⁻¹ = φ (LineU.permSU hM.field σ.symm) := by
      refine inv_eq_of_mul_eq_one_right ?_
      rw [← map_mul]
      have h2 : LineU.permSU hM.field σ * LineU.permSU hM.field σ.symm = 1 := by
        rw [← UnitAct.permSU_mul]
        have h3 : σ * σ.symm = 1 := by
          ext i
          simp
        rw [h3, UnitAct.permSU_one]
      rw [h2, map_one]
    exact congrArg (fun u : ↥X => (u : G)) h1
  have hmem_sinv' : ∀ b : ↥Bs, ((φ (LineU.permSU hM.field σ) : ↥X) : G)⁻¹ * (b : G) *
      ((φ (LineU.permSU hM.field σ) : ↥X) : G) ∈ Bs := by
    intro b
    have h2 : ((φ (LineU.permSU hM.field σ) : ↥X) : G)⁻¹ =
        ((φ (LineU.permSU hM.field σ.symm) : ↥X) : G) := hs_inv
    have h3 : ((φ (LineU.permSU hM.field σ) : ↥X) : G) =
        ((φ (LineU.permSU hM.field σ.symm) : ↥X) : G)⁻¹ :=
      calc ((φ (LineU.permSU hM.field σ) : ↥X) : G)
          = (((φ (LineU.permSU hM.field σ) : ↥X) : G)⁻¹)⁻¹ := (inv_inv _).symm
        _ = ((φ (LineU.permSU hM.field σ.symm) : ↥X) : G)⁻¹ := by rw [h2]
    rw [h2, h3]
    exact hmem_sinv b
  have hsN : ((φ (LineU.permSU hM.field σ) : ↥X) : G) ∈
      Subgroup.normalizer (Bs : Set G) :=
    hdRo7A3SMAux_mem_normalizer_of_conj hmem_s hmem_sinv'
  have hsX : ((φ (LineU.permSU hM.field σ) : ↥X) : G) ∈ X :=
    (φ (LineU.permSU hM.field σ)).2
  refine Subgroup.mem_map.mpr ⟨ggConjAut Bs hsN, ggConjAut_mem_ggAutomizer hsX hsN, ?_⟩
  apply LinearEquiv.ext
  intro v
  obtain ⟨u, huaug, c, rfl⟩ := hfr.2.1 v
  rw [map_add, map_smul, map_add, map_smul]
  congr 1
  · rw [hσu u huaug]
    have hconj : ∀ b : ↥Bs, ((ggConjAut Bs hsN b : ↥Bs) : G) =
        ((φ (LineU.permSU hM.field σ) : ↥X) : G) * (b : G) *
          ((φ (LineU.permSU hM.field σ) : ↥X) : G)⁻¹ :=
      fun b => ggConjAut_apply Bs hsN b
    have htor := hdRo7A3SMAux_conjAut_torB hN uF hu hp3 hBs hM hdiag (ggConjAut Bs hsN)
      (LineU.permSU hM.field σ) σ.symm hconj
      (x := Multiplicative.ofAdd (κ • (⟨u, huaug⟩ : ↥(a3Aug 3 m)))) (hperm_s _)
    rw [hdRo7A3SMAux_theta_apply_aug hN uF hu hp3 hBs hM hdiag i0 κ hzB hz3 huaug]
    change Additive.ofMul ((ggConjAut Bs hsN)
        (hdRo7A3SMAux_torB hN uF hu hp3 hBs hM hdiag
          (Multiplicative.ofAdd (κ • (⟨u, huaug⟩ : ↥(a3Aug 3 m)))))) =
      (hdRo7A3SMAux_theta hN uF hu hp3 hBs hM hdiag i0 κ hzB hz3) (fun i => u (σ.symm i))
    rw [htor, hdRo7A3SMAux_theta_apply_aug hN uF hu hp3 hBs hM hdiag i0 κ hzB hz3
      (a3Aug_perm huaug σ.symm)]
    rfl
  · rw [hσz]
    congr 1
    have hzBfix : (ggConjAut Bs hsN) (⟨z, hzB⟩ : ↥Bs) = ⟨z, hzB⟩ := by
      apply Subtype.ext
      rw [ggConjAut_apply]
      exact hzfix_s
    change Additive.ofMul ((ggConjAut Bs hsN) (⟨z, hzB⟩ : ↥Bs)) =
      Additive.ofMul (⟨z, hzB⟩ : ↥Bs)
    rw [hzBfix]

private theorem hdRo7A3SMAux_gOne_pow_three (h3m : 3 ∣ m) :
    hdRo7A3SMAux_gOne (m := m) h3m ^ 3 = 1 := by
  apply Multiplicative.toAdd.injective
  have h : hdRo7A3SMAux_gOne (m := m) h3m ^ 3 =
      Multiplicative.ofAdd ((3 : ℕ) • hdRo7A3SMAux_ones (m := m) h3m) := ofAdd_nsmul 3 _
  rw [h]
  apply Subtype.ext
  funext i
  show ((3 : ℕ) • ((hdRo7A3SMAux_ones (m := m) h3m : ↥(a3Aug 3 m)) :
    Fin m → ZMod 3)) i = 0
  rw [Pi.smul_apply, hdRo7A3SMAux_ones_val, nsmul_eq_mul, mul_one]
  exact ZMod.natCast_self 3

private theorem hdRo7A3SMAux_zpowers_U
    [Finite G]
    [IsMulCommutative ↥Bs] [Fact (∀ b : ↥Bs, b ^ 3 = 1)]
    (hN : Bs ≤ Subgroup.normalizer (X : Set G)) (uF : Fˣ) (hu : uF ^ 3 = 1)
    (huord : orderOf uF = 3) (hBs : GGBstar 3 B Bs) (hM : UnitTB.Model φ)
    (hdiag : ∀ b : ↥Bs, ∃ t : Fin m → F, LineU.ActsDiagU φ (ggGamma X hN b) t)
    (h3m : 3 ∣ m) (hm : 3 ≤ m) {z : G} (hzB : z ∈ Bs) (hz1 : z ≠ 1)
    (hzC : z ∈ Subgroup.centralizer (X : Set G))
    (hcardBs : Nat.card ↥Bs ≤ 3 ^ (m - 1))
    (hU : φ (hdRo7A3SMAux_dSU uF hu hM (hdRo7A3SMAux_gOne (m := m) h3m)) ≠ 1)
    {e : G} (heB : e ∈ Bs) (heC : e ∈ Subgroup.centralizer (X : Set G)) :
    e ∈ Subgroup.zpowers z := by
  classical
  have htop := hdRo7A3SMAux_range_eq_topU hN uF hu huord (p := 3) rfl hBs hM hdiag h3m
    (by omega : 1 ≤ m) hU hcardBs
  set eB : ↥Bs := ⟨e, heB⟩ with heBdef
  have hb : eB ∈ (hdRo7A3SMAux_torB hN uF hu rfl hBs hM hdiag).range := by
    rw [htop]
    exact Subgroup.mem_top _
  obtain ⟨w, hw⟩ := hb
  have hwG : ((hdRo7A3SMAux_tor uF hu hM w : ↥X) : G) = e := by
    rw [← hdRo7A3SMAux_torB_coe hN uF hu rfl hBs hM hdiag w, hw]
  have heC' : ((hdRo7A3SMAux_tor uF hu hM w : ↥X) : G) ∈
      Subgroup.centralizer (X : Set G) := by
    rw [hwG]
    exact heC
  obtain ⟨c, hc⟩ := hdRo7A3SMAux_const_of_mem_centralizer uF hu huord hM hm w heC'
  obtain ⟨κ, hκ, hzκ⟩ := hdRo7A3SMAux_kappaU hN uF hu huord (p := 3) rfl hBs hM hdiag h3m
    (by omega : 2 ≤ m) hzB hz1 hzC hcardBs hU
  set G1 : ↥Bs := hdRo7A3SMAux_torB hN uF hu rfl hBs hM hdiag
    (hdRo7A3SMAux_gOne (m := m) h3m) with hG1
  have he_eq : eB = G1 ^ c.val := by
    rw [← hw, hdRo7A3SMAux_eq_gOne_pow_of_const h3m hc, map_pow, hG1]
  have hG1_3 : G1 ^ 3 = 1 := by
    rw [hG1, ← map_pow, hdRo7A3SMAux_gOne_pow_three h3m, map_one]
  have hz_eq : (⟨z, hzB⟩ : ↥Bs) = G1 ^ κ.val := by
    rw [hzκ]
    have hsm : Multiplicative.ofAdd (κ • hdRo7A3SMAux_ones (m := m) h3m) =
        hdRo7A3SMAux_gOne (m := m) h3m ^ κ.val := by
      rw [hdRo7A3SMAux_smul_eq_nsmul κ (hdRo7A3SMAux_ones (m := m) h3m), ofAdd_nsmul]
      rfl
    rw [hsm, map_pow, hG1]
  set g : G := (G1 : G) with hgdef
  have hg3 : g ^ 3 = 1 := by
    rw [hgdef, ← Subgroup.coe_pow, hG1_3]
    rfl
  have heG : e = g ^ c.val := by
    have h1 : ((eB : ↥Bs) : G) = e := rfl
    rw [← h1, he_eq, hgdef, Subgroup.coe_pow]
  have hzG : z = g ^ κ.val := by
    have h1 : ((⟨z, hzB⟩ : ↥Bs) : G) = z := rfl
    rw [← h1, hz_eq, hgdef, Subgroup.coe_pow]
  have hz_val : κ.val = 1 ∨ κ.val = 2 := by
    have hlt : κ.val < 3 := ZMod.val_lt κ
    have h0 : κ.val ≠ 0 := by
      intro h
      apply hκ
      have h1 : κ = (κ.val : ZMod 3) := (ZMod.natCast_zmod_val κ).symm
      rw [h] at h1
      simpa using h1
    omega
  rcases hz_val with hv | hv
  · refine Subgroup.mem_zpowers_iff.mpr ⟨(c.val : ℤ), ?_⟩
    rw [zpow_natCast, hzG, hv, pow_one]
    exact heG.symm
  · refine Subgroup.mem_zpowers_iff.mpr ⟨((2 * c.val : ℕ) : ℤ), ?_⟩
    rw [zpow_natCast, hzG, hv, ← pow_mul]
    have harith : g ^ (2 * (2 * c.val)) = g ^ c.val := by
      conv_lhs => rw [show 2 * (2 * c.val) = 3 * c.val + c.val by ring]
      rw [pow_add, pow_mul, hg3, one_pow, one_mul]
    rw [harith]
    exact heG.symm

private theorem hdRo7A3SMAux_zpowers_M
    [Finite G]
    [IsMulCommutative ↥Bs] [Fact (∀ b : ↥Bs, b ^ 3 = 1)]
    (hN : Bs ≤ Subgroup.normalizer (X : Set G)) (uF : Fˣ) (hu : uF ^ 3 = 1)
    (huord : orderOf uF = 3) (hBs : GGBstar 3 B Bs) (hM : UnitTB.Model φ)
    (hdiag : ∀ b : ↥Bs, ∃ t : Fin m → F, LineU.ActsDiagU φ (ggGamma X hN b) t)
    (h3m : 3 ∣ m) (hm : 2 ≤ m) {z : G} (hzB : z ∈ Bs) (hz1 : z ≠ 1)
    (hzC : z ∈ Subgroup.centralizer (X : Set G))
    (hcardBs : Nat.card ↥Bs ≤ 3 ^ (m - 1))
    (hMone : φ (hdRo7A3SMAux_dSU uF hu hM (hdRo7A3SMAux_gOne (m := m) h3m)) = 1)
    {e : G} (heB : e ∈ Bs) (heC : e ∈ Subgroup.centralizer (X : Set G)) :
    e ∈ Subgroup.zpowers z := by
  classical
  set eB : ↥Bs := ⟨e, heB⟩ with heBdef
  obtain ⟨w, k, hk⟩ := hdRo7A3SMAux_decompM hN uF hu huord (p := 3) rfl hBs hM hdiag h3m hm
    hMone hzB hz1 (hBs.2.1.2 z hzB) hzC hcardBs eB
  have htorG : ((hdRo7A3SMAux_torB hN uF hu rfl hBs hM hdiag w : ↥Bs) : G) =
      e * (z ^ k)⁻¹ := by
    have h := congrArg (fun b : ↥Bs => (b : G)) hk
    rw [Subgroup.coe_mul, Subgroup.coe_pow] at h
    have h' : ((hdRo7A3SMAux_torB hN uF hu rfl hBs hM hdiag w : ↥Bs) : G) * z ^ k = e := by
      rw [← h]
    rw [← h']
    group
  have heC'' : ((hdRo7A3SMAux_torB hN uF hu rfl hBs hM hdiag w : ↥Bs) : G) ∈
      Subgroup.centralizer (X : Set G) := by
    rw [htorG]
    exact Subgroup.mul_mem _ heC (Subgroup.inv_mem _ (Subgroup.pow_mem _ hzC k))
  have hwC : ((hdRo7A3SMAux_tor uF hu hM w : ↥X) : G) ∈
      Subgroup.centralizer (X : Set G) := by
    rw [← hdRo7A3SMAux_torB_coe hN uF hu rfl hBs hM hdiag w]
    exact heC''
  obtain ⟨c, hc⟩ := hdRo7A3SMAux_const_of_mem_centralizer uF hu huord hM (by omega) w hwC
  have htor1 : hdRo7A3SMAux_tor uF hu hM (hdRo7A3SMAux_gOne (m := m) h3m) = 1 := by
    rw [hdRo7A3SMAux_tor_apply, hMone]
  have hw1 : hdRo7A3SMAux_torB hN uF hu rfl hBs hM hdiag w = 1 := by
    apply Subtype.ext
    rw [hdRo7A3SMAux_torB_coe, hdRo7A3SMAux_eq_gOne_pow_of_const h3m hc, map_pow, htor1,
      one_pow]
    rfl
  have hek : e = z ^ k := by
    have h := congrArg (fun b : ↥Bs => (b : G)) hk
    rw [Subgroup.coe_mul, Subgroup.coe_pow, hw1] at h
    simpa using h
  refine Subgroup.mem_zpowers_iff.mpr ⟨(k : ℤ), ?_⟩
  rw [zpow_natCast]
  exact hek.symm

private theorem hdRo7A3SMAux_a3P_of_mem
    [Finite F]
    [IsMulCommutative ↥Bs] [Fact (∀ b : ↥Bs, b ^ 3 = 1)]
    (hN : Bs ≤ Subgroup.normalizer (X : Set G)) (uF : Fˣ) (hu : uF ^ 3 = 1)
    (hFcard : Nat.card F = 4) (hBs : GGBstar 3 B Bs) (hM : UnitTB.Model φ)
    (hdiag : ∀ b : ↥Bs, ∃ t : Fin m → F, LineU.ActsDiagU φ (ggGamma X hN b) t)
    (hm9 : 9 ≤ m) (i0 : Fin m) (κ : ZMod 3) {z : G} (hzB : z ∈ Bs)
    (hz3 : (⟨z, hzB⟩ : ↥Bs) ^ 3 = 1)
    (hzC : z ∈ Subgroup.centralizer (X : Set G))
    {ψ : MulAut ↥Bs} (hψ : ψ ∈ ggAutomizer X Bs) :
    A3P 3 m (hdRo7A3SMAux_theta hN uF hu rfl hBs hM hdiag i0 κ hzB hz3)
      (Additive.ofMul (⟨z, hzB⟩ : ↥Bs))
      (ggLin (p := 3) (AddEquiv.refl (Additive ↥Bs)) ψ) := by
  classical
  obtain ⟨s, hsX, hsN, hconj⟩ := mem_ggAutomizer_iff.mp hψ
  obtain ⟨gU, hgU⟩ := hM.surj ⟨s, hsX⟩
  have hgN : MulAut.conj (φ gU) ∈
      Subgroup.normalizer ((ggGamma X hN).range : Set (MulAut ↥X)) := by
    rw [hgU]
    exact hdRo7A3SMAux_conj_mem_normalizer hN hsX hsN
  have hK : Nat.card F = (2 ^ 1) ^ 2 := by rw [hFcard]; norm_num
  obtain ⟨π, hperm⟩ := UnitAct.exists_perm_of_normalizes hM hK (by norm_num) (by norm_num)
    (by norm_num) (by omega) (hdRo7A3SMAux_range_elemAbelian hN rfl hBs)
    (ggTorusSelfCent_ggGamma hN hBs.2.2.2) (hdRo7A3SMAux_range_diag hN hdiag) hgN
  have hconj' : ∀ b : ↥Bs, ((ψ b : ↥Bs) : G) =
      ((φ gU : ↥X) : G) * (b : G) * ((φ gU : ↥X) : G)⁻¹ := by
    intro b
    rw [hconj b, hgU]
  have hzfix : ((φ gU : ↥X) : G) * z * ((φ gU : ↥X) : G)⁻¹ = z := by
    rw [hgU]
    have hcomm := (Subgroup.mem_centralizer_iff.mp hzC) s hsX
    calc s * z * s⁻¹ = z * s * s⁻¹ := by rw [hcomm]
      _ = z := by group
  exact hdRo7A3SMAux_a3P_of_perm hN uF hu rfl hBs hM hdiag i0 κ hzB hz3 ψ gU π
    hconj' hperm hzfix

private theorem hdRo7A3SMAux_model_U
    [Finite G] [Finite F]
    [IsMulCommutative ↥Bs] [Fact (∀ b : ↥Bs, b ^ 3 = 1)]
    (hN : Bs ≤ Subgroup.normalizer (X : Set G)) (uF : Fˣ) (hu : uF ^ 3 = 1)
    (huord : orderOf uF = 3) (hFcard : Nat.card F = 4) (hBs : GGBstar 3 B Bs)
    (hM : UnitTB.Model φ)
    (hdiag : ∀ b : ↥Bs, ∃ t : Fin m → F, LineU.ActsDiagU φ (ggGamma X hN b) t)
    (hm9 : 9 ≤ m) (h3m : 3 ∣ m) {z : G} (hzB : z ∈ Bs) (hz1 : z ≠ 1)
    (hzC : z ∈ Subgroup.centralizer (X : Set G))
    (hz3 : (⟨z, hzB⟩ : ↥Bs) ^ 3 = 1)
    (hcardBs : Nat.card ↥Bs ≤ 3 ^ (m - 1))
    (hU : φ (hdRo7A3SMAux_dSU uF hu hM (hdRo7A3SMAux_gOne (m := m) h3m)) ≠ 1) :
    A3ModelAt 3 Bs X z := by
  classical
  obtain ⟨i0⟩ : Nonempty (Fin m) := ⟨⟨0, by omega⟩⟩
  obtain ⟨κ, hκ, hzκ⟩ := hdRo7A3SMAux_kappaU hN uF hu huord (p := 3) rfl hBs hM hdiag h3m
    (by omega : 2 ≤ m) hzB hz1 hzC hcardBs hU
  have hfr := hdRo7A3SMAux_frameU (m := m) hN uF hu huord (p := 3) rfl hBs hM hdiag h3m
    (by omega : 2 ≤ m) hzB hz3 hz1 hzC hcardBs i0 hU κ hκ hzκ
  have hdec : ∀ b : ↥Bs, ∃ (w : Multiplicative ↥(a3Aug 3 m)) (k : ℕ),
      b = hdRo7A3SMAux_torB hN uF hu rfl hBs hM hdiag w * (⟨z, hzB⟩ : ↥Bs) ^ k := by
    intro b
    have htop := hdRo7A3SMAux_range_eq_topU hN uF hu huord (p := 3) rfl hBs hM hdiag h3m
      (by omega : 1 ≤ m) hU hcardBs
    have hb : b ∈ (hdRo7A3SMAux_torB hN uF hu rfl hBs hM hdiag).range := by
      rw [htop]
      exact Subgroup.mem_top b
    obtain ⟨w, hw⟩ := hb
    exact ⟨w, 0, by rw [pow_zero, mul_one]; exact hw.symm⟩
  refine ⟨m, Additive ↥Bs, hdRo7A3SMAux_instAddCommGroup, hdRo7A3SMAux_instModule,
    AddEquiv.refl _, hdRo7A3SMAux_theta hN uF hu rfl hBs hM hdiag i0 κ hzB hz3, hzB,
    rfl, hm9, h3m, hfr, ?_⟩
  intro g
  constructor
  · intro hg
    obtain ⟨ψ, hψ, rfl⟩ := Subgroup.mem_map.mp hg
    exact hdRo7A3SMAux_a3P_of_mem hN uF hu hFcard hBs hM hdiag hm9 i0 κ hzB hz3 hzC hψ
  · intro hg
    exact hdRo7A3SMAux_mem_map_of_a3P hN uF hu rfl hBs hM hdiag i0 κ hzB hz3 hzC hdec hfr hg

private theorem hdRo7A3SMAux_model_M
    [Finite G] [Finite F]
    [IsMulCommutative ↥Bs] [Fact (∀ b : ↥Bs, b ^ 3 = 1)]
    (hN : Bs ≤ Subgroup.normalizer (X : Set G)) (uF : Fˣ) (hu : uF ^ 3 = 1)
    (huord : orderOf uF = 3) (hFcard : Nat.card F = 4) (hBs : GGBstar 3 B Bs)
    (hM : UnitTB.Model φ)
    (hdiag : ∀ b : ↥Bs, ∃ t : Fin m → F, LineU.ActsDiagU φ (ggGamma X hN b) t)
    (hm9 : 9 ≤ m) (h3m : 3 ∣ m) {z : G} (hzB : z ∈ Bs) (hz1 : z ≠ 1)
    (hzC : z ∈ Subgroup.centralizer (X : Set G))
    (hz3 : (⟨z, hzB⟩ : ↥Bs) ^ 3 = 1)
    (hcardBs : Nat.card ↥Bs ≤ 3 ^ (m - 1))
    (hMone : φ (hdRo7A3SMAux_dSU uF hu hM (hdRo7A3SMAux_gOne (m := m) h3m)) = 1) :
    A3ModelAt 3 Bs X z := by
  classical
  obtain ⟨i0⟩ : Nonempty (Fin m) := ⟨⟨0, by omega⟩⟩
  have hfr := hdRo7A3SMAux_frameM (m := m) hN uF hu huord (p := 3) rfl hBs hM hdiag h3m
    (by omega : 2 ≤ m) hzB hz3 hz1 hzC hcardBs i0 hMone
  have hdec : ∀ b : ↥Bs, ∃ (w : Multiplicative ↥(a3Aug 3 m)) (k : ℕ),
      b = hdRo7A3SMAux_torB hN uF hu rfl hBs hM hdiag w * (⟨z, hzB⟩ : ↥Bs) ^ k :=
    fun b => hdRo7A3SMAux_decompM hN uF hu huord (p := 3) rfl hBs hM hdiag h3m
      (by omega : 2 ≤ m) hMone hzB hz1 (hBs.2.1.2 z hzB) hzC hcardBs b
  refine ⟨m, Additive ↥Bs, hdRo7A3SMAux_instAddCommGroup, hdRo7A3SMAux_instModule,
    AddEquiv.refl _, hdRo7A3SMAux_theta hN uF hu rfl hBs hM hdiag i0 1 hzB hz3, hzB,
    rfl, hm9, h3m, hfr, ?_⟩
  intro g
  constructor
  · intro hg
    obtain ⟨ψ, hψ, rfl⟩ := Subgroup.mem_map.mp hg
    exact hdRo7A3SMAux_a3P_of_mem hN uF hu hFcard hBs hM hdiag hm9 i0 1 hzB hz3 hzC hψ
  · intro hg
    exact hdRo7A3SMAux_mem_map_of_a3P hN uF hu rfl hBs hM hdiag i0 1 hzB hz3 hzC hdec hfr hg

end Automizer

theorem a3_sideMat_holds : A3SideMatLeaf := by
  intro G _ _ p hpFact B Bs X z m hp3 hm9 h3m hBs hD hzB hz1 hzC hcardBs
  subst hp3
  obtain ⟨hN, F, hFfield, hFfin, φ, hFcard, hM, hdiag⟩ := hD
  have hcommBs : IsMulCommutative ↥Bs := hBs.2.1.1
  have hfactBs : Fact (∀ b : ↥Bs, b ^ 3 = 1) := ⟨fun b => Subtype.ext (by
    simpa using hBs.2.1.2 (b : G) b.2)⟩
  have hz3 : (⟨z, hzB⟩ : ↥Bs) ^ 3 = 1 := by
    apply Subtype.ext
    simpa using hBs.2.1.2 z hzB
  obtain ⟨ω, hω⟩ := CFSG.RankThree.PartOne.KFU.exists_isPrimitiveRoot (ℓ := 2) (f := 1)
    (p := 3) (K := F) hM.field (by norm_num) (by norm_num)
  obtain ⟨uF, huF⟩ := hω.isUnit (by norm_num : 3 ≠ 0)
  have hu : uF ^ 3 = 1 := by
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, huF, hω.pow_eq_one, Units.val_one]
  have hune : uF ≠ 1 := by
    intro h
    apply hω.ne_one (by norm_num : 1 < 3)
    rw [← huF, h, Units.val_one]
  have huord : orderOf uF = 3 := orderOf_eq_prime hu hune
  constructor
  · by_cases hMone : φ (hdRo7A3SMAux_dSU uF hu hM (hdRo7A3SMAux_gOne (m := m) h3m)) = 1
    · exact hdRo7A3SMAux_model_M hN uF hu huord hFcard hBs hM hdiag hm9 h3m hzB hz1 hzC
        hz3 hcardBs hMone
    · exact hdRo7A3SMAux_model_U hN uF hu huord hFcard hBs hM hdiag hm9 h3m hzB hz1 hzC
        hz3 hcardBs hMone
  · intro e he
    by_cases hMone : φ (hdRo7A3SMAux_dSU uF hu hM (hdRo7A3SMAux_gOne (m := m) h3m)) = 1
    · exact hdRo7A3SMAux_zpowers_M hN uF hu huord hBs hM hdiag h3m (by omega) hzB hz1 hzC
        hcardBs hMone he.1 he.2
    · exact hdRo7A3SMAux_zpowers_U hN uF hu huord hBs hM hdiag h3m (by omega) hzB hz1 hzC
        hcardBs hMone he.1 he.2

end CFSG.StandardType.HdRo7A3
