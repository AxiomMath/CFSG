module

public import CFSG.Quasithin.Vol2.GoldschmidtF431U42AutP6Cls
public import CFSG.Quasithin.Vol2.GoldschmidtF431U42AutP6Fix
public import CFSG.Quasithin.Vol2.GoldschmidtF431U42AutP6Mod

public section

namespace CFSG.Quasithin.H13.F431.U42Aut

open CFSG.Quasithin CFSG.QuasithinUnique U42F431
open CFSG.Quasithin.H13.F431.U42 (P45)

@[expose] def da1 : PL := Thl.getD 81 []

@[expose] def db1 : PL := Thl.getD 17 []

@[expose] def da2 : PL := Thl.getD 94 []

@[expose] def db2 : PL := Thl.getD 3 []

@[expose] def powL (l : PL) : ℕ → PL
  | 0 => idL
  | k + 1 => comp l (powL l k)

@[expose] def dphi (a b : PL) : DihedralGroup 4 → PL
  | DihedralGroup.r i => powL a i.val
  | DihedralGroup.sr i => comp (powL a ((4 - i.val) % 4)) b

theorem dphi_mul1 : ∀ x y : DihedralGroup 4,
    dphi da1 db1 (x * y) = comp (dphi da1 db1 x) (dphi da1 db1 y) := by decide +kernel

theorem dphi_mul2 : ∀ x y : DihedralGroup 4,
    dphi da2 db2 (x * y) = comp (dphi da2 db2 x) (dphi da2 db2 y) := by decide +kernel

theorem dphi_comm : ∀ x y : DihedralGroup 4,
    comp (dphi da1 db1 x) (dphi da2 db2 y) = comp (dphi da2 db2 y) (dphi da1 db1 x) := by
  decide +kernel

theorem dphi_one : ∀ a b : PL, dphi a b 1 = idL := by
  intro a b
  rfl

theorem dphi_mem : (∀ x, dphi da1 db1 x ∈ Thl ∧ comp (dphi da1 db1 x) (Tl.getD 20 []) =
      comp (Tl.getD 20 []) (dphi da1 db1 x)) ∧
    (∀ x, dphi da2 db2 x ∈ Thl ∧ comp (dphi da2 db2 x) (Tl.getD 20 []) =
      comp (Tl.getD 20 []) (dphi da2 db2 x)) := by
  decide +kernel

theorem dPhi_inj : ∀ x y : DihedralGroup 4 × DihedralGroup 4,
    comp (dphi da1 db1 x.1) (dphi da2 db2 x.2) = comp (dphi da1 db1 y.1) (dphi da2 db2 y.2) →
      x = y := by
  decide +kernel

@[expose] noncomputable def eltOf (l : PL) (h : l ∈ Thl) : Ah :=
  Classical.choose (exists_That_of_mem_Thl h)

theorem eltOf_mem (l : PL) (h : l ∈ Thl) : eltOf l h ∈ That :=
  (Classical.choose_spec (exists_That_of_mem_Thl h)).1

theorem repL_eltOf (l : PL) (h : l ∈ Thl) :
    RepL l ((eltOf l h : Ah) : P45) :=
  (Classical.choose_spec (exists_That_of_mem_Thl h)).2

@[expose] noncomputable def dhom (a b : PL)
    (hmem : ∀ x, dphi a b x ∈ Thl) (hmul : ∀ x y : DihedralGroup 4,
      dphi a b (x * y) = comp (dphi a b x) (dphi a b y)) : DihedralGroup 4 →* Ah where
  toFun x := eltOf (dphi a b x) (hmem x)
  map_one' := by
    apply Subtype.ext
    apply eq_of_repL (repL_eltOf _ (hmem 1))
    rw [dphi_one]
    exact repL_one 45
  map_mul' x y := by
    apply Subtype.ext
    apply eq_of_repL (repL_eltOf _ (hmem (x * y)))
    rw [hmul]
    exact repL_mul (repL_eltOf _ (hmem x)) (repL_eltOf _ (hmem y))

theorem repL_dhom (a b : PL) (hmem : ∀ x, dphi a b x ∈ Thl)
    (hmul : ∀ x y : DihedralGroup 4, dphi a b (x * y) = comp (dphi a b x) (dphi a b y))
    (x : DihedralGroup 4) : RepL (dphi a b x) ((dhom a b hmem hmul x : Ah) : P45) :=
  repL_eltOf _ (hmem x)

theorem dcomm (m n : DihedralGroup 4) :
    Commute (dhom da1 db1 (fun x => (dphi_mem.1 x).1) dphi_mul1 m)
      (dhom da2 db2 (fun x => (dphi_mem.2 x).1) dphi_mul2 n) :=
  comm_of_comp_comm (repL_dhom da2 db2 (fun x => (dphi_mem.2 x).1) dphi_mul2 n)
    (repL_dhom da1 db1 (fun x => (dphi_mem.1 x).1) dphi_mul1 m) (dphi_comm m n)

@[expose] noncomputable def dprod :
    DihedralGroup 4 × DihedralGroup 4 →* Ah :=
  (dhom da1 db1 (fun x => (dphi_mem.1 x).1) dphi_mul1).noncommCoprod
    (dhom da2 db2 (fun x => (dphi_mem.2 x).1) dphi_mul2) dcomm

theorem dprod_apply (x : DihedralGroup 4 × DihedralGroup 4) :
    dprod x = dhom da1 db1 (fun x => (dphi_mem.1 x).1) dphi_mul1 x.1 *
      dhom da2 db2 (fun x => (dphi_mem.2 x).1) dphi_mul2 x.2 := rfl

theorem repL_dprod (x : DihedralGroup 4 × DihedralGroup 4) :
    RepL (comp (dphi da1 db1 x.1) (dphi da2 db2 x.2)) ((dprod x : Ah) : P45) := by
  rw [dprod_apply]
  exact repL_mul (repL_dhom da1 db1 (fun x => (dphi_mem.1 x).1) dphi_mul1 x.1)
    (repL_dhom da2 db2 (fun x => (dphi_mem.2 x).1) dphi_mul2 x.2)

theorem dprod_injective : Function.Injective dprod := by
  intro x y h
  apply dPhi_inj
  have h1 := repL_dprod x
  have h2 := repL_dprod y
  rw [h] at h1
  exact repL_unique h1 h2

theorem dprod_mem (x : DihedralGroup 4 × DihedralGroup 4) :
    dprod x ∈ That ⊓ Subgroup.centralizer ({t0A} : Set Ah) := by
  refine ⟨?_, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
  · rw [dprod_apply]
    exact That.mul_mem (eltOf_mem _ (dphi_mem.1 x.1).1) (eltOf_mem _ (dphi_mem.2 x.2).1)
  · rw [dprod_apply]
    have c1 := comm_of_comp_comm (v := t0A) repL_t0A
      (repL_dhom da1 db1 (fun x => (dphi_mem.1 x).1) dphi_mul1 x.1) (dphi_mem.1 x.1).2
    have c2 := comm_of_comp_comm (v := t0A) repL_t0A
      (repL_dhom da2 db2 (fun x => (dphi_mem.2 x).1) dphi_mul2 x.2) (dphi_mem.2 x.2).2
    calc dhom da1 db1 (fun x => (dphi_mem.1 x).1) dphi_mul1 x.1 *
          dhom da2 db2 (fun x => (dphi_mem.2 x).1) dphi_mul2 x.2 * t0A
        = dhom da1 db1 (fun x => (dphi_mem.1 x).1) dphi_mul1 x.1 *
          (dhom da2 db2 (fun x => (dphi_mem.2 x).1) dphi_mul2 x.2 * t0A) := by group
      _ = dhom da1 db1 (fun x => (dphi_mem.1 x).1) dphi_mul1 x.1 *
          (t0A * dhom da2 db2 (fun x => (dphi_mem.2 x).1) dphi_mul2 x.2) := by rw [c2]
      _ = t0A * (dhom da1 db1 (fun x => (dphi_mem.1 x).1) dphi_mul1 x.1 *
          dhom da2 db2 (fun x => (dphi_mem.2 x).1) dphi_mul2 x.2) := by
        rw [← mul_assoc, c1, mul_assoc]

theorem card_cent_t0 :
    Nat.card ↥(That ⊓ Subgroup.centralizer ({t0A} : Set Ah)) ≤ 64 :=
  card_cent_le_64 t0A_mem_That t0A_sq t0A_ne_one (fun h => not_isConj_t0A_xA (h ▸ IsConj.refl _))

theorem cent_t0_equiv :
    Nonempty (↥(That ⊓ Subgroup.centralizer ({t0A} : Set Ah)) ≃*
      DihedralGroup 4 × DihedralGroup 4) := by
  have hle : dprod.range ≤ That ⊓ Subgroup.centralizer ({t0A} : Set Ah) := by
    rintro _ ⟨x, rfl⟩
    exact dprod_mem x
  have hcard : Nat.card ↥(That ⊓ Subgroup.centralizer ({t0A} : Set Ah)) ≤ Nat.card dprod.range := by
    rw [Nat.card_congr (MonoidHom.ofInjective dprod_injective).toEquiv.symm]
    have : Nat.card (DihedralGroup 4 × DihedralGroup 4) = 64 := by
      rw [Nat.card_prod, DihedralGroup.nat_card]
    rw [this]
    exact card_cent_t0
  have hrange := Subgroup.eq_of_le_of_card_ge hle hcard
  exact ⟨((MonoidHom.ofInjective dprod_injective).trans
    (MulEquiv.subgroupCongr hrange)).symm⟩

end CFSG.Quasithin.H13.F431.U42Aut
