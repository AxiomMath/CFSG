module

public import CFSG.LocalAnalysis.StandardType.GGFFModel
public import CFSG.RankThree.PartTwo.Sec21.FF81Defs
public import CFSG.LieType.CurtisTits.Conclusion
public import CFSG.LieType.Universal.Spin.Roots
public import CFSG.LieType.Universal.Unitary
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.RankThree.PartTwo.Sec21.HoltCatalog
public import Certificates.Certificate43

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

@[expose] public section

namespace CFSG.StandardType.GGFF

open scoped Pointwise
open CFSG.RankThree.PartTwo.Sec21.FF79 (Cen CenS Nor conjBy IsElemAb)
open CFSG.RankThree.PartTwo.Sec21.FF81 (HasH0)
open CFSG.RankThree.PartTwo.Sec4.Item434Kit (vecElt vecElt_single_one)

variable {G : Type} [Group G]

theorem eq_or_eq_inv_of_mem_zpowers {b x : G} (hb : orderOf b = 3) (hx : x ∈ Subgroup.zpowers b)
    (hx1 : x ≠ 1) : x = b ∨ x = b⁻¹ := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
  rw [← zpow_mod_orderOf, hb] at hx1 ⊢
  have : (k % ((3 : ℕ) : ℤ)) = 0 ∨ k % ((3 : ℕ) : ℤ) = 1 ∨ k % ((3 : ℕ) : ℤ) = 2 := by omega
  rcases this with h0 | h0 | h0 <;> rw [h0] at hx1 ⊢
  · exact absurd (zpow_zero b) hx1
  · left; exact zpow_one b
  · right
    rw [eq_inv_iff_mul_eq_one, ← zpow_add_one]
    norm_num
    rw [← hb]
    exact pow_orderOf_eq_one b

theorem mem_nor_of_conj_mem [Finite G] {B : Subgroup G} {n : G}
    (h : ∀ x ∈ B, n * x * n⁻¹ ∈ B) : n ∈ Nor B := by
  have hle : conjBy n B ≤ B := by
    rintro _ ⟨x, hx, rfl⟩
    exact h x hx
  have heq : conjBy n B = B := Subgroup.eq_of_le_of_card_ge hle
    (by rw [Subgroup.card_map_of_injective (MulAut.conj n).injective])
  refine Subgroup.mem_normalizer_iff.mpr fun x => ⟨h x, fun hx => ?_⟩
  rw [← heq] at hx
  obtain ⟨y, hy, hyx⟩ := hx
  have : y = x := by
    have := hyx
    simp only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe, MulAut.conj_apply] at this
    exact mul_left_cancel (mul_right_cancel this)
  exact this ▸ hy

theorem inv_conj_mem_of_conj_mem [Finite G] {K : Subgroup G} {n : G}
    (h : ∀ k ∈ K, n * k * n⁻¹ ∈ K) {k : G} (hk : k ∈ K) : n⁻¹ * k * n ∈ K := by
  have hn : n ∈ Nor K := mem_nor_of_conj_mem h
  have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hn) k).mp hk
  simpa using this

def conjAut [Finite G] {K : Subgroup G} {n : G} (hn : ∀ k ∈ K, n * k * n⁻¹ ∈ K) : MulAut K where
  toFun y := ⟨n * y * n⁻¹, hn y y.2⟩
  invFun y := ⟨n⁻¹ * y * n, inv_conj_mem_of_conj_mem hn y.2⟩
  left_inv y := Subtype.ext (by simp only; group)
  right_inv y := Subtype.ext (by simp only; group)
  map_mul' a c := Subtype.ext (by simp only [Subgroup.coe_mul]; group)

theorem conjAut_apply [Finite G] {K : Subgroup G} {n : G} (hn : ∀ k ∈ K, n * k * n⁻¹ ∈ K)
    (y : K) : ((conjAut hn y : K) : G) = n * y * n⁻¹ := rfl

theorem mem_nor_of_closure [Finite G] {S : Set G} {n : G}
    (h : ∀ s ∈ S, n * s * n⁻¹ ∈ Subgroup.closure S) : n ∈ Nor (Subgroup.closure S) := by
  refine mem_nor_of_conj_mem fun x hx => ?_
  have hle : Subgroup.closure S ≤ (Subgroup.closure S).comap (MulAut.conj n).toMonoidHom :=
    (Subgroup.closure_le _).mpr fun s hs => by
      simpa only [SetLike.mem_coe, Subgroup.mem_comap, MulEquiv.toMonoidHom_eq_coe,
        MonoidHom.coe_coe, MulAut.conj_apply] using h s hs
  simpa only [Subgroup.mem_comap, MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe,
    MulAut.conj_apply] using hle hx

theorem mem_conjBy {g x : G} {H : Subgroup G} : x ∈ conjBy g H ↔ g⁻¹ * x * g ∈ H := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    have e : g⁻¹ * ((MulAut.conj g).toMonoidHom y) * g = y := by
      simp only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe, MulAut.conj_apply]
      group
    rwa [e]
  · intro hx
    refine ⟨_, hx, ?_⟩
    simp only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe, MulAut.conj_apply]
    group

theorem card_le_three_of_cyclic {P : Subgroup G} [IsCyclic P]
    (hP : CFSG.Assembly.IsElemAbelian 3 P) : Nat.card P ≤ 3 := by
  have hexp : Monoid.exponent P ∣ 3 :=
    Monoid.exponent_dvd_of_forall_pow_eq_one fun y => Subtype.ext (by simpa using hP.2 y y.2)
  rw [IsCyclic.exponent_eq_card] at hexp
  exact Nat.le_of_dvd (by norm_num) hexp

abbrev zs {K : Subgroup G} (z : Fin 3 → K) : Fin 3 → G := fun i => (z i : G)

def Bt (b : G) {K : Subgroup G} (z : Fin 3 → K) : Subgroup G := Subgroup.zpowers b ⊔ tor (zs z)

structure SettingCore (b : G) (K : Subgroup G) (z : Fin 3 → K) : Prop where
  ord : orderOf b = 3
  le : K ≤ Cen b
  nor : ∀ c ∈ Cen b, ∀ k ∈ K, c * k * c⁻¹ ∈ K
  model : Model K z
  cyc : ∀ P : Subgroup G, P ≤ CenS K → IsPGroup 3 P → IsCyclic P

structure Setting (b : G) (K : Subgroup G) (z : Fin 3 → K) : Prop extends SettingCore b K z where
  meet : ∃ g : G, g * b * g⁻¹ ∈ K

namespace SettingCore

variable {b : G} {K : Subgroup G} {z : Fin 3 → K}

theorem b_cube (h : SettingCore b K z) : b ^ 3 = 1 := by
  rw [← h.ord]
  exact pow_orderOf_eq_one b

theorem b_ne_one (h : SettingCore b K z) : b ≠ 1 := fun h1 => by
  have := h.ord
  rw [h1, orderOf_one] at this
  omega

theorem comm_of_mem (h : SettingCore b K z) {k : G} (hk : k ∈ K) : k * b = b * k :=
  Subgroup.mem_centralizer_singleton_iff.mp (h.le hk)

theorem b_mem_cenS (h : SettingCore b K z) : b ∈ CenS K :=
  Subgroup.mem_centralizer_iff.mpr fun _ hk => (h.comm_of_mem hk)

theorem eq_one_of_mem (h : SettingCore b K z) {k : G} (hk : k ∈ K) (hc : ∀ y ∈ K, k * y = y * k) :
    k = 1 := by
  have := h.model.eq_one_of_forall_comm (x := ⟨k, hk⟩) fun y => Subtype.ext (hc y y.2)
  exact congrArg Subtype.val this

theorem b_not_mem (h : SettingCore b K z) : b ∉ K := fun hb =>
  h.b_ne_one (h.eq_one_of_mem hb fun _ hy => (h.comm_of_mem hy).symm)

theorem zpow_eq_one_of_mem (h : SettingCore b K z) {j : ℤ} (hj : b ^ j ∈ K) : b ^ j = 1 := by
  by_contra hne
  rcases eq_or_eq_inv_of_mem_zpowers h.ord (Subgroup.zpow_mem_zpowers b j) hne with he | he
  · exact h.b_not_mem (he ▸ hj)
  · have hb : b⁻¹ ∈ K := he ▸ hj
    exact h.b_not_mem (by simpa using K.inv_mem hb)

theorem zs_mem (z : Fin 3 → K) (i : Fin 3) : zs z i ∈ K := (z i).2

theorem zs_pow (h : SettingCore b K z) (i : Fin 3) : zs z i ^ 3 = 1 := by
  simp only [zs]
  rw [← Subgroup.coe_pow, h.model.pow_z, Subgroup.coe_one]

theorem zs_comm (h : SettingCore b K z) (i j : Fin 3) : zs z i * zs z j = zs z j * zs z i := by
  simp only [zs]
  rw [← Subgroup.coe_mul, h.model.comm_z, Subgroup.coe_mul]

theorem vecElt_zs (z : Fin 3 → K) (v : Fin 3 → ZMod 3) :
    vecElt (zs z) v = ((vecElt z v : K) : G) :=
  vecElt_map K.subtype z v

theorem tor_le (z : Fin 3 → K) : tor (zs z) ≤ K :=
  (Subgroup.closure_le _).mpr (by rintro _ ⟨i, rfl⟩; exact zs_mem z i)

theorem mem_torG (h : SettingCore b K z) {x : G} : x ∈ tor (zs z) ↔ ∃ v, x = vecElt (zs z) v :=
  mem_tor h.zs_pow h.zs_comm

theorem tor_le_cen (h : SettingCore b K z) : tor (zs z) ≤ Cen b := (tor_le z).trans h.le

theorem zpowers_le_nor (h : SettingCore b K z) : Subgroup.zpowers b ≤ Nor (tor (zs z)) := by
  rw [Subgroup.zpowers_le]
  refine Subgroup.mem_normalizer_iff.mpr fun x => ?_
  by_cases hx : x ∈ tor (zs z)
  · have hc : x * b = b * x := Subgroup.mem_centralizer_singleton_iff.mp (h.tor_le_cen hx)
    have : b * x * b⁻¹ = x := by rw [← hc]; group
    rw [this]
  · have hc : ∀ y ∈ tor (zs z), b * x * b⁻¹ = y → x ∈ tor (zs z) := fun y hy hyx => by
      have hc : y * b = b * y := Subgroup.mem_centralizer_singleton_iff.mp (h.tor_le_cen hy)
      have : x = y := by
        have e : x = b⁻¹ * y * b := by rw [← hyx]; group
        rw [e, mul_assoc, hc]; group
      exact this ▸ hy
    exact ⟨fun h' => absurd h' hx, fun h' => absurd (hc _ h' rfl) hx⟩

theorem mem_Bt (h : SettingCore b K z) {x : G} :
    x ∈ Bt b z ↔ ∃ (j : ℤ) (v : Fin 3 → ZMod 3), x = b ^ j * vecElt (zs z) v := by
  rw [Bt, ← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right _ _ h.zpowers_le_nor]
  constructor
  · rintro ⟨y, hy, t, ht, rfl⟩
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    obtain ⟨v, rfl⟩ := h.mem_torG.mp ht
    exact ⟨j, v, rfl⟩
  · rintro ⟨j, v, rfl⟩
    exact ⟨b ^ j, Subgroup.zpow_mem_zpowers b j, _, vecElt_mem_tor _ v, rfl⟩

theorem b_mem_Bt (b : G) (z : Fin 3 → K) : b ∈ Bt b z :=
  Subgroup.mem_sup_left (Subgroup.mem_zpowers b)

theorem tor_le_Bt (b : G) (z : Fin 3 → K) : tor (zs z) ≤ Bt b z := le_sup_right

theorem zs_mem_Bt (b : G) (z : Fin 3 → K) (i : Fin 3) : zs z i ∈ Bt b z :=
  tor_le_Bt b z (Subgroup.subset_closure ⟨i, rfl⟩)

theorem isElemAbelian_Bt (h : SettingCore b K z) : CFSG.Assembly.IsElemAbelian 3 (Bt b z) :=
  CFSG.Open.IsElemAbelian.sup_of_commute (CFSG.Open.isElemAbelian_zpowers h.b_cube)
    (isElemAbelian_tor h.zs_pow h.zs_comm) (fun x hx y hy => by
      obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
      exact (Commute.zpow_right (Subgroup.mem_centralizer_singleton_iff.mp (h.tor_le_cen hy)) j
        |>.eq).symm)

theorem mem_tor_of_mem_Bt (h : SettingCore b K z) {x : G} (hx : x ∈ Bt b z) (hxK : x ∈ K) :
    x ∈ tor (zs z) := by
  obtain ⟨j, v, rfl⟩ := h.mem_Bt.mp hx
  have hv : vecElt (zs z) v ∈ K := tor_le z (vecElt_mem_tor _ v)
  have hj : b ^ j ∈ K := by simpa using K.mul_mem hxK (K.inv_mem hv)
  rw [h.zpow_eq_one_of_mem hj, one_mul]
  exact vecElt_mem_tor _ v

theorem card_Bt (h : SettingCore b K z) : Nat.card (Bt b z) = 81 := by
  have hinj : Function.Injective fun p : ZMod 3 × (Fin 3 → ZMod 3) =>
      b ^ (p.1.val : ℤ) * vecElt (zs z) p.2 := by
    rintro ⟨j, v⟩ ⟨j', v'⟩ hjv
    simp only at hjv
    have hv : vecElt (zs z) v ∈ K := tor_le z (vecElt_mem_tor _ v)
    have hv' : vecElt (zs z) v' ∈ K := tor_le z (vecElt_mem_tor _ v')
    have hK : b ^ ((j'.val : ℤ) - j.val) ∈ K := by
      have e0 : vecElt (zs z) v = b ^ (-(j.val : ℤ)) * (b ^ (j'.val : ℤ) * vecElt (zs z) v') := by
        rw [← hjv]; group
      have e : b ^ ((j'.val : ℤ) - j.val) = vecElt (zs z) v * (vecElt (zs z) v')⁻¹ := by
        rw [e0]; group
      rw [e]
      exact K.mul_mem hv (K.inv_mem hv')
    have h1 := h.zpow_eq_one_of_mem hK
    have hjj : j = j' := by
      rw [← orderOf_dvd_iff_zpow_eq_one, h.ord] at h1
      have hlt : j.val < 3 := ZMod.val_lt j
      have hlt' : j'.val < 3 := ZMod.val_lt j'
      have : j.val = j'.val := by omega
      exact ZMod.val_injective 3 this
    subst hjj
    have hvv := mul_left_cancel hjv
    rw [vecElt_zs, vecElt_zs] at hvv
    have := h.model.vecElt_inj (Subtype.ext hvv)
    rw [this]
  have e : ZMod 3 × (Fin 3 → ZMod 3) ≃ Bt b z :=
    Equiv.ofBijective (fun p => ⟨_, h.mem_Bt.mpr ⟨_, _, rfl⟩⟩) ⟨fun p q hpq =>
      hinj (congrArg Subtype.val hpq), fun ⟨x, hx⟩ => by
        obtain ⟨j, v, rfl⟩ := h.mem_Bt.mp hx
        refine ⟨((j : ZMod 3), v), Subtype.ext ?_⟩
        simp only
        congr 1
        rw [← zpow_mod_orderOf, h.ord, ← zpow_mod_orderOf b j, h.ord]
        congr 1
        rw [ZMod.val_intCast]
        push_cast
        omega⟩
  rw [← Nat.card_congr e, Nat.card_prod, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card,
    Fintype.card_fun, ZMod.card, Fintype.card_fin]
  norm_num

theorem Bt_eq_closure (b : G) (z : Fin 3 → K) :
    Bt b z = Subgroup.closure {b, zs z 0, zs z 1, zs z 2} := by
  rw [Set.insert_eq, Subgroup.closure_union, ← Subgroup.zpowers_eq_closure, Bt, tor]
  congr 2
  ext x
  simp only [Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨i, rfl⟩
    fin_cases i <;> simp
  · rintro (rfl | rfl | rfl)
    exacts [⟨0, rfl⟩, ⟨1, rfl⟩, ⟨2, rfl⟩]

theorem tor_eq_closure (z : Fin 3 → K) :
    tor (zs z) = Subgroup.closure {zs z 0, zs z 1, zs z 2} := by
  rw [tor]
  congr 1
  ext x
  simp only [Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨i, rfl⟩
    fin_cases i <;> simp
  · rintro (rfl | rfl | rfl)
    exacts [⟨0, rfl⟩, ⟨1, rfl⟩, ⟨2, rfl⟩]

theorem inj' (h : SettingCore b K z) (v : Fin 3 → ZMod 3) (hv : vecElt (zs z) v = 1) : v = 0 :=
  h.model.inj v (Subtype.ext (by rw [← vecElt_zs, hv]; rfl))

theorem card_torG (h : SettingCore b K z) : Nat.card (tor (zs z)) = 27 :=
  card_tor h.zs_pow h.zs_comm h.inj'

theorem conj_b (h : SettingCore b K z) {k : G} (hk : k ∈ K) : k * b * k⁻¹ = b := by
  rw [h.comm_of_mem hk, mul_inv_cancel_right]

theorem conj_mem_cen {n : G} (hn : n ∈ Nor (Subgroup.zpowers b)) {c : G} (hc : c ∈ Cen b) :
    n⁻¹ * c * n ∈ Cen b := by
  rw [Subgroup.mem_centralizer_singleton_iff] at hc ⊢
  obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp
    ((Subgroup.mem_normalizer_iff.mp hn b).mp (Subgroup.mem_zpowers b))
  have hcj : c * b ^ j = b ^ j * c := (Commute.zpow_right hc j).eq
  have hb : b = n⁻¹ * b ^ j * n := by rw [hj]; group
  calc n⁻¹ * c * n * b = n⁻¹ * c * n * (n⁻¹ * b ^ j * n) := by rw [← hb]
    _ = n⁻¹ * (c * b ^ j) * n := by group
    _ = n⁻¹ * (b ^ j * c) * n := by rw [hcj]
    _ = (n⁻¹ * b ^ j * n) * (n⁻¹ * c * n) := by group
    _ = b * (n⁻¹ * c * n) := by rw [← hb]

theorem cube_conj (h : SettingCore b K z) {g : G} (hg : g * b * g⁻¹ ∈ K) :
    (⟨g * b * g⁻¹, hg⟩ : K) ^ 3 = 1 :=
  Subtype.ext (by simp [conj_pow, h.b_cube])

theorem zs_sq (h : SettingCore b K z) (i : Fin 3) : zs z i ^ (2 : ZMod 3).val = (zs z i)⁻¹ := by
  rw [show (2 : ZMod 3).val = 2 from rfl, eq_inv_iff_mul_eq_one, ← pow_succ, h.zs_pow]

theorem zs_one (z : Fin 3 → K) (i : Fin 3) : zs z i ^ (1 : ZMod 3).val = zs z i := by
  rw [ZMod.val_one, pow_one]

variable [Finite G]

theorem exists_inner (h : SettingCore b K z) {x : G} (hx : x ∈ Cen b) (hx3 : x ^ 3 = 1) :
    ∃ k ∈ K, ∀ y ∈ K, x * y * x⁻¹ = k * y * k⁻¹ := by
  have hx3' : x * x * x = 1 := by rw [← pow_three', hx3]
  have h3 : conjAut (h.nor x hx) ^ 3 = 1 := by
    ext y
    simp only [pow_succ, pow_zero, one_mul, MulAut.mul_apply, conjAut_apply, MulAut.one_apply]
    calc x * (x * (x * (y : G) * x⁻¹) * x⁻¹) * x⁻¹ = (x * x * x) * y * (x * x * x)⁻¹ := by
          group
      _ = y := by rw [hx3']; group
  obtain ⟨k, hk⟩ := h.model.inner3 _ h3
  refine ⟨k, k.2, fun y hy => ?_⟩
  have := congrArg (fun α : MulAut K => ((α ⟨y, hy⟩ : K) : G)) hk
  simpa [conjAut_apply, MulAut.conj_apply] using this

theorem mem_zpowers_of_cube (h : SettingCore b K z) {d : G} (hdb : d ∈ Cen b) (hdK : d ∈ CenS K)
    (hd3 : d ^ 3 = 1) : d ∈ Subgroup.zpowers b := by
  set P := Subgroup.zpowers d ⊔ Subgroup.zpowers b
  have hP : CFSG.Assembly.IsElemAbelian 3 P :=
    CFSG.Open.IsElemAbelian.sup_of_commute (CFSG.Open.isElemAbelian_zpowers hd3)
      (CFSG.Open.isElemAbelian_zpowers h.b_cube) (fun x hx y hy => by
        obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
        obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
        exact (Commute.zpow_zpow (Subgroup.mem_centralizer_singleton_iff.mp hdb) i j).eq)
  have hPK : P ≤ CenS K := sup_le (Subgroup.zpowers_le.mpr hdK) (Subgroup.zpowers_le.mpr h.b_mem_cenS)
  have := h.cyc P hPK hP.isPGroup
  have hbP : Subgroup.zpowers b ≤ P := le_sup_right
  have hcb : Nat.card (Subgroup.zpowers b) = 3 := by rw [Nat.card_zpowers, h.ord]
  have hEq : Subgroup.zpowers b = P := Subgroup.eq_of_le_of_card_ge hbP
    (by rw [hcb]; exact card_le_three_of_cyclic hP)
  rw [hEq]
  exact Subgroup.mem_sup_left (Subgroup.mem_zpowers d)

theorem cube_decomp (h : SettingCore b K z) {x : G} (hx : x ∈ Cen b) (hx3 : x ^ 3 = 1) :
    ∃ k ∈ K, k ^ 3 = 1 ∧ ∃ j : ℤ, x = k * b ^ j := by
  obtain ⟨k, hkK, hk⟩ := h.exists_inner hx hx3
  set d := k⁻¹ * x with hd
  have hdK : d ∈ CenS K := Subgroup.mem_centralizer_iff.mpr fun y hy => by
    have := hk y hy
    calc y * (k⁻¹ * x) = k⁻¹ * (k * y * k⁻¹) * x := by group
      _ = k⁻¹ * (x * y * x⁻¹) * x := by rw [this]
      _ = k⁻¹ * x * y := by group
  have hkd : Commute k d := (Subgroup.mem_centralizer_iff.mp hdK k hkK)
  have hxd : x = k * d := by rw [hd]; group
  have h3 : k ^ 3 * d ^ 3 = 1 := by rw [← hkd.mul_pow, ← hxd, hx3]
  have hk3 : k ^ 3 = 1 := by
    refine h.eq_one_of_mem (K.pow_mem hkK 3) fun y hy => ?_
    rw [eq_inv_of_mul_eq_one_left h3]
    exact (Subgroup.mem_centralizer_iff.mp ((CenS K).inv_mem ((CenS K).pow_mem hdK 3)) y hy).symm
  have hd3 : d ^ 3 = 1 := by rwa [hk3, one_mul] at h3
  have hdb : d ∈ Cen b := (Cen b).mul_mem ((Cen b).inv_mem (h.le hkK)) hx
  obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp (h.mem_zpowers_of_cube hdb hdK hd3)
  exact ⟨k, hkK, hk3, j, by rw [hj]; exact hxd⟩

theorem mem_nor_Bt {n : G} (hb : n * b * n⁻¹ ∈ Bt b z) (hz : ∀ i, n * zs z i * n⁻¹ ∈ Bt b z) :
    n ∈ Nor (Bt b z) := by
  rw [Bt_eq_closure]
  refine mem_nor_of_closure fun s hs => ?_
  rw [← Bt_eq_closure]
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
  rcases hs with rfl | rfl | rfl | rfl
  exacts [hb, hz 0, hz 1, hz 2]

theorem e81 (h : SettingCore b K z) {E : Subgroup G} (hEC : E ≤ Cen b)
    (hE : CFSG.Assembly.IsElemAbelian 3 E) (hcard : Nat.card E = 81) (hbE : b ∈ E) :
    ∃ k ∈ K, conjBy k (Bt b z) = E := by
  have hsub : (E : Set G) ⊆ ((E ⊓ K : Subgroup G) : Set G) * (Subgroup.zpowers b : Set G) := by
    intro x hx
    obtain ⟨k, hkK, -, j, rfl⟩ := h.cube_decomp (hEC hx) (hE.2 _ hx)
    refine ⟨k, ⟨?_, hkK⟩, b ^ j, Subgroup.zpow_mem_zpowers b j, rfl⟩
    have e : k = k * b ^ j * (b ^ j)⁻¹ := by group
    rw [e]
    exact E.mul_mem hx (E.inv_mem (E.zpow_mem hbE j))
  have hle27 : 27 ≤ Nat.card (E ⊓ K : Subgroup G) := by
    have h1 : Nat.card E ≤ Nat.card (E ⊓ K : Subgroup G) * 3 :=
      calc Nat.card E = Nat.card (E : Set G) := rfl
        _ ≤ Nat.card (((E ⊓ K : Subgroup G) : Set G) * (Subgroup.zpowers b : Set G)) :=
          Nat.card_mono (Set.toFinite _) hsub
        _ ≤ Nat.card ((E ⊓ K : Subgroup G) : Set G) * Nat.card (Subgroup.zpowers b : Set G) :=
          Set.natCard_mul_le
        _ = Nat.card (E ⊓ K : Subgroup G) * 3 := by
          rw [show Nat.card (Subgroup.zpowers b : Set G) = Nat.card (Subgroup.zpowers b) from rfl,
            Nat.card_zpowers, h.ord]
          rfl
    omega
  set F : Subgroup K := E.subgroupOf K
  have hFab : CFSG.Assembly.IsElemAbelian 3 F := hE.subgroupOf K
  have hFcard : Nat.card F = Nat.card (E ⊓ K : Subgroup G) := by
    rw [← Subgroup.card_map_of_injective K.subtype_injective, Subgroup.subgroupOf_map_subtype]
  have hF27 : Nat.card F = 27 := le_antisymm (h.model.rank F hFab) (hFcard ▸ hle27)
  obtain ⟨g, hg⟩ := h.model.torus F hFab hF27
  refine ⟨g, g.2, ?_⟩
  have hle : conjBy (g : G) (Bt b z) ≤ E := by
    rintro _ ⟨y, hy, rfl⟩
    obtain ⟨j, v, rfl⟩ := h.mem_Bt.mp hy
    have hv : (g : G) * vecElt (zs z) v * (g : G)⁻¹ ∈ E := by
      have hF : (g * vecElt z v * g⁻¹ : K) ∈ F := (hg _).mpr ⟨v, rfl⟩
      rw [Subgroup.mem_subgroupOf] at hF
      rw [vecElt_zs]
      exact hF
    have hgj : (g : G) * b ^ j * (g : G)⁻¹ = b ^ j := by
      rw [(Commute.zpow_right (h.comm_of_mem g.2) j).eq, mul_inv_cancel_right]
    have e : (MulAut.conj (g : G)).toMonoidHom (b ^ j * vecElt (zs z) v) =
        b ^ j * ((g : G) * vecElt (zs z) v * (g : G)⁻¹) := by
      simp only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe, MulAut.conj_apply]
      calc (g : G) * (b ^ j * vecElt (zs z) v) * (g : G)⁻¹ =
          ((g : G) * b ^ j * (g : G)⁻¹) * ((g : G) * vecElt (zs z) v * (g : G)⁻¹) := by group
        _ = _ := by rw [hgj]
    rw [e]
    exact E.mul_mem (E.zpow_mem hbE j) hv
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  rw [Subgroup.card_map_of_injective (MulAut.conj (g : G)).injective, h.card_Bt, hcard]

theorem fusion (h : SettingCore b K z) {g β : G} (hβ : β ∈ Bt b z) (hg : g * b * g⁻¹ = β) :
    ∃ n ∈ Nor (Bt b z), n * b * n⁻¹ = β := by
  set E := conjBy g⁻¹ (Bt b z)
  have hEab : CFSG.Assembly.IsElemAbelian 3 E := h.isElemAbelian_Bt.map _
  have hbE : b ∈ E := mem_conjBy.mpr (by rw [inv_inv, hg]; exact hβ)
  have hEC : E ≤ Cen b := fun x hx => Subgroup.mem_centralizer_singleton_iff.mpr (by
    simpa using congrArg Subtype.val (hEab.1.is_comm.comm ⟨x, hx⟩ ⟨b, hbE⟩))
  have hcard : Nat.card E = 81 := by
    rw [Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective, h.card_Bt]
  obtain ⟨k, hkK, hk⟩ := h.e81 hEC hEab hcard hbE
  refine ⟨g * k, mem_nor_of_conj_mem fun x hx => ?_, ?_⟩
  · have hx' : k * x * k⁻¹ ∈ E := by
      rw [← hk]
      exact mem_conjBy.mpr (by simpa [mul_assoc] using hx)
    have := mem_conjBy.mp hx'
    rw [inv_inv] at this
    simpa [mul_assoc] using this
  · rw [show g * k * b * (g * k)⁻¹ = g * (k * b * k⁻¹) * g⁻¹ by group, h.conj_b hkK, hg]

theorem nor_K (h : SettingCore b K z) {n : G} (hn : n ∈ Nor (Subgroup.zpowers b)) {k : G}
    (hk : k ∈ K) : n * k * n⁻¹ ∈ K := by
  have hn' : n⁻¹ ∈ Nor (Subgroup.zpowers b) := (Nor _).inv_mem hn
  have hK'C : ∀ x, n⁻¹ * x * n ∈ K → x ∈ Cen b := fun x hx => by
    have := conj_mem_cen hn' (h.le hx)
    simpa [mul_assoc] using this
  have hK'N : ∀ c ∈ Cen b, ∀ x, n⁻¹ * x * n ∈ K → n⁻¹ * (c * x * c⁻¹) * n ∈ K := fun c hc x hx => by
    have := h.nor _ (conj_mem_cen hn hc) _ hx
    rwa [show n⁻¹ * c * n * (n⁻¹ * x * n) * (n⁻¹ * c * n)⁻¹ = n⁻¹ * (c * x * c⁻¹) * n by group]
      at this
  set I : Subgroup K := (conjBy n K).subgroupOf K
  have hI : ∀ y : K, y ∈ I ↔ n⁻¹ * y * n ∈ K := fun y => by
    rw [Subgroup.mem_subgroupOf, mem_conjBy]
  have : I.Normal := ⟨fun y hy c => by
    rw [hI] at hy ⊢
    exact hK'N c (h.le c.2) y hy⟩
  have := h.model.simple
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal I with hbot | htop
  · exfalso
    have hcomm : ∀ x, n⁻¹ * x * n ∈ K → x ∈ CenS K := fun x hx =>
      Subgroup.mem_centralizer_iff.mpr fun y hy => by
        have hcK : y * x * y⁻¹ * x⁻¹ ∈ K := by
          rw [show y * x * y⁻¹ * x⁻¹ = y * (x * y⁻¹ * x⁻¹) by group]
          exact K.mul_mem hy (h.nor x (hK'C x hx) _ (K.inv_mem hy))
        have hcK' : n⁻¹ * (y * x * y⁻¹ * x⁻¹) * n ∈ K := by
          rw [show n⁻¹ * (y * x * y⁻¹ * x⁻¹) * n =
            (n⁻¹ * (y * x * y⁻¹) * n) * (n⁻¹ * x * n)⁻¹ by group]
          exact K.mul_mem (hK'N y (h.le hy) x hx) (K.inv_mem hx)
        have hmem : (⟨_, hcK⟩ : K) ∈ I := (hI _).mpr hcK'
        rw [hbot, Subgroup.mem_bot] at hmem
        have h1 : y * x * y⁻¹ * x⁻¹ = 1 := congrArg Subtype.val hmem
        rw [mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at h1
        exact h1
    set P := conjBy n (tor (zs z))
    have hPab : CFSG.Assembly.IsElemAbelian 3 P := (isElemAbelian_tor h.zs_pow h.zs_comm).map _
    have hPle : P ≤ CenS K := fun y hy => hcomm y (tor_le z (mem_conjBy.mp hy))
    have := h.cyc P hPle hPab.isPGroup
    have hP27 : Nat.card P = 27 := by
      rw [Subgroup.card_map_of_injective (MulAut.conj n).injective, h.card_torG]
    have := card_le_three_of_cyclic hPab
    omega
  · have hall : ∀ y ∈ K, n⁻¹ * y * n⁻¹⁻¹ ∈ K := fun y hy => by
      rw [inv_inv]
      exact (hI ⟨y, hy⟩).mp (htop ▸ Subgroup.mem_top _)
    simpa using inv_conj_mem_of_conj_mem hall hk

theorem tor_stable (h : SettingCore b K z) {n : G} (hn : n ∈ Nor (Bt b z))
    (hK : ∀ k ∈ K, n * k * n⁻¹ ∈ K) (v : Fin 3 → ZMod 3) :
    ∃ w, conjAut hK (vecElt z v) = vecElt z w := by
  have hB : n * vecElt (zs z) v * n⁻¹ ∈ Bt b z :=
    (Subgroup.mem_normalizer_iff.mp hn _).mp (tor_le_Bt b z (vecElt_mem_tor _ v))
  have hKm : n * vecElt (zs z) v * n⁻¹ ∈ K := hK _ (tor_le z (vecElt_mem_tor _ v))
  obtain ⟨w, hw⟩ := h.mem_torG.mp (h.mem_tor_of_mem_Bt hB hKm)
  refine ⟨w, Subtype.ext ?_⟩
  rw [conjAut_apply, ← vecElt_zs, hw, vecElt_zs]

theorem mem_nor_zpowers {n : G} (hn : conjBy n (Subgroup.zpowers b) = Subgroup.zpowers b) :
    n ∈ Nor (Subgroup.zpowers b) :=
  mem_nor_of_conj_mem fun x hx => by
    rw [← hn]
    exact mem_conjBy.mpr (by simpa [mul_assoc] using hx)

theorem stab (h : SettingCore b K z) : ∀ n ∈ Nor (Bt b z),
    conjBy n (Subgroup.zpowers b) = Subgroup.zpowers b →
      n * b * n⁻¹ ∈ ({b, b⁻¹} : Set G) ∧ ∀ x ∈ ({zs z 0, zs z 1, zs z 2} : Set G),
        n * x * n⁻¹ ∈ ({zs z 0, (zs z 0)⁻¹, zs z 1, (zs z 1)⁻¹, zs z 2, (zs z 2)⁻¹} : Set G) := by
  intro n hn hnb
  refine ⟨?_, ?_⟩
  · have hmem : n * b * n⁻¹ ∈ Subgroup.zpowers b := by
      rw [← hnb]
      exact mem_conjBy.mpr (by simp [mul_assoc])
    have hne : n * b * n⁻¹ ≠ 1 := fun h1 => h.b_ne_one (by
      rw [show b = n⁻¹ * (n * b * n⁻¹) * n by group, h1]
      group)
    rcases eq_or_eq_inv_of_mem_zpowers h.ord hmem hne with e | e
    · exact Or.inl e
    · exact Or.inr e
  · have hK : ∀ k ∈ K, n * k * n⁻¹ ∈ K := fun k hk => h.nor_K (mem_nor_zpowers hnb) hk
    have key : ∀ i, n * zs z i * n⁻¹ ∈
        ({zs z 0, (zs z 0)⁻¹, zs z 1, (zs z 1)⁻¹, zs z 2, (zs z 2)⁻¹} : Set G) := fun i => by
      obtain ⟨j, hj⟩ := h.model.mono_of_aut (conjAut hK) (h.tor_stable hn hK) i
      have hj' : n * zs z i * n⁻¹ = zs z j ∨ n * zs z i * n⁻¹ = (zs z j)⁻¹ := by
        rcases hj with e | e
        · exact Or.inl (congrArg Subtype.val e)
        · exact Or.inr (congrArg Subtype.val e)
      rcases (by decide : ∀ j : Fin 3, j = 0 ∨ j = 1 ∨ j = 2) j with rfl | rfl | rfl <;>
        rcases hj' with e | e <;> rw [e] <;> simp
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl
    exacts [key 0, key 1, key 2]

end SettingCore

namespace Setting

open SettingCore

variable {b : G} {K : Subgroup G} {z : Fin 3 → K} [Finite G]

theorem exists_inv (h : Setting b K z) : ∃ n ∈ Nor (Bt b z), n * b * n⁻¹ = b⁻¹ := by
  obtain ⟨g, hg⟩ := h.meet
  obtain ⟨c, hc⟩ := isConj_iff.mp (h.model.isConj_inv (h.cube_conj hg))
  have hc' : (c : G) * (g * b * g⁻¹) * (c : G)⁻¹ = (g * b * g⁻¹)⁻¹ := congrArg Subtype.val hc
  refine h.fusion ((Bt b z).inv_mem (b_mem_Bt b z)) (g := g⁻¹ * c * g) ?_
  calc g⁻¹ * c * g * b * (g⁻¹ * c * g)⁻¹ = g⁻¹ * ((c : G) * (g * b * g⁻¹) * (c : G)⁻¹) * g := by
        group
    _ = b⁻¹ := by rw [hc']; group

theorem meetB (h : Setting b K z) :
    ∃ n ∈ Nor (Bt b z), n * b * n⁻¹ ∈ Subgroup.closure {zs z 0, zs z 1, zs z 2} := by
  obtain ⟨g, hg⟩ := h.meet
  obtain ⟨c, v, hcv⟩ := h.model.fus _ (h.cube_conj hg)
  have hcv' : g * b * g⁻¹ = (c : G) * vecElt (zs z) v * (c : G)⁻¹ := by
    rw [vecElt_zs]
    exact congrArg Subtype.val hcv
  obtain ⟨n, hn, hnb⟩ := h.fusion (tor_le_Bt b z (vecElt_mem_tor _ v)) (g := (c : G)⁻¹ * g) (by
    rw [show (c : G)⁻¹ * g * b * ((c : G)⁻¹ * g)⁻¹ = (c : G)⁻¹ * (g * b * g⁻¹) * c by group, hcv']
    group)
  exact ⟨n, hn, by rw [hnb, ← tor_eq_closure]; exact vecElt_mem_tor _ v⟩

theorem exists_t0 (h : Setting b K z) :
    ∃ n ∈ Nor (Bt b z), n * b * n⁻¹ = b⁻¹ ∧ ∀ i, n * zs z i * n⁻¹ = zs z i := by
  obtain ⟨n₀, hn₀, hn₀b⟩ := h.exists_inv
  have hnb : n₀ ∈ Nor (Subgroup.zpowers b) := by
    rw [Subgroup.zpowers_eq_closure]
    refine mem_nor_of_closure fun s hs => ?_
    rw [Set.mem_singleton_iff] at hs
    subst hs
    rw [hn₀b, ← Subgroup.zpowers_eq_closure]
    exact (Subgroup.zpowers s).inv_mem (Subgroup.mem_zpowers s)
  have hK : ∀ k ∈ K, n₀ * k * n₀⁻¹ ∈ K := fun k hk => h.nor_K hnb hk
  obtain ⟨k, hk⟩ := h.model.exists_conj_of_aut (conjAut hK) (h.tor_stable hn₀ hK)
  have hk' : ∀ i, n₀ * zs z i * n₀⁻¹ = (k : G) * zs z i * (k : G)⁻¹ := fun i =>
    congrArg Subtype.val (hk i)
  have hkN : (k : G) ∈ Nor (Bt b z) := mem_nor_Bt (by rw [h.conj_b k.2]; exact b_mem_Bt b z)
    fun i => by
      rw [← hk']
      exact (Subgroup.mem_normalizer_iff.mp hn₀ _).mp (zs_mem_Bt b z i)
  refine ⟨(k : G)⁻¹ * n₀, (Nor _).mul_mem ((Nor _).inv_mem hkN) hn₀, ?_, fun i => ?_⟩
  · rw [show (k : G)⁻¹ * n₀ * b * ((k : G)⁻¹ * n₀)⁻¹ = ((k : G)⁻¹ * (n₀ * b * n₀⁻¹)⁻¹ * k)⁻¹ by
      group, hn₀b, inv_inv, show (k : G)⁻¹ * b * k = (k : G)⁻¹ * b * (k : G)⁻¹⁻¹ by rw [inv_inv],
      h.conj_b (K.inv_mem k.2)]
  · rw [show (k : G)⁻¹ * n₀ * zs z i * ((k : G)⁻¹ * n₀)⁻¹ = (k : G)⁻¹ * (n₀ * zs z i * n₀⁻¹) * k
      by group, hk']
    group

theorem exists_mono (h : Setting b K z) (σ : Equiv.Perm (Fin 3)) (ε : Fin 3 → ZMod 3)
    (hε : ∀ i, ε i ≠ 0) : ∃ n ∈ Nor (Bt b z), n * b * n⁻¹ = b ∧
      ∀ i, n * zs z i * n⁻¹ = zs z (σ i) ^ (ε i).val := by
  obtain ⟨k, hk⟩ := h.model.mono σ ε hε
  have hk' : ∀ i, (k : G) * zs z i * (k : G)⁻¹ = zs z (σ i) ^ (ε i).val := fun i =>
    congrArg Subtype.val (hk i)
  refine ⟨k, mem_nor_Bt (by rw [h.conj_b k.2]; exact b_mem_Bt b z) fun i => ?_, h.conj_b k.2, hk'⟩
  rw [hk']
  exact (Bt b z).pow_mem (zs_mem_Bt b z _) _

theorem hasH0 (h : Setting b K z) : HasH0 (Bt b z) b (zs z 0) (zs z 1) (zs z 2) := by
  refine ⟨⟨CFSG.Open.isElemAbelian_iff_isElementaryAbelian.mp h.isElemAbelian_Bt, ?_⟩,
    Bt_eq_closure b z, ?_, ?_, ?_, ?_⟩
  · rw [h.card_Bt]
    norm_num
  · obtain ⟨n, hn, hb, hz⟩ := h.exists_t0
    exact ⟨n, hn, hb, hz 0, hz 1, hz 2⟩
  · obtain ⟨n, hn, hb, hz⟩ := h.exists_mono 1 ![2, 1, 1] (by decide)
    exact ⟨n, hn, hb, (hz 0).trans (h.zs_sq 0), (hz 1).trans (zs_one z 1),
      (hz 2).trans (zs_one z 2)⟩
  · obtain ⟨n, hn, hb, hz⟩ := h.exists_mono (Equiv.swap 0 1) 1 (by decide)
    have e : ∀ i, n * zs z i * n⁻¹ = zs z (Equiv.swap 0 1 i) := fun i =>
      (hz i).trans (zs_one z _)
    refine ⟨n, hn, hb, e 0, e 1, e 2⟩
  · obtain ⟨n, hn, hb, hz⟩ := h.exists_mono (finRotate 3) 1 (by decide)
    have e : ∀ i, n * zs z i * n⁻¹ = zs z (finRotate 3 i) := fun i => (hz i).trans (zs_one z _)
    refine ⟨n, hn, hb, e 0, e 1, e 2⟩

end Setting

end CFSG.StandardType.GGFF

end
