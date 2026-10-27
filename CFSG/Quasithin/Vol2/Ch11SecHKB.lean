module

public import CFSG.Quasithin.Vol2.Ch11SecHTransport
import CFSG.GroupTheory.ElemAbelianClosure
public import CFSG.Quasithin.Vol2.Ch11SecHSet
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecH

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13 CFSG.Quasithin.InternalSec

variable {G : Type} [Group G]

theorem conjAct_apply_coe (W : Subgroup G) (x : ↥(Subgroup.normalizer (W : Set G))) (w : ↥W) :
    ((conjAct W x w : ↥W) : G) = (x : G) * w * (x : G)⁻¹ :=
  Subgroup.normalizerMonoidHom_apply_apply_coe W _ w

theorem conjAct_eq_one_iff (W : Subgroup G) (x : ↥(Subgroup.normalizer (W : Set G))) :
    conjAct W x = 1 ↔ (x : G) ∈ Subgroup.centralizer (W : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  constructor
  · intro h w hw
    have := congrArg (fun φ : MulAut ↥W => ((φ ⟨w, hw⟩ : ↥W) : G)) h
    simp only [conjAct_apply_coe, MulAut.one_apply] at this
    calc w * (x : G) = ((x : G) * w * (x : G)⁻¹) * x := by rw [this]
      _ = x * w := by group
  · intro h
    ext w
    rw [conjAct_apply_coe, MulAut.one_apply, ← h w w.2, mul_inv_cancel_right]

theorem comm_of_isElemAbelian {V : Subgroup G} (hV : IsElemAbelian 2 V) {a b : G} (ha : a ∈ V)
    (hb : b ∈ V) : a * b = b * a := CFSG.Open.IsElemAbelian.comm hV ha hb

variable [Finite G]

namespace Data

variable {T L I : Subgroup G} {n : ℕ} {V₁ H : Subgroup G} {g h y : G}
  (d : Data T L I n V₁ H g h y)
include d

theorem y_mem_K : y ∈ oTwoUpper H := mem_oTwoUpper_of_odd d.yH d.yodd

theorem y_mem_normalizer_V : y ∈ Subgroup.normalizer (fsuV T I : Set G) :=
  SecA.L_le_normalizer_fsuV d.c.s.hyp d.yL

theorem y_not_mem_centralizer (i : Inp32) : y ∉ Subgroup.centralizer (VZ T H : Set G) := by
  intro hy
  have hmem := d.c.centralizer_VZ_le i.h1135 i.h1136 ⟨d.yH, hy⟩
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H)) ⟨y, hmem⟩
  rw [Subgroup.orderOf_mk] at hk
  have hk0 : k = 0 := by
    by_contra hk0
    have : Even (orderOf y) := hk ▸ (Nat.even_pow' hk0).mpr even_two
    exact (Nat.not_even_iff_odd.mpr d.yodd) this
  rw [hk0, pow_zero, orderOf_eq_one_iff] at hk
  exact d.yne hk

theorem fpf (i : Inp32) {v : G} (hv : v ∈ fsuV T I)
    (hc : y * v * y⁻¹ * v⁻¹ ∈ Subgroup.centralizer (VZ T H : Set G)) :
    v ∈ Subgroup.centralizer (VZ T H : Set G) := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := d.kStar
  have hHN := SecC.le_normalizer_VZ T H
  set N := Subgroup.normalizer (VZ T H : Set G)
  have hyN : y ∈ N := hHN d.yH
  have hvN : v ∈ N := hHN (d.c.V_le_H hv)
  set ys := conjAct (VZ T H) ⟨y, hyN⟩
  have hysK : ys ∈ autOn (oTwoUpper H) (VZ T H) :=
    ⟨⟨y, hyN⟩, Subgroup.mem_subgroupOf.mpr d.y_mem_K, rfl⟩
  have hyV := d.y_mem_normalizer_V
  have hysN : ys ∈ Subgroup.normalizer
      (autOn (fsuV T I) (VZ T H) : Set (MulAut ↥(VZ T H))) := by
    rw [Subgroup.mem_normalizer_iff]
    intro σ
    constructor
    · rintro ⟨x, hx, rfl⟩
      refine ⟨⟨y, hyN⟩ * x * ⟨y, hyN⟩⁻¹, Subgroup.mem_subgroupOf.mpr ?_, by simp [ys]⟩
      exact (Subgroup.mem_normalizer_iff.mp hyV _).mp (Subgroup.mem_subgroupOf.mp hx)
    · rintro ⟨x, hx, hxe⟩
      refine ⟨⟨y, hyN⟩⁻¹ * x * ⟨y, hyN⟩, Subgroup.mem_subgroupOf.mpr ?_, ?_⟩
      · have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hyV) _).mp
          (Subgroup.mem_subgroupOf.mp hx)
        simpa using this
      · rw [map_mul, map_mul, hxe, map_inv]
        change ys⁻¹ * (ys * σ * ys⁻¹) * ys = σ
        group
  have hodd : Odd (orderOf ys) := d.yodd.of_dvd_nat
    ((orderOf_map_dvd (conjAct (VZ T H)) _).trans (by rw [Subgroup.orderOf_mk]))
  have hys1 : ys ≠ 1 := fun h1 =>
    d.y_not_mem_centralizer i ((conjAct_eq_one_iff (VZ T H) ⟨y, hyN⟩).mp h1)
  have hvs : conjAct (VZ T H) ⟨v, hvN⟩ ∈ autOn (fsuV T I) (VZ T H) :=
    ⟨⟨v, hvN⟩, Subgroup.mem_subgroupOf.mpr hv, rfl⟩
  have hcN : y * v * y⁻¹ * v⁻¹ ∈ N := N.mul_mem (N.mul_mem (N.mul_mem hyN hvN)
    (N.inv_mem hyN)) (N.inv_mem hvN)
  have h1 : conjAct (VZ T H) ⟨y * v * y⁻¹ * v⁻¹, hcN⟩ = 1 :=
    (conjAct_eq_one_iff (VZ T H) _).mpr hc
  have hcomm : ys * conjAct (VZ T H) ⟨v, hvN⟩ * ys⁻¹ = conjAct (VZ T H) ⟨v, hvN⟩ := by
    have h2 : (⟨y * v * y⁻¹ * v⁻¹, hcN⟩ : ↥N) = ⟨y, hyN⟩ * ⟨v, hvN⟩ * ⟨y, hyN⟩⁻¹ * ⟨v, hvN⟩⁻¹ :=
      rfl
    rw [h2, map_mul, map_mul, map_mul, map_inv, map_inv] at h1
    calc ys * conjAct (VZ T H) ⟨v, hvN⟩ * ys⁻¹ =
        (ys * conjAct (VZ T H) ⟨v, hvN⟩ * ys⁻¹ * (conjAct (VZ T H) ⟨v, hvN⟩)⁻¹) *
          conjAct (VZ T H) ⟨v, hvN⟩ := by group
      _ = conjAct (VZ T H) ⟨v, hvN⟩ := by rw [h1, one_mul]
  have := fpf_of_sylow i.hKF6 d.c.two_le hF e d.sylow hysK hysN hodd hys1 hvs hcomm
  exact (conjAct_eq_one_iff (VZ T H) ⟨v, hvN⟩).mp this

theorem exists_decomp (i : Inp32) {v : G} (hv : v ∈ fsuV T I) :
    ∃ k ∈ fsuV T I ⊓ oTwoUpper H, ∃ b ∈ fsuV T I ⊓ pCoreOf 2 H, v = k * b := by
  have hVab := SecA.isElemAbelian_fsuV d.c.s.hyp
  have hyV := d.y_mem_normalizer_V
  have hBeq := d.c.fsuV_inf_pCoreOf i.h1135 i.h1136
  have hyO : y ∈ Subgroup.normalizer (pCoreOf 2 H : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H d.yH
  have hf : ∀ x ∈ fsuV T I, y * x * y⁻¹ * x⁻¹ ∈ fsuV T I := fun x hx =>
    (fsuV T I).mul_mem ((Subgroup.mem_normalizer_iff.mp hyV x).mp hx) ((fsuV T I).inv_mem hx)
  let f : ↥(fsuV T I) →* ↥(fsuV T I) :=
    { toFun := fun x => ⟨y * x * y⁻¹ * x⁻¹, hf x x.2⟩
      map_one' := by ext; simp
      map_mul' := fun a b => by
        ext
        simp only [Subgroup.coe_mul]
        have hcm := comm_of_isElemAbelian hVab (hf b b.2) ((fsuV T I).inv_mem a.2)
        calc y * (a * b) * y⁻¹ * ((a : G) * b)⁻¹ =
            y * a * y⁻¹ * ((y * b * y⁻¹ * (b : G)⁻¹) * (a : G)⁻¹) := by group
          _ = y * a * y⁻¹ * ((a : G)⁻¹ * (y * b * y⁻¹ * (b : G)⁻¹)) := by rw [hcm]
          _ = y * a * y⁻¹ * (a : G)⁻¹ * (y * b * y⁻¹ * (b : G)⁻¹) := by group }
  have hNor : ((fsuV T I ⊓ pCoreOf 2 H).subgroupOf (fsuV T I)).Normal := by
    refine ⟨fun x hx z => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    have : ((z * x * z⁻¹ : ↥(fsuV T I)) : G) = x := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      rw [comm_of_isElemAbelian hVab z.2 x.2, mul_inv_cancel_right]
    rw [this]
    exact hx
  let F' := (QuotientGroup.mk' ((fsuV T I ⊓ pCoreOf 2 H).subgroupOf (fsuV T I))).comp f
  have hker : F'.ker = (fsuV T I ⊓ pCoreOf 2 H).subgroupOf (fsuV T I) := by
    ext x
    simp only [F', MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    constructor
    · intro hx
      have hc : y * x * y⁻¹ * (x : G)⁻¹ ∈ Subgroup.centralizer (VZ T H : Set G) := by
        rw [hBeq] at hx
        exact hx.2
      rw [hBeq]
      exact ⟨x.2, d.fpf i x.2 hc⟩
    · intro hx
      refine ⟨hf x x.2, (pCoreOf 2 H).mul_mem ?_ ((pCoreOf 2 H).inv_mem hx.2)⟩
      exact (Subgroup.mem_normalizer_iff.mp hyO x).mp hx.2
  have hrange : F'.range = ⊤ := by
    apply Subgroup.eq_top_of_card_eq
    have h1 : Nat.card F'.range = F'.ker.index :=
      (Nat.card_congr (QuotientGroup.quotientKerEquivRange F').toEquiv).symm
    rw [hker] at h1
    exact h1
  obtain ⟨x, hx⟩ : (QuotientGroup.mk' ((fsuV T I ⊓ pCoreOf 2 H).subgroupOf (fsuV T I))
      ⟨v, hv⟩) ∈ F'.range := hrange ▸ Subgroup.mem_top _
  simp only [F', MonoidHom.comp_apply, QuotientGroup.mk'_apply] at hx
  have hb := Subgroup.mem_subgroupOf.mp (QuotientGroup.eq.mp hx)
  have hxK : y * x * y⁻¹ * (x : G)⁻¹ ∈ oTwoUpper H := by
    rw [mul_assoc (y * x)]
    rw [mul_assoc]
    refine (oTwoUpper H).mul_mem d.y_mem_K ?_
    have := (Subgroup.mem_normalizer_iff.mp (le_normalizer_oTwoUpper H (d.c.V_le_H x.2)) y⁻¹).mp
      ((oTwoUpper H).inv_mem d.y_mem_K)
    simpa [mul_assoc] using this
  refine ⟨y * x * y⁻¹ * (x : G)⁻¹, ⟨hf x x.2, hxK⟩, (y * x * y⁻¹ * (x : G)⁻¹)⁻¹ * v, ?_,
    by group⟩
  have hfx : ((f x : ↥(fsuV T I)) : G) = y * x * y⁻¹ * (x : G)⁻¹ := rfl
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, hfx] at hb
  exact hb

end Data

end CFSG.Quasithin.Vol2.Ch11.SecH
