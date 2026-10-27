module

public import CFSG.LocalAnalysis.StandardType.FS81.E7FrameAssemble
public import CFSG.LocalAnalysis.StandardType.FS81.E7FrameJ0
public import CFSG.LocalAnalysis.StandardType.FS81.E7FrameTrans
public import CFSG.Mathlib.GroupTheory.NormalSimpleProj
public import CFSG.GroupTheory.CommutingProductFixedSubgroup

public noncomputable section

namespace CFSG.StandardType.FrameRoute.FS81.E7Frame

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.ClassicalInvolution.WeakCT
open CFSG.Timmesfeld

variable {G : Type} [Group G] {K : Subgroup G}

theorem coe_mem_tr_iff (ψ : ↥L7 ≃* ↥K) {X : Subgroup (ModGL .E7 (ZMod 2))} (y : ↥L7) :
    ((ψ y : ↥K) : G) ∈ tr ψ X ↔ (y : ModGL .E7 (ZMod 2)) ∈ X := by
  constructor
  · intro h
    obtain ⟨y', hy', he⟩ := mem_tr.mp h
    have : y' = y := ψ.injective (Subtype.ext he)
    rwa [← this]
  · intro h
    exact mem_tr.mpr ⟨y, h, rfl⟩

theorem exists_eq_psi (ψ : ↥L7 ≃* ↥K) {x : G} (hx : x ∈ K) : ∃ y : ↥L7, ((ψ y : ↥K) : G) = x :=
  ⟨ψ.symm ⟨x, hx⟩, by rw [MulEquiv.apply_symm_apply]⟩

theorem psi_commute_iff (ψ : ↥L7 ≃* ↥K) (y y' : ↥L7) :
    ((ψ y : ↥K) : G) * ((ψ y' : ↥K) : G) = ((ψ y' : ↥K) : G) * ((ψ y : ↥K) : G) ↔
      (y : ModGL .E7 (ZMod 2)) * y' = y' * y := by
  constructor
  · intro h
    have h1 : ψ (y * y') = ψ (y' * y) := by
      apply Subtype.ext
      simpa only [map_mul, Subgroup.coe_mul] using h
    exact congrArg Subtype.val (ψ.injective h1)
  · intro h
    have h1 : y * y' = y' * y := Subtype.ext h
    have h2 := congrArg (fun w => ((ψ w : ↥K) : G)) h1
    simpa only [map_mul, Subgroup.coe_mul] using h2

theorem tr_map_conj (ψ : ↥L7 ≃* ↥K) (y : ↥L7) (X : Subgroup (ModGL .E7 (ZMod 2))) :
    (tr ψ X).map (MulAut.conj ((ψ y : ↥K) : G)).toMonoidHom =
      tr ψ (X.map (MulAut.conj (y : ModGL .E7 (ZMod 2))).toMonoidHom) := by
  ext w
  constructor
  · rintro ⟨_, hx, rfl⟩
    obtain ⟨x, hxX, rfl⟩ := mem_tr.mp hx
    refine mem_tr.mpr ⟨y * x * y⁻¹, ⟨x, hxX, rfl⟩, ?_⟩
    simp only [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv, MulEquiv.coe_toMonoidHom,
      MulAut.conj_apply]
  · intro hw
    obtain ⟨x', hx', rfl⟩ := mem_tr.mp hw
    obtain ⟨u, huX, hu⟩ := hx'
    have hu' : u = ((y⁻¹ * x' * y : ↥L7) : ModGL .E7 (ZMod 2)) := by
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hu
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, ← hu]
      group
    refine ⟨((ψ (y⁻¹ * x' * y) : ↥K) : G), mem_tr.mpr ⟨_, hu' ▸ huX, rfl⟩, ?_⟩
    simp only [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv, MulEquiv.coe_toMonoidHom,
      MulAut.conj_apply]
    group

theorem orderOf_z {B : Basis3 G 8} (ψ : ↥L7 ≃* ↥K) {z : ↥L7}
    (hψz : ((ψ z : ↥K) : G) = B.b 1) : orderOf (z : ModGL .E7 (ZMod 2)) = 3 := by
  rw [Subgroup.orderOf_coe, ← MulEquiv.orderOf_eq ψ, ← Subgroup.orderOf_coe, hψz, B.ord 1]

theorem mem_normalizer_of_forall_commute {H : Subgroup G} {g : G}
    (h : ∀ x ∈ H, g * x = x * g) : g ∈ Subgroup.normalizer (H : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    rw [h x hx, mul_inv_cancel_right]
    exact hx
  · intro hx
    have hy := h _ hx
    have h1 : g * x * g⁻¹ = x := by
      calc g * x * g⁻¹ = g⁻¹ * (g * (g * x * g⁻¹)) := by group
        _ = g⁻¹ * ((g * x * g⁻¹) * g) := by rw [hy]
        _ = x := by group
    rwa [h1] at hx

theorem commute_of_mem_zpowers {x y w : G} (hxy : x * y = y * x)
    (hw : w ∈ Subgroup.zpowers y) : x * w = w * x := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
  exact (Commute.zpow_right (show Commute x y from hxy) k).eq

theorem map_conj_map_conj (X : Subgroup G) (a b : G) :
    (X.map (MulAut.conj a).toMonoidHom).map (MulAut.conj b).toMonoidHom =
      X.map (MulAut.conj (b * a)).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1
  ext x
  simp only [MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom, Function.comp_apply, MulAut.conj_apply]
  group

theorem conj_mem_normalizer_of_map {Y Y' : Subgroup G} {n p : G}
    (hY : Y.map (MulAut.conj n).toMonoidHom = Y')
    (hp : p ∈ Subgroup.normalizer (Y : Set G)) :
    n * p * n⁻¹ ∈ Subgroup.normalizer (Y' : Set G) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  change Y'.map (MulAut.conj (n * p * n⁻¹)).toMonoidHom = Y'
  have hp' : Y.map (MulAut.conj p).toMonoidHom = Y := Subgroup.mem_normalizer_iff_map_conj_eq.mp hp
  rw [← hY, map_conj_map_conj, show n * p * n⁻¹ * n = n * p by group, ← map_conj_map_conj, hp']

theorem conj_mem_centralizer_of_map {Y Y' : Subgroup G} {n p : G}
    (hY : Y.map (MulAut.conj n).toMonoidHom = Y')
    (hp : p ∈ Subgroup.centralizer (Y : Set G)) :
    n * p * n⁻¹ ∈ Subgroup.centralizer (Y' : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  rw [← hY] at hy
  obtain ⟨y', hy', rfl⟩ := hy
  have h := Subgroup.mem_centralizer_iff.mp hp y' hy'
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  calc n * y' * n⁻¹ * (n * p * n⁻¹) = n * (y' * p) * n⁻¹ := by group
    _ = n * (p * y') * n⁻¹ := by rw [h]
    _ = n * p * n⁻¹ * (n * y' * n⁻¹) := by group

theorem mem_normalizer_of_conj_mem [Finite G] {H : Subgroup G} {g : G}
    (h : ∀ x ∈ H, g * x * g⁻¹ ∈ H) : g ∈ Subgroup.normalizer (H : Set G) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  change H.map (MulAut.conj g).toMonoidHom = H
  refine Subgroup.eq_of_le_of_card_ge ?_ ?_
  · rintro _ ⟨x, hx, rfl⟩
    exact h x hx
  · rw [Subgroup.card_map_of_injective (MulAut.conj g).injective]

theorem zpowers_map_conj (x n : G) :
    (Subgroup.zpowers x).map (MulAut.conj n).toMonoidHom = Subgroup.zpowers (n * x * n⁻¹) := by
  rw [MonoidHom.map_zpowers]
  rfl

section Native

theorem tr_M0_le_centralizer (ψ : ↥L7 ≃* ↥K) {z : ↥L7} (hz : (z : ModGL .E7 (ZMod 2)) ∈ Jn 0) :
    tr ψ M0 ≤ Subgroup.centralizer ({((ψ z : ↥K) : G)} : Set G) := by
  intro w hw
  obtain ⟨m, hm, rfl⟩ := mem_tr.mp hw
  rw [Subgroup.mem_centralizer_singleton_iff]
  exact (psi_commute_iff ψ m z).mpr (Subgroup.mem_centralizer_iff.mp hm.2 _ hz).symm

theorem tr_jn0_le_centralizer (ψ : ↥L7 ≃* ↥K) :
    tr ψ (Jn 0) ≤ Subgroup.centralizer (tr ψ M0 : Set G) := by
  intro w hw
  obtain ⟨j, hj, rfl⟩ := mem_tr.mp hw
  rw [Subgroup.mem_centralizer_iff]
  intro v hv
  obtain ⟨m, hm, rfl⟩ := mem_tr.mp hv
  exact (psi_commute_iff ψ m j).mpr (Subgroup.mem_centralizer_iff.mp hm.2 _ hj).symm

theorem inf_centralizer_le_tr_jn0 (hC : E7NatCent) (ψ : ↥L7 ≃* ↥K) :
    K ⊓ Subgroup.centralizer (tr ψ M0 : Set G) ≤ tr ψ (Jn 0) := by
  intro w ⟨hwK, hwC⟩
  obtain ⟨y, rfl⟩ := exists_eq_psi ψ hwK
  rw [coe_mem_tr_iff, ← hC.1]
  refine ⟨y.2, Subgroup.mem_centralizer_iff.mpr fun m hm => ?_⟩
  have h := Subgroup.mem_centralizer_iff.mp hwC _ ((coe_mem_tr_iff ψ ⟨m, hm.1⟩).mpr hm)
  exact (psi_commute_iff ψ ⟨m, hm.1⟩ y).mp h

theorem tr_jn0_eq_one_of_central (hF : E7NatFrame) (ψ : ↥L7 ≃* ↥K) {w : G}
    (hw : w ∈ tr ψ (Jn 0)) (hc : ∀ v ∈ tr ψ (Jn 0), w * v = v * w) : w = 1 := by
  obtain ⟨y, hy, rfl⟩ := mem_tr.mp hw
  have : (y : ModGL .E7 (ZMod 2)) = 1 := by
    refine jn0_eq_one_of_central hF hy fun h hh => ?_
    have hhL : h ∈ L7 := hF.1 0 hh
    exact (psi_commute_iff ψ y ⟨h, hhL⟩).mp (hc _ ((coe_mem_tr_iff ψ ⟨h, hhL⟩).mpr hh))
  have hy1 : y = 1 := Subtype.ext this
  rw [hy1, map_one, Subgroup.coe_one]

theorem tr_m0_eq_one_of_central (hF : E7NatFrame) (hH : E7NatHigh) (hC : E7NatCent)
    (ψ : ↥L7 ≃* ↥K) {w : G} (hw : w ∈ tr ψ M0) (hc : ∀ v ∈ tr ψ M0, w * v = v * w) : w = 1 := by
  obtain ⟨y, hy, rfl⟩ := mem_tr.mp hw
  have : (y : ModGL .E7 (ZMod 2)) = 1 := by
    refine m0_eq_one_of_central hF hH hC hy fun h hh => ?_
    exact (psi_commute_iff ψ y ⟨h, hh.1⟩).mp (hc _ ((coe_mem_tr_iff ψ ⟨h, hh.1⟩).mpr hh))
  have hy1 : y = 1 := Subtype.ext this
  rw [hy1, map_one, Subgroup.coe_one]

theorem exists_zpow_mul_of_commute (hC : E7NatCent) (ψ : ↥L7 ≃* ↥K) {z : ↥L7}
    (hz : (z : ModGL .E7 (ZMod 2)) ∈ Jn 0) (hz3 : orderOf (z : ModGL .E7 (ZMod 2)) = 3)
    {κ : G} (hκ : κ ∈ K) (hcomm : κ * ((ψ z : ↥K) : G) = ((ψ z : ↥K) : G) * κ) :
    ∃ i : ℤ, ∃ m ∈ tr ψ M0, κ = ((ψ z : ↥K) : G) ^ i * m := by
  obtain ⟨y, rfl⟩ := exists_eq_psi ψ hκ
  have hyz : (y : ModGL .E7 (ZMod 2)) * z = z * y := (psi_commute_iff ψ y z).mp hcomm
  have hyC : (y : ModGL .E7 (ZMod 2)) ∈
      L7 ⊓ Subgroup.centralizer ({(z : ModGL .E7 (ZMod 2))} : Set (ModGL .E7 (ZMod 2))) :=
    ⟨y.2, Subgroup.mem_centralizer_singleton_iff.mpr hyz⟩
  rw [hC.2.1 _ hz hz3] at hyC
  obtain ⟨u, hu, m, hm, hum⟩ := CFSG.GroupTheory.exists_mul_of_mem_sup_of_commute
    (A := Subgroup.zpowers (z : ModGL .E7 (ZMod 2))) (B := M0)
    (fun a ha b hb => Subgroup.mem_centralizer_iff.mp hb.2 a
      ((Subgroup.zpowers_le.mpr hz) ha)) hyC
  obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hu
  refine ⟨i, ((ψ ⟨m, hm.1⟩ : ↥K) : G), (coe_mem_tr_iff ψ _).mpr hm, ?_⟩
  have hy : y = z ^ i * ⟨m, hm.1⟩ := Subtype.ext (by
    rw [Subgroup.coe_mul, Subgroup.coe_zpow, hum])
  rw [hy, map_mul, map_zpow, Subgroup.coe_mul, Subgroup.coe_zpow]

end Native

section Swap

variable [Finite G] {b₀ : G} {E : Subgroup G}

theorem le_normalizer_M (hstd : StdAssumptions b₀ K E Row.E7) {B : Basis3 G 8}
    (hB : Adapted B b₀ K E) (hC : E7NatCent) (ψ : ↥L7 ≃* ↥K) {z : ↥L7}
    (hz : (z : ModGL .E7 (ZMod 2)) ∈ Jn 0) (hψz : ((ψ z : ↥K) : G) = B.b 1)
    (hOut : Subgroup.normalizer (K : Set G) ≤ K ⊔ Subgroup.centralizer (K : Set G)) :
    Subgroup.centralizer ({b₀} : Set G) ⊓ Subgroup.centralizer ({B.b 1} : Set G) ≤
      Subgroup.normalizer (tr ψ M0 : Set G) := by
  have hKC : K ≤ Subgroup.centralizer ({b₀} : Set G) := hstd.2.1.1.2.1
  have hCK : Subgroup.centralizer ({b₀} : Set G) ≤ Subgroup.normalizer (K : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKC).mp hstd.2.1.1.2.2.1
  have hb₁K : B.b 1 ∈ K := hB.2.2 1 (by decide)
  intro x hx
  obtain ⟨κ, hκ, c, hc, rfl⟩ := CFSG.GroupTheory.exists_mul_of_mem_sup_of_commute
    (fun a ha b hb => Subgroup.mem_centralizer_iff.mp hb a ha) (hOut (hCK hx.1))
  have hcb : c * B.b 1 = B.b 1 * c := (Subgroup.mem_centralizer_iff.mp hc _ hb₁K).symm
  have hxb : κ * c * B.b 1 = B.b 1 * (κ * c) := Subgroup.mem_centralizer_singleton_iff.mp hx.2
  have hκb : κ * B.b 1 = B.b 1 * κ := by
    calc κ * B.b 1 = κ * c * B.b 1 * c⁻¹ := by rw [mul_assoc κ c, hcb]; group
      _ = B.b 1 * κ := by rw [hxb]; group
  obtain ⟨i, m, hm, rfl⟩ := exists_zpow_mul_of_commute hC ψ hz (orderOf_z ψ hψz) hκ
    (hψz ▸ hκb)
  have hzM : ((ψ z : ↥K) : G) ∈ Subgroup.normalizer (tr ψ M0 : Set G) :=
    mem_normalizer_of_forall_commute fun y hy =>
      (Subgroup.mem_centralizer_singleton_iff.mp (tr_M0_le_centralizer ψ hz hy)).symm
  have hcM : c ∈ Subgroup.normalizer (tr ψ M0 : Set G) :=
    mem_normalizer_of_forall_commute fun y hy =>
      (Subgroup.mem_centralizer_iff.mp hc y (tr_le_K ψ M0 hy)).symm
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.zpow_mem _ hzM i)
    (Subgroup.le_normalizer hm)) hcM

theorem conj_M_eq (hstd : StdAssumptions b₀ K E Row.E7) {B : Basis3 G 8}
    (hB : Adapted B b₀ K E) (hF : E7NatFrame) (hH : E7NatHigh) (hC : E7NatCent)
    (ψ : ↥L7 ≃* ↥K) {z : ↥L7} (hz : (z : ModGL .E7 (ZMod 2)) ∈ Jn 0)
    (hψz : ((ψ z : ↥K) : G) = B.b 1)
    (hOut : Subgroup.normalizer (K : Set G) ≤ K ⊔ Subgroup.centralizer (K : Set G))
    {n : G} (hnE : n ∈ Subgroup.normalizer (B.span : Set G)) (hn1 : n * B.b 1 * n⁻¹ = b₀)
    (hn0 : Subgroup.zpowers (n * b₀ * n⁻¹) = Subgroup.zpowers (B.b 1)) :
    (tr ψ M0).map (MulAut.conj n).toMonoidHom = tr ψ M0 := by
  classical
  have hKC : K ≤ Subgroup.centralizer ({b₀} : Set G) := hstd.2.1.1.2.1
  let D := Subgroup.centralizer ({b₀} : Set G) ⊓ Subgroup.centralizer ({B.b 1} : Set G)
  have hMD : tr ψ M0 ≤ D :=
    le_inf ((tr_le_K ψ M0).trans hKC) (hψz ▸ tr_M0_le_centralizer ψ hz)
  have hDM : D ≤ Subgroup.normalizer (tr ψ M0 : Set G) := le_normalizer_M hstd hB hC ψ hz hψz hOut
  have hb₁mem : B.b 1 ∈ Subgroup.zpowers (n * b₀ * n⁻¹) := hn0 ▸ Subgroup.mem_zpowers _
  have hb₀mem : b₀ ∈ Subgroup.zpowers (n⁻¹ * B.b 1 * n) := by
    have h := congrArg (fun H : Subgroup G => H.map (MulAut.conj n⁻¹).toMonoidHom) hn0
    simp only [MonoidHom.map_zpowers, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv] at h
    rw [← h]
    have : n⁻¹ * (n * b₀ * n⁻¹) * n = b₀ := by group
    rw [this]
    exact Subgroup.mem_zpowers _
  have hnD : ∀ d ∈ D, n * d * n⁻¹ ∈ D := by
    intro d hd
    have hd0 : d * b₀ = b₀ * d := Subgroup.mem_centralizer_singleton_iff.mp hd.1
    have hd1 : d * B.b 1 = B.b 1 * d := Subgroup.mem_centralizer_singleton_iff.mp hd.2
    refine ⟨Subgroup.mem_centralizer_singleton_iff.mpr ?_,
      Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
    · rw [← hn1]
      calc n * d * n⁻¹ * (n * B.b 1 * n⁻¹) = n * (d * B.b 1) * n⁻¹ := by group
        _ = n * (B.b 1 * d) * n⁻¹ := by rw [hd1]
        _ = n * B.b 1 * n⁻¹ * (n * d * n⁻¹) := by group
    · refine commute_of_mem_zpowers ?_ hb₁mem
      calc n * d * n⁻¹ * (n * b₀ * n⁻¹) = n * (d * b₀) * n⁻¹ := by group
        _ = n * (b₀ * d) * n⁻¹ := by rw [hd0]
        _ = n * b₀ * n⁻¹ * (n * d * n⁻¹) := by group
  have hnD' : ∀ d ∈ D, n⁻¹ * d * n ∈ D := by
    intro d hd
    have hd0 : d * b₀ = b₀ * d := Subgroup.mem_centralizer_singleton_iff.mp hd.1
    have hd1 : d * B.b 1 = B.b 1 * d := Subgroup.mem_centralizer_singleton_iff.mp hd.2
    have hb₁ : B.b 1 = n⁻¹ * b₀ * n := by rw [← hn1]; group
    refine ⟨Subgroup.mem_centralizer_singleton_iff.mpr ?_,
      Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
    · refine commute_of_mem_zpowers ?_ hb₀mem
      calc n⁻¹ * d * n * (n⁻¹ * B.b 1 * n) = n⁻¹ * (d * B.b 1) * n := by group
        _ = n⁻¹ * (B.b 1 * d) * n := by rw [hd1]
        _ = n⁻¹ * B.b 1 * n * (n⁻¹ * d * n) := by group
    · rw [hb₁]
      calc n⁻¹ * d * n * (n⁻¹ * b₀ * n) = n⁻¹ * (d * b₀) * n := by group
        _ = n⁻¹ * (b₀ * d) * n := by rw [hd0]
        _ = n⁻¹ * b₀ * n * (n⁻¹ * d * n) := by group
  let N : Subgroup G := (tr ψ M0).map (MulAut.conj n).toMonoidHom
  have hND : N ≤ D := by
    rintro _ ⟨m, hm, rfl⟩
    exact hnD m (hMD hm)
  have hDN : D ≤ Subgroup.normalizer (N : Set G) := by
    intro d hd
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    change N.map (MulAut.conj d).toMonoidHom = N
    have hd' := Subgroup.mem_normalizer_iff_map_conj_eq.mp (hDM (hnD' d hd))
    change (tr ψ M0).map (MulAut.conj (n⁻¹ * d * n)).toMonoidHom = tr ψ M0 at hd'
    calc N.map (MulAut.conj d).toMonoidHom
        = (tr ψ M0).map (MulAut.conj (d * n)).toMonoidHom := map_conj_map_conj _ _ _
      _ = (tr ψ M0).map (MulAut.conj (n * (n⁻¹ * d * n))).toMonoidHom := by congr 2; group
      _ = ((tr ψ M0).map (MulAut.conj (n⁻¹ * d * n)).toMonoidHom).map
            (MulAut.conj n).toMonoidHom := (map_conj_map_conj _ _ _).symm
      _ = N := by rw [hd']
  have hNsimple : IsSimpleGroup ↥N := by
    have : IsSimpleGroup ↥M0 := hC.2.2.1
    let e1 : ↥(tr ψ M0) ≃* ↥N :=
      (tr ψ M0).equivMapOfInjective (MulAut.conj n).toMonoidHom (MulAut.conj n).injective
    let e2 : ↥(M0.subgroupOf L7) ≃* ↥(tr ψ M0) :=
      (M0.subgroupOf L7).equivMapOfInjective (K.subtype.comp ψ.toMonoidHom)
        (K.subtype_injective.comp ψ.injective)
    let e3 : ↥(M0.subgroupOf L7) ≃* ↥M0 := Subgroup.subgroupOfEquivOfLe inf_le_left
    exact MulEquiv.isSimpleGroup (e1.symm.trans (e2.symm.trans e3))
  have hcard : Nat.card ↥N = Nat.card ↥(tr ψ M0) :=
    Subgroup.card_map_of_injective (MulAut.conj n).injective
  have hc : ¬ N ≤ Subgroup.centralizer (tr ψ M0 : Set G) := by
    intro hNC
    have hspan : B.span = E := hB.1
    have hEea : CFSG.Open.IsElemAbelian 3 E := hstd.2.1.2.1.2.1
    have hcommE : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a := fun a ha b hb =>
      congrArg Subtype.val (hEea.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
    have hb₁E : B.b 1 ∈ E := hspan ▸ B.b_mem_span 1
    let A₀ : Subgroup G := E ⊓ tr ψ M0
    have hAle : Nat.card ↥(E ⊓ K) ≤ 3 * Nat.card ↥A₀ := by
      have hdec : ∀ a : ↥(E ⊓ K), ∃ p : ↥(Subgroup.zpowers (B.b 1)) × ↥A₀,
          (p.1 : G) * p.2 = a := by
        rintro ⟨a, haE, haK⟩
        have hab : a * B.b 1 = B.b 1 * a := hcommE a haE _ hb₁E
        obtain ⟨i, m, hm, ham⟩ :=
          exists_zpow_mul_of_commute hC ψ hz (orderOf_z ψ hψz) haK (hψz ▸ hab)
        rw [hψz] at ham
        have hmE : m ∈ E := by
          have : m = (B.b 1 ^ i)⁻¹ * a := by rw [ham]; group
          rw [this]
          exact E.mul_mem (E.inv_mem (E.zpow_mem hb₁E i)) haE
        exact ⟨(⟨B.b 1 ^ i, Subgroup.zpow_mem_zpowers _ i⟩, ⟨m, hmE, hm⟩), ham.symm⟩
      choose f hf using hdec
      have hfinj : Function.Injective f := fun a a' h => Subtype.ext (by rw [← hf a, ← hf a', h])
      calc Nat.card ↥(E ⊓ K) ≤ Nat.card (↥(Subgroup.zpowers (B.b 1)) × ↥A₀) :=
            Nat.card_le_card_of_injective f hfinj
        _ = 3 * Nat.card ↥A₀ := by rw [Nat.card_prod, Nat.card_zpowers, B.ord 1]
    let X : Subgroup G := A₀.map (MulAut.conj n).toMonoidHom
    have hXE : X ≤ E := by
      rintro _ ⟨a, ha, rfl⟩
      have haS : a ∈ B.span := by rw [hspan]; exact ha.1
      have h := (Subgroup.mem_normalizer_iff.mp hnE a).mp haS
      rw [hspan] at h
      exact h
    have hXC : X ≤ Subgroup.centralizer (tr ψ M0 : Set G) := fun x hx =>
      hNC (Subgroup.map_mono inf_le_right hx)
    have hXA : ∀ x ∈ X, x ∈ A₀ → x = 1 := fun x hx hxA =>
      tr_m0_eq_one_of_central hF hH hC ψ hxA.2
        (fun v hv => (Subgroup.mem_centralizer_iff.mp (hXC hx) v hv).symm)
    have hXAle : Nat.card ↥X * Nat.card ↥A₀ ≤ Nat.card ↥E := by
      let g : ↥X × ↥A₀ → ↥E := fun p => ⟨(p.1 : G) * p.2, E.mul_mem (hXE p.1.2) p.2.2.1⟩
      have hginj : Function.Injective g := by
        rintro ⟨x, a⟩ ⟨x', a'⟩ h
        have h' : (x : G) * a = x' * a' := congrArg Subtype.val h
        have h1 : (x' : G)⁻¹ * x = a' * (a : G)⁻¹ := by
          calc (x' : G)⁻¹ * x = (x' : G)⁻¹ * (x * a) * (a : G)⁻¹ := by group
            _ = (x' : G)⁻¹ * (x' * a') * (a : G)⁻¹ := by rw [h']
            _ = a' * (a : G)⁻¹ := by group
        have h2 : (x' : G)⁻¹ * x = 1 :=
          hXA _ (X.mul_mem (X.inv_mem x'.2) x.2) (h1 ▸ A₀.mul_mem a'.2 (A₀.inv_mem a.2))
        have hx : (x : G) = x' := by
          calc (x : G) = x' * ((x' : G)⁻¹ * x) := by group
            _ = x' := by rw [h2, mul_one]
        have ha : (a : G) = a' := by
          rw [hx] at h'
          exact mul_left_cancel h'
        exact Prod.ext (Subtype.ext hx) (Subtype.ext ha)
      rw [← Nat.card_prod]
      exact Nat.card_le_card_of_injective g hginj
    have hXcard : Nat.card ↥X = Nat.card ↥A₀ :=
      Subgroup.card_map_of_injective (MulAut.conj n).injective
    have hEcard : Nat.card ↥E = 3 ^ 8 := hstd.2.1.2.2.2.1
    have hAcard : Nat.card ↥(E ⊓ K) = 3 ^ 7 := hstd.2.2.2.2.2.2.1
    rw [hXcard, hEcard] at hXAle
    rw [hAcard] at hAle
    nlinarith
  exact CFSG.GroupTheory.eq_of_normal_of_not_le_centralizer hND hMD hDN hDM hNsimple hcard hc

theorem tr_jn0_le_normalizer_zpowers (hF : E7NatFrame) (ψ : ↥L7 ≃* ↥K) {z : ↥L7}
    (hz : (z : ModGL .E7 (ZMod 2)) ∈ Jn 0) (hz3 : orderOf (z : ModGL .E7 (ZMod 2)) = 3) :
    tr ψ (Jn 0) ≤ Subgroup.normalizer (Subgroup.zpowers ((ψ z : ↥K) : G) : Set G) := by
  intro j hj
  obtain ⟨y, hy, rfl⟩ := mem_tr.mp hj
  refine mem_normalizer_of_conj_mem fun w hw => ?_
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
  have hyz := jn0_conj_mem hF hz hz3 hy
  obtain ⟨l, hl⟩ := Subgroup.mem_zpowers_iff.mp hyz
  refine ⟨l * k, ?_⟩
  have hl' : ((ψ (y * z * y⁻¹) : ↥K) : G) = ((ψ z : ↥K) : G) ^ l := by
    have : y * z * y⁻¹ = z ^ l := Subtype.ext (by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_zpow, hl])
    rw [this, map_zpow, Subgroup.coe_zpow]
  simp only [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv] at hl'
  show ((ψ z : ↥K) : G) ^ (l * k) = _
  rw [zpow_mul, ← hl', conj_zpow]

omit [Finite G] in
theorem le_centralizer_of_commute_tr_jn0 (hF : E7NatFrame) (hC : E7NatCent) (ψ : ↥L7 ≃* ↥K)
    (hOut : Subgroup.normalizer (K : Set G) ≤ K ⊔ Subgroup.centralizer (K : Set G))
    {K₀ : Subgroup G} (hK₀N : K₀ ≤ Subgroup.normalizer (K : Set G))
    (hK₀M : K₀ ≤ Subgroup.centralizer (tr ψ M0 : Set G))
    (hcomm : ∀ k ∈ K₀, ∀ j ∈ tr ψ (Jn 0), k * j = j * k) :
    K₀ ≤ Subgroup.centralizer (K : Set G) := by
  have hJK : tr ψ (Jn 0) ≤ K := tr_le_K ψ _
  intro k hk
  obtain ⟨κ, hκ, c, hc, rfl⟩ := CFSG.GroupTheory.exists_mul_of_mem_sup_of_commute
    (fun a ha b hb => Subgroup.mem_centralizer_iff.mp hb a ha) (hOut (hK₀N hk))
  have hκM : κ ∈ Subgroup.centralizer (tr ψ M0 : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro m hm
    have h1 := Subgroup.mem_centralizer_iff.mp (hK₀M hk) m hm
    have h2 := Subgroup.mem_centralizer_iff.mp hc m (tr_le_K ψ M0 hm)
    calc m * κ = m * (κ * c) * c⁻¹ := by group
      _ = κ * c * m * c⁻¹ := by rw [h1]
      _ = κ * (c * m) * c⁻¹ := by group
      _ = κ * (m * c) * c⁻¹ := by rw [← h2]
      _ = κ * m := by group
  have hκJ : κ ∈ tr ψ (Jn 0) := inf_centralizer_le_tr_jn0 hC ψ ⟨hκ, hκM⟩
  have hκ1 : κ = 1 := tr_jn0_eq_one_of_central hF ψ hκJ fun v hv => by
    have h1 := hcomm _ hk v hv
    have h2 := Subgroup.mem_centralizer_iff.mp hc v (hJK hv)
    calc κ * v = κ * c * v * c⁻¹ := by rw [mul_assoc κ c v, ← h2]; group
      _ = v * (κ * c) * c⁻¹ := by rw [h1]
      _ = v * κ := by group
  rw [hκ1, one_mul]
  exact hc

theorem map_conj_map_conj_tr_jn0 (hC : E7NatCent) (ψ : ↥L7 ≃* ↥K) {n : G}
    (hnnK : n * n ∈ Subgroup.normalizer (K : Set G))
    (hnM : (tr ψ M0).map (MulAut.conj n).toMonoidHom = tr ψ M0) :
    ((tr ψ (Jn 0)).map (MulAut.conj n).toMonoidHom).map (MulAut.conj n).toMonoidHom =
      tr ψ (Jn 0) := by
  rw [map_conj_map_conj]
  refine Subgroup.mem_normalizer_iff_map_conj_eq.mp (mem_normalizer_of_conj_mem fun x hx => ?_)
  have hMnn : (tr ψ M0).map (MulAut.conj (n * n)).toMonoidHom = tr ψ M0 := by
    rw [← map_conj_map_conj, hnM, hnM]
  refine inf_centralizer_le_tr_jn0 hC ψ ⟨(Subgroup.mem_normalizer_iff.mp hnnK x).mp
    (tr_le_K ψ _ hx), ?_⟩
  exact conj_mem_centralizer_of_map hMnn (tr_jn0_le_centralizer ψ hx)

theorem commute_tr_jn0_of_conj (hF : E7NatFrame) (hC : E7NatCent) (ψ : ↥L7 ≃* ↥K)
    {z : ↥L7} (hz : (z : ModGL .E7 (ZMod 2)) ∈ Jn 0)
    (hz3 : orderOf (z : ModGL .E7 (ZMod 2)) = 3) {n : G}
    (hK₀N : (tr ψ (Jn 0)).map (MulAut.conj n).toMonoidHom ≤ Subgroup.normalizer (K : Set G))
    (hK₀M : (tr ψ (Jn 0)).map (MulAut.conj n).toMonoidHom ≤
      Subgroup.centralizer (tr ψ M0 : Set G))
    (hn2 : ((tr ψ (Jn 0)).map (MulAut.conj n).toMonoidHom).map (MulAut.conj n).toMonoidHom =
      tr ψ (Jn 0))
    (hnz : n * ((ψ z : ↥K) : G) * n⁻¹ ∉ K) :
    ∀ k ∈ (tr ψ (Jn 0)).map (MulAut.conj n).toMonoidHom, ∀ j ∈ tr ψ (Jn 0),
      k * j = j * k := by
  have hJK : tr ψ (Jn 0) ≤ K := tr_le_K ψ _
  have hnn : n * n ∈ Subgroup.normalizer (tr ψ (Jn 0) : Set G) :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mpr ((map_conj_map_conj _ n n).symm.trans hn2)
  set K₀ : Subgroup G := (tr ψ (Jn 0)).map (MulAut.conj n).toMonoidHom
  have hK₀J : K₀ ≤ Subgroup.normalizer (tr ψ (Jn 0) : Set G) := by
    intro p hp
    refine mem_normalizer_of_conj_mem fun j hj => ?_
    refine inf_centralizer_le_tr_jn0 hC ψ ⟨(Subgroup.mem_normalizer_iff.mp (hK₀N hp) j).mp
      (hJK hj), ?_⟩
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (hK₀M hp) (tr_jn0_le_centralizer ψ hj))
      (Subgroup.inv_mem _ (hK₀M hp))
  have hJK₀ : tr ψ (Jn 0) ≤ Subgroup.normalizer (K₀ : Set G) := by
    intro j hj
    have hj' : n⁻¹ * j * n ∈ K₀ := by
      refine ⟨(n * n)⁻¹ * j * (n * n)⁻¹⁻¹,
        (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hnn) j).mp hj, ?_⟩
      show n * ((n * n)⁻¹ * j * (n * n)⁻¹⁻¹) * n⁻¹ = n⁻¹ * j * n
      group
    have h := conj_mem_normalizer_of_map (n := n) (Y := tr ψ (Jn 0)) rfl (hK₀J hj')
    rwa [show n * (n⁻¹ * j * n) * n⁻¹ = j by group] at h
  have hK₀K : ∀ w ∈ K₀, w ∈ K → w = 1 := by
    rintro _ ⟨j, hj, rfl⟩ hjK
    by_contra hne
    obtain ⟨y, hy, rfl⟩ := mem_tr.mp hj
    have hy1 : (y : ModGL .E7 (ZMod 2)) ≠ 1 := by
      intro h1
      apply hne
      have : y = 1 := Subtype.ext h1
      simp [this]
    obtain ⟨g₁, hg₁, g₂, hg₂, hcase⟩ := jn0_mem_of_ne_one hF hz hz3 hy hy1
    have hconj : ∀ g : ↥L7, (g : ModGL .E7 (ZMod 2)) ∈ Jn 0 →
        n * ((ψ (g * y * g⁻¹) : ↥K) : G) * n⁻¹ ∈ K := by
      intro g hg
      have hgN : n * ((ψ g : ↥K) : G) * n⁻¹ ∈ Subgroup.normalizer (K : Set G) :=
        hK₀N ⟨_, (coe_mem_tr_iff ψ g).mpr hg, rfl⟩
      have h := (Subgroup.mem_normalizer_iff.mp hgN _).mp hjK
      have heq : n * ((ψ (g * y * g⁻¹) : ↥K) : G) * n⁻¹ =
          n * ((ψ g : ↥K) : G) * n⁻¹ * (n * ((ψ y : ↥K) : G) * n⁻¹) *
            (n * ((ψ g : ↥K) : G) * n⁻¹)⁻¹ := by
        simp only [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv]
        group
      rw [heq]
      exact h
    apply hnz
    let g₁' : ↥L7 := ⟨g₁, hF.1 0 hg₁⟩
    let g₂' : ↥L7 := ⟨g₂, hF.1 0 hg₂⟩
    rcases hcase with h | h
    · have hzL : z = (g₁' * y * g₁'⁻¹) * (g₂' * y * g₂'⁻¹) := Subtype.ext (by
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, g₁', g₂']
        exact h)
      have heq : n * ((ψ z : ↥K) : G) * n⁻¹ =
          n * ((ψ (g₁' * y * g₁'⁻¹) : ↥K) : G) * n⁻¹ *
            (n * ((ψ (g₂' * y * g₂'⁻¹) : ↥K) : G) * n⁻¹) := by
        rw [hzL, map_mul, Subgroup.coe_mul]
        group
      rw [heq]
      exact K.mul_mem (hconj g₁' hg₁) (hconj g₂' hg₂)
    · have hzL : z = g₁' * y * g₁'⁻¹ := Subtype.ext (by
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, g₁']
        exact h)
      rw [hzL]
      exact hconj g₁' hg₁
  intro k hk j hj
  have h1 : k * j * k⁻¹ * j⁻¹ ∈ K₀ := by
    have h' : j * k⁻¹ * j⁻¹ ∈ K₀ :=
      (Subgroup.mem_normalizer_iff.mp (hJK₀ hj) _).mp (K₀.inv_mem hk)
    have h'' := K₀.mul_mem hk h'
    rwa [show k * (j * k⁻¹ * j⁻¹) = k * j * k⁻¹ * j⁻¹ by group] at h''
  have h2 : k * j * k⁻¹ * j⁻¹ ∈ K := by
    have h' : k * j * k⁻¹ ∈ tr ψ (Jn 0) :=
      (Subgroup.mem_normalizer_iff.mp (hK₀J hk) j).mp hj
    exact hJK ((tr ψ (Jn 0)).mul_mem h' ((tr ψ (Jn 0)).inv_mem hj))
  have h3 := hK₀K _ h1 h2
  calc k * j = (k * j * k⁻¹ * j⁻¹) * (j * k) := by group
    _ = j * k := by rw [h3, one_mul]

theorem K0_le_centralizer (hstd : StdAssumptions b₀ K E Row.E7) {B : Basis3 G 8}
    (hB : Adapted B b₀ K E) (hF : E7NatFrame) (hH : E7NatHigh) (hC : E7NatCent)
    (ψ : ↥L7 ≃* ↥K) {z : ↥L7} (hz : (z : ModGL .E7 (ZMod 2)) ∈ Jn 0)
    (hψz : ((ψ z : ↥K) : G) = B.b 1)
    (hOut : Subgroup.normalizer (K : Set G) ≤ K ⊔ Subgroup.centralizer (K : Set G))
    (hNK : Subgroup.normalizer (Subgroup.zpowers b₀ : Set G) ≤ Subgroup.normalizer (K : Set G))
    {n : G} (hnE : n ∈ Subgroup.normalizer (B.span : Set G)) (hn1 : n * B.b 1 * n⁻¹ = b₀)
    (hn0 : Subgroup.zpowers (n * b₀ * n⁻¹) = Subgroup.zpowers (B.b 1)) :
    (tr ψ (Jn 0)).map (MulAut.conj n).toMonoidHom ≤ Subgroup.centralizer (K : Set G) := by
  have hz3 := orderOf_z ψ hψz
  have hnM := conj_M_eq hstd hB hF hH hC ψ hz hψz hOut hnE hn1 hn0
  have hJ1 : tr ψ (Jn 0) ≤ Subgroup.normalizer (Subgroup.zpowers (B.b 1) : Set G) := by
    rw [← hψz]
    exact tr_jn0_le_normalizer_zpowers hF ψ hz hz3
  have h10 : (Subgroup.zpowers (B.b 1)).map (MulAut.conj n).toMonoidHom = Subgroup.zpowers b₀ := by
    rw [zpowers_map_conj, hn1]
  have hK₀N : (tr ψ (Jn 0)).map (MulAut.conj n).toMonoidHom ≤
      Subgroup.normalizer (K : Set G) := by
    rintro _ ⟨j, hj, rfl⟩
    exact hNK (conj_mem_normalizer_of_map h10 (hJ1 hj))
  have hK₀M : (tr ψ (Jn 0)).map (MulAut.conj n).toMonoidHom ≤
      Subgroup.centralizer (tr ψ M0 : Set G) := by
    rintro _ ⟨j, hj, rfl⟩
    exact conj_mem_centralizer_of_map hnM (tr_jn0_le_centralizer ψ hj)
  have h00 : (Subgroup.zpowers b₀).map (MulAut.conj (n * n)).toMonoidHom =
      Subgroup.zpowers b₀ := by
    rw [← map_conj_map_conj, zpowers_map_conj, hn0, zpowers_map_conj, hn1]
  have hn2 := map_conj_map_conj_tr_jn0 hC ψ
    (hNK (Subgroup.mem_normalizer_iff_map_conj_eq.mpr h00)) hnM
  have hb₀K : b₀ ∉ K := by
    intro hb
    have hb₀E : b₀ ∈ E := hstd.2.1.2.2.1
    have h1 : b₀ = 1 := (Subgroup.disjoint_def.mp hstd.2.2.2.1) (Subgroup.mem_zpowers b₀)
      ⟨hb₀E, hb⟩
    have hord : orderOf b₀ = 3 := hstd.2.1.1.1
    rw [h1, orderOf_one] at hord
    exact absurd hord (by decide)
  exact le_centralizer_of_commute_tr_jn0 hF hC ψ hOut hK₀N hK₀M
    (commute_tr_jn0_of_conj hF hC ψ hz hz3 hK₀N hK₀M hn2 (by rw [hψz, hn1]; exact hb₀K))

end Swap

end CFSG.StandardType.FrameRoute.FS81.E7Frame
