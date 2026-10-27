module

public import CFSG.RankThree.PartTwo.Sec8.Hering611SJ3Core
public import CFSG.RankThree.PartTwo.Sec8.Hering611SJ3Phi
public import CFSG.RankThree.PartTwo.Sec8.Hering611SJ3D
public import CFSG.RankThree.PartTwo.Sec8.Hering611SJ3Count
public import CFSG.RankThree.PartTwo.Sec8.Hering611SGenC
public import CFSG.RankThree.PartTwo.Sec8.Hering611SImg2
public import CFSG.RankThree.PartTwo.Sec8.Hering611SL14
public import CFSG.RankThree.PartTwo.Sec8.Hering611SLFus
import CFSG.RankThree.PartTwo.Sec12.Item123Inputs
public import CFSG.RankThree.PartTwo.Sec8.Hering611SImg

public section

namespace CFSG.RankThree.PartTwo.Sec8.Hering611

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec4

theorem exists_eps_of_mem_zpowers {M : Type*} [Group M] {y z : M} (hy3 : y ^ 3 = 1)
    (hz : z ∈ Subgroup.zpowers y) (hz1 : z ≠ 1) : ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧ z = y ^ ε := by
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
  have h3 : y ^ (3 : ℤ) = 1 := by
    rw [show (3 : ℤ) = ((3 : ℕ) : ℤ) by norm_num, zpow_natCast, hy3]
  have hmod : y ^ n = y ^ (n % 3) := zpow_eq_zpow_emod n h3
  rcases (show n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 by omega) with h | h | h
  · exfalso
    apply hz1
    rw [hmod, h, zpow_zero]
  · exact ⟨1, Or.inl rfl, by rw [hmod, h]⟩
  · refine ⟨-1, Or.inr rfl, ?_⟩
    rw [hmod, h]
    have h2 : y ^ (2 : ℤ) = y⁻¹ := by
      apply eq_inv_of_mul_eq_one_left
      rw [← zpow_add_one]
      exact h3
    rw [h2, zpow_neg_one]

section J3Fuse


theorem kF611J3CoverFuse_of (h45 : Sec4.Item4_5) : KF611J3CoverFuse := by
  intro G _ _ A c L E T d S K C hcov
  obtain ⟨hZ3, hJ⟩ := hcov
  have hperf : Group.IsPerfect (K ⧸ aschbacherSolvableCore 3 K) :=
    (Sec12.isQuasisimple_thetaQuot_of_mem C.mem_thetaComponentsAt_K).1
  have hAe := C.toFrame611.isElemAbelian
  have hdA := C.toFrame611.d_mem_A
  have hd3 := C.toFrame611.d_pow_three
  have hALK : A ⊓ L ≤ K := C.inf_L_le_K
  obtain ⟨dK, rfl, hZgen⟩ := exists_d_mem_K h45 C hZ3
  obtain ⟨Φ, hΦker, hΦK⟩ := exists_hom_Phi h45 C hperf hJ
  have hkerΦ : Φ.ker = (Subgroup.zpowers (dK : G)).subgroupOf A := by
    ext a
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    exact hΦker a
  have hdA' : Subgroup.zpowers (dK : G) ≤ A := Subgroup.zpowers_le.mpr hdA
  have hker3 : Nat.card Φ.ker = 3 := by
    rw [hkerΦ, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hdA').toEquiv, Nat.card_zpowers,
      orderOf_eq_prime hd3 C.toFrame611.d_ne_one]
  have hB9 : Nat.card ((A ⊓ L).subgroupOf A) = 9 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left : A ⊓ L ≤ A)).toEquiv]
    exact C.toFrame611.card_inf_L h45
  have hdisj : Disjoint ((A ⊓ L).subgroupOf A) Φ.ker := by
    rw [Subgroup.disjoint_def]
    intro b hb1 hb2
    have hbL : (b : G) ∈ L := (Subgroup.mem_subgroupOf.mp hb1).2
    have hbd : (b : G) ∈ Subgroup.zpowers (dK : G) := (hΦker b).mp (MonoidHom.mem_ker.mp hb2)
    have h1 : (b : G) ∈ Subgroup.zpowers (dK : G) ⊓ L := ⟨hbd, hbL⟩
    rw [C.toFrame611.zpowers_inf_L, Subgroup.mem_bot] at h1
    exact Subtype.ext h1
  obtain ⟨hAb27, hEb9⟩ := card_range_and_map Φ C.toFrame611.card_A hker3 _ hB9 hdisj
  have hcommA : ∀ x y : A, x * y = y * x := fun x y =>
    Subtype.ext (C.toFrame611.comm_of_mem x.2 y.2)
  have hexpA : ∀ x : A, x ^ 3 = 1 := fun x => Subtype.ext (hAe.2 x x.2)
  obtain ⟨hAcomm, hAexp⟩ := isElemAbelian_range Φ hcommA hexpA
  have hAb : CFSG.Assembly.IsElemAbelian 3 Φ.range :=
    ⟨⟨⟨fun x y => hAcomm x y⟩⟩, fun x hx => congrArg Subtype.val (hAexp ⟨x, hx⟩)⟩
  obtain ⟨e, heE, he1, hcore⟩ := exists_noncentral_lift hperf (Z := Subgroup.center _)
    le_rfl hZ3 hJ hAb hAb27 (Subgroup.map_le_range Φ _) hEb9
  obtain ⟨b, hb, rfl⟩ := Subgroup.mem_map.mp heE
  have hbAL : (b : G) ∈ A ⊓ L := Subgroup.mem_subgroupOf.mp hb
  have haA : (b : G) ∈ A := hbAL.1
  have haL : (b : G) ∈ L := hbAL.2
  have haK : (b : G) ∈ K := hALK hbAL
  have ha1 : (b : G) ≠ 1 := by
    intro h
    apply he1
    have : b = 1 := Subtype.ext h
    rw [this, map_one]
  set aK : K := ⟨(b : G), haK⟩ with haKdef
  set πK := QuotientGroup.mk' (aschbacherSolvableCore 3 K) with hπK
  set ρ := QuotientGroup.mk' (Subgroup.center (K ⧸ aschbacherSolvableCore 3 K)) with hρ
  have hΦb : Φ b = ρ (πK aK) := hΦK b aK rfl
  obtain ⟨t, hte, hnc⟩ := hcore (πK aK) hΦb.symm
  have hdb3 : (πK dK) ^ 3 = 1 := by
    rw [← map_pow, show dK ^ 3 = 1 from Subtype.ext (by simpa using hd3), map_one]
  have hz : t * πK aK * t⁻¹ * (πK aK)⁻¹ ∈ Subgroup.center (K ⧸ aschbacherSolvableCore 3 K) := by
    rw [← QuotientGroup.eq_one_iff (N := Subgroup.center (K ⧸ aschbacherSolvableCore 3 K))]
    show ρ (t * πK aK * t⁻¹ * (πK aK)⁻¹) = 1
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, ← hΦb]
    have h1 : ρ t * Φ b = Φ b * ρ t := hte
    calc ρ t * Φ b * (ρ t)⁻¹ * (Φ b)⁻¹ = (Φ b * ρ t) * (ρ t)⁻¹ * (Φ b)⁻¹ := by rw [h1]
      _ = 1 := by group
  have hz1 : t * πK aK * t⁻¹ * (πK aK)⁻¹ ≠ 1 := by
    intro h
    apply hnc
    have h2 : t * πK aK * t⁻¹ = πK aK := by
      calc t * πK aK * t⁻¹ = (t * πK aK * t⁻¹ * (πK aK)⁻¹) * πK aK := by group
        _ = πK aK := by rw [h, one_mul]
    calc πK aK * t = (t * πK aK * t⁻¹) * t := by rw [h2]
      _ = t * πK aK := by group
  obtain ⟨ε, hε, hzε⟩ := exists_eps_of_mem_zpowers hdb3 (hZgen ▸ hz) hz1
  have hdc : πK dK ∈ Subgroup.center (K ⧸ aschbacherSolvableCore 3 K) :=
    hZgen ▸ Subgroup.mem_zpowers _
  have hwc : ∀ g : K ⧸ aschbacherSolvableCore 3 K, g * (πK dK) ^ ε = (πK dK) ^ ε * g :=
    fun g => Subgroup.mem_center_iff.mp (Subgroup.zpow_mem _ hdc ε) g
  have hkey : t * πK aK * t⁻¹ = πK aK * (πK dK) ^ ε := by
    calc t * πK aK * t⁻¹ = (t * πK aK * t⁻¹ * (πK aK)⁻¹) * πK aK := by group
      _ = (πK dK) ^ ε * πK aK := by rw [hzε]
      _ = πK aK * (πK dK) ^ ε := (hwc _).symm
  set D : Subgroup G := Subgroup.zpowers (aK : G) ⊔ Subgroup.zpowers (dK : G) with hD
  have hDK : D ≤ K := sup_le (Subgroup.zpowers_le.mpr aK.2) (Subgroup.zpowers_le.mpr dK.2)
  have hDA : D ≤ A := sup_le (Subgroup.zpowers_le.mpr haA) (Subgroup.zpowers_le.mpr hdA)
  have hD3 : IsPGroup 3 D := Sec5.isPGroup_of_isElemAbelian (Sec5.isElemAbelian_of_le hAe hDA)
  have hDimg : imageSub K D = Subgroup.zpowers (πK aK) ⊔ Subgroup.zpowers (πK dK) := by
    rw [hD, imageSub_sup (Subgroup.zpowers_le.mpr aK.2) (Subgroup.zpowers_le.mpr dK.2),
      imageSub_zpowers, imageSub_zpowers]
  have hback : t⁻¹ * πK aK * t = πK aK * ((πK dK) ^ ε)⁻¹ := by
    have hc : t⁻¹ * (πK dK) ^ ε * t = (πK dK) ^ ε := by
      rw [hwc t⁻¹]
      group
    calc t⁻¹ * πK aK * t
        = t⁻¹ * πK aK * t * (t⁻¹ * (πK dK) ^ ε * t) * ((πK dK) ^ ε)⁻¹ := by rw [hc]; group
      _ = t⁻¹ * (πK aK * (πK dK) ^ ε) * t * ((πK dK) ^ ε)⁻¹ := by group
      _ = t⁻¹ * (t * πK aK * t⁻¹) * t * ((πK dK) ^ ε)⁻¹ := by rw [hkey]
      _ = πK aK * ((πK dK) ^ ε)⁻¹ := by group
  have hnorm : t⁻¹ ∈ Subgroup.normalizer (imageSub K D : Set (K ⧸ aschbacherSolvableCore 3 K)) := by
    refine mem_normalizer_of_conj_mem (fun y hy => ?_)
    rw [hDimg] at hy ⊢
    have hle : (Subgroup.zpowers (πK aK) ⊔ Subgroup.zpowers (πK dK)).map
        (MulAut.conj t⁻¹).toMonoidHom ≤ Subgroup.zpowers (πK aK) ⊔ Subgroup.zpowers (πK dK) := by
      rw [Subgroup.map_sup, MonoidHom.map_zpowers, MonoidHom.map_zpowers]
      refine sup_le (Subgroup.zpowers_le.mpr ?_) (Subgroup.zpowers_le.mpr ?_)
      · show t⁻¹ * πK aK * t⁻¹⁻¹ ∈ _
        rw [inv_inv, hback]
        exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (Subgroup.mem_zpowers _))
          (Subgroup.inv_mem _ (Subgroup.mem_sup_right (Subgroup.zpow_mem_zpowers _ ε)))
      · show t⁻¹ * πK dK * t⁻¹⁻¹ ∈ _
        have : t⁻¹ * πK dK * t⁻¹⁻¹ = πK dK := by
          rw [inv_inv]
          have := Subgroup.mem_center_iff.mp hdc t⁻¹
          rw [this]
          group
        rw [this]
        exact Subgroup.mem_sup_right (Subgroup.mem_zpowers _)
    exact hle (Subgroup.mem_map_of_mem (MulAut.conj t⁻¹).toMonoidHom hy)
  obtain ⟨w, hwN, hwπ⟩ := exists_lift_normalizer hDK hD3 hnorm
  have haD : (aK : G) ∈ D := Subgroup.mem_sup_left (Subgroup.mem_zpowers _)
  have hdD : (dK : G) ∈ D := Subgroup.mem_sup_right (Subgroup.mem_zpowers _)
  have hconjD : ∀ x : G, x ∈ D → (w : G)⁻¹ * x * w ∈ D := fun x hx =>
    ((Subgroup.mem_normalizer_iff''.mp hwN) x).mp hx
  have hw1K : w⁻¹ * aK * w = aK * dK ^ ε := by
    have hmem : ((aK * dK ^ ε : K) : G) ∈ D := by
      have h' := D.mul_mem haD (Subgroup.zpow_mem D hdD ε)
      simpa using h'
    apply eq_of_mk_eq_of_isPGroup hD3 (K := K) (D := D)
    · exact hconjD _ haD
    · exact hmem
    · rw [map_mul, map_mul, map_inv, hwπ, map_mul, map_zpow, inv_inv]
      exact hkey
  have hw2K : w⁻¹ * dK * w = dK := by
    apply eq_of_mk_eq_of_isPGroup hD3 (K := K) (D := D)
    · exact hconjD _ hdD
    · exact hdD
    · rw [map_mul, map_mul, map_inv, hwπ, inv_inv]
      have := Subgroup.mem_center_iff.mp hdc t
      rw [this]
      group
      rfl
  have hw1 : (w : G)⁻¹ * (b : G) * w = (b : G) * (dK : G) ^ ε := by
    have := congrArg Subtype.val hw1K
    simpa using this
  have hw2 : (w : G)⁻¹ * (dK : G) * w = dK := by
    have := congrArg Subtype.val hw2K
    simpa using this
  obtain ⟨u, huL, hu1, hu2⟩ := exists_L_fusion C.toFrame611 haA haL ha1
  have had : (b : G) * (dK : G) = (dK : G) * (b : G) := C.toFrame611.comm_of_mem haA hdA
  have hfin := conj_eq_zpow_of_transvections had hε (Or.inl rfl : (1 : ℤ) = 1 ∨ (1 : ℤ) = -1)
    hw1 hw2 hu1 (by rw [zpow_one]; exact hu2)
  rcases hε with rfl | rfl
  · refine ⟨b, haA, haL, ha1, ?_⟩
    rw [isConj_iff]
    refine ⟨((w : G) * u ^ (-((1 : ℤ) * 1)))⁻¹, ?_⟩
    rw [inv_inv]
    simpa using hfin
  · refine ⟨(b : G)⁻¹, A.inv_mem haA, L.inv_mem haL, inv_ne_one.mpr ha1, ?_⟩
    rw [isConj_iff]
    refine ⟨((w : G) * u ^ (-((-1 : ℤ) * 1)))⁻¹, ?_⟩
    rw [inv_inv]
    have h2 := congrArg (fun x : G => x⁻¹) hfin
    simp only [zpow_neg_one, inv_inv] at h2
    calc ((w : G) * u ^ (-((-1 : ℤ) * 1)))⁻¹ * (b : G)⁻¹ * ((w : G) * u ^ (-((-1 : ℤ) * 1)))
        = (((w : G) * u ^ (-((-1 : ℤ) * 1)))⁻¹ * (b : G) *
            ((w : G) * u ^ (-((-1 : ℤ) * 1))))⁻¹ := by
          group
      _ = (dK : G) := by rw [hfin, zpow_neg_one, inv_inv]

end J3Fuse

end CFSG.RankThree.PartTwo.Sec8.Hering611
