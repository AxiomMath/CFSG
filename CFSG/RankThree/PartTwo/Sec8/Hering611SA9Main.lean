module

public import CFSG.RankThree.PartTwo.Sec8.Hering611KFFinal
public import CFSG.RankThree.PartTwo.Sec8.Hering611SA9Tr
public import CFSG.RankThree.PartTwo.Sec8.Hering611SL14
public import CFSG.RankThree.PartTwo.Sec8.Hering611SLFus
public import CFSG.RankThree.PartTwo.Sec8.Hering611SK1
public import CFSG.RankThree.PartTwo.Sec8.Hering611SImg2
import CFSG.RankThree.PartTwo.Sec12.Item125Act
public import CFSG.RankThree.PartTwo.Sec8.Hering611SImg

public section

namespace CFSG.RankThree.PartTwo.Sec8.Hering611

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec4

section A9Main


variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L E T : Subgroup G} {d : G}
  {S K : Subgroup G}

theorem a9_step1 (h45 : Sec4.Item4_5) (C : Cfg611 G A c L E T d S K) (hcK : c ∉ K)
    (hZ : Subgroup.center (K ⧸ aschbacherSolvableCore 3 K) = ⊥)
    (hin : ∀ γ : MulAut (K ⧸ aschbacherSolvableCore 3 K), γ ^ 3 = 1 → KFacts.IsInnerAut γ) :
    ∃ (k : K) (ε : ℤ), (k : G) ∈ A ∧ (ε = 1 ∨ ε = -1) ∧ c = d ^ ε * (k : G) ∧
      QuotientGroup.mk' (aschbacherSolvableCore 3 K) k ≠ 1 ∧
      (QuotientGroup.mk' (aschbacherSolvableCore 3 K) k) ^ 3 = 1 ∧
      MulAut.conj (QuotientGroup.mk' (aschbacherSolvableCore 3 K) k) =
        thetaQuotMulAut K (compAction K ⟨c, C.A_le_normalizer_K h45 C.c_mem⟩) := by
  have hAe := C.toFrame611.isElemAbelian
  have hd3 := C.toFrame611.d_pow_three
  obtain ⟨k, hkA, hck, hkact⟩ := exists_mul_mem_zpowers_d h45 C hZ hin C.c_mem
  obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hck
  have hk1 : QuotientGroup.mk' (aschbacherSolvableCore 3 K) k ≠ 1 := by
    intro h1
    apply C.c_not_cent
    rw [Sec12.mem_thetaQuotCentralizer_iff_thetaBarAct (C.A_le_normalizer_K h45 C.c_mem)]
    have h2 : thetaQuotMulAut K (compAction K ⟨c, C.A_le_normalizer_K h45 C.c_mem⟩) = 1 := by
      rw [← hkact, h1, map_one]
    exact h2
  have hk3 : (QuotientGroup.mk' (aschbacherSolvableCore 3 K) k) ^ 3 = 1 := by
    have h3 : k ^ 3 = 1 := Subtype.ext (by simpa using hAe.2 (k : G) hkA)
    rw [← map_pow, h3, map_one]
  have hdz : d ^ (3 : ℤ) = 1 := by
    rw [show (3 : ℤ) = ((3 : ℕ) : ℤ) by norm_num, zpow_natCast, hd3]
  have hjmod : d ^ j = d ^ (j % 3) := zpow_eq_zpow_emod j hdz
  have hcj : c = d ^ j * (k : G) := by rw [hj]; group
  rcases (show j % 3 = 0 ∨ j % 3 = 1 ∨ j % 3 = 2 by omega) with h | h | h
  · exfalso
    apply hcK
    rw [hcj, hjmod, h, zpow_zero, one_mul]
    exact k.2
  · refine ⟨k, 1, hkA, Or.inl rfl, ?_, hk1, hk3, hkact⟩
    rw [hcj, hjmod, h]
  · refine ⟨k, -1, hkA, Or.inr rfl, ?_, hk1, hk3, hkact⟩
    rw [hcj, hjmod, h]
    congr 1
    have h2 : d ^ (2 : ℤ) = d⁻¹ := by
      apply eq_inv_of_mul_eq_one_left
      rw [← zpow_add_one]
      exact hdz
    rw [zpow_neg_one]
    exact h2

theorem kF611A9FuseSym_of (h45 : Sec4.Item4_5) : KF611A9FuseSym := by
  intro G _ _ A c L E T d S K C hiso hcK
  obtain ⟨e⟩ := hiso
  have hAe := C.toFrame611.isElemAbelian
  have hAK := C.A_le_normalizer_K h45
  have hdA := C.toFrame611.d_mem_A
  have hd3 := C.toFrame611.d_pow_three
  have hKd := C.K_le_centralizer
  have hALK : A ⊓ L ≤ K := C.inf_L_le_K
  have hZ : Subgroup.center (K ⧸ aschbacherSolvableCore 3 K) = ⊥ :=
    CFSG.GorensteinWalter.center_eq_bot_of_mulEquiv e
      (alternatingGroup.center_eq_bot (by simp))
  have hin : ∀ γ : MulAut (K ⧸ aschbacherSolvableCore 3 K), γ ^ 3 = 1 → KFacts.IsInnerAut γ :=
    fun γ hγ => mem_range_conj_of_pow_three_alt9 e hγ
  obtain ⟨k, ε, hkA, hε, hck, hk1, hk3, hkact⟩ := a9_step1 h45 C hcK hZ hin
  obtain ⟨hcN, -, -, hPcomp0, hP60⟩ := exists_bridge_image h45 C
  have hPcomp : imageSub K (Sec11.sec11K L d) ∈
      thetaComponentsIn (Item426.fixSub (Item426.thetaAut K hcN)) := hPcomp0
  have hP6 : Nonempty (imageSub K (Sec11.sec11K L d) ⧸
      aschbacherSolvableCore 3 (imageSub K (Sec11.sec11K L d)) ≃* alternatingGroup (Fin 6)) :=
    hP60
  have hPperf := isPerfect_of_mem_thetaComponentsIn hPcomp
  have hPle := le_of_mem_thetaComponentsIn hPcomp
  set π := QuotientGroup.mk' (aschbacherSolvableCore 3 K) with hπ
  have hPc : ∀ p ∈ imageSub K (Sec11.sec11K L d), p * π k = π k * p := by
    intro p hp
    have h1 : thetaQuotMulAut K (compAction K ⟨c, hcN⟩) p = p := hPle hp
    have h2 : (MulAut.conj (π k)) p = p := by
      rw [hkact]
      exact h1
    have h3 : π k * p * (π k)⁻¹ = p := h2
    calc p * π k = (π k * p * (π k)⁻¹) * π k := by rw [h3]
      _ = π k * p := by group
  have h360 : 360 ∣ Nat.card (imageSub K (Sec11.sec11K L d)) := by
    obtain ⟨ψ⟩ := hP6
    have h1 : Nat.card (imageSub K (Sec11.sec11K L d) ⧸
        aschbacherSolvableCore 3 (imageSub K (Sec11.sec11K L d))) = 360 := by
      rw [Nat.card_congr ψ.toEquiv, nat_card_alternatingGroup]
      simp only [Nat.card_eq_fintype_card, Fintype.card_fin]
      decide
    rw [← h1]
    exact Subgroup.card_quotient_dvd_card _
  have hAL3 : IsPGroup 3 (A ⊓ L : Subgroup G) :=
    Sec5.isPGroup_of_isElemAbelian (Sec5.isElemAbelian_of_le hAe inf_le_left)
  have hEP : imageSub K (A ⊓ L) ≤ imageSub K (Sec11.sec11K L d) :=
    imageSub_mono C.toFrame611.inf_L_le_sec11K
  have hE9 : Nat.card (imageSub K (A ⊓ L)) = 9 := by
    rw [card_imageSub_of_isPGroup hALK hAL3]
    exact C.toFrame611.card_inf_L h45
  obtain ⟨wb, hwb1, hwb2, hwb3⟩ := alt9_fusion e hk3 hk1 hPperf hPc h360 hEP hE9
  set D : Subgroup G := Subgroup.zpowers (k : G) ⊔ (A ⊓ L) with hD
  have hDK : D ≤ K := sup_le (Subgroup.zpowers_le.mpr k.2) hALK
  have hDA : D ≤ A := sup_le (Subgroup.zpowers_le.mpr hkA) inf_le_left
  have hD3 : IsPGroup 3 D := Sec5.isPGroup_of_isElemAbelian (Sec5.isElemAbelian_of_le hAe hDA)
  have hDimg : imageSub K D = Subgroup.zpowers (π k) ⊔ imageSub K (A ⊓ L) := by
    rw [hD, imageSub_sup (Subgroup.zpowers_le.mpr k.2) hALK, imageSub_zpowers]
  have hnorm : wb ∈ Subgroup.normalizer
      (imageSub K D : Set (K ⧸ aschbacherSolvableCore 3 K)) := by
    rw [hDimg]
    exact mem_normalizer_of_conj_mem hwb1
  obtain ⟨w, hwN, hwπ⟩ := exists_lift_normalizer hDK hD3 hnorm
  set kk : K := w * k * w⁻¹ with hkk
  have hkkG : (kk : G) = (w : G) * k * (w : G)⁻¹ := rfl
  have hkD : (k : G) ∈ D := Subgroup.mem_sup_left (Subgroup.mem_zpowers _)
  have hkkD : (kk : G) ∈ D := by
    rw [hkkG]
    exact (Subgroup.mem_normalizer_iff.mp hwN (k : G)).mp hkD
  have hπkk : π kk = wb * π k * wb⁻¹ := by
    rw [hkk, map_mul, map_mul, map_inv, hwπ]
  have hkkAL : (kk : G) ∈ A ⊓ L :=
    mem_of_mk_mem_imageSub hD3 (le_sup_right : A ⊓ L ≤ D) hDK hkkD (by rw [hπkk]; exact hwb2)
  have hkk1 : (kk : G) ≠ 1 := by
    intro h
    have h' : kk = 1 := Subtype.ext h
    apply hwb3
    rw [← hπkk, h', map_one]
  have hkkA : (kk : G) ∈ A := hkkAL.1
  have hkkL : (kk : G) ∈ L := hkkAL.2
  have hwd : (w : G) * d = d * (w : G) := Subgroup.mem_centralizer_singleton_iff.mp (hKd w.2)
  have hwc : (w : G) * (d ^ ε * (k : G)) * (w : G)⁻¹ = d ^ ε * (kk : G) := by
    have hwdε : (w : G) * d ^ ε = d ^ ε * (w : G) :=
      ((Commute.zpow_right (show Commute (w : G) d from hwd) ε)).eq
    rw [hkkG]
    calc (w : G) * (d ^ ε * (k : G)) * (w : G)⁻¹
        = ((w : G) * d ^ ε) * (k : G) * (w : G)⁻¹ := by group
      _ = d ^ ε * ((w : G) * k * (w : G)⁻¹) := by rw [hwdε]; group
  rcases hε with rfl | rfl
  ·
    obtain ⟨u, huL, hu1, hu2⟩ := exists_L_fusion C.toFrame611 hkkA hkkL hkk1
    left
    rw [isConj_iff]
    refine ⟨u * w, ?_⟩
    have h1 : (u * (w : G)) * c * (u * (w : G))⁻¹ = u * ((w : G) * c * (w : G)⁻¹) * u⁻¹ := by
      group
    rw [h1, hck, hwc, zpow_one, ← hu2]
    group
  ·
    obtain ⟨u, huL, hu1, hu2⟩ := exists_L_fusion C.toFrame611 (A.inv_mem hkkA) (L.inv_mem hkkL)
      (inv_ne_one.mpr hkk1)
    right
    rw [isConj_iff]
    refine ⟨u * w, ?_⟩
    have h1 : (u * (w : G)) * c * (u * (w : G))⁻¹ = u * ((w : G) * c * (w : G)⁻¹) * u⁻¹ := by
      group
    have hcomm : d * (kk : G) = (kk : G) * d := C.toFrame611.comm_of_mem hdA hkkA
    have h2 : u⁻¹ * d⁻¹ * u = d⁻¹ * (kk : G) := by
      have : u⁻¹ * d⁻¹ * u = (u⁻¹ * d * u)⁻¹ := by group
      rw [this, hu2]
      calc (d * (kk : G)⁻¹)⁻¹ = (kk : G) * d⁻¹ := by group
        _ = d⁻¹ * (kk : G) := by
          rw [mul_inv_eq_iff_eq_mul, mul_assoc, ← hcomm]
          group
    rw [h1, hck, hwc, zpow_neg_one, ← h2]
    group

end A9Main

end CFSG.RankThree.PartTwo.Sec8.Hering611
