module

public import CFSG.Quasithin.H13.L32NLem14331a
public import CFSG.Quasithin.H13.L32NLem14330d

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique

namespace L14331

variable {G : Type} [Group G]

abbrev kA (T V : Subgroup G) (a : G) : Subgroup G :=
  conjClosure (Subgroup.zpowers a) (l32nH T V)

end L14331

namespace L14328

open L14331

variable {G : Type} [Group G] [Finite G] {T L V V₂ : Subgroup G} [IsMulCommutative ↥V]

omit [Finite G] [IsMulCommutative ↥V] in
theorem centralizer_le_normalizer_zv {v : G} (hv : v ∈ V) :
    Subgroup.centralizer (V : Set G) ≤ Subgroup.normalizer (zv V v : Set G) := by
  intro c hc
  have hcv : c ∈ Subgroup.normalizer (Subgroup.zpowers v : Set G) :=
    Subgroup.centralizer_le_normalizer _
      (Subgroup.centralizer_le (Subgroup.zpowers_le.mpr hv) hc)
  exact L14332.normalizer_le_normalizer_centerOf _ (le_normalizer_conjClosure _ _ hcv)

omit [Finite G] [IsMulCommutative ↥V] in
theorem kA_le {a : G} (ha : a ∈ l32nH T V) : kA T V a ≤ l32nH T V :=
  conjClosure_le fun _ hh _ hy => (l32nH T V).mul_mem ((l32nH T V).mul_mem hh
    ((Subgroup.zpowers_le.mpr ha) hy)) ((l32nH T V).inv_mem hh)

omit [Finite G] [IsMulCommutative ↥V] in
theorem le_normalizer_kA (a : G) : l32nH T V ≤ Subgroup.normalizer (kA T V a : Set G) :=
  le_normalizer_conjClosure _ _

omit [Finite G] [IsMulCommutative ↥V] in
theorem kA_le_centralizer {a : G} (ha : ∀ w ∈ centerOf (fsuU T V), a * w = w * a) :
    kA T V a ≤ Subgroup.centralizer (centerOf (fsuU T V) : Set G) := by
  have haC : Subgroup.zpowers a ≤ Subgroup.centralizer (centerOf (fsuU T V) : Set G) := by
    rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_iff]
    intro w hw
    exact (ha w hw).symm
  refine conjClosure_le fun h hh y hy => ?_
  have hhN := mem_normalizer_centralizer
    (L14332.normalizer_le_normalizer_centerOf _ (L14332.l32nH_le_normalizer_fsuU T V hh))
  exact (Subgroup.mem_normalizer_iff.mp hhN y).mp (haC hy)

namespace Ctx

variable {g z b l : G} (C : Ctx G T L V V₂ g z b l) (D : HatModelU (fsuU T V))
include C

theorem exists_x : ∃ x ∈ L, x ^ 3 = 1 ∧ x * z * x⁻¹ = z ∧ x * (g⁻¹ * z * g) * x⁻¹ = z * b := by
  have haV₂ := C.a_mem
  have haV₁ := C.a_nmem
  have haV := C.a_V
  generalize g⁻¹ * z * g = a at haV₂ haV₁ haV ⊢
  have hzb : z * b ∈ V := V.mul_mem C.z_V C.b_mem
  have hzz := C.mul_self_V C.z_V
  have hbz : b = z * (z * b) := by rw [← mul_assoc, hzz, one_mul]
  obtain ⟨x, hxL, hx3, hxz, hxa, -⟩ := C.S.exists_rot C.z_V haV hzb
    (fun h => haV₁ (h ▸ one_mem _))
    (fun h => C.b_nmem (by rw [hbz, h, mul_one]; exact C.z_V₂)) (fun h => haV₁ (h ▸ C.z_mem))
    (fun h => C.b_nmem (by rw [hbz, h, hzz]; exact one_mem _))
    (fun h => C.b_nmem (by rw [hbz, ← h]; exact V₂.mul_mem C.z_V₂ haV₂))
    (fun h => C.b_nmem (by
      rw [hbz, h, ← mul_assoc, hzz, one_mul]
      exact haV₂))
  exact ⟨x, hxL, hx3, hxz, hxa⟩

theorem eq_one_of_conj (h14325 : Lemma14325One) (h1222 : Stmt12_2_2) {e x : G}
    (he : e ∈ centerOf (i128 T L V (fsuV1 T V))) (hxN : x ∈ Subgroup.normalizer (V : Set G))
    (hxa : x * (g⁻¹ * z * g) * x⁻¹ = z * b) (hxe : x * e * x⁻¹ = e) : e = 1 := by
  rw [C.zI_za] at he
  have h1 : e ∈ zv V (z * b) := by
    have hc := conjugate_zv (v := z * b) hxN
    have e1 : x⁻¹ * (z * b) * x = g⁻¹ * z * g := by
      rw [← hxa]
      group
    rw [e1] at hc
    have h2 : e ∈ CFSG.conjugate (zv V (z * b)) x := by
      rw [hc]
      exact he.2
    rw [mem_conj_iff, hxe] at h2
    exact h2
  have hmem : e ∈ centerOf (fsuU T V) ⊓ CFSG.conjugate (centerOf (fsuU T V)) g ⊓
      CFSG.conjugate (centerOf (fsuU T V)) l := by
    rw [C.conj_zU (C.P_le C.gP), C.conj_zU (C.L_le C.l_mem), C.l_inv_z, C.zU_eq]
    exact ⟨he, h1⟩
  rw [C.zU_inf_eq_bot h14325 h1222] at hmem
  exact Subgroup.mem_bot.mp hmem

theorem comm_zU (h14325 : Lemma14325One) (h1222 : Stmt12_2_2) (h12813 : Lemma12_8_13) {a w : G}
    (ha : a ∈ CFSG.conjugate (centerOf (fsuU T V)) g ⊓ CFSG.conjugate (centerOf (fsuU T V)) l)
    (hw : w ∈ centerOf (fsuU T V)) : a * w = w * a := by
  have hwV : w ∈ Subgroup.centralizer (V : Set G) := Subgroup.centralizer_le V_le_U hw.2
  have hgN : w ∈ Subgroup.normalizer (CFSG.conjugate (centerOf (fsuU T V)) g : Set G) := by
    rw [C.conj_zU (C.P_le C.gP)]
    exact centralizer_le_normalizer_zv C.a_V hwV
  have hlN : w ∈ Subgroup.normalizer (CFSG.conjugate (centerOf (fsuU T V)) l : Set G) := by
    rw [C.conj_zU (C.L_le C.l_mem), C.l_inv_z]
    exact centralizer_le_normalizer_zv (V.mul_mem C.z_V C.b_mem) hwV
  have haH : a ∈ l32nH T V := L14332.conj_zU_le h12813 C.setting C.gP C.gN ha.1
  have haZ := L14332.normalizer_le_normalizer_centerOf _ (L14332.l32nH_le_normalizer_fsuU T V haH)
  set c := a * w * a⁻¹ * w⁻¹ with hc
  have hcZ : c ∈ centerOf (fsuU T V) :=
    (centerOf (fsuU T V)).mul_mem ((Subgroup.mem_normalizer_iff.mp haZ w).mp hw)
      ((centerOf (fsuU T V)).inv_mem hw)
  have e1 : c = a * (w * a⁻¹ * w⁻¹) := by rw [hc]; group
  have hcg : c ∈ CFSG.conjugate (centerOf (fsuU T V)) g := by
    rw [e1]
    exact Subgroup.mul_mem _ ha.1 ((Subgroup.mem_normalizer_iff.mp hgN _).mp
      (Subgroup.inv_mem _ ha.1))
  have hcl : c ∈ CFSG.conjugate (centerOf (fsuU T V)) l := by
    rw [e1]
    exact Subgroup.mul_mem _ ha.2 ((Subgroup.mem_normalizer_iff.mp hlN _).mp
      (Subgroup.inv_mem _ ha.2))
  have hmem : c ∈ centerOf (fsuU T V) ⊓ CFSG.conjugate (centerOf (fsuU T V)) g ⊓
      CFSG.conjugate (centerOf (fsuU T V)) l := ⟨⟨hcZ, hcg⟩, hcl⟩
  rw [C.zU_inf_eq_bot h14325 h1222, Subgroup.mem_bot] at hmem
  calc a * w = a * w * a⁻¹ * w⁻¹ * (w * a) := by group
    _ = w * a := by rw [← hc, hmem, one_mul]

theorem not_three_dvd_inf
    (hQ : centralizerMod (fsuV1 T V) (l32nH T V) (fsuU T V) = pCoreOf 2 (l32nH T V))
    {K : Subgroup G} (hKZ : K ≤ Subgroup.centralizer (centerOf (fsuU T V) : Set G)) :
    ¬ 3 ∣ Nat.card ↥(K ⊓ l32nCHat T V) := by
  intro h3
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' 3 h3
  set c : G := (y : G) with hcy
  have hcK : c ∈ K := (Subgroup.mem_inf.mp y.2).1
  have hcE : c ∈ l32nCHat T V := (Subgroup.mem_inf.mp y.2).2
  have hc3 : orderOf c = 3 := by rw [hcy, Subgroup.orderOf_coe]; exact hy
  have hc3' : c ^ 3 = 1 := by rw [← hc3]; exact pow_orderOf_eq_one c
  have hU2 : IsPGroup 2 ↥(fsuU T V) := C.S.hH.sylow.1.to_le C.U_T
  have hcU : ∀ u ∈ fsuU T V, c * u * c⁻¹ = u := by
    intro u hu
    set d := c * u * c⁻¹ * u⁻¹ with hd
    have hdZ : d ∈ centerOf (fsuU T V) := hcE.2.2 u hu
    have hcd : c * d * c⁻¹ = d := by
      rw [← Subgroup.mem_centralizer_iff.mp (hKZ hcK) d hdZ, mul_inv_cancel_right]
    have hcu : c * u * c⁻¹ = d * u := by rw [hd]; group
    have h3 := L14332.pow_conj_eq hcd hcu 3
    rw [hc3', one_mul, inv_one, mul_one] at h3
    have hd3 : d ^ 3 = 1 := by
      have : u * u⁻¹ = d ^ 3 * u * u⁻¹ := by rw [← h3]
      simpa using this.symm
    obtain ⟨k, hk⟩ := hU2 ⟨d, hdZ.1⟩
    have hd2 : d ^ (2 ^ k) = 1 := by simpa using congrArg Subtype.val hk
    have hd1 : d = 1 := orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes
      (Nat.Coprime.pow_left k (by norm_num : Nat.Coprime 2 3))
      (orderOf_dvd_of_pow_eq_one hd2) (orderOf_dvd_of_pow_eq_one hd3))
    rw [hcu, hd1, one_mul]
  have hcQ : c ∈ pCoreOf 2 (l32nH T V) := by
    rw [← hQ]
    refine ⟨hcE.1, hcE.1, fun u hu => ?_⟩
    rw [hcU u hu, mul_inv_cancel]
    exact one_mem _
  obtain ⟨k, hk⟩ := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (l32nH T V) ⟨c, hcQ⟩
  have hc2 : c ^ (2 ^ k) = 1 := by simpa using congrArg Subtype.val hk
  have hc1 : c = 1 := orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes
    (Nat.Coprime.pow_left k (by norm_num : Nat.Coprime 2 3))
    (orderOf_dvd_of_pow_eq_one hc2) (orderOf_dvd_of_pow_eq_one hc3'))
  rw [hc1, orderOf_one] at hc3
  exact absurd hc3 (by norm_num)

omit [IsMulCommutative ↥V] C in
theorem mem_of_rho_mem {K : Subgroup G} (hKH : K ≤ l32nH T V)
    (hHK : l32nH T V ≤ Subgroup.normalizer (K : Set G)) (hN3 : ¬ 3 ∣ Nat.card ↥(l32nCHat T V))
    {x : G} (hxH : x ∈ l32nH T V) (hx3 : x ^ 3 = 1)
    (hxK : D.ρ ⟨x, L14332.l32nH_le_normalizer_fsuU T V hxH⟩ ∈ D.img K) : x ∈ K := by
  obtain ⟨k, hkK, hkN, hk⟩ := (L128A.HatU.mem_img D).mp hxK
  have hkH := hKH hkK
  set c := k⁻¹ * x with hc
  have hcH : c ∈ l32nH T V := (l32nH T V).mul_mem ((l32nH T V).inv_mem hkH) hxH
  have hcN : c ∈ Subgroup.normalizer (fsuU T V : Set G) :=
    L14332.l32nH_le_normalizer_fsuU T V hcH
  have hρc : D.ρ ⟨c, hcN⟩ = 1 := by
    have e : (⟨c, hcN⟩ : ↥(Subgroup.normalizer (fsuU T V : Set G))) =
        (⟨k, hkN⟩ : ↥(Subgroup.normalizer (fsuU T V : Set G)))⁻¹ *
          ⟨x, L14332.l32nH_le_normalizer_fsuU T V hxH⟩ := rfl
    rw [e, map_mul, map_inv, hk, inv_mul_cancel]
  have hcE : c ∈ l32nCHat T V := (L14332.rho_eq_one_iff_mem hcH hcN).mp hρc
  have hc3 : c ^ 3 ∈ K := by
    have e : c ^ 3 = k⁻¹ * (x * k⁻¹ * x⁻¹) * (x * x * k⁻¹ * x⁻¹ * x⁻¹) * x ^ 3 := by
      rw [hc, pow_three, pow_three]
      group
    rw [e, hx3, mul_one]
    have h1 : x * k⁻¹ * x⁻¹ ∈ K :=
      (Subgroup.mem_normalizer_iff.mp (hHK hxH) _).mp (K.inv_mem hkK)
    have h2 : x * x * k⁻¹ * x⁻¹ * x⁻¹ ∈ K := by
      have := (Subgroup.mem_normalizer_iff.mp (hHK hxH) _).mp h1
      rwa [show x * (x * k⁻¹ * x⁻¹) * x⁻¹ = x * x * k⁻¹ * x⁻¹ * x⁻¹ by group] at this
    exact K.mul_mem (K.mul_mem (K.inv_mem hkK) h1) h2
  have hcK := mem_of_cube_mem hN3 hcE hc3
  have : x = k * c := by rw [hc]; group
  rw [this]
  exact K.mul_mem hkK hcK

end Ctx

end L14328

end CFSG.Quasithin.H13
