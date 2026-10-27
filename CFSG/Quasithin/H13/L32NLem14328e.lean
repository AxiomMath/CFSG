module

public import CFSG.Quasithin.H13.L32NLem14328d
public import CFSG.Quasithin.H13.L32NLem14328a

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique

namespace L14328

variable {G : Type} [Group G] [Finite G] {T L V V₂ : Subgroup G} [IsMulCommutative ↥V]

omit [Finite G] [IsMulCommutative ↥V] in
theorem mem_normalizer_centralizer {X : Subgroup G} {h : G}
    (hh : h ∈ Subgroup.normalizer (X : Set G)) :
    h ∈ Subgroup.normalizer (Subgroup.centralizer (X : Set G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro k
  constructor
  · intro hk
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    have hw' : h⁻¹ * w * h⁻¹⁻¹ ∈ X :=
      (Subgroup.mem_normalizer_iff.mp ((Subgroup.normalizer _).inv_mem hh) w).mp hw
    have hc := Subgroup.mem_centralizer_iff.mp hk _ hw'
    rw [inv_inv] at hc
    calc w * (h * k * h⁻¹) = h * ((h⁻¹ * w * h) * k) * h⁻¹ := by group
      _ = h * (k * (h⁻¹ * w * h)) * h⁻¹ := by rw [hc]
      _ = h * k * h⁻¹ * w := by group
  · intro hk
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    have hw' : h * w * h⁻¹ ∈ X := (Subgroup.mem_normalizer_iff.mp hh w).mp hw
    have hc := Subgroup.mem_centralizer_iff.mp hk _ hw'
    calc w * k = h⁻¹ * ((h * w * h⁻¹) * (h * k * h⁻¹)) * h := by group
      _ = h⁻¹ * ((h * k * h⁻¹) * (h * w * h⁻¹)) * h := by rw [hc]
      _ = k * w := by group

abbrev l2 (L V₂ : Subgroup G) : Subgroup G := oTwoUpper (L ⊓ Subgroup.normalizer (V₂ : Set G))

namespace Ctx

variable {g z b l : G} (C : Ctx G T L V V₂ g z b l)
include C

theorem V_cases {v : G} (hv : v ∈ V) (hv1 : v ≠ 1) :
    v = z ∨ v = g⁻¹ * z * g ∨ v = z * (g⁻¹ * z * g) ∨ v = b ∨ v = b * z ∨
      v = b * (g⁻¹ * z * g) ∨ v = b * (z * (g⁻¹ * z * g)) := by
  rcases C.S.mem_V C.b_mem C.b_nmem hv with h | h
  · rcases C.V2_cases h hv1 with h1 | h1 | h1
    · exact Or.inl h1
    · exact Or.inr (Or.inl h1)
    · exact Or.inr (Or.inr (Or.inl h1))
  · have hbb := C.mul_self_V C.b_mem
    have e : v = b * (b * v) := by rw [← mul_assoc, hbb, one_mul]
    by_cases hbv : b * v = 1
    · right; right; right; left
      rw [e, hbv, mul_one]
    · rcases C.V2_cases h hbv with h1 | h1 | h1 <;> rw [e, h1]
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl)))))

theorem l_inv_z : l⁻¹ * z * l = z * b := by
  have hl : l⁻¹ = l * l := by
    rw [eq_comm, ← mul_eq_one_iff_eq_inv, ← pow_three', C.l3]
  rw [hl, show l * l * z * l = l * (l * z * l⁻¹) * l⁻¹ * (l * l * l) by group, C.l_z,
    ← pow_three', C.l3, mul_one, C.l_b]

theorem l_inv_a : l⁻¹ * (g⁻¹ * z * g) * l = g⁻¹ * z * g := by
  calc l⁻¹ * (g⁻¹ * z * g) * l = l⁻¹ * (l * (g⁻¹ * z * g) * l⁻¹) * l := by rw [C.l_a]
    _ = g⁻¹ * z * g := by group

theorem l_inv_b : l⁻¹ * b * l = z := by
  calc l⁻¹ * b * l = l⁻¹ * (l * z * l⁻¹) * l := by rw [C.l_z]
    _ = z := by group

theorem mem_zv_of (h1222 : Stmt12_2_2) {y : G}
    (hy : y ∈ zv V z ⊓ zv V (g⁻¹ * z * g) ⊓ zv V (z * b)) {v : G} (hv : v ∈ V) (hv1 : v ≠ 1) :
    y ∈ zv V v := by
  have hcases := C.V_cases hv hv1
  have haV₂ := C.a_mem
  have haV₁ := C.a_nmem
  have haV := C.a_V
  have hla := C.l_a
  have hlia := C.l_inv_a
  generalize g⁻¹ * z * g = a at hy hcases haV₂ haV₁ haV hla hlia
  have hzV := C.z_V
  have hbV := C.b_mem
  have hzV₂ := C.z_V₂
  have hzz := C.mul_self_V hzV
  have haa := C.mul_self_V haV
  have hbb := C.mul_self_V hbV
  have hza := C.mul_comm_V hzV haV
  have hzb := C.mul_comm_V hzV hbV
  have hab := C.mul_comm_V haV hbV
  obtain ⟨⟨hyz, hya⟩, hyzb⟩ := hy
  have hb1 : b ≠ 1 := fun h => C.b_nmem (h ▸ one_mem _)
  have hbz : b = z * (z * b) := by rw [← mul_assoc, hzz, one_mul]
  have hzb1 : z * b ≠ 1 := fun h => C.b_nmem (by rw [hbz, h, mul_one]; exact hzV₂)
  have ha1 : a ≠ 1 := fun h => haV₁ (h ▸ one_mem _)
  have hza' : z ≠ a := fun h => haV₁ (h ▸ C.z_mem)
  have hNV : (1 : G) ∈ Subgroup.normalizer (V : Set G) := one_mem _
  have hyza : y ∈ zv V (z * a) := C.zv_inf_le h1222 hNV (by simpa using hzV₂)
    (by simpa using haV₂) C.z_ne ha1 hza' ⟨hyz, hya⟩
  obtain ⟨x₁, hx₁L, -, hx₁z, hx₁a, -⟩ := C.S.exists_rot hzV haV hbV ha1 hb1 hza'.symm
    (fun h => C.b_nmem (h ▸ hzV₂)) (fun h => C.b_nmem (h ▸ haV₂))
    (fun h => C.b_nmem (h ▸ V₂.mul_mem hzV₂ haV₂))
  have hx₁N := (Subgroup.normalizer _).inv_mem (C.L_le hx₁L)
  have hx₁z' : x₁⁻¹ * z * x₁⁻¹⁻¹ = z := by
    rw [inv_inv]
    calc x₁⁻¹ * z * x₁ = x₁⁻¹ * (x₁ * z * x₁⁻¹) * x₁ := by rw [hx₁z]
      _ = z := by group
  have hx₁b : x₁⁻¹ * b * x₁ = a := by
    calc x₁⁻¹ * b * x₁ = x₁⁻¹ * (x₁ * a * x₁⁻¹) * x₁ := by rw [hx₁a]
      _ = a := by group
  have hx₁zb : x₁⁻¹ * (z * b) * x₁⁻¹⁻¹ = z * a := by
    rw [inv_inv, show x₁⁻¹ * (z * b) * x₁ = (x₁⁻¹ * z * x₁) * (x₁⁻¹ * b * x₁) by group, hx₁b]
    rw [inv_inv] at hx₁z'
    rw [hx₁z']
  have hzzb : z ≠ z * b := fun h => hb1 (by simpa using h)
  have hyb : y ∈ zv V b := by
    have := C.zv_inf_le h1222 hx₁N (by rw [hx₁z']; exact hzV₂)
      (by rw [hx₁zb]; exact V₂.mul_mem hzV₂ haV₂) C.z_ne hzb1 hzzb ⟨hyz, hyzb⟩
    rwa [← hbz] at this
  have hlN := C.L_le C.l_mem
  have hlzb : l * (z * b) * l⁻¹ = z := by
    rw [show l * (z * b) * l⁻¹ = (l * z * l⁻¹) * (l * b * l⁻¹) by group, C.l_z, C.l_b,
      ← mul_assoc, ← hzb, mul_assoc, hbb, mul_one]
  have hazb : a ≠ z * b := fun h => C.b_nmem (by rw [hbz, ← h]; exact V₂.mul_mem hzV₂ haV₂)
  have hyzab : y ∈ zv V (a * (z * b)) := C.zv_inf_le h1222 hlN (by rw [hla]; exact haV₂)
    (by rw [hlzb]; exact hzV₂) ha1 hzb1 hazb ⟨hya, hyzb⟩
  have hlN' := (Subgroup.normalizer _).inv_mem hlN
  have hla' : l⁻¹ * a * l⁻¹⁻¹ = a := by rw [inv_inv]; exact hlia
  have hlb' : l⁻¹ * b * l⁻¹⁻¹ = z := by rw [inv_inv]; exact C.l_inv_b
  have hab' : a ≠ b := fun h => C.b_nmem (h ▸ haV₂)
  have hyab : y ∈ zv V (a * b) := C.zv_inf_le h1222 hlN' (by rw [hla']; exact haV₂)
    (by rw [hlb']; exact hzV₂) ha1 hb1 hab' ⟨hya, hyb⟩
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact hyz
  · exact hya
  · exact hyza
  · exact hyb
  · rwa [← hzb]
  · rwa [← hab]
  · have e : b * (z * a) = a * (z * b) := by
      rw [← mul_assoc, ← hzb, mul_assoc, ← hab, ← mul_assoc, hza, mul_assoc]
    rwa [e]

theorem le_p128 (h1222 : Stmt12_2_2) :
    L ⊓ Subgroup.normalizer (V₂ : Set G) ≤ p128 T L V := by
  rintro c ⟨hcL, hcN⟩
  refine Subgroup.mem_inf.2 ⟨Subgroup.mem_sup_left hcL,
    Subgroup.mem_iInf.2 fun Y => Subgroup.mem_iInf.2 fun hY => ?_⟩
  obtain ⟨i, hi, hYi⟩ := hY
  rcases tinv_comparable_of_hyp1281One h1222 C.setting.hyp hYi.1 C.plane.1.1 hYi.2.2
      C.plane.1.2.2 with hle | hle
  · have heq : Y = V₂ := Subgroup.eq_of_le_of_card_ge hle (by
      rw [C.plane.1.2.1, hYi.2.1]
      exact Nat.pow_le_pow_right (by norm_num) hi)
    rw [heq]
    exact hcN
  · have h8 : Nat.card Y ≤ 8 := by
      rw [← C.S.card_V]
      exact Subgroup.card_le_of_le hYi.1
    rw [hYi.2.1] at h8
    have hi3 : i ≤ 3 := by
      by_contra h
      push Not at h
      have : 2 ^ 4 ≤ 2 ^ i := Nat.pow_le_pow_right (by norm_num) h
      omega
    interval_cases i
    · have heq : Y = V₂ := (Subgroup.eq_of_le_of_card_ge hle (by
        rw [C.plane.1.2.1, hYi.2.1])).symm
      rw [heq]
      exact hcN
    · have heq : Y = V := Subgroup.eq_of_le_of_card_ge hYi.1 (by
        rw [C.S.card_V, hYi.2.1]; norm_num)
      rw [heq]
      exact C.L_le hcL

theorem l2_le_I (h1222 : Stmt12_2_2) : l2 L V₂ ≤ i128 T L V (fsuV1 T V) := by
  rw [C.I_eq]
  exact (oTwoUpper_mono (C.le_p128 h1222)).trans le_sup_left

theorem l2_not_le : ¬ l2 L V₂ ≤ Subgroup.centralizer (V : Set G) := by
  have haV₂ := C.a_mem
  have haV₁ := C.a_nmem
  have haV := C.a_V
  generalize g⁻¹ * z * g = a at haV₂ haV₁ haV
  have ha1 : a ≠ 1 := fun h => haV₁ (h ▸ one_mem _)
  have hza' : z ≠ a := fun h => haV₁ (h ▸ C.z_mem)
  obtain ⟨x, hxL, hx3, -, hxz, hxa⟩ := C.S.exists_rot C.b_mem C.z_V haV C.z_ne ha1
    (fun h => C.b_nmem (h ▸ C.z_V₂)) (fun h => C.b_nmem (h ▸ haV₂)) hza'
    (fun h => C.b_nmem (by
      have hbz : b * z ∈ V₂ := h ▸ haV₂
      rw [show b = b * z * z by rw [mul_assoc, C.mul_self_V C.z_V, mul_one]]
      exact V₂.mul_mem hbz C.z_V₂))
  have hxN : x ∈ Subgroup.normalizer (V₂ : Set G) := by
    refine mem_normalizer_of_maps fun w hw => ?_
    rcases C.S.mem_V2 haV₂ haV₁ hw with h | h
    · rcases C.S.eq_of_mem_V1 C.z_mem C.z_ne h with rfl | rfl
      · rw [mul_one, mul_inv_cancel]
        exact one_mem _
      · rw [hxz]; exact haV₂
    · have e : w = a * (a * w) := by rw [← mul_assoc, C.mul_self_V haV, one_mul]
      rcases C.S.eq_of_mem_V1 C.z_mem C.z_ne h with h1 | h1 <;> rw [e, h1]
      · rw [mul_one, hxa]; exact V₂.mul_mem C.z_V₂ haV₂
      · rw [show x * (a * z) * x⁻¹ = (x * a * x⁻¹) * (x * z * x⁻¹) by group, hxz, hxa]
        exact V₂.mul_mem (V₂.mul_mem C.z_V₂ haV₂) haV₂
  have hxo : Odd (orderOf x) := Odd.of_dvd_nat (by decide) (orderOf_dvd_of_pow_eq_one hx3)
  intro hle
  have hc := Subgroup.mem_centralizer_iff.mp (hle (mem_oTwoUpper_of_odd ⟨hxL, hxN⟩ hxo)) z C.z_V
  apply hza'
  calc z = x * z * x⁻¹ := by rw [← hc]; group
    _ = a := hxz

theorem mem_centralizer_L (h1222 : Stmt12_2_2) {y : G}
    (hy : ∀ v ∈ V, v ≠ 1 → y ∈ zv V v) : y ∈ Subgroup.centralizer (L : Set G) := by
  have hzI := C.zI_za
  have hL2L : l2 L V₂ ≤ L := (oTwoUpper_le _).trans inf_le_left
  have hK : conjClosure (l2 L V₂) L ≤ Subgroup.centralizer ({y} : Set G) := by
    refine conjClosure_le fun h hh c hc => ?_
    have hhN := C.L_le hh
    have hhN' := (Subgroup.normalizer _).inv_mem hhN
    have hpt : ∀ v ∈ V, v ≠ 1 → h * v * h⁻¹ ∈ V ∧ h * v * h⁻¹ ≠ 1 := fun v hv hv1 =>
      ⟨(Subgroup.mem_normalizer_iff.mp hhN v).mp hv, fun h1 => hv1 (by
        calc v = h⁻¹ * (h * v * h⁻¹) * h := by group
          _ = 1 := by rw [h1]; group)⟩
    have hyI : h⁻¹ * y * h ∈ centerOf (i128 T L V (fsuV1 T V)) := by
      rw [hzI]
      have hz' := hpt z C.z_V C.z_ne
      have ha' := hpt _ C.a_V (fun h1 => C.a_nmem (h1 ▸ one_mem _))
      have h1 : y ∈ CFSG.conjugate (zv V z ⊓ zv V (g⁻¹ * z * g)) h⁻¹ := by
        rw [conjugate_inf, conjugate_zv hhN', conjugate_zv hhN', inv_inv]
        exact ⟨hy _ hz'.1 hz'.2, hy _ ha'.1 ha'.2⟩
      rw [mem_conj_iff, inv_inv] at h1
      exact h1
    have hcI := C.l2_le_I h1222 hc
    have hcomm := Subgroup.mem_centralizer_iff.mp hyI.2 c hcI
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc h * c * h⁻¹ * y = h * (c * (h⁻¹ * y * h)) * h⁻¹ := by group
      _ = h * ((h⁻¹ * y * h) * c) * h⁻¹ := by rw [hcomm]
      _ = y * (h * c * h⁻¹) := by group
  rw [C.S.conjClosure_eq hL2L C.l2_not_le] at hK
  rw [Subgroup.mem_centralizer_iff]
  intro k hk
  exact Subgroup.mem_centralizer_singleton_iff.mp (hK hk)

theorem cU_L_eq_bot (h14325 : Lemma14325One) :
    fsuU T V ⊓ Subgroup.centralizer (L : Set G) = ⊥ := by
  by_contra hne
  have hT2 : IsPGroup 2 ↥T := C.S.hH.sylow.1
  have hle : fsuU T V ⊓ Subgroup.centralizer (L : Set G) ≤ T := inf_le_left.trans C.U_T
  have hnorm : T ≤ Subgroup.normalizer
      ((fsuU T V ⊓ Subgroup.centralizer (L : Set G) : Subgroup G) : Set G) :=
    fun t ht => Subgroup.inf_normalizer_le_normalizer_inf
      ⟨C.T_U ht, mem_normalizer_centralizer (C.S.TL ht)⟩
  have : Group.IsNilpotent T := hT2.isNilpotent
  have hnormal : ((fsuU T V ⊓ Subgroup.centralizer (L : Set G)).subgroupOf T).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer hnorm
  have hne' : (fsuU T V ⊓ Subgroup.centralizer (L : Set G)).subgroupOf T ≠ ⊥ := by
    intro h
    apply hne
    rw [← Subgroup.map_subgroupOf_eq_of_le hle, h, Subgroup.map_bot]
  obtain ⟨⟨y, hy⟩, hy1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp
    (Group.IsNilpotent.inf_center_ne_bot_of_normal hne')
  have hyU : (y : G) ∈ fsuU T V := (Subgroup.mem_subgroupOf.mp hy.1).1
  have hyL : (y : G) ∈ Subgroup.centralizer (L : Set G) := (Subgroup.mem_subgroupOf.mp hy.1).2
  have hyT : (y : G) ∈ Subgroup.centralizer (T : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro t ht
    exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hy.2 ⟨t, ht⟩)
  have hyZ : (y : G) ∈ centerOf (L ⊔ T) ⊓ fsuU T V := by
    refine ⟨⟨Subgroup.mem_sup_right y.2, ?_⟩, hyU⟩
    have hLT : L ⊔ T ≤ Subgroup.centralizer ({(y : G)} : Set G) := sup_le
      (fun k hk => Subgroup.mem_centralizer_singleton_iff.mpr
        (Subgroup.mem_centralizer_iff.mp hyL k hk))
      (fun t ht => Subgroup.mem_centralizer_singleton_iff.mpr
        (Subgroup.mem_centralizer_iff.mp hyT t ht))
    show (y : G) ∈ Subgroup.centralizer ((L ⊔ T : Subgroup G) : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    exact Subgroup.mem_centralizer_singleton_iff.mp (hLT hk)
  rw [h14325 G T L V C.hyp, Subgroup.mem_bot] at hyZ
  exact hy1 (Subtype.ext (Subtype.ext hyZ))

theorem zIl_eq : CFSG.conjugate (centerOf (i128 T L V (fsuV1 T V))) l =
    CFSG.conjugate (centerOf (fsuU T V)) g ⊓ CFSG.conjugate (centerOf (fsuU T V)) l := by
  have hlN := C.L_le C.l_mem
  rw [C.zI_za, conjugate_inf, conjugate_zv hlN, conjugate_zv hlN, C.l_inv_a,
    C.conj_zU (C.P_le C.gP), C.conj_zU hlN, inf_comm]

theorem zU_inf_eq_bot (h14325 : Lemma14325One) (h1222 : Stmt12_2_2) :
    centerOf (fsuU T V) ⊓ CFSG.conjugate (centerOf (fsuU T V)) g ⊓
      CFSG.conjugate (centerOf (fsuU T V)) l = ⊥ := by
  have hlN := C.L_le C.l_mem
  rw [eq_bot_iff]
  intro y hy
  have hy' : y ∈ zv V z ⊓ zv V (g⁻¹ * z * g) ⊓ zv V (z * b) := by
    rw [C.conj_zU (C.P_le C.gP), C.conj_zU hlN, C.l_inv_z, C.zU_eq] at hy
    exact hy
  have hyL := C.mem_centralizer_L h1222 fun v hv hv1 => C.mem_zv_of h1222 hy' hv hv1
  have hyU : y ∈ fsuU T V := hy.1.1.1
  have := C.cU_L_eq_bot h14325
  rw [← this]
  exact ⟨hyU, hyL⟩

end Ctx

end L14328

end CFSG.Quasithin.H13
