module

public import CFSG.Quasithin.H13.L32NLem14413e
public import CFSG.Quasithin.H13.L32NLem1447a

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin

namespace L144B.Base

open L1447

variable {G : Type} [Group G] [Finite G] {T L V V₂ : Subgroup G} {g : G}
variable (C : Base G T L V V₂ g)
include C

theorem conj_z_mem' {z : G} (hz : z ∈ fsuV1 T V) (hz1 : z ≠ 1) :
    g⁻¹ * z * g ∈ V₂ ∧ g⁻¹ * z * g ∉ fsuV1 T V := by
  have h1 : g⁻¹ * z * g ∈ CFSG.conjugate (fsuV1 T V) g :=
    mem_conj.mpr (by simpa [mul_assoc] using hz)
  refine ⟨C.V1g_le_V2 h1, fun h => hz1 ?_⟩
  have h2 := C.eq_one_of_mem_V1_V1g h h1
  have := congrArg (fun y => g * y * g⁻¹) h2
  simpa [mul_assoc] using this

theorem mem_V_cases {z p b : G} (hz : z ∈ fsuV1 T V) (hz1 : z ≠ 1) (hp : p ∈ V₂)
    (hpV : p ∉ fsuV1 T V) (hb : b ∈ V) (hbV : b ∉ V₂) {v : G} (hv : v ∈ V) :
    v = 1 ∨ v = z ∨ v = p ∨ v = p * z ∨ v = b ∨ v = b * z ∨ v = b * p ∨ v = b * (p * z) := by
  obtain ⟨_, S⟩ := C.set14
  have hpp : p * p = 1 := S.mul_self_V (C.plane.1.1 hp)
  have hbb : b * b = 1 := S.mul_self_V hb
  have hV2 : ∀ x ∈ V₂, x = 1 ∨ x = z ∨ x = p ∨ x = p * z := by
    intro x hx
    rcases S.mem_V2 hp hpV hx with h | h
    · rcases S.eq_of_mem_V1 hz hz1 h with rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
    · rcases S.eq_of_mem_V1 hz hz1 h with h' | h'
      · refine Or.inr (Or.inr (Or.inl ?_))
        calc x = p * p * x := by rw [hpp, one_mul]
          _ = p * (p * x) := by group
          _ = p := by rw [h', mul_one]
      · refine Or.inr (Or.inr (Or.inr ?_))
        calc x = p * p * x := by rw [hpp, one_mul]
          _ = p * (p * x) := by group
          _ = p * z := by rw [h']
  rcases S.mem_V hb hbV hv with h | h
  · rcases hV2 v h with h' | h' | h' | h'
    · exact Or.inl h'
    · exact Or.inr (Or.inl h')
    · exact Or.inr (Or.inr (Or.inl h'))
    · exact Or.inr (Or.inr (Or.inr (Or.inl h')))
  · have e : v = b * (b * v) := by
      calc v = b * b * v := by rw [hbb, one_mul]
        _ = b * (b * v) := by group
    rcases hV2 _ h with h' | h' | h' | h' <;> rw [h'] at e
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by rw [e, mul_one])))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl e)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl e))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr e))))))

theorem fix_V {z p b x : G} (hz : z ∈ fsuV1 T V) (hz1 : z ≠ 1) (hp : p ∈ V₂)
    (hpV : p ∉ fsuV1 T V) (hb : b ∈ V) (hbV : b ∉ V₂) (hxz : x * z * x⁻¹ = z)
    (hxp : x * p * x⁻¹ = p) (hxb : x * b * x⁻¹ = b) : ∀ v ∈ V, x * v * x⁻¹ = v := by
  have hmul : ∀ u w : G, x * u * x⁻¹ = u → x * w * x⁻¹ = w → x * (u * w) * x⁻¹ = u * w := by
    intro u w hu hw
    calc x * (u * w) * x⁻¹ = (x * u * x⁻¹) * (x * w * x⁻¹) := by group
      _ = u * w := by rw [hu, hw]
  intro v hv
  rcases C.mem_V_cases hz hz1 hp hpV hb hbV hv with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · group
  · exact hxz
  · exact hxp
  · exact hmul _ _ hxp hxz
  · exact hxb
  · exact hmul _ _ hxb hxz
  · exact hmul _ _ hxb hxp
  · exact hmul _ _ hxb (hmul _ _ hxp hxz)

theorem U_comm_cases {z : G} (hz : z ∈ fsuV1 T V) (hz1 : z ≠ 1) :
    ∀ u ∈ fsuU T V, ∀ v ∈ fsuU T V, u * v * u⁻¹ * v⁻¹ = 1 ∨ u * v * u⁻¹ * v⁻¹ = z := by
  obtain ⟨_, S⟩ := C.set14
  intro u hu v hv
  have := C.comm_center u hu v hv
  rw [C.zU] at this
  exact S.eq_of_mem_V1 hz hz1 this

theorem z_comm_U {z : G} (hz : z ∈ fsuV1 T V) : ∀ u ∈ fsuU T V, u * z = z * u := by
  intro u hu
  have hzZ : z ∈ centerOf (fsuU T V) := by rw [C.zU]; exact hz
  exact Subgroup.mem_centralizer_iff.mp hzZ.2 u hu

theorem exists_noncomm {x : G} (hxU : x ∈ fsuU T V) (hxV : x ∉ fsuV1 T V) :
    ∃ u ∈ fsuU T V, u * x * u⁻¹ * x⁻¹ ≠ 1 := by
  by_contra h
  push Not at h
  apply hxV
  rw [← C.zU]
  refine ⟨hxU, Subgroup.mem_centralizer_iff.mpr fun u hu => ?_⟩
  have := h u hu
  calc u * x = u * x * u⁻¹ * x⁻¹ * (x * u) := by group
    _ = x * u := by rw [this, one_mul]

theorem conj_mem_V {v : G} (hv : v ∈ V) : g * v * g⁻¹ ∈ V :=
  (Subgroup.mem_normalizer_iff.mp C.gV v).mp hv

theorem exists_transv' {z x y : G} (hz : z ∈ fsuV1 T V) (hz1 : z ≠ 1) (hx : x ∈ V) (hy : y ∈ V)
    (hxV : x ∉ fsuV1 T V) (hyV : y ∉ fsuV1 T V) (hxyV : x * y ∉ fsuV1 T V) :
    ∃ u ∈ fsuU T V, u * x * u⁻¹ * x⁻¹ = z ∧ u * y * u⁻¹ * y⁻¹ = 1 := by
  obtain ⟨_, S⟩ := C.set14
  exact L14413.exists_transv (C.z_comm_U hz) (S.mul_self_V (Subgroup.mem_inf.mp hz).1)
    (C.U_comm_cases hz hz1) (V_le_U hx) (V_le_U hy) (C.exists_noncomm (V_le_U hx) hxV)
    (C.exists_noncomm (V_le_U hy) hyV) (C.exists_noncomm (V_le_U (V.mul_mem hx hy)) hxyV)

theorem mem_Hg_of_fix {z l : G} (hz : z ∈ fsuV1 T V) (hz1 : z ≠ 1)
    (hl : l * (g⁻¹ * z * g) * l⁻¹ = g⁻¹ * z * g) : l ∈ CFSG.conjugate (l32nH T V) g := by
  obtain ⟨_, S⟩ := C.set14
  rw [mem_conj]
  refine S.mem_g1 hz hz1 ?_
  calc g * l * g⁻¹ * z * (g * l * g⁻¹)⁻¹ = g * (l * (g⁻¹ * z * g) * l⁻¹) * g⁻¹ := by group
    _ = z := by rw [hl]; group

theorem rconj_U_eq {z g₁ : G} (hz : z ∈ fsuV1 T V) (hz1 : z ≠ 1)
    (hg₁ : g₁⁻¹ * z * g₁ = g⁻¹ * z * g) :
    rconj (fsuU T V) g₁ = CFSG.conjugate (fsuU T V) g := by
  obtain ⟨_, S⟩ := C.set14
  have hc : g * g₁⁻¹ ∈ Subgroup.normalizer (fsuU T V : Set G) := by
    refine L14332.l32nH_le_normalizer_fsuU T V (S.mem_g1 hz hz1 ?_)
    calc g * g₁⁻¹ * z * (g * g₁⁻¹)⁻¹ = g * (g₁⁻¹ * z * g₁) * g⁻¹ := by group
      _ = z := by rw [hg₁]; group
  ext y
  rw [mem_rconj, mem_conj]
  have e : g * y * g⁻¹ = (g * g₁⁻¹) * (g₁ * y * g₁⁻¹) * (g * g₁⁻¹)⁻¹ := by group
  rw [e]
  exact Subgroup.mem_normalizer_iff.mp hc _

structure Frame (C : Base G T L V V₂ g) where
  z : G
  b : G
  g₁ : G
  l : G
  hz : z ∈ fsuV1 T V
  hz1 : z ≠ 1
  hb : b ∈ V
  hbV : b ∉ V₂
  hg₁ : g₁ ∈ L
  hl : l ∈ L
  g₁z : g₁⁻¹ * z * g₁ = g⁻¹ * z * g
  l3 : l ^ 3 = 1
  lp : l * (g⁻¹ * z * g) * l⁻¹ = g⁻¹ * z * g
  lz : l * z * l⁻¹ = b
  lb : l * b * l⁻¹ = z * b
  hV : V = fsuV1 T V ⊔ rconj (fsuV1 T V) g₁ ⊔ rconj (fsuV1 T V) l⁻¹

theorem exists_frame (h12213 : Stmt12_2_13) : Nonempty (Frame C) := by
  obtain ⟨_, S⟩ := C.set14
  obtain ⟨z, -, b, hz, hz1, -, -, hb, hbV⟩ := S.exists_basis
  obtain ⟨hpV2, hpV1⟩ := C.conj_z_mem' hz hz1
  have hzV : z ∈ V := (Subgroup.mem_inf.mp hz).1
  have hzV2 : z ∈ V₂ := C.plane.2 hz
  have hpV : g⁻¹ * z * g ∈ V := C.plane.1.1 hpV2
  have h13322 := stmt13_3_2_two_of_stmt13_3_2 C.h1332
  have hVm := stmtL32NModule_of_inputs C.h1332 C.h1334
  have h1283 := lemma12_8_3 h12213 G T L V 3 (C.hyp.hyp1281One h13322 hVm)
  have htrans : ∀ w ∈ V, w ≠ 1 → ∃ l ∈ L, l * z * l⁻¹ = w := by
    intro w hw hw1
    have hw2 : orderOf w = 2 := orderOf_eq_prime (S.sq_V hw) hw1
    obtain ⟨l, hl, hlc⟩ := h1283.2.1 1 (fsuV1 T V) (Subgroup.zpowers w) inf_le_left
      (Subgroup.zpowers_le.mpr hw) (by rw [S.card_V1]; norm_num)
      (by rw [Nat.card_zpowers, hw2]; norm_num)
    have hwc : w ∈ CFSG.conjugate (fsuV1 T V) l := hlc ▸ Subgroup.mem_zpowers w
    obtain ⟨x, hx, hxw⟩ := Subgroup.mem_map.mp hwc
    rcases S.eq_of_mem_V1 hz hz1 hx with hx1 | hxz
    · rw [hx1, map_one] at hxw
      exact absurd hxw.symm hw1
    · refine ⟨l⁻¹, inv_mem hl, ?_⟩
      rw [hxz] at hxw
      simpa using hxw
  have hp1 : g⁻¹ * z * g ≠ 1 := fun h => hpV1 (h ▸ one_mem _)
  obtain ⟨l₀, hl₀, hl₀z⟩ := htrans _ hpV hp1
  have hb1 : b ≠ 1 := fun h => hbV (h ▸ one_mem _)
  obtain ⟨l, hl, hl3, hlp, hlz, hlb⟩ := S.exists_rot hpV hzV hb hz1 hb1
    (fun h => hpV1 (h ▸ hz)) (fun h => hbV (h ▸ hpV2)) (fun h => hbV (h ▸ hzV2))
    (fun h => hbV (h ▸ V₂.mul_mem hpV2 hzV2))
  have hg₁z : l₀⁻¹⁻¹ * z * l₀⁻¹ = g⁻¹ * z * g := by simpa using hl₀z
  refine ⟨⟨z, b, l₀⁻¹, l, hz, hz1, hb, hbV, inv_mem hl₀, hl, hg₁z, hl3, hlp, hlz, hlb, ?_⟩⟩
  have hLV : ∀ k ∈ L, ∀ v ∈ V, k * v * k⁻¹ ∈ V := fun k hk v hv =>
    (Subgroup.mem_normalizer_iff.mp (S.LV hk) v).mp hv
  refine le_antisymm (fun v hv => ?_) (sup_le (sup_le inf_le_left fun x hx => ?_) fun x hx => ?_)
  · have hz' : z ∈ fsuV1 T V ⊔ rconj (fsuV1 T V) l₀⁻¹ ⊔ rconj (fsuV1 T V) l⁻¹ :=
      Subgroup.mem_sup_left (Subgroup.mem_sup_left hz)
    have hp' : g⁻¹ * z * g ∈ fsuV1 T V ⊔ rconj (fsuV1 T V) l₀⁻¹ ⊔ rconj (fsuV1 T V) l⁻¹ := by
      refine Subgroup.mem_sup_left (Subgroup.mem_sup_right (mem_rconj.mpr ?_))
      rw [← hg₁z]
      simpa [mul_assoc] using hz
    have hb' : b ∈ fsuV1 T V ⊔ rconj (fsuV1 T V) l₀⁻¹ ⊔ rconj (fsuV1 T V) l⁻¹ := by
      refine Subgroup.mem_sup_right (mem_rconj.mpr ?_)
      rw [← hlz]
      simpa [mul_assoc] using hz
    rcases C.mem_V_cases hz hz1 hpV2 hpV1 hb hbV hv with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact one_mem _
    · exact hz'
    · exact hp'
    · exact mul_mem hp' hz'
    · exact hb'
    · exact mul_mem hb' hz'
    · exact mul_mem hb' hp'
    · exact mul_mem hb' (mul_mem hp' hz')
  · have h1 := (Subgroup.mem_inf.mp (mem_rconj.mp hx)).1
    have := hLV _ (inv_mem (inv_mem hl₀)) _ h1
    simpa [mul_assoc] using this
  · have h1 := (Subgroup.mem_inf.mp (mem_rconj.mp hx)).1
    have := hLV _ (inv_mem (inv_mem hl)) _ h1
    simpa [mul_assoc] using this

end L144B.Base

end CFSG.Quasithin.H13
