module

public import CFSG.Quasithin.H13.L32NLem1447i
public import CFSG.Quasithin.H13.L32N1449Model
public import CFSG.Quasithin.H13.L32NLem1447d

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin L14411 L144B L1442M Mat8Cert
  O3Cert Q1447Cert Q1449Cert L1447

variable {G : Type} [Group G] [Finite G] {T L V V₂ : Subgroup G} {g : G}
  {D : HatModelU (fsuU T V)}

namespace L1449

theorem mem_W_of_B (C : Base G T L V V₂ g) {a : G} (ha : a ∈ V₂) (haV : a ∉ fsuV1 T V) {t : G}
    (ht : t ∈ fsuU T V) (hB : D.B (D.π t) (D.π a) = 0) : t ∈ l32nW T V V₂ := by
  obtain ⟨_, S⟩ := C.set14
  have haU := C.V2U ha
  have hta : t * a = a * t := by
    have h1 := (D.B_spec t ht a haU).mp hB
    calc t * a = t * a * t⁻¹ * a⁻¹ * (a * t) := by group
      _ = a * t := by rw [h1, one_mul]
  have hta' : a⁻¹ * t = t * a⁻¹ := by
    calc a⁻¹ * t = a⁻¹ * (t * a) * a⁻¹ := by group
      _ = a⁻¹ * (a * t) * a⁻¹ := by rw [hta]
      _ = t * a⁻¹ := by group
  have hZ : ∀ z ∈ fsuV1 T V, z * t = t * z := fun z hz => by
    have hz' : z ∈ centerOf (fsuU T V) := by rw [C.zU]; exact hz
    exact (Subgroup.mem_centralizer_iff.mp hz'.2 t ht).symm
  refine ⟨ht, Subgroup.mem_centralizer_iff.mpr fun c' hc' => ?_⟩
  rcases S.mem_V2 ha haV hc' with h1 | h1
  · exact hZ c' h1
  · have hd := hZ _ h1
    calc c' * t = a⁻¹ * ((a * c') * t) := by group
      _ = a⁻¹ * (t * (a * c')) := by rw [hd]
      _ = (a⁻¹ * t) * (a * c') := by group
      _ = (t * a⁻¹) * (a * c') := by rw [hta']
      _ = t * c' := by group

end L1449

namespace L1447.Ctx3

variable
  {e : D.V ≃ₗ[ZMod 2] (Fin 8 → ZMod 2)} {c : ℕ} (C : Ctx3 G T L V V₂ g D e c)
include C

theorem imgW : img8 D e (CFSG.conjugate (l32nW T V V₂) g) = WW c := by
  refine le_antisymm (fun x hx => ?_) C.WW_le
  have hxP : x ∈ PP c := by
    rw [← C.imgT]
    exact img8_mono D e C.base.Wg_le_T hx
  exact mem_WW_of_comm C.hc hxP fun w hw => C.base.img_Wg_comm e x hx w (C.WW_le hw)

theorem img_L1T : img8 D e (lOne L (fsuV1 T V) ⊔ T) = MM c := by
  obtain ⟨a, ha, haV⟩ := C.base.abs.exists_mem_not_mem
  obtain ⟨l, hl, hlm⟩ := C.base.exists_L1_move (D := D) ha haV
  refine eq_MM_of C.hc ?_ ?_ ?_ (y := matOf e (D.ρ ⟨l, HN (L14411.L1H hl)⟩)) ?_ ?_
  · rw [← C.imgH]
    exact img8_mono D e C.base.L1TH
  · rw [← C.imgT]
    exact img8_mono D e le_sup_right
  · rw [C.base.card_img_L1T e, C.imgT, card_PP C.hc, mul_comm]
  · exact (mem_img8 D e).mpr ⟨l, Subgroup.mem_sup_left hl, _, rfl⟩
  · rw [← C.e_pi_a ha haV, matOf_mulVec]
    intro h
    exact hlm (e.injective h)

theorem img_L1 : img8 D e (lOne L (fsuV1 T V)) = OM c := by
  rw [C.base.L1_eq_oTwoUpper, img8_oTwoUpper D e (C.base.L1TH.trans HN), C.img_L1T,
    oTwoUpper_MM C.hc]

theorem exists_w1 {a : G} (ha : a ∈ V₂) (haV : a ∉ fsuV1 T V) :
    ∃ b ∈ V, e (D.π b) = vec8 (wS c).1 := by
  obtain ⟨⟨y, hy, hyw⟩, -, -⟩ := OM_vec_eq C.hc
  rw [← C.img_L1] at hy
  obtain ⟨l, hl, hlN, rfl⟩ := (mem_img8 D e).mp hy
  obtain ⟨_, S⟩ := C.base.set14
  have haV' : a ∈ V := C.base.plane.1.1 ha
  have hlL : l ∈ L := (Subgroup.mem_inf.mp (oTwoUpper_le _ hl)).1
  have hlV : l * a * l⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.mp (S.LV hlL) a).mp haV'
  refine ⟨a * (l * a * l⁻¹), V.mul_mem haV' hlV, ?_⟩
  rw [D.π_mul _ (C.base.V2U ha) _ (V_le_U hlV), map_add]
  have h1 : D.π (l * a * l⁻¹) = D.ρ ⟨l, hlN⟩ (D.π a) := (D.ρ_π ⟨l, hlN⟩ a (C.base.V2U ha)).symm
  rw [h1, ← matOf_mulVec, C.e_pi_a ha haV, ← hyw, add_comm]

theorem e_pi_V {v : G} (hv : v ∈ V) :
    e (D.π v) = 0 ∨ e (D.π v) = vec8 (vS c) ∨ e (D.π v) = vec8 (wS c).1 ∨
      e (D.π v) = vec8 (wS c).2 := by
  obtain ⟨_, S⟩ := C.base.set14
  obtain ⟨a, ha, haV⟩ := C.base.abs.exists_mem_not_mem
  obtain ⟨b, hb, hbw⟩ := C.exists_w1 ha haV
  obtain ⟨-, -, hw12⟩ := OM_vec_eq C.hc
  have hva := C.e_pi_a ha haV
  have hV2 : ∀ x ∈ V₂, e (D.π x) = 0 ∨ e (D.π x) = vec8 (vS c) := fun x hx => by
    rcases C.base.pi_V2 D ha haV hx with h | h
    · exact Or.inl (by rw [h, map_zero])
    · exact Or.inr (by rw [h, hva])
  have hw1 : vec8 (wS c).1 ≠ 0 ∧ vec8 (wS c).1 ≠ vec8 (vS c) := by
    have hc := C.hc
    interval_cases c <;> decide
  have hbV : b ∉ V₂ := fun h => by
    rcases hV2 b h with h' | h'
    · exact hw1.1 (hbw.symm.trans h')
    · exact hw1.2 (hbw.symm.trans h')
  have hw2 : vec8 (wS c).2 = vec8 (wS c).1 + vec8 (vS c) := by
    rw [← hw12, ← add_assoc, CharTwo.add_self_eq_zero, zero_add]
  rcases S.mem_V hb hbV hv with h | h
  · rcases hV2 v h with h' | h'
    · exact Or.inl h'
    · exact Or.inr (Or.inl h')
  · have hbv := hV2 _ h
    rw [D.π_mul _ (V_le_U hb) _ (V_le_U hv), map_add, hbw] at hbv
    rcases hbv with h' | h'
    · refine Or.inr (Or.inr (Or.inl ?_))
      exact (CharTwo.add_eq_zero.mp h').symm
    · refine Or.inr (Or.inr (Or.inr ?_))
      rw [hw2, ← h', ← add_assoc, CharTwo.add_self_eq_zero, zero_add]

theorem exists_k : ∃ k ∈ oTwoUpper (l32nH T V), ∃ hk : k ∈ Subgroup.normalizer (fsuU T V : Set G),
    G5Cert.b5V ((matOf e (D.ρ ⟨k, hk⟩) : Matrix (Fin 8) (Fin 8) (ZMod 2)).mulVec (vec8 (vS c)))
      (vec8 (vS c)) = 0 ∧
    G5Cert.b5V ((matOf e (D.ρ ⟨k, hk⟩) : Matrix (Fin 8) (Fin 8) (ZMod 2)).mulVec (vec8 (vS c)))
      (vec8 (wS c).1) = 1 := by
  obtain ⟨κ, hκ, -, hκ1, hκ2⟩ := kS_spec C.hc
  have hK : img8 D e (oTwoUpper (l32nH T V)) = omega3 := by
    rw [img8_oTwoUpper D e HN, C.imgH, C.oTwo]
  rw [← hK] at hκ
  obtain ⟨k, hk, hkN, rfl⟩ := (mem_img8 D e).mp hκ
  exact ⟨k, hk, hkN, hκ1, hκ2⟩

theorem exists_good {z : G} (hz : z ∈ fsuV1 T V) (hz1 : z ≠ 1) {x₀ : GL (Fin 8) (ZMod 2)}
    (hx₀ : colsOf (x₀ : Matrix (Fin 8) (Fin 8) (ZMod 2)) = xsS c) :
    ∃ i x : G, ∃ hi : i ∈ l32nH T V, i * i = 1 ∧ x⁻¹ * z * x = i ∧
      matOf e (D.ρ ⟨i, HN hi⟩) = x₀ := by
  obtain ⟨_, S⟩ := C.base.set14
  have B := C.base
  obtain ⟨a, ha, haV⟩ := B.abs.exists_mem_not_mem
  have haU := B.V2U ha
  have hva := C.e_pi_a ha haV
  obtain ⟨hsV₂, hsV₁⟩ := B.conj_z_mem' hz hz1
  set s := g⁻¹ * z * g with hs
  have hsU := B.V2U hsV₂
  have hvs := C.e_pi_a hsV₂ hsV₁
  have hss : s * s = 1 := S.mul_self_V (B.plane.1.1 hsV₂)
  obtain ⟨k, hk, hkN, hk1, hk2⟩ := C.exists_k
  have hkH : k ∈ l32nH T V := oTwoUpper_le _ hk
  set t := k * s * k⁻¹ with ht
  have htU : t ∈ fsuU T V := L128A.HatU.conj_mem hkN hsU
  have het : e (D.π t) = (matOf e (D.ρ ⟨k, hkN⟩) : Matrix (Fin 8) (Fin 8) (ZMod 2)).mulVec
      (vec8 (vS c)) := by
    rw [← hvs, matOf_mulVec, D.ρ_π _ s hsU]
  have htW : t ∈ l32nW T V V₂ := by
    refine L1449.mem_W_of_B (D := D) B ha haV htU ?_
    rw [C.form, het, hva]
    exact hk1
  obtain ⟨b, hb, hbw⟩ := C.exists_w1 ha haV
  have hbU : b ∈ fsuU T V := V_le_U hb
  have htb : t * b * t⁻¹ * b⁻¹ = z := by
    have h1 : t * b * t⁻¹ * b⁻¹ ∈ fsuV1 T V := by
      rw [← B.zU]
      exact B.comm_center t htU b hbU
    rcases S.eq_of_mem_V1 hz hz1 h1 with h2 | h2
    · exfalso
      have h3 := (D.B_spec t htU b hbU).mpr h2
      rw [C.form, het, hbw, hk2] at h3
      exact one_ne_zero h3
    · exact h2
  set i₀ := g⁻¹ * t * g with hi₀
  have hi₀W : i₀ ∈ CFSG.conjugate (l32nW T V V₂) g := by
    rw [mem_conj, hi₀]
    simpa [mul_assoc] using htW
  have hi₀H : i₀ ∈ l32nH T V := B.WgH hi₀W
  have hi₀i₀ : i₀ * i₀ = 1 := by
    rw [hi₀, ht]
    calc g⁻¹ * (k * s * k⁻¹) * g * (g⁻¹ * (k * s * k⁻¹) * g) = g⁻¹ * k * (s * s) * k⁻¹ * g := by
          group
      _ = 1 := by rw [hss]; group
  have hb'V : g⁻¹ * b * g ∈ V := by
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ B.gV) b).mp hb
    simpa [mul_assoc] using this
  have hib : i₀ * (g⁻¹ * b * g) * i₀⁻¹ = s * (g⁻¹ * b * g) := by
    have h1 : t * b * t⁻¹ = z * b := by
      calc t * b * t⁻¹ = t * b * t⁻¹ * b⁻¹ * b := by group
        _ = z * b := by rw [htb]
    calc i₀ * (g⁻¹ * b * g) * i₀⁻¹ = g⁻¹ * (t * b * t⁻¹) * g := by rw [hi₀]; group
      _ = g⁻¹ * (z * b) * g := by rw [h1]
      _ = s * (g⁻¹ * b * g) := by rw [hs]; group
  set ι := matOf e (D.ρ ⟨i₀, HN hi₀H⟩) with hι
  have hιW : ι ∈ WW c := by
    rw [← C.imgW]
    exact (mem_img8 D e).mpr ⟨i₀, hi₀W, _, rfl⟩
  have hι3 : ι ∉ omega3 := by
    intro h3
    rcases mem_WW C.hc hιW with ⟨-, hfv, hfw⟩ | ⟨hF, -⟩
    · have hb'U : g⁻¹ * b * g ∈ fsuU T V := V_le_U hb'V
      have h1 : ι.val.mulVec (e (D.π (g⁻¹ * b * g))) =
          vec8 (vS c) + e (D.π (g⁻¹ * b * g)) := by
        rw [hι, matOf_mulVec, D.ρ_π _ _ hb'U]
        show e (D.π (i₀ * (g⁻¹ * b * g) * i₀⁻¹)) = _
        rw [hib, D.π_mul _ hsU _ hb'U, map_add, hvs]
      have hfix : ∀ w ∈ ({0, vec8 (vS c), vec8 (wS c).1, vec8 (wS c).2} :
          Set (Fin 8 → ZMod 2)), ι.val.mulVec w = w := by
        obtain ⟨-, -, hw12⟩ := OM_vec_eq C.hc
        have hw2 : vec8 (wS c).2 = vec8 (wS c).1 + vec8 (vS c) := by
          rw [← hw12, ← add_assoc, CharTwo.add_self_eq_zero, zero_add]
        intro w hw
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
        rcases hw with rfl | rfl | rfl | rfl
        · exact Matrix.mulVec_zero _
        · exact hfv
        · exact hfw
        · rw [hw2, Matrix.mulVec_add, hfw, hfv]
      have h2 := hfix (e (D.π (g⁻¹ * b * g))) (by
        rcases C.e_pi_V hb'V with h | h | h | h <;> simp [h])
      rw [h1] at h2
      have h3 : vec8 (vS c) = 0 := by
        have := congrArg (· + e (D.π (g⁻¹ * b * g))) h2
        simpa [add_assoc, CharTwo.add_self_eq_zero] using this
      have hc := C.hc
      revert h3
      interval_cases c <;> decide
    · exact hF (omega3_le_omega3F h3)
  obtain ⟨h₀, hh₀, hh₀ι⟩ := exists_conj_x0 C.hc hx₀ hιW hι3
  rw [← C.imgH] at hh₀
  obtain ⟨h, hhH, hhN, rfl⟩ := (mem_img8 D e).mp hh₀
  refine ⟨h * i₀ * h⁻¹, (h * g⁻¹ * k * g⁻¹)⁻¹, (l32nH T V).mul_mem ((l32nH T V).mul_mem hhH hi₀H)
    ((l32nH T V).inv_mem hhH), ?_, ?_, ?_⟩
  · calc h * i₀ * h⁻¹ * (h * i₀ * h⁻¹) = h * (i₀ * i₀) * h⁻¹ := by group
      _ = 1 := by rw [hi₀i₀]; group
  · rw [hi₀, ht, hs]
    group
  · rw [← hh₀ι, hι]
    have e1 : (⟨h * i₀ * h⁻¹, HN ((l32nH T V).mul_mem ((l32nH T V).mul_mem hhH hi₀H)
        ((l32nH T V).inv_mem hhH))⟩ : ↥(Subgroup.normalizer (fsuU T V : Set G))) =
        ⟨h, hhN⟩ * ⟨i₀, HN hi₀H⟩ * ⟨h, hhN⟩⁻¹ := rfl
    rw [e1, map_mul, map_mul, map_inv, map_mul, map_mul, map_inv]

end L1447.Ctx3

end CFSG.Quasithin.H13
