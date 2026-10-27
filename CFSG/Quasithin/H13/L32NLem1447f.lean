module

public import CFSG.Quasithin.H13.L32NLem1447e
public import CFSG.Quasithin.EmptyFaithful.SBc8Transfer
public import CFSG.Quasithin.H13.L32NLem1447b
public import CFSG.Quasithin.H13.L32NLem1447c

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin

namespace L144B.Base

open L1447

variable {G : Type} [Group G] [Finite G] {T L V V₂ : Subgroup G} {g : G}

section

variable (C : Base G T L V V₂ g)
include C

theorem Tg_norm {t : G} (ht : t ∈ CFSG.conjugate T g) :
    t ∈ Subgroup.normalizer (V : Set G) ∧ t ∈ Subgroup.normalizer (V₂ : Set G) := by
  obtain ⟨_, S⟩ := C.set14
  have h1 : g * t * g⁻¹ ∈ T := mem_conj.mp ht
  have e : t = g⁻¹ * (g * t * g⁻¹) * g := by group
  rw [e]
  exact ⟨mul_mem (mul_mem (inv_mem C.gV) (S.TV h1)) C.gV,
    mul_mem (mul_mem (inv_mem C.gV₂) (C.plane.1.2.2 h1)) C.gV₂⟩

theorem V1g_le_dG : CFSG.conjugate (fsuV1 T V) g ≤ dG T V g := by
  intro x hx
  have h1 : g * x * g⁻¹ ∈ fsuV1 T V := mem_conj.mp hx
  have h2 : g * x * g⁻¹ ∈ centerOf (fsuU T V) := by rw [C.zU]; exact h1
  refine ⟨mem_conj.mpr (Subgroup.le_normalizer h1), Subgroup.mem_centralizer_iff.mpr
    fun u hu => ?_⟩
  have hc := Subgroup.mem_centralizer_iff.mp h2.2 _ (mem_conj.mp hu)
  calc u * x = g⁻¹ * ((g * u * g⁻¹) * (g * x * g⁻¹)) * g := by group
    _ = g⁻¹ * ((g * x * g⁻¹) * (g * u * g⁻¹)) * g := by rw [hc]
    _ = x * u := by group

end

namespace Frame

variable {C : Base G T L V V₂ g} (F : Frame C)
include F

theorem mem_V2_cases {v : G} (hv : v ∈ V₂) :
    v = 1 ∨ v = F.z ∨ v = g⁻¹ * F.z * g ∨ v = g⁻¹ * F.z * g * F.z := by
  obtain ⟨_, S⟩ := C.set14
  obtain ⟨hp, hpV⟩ := C.conj_z_mem' F.hz F.hz1
  have hpp : g⁻¹ * F.z * g * (g⁻¹ * F.z * g) = 1 := S.mul_self_V (C.plane.1.1 hp)
  rcases S.mem_V2 hp hpV hv with h | h
  · rcases S.eq_of_mem_V1 F.hz F.hz1 h with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
  · rcases S.eq_of_mem_V1 F.hz F.hz1 h with h' | h'
    · refine Or.inr (Or.inr (Or.inl ?_))
      calc v = g⁻¹ * F.z * g * (g⁻¹ * F.z * g) * v := by rw [hpp, one_mul]
        _ = g⁻¹ * F.z * g * (g⁻¹ * F.z * g * v) := by group
        _ = g⁻¹ * F.z * g := by rw [h', mul_one]
    · refine Or.inr (Or.inr (Or.inr ?_))
      calc v = g⁻¹ * F.z * g * (g⁻¹ * F.z * g) * v := by rw [hpp, one_mul]
        _ = g⁻¹ * F.z * g * (g⁻¹ * F.z * g * v) := by group
        _ = g⁻¹ * F.z * g * F.z := by rw [h']

theorem Ug_le_I : CFSG.conjugate (fsuU T V) g ≤ F.iG := by
  rw [← F.Ug₁]
  show rconj (fsuU T V) F.g₁ ≤ fsuU T V ⊔ rconj (fsuU T V) F.g₁ ⊔ rconj (fsuU T V) F.l⁻¹
  exact le_sup_right.trans le_sup_left

theorem W_le_I : l32nW T V V₂ ≤ F.iG := fun _ hw =>
  (le_sup_left.trans le_sup_left : fsuU T V ≤ F.iG) hw.1

theorem exists_uA : ∃ u ∈ CFSG.conjugate (fsuU T V) g, u * F.z * u⁻¹ = g⁻¹ * F.z * g * F.z ∧
    u * F.b * u⁻¹ = F.b ∧ u * (g⁻¹ * F.z * g) * u⁻¹ = g⁻¹ * F.z * g := by
  obtain ⟨_, S⟩ := C.set14
  have hzV : F.z ∈ V := (Subgroup.mem_inf.mp F.hz).1
  have hzV2 : F.z ∈ V₂ := C.plane.2 F.hz
  have hx : g * F.z * g⁻¹ ∉ fsuV1 T V := by
    intro h
    rcases S.eq_of_mem_V1 F.hz F.hz1 h with h1 | h1
    · apply F.hz1
      have := congrArg (fun y => g⁻¹ * y * g) h1
      simpa [mul_assoc] using this
    · exact C.gH (S.mem_g1 F.hz F.hz1 h1)
  have hnot : ∀ {v : G}, v ∉ V₂ → g * v * g⁻¹ ∉ fsuV1 T V := by
    intro v hv h
    apply hv
    have := C.V1g_le_V2 (mem_conj.mpr h)
    exact this
  obtain ⟨u, hu, h1, h2⟩ := C.exists_transv' F.hz F.hz1 (C.conj_mem_V hzV) (C.conj_mem_V F.hb)
    hx (hnot F.hbV) (by
      have : g * F.z * g⁻¹ * (g * F.b * g⁻¹) = g * (F.z * F.b) * g⁻¹ := by group
      rw [this]
      exact hnot fun h => F.hbV (by simpa using V₂.mul_mem (V₂.inv_mem hzV2) h))
  refine ⟨g⁻¹ * u * g, mem_conj.mpr (by simpa [mul_assoc] using hu), ?_, ?_, ?_⟩
  · have e : u * (g * F.z * g⁻¹) * u⁻¹ = F.z * (g * F.z * g⁻¹) := by
      calc u * (g * F.z * g⁻¹) * u⁻¹ =
          u * (g * F.z * g⁻¹) * u⁻¹ * (g * F.z * g⁻¹)⁻¹ * (g * F.z * g⁻¹) := by group
        _ = F.z * (g * F.z * g⁻¹) := by rw [h1]
    calc g⁻¹ * u * g * F.z * (g⁻¹ * u * g)⁻¹ = g⁻¹ * (u * (g * F.z * g⁻¹) * u⁻¹) * g := by group
      _ = g⁻¹ * F.z * g * F.z := by rw [e]; group
  · have e : u * (g * F.b * g⁻¹) * u⁻¹ = g * F.b * g⁻¹ := by
      calc u * (g * F.b * g⁻¹) * u⁻¹ =
          u * (g * F.b * g⁻¹) * u⁻¹ * (g * F.b * g⁻¹)⁻¹ * (g * F.b * g⁻¹) := by group
        _ = g * F.b * g⁻¹ := by rw [h2, one_mul]
    calc g⁻¹ * u * g * F.b * (g⁻¹ * u * g)⁻¹ = g⁻¹ * (u * (g * F.b * g⁻¹) * u⁻¹) * g := by group
      _ = F.b := by rw [e]; group
  · have e : u * F.z * u⁻¹ = F.z := by
      rw [C.z_comm_U F.hz u hu]
      group
    calc g⁻¹ * u * g * (g⁻¹ * F.z * g) * (g⁻¹ * u * g)⁻¹ = g⁻¹ * (u * F.z * u⁻¹) * g := by group
      _ = g⁻¹ * F.z * g := by rw [e]

theorem exists_uB : ∃ u ∈ CFSG.conjugate (fsuU T V) g, u * F.b * u⁻¹ = g⁻¹ * F.z * g * F.b ∧
    u * F.z * u⁻¹ = F.z ∧ u * (g⁻¹ * F.z * g) * u⁻¹ = g⁻¹ * F.z * g := by
  obtain ⟨_, S⟩ := C.set14
  have hzV : F.z ∈ V := (Subgroup.mem_inf.mp F.hz).1
  have hzV2 : F.z ∈ V₂ := C.plane.2 F.hz
  have hx : g * F.z * g⁻¹ ∉ fsuV1 T V := by
    intro h
    rcases S.eq_of_mem_V1 F.hz F.hz1 h with h1 | h1
    · apply F.hz1
      have := congrArg (fun y => g⁻¹ * y * g) h1
      simpa [mul_assoc] using this
    · exact C.gH (S.mem_g1 F.hz F.hz1 h1)
  have hnot : ∀ {v : G}, v ∉ V₂ → g * v * g⁻¹ ∉ fsuV1 T V := fun hv h =>
    hv (C.V1g_le_V2 (mem_conj.mpr h))
  obtain ⟨u, hu, h1, h2⟩ := C.exists_transv' F.hz F.hz1 (C.conj_mem_V F.hb) (C.conj_mem_V hzV)
    (hnot F.hbV) hx (by
      have : g * F.b * g⁻¹ * (g * F.z * g⁻¹) = g * (F.b * F.z) * g⁻¹ := by group
      rw [this]
      exact hnot fun h => F.hbV (by simpa using V₂.mul_mem h (V₂.inv_mem hzV2)))
  refine ⟨g⁻¹ * u * g, mem_conj.mpr (by simpa [mul_assoc] using hu), ?_, ?_, ?_⟩
  · have e : u * (g * F.b * g⁻¹) * u⁻¹ = F.z * (g * F.b * g⁻¹) := by
      calc u * (g * F.b * g⁻¹) * u⁻¹ =
          u * (g * F.b * g⁻¹) * u⁻¹ * (g * F.b * g⁻¹)⁻¹ * (g * F.b * g⁻¹) := by group
        _ = F.z * (g * F.b * g⁻¹) := by rw [h1]
    calc g⁻¹ * u * g * F.b * (g⁻¹ * u * g)⁻¹ = g⁻¹ * (u * (g * F.b * g⁻¹) * u⁻¹) * g := by group
      _ = g⁻¹ * F.z * g * F.b := by rw [e]; group
  · have e : u * (g * F.z * g⁻¹) * u⁻¹ = g * F.z * g⁻¹ := by
      calc u * (g * F.z * g⁻¹) * u⁻¹ =
          u * (g * F.z * g⁻¹) * u⁻¹ * (g * F.z * g⁻¹)⁻¹ * (g * F.z * g⁻¹) := by group
        _ = g * F.z * g⁻¹ := by rw [h2, one_mul]
    calc g⁻¹ * u * g * F.z * (g⁻¹ * u * g)⁻¹ = g⁻¹ * (u * (g * F.z * g⁻¹) * u⁻¹) * g := by group
      _ = F.z := by rw [e]; group
  · have e : u * F.z * u⁻¹ = F.z := by
      rw [C.z_comm_U F.hz u hu]
      group
    calc g⁻¹ * u * g * (g⁻¹ * F.z * g) * (g⁻¹ * u * g)⁻¹ = g⁻¹ * (u * F.z * u⁻¹) * g := by group
      _ = g⁻¹ * F.z * g := by rw [e]

theorem exists_wC : ∃ w ∈ l32nW T V V₂, w * F.b * w⁻¹ = F.z * F.b ∧ w * F.z * w⁻¹ = F.z ∧
    w * (g⁻¹ * F.z * g) * w⁻¹ = g⁻¹ * F.z * g := by
  obtain ⟨_, S⟩ := C.set14
  obtain ⟨hp, hpV⟩ := C.conj_z_mem' F.hz F.hz1
  have hbV1 : F.b ∉ fsuV1 T V := fun h => F.hbV (C.plane.2 h)
  obtain ⟨w, hw, h1, h2⟩ := C.exists_transv' F.hz F.hz1 F.hb (C.plane.1.1 hp) hbV1 hpV
    (fun h => F.hbV (by
      have := V₂.mul_mem (C.plane.2 h) (V₂.inv_mem hp)
      rwa [mul_inv_cancel_right] at this))
  have hwz : w * F.z * w⁻¹ = F.z := by
    rw [C.z_comm_U F.hz w hw]
    group
  have hwp : w * (g⁻¹ * F.z * g) * w⁻¹ = g⁻¹ * F.z * g := by
    calc w * (g⁻¹ * F.z * g) * w⁻¹ =
        w * (g⁻¹ * F.z * g) * w⁻¹ * (g⁻¹ * F.z * g)⁻¹ * (g⁻¹ * F.z * g) := by group
      _ = g⁻¹ * F.z * g := by rw [h2, one_mul]
  have hfix : ∀ v ∈ V₂, w * v * w⁻¹ = v := by
    intro v hv
    rcases F.mem_V2_cases hv with rfl | rfl | rfl | rfl
    · group
    · exact hwz
    · exact hwp
    · calc w * (g⁻¹ * F.z * g * F.z) * w⁻¹ =
          (w * (g⁻¹ * F.z * g) * w⁻¹) * (w * F.z * w⁻¹) := by group
        _ = g⁻¹ * F.z * g * F.z := by rw [hwp, hwz]
  refine ⟨w, ⟨hw, Subgroup.mem_centralizer_iff.mpr fun v hv => ?_⟩, ?_, hwz, hwp⟩
  · calc v * w = (w * v * w⁻¹) * w := by rw [hfix v hv]
      _ = w * v := by group
  · calc w * F.b * w⁻¹ = w * F.b * w⁻¹ * F.b⁻¹ * F.b := by group
      _ = F.z * F.b := by rw [h1]

theorem exists_s₂ (hF1 : F1 T V V₂) (hF2 : F2 T V V₂ g) {c : G} (hc : c ∈ V₂) :
    ∃ s ∈ F.iG, (∀ d ∈ dG T V g, s * d = d * s) ∧ s * F.z * s⁻¹ = F.z ∧
      s * (g⁻¹ * F.z * g) * s⁻¹ = g⁻¹ * F.z * g ∧ s * F.b * s⁻¹ = c * F.b := by
  obtain ⟨_, S⟩ := C.set14
  obtain ⟨u, hu, hub, huz, hup⟩ := F.exists_uB
  obtain ⟨w, hw, hwb, hwz, hwp⟩ := F.exists_wC
  have hcomm_u : ∀ d ∈ dG T V g, u * d = d * u := fun d hd =>
    Subgroup.mem_centralizer_iff.mp hd.2 u hu
  have hcomm_w : ∀ d ∈ dG T V g, w * d = d * w := fun d hd => (C.dG_comm_W hF1 hF2 hd hw).symm
  rcases F.mem_V2_cases hc with rfl | rfl | rfl | rfl
  · exact ⟨1, one_mem _, fun d _ => by group, by group, by group, by group⟩
  · exact ⟨w, F.W_le_I hw, hcomm_w, hwz, hwp, hwb⟩
  · exact ⟨u, F.Ug_le_I hu, hcomm_u, huz, hup, hub⟩
  · refine ⟨u * w, mul_mem (F.Ug_le_I hu) (F.W_le_I hw), fun d hd => ?_, ?_, ?_, ?_⟩
    · calc u * w * d = u * (w * d) := by group
        _ = u * (d * w) := by rw [hcomm_w d hd]
        _ = (u * d) * w := by group
        _ = d * u * w := by rw [hcomm_u d hd]
        _ = d * (u * w) := by group
    · calc u * w * F.z * (u * w)⁻¹ = u * (w * F.z * w⁻¹) * u⁻¹ := by group
        _ = F.z := by rw [hwz, huz]
    · have e : u * w * (g⁻¹ * F.z * g) * (u * w)⁻¹ = u * (w * (g⁻¹ * F.z * g) * w⁻¹) * u⁻¹ := by
        group
      rw [e, hwp, hup]
    · have hpV := C.plane.1.1 (C.conj_z_mem' F.hz F.hz1).1
      have hzV : F.z ∈ V := (Subgroup.mem_inf.mp F.hz).1
      calc u * w * F.b * (u * w)⁻¹ = (u * F.z * u⁻¹) * (u * F.b * u⁻¹) := by
            rw [show u * w * F.b * (u * w)⁻¹ = u * (w * F.b * w⁻¹) * u⁻¹ by group, hwb]
            group
        _ = F.z * (g⁻¹ * F.z * g * F.b) := by rw [huz, hub]
        _ = (F.z * (g⁻¹ * F.z * g)) * F.b := by group
        _ = (g⁻¹ * F.z * g * F.z) * F.b := by rw [S.comm_V hzV hpV]

theorem exists_s₁ {c : G} (hc : c = F.z ∨ c = g⁻¹ * F.z * g * F.z) :
    ∃ s ∈ F.iG, (∀ d ∈ dG T V g, s * d = d * s) ∧ s * F.z * s⁻¹ = c ∧
      s * (g⁻¹ * F.z * g) * s⁻¹ = g⁻¹ * F.z * g ∧ s * F.b * s⁻¹ = F.b := by
  rcases hc with rfl | rfl
  · exact ⟨1, one_mem _, fun d _ => by group, by group, by group, by group⟩
  · obtain ⟨u, hu, huz, hub, hup⟩ := F.exists_uA
    exact ⟨u, F.Ug_le_I hu, fun d hd => Subgroup.mem_centralizer_iff.mp hd.2 u hu, huz, hup, hub⟩

theorem Tg_fix_p {t : G} (ht : t ∈ CFSG.conjugate T g) :
    t * (g⁻¹ * F.z * g) * t⁻¹ = g⁻¹ * F.z * g := by
  obtain ⟨_, S⟩ := C.set14
  have h1 : g * t * g⁻¹ ∈ l32nH T V := mem_conj.mp (C.Tg_le_Hg ht)
  rw [l32nH, normalizer_eq_centralizer_of_card_eq_two S.card_V1] at h1
  have h2 := Subgroup.mem_centralizer_iff.mp h1 F.z F.hz
  calc t * (g⁻¹ * F.z * g) * t⁻¹ = g⁻¹ * ((g * t * g⁻¹) * F.z) * (g * t * g⁻¹)⁻¹ * g := by group
    _ = g⁻¹ * (F.z * (g * t * g⁻¹)) * (g * t * g⁻¹)⁻¹ * g := by rw [h2]
    _ = g⁻¹ * F.z * g := by group

theorem sylow_comm (h12213 : Stmt12_2_13) (hF1 : F1 T V V₂) (hF2 : F2 T V V₂ g) {t : G}
    (ht : t ∈ CFSG.conjugate T g ⊓ F.iG) {d : G} (hd : d ∈ dG T V g) : t * d = d * t := by
  obtain ⟨_, S⟩ := C.set14
  obtain ⟨htT, htI⟩ := Subgroup.mem_inf.mp ht
  obtain ⟨hp, hpV⟩ := C.conj_z_mem' F.hz F.hz1
  have hzV2 : F.z ∈ V₂ := C.plane.2 F.hz
  have htp := F.Tg_fix_p htT
  obtain ⟨htV, htV2⟩ := C.Tg_norm htT
  have hIN := F.I_le_NV h12213
  have htz : t * F.z * t⁻¹ = F.z ∨ t * F.z * t⁻¹ = g⁻¹ * F.z * g * F.z := by
    rcases F.mem_V2_cases ((Subgroup.mem_normalizer_iff.mp htV2 _).mp hzV2) with h | h | h | h
    · exfalso
      apply F.hz1
      have := congrArg (fun y => t⁻¹ * y * t) h
      simpa [mul_assoc] using this
    · exact Or.inl h
    · exfalso
      apply hpV
      have h' : F.z = g⁻¹ * F.z * g := by
        calc F.z = t⁻¹ * (t * F.z * t⁻¹) * t := by group
          _ = t⁻¹ * (t * (g⁻¹ * F.z * g) * t⁻¹) * t := by rw [h, htp]
          _ = g⁻¹ * F.z * g := by group
      rw [← h']
      exact F.hz
    · exact Or.inr h
  obtain ⟨s₁, hs₁I, hs₁d, hs₁z, hs₁p, hs₁b⟩ := F.exists_s₁ htz
  set t₁ := s₁⁻¹ * t with ht₁
  have ht₁z : t₁ * F.z * t₁⁻¹ = F.z := by
    calc t₁ * F.z * t₁⁻¹ = s₁⁻¹ * (t * F.z * t⁻¹) * s₁ := by rw [ht₁]; group
      _ = s₁⁻¹ * (s₁ * F.z * s₁⁻¹) * s₁ := by rw [hs₁z]
      _ = F.z := by group
  have ht₁p : t₁ * (g⁻¹ * F.z * g) * t₁⁻¹ = g⁻¹ * F.z * g := by
    calc t₁ * (g⁻¹ * F.z * g) * t₁⁻¹ = s₁⁻¹ * (t * (g⁻¹ * F.z * g) * t⁻¹) * s₁ := by
          rw [ht₁]; group
      _ = s₁⁻¹ * (s₁ * (g⁻¹ * F.z * g) * s₁⁻¹) * s₁ := by rw [htp, hs₁p]
      _ = g⁻¹ * F.z * g := by group
  have ht₁V : t₁ ∈ Subgroup.normalizer (V : Set G) := mul_mem (inv_mem (hIN hs₁I)) htV
  have ht₁V2 : ∀ v ∈ V₂, t₁ * v * t₁⁻¹ = v := by
    intro v hv
    rcases F.mem_V2_cases hv with rfl | rfl | rfl | rfl
    · group
    · exact ht₁z
    · exact ht₁p
    · calc t₁ * (g⁻¹ * F.z * g * F.z) * t₁⁻¹ =
          (t₁ * (g⁻¹ * F.z * g) * t₁⁻¹) * (t₁ * F.z * t₁⁻¹) := by group
        _ = g⁻¹ * F.z * g * F.z := by rw [ht₁p, ht₁z]
  have hbV : t₁ * F.b * t₁⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.mp ht₁V _).mp F.hb
  have hnot : t₁ * F.b * t₁⁻¹ ∉ V₂ := fun h => F.hbV (by
    have := ht₁V2 _ h
    have e : F.b = t₁⁻¹ * (t₁ * F.b * t₁⁻¹) * t₁ := by group
    rw [e, show t₁⁻¹ * (t₁ * F.b * t₁⁻¹) * t₁ = t₁ * F.b * t₁⁻¹ by
      calc t₁⁻¹ * (t₁ * F.b * t₁⁻¹) * t₁ = t₁⁻¹ * (t₁ * (t₁ * F.b * t₁⁻¹) * t₁⁻¹) * t₁ := by
            rw [this]
        _ = t₁ * F.b * t₁⁻¹ := by group]
    exact h)
  have hc := (S.mem_V F.hb F.hbV hbV).resolve_left hnot
  obtain ⟨s₂, hs₂I, hs₂d, hs₂z, hs₂p, hs₂b⟩ := F.exists_s₂ hF1 hF2 hc
  have hbb : F.b * F.b = 1 := S.mul_self_V F.hb
  have hcb : F.b * (t₁ * F.b * t₁⁻¹) * F.b = t₁ * F.b * t₁⁻¹ := by
    calc F.b * (t₁ * F.b * t₁⁻¹) * F.b = (t₁ * F.b * t₁⁻¹) * F.b * F.b := by
          rw [S.comm_V F.hb hbV]
      _ = t₁ * F.b * t₁⁻¹ := by rw [mul_assoc, hbb, mul_one]
  set x := s₂⁻¹ * t₁ with hx
  have hxz : x * F.z * x⁻¹ = F.z := by
    calc x * F.z * x⁻¹ = s₂⁻¹ * (t₁ * F.z * t₁⁻¹) * s₂ := by rw [hx]; group
      _ = s₂⁻¹ * (s₂ * F.z * s₂⁻¹) * s₂ := by rw [ht₁z, hs₂z]
      _ = F.z := by group
  have hxp : x * (g⁻¹ * F.z * g) * x⁻¹ = g⁻¹ * F.z * g := by
    calc x * (g⁻¹ * F.z * g) * x⁻¹ = s₂⁻¹ * (t₁ * (g⁻¹ * F.z * g) * t₁⁻¹) * s₂ := by
          rw [hx]; group
      _ = s₂⁻¹ * (s₂ * (g⁻¹ * F.z * g) * s₂⁻¹) * s₂ := by rw [ht₁p, hs₂p]
      _ = g⁻¹ * F.z * g := by group
  have hxb : x * F.b * x⁻¹ = F.b := by
    calc x * F.b * x⁻¹ = s₂⁻¹ * (t₁ * F.b * t₁⁻¹) * s₂ := by rw [hx]; group
      _ = s₂⁻¹ * (F.b * (t₁ * F.b * t₁⁻¹) * F.b) * s₂ := by rw [hcb]
      _ = s₂⁻¹ * (s₂ * F.b * s₂⁻¹) * s₂ := by rw [hs₂b]
      _ = F.b := by group
  have hxI : x ∈ F.iG := mul_mem (inv_mem hs₂I) (mul_mem (inv_mem hs₁I) htI)
  have hxO := F.mem_O2_of_cent h12213 hxI (C.fix_V F.hz F.hz1 hp hpV F.hb F.hbV hxz hxp hxb)
  have hxd := F.O2_comm h12213 hF1 hF2 hd hxO
  have ht' : t = s₁ * (s₂ * x) := by rw [hx, ht₁]; group
  rw [ht']
  calc s₁ * (s₂ * x) * d = s₁ * (s₂ * (x * d)) := by group
    _ = s₁ * (s₂ * (d * x)) := by rw [hxd]
    _ = s₁ * ((s₂ * d) * x) := by group
    _ = s₁ * ((d * s₂) * x) := by rw [hs₂d d hd]
    _ = (s₁ * d) * (s₂ * x) := by group
    _ = (d * s₁) * (s₂ * x) := by rw [hs₁d d hd]
    _ = d * (s₁ * (s₂ * x)) := by group

theorem sylow_odd (h12213 : Stmt12_2_13) :
    ¬ 2 ∣ (CFSG.conjugate T g ⊓ F.iG).relIndex F.iG := by
  obtain ⟨_, S⟩ := C.set14
  set Tg := CFSG.conjugate T g with hTg
  have hTgLT : Tg ≤ L ⊔ T := C.sup_conj_T ▸ le_sup_right
  have hLTN : L ⊔ T ≤ Subgroup.normalizer (F.iG : Set G) := by
    rw [F.I_eq h12213]
    refine sup_le (le_sup_left.trans Subgroup.le_normalizer) ?_
    exact CFSG.LieType.Steinberg.le_normalizer_sup S.TL
      (C.TH.trans (L14332.l32nH_le_normalizer_fsuU T V))
  have h1 := L32NSet14.card_sup_mul_card_inf (hTgLT.trans hLTN)
  have h2 := Subgroup.relIndex_mul_card (Tg ⊓ F.iG) F.iG
  rw [inf_assoc, inf_idem] at h2
  have h3 := Subgroup.relIndex_mul_card Tg (Tg ⊔ F.iG)
  rw [inf_sup_self] at h3
  have h4 := Subgroup.relIndex_mul_index (le_sup_left : Tg ≤ Tg ⊔ F.iG)
  have hidx : Tg.index = T.index := Subgroup.index_map_equiv _ (MulAut.conj g⁻¹)
  have hT := C.hyp.fsu.sylow.2
  have hpos1 : 0 < Nat.card Tg := Nat.card_pos
  have hpos2 : 0 < Nat.card ↥(Tg ⊓ F.iG) := Nat.card_pos
  have heq : (Tg ⊓ F.iG).relIndex F.iG = Tg.relIndex (Tg ⊔ F.iG) := by
    have e : (Tg ⊓ F.iG).relIndex F.iG * (Nat.card ↥(Tg ⊓ F.iG) * Nat.card Tg) =
        Tg.relIndex (Tg ⊔ F.iG) * (Nat.card ↥(Tg ⊓ F.iG) * Nat.card Tg) := by
      calc (Tg ⊓ F.iG).relIndex F.iG * (Nat.card ↥(Tg ⊓ F.iG) * Nat.card Tg) =
          Nat.card F.iG * Nat.card Tg := by rw [← h2]; ring
        _ = Nat.card ↥(Tg ⊔ F.iG) * Nat.card ↥(Tg ⊓ F.iG) := by rw [h1]; ring
        _ = Tg.relIndex (Tg ⊔ F.iG) * (Nat.card ↥(Tg ⊓ F.iG) * Nat.card Tg) := by
          rw [← h3]; ring
    exact Nat.eq_of_mul_eq_mul_right (Nat.mul_pos hpos2 hpos1) e
  rw [heq]
  intro h
  apply hT
  rw [← hidx, ← h4]
  exact Dvd.dvd.mul_right h _

theorem dG_le_V (h12213 : Stmt12_2_13) (hF1 : F1 T V V₂) (hF2 : F2 T V V₂ g)
    (hF3 : F3 T V V₂ g⁻¹) : dG T V g ≤ V := by
  obtain ⟨_, S⟩ := C.set14
  obtain ⟨hp, hpV⟩ := C.conj_z_mem' F.hz F.hz1
  have hpV' : g⁻¹ * F.z * g ∈ V := C.plane.1.1 hp
  have hzV : F.z ∈ V := (Subgroup.mem_inf.mp F.hz).1
  intro d hd
  have hV2grp : IsPGroup 2 V := fun v => ⟨1, Subtype.ext (by
    simpa [pow_one, sq] using S.mul_self_V v.2)⟩
  obtain ⟨m, hm, hc⟩ := SBc8.exists_mul_centralizer_of_cocycle (L := F.iG)
    (P := CFSG.conjugate T g ⊓ F.iG) (W := V) (d := d) (F.I_le_NV h12213)
    (fun x hx y hy => S.comm_V hx hy) hV2grp inf_le_right (F.sylow_odd h12213)
    (fun w hw => by rw [C.dG_comm_V hd hw]; group)
    (fun x hx => F.comm_mem_V hF1 hF2 hd hx)
    (fun t ht => by rw [F.sylow_comm h12213 hF1 hF2 ht hd]; group)
  have hLI : L ≤ F.iG := by rw [F.I_eq h12213]; exact le_sup_left
  have hlc := hc F.l (hLI F.hl)
  have hd' : F.l * d * F.l⁻¹ ∈ dG T V g := dG_normal F.l_mem_Hg hd
  have hlN : F.l ∈ Subgroup.normalizer (V : Set G) := S.LV F.hl
  have hk : (F.l * m⁻¹ * F.l⁻¹) * m ∈ CFSG.conjugate (fsuV1 T V) g := by
    have hkD : (F.l * m⁻¹ * F.l⁻¹) * m ∈ dG T V g := by
      have e : (F.l * m⁻¹ * F.l⁻¹) * m = (F.l * d * F.l⁻¹)⁻¹ * d := by
        have := hlc
        calc (F.l * m⁻¹ * F.l⁻¹) * m = (F.l * d * F.l⁻¹)⁻¹ * (F.l * (d * m⁻¹) * F.l⁻¹) * m := by
              group
          _ = (F.l * d * F.l⁻¹)⁻¹ * (d * m⁻¹) * m := by rw [this]
          _ = (F.l * d * F.l⁻¹)⁻¹ * d := by group
      rw [e]
      exact mul_mem (inv_mem hd') hd
    have hkV : (F.l * m⁻¹ * F.l⁻¹) * m ∈ V :=
      mul_mem ((Subgroup.mem_normalizer_iff.mp hlN _).mp (inv_mem hm)) hm
    exact C.mem_V1g_of_mem_V hkD hkV
  have hlm : F.l * m * F.l⁻¹ = m := by
    have h1 := mem_conj.mp hk
    rcases S.eq_of_mem_V1 F.hz F.hz1 h1 with h2 | h2
    · have h3 : (F.l * m⁻¹ * F.l⁻¹) * m = 1 := by
        have := congrArg (fun y => g⁻¹ * y * g) h2
        simpa [mul_assoc] using this
      have h4 : F.l * m⁻¹ * F.l⁻¹ = m⁻¹ := eq_inv_of_mul_eq_one_left h3
      calc F.l * m * F.l⁻¹ = (F.l * m⁻¹ * F.l⁻¹)⁻¹ := by group
        _ = m := by rw [h4, inv_inv]
    · exfalso
      have h3 : (F.l * m⁻¹ * F.l⁻¹) * m = g⁻¹ * F.z * g := by
        rw [← h2]
        group
      have hpp : g⁻¹ * F.z * g * (g⁻¹ * F.z * g) = 1 := S.mul_self_V hpV'
      have hmV : F.l * m * F.l⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.mp hlN _).mp hm
      have h4 : F.l * m * F.l⁻¹ = m * (g⁻¹ * F.z * g) := by
        have e1 : F.l * m⁻¹ * F.l⁻¹ = (F.l * m * F.l⁻¹)⁻¹ := by group
        rw [e1] at h3
        calc F.l * m * F.l⁻¹ = m * ((F.l * m * F.l⁻¹)⁻¹ * m)⁻¹ := by group
          _ = m * (g⁻¹ * F.z * g)⁻¹ := by rw [h3]
          _ = m * (g⁻¹ * F.z * g) := by
            rw [show (g⁻¹ * F.z * g)⁻¹ = g⁻¹ * F.z * g from inv_eq_of_mul_eq_one_right hpp]
      have e2 : F.l ^ 2 = F.l * F.l := sq F.l
      have e3 : F.l ^ 3 = F.l * (F.l * F.l) := by rw [pow_succ', sq]
      have h5 : F.l ^ 2 * m * (F.l ^ 2)⁻¹ = m := by
        calc F.l ^ 2 * m * (F.l ^ 2)⁻¹ = F.l * (F.l * m * F.l⁻¹) * F.l⁻¹ := by rw [e2]; group
          _ = F.l * (m * (g⁻¹ * F.z * g)) * F.l⁻¹ := by rw [h4]
          _ = (F.l * m * F.l⁻¹) * (F.l * (g⁻¹ * F.z * g) * F.l⁻¹) := by group
          _ = m * (g⁻¹ * F.z * g) * (g⁻¹ * F.z * g) := by rw [h4, F.lp]
          _ = m := by rw [mul_assoc, hpp, mul_one]
      have h6 : F.l ^ 3 * m * (F.l ^ 3)⁻¹ = m * (g⁻¹ * F.z * g) := by
        calc F.l ^ 3 * m * (F.l ^ 3)⁻¹ = F.l * (F.l ^ 2 * m * (F.l ^ 2)⁻¹) * F.l⁻¹ := by
              rw [e3, e2]; group
          _ = m * (g⁻¹ * F.z * g) := by rw [h5, h4]
      rw [F.l3] at h6
      have h7 : g⁻¹ * F.z * g = 1 := by
        have := congrArg (fun y => m⁻¹ * y) h6
        simpa using this.symm
      exact hpV (h7 ▸ one_mem _)
  have hmD : m ∈ dG T V g := by
    have hbV : F.b ∈ V := F.hb
    have hb1 : F.b ≠ 1 := fun h => F.hbV (h ▸ one_mem _)
    have hzb : F.b ≠ F.z := fun h => F.hbV (h ▸ C.plane.2 F.hz)
    have hcomm : ∀ {x y : G}, x ∈ V → y ∈ V → x * y = y * x := fun hx hy => S.comm_V hx hy
    have hbb : F.b * F.b = 1 := S.mul_self_V F.hb
    have hconj : ∀ u w : G, F.l * (u * w) * F.l⁻¹ = (F.l * u * F.l⁻¹) * (F.l * w * F.l⁻¹) :=
      fun u w => by group
    rcases C.mem_V_cases F.hz F.hz1 hp hpV F.hb F.hbV hm with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact one_mem _
    · exfalso
      rw [F.lz] at hlm
      exact hzb hlm
    · exact C.V1g_le_dG (mem_conj.mpr (by simpa [mul_assoc] using F.hz))
    · exfalso
      rw [hconj, F.lp, F.lz] at hlm
      exact hzb (mul_left_cancel hlm)
    · exfalso
      rw [F.lb] at hlm
      exact F.hz1 (by simpa using hlm)
    · exfalso
      rw [hconj, F.lb, F.lz, mul_assoc, hbb, mul_one] at hlm
      apply hb1
      calc F.b = F.b * F.z * F.z⁻¹ := by group
        _ = F.z * F.z⁻¹ := by rw [← hlm]
        _ = 1 := by group
    · exfalso
      rw [hconj, F.lb, F.lp] at hlm
      apply F.hz1
      have := congrArg (fun y => y * (F.b * (g⁻¹ * F.z * g))⁻¹) hlm
      simpa [mul_assoc] using this
    · exfalso
      rw [hconj, hconj, F.lb, F.lp, F.lz] at hlm
      have e1 : F.z * F.b * (g⁻¹ * F.z * g * F.b) = F.z * (g⁻¹ * F.z * g) := by
        calc F.z * F.b * (g⁻¹ * F.z * g * F.b) = F.z * (F.b * (g⁻¹ * F.z * g)) * F.b := by group
          _ = F.z * ((g⁻¹ * F.z * g) * F.b) * F.b := by rw [hcomm hbV hpV']
          _ = F.z * (g⁻¹ * F.z * g) * (F.b * F.b) := by group
          _ = F.z * (g⁻¹ * F.z * g) := by rw [hbb, mul_one]
      rw [e1, hcomm hpV' hzV] at hlm
      apply hb1
      have := congrArg (fun y => y * (F.z * (g⁻¹ * F.z * g))⁻¹) hlm
      simpa [mul_assoc] using this.symm
  have hcD : d * m⁻¹ ∈ dG T V g ⊓ Subgroup.centralizer (L : Set G) := by
    refine Subgroup.mem_inf.mpr ⟨(dG T V g).mul_mem hd ((dG T V g).inv_mem hmD),
      Subgroup.mem_centralizer_iff.mpr fun l hl => ?_⟩
    have := hc l (hLI hl)
    calc l * (d * m⁻¹) = l * (d * m⁻¹) * l⁻¹ * l := by group
      _ = d * m⁻¹ * l := by rw [this]
  rw [C.cdL_eq_bot h12213 hF1 hF2 hF3, Subgroup.mem_bot] at hcD
  have : d = m := by
    have := congrArg (fun y => y * m) hcD
    simpa using this
  rw [this]
  exact hm

end Frame

theorem fsuU_eq_pCoreOf_of_F (C : Base G T L V V₂ g) (h12213 : Stmt12_2_13) (hF1 : F1 T V V₂)
    (hF2 : F2 T V V₂ g) (hF3 : F3 T V V₂ g⁻¹) : fsuU T V = pCoreOf 2 (l32nH T V) := by
  obtain ⟨F⟩ := C.exists_frame h12213
  have hDV := F.dG_le_V h12213 hF1 hF2 hF3
  refine C.fsuU_eq_of_cent h12213 fun x hx => ?_
  obtain ⟨hxH, hxc⟩ := Subgroup.mem_inf.mp hx
  have hy : g⁻¹ * x * g ∈ dG T V g := by
    refine ⟨mem_conj.mpr (by simpa [mul_assoc] using hxH),
      Subgroup.mem_centralizer_iff.mpr fun u hu => ?_⟩
    have hc := Subgroup.mem_centralizer_iff.mp hxc _ (mem_conj.mp hu)
    calc u * (g⁻¹ * x * g) = g⁻¹ * ((g * u * g⁻¹) * x) * g := by group
      _ = g⁻¹ * (x * (g * u * g⁻¹)) * g := by rw [hc]
      _ = g⁻¹ * x * g * u := by group
  have hxV : x ∈ V := by
    have := C.conj_mem_V (hDV hy)
    simpa [mul_assoc] using this
  exact ⟨V_le_U hxV, hxc⟩

end L144B.Base

end CFSG.Quasithin.H13
