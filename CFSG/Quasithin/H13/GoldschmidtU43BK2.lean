module

public import CFSG.Quasithin.H13.GoldschmidtU43BK1
public import CFSG.Quasithin.H13.GoldschmidtU43BP2

public section

namespace CFSG.Quasithin.H13.U43

open CFSG.Quasithin CFSG.Open CFSG.Quasithin.H13.A5.Orth CFSG.Quasithin.H13.A6

variable {G : Type} [Group G]

namespace Swap

variable {z t w a : G}

theorem m_notin_A0 [Finite G] (s : Swap z t w) (ha : Good z t a) : w⁻¹ * a * w ∉ A0 s ha := by
  rintro ⟨hmU, -⟩
  apply s.m_notV ha
  exact (s.mem_N1_inf_N2 _).1 ⟨⟨hmU, (s.m_mem_B ha).2⟩, m_mem_N2 ha⟩

theorem vapp_mul (g h : MulAut (Multiplicative V4)) (v : V4) :
    vapp (g * h) v = vapp g (vapp h v) := by
  unfold vapp
  rw [MulAut.mul_apply, ofAdd_toAdd]

theorem vapp_one (v : V4) : vapp (1 : MulAut (Multiplicative V4)) v = v := by
  unfold vapp
  simp

theorem theta_zt_cases (s : Swap z t w) {x : G} (hx : x ∈ Uz z) (h : x = t ∨ x = z * t) :
    s.hyp.θ ⟨x, hx⟩ = s.hyp.θ ⟨t, s.ht.1⟩ := by
  rcases h with rfl | rfl
  · rfl
  · have : (⟨z * t, hx⟩ : ↥(Uz z)) = ⟨z, s.hyp.z_mem⟩ * ⟨t, s.ht.1⟩ := rfl
    rw [this, map_mul, (s.hyp.θ_eq_one_iff _).2 (Or.inr rfl), one_mul]

theorem theta_za_cases (s : Swap z t w) (ha : Good z t a) {x : G} (hx : x ∈ Uz z)
    (h : x = a ∨ x = z * a) : s.hyp.θ ⟨x, hx⟩ = s.hyp.θ ⟨a, ha.mem.1⟩ := by
  rcases h with rfl | rfl
  · rfl
  · have : (⟨z * a, hx⟩ : ↥(Uz z)) = ⟨z, s.hyp.z_mem⟩ * ⟨a, ha.mem.1⟩ := rfl
    rw [this, map_mul, (s.hyp.θ_eq_one_iff _).2 (Or.inr rfl), one_mul]

theorem not_mem_U_of_orderOf_three [Finite G] (z : G) {σ : G} (hσ3 : orderOf σ = 3) :
    σ ∉ Uz z := by
  intro hU
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp (isPGroup_Uz z)) ⟨σ, hU⟩
  rw [Subgroup.orderOf_mk, hσ3] at hk
  have h3 : 3 ∣ 2 ^ k := hk ▸ dvd_refl 3
  have := Nat.Prime.dvd_of_dvd_pow (by norm_num) h3
  omega

theorem exists_Msig [Finite G] (s : Swap z t w) (ha : Good z t a) {σ : G}
    (hσP : σ ∈ Pg z t w a) (hσ3 : orderOf σ = 3) :
    ∃ p q r : V4, GuardS (Msig p q r) ∧
      ∀ i : Fin 4, σ * gE z t w a i * σ⁻¹ = crd (gE z t w a) (Msig p q r i) := by
  have h := s.hyp
  have hσH : σ ∈ Hz z := hσP.1
  have hσN : σ ∈ Subgroup.normalizer (Eg z t w a : Set G) := hσP.2
  have hg := s.comm4_gE ha
  have hAt := (s.mem_A0_iff ha _).1 (s.maps_A0_of_mem_normalizer ha hσH hσN (s.t_mem_A0 ha))
  have hAa := (s.mem_A0_iff ha _).1 (s.maps_A0_of_mem_normalizer ha hσH hσN (s.a_mem_A0 ha))
  obtain ⟨v1, hv1, i1, ht'⟩ := hAt
  obtain ⟨v2, hv2, i2, ha'⟩ := hAa
  obtain ⟨c0, c1, rfl⟩ := (s.cm.mem_Vg_iff v1).1 hv1
  obtain ⟨d0, d1, rfl⟩ := (s.cm.mem_Vg_iff v2).1 hv2
  have hmE : σ * (w⁻¹ * a * w) * σ⁻¹ ∈ Eg z t w a :=
    (Subgroup.mem_normalizer_iff.mp hσN _).mp m_mem_Eg
  obtain ⟨v3, hv3, i3, j3, hm'⟩ := (s.mem_Eg_iff ha _).1 hmE
  obtain ⟨e0, e1, rfl⟩ := (s.cm.mem_Vg_iff v3).1 hv3
  have hj3 : j3 = 1 := by
    rcases zmod_two_cases j3 with rfl | rfl
    · exfalso
      have hA0 : σ * (w⁻¹ * a * w) * σ⁻¹ ∈ A0 s ha :=
        (s.mem_A0_iff ha _).2 ⟨zp z e0 * zp t e1, hv3, i3, by rw [hm', zp_zero, mul_one]⟩
      have hinv := conj_inv_mem_of_maps (S := A0 s ha) (g := σ)
        (fun x hx => s.maps_A0_of_mem_normalizer ha hσH hσN hx)
      have := hinv _ hA0
      apply s.m_notin_A0 ha
      have e : σ⁻¹ * (σ * (w⁻¹ * a * w) * σ⁻¹) * σ = w⁻¹ * a * w := by group
      rwa [e] at this
    · rfl
  subst hj3
  have hM : ∀ i : Fin 4, σ * gE z t w a i * σ⁻¹ = crd (gE z t w a)
      (Msig ![c0, c1, i1, 0] ![d0, d1, i2, 0] ![e0, e1, i3, 1] i) := by
    intro i
    fin_cases i
    · show σ * z * σ⁻¹ = crd (gE z t w a) (idc 0)
      rw [crd_idc]
      exact conj_z_eq hσH
    · show σ * t * σ⁻¹ = crd (gE z t w a) ![c0, c1, i1, 0]
      rw [ht']
      simp [crd, gE, zp_zero]
    · show σ * a * σ⁻¹ = crd (gE z t w a) ![d0, d1, i2, 0]
      rw [ha']
      simp [crd, gE, zp_zero]
    · show σ * (w⁻¹ * a * w) * σ⁻¹ = crd (gE z t w a) ![e0, e1, i3, 1]
      rw [hm']
      simp [crd, gE]
  refine ⟨_, _, _, ?_, hM⟩
  set M := Msig ![c0, c1, i1, 0] ![d0, d1, i2, 0] ![e0, e1, i3, 1] with hMdef
  have hσ3' : σ * σ * σ = 1 := by
    have := pow_orderOf_eq_one σ
    rw [hσ3, pow_three] at this
    simpa [mul_assoc] using this
  refine ⟨rfl, rfl, rfl, rfl, ?_, ?_⟩
  · intro c
    have e1 : ∀ c, σ * crd (gE z t w a) c * σ⁻¹ = crd (gE z t w a) (app M c) :=
      fun c => hg.conj_crd σ M hM c
    apply hg.crd_injective (fun c hc => s.crd_gE_indep ha hc)
    rw [← e1, ← e1, ← e1]
    calc σ * (σ * (σ * crd (gE z t w a) c * σ⁻¹) * σ⁻¹) * σ⁻¹
        = (σ * σ * σ) * crd (gE z t w a) c * (σ * σ * σ)⁻¹ := by group
      _ = crd (gE z t w a) c := by rw [hσ3']; group
  · rintro ⟨hn1, hn2⟩
    have ht1 : σ * t * σ⁻¹ = t ∨ σ * t * σ⁻¹ = z * t := by
      have := hM 1
      rcases hn1 with e | e
      · left
        rw [e, crd_idc] at this
        exact this
      · right
        rw [e, hg.crd_add, crd_idc, crd_idc] at this
        exact this
    have ha1 : σ * a * σ⁻¹ = a ∨ σ * a * σ⁻¹ = z * a := by
      have := hM 2
      rcases hn2 with e | e
      · left
        rw [e, crd_idc] at this
        exact this
      · right
        rw [e, hg.crd_add, crd_idc, crd_idc] at this
        exact this
    set γ := h.act ⟨σ, hσH⟩ with hγdef
    have hσt : σ * t * σ⁻¹ ∈ Uz z := (Subgroup.mem_normalizer_iff.mp (Hz_le_normalizer z hσH)
      t).mp s.ht.1
    have hσa : σ * a * σ⁻¹ ∈ Uz z := (Subgroup.mem_normalizer_iff.mp (Hz_le_normalizer z hσH)
      a).mp ha.mem.1
    have hγτ : vapp γ s.tauV = s.tauV := by
      have := s.vapp_act hσH s.ht.1
      show vapp γ (Multiplicative.toAdd (h.θ ⟨t, s.ht.1⟩)) = Multiplicative.toAdd (h.θ ⟨t, s.ht.1⟩)
      rw [this, s.theta_zt_cases hσt ht1]
    have hγα : vapp γ (s.alphaV ha) = s.alphaV ha := by
      have := s.vapp_act hσH ha.mem.1
      show vapp γ (Multiplicative.toAdd (h.θ ⟨a, ha.mem.1⟩)) =
        Multiplicative.toAdd (h.θ ⟨a, ha.mem.1⟩)
      rw [this, s.theta_za_cases ha hσa ha1]
    have hγF : γ ∈ FixA s.tauV (s.alphaV ha) := ⟨h.act_mem_Oq _, hγτ, hγα⟩
    have hγ3 : γ * γ * γ = 1 := by
      have : (⟨σ, hσH⟩ : ↥(Hz z)) * ⟨σ, hσH⟩ * ⟨σ, hσH⟩ = 1 := Subtype.ext hσ3'
      rw [hγdef, ← map_mul, ← map_mul, this, map_one]
    have hγ1 : γ ≠ 1 := by
      intro e
      exact not_mem_U_of_orderOf_three z hσ3 (h.mem_U_of_act_eq_one ⟨σ, hσH⟩ e)
    have hd1 : (1 : MulAut (Multiplicative V4)) ≠ γ := fun e => hγ1 e.symm
    have hd2 : (1 : MulAut (Multiplicative V4)) ≠ γ * γ := by
      intro e
      apply hγ1
      calc γ = γ * γ * γ * (γ * γ)⁻¹ := by group
        _ = 1 := by rw [hγ3, ← e]; group
    have hd3 : γ ≠ γ * γ := by
      intro e
      apply hγ1
      calc γ = (γ * γ) * γ⁻¹ := by group
        _ = γ * γ⁻¹ := by rw [← e]
        _ = 1 := by group
    have hsub : ({1, γ, γ * γ} : Set (MulAut (Multiplicative V4))) ⊆
        FixA s.tauV (s.alphaV ha) := by
      intro g hg
      rcases hg with rfl | rfl | rfl
      · exact ⟨one_mem _, vapp_one _, vapp_one _⟩
      · exact hγF
      · exact ⟨mul_mem hγF.1 hγF.1, by rw [vapp_mul, hγF.2.1, hγF.2.1],
          by rw [vapp_mul, hγF.2.2, hγF.2.2]⟩
    have h3 : ({1, γ, γ * γ} : Set (MulAut (Multiplicative V4))).ncard = 3 :=
      Set.ncard_eq_three.mpr ⟨1, γ, γ * γ, hd1, hd2, hd3, rfl⟩
    have hle := Set.ncard_le_ncard hsub (Set.toFinite _)
    have hfix : (FixA s.tauV (s.alphaV ha)).ncard ≤ 2 := by
      rw [← Nat.card_coe_set_eq]
      exact card_FixA_le (s.linePair_ta ha)
    omega

theorem card_normalizer_Eg [Finite G] (s : Swap z t w) (ha : Good z t a) :
    Nat.card ↥(Subgroup.normalizer (Eg z t w a : Set G)) = 5760 := by
  classical
  have h := s.hyp
  have hg := s.comm4_gE ha
  obtain ⟨x, y, hW⟩ := s.exists_Wm ha
  obtain ⟨u, hu, hu'⟩ := s.exists_u0
  have hut : u * t * u⁻¹ = z * t := by
    calc u * t * u⁻¹ = (u * t * u⁻¹ * t⁻¹) * t := by group
      _ = z * t := by rw [hu']
  obtain ⟨ε, x', y', hU⟩ := s.exists_Um ha hu hut
  obtain ⟨σ, hσP, hσ3⟩ := s.exists_sigma ha
  obtain ⟨p, q, r, hG, hS⟩ := s.exists_Msig ha hσP hσ3
  have hwK : w ∈ Subgroup.normalizer (Eg z t w a : Set G) :=
    s.normalizer_V_le ha (s.cm.mem_normalizer_Vg (by rw [s.w1']; exact t_mem_Vg z t)
      (by rw [s.w2']; exact z_mem_Vg z t))
  have huT : u ∈ Tn z t := h.mem_Tn_of s.ht (Uz_le_Hz z hu) (by
    rw [hut]; exact zt_mem_Vg z t)
  have huK : u ∈ Subgroup.normalizer (Eg z t w a : Set G) := s.T_le_normalizer ha huT
  have hσK : σ ∈ Subgroup.normalizer (Eg z t w a : Set G) := hσP.2
  let O : Set V4 := {c | ∃ k ∈ Subgroup.normalizer (Eg z t w a : Set G),
    k * z * k⁻¹ = crd (gE z t w a) c}
  have hstep : ∀ γ : G, γ ∈ Subgroup.normalizer (Eg z t w a : Set G) → ∀ M : Fin 4 → V4,
      (∀ i, γ * gE z t w a i * γ⁻¹ = crd (gE z t w a) (M i)) → ∀ c ∈ O, app M c ∈ O := by
    rintro γ hγ M hM c ⟨k, hk, hkc⟩
    refine ⟨γ * k, mul_mem hγ hk, ?_⟩
    calc γ * k * z * (γ * k)⁻¹ = γ * (k * z * k⁻¹) * γ⁻¹ := by group
      _ = γ * crd (gE z t w a) c * γ⁻¹ := by rw [hkc]
      _ = crd (gE z t w a) (app M c) := hg.conj_crd γ M hM c
  have h0 : idc 0 ∈ O := ⟨1, one_mem _, by rw [crd_idc]; simp [gE]⟩
  have hall := reach_transitive x y ε x' y' p q r hG O h0 (hstep w hwK _ hW)
    (hstep u huK _ hU) (hstep σ hσK _ hS)
  have hΩ : ∀ g ∈ Subgroup.normalizer (Eg z t w a : Set G), ∀ y ∈ (Eg z t w a : Set G) \ {1},
      g * y * g⁻¹ ∈ (Eg z t w a : Set G) \ {1} := by
    intro g hg' y hy
    refine ⟨(Subgroup.mem_normalizer_iff.mp hg' y).mp hy.1, fun e => hy.2 ?_⟩
    have e' : g * y * g⁻¹ = 1 := e
    calc y = g⁻¹ * (g * y * g⁻¹) * g := by group
      _ = 1 := by rw [e']; group
  have hzΩ : z ∈ (Eg z t w a : Set G) \ {1} := ⟨z_mem_Eg, h.z_ne_one⟩
  have htr : ∀ y ∈ (Eg z t w a : Set G) \ {1},
      ∃ g ∈ Subgroup.normalizer (Eg z t w a : Set G), g * z * g⁻¹ = y := by
    intro y hy
    obtain ⟨c, rfl⟩ := s.exists_crd ha hy.1
    have hc : c ≠ 0 := by
      rintro rfl
      exact hy.2 (crd_zero _)
    obtain ⟨k, hk, hkc⟩ := hall c hc
    exact ⟨k, hk, hkc⟩
  have hcount := card_eq_ncard_mul_card_inf_centralizer
    (Subgroup.normalizer (Eg z t w a : Set G)) ((Eg z t w a : Set G) \ {1}) z hΩ hzΩ htr
  have hKP : Subgroup.normalizer (Eg z t w a : Set G) ⊓ Subgroup.centralizer ({z} : Set G) =
      Pg z t w a := inf_comm _ _
  rw [hKP, s.card_P ha] at hcount
  have hΩc : ((Eg z t w a : Set G) \ {1}).ncard = 15 := by
    have := Set.ncard_sdiff_singleton_of_mem (s := (Eg z t w a : Set G)) (a := 1) (one_mem _)
    rw [this]
    have h16 : (Eg z t w a : Set G).ncard = 16 := by
      rw [← Nat.card_coe_set_eq]
      exact s.card_Eg ha
    omega
  rw [hΩc] at hcount
  omega

end Swap

end CFSG.Quasithin.H13.U43
