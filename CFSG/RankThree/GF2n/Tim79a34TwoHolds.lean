module

public import CFSG.RankThree.GF2n.Tim79a34TwoRoot
public import CFSG.RankThree.GF2n.Tim79a34TwoSpace
public import CFSG.RankThree.GF2n.Tim79a34TwoAct
public import CFSG.RankThree.GF2n.Tim79a34TwoGame
public import CFSG.RankThree.GF2n.Tim79a34TwoGameEnd

public section

namespace CFSG.RankThree.GF2n.Tim79a.TwoRoot

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Timmesfeld.ARS CFSG.Timmesfeld.ARS.CaseM
  CFSG.Timmesfeld.Transvection CFSG.Timmesfeld.Transvection.ModelRank
  CFSG.LieType.Universal.Symplectic CFSG.RankThree.GF2n.Tim79a
  CFSG.RankThree.GF2n.Tim79a.Gamma
  CFSG.RankThree.GF2n.Tim79a.TwoModel CFSG.RankThree.GF2n.Tim79a.TwoSpace
open scoped commutatorElement

theorem vec4_eq_of_add_eq_zero : ∀ x y : Vec4, x + y = 0 → y = x := by
  intro x y h
  funext i
  have key : ∀ a b : ZMod 2, a + b = 0 → b = a := by decide
  exact key _ _ (congrFun h i)

variable {G : Type} [Group G] [Finite G] {M V Q P H : Subgroup G}
  {Φ : ↥(StatedSp 2 (GaloisField 2 1)) ≃* Xbar V H}
  {ψ : (Fin 2 ⊕ Fin 2 → GaloisField 2 1) ≃+ Additive ↥(wOf V H)}
  {a : Fin 2 ⊕ Fin 2 → GaloisField 2 1} {T : Subgroup ↥(StatedSp 2 (GaloisField 2 1))}

set_option hygiene false in
local notation "ψG " v:max => ((Additive.toMul (ψ v) : ↥(wOf V H)) : G)

theorem sq_centralizes_V (L : Lem) (cfg : GCfg M V Q P H Φ ψ a T) {v₀ b : G}
    (hT : TwoGame.TIData V Q P M (ψG a) v₀ b) (m : M) (hv₀ : v₀ ∈ V) (hv₀W : v₀ ∉ wOf V H) :
    ∀ z ∈ V, ((m * m : M) : G) * z = z * ((m * m : M) : G) := by
  have hma : (m : G) * ψG a = ψG a * (m : G) := (hT.M_cent _).mp m.2
  have hmw := conj_not_mem_W L.h11b cfg m.2 hv₀ hv₀W
  obtain ⟨haK, haG1⟩ := aG_mem_VW cfg
  have haW : ψG a ∈ wOf V H := (Subgroup.mem_inf.mp haK).2
  have hmv : (m : G) * v₀ * (m : G)⁻¹ = v₀ ∨ (m : G) * v₀ * (m : G)⁻¹ = ψG a * v₀ := by
    rcases hT.V_enum _ hmw.1 with h | h | h | h
    · exact absurd (by rw [h]; exact (wOf V H).one_mem) hmw.2
    · exact absurd (by rw [h]; exact haW) hmw.2
    · exact Or.inl h
    · exact Or.inr h
  have hρa : ((m * m : M) : G) * ψG a = ψG a * ((m * m : M) : G) := by
    show (m : G) * (m : G) * ψG a = ψG a * ((m : G) * (m : G))
    rw [mul_assoc, hma, ← mul_assoc, hma, mul_assoc]
  have hρv : ((m * m : M) : G) * v₀ = v₀ * ((m * m : M) : G) := by
    show (m : G) * (m : G) * v₀ = v₀ * ((m : G) * (m : G))
    rcases hmv with h | h
    · have h1 : (m : G) * v₀ = v₀ * (m : G) := mul_inv_eq_iff_eq_mul.mp h
      rw [mul_assoc, h1, ← mul_assoc, h1, mul_assoc]
    · have h1 : (m : G) * v₀ = ψG a * v₀ * (m : G) := mul_inv_eq_iff_eq_mul.mp h
      calc (m : G) * (m : G) * v₀ = (m : G) * ((m : G) * v₀) := by rw [mul_assoc]
        _ = (m : G) * (ψG a * v₀ * (m : G)) := by rw [h1]
        _ = ((m : G) * ψG a) * v₀ * (m : G) := by simp only [mul_assoc]
        _ = (ψG a * (m : G)) * v₀ * (m : G) := by rw [hma]
        _ = ψG a * ((m : G) * v₀) * (m : G) := by simp only [mul_assoc]
        _ = ψG a * (ψG a * v₀ * (m : G)) * (m : G) := by rw [h1]
        _ = (ψG a * ψG a) * v₀ * ((m : G) * (m : G)) := by simp only [mul_assoc]
        _ = v₀ * ((m : G) * (m : G)) := by rw [hT.a_sq, one_mul]
  intro z hz
  rcases hT.V_enum z hz with rfl | rfl | rfl | rfl
  · simp
  · exact hρa
  · exact hρv
  · calc ((m * m : M) : G) * (ψG a * v₀) = (((m * m : M) : G) * ψG a) * v₀ := by rw [mul_assoc]
      _ = (ψG a * ((m * m : M) : G)) * v₀ := by rw [hρa]
      _ = ψG a * (((m * m : M) : G) * v₀) := by rw [mul_assoc]
      _ = ψG a * (v₀ * ((m * m : M) : G)) := by rw [hρv]
      _ = (ψG a * v₀) * ((m * m : M) : G) := by rw [mul_assoc]

theorem final_false (L : Lem) (cfg : GCfg M V Q P H Φ ψ a T) {t0 t1 : G}
    (K : Coord P V M (P ⊓ wOf V H) t0 t1) {v₀ : G} (hv₀ : v₀ ∈ V) (hv₀W : v₀ ∉ wOf V H)
    {β : Fin 2 ⊕ Fin 2 → GaloisField 2 1} (hβ : spForm a β = 1) (bM : M)
    (hbβ : (bM : G) = ψG β) (hb : ⇑(K.act bM) = bS)
    {y : Fin 2 ⊕ Fin 2 → GaloisField 2 1} (hy : spForm a y = 0) (hy0 : y ≠ 0) (hya : y ≠ a)
    (hyβ : spForm y β = 0) {x : G} (hxa : x * ψG a * x⁻¹ = ψG y)
    (hact : ∀ w, (x * v₀ * x⁻¹) * ψG w * (x * v₀ * x⁻¹)⁻¹ = ψG (w + spForm y w • y))
    (hθ : ∀ hu : ψG y ∈ P, K.θ ⟨ψG y, hu⟩ = e0) (sM : M) (hsM : (sM : G) = x * v₀ * x⁻¹)
    (hsQ : (sM : G) ∉ Q) (hs0 : ⇑(K.act sM) = tS0) (m : M) (hm : ⇑(K.act m) = rho0) :
    False := by
  have hc : MinCex M V Q P H := cfg.hyp.setup.mc.toMinCex
  have hZ := cfg.centre
  have hT := tiData_of_cfg L cfg hβ hv₀ hv₀W
  have LF : TwoGame.LocalFacts V M (ψG a) v₀ := hT.localFacts
  have huP : ψG y ∈ P := (psi_mem_P_iff L.h11a cfg y).mpr hy
  have huV : ψG y ∉ V := psi_not_mem_V cfg hy0 hya
  have hWab : ∀ z ∈ wOf V H, ∀ w ∈ wOf V H, z * w = w * z := fun z hz w hw =>
    elemAbelian_mul_comm hc.wOf_isElemAbelian hz hw
  have hbW : (bM : G) ∈ wOf V H := by rw [hbβ]; exact psi_mem_W β
  set ρM : M := m * m with hρM
  set ρ : G := (ρM : G) with hρ
  set u : G := ψG y with hu
  set s : G := x * v₀ * x⁻¹ with hs
  set u' : G := ρ * u * ρ⁻¹ with hu'
  have hsMM : s ∈ M := by rw [← hsM]; exact sM.2
  have hu'P : u' ∈ P := P_norm_of_cfg cfg ρ ρM.2 u huP
  have hρact : ⇑(K.act ρM) = rho0 ∘ rho0 := by
    rw [hρM, map_mul, Equiv.Perm.coe_mul, hm]
  have hρinv : ⇑(K.act ρM⁻¹) = rho0 := by
    have h1 : K.act ρM * K.act m = 1 := by
      refine Equiv.ext fun z => ?_
      show (⇑(K.act ρM)) (⇑(K.act m) z) = z
      rw [hρact, hm]
      exact rho0_cube z
    have h2 : K.act ρM⁻¹ = K.act m := by
      rw [map_inv]
      exact inv_eq_of_mul_eq_one_right h1
    rw [h2, hm]
  have hθu : K.θ ⟨u, huP⟩ = e0 := hθ huP
  have hθu' : K.θ ⟨u', hu'P⟩ = (rho0 ∘ rho0) e0 := by
    rw [K.act_spec ρM ⟨u, huP⟩ hu'P, hρact, hθu]
  obtain ⟨hr1, hr2, hr3, hr4, hr5, hr6⟩ := rho0_prop
  have hρV : ∀ z ∈ V, ρ * z = z * ρ := sq_centralizes_V L cfg hT m hv₀ hv₀W
  have hsρ : s * ρ * s⁻¹ * ρ⁻¹ ∈ Q := by
    have hcomm : K.act sM * K.act ρM = K.act ρM * K.act sM := by
      refine Equiv.ext fun z => ?_
      show (⇑(K.act sM)) (⇑(K.act ρM) z) = (⇑(K.act ρM)) (⇑(K.act sM) z)
      rw [hs0, hρact]
      exact (hr4 z).symm
    have hk : K.act (sM * ρM * sM⁻¹ * ρM⁻¹) = 1 := by
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, hcomm]
      group
    have hkQ := mem_Q_of_act_id cfg K (sM * ρM * sM⁻¹ * ρM⁻¹) (fun z => by
      have := congrArg (fun g : Equiv.Perm Vec4 => g z) hk
      simpa using this)
    have e : ((sM * ρM * sM⁻¹ * ρM⁻¹ : M) : G) = s * ρ * s⁻¹ * ρ⁻¹ := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, hsM, hρ]
    rw [← e]
    exact hkQ
  have hbu : (bM : G) * u = u * (bM : G) := hWab _ hbW _ (psi_mem_W y)
  have hbs : (bM : G) * s = s * (bM : G) := by
    have h1 := hact β
    rw [hyβ, zero_smul, add_zero] at h1
    rw [hbβ]
    exact (mul_inv_eq_iff_eq_mul.mp h1).symm
  have he1 : u * u' = u' * u := by
    have h := (K.coords.comm ⟨u, huP⟩ ⟨u', hu'P⟩).mpr (by rw [hθu, hθu']; exact hr1)
    exact commutatorElement_eq_one_iff_mul_comm.mp h
  have hperp : ∀ k ∈ P, k * u = u * k → k * u' = u' * k →
      ∃ z ∈ V, k = z ∨ k = z * u ∨ k = z * u' ∨ k = z * u * u' := by
    intro k hk hku hku'
    have hb1 : bf (K.θ ⟨k, hk⟩) e0 = 0 := by
      rw [← hθu]
      exact (K.coords.comm ⟨k, hk⟩ ⟨u, huP⟩).mp (commutatorElement_eq_one_iff_mul_comm.mpr hku)
    have hb2 : bf (K.θ ⟨k, hk⟩) ((rho0 ∘ rho0) e0) = 0 := by
      rw [← hθu']
      exact (K.coords.comm ⟨k, hk⟩ ⟨u', hu'P⟩).mp
        (commutatorElement_eq_one_iff_mul_comm.mpr hku')
    have hrne : (rho0 ∘ rho0) e0 ≠ 0 := hr3
    have hne0 : e0 ≠ 0 := by decide
    rcases perp_span e0 ((rho0 ∘ rho0) e0) hne0 hrne (Ne.symm hr2) hr1 (K.θ ⟨k, hk⟩) hb1 hb2
      with h | h | h | h
    · refine ⟨k, (K.coords.ker ⟨k, hk⟩).mp h, Or.inl rfl⟩
    · refine ⟨k * u⁻¹, ?_, Or.inr (Or.inl (by group))⟩
      have h0 : K.θ (⟨k, hk⟩ * ⟨u, huP⟩⁻¹) = 0 := by
        rw [K.coords.add, K.θ_inv, h, hθu]
        funext i
        have key : ∀ c : ZMod 2, c + c = 0 := by decide
        exact key _
      exact (K.coords.ker _).mp h0
    · refine ⟨k * u'⁻¹, ?_, Or.inr (Or.inr (Or.inl (by group)))⟩
      have h0 : K.θ (⟨k, hk⟩ * ⟨u', hu'P⟩⁻¹) = 0 := by
        rw [K.coords.add, K.θ_inv, h, hθu']
        funext i
        have key : ∀ c : ZMod 2, c + c = 0 := by decide
        exact key _
      exact (K.coords.ker _).mp h0
    · refine ⟨k * (u * u')⁻¹, ?_, Or.inr (Or.inr (Or.inr (by group)))⟩
      have h0 : K.θ (⟨k, hk⟩ * (⟨u, huP⟩ * ⟨u', hu'P⟩)⁻¹) = 0 := by
        rw [K.coords.add, K.θ_inv, K.coords.add, h, hθu, hθu']
        funext i
        have key : ∀ c : ZMod 2, c + c = 0 := by decide
        exact key _
      exact (K.coords.ker _).mp h0
  have hind : ∀ z ∈ V, z ≠ u ∧ z ≠ u' ∧ z ≠ u * u' := by
    intro z hz
    have hz0 : ∀ hzP : z ∈ P, K.θ ⟨z, hzP⟩ = 0 := fun hzP => (K.coords.ker _).mpr hz
    have hzP : z ∈ P := hc.V_le_P hz
    refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩
    · have h1 := hz0 hzP
      have h2 : K.θ ⟨z, hzP⟩ = K.θ ⟨u, huP⟩ := congrArg K.θ (Subtype.ext h)
      rw [h2, hθu] at h1
      exact absurd h1 (by decide)
    · have h1 := hz0 hzP
      have h2 : K.θ ⟨z, hzP⟩ = K.θ ⟨u', hu'P⟩ := congrArg K.θ (Subtype.ext h)
      rw [h2, hθu'] at h1
      exact hr3 h1
    · have h1 := hz0 hzP
      have h2 : K.θ ⟨z, hzP⟩ = K.θ ⟨u, huP⟩ + K.θ ⟨u', hu'P⟩ := by
        rw [← K.coords.add]
        exact congrArg K.θ (Subtype.ext h)
      rw [h2, hθu, hθu'] at h1
      exact hr2 (vec4_eq_of_add_eq_zero _ _ h1)
  have hm3 : ¬ ((bM : G) * u' = u' * (bM : G)) := by
    intro h
    have h1 : (bM : G) * u' * (bM : G)⁻¹ = u' := mul_inv_eq_iff_eq_mul.mpr h
    have h2 := K.act_spec bM ⟨u', hu'P⟩ (P_norm_of_cfg cfg _ bM.2 _ hu'P)
    have h3 : K.θ ⟨(bM : G) * u' * (bM : G)⁻¹, P_norm_of_cfg cfg _ bM.2 _ hu'P⟩ =
        K.θ ⟨u', hu'P⟩ := congrArg K.θ (Subtype.ext h1)
    rw [h3, hθu', hb] at h2
    exact hr5 h2.symm
  have hm4 : ¬ ((ρ * (bM : G) * ρ⁻¹) * ((bM : G) * u' * (bM : G)⁻¹) =
      ((bM : G) * u' * (bM : G)⁻¹) * (ρ * (bM : G) * ρ⁻¹)) := by
    intro h
    have hdP : (bM : G) * u' * (bM : G)⁻¹ ∈ P := P_norm_of_cfg cfg _ bM.2 u' hu'P
    have hc1M : ρ * (bM : G) * ρ⁻¹ ∈ M :=
      M.mul_mem (M.mul_mem ρM.2 bM.2) (M.inv_mem ρM.2)
    have h1 : (ρ * (bM : G) * ρ⁻¹) * ((bM : G) * u' * (bM : G)⁻¹) *
        (ρ * (bM : G) * ρ⁻¹)⁻¹ = (bM : G) * u' * (bM : G)⁻¹ := mul_inv_eq_iff_eq_mul.mpr h
    have h2 := K.act_spec ⟨ρ * (bM : G) * ρ⁻¹, hc1M⟩ ⟨(bM : G) * u' * (bM : G)⁻¹, hdP⟩
      (P_norm_of_cfg cfg _ hc1M _ hdP)
    have h3 : K.θ ⟨ρ * (bM : G) * ρ⁻¹ * ((bM : G) * u' * (bM : G)⁻¹) *
        (ρ * (bM : G) * ρ⁻¹)⁻¹, P_norm_of_cfg cfg _ hc1M _ hdP⟩ =
        K.θ ⟨(bM : G) * u' * (bM : G)⁻¹, hdP⟩ := congrArg K.θ (Subtype.ext h1)
    rw [h3] at h2
    have h4 : K.θ ⟨(bM : G) * u' * (bM : G)⁻¹, hdP⟩ = bS ((rho0 ∘ rho0) e0) := by
      rw [K.act_spec bM ⟨u', hu'P⟩ hdP, hb, hθu']
    have hact1 : ∀ w, K.act ⟨ρ * (bM : G) * ρ⁻¹, hc1M⟩ w = (rho0 ∘ rho0) (bS (rho0 w)) := by
      intro w
      have e : (⟨ρ * (bM : G) * ρ⁻¹, hc1M⟩ : M) = ρM * bM * ρM⁻¹ := Subtype.ext rfl
      rw [e, map_mul, map_mul, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply]
      show (⇑(K.act ρM)) ((⇑(K.act bM)) ((⇑(K.act ρM⁻¹)) w)) = _
      rw [hρact, hb, hρinv]
    rw [hact1] at h2
    have h5 : rho0 (K.θ ⟨(bM : G) * u' * (bM : G)⁻¹, hdP⟩) =
        bS (rho0 (K.θ ⟨(bM : G) * u' * (bM : G)⁻¹, hdP⟩)) := by
      conv_lhs => rw [h2]
      exact rho0_cube _
    rw [h4] at h5
    exact hr6 h5.symm
  have hsQ' : s ∉ Q := by rw [← hsM]; exact hsQ
  have hbu' : ψG β * u = u * ψG β := by rw [← hbβ]; exact hbu
  have hbs' : ψG β * s = s * ψG β := by rw [← hbβ]; exact hbs
  have hm3' : ¬ (ψG β * u' = u' * ψG β) := by rw [← hbβ]; exact hm3
  have hm4' : ¬ ((ρ * ψG β * ρ⁻¹) * (ψG β * u' * (ψG β)⁻¹) =
      (ψG β * u' * (ψG β)⁻¹) * (ρ * ψG β * ρ⁻¹)) := by rw [← hbβ]; exact hm4
  obtain ⟨x₀, y₀, hx₀, hx₀M, hbx₀, hy₀, hy₀M, hb'y₀, hz, hz1⟩ :=
    TwoGame.two_game_dec hT LF x ρ u s u' hxa.symm rfl rfl huP huV hsMM hsQ' ρM.2 hρV hsρ
      hbu' hbs' he1 hperp hind
  exact TwoGame.two_game_fin hT LF x ρ u u' x₀ y₀ hxa.symm rfl hm3' hm4' ρM.2 hx₀ hx₀M hbx₀
    hy₀ hy₀M hb'y₀ hz hz1

theorem card_F (cfg : GCfg M V Q P H Φ ψ a T) : Nat.card ↥(P ⊓ wOf V H) = 8 := by
  have hF2 : Nat.card (GaloisField 2 1) = 2 := by
    rw [GaloisField.card 2 1 one_ne_zero, pow_one]
  have hWcard : Nat.card ↥(wOf V H) = 2 ^ (2 * 2) := by
    have h1 : Nat.card (Fin 2 ⊕ Fin 2 → GaloisField 2 1) = Nat.card ↥(wOf V H) :=
      Nat.card_congr (ψ.toEquiv.trans Additive.toMul)
    rw [← h1, Nat.card_fun, Nat.card_sum, hF2]
    simp [two_mul, Nat.card_eq_fintype_card]
  have hVW : Nat.card ↥(V ⊓ wOf V H) = 2 := cfg.hyp.module.trans cfg.hyp.q_two
  have h := twistedWSplit_holds G M V Q P H cfg.hyp.setup cfg.hyp.concl
  have h16 : (2 : ℕ) ^ (2 * 2) = 16 := by norm_num
  rw [hWcard, hVW, h16] at h
  omega

theorem exists_mem_not_mem {F : Subgroup G} (hF : Nat.card F = 8) (S : Finset G)
    (hS : S.card ≤ 4) : ∃ t ∈ F, t ∉ S := by
  by_contra hcon
  push Not at hcon
  have hsub : (F : Set G) ⊆ (S : Set G) := fun t ht => by exact_mod_cast hcon t ht
  have h1 : (F : Set G).ncard ≤ (S : Set G).ncard :=
    Set.ncard_le_ncard hsub (Set.toFinite _)
  rw [Set.ncard_coe_finset] at h1
  have h2 : (F : Set G).ncard = 8 := by rw [← Nat.card_coe_set_eq]; exact hF
  omega

theorem exists_t01 (cfg : GCfg M V Q P H Φ ψ a T) :
    ∃ t0 t1 : G, t0 ∈ P ⊓ wOf V H ∧ t1 ∈ P ⊓ wOf V H ∧
      ∀ z ∈ V, z ≠ t0 ∧ z ≠ t1 ∧ z ≠ t0 * t1 := by
  have hc : MinCex M V Q P H := cfg.hyp.setup.mc.toMinCex
  classical
  obtain ⟨haK, haG1⟩ := aG_mem_VW cfg
  have hA2 : Nat.card ↥(V ⊓ wOf V H) = 2 := cfg.hyp.module.trans cfg.hyp.q_two
  have hWsq : ∀ x ∈ wOf V H, x * x = 1 := fun x hx => elemAbelian_mul_self hc.wOf_isElemAbelian hx
  have hWab : ∀ z ∈ wOf V H, ∀ w ∈ wOf V H, z * w = w * z := fun z hz w hw =>
    elemAbelian_mul_comm hc.wOf_isElemAbelian hz hw
  have hF8 := card_F cfg
  obtain ⟨t0, ht0F, ht0S⟩ :=
    exists_mem_not_mem hF8 {1, ψG a} (le_trans Finset.card_le_two (by norm_num))
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at ht0S
  obtain ⟨t1, ht1F, ht1S⟩ := exists_mem_not_mem hF8 {1, ψG a, t0, t0 * ψG a} (by
    refine (Finset.card_insert_le _ _).trans ?_
    refine Nat.succ_le_succ ((Finset.card_insert_le _ _).trans ?_)
    exact Nat.succ_le_succ (Finset.card_le_two))
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at ht1S
  refine ⟨t0, t1, ht0F, ht1F, fun z hz => ?_⟩
  have hmemA : ∀ w ∈ wOf V H, w ∈ V → w = 1 ∨ w = ψG a := fun w hw hwV =>
    l12_two_elt hA2 haK haG1 w (Subgroup.mem_inf.mpr ⟨hwV, hw⟩)
  have ht0W : t0 ∈ wOf V H := (Subgroup.mem_inf.mp ht0F).2
  have ht1W : t1 ∈ wOf V H := (Subgroup.mem_inf.mp ht1F).2
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩
  · rcases hmemA t0 ht0W (h ▸ hz) with h1 | h1
    · exact ht0S.1 h1
    · exact ht0S.2 h1
  · rcases hmemA t1 ht1W (h ▸ hz) with h1 | h1
    · exact ht1S.1 h1
    · exact ht1S.2.1 h1
  · have hW01 : t0 * t1 ∈ wOf V H := (wOf V H).mul_mem ht0W ht1W
    rcases hmemA _ hW01 (h ▸ hz) with h1 | h1
    · apply ht1S.2.2.1
      calc t1 = (t0 * t0) * t1 := by rw [hWsq t0 ht0W, one_mul]
        _ = t0 * (t0 * t1) := by rw [mul_assoc]
        _ = t0 := by rw [h1, mul_one]
    · apply ht1S.2.2.2
      calc t1 = (t0 * t0) * t1 := by rw [hWsq t0 ht0W, one_mul]
        _ = t0 * (t0 * t1) := by rw [mul_assoc]
        _ = t0 * ψG a := by rw [h1]

theorem two_false (cfg : GCfg M V Q P H Φ ψ a T) : False := by
  have L := lem_holds
  have hc : MinCex M V Q P H := cfg.hyp.setup.mc.toMinCex
  have hZ := cfg.centre
  obtain ⟨haK, haG1⟩ := aG_mem_VW cfg
  have haV : ψG a ∈ V := (Subgroup.mem_inf.mp haK).1
  have hA2 : Nat.card ↥(V ⊓ wOf V H) = 2 := cfg.hyp.module.trans cfg.hyp.q_two
  obtain ⟨v₀, hv₀, hv₀W⟩ := exists_mem_V_not_mem_W cfg
  obtain ⟨t0, t1, ht0F, ht1F, hind⟩ := exists_t01 cfg
  have hWab : ∀ z ∈ wOf V H, ∀ w ∈ wOf V H, z * w = w * z := fun z hz w hw =>
    elemAbelian_mul_comm hc.wOf_isElemAbelian hz hw
  have hWsq : ∀ x ∈ wOf V H, x * x = 1 := fun x hx => elemAbelian_mul_self hc.wOf_isElemAbelian hx
  have hVsq : ∀ z ∈ V, z * z = 1 := fun z hz => elemAbelian_mul_self hc.elemAb hz
  have h11b := L.h11b G M V Q P H cfg.hyp cfg.centre cfg.iw
  have hP64 : Nat.card ↥P = 64 := by
    have := (L.h11a G M V Q P H cfg.hyp cfg.centre cfg.iw Φ ψ cfg.nat a T cfg.ne cfg.trans
      cfg.point).2.2.2
    rw [this]
    norm_num
  obtain ⟨θ, hθ, hF1, hF2, hθ0, hθ1⟩ := exists_coords P V (P ⊓ wOf V H) (ψG a) t0 t1
    hc.V_le_P inf_le_left haV haG1 hP64 (card_V cfg)
    (fun z hz p hp => by
      have : z ∈ Subgroup.centralizer (P : Set G) := by rw [h11b.2.2]; exact hz
      exact (Subgroup.mem_centralizer_iff.mp this p hp).symm)
    (fun p hp h => by
      rw [← h11b.2.2]
      exact Subgroup.mem_centralizer_iff.mpr fun q hq => (h q hq).symm)
    hVsq
    (fun p hp q hq => by
      have : ⁅p, q⁆ ∈ V ⊓ wOf V H := by
        rw [← h11b.1]
        exact Subgroup.commutator_mem_commutator hp hq
      exact l12_two_elt hA2 haK haG1 _ this)
    (fun p hp => l12_two_elt hA2 haK haG1 _ (mul_self_mem_VW L.h11b cfg hp))
    (fun f hf f' hf' => hWab f (Subgroup.mem_inf.mp hf).2 f' (Subgroup.mem_inf.mp hf').2)
    (fun f hf => hWsq f (Subgroup.mem_inf.mp hf).2) ht0F ht1F hind
  obtain ⟨act, hact_isom, hact_spec⟩ := exists_act hθ (P_norm_of_cfg cfg) (V_norm_of_cfg cfg)
  let K : Coord P V M (P ⊓ wOf V H) t0 t1 :=
    { θ := θ, coords := hθ, F_to := hF1, F_of := hF2, θ_t0 := fun h => hθ0,
      θ_t1 := fun h => hθ1, act := act, act_isom := hact_isom, act_spec := hact_spec }
  have ht0P : t0 ∈ P := (Subgroup.mem_inf.mp ht0F).1
  have ht1P : t1 ∈ P := (Subgroup.mem_inf.mp ht1F).1
  have ht0W : t0 ∈ wOf V H := (Subgroup.mem_inf.mp ht0F).2
  have ht1W : t1 ∈ wOf V H := (Subgroup.mem_inf.mp ht1F).2
  set y1 := toVec ψ t0 with hy1
  set y2 := toVec ψ t1 with hy2
  have hψy1 : ψG y1 = t0 := psi_toVec ht0W
  have hψy2 : ψG y2 = t1 := psi_toVec ht1W
  have hy1a : spForm a y1 = 0 :=
    (psi_mem_P_iff L.h11a cfg y1).mp (by rw [hψy1]; exact ht0P)
  have hy2a : spForm a y2 = 0 :=
    (psi_mem_P_iff L.h11a cfg y2).mp (by rw [hψy2]; exact ht1P)
  have hyne : ∀ y t, ψG y = t → (∀ z ∈ V, z ≠ t) → y ≠ 0 ∧ y ≠ a := fun y t h hz =>
    ⟨fun hy => hz 1 V.one_mem (by rw [← h, hy, psi_zero]),
      fun hy => hz (ψG a) haV (by rw [← h, hy])⟩
  have hy1ne := hyne y1 t0 hψy1 (fun z hz => (hind z hz).1)
  have hy2ne := hyne y2 t1 hψy2 (fun z hz => (hind z hz).2.1)
  obtain ⟨β, hβy, hβa⟩ := exists_perp_pair (a := y1) (y := a) hy1ne.1 cfg.ne (Ne.symm hy1ne.2)
  let bM : M := ⟨ψG β, wOf_le_M cfg (psi_mem_W β)⟩
  have hb : ⇑(K.act bM) = bS := act_b L cfg K bM hβa rfl
  have hT := tiData_of_cfg L cfg hβa hv₀ hv₀W
  have LF : TwoGame.LocalFacts V M (ψG a) v₀ := hT.localFacts
  obtain ⟨x1, hx1X, hx1a, hact1⟩ := exists_root_conj cfg hy1ne.1 hv₀ hv₀W
  obtain ⟨x2, hx2X, hx2a, hact2⟩ := exists_root_conj cfg hy2ne.1 hv₀ hv₀W
  have hθe0 : ∀ hu : ψG y1 ∈ P, K.θ ⟨ψG y1, hu⟩ = e0 := fun hu => by
    have : (⟨ψG y1, hu⟩ : P) = ⟨t0, ht0P⟩ := Subtype.ext hψy1
    rw [this]
    exact hθ0
  have hθe1 : ∀ hu : ψG y2 ∈ P, K.θ ⟨ψG y2, hu⟩ = e1 := fun hu => by
    have : (⟨ψG y2, hu⟩ : P) = ⟨t1, ht1P⟩ := Subtype.ext hψy2
    rw [this]
    exact hθ1
  obtain ⟨s0, hs0, hs0Q, hs0X, hs0e0, -⟩ := root_pair L cfg K hv₀ hv₀W LF bM rfl hb hy1a
    hy1ne.1 hy1ne.2 hx1X hx1a hact1
  obtain ⟨s1, hs1, hs1Q, hs1X, -, hs1e1⟩ := root_pair L cfg K hv₀ hv₀W LF bM rfl hb hy2a
    hy2ne.1 hy2ne.2 hx2X hx2a hact2
  have h0 : ⇑(K.act s0) = tS0 := hs0e0 (by rw [hψy1]; exact ht0P) (hθe0 _)
  have h1 : ⇑(K.act s1) = tS1 := hs1e1 (by rw [hψy2]; exact ht1P) (hθe1 _)
  obtain ⟨g, hg⟩ := exists_not_stab L cfg K bM s0 s1 hb h0 h1 (wOf_le_xOf V H (psi_mem_W β))
    hs0X hs1X
  obtain ⟨m, hm⟩ := exists_rho_act L cfg K bM s0 s1 hb h0 h1 ⟨g, hg⟩
  exact final_false L cfg K hv₀ hv₀W hβa bM rfl hb hy1a hy1ne.1 hy1ne.2 hβy hx1a hact1 hθe0
    s0 hs0 hs0Q h0 m hm

end CFSG.RankThree.GF2n.Tim79a.TwoRoot

namespace CFSG.RankThree.GF2n.Tim79a

theorem ntTwoStatement_holds : NTTwoStatement := by
  intro G _ _ M V Q P H hH hZ hiso
  obtain ⟨Φ, ψ, a, T, ⟨cfg⟩⟩ := TwoRoot.exists_cfg hH hZ hiso
  exact TwoRoot.two_false cfg

end CFSG.RankThree.GF2n.Tim79a
