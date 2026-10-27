module

public import CFSG.Quasithin.H13.AS91Sec4TwoIdent
public import CFSG.GF2Type.Smith1979.IdxFourModelStab
public import CFSG.LargeExtraspecial.S4Weak
public import Certificates.Certificate89402

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.H13.AS91

open Subgroup CFSG.Open CFSG.LargeExtraspecial CFSG.Quasithin CFSG.Quasithin.HatM22 Module
open CFSG.GF2Type.Smith1979.GammaU CFSG.GF2Type.Smith1979.GammaU.StepA
open CFSG.GF2Type.Smith1979.GammaU.Viol CFSG.GF2Type.Smith1979.IdxFour
open CFSG.CharacterTheory.SteinbergBY CFSG.CharacterTheory.SteinbergBY.FieldFour
open scoped Matrix

variable {G : Type} [Group G] [Finite G] {z : G} {h : HypJ4 G z}

theorem exists_conj_of_rho_cl (S : Setting G) {x y : G} (hx : x ∈ S.QG) (hy : y ∈ S.QG)
    (hy1 : y ≠ 1) (hyz : y ≠ S.z) {m : S.M}
    (hm : ((S.ρ m : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl x) = S.cl y) :
    ∃ g ∈ S.M, g * x * g⁻¹ = y := by
  rw [S.ρ_cl m hx] at hm
  have hx' : (m : G) * x * (m : G)⁻¹ ∈ S.QG := S.conj_mem_QG m.2 hx
  rcases (S.cl_eq_cl_iff hx' hy).mp hm with h1 | h1
  · exact ⟨m, m.2, h1.symm⟩
  · have ht1 : (m : G) * x * (m : G)⁻¹ ≠ 1 := fun he => hyz (by rw [h1, he, one_mul])
    have htz : (m : G) * x * (m : G)⁻¹ ≠ S.z := fun he => hy1 (by rw [h1, he, S.z_mul_z])
    obtain ⟨u, hu, hut⟩ := S.exists_conj_eq_mul_z hx' ht1 htz
    refine ⟨u * m, mul_mem (S.QG_le_M hu) m.2, ?_⟩
    rw [h1, ← hut]
    group

namespace Data41

variable (D : Data41 h)

theorem q_ψV_symm (v : V12) :
    h.setting.q (D.ψV.symm v) = q0 v := by
  refine Two.eq_q0_of_invariant (fun v => h.setting.q (D.ψV.symm v)) (fun x y w => ?_)
    (by simp) (fun U hU x => ?_) ?_ v
  · simp only [map_add]
    exact QuadraticMap.map_add_add_add_map _ _ _ _
  · rw [← D.map_cMbar] at hU
    obtain ⟨g, hg, rfl⟩ := hU
    obtain ⟨m, -, -, rfl⟩ := mem_cMbar.mp hg
    change h.setting.q (D.ψV.symm (D.Φ (m : h.setting.Qt ≃ₗ[ZMod 2] h.setting.Qt) x)) = _
    rw [Φ_apply, AddEquiv.symm_apply_apply]
    exact TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp m.2 _
  · by_contra hall
    push Not at hall
    have hq0 : ∀ u : h.setting.Qt, h.setting.q u = 0 := fun u => by
      have := hall (D.ψV u)
      rwa [AddEquiv.symm_apply_apply] at this
    haveI : Module.Finite (ZMod 2) h.setting.Qt := Module.Finite.of_finite
    have hpos : 0 < finrank (ZMod 2) h.setting.Qt := by
      rw [h.setting.finrank_Qt_eq_two_mul_width, h.setting_width]
      norm_num
    obtain ⟨u, hu⟩ := Module.finrank_pos_iff_exists_ne_zero.mp hpos
    apply hu
    refine h.setting.q_nondegenerate.1 u fun w => ?_
    simp [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar, hq0]

@[expose] noncomputable def rep (n : ℕ) : G := (h.setting.exists_cl (D.ψV.symm (vecOf n))).choose

theorem rep_mem (n : ℕ) : D.rep n ∈ h.setting.QG := (h.setting.exists_cl _).choose_spec.1

theorem cl_rep (n : ℕ) : h.setting.cl (D.rep n) = D.ψV.symm (vecOf n) :=
  (h.setting.exists_cl _).choose_spec.2

theorem ψV_cl_rep (n : ℕ) : D.ψV (h.setting.cl (D.rep n)) = vecOf n := by
  rw [cl_rep, AddEquiv.apply_symm_apply]

theorem rep_props {n : ℕ} (hn0 : vecOf n ≠ 0)
    (hq : q0 (vecOf n) = 0) :
    D.rep n * D.rep n = 1 ∧ D.rep n ≠ 1 ∧ D.rep n ≠ z := by
  have hQ := D.rep_mem n
  have hcl0 : h.setting.cl (D.rep n) ≠ 0 := by
    rw [cl_rep]
    intro h0
    apply hn0
    have := congrArg D.ψV h0
    rwa [AddEquiv.apply_symm_apply, map_zero] at this
  refine ⟨?_, fun h1 => hcl0 ((h.setting.cl_eq_zero_iff hQ).mpr (Or.inl h1)),
    fun hz => hcl0 ((h.setting.cl_eq_zero_iff hQ).mpr (Or.inr hz))⟩
  have h2 : D.rep n ^ 2 = 1 := by
    rw [← h.setting.q_cl_eq_zero_iff hQ, cl_rep, q_ψV_symm, hq]
  rw [← pow_two, h2]

theorem vecOf_three_ne : vecOf 3 ≠ 0 := by
  intro h0
  have := congrFun h0 0
  simp [vecOf] at this

theorem vecOf_five_ne : vecOf 5 ≠ 0 := by
  intro h0
  have := congrFun h0 0
  simp [vecOf] at this

@[expose] noncomputable def Φo : h.setting.O →* (V12 ≃ₗ[ZMod 2] V12) :=
  D.Φ.toMonoidHom.comp h.setting.O.subtype

theorem Φo_apply (m : h.setting.O) : D.Φo m = D.Φ (m : h.setting.Qt ≃ₗ[ZMod 2] h.setting.Qt) := rfl

theorem Φo_injective : Function.Injective D.Φo :=
  D.Φ.injective.comp h.setting.O.subtype_injective

theorem map_Mbar_Φo
    (hOut : KG82HatM22Out) (hTw : KG82HatM22Twelve) : h.setting.Mbar.map D.Φo = Two.nGrp := by
  rw [← D.map_Mbar hOut hTw, Φo, ← map_map]

theorem Φo_mem_nGrp
    (hOut : KG82HatM22Out) (hTw : KG82HatM22Twelve) {m : h.setting.O} (hm : m ∈ h.setting.Mbar) :
    D.Φo m ∈ Two.nGrp := by
  rw [← D.map_Mbar_Φo hOut hTw]
  exact ⟨m, hm, rfl⟩

theorem Φo_apply_ψV (m : h.setting.O) (v : h.setting.Qt) :
    D.Φo m (D.ψV v) = D.ψV ((m : h.setting.Qt ≃ₗ[ZMod 2] h.setting.Qt) v) :=
  D.Φ_apply_ψV _ v

include D in
theorem card_nGrp
    (hOut : KG82HatM22Out) (hTw : KG82HatM22Twelve) : Nat.card Two.nGrp = 2661120 := by
  rw [← D.map_Mbar_Φo hOut hTw, Subgroup.card_map_of_injective D.Φo_injective, D.card_Mbar]

theorem map_stab
    (hOut : KG82HatM22Out) (hTw : KG82HatM22Twelve) (n : ℕ) :
    (stab h.setting (h.setting.cl (D.rep n))).map D.Φo = stabIn Two.nGrp (vecOf n) := by
  ext U
  constructor
  · rintro ⟨m, ⟨hmM, hmv⟩, rfl⟩
    refine mem_stabIn.mpr ⟨D.Φo_mem_nGrp hOut hTw hmM, ?_⟩
    rw [← D.ψV_cl_rep n, Φo_apply_ψV, hmv]
  · intro hU
    obtain ⟨hUN, hUv⟩ := mem_stabIn.mp hU
    rw [← D.map_Mbar_Φo hOut hTw] at hUN
    obtain ⟨m, hmM, rfl⟩ := hUN
    refine ⟨m, ⟨hmM, ?_⟩, rfl⟩
    apply D.ψV.injective
    rw [← Φo_apply_ψV, ψV_cl_rep, hUv]

theorem card_stab_mul
    (hOut : KG82HatM22Out) (hTw : KG82HatM22Twelve) (n : ℕ) {O : Set V12}
    (hO : MulAction.orbit ↥Two.nGrp (vecOf n) = O) :
    Nat.card (stab h.setting (h.setting.cl (D.rep n))) * O.ncard = 2661120 := by
  rw [← D.card_nGrp hOut hTw, ← card_stabIn_mul_ncard hO, ← D.map_stab hOut hTw n,
    Subgroup.card_map_of_injective D.Φo_injective]

theorem orbit_three :
    MulAction.orbit ↥Two.nGrp (vecOf 3) = {x | Two.InO1 x} := by
  ext x
  constructor
  · rintro ⟨⟨U, hU⟩, rfl⟩
    exact Two.inO1_invariant hU Two.inO1_three
  · intro hx
    obtain ⟨U, hU, hUx⟩ := Two.exists_of_inO1 hx
    exact ⟨⟨U, Two.gamGrp_le_nGrp hU⟩, hUx⟩

theorem orbit_five :
    MulAction.orbit ↥Two.nGrp (vecOf 5) = {x | Two.InO2 x} := by
  ext x
  constructor
  · rintro ⟨⟨U, hU⟩, rfl⟩
    exact Two.inO2_invariant hU Two.inO2_five
  · intro hx
    obtain ⟨U, hU, hUx⟩ := Two.exists_of_inO2 hx
    exact ⟨⟨U, Two.gamGrp_le_nGrp hU⟩, hUx⟩

theorem core_of_stabOK
    (hOut : KG82HatM22Out) (hTw : KG82HatM22Twelve) {n : ℕ} {gs ps : List (Array ℕ)}
    {W : List (Array ℕ × Array ℕ)} {nS nP k : ℕ} (hok : Two.stabOK n gs ps W nS nP = true)
    (hnP : nP = 2 ^ k) (hgsN : genGrp gs ≤ Two.nGrp)
    (hcard : Nat.card (stab h.setting (h.setting.cl (D.rep n))) = nS) (hdvd : nS ∣ 3840) :
    (∃ P : Subgroup h.setting.O, P ≤ stab h.setting (h.setting.cl (D.rep n)) ∧
      (∀ s ∈ stab h.setting (h.setting.cl (D.rep n)), ∀ p ∈ P, s * p * s⁻¹ ∈ P) ∧
      IsPGroup 2 P ∧ Nat.card P = nP) ∧
    ∀ P : Subgroup h.setting.O, P ≤ stab h.setting (h.setting.cl (D.rep n)) →
      (∀ s ∈ stab h.setting (h.setting.cl (D.rep n)), ∀ p ∈ P, s * p * s⁻¹ ∈ P) →
      IsPGroup 2 P → Nat.card P ≤ nP := by
  obtain ⟨-, hfix, hcS, hcP, hPS, hnorm, hwit⟩ := Two.stabOK_spec hok
  set K := stab h.setting (h.setting.cl (D.rep n)) with hK
  have hmapK := D.map_stab hOut hTw n
  have hgsK : genGrp gs = K.map D.Φo := by
    rw [hmapK]
    refine Subgroup.eq_of_le_of_card_ge (fun U hU => mem_stabIn.mpr ⟨hgsN hU, hfix U hU⟩) ?_
    rw [← hmapK, Subgroup.card_map_of_injective D.Φo_injective, hcard, hcS]
  have hmemK : ∀ {U}, U ∈ genGrp gs → ∃ s ∈ K, D.Φo s = U := fun hU => by
    rw [hgsK] at hU
    exact hU
  refine ⟨⟨(genGrp ps).comap D.Φo, fun x hp => ?_, fun s hs p hp => ?_, ?_, ?_⟩, ?_⟩
  · obtain ⟨s, hs, hsp⟩ := hmemK (hPS hp)
    rwa [D.Φo_injective hsp] at hs
  · obtain ⟨s', hs', hs's⟩ := hmemK (show D.Φo s ∈ genGrp gs by rw [hgsK]; exact ⟨s, hs, rfl⟩)
    show D.Φo (s * p * s⁻¹) ∈ genGrp ps
    rw [map_mul, map_mul, map_inv]
    exact hnorm _ (by rw [hgsK]; exact ⟨s, hs, rfl⟩) _ hp
  · have hc : Nat.card ((genGrp ps).comap D.Φo) = nP := by
      rw [← hcP, ← Subgroup.card_map_of_injective D.Φo_injective (K := (genGrp ps).comap D.Φo),
        Subgroup.map_comap_eq_self]
      intro U hU
      obtain ⟨s, -, rfl⟩ := hmemK (hPS hU)
      exact ⟨s, rfl⟩
    exact IsPGroup.of_card (n := k) (by rw [hc, hnP])
  · rw [← hcP, ← Subgroup.card_map_of_injective D.Φo_injective (K := (genGrp ps).comap D.Φo),
      Subgroup.map_comap_eq_self]
    intro U hU
    obtain ⟨s, -, rfl⟩ := hmemK (hPS hU)
    exact ⟨s, rfl⟩
  · intro P hPK hPn hP2
    have hPdvd : Nat.card P ∣ 256 := by
      obtain ⟨k, hk⟩ := hP2.exists_card_eq
      have h1 : Nat.card P ∣ 3840 := (Subgroup.card_dvd_of_le hPK).trans (hcard ▸ hdvd)
      rw [hk] at h1 ⊢
      have hcop : Nat.Coprime (2 ^ k) 15 := Nat.Coprime.pow_left k (by norm_num)
      exact hcop.dvd_of_dvd_mul_right (by simpa using h1)
    have h256 : ∀ p ∈ P, p ^ 256 = 1 := fun p hp => by
      have h1 : orderOf p ∣ 256 := by
        have := orderOf_dvd_natCard (⟨p, hp⟩ : ↥P)
        rw [Subgroup.orderOf_mk] at this
        exact this.trans hPdvd
      exact orderOf_dvd_iff_pow_eq_one.mp h1
    have hle : P.map D.Φo ≤ genGrp ps := by
      rintro _ ⟨p, hp, rfl⟩
      by_contra hnot
      have hpK : D.Φo p ∈ genGrp gs := by rw [hgsK]; exact ⟨p, hPK hp, rfl⟩
      obtain ⟨t, ht, ht256⟩ := hwit _ hpK (by rw [← map_pow, h256 p hp, map_one]) hnot
      obtain ⟨t₀, ht₀, rfl⟩ := hmemK ht
      apply ht256
      have hmem : p * (t₀ * p * t₀⁻¹) ∈ P := mul_mem hp (hPn t₀ ht₀ p hp)
      rw [← map_inv, ← map_mul, ← map_mul, ← map_mul, ← map_pow, h256 _ hmem, map_one]
    rw [← Subgroup.card_map_of_injective D.Φo_injective (K := P), ← hcP]
    exact Subgroup.card_le_of_le hle

theorem exists_scalar :
    ∃ e : FieldFour, (e = ω ∨ e = ω₂) ∧ ∀ u : h.setting.Qt,
      D.ψ ((D.θ : h.setting.Qt ≃ₗ[ZMod 2] h.setting.Qt) u) = e • D.ψ u := by
  obtain ⟨γ, hγ, hθγ, hcen⟩ := D.exists_center_matrix
  have hc : (⟨γ, hγ⟩ : ↥hatM22Γ₀) ∈ center ↥hatM22Γ₀ :=
    mem_center_iff.mpr fun g => Subtype.ext (hcen g g.2).symm
  rw [center_hatM22Γ₀, mem_ker_hatM22Act_iff] at hc
  rcases hc with h1 | hZ | hZ2
  · exfalso
    apply D.θ_ne
    apply Subtype.ext
    apply LinearEquiv.ext
    intro v
    apply D.ψ.injective
    rw [hθγ, show γ = 1 from congrArg Subtype.val h1, Units.val_one, Matrix.one_mulVec]
    rfl
  · refine ⟨ω, Or.inl rfl, fun u => ?_⟩
    have : ((γ : Matrix.GeneralLinearGroup (Fin 6) FieldFour) : Matrix (Fin 6) (Fin 6) FieldFour) =
        (((hatM22Z : ↥hatM22Γ₀) : Matrix.GeneralLinearGroup (Fin 6) FieldFour) :
          Matrix (Fin 6) (Fin 6) FieldFour) :=
      congrArg (fun g : ↥hatM22Γ₀ =>
        ((g : Matrix.GeneralLinearGroup (Fin 6) FieldFour) : Matrix (Fin 6) (Fin 6) FieldFour)) hZ
    rw [hθγ, this, hatM22Z_val, Matrix.smul_mulVec, Matrix.one_mulVec]
  · refine ⟨ω₂, Or.inr rfl, fun u => ?_⟩
    have : ((γ : Matrix.GeneralLinearGroup (Fin 6) FieldFour) : Matrix (Fin 6) (Fin 6) FieldFour) =
        (((hatM22Z ^ 2 : ↥hatM22Γ₀) : Matrix.GeneralLinearGroup (Fin 6) FieldFour) :
          Matrix (Fin 6) (Fin 6) FieldFour) :=
      congrArg (fun g : ↥hatM22Γ₀ =>
        ((g : Matrix.GeneralLinearGroup (Fin 6) FieldFour) : Matrix (Fin 6) (Fin 6) FieldFour)) hZ2
    rw [hθγ, this, hatM22Z_sq_val, Matrix.smul_mulVec, Matrix.one_mulVec]

theorem f4_cases (e : FieldFour) (he : e = ω ∨ e = ω₂) (c : FieldFour) :
    c = 0 ∨ c = 1 ∨ c = e ∨ c = e * e := by
  rcases he with rfl | rfl <;> revert c <;> decide

theorem f4_cube (e : FieldFour) (he : e = ω ∨ e = ω₂) : e * e * e = 1 := by
  rcases he with rfl | rfl <;> decide

theorem semilinear
    {g : h.setting.Qt ≃ₗ[ZMod 2] h.setting.Qt}
    (hg : g * (D.θ : h.setting.Qt ≃ₗ[ZMod 2] h.setting.Qt) =
      (D.θ : h.setting.Qt ≃ₗ[ZMod 2] h.setting.Qt) *
        ((D.θ : h.setting.Qt ≃ₗ[ZMod 2] h.setting.Qt) * g))
    (c : FieldFour) (v : h.setting.Qt) :
    D.ψ (g (D.ψ.symm (c • D.ψ v))) = (c * c) • D.ψ (g v) := by
  obtain ⟨e, he, hθe⟩ := D.exists_scalar
  set θG := (D.θ : h.setting.Qt ≃ₗ[ZMod 2] h.setting.Qt)
  have hgθ : ∀ u, g (θG u) = θG (θG (g u)) := fun u => by
    have := LinearEquiv.congr_fun hg u
    simpa using this
  have hθ2 : ∀ u, D.ψ (θG (θG u)) = (e * e) • D.ψ u := fun u => by
    rw [hθe, hθe, smul_smul]
  have hθ3 : ∀ u, θG (θG (θG u)) = u := fun u => by
    apply D.ψ.injective
    rw [hθe, hθ2, smul_smul, ← mul_assoc, f4_cube e he, one_smul]
  rcases f4_cases e he c with rfl | rfl | rfl | rfl
  · simp
  · simp
  · rw [← hθe, AddEquiv.symm_apply_apply, hgθ, hθ2, ← smul_smul]
  · rw [← hθ2, AddEquiv.symm_apply_apply, hgθ, hgθ, hθ3, hθe]
    congr 1
    calc e = e * e * e * e := by rw [f4_cube e he, one_mul]
      _ = e * e * (e * e) := by ring

theorem stabOK42_spec :
    Two.stabOK 3 (Two.stab1Gens ()) Two.core1Rows Two.wit1 3840 32 = true ∧
      Two.stabOK 5 (Two.stab2Gens ()) Two.core2Rows Two.wit2 1920 16 = true := by
  have h := Certificates.certificate89402
  simp only [Two.stabOK42, Bool.and_eq_true] at h
  exact h

theorem genGrp_stabGens_le {ws : List (List ℕ)} (hws : ∀ w ∈ ws, ∀ i ∈ w, i < 6) :
    genGrp (ws.map (wordRows Two.nGensI)) ≤ Two.nGrp :=
  genGrp_le_of_rep fun g hg => by
    obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hg
    exact rep_word Two.gensOK_nGensI w fun i hi => by simpa [Two.nGensI] using hws w hw i hi

theorem q0_three : q0 (vecOf 3) = 0 := by rw [q0_vecOf]; decide

theorem q0_five : q0 (vecOf 5) = 0 := by rw [q0_vecOf]; decide

theorem conj_or {r : G} (hrQ : r ∈ Q z) (hr2 : r * r = 1)
    (hr1 : r ≠ 1) (hrz : r ≠ z) :
    (∃ g ∈ H z, g * r * g⁻¹ = D.rep 3) ∨ ∃ g ∈ H z, g * r * g⁻¹ = D.rep 5 := by
  rw [← h.setting_QG] at hrQ
  have hcl0 : h.setting.cl r ≠ 0 := fun h0 => by
    rcases (h.setting.cl_eq_zero_iff hrQ).mp h0 with h1 | h1
    · exact hr1 h1
    · exact hrz h1
  have hv0 : D.ψV (h.setting.cl r) ≠ 0 := fun h0 => hcl0 (by
    have := congrArg D.ψV.symm h0
    rwa [AddEquiv.symm_apply_apply, map_zero] at this)
  have hvq : q0 (D.ψV (h.setting.cl r)) = 0 := by
    rw [← D.q_ψV_symm, AddEquiv.symm_apply_apply, h.setting.q_cl_eq_zero_iff hrQ, pow_two, hr2]
  have key : ∀ n, (D.rep n * D.rep n = 1 ∧ D.rep n ≠ 1 ∧ D.rep n ≠ z) →
      (∃ U ∈ Two.gamGrp, U (vecOf n) = D.ψV (h.setting.cl r)) →
        ∃ g ∈ H z, g * r * g⁻¹ = D.rep n := by
    rintro n ⟨-, hn1, hnz⟩ ⟨U, hU, hUv⟩
    rw [← D.map_cMbar] at hU
    obtain ⟨l, hl, rfl⟩ := hU
    obtain ⟨m, hmM, -, rfl⟩ := mem_cMbar.mp hl
    have hmv : (m : h.setting.Qt ≃ₗ[ZMod 2] h.setting.Qt) (h.setting.cl (D.rep n)) =
        h.setting.cl r := by
      apply D.ψV.injective
      rw [← hUv, cl_rep]
      rfl
    obtain ⟨m₀, hm₀⟩ := MonoidHom.mem_range.mp (inv_mem hmM)
    have hm : ((h.setting.ρ m₀ : h.setting.O) : h.setting.Qt ≃ₗ[ZMod 2] h.setting.Qt)
        (h.setting.cl r) = h.setting.cl (D.rep n) := by
      rw [hm₀, Subgroup.coe_inv]
      change (m : h.setting.Qt ≃ₗ[ZMod 2] h.setting.Qt).symm (h.setting.cl r) = _
      rw [LinearEquiv.symm_apply_eq, hmv]
    exact exists_conj_of_rho_cl h.setting hrQ (D.rep_mem n) hn1 hnz hm
  rcases Two.singular_cases42 hv0 hvq with h1 | h2
  · exact Or.inl (key 3 (D.rep_props Data41.vecOf_three_ne q0_three) (Two.exists_of_inO1 h1))
  · exact Or.inr (key 5 (D.rep_props Data41.vecOf_five_ne q0_five) (Two.exists_of_inO2 h2))

theorem not_conj
    (hOut : KG82HatM22Out) (hTw : KG82HatM22Twelve) {g : G}
    (hg : g ∈ H z) : g * D.rep 3 * g⁻¹ ≠ D.rep 5 := by
  intro he
  have hm := h.setting.ρ_cl ⟨g, hg⟩ (D.rep_mem 3)
  change _ = h.setting.cl (g * D.rep 3 * g⁻¹) at hm
  rw [he] at hm
  have hU := D.Φo_mem_nGrp hOut hTw (MonoidHom.mem_range.mpr ⟨⟨g, hg⟩, rfl⟩)
  have hv : D.Φo (h.setting.ρ ⟨g, hg⟩) (vecOf 3) = vecOf 5 := by
    rw [← D.ψV_cl_rep 3, Φo_apply_ψV, hm, ψV_cl_rep]
  have h1 := Two.inO1_invariant hU Two.inO1_three
  rw [hv] at h1
  exact (Two.inO2_singular Two.inO2_five).2.2 h1

theorem card_stab_three
    (hOut : KG82HatM22Out) (hTw : KG82HatM22Twelve) :
    Nat.card (stab h.setting (h.setting.cl (D.rep 3))) = 3840 := by
  have := D.card_stab_mul hOut hTw 3 orbit_three
  rw [Two.ncard_inO1] at this
  omega

theorem card_stab_five
    (hOut : KG82HatM22Out) (hTw : KG82HatM22Twelve) :
    Nat.card (stab h.setting (h.setting.cl (D.rep 5))) = 1920 := by
  have := D.card_stab_mul hOut hTw 5 orbit_five
  rw [Two.ncard_inO2] at this
  omega

theorem core_three
    (hOut : KG82HatM22Out)
    (hTw : KG82HatM22Twelve) :
    (∃ P : Subgroup h.setting.O, P ≤ stab h.setting (h.setting.cl (D.rep 3)) ∧
      (∀ s ∈ stab h.setting (h.setting.cl (D.rep 3)), ∀ p ∈ P, s * p * s⁻¹ ∈ P) ∧
      IsPGroup 2 P ∧ Nat.card P = 2 ^ 5) ∧
    ∀ P : Subgroup h.setting.O, P ≤ stab h.setting (h.setting.cl (D.rep 3)) →
      (∀ s ∈ stab h.setting (h.setting.cl (D.rep 3)), ∀ p ∈ P, s * p * s⁻¹ ∈ P) →
      IsPGroup 2 P → Nat.card P ≤ 2 ^ 5 :=
  D.core_of_stabOK hOut hTw stabOK42_spec.1 (by norm_num : (32 : ℕ) = 2 ^ 5)
    (genGrp_stabGens_le (ws := Two.stab1Words) (by decide)) (D.card_stab_three hOut hTw)
    (by norm_num)

theorem core_five
    (hOut : KG82HatM22Out)
    (hTw : KG82HatM22Twelve) :
    (∃ P : Subgroup h.setting.O, P ≤ stab h.setting (h.setting.cl (D.rep 5)) ∧
      (∀ s ∈ stab h.setting (h.setting.cl (D.rep 5)), ∀ p ∈ P, s * p * s⁻¹ ∈ P) ∧
      IsPGroup 2 P ∧ Nat.card P = 2 ^ 4) ∧
    ∀ P : Subgroup h.setting.O, P ≤ stab h.setting (h.setting.cl (D.rep 5)) →
      (∀ s ∈ stab h.setting (h.setting.cl (D.rep 5)), ∀ p ∈ P, s * p * s⁻¹ ∈ P) →
      IsPGroup 2 P → Nat.card P ≤ 2 ^ 4 :=
  D.core_of_stabOK hOut hTw stabOK42_spec.2 (by norm_num : (16 : ℕ) = 2 ^ 4)
    (genGrp_stabGens_le (ws := Two.stab2Words) (by decide)) (D.card_stab_five hOut hTw)
    (by norm_num)

theorem linear_or_semilinear
    (m : h.setting.M) :
    (∃ γ ∈ hatM22Γ₀, ∀ v : h.setting.Qt,
      D.ψ ((h.setting.ρ m : h.setting.Qt ≃ₗ[ZMod 2] h.setting.Qt) v) =
        ((γ : Matrix.GeneralLinearGroup (Fin 6) FieldFour) :
          Matrix (Fin 6) (Fin 6) FieldFour).mulVec (D.ψ v)) ∨
    ∀ (c : FieldFour) (v : h.setting.Qt),
      D.ψ ((h.setting.ρ m : h.setting.Qt ≃ₗ[ZMod 2] h.setting.Qt) (D.ψ.symm (c • D.ψ v))) =
        (c * c) • D.ψ ((h.setting.ρ m : h.setting.Qt ≃ₗ[ZMod 2] h.setting.Qt) v) := by
  have hmM : h.setting.ρ m ∈ h.setting.Mbar := MonoidHom.mem_range.mpr ⟨m, rfl⟩
  by_cases hθ : h.setting.ρ m * D.θ = D.θ * h.setting.ρ m
  · exact Or.inl (D.ψ_acts _ (mem_cMbar.mpr ⟨_, hmM, hθ, rfl⟩))
  · refine Or.inr (D.semilinear ?_)
    have h1 := D.conj_θ_of_not_comm hmM hθ
    have h2 : D.θ * D.θ = D.θ⁻¹ := by
      have : D.θ * D.θ * D.θ = 1 := by rw [← pow_three']; exact D.θ_pow
      exact eq_inv_of_mul_eq_one_left this
    have h3 : h.setting.ρ m * D.θ = D.θ * (D.θ * h.setting.ρ m) := by
      calc h.setting.ρ m * D.θ = (h.setting.ρ m * D.θ * (h.setting.ρ m)⁻¹) * h.setting.ρ m := by
            group
        _ = D.θ * (D.θ * h.setting.ρ m) := by rw [h1, ← h2, mul_assoc]
    have := congrArg (fun e : h.setting.O => (e : h.setting.Qt ≃ₗ[ZMod 2] h.setting.Qt)) h3
    simpa only [Subgroup.coe_mul] using this

@[expose] noncomputable def toLoc42
    (hHat : HatM22SmallModules)
    (hOut : KG82HatM22Out) (hTw : KG82HatM22Twelve) : Loc42 G z where
  toLoc41 := D.toLoc41 hHat
  card_Mbar := D.card_Mbar
  linear_or_semilinear := D.linear_or_semilinear
  r₁ := D.rep 3
  r₂ := D.rep 5
  r₁_mem := h.setting_QG ▸ D.rep_mem 3
  r₂_mem := h.setting_QG ▸ D.rep_mem 5
  r₁_sq := (D.rep_props vecOf_three_ne q0_three).1
  r₂_sq := (D.rep_props vecOf_five_ne q0_five).1
  r₁_ne_one := (D.rep_props vecOf_three_ne q0_three).2.1
  r₂_ne_one := (D.rep_props vecOf_five_ne q0_five).2.1
  r₁_ne_z := (D.rep_props vecOf_three_ne q0_three).2.2
  r₂_ne_z := (D.rep_props vecOf_five_ne q0_five).2.2
  conj_or := fun _ hr h2 h1 hz => D.conj_or hr h2 h1 hz
  not_conj := fun _ hg => D.not_conj hOut hTw hg
  card_stab₁ := D.card_stab_three hOut hTw
  card_stab₂ := D.card_stab_five hOut hTw
  core₁ := (D.core_three hOut hTw).1
  core₁_le := (D.core_three hOut hTw).2
  core₂ := (D.core_five hOut hTw).1
  core₂_le := (D.core_five hOut hTw).2

end Data41

end CFSG.Quasithin.H13.AS91
