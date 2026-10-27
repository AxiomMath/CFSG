module

public import CFSG.Quasithin.Recognition.Stroth.Str83G4CaseAKernel

public section

namespace CFSG.Quasithin.Stroth

open CFSG.Quasithin.F112R

variable {G : Type} [Group G] [Finite G] {L1 L2 S : Subgroup G}

@[expose] noncomputable def caseATheta (L1 L2 S : Subgroup G) :
    (f112Amalgam L1 L2 S).Ghat →* G :=
  ((L1 ⊔ bigB L1 L2 S) ⊔ (L2 ⊔ bigB L1 L2 S)).subtype.comp (f112Completion L1 L2 S).theta

theorem coe_f112StabEquiv0_caseATheta
    (h : MulAction.stabilizer (f112Acting L1 L2 S) (f112Gamma0 L1 L2 S)) :
    (f112StabEquiv0 L1 L2 S h : G) =
      caseATheta L1 L2 S ((h : f112Acting L1 L2 S) : (f112Amalgam L1 L2 S).Ghat) := by
  rw [coe_f112StabEquiv0, RankTwoAmalgam.Completion.coe_theta0]
  rfl

theorem coe_f112StabEquiv1_caseATheta
    (h : MulAction.stabilizer (f112Acting L1 L2 S) (f112Gamma1 L1 L2 S)) :
    (f112StabEquiv1 L1 L2 S h : G) =
      caseATheta L1 L2 S ((h : f112Acting L1 L2 S) : (f112Amalgam L1 L2 S).Ghat) := by
  rw [coe_f112StabEquiv1, RankTwoAmalgam.Completion.coe_theta0]
  rfl

theorem caseATheta_map_Z_γ₁ :
    (caseAZ (f112Gamma1 L1 L2 S)).map (caseATheta L1 L2 S) = Z2 L1 L2 S := by
  apply le_antisymm
  · rw [Subgroup.map_le_iff_le_comap]
    intro x hx
    rw [Subgroup.mem_comap]
    have hxstab : x ∈ CosetGeom.stab (f112Gamma1 L1 L2 S) :=
      caseA_Qy_le_stab _ (caseA_Z_le_Qy _ hx)
    obtain ⟨h, hh, rfl⟩ := Subgroup.mem_map.mp hxstab
    have hZ : (f112StabEquiv1 L1 L2 S ⟨h, hh⟩ : G) ∈ Z2 L1 L2 S :=
      (caseA_mem_Z_γ₁_iff ⟨h, hh⟩).mp (by simpa using hx)
    rwa [coe_f112StabEquiv1_caseATheta] at hZ
  · intro z hz
    have hzP2 : z ∈ P2 L1 L2 S :=
      (A4.omegaOneCenterOf_le (Q2 L1 L2 S)).trans
        (CFSG.LieType.BorelTits.pCoreOf_le 2 (P2 L1 L2 S)) hz
    let h : MulAction.stabilizer (f112Acting L1 L2 S) (f112Gamma1 L1 L2 S) :=
      (f112StabEquiv1 L1 L2 S).symm ⟨z, hzP2⟩
    have hh : (f112StabEquiv1 L1 L2 S h : G) = z :=
      congrArg Subtype.val ((f112StabEquiv1 L1 L2 S).apply_symm_apply ⟨z, hzP2⟩)
    refine Subgroup.mem_map.mpr ⟨((h : f112Acting L1 L2 S) :
      (f112Amalgam L1 L2 S).Ghat), ?_, ?_⟩
    · exact (caseA_mem_Z_γ₁_iff h).mpr (by rw [hh]; exact hz)
    · rw [← coe_f112StabEquiv1_caseATheta]; exact hh

theorem caseATheta_map_X_γ₀ :
    (caseAX (f112Gamma0 L1 L2 S)).map (caseATheta L1 L2 S) = str83X L1 L2 S := by
  apply le_antisymm
  · rw [Subgroup.map_le_iff_le_comap]
    refine iSup₂_le fun w hw => ?_
    intro x hx
    rw [Subgroup.mem_comap]
    obtain ⟨g, hgstab, hgw⟩ := CosetGeom.stab_transitive_on_nbrs
      (γ := f112Gamma0 L1 L2 S) (δ := f112Gamma1 L1 L2 S) (δ' := w)
      (CosetGeom.adj_γ₀_γ₁) hw
    obtain ⟨k, hkW, hk_eq⟩ := Subgroup.mem_map.mp hgstab
    have hkg : k = g := Subtype.ext hk_eq
    have hkw : k • f112Gamma1 L1 L2 S = w := by rw [hkg, hgw]
    rw [← hkw, caseA_Z_smul k (f112Gamma1 L1 L2 S), mem_conjSub] at hx
    have hzZ2 : caseATheta L1 L2 S
        ((k : (f112Amalgam L1 L2 S).Ghat)⁻¹ * x *
          (k : (f112Amalgam L1 L2 S).Ghat)) ∈ Z2 L1 L2 S := by
      have h1 := Subgroup.mem_map_of_mem (caseATheta L1 L2 S) hx
      rwa [caseATheta_map_Z_γ₁] at h1
    have hkP1 : caseATheta L1 L2 S (k : (f112Amalgam L1 L2 S).Ghat) ∈ P1 L1 L2 S :=
      coe_f112StabEquiv0_caseATheta (L1 := L1) (L2 := L2) (S := S) ⟨k, hkW⟩ ▸
        (f112StabEquiv0 L1 L2 S ⟨k, hkW⟩).2
    have hx_eq : x = (k : (f112Amalgam L1 L2 S).Ghat) *
        ((k : (f112Amalgam L1 L2 S).Ghat)⁻¹ * x *
          (k : (f112Amalgam L1 L2 S).Ghat)) * (k : (f112Amalgam L1 L2 S).Ghat)⁻¹ := by
      group
    rw [hx_eq, map_mul, map_mul, map_inv]
    exact mem_conjClosure hkP1 hzZ2
  · refine conjClosure_le fun h hh z hz => ?_
    obtain ⟨k, hk_eq⟩ : ∃ k : MulAction.stabilizer (f112Acting L1 L2 S)
        (f112Gamma0 L1 L2 S), (f112StabEquiv0 L1 L2 S k : G) = h := by
      refine ⟨(f112StabEquiv0 L1 L2 S).symm ⟨h, hh⟩, ?_⟩
      exact congrArg Subtype.val ((f112StabEquiv0 L1 L2 S).apply_symm_apply ⟨h, hh⟩)
    obtain ⟨x, hx, hxz⟩ := Subgroup.mem_map.mp
      ((caseATheta_map_Z_γ₁ (L1 := L1) (L2 := L2) (S := S)).ge hz)
    have hxX : x ∈ caseAX (f112Gamma0 L1 L2 S) :=
      le_iSup₂ (f := fun w (_ : w ∈ CosetGeom.nbrs (f112Gamma0 L1 L2 S)) => caseAZ w)
        (f112Gamma1 L1 L2 S) (CosetGeom.adj_γ₀_γ₁) hx
    have hkstab : (k : (f112Amalgam L1 L2 S).Ghat) ∈
        CosetGeom.stab (f112Gamma0 L1 L2 S) :=
      Subgroup.mem_map.mpr ⟨(k : f112Acting L1 L2 S), k.2, rfl⟩
    have hconj : (k : (f112Amalgam L1 L2 S).Ghat) * x *
        (k : (f112Amalgam L1 L2 S).Ghat)⁻¹ ∈ caseAX (f112Gamma0 L1 L2 S) :=
      (Subgroup.mem_normalizer_iff.mp (caseA_stab_le_normalizer_X _ hkstab) x).mp hxX
    refine Subgroup.mem_map.mpr ⟨(k : (f112Amalgam L1 L2 S).Ghat) * x *
      (k : (f112Amalgam L1 L2 S).Ghat)⁻¹, hconj, ?_⟩
    rw [map_mul, map_mul, map_inv, ← hk_eq, coe_f112StabEquiv0_caseATheta k, ← hxz]

theorem caseATheta_injOn_stab_γ₀ :
    Set.InjOn (caseATheta L1 L2 S)
      (CosetGeom.stab (f112Gamma0 L1 L2 S) : Set (f112Amalgam L1 L2 S).Ghat) := by
  intro x hx y hy hxy
  obtain ⟨kx, hkx, hkx_eq⟩ := Subgroup.mem_map.mp hx
  obtain ⟨ky, hky, hky_eq⟩ := Subgroup.mem_map.mp hy
  have hkx' : (kx : (f112Amalgam L1 L2 S).Ghat) = x := hkx_eq
  have hky' : (ky : (f112Amalgam L1 L2 S).Ghat) = y := hky_eq
  have h1 : caseATheta L1 L2 S (kx : (f112Amalgam L1 L2 S).Ghat) =
      caseATheta L1 L2 S (ky : (f112Amalgam L1 L2 S).Ghat) := by
    rw [hkx', hky']; exact hxy
  have h2 : f112StabEquiv0 L1 L2 S ⟨kx, hkx⟩ = f112StabEquiv0 L1 L2 S ⟨ky, hky⟩ := by
    apply Subtype.ext
    rw [coe_f112StabEquiv0_caseATheta, coe_f112StabEquiv0_caseATheta]
    exact h1
  have h3 : (⟨kx, hkx⟩ : MulAction.stabilizer (f112Acting L1 L2 S) (f112Gamma0 L1 L2 S)) =
      ⟨ky, hky⟩ := (f112StabEquiv0 L1 L2 S).injective h2
  rw [← hkx', ← hky']
  exact congrArg (fun w : MulAction.stabilizer (f112Acting L1 L2 S) (f112Gamma0 L1 L2 S) =>
    ((w : f112Acting L1 L2 S) : (f112Amalgam L1 L2 S).Ghat)) h3

theorem caseA_X_le_stab {a : ℕ} (hfr : Str83G4Frame L1 L2 S a)
    (v : f112Gamma L1 L2 S) : caseAX v ≤ CosetGeom.stab v := by
  refine iSup₂_le fun w hw => ?_
  refine (caseA_Z_le_Qy w).trans ((caseA_Qy_le_ballStab_one hfr w).trans ?_)
  refine CosetGeom.ballStab_le_stab_of_dist_le (n := 1) (γ := w) (δ := v) ?_
  rw [CosetGeom.dist_comm]
  exact (CosetGeom.dist_eq_one_iff_adj.mpr hw).le

theorem caseA_mem_X_γ₀_iff {a : ℕ}
    (hfr : Str83G4Frame L1 L2 S a)
    (h : MulAction.stabilizer (f112Acting L1 L2 S) (f112Gamma0 L1 L2 S)) :
    ((h : f112Acting L1 L2 S) : (f112Amalgam L1 L2 S).Ghat) ∈ caseAX (f112Gamma0 L1 L2 S) ↔
      (f112StabEquiv0 L1 L2 S h : G) ∈ str83X L1 L2 S := by
  constructor
  · intro hh
    rw [coe_f112StabEquiv0_caseATheta h]
    have h1 := Subgroup.mem_map_of_mem (caseATheta L1 L2 S) hh
    rwa [caseATheta_map_X_γ₀] at h1
  · intro hh
    rw [coe_f112StabEquiv0_caseATheta h] at hh
    have hmem : caseATheta L1 L2 S
        ((h : f112Acting L1 L2 S) : (f112Amalgam L1 L2 S).Ghat) ∈
        (caseAX (f112Gamma0 L1 L2 S)).map (caseATheta L1 L2 S) := by
      rwa [caseATheta_map_X_γ₀]
    obtain ⟨x, hx, hxθ⟩ := Subgroup.mem_map.mp hmem
    have hx' : x = ((h : f112Acting L1 L2 S) : (f112Amalgam L1 L2 S).Ghat) :=
      caseATheta_injOn_stab_γ₀ (caseA_X_le_stab hfr _ hx)
        (Subgroup.mem_map.mpr ⟨(h : f112Acting L1 L2 S), h.2, rfl⟩) hxθ
    rwa [hx'] at hx

private theorem caseA_X_le_Qy_of_vtype_false
    {a : ℕ} (hfr : Str83G4Frame L1 L2 S a) {α : f112Gamma L1 L2 S}
    (hα : CosetGeom.vtype α = false) : caseAX α ≤ CosetGeom.Qy α := by
  obtain ⟨g, hg⟩ := CosetGeom.exists_smul_eq_γ₀ hα
  rw [hg, caseA_X_smul, caseA_Qy_smul]
  refine conjSub_mono (g : (f112Amalgam L1 L2 S).Ghat) ?_
  intro x hx
  have hxstab : x ∈ CosetGeom.stab (f112Gamma0 L1 L2 S) := caseA_X_le_stab hfr _ hx
  obtain ⟨h, hh, hh_eq⟩ := Subgroup.mem_map.mp hxstab
  have hh_eq' : (h : (f112Amalgam L1 L2 S).Ghat) = x := hh_eq
  have hX : (f112StabEquiv0 L1 L2 S ⟨h, hh⟩ : G) ∈ str83X L1 L2 S :=
    (caseA_mem_X_γ₀_iff hfr ⟨h, hh⟩).mp (by rw [hh_eq']; exact hx)
  have hQ : (f112StabEquiv0 L1 L2 S ⟨h, hh⟩ : G) ∈ Q1 L1 L2 S := str83X_le_q1 hfr hX
  rw [← hh_eq']
  exact (caseA_mem_Qy_γ₀_iff ⟨h, hh⟩).mpr hQ

theorem caseA_R_le_stab
    {a : ℕ}
    (hfr : Str83G4Frame L1 L2 S a) {β : f112Gamma L1 L2 S} (hβ : CosetGeom.vtype β = true) :
    caseAR β ≤ CosetGeom.stab β := by
  refine iSup₂_le fun α hα => ?_
  have hαfalse : CosetGeom.vtype α = false := by
    cases hv : CosetGeom.vtype α with
    | false => rfl
    | true => exact absurd (hβ.trans hv.symm) (CosetGeom.vtype_ne_of_adj hα)
  refine (caseA_X_le_Qy_of_vtype_false hfr hαfalse).trans ?_
  refine (caseA_Qy_le_ballStab_one hfr α).trans ?_
  refine CosetGeom.ballStab_le_stab_of_dist_le (n := 1) (γ := α) (δ := β) ?_
  rw [CosetGeom.dist_comm]
  exact (CosetGeom.dist_eq_one_iff_adj.mpr hα).le

theorem caseATheta_map_R_γ₁ :
    (caseAR (f112Gamma1 L1 L2 S)).map (caseATheta L1 L2 S) = str83R L1 L2 S := by
  apply le_antisymm
  · rw [Subgroup.map_le_iff_le_comap]
    refine iSup₂_le fun α hα => ?_
    intro x hx
    rw [Subgroup.mem_comap]
    obtain ⟨g, hgstab, hgα⟩ := CosetGeom.stab_transitive_on_nbrs
      (γ := f112Gamma1 L1 L2 S) (δ := f112Gamma0 L1 L2 S) (δ' := α)
      (CosetGeom.adj_γ₀_γ₁.symm) hα
    obtain ⟨k, hkW, hk_eq⟩ := Subgroup.mem_map.mp hgstab
    have hkg : k = g := Subtype.ext hk_eq
    have hkα : k • f112Gamma0 L1 L2 S = α := by rw [hkg, hgα]
    rw [← hkα, caseA_X_smul k (f112Gamma0 L1 L2 S), mem_conjSub] at hx
    have hxX : caseATheta L1 L2 S
        ((k : (f112Amalgam L1 L2 S).Ghat)⁻¹ * x *
          (k : (f112Amalgam L1 L2 S).Ghat)) ∈ str83X L1 L2 S := by
      have h1 := Subgroup.mem_map_of_mem (caseATheta L1 L2 S) hx
      rwa [caseATheta_map_X_γ₀] at h1
    have hkP2 : caseATheta L1 L2 S (k : (f112Amalgam L1 L2 S).Ghat) ∈ P2 L1 L2 S :=
      coe_f112StabEquiv1_caseATheta (L1 := L1) (L2 := L2) (S := S) ⟨k, hkW⟩ ▸
        (f112StabEquiv1 L1 L2 S ⟨k, hkW⟩).2
    have hx_eq : x = (k : (f112Amalgam L1 L2 S).Ghat) *
        ((k : (f112Amalgam L1 L2 S).Ghat)⁻¹ * x *
          (k : (f112Amalgam L1 L2 S).Ghat)) * (k : (f112Amalgam L1 L2 S).Ghat)⁻¹ := by
      group
    rw [hx_eq, map_mul, map_mul, map_inv]
    exact mem_conjClosure hkP2 hxX
  · refine conjClosure_le fun p hp x hx => ?_
    obtain ⟨k, hk_eq⟩ : ∃ k : MulAction.stabilizer (f112Acting L1 L2 S)
        (f112Gamma1 L1 L2 S), (f112StabEquiv1 L1 L2 S k : G) = p := by
      refine ⟨(f112StabEquiv1 L1 L2 S).symm ⟨p, hp⟩, ?_⟩
      exact congrArg Subtype.val ((f112StabEquiv1 L1 L2 S).apply_symm_apply ⟨p, hp⟩)
    obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp
      ((caseATheta_map_X_γ₀ (L1 := L1) (L2 := L2) (S := S)).ge hx)
    have hkγ₁ : (k : f112Acting L1 L2 S) • f112Gamma1 L1 L2 S = f112Gamma1 L1 L2 S := k.2
    have hkγ : (k : f112Acting L1 L2 S) • f112Gamma0 L1 L2 S ∈
        CosetGeom.nbrs (f112Gamma1 L1 L2 S) := by
      have h := (CosetGeom.smul_adj (G₀ := (f112Amalgam L1 L2 S).Ghat1 ⊔
          (f112Amalgam L1 L2 S).Ghat2) (G₁ := (f112Amalgam L1 L2 S).Ghat1)
          (G₂ := (f112Amalgam L1 L2 S).Ghat2)
          (k : f112Acting L1 L2 S)).mpr (CosetGeom.adj_γ₀_γ₁.symm)
      simpa [hkγ₁, CosetGeom.nbrs] using h
    have hyX : (k : (f112Amalgam L1 L2 S).Ghat) * y *
        (k : (f112Amalgam L1 L2 S).Ghat)⁻¹ ∈
        caseAX ((k : f112Acting L1 L2 S) • f112Gamma0 L1 L2 S) := by
      rw [caseA_X_smul]
      exact mul_mem_conjSub hy
    have hconj : (k : (f112Amalgam L1 L2 S).Ghat) * y *
        (k : (f112Amalgam L1 L2 S).Ghat)⁻¹ ∈ caseAR (f112Gamma1 L1 L2 S) :=
      le_iSup₂ (f := fun α (_ : α ∈ CosetGeom.nbrs (f112Gamma1 L1 L2 S)) => caseAX α)
        ((k : f112Acting L1 L2 S) • f112Gamma0 L1 L2 S) hkγ hyX
    refine Subgroup.mem_map.mpr ⟨(k : (f112Amalgam L1 L2 S).Ghat) * y *
      (k : (f112Amalgam L1 L2 S).Ghat)⁻¹, hconj, ?_⟩
    rw [map_mul, map_mul, map_inv, ← hk_eq, coe_f112StabEquiv1_caseATheta k, ← hyx]

theorem caseATheta_injOn_stab_γ₁ :
    Set.InjOn (caseATheta L1 L2 S)
      (CosetGeom.stab (f112Gamma1 L1 L2 S) : Set (f112Amalgam L1 L2 S).Ghat) := by
  intro x hx y hy hxy
  obtain ⟨kx, hkx, hkx_eq⟩ := Subgroup.mem_map.mp hx
  obtain ⟨ky, hky, hky_eq⟩ := Subgroup.mem_map.mp hy
  have hkx' : (kx : (f112Amalgam L1 L2 S).Ghat) = x := hkx_eq
  have hky' : (ky : (f112Amalgam L1 L2 S).Ghat) = y := hky_eq
  have h1 : caseATheta L1 L2 S (kx : (f112Amalgam L1 L2 S).Ghat) =
      caseATheta L1 L2 S (ky : (f112Amalgam L1 L2 S).Ghat) := by
    rw [hkx', hky']; exact hxy
  have h2 : f112StabEquiv1 L1 L2 S ⟨kx, hkx⟩ = f112StabEquiv1 L1 L2 S ⟨ky, hky⟩ := by
    apply Subtype.ext
    rw [coe_f112StabEquiv1_caseATheta, coe_f112StabEquiv1_caseATheta]
    exact h1
  have h3 : (⟨kx, hkx⟩ : MulAction.stabilizer (f112Acting L1 L2 S) (f112Gamma1 L1 L2 S)) =
      ⟨ky, hky⟩ := (f112StabEquiv1 L1 L2 S).injective h2
  rw [← hkx', ← hky']
  exact congrArg (fun w : MulAction.stabilizer (f112Acting L1 L2 S) (f112Gamma1 L1 L2 S) =>
    ((w : f112Acting L1 L2 S) : (f112Amalgam L1 L2 S).Ghat)) h3

theorem caseA_mem_R_γ₁_iff
    {a : ℕ}
    (hfr : Str83G4Frame L1 L2 S a)
    (h : MulAction.stabilizer (f112Acting L1 L2 S) (f112Gamma1 L1 L2 S)) :
    ((h : f112Acting L1 L2 S) : (f112Amalgam L1 L2 S).Ghat) ∈ caseAR (f112Gamma1 L1 L2 S) ↔
      (f112StabEquiv1 L1 L2 S h : G) ∈ str83R L1 L2 S := by
  constructor
  · intro hh
    rw [coe_f112StabEquiv1_caseATheta h]
    have h1 := Subgroup.mem_map_of_mem (caseATheta L1 L2 S) hh
    rwa [caseATheta_map_R_γ₁] at h1
  · intro hh
    rw [coe_f112StabEquiv1_caseATheta h] at hh
    have hmem : caseATheta L1 L2 S
        ((h : f112Acting L1 L2 S) : (f112Amalgam L1 L2 S).Ghat) ∈
        (caseAR (f112Gamma1 L1 L2 S)).map (caseATheta L1 L2 S) := by
      rwa [caseATheta_map_R_γ₁]
    obtain ⟨x, hx, hxθ⟩ := Subgroup.mem_map.mp hmem
    have hx' : x = ((h : f112Acting L1 L2 S) : (f112Amalgam L1 L2 S).Ghat) :=
      caseATheta_injOn_stab_γ₁ (caseA_R_le_stab hfr CosetGeom.vtype_γ₁ hx)
        (Subgroup.mem_map.mpr ⟨(h : f112Acting L1 L2 S), h.2, rfl⟩) hxθ
    rwa [hx'] at hx

end CFSG.Quasithin.Stroth

end
