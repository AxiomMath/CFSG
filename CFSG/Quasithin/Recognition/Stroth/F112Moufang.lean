module
public import CFSG.Quasithin.Recognition.Stroth.F112Tree
public import CFSG.Quasithin.Recognition.Stroth.WeissCount
public import CFSG.GH74.GLS.Stage2.Bender.Thm2.T3Lift

public section

namespace CFSG.Quasithin.Stroth

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.F112R

universe u

noncomputable section

variable {G : Type} [Group G] [Finite G]

private theorem f112Θγ₀ (L1 L2 S : Subgroup G) :
    (f112Completion L1 L2 S).Θ (f112Completion_isFaithful L1 L2 S) (f112Gamma0 L1 L2 S) =
      CosetGeom.γ₀ ((f112Completion L1 L2 S).φ1.range ⊔ (f112Completion L1 L2 S).φ2.range)
        (f112Completion L1 L2 S).φ1.range (f112Completion L1 L2 S).φ2.range :=
  ((f112Completion L1 L2 S).coverData (f112Completion_isFaithful L1 L2 S)).Θ_γ₀

private theorem f112Θγ₁ (L1 L2 S : Subgroup G) :
    (f112Completion L1 L2 S).Θ (f112Completion_isFaithful L1 L2 S) (f112Gamma1 L1 L2 S) =
      CosetGeom.γ₁ ((f112Completion L1 L2 S).φ1.range ⊔ (f112Completion L1 L2 S).φ2.range)
        (f112Completion L1 L2 S).φ1.range (f112Completion L1 L2 S).φ2.range :=
  ((f112Completion L1 L2 S).coverData (f112Completion_isFaithful L1 L2 S)).Θ_γ₁

private def cosetAct {X : Type} [Group X] {A B : Subgroup X} (x : ↥(A ⊔ B))
    (v : CosetGeom (A ⊔ B) A B) : CosetGeom (A ⊔ B) A B := x • v

private theorem cosetAct_mul {X : Type} [Group X] {A B : Subgroup X} (a b : ↥(A ⊔ B))
    (v : CosetGeom (A ⊔ B) A B) : cosetAct (a * b) v = cosetAct a (cosetAct b v) :=
  mul_smul a b v

private theorem cosetAct_γ₁_eq_iff {X : Type} [Group X] {A B : Subgroup X} (x : ↥(A ⊔ B)) :
    cosetAct x (CosetGeom.γ₁ (A ⊔ B) A B) = CosetGeom.γ₁ (A ⊔ B) A B ↔ (x : X) ∈ B := by
  constructor
  · intro h
    have := CosetGeom.mem_stab_of_smul_eq (γ := CosetGeom.γ₁ (A ⊔ B) A B) h
    rwa [CosetGeom.stab_γ₁ (le_sup_right : B ≤ A ⊔ B)] at this
  · intro h
    exact CosetGeom.smul_eq_of_mem_stab (γ := CosetGeom.γ₁ (A ⊔ B) A B) (by
      rw [CosetGeom.stab_γ₁ (le_sup_right : B ≤ A ⊔ B)]; exact h)

private theorem cosetAct_eq_iff {X : Type} [Group X] {A B : Subgroup X} (a b : ↥(A ⊔ B))
    (v : CosetGeom (A ⊔ B) A B) :
    cosetAct a v = cosetAct b v ↔ cosetAct (b⁻¹ * a) v = v := by
  constructor
  · intro h
    calc cosetAct (b⁻¹ * a) v = cosetAct b⁻¹ (cosetAct a v) := cosetAct_mul b⁻¹ a v
      _ = cosetAct b⁻¹ (cosetAct b v) := by rw [h]
      _ = cosetAct (b⁻¹ * b) v := (cosetAct_mul b⁻¹ b v).symm
      _ = cosetAct 1 v := by rw [inv_mul_cancel]
      _ = v := by rw [cosetAct]; exact one_smul _ _
  · intro h
    calc cosetAct a v = cosetAct (b * (b⁻¹ * a)) v := by rw [mul_inv_cancel_left]
      _ = cosetAct b (cosetAct (b⁻¹ * a) v) := cosetAct_mul b (b⁻¹ * a) v
      _ = cosetAct b v := by rw [h]

private def f112Incl (L1 L2 S : Subgroup G) :
    ↥(L1 ⊔ bigB L1 L2 S) →*
      ↥((f112Completion L1 L2 S).φ1.range ⊔ (f112Completion L1 L2 S).φ2.range) :=
  (((f112Completion L1 L2 S).theta0 (f112Completion_isFaithful L1 L2 S)).comp
    (MulAction.stabilizer (f112Acting L1 L2 S) (f112Gamma0 L1 L2 S)).subtype).comp
    (f112StabEquiv0 L1 L2 S).symm.toMonoidHom

private theorem coe_f112Incl (L1 L2 S : Subgroup G) (p : ↥(L1 ⊔ bigB L1 L2 S)) :
    ((f112Incl L1 L2 S p : ↥((f112Completion L1 L2 S).φ1.range ⊔
      (f112Completion L1 L2 S).φ2.range)) : G) = (p : G) := by
  rw [f112Incl, MonoidHom.comp_apply, MonoidHom.comp_apply, Subgroup.subtype_apply,
    ← coe_f112StabEquiv0]
  change ((f112StabEquiv0 L1 L2 S ((f112StabEquiv0 L1 L2 S).symm p) :
    ↥(L1 ⊔ bigB L1 L2 S)) : G) = (p : G)
  rw [MulEquiv.apply_symm_apply]

private def f112VOf (L1 L2 S : Subgroup G) (p : ↥(L1 ⊔ bigB L1 L2 S)) :
    f112Gamma L1 L2 S :=
  ((f112StabEquiv0 L1 L2 S).symm p : f112Acting L1 L2 S) • f112Gamma1 L1 L2 S

private theorem f112_adj_vOf (L1 L2 S : Subgroup G) (p : ↥(L1 ⊔ bigB L1 L2 S)) :
    (f112Amalgam L1 L2 S).graphHat.Adj (f112Gamma0 L1 L2 S) (f112VOf L1 L2 S p) := by
  set k : f112Acting L1 L2 S := ((f112StabEquiv0 L1 L2 S).symm p : f112Acting L1 L2 S) with hk
  have hfix : k • f112Gamma0 L1 L2 S = f112Gamma0 L1 L2 S :=
    MulAction.mem_stabilizer_iff.mp ((f112StabEquiv0 L1 L2 S).symm p).2
  have hadj := (CosetGeom.smul_adj k).mpr
    (CosetGeom.adj_γ₀_γ₁ (G₀ := (f112Amalgam L1 L2 S).Ghat1 ⊔ (f112Amalgam L1 L2 S).Ghat2)
      (G₁ := (f112Amalgam L1 L2 S).Ghat1) (G₂ := (f112Amalgam L1 L2 S).Ghat2))
  rw [hfix] at hadj
  exact hadj

private theorem f112_Θ_vOf (L1 L2 S : Subgroup G) (p : ↥(L1 ⊔ bigB L1 L2 S)) :
    (f112Completion L1 L2 S).Θ (f112Completion_isFaithful L1 L2 S) (f112VOf L1 L2 S p) =
      cosetAct (f112Incl L1 L2 S p)
        (CosetGeom.γ₁ ((f112Completion L1 L2 S).φ1.range ⊔ (f112Completion L1 L2 S).φ2.range)
          (f112Completion L1 L2 S).φ1.range (f112Completion L1 L2 S).φ2.range) := by
  rw [f112VOf, RankTwoAmalgam.Completion.Θ_smul, f112Θγ₁]
  rfl

private theorem f112Rangeφ₂ (L1 L2 S : Subgroup G) :
    (f112Completion L1 L2 S).φ2.range =
      (L2 ⊔ bigB L1 L2 S).subgroupOf ((L1 ⊔ bigB L1 L2 S) ⊔ (L2 ⊔ bigB L1 L2 S)) :=
  Subgroup.inclusion_range (le_sup_right : (L2 ⊔ bigB L1 L2 S) ≤
    (L1 ⊔ bigB L1 L2 S) ⊔ (L2 ⊔ bigB L1 L2 S))

private theorem f112_mem_range_φ₂_iff (L1 L2 S : Subgroup G)
    (y : ↥((L1 ⊔ bigB L1 L2 S) ⊔ (L2 ⊔ bigB L1 L2 S))) :
    y ∈ (f112Completion L1 L2 S).φ2.range ↔ (y : G) ∈ L2 ⊔ bigB L1 L2 S := by
  rw [f112Rangeφ₂]
  exact Subgroup.mem_subgroupOf

private theorem f112_mem_range_φ₂_iff' (L1 L2 S : Subgroup G)
    (x : ↥((f112Completion L1 L2 S).φ1.range ⊔ (f112Completion L1 L2 S).φ2.range)) :
    x.1 ∈ (f112Completion L1 L2 S).φ2.range ↔ (x : G) ∈ L2 ⊔ bigB L1 L2 S :=
  f112_mem_range_φ₂_iff L1 L2 S x.1

private theorem f112_vOf_eq_iff {L1 L2 S : Subgroup G}
    (hF : F112HypW L1 L2 S) {p q : ↥(L1 ⊔ bigB L1 L2 S)} :
    f112VOf L1 L2 S p = f112VOf L1 L2 S q ↔ (q : G)⁻¹ * (p : G) ∈ bigB L1 L2 S := by
  have hc : (f112Completion L1 L2 S).IsFaithful := f112Completion_isFaithful L1 L2 S
  have hcoe : ∀ a b : ↥(L1 ⊔ bigB L1 L2 S),
      ((((f112Incl L1 L2 S a)⁻¹ * f112Incl L1 L2 S b :
        ↥((f112Completion L1 L2 S).φ1.range ⊔
          (f112Completion L1 L2 S).φ2.range)) : G)) = (a : G)⁻¹ * (b : G) := by
    intro a b
    simp only [Subgroup.coe_inv, Subgroup.coe_mul, coe_f112Incl]
  constructor
  · intro h
    have hΘ : (f112Completion L1 L2 S).Θ hc (f112VOf L1 L2 S p) =
        (f112Completion L1 L2 S).Θ hc (f112VOf L1 L2 S q) := by rw [h]
    rw [f112_Θ_vOf, f112_Θ_vOf] at hΘ
    have hfix : cosetAct ((f112Incl L1 L2 S q)⁻¹ * f112Incl L1 L2 S p)
        (CosetGeom.γ₁ ((f112Completion L1 L2 S).φ1.range ⊔
          (f112Completion L1 L2 S).φ2.range)
          (f112Completion L1 L2 S).φ1.range (f112Completion L1 L2 S).φ2.range) =
        CosetGeom.γ₁ ((f112Completion L1 L2 S).φ1.range ⊔
          (f112Completion L1 L2 S).φ2.range)
          (f112Completion L1 L2 S).φ1.range (f112Completion L1 L2 S).φ2.range :=
      (cosetAct_eq_iff (f112Incl L1 L2 S p) (f112Incl L1 L2 S q) _).mp hΘ
    have hmem := (cosetAct_γ₁_eq_iff ((f112Incl L1 L2 S q)⁻¹ * f112Incl L1 L2 S p)).mp hfix
    have hmem2 : (q : G)⁻¹ * (p : G) ∈ L2 ⊔ bigB L1 L2 S := by
      have h1 := (f112_mem_range_φ₂_iff' L1 L2 S
        ((f112Incl L1 L2 S q)⁻¹ * f112Incl L1 L2 S p)).mp hmem
      rwa [hcoe q p] at h1
    have hmem1 : (q : G)⁻¹ * (p : G) ∈ L1 ⊔ bigB L1 L2 S :=
      Subgroup.mul_mem _ (Subgroup.inv_mem _ q.2) p.2
    have hinf := Subgroup.mem_inf.mpr ⟨hmem1, hmem2⟩
    rwa [f112_parabolic_inf_eq_bigB hF] at hinf
  · intro h
    have hmem : (q : G)⁻¹ * (p : G) ∈ L2 ⊔ bigB L1 L2 S :=
      (le_sup_right : bigB L1 L2 S ≤ L2 ⊔ bigB L1 L2 S) h
    have hfix : cosetAct ((f112Incl L1 L2 S q)⁻¹ * f112Incl L1 L2 S p)
        (CosetGeom.γ₁ ((f112Completion L1 L2 S).φ1.range ⊔
          (f112Completion L1 L2 S).φ2.range)
          (f112Completion L1 L2 S).φ1.range (f112Completion L1 L2 S).φ2.range) =
        CosetGeom.γ₁ ((f112Completion L1 L2 S).φ1.range ⊔
          (f112Completion L1 L2 S).φ2.range)
          (f112Completion L1 L2 S).φ1.range (f112Completion L1 L2 S).φ2.range := by
      refine (cosetAct_γ₁_eq_iff _).mpr ?_
      rw [f112_mem_range_φ₂_iff' L1 L2 S, hcoe]
      exact hmem
    have hΘ : (f112Completion L1 L2 S).Θ hc (f112VOf L1 L2 S p) =
        (f112Completion L1 L2 S).Θ hc (f112VOf L1 L2 S q) := by
      rw [f112_Θ_vOf, f112_Θ_vOf]
      exact (cosetAct_eq_iff (f112Incl L1 L2 S p) (f112Incl L1 L2 S q) _).mpr hfix
    exact (f112Completion L1 L2 S).graphCovering hc |>.loc_inj (f112Gamma0 L1 L2 S)
      (f112VOf L1 L2 S p) (f112VOf L1 L2 S q) (f112_adj_vOf L1 L2 S p)
      (f112_adj_vOf L1 L2 S q) hΘ

private theorem f112_exists_vOf {L1 L2 S : Subgroup G}
    (hF : F112HypW L1 L2 S) {w : f112Gamma L1 L2 S}
    (hw : w ∈ (f112Amalgam L1 L2 S).graphHat.neighborSet (f112Gamma0 L1 L2 S)) :
    ∃ p : ↥(L1 ⊔ bigB L1 L2 S), f112VOf L1 L2 S p = w := by
  have hadj : (f112Amalgam L1 L2 S).graphHat.Adj (f112Gamma0 L1 L2 S) w := hw
  have hadj1 : (f112Amalgam L1 L2 S).graphHat.Adj (f112Gamma0 L1 L2 S) (f112Gamma1 L1 L2 S) :=
    CosetGeom.adj_γ₀_γ₁
  have hγ₁ : (f112Gamma1 L1 L2 S) ∈
      (f112Amalgam L1 L2 S).graphHat.neighborSet (f112Gamma0 L1 L2 S) := hadj1
  obtain ⟨g, hg, hgw⟩ := f112_stabilizer_transitive_on_nbrs hF hγ₁ hw
  exact ⟨f112StabEquiv0 L1 L2 S ⟨g, hg⟩, by rw [f112VOf, MulEquiv.symm_apply_apply]; exact hgw⟩

private theorem f112_smul_vOf (L1 L2 S : Subgroup G) (h : f112Acting L1 L2 S)
    (hh : h ∈ MulAction.stabilizer (f112Acting L1 L2 S) (f112Gamma0 L1 L2 S))
    (p : ↥(L1 ⊔ bigB L1 L2 S)) :
    h • f112VOf L1 L2 S p =
      f112VOf L1 L2 S (f112StabEquiv0 L1 L2 S ⟨h, hh⟩ * p) := by
  have hmem : h * ((f112StabEquiv0 L1 L2 S).symm p : f112Acting L1 L2 S) ∈
      MulAction.stabilizer (f112Acting L1 L2 S) (f112Gamma0 L1 L2 S) :=
    (MulAction.stabilizer (f112Acting L1 L2 S) (f112Gamma0 L1 L2 S)).mul_mem hh
      ((f112StabEquiv0 L1 L2 S).symm p).2
  have hx : f112StabEquiv0 L1 L2 S
      (⟨h * ((f112StabEquiv0 L1 L2 S).symm p : f112Acting L1 L2 S), hmem⟩ :
        ↥(MulAction.stabilizer (f112Acting L1 L2 S) (f112Gamma0 L1 L2 S))) =
      f112StabEquiv0 L1 L2 S ⟨h, hh⟩ * p := by
    have h1 : (⟨h * ((f112StabEquiv0 L1 L2 S).symm p : f112Acting L1 L2 S), hmem⟩ :
        ↥(MulAction.stabilizer (f112Acting L1 L2 S) (f112Gamma0 L1 L2 S))) =
        ⟨h, hh⟩ * (f112StabEquiv0 L1 L2 S).symm p := Subtype.ext rfl
    rw [h1, map_mul, MulEquiv.apply_symm_apply]
  have hmul : h * ((f112StabEquiv0 L1 L2 S).symm p : f112Acting L1 L2 S) =
      ((f112StabEquiv0 L1 L2 S).symm (f112StabEquiv0 L1 L2 S ⟨h, hh⟩ * p) :
        f112Acting L1 L2 S) := by
    have heq : (⟨h * ((f112StabEquiv0 L1 L2 S).symm p : f112Acting L1 L2 S), hmem⟩ :
        ↥(MulAction.stabilizer (f112Acting L1 L2 S) (f112Gamma0 L1 L2 S))) =
        (f112StabEquiv0 L1 L2 S).symm (f112StabEquiv0 L1 L2 S ⟨h, hh⟩ * p) :=
      (f112StabEquiv0 L1 L2 S).injective (by rw [hx, MulEquiv.apply_symm_apply])
    exact congrArg Subtype.val heq
  rw [f112VOf, ← mul_smul, hmul, f112VOf]

private theorem f112_smul_vOf' (L1 L2 S : Subgroup G)
    (k : ↥(MulAction.stabilizer (f112Acting L1 L2 S) (f112Gamma0 L1 L2 S)))
    (p : ↥(L1 ⊔ bigB L1 L2 S)) :
    (k : f112Acting L1 L2 S) • f112VOf L1 L2 S p =
      f112VOf L1 L2 S (f112StabEquiv0 L1 L2 S k * p) :=
  f112_smul_vOf L1 L2 S (k : f112Acting L1 L2 S) k.2 p

private theorem mem_normalCore_iff {H : Type*} [Group H] {Q : Subgroup H} {x : H} :
    x ∈ Q.normalCore ↔ ∀ g : H, g⁻¹ * x * g ∈ Q := by
  rw [Subgroup.normalCore_eq_iInf_map_conj, Subgroup.mem_iInf]
  constructor
  · intro h g
    obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp (h g)
    change (MulAut.conj g) y = x at hyx
    rw [MulAut.conj_apply] at hyx
    have h2 : g⁻¹ * x * g = y := by rw [← hyx]; group
    rw [h2]; exact hy
  · intro h g
    refine Subgroup.mem_map.mpr ⟨g⁻¹ * x * g, h g, ?_⟩
    change (MulAut.conj g) (g⁻¹ * x * g) = x
    rw [MulAut.conj_apply]
    group

theorem f112_fixes_nbrs_iff_mem_K1 {L1 L2 S : Subgroup G}
    (hF : F112HypW L1 L2 S) (h : f112Acting L1 L2 S)
    (hh : h ∈ MulAction.stabilizer (f112Acting L1 L2 S) (f112Gamma0 L1 L2 S)) :
    (∀ w, (f112Amalgam L1 L2 S).graphHat.Adj (f112Gamma0 L1 L2 S) w → h • w = w) ↔
      f112StabEquiv0 L1 L2 S ⟨h, hh⟩ ∈ f112K1 L1 L2 S := by
  have hK1 : f112K1 L1 L2 S =
      ((bigB L1 L2 S).subgroupOf (L1 ⊔ bigB L1 L2 S)).normalCore := by
    rw [f112K1, f112_parabolic_inf_eq_bigB hF]
  set x : ↥(L1 ⊔ bigB L1 L2 S) := f112StabEquiv0 L1 L2 S ⟨h, hh⟩
  constructor
  · intro hfix
    rw [hK1, mem_normalCore_iff]
    intro g
    have hv : f112VOf L1 L2 S (x * g) = f112VOf L1 L2 S g := by
      rw [← f112_smul_vOf L1 L2 S h hh g]
      exact hfix _ (f112_adj_vOf L1 L2 S g)
    have h2 := (f112_vOf_eq_iff hF).mp hv
    have h3 : (g : G)⁻¹ * (x : G) * (g : G) ∈ bigB L1 L2 S := by
      simpa [Subgroup.coe_mul, Subgroup.coe_inv, mul_assoc] using h2
    exact Subgroup.mem_subgroupOf.mpr h3
  · intro hx w hw
    obtain ⟨p, rfl⟩ := f112_exists_vOf hF hw
    rw [f112_smul_vOf L1 L2 S h hh p]
    refine (f112_vOf_eq_iff hF).mpr ?_
    have hmem := mem_normalCore_iff.mp (hK1 ▸ hx) p
    have hmem' : ((p⁻¹ : ↥(L1 ⊔ bigB L1 L2 S)) : G) * (x : G) *
        (p : G) ∈ bigB L1 L2 S := Subgroup.mem_subgroupOf.mp hmem
    simpa [Subgroup.coe_mul, Subgroup.coe_inv, mul_assoc] using hmem'

theorem f112_smul_γ₁_eq_iff {L1 L2 S : Subgroup G}
    (hF : F112HypW L1 L2 S) (h : f112Acting L1 L2 S)
    (hh : h ∈ MulAction.stabilizer (f112Acting L1 L2 S) (f112Gamma0 L1 L2 S)) :
    h • f112Gamma1 L1 L2 S = f112Gamma1 L1 L2 S ↔
      (f112StabEquiv0 L1 L2 S ⟨h, hh⟩ : G) ∈ bigB L1 L2 S := by
  have hc : (f112Completion L1 L2 S).IsFaithful := f112Completion_isFaithful L1 L2 S
  have hP1 : (f112StabEquiv0 L1 L2 S ⟨h, hh⟩ : G) ∈ L1 ⊔ bigB L1 L2 S :=
    (f112StabEquiv0 L1 L2 S ⟨h, hh⟩).2
  constructor
  · intro hfix
    have hΘ : (f112Completion L1 L2 S).Θ hc (h • f112Gamma1 L1 L2 S) =
        (f112Completion L1 L2 S).Θ hc (f112Gamma1 L1 L2 S) := by rw [hfix]
    rw [RankTwoAmalgam.Completion.Θ_smul, f112Θγ₁] at hΘ
    have hstab : ((f112Completion L1 L2 S).theta0 hc h).1 ∈
        (f112Completion L1 L2 S).φ2.range := by
      have h1 := CosetGeom.mem_stab_of_smul_eq
        (γ := CosetGeom.γ₁ ((f112Completion L1 L2 S).φ1.range ⊔
          (f112Completion L1 L2 S).φ2.range) (f112Completion L1 L2 S).φ1.range
          (f112Completion L1 L2 S).φ2.range) hΘ
      rwa [CosetGeom.stab_γ₁ (le_sup_right : (f112Completion L1 L2 S).φ2.range ≤
        (f112Completion L1 L2 S).φ1.range ⊔ (f112Completion L1 L2 S).φ2.range)] at h1
    have hP2 : (f112StabEquiv0 L1 L2 S ⟨h, hh⟩ : G) ∈ L2 ⊔ bigB L1 L2 S := by
      rw [coe_f112StabEquiv0 L1 L2 S ⟨h, hh⟩]
      exact (f112_mem_range_φ₂_iff' L1 L2 S ((f112Completion L1 L2 S).theta0 hc h)).mp hstab
    have hinf := Subgroup.mem_inf.mpr ⟨hP1, hP2⟩
    rwa [f112_parabolic_inf_eq_bigB hF] at hinf
  · intro hB
    have hP2 : (f112StabEquiv0 L1 L2 S ⟨h, hh⟩ : G) ∈ L2 ⊔ bigB L1 L2 S :=
      (le_sup_right : bigB L1 L2 S ≤ L2 ⊔ bigB L1 L2 S) hB
    have hstab : ((f112Completion L1 L2 S).theta0 hc h : G) ∈ L2 ⊔ bigB L1 L2 S := by
      rw [← coe_f112StabEquiv0 L1 L2 S ⟨h, hh⟩]
      exact hP2
    have hmem : ((f112Completion L1 L2 S).theta0 hc h).1 ∈
        (f112Completion L1 L2 S).φ2.range :=
      (f112_mem_range_φ₂_iff' L1 L2 S ((f112Completion L1 L2 S).theta0 hc h)).mpr hstab
    have hfix : cosetAct ((f112Completion L1 L2 S).theta0 hc h)
        (CosetGeom.γ₁ ((f112Completion L1 L2 S).φ1.range ⊔
          (f112Completion L1 L2 S).φ2.range) (f112Completion L1 L2 S).φ1.range
          (f112Completion L1 L2 S).φ2.range) =
        CosetGeom.γ₁ ((f112Completion L1 L2 S).φ1.range ⊔
          (f112Completion L1 L2 S).φ2.range) (f112Completion L1 L2 S).φ1.range
          (f112Completion L1 L2 S).φ2.range :=
      (cosetAct_γ₁_eq_iff _).mpr hmem
    have hΘ : (f112Completion L1 L2 S).Θ hc (h • f112Gamma1 L1 L2 S) =
        (f112Completion L1 L2 S).Θ hc (f112Gamma1 L1 L2 S) := by
      rw [RankTwoAmalgam.Completion.Θ_smul, f112Θγ₁]
      exact hfix
    have hfix0 : h • f112Gamma0 L1 L2 S = f112Gamma0 L1 L2 S :=
      MulAction.mem_stabilizer_iff.mp hh
    have hadj : (f112Amalgam L1 L2 S).graphHat.Adj (f112Gamma0 L1 L2 S)
        (h • f112Gamma1 L1 L2 S) := by
      have h := (CosetGeom.smul_adj h).mpr
        (CosetGeom.adj_γ₀_γ₁ (G₀ := (f112Amalgam L1 L2 S).Ghat1 ⊔ (f112Amalgam L1 L2 S).Ghat2)
          (G₁ := (f112Amalgam L1 L2 S).Ghat1) (G₂ := (f112Amalgam L1 L2 S).Ghat2))
      rwa [hfix0] at h
    exact (f112Completion L1 L2 S).graphCovering hc |>.loc_inj (f112Gamma0 L1 L2 S)
      (h • f112Gamma1 L1 L2 S) (f112Gamma1 L1 L2 S) hadj CosetGeom.adj_γ₀_γ₁ hΘ

theorem f112_exists_smul_nbr_of_fac {L1 L2 S : Subgroup G}
    (hF : F112HypW L1 L2 S) {C : Subgroup G} (hCP : C ≤ L1 ⊔ bigB L1 L2 S)
    (hfac : ∀ p ∈ L1 ⊔ bigB L1 L2 S, ∃ c ∈ C, ∃ b ∈ bigB L1 L2 S, p = c * b)
    {w₁ w₂ : f112Gamma L1 L2 S}
    (hw₁ : (f112Amalgam L1 L2 S).graphHat.Adj (f112Gamma0 L1 L2 S) w₁)
    (hw₂ : (f112Amalgam L1 L2 S).graphHat.Adj (f112Gamma0 L1 L2 S) w₂) :
    ∃ k : ↥(MulAction.stabilizer (f112Acting L1 L2 S) (f112Gamma0 L1 L2 S)),
      (f112StabEquiv0 L1 L2 S k : G) ∈ C ∧ (k : f112Acting L1 L2 S) • w₁ = w₂ := by
  obtain ⟨p₁, rfl⟩ := f112_exists_vOf hF hw₁
  obtain ⟨p₂, rfl⟩ := f112_exists_vOf hF hw₂
  obtain ⟨c₁, hc₁C, b₁, hb₁, hp₁⟩ := hfac p₁ p₁.2
  obtain ⟨c₂, hc₂C, b₂, hb₂, hp₂⟩ := hfac p₂ p₂.2
  have hc₁P : c₁ ∈ L1 ⊔ bigB L1 L2 S := hCP hc₁C
  have hc₂P : c₂ ∈ L1 ⊔ bigB L1 L2 S := hCP hc₂C
  have hvc : ∀ (c : G) (hc : c ∈ L1 ⊔ bigB L1 L2 S) (b : G) (hb : b ∈ bigB L1 L2 S)
      (p : ↥(L1 ⊔ bigB L1 L2 S)), (p : G) = c * b →
      f112VOf L1 L2 S p = f112VOf L1 L2 S ⟨c, hc⟩ := by
    intro c hc b hb p hp
    refine (f112_vOf_eq_iff hF).mpr ?_
    have h1 : ((⟨c, hc⟩ : ↥(L1 ⊔ bigB L1 L2 S)) : G)⁻¹ * (p : G) = b := by
      rw [hp]; group
    rw [h1]
    exact hb
  have hv₁ : f112VOf L1 L2 S p₁ = f112VOf L1 L2 S ⟨c₁, hc₁P⟩ := hvc c₁ hc₁P b₁ hb₁ p₁ hp₁
  have hv₂ : f112VOf L1 L2 S p₂ = f112VOf L1 L2 S ⟨c₂, hc₂P⟩ := hvc c₂ hc₂P b₂ hb₂ p₂ hp₂
  refine ⟨(f112StabEquiv0 L1 L2 S).symm
    ((⟨c₂, hc₂P⟩ : ↥(L1 ⊔ bigB L1 L2 S)) * (⟨c₁, hc₁P⟩ : ↥(L1 ⊔ bigB L1 L2 S))⁻¹), ?_, ?_⟩
  · rw [MulEquiv.apply_symm_apply]
    exact C.mul_mem hc₂C (C.inv_mem hc₁C)
  · rw [hv₁, f112_smul_vOf', MulEquiv.apply_symm_apply]
    have h3 : ((⟨c₂, hc₂P⟩ : ↥(L1 ⊔ bigB L1 L2 S)) *
        (⟨c₁, hc₁P⟩ : ↥(L1 ⊔ bigB L1 L2 S))⁻¹) *
        (⟨c₁, hc₁P⟩ : ↥(L1 ⊔ bigB L1 L2 S)) = ⟨c₂, hc₂P⟩ := by group
    rw [h3, hv₂]

private theorem f112_pCoreOf_le_bigB_left {L1 L2 S : Subgroup G}
    (hF : F112HypW L1 L2 S) : pCoreOf 2 L1 ≤ bigB L1 L2 S :=
  (Hyp111.pCoreOf_le_pCoreOf_vertex hF.1).trans
    ((F7.isSylowTwoOf_pCoreOf_le (f112_isSylowTwoOf_P1 hF)).trans
      (le_sup_right : S ≤ bigB L1 L2 S))

private theorem f112_pCoreOf_le_bigB_right {L1 L2 S : Subgroup G}
    (hF : F112HypW L1 L2 S) : pCoreOf 2 L2 ≤ bigB L1 L2 S := by
  have h' := Hyp111.pCoreOf_le_pCoreOf_vertex (L1 := L2) (L2 := L1) (S := S) hF.1.symm
  rw [bigB_comm L1 L2 S] at h'
  exact h'.trans ((F7.isSylowTwoOf_pCoreOf_le (f112_isSylowTwoOf_P2 hF)).trans
    (le_sup_right : S ≤ bigB L1 L2 S))

theorem f112_kernel_centralizes_of_isSimpleGroup
    {L1 L2 S : Subgroup G} (hF : F112HypW L1 L2 S) (hL1 : IsSimpleGroup (oTwoQuot ↥L1)) :
    ∀ t ∈ (f112K1 L1 L2 S).map (L1 ⊔ bigB L1 L2 S).subtype, ∀ l ∈ L1,
      l * t * l⁻¹ * t⁻¹ ∈ pCoreOf 2 L1 := by
  have hR : Hyp111R L1 L2 S := Hyp111R.of_hyp111 rankOneListedFacts hF.1
  have hnorm : bigB L1 L2 S ≤ Subgroup.normalizer (L1 : Set G) :=
    (F1.bigB_le_normalizer_left hR).1
  intro t ht l hl
  obtain ⟨k, hkK1, rfl⟩ := Subgroup.mem_map.mp ht
  have hkB : (k : G) ∈ bigB L1 L2 S := by
    have h1 : k ∈ ((L1 ⊔ bigB L1 L2 S) ⊓ (L2 ⊔ bigB L1 L2 S)).subgroupOf
        (L1 ⊔ bigB L1 L2 S) := Subgroup.normalCore_le _ hkK1
    have h2 : (k : G) ∈ (L1 ⊔ bigB L1 L2 S) ⊓ (L2 ⊔ bigB L1 L2 S) :=
      Subgroup.mem_subgroupOf.mp h1
    rwa [f112_parabolic_inf_eq_bigB hF] at h2
  have hkL : (k : G) * (l : G) * (k : G)⁻¹ ∈ L1 :=
    (Subgroup.mem_normalizer_iff.mp (hnorm hkB) l).mp hl
  have hconjL : (k : G) * (l : G)⁻¹ * (k : G)⁻¹ ∈ L1 := by
    have h := L1.inv_mem hkL
    rwa [show ((k : G) * (l : G) * (k : G)⁻¹)⁻¹ = (k : G) * (l : G)⁻¹ * (k : G)⁻¹ from by
      group] at h
  have hL1mem : (l : G) * (k : G) * (l : G)⁻¹ * (k : G)⁻¹ ∈ L1 := by
    have h1 : (l : G) * (k : G) * (l : G)⁻¹ * (k : G)⁻¹ =
        (l : G) * ((k : G) * (l : G)⁻¹ * (k : G)⁻¹) := by group
    rw [h1]; exact L1.mul_mem hl hconjL
  have hK1map : (l : G) * (k : G) * (l : G)⁻¹ * (k : G)⁻¹ ∈
      (f112K1 L1 L2 S).map (L1 ⊔ bigB L1 L2 S).subtype := by
    have h1 : (⟨l, (le_sup_left : L1 ≤ L1 ⊔ bigB L1 L2 S) hl⟩ :
        ↥(L1 ⊔ bigB L1 L2 S)) * k *
        (⟨l, (le_sup_left : L1 ≤ L1 ⊔ bigB L1 L2 S) hl⟩ :
          ↥(L1 ⊔ bigB L1 L2 S))⁻¹ ∈ f112K1 L1 L2 S :=
      (Subgroup.normalCore_normal _).conj_mem k hkK1 _
    have h2 : (l : G) * (k : G) * (l : G)⁻¹ ∈
        (f112K1 L1 L2 S).map (L1 ⊔ bigB L1 L2 S).subtype :=
      Subgroup.mem_map.mpr ⟨_, h1, rfl⟩
    have h3 : (k : G)⁻¹ ∈ (f112K1 L1 L2 S).map (L1 ⊔ bigB L1 L2 S).subtype :=
      Subgroup.mem_map.mpr ⟨k⁻¹, (f112K1 L1 L2 S).inv_mem hkK1, rfl⟩
    rw [show (l : G) * (k : G) * (l : G)⁻¹ * (k : G)⁻¹ =
      ((l : G) * (k : G) * (l : G)⁻¹) * (k : G)⁻¹ from by group]
    exact Subgroup.mul_mem _ h2 h3
  have hinf : (l : G) * (k : G) * (l : G)⁻¹ * (k : G)⁻¹ ∈
      L1 ⊓ (f112K1 L1 L2 S).map (L1 ⊔ bigB L1 L2 S).subtype :=
    Subgroup.mem_inf.mpr ⟨hL1mem, hK1map⟩
  rwa [f112_inf_map_K1_eq_pCoreOf hF hL1] at hinf

theorem f112_kernel_centralizes_of_isSimpleGroup_right
    {L1 L2 S : Subgroup G} (hF : F112HypW L1 L2 S) (hL2 : IsSimpleGroup (oTwoQuot ↥L2)) :
    ∀ t ∈ (f112K2 L1 L2 S).map (L2 ⊔ bigB L1 L2 S).subtype, ∀ l ∈ L2,
      l * t * l⁻¹ * t⁻¹ ∈ pCoreOf 2 L2 := by
  have hR : Hyp111R L1 L2 S := Hyp111R.of_hyp111 rankOneListedFacts hF.1
  have hnorm : bigB L1 L2 S ≤ Subgroup.normalizer (L2 : Set G) :=
    (F1.bigB_le_normalizer_left hR).2
  intro t ht l hl
  obtain ⟨k, hkK2, rfl⟩ := Subgroup.mem_map.mp ht
  have hkB : (k : G) ∈ bigB L1 L2 S := by
    have h1 : k ∈ ((L2 ⊔ bigB L1 L2 S) ⊓ (L1 ⊔ bigB L1 L2 S)).subgroupOf
        (L2 ⊔ bigB L1 L2 S) := Subgroup.normalCore_le _ hkK2
    have h2 : (k : G) ∈ (L2 ⊔ bigB L1 L2 S) ⊓ (L1 ⊔ bigB L1 L2 S) :=
      Subgroup.mem_subgroupOf.mp h1
    have h3 : (L2 ⊔ bigB L1 L2 S) ⊓ (L1 ⊔ bigB L1 L2 S) = bigB L1 L2 S := by
      rw [inf_comm]; exact f112_parabolic_inf_eq_bigB hF
    rwa [h3] at h2
  have hkL : (k : G) * (l : G) * (k : G)⁻¹ ∈ L2 :=
    (Subgroup.mem_normalizer_iff.mp (hnorm hkB) l).mp hl
  have hconjL : (k : G) * (l : G)⁻¹ * (k : G)⁻¹ ∈ L2 := by
    have h := L2.inv_mem hkL
    rwa [show ((k : G) * (l : G) * (k : G)⁻¹)⁻¹ = (k : G) * (l : G)⁻¹ * (k : G)⁻¹ from by
      group] at h
  have hL2mem : (l : G) * (k : G) * (l : G)⁻¹ * (k : G)⁻¹ ∈ L2 := by
    have h1 : (l : G) * (k : G) * (l : G)⁻¹ * (k : G)⁻¹ =
        (l : G) * ((k : G) * (l : G)⁻¹ * (k : G)⁻¹) := by group
    rw [h1]; exact L2.mul_mem hl hconjL
  have hK2map : (l : G) * (k : G) * (l : G)⁻¹ * (k : G)⁻¹ ∈
      (f112K2 L1 L2 S).map (L2 ⊔ bigB L1 L2 S).subtype := by
    have h1 : (⟨l, (le_sup_left : L2 ≤ L2 ⊔ bigB L1 L2 S) hl⟩ :
        ↥(L2 ⊔ bigB L1 L2 S)) * k *
        (⟨l, (le_sup_left : L2 ≤ L2 ⊔ bigB L1 L2 S) hl⟩ :
          ↥(L2 ⊔ bigB L1 L2 S))⁻¹ ∈ f112K2 L1 L2 S :=
      (Subgroup.normalCore_normal _).conj_mem k hkK2 _
    have h2 : (l : G) * (k : G) * (l : G)⁻¹ ∈
        (f112K2 L1 L2 S).map (L2 ⊔ bigB L1 L2 S).subtype :=
      Subgroup.mem_map.mpr ⟨_, h1, rfl⟩
    have h3 : (k : G)⁻¹ ∈ (f112K2 L1 L2 S).map (L2 ⊔ bigB L1 L2 S).subtype :=
      Subgroup.mem_map.mpr ⟨k⁻¹, (f112K2 L1 L2 S).inv_mem hkK2, rfl⟩
    rw [show (l : G) * (k : G) * (l : G)⁻¹ * (k : G)⁻¹ =
      ((l : G) * (k : G) * (l : G)⁻¹) * (k : G)⁻¹ from by group]
    exact Subgroup.mul_mem _ h2 h3
  have hinf : (l : G) * (k : G) * (l : G)⁻¹ * (k : G)⁻¹ ∈
      L2 ⊓ (f112K2 L1 L2 S).map (L2 ⊔ bigB L1 L2 S).subtype :=
    Subgroup.mem_inf.mpr ⟨hL2mem, hK2map⟩
  rwa [f112_inf_map_K2_eq_pCoreOf hF hL2] at hinf

private theorem f112_fac_left {L1 L2 S : Subgroup G}
    (hF : F112HypW L1 L2 S) {t : G} {ℓ : ℕ} (hℓ : ℓ.Prime) (hodd : Odd ℓ)
    (htP1 : t ∈ L1 ⊔ bigB L1 L2 S)
    (htord : orderOf (⟨t, htP1⟩ : ↥(L1 ⊔ bigB L1 L2 S)) = ℓ)
    (htK : (⟨t, htP1⟩ : ↥(L1 ⊔ bigB L1 L2 S)) ∈ f112K1 L1 L2 S)
    (hK1 : ∀ t' ∈ (f112K1 L1 L2 S).map (L1 ⊔ bigB L1 L2 S).subtype, ∀ l ∈ L1,
      l * t' * l⁻¹ * t'⁻¹ ∈ pCoreOf 2 L1) :
    ∀ x ∈ L1 ⊔ bigB L1 L2 S,
      ∃ c ∈ Subgroup.centralizer ({t} : Set G) ⊓ L1, ∃ b ∈ bigB L1 L2 S, x = c * b := by
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  have hR : Hyp111R L1 L2 S := Hyp111R.of_hyp111 rankOneListedFacts hF.1
  have hBL1 : bigB L1 L2 S ≤ Subgroup.normalizer (L1 : Set G) :=
    (F1.bigB_le_normalizer_left hR).1
  let E : Subgroup ↥(L1 ⊔ bigB L1 L2 S) :=
    (pCoreOf 2 L1).subgroupOf (L1 ⊔ bigB L1 L2 S)
  have hEnorm : E.Normal := by
    dsimp only [E]
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer
      ((CFSG.LieType.BorelTits.pCoreOf_le 2 L1).trans
        (le_sup_left : L1 ≤ L1 ⊔ bigB L1 L2 S))).mpr
      (sup_le (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 L1)
        (hBL1.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 L1)))
  haveI : E.Normal := hEnorm
  have hEcard : ¬ ℓ ∣ Nat.card ↥E := by
    obtain ⟨n, hn⟩ := (CFSG.LieType.BorelTits.pCoreOf_isPGroup (G := G) 2 L1).exists_card_eq
    have hcard : Nat.card ↥E = Nat.card ↥(pCoreOf 2 L1) := by
      dsimp only [E]
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe
        ((CFSG.LieType.BorelTits.pCoreOf_le 2 L1).trans
          (le_sup_left : L1 ≤ L1 ⊔ bigB L1 L2 S))).toEquiv
    rw [hcard, hn]
    intro hdvd
    have h2 : ℓ ∣ 2 := Nat.Prime.dvd_of_dvd_pow hℓ hdvd
    have hℓ2 : ℓ = 2 := by
      rcases (Nat.dvd_prime Nat.prime_two).mp h2 with h | h
      · exact absurd h hℓ.ne_one
      · exact h
    rw [hℓ2] at hodd
    obtain ⟨k, hk⟩ := hodd
    omega
  intro x hx
  obtain ⟨l, hl, b, hb, rfl⟩ := (F1.mem_sup_iff_exists_mul_of_normalizes hBL1).mp hx
  have hlp1 : l ∈ L1 ⊔ bigB L1 L2 S := (le_sup_left : L1 ≤ L1 ⊔ bigB L1 L2 S) hl
  have hmemE : (⟨t, htP1⟩ * ⟨l, hlp1⟩ * (⟨l, hlp1⟩ * ⟨t, htP1⟩)⁻¹ :
      ↥(L1 ⊔ bigB L1 L2 S)) ∈ E := by
    rw [Subgroup.mem_subgroupOf]
    have h1 : ((⟨t, htP1⟩ * ⟨l, hlp1⟩ * (⟨l, hlp1⟩ * ⟨t, htP1⟩)⁻¹ :
        ↥(L1 ⊔ bigB L1 L2 S)) : G) = (l * t * l⁻¹ * t⁻¹)⁻¹ := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      group
    rw [h1]
    exact (pCoreOf 2 L1).inv_mem
      (hK1 t (Subgroup.mem_map.mpr ⟨⟨t, htP1⟩, htK, rfl⟩) l hl)
  have hcomm : ((⟨t, htP1⟩ : ↥(L1 ⊔ bigB L1 L2 S)) : ↥(L1 ⊔ bigB L1 L2 S) ⧸ E) *
      ((⟨l, hlp1⟩ : ↥(L1 ⊔ bigB L1 L2 S)) : ↥(L1 ⊔ bigB L1 L2 S) ⧸ E) =
      ((⟨l, hlp1⟩ : ↥(L1 ⊔ bigB L1 L2 S)) : ↥(L1 ⊔ bigB L1 L2 S) ⧸ E) *
        ((⟨t, htP1⟩ : ↥(L1 ⊔ bigB L1 L2 S)) : ↥(L1 ⊔ bigB L1 L2 S) ⧸ E) := by
    have h2 : ((⟨t, htP1⟩ * ⟨l, hlp1⟩ * (⟨l, hlp1⟩ * ⟨t, htP1⟩)⁻¹ :
        ↥(L1 ⊔ bigB L1 L2 S)) : ↥(L1 ⊔ bigB L1 L2 S) ⧸ E) = 1 :=
      (QuotientGroup.eq_one_iff _).mpr hmemE
    rw [QuotientGroup.mk_mul E, QuotientGroup.mk_mul E, QuotientGroup.mk_inv E,
      QuotientGroup.mk_mul E] at h2
    rwa [mul_inv_eq_one] at h2
  have hcen : ((⟨l, hlp1⟩ : ↥(L1 ⊔ bigB L1 L2 S)) : ↥(L1 ⊔ bigB L1 L2 S) ⧸ E) ∈
      Subgroup.centralizer ({(((⟨t, htP1⟩ : ↥(L1 ⊔ bigB L1 L2 S)) :
        ↥(L1 ⊔ bigB L1 L2 S) ⧸ E))} : Set (↥(L1 ⊔ bigB L1 L2 S) ⧸ E)) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst hy
    exact hcomm
  obtain ⟨g, hgcent, hgg⟩ :=
    CFSG.GH74.GLS.Stage2.Bender.Thm2.T3.exists_lift_of_mem_centralizer_quotient
      E hℓ hEcard htord hcen
  have hn : (⟨l, hlp1⟩ : ↥(L1 ⊔ bigB L1 L2 S))⁻¹ * g ∈ E := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul E, QuotientGroup.mk_inv E, hgg,
      inv_mul_cancel]
  have hgL : (g : G) ∈ L1 := by
    have h1 : (g : ↥(L1 ⊔ bigB L1 L2 S)) = ⟨l, hlp1⟩ * (⟨l, hlp1⟩⁻¹ * g) := by group
    rw [congrArg Subtype.val h1]
    simp only [Subgroup.coe_mul]
    exact L1.mul_mem hl
      ((CFSG.LieType.BorelTits.pCoreOf_le 2 L1) (Subgroup.mem_subgroupOf.mp hn))
  have hgC : (g : G) ∈ Subgroup.centralizer ({t} : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    rw [hy]
    have h1 : (⟨t, htP1⟩ : ↥(L1 ⊔ bigB L1 L2 S)) * g = g * ⟨t, htP1⟩ :=
      Subgroup.mem_centralizer_iff.mp hgcent ⟨t, htP1⟩ (Set.mem_singleton _)
    calc t * (g : G) =
          (((⟨t, htP1⟩ : ↥(L1 ⊔ bigB L1 L2 S)) * g : ↥(L1 ⊔ bigB L1 L2 S)) : G) := by
          simp only [Subgroup.coe_mul]
      _ = ((g * ⟨t, htP1⟩ : ↥(L1 ⊔ bigB L1 L2 S)) : G) := by rw [h1]
      _ = (g : G) * t := by simp only [Subgroup.coe_mul]
  have hgl : (g : G) = l * ((⟨l, hlp1⟩⁻¹ * g : ↥(L1 ⊔ bigB L1 L2 S)) : G) := by
    have h1 : (g : ↥(L1 ⊔ bigB L1 L2 S)) = ⟨l, hlp1⟩ * (⟨l, hlp1⟩⁻¹ * g) := by group
    calc (g : G) = ((⟨l, hlp1⟩ * (⟨l, hlp1⟩⁻¹ * g) : ↥(L1 ⊔ bigB L1 L2 S)) : G) := by
          rw [← h1]
      _ = l * ((⟨l, hlp1⟩⁻¹ * g : ↥(L1 ⊔ bigB L1 L2 S)) : G) := by
          simp only [Subgroup.coe_mul]
  refine ⟨(g : G), ⟨hgC, hgL⟩, ((⟨l, hlp1⟩⁻¹ * g : ↥(L1 ⊔ bigB L1 L2 S)) : G)⁻¹ * b,
    ?_, ?_⟩
  · exact (bigB L1 L2 S).mul_mem
      (Subgroup.inv_mem _ (f112_pCoreOf_le_bigB_left hF (Subgroup.mem_subgroupOf.mp hn))) hb
  · rw [hgl]; group

private theorem f112_fac_right {L1 L2 S : Subgroup G}
    (hF : F112HypW L1 L2 S) {t : G} {ℓ : ℕ} (hℓ : ℓ.Prime) (hodd : Odd ℓ)
    (htP2 : t ∈ L2 ⊔ bigB L1 L2 S)
    (htord : orderOf (⟨t, htP2⟩ : ↥(L2 ⊔ bigB L1 L2 S)) = ℓ)
    (htK : (⟨t, htP2⟩ : ↥(L2 ⊔ bigB L1 L2 S)) ∈ f112K2 L1 L2 S)
    (hK2 : ∀ t' ∈ (f112K2 L1 L2 S).map (L2 ⊔ bigB L1 L2 S).subtype, ∀ l ∈ L2,
      l * t' * l⁻¹ * t'⁻¹ ∈ pCoreOf 2 L2) :
    ∀ x ∈ L2 ⊔ bigB L1 L2 S,
      ∃ c ∈ Subgroup.centralizer ({t} : Set G) ⊓ L2, ∃ b ∈ bigB L1 L2 S, x = c * b := by
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  have hR : Hyp111R L1 L2 S := Hyp111R.of_hyp111 rankOneListedFacts hF.1
  have hBL2 : bigB L1 L2 S ≤ Subgroup.normalizer (L2 : Set G) :=
    (F1.bigB_le_normalizer_left hR).2
  let E : Subgroup ↥(L2 ⊔ bigB L1 L2 S) :=
    (pCoreOf 2 L2).subgroupOf (L2 ⊔ bigB L1 L2 S)
  have hEnorm : E.Normal := by
    dsimp only [E]
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer
      ((CFSG.LieType.BorelTits.pCoreOf_le 2 L2).trans
        (le_sup_left : L2 ≤ L2 ⊔ bigB L1 L2 S))).mpr
      (sup_le (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 L2)
        (hBL2.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 L2)))
  haveI : E.Normal := hEnorm
  have hEcard : ¬ ℓ ∣ Nat.card ↥E := by
    obtain ⟨n, hn⟩ := (CFSG.LieType.BorelTits.pCoreOf_isPGroup (G := G) 2 L2).exists_card_eq
    have hcard : Nat.card ↥E = Nat.card ↥(pCoreOf 2 L2) := by
      dsimp only [E]
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe
        ((CFSG.LieType.BorelTits.pCoreOf_le 2 L2).trans
          (le_sup_left : L2 ≤ L2 ⊔ bigB L1 L2 S))).toEquiv
    rw [hcard, hn]
    intro hdvd
    have h2 : ℓ ∣ 2 := Nat.Prime.dvd_of_dvd_pow hℓ hdvd
    have hℓ2 : ℓ = 2 := by
      rcases (Nat.dvd_prime Nat.prime_two).mp h2 with h | h
      · exact absurd h hℓ.ne_one
      · exact h
    rw [hℓ2] at hodd
    obtain ⟨k, hk⟩ := hodd
    omega
  intro x hx
  obtain ⟨l, hl, b, hb, rfl⟩ := (F1.mem_sup_iff_exists_mul_of_normalizes hBL2).mp hx
  have hlp2 : l ∈ L2 ⊔ bigB L1 L2 S := (le_sup_left : L2 ≤ L2 ⊔ bigB L1 L2 S) hl
  have hmemE : (⟨t, htP2⟩ * ⟨l, hlp2⟩ * (⟨l, hlp2⟩ * ⟨t, htP2⟩)⁻¹ :
      ↥(L2 ⊔ bigB L1 L2 S)) ∈ E := by
    rw [Subgroup.mem_subgroupOf]
    have h1 : ((⟨t, htP2⟩ * ⟨l, hlp2⟩ * (⟨l, hlp2⟩ * ⟨t, htP2⟩)⁻¹ :
        ↥(L2 ⊔ bigB L1 L2 S)) : G) = (l * t * l⁻¹ * t⁻¹)⁻¹ := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      group
    rw [h1]
    exact (pCoreOf 2 L2).inv_mem
      (hK2 t (Subgroup.mem_map.mpr ⟨⟨t, htP2⟩, htK, rfl⟩) l hl)
  have hcomm : ((⟨t, htP2⟩ : ↥(L2 ⊔ bigB L1 L2 S)) : ↥(L2 ⊔ bigB L1 L2 S) ⧸ E) *
      ((⟨l, hlp2⟩ : ↥(L2 ⊔ bigB L1 L2 S)) : ↥(L2 ⊔ bigB L1 L2 S) ⧸ E) =
      ((⟨l, hlp2⟩ : ↥(L2 ⊔ bigB L1 L2 S)) : ↥(L2 ⊔ bigB L1 L2 S) ⧸ E) *
        ((⟨t, htP2⟩ : ↥(L2 ⊔ bigB L1 L2 S)) : ↥(L2 ⊔ bigB L1 L2 S) ⧸ E) := by
    have h2 : ((⟨t, htP2⟩ * ⟨l, hlp2⟩ * (⟨l, hlp2⟩ * ⟨t, htP2⟩)⁻¹ :
        ↥(L2 ⊔ bigB L1 L2 S)) : ↥(L2 ⊔ bigB L1 L2 S) ⧸ E) = 1 :=
      (QuotientGroup.eq_one_iff _).mpr hmemE
    rw [QuotientGroup.mk_mul E, QuotientGroup.mk_mul E, QuotientGroup.mk_inv E,
      QuotientGroup.mk_mul E] at h2
    rwa [mul_inv_eq_one] at h2
  have hcen : ((⟨l, hlp2⟩ : ↥(L2 ⊔ bigB L1 L2 S)) : ↥(L2 ⊔ bigB L1 L2 S) ⧸ E) ∈
      Subgroup.centralizer ({(((⟨t, htP2⟩ : ↥(L2 ⊔ bigB L1 L2 S)) :
        ↥(L2 ⊔ bigB L1 L2 S) ⧸ E))} : Set (↥(L2 ⊔ bigB L1 L2 S) ⧸ E)) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    rw [hy]
    exact hcomm
  obtain ⟨g, hgcent, hgg⟩ :=
    CFSG.GH74.GLS.Stage2.Bender.Thm2.T3.exists_lift_of_mem_centralizer_quotient
      E hℓ hEcard htord hcen
  have hn : (⟨l, hlp2⟩ : ↥(L2 ⊔ bigB L1 L2 S))⁻¹ * g ∈ E := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul E, QuotientGroup.mk_inv E, hgg,
      inv_mul_cancel]
  have hgL : (g : G) ∈ L2 := by
    have h1 : (g : ↥(L2 ⊔ bigB L1 L2 S)) = ⟨l, hlp2⟩ * (⟨l, hlp2⟩⁻¹ * g) := by group
    rw [congrArg Subtype.val h1]
    simp only [Subgroup.coe_mul]
    exact L2.mul_mem hl
      ((CFSG.LieType.BorelTits.pCoreOf_le 2 L2) (Subgroup.mem_subgroupOf.mp hn))
  have hgC : (g : G) ∈ Subgroup.centralizer ({t} : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    rw [hy]
    have h1 : (⟨t, htP2⟩ : ↥(L2 ⊔ bigB L1 L2 S)) * g = g * ⟨t, htP2⟩ :=
      Subgroup.mem_centralizer_iff.mp hgcent ⟨t, htP2⟩ (Set.mem_singleton _)
    calc t * (g : G) =
          (((⟨t, htP2⟩ : ↥(L2 ⊔ bigB L1 L2 S)) * g : ↥(L2 ⊔ bigB L1 L2 S)) : G) := by
          simp only [Subgroup.coe_mul]
      _ = ((g * ⟨t, htP2⟩ : ↥(L2 ⊔ bigB L1 L2 S)) : G) := by rw [h1]
      _ = (g : G) * t := by simp only [Subgroup.coe_mul]
  have hgl : (g : G) = l * ((⟨l, hlp2⟩⁻¹ * g : ↥(L2 ⊔ bigB L1 L2 S)) : G) := by
    have h1 : (g : ↥(L2 ⊔ bigB L1 L2 S)) = ⟨l, hlp2⟩ * (⟨l, hlp2⟩⁻¹ * g) := by group
    calc (g : G) = ((⟨l, hlp2⟩ * (⟨l, hlp2⟩⁻¹ * g) : ↥(L2 ⊔ bigB L1 L2 S)) : G) := by
          rw [← h1]
      _ = l * ((⟨l, hlp2⟩⁻¹ * g : ↥(L2 ⊔ bigB L1 L2 S)) : G) := by
          simp only [Subgroup.coe_mul]
  refine ⟨(g : G), ⟨hgC, hgL⟩, ((⟨l, hlp2⟩⁻¹ * g : ↥(L2 ⊔ bigB L1 L2 S)) : G)⁻¹ * b,
    ?_, ?_⟩
  · exact (bigB L1 L2 S).mul_mem
      (Subgroup.inv_mem _ (f112_pCoreOf_le_bigB_right hF (Subgroup.mem_subgroupOf.mp hn))) hb
  · rw [hgl]; group

private theorem cosetAct_γ₀_eq_iff {X : Type} [Group X] {A B : Subgroup X} (x : ↥(A ⊔ B)) :
    cosetAct x (CosetGeom.γ₀ (A ⊔ B) A B) = CosetGeom.γ₀ (A ⊔ B) A B ↔ (x : X) ∈ A := by
  constructor
  · intro h
    have := CosetGeom.mem_stab_of_smul_eq (γ := CosetGeom.γ₀ (A ⊔ B) A B) h
    rwa [CosetGeom.stab_γ₀ (le_sup_left : A ≤ A ⊔ B)] at this
  · intro h
    exact CosetGeom.smul_eq_of_mem_stab (γ := CosetGeom.γ₀ (A ⊔ B) A B) (by
      rw [CosetGeom.stab_γ₀ (le_sup_left : A ≤ A ⊔ B)]; exact h)

private theorem f112Rangeφ₁ (L1 L2 S : Subgroup G) :
    (f112Completion L1 L2 S).φ1.range =
      (L1 ⊔ bigB L1 L2 S).subgroupOf ((L1 ⊔ bigB L1 L2 S) ⊔ (L2 ⊔ bigB L1 L2 S)) :=
  Subgroup.inclusion_range (le_sup_left : (L1 ⊔ bigB L1 L2 S) ≤
    (L1 ⊔ bigB L1 L2 S) ⊔ (L2 ⊔ bigB L1 L2 S))

private theorem f112_mem_range_φ₁_iff (L1 L2 S : Subgroup G)
    (y : ↥((L1 ⊔ bigB L1 L2 S) ⊔ (L2 ⊔ bigB L1 L2 S))) :
    y ∈ (f112Completion L1 L2 S).φ1.range ↔ (y : G) ∈ L1 ⊔ bigB L1 L2 S := by
  rw [f112Rangeφ₁]
  exact Subgroup.mem_subgroupOf

private theorem f112_mem_range_φ₁_iff' (L1 L2 S : Subgroup G)
    (x : ↥((f112Completion L1 L2 S).φ1.range ⊔ (f112Completion L1 L2 S).φ2.range)) :
    x.1 ∈ (f112Completion L1 L2 S).φ1.range ↔ (x : G) ∈ L1 ⊔ bigB L1 L2 S :=
  f112_mem_range_φ₁_iff L1 L2 S x.1

private def f112Incl1 (L1 L2 S : Subgroup G) :
    ↥(L2 ⊔ bigB L1 L2 S) →*
      ↥((f112Completion L1 L2 S).φ1.range ⊔ (f112Completion L1 L2 S).φ2.range) :=
  (((f112Completion L1 L2 S).theta0 (f112Completion_isFaithful L1 L2 S)).comp
    (MulAction.stabilizer (f112Acting L1 L2 S) (f112Gamma1 L1 L2 S)).subtype).comp
    (f112StabEquiv1 L1 L2 S).symm.toMonoidHom

private theorem coe_f112Incl1 (L1 L2 S : Subgroup G) (p : ↥(L2 ⊔ bigB L1 L2 S)) :
    ((f112Incl1 L1 L2 S p : ↥((f112Completion L1 L2 S).φ1.range ⊔
      (f112Completion L1 L2 S).φ2.range)) : G) = (p : G) := by
  rw [f112Incl1, MonoidHom.comp_apply, MonoidHom.comp_apply, Subgroup.subtype_apply,
    ← coe_f112StabEquiv1]
  change ((f112StabEquiv1 L1 L2 S ((f112StabEquiv1 L1 L2 S).symm p) :
    ↥(L2 ⊔ bigB L1 L2 S)) : G) = (p : G)
  rw [MulEquiv.apply_symm_apply]

private def f112VOf1 (L1 L2 S : Subgroup G) (p : ↥(L2 ⊔ bigB L1 L2 S)) :
    f112Gamma L1 L2 S :=
  ((f112StabEquiv1 L1 L2 S).symm p : f112Acting L1 L2 S) • f112Gamma0 L1 L2 S

private theorem f112_adj_vOf1 (L1 L2 S : Subgroup G) (p : ↥(L2 ⊔ bigB L1 L2 S)) :
    (f112Amalgam L1 L2 S).graphHat.Adj (f112Gamma1 L1 L2 S) (f112VOf1 L1 L2 S p) := by
  set k : f112Acting L1 L2 S := ((f112StabEquiv1 L1 L2 S).symm p : f112Acting L1 L2 S) with hk
  have hfix : k • f112Gamma1 L1 L2 S = f112Gamma1 L1 L2 S :=
    MulAction.mem_stabilizer_iff.mp ((f112StabEquiv1 L1 L2 S).symm p).2
  have hadj := (CosetGeom.smul_adj k).mpr
    (CosetGeom.adj_γ₀_γ₁ (G₀ := (f112Amalgam L1 L2 S).Ghat1 ⊔ (f112Amalgam L1 L2 S).Ghat2)
      (G₁ := (f112Amalgam L1 L2 S).Ghat1) (G₂ := (f112Amalgam L1 L2 S).Ghat2)).symm
  rw [hfix] at hadj
  exact hadj

private theorem f112_Θ_vOf1 (L1 L2 S : Subgroup G) (p : ↥(L2 ⊔ bigB L1 L2 S)) :
    (f112Completion L1 L2 S).Θ (f112Completion_isFaithful L1 L2 S) (f112VOf1 L1 L2 S p) =
      cosetAct (f112Incl1 L1 L2 S p)
        (CosetGeom.γ₀ ((f112Completion L1 L2 S).φ1.range ⊔ (f112Completion L1 L2 S).φ2.range)
          (f112Completion L1 L2 S).φ1.range (f112Completion L1 L2 S).φ2.range) := by
  rw [f112VOf1, RankTwoAmalgam.Completion.Θ_smul, f112Θγ₀]
  rfl

private theorem f112_vOf_eq_iff1 {L1 L2 S : Subgroup G}
    (hF : F112HypW L1 L2 S) {p q : ↥(L2 ⊔ bigB L1 L2 S)} :
    f112VOf1 L1 L2 S p = f112VOf1 L1 L2 S q ↔ (q : G)⁻¹ * (p : G) ∈ bigB L1 L2 S := by
  have hc : (f112Completion L1 L2 S).IsFaithful := f112Completion_isFaithful L1 L2 S
  have hcoe : ∀ a b : ↥(L2 ⊔ bigB L1 L2 S),
      ((((f112Incl1 L1 L2 S a)⁻¹ * f112Incl1 L1 L2 S b :
        ↥((f112Completion L1 L2 S).φ1.range ⊔
          (f112Completion L1 L2 S).φ2.range)) : G)) = (a : G)⁻¹ * (b : G) := by
    intro a b
    simp only [Subgroup.coe_inv, Subgroup.coe_mul, coe_f112Incl1]
  constructor
  · intro h
    have hΘ : (f112Completion L1 L2 S).Θ hc (f112VOf1 L1 L2 S p) =
        (f112Completion L1 L2 S).Θ hc (f112VOf1 L1 L2 S q) := by rw [h]
    rw [f112_Θ_vOf1, f112_Θ_vOf1] at hΘ
    have hfix : cosetAct ((f112Incl1 L1 L2 S q)⁻¹ * f112Incl1 L1 L2 S p)
        (CosetGeom.γ₀ ((f112Completion L1 L2 S).φ1.range ⊔
          (f112Completion L1 L2 S).φ2.range)
          (f112Completion L1 L2 S).φ1.range (f112Completion L1 L2 S).φ2.range) =
        CosetGeom.γ₀ ((f112Completion L1 L2 S).φ1.range ⊔
          (f112Completion L1 L2 S).φ2.range)
          (f112Completion L1 L2 S).φ1.range (f112Completion L1 L2 S).φ2.range :=
      (cosetAct_eq_iff (f112Incl1 L1 L2 S p) (f112Incl1 L1 L2 S q) _).mp hΘ
    have hmem := (cosetAct_γ₀_eq_iff ((f112Incl1 L1 L2 S q)⁻¹ * f112Incl1 L1 L2 S p)).mp hfix
    have hmem1 : (q : G)⁻¹ * (p : G) ∈ L1 ⊔ bigB L1 L2 S := by
      have h1 := (f112_mem_range_φ₁_iff' L1 L2 S
        ((f112Incl1 L1 L2 S q)⁻¹ * f112Incl1 L1 L2 S p)).mp hmem
      rwa [hcoe q p] at h1
    have hmem2 : (q : G)⁻¹ * (p : G) ∈ L2 ⊔ bigB L1 L2 S :=
      Subgroup.mul_mem _ (Subgroup.inv_mem _ q.2) p.2
    have hinf : (q : G)⁻¹ * (p : G) ∈
        (L1 ⊔ bigB L1 L2 S) ⊓ (L2 ⊔ bigB L1 L2 S) := Subgroup.mem_inf.mpr ⟨hmem1, hmem2⟩
    rwa [f112_parabolic_inf_eq_bigB hF] at hinf
  · intro h
    have hmem : (q : G)⁻¹ * (p : G) ∈ L1 ⊔ bigB L1 L2 S :=
      (le_sup_right : bigB L1 L2 S ≤ L1 ⊔ bigB L1 L2 S) h
    have hfix : cosetAct ((f112Incl1 L1 L2 S q)⁻¹ * f112Incl1 L1 L2 S p)
        (CosetGeom.γ₀ ((f112Completion L1 L2 S).φ1.range ⊔
          (f112Completion L1 L2 S).φ2.range)
          (f112Completion L1 L2 S).φ1.range (f112Completion L1 L2 S).φ2.range) =
        CosetGeom.γ₀ ((f112Completion L1 L2 S).φ1.range ⊔
          (f112Completion L1 L2 S).φ2.range)
          (f112Completion L1 L2 S).φ1.range (f112Completion L1 L2 S).φ2.range := by
      refine (cosetAct_γ₀_eq_iff _).mpr ?_
      rw [f112_mem_range_φ₁_iff' L1 L2 S, hcoe]
      exact hmem
    have hΘ : (f112Completion L1 L2 S).Θ hc (f112VOf1 L1 L2 S p) =
        (f112Completion L1 L2 S).Θ hc (f112VOf1 L1 L2 S q) := by
      rw [f112_Θ_vOf1, f112_Θ_vOf1]
      exact (cosetAct_eq_iff (f112Incl1 L1 L2 S p) (f112Incl1 L1 L2 S q) _).mpr hfix
    exact (f112Completion L1 L2 S).graphCovering hc |>.loc_inj (f112Gamma1 L1 L2 S)
      (f112VOf1 L1 L2 S p) (f112VOf1 L1 L2 S q) (f112_adj_vOf1 L1 L2 S p)
      (f112_adj_vOf1 L1 L2 S q) hΘ

private theorem f112_exists_vOf1 {L1 L2 S : Subgroup G}
    (hF : F112HypW L1 L2 S) {w : f112Gamma L1 L2 S}
    (hw : w ∈ (f112Amalgam L1 L2 S).graphHat.neighborSet (f112Gamma1 L1 L2 S)) :
    ∃ p : ↥(L2 ⊔ bigB L1 L2 S), f112VOf1 L1 L2 S p = w := by
  have hγ₀ : (f112Gamma0 L1 L2 S) ∈
      (f112Amalgam L1 L2 S).graphHat.neighborSet (f112Gamma1 L1 L2 S) :=
    (CosetGeom.adj_γ₀_γ₁ (G₀ := (f112Amalgam L1 L2 S).Ghat1 ⊔ (f112Amalgam L1 L2 S).Ghat2)
      (G₁ := (f112Amalgam L1 L2 S).Ghat1) (G₂ := (f112Amalgam L1 L2 S).Ghat2)).symm
  obtain ⟨g, hg, hgw⟩ := f112_stabilizer_transitive_on_nbrs hF hγ₀ hw
  exact ⟨f112StabEquiv1 L1 L2 S ⟨g, hg⟩, by rw [f112VOf1, MulEquiv.symm_apply_apply]; exact hgw⟩

private theorem f112_smul_vOf1 (L1 L2 S : Subgroup G) (h : f112Acting L1 L2 S)
    (hh : h ∈ MulAction.stabilizer (f112Acting L1 L2 S) (f112Gamma1 L1 L2 S))
    (p : ↥(L2 ⊔ bigB L1 L2 S)) :
    h • f112VOf1 L1 L2 S p =
      f112VOf1 L1 L2 S (f112StabEquiv1 L1 L2 S ⟨h, hh⟩ * p) := by
  have hmem : h * ((f112StabEquiv1 L1 L2 S).symm p : f112Acting L1 L2 S) ∈
      MulAction.stabilizer (f112Acting L1 L2 S) (f112Gamma1 L1 L2 S) :=
    (MulAction.stabilizer (f112Acting L1 L2 S) (f112Gamma1 L1 L2 S)).mul_mem hh
      ((f112StabEquiv1 L1 L2 S).symm p).2
  have hx : f112StabEquiv1 L1 L2 S
      (⟨h * ((f112StabEquiv1 L1 L2 S).symm p : f112Acting L1 L2 S), hmem⟩ :
        ↥(MulAction.stabilizer (f112Acting L1 L2 S) (f112Gamma1 L1 L2 S))) =
      f112StabEquiv1 L1 L2 S ⟨h, hh⟩ * p := by
    have h1 : (⟨h * ((f112StabEquiv1 L1 L2 S).symm p : f112Acting L1 L2 S), hmem⟩ :
        ↥(MulAction.stabilizer (f112Acting L1 L2 S) (f112Gamma1 L1 L2 S))) =
        ⟨h, hh⟩ * (f112StabEquiv1 L1 L2 S).symm p := Subtype.ext rfl
    rw [h1, map_mul, MulEquiv.apply_symm_apply]
  have hmul : h * ((f112StabEquiv1 L1 L2 S).symm p : f112Acting L1 L2 S) =
      ((f112StabEquiv1 L1 L2 S).symm (f112StabEquiv1 L1 L2 S ⟨h, hh⟩ * p) :
        f112Acting L1 L2 S) := by
    have heq : (⟨h * ((f112StabEquiv1 L1 L2 S).symm p : f112Acting L1 L2 S), hmem⟩ :
        ↥(MulAction.stabilizer (f112Acting L1 L2 S) (f112Gamma1 L1 L2 S))) =
        (f112StabEquiv1 L1 L2 S).symm (f112StabEquiv1 L1 L2 S ⟨h, hh⟩ * p) :=
      (f112StabEquiv1 L1 L2 S).injective (by rw [hx, MulEquiv.apply_symm_apply])
    exact congrArg Subtype.val heq
  rw [f112VOf1, ← mul_smul, hmul, f112VOf1]

private theorem f112_smul_vOf1' (L1 L2 S : Subgroup G)
    (k : ↥(MulAction.stabilizer (f112Acting L1 L2 S) (f112Gamma1 L1 L2 S)))
    (p : ↥(L2 ⊔ bigB L1 L2 S)) :
    (k : f112Acting L1 L2 S) • f112VOf1 L1 L2 S p =
      f112VOf1 L1 L2 S (f112StabEquiv1 L1 L2 S k * p) :=
  f112_smul_vOf1 L1 L2 S (k : f112Acting L1 L2 S) k.2 p

theorem f112_fixes_nbrs_iff_mem_K2 {L1 L2 S : Subgroup G}
    (hF : F112HypW L1 L2 S) (h : f112Acting L1 L2 S)
    (hh : h ∈ MulAction.stabilizer (f112Acting L1 L2 S) (f112Gamma1 L1 L2 S)) :
    (∀ w, (f112Amalgam L1 L2 S).graphHat.Adj (f112Gamma1 L1 L2 S) w → h • w = w) ↔
      f112StabEquiv1 L1 L2 S ⟨h, hh⟩ ∈ f112K2 L1 L2 S := by
  have hK2 : f112K2 L1 L2 S =
      ((bigB L1 L2 S).subgroupOf (L2 ⊔ bigB L1 L2 S)).normalCore := by
    show (((L2 ⊔ bigB L1 L2 S) ⊓ (L1 ⊔ bigB L1 L2 S)).subgroupOf
      (L2 ⊔ bigB L1 L2 S)).normalCore = _
    rw [show (L2 ⊔ bigB L1 L2 S) ⊓ (L1 ⊔ bigB L1 L2 S) = bigB L1 L2 S from by
      rw [inf_comm]; exact f112_parabolic_inf_eq_bigB hF]
  set x : ↥(L2 ⊔ bigB L1 L2 S) := f112StabEquiv1 L1 L2 S ⟨h, hh⟩
  constructor
  · intro hfix
    rw [hK2, mem_normalCore_iff]
    intro g
    have hv : f112VOf1 L1 L2 S (x * g) = f112VOf1 L1 L2 S g := by
      rw [← f112_smul_vOf1 L1 L2 S h hh g]
      exact hfix _ (f112_adj_vOf1 L1 L2 S g)
    have h2 := (f112_vOf_eq_iff1 hF).mp hv
    have h3 : (g : G)⁻¹ * (x : G) * (g : G) ∈ bigB L1 L2 S := by
      simpa [Subgroup.coe_mul, Subgroup.coe_inv, mul_assoc] using h2
    exact Subgroup.mem_subgroupOf.mpr h3
  · intro hx w hw
    obtain ⟨p, rfl⟩ := f112_exists_vOf1 hF hw
    rw [f112_smul_vOf1 L1 L2 S h hh p]
    refine (f112_vOf_eq_iff1 hF).mpr ?_
    have hmem := mem_normalCore_iff.mp (hK2 ▸ hx) p
    have hmem' : ((p⁻¹ : ↥(L2 ⊔ bigB L1 L2 S)) : G) * (x : G) * (p : G) ∈ bigB L1 L2 S :=
      Subgroup.mem_subgroupOf.mp hmem
    simpa [Subgroup.coe_mul, Subgroup.coe_inv, mul_assoc] using hmem'

theorem f112_smul_γ₀_eq_iff {L1 L2 S : Subgroup G}
    (hF : F112HypW L1 L2 S) (h : f112Acting L1 L2 S)
    (hh : h ∈ MulAction.stabilizer (f112Acting L1 L2 S) (f112Gamma1 L1 L2 S)) :
    h • f112Gamma0 L1 L2 S = f112Gamma0 L1 L2 S ↔
      (f112StabEquiv1 L1 L2 S ⟨h, hh⟩ : G) ∈ bigB L1 L2 S := by
  have hc : (f112Completion L1 L2 S).IsFaithful := f112Completion_isFaithful L1 L2 S
  have hP2 : (f112StabEquiv1 L1 L2 S ⟨h, hh⟩ : G) ∈ L2 ⊔ bigB L1 L2 S :=
    (f112StabEquiv1 L1 L2 S ⟨h, hh⟩).2
  constructor
  · intro hfix
    have hΘ : (f112Completion L1 L2 S).Θ hc (h • f112Gamma0 L1 L2 S) =
        (f112Completion L1 L2 S).Θ hc (f112Gamma0 L1 L2 S) := by rw [hfix]
    rw [RankTwoAmalgam.Completion.Θ_smul, f112Θγ₀] at hΘ
    have hstab : ((f112Completion L1 L2 S).theta0 hc h).1 ∈
        (f112Completion L1 L2 S).φ1.range := by
      have h1 := CosetGeom.mem_stab_of_smul_eq
        (γ := CosetGeom.γ₀ ((f112Completion L1 L2 S).φ1.range ⊔
          (f112Completion L1 L2 S).φ2.range) (f112Completion L1 L2 S).φ1.range
          (f112Completion L1 L2 S).φ2.range) hΘ
      rwa [CosetGeom.stab_γ₀ (le_sup_left : (f112Completion L1 L2 S).φ1.range ≤
        (f112Completion L1 L2 S).φ1.range ⊔ (f112Completion L1 L2 S).φ2.range)] at h1
    have hP1 : (f112StabEquiv1 L1 L2 S ⟨h, hh⟩ : G) ∈ L1 ⊔ bigB L1 L2 S := by
      rw [coe_f112StabEquiv1 L1 L2 S ⟨h, hh⟩]
      exact (f112_mem_range_φ₁_iff' L1 L2 S ((f112Completion L1 L2 S).theta0 hc h)).mp hstab
    have hinf := Subgroup.mem_inf.mpr ⟨hP1, hP2⟩
    have h4 : (L1 ⊔ bigB L1 L2 S) ⊓ (L2 ⊔ bigB L1 L2 S) = bigB L1 L2 S :=
      f112_parabolic_inf_eq_bigB hF
    rw [h4] at hinf
    exact hinf
  · intro hB
    have hP1 : (f112StabEquiv1 L1 L2 S ⟨h, hh⟩ : G) ∈ L1 ⊔ bigB L1 L2 S :=
      (le_sup_right : bigB L1 L2 S ≤ L1 ⊔ bigB L1 L2 S) hB
    have hstab : ((f112Completion L1 L2 S).theta0 hc h : G) ∈ L1 ⊔ bigB L1 L2 S := by
      rw [← coe_f112StabEquiv1 L1 L2 S ⟨h, hh⟩]
      exact hP1
    have hmem : ((f112Completion L1 L2 S).theta0 hc h).1 ∈
        (f112Completion L1 L2 S).φ1.range :=
      (f112_mem_range_φ₁_iff' L1 L2 S ((f112Completion L1 L2 S).theta0 hc h)).mpr hstab
    have hfix : cosetAct ((f112Completion L1 L2 S).theta0 hc h)
        (CosetGeom.γ₀ ((f112Completion L1 L2 S).φ1.range ⊔
          (f112Completion L1 L2 S).φ2.range) (f112Completion L1 L2 S).φ1.range
          (f112Completion L1 L2 S).φ2.range) =
        CosetGeom.γ₀ ((f112Completion L1 L2 S).φ1.range ⊔
          (f112Completion L1 L2 S).φ2.range) (f112Completion L1 L2 S).φ1.range
          (f112Completion L1 L2 S).φ2.range :=
      (cosetAct_γ₀_eq_iff _).mpr hmem
    have hΘ : (f112Completion L1 L2 S).Θ hc (h • f112Gamma0 L1 L2 S) =
        (f112Completion L1 L2 S).Θ hc (f112Gamma0 L1 L2 S) := by
      rw [RankTwoAmalgam.Completion.Θ_smul, f112Θγ₀]
      exact hfix
    have hfix1 : h • f112Gamma1 L1 L2 S = f112Gamma1 L1 L2 S :=
      MulAction.mem_stabilizer_iff.mp hh
    have hadj : (f112Amalgam L1 L2 S).graphHat.Adj (f112Gamma1 L1 L2 S)
        (h • f112Gamma0 L1 L2 S) := by
      have h := (CosetGeom.smul_adj h).mpr
        (CosetGeom.adj_γ₀_γ₁ (G₀ := (f112Amalgam L1 L2 S).Ghat1 ⊔ (f112Amalgam L1 L2 S).Ghat2)
          (G₁ := (f112Amalgam L1 L2 S).Ghat1) (G₂ := (f112Amalgam L1 L2 S).Ghat2)).symm
      rwa [hfix1] at h
    exact (f112Completion L1 L2 S).graphCovering hc |>.loc_inj (f112Gamma1 L1 L2 S)
      (h • f112Gamma0 L1 L2 S) (f112Gamma0 L1 L2 S) hadj
      (CosetGeom.adj_γ₀_γ₁ (G₀ := (f112Amalgam L1 L2 S).Ghat1 ⊔ (f112Amalgam L1 L2 S).Ghat2)
        (G₁ := (f112Amalgam L1 L2 S).Ghat1) (G₂ := (f112Amalgam L1 L2 S).Ghat2)).symm hΘ

theorem f112_exists_smul_nbr_of_fac1 {L1 L2 S : Subgroup G}
    (hF : F112HypW L1 L2 S) {C : Subgroup G} (hCP : C ≤ L2 ⊔ bigB L1 L2 S)
    (hfac : ∀ p ∈ L2 ⊔ bigB L1 L2 S, ∃ c ∈ C, ∃ b ∈ bigB L1 L2 S, p = c * b)
    {w₁ w₂ : f112Gamma L1 L2 S}
    (hw₁ : (f112Amalgam L1 L2 S).graphHat.Adj (f112Gamma1 L1 L2 S) w₁)
    (hw₂ : (f112Amalgam L1 L2 S).graphHat.Adj (f112Gamma1 L1 L2 S) w₂) :
    ∃ k : ↥(MulAction.stabilizer (f112Acting L1 L2 S) (f112Gamma1 L1 L2 S)),
      (f112StabEquiv1 L1 L2 S k : G) ∈ C ∧ (k : f112Acting L1 L2 S) • w₁ = w₂ := by
  obtain ⟨p₁, rfl⟩ := f112_exists_vOf1 hF hw₁
  obtain ⟨p₂, rfl⟩ := f112_exists_vOf1 hF hw₂
  obtain ⟨c₁, hc₁C, b₁, hb₁, hp₁⟩ := hfac p₁ p₁.2
  obtain ⟨c₂, hc₂C, b₂, hb₂, hp₂⟩ := hfac p₂ p₂.2
  have hc₁P : c₁ ∈ L2 ⊔ bigB L1 L2 S := hCP hc₁C
  have hc₂P : c₂ ∈ L2 ⊔ bigB L1 L2 S := hCP hc₂C
  have hvc : ∀ (c : G) (hc : c ∈ L2 ⊔ bigB L1 L2 S) (b : G) (hb : b ∈ bigB L1 L2 S)
      (p : ↥(L2 ⊔ bigB L1 L2 S)), (p : G) = c * b →
      f112VOf1 L1 L2 S p = f112VOf1 L1 L2 S ⟨c, hc⟩ := by
    intro c hc b hb p hp
    refine (f112_vOf_eq_iff1 hF).mpr ?_
    have h1 : ((⟨c, hc⟩ : ↥(L2 ⊔ bigB L1 L2 S)) : G)⁻¹ * (p : G) = b := by
      rw [hp]; group
    rw [h1]
    exact hb
  have hv₁ : f112VOf1 L1 L2 S p₁ = f112VOf1 L1 L2 S ⟨c₁, hc₁P⟩ := hvc c₁ hc₁P b₁ hb₁ p₁ hp₁
  have hv₂ : f112VOf1 L1 L2 S p₂ = f112VOf1 L1 L2 S ⟨c₂, hc₂P⟩ := hvc c₂ hc₂P b₂ hb₂ p₂ hp₂
  refine ⟨(f112StabEquiv1 L1 L2 S).symm
    ((⟨c₂, hc₂P⟩ : ↥(L2 ⊔ bigB L1 L2 S)) * (⟨c₁, hc₁P⟩ : ↥(L2 ⊔ bigB L1 L2 S))⁻¹), ?_, ?_⟩
  · rw [MulEquiv.apply_symm_apply]
    exact C.mul_mem hc₂C (C.inv_mem hc₁C)
  · rw [hv₁, f112_smul_vOf1', MulEquiv.apply_symm_apply]
    have h3 : ((⟨c₂, hc₂P⟩ : ↥(L2 ⊔ bigB L1 L2 S)) *
        (⟨c₁, hc₁P⟩ : ↥(L2 ⊔ bigB L1 L2 S))⁻¹) *
        (⟨c₁, hc₁P⟩ : ↥(L2 ⊔ bigB L1 L2 S)) = ⟨c₂, hc₂P⟩ := by group
    rw [h3, hv₂]

private theorem f112_base_edge_prime {L1 L2 S : Subgroup G}
    (hF : F112HypW L1 L2 S) {ℓ : ℕ} (hℓ : ℓ.Prime) (hodd : Odd ℓ)
    (hK1 : ∀ t ∈ (f112K1 L1 L2 S).map (L1 ⊔ bigB L1 L2 S).subtype, ∀ l ∈ L1,
      l * t * l⁻¹ * t⁻¹ ∈ pCoreOf 2 L1)
    (hK2 : ∀ t ∈ (f112K2 L1 L2 S).map (L2 ⊔ bigB L1 L2 S).subtype, ∀ l ∈ L2,
      l * t * l⁻¹ * t⁻¹ ∈ pCoreOf 2 L2)
    {u : f112Acting L1 L2 S}
    (hu : u ∈ edgeKernel (H := f112Acting L1 L2 S) (f112Amalgam L1 L2 S).graphHat
      (f112Gamma0 L1 L2 S) (f112Gamma1 L1 L2 S))
    (huord : orderOf u = ℓ) : u = 1 := by
  have hu' := mem_edgeKernel.mp hu
  have hfix0 : u • f112Gamma0 L1 L2 S = f112Gamma0 L1 L2 S :=
    hu'.2 _ (CosetGeom.adj_γ₀_γ₁ (G₀ := (f112Amalgam L1 L2 S).Ghat1 ⊔ (f112Amalgam L1 L2 S).Ghat2)
      (G₁ := (f112Amalgam L1 L2 S).Ghat1) (G₂ := (f112Amalgam L1 L2 S).Ghat2)).symm
  have hfix1 : u • f112Gamma1 L1 L2 S = f112Gamma1 L1 L2 S :=
    hu'.1 _ (CosetGeom.adj_γ₀_γ₁ (G₀ := (f112Amalgam L1 L2 S).Ghat1 ⊔ (f112Amalgam L1 L2 S).Ghat2)
      (G₁ := (f112Amalgam L1 L2 S).Ghat1) (G₂ := (f112Amalgam L1 L2 S).Ghat2))
  have hstab0 : u ∈ MulAction.stabilizer (f112Acting L1 L2 S) (f112Gamma0 L1 L2 S) :=
    MulAction.mem_stabilizer_iff.mpr hfix0
  have hstab1 : u ∈ MulAction.stabilizer (f112Acting L1 L2 S) (f112Gamma1 L1 L2 S) :=
    MulAction.mem_stabilizer_iff.mpr hfix1
  set t0 : ↥(L1 ⊔ bigB L1 L2 S) := f112StabEquiv0 L1 L2 S ⟨u, hstab0⟩ with ht0def
  set t1 : ↥(L2 ⊔ bigB L1 L2 S) := f112StabEquiv1 L1 L2 S ⟨u, hstab1⟩ with ht1def
  have ht0K : t0 ∈ f112K1 L1 L2 S :=
    (f112_fixes_nbrs_iff_mem_K1 hF u hstab0).mp hu'.1
  have ht1K : t1 ∈ f112K2 L1 L2 S :=
    (f112_fixes_nbrs_iff_mem_K2 hF u hstab1).mp hu'.2
  have ht0ord : orderOf (⟨(t0 : G), t0.2⟩ : ↥(L1 ⊔ bigB L1 L2 S)) = ℓ := by
    have h1 : orderOf t0 = ℓ := by
      rw [ht0def, MulEquiv.orderOf_eq, ← Subgroup.orderOf_coe ⟨u, hstab0⟩]
      exact huord
    exact h1
  have ht1ord : orderOf (⟨(t1 : G), t1.2⟩ : ↥(L2 ⊔ bigB L1 L2 S)) = ℓ := by
    have h1 : orderOf t1 = ℓ := by
      rw [ht1def, MulEquiv.orderOf_eq, ← Subgroup.orderOf_coe ⟨u, hstab1⟩]
      exact huord
    exact h1
  let C0 : Subgroup G := Subgroup.centralizer ({(t0 : G)} : Set G) ⊓ L1
  let C1 : Subgroup G := Subgroup.centralizer ({(t1 : G)} : Set G) ⊓ L2
  have hC0P : C0 ≤ L1 ⊔ bigB L1 L2 S := fun x hx =>
    (le_sup_left : L1 ≤ L1 ⊔ bigB L1 L2 S) hx.2
  have hC1P : C1 ≤ L2 ⊔ bigB L1 L2 S := fun x hx =>
    (le_sup_left : L2 ≤ L2 ⊔ bigB L1 L2 S) hx.2
  let Cx : Subgroup (f112Acting L1 L2 S) :=
    ((C0.subgroupOf (L1 ⊔ bigB L1 L2 S)).comap (f112StabEquiv0 L1 L2 S).toMonoidHom).map
      (Subgroup.subtype _)
  let Cy : Subgroup (f112Acting L1 L2 S) :=
    ((C1.subgroupOf (L2 ⊔ bigB L1 L2 S)).comap (f112StabEquiv1 L1 L2 S).toMonoidHom).map
      (Subgroup.subtype _)
  have hfac0 := f112_fac_left hF hℓ hodd t0.2 ht0ord ht0K hK1
  have hfac1 := f112_fac_right hF hℓ hodd t1.2 ht1ord ht1K hK2
  have hCxu : ∀ c ∈ Cx, c * u = u * c := by
    intro c hc
    obtain ⟨k, hk, rfl⟩ := Subgroup.mem_map.mp hc
    have hkC : (f112StabEquiv0 L1 L2 S k : G) ∈ C0 :=
      Subgroup.mem_subgroupOf.mp (Subgroup.mem_comap.mp hk)
    have hcent : (t0 : G) * (f112StabEquiv0 L1 L2 S k : G) =
        (f112StabEquiv0 L1 L2 S k : G) * (t0 : G) :=
      Subgroup.mem_centralizer_iff.mp hkC.1 (t0 : G) (Set.mem_singleton _)
    have hkeq : (k * ⟨u, hstab0⟩ : ↥(MulAction.stabilizer (f112Acting L1 L2 S)
        (f112Gamma0 L1 L2 S))) = ⟨u, hstab0⟩ * k := by
      apply (f112StabEquiv0 L1 L2 S).injective
      rw [map_mul, map_mul]
      exact Subtype.ext hcent.symm
    have hcoe := congrArg Subtype.val hkeq
    simpa [Subgroup.coe_mul] using hcoe
  have hCyu : ∀ c ∈ Cy, c * u = u * c := by
    intro c hc
    obtain ⟨k, hk, rfl⟩ := Subgroup.mem_map.mp hc
    have hkC : (f112StabEquiv1 L1 L2 S k : G) ∈ C1 :=
      Subgroup.mem_subgroupOf.mp (Subgroup.mem_comap.mp hk)
    have hcent : (t1 : G) * (f112StabEquiv1 L1 L2 S k : G) =
        (f112StabEquiv1 L1 L2 S k : G) * (t1 : G) :=
      Subgroup.mem_centralizer_iff.mp hkC.1 (t1 : G) (Set.mem_singleton _)
    have hkeq : (k * ⟨u, hstab1⟩ : ↥(MulAction.stabilizer (f112Acting L1 L2 S)
        (f112Gamma1 L1 L2 S))) = ⟨u, hstab1⟩ * k := by
      apply (f112StabEquiv1 L1 L2 S).injective
      rw [map_mul, map_mul]
      exact Subtype.ext hcent.symm
    have hcoe := congrArg Subtype.val hkeq
    simpa [Subgroup.coe_mul] using hcoe
  have hCxtrans : ∀ w₁ w₂ : f112Gamma L1 L2 S,
      (f112Amalgam L1 L2 S).graphHat.Adj (f112Gamma0 L1 L2 S) w₁ →
      (f112Amalgam L1 L2 S).graphHat.Adj (f112Gamma0 L1 L2 S) w₂ →
      ∃ c ∈ Cx, c • w₁ = w₂ := by
    intro w₁ w₂ hw₁ hw₂
    obtain ⟨k, hkC, hkw⟩ :=
      f112_exists_smul_nbr_of_fac hF hC0P hfac0 hw₁ hw₂
    refine ⟨(k : f112Acting L1 L2 S), Subgroup.mem_map.mpr ⟨k, ?_, rfl⟩, hkw⟩
    exact Subgroup.mem_comap.mpr (Subgroup.mem_subgroupOf.mpr hkC)
  have hCytrans : ∀ w₁ w₂ : f112Gamma L1 L2 S,
      (f112Amalgam L1 L2 S).graphHat.Adj (f112Gamma1 L1 L2 S) w₁ →
      (f112Amalgam L1 L2 S).graphHat.Adj (f112Gamma1 L1 L2 S) w₂ →
      ∃ c ∈ Cy, c • w₁ = w₂ := by
    intro w₁ w₂ hw₁ hw₂
    obtain ⟨k, hkC, hkw⟩ :=
      f112_exists_smul_nbr_of_fac1 hF hC1P hfac1 hw₁ hw₂
    refine ⟨(k : f112Acting L1 L2 S), Subgroup.mem_map.mpr ⟨k, ?_, rfl⟩, hkw⟩
    exact Subgroup.mem_comap.mpr (Subgroup.mem_subgroupOf.mpr hkC)
  exact eq_one_of_mem_edgeKernel_of_commute (f112_graphHat_connected L1 L2 S)
    (fun h hfix => f112_eq_one_of_forall_smul_eq hF hfix)
    (CosetGeom.adj_γ₀_γ₁ (G₀ := (f112Amalgam L1 L2 S).Ghat1 ⊔ (f112Amalgam L1 L2 S).Ghat2)
      (G₁ := (f112Amalgam L1 L2 S).Ghat1) (G₂ := (f112Amalgam L1 L2 S).Ghat2))
    hu hCxu hCyu hCxtrans hCytrans

private theorem mem_edgeKernel_conj {V : Type*} {H : Type*} [Group H] [MulAction H V]
    {Γ : SimpleGraph V} [GraphAction H Γ] {x y : V} {u : H}
    (hu : u ∈ edgeKernel Γ x y) (k : H) :
    k * u * k⁻¹ ∈ edgeKernel Γ (k • x) (k • y) := by
  rw [mem_edgeKernel] at hu ⊢
  constructor
  · intro w hw
    have h1 : Γ.Adj x (k⁻¹ • w) := by
      have hw' : Γ.Adj (k • x) (k • (k⁻¹ • w)) := by simpa using hw
      exact (GraphAction.adj_smul (Γ := Γ) k x (k⁻¹ • w)).mp hw'
    have h2 : u • (k⁻¹ • w) = k⁻¹ • w := hu.1 _ h1
    calc (k * u * k⁻¹) • w = k • (u • (k⁻¹ • w)) := by rw [mul_smul, mul_smul]
      _ = k • (k⁻¹ • w) := by rw [h2]
      _ = w := by rw [smul_inv_smul]
  · intro w hw
    have h1 : Γ.Adj y (k⁻¹ • w) := by
      have hw' : Γ.Adj (k • y) (k • (k⁻¹ • w)) := by simpa using hw
      exact (GraphAction.adj_smul (Γ := Γ) k y (k⁻¹ • w)).mp hw'
    have h2 : u • (k⁻¹ • w) = k⁻¹ • w := hu.2 _ h1
    calc (k * u * k⁻¹) • w = k • (u • (k⁻¹ • w)) := by rw [mul_smul, mul_smul]
      _ = k • (k⁻¹ • w) := by rw [h2]
      _ = w := by rw [smul_inv_smul]

private theorem edgeKernel_comm {V : Type*} {H : Type*} [Group H] [MulAction H V]
    {Γ : SimpleGraph V} (x y : V) : edgeKernel (H := H) Γ x y = edgeKernel (H := H) Γ y x :=
  inf_comm _ _

private theorem f112_base_edge_finite {L1 L2 S : Subgroup G}
    (hF : F112HypW L1 L2 S) :
    Finite ↥(edgeKernel (H := f112Acting L1 L2 S) (f112Amalgam L1 L2 S).graphHat
      (f112Gamma0 L1 L2 S) (f112Gamma1 L1 L2 S)) := by
  haveI hstab : Finite ↥(MulAction.stabilizer (f112Acting L1 L2 S) (f112Gamma0 L1 L2 S)) :=
    f112_finite_stabilizer hF (f112Gamma0 L1 L2 S)
  refine Finite.of_injective
    (fun x : ↥(edgeKernel (H := f112Acting L1 L2 S) (f112Amalgam L1 L2 S).graphHat
        (f112Gamma0 L1 L2 S) (f112Gamma1 L1 L2 S)) =>
      (⟨(x : f112Acting L1 L2 S), (mem_edgeKernel.mp x.2).2 _
        (CosetGeom.adj_γ₀_γ₁ (G₀ := (f112Amalgam L1 L2 S).Ghat1 ⊔
          (f112Amalgam L1 L2 S).Ghat2) (G₁ := (f112Amalgam L1 L2 S).Ghat1)
          (G₂ := (f112Amalgam L1 L2 S).Ghat2)).symm⟩ :
        ↥(MulAction.stabilizer (f112Acting L1 L2 S) (f112Gamma0 L1 L2 S)))) ?_
  intro a b hab
  exact Subtype.ext (congrArg (fun z : ↥(MulAction.stabilizer (f112Acting L1 L2 S)
    (f112Gamma0 L1 L2 S)) => (z : f112Acting L1 L2 S)) hab)

private theorem f112_base_edge_isPGroup {L1 L2 S : Subgroup G}
    (hF : F112HypW L1 L2 S)
    (hprime : ∀ (ℓ : ℕ), ℓ.Prime → Odd ℓ → ∀ u : f112Acting L1 L2 S,
      u ∈ edgeKernel (H := f112Acting L1 L2 S) (f112Amalgam L1 L2 S).graphHat
        (f112Gamma0 L1 L2 S) (f112Gamma1 L1 L2 S) → orderOf u = ℓ → False) :
    IsPGroup 2 ↥(edgeKernel (H := f112Acting L1 L2 S) (f112Amalgam L1 L2 S).graphHat
      (f112Gamma0 L1 L2 S) (f112Gamma1 L1 L2 S)) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let K : Subgroup (f112Acting L1 L2 S) :=
    edgeKernel (H := f112Acting L1 L2 S) (f112Amalgam L1 L2 S).graphHat
      (f112Gamma0 L1 L2 S) (f112Gamma1 L1 L2 S)
  haveI hKfin : Finite ↥K := f112_base_edge_finite hF
  obtain ⟨P⟩ := Sylow.nonempty (p := 2) (G := ↥K)
  have hidx : (P : Subgroup ↥K).index = 1 := by
    by_contra hne
    have hodd : Odd (P : Subgroup ↥K).index :=
      Nat.not_even_iff_odd.mp (by simpa [even_iff_two_dvd] using P.not_dvd_index)
    have hgt : 1 < (P : Subgroup ↥K).index := by
      have hpos : 0 < (P : Subgroup ↥K).index :=
        Nat.pos_of_ne_zero (Subgroup.index_ne_zero_of_finite)
      omega
    obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd (by omega : (P : Subgroup ↥K).index ≠ 1)
    haveI : Fact (Nat.Prime p) := ⟨hp⟩
    have hpn2 : p ≠ 2 := by
      intro h2
      rw [h2] at hpdvd
      exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr hpdvd)
    have hpodd : Odd p := hp.odd_of_ne_two hpn2
    have hpcard : p ∣ Nat.card ↥K := by
      rw [← Subgroup.card_mul_index (P : Subgroup ↥K)]
      exact dvd_mul_of_dvd_right hpdvd _
    obtain ⟨x, hxord⟩ := exists_prime_orderOf_dvd_card' p hpcard
    have hxord' : orderOf ((x : ↥K) : f112Acting L1 L2 S) = p := by
      rw [Subgroup.orderOf_coe]
      exact hxord
    exact hprime p hp hpodd _ x.2 hxord'
  obtain ⟨n, hn⟩ := P.isPGroup'.exists_card_eq
  have hcard : Nat.card ↥K = 2 ^ n := by
    rw [← Subgroup.card_mul_index (P : Subgroup ↥K), hidx, mul_one]
    exact hn
  exact IsPGroup.of_card hcard

private theorem f112_hedge {L1 L2 S : Subgroup G}
    (hF : F112HypW L1 L2 S)
    (hK1 : ∀ t ∈ (f112K1 L1 L2 S).map (L1 ⊔ bigB L1 L2 S).subtype, ∀ l ∈ L1,
      l * t * l⁻¹ * t⁻¹ ∈ pCoreOf 2 L1)
    (hK2 : ∀ t ∈ (f112K2 L1 L2 S).map (L2 ⊔ bigB L1 L2 S).subtype, ∀ l ∈ L2,
      l * t * l⁻¹ * t⁻¹ ∈ pCoreOf 2 L2) :
    ∀ (x y : f112Gamma L1 L2 S) (g : f112Acting L1 L2 S),
      (f112Amalgam L1 L2 S).graphHat.Adj x y →
      (∀ w, (f112Amalgam L1 L2 S).graphHat.Adj x w → g • w = w) →
      (∀ w, (f112Amalgam L1 L2 S).graphHat.Adj y w → g • w = w) →
      ∃ k, orderOf g = 2 ^ k := by
  have hprime : ∀ (ℓ : ℕ), ℓ.Prime → Odd ℓ → ∀ u : f112Acting L1 L2 S,
      u ∈ edgeKernel (H := f112Acting L1 L2 S) (f112Amalgam L1 L2 S).graphHat
        (f112Gamma0 L1 L2 S) (f112Gamma1 L1 L2 S) → orderOf u = ℓ → False := by
    intro ℓ hℓ hodd u hu huord
    have h1 := f112_base_edge_prime hF hℓ hodd hK1 hK2 hu huord
    rw [h1, orderOf_one] at huord
    exact hℓ.ne_one huord.symm
  have hisP := f112_base_edge_isPGroup hF hprime
  let K : Subgroup (f112Acting L1 L2 S) :=
    edgeKernel (H := f112Acting L1 L2 S) (f112Amalgam L1 L2 S).graphHat
      (f112Gamma0 L1 L2 S) (f112Gamma1 L1 L2 S)
  haveI hKfin : Finite ↥K := f112_base_edge_finite hF
  intro x y g hxy hx hy
  have hgK : g ∈ edgeKernel (H := f112Acting L1 L2 S) (f112Amalgam L1 L2 S).graphHat x y := by
    rw [mem_edgeKernel]
    exact ⟨hx, hy⟩
  obtain ⟨h, hh | hh⟩ := CosetGeom.exists_smul_edge hxy
  · have hconj : h⁻¹ * g * h ∈ K := by
      have h1 := mem_edgeKernel_conj hgK h⁻¹
      have h2 : h⁻¹ • x = f112Gamma0 L1 L2 S := by rw [← hh.1, inv_smul_smul]
      have h3 : h⁻¹ • y = f112Gamma1 L1 L2 S := by rw [← hh.2, inv_smul_smul]
      rw [h2, h3] at h1
      simpa using h1
    have hord : orderOf (h⁻¹ * g * h) = orderOf g := by
      have h1 : orderOf ((MulAut.conj h⁻¹) g) = orderOf g := (MulAut.conj h⁻¹).orderOf_eq g
      have h2 : (MulAut.conj h⁻¹) g = h⁻¹ * g * h := by rw [MulAut.conj_apply, inv_inv]
      rwa [h2] at h1
    obtain ⟨n, hn⟩ :=
      (hisP.to_subgroup (Subgroup.zpowers (⟨h⁻¹ * g * h, hconj⟩ : ↥K))).exists_card_eq
    refine ⟨n, ?_⟩
    rw [← hord, Subgroup.orderOf_coe (⟨h⁻¹ * g * h, hconj⟩ : ↥K),
      ← Nat.card_zpowers (⟨h⁻¹ * g * h, hconj⟩ : ↥K)]
    exact hn
  · have hconj : h⁻¹ * g * h ∈ K := by
      have h1 := mem_edgeKernel_conj hgK h⁻¹
      have h2 : h⁻¹ • x = f112Gamma1 L1 L2 S := by rw [← hh.2, inv_smul_smul]
      have h3 : h⁻¹ • y = f112Gamma0 L1 L2 S := by rw [← hh.1, inv_smul_smul]
      rw [h2, h3, edgeKernel_comm] at h1
      simpa using h1
    have hord : orderOf (h⁻¹ * g * h) = orderOf g := by
      have h1 : orderOf ((MulAut.conj h⁻¹) g) = orderOf g := (MulAut.conj h⁻¹).orderOf_eq g
      have h2 : (MulAut.conj h⁻¹) g = h⁻¹ * g * h := by rw [MulAut.conj_apply, inv_inv]
      rwa [h2] at h1
    obtain ⟨n, hn⟩ :=
      (hisP.to_subgroup (Subgroup.zpowers (⟨h⁻¹ * g * h, hconj⟩ : ↥K))).exists_card_eq
    refine ⟨n, ?_⟩
    rw [← hord, Subgroup.orderOf_coe (⟨h⁻¹ * g * h, hconj⟩ : ↥K),
      ← Nat.card_zpowers (⟨h⁻¹ * g * h, hconj⟩ : ↥K)]
    exact hn

private theorem pCore_card_eq_of_mulEquiv {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y) :
    Nat.card (pCore 2 X) = Nat.card (pCore 2 Y) := by
  have h : (pCore 2 X).map e.toMonoidHom = pCore 2 Y :=
    CFSG.LieType.BorelTits.map_pCore_mulEquiv 2 e
  calc Nat.card (pCore 2 X) = Nat.card ↥((pCore 2 X).map e.toMonoidHom) :=
        (Subgroup.card_map_of_injective e.injective).symm
    _ = Nat.card (pCore 2 Y) := by rw [h]

private theorem pCoreOf_card_eq {G : Type*} [Group G] (P : Subgroup G) :
    Nat.card (pCoreOf 2 P) = Nat.card ↥(pCore 2 ↥P) :=
  Subgroup.card_map_of_injective (f := P.subtype) P.subtype_injective

private theorem f112_stabilizer_equiv_of_vtype_false
    {L1 L2 S : Subgroup G} (hF : F112HypW L1 L2 S) {v : f112Gamma L1 L2 S}
    (hv : CosetGeom.vtype v = false) :
    Nonempty (MulAction.stabilizer (f112Acting L1 L2 S) v ≃* ↥(L1 ⊔ bigB L1 L2 S)) := by
  obtain ⟨g, hg⟩ := CosetGeom.exists_smul_eq_γ₀ (G₀ := (f112Amalgam L1 L2 S).Ghat1 ⊔
    (f112Amalgam L1 L2 S).Ghat2) (G₁ := (f112Amalgam L1 L2 S).Ghat1)
    (G₂ := (f112Amalgam L1 L2 S).Ghat2) hv
  rw [hg, MulAction.stabilizer_smul_eq_stabilizer_map_conj]
  exact ⟨(Subgroup.equivMapOfInjective _ (MulAut.conj g).toMonoidHom
    (MulAut.conj g).injective).symm.trans (f112StabEquiv0 L1 L2 S)⟩

private theorem f112_stabilizer_equiv_of_vtype_true
    {L1 L2 S : Subgroup G} (hF : F112HypW L1 L2 S) {v : f112Gamma L1 L2 S}
    (hv : CosetGeom.vtype v = true) :
    Nonempty (MulAction.stabilizer (f112Acting L1 L2 S) v ≃* ↥(L2 ⊔ bigB L1 L2 S)) := by
  obtain ⟨g, hg⟩ := CosetGeom.exists_smul_eq_γ₁ (G₀ := (f112Amalgam L1 L2 S).Ghat1 ⊔
    (f112Amalgam L1 L2 S).Ghat2) (G₁ := (f112Amalgam L1 L2 S).Ghat1)
    (G₂ := (f112Amalgam L1 L2 S).Ghat2) hv
  rw [hg, MulAction.stabilizer_smul_eq_stabilizer_map_conj]
  exact ⟨(Subgroup.equivMapOfInjective _ (MulAut.conj g).toMonoidHom
    (MulAut.conj g).injective).symm.trans (f112StabEquiv1 L1 L2 S)⟩

private theorem f112_hval {L1 L2 S : Subgroup G}
    (hF : F112HypW L1 L2 S) {e₁ e₂ : ℕ}
    (hv1 : (bigB L1 L2 S).relIndex (L1 ⊔ bigB L1 L2 S) = 2 ^ e₁ + 1)
    (hv2 : (bigB L1 L2 S).relIndex (L2 ⊔ bigB L1 L2 S) = 2 ^ e₂ + 1)
    (v w : f112Gamma L1 L2 S) (hw : (f112Amalgam L1 L2 S).graphHat.Adj v w) :
    ∃ k, Nat.card {y : f112Gamma L1 L2 S // (f112Amalgam L1 L2 S).graphHat.Adj v y ∧ y ≠ w} =
      2 ^ k := by
  have hw' : w ∈ (f112Amalgam L1 L2 S).graphHat.neighborSet v := hw
  have hcard : Nat.card {y : f112Gamma L1 L2 S //
      (f112Amalgam L1 L2 S).graphHat.Adj v y ∧ y ≠ w} =
      Nat.card ((f112Amalgam L1 L2 S).graphHat.neighborSet v) - 1 := by
    have h1 : {y : f112Gamma L1 L2 S |
        (f112Amalgam L1 L2 S).graphHat.Adj v y ∧ y ≠ w} =
        (f112Amalgam L1 L2 S).graphHat.neighborSet v \ {w} := rfl
    have e1 : Nat.card {y : f112Gamma L1 L2 S //
        (f112Amalgam L1 L2 S).graphHat.Adj v y ∧ y ≠ w} =
        {y : f112Gamma L1 L2 S |
          (f112Amalgam L1 L2 S).graphHat.Adj v y ∧ y ≠ w}.ncard :=
        Nat.card_coe_set_eq (s := {y : f112Gamma L1 L2 S |
          (f112Amalgam L1 L2 S).graphHat.Adj v y ∧ y ≠ w})
    rw [e1, h1, Set.ncard_sdiff_singleton_of_mem hw', Nat.card_coe_set_eq]
  rcases f112_natCard_neighborSet hF v with h | h
  · refine ⟨e₁, ?_⟩
    rw [hcard, h, hv1, Nat.add_sub_cancel]
  · refine ⟨e₂, ?_⟩
    rw [hcard, h, hv2, Nat.add_sub_cancel]

private theorem f112_h2 {L1 L2 S : Subgroup G}
    (hF : F112HypW L1 L2 S) {j e₁ e₂ : ℕ} (hj : 1 ≤ j)
    (hLT : IsLocallyTransHat (f112Amalgam L1 L2 S) (2 * j + 1))
    (hv1 : (bigB L1 L2 S).relIndex (L1 ⊔ bigB L1 L2 S) = 2 ^ e₁ + 1)
    (hv2 : (bigB L1 L2 S).relIndex (L2 ⊔ bigB L1 L2 S) = 2 ^ e₂ + 1)
    (hQ1 : Nat.card (pCoreOf 2 (L1 ⊔ bigB L1 L2 S)) * 2 ^ e₁ = Nat.card S)
    (hQ2 : Nat.card (pCoreOf 2 (L2 ⊔ bigB L1 L2 S)) * 2 ^ e₂ = Nat.card S)
    (hS : Nat.card S = 2 ^ ((e₁ + e₂) * j)) :
    ∀ (v w w' : f112Gamma L1 L2 S) (g : f112Acting L1 L2 S),
      (f112Amalgam L1 L2 S).graphHat.Adj v w →
      (f112Amalgam L1 L2 S).graphHat.Adj v w' → w ≠ w' →
      (∃ k, orderOf g = 2 ^ k) → g • v = v → g • w = w → g • w' = w' →
      ∀ u, (f112Amalgam L1 L2 S).graphHat.Adj v u → g • u = u := by
  intro v w w' g hw hw' hww' hg hgv hgw hgw' u hu
  have hne : ∀ v w : f112Gamma L1 L2 S, (f112Amalgam L1 L2 S).graphHat.Adj v w →
      ∃ u, (f112Amalgam L1 L2 S).graphHat.Adj v u ∧ u ≠ w :=
    fun v w h => f112_no_dead_ends hF h
  have htr : ∀ w₁ w₂ : f112Gamma L1 L2 S,
      (f112Amalgam L1 L2 S).graphHat.Adj v w₁ →
      (f112Amalgam L1 L2 S).graphHat.Adj v w₂ →
      ∃ g : f112Acting L1 L2 S, g • v = v ∧ g • w₁ = w₂ := by
    intro w₁ w₂ h₁ h₂
    obtain ⟨g, hg, hgw⟩ := f112_stabilizer_transitive_on_nbrs hF h₁ h₂
    exact ⟨g, MulAction.mem_stabilizer_iff.mp hg, hgw⟩
  have htr2 : ∀ w₀ x₁ x₂ : f112Gamma L1 L2 S,
      (f112Amalgam L1 L2 S).graphHat.Adj v w₀ →
      (f112Amalgam L1 L2 S).graphHat.Adj v x₁ →
      (f112Amalgam L1 L2 S).graphHat.Adj v x₂ → x₁ ≠ w₀ → x₂ ≠ w₀ →
      ∃ g : f112Acting L1 L2 S, g • v = v ∧ g • w₀ = w₀ ∧ g • x₁ = x₂ := by
    intro w₀ x₁ x₂ h₀ h₁ h₂ h₁₀ h₂₀
    have h2 : IsLocallyTransHat (f112Amalgam L1 L2 S) 2 :=
      IsLocallyTrans.mono (t := 2) (by omega) hne hLT
    exact exists_smul_nbr_fix_of_isLocallyTrans h2 le_rfl hne h₀ h₁ h₂ h₁₀ h₂₀
  haveI hfinv : Finite ↥(MulAction.stabilizer (f112Acting L1 L2 S) v) :=
    f112_finite_stabilizer hF v
  have hsyl1 : ∀ P : Sylow 2 (MulAction.stabilizer (f112Acting L1 L2 S) v),
      Nat.card P = 2 ^ e₁ * Nat.card (pCoreOf 2 (L1 ⊔ bigB L1 L2 S)) := by
    intro P
    have h1 : Nat.card S = 2 ^ e₁ * Nat.card (pCoreOf 2 (L1 ⊔ bigB L1 L2 S)) := by
      rw [← hQ1, mul_comm]
    rw [f112_card_sylow_stabilizer hF v P, h1]
  have hsyl2 : ∀ P : Sylow 2 (MulAction.stabilizer (f112Acting L1 L2 S) v),
      Nat.card P = 2 ^ e₂ * Nat.card (pCoreOf 2 (L2 ⊔ bigB L1 L2 S)) := by
    intro P
    have h1 : Nat.card S = 2 ^ e₂ * Nat.card (pCoreOf 2 (L2 ⊔ bigB L1 L2 S)) := by
      rw [← hQ2, mul_comm]
    rw [f112_card_sylow_stabilizer hF v P, h1]
  cases hv : CosetGeom.vtype v
  · have hval : Nat.card ((f112Amalgam L1 L2 S).graphHat.neighborSet v) = 2 ^ e₁ + 1 := by
      rw [f112_natCard_neighborSet_of_vtype_false hF hv, hv1]
    have hpc : Nat.card (pCore 2 ↥(MulAction.stabilizer (f112Acting L1 L2 S) v)) =
        Nat.card (pCoreOf 2 (L1 ⊔ bigB L1 L2 S)) := by
      obtain ⟨e⟩ := f112_stabilizer_equiv_of_vtype_false hF hv
      rw [pCore_card_eq_of_mulEquiv e, pCoreOf_card_eq]
    exact forall_smul_eq_of_card htr htr2 hval hsyl1 (le_of_eq hpc.symm)
      hw hw' hww' hg hgv hgw hgw' u hu
  · have hval : Nat.card ((f112Amalgam L1 L2 S).graphHat.neighborSet v) = 2 ^ e₂ + 1 := by
      rw [f112_natCard_neighborSet_of_vtype_true hF hv, hv2]
    have hpc : Nat.card (pCore 2 ↥(MulAction.stabilizer (f112Acting L1 L2 S) v)) =
        Nat.card (pCoreOf 2 (L2 ⊔ bigB L1 L2 S)) := by
      obtain ⟨e⟩ := f112_stabilizer_equiv_of_vtype_true hF hv
      rw [pCore_card_eq_of_mulEquiv e, pCoreOf_card_eq]
    exact forall_smul_eq_of_card htr htr2 hval hsyl2 (le_of_eq hpc.symm)
      hw hw' hww' hg hgv hgw hgw' u hu

theorem f112_qOne {L1 L2 S : Subgroup G}
    (hF : F112HypW L1 L2 S) {e₁ : ℕ}
    (hv1 : (bigB L1 L2 S).relIndex (L1 ⊔ bigB L1 L2 S) = 2 ^ e₁ + 1) :
    (f112Amalgam L1 L2 S).qOne = 2 ^ e₁ := by
  have hidx : (f112Amalgam L1 L2 S).α1.range.index = 2 ^ e₁ + 1 := by
    have h3 : (f112Amalgam L1 L2 S).α1.range =
        (bigB L1 L2 S).subgroupOf (L1 ⊔ bigB L1 L2 S) := by
      rw [show (f112Amalgam L1 L2 S).α1.range =
          ((L1 ⊔ bigB L1 L2 S) ⊓ (L2 ⊔ bigB L1 L2 S)).subgroupOf
            (L1 ⊔ bigB L1 L2 S) from
        Subgroup.inclusion_range (inf_le_left : (L1 ⊔ bigB L1 L2 S) ⊓
          (L2 ⊔ bigB L1 L2 S) ≤ (L1 ⊔ bigB L1 L2 S)),
        f112_parabolic_inf_eq_bigB hF]
    rw [h3, ← hv1]
    rfl
  show (f112Amalgam L1 L2 S).α1.range.index - 1 = 2 ^ e₁
  rw [hidx, Nat.add_sub_cancel]

theorem f112_qTwo {L1 L2 S : Subgroup G}
    (hF : F112HypW L1 L2 S) {e₂ : ℕ}
    (hv2 : (bigB L1 L2 S).relIndex (L2 ⊔ bigB L1 L2 S) = 2 ^ e₂ + 1) :
    (f112Amalgam L1 L2 S).qTwo = 2 ^ e₂ := by
  have hidx : (f112Amalgam L1 L2 S).α2.range.index = 2 ^ e₂ + 1 := by
    have h3 : (f112Amalgam L1 L2 S).α2.range =
        (bigB L1 L2 S).subgroupOf (L2 ⊔ bigB L1 L2 S) := by
      rw [show (f112Amalgam L1 L2 S).α2.range =
          ((L1 ⊔ bigB L1 L2 S) ⊓ (L2 ⊔ bigB L1 L2 S)).subgroupOf
            (L2 ⊔ bigB L1 L2 S) from
        Subgroup.inclusion_range (inf_le_right : (L1 ⊔ bigB L1 L2 S) ⊓
          (L2 ⊔ bigB L1 L2 S) ≤ (L2 ⊔ bigB L1 L2 S)),
        f112_parabolic_inf_eq_bigB hF]
    rw [h3, ← hv2]
    rfl
  show (f112Amalgam L1 L2 S).α2.range.index - 1 = 2 ^ e₂
  rw [hidx, Nat.add_sub_cancel]

private theorem f112_path_stab_odd {L1 L2 S : Subgroup G}
    (hF : F112HypW L1 L2 S) {j e₁ e₂ : ℕ}
    (hLT : IsLocallyTransHat (f112Amalgam L1 L2 S) (2 * j + 1))
    (hQ1 : Nat.card (pCoreOf 2 (L1 ⊔ bigB L1 L2 S)) * 2 ^ e₁ = Nat.card S)
    (hQ2 : Nat.card (pCoreOf 2 (L2 ⊔ bigB L1 L2 S)) * 2 ^ e₂ = Nat.card S)
    (hS : Nat.card S = 2 ^ ((e₁ + e₂) * j))
    (hq1 : (f112Amalgam L1 L2 S).qOne = 2 ^ e₁)
    (hq2 : (f112Amalgam L1 L2 S).qTwo = 2 ^ e₂)
    {p : GPath (f112Amalgam L1 L2 S).graphHat (2 * j + 1)} (hp : p.NoBack) :
    Odd (Nat.card ((((f112Completion L1 L2 S).graphCovering
      (f112Completion_isFaithful L1 L2 S)).pathMap p).stabPath :
        Subgroup (f112Completion L1 L2 S).G0)) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hc : (f112Completion L1 L2 S).IsFaithful := f112Completion_isFaithful L1 L2 S
  have hM : ((f112Amalgam L1 L2 S).qOne * (f112Amalgam L1 L2 S).qTwo) ^ j = Nat.card S := by
    rw [hq1, hq2, ← pow_add, ← pow_mul, hS]
  let a : (f112Completion L1 L2 S).Γ := (f112Completion L1 L2 S).Θ hc (p 0)
  let q : GPath (f112Completion L1 L2 S).graph (2 * j + 1) :=
    ((f112Completion L1 L2 S).graphCovering hc).pathMap p
  have hq : q ∈ GPath.nbPaths (f112Completion L1 L2 S).graph a (2 * j + 1) := by
    refine ⟨?_, ?_⟩
    · simp [q, a, GraphCovering.pathMap_apply]
    · exact (((f112Completion L1 L2 S).graphCovering hc).noBack_pathMap_iff p).mpr hp
  have htrans : ∀ q₁ q₂ : GPath (f112Amalgam L1 L2 S).graphHat (2 * j + 1),
      q₁ ∈ GPath.nbPaths (f112Amalgam L1 L2 S).graphHat (p 0) (2 * j + 1) →
      q₂ ∈ GPath.nbPaths (f112Amalgam L1 L2 S).graphHat (p 0) (2 * j + 1) →
      ∃ u : f112Acting L1 L2 S, u • p 0 = p 0 ∧ u • q₁ = q₂ := by
    intro q₁ q₂ hq₁ hq₂
    obtain ⟨u, hu⟩ := hLT q₁ q₂ hq₁.2 hq₂.2 (by rw [hq₁.1, hq₂.1])
    refine ⟨u, ?_, hu⟩
    have h0 : u • q₁ 0 = q₂ 0 := by
      simpa [GPath.smul_apply] using
        congrArg (fun r : GPath (f112Amalgam L1 L2 S).graphHat (2 * j + 1) => r 0) hu
    rwa [hq₁.1, hq₂.1] at h0
  have hT : (f112Completion L1 L2 S).PathTrans a (2 * j + 1) :=
    (f112Completion L1 L2 S).lemma_F33_4 hc (p 0) (2 * j + 1) htrans
  haveI hfin0 : Finite (MulAction.stabilizer (f112Acting L1 L2 S) (p 0)) := by
    let e := ((f112Completion L1 L2 S).stabIso hc (p 0)).equiv
    refine Finite.of_injective (fun x => (e x : ↥((f112Completion L1 L2 S).φ1.range ⊔
      (f112Completion L1 L2 S).φ2.range))) ?_
    intro x y hxy
    exact e.injective (Subtype.ext hxy)
  have hrel := RankTwoAmalgam.Completion.relIndex_stabPath (c := f112Completion L1 L2 S) hc hT hq
  have hqvprod : (f112Amalgam L1 L2 S).qv (CosetGeom.vtype a) *
      (f112Amalgam L1 L2 S).qv (!CosetGeom.vtype a) =
      (f112Amalgam L1 L2 S).qOne * (f112Amalgam L1 L2 S).qTwo := by
    cases hb : CosetGeom.vtype a <;> simp [RankTwoAmalgam.qv, hb, mul_comm]
  have hpathNum : (f112Amalgam L1 L2 S).pathNum (CosetGeom.vtype a) (2 * j + 1) =
      ((f112Amalgam L1 L2 S).qv (CosetGeom.vtype a) + 1) *
        ((f112Amalgam L1 L2 S).qOne * (f112Amalgam L1 L2 S).qTwo) ^ j := by
    rw [RankTwoAmalgam.pathNum_odd, hqvprod]
  have hle : (q.stabPath : Subgroup (f112Completion L1 L2 S).G0) ≤
      (f112Completion L1 L2 S).stv a := GPath.stabPath_le_stabilizer q hq.1
  have hrelMul := Subgroup.relIndex_mul_card
    (H := (q.stabPath : Subgroup (f112Completion L1 L2 S).G0))
    (K := (f112Completion L1 L2 S).stv a)
  rw [inf_eq_left.mpr hle, hrel, hpathNum] at hrelMul
  obtain ⟨P⟩ := Sylow.nonempty (p := 2) (G := (f112Completion L1 L2 S).stv a)
  have hPcard : Nat.card P = ((f112Amalgam L1 L2 S).qOne * (f112Amalgam L1 L2 S).qTwo) ^ j := by
    let e := ((f112Completion L1 L2 S).stabIso hc (p 0)).equiv
    let P' : Sylow 2 (MulAction.stabilizer (f112Acting L1 L2 S) (p 0)) :=
      P.mapSurjective (f := e.symm.toMonoidHom) e.symm.surjective
    have h1 : Nat.card P' = Nat.card S := f112_card_sylow_stabilizer hF (p 0) P'
    have h2 : Nat.card P' = Nat.card P := by
      rw [show (P' : Subgroup ↥(MulAction.stabilizer (f112Acting L1 L2 S) (p 0))) =
          (P : Subgroup ((f112Completion L1 L2 S).stv a)).map e.symm.toMonoidHom from
        Sylow.coe_mapSurjective e.symm.surjective P]
      exact Subgroup.card_map_of_injective
        (K := (P : Subgroup ((f112Completion L1 L2 S).stv a)))
        (f := e.symm.toMonoidHom) e.symm.injective
    rw [← h2, h1, ← hM]
  have hMpos : 0 < ((f112Amalgam L1 L2 S).qOne * (f112Amalgam L1 L2 S).qTwo) ^ j := by
    haveI : Nonempty ↥(P : Subgroup ((f112Completion L1 L2 S).stv a)) :=
      ⟨⟨1, Subgroup.one_mem (P : Subgroup ((f112Completion L1 L2 S).stv a))⟩⟩
    have hPpos : 0 < Nat.card P := Nat.card_pos
    rwa [hPcard] at hPpos
  have hcardStv : Nat.card ((f112Completion L1 L2 S).stv a) =
      Nat.card (q.stabPath : Subgroup (f112Completion L1 L2 S).G0) *
        (((f112Amalgam L1 L2 S).qv (CosetGeom.vtype a) + 1) *
          ((f112Amalgam L1 L2 S).qOne * (f112Amalgam L1 L2 S).qTwo) ^ j) := by
    rw [← hrelMul]
    ring
  have hPodd : Odd (P : Subgroup ((f112Completion L1 L2 S).stv a)).index :=
    Nat.not_even_iff_odd.mp (by simpa [even_iff_two_dvd] using P.not_dvd_index)
  have hcardStv2 : Nat.card ((f112Completion L1 L2 S).stv a) =
      ((f112Amalgam L1 L2 S).qOne * (f112Amalgam L1 L2 S).qTwo) ^ j *
        (P : Subgroup ((f112Completion L1 L2 S).stv a)).index := by
    rw [← Subgroup.card_mul_index (P : Subgroup ((f112Completion L1 L2 S).stv a)), hPcard]
  have hcancel : Nat.card (q.stabPath : Subgroup (f112Completion L1 L2 S).G0) *
      ((f112Amalgam L1 L2 S).qv (CosetGeom.vtype a) + 1) =
      (P : Subgroup ((f112Completion L1 L2 S).stv a)).index := by
    have h1 : ((f112Amalgam L1 L2 S).qOne * (f112Amalgam L1 L2 S).qTwo) ^ j *
        (Nat.card (q.stabPath : Subgroup (f112Completion L1 L2 S).G0) *
          ((f112Amalgam L1 L2 S).qv (CosetGeom.vtype a) + 1)) =
        ((f112Amalgam L1 L2 S).qOne * (f112Amalgam L1 L2 S).qTwo) ^ j *
          (P : Subgroup ((f112Completion L1 L2 S).stv a)).index := by
      calc ((f112Amalgam L1 L2 S).qOne * (f112Amalgam L1 L2 S).qTwo) ^ j *
            (Nat.card (q.stabPath : Subgroup (f112Completion L1 L2 S).G0) *
              ((f112Amalgam L1 L2 S).qv (CosetGeom.vtype a) + 1))
          = Nat.card (q.stabPath : Subgroup (f112Completion L1 L2 S).G0) *
            (((f112Amalgam L1 L2 S).qv (CosetGeom.vtype a) + 1) *
              ((f112Amalgam L1 L2 S).qOne * (f112Amalgam L1 L2 S).qTwo) ^ j) := by ring
        _ = Nat.card ((f112Completion L1 L2 S).stv a) := hcardStv.symm
        _ = ((f112Amalgam L1 L2 S).qOne * (f112Amalgam L1 L2 S).qTwo) ^ j *
            (P : Subgroup ((f112Completion L1 L2 S).stv a)).index := hcardStv2
    exact Nat.mul_left_cancel hMpos h1
  exact hPodd.of_dvd_nat ⟨(f112Amalgam L1 L2 S).qv (CosetGeom.vtype a) + 1, hcancel.symm⟩

private theorem f112_path_odd {L1 L2 S : Subgroup G}
    (hF : F112HypW L1 L2 S) {j e₁ e₂ : ℕ}
    (hLT : IsLocallyTransHat (f112Amalgam L1 L2 S) (2 * j + 1))
    (hQ1 : Nat.card (pCoreOf 2 (L1 ⊔ bigB L1 L2 S)) * 2 ^ e₁ = Nat.card S)
    (hQ2 : Nat.card (pCoreOf 2 (L2 ⊔ bigB L1 L2 S)) * 2 ^ e₂ = Nat.card S)
    (hS : Nat.card S = 2 ^ ((e₁ + e₂) * j))
    (hq1 : (f112Amalgam L1 L2 S).qOne = 2 ^ e₁)
    (hq2 : (f112Amalgam L1 L2 S).qTwo = 2 ^ e₂)
    {g : f112Acting L1 L2 S} {p : GPath (f112Amalgam L1 L2 S).graphHat (2 * j + 1)}
    (hp : p.NoBack) (hfix : ∀ i, i ≤ 2 * j + 1 → g • p i = p i)
    (hg : ∃ k, orderOf g = 2 ^ k) : g = 1 := by
  have hc : (f112Completion L1 L2 S).IsFaithful := f112Completion_isFaithful L1 L2 S
  let q : GPath (f112Completion L1 L2 S).graph (2 * j + 1) :=
    ((f112Completion L1 L2 S).graphCovering hc).pathMap p
  have hoddStab : Odd (Nat.card (q.stabPath : Subgroup (f112Completion L1 L2 S).G0)) :=
    f112_path_stab_odd hF hLT hQ1 hQ2 hS hq1 hq2 hp
  obtain ⟨k, hk⟩ := hg
  have hgmap : (f112Completion L1 L2 S).theta0 hc g ∈
      (q.stabPath : Subgroup (f112Completion L1 L2 S).G0) := by
    have hmap := ((f112Completion L1 L2 S).lemma_F33_3 hc (p 0) p rfl).1
    rw [← hmap]
    exact Subgroup.mem_map_of_mem ((f112Completion L1 L2 S).theta0 hc)
      (GPath.mem_stabPath_iff.mpr hfix)
  have horderStab : orderOf ((f112Completion L1 L2 S).theta0 hc g) ∣
      Nat.card (q.stabPath : Subgroup (f112Completion L1 L2 S).G0) :=
    Subgroup.orderOf_dvd_natCard _ hgmap
  have horder2 : orderOf ((f112Completion L1 L2 S).theta0 hc g) ∣ 2 ^ k := by
    rw [← hk]
    exact orderOf_map_dvd ((f112Completion L1 L2 S).theta0 hc) g
  have hcop : Nat.Coprime (Nat.card (q.stabPath : Subgroup (f112Completion L1 L2 S).G0))
      (2 ^ k) := hoddStab.coprime_two_right.pow_right k
  have hOrderOne : orderOf ((f112Completion L1 L2 S).theta0 hc g) = 1 :=
    Nat.eq_one_of_dvd_coprimes hcop horderStab horder2
  have htheta1 : (f112Completion L1 L2 S).theta0 hc g = 1 := orderOf_eq_one_iff.mp hOrderOne
  exact ((f112Completion L1 L2 S).stabIso hc (p 0)).inj g
    (by simpa using hfix 0 (Nat.zero_le _)) htheta1

theorem f112_weissMoufangHat {G : Type} [Group G] [Finite G]
    {L1 L2 S : Subgroup G} (hF : F112HypW L1 L2 S) {j e₁ e₂ : ℕ} (hj : 1 ≤ j)
    (hLT : IsLocallyTransHat (f112Amalgam L1 L2 S) (2 * j + 1))
    (hv1 : (bigB L1 L2 S).relIndex (L1 ⊔ bigB L1 L2 S) = 2 ^ e₁ + 1)
    (hv2 : (bigB L1 L2 S).relIndex (L2 ⊔ bigB L1 L2 S) = 2 ^ e₂ + 1)
    (hQ1 : Nat.card (pCoreOf 2 (L1 ⊔ bigB L1 L2 S)) * 2 ^ e₁ = Nat.card S)
    (hQ2 : Nat.card (pCoreOf 2 (L2 ⊔ bigB L1 L2 S)) * 2 ^ e₂ = Nat.card S)
    (hS : Nat.card S = 2 ^ ((e₁ + e₂) * j))
    (hK1 : ∀ t ∈ (f112K1 L1 L2 S).map (L1 ⊔ bigB L1 L2 S).subtype, ∀ l ∈ L1,
      l * t * l⁻¹ * t⁻¹ ∈ pCoreOf 2 L1)
    (hK2 : ∀ t ∈ (f112K2 L1 L2 S).map (L2 ⊔ bigB L1 L2 S).subtype, ∀ l ∈ L2,
      l * t * l⁻¹ * t⁻¹ ∈ pCoreOf 2 L2) :
    WeissMoufangHat (f112Amalgam L1 L2 S) (2 * j) := by
  have hq1 : (f112Amalgam L1 L2 S).qOne = 2 ^ e₁ := f112_qOne hF hv1
  have hq2 : (f112Amalgam L1 L2 S).qTwo = 2 ^ e₂ := f112_qTwo hF hv2
  have hne : ∀ v w : f112Gamma L1 L2 S, (f112Amalgam L1 L2 S).graphHat.Adj v w →
      ∃ u, (f112Amalgam L1 L2 S).graphHat.Adj v u ∧ u ≠ w :=
    fun v w h => f112_no_dead_ends hF h
  constructor
  · have hs : 3 ≤ 2 * j + 1 := by omega
    have hm : MoufangHat (f112Amalgam L1 L2 S) (2 * j + 1 - 1) :=
      moufangHat_of_isLocallyTrans (f112Amalgam L1 L2 S) hs hLT
        (f112_hval hF hv1 hv2) (f112_finite_stabilizer hF)
        (f112_h2 hF hj hLT hv1 hv2 hQ1 hQ2 hS) hne
    simpa using hm
  · refine weissFreeHat_of_odd (f112Amalgam L1 L2 S) (n := 2 * j) (by omega)
      (f112_hedge hF hK1 hK2) ?_ hne
    intro g q hq hfix hg
    exact f112_path_odd hF hLT hQ1 hQ2 hS hq1 hq2 hq hfix hg

end
end CFSG.Quasithin.Stroth
