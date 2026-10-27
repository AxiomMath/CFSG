module

public import CFSG.Quasithin.Recognition.CertTwoLocalIndexTwo
public import CFSG.Quasithin.Recognition.CertU33Phi
public import CFSG.Quasithin.Recognition.CertU33AutBound

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

theorem u33Pi_core
    : IndexTwoCore u33PresHom u33Pi u33Phi' where
  sq := u33Pi_sq
  conj x := by rw [u33Pi_inv, u33PresHom_phi']

@[expose] noncomputable def g2CG
    : Subgroup (Equiv.Perm (Fin 28)) :=
  u33Pi_core.ext (⊤ : Subgroup U33G) (fun _ _ => Subgroup.mem_top _)

abbrev G2P :
    Type := ↥g2CG

theorem u33PresHom_mem_g2CG
    (x : U33G) : u33PresHom x ∈ g2CG :=
  u33Pi_core.map_le_ext (H₀ := (⊤ : Subgroup U33G)) (fun _ _ => Subgroup.mem_top _)
    ⟨x, trivial, rfl⟩

theorem u33Pi_mem_g2CG
    : u33Pi ∈ g2CG :=
  u33Pi_core.rho_mem_ext (H₀ := (⊤ : Subgroup U33G)) (fun _ _ => Subgroup.mem_top _)

@[expose] noncomputable def g2F
    : U33G →* G2P := u33PresHom.codRestrict g2CG u33PresHom_mem_g2CG

@[expose] def g2E8Rho
    : G2P := ⟨u33Pi, u33Pi_mem_g2CG⟩

theorem g2F_coe
    (x : U33G) : ((g2F x : G2P) : Equiv.Perm (Fin 28)) = u33PresHom x := rfl

theorem g2E8Rho_coe
    : ((g2E8Rho : G2P) : Equiv.Perm (Fin 28)) = u33Pi := rfl

theorem g2_indexTwo
    : IndexTwoData g2F g2E8Rho u33Phi' where
  sq := Subtype.ext (by
    show u33Pi * u33Pi = 1
    exact u33Pi_sq)
  conj x := Subtype.ext (by
    show u33Pi * u33PresHom x * u33Pi⁻¹ = u33PresHom (u33Phi' x)
    rw [u33Pi_inv, u33PresHom_phi'])
  inj := fun x y h => u33PresHom_injective (congrArg Subtype.val h)
  cover := fun g => by
    rcases (u33Pi_core.mem_ext (H₀ := (⊤ : Subgroup U33G))
      (hH := fun _ _ => Subgroup.mem_top _)).1 g.2 with ⟨x, -, hx⟩ | ⟨x, -, hx⟩
    · exact Or.inl ⟨x, Subtype.ext hx⟩
    · exact Or.inr ⟨x, Subtype.ext hx⟩
  outer := u33Phi'_not_inner

@[expose] noncomputable def g2AmalL
    : TwoLocalLattice G2P where
  S := g2_indexTwo.ext u33Data.T u33Phi'_T
  P₁ := g2_indexTwo.ext u33Data.A u33Phi'_A
  P₂ := g2_indexTwo.ext u33Data.B u33Phi'_B
  sylow := ⟨g2_indexTwo.isPGroup_ext u33Phi'_T u33Extra.syl.1, by
    rw [g2_indexTwo.index_ext_T u33Phi'_T]
    exact u33Extra.syl.2⟩
  lattice := g2_indexTwo.lattice u33Phi'_T u33Phi'_A u33Phi'_B
  S_le_P₁ := g2_indexTwo.ext_mono u33Phi'_T u33Phi'_A u33Data.T_le_A
  S_le_P₂ := g2_indexTwo.ext_mono u33Phi'_T u33Phi'_B u33Data.T_le_B
  S_ne_P₁ := by
    intro h
    apply IndexTwoData.x_not_mem_T u33Extra
    apply g2_indexTwo.mem_of_map_mem_ext (hH := u33Phi'_T)
    rw [h]
    exact g2_indexTwo.map_le_ext u33Phi'_A ⟨u33Data.x, u33Data.x_mem_A, rfl⟩
  S_ne_P₂ := by
    intro h
    apply IndexTwoData.y_not_mem_T u33Extra
    apply g2_indexTwo.mem_of_map_mem_ext (hH := u33Phi'_T)
    rw [h]
    exact g2_indexTwo.map_le_ext u33Phi'_B ⟨u33Data.y, u33Data.y_mem_B, rfl⟩
  P₁_not_le_P₂ := by
    intro h
    apply u33Data.T_ne_A
    refine le_antisymm u33Data.T_le_A ?_
    rw [← u33Data.inf_AB]
    refine le_inf le_rfl fun x hx => ?_
    exact g2_indexTwo.mem_of_map_mem_ext (h (g2_indexTwo.map_le_ext u33Phi'_A ⟨x, hx, rfl⟩))
  P₂_not_le_P₁ := by
    intro h
    apply u33Data.T_ne_B
    refine le_antisymm u33Data.T_le_B ?_
    rw [← u33Data.inf_AB]
    refine le_inf (fun x hx => ?_) le_rfl
    exact g2_indexTwo.mem_of_map_mem_ext (h (g2_indexTwo.map_le_ext u33Phi'_B ⟨x, hx, rfl⟩))
  O₂ := fun Q hQ hQp => g2_indexTwo.eq_bot_of_normal u33Extra Q hQ hQp
  loc₁ := ⟨u33Extra.PA.map g2F,
    (Subgroup.map_eq_bot_iff_of_injective u33Extra.PA g2_indexTwo.inj).not.2 u33Extra.PA_ne,
    u33Extra.PA_p.map g2F, g2_indexTwo.ext_le_normalizer u33Phi'_A u33Phi'_PA u33Extra.PA_norm⟩
  loc₂ := ⟨u33Extra.PB.map g2F,
    (Subgroup.map_eq_bot_iff_of_injective u33Extra.PB g2_indexTwo.inj).not.2 u33Extra.PB_ne,
    u33Extra.PB_p.map g2F, g2_indexTwo.ext_le_normalizer u33Phi'_B u33Phi'_PB u33Extra.PB_norm⟩
  normS := by
    have hSM : g2_indexTwo.ext u33Data.T u33Phi'_T ≤
        Subgroup.normalizer ((g2_indexTwo.ext u33Data.T u33Phi'_T : Subgroup G2P) : Set G2P) :=
      Subgroup.le_normalizer
    rcases g2_indexTwo.lattice u33Phi'_T u33Phi'_A u33Phi'_B _ hSM with h | h | h | h
    · exact h.le
    · exfalso
      have hfx : g2F u33Data.x ∈ Subgroup.normalizer
          ((g2_indexTwo.ext u33Data.T u33Phi'_T : Subgroup G2P) : Set G2P) := by
        rw [h]
        exact g2_indexTwo.map_le_ext u33Phi'_A ⟨u33Data.x, u33Data.x_mem_A, rfl⟩
      obtain ⟨i, hi⟩ := u33Extra.xN
      have h1 : g2F (u33Data.Tel i) ∈ g2_indexTwo.ext u33Data.T u33Phi'_T :=
        g2_indexTwo.map_le_ext u33Phi'_T ⟨u33Data.Tel i, u33Data.Tel_mem_T i, rfl⟩
      have h2 := (Subgroup.mem_normalizer_iff.1 hfx _).1 h1
      have h3 : g2F (u33Data.x * u33Data.Tel i * u33Data.x⁻¹) ∈
          g2_indexTwo.ext u33Data.T u33Phi'_T := by simpa [map_mul, map_inv] using h2
      obtain ⟨i', hi'⟩ := (u33Data.mem_T_iff _).1 (g2_indexTwo.mem_of_map_mem_ext h3)
      exact hi i' hi'.symm
    · exfalso
      have hfy : g2F u33Data.y ∈ Subgroup.normalizer
          ((g2_indexTwo.ext u33Data.T u33Phi'_T : Subgroup G2P) : Set G2P) := by
        rw [h]
        exact g2_indexTwo.map_le_ext u33Phi'_B ⟨u33Data.y, u33Data.y_mem_B, rfl⟩
      obtain ⟨i, hi⟩ := u33Extra.yN
      have h1 : g2F (u33Data.Tel i) ∈ g2_indexTwo.ext u33Data.T u33Phi'_T :=
        g2_indexTwo.map_le_ext u33Phi'_T ⟨u33Data.Tel i, u33Data.Tel_mem_T i, rfl⟩
      have h2 := (Subgroup.mem_normalizer_iff.1 hfy _).1 h1
      have h3 : g2F (u33Data.y * u33Data.Tel i * u33Data.y⁻¹) ∈
          g2_indexTwo.ext u33Data.T u33Phi'_T := by simpa [map_mul, map_inv] using h2
      obtain ⟨i', hi'⟩ := (u33Data.mem_T_iff _).1 (g2_indexTwo.mem_of_map_mem_ext h3)
      exact hi i' hi'.symm
    · exfalso
      have hn : (g2_indexTwo.ext u33Data.T u33Phi'_T).Normal := Subgroup.normalizer_eq_top_iff.1 h
      have hbot := g2_indexTwo.eq_bot_of_normal u33Extra _ hn
        (g2_indexTwo.isPGroup_ext u33Phi'_T u33Extra.syl.1)
      have hρ : g2E8Rho ∈ g2_indexTwo.ext u33Data.T u33Phi'_T :=
        g2_indexTwo.rho_mem_ext u33Phi'_T
      rw [hbot] at hρ
      exact g2_indexTwo.rho_not_mem ⟨1, by rw [map_one, (Subgroup.mem_bot.1 hρ)]⟩

theorem g2L_S
    : g2AmalL.S = g2_indexTwo.ext u33Data.T u33Phi'_T := rfl

theorem g2L_P₁
    : g2AmalL.P₁ = g2_indexTwo.ext u33Data.A u33Phi'_A := rfl

theorem g2L_P₂
    : g2AmalL.P₂ = g2_indexTwo.ext u33Data.B u33Phi'_B := rfl

theorem center_u33G'
    : Subgroup.center U33G = ⊥ := by
  have := isSimpleGroup_u33Pres
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center U33G) with h1 | h1
  · exact h1
  · exfalso
    obtain ⟨x, y, hxy⟩ := u33J_nonabelian
    have hx : u33ToJ.symm x ∈ Subgroup.center U33G := by rw [h1]; trivial
    apply hxy
    have := Subgroup.mem_center_iff.1 hx (u33ToJ.symm y)
    have h2 := congrArg u33ToJ this
    simpa using h2.symm

theorem g2_normal_range
    : g2F.range.Normal :=
  Subgroup.normal_of_index_eq_two g2_indexTwo.index_range

noncomputable def g2E8Action
    : G2P →* MulAut U33G :=
  haveI := g2_normal_range
  (MulAut.congr (MonoidHom.ofInjective g2_indexTwo.inj).symm).toMonoidHom.comp MulAut.conjNormal

theorem g2F_action
    (c : G2P) (x : U33G) : g2F (g2E8Action c x) = c * g2F x * c⁻¹ := by
  have := g2_normal_range
  simp [g2E8Action, MulAut.congr_apply, MonoidHom.apply_ofInjective_symm,
    MulAut.conjNormal_apply, MonoidHom.ofInjective_apply]

theorem g2E8Action_injective
    : Function.Injective g2E8Action := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro c hc
  rw [MonoidHom.mem_ker] at hc
  have hcomm : ∀ x : U33G, c * g2F x = g2F x * c := by
    intro x
    have h := g2F_action c x
    rw [hc, MulAut.one_apply] at h
    calc c * g2F x = (c * g2F x * c⁻¹) * c := by group
      _ = g2F x * c := by rw [← h]
  have D := g2_indexTwo
  rcases D.cover c with ⟨r, hr⟩ | ⟨r, hr⟩
  · have hcen : r ∈ Subgroup.center U33G := by
      rw [Subgroup.mem_center_iff]
      intro y
      apply D.inj
      rw [map_mul, map_mul, hr]
      exact (hcomm y).symm
    rw [center_u33G'] at hcen
    rw [Subgroup.mem_bot.1 hcen, map_one] at hr
    exact Subgroup.mem_bot.2 hr.symm
  · exfalso
    apply u33Phi'_not_inner
    refine ⟨r⁻¹, fun x => ?_⟩
    apply D.inj
    have hρ : g2E8Rho * g2E8Rho = 1 := D.sq
    have hc : c = g2F r * g2E8Rho := by
      calc c = c * (g2E8Rho * g2E8Rho) := by rw [hρ, mul_one]
        _ = g2F r * g2E8Rho := by rw [← mul_assoc, hr]
    have h1 := hcomm x
    rw [hc] at h1
    have h3 : g2E8Rho * g2F x * (g2E8Rho)⁻¹ = g2F (u33Phi' x) := D.conj x
    calc g2F (u33Phi' x) = g2E8Rho * g2F x * (g2E8Rho)⁻¹ := h3.symm
      _ = (g2F r)⁻¹ * (g2F r * g2E8Rho * g2F x) * (g2E8Rho)⁻¹ := by group
      _ = (g2F r)⁻¹ * (g2F x * (g2F r * g2E8Rho)) * (g2E8Rho)⁻¹ := by rw [h1]
      _ = g2F (r⁻¹ * x * r⁻¹⁻¹) := by
          simp only [map_mul, map_inv]
          group

theorem card_g2P
    : Nat.card G2P = 12096 := by
  have D := g2_indexTwo
  have h1 := Subgroup.card_mul_index g2F.range
  rw [D.index_range] at h1
  have h3 : Nat.card g2F.range = 6048 := by
    rw [← card_u33Pres]
    exact (Nat.card_congr (MonoidHom.ofInjective D.inj).toEquiv).symm
  omega

theorem g2E8Action_bijective
    : Function.Bijective g2E8Action := by
  have : Finite U33G := u33Pres_finite_card_le.1
  refine g2E8Action_injective.bijective_of_nat_card_le ?_
  rw [card_g2P]
  exact card_mulAut_u33Pres_le

theorem g2P_mulEquiv_aut
    : Nonempty (G2P ≃* MulAut (PSU3 3 1)) := by
  obtain ⟨e⟩ := u33Pres_mulEquiv_PSU3
  exact ⟨(MulEquiv.ofBijective g2E8Action g2E8Action_bijective).trans (MulAut.congr e)⟩

end CFSG.Quasithin
