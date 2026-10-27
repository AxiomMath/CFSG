module

public import CFSG.Quasithin.Background.H153Sp
public import CFSG.Quasithin.Background.H156Tr

public section

open scoped Pointwise

namespace CFSG.Quasithin.H153

open CFSG.ASVolI.ChH CFSG.Open CFSG.Monster.Code CFSG.Quasithin CFSG.Quasithin.H.Mathieu
  CFSG.Quasithin.H.Coc24 CFSG.Quasithin.H.ModChk CFSG.Quasithin.H156 CFSG.Quasithin.H.ZTrans
  CFSG.Quasithin.H

theorem rk_of_card {W : Type*} [Group W] {k : ℕ} (h : Nat.card W = 2 ^ k) : rk W = k := by
  unfold rk
  rw [h]
  exact padicValNat.prime_pow k

theorem chief_of_map' {V W : Type*} [CommGroup V] [CommGroup W] (eg : V ≃* W)
    {G : Subgroup (MulAut V)} {X Y : Subgroup V} {G' : Subgroup (MulAut W)} {X' Y' : Subgroup W}
    (hG : G.map (congrHom eg) = G') (hX : X.map eg.toMonoidHom = X')
    (hY : Y.map eg.toMonoidHom = Y') (h : IsChiefFactorUnder (actsOnModule G') X' Y') :
    IsChiefFactorUnder (actsOnModule G) X Y := by
  subst hG hX hY
  exact chief_of_map eg h

theorem fullTransp_of_map' {V W : Type*} [CommGroup V] [CommGroup W] (eg : V ≃* W)
    {G X : Subgroup (MulAut V)} {A V₁ : Subgroup V} {G' X' : Subgroup (MulAut W)}
    {A' V₁' : Subgroup W} (hG : G.map (congrHom eg) = G') (hX : X.map (congrHom eg) = X')
    (hA : A.map eg.toMonoidHom = A') (hV : V₁.map eg.toMonoidHom = V₁')
    (h : FullTranspCenter' G' X' A' V₁') : FullTranspCenter' G X A V₁ := by
  subst hG hX hA hV
  exact fullTransp_of_map eg h

theorem xiSub_eq_top_of_map' {V W : Type*} [CommGroup V] [CommGroup W] (eg : V ≃* W)
    {A : Subgroup (MulAut V)} {A' : Subgroup (MulAut W)} (hA : A.map (congrHom eg) = A')
    (h : xiSub A' = ⊤) : xiSub A = ⊤ := by
  subst hA
  exact xiSub_eq_top_of_map eg h

theorem chief_bot_V1_std :
    IsChiefFactorUnder (actsOnModule (img11 (MY M24g S0))) ⊥ (Subgroup.zpowers z0) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine lt_of_le_of_ne bot_le fun h => z0_ne_one ?_
    have : z0 ∈ Subgroup.zpowers z0 := Subgroup.mem_zpowers _
    rw [← h] at this
    exact this
  · rintro f ⟨g, hg, rfl⟩ u hu
    rw [Subgroup.mem_bot] at hu ⊢
    rw [hu]
    exact MulEquiv.map_one g
  · rintro f ⟨g, hg, rfl⟩ u hu
    exact map_mem_zpowers_z0 (HS_fix_z0 hg) hu
  · intro Y h1 h2 hY
    by_cases hY1 : Y = ⊥
    · exact Or.inl hY1
    · right
      obtain ⟨⟨u, huY⟩, hu1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hY1
      have hu : u ∈ Subgroup.zpowers z0 := h2 huY
      rcases eq_one_or_of_mem_zpowers z0_mul_self hu with h | h
      · exact absurd (Subtype.ext h) hu1
      · rw [h] at huY
        exact le_antisymm h2 ((Subgroup.zpowers_le).2 huY)

@[expose] def Conc153 {V : Type} [CommGroup V] (ρ : ↥M24g →* MulAut V) (V₇ : Subgroup V) : Prop :=
  IsChiefFactorUnder (actsOnModule (rImg ρ (MY M24g S0))) ⊥ (fixV (rImg ρ (KY M24g S0))) ∧
  rk ↥(fixV (rImg ρ (KY M24g S0))) = 1 ∧
  IsChiefFactorUnder (actsOnModule (rImg ρ (MY M24g S0))) (fixV (rImg ρ (KY M24g S0))) V₇ ∧
  IsChiefFactorUnder (actsOnModule (rImg ρ (MY M24g S0))) V₇ ⊤ ∧
  rk ↥V₇ = 1 + 6 ∧
  IsDualOfConj' ρ (MY M24g S0) V₇ (fixV (rImg ρ (KY M24g S0))) (KY M24g S0) ∧
  (∃ N : Subgroup S24, IsO23' (MY M24g S0) N ∧
    (∃ π : ↥(MY M24g S0) →* Equiv.Perm (Fin 6), Function.Surjective π ∧
      π.ker = N.subgroupOf (MY M24g S0)) ∧
    (∀ g : ↥M24g, (g : S24) ∈ MY M24g S0 → ((∀ x : V, ρ g x * x⁻¹ ∈ V₇) ↔ (g : S24) ∈ N)) ∧
    InducesOn (rImg ρ (MY M24g S0)) ⊤ V₇ (Multiplicative (Fin 2 ⊕ Fin 2 → ZMod 2))
      (natSubI' (Fin 2 ⊕ Fin 2) (ZMod 2) (CFSG.Open.StatedSp 2 (ZMod 2)))) ∧
  FullTranspCenter' (rImg ρ (MY M24g S0)) (rImg ρ (KY M24g S0)) V₇
    (fixV (rImg ρ (KY M24g S0))) ∧
  xiSub (rImg ρ (KY M24g S0)) = ⊤ ∧
  (∀ x : V, x ∈ V₇ ↔ ∀ g ∈ rImg ρ (KY M24g S0), g x * x⁻¹ ∈ fixV (rImg ρ (KY M24g S0)))

theorem h153_std
    {V : Type} [CommGroup V] (ρ : ↥M24g →* MulAut V)
    (e : V ≃* W11)
    (hc : ∀ (γ : ↥M24g) (v : V), e (ρ γ v) = rho11 AutPerm le_rfl γ (e v)) :
    ∃ (V₇ : Subgroup V) (z : V), e z = z0 ∧ fixV (rImg ρ (KY M24g S0)) = Subgroup.zpowers z ∧
      Conc153 ρ V₇ := by
  have hKY : KY M24g S0 = KSp := pCoreOf_MY0
  have hcg : ∀ γ : ↥M24g, congrHom e (ρ γ) = rho11 AutPerm le_rfl γ := fun γ =>
    MulEquiv.ext fun w =>
      (congrHom_apply e (ρ γ) w).trans ((hc γ _).trans (congrArg _ (e.apply_symm_apply w)))
  have hmapR : ∀ A : Subgroup S24, A ≤ AutPerm →
      (rImg ρ A).map (congrHom e) = img11 A := by
    intro A hA
    show ((A.subgroupOf M24g).map ρ).map (congrHom e) =
      (A.subgroupOf AutPerm).map (rho11 AutPerm le_rfl)
    rw [Subgroup.map_map]
    have : (congrHom e).comp ρ = rho11 AutPerm le_rfl := MonoidHom.ext hcg
    rw [this]
    rfl
  have hG : (rImg ρ (MY M24g S0)).map (congrHom e) = img11 (MY M24g S0) :=
    hmapR _ MY0_le_autPerm
  have hK : (rImg ρ (KY M24g S0)).map (congrHom e) = img11 KSp := by
    rw [hKY]
    exact hmapR _ KSp_le_autPerm
  set z : V := e.symm z0 with hz
  have hez : e z = z0 := e.apply_symm_apply z0
  have hV1map : (fixV (rImg ρ (KY M24g S0))).map e.toMonoidHom = Subgroup.zpowers z0 :=
    ((fixV_map_congrHom e _).symm.trans (congrArg fixV hK)).trans fixV_KS
  have hzp : (Subgroup.zpowers z).map e.toMonoidHom = Subgroup.zpowers z0 :=
    (MonoidHom.map_zpowers e.toMonoidHom z).trans (congrArg Subgroup.zpowers hez)
  have hV1 : fixV (rImg ρ (KY M24g S0)) = Subgroup.zpowers z :=
    Subgroup.map_injective e.injective (hV1map.trans hzp.symm)
  have hzmem : ∀ c : V, c ∈ Subgroup.zpowers z ↔ e c ∈ Subgroup.zpowers z0 := fun c => by
    rw [← hzp]
    exact (Subgroup.mem_map_iff_mem e.injective).symm
  set V₇ : Subgroup V := W0.comap e.toMonoidHom with hV₇
  have hV7map : V₇.map e.toMonoidHom = W0 :=
    Subgroup.map_comap_eq_self_of_surjective e.surjective W0
  have hV7mem : ∀ x : V, x ∈ V₇ ↔ e x ∈ W0 := fun x => Iff.rfl
  have he_comm : ∀ (k : ↥M24g) (x : V),
      e (ρ k x * x⁻¹) = rho11 AutPerm le_rfl k (e x) * (e x)⁻¹ := fun k x =>
    (map_mul e _ _).trans (congrArg₂ (fun a b => a * b) (hc k x) (map_inv e x))
  have hcomm_img : ∀ (g : MulAut V) (x : V),
      e (g x * x⁻¹) = congrHom e g (e x) * (e x)⁻¹ := fun g x =>
    (map_mul e _ _).trans (congrArg₂ (fun a b => a * b) (congrHom_apply_eg e g x).symm
      (map_inv e x))
  have hcardV1 : Nat.card ↥(fixV (rImg ρ (KY M24g S0))) = 2 ^ 1 := by
    have := Subgroup.card_map_of_injective (f := e.toMonoidHom) e.injective
      (K := fixV (rImg ρ (KY M24g S0)))
    rw [hV1map, card_zpowers_z0] at this
    exact this.symm
  have hcardV7 : Nat.card ↥V₇ = 2 ^ 7 := by
    have := Subgroup.card_map_of_injective (f := e.toMonoidHom) e.injective (K := V₇)
    rw [hV7map, card_W0] at this
    exact this.symm
  have hI4 : InducesOn (rImg ρ (MY M24g S0)) ⊤ V₇ (Multiplicative (Fin 2 ⊕ Fin 2 → ZMod 2))
      (natSubI' (Fin 2 ⊕ Fin 2) (ZMod 2) (CFSG.Open.StatedSp 2 (ZMod 2))) :=
    inducesOn_of_map' e hG (Subgroup.map_top_of_surjective e.toMonoidHom e.surjective) hV7map
      std_ind4
  have hlt : V₇ < ⊤ := lt_of_le_of_ne le_top fun h => W0_ne_top (by
    rw [← hV7map, h, Subgroup.map_top_of_surjective e.toMonoidHom e.surjective])
  have hzz : z * z = 1 := e.injective (by rw [map_mul, hez, z0_mul_self, map_one])
  have hMYfix : ∀ g : ↥M24g, (g : S24) ∈ MY M24g S0 → ρ g z = z := fun g hg =>
    e.injective ((hc g z).trans ((congrArg (rho11 AutPerm le_rfl g) hez).trans
      ((rho11_z0_of_mem (σ := g) hg.2).trans hez.symm)))
  refine ⟨V₇, z, hez, hV1, ?_⟩
  refine ⟨?_, rk_of_card hcardV1, ?_, ?_, rk_of_card hcardV7, ?_, ?_, ?_,
    xiSub_eq_top_of_map' e hK xi_std, ?_⟩
  · exact chief_of_map' e hG (Subgroup.map_bot _) hV1map chief_bot_V1_std
  · exact chief_of_map' e hG hV1map hV7map chief_V1_V7
  · exact chief_of_inducesOn hI4 hlt irred4
  ·
    rw [hV1, hKY]
    refine isDualOfConj_of ρ (MY M24g S0) KSp KSp_le_autPerm KSp_le_MY0 V₇ z hzz hMYfix ?_ ?_ ?_
      (fun g hg k hk => MY0_conj_KSp hg hk)
    · intro k hk x hx
      have h1 : rho11 AutPerm le_rfl k ∈ img11 KSp := ⟨k, Subgroup.mem_subgroupOf.2 hk, rfl⟩
      have h2 := KS_comm_mem h1 hx
      exact (hzmem _).2 ((he_comm k x).symm ▸ h2)
    · intro x hx hxz
      by_contra hno
      push Not at hno
      apply hxz
      refine (hzmem x).2 ?_
      have : e x ∈ fixV (img11 KSp) := by
        intro φ hφ
        obtain ⟨k, hk, rfl⟩ := hφ
        exact ((hc k x).symm.trans (congrArg e (hno k (Subgroup.mem_subgroupOf.1 hk))))
      rwa [fixV_KS] at this
    · intro k hk hk1
      by_contra hno
      push Not at hno
      apply hk1
      have h1 : rho11 AutPerm le_rfl k ∈ img11 KSp := ⟨k, Subgroup.mem_subgroupOf.2 hk, rfl⟩
      have h2 : rho11 AutPerm le_rfl k = 1 := by
        refine KS_faithful h1 fun w hw => ?_
        have hx : e.symm w ∈ V₇ := by
          show e (e.symm w) ∈ W0
          rw [MulEquiv.apply_symm_apply]
          exact hw
        have h3 := hno (e.symm w) hx
        have h4 := hc k (e.symm w)
        rw [h3] at h4
        rw [MulEquiv.apply_symm_apply] at h4
        exact h4.symm
      have h3 : k = 1 := rho11_injective AutPerm le_rfl (h2.trans (map_one _).symm)
      rw [h3]
      rfl
  ·
    refine ⟨N0, isO23_MY0, ⟨piM, piM_surjective, N0_subgroupOf.symm⟩, ?_, hI4⟩
    intro g hg
    rw [← act_trivial_iff hg]
    constructor
    · intro h w
      obtain ⟨x, rfl⟩ := e.surjective w
      have h1 := (hV7mem _).1 (h x)
      rw [he_comm] at h1
      exact h1
    · intro h x
      refine (hV7mem _).2 ?_
      rw [he_comm]
      exact h (e x)
  · exact fullTransp_of_map' e hG hK hV7map hV1map fullTransp_std
  · intro x
    rw [hV7mem, W0_iff]
    constructor
    · intro h g hg
      have hg' : congrHom e g ∈ img11 KSp := by rw [← hK]; exact Subgroup.mem_map_of_mem _ hg
      have h1 := h _ hg'
      rw [hV1]
      refine (hzmem _).2 ?_
      rw [hcomm_img]
      exact h1
    · intro h k hk
      rw [← hK] at hk
      obtain ⟨g, hg, rfl⟩ := hk
      have h1 := h g hg
      rw [hV1] at h1
      have h2 := (hzmem _).1 h1
      rw [hcomm_img] at h2
      exact h2

end CFSG.Quasithin.H153
