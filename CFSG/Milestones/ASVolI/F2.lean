module

public import CFSG.Quasithin.Background.F2Inner

public section

namespace CFSG.ASVolI.ChF

open CFSG.Quasithin CFSG.Quasithin.Amalgam CFSG.Quasithin.Amalgam.Completion

abbrev HypF_2_10 (D : Type) [Preorder D] (Y : Type) [Group Y] : Type := XYSetting D Y

end CFSG.ASVolI.ChF

namespace CFSG.ASVolI

open CFSG.Quasithin CFSG.Quasithin.Amalgam CFSG.Quasithin.Amalgam.Completion
open CFSG.ASVolI.ChF

@[expose] def F_2_2 : Prop :=
  ∀ (D : Type) [Preorder D] (α : Amalgam.{0, 0} D) (G : Type) [Group G]
    (μ : Amalgam.Completion α G),
    ∃! f : gp α →* G, ∀ (d : D) (x : α.X d), f (ξ α d x) = μ.toHom d x

theorem as_F_2_2 : F_2_2 := by
  unfold F_2_2
  intro D _ α G _ μ
  exact ⟨μ.hat, fun d x => hat_ξ μ d x, fun ψ hψ => hat_unique μ ψ hψ⟩

@[expose] def F_2_4 : Prop :=
  ∀ (D : Type) [Preorder D] (α : Amalgam.{0, 0} D) (G H : Type) [Group G] [Group H]
    (μ : Amalgam.Completion α G) (η : Amalgam.Completion α H),
    (∀ φ : G ≃* H, (∀ (d : D) (x : α.X d), φ (μ.toHom d x) = η.toHom d x) ↔
      φ.toMonoidHom.comp μ.hat = η.hat) ∧
    (IsEquivalent μ η ↔ μ.hat.ker = η.hat.ker)

theorem as_F_2_4 : F_2_4 := by
  unfold F_2_4
  intro D _ α G H _ _ μ η
  exact ⟨fun φ => equiv_iff_comp_hat μ η φ, isEquivalent_iff_ker_hat_eq μ η⟩

@[expose] def F_2_5 : Prop :=
  ∀ (D : Type) [Preorder D] (α : Amalgam.{0, 0} D) (G H : Type) [Group G] [Group H]
    (a b : Aut α) (μ : Amalgam.Completion α G) (η : Amalgam.Completion α H),
    act 1 μ = μ ∧ act (a * b) μ = act a (act b μ) ∧ act a⁻¹ (act a μ) = μ ∧
    (∀ (d : D) (x : α.X d), (act a μ).toHom d x = μ.toHom d ((a⁻¹).1 d x)) ∧
    (IsEquivalent μ η → IsEquivalent (act a μ) (act a η))

theorem as_F_2_5 : F_2_5 := by
  unfold F_2_5
  intro D _ α G H _ _ a b μ η
  exact ⟨act_one μ, act_mul a b μ, act_inv_act a μ, fun d x => act_apply a μ d x,
    fun h => h.act a⟩

@[expose] def F_2_6_sameAmalgam : Prop :=
  ∀ (D : Type) [Preorder D] (α : Amalgam.{0, 0} D) (G H : Type) [Group G] [Group H]
    (μ : Amalgam.Completion α G) (η : Amalgam.Completion α H),
    IsQuasiEquivalent μ η ↔ ∃ a : Aut α, IsEquivalent (act a μ) η

@[expose] def F_2_6 : Prop :=
  (∀ (D : Type) [Preorder D] (α γ : Amalgam.{0, 0} D) (G H : Type) [Group G] [Group H]
    (μ : Amalgam.Completion α G) (η : Amalgam.Completion γ H),
    IsQuasiEquivalent μ η ↔
      ∃ (φ : G ≃* H) (ψ : Iso α γ),
        ∀ (d : D) (x : α.X d), φ (μ.toHom d x) = η.toHom d (ψ.toEquiv d x)) ∧
    F_2_6_sameAmalgam

theorem as_F_2_6 : F_2_6 := by
  unfold F_2_6 F_2_6_sameAmalgam
  refine ⟨?_, ?_⟩
  · intro D _ α γ G H _ _ μ η
    exact Iff.rfl
  · intro D _ α G H _ _ μ η
    exact isQuasiEquivalent_iff_exists_act μ η

@[expose] def F_2_7 : Prop :=
  ∀ (D : Type) [Preorder D] (α : Amalgam.{0, 0} D),
    (∀ a : Aut α, ∃! f : gp α →* gp α, ∀ (d : D) (x : α.X d), f (ξ α d x) = ξ α d (a.1 d x)) ∧
    (∀ a b : Aut α, hatPiHom (a * b) = (hatPiHom a).comp (hatPiHom b)) ∧
    hatPiHom (1 : Aut α) = MonoidHom.id (gp α) ∧
    (∀ a : Aut α, (hatPiHom a⁻¹).comp (hatPiHom a) = MonoidHom.id (gp α) ∧
      (hatPiHom a).comp (hatPiHom a⁻¹) = MonoidHom.id (gp α)) ∧
    (∀ (a : Aut α) (g : gp α), hatPi a g = hatPiHom a g)

theorem as_F_2_7 : F_2_7 := by
  unfold F_2_7
  intro D _ α
  refine ⟨fun a => ⟨hatPiHom a, fun d x => hatPiHom_ξ a d x,
    fun ψ hψ => hom_ext fun d x => (hψ d x).trans (hatPiHom_ξ a d x).symm⟩,
    fun a b => hatPiHom_mul a b, hatPiHom_one, fun a => ⟨?_, ?_⟩, fun a g => hatPi_apply a g⟩
  · rw [← hatPiHom_mul, inv_mul_cancel, hatPiHom_one]
  · rw [← hatPiHom_mul, mul_inv_cancel, hatPiHom_one]

@[expose] def F_2_8 : Prop :=
  ∀ (D : Type) [Preorder D] (α : Amalgam.{0, 0} D) (G : Type) [Group G]
    (μ : Amalgam.Completion α G) (a : Aut α),
    (act a μ).hat = μ.hat.comp (hatPi a⁻¹).toMonoidHom ∧
    (act a μ).hat.ker = μ.hat.ker.map (hatPi a).toMonoidHom ∧
    (IsEquivalent (act a μ) μ ↔ μ.hat.ker.map (hatPi a).toMonoidHom = μ.hat.ker) ∧
    (∀ h : a ∈ stabilizer μ,
      (∀ g : gp α, aPlus μ a h (QuotientGroup.mk g) = QuotientGroup.mk (hatPi a g)) ∧
      (∀ (d : D) (x : α.X d),
        aPlus μ a h (QuotientGroup.mk (ξ α d x)) = QuotientGroup.mk (ξ α d (a.1 d x))) ∧
      (∀ g : G, aMinus μ a h g = μ.plus (aPlus μ a h (μ.plus.symm g))) ∧
      (∀ (d : D) (x : α.X d), aMinus μ a h (μ.toHom d x) = μ.toHom d (a.1 d x)) ∧
      piMinus μ ⟨a, h⟩ = aMinus μ a h) ∧
    (∀ a b : stabilizer μ, piMinus μ (a * b) = piMinus μ a * piMinus μ b) ∧
    (∀ hμ : μ.IsFaithful,
      (∀ b : normAut μ, sigma μ hμ b ∈ stabilizer μ ∧
        IsEquivalent (act (sigma μ hμ b) μ) μ) ∧
      (∀ (b : normAut μ) (d : D) (x : α.X d),
        μ.toHom d ((sigma μ hμ b).1 d x) = b.1 (μ.toHom d x)) ∧
      (∀ b c : normAut μ, sigma μ hμ (b * c) =
        sigma μ hμ b * sigma μ hμ c) ∧
      (∀ c : stabilizer μ, piMinus μ c ∈ normAut μ) ∧
      (∀ (b : normAut μ) (h : sigma μ hμ b ∈ stabilizer μ),
        piMinus μ ⟨sigma μ hμ b, h⟩ = b.1) ∧
      (∀ (c : stabilizer μ) (h : piMinus μ c ∈ normAut μ),
        sigma μ hμ ⟨piMinus μ c, h⟩ = c.1) ∧
      (sigma μ hμ).range = stabilizer μ)

theorem as_F_2_8 : F_2_8 := by
  unfold F_2_8
  intro D _ α G _ μ a
  refine ⟨hat_act a μ, ker_hat_act a μ, isEquivalent_act_iff a μ, ?_, ?_, ?_⟩
  · intro h
    have he : (μ.plus.symm.trans ((aPlus μ a h).trans μ.plus) : MulAut G) = aMinus μ a h := by
      refine (eq_aMinus_iff μ a h _).mpr fun d x => ?_
      have h1 : μ.plus.symm (μ.toHom d x) = QuotientGroup.mk (ξ α d x) := by
        rw [MulEquiv.symm_apply_eq]
        exact (hat_ξ μ d x).symm
      rw [MulEquiv.trans_apply, MulEquiv.trans_apply, h1, aPlus_mk_ξ, plus_mk, hat_ξ]
    refine ⟨fun g => aPlus_mk μ a h g, fun d x => aPlus_mk_ξ μ a h d x, ?_,
      fun d x => aMinus_apply μ a h d x, ?_⟩
    · intro g
      rw [← he, MulEquiv.trans_apply, MulEquiv.trans_apply]
    · exact (eq_aMinus_iff μ a h (piMinus μ ⟨a, h⟩)).mpr fun d x => piMinus_apply μ ⟨a, h⟩ d x
  · intro c d
    exact map_mul (piMinus μ) c d
  · intro hμ
    refine ⟨fun b => ⟨sigma_mem_stabilizer μ hμ b, mem_stabilizer.mp (sigma_mem_stabilizer μ hμ b)⟩,
      fun b d x => ((piMinus_apply μ ⟨sigma μ hμ b, sigma_mem_stabilizer μ hμ b⟩ d x).symm.trans
        (congrArg (fun φ : MulAut G => φ (μ.toHom d x)) (piMinus_sigma μ hμ b))),
      fun b c => map_mul (sigma μ hμ) b c,
      fun c => piMinus_mem_normAut μ c, fun b _ => piMinus_sigma μ hμ b,
      fun c _ => sigma_piMinus μ hμ c, range_sigma μ hμ⟩

@[expose] def F_2_9 : Prop :=
  ∀ (D : Type) [Preorder D] (Y : Type) [Group Y] (Yd : D → Subgroup Y) (hY : Monotone Yd),
    (⨆ d, Yd d) = ⊤ →
      ∃ η : Amalgam.Completion (ofSubgroups Yd hY) Y, η.IsFaithful ∧
        ∀ d, η.toHom d = (Yd d).subtype

theorem as_F_2_9 : F_2_9 := by
  unfold F_2_9
  intro D _ Y _ Yd hY hgen
  refine ⟨⟨fun d => (Yd d).subtype, fun {d e} h x => rfl, ?_⟩, ?_, fun d => rfl⟩
  · simpa only [Subgroup.range_subtype] using hgen
  · intro d
    exact (Yd d).subtype_injective

@[expose] def F_2_10 : Prop :=
  ∀ (D : Type) [Preorder D] (Y : Type) [Group Y] (S : HypF_2_10 D Y),
    (∀ (y : S.Yd S.least) (d : D) (x : S.Xd d),
      (((S.cAut y).1 d x : S.Xd d) : Y) = (y : Y) * (x : Y) * (y : Y)⁻¹) ∧
    (S.cAut 1 = 1 ∧ ∀ y y' : S.Yd S.least, S.cAut (y * y') = S.cAut y * S.cAut y') ∧
    (∀ y : S.Yd S.least, S.cAut y = 1 ↔
      ∀ (d : D) (x : Y), x ∈ S.Xd d → (y : Y) * x * (y : Y)⁻¹ = x) ∧
    (∀ x : S.Xd S.least,
      hatPi (S.cAut ⟨x, S.le _ x.2⟩) = MulAut.conj (ξ S.alpha S.least x)) ∧
    (∀ (G : Type) [Group G] (μ : Amalgam.Completion S.alpha G) (x : S.Xd S.least),
      S.cAut ⟨x, S.le _ x.2⟩ ∈ stabilizer μ) ∧
    (∀ (G : Type) [Group G] (μ : Amalgam.Completion S.alpha G), μ.IsFaithful →
      ∀ (x : S.Xd S.least) (h : S.cAut ⟨x, S.le _ x.2⟩ ∈ stabilizer μ),
        piMinus μ ⟨S.cAut ⟨x, S.le _ x.2⟩, h⟩ = MulAut.conj (μ.toHom S.least x))

theorem as_F_2_10 : F_2_10 := by
  unfold F_2_10
  intro D _ Y _ S
  refine ⟨fun y d x => S.cAut_apply_coe y d x, ⟨map_one S.c, fun y y' => map_mul S.c y y'⟩, ?_,
    fun x => S.hatPi_c x, fun G _ μ x => S.c_mem_stabilizer μ x,
    fun G _ μ _ x _ => S.piMinus_c μ x⟩
  intro y
  constructor
  · intro h d x hx
    exact congrArg (fun a : Aut S.alpha => ((a.1 d ⟨x, hx⟩ : S.Xd d) : Y)) h
  · intro h
    apply Subtype.ext
    funext d
    apply MulEquiv.ext
    intro x
    apply Subtype.ext
    exact h d x.1 x.2

@[expose] def F_2_11 : Prop :=
  ∀ (D : Type) [Preorder D] (Y : Type) [Group Y] (S : HypF_2_10 D Y) (G : Type) [Group G]
    (μ : Amalgam.Completion S.alpha G) (h : S.Hyp211 μ),
    (∃ η : Amalgam.Completion S.gamma ↥h.G0,
      (∀ (d : D) (y : S.Yd S.least) (x : S.Xd d) (g : S.Yd d), (y : Y) * (x : Y) = (g : Y) →
        ((η.toHom d g : ↥h.G0) : MulAut G) = h.piC y * MulAut.conj (μ.toHom d x)) ∧
      (∀ (d : D) (x : S.Xd d),
        ((η.toHom d ⟨x, S.le d x.2⟩ : ↥h.G0) : MulAut G) = MulAut.conj (μ.toHom d x)) ∧
      (((∀ d, ∀ g ∈ S.Yd d, g ∈ Subgroup.centralizer (S.Xd d : Set Y) → g ∈ S.Xd d) ∧
          (∀ (d : D) (x : S.Xd d), μ.toHom d x ∈ Subgroup.center G → x = 1)) →
        η.IsFaithful) ∧
    (∃ η' : Amalgam.Completion S.alpha ↥(MulAut.conj : G →* MulAut G).range,
      (∀ (d : D) (x : S.Xd d),
        ((η.toHom d ⟨x, S.le d x.2⟩ : ↥h.G0) : MulAut G) =
          ((η'.toHom d x : ↥(MulAut.conj : G →* MulAut G).range) : MulAut G)) ∧
      (∀ (d : D) (x : S.Xd d), ((η'.toHom d x : ↥(MulAut.conj : G →* MulAut G).range) : MulAut G) =
        MulAut.conj (μ.toHom d x)) ∧
      (η'.IsFaithful ↔ ∀ (d : D) (x : S.Xd d), μ.toHom d x ∈ Subgroup.center G → x = 1) ∧
      (Subgroup.center G = ⊥ → IsEquivalent μ η')))

theorem as_F_2_11 : F_2_11 := by
  unfold F_2_11
  intro D _ Y _ S G _ μ h
  let η : Amalgam.Completion S.gamma h.G0 :=
    { toHom := fun d => (h.eta d).codRestrict h.G0 (h.eta_mem_G0 d)
      comm := fun {_ _} hd g => Subtype.ext (h.eta_map hd g)
      gen := by
        refine Subgroup.map_injective (f := h.G0.subtype) h.G0.subtype_injective ?_
        rw [Subgroup.map_iSup, Subgroup.map_top, Subgroup.range_subtype]
        simp only [MonoidHom.map_range]
        exact h.range_iSup_eta }
  refine ⟨η, ?_, ?_, ?_, μ.innComp, ?_, ?_, ?_, ?_⟩
  · intro d y x g hg
    exact (h.eta_apply d g).trans (h.etaFun_eq d g y x hg)
  · intro d x
    exact h.eta_apply_X d x
  · rintro ⟨hC, hZ⟩ d g g' hgg'
    exact h.eta_injective hC hZ d (show h.eta d g = h.eta d g' from congrArg Subtype.val hgg')
  · intro d x
    exact (h.eta_apply_X d x).trans (μ.innComp_apply d x).symm
  · intro d x
    exact μ.innComp_apply d x
  · exact μ.innComp_injective_iff
  · intro hZ
    exact μ.isEquivalent_innComp hZ

end CFSG.ASVolI
