module

public import CFSG.Quasithin.Vol2.Ch10SecAElemAb
public import CFSG.Quasithin.Background.B4Models

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecA

open CFSG.Quasithin CFSG.Assembly.LowTwoRank

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem mulAutPiEquivGL_symm_apply (d : ℕ) (γ : GL (Fin d) (ZMod 2))
    (x : Multiplicative (Fin d → ZMod 2)) :
    (mulAutPiEquivGL d).symm γ x =
      Multiplicative.ofAdd ((γ : Matrix (Fin d) (Fin d) (ZMod 2)).mulVec
        (Multiplicative.toAdd x)) := by
  simp [mulAutPiEquivGL, mulAutPiEquivLinearEquiv, LinearMap.GeneralLinearGroup.generalLinearEquiv]

theorem mem_statedSL_three_two (g : GL (Fin 3) (ZMod 2)) : g ∈ StatedSL 3 (ZMod 2) :=
  CFSG.Open.StatedAPI.mem_statedSL_zmod_two g

theorem realizesVia_mk_top {V : Type*} [CommGroup V] {Γ : Type} [Group Γ] {A : Type}
    [CommGroup A] (act : Γ → A → A) (hact1 : ∀ γ, act γ 1 = 1) {H : Subgroup (MulAut V)}
    (π : Γ →* ↥H) (hπ : Function.Surjective π) (e : V ≃* A)
    (he : ∀ γ v, e (((π γ : ↥H) : MulAut V) v) = act γ (e v)) :
    (FFModel.mk Γ A act ⊤ ⊥).RealizesVia H ⊤ ⊥ π := by
  refine ⟨hπ, bot_le, bot_le, fun _ _ _ => trivial, ?_, fun _ _ _ => trivial, ?_, ?_⟩
  · intro h z hz
    rw [Subgroup.mem_bot] at hz ⊢
    rw [hz, map_one]
  · intro γ m hm
    change m ∈ (⊥ : Subgroup A) at hm
    change act γ m ∈ (⊥ : Subgroup A)
    rw [Subgroup.mem_bot] at hm ⊢
    rw [hm, hact1]
  · let β : ↥(⊤ : Subgroup V) →* ↥(⊤ : Subgroup A) ⧸ (⊥ : Subgroup A).subgroupOf ⊤ :=
      (QuotientGroup.mk' _).comp (Subgroup.topEquiv.symm.toMonoidHom.comp
        (e.toMonoidHom.comp Subgroup.topEquiv.toMonoidHom))
    have hβ : ∀ u : ↥(⊤ : Subgroup V),
        β u = ((Subgroup.topEquiv.symm (e u) : ↥(⊤ : Subgroup A)) :
          ↥(⊤ : Subgroup A) ⧸ (⊥ : Subgroup A).subgroupOf ⊤) := fun _ => rfl
    have hinj : ∀ a b : ↥(⊤ : Subgroup A), ((a : ↥(⊤ : Subgroup A) ⧸
        (⊥ : Subgroup A).subgroupOf ⊤) = b) → a = b := by
      intro a b h
      rw [QuotientGroup.eq, Subgroup.bot_subgroupOf, Subgroup.mem_bot] at h
      exact (inv_mul_eq_one.mp h)
    refine ⟨β, ?_, ?_, ?_⟩
    · intro y
      obtain ⟨⟨m, -⟩, rfl⟩ := QuotientGroup.mk_surjective y
      refine ⟨⟨e.symm m, trivial⟩, ?_⟩
      rw [hβ]
      congr 1
      exact Subtype.ext (by simp)
    · intro u
      rw [hβ, QuotientGroup.eq_one_iff, Subgroup.bot_subgroupOf, Subgroup.mem_bot,
        Subgroup.mem_bot]
      constructor
      · intro h
        have h' := congrArg Subtype.val h
        simpa using h'
      · intro h
        apply Subtype.ext
        simp [h]
    · intro γ u m hu hm hum
      rw [hβ] at hum ⊢
      have hm' := hinj _ _ hum
      congr 1
      apply Subtype.ext
      change e (((π γ : ↥H) : MulAut V) u) = act γ (m : A)
      rw [he, ← hm']
      rfl

theorem binaryNaturalSL_three_of_eq_top {W : Type} [CommGroup W] [Finite W]
    (h2 : ∀ w : W, w ^ 2 = 1) (hcard : Nat.card W = 2 ^ 3) {H : Subgroup (MulAut W)}
    (hH : H = ⊤) : BinaryNaturalSL H ⊤ ⊥ 3 1 := by
  obtain ⟨e⟩ := nonempty_mulEquiv_pi_of_sq_eq_one h2 hcard
  set φ : MulAut W ≃* GL (Fin 3) (ZMod 2) := (MulAut.congr e).trans (mulAutPiEquivGL 3)
  let π : ↥(StatedSL 3 (ZMod 2)) →* ↥H :=
    ((φ.symm.toMonoidHom).comp (StatedSL 3 (ZMod 2)).subtype).codRestrict H
      fun _ => hH ▸ Subgroup.mem_top _
  have hπs : Function.Surjective π := fun h =>
    ⟨⟨φ h, mem_statedSL_three_two _⟩, Subtype.ext (φ.symm_apply_apply (h : MulAut W))⟩
  have hπ : ∀ (γ : ↥(StatedSL 3 (ZMod 2))) (u : W),
      e (((π γ : ↥H) : MulAut W) u) = natAct (StatedSL 3 (ZMod 2)) γ (e u) := by
    intro γ u
    simp only [π, φ, MonoidHom.codRestrict_apply, MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom,
      Function.comp_apply, Subgroup.coe_subtype, MulEquiv.symm_trans_apply,
      MulAut.congr_symm_apply, MulEquiv.trans_apply, MulEquiv.apply_symm_apply]
    rw [mulAutPiEquivGL_symm_apply]
    rfl
  exact ⟨ZMod 2, inferInstance, inferInstance, by simp, π,
    realizesVia_mk_top (natAct (StatedSL 3 (ZMod 2))) (fun _ => by simp [natAct]) π hπs e hπ⟩

end CFSG.Quasithin.Vol2.Ch10.SecA
