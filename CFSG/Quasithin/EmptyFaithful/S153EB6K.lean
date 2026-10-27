module

public import CFSG.Quasithin.EmptyFaithful.S153E58C
public import CFSG.Quasithin.Background.B4Models

public section

namespace CFSG.Quasithin

namespace S153EB6

open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open CFSG.Open hiding StatedSL

theorem realizesVia_of_equiv {V : Type*} [CommGroup V] {Γ : Type} [Group Γ] {A : Type} [CommGroup A]
    (act : Γ → A → A) (hact1 : ∀ γ, act γ 1 = 1) {H : Subgroup (MulAut V)} {U : Subgroup V}
    (π : Γ →* ↥H) (hπ : Function.Surjective π) (hHU : ∀ h : ↥H, ∀ u ∈ U, (h : MulAut V) u ∈ U)
    (e : ↥U ≃* A)
    (he : ∀ (γ : Γ) (u : ↥U) (hu : ((π γ : ↥H) : MulAut V) (u : V) ∈ U),
      e ⟨((π γ : ↥H) : MulAut V) (u : V), hu⟩ = act γ (e u)) :
    (FFModel.mk Γ A act ⊤ ⊥).RealizesVia H U ⊥ π := by
  refine ⟨hπ, bot_le, bot_le, hHU, ?_, fun _ _ _ => trivial, ?_, ?_⟩
  · intro h z hz
    rw [Subgroup.mem_bot] at hz ⊢
    rw [hz, map_one]
  · intro γ m hm
    change m ∈ (⊥ : Subgroup A) at hm
    change act γ m ∈ (⊥ : Subgroup A)
    rw [Subgroup.mem_bot] at hm ⊢
    rw [hm, hact1]
  · let β : ↥U →* ↥(⊤ : Subgroup A) ⧸ (⊥ : Subgroup A).subgroupOf ⊤ :=
      (QuotientGroup.mk' _).comp (Subgroup.topEquiv.symm.toMonoidHom.comp e.toMonoidHom)
    have hβ : ∀ u : ↥U,
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
      refine ⟨e.symm m, ?_⟩
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
        have hu1 : u = 1 := Subtype.ext h
        apply Subtype.ext
        simp [hu1]
    · intro γ u m hu hm hum
      rw [hβ] at hum ⊢
      have hm' := hinj _ _ hum
      congr 1
      apply Subtype.ext
      change e ⟨((π γ : ↥H) : MulAut V) (u : V), hu⟩ = act γ (m : A)
      rw [he, ← hm']
      rfl

theorem realizes_of_top {W : Type} [CommGroup W] [Finite W] {K : Subgroup (MulAut W)} {W₁ : Subgroup W}
    (hexp : ∀ w : W, w ^ 2 = 1) (hKW : ∀ k ∈ K, ∀ u ∈ W₁, k u ∈ W₁)
    (hcard : Nat.card ↥W₁ = 8) (ρ : ↥K →* MulAut ↥W₁)
    (hρ : ∀ (k : ↥K) (u : ↥W₁), ((ρ k u : ↥W₁) : W) = (k : MulAut W) (u : W))
    (hinj : Function.Injective ρ) (hsurj : Function.Surjective ρ) :
    ∃ π : ↥(StatedSL 3 (ZMod 2)) →* ↥K,
      (FFModel.nat (StatedSL 3 (ZMod 2))).RealizesVia K W₁ ⊥ π := by
  have hexp₁ : ∀ w : ↥W₁, w ^ 2 = 1 := fun w => Subtype.ext (hexp w)
  obtain ⟨e⟩ := S153E58.nonempty_mulEquiv_pi_of_sq_eq_one hexp₁ (d := 3) (by rw [hcard]; norm_num)
  let Θ : MulAut ↥W₁ ≃* GL (Fin 3) (ZMod 2) := (MulAut.congr e).trans (S153E58.mulAutPiEquivGL 3)
  let ρe : ↥K ≃* MulAut ↥W₁ := MulEquiv.ofBijective ρ ⟨hinj, hsurj⟩
  let π : ↥(StatedSL 3 (ZMod 2)) →* ↥K :=
    ρe.symm.toMonoidHom.comp (Θ.symm.toMonoidHom.comp (StatedSL 3 (ZMod 2)).subtype)
  have hπ : Function.Surjective π := by
    intro k
    refine ⟨⟨Θ (ρ k), S153E58.mem_statedSL_three_two _⟩, ?_⟩
    show ρe.symm (Θ.symm (Θ (ρ k))) = k
    rw [MulEquiv.symm_apply_apply]
    exact ρe.symm_apply_apply k
  refine ⟨π, ?_⟩
  refine realizesVia_of_equiv (natAct (StatedSL 3 (ZMod 2))) ?_ π hπ
    (fun h u hu => hKW _ h.2 u hu) e ?_
  · intro γ
    show Multiplicative.ofAdd (((γ : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec
      (Multiplicative.toAdd (1 : Multiplicative (Fin 3 → ZMod 2)))) = 1
    simp
  · intro γ u hu
    have hk : ρ (π γ) = Θ.symm (γ : GL (Fin 3) (ZMod 2)) := by
      show ρ (ρe.symm (Θ.symm (γ : GL (Fin 3) (ZMod 2)))) = _
      exact ρe.apply_symm_apply _
    have hval : (⟨(π γ : MulAut W) (u : W), hu⟩ : ↥W₁) = ρ (π γ) u :=
      Subtype.ext (hρ (π γ) u).symm
    rw [hval, hk]
    set φ : MulAut (Multiplicative (Fin 3 → ZMod 2)) :=
      (S153E58.mulAutPiEquivGL 3).symm (γ : GL (Fin 3) (ZMod 2)) with hφ
    have hΘ : Θ.symm (γ : GL (Fin 3) (ZMod 2)) = (MulAut.congr e).symm φ := rfl
    rw [hΘ]
    have h1 : e (((MulAut.congr e).symm φ) u) = φ (e u) := by
      simp
    refine h1.trans ?_
    rw [hφ, S153E58.mulAutPiEquivGL_symm_apply]
    rfl

end S153EB6

end CFSG.Quasithin
