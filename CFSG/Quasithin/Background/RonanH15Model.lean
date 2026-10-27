module

public import CFSG.Quasithin.Background.HMathieuStatements

public section

namespace CFSG.Quasithin.RonanH15

open CFSG.Quasithin CFSG.Quasithin.H.Mathieu

variable {V : Type*} [CommGroup V]

@[expose] def VecOf (D : FFModel)
    (β : ↥(⊤ : Subgroup V) →* ↥D.sec ⧸ D.ker.subgroupOf D.sec) (e : D.Amb) (v : V) : Prop :=
  ∃ he : e ∈ D.sec, β ⟨v, Subgroup.mem_top v⟩ = QuotientGroup.mk ⟨e, he⟩

section Realization

variable {D : FFModel} {H : Subgroup (MulAut V)} {π : D.Gam →* ↥H}
  {β : ↥(⊤ : Subgroup V) →* ↥D.sec ⧸ D.ker.subgroupOf D.sec}

theorem VecOf.eq_iff (h : RealizesBy D H ⊤ ⊥ π β) {e e' : D.Amb} {v v' : V}
    (hv : VecOf D β e v) (hv' : VecOf D β e' v') : v = v' ↔ e⁻¹ * e' ∈ D.ker := by
  obtain ⟨-, -, -, -, -, -, -, -, hβ1, -⟩ := h
  have hinj : Function.Injective β := by
    refine (injective_iff_map_eq_one β).2 fun a ha => ?_
    exact Subtype.ext (Subgroup.mem_bot.1 ((hβ1 a).1 ha))
  obtain ⟨he, hβv⟩ := hv
  obtain ⟨he', hβv'⟩ := hv'
  have key : v = v' ↔ β ⟨v, Subgroup.mem_top v⟩ = β ⟨v', Subgroup.mem_top v'⟩ :=
    ⟨fun hvv => by subst hvv; rfl, fun hh => congrArg Subtype.val (hinj hh)⟩
  rw [key, hβv, hβv', QuotientGroup.eq, Subgroup.mem_subgroupOf]
  rfl

theorem VecOf.eq_one_iff (h : RealizesBy D H ⊤ ⊥ π β) {e : D.Amb} {v : V}
    (hv : VecOf D β e v) : v = 1 ↔ e ∈ D.ker := by
  obtain ⟨-, -, -, -, -, -, -, -, hβ1, -⟩ := h
  obtain ⟨he, hβv⟩ := hv
  have key : v = 1 ↔ β ⟨v, Subgroup.mem_top v⟩ = 1 := by
    rw [hβ1 ⟨v, Subgroup.mem_top v⟩, Subgroup.mem_bot]
  rw [key, hβv, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]

theorem VecOf.act (h : RealizesBy D H ⊤ ⊥ π β) {e : D.Amb} {v : V} (hv : VecOf D β e v)
    (γ : D.Gam) : VecOf D β (D.act γ e) (((π γ : ↥H) : MulAut V) v) := by
  obtain ⟨-, -, -, -, -, hsec, -, -, -, hβeq⟩ := h
  obtain ⟨he, hβv⟩ := hv
  exact ⟨hsec γ e he, hβeq γ ⟨v, Subgroup.mem_top v⟩ ⟨e, he⟩ (Subgroup.mem_top _) (hsec γ e he) hβv⟩

theorem exists_vecOf (h : RealizesBy D H ⊤ ⊥ π β) {e : D.Amb} (he : e ∈ D.sec) :
    ∃ v : V, VecOf D β e v := by
  obtain ⟨-, -, -, -, -, -, -, hβs, -, -⟩ := h
  obtain ⟨u, hu⟩ := hβs (QuotientGroup.mk ⟨e, he⟩)
  exact ⟨(u : V), he, hu⟩

theorem realizesBy_golaySec_restrict {numer denom : Subgroup (G6.PermMod 24)}
    {Γ Γ' : Subgroup (Equiv.Perm (Fin 24))} (hΓ' : Γ' ≤ Γ) {ρ : ↥Γ →* MulAut V}
    {β : ↥(⊤ : Subgroup V) →* ↥numer ⧸ denom.subgroupOf numer}
    (h : RealizesBy (FFModel.golaySec Γ numer denom) ρ.range ⊤ ⊥ ρ.rangeRestrict β) :
    RealizesBy (FFModel.golaySec Γ' numer denom) (ρ.comp (Subgroup.inclusion hΓ')).range ⊤ ⊥
      (ρ.comp (Subgroup.inclusion hΓ')).rangeRestrict β := by
  obtain ⟨-, -, h3, -, -, h6, h7, h8, h9, h10⟩ := h
  unfold CFSG.Quasithin.H.Mathieu.RealizesBy
  refine ⟨MonoidHom.rangeRestrict_surjective _, bot_le, h3, fun _ _ _ => Subgroup.mem_top _,
    ?_, ?_, ?_, h8, h9, ?_⟩
  · intro x z hz
    rw [Subgroup.mem_bot.1 hz, map_one]
    exact Subgroup.one_mem _
  · intro γ m hm
    exact h6 ⟨Subtype.val γ, hΓ' γ.2⟩ m hm
  · intro γ m hm
    exact h7 ⟨Subtype.val γ, hΓ' γ.2⟩ m hm
  · intro γ u m hu hm hβu
    exact h10 ⟨Subtype.val γ, hΓ' γ.2⟩ u m (Subgroup.mem_top _) hm hβu

end Realization

end CFSG.Quasithin.RonanH15
