module

public import CFSG.Quasithin.H13.VolIAltCoverEight

public section

namespace CFSG.Quasithin.H13.A7.LinCover

open CFSG.Quasithin CFSG.Quasithin.G6 CFSG.Quasithin.H13.VolI Subgroup

@[expose] def restrictHom {Γ X : Type*} [Group Γ] [Group X] (ρ : Γ →* MulAut X)
    (U : Subgroup X) (h : ∀ γ, ∀ u ∈ U, ρ γ u ∈ U) : Γ →* MulAut ↥U where
  toFun γ :=
    { toFun := fun u => ⟨ρ γ u, h γ u u.2⟩
      invFun := fun u => ⟨(ρ γ)⁻¹ u, by simpa [map_inv] using h γ⁻¹ u u.2⟩
      left_inv := fun u => Subtype.ext (by simp)
      right_inv := fun u => Subtype.ext (by simp)
      map_mul' := fun x y => Subtype.ext (by simp) }
  map_one' := MulEquiv.ext fun u => Subtype.ext (by simp)
  map_mul' := fun g g' => MulEquiv.ext fun u => Subtype.ext (by simp)

theorem restrictHom_apply {Γ X : Type*} [Group Γ] [Group X] (ρ : Γ →* MulAut X)
    (U : Subgroup X) (h : ∀ γ, ∀ u ∈ U, ρ γ u ∈ U) (γ : Γ) (u : ↥U) :
    ((restrictHom ρ U h γ u : ↥U) : X) = ρ γ u := rfl

theorem exists_cover_of_realizesVia {V : Type} [CommGroup V] {D : FFModel}
    {L : Subgroup (MulAut V)} {U Z : Subgroup V} {π : D.Gam →* ↥L} (h : D.RealizesVia L U Z π)
    (hZ : Z ≤ fixV L) (hU : XMod.commOf ↥L U = U) :
    ∃ C : ModelCover D ↥U, (∀ γ (u : ↥U), ((C.ρ γ u : ↥U) : V) = ((π γ : ↥L) : MulAut V) u) ∧
      ∀ u : ↥U, C.β u = 1 ↔ (u : V) ∈ Z := by
  obtain ⟨hπs, -, -, hLU, -, -, -, β, hβs, hβk, hβe⟩ := h
  have hinv : ∀ γ, ∀ u ∈ U, (L.subtype.comp π) γ u ∈ U := fun γ u hu => hLU (π γ) u hu
  set ρ := restrictHom (L.subtype.comp π) U hinv with hρ
  have hgen : ∀ v : ↥U, v ∈ closure {x | ∃ γ w, x = ρ γ w * w⁻¹} := by
    intro v
    have hmem : (v : V) ∈ XMod.commOf ↥L U := by rw [hU]; exact v.2
    have hle : XMod.commOf ↥L U ≤ (closure {x | ∃ γ w, x = ρ γ w * w⁻¹}).map U.subtype := by
      refine (closure_le _).2 ?_
      rintro c ⟨a, l, hl, rfl⟩
      obtain ⟨γ, hγ⟩ := hπs a
      refine ⟨ρ γ ⟨l, hl⟩ * (⟨l, hl⟩ : ↥U)⁻¹, subset_closure ⟨γ, ⟨l, hl⟩, rfl⟩, ?_⟩
      simp only [coe_subtype, coe_mul, coe_inv]
      rw [hρ, restrictHom_apply]
      show ((π γ : ↥L) : MulAut V) l * l⁻¹ = a • l * l⁻¹
      rw [hγ]
      rfl
    obtain ⟨y, hy, hyv⟩ := mem_map.1 (hle hmem)
    have : y = v := Subtype.ext hyv
    rwa [← this]
  refine ⟨⟨ρ, β, hβs, fun γ v hv => ?_, fun γ v m hm hvm => hβe γ v m (hinv γ v v.2) hm hvm,
    hgen⟩, fun γ u => rfl, hβk⟩
  apply Subtype.ext
  exact hZ ((hβk v).1 hv) _ (π γ).2

theorem exists_mulEquiv_coreMod_eight {V : Type} [CommGroup V] [Finite V]
    (hV2 : ∀ v : V, v ^ 2 = 1) {L : Subgroup (MulAut V)} {U Z : Subgroup V}
    (h : AlternatingNatural L U Z 8) (hZ : Z ≤ fixV L) (hU : XMod.commOf ↥L U = U)
    (hZ1 : Z ≠ ⊥) :
    ∃ (π : ↥(alternatingGroup (Fin 8)) →* ↥L) (Φ : ↥U ≃* ↥(coreMod 8)),
      Function.Surjective π ∧ ∀ γ (u : ↥U) (hu : ((π γ : ↥L) : MulAut V) u ∈ U),
        Φ ⟨((π γ : ↥L) : MulAut V) u, hu⟩ = act8 γ (Φ u) := by
  obtain ⟨π, hπ⟩ := h
  obtain ⟨C, hCρ, hCβ⟩ := exists_cover_of_realizesVia hπ hZ hU
  have hU2 : ∀ u : ↥U, u ^ 2 = 1 := fun u => Subtype.ext (by simpa using hV2 u)
  have hle := cover8_bound ↥U hU2 C
  have hZU : Z ≤ U := hπ.2.1
  have hker : C.β.ker = Z.subgroupOf U := by
    ext u
    rw [MonoidHom.mem_ker, hCβ, mem_subgroupOf]
  have hZcard : 2 ≤ Nat.card ↥(Z.subgroupOf U) := by
    obtain ⟨⟨x, hxZ⟩, hx1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hZ1
    have hx1' : (⟨x, hZU hxZ⟩ : ↥U) ≠ 1 := fun h =>
      hx1 (Subtype.ext (by simpa using congrArg Subtype.val h))
    have hne : Z.subgroupOf U ≠ ⊥ := by
      intro hb
      have : (⟨x, hZU hxZ⟩ : ↥U) ∈ Z.subgroupOf U := hxZ
      rw [hb, mem_bot] at this
      exact hx1' this
    have h1 := (Subgroup.one_lt_card_iff_ne_bot (Z.subgroupOf U)).2 hne
    omega
  have h2 : Nat.card C.β.ker = 2 := by rw [hker] at hle ⊢; omega
  have : Finite ↥(FFModel.altDn 8).sec := (inferInstance : Finite ↥(coreMod 8))
  obtain ⟨Φ, hΦ⟩ := ModelCover.exists_mulEquiv (D := FFModel.altDn 8) act8 (fun _ _ => rfl)
    act8_ker card_ker_eight coreMod_eight_gen (fun m => Subtype.ext (permMod_sq _)) cover8_bound
    hU2 C h2
  refine ⟨π, Φ, hπ.1, fun γ u hu => ?_⟩
  have e : (⟨((π γ : ↥L) : MulAut V) u, hu⟩ : ↥U) = C.ρ γ u := Subtype.ext (hCρ γ u).symm
  exact (congrArg Φ e).trans (hΦ γ u)

end CFSG.Quasithin.H13.A7.LinCover
