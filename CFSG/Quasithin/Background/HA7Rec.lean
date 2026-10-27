module

public import CFSG.Quasithin.Background.HA7
public import CFSG.Quasithin.Background.HSecTransfer
public import CFSG.Quasithin.Background.B5FinS8Core

public section

namespace CFSG.Quasithin

namespace H

namespace A7

open CFSG.Open Matrix Equiv

theorem isSimpleGroup_GL_four : IsSimpleGroup (GL (Fin 4) (ZMod 2)) :=
  isSimpleGroup_GL (MulEquiv.ofBijective B5FinS8.alphaHom B5FinS8.alphaHom_bijective)

theorem card_GL_four : Nat.card (GL (Fin 4) (ZMod 2)) = 20160 :=
  card_GL (MulEquiv.ofBijective B5FinS8.alphaHom B5FinS8.alphaHom_bijective)

theorem altLift7_last (σ : alternatingGroup (Fin 7)) :
    ((altLift7 σ : alternatingGroup (Fin 8)) : Perm (Fin 8)) (Fin.last 7) = Fin.last 7 := by
  rw [coe_altLift7, Equiv.Perm.viaEmbedding_apply_of_notMem]
  rintro ⟨i, hi⟩
  exact Fin.castSucc_ne_last i hi

theorem exists_alpha_of_index {Γ' : Subgroup (GL (Fin 4) (ZMod 2))} (h8 : Γ'.index = 8) :
    ∃ α : ↥(alternatingGroup (Fin 8)) ≃* GL (Fin 4) (ZMod 2), ∀ σ, α (altLift7 σ) ∈ Γ' := by
  classical
  have hsimp := isSimpleGroup_GL_four
  have hQ : Nat.card (GL (Fin 4) (ZMod 2) ⧸ Γ') = 8 := h8
  have : Finite (GL (Fin 4) (ZMod 2) ⧸ Γ') := Nat.finite_of_card_ne_zero (by rw [hQ]; norm_num)
  let c₀ : GL (Fin 4) (ZMod 2) ⧸ Γ' ≃ Fin 8 := Finite.equivFinOfCardEq hQ
  let c : GL (Fin 4) (ZMod 2) ⧸ Γ' ≃ Fin 8 :=
    c₀.trans (Equiv.swap (c₀ (QuotientGroup.mk 1)) (Fin.last 7))
  have hc : c (QuotientGroup.mk 1) = Fin.last 7 := by
    simp only [c, Equiv.trans_apply, Equiv.swap_apply_left]
  have hcs : c.symm (Fin.last 7) = QuotientGroup.mk 1 := by
    rw [Equiv.symm_apply_eq]
    exact hc.symm
  let f : GL (Fin 4) (ZMod 2) →* Perm (Fin 8) :=
    (Equiv.permCongrHom c).toMonoidHom.comp
      (MulAction.toPermHom (GL (Fin 4) (ZMod 2)) (GL (Fin 4) (ZMod 2) ⧸ Γ'))
  have hf : ∀ g x, f g x = c (g • c.symm x) := fun g x => rfl
  have hfix : ∀ g, f g (Fin.last 7) = Fin.last 7 → g ∈ Γ' := by
    intro g hg
    rw [hf, hcs] at hg
    have h1 : g • (QuotientGroup.mk 1 : GL (Fin 4) (ZMod 2) ⧸ Γ') = QuotientGroup.mk 1 :=
      c.injective (hg.trans hc.symm)
    rw [MulAction.Quotient.smul_mk, smul_eq_mul, mul_one] at h1
    have h2 := QuotientGroup.eq.mp h1
    rw [mul_one] at h2
    exact inv_mem_iff.mp h2
  have hfinj : Function.Injective f := by
    rcases (MonoidHom.normal_ker f).eq_bot_or_eq_top with hk | hk
    · exact (MonoidHom.ker_eq_bot_iff f).mp hk
    · exfalso
      have htop : Γ' = ⊤ := by
        rw [eq_top_iff]
        intro g _
        refine hfix g ?_
        have hg : f g = 1 := MonoidHom.mem_ker.mp (hk ▸ Subgroup.mem_top g)
        rw [hg]
        rfl
      rw [htop, Subgroup.index_top] at h8
      omega
  have hsign : ∀ g, Perm.sign (f g) = 1 := by
    rcases (MonoidHom.normal_ker (Perm.sign.comp f)).eq_bot_or_eq_top with hk | hk
    · exfalso
      have hinj : Function.Injective (Perm.sign.comp f) := (MonoidHom.ker_eq_bot_iff _).mp hk
      have h1 := Nat.card_le_card_of_injective _ hinj
      rw [card_GL_four, Nat.card_eq_fintype_card, Fintype.card_units_int] at h1
      omega
    · intro g
      have hg : g ∈ (Perm.sign.comp f).ker := hk ▸ Subgroup.mem_top g
      exact MonoidHom.mem_ker.mp hg
  let f' : GL (Fin 4) (ZMod 2) →* alternatingGroup (Fin 8) :=
    f.codRestrict (alternatingGroup (Fin 8)) fun g => Equiv.Perm.mem_alternatingGroup.mpr (hsign g)
  have hf'inj : Function.Injective f' := fun g h e => hfinj (congrArg Subtype.val e)
  have hcard : Nat.card (GL (Fin 4) (ZMod 2)) = Nat.card (alternatingGroup (Fin 8)) := by
    rw [card_GL_four, nat_card_alternatingGroup, Nat.card_fin]
    rfl
  let φ := MulEquiv.ofBijective f' (hf'inj.bijective_of_nat_card_le hcard.ge)
  refine ⟨φ.symm, fun σ => hfix _ ?_⟩
  have h1 : f (φ.symm (altLift7 σ)) = ((altLift7 σ : alternatingGroup (Fin 8)) : Perm (Fin 8)) :=
    congrArg Subtype.val (φ.apply_symm_apply (altLift7 σ))
  rw [h1]
  exact altLift7_last σ

theorem a7Four_of_faithful {V : Type*} [CommGroup V] {H : Subgroup (MulAut V)} {U : Subgroup V}
    (hA7 : Nonempty (↥H ≃* alternatingGroup (Fin 7))) (hU : ∀ h ∈ H, ∀ u ∈ U, h u ∈ U)
    (hsq : ∀ u ∈ U, u * u = 1) (hcard : Nat.card U = 2 ^ 4)
    (hfaith : ∀ h ∈ H, (∀ u ∈ U, h u = u) → h = 1) : A7Four H U ⊥ := by
  classical
  obtain ⟨eH⟩ := hA7
  have : Finite ↥U := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨e⟩ := CFSG.SectionRank.Ccomm.nonempty_mulEquiv_of_elementary (W := ↥U) (p := 2)
    (fun a b => Subtype.ext (mul_comm (a : V) b))
    (fun a => Subtype.ext (by rw [Subgroup.coe_pow, sq, hsq _ a.2]; rfl)) hcard
  have hresinj : Function.Injective (resHom hU) := by
    rw [injective_iff_map_eq_one]
    intro h hh
    apply Subtype.ext
    refine hfaith _ h.2 fun u hu => ?_
    exact congrArg (fun a : MulAut ↥U => ((a ⟨u, hu⟩ : ↥U) : V)) hh
  let ρ : ↥H →* GL (Fin 4) (ZMod 2) :=
    (CFSG.SectionRank.Ccomm.elemAutEquivGL e).toMonoidHom.comp (resHom hU)
  have hρinj : Function.Injective ρ :=
    (CFSG.SectionRank.Ccomm.elemAutEquivGL e).injective.comp hresinj
  have hρ : ∀ (h : ↥H) (u : ↥U),
      ((ρ h : GL (Fin 4) (ZMod 2)) : Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ
        Multiplicative.toAdd (e u) = Multiplicative.toAdd (e (resHom hU h u)) :=
    fun h u => CFSG.SectionRank.Ccomm.elemAutEquivGL_mulVec e (resHom hU h) u
  have hH : Nat.card ↥H = 2520 := by rw [Nat.card_congr eH.toEquiv, card_A7]
  have hΓ : Nat.card ρ.range = 2520 := by
    rw [← hH]
    exact (Nat.card_congr (MonoidHom.ofInjective hρinj).toEquiv).symm
  have h8 : ρ.range.index = 8 := by
    have := ρ.range.index_mul_card
    rw [card_GL_four, hΓ] at this
    omega
  obtain ⟨α, hα⟩ := exists_alpha_of_index h8
  let κ : ↥(alternatingGroup (Fin 7)) →* ↥ρ.range :=
    (α.toMonoidHom.comp altLift7).codRestrict ρ.range hα
  have hκinj : Function.Injective κ := fun x y hxy =>
    altLift7_injective (α.injective (congrArg Subtype.val hxy))
  have hκ : Function.Bijective κ := hκinj.bijective_of_nat_card_le (by rw [hΓ, card_A7])
  let ψ' : ↥H ≃* ↥ρ.range := MonoidHom.ofInjective hρinj
  let π : ↥(alternatingGroup (Fin 7)) →* ↥H := ψ'.symm.toMonoidHom.comp κ
  have hπρ : ∀ σ, ρ (π σ) = α (altLift7 σ) := fun σ =>
    congrArg Subtype.val (ψ'.apply_symm_apply (κ σ))
  let β : ↥U →* ↥(FFModel.a7Four α).sec ⧸
      (FFModel.a7Four α).ker.subgroupOf (FFModel.a7Four α).sec :=
    (QuotientGroup.mk' _).comp
      (e.toMonoidHom.codRestrict (FFModel.a7Four α).sec fun _ => Subgroup.mem_top _)
  have hβ : ∀ u, β u = QuotientGroup.mk ⟨e u, Subgroup.mem_top _⟩ := fun u => rfl
  refine ⟨α, π, ψ'.symm.surjective.comp hκ.2, bot_le, fun _ _ => Subgroup.mem_top _,
    fun h u hu => hU _ h.2 _ hu, fun h z hz => ?_, fun _ _ _ => Subgroup.mem_top _,
    fun γ m hm => ?_, β, ?_, ?_, ?_⟩
  · rw [Subgroup.mem_bot] at hz ⊢
    rw [hz, map_one]
  · have hm1 : m = 1 := Subgroup.mem_bot.mp hm
    refine Subgroup.mem_bot.mpr ?_
    rw [hm1]
    change Multiplicative.ofAdd
      (_ *ᵥ Multiplicative.toAdd (1 : Multiplicative (Fin 4 → ZMod 2))) = 1
    rw [toAdd_one, Matrix.mulVec_zero, ofAdd_zero]
  · intro y
    obtain ⟨⟨w, hw⟩, rfl⟩ := QuotientGroup.mk_surjective y
    refine ⟨e.symm w, ?_⟩
    rw [hβ]
    congr 1
    exact Subtype.ext (e.apply_symm_apply w)
  · intro u
    rw [hβ, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    change e u ∈ (⊥ : Subgroup (Multiplicative (Fin 4 → ZMod 2))) ↔ (u : V) ∈ (⊥ : Subgroup V)
    rw [Subgroup.mem_bot, Subgroup.mem_bot, map_eq_one_iff e e.injective]
    exact ⟨fun h => by rw [h]; rfl, fun h => Subtype.ext h⟩
  · rintro (γ : ↥(alternatingGroup (Fin 7))) u m hu hm hβu
    have hm' : (m : (FFModel.a7Four α).Amb) = e u := by
      rw [hβ] at hβu
      have h1 := QuotientGroup.eq.mp hβu
      rw [Subgroup.mem_subgroupOf] at h1
      have h2 : (show (FFModel.a7Four α).Amb from e u)⁻¹ * (m : (FFModel.a7Four α).Amb) = 1 :=
        Subgroup.mem_bot.mp h1
      exact (inv_mul_eq_one.mp h2).symm
    have key : Multiplicative.toAdd (e ⟨((π γ : ↥H) : MulAut V) (u : V), hu⟩) =
        ((α (altLift7 γ) : GL (Fin 4) (ZMod 2)) : Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ
          Multiplicative.toAdd (e u) := by
      rw [← hπρ γ, hρ]
      rfl
    rw [hβ]
    congr 1
    apply Subtype.ext
    change e ⟨((π γ : ↥H) : MulAut V) (u : V), hu⟩ =
      Multiplicative.ofAdd (((α (altLift7 γ) : GL (Fin 4) (ZMod 2)) :
        Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ Multiplicative.toAdd (m : (FFModel.a7Four α).Amb))
    rw [hm', ← key]
    rfl

theorem a7Four_of_nontrivial {V : Type*} [CommGroup V] {H : Subgroup (MulAut V)}
    {U : Subgroup V} (hA7 : Nonempty (↥H ≃* alternatingGroup (Fin 7)))
    (hU : ∀ h ∈ H, ∀ u ∈ U, h u ∈ U) (hsq : ∀ u ∈ U, u * u = 1) (hcard : Nat.card U = 2 ^ 4)
    (hnt : ∃ h ∈ H, ∃ u ∈ U, h u ≠ u) : A7Four H U ⊥ := by
  refine a7Four_of_faithful hA7 hU hsq hcard fun h hh hfix => ?_
  obtain ⟨eH⟩ := hA7
  have : IsSimpleGroup ↥H := eH.isSimpleGroup
  rcases (MonoidHom.normal_ker (resHom hU)).eq_bot_or_eq_top with hk | hk
  · have h1 : (⟨h, hh⟩ : ↥H) ∈ (resHom hU).ker :=
      MonoidHom.mem_ker.mpr (MulEquiv.ext fun u => Subtype.ext (hfix u u.2))
    rw [hk, Subgroup.mem_bot] at h1
    exact congrArg Subtype.val h1
  · exfalso
    obtain ⟨h₀, hh₀, u, hu, hne⟩ := hnt
    have h1 : (⟨h₀, hh₀⟩ : ↥H) ∈ (resHom hU).ker := hk ▸ Subgroup.mem_top _
    have h2 := congrArg (fun a : MulAut ↥U => ((a ⟨u, hu⟩ : ↥U) : V)) (MonoidHom.mem_ker.mp h1)
    exact hne h2

end A7

end H

end CFSG.Quasithin
