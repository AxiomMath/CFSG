module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11E3V1SixBoth
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11E3V1SixCoord
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11E3V1SixExo
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11E3V1SixNotInner

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.Quasithin.G6 CFSG.Quasithin.H13.VolI

variable {W W' : Type} [CommGroup W] [Finite W] [CommGroup W'] [Finite W']
  {M L : Subgroup (MulAut W)} {L' : Subgroup (MulAut W')} {κ : W →* W'} {e : ↥L' →* ↥L}

private theorem s1611e3_act6_ne_one :
    ∃ a : ↥(alternatingGroup (Fin 6)), CFSG.Quasithin.H13.VolI.act6 a ≠ 1 := by
  decide +kernel

private theorem s1611e3_sixZ_ne_one : sixZ ≠ (1 : SixE6) := by
  intro h
  have h1 : (allOnes 6 : PermMod 6) = 1 := by simpa [sixZ] using congrArg Subtype.val h
  have h2 := congrFun (congrArg Multiplicative.toAdd h1) 0
  have h3 : (1 : ZMod 2) = 0 := by simpa [allOnes] using h2
  exact one_ne_zero h3

private theorem s1611e3_sixZ_sq : sixZ ^ 2 = (1 : SixE6) := by
  apply Subtype.ext
  apply Multiplicative.toAdd.injective
  funext i
  show (1 : ZMod 2) + 1 = 0
  decide +kernel

private theorem s1611e3_permAct_allOnes (n : ℕ) (σ : Equiv.Perm (Fin n)) :
    permAct n σ (allOnes n) = allOnes n := by
  apply Multiplicative.toAdd.injective
  funext i
  rw [permAct_apply]
  rfl

private theorem s1611e3_coreAct_sixZ (σ : Equiv.Perm (Fin 6)) :
    coreAct 6 σ sixZ = sixZ := by
  apply Subtype.ext
  rw [coreAct_coe]
  exact s1611e3_permAct_allOnes 6 σ

private theorem s1611e3_coreAct_zpowers_sixZ (σ : Equiv.Perm (Fin 6)) {x : SixE6}
    (hx : x ∈ Subgroup.zpowers sixZ) : coreAct 6 σ x = x := by
  obtain ⟨z, hz⟩ := Subgroup.mem_zpowers_iff.1 hx
  rw [← hz, map_zpow, s1611e3_coreAct_sixZ]

private theorem s1611e3_resHom_injective (h : SixHyp M L L' κ e)
    {U : Subgroup W} (hU : ∀ ℓ ∈ L, ∀ w ∈ U, (ℓ : MulAut W) w ∈ U)
    (hreal : FFModel.Realizes (CFSG.Quasithin.H13.altCoreModel 6)
      (CFSG.Quasithin.H13.VolI.resHom L U hU).range ⊤ ⊥) :
    Function.Injective (CFSG.Quasithin.H13.VolI.resHom L U hU) := by
  classical
  haveI : IsSimpleGroup ↥L := by
    obtain ⟨φ⟩ := h.isAlt
    haveI : IsSimpleGroup (alternatingGroup (Fin 6)) :=
      alternatingGroup.isSimpleGroup (by simp)
    exact φ.isSimpleGroup
  rw [injective_iff_map_eq_one]
  intro ℓ hℓ
  by_contra hℓ1
  have hker_top : (CFSG.Quasithin.H13.VolI.resHom L U hU).ker = ⊤ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
        (CFSG.Quasithin.H13.VolI.resHom L U hU).ker with hbot | htop
    · exact absurd (Subgroup.mem_bot.1 (hbot ▸ MonoidHom.mem_ker.2 hℓ)) hℓ1
    · exact htop
  have hH : (CFSG.Quasithin.H13.VolI.resHom L U hU).range = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro x hx
    obtain ⟨ℓ', rfl⟩ := hx
    exact MonoidHom.mem_ker.1 (hker_top ▸ Subgroup.mem_top ℓ')
  obtain ⟨π, Ψ, -, hΨ⟩ := s1611e3_six_coord hreal
  haveI : Subsingleton ↥((CFSG.Quasithin.H13.VolI.resHom L U hU).range) := by
    rw [hH]; infer_instance
  have hπ1 : ∀ a, π a = 1 := fun a => Subsingleton.elim _ _
  obtain ⟨a, ha⟩ := s1611e3_act6_ne_one
  exact ha (by
    apply MulEquiv.ext
    intro x
    apply Ψ.injective
    rw [hΨ a x, hπ1 a]
    simp)

private theorem s1611e3_six_coord_ker (h : SixHyp M L L' κ e)
    {U : Subgroup W} (hU : ∀ ℓ ∈ L, ∀ w ∈ U, (ℓ : MulAut W) w ∈ U)
    {π : ↥(alternatingGroup (Fin 6)) →* ↥(CFSG.Quasithin.H13.VolI.resHom L U hU).range}
    {Ψ : SixE6 ≃* ↥U} (hπs : Function.Surjective π)
    (hΨ : ∀ (a : ↥(alternatingGroup (Fin 6))) (x : SixE6),
      Ψ (CFSG.Quasithin.H13.VolI.act6 a x) =
        ((π a : ↥(CFSG.Quasithin.H13.VolI.resHom L U hU).range) : MulAut ↥U) (Ψ x))
    (hZ : Nat.card ↥(U ⊓ κ.ker) = 2) :
    ∀ x : SixE6, ((Ψ x : ↥U) : W) ∈ κ.ker ↔ x ∈ Subgroup.zpowers sixZ := by
  classical
  have hz : ∀ a : ↥(alternatingGroup (Fin 6)),
      CFSG.Quasithin.H13.VolI.act6 a sixZ = sixZ := by
    intro a
    rw [show sixZ = (⟨allOnes 6, allOnes_six_mem⟩ : SixE6) from Subtype.ext rfl]
    exact CFSG.Quasithin.H13.VolI.act6_allOnes a
  have hfix : ((Ψ sixZ : ↥U) : W) ∈ fixV L := by
    rw [mem_fixV]
    intro ℓ hℓ
    let ℓ' : ↥L := ⟨ℓ, hℓ⟩
    obtain ⟨a, ha⟩ := hπs ⟨CFSG.Quasithin.H13.VolI.resHom L U hU ℓ', ⟨ℓ', rfl⟩⟩
    have h1 : ((π a : ↥(CFSG.Quasithin.H13.VolI.resHom L U hU).range) : MulAut ↥U) =
        CFSG.Quasithin.H13.VolI.resHom L U hU ℓ' := congrArg Subtype.val ha
    calc (ℓ : MulAut W) ((Ψ sixZ : ↥U) : W)
        = (CFSG.Quasithin.H13.VolI.resHom L U hU ℓ' (Ψ sixZ) : W) :=
          (CFSG.Quasithin.H13.VolI.coe_resHom_apply L U hU ℓ' (Ψ sixZ)).symm
      _ = (((π a : ↥(CFSG.Quasithin.H13.VolI.resHom L U hU).range) : MulAut ↥U)
            (Ψ sixZ) : W) := by rw [← h1]
      _ = (Ψ (CFSG.Quasithin.H13.VolI.act6 a sixZ) : W) := by rw [← hΨ a sixZ]
      _ = ((Ψ sixZ : ↥U) : W) := by rw [hz a]
  have hzker : ((Ψ sixZ : ↥U) : W) ∈ κ.ker := by
    rw [SixHyp.ker_eq h]; exact hfix
  have hzU : Ψ sixZ ∈ (U ⊓ κ.ker).subgroupOf U :=
    Subgroup.mem_subgroupOf.mpr ⟨(Ψ sixZ).2, hzker⟩
  have hzp : Subgroup.zpowers (Ψ sixZ) ≤ (U ⊓ κ.ker).subgroupOf U :=
    Subgroup.zpowers_le.mpr hzU
  have hz_ne : Ψ sixZ ≠ (1 : ↥U) := by
    intro h1
    exact s1611e3_sixZ_ne_one (Ψ.injective (by rw [h1, map_one]))
  have hz_sq : (Ψ sixZ) ^ 2 = (1 : ↥U) := by
    rw [← map_pow, s1611e3_sixZ_sq, map_one]
  have hcard_zp : Nat.card ↥(Subgroup.zpowers (Ψ sixZ)) = 2 := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime hz_sq hz_ne
  have hcard_Z : Nat.card ↥((U ⊓ κ.ker).subgroupOf U) = 2 := by
    rw [Nat.card_congr
      (Subgroup.subgroupOfEquivOfLe (inf_le_left : U ⊓ κ.ker ≤ U)).toEquiv, hZ]
  have heq : Subgroup.zpowers (Ψ sixZ) = (U ⊓ κ.ker).subgroupOf U :=
    Subgroup.eq_of_le_of_card_ge hzp (by rw [hcard_Z, hcard_zp])
  intro x
  have hmem : ((Ψ x : ↥U) : W) ∈ κ.ker ↔ Ψ x ∈ Subgroup.zpowers (Ψ sixZ) := by
    rw [heq, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    exact ⟨fun hx => ⟨(Ψ x).2, hx⟩, fun hx => hx.2⟩
  rw [hmem, Subgroup.mem_zpowers_iff, Subgroup.mem_zpowers_iff]
  constructor
  · rintro ⟨n, hn⟩
    exact ⟨n, Ψ.injective (by rw [map_zpow, hn])⟩
  · rintro ⟨n, hn⟩
    exact ⟨n, by rw [← map_zpow, hn]⟩

theorem s1611e3_six_coords
    (h : SixHyp M L L' κ e) :
    ∃ (W₁ W₂ : Subgroup W) (θ₁ : ↥(alternatingGroup (Fin 6)) →* ↥L)
      (Ψ₁ : SixE6 ≃* ↥W₁) (Ψ₂ : SixE6 ≃* ↥W₂),
      Function.Bijective θ₁ ∧ W₁ ⊔ W₂ = ⊤ ∧ W₁ ⊓ W₂ ≤ κ.ker ∧
      (∀ x : SixE6, ((Ψ₁ x : ↥W₁) : W) ∈ κ.ker ↔ x ∈ Subgroup.zpowers sixZ) ∧
      (∀ y : SixE6, ((Ψ₂ y : ↥W₂) : W) ∈ κ.ker ↔ y ∈ Subgroup.zpowers sixZ) ∧
      (∀ (a : ↥(alternatingGroup (Fin 6))) (x : SixE6),
        ((Ψ₁ (CFSG.Quasithin.H13.VolI.act6 a x) : ↥W₁) : W) =
          ((θ₁ a : ↥L) : MulAut W) ((Ψ₁ x : ↥W₁) : W)) ∧
      (∀ (a : ↥(alternatingGroup (Fin 6))) (y : SixE6),
        ((Ψ₂ (CFSG.Quasithin.H13.VolI.act6 (sixAlphaA a) y) : ↥W₂) : W) =
          ((θ₁ a : ↥L) : MulAut W) ((Ψ₂ y : ↥W₂) : W)) := by
  classical
  obtain ⟨I₁, I₂, W₁, W₂, h₁, h₂, hIinf, hIsup, hN₁, hN₂, hne, hWsup, hκW₁, hκW₂,
    hκsurj₁, hκsurj₂, hZ₁, hZ₂, hker12, hreal₁, hreal₂⟩ := s1611e3_six_both h
  obtain ⟨π₁, Ψ₁', hπ₁s, hπ₁eq⟩ := s1611e3_six_coord hreal₁
  obtain ⟨π₂, Ψ₂', hπ₂s, hπ₂eq⟩ := s1611e3_six_coord hreal₂
  have hinj₁ : Function.Injective (resHom L W₁ h₁) := s1611e3_resHom_injective h h₁ hreal₁
  have hinj₂ : Function.Injective (resHom L W₂ h₂) := s1611e3_resHom_injective h h₂ hreal₂
  let iso₁ : ↥L ≃* ↥(resHom L W₁ h₁).range := MonoidHom.ofInjective (f := resHom L W₁ h₁) hinj₁
  let iso₂ : ↥L ≃* ↥(resHom L W₂ h₂).range := MonoidHom.ofInjective (f := resHom L W₂ h₂) hinj₂
  let θ₁ : ↥(alternatingGroup (Fin 6)) →* ↥L := iso₁.symm.toMonoidHom.comp π₁
  let θ₂ : ↥(alternatingGroup (Fin 6)) →* ↥L := iso₂.symm.toMonoidHom.comp π₂
  have hθ₁ : ∀ a, resHom L W₁ h₁ (θ₁ a) =
      ((π₁ a : ↥(resHom L W₁ h₁).range) : MulAut ↥W₁) :=
    fun a => MonoidHom.apply_ofInjective_symm hinj₁ (π₁ a)
  have hθ₂ : ∀ a, resHom L W₂ h₂ (θ₂ a) =
      ((π₂ a : ↥(resHom L W₂ h₂).range) : MulAut ↥W₂) :=
    fun a => MonoidHom.apply_ofInjective_symm hinj₂ (π₂ a)
  have hcardA : Nat.card ↥(alternatingGroup (Fin 6)) = 360 := by
    rw [nat_card_alternatingGroup, Nat.card_fin]
    norm_num
  have hLcard : Nat.card ↥L = 360 := by
    obtain ⟨φ⟩ := h.isAlt
    rw [Nat.card_congr φ.toEquiv, nat_card_alternatingGroup, Nat.card_fin]
    norm_num
  have hθ₁surj : Function.Surjective θ₁ := iso₁.symm.surjective.comp hπ₁s
  have hθ₂surj : Function.Surjective θ₂ := iso₂.symm.surjective.comp hπ₂s
  have hθ₁bij : Function.Bijective θ₁ := by
    refine ⟨?_, hθ₁surj⟩
    have hker : Nat.card θ₁.ker = 1 := by
      have hs := Subgroup.card_ker_mul_card_of_surjective (f := θ₁) hθ₁surj
      rw [hLcard, hcardA] at hs
      exact Nat.eq_of_mul_eq_mul_right (by norm_num : 0 < 360) (by rw [one_mul]; exact hs)
    exact (MonoidHom.ker_eq_bot_iff θ₁).mp (Subgroup.eq_bot_of_card_eq θ₁.ker hker)
  have hθ₂bij : Function.Bijective θ₂ := by
    refine ⟨?_, hθ₂surj⟩
    have hker : Nat.card θ₂.ker = 1 := by
      have hs := Subgroup.card_ker_mul_card_of_surjective (f := θ₂) hθ₂surj
      rw [hLcard, hcardA] at hs
      exact Nat.eq_of_mul_eq_mul_right (by norm_num : 0 < 360) (by rw [one_mul]; exact hs)
    exact (MonoidHom.ker_eq_bot_iff θ₂).mp (Subgroup.eq_bot_of_card_eq θ₂.ker hker)
  let θ₁Iso : ↥(alternatingGroup (Fin 6)) ≃* ↥L := MulEquiv.ofBijective θ₁ hθ₁bij
  let θ₂Iso : ↥(alternatingGroup (Fin 6)) ≃* ↥L := MulEquiv.ofBijective θ₂ hθ₂bij
  let ε : MulAut ↥(alternatingGroup (Fin 6)) := θ₁Iso.trans θ₂Iso.symm
  have hε : ∀ a, θ₁ a = θ₂ (ε a) := by
    intro a
    change θ₁Iso a = θ₂Iso (θ₂Iso.symm (θ₁Iso a))
    rw [MulEquiv.apply_symm_apply]
  have hL'card : Nat.card ↥L' = 360 := by
    obtain ⟨π, hπ⟩ := hN₁
    have hdvd : Nat.card ↥L' ∣ 360 := by
      rw [← hcardA]
      exact Subgroup.card_dvd_of_surjective hπ.1
    have h360 : 360 ∣ Nat.card ↥L' := by
      rw [← hLcard]
      exact Subgroup.card_dvd_of_surjective h.esurj
    exact Nat.dvd_antisymm hdvd h360
  have he_inj : Function.Injective e := by
    have hker : Nat.card e.ker = 1 := by
      have hs := Subgroup.card_ker_mul_card_of_surjective (f := e) h.esurj
      rw [hLcard, hL'card] at hs
      exact Nat.eq_of_mul_eq_mul_right (by norm_num : 0 < 360) (by rw [one_mul]; exact hs)
    exact (MonoidHom.ker_eq_bot_iff e).mp (Subgroup.eq_bot_of_card_eq e.ker hker)
  let eIso : ↥L' ≃* ↥L := MulEquiv.ofBijective e ⟨he_inj, h.esurj⟩
  let ρ₁ : ↥(alternatingGroup (Fin 6)) →* ↥L' := eIso.symm.toMonoidHom.comp θ₁
  let ρ₂ : ↥(alternatingGroup (Fin 6)) →* ↥L' := eIso.symm.toMonoidHom.comp θ₂
  have hρ₁ : ∀ a, e (ρ₁ a) = θ₁ a := fun a => by
    change eIso (eIso.symm (θ₁ a)) = θ₁ a
    rw [MulEquiv.apply_symm_apply]
  have hρ₂ : ∀ a, e (ρ₂ a) = θ₂ a := fun a => by
    change eIso (eIso.symm (θ₂ a)) = θ₂ a
    rw [MulEquiv.apply_symm_apply]
  let β₁ : SixE6 →* W' := κ.comp (W₁.subtype.comp Ψ₁'.toMonoidHom)
  let β₂ : SixE6 →* W' := κ.comp (W₂.subtype.comp Ψ₂'.toMonoidHom)
  have hβ₁ : β₁.range = I₁ := by
    apply le_antisymm
    · rintro y ⟨x, rfl⟩
      exact hκW₁ _ (Ψ₁' x).2
    · intro i hi
      obtain ⟨w, hw, hwκ⟩ := hκsurj₁ i hi
      obtain ⟨x, hx⟩ := Ψ₁'.surjective ⟨w, hw⟩
      refine ⟨x, ?_⟩
      change κ ((Ψ₁' x : ↥W₁) : W) = i
      rw [show ((Ψ₁' x : ↥W₁) : W) = w from congrArg Subtype.val hx]
      exact hwκ
  have hβ₂ : β₂.range = I₂ := by
    apply le_antisymm
    · rintro y ⟨x, rfl⟩
      exact hκW₂ _ (Ψ₂' x).2
    · intro i hi
      obtain ⟨w, hw, hwκ⟩ := hκsurj₂ i hi
      obtain ⟨x, hx⟩ := Ψ₂'.surjective ⟨w, hw⟩
      refine ⟨x, ?_⟩
      change κ ((Ψ₂' x : ↥W₂) : W) = i
      rw [show ((Ψ₂' x : ↥W₂) : W) = w from congrArg Subtype.val hx]
      exact hwκ
  have hker₁' := s1611e3_six_coord_ker (U := W₁) h h₁ hπ₁s hπ₁eq hZ₁
  have hker₂' := s1611e3_six_coord_ker (U := W₂) h h₂ hπ₂s hπ₂eq hZ₂
  have hk₁ : β₁.ker = Subgroup.zpowers sixZ := by
    ext x
    rw [MonoidHom.mem_ker]
    show κ ((Ψ₁' x : ↥W₁) : W) = 1 ↔ x ∈ Subgroup.zpowers sixZ
    rw [← MonoidHom.mem_ker]
    exact hker₁' x
  have hk₂ : β₂.ker = Subgroup.zpowers sixZ := by
    ext x
    rw [MonoidHom.mem_ker]
    show κ ((Ψ₂' x : ↥W₂) : W) = 1 ↔ x ∈ Subgroup.zpowers sixZ
    rw [← MonoidHom.mem_ker]
    exact hker₂' x
  have he₁ : ∀ a x, β₁ (act6 a x) = ((ρ₁ a : ↥L') : MulAut W') (β₁ x) := by
    intro a x
    show κ ((Ψ₁' (act6 a x) : ↥W₁) : W) =
      ((ρ₁ a : ↥L') : MulAut W') (κ ((Ψ₁' x : ↥W₁) : W))
    rw [hπ₁eq a x]
    have hres : ((π₁ a : ↥(resHom L W₁ h₁).range) : MulAut ↥W₁) =
        resHom L W₁ h₁ (θ₁ a) := (hθ₁ a).symm
    rw [hres, coe_resHom_apply, ← hρ₁ a, h.equiv]
  have he₂ : ∀ a x, β₂ (act6 a x) = ((ρ₂ a : ↥L') : MulAut W') (β₂ x) := by
    intro a x
    show κ ((Ψ₂' (act6 a x) : ↥W₂) : W) =
      ((ρ₂ a : ↥L') : MulAut W') (κ ((Ψ₂' x : ↥W₂) : W))
    rw [hπ₂eq a x]
    have hres : ((π₂ a : ↥(resHom L W₂ h₂).range) : MulAut ↥W₂) =
        resHom L W₂ h₂ (θ₂ a) := (hθ₂ a).symm
    rw [hres, coe_resHom_apply, ← hρ₂ a, h.equiv]
  have hL₁ : Function.Surjective ρ₁ := eIso.symm.surjective.comp hθ₁surj
  have hL₂ : Function.Surjective ρ₂ := eIso.symm.surjective.comp hθ₂surj
  rcases s1611e3_six_aut_cosets ε with ⟨s, hs⟩ | ⟨s, hs⟩
  · exfalso
    have hsymm : ∀ a : ↥(alternatingGroup (Fin 6)),
        ((ε.symm a : ↥(alternatingGroup (Fin 6))) : Equiv.Perm (Fin 6)) =
          s⁻¹ * (a : Equiv.Perm (Fin 6)) * s := by
      intro a
      have h1 := hs (ε.symm a)
      rw [MulEquiv.apply_symm_apply] at h1
      calc ((ε.symm a : ↥(alternatingGroup (Fin 6))) : Equiv.Perm (Fin 6))
          = s⁻¹ * (s * ((ε.symm a : ↥(alternatingGroup (Fin 6))) : Equiv.Perm (Fin 6)) * s⁻¹) * s :=
            by group
        _ = s⁻¹ * (a : Equiv.Perm (Fin 6)) * s := by rw [← h1]
    have hs' : ∀ a : ↥(alternatingGroup (Fin 6)), ∃ b : ↥(alternatingGroup (Fin 6)),
        (b : Equiv.Perm (Fin 6)) = s⁻¹ * (a : Equiv.Perm (Fin 6)) * (s⁻¹)⁻¹ ∧ ρ₂ a = ρ₁ b := by
      intro a
      refine ⟨ε.symm a, ?_, ?_⟩
      · rw [inv_inv]; exact hsymm a
      · have h2 : θ₂ a = θ₁ (ε.symm a) := by
          rw [hε (ε.symm a), MulEquiv.apply_symm_apply]
        exact congrArg eIso.symm h2
    obtain ⟨ψ, hψc, hψmap⟩ := s1611e3_six_not_inner hIinf hIsup ρ₁ ρ₂ β₁ β₂
      hβ₁ hβ₂ hk₁ hk₂ he₁ he₂ hL₁ hL₂ hs'
    exact hne ψ hψc hψmap
  · let Ψ₂ : SixE6 ≃* ↥W₂ := (coreAct 6 s).trans Ψ₂'
    have hker₂ : ∀ y, ((Ψ₂ y : ↥W₂) : W) ∈ κ.ker ↔ y ∈ Subgroup.zpowers sixZ := by
      intro y
      show ((Ψ₂' (coreAct 6 s y) : ↥W₂) : W) ∈ κ.ker ↔ y ∈ Subgroup.zpowers sixZ
      rw [hker₂' (coreAct 6 s y)]
      constructor
      · intro hy
        have hthis := s1611e3_coreAct_zpowers_sixZ s⁻¹ hy
        rw [show coreAct 6 s⁻¹ (coreAct 6 s y) = y from by
          rw [← MulAut.mul_apply, ← map_mul, inv_mul_cancel, map_one, MulAut.one_apply]] at hthis
        rw [hthis]
        exact hy
      · intro hy
        rw [s1611e3_coreAct_zpowers_sixZ s hy]
        exact hy
    have hWinf : W₁ ⊓ W₂ ≤ κ.ker := by
      intro w hw
      rw [MonoidHom.mem_ker]
      have h3 : κ w ∈ I₁ ⊓ I₂ := Subgroup.mem_inf.mpr ⟨hκW₁ w hw.1, hκW₂ w hw.2⟩
      rw [hIinf] at h3
      exact Subgroup.mem_bot.1 h3
    have he₁fin : ∀ a x, ((Ψ₁' (act6 a x) : ↥W₁) : W) =
        ((θ₁ a : ↥L) : MulAut W) ((Ψ₁' x : ↥W₁) : W) := by
      intro a x
      rw [hπ₁eq a x]
      have hres : ((π₁ a : ↥(resHom L W₁ h₁).range) : MulAut ↥W₁) =
          resHom L W₁ h₁ (θ₁ a) := (hθ₁ a).symm
      rw [hres, coe_resHom_apply]
    have hact : ∀ a : ↥(alternatingGroup (Fin 6)), act6 (ε a) =
        coreAct 6 s * act6 (sixAlphaA a) * coreAct 6 s⁻¹ := by
      intro a
      show coreAct 6 (((ε a : ↥(alternatingGroup (Fin 6))) : Equiv.Perm (Fin 6))) =
        coreAct 6 s * act6 (sixAlphaA a) * coreAct 6 s⁻¹
      rw [hs a, map_mul, map_mul, map_inv]
      rfl
    have hcore : ∀ (a : ↥(alternatingGroup (Fin 6))) (y : SixE6),
        coreAct 6 s (act6 (sixAlphaA a) y) = act6 (ε a) (coreAct 6 s y) := by
      intro a y
      rw [hact a]
      have hinv : coreAct 6 s⁻¹ (coreAct 6 s y) = y := by
        rw [← MulAut.mul_apply, ← map_mul, inv_mul_cancel, map_one, MulAut.one_apply]
      rw [MulAut.mul_apply, MulAut.mul_apply, hinv]
    have he₂fin : ∀ a y, ((Ψ₂ (act6 (sixAlphaA a) y) : ↥W₂) : W) =
        ((θ₁ a : ↥L) : MulAut W) ((Ψ₂ y : ↥W₂) : W) := by
      intro a y
      show ((Ψ₂' (coreAct 6 s (act6 (sixAlphaA a) y)) : ↥W₂) : W) =
        ((θ₁ a : ↥L) : MulAut W) ((Ψ₂' (coreAct 6 s y) : ↥W₂) : W)
      rw [hcore a y, hπ₂eq (ε a) (coreAct 6 s y)]
      have hres : ((π₂ (ε a) : ↥(resHom L W₂ h₂).range) : MulAut ↥W₂) =
          resHom L W₂ h₂ (θ₁ a) := by
        rw [← hθ₂ (ε a), ← hε a]
      rw [hres, coe_resHom_apply]
    exact ⟨W₁, W₂, θ₁, Ψ₁', Ψ₂, hθ₁bij, hWsup, hWinf, hker₁', hker₂, he₁fin, he₂fin⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
