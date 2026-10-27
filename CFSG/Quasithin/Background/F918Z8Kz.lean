module

public import CFSG.Quasithin.Background.F918Z8Kc
public import CFSG.Quasithin.Background.F918Z8Kw2
public import CFSG.Quasithin.Background.F918Z8Kw3
public import CFSG.Quasithin.Background.F918Z8Kw5
public import CFSG.Quasithin.Background.F918Z8Kp
public import CFSG.Quasithin.Background.F918Z8Kk3
public import CFSG.Quasithin.Background.F918Z8Kk5
public import CFSG.Quasithin.EmptyFaithful.R3c2Types
public import CFSG.Quasithin.Background.F918Z8Loc3
public import CFSG.ThirdParty.QiuzhenCFSG.BenderGlauberman.Lemma19

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique CFSG.QuasithinUnique.Bridge
open scoped Pointwise

theorem loc_out_three {X : Type} [Group X] (hΛ : IsPSL 3 2 1 X) :
    Subgroup.center X = ⊥ ∧ Nat.card (MulAut X) ≤ 2 * Nat.card X :=
  CFSG.Quasithin.lkf_out_three hΛ

theorem loc_out_alt5 {X : Type} [Group X] (e : X ≃* ↥(alternatingGroup (Fin 5))) :
    Subgroup.center X = ⊥ ∧ Nat.card (MulAut X) ≤ 2 * Nat.card X := by
  have hcard : Nat.card X = 60 := by
    rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_eq_fintype_card,
      Fintype.card_fin]
    decide
  have : IsSimpleGroup ↥(alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup (by simp)
  have : IsSimpleGroup X := e.isSimpleGroup
  have : Finite X := Finite.of_equiv _ e.symm.toEquiv
  have hcen : Subgroup.center X = ⊥ := by
    rcases (inferInstance : IsSimpleGroup X).eq_bot_or_eq_top_of_normal (Subgroup.center X) with
      hc | hc
    · exact hc
    · exfalso
      have : IsMulCommutative X := Subgroup.center_eq_top_iff.mp hc
      have hp : (Nat.card X).Prime := Group.is_simple_iff_prime_card.mp inferInstance
      rw [hcard] at hp
      norm_num at hp
  refine ⟨hcen, ?_⟩
  rw [Nat.card_congr (MulAut.congr e).toEquiv]
  have h1 := FFC.card_mulAut_alternating_le (n := 5) (Or.inl rfl)
  have h2 : Nat.card ↥(alternatingGroup (Fin 5)) = Nat.card X := (Nat.card_congr e.toEquiv).symm
  omega


variable {Y : Type} [CommGroup Y] [Finite Y] {Γ Λ S : Subgroup (MulAut Y)} {V : Subgroup Y}

theorem loc_isPSL_three (h : LocCfg Γ Λ S V)
    (hnat : BinaryNaturalSL (autSub Λ V) ⊤ ⊥ 3 1) : IsPSL 3 2 1 ↥Λ := by
  obtain ⟨π, hπ⟩ := FFC.BinaryNaturalSL.exists_zmod hnat
  have hπs : Function.Surjective π := hπ.1
  have hsimp : IsSimpleGroup ↥Λ := insp5a_sec_isSimpleGroup h.a38
  obtain ⟨hID, -, -⟩ := loc_irr_data h
  obtain ⟨eΛ⟩ := CaseIISec.equiv hsimp hID (loc_nontriv h)
  have hS : IsSimpleGroup ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 (ZMod 2)) :=
    SBc11.isSimpleGroup_of_list
      (Or.inl (R3c2.isPSL_two_of_statedSL (by norm_num) (MulEquiv.refl _)))
  have hker : π.ker = ⊥ := by
    rcases hS.eq_bot_or_eq_top_of_normal π.ker with h0 | h0
    · exact h0
    · exfalso
      have hsub : Subsingleton ↥(autSub Λ V) := by
        refine ⟨fun a b => ?_⟩
        obtain ⟨x, rfl⟩ := hπs a
        obtain ⟨y, rfl⟩ := hπs b
        have hx : π x = 1 := by rw [← MonoidHom.mem_ker, h0]; trivial
        have hy : π y = 1 := by rw [← MonoidHom.mem_ker, h0]; trivial
        rw [hx, hy]
      have hsubΛ : Subsingleton ↥Λ := eΛ.toEquiv.subsingleton
      obtain ⟨a, b, hab⟩ := exists_pair_ne ↥Λ
      exact hab (Subsingleton.elim a b)
  have hinj : Function.Injective π := (MonoidHom.ker_eq_bot_iff π).1 hker
  let eπ : ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 (ZMod 2)) ≃* ↥(autSub Λ V) :=
    MulEquiv.ofBijective π ⟨hinj, hπs⟩
  exact R3c2.isPSL_two_of_statedSL (by norm_num) (eΛ.trans eπ.symm)

theorem loc_alt5_equiv (h : LocCfg Γ Λ S V)
    (halt : AlternatingNatural (autSub Λ V) ⊤ ⊥ 5) :
    Nonempty (↥Λ ≃* ↥(alternatingGroup (Fin 5))) := by
  obtain ⟨π₀, hπ⟩ := halt
  let π : ↥(alternatingGroup (Fin 5)) →* ↥(autSub Λ V) := π₀
  have hπs : Function.Surjective π := hπ.1
  have hsimp : IsSimpleGroup ↥Λ := insp5a_sec_isSimpleGroup h.a38
  obtain ⟨hID, -, -⟩ := loc_irr_data h
  obtain ⟨eΛ⟩ := CaseIISec.equiv hsimp hID (loc_nontriv h)
  have hS : IsSimpleGroup ↥(alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup (by simp)
  have hker : π.ker = ⊥ := by
    rcases hS.eq_bot_or_eq_top_of_normal π.ker with h0 | h0
    · exact h0
    · exfalso
      have hsub : Subsingleton ↥(autSub Λ V) := by
        refine ⟨fun a b => ?_⟩
        obtain ⟨x, rfl⟩ := hπs a
        obtain ⟨y, rfl⟩ := hπs b
        have hx : π x = 1 := by rw [← MonoidHom.mem_ker, h0]; trivial
        have hy : π y = 1 := by rw [← MonoidHom.mem_ker, h0]; trivial
        rw [hx, hy]
      have hsubΛ : Subsingleton ↥Λ := eΛ.toEquiv.subsingleton
      obtain ⟨a, b, hab⟩ := exists_pair_ne ↥Λ
      exact hab (Subsingleton.elim a b)
  have hinj : Function.Injective π := (MonoidHom.ker_eq_bot_iff π).1 hker
  let eπ : ↥(alternatingGroup (Fin 5)) ≃* ↥(autSub Λ V) := MulEquiv.ofBijective π ⟨hinj, hπs⟩
  exact ⟨eΛ.trans eπ.symm⟩

theorem d321LocFaith_of_inputs
    (hB42 : AsB42) (hA21 : AsA21SQTKSection) (hF : Vol2.Ch10.SecA.Facts10_1)
    (hX : Insp5aNonShape) : D321LocFaith := by
  intro Y _ _ Γ Λ S V h A hA hAS hAf
  obtain ⟨hrkA, hAV, hAfV, hEe, hrkE, hEN⟩ := loc_A_data h hA hAS hAf
  have hFF := loc_ff h hA hAS hAf
  obtain ⟨hID, hV0, -⟩ := loc_irr_data h
  have hLs : Λ ≤ stabSub V := le_stabSub_of_forall_mem hID
  have hfaith := loc_faithful h
  have hΓn : Γ ≤ Subgroup.normalizer (Λ : Set (MulAut Y)) := fun g hg => h.std.hyp.Mp_normal hg
  have hgen : (⨆ g ∈ Γ, V.map g.toMonoidHom) = ⊤ := h.std.hyp.gen
  have hbot : (⊥ : Subgroup Y).subgroupOf V = ⊥ := Subgroup.bot_subgroupOf V
  have hLZ : Λ ≤ stabSub (⊥ : Subgroup Y) := fun g _ u => by simp
  have hE1 : autSub A V ≠ ⊥ := by
    intro hE
    rw [hE, rk_bot] at hrkE
    omega
  rcases loc_shape hB42 hA21 hF hX h hFF with ⟨n, hn, hnat⟩ | hnat3 | halt
  ·
    have hst := d321k_stableMod_of_binaryNaturalSL_two hnat
    have hiso : ∀ g ∈ Γ, XMod.Iso ↥Λ (V.map g.toMonoidHom) V := fun g hg =>
      d321k_iso_conj_of_stableMod hLs hfaith hst (hΓn hg)
    have hnatΛ : BinaryNaturalSL Λ V ⊥ 2 n :=
      binaryNaturalSL_of_autSub hLs hLZ bot_le hfaith (by rwa [hbot])
    obtain ⟨K, hKf, hKfin, hK, π, hπ⟩ := hnatΛ
    obtain ⟨k, hds, hk⟩ := loc_directSum h.std.hyp.exp (loc_isIrr h) hπ hΓn hgen hiso
    have hk2 := loc_two_le h hk
    have hcount := loc_count h hA hAS hiso hk
    have hw := natL2_weight hnat hEN hEe
    rw [hrkE] at hw
    have hkle : k ≤ 2 := by
      by_contra hk3
      push Not at hk3
      nlinarith
    obtain rfl : k = 2 := le_antisymm hkle hk2
    exact Or.inr ⟨n, loc_isPSL_two h hn hnat, K, hKf, hKfin, hK, hds⟩
  ·
    have hΛ3 : IsPSL 3 2 1 ↥Λ := loc_isPSL_three h hnat3
    obtain ⟨hZ, hAut⟩ := loc_out_three hΛ3
    have hiso := d321k_iso_conj_of_out_two h hZ hAut
    have hnatΛ : BinaryNaturalSL Λ V ⊥ 3 1 :=
      binaryNaturalSL_of_autSub hLs hLZ bot_le hfaith (by rwa [hbot])
    obtain ⟨π, hπ⟩ := FFC.BinaryNaturalSL.exists_zmod hnatΛ
    obtain ⟨k, hds, hk⟩ := loc_directSum h.std.hyp.exp (loc_isIrr h) hπ hΓn hgen hiso
    have hk2 := loc_two_le h hk
    have hcount := loc_count h hA hAS hiso hk
    have hw := natL3_weight hnat3 hEe hE1
    rw [hrkE] at hw
    have hkle : k ≤ 4 := by
      by_contra hk5
      push Not at hk5
      nlinarith
    have hkge := loc_k_ge_four h hΛ3 hk2 hds
    obtain rfl : k = 4 := le_antisymm hkle hkge
    exact Or.inl ⟨hΛ3, hds⟩
  ·
    exfalso
    obtain ⟨e5⟩ := loc_alt5_equiv h halt
    obtain ⟨hZ, hAut⟩ := loc_out_alt5 e5
    have hiso := d321k_iso_conj_of_out_two h hZ hAut
    have halt' : AlternatingNatural Λ V ⊥ 5 :=
      alternatingNatural_of_autSub hLs hLZ bot_le hfaith (by rwa [hbot])
    obtain ⟨π, hπ⟩ := halt'
    obtain ⟨k, hds, hk⟩ := loc_directSum h.std.hyp.exp (loc_isIrr h) hπ hΓn hgen hiso
    have hk2 := loc_two_le h hk
    have hcount := loc_count h hA hAS hiso hk
    have hw := alt5_weight halt hEN hEe
    rw [hrkE] at hw
    have hkle : k ≤ 2 := by
      by_contra hk3
      push Not at hk3
      nlinarith
    exact loc_alt5_false h e5 hk2 hkle hds

end CFSG.Quasithin
