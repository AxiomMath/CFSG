module

public import CFSG.Quasithin.Background.H16TwoM22PfC
public import CFSG.Quasithin.Background.HMathieuCodeCent
public import CFSG.Quasithin.Background.H16TwoM22

public section

namespace CFSG.Quasithin.H.Mathieu.H16Pf

open CFSG.Monster.Code CFSG.Quasithin.H.Mathieu CFSG.Open CFSG.Quasithin.SzN15

theorem pCoreOf_map_inj {X G : Type} [Group X] [Group G] (f : X →* G)
    (hf : Function.Injective f) (K : Subgroup X) :
    pCoreOf 2 (K.map f) = (pCoreOf 2 K).map f := by
  unfold pCoreOf
  rw [← CFSG.LieType.BorelTits.map_pCore_mulEquiv 2 (K.equivMapOfInjective f hf),
    Subgroup.map_map, Subgroup.map_map]
  rfl

@[expose] def fixW10Sub (R : Subgroup (Equiv.Perm (Fin 24))) : Subgroup W10 where
  carrier := fixW10 R
  mul_mem' ha hb x hx := by rw [map_mul, ha x hx, hb x hx]
  one_mem' x _ := map_one _
  inv_mem' {a} ha x hx := (map_inv _ a).trans (congrArg (·⁻¹) (ha x hx))

theorem card_fixW10Sub
    {N : Subgroup (Equiv.Perm (Fin 24))} (hN : N ≤ mog22) (hc : Nat.card N = 5760) :
    Nat.card (fixW10Sub (pCoreOf 2 N)) = 2 := by
  obtain ⟨w₀, hw₀, h⟩ := fixW10_pCoreOf hN hc
  change Nat.card ↥(fixW10 (pCoreOf 2 N)) = 2
  rw [h, Nat.card_coe_set_eq, Set.ncard_pair (Ne.symm hw₀)]

theorem stmtH16_2_1M22_holds :
    StmtH16_2_1M22 := by
  intro W _ _ L U Z hL N hNL hN
  obtain ⟨x, y, hxy, π, hπs, hZU, -, hUinv, -, -, -, β, hβs, hβ1, hβa⟩ := hL
  obtain ⟨τ, hτ, hτ0, hτ1⟩ := CFSG.Monster.B.TwoA.autPerm_maps_two x y hxy
  have hC := (preserves_iff_of_mem hτ).2
  have hn : ∀ m, m ∈ golayC ⊓ pairKer x y ↔ G6.permAct 24 τ⁻¹ m ∈ golayC ⊓ pairKer 0 1 := by
    intro m
    rw [mem_code22, Subgroup.mem_inf, mem_pairKer, hC m]
    refine and_congr Iff.rfl ?_
    rw [toAdd_permAct]
    simp only [permWord, Function.comp_apply, inv_inv, hτ0, hτ1]
  have hd := zpowers_allOnes_iff τ
  have hΓxy : ∀ σ ∈ AutPerm ⊓ stab x ⊓ stab y,
      Preserves (golayC ⊓ pairKer x y) (Subgroup.zpowers (G6.allOnes 24)) σ := by
    intro σ hσ
    have hσx : σ x = x := (mem_stab_iff x σ).1 hσ.1.2
    have hσy : σ y = y := (mem_stab_iff y σ).1 hσ.2
    refine ⟨fun m hm => ?_, fun _ hm => permAct_mem_zpowers_allOnes σ hm⟩
    obtain ⟨hmC, hmxy⟩ := hm
    refine ⟨(preserves_cocode hσ.1.1).2 m hmC, (mem_pairKer x y _).2 ?_⟩
    rw [toAdd_permAct]
    simp only [permWord, Function.comp_apply]
    have hx' : σ⁻¹ x = x := by rw [Equiv.Perm.inv_eq_iff_eq]; exact hσx.symm
    have hy' : σ⁻¹ y = y := by rw [Equiv.Perm.inv_eq_iff_eq]; exact hσy.symm
    rw [hx', hy']
    exact hmxy
  have hσ : ∀ γ : ↥(AutPerm ⊓ stab x ⊓ stab y),
      τ⁻¹ * (γ : Equiv.Perm (Fin 24)) * τ ∈ mog22 := by
    rintro ⟨γ, ⟨hγ, hγx⟩, hγy⟩
    have hτ0' : τ⁻¹ x = 0 := by rw [← hτ0]; simp
    have hτ1' : τ⁻¹ y = 1 := by rw [← hτ1]; simp
    refine ⟨⟨AutPerm.mul_mem (AutPerm.mul_mem (AutPerm.inv_mem hτ) hγ) hτ,
      (mem_stab_iff 0 _).2 ?_⟩, (mem_stab_iff 1 _).2 ?_⟩
    · rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, hτ0, (mem_stab_iff x γ).1 hγx, hτ0']
    · rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, hτ1, (mem_stab_iff y γ).1 hγy, hτ1']
  set c' := code22Coords.conj τ hn hd
  set ρ := rhoC10 mog22 mog22_le_mog22plus
  let κb : ↥(golayC ⊓ pairKer x y) ⧸ (Subgroup.zpowers (G6.allOnes 24)).subgroupOf
      (golayC ⊓ pairKer x y) →* W10 :=
    QuotientGroup.lift _ (c'.κ.comp (Subgroup.subtype _)) fun m hm =>
      (c'.ker_iff m.1 m.2).2 (Subgroup.mem_subgroupOf.1 hm)
  have hκb : ∀ m, κb (QuotientGroup.mk m) = c'.κ m := fun _ => rfl
  obtain ⟨β', hβ'⟩ : ∃ β' : ↥U →* W10, ∀ u, β' u = κb (β u) := ⟨κb.comp β, fun _ => rfl⟩
  have hβ's : Function.Surjective β' := fun w => by
    obtain ⟨u, hu⟩ := hβs (QuotientGroup.mk ⟨c'.lift w, c'.lift_mem w⟩)
    exact ⟨u, by rw [hβ', hu]; exact c'.κ_lift w⟩
  have hker : β'.ker = Z.subgroupOf U := by
    ext u
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, ← hβ1]
    obtain ⟨m, hm⟩ := QuotientGroup.mk_surjective (β u)
    rw [hβ', ← hm]
    change c'.κ m.1 = 1 ↔ _
    rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    exact c'.ker_iff m.1 m.2
  have hequi : ∀ (γ : ↥(AutPerm ⊓ stab x ⊓ stab y)) (u : ↥U)
      (hu : ((π γ : ↥L) : MulAut W) u ∈ U), β' ⟨_, hu⟩ = ρ ⟨_, hσ γ⟩ (β' u) := by
    intro γ u hu
    obtain ⟨m, hm⟩ := QuotientGroup.mk_surjective (β u)
    have hm' : G6.permAct 24 (γ : Equiv.Perm (Fin 24)) m.1 ∈ golayC ⊓ pairKer x y :=
      (hΓxy γ γ.2).1 m.1 m.2
    rw [hβ', hβa γ u m hu hm' hm.symm, hβ', ← hm]
    change c'.κ (G6.permAct 24 (γ : Equiv.Perm (Fin 24)) m.1) = ρ ⟨_, hσ γ⟩ (c'.κ m.1)
    rw [SecCoords.κ_permAct c' (hΓxy γ γ.2) m.2, SecCoords.conj_rhoHom]
    rfl
  have hπi : Function.Injective π := by
    rw [injective_iff_map_eq_one]
    intro γ hγ
    let γ0 : ↥(AutPerm ⊓ stab x ⊓ stab y) := γ
    have hfix : ∀ w, ρ ⟨_, hσ γ0⟩ w = w := by
      intro w
      obtain ⟨u, rfl⟩ := hβ's w
      have hu : ((π γ : ↥L) : MulAut W) u ∈ U := by rw [hγ]; exact u.2
      rw [← hequi γ0 u hu]
      congr 1
      exact Subtype.ext (by show ((π γ : ↥L) : MulAut W) u = u; rw [hγ]; rfl)
    have h1 : (⟨_, mog22_le_mog22plus (hσ γ0)⟩ : ↥mog22plus) = 1 :=
      rhoC10_mog22plus_injective (MulEquiv.ext fun w => by rw [map_one]; exact hfix w)
    have h2 : τ⁻¹ * (γ0 : Equiv.Perm (Fin 24)) * τ = 1 := congrArg Subtype.val h1
    have h3 : (γ0 : Equiv.Perm (Fin 24)) = 1 := by
      have : (γ0 : Equiv.Perm (Fin 24)) = τ * (τ⁻¹ * γ0 * τ) * τ⁻¹ := by group
      rw [this, h2]; simp
    exact Subtype.ext h3
  obtain ⟨K', hK'⟩ : ∃ K', K' = (N.subgroupOf L).comap π := ⟨_, rfl⟩
  obtain ⟨f, hfv⟩ : ∃ f : ↥(AutPerm ⊓ stab x ⊓ stab y) →* Equiv.Perm (Fin 24),
      ∀ γ, f γ = τ⁻¹ * (γ : Equiv.Perm (Fin 24)) * τ :=
    ⟨(MulAut.conj τ⁻¹).toMonoidHom.comp (Subgroup.subtype _), fun γ => by simp⟩
  have hf : Function.Injective f := fun a b hab => by
    rw [hfv, hfv] at hab
    exact Subtype.ext (mul_left_cancel (mul_right_cancel hab))
  have hg : Function.Injective (L.subtype.comp π) := (Subgroup.subtype_injective _).comp hπi
  have hNK : N = K'.map (L.subtype.comp π) := by
    rw [hK', ← Subgroup.map_map, Subgroup.map_comap_eq_self_of_surjective hπs,
      Subgroup.map_subgroupOf_eq_of_le hNL]
  have hNc : K'.map f ≤ mog22 := by rintro _ ⟨γ, -, rfl⟩; rw [hfv]; exact hσ γ
  have hcard : Nat.card (K'.map f) = 5760 := by
    rw [← hN, hNK]
    exact (Nat.card_congr (K'.equivMapOfInjective f hf).toEquiv).symm.trans
      (Nat.card_congr (K'.equivMapOfInjective _ hg).toEquiv)
  have hpN : pCoreOf 2 N = (pCoreOf 2 K').map (L.subtype.comp π) := by
    rw [hNK, pCoreOf_map_inj _ hg]
  have hpNc : pCoreOf 2 (K'.map f) = (pCoreOf 2 K').map f := pCoreOf_map_inj _ hf K'
  set F := fixW10Sub (pCoreOf 2 (K'.map f))
  have hfixU : (fixMod (pCoreOf 2 N) U Z).subgroupOf U = F.comap β' := by
    ext u
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_comap]
    constructor
    · rintro ⟨-, hu⟩ σ hσx
      obtain ⟨γ, hγ, hγσ⟩ : ∃ γ ∈ pCoreOf 2 K', f γ = σ := by
        rw [hpNc] at hσx; exact hσx.1
      have hr : ((π γ : ↥L) : MulAut W) ∈ pCoreOf 2 N := by rw [hpN]; exact ⟨γ, hγ, rfl⟩
      have hru := hu _ hr
      have hu' : ((π γ : ↥L) : MulAut W) u ∈ U := hUinv (π γ) u u.2
      have h1 : β' u = β' ⟨_, hu'⟩ := (MonoidHom.eq_iff β').2 (by
        rw [hker, Subgroup.mem_subgroupOf]
        rw [Subgroup.coe_mul, Subgroup.coe_inv, mul_comm]
        simpa [mul_inv_rev] using Z.inv_mem hru)
      rw [hequi γ u hu'] at h1
      have he : (⟨σ, hσx.2⟩ : ↥mog22) = ⟨_, hσ γ⟩ := Subtype.ext (hγσ.symm.trans (hfv γ))
      rw [he]
      exact h1.symm
    · intro hu
      refine ⟨u.2, fun r hr => ?_⟩
      rw [hpN] at hr
      obtain ⟨γ, hγ, rfl⟩ := hr
      have hu' : ((π γ : ↥L) : MulAut W) u ∈ U := hUinv (π γ) u u.2
      have hσx : f γ ∈ pCoreOf 2 (K'.map f) ⊓ mog22 := ⟨by rw [hpNc]; exact ⟨γ, hγ, rfl⟩, hNc
        (CFSG.LieType.BorelTits.pCoreOf_le 2 _ (by rw [hpNc]; exact ⟨γ, hγ, rfl⟩))⟩
      have h1 := hu _ hσx
      have he : (⟨f γ, hσx.2⟩ : ↥mog22) = ⟨_, hσ γ⟩ := Subtype.ext (hfv γ)
      rw [he, ← hequi γ u hu'] at h1
      have h2 := (MonoidHom.eq_iff β').1 h1.symm
      rw [hker, Subgroup.mem_subgroupOf] at h2
      rw [Subgroup.coe_mul, Subgroup.coe_inv, mul_comm] at h2
      simpa [mul_inv_rev] using Z.inv_mem h2
  have hF : Nat.card F = 2 := card_fixW10Sub hNc hcard
  have hW : Nat.card W10 = 1024 := by
    rw [Nat.card_congr (Multiplicative.toAdd : W10 ≃ (Fin 10 → ZMod 2)), Nat.card_fun,
      Nat.card_zmod, Nat.card_fin]
    norm_num
  have hU : Nat.card U = Nat.card Z * 1024 := by
    have h := (β'.ker).card_mul_index
    rw [Subgroup.index_ker, MonoidHom.range_eq_top.2 hβ's, Subgroup.card_top, hW, hker,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZU).toEquiv] at h
    exact h.symm
  have hidx : (F.comap β').index * 2 = 1024 := by
    have := F.card_mul_index
    rw [hF, hW] at this
    rw [Subgroup.index_comap_of_surjective _ hβ's]
    omega
  have h2 := (F.comap β').card_mul_index
  have h3 : Nat.card (F.comap β') = Nat.card (fixMod (pCoreOf 2 N) U Z) := by
    rw [← hfixU]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (fun _ hv => hv.1 : fixMod (pCoreOf 2 N) U Z ≤ U)).toEquiv
  rw [h3, hU] at h2
  have hpos : 0 < (F.comap β').index := by omega
  refine Nat.eq_of_mul_eq_mul_right hpos ?_
  rw [h2]
  calc Nat.card Z * 1024 = Nat.card Z * ((F.comap β').index * 2) := by rw [hidx]
    _ = 2 * Nat.card Z * (F.comap β').index := by ring

end CFSG.Quasithin.H.Mathieu.H16Pf
