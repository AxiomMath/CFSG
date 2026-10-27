module

public import CFSG.Quasithin.Background.GoldschmidtE23SymTriv
public import CFSG.Quasithin.Background.GoldschmidtE23Two

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits B2F G6 Equiv

namespace GE23

section Theta

variable {V : Type} [CommGroup V]

theorem SymSpec.exists_theta {H D : Subgroup (MulAut V)} {ψ : Perm (Fin 5) →* MulAut V}
    {β : ↥(coreMod 5) →* V} (hS : SymSpec H D ψ β) :
    ∃ θ : ↥H ≃* Perm (Fin 5), e4.map ψ =
      Subgroup.closure {x | ∃ hx : x ∈ H, x ∈ D ∧ (θ ⟨x, hx⟩).IsSwap} := by
  let f : Perm (Fin 5) →* ↥H := ψ.codRestrict H hS.ψ_mem
  have hfi : Function.Injective f := fun a b hab => hS.ψ_inj (congrArg Subtype.val hab)
  have hfs : Function.Surjective f := fun x => by
    obtain ⟨σ, hσ⟩ := hS.exists_ψ x.2
    exact ⟨σ, Subtype.ext hσ⟩
  let e : Perm (Fin 5) ≃* ↥H := MulEquiv.ofBijective f ⟨hfi, hfs⟩
  refine ⟨e.symm, le_antisymm ?_ ?_⟩
  · rw [e4, MonoidHom.map_closure]
    refine Subgroup.closure_mono ?_
    rintro _ ⟨σ, hσ, rfl⟩
    have hσd8 : σ ∈ d8 := by
      rcases hσ with rfl | rfl
      · exact sa_mem_d8
      · exact sb_mem_d8
    have hsw : σ.IsSwap := by
      rcases hσ with rfl | rfl
      · exact ⟨0, 1, by decide, rfl⟩
      · exact ⟨2, 3, by decide, rfl⟩
    refine ⟨hS.ψ_mem σ, ?_, ?_⟩
    · rw [hS.syl]
      exact Subgroup.mem_map_of_mem ψ hσd8
    · have : e.symm ⟨ψ σ, hS.ψ_mem σ⟩ = σ := e.symm_apply_apply σ
      rw [this]
      exact hsw
  · refine (Subgroup.closure_le _).2 ?_
    rintro x ⟨hx, hxD, hsw⟩
    have hσ : ψ (e.symm ⟨x, hx⟩) = x := by
      have := e.apply_symm_apply ⟨x, hx⟩
      exact congrArg Subtype.val this
    have hσd8 : e.symm ⟨x, hx⟩ ∈ d8 := by
      rw [hS.syl] at hxD
      obtain ⟨τ, hτ, hτx⟩ := Subgroup.mem_map.1 hxD
      have : τ = e.symm ⟨x, hx⟩ := hS.ψ_inj (hτx.trans hσ.symm)
      rw [← this]
      exact hτ
    rcases isSwap_mem_d8 hσd8 hsw with h | h
    · rw [← hσ, h]
      exact Subgroup.mem_map_of_mem ψ sa_mem_e4
    · rw [← hσ, h]
      exact Subgroup.mem_map_of_mem ψ sb_mem_e4

end Theta

section Three

variable {Γ : Type} [Group Γ] [Finite Γ] {H T M V : Subgroup Γ} (hV : IsElemAbelian 2 V)

theorem e23_three_sym (hP4 : AsB15Part4) (hComp : B69.AsB69Component)
    (hone : B69One) (h22 : E2.E22StatementNoN) (h : MinParabolic H T M) (hsq : SQTKGroup ↥H)
    (hred : IsTwoReducedIn H V) (hJ : ¬ thompsonJ T ≤ Subgroup.centralizer (V : Set Γ))
    (hns : ¬ Group.IsSolvable ↥H)
    (hA5 : ∀ L ∈ B69.blkFamily (autI hV H), E2.IsA5Module L) :
    autI hV (baum T) = autI hV (thompsonJ T) ∧
    autI hV (thompsonJ T) = ⨆ L ∈ B69.blkFamily (autI hV H), (L ⊓ autI hV (thompsonJ T)) ∧
    ∀ L ∈ B69.blkFamily (autI hV H), Nat.card ↥(L ⊓ autI hV (thompsonJ T)) = 4 ∧
      ∃ θ : ↥L ≃* Equiv.Perm (Fin 5), L ⊓ autI hV (thompsonJ T) =
        Subgroup.closure {x | ∃ hx : x ∈ L, x ∈ autI hV T ∧ (θ ⟨x, hx⟩).IsSwap} := by
  classical
  have hT := h.isSylow
  have hHN : H ≤ Subgroup.normalizer (V : Set Γ) := hred.2.1
  have hVT : V ≤ T := (MinParabolic.le_pCoreOf_of_isTwoReduced hred).trans
    (B6.pCoreOf_two_le_of_isSylowTwoOf hT)
  have hTN : T ≤ Subgroup.normalizer (V : Set Γ) := hT.1.trans hHN
  have hHV : ¬ H ≤ Subgroup.centralizer (V : Set Γ) := fun hle =>
    hJ ((thompsonJ_le_self T).trans (hT.1.trans hle))
  have hJH : ¬ thompsonJ H ≤ Subgroup.centralizer (V : Set Γ) := fun hle =>
    hJ ((thompsonJ_le_thompsonJ_of_isSylowTwoOf hT).trans hle)
  obtain ⟨hFF, hstab, hJeqH, -⟩ := B2_7_of_not_le hV hred.1 hHN hJH
  have hB := blkCtx_star hV hP4 hComp h hsq hred hJ hns
  have hmp := minParabolic_star hV h hred hHV
  have hnsX := not_isSolvable_star hV h hred hHV hns
  have hX := isRankTwoQuotient_star hV hsq hHN
  have hsqX := sqtk_star hV hsq hHN
  have hKY := hmp.twoResidual_le_ffJ hB.hO2 hFF
  have hk2 : ∀ {H' : Subgroup (MulAut (IntMod V hV))} {k : ℕ},
      SymBlk (autI hV H) H' k → k = 2 := fun hS => hS.k_eq_two h22 hmp hsqX hX
  have hone' : ¬ IsStrongFFModule (autI hV H) :=
    hone (IntMod V hV) (fun v => IntMod.sq_eq_one v) (autI hV H) _ _ hsqX
      (minParabolic_star_top hV h hred hHV) (pCoreOf_top_star hV hred)
  have hsym : ∀ L, CFSG.Open.IsComponentOf L (autI hV H) →
      SymBlk (autI hV H) (B69.blk (autI hV H) L) 2 := by
    intro L hL
    rcases comp_type' hB hL with hN | ⟨k, hS⟩
    · exfalso
      obtain ⟨n, hn⟩ := (hN.natBlk hB hL).isL2Natural hB hKY
      have hmem : B69.blk (autI hV H) L ∈ B69.blkFamily (autI hV H) :=
        B69.mem_blkFamily.2 ⟨L, hL, rfl⟩
      have h5 := hA5 _ hmem
      rw [hN.1] at h5
      exact two_pow_mul_ne_120 n ((card_isL2Natural hn).symm.trans (card_isA5Module h5))
    · have hk := hk2 hS
      subst hk
      exact hS
  have hC : SymCtx (autI hV H) (autI hV T) (autI hV M) :=
    ⟨hB, hmp, hFF, hnsX, hone', hk2, hsym⟩
  have hPs : IsStableFF (autI hV T) (offenderImages hV T) :=
    (B2_7_of_not_le hV hVT hTN hJ).2.1
  obtain ⟨ψ, β, hspec⟩ := hC.exists_spec
  have hD : SymData (autI hV H) (autI hV T) (autI hV M) (offenderImages hV T) ψ β :=
    ⟨hC, hPs, hspec⟩
  have hJeq : autI hV (thompsonJ T) = ffJP (offenderImages hV T) (autI hV T) :=
    autI_thompsonJ hV hTN
  have hJN : thompsonJ T ≤ Subgroup.normalizer (V : Set Γ) := (thompsonJ_le_self T).trans hTN
  have hS : autI hV (baum T) = autI hV (thompsonJ T) := by
    refine le_antisymm ?_ (autI_mono hV (B2F.thompsonJ_le_baum T))
    have hbaum : autI hV (baum T) ≤ autI hV T ⊓ centSub (fixV (autI hV (thompsonJ T))) := by
      refine le_inf (autI_mono hV (B2F.baum_le T)) ?_
      intro φ hφ
      obtain ⟨x, hx, rfl⟩ := (mem_autI hV).1 hφ
      rw [mem_centSub]
      intro u hu
      have hu2 := (mem_fixV_autI hV hJN u).1 hu
      have hE : u.val ∈ omegaOneCenterOf (thompsonJ T) :=
        inf_centralizer_thompsonJ_le hV hVT ⟨u.val_mem, hu2⟩
      have hcomm : (x : Γ) * u.val = u.val * x :=
        (Subgroup.mem_centralizer_iff.1 hx.2 u.val hE).symm
      refine IntMod.val_injective ?_
      rw [convI_apply_val, hcomm, mul_inv_cancel_right]
    have := hbaum
    rw [hJeq] at this ⊢
    rwa [hD.centSub_eq] at this
  have hinf : ∀ L ∈ B69.blkFamily (autI hV H),
      L ⊓ autI hV (thompsonJ T) = e4.map (ψ L) := by
    intro L hL
    rw [inf_comm, hJeq]
    exact hD.ffJP_inf_eq hL
  refine ⟨hS, ?_, fun L hL => ?_⟩
  · calc autI hV (thompsonJ T) = ⨆ L ∈ B69.blkFamily (autI hV H), e4.map (ψ L) := by
          rw [hJeq]
          exact hD.ffJP_eq
      _ = ⨆ L ∈ B69.blkFamily (autI hV H), (L ⊓ autI hV (thompsonJ T)) :=
          iSup_congr fun L => iSup_congr fun hL => (hinf L hL).symm
  · refine ⟨?_, ?_⟩
    · rw [hinf L hL, Subgroup.card_map_of_injective (hspec L hL).ψ_inj, card_e4]
    · obtain ⟨θ, hθ⟩ := (hspec L hL).exists_theta
      refine ⟨θ, ?_⟩
      rw [hinf L hL, hθ]
      congr 1
      ext x
      constructor
      · rintro ⟨hx, hxD, hsw⟩
        exact ⟨hx, hxD.1, hsw⟩
      · rintro ⟨hx, hxT, hsw⟩
        exact ⟨hx, ⟨hxT, hx⟩, hsw⟩

end Three

end GE23

end CFSG.Quasithin
