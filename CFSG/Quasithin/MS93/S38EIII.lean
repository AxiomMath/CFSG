module

public import CFSG.Quasithin.MS93.S38EGSec
public import CFSG.Quasithin.MS93.S38EB
public import CFSG.Quasithin.MS93.S38EIdent
public import CFSG.Quasithin.MS93.S38ETypes

public section

namespace CFSG.Quasithin.MS93.S38E

open CFSG.Quasithin CFSG.Quasithin.Fan86.Univ CFSG.Quasithin.MS93 CFSG.QuasithinUnique
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open scoped commutatorElement

section Uniq

variable {Y : Type*} [CommGroup Y] [Finite Y]

theorem irrSec_commV_of_big (p : Pairing Y ℂˣ) {X K E : Subgroup (MulAut Y)}
    (hpX : p.IsInv X) (hKX : K ≤ X) (hEX : E ≤ X)
    (hKn : X ≤ Subgroup.normalizer (K : Set (MulAut Y))) (hKp : ⁅K, K⁆ = K)
    {e : ℕ} (hFF : (fixV E).index ≤ e)
    (hbig : ∀ W N : Subgroup Y, IrrSec X W N → NonCent K W N → e < aI E W N * cI E W N)
    (hK1 : NonCent K ⊤ ⊥) :
    IrrSec X (commV K) (commV K ⊓ fixV K) := by
  set W₀ := commV K with hW₀
  set M₀ := commV K ⊓ fixV K with hM₀
  have hW₀s : Stab X W₀ := stab_commV hKn
  have hFs : Stab X (fixV K) := stab_fixV hKn
  have hM₀s : Stab X M₀ := stab_inf hW₀s hFs
  have hKs : ∀ k ∈ K, ∀ y : Y, k y * y⁻¹ ∈ W₀ := fun k hk y =>
    Subgroup.subset_closure ⟨k, hk, y, rfl⟩
  have htriv : ∀ A : Subgroup Y, Stab K A → (∀ k ∈ K, ∀ a ∈ A, k a * a⁻¹ ∈ fixV K) →
      A ≤ fixV K := by
    intro A hA h a ha k hk
    have := perfect_trivial_of_two_step hKp hA (stab_bot K) h
      (fun k hk w hw => by rw [Subgroup.mem_bot, mul_inv_eq_one]; exact hw k hk) k hk a ha
    rwa [Subgroup.mem_bot, mul_inv_eq_one] at this
  have hc : cI E ⊤ ⊥ = aI E ⊤ ⊥ := cI_eq_aI_of_pairing p (hpX.mono hEX)
  have haY : aI E ⊤ ⊥ ≤ e := by rw [aI_top_bot]; exact hFF
  have hlt : M₀ < W₀ := by
    refine lt_of_le_of_ne inf_le_left fun heq => ?_
    have hW₀F : W₀ ≤ fixV K := by rw [← heq]; exact inf_le_right
    obtain ⟨k, hk, y, -, hy⟩ := hK1
    apply hy
    rw [Subgroup.mem_bot, mul_inv_eq_one]
    have h1 := htriv ⊤ (stab_top K) (fun k hk a _ => hW₀F (hKs k hk a)) (Subgroup.mem_top y)
    exact h1 k hk
  refine ⟨hlt, hW₀s, hM₀s, fun J hJ hMJ hJW => ?_⟩
  by_contra hcon
  push Not at hcon
  obtain ⟨hJM, hJW'⟩ := hcon
  have hMJ' : M₀ < J := lt_of_le_of_ne hMJ (Ne.symm hJM)
  have hJW'' : J < W₀ := lt_of_le_of_ne hJW hJW'
  obtain ⟨S, hS, hMS, hSJ, hSmin⟩ := exists_minimal hMJ' hJ
  obtain ⟨N', hN', hJN', hN'W, hN'max⟩ := exists_maximal hJW'' hJ
  have hirrS : IrrSec X S M₀ := ⟨hMS, hS, hM₀s, fun J' hJ' h1 h2 => by
    rcases eq_or_lt_of_le h1 with h | h
    · exact Or.inl h.symm
    · exact Or.inr (hSmin J' hJ' h h2)⟩
  have hirrW : IrrSec X W₀ N' := ⟨hN'W, hW₀s, hN', fun J' hJ' h1 h2 => by
    rcases eq_or_lt_of_le h2 with h | h
    · exact Or.inr h
    · exact Or.inl (hN'max J' hJ' h1 h)⟩
  have hSW : S ≤ W₀ := hSJ.trans hJW
  have hncS : NonCent K S M₀ := by
    by_contra hnc
    unfold NonCent at hnc
    push Not at hnc
    have h1 : S ≤ fixV K := htriv S (hS.mono hKX) fun k hk a ha => (hnc k hk a ha).2
    exact (lt_irrefl M₀) (lt_of_lt_of_le hMS (le_inf hSW h1))
  have hncW : NonCent K W₀ N' := by
    by_contra hnc
    unfold NonCent at hnc
    push Not at hnc
    have h1 := perfect_trivial_of_two_step hKp (stab_top K) (hN'.mono hKX)
      (fun k hk y _ => hKs k hk y) hnc
    have h2 : W₀ ≤ N' := by
      rw [hW₀, commV, Subgroup.closure_le]
      rintro _ ⟨k, hk, y, rfl⟩
      exact h1 k hk y (Subgroup.mem_top y)
    exact (lt_irrefl N') (lt_of_lt_of_le hN'W h2)
  have hEs : ∀ A : Subgroup Y, Stab X A → Stab E A := fun A hA => hA.mono hEX
  have hSN' : S ≤ N' := hSJ.trans hJN'
  have hA : aI E W₀ N' * aI E S M₀ ≤ aI E ⊤ ⊥ := by
    have h1 := aI_mul_le (E := E) (W := W₀) (W' := N') (N := M₀) (hEs N' hN')
      (hMS.le.trans hSN') hN'W.le
    have h2 := aI_le_of_le (E := E) (W := N') (W' := S) (N := M₀) (hEs S hS) hMS.le hSN'
    have h3 := aI_le_of_le (E := E) (W := ⊤) (W' := W₀) (N := M₀) (hEs W₀ hW₀s) hlt.le le_top
    have h4 := aI_le_of_le' (E := E) (W := ⊤) (W' := M₀) (N := ⊥) (hEs M₀ hM₀s) bot_le le_top
    calc aI E W₀ N' * aI E S M₀ ≤ aI E W₀ N' * aI E N' M₀ := Nat.mul_le_mul_left _ h2
      _ ≤ aI E W₀ M₀ := h1
      _ ≤ aI E ⊤ M₀ := h3
      _ ≤ aI E ⊤ ⊥ := h4
  have hC : cI E W₀ N' * cI E S M₀ ≤ cI E ⊤ ⊥ := by
    have h1 := cI_mul_le (E := E) (W := W₀) (W' := N') (N := M₀) (hEs N' hN')
      (hMS.le.trans hSN') hN'W.le
    have h2 := cI_le_of_le (E := E) (W := N') (W' := S) (N := M₀) (hEs S hS) hMS.le hSN'
    have h3 := cI_le_of_le (E := E) (W := ⊤) (W' := W₀) (N := M₀) (hEs W₀ hW₀s) hlt.le le_top
    have h4 := cI_le_of_le' (E := E) (W := ⊤) (W' := M₀) (N := ⊥) (hEs M₀ hM₀s) bot_le le_top
    calc cI E W₀ N' * cI E S M₀ ≤ cI E W₀ N' * cI E N' M₀ := Nat.mul_le_mul_left _ h2
      _ ≤ cI E W₀ M₀ := h1
      _ ≤ cI E ⊤ M₀ := h3
      _ ≤ cI E ⊤ ⊥ := h4
  have hb1 := hbig W₀ N' hirrW hncW
  have hb2 := hbig S M₀ hirrS hncS
  have hA' : aI E W₀ N' * aI E S M₀ ≤ e := hA.trans haY
  have hC' : cI E W₀ N' * cI E S M₀ ≤ e := (hC.trans hc.le).trans haY
  have key : (aI E W₀ N' * cI E W₀ N') * (aI E S M₀ * cI E S M₀) ≤ e * e := by
    calc (aI E W₀ N' * cI E W₀ N') * (aI E S M₀ * cI E S M₀)
        = (aI E W₀ N' * aI E S M₀) * (cI E W₀ N' * cI E S M₀) := by ring
      _ ≤ e * e := Nat.mul_le_mul hA' hC'
  have : (e + 1) * (e + 1) ≤ (aI E W₀ N' * cI E W₀ N') * (aI E S M₀ * cI E S M₀) :=
    Nat.mul_le_mul hb1 hb2
  nlinarith

end Uniq

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G}

theorem exists_isXOff_imM_eq (h : PUHyp M T L) (hD : XOffData M T)
    {α' : Vtx (puAmalgam h.le)} (hc : IsCritical _ (baseA _) α')
    (hgeo : geo _ (baseA _) α' 1 = baseB _) :
    ∃ F : Subgroup G, F ≤ T ∧ IsXOff M T F ∧ imM h.le F = XM (puAmalgam h.le) α' ∧
      (Qv (puAmalgam h.le) (baseA _)).relIndex (XM _ α') = (pCoreOf 2 M).relIndex F := by
  have hb0 := h.critDist_pos
  have hc' := ms22_iii _ h.hyp20 hb0 h.centHyp hc
  have hoff := (isOffAt_xm h.hyp20 hb0 h.centHyp hc
    (h.offDataAt hD (PU.isMVtx_baseA _) (adj_geo_one_of_isCritical _ hb0 hc))
    (h.offDataAt hD hc'.1 (adj_geo_one_of_isCritical _ hb0 hc'))).1
  rw [hgeo] at hoff
  have hXT : XM (puAmalgam h.le) α' ≤ imM h.le T := by
    have := hoff.1
    rwa [puAmalgam.qv_baseB] at this
  obtain ⟨F, hFT, hF⟩ := exists_imM_eq_of_le h.le hXT
  refine ⟨F, hFT, (h.isOffAt_base_iff hFT).mp (hF ▸ hoff), hF, ?_⟩
  rw [← hF, puAmalgam.qv_baseA_eq_pCoreOf h.le h.isPGroup h.pCore_le,
    imM_relIndex' h.le _ (hFT.trans h.le)]

namespace EndSetup

variable (h : PUHyp M T L) {α' : Vtx (puAmalgam h.le)} {e : ℕ}
  (hS : EndSetup (Vv (puAmalgam h.le) (baseA _)) (stab _ (baseA _)) (puTrans h.le L (baseA _))
    (Qv _ (baseB _)) (Qv _ (baseA _)) (XM _ α') e)
  (lam : ↥⁅Vv (puAmalgam h.le) (baseA _), Vv (puAmalgam h.le) (baseA _)⁆ →* ℂˣ)
  (hlam1 : ∀ c : ↥⁅Vv (puAmalgam h.le) (baseA _), Vv (puAmalgam h.le) (baseA _)⁆,
    (c : (puAmalgam h.le).Universal) ∈
      ⁅⁅Vv (puAmalgam h.le) (baseA _), Vv (puAmalgam h.le) (baseA _)⁆, Qv _ (baseB _)⁆ →
      lam c = 1)
  (W N : Subgroup (hS.YM lam)) (hirr : IrrSec (hS.rho lam hlam1).range W N)

noncomputable abbrev gRhoM : ↥M →* MulAut (Sec W N) :=
  (hS.gSecRho lam hlam1 W N hirr).comp (phiM h.le)

theorem range_gRhoM :
    (hS.gRhoM h lam hlam1 W N hirr).range = (hS.gSecRho lam hlam1 W N hirr).range :=
  hS.range_gSecRho_comp lam hlam1 W N hirr (phiM h.le) (phiM_surjective h.le)

theorem map_gRhoM_eq {F : Subgroup G} (hFX : imM h.le F = XM _ α') :
    (F.subgroupOf M).map (hS.gRhoM h lam hlam1 W N hirr) = hS.geS lam hlam1 W N hirr := by
  rw [← Subgroup.map_map]
  congr 1
  ext g
  rw [Subgroup.mem_map, Subgroup.mem_subgroupOf, ← hFX]
  constructor
  · rintro ⟨f, hf, rfl⟩
    exact ⟨f, hf, rfl⟩
  · rintro ⟨f, hf, hfg⟩
    exact ⟨f, hf, Subtype.ext hfg⟩

variable (hnc : NonCent (hS.kY lam hlam1) W N)
include hirr hnc

theorem isIrrRep_gRhoM : IsIrrRep L (hS.gRhoM h lam hlam1 W N hirr) where
  sq := hS.sq_gSM lam W N
  pCore m hm := by
    have hmQ : ((phiM h.le m : ↥(stab _ _)) : (puAmalgam h.le).Universal) ∈
        Qv (puAmalgam h.le) (baseA _) := by
      rw [phiM_coe, puAmalgam.qv_baseA_eq_pCoreOf h.le h.isPGroup h.pCore_le]
      exact ⟨m, Subgroup.mem_subgroupOf.mpr hm, rfl⟩
    exact hS.gSecRho_comp_eq_one lam hlam1 W N hirr hnc (phiM h.le) hS.qa_le hS.nQa hS.qa2 hmQ
  irr := hS.irr_gSecRho_comp lam hlam1 W N hirr (phiM h.le) (phiM_surjective h.le)
  ne := by
    obtain ⟨x, hxL, hx1⟩ :=
      hS.exists_gSecRho_comp_ne_one lam hlam1 W N hirr hnc (phiM h.le) (phiM_surjective h.le)
    refine ⟨x, ?_, hx1⟩
    rw [phiM_coe, puTrans_baseA h.le h.L_subgroupOf_normal] at hxL
    obtain ⟨y, hy, hyx⟩ := hxL
    rw [← (puAmalgam h.le).ofA_injective hyx]
    exact Subgroup.mem_subgroupOf.mp hy

theorem isFFModule_gRhoM (he2 : 2 ≤ e) : IsFFModule (hS.gRhoM h lam hlam1 W N hirr).range := by
  rw [range_gRhoM]
  have : Finite (Sec W N) := hS.finite_gSM lam W N
  exact ⟨hS.geS lam hlam1 W N hirr, Subgroup.map_le_range _ _,
    hS.geS_ne_bot lam hlam1 W N hirr hnc he2, hS.isElemAbelian2_geS lam hlam1 W N hirr,
    hS.card_le_card_geS_mul lam hlam1 W N hirr hnc⟩

theorem lt_aI_mul_cI (h14 : MS14AS) (hSQ : SQTKQuot) (hT : S32.TypeFacts)
    (hB : SL3SecBound) (hcent : T ⊓ Subgroup.centralizer (Z0q M T : Set G) = pCoreOf 2 M)
    (hX : IsDoubleSL3U M T L) {F : Subgroup G} (hF : IsXOff M T F)
    (hFX : imM h.le F = XM _ α') (heF : e = (pCoreOf 2 M).relIndex F) (he2 : 2 ≤ e) :
    e < aI (hS.eY lam hlam1) W N * cI (hS.eY lam hlam1) W N := by
  have : Finite (Sec W N) := hS.finite_gSM lam W N
  have hρ := hS.isIrrRep_gRhoM h lam hlam1 W N hirr hnc
  have hFF := hρ.ffHyp h hSQ (hS.isFFModule_gRhoM h lam hlam1 W N hirr hnc he2)
  obtain ⟨-, -, hcase, -⟩ := h14 _ (hS.sq_gSM lam W N) _ _ hFF
  obtain ⟨m, hm, hLm⟩ := card_lstar_of_isDoubleSL3U h hX
  rcases hcase with hsl3 | hhat | hsp4 | hg2
  · obtain ⟨n, Fq, _, _, hn, hFq, ⟨eK⟩, -, hreal⟩ := hsl3
    have hbound := hB G M T L h hcent hX F hF (Sec W N) _ hρ Fq hreal
    rw [map_gRhoM_eq h hS lam hlam1 W N hirr hFX,
      hS.index_fixV_geS lam hlam1 W N hirr, hS.card_commV_geS lam hlam1 W N hirr] at hbound
    obtain ⟨-, -, n₀, K₀, _, _, α, hK₀, hα, hnat⟩ := hX
    have hcharFq : CharP Fq 2 := FFC.charP_two_of_card_pow hFq
    have hq := S38EB.card_field_eq h hρ hK₀ hα hnat eK.symm
    have he : e = Fintype.card K₀ ^ 2 :=
      heF.trans (h.relIndex_of_isXOff_of_doubleNat hK₀ hα hnat hF)
    rw [hq, Nat.card_eq_fintype_card] at hbound
    have h2 : 2 ≤ Fintype.card K₀ := by
      rw [hK₀]
      have h1 : 1 ≤ n₀ := by
        by_contra h0
        push Not at h0
        have : n₀ = 0 := by omega
        rw [this, pow_zero] at hK₀
        exact absurd hK₀ (by have := Fintype.one_lt_card (α := K₀); omega)
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ n₀ := Nat.pow_le_pow_right (by norm_num) h1
    calc e = Fintype.card K₀ ^ 2 := he
      _ < Fintype.card K₀ ^ 3 := Nat.pow_lt_pow_right (by omega) (by norm_num)
      _ ≤ _ := hbound
  · exact absurd (hLm.symm.trans (card_lstar_of_ffCaseHatA6 hρ h hhat))
      (S32.ordA_two_ne_360 hm)
  · rcases hsp4 with ⟨n, hn, hbin⟩ | halt
    · exact absurd ((card_lstar_of_sp4Nat hρ h hn hbin).symm.trans hLm)
        (ordBC_two_ne_ordA_two (by omega) hm)
    · exact absurd (hLm.symm.trans (card_lstar_of_altNat hρ h halt)) (S32.ordA_two_ne_360 hm)
  · rcases card_lstar_of_ffCaseG2 hρ h hT hg2 with ⟨n, hn, h1⟩ | h1
    · exact absurd (h1.symm.trans hLm) (ordG2_ne_ordA_two (by omega) hm)
    · exact absurd (hLm.symm.trans h1) (S32.ordA_two_ne_6048 hm)

end EndSetup

end CFSG.Quasithin.MS93.S38E
