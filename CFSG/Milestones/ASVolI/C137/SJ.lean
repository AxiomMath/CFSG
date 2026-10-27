module

public import CFSG.Milestones.ASVolI.C137.SCtx
public import CFSG.Milestones.ASVolI.C137.SIrr
public import CFSG.Quasithin.H13.GoldschmidtC137Data

public section

namespace CFSG.ASVolI

open Subgroup CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Blueprint CFSG.ASVolI.ChC
open CFSG.Quasithin.L3 CFSG.Quasithin.H13.U3 CFSG.Quasithin.H13.U3.GC137

variable {G : Type} [Group G]

@[expose] def burnsideC137_planeSub (S : Finset Vec) (hS : IsPlane S) :
    Submodule (ZMod 2) Vec where
  carrier := {v | v ∈ S}
  add_mem' := fun {a b} ha hb => hS.2.2 a ha b hb
  zero_mem' := hS.2.1
  smul_mem' := fun c x hx => by
    rcases (by decide : ∀ c : ZMod 2, c = 0 ∨ c = 1) c with rfl | rfl
    · rw [zero_smul]; exact hS.2.1
    · rw [one_smul]; exact hx

theorem burnsideC137_finrank_planeSub (S : Finset Vec) (hS : IsPlane S) :
    Module.finrank (ZMod 2) (burnsideC137_planeSub S hS) = 2 := by
  have h1 : Nat.card (burnsideC137_planeSub S hS) = 4 := by
    rw [← hS.1]
    exact burnsideC137_natCard_eq _ S fun v => Iff.rfl
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod] at h1
  have h2 : (2 : ℕ) ^ Module.finrank (ZMod 2) (burnsideC137_planeSub S hS) = 2 ^ 2 := by
    rw [h1]; norm_num
  exact Nat.pow_right_injective le_rfl h2

namespace burnsideC137_SCtx

variable [Finite G] {X T L P U U₁ U₂ : Subgroup G} {α : ↥L →* Γ}
  {β₁ : ↥U₁ →* Multiplicative Vec} {β₂ : ↥U₂ →* Multiplicative Vec}
  (h : burnsideC137_SCtx X T L P U α U₁ U₂ β₁ β₂)
include h

theorem jStruct (hst : IsStableFF (autI h.hU X) (C124.offenderImagesConjIn h.hU X (pCoreOf 2 P)))
    (hJ : ¬ thompsonJ (pCoreOf 2 P) ≤ centralizer (U : Set G)) :
    ∃ (A₀ : Subgroup G) (S : Finset Vec), IsMaxElemAbelian (pCoreOf 2 P) A₀ ∧ IsPlane S ∧
      autI h.hU A₀ ≤ autI h.hU L ∧
      (∀ a : ↥(autI h.hU L), (a : MulAut (IntMod U h.hU)) ∈ autI h.hU A₀ ↔
        burnsideC137_ψ h.hs h.hU a ∈ BS S) ∧
      Nat.card (fixV (autI h.hU A₀)) = 16 ∧
      autI h.hU (thompsonJ (pCoreOf 2 P)) = autI h.hU A₀ := by
  set R := pCoreOf 2 P with hR
  have hRN : R ≤ normalizer (U : Set G) := h.hRX.trans h.hXN
  obtain ⟨A₀, hA₀, hA₀C⟩ : ∃ A₀, IsMaxElemAbelian R A₀ ∧ ¬ A₀ ≤ centralizer (U : Set G) := by
    by_contra hne
    push Not at hne
    exact hJ (iSup₂_le fun A hA => hne A hA)
  have hA₀1 : autI h.hU A₀ ≠ ⊥ := fun hb =>
    hA₀C ((autI_eq_bot_iff h.hU (hA₀.1.trans hRN)).1 hb)
  obtain ⟨hBL, S, hS, hAS, -, h16⟩ := h.offImg hst hA₀ hA₀1
  have hA₀R : autI h.hU A₀ ≤ autI h.hU R := autI_mono h.hU hA₀.1
  refine ⟨A₀, S, hA₀, hS, hBL, hAS, h16, le_antisymm ?_
    (autI_mono h.hU (le_iSup₂_of_le A₀ hA₀ le_rfl))⟩
  have hJle : thompsonJ R ≤ starPreIn h.hU R (autI h.hU A₀) := by
    refine iSup₂_le fun A hA => fun a ha => ?_
    have haR : a ∈ R := hA.1 ha
    refine (mem_starPreIn).2 ⟨haR, hRN haR, ?_⟩
    have hmem : convI h.hU ⟨a, hRN haR⟩ ∈ autI h.hU A := convI_mem_autI h.hU ha (hRN haR)
    by_cases hA1 : autI h.hU A = ⊥
    · rw [hA1, Subgroup.mem_bot] at hmem
      rw [hmem]
      exact one_mem _
    · obtain ⟨hBL', S', hS', hAS', -, -⟩ := h.offImg hst hA hA1
      have hSS : S' = S := h.plane_unique (autI_mono h.hU hA.1) hA₀R hS' hS hAS' hAS
      have hL' := hBL' hmem
      have := (hAS' ⟨_, hL'⟩).1 hmem
      rw [hSS] at this
      exact (hAS ⟨_, hL'⟩).2 this
  calc autI h.hU (thompsonJ R) ≤ autI h.hU (starPreIn h.hU R (autI h.hU A₀)) :=
        autI_mono h.hU hJle
    _ = autI h.hU A₀ := autI_starPreIn h.hU hRN hA₀R

theorem pStab {A₀ : Subgroup G} {S : Finset Vec} (hS : IsPlane S)
    (hAS : ∀ a : ↥(autI h.hU L), (a : MulAut (IntMod U h.hU)) ∈ autI h.hU A₀ ↔
      burnsideC137_ψ h.hs h.hU a ∈ BS S)
    (hJeq : autI h.hU (thompsonJ (pCoreOf 2 P)) = autI h.hU A₀) {x : G} (hx : x ∈ P) :
    ∃ l : ↥L, (l : G)⁻¹ * x ∈ centralizer (U : Set G) ∧ ∀ v ∈ S, act (α l) v ∈ S := by
  have hxX : x ∈ X := h.hPX.le hx
  obtain ⟨l, hl, hc⟩ := h.exists_L hxX
  refine ⟨⟨l, hl⟩, hc, ?_⟩
  have hxN := h.hXN hxX
  have hxR : x ∈ normalizer ((pCoreOf 2 P : Subgroup G) : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 P hx
  have hmap := autI_cjSub h.hU hxN (thompsonJ (pCoreOf 2 P))
  rw [cjSub_thompsonJ hxR, hJeq] at hmap
  have hcx : convI h.hU ⟨x, hxN⟩ = convI h.hU ⟨l, h.hLN hl⟩ := h.convI_eq hxX hl hc
  have hlmem : convI h.hU ⟨l, h.hLN hl⟩ ∈ autI h.hU L := convI_mem_autI h.hU hl (h.hLN hl)
  set lstar : ↥(autI h.hU L) := ⟨_, hlmem⟩ with hlstar
  have hψl : burnsideC137_ψ h.hs h.hU lstar = α ⟨l, hl⟩ :=
    burnsideC137_ψ_conv h.hs h.hU ⟨l, hl⟩ _
  apply burnsideC137_stab_of_norm hS
  intro t ht
  set c := (burnsideC137_ψ h.hs h.hU).symm t with hc'
  have hcA : (c : MulAut (IntMod U h.hU)) ∈ autI h.hU A₀ :=
    (hAS c).2 (by rw [hc', MulEquiv.apply_symm_apply]; exact ht)
  have hconj : ((lstar * c * lstar⁻¹ : ↥(autI h.hU L)) : MulAut (IntMod U h.hU)) ∈
      autI h.hU A₀ := by
    have : convI h.hU ⟨x, hxN⟩ * (c : MulAut _) * (convI h.hU ⟨x, hxN⟩)⁻¹ ∈ autI h.hU A₀ := by
      rw [← hmap]
      exact ⟨c, hcA, rfl⟩
    rw [hcx] at this
    exact this
  have := (hAS _).1 hconj
  rwa [map_mul, map_mul, map_inv, hψl, hc', MulEquiv.apply_symm_apply] at this

theorem mem_norm_pre {S : Finset Vec} (hS : IsPlane S) {I : Subgroup G}
    (hLI : L ≤ normalizer (I : Set G)) {γ : ↥I →* Multiplicative Vec}
    (hγ : IsNatVia L I ⊥ α γ) (l : ↥L) (hl : ∀ v ∈ S, act (α l) v ∈ S) :
    (l : G) ∈ normalizer (preimageIn I γ (burnsideC137_planeSub S hS) : Set G) := by
  refine Subgroup.mem_normalizer_iff.2 fun y => ⟨fun hy =>
    burnsideC137_conj_mem_pre hγ hLI _ l (fun u _ => rfl) hl hy, fun hy => ?_⟩
  have hl' : ∀ v ∈ S, act (α l⁻¹) v ∈ S := by
    rw [map_inv]
    exact burnsideC137_stab_inv S hS (α l) hl
  have := burnsideC137_conj_mem_pre hγ hLI _ l⁻¹ (x := ((l⁻¹ : ↥L) : G)) (fun u _ => rfl) hl' hy
  simpa [mul_assoc] using this

theorem concl3 {S : Finset Vec} (hS : IsPlane S)
    (hstab : ∀ x ∈ P, ∃ l : ↥L, (l : G)⁻¹ * x ∈ centralizer (U : Set G) ∧
      ∀ v ∈ S, act (α l) v ∈ S) :
    (∃ (ℓ : Submodule (ZMod 2) Vec)
      (coordinates : ∀ I : {I : Subgroup G // I ∈ internalIrrPlus L U},
        ↥I.val →* Multiplicative Vec),
      Module.finrank (ZMod 2) ℓ = 2 ∧ (∀ I, IsNatVia L I.val ⊥ α (coordinates I)) ∧
      P = X ⊓ ⨅ I : {I : Subgroup G // I ∈ internalIrrPlus L U},
        normalizer (preimageIn I.val (coordinates I) ℓ : Set G)) ∧
    ∀ l : ↥L, (∀ v ∈ S, act (α l) v ∈ S) → (l : G) ∈ P := by
  set ℓ := burnsideC137_planeSub S hS with hℓ
  set crd : ∀ I : {I : Subgroup G // I ∈ internalIrrPlus L U}, ↥I.val →* Multiplicative Vec :=
    fun I => burnsideC137_crd h.hs h.hU I.val I.2.1 with hcrd
  have hnat : ∀ I, IsNatVia L I.val ⊥ α (crd I) := fun I => burnsideC137_crd_nat h.hs h.hU I.2
  have hLI : ∀ I : {I : Subgroup G // I ∈ internalIrrPlus L U},
      L ≤ normalizer (I.val : Set G) := fun I => I.2.2.2.2.2.1
  set K := X ⊓ ⨅ I : {I : Subgroup G // I ∈ internalIrrPlus L U},
    normalizer (preimageIn I.val (crd I) ℓ : Set G) with hK
  have hconj : ∀ x ∈ P, ∀ I : {I : Subgroup G // I ∈ internalIrrPlus L U},
      ∀ y ∈ preimageIn I.val (crd I) ℓ, x * y * x⁻¹ ∈ preimageIn I.val (crd I) ℓ := by
    intro x hx I y hy
    obtain ⟨l, hlc, hlS⟩ := hstab x hx
    refine burnsideC137_conj_mem_pre (hnat I) (hLI I) ℓ l ?_ (fun v hv => hlS v hv) hy
    intro u hu
    have huU : u ∈ U := I.2.1 hu
    have hcomm := Subgroup.mem_centralizer_iff.1 hlc u huU
    calc x * u * x⁻¹ = (l : G) * (((l : G)⁻¹ * x) * u * ((l : G)⁻¹ * x)⁻¹) * (l : G)⁻¹ := by
          group
      _ = (l : G) * u * (l : G)⁻¹ := by rw [← hcomm]; group
  have hPK : P ≤ K := by
    intro x hx
    refine ⟨h.hPX.le hx, Subgroup.mem_iInf.2 fun I => Subgroup.mem_normalizer_iff.2 fun y =>
      ⟨fun hy => hconj x hx I y hy, fun hy => ?_⟩⟩
    have := hconj x⁻¹ (P.inv_mem hx) I _ hy
    simpa [mul_assoc] using this
  have hU₁ : U₁ ∈ internalIrrPlus L U :=
    burnsideC137_nat_mem_irr h.hs h.hU h.hs.le₁ h.hs.norm₁ h.hs.nat₁
  set I₁ : {I : Subgroup G // I ∈ internalIrrPlus L U} := ⟨U₁, hU₁⟩ with hI₁
  obtain ⟨g, v, hvS, hgv⟩ := burnsideC137_plane_moved S hS
  obtain ⟨l, rfl⟩ := h.hs.alpha_onto g
  have hlK : (l : G) ∉ K := by
    intro hl
    have hlN := (Subgroup.mem_iInf.1 hl.2) I₁
    obtain ⟨u, hu⟩ := (hnat I₁).1 (Multiplicative.ofAdd v)
    have hupre : (u : G) ∈ preimageIn I₁.val (crd I₁) ℓ :=
      burnsideC137_mem_preimageIn.2 ⟨u.2, by rw [hu]; exact hvS⟩
    have := (Subgroup.mem_normalizer_iff.1 hlN u).1 hupre
    obtain ⟨hw, hwℓ⟩ := burnsideC137_mem_preimageIn.1 this
    have h1 := (hnat I₁).2.2 l u ⟨_, hw⟩ rfl
    rw [h1, hu] at hwℓ
    exact hgv hwℓ
  have hKX : K ≠ X := fun heq => hlK (heq ▸ h.hLX l.2)
  have hPeq : P = K := ((h.hmax K hPK inf_le_left).resolve_right hKX).symm
  refine ⟨⟨ℓ, crd, burnsideC137_finrank_planeSub S hS, hnat, hPeq⟩, fun l' hl' => ?_⟩
  rw [hPeq]
  exact ⟨h.hLX l'.2, Subgroup.mem_iInf.2 fun I => h.mem_norm_pre hS (hLI I) (hnat I) l' hl'⟩

theorem autR_le {A₀ : Subgroup G} {S : Finset Vec} (hS : IsPlane S)
    (hAS : ∀ a : ↥(autI h.hU L), (a : MulAut (IntMod U h.hU)) ∈ autI h.hU A₀ ↔
      burnsideC137_ψ h.hs h.hU a ∈ BS S)
    (hstab : ∀ x ∈ P, ∃ l : ↥L, (l : G)⁻¹ * x ∈ centralizer (U : Set G) ∧
      ∀ v ∈ S, act (α l) v ∈ S)
    (hLP : ∀ l : ↥L, (∀ v ∈ S, act (α l) v ∈ S) → (l : G) ∈ P) :
    autI h.hU (pCoreOf 2 P) ≤ autI h.hU A₀ := by
  intro φ hφ
  obtain ⟨⟨r, hrN⟩, hrR, rfl⟩ := (mem_autI h.hU).1 hφ
  have hrP : r ∈ P := CFSG.LieType.BorelTits.pCoreOf_le 2 P hrR
  obtain ⟨l, hlc, hlS⟩ := hstab r hrP
  have hrX := h.hPX.le hrP
  have hcr : convI h.hU ⟨r, hrN⟩ = convI h.hU ⟨l, h.hLN l.2⟩ := h.convI_eq hrX l.2 hlc
  have hlmem : convI h.hU ⟨l, h.hLN l.2⟩ ∈ autI h.hU L := convI_mem_autI h.hU l.2 (h.hLN l.2)
  set lstar : ↥(autI h.hU L) := ⟨_, hlmem⟩ with hlstar
  have hψl : burnsideC137_ψ h.hs h.hU lstar = α l := burnsideC137_ψ_conv h.hs h.hU l _
  rw [hcr]
  refine (hAS lstar).2 ?_
  rw [hψl, burnsideC137_mem_BS]
  by_contra hfix
  obtain ⟨g, hgS, h3⟩ := burnsideC137_stab_not_BS S hS (α l) hlS hfix
  obtain ⟨l', rfl⟩ := h.hs.alpha_onto g
  have hl'P : (l' : G) ∈ P := hLP l' hgS
  have hcR : r * l' * r⁻¹ * (l' : G)⁻¹ ∈ pCoreOf 2 P := by
    have h1 : (l' : G) * r⁻¹ * (l' : G)⁻¹ ∈ pCoreOf 2 P :=
      (Subgroup.mem_normalizer_iff.1 (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 P hl'P)
        r⁻¹).1 (Subgroup.inv_mem _ hrR)
    have := (pCoreOf 2 P).mul_mem hrR h1
    simpa [mul_assoc] using this
  have hl'mem : convI h.hU ⟨l', h.hLN l'.2⟩ ∈ autI h.hU L :=
    convI_mem_autI h.hU l'.2 (h.hLN l'.2)
  set l'star : ↥(autI h.hU L) := ⟨_, hl'mem⟩ with hl'star
  have hψl' : burnsideC137_ψ h.hs h.hU l'star = α l' := burnsideC137_ψ_conv h.hs h.hU l' _
  have heR : ((lstar * l'star * lstar⁻¹ * l'star⁻¹ : ↥(autI h.hU L)) :
      MulAut (IntMod U h.hU)) ∈ autI h.hU (pCoreOf 2 P) := by
    have hcN : r * l' * r⁻¹ * (l' : G)⁻¹ ∈ normalizer (U : Set G) :=
      (normalizer _).mul_mem ((normalizer _).mul_mem ((normalizer _).mul_mem hrN (h.hLN l'.2))
        ((normalizer _).inv_mem hrN)) ((normalizer _).inv_mem (h.hLN l'.2))
    have := convI_mem_autI h.hU hcR hcN
    have e1 : (⟨r * l' * r⁻¹ * (l' : G)⁻¹, hcN⟩ : ↥(normalizer (U : Set G))) =
        ⟨r, hrN⟩ * ⟨l', h.hLN l'.2⟩ * ⟨r, hrN⟩⁻¹ * ⟨l', h.hLN l'.2⟩⁻¹ := Subtype.ext rfl
    rw [e1, map_mul, map_mul, map_mul, map_inv, map_inv, hcr] at this
    exact this
  obtain ⟨k, hk⟩ := h.autR_pow heR
  have hk' : (lstar * l'star * lstar⁻¹ * l'star⁻¹) ^ 2 ^ k = 1 :=
    Subtype.ext (by rw [Subgroup.coe_pow]; exact hk)
  have : (α l * α l' * (α l)⁻¹ * (α l')⁻¹) ^ 2 ^ k = 1 := by
    have := congrArg (burnsideC137_ψ h.hs h.hU) hk'
    rw [map_pow, map_one, map_mul, map_mul, map_mul, map_inv, map_inv, hψl, hψl'] at this
    exact this
  exact burnsideC137_not_ord3 h3 this

end burnsideC137_SCtx

end CFSG.ASVolI
