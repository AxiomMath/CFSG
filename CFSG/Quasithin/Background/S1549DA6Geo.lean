module

public import CFSG.Quasithin.Background.S1549DA6Dict
public import CFSG.Quasithin.Background.S1549DA6Grp
public import CFSG.Quasithin.Background.S1549DA6Mod
public import CFSG.Quasithin.Background.S1549DSMod

public section

namespace CFSG.Quasithin.S1549D

open CFSG.QuasithinUnique CFSG.Quasithin.B5 CFSG.Open CFSG.LieType.BorelTits CFSG.Quasithin.S143

variable {V : Type} [CommGroup V] [Finite V]

theorem b51Hyp_ffJ {X L S : Subgroup (MulAut V)}
    (hLn : ∀ x ∈ X, ∀ l ∈ L, x * l * x⁻¹ ∈ L) (hLq : CFSG.IsQuasisimple ↥L) (hLs : SQTKGroup ↥L)
    (hS : IsSylowTwoOf S X) (hXLS : X ≤ L ⊔ S) (hO2 : pCoreOf 2 X = ⊥) (hLJ : L ≤ ffJ X) :
    B51Hyp (ffJ X) L := by
  classical
  have hXn : X ≤ Subgroup.normalizer (L : Set (MulAut V)) := le_normalizer_of_conj hLn
  have hX2 : ∀ x ∈ X, ∃ e : ℕ, x ^ 2 ^ e ∈ L := fun x hx =>
    C1Pack153.exists_pow_mem_of_mem_sup_two hS.2.1 (fun s hs => hXn (hS.1 hs)) (hXLS hx)
  set G₁ := ffJ X with hG₁
  have hG₁X : G₁ ≤ X := B6.ffJ_le X
  have hLo := B1Red.isQuasisimple_to_open hLq
  have hG₁n : ∀ y ∈ G₁, ∀ l ∈ L, y * l * y⁻¹ ∈ L := fun y hy l hl => hLn y (hG₁X hy) l hl
  have hG₁2 : ∀ y ∈ G₁, ∃ e : ℕ, y ^ 2 ^ e ∈ L := fun y hy => hX2 y (hG₁X hy)
  have hO2G₁ : pCoreOf 2 G₁ = ⊥ := by
    refine le_bot_iff.mp ?_
    have h1 := pCoreOf_le_pCoreOf_of_normalizes hG₁X (B6.le_normalizer_ffJ X)
    rwa [hO2] at h1
  have hFstar : quasithinGenFitting G₁ = L :=
    InternalSec.quasithinGenFitting_eq_of_two_pow hLJ hG₁n hLo hG₁2 hO2G₁
  refine ⟨?_, hLq, hLs, hLJ, hO2G₁, (InternalSec.ffJ_ffJ X).symm⟩
  have hZL : centerOf G₁ ≤ L := (FFC.centerOf_le_genFitting G₁).trans hFstar.le
  rw [hFstar, sup_eq_left.mpr hZL]

theorem a6_endgame (hB51 : AsB51) (hB42 : AsB42) (hV : ∀ v : V, v ^ 2 = 1)
    {X L S P₀ M' A : Subgroup (MulAut V)}
    (hLX : L ≤ X) (hLn : ∀ x ∈ X, ∀ l ∈ L, x * l * x⁻¹ ∈ L)
    (hLq : CFSG.IsQuasisimple ↥L) (hLs : SQTKGroup ↥L) (hLc : Nat.card ↥L = 360)
    (hS : IsSylowTwoOf S X) (hXLS : X ≤ L ⊔ S) (hO2 : pCoreOf 2 X = ⊥)
    (hLJ : L ≤ ffJ X) (hA : IsStrongFFStarOffender X A)
    {z : V} (hzS : ∀ s ∈ S, s z = z)
    (hgen : Subgroup.closure {v : V | ∃ g ∈ X, g z = v} = ⊤)
    (hM : ∀ g ∈ X, g z = z → g ∈ M')
    (hP₀L : P₀ ≤ L) (hpar : IsMinParabolicOf L P₀)
    (hPM : P₀ ⊔ S ≤ M') (hAP : A ≤ pCoreOf 2 (P₀ ⊔ S)) : L ≤ M' := by
  classical
  by_contra hnot
  have hXn : X ≤ Subgroup.normalizer (L : Set (MulAut V)) := le_normalizer_of_conj hLn
  have hB : B51Hyp (ffJ X) L := b51Hyp_ffJ hLn hLq hLs hS hXLS hO2 hLJ
  set G₁ := ffJ X with hG₁
  have hG₁X : G₁ ≤ X := B6.ffJ_le X
  have hirr := a6_irrPlus hB51 hV hB hLc
  have hAoff := hA.1
  have hAG₁ : A ≤ G₁ := B6.le_ffJ hAoff
  have hA' : IsFFStarOffender G₁ A := ⟨hAG₁, hAoff.2⟩
  have hQp : IsPGroup 2 ↥(pCoreOf 2 (P₀ ⊔ S)) := pCoreOf_isPGroup 2 _
  have hQ₁p : IsPGroup 2 ↥(pCoreOf 2 (P₀ ⊔ S) ⊓ G₁) := hQp.to_inf_left
  have hAQ₁ : A ≤ pCoreOf 2 (P₀ ⊔ S) ⊓ G₁ := le_inf hAP hAG₁
  obtain ⟨T, hT, hQ₁T⟩ := FFC.B59.exists_isSylowTwoOf_ge
    (inf_le_right : pCoreOf 2 (P₀ ⊔ S) ⊓ G₁ ≤ G₁) hQ₁p
  have hAT : A ≤ T := hAQ₁.trans hQ₁T
  obtain ⟨C, hC⟩ : ∃ C : Subgroup V, C = fixV L ⊓ commV L := ⟨_, rfl⟩
  rcases a6_section_dichotomy hB42 hV hB hirr hT hA' hAT hC hLc with hq | ⟨hSp4, -, hLcomm, -⟩
  · exact absurd hA.2 (not_lt.2 (no_strong_of_section_q hV hB hirr hT hA' hAT hC hq))
  obtain ⟨hUC, hlt, hGU, hGC, hfL, hfM⟩ := secConfig hV hB hirr hT hC
  have hXU : X ≤ stabSub (commV L) := le_stabSub_commV hLn (fun g hg => X.inv_mem hg)
  have hXC : X ≤ stabSub C := by
    rw [hC]
    exact le_stabSub_fixV_inf_commV hLn (fun g hg => X.inv_mem hg)
  have hCinv : ∀ x ∈ X, ∀ c ∈ C, x c ∈ C := fun x hx c hc => ((hXC hx) c).2 hc
  have hCL : C ≤ fixV L := by rw [hC]; exact inf_le_left
  have hTX : T ≤ X := hT.1.trans hG₁X
  have htop := commV_L_sup_fixV_L_eq_top hV hLX hLn hS hXLS hzS hgen
  obtain ⟨u, hu, c, hc, huc⟩ := Subgroup.mem_sup.mp (htop ▸ Subgroup.mem_top z)
  have hu0 : u ∉ fixV L := by
    intro huL
    have hzfix : z ∈ fixV L := by
      rw [← huc]
      exact Subgroup.mul_mem _ huL hc
    have hfix : fixV L = ⊤ := by
      refine eq_top_iff.mpr ?_
      rw [← hgen, Subgroup.closure_le]
      rintro _ ⟨g, hg, rfl⟩
      exact fixV_invariant hLn hg hzfix
    have hL1 : L ≠ ⊥ := by
      intro hbot
      rw [hbot, Subgroup.card_bot] at hLc
      omega
    obtain ⟨l, hl⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hL1
    apply hl
    apply Subtype.ext
    apply MulEquiv.ext
    intro v
    exact (hfix ▸ Subgroup.mem_top v : v ∈ fixV L) l l.2
  let ubar : Sec (commV L) C := QuotientGroup.mk ⟨u, hu⟩
  have hubar : ubar ≠ 1 := by
    intro h1
    have h2 := (QuotientGroup.eq_one_iff _).mp h1
    rw [Subgroup.mem_subgroupOf, hC] at h2
    exact hu0 h2.1
  let σX := B5.secHom X hXU hXC
  have hfixU : ∀ g : ↥X, σX g ubar = ubar ↔ (g : MulAut V) u * u⁻¹ ∈ C := by
    intro g
    show (QuotientGroup.mk ⟨(g : MulAut V) u, (hXU g.2 u).2 hu⟩ : Sec (commV L) C) =
      QuotientGroup.mk ⟨u, hu⟩ ↔ _
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
    have e : ((g : MulAut V) u)⁻¹ * u = ((g : MulAut V) u * u⁻¹)⁻¹ := by
      rw [mul_inv_rev, inv_inv, mul_comm]
    show ((g : MulAut V) u)⁻¹ * u ∈ C ↔ _
    rw [e, inv_mem_iff]
  have hLC : ∀ l ∈ L, ∀ c ∈ C, l c ∈ C := fun l hl c hc => by
    rw [(hCL hc) l hl]
    exact hc
  let Pu : Subgroup (MulAut V) := stabU L u C hLC
  let stabX : Subgroup (MulAut V) := stabU X u C hCinv
  have hPuL : Pu ≤ L := fun g hg => hg.1
  have hSstab : S ≤ stabX := by
    intro s hs
    refine ⟨hS.1 hs, ?_⟩
    have hsz := hzS s hs
    rw [← huc, map_mul] at hsz
    have h1 : s u * u⁻¹ = c * (s c)⁻¹ := by
      rw [← div_eq_mul_inv, ← div_eq_mul_inv, div_eq_div_iff_mul_eq_mul, hsz, mul_comm]
    rw [h1, hC]
    exact ⟨Subgroup.mul_mem _ hc (Subgroup.inv_mem _ (fixV_invariant hLn (hS.1 hs) hc)), by
      have e : c * (s c)⁻¹ = s u * u⁻¹ := h1.symm
      rw [e]
      exact Subgroup.mul_mem _ (commV_invariant hLn (hS.1 hs) hu) (Subgroup.inv_mem _ hu)⟩
  have hSLu : ∀ s ∈ S ⊓ L, s u = u := by
    intro s hs
    have hsz := hzS s hs.1
    rw [← huc, map_mul, (hc s hs.2 : s c = c)] at hsz
    exact mul_right_cancel hsz
  have hSylL : IsSylowTwoOf (S ⊓ L) L := B6.isSylowTwoOf_inf_normal hS hLX hXn
  have hSLPu : S ⊓ L ≤ Pu := fun s hs =>
    ⟨hs.2, by rw [hSLu s hs, mul_inv_cancel]; exact C.one_mem⟩
  have hSylPu : IsSylowTwoOf (S ⊓ L) Pu := B6.isSylowTwoOf_mono hSylL hSLPu hPuL
  have hufix : u ∈ fixV Pu :=
    mem_fixV_of_sylow hV hSylPu hSLu (Z := C) (fun c' hc' p hp => (hCL hc') p (hPuL hp))
      (fun p hp => hp.2)
  have hPuM : Pu ≤ M' := by
    intro g hg
    have hgu : g u = u := hufix g hg
    have hgc : g c = c := hc g hg.1
    apply hM g (hLX hg.1)
    rw [← huc, map_mul, hgu, hgc]
  have hP₀M : P₀ ≤ M' := le_sup_left.trans hPM
  set G'' := autSec (L ⊔ T) (commV L) C with hG''
  obtain ⟨π₀, hπ₀⟩ := asSp4S6 (Sec (commV L) C) G'' ⊤ ⊥ hSp4
  obtain ⟨π, Θ, hπbij, hΘū, hΘ⟩ := exists_normalized_dict hπ₀ hubar
  have hLU : L ≤ stabSub (commV L) := hLX.trans hXU
  have hLC' : L ≤ stabSub C := hLX.trans hXC
  let f : Equiv.Perm (Fin 6) →* MulAut (Sec (commV L) C) := G''.subtype.comp π
  have hf : Function.Injective f := Subtype.val_injective.comp hπbij.1
  have hL'eq : autSec L (commV L) C = (alternatingGroup (Fin 6)).map f :=
    hLcomm.trans (commutator_eq_map_alt hπbij.2)
  let ε₂ : ↥(alternatingGroup (Fin 6)) ≃* ↥(autSec L (commV L) C) :=
    (Subgroup.equivMapOfInjective (alternatingGroup (Fin 6)) f hf).trans
      (MulEquiv.subgroupCongr hL'eq.symm)
  let ε : ↥L ≃* ↥(alternatingGroup (Fin 6)) := (B5.secEquiv L hLU hLC' hfL).trans ε₂.symm
  have hεf : ∀ g : ↥L, (f ((ε g : ↥(alternatingGroup (Fin 6))) : Equiv.Perm (Fin 6)) :
      MulAut (Sec (commV L) C)) = σX ⟨(g : MulAut V), hLX g.2⟩ := by
    intro g
    have h1 : ε₂ (ε g) = B5.secEquiv L hLU hLC' hfL g := by simp [ε]
    have h2 := congrArg (fun q : ↥(autSec L (commV L) C) => (q : MulAut (Sec (commV L) C))) h1
    exact h2
  have : IsSimpleGroup ↥(alternatingGroup (Fin 6)) :=
    alternatingGroup.isSimpleGroup (by simp)
  have : IsSimpleGroup ↥L := ε.isSimpleGroup
  have hPuε : ∀ g : ↥L, (g : MulAut V) ∈ Pu ↔ n6Act (ε g : Equiv.Perm (Fin 6)) a6u0 = a6u0 := by
    intro g
    have h1 : (g : MulAut V) ∈ Pu ↔ (g : MulAut V) u * u⁻¹ ∈ C := ⟨fun h => h.2, fun h => ⟨g.2, h⟩⟩
    rw [h1, ← hfixU ⟨(g : MulAut V), hLX g.2⟩, ← hεf g]
    have h2 : Θ ((f (ε g : Equiv.Perm (Fin 6)) : MulAut (Sec (commV L) C)) ubar) =
        n6Act (ε g : Equiv.Perm (Fin 6)) a6u0 := by
      have := hΘ (ε g : Equiv.Perm (Fin 6)) ubar
      rw [hΘū] at this
      exact this
    constructor
    · intro h
      rw [← h2, h, hΘū]
    · intro h
      apply Θ.injective
      rw [h2, h, hΘū]
  have hcardPu : Nat.card Pu = 24 := by
    have hbij : Function.Bijective (fun g : Pu =>
        (⟨((ε ⟨(g : MulAut V), hPuL g.2⟩ : ↥(alternatingGroup (Fin 6))) : Equiv.Perm (Fin 6)),
          Equiv.Perm.mem_alternatingGroup.mp (ε ⟨(g : MulAut V), hPuL g.2⟩).2,
          (hPuε ⟨(g : MulAut V), hPuL g.2⟩).1 g.2⟩ :
          {σ : Equiv.Perm (Fin 6) // Equiv.Perm.sign σ = 1 ∧ n6Act σ a6u0 = a6u0})) := by
      constructor
      · intro g₁ g₂ h12
        have h3 := congrArg Subtype.val h12
        have h4 : ε ⟨(g₁ : MulAut V), hPuL g₁.2⟩ = ε ⟨(g₂ : MulAut V), hPuL g₂.2⟩ :=
          Subtype.ext h3
        have h5 := ε.injective h4
        exact Subtype.ext (congrArg (fun x : ↥L => (x : MulAut V)) h5)
      · rintro ⟨σ, hσ1, hσu⟩
        let a : ↥(alternatingGroup (Fin 6)) := ⟨σ, Equiv.Perm.mem_alternatingGroup.mpr hσ1⟩
        have hεa : ε (ε.symm a) = a := ε.apply_symm_apply a
        have hgPu : ((ε.symm a : ↥L) : MulAut V) ∈ Pu := by
          rw [hPuε, hεa]
          exact hσu
        refine ⟨⟨((ε.symm a : ↥L) : MulAut V), hgPu⟩, ?_⟩
        apply Subtype.ext
        show ((ε ⟨((ε.symm a : ↥L) : MulAut V), _⟩ : ↥(alternatingGroup (Fin 6))) :
          Equiv.Perm (Fin 6)) = σ
        have : (⟨((ε.symm a : ↥L) : MulAut V), hPuL hgPu⟩ : ↥L) = ε.symm a := rfl
        rw [this, hεa]
    rw [Nat.card_congr (Equiv.ofBijective _ hbij), Nat.card_eq_fintype_card, Fintype.card_subtype]
    exact a6P_card
  have hPu'card : Nat.card (Pu.subgroupOf L) = 24 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPuL).toEquiv]
    exact hcardPu
  have hPuH : Pu.subgroupOf L ≤ (Pu ⊔ P₀).subgroupOf L := fun x hx =>
    Subgroup.mem_subgroupOf.mpr ((le_sup_left : Pu ≤ Pu ⊔ P₀) (Subgroup.mem_subgroupOf.mp hx))
  have hP₀Pu : P₀ ≤ Pu := by
    rcases eq_or_top_of_card_24 hLc hPu'card hPuH with hH | hH
    · intro p hp
      have hpH : (⟨p, hP₀L hp⟩ : ↥L) ∈ (Pu ⊔ P₀).subgroupOf L :=
        Subgroup.mem_subgroupOf.mpr ((le_sup_right : P₀ ≤ Pu ⊔ P₀) hp)
      rw [hH] at hpH
      exact Subgroup.mem_subgroupOf.mp hpH
    · exfalso
      apply hnot
      intro l hl
      have h1 : (⟨l, hl⟩ : ↥L) ∈ (Pu ⊔ P₀).subgroupOf L := by
        rw [hH]
        trivial
      exact (sup_le hPuM hP₀M) (Subgroup.mem_subgroupOf.mp h1)
  obtain ⟨T', hT', hP⟩ := hpar
  have hT'P : T' < P₀ := hP.1.2.1
  have hP₀Pu' : P₀ = Pu := eq_of_lt_le_card (card_sylow_eight hT' hLc) hcardPu hT'P hP₀Pu
  have hP₀X : P₀ ≤ X := hP₀L.trans hLX
  have hP₀stab : P₀ ≤ stabX := fun g hg => ⟨hP₀X hg, (hP₀Pu hg).2⟩
  have hRstab : P₀ ⊔ S ≤ stabX := sup_le hP₀stab hSstab
  have hmemSec : ∀ {Y : Subgroup (MulAut V)}, Y ≤ X → ∀ {q : MulAut (Sec (commV L) C)},
      q ∈ autSec Y (commV L) C ↔ ∃ g : ↥X, (g : MulAut V) ∈ Y ∧ σX g = q := by
    intro Y hYX q
    rw [← B5.map_secHom_eq_autSec X hXU hXC hYX, Subgroup.mem_map]
    constructor
    · rintro ⟨g, hg, rfl⟩
      exact ⟨g, hg, rfl⟩
    · rintro ⟨g, hg, rfl⟩
      exact ⟨g, hg, rfl⟩
  have hAle : A ≤ L ⊔ T := hAT.trans le_sup_right
  have hAX : A ≤ X := hAG₁.trans hG₁X
  have hAU : A ≤ stabSub (commV L) := hAX.trans hXU
  have hAC : A ≤ stabSub C := hAX.trans hXC
  have hfA : A ⊓ centSec (commV L) C = ⊥ := by
    refine eq_bot_iff.mpr ?_
    rw [← hfM]
    exact inf_le_inf_right _ hAle
  have hne : autSec A (commV L) C ≠ ⊥ := by
    intro hbot
    have hcard := card_autSec_mul (A := A) hAU hAC
    rw [hfA, Subgroup.card_bot, mul_one, hbot, Subgroup.card_bot] at hcard
    exact hAoff.2.1 (Subgroup.card_eq_one.1 hcard.symm)
  have hA2 : IsA2 G'' (autSec A (commV L) C) :=
    ⟨autSec_mono hAle _ _, hne, isElemAbelian2_autSec _ _ hAoff.2.2.1⟩
  have hS2 := sq_eq_one_sec hV (commV L) C
  have hr := FFC.B59.rAV_autSec_le hV hUC hAU hAC hfA hAoff.2.1 hAoff.2.2.1
  have hQ₁X : pCoreOf 2 (P₀ ⊔ S) ⊓ G₁ ≤ X := inf_le_right.trans hG₁X
  have hPp : ∀ σ ∈ alternatingGroup (Fin 6), ((π σ : ↥G'') : MulAut (Sec (commV L) C)) ubar = ubar →
      ((π σ : ↥G'') : MulAut (Sec (commV L) C)) ∈ autSec P₀ (commV L) C := by
    intro σ hσ hfix
    have hfσ : (f σ : MulAut (Sec (commV L) C)) ∈ autSec L (commV L) C := by
      rw [hL'eq]
      exact ⟨σ, hσ, rfl⟩
    obtain ⟨g, hgL, hgσ⟩ := (hmemSec hLX).mp hfσ
    have hgfix : σX g ubar = ubar := by
      rw [hgσ]
      exact hfix
    have hgPu : (g : MulAut V) ∈ Pu := ⟨hgL, (hfixU g).mp hgfix⟩
    refine (hmemSec hP₀X).mpr ⟨g, hP₀Pu' ▸ hgPu, ?_⟩
    exact hgσ
  have hbound := a6_no_strong_normalized (G' := G'') (π' := π) (Θ := Θ) (ū := ubar) hπbij hΘū hΘ
    (Pp := autSec P₀ (commV L) C) (Qp := autSec (pCoreOf 2 (P₀ ⊔ S) ⊓ G₁) (commV L) C)
    (Ap := autSec A (commV L) C) hPp
    (autSec_mono (hQ₁T.trans le_sup_right) _ _)
    (by
      intro q hq
      obtain ⟨g, hg, rfl⟩ := (hmemSec hQ₁X).mp hq
      obtain ⟨k, hk⟩ := hQ₁p ⟨(g : MulAut V), hg⟩
      refine ⟨k, ?_⟩
      rw [← map_pow]
      have hk' := congrArg (fun x : ↥(pCoreOf 2 (P₀ ⊔ S) ⊓ G₁) => (x : MulAut V)) hk
      have : g ^ 2 ^ k = 1 := Subtype.ext (by simpa using hk')
      rw [this, map_one])
    (by
      intro q hq
      obtain ⟨g, hg, rfl⟩ := (hmemSec hQ₁X).mp hq
      exact (hfixU g).mpr (hRstab (pCoreOf_le 2 _ hg.1)).2)
    (by
      intro p hp q hq
      obtain ⟨a, ha, rfl⟩ := (hmemSec hP₀X).mp hp
      obtain ⟨g, hg, rfl⟩ := (hmemSec hQ₁X).mp hq
      refine (hmemSec hQ₁X).mpr ⟨a * g * a⁻¹, ⟨?_, ?_⟩, by simp⟩
      · have hn := le_normalizer_pCoreOf (r := 2) (P₀ ⊔ S) ((le_sup_left : P₀ ≤ P₀ ⊔ S) ha)
        exact (Subgroup.mem_normalizer_iff.mp hn (g : MulAut V)).mp hg.1
      · exact G₁.mul_mem (G₁.mul_mem (hLJ (hP₀L ha)) hg.2) (G₁.inv_mem (hLJ (hP₀L ha))))
    (autSec_mono hAQ₁ _ _) hne
  have hlt1 : rAV (autSec A (commV L) C) < 1 := lt_of_le_of_lt hr hA.2
  have h1 := (rAV_lt_one_iff hS2 hA2).mp hlt1
  exact absurd hbound (not_le.mpr h1)
