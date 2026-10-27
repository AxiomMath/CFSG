module

public import CFSG.Quasithin.Background.F918Z6Aux
public import CFSG.Quasithin.Background.RonanD35Three
public import CFSG.Quasithin.Vol2.Ch5Sec1L34D38

public section

namespace CFSG.Quasithin.RonanD38

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.F7
open CFSG.LieType.BorelTits

section Restrict

variable {W : Type} [CommGroup W] [Finite W] {M Mp T L : Subgroup (MulAut W)} {V : Subgroup W}

theorem d38r_sup_le_stabSub (hD : D3Std M Mp T L V) : Mp ⊔ T ≤ stabSub (orbSup T V) := by
  have hTn : T ≤ Subgroup.normalizer (Mp : Set (MulAut W)) := by
    rw [hD.hyp.Mp_eq]
    exact le_normalizer_conjClosure L T
  have hVinv : ∀ x ∈ Mp, ∀ v ∈ V, x v ∈ V := fun x hx v hv => hD.hyp.irr.2.1 ⟨x, hx⟩ v hv
  exact sup_le (D36.le_stabSub_orbSup_Mp hTn hVinv) (le_stabSub_orbSup T V)

theorem d38r_autSub_L_ne_bot (hD : D3Std M Mp T L V) : autSub L (orbSup T V) ≠ ⊥ := by
  set Y := orbSup T V with hY
  have hX := d38r_sup_le_stabSub hD
  have hLMp : L ≤ Mp := by
    rw [hD.hyp.Mp_eq]
    exact le_conjClosure L T
  have hLY : L ≤ stabSub Y := (hLMp.trans le_sup_left).trans hX
  have hTY : T ≤ stabSub Y := le_stabSub_orbSup T V
  intro hbot
  have hLc : L ≤ centSub Y := by
    intro l hl y hy
    have h0 : resHom Y ⟨l, hLY hl⟩ ∈ autSub L Y := mem_autSub.mpr ⟨⟨l, hLY hl⟩, hl, rfl⟩
    rw [hbot] at h0
    have h1 : resHom Y ⟨l, hLY hl⟩ = 1 := h0
    exact congrArg (fun f : MulAut ↥Y => ((f ⟨y, hy⟩ : ↥Y) : W)) h1
  have hMpc : Mp ≤ centSub Y := by
    rw [hD.hyp.Mp_eq]
    refine conjClosure_le fun s hs z hz y hy => ?_
    have hs' : s⁻¹ y ∈ Y := (hTY (T.inv_mem hs) y).2 hy
    show s (z (s⁻¹ y)) = y
    rw [hLc hz _ hs']
    simp
  obtain ⟨-, -, hlt, -⟩ := mem_irrPlus_top_iff.mp hD.hyp.irr
  apply hlt.not_ge
  intro v hv
  exact ⟨hv, fun m hm => hMpc hm v (le_orbSup T V hv)⟩

theorem d38_restrict (hD : D3Std M Mp T L V) :
    D3Std (autSub (Mp ⊔ T) (orbSup T V)) (autSub Mp (orbSup T V)) (autSub T (orbSup T V))
      (autSub L (orbSup T V)) (V.subgroupOf (orbSup T V)) := by
  set Y := orbSup T V with hY
  have hTM : T ≤ M := hD.hyp.sylow.1
  have hLMp : L ≤ Mp := by
    rw [hD.hyp.Mp_eq]
    exact le_conjClosure L T
  have hMpM : Mp ≤ M := RonanD35.d3Std_Mp_le hD
  have hTn : T ≤ Subgroup.normalizer (Mp : Set (MulAut W)) := by
    rw [hD.hyp.Mp_eq]
    exact le_normalizer_conjClosure L T
  have hX : Mp ⊔ T ≤ stabSub Y := d38r_sup_le_stabSub hD
  have hMps : Mp ≤ stabSub Y := le_sup_left.trans hX
  have hTs : T ≤ stabSub Y := le_sup_right.trans hX
  have hXM : Mp ⊔ T ≤ M := sup_le hMpM hTM
  have hXMp : Mp ⊔ T ≤ Subgroup.normalizer (Mp : Set (MulAut W)) :=
    sup_le Subgroup.le_normalizer hTn
  have hLX : L ≤ Mp ⊔ T := hLMp.trans le_sup_left
  have hMpX : Mp ≤ Mp ⊔ T := le_sup_left
  have hTX : T ≤ Mp ⊔ T := le_sup_right
  have hexp : ∀ w : ↥Y, w ^ 2 = 1 := fun w => Subtype.ext (by simp [hD.hyp.exp])
  have eL : autSub L Y = (L.subgroupOf (Mp ⊔ T)).map (resHomOn Y hX) :=
    autSub_eq_map_resHomOn hLX hX
  have eT : autSub T Y = (T.subgroupOf (Mp ⊔ T)).map (resHomOn Y hX) :=
    autSub_eq_map_resHomOn hTX hX
  have eMp : autSub Mp Y = (Mp.subgroupOf (Mp ⊔ T)).map (resHomOn Y hX) :=
    autSub_eq_map_resHomOn hMpX hX
  have eX : autSub (Mp ⊔ T) Y = ((Mp ⊔ T).subgroupOf (Mp ⊔ T)).map (resHomOn Y hX) :=
    autSub_eq_map_resHomOn le_rfl hX
  have hLne : autSub L Y ≠ ⊥ := d38r_autSub_L_ne_bot hD
  have hMnorm : autSub (Mp ⊔ T) Y ≤ Subgroup.normalizer (autSub Mp Y : Set (MulAut ↥Y)) := by
    rw [eX, eMp]
    exact map_le_normalizer_map_of_le_normalizer (resHomOn Y hX) hMpX hXMp
  have hSyl : IsSylowTwoOf T (Mp ⊔ T) := isSylowTwoOf_mono_right hD.hyp.sylow le_sup_right hXM
  have hSylF : IsSylowTwoOf (autSub T Y) (autSub (Mp ⊔ T) Y) := by
    rw [eT, eX]
    exact isSylowTwoOf_map_subgroupOf (resHomOn Y hX) hSyl
  have hcomp : autSub L Y ∈ cComp (autSub (Mp ⊔ T) Y) := by
    rw [eL, eX]
    exact map_subgroupOf_mem_cComp (resHomOn Y hX) (cComp_mem_of_le hD.hyp.comp hLX hXM)
      (by rw [← eL]; exact hLne)
  have hquasi : CFSG.IsQuasisimple ↥(autSub L Y) := by
    rw [eL]
    exact isQuasisimple_map_subgroupOf_of_ne_bot hLX hD.hyp.quasi (resHomOn Y hX)
      (by rw [← eL]; exact hLne)
  have hMpeq : autSub Mp Y = conjClosure (autSub L Y) (autSub T Y) := by
    have h := map_subgroupOf_conjClosure (resHomOn Y hX) hLX hTX
    rw [← hD.hyp.Mp_eq] at h
    rw [eMp, eL, eT]
    exact h
  have hMpAC : ActCompat Y.subtype (autSub Mp Y) Mp :=
    actCompat_autSub hMps le_rfl (fun a ha => ⟨a, ha, fun u _ => rfl⟩)
  have hTAC : ActCompat Y.subtype (autSub T Y) T :=
    actCompat_autSub hTs le_rfl (fun a ha => ⟨a, ha, fun u _ => rfl⟩)
  have hVY : V ≤ Y := le_orbSup T V
  have hmapV : (V.subgroupOf Y).map Y.subtype = V := Subgroup.map_subgroupOf_eq_of_le hVY
  have hVirr : XMod.IsIrrPlus ↥(autSub Mp Y) (V.subgroupOf Y) :=
    (hMpAC.isIrrPlus_map_iff Y.subtype_injective (V.subgroupOf Y)).mp
      (by rw [hmapV]; exact hD.hyp.irr.2)
  have hWT : ∀ s ∈ T, ∀ w ∈ orbSup T V, s • w ∈ orbSup T V := fun s hs w hw =>
    mem_orbSup_of_mem_map hs hw
  have hTnAut : autSub T Y ≤ Subgroup.normalizer (autSub Mp Y : Set (MulAut ↥Y)) :=
    (autSub_mono hTX Y).trans hMnorm
  have hirrT : V.subgroupOf Y ∈
      IrrPlusOn (autSub Mp Y) (orbSup (autSub T Y) (V.subgroupOf Y)) (autSub T Y) := by
    rw [orbSup_eq_biSup_smul]
    exact hMpAC.mem_irrPlusOn_of_map Y.subtype_injective hTAC hTnAut hTn
      (Wq := orbSup T V) hWT (by rw [hmapV]; exact hD.irrT)
  have hO2 : pCoreOf 2 (autSub Mp Y ⊔ autSub T Y) = ⊥ := by
    rw [← autSub_sup hX]
    exact D31.pCoreOf_autSub_orbSup_eq_bot hD.hyp
  have ho2 : ∀ g ∈ pCoreOf 2 (autSub Mp Y ⊔ autSub T Y), ∀ v ∈ V.subgroupOf Y,
      g v ∈ V.subgroupOf Y := by
    intro g hg v hv
    rw [hO2, Subgroup.mem_bot] at hg
    rw [hg]
    exact hv
  have htop : orbSup (autSub T Y) (V.subgroupOf Y) = ⊤ :=
    orbSup_autSub_subgroupOf_eq_top hVY hTs le_rfl
  have hgen : (⨆ m ∈ autSub (Mp ⊔ T) Y, (V.subgroupOf Y).map m.toMonoidHom) = ⊤ := by
    rw [eq_top_iff, ← htop]
    exact iSup₂_le fun τ hτ => le_iSup₂_of_le τ ((autSub_mono hTX Y) hτ) le_rfl
  have hqhat : qhatOf (autSub (autSub Mp Y ⊔ autSub T Y)
      (orbSup (autSub T Y) (V.subgroupOf Y))) ≤ ((2 : ℚ) : WithTop ℚ) := by
    rw [qhatOf_autSub_congr htop, H13.qhatOf_autSub_top, ← autSub_sup hX]
    exact hD.qhat
  exact ⟨⟨hexp, isQuotientOfSQTK_autSub_aux hXM hD.hyp.qsqtk, hSylF, hcomp, hquasi, hMpeq, hMnorm,
    ⟨le_top, hVirr⟩, ho2, hgen⟩, hqhat, hirrT⟩

omit [Finite W] in
theorem d38_restrict_orbSup (T : Subgroup (MulAut W)) (V : Subgroup W) :
    orbSup (autSub T (orbSup T V)) (V.subgroupOf (orbSup T V)) = ⊤ :=
  orbSup_autSub_subgroupOf_eq_top (le_orbSup T V) (le_stabSub_orbSup T V) le_rfl

theorem d38_restrict_qhatOf (hD : D3Std M Mp T L V) :
    qhatOf (autSub (autSub Mp (orbSup T V) ⊔ autSub T (orbSup T V))
        (orbSup (autSub T (orbSup T V)) (V.subgroupOf (orbSup T V)))) =
      qhatOf (autSub (Mp ⊔ T) (orbSup T V)) := by
  rw [qhatOf_autSub_congr (d38_restrict_orbSup T V), H13.qhatOf_autSub_top,
    autSub_sup (d38r_sup_le_stabSub hD)]

theorem d38_restrict_suzuki (hD : D3Std M Mp T L V) (hLs : IsSimpleGroup ↥L)
    (hcen : Subgroup.center ↥L = ⊥) {n : ℕ} (hsz : CFSG.Blueprint.SuzukiModel ↥L 2 n) :
    ∃ n, CFSG.Blueprint.SuzukiModel
      (↥(autSub L (orbSup T V)) ⧸ Subgroup.center ↥(autSub L (orbSup T V))) 2 n := by
  set Y := orbSup T V with hY
  have hX := d38r_sup_le_stabSub hD
  have hLMp : L ≤ Mp := by
    rw [hD.hyp.Mp_eq]
    exact le_conjClosure L T
  have hLY : L ≤ stabSub Y := (hLMp.trans le_sup_left).trans hX
  have hne : ¬ L ≤ centSub Y := fun h => d38r_autSub_L_ne_bot hD
    ((autSub_eq_bot_iff hLY).mpr (commSub_eq_bot_iff.mpr fun y hy l hl => h hl y hy))
  have hfaith : L ⊓ centSub Y = ⊥ := inf_centSub_eq_bot_of_isSimpleGroup hLs hLY hne
  let e : ↥L ≃* ↥(autSub L Y) := autSubEquivOfFaithful hLY hfaith
  have hc : Subgroup.center ↥(autSub L Y) = ⊥ := by
    have h1 : Nat.card (Subgroup.center ↥(autSub L Y)) = 1 := by
      rw [← Nat.card_congr (Subgroup.centerCongr e).toEquiv, hcen, Subgroup.card_bot]
    exact Subgroup.eq_bot_of_card_eq _ h1
  let e2 : (↥(autSub L Y) ⧸ Subgroup.center ↥(autSub L Y)) ≃* ↥(autSub L Y) :=
    (QuotientGroup.quotientMulEquivOfEq hc).trans QuotientGroup.quotientBot
  exact ⟨n, H13.suzukiModel_congr (e2.trans e.symm) hsz⟩

omit [Finite W] in
theorem d38_restrict_stabSub {A : Subgroup (MulAut W)} {Y : Subgroup W} (hAY : A ≤ stabSub Y)
    (hVY : V ≤ Y) (h : autSub A Y ≤ stabSub (V.subgroupOf Y)) : A ≤ stabSub V := by
  intro a ha u
  have haS : a ∈ stabSub Y := hAY ha
  by_cases hu : u ∈ Y
  · exact h (mem_autSub.mpr ⟨⟨a, haS⟩, ha, rfl⟩) ⟨u, hu⟩
  · have h1 : u ∉ V := fun h => hu (hVY h)
    have h2 : a u ∉ Y := fun h => hu ((haS u).mp h)
    exact ⟨fun h => absurd (hVY h) h2, fun h => absurd h h1⟩

end Restrict

end CFSG.Quasithin.RonanD38
