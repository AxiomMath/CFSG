module

public import CFSG.Quasithin.EmptyFaithful.F918C16
public import CFSG.Quasithin.Background.F918C3
public import CFSG.Quasithin.EmptyFaithful.F918C10
public import CFSG.Quasithin.EmptyFaithful.F918C15

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.F7
open scoped Pointwise commutatorElement

section Out

variable {W : Type} [CommGroup W]

theorem hout_of_modDynkin {L : Subgroup (MulAut W)} {σ : MulAut W} (hL32 : IsPSL 3 2 1 ↥L)
    (h : ModDynkin L σ) :
    ¬ ∃ l₀ ∈ L, ∀ x ∈ L, (σ * l₀⁻¹) * x = x * (σ * l₀⁻¹) := by
  rcases h with ⟨-, hout⟩ | ⟨⟨e⟩, -⟩
  · exact hout
  · exfalso
    have h1 := card_eq_168_of_isPSL_three_two hL32
    have h2 : Nat.card ↥L = Nat.card ↥(alternatingGroup (Fin 6)) := Nat.card_congr e.toEquiv
    have h3 : Nat.card ↥(alternatingGroup (Fin 6)) = 360 := by
      rw [Nat.card_eq_fintype_card, card_alternatingGroup, Fintype.card_fin]
      decide
    omega

end Out

section Case2

attribute [local instance] commGroupOfFact

variable {G : Type} [Group G] [Finite G] {T V L V₁ Vp H K : Subgroup G}

theorem case2_aux
    (h : HypF918 T V L V₁ Vp H K) (hH : SQTKGroup ↥H) (hodd : OddCoreModTwoTrivial H)
    (hS' : IsSimpleGroup (KBar K)) (hL : KbarIsL3Two K) (hHeq : H = conjClosure K T ⊔ T)
    (hKne : conjClosure K T ≠ K) {t : G} (htT : t ∈ T) (htK : t ∉ Subgroup.normalizer (K : Set G))
    (htt : t * t ∈ Subgroup.normalizer (K : Set G)) (hKt : conjSub t K ∈ cComp H)
    (hall : ∀ L ∈ cComp H, L = K ∨ L = conjSub t K)
    (hKtV₁ : ∀ g ∈ conjSub t K, ∀ v ∈ V₁, g * v = v * g) {s : G} (hsT : s ∈ T)
    (hsK : s ∈ Subgroup.normalizer (K : Set G)) (hdyn : KbarNontrivialOnDynkin K s)
    (h37 : A37ForSQTK) (h38 : A38ForSQTK) (hD36 : D36) (hD37 : D37) (hD321 : D321) (hI5 : Insp5a)
    (hTens : TensorTwistL32)
    (hNo : HasNoFaithfulFFModulesMod (conjClosure K T ⊔ T) (pCoreOf 2 H)) :
    ∃ U₁ : Subgroup G, V₁ ≤ U₁ ∧ ⁅conjClosure Vp H, K⁆ ⊔ V₁ = U₁ ⊔ conjSub s U₁ ∧
      IsNaturalLike K V₁ U₁ ∧ ⁅⁅conjClosure Vp H, K⁆, conjSub t K⁆ = ⊥ := by
  have hKtle : conjSub t K ≤ conjClosure K T := by
    rintro _ ⟨z, hz, rfl⟩
    exact mem_conjClosure htT hz
  obtain ⟨I, hV₁I, hIU, W, hW, hirrU⟩ := exists_isIrrPlusTildeU h
  have hirrT := isIrrPlusTildeT_of_ambient h hIU W hW hirrU
  have hF := factElem h hIU
  have hIHN := h.conjClosure_le_normalizer_V₁ hIU
  have hIH := le_normalizer_conjClosure I H
  have hKH : K ≤ H := le_of_mem_cComp h.K_cComp
  have hKtH : conjSub t K ≤ H := le_of_mem_cComp hKt
  have htH : t ∈ H := h.T_le_H htT
  have hsH : s ∈ H := h.T_le_H hsT
  have hV₁IH : V₁ ≤ conjClosure I H := hV₁I.trans (le_conjClosure I H)
  have hIHUU : conjClosure I H ≤ conjClosure Vp H := conjClosure_le_conjClosure_U hIU le_rfl
  have hirr' : subM V₁ (conjClosure I H) I ∈
      IrrPlusOn (autIH V₁ I H (conjClosure K T))
        (orbSup (autIH V₁ I H T) (subM V₁ (conjClosure I H) I)) (autIH V₁ I H T) := hirrT
  have hD := d31_of_hyp h hH hIU hV₁I hirr'
  have hnt := hnt_of_irrSec h hIU hirr'.1.2.2.2.1
  have hKI := K₀_le_normalizer_of_isInv h hIU hV₁I hirr'.1.2.1
  obtain ⟨B, hA⟩ := qOff_of_hyp h hIU hV₁I hKI hnt
  have hstd : D3Std (autIH V₁ I H H) (autIH V₁ I H (conjClosure K T)) (autIH V₁ I H T)
      (autIH V₁ I H K) (subM V₁ (conjClosure I H) I) := ⟨hD, hA.qhat_VT hD.exp, hirr'⟩
  obtain ⟨-, hFive⟩ := F918_5 h hH hKne hV₁I hIU hirrT hD36 hD37 hD321 hI5 h37 h38
  have hF5 := hFive t htT htK
  obtain ⟨-, -, hdata⟩ := five_prelim h hH hKne hIU hnt h37 h38
  obtain ⟨ht'T, -, hMp, -⟩ := hdata t htT htK
  obtain ⟨-, hdataG⟩ := five_group_data h hH h37 h38 hKne
  obtain ⟨-, -, hcommK, -⟩ := hdataG t htT htK
  set φ := actH h.H_le_normalizer_V₁ hIH with hφ
  have hconj : conjAutSub (φ ⟨t, htH⟩) (autIH V₁ I H K) = autIH V₁ I H (conjSub t K) := by
    rw [autIH_eq_map h hKH, autIH_eq_map h hKtH]
    exact conjAutSub_map_subgroupOf φ htH
  have hLL : ∀ x ∈ autIH V₁ I H K, ∀ y ∈ conjAutSub (φ ⟨t, htH⟩) (autIH V₁ I H K),
      x * y = y * x := by
    intro x hx y hy
    rw [hconj, autIH_eq_map h hKtH] at hy
    rw [autIH_eq_map h hKH] at hx
    obtain ⟨a, ha, rfl⟩ := hx
    obtain ⟨b, hb, rfl⟩ := hy
    have ha' : (a : G) ∈ K := Subgroup.mem_subgroupOf.mp ha
    have hb' : (b : G) ∈ conjSub t K := Subgroup.mem_subgroupOf.mp hb
    have hab : (a : G) * b * (a : G)⁻¹ * (b : G)⁻¹ ∈ pCoreOf 2 H := by
      have := hcommK (Subgroup.commutator_mem_commutator ha' hb')
      simpa [commutatorElement_def] using this
    have h1 := h.actH_eq_one_of_mem_pCoreOf hIU (x := a * b * a⁻¹ * b⁻¹) hab
    simp only [map_mul, map_inv] at h1
    exact mul_inv_eq_iff_eq_mul.mp (mul_inv_eq_one.mp h1)
  have htt' : φ ⟨t, htH⟩ * φ ⟨t, htH⟩ ∈
      Subgroup.normalizer ((autIH V₁ I H K : Subgroup _) : Set _) := by
    have := actH_mem_normalizer_autIH (I := I) h (H.mul_mem htH htH) htt
    rw [show (⟨t * t, H.mul_mem htH htH⟩ : ↥H) = ⟨t, htH⟩ * ⟨t, htH⟩ from rfl, map_mul] at this
    exact this
  have hS : IsSimpleGroup (↥K ⧸ CFSG.pCore 2 ↥K) := MulEquiv.isSimpleGroup (kbarEquiv K).symm
  have hne : autIH V₁ I H K ≠ ⊥ := by
    rw [autIH_eq_map h hKH]
    exact map_K_ne_bot h hIU hnt
  obtain ⟨e⟩ := nonempty_mulEquiv_quotient_autI h hIU hS hne
  have hL32 : IsPSL 3 2 1 ↥(autIH V₁ I H K) := by
    obtain ⟨eL⟩ := hL
    exact CFSG.QuasithinUnique.Vol2Native.A312L.Seven.isPSL_three_two
      ((e.symm.trans (kbarEquiv K).symm).trans eL)
  have hout := hout_of_modDynkin hL32 (modDynkin_of_group h hIU hS' hne hsH hsK hdyn)
  have hσT := actH_mem_autIH_of_mem (I := I) h h.T_le_H hsT
  have hσL := actH_mem_normalizer_autIH (I := I) h hsH hsK
  obtain ⟨V', hcd, hV'⟩ := case2_core hTens hstd hMp ht'T htt' hLL hσT hσL hL32 hout hF5
  have hbetween : ∀ x ∈ H, ∀ J : Subgroup G, V₁ ≤ J → J ≤ conjClosure I H →
      V₁ ≤ conjSub x J ∧ conjSub x J ≤ conjClosure I H := by
    intro x hx J hV₁J hJI
    refine ⟨fun v hv => ?_, fun y hy => ?_⟩
    · rw [mem_conjSub]
      exact hV₁J ((Subgroup.mem_normalizer_iff''.mp (h.H_le_normalizer_V₁ hx) v).mp hv)
    · rw [mem_conjSub] at hy
      have := (Subgroup.mem_normalizer_iff.mp (hIH hx) (x⁻¹ * y * x)).mp (hJI hy)
      simpa [mul_assoc] using this
  obtain ⟨U₁, hV₁U₁, hU₁IH, hsubU₁⟩ : ∃ U₁ : Subgroup G, V₁ ≤ U₁ ∧ U₁ ≤ conjClosure I H ∧
      subM V₁ (conjClosure I H) U₁ = V' := by
    rcases hV' with rfl | rfl
    · exact ⟨I, hV₁I, le_conjClosure I H, rfl⟩
    · have htinv : t⁻¹ ∈ H := H.inv_mem htH
      obtain ⟨hb1, hb2⟩ := hbetween t⁻¹ htinv I hV₁I (le_conjClosure I H)
      refine ⟨conjSub t⁻¹ I, hb1, hb2, ?_⟩
      have h1 := map_actH_subM h.H_le_normalizer_V₁ hIHN hIH hV₁I (le_conjClosure I H) ⟨t⁻¹, htinv⟩
      have hxinv : (⟨t, htH⟩ : ↥H)⁻¹ = ⟨t⁻¹, htinv⟩ := Subtype.ext rfl
      have hinv : (φ ⟨t, htH⟩)⁻¹ = φ ⟨t⁻¹, htinv⟩ := by rw [← map_inv, hxinv]
      rw [← h1, hinv]
  subst hsubU₁
  obtain ⟨hU₂1, hU₂2⟩ := hbetween s hsH U₁ hV₁U₁ hU₁IH
  have hsubU₂ : subM V₁ (conjClosure I H) (conjSub s U₁) =
      (subM V₁ (conjClosure I H) U₁).map (φ ⟨s, hsH⟩).toMonoidHom :=
    (map_actH_subM h.H_le_normalizer_V₁ hIHN hIH hV₁U₁ hU₁IH ⟨s, hsH⟩).symm
  have hsum' : commV (autIH V₁ I H K) =
      subM V₁ (conjClosure I H) U₁ ⊔ subM V₁ (conjClosure I H) (conjSub s U₁) := by
    rw [hsubU₂]
    exact hcd.direct.1.symm
  have hsupeq : ⁅conjClosure I H, K⁆ ⊔ V₁ = U₁ ⊔ conjSub s U₁ :=
    comm_sup_eq_of_commV h hIU hV₁U₁ hU₁IH hU₂2 hsum'
  have hZ := hZ_of_cComp_le hodd h.K₀_le_H fun L hL' => by
    rcases hall L hL' with hLK | hLK
    · rw [hLK]
      exact le_conjClosure K T
    · rw [hLK]
      exact hKtle
  have hI := isIrrPlusTilde_of_module h hV₁I hIU hirrT
  have h7 := h.F918_7' hHeq hZ hV₁I hIU hI hNo
  have hB := commutator_le_of_h7 h hIU hV₁I h7.symm
  have hsup : ⁅conjClosure Vp H, K⁆ ⊔ V₁ = U₁ ⊔ conjSub s U₁ := by
    apply le_antisymm
    · rw [← hsupeq]
      exact sup_le hB le_sup_right
    · rw [← hsupeq]
      exact sup_le_sup_right (Subgroup.commutator_mono hIHUU le_rfl) V₁
  obtain ⟨hirrSec, -⟩ := isIrredOnSection_of_isIrr h hIU hV₁U₁ hU₁IH hcd.irr
  have hrel : V₁.relIndex U₁ = 2 ^ 3 := by
    rw [← card_subM hIHN hV₁U₁ hU₁IH]
    simpa using hcd.card
  have hnat : IsNaturalLike K V₁ U₁ := Or.inl ⟨hL, mIdx_eq_of_card hrel, hirrSec⟩
  have hV₁C : V₁ ≤ centralizerMod V₁ (conjClosure I H) (conjSub t K) :=
    le_centralizerMod h.H_le_normalizer_V₁ hKtH hV₁IH
  have hcent : U₁ ⊔ conjSub s U₁ ≤ centralizerMod V₁ (conjClosure I H) (conjSub t K) := by
    refine (subM_le_iff hIHN (hV₁U₁.trans le_sup_left) hV₁C (sup_le hU₁IH hU₂2)).1 ?_
    rw [subM_sup hIHN hU₁IH hU₂2, ← hsum',
      subM_centralizerMod h.H_le_normalizer_V₁ hIHN hIH hKtH hV₁IH le_rfl]
    intro w hw
    refine ⟨mem_subM_iff.mpr w.2, fun a => ?_⟩
    have ha : (a : MulAut _) ∈ conjAutSub (φ ⟨t, htH⟩) (autIH V₁ I H K) := by
      rw [hconj]
      exact a.2
    exact hcd.perp hw _ ha
  have hBV₁ : ⁅⁅conjClosure Vp H, K⁆, conjSub t K⁆ ≤ V₁ := by
    refine Subgroup.commutator_le.mpr fun b hb k' hk' => ?_
    rw [commutatorElement_def]
    have hb' : b ∈ U₁ ⊔ conjSub s U₁ := hsup ▸ Subgroup.mem_sup_left hb
    exact (mem_centralizerMod.mp (hcent hb')).2.2 k' hk'
  have hperf' : ⁅conjSub t K, conjSub t K⁆ = conjSub t K := perfect_of_mem_cComp hKt
  have hV₁K' : ⁅V₁, conjSub t K⁆ = ⊥ := by
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro v hv
    exact Subgroup.mem_centralizer_iff.mpr fun g hg => hKtV₁ g hg v hv
  have h2 : ⁅⁅conjSub t K, ⁅conjClosure Vp H, K⁆⁆, conjSub t K⁆ ≤ (⊥ : Subgroup G) := by
    rw [Subgroup.commutator_comm (conjSub t K) ⁅conjClosure Vp H, K⁆]
    calc ⁅⁅⁅conjClosure Vp H, K⁆, conjSub t K⁆, conjSub t K⁆ ≤ ⁅V₁, conjSub t K⁆ :=
          Subgroup.commutator_mono hBV₁ le_rfl
      _ = ⊥ := hV₁K'
  have h3 := commutator_le_of_commutator_commutator_le (Q := (⊥ : Subgroup G))
    (A := ⁅conjClosure Vp H, K⁆) (P := conjSub t K)
    (fun x _ => by rw [Subgroup.mem_normalizer_iff]; intro y; simp [Subgroup.mem_bot])
    (fun x _ => by rw [Subgroup.mem_normalizer_iff]; intro y; simp [Subgroup.mem_bot]) hperf' h2
  exact ⟨U₁, hV₁U₁, hsup, hnat, le_bot_iff.mp h3⟩

end Case2

end CFSG.Quasithin
