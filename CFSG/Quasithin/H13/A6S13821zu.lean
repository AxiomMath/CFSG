module

public import CFSG.Quasithin.H13.A6S13821zt
public import CFSG.Quasithin.H13.A6S13821zq
public import CFSG.Quasithin.H13.A6S13821zr

public section

namespace CFSG.Quasithin.H13.A6.A6S20

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin
open CFSG.Quasithin.F7

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem tildeOf_le_of_le_sup {V₁ X Y : Subgroup G} (hY : Y ≤ Subgroup.normalizer (V₁ : Set G))
    (h : X ≤ Y ⊔ V₁) : tildeOf V₁ X ≤ tildeOf V₁ Y := by
  intro w hw
  obtain ⟨x, hxX, rfl⟩ := mem_secImg.mp hw
  obtain ⟨a, ha, b, hb, hab⟩ := (F1.mem_sup_iff_exists_mul_of_le_normalizer hY).mp (h hxX)
  refine mem_secImg.mpr ⟨⟨a, hY ha⟩, ha, ?_⟩
  rw [secMk_eq_secMk_iff]
  have e : (a : G)⁻¹ * (x : G) = b := by rw [hab]; group
  show (a : G)⁻¹ * (x : G) ∈ V₁
  rw [e]
  exact hb

omit [Finite G] in
theorem le_sup_of_tildeOf_le {V₁ X Y : Subgroup G} (hX : X ≤ Subgroup.normalizer (V₁ : Set G))
    (h : tildeOf V₁ X ≤ tildeOf V₁ Y) : X ≤ Y ⊔ V₁ := by
  intro x hx
  obtain ⟨y, hyY, hy⟩ := mem_secImg.mp (h (secMk_mem_secImg
    (A := Subgroup.normalizer (V₁ : Set G)) (B := V₁) (x := ⟨x, hX hx⟩) hx))
  rw [secMk_eq_secMk_iff] at hy
  have e : x = (y : G) * ((y : G)⁻¹ * x) := by group
  rw [e]
  exact Subgroup.mul_mem_sup hyY hy

attribute [local instance] commGroupOfFact

theorem commutator_le_sup_sl2 (hA21 : AsA21SQTKSection)
    (h42 : AsB42) (hF10 : Vol2.Ch10.SecA.Facts10_1) {T V L V₁ Vp H K I : Subgroup G}
    (hSQ : SQTKGroup ↥H) (hF : HypF918 T V L V₁ Vp H K) (hK₀ : conjClosure K T = K) {n : ℕ}
    (hn : 2 ≤ n) {F : Type} [Field F] [Finite F] (hFn : Nat.card F = 2 ^ n)
    (eK : (↥K ⧸ CFSG.pCore 2 ↥K) ≃* Matrix.SpecialLinearGroup (Fin 2) F)
    (hS' : IsSimpleGroup (↥K ⧸ CFSG.pCore 2 ↥K))
    (hV₁I : V₁ ≤ I) (hIU : I ≤ conjClosure Vp H) (hirrT : IsIrrPlusTildeT hF hIU)
    (hTI : T ≤ Subgroup.normalizer (I : Set G))
    [Fact (IsElemAbelian 2 (tildeOf V₁ (conjClosure I H)))]
    (hFF : IsFFModule (autSec (autIH V₁ I H K ⊔ autIH V₁ I H T) (subM V₁ (conjClosure I H) I)
      (fixV (autIH V₁ I H (conjClosure K T)))))
    {c : G} (hcH : c ∈ H) (hII : I ⊓ conjSub c I ≤ centralizerMod V₁ I K)
    (hJN : K ⊔ T ≤ Subgroup.normalizer ((I ⊔ conjSub c I : Subgroup G) : Set G))
    (hRc : ∀ b ∈ pCoreOf 2 (L₁Of L V₁ ⊔ T), c * b * c⁻¹ * b⁻¹ ∈ pCoreOf 2 H) :
    ⁅conjClosure Vp H, K⁆ ≤ I ⊔ conjSub c I := by
  classical
  set J := I ⊔ conjSub c I with hJ
  set U := conjClosure Vp H with hUdef
  have h1 := hF.toHypF98.toHypF91
  have hKH : K ≤ H := le_of_mem_cComp hF.K_cComp
  have hTH : T ≤ H := hF.T_le_H
  have hHV₁ : H ≤ Subgroup.normalizer (V₁ : Set G) := hF.H_le_normalizer_V₁
  have hUH : U ≤ H := h1.conjClosure_Vp_le_pCoreOf.trans (pCoreOf_le 2 H)
  have hcU : c ∈ Subgroup.normalizer (U : Set G) := le_normalizer_conjClosure Vp H hcH
  have hcK : c ∈ Subgroup.normalizer (K : Set G) := by
    have := hF.K₀_normal hcH
    rwa [hK₀] at this
  have hcV₁ : c ∈ Subgroup.normalizer (V₁ : Set G) := hHV₁ hcH
  have hirr := isIrrPlusTilde_of_module hF hV₁I hIU hirrT
  rw [hK₀] at hirr
  have hIc : conjSub c I ≤ U := by
    rw [← conjSub_eq_of_mem_normalizer hcU]
    exact conjSub_mono c hIU
  have hJU : J ≤ U := sup_le hIU hIc
  have hV₁J : V₁ ≤ J := hV₁I.trans le_sup_left
  have hJN' : conjClosure K T ⊔ T ≤ Subgroup.normalizer (J : Set G) := by rw [hK₀]; exact hJN
  have hcomm : ⁅U, K⁆ ≤ H := Subgroup.commutator_le.mpr fun u hu k hk =>
    H.mul_mem (H.mul_mem (H.mul_mem (hUH hu) (hKH hk)) (H.inv_mem (hUH hu))) (H.inv_mem (hKH hk))
  have hIle : I ≤ ⁅U, K⁆ ⊔ V₁ := by
    refine (le_sup_of_tildeOf_le (hIU.trans (hUH.trans hHV₁)) hirr.2.1.ge).trans ?_
    exact sup_le_sup_right (Subgroup.commutator_mono hIU le_rfl) _
  have hJle : J ≤ ⁅U, K⁆ ⊔ V₁ := by
    refine sup_le hIle ?_
    have h2 := conjSub_mono c hIle
    rwa [conjSub_sup, ← conjSub_commutator, conjSub_eq_of_mem_normalizer hcU,
      conjSub_eq_of_mem_normalizer hcK, conjSub_eq_of_mem_normalizer hcV₁] at h2
  have hle1 : tildeOf V₁ J ≤ tildeOf V₁ ⁅U, conjClosure K T⁆ := by
    rw [hK₀]
    exact tildeOf_le_of_le_sup (hcomm.trans hHV₁) hJle
  suffices hmain : tildeOf V₁ J = tildeOf V₁ ⁅U, conjClosure K T⁆ by
    rw [hK₀] at hmain
    have h2 := le_sup_of_tildeOf_le (hcomm.trans hHV₁) hmain.ge
    rwa [sup_eq_left.mpr hV₁J] at h2
  by_contra ha
  obtain ⟨B, hB, h2a⟩ := f918_6_core hF hV₁J hJU hJN' hle1 ha
  have hBT : B ≤ T := hB.1.trans hF.pCoreOf_L₁T_le_T
  have hBH : B ≤ H := hBT.trans hTH
  set C := centralizerMod V₁ I (conjClosure K T) with hC
  set C' := centralizerMod V₁ (conjSub c I) (conjClosure K T) with hC'
  have hUab := hF.toHypF98.F911_3
  have hJI : J ≤ Subgroup.normalizer (I : Set G) :=
    hJU.trans (HypF91.le_normalizer_of_isElemAbelian_le hUab hIU)
  have hBcQ : ∀ b ∈ B, c⁻¹ * b * c ∈ T := by
    intro b hb
    have hq := hRc b (hB.1 hb)
    have hq' : c⁻¹ * b * c * b⁻¹ ∈ pCoreOf 2 H := by
      have := (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 H (H.inv_mem hcH)) _).mp
        ((pCoreOf 2 H).inv_mem hq)
      have e : c⁻¹ * (c * b * c⁻¹ * b⁻¹)⁻¹ * c⁻¹⁻¹ = c⁻¹ * b * c * b⁻¹ := by group
      rwa [e] at this
    have e : c⁻¹ * b * c = (c⁻¹ * b * c * b⁻¹) * b := by group
    rw [e]
    exact T.mul_mem (isSylowTwoOf_pCoreOf_le h1.sylow_H hq') (hBT hb)
  have hBI' : B ≤ Subgroup.normalizer ((conjSub c I : Subgroup G) : Set G) := fun b hb =>
    mem_normalizer_conjSub (hTI (hBcQ b hb))
  have hV₁C : V₁ ≤ C := le_centralizerMod hHV₁ hF.K₀_le_H hV₁I
  have hIC : I ≤ Subgroup.normalizer (C : Set G) :=
    HypF91.le_normalizer_of_isElemAbelian_le (isElemAbelian_mono hUab hIU)
      (centralizerMod_le_left _ _ _)
  have hI'C' : conjSub c I ≤ Subgroup.normalizer (C' : Set G) :=
    HypF91.le_normalizer_of_isElemAbelian_le (isElemAbelian_mono hUab hIc)
      (centralizerMod_le_left _ _ _)
  have hII' : I ⊓ conjSub c I ≤ C' := by
    intro x hx
    have h3 := hII hx
    refine ⟨hx.2, h3.2.1, ?_⟩
    rw [hK₀]
    exact h3.2.2
  have hcount := relIndex_mul_le_sup (B := B) hV₁I le_sup_left le_sup_right hJI
    (hBT.trans hTI) hBI' hV₁C hIC hI'C' hII'
  have hCc : conjSub c C = C' := by
    rw [hC, hC', conjSub_centralizerMod, conjSub_eq_of_mem_normalizer hcV₁,
      conjSub_eq_of_mem_normalizer (hF.K₀_normal hcH)]
  have hV₁c : V₁ ≤ conjSub c I := by
    have h3 := conjSub_mono c hV₁I
    rwa [conjSub_eq_of_mem_normalizer hcV₁] at h3
  have hQc : ∀ q ∈ pCoreOf 2 H, ∀ u ∈ conjSub c I, q * u * q⁻¹ * u⁻¹ ∈ V₁ := by
    intro q hq u hu
    rw [h1.pCoreOf_eq_centralizerMod] at hq
    exact hq.2.2 u (hIc hu)
  have hconj := relIndex_centralizerMod_conjSub (V₁ := V₁) (C := C) (I := I) (B := B)
    (Q := pCoreOf 2 H) (c := c)
    (hCc ▸ le_centralizerMod hHV₁ hF.K₀_le_H hV₁c) (fun b hb => hRc b (hB.1 hb)) hQc hBI'
  rw [hCc] at hconj
  rw [hconj] at hcount
  have hlt : (centralizerMod C I B).relIndex I < (B ⊓ pCoreOf 2 H).relIndex B := by
    by_contra hge
    push Not at hge
    have hβ := relIndex_ne_zero' (B ⊓ pCoreOf 2 H) B
    have hsq : ((B ⊓ pCoreOf 2 H).relIndex B) ^ 2 ≤ (centralizerMod C I B).relIndex I *
        (centralizerMod C I B).relIndex I := by
      rw [sq]
      exact Nat.mul_le_mul hge hge
    have hpos : 0 < ((B ⊓ pCoreOf 2 H).relIndex B) ^ 2 := by positivity
    have hJJ : (centralizerMod V₁ J B).relIndex J =
        (centralizerMod V₁ (I ⊔ conjSub c I) B).relIndex (I ⊔ conjSub c I) := rfl
    omega
  have hirr0 := isIrrPlusTilde_of_module hF hV₁I hIU hirrT
  obtain ⟨hB4, hQS, -, ⟨eLs⟩, hexp, hFF2⟩ :=
    ff_data_sl2 hA21 hSQ hF hK₀ eK hS' hV₁I hIU hirrT hTI hFF
  have hstrong := isStrongFFModule_of_lt hF hV₁I hIU hirr0 hTI hQS hB hlt
  obtain ⟨A, hA⟩ := B6.exists_isFFStarOffender hFF2
  exact not_isStrongFFModule_sl2 hF10 hexp hB4 hA (h42 _ hexp _ _ hB4 A hA) hn hFn eLs hstrong

end CFSG.Quasithin.H13.A6.A6S20
