module

public import CFSG.Milestones.ASVolI.B610.CompA
public import CFSG.Milestones.ASVolI.B610.Targets
public import CFSG.Quasithin.Background.C116Bridge.Main
public import CFSG.Milestones.ASVolI.B610.FamA

public section

namespace CFSG.Quasithin.B610T

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open scoped commutatorElement

variable {G : Type} [Group G]

theorem burnsideB610_mem_of_convI_mem {H V Y : Subgroup G} {hV : IsElemAbelian 2 V}
    (hYH : Y ≤ H) (hCY : H ⊓ Subgroup.centralizer (V : Set G) ≤ Y) {x : G} (hxH : x ∈ H)
    (hxN : x ∈ Subgroup.normalizer (V : Set G)) (hx : convI hV ⟨x, hxN⟩ ∈ autI hV Y) : x ∈ Y := by
  obtain ⟨y, hyY, hyx⟩ := (mem_autI hV).1 hx
  have hc : (y : G)⁻¹ * x ∈ Subgroup.centralizer (V : Set G) := by
    have h1 : convI hV (y⁻¹ * ⟨x, hxN⟩) = 1 := by rw [map_mul, map_inv, hyx, inv_mul_cancel]
    have := (convI_eq_one_iff hV _).1 h1
    simpa using this
  have h2 := hCY ⟨H.mul_mem (H.inv_mem (hYH hyY)) hxH, hc⟩
  have e : x = (y : G) * ((y : G)⁻¹ * x) := by group
  rw [e]
  exact Y.mul_mem hyY h2

theorem burnsideB610_autI_cjSub' {V : Subgroup G} {hV : IsElemAbelian 2 V} {h : G}
    (hh : h ∈ Subgroup.normalizer (V : Set G)) (L : Subgroup G) :
    autI hV (cjSub h L) = (autI hV L).map (MulAut.conj (convI hV ⟨h, hh⟩)).toMonoidHom :=
  (autI_cjSub hV hh L).symm

section Comp

variable [Finite G] {H T V L : Subgroup G} {F : Type} [Field F] [Fintype F]

theorem burnsideB610_isComponentOf (hV : IsElemAbelian 2 V) (hHV : H ≤ Subgroup.normalizer (V : Set G))
    (hL : IsSubnormal L H) (D : NatData L V F) (h4 : ∃ s : Finset F, s.card = 4) :
    IsComponentOf (autI hV (L ⊔ (H ⊓ Subgroup.centralizer (V : Set G)))) (autI hV H) := by
  have hLH : L ≤ H := hL.le
  have hLV : L ≤ Subgroup.normalizer (V : Set G) := hLH.trans hHV
  have hCN : H ⊓ Subgroup.centralizer (V : Set G) ≤ Subgroup.normalizer (V : Set G) :=
    inf_le_left.trans hHV
  have he : autI hV (L ⊔ (H ⊓ Subgroup.centralizer (V : Set G))) = autI hV L := by
    rw [autI_sup hV hLV hCN, (autI_eq_bot_iff hV hCN).2 inf_le_right, sup_bot_eq]
  rw [he]
  refine ⟨autI_mono hV hLH, ?_, burnsideB610_isQuasisimple_autI D h4 hV hLV⟩
  exact (CFSG.Open.IsSubnormal.comap (Subgroup.normalizer (V : Set G)).subtype hL).map (convI hV)

theorem burnsideB610_isComponentOf_cjSub (hV : IsElemAbelian 2 V)
    (hHV : H ≤ Subgroup.normalizer (V : Set G)) (hL : IsSubnormal L H) (D : NatData L V F)
    (h4 : ∃ s : Finset F, s.card = 4) {h : G} (hh : h ∈ H) :
    IsComponentOf (autI hV (cjSub h (L ⊔ (H ⊓ Subgroup.centralizer (V : Set G))))) (autI hV H) := by
  rw [burnsideB610_autI_cjSub' (hHV hh)]
  exact B113.isComponentOf_conj (burnsideB610_isComponentOf hV hHV hL D h4)
    (convI_mem_autI hV hh (hHV hh))

theorem burnsideB610_cent_le_cjSub (hHV : H ≤ Subgroup.normalizer (V : Set G)) {h : G}
    (hh : h ∈ H) : H ⊓ Subgroup.centralizer (V : Set G) ≤
      cjSub h (L ⊔ (H ⊓ Subgroup.centralizer (V : Set G))) := by
  rintro c ⟨hcH, hcV⟩
  rw [mem_cjSub]
  refine Subgroup.mem_sup_right ⟨H.mul_mem (H.mul_mem (H.inv_mem hh) hcH) hh, ?_⟩
  have := B6.conj_mem_centralizer_of_mem_normalizer (V := V)
    ((Subgroup.normalizer (V : Set G)).inv_mem (hHV hh)) hcV
  simpa using this

theorem burnsideB610_cjSub_le (hL : IsSubnormal L H) {h : G} (hh : h ∈ H) :
    cjSub h (L ⊔ (H ⊓ Subgroup.centralizer (V : Set G))) ≤ H :=
  cjSub_le (Subgroup.le_normalizer hh) (sup_le hL.le inf_le_left)

theorem burnsideB610_comm_of_ne (hV : IsElemAbelian 2 V)
    (hHV : H ≤ Subgroup.normalizer (V : Set G)) (hL : IsSubnormal L H) (D : NatData L V F)
    (h4 : ∃ s : Finset F, s.card = 4) {h₁ h₂ : G} (hh₁ : h₁ ∈ H) (hh₂ : h₂ ∈ H)
    (hne : cjSub h₁ (L ⊔ (H ⊓ Subgroup.centralizer (V : Set G))) ≠
      cjSub h₂ (L ⊔ (H ⊓ Subgroup.centralizer (V : Set G)))) :
    ∀ x ∈ cjSub h₁ (L ⊔ (H ⊓ Subgroup.centralizer (V : Set G))),
      ∀ y ∈ cjSub h₂ (L ⊔ (H ⊓ Subgroup.centralizer (V : Set G))),
        x * y * x⁻¹ * y⁻¹ ∈ Subgroup.centralizer (V : Set G) := by
  set L₀ := L ⊔ (H ⊓ Subgroup.centralizer (V : Set G)) with hL₀
  have hK₁ := burnsideB610_isComponentOf_cjSub hV hHV hL D h4 hh₁
  have hK₂ := burnsideB610_isComponentOf_cjSub hV hHV hL D h4 hh₂
  rcases B113.component_le_or_commutator_eq_bot hK₁ hK₂.2.1 with hle | hcomm
  · exfalso
    apply hne
    have hsub : cjSub h₁ L₀ ≤ cjSub h₂ L₀ := by
      intro x hx
      have hxH := burnsideB610_cjSub_le hL hh₁ hx
      exact burnsideB610_mem_of_convI_mem (burnsideB610_cjSub_le hL hh₂)
        (burnsideB610_cent_le_cjSub hHV hh₂) hxH (hHV hxH)
        (hle (convI_mem_autI hV hx (hHV hxH)))
    exact Subgroup.eq_of_le_of_card_ge hsub (by rw [card_cjSub, card_cjSub])
  · intro x hx y hy
    have hxH := burnsideB610_cjSub_le hL hh₁ hx
    have hyH := burnsideB610_cjSub_le hL hh₂ hy
    have hc := (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm)
      (convI_mem_autI hV hx (hHV hxH))
    have hcy := Subgroup.mem_centralizer_iff.mp hc _ (convI_mem_autI hV hy (hHV hyH))
    have h1 : convI hV (⟨x, hHV hxH⟩ * ⟨y, hHV hyH⟩ * (⟨x, hHV hxH⟩ : ↥(Subgroup.normalizer
        (V : Set G)))⁻¹ * (⟨y, hHV hyH⟩ : ↥(Subgroup.normalizer (V : Set G)))⁻¹) = 1 := by
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, ← hcy]
      group
    have := (convI_eq_one_iff hV _).1 h1
    simpa using this

theorem burnsideB610_le_normalizer_cjSub (hV : IsElemAbelian 2 V)
    (hHV : H ≤ Subgroup.normalizer (V : Set G)) (hL : IsSubnormal L H) (D : NatData L V F)
    (h4 : ∃ s : Finset F, s.card = 4) {h₁ h₂ : G} (hh₁ : h₁ ∈ H) (hh₂ : h₂ ∈ H) :
    cjSub h₂ (L ⊔ (H ⊓ Subgroup.centralizer (V : Set G))) ≤
      Subgroup.normalizer ((cjSub h₁ (L ⊔ (H ⊓ Subgroup.centralizer (V : Set G))) :
        Subgroup G) : Set G) := by
  set L₀ := L ⊔ (H ⊓ Subgroup.centralizer (V : Set G)) with hL₀
  by_cases heq : cjSub h₁ L₀ = cjSub h₂ L₀
  · rw [heq]
    exact Subgroup.le_normalizer
  have key : ∀ y ∈ cjSub h₂ L₀, ∀ x ∈ cjSub h₁ L₀, y * x * y⁻¹ ∈ cjSub h₁ L₀ := by
    intro y hy x hx
    have h1 := burnsideB610_comm_of_ne hV hHV hL D h4 hh₂ hh₁ (Ne.symm heq) y hy x hx
    have hyH := burnsideB610_cjSub_le hL hh₂ hy
    have hxH := burnsideB610_cjSub_le hL hh₁ hx
    have h2 : y * x * y⁻¹ * x⁻¹ ∈ H :=
      H.mul_mem (H.mul_mem (H.mul_mem hyH hxH) (H.inv_mem hyH)) (H.inv_mem hxH)
    have h3 := burnsideB610_cent_le_cjSub (L := L) hHV hh₁ ⟨h2, h1⟩
    have e : y * x * y⁻¹ = (y * x * y⁻¹ * x⁻¹) * x := by group
    rw [e]
    exact Subgroup.mul_mem _ h3 hx
  intro y hy
  exact B6.mem_normalizer_of_forall_mem (fun x hx => key y hy x hx)
    (fun x hx => by simpa using key y⁻¹ (Subgroup.inv_mem _ hy) x hx)

theorem burnsideB610_triv_of_ne (hV : IsElemAbelian 2 V)
    (hHV : H ≤ Subgroup.normalizer (V : Set G)) (hL : IsSubnormal L H) (D : NatData L V F)
    (h4 : ∃ s : Finset F, s.card = 4) {h₁ h₂ : G} (hh₁ : h₁ ∈ H) (hh₂ : h₂ ∈ H)
    (hne : cjSub h₁ (L ⊔ (H ⊓ Subgroup.centralizer (V : Set G))) ≠
      cjSub h₂ (L ⊔ (H ⊓ Subgroup.centralizer (V : Set G))))
    (D₁ : NatData (cjSub h₁ (L ⊔ (H ⊓ Subgroup.centralizer (V : Set G)))) V F)
    (D₂ : NatData (cjSub h₂ (L ⊔ (H ⊓ Subgroup.centralizer (V : Set G)))) V F) :
    cjSub h₂ (L ⊔ (H ⊓ Subgroup.centralizer (V : Set G))) ≤
      Subgroup.centralizer ((⁅V, cjSub h₁ (L ⊔ (H ⊓ Subgroup.centralizer (V : Set G)))⁆ :
        Subgroup G) : Set G) := by
  set L₀ := L ⊔ (H ⊓ Subgroup.centralizer (V : Set G)) with hL₀
  have hX₁V : cjSub h₁ L₀ ≤ Subgroup.normalizer (V : Set G) :=
    (burnsideB610_cjSub_le hL hh₁).trans hHV
  have hYN : cjSub h₂ L₀ ≤ nLV (cjSub h₁ L₀) V := fun y hy =>
    ⟨burnsideB610_le_normalizer_cjSub hV hHV hL D h4 hh₁ hh₂ hy,
      hHV (burnsideB610_cjSub_le hL hh₂ hy)⟩
  have hY := burnsideB610_comm_of_ne hV hHV hL D h4 hh₂ hh₁ (Ne.symm hne)
  have hperf₂ := burnsideB610_le_commutator_sup D₂ h4
  have hact := burnsideB610_act_eq_one_of_commute D₁ hX₁V hYN hY hperf₂
  have hperf₁ := burnsideB610_le_commutator_sup D₁ h4
  intro y hy
  have h1 := burnsideB610_centralizes_of_act_eq_one D₁ hV hX₁V hperf₁ ⟨y, hYN hy⟩ (hact y hy)
  rw [Subgroup.mem_centralizer_iff]
  intro u hu
  exact (h1 u hu).symm

theorem burnsideB610_two_dvd_card_autI (hV : IsElemAbelian 2 V)
    (hLV : L ≤ Subgroup.normalizer (V : Set G)) (D : NatData L V F) {n : ℕ} (hn : 1 ≤ n)
    (hF : Nat.card F = 2 ^ n) : 2 ∣ Nat.card (autI hV L) := by
  obtain ⟨ψ, hψi, hψr⟩ := D.exists_psi hV hLV
  have h1 : Nat.card (autI hV L) = Nat.card (Matrix.SpecialLinearGroup (Fin 2) F) := by
    rw [← hψr]
    exact (Nat.card_congr (MonoidHom.ofInjective hψi).toEquiv).symm
  rw [h1, CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two, hF]
  exact Dvd.dvd.mul_right (dvd_pow_self 2 (by omega)) _

theorem burnsideB610_thompsonJ_le_normalizer (hred : IsTwoReducedIn H V)
    (hT : IsSylowTwoOf T H) (hL : IsSubnormal L H) (D : NatData L V F)
    (h4 : ∃ s : Finset F, s.card = 4) {h : G} (hh : h ∈ H) :
    thompsonJ T ≤ Subgroup.normalizer ((cjSub h (L ⊔ (H ⊓ Subgroup.centralizer (V : Set G))) :
      Subgroup G) : Set G) := by
  set L₀ := L ⊔ (H ⊓ Subgroup.centralizer (V : Set G)) with hL₀
  have hV : IsElemAbelian 2 V := hred.2.2.1
  have hHV : H ≤ Subgroup.normalizer (V : Set G) := hred.2.1
  have hcomp := burnsideB610_isComponentOf_cjSub hV hHV hL D h4 hh
  have hnorm := C116Bridge.thompsonJ_normalizes_components hred hT
    (autI hV (cjSub h L₀)) hcomp
  have hJT : thompsonJ T ≤ T := iSup₂_le fun A hA => hA.1
  intro j hj
  have hjH : j ∈ H := hT.1 (hJT hj)
  have hjN : j ∈ Subgroup.normalizer (V : Set G) := hHV hjH
  have hjc : convI hV ⟨j, hjN⟩ ∈ Subgroup.normalizer
      ((autI hV (cjSub h L₀) : Subgroup (MulAut (IntMod V hV))) : Set (MulAut (IntMod V hV))) :=
    hnorm (convI_mem_autI hV hj hjN)
  have he : autI hV (cjSub j (cjSub h L₀)) = autI hV (cjSub h L₀) := by
    rw [burnsideB610_autI_cjSub' hjN]
    exact Subgroup.mem_normalizer_iff_map_conj_eq.mp hjc
  have hX : cjSub h L₀ ≤ H := burnsideB610_cjSub_le hL hh
  have hle : cjSub j (cjSub h L₀) ≤ cjSub h L₀ := by
    intro x hx
    have hxH : x ∈ H := cjSub_le (Subgroup.le_normalizer hjH) hX hx
    refine burnsideB610_mem_of_convI_mem (hV := hV) hX (burnsideB610_cent_le_cjSub hHV hh) hxH
      (hHV hxH) ?_
    rw [← he]
    exact convI_mem_autI hV hx (hHV hxH)
  have heq : cjSub j (cjSub h L₀) = cjSub h L₀ :=
    Subgroup.eq_of_le_of_card_ge hle (by simp only [card_cjSub, le_refl])
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  exact heq

end Comp

theorem burnsideB610_compFamTarget_holds : burnsideB610_CompFamTarget := by
  intro G _ _ H T M V L F _ _ n hMP hred hJ hL hn hFc D
  classical
  haveI : CharP F 2 := charP_of_card_eq_prime_pow hFc
  have hV : IsElemAbelian 2 V := hred.2.2.1
  have hHV : H ≤ Subgroup.normalizer (V : Set G) := hred.2.1
  have hT := hMP.isSylow
  have hLH : L ≤ H := hL.le
  have hLV : L ≤ Subgroup.normalizer (V : Set G) := hLH.trans hHV
  have hF : Nat.card F = 2 ^ n := by rw [Nat.card_eq_fintype_card, hFc]
  have h4 : ∃ s : Finset F, s.card = 4 := by
    have h4le : 4 ≤ (Finset.univ : Finset F).card := by
      rw [Finset.card_univ, hFc]
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
    obtain ⟨s, -, hs⟩ := Finset.exists_subset_card_eq h4le
    exact ⟨s, hs⟩
  set C : Subgroup G := H ⊓ Subgroup.centralizer (V : Set G) with hC
  have hCV : C ≤ Subgroup.centralizer (V : Set G) := inf_le_right
  have hLC : L ≤ Subgroup.normalizer (C : Set G) := fun g hg =>
    Subgroup.inf_normalizer_le_normalizer_inf
      ⟨Subgroup.le_normalizer (hLH hg), B6.le_normalizer_centralizer hHV (hLH hg)⟩
  set L₀ : Subgroup G := L ⊔ C with hL₀
  set D₀ : NatData L₀ V F := burnsideB610_natExt D hV hLV hCV hLC with hD₀
  haveI : Fintype ↥H := Fintype.ofFinite _
  set X : ↥H → Subgroup G := fun h => cjSub (h : G) L₀ with hX
  set Dx : ∀ h : ↥H, NatData (X h) V F := fun h => burnsideB610_natConj D₀ (hHV h.2) with hDx
  set rep : Subgroup G → ↥H := fun Y => if hY : ∃ h : ↥H, X h = Y then hY.choose else 1
    with hrepdef
  have hrep : ∀ h : ↥H, X (rep (X h)) = X h := by
    intro h
    have hex : ∃ h' : ↥H, X h' = X h := ⟨h, rfl⟩
    simp only [hrepdef, dif_pos hex]
    exact hex.choose_spec
  set S : Finset ↥H := (Finset.univ.image X).image rep with hS
  have hmemS : ∀ s ∈ S, rep (X s) = s := by
    intro s hs
    obtain ⟨Y, hY, rfl⟩ := Finset.mem_image.mp hs
    obtain ⟨h, -, rfl⟩ := Finset.mem_image.mp hY
    rw [hrep h]
  have hcov : ∀ h : ↥H, rep (X h) ∈ S := fun h =>
    Finset.mem_image_of_mem _ (Finset.mem_image_of_mem _ (Finset.mem_univ h))
  have hinj : ∀ i ∈ S, ∀ j ∈ S, X i = X j → i = j := by
    intro i hi j hj hij
    rw [← hmemS i hi, ← hmemS j hj, hij]
  have hXle : ∀ i : ↥H, X i ≤ H := fun i => burnsideB610_cjSub_le hL i.2
  have hXV : ∀ i : ↥H, X i ≤ Subgroup.normalizer (V : Set G) := fun i => (hXle i).trans hHV
  have hne : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → X i ≠ X j := fun i hi j hj hij h =>
    hij (hinj i hi j hj h)
  have hperfX : ∀ i : ↥H, X i ≤ ⁅X i, X i⁆ ⊔ (X i ⊓ Subgroup.centralizer (V : Set G)) :=
    fun i => burnsideB610_le_commutator_sup (Dx i) h4
  have hres : twoResidual H ≤ ⨆ i ∈ S, X i := by
    set N : Subgroup G := ⨆ i ∈ S, X i with hN
    have hNH : N ≤ H := iSup₂_le fun i _ => hXle i
    have hcj : ∀ h ∈ H, cjSub h N ≤ N := by
      intro h hh
      rw [cjSub, Subgroup.map_le_iff_le_comap]
      refine iSup₂_le fun i hi => ?_
      rw [← Subgroup.map_le_iff_le_comap]
      have e : (X i).map (MulAut.conj h).toMonoidHom = X (⟨h, hh⟩ * i) := by
        show cjSub h (cjSub (i : G) L₀) = cjSub ((⟨h, hh⟩ * i : ↥H) : G) L₀
        rw [burnsideB610_cjSub_cjSub]
        rfl
      rw [e, ← hrep (⟨h, hh⟩ * i)]
      exact le_iSup₂_of_le (f := fun i (_ : i ∈ S) => X i) _ (hcov _) le_rfl
    have hHN : H ≤ Subgroup.normalizer (N : Set G) := by
      intro h hh
      rw [Subgroup.mem_normalizer_iff_map_conj_eq]
      apply le_antisymm (hcj h hh)
      have h1 := cjSub_mono (g := h) (hcj h⁻¹ (H.inv_mem hh))
      rw [cjSub_cjSub_inv] at h1
      exact h1
    rcases hMP.le_kerIn_or_twoResidual_le hNH hHN with hNJ | hKN
    · exfalso
      have hL₀N : L₀ ≤ N := by
        have h1 : X (rep (X 1)) = L₀ := by
          rw [hrep 1]
          ext x
          simp [hX, mem_cjSub]
        rw [← h1]
        exact le_iSup₂_of_le (f := fun i (_ : i ∈ S) => X i) _ (hcov 1) le_rfl
      have hLJ : L ≤ kerIn M H := (le_sup_left.trans hL₀N).trans hNJ
      have hodd := E2.odd_card_autI_kerIn (hV := hV) hMP hred
      have hdvd := Subgroup.card_dvd_of_le (autI_mono hV hLJ)
      have h2 := burnsideB610_two_dvd_card_autI hV hLV D (by omega : 1 ≤ n) hF
      exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr (h2.trans hdvd))
    · exact hKN
  have hFam : burnsideB610_Fam H T V hV F S X Dx := by
    refine ⟨hinj, fun i _ => hXle i, fun i _ => burnsideB610_cent_le_cjSub hHV i.2,
      fun i hi j hj hij => burnsideB610_comm_of_ne hV hHV hL D h4 i.2 j.2 (hne i hi j hj hij),
      fun i hi j hj hij => burnsideB610_triv_of_ne hV hHV hL D h4 i.2 j.2 (hne i hi j hj hij)
        (Dx i) (Dx j), ?_, ?_, ?_, hres, ?_, ?_, ?_⟩
    ·
      intro i _ a ha
      have h1 := burnsideB610_centralizes_of_act_eq_one (Dx i) hV (hXV i) (hperfX i) a ha
      rw [Subgroup.mem_centralizer_iff]
      intro u hu
      exact (h1 u hu).symm
    ·
      intro i _ h hh
      refine ⟨rep (X (⟨h, hh⟩ * i)), hcov _, ?_⟩
      rw [hrep]
      show cjSub h (cjSub (i : G) L₀) = cjSub ((⟨h, hh⟩ * i : ↥H) : G) L₀
      rw [burnsideB610_cjSub_cjSub]
      rfl
    ·
      intro i _ j _
      refine ⟨(j : G) * (i : G)⁻¹, H.mul_mem j.2 (H.inv_mem i.2), ?_⟩
      show cjSub ((j : G) * (i : G)⁻¹) (cjSub (i : G) L₀) = cjSub (j : G) L₀
      rw [burnsideB610_cjSub_cjSub, inv_mul_cancel_right]
    ·
      intro i _
      exact burnsideB610_fixV_img_twoResidual (Dx i) h4 (hXV i) (F6.twoResidual_mono (hXle i))
    ·
      intro i _ P hPX hP2 hPc
      obtain ⟨k, hk, hgen⟩ := burnsideB610_gen (Dx i) h4 hV (hXV i) hPX hP2 hPc
      exact ⟨k, ⟨twoResidual_le _ hk, F6.twoResidual_mono (hXle i) hk⟩, hgen⟩
    ·
      intro i _
      exact burnsideB610_thompsonJ_le_normalizer hred hT hL D h4 i.2
  refine ⟨↥H, S, X, Dx, hFam, rep (X 1), hcov 1, ?_⟩
  rw [hrep 1]
  ext x
  simp [hX, mem_cjSub]

end CFSG.Quasithin.B610T
