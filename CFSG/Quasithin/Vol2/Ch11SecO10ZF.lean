module

public import CFSG.Quasithin.Vol2.Ch11SecO10ZB
public import CFSG.Quasithin.Vol2.Ch11SecO10ZE
public import CFSG.Quasithin.Background.F1Models
public import CFSG.Quasithin.Vol2.Ch11SecO10Q
public import CFSG.Quasithin.Vol2.Ch11SecO10Z
public import CFSG.Quasithin.Vol2.Ch11SecO10ZA
public import CFSG.Quasithin.Vol2.Ch11SecO10ZC
public import CFSG.Quasithin.Vol2.Ch11SecO10ZD

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.Vol2.Ch11.O10

open Equiv Equiv.Perm Subgroup CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.Quasithin.H13
  CFSG.Quasithin.SteinbergCB CFSG.Quasithin.H13.A7 SecE
open scoped IsMulCommutative

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G} {n : ℕ} {V₁ : Subgroup G} {z : G}

theorem false_of_natural (hF : Facts42) (hS : Facts42S3) (hF43 : Facts43) (h701 : Stmt7_0_1)
    (hN : SecA.NatFacts) (hF15 : SecA.Facts15) (hB42 : AsB42) (h8 : Ch10.TmpL6_3_2_2_eight)
    (h1102 : Stmt11_0_2) (h1110 : Stmt11_1_0) (h1111 : Stmt11_1_1) (h1141 : Stmt11_4_1)
    (hc : Conf11_4_2 T L I n V₁ z) (hn2 : n = 2) {I' : Subgroup G}
    (hfsu : FSU G T (kz L V₁ z) I')
    (hJ : ¬ thompsonJ (ROf T L V₁) ≤ pCoreOf 2 (kz L V₁ z ⊔ T))
    (hA7 : IsAlt 7 (↥(kz L V₁ z) ⧸ CFSG.pCore 2 ↥(kz L V₁ z)) ∨
      IsHat (↥(kz L V₁ z) ⧸ CFSG.pCore 2 ↥(kz L V₁ z)) ↥(alternatingGroup (Fin 7)))
    [IsMulCommutative ↥(fsuV T I')]
    (hnat : AlternatingNatural (V := ↥(fsuV T I')) (autOn (kz L V₁ z) (fsuV T I')) ⊤ ⊥ 7) :
    False := by
  classical
  have h := hc.hyp
  obtain ⟨-, -, hTs, hTK, hLK⟩ := kz_setting hF hS hF43 h1102 h1110 h1111 h1141 hc
  obtain ⟨hKV, hTV, -, -⟩ := fsuV_spec h701 hfsu hTK
  have hVe := isElemAbelian_fsuV_of_fsu hfsu
  have hVR := fsuV_le_rOf_kz hF hS hF43 h701 h1102 h1110 h1111 h1141 hc hfsu
  have hVT := fsuV_le_T_of_fsu hfsu hTs
  obtain ⟨X₀, hX₀⟩ := SecD.exists_isCartanX h
  have hcV := (h1141 G T L I n V₁ X₀ h hc.vi hX₀).1.1
  obtain ⟨ψ₀, hKact₀, hKonto₀⟩ := exists_coord_bot hKV hnat
  obtain ⟨ψ, hKact, hKonto, hTP⟩ :=
    exists_aligned_sup h.fsu.sylow hKV hTV hTK hKact₀ hKonto₀
  have hKN : kz L V₁ z ≤ kz L V₁ z ⊔ T := le_sup_left
  have hTN : T ≤ kz L V₁ z ⊔ T := le_sup_right
  have hNV : kz L V₁ z ⊔ T ≤ Subgroup.normalizer (fsuV T I' : Set G) := sup_le hKV hTV
  have hNK : kz L V₁ z ⊔ T ≤ Subgroup.normalizer (kz L V₁ z : Set G) :=
    sup_le Subgroup.le_normalizer hTK
  have hNact : ∀ m ∈ kz L V₁ z ⊔ T, ∃ σ, IsCoordAct ψ m σ := fun m hm =>
    exists_coordAct hKV hKact hKonto (hNV hm) (hNK hm)
  set ρ := coordRep ψ hNV hNact with hρ
  have hρeq : ∀ (m : ↥(kz L V₁ z ⊔ T)) {σ : Perm (Fin 7)}, IsCoordAct ψ m σ → ρ m = σ :=
    fun m σ hσ => IsCoordAct.unique ψ (hNV m.2) (coordRep_spec ψ hNV hNact m) hσ
  have hKA : ∀ k (hk : k ∈ kz L V₁ z), ρ ⟨k, hKN hk⟩ ∈ alternatingGroup (Fin 7) := by
    intro k hk
    obtain ⟨σ, hσ, hact⟩ := hKact k hk
    rw [hρeq _ hact]
    exact hσ
  have hfK : (ρ.comp (Subgroup.inclusion hKN)).range = alternatingGroup (Fin 7) := by
    apply le_antisymm
    · rintro _ ⟨k, rfl⟩
      exact hKA k k.2
    · intro σ hσ
      obtain ⟨k, hk, hact⟩ := hKonto σ hσ
      exact ⟨⟨k, hk⟩, hρeq _ hact⟩
  obtain ⟨K₀, _, _, hK₀, ⟨e₁⟩⟩ := SecA.lOf_quot_SL2 hN h1102 h (Or.inl rfl) hc.vi
  rw [hn2] at hK₀
  obtain ⟨y, hyL, hy5, hy1⟩ := exists_five_lOf hLK _ hfK hA7 hK₀ e₁
  have hyV : y ∉ Subgroup.centralizer (fsuV T I' : Set G) := fun hyc =>
    hy1 ((coordRep_eq_one_iff ψ hNV hNact _).2 hyc)
  obtain ⟨A₀, hA₀, hA₀O⟩ : ∃ A, IsMaxElemAbelian (ROf T L V₁) A ∧
      ¬ A ≤ pCoreOf 2 (kz L V₁ z ⊔ T) := by
    by_contra hcon
    refine hJ ?_
    unfold thompsonJ
    exact iSup₂_le fun A hA => by_contra fun h' => hcon ⟨A, hA, h'⟩
  have hRT : ROf T L V₁ ≤ T := SecD.ROf_le_T h V₁
  have hA₀T : A₀ ≤ T := hA₀.1.trans hRT
  have hCV : T ⊓ Subgroup.centralizer (fsuV T I' : Set G) ≤ pCoreOf 2 (kz L V₁ z ⊔ T) :=
    inf_centralizer_fsuV_le_kz hF hS hF43 h701 h1102 h1110 h1111 h1141 hc hfsu
  have hA₀V : ¬ A₀ ≤ Subgroup.centralizer (fsuV T I' : Set G) := fun hle =>
    hA₀O fun a ha => hCV ⟨hA₀T ha, hle ha⟩
  obtain ⟨-, a₀, ha₀, τ, hτ, hτTP⟩ := offender_coord hNV hNact hVe hVR hA₀ (hA₀T.trans hTN)
    (fun a ha => hTP a (hA₀T ha)) hA₀V
  have hOR : pCoreOf 2 (kz L V₁ z ⊔ T) ≤ ROf T L V₁ :=
    SecD.le_ROf' (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _)
      ((B6.pCoreOf_two_le_of_isSylowTwoOf hTs).trans le_sup_right)
      ((sup_le_sup_right hLK T).trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _))
  obtain ⟨B, hB, hBV⟩ : ∃ B, IsMaxElemAbelian T B ∧
      ¬ B ≤ Subgroup.centralizer (fsuV T I' : Set G) := by
    by_contra hcon
    obtain ⟨B₀, hB₀⟩ := exists_isMaxElemAbelian T
    have hB₀V : B₀ ≤ Subgroup.centralizer (fsuV T I' : Set G) :=
      by_contra fun h' => hcon ⟨B₀, hB₀, h'⟩
    have hB₀R : B₀ ≤ ROf T L V₁ := fun b hb => hOR (hCV ⟨hB₀.1 hb, hB₀V hb⟩)
    have hA₀max : IsMaxElemAbelian T A₀ := ⟨hA₀T, hA₀.2.1, fun C hC hCe =>
      (hB₀.2.2 C hC hCe).trans (hA₀.2.2 B₀ hB₀R hB₀.2.1)⟩
    exact hcon ⟨A₀, hA₀max, hA₀V⟩
  obtain ⟨hBT3, b₀, hb₀, τB, hτB, hτBTP⟩ := offender_coord hNV hNact hVe hVT hB
    (hB.1.trans hTN) (fun b hb => hTP b (hB.1 hb)) hBV
  obtain ⟨A, hA, a, ha, τ'', hτ'', hτ''TP, hne⟩ : ∃ A, IsMaxElemAbelian T A ∧ ∃ a ∈ A,
      ∃ τ'', IsCoordAct ψ a τ'' ∧ IsTP τ'' ∧ τ'' ≠ τ := by
    by_cases hττ : τB = τ
    · subst hττ
      obtain ⟨κ, hκA, hκT3, hκ⟩ := exists_kappa hτBTP
      obtain ⟨k, hk, hkκ⟩ := hKonto κ hκA
      obtain ⟨A, hA, a, ha, σ, hσ, hact⟩ := exists_conj_offender h.fsu.sylow hNV hNact hTN hTP
        hB hBT3 hb₀ hτB (hKN hk) hkκ hκT3
      exact ⟨A, hA, a, ha, _, hact, (hκ σ hσ).1, (hκ σ hσ).2⟩
    · exact ⟨B, hB, b₀, hb₀, τB, hτB, hτBTP, hττ⟩
  obtain ⟨p, q, c, d, rfl, rfl, hpq, hcp, hdp, hcd⟩ := exists_disjoint_swaps hτTP hτ''TP hne
  have hR₁N : ROf T L V₁ ≤ kz L V₁ z ⊔ T := hRT.trans hTN
  have ha₀N : a₀ ∈ kz L V₁ z ⊔ T := hR₁N (hA₀.1 ha₀)
  have hX := map_lOf_eq_fix2 hNV hNact hKN hKA hLK (perfectCore_perfect _) hK₀ e₁ hyL hy5 hyV
    hpq ha₀N (hρeq _ hτ) fun l hl => comm_mem_pCoreOf_lOf h hc.vi (hA₀.1 ha₀) hl
  have hC1 := pCoreOf_le_centralizer_coord hNV hNact hKN hKA hLK hyL hy5 hyV
  have hRX : ∀ r ∈ ((ROf T L V₁).subgroupOf (kz L V₁ z ⊔ T)).map ρ, ∀ x ∈ fix2 p q,
      r * x = x * r := by
    rintro _ ⟨r, hr, rfl⟩ x hx
    rw [← hX] at hx
    obtain ⟨l, hl, rfl⟩ := hx
    exact coordRep_comm hNV hNact r.2 l.2
      (hC1 (comm_mem_pCoreOf_lOf h hc.vi (mem_subgroupOf.1 hr) (mem_subgroupOf.1 hl)))
  have haLR := le_lOf_sup_rOf hB42 h1102 h8 hF15 h hcV hc.vi hA ha
  have hmem : ρ ⟨a, hTN (hA.1 ha)⟩ ∈
      fix2 p q ⊔ ((ROf T L V₁).subgroupOf (kz L V₁ z ⊔ T)).map ρ := by
    rw [← hX, ← Subgroup.map_sup, ← Subgroup.subgroupOf_sup (hLK.trans hKN) hR₁N]
    exact ⟨⟨a, hTN (hA.1 ha)⟩, mem_subgroupOf.2 haLR, rfl⟩
  rw [hρeq _ hτ''] at hmem
  exact swap_not_mem_sup hpq hcp hdp hcd hRX hmem

end CFSG.Quasithin.Vol2.Ch11.O10
