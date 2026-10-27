module

public import CFSG.Quasithin.EmptyFaithful.LRed10Core
public import CFSG.Quasithin.EmptyFaithful.LRed10Ext
public import CFSG.Quasithin.EmptyFaithful.LRed10Frat
public import CFSG.Quasithin.Background.E2TwoNoNStmt

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits B2F E2 CFSG.Quasithin.Ch3n317A5

namespace LRed10

@[expose] def FratNonsolvable : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (H T M : Subgroup G), MinParabolic H T M → SQTKGroup ↥H →
    ¬ Group.IsSolvable ↥H → ∀ {Y : Subgroup G}, Y ≤ H → twoResidual H ≤ Y ⊔ kerIn M H →
      twoResidual H ≤ Y ⊔ pCoreOf 2 H

theorem twoResidual_le_sup_pCoreOf_of_e22_noN (he22 : E2.E22StatementNoN) {G : Type} [Group G]
    [Finite G] {H T M : Subgroup G} (h : MinParabolic H T M) (hsq : SQTKGroup ↥H)
    (hns : ¬ Group.IsSolvable ↥H) {Y : Subgroup G} (hYH : Y ≤ H)
    (hY : twoResidual H ≤ Y ⊔ kerIn M H) : twoResidual H ≤ Y ⊔ pCoreOf 2 H := by
  obtain ⟨⟨C, -, hHC, hqs, hcases⟩, -⟩ := he22 G H T M h hsq hns
  rcases hcases with ⟨hJQ, -⟩ | ⟨hTC, hJ, -⟩
  · rw [hJQ] at hY
    exact hY
  · exact twoResidual_le_sup_pCoreOf_of_case_two h hHC hqs.1 hTC hJ hYH hY

theorem fratNonsolvable_of_e22_noN (he22 : E2.E22StatementNoN) : FratNonsolvable :=
  fun _ _ _ _ _ _ h hsq hns _ hYH hY => twoResidual_le_sup_pCoreOf_of_e22_noN he22 h hsq hns hYH hY

theorem ker317A5_of_e23_frat (he23 : E2.E23Nonsolvable) (hF : FratNonsolvable) : Ker317A5 := by
  intro G _ _ H T M₂ V hmin hsq hchar hV hJ hns hS
  classical
  have hpg : ∀ X : Subgroup (IntMod V hV.2.2.1), IsPGroup 2 ↥X := fun X x =>
    ⟨1, Subtype.ext (by simpa using IntMod.sq_eq_one x.1)⟩
  have hVe : IsElemAbelian 2 V := hV.2.2.1
  have hHN : H ≤ Subgroup.normalizer (V : Set G) := hV.2.1
  have hT := hmin.isSylow
  have hTH : T ≤ H := hT.1
  have hKH : twoResidual H ≤ H := twoResidual_le H
  have hVT : V ≤ T := (MinParabolic.le_pCoreOf_of_isTwoReduced hV).trans
    (B6.pCoreOf_two_le_of_isSylowTwoOf hT)
  have hTN : T ≤ Subgroup.normalizer (V : Set G) := hTH.trans hHN
  have hKN : twoResidual H ≤ Subgroup.normalizer (V : Set G) := hKH.trans hHN
  have hJTH : thompsonJ T ≤ H := (thompsonJ_le_self T).trans hTH
  have hJTN : thompsonJ T ≤ Subgroup.normalizer (V : Set G) := hJTH.trans hHN
  obtain ⟨hKJ, I, hIcard, hJI, hcomm, hind, hconj, htype, hsup, hinf, h2, h3⟩ :=
    he23 G H T M₂ V hVe hmin hsq hchar hV hJ hns
  have hA5 : ∀ L ∈ I, E2.IsA5Module L := by
    by_contra hall
    push Not at hall
    obtain ⟨L₀, hL₀, hL₀a⟩ := hall
    have hL2 : ∀ L ∈ I, ∃ n : ℕ,
        E2.IsL2Natural L (fixV (autI hVe (twoResidual H))) n := by
      intro L hL
      rcases htype L hL with h | h
      · exact h
      · exfalso
        obtain ⟨t, -, ht⟩ := hconj L hL L₀ hL₀
        rcases htype L₀ hL₀ with ⟨n, hn⟩ | h0
        · have h1 := card_of_isL2Natural hn
          rw [← ht, card_conjAut, card_of_isA5Module h] at h1
          exact two_pow_mul_ne_120 n h1.symm
        · exact hL₀a h0
    exact hS (h2 hL2).2.2.1
  obtain ⟨hSJ, hJdec, hL4⟩ := h3 hA5
  have hLH : ∀ L ∈ I, L ≤ autI hVe H := fun L hL =>
    (le_iSup₂_of_le (f := fun L' (_ : L' ∈ I) => L') L hL le_rfl).trans
      (hJI.symm.le.trans (autI_mono hVe (thompsonJ_le_self H)))
  have hK : ∀ L ∈ I, ∀ x ∈ L, Odd (orderOf x) → x ∈ autI hVe (twoResidual H) :=
    fun L hL x hx hodd => E2.mem_autI_twoResidual_of_odd (hLH L hL hx) hodd
  have hkinv : ∀ φ ∈ autI hVe (thompsonJ T), ∀ w ∈ fixV (autI hVe (twoResidual H)),
      φ w ∈ fixV (autI hVe (twoResidual H)) := by
    intro φ hφ w hw κ hκ
    obtain ⟨j, hjJ, rfl⟩ := (mem_autI hVe).1 hφ
    obtain ⟨k, hkK, rfl⟩ := (mem_autI hVe).1 hκ
    have hjH : (j : G) ∈ H := hJTH hjJ
    have hjk : (j : G)⁻¹ * k * j ∈ twoResidual H := by
      have := (Subgroup.mem_normalizer_iff.mp (le_normalizer_twoResidual H (H.inv_mem hjH)) (k : G)).mp
        hkK
      simpa [mul_assoc] using this
    have hjkN : (j : G)⁻¹ * k * j ∈ Subgroup.normalizer (V : Set G) := hKN hjk
    have hκ' : convI hVe ⟨(j : G)⁻¹ * k * j, hjkN⟩ ∈ autI hVe (twoResidual H) :=
      convI_mem_autI hVe hjk hjkN
    have e : convI hVe k * convI hVe j = convI hVe j * convI hVe ⟨(j : G)⁻¹ * k * j, hjkN⟩ := by
      rw [← map_mul, ← map_mul]
      congr 1
      apply Subtype.ext
      simp [mul_assoc]
    have := hw _ hκ'
    calc (convI hVe k) ((convI hVe j) w) = (convI hVe k * convI hVe j) w := rfl
      _ = (convI hVe j * convI hVe ⟨(j : G)⁻¹ * k * j, hjkN⟩) w := by rw [e]
      _ = (convI hVe j) w := by
        rw [MulAut.mul_apply, this]
  obtain ⟨L₁, L₂, P₁, P₂, hP, hJst, hLsup, gs, hgsK, hgs⟩ :=
    a5_bundle (Kst := autI hVe (twoResidual H)) (Jst := autI hVe (thompsonJ T))
      (Tst := autI hVe T) hIcard hcomm hind hsup hinf hA5 hJdec hL4 hK hkinv
  have hEq : ∀ A : Subgroup G, IsMaxElemAbelian T A → ¬ A ≤ Subgroup.centralizer (V : Set G) →
      Nat.card (IntMod V hVe) = Nat.card (autI hVe A) * Nat.card (fixV (autI hVe A)) := by
    intro A hA hAC
    have hAJ : A ≤ thompsonJ T :=
      le_iSup₂_of_le (f := fun (A : Subgroup G) (_ : IsMaxElemAbelian T A) => A) A hA le_rfl
    have hBle : autI hVe A ≤ P₁ ⊔ P₂ := hJst ▸ autI_mono hVe hAJ
    have hO1 := hP.rk_B_le hBle
    have hAs : IsFFStarOffender (autI hVe T) (autI hVe A) :=
      offenderImages_isFFStarOffender hVe hVT hTN ⟨A, ⟨hA, hAC⟩, rfl⟩
    have hnot : ¬ IsStrongFFOffender hVe T A := by
      intro hs
      have hr : (0 : ℚ) < (rk (autI hVe A) : ℚ) := by exact_mod_cast hAs.isA2.rk_pos
      have h1 := hs.2.2
      unfold rAV at h1
      rw [div_lt_one hr] at h1
      have h1' : rkIdx (fixV (autI hVe A)) < rk (autI hVe A) := by exact_mod_cast h1
      have hle : rk ↥(fixV (autI hVe A) ⊓ fixV (autI hVe (twoResidual H))) ≤
          rk ↥(fixV (autI hVe (twoResidual H))) := rk_mono inf_le_right
      omega
    exact B2_8_card_eq hVe hVT hTN ⟨hA, hAC⟩ hnot
  have hCard : CardEq V T := by
    intro A hA hAC
    have h := hEq A hA hAC
    have hAN : A ≤ Subgroup.normalizer (V : Set G) := hA.1.trans hTN
    have h1 : Nat.card (IntMod V hVe) = Nat.card V := rfl
    rw [h1, card_autI_eq hVe hAN, card_fixV_autI hVe hAN] at h
    exact h
  have hfixA : ∀ A : Subgroup G, IsMaxElemAbelian T A →
      fixV (autI hVe (twoResidual H)) ≤ fixV (autI hVe A) := by
    intro A hA
    by_cases hAC : A ≤ Subgroup.centralizer (V : Set G)
    · rw [autI_eq_bot_of_le_centralizer hVe hAC, fixV_bot']
      exact le_top
    · have h := hEq A hA hAC
      have hAJ : A ≤ thompsonJ T :=
        le_iSup₂_of_le (f := fun (A : Subgroup G) (_ : IsMaxElemAbelian T A) => A) A hA le_rfl
      have hBle : autI hVe A ≤ P₁ ⊔ P₂ := hJst ▸ autI_mono hVe hAJ
      have hO1 := hP.rk_B_le hBle
      have hrkW : rk (IntMod V hVe) = rk (autI hVe A) + rk (fixV (autI hVe A)) := by
        unfold rk
        rw [h, padicValNat.mul Nat.card_pos.ne' Nat.card_pos.ne']
      have hidx := rk_add_rkIdx (fixV (autI hVe A))
      have hle : rk ↥(fixV (autI hVe A) ⊓ fixV (autI hVe (twoResidual H))) ≤
          rk ↥(fixV (autI hVe (twoResidual H))) := rk_mono inf_le_right
      have heq : fixV (autI hVe A) ⊓ fixV (autI hVe (twoResidual H)) =
          fixV (autI hVe (twoResidual H)) :=
        eq_of_le_of_rk_le_of_isPGroup (hpg _)
          inf_le_right (by omega)
      exact heq ▸ inf_le_left
  have hfix : fixV (autI hVe (twoResidual H)) ≤ fixV (autI hVe (thompsonJ T)) := by
    intro v hv φ hφ
    have hφ' : φ ∈ ⨆ (A : Subgroup G) (_ : IsMaxElemAbelian T A), autI hVe A := by
      have hφ2 : φ ∈ autI hVe (⨆ (A : Subgroup G) (_ : IsMaxElemAbelian T A), A) := hφ
      rwa [autI_iSup₂ hVe (P := IsMaxElemAbelian T) (fun A hA => hA.1.trans hTN)] at hφ2
    have hle : (⨆ (A : Subgroup G) (_ : IsMaxElemAbelian T A), autI hVe A) ≤
        MulAction.stabilizer (MulAut (IntMod V hVe)) v :=
      iSup₂_le fun A hA φ hφ => MulAction.mem_stabilizer_iff.2 (hfixA A hA hv φ hφ)
    exact MulAction.mem_stabilizer_iff.1 (hle hφ')
  have hrank : 2 * rkIdx (fixV (autI hVe (thompsonJ T))) ≤
      rkIdx (fixV (autI hVe (twoResidual H))) := by
    rw [hJst]
    exact hP.two_mul_rkIdx_le (hJst ▸ hfix)
  obtain ⟨g, hgK, rfl⟩ := (mem_autI hVe).1 hgsK
  have hgN : (g : G) ∈ Subgroup.normalizer (V : Set G) := g.2
  set I₀ := thompsonJ T ⊔ cjSub (g : G) (thompsonJ T) with hI₀
  have hI₀H : I₀ ≤ H := by
    refine sup_le hJTH fun z hz => ?_
    rw [mem_cjSub] at hz
    have := H.mul_mem (H.mul_mem (hKH hgK) (hJTH hz)) (H.inv_mem (hKH hgK))
    simpa [mul_assoc] using this
  have hKI : autI hVe (twoResidual H) ≤ autI hVe I₀ := by
    rw [hI₀, autI_sup hVe hJTN (fun z hz => hHN (hI₀H (Subgroup.mem_sup_right hz))),
      ← autI_cjSub hVe hgN]
    calc autI hVe (twoResidual H) ≤ autI hVe (thompsonJ H) := autI_mono hVe hKJ
      _ = ⨆ L ∈ I, L := hJI
      _ = L₁ ⊔ L₂ := hLsup
      _ ≤ _ := hgs
  have hKIJ : twoResidual H ≤ I₀ ⊔ kerIn M₂ H := by
    intro k hk
    have hkN : k ∈ Subgroup.normalizer (V : Set G) := hHN (hKH hk)
    obtain ⟨i, hiI, hik⟩ := (mem_autI hVe).1 (hKI (convI_mem_autI hVe hk hkN))
    have hc : (i : G)⁻¹ * k ∈ Subgroup.centralizer (V : Set G) := by
      have := (convI_eq_one_iff hVe (i⁻¹ * ⟨k, hkN⟩)).1 (by rw [map_mul, map_inv, hik,
        inv_mul_cancel])
      simpa using this
    have hiH : (i : G) ∈ H := hI₀H hiI
    have hcJ : (i : G)⁻¹ * k ∈ kerIn M₂ H :=
      hmin.inf_centralizer_le_kerIn hV (not_le_centralizer hmin hJ)
        ⟨H.mul_mem (H.inv_mem hiH) (hKH hk), hc⟩
    have : k = (i : G) * ((i : G)⁻¹ * k) := by group
    rw [this]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hiI) (Subgroup.mem_sup_right hcJ)
  have hKIQ := hF G H T M₂ hmin hsq hns hI₀H hKIJ
  have hI₀N : I₀ ≤ Subgroup.normalizer (pCoreOf 2 H : Set G) :=
    hI₀H.trans (le_normalizer_pCoreOf 2 H)
  have hcl : conjClosure (thompsonJ T) H ≤ I₀ := by
    refine conjClosure_le fun y hy z hz => ?_
    have hH : H = twoResidual H ⊔ T := by rw [sup_comm]; exact (sup_twoResidual_eq hT).symm
    have hTK : T ≤ Subgroup.normalizer (twoResidual H : Set G) :=
      hT.1.trans (le_normalizer_twoResidual H)
    have hy' : y ∈ ((twoResidual H ⊔ T : Subgroup G) : Set G) := by rw [← hH]; exact hy
    rw [Subgroup.coe_mul_of_right_le_normalizer_left _ _ hTK] at hy'
    obtain ⟨k, hk, t, ht, rfl⟩ := hy'
    have hk' : k ∈ ((I₀ ⊔ pCoreOf 2 H : Subgroup G) : Set G) := hKIQ hk
    rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ hI₀N] at hk'
    obtain ⟨i, hi, q, hq, rfl⟩ := hk'
    have hqT : q ∈ T := B6.pCoreOf_two_le_of_isSylowTwoOf hT hq
    have hJTN' : T ≤ Subgroup.normalizer (thompsonJ T : Set G) :=
      Subgroup.le_normalizer.trans (normalizer_le_normalizer_thompsonJ T)
    have hz' : (q * t) * z * (q * t)⁻¹ ∈ thompsonJ T :=
      (Subgroup.mem_normalizer_iff.mp (hJTN' (T.mul_mem hqT ht)) z).mp hz
    have e : i * q * t * z * (i * q * t)⁻¹ = i * ((q * t) * z * (q * t)⁻¹) * i⁻¹ := by group
    rw [e]
    exact I₀.mul_mem (I₀.mul_mem hi (Subgroup.mem_sup_left hz')) (I₀.inv_mem hi)
  have hclJ : ¬ conjClosure (thompsonJ T) H ≤ kerIn M₂ H := by
    intro hle
    apply hJ
    have h1 : thompsonJ T ≤ pCoreOf 2 H :=
      hmin.le_pCoreOf_of_isPGroup_of_le_kerIn (hT.2.1.to_le (thompsonJ_le_self T))
        ((le_conjClosure _ _).trans hle)
    exact h1.trans (MinParabolic.pCoreOf_le_centralizer hV)
  have hclH : conjClosure (thompsonJ T) H ≤ H :=
    conjClosure_le fun y hy z hz => H.mul_mem (H.mul_mem hy (hJTH hz)) (H.inv_mem hy)
  have hKcl := (hmin.le_kerIn_or_twoResidual_le hclH (le_normalizer_conjClosure _ _)).resolve_left
    hclJ
  exact pCoreOf_twoResidual_le_baum hVe hmin hV hJ hCard ⟨g, hgK, hgN, hKcl.trans hcl⟩ hrank

theorem ker317A5_of_e23_noN (he23 : E2.E23Nonsolvable) (he22 : E2.E22StatementNoN) : Ker317A5 :=
  ker317A5_of_e23_frat he23 (fratNonsolvable_of_e22_noN he22)

theorem as317SylowNonsolvable_of_e23_noN (he23 : E2.E23Nonsolvable) (he22 : E2.E22StatementNoN) :
    AS317SylowNonsolvable :=
  as317SylowNonsolvable_of_e23 he23 (ker317A5_of_e23_noN he23 he22)

end LRed10

end CFSG.Quasithin
