module

public import CFSG.Quasithin.Vol2.Ch12Sec7GzSFin1
public import CFSG.Quasithin.Vol2.Ch12Sec7GzSOrb
public import CFSG.Quasithin.Vol2.Ch12Sec7GzSConjA
public import CFSG.Quasithin.Vol2.Ch12Sec7GzSSplit
public import Certificates.Certificate589103

public section

namespace CFSG.Quasithin.H13.I1277

open CFSG.Open CFSG.Quasithin S127 S127.I77 CFSG.Quasithin.H13.S127.Mod Certificates.Data.S1277Facts
open scoped IsMulCommutative

theorem structOfNotLe1277_holds
    (h71 : Setup1271) (h74 : Lemma12_7_4) (h125 : Lemma12_7_5)
    (h331 : Stmt3_3_1) (h1222 : Stmt12_2_2) (h1226 : Stmt12_2_6) : StructOfNotLe1277 := by
  intro G _ _ T L V h t ht h18 hGt z hzV hz45 hGz
  classical
  obtain ⟨hmf, -, horb⟩ := Certificates.certificate589103
  have hgm := hmf gm6 List.mem_cons_self
  have hnm := hmf nm6 (List.mem_cons_of_mem _ List.mem_cons_self)
  have s : Set77 G T L V t := set77_of h71 h74 h125 h ht h18 hGt
  haveI : IsMulCommutative ↥V := ⟨⟨fun a b => Subtype.ext (s.d.comm a a.2 b b.2)⟩⟩
  have hNLV : Subgroup.normalizer (L : Set G) = Subgroup.normalizer (V : Set G) :=
    mEqNormV1277_of h331 h1222 h1226 G T L V t s
  have hCV : Subgroup.centralizer (V : Set G) = V := s.centralizer_V_eq h1222 h1226 h331
  have hV64 : Nat.card ↥V = 64 := s.d.card_V.trans (by norm_num)
  have hV2 : ∀ x ∈ V, x ^ 2 = 1 := fun x hx => S127.sq_eq_one_of_mem h.hyp hx
  have hH : Subgroup.normalizer (L : Set G) ≤ Subgroup.normalizer (V : Set G) := hNLV.le
  have hLV : L ≤ Subgroup.normalizer (V : Set G) := Subgroup.le_normalizer.trans hH
  have hVL : V ≤ L := s.d.v_le_lt.trans (Set77.lt_le_L (L := L) (t := t))
  have hVel : IsElemAbelian 2 V := ⟨inferInstance, hV2⟩
  have hMV : h.hyp.MVbar = autOn (Subgroup.normalizer (L : Set G)) V := by
    show autOn (Subgroup.normalizer (L : Set G) ⊓ Subgroup.normalizer (V : Set G)) V = _
    rw [inf_eq_left.2 hH]
  obtain ⟨M₀, hM₀M, hM₀inf, hdec⟩ := exists_complement_1277 h71 h331 h1222 h1226 s
  have SP : SplitHyp V (Subgroup.normalizer (L : Set G)) M₀ :=
    ⟨hVL.trans Subgroup.le_normalizer, hH, hM₀M, hM₀inf, hdec, hCV⟩
  obtain ⟨z₁, hz₁V, hz₁1, hTz₁, h45₁⟩ := L1_of h1222 G T L V h
  obtain ⟨C₀, hC₀⟩ : ∃ C : Coding ↥V, IdentL C (autOn L V) := exists_identL_G h1222 h
  obtain ⟨C, hC, hcd⟩ := exists_coding_five hLV hC₀ horb hz₁V h45₁
  have hz₁2 : z₁ * z₁ = 1 := by rw [← pow_two]; exact hV2 z₁ hz₁V
  have hz₁H : z₁ ∈ Gz z₁ := Subgroup.mem_centralizer_singleton_iff.2 rfl
  have hz₁Q : z₁ ∈ pCoreOf 2 (Gz z₁) :=
    mem_pcore_of_central hz₁H (fun x hx => Subgroup.mem_centralizer_singleton_iff.1 hx) hz₁2
  have hQne : pCoreOf 2 (Gz z₁) ≠ ⊥ := fun hb => hz₁1 (by
    have := hz₁Q
    rw [hb, Subgroup.mem_bot] at this
    exact this)
  have hchar : Gz z₁ ⊓ Subgroup.centralizer ((pCoreOf 2 (Gz z₁) : Subgroup G) : Set G) ≤
      pCoreOf 2 (Gz z₁) := charTwo_of_inH' h.hyp.qtke h.hyp.sylow ⟨hTz₁, hQne⟩
  obtain ⟨l, hlL, hlz⟩ := exists_conj_of_45 hLV hC horb hzV hz₁V hz45 h45₁
  have hne₁ : ¬ Gz z₁ ≤ Subgroup.normalizer (L : Set G) := by
    intro hle
    apply hGz
    intro x hx
    have hxc : x * z = z * x := Subgroup.mem_centralizer_singleton_iff.1 hx
    have hmem : l * x * l⁻¹ ∈ Gz z₁ := by
      rw [Subgroup.mem_centralizer_singleton_iff, ← hlz]
      calc l * x * l⁻¹ * (l * z * l⁻¹) = l * (x * z) * l⁻¹ := by group
        _ = l * (z * x) * l⁻¹ := by rw [hxc]
        _ = l * z * l⁻¹ * (l * x * l⁻¹) := by group
    have hl' : l ∈ Subgroup.normalizer (L : Set G) := Subgroup.le_normalizer hlL
    have h1 := hle hmem
    have e : x = l⁻¹ * (l * x * l⁻¹) * l := by group
    rw [e]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hl') h1) hl'
  have key : ∀ Γ : List B6, (∀ a ∈ autOn (Subgroup.normalizer (L : Set G)) V, C.cB a ∈ Γ) →
      (∀ B ∈ Γ, ∃ a ∈ autOn (Subgroup.normalizer (L : Set G)) V, C.cB a = B) →
      ModelFacts1277 Γ → StructAt G z₁ := fun Γ hΓ1 hΓ2 hs =>
    structAt_T_fixed SP C hΓ1 hΓ2 hz₁V hcd hs hVel hV64 h.hyp.normalizes hTz₁ h.hyp.sylow.1
      h.hyp.sylow.2 hne₁ hNLV.symm.le hz₁2 hchar
  have hStruct₁ : StructAt G z₁ := by
    by_cases hM : h.hyp.MVbar = autOn L V
    · have hAut : autOn (Subgroup.normalizer (L : Set G)) V = autOn L V := hMV.symm.trans hM
      refine key gm6 (fun a ha => ?_) (fun B hB => ?_) hgm
      · rw [hAut] at ha
        exact (hC.1 a).1 ha
      · obtain ⟨a, ha⟩ := hC.2 B hB
        exact ⟨a, by rw [hAut]; exact (hC.1 a).2 (by rw [ha]; exact hB), ha⟩
    · refine key nm6 (fun a ha => ?_) (fun B hB => ?_) hnm
      · rw [← hMV] at ha
        exact (MVbar_code h hC ha).1
      · obtain ⟨a, ha, hBa⟩ := MVbar_surj h hC hM B hB
        exact ⟨a, by rw [← hMV]; exact ha, hBa⟩
  have hconj := structAt_conj l⁻¹ z₁ hStruct₁
  have e : l⁻¹ * z₁ * l⁻¹⁻¹ = z := by rw [← hlz]; group
  rwa [e] at hconj

end CFSG.Quasithin.H13.I1277

end
