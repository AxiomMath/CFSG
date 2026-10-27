module

public import CFSG.Quasithin.Vol2.Ch12Sec1Lem1NmB

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique

namespace Sec1211Ns

namespace Setting

variable {G : Type} [Group G] [Finite G] {T L V V₁ V₂ : Subgroup G} {n : ℕ} {a₀ c₀ : G}
  {S : Setting T L V V₁ V₂ n a₀ c₀} {m : ℕ}

variable (S) in
include S in
theorem normalizer_le_of_characteristic (h331 : Stmt3_3_1) {C : Subgroup G}
    (hCQ : C ≤ T ⊓ Subgroup.centralizer (V : Set G)) (hC1 : C ≠ ⊥)
    (hCch : (C.subgroupOf (T ⊓ Subgroup.centralizer (V : Set G))).Characteristic) :
    Subgroup.normalizer (C : Set G) ≤ Subgroup.normalizer (L : Set G) := by
  have huniq := Sec1215.isUniqueM_of_hyp121 h331 S.hyp S.hTL
  have hNQC : Subgroup.normalizer
      ((T ⊓ Subgroup.centralizer (V : Set G) : Subgroup G) : Set G) ≤
      Subgroup.normalizer (C : Set G) := by
    have h1 := CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic
      (C.subgroupOf (T ⊓ Subgroup.centralizer (V : Set G)))
    rwa [Subgroup.map_subgroupOf_eq_of_le hCQ] at h1
  have hC2 : IsPGroup 2 C := (S.hyp.sylow.1.to_le inf_le_left).to_le hCQ
  obtain ⟨M', hM', hNM'⟩ := exists_maxTwoLocal_ge
    (⟨C, hC1, hC2, rfl⟩ : IsTwoLocal (Subgroup.normalizer (C : Set G)))
  have hM'M : M' = Subgroup.normalizer (L : Set G) := huniq.2 M' ⟨hM', hNQC.trans hNM'⟩
  exact hM'M ▸ hNM'

variable (S) in
theorem exists_block_not_le (h331 : Stmt3_3_1)
    (h129 : ∀ (G : Type) [Group G] [Finite G], ASC129Statement G) (F : Frame S m) (hm : 3 ≤ m)
    (hchar : CharTwo (Subgroup.centralizer ({a₀ * c₀} : Set G)))
    (hnorm : Subgroup.centralizer ({a₀ * c₀} : Set G) ≤
      Subgroup.normalizer (Sec1216Lv.lv L (a₀ * c₀) : Set G))
    (hHM : ¬ Subgroup.centralizer ({a₀ * c₀} : Set G) ≤ Subgroup.normalizer (L : Set G)) :
    ∃ R B : Subgroup G, IsSylowTwoOf R (Subgroup.centralizer ({a₀ * c₀} : Set G)) ∧
      R ≤ Subgroup.normalizer (L : Set G) ∧ T ⊓ Subgroup.centralizer (V : Set G) ≤ R ∧
      IsSylowTwoOf (T ⊓ Subgroup.centralizer (V : Set G))
        (centralizerSection (Subgroup.centralizer ({a₀ * c₀} : Set G))
          (Sec1216Lv.lv L (a₀ * c₀)) (pCoreOf 2 (Sec1216Lv.lv L (a₀ * c₀)))) ∧
      IsChi0Block (centralizerSection (Subgroup.centralizer ({a₀ * c₀} : Set G))
          (Sec1216Lv.lv L (a₀ * c₀)) (pCoreOf 2 (Sec1216Lv.lv L (a₀ * c₀)))) B ∧
      IsBorelOfBlock B (B ⊓ (centralizerSection (Subgroup.centralizer ({a₀ * c₀} : Set G))
          (Sec1216Lv.lv L (a₀ * c₀)) (pCoreOf 2 (Sec1216Lv.lv L (a₀ * c₀))) ⊓
          Subgroup.normalizer (L : Set G))) ∧
      ⁅B, thompsonJ (T ⊓ Subgroup.centralizer (V : Set G))⁆ = B ∧
      ¬ B ≤ Subgroup.normalizer (L : Set G) := by
  set H := Subgroup.centralizer ({a₀ * c₀} : Set G) with hH
  set M := Subgroup.normalizer (L : Set G) with hMdef
  set Lv := Sec1216Lv.lv L (a₀ * c₀) with hLv
  set Y := centralizerSection H Lv (pCoreOf 2 Lv) with hY
  set Q := T ⊓ Subgroup.centralizer (V : Set G) with hQ
  obtain ⟨R, hR, hRM, hQR, hRY⟩ := S.exists_sylow_of_normal h331 F hm hnorm
  have hYH : Y ≤ H := centralizerSection_le_left H Lv (pCoreOf 2 Lv)
  have hYn : ∀ h ∈ H, h ∈ Subgroup.normalizer (Y : Set G) := fun h hh =>
    mem_normalizer_centralizerSection hh (hnorm hh)
  have hQY : IsSylowTwoOf Q Y := by
    have h1 := A4.isSylowTwoOf_inf_normal hR hYH hYn
    rwa [hRY] at h1
  have hsq : IsSQTKIn Y :=
    IsSQTKIn.mono (sqtkGroup_of_pCoreOf_ne_bot S.hyp.qtke S.hyp.simple S.hyp.nonabelian
      S.pCoreOf_ne_bot) hYH
  have hcY : CharTwo Y := A4.charTwo_of_normal hYH hYn hchar
  have hcgs : cgsIn Y Q ≤ Y ⊓ M := by
    refine iSup_le fun C => iSup_le fun hCQ => iSup_le fun hC1 => iSup_le fun hCch => ?_
    exact inf_le_inf_left Y (S.normalizer_le_of_characteristic h331 hCQ hC1 hCch)
  obtain ⟨r, Lb, -, hLb, hprod⟩ := h129 G Y Q (Y ⊓ M) hsq hcY hQY hcgs inf_le_left
  have hYM : ¬ Y ≤ M := by
    intro hle
    apply hHM
    intro g hg
    obtain ⟨x, hx, hxg⟩ := S.exists_mul_mem_section F hm hnorm hg
    have e : g = x * (x⁻¹ * g) := by group
    rw [e]
    exact M.mul_mem hx.1 (hle hxg)
  obtain ⟨i, hi⟩ : ∃ i, ¬ Lb i ≤ M := by
    by_contra hall
    push Not at hall
    apply hYM
    intro y hy
    obtain ⟨mm, hmm, x, hx, rfl⟩ := hprod y hy
    refine M.mul_mem hmm.2 (Subgroup.list_prod_mem M fun z hz => ?_)
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hz
    exact hall j (hx j)
  exact ⟨R, Lb i, hR, hRM, hQR, hQY, (hLb i).1, (hLb i).2.1, (hLb i).2.2, hi⟩

end Setting

end Sec1211Ns

end CFSG.Quasithin.H13
