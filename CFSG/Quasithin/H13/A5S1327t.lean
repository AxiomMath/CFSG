module

public import CFSG.Quasithin.H13.A5S1327s
public import CFSG.Quasithin.H13.A5S1327r

public section

namespace CFSG.Quasithin.H13.A5

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.A5Model
open CFSG.LieType.BorelTits

namespace Setting

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} (S : Setting G T L V)
include S

theorem L1_le_centralizer_UH (h331 : Stmt3_3_1)
    (h1222 : Stmt12_2_2) (h5172 : Stmt5_1_7_two) (h1332 : Stmt13_3_2) (h512 : Stmt5_1_2)
    (h137 : EmptyFaithfulMultiple.Input137) {H : Subgroup G}
    (hH : IsHStar T (Subgroup.normalizer (L : Set G)) H)
    (hHZ : ¬ H ≤ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G))
    (hsolv : Group.IsSolvable ↥H) (hS3 : ¬ Nonempty (↥(S.HStar H) ≃* Equiv.Perm (Fin 3)))
    (hO2 : pCoreOf 2 (S.H0 H) ≠ ⊥) :
    S.L1 ≤ Subgroup.centralizer (S.UH H : Set G) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h501 := S.hyp501
  have hTH : T ≤ H := hH.1.1
  have hsyl : IsSylowTwoOf T H := isSylowTwoOf_of_le S.h13.sylow hTH
  obtain ⟨hMP, -⟩ := h501.minParabolic_of_isHStar h331 hH
  have hF : CharTwo H := S.charTwo_of_inH hH.1
  obtain ⟨hUO, hUel, hUred⟩ : S.UH H ≤ pCoreOf 2 H ⊓ Subgroup.centralizer (pCoreOf 2 H : Set G) ∧
      IsElemAbelian 2 (S.UH H) ∧ IsTwoReducedIn H (S.UH H) :=
    conjClosure_isTwoReducedIn_of_charTwo hsyl hF le_rfl
  have hSQT : ∀ p : ℕ, p.Prime → p ≠ 2 → CFSG.Open.pRank p H ≤ 2 := by
    obtain ⟨-, hq⟩ := isSQTKSub_of_inH S.h13.qtke S.h13.simple S.h13.nonabelian hH.1
    intro p hp hp2
    have : Fact p.Prime := ⟨hp⟩
    have h1 := hq p hp hp2
    rwa [← pRank_top_subtype]
  have hJT := S.thompsonJ_not_le_centralizer_UH h331 h5172 hH hHZ
  have hH0L := S.H0_le_normalizer_oTwoUpper h331 h1222 h5172 h1332 h137 hH hHZ hsolv hS3 hO2
  have hL1Z := S.L1_le_centralizer_Z h512 h5172 hH hHZ
  have hL1N := S.L1_le_normalizer_UH hTH hH0L hL1Z
  set U := S.UH H with hUdef
  set Z := quasithinOmegaOneCenter T with hZdef
  have hHN : H ≤ Subgroup.normalizer (U : Set G) := hUred.2.1
  have hZU : Z ≤ U := le_conjClosure _ _
  have hLN : twoResidual H ≤ Subgroup.normalizer (U : Set G) := (twoResidual_le H).trans hHN
  obtain ⟨K₁, K₂, B⟩ := exists_twoBlocks hUel hMP hsolv hSQT hUred hJT hS3
  obtain ⟨y₁, hy₁, hy₁3, hy₁1⟩ := S1417.exists_orderThree B.nat₁
  obtain ⟨t, htT, ht⟩ := B.swap
  have hy₂ : t * y₁ * t⁻¹ ∈ K₂ := by
    rw [← ht, B1.mem_conjAut]
    simpa [mul_assoc] using hy₁
  have hy₂3 : (t * y₁ * t⁻¹) ^ 3 = 1 := by rw [conj_pow, hy₁3]; group
  have hy₂1 : t * y₁ * t⁻¹ ≠ 1 := fun h => hy₁1 (by
    have e : y₁ = t⁻¹ * (t * y₁ * t⁻¹) * t := by group
    rw [e, h]; group)
  have hŨ := B.commV_autI_twoResidual hy₁ hy₁3 hy₁1 hy₂ hy₂3 hy₂1
  set C := fixV (autI hUel (twoResidual H)) with hC
  set Ũ := commV K₁ ⊔ commV K₂ with hŨdef
  have hpres : ∀ g : MulAut (IntMod U hUel),
      (∀ φ ∈ autI hUel (twoResidual H), g * φ * g⁻¹ ∈ autI hUel (twoResidual H)) →
      (∀ φ ∈ autI hUel (twoResidual H), g⁻¹ * φ * g⁻¹⁻¹ ∈ autI hUel (twoResidual H)) →
      (∀ w ∈ C, g w ∈ C) ∧ ∀ w ∈ Ũ, g w ∈ Ũ := by
    intro g hg hg'
    refine ⟨fun w hw φ hφ => ?_, fun w hw => ?_⟩
    · have h1 := hw _ (hg' φ hφ)
      have e : φ (g w) = g ((g⁻¹ * φ * g⁻¹⁻¹) w) := by
        simp [MulAut.mul_apply]
      rw [e, h1]
    · rw [← hŨ] at hw ⊢
      have h1 : g w ∈ (commV (autI hUel (twoResidual H))).map g.toMonoidHom := ⟨w, hw, rfl⟩
      rw [commV_map_conjAut] at h1
      refine commV_mono' ?_ h1
      intro x hx
      rw [B1.mem_conjAut] at hx
      have := hg _ hx
      simpa [mul_assoc] using this
  have hnormL : ∀ (g : ↥(Subgroup.normalizer (U : Set G))),
      (g : G) ∈ Subgroup.normalizer (twoResidual H : Set G) →
      ∀ φ ∈ autI hUel (twoResidual H),
        convI hUel g * φ * (convI hUel g)⁻¹ ∈ autI hUel (twoResidual H) := by
    intro g hg φ hφ
    obtain ⟨x, hx, rfl⟩ := (mem_autI hUel).1 hφ
    rw [← map_inv, ← map_mul, ← map_mul]
    exact convI_mem_autI hUel ((Subgroup.mem_normalizer_iff.mp hg x).mp hx) _
  obtain ⟨z₀, hz₀Z, hz₀C⟩ : ∃ z₀, ∃ hz : z₀ ∈ Z, (IntMod.mk hUel ⟨z₀, hZU hz⟩) ∉ C := by
    by_contra hcon
    push Not at hcon
    apply hHZ
    rw [eq_oTwoUpper_sup_of_isSylowTwoOf' hsyl, ← twoResidual_eq_oTwoUpper']
    refine sup_le (fun x hx => ?_) (T_le_centralizer_omegaOneCenter T)
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    have h1 := (mem_fixV_autI hUel hLN (IntMod.mk hUel ⟨z, hZU hz⟩)).1 (hcon z hz)
    exact (Subgroup.mem_centralizer_iff.mp h1 x hx).symm
  set w₀ := IntMod.mk hUel ⟨z₀, hZU hz₀Z⟩ with hw₀
  obtain ⟨c, hc, ũ, hũ, hcũ⟩ := Subgroup.mem_sup.mp (B.fix_sup ▸ Subgroup.mem_top w₀)
  have hũ1 : ũ ≠ 1 := by
    intro h
    rw [h, mul_one] at hcũ
    exact hz₀C (hcũ ▸ hc)
  have hfixũ : ∀ g : MulAut (IntMod U hUel), (∀ w ∈ C, g w ∈ C) → (∀ w ∈ Ũ, g w ∈ Ũ) →
      g w₀ = w₀ → g ũ = ũ := by
    intro g hgC hgŨ hgw
    rw [← hcũ, map_mul] at hgw
    exact (S1417.eq_of_mul_eq_of_inf_eq_bot B.fix_inf (hgC c hc) hc (hgŨ ũ hũ) hũ hgw).2
  obtain ⟨t₀, ht₀T, rfl⟩ := (mem_autI hUel).1 htT
  have hTL : T ≤ Subgroup.normalizer (twoResidual H : Set G) :=
    hTH.trans (le_normalizer_twoResidual H)
  have hte : convI hUel t₀ ũ = ũ := by
    have hpr := hpres (convI hUel t₀) (hnormL t₀ (hTL ht₀T))
      (by rw [← map_inv]; exact hnormL t₀⁻¹ (hTL (T.inv_mem ht₀T)))
    refine hfixũ _ hpr.1 hpr.2 (IntMod.val_injective ?_)
    rw [convI_apply_val]
    show (t₀ : G) * z₀ * (t₀ : G)⁻¹ = z₀
    have := Subgroup.mem_centralizer_iff.mp (mem_quasithinOmegaOneCenter_iff.mp hz₀Z).2.1 t₀ ht₀T
    rw [this]; group
  have hH0 : S.L1 ≤ S.H0 H := by
    rw [S.H0_eq_sup hTH]; exact le_sup_left.trans le_sup_left
  refine (Subgroup.closure_le _).mpr fun l ⟨hlLN, m, hm, hlm⟩ => ?_
  have hl1 : l ∈ S.L1 := Subgroup.subset_closure ⟨hlLN, m, hm, hlm⟩
  have hlN : l ∈ Subgroup.normalizer (U : Set G) := hL1N hl1
  have hlL : l ∈ Subgroup.normalizer (twoResidual H : Set G) := by
    rw [twoResidual_eq_oTwoUpper']; exact hH0L (hH0 hl1)
  set ls := convI hUel ⟨l, hlN⟩ with hls
  have hlsodd : Odd (orderOf ls) := by
    refine Odd.of_dvd_nat hm ((orderOf_map_dvd _ _).trans ?_)
    rw [Subgroup.orderOf_mk]
    exact orderOf_dvd_of_pow_eq_one hlm
  have hgL := hnormL ⟨l, hlN⟩ hlL
  have hpr := hpres ls hgL (by
    rw [hls, ← map_inv]
    exact hnormL _ (Subgroup.inv_mem _ hlL))
  have hlz : ∀ z ∈ Z, l * z * l⁻¹ = z := fun z hz => by
    have := Subgroup.mem_centralizer_iff.mp (hL1Z hl1) z hz
    rw [← this]; group
  have hge : ls ũ = ũ := by
    refine hfixũ _ hpr.1 hpr.2 (IntMod.val_injective ?_)
    rw [hls, convI_apply_val]
    exact hlz z₀ hz₀Z
  have htriv := B.apply_eq_of_odd hy₁ hy₁3 hy₁1 hy₂ hy₂3 hy₂1 ht hlsodd hgL hũ1 hũ hte hge
  show l ∈ Subgroup.centralizer (U : Set G)
  rw [Subgroup.mem_centralizer_iff]
  intro u hu
  have hle : U ≤ Subgroup.centralizer ({l} : Set G) := by
    rw [hUdef, S.UH_eq_conjClosure_oTwoUpper hTH]
    refine conjClosure_le fun x hx z hz => ?_
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hxL : x ∈ twoResidual H := by rw [twoResidual_eq_oTwoUpper']; exact hx
    have hxN : x ∈ Subgroup.normalizer (U : Set G) := hLN hxL
    have hxz : x * z * x⁻¹ ∈ U := (Subgroup.mem_normalizer_iff.mp hxN z).mp (hZU hz)
    set zw := IntMod.mk hUel ⟨z, hZU hz⟩ with hzw
    set d := convI hUel ⟨x, hxN⟩ zw * zw⁻¹ with hd
    have hdŨ : d ∈ Ũ := by
      rw [← hŨ]
      exact Subgroup.subset_closure ⟨_, convI_mem_autI hUel hxL hxN, zw, rfl⟩
    have h1 : ls (convI hUel ⟨x, hxN⟩ zw) = convI hUel ⟨x, hxN⟩ zw := by
      have e : convI hUel ⟨x, hxN⟩ zw = zw * d := by
        rw [hd, mul_comm zw, inv_mul_cancel_right]
      rw [e, map_mul, htriv d hdŨ]
      congr 1
      apply IntMod.val_injective
      rw [hls, convI_apply_val]
      exact hlz z hz
    have h2 := congrArg IntMod.val h1
    rw [hls, convI_apply_val, convI_apply_val] at h2
    have h3 : l * (x * z * x⁻¹) * l⁻¹ = x * z * x⁻¹ := h2
    calc x * z * x⁻¹ * l = (l * (x * z * x⁻¹) * l⁻¹) * l := by rw [h3]
      _ = l * (x * z * x⁻¹) := by group
  exact Subgroup.mem_centralizer_singleton_iff.mp (hle hu)

end Setting

end CFSG.Quasithin.H13.A5
