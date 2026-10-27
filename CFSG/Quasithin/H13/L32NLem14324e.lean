module

public import CFSG.Quasithin.Background.SzG11SConcl
public import CFSG.Quasithin.Background.G10Basic
public import CFSG.Quasithin.H13.L32NLem14312a
public import CFSG.Quasithin.H13.L32NLem14332e

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique

namespace L14324

variable {G : Type} [Group G] [Finite G]

theorem fixS_of (h1222 : Stmt12_2_2) (h12213 : Stmt12_2_13) (hFixS : G11.SzG11S.TheoremG112FixS)
    {T L V : Subgroup G} {n : ℕ} {V₁ V₂ : Subgroup G} (hs : Setting1282One G T L V n V₁ V₂)
    {g : G} (hg : g ∈ p128 T L V) (hgN : g ∉ Subgroup.normalizer (V₁ : Set G)) {a : G}
    (ha : a ∈ V₂) (haV₁ : a ∉ V₁) (D : HatModelU (u128 V V₁)) :
    G111Hyp D.B (D.img (Subgroup.normalizer (V₁ : Set G))) (D.π a)
        (D.hat (w128 V V₁ V₂ ⊓ CFSG.conjugate (w128 V V₁ V₂) g))
        (D.img (CFSG.conjugate (w128 V V₁ V₂) g)) (D.img (CFSG.conjugate (zU128 V V₁) g)) ∧
      G11.SzG11S.G112ConclusionFixS D.B (D.img (Subgroup.normalizer (V₁ : Set G)))
        (D.img (CFSG.conjugate (w128 V V₁ V₂) g)) := by
  have S := L128P.setting128A h1222 h12213 hs
  obtain ⟨k, hk, hkN, hkY⟩ := L128P.exists_conjugate_eq hs.hyp hs.v1 hg hgN
  obtain ⟨hTW, hTZ⟩ := L128P.T_le_normalizer_w128 h1222 h12213 hs
  rw [hkY _ hTW, hkY _ hTZ]
  have h3 := L14312.twelve_three_of_eq S ⟨hk, hkN⟩ (L128P.uA_eq h1222 hs) D
    (L128P.four_lt_relIndex h1222 h12213 hs) ha haV₁
  exact ⟨h3, hFixS D.V D.B _ (D.π a) _ _ _ h3 (L128P.isQuotientOfSQTK_img hs D)⟩

open L14332 in
theorem data_of (h1332 : Stmt13_3_2) (h1334 : A6.Stmt13_3_4) (h1222 : Stmt12_2_2)
    (h12213 : Stmt12_2_13) (h12813 : Lemma12_8_13) (h14312 : Lemma14312One)
    (hFixS : G11.SzG11S.TheoremG112FixS) {T L V : Subgroup G} (h : Hyp14310One G T L V)
    (hlt : fsuV1 T V < centerOf (fsuU T V)) {V₂ : Subgroup G} {g : G}
    (hV₂ : IsL32NPlane T V V₂) (hgP : g ∈ p128 T L V) (hgN : g ∉ l32nH T V)
    (D : HatModelU (fsuU T V)) :
    ∃ a : G, G111Hyp D.B (D.img (l32nH T V)) (D.π a) (D.hat (l32nE T V V₂ g))
        (D.img (CFSG.conjugate (l32nW T V V₂) g)) (D.img (CFSG.conjugate (centerOf (fsuU T V)) g)) ∧
      G11.SzG11S.G112ConclusionFixS D.B (D.img (l32nH T V))
        (D.img (CFSG.conjugate (l32nW T V V₂) g)) ∧
      2 ^ (Module.finrank (ZMod 2) D.V / 2) ≤ Nat.card ↥(D.img (CFSG.conjugate (l32nW T V V₂) g)) ∧
      D.img (CFSG.conjugate (centerOf (fsuU T V)) g) ≠ ⊥ := by
  have h13322 := stmt13_3_2_two_of_stmt13_3_2 h1332
  have hV := stmtL32NModule_of_inputs h1332 h1334
  have hs := h.setting1282One h13322 hV hV₂
  obtain ⟨-, -, -, hV1, -⟩ := hV G T L V h.hyp h.fsu
  have hV₂4 : Nat.card V₂ = 4 := hV₂.1.2.1
  have hlt12 : fsuV1 T V < V₂ := lt_of_le_of_ne hV₂.2 fun he => by rw [he] at hV1; omega
  obtain ⟨a, haV₂, ha1⟩ := IsConcreteLE.exists_of_lt hlt12
  obtain ⟨H, hconc⟩ := fixS_of h1222 h12213 hFixS hs hgP hgN haV₂ ha1 D
  refine ⟨a, H, hconc, ?_, ?_⟩
  ·
    by_contra hcon
    push Not at hcon
    obtain ⟨k, hk₀⟩ := H.toG101Hyp.exists_card_X
    have hk : Nat.card ↥(D.img (CFSG.conjugate (l32nW T V V₂) g)) = 2 ^ k := hk₀
    rw [hk] at hcon
    have hkd : k < Module.finrank (ZMod 2) D.V / 2 := by
      by_contra hk'
      push Not at hk'
      have := Nat.pow_le_pow_right (show 0 < 2 by norm_num) hk'
      omega
    have hle : Nat.card ↥(D.img (CFSG.conjugate (l32nW T V V₂) g)) ≤
        2 ^ (Module.finrank (ZMod 2) D.V / 2 - 1) := by
      rw [hk]
      exact Nat.pow_le_pow_right (by norm_num) (by omega)
    have hZ := (h14312 G T L V h V₂ g hV₂ hgP hgN D hle).2.2.1.1
    exact hlt.ne' hZ
  ·
    intro hbot
    apply (h12813 G T L V 3 (fsuV1 T V) V₂ hs g hgP hgN).2.2.1 hlt
    intro y hy
    have hyH := conj_zU_le h12813 hs hgP hgN hy
    have hρ : D.ρ ⟨y, l32nH_le_normalizer_fsuU T V hyH⟩ = 1 := by
      have hmem : D.ρ ⟨y, l32nH_le_normalizer_fsuU T V hyH⟩ ∈
          D.img (CFSG.conjugate (centerOf (fsuU T V)) g) :=
        L128A.HatU.rho_mem_img D hy (l32nH_le_normalizer_fsuU T V hyH)
      rw [hbot, Subgroup.mem_bot] at hmem
      exact hmem
    exact (rho_eq_one_iff_mem hyH _).mp hρ

end L14324

end CFSG.Quasithin.H13
