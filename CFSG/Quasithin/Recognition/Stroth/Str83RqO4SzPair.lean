module

import CFSG.Quasithin.Recognition.Stroth.Str83RqO4Dictionary
import CFSG.Quasithin.Recognition.Stroth.Str83RqTorus
import CFSG.LieType.SuzukiSubgroups.Torus
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.ProofsSzPointAction
import CFSG.Quasithin.Recognition.Stroth.BenderCaseIIFacts
import CFSG.Quasithin.Recognition.Stroth.F112Tree
import CFSG.Quasithin.Recognition.GoldschmidtF112RAutJ2
import CFSG.Goldschmidt.Steps.Sec82Tools
public import CFSG.Quasithin.EmptyFaithful.S152Y06
public import CFSG.Quasithin.Recognition.Stroth.Str83RqTrack

public section

namespace CFSG.Quasithin.Stroth.Rq

open Subgroup CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.LieType.BorelTits
open CFSG.Quasithin.Stroth.G5

section Quot

variable {X : Type} [Group X] [Finite X]

private theorem szp_eq_top_or_pair
    {n : ℕ} (hX : CFSG.Quasithin.IsSz n X) {Q₁ Q₂ : Sylow 2 X} (hne : Q₁ ≠ Q₂) {Y : Subgroup X}
    (hK : normalizer ((Q₁ : Subgroup X) : Set X) ⊓ normalizer ((Q₂ : Subgroup X) : Set X) ≤ Y)
    {y : X} (hy : y ∈ Y) (hyQ : y • Q₁ = Q₂) :
    Y = ⊤ ∨ ∀ g ∈ Y, (g • Q₁ = Q₁ ∧ g • Q₂ = Q₂) ∨ (g • Q₁ = Q₂ ∧ g • Q₂ = Q₁) := by
  classical
  rcases CFSG.LieType.SuzukiSubgroups.eq_top_or_le_normalizer_torus hX hne hK hy hyQ with h | h
  · exact Or.inl h
  right
  intro g hg
  have T : CFSG.GroupTheory.SuzukiTorusData X (2 ^ n) :=
    CFSG.LocalAnalysis.UniquenessCase.UC22.szPointActionFacts_holds X n
      (CFSG.GH74.Filter.lieModel_of_suzuki hX)
  set D : Subgroup X :=
    normalizer ((Q₁ : Subgroup X) : Set X) ⊓ normalizer ((Q₂ : Subgroup X) : Set X) with hDdef
  have hcard : Nat.card D = 2 ^ n - 1 := CFSG.GroupTheory.SuzukiTorusData.torus_card T hne
  have hn : 2 ≤ n := by
    obtain ⟨-, a, ha, -, -, -, rfl, -⟩ := hX
    omega
  have h4 : 4 ≤ 2 ^ n := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  obtain ⟨t, htD, ht1⟩ : ∃ t ∈ D, t ≠ 1 := by
    by_contra hc
    push Not at hc
    have hbot : D = ⊥ := (Subgroup.eq_bot_iff_forall D).mpr hc
    have h1 : Nat.card D = 1 := by rw [hbot, Subgroup.card_bot]
    omega
  have hgN : g ∈ normalizer (D : Set X) := h hg
  have hgD : g⁻¹ * t * g ∈ D := by
    have := (Subgroup.mem_normalizer_iff'' .. |>.mp hgN t).mp htD
    simpa [mul_assoc] using this
  have hfix : ∀ P : Sylow 2 X, P = Q₁ ∨ P = Q₂ ∨ P = g • Q₁ ∨ P = g • Q₂ → t • P = P := by
    intro P hP
    rcases hP with rfl | rfl | rfl | rfl
    · exact Sylow.smul_eq_iff_mem_normalizer.mpr (Subgroup.mem_inf.mp htD).1
    · exact Sylow.smul_eq_iff_mem_normalizer.mpr (Subgroup.mem_inf.mp htD).2
    · have h1 : (g⁻¹ * t * g) • Q₁ = Q₁ :=
        Sylow.smul_eq_iff_mem_normalizer.mpr (Subgroup.mem_inf.mp hgD).1
      calc t • g • Q₁ = g • (g⁻¹ * t * g) • Q₁ := by rw [smul_smul, smul_smul]; group
        _ = g • Q₁ := by rw [h1]
    · have h1 : (g⁻¹ * t * g) • Q₂ = Q₂ :=
        Sylow.smul_eq_iff_mem_normalizer.mpr (Subgroup.mem_inf.mp hgD).2
      calc t • g • Q₂ = g • (g⁻¹ * t * g) • Q₂ := by rw [smul_smul, smul_smul]; group
        _ = g • Q₂ := by rw [h1]
  have hle := T.fixes_le_two t ht1
  have key : ∀ P : Sylow 2 X, t • P = P → P = Q₁ ∨ P = Q₂ := by
    intro P hP
    by_contra hc
    push Not at hc
    obtain ⟨hc1, hc2⟩ := hc
    haveI : Finite (Sylow 2 X) := CFSG.GroupTheory.SuzukiTorusData.sylow_finite
    have hQ₁ : t • Q₁ = Q₁ := hfix Q₁ (Or.inl rfl)
    have hQ₂ : t • Q₂ = Q₂ := hfix Q₂ (Or.inr (Or.inl rfl))
    let f : Fin 3 → {P : Sylow 2 X // t • P = P} := ![⟨Q₁, hQ₁⟩, ⟨Q₂, hQ₂⟩, ⟨P, hP⟩]
    have hf : Function.Injective f := by
      intro i j hij
      have hv := congrArg Subtype.val hij
      fin_cases i <;> fin_cases j <;> simp [f] at hv ⊢ <;>
        first
        | exact hne hv | exact hne hv.symm | exact hc1 hv | exact hc1 hv.symm
        | exact hc2 hv | exact hc2 hv.symm
    have h3 := Nat.card_le_card_of_injective f hf
    simp only [Nat.card_eq_fintype_card, Fintype.card_fin] at h3
    omega
  have hg1 := key (g • Q₁) (hfix _ (Or.inr (Or.inr (Or.inl rfl))))
  have hg2 := key (g • Q₂) (hfix _ (Or.inr (Or.inr (Or.inr rfl))))
  have hinj : g • Q₁ ≠ g • Q₂ := fun h' => hne (smul_left_cancel g h')
  rcases hg1 with h1 | h1 <;> rcases hg2 with h2 | h2
  · exact absurd (h1.trans h2.symm) hinj
  · exact Or.inl ⟨h1, h2⟩
  · exact Or.inr ⟨h1, h2⟩
  · exact absurd (h1.trans h2.symm) hinj

end Quot

variable {G : Type} [Group G] [Finite G]

namespace Track

variable {L1 L2 S : Subgroup G} (t : Track L1 L2 S)

private theorem szp_Gv_zero_eq : t.Gv 0 = (L1 ⊔ S) ⊔ t.K := by
  calc t.Gv 0 = P1 L1 L2 S := t.Gv_zero
    _ = L1 ⊔ bigB L1 L2 S := rfl
    _ = L1 ⊔ (S ⊔ t.K) := by rw [← t.sup_K_eq_bigB]
    _ = (L1 ⊔ S) ⊔ t.K := by rw [sup_assoc]

private theorem szp_K_le_normalizer_sup {a f : ℕ} (hfr : Frame L1 L2 S a f) :
    t.K ≤ normalizer ((L1 ⊔ S : Subgroup G) : Set G) := by
  have hKL1 : t.K ≤ normalizer (L1 : Set G) := by
    refine sup_le ?_ ?_
    · exact (le_sup_right : t.D1 ≤ (S ⊓ L1) ⊔ t.D1).trans
        ((le_of_eq t.hD1sup.symm).trans ((F1.borelOf_le L1 S).trans Subgroup.le_normalizer))
    · exact (le_sup_right : t.D2 ≤ (S ⊓ L2) ⊔ t.D2).trans
        ((le_of_eq t.hD2sup.symm).trans hfr.hF.1.h1.borel_le)
  have hKS : t.K ≤ normalizer (S : Set G) :=
    ((le_sup_right : t.K ≤ S ⊔ t.K).trans (le_of_eq t.sup_K_eq_bigB)).trans hfr.hN
  exact F1.le_normalizer_sup hKL1 hKS

private theorem szp_vertex {a f : ℕ} (hfr : Frame L1 L2 S a f) :
    pCoreOf 2 (L1 ⊔ S) = t.Qv 0 ∧ IsSylowTwoOf S (L1 ⊔ S) ∧
      Nonempty (oTwoQuot ↥(L1 ⊔ S) ≃* Sz a) := by
  have hF : F112HypW L1 L2 S := hfr.hF
  have hH : Hyp111 L1 L2 S := hF.1
  have hS1 : S = (S ⊓ L1) ⊔ Q1 L1 L2 S :=
    eq_sup_pCoreOf_of_bender_left hH hfr.hN (Or.inl ⟨a, hfr.ha, hfr.hSz⟩)
  have hsup : L1 ⊔ S = L1 ⊔ Q1 L1 L2 S := sup_eq_of_S_eq hS1
  refine ⟨?_, ?_, ?_⟩
  · rw [hsup, t.Qv_zero]
    exact pCoreOf_sup_pCoreOf hH
  · refine F7.isSylowTwoOf_mono_right (f112_isSylowTwoOf_P1 hF) le_sup_right ?_
    exact sup_le le_sup_left ((le_sup_right : S ≤ bigB L1 L2 S).trans le_sup_right)
  · exact ⟨(CFSG.Quasithin.F112R.oTwoQuotCongr (MulEquiv.subgroupCongr hsup)).trans
      ((oTwoQuotSupEquiv hH).trans (Classical.choice hfr.hSz))⟩

private theorem szp_mem_bigB {a f : ℕ} (hfr : Frame L1 L2 S a f)
    {l : G} (hl : l ∈ L1 ⊔ S) (hlN : l ∈ normalizer (S : Set G)) : l ∈ bigB L1 L2 S := by
  have hH : Hyp111 L1 L2 S := hfr.hF.1
  rw [sup_comm] at hl
  obtain ⟨s, hs, m, hm, rfl⟩ :=
    (F1.mem_sup_iff_exists_mul_of_le_normalizer (H := S) (K := L1) hH.h1.normalizes).mp hl
  have hmN : m ∈ normalizer (S : Set G) := by
    have hsN : s ∈ normalizer (S : Set G) := Subgroup.le_normalizer hs
    have h := (normalizer (S : Set G)).mul_mem ((normalizer (S : Set G)).inv_mem hsN) hlN
    simpa [mul_assoc] using h
  have hmB : m ∈ borelOf L1 S :=
    Subgroup.mem_inf.mpr ⟨hm,
      A4.mem_normalizer_inf (A := S) (B := L1) hmN (Subgroup.le_normalizer hm)⟩
  have hle : borelOf L1 S ≤ bigB L1 L2 S := le_sup_left.trans le_sup_left
  exact (bigB L1 L2 S).mul_mem ((le_sup_right : S ≤ bigB L1 L2 S) hs) (hle hmB)

private theorem szp_bigB_le_Gv_one {a f : ℕ}
    (hfr : Frame L1 L2 S a f) : bigB L1 L2 S ≤ t.Gv 1 := by
  rw [t.Gv_one, ← f112_parabolic_inf_eq_bigB hfr.hF]
  exact inf_le_right

private theorem szp_mk_mem_normalizer_iff {a f : ℕ}
    (hfr : Frame L1 L2 S a f) (l : ↥(L1 ⊔ S)) :
    (QuotientGroup.mk l : OTwoQuot (L1 ⊔ S)) ∈
        normalizer ((imageOTwoQuot (L1 ⊔ S) S : Subgroup (OTwoQuot (L1 ⊔ S))) :
          Set (OTwoQuot (L1 ⊔ S))) ↔
      (l : G) ∈ t.Gv 1 := by
  classical
  obtain ⟨hpc, -, -⟩ := t.szp_vertex hfr
  have hSL : S ≤ L1 ⊔ S := le_sup_right
  have hQS : t.Qv 0 ≤ S := by rw [t.Qv_zero]; exact Q1_le_S hfr.hF
  constructor
  · intro hl
    have hconj : ∀ s ∈ S, (l : G) * s * (l : G)⁻¹ ∈ S := by
      intro s hs
      have hsbar : (QuotientGroup.mk (⟨s, hSL hs⟩ : ↥(L1 ⊔ S)) : OTwoQuot (L1 ⊔ S)) ∈
          imageOTwoQuot (L1 ⊔ S) S :=
        mem_imageOTwoQuot_iff.mpr ⟨s, hSL hs, hs, rfl⟩
      have h1 := (Subgroup.mem_normalizer_iff.mp hl _).mp hsbar
      have h2 : (QuotientGroup.mk (l * ⟨s, hSL hs⟩ * l⁻¹ : ↥(L1 ⊔ S)) : OTwoQuot (L1 ⊔ S)) ∈
          imageOTwoQuot (L1 ⊔ S) S := by
        rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv]
        exact h1
      have h3 := mem_sup_pCoreOf_of_mk_mem h2
      rw [hpc, sup_eq_left.mpr hQS] at h3
      simpa using h3
    have hlN : (l : G) ∈ normalizer (S : Set G) :=
      CFSG.Goldschmidt.Sec82.mem_normalizer_of_conj_mem hconj
    exact t.szp_bigB_le_Gv_one hfr (szp_mem_bigB hfr l.2 hlN)
  · intro hl1
    have hl0 : (l : G) ∈ t.Gv 0 := by
      rw [t.szp_Gv_zero_eq]
      exact Subgroup.mem_sup_left l.2
    have hB : t.Gv 0 ⊓ t.Gv 1 = bigB L1 L2 S := by
      rw [t.Gv_zero, t.Gv_one]
      exact f112_parabolic_inf_eq_bigB hfr.hF
    have hlB : (l : G) ∈ bigB L1 L2 S := hB ▸ Subgroup.mem_inf.mpr ⟨hl0, hl1⟩
    have hle := S152Y.imageOTwoQuot_le_normalizer (M := L1 ⊔ S)
      (X := (L1 ⊔ S) ⊓ bigB L1 L2 S) (Y := S) (inf_le_right.trans hfr.hN)
    exact hle (mem_imageOTwoQuot_iff.mpr ⟨l, l.2, ⟨l.2, hlB⟩, rfl⟩)

private theorem szp_conj_mem_Gv_one_iff {u : G} (hu : t.x₁⁻¹ * u ∈ t.Gv 1) (z : G) :
    u⁻¹ * z * u ∈ t.Gv 1 ↔ z ∈ t.Gv (-1) := by
  have hmap := t.map_Gv_x₁ 1
  constructor
  · intro hz
    rw [← hmap]
    refine Subgroup.mem_map.mpr ⟨(t.x₁⁻¹ * u) * (u⁻¹ * z * u) * (t.x₁⁻¹ * u)⁻¹,
      (t.Gv 1).mul_mem ((t.Gv 1).mul_mem hu hz) ((t.Gv 1).inv_mem hu), ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  · intro hz
    rw [← hmap] at hz
    obtain ⟨w, hw, hwz⟩ := Subgroup.mem_map.mp hz
    have : u⁻¹ * z * u = (t.x₁⁻¹ * u)⁻¹ * w * (t.x₁⁻¹ * u) := by
      rw [← hwz]
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
    rw [this]
    exact (t.Gv 1).mul_mem ((t.Gv 1).mul_mem ((t.Gv 1).inv_mem hu) hw) hu

theorem pair_or_le_sup_Qv_zero
    {a f : ℕ} (hfr : Frame L1 L2 S a f) {H : Subgroup G} (hH : H ≤ t.Gv 0) (hK : t.K ≤ H)
    {y : G} (hy : y ∈ H) (hyx : t.x₁⁻¹ * y ∈ t.Gv 1 ⊓ t.Gv (-1)) :
    (∀ g ∈ H, g ∈ t.Gv 1 ⊓ t.Gv (-1) ∨ t.x₁⁻¹ * g ∈ t.Gv 1 ⊓ t.Gv (-1)) ∨
      L1 ≤ H ⊔ t.Qv 0 := by
  classical
  obtain ⟨hpc, hSyl, hSzH⟩ := t.szp_vertex hfr
  have hIsSz : CFSG.Quasithin.IsSz (2 * a + 1) (oTwoQuot ↥(L1 ⊔ S)) :=
    CFSG.LieType.SuzukiSubgroups.isSz_of_mulEquiv hfr.ha (Classical.choice hSzH)
  have hdec : ∀ g ∈ t.Gv 0, ∃ gL ∈ L1 ⊔ S, ∃ k ∈ t.K, g = gL * k := by
    intro g hg
    rw [t.szp_Gv_zero_eq] at hg
    exact (F1.mem_sup_iff_exists_mul_of_normalizes (H := L1 ⊔ S) (K := t.K)
      (t.szp_K_le_normalizer_sup hfr)).mp hg
  obtain ⟨Q₁, hQ₁⟩ := exists_sylow_imageOTwoQuot hSyl
  have T1 : ∀ l : ↥(L1 ⊔ S), (QuotientGroup.mk l : OTwoQuot (L1 ⊔ S)) ∈
      normalizer ((Q₁ : Subgroup (oTwoQuot ↥(L1 ⊔ S))) : Set (oTwoQuot ↥(L1 ⊔ S))) ↔
        (l : G) ∈ t.Gv 1 := by
    intro l
    rw [hQ₁]
    exact t.szp_mk_mem_normalizer_iff hfr l
  obtain ⟨yL, hyL, ky, hky, rfl⟩ := hdec y (hH hy)
  have hyLH : yL ∈ H := by simpa using H.mul_mem hy (H.inv_mem (hK hky))
  have hm : t.x₁⁻¹ * yL ∈ t.Gv 1 ⊓ t.Gv (-1) := by
    have hkinv : ky⁻¹ ∈ t.Gv 1 ⊓ t.Gv (-1) :=
      (t.Gv 1 ⊓ t.Gv (-1)).inv_mem ⟨t.K_le_Gv 1 hky, t.K_le_Gv (-1) hky⟩
    have h := (t.Gv 1 ⊓ t.Gv (-1)).mul_mem hyx hkinv
    simpa [mul_assoc] using h
  set yb : oTwoQuot ↥(L1 ⊔ S) := QuotientGroup.mk (⟨yL, hyL⟩ : ↥(L1 ⊔ S)) with hyb
  set Q₂ : Sylow 2 (oTwoQuot ↥(L1 ⊔ S)) := yb • Q₁ with hQ₂
  have conjEq : ∀ g : oTwoQuot ↥(L1 ⊔ S), g • Q₂ = Q₂ ↔ (yb⁻¹ * g * yb) • Q₁ = Q₁ := by
    intro g
    rw [mul_smul, mul_smul, inv_smul_eq_iff]
  have T1' : ∀ l : ↥(L1 ⊔ S), (QuotientGroup.mk l : OTwoQuot (L1 ⊔ S)) ∈
      normalizer ((Q₂ : Subgroup (oTwoQuot ↥(L1 ⊔ S))) : Set (oTwoQuot ↥(L1 ⊔ S))) ↔
        (l : G) ∈ t.Gv (-1) := by
    intro l
    have e1 : (QuotientGroup.mk l : OTwoQuot (L1 ⊔ S)) ∈
        normalizer ((Q₂ : Subgroup (oTwoQuot ↥(L1 ⊔ S))) : Set (oTwoQuot ↥(L1 ⊔ S))) ↔
          (QuotientGroup.mk l : oTwoQuot ↥(L1 ⊔ S)) • Q₂ = Q₂ :=
      Sylow.smul_eq_iff_mem_normalizer.symm
    have e2 : (yb⁻¹ * (QuotientGroup.mk l : oTwoQuot ↥(L1 ⊔ S)) * yb) • Q₁ = Q₁ ↔
        yb⁻¹ * (QuotientGroup.mk l : oTwoQuot ↥(L1 ⊔ S)) * yb ∈
          normalizer ((Q₁ : Subgroup (oTwoQuot ↥(L1 ⊔ S))) : Set (oTwoQuot ↥(L1 ⊔ S))) :=
      Sylow.smul_eq_iff_mem_normalizer
    rw [e1, conjEq, e2]
    have he : yb⁻¹ * (QuotientGroup.mk l : OTwoQuot (L1 ⊔ S)) * yb =
        QuotientGroup.mk ((⟨yL, hyL⟩ : ↥(L1 ⊔ S))⁻¹ * l * ⟨yL, hyL⟩) := by
      rw [hyb, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv]
    rw [he, T1]
    have hc : (((⟨yL, hyL⟩ : ↥(L1 ⊔ S))⁻¹ * l * ⟨yL, hyL⟩ : ↥(L1 ⊔ S)) : G) =
        yL⁻¹ * (l : G) * yL := by simp
    rw [hc]
    exact t.szp_conj_mem_Gv_one_iff hm.1 (l : G)
  have hne : Q₁ ≠ Q₂ := by
    intro h
    have h' : yb • Q₁ = Q₁ := by rw [← hQ₂]; exact h.symm
    have hmem := (T1 ⟨yL, hyL⟩).mp (Sylow.smul_eq_iff_mem_normalizer.mp h')
    apply t.x₁_not_mem_Gv_one
    have hx : t.x₁ = yL * (t.x₁⁻¹ * yL)⁻¹ := by group
    rw [hx]
    exact (t.Gv 1).mul_mem hmem ((t.Gv 1).inv_mem hm.1)
  have hD1L : t.D1 ≤ L1 ⊔ S :=
    (t.hD1hall.1.trans (F1.borelOf_le L1 S)).trans le_sup_left
  have hD1sub : imageOTwoQuot (L1 ⊔ S) t.D1 ≤
      normalizer ((Q₁ : Subgroup (oTwoQuot ↥(L1 ⊔ S))) : Set (oTwoQuot ↥(L1 ⊔ S))) ⊓
        normalizer ((Q₂ : Subgroup (oTwoQuot ↥(L1 ⊔ S))) : Set (oTwoQuot ↥(L1 ⊔ S))) := by
    intro u hu
    obtain ⟨d, hdL, hdD, rfl⟩ := mem_imageOTwoQuot_iff.mp hu
    have hdK : d ∈ t.K := (le_sup_left : t.D1 ≤ t.D1 ⊔ t.D2) hdD
    exact ⟨(T1 ⟨d, hdL⟩).mpr (t.K_le_Gv 1 hdK), (T1' ⟨d, hdL⟩).mpr (t.K_le_Gv (-1) hdK)⟩
  have Tt : CFSG.GroupTheory.SuzukiTorusData (oTwoQuot ↥(L1 ⊔ S)) (2 ^ (2 * a + 1)) :=
    CFSG.LocalAnalysis.UniquenessCase.UC22.szPointActionFacts_holds _ (2 * a + 1)
      (CFSG.GH74.Filter.lieModel_of_suzuki hIsSz)
  have hcardT : Nat.card ↥(normalizer ((Q₁ : Subgroup (oTwoQuot ↥(L1 ⊔ S))) :
      Set (oTwoQuot ↥(L1 ⊔ S))) ⊓ normalizer ((Q₂ : Subgroup (oTwoQuot ↥(L1 ⊔ S))) :
        Set (oTwoQuot ↥(L1 ⊔ S)))) = 2 ^ (2 * a + 1) - 1 :=
    CFSG.GroupTheory.SuzukiTorusData.torus_card Tt hne
  have hcardD : Nat.card (imageOTwoQuot (L1 ⊔ S) t.D1) = 2 ^ (2 * a + 1) - 1 := by
    rw [QA12.card_image_of_odd hD1L t.hD1hall.2.1, t.card_D1 hfr]
  have hDeq := Subgroup.eq_of_le_of_card_ge hD1sub (by rw [hcardT, hcardD])
  set Y : Subgroup (oTwoQuot ↥(L1 ⊔ S)) := imageOTwoQuot (L1 ⊔ S) (H ⊓ (L1 ⊔ S)) with hY
  have hTY : normalizer ((Q₁ : Subgroup (oTwoQuot ↥(L1 ⊔ S))) : Set (oTwoQuot ↥(L1 ⊔ S))) ⊓
      normalizer ((Q₂ : Subgroup (oTwoQuot ↥(L1 ⊔ S))) : Set (oTwoQuot ↥(L1 ⊔ S))) ≤ Y := by
    rw [← hDeq, hY]
    exact imageOTwoQuot_mono (le_inf (le_sup_left.trans hK) hD1L)
  have hyY : yb ∈ Y := mem_imageOTwoQuot_iff.mpr ⟨yL, hyL, ⟨hyLH, hyL⟩, rfl⟩
  rcases szp_eq_top_or_pair hIsSz hne hTY hyY hQ₂.symm with htop | hpair
  · right
    intro l hl
    have hlL : l ∈ L1 ⊔ S := le_sup_left (a := L1) hl
    have hmem : (QuotientGroup.mk (⟨l, hlL⟩ : ↥(L1 ⊔ S)) : OTwoQuot (L1 ⊔ S)) ∈
        imageOTwoQuot (L1 ⊔ S) (H ⊓ (L1 ⊔ S)) := by
      rw [← hY, htop]
      exact Subgroup.mem_top _
    have h := mem_sup_pCoreOf_of_mk_mem hmem
    rw [hpc] at h
    exact (sup_le_sup_right (inf_le_left : H ⊓ (L1 ⊔ S) ≤ H) (t.Qv 0)) h
  · left
    have hyswap : yb • Q₂ = Q₁ := by
      rcases hpair yb hyY with ⟨h1', -⟩ | ⟨-, h2'⟩
      · exact absurd (hQ₂.trans h1') hne.symm
      · exact h2'
    intro g hg
    obtain ⟨gL, hgL, k, hk, rfl⟩ := hdec g (hH hg)
    have hgLH : gL ∈ H := by simpa using H.mul_mem hg (H.inv_mem (hK hk))
    have hgY : (QuotientGroup.mk (⟨gL, hgL⟩ : ↥(L1 ⊔ S)) : oTwoQuot ↥(L1 ⊔ S)) ∈ Y :=
      mem_imageOTwoQuot_iff.mpr ⟨gL, hgL, ⟨hgLH, hgL⟩, rfl⟩
    have hk1 := t.K_le_Gv 1 hk
    have hk2 := t.K_le_Gv (-1) hk
    rcases hpair _ hgY with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · left
      have hg1 := (T1 ⟨gL, hgL⟩).mp (Sylow.smul_eq_iff_mem_normalizer.mp h1)
      have hg2 := (T1' ⟨gL, hgL⟩).mp (Sylow.smul_eq_iff_mem_normalizer.mp h2)
      exact ⟨(t.Gv 1).mul_mem hg1 hk1, (t.Gv (-1)).mul_mem hg2 hk2⟩
    · right
      have hce : (QuotientGroup.mk ((⟨yL, hyL⟩ : ↥(L1 ⊔ S))⁻¹ * ⟨gL, hgL⟩) :
          oTwoQuot ↥(L1 ⊔ S)) = yb⁻¹ * QuotientGroup.mk (⟨gL, hgL⟩ : ↥(L1 ⊔ S)) := by
        rw [hyb, QuotientGroup.mk_mul, QuotientGroup.mk_inv]
      have hc1 : (QuotientGroup.mk ((⟨yL, hyL⟩ : ↥(L1 ⊔ S))⁻¹ * ⟨gL, hgL⟩) :
          oTwoQuot ↥(L1 ⊔ S)) • Q₁ = Q₁ := by
        rw [hce, mul_smul, h1, hQ₂, inv_smul_smul]
      have hc2 : (QuotientGroup.mk ((⟨yL, hyL⟩ : ↥(L1 ⊔ S))⁻¹ * ⟨gL, hgL⟩) :
          oTwoQuot ↥(L1 ⊔ S)) • Q₂ = Q₂ := by
        rw [hce, mul_smul, h2, inv_smul_eq_iff, hyswap]
      have hc1' := (T1 _).mp (Sylow.smul_eq_iff_mem_normalizer.mp hc1)
      have hc2' := (T1' _).mp (Sylow.smul_eq_iff_mem_normalizer.mp hc2)
      simp only [Subgroup.coe_mul, Subgroup.coe_inv] at hc1' hc2'
      have he : t.x₁⁻¹ * (gL * k) = (t.x₁⁻¹ * yL) * (yL⁻¹ * gL) * k := by group
      rw [he]
      exact ⟨(t.Gv 1).mul_mem ((t.Gv 1).mul_mem hm.1 hc1') hk1,
        (t.Gv (-1)).mul_mem ((t.Gv (-1)).mul_mem hm.2 hc2') hk2⟩

end Track

end CFSG.Quasithin.Stroth.Rq
