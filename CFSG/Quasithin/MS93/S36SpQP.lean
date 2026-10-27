module

public import CFSG.Quasithin.MS93.S36SpLine

public section

namespace CFSG.Quasithin.MS93.S36SP

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.MS93.MSP
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open CFSG.Quasithin.MS93.S36
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G} {h : PUHyp M T L}

theorem mat_pow_mulVec {F : Type} [Field F] {g : Sp4 F} {v : V4 F} {c : F}
    (hg : mat g *ᵥ v = c • v) (n : ℕ) : mat (g ^ n) *ᵥ v = c ^ n • v := by
  induction n with
  | zero => rw [pow_zero, pow_zero, mat_one, Matrix.one_mulVec, one_smul]
  | succ n ih =>
    rw [pow_succ g, mat_mul_mulVec, hg, Matrix.mulVec_smul, ih, smul_smul, ← pow_succ']

namespace PairHyp

variable {d : SpFrame h} {χ : MulAut ↥T} (hp : PairHyp d χ)
include hp

theorem actsMat_qPoint {v : V4 d.F} (hx : XData d (tImage χ (Z0q M T)) v) {K : Subgroup G}
    (hKT : K ≤ T) (hK : ⁅tImage χ (pCoreOf 2 M), K⁆ ≤ tImage χ (Z0q M T)) :
    ∀ k ∈ K, ∃ g, ActsMat d.vec k g ∧ g ∈ qPoint (d.F ∙ v) := by
  have hE := hp.actsMat_E
  have hP := actsMat_P hx
  have hPM : tImage χ (pCoreOf 2 M) ≤ M := tImage_le_M h χ _
  have hfixP : fixSp (d.img _ hPM hP) = d.F ∙ v := hp.fixSp_P hx
  intro k hk
  have hkM : k ∈ M := h.le (hKT hk)
  obtain ⟨f, hfb, hfn, hf⟩ := d.exists_add hkM
  have hfw : ∀ w ∈ perp (d.F ∙ v), f w - w ∈ d.F ∙ v := by
    intro w hw
    obtain ⟨u, hu⟩ := d.surj (Multiplicative.ofAdd w)
    have huP : (u : G) ∈ tImage χ (pCoreOf 2 M) := by
      refine pre_perp_le hx hE ((d.mem_pre_coe u).2 ?_)
      rw [hu, toAdd_ofAdd]
      exact hw
    have hcU : k * u * k⁻¹ * (u : G)⁻¹ ∈ Uq M T L :=
      mul_mem (conj_mem (d.normU hkM) u) (inv_mem u.2)
    have hcE : k * u * k⁻¹ * (u : G)⁻¹ ∈ tImage χ (Z0q M T) := by
      have := Subgroup.commutator_mem_commutator huP hk
      have e : ⁅(u : G), k⁆⁻¹ = k * u * k⁻¹ * (u : G)⁻¹ := by
        simp only [commutatorElement_def]
        group
      rw [← e]
      exact Subgroup.inv_mem _ (hK this)
    have hcC : k * u * k⁻¹ * (u : G)⁻¹ ∈ Subgroup.centralizer (tImage χ (pCoreOf 2 M) : Set G) :=
      fun x hx' => (Subgroup.mem_centralizer_iff.1
        (tImage_pCoreOf_le_centralizer h χ hx') _ hcE).symm
    have hcv := (d.mem_centralizer_iff hPM hP ⟨_, hcU⟩).1 hcC
    rw [hfixP] at hcv
    have e : (⟨k * u * k⁻¹ * (u : G)⁻¹, hcU⟩ : ↥(Uq M T L)) =
        ⟨_, conj_mem (d.normU hkM) u⟩ * u⁻¹ := rfl
    rw [e, map_mul, map_inv, toAdd_mul, toAdd_inv, hf u _ rfl, hu, toAdd_ofAdd,
      ← sub_eq_add_neg] at hcv
    exact hcv
  obtain ⟨w₀, hw₀, hw₀v⟩ : ∃ w₀ ∈ perp (d.F ∙ v), w₀ ∉ d.F ∙ v := by
    by_contra hcon
    push Not at hcon
    have h1 : Module.finrank d.F (perp (d.F ∙ v)) ≤ Module.finrank d.F (d.F ∙ v) :=
      Submodule.finrank_mono hcon
    rw [finrank_span_singleton hx.ne] at h1
    have h2 := finrank_perp (d.F ∙ v)
    rw [finrank_span_singleton hx.ne] at h2
    omega
  have hlin := linear_of_fix_mod hfb hfn hw₀v fun c => hfw _ (Submodule.smul_mem _ c hw₀)
  obtain ⟨g, hg⟩ := d.exists_actsMat hkM (pow_eq_one_of_mem_T h (hKT hk)) hfb hfn hf hlin
  refine ⟨g, hg, mem_qPoint.2 ⟨?_, fun w hw => ?_⟩⟩
  ·
    have hfg : ∀ w, f w = mat g *ᵥ w := by
      intro w
      obtain ⟨u, hu⟩ := d.surj (Multiplicative.ofAdd w)
      have h1 := hf u ⟨_, conj_mem (d.normU hkM) u⟩ rfl
      have h2 := hg u ⟨_, conj_mem (d.normU hkM) u⟩ rfl
      rw [hu, toAdd_ofAdd] at h1 h2
      rw [← h1, h2]
    have hv : v ∈ perp (d.F ∙ v) := le_perp_of_isPoint (isPoint_span hx.ne)
      (Submodule.mem_span_singleton_self v)
    obtain ⟨μ, hμ⟩ := Submodule.mem_span_singleton.1 (hfw v hv)
    rw [hfg] at hμ
    have hgv : mat g *ᵥ v = (μ + 1) • v := by
      rw [add_smul, one_smul, hμ, sub_add_cancel]
    obtain ⟨e, he⟩ := pow_eq_one_of_mem_T h (hKT hk)
    have hge : g ^ 2 ^ e = 1 := by
      have h1 := actsMat_pow (d.normU hkM) hg (2 ^ e)
      rw [he] at h1
      exact actsMat_unique d.surj (one_mem _) h1 actsMat_one
    have h3 := mat_pow_mulVec hgv (2 ^ e)
    rw [hge, mat_one, Matrix.one_mulVec] at h3
    have h4 : (μ + 1) ^ 2 ^ e = 1 := by
      have := smul_left_injective d.F hx.ne (h3.symm.trans (one_smul d.F v).symm)
      exact this
    rw [eq_one_of_pow_two_pow h4, one_smul] at hgv
    intro y hy
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hy
    rw [Matrix.mulVec_smul, hgv]
  · have h1 := hfw w hw
    have h2 : f w = mat g *ᵥ w := by
      obtain ⟨u, hu⟩ := d.surj (Multiplicative.ofAdd w)
      have h3 := hf u ⟨_, conj_mem (d.normU hkM) u⟩ rfl
      have h4 := hg u ⟨_, conj_mem (d.normU hkM) u⟩ rfl
      rw [hu, toAdd_ofAdd] at h3 h4
      rw [← h3, h4]
    rwa [h2] at h1

theorem relIndex_le {v : V4 d.F} (hx : XData d (tImage χ (Z0q M T)) v) {K : Subgroup G}
    (hKT : K ≤ T) (hK : ⁅tImage χ (pCoreOf 2 M), K⁆ ≤ tImage χ (Z0q M T)) :
    (pCoreOf 2 M).relIndex K ≤ (2 ^ d.k) ^ 3 := by
  have hq := hp.actsMat_qPoint hx hKT hK
  have hKM : K ≤ M := hKT.trans h.le
  have hKa : ∀ k ∈ K, ∃ g, ActsMat d.vec k g := fun k hk => (hq k hk).imp fun _ h => h.1
  have hle : d.img K hKM hKa ≤ qPoint (d.F ∙ v) := by
    intro g hg
    obtain ⟨k, hk, hkg⟩ := (d.mem_img hKM hKa).1 hg
    obtain ⟨g', hg', hg'q⟩ := hq k hk
    rw [actsMat_unique d.surj (d.normU (hKM hk)) hkg hg']
    exact hg'q
  rw [← d.card_img hKM hKa hKT, ← d.card_F, ← card_qPoint (isPoint_span hx.ne)]
  exact Subgroup.card_le_of_le hle

theorem commutator_le_of_relIndex {v : V4 d.F} (hx : XData d (tImage χ (Z0q M T)) v)
    {K : Subgroup G} (hKT : K ≤ T) (hK : ⁅tImage χ (pCoreOf 2 M), K⁆ ≤ tImage χ (Z0q M T))
    (hidx : (2 ^ d.k) ^ 3 ≤ (pCoreOf 2 M).relIndex K) :
    ⁅tImage χ (pCoreOf 2 M), Z0q M T⁆ ≤ ⁅K, Z0q M T⁆ := by
  have hE := hp.actsMat_E
  have hP := actsMat_P hx
  have hPM : tImage χ (pCoreOf 2 M) ≤ M := tImage_le_M h χ _
  have hq := hp.actsMat_qPoint hx hKT hK
  have hKM : K ≤ M := hKT.trans h.le
  have hKa : ∀ k ∈ K, ∃ g, ActsMat d.vec k g := fun k hk => (hq k hk).imp fun _ h => h.1
  have himg : d.img K hKM hKa = qPoint (d.F ∙ v) := by
    have hle : d.img K hKM hKa ≤ qPoint (d.F ∙ v) := by
      intro g hg
      obtain ⟨k, hk, hkg⟩ := (d.mem_img hKM hKa).1 hg
      obtain ⟨g', hg', hg'q⟩ := hq k hk
      rw [actsMat_unique d.surj (d.normU (hKM hk)) hkg hg']
      exact hg'q
    refine Subgroup.eq_of_le_of_card_ge hle ?_
    rw [d.card_img hKM hKa hKT, card_qPoint (isPoint_span hx.ne), d.card_F]
    exact hidx
  have hPq : ∀ x ∈ tImage χ (pCoreOf 2 M), ∀ g, ActsMat d.vec x g → g ∈ qPoint (d.F ∙ v) := by
    intro x hxP g hg
    refine mem_qPoint_of_commutator_mem hx.ne (fix_P hx hxP hg) fun w hw => ?_
    have hs : siegel v w ∈ d.img K hKM hKa := by
      rw [himg]
      exact siegel_mem_qPoint (mem_perp_span.1 hw)
    obtain ⟨k, hk, hks⟩ := (d.mem_img hKM hKa).1 hs
    have hxM := hPM hxP
    have hkM := hKM hk
    have hc : x * k * x⁻¹ * k⁻¹ ∈ tImage χ (Z0q M T) := by
      have := hK (Subgroup.commutator_mem_commutator hxP hk)
      rwa [commutatorElement_def] at this
    have h1 : ActsMat d.vec (x * k * x⁻¹ * k⁻¹) (g * siegel v w * g⁻¹ * (siegel v w)⁻¹) :=
      actsMat_mul (inv_mem (d.normU hkM))
        (actsMat_mul (inv_mem (d.normU hxM)) (actsMat_mul (d.normU hkM) hg hks) (actsMat_inv hg))
        (actsMat_inv hks)
    obtain ⟨c, hc'⟩ := hx.mem _ hc _ h1
    rw [hc']
    exact transv_mem_xPoint v c
  rw [Subgroup.commutator_comm, S33.commutator_Z0q_eq h (tImage_le _ _), Subgroup.commutator_comm K,
    S33.commutator_Z0q_eq h hKT, Subgroup.commutator_le]
  intro u hu x hxP
  obtain ⟨g, hg⟩ := hP x hxP
  have hgK : g ∈ d.img K hKM hKa := by
    rw [himg]
    exact hPq x hxP g hg
  obtain ⟨k, hk, hkg⟩ := (d.mem_img hKM hKa).1 hgK
  have hxM := hPM hxP
  have hkM := hKM hk
  have htr : x * k⁻¹ ∈ Subgroup.centralizer (Uq M T L : Set G) := by
    have h1 : ActsMat d.vec (x * k⁻¹) (g * g⁻¹) := actsMat_mul (inv_mem (d.normU hkM)) hg
      (actsMat_inv hkg)
    rw [mul_inv_cancel] at h1
    exact mem_centralizer_of_mem_trivW h
      (mem_trivW_of_actsMat_one h d.ker (M.mul_mem hxM (M.inv_mem hkM)) h1)
  have hux : x * u⁻¹ * x⁻¹ = k * u⁻¹ * k⁻¹ := by
    have h1 := Subgroup.mem_centralizer_iff.1 htr _
      (conj_mem (d.normU hkM) ⟨u⁻¹, inv_mem hu⟩)
    calc x * u⁻¹ * x⁻¹ = (x * k⁻¹) * (k * u⁻¹ * k⁻¹) * (x * k⁻¹)⁻¹ := by group
      _ = k * u⁻¹ * k⁻¹ := by rw [← h1]; group
  have e : ⁅u, x⁆ = ⁅u, k⁆ := by
    simp only [commutatorElement_def]
    calc u * x * u⁻¹ * x⁻¹ = u * (x * u⁻¹ * x⁻¹) := by group
      _ = u * (k * u⁻¹ * k⁻¹) := by rw [hux]
      _ = u * k * u⁻¹ * k⁻¹ := by group
  rw [e]
  exact Subgroup.commutator_mem_commutator hu hk

end PairHyp

end CFSG.Quasithin.MS93.S36SP
