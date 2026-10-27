module

public import CFSG.RankThree.GF2n.Smith81.OrthRootSing
public import CFSG.RankThree.GF2n.Smith81.OrthRootBack
public import CFSG.RankThree.GF2n.Smith81.OrthRootLA

public section

namespace CFSG.RankThree.GF2n.Smith81

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Stroth80
open scoped Matrix

section Tensor

variable {K ι : Type} [Field K]

theorem orthTensor_id_smul (g : Matrix (Fin 2) (Fin 2) K) (k : K) (p : (ι → K) × (ι → K)) :
    orthTensor g id (k • p) = k • orthTensor g id p := by
  simp only [orthTensor, id, Prod.smul_fst, Prod.smul_snd, Prod.smul_mk]
  ext <;> simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] <;> ring

theorem eq_one_of_orthTensor_eq_self [Nonempty ι] {g : Matrix (Fin 2) (Fin 2) K}
    (h : ∀ p : (ι → K) × (ι → K), orthTensor g id p = p) : g = 1 := by
  obtain ⟨κ, -, hg, hv⟩ := exists_scalar_of_orthTensor_eq_self g LinearMap.id h
  obtain ⟨i⟩ := ‹Nonempty ι›
  have h1 : κ = 1 := by simpa using congrFun (hv fun _ => 1) i
  rw [hg, h1, one_smul]

end Tensor

variable {G : Type} [Group G] [Finite G] {M Q Z B A : Subgroup G}
  {K : Type} [Field K] [Finite K] [CharP K 2] {γ : G → K} {M₀ : Tim79.QuadModel Q Z K γ}
  {ι : Type} [Fintype ι] [DecidableEq ι] {qU : QuadraticForm K (ι → K)}
  {φ : M₀.E ≃ₗ[K] (ι → K) × (ι → K)}

theorem LB_le_Lgen_of_eq_conj (hcB : Ctx M Q Z B) {C : Subgroup G} {m : G} (hm : m ∈ M)
    (hC : C = conjSubgroup m B) : LB M Q C ≤ Lgen M (LB M Q B) := by
  subst hC
  rw [hcB.LB_conj hm]
  exact le_iSup₂_of_le m hm le_rfl

theorem exists_pure_of_mem_conj (hcB : Ctx M Q Z B) (hD : GlobalModelData M Q Z γ M₀)
    (hAct : OrthAct Q Z M₀ qU φ (Lgen M (LB M Q B)))
    (hN : ∀ s ∈ Lgen M (LB M Q B), ∀ g : Matrix (Fin 2) (Fin 2) K, g.det = 1 →
      ActsAsTensor Q Z M₀ φ s g id → ∀ x ∈ M, ∃ g' : Matrix (Fin 2) (Fin 2) K, g'.det = 1 ∧
        ActsAsTensor Q Z M₀ φ (x * s * x⁻¹) g' id)
    [Nonempty ι] {c₀ : Fin 2 → K} {u₀ : ι → K}
    (hBimg : ∀ e ∈ M₀.img B, ∃ k : K, φ e = k • (c₀ 0 • u₀, c₀ 1 • u₀))
    {m : G} (hm : m ∈ M) {x : G} (hx : x ∈ conjSubgroup m B) (hxQ : x ∈ Q) :
    ∃ (c : Fin 2 → K) (v : ι → K), φ (M₀.π x) = (c 0 • v, c 1 • v) := by
  classical
  obtain ⟨g, hgdet, hg1, hgfix⟩ :=
    (pure_iff_exists_fix ((c₀ 0 • u₀, c₀ 1 • u₀) : (ι → K) × (ι → K))).mpr ⟨c₀, u₀, rfl⟩
  obtain ⟨s, hs, hsg⟩ := hAct.sl g hgdet
  obtain ⟨g', hg'det, hsg'⟩ := hN s hs g hgdet hsg m hm
  have hsM : s ∈ M := (Lgen_le_H0 hcB hs).1
  have hsQ := (hcB.conj_mem_Q_of_mem_M hsM).1
  have hmQ := (hcB.conj_mem_Q_of_mem_M hm).1
  obtain ⟨σ, a, T, -, hTpi, -, -⟩ := hD.act m hm
  have hb : m⁻¹ * x * m ∈ B := mem_conjSubgroup.mp hx
  set b := m⁻¹ * x * m with hbdef
  have hxb : x = m * b * m⁻¹ := by rw [hbdef]; group
  have hbQ : b ∈ Q := hcB.le hb
  have hsb : M₀.π (s * b * s⁻¹) = M₀.π b := by
    apply φ.injective
    rw [hsg b hbQ]
    obtain ⟨k, hk⟩ := hBimg _ (M₀.pi_mem_img hb hbQ)
    rw [hk, orthTensor_id_smul, hgfix]
  have hfix : orthTensor g' id (φ (M₀.π x)) = φ (M₀.π x) := by
    rw [← hsg' x hxQ]
    have e : m * s * m⁻¹ * x * (m * s * m⁻¹)⁻¹ = m * (s * b * s⁻¹) * m⁻¹ := by
      rw [hxb]; group
    rw [e, hTpi _ (hsQ b hbQ), hsb, ← hTpi b hbQ, ← hxb]
  have hg'1 : g' ≠ 1 := by
    rintro rfl
    have htriv : ∀ y ∈ Q, M₀.π (s * y * s⁻¹) = M₀.π y := by
      intro y hy
      apply T.injective
      rw [← hTpi _ (hsQ y hy), ← hTpi y hy]
      apply φ.injective
      have e : m * (s * y * s⁻¹) * m⁻¹ =
          m * s * m⁻¹ * (m * y * m⁻¹) * (m * s * m⁻¹)⁻¹ := by group
      rw [e, hsg' _ (hmQ y hy), orthTensor_one_id]
    refine hg1 (eq_one_of_orthTensor_eq_self (ι := ι) fun p => ?_)
    obtain ⟨y, hy, rfl⟩ := exists_mem_phi_pi (M₀ := M₀) (φ := φ) p
    rw [← hsg y hy, htriv y hy]
  exact (pure_iff_exists_fix _).mp ⟨g', hg'det, hg'1, hfix⟩

theorem qU_eq_zero_of_pure (hcB : Ctx M Q Z B) (hcA : Ctx M Q Z A)
    (hno : NoA2 Q Z (LB M Q A)) (hLA : LB M Q A ≤ Lgen M (LB M Q B))
    (hD : GlobalModelData M Q Z γ M₀) (hF : OrthPreFrame Q Z M₀ qU φ)
    (hAct : OrthAct Q Z M₀ qU φ (Lgen M (LB M Q B))) (hn : 4 ≤ Fintype.card ι)
    {a : G} (haA : a ∈ A) (ha1 : a ≠ 1) {c : Fin 2 → K} {v : ι → K} (hc : c ≠ 0) (hv : v ≠ 0)
    (hpa : φ (M₀.π a) = (c 0 • v, c 1 • v)) : qU v = 0 := by
  obtain ⟨h, hdet, hh⟩ := exists_SL_mulVec_eq c hc
  have hpa' : (φ.trans (orthTensorEquiv h)) (M₀.π a) = (v, 0) := by
    rw [LinearEquiv.trans_apply, hpa, orthTensorEquiv_apply, orthTensor_pure_apply, hh]
    simp
  exact qU_eq_zero_of_root_std hcB hcA hno hLA hD (hF.change hdet) (hAct.change hdet) hn hv haA
    ha1 hpa'

theorem pairTypeA_of_isConj (hcB : Ctx M Q Z B)
    (hconj : ∀ C : Subgroup G, Ctx M Q Z C → ∃ m ∈ M, C = conjSubgroup m B)
    (hno : ∀ C : Subgroup G, Ctx M Q Z C → NoA2 Q Z (LB M Q C))
    (hD : GlobalModelData M Q Z γ M₀) (hF : OrthPreFrame Q Z M₀ qU φ)
    (hAct : OrthAct Q Z M₀ qU φ (Lgen M (LB M Q B)))
    (hN : ∀ s ∈ Lgen M (LB M Q B), ∀ g : Matrix (Fin 2) (Fin 2) K, g.det = 1 →
      ActsAsTensor Q Z M₀ φ s g id → ∀ x ∈ M, ∃ g' : Matrix (Fin 2) (Fin 2) K, g'.det = 1 ∧
        ActsAsTensor Q Z M₀ φ (x * s * x⁻¹) g' id)
    (hn : 4 ≤ Fintype.card ι) {c₀ : Fin 2 → K} {u₀ : ι → K}
    (hBimg : ∀ e ∈ M₀.img B, ∃ k : K, φ e = k • (c₀ 0 • u₀, c₀ 1 • u₀))
    {z : G} (hz : z ∈ Z) {x : G} (hxQ : x ∈ Q) (hxZ : x ∉ Z) (hx : IsConj z x) :
    PairTypeA qU (φ (M₀.π x)) := by
  have : Nonempty ι := Fintype.card_pos_iff.mp (by omega)
  obtain ⟨w, hw⟩ := isConj_iff.mp hx
  obtain ⟨g, hgQ, hxC⟩ := stroth_2_6 hcB.hyp hxQ hxZ ⟨w, z, hz, hw.symm⟩
  have hcC : Ctx M Q Z (conjSubgroup g Z) :=
    ⟨hcB.hyp, ⟨g, rfl⟩, hgQ, fun h => hxZ (h ▸ hxC)⟩
  obtain ⟨m, hm, hCm⟩ := hconj _ hcC
  obtain ⟨c, v, hcv⟩ :=
    exists_pure_of_mem_conj hcB hD hAct hN hBimg hm (hCm ▸ hxC) hxQ
  have hx0 : φ (M₀.π x) ≠ 0 := by
    intro h0
    exact hxZ ((M₀.π_ker x hxQ).mp (by simpa using h0))
  have hc : c ≠ 0 := by
    rintro rfl
    exact hx0 (by simp [hcv])
  have hv : v ≠ 0 := by
    rintro rfl
    exact hx0 (by simp [hcv])
  have hx1 : x ≠ 1 := by
    rintro rfl
    exact hxZ (one_mem Z)
  have hqv : qU v = 0 :=
    qU_eq_zero_of_pure hcB hcC (hno _ hcC) (LB_le_Lgen_of_eq_conj hcB hm hCm) hD hF hAct hn hxC
      hx1 hc hv hcv
  have hc' : c 0 ≠ 0 ∨ c 1 ≠ 0 := by
    by_contra h
    push_neg at h
    exact hc (funext fun i => by fin_cases i <;> simp [h.1, h.2])
  exact ⟨c 0, c 1, v, hc', hv, hqv, hcv⟩

theorem qU_eq_zero_of_img_eq (hcB : Ctx M Q Z B) (hno : NoA2 Q Z (LB M Q B))
    (hD : GlobalModelData M Q Z γ M₀) (hF : OrthPreFrame Q Z M₀ qU φ)
    (hAct : OrthAct Q Z M₀ qU φ (Lgen M (LB M Q B))) (hn : 4 ≤ Fintype.card ι)
    {c₀ : Fin 2 → K} {u₀ : ι → K} (hc₀ : c₀ ≠ 0) (hu₀ : u₀ ≠ 0)
    (hBimg : ∀ e : M₀.E, e ∈ M₀.img B ↔ ∃ k : K, φ e = k • (c₀ 0 • u₀, c₀ 1 • u₀)) :
    qU u₀ = 0 := by
  have hp : φ.symm (c₀ 0 • u₀, c₀ 1 • u₀) ∈ M₀.img B :=
    (hBimg _).mpr ⟨1, by rw [LinearEquiv.apply_symm_apply, one_smul]⟩
  obtain ⟨b, hb, hbQ, hbe⟩ := M₀.mem_img.mp hp
  have hpb : φ (M₀.π b) = (c₀ 0 • u₀, c₀ 1 • u₀) := by
    rw [hbe, LinearEquiv.apply_symm_apply]
  have hb1 : b ≠ 1 := by
    rintro rfl
    rw [M₀.pi_one, map_zero] at hpb
    have h0 : (c₀ 0 • u₀, c₀ 1 • u₀) = ((0 : ι → K), (0 : ι → K)) := hpb.symm
    have hc0 : c₀ 0 = 0 := by
      by_contra h
      exact hu₀ ((smul_eq_zero.mp (congrArg Prod.fst h0)).resolve_left h)
    have hc1 : c₀ 1 = 0 := by
      by_contra h
      exact hu₀ ((smul_eq_zero.mp (congrArg Prod.snd h0)).resolve_left h)
    exact hc₀ (funext fun i => by fin_cases i <;> simp [hc0, hc1])
  exact qU_eq_zero_of_pure hcB hcB hno (le_Lgen_self M (LB M Q B)) hD hF hAct hn hb hb1 hc₀ hu₀
    hpb

theorem orthFrame_of_tensor (hcB : Ctx M Q Z B)
    (hconj : ∀ C : Subgroup G, Ctx M Q Z C → ∃ m ∈ M, C = conjSubgroup m B)
    (hno : ∀ C : Subgroup G, Ctx M Q Z C → NoA2 Q Z (LB M Q C))
    (hD : GlobalModelData M Q Z γ M₀) (hF : OrthPreFrame Q Z M₀ qU φ)
    (hAct : OrthAct Q Z M₀ qU φ (Lgen M (LB M Q B)))
    (hN : ∀ s ∈ Lgen M (LB M Q B), ∀ g : Matrix (Fin 2) (Fin 2) K, g.det = 1 →
      ActsAsTensor Q Z M₀ φ s g id → ∀ x ∈ M, ∃ g' : Matrix (Fin 2) (Fin 2) K, g'.det = 1 ∧
        ActsAsTensor Q Z M₀ φ (x * s * x⁻¹) g' id)
    (hn : 4 ≤ Fintype.card ι) {c₀ : Fin 2 → K} {u₀ : ι → K} (hc₀ : c₀ ≠ 0) (hu₀ : u₀ ≠ 0)
    (hBimg : ∀ e : M₀.E, e ∈ M₀.img B ↔ ∃ k : K, φ e = k • (c₀ 0 • u₀, c₀ 1 • u₀)) :
    OrthFrame Q Z M₀ qU φ := by
  have hqu₀ : qU u₀ = 0 := qU_eq_zero_of_img_eq hcB (hno B hcB) hD hF hAct hn hc₀ hu₀ hBimg
  refine ⟨hF.nondeg, hF.qf, fun z hz hz1 x hxQ hxZ => ⟨fun hx => ?_, fun hx => ?_⟩⟩
  · exact pairTypeA_of_isConj hcB hconj hno hD hF hAct hN hn (fun e he => (hBimg e).mp he) hz
      hxQ hxZ hx
  · exact isConj_of_pairTypeA hcB hD hF hAct hn ⟨c₀, u₀, hc₀, hu₀, hqu₀, hBimg⟩ hz hz1 hxQ hxZ hx

end CFSG.RankThree.GF2n.Smith81
