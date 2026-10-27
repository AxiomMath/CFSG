module

public import CFSG.RankThree.GF2n.Smith81.OrthE2PlusTwo
public import CFSG.RankThree.GF2n.Smith81.OrthE2Two

public section

open scoped Matrix commutatorElement

namespace CFSG.RankThree.GF2n.Smith81

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Stroth80

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}
  {K : Type} [Field K] [Finite K] [CharP K 2] {γ : G → K} {M₀ : Tim79.QuadModel Q Z K γ}
  {ι : Type} [Fintype ι] [DecidableEq ι] {qU : QuadraticForm K (ι → K)}
  {φ : M₀.E ≃ₗ[K] (ι → K) × (ι → K)}

theorem exists_pure_of_mem_conj_fixer (hcB : Ctx M Q Z B) (hD : GlobalModelData M Q Z γ M₀)
    (hLfix : ∀ s ∈ LB M Q B, ∀ b ∈ B, M₀.π (s * b * s⁻¹) = M₀.π b)
    (hN : ∀ x ∈ M, ∃ s ∈ LB M Q B, s ∉ Q ∧ ∃ g' : Matrix (Fin 2) (Fin 2) K, g'.det = 1 ∧
      ActsAsTensor Q Z M₀ φ (x * s * x⁻¹) g' id)
    {m : G} (hm : m ∈ M) {x : G} (hx : x ∈ conjSubgroup m B) (hxQ : x ∈ Q) :
    ∃ (c : Fin 2 → K) (v : ι → K), φ (M₀.π x) = (c 0 • v, c 1 • v) := by
  classical
  obtain ⟨s, hsLB, hsQ', g', hg'det, hsg'⟩ := hN m hm
  have hsM : s ∈ M := hcB.LB_le_M hsLB
  have hsQ := (hcB.conj_mem_Q_of_mem_M hsM).1
  have hmQ := (hcB.conj_mem_Q_of_mem_M hm).1
  obtain ⟨σ, a, T, -, hTpi, -, -⟩ := hD.act m hm
  have hb : m⁻¹ * x * m ∈ B := mem_conjSubgroup.mp hx
  set b := m⁻¹ * x * m with hbdef
  have hxb : x = m * b * m⁻¹ := by rw [hbdef]; group
  have hbQ : b ∈ Q := hcB.le hb
  have hsb : M₀.π (s * b * s⁻¹) = M₀.π b := hLfix s hsLB b hb
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
    exact hsQ' (mem_Q_of_pi_conj_eq (M₀ := M₀) hcB.hyp hsM htriv)
  exact (pure_iff_exists_fix _).mp ⟨g', hg'det, hg'1, hfix⟩

theorem pairTypeA_of_isConj_fixer (hcB : Ctx M Q Z B)
    (hconj : ∀ C : Subgroup G, Ctx M Q Z C → ∃ m ∈ M, C = conjSubgroup m B)
    (hno : ∀ C : Subgroup G, Ctx M Q Z C → NoA2 Q Z (LB M Q C))
    (hD : GlobalModelData M Q Z γ M₀) (hF : OrthPreFrame Q Z M₀ qU φ)
    (hAct : OrthAct Q Z M₀ qU φ (Lgen M (LB M Q B)))
    (hLfix : ∀ s ∈ LB M Q B, ∀ b ∈ B, M₀.π (s * b * s⁻¹) = M₀.π b)
    (hN : ∀ x ∈ M, ∃ s ∈ LB M Q B, s ∉ Q ∧ ∃ g' : Matrix (Fin 2) (Fin 2) K, g'.det = 1 ∧
      ActsAsTensor Q Z M₀ φ (x * s * x⁻¹) g' id)
    (hn : 4 ≤ Fintype.card ι) {z : G} (hz : z ∈ Z) {x : G} (hxQ : x ∈ Q) (hxZ : x ∉ Z)
    (hx : IsConj z x) : PairTypeA qU (φ (M₀.π x)) := by
  have : Nonempty ι := Fintype.card_pos_iff.mp (by omega)
  obtain ⟨w, hw⟩ := isConj_iff.mp hx
  obtain ⟨g, hgQ, hxC⟩ := stroth_2_6 hcB.hyp hxQ hxZ ⟨w, z, hz, hw.symm⟩
  have hcC : Ctx M Q Z (conjSubgroup g Z) :=
    ⟨hcB.hyp, ⟨g, rfl⟩, hgQ, fun h => hxZ (h ▸ hxC)⟩
  obtain ⟨m, hm, hCm⟩ := hconj _ hcC
  obtain ⟨c, v, hcv⟩ := exists_pure_of_mem_conj_fixer hcB hD hLfix hN hm (hCm ▸ hxC) hxQ
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
    push Not at h
    exact hc (funext fun i => by fin_cases i <;> simp [h.1, h.2])
  exact ⟨c 0, c 1, v, hc', hv, hqv, hcv⟩

theorem orthFrame_of_tensor_fixer (hcB : Ctx M Q Z B)
    (hconj : ∀ C : Subgroup G, Ctx M Q Z C → ∃ m ∈ M, C = conjSubgroup m B)
    (hno : ∀ C : Subgroup G, Ctx M Q Z C → NoA2 Q Z (LB M Q C))
    (hD : GlobalModelData M Q Z γ M₀) (hF : OrthPreFrame Q Z M₀ qU φ)
    (hAct : OrthAct Q Z M₀ qU φ (Lgen M (LB M Q B)))
    (hLfix : ∀ s ∈ LB M Q B, ∀ b ∈ B, M₀.π (s * b * s⁻¹) = M₀.π b)
    (hN : ∀ x ∈ M, ∃ s ∈ LB M Q B, s ∉ Q ∧ ∃ g' : Matrix (Fin 2) (Fin 2) K, g'.det = 1 ∧
      ActsAsTensor Q Z M₀ φ (x * s * x⁻¹) g' id)
    (hn : 4 ≤ Fintype.card ι) {c₀ : Fin 2 → K} {u₀ : ι → K} (hc₀ : c₀ ≠ 0) (hu₀ : u₀ ≠ 0)
    (hBimg : ∀ e : M₀.E, e ∈ M₀.img B ↔ ∃ k : K, φ e = k • (c₀ 0 • u₀, c₀ 1 • u₀)) :
    OrthFrame Q Z M₀ qU φ := by
  have hqu₀ : qU u₀ = 0 := qU_eq_zero_of_img_eq hcB (hno B hcB) hD hF hAct hn hc₀ hu₀ hBimg
  refine ⟨hF.nondeg, hF.qf, fun z hz hz1 x hxQ hxZ => ⟨fun hx => ?_, fun hx => ?_⟩⟩
  · exact pairTypeA_of_isConj_fixer hcB hconj hno hD hF hAct hLfix hN hn hz hxQ hxZ hx
  · exact isConj_of_pairTypeA hcB hD hF hAct hn ⟨c₀, u₀, hc₀, hu₀, hqu₀, hBimg⟩ hz hz1 hxQ hxZ hx

theorem orth_LB_fix_pi (h34 : Stroth34Statement) (hc : Ctx M Q Z B) {n : ℕ} (hw : Width Q Z n)
    (hn : 2 < n) (hno : NoA2 Q Z (LB M Q B)) (hgen : GenByB M Q B) :
    ∀ s ∈ LB M Q B, ∀ b ∈ B, M₀.π (s * b * s⁻¹) = M₀.π b := by
  have h35 := (stroth_3_5 h34 hc hw hn hno hgen).2.1
  intro s hs b hb
  have hbQ : b ∈ Q := hc.le hb
  have hsM : s ∈ M := hc.LB_le_M hs
  have hbC : b ∈ CQt Q Z (LB M Q B) := by
    rw [h35]
    exact (Subgroup.mem_sup_left hb : b ∈ B ⊔ Z)
  have hcomm : ⁅s, b⁆ ∈ Z := hbC.2 s hs
  have hsbQ : s * b * s⁻¹ ∈ Q := (hc.conj_mem_Q_of_mem_M hsM).1 b hbQ
  have e : s * b * s⁻¹ = ⁅s, b⁆ * b := by
    simp only [commutatorElement_def]
    group
  have hzQ : ⁅s, b⁆ ∈ Q := hc.Z_le_Q hcomm
  rw [e, M₀.π_mul _ hzQ b hbQ, (M₀.π_ker _ hzQ).mpr hcomm, zero_add]

theorem smith24ActE2PlusTwo_holds (h34 : Stroth34Statement) (h310 : Stroth310Statement)
    (hNt : StrothNtStatement) (hG : StrothGenByBStatement) : Smith24ActE2PlusTwoStatement := by
  intro G _ _ M Q Z B t hc ht hE
  have hE' : CaseE2 M Q Z B t 2 := (caseE2_iff M Q Z B t 2).mpr (Or.inl hE)
  have hT := orthTacit_of_caseE2 hc.toCfg hE' hG
  obtain ⟨hno, hgen⟩ := hT B hc.ctx
  have hw : Width Q Z 4 := by
    unfold Width
    rw [hE.2.1]
  obtain ⟨K, _, _, _, γ, M₀, hD, ι, _, _, qU, φ, hF, hAct, ⟨u, hu0, hline⟩, hN⟩ :=
    smith24E2PlusTwo_tensor h34 h310 hNt hc hE hno hgen
  refine ⟨K, inferInstance, inferInstance, inferInstance, γ, M₀, hD, ι, inferInstance,
    inferInstance, qU, φ, ?_, hAct⟩
  have hn : 4 ≤ Fintype.card ι := by
    obtain ⟨n, hw', -, h4⟩ := hc.orth.exists_width
    have hZ : 2 ≤ Nat.card Z := by have := hc.ctx.hyp.q4; omega
    rw [width_eq_of_width hZ (width_of_tensor hD φ) hw']
    exact h4
  exact orthFrame_of_tensor_fixer hc.ctx (fun C hC => exists_mem_M_eq_conj_of_tacit h34 hc hT hC)
    (fun C hC => (hT C hC).1) hD hF hAct (orth_LB_fix_pi h34 hc.ctx hw (by norm_num) hno hgen) hN hn
    (c₀ := ![1, 0]) (fun h => one_ne_zero (congrFun h 0)) hu0 (fun e => by simpa using hline e)

end CFSG.RankThree.GF2n.Smith81
