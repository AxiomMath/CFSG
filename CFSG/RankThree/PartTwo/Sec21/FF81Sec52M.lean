module

public import CFSG.RankThree.PartTwo.Sec21.FF81Sec52C
import CFSG.RankThree.PartTwo.Sec21.FF81Sec53
import CFSG.RankThree.PartTwo.Sec21.FF81Sec54

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

@[expose] public section

namespace CFSG.RankThree.PartTwo.Sec21.FF81

open CFSG.RankThree.PartTwo.Sec21.FF79 Matrix
open P51 (V e)

namespace S52

def ft (v : V) : V := ![-v 0, v 1, v 2, v 3]

def fs (v : V) : V := ![v 1, v 0, v 2, v 3]

def fr (v : V) : V := v + (v 0 + v 1 + v 2 + v 3) • ![1, 1, 1, 1]

def uv : Fin 3 → V := ![![1, 1, 0, 0], ![1, 2, 0, 0], ![0, 0, 1, 1]]

def ffv : Fin 6 → V :=
  ![![1, 1, 0, 0], ![2, 2, 0, 0], ![1, 2, 0, 0], ![2, 1, 0, 0], ![0, 0, 1, 1], ![0, 0, 2, 2]]

theorem sig01_mulVec (v : V) : P51.Sig01 *ᵥ v = fs v := by
  ext i; fin_cases i <;> simp [P51.Sig01, mulVec, dotProduct, Fin.sum_univ_four, fs]

theorem refl_mulVec (w ψ v : V) : (1 + vecMulVec w ψ) *ᵥ v = v + (ψ ⬝ᵥ v) • w := by
  rw [add_mulVec, one_mulVec, vecMulVec_mulVec, op_smul_eq_smul]

theorem refl6_eq (v : V) : v + (![1, 1, 1, 1] ⬝ᵥ v) • P51.rep 6 = fr v := by
  simp [fr, P51.rep, dotProduct, Fin.sum_univ_four]

set_option maxRecDepth 100000 in
theorem psi6 : ∀ ψ ∈ P51.okL 6, ∀ m ∈ [P51.mB, P51.mC],
    (∀ v : V, v ≠ 0 → m (P51.orbOf v) = true →
      m (P51.orbOf (v + (ψ ⬝ᵥ v) • P51.rep 6)) = true) → ψ = ![1, 1, 1, 1] := by
  decide +kernel

open P51T P51 in
theorem setup {G : Type} [Group G] [Finite G] {b : G}
    {L B : Subgroup G} {b₁ b₂ b₃ : G} (hB : FF81Basis b L B b₁ b₂ b₃)
    (hII : (ConjLines B b).ncard = 12 ∨ (ConjLines B b).ncard = 24) :
    ∃ m : Fin 7 → Bool, (m = mB ∨ m = mC) ∧
      (∀ v : V, v ≠ 0 →
        (Subgroup.zpowers (S36.ε4 b b₁ b₂ b₃ v) ∈ ConjLines B b ↔ m (orbOf v) = true)) ∧
      (∃ n : G, ∀ v, n * S36.ε4 b b₁ b₂ b₃ v * n⁻¹ = S36.ε4 b b₁ b₂ b₃ (fs v)) ∧
      (∃ n : G, ∀ v, n * S36.ε4 b b₁ b₂ b₃ v * n⁻¹ = S36.ε4 b b₁ b₂ b₃ (fr v)) := by
  obtain ⟨hE, hcl, -⟩ := hB.mono
  haveI : IsElementaryAbelian 3 B := hE.1
  obtain ⟨β, hβ⟩ := exists_basis (B := B) hE.2 hcl
  set bs : Fin 4 → G := ![b, b₁, b₂, b₃] with hbs
  have hbB : ∀ i, bs i ∈ B := fun i => hβ i ▸ (Additive.toMul (β i)).2
  have hcol : ∀ (n : G) (hn : n ∈ Nor B) (i : Fin 4),
      ρM β ⟨n, hn⟩ *ᵥ e i = cvG β (n * bs i * n⁻¹) := fun n hn i => by
    rw [ρM_col, hβ i]
  have hconj : ∀ n ∈ Nor B, ∀ x ∈ B, n * x * n⁻¹ ∈ B := fun n hn x hx =>
    (Subgroup.mem_normalizer_iff.mp hn x).mp hx
  set Γ := (ρU β).range with hΓdef
  have hΓ : ∀ g ∈ Γ, ∃ (n : G) (hn : n ∈ Nor B), (g : Mat) = ρM β ⟨n, hn⟩ := by
    rintro g ⟨⟨n, hn⟩, rfl⟩
    exact ⟨n, hn, rfl⟩
  have hρΓ : ∀ (n : G) (hn : n ∈ Nor B), ρU β ⟨n, hn⟩ ∈ Γ := fun n hn => ⟨_, rfl⟩
  have hzp : ∀ n : G, conjBy n (Subgroup.zpowers b) = Subgroup.zpowers (n * b * n⁻¹) := by
    intro n
    rw [conjBy, MonoidHom.map_zpowers]
    rfl
  have hyp : Hyp Γ := hyp_of hB.mono hB.stab hB.meet β hβ
  have homneg : ∀ v ∈ Om Γ, -v ∈ Om Γ := by
    rintro v ⟨g, hg, rfl⟩
    obtain ⟨t, ht, htT⟩ := hyp.t0
    refine ⟨g * t, Γ.mul_mem hg ht, ?_⟩
    rw [Units.val_mul, ← Matrix.mulVec_mulVec, htT, T0_e0, Matrix.mulVec_neg]
  have hlines : {D | ∃ n ∈ Nor B, conjBy n (Subgroup.zpowers b) = D} = Lv β '' Om Γ := by
    ext D
    constructor
    · rintro ⟨n, hn, rfl⟩
      refine ⟨ρM β ⟨n, hn⟩ *ᵥ e 0, ⟨_, hρΓ n hn, rfl⟩, ?_⟩
      rw [hcol, Lv, hzp, cvG_of_mem β (hconj n hn _ (hbB 0)), vB_cv]
      rfl
    · rintro ⟨v, ⟨g, hg, rfl⟩, rfl⟩
      obtain ⟨n, hn, hgn⟩ := hΓ g hg
      refine ⟨n, hn, ?_⟩
      rw [hgn, hcol, Lv, hzp, cvG_of_mem β (hconj n hn _ (hbB 0)), vB_cv]
      rfl
  have hCL : ConjLines B b = {D | ∃ n ∈ Nor B, conjBy n (Subgroup.zpowers b) = D} := by
    ext D
    constructor
    · exact fun hD => hB.fus D hD
    · rintro ⟨n, hn, rfl⟩
      refine ⟨?_, n, rfl⟩
      rw [hzp, Subgroup.zpowers_le]
      exact hconj n hn b (hbB 0)
  have hncard : (ConjLines B b).ncard = lineCount (cfgOf Γ).1 := by
    rw [hCL, hlines]
    have himg : Lv β '' Om Γ = Lv β '' (Om Γ ∩ {v | pos v = true}) := by
      apply le_antisymm
      · rintro _ ⟨v, hv, rfl⟩
        have hn := mem_nonzeroL _ (ne_zero_of_mem_Om hv)
        rcases pos_or v hn with hp | hp
        · exact ⟨v, ⟨hv, hp⟩, rfl⟩
        · exact ⟨-v, ⟨homneg v hv, hp⟩, Lv_neg β v⟩
      · exact Set.image_mono Set.inter_subset_left
    have hinj : Set.InjOn (Lv β) (Om Γ ∩ {v | pos v = true}) := by
      rintro v ⟨hv, hpv⟩ w ⟨hw, hpw⟩ hvw
      rcases Lv_eq β (ne_zero_of_mem_Om hw) hvw with h | h
      · exact h.symm
      · exfalso
        exact not_pos_and v (mem_nonzeroL _ (ne_zero_of_mem_Om hv)) ⟨hpv, h ▸ hpw⟩
    rw [himg, hinj.ncard_image, lineCount]
    have : Om Γ ∩ {v | pos v = true} =
        ↑((nonzeroL.filter fun v => (cfgOf Γ).1 (tab v).1 && pos v).toFinset) := by
      ext v
      simp only [Set.mem_inter_iff, Set.mem_setOf_eq, om_iff hyp, List.coe_toFinset,
        List.mem_filter, Bool.and_eq_true]
      tauto
    rw [this, Set.ncard_coe_finset]
  have hm : ((cfgOf Γ).1 = mB ∨ (cfgOf Γ).1 = mC) ∧ W (cfgOf Γ) := by
    rcases cfgOf_good hyp with h | ⟨h, hW⟩ | ⟨h, hW⟩ | h | h
    · rw [h, lineCount_mA] at hncard; rcases hII with h' | h' <;> omega
    · exact ⟨Or.inl h, hW⟩
    · exact ⟨Or.inr h, hW⟩
    · rw [h, lineCount_mD] at hncard; rcases hII with h' | h' <;> omega
    · rw [h, lineCount_mE] at hncard; rcases hII with h' | h' <;> omega
  have hact : ∀ g ∈ Γ, ∃ n : G, ∀ v, n * S36.ε4 b b₁ b₂ b₃ v * n⁻¹ =
      S36.ε4 b b₁ b₂ b₃ ((g : Mat) *ᵥ v) := by
    intro g hg
    obtain ⟨n, hn, hgn⟩ := hΓ g hg
    refine ⟨n, fun v => ?_⟩
    have hx := S36.ε4_mem hcl v
    refine cvG_inj β (hconj n hn _ hx) (S36.ε4_mem hcl _) ?_
    rw [S36.cvG_ε4 β hβ, hgn, cvG_of_mem β (hconj n hn _ hx),
      show (⟨n * S36.ε4 b b₁ b₂ b₃ v * n⁻¹, hconj n hn _ hx⟩ : B) =
        conjB ⟨n, hn⟩ ⟨_, hx⟩ from rfl, ← ρM_mulVec, ← cvG_of_mem β hx, S36.cvG_ε4 β hβ]
  refine ⟨(cfgOf Γ).1, hm.1, fun v hv => ?_, ?_, ?_⟩
  · have hLv : Subgroup.zpowers (S36.ε4 b b₁ b₂ b₃ v) = Lv β v := by
      rw [Lv, S36.ε4_eq_vB β hβ]
    rw [hLv, hCL, hlines]
    constructor
    · rintro ⟨w, hw, hwv⟩
      rcases Lv_eq β (ne_zero_of_mem_Om hw) hwv.symm with h | h
      · rw [← h]; exact ((om_iff hyp w).1 hw).2
      · have := (om_iff hyp (-w)).1 (homneg w hw)
        rw [show -w = v by rw [h, neg_neg]] at this
        exact this.2
    · intro h
      exact ⟨v, (om_iff hyp v).2 ⟨mem_nonzeroL v hv, h⟩, rfl⟩
  · obtain ⟨g, hg, hgS⟩ := mem_GM.1 (sig01_of_W hyp hm.2)
    obtain ⟨n, hn⟩ := hact g hg
    exact ⟨n, fun v => by rw [hn, hgS, sig01_mulVec]⟩
  · have h6 : (cfgOf Γ).1 6 = true := by rcases hm.1 with h | h <;> rw [h] <;> rfl
    have hrep : rep 6 ∈ Om Γ := (om_iff hyp _).2 ⟨mem_nonzeroL _ (rep_ne_zero 6), by
      rw [tab_rep]; exact h6⟩
    obtain ⟨ψ, hψ⟩ := real_of_mem hrep
    obtain ⟨r, hr, hr1, -⟩ := real_refl hyp hψ
    have hinv : ∀ v : V, v ≠ 0 → (cfgOf Γ).1 (orbOf v) = true →
        (cfgOf Γ).1 (orbOf (v + (ψ ⬝ᵥ v) • rep 6)) = true := by
      intro v hv hmv
      have hvO : v ∈ Om Γ := (om_iff hyp v).2 ⟨mem_nonzeroL v hv, hmv⟩
      obtain ⟨g, hg, rfl⟩ := hvO
      have : (r : Mat) *ᵥ ((g : Mat) *ᵥ e 0) ∈ Om Γ :=
        ⟨r * g, Γ.mul_mem hr hg, by rw [Units.val_mul, ← Matrix.mulVec_mulVec]⟩
      rw [hr1, refl_mulVec] at this
      exact ((om_iff hyp _).1 this).2
    have hψ1 := psi6 ψ (ok_rep 6 ψ (mem_allV ψ) (real_dot hψ) (real_ok hyp hψ)) _
      (by rcases hm.1 with h | h <;> rw [h] <;> simp) hinv
    obtain ⟨n, hn⟩ := hact r hr
    exact ⟨n, fun v => by rw [hn, hr1, refl_mulVec, hψ1, refl6_eq]⟩

end S52

variable {G : Type} [Group G] [Finite G] {b : G} {L B : Subgroup G} {b₁ b₂ b₃ t₀ s₀ : G}

theorem FF81Sec5.setup (h5 : FF81Sec5 b L B b₁ b₂ b₃ t₀ s₀) :
    ∃ m : Fin 7 → Bool, (m = P51.mB ∨ m = P51.mC) ∧
      (∀ v : V, v ≠ 0 →
        (Subgroup.zpowers (h5.ε v) ∈ ConjLines B b ↔ m (P51.orbOf v) = true)) ∧
      (∃ n : G, ∀ v, n * h5.ε v * n⁻¹ = h5.ε (S52.fs v)) ∧
      (∃ n : G, ∀ v, n * h5.ε v * n⁻¹ = h5.ε (S52.fr v)) :=
  S52.setup h5.basis (by rcases h5.caseII with h | h; exacts [Or.inl h.2.2.1, Or.inr h.2.2.1])

theorem FF81Sec5.t₀_ε (h5 : FF81Sec5 b L B b₁ b₂ b₃ t₀ s₀) (v : V) :
    t₀ * h5.ε v * t₀⁻¹ = h5.ε (S52.ft v) := by
  have hc : ∀ x ∈ L, t₀ * x * t₀⁻¹ = x := fun x hx => by
    rw [← Subgroup.mem_centralizer_iff.mp h5.ht₀L x hx, mul_inv_cancel_right]
  have h0 : t₀ * b * t₀⁻¹ = h5.ε (-(e 0)) := by rw [h5.ε_neg, h5.ε_e0, h5.ht₀b]
  rw [ε4_conj h5.hE h5.hcl ![-(e 0), e 1, e 2, e 3] h0
    ((hc _ h5.basis.hb₁).trans h5.ε_e1.symm) ((hc _ h5.basis.hb₂).trans h5.ε_e2.symm)
    ((hc _ h5.basis.hb₃).trans h5.ε_e3.symm)]
  congr 1
  ext j; fin_cases j <;> simp [e, Pi.single_apply, S52.ft]

theorem FF81Sec5.lift (hKF : KF_Sp6Levi) (h5 : FF81Sec5 b L B b₁ b₂ b₃ t₀ s₀) {n : G}
    {f : V → V} (hn : ∀ v, n * h5.ε v * n⁻¹ = h5.ε (f v)) (hA : ∀ v : V, v 2 = v 3 → f v 2 = f v 3)
    (hβ : f ![0, 0, 1, 2] = ![0, 0, 1, 2]) :
    ∃ h ∈ H₅₂ b b₁ b₂ b₃ s₀, ∀ v, h * h5.ε v * h⁻¹ = h5.ε (f v) := by
  have hnA : n ∈ Nor (A₁sub b b₁ b₂ b₃) := Subgroup.mem_normalizer_fintype fun x hx => by
    obtain ⟨v, hv, rfl⟩ := h5.coord_of_mem_A₁ hx
    rw [hn]; exact h5.mem_A₁_of (hA v hv)
  have hnβ : n * β' b₂ b₃ * n⁻¹ = β' b₂ b₃ := by rw [← h5.ε_β, hn, hβ]
  obtain ⟨k, hk⟩ := h5.exists_mem_H hKF hnA hnβ
  refine ⟨_, hk, fun v => ?_⟩
  have hc := h5.basis.B_comm (B.pow_mem h5.β_mem k) (h5.ε_mem (f v))
  calc β' b₂ b₃ ^ k * n * h5.ε v * (β' b₂ b₃ ^ k * n)⁻¹
      = β' b₂ b₃ ^ k * (n * h5.ε v * n⁻¹) * (β' b₂ b₃ ^ k)⁻¹ := by group
    _ = h5.ε (f v) := by rw [hn, hc, mul_inv_cancel_right]

theorem FF81Sec5.ε_uv (h5 : FF81Sec5 b L B b₁ b₂ b₃ t₀ s₀) :
    h5.ε (S52.uv 0) = b * b₁ ∧ h5.ε (S52.uv 1) = b * b₁ ^ 2 ∧ h5.ε (S52.uv 2) = b₂ * b₃ := by
  refine ⟨?_, ?_, ?_⟩ <;>
  · rw [show S52.uv _ = ![_, _, _, _] from rfl, FF81Sec5.ε_lit]
    simp only [ZMod.val_zero, pow_zero, mul_one, one_mul, show (1 : ZMod 3).val = 1 from rfl,
      show (2 : ZMod 3).val = 2 from rfl, pow_one]

theorem FF81Sec5.ε_ffv_mem (h5 : FF81Sec5 b L B b₁ b₂ b₃ t₀ s₀) (j : Fin 6) :
    h5.ε (S52.ffv j) ∈ ({b * b₁, (b * b₁)⁻¹, b * b₁ ^ 2, (b * b₁ ^ 2)⁻¹, b₂ * b₃, (b₂ * b₃)⁻¹} :
      Set G) := by
  obtain ⟨h0, h1, h2⟩ := h5.ε_uv
  fin_cases j
  · change h5.ε (S52.ffv 0) ∈ _
    rw [show S52.ffv 0 = S52.uv 0 from rfl, h0]; simp
  · change h5.ε (S52.ffv 1) ∈ _
    rw [show S52.ffv 1 = -S52.uv 0 by decide, h5.ε_neg, h0]; simp
  · change h5.ε (S52.ffv 2) ∈ _
    rw [show S52.ffv 2 = S52.uv 1 from rfl, h1]; simp
  · change h5.ε (S52.ffv 3) ∈ _
    rw [show S52.ffv 3 = -S52.uv 1 by decide, h5.ε_neg, h1]; simp
  · change h5.ε (S52.ffv 4) ∈ _
    rw [show S52.ffv 4 = S52.uv 2 from rfl, h2]; simp
  · change h5.ε (S52.ffv 5) ∈ _
    rw [show S52.ffv 5 = -S52.uv 2 by decide, h5.ε_neg, h2]; simp

set_option maxRecDepth 100000 in
theorem S52.mono_key : ∀ m ∈ [P51.mB, P51.mC], ∀ i : Fin 3, ∀ y : V, y 2 = y 3 → y ≠ 0 →
    m (P51.orbOf (y + ![0, 0, 1, 2])) = true →
    (m (P51.orbOf (S52.uv i)) = true → m (P51.orbOf y) = true) → ∃ j : Fin 6, y = S52.ffv j := by
  decide +kernel

theorem FF81Sec5.monomial (hKF : KF_Sp6Levi)
    (h5 : FF81Sec5 b L B b₁ b₂ b₃ t₀ s₀) {h : G} (hh : h ∈ H₅₂ b b₁ b₂ b₃ s₀) (i : Fin 3) :
    ∃ j : Fin 6, h * h5.ε (S52.uv i) * h⁻¹ = h5.ε (S52.ffv j) := by
  obtain ⟨m, hm, hiff, -, -⟩ := h5.setup
  have hmL : m ∈ [P51.mB, P51.mC] := by rcases hm with rfl | rfl <;> simp
  have hNA := hh.2
  have hNB := h5.nor_A₁_le_nor_B hKF hNA
  have hβc : h * β' b₂ b₃ * h⁻¹ = β' b₂ b₃ := by
    rw [(mem_cenS_pair_iff.mp hh.1).1, mul_inv_cancel_right]
  have hui : S52.uv i 2 = S52.uv i 3 := by fin_cases i <;> rfl
  have hu0 : S52.uv i ≠ 0 := by fin_cases i <;> decide
  have hy : h * h5.ε (S52.uv i) * h⁻¹ ∈ A₁sub b b₁ b₂ b₃ :=
    (Subgroup.mem_normalizer_iff.mp hNA _).mp (h5.mem_A₁_of hui)
  obtain ⟨y, hy23, hyε⟩ := h5.coord_of_mem_A₁ hy
  have hy0 : y ≠ 0 := by
    rintro rfl
    rw [h5.ε_zero] at hyε
    exact hu0 (h5.ε_eq_one (conj_eq_one_iff.mp hyε.symm))
  have hne : ∀ y : V, y 2 = y 3 → y + ![0, 0, 1, 2] ≠ 0 := by decide
  have hβl : Subgroup.zpowers (h5.ε (y + ![0, 0, 1, 2])) ∈ ConjLines B b := by
    have h1 : Subgroup.zpowers (h5.ε (S52.uv i + ![0, 0, 1, 2])) ∈ ConjLines B b :=
      (hiff _ (hne _ hui)).2 (by rcases hm with rfl | rfl <;> fin_cases i <;> rfl)
    have h2 := S36.conjLines_conj hNB h1
    rwa [h5.ε_add, h5.ε_β, show h * (h5.ε (S52.uv i) * β' b₂ b₃) * h⁻¹ =
      (h * h5.ε (S52.uv i) * h⁻¹) * (h * β' b₂ b₃ * h⁻¹) by group, hβc, ← hyε, ← h5.ε_β,
      ← h5.ε_add] at h2
  have hmy := (hiff _ (hne y hy23)).1 hβl
  have hmu : m (P51.orbOf (S52.uv i)) = true → m (P51.orbOf y) = true := fun hmu => by
    refine (hiff y hy0).1 ?_
    rw [hyε]
    exact S36.conjLines_conj hNB ((hiff _ hu0).2 hmu)
  obtain ⟨j, hj⟩ := S52.mono_key m hmL i y hy23 hy0 hmy hmu
  exact ⟨j, by rw [← hyε, hj]⟩

end CFSG.RankThree.PartTwo.Sec21.FF81
