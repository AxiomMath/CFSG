module

public import CFSG.RankThree.GF2n.Stroth80.Sec53Hbound
public import CFSG.RankThree.GF2n.Stroth80.Sec53CentralizerStmt
public import CFSG.RankThree.GF2n.Stroth80.Sec8StepsConj

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem sec53CentralizerW1_of_decomp_hBC
    (h34 : Stroth34Statement) (hRoot : Stroth310RootStatement) (h51 : Stroth51Statement)
    (hprod : ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B)
      (n : ℕ) (t : G), Sec5Hyp hc n t → SpNat hc t →
      ∀ r ∈ Rt M (LB M Q B) t, HypPlane Q Z B (conjSubgroup r B) t →
        ∀ x ∈ Wt Q (Vone Q B (conjSubgroup r B) (Vt M (LB M Q B) B Z t)),
          ∃ a ∈ QB B ⊓ Wt Q (Vone Q B (conjSubgroup r B) (Vt M (LB M Q B) B Z t)),
          ∃ b ∈ QB (conjSubgroup r B) ⊓
              Wt Q (Vone Q B (conjSubgroup r B) (Vt M (LB M Q B) B Z t)), x = a * b)
    (hBC : ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B)
      (n : ℕ) (t : G), Sec5Hyp hc n t → SpNat hc t →
      ∀ r ∈ Rt M (LB M Q B) t, HypPlane Q Z B (conjSubgroup r B) t →
      ∀ (m : ℕ), SpMNat hc t m →
      ∀ (K : Type) [Field K] [Finite K] [CharP K 2] (γ : G → K)
        (M₀ : Tim79.QuadModel Q Z K γ), GlobalModelData M Q Z γ M₀ →
      ∃ T : Submodule K M₀.E,
        (∀ e : M₀.E, e ∈ T ↔ e ∈ M₀.img (Vt M (LB M Q B) B Z t)) ∧
        Module.finrank K ↥(imgQInfQB M₀ B ⊓
          imgQInfQB M₀ (conjSubgroup r B)) + 1 = 2 * m)
    (hcentC : ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B)
      (n : ℕ) (t : G), Sec5Hyp hc n t → SpNat hc t →
      ∀ r ∈ Rt M (LB M Q B) t, HypPlane Q Z B (conjSubgroup r B) t →
      ∀ d ∈ Q ⊓ QB (conjSubgroup r B),
        (∀ l ∈ (QB (conjSubgroup r B) ⊓ M) ⊓ hc.CN t, ⁅l, d⁆ ∈ Z) →
        d ∈ Vone Q B (conjSubgroup r B) (Vt M (LB M Q B) B Z t)) :
    Sec53CentralizerW1Statement := by
  intro G _ _ M Q Z B hc n t hs hsp0 r hr hplane C N V W₁ V₁ hC hN hV hV₁ hW₁
  subst hC hN hV hV₁ hW₁
  set V : Subgroup G := Vt M (LB M Q B) B Z t with hV
  set V1 : Subgroup G := Vone Q B (conjSubgroup r B) V with hV1
  set W1 : Subgroup G := Wt Q V1 with hW1
  set N : Subgroup G := hc.CN t with hN
  intro y hyW hyZ
  have hrM : r ∈ M := hc.Rt_le_M t hr
  have hcC : Ctx M Q Z (conjSubgroup r B) := hc.conj_of_mem hrM
  obtain ⟨a, haW, b, hbW, hab⟩ := hprod G M Q Z B hc n t hs hsp0 r hr hplane y hyW
  have haQ : a ∈ Q := (inf_le_left : W1 ≤ Q) haW.2
  have haQB : a ∈ QB B := haW.1
  have hbQ : b ∈ Q := (inf_le_left : W1 ≤ Q) hbW.2
  have hbQC : b ∈ QB (conjSubgroup r B) := hbW.1
  have hBinf : B ⊓ QB (conjSubgroup r B) = ⊥ :=
    sec53_sp_B_inf_QB_conj_eq_bot h34 hc hs hsp0 hr hplane
  have hCinfB : conjSubgroup r B ⊓ QB B = ⊥ :=
    sec53_sp_QB_conj_inf_B_eq_bot h34 hc hs hsp0 hr hplane
  have hBZnorm : B ≤ Subgroup.normalizer (Z : Set G) := fun b hb =>
    hc.hyp.Z_normal.2 (hc.Z_le_QB.2 hb)
  have hCZnorm : conjSubgroup r B ≤ Subgroup.normalizer (Z : Set G) := fun c hc' =>
    hc.hyp.Z_normal.2 (hcC.Z_le_QB.2 hc')
  have hBZinf : (Z ⊔ B) ⊓ QB (conjSubgroup r B) = Z := by
    refine le_antisymm ?_ (le_inf le_sup_left hcC.Z_le_QB.1)
    intro x hx
    obtain ⟨hxZB, hxQC⟩ := Subgroup.mem_inf.mp hx
    have hx' : x ∈ ((Z ⊔ B : Subgroup G) : Set G) := hxZB
    rw [Subgroup.coe_mul_of_right_le_normalizer_left Z B hBZnorm] at hx'
    obtain ⟨z, hz, b, hb, rfl⟩ := hx'
    have hzQC : z ∈ QB (conjSubgroup r B) := hcC.Z_le_QB.1 hz
    have hbQC : b ∈ QB (conjSubgroup r B) := by
      have h : z⁻¹ * (z * b) ∈ QB (conjSubgroup r B) :=
        (QB (conjSubgroup r B)).mul_mem ((QB (conjSubgroup r B)).inv_mem hzQC) hxQC
      simpa using h
    have hbBot : b ∈ (⊥ : Subgroup G) := by
      rw [← hBinf]
      exact ⟨hb, hbQC⟩
    rw [Subgroup.mem_bot] at hbBot
    simpa [hbBot] using hz
  have hCZinfB : (Z ⊔ conjSubgroup r B) ⊓ QB B = Z := by
    refine le_antisymm ?_ (le_inf le_sup_left hc.Z_le_QB.1)
    intro x hx
    obtain ⟨hxZC, hxQB⟩ := Subgroup.mem_inf.mp hx
    have hx' : x ∈ ((Z ⊔ conjSubgroup r B : Subgroup G) : Set G) := hxZC
    rw [Subgroup.coe_mul_of_right_le_normalizer_left Z (conjSubgroup r B) hCZnorm] at hx'
    obtain ⟨z, hz, c, hc', rfl⟩ := hx'
    have hzQB : z ∈ QB B := hc.Z_le_QB.1 hz
    have hcQB : c ∈ QB B := by
      have h : z⁻¹ * (z * c) ∈ QB B :=
        (QB B).mul_mem ((QB B).inv_mem hzQB) hxQB
      simpa using h
    have hcBot : c ∈ (⊥ : Subgroup G) := by
      rw [← hCinfB]
      exact ⟨hc', hcQB⟩
    rw [Subgroup.mem_bot] at hcBot
    simpa [hcBot] using hz
  have hdecN : ∀ x ∈ N, ∃ l ∈ LB M Q B ⊓ N,
      ∃ l' ∈ LB M Q (conjSubgroup r B) ⊓ N, x = l * l' := by
    intro x hx
    exact (h51 G M Q Z B hc n t hs (Or.inl hsp0) r hr hplane (conjSubgroup r B)
      (LB M Q B) (LB M Q (conjSubgroup r B)) (hc.CN t) (Rt M (LB M Q B) t)
      rfl rfl rfl rfl rfl).1 x hx
  have hLB : ∀ s ∈ LB M Q B ⊓ N, ⁅s, a⁆ ∈ Z ∧ ⁅s, b⁆ ∈ Z := by
    intro s hsL
    obtain ⟨hsLB, hsN⟩ := Subgroup.mem_inf.mp hsL
    have hsy : ⁅s, y⁆ ∈ Z := hyZ s hsN
    have hsaBZ : ⁅s, a⁆ ∈ (Z ⊔ B : Subgroup G) :=
      hc.comm_LB_inf_QB_mem_sup hsLB ⟨haQ, haQB⟩
    have hsbQC : ⁅s, b⁆ ∈ QB (conjSubgroup r B) := by
      have hnorm := sec52a_QB_inf_normalizes_of_mem_CN hc hs hr hsN
      have hldQC : s * b * s⁻¹ ∈ Q ⊓ QB (conjSubgroup r B) :=
        (Subgroup.mem_normalizer_iff.mp hnorm b).mp ⟨hbQ, hbQC⟩
      simpa only [commutatorElement_def] using
        (QB (conjSubgroup r B)).mul_mem hldQC.2 ((QB (conjSubgroup r B)).inv_mem hbQC)
    have hsbQ : ⁅s, b⁆ ∈ Q := by
      have hsM : s ∈ M := hc.LB_le_M hsLB
      have h1 : s * b * s⁻¹ ∈ Q :=
        (Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 hsM) b).mp hbQ
      simpa only [commutatorElement_def] using Q.mul_mem h1 (Q.inv_mem hbQ)
    have hsbIQC : ⁅s, b⁆ ∈ Q ⊓ QB (conjSubgroup r B) := ⟨hsbQ, hsbQC⟩
    have haNorm : conjSubgroup a (Q ⊓ QB (conjSubgroup r B)) =
        Q ⊓ QB (conjSubgroup r B) := by
      rw [conjSubgroup_inf, hc.conj_Q_eq (hc.hyp.Q_normal.1 haQ), ← QB_conj]
      exact hcC.conj_inf_QB_of_mem_Q haQ
    have haN : a ∈ Subgroup.normalizer
        ((Q ⊓ QB (conjSubgroup r B) : Subgroup G) : Set G) :=
      conjSubgroup_eq_self_iff.mp haNorm
    have hasbQC : a * ⁅s, b⁆ * a⁻¹ ∈ Q ⊓ QB (conjSubgroup r B) :=
      (Subgroup.mem_normalizer_iff.mp haN ⁅s, b⁆).mp hsbIQC
    have hcomm : ⁅s, a * b⁆ = ⁅s, a⁆ * (a * ⁅s, b⁆ * a⁻¹) := by
      rw [commutatorElement_mul_right_eq_mul_conj]
      group
    have hsy' : ⁅s, a * b⁆ ∈ Z := by rwa [hab] at hsy
    have hsaQC : ⁅s, a⁆ ∈ QB (conjSubgroup r B) := by
      have hsa_eq : ⁅s, a⁆ = ⁅s, a * b⁆ * (a * ⁅s, b⁆ * a⁻¹)⁻¹ := by
        rw [hcomm]; group
      rw [hsa_eq]
      exact (QB (conjSubgroup r B)).mul_mem (hcC.Z_le_QB.1 hsy')
        ((QB (conjSubgroup r B)).inv_mem hasbQC.2)
    have hsaZ : ⁅s, a⁆ ∈ Z := by
      have hmem : ⁅s, a⁆ ∈ (Z ⊔ B) ⊓ QB (conjSubgroup r B) := ⟨hsaBZ, hsaQC⟩
      rwa [hBZinf] at hmem
    have hsbZ : ⁅s, b⁆ ∈ Z := by
      have h1 : a * ⁅s, b⁆ * a⁻¹ ∈ Z := by
        have h2 : a * ⁅s, b⁆ * a⁻¹ = ⁅s, a⁆⁻¹ * ⁅s, a * b⁆ := by
          rw [hcomm]; group
        rw [h2]
        exact Z.mul_mem (Z.inv_mem hsaZ) hsy'
      have haM : a ∈ M := hc.hyp.Q_normal.1 haQ
      have hconj : a⁻¹ * (a * ⁅s, b⁆ * a⁻¹) * a ∈ Z := by
        have h := (Subgroup.mem_normalizer_iff.mp
          (hc.hyp.Z_normal.2 (M.inv_mem haM)) (a * ⁅s, b⁆ * a⁻¹)).mp h1
        simpa using h
      have e : a⁻¹ * (a * ⁅s, b⁆ * a⁻¹) * a = ⁅s, b⁆ := by group
      rwa [e] at hconj
    exact ⟨hsaZ, hsbZ⟩
  have hLC : ∀ s ∈ LB M Q (conjSubgroup r B) ⊓ N, ⁅s, a⁆ ∈ Z ∧ ⁅s, b⁆ ∈ Z := by
    intro s hsL
    obtain ⟨hsLC, hsN⟩ := Subgroup.mem_inf.mp hsL
    have hsy : ⁅s, y⁆ ∈ Z := hyZ s hsN
    have hsbCZ : ⁅s, b⁆ ∈ (Z ⊔ conjSubgroup r B : Subgroup G) :=
      hcC.comm_LB_inf_QB_mem_sup hsLC ⟨hbQ, hbQC⟩
    have hsaQB : ⁅s, a⁆ ∈ QB B := by
      have hnorm := sec52a_QB_inf_normalizes_of_mem_CN hc hs (r := 1)
        (Subgroup.one_mem (Rt M (LB M Q B) t)) hsN
      have hnorm' : s ∈ Subgroup.normalizer ((Q ⊓ QB B : Subgroup G) : Set G) := by
        simpa [conjSubgroup_one] using hnorm
      have hldQB : s * a * s⁻¹ ∈ Q ⊓ QB B :=
        (Subgroup.mem_normalizer_iff.mp hnorm' a).mp ⟨haQ, haQB⟩
      simpa only [commutatorElement_def] using
        (QB B).mul_mem hldQB.2 ((QB B).inv_mem haQB)
    have hsaQ : ⁅s, a⁆ ∈ Q := by
      have hsM : s ∈ M := hcC.LB_le_M hsLC
      have h1 : s * a * s⁻¹ ∈ Q :=
        (Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 hsM) a).mp haQ
      simpa only [commutatorElement_def] using Q.mul_mem h1 (Q.inv_mem haQ)
    have hcomm : ⁅s, a * b⁆ = ⁅s, a⁆ * (a * ⁅s, b⁆ * a⁻¹) := by
      rw [commutatorElement_mul_right_eq_mul_conj]
      group
    have hsy' : ⁅s, a * b⁆ ∈ Z := by rwa [hab] at hsy
    have hsbQB : ⁅s, b⁆ ∈ QB B := by
      have h1 : ⁅s, a⁆⁻¹ * ⁅s, a * b⁆ ∈ QB B :=
        (QB B).mul_mem ((QB B).inv_mem hsaQB) (hc.Z_le_QB.1 hsy')
      have e : ⁅s, b⁆ = a⁻¹ * (⁅s, a⁆⁻¹ * ⁅s, a * b⁆) * a := by
        rw [hcomm]; group
      rw [e]
      have h := (Subgroup.mem_normalizer_iff.mp
        (Subgroup.inv_mem _ (Subgroup.le_normalizer haQB))
        (⁅s, a⁆⁻¹ * ⁅s, a * b⁆)).mp h1
      simpa using h
    have hsbZ : ⁅s, b⁆ ∈ Z := by
      have hmem : ⁅s, b⁆ ∈ (Z ⊔ conjSubgroup r B) ⊓ QB B := ⟨hsbCZ, hsbQB⟩
      rwa [hCZinfB] at hmem
    have hsaZ : ⁅s, a⁆ ∈ Z := by
      have hconjZ : a * ⁅s, b⁆ * a⁻¹ ∈ Z :=
        (Subgroup.mem_normalizer_iff.mp
          (hc.hyp.Z_normal.2 (hc.hyp.Q_normal.1 haQ)) _).mp hsbZ
      have h2 : ⁅s, a⁆ = ⁅s, a * b⁆ * (a * ⁅s, b⁆ * a⁻¹)⁻¹ := by
        rw [hcomm]; group
      rw [h2]
      exact Z.mul_mem hsy' (Z.inv_mem hconjZ)
    exact ⟨hsaZ, hsbZ⟩
  have hNZ : ∀ s ∈ N, ⁅s, a⁆ ∈ Z ∧ ⁅s, b⁆ ∈ Z := by
    intro s hsN
    obtain ⟨l, hl, l', hl', hdec⟩ := hdecN s hsN
    have hlM : l ∈ M := hc.LB_le_M hl.1
    have hnorm : l ∈ Subgroup.normalizer (Z : Set G) := hc.hyp.Z_normal.2 hlM
    have h1a : ⁅l, a⁆ ∈ Z := (hLB l hl).1
    have h2a : ⁅l', a⁆ ∈ Z := (hLC l' hl').1
    have h1b : ⁅l, b⁆ ∈ Z := (hLB l hl).2
    have h2b : ⁅l', b⁆ ∈ Z := (hLC l' hl').2
    constructor
    · rw [hdec, commutatorElement_mul_left_eq_conj_mul]
      exact Z.mul_mem ((Subgroup.mem_normalizer_iff.mp hnorm _).mp h2a) h1a
    · rw [hdec, commutatorElement_mul_left_eq_conj_mul]
      exact Z.mul_mem ((Subgroup.mem_normalizer_iff.mp hnorm _).mp h2b) h1b
  have hspC : SpNat hcC t := by
    obtain ⟨K, iF, iFin, hK, m, hm, hrep⟩ := hsp0
    refine ⟨K, iF, iFin, hK, m, hm, ?_⟩
    have hCN : hcC.CN t = hc.CN t := Ctx.CN_conj_left hc hrM t
    have hRt : Rt M (LB M Q (conjSubgroup r B)) t = Rt M (LB M Q B) t := by
      rw [hc.LB_conj hrM]
      exact Rt_conj_left hrM t
    have hVtC : Vt M (LB M Q (conjSubgroup r B)) (conjSubgroup r B) Z t =
        Vt M (LB M Q B) B Z t := by
      rw [hc.LB_conj hrM]
      exact Vt_conj_left (M := M) (L := LB M Q B) (B := B) (Z := Z) hrM t
    rwa [hCN, hRt, hVtC]
  have hCN : hcC.CN t = hc.CN t := Ctx.CN_conj_left hc hrM t
  have hRt : Rt M (LB M Q (conjSubgroup r B)) t = Rt M (LB M Q B) t := by
    rw [hc.LB_conj hrM]
    exact Rt_conj_left hrM t
  have hVtC : Vt M (LB M Q (conjSubgroup r B)) (conjSubgroup r B) Z t =
      Vt M (LB M Q B) B Z t := by
    rw [hc.LB_conj hrM]
    exact Vt_conj_left (M := M) (L := LB M Q B) (B := B) (Z := Z) hrM t
  have haV1 : a ∈ V1 := by
    rw [hV1]
    have hspKeep : SpNat hc t := hsp0
    obtain ⟨K, iF, iFin, hK, m, hm, hrep⟩ := hsp0
    letI := iF
    letI := iFin
    have hVnat : SpMNat hc t m := ⟨K, iF, iFin, hK, hrep⟩
    obtain ⟨K₂, iF₂, iFin₂, iCh₂, γ, M₀, hD⟩ := stroth_globalModelData hc.hyp
    letI := iF₂
    letI := iFin₂
    letI := iCh₂
    obtain ⟨T, hTmem, hBC'⟩ :=
      hBC G M Q Z B hc n t hs hspKeep r hr hplane m hVnat K₂ γ M₀ hD
    exact Ctx.centLam_sp_vone h34 hRoot h51 hc hs hm hVnat hr hplane hD T hTmem hBC'
      a ⟨haQ, haQB⟩ (fun l hl => (hNZ l hl.2).1)
  have hbV1 : b ∈ V1 := by
    rw [hV1]
    exact hcentC G M Q Z B hc n t hs hsp0 r hr hplane b ⟨hbQ, hbQC⟩
      (fun l hl => (hNZ l (by rw [hN]; exact hCN ▸ hl.2)).2)
  rw [hab]
  exact V1.mul_mem haV1 hbV1
theorem sec53CentralizerW1Statement_holds_of_prod_hBC
    (h34 : Stroth34Statement) (hRoot : Stroth310RootStatement) (h51 : Stroth51Statement)
    (hprod : ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B)
      (n : ℕ) (t : G), Sec5Hyp hc n t → SpNat hc t →
      ∀ r ∈ Rt M (LB M Q B) t, HypPlane Q Z B (conjSubgroup r B) t →
        ∀ x ∈ Wt Q (Vone Q B (conjSubgroup r B) (Vt M (LB M Q B) B Z t)),
          ∃ a ∈ QB B ⊓ Wt Q (Vone Q B (conjSubgroup r B) (Vt M (LB M Q B) B Z t)),
          ∃ b ∈ QB (conjSubgroup r B) ⊓
              Wt Q (Vone Q B (conjSubgroup r B) (Vt M (LB M Q B) B Z t)), x = a * b)
    (hBC : ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B)
      (n : ℕ) (t : G), Sec5Hyp hc n t → SpNat hc t →
      ∀ r ∈ Rt M (LB M Q B) t, HypPlane Q Z B (conjSubgroup r B) t →
      ∀ (m : ℕ), SpMNat hc t m →
      ∀ (K : Type) [Field K] [Finite K] [CharP K 2] (γ : G → K)
        (M₀ : Tim79.QuadModel Q Z K γ), GlobalModelData M Q Z γ M₀ →
      ∃ T : Submodule K M₀.E,
        (∀ e : M₀.E, e ∈ T ↔ e ∈ M₀.img (Vt M (LB M Q B) B Z t)) ∧
        Module.finrank K ↥(imgQInfQB M₀ B ⊓
          imgQInfQB M₀ (conjSubgroup r B)) + 1 = 2 * m)
    (hcentC : ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B)
      (n : ℕ) (t : G), Sec5Hyp hc n t → SpNat hc t →
      ∀ r ∈ Rt M (LB M Q B) t, HypPlane Q Z B (conjSubgroup r B) t →
      ∀ d ∈ Q ⊓ QB (conjSubgroup r B),
        (∀ l ∈ (QB (conjSubgroup r B) ⊓ M) ⊓ hc.CN t, ⁅l, d⁆ ∈ Z) →
        d ∈ Vone Q B (conjSubgroup r B) (Vt M (LB M Q B) B Z t)) :
    Sec53CentralizerW1Statement :=
  sec53CentralizerW1_of_decomp_hBC h34 hRoot h51 hprod hBC hcentC

end CFSG.RankThree.GF2n.Stroth80
