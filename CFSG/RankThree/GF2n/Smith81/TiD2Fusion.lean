module

public import CFSG.RankThree.GF2n.Smith81.TiD2Module
public import CFSG.RankThree.GF2n.Smith81.TiRootLines
public import CFSG.RankThree.GF2n.Stroth80.Sec5Vt
public import CFSG.RankThree.GF2n.Smith81.TiLane
public import CFSG.RankThree.GF2n.Smith81.TiLemmaC

public section

namespace CFSG.RankThree.GF2n.Smith81

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Stroth80
open scoped commutatorElement MatrixGroups Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

variable {K : Type} [Field K] [Finite K] [CharP K 2] {γ : G → K} {M₀ : Tim79.QuadModel Q Z K γ}

structure D2Ctx (M Q Z B : Subgroup G) (M₀ : Tim79.QuadModel Q Z K γ) where
  hc : Ctx M Q Z B
  hw : Width Q Z 2
  hD : GlobalModelData M Q Z γ M₀
  φ : ↥(H0 M Z) →* (M₀.E ≃ₗ[K] M₀.E)
  hφπ : ∀ (m : ↥(H0 M Z)) (x : G), x ∈ Q →
    M₀.π ((m : G) * x * (m : G)⁻¹) = φ m (M₀.π x)
  hφker : ∀ m : ↥(H0 M Z), φ m = 1 ↔ (m : G) ∈ Q
  hφQ : ∀ (m : ↥(H0 M Z)) e, M₀.Qf (φ m e) = M₀.Qf e
  δ : ↥(D2.detIsom K) →* Multiplicative (ZMod 2)
  hδ : ∀ T : ↥(D2.detIsom K), δ T = 1 ↔ (T : Mat2 K ≃ₗ[K] Mat2 K) ∈ D2.pairGroup K
  D : D2Data Q Z M₀ (φ.comp (Subgroup.inclusion hc.Lgen_le_H0))

namespace D2Ctx

variable (R : D2Ctx M Q Z B M₀)

theorem hφSπ (m : ↥(Lgen M (LB M Q B))) (x : G) (hx : x ∈ Q) :
    M₀.π ((m : G) * x * (m : G)⁻¹) =
      (R.φ.comp (Subgroup.inclusion R.hc.Lgen_le_H0)) m (M₀.π x) :=
  R.hφπ ⟨m, R.hc.Lgen_le_H0 m.2⟩ x hx

include R in
theorem card_le_two_mul {P : Subgroup G} (hP : P ≤ H0 M Z) :
    Nat.card P ≤ 2 * Nat.card ↥(P ⊓ Lgen M (LB M Q B)) :=
  R.D.card_le_two_mul R.δ R.hδ R.φ R.hc.Lgen_le_H0 (fun _ => rfl)
    (fun m h => (R.hφker m).mp h) R.hc.Q_le_Lgen R.hφQ
    (fun m hm s hs => R.hc.mem_Lgen_conj (hm.1) hs) hP

include R in
theorem line_of_root {A : Subgroup G} (hA : Ctx M Q Z A) :
    ∃ c : Fin 2 → K, c ≠ 0 ∧
      ∀ v, v ∈ M₀.img A ↔ ∃ μ : K, v = μ • R.D.Θ.symm (D2.tw R.D.σ c) := by
  obtain ⟨t, ht, htQ⟩ : ∃ t ∈ LB M Q A ⊓ Lgen M (LB M Q B), t ∉ Q := by
    by_contra hcon
    push Not at hcon
    have hle : LB M Q A ⊓ Lgen M (LB M Q B) ≤ Q := fun t ht => hcon t ht
    have h1 := R.card_le_two_mul (P := LB M Q A) hA.LB_le_H0
    have h2 := hA.card_LB_ge R.hw (by norm_num : 1 ≤ 2)
    have h3 : Nat.card ↥(LB M Q A ⊓ Lgen M (LB M Q B)) ≤ Nat.card Q :=
      Subgroup.card_le_of_le hle
    have h4 : Nat.card Z ^ (2 - 1) = Nat.card Z := by norm_num
    rw [h4] at h2
    have hq4 : 4 ≤ Nat.card Z := R.hc.hyp.q4
    have h5 : 0 < Nat.card Q := Nat.card_pos
    nlinarith
  set t' : ↥(Lgen M (LB M Q B)) := ⟨t, ht.2⟩ with ht'def
  have ht2 : t ^ 2 ∈ Q := hA.sq_mem_Q_of_mem_LB ht.1
  obtain ⟨c, hc0, hcl⟩ := R.D.lemmaS (t := t') htQ ht2
  obtain ⟨b, hb0, hbs, hb, -, -⟩ := hA.dictB R.hD
  obtain ⟨a₀, ha₀A, ha₀Q, ha₀⟩ := (hb b).mpr ⟨1, (one_smul K b).symm⟩
  have hfix : (R.φ.comp (Subgroup.inclusion R.hc.Lgen_le_H0)) t' b = b := by
    rw [← ha₀, ← R.hφSπ t' a₀ ha₀Q]
    exact (Tim79.QuadModel.comm_mem_iff (M₀ := M₀) ha₀Q
      (conj_mem_Q R.hc.hyp (hA.LB_le_M ht.1) ha₀Q)).mp (hA.comm_B_mem_Z ht.1 ha₀A)
  obtain ⟨μ, hμ⟩ := hcl b hfix hbs
  have hμ0 : μ ≠ 0 := by
    rintro rfl
    exact hb0 (by rw [hμ, zero_smul])
  refine ⟨c, hc0, fun v => ?_⟩
  constructor
  · intro hv
    obtain ⟨s, hs⟩ := (hb v).mp hv
    exact ⟨s * μ, by rw [hs, hμ, smul_smul]⟩
  · rintro ⟨ν, hν⟩
    refine (hb v).mpr ⟨ν * μ⁻¹, ?_⟩
    rw [hν, hμ, smul_smul, mul_assoc, inv_mul_cancel₀ hμ0, mul_one]

include R in
theorem omega : OmegaProp M Q Z := by
  refine omega_of_lines R.hc.hyp R.hD
    {v | ∃ c : Fin 2 → K, c ≠ 0 ∧ v = R.D.Θ.symm (D2.tw R.D.σ c)} ?_ ?_
  · rintro v ⟨c, hc0, rfl⟩ w ⟨c', hc0', rfl⟩ hB
    have hΔ : c 0 * c' 1 - c 1 * c' 0 = 0 := by
      by_contra h
      exact R.D.B_tw_ne_zero h hB
    obtain ⟨s, hs⟩ := D2.exists_smul_of_det_zero hc0 hΔ
    refine ⟨s * R.D.σ s, ?_⟩
    rw [hs, D2.tw_smul, map_smul]
  · intro A hA
    obtain ⟨c, hc0, hl⟩ := R.line_of_root hA
    refine ⟨R.D.Θ.symm (D2.tw R.D.σ c), ⟨c, hc0, rfl⟩, ?_, fun a ha => ?_⟩
    · intro h
      apply D2.tw_ne_zero R.D.σ hc0
      have := congrArg R.D.Θ h
      simpa using this
    · exact (hl _).mp (M₀.pi_mem_img ha (hA.le ha))

include R in
theorem p2 : P2Prop M Q Z := by
  refine p2_of_conj R.hc.hyp fun X x hs => ?_
  have h12 := smith_1_12 hs
  obtain ⟨g, hg, hQB, -⟩ := hs.QB_eq
  have hq4 : 4 ≤ Nat.card Z := R.hc.hyp.q4
  have hKZ : Nat.card K = Nat.card Z := R.hD.card
  have hQ2 : IsPGroup 2 Q := by
    rw [R.hc.hyp.hQ]
    exact (inSubgroup_pCore_two M).1
  have hQB2 : IsPGroup 2 (QB X) := by
    rw [hQB]
    exact hQ2.map (MulAut.conj g).toMonoidHom
  have hne : Q ⊓ QB X ≠ ⊥ := by
    intro hbot
    have hLx : Lx M X ≤ H0 M Z := Lx_le_H0 hs h12
    have h1 := R.card_le_two_mul hLx
    have h2 : Nat.card Z ^ 2 ≤ Nat.card ↥(Lx M X) := hs.card_Lx_ge R.hw
    have hLxQB : Lx M X ⊓ Lgen M (LB M Q B) ≤ QB X := inf_le_left.trans inf_le_left
    have h3 : Nat.card ↥(Lx M X ⊓ Lgen M (LB M Q B)) ≤ Nat.card K := by
      refine R.D.card_le_of_pGroup inf_le_right (hQB2.to_le hLxQB) ?_
      rw [eq_bot_iff]
      intro y hy
      have : y ∈ Q ⊓ QB X := ⟨hy.2, hLxQB hy.1⟩
      rw [hbot] at this
      exact this
    nlinarith
  obtain ⟨⟨b, hbQQ⟩, hb1'⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
  have hb1 : b ≠ 1 := fun h => hb1' (Subtype.ext h)
  obtain ⟨hbQ, hbB⟩ := Subgroup.mem_inf.mp hbQQ
  have hXcard : Nat.card X = Nat.card Z := by
    obtain ⟨g', hg'⟩ := hs.conj
    rw [hg', card_conjSubgroup]
  have hXS : X ⊓ Lgen M (LB M Q B) ≠ ⊥ := by
    intro hbot
    have h1 := R.card_le_two_mul h12.1
    rw [hbot, Subgroup.card_bot, hXcard] at h1
    omega
  obtain ⟨⟨x₀, hx₀⟩, hx₀1'⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hXS
  have hx₀1 : x₀ ≠ 1 := fun h => hx₀1' (Subtype.ext h)
  have hx₀X : x₀ ∈ X := hx₀.1
  have hx₀S : x₀ ∈ Lgen M (LB M Q B) := hx₀.2
  have hx₀Q : x₀ ∉ Q := by
    intro hQ
    have : x₀ ∈ X ⊓ Q := ⟨hx₀X, hQ⟩
    rw [h12.2, Subgroup.mem_bot] at this
    exact hx₀1 this
  have hx₀2 : x₀ ^ 2 ∈ Q := by
    rw [pow_two, hs.X_sq x₀ hx₀X]
    exact Q.one_mem
  set t' : ↥(Lgen M (LB M Q B)) := ⟨x₀, hx₀S⟩ with ht'def
  obtain ⟨c, hc0, hcl⟩ := R.D.lemmaS (t := t') hx₀Q hx₀2
  have hfix : (R.φ.comp (Subgroup.inclusion R.hc.Lgen_le_H0)) t' (M₀.π b) = M₀.π b := by
    rw [← R.hφSπ t' b hbQ]
    have hcomm : x₀ * b = b * x₀ := hs.QB_comm_X hx₀X hbB
    rw [show x₀ * b * x₀⁻¹ = b by rw [hcomm]; group]
  have hsing : M₀.Qf (M₀.π b) = 0 :=
    (M₀.sq_iff_Qf R.hD.reg hbQ).mp (hs.inf_QB_elemAbelian.2 b hbQQ)
  obtain ⟨μ, hμ⟩ := hcl _ hfix hsing
  obtain ⟨c₁, hc₁, hB⟩ := R.line_of_root R.hc
  obtain ⟨A', hA', hl⟩ := R.D.exists_ctx_line R.hc R.hc.Lgen_le_M
    (fun m x hx => R.hφSπ m x hx) hc₁ hB hc0
  have hπ : M₀.π b ∈ M₀.img A' := (hl _).mpr ⟨μ, hμ⟩
  have hbA : b ∈ A' ⊔ Z := (M₀.mem_img_iff (le_sup_right : Z ≤ A' ⊔ Z) hbQ).mp
    (M₀.img_mono le_sup_left hπ)
  rw [sup_comm] at hbA
  obtain ⟨h, hh⟩ := hA'.exists_conj_mem_Z hbA hb1
  exact ⟨b, hbQQ, hb1, h, h⁻¹ * b * h, hh, by group⟩

end D2Ctx

theorem tiFusionD2 : TiFusionD2Statement := by
  intro G _ _ M Q Z B H hB hBQ hBZ hc hno
  have hC : Ctx M Q Z B := ⟨H, hB, hBQ, hBZ⟩
  have hw : Width Q Z 2 := by
    have := hc.1
    unfold Width
    simpa using this
  obtain ⟨K, _, _, _, γ, M₀, hD⟩ := stroth_globalModelData H
  obtain ⟨φ, hφπ, hφker, hφQ⟩ := exists_actionHom_H0 H hD
  have hK : 1 < Nat.card K := by
    have := H.q4
    rw [hD.card]
    omega
  obtain ⟨Θ₀, hΘ₀⟩ := exists_det_equiv (CharTwo.two_eq_zero) M₀.B M₀.Qf M₀.alt M₀.nondeg
    M₀.Qf_add hD.hyperbolic (by rw [hD.finrank_E hw hK])
  obtain ⟨δ, hδ⟩ := D2.exists_dicksonHom K
  obtain ⟨D⟩ := exists_d2Data hC hw hno hc.2 hD (φ.comp (Subgroup.inclusion hC.Lgen_le_H0))
    (fun m x hx => hφπ ⟨m, hC.Lgen_le_H0 m.2⟩ x hx)
    (fun m => hφker ⟨m, hC.Lgen_le_H0 m.2⟩)
    (fun m e => hφQ ⟨m, hC.Lgen_le_H0 m.2⟩ e) Θ₀ hΘ₀
  let R : D2Ctx M Q Z B M₀ := ⟨hC, hw, hD, φ, hφπ, hφker, hφQ, δ, hδ, D⟩
  exact tiFusion_of_omega_p2 H R.omega R.p2

end CFSG.RankThree.GF2n.Smith81
