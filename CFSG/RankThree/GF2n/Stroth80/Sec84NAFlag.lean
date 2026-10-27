module

public import CFSG.RankThree.GF2n.Stroth80.Sec310RootMain
public import CFSG.RankThree.GF2n.Stroth80.Sec8StepsModel
public import CFSG.RankThree.GF2n.Stroth80.Sec8CentreModel
public import CFSG.RankThree.GF2n.Stroth80.Sec8StepsLin
public import CFSG.RankThree.GF2n.Stroth80.Sec85IrredW1V1
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.LocalAnalysis.AGLEmbedding.SeitzEqTwo.DescentE
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.Quasithin.Vol2.Ch10SecKGA318
public import CFSG.RankThree.PartTwo.KFacts.KS21Mult
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open CFSG.ClassicalGroups.Symplectic
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem sec8_flag (h34 : Stroth34Statement) (h51 : Stroth51Statement)
    (h53 : Stroth53Statement) (h310chi : Stroth310ChiStatement) (hzt : Sec8ZtStatement)
    (hA : Sec8AExistsStatement) (hc : Ctx M Q Z B) {n : ℕ} {t r : G} (hs : Sec8Hyp hc n t)
    (hr : Sec7A hc t r) (hC : Conc83 hc n t)
    {K : Type} [Field K] [Finite K] [CharP K 2] {γ : G → K} (M₀ : Tim79.QuadModel Q Z K γ)
    (hD : GlobalModelData M Q Z γ M₀) :
    ∃ (m : ℕ) (A₀ A : Submodule K M₀.E) (φ : ↥(H0 M Z) →* (M₀.E ≃ₗ[K] M₀.E))
      (ψ : M₀.E →ₗ[K] M₀.E), 2 ≤ m ∧ SpMNat hc t m ∧ (n = 11 ∧ m = 3 ∨ n = 17 ∧ m = 4) ∧
      (∀ e, e ∈ A₀ ↔ e ∈ M₀.img (Vt M (LB M Q B) B Z t)) ∧
      (∀ e, e ∈ A ↔ e ∈ M₀.img (Sec8V1 M Q Z B t r)) ∧
      (∀ e, e ∈ M₀.img (Sec8W1 M Q Z B t r) ↔ e ∈ M₀.B.orthogonal A) ∧
      (∀ e, e ∈ M₀.img (Wt Q (Vt M (LB M Q B) B Z t)) ↔ e ∈ M₀.B.orthogonal A₀) ∧
      (∀ (h : ↥(H0 M Z)), ∀ y ∈ Q, M₀.π ((h : G) * y * (h : G)⁻¹) = φ h (M₀.π y)) ∧
      (∀ (h : ↥(H0 M Z)), φ h = 1 ↔ (h : G) ∈ Q) ∧
      (∀ (h : ↥(H0 M Z)) x y, M₀.B (φ h x) (φ h y) = M₀.B x y) ∧
      A₀ ≤ A ∧ A ≤ M₀.B.orthogonal A ∧ M₀.B.orthogonal A ≤ M₀.B.orthogonal A₀ ∧
      Module.finrank K ↥A₀ = 2 * m ∧ Module.finrank K ↥A = 2 * m + 1 ∧
      Module.finrank K ↥(M₀.B.orthogonal A) = 2 * m + 1 + 2 ^ m ∧
      Module.finrank K ↥(M₀.B.orthogonal A₀) = Module.finrank K ↥(M₀.B.orthogonal A) + 1 ∧
      (∀ e, e ∈ LinearMap.range ψ ↔ e ∈ A₀) ∧ LinearMap.ker ψ = M₀.B.orthogonal A₀ ∧
      (∀ ρ (hρ : ρ ∈ Rt M (LB M Q B) t) e,
        φ ⟨ρ, hc.Rt_le_H0 t hρ⟩ (ψ e) = ψ (φ ⟨ρ, hc.Rt_le_H0 t hρ⟩ e)) ∧
      (∀ ρ (hρ : ρ ∈ Rt M (LB M Q B) t), ∀ e ∈ A₀, φ ⟨ρ, hc.Rt_le_H0 t hρ⟩ e ∈ A₀) ∧
      (∀ ρ (hρ : ρ ∈ Rt M (LB M Q B) t), ∀ e ∈ A, φ ⟨ρ, hc.Rt_le_H0 t hρ⟩ e ∈ A) ∧
      (∀ ρ (hρ : ρ ∈ Rt M (LB M Q B) t), ∀ e ∈ M₀.B.orthogonal A,
        φ ⟨ρ, hc.Rt_le_H0 t hρ⟩ e ∈ M₀.B.orthogonal A) ∧
      (∀ ρ (hρ : ρ ∈ Rt M (LB M Q B) t), ∀ e ∈ M₀.B.orthogonal A₀,
        φ ⟨ρ, hc.Rt_le_H0 t hρ⟩ e ∈ M₀.B.orthogonal A₀) ∧
      (∀ Sp : Submodule K M₀.E, Sp ≠ ⊥ →
        (∀ ρ (hρ : ρ ∈ Rt M (LB M Q B) t), ∀ v ∈ Sp, φ ⟨ρ, hc.Rt_le_H0 t hρ⟩ v ∈ Sp) →
        A₀ ≤ Sp) := by
  classical
  have hRoot := stroth310Root_of_34 h34
  have h5 := hs.toSec5
  have ht : t ∈ LB M Q B := h5.mem
  have htM : t ∈ M := hc.LB_le_M ht
  have hZQ : Z ≤ Q := hc.Z_le_Q
  have hVQ : Vt M (LB M Q B) B Z t ≤ Q := hc.Vt_le_Q t
  have hZV : Z ≤ Vt M (LB M Q B) B Z t := sec39_Z_le_Vt
  have hRM : Rt M (LB M Q B) t ≤ M := hc.Rt_le_M t
  have hNR : hc.CN t ≤ Rt M (LB M Q B) t := fun y hy => (Ctx.mem_CN.1 hy).1
  have hQn : ∀ a ∈ M, ∀ y ∈ Q, a * y * a⁻¹ ∈ Q := fun a ha y hy =>
    (Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 ha) y).mp hy
  have h35 := (stroth_3_5 h34 hc h5.width h5.n_gt h5.noA2 h5.gen).2.1
  obtain ⟨m, hm2, hmSp, hmn, hWV, hV1c, hirrX⟩ := sec8_irred_W1V1 h34 hRoot h53 hc hs hr hC
  have hInv := fun ρ hρ => sec8InvStatement_holds G M Q Z B hc n t hs r hr ρ hρ
  have h53a := h53.1 G M Q Z B hc n t h5 hs.spNat r hr.mem hr.plane (conjSubgroup r B)
    (Vt M (LB M Q B) B Z t) (Wt Q (Vt M (LB M Q B) B Z t)) (Sec8V1 M Q Z B t r)
    (Sec8W1 M Q Z B t r) rfl rfl rfl rfl rfl
  have h53b := h53.2.1 G M Q Z B hc n t h5 hs.spNat r hr.mem hr.plane (conjSubgroup r B)
    (hc.CN t) (Vt M (LB M Q B) B Z t) (Sec8W1 M Q Z B t r) (Sec8V1 M Q Z B t r)
    rfl rfl rfl rfl rfl
  have h53d := h53.2.2.2.1 G M Q Z B hc n t h5 hs.spNat r hr.mem hr.plane (conjSubgroup r B)
    (hc.CN t) (Rt M (LB M Q B) t) (Vt M (LB M Q B) B Z t) (Sec8W1 M Q Z B t r)
    (Sec8V1 M Q Z B t r) rfl rfl rfl rfl rfl rfl
  haveI hEfin : Module.Finite K M₀.E := M₀.fin
  haveI hEfinite : Finite M₀.E := Module.finite_of_finite K
  have hq : Nat.card K = Nat.card Z := hD.card
  have hq2 : 2 ≤ Nat.card Z := by have := hc.hyp.q4; omega
  obtain ⟨A, A₀, hAmem, hA₀mem, hA₀A, hdim⟩ := sec8_exists_codim_one h310chi h53.1 hc hs hr hD
  obtain ⟨φ, hφπ, hφker, hφQ⟩ := exists_actionHom_H0 hc.hyp hD
  have hnd : M₀.B.Nondegenerate := by
    refine ⟨fun x hx => M₀.nondeg x hx, fun y hy => M₀.nondeg y fun f => ?_⟩
    rw [Tim79.QuadModel.B_comm, hy f, neg_zero]
  have hrefl : M₀.B.IsRefl := fun x y h => by rw [Tim79.QuadModel.B_comm, h, neg_zero]
  have h2K : (2 : K) = 0 := CharP.cast_eq_zero K 2
  have hneg : ∀ x : M₀.E, x + x = 0 := fun x => by rw [← two_smul K x, h2K, zero_smul]
  have hcommφ : ∀ (a b : ↥(H0 M Z)), ⁅(a : G), (b : G)⁆ ∈ Q → ∀ e, φ a (φ b e) = φ b (φ a e) := by
    intro a b hab e
    have h1 : φ ⁅a, b⁆ = 1 := (hφker ⁅a, b⁆).mpr hab
    rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm] at h1
    exact LinearEquiv.congr_fun h1 e
  have htH : t ∈ H0 M Z := hc.LB_le_H0 ht
  have htcz : ∀ z ∈ Z, t * z * t⁻¹ = z := fun z hz => by
    rw [← Subgroup.mem_centralizer_iff.mp htH.2 z hz, mul_inv_cancel_right]
  set tH : ↥(H0 M Z) := ⟨t, htH⟩ with htHdef
  set Tt : M₀.E ≃ₗ[K] M₀.E := φ tH with hTt
  have hTtπ : ∀ y ∈ Q, M₀.π (t * y * t⁻¹) = Tt (M₀.π y) := fun y hy => hφπ tH y hy
  have hTtB : ∀ e f, M₀.B (Tt e) (Tt f) = M₀.B e f := fun e f =>
    quadModel_B_iso M₀ Tt (hφQ tH) e f
  set ψ : M₀.E →ₗ[K] M₀.E := (Tt : M₀.E →ₗ[K] M₀.E) - 1 with hψ
  have hψapp : ∀ e, ψ e = Tt e - e := fun e => by simp [hψ]
  have hTt2 : ∀ e, Tt (Tt e) = e := by
    intro e
    obtain ⟨y, hyQ, rfl⟩ := M₀.π_surj e
    have h1 : t * y * t⁻¹ ∈ Q := hQn t htM y hyQ
    rw [← hTtπ y hyQ, ← hTtπ _ h1]
    have e2 : t * (t * y * t⁻¹) * t⁻¹ = t ^ 2 * y * (t ^ 2)⁻¹ := by
      rw [pow_two]
      group
    rw [e2]
    exact Tim79.QuadModel.pi_conj_self (M₀ := M₀) (hc.sq_mem_Q_of_mem_LB ht) hyQ
  have hψψ : ∀ e, ψ (ψ e) = 0 := by
    intro e
    rw [hψapp, hψapp, map_sub, hTt2]
    calc e - Tt e - (Tt e - e) = (e + e) - (Tt e + Tt e) := by abel
      _ = 0 := by rw [hneg e, hneg (Tt e), sub_zero]
  have hVU : Vt M (LB M Q B) B Z t = Ut Q Z t :=
    (h310chi G M Q Z B hc n t h5 (Or.inl hs.spNat)).1
  have hψrange : ∀ e, e ∈ LinearMap.range ψ ↔ e ∈ A₀ := by
    intro e
    rw [hA₀mem, hVU, sec8_img_Ut_iff hc hD htM (hc.sq_mem_Q_of_mem_LB ht) hTtπ e,
      LinearMap.mem_range]
    constructor
    · rintro ⟨f, hf⟩
      exact ⟨f, by rw [← hf, hψapp]⟩
    · rintro ⟨f, hf⟩
      exact ⟨f, by rw [hψapp, hf]⟩
  have hrangeψ : LinearMap.range ψ = A₀ := Submodule.ext hψrange
  set AW : Submodule K M₀.E := M₀.B.orthogonal A₀ with hAWdef
  have hkerψ : LinearMap.ker ψ = AW := by
    have h := ker_sub_one_eq_orthogonal_range M₀.B hnd hrefl (Tt : M₀.E →ₗ[K] M₀.E)
      (fun u v => hTtB u v) Tt.surjective
    rw [hrangeψ] at h
    exact h
  have hψcomm : ∀ ρ (hρ : ρ ∈ Rt M (LB M Q B) t) e,
      φ ⟨ρ, hc.Rt_le_H0 t hρ⟩ (ψ e) = ψ (φ ⟨ρ, hc.Rt_le_H0 t hρ⟩ e) := by
    intro ρ hρ e
    rw [hψapp, hψapp, map_sub]
    rw [hcommφ ⟨ρ, hc.Rt_le_H0 t hρ⟩ tH (hc.Rt_comm_mem_Q hρ) e]
  have hAset : (A : Set M₀.E) = ↑(M₀.img (Sec8V1 M Q Z B t r)) := Set.ext hAmem
  set AW1 : Submodule K M₀.E := M₀.B.orthogonal A with hAW1def
  have hAW1mem : ∀ e, e ∈ M₀.img (Sec8W1 M Q Z B t r) ↔ e ∈ AW1 :=
    sec8_img_W1_eq_orthogonal hc hD A hAset
  have hAWmem : ∀ e, e ∈ M₀.img (Wt Q (Vt M (LB M Q B) B Z t)) ↔ e ∈ AW := by
    intro e
    rw [mem_img_Wt_iff M₀ hD.reg hVQ, hAWdef, LinearMap.BilinForm.mem_orthogonal_iff]
    constructor
    · intro h a ha
      rw [Tim79.QuadModel.B_comm, h a ((hA₀mem a).mp ha), neg_zero]
    · intro h a ha
      have := h a ((hA₀mem a).mpr ha)
      rw [Tim79.QuadModel.B_comm, this, neg_zero]
  have hfinS : ∀ (S : Subgroup G) (P : Submodule K M₀.E), S ≤ Q → Z ≤ S →
      (∀ e, e ∈ M₀.img S ↔ e ∈ P) →
      Nat.card ↥S = Nat.card Z * Nat.card Z ^ Module.finrank K ↥P := by
    intro S P hSQ hZS hSP
    have h1 : Nat.card ↥S = Nat.card Z * Nat.card ↥(M₀.img S) := M₀.card_eq hSQ hZS
    have h2 : Nat.card ↥(M₀.img S) = Nat.card ↥P :=
      Nat.card_congr (Equiv.subtypeEquivRight hSP)
    rw [h1, h2, Module.natCard_eq_pow_finrank (K := K) (V := ↥P), hq]
  have hpowinj : ∀ a b : ℕ, Nat.card Z ^ a = Nat.card Z ^ b → a = b := fun a b h =>
    Nat.pow_right_injective hq2 h
  have hfinA₀ : Module.finrank K ↥A₀ = 2 * m := by
    have h1 := hfinS (Vt M (LB M Q B) B Z t) A₀ hVQ hZV (fun e => (hA₀mem e).symm)
    rw [hmSp.card_V, pow_succ'] at h1
    exact (hpowinj _ _ (Nat.eq_of_mul_eq_mul_left (Nat.card_pos (α := ↥Z)) h1)).symm
  have hfinA : Module.finrank K ↥A = 2 * m + 1 := by omega
  have hfinAW1 : Module.finrank K ↥AW1 = 2 * m + 1 + 2 ^ m := by
    have h1 := hfinS (Sec8W1 M Q Z B t r) AW1 (sec8_W1_le_Q M Q Z B t r) (sec8_Z_le_W1 hc t r)
      hAW1mem
    rw [hWV, hV1c] at h1
    have h2 : Nat.card Z * Nat.card Z ^ (2 * m + 1 + 2 ^ m) =
        Nat.card Z * Nat.card Z ^ Module.finrank K ↥AW1 := by
      rw [← h1]
      ring
    exact (hpowinj _ _ (Nat.eq_of_mul_eq_mul_left (Nat.card_pos (α := ↥Z)) h2)).symm
  have hfinAW : Module.finrank K ↥AW = Module.finrank K ↥AW1 + 1 := by
    obtain ⟨-, hWc, -⟩ := h53a
    have h1 := hfinS (Wt Q (Vt M (LB M Q B) B Z t)) AW (inf_le_left) (fun z hz => ?_) hAWmem
    · have h2 := hfinS (Sec8W1 M Q Z B t r) AW1 (sec8_W1_le_Q M Q Z B t r)
        (sec8_Z_le_W1 hc t r) hAW1mem
      rw [hWc, h2] at h1
      have h3 : Nat.card Z * Nat.card Z ^ (Module.finrank K ↥AW1) * Nat.card Z =
          Nat.card Z * Nat.card Z ^ (Module.finrank K ↥AW1 + 1) := by ring
      rw [h3] at h1
      exact (hpowinj _ _ (Nat.eq_of_mul_eq_mul_left (Nat.card_pos (α := ↥Z)) h1)).symm
    · exact ⟨hZQ hz, Subgroup.mem_centralizer_iff.mpr fun v hv =>
        (hc.hyp.toHyp79.V_central hz (hVQ hv)).symm⟩
  have hinvA₀ : ∀ Sp : Submodule K M₀.E, Sp ≠ ⊥ →
      (∀ ρ (hρ : ρ ∈ Rt M (LB M Q B) t), ∀ v ∈ Sp, φ ⟨ρ, hc.Rt_le_H0 t hρ⟩ v ∈ Sp) →
      A₀ ≤ Sp := by
    intro Sp hSp hinv e he
    refine hc.img_Vt_le_of_invariant h35 hD t Sp hSp (fun l hl S hS1 hS2 v hv => ?_) e
      ((hA₀mem e).mp he)
    have hSeq : (S : M₀.E → M₀.E) = φ ⟨l, hc.Rt_le_H0 t hl⟩ :=
      eq_of_pi_conj_eq hS1 (hφπ ⟨l, hc.Rt_le_H0 t hl⟩)
    have h1 := hinv l hl v hv
    have h2 : S v = φ ⟨l, hc.Rt_le_H0 t hl⟩ v := congrFun hSeq v
    rwa [h2]
  have hRA : ∀ ρ (hρ : ρ ∈ Rt M (LB M Q B) t), ∀ e ∈ A, φ ⟨ρ, hc.Rt_le_H0 t hρ⟩ e ∈ A := by
    intro ρ hρ e he
    obtain ⟨u, hu, huQ, rfl⟩ := (hAmem e).mp he
    rw [← hφπ ⟨ρ, hc.Rt_le_H0 t hρ⟩ u huQ]
    exact (hAmem _).mpr (M₀.pi_mem_img (conj_mem_of_conjSubgroup_eq (hInv ρ hρ).1 hu)
      (hQn ρ (hRM hρ) u huQ))
  have hRAW1 : ∀ ρ (hρ : ρ ∈ Rt M (LB M Q B) t), ∀ e ∈ AW1,
      φ ⟨ρ, hc.Rt_le_H0 t hρ⟩ e ∈ AW1 := by
    intro ρ hρ e he
    obtain ⟨u, hu, huQ, rfl⟩ := (hAW1mem e).mpr he
    rw [← hφπ ⟨ρ, hc.Rt_le_H0 t hρ⟩ u huQ]
    exact (hAW1mem _).mp (M₀.pi_mem_img (conj_mem_of_conjSubgroup_eq (hInv ρ hρ).2 hu)
      (hQn ρ (hRM hρ) u huQ))
  have hRAW : ∀ ρ (hρ : ρ ∈ Rt M (LB M Q B) t), ∀ e ∈ AW,
      φ ⟨ρ, hc.Rt_le_H0 t hρ⟩ e ∈ AW := by
    intro ρ hρ e he
    obtain ⟨u, hu, huQ, rfl⟩ := (hAWmem e).mpr he
    rw [← hφπ ⟨ρ, hc.Rt_le_H0 t hρ⟩ u huQ]
    refine (hAWmem _).mp (M₀.pi_mem_img ?_ (hQn ρ (hRM hρ) u huQ))
    exact conj_mem_of_conjSubgroup_eq (sec8_conjSubgroup_eq_of_mem_normalizer
      (sec8_Wt_mem_normalizer (hc.hyp.Q_normal.2 (hRM hρ)) (hc.Rt_normalizes_Vt ht hρ))) hu
  have h53c := h53.2.2.1 G M Q Z B hc n t h5 hs.spNat r hr.mem hr.plane (conjSubgroup r B)
    (LB M Q B) (LB M Q (conjSubgroup r B)) (Vt M (LB M Q B) B Z t) (Sec8W1 M Q Z B t r)
    (Sec8V1 M Q Z B t r) rfl rfl rfl rfl rfl rfl
  have hV₁W₁ : Sec8V1 M Q Z B t r ≤ Sec8W1 M Q Z B t r := h53c.1.trans h53c.2.1
  have hBV : B ≤ Vt M (LB M Q B) B Z t := by
    have h1 := sec39_conjB_le_Vt (M := M) (L := LB M Q B) (B := B) (Z := Z) (t := t) M.one_mem
      (by rw [conjSubgroup_one]; exact ht)
    rwa [conjSubgroup_one] at h1
  have hAAW1 : A ≤ AW1 := fun e he =>
    (hAW1mem e).mp (M₀.img_mono hV₁W₁ ((hAmem e).mp he))
  have hAW1AW : AW1 ≤ AW := fun e he =>
    LinearMap.BilinForm.mem_orthogonal_iff.mpr fun a ha =>
      LinearMap.BilinForm.mem_orthogonal_iff.mp he a (hA₀A ha)
  have hRA₀ : ∀ ρ (hρ : ρ ∈ Rt M (LB M Q B) t), ∀ e ∈ A₀, φ ⟨ρ, hc.Rt_le_H0 t hρ⟩ e ∈ A₀ := by
    intro ρ hρ e he
    obtain ⟨u, hu, huQ, rfl⟩ := (hA₀mem e).mp he
    rw [← hφπ ⟨ρ, hc.Rt_le_H0 t hρ⟩ u huQ]
    refine (hA₀mem _).mpr (M₀.pi_mem_img ?_ (hQn ρ (hRM hρ) u huQ))
    exact conj_mem_of_conjSubgroup_eq
      (conjSubgroup_eq_self_iff.mpr (hc.Rt_normalizes_Vt ht hρ)) hu
  exact ⟨m, A₀, A, φ, ψ, hm2, hmSp, hmn, hA₀mem, hAmem, hAW1mem, hAWmem, hφπ, hφker,
    fun h x y => quadModel_B_iso M₀ (φ h) (hφQ h) x y, hA₀A, hAAW1, hAW1AW, hfinA₀, hfinA,
    hfinAW1, hfinAW, hψrange, hkerψ, hψcomm, hRA₀, hRA, hRAW1, hRAW, hinvA₀⟩

end CFSG.RankThree.GF2n.Stroth80
