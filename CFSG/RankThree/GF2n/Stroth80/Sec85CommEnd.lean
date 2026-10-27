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
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LayerNonsolv3
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

theorem sec85_centralizer_le_Z0 (h34 : Stroth34Statement) (h51 : Stroth51Statement)
    (h53 : Stroth53Statement) (h310chi : Stroth310ChiStatement) (hzt : Sec8ZtStatement)
    (hA : Sec8AExistsStatement) (hc : Ctx M Q Z B) {n : ℕ} {t r : G} (hs : Sec8Hyp hc n t)
    (hr : Sec7A hc t r) (hC : Conc83 hc n t) {Z0 : Subgroup G}
    (hZ0 : IsCentrePre Z0 (Rt M (LB M Q B) t) Q) {w : G} (hwH : w ∈ H0 M Z)
    (hwR : ∀ ρ ∈ Rt M (LB M Q B) t, ⁅w, ρ⁆ ∈ Q)
    (hwV₁ : ∀ v ∈ Sec8V1 M Q Z B t r, ⁅w, v⁆ ∈ Z)
    (hwW₁ : ∀ y ∈ Sec8W1 M Q Z B t r, ⁅w, y⁆ ∈ Sec8V1 M Q Z B t r) : w ∈ Z0 := by
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
  have hQZ0 : Q ≤ Z0 := hc.Q_le_centre ht hZ0
  have hZ0R : Z0 ≤ Rt M (LB M Q B) t := hZ0.le
  have hZ0N : Z0 ≤ hc.CN t := sec8_Z0_le_CN hc hs hZ0
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
  have hZ0card : Nat.card ↥Z0 = Nat.card Q * Nat.card Z :=
    sec86ZCard_of_51 h51 hA G M Q Z B hc n t hs Z0 hZ0
  obtain ⟨K, iF, iFin, hchar, γ, M₀, hD⟩ := stroth_globalModelData hc.hyp
  haveI : CharP K 2 := hchar
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
  have key : ∀ (w' : G) (hw'H : w' ∈ H0 M Z), (∀ ρ ∈ Rt M (LB M Q B) t, ⁅w', ρ⁆ ∈ Q) →
      (∀ v ∈ Sec8V1 M Q Z B t r, ⁅w', v⁆ ∈ Z) →
      (∀ y ∈ Sec8W1 M Q Z B t r, ⁅w', y⁆ ∈ Sec8V1 M Q Z B t r) →
      ∃ c : K, ∀ e, φ ⟨w', hw'H⟩ e - e = c • ψ e := by
    intro w' hw'H hw'R hw'V₁ hw'W₁
    have hw'M : w' ∈ M := hw'H.1
    set wH : ↥(H0 M Z) := ⟨w', hw'H⟩ with hwHdef
    set T : M₀.E ≃ₗ[K] M₀.E := φ wH with hT
    have hTπ : ∀ y ∈ Q, M₀.π (w' * y * w'⁻¹) = T (M₀.π y) := fun y hy => hφπ wH y hy
    have hTB : ∀ e f, M₀.B (T e) (T f) = M₀.B e f := fun e f =>
      quadModel_B_iso M₀ T (hφQ wH) e f
    set ν : M₀.E →ₗ[K] M₀.E := (T : M₀.E →ₗ[K] M₀.E) - 1 with hν
    have hνapp : ∀ e, ν e = T e - e := fun e => by simp [hν]
    have hνcomm : ∀ ρ (hρ : ρ ∈ Rt M (LB M Q B) t) e,
        φ ⟨ρ, hc.Rt_le_H0 t hρ⟩ (ν e) = ν (φ ⟨ρ, hc.Rt_le_H0 t hρ⟩ e) := by
      intro ρ hρ e
      rw [hνapp, hνapp, map_sub]
      have hQ : ⁅ρ, w'⁆ ∈ Q := by
        have := Q.inv_mem (hw'R ρ hρ)
        rwa [commutatorElement_inv] at this
      rw [hcommφ ⟨ρ, hc.Rt_le_H0 t hρ⟩ wH hQ e]
    have hνπ : ∀ y ∈ Q, ν (M₀.π y) = M₀.π ⁅w', y⁆ := fun y hy => by
      rw [hνapp]
      exact (sec8_pi_comm M₀ hy (hQn w' hw'M y hy) (hTπ y hy)).symm
    have hνA : ∀ e ∈ A, ν e = 0 := by
      intro e he
      obtain ⟨u, hu, huQ, rfl⟩ := (hAmem e).mp he
      rw [hνπ u huQ]
      exact (M₀.π_ker _ (hZQ (hw'V₁ u hu))).mpr (hw'V₁ u hu)
    have hνAW1 : ∀ e ∈ AW1, ν e ∈ A := by
      intro e he
      obtain ⟨y, hy, hyQ, rfl⟩ := (hAW1mem e).mpr he
      rw [hνπ y hyQ]
      exact (hAmem _).mpr (M₀.pi_mem_img (hw'W₁ y hy) (sec8_V1_le_Q hc t r (hw'W₁ y hy)))
    have hν1 : ∀ e ∈ AW1, ν e = 0 := by
      set S : Subgroup G := M₀.lift (LinearMap.ker ν ⊓ AW1).toAddSubgroup with hS
      have hV₁S : Sec8V1 M Q Z B t r ≤ S := by
        intro u hu
        have huQ : u ∈ Q := sec8_V1_le_Q hc t r hu
        have hπ : M₀.π u ∈ A := (hAmem _).mpr (M₀.pi_mem_img hu huQ)
        exact ⟨huQ, Submodule.mem_inf.mpr ⟨LinearMap.mem_ker.mpr (hνA _ hπ), hAAW1 hπ⟩⟩
      have hSW₁ : S ≤ Sec8W1 M Q Z B t r := by
        intro u hu
        exact (M₀.mem_img_iff (sec8_Z_le_W1 hc t r) hu.1).mp
          ((hAW1mem _).mpr (Submodule.mem_inf.mp hu.2).2)
      have hSinv : ∀ ρ ∈ Rt M (LB M Q B) t, conjSubgroup ρ S = S := by
        intro ρ hρ
        refine conjSubgroup_eq_self_iff.mpr (Subgroup.mem_normalizer_fintype fun u hu => ?_)
        refine ⟨hQn ρ (hRM hρ) u hu.1, ?_⟩
        obtain ⟨hk, hw⟩ := Submodule.mem_inf.mp hu.2
        show M₀.π (ρ * u * ρ⁻¹) ∈ (LinearMap.ker ν ⊓ AW1 : Submodule K M₀.E)
        rw [hφπ ⟨ρ, hc.Rt_le_H0 t hρ⟩ u hu.1]
        refine Submodule.mem_inf.mpr ⟨LinearMap.mem_ker.mpr ?_, hRAW1 ρ hρ _ hw⟩
        rw [← hνcomm ρ hρ, LinearMap.mem_ker.mp hk, map_zero]
      rcases hirrX S hV₁S hSW₁ hSinv with hS1 | hS1
      · exfalso
        have hKrA : ∀ e, ν e = 0 → e ∈ AW1 → e ∈ A := by
          intro e hk hw
          obtain ⟨u, huQ, rfl⟩ := M₀.π_surj e
          have huS : u ∈ S := ⟨huQ, Submodule.mem_inf.mpr ⟨LinearMap.mem_ker.mpr hk, hw⟩⟩
          rw [hS1] at huS
          exact (hAmem _).mpr (M₀.pi_mem_img huS huQ)
        let μ : ↥AW1 →ₗ[K] ↥A := ν.restrict (fun e he => hνAW1 e he)
        have hrn := LinearMap.finrank_range_add_finrank_ker μ
        have hr1 : Module.finrank K ↥(LinearMap.range μ) ≤ Module.finrank K ↥A :=
          Submodule.finrank_le _
        have hk1 : Module.finrank K ↥(LinearMap.ker μ) ≤ Module.finrank K ↥A := by
          have hle : LinearMap.ker μ ≤ Submodule.comap AW1.subtype A := by
            intro x hx
            have h0 : ν (x : M₀.E) = 0 := by
              have := congrArg Subtype.val (LinearMap.mem_ker.mp hx)
              simpa [μ, LinearMap.restrict_apply] using this
            exact hKrA x h0 x.2
          calc Module.finrank K ↥(LinearMap.ker μ)
              ≤ Module.finrank K ↥(Submodule.comap AW1.subtype A) := Submodule.finrank_mono hle
            _ = Module.finrank K ↥A := (Submodule.comapSubtypeEquivOfLe hAAW1).finrank_eq
        have hm' : 2 ^ m > 2 * m + 1 := by
          rcases hmn with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> norm_num
        omega
      · intro e he
        obtain ⟨y, hy, hyQ, rfl⟩ := (hAW1mem e).mpr he
        have hyS : y ∈ S := hS1 ▸ hy
        exact LinearMap.mem_ker.mp (Submodule.mem_inf.mp hyS.2).1
    have hν2 : ∀ e ∈ AW, ν e = 0 := by
      by_contra hne
      push Not at hne
      obtain ⟨e₀, he₀, hν₀⟩ := hne
      set Y : Submodule K M₀.E := Submodule.map ν AW with hY
      have hYne : Y ≠ ⊥ := by
        intro h
        apply hν₀
        have h1 : ν e₀ ∈ Y := Submodule.mem_map_of_mem he₀
        rw [h] at h1
        exact (Submodule.mem_bot K).mp h1
      have hYinv : ∀ ρ (hρ : ρ ∈ Rt M (LB M Q B) t), ∀ v ∈ Y,
          φ ⟨ρ, hc.Rt_le_H0 t hρ⟩ v ∈ Y := by
        intro ρ hρ v hv
        obtain ⟨e, he, rfl⟩ := hv
        exact ⟨φ ⟨ρ, hc.Rt_le_H0 t hρ⟩ e, hRAW ρ hρ e he, (hνcomm ρ hρ e).symm⟩
      have hA₀Y : A₀ ≤ Y := hinvA₀ Y hYne hYinv
      let μ₂ : ↥AW →ₗ[K] M₀.E := ν.domRestrict AW
      have hrn := LinearMap.finrank_range_add_finrank_ker μ₂
      have hrange : LinearMap.range μ₂ = Y := LinearMap.range_domRestrict AW ν
      have hker : Module.finrank K ↥AW1 ≤ Module.finrank K ↥(LinearMap.ker μ₂) := by
        have hle : Submodule.comap AW.subtype AW1 ≤ LinearMap.ker μ₂ := by
          intro x hx
          exact LinearMap.mem_ker.mpr (hν1 x hx)
        calc Module.finrank K ↥AW1
            = Module.finrank K ↥(Submodule.comap AW.subtype AW1) :=
              ((Submodule.comapSubtypeEquivOfLe hAW1AW).finrank_eq).symm
          _ ≤ _ := Submodule.finrank_mono hle
      rw [hrange] at hrn
      have hYle : Module.finrank K ↥A₀ ≤ Module.finrank K ↥Y := Submodule.finrank_mono hA₀Y
      omega
    have hν3 : ∀ e, ν e ∈ A₀ := by
      intro e
      rw [← LinearMap.BilinForm.orthogonal_orthogonal hnd hrefl A₀,
        LinearMap.BilinForm.mem_orthogonal_iff]
      intro f hf
      have hfix : T f = f := by
        have := hν2 f hf
        rw [hνapp] at this
        exact sub_eq_zero.mp this
      show M₀.B f (ν e) = 0
      rw [hνapp, map_sub]
      have := hTB f e
      rw [hfix] at this
      rw [this, sub_self]
    obtain ⟨b, hb0, -, hbline, -, -⟩ := hc.dictB hD
    have hbB : b ∈ M₀.img B := (hbline b).mpr ⟨1, (one_smul K b).symm⟩
    have hbA₀ : b ∈ A₀ := (hA₀mem b).mpr (M₀.img_mono hBV hbB)
    obtain ⟨eb, heb⟩ := (hψrange b).mpr hbA₀
    have hLBfix : ∀ l (hl : l ∈ LB M Q B), φ ⟨l, hc.LB_le_H0 hl⟩ b = b := by
      intro l hl
      obtain ⟨x, hxB, hxQ, hxb⟩ := hbB
      have hxC : x ∈ CQt Q Z (LB M Q B) := by rw [h35]; exact Subgroup.mem_sup_left hxB
      have hlx : ⁅l, x⁆ ∈ Z := hxC.2 l hl
      have hlxQ : ⁅l, x⁆ ∈ Q := hZQ hlx
      rw [← hxb, ← hφπ ⟨l, hc.LB_le_H0 hl⟩ x hxQ]
      have e : l * x * l⁻¹ = ⁅l, x⁆ * x := by
        simp only [commutatorElement_def]
        group
      show M₀.π (l * x * l⁻¹) = M₀.π x
      rw [e, M₀.π_mul _ hlxQ _ hxQ, (M₀.π_ker _ hlxQ).mpr hlx, zero_add]
    have hfix : ∀ l (hl : l ∈ LB M Q B), φ ⟨l, hc.LB_le_H0 hl⟩ (ν eb) = ν eb := by
      intro l hl
      have hlR : l ∈ Rt M (LB M Q B) t := le_Rt (LB M Q B) ht hl
      have h1 : ψ (φ ⟨l, hc.Rt_le_H0 t hlR⟩ eb - eb) = 0 := by
        rw [map_sub, ← hψcomm l hlR, heb, hLBfix l hl, sub_self]
      have h2 : φ ⟨l, hc.Rt_le_H0 t hlR⟩ eb - eb ∈ AW := by
        rw [← hkerψ]
        exact LinearMap.mem_ker.mpr h1
      have h3 := hν2 _ h2
      rw [map_sub, sub_eq_zero] at h3
      rw [hνcomm l hlR]
      exact h3
    obtain ⟨c, hcb⟩ : ∃ c : K, ν eb = c • b := by
      obtain ⟨x, hxQ, hx⟩ := M₀.π_surj (ν eb)
      have hxC : x ∈ CQt Q Z (LB M Q B) := by
        refine ⟨hxQ, fun l hl => ?_⟩
        have h1 := hfix l hl
        rw [← hx, ← hφπ ⟨l, hc.LB_le_H0 hl⟩ x hxQ] at h1
        exact (Tim79.QuadModel.comm_mem_iff (M₀ := M₀) hxQ
          ((Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 (hc.LB_le_M hl)) x).mp hxQ)).mpr h1
      rw [h35] at hxC
      have hle' : (B ⊔ Z : Subgroup G) ≤ M₀.lift (M₀.img B) := sup_le
        (fun u hu => ⟨hc.le hu, M₀.pi_mem_img hu (hc.le hu)⟩)
        (fun z hz => ⟨hZQ hz, by
          rw [(M₀.π_ker z (hZQ hz)).mpr hz]
          exact AddSubgroup.zero_mem _⟩)
      obtain ⟨s, hs⟩ := (hbline _).mp (hle' hxC).2
      exact ⟨s, hx.symm.trans hs⟩
    set S' : Submodule K M₀.E := LinearMap.ker (ν - c • ψ) with hS'
    have hebS' : eb ∈ S' := by
      rw [hS', LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, hcb, heb, sub_self]
    have hAWS' : ∀ e ∈ AW, e ∈ S' := by
      intro e he
      have h1 : ψ e = 0 := LinearMap.mem_ker.mp (hkerψ ▸ he)
      rw [hS', LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, hν2 e he, h1,
        smul_zero, sub_zero]
    set Y' : Submodule K M₀.E := Submodule.map ψ S' with hY'
    have hY'ne : Y' ≠ ⊥ := by
      intro h
      have h1 : ψ eb ∈ Y' := Submodule.mem_map_of_mem hebS'
      rw [h, heb] at h1
      exact hb0 ((Submodule.mem_bot K).mp h1)
    have hY'inv : ∀ ρ (hρ : ρ ∈ Rt M (LB M Q B) t), ∀ v ∈ Y',
        φ ⟨ρ, hc.Rt_le_H0 t hρ⟩ v ∈ Y' := by
      intro ρ hρ v hv
      obtain ⟨e, he, rfl⟩ := hv
      have he' : ν e - c • ψ e = 0 := he
      refine ⟨φ ⟨ρ, hc.Rt_le_H0 t hρ⟩ e, ?_, (hψcomm ρ hρ e).symm⟩
      show ν (φ ⟨ρ, hc.Rt_le_H0 t hρ⟩ e) - c • ψ (φ ⟨ρ, hc.Rt_le_H0 t hρ⟩ e) = 0
      rw [← hνcomm ρ hρ, ← hψcomm ρ hρ, ← map_smul, ← map_sub, he', map_zero]
    have hA₀Y' : A₀ ≤ Y' := hinvA₀ Y' hY'ne hY'inv
    refine ⟨c, fun e => ?_⟩
    have heS' : e ∈ S' := by
      have hψe : ψ e ∈ A₀ := (hψrange _).mp ⟨e, rfl⟩
      obtain ⟨s, hsS', hs⟩ := hA₀Y' hψe
      have hdiff : e - s ∈ AW := by
        rw [← hkerψ, LinearMap.mem_ker, map_sub, hs, sub_self]
      have h1 := S'.add_mem hsS' (hAWS' _ hdiff)
      simpa using h1
    have h1 := LinearMap.mem_ker.mp heS'
    rw [LinearMap.sub_apply, LinearMap.smul_apply, sub_eq_zero] at h1
    exact (hνapp e).symm.trans h1
  let Φ : Subgroup (M₀.E ≃ₗ[K] M₀.E) :=
    { carrier := {S | ∃ c : K, ∀ e, S e = e + c • ψ e}
      mul_mem' := by
        rintro S S' ⟨c, hc1⟩ ⟨c', hc2⟩
        refine ⟨c + c', fun e => ?_⟩
        rw [LinearEquiv.mul_apply, hc2, map_add, map_smul, hc1, hc1, hψψ, smul_zero, add_zero,
          add_smul]
        abel
      one_mem' := ⟨0, fun e => by simp⟩
      inv_mem' := by
        rintro S ⟨c, hc1⟩
        refine ⟨c, fun e => ?_⟩
        apply S.injective
        have h1 : S (S⁻¹ e) = e := by
          show S (S.symm e) = e
          exact S.apply_symm_apply e
        rw [h1, hc1, map_add, map_smul, hψψ, smul_zero, add_zero]
        have h2 : c • ψ e + c • ψ e = 0 := by rw [← two_smul K (c • ψ e), h2K, zero_smul]
        calc e = e + (c • ψ e + c • ψ e) := by rw [h2, add_zero]
          _ = e + c • ψ e + c • ψ e := by abel }
  have hΦcard : Nat.card ↥Φ ≤ Nat.card K := by
    let cof : ↥Φ → K := fun S => Classical.choose
      (show ∃ c : K, ∀ e, (S : M₀.E ≃ₗ[K] M₀.E) e = e + c • ψ e from S.2)
    have hcof : ∀ S : ↥Φ, ∀ e, (S : M₀.E ≃ₗ[K] M₀.E) e = e + cof S • ψ e := fun S =>
      Classical.choose_spec
        (show ∃ c : K, ∀ e, (S : M₀.E ≃ₗ[K] M₀.E) e = e + c • ψ e from S.2)
    have hinj : Function.Injective cof := by
      intro S S' h
      apply Subtype.ext
      apply LinearEquiv.ext
      intro e
      rw [hcof S e, hcof S' e, h]
    exact Nat.card_le_card_of_injective cof hinj
  have hZ0H : Z0 ≤ H0 M Z := fun x hx => hc.Rt_le_H0 t (hZ0R hx)
  let φZ : ↥Z0 →* (M₀.E ≃ₗ[K] M₀.E) := φ.comp (Subgroup.inclusion hZ0H)
  have hφZΦ : ∀ z : ↥Z0, φZ z ∈ Φ := by
    intro z
    obtain ⟨c, hcz⟩ := key z (hZ0H z.2) (fun ρ hρ => hZ0.comm_mem z.2 hρ)
      (fun v hv => h53d.1 z (hZ0N z.2) v hv) (fun y hy => h53b.2 z (hZ0N z.2) y hy)
    exact ⟨c, fun e => eq_add_of_sub_eq' (hcz e)⟩
  have hker : φZ.ker = Q.subgroupOf Z0 := by
    ext z
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    exact hφker (Subgroup.inclusion hZ0H z)
  have hcardZ0 := Subgroup.card_ker_mul_card_range φZ
  rw [hker, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQZ0).toEquiv, hZ0card] at hcardZ0
  have hrangecard : Nat.card ↥φZ.range = Nat.card K := by
    rw [hq]
    exact Nat.eq_of_mul_eq_mul_left (Nat.card_pos (α := ↥Q)) hcardZ0
  have hrangeΦ : φZ.range ≤ Φ := by
    rintro _ ⟨z, rfl⟩
    exact hφZΦ z
  have hrangeEq : φZ.range = Φ :=
    Subgroup.eq_of_le_of_card_ge hrangeΦ (by rw [hrangecard]; exact hΦcard)
  obtain ⟨cw, hcw⟩ := key w hwH hwR hwV₁ hwW₁
  have hwΦ : φ ⟨w, hwH⟩ ∈ φZ.range := by
    rw [hrangeEq]
    exact ⟨cw, fun e => eq_add_of_sub_eq' (hcw e)⟩
  obtain ⟨z, hz⟩ := hwΦ
  have h1 : φ (⟨w, hwH⟩ * (Subgroup.inclusion hZ0H z)⁻¹) = 1 := by
    rw [map_mul, map_inv]
    have : φ (Subgroup.inclusion hZ0H z) = φ ⟨w, hwH⟩ := hz
    rw [this, mul_inv_cancel]
  have h2 : w * (z : G)⁻¹ ∈ Q := (hφker _).mp h1
  have h3 : w = (w * (z : G)⁻¹) * z := by group
  rw [h3]
  exact Z0.mul_mem (hQZ0 h2) z.2

end CFSG.RankThree.GF2n.Stroth80
