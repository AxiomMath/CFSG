module

public import CFSG.Quasithin.Recognition.Kleidman.F204.O2Rep

public section

namespace CFSG.Quasithin.Kleidman.F204

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin CFSG.Quasithin.F7
  CFSG.Quasithin.FA5 CFSG.OrderReductions.FrattiniAutomorphisms CFSG
  CFSG.QuasithinUnique.A5.Delta5

open scoped IsMulCommutative commutatorElement

set_option linter.unusedSectionVars false

variable {G : Type} [Group G] [Finite G] {L1 L2 S D X Z : Subgroup G}

@[expose] def Ygen (L1 L2 S Z : Subgroup G) (x0 : G) : Set G :=
  {z | z ∈ Q1 L1 L2 S ∧ ∃ j : ℤ, (x0 ^ j)⁻¹ * z * x0 ^ j ∈ Frame.Z2 L1 L2 S Z}

@[expose] def Tsub (L1 L2 S Z : Subgroup G) (x0 : G) : Subgroup G :=
  Subgroup.closure (Ygen L1 L2 S Z x0)

section T

variable (F : Frame L1 L2 S D X) {x0 : G} (hx0 : x0 ∈ X)

omit [Finite G] in
theorem Tsub_le_Q1 : Tsub L1 L2 S Z x0 ≤ Q1 L1 L2 S :=
  (Subgroup.closure_le _).mpr fun _ hz => hz.1

include F hx0

theorem x0_conj_Q1 {q : G} (hq : q ∈ Q1 L1 L2 S) : x0 * q * x0⁻¹ ∈ Q1 L1 L2 S := by
  have hP : x0 ∈ P1 L1 L2 S := F.mem_P1_of_mem_X hx0
  exact (Subgroup.mem_normalizer_iff.mp (P1_le_normalizer_Q1 L1 L2 S hP) q).mp hq

theorem x0_conj_Tsub {τ : G} (hτ : τ ∈ Tsub L1 L2 S Z x0) : x0 * τ * x0⁻¹ ∈ Tsub L1 L2 S Z x0 := by
  have : Tsub L1 L2 S Z x0 ≤ (Tsub L1 L2 S Z x0).comap (MulAut.conj x0).toMonoidHom := by
    refine (Subgroup.closure_le _).mpr fun z hz => ?_
    obtain ⟨hzQ, j, hj⟩ := hz
    refine Subgroup.mem_comap.mpr (Subgroup.subset_closure ⟨?_, j + 1, ?_⟩)
    · exact x0_conj_Q1 F hx0 hzQ
    · have e : (x0 ^ (j + 1))⁻¹ * (x0 * z * x0⁻¹) * x0 ^ (j + 1) =
          (x0 ^ j)⁻¹ * z * x0 ^ j := by group
      show (x0 ^ (j + 1))⁻¹ * (x0 * z * x0⁻¹) * x0 ^ (j + 1) ∈ _
      rw [e]; exact hj
  exact this hτ

theorem d_conj_Tsub (_hZ : ZData L1 L2 S Z) {d : G} (hd : d ∈ D) {τ : G}
    (hτ : τ ∈ Tsub L1 L2 S Z x0) : d * τ * d⁻¹ ∈ Tsub L1 L2 S Z x0 := by
  have hdB : d ∈ bigB L1 L2 S := F.D_le_B hd
  have hdP1 : d ∈ P1 L1 L2 S := (le_sup_right : bigB L1 L2 S ≤ P1 L1 L2 S) hdB
  have hdP2 : d ∈ P2 L1 L2 S := (le_sup_right : bigB L1 L2 S ≤ P2 L1 L2 S) hdB
  have hdc : Commute d x0 := (Subgroup.mem_centralizer_iff.mp (F.D_cent hd) x0 hx0).symm
  have : Tsub L1 L2 S Z x0 ≤ (Tsub L1 L2 S Z x0).comap (MulAut.conj d).toMonoidHom := by
    refine (Subgroup.closure_le _).mpr fun z hz => ?_
    obtain ⟨hzQ, j, hj⟩ := hz
    refine Subgroup.mem_comap.mpr (Subgroup.subset_closure ⟨?_, j, ?_⟩)
    · exact (Subgroup.mem_normalizer_iff.mp (P1_le_normalizer_Q1 L1 L2 S hdP1) z).mp hzQ
    · have hc : Commute d (x0 ^ j) := hdc.zpow_right j
      have e : (x0 ^ j)⁻¹ * (d * z * d⁻¹) * x0 ^ j =
          d * ((x0 ^ j)⁻¹ * z * x0 ^ j) * d⁻¹ := by
        have h1 : (x0 ^ j)⁻¹ * d * x0 ^ j = d := by
          rw [mul_assoc, hc.eq, ← mul_assoc, inv_mul_cancel, one_mul]
        have h2 : (x0 ^ j)⁻¹ * d⁻¹ * x0 ^ j = d⁻¹ := by
          rw [mul_assoc, hc.inv_left.eq, ← mul_assoc, inv_mul_cancel, one_mul]
        calc (x0 ^ j)⁻¹ * (d * z * d⁻¹) * x0 ^ j
            = ((x0 ^ j)⁻¹ * d * x0 ^ j) * ((x0 ^ j)⁻¹ * z * x0 ^ j) *
              ((x0 ^ j)⁻¹ * d⁻¹ * x0 ^ j) := by group
          _ = d * ((x0 ^ j)⁻¹ * z * x0 ^ j) * d⁻¹ := by rw [h1, h2]
      show (x0 ^ j)⁻¹ * (d * z * d⁻¹) * x0 ^ j ∈ _
      rw [e]
      exact Z2_norm hdP2 hj
  exact this hτ

abbrev VV (F : Frame L1 L2 S D X) {x0 : G} (hx0 : x0 ∈ X) :=
  UQ L1 L2 S ⧸ O2Alg.fixSub (theta L1 L2 S ⟨x0, F.mem_P1_of_mem_X hx0⟩)

@[expose] noncomputable def evQ : ↥(Q1 L1 L2 S) →* Multiplicative (VV F hx0) where
  toFun q := Multiplicative.ofAdd (Submodule.Quotient.mk (mu q))
  map_one' := by simp [mu_one]
  map_mul' q q' := by simp [mu_mul, Submodule.Quotient.mk_add]

@[expose] noncomputable def psiT : ↥(Tsub L1 L2 S Z x0) →* Multiplicative (VV F hx0) :=
  (evQ F hx0).comp (Subgroup.inclusion Tsub_le_Q1)

theorem psiT_eq_one_iff (τ : ↥(Tsub L1 L2 S Z x0)) :
    psiT F hx0 τ = 1 ↔
      mu (⟨τ, Tsub_le_Q1 τ.2⟩ : ↥(Q1 L1 L2 S)) ∈
        O2Alg.fixSub (theta L1 L2 S ⟨x0, F.mem_P1_of_mem_X hx0⟩) := by
  show Multiplicative.ofAdd (Submodule.Quotient.mk (mu (⟨τ, Tsub_le_Q1 τ.2⟩ : ↥(Q1 L1 L2 S)))) = 1 ↔ _
  rw [← ofAdd_zero, Multiplicative.ofAdd.injective.eq_iff, Submodule.Quotient.mk_eq_zero]

end T

section Ker

variable (hZ : ZData L1 L2 S Z) {a : G} (ha : a ∈ Frame.Z2 L1 L2 S Z) (haQ : a ∉ Q1 L1 L2 S)
  {x0 : G} (hx0 : x0 ∈ X) (hx05 : x0 ^ 5 = 1) (hx01 : x0 ≠ 1) (F : Frame L1 L2 S D X)
include F hx0 hZ ha haQ hx05 hx01

theorem psiT_ker_central (τ : ↥(Tsub L1 L2 S Z x0)) (hτ : psiT F hx0 τ = 1) :
    ∀ σ : ↥(Tsub L1 L2 S Z x0), τ * σ = σ * τ := by
  have hmu := (psiT_eq_one_iff F hx0 τ).mp hτ
  have hx0P : x0 ∈ P1 L1 L2 S := F.mem_P1_of_mem_X hx0
  set X0 : ↥(P1 L1 L2 S) := ⟨x0, hx0P⟩ with hX0
  set τQ : ↥(Q1 L1 L2 S) := ⟨τ, Tsub_le_Q1 τ.2⟩ with hτQ
  have hQ2j : ∀ j : ℤ, (x0 ^ j)⁻¹ * (τ : G) * x0 ^ j ∈ Q2 L1 L2 S := by
    intro j
    have hjP : (x0 ^ j)⁻¹ ∈ P1 L1 L2 S := (P1 L1 L2 S).inv_mem ((P1 L1 L2 S).zpow_mem hx0P j)
    set g : ↥(P1 L1 L2 S) := ⟨(x0 ^ j)⁻¹, hjP⟩ with hg
    have hgX : g = X0 ^ (-j) := Subtype.ext (by simp [hg, hX0, zpow_neg])
    have hfix : theta L1 L2 S g (mu τQ) = mu τQ := by
      rw [hgX, map_zpow]
      have hx : theta L1 L2 S X0 (mu τQ) = mu τQ := hmu
      have hst : theta L1 L2 S X0 ∈ MulAction.stabilizer (UQ L1 L2 S ≃ₗ[ZMod 2] UQ L1 L2 S)
          (mu τQ) := by
        rw [MulAction.mem_stabilizer_iff]; exact hx
      have := Subgroup.zpow_mem _ hst (-j)
      rw [MulAction.mem_stabilizer_iff] at this
      exact this
    have hmem : (g : G) * (τQ : G) * (g : G)⁻¹ ∈ Q1 L1 L2 S := theta_mem_conj g τQ
    rw [theta_apply] at hfix
    have hq := mem_Q2_of_fix F hZ ha haQ hx0 hx05 hx01
      (⟨(g : G) * (τQ : G) * (g : G)⁻¹, hmem⟩ : ↥(Q1 L1 L2 S)) (by rw [hfix]; exact hmu)
    have e : (g : G) * (τQ : G) * (g : G)⁻¹ = (x0 ^ j)⁻¹ * (τ : G) * x0 ^ j := by
      simp [hg, hτQ]
    rw [show ((⟨(g : G) * (τQ : G) * (g : G)⁻¹, hmem⟩ : ↥(Q1 L1 L2 S)) : G) =
      (g : G) * (τQ : G) * (g : G)⁻¹ from rfl, e] at hq
    exact hq
  rintro ⟨σ0, hσ0⟩
  apply Subtype.ext
  show (τ : G) * σ0 = σ0 * (τ : G)
  have hσ : σ0 ∈ Subgroup.closure (Ygen L1 L2 S Z x0) := hσ0
  clear hσ0
  induction hσ using Subgroup.closure_induction with
  | mem z hz =>
    obtain ⟨hzQ, j, hj⟩ := hz
    have hcomm := F.Z2_comm hZ _ hj _ (hQ2j j)
    set τ' := (x0 ^ j)⁻¹ * (τ : G) * x0 ^ j with hτ'
    set z' := (x0 ^ j)⁻¹ * z * x0 ^ j with hz'
    calc (τ : G) * z = (x0 ^ j * τ' * (x0 ^ j)⁻¹) * (x0 ^ j * z' * (x0 ^ j)⁻¹) := by
          simp only [hτ', hz']; group
      _ = x0 ^ j * (τ' * z') * (x0 ^ j)⁻¹ := by group
      _ = x0 ^ j * (z' * τ') * (x0 ^ j)⁻¹ := by rw [hcomm.symm]
      _ = z * (τ : G) := by simp only [hτ', hz']; group
  | one => simp
  | mul x y _ _ hx hy =>
    calc (τ : G) * (x * y) = ((τ : G) * x) * y := by group
      _ = (x * (τ : G)) * y := by rw [hx]
      _ = x * ((τ : G) * y) := by group
      _ = x * (y * (τ : G)) := by rw [hy]
      _ = (x * y) * (τ : G) := by group
  | inv x _ hx =>
    calc (τ : G) * x⁻¹ = x⁻¹ * (x * (τ : G)) * x⁻¹ := by group
      _ = x⁻¹ * ((τ : G) * x) * x⁻¹ := by rw [hx]
      _ = x⁻¹ * (τ : G) := by group

theorem psiT_surjective {y : G} (hyT : y ∈ Tsub L1 L2 S Z x0) (hyQ2 : y ∉ Q2 L1 L2 S) :
    Function.Surjective (psiT (Z := Z) F hx0) := by
  classical
  have hx0P : x0 ∈ P1 L1 L2 S := F.mem_P1_of_mem_X hx0
  have haS : a ∈ S := F.Q2_le_S (F.Z2_le_Q2 hZ ha)
  have haa : a * a = 1 := F.Z2_sq hZ a ha
  obtain ⟨hx5, htt, htx⟩ := theta_rel F hx0 hx05 haS haa haQ
  have hrk := finrank_range_theta_le F hZ ha
  have hne := theta_x_ne F hx0 hx05 hx01
  obtain ⟨-, hdim, -⟩ := O2Alg.K_main _ _ hx5 htt htx hrk hne
  set xθ := theta L1 L2 S ⟨x0, hx0P⟩ with hxθ
  set tθ := theta L1 L2 S ⟨a, F.mem_P1_of_mem_S haS⟩ with htθ
  have hfpf := O2Alg.quot_fpf xθ tθ hx5 htt htx
  have hxq5 := O2Alg.xq_pow xθ tθ hx5 htt htx
  let psiv : ↥(Tsub L1 L2 S Z x0) → VV F hx0 := fun τ =>
    Submodule.Quotient.mk (mu (⟨τ, Tsub_le_Q1 τ.2⟩ : ↥(Q1 L1 L2 S)))
  have hpsiv_mul : ∀ τ σ : ↥(Tsub L1 L2 S Z x0), psiv (τ * σ) = psiv τ + psiv σ := by
    intro τ σ
    show Submodule.Quotient.mk (mu (⟨(τ * σ : ↥(Tsub L1 L2 S Z x0)), _⟩ : ↥(Q1 L1 L2 S))) = _
    have : (⟨((τ * σ : ↥(Tsub L1 L2 S Z x0)) : G), Tsub_le_Q1 (τ * σ).2⟩ : ↥(Q1 L1 L2 S)) =
        ⟨τ, Tsub_le_Q1 τ.2⟩ * ⟨σ, Tsub_le_Q1 σ.2⟩ := rfl
    rw [this, mu_mul, Submodule.Quotient.mk_add]
  have hpsiv_one : psiv 1 = 0 := by
    show Submodule.Quotient.mk (mu (⟨((1 : ↥(Tsub L1 L2 S Z x0)) : G), _⟩ : ↥(Q1 L1 L2 S))) = 0
    have : (⟨((1 : ↥(Tsub L1 L2 S Z x0)) : G), Tsub_le_Q1 (1 : ↥(Tsub L1 L2 S Z x0)).2⟩ :
        ↥(Q1 L1 L2 S)) = 1 := rfl
    rw [this, mu_one]
    rfl
  let ST : Submodule (ZMod 2) (VV F hx0) :=
    { carrier := Set.range psiv
      zero_mem' := ⟨1, hpsiv_one⟩
      add_mem' := by
        rintro _ _ ⟨τ, rfl⟩ ⟨σ, rfl⟩
        exact ⟨τ * σ, hpsiv_mul τ σ⟩
      smul_mem' := by
        intro c v hv
        have hc : c = 0 ∨ c = 1 := by revert c; decide
        rcases hc with rfl | rfl
        · rw [zero_smul]; exact ⟨1, hpsiv_one⟩
        · rw [one_smul]; exact hv }
  have hinv : ∀ w ∈ ST, O2Alg.xq xθ tθ hx5 htt htx w ∈ ST := by
    rintro _ ⟨τ, rfl⟩
    refine ⟨⟨x0 * τ * x0⁻¹, x0_conj_Tsub F hx0 τ.2⟩, ?_⟩
    show Submodule.Quotient.mk (mu (⟨x0 * τ * x0⁻¹, _⟩ : ↥(Q1 L1 L2 S))) =
      O2Alg.xq xθ tθ hx5 htt htx (Submodule.Quotient.mk
        (mu (⟨τ, Tsub_le_Q1 τ.2⟩ : ↥(Q1 L1 L2 S))))
    rw [O2Alg.xq_mk, hxθ, theta_apply]
  have hbt := O2Alg.eq_bot_or_top_of_invariant (O2Alg.xq xθ tθ hx5 htt htx) hxq5 hfpf hdim ST hinv
  have hne0 : ST ≠ ⊥ := by
    intro hbot
    have hyST : psiv ⟨y, hyT⟩ ∈ ST := ⟨_, rfl⟩
    rw [hbot, Submodule.mem_bot] at hyST
    have h0 : mu (⟨y, Tsub_le_Q1 hyT⟩ : ↥(Q1 L1 L2 S)) ∈ O2Alg.fixSub xθ :=
      (Submodule.Quotient.mk_eq_zero _).mp hyST
    exact hyQ2 (mem_Q2_of_fix F hZ ha haQ hx0 hx05 hx01 _ h0)
  have htop : ST = ⊤ := hbt.resolve_left hne0
  intro v
  have hv : Multiplicative.toAdd v ∈ ST := by rw [htop]; trivial
  obtain ⟨τ, hτ⟩ := hv
  exact ⟨τ, by
    apply Multiplicative.toAdd.injective
    exact hτ⟩

end Ker

end CFSG.Quasithin.Kleidman.F204
