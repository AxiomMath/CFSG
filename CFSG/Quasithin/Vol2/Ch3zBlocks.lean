module

public import CFSG.Quasithin.Vol2.Ch3zCoreMod2
public import CFSG.Quasithin.Background.B69SolvStruct
public import CFSG.LinearAlgebra.SL2MinimalFaithfulMatrix

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank G6

namespace Ch3z

variable {V : Type} [CommGroup V]

structure BlkCtx (X T M : Subgroup (MulAut V)) (𝓗 : Finset (Subgroup (MulAut V))) : Prop where
  hV : ∀ v : V, v ^ 2 = 1
  mp : MinParabolic X T M
  irr : ∀ W : Subgroup V, (∀ x ∈ X, ∀ w ∈ W, x w ∈ W) → W = ⊥ ∨ W = ⊤
  nt : ∃ v : V, v ≠ 1
  sc : B69.StructConcl X T M 𝓗
  ffne : ffJ X ≠ ⊥

variable {X T M : Subgroup (MulAut V)} {𝓗 : Finset (Subgroup (MulAut V))}

theorem BlkCtx.mem_le (h : BlkCtx X T M 𝓗) {H : Subgroup (MulAut V)} (hH : H ∈ 𝓗) : H ≤ X :=
  h.sc.1 H hH

theorem BlkCtx.fixV_ffJ (h : BlkCtx X T M 𝓗) : fixV (ffJ X) = ⊥ := by
  have hinv : ∀ x ∈ X, ∀ w ∈ fixV (ffJ X), x w ∈ fixV (ffJ X) := by
    intro x hx w hw y hy
    have hn : x⁻¹ * y * x ∈ ffJ X := by
      have := (Subgroup.mem_normalizer_iff.mp (B6.le_normalizer_ffJ X (X.inv_mem hx)) y).mp hy
      simpa using this
    have h1 := hw _ hn
    have e : y (x w) = x ((x⁻¹ * y * x) w) := by simp [MulAut.mul_apply]
    rw [e, h1]
  rcases h.irr _ hinv with h0 | h0
  · exact h0
  · exfalso
    apply h.ffne
    rw [eq_bot_iff]
    intro y hy
    rw [Subgroup.mem_bot]
    refine MulEquiv.ext fun v => ?_
    have : v ∈ fixV (ffJ X) := by rw [h0]; trivial
    exact this y hy

theorem BlkCtx.commV_ffJ (h : BlkCtx X T M 𝓗) : commV (ffJ X) = ⊤ := by
  have hinv : ∀ x ∈ X, ∀ w ∈ commV (ffJ X), x w ∈ commV (ffJ X) := by
    intro x hx w hw
    unfold commV at hw ⊢
    induction hw using Subgroup.closure_induction with
    | mem c hc =>
      obtain ⟨y, hy, v, rfl⟩ := hc
      apply Subgroup.subset_closure
      refine ⟨x * y * x⁻¹, ?_, x v, ?_⟩
      · exact (Subgroup.mem_normalizer_iff.mp (B6.le_normalizer_ffJ X hx) y).mp hy
      · simp [MulAut.mul_apply]
    | one => simp
    | mul a b _ _ iha ihb => simpa using (Subgroup.closure _).mul_mem iha ihb
    | inv a _ ih => simpa using (Subgroup.closure _).inv_mem ih
  rcases h.irr _ hinv with h0 | h0
  · exfalso
    apply h.ffne
    rw [eq_bot_iff]
    intro y hy
    rw [Subgroup.mem_bot]
    refine MulEquiv.ext fun v => ?_
    have : y v * v⁻¹ ∈ commV (ffJ X) := Subgroup.subset_closure ⟨y, hy, v, rfl⟩
    rw [h0, Subgroup.mem_bot, mul_inv_eq_one] at this
    exact this
  · exact h0

theorem BlkCtx.iSup_comm (h : BlkCtx X T M 𝓗) : ⨆ H ∈ 𝓗, commV H = ⊤ := by
  have h5 := h.sc.2.2.2.2.1
  rw [h.fixV_ffJ, h.commV_ffJ, sup_bot_eq, sup_bot_eq] at h5
  exact h5.symm

theorem BlkCtx.inf_iSup_comm (h : BlkCtx X T M 𝓗) {H : Subgroup (MulAut V)} (hH : H ∈ 𝓗) :
    commV H ⊓ (⨆ H' ∈ 𝓗, ⨆ (_ : H' ≠ H), commV H') = ⊥ := by
  have h6 := h.sc.2.2.2.2.2.1 H hH
  rwa [h.fixV_ffJ, sup_bot_eq, sup_bot_eq] at h6

theorem BlkCtx.act_commV_of_ne (h : BlkCtx X T M 𝓗) {H H' : Subgroup (MulAut V)} (hH : H ∈ 𝓗)
    (hH' : H' ∈ 𝓗) (hne : H ≠ H') {a : MulAut V} (ha : a ∈ H') {v : V} (hv : v ∈ commV H) :
    a v = v :=
  (commSub_eq_bot_iff.1 (h.sc.2.2.2.2.2.2.1 H hH H' hH' hne)) hv a ha

theorem BlkCtx.comm_of_ne (h : BlkCtx X T M 𝓗) {H H' : Subgroup (MulAut V)} (hH : H ∈ 𝓗)
    (hH' : H' ∈ 𝓗) (hne : H ≠ H') {a b : MulAut V} (ha : a ∈ H) (hb : b ∈ H') : a * b = b * a :=
  h.sc.2.2.1 H hH H' hH' hne a ha b hb

theorem BlkCtx.inf_blocks (h : BlkCtx X T M 𝓗) {H : Subgroup (MulAut V)} (hH : H ∈ 𝓗) :
    H ⊓ (⨆ H' ∈ 𝓗, ⨆ (_ : H' ≠ H), H') = ⊥ :=
  h.sc.2.2.2.1 H hH

theorem BlkCtx.trans (h : BlkCtx X T M 𝓗) {H H' : Subgroup (MulAut V)} (hH : H ∈ 𝓗)
    (hH' : H' ∈ 𝓗) : ∃ t ∈ T, B6.conjSub t H = H' :=
  h.sc.2.2.2.2.2.2.2.1 H hH H' hH'

theorem BlkCtx.eq_sup (h : BlkCtx X T M 𝓗) : X = ffJ X ⊔ T :=
  h.sc.2.2.2.2.2.2.2.2.1

theorem BlkCtx.ffJ_eq (h : BlkCtx X T M 𝓗) : ffJ X = ⨆ H ∈ 𝓗, H :=
  h.sc.2.1

theorem BlkCtx.types (h : BlkCtx X T M 𝓗) :
    ∀ H ∈ 𝓗,
    (∃ e : ℕ, 1 ≤ e ∧ BinaryNaturalSL H (commV H) (commV H ⊓ fixV (ffJ X)) 2 e ∧
      M ⊓ H = H ⊓ Subgroup.normalizer ((T ⊓ H : Subgroup (MulAut V)) : Set (MulAut V))) ∨
    (∃ k : ℕ, 1 ≤ k ∧ ∃ π : Equiv.Perm (Fin (2 * k + 1)) →* ↥H,
      (FFModel.symDn (2 * k + 1)).RealizesVia H (commV H) ⊥ π ∧
      (M ⊓ H).subgroupOf H =
        (MulAction.stabilizer (Equiv.Perm (Fin (2 * k + 1))) (⟨0, by omega⟩ : Fin (2 * k + 1))).map π) :=
  h.sc.2.2.2.2.2.2.2.2.2

@[expose] def NatBlockData (H : Subgroup (MulAut V)) (U : Subgroup V) (e : ℕ) : Prop :=
  ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = 2 ^ e ∧
    ∃ (π : Matrix.SpecialLinearGroup (Fin 2) K →* ↥H) (β : ↥U →* Multiplicative (Fin 2 → K)),
      Function.Surjective π ∧ Function.Bijective β ∧
      ∀ (γ : Matrix.SpecialLinearGroup (Fin 2) K) (u : ↥U)
        (hu : ((π γ : ↥H) : MulAut V) (u : V) ∈ U),
        β ⟨((π γ : ↥H) : MulAut V) (u : V), hu⟩ =
          Multiplicative.ofAdd ((γ : Matrix (Fin 2) (Fin 2) K).mulVec (Multiplicative.toAdd (β u)))

@[expose] noncomputable def quotTopBotEquiv (A : Type) [Group A] :
    ↥(⊤ : Subgroup A) ⧸ (⊥ : Subgroup A).subgroupOf ⊤ ≃* A :=
  ((QuotientGroup.quotientMulEquivOfEq (by simp : (⊥ : Subgroup A).subgroupOf ⊤ = ⊥)).trans
    QuotientGroup.quotientBot).trans Subgroup.topEquiv

theorem quotTopBotEquiv_mk (A : Type) [Group A] (m : ↥(⊤ : Subgroup A)) :
    quotTopBotEquiv A (QuotientGroup.mk m) = (m : A) := rfl

theorem natBlockData_of_binaryNatural {H : Subgroup (MulAut V)} {U : Subgroup V} {e : ℕ}
    (h : BinaryNaturalSL H U ⊥ 2 e) : NatBlockData H U e := by
  obtain ⟨K, instK, instF, hK, π', hπs, -, -, -, -, -, -, β', hβs, hβz, hβeq⟩ := h
  let π'' : ↥(CFSG.Assembly.LowTwoRank.StatedSL 2 K) →* ↥H := π'
  let β'' : ↥U →* ↥(⊤ : Subgroup (Multiplicative (Fin 2 → K))) ⧸
      (⊥ : Subgroup (Multiplicative (Fin 2 → K))).subgroupOf ⊤ := β'
  have hπs'' : Function.Surjective π'' := hπs
  have hβs'' : Function.Surjective β'' := hβs
  have hβz'' : ∀ u : ↥U, β'' u = 1 ↔ (u : V) ∈ (⊥ : Subgroup V) := hβz
  have hβeq'' : ∀ (γ : ↥(CFSG.Assembly.LowTwoRank.StatedSL 2 K)) (u : ↥U)
      (m : ↥(⊤ : Subgroup (Multiplicative (Fin 2 → K))))
      (hu : ((π'' γ : ↥H) : MulAut V) (u : V) ∈ U), β'' u = QuotientGroup.mk m →
      β'' ⟨((π'' γ : ↥H) : MulAut V) (u : V), hu⟩ =
        QuotientGroup.mk ⟨natAct (CFSG.Assembly.LowTwoRank.StatedSL 2 K) γ (m : Multiplicative (Fin 2 → K)), trivial⟩ :=
    fun γ u m hu hmk => hβeq γ u m hu trivial hmk
  refine ⟨K, instK, instF, hK, π''.comp (specialLinearGroupEquivStatedSL 2 K).toMonoidHom,
    (quotTopBotEquiv (Multiplicative (Fin 2 → K))).toMonoidHom.comp β'', ?_, ?_, ?_⟩
  · exact hπs''.comp (specialLinearGroupEquivStatedSL 2 K).surjective
  · constructor
    · intro a b hab
      have h1 : β'' a = β'' b := (quotTopBotEquiv _).injective hab
      have h2 : β'' (a * b⁻¹) = 1 := by rw [map_mul, map_inv, h1, mul_inv_cancel]
      have h3 := (hβz'' _).1 h2
      rw [Subgroup.mem_bot] at h3
      have h4 : a * b⁻¹ = 1 := Subtype.ext h3
      exact mul_inv_eq_one.1 h4
    · intro y
      obtain ⟨q, hq⟩ := hβs'' ((quotTopBotEquiv (Multiplicative (Fin 2 → K))).symm y)
      refine ⟨q, ?_⟩
      show quotTopBotEquiv (Multiplicative (Fin 2 → K)) (β'' q) = y
      rw [hq]
      exact MulEquiv.apply_symm_apply _ _
  · intro γ u hu
    obtain ⟨m, hm⟩ := QuotientGroup.mk_surjective (β'' u)
    have key := hβeq'' (specialLinearGroupEquivStatedSL 2 K γ) u m hu hm.symm
    change quotTopBotEquiv (Multiplicative (Fin 2 → K))
        (β'' ⟨((π'' (specialLinearGroupEquivStatedSL 2 K γ) : ↥H) : MulAut V) (u : V), hu⟩) =
      Multiplicative.ofAdd ((γ : Matrix (Fin 2) (Fin 2) K).mulVec
        (Multiplicative.toAdd (quotTopBotEquiv (Multiplicative (Fin 2 → K)) (β'' u))))
    rw [key, ← hm, quotTopBotEquiv_mk, quotTopBotEquiv_mk]
    rfl

theorem zpowers_allOnes_inf_core_eq_bot {n : ℕ} (hn : Odd n) :
    Subgroup.zpowers (allOnes n) ⊓ coreMod n = ⊥ := by
  rw [eq_bot_iff]
  rintro x ⟨hx1, hx2⟩
  rw [Subgroup.mem_bot]
  obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx1
  have h1 : ∀ i : Fin n, Multiplicative.toAdd (allOnes n ^ j) i = (j : ZMod 2) := by
    intro i
    simp [allOnes, toAdd_zpow]
  have hx2' : allOnes n ^ j ∈ coreMod n := hx2
  rw [mem_coreMod] at hx2'
  simp only [h1, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hx2'
  have hn1 : (n : ZMod 2) = 1 := hn.natCast_zmod_two
  rw [hn1, one_mul] at hx2'
  apply Multiplicative.toAdd.injective
  funext i
  rw [h1 i, hx2']
  rfl

@[expose] noncomputable def coreQuotEquiv {n : ℕ} (hn : Odd n) :
    (↥(coreMod n) ⧸ (Subgroup.zpowers (allOnes n) ⊓ coreMod n).subgroupOf (coreMod n)) ≃*
      ↥(coreMod n) :=
  (QuotientGroup.quotientMulEquivOfEq (by
    rw [zpowers_allOnes_inf_core_eq_bot hn, Subgroup.bot_subgroupOf])).trans
    QuotientGroup.quotientBot

theorem coreQuotEquiv_mk {n : ℕ} (hn : Odd n) (m : ↥(coreMod n)) :
    coreQuotEquiv hn (QuotientGroup.mk m) = m := rfl

theorem isSymCore_of_realizes' {H : Subgroup (MulAut V)} {U : Subgroup V} {k : ℕ}
    {π : Equiv.Perm (Fin (2 * k + 1)) →* ↥H}
    (h : (FFModel.symDn (2 * k + 1)).RealizesVia H U ⊥ π) :
    ∃ (θ : ↥H ≃* Equiv.Perm (Fin (2 * k + 1))) (β : ↥(coreMod (2 * k + 1)) →* V),
      (∀ σ, θ.symm σ = π σ) ∧
      (∀ (x : ↥H) (u : ↥(coreMod (2 * k + 1))),
        β (coreAct (2 * k + 1) (θ x) u) = (x : MulAut V) (β u)) ∧ β.range = U ∧ β.ker = ⊥ := by
  have hodd : Odd (2 * k + 1) := odd_two_mul_add_one k
  obtain ⟨hπs, -, -, hUinv, -, -, -, β', hβs, hβz, hβeq⟩ := h
  let β'' : ↥U →* (↥(coreMod (2 * k + 1)) ⧸
      (Subgroup.zpowers (allOnes (2 * k + 1)) ⊓ coreMod (2 * k + 1)).subgroupOf
        (coreMod (2 * k + 1))) := β'
  let β₀ : ↥U →* ↥(coreMod (2 * k + 1)) := (coreQuotEquiv hodd).toMonoidHom.comp β''
  have hβz'' : ∀ u : ↥U, β'' u = 1 ↔ (u : V) ∈ (⊥ : Subgroup V) := hβz
  have hβs'' : Function.Surjective β'' := hβs
  have hbij : Function.Bijective β₀ := by
    constructor
    · intro a b hab
      have h1 : β'' a = β'' b := (coreQuotEquiv hodd).injective hab
      have h2 : β'' (a * b⁻¹) = 1 := by rw [map_mul, map_inv, h1, mul_inv_cancel]
      have h3 := (hβz'' _).1 h2
      rw [Subgroup.mem_bot] at h3
      exact mul_inv_eq_one.1 (Subtype.ext h3)
    · intro y
      obtain ⟨q, hq⟩ := hβs'' ((coreQuotEquiv hodd).symm y)
      refine ⟨q, ?_⟩
      show coreQuotEquiv hodd (β'' q) = y
      rw [hq]
      exact MulEquiv.apply_symm_apply _ _
  have hβ₀eq : ∀ (σ : Equiv.Perm (Fin (2 * k + 1))) (w : ↥U)
      (hw : ((π σ : ↥H) : MulAut V) (w : V) ∈ U),
      β₀ ⟨((π σ : ↥H) : MulAut V) (w : V), hw⟩ = coreAct (2 * k + 1) σ (β₀ w) := by
    intro σ w hw
    have hmk : β'' w = QuotientGroup.mk (β₀ w) := by
      apply (coreQuotEquiv hodd).injective
      rw [coreQuotEquiv_mk]
      rfl
    have hm' : G6.permAct (2 * k + 1) σ ((β₀ w : ↥(coreMod (2 * k + 1))) : PermMod (2 * k + 1)) ∈
        coreMod (2 * k + 1) := permAct_mem_coreMod σ (β₀ w).2
    have key : β'' ⟨((π σ : ↥H) : MulAut V) (w : V), hw⟩ =
        QuotientGroup.mk ⟨G6.permAct (2 * k + 1) σ
          ((β₀ w : ↥(coreMod (2 * k + 1))) : PermMod (2 * k + 1)), hm'⟩ :=
      hβeq σ w (β₀ w) hw hm' hmk
    show coreQuotEquiv hodd (β'' ⟨_, hw⟩) = _
    rw [key, coreQuotEquiv_mk]
    rfl
  have hπinj : Function.Injective π := by
    rw [injective_iff_map_eq_one]
    intro σ hσ
    rw [← coreAct_eq_one_iff (2 * k + 1) hodd]
    refine MulEquiv.ext fun u => ?_
    obtain ⟨w, rfl⟩ := hbij.2 u
    have hw : ((π σ : ↥H) : MulAut V) (w : V) ∈ U := hUinv _ _ w.2
    have h1 := hβ₀eq σ w hw
    have h2v : ((π σ : ↥H) : MulAut V) (w : V) = (w : V) := by
      rw [hσ]
      rfl
    have h2 : (⟨((π σ : ↥H) : MulAut V) (w : V), hw⟩ : ↥U) = w := Subtype.ext h2v
    rw [h2] at h1
    exact h1.symm
  let θ : ↥H ≃* Equiv.Perm (Fin (2 * k + 1)) := (MulEquiv.ofBijective π ⟨hπinj, hπs⟩).symm
  let β₀e : ↥U ≃* ↥(coreMod (2 * k + 1)) := MulEquiv.ofBijective β₀ hbij
  refine ⟨θ, U.subtype.comp β₀e.symm.toMonoidHom, fun σ => rfl, ?_, ?_, ?_⟩
  · intro x u
    set σ := θ x with hσ
    have hπσ : π σ = x := by
      rw [hσ]
      exact (MulEquiv.ofBijective π ⟨hπinj, hπs⟩).apply_symm_apply x
    obtain ⟨w, rfl⟩ := hbij.2 u
    have hw : ((π σ : ↥H) : MulAut V) (w : V) ∈ U := hUinv _ _ w.2
    have h1 := hβ₀eq σ w hw
    have e1 : β₀e.symm (β₀ w) = w := β₀e.symm_apply_apply w
    have e2 : β₀e.symm (coreAct (2 * k + 1) σ (β₀ w)) = ⟨((π σ : ↥H) : MulAut V) (w : V), hw⟩ := by
      rw [← h1]
      exact β₀e.symm_apply_apply _
    show ((β₀e.symm (coreAct (2 * k + 1) σ (β₀ w)) : ↥U) : V) =
      ((x : ↥H) : MulAut V) ((β₀e.symm (β₀ w) : ↥U) : V)
    rw [e2, e1, ← hπσ]
  · apply le_antisymm
    · rintro _ ⟨u, rfl⟩
      exact (β₀e.symm u).2
    · intro v hv
      refine ⟨β₀e ⟨v, hv⟩, ?_⟩
      show ((β₀e.symm (β₀e ⟨v, hv⟩) : ↥U) : V) = v
      rw [MulEquiv.symm_apply_apply]
  · rw [eq_bot_iff]
    intro u hu
    rw [MonoidHom.mem_ker] at hu
    rw [Subgroup.mem_bot]
    have : β₀e.symm u = 1 := Subtype.ext hu
    exact β₀e.symm.injective (this.trans (map_one _).symm)

theorem isSymCore_of_realizes {H : Subgroup (MulAut V)} {U : Subgroup V} {k : ℕ}
    {π : Equiv.Perm (Fin (2 * k + 1)) →* ↥H}
    (h : (FFModel.symDn (2 * k + 1)).RealizesVia H U ⊥ π) : IsSymCore H U (2 * k + 1) := by
  obtain ⟨θ, β, -, h1, h2, h3⟩ := isSymCore_of_realizes' h
  exact ⟨θ, β, h1, h2, h3⟩

theorem pow_val_add {A : Type*} [CommGroup A] (g : A) (hg : g * g = 1) (a b : ZMod 2) :
    g ^ (a + b).val = g ^ a.val * g ^ b.val := by
  fin_cases a <;> fin_cases b
  · show g ^ 0 = g ^ 0 * g ^ 0
    simp
  · show g ^ 1 = g ^ 0 * g ^ 1
    simp
  · show g ^ 1 = g ^ 1 * g ^ 0
    simp
  · show g ^ 0 = g ^ 1 * g ^ 1
    simp [hg]

@[expose] noncomputable def evalHom {A : Type*} [CommGroup A] {n : ℕ} (f : Fin n → A)
    (hf : ∀ i, f i * f i = 1) : PermMod n →* A where
  toFun x := ∏ i, f i ^ (Multiplicative.toAdd x i).val
  map_one' := by simp
  map_mul' x y := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    simp only [toAdd_mul, Pi.add_apply]
    exact pow_val_add (f i) (hf i) _ _

theorem evalHom_apply {A : Type*} [CommGroup A] {n : ℕ} (f : Fin n → A) (hf : ∀ i, f i * f i = 1)
    (x : PermMod n) : evalHom f hf x = ∏ i, f i ^ (Multiplicative.toAdd x i).val := rfl

theorem evalHom_permAct {A : Type*} [CommGroup A] {n : ℕ} (f : Fin n → A) (hf : ∀ i, f i * f i = 1)
    (σ : Equiv.Perm (Fin n)) (x : PermMod n) :
    evalHom f hf (G6.permAct n σ x) = ∏ j, f (σ j) ^ (Multiplicative.toAdd x j).val := by
  rw [evalHom_apply]
  rw [← Equiv.prod_comp σ]
  refine Finset.prod_congr rfl fun j _ => ?_
  simp [permAct_apply]

theorem isSymCore_three_of_klein {U : Subgroup V} {H : Subgroup (MulAut V)}
    (hV : ∀ v : V, v ^ 2 = 1) (hU : Nat.card U = 4) (hUinv : ∀ h ∈ H, ∀ u ∈ U, h u ∈ U)
    (hfaith : ∀ h ∈ H, (∀ u ∈ U, h u = u) → h = 1) (hH : Nat.card H = 6) :
    IsSymCore H U 3 := by
  classical
  have hUfin : Finite U := Nat.finite_of_card_ne_zero (by omega)
  have hHfin : Finite H := Nat.finite_of_card_ne_zero (by omega)
  have hN : Nat.card {u : ↥U // u ≠ 1} = 3 := by
    have := Fintype.ofFinite U
    rw [Nat.card_eq_fintype_card] at hU ⊢
    rw [Fintype.card_subtype_compl]
    simp [hU]
  let ν : {u : ↥U // u ≠ 1} ≃ Fin 3 := Finite.equivFinOfCardEq hN
  let f : Fin 3 → V := fun i => (((ν.symm i : {u : ↥U // u ≠ 1}) : ↥U) : V)
  have hfU : ∀ i, f i ∈ U := fun i => ((ν.symm i : {u : ↥U // u ≠ 1}) : ↥U).2
  have hfne : ∀ i, f i ≠ 1 := fun i h1 => (ν.symm i).2 (Subtype.ext h1)
  have hf : ∀ i, f i * f i = 1 := fun i => by rw [← pow_two]; exact hV _
  have hfinj : Function.Injective f := fun a b hab =>
    ν.symm.injective (Subtype.ext (Subtype.ext hab))
  have hact : ∀ (h : ↥H) (i : Fin 3), (h : MulAut V) (f i) ≠ 1 := fun h i h1 =>
    hfne i (by simpa using (h : MulAut V).injective (h1.trans (map_one _).symm))
  let act : ↥H → Fin 3 → Fin 3 := fun h i =>
    ν ⟨⟨(h : MulAut V) (f i), hUinv h h.2 _ (hfU i)⟩, fun h1 => hact h i (congrArg Subtype.val h1)⟩
  have hact_f : ∀ (h : ↥H) (i : Fin 3), f (act h i) = (h : MulAut V) (f i) := by
    intro h i
    simp only [f, act, Equiv.symm_apply_apply]
  have hactinj : ∀ h : ↥H, Function.Injective (act h) := by
    intro h a b hab
    apply hfinj
    have h1 : (h : MulAut V) (f a) = (h : MulAut V) (f b) := by
      rw [← hact_f h a, ← hact_f h b, hab]
    exact (h : MulAut V).injective h1
  let θ₀ : ↥H →* Equiv.Perm (Fin 3) :=
    { toFun := fun h => Equiv.ofBijective (act h) (Finite.injective_iff_bijective.1 (hactinj h))
      map_one' := by
        apply Equiv.ext
        intro i
        apply hfinj
        show f (act 1 i) = f i
        rw [hact_f]
        rfl
      map_mul' := by
        intro h h'
        apply Equiv.ext
        intro i
        apply hfinj
        show f (act (h * h') i) = f (act h (act h' i))
        rw [hact_f, hact_f, hact_f]
        rfl }
  have hθ₀f : ∀ (h : ↥H) (i : Fin 3), f (θ₀ h i) = (h : MulAut V) (f i) := hact_f
  have hθ₀inj : Function.Injective θ₀ := by
    rw [injective_iff_map_eq_one]
    intro h hh
    apply Subtype.ext
    apply hfaith h h.2
    intro u hu
    by_cases hu1 : u = 1
    · rw [hu1, map_one]
    · obtain ⟨i, hi⟩ : ∃ i, f i = u := ⟨ν ⟨⟨u, hu⟩, fun h1 => hu1 (congrArg Subtype.val h1)⟩, by
        simp [f]⟩
      rw [← hi, ← hθ₀f h i, hh]
      rfl
  have hθ₀bij : Function.Bijective θ₀ := by
    have hc : Nat.card (Equiv.Perm (Fin 3)) ≤ Nat.card H := by
      rw [Nat.card_perm, hH]
      simp [Nat.factorial]
    exact hθ₀inj.bijective_of_nat_card_le hc
  let θ : ↥H ≃* Equiv.Perm (Fin 3) := MulEquiv.ofBijective θ₀ hθ₀bij
  let β : ↥(coreMod 3) →* V := (evalHom f hf).comp (coreMod 3).subtype
  have hβ_mem : ∀ v : ↥(coreMod 3), β v ∈ U := by
    intro v
    show ∏ i, f i ^ (Multiplicative.toAdd (v : PermMod 3) i).val ∈ U
    exact Subgroup.prod_mem U fun i _ => U.pow_mem (hfU i) _
  have hker : ∀ v : ↥(coreMod 3), β v = 1 → v = 1 := by
    intro v hv
    by_contra hv1
    obtain ⟨k, rfl⟩ := eq_uCore_of_ne_one3 v hv1
    have hv' : evalHom f hf (uvec 3 k) = 1 := hv
    rw [evalHom_apply, Fin.prod_univ_three] at hv'
    have h1 : ZMod.val (1 : ZMod 2) = 1 := rfl
    fin_cases k
    · simp [uvec, h1] at hv'
      exact absurd (hfinj (mul_right_cancel (hv'.trans (hf 2).symm))) (by decide)
    · simp [uvec, h1] at hv'
      exact absurd (hfinj (mul_right_cancel (hv'.trans (hf 2).symm))) (by decide)
    · simp [uvec, h1] at hv'
      exact absurd (hfinj (mul_right_cancel (hv'.trans (hf 1).symm))) (by decide)
  have hinj : Function.Injective β := by
    rw [injective_iff_map_eq_one]
    exact hker
  refine ⟨θ, β, ?_, ?_, ?_⟩
  · intro x u
    have hθx : ∀ j, f (θ x j) = (x : MulAut V) (f j) := fun j => hθ₀f x j
    show evalHom f hf (G6.permAct 3 (θ x) (u : PermMod 3)) = (x : MulAut V) (evalHom f hf u)
    rw [evalHom_permAct, evalHom_apply, map_prod]
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [hθx j, map_pow]
  · apply le_antisymm
    · rintro _ ⟨v, rfl⟩
      exact hβ_mem v
    · have hle : β.range ≤ U := by
        rintro _ ⟨v, rfl⟩
        exact hβ_mem v
      have hc : Nat.card (coreMod 3) = 4 := by
        rw [Nat.card_eq_fintype_card]
        decide
      have hrc : Nat.card β.range = 4 := by
        rw [← hc]
        exact (Nat.card_congr (Equiv.ofInjective β hinj)).symm
      exact (Subgroup.eq_of_le_of_card_ge hle (by rw [hrc, hU])).ge
  · exact (injective_iff_map_eq_one β).1 hinj |> fun h => by
      rw [eq_bot_iff]
      intro v hv
      rw [Subgroup.mem_bot]
      exact h v hv

theorem sl2_eq_one_of_mulVec {K : Type} [Field K] (γ : Matrix.SpecialLinearGroup (Fin 2) K)
    (h : ∀ w : Fin 2 → K, (γ : Matrix (Fin 2) (Fin 2) K).mulVec w = w) : γ = 1 := by
  ext i j
  have := congrFun (h (Pi.single j 1)) i
  simp at this
  rw [this, Matrix.SpecialLinearGroup.coe_one, Matrix.one_apply, Pi.single_apply]

theorem isSymCore_three_of_natBlock {H : Subgroup (MulAut V)} {U : Subgroup V}
    (hV : ∀ v : V, v ^ 2 = 1) (hUinv : ∀ h ∈ H, ∀ u ∈ U, h u ∈ U)
    (hN : NatBlockData H U 1) : IsSymCore H U 3 := by
  obtain ⟨K, instK, instF, hK, π, β, hπs, hβ, hβeq⟩ := hN
  have htriv : ∀ γ : Matrix.SpecialLinearGroup (Fin 2) K,
      (∀ u ∈ U, ((π γ : ↥H) : MulAut V) u = u) → γ = 1 := by
    intro γ hγ
    apply sl2_eq_one_of_mulVec
    intro w
    obtain ⟨u, hu⟩ := hβ.2 (Multiplicative.ofAdd w)
    have hu' := hUinv _ (π γ).2 _ u.2
    have h1 := hβeq γ u hu'
    have h2 : (⟨((π γ : ↥H) : MulAut V) (u : V), hu'⟩ : ↥U) = u := Subtype.ext (hγ _ u.2)
    rw [h2, hu] at h1
    have h3 := congrArg Multiplicative.toAdd h1
    simpa using h3.symm
  have hπinj : Function.Injective π := by
    rw [injective_iff_map_eq_one]
    intro γ hγ
    refine htriv γ fun u _ => ?_
    rw [hγ]
    rfl
  have hH : Nat.card H = 6 := by
    have hbij : Function.Bijective π := ⟨hπinj, hπs⟩
    rw [← Nat.card_congr (Equiv.ofBijective π hbij),
      CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two K, hK]
    norm_num
  have hU : Nat.card U = 4 := by
    rw [Nat.card_congr (Equiv.ofBijective β hβ)]
    have := Fintype.ofFinite K
    have hK' : Fintype.card K = 2 := by rw [← Nat.card_eq_fintype_card, hK]; norm_num
    rw [Nat.card_eq_fintype_card]
    simp [hK']
  refine isSymCore_three_of_klein hV hU hUinv ?_ hH
  intro h hh hfix
  obtain ⟨γ, hγ⟩ := hπs ⟨h, hh⟩
  have : γ = 1 := htriv γ fun u hu => by rw [hγ]; exact hfix u hu
  rw [this, map_one] at hγ
  exact congrArg Subtype.val hγ.symm

theorem exists_mem_eq_on_of_normalizes {H : Subgroup (MulAut V)} {W : Subgroup V} {m : ℕ}
    (hm : m = 3 ∨ m = 5 ∨ m = 7) (hH : IsSymCore H W m) (x : MulAut V) (hxW : ∀ w ∈ W, x w ∈ W)
    (hxW' : ∀ w ∈ W, x⁻¹ w ∈ W) (hx : x ∈ Subgroup.normalizer (H : Set (MulAut V))) :
    ∃ h ∈ H, ∀ w ∈ W, x w = h w := by
  obtain ⟨θ, β, hβeq, hβr, hβk⟩ := hH
  have hβinj : Function.Injective β := by
    rw [injective_iff_map_eq_one]
    intro u hu
    have : u ∈ β.ker := hu
    rw [hβk] at this
    simpa using this
  have hβW : ∀ u, β u ∈ W := fun u => hβr ▸ ⟨u, rfl⟩
  have hsurj : ∀ w ∈ W, ∃ u, β u = w := fun w hw => by
    have : w ∈ β.range := by rw [hβr]; exact hw
    exact this
  choose x' hx' using fun u : ↥(coreMod m) => hsurj (x (β u)) (hxW _ (hβW u))
  choose x'' hx'' using fun u : ↥(coreMod m) => hsurj (x⁻¹ (β u)) (hxW' _ (hβW u))
  have hx'mul : ∀ u v, x' (u * v) = x' u * x' v := fun u v => hβinj (by
    calc β (x' (u * v)) = x (β (u * v)) := hx' _
      _ = x (β u) * x (β v) := by rw [map_mul, map_mul]
      _ = β (x' u) * β (x' v) := by rw [hx', hx']
      _ = β (x' u * x' v) := (map_mul β _ _).symm)
  have hlr : ∀ u, x'' (x' u) = u := fun u => hβinj (by
    rw [hx'', hx', MulAut.inv_apply_self])
  have hrl : ∀ u, x' (x'' u) = u := fun u => hβinj (by
    rw [hx', hx'', MulAut.apply_inv_self])
  let xe : MulAut (coreMod m) :=
    { toFun := x', invFun := x'', left_inv := hlr, right_inv := hrl, map_mul' := hx'mul }
  have hxe : ∀ u, β (xe u) = x (β u) := hx'
  have hxe' : ∀ u, β (xe⁻¹ u) = x⁻¹ (β u) := hx''
  have hβσ : ∀ (σ : Equiv.Perm (Fin m)) (u : ↥(coreMod m)),
      β (coreAct m σ u) = ((θ.symm σ : ↥H) : MulAut V) (β u) := fun σ u => by
    have := hβeq (θ.symm σ) u
    rwa [MulEquiv.apply_symm_apply] at this
  have hN : ∀ σ : Equiv.Perm (Fin m), ∃ τ : Equiv.Perm (Fin m),
      xe * coreAct m σ * xe⁻¹ = coreAct m τ := by
    intro σ
    have hg : ((θ.symm σ : ↥H) : MulAut V) ∈ H := (θ.symm σ).2
    have hconj : x * ((θ.symm σ : ↥H) : MulAut V) * x⁻¹ ∈ H := by
      have := (Subgroup.mem_normalizer_iff.mp hx _).mp hg
      exact this
    refine ⟨θ ⟨_, hconj⟩, MulEquiv.ext fun u => hβinj ?_⟩
    show β (xe (coreAct m σ (xe⁻¹ u))) = β (coreAct m (θ ⟨_, hconj⟩) u)
    rw [hxe, hβσ, hxe', hβeq]
    simp [MulAut.mul_apply]
  obtain ⟨σ₀, hσ₀⟩ : ∃ σ₀ : Equiv.Perm (Fin m), xe = coreAct m σ₀ := by
    rcases hm with rfl | rfl | rfl
    · exact normLemma 3 (Or.inl rfl) xe hN
    · exact normLemma 5 (Or.inr rfl) xe hN
    · exact normLemma7 xe hN
  refine ⟨((θ.symm σ₀ : ↥H) : MulAut V), (θ.symm σ₀).2, fun w hw => ?_⟩
  obtain ⟨u, rfl⟩ := hsurj w hw
  rw [← hxe, hσ₀, hβσ]

end Ch3z

end CFSG.Quasithin
