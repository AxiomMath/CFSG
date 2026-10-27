module

public import CFSG.Quasithin.Background.E6TwentyFourA
public import CFSG.Quasithin.Background.E6Sixteen
public import CFSG.LocalAnalysis.QuasithinUnique.BenderInterfaces

public section

namespace CFSG.Quasithin

namespace E6

open CFSG.Open CFSG.QuasithinUnique
open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.Blueprint

section Statements

variable {G : Type} [Group G] {V : Subgroup G}

@[expose] def E611Data (hV : CFSG.Open.IsElemAbelian 2 V) (M U L X : Subgroup G) : Prop :=
  L ≤ Subgroup.centralizer (U : Set G) ∧
    (L.subgroupOf (Subgroup.centralizer (U : Set G))).Normal ∧ ¬ L ≤ M ∧
    V ⊓ Subgroup.centralizer (L : Set G) = U ∧
    X ≤ L ⊓ M ∧ IsCyclic (autI hV X) ∧ Nat.card (autI hV X) = 2 ^ E3.mQuot V U - 1 ∧
    U ⊓ ⁅V, X⁆ = ⊥ ∧ U ⊔ ⁅V, X⁆ = V ∧
    (∀ v ∈ ⁅V, X⁆, v ≠ 1 → ∀ x ∈ X, x * v = v * x → x ∈ Subgroup.centralizer (V : Set G)) ∧
    (∀ g ∈ M ⊓ Subgroup.normalizer (V : Set G), g ∈ Subgroup.normalizer (U : Set G) →
      ∀ x ∈ X, ∃ y ∈ X, g * x * g⁻¹ * y⁻¹ ∈ Subgroup.centralizer (V : Set G)) ∧
    (∀ g ∈ M ⊓ Subgroup.normalizer (V : Set G), g ∈ Subgroup.normalizer (U : Set G) →
      g ∈ Subgroup.normalizer (L : Set G)) ∧
    L ⊓ M ≤ X ∧
    ((((IsBlock2 (Subgroup.centralizer (U : Set G)) L ∧ IsLin2Type L (E3.mQuot V U)) ∨
        (IsComponentIn L (Subgroup.centralizer (U : Set G)) ∧
          (StatedClassicalModel (↥L ⧸ Subgroup.center ↥L) .PSL 2 2 (E3.mQuot V U) ∨
            SuzukiModel (↥L ⧸ Subgroup.center ↥L) 2 (E3.mQuot V U) ∨
            StatedClassicalModel (↥L ⧸ Subgroup.center ↥L) .PSU 3 2 (E3.mQuot V U)))) ∧
        ∀ p : ℕ, p.Prime → p ∣ 2 ^ E3.mQuot V U - 1 →
          ¬ p ∣ Nat.card ↥((L ⊓ M) ⊓ Subgroup.centralizer (V : Set G))) ∨
      (IsComponentIn L (Subgroup.centralizer (U : Set G)) ∧
        (StatedClassicalModel (↥L ⧸ Subgroup.center ↥L) .PSL 3 2 (E3.mQuot V U) ∨
          StatedClassicalModel ↥L .PSp 2 2 (E3.mQuot V U))))

@[expose] def E611Strong : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M V U : Subgroup G) (hV : CFSG.Open.IsElemAbelian 2 V),
    HypE61 T M V → U ∈ gammaE64 V M →
    (∀ W : Subgroup G, U < W → W ≤ V → Subgroup.centralizer (W : Set G) ≤ M) →
    1 < E3.mQuot V U → ∃ L X : Subgroup G, E611Data hV M U L X

@[expose] def E624Body (hV : CFSG.Open.IsElemAbelian 2 V) (M X : Subgroup G) (s : ℕ)
    (Y : Fin s → Subgroup (MulAut (IntMod V hV))) (Vs : Fin s → Subgroup (IntMod V hV)) :
    Prop :=
  ((⨆ i, Y i) = e624Y hV M X ∧ iSupIndep Y ∧
      ∀ i j, i ≠ j → ∀ a ∈ Y i, ∀ b ∈ Y j, a * b = b * a) ∧
    (fixV (e624Y hV M X) ⊓ commSub ⊤ (e624Y hV M X) = ⊥ ∧
      fixV (e624Y hV M X) ⊔ commSub ⊤ (e624Y hV M X) = ⊤) ∧
    ((⨆ i, Vs i) = commSub ⊤ (e624Y hV M X) ∧ iSupIndep Vs ∧
      ∀ i, commSub ⊤ (Y i) = Vs i ∧ commSub (Vs i) (Y i) = Vs i) ∧
    ((∀ φ ∈ autI hV M, ∀ i, ∃ j, (Y i).map (MulAut.conj φ).toMonoidHom = Y j) ∧
      ∀ i j, ∃ φ ∈ autI hV M, (Y i).map (MulAut.conj φ).toMonoidHom = Y j) ∧
    ((∃ i, autI hV X = Y i) ∨
      (Nat.card (autI hV X) = 3 ∧ ∃ i, autI hV X ≤ Y i ∧
        Y i = Subgroup.closure {ψ | ∃ φ ∈ Y i, ∃ ξ ∈ autI hV X, ψ = φ * ξ * φ⁻¹} ∧
        Nat.card (Y i) = 21 ∧ (∃ a ∈ Y i, ∃ b ∈ Y i, a * b ≠ b * a) ∧
        ∀ j, Nat.card (Vs j) = 8))

theorem e624Concl_iff (hV : CFSG.Open.IsElemAbelian 2 V) (M X : Subgroup G) :
    E624Concl hV M X ↔ ∃ s Y Vs, E624Body hV M X s Y Vs := Iff.rfl

@[expose] def E625Setting [Finite G] (T M V U : Subgroup G) (hV : CFSG.Open.IsElemAbelian 2 V) :
    Prop :=
  HypE61 T M V ∧ 2 < E3.mParam (autI hV M) ∧ U ∈ gammaE64 V M ∧
    (E3.mQuot V U : ℕ∞) = E3.rParam V ∧ 1 < E3.mQuot V U ∧
    E3.mQuot V U < E3.mParam (autI hV M)

end Statements

@[expose] def E625SLeTwo : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M V U L X : Subgroup G) (hV : CFSG.Open.IsElemAbelian 2 V),
    E625Setting T M V U hV → E611Data hV M U L X →
    ∀ (s : ℕ) (Y : Fin s → Subgroup (MulAut (IntMod V hV)))
      (Vs : Fin s → Subgroup (IntMod V hV)), E624Body hV M X s Y Vs → s ≤ 2

@[expose] def E625NotTwo : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M V U L X : Subgroup G) (hV : CFSG.Open.IsElemAbelian 2 V),
    E625Setting T M V U hV → E611Data hV M U L X →
    ∀ (Y : Fin 2 → Subgroup (MulAut (IntMod V hV))) (Vs : Fin 2 → Subgroup (IntMod V hV)),
      E624Body hV M X 2 Y Vs → Nat.card (autI hV X) = 3 → (∀ i, autI hV X ≠ Y i) → False

section Proof

variable {G : Type} [Group G] [Finite G] {T M V U X : Subgroup G}

omit [Finite G] in
theorem card_mulAut_eight' {W : Type*} [Group W] [Finite W] (hcomm : ∀ a b : W, a * b = b * a)
    (hsq : ∀ a : W, a ^ 2 = 1) (h8 : Nat.card W = 8) : Nat.card (MulAut W) = 168 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨e⟩ := CFSG.SectionRank.Ccomm.nonempty_mulEquiv_of_elementary (p := 2) hcomm hsq
    (n := 3) (by rw [h8]; norm_num)
  rw [CFSG.SectionRank.Ccomm.card_mulAut_eq_card_GL e, CFSG.SectionRank.Ccomm.card_GL_zmod]
  simp [Fin.prod_univ_succ]

theorem maximal_of_eq_rParam (h : HypE61 T M V) (hr : (E3.mQuot V U : ℕ∞) = E3.rParam V) :
    ∀ W : Subgroup G, U < W → W ≤ V → Subgroup.centralizer (W : Set G) ≤ M := by
  intro W hUW hWV
  by_contra hWM
  have hWN : ¬ Subgroup.centralizer (W : Set G) ≤ Subgroup.normalizer (V : Set G) :=
    fun hle => hWM (hle.trans h.normalizer_le)
  have h1 := rParam_le_mQuot hWV hWN
  rw [← hr] at h1
  have h2 := E3.mQuot_add hUW.le hWV
  have h3 : E3.mQuot W U ≠ 0 := fun h0 =>
    hUW.ne ((E3.mQuot_eq_zero_iff (h.isPGroup_V.to_le hWV) hUW.le).1 h0)
  have h4 : E3.mQuot V U ≤ E3.mQuot V W := by exact_mod_cast h1
  omega

theorem fixV_e624Y_eq_bot (hV : CFSG.Open.IsElemAbelian 2 V) (h : HypE61 T M V)
    (hU : U ∈ gammaE64 V M) (hfixmap : (fixV (autI hV X)).map (E3.valHom hV) = U) :
    fixV (e624Y hV M X) = ⊥ := by
  classical
  by_contra hne
  set W₀ := (fixV (e624Y hV M X)).map (E3.valHom hV) with hW₀def
  have hfix : fixV (e624Y hV M X) ≤ fixV (autI hV X) := fun v hv x hx =>
    hv x (autI_le_e624Y hV M X hx)
  have hW₀U : W₀ ≤ U := hfixmap ▸ Subgroup.map_mono hfix
  have hW₀1 : W₀ ≠ ⊥ := fun h0 =>
    hne ((Subgroup.map_eq_bot_iff_of_injective _ (E3.valHom_injective hV)).1 h0)
  have hW₀2 : IsPGroup 2 W₀ := h.isPGroup_V.to_le (E3.map_valHom_le hV _)
  have hYn : ∀ φ ∈ autI hV M, ∀ y ∈ e624Y hV M X, φ * y * φ⁻¹ ∈ e624Y hV M X := by
    intro φ hφ y hy
    refine Subgroup.closure_induction (p := fun y _ => φ * y * φ⁻¹ ∈ e624Y hV M X) ?_ ?_ ?_ ?_ hy
    · rintro _ ⟨ψ, hψ, ξ, hξ, rfl⟩
      exact Subgroup.subset_closure ⟨φ * ψ, (autI hV M).mul_mem hφ hψ, ξ, hξ, by group⟩
    · simp only [mul_one, mul_inv_cancel]
      exact Subgroup.one_mem _
    · intro a b _ _ ha hb
      have : φ * (a * b) * φ⁻¹ = (φ * a * φ⁻¹) * (φ * b * φ⁻¹) := by group
      rw [this]
      exact Subgroup.mul_mem _ ha hb
    · intro a _ ha
      have : φ * a⁻¹ * φ⁻¹ = (φ * a * φ⁻¹)⁻¹ := by group
      rw [this]
      exact Subgroup.inv_mem _ ha
  have hfixinv : ∀ φ ∈ autI hV M, ∀ v ∈ fixV (e624Y hV M X), φ v ∈ fixV (e624Y hV M X) := by
    intro φ hφ v hv y hy
    have h1 := hv _ (hYn _ ((autI hV M).inv_mem hφ) y hy)
    have h2 : (φ⁻¹ * y * φ⁻¹⁻¹) v = v := h1
    rw [inv_inv, MulAut.mul_apply, MulAut.mul_apply] at h2
    have h3 := congrArg (fun w => φ w) h2
    simp only [MulAut.apply_inv_self] at h3
    exact h3
  have hN : Subgroup.normalizer ((T ⊓ Subgroup.centralizer (V : Set G) : Subgroup G) : Set G) ⊓
      (M ⊓ Subgroup.normalizer (V : Set G)) ≤ Subgroup.normalizer (W₀ : Set G) := by
    rintro g ⟨-, hgM, hgN⟩
    have hle : W₀.map (MulAut.conj g).toMonoidHom ≤ W₀ := by
      rintro _ ⟨_, ⟨v, hv, rfl⟩, rfl⟩
      refine ⟨convI hV ⟨g, hgN⟩ v, hfixinv _ (convI_mem_autI hV hgM hgN) v hv, ?_⟩
      rw [E3.valHom_apply, convI_apply_val]
      rfl
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    exact Subgroup.eq_of_le_of_card_ge hle
      (Subgroup.card_map_of_injective (MulAut.conj g).injective).ge
  have huniq := h.isUniqueM_of_le hW₀1 hW₀2 hN
  apply hU.2.2.1
  exact (Subgroup.centralizer_le hW₀U).trans
    ((Subgroup.centralizer_le_normalizer _).trans huniq.1.2)

end Proof

section Main

theorem e625_of (h624 : E624Stmt) (h611 : E611Strong) (hS2 : E625SLeTwo) (hN2 : E625NotTwo) :
    E625Stmt := by
  intro G _ _ T M V U hV h hm hU hr hU1 hUm
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hW : ∀ w : IntMod V hV, w ^ 2 = 1 := IntMod.sq_eq_one
  have hset : E625Setting T M V U hV := ⟨h, hm, hU, hr, hU1, hUm⟩
  obtain ⟨L, X, hD⟩ := h611 G T M V U hV h hU (maximal_of_eq_rParam h hr) hU1
  have hD' := hD
  obtain ⟨hLU, -, -, -, hXLM, hXcyc, hXcard, hUX1, hUX2, hreg, hnorm, -⟩ := hD'
  have hXMU : X ≤ M ⊓ Subgroup.centralizer (U : Set G) :=
    le_inf (hXLM.trans inf_le_right) ((hXLM.trans inf_le_left).trans hLU)
  obtain ⟨s, Y, Vs, hB⟩ := (e624Concl_iff hV M X).1
    (h624 G T M V U X hV h hm hU hr hU1 hUm hXMU hXcyc hXcard hUX1 hUX2 hreg hnorm)
  have hs2 := hS2 G T M V U L X hV hset hD s Y Vs hB
  obtain ⟨hyp, hfixmap, hcardc⟩ :=
    hyp102_autI hV h hU hU1 hUm hXMU hXcyc hXcard hUX2 hreg hnorm
  have hB' := hB
  obtain ⟨⟨hYsup, hYind, -⟩, ⟨-, hfix2⟩, ⟨hVsup, hVind, hVi⟩, ⟨hperm, htrans⟩, hdich⟩ := hB'
  have hY0 : fixV (e624Y hV M X) = ⊥ := fixV_e624Y_eq_bot hV h hU hfixmap
  have hVtop : commSub ⊤ (e624Y hV M X) = ⊤ := by
    rw [hY0, bot_sup_eq] at hfix2
    exact hfix2
  have hXodd : Odd (Nat.card (autI hV X)) := hyp.1.2.2.2.1
  have hXne : autI hV X ≠ ⊥ := hyp.1.2.1
  have hUne : U ≠ ⊥ := hU.2.1
  have hYne : ∀ i j, Y i ≠ ⊥ → Y j ≠ ⊥ := by
    intro i j hi h0
    obtain ⟨φ, -, hφ⟩ := htrans i j
    rw [h0] at hφ
    exact hi ((Subgroup.map_eq_bot_iff_of_injective _ (MulAut.conj φ).injective).1 hφ)
  have hne : ∀ i, autI hV X ≠ Y i := by
    intro i hi
    have hVj : ∀ j, Nat.card (Vs j) = 2 ^ E3.mQuot V U := by
      intro j
      obtain ⟨φ, -, hφ⟩ := htrans i j
      rw [← (hVi j).1, ← hφ, Asc81c.commSub_map_conj,
        Subgroup.card_map_of_injective (φ : MulAut (IntMod V hV)).injective, ← hi, hcardc]
    interval_cases s
    · exact Fin.elim0 i
    ·
      apply hUne
      have h1 : Vs 0 = ⊤ := by
        rw [← hVtop, ← hVsup]
        exact le_antisymm (le_iSup Vs 0) (iSup_le fun j => by rw [Subsingleton.elim j 0])
      have h2 : commSub ⊤ (autI hV X) = ⊤ := by
        rw [hi, (hVi i).1, Subsingleton.elim i 0, h1]
      have h3 : fixV (autI hV X) = ⊥ := by
        have := Asc81c.fixV_inf_commSub_eq_bot' hW hXodd
        rwa [h2, inf_top_eq] at this
      rw [← hfixmap, h3, Subgroup.map_bot]
    ·
      have hsup2 : Vs 0 ⊔ Vs 1 = ⊤ := by
        rw [← hVtop, ← hVsup]
        exact le_antisymm (sup_le (le_iSup Vs 0) (le_iSup Vs 1))
          (iSup_le (Fin.forall_fin_two.2 ⟨le_sup_left, le_sup_right⟩))
      have hinf2 : Vs 0 ⊓ Vs 1 = ⊥ :=
        disjoint_iff.1 (hVind.pairwiseDisjoint (by decide : (0 : Fin 2) ≠ 1))
      have hcardW : Nat.card (IntMod V hV) = 2 ^ E3.mQuot V U * 2 ^ E3.mQuot V U := by
        have h1 := card_sup_mul_card_inf (Vs 0) (Vs 1)
        rw [hsup2, hinf2, Subgroup.card_bot, mul_one, Subgroup.card_top, hVj 0, hVj 1] at h1
        exact h1
      have hrkW : rk (IntMod V hV) = 2 * E3.mQuot V U := by
        unfold rk
        rw [hcardW, ← pow_add, padicValNat.prime_pow]
        ring
      have hY1 : Y i ≠ ⊥ := hi ▸ hXne
      have hY01 : Y 0 ≠ Y 1 := by
        intro heq
        have h1 : Disjoint (Y 0) (Y 1) := hYind.pairwiseDisjoint (by decide : (0 : Fin 2) ≠ 1)
        rw [heq, disjoint_self] at h1
        exact hYne i 1 hY1 h1
      obtain ⟨φ, hφ, hφ01⟩ := htrans 0 1
      have hφ10 : (Y 1).map (MulAut.conj φ).toMonoidHom = Y 0 := by
        obtain ⟨j, hj⟩ := hperm φ hφ 1
        rcases Fin.exists_fin_two.1 ⟨j, rfl⟩ with h0 | h1
        · rw [h0] at hj
          exact hj
        · exfalso
          rw [h1] at hj
          exact hY01 (Subgroup.map_injective (MulAut.conj φ).injective (hφ01.trans hj.symm))
      have hstep : ∀ k : ℕ, (Y 0).map (MulAut.conj (φ ^ (k + 1))).toMonoidHom =
          ((Y 0).map (MulAut.conj (φ ^ k)).toMonoidHom).map (MulAut.conj φ).toMonoidHom := by
        intro k
        rw [pow_succ', map_mul, Subgroup.map_map]
        rfl
      have horb : ∀ k : ℕ, (Y 0).map (MulAut.conj (φ ^ (2 * k))).toMonoidHom = Y 0 ∧
          (Y 0).map (MulAut.conj (φ ^ (2 * k + 1))).toMonoidHom = Y 1 := by
        intro k
        induction k with
        | zero =>
          refine ⟨?_, ?_⟩
          · rw [mul_zero, pow_zero, map_one]
            exact Subgroup.map_id _
          · rw [mul_zero, zero_add, pow_one]
            exact hφ01
        | succ k ih =>
          have e1 : 2 * (k + 1) = (2 * k + 1) + 1 := by ring
          have h1 : (Y 0).map (MulAut.conj (φ ^ (2 * (k + 1)))).toMonoidHom = Y 0 := by
            rw [e1, hstep, ih.2]
            exact hφ10
          refine ⟨h1, ?_⟩
          rw [hstep, h1]
          exact hφ01
      have hord0 : orderOf φ ≠ 0 := (orderOf_pos φ).ne'
      have hev : Even (orderOf φ) := by
        by_contra hodd
        rw [Nat.not_even_iff_odd] at hodd
        obtain ⟨k, hk⟩ := hodd
        have h1 := (horb k).2
        rw [← hk, pow_orderOf_eq_one, map_one] at h1
        exact hY01 ((Subgroup.map_id (Y 0)).symm.trans h1)
      set t := φ ^ (orderOf φ / 2) with htdef
      have ht2 : orderOf t = 2 := orderOf_pow_orderOf_div hord0 (even_iff_two_dvd.1 hev)
      have htM : t ∈ autI hV M := Subgroup.pow_mem _ hφ _
      have hevM : Even (Nat.card (autI hV M)) := by
        have := Subgroup.orderOf_dvd_natCard (autI hV M) htM
        rw [ht2] at this
        exact even_iff_two_dvd.2 this
      have := two_mul_mParam_le hW hevM
      omega
  rcases hdich with ⟨i, hi⟩ | ⟨h3, i₀, hi₀, hcl, h21, hna, h8⟩
  · exact absurd hi (hne i)
  have hn2 : E3.mQuot V U = 2 := by
    rw [hXcard] at h3
    have h4 : 2 ^ E3.mQuot V U = 2 ^ 2 := by omega
    exact Nat.pow_right_injective (le_refl 2) h4
  interval_cases s
  · exact Fin.elim0 i₀
  ·
    have hV1 : Vs 0 = ⊤ := by
      rw [← hVtop, ← hVsup]
      exact le_antisymm (le_iSup Vs 0) (iSup_le fun j => by rw [Subsingleton.elim j 0])
    have hcardV : Nat.card V = 8 := by
      have := h8 0
      rw [hV1, Subgroup.card_top] at this
      exact this
    have hcardU : Nat.card U = 2 := by
      have := E3.card_eq_two_pow_mul h.isPGroup_V hU.1
      rw [hn2, hcardV] at this
      omega
    have hYeq : Y 0 = e624Y hV M X := by
      rw [← hYsup]
      exact le_antisymm (le_iSup Y 0) (iSup_le fun j => by rw [Subsingleton.elim j 0])
    have hYM : Y 0 ≤ autI hV M := hYeq ▸ e624Y_le hV (hXMU.trans inf_le_left)
    have hi₀0 : i₀ = 0 := Subsingleton.elim _ _
    rw [hi₀0] at h21 hna
    have hcardW : Nat.card (IntMod V hV) = 8 := hcardV
    have hrkW : rk (IntMod V hV) = 3 := by
      unfold rk
      rw [hcardW, show (8 : ℕ) = 2 ^ 3 by norm_num, padicValNat.prime_pow]
    have hModd : Odd (Nat.card (autI hV M)) := by
      by_contra hev
      rw [Nat.not_odd_iff_even] at hev
      have := two_mul_mParam_le hW hev
      omega
    have hM21 : Nat.card (autI hV M) = 21 := by
      have h168 := card_mulAut_eight' (W := IntMod V hV) (fun a b => mul_comm a b) hW hcardW
      have hdvd : Nat.card (autI hV M) ∣ 21 * 8 := by
        rw [show 21 * 8 = 168 by norm_num, ← h168]
        exact Subgroup.card_subgroup_dvd_card _
      obtain ⟨k, hk⟩ : 21 ∣ Nat.card (autI hV M) := h21 ▸ Subgroup.card_dvd_of_le hYM
      rw [hk] at hdvd hModd
      have hk8 : k ∣ 8 := Nat.dvd_of_mul_dvd_mul_left (by norm_num) hdvd
      obtain ⟨j, hj, rfl⟩ := (Nat.dvd_prime_pow Nat.prime_two).1
        (show k ∣ 2 ^ 3 by simpa using hk8)
      have hj0 : j = 0 := by
        by_contra hj0
        apply (Nat.not_even_iff_odd.2 hModd)
        exact (Nat.even_pow.2 ⟨even_two, hj0⟩).mul_left 21
      rw [hk, hj0, pow_zero, mul_one]
    have hMY : autI hV M = Y 0 := (Subgroup.eq_of_le_of_card_ge hYM (by rw [hM21, h21])).symm
    refine ⟨⟨hM21, ?_⟩, ⟨hcardV, hcardU⟩, ?_⟩
    · rw [hMY]
      exact hna
    ·
      have hTN : T ≤ Subgroup.normalizer (V : Set G) := h.normal
      have hTb : autI hV T ≤ autI hV M := autI_mono hV h.inM.2
      have hT2 : IsPGroup 2 (autI hV T) :=
        (h.sylow.1.comap_subtype (K := Subgroup.normalizer (V : Set G))).map _
      obtain ⟨k, hk⟩ := (IsPGroup.iff_card (p := 2)).1 hT2
      have hdvd : 2 ^ k ∣ 21 := hk ▸ hM21 ▸ Subgroup.card_dvd_of_le hTb
      have hk0 : k = 0 := by
        by_contra hk0
        have h2 : 2 ∣ 21 := (dvd_pow_self 2 hk0).trans hdvd
        omega
      rw [hk0, pow_zero] at hk
      have hT1 : autI hV T = ⊥ := Subgroup.eq_bot_of_card_eq _ hk
      rw [autI_eq_bot_iff hV hTN] at hT1
      exact inf_eq_left.2 hT1
  ·
    exact (hN2 G T M V U L X hV hset hD Y Vs hB h3 hne).elim

end Main

end E6

end CFSG.Quasithin
