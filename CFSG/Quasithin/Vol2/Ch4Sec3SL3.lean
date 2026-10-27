module

public import CFSG.Quasithin.Vol2.Ch4Sec3Ut
import CFSG.GroupTheory.PCore.OpenTransport

public section

namespace CFSG.Quasithin.H13.Ch4

open CFSG.Open hiding StatedSL
open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin CFSG.Quasithin.A4
open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Pointwise

theorem mulVec_sub_mem_of_perfect {F : Type} [Field F] (W : Submodule F (Fin 3 → F))
    (hW : Module.finrank F W = 2) (Y : Subgroup (GL (Fin 3) F)) (hY : ⁅Y, Y⁆ = Y)
    (hstab : ∀ y ∈ Y, ∀ w ∈ W, ((y : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).mulVec w ∈ W)
    {y : GL (Fin 3) F} (hy : y ∈ Y) (v : Fin 3 → F) :
    ((y : Matrix (Fin 3) (Fin 3) F).mulVec v - v) ∈ W := by
  classical
  have hq : Module.finrank F ((Fin 3 → F) ⧸ W) = 1 := by
    have := W.finrank_quotient_add_finrank
    rw [hW, Module.finrank_fin_fun] at this
    omega
  let T : ↥Y → ((Fin 3 → F) ⧸ W) →ₗ[F] ((Fin 3 → F) ⧸ W) := fun a =>
    W.mapQ W (Matrix.mulVecLin ((a : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F))
      (fun w hw => hstab a a.2 w hw)
  have hT : ∀ (a : ↥Y) (x : Fin 3 → F),
      T a (Submodule.Quotient.mk x) =
        Submodule.Quotient.mk (((a : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).mulVec x) :=
    fun a x => rfl
  have hex := fun a : ↥Y => LinearMap.existsUnique_eq_smul_id_of_finrank_eq_one hq (T a)
  choose c hc huniq using hex
  have hTmul : ∀ a b : ↥Y, T (a * b) = (T a).comp (T b) := by
    intro a b
    apply LinearMap.ext
    intro x
    induction x using Submodule.Quotient.induction_on with
    | H x =>
      rw [LinearMap.comp_apply, hT, hT, hT]
      congr 1
      simp [Matrix.mulVec_mulVec]
  have hT1 : T 1 = LinearMap.id := by
    apply LinearMap.ext
    intro x
    induction x using Submodule.Quotient.induction_on with
    | H x => simp [hT]
  have hmul : ∀ a b : ↥Y, c (a * b) = c a * c b := by
    intro a b
    refine (huniq (a * b) (c a * c b) ?_).symm
    rw [hTmul, hc a, hc b]
    ext x
    simp [mul_smul]
  have hone : c 1 = 1 := by
    refine (huniq 1 1 ?_).symm
    show T 1 = (1 : F) • LinearMap.id
    rw [hT1, one_smul]
  let χ : ↥Y →* F := { toFun := c, map_one' := hone, map_mul' := hmul }
  let χ' : ↥Y →* Fˣ := χ.toHomUnits
  have htop : commutator ↥Y = ⊤ := Group.isPerfect_def.1 (Subgroup.isPerfect_iff.2 hY)
  have hker : χ' ⟨y, hy⟩ = 1 := by
    have h1 : (⟨y, hy⟩ : ↥Y) ∈ commutator ↥Y := htop ▸ Subgroup.mem_top _
    exact Abelianization.commutator_subset_ker χ' h1
  have hc1 : c ⟨y, hy⟩ = 1 := by
    have := congrArg Units.val hker
    simpa [χ', χ] using this
  have h2 := LinearMap.congr_fun (hc ⟨y, hy⟩) (Submodule.Quotient.mk v)
  rw [hc1, one_smul, LinearMap.id_apply, hT] at h2
  exact (Submodule.Quotient.eq W).mp h2

section Induced

variable {G : Type} [Group G]

@[expose] def conjOn (K : Subgroup G) (g : G) (hg : g ∈ Subgroup.normalizer (K : Set G)) :
    ↥K ≃* ↥K where
  toFun k := ⟨g * k * g⁻¹, (Subgroup.mem_normalizer_iff.mp hg k).mp k.2⟩
  invFun k := ⟨g⁻¹ * k * g, by
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hg) k).mp k.2
    simpa using this⟩
  left_inv k := by ext; simp [mul_assoc]
  right_inv k := by ext; simp [mul_assoc]
  map_mul' a b := by ext; simp [mul_assoc]

theorem conjOn_apply (K : Subgroup G) (g : G) (hg : g ∈ Subgroup.normalizer (K : Set G))
    (k : ↥K) : ((conjOn K g hg k : ↥K) : G) = g * k * g⁻¹ := rfl

@[expose] noncomputable def inducedAut {K : Subgroup G} {Γ : Type} [Group Γ] (α : ↥K →* Γ)
    (hα : Function.Surjective α) (g : G) (hg : g ∈ Subgroup.normalizer (K : Set G))
    (hker : α.ker.map (conjOn K g hg).toMonoidHom = α.ker) : MulAut Γ :=
  ((QuotientGroup.quotientKerEquivOfSurjective α hα).symm.trans
    (QuotientGroup.congr α.ker α.ker (conjOn K g hg) hker)).trans
    (QuotientGroup.quotientKerEquivOfSurjective α hα)

theorem inducedAut_apply {K : Subgroup G} {Γ : Type} [Group Γ] (α : ↥K →* Γ)
    (hα : Function.Surjective α) (g : G) (hg : g ∈ Subgroup.normalizer (K : Set G))
    (hker : α.ker.map (conjOn K g hg).toMonoidHom = α.ker) (k : ↥K) :
    inducedAut α hα g hg hker (α k) = α (conjOn K g hg k) := by
  have h1 : (QuotientGroup.quotientKerEquivOfSurjective α hα).symm (α k) = (k : ↥K ⧸ α.ker) := by
    rw [MulEquiv.symm_apply_eq]
    rfl
  simp only [inducedAut, MulEquiv.trans_apply, h1]
  rfl

end Induced

@[expose] def SL3ParabolicAutFact : Prop :=
  ∀ (F : Type) [Field F] [Fintype F] (n : ℕ), 2 ≤ n → Fintype.card F = 2 ^ n →
    ∀ W : Submodule F (Fin 3 → F), Module.finrank F W = 2 →
    ∀ Y : Subgroup ↥(StatedSL 3 F), Y ≠ ⊥ → ⁅Y, Y⁆ = Y →
      (∀ y ∈ Y, ∀ w ∈ W,
        (((y : ↥(StatedSL 3 F)) : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).mulVec w ∈ W) →
      (∀ g : ↥(StatedSL 3 F),
        (∀ w ∈ W, ((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).mulVec w ∈ W) →
          g ∈ Subgroup.normalizer (Y : Set ↥(StatedSL 3 F))) →
      ∀ σ : MulAut ↥(StatedSL 3 F), σ * σ = 1 → (∀ y ∈ Y, σ y = y) → σ = 1

theorem card_statedSL_three (F : Type) [Field F] [Fintype F] :
    Nat.card ↥(StatedSL 3 F) =
      Fintype.card F ^ 3 * ((Fintype.card F ^ 2 - 1) * (Fintype.card F ^ 3 - 1)) := by
  rw [← Nat.card_congr (specialLinearGroupEquivStatedSL 3 F).toEquiv,
    CFSG.LocalAnalysis.ComponentInitial.LinearFlag.card_SL_eq (by norm_num),
    Nat.card_eq_fintype_card]
  have : Finset.Icc 2 3 = {2, 3} := by decide
  rw [this, Finset.prod_pair (by norm_num)]

theorem sl3_card_ne {m N : ℕ} (hN : N = 2520 ∨ N = 20160 ∨ N = 9999360) :
    (2 ^ m) ^ 3 * (((2 ^ m) ^ 2 - 1) * ((2 ^ m) ^ 3 - 1)) ≠ N := by
  intro h
  by_cases hm : m < 4
  · interval_cases m <;> rcases hN with rfl | rfl | rfl <;> simp at h
  · have h16 : 16 ≤ 2 ^ m :=
      calc (16 : ℕ) = 2 ^ 4 := by norm_num
        _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h1 : 4096 ≤ (2 ^ m) ^ 3 :=
      calc (4096 : ℕ) = 16 ^ 3 := by norm_num
        _ ≤ (2 ^ m) ^ 3 := Nat.pow_le_pow_left h16 3
    have h2 : 255 ≤ (2 ^ m) ^ 2 - 1 := by
      have : 256 ≤ (2 ^ m) ^ 2 :=
        calc (256 : ℕ) = 16 ^ 2 := by norm_num
          _ ≤ (2 ^ m) ^ 2 := Nat.pow_le_pow_left h16 2
      omega
    have h3 : 4095 ≤ (2 ^ m) ^ 3 - 1 := by omega
    have : 4096 * (255 * 4095) ≤ (2 ^ m) ^ 3 * (((2 ^ m) ^ 2 - 1) * ((2 ^ m) ^ 3 - 1)) :=
      Nat.mul_le_mul h1 (Nat.mul_le_mul h2 h3)
    rcases hN with rfl | rfl | rfl <;> omega

section Blocks

variable {G : Type} [Group G]

theorem card_blockU_eq [Finite G] {L : Subgroup G} {ι F : Type} [Fintype ι] [Field F] [Fintype F]
    (β : ↥(blockU L) →* Multiplicative (ι → F)) (hβ : Function.Surjective β)
    (hker : β.ker = (blockZ L).subgroupOf (blockU L)) :
    Nat.card ↥(blockU L) = Nat.card ↥(blockZ L) * Fintype.card F ^ Fintype.card ι := by
  classical
  have hZU : blockZ L ≤ blockU L := inf_le_left
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup β.ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective β hβ).toEquiv, hker,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZU).toEquiv] at h1
  have h2 : Nat.card (Multiplicative (ι → F)) = Fintype.card F ^ Fintype.card ι := by
    rw [show Nat.card (Multiplicative (ι → F)) = Nat.card (ι → F) from rfl,
      Nat.card_eq_fintype_card, Fintype.card_fun]
  rw [h1, h2, mul_comm]

theorem mem_pCoreOf_iff' {X : Subgroup G} (x : ↥X) :
    (x : G) ∈ pCoreOf 2 X ↔ x ∈ CFSG.pCore 2 ↥X := CFSG.mem_openPCoreOf_iff x

theorem commutator_le_pCoreOf_of_le [Finite G] {K R X : Subgroup G} (hK : ⁅K, K⁆ = K)
    (hR : R ≤ Subgroup.normalizer (K : Set G)) (hX : X ≤ pCoreOf 2 (K ⊔ R)) :
    ⁅X, K⁆ ≤ pCoreOf 2 K ∧ ⁅X, K⁆ ≤ blockU K := by
  have hKRN : K ⊔ R ≤ Subgroup.normalizer (K : Set G) :=
    _root_.sup_le Subgroup.le_normalizer hR
  have hXN : X ≤ Subgroup.normalizer (K : Set G) := hX.trans ((pCoreOf_le 2 _).trans hKRN)
  have h1 : ⁅X, K⁆ ≤ K := commutator_le_right_of_le_normalizer hXN
  have hO : K ≤ Subgroup.normalizer (pCoreOf 2 (K ⊔ R) : Set G) :=
    le_sup_left.trans (le_normalizer_pCoreOf 2 (K ⊔ R))
  have h2 : ⁅X, K⁆ ≤ pCoreOf 2 (K ⊔ R) :=
    (Subgroup.commutator_mono hX le_rfl).trans (commutator_le_left_of_le_normalizer hO)
  have h3 : K ⊓ pCoreOf 2 (K ⊔ R) ≤ pCoreOf 2 K :=
    le_pCoreOf_of_le_normalizer 2 inf_le_left
      (fun k hk => mem_normalizer_inf (Subgroup.le_normalizer hk) (hO hk))
      ((pCoreOf_isPGroup 2 _).to_le inf_le_right)
  have h4 : ⁅X, K⁆ ≤ pCoreOf 2 K := (le_inf h1 h2).trans h3
  refine ⟨h4, ?_⟩
  rw [commutator_eq_commutator_commutator_of_perfect' hK hXN]
  exact Subgroup.commutator_mono h4 le_rfl

theorem not_le_centralizer_of_naturalSection {K W : Subgroup G} {F : Type} [Field F]
    {α : ↥K →* ↥(StatedSL 3 F)} {β : ↥W →* Multiplicative (Fin 3 → F)}
    (h : IsNaturalSectionWith K W ⊥ (CFSG.pCore 2 ↥K) (StatedSL 3 F) α β) :
    ¬ W ≤ Subgroup.centralizer (K : Set G) := by
  intro hWC
  obtain ⟨-, hα, -, hβ, -, heq⟩ := h
  let A : Matrix.SpecialLinearGroup (Fin 3) F :=
    ⟨Matrix.transvection 0 1 1, Matrix.det_transvection_of_ne 0 1 (by decide) 1⟩
  obtain ⟨k, hk⟩ := hα (specialLinearGroupEquivStatedSL 3 F A)
  obtain ⟨u, hu⟩ := hβ (Multiplicative.ofAdd (Pi.single 1 1))
  have hcomm : (u : G) = k * u * (k : G)⁻¹ := by
    have := Subgroup.mem_centralizer_iff.mp (hWC u.2) k k.2
    rw [this]
    group
  have h1 := heq k u u hcomm
  rw [hk, hu, specialLinearGroupEquivStatedSL_coe] at h1
  have h2 := congrFun h1 0
  simp [A, Matrix.transvection, Matrix.mulVec, dotProduct, Matrix.one_apply,
    Pi.single_apply] at h2

end Blocks

variable {G : Type} [Group G] [Finite G]

namespace Setting432K

variable {T M L I H K : Subgroup G} {n : ℕ} {t : G} (sk : Setting432K G T M L n I H K t)
include sk

theorem le_pCoreOf_of_isStabilizedLine {F : Type} [Field F]
    {V₁ : Subgroup G} (h : IsStabilizedLineOfNatural F (pCoreOf 2 I) (H ⊓ M) K V₁) :
    V₁ ≤ pCoreOf 2 K := by
  obtain ⟨W, hWle, α, β, -, hline, -⟩ := h
  have hRK : pCoreOf 2 I ≤ Subgroup.normalizer (K : Set G) :=
    sk.base.pCoreOf_le_S.trans sk.S_le_normalizer
  exact hline.1.trans (hWle.trans (commutator_le_pCoreOf_of_le (perfect_of_mem_cComp sk.cComp)
    hRK (omegaOneCenterOf_le _)).1)

theorem not_isSL3Block (hR : L2RankOneSylowFact) (hC : LemmaC53C56Six) (h37 : A37ForSQTK)
    (h38 : A38ForSQTK) (h39 : A39ForSQTK) (hKG : SL3ParabolicAutFact) (hchar : CharTwo K)
    (h41 : C41Conclusion H (pCoreOf 2 I) (H ⊓ M) L
      ⁅omegaOneCenterOf (T ⊓ centralizerSection M L (pCoreOf 2 L)), L⁆ K) :
    ¬ IsSL3Block K := by
  intro hblk
  set V := ⁅omegaOneCenterOf (T ⊓ centralizerSection M L (pCoreOf 2 L)), L⁆ with hV
  set S := T ⊓ H with hS
  set φt := (MulAut.conj t).toMonoidHom with hφt
  obtain ⟨hshort, m₀, F₀, _, _, hF₀, α₀, hα₀, hker₀, β₀, hβ₀, hβker₀, -⟩ := hblk
  have hperf : ⁅K, K⁆ = K := perfect_of_mem_cComp sk.cComp
  have hSK := sk.S_le_normalizer
  have hLK := sk.L_le_K
  have hcardK : Nat.card (ModO2 K) =
      (2 ^ m₀) ^ 3 * (((2 ^ m₀) ^ 2 - 1) * ((2 ^ m₀) ^ 3 - 1)) := by
    rw [card_modO2_of_surjective α₀ hα₀ hker₀, card_statedSL_three, hF₀]
  have hc3 : C41Case3 H (pCoreOf 2 I) (H ⊓ M) L V K := by
    rcases h41.2.2.2 with c1 | c2 | c3 | c4
    · exfalso
      obtain ⟨m, hm, -, -, ⟨-, α₁, hα₁, hker₁, -⟩, -, -⟩ := c1
      have h1 := card_modO2_of_surjective α₁ hα₁ hker₁
      rw [card_of_alt' (by omega) (MulEquiv.refl _), hcardK] at h1
      rcases hm with rfl | rfl
      · exact sl3_card_ne (N := (5 + 2).factorial / 2) (Or.inl (by decide)) h1
      · exact sl3_card_ne (N := (6 + 2).factorial / 2) (Or.inr (Or.inl (by decide))) h1
    · exfalso
      obtain ⟨⟨-, F₁, _, _, hF₁, α₁, -, -, β₁, hβ₁, hβker₁, -⟩, -⟩ := c2
      have e0 := card_blockU_eq β₀ hβ₀ hβker₀
      have e1 := card_blockU_eq β₁ hβ₁ hβker₁
      rw [e0, hF₀, hF₁] at e1
      have hZ : 0 < Nat.card ↥(blockZ K) := Nat.card_pos
      have e2 : (2 ^ m₀) ^ Fintype.card (Fin 3) = 4 ^ Fintype.card (Fin 2 ⊕ Fin 2) :=
        Nat.eq_of_mul_eq_mul_left hZ e1
      simp only [Fintype.card_fin, Fintype.card_sum] at e2
      rw [← pow_mul, show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_mul] at e2
      have := Nat.pow_right_injective (le_refl 2) e2
      omega
    · exact c3
    · exfalso
      obtain ⟨h4, -, -⟩ := c4
      rcases h4 with h | h
      · exact sl3_card_ne (Or.inr (Or.inl rfl)) (hcardK.symm.trans (F420.card_of_l42 h))
      · exact sl3_card_ne (Or.inr (Or.inr rfl)) (hcardK.symm.trans (F420.card_of_l52 h))
  obtain ⟨n', F, _, _, hn', hF, -, -, -, -, -, hline⟩ := hc3
  have key : ∃ V₁ : Subgroup G, IsStabilizedLineOfNatural F (pCoreOf 2 I) (H ⊓ M) K V₁ ∧
      V₁ ≤ V ∧ V ≤ pCoreOf 2 K := by
    rcases hline with h | ⟨-, V₁, V₂, h₁, h₂, hV12⟩
    · exact ⟨V, h, le_rfl, sk.le_pCoreOf_of_isStabilizedLine h⟩
    · refine ⟨V₁, h₁, hV12 ▸ le_sup_left, ?_⟩
      rw [hV12]
      exact _root_.sup_le (sk.le_pCoreOf_of_isStabilizedLine h₁)
        (sk.le_pCoreOf_of_isStabilizedLine h₂)
  obtain ⟨V₁, ⟨W, hWle, α, β, hnat, hline1, hMK⟩, hV1V, hVO⟩ := key
  have hnot := not_le_centralizer_of_naturalSection hnat
  obtain ⟨hKW, hα, hkerα, hβ, -, hequiv⟩ := hnat
  obtain ⟨hV1W, W', hW', hW'iff⟩ := hline1
  have hRK : pCoreOf 2 I ≤ Subgroup.normalizer (K : Set G) :=
    sk.base.pCoreOf_le_S.trans hSK
  have hWU : W ≤ blockU K :=
    hWle.trans (commutator_le_pCoreOf_of_le hperf hRK (omegaOneCenterOf_le _)).2
  have hUO : blockU K ≤ pCoreOf 2 K :=
    commutator_le_left_of_le_normalizer (le_normalizer_pCoreOf 2 K)
  have hLHM : L ≤ H ⊓ M :=
    le_inf (sk.base.L_le_I.trans sk.base.inM.2) sk.base.hyp.L_le
  have hLN : L ≤ Subgroup.normalizer (V₁ : Set G) := by
    have : L ≤ H ⊓ M ⊓ K := le_inf hLHM hLK
    rw [hMK] at this
    exact this.trans inf_le_right
  have hZC : blockZ K ≤ Subgroup.centralizer (K : Set G) := inf_le_right
  have hKZ : K ≤ Subgroup.normalizer (blockZ K : Set G) := by
    intro k hk
    apply mem_normalizer_of_map_conj_le
    rintro _ ⟨z, hz, rfl⟩
    have hzk := Subgroup.mem_centralizer_iff.mp (hZC hz) k hk
    have e : (MulAut.conj k).toMonoidHom z = z := by
      show k * z * k⁻¹ = z
      rw [hzk]
      group
    rw [e]
    exact hz
  have hWZ : W ⊔ blockZ K = blockU K := by
    have hKWZ : K ≤ Subgroup.normalizer ((W ⊔ blockZ K : Subgroup G) : Set G) := by
      intro k hk
      apply mem_normalizer_of_map_conj_le
      rw [Subgroup.map_sup, map_conj_eq_of_mem_normalizer (hKW hk),
        map_conj_eq_of_mem_normalizer (hKZ hk)]
    rcases hshort.2.2.2.2.2 (W ⊔ blockZ K) le_sup_right (_root_.sup_le hWU inf_le_left)
      hKWZ with h | h
    · exact absurd ((le_sup_left.trans h.le).trans hZC) hnot
    · exact h
  set A := L.subgroupOf K with hA
  have hAmap : A.map K.subtype = L := by
    rw [hA, Subgroup.subgroupOf_map_subtype]
    exact inf_eq_left.mpr hLK
  have hAperf : ⁅A, A⁆ = A := by
    apply Subgroup.map_injective K.subtype_injective
    rw [Subgroup.map_commutator, hAmap, sk.base.hyp.commutator_eq]
  set Y₀ := A.map α with hY₀
  have hY₀perf : ⁅Y₀, Y₀⁆ = Y₀ := by rw [hY₀, ← Subgroup.map_commutator, hAperf]
  have hstab₀ : ∀ y ∈ Y₀, ∀ w ∈ W',
      (((y : ↥(StatedSL 3 F)) : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).mulVec w ∈ W' := by
    rintro _ ⟨l, hl, rfl⟩ w hw
    obtain ⟨u, hu⟩ := hβ (Multiplicative.ofAdd w)
    have huV : (u : G) ∈ V₁ := (hW'iff u).mpr (by rw [hu, toAdd_ofAdd]; exact hw)
    have hlN : (l : G) ∈ Subgroup.normalizer (V₁ : Set G) := hLN hl
    let v : ↥W := ⟨l * u * (l : G)⁻¹, (Subgroup.mem_normalizer_iff.mp (hKW l.2) u).mp u.2⟩
    have h1 := hequiv l u v rfl
    rw [hu, toAdd_ofAdd] at h1
    have h2 : (v : G) ∈ V₁ := (Subgroup.mem_normalizer_iff.mp hlN u).mp huV
    have h3 := (hW'iff v).mp h2
    rw [h1] at h3
    exact h3
  set Y := Y₀.map (StatedSL 3 F).subtype with hY
  have hYperf : ⁅Y, Y⁆ = Y := by rw [hY, ← Subgroup.map_commutator, hY₀perf]
  have hYstab : ∀ y ∈ Y, ∀ w ∈ W',
      ((y : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).mulVec w ∈ W' := by
    rintro _ ⟨y, hy, rfl⟩ w hw
    exact hstab₀ y hy w hw
  have hWL : ∀ w ∈ W, ∀ l ∈ L, ⁅w, l⁆ ∈ V₁ := by
    intro w hw l hl
    let wW : ↥W := ⟨w, hw⟩
    let lK : ↥K := ⟨l, hLK hl⟩
    let v : ↥W := ⟨l * w * l⁻¹, (Subgroup.mem_normalizer_iff.mp (hKW (hLK hl)) w).mp hw⟩
    have h1 := hequiv lK wW v rfl
    let c : ↥W := wW * v⁻¹
    have hc : (c : G) = ⁅w, l⁆ := by
      show w * (l * w * l⁻¹)⁻¹ = w * l * w⁻¹ * l⁻¹
      group
    rw [← hc]
    apply (hW'iff c).mpr
    have hβc : Multiplicative.toAdd (β c) =
        Multiplicative.toAdd (β wW) - Multiplicative.toAdd (β v) := by
      simp [c, map_mul, map_inv, toAdd_mul, toAdd_inv, sub_eq_add_neg]
    rw [hβc, h1]
    have hyY : ((α lK : ↥(StatedSL 3 F)) : GL (Fin 3) F) ∈ Y := ⟨α lK, ⟨lK, hl, rfl⟩, rfl⟩
    have h2 := W'.neg_mem
      (mulVec_sub_mem_of_perfect W' hW' Y hYperf hYstab hyY (Multiplicative.toAdd (β wW)))
    simpa [neg_sub] using h2
  have hUL : ⁅blockU K, L⁆ ≤ V₁ := by
    rw [Subgroup.commutator_le]
    intro x hx l hl
    have hWZn : W ≤ Subgroup.normalizer (blockZ K : Set G) :=
      fun w hw => hKZ ((hUO.trans (pCoreOf_le 2 K)) (hWU hw))
    have hx' : x ∈ ((W : Set G) * (blockZ K : Set G)) := by
      rw [← Subgroup.coe_mul_of_left_le_normalizer_right W (blockZ K) hWZn, hWZ]
      exact hx
    obtain ⟨w, hw, z, hz, rfl⟩ := hx'
    have hzl : z * l = l * z := (Subgroup.mem_centralizer_iff.mp (hZC hz) l (hLK hl)).symm
    have e : ⁅w * z, l⁆ = ⁅w, l⁆ := by
      rw [commutatorElement_def, commutatorElement_def]
      calc w * z * l * (w * z)⁻¹ * l⁻¹ = w * (z * l) * z⁻¹ * w⁻¹ * l⁻¹ := by group
        _ = w * (l * z) * z⁻¹ * w⁻¹ * l⁻¹ := by rw [hzl]
        _ = w * l * w⁻¹ * l⁻¹ := by group
    rw [e]
    exact hWL w hw l hl
  have htL : t ∈ Subgroup.normalizer (L : Set G) :=
    sk.base.hyp.normal (sk.base.hyp.T_le sk.t_mem)
  have htV : t ∈ Subgroup.normalizer (V : Set G) :=
    mem_normalizer_commutator
      (normalizer_le_normalizer_omegaOneCenterOf _ (sk.base.le_normalizer_Rp sk.t_mem)) htL
  have hUtL : ⁅(blockU K).map φt, L⁆ ≤ V := by
    have hLt : L.map φt = L := map_conj_eq_of_mem_normalizer htL
    calc ⁅(blockU K).map φt, L⁆ = ⁅(blockU K).map φt, L.map φt⁆ := by rw [hLt]
      _ = (⁅blockU K, L⁆).map φt := (Subgroup.map_commutator _ _ _).symm
      _ ≤ V.map φt := map_conj_mono (hUL.trans hV1V) t
      _ = V := map_conj_eq_of_mem_normalizer htV
  have hY₀ne : Y₀ ≠ ⊥ := by
    intro hbot
    apply hyp501_L_ne_bot sk.base.hyp
    apply eq_bot_of_perfect_of_isPGroup_two sk.base.hyp.commutator_eq
    refine (pCoreOf_isPGroup 2 K).to_le ?_
    intro l hl
    have h1 : α ⟨l, hLK hl⟩ ∈ Y₀ := ⟨⟨l, hLK hl⟩, hl, rfl⟩
    rw [hbot, Subgroup.mem_bot] at h1
    have h2 : (⟨l, hLK hl⟩ : ↥K) ∈ α.ker := h1
    rw [hkerα] at h2
    exact (mem_pCoreOf_iff' _).mpr h2
  have hPnorm : ∀ g : ↥(StatedSL 3 F),
      (∀ w ∈ W', ((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).mulVec w ∈ W') →
        g ∈ Subgroup.normalizer (Y₀ : Set ↥(StatedSL 3 F)) := by
    intro g hg
    obtain ⟨k', rfl⟩ := hα g
    have hk'V : (k' : G) ∈ Subgroup.normalizer (V₁ : Set G) := by
      apply mem_normalizer_of_map_conj_le
      rintro _ ⟨v, hv, rfl⟩
      have hvW : v ∈ W := hV1W hv
      let vW : ↥W := ⟨v, hvW⟩
      let v' : ↥W := ⟨k' * v * (k' : G)⁻¹, (Subgroup.mem_normalizer_iff.mp (hKW k'.2) v).mp hvW⟩
      have h1 := hequiv k' vW v' rfl
      have h2 : Multiplicative.toAdd (β vW) ∈ W' := (hW'iff vW).mp hv
      exact (hW'iff v').mpr (by rw [h1]; exact hg _ h2)
    have hk'M : (k' : G) ∈ M := by
      have : (k' : G) ∈ K ⊓ Subgroup.normalizer (V₁ : Set G) := ⟨k'.2, hk'V⟩
      rw [← hMK] at this
      exact this.1.2
    have hk'L : (k' : G) ∈ Subgroup.normalizer (L : Set G) := sk.base.hyp.normal hk'M
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · rintro ⟨l, hl, rfl⟩
      refine ⟨k' * l * k'⁻¹, ?_, by simp [map_mul, map_inv]⟩
      exact (Subgroup.mem_normalizer_iff.mp hk'L l).mp hl
    · rintro ⟨l, hl, hle⟩
      refine ⟨k'⁻¹ * l * k', ?_, ?_⟩
      · have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hk'L) l).mp hl
        rw [inv_inv] at this
        exact this
      · rw [map_mul, map_mul, map_inv, hle]
        group
  apply sk.not_commutator_conj_blockU_le hR hC h37 h38 h39 hchar
  rw [Subgroup.commutator_le]
  rintro _ ⟨x, hx, rfl⟩ k hk
  have hxS : x ∈ S := (hUO.trans (sk.pCoreOf_K_le_S hR hC h37 h38 h39)) hx
  have huS : φt x ∈ S := (Subgroup.mem_normalizer_iff.mp sk.t_normalizer x).mp hxS
  have huN : φt x ∈ Subgroup.normalizer (K : Set G) := hSK huS
  have hx2 : x ^ 2 = 1 := hshort.2.2.1.2 x hx
  have hu2 : φt x * φt x = 1 := by rw [← map_mul, ← pow_two, hx2, map_one]
  have hkerα' : α.ker.map (conjOn K (φt x) huN).toMonoidHom = α.ker := by
    have hle : α.ker.map (conjOn K (φt x) huN).toMonoidHom ≤ α.ker := by
      rintro _ ⟨y, hy, rfl⟩
      rw [hkerα] at hy ⊢
      have hy' := (mem_pCoreOf_iff' y).mpr hy
      apply (mem_pCoreOf_iff' _).mp
      show φt x * (y : G) * (φt x)⁻¹ ∈ pCoreOf 2 K
      exact (Subgroup.mem_normalizer_iff.mp (normalizer_le_normalizer_pCoreOf 2 K huN) y).mp hy'
    exact Subgroup.eq_of_le_of_card_ge hle
      (Nat.card_congr (α.ker.equivMapOfInjective _ (conjOn K _ huN).injective).toEquiv).le
  have hσapp := inducedAut_apply α hα (φt x) huN hkerα'
  have hσσ : inducedAut α hα (φt x) huN hkerα' * inducedAut α hα (φt x) huN hkerα' = 1 := by
    refine MulEquiv.ext fun γ => ?_
    obtain ⟨k', rfl⟩ := hα γ
    rw [MulAut.mul_apply, hσapp, hσapp, MulAut.one_apply]
    congr 1
    apply Subtype.ext
    simp only [conjOn_apply]
    calc φt x * (φt x * (k' : G) * (φt x)⁻¹) * (φt x)⁻¹ =
        (φt x * φt x) * k' * (φt x * φt x)⁻¹ := by group
      _ = k' := by rw [hu2]; group
  have hσY : ∀ y ∈ Y₀, inducedAut α hα (φt x) huN hkerα' y = y := by
    rintro _ ⟨l, hl, rfl⟩
    rw [hσapp]
    have hcomm : ⁅φt x, (l : G)⁆ ∈ pCoreOf 2 K :=
      hVO (hUtL (Subgroup.commutator_mem_commutator ⟨x, hx, rfl⟩ hl))
    rw [← mul_inv_eq_one, ← map_inv, ← map_mul, ← MonoidHom.mem_ker, hkerα,
      ← mem_pCoreOf_iff']
    simpa [conjOn_apply, commutatorElement_def, mul_assoc] using hcomm
  have hσ1 := hKG F n' (by omega) hF W' hW' Y₀ hY₀ne hY₀perf hstab₀ hPnorm _ hσσ hσY
  have h1 := hσapp ⟨k, hk⟩
  rw [hσ1, MulAut.one_apply] at h1
  have h2 : α (conjOn K (φt x) huN ⟨k, hk⟩ * (⟨k, hk⟩ : ↥K)⁻¹) = 1 := by
    rw [map_mul, map_inv, ← h1, mul_inv_cancel]
  rw [← MonoidHom.mem_ker, hkerα, ← mem_pCoreOf_iff'] at h2
  have e : ⁅φt x, k⁆ = ((conjOn K (φt x) huN ⟨k, hk⟩ * (⟨k, hk⟩ : ↥K)⁻¹ : ↥K) : G) := by
    rw [commutatorElement_def]
    rfl
  rw [e]
  exact h2

end Setting432K

theorem lemma437SL3_holds (hR : L2RankOneSylowFact) (hC : LemmaC53C56Six) (h37 : A37ForSQTK)
    (h38 : A38ForSQTK) (h39 : A39ForSQTK) (hKG : SL3ParabolicAutFact) : Lemma437SL3 :=
  fun _ _ _ _ _ _ _ _ _ _ _ sk hchar h41 =>
    sk.not_isSL3Block hR hC h37 h38 h39 hKG hchar h41

end CFSG.Quasithin.H13.Ch4
