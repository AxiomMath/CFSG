module

public import CFSG.Quasithin.Vol2.Ch4Sec3NatMod
public import CFSG.Quasithin.Vol2.Ch4Sec3NatFix
public import CFSG.Quasithin.Vol2.Ch4Sec3L439
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Hypotheses

public section

namespace CFSG.Quasithin.H13.Ch4

open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin CFSG.Quasithin.A4
open CFSG.Open hiding StatedSL
open CFSG.Assembly.LowTwoRank
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem sl3Order_lt {a b : ℕ} (ha : 2 ≤ a) (hab : a < b) :
    a ^ 3 * ((a ^ 2 - 1) * (a ^ 3 - 1)) < b ^ 3 * ((b ^ 2 - 1) * (b ^ 3 - 1)) := by
  have h1 : a ^ 3 < b ^ 3 := Nat.pow_lt_pow_left hab (by norm_num)
  have h2 : a ^ 2 < b ^ 2 := Nat.pow_lt_pow_left hab (by norm_num)
  have ha2 : 1 ≤ a ^ 2 := Nat.one_le_pow _ _ (by omega)
  have ha3 : 1 ≤ a ^ 3 := Nat.one_le_pow _ _ (by omega)
  have ha2' : 0 < a ^ 2 - 1 := by
    have : 4 ≤ a ^ 2 := by nlinarith
    omega
  have h3 : a ^ 2 - 1 < b ^ 2 - 1 := by omega
  have h4 : a ^ 3 - 1 < b ^ 3 - 1 := by omega
  exact Nat.mul_lt_mul'' h1 (Nat.mul_lt_mul'' h3 h4)

omit [Finite G] in
theorem card_eq_of_card_statedSL_eq {F F₂ : Type} [Field F] [Fintype F] [Field F₂] [Fintype F₂]
    (h : Nat.card ↥(StatedSL 3 F) = Nat.card ↥(StatedSL 3 F₂)) :
    Fintype.card F = Fintype.card F₂ := by
  rw [card_statedSL_three, card_statedSL_three] at h
  have ha : 2 ≤ Fintype.card F := Fintype.one_lt_card
  have hb : 2 ≤ Fintype.card F₂ := Fintype.one_lt_card
  rcases lt_trichotomy (Fintype.card F) (Fintype.card F₂) with hlt | heq | hgt
  · exact absurd h (sl3Order_lt ha hlt).ne
  · exact heq
  · exact absurd h (sl3Order_lt hb hgt).ne'

omit [Finite G] in
theorem exists_good_scalar {F : Type} [Field F] [Fintype F] {m : ℕ} (hm : 2 ≤ m)
    (hF : Fintype.card F = 2 ^ m) : ∃ c : F, c ≠ 0 ∧ c ≠ 1 ∧ c * c ≠ 1 := by
  classical
  have h2 : (2 : F) = 0 := by
    have h := FiniteField.cast_card_eq_zero F
    rw [hF, Nat.cast_pow] at h
    exact pow_eq_zero_iff (by omega) |>.mp h
  obtain ⟨c, hc0, hc1⟩ : ∃ c : F, c ≠ 0 ∧ c ≠ 1 := by
    by_contra h
    push Not at h
    have hsurj : Function.Surjective (fun b : Bool => if b then (1 : F) else 0) := by
      intro c
      by_cases hc : c = 0
      · exact ⟨false, by simp [hc]⟩
      · exact ⟨true, by simp [h c hc]⟩
    have h3 := Fintype.card_le_of_surjective _ hsurj
    rw [hF, Fintype.card_bool] at h3
    have h4 : 4 ≤ 2 ^ m :=
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
    omega
  refine ⟨c, hc0, hc1, fun hcc => hc1 ?_⟩
  have h3 : (c + 1) * (c + 1) = 0 := by
    have : (c + 1) * (c + 1) = c * c + 2 * c + 1 := by ring
    rw [this, hcc, h2, zero_mul, add_zero]
    calc (1 : F) + 1 = 2 := by ring
      _ = 0 := h2
  have h4 := mul_self_eq_zero.mp h3
  have h5 : (-1 : F) = 1 := neg_eq_iff_add_eq_zero.mpr (by rw [one_add_one_eq_two, h2])
  calc c = c + 1 - 1 := by ring
    _ = 1 := by rw [h4, zero_sub, h5]

theorem commutator_mem_pCoreOf_of_involution (hKG : SL3ParabolicAutFact) {K L : Subgroup G}
    {F : Type} [Field F]
    [Fintype F] {m : ℕ} (hm : 2 ≤ m) (hF : Fintype.card F = 2 ^ m)
    {α : ↥K →* ↥(StatedSL 3 F)} (hα : Function.Surjective α) (hkerα : α.ker = CFSG.pCore 2 ↥K)
    {W' : Submodule F (Fin 3 → F)} (hW' : Module.finrank F W' = 2)
    (hY₀ne : (L.subgroupOf K).map α ≠ ⊥)
    (hY₀perf : ⁅(L.subgroupOf K).map α, (L.subgroupOf K).map α⁆ = (L.subgroupOf K).map α)
    (hstab₀ : ∀ y ∈ (L.subgroupOf K).map α, ∀ w ∈ W',
      (((y : ↥(StatedSL 3 F)) : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).mulVec w ∈ W')
    (hPnorm : ∀ g : ↥(StatedSL 3 F),
      (∀ w ∈ W', ((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).mulVec w ∈ W') →
        g ∈ Subgroup.normalizer
          (((L.subgroupOf K).map α : Subgroup ↥(StatedSL 3 F)) : Set ↥(StatedSL 3 F)))
    {x : G} (hxN : x ∈ Subgroup.normalizer (K : Set G)) (hx2 : x * x = 1)
    (hxL : ∀ l ∈ L, ⁅x, l⁆ ∈ pCoreOf 2 K) : ∀ k ∈ K, ⁅x, k⁆ ∈ pCoreOf 2 K := by
  intro k hk
  have hkerα' : α.ker.map (conjOn K x hxN).toMonoidHom = α.ker := by
    have hle : α.ker.map (conjOn K x hxN).toMonoidHom ≤ α.ker := by
      rintro _ ⟨y, hy, rfl⟩
      rw [hkerα] at hy ⊢
      have hy' := (mem_pCoreOf_iff' y).mpr hy
      apply (mem_pCoreOf_iff' _).mp
      show x * (y : G) * x⁻¹ ∈ pCoreOf 2 K
      exact (Subgroup.mem_normalizer_iff.mp (normalizer_le_normalizer_pCoreOf 2 K hxN) y).mp hy'
    exact Subgroup.eq_of_le_of_card_ge hle
      (Nat.card_congr (α.ker.equivMapOfInjective _ (conjOn K _ hxN).injective).toEquiv).le
  have hσapp := inducedAut_apply α hα x hxN hkerα'
  have hσσ : inducedAut α hα x hxN hkerα' * inducedAut α hα x hxN hkerα' = 1 := by
    refine MulEquiv.ext fun γ => ?_
    obtain ⟨k', rfl⟩ := hα γ
    rw [MulAut.mul_apply, hσapp, hσapp, MulAut.one_apply]
    congr 1
    apply Subtype.ext
    simp only [conjOn_apply]
    calc x * (x * (k' : G) * x⁻¹) * x⁻¹ = (x * x) * k' * (x * x)⁻¹ := by group
      _ = k' := by rw [hx2]; group
  have hσY : ∀ y ∈ (L.subgroupOf K).map α, inducedAut α hα x hxN hkerα' y = y := by
    rintro _ ⟨l, hl, rfl⟩
    rw [hσapp]
    have hcomm : ⁅x, (l : G)⁆ ∈ pCoreOf 2 K := hxL l hl
    rw [← mul_inv_eq_one, ← map_inv, ← map_mul, ← MonoidHom.mem_ker, hkerα,
      ← mem_pCoreOf_iff']
    simpa [conjOn_apply, commutatorElement_def, mul_assoc] using hcomm
  have hσ1 := hKG F m hm hF W' hW' _ hY₀ne hY₀perf hstab₀ hPnorm _ hσσ hσY
  have h1 := hσapp ⟨k, hk⟩
  rw [hσ1, MulAut.one_apply] at h1
  have h2 : α (conjOn K x hxN ⟨k, hk⟩ * (⟨k, hk⟩ : ↥K)⁻¹) = 1 := by
    rw [map_mul, map_inv, ← h1, mul_inv_cancel]
  rw [← MonoidHom.mem_ker, hkerα, ← mem_pCoreOf_iff'] at h2
  have e : ⁅x, k⁆ = ((conjOn K x hxN ⟨k, hk⟩ * (⟨k, hk⟩ : ↥K)⁻¹ : ↥K) : G) := by
    rw [commutatorElement_def]
    rfl
  rw [e]
  exact h2

namespace Setting432K

variable {T M L I H K : Subgroup G} {n : ℕ} {t : G} (sk : Setting432K G T M L n I H K t)
include sk

theorem exists_parabolicData {V : Subgroup G} (hc3 : C41Case3 H (pCoreOf 2 I) (H ⊓ M) L V K) :
    ∃ (m : ℕ) (F : Type) (_ : Field F) (_ : Fintype F) (W : Subgroup G)
      (α : ↥K →* ↥(StatedSL 3 F)) (β : ↥W →* Multiplicative (Fin 3 → F))
      (W' : Submodule F (Fin 3 → F)),
      2 ≤ m ∧ Fintype.card F = 2 ^ m ∧
      W ≤ ⁅omegaOneCenterOf (pCoreOf 2 (K ⊔ pCoreOf 2 I)), K⁆ ∧
      IsNaturalSectionWith K W ⊥ (CFSG.pCore 2 ↥K) (StatedSL 3 F) α β ∧
      Module.finrank F W' = 2 ∧
      (L.subgroupOf K).map α ≠ ⊥ ∧
      ⁅(L.subgroupOf K).map α, (L.subgroupOf K).map α⁆ = (L.subgroupOf K).map α ∧
      (∀ y ∈ (L.subgroupOf K).map α, ∀ w ∈ W',
        (((y : ↥(StatedSL 3 F)) : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).mulVec w ∈ W') ∧
      (∀ g : ↥(StatedSL 3 F),
        (∀ w ∈ W', ((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).mulVec w ∈ W') →
          g ∈ Subgroup.normalizer
            (((L.subgroupOf K).map α : Subgroup ↥(StatedSL 3 F)) : Set ↥(StatedSL 3 F))) := by
  obtain ⟨m, F, _, _, hm, hF, -, -, -, -, -, hline⟩ := hc3
  have hLK := sk.L_le_K
  obtain ⟨V₁, ⟨W, hWle, α, β, hnat, hline1, hMK⟩⟩ :
      ∃ V₁ : Subgroup G, IsStabilizedLineOfNatural F (pCoreOf 2 I) (H ⊓ M) K V₁ := by
    rcases hline with h | ⟨-, V₁, -, h₁, -, -⟩
    · exact ⟨V, h⟩
    · exact ⟨V₁, h₁⟩
  refine ⟨m, F, inferInstance, inferInstance, W, α, β, ?_⟩
  obtain ⟨hKW, hα, hkerα, hβ, hβker, hequiv⟩ := hnat
  obtain ⟨hV1W, W', hW', hW'iff⟩ := hline1
  refine ⟨W', by omega, hF, hWle, ⟨hKW, hα, hkerα, hβ, hβker, hequiv⟩, hW', ?_⟩
  have hLHM : L ≤ H ⊓ M :=
    le_inf (sk.base.L_le_I.trans sk.base.inM.2) sk.base.hyp.L_le
  have hLN : L ≤ Subgroup.normalizer (V₁ : Set G) := by
    have : L ≤ H ⊓ M ⊓ K := le_inf hLHM hLK
    rw [hMK] at this
    exact this.trans inf_le_right
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
  refine ⟨hY₀ne, hY₀perf, hstab₀, ?_⟩
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

theorem omegaOneCenter_inf_centralizer_le (hR : L2RankOneSylowFact) (hC : LemmaC53C56Six)
    (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK) (hKG : SL3ParabolicAutFact)
    {V : Subgroup G} (h438 : Concl438 H (pCoreOf 2 I) (H ⊓ M) L V K) :
    omegaOneCenterOf (T ⊓ H) ⊓ Subgroup.centralizer (L : Set G) ≤
      Subgroup.centralizer (K : Set G) := by
  intro z hz
  obtain ⟨hzZ, hzL⟩ := hz
  obtain ⟨hzS, hzC, hz2⟩ := mem_quasithinOmegaOneCenter_iff.mp hzZ
  set S := T ⊓ H with hS
  set R := pCoreOf 2 I with hRdef
  have hSK : S ≤ Subgroup.normalizer (K : Set G) := sk.S_le_normalizer
  have hOS : pCoreOf 2 K ≤ S := sk.pCoreOf_K_le_S hR hC h37 h38 h39
  have hperf : ⁅K, K⁆ = K := perfect_of_mem_cComp sk.cComp
  have hLK := sk.L_le_K
  have hRK : R ≤ Subgroup.normalizer (K : Set G) := sk.base.pCoreOf_le_S.trans hSK
  have hzN : z ∈ Subgroup.normalizer (K : Set G) := hSK hzS
  have hzO : ∀ a ∈ S, a * z = z * a := fun a ha => Subgroup.mem_centralizer_iff.mp hzC a ha
  obtain ⟨m, F, _, _, W, α', β', W', hm, hF, hWle, hnat, hW', hY₀ne, hY₀perf, hstab₀, hPnorm⟩ :=
    sk.exists_parabolicData h438.1
  have hα' := hnat.2.1
  have hkerα' := hnat.2.2.1
  have hz22 : z * z = 1 := by rw [← pow_two]; exact hz2
  have hzK : ∀ k ∈ K, ⁅z, k⁆ ∈ pCoreOf 2 K :=
    commutator_mem_pCoreOf_of_involution hKG hm hF hα' hkerα' hW' hY₀ne hY₀perf hstab₀ hPnorm
      hzN hz22 fun l hl => by
        rw [commutatorElement_eq_one_iff_mul_comm.mpr
          (Subgroup.mem_centralizer_iff.mp hzL l hl).symm]
        exact Subgroup.one_mem _
  set Q := c134Q (K ⊔ R) K with hQ
  have hQO : Q ≤ pCoreOf 2 K := (commutator_le_pCoreOf_of_le hperf hRK le_rfl).1
  have hKO : K ≤ Subgroup.normalizer (pCoreOf 2 (K ⊔ R) : Set G) :=
    le_sup_left.trans (le_normalizer_pCoreOf 2 (K ⊔ R))
  have hQOKR : Q ≤ pCoreOf 2 (K ⊔ R) := commutator_le_left_of_le_normalizer hKO
  have hOO : pCoreOf 2 K ≤ pCoreOf 2 (K ⊔ R) :=
    le_pCoreOf_of_le_normalizer 2 ((pCoreOf_le 2 K).trans le_sup_left)
      ((_root_.sup_le (fun x hx => Subgroup.le_normalizer hx) hRK).trans
        (normalizer_le_normalizer_pCoreOf 2 K)) (pCoreOf_isPGroup 2 K)
  have hKQ : K ≤ Subgroup.normalizer (Q : Set G) := fun k hk =>
    mem_normalizer_commutator (hKO hk) (Subgroup.le_normalizer hk)
  have hKCQ : K ≤ Subgroup.normalizer (Subgroup.centralizer (Q : Set G) : Set G) :=
    fun k hk => mem_normalizer_centralizer_of_mem (hKQ hk)
  have hcommC : ∀ X : Subgroup G, X ≤ Subgroup.centralizer (Q : Set G) →
      ⁅X, K⁆ ≤ Subgroup.centralizer (Q : Set G) := by
    intro X hX
    rw [Subgroup.commutator_le]
    intro g hg k hk
    have hgC := hX hg
    have e : ⁅g, k⁆ = g * (k * g⁻¹ * k⁻¹) := by simp only [commutatorElement_def]; group
    rw [e]
    exact Subgroup.mul_mem _ hgC
      ((Subgroup.mem_normalizer_iff.mp (hKCQ hk) g⁻¹).mp (Subgroup.inv_mem _ hgC))
  set Zz := Subgroup.zpowers z with hZz
  have hZzN : Zz ≤ Subgroup.normalizer (K : Set G) := Subgroup.zpowers_le.mpr hzN
  have hZzcs : Zz ≤ centralizerSection ⊤ K (pCoreOf 2 K) := by
    rw [Subgroup.zpowers_le]
    refine ⟨Subgroup.mem_top z, hzN, normalizer_le_normalizer_pCoreOf 2 K hzN, fun k hk => ?_⟩
    have h1 := (pCoreOf 2 K).inv_mem (hzK k hk)
    have e : (⁅z, k⁆)⁻¹ = k * z * k⁻¹ * z⁻¹ := by simp only [commutatorElement_def]; group
    rwa [e] at h1
  have hZzK : ⁅Zz, K⁆ ≤ pCoreOf 2 K := by
    rw [Subgroup.commutator_le]
    intro g hg k hk
    have h1 := (hZzcs hg).2.2.2 k hk
    have h2 := (pCoreOf 2 K).inv_mem h1
    have e : (k * g * k⁻¹ * g⁻¹)⁻¹ = ⁅g, k⁆ := by simp only [commutatorElement_def]; group
    rwa [e] at h2
  have hZzKK : ⁅Zz, K⁆ = ⁅⁅Zz, K⁆, K⁆ := commutator_eq_commutator_commutator_of_perfect' hperf hZzN
  have hZzQ : ⁅Zz, K⁆ ≤ Q := by
    rw [hZzKK]
    exact (Subgroup.commutator_mono hZzK le_rfl).trans (Subgroup.commutator_mono hOO le_rfl)
  have hzCQ : z ∈ Subgroup.centralizer (Q : Set G) :=
    Subgroup.mem_centralizer_iff.mpr fun q hq => hzO q (hOS (hQO hq))
  have hZzCQ : ⁅Zz, K⁆ ≤ Subgroup.centralizer (Q : Set G) :=
    hcommC Zz (Subgroup.zpowers_le.mpr hzCQ)
  set A := omegaOneCenterOf (pCoreOf 2 (K ⊔ R)) with hA
  have hAO : A ≤ pCoreOf 2 (K ⊔ R) := omegaOneCenterOf_le _
  have hAC : A ≤ Subgroup.centralizer (Q : Set G) := fun a ha =>
    Subgroup.mem_centralizer_iff.mpr fun q hq =>
      Subgroup.mem_centralizer_iff.mp (mem_quasithinOmegaOneCenter_iff.mp ha).2.1 q (hQOKR hq)
  have hAN : A ≤ Subgroup.normalizer (K : Set G) :=
    hAO.trans ((pCoreOf_le 2 _).trans (_root_.sup_le (fun x hx => Subgroup.le_normalizer hx) hRK))
  have hAK : ⁅A, K⁆ = ⁅⁅A, K⁆, K⁆ := commutator_eq_commutator_commutator_of_perfect' hperf hAN
  have hAQ : ⁅A, K⁆ ≤ Q := Subgroup.commutator_mono hAO le_rfl
  have hACQ : ⁅A, K⁆ ≤ Subgroup.centralizer (Q : Set G) := hcommC A hAC
  have hfp' : ∀ v : Fin 3 → F, (∀ l : ↥K, (l : G) ∈ L →
      ((α' l : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).mulVec v = v) → v = 0 := by
    intro v hv
    refine eq_zero_of_mulVec_eq_of_planeStab hKG hm hF W' hW' _ hY₀ne hY₀perf hstab₀ hPnorm v ?_
    rintro _ ⟨l, hl, rfl⟩
    exact hv l hl
  have finish : ∀ {F₂ : Type} [Field F₂] [Fintype F₂] {k : ℕ} {α : ↥K →* ↥(StatedSL 3 F₂)}
      {N₀ : Subgroup G}, IsModO2Surj K α → IsSumOfNaturalModulesVia K N₀ ⊥ α false k →
      ⁅Zz, K⁆ ≤ N₀ → W ≤ N₀ → z ∈ Subgroup.centralizer (K : Set G) := by
    intro F₂ _ _ k α N₀ hαm hN hZN hWN
    have hcard : Fintype.card F = Fintype.card F₂ :=
      card_eq_of_card_statedSL_eq ((card_modO2_of_surjective α' hα' hkerα').symm.trans
        (card_modO2_of_surjective α hαm.1 hαm.2))
    obtain ⟨c, hc0, hc1, hcc⟩ := exists_good_scalar hm (hcard.symm.trans hF)
    have hxker : ∀ a : ↥K, α a = 1 → (a : G) * z = z * a := by
      intro a ha
      have h1 : a ∈ α.ker := ha
      rw [hαm.2] at h1
      exact hzO a (hOS ((mem_pCoreOf_iff' a).mpr h1))
    have hxK : ∀ g ∈ K, z⁻¹ * (g * z * g⁻¹) ∈ N₀ := by
      intro g hg
      apply hZN
      have h1 : ⁅z⁻¹, g⁆ ∈ ⁅Zz, K⁆ :=
        Subgroup.commutator_mem_commutator (Subgroup.inv_mem _ (Subgroup.mem_zpowers z)) hg
      have e : ⁅z⁻¹, g⁆ = z⁻¹ * (g * z * g⁻¹) := by
        simp only [commutatorElement_def, inv_inv]; group
      rwa [e] at h1
    obtain ⟨n₁, hn₁N, hzn⟩ := exists_mul_mem_centralizer_of_natural hc0 hc1 hcc hαm.1 hN hxker hxK
    have hn₁L : n₁ ∈ Subgroup.centralizer (L : Set G) := by
      have h1 : z⁻¹ ∈ Subgroup.centralizer (L : Set G) := Subgroup.inv_mem _ hzL
      have h2 : z * n₁ ∈ Subgroup.centralizer (L : Set G) :=
        Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hLK) hzn
      have h3 := Subgroup.mul_mem _ h1 h2
      simpa using h3
    obtain ⟨hKN₀, hZ₀, β, hβ, hβker, hβeq⟩ := hN
    have hβinj : Function.Injective β := by
      rw [← MonoidHom.ker_eq_bot_iff, hβker, Subgroup.bot_subgroupOf]
    have hfix : ∀ (i : Fin k) (l : ↥K), (l : G) ∈ L →
        ((α l : GL (Fin 3) F₂) : Matrix (Fin 3) (Fin 3) F₂).mulVec
          (Multiplicative.toAdd (β ⟨n₁, hn₁N⟩) i) = Multiplicative.toAdd (β ⟨n₁, hn₁N⟩) i := by
      intro i l hl
      have h1 := hβeq l ⟨n₁, hn₁N⟩ ⟨n₁, hn₁N⟩ (by
        show n₁ = l * n₁ * (l : G)⁻¹
        rw [Subgroup.mem_centralizer_iff.mp hn₁L l hl]
        group) i
      simpa [moduleAct] using h1.symm
    have hn₁1 : n₁ = 1 := by
      have h1 : ∀ i, Multiplicative.toAdd (β ⟨n₁, hn₁N⟩) i = 0 := fun i =>
        eq_zero_of_fixed_of_natural_le hcard hnat ⟨hKN₀, hZ₀, β, hβ, hβker, hβeq⟩ hWN hfp' _
          (hfix i)
      have h2 : β ⟨n₁, hn₁N⟩ = 1 := by
        apply Multiplicative.toAdd.injective
        funext i
        rw [h1 i]
        rfl
      have h3 := hβinj (h2.trans (map_one β).symm)
      exact congrArg Subtype.val h3
    rw [hn₁1, mul_one] at hzn
    exact hzn
  rcases h438.2 with h2 | h3 | h4
  · obtain ⟨⟨-, F₂, _, _, α, -, hαm, hN⟩, -⟩ := h2
    exact finish hαm hN hZzQ (hWle.trans hAQ)
  · obtain ⟨⟨-, F₂, _, _, α, -, hαm, hN, -⟩, -⟩ := h3
    exact finish hαm hN (le_inf hZzQ hZzCQ) (hWle.trans (le_inf hAQ hACQ))
  · obtain ⟨⟨-, F₂, _, _, α, -, hαm, -, -, -, hN, -, -, -⟩, -⟩ := h4
    refine finish hαm hN ?_ ?_
    · rw [hZzKK]
      exact Subgroup.commutator_mono (le_inf hZzQ hZzCQ) le_rfl
    · refine hWle.trans ?_
      rw [hAK]
      exact Subgroup.commutator_mono (le_inf hAQ hACQ) le_rfl

end Setting432K

theorem lemma439Fix_holds (hR : L2RankOneSylowFact) (hC : LemmaC53C56Six) (h37 : A37ForSQTK)
    (h38 : A38ForSQTK) (h39 : A39ForSQTK) (hKG : SL3ParabolicAutFact) : Lemma439Fix :=
  fun _ _ _ _ _ _ _ _ _ _ _ sk _ _ h438 =>
    sk.omegaOneCenter_inf_centralizer_le hR hC h37 h38 h39 hKG h438

end CFSG.Quasithin.H13.Ch4
