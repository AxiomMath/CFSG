module

public import CFSG.Quasithin.Vol2.Ch12Sec7L5e
public import CFSG.Quasithin.Background.GoldschmidtS146RArith
public import CFSG.Quasithin.EmptyFaithful.SBc11List

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique S127

@[expose] def Lemma12_7_5K41 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G) (t : G), Hyp1271 G T L V → t ∈ V →
    (Subgroup.centralizer ({t} : Set G)).relIndex L = 18 →
    HypC28 (Subgroup.centralizer ({t} : Set G)) (pCoreOf 2 (L ⊔ T))
      (Subgroup.normalizer (L : Set G) ⊓ Subgroup.centralizer ({t} : Set G))
      (oTwoUpper (L ⊓ Subgroup.centralizer ({t} : Set G))) V →
    ∀ K : Subgroup G, K ∈ cComp (Subgroup.centralizer ({t} : Set G)) → CharTwo K →
      CFSG.IsQuasisimple (↥K ⧸ CFSG.pCore 2 ↥K) →
      ¬ K ≤ Subgroup.normalizer (L : Set G) ⊓ Subgroup.centralizer ({t} : Set G) →
      C41Conclusion (Subgroup.centralizer ({t} : Set G)) (pCoreOf 2 (L ⊔ T))
        (Subgroup.normalizer (L : Set G) ⊓ Subgroup.centralizer ({t} : Set G))
        (oTwoUpper (L ⊓ Subgroup.centralizer ({t} : Set G))) V K → False

@[expose] def Lemma12_7_5K31 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G) (t : G), Hyp1271 G T L V → t ∈ V →
    (Subgroup.centralizer ({t} : Set G)).relIndex L = 18 →
    HypC28 (Subgroup.centralizer ({t} : Set G)) (pCoreOf 2 (L ⊔ T))
      (Subgroup.normalizer (L : Set G) ⊓ Subgroup.centralizer ({t} : Set G))
      (oTwoUpper (L ⊓ Subgroup.centralizer ({t} : Set G))) V →
    ∀ K : Subgroup G, IsComponentOf K (Subgroup.centralizer ({t} : Set G)) →
      C31Conclusion (Subgroup.centralizer ({t} : Set G)) (pCoreOf 2 (L ⊔ T))
        (Subgroup.normalizer (L : Set G) ⊓ Subgroup.centralizer ({t} : Set G))
        (oTwoUpper (L ⊓ Subgroup.centralizer ({t} : Set G))) V K →
      IsComponentOf (conjClosure (oTwoUpper (L ⊓ Subgroup.centralizer ({t} : Set G)))
          (Subgroup.centralizer ({t} : Set G))) (Subgroup.centralizer ({t} : Set G)) ∧
        (Subgroup.center ↥(conjClosure (oTwoUpper (L ⊓ Subgroup.centralizer ({t} : Set G)))
            (Subgroup.centralizer ({t} : Set G)))).map
          (conjClosure (oTwoUpper (L ⊓ Subgroup.centralizer ({t} : Set G)))
            (Subgroup.centralizer ({t} : Set G))).subtype = Vt L t ∧
        IsPSL 3 2 2
          (↥(conjClosure (oTwoUpper (L ⊓ Subgroup.centralizer ({t} : Set G)))
              (Subgroup.centralizer ({t} : Set G))) ⧸
            Subgroup.center ↥(conjClosure (oTwoUpper (L ⊓ Subgroup.centralizer ({t} : Set G)))
              (Subgroup.centralizer ({t} : Set G))))

theorem lemma12_7_5K_of (hK41 : Lemma12_7_5K41) (hK31 : Lemma12_7_5K31) : Lemma12_7_5K := by
  intro G _ _ T L V t h ht h18 hC K _ _ _ hKM _ hdesc
  rcases hdesc with ⟨hc, h31⟩ | ⟨hKc, hK2, hKq', hKM', h41⟩
  · exact hK31 G T L V t h ht h18 hC K hc h31
  · exact (hK41 G T L V t h ht h18 hC K hKc hK2 hKq' hKM' h41).elim

@[expose] def Sp4BlockLineSplit : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (K V : Subgroup G) (F : Type) [Field F] [Fintype F]
    (α : ↥K →* ↥(StatedSp 2 F)) (β : ↥(blockU K) →* Multiplicative (Fin 2 ⊕ Fin 2 → F)),
    IsSp4Block K → Fintype.card F = 4 → IsMatrixBlockTypeWith K (StatedSp 2 F) α β →
    IsFLineVia (blockU K) V β → IsMaxParabolic2 K (K ⊓ Subgroup.normalizer (V : Set G)) →
    ∃ W : Subgroup G, W ≤ V ∧
      K ⊓ Subgroup.normalizer (V : Set G) ≤ Subgroup.normalizer (W : Set G) ∧
      W ⊓ blockZ K = ⊥ ∧ W ⊔ blockZ K = V

@[expose] def Lemma12_7_5K41Case1 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G) (t : G), Hyp1271 G T L V → t ∈ V →
    (Subgroup.centralizer ({t} : Set G)).relIndex L = 18 →
    HypC28 (Subgroup.centralizer ({t} : Set G)) (pCoreOf 2 (L ⊔ T))
      (Subgroup.normalizer (L : Set G) ⊓ Subgroup.centralizer ({t} : Set G))
      (oTwoUpper (L ⊓ Subgroup.centralizer ({t} : Set G))) V →
    oTwoUpper (L ⊓ Subgroup.centralizer ({t} : Set G)) =
      conjClosure (oTwoUpper (L ⊓ Subgroup.centralizer ({t} : Set G)))
        (Subgroup.normalizer (L : Set G) ⊓ Subgroup.centralizer ({t} : Set G)) →
    ∀ K : Subgroup G, C41Case1 (Subgroup.centralizer ({t} : Set G)) (pCoreOf 2 (L ⊔ T))
      (Subgroup.normalizer (L : Set G) ⊓ Subgroup.centralizer ({t} : Set G))
      (oTwoUpper (L ⊓ Subgroup.centralizer ({t} : Set G))) V K → False

namespace S127.L5

theorem det_eq_one {n : ℕ} {F : Type} [Field F] (g : ↥(CFSG.Assembly.LowTwoRank.StatedSL n F)) :
    ((g : GL (Fin n) F) : Matrix (Fin n) (Fin n) F).det = 1 := by
  obtain ⟨g, hg⟩ := g
  induction hg using Subgroup.closure_induction with
  | mem x hx => exact hx
  | one => simp
  | mul x y _ _ hx hy => simp [Matrix.det_mul, hx, hy]
  | inv x _ hx =>
    have h1 := congrArg Matrix.det (Units.inv_mul x)
    rw [Matrix.det_mul, hx, mul_one, Matrix.det_one] at h1
    exact h1

theorem sq_eq_one_of_mulVec_eq {F : Type} [Field F] [CharP F 2]
    (g : ↥(CFSG.Assembly.LowTwoRank.StatedSL 2 F)) {w : Fin 2 → F} (hw : w ≠ 0)
    (hg : ((g : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F).mulVec w = w) : g ^ 2 = 1 := by
  have hdet := det_eq_one g
  set A : Matrix (Fin 2) (Fin 2) F := ((g : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) with hA
  rw [Matrix.det_fin_two] at hdet
  have e0 := congrFun hg 0
  have e1 := congrFun hg 1
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two] at e0 e1
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  have htr : A 0 0 + A 1 1 = 0 := by
    have hd : (A 0 0 - 1) * (A 1 1 - 1) - A 0 1 * A 1 0 = 0 := by
      by_cases h0 : w 0 = 0
      · have h1 : w 1 ≠ 0 := fun h1 => hw (funext fun i => by fin_cases i <;> simp_all)
        apply (mul_left_inj' h1).mp
        linear_combination (A 0 0 - 1) * e1 - A 1 0 * e0
      · apply (mul_left_inj' h0).mp
        linear_combination (A 1 1 - 1) * e0 - A 0 1 * e1
    linear_combination -hd + hdet + h2
  have hsq : A * A = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
    · linear_combination A 0 0 * htr - hdet - h2
    · linear_combination A 0 1 * htr
    · linear_combination A 1 0 * htr
    · linear_combination A 1 1 * htr - hdet - h2
  apply Subtype.ext
  apply Units.ext
  simp only [sq, OneMemClass.coe_one, Units.val_one]
  exact hsq

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem card_eq_of_isFLineVia {U V Z : Subgroup G} {ι F : Type} [Finite ι] [Field F] [Fintype F]
    (hF : Fintype.card F = 4) (β : ↥U →* Multiplicative (ι → F)) (hβs : Function.Surjective β)
    (hβk : β.ker = Z.subgroupOf U) (hZU : Z ≤ U) (hV : IsFLineVia U V β) :
    Nat.card ↥V = Nat.card ↥Z * 16 := by
  classical
  obtain ⟨hVU, W, hW2, hW⟩ := hV
  have hZV : Z ≤ V := fun z hz => by
    have h1 : β ⟨z, hZU hz⟩ = 1 := by
      rw [← MonoidHom.mem_ker, hβk]
      exact hz
    exact (hW ⟨z, hZU hz⟩).mpr (by rw [h1]; exact W.zero_mem)
  let φ : ↥V →* Multiplicative (ι → F) := β.comp (Subgroup.inclusion hVU)
  have hker : φ.ker = Z.subgroupOf V := by
    ext v
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    have := congrArg (fun S : Subgroup ↥U => Subgroup.inclusion hVU v ∈ S) hβk
    simp only [MonoidHom.mem_ker, eq_iff_iff, Subgroup.mem_subgroupOf] at this
    exact this
  have hrange : Nat.card ↥φ.range = 16 := by
    have e : ↥φ.range ≃ ↥W :=
      { toFun := fun x => ⟨Multiplicative.toAdd (x : Multiplicative (ι → F)), by
          obtain ⟨v, hv⟩ := x.2
          rw [← hv]
          exact (hW (Subgroup.inclusion hVU v)).mp v.2⟩
        invFun := fun w => ⟨Multiplicative.ofAdd (w : ι → F), by
          obtain ⟨u, hu⟩ := hβs (Multiplicative.ofAdd (w : ι → F))
          have huV : (u : G) ∈ V := (hW u).mpr (by rw [hu]; exact w.2)
          exact ⟨⟨u, huV⟩, hu⟩⟩
        left_inv := fun x => rfl
        right_inv := fun w => rfl }
    have : Fintype ↥W := Fintype.ofFinite _
    rw [Nat.card_congr e, Nat.card_eq_fintype_card, Module.card_eq_pow_finrank (K := F), hW2,
      hF]
    norm_num
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup φ.ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv, hrange, hker,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZV).toEquiv] at h1
  rw [h1, mul_comm]

omit [Finite G] in
theorem card_modO2_congr {A B : Subgroup G} (h : A = B) :
    Nat.card (ModO2 A) = Nat.card (ModO2 B) := by
  subst h
  rfl

theorem eq_two_of_isPSL {X : Type} [Group X] {n : ℕ} (h : IsPSL 2 2 n X)
    (hc : Nat.card X = 60) : n = 2 := by
  rw [GoldS146R.card_isPSL_two_two h] at hc
  have hn : n ≤ 2 := by
    by_contra hn
    rw [not_le] at hn
    have h8 : 8 ≤ 2 ^ n := by
      calc 8 = 2 ^ 3 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
    have h63 : 63 ≤ (2 ^ n) ^ 2 - 1 := by
      have : 64 ≤ (2 ^ n) ^ 2 := by nlinarith
      omega
    have := Nat.mul_le_mul h8 h63
    omega
  interval_cases n <;> first | rfl | norm_num at hc

variable {T L V : Subgroup G} {t : G}

namespace D127

variable (d : D127 G T L V t)
include d

theorem card_modO2 : Nat.card (ModO2 (Lt L t)) = 60 := by
  obtain ⟨e⟩ := d.a5
  rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, card_alternatingGroup]
  rfl

theorem inf_centralizer_le : V ⊓ Subgroup.centralizer (Lt L t : Set G) ≤ Vt L t := by
  have hN : Lt L t ≤ Subgroup.normalizer
      ((V ⊓ Subgroup.centralizer (Lt L t : Set G) : Subgroup G) : Set G) := fun l hl =>
    Subgroup.inf_normalizer_le_normalizer_inf ⟨d.lt_le_normalizer hl,
      Subgroup.mem_normalizer_fintype fun x hx => by
        have e : l * x * l⁻¹ = x := by
          rw [Subgroup.mem_centralizer_iff.mp hx l hl, mul_inv_cancel_right]
        rw [e]
        exact hx⟩
  rcases d.le_or_sup_eq inf_le_left hN with hle | hsup
  · exact hle
  · exfalso
    have hVC : V ≤ Subgroup.centralizer (Lt L t : Set G) := by
      rw [← hsup]
      exact sup_le inf_le_right fun v hv => Subgroup.mem_centralizer_iff.mpr fun l hl =>
        (Subgroup.mem_centralizer_iff.mp (d.lt_le hl).2 v hv).symm
    have hb : ⁅V, Lt L t⁆ = ⊥ := Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hVC
    have h1 : Nat.card ↥V = 1 := by
      rw [d.comm_eq, hb]
      simp
    rw [d.card_V] at h1
    norm_num at h1

theorem not_c41Case4 {H R M K : Subgroup G} (hM0 : Lt L t = conjClosure (Lt L t) M)
    (h : C41Case4 H R M (Lt L t) V K) : False := by
  have h60 := (card_modO2_congr hM0.symm).trans d.card_modO2
  obtain ⟨-, -, h3 | h4⟩ := h
  · have := SBc11.card_of_isPSL_three_two h3
    rw [h60] at this
    norm_num at this
  · have := card_of_isPSL_two1522 4 h4
    rw [h60] at this
    simp [Fin.prod_univ_four] at this

theorem not_c41Case3 {H R M K : Subgroup G} (hM0 : Lt L t = conjClosure (Lt L t) M)
    (hLMK : Lt L t ≤ M ⊓ K) (h : C41Case3 H R M (Lt L t) V K) : False := by
  obtain ⟨n, F, _, _, -, hFn, -, -, -, -, hpsl, hline⟩ := h
  have hn := eq_two_of_isPSL hpsl ((card_modO2_congr hM0.symm).trans d.card_modO2)
  subst hn
  have hF : Fintype.card F = 4 := by rw [hFn]; norm_num
  obtain ⟨V₁, hV₁V, hV₁⟩ : ∃ V₁, V₁ ≤ V ∧ IsStabilizedLineOfNatural F R M K V₁ := by
    rcases hline with h1 | ⟨-, V₁, V₂, h1, -, hVeq⟩
    · exact ⟨V, le_rfl, h1⟩
    · exact ⟨V₁, le_sup_left.trans hVeq.ge, h1⟩
  obtain ⟨W, -, α, β, hNS, hFL, hMK⟩ := hV₁
  obtain ⟨-, -, -, hβs, hβk, -⟩ := hNS
  have hcard := card_eq_of_isFLineVia hF β hβs hβk bot_le hFL
  rw [Subgroup.card_bot, one_mul] at hcard
  exact d.false_of_card_sixteen hV₁V (fun l hl => (hMK.le (hLMK hl)).2) hcard

open scoped commutatorElement Pointwise in
theorem not_c41Case2 (hR1 : Sp4BlockLineSplit) {H R M K : Subgroup G} (hLK : Lt L t ≤ K)
    (h : C41Case2 H R M (Lt L t) V K) : False := by
  obtain ⟨hK, F, _, _, α, β, hF, hblk, hFL, hpar, hMK, -⟩ := h
  have hblk' := hblk
  obtain ⟨-, -, hβs, hβk, -⟩ := hblk'
  obtain ⟨hVbU, W₀, hW₀, hmem⟩ := hFL
  have hKZ : K ≤ Subgroup.normalizer (blockZ K : Set G) := fun k hk =>
    Subgroup.mem_normalizer_fintype fun z hz => by
      rw [Subgroup.mem_centralizer_iff.mp hz.2 k hk, mul_inv_cancel_right]
      exact hz
  have hsupN : ∀ {A B : Subgroup G} {x : G}, x ∈ Subgroup.normalizer (A : Set G) →
      x ∈ Subgroup.normalizer (B : Set G) →
        x ∈ Subgroup.normalizer ((A ⊔ B : Subgroup G) : Set G) := by
    intro A B x hA hB
    rw [Subgroup.mem_normalizer_iff_map_conj_eq] at hA hB ⊢
    rw [Subgroup.map_sup, hA, hB]
  set Vb := V ⊔ blockZ K with hVb
  have hPle : K ⊓ Subgroup.normalizer (V : Set G) ≤ K ⊓ Subgroup.normalizer (Vb : Set G) :=
    fun x hx => ⟨hx.1, hsupN hx.2 (hKZ hx.1)⟩
  have hne : K ⊓ Subgroup.normalizer (Vb : Set G) ≠ K := by
    intro he
    have hKN : K ≤ Subgroup.normalizer (Vb : Set G) := he ▸ inf_le_right
    rcases hK.1.2.2.2.2.2 Vb le_sup_right hVbU hKN with h0 | h0
    ·
      have hW0 : W₀ = ⊥ := by
        rw [eq_bot_iff]
        intro w hw
        obtain ⟨u, hu⟩ := hβs (Multiplicative.ofAdd w)
        have huVb : (u : G) ∈ Vb := (hmem u).mpr (by rw [hu]; exact hw)
        rw [h0] at huVb
        have hk : u ∈ β.ker := by
          rw [hβk]
          exact huVb
        rw [MonoidHom.mem_ker, hu] at hk
        exact (Submodule.mem_bot F).mpr (congrArg Multiplicative.toAdd hk)
      rw [hW0, finrank_bot] at hW₀
      exact absurd hW₀ (by norm_num)
    ·
      have hWtop : W₀ = ⊤ := by
        rw [eq_top_iff]
        intro w _
        obtain ⟨u, hu⟩ := hβs (Multiplicative.ofAdd w)
        have := (hmem u).mp (by rw [h0]; exact u.2)
        rwa [hu] at this
      rw [hWtop, finrank_top, Module.finrank_fintype_fun_eq_card] at hW₀
      simp at hW₀
  have hpar' : IsMaxParabolic2 K (K ⊓ Subgroup.normalizer (Vb : Set G)) := by
    obtain ⟨⟨-, S, hS, hSP⟩, -, hmax⟩ := hpar
    have hP' : IsParabolic2 K (K ⊓ Subgroup.normalizer (Vb : Set G)) :=
      ⟨inf_le_left, S, hS, hSP.trans (hMK ▸ hPle)⟩
    have heq := hmax _ hP' hne (hMK ▸ hPle)
    rw [heq]
    exact ⟨⟨inf_le_right, S, hS, hSP⟩, by
      intro h'
      exact hne (heq.trans h'), hmax⟩
  obtain ⟨W, hWVb, hWN, hWZ, hWsup⟩ :=
    hR1 G K Vb F α β hK hF hblk ⟨hVbU, W₀, hW₀, hmem⟩ hpar'
  have hLtW : Lt L t ≤ Subgroup.normalizer (W : Set G) := fun l hl =>
    hWN ⟨hLK hl, hsupN (d.lt_le_normalizer hl) (hKZ (hLK hl))⟩
  have hUC : blockU K ≤ Subgroup.centralizer (blockZ K : Set G) := fun u hu =>
    Subgroup.mem_centralizer_iff.mpr fun z hz =>
      Subgroup.mem_centralizer_iff.mp (hK.1.2.2.1.1 hu).2 z (hK.1.2.2.1.1 hz.1).1
  have hWZn : W ≤ Subgroup.normalizer (blockZ K : Set G) := fun w hw =>
    Subgroup.mem_normalizer_fintype fun z hz => by
      have hc := Subgroup.mem_centralizer_iff.mp (hUC (hVbU (hWVb hw))) z hz
      rw [← hc, mul_inv_cancel_right]
      exact hz
  have hVW : V ≤ W := by
    have hle : ⁅V, Lt L t⁆ ≤ W := by
      rw [Subgroup.commutator_le]
      intro v hv l hl
      have hvVb : v ∈ W ⊔ blockZ K := by
        rw [hWsup]
        exact Subgroup.mem_sup_left hv
      have hx : v ∈ ((W : Set G) * (blockZ K : Set G)) := by
        rw [← Subgroup.coe_mul_of_left_le_normalizer_right W (blockZ K) hWZn]
        exact hvVb
      obtain ⟨w, hw, z, hz, rfl⟩ := hx
      have hzl : l * z = z * l := Subgroup.mem_centralizer_iff.mp hz.2 l (hLK hl)
      have hw' : l * w⁻¹ * l⁻¹ ∈ W :=
        (Subgroup.mem_normalizer_iff.mp (hLtW hl) _).mp (W.inv_mem hw)
      have e : ⁅w * z, l⁆ = w * (l * w⁻¹ * l⁻¹) := by
        rw [commutatorElement_def]
        calc w * z * l * (w * z)⁻¹ * l⁻¹ = w * (z * l) * z⁻¹ * w⁻¹ * l⁻¹ := by group
          _ = w * (l * w⁻¹ * l⁻¹) := by rw [← hzl]; group
      rw [e]
      exact W.mul_mem hw hw'
    calc V = ⁅V, Lt L t⁆ := d.comm_eq
      _ ≤ W := hle
  have hVU : V ≤ blockU K := le_sup_left.trans hVbU
  let f : ↥V → ↥W₀ := fun v => ⟨Multiplicative.toAdd (β ⟨v, hVU v.2⟩),
    (hmem ⟨v, hVU v.2⟩).mp (Subgroup.mem_sup_left v.2)⟩
  have hf : Function.Injective f := by
    intro a b hab
    have h1 : β ⟨a, hVU a.2⟩ = β ⟨b, hVU b.2⟩ := by
      have := congrArg Subtype.val hab
      exact this
    have h2 : (⟨a, hVU a.2⟩ : ↥(blockU K))⁻¹ * ⟨b, hVU b.2⟩ ∈ β.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, h1, inv_mul_cancel]
    rw [hβk, Subgroup.mem_subgroupOf] at h2
    have h3 : ((a : G))⁻¹ * b ∈ W ⊓ blockZ K :=
      ⟨W.mul_mem (W.inv_mem (hVW a.2)) (hVW b.2), h2⟩
    rw [hWZ, Subgroup.mem_bot] at h3
    apply Subtype.ext
    have := congrArg (fun x => (a : G) * x) h3
    simpa using this.symm
  have hcard := Nat.card_le_card_of_injective f hf
  have : Fintype ↥W₀ := Fintype.ofFinite _
  rw [Nat.card_eq_fintype_card (α := ↥W₀), Module.card_eq_pow_finrank (K := F), hW₀, hF,
    d.card_V] at hcard
  norm_num at hcard

end D127

end S127.L5

open S127.L5 in
theorem lemma12_7_5K41_of (h71 : Setup1271) (h74 : Lemma12_7_4) (hR1 : Sp4BlockLineSplit)
    (hC1 : Lemma12_7_5K41Case1) : Lemma12_7_5K41 := by
  intro G _ _ T L V t h ht h18 hC K _ _ _ _ h41
  have d := d127_of h71 h74 h ht h18
  obtain ⟨hM0, hle, hKK, hcase⟩ := h41
  have hLK : Lt L t ≤ K := hM0.le.trans (hle.trans hKK.le)
  have hLM : Lt L t ≤ Subgroup.normalizer (L : Set G) ⊓ Subgroup.centralizer ({t} : Set G) :=
    le_of_mem_cComp hC.comp
  rcases hcase with h1 | h2 | h3 | h4
  · exact hC1 G T L V t h ht h18 hC hM0 K h1
  · exact d.not_c41Case2 hR1 hLK h2
  · exact d.not_c41Case3 hM0 (le_inf hLM hLK) h3
  · exact d.not_c41Case4 hM0 h4

end CFSG.Quasithin.H13
