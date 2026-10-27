module

public import CFSG.Quasithin.Vol2.Ch12Sec9Lemma5Red
public import CFSG.Quasithin.Vol2.Ch12Sec9Lemma7Act

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin
open scoped IsMulCommutative commutatorElement

namespace L1288

variable {G : Type} [Group G]

theorem comm_mul_right {U Z : Subgroup G} (hc : ∀ a ∈ U, ∀ b ∈ U, a * b * a⁻¹ * b⁻¹ ∈ Z)
    (hZ : ∀ z ∈ Z, ∀ u ∈ U, u * z = z * u) {a b b' : G} (ha : a ∈ U) (hb : b ∈ U)
    (hb' : b' ∈ U) :
    a * (b * b') * a⁻¹ * (b * b')⁻¹ = (a * b * a⁻¹ * b⁻¹) * (a * b' * a⁻¹ * b'⁻¹) := by
  have h1 : b * (a * b' * a⁻¹ * b'⁻¹) = (a * b' * a⁻¹ * b'⁻¹) * b := hZ _ (hc a ha b' hb') b hb
  calc a * (b * b') * a⁻¹ * (b * b')⁻¹
      = (a * b * a⁻¹ * b⁻¹) * (b * (a * b' * a⁻¹ * b'⁻¹)) * b⁻¹ := by group
    _ = (a * b * a⁻¹ * b⁻¹) * ((a * b' * a⁻¹ * b'⁻¹) * b) * b⁻¹ := by rw [h1]
    _ = (a * b * a⁻¹ * b⁻¹) * (a * b' * a⁻¹ * b'⁻¹) := by group

theorem finrank_span_singleton_le' {K M : Type*} [Field K] [AddCommGroup M] [Module K M] (x : M) :
    Module.finrank K (K ∙ x) ≤ 1 := by
  by_cases hx : x = 0
  · rw [hx, Submodule.span_singleton_eq_bot.2 rfl, finrank_bot]
    omega
  · rw [finrank_span_singleton hx]

variable [Finite G]

theorem exists_mem_lOne_of_mulAut {T L V : Subgroup G} {n : ℕ} (h : Hyp1281One G T L V n)
    {V₁ : Subgroup G} (hV₁ : IsTSub T V V₁ 1) (α : MulAut ↥V) (hα3 : α ^ 3 = 1)
    (hαV₁ : ∀ x (hx : x ∈ V₁), ((α ⟨x, hV₁.1 hx⟩ : ↥V) : G) = x) :
    ∃ σ ∈ lOne L V₁, ∀ x (hx : x ∈ V), σ * x * σ⁻¹ = ((α ⟨x, hx⟩ : ↥V) : G) := by
  have hαL : α ∈ autOn L V := by
    rw [autOn_eq_top_of_hyp1281One h]
    exact Subgroup.mem_top _
  obtain ⟨⟨l, hlN⟩, hlL, hlα⟩ := hαL
  have hlL' : l ∈ L := Subgroup.mem_subgroupOf.1 hlL
  have hconj : ∀ x (hx : x ∈ V), l * x * l⁻¹ = ((α ⟨x, hx⟩ : ↥V) : G) := by
    intro x hx
    rw [← hlα]
    rfl
  have hpow : ∀ (m : ℕ) (x : G) (hx : x ∈ V), l ^ m * x * (l ^ m)⁻¹ =
      (((α ^ m) ⟨x, hx⟩ : ↥V) : G) := by
    intro m
    induction m with
    | zero =>
      intro x hx
      simp
    | succ m ih =>
      intro x hx
      rw [show l ^ (m + 1) * x * (l ^ (m + 1))⁻¹ = l * (l ^ m * x * (l ^ m)⁻¹) * l⁻¹ by group,
        ih x hx, hconj _ ((α ^ m) ⟨x, hx⟩).2, pow_succ', MulAut.mul_apply]
  have hlV₁ : l ∈ Subgroup.normalizer (V₁ : Set G) := by
    refine Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.2 fun x hx => ?_)
    have h1 := hconj x (hV₁.1 hx)
    rw [hαV₁ x hx] at h1
    calc x * l = (l * x * l⁻¹) * l := by rw [h1]
      _ = l * x := by group
  obtain ⟨k, hk⟩ := exists_pow_mem_oTwoUpper (L ⊓ Subgroup.normalizer (V₁ : Set G))
    (Subgroup.mem_inf.2 ⟨hlL', hlV₁⟩)
  obtain ⟨r, hr⟩ : ∃ r : ℕ, (2 ^ k * r) % 3 = 1 ∧ l ^ (2 ^ k * r) ∈ lOne L V₁ := by
    rcases two_pow_mod_three k with h1 | h2
    · exact ⟨1, by rw [mul_one, h1], by rw [mul_one]; exact hk⟩
    · exact ⟨2, by rw [Nat.mul_mod, h2], by rw [pow_mul]; exact (lOne L V₁).pow_mem hk 2⟩
  refine ⟨l ^ (2 ^ k * r), hr.2, fun x hx => ?_⟩
  have hred : α ^ (2 ^ k * r) = α := by
    conv_lhs => rw [← Nat.div_add_mod (2 ^ k * r) 3, pow_add, pow_mul, hα3, one_pow, one_mul,
      hr.1, pow_one]
  rw [hpow _ x hx, hred]

end L1288

open L1288 in
theorem lemma12_8_8_five_of (h1222 : Stmt12_2_2) (h12213 : Stmt12_2_13) (h37 : A37ForSQTK)
    (h38 : A38ForSQTK) (h39 : A39ForSQTK) (hOut : OutFact1295) : Lemma12_8_8_five := by
  classical
  intro G _ _ T L V n V₁ V₂ hs hG₁L₁
  by_contra hn3
  have h := hs.hyp
  have hV₁ := hs.v1
  have hn45 : n = 4 ∨ n = 5 := by rcases h.n_mem with rfl | rfl | rfl <;> omega
  have hn : n ≠ 3 := by omega
  obtain ⟨hcard, hsq, hab⟩ := h.card_sq
  obtain ⟨hcV, -⟩ := h.natural
  have hV₁2 : Nat.card V₁ = 2 := by simpa using hV₁.2.1
  have hA := hs.almostSpecial h1222 h12213
  have hV₁Z := hs.le_centerOf h1222 h12213
  have h3 := lemma12_8_8_three h1222 h12213 hs
  obtain ⟨-, hTV⟩ := h.hyp.le_and_normalizes h1222
  have hLV : L ≤ Subgroup.normalizer (V : Set G) := h.hyp.irrPlus.2.2.1
  have hL₁L : lOne L V₁ ≤ L := (oTwoUpper_le _).trans inf_le_left
  have hL₁G₁ : lOne L V₁ ≤ Subgroup.normalizer (V₁ : Set G) :=
    (oTwoUpper_le _).trans inf_le_right
  have hVU : V ≤ u128 V V₁ := le_conjClosure V _
  have hUn : Subgroup.normalizer (V₁ : Set G) ≤ Subgroup.normalizer (u128 V V₁ : Set G) :=
    le_normalizer_conjClosure V _
  have hcomm : ∀ a ∈ u128 V V₁, ∀ b ∈ u128 V V₁, a * b * a⁻¹ * b⁻¹ ∈ V₁ :=
    fun a ha b hb => hA.G22_commutator_mem ha hb
  have hZc : ∀ z ∈ V₁, ∀ u ∈ u128 V V₁, u * z = z * u := fun z hz u hu =>
    Subgroup.mem_centralizer_iff.mp (hV₁Z hz).2 u hu
  obtain ⟨g, hg, v₀, hv₀, w₀, hw₀, hvw⟩ : ∃ g ∈ Subgroup.normalizer (V₁ : Set G), ∃ v ∈ V,
      ∃ w ∈ V, v * (g * w * g⁻¹) ≠ (g * w * g⁻¹) * v := by
    by_contra hall
    push Not at hall
    have hUC : u128 V V₁ ≤ Subgroup.centralizer (V : Set G) :=
      conjClosure_le fun g hg w hw =>
        Subgroup.mem_centralizer_iff.2 fun v hv => hall g hg v hv w hw
    have hVZ : V ≤ zU128 V V₁ := fun v hv => ⟨hVU hv, Subgroup.mem_centralizer_iff.2 fun u hu =>
      (Subgroup.mem_centralizer_iff.1 (hUC hu) v hv).symm⟩
    have hVV₁ : V = V₁ := by
      rw [← h3]
      exact (inf_eq_left.2 hVZ).symm
    have h1 : Nat.card V = Nat.card V₁ := by rw [hVV₁]
    rw [hcard, hV₁2] at h1
    have h2 : n = 1 := Nat.pow_right_injective le_rfl (h1.trans (pow_one 2).symm)
    omega
  have hT : QuasithinUnique.IsSylowTwoOf T (Subgroup.normalizer (V₁ : Set G)) :=
    isSylowTwoOf_of_quasithinIsSylowTwo h.hyp.sylow hV₁.2.2
  have hiso : Nonempty (↥(lOne L V₁) ⧸ CFSG.pCore 2 ↥(lOne L V₁) ≃*
        Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) ∨
      Nonempty (↥(lOne L V₁) ⧸ CFSG.pCore 2 ↥(lOne L V₁) ≃*
        Matrix.SpecialLinearGroup (Fin 4) (ZMod 2)) := by
    obtain ⟨e⟩ := lOne_quotient_mulEquiv h1222 h hn hV₁
    rcases hn45 with h4 | h5
    · subst h4
      exact Or.inl ⟨e⟩
    · subst h5
      exact Or.inr ⟨e⟩
  obtain ⟨d, ⟨hdG₁, -, hdk⟩, hdg⟩ := hOut G _ _ T hL₁G₁ hG₁L₁ hT hiso g hg
  have hyV : d⁻¹ * g ∈ Subgroup.normalizer (V : Set G) := (sup_le (hL₁L.trans hLV) hTV) hdg
  have hw₁V : (d⁻¹ * g) * w₀ * (d⁻¹ * g)⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.mp hyV w₀).mp hw₀
  have hgw : g * w₀ * g⁻¹ = d * ((d⁻¹ * g) * w₀ * (d⁻¹ * g)⁻¹) * d⁻¹ := by group
  rw [hgw] at hvw
  have hdU : ∀ w ∈ V, d * w * d⁻¹ ∈ u128 V V₁ := fun w hw =>
    (Subgroup.mem_normalizer_iff.mp (hUn hdG₁) w).mp (hVU hw)
  have hfR : ∀ v ∈ V, ∀ w ∈ V, ∀ w' ∈ V,
      ⁅v, d * (w * w') * d⁻¹⁆ = ⁅v, d * w * d⁻¹⁆ * ⁅v, d * w' * d⁻¹⁆ := by
    intro v hv w hw w' hw'
    have e : d * (w * w') * d⁻¹ = (d * w * d⁻¹) * (d * w' * d⁻¹) := by group
    simp only [commutatorElement_def, e]
    exact comm_mul_right hcomm hZc (hVU hv) (hdU w hw) (hdU w' hw')
  have hf₁L : ∀ z ∈ V₁, ∀ w ∈ V, ⁅z, d * w * d⁻¹⁆ = 1 := fun z hz w hw =>
    commutatorElement_eq_one_iff_mul_comm.2 (hZc z hz _ (hdU w hw)).symm
  have hf₁R : ∀ v ∈ V, ∀ z ∈ V₁, ⁅v, d * z * d⁻¹⁆ = 1 := fun v hv z hz =>
    commutatorElement_eq_one_iff_mul_comm.2
      (hZc _ ((Subgroup.mem_normalizer_iff.mp hdG₁ z).mp hz) v (hVU hv))
  have hO : pCoreOf 2 (lOne L V₁) ≤ pCoreOf 2 (Subgroup.normalizer (V₁ : Set G)) :=
    LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
      ((LieType.BorelTits.pCoreOf_le 2 _).trans hL₁G₁)
      (hG₁L₁.trans (LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 _))
      (LieType.BorelTits.pCoreOf_isPGroup 2 _)
  have h84 := lemma12_8_4_four h1222 h37 h38 h39 G T L V n h V₁ _ hV₁
    (isHzOne_normalizer h12213 h hV₁)
  have hinv : ∀ σ ∈ lOne L V₁, ∀ v ∈ V, ∀ w ∈ V,
      ⁅σ * v * σ⁻¹, d * (σ * w * σ⁻¹) * d⁻¹⁆ = ⁅v, d * w * d⁻¹⁆ := by
    intro σ hσ v hv w hw
    have hσG₁ := hL₁G₁ hσ
    have hoP : d * σ * d⁻¹ * σ⁻¹ ∈ pCoreOf 2 (Subgroup.normalizer (V₁ : Set G)) := hO (hdk σ hσ)
    rw [← h84] at hoP
    obtain ⟨-, -, hoU⟩ := hoP
    have huU : σ * (d * w * d⁻¹) * σ⁻¹ ∈ u128 V V₁ :=
      (Subgroup.mem_normalizer_iff.mp (hUn hσG₁) _).mp (hdU w hw)
    obtain ⟨z, hzV₁, hzdef⟩ : ∃ z ∈ V₁,
        d * (σ * w * σ⁻¹) * d⁻¹ = z * (σ * (d * w * d⁻¹) * σ⁻¹) :=
      ⟨_, hoU _ huU, by group⟩
    have hσv : σ * v * σ⁻¹ ∈ u128 V V₁ :=
      hVU ((Subgroup.mem_normalizer_iff.mp (hLV (hL₁L hσ)) v).mp hv)
    rw [hzdef, commutatorElement_def, comm_mul_right hcomm hZc hσv (hV₁Z hzV₁).1 huU]
    have hxz : σ * v * σ⁻¹ * z * (σ * v * σ⁻¹)⁻¹ * z⁻¹ = 1 := by
      rw [← commutatorElement_def]
      exact commutatorElement_eq_one_iff_mul_comm.2 (hZc z hzV₁ _ hσv)
    have hc := hcomm v (hVU hv) _ (hdU w hw)
    have e2 : σ * v * σ⁻¹ * (σ * (d * w * d⁻¹) * σ⁻¹) * (σ * v * σ⁻¹)⁻¹ *
        (σ * (d * w * d⁻¹) * σ⁻¹)⁻¹ =
        σ * (v * (d * w * d⁻¹) * v⁻¹ * (d * w * d⁻¹)⁻¹) * σ⁻¹ := by group
    rw [hxz, one_mul, e2, L1297.conj_eq_of_mem_normalizer hV₁2 hc hσG₁, commutatorElement_def]
  let _ := zmodModuleOf hsq
  have : Module.Finite (ZMod 2) (Additive ↥V) := Module.Finite.of_finite
  have hdimV : Module.finrank (ZMod 2) (Additive ↥V) = n := by
    have h1 := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive ↥V)
    rw [Nat.card_zmod] at h1
    have h2 : Nat.card (Additive ↥V) = 2 ^ n := hcard
    rw [h2] at h1
    exact (Nat.pow_right_injective le_rfl h1).symm
  have hdimV₁ : Module.finrank (ZMod 2) (subOf (V := V) V₁) = 1 :=
    finrank_subOf (i := 1) hV₁.1 (by rw [hV₁2, pow_one])
  have hexists : ∀ S : Submodule (ZMod 2) (Additive ↥V), Module.finrank (ZMod 2) S < n →
      ∃ b, b ∉ S := by
    intro S hS
    by_contra hall
    push Not at hall
    have htop : S = ⊤ := eq_top_iff.2 fun x _ => hall x
    rw [htop, finrank_top, hdimV] at hS
    exact lt_irrefl _ hS
  have hmem : ∀ x : Additive ↥V, x ∈ subOf (V := V) V₁ ↔
      ((Additive.toMul x : ↥V) : G) ∈ V₁ := fun x => mem_subOf
  have hindep : ∀ {x y : G} (hx : x ∈ V) (hy : y ∈ V), x ∉ V₁ → x * y⁻¹ ∉ V₁ →
      Additive.ofMul (⟨x, hx⟩ : ↥V) ∉ subOf (V := V) V₁ ⊔ (ZMod 2) ∙
        Additive.ofMul (⟨y, hy⟩ : ↥V) := by
    intro x y hx hy hxV₁ hxy hmem'
    obtain ⟨p, hp, q, hq, hpq⟩ := Submodule.mem_sup.1 hmem'
    obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.1 hq
    rcases zmod_two_cases t with rfl | rfl
    · rw [zero_smul, add_zero] at hpq
      exact hxV₁ (by have := (hmem p).1 hp; rwa [hpq] at this)
    · rw [one_smul] at hpq
      apply hxy
      have h1 := (hmem p).1 hp
      have h2 : p = Additive.ofMul (⟨x, hx⟩ : ↥V) - Additive.ofMul ⟨y, hy⟩ := by
        rw [← hpq]; abel
      rw [h2, toMul_sub, toMul_ofMul, toMul_ofMul, Subgroup.coe_div, div_eq_mul_inv] at h1
      exact h1
  have hfin : ∀ S : Submodule (ZMod 2) (Additive ↥V), FiniteDimensional (ZMod 2) S :=
    fun S => inferInstance
  have hrank : ∀ (S : Submodule (ZMod 2) (Additive ↥V)) (x : Additive ↥V),
      Module.finrank (ZMod 2) ↥(S ⊔ (ZMod 2) ∙ x) ≤ Module.finrank (ZMod 2) S + 1 := by
    intro S x
    exact (Submodule.finrank_add_le_finrank_add_finrank S _).trans
      (Nat.add_le_add_left (finrank_span_singleton_le' x) _)
  have hrot : ∀ c ∈ V, ∀ w ∈ V, c ∉ V₁ → w ∉ V₁ → w * c⁻¹ ∉ V₁ → ⁅c, d * w * d⁻¹⁆ = 1 := by
    intro c hc w hw hcV₁ hwV₁ hwc
    have ha : Additive.ofMul (⟨w, hw⟩ : ↥V) ∉
        subOf (V := V) V₁ ⊔ (ZMod 2) ∙ Additive.ofMul (⟨c, hc⟩ : ↥V) := hindep hw hc hwV₁ hwc
    obtain ⟨b, hb⟩ := hexists ((subOf (V := V) V₁ ⊔ (ZMod 2) ∙ Additive.ofMul (⟨c, hc⟩ : ↥V)) ⊔
      (ZMod 2) ∙ Additive.ofMul (⟨w, hw⟩ : ↥V)) (by
        have h1 := hrank (subOf (V := V) V₁ ⊔ (ZMod 2) ∙ Additive.ofMul (⟨c, hc⟩ : ↥V))
          (Additive.ofMul (⟨w, hw⟩ : ↥V))
        have h2 := hrank (subOf (V := V) V₁) (Additive.ofMul (⟨c, hc⟩ : ↥V))
        omega)
    have ha' : Additive.ofMul (⟨w, hw⟩ : ↥V) ∉
        (subOf (V := V) V₁ ⊔ (ZMod 2) ∙ Additive.ofMul (⟨c, hc⟩ : ↥V)) ⊔ (ZMod 2) ∙ b := by
      intro hmem'
      obtain ⟨p, hp, q, hq, hpq⟩ := Submodule.mem_sup.1 hmem'
      obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.1 hq
      rcases zmod_two_cases t with rfl | rfl
      · rw [zero_smul, add_zero] at hpq
        exact ha (hpq ▸ hp)
      · rw [one_smul] at hpq
        apply hb
        have e : b = Additive.ofMul (⟨w, hw⟩ : ↥V) - p := by rw [← hpq]; abel
        rw [e]
        exact Submodule.sub_mem _ (Submodule.mem_sup_right (Submodule.mem_span_singleton_self _))
          (Submodule.mem_sup_left hp)
    obtain ⟨ρ, hρ3, hρa, hρb, hρP⟩ := exists_rotation ha' hb
    have hα3 : mulAutOfLin ρ ^ 3 = 1 := by
      refine MulEquiv.ext fun x => ?_
      rw [pow_three, MulAut.mul_apply, MulAut.mul_apply, mulAutOfLin_apply, mulAutOfLin_apply,
        mulAutOfLin_apply, ofMul_toMul, ofMul_toMul, hρ3, toMul_ofMul, MulAut.one_apply]
    have hαV₁ : ∀ x (hx : x ∈ V₁), ((mulAutOfLin ρ ⟨x, hV₁.1 hx⟩ : ↥V) : G) = x := by
      intro x hx
      rw [mulAutOfLin_apply,
        hρP _ (Submodule.mem_sup_left ((hmem (Additive.ofMul ⟨x, hV₁.1 hx⟩)).2 hx)), toMul_ofMul]
    obtain ⟨σ, hσ, hσx⟩ := exists_mem_lOne_of_mulAut h hV₁ (mulAutOfLin ρ) hα3 hαV₁
    set z : G := ((Additive.toMul b : ↥V) : G) with hz
    have hzV : z ∈ V := (Additive.toMul b).2
    have hσc : σ * c * σ⁻¹ = c := by
      rw [hσx c hc, mulAutOfLin_apply,
        hρP _ (Submodule.mem_sup_right (Submodule.mem_span_singleton_self _)), toMul_ofMul]
    have hσw : σ * w * σ⁻¹ = z := by
      rw [hσx w hw, mulAutOfLin_apply, hρa]
    have hσz : σ * z * σ⁻¹ = w * z := by
      rw [hσx z hzV, mulAutOfLin_apply]
      have hbz : Additive.ofMul (⟨z, hzV⟩ : ↥V) = b := rfl
      rw [hbz, hρb]
      have hneg : ∀ y : Additive ↥V, -y = y := fun y => by
        have h1 : y + y = 0 := by
          rw [← one_smul (ZMod 2) y, ← add_smul, show (1 + 1 : ZMod 2) = 0 from rfl, zero_smul]
        exact neg_eq_of_add_eq_zero_left h1
      rw [sub_eq_add_neg, hneg, hneg, toMul_add, Subgroup.coe_mul, toMul_ofMul]
    have e1 := hinv σ hσ c hc w hw
    rw [hσc, hσw] at e1
    have e2 := hinv σ hσ c hc z hzV
    rw [hσc, hσz, hfR c hc w hw z hzV] at e2
    rw [e1] at e2
    exact (mul_left_inj _).mp (e2.trans (one_mul _).symm)
  have hall : ∀ v ∈ V, ∀ w ∈ V, ⁅v, d * w * d⁻¹⁆ = 1 := by
    intro v hv w hw
    by_cases hvV₁ : v ∈ V₁
    · exact hf₁L v hvV₁ w hw
    by_cases hwV₁ : w ∈ V₁
    · exact hf₁R v hv w hwV₁
    by_cases hwv : w * v⁻¹ ∈ V₁
    · have e : w = (w * v⁻¹) * v := by group
      rw [e, hfR v hv _ (V.mul_mem hw (V.inv_mem hv)) v hv, hf₁R v hv _ hwv, one_mul]
      obtain ⟨b, hb⟩ := hexists (subOf (V := V) V₁ ⊔ (ZMod 2) ∙ Additive.ofMul (⟨v, hv⟩ : ↥V))
        (by have := hrank (subOf (V := V) V₁) (Additive.ofMul (⟨v, hv⟩ : ↥V)); omega)
      set y : G := ((Additive.toMul b : ↥V) : G) with hy
      have hyV : y ∈ V := (Additive.toMul b).2
      have hby : Additive.ofMul (⟨y, hyV⟩ : ↥V) = b := rfl
      have hyV₁ : y ∉ V₁ := fun h1 =>
        hb (Submodule.mem_sup_left ((hmem _).2 (by rw [← hby, toMul_ofMul]; exact h1)))
      have hyv : y * v⁻¹ ∉ V₁ := by
        intro h1
        apply hb
        have e3 : b = Additive.ofMul (⟨y * v⁻¹, V.mul_mem hyV (V.inv_mem hv)⟩ : ↥V) +
            Additive.ofMul (⟨v, hv⟩ : ↥V) := by
          rw [← ofMul_mul, ← hby]
          congr 1
          apply Subtype.ext
          simp
        rw [e3]
        exact Submodule.add_mem _ (Submodule.mem_sup_left ((hmem _).2 h1))
          (Submodule.mem_sup_right (Submodule.mem_span_singleton_self _))
      have hvinv : v⁻¹ = v := inv_eq_of_mul_eq_one_right (by rw [← pow_two]; exact hsq v hv)
      have h1 := hrot v hv y hyV hvV₁ hyV₁ hyv
      have h2 := hrot v hv (y * v) (V.mul_mem hyV hv) hvV₁
        (fun h4 => hyv (by rw [hvinv]; exact h4))
        (by rw [show y * v * v⁻¹ = y by group]; exact hyV₁)
      rw [hfR v hv y hyV v hv, h1, one_mul] at h2
      exact h2
    · exact hrot v hv w hw hvV₁ hwV₁ hwv
  exact hvw (commutatorElement_eq_one_iff_mul_comm.1 (hall v₀ hv₀ _ hw₁V))

end CFSG.Quasithin.H13
