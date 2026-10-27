module

public import CFSG.Quasithin.Vol2.Ch12Sec9Lemma9Core

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint
open scoped IsMulCommutative commutatorElement

@[expose] def OutFact1297 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (X K S : Subgroup G), K ≤ X →
    X ≤ Subgroup.normalizer (K : Set G) → QuasithinUnique.IsSylowTwoOf S X →
    (Nonempty (↥K ⧸ CFSG.pCore 2 ↥K ≃* alternatingGroup (Fin 7)) ∨
      Nonempty (↥K ⧸ CFSG.pCore 2 ↥K ≃* Matrix.SpecialLinearGroup (Fin 4) (ZMod 2)) ∨
      Nonempty (↥K ⧸ CFSG.pCore 2 ↥K ≃* Matrix.SpecialLinearGroup (Fin 5) (ZMod 2))) →
    ∀ x ∈ X, ∃ d ∈ centralizerMod (pCoreOf 2 K) X K, d⁻¹ * x ∈ K ⊔ S

@[expose] def Core1297 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G) (n : ℕ), Cx1291 G T L V n →
    ∀ V₁ V₂ K₁ : Subgroup G, IsTSub T V V₁ 1 → IsTSub T V V₂ 2 → V₁ ≤ V₂ → lOne L V₁ ≤ K₁ →
      quasithinIsCComponent K₁ (Subgroup.normalizer (V₁ : Set G)) →
      (K₁ ⊔ T) ⊓ Subgroup.normalizer (V₂ : Set G) ≤ lOne L V₁ ⊔ T

namespace L1297

variable {G : Type} [Group G] [Finite G]

theorem commutator_mem_of_commutator_mem {T L V : Subgroup G} {n : ℕ}
    (h : Hyp1281One G T L V n) (hn4 : 4 ≤ n) {V₁ : Subgroup G} (hV₁ : IsTSub T V V₁ 1) {d : G}
    (hdV : d ∈ Subgroup.normalizer (V : Set G)) (hdV₁ : d ∈ Subgroup.normalizer (V₁ : Set G))
    (hc : ∀ l ∈ lOne L V₁, ∀ v ∈ V,
      (d * l * d⁻¹ * l⁻¹) * v * (d * l * d⁻¹ * l⁻¹)⁻¹ * v⁻¹ ∈ V₁) :
    ∀ v ∈ V, d * v * d⁻¹ * v⁻¹ ∈ V₁ := by
  classical
  obtain ⟨hcard, hsq, hab⟩ := h.card_sq
  obtain ⟨hcV, -⟩ := h.natural
  have hV₁2 : Nat.card V₁ = 2 := by simpa using hV₁.2.1
  by_contra hne
  push Not at hne
  obtain ⟨c, hcV', hcd⟩ := hne
  set e := d * c * d⁻¹ with hedef
  have heV : e ∈ V := (Subgroup.mem_normalizer_iff.1 hdV c).1 hcV'
  have hcd' : e * c⁻¹ ∉ V₁ := hcd
  let _ := zmodModuleOf hsq
  set c' : Additive ↥V := Additive.ofMul ⟨c, hcV'⟩ with hc'def
  set e' : Additive ↥V := Additive.ofMul ⟨e, heV⟩ with he'def
  have hmem : ∀ x : Additive ↥V, x ∈ subOf (V := V) V₁ ↔
      ((Additive.toMul x : ↥V) : G) ∈ V₁ := fun x => mem_subOf
  have he' : e' ∉ subOf (V := V) V₁ ⊔ (ZMod 2) ∙ c' := by
    intro hx
    obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.1 hx
    obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.1 hz
    rcases zmod_two_cases t with rfl | rfl
    · rw [zero_smul, add_zero] at hyz
      have heV₁ : e ∈ V₁ := by
        have := (hmem y).1 hy
        rwa [hyz] at this
      have hcV₁ : c ∈ V₁ := by
        have h1 := (Subgroup.mem_normalizer_iff.1 (Subgroup.inv_mem _ hdV₁) e).1 heV₁
        rwa [hedef, show d⁻¹ * (d * c * d⁻¹) * d⁻¹⁻¹ = c by group] at h1
      exact hcd' (V₁.mul_mem heV₁ (V₁.inv_mem hcV₁))
    · rw [one_smul] at hyz
      apply hcd'
      have h1 := (hmem y).1 hy
      have h2 : y = e' - c' := by rw [← hyz]; abel
      rw [h2, toMul_sub, he'def, hc'def, toMul_ofMul, toMul_ofMul, Subgroup.coe_div,
        div_eq_mul_inv] at h1
      exact h1
  have : Module.Finite (ZMod 2) (Additive ↥V) := Module.Finite.of_finite
  have hrank : Module.finrank (ZMod 2) (Additive ↥V) = n := by
    have h1 := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive ↥V)
    rw [Nat.card_zmod] at h1
    have h3 : Nat.card (Additive ↥V) = 2 ^ n := hcard
    exact Nat.pow_right_injective le_rfl (h1.symm.trans h3)
  obtain ⟨b', hb'⟩ : ∃ b' : Additive ↥V,
      b' ∉ subOf (V := V) V₁ ⊔ (ZMod 2) ∙ c' ⊔ (ZMod 2) ∙ e' := by
    by_contra hall
    push Not at hall
    have htop : subOf (V := V) V₁ ⊔ (ZMod 2) ∙ c' ⊔ (ZMod 2) ∙ e' = ⊤ :=
      eq_top_iff.2 fun x _ => hall x
    have h1 := Submodule.finrank_add_le_finrank_add_finrank
      (subOf (V := V) V₁ ⊔ (ZMod 2) ∙ c') ((ZMod 2) ∙ e')
    have h2 := Submodule.finrank_add_le_finrank_add_finrank (subOf (V := V) V₁) ((ZMod 2) ∙ c')
    have hspan1 : ∀ x : Additive ↥V, Module.finrank (ZMod 2) ↥((ZMod 2) ∙ x) ≤ 1 := fun x => by
      have := finrank_span_le_card (R := ZMod 2) ({x} : Set (Additive ↥V))
      simpa using this
    have h3 := hspan1 c'
    have h4 := hspan1 e'
    rw [htop, finrank_top, hrank] at h1
    rw [finrank_subOf hV₁.1 hV₁.2.1] at h2
    omega
  have ha : e' ∉ (subOf (V := V) V₁ ⊔ (ZMod 2) ∙ c') ⊔ (ZMod 2) ∙ b' := by
    intro hx
    obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.1 hx
    obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.1 hz
    rcases zmod_two_cases t with rfl | rfl
    · rw [zero_smul, add_zero] at hyz
      exact he' (hyz ▸ hy)
    · rw [one_smul] at hyz
      apply hb'
      have h2 : b' = e' - y := by rw [← hyz]; abel
      rw [h2]
      exact Submodule.sub_mem _ (Submodule.mem_sup_right (Submodule.mem_span_singleton_self e'))
        (Submodule.mem_sup_left hy)
  obtain ⟨ρ, hρ3, hρa, hρb, hρP⟩ := exists_rotation ha hb'
  have hαL : mulAutOfLin ρ ∈ autOn L V := by
    rw [autOn_eq_top_of_hyp1281One h]
    exact Subgroup.mem_top _
  obtain ⟨⟨l, hlN⟩, hlL, hlα⟩ := hαL
  have hlL' : l ∈ L := Subgroup.mem_subgroupOf.1 hlL
  have hpow : ∀ (m : ℕ) (x : G) (hx : x ∈ V), l ^ m * x * (l ^ m)⁻¹ =
      ((Additive.toMul ((ρ ^ m) (Additive.ofMul ⟨x, hx⟩)) : ↥V) : G) := by
    have hconj : ∀ x (hx : x ∈ V), l * x * l⁻¹ =
        ((Additive.toMul (ρ (Additive.ofMul ⟨x, hx⟩)) : ↥V) : G) := by
      intro x hx
      rw [← mulAutOfLin_apply, ← hlα]
      rfl
    intro m
    induction m with
    | zero =>
      intro x hx
      simp
    | succ m ih =>
      intro x hx
      rw [show l ^ (m + 1) * x * (l ^ (m + 1))⁻¹ = l * (l ^ m * x * (l ^ m)⁻¹) * l⁻¹ by group,
        ih x hx, hconj _ (Additive.toMul ((ρ ^ m) (Additive.ofMul ⟨x, hx⟩))).2, pow_succ',
        LinearEquiv.mul_apply]
      rfl
  have hlV₁ : l ∈ Subgroup.normalizer (V₁ : Set G) := by
    refine Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.2 fun x hx => ?_)
    have h1 := hpow 1 x (hV₁.1 hx)
    rw [pow_one, pow_one,
      hρP _ (Submodule.mem_sup_left ((hmem (Additive.ofMul ⟨x, hV₁.1 hx⟩)).2 hx)),
      toMul_ofMul] at h1
    have h2 : l * x = x * l := by
      calc l * x = (l * x * l⁻¹) * l := by group
        _ = x * l := by rw [h1]
    exact h2.symm
  obtain ⟨k, hk⟩ := exists_pow_mem_oTwoUpper (L ⊓ Subgroup.normalizer (V₁ : Set G))
    (Subgroup.mem_inf.2 ⟨hlL', hlV₁⟩)
  set σ := l ^ 2 ^ k with hσ
  have hρ3' : ρ ^ 3 = 1 := LinearEquiv.ext fun x => by
    rw [pow_three, LinearEquiv.mul_apply, LinearEquiv.mul_apply]
    exact hρ3 x
  have hred : ρ ^ 2 ^ k = ρ ^ (2 ^ k % 3) := by
    conv_lhs => rw [← Nat.div_add_mod (2 ^ k) 3, pow_add, pow_mul, hρ3', one_pow, one_mul]
  have hσc : σ * c * σ⁻¹ = c := by
    rw [hσ, hpow _ c hcV', hred]
    have hcP : c' ∈ subOf (V := V) V₁ ⊔ (ZMod 2) ∙ c' :=
      Submodule.mem_sup_right (Submodule.mem_span_singleton_self c')
    rcases two_pow_mod_three k with h1 | h2
    · rw [h1, pow_one, hρP _ hcP]
      rfl
    · rw [h2, pow_two, LinearEquiv.mul_apply, hρP _ hcP, hρP _ hcP]
      rfl
  have hσe : σ * e * σ⁻¹ * e⁻¹ ∉ V₁ := by
    intro hx
    rw [hσ, hpow _ e heV, hred] at hx
    apply hb'
    rcases two_pow_mod_three k with h1 | h2
    · rw [h1, pow_one] at hx
      have h3 : ρ e' - e' ∈ subOf (V := V) V₁ := by
        rw [hmem, toMul_sub, Subgroup.coe_div, div_eq_mul_inv]
        exact hx
      rw [hρa] at h3
      have h4 : b' = (b' - e') + e' := by abel
      rw [h4]
      exact Submodule.add_mem _ (Submodule.mem_sup_left (Submodule.mem_sup_left h3))
        (Submodule.mem_sup_right (Submodule.mem_span_singleton_self e'))
    · rw [h2, pow_two, LinearEquiv.mul_apply, hρa, hρb] at hx
      have h3 : (-e' - b') - e' ∈ subOf (V := V) V₁ := by
        rw [hmem, toMul_sub, Subgroup.coe_div, div_eq_mul_inv]
        exact hx
      have h2x : e' + e' = 0 := by
        rw [← one_smul (ZMod 2) e', ← add_smul, show (1 + 1 : ZMod 2) = 0 from rfl, zero_smul]
      have h4 : b' = -((-e' - b') - e') - (e' + e') := by abel
      rw [h4, h2x, sub_zero]
      exact Submodule.neg_mem _ (Submodule.mem_sup_left (Submodule.mem_sup_left h3))
  have hσL₁ : σ ∈ lOne L V₁ := hk
  have hfV : σ * e * σ⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.1
    (Subgroup.pow_mem _ (h.hyp.irrPlus.2.2.1 hlL') _) e).1 heV
  have hx1 := hc σ hσL₁ (σ * e * σ⁻¹) hfV
  have hkey : (d * σ * d⁻¹ * σ⁻¹) * (σ * e * σ⁻¹) * (d * σ * d⁻¹ * σ⁻¹)⁻¹ = e := by
    calc (d * σ * d⁻¹ * σ⁻¹) * (σ * e * σ⁻¹) * (d * σ * d⁻¹ * σ⁻¹)⁻¹ =
          d * (σ * c * σ⁻¹) * d⁻¹ := by rw [hedef]; group
      _ = e := by rw [hσc, hedef]
  rw [hkey] at hx1
  apply hσe
  have h1 := V₁.inv_mem hx1
  rwa [show (e * (σ * e * σ⁻¹)⁻¹)⁻¹ = σ * e * σ⁻¹ * e⁻¹ by group] at h1

theorem centralizerMod_le_normalizer (h1222 : Stmt12_2_2) (h12213 : Stmt12_2_13)
    (h37 : A37ForSQTK) (h38 : A38ForSQTK) {T L V : Subgroup G} {n : ℕ}
    (hcx : Cx1291 G T L V n) {V₁ K₁ : Subgroup G} (hV₁ : IsTSub T V V₁ 1)
    (hLK : lOne L V₁ ≤ K₁) (hK : quasithinIsCComponent K₁ (Subgroup.normalizer (V₁ : Set G)))
    (hDM : centralizerMod (pCoreOf 2 K₁) (Subgroup.normalizer (V₁ : Set G)) K₁ ≤
      Subgroup.normalizer (L : Set G))
    {W : Subgroup G} (hV₁W : V₁ ≤ W) (hWV : W ≤ V) :
    centralizerMod (pCoreOf 2 K₁) (Subgroup.normalizer (V₁ : Set G)) K₁ ≤
      Subgroup.normalizer (W : Set G) := by
  have h := hcx.hyp
  have hyp := h.hyp
  have hn : n ≠ 3 := by rcases hcx.n45 with h | h <;> omega
  have hn4 : 4 ≤ n := by rcases hcx.n45 with h | h <;> omega
  intro d hd
  have hdM := hDM hd
  obtain ⟨hdG₁, -, hdc⟩ := hd
  have hdV : d ∈ Subgroup.normalizer (V : Set G) := by
    rcases hyp.ti_of_1222 h1222 hdM with h1 | h1
    · exact SteinbergBS.mem_normalizer_of_conjugate_eq h1
    · exfalso
      have h2 : V₁ ≤ V ⊓ CFSG.conjugate V d := le_inf hV₁.1 fun x hx => by
        rw [SteinbergBS.mem_conjugate_iff]
        exact hV₁.1 ((Subgroup.mem_normalizer_iff.1 hdG₁ x).1 hx)
      rw [h1, le_bot_iff] at h2
      have h3 := hV₁.2.1
      rw [h2, Subgroup.card_bot] at h3
      norm_num at h3
  have hA := lemma12_8_4_one h1222 h hV₁ (isHzOne_normalizer h12213 h hV₁)
  have hK₁G₁ : K₁ ≤ Subgroup.normalizer (V₁ : Set G) := le_of_mem_cComp (show K₁ ∈ cComp _ from hK)
  have hK₁n := normalizer_le_of_lOne_le h1222 h37 h38 h hn hV₁ hLK hK
  have hO₂ : pCoreOf 2 K₁ ≤ pCoreOf 2 (Subgroup.normalizer (V₁ : Set G)) :=
    LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
      ((LieType.BorelTits.pCoreOf_le 2 K₁).trans hK₁G₁)
      (hK₁n.trans (LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 K₁))
      (LieType.BorelTits.pCoreOf_isPGroup 2 K₁)
  have hVQ : ∀ y ∈ pCoreOf 2 K₁, ∀ v ∈ V, y * v * y⁻¹ * v⁻¹ ∈ V₁ := by
    intro y hy v hv
    have h1 := V₁.inv_mem (commutator_mem_of_mem_pCoreOf hA (le_conjClosure V _ hv) (hO₂ hy))
    rwa [show (v * y * v⁻¹ * y⁻¹)⁻¹ = y * v * y⁻¹ * v⁻¹ by group] at h1
  have hkey := commutator_mem_of_commutator_mem h hn4 hV₁ hdV hdG₁
    (fun l hl v hv => hVQ _ (hdc l (hLK hl)) v hv)
  rw [Subgroup.mem_normalizer_iff]
  intro w
  constructor
  · intro hw
    have h1 := W.mul_mem (hV₁W (hkey w (hWV hw))) hw
    rwa [inv_mul_cancel_right] at h1
  · intro hw
    have hwV : w ∈ V := by
      have h1 := (Subgroup.mem_normalizer_iff.1 (Subgroup.inv_mem _ hdV) _).1 (hWV hw)
      rwa [show d⁻¹ * (d * w * d⁻¹) * d⁻¹⁻¹ = w by group] at h1
    have h1 := W.mul_mem (W.inv_mem (hV₁W (hkey w hwV))) hw
    rwa [show (d * w * d⁻¹ * w⁻¹)⁻¹ * (d * w * d⁻¹) = w by group] at h1

end L1297

theorem claim12_9_7_of_core (h1222 : Stmt12_2_2) (h12213 : Stmt12_2_13) (h37 : A37ForSQTK)
    (h38 : A38ForSQTK) (h39 : A39ForSQTK) (h1295 : Lemma12_9_5) (hOut : OutFact1297)
    (hCore : Core1297) : Claim12_9_7 := by
  intro G _ _ T L V n hcx V₂ hV₂ x hx
  have h := hcx.hyp
  have hyp := h.hyp
  have hn : n ≠ 3 := by rcases hcx.n45 with h | h <;> omega
  obtain ⟨V₁, hV₁⟩ := exists_v1_of_hyp1281One h1222 h
  have hV₁₂ : V₁ ≤ V₂ := by
    rcases tinv_comparable_of_hyp1281One h1222 h hV₁.1 hV₂.1 hV₁.2.2 hV₂.2.2 with hle | hle
    · exact hle
    · exfalso
      have h1 := Subgroup.card_le_of_le hle
      rw [hV₁.2.1, hV₂.2.1] at h1
      norm_num at h1
  obtain ⟨K₁, hLK, hK, hK₁n⟩ := exists_cComp_normalizer_ge_lOne h1222 h37 h38 h39 h hn hV₁
  obtain ⟨⟨hDM, -⟩, hiso, -⟩ := h1295 G T L V n hcx V₁ K₁ hV₁ hLK hK
  have hK₁G₁ : K₁ ≤ Subgroup.normalizer (V₁ : Set G) := le_of_mem_cComp (show K₁ ∈ cComp _ from hK)
  have hxG₁ : x ∈ Subgroup.normalizer (V₁ : Set G) :=
    Subgroup.centralizer_le_normalizer _ (Subgroup.centralizer_le hV₁₂ hx)
  obtain ⟨d, hd, hdx⟩ := hOut G (Subgroup.normalizer (V₁ : Set G)) K₁ T hK₁G₁ hK₁n
    (isSylowTwoOf_of_quasithinIsSylowTwo hyp.sylow hV₁.2.2) hiso x hxG₁
  have hdV₂ := L1297.centralizerMod_le_normalizer h1222 h12213 h37 h38 hcx hV₁ hLK hK hDM hV₁₂
    hV₂.1 hd
  have hy : d⁻¹ * x ∈ (K₁ ⊔ T) ⊓ Subgroup.normalizer (V₂ : Set G) :=
    ⟨hdx, Subgroup.mul_mem _ (Subgroup.inv_mem _ hdV₂)
      (Subgroup.centralizer_le_normalizer _ hx)⟩
  have hyM := hCore G T L V n hcx V₁ V₂ K₁ hV₁ hV₂ hV₁₂ hLK hK hy
  have hL₁T : lOne L V₁ ⊔ T ≤ Subgroup.normalizer (L : Set G) :=
    sup_le ((oTwoUpper_le _).trans (inf_le_left.trans Subgroup.le_normalizer)) hyp.normalizes
  rw [show x = d * (d⁻¹ * x) by group]
  exact Subgroup.mul_mem _ (hDM hd) (hL₁T hyM)

end CFSG.Quasithin.H13
