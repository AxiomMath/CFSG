module

public import CFSG.Quasithin.EmptyFaithful.S151V7
public import CFSG.Quasithin.EmptyFaithful.S151V6

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.FLc
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem v2_le_blockU_four (hK : KnownFacts15122Types) {T Mc M Z₁ Z₂ V₁ V₂ L : Subgroup G}
    (h15 : Lemma1515Concl T Mc M) (hc : Ctx15124 T Mc M Z₁ Z₂ V₁ V₂ L) (hb : IsLnBlock L 3)
    (h4 : Ce15Four T Mc M) : V₂ ≤ blockU L := by
  have hS := hc.ctx.setting
  have hq := hc.ctx.qtfe
  have hMf := hc.ctx.mf
  obtain ⟨hY₀L, -, hnorm, c, hcY, hfpf⟩ := v2_data hK h15 hc hb
  obtain ⟨hZ₂V₂, -, hZ₂Q, -, -⟩ := z2_facts hK h15 hc hb h4.not_seven
  have hr := hS.ranks_four h4
  have hcomm : ∀ a ∈ V₂, ∀ b ∈ V₂, a * b = b * a := by
    have hV2ab : IsElemAbelian 2 V₂ := isElemAbelian_mono151 hS.v2_le (hS.V_isElemAbelian hq hMf)
    intro a ha b hb'
    have := hV2ab.1
    have h1 := mul_comm' (⟨a, ha⟩ : V₂) ⟨b, hb'⟩
    exact congrArg (fun z : V₂ => (z : G)) h1
  have hcL : c ∈ L := hY₀L hcY
  have hU := inf_blockQ_le_blockU hcomm hcL (hnorm c hcY) hfpf
  have hZ2 : 1 < Nat.card Z₂ := by rw [hr.2.2.2]; norm_num
  have hfin : Fintype Z₂ := Fintype.ofFinite Z₂
  have hnt : Nontrivial Z₂ := by
    rw [← Fintype.one_lt_card_iff_nontrivial, ← Nat.card_eq_fintype_card]; exact hZ2
  obtain ⟨⟨z, hz⟩, hz1⟩ := exists_ne (1 : Z₂)
  have hz1' : z ≠ 1 := fun h => hz1 (Subtype.ext h)
  have hzV : z ∈ V₂ := hZ₂V₂ hz
  have hzQ : z ∈ blockQ L := hZ₂Q hz
  have hz'V : c * z * c⁻¹ ∈ V₂ := hnorm c hcY z hzV
  have hz'Q : c * z * c⁻¹ ∈ blockQ L :=
    (Subgroup.mem_normalizer_iff.mp (L_le_normalizer_blockQ L hcL) z).mp hzQ
  have hz'1 : c * z * c⁻¹ ≠ 1 := fun h => hz1' (by simpa using h)
  have hz'z : z ≠ c * z * c⁻¹ := fun h => hz1' (hfpf z hzV h.symm)
  have hEV : V₂ ⊓ blockQ L = V₂ :=
    s151v_eq_of_card_four inf_le_left hr.2.1 ⟨hzV, hzQ⟩ ⟨hz'V, hz'Q⟩ hz1' hz'1 hz'z
  intro a ha
  have : a ∈ V₂ ⊓ blockQ L := by rw [hEV]; exact ha
  exact hU this

omit [Finite G] in
theorem s151v_conj_mem_sup {A B C : Subgroup G} {x : G} (hA : ∀ a ∈ A, x * a * x⁻¹ ∈ C)
    (hB : ∀ b ∈ B, x * b * x⁻¹ ∈ C) : ∀ y ∈ A ⊔ B, x * y * x⁻¹ ∈ C := by
  intro y hy
  rw [Subgroup.sup_eq_closure] at hy
  induction hy using Subgroup.closure_induction with
  | mem g hg =>
    rcases hg with hg | hg
    · exact hA g hg
    · exact hB g hg
  | one => simp
  | mul g h _ _ ihg ihh =>
    have : x * (g * h) * x⁻¹ = (x * g * x⁻¹) * (x * h * x⁻¹) := by group
    rw [this]
    exact Subgroup.mul_mem _ ihg ihh
  | inv g _ ih =>
    have : x * g⁻¹ * x⁻¹ = (x * g * x⁻¹)⁻¹ := by group
    rw [this]
    exact Subgroup.inv_mem _ ih

theorem notblock_core (hK : KnownFacts15122Types) (h1416 : StageLemma1416)
    {T Mc M Z₁ Z₂ V₁ V₂ L : Subgroup G} (h15 : Lemma1515Concl T Mc M)
    (hc : Ctx15124 T Mc M Z₁ Z₂ V₁ V₂ L) (hb : IsLnBlock L 3) (h4 : Ce15Four T Mc M)
    (hNV₁ : ∀ y ∈ Subgroup.normalizer (V₁ : Set G), y ∈ Subgroup.normalizer (L : Set G)) :
    False := by
  classical
  have hS := hc.ctx.setting
  have hq := hc.ctx.qtfe
  have hMf := hc.ctx.mf
  have h7n : ¬ Ce15Seven T Mc M := h4.not_seven
  have hLG : L ≤ g1_1516 Z₁ := le_of_mem_cComp hc.hL.comp
  have hperf : ⁅L, L⁆ = L := perfect_of_mem_cComp hc.hL.comp
  obtain ⟨e, β, hs⟩ := exists_lnStr hb
  have hsh : IsShort2 L := hb.1
  have h9 := s151v_not_nine_dvd_card hs
  obtain ⟨-, -, -, -, -, hCent⟩ := case15122Two_of_ln3 hK hb hc.h22
  obtain ⟨hY₀L, hV2Y₀, hnorm, c, hcY, hfpf⟩ := v2_data hK h15 hc hb
  obtain ⟨hZ₂V₂, -, hZ₂Q, hsyl, -⟩ := z2_facts hK h15 hc hb h7n
  have hV2U : V₂ ≤ blockU L := v2_le_blockU_four hK h15 hc hb h4
  have hr := hS.ranks_four h4
  have hcL : c ∈ L := hY₀L hcY
  have hZ := inf_blockZ_trivial (L := L) hcL hfpf
  have hS2 : (s1516 T Z₁).relIndex T = 2 := hS.index_two hc.small h7n
  have hswap := hS.swap_small hc.small h7n
  have hTNS : T ≤ Subgroup.normalizer (s1516 T Z₁ : Set G) :=
    (hS.extra_small hc.small).s_normal
  have hS2grp : IsPGroup 2 (s1516 T Z₁) := hc.h18.four.2.1
  have hST : s1516 T Z₁ ≤ T := s1516_le T Z₁
  obtain ⟨t₀, ht₀T, ht₀S⟩ : ∃ t ∈ T, t ∉ s1516 T Z₁ := by
    by_contra hall
    push Not at hall
    have : T ≤ s1516 T Z₁ := hall
    rw [Subgroup.relIndex_eq_one.mpr this] at hS2
    exact absurd hS2 (by norm_num)
  have hconj12 : ∀ g ∈ T, g ∉ s1516 T Z₁ → ∀ x, x ∈ V₁ ↔ g⁻¹ * x * g ∈ V₂ := by
    intro g hg hgS x
    rw [← hswap g hg hgS, mem_conjByElt]
  have hinv : ∀ g ∈ T, g ∉ s1516 T Z₁ → g⁻¹ ∈ T ∧ g⁻¹ ∉ s1516 T Z₁ := fun g hg hgS =>
    ⟨T.inv_mem hg, fun h => hgS (by simpa using (s1516 T Z₁).inv_mem h)⟩
  have hconj21 : ∀ g ∈ T, g ∉ s1516 T Z₁ → ∀ x, x ∈ V₂ ↔ g⁻¹ * x * g ∈ V₁ := by
    intro g hg hgS x
    have := hconj12 g⁻¹ (hinv g hg hgS).1 (hinv g hg hgS).2 (g⁻¹ * x * g)
    rw [inv_inv, show g * (g⁻¹ * x * g) * g⁻¹ = x by group] at this
    exact this.symm
  have hSV₁ : ∀ s ∈ s1516 T Z₁, ∀ x ∈ V₁, s * x * s⁻¹ ∈ V₁ := by
    intro s hs' x hx
    have h1 : t₀⁻¹ * x * t₀ ∈ V₂ := (hconj12 t₀ ht₀T ht₀S x).mp hx
    have hst : s * t₀ ∈ T := T.mul_mem (hST hs') ht₀T
    have hstS : s * t₀ ∉ s1516 T Z₁ := fun h => ht₀S (by simpa using (s1516 T Z₁).mul_mem ((s1516 T Z₁).inv_mem hs') h)
    refine (hconj12 (s * t₀) hst hstS _).mpr ?_
    have : (s * t₀)⁻¹ * (s * x * s⁻¹) * (s * t₀) = t₀⁻¹ * x * t₀ := by group
    rw [this]; exact h1
  have hSNV₁ : ∀ s ∈ s1516 T Z₁, s ∈ Subgroup.normalizer (V₁ : Set G) := fun s hs' =>
    s151v_mem_normalizer_of_conj (hSV₁ s hs') (fun x hx => by
      simpa using hSV₁ s⁻¹ ((s1516 T Z₁).inv_mem hs') x hx)
  have hSNL : ∀ s ∈ s1516 T Z₁, s ∈ Subgroup.normalizer (L : Set G) := fun s hs' =>
    hNV₁ s (hSNV₁ s hs')
  have hY₀Y : oPrimeResidualOf 3 (M ⊓ L) ≤ oPrimeResidualOf 3 (M ⊓ g1_1516 Z₁) :=
    oPrimeResidualOf_mono1516 3 (inf_le_inf_left M hLG)
  have hYN : oPrimeResidualOf 3 (M ⊓ L) ≤ Subgroup.normalizer (V₂ : Set G) :=
    hY₀Y.trans (hS.y_facts hc.small).1.2.2.2
  have hYC₁ : ∀ y ∈ oPrimeResidualOf 3 (M ⊓ L), ∀ x ∈ V₁, y * x = x * y := by
    have hYC := le_centralizer_of_commutator_eq_bot ((hS.y_facts hc.small).2 h7n)
    intro y hy x hx
    exact (Subgroup.mem_centralizer_iff.mp (hYC (hY₀Y hy)) x hx).symm
  have hconjN : ∀ g ∈ T, g ∉ s1516 T Z₁ → ∀ y ∈ Subgroup.normalizer (V₂ : Set G),
      g * y * g⁻¹ ∈ Subgroup.normalizer (V₁ : Set G) := by
    intro g hg hgS y hy
    rw [Subgroup.mem_normalizer_iff]
    intro v
    rw [hconj12 g hg hgS v, hconj12 g hg hgS ((g * y * g⁻¹) * v * (g * y * g⁻¹)⁻¹)]
    have : g⁻¹ * ((g * y * g⁻¹) * v * (g * y * g⁻¹)⁻¹) * g = y * (g⁻¹ * v * g) * y⁻¹ := by group
    rw [this]
    exact Subgroup.mem_normalizer_iff.mp hy (g⁻¹ * v * g)
  have hconjC : ∀ g ∈ T, g ∉ s1516 T Z₁ → ∀ y ∈ oPrimeResidualOf 3 (M ⊓ L), ∀ a ∈ V₂,
      (g * y * g⁻¹) * a = a * (g * y * g⁻¹) := by
    intro g hg hgS y hy a ha
    have hx : g⁻¹ * a * g ∈ V₁ := (hconj21 g hg hgS a).mp ha
    have h := hYC₁ y hy _ hx
    calc (g * y * g⁻¹) * a = g * (y * (g⁻¹ * a * g)) * g⁻¹ := by group
      _ = g * ((g⁻¹ * a * g) * y) * g⁻¹ := by rw [h]
      _ = a * (g * y * g⁻¹) := by group
  obtain ⟨a, haV, b, hbV, ha1, hb1, hab⟩ : ∃ a ∈ V₂, ∃ b ∈ V₂, a ≠ 1 ∧ b ≠ 1 ∧ a ≠ b :=
    s151v_exists_two_ne_one (A := V₂) (by rw [hr.2.1]; norm_num)
  have haU : a ∈ blockU L := hV2U haV
  have hbU : b ∈ blockU L := hV2U hbV
  have hβa : β ⟨a, haU⟩ ≠ 1 := s151v_beta_ne_one hs haU (fun hz => ha1 (hZ a haV hz))
  have hβb : β ⟨b, hbU⟩ ≠ 1 := s151v_beta_ne_one hs hbU (fun hz => hb1 (hZ b hbV hz))
  have hβab : β ⟨a, haU⟩ ≠ β ⟨b, hbU⟩ := by
    intro h
    have h1 := s151v_beta_inj hs haU hbU h
    have h2 : a⁻¹ * b ∈ V₂ := V₂.mul_mem (V₂.inv_mem haV) hbV
    exact hab (inv_mul_eq_one.mp (hZ _ h2 h1))
  have hy3 : ∀ y ∈ L, ∀ k : ℕ, orderOf y = 3 ^ k → y ^ 3 = 1 := by
    intro y hyL k hk
    have hdvd : orderOf y ∣ Nat.card ↥L := by
      have := orderOf_dvd_natCard (⟨y, hyL⟩ : ↥L)
      rwa [← Subgroup.orderOf_coe] at this
    rcases k with _ | _ | k
    · have : y = 1 := orderOf_eq_one_iff.mp (by simpa using hk)
      rw [this]; simp
    · have h3 : orderOf y = 3 := by simpa using hk
      rw [← h3]; exact pow_orderOf_eq_one y
    · exfalso
      apply h9
      have : 9 ∣ orderOf y := by
        rw [hk]; exact ⟨3 ^ k, by ring⟩
      exact this.trans hdvd
  have hgen : ∀ g ∈ T, g ∉ s1516 T Z₁ → ∀ y ∈ M ⊓ L, ∀ k : ℕ, orderOf y = 3 ^ k →
      ∀ u ∈ blockU L, (g * y * g⁻¹) * u = u * (g * y * g⁻¹) := by
    intro g hg hgS y hyML k hk u hu
    have hyY : y ∈ oPrimeResidualOf 3 (M ⊓ L) := Subgroup.subset_closure ⟨hyML, k, hk⟩
    have hxN : g * y * g⁻¹ ∈ Subgroup.normalizer (L : Set G) :=
      hNV₁ _ (hconjN g hg hgS y (hYN hyY))
    have hx3 : (g * y * g⁻¹) ^ 3 = 1 := by
      rw [conj_pow, hy3 y hyML.2 k hk]; group
    have hxa : (g * y * g⁻¹) * a * (g * y * g⁻¹)⁻¹ = a := by
      rw [hconjC g hg hgS y hyY a haV]; group
    have hxb : (g * y * g⁻¹) * b * (g * y * g⁻¹)⁻¹ = b := by
      rw [hconjC g hg hgS y hyY b hbV]; group
    have := local_x_centralizes_U hs hsh hperf hxN hx3 haU hbU hxa hxb hβa hβb hβab u hu
    calc (g * y * g⁻¹) * u = (g * y * g⁻¹) * u * (g * y * g⁻¹)⁻¹ * (g * y * g⁻¹) := by group
      _ = u * (g * y * g⁻¹) := by rw [this]
  have hclos : ∀ g ∈ T, g ∉ s1516 T Z₁ → ∀ y ∈ oPrimeResidualOf 3 (M ⊓ L), ∀ u ∈ blockU L,
      (g * y * g⁻¹) * u = u * (g * y * g⁻¹) := by
    intro g hg hgS y hy u hu
    unfold oPrimeResidualOf at hy
    induction hy using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨hxML, k, hk⟩ := hx
      exact hgen g hg hgS x hxML k hk u hu
    | one => simp
    | mul x z _ _ ihx ihz =>
      have h1 : g * (x * z) * g⁻¹ = (g * x * g⁻¹) * (g * z * g⁻¹) := by group
      rw [h1, mul_assoc, ihz, ← mul_assoc, ihx, mul_assoc]
    | inv x _ ih =>
      have h1 : g * x⁻¹ * g⁻¹ = (g * x * g⁻¹)⁻¹ := by group
      rw [h1]
      calc (g * x * g⁻¹)⁻¹ * u = (g * x * g⁻¹)⁻¹ * (u * (g * x * g⁻¹)) * (g * x * g⁻¹)⁻¹ := by group
        _ = (g * x * g⁻¹)⁻¹ * ((g * x * g⁻¹) * u) * (g * x * g⁻¹)⁻¹ := by rw [← ih]
        _ = u * (g * x * g⁻¹)⁻¹ := by group
  have hQB : blockQ L ≤ s1516 T Z₁ ⊓ L := pCoreOf_le_of_isSylowTwoOf hsyl
  have hU_S : blockU L ≤ s1516 T Z₁ :=
    (s151v_blockU_le_blockQ hsh).trans (hQB.trans inf_le_left)
  have hUL : ∀ h ∈ T, h ∉ s1516 T Z₁ → ∀ u ∈ blockU L, ∀ ℓ ∈ L,
      (h * u * h⁻¹) * ℓ = ℓ * (h * u * h⁻¹) := by
    intro h hh hhS u hu ℓ hℓ
    have hinv' := hinv h hh hhS
    have hu'S : h * u * h⁻¹ ∈ s1516 T Z₁ :=
      (Subgroup.mem_normalizer_iff.mp (hTNS hh) u).mp (hU_S hu)
    have hu'C : h * u * h⁻¹ ∈ Subgroup.centralizer (oPrimeResidualOf 3 (M ⊓ L) : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      have h1 := hclos h⁻¹ hinv'.1 hinv'.2 y hy u hu
      rw [inv_inv] at h1
      calc y * (h * u * h⁻¹) = h * ((h⁻¹ * y * h) * u) * h⁻¹ := by group
        _ = h * (u * (h⁻¹ * y * h)) * h⁻¹ := by rw [h1]
        _ = (h * u * h⁻¹) * y := by group
    have hw : h * u * h⁻¹ ∈ s1516 T Z₁ ⊓ Subgroup.centralizer (L : Set G) := by
      rw [← hCent]; exact ⟨hu'S, hu'C⟩
    exact (Subgroup.mem_centralizer_iff.mp hw.2 ℓ hℓ).symm
  have hIdx : ((s1516 T Z₁).subgroupOf T).index = 2 := hS2
  have ht₀sq : t₀ * t₀ ∈ s1516 T Z₁ := Subgroup.mul_self_mem_of_index_two hIdx ⟨t₀, ht₀T⟩
  have hquot : ∀ g ∈ T, g ∉ s1516 T Z₁ → g * t₀⁻¹ ∈ s1516 T Z₁ := by
    intro g hg hgS
    refine (Subgroup.mul_mem_iff_of_index_two hIdx (a := (⟨g, hg⟩ : ↥T))
      (b := (⟨t₀, ht₀T⟩ : ↥T)⁻¹)).mpr ⟨fun h => absurd h hgS, fun h => ?_⟩
    exact absurd (by simpa using (s1516 T Z₁).inv_mem h) ht₀S
  let U' : Subgroup G := conjByElt t₀ (blockU L)
  have hU'mem : ∀ x, x ∈ U' ↔ t₀⁻¹ * x * t₀ ∈ blockU L := fun x => mem_conjByElt
  have hU'S : U' ≤ s1516 T Z₁ := by
    intro x hx
    have h1 : t₀⁻¹ * x * t₀ ∈ blockU L := (hU'mem x).mp hx
    have h2 : t₀ * (t₀⁻¹ * x * t₀) * t₀⁻¹ ∈ s1516 T Z₁ :=
      (Subgroup.mem_normalizer_iff.mp (hTNS ht₀T) _).mp (hU_S h1)
    rwa [show t₀ * (t₀⁻¹ * x * t₀) * t₀⁻¹ = x by group] at h2
  have hU'C : ∀ x ∈ U', ∀ ℓ ∈ L, x * ℓ = ℓ * x := by
    intro x hx ℓ hℓ
    have h1 : t₀⁻¹ * x * t₀ ∈ blockU L := (hU'mem x).mp hx
    have h2 := hUL t₀ ht₀T ht₀S _ h1 ℓ hℓ
    rwa [show t₀ * (t₀⁻¹ * x * t₀) * t₀⁻¹ = x by group] at h2
  let W : Subgroup G := blockU L ⊔ U'
  have hWS : W ≤ s1516 T Z₁ := sup_le hU_S hU'S
  have hW2 : IsPGroup 2 W := hS2grp.to_le hWS
  have hUne : blockU L ≠ ⊥ := by
    intro h
    have := hsh.2.2.2.2.1
    rw [h] at this
    exact absurd this not_lt_bot
  have hWne : W ≠ ⊥ := fun h => hUne (le_bot_iff.mp (le_sup_left.trans h.le))
  have hLW : L ≤ Subgroup.normalizer (W : Set G) := by
    intro ℓ hℓ
    have hU'N : ℓ ∈ Subgroup.normalizer (U' : Set G) := by
      refine s151v_mem_normalizer_of_conj (fun x hx => ?_) (fun x hx => ?_)
      · have : ℓ * x * ℓ⁻¹ = x := by
          calc ℓ * x * ℓ⁻¹ = x * ℓ * ℓ⁻¹ := by rw [hU'C x hx ℓ hℓ]
            _ = x := by group
        rwa [this]
      · have : ℓ⁻¹ * x * ℓ = x := by
          calc ℓ⁻¹ * x * ℓ = ℓ⁻¹ * (x * ℓ) := by group
            _ = ℓ⁻¹ * (ℓ * x) := by rw [hU'C x hx ℓ hℓ]
            _ = x := by group
        rwa [this]
    exact s151v_mem_normalizer_sup (s151v_L_le_normalizer_blockU L hℓ) hU'N
  have hSU' : ∀ s ∈ s1516 T Z₁, ∀ x ∈ U', s * x * s⁻¹ ∈ U' := by
    intro s hs' x hx
    rw [hU'mem] at hx ⊢
    have hs'' : t₀⁻¹ * s * t₀ ∈ s1516 T Z₁ := by
      have := (Subgroup.mem_normalizer_iff.mp (hTNS (T.inv_mem ht₀T)) s).mp hs'
      simpa using this
    have hs''N : t₀⁻¹ * s * t₀ ∈ Subgroup.normalizer (blockU L : Set G) :=
      s151v_normalizer_le_normalizer_blockU L (hSNL _ hs'')
    have h1 := (Subgroup.mem_normalizer_iff.mp hs''N _).mp hx
    have e : t₀⁻¹ * (s * x * s⁻¹) * t₀ =
        (t₀⁻¹ * s * t₀) * (t₀⁻¹ * x * t₀) * (t₀⁻¹ * s * t₀)⁻¹ := by group
    rw [e]; exact h1
  have hSW : ∀ s ∈ s1516 T Z₁, s ∈ Subgroup.normalizer (W : Set G) := by
    intro s hs'
    have hsU : s ∈ Subgroup.normalizer (blockU L : Set G) :=
      s151v_normalizer_le_normalizer_blockU L (hSNL s hs')
    have hsU' : s ∈ Subgroup.normalizer (U' : Set G) :=
      s151v_mem_normalizer_of_conj (hSU' s hs') (fun x hx => by
        simpa using hSU' s⁻¹ ((s1516 T Z₁).inv_mem hs') x hx)
    exact s151v_mem_normalizer_sup hsU hsU'
  have ht₀W : t₀ ∈ Subgroup.normalizer (W : Set G) := by
    have hsqN : t₀ * t₀ ∈ Subgroup.normalizer (blockU L : Set G) :=
      s151v_normalizer_le_normalizer_blockU L (hSNL _ ht₀sq)
    refine s151v_mem_normalizer_of_conj ?_ ?_
    · intro y hy
      refine s151v_conj_mem_sup (A := blockU L) (B := U') (C := W) (x := t₀) ?_ ?_ y hy
      · intro u hu
        have : t₀⁻¹ * (t₀ * u * t₀⁻¹) * t₀ = u := by group
        exact Subgroup.mem_sup_right ((hU'mem _).mpr (by rw [this]; exact hu))
      · intro x hx
        have h1 : t₀⁻¹ * x * t₀ ∈ blockU L := (hU'mem x).mp hx
        have h2 := (Subgroup.mem_normalizer_iff.mp hsqN _).mp h1
        have e : (t₀ * t₀) * (t₀⁻¹ * x * t₀) * (t₀ * t₀)⁻¹ = t₀ * x * t₀⁻¹ := by group
        rw [e] at h2
        exact Subgroup.mem_sup_left h2
    · intro y hy
      have key := s151v_conj_mem_sup (A := blockU L) (B := U') (C := W) (x := t₀⁻¹) (fun u hu => by
          have h1 : t₀ * u * t₀⁻¹ ∈ U' := by
            refine (hU'mem _).mpr ?_
            have : t₀⁻¹ * (t₀ * u * t₀⁻¹) * t₀ = u := by group
            rw [this]; exact hu
          have hsq' : (t₀ * t₀)⁻¹ ∈ s1516 T Z₁ := (s1516 T Z₁).inv_mem ht₀sq
          have h2 := hSU' _ hsq' _ h1
          have e : (t₀ * t₀)⁻¹ * (t₀ * u * t₀⁻¹) * ((t₀ * t₀)⁻¹)⁻¹ = t₀⁻¹ * u * t₀⁻¹⁻¹ := by group
          rw [e] at h2
          exact Subgroup.mem_sup_right h2) (fun x hx => by
          have h1 : t₀⁻¹ * x * t₀ ∈ blockU L := (hU'mem x).mp hx
          have e : t₀⁻¹ * x * t₀⁻¹⁻¹ = t₀⁻¹ * x * t₀ := by group
          rw [e]; exact Subgroup.mem_sup_left h1) y hy
      simpa using key
  have hTW : T ≤ Subgroup.normalizer (W : Set G) := by
    intro g hg
    by_cases hgS : g ∈ s1516 T Z₁
    · exact hSW g hgS
    · have h1 : g * t₀⁻¹ ∈ s1516 T Z₁ := hquot g hg hgS
      have : g = (g * t₀⁻¹) * t₀ := by group
      rw [this]
      exact Subgroup.mul_mem _ (hSW _ h1) ht₀W
  have hpc : pCoreOf 2 (Subgroup.normalizer (W : Set G)) ≠ ⊥ := by
    intro h
    have := CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
      (Subgroup.le_normalizer : W ≤ Subgroup.normalizer (W : Set G)) le_rfl hW2
    rw [h] at this
    exact hWne (le_bot_iff.mp this)
  have h14 := (h1416 G T Mc hq).2.2.2 _ (And.intro hTW hpc)
  have hLper : L ≤ perfectCore (Subgroup.normalizer (W : Set G)) :=
    le_perfectCore_of_perfect hLW hperf
  exact hc.hL.not_le (fun x hx => ⟨hLG hx, h14.2 (h14.1 (hLper hx))⟩)

end CFSG.Quasithin
