module

public import CFSG.Quasithin.Background.C48Asm

public section

namespace CFSG.Quasithin.C48

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open scoped commutatorElement

variable {G : Type} [Group G]

theorem eq_right_of_commutator_eq_bot {V V₁ V₂ L : Subgroup G} (hV : V = V₁ ⊔ V₂)
    (hab : ∀ x ∈ V, ∀ y ∈ V, x * y = y * x) (hL2 : L ≤ Subgroup.normalizer (V₂ : Set G))
    (h1 : ⁅V₁, L⁆ = ⊥) (hVL : ⁅V, L⁆ = V) : V = V₂ := by
  have hV₁ : V₁ ≤ V := hV ▸ le_sup_left
  have hV₂ : V₂ ≤ V := hV ▸ le_sup_right
  let S : Subgroup G :=
    { carrier := {v | v ∈ V ∧ ∀ l ∈ L, ⁅v, l⁆ ∈ V₂}
      one_mem' := ⟨V.one_mem, fun l _ => by simp⟩
      mul_mem' := by
        rintro v w ⟨hv, hv'⟩ ⟨hw, hw'⟩
        refine ⟨V.mul_mem hv hw, fun l hl => ?_⟩
        have e : ⁅v * w, l⁆ = v * ⁅w, l⁆ * v⁻¹ * ⁅v, l⁆ := by
          simp only [commutatorElement_def]
          group
        have hc : v * ⁅w, l⁆ * v⁻¹ = ⁅w, l⁆ := by
          rw [hab v hv _ (hV₂ (hw' l hl)), mul_inv_cancel_right]
        rw [e, hc]
        exact V₂.mul_mem (hw' l hl) (hv' l hl)
      inv_mem' := by
        rintro v ⟨hv, hv'⟩
        refine ⟨V.inv_mem hv, fun l hl => ?_⟩
        have e : ⁅v⁻¹, l⁆ = v⁻¹ * ⁅v, l⁆⁻¹ * v := by
          simp only [commutatorElement_def]
          group
        have hc : v⁻¹ * ⁅v, l⁆⁻¹ * v = ⁅v, l⁆⁻¹ := by
          rw [hab _ (V.inv_mem hv) _ (V.inv_mem (hV₂ (hv' l hl))), mul_assoc, inv_mul_cancel,
            mul_one]
        rw [e, hc]
        exact V₂.inv_mem (hv' l hl) }
  have hS : V₁ ⊔ V₂ ≤ S := by
    refine sup_le (fun v hv => ⟨hV₁ hv, fun l hl => ?_⟩) (fun v hv => ⟨hV₂ hv, fun l hl => ?_⟩)
    · have : ⁅v, l⁆ ∈ ⁅V₁, L⁆ := Subgroup.commutator_mem_commutator hv hl
      rw [h1, Subgroup.mem_bot] at this
      rw [this]
      exact V₂.one_mem
    · have hl' : l * v⁻¹ * l⁻¹ ∈ V₂ :=
        (Subgroup.mem_normalizer_iff.mp (hL2 hl) _).mp (V₂.inv_mem hv)
      have e : ⁅v, l⁆ = v * (l * v⁻¹ * l⁻¹) := by
        simp only [commutatorElement_def]
        group
      rw [e]
      exact V₂.mul_mem hv hl'
  refine le_antisymm ?_ hV₂
  rw [← hVL, Subgroup.commutator_le]
  intro v hv l hl
  rw [hV] at hv
  exact (hS hv).2 l hl

variable [Finite G] {H R M L V K : Subgroup G}

theorem isNaturalSection_of_isStabilizedLine (h : HypC28 H R M L V) (hL0 : L = conjClosure L M)
    (hLK : L ≤ K) {n : ℕ} {F : Type} [Field F] [Fintype F] (hF : Fintype.card F = 2 ^ n)
    (hpsl : IsPSL 2 2 n (ModO2 L)) {V₁ : Subgroup G} (hV₁ : V₁ ≤ V)
    (hline : IsStabilizedLineOfNatural F R M K V₁) (hnt : ⁅V₁, L⁆ ≠ ⊥) :
    IsNaturalSection (L ⊔ R) V₁ (V₁ ⊓ Subgroup.centralizer (L : Set G))
      (R.subgroupOf (L ⊔ R)) (StatedSL 2 F) := by
  obtain ⟨W, -, α, β, ⟨-, -, -, hβs, hβker, hβeq⟩, hfl, hMK⟩ := hline
  have hLM : L ≤ M := le_of_mem_cComp h.comp
  have hLV : L ≤ Subgroup.normalizer (V₁ : Set G) := by
    intro x hx
    have hx' : x ∈ M ⊓ K := ⟨hLM hx, hLK hx⟩
    rw [hMK] at hx'
    exact hx'.2
  have hRV : R ≤ Subgroup.centralizer (V₁ : Set G) :=
    (le_centralizer_V h).trans (Subgroup.centralizer_le hV₁)
  have hO : pCoreOf 2 L ≤ Subgroup.centralizer (V₁ : Set G) := by
    have h0 := pCoreOf_conjClosure_le h
    rw [← hL0] at h0
    exact h0.trans hRV
  have hNS := isNaturalSection_of_line α β hβs hβker hβeq hfl hLK hLV
    (perfect_of_mem_cComp h.comp) (by rw [Nat.card_eq_fintype_card, hF]) hpsl hO
    (fun hle => hnt (le_bot_iff.mp hle))
  have hZ := inf_centralizer_eq_bot_of_isNaturalSection hNS
  have hN := subgroupOf_conjClosure_eq h
  rw [← hL0] at hN
  rw [← hN] at hNS
  have hLR : L ≤ Subgroup.normalizer (R : Set G) := hL0 ▸ (c2_9_two h).1
  rw [hZ]
  exact isNaturalSection_sup hNS hLR hRV

omit [Finite G] in
open scoped Pointwise in
theorem isNaturalSection_of_sup {A V Z : Subgroup G} {N : Subgroup ↥A} {ι : Type} [Fintype ι]
    [DecidableEq ι] {F : Type} [Field F] {Γ : Subgroup (Matrix.GeneralLinearGroup ι F)}
    (h : IsNaturalSection A (V ⊔ Z) Z N Γ) (hAV : A ≤ Subgroup.normalizer (V : Set G))
    (hVZ : V ≤ Subgroup.normalizer (Z : Set G)) :
    IsNaturalSection A V (V ⊓ Z) N Γ := by
  obtain ⟨-, α, hα, hker, β, hβ, hβker, hβeq⟩ := h
  refine ⟨hAV, α, hα, hker, β.comp (Subgroup.inclusion le_sup_left), ?_, ?_, ?_⟩
  · intro y
    obtain ⟨x, rfl⟩ := hβ y
    have hx : (x : G) ∈ ((V : Set G) * (Z : Set G)) := by
      rw [← Subgroup.coe_mul_of_left_le_normalizer_right V Z hVZ]
      exact x.2
    obtain ⟨v, hv, z, hz, hvz⟩ := hx
    refine ⟨⟨v, hv⟩, ?_⟩
    have hz1 : β ⟨z, Subgroup.mem_sup_right hz⟩ = 1 := by
      rw [← MonoidHom.mem_ker, hβker]
      exact hz
    have e : x = ⟨v, Subgroup.mem_sup_left hv⟩ * ⟨z, Subgroup.mem_sup_right hz⟩ :=
      Subtype.ext hvz.symm
    rw [e, map_mul, hz1, mul_one]
    rfl
  · ext v
    have := congrArg (fun S : Subgroup ↥(V ⊔ Z) =>
      Subgroup.inclusion (le_sup_left : V ≤ V ⊔ Z) v ∈ S) hβker
    simp only [MonoidHom.mem_ker, eq_iff_iff, Subgroup.mem_subgroupOf] at this
    simp only [MonoidHom.mem_ker, MonoidHom.coe_comp, Function.comp_apply,
      Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    rw [this]
    exact ⟨fun h => ⟨v.2, h⟩, fun h => h.2⟩
  · intro a u v huv
    exact hβeq a _ _ huv

theorem c48Case1_of_c41Case2 (h : HypC28 H R M L V) (hL0 : L = conjClosure L M) (hLK : L ≤ K)
    (h2 : C41Case2 H R M L V K) : C48Case1 H R M L V K := by
  obtain ⟨-, F, _, _, α, β, hF, ⟨-, -, hβs, hβker, hβeq⟩, hfl, -, hMK, hpsl0⟩ := h2
  have hpsl : IsPSL 2 2 2 (ModO2 L) := by
    rw [hL0]
    exact hpsl0
  have hLM : L ≤ M := le_of_mem_cComp h.comp
  have hLV : L ≤ Subgroup.normalizer (V : Set G) := by
    intro x hx
    have hx' : x ∈ M ⊓ K := ⟨hLM hx, hLK hx⟩
    rw [hMK] at hx'
    exact hx'.2
  have hVL : ⁅V, L⁆ = V := by
    have h0 := h.V_comm
    rwa [← hL0] at h0
  have hVK : V ≤ K := by
    have h0 := h.V_le
    rw [← hL0] at h0
    exact h0.trans hLK
  have hLZ : L ≤ Subgroup.centralizer (blockZ K : Set G) := fun l hl =>
    Subgroup.mem_centralizer_iff.mpr fun z hz =>
      (Subgroup.mem_centralizer_iff.mp hz.2 l (hLK hl)).symm
  have hsupN : ∀ {A B : Subgroup G} {x : G}, x ∈ Subgroup.normalizer (A : Set G) →
      x ∈ Subgroup.normalizer (B : Set G) →
        x ∈ Subgroup.normalizer ((A ⊔ B : Subgroup G) : Set G) := by
    intro A B x hA hB
    rw [Subgroup.mem_normalizer_iff_map_conj_eq] at hA hB ⊢
    rw [Subgroup.map_sup, hA, hB]
  have hLVZ : L ≤ Subgroup.normalizer ((V ⊔ blockZ K : Subgroup G) : Set G) := fun l hl =>
    hsupN (hLV hl) (le_normalizer_of_le_centralizer hLZ hl)
  have hRV := le_centralizer_V h
  have hO : pCoreOf 2 L ≤ Subgroup.centralizer ((V ⊔ blockZ K : Subgroup G) : Set G) := by
    have h0 := pCoreOf_conjClosure_le h
    rw [← hL0] at h0
    rw [Subgroup.le_centralizer_iff]
    refine sup_le ?_ ?_
    · rw [← Subgroup.le_centralizer_iff]
      exact h0.trans hRV
    · rw [← Subgroup.le_centralizer_iff]
      exact (CFSG.LieType.BorelTits.pCoreOf_le 2 L).trans hLZ
  have hnt : ¬ ⁅V ⊔ blockZ K, L⁆ ≤ blockZ K := by
    intro hle
    have hVZ : V ≤ blockZ K := by
      rw [← hVL]
      exact (Subgroup.commutator_mono le_sup_left le_rfl).trans hle
    apply h.V_ne
    rw [← hVL, eq_bot_iff]
    calc ⁅V, L⁆ ≤ ⁅blockZ K, L⁆ := Subgroup.commutator_mono hVZ le_rfl
      _ = ⊥ := by
        rw [Subgroup.commutator_comm]
        exact Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hLZ
  have hNS := isNaturalSection_of_line α β hβs hβker hβeq hfl hLK hLVZ
    (perfect_of_mem_cComp h.comp) (n := 2) (by rw [Nat.card_eq_fintype_card, hF]; norm_num)
    hpsl hO hnt
  have hVZn : V ≤ Subgroup.normalizer (blockZ K : Set G) :=
    le_normalizer_of_le_centralizer fun x hx => Subgroup.mem_centralizer_iff.mpr fun z hz =>
      (Subgroup.mem_centralizer_iff.mp hz.2 x (hVK hx)).symm
  have hNS' := isNaturalSection_of_sup hNS hLV hVZn
  have hZL : blockZ K ≤ Subgroup.centralizer (L : Set G) := Subgroup.le_centralizer_iff.mp hLZ
  have hZeq : V ⊓ blockZ K = V ⊓ Subgroup.centralizer (L : Set G) :=
    le_antisymm (inf_le_inf_left V hZL) (inf_centralizer_le_of_isNaturalSection hNS')
  rw [hZeq] at hNS'
  have hN := subgroupOf_conjClosure_eq h
  rw [← hL0] at hN
  rw [← hN] at hNS'
  have hLR : L ≤ Subgroup.normalizer (R : Set G) := hL0 ▸ (c2_9_two h).1
  exact ⟨2, hpsl, Or.inl ⟨F, inferInstance, inferInstance, by rw [hF]; norm_num,
    isNaturalSection_sup hNS' hLR hRV⟩⟩

theorem c48Case1_of_c41Case3 (h : HypC28 H R M L V) (hL0 : L = conjClosure L M) (hLK : L ≤ K)
    (h3 : C41Case3 H R M L V K) : C48Case1 H R M L V K := by
  obtain ⟨n, F, _, _, hn, hF, -, -, -, -, hpsl0, hcase⟩ := h3
  have hpsl : IsPSL 2 2 n (ModO2 L) := by
    rw [hL0]
    exact hpsl0
  have hVL : ⁅V, L⁆ = V := by
    have h0 := h.V_comm
    rwa [← hL0] at h0
  have hVne : ⁅V, L⁆ ≠ ⊥ := by
    rw [hVL]
    exact h.V_ne
  rcases hcase with hline | ⟨h134, V₁, V₂, hl1, hl2, hV12⟩
  · exact ⟨n, hpsl, Or.inl ⟨F, inferInstance, inferInstance, hF,
      isNaturalSection_of_isStabilizedLine h hL0 hLK hF hpsl le_rfl hline hVne⟩⟩
  have hab : ∀ x ∈ V, ∀ y ∈ V, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (h.V_elem.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hLM : L ≤ M := le_of_mem_cComp h.comp
  have hLn : ∀ {W : Subgroup G}, IsStabilizedLineOfNatural F R M K W →
      L ≤ Subgroup.normalizer (W : Set G) := by
    intro W hW x hx
    obtain ⟨-, -, -, -, -, -, hMK⟩ := hW
    have hx' : x ∈ M ⊓ K := ⟨hLM hx, hLK hx⟩
    rw [hMK] at hx'
    exact hx'.2
  have hV₁ : V₁ ≤ V := hV12 ▸ le_sup_left
  have hV₂ : V₂ ≤ V := hV12 ▸ le_sup_right
  by_cases h1 : ⁅V₁, L⁆ = ⊥
  · have hVe := eq_right_of_commutator_eq_bot hV12 hab (hLn hl2) h1 hVL
    refine ⟨n, hpsl, Or.inl ⟨F, inferInstance, inferInstance, hF, ?_⟩⟩
    have hl2' := hl2
    rw [← hVe] at hl2'
    exact isNaturalSection_of_isStabilizedLine h hL0 hLK hF hpsl le_rfl hl2' hVne
  by_cases h2 : ⁅V₂, L⁆ = ⊥
  · have hVe := eq_right_of_commutator_eq_bot (sup_comm V₁ V₂ ▸ hV12) hab (hLn hl1) h2 hVL
    refine ⟨n, hpsl, Or.inl ⟨F, inferInstance, inferInstance, hF, ?_⟩⟩
    have hl1' := hl1
    rw [← hVe] at hl1'
    exact isNaturalSection_of_isStabilizedLine h hL0 hLK hF hpsl le_rfl hl1' hVne
  exact ⟨n, hpsl, Or.inr (Or.inr ⟨hn, h134, ⟨n, F, inferInstance, inferInstance, V₁, hn, hF, hl1⟩,
    F, inferInstance, inferInstance, V₁, V₂, hF, hV12,
    isNaturalSection_of_isStabilizedLine h hL0 hLK hF hpsl hV₁ hl1 h1,
    isNaturalSection_of_isStabilizedLine h hL0 hLK hF hpsl hV₂ hl2 h2⟩)⟩

theorem c48C41LineStep : C48C41LineStep G := by
  intro H R M L V K h _ _ _ _ hC41 hcase
  obtain ⟨hL0, hLK0, hK0, -⟩ := hC41
  have hLK : L ≤ K := by
    have h0 := hLK0
    rw [hK0, ← hL0] at h0
    exact h0
  rcases hcase with h2 | h3
  · exact c48Case1_of_c41Case2 h hL0 hLK h2
  · exact c48Case1_of_c41Case3 h hL0 hLK h3

end CFSG.Quasithin.C48
