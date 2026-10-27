module

public import CFSG.Quasithin.Recognition.L34AmalgamIsoGlue
public import CFSG.Quasithin.Recognition.L34AmalgamParabolic
public import CFSG.Quasithin.Recognition.L34Amalgam
public import CFSG.Quasithin.Recognition.L34AmalgamIsoConj

public section

namespace CFSG.Quasithin.L34Amalgam

open MulAction CFSG.ComponentClassification.WittDesign CFSG.Quasithin.Asc94

theorem exists_iso_P1_of_parabolic
    {L : Type*} [Group L] [Finite L]
    {K E : Subgroup L} {a b : L} (h : IsParabolic K E a b) :
    ∃ ψ : ↥m22TwoStab ≃* ↥K, ∀ g : ↥m22TwoStab, ((ψ g : ↥K) : L) ∈ E ↔ (g : M22) ∈ barA1 := by
  have := h.normal_subgroupOf
  obtain ⟨ψ, hψ⟩ := exists_mulEquiv_P1_iff (X := ↥K) (E := E.subgroupOf K)
    (C := (Subgroup.closure {a, b}).subgroupOf K) (a := ⟨a, h.mem_a⟩) (b := ⟨b, h.mem_b⟩)
    (fun x hx => Subtype.ext (h.mul_self _ hx))
    (by rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe h.le).toEquiv, h.card_E])
    (by
      refine (Subgroup.eq_bot_iff_forall _).mpr fun x ⟨hxE, hxC⟩ => Subtype.ext ?_
      have hx : (x : L) ∈ E ⊓ Subgroup.closure {a, b} := ⟨hxE, hxC⟩
      rw [h.inf, Subgroup.mem_bot] at hx
      exact hx)
    (by rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe h.closure_le).toEquiv, h.card_C])
    h.card h.closure_subgroupOf (Subtype.ext h.ha)
    (Subtype.ext (by rw [Subgroup.coe_pow]; exact h.hb))
    (Subtype.ext (by rw [Subgroup.coe_pow, Subgroup.coe_mul]; exact h.hab))
    (fun e he hc => Subtype.ext (h.fpf _ he (congrArg Subtype.val hc)))
  exact ⟨ψ, fun g => hψ g⟩

theorem exists_iso_P2_of_parabolic
    {L : Type*} [Group L] [Finite L]
    {K E : Subgroup L} {a b : L} (h : IsParabolic K E a b) :
    ∃ ψ : ↥m22PtHexStab ≃* ↥K, ∀ g : ↥m22PtHexStab, ((ψ g : ↥K) : L) ∈ E ↔ (g : M22) ∈ barA2 := by
  have := h.normal_subgroupOf
  obtain ⟨ψ, hψ⟩ := exists_mulEquiv_P2_iff (X := ↥K) (E := E.subgroupOf K)
    (C := (Subgroup.closure {a, b}).subgroupOf K) (a := ⟨a, h.mem_a⟩) (b := ⟨b, h.mem_b⟩)
    (fun x hx => Subtype.ext (h.mul_self _ hx))
    (by rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe h.le).toEquiv, h.card_E])
    (by
      refine (Subgroup.eq_bot_iff_forall _).mpr fun x ⟨hxE, hxC⟩ => Subtype.ext ?_
      have hx : (x : L) ∈ E ⊓ Subgroup.closure {a, b} := ⟨hxE, hxC⟩
      rw [h.inf, Subgroup.mem_bot] at hx
      exact hx)
    (by rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe h.closure_le).toEquiv, h.card_C])
    h.card h.closure_subgroupOf (Subtype.ext h.ha)
    (Subtype.ext (by rw [Subgroup.coe_pow]; exact h.hb))
    (Subtype.ext (by rw [Subgroup.coe_pow, Subgroup.coe_mul]; exact h.hab))
    (fun e he hc => Subtype.ext (h.fpf _ he (congrArg Subtype.val hc)))
  exact ⟨ψ, fun g => hψ g⟩

theorem card_comap_subgroupOf {X L : Type*} [Group X] [Group L] {K S : Subgroup L}
    (ψ : X ≃* ↥K) : Nat.card ((S.subgroupOf K).comap ψ.toMonoidHom) = Nat.card ↥(K ⊓ S) := by
  rw [← Subgroup.card_map_of_injective (f := ψ.toMonoidHom) ψ.injective,
    Subgroup.map_comap_eq_self_of_surjective (f := ψ.toMonoidHom) ψ.surjective,
    ← Subgroup.inf_subgroupOf_left,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv]

theorem exists_iso_P1_normalized
    {L : Type*} [Group L] [Finite L]
    {K₁ K₂ E₁ E₂ : Subgroup L} {a b : L} (h : IsParabolic K₁ E₁ a b) (hE₂ : E₂ ≤ K₁ ⊓ K₂)
    (hE₂n : ∀ x ∈ K₂, ∀ e ∈ E₂, x * e * x⁻¹ ∈ E₂) (hE₂2 : ∀ e ∈ E₂, e * e = 1)
    (hE₂c : Nat.card E₂ = 16) (hne : E₁ ≠ E₂) (hB : Nat.card ↥(K₁ ⊓ K₂) = 192) :
    ∃ ψ : ↥m22TwoStab ≃* ↥K₁,
      (∀ g : ↥m22TwoStab, ((ψ g : ↥K₁) : L) ∈ K₂ ↔ (g : M22) ∈ m22PtHexStab) ∧
      (∀ g : ↥m22TwoStab, ((ψ g : ↥K₁) : L) ∈ E₁ ↔ (g : M22) ∈ barA1) ∧
      ∀ g : ↥m22TwoStab, ((ψ g : ↥K₁) : L) ∈ E₂ ↔ (g : M22) ∈ barA2 := by
  obtain ⟨ψ, hψ⟩ := exists_iso_P1_of_parabolic h
  set H := (K₂.subgroupOf K₁).comap ψ.toMonoidHom with hH
  set F := (E₂.subgroupOf K₁).comap ψ.toMonoidHom with hF
  have hHmem : ∀ x, x ∈ H ↔ ((ψ x : ↥K₁) : L) ∈ K₂ := fun x => Iff.rfl
  have hFmem : ∀ x, x ∈ F ↔ ((ψ x : ↥K₁) : L) ∈ E₂ := fun x => Iff.rfl
  have hHc : Nat.card H = 192 := by rw [hH, card_comap_subgroupOf, hB]
  have hFc : Nat.card F = 16 := by
    rw [hF, card_comap_subgroupOf, inf_eq_right.mpr (hE₂.trans inf_le_left), hE₂c]
  have hFn : ∀ y ∈ H, ∀ f ∈ F, y * f * y⁻¹ ∈ F := by
    intro y hy f hf
    rw [hFmem, map_mul, map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
    exact hE₂n _ ((hHmem y).mp hy) _ ((hFmem f).mp hf)
  have hF2 : ∀ f ∈ F, f * f = 1 := by
    intro f hf
    apply ψ.injective
    apply Subtype.ext
    rw [map_mul, Subgroup.coe_mul, map_one, Subgroup.coe_one]
    exact hE₂2 _ ((hFmem f).mp hf)
  have hFA : F ≠ barA1' := by
    intro hFe
    apply hne
    ext e
    constructor
    · intro he
      obtain ⟨x, hx⟩ := ψ.surjective ⟨e, h.le he⟩
      have hxA : x ∈ barA1' := by
        rw [Subgroup.mem_subgroupOf, ← hψ, hx]
        exact he
      rw [← hFe, hFmem, hx] at hxA
      exact hxA
    · intro he
      obtain ⟨x, hx⟩ := ψ.surjective ⟨e, (hE₂.trans inf_le_left) he⟩
      have hxF : x ∈ F := by
        rw [hFmem, hx]
        exact he
      rw [hFe, Subgroup.mem_subgroupOf, ← hψ, hx] at hxF
      exact hxF
  obtain ⟨g, hgH, hgF⟩ := exists_conj_P1 hHc hFn hF2 hFc hFA
  refine ⟨(MulAut.conj g).trans ψ, fun x => ?_, fun x => ?_, fun x => ?_⟩
  · rw [MulEquiv.trans_apply, MulAut.conj_apply, ← hHmem, hgH,
      show g⁻¹ * (g * x * g⁻¹) * g = x by group, Subgroup.mem_subgroupOf]
  · rw [MulEquiv.trans_apply, MulAut.conj_apply, hψ, Subgroup.coe_mul, Subgroup.coe_mul,
      Subgroup.coe_inv]
    constructor
    · intro hx
      have := conj_mem_barA1 (m22TwoStab.inv_mem g.2) hx
      rwa [show (g : M22)⁻¹ * ((g : M22) * x * (g : M22)⁻¹) * (g : M22)⁻¹⁻¹ = x by group] at this
    · intro hx
      exact conj_mem_barA1 g.2 hx
  · rw [MulEquiv.trans_apply, MulAut.conj_apply, ← hFmem, hgF,
      show g⁻¹ * (g * x * g⁻¹) * g = x by group, Subgroup.mem_subgroupOf]

theorem exists_iso_P2_normalized
    {L : Type*} [Group L] [Finite L] {K₁ K₂ E₁ E₂ : Subgroup L} {a b : L}
    (h : IsParabolic K₂ E₂ a b) (hE₁ : E₁ ≤ K₁ ⊓ K₂)
    (hE₁n : ∀ x ∈ K₁, ∀ e ∈ E₁, x * e * x⁻¹ ∈ E₁) (hE₁2 : ∀ e ∈ E₁, e * e = 1)
    (hE₁c : Nat.card E₁ = 16) (hne : E₁ ≠ E₂) (hB : Nat.card ↥(K₁ ⊓ K₂) = 192) :
    ∃ ψ : ↥m22PtHexStab ≃* ↥K₂,
      (∀ g : ↥m22PtHexStab, ((ψ g : ↥K₂) : L) ∈ K₁ ↔ (g : M22) ∈ m22TwoStab) ∧
      (∀ g : ↥m22PtHexStab, ((ψ g : ↥K₂) : L) ∈ E₂ ↔ (g : M22) ∈ barA2) ∧
      ∀ g : ↥m22PtHexStab, ((ψ g : ↥K₂) : L) ∈ E₁ ↔ (g : M22) ∈ barA1 := by
  obtain ⟨ψ, hψ⟩ := exists_iso_P2_of_parabolic h
  set H := (K₁.subgroupOf K₂).comap ψ.toMonoidHom with hH
  set F := (E₁.subgroupOf K₂).comap ψ.toMonoidHom with hF
  have hHmem : ∀ x, x ∈ H ↔ ((ψ x : ↥K₂) : L) ∈ K₁ := fun x => Iff.rfl
  have hFmem : ∀ x, x ∈ F ↔ ((ψ x : ↥K₂) : L) ∈ E₁ := fun x => Iff.rfl
  have hHc : Nat.card H = 192 := by rw [hH, card_comap_subgroupOf, inf_comm, hB]
  have hFc : Nat.card F = 16 := by
    rw [hF, card_comap_subgroupOf, inf_eq_right.mpr (hE₁.trans inf_le_right), hE₁c]
  have hFn : ∀ y ∈ H, ∀ f ∈ F, y * f * y⁻¹ ∈ F := by
    intro y hy f hf
    rw [hFmem, map_mul, map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
    exact hE₁n _ ((hHmem y).mp hy) _ ((hFmem f).mp hf)
  have hF2 : ∀ f ∈ F, f * f = 1 := by
    intro f hf
    apply ψ.injective
    apply Subtype.ext
    rw [map_mul, Subgroup.coe_mul, map_one, Subgroup.coe_one]
    exact hE₁2 _ ((hFmem f).mp hf)
  have hFA : F ≠ barA2' := by
    intro hFe
    apply hne
    ext e
    constructor
    · intro he
      obtain ⟨x, hx⟩ := ψ.surjective ⟨e, (hE₁.trans inf_le_right) he⟩
      have hxF : x ∈ F := by
        rw [hFmem, hx]
        exact he
      rw [hFe, Subgroup.mem_subgroupOf, ← hψ, hx] at hxF
      exact hxF
    · intro he
      obtain ⟨x, hx⟩ := ψ.surjective ⟨e, h.le he⟩
      have hxA : x ∈ barA2' := by
        rw [Subgroup.mem_subgroupOf, ← hψ, hx]
        exact he
      rw [← hFe, hFmem, hx] at hxA
      exact hxA
  obtain ⟨g, hgH, hgF⟩ := exists_conj_P2 hHc hFn hF2 hFc hFA
  refine ⟨(MulAut.conj g).trans ψ, fun x => ?_, fun x => ?_, fun x => ?_⟩
  · rw [MulEquiv.trans_apply, MulAut.conj_apply, ← hHmem, hgH,
      show g⁻¹ * (g * x * g⁻¹) * g = x by group, Subgroup.mem_subgroupOf]
  · rw [MulEquiv.trans_apply, MulAut.conj_apply, hψ, Subgroup.coe_mul, Subgroup.coe_mul,
      Subgroup.coe_inv]
    constructor
    · intro hx
      have := conj_mem_barA2 (m22PtHexStab.inv_mem g.2) hx
      rwa [show (g : M22)⁻¹ * ((g : M22) * x * (g : M22)⁻¹) * (g : M22)⁻¹⁻¹ = x by group] at this
    · intro hx
      exact conj_mem_barA2 g.2 hx
  · rw [MulEquiv.trans_apply, MulAut.conj_apply, ← hFmem, hgF,
      show g⁻¹ * (g * x * g⁻¹) * g = x by group, Subgroup.mem_subgroupOf]

theorem exists_amalgam_iso
    {L : Type*} [Group L] [Finite L] {L₁ L₂ E₁ E₂ : Subgroup L}
    {a₁ b₁ a₂ b₂ : L} (h₁ : IsParabolic L₁ E₁ a₁ b₁) (h₂ : IsParabolic L₂ E₂ a₂ b₂)
    (hE₁₂ : E₁ ≤ L₂) (hE₂₁ : E₂ ≤ L₁) (hne : E₁ ≠ E₂) (hB : Nat.card ↥(L₁ ⊓ L₂) = 192) :
    ∃ (φ₁ : ↥m22TwoStab ≃* ↥L₁) (φ₂ : ↥m22PtHexStab ≃* ↥L₂),
      (∀ (b : M22) (hb₁ : b ∈ m22TwoStab) (hb₂ : b ∈ m22PtHexStab),
        ((φ₁ ⟨b, hb₁⟩ : ↥L₁) : L) = φ₂ ⟨b, hb₂⟩) ∧
      ∀ p : ↥m22TwoStab, ((φ₁ p : ↥L₁) : L) ∈ L₂ ↔ (p : M22) ∈ m22PtHexStab := by
  obtain ⟨ψ₁, hB₁, hE₁, hE₂⟩ := exists_iso_P1_normalized h₁ (le_inf hE₂₁ h₂.le) h₂.normal
    h₂.mul_self h₂.card_E hne hB
  obtain ⟨ψ₂, hB₂, hE₂', hE₁'⟩ := exists_iso_P2_normalized h₂ (le_inf h₁.le hE₁₂) h₁.normal
    h₁.mul_self h₁.card_E hne hB
  exact exists_glue ψ₁ ψ₂ hB₁ hB₂ hE₁ (fun g _ => hE₂ g) hE₁' hE₂'

theorem exists_mulEquiv_m22Stab_of_parabolics
    {L : Type*} [Group L] [Finite L] {L₁ L₂ E₁ E₂ : Subgroup L} {a₁ b₁ a₂ b₂ : L}
    (hgen : L₁ ⊔ L₂ = ⊤) (h₁ : IsParabolic L₁ E₁ a₁ b₁) (h₂ : IsParabolic L₂ E₂ a₂ b₂)
    (hE₁₂ : E₁ ≤ L₂) (hE₂₁ : E₂ ≤ L₁) (hne : E₁ ≠ E₂) (hB : Nat.card ↥(L₁ ⊓ L₂) = 192)
    {t₁ t₂ : L} (ht₁ : t₁ ∈ L₁) (ht₁' : t₁ ∉ L₂) (ht₂ : t₂ ∈ L₂) (ht₂' : t₂ ∉ L₁)
    (hs₁ : t₁ * t₁ = 1) (hs₂ : t₂ * t₂ = 1) (h₃ : orderOf (t₁ * t₂) ≤ 3) :
    ∃ Φ : L ≃* stabilizer M22 (0 : Fin 22),
      (∀ x : L, x ∈ L₁ ↔ ((Φ x : ↥(stabilizer M22 (0 : Fin 22))) : M22) ∈ m22TwoStab) ∧
      ∀ x : L, x ∈ L₂ ↔ ((Φ x : ↥(stabilizer M22 (0 : Fin 22))) : M22) ∈ m22PtHexStab := by
  obtain ⟨φ₁, φ₂, hB', hB''⟩ := exists_amalgam_iso h₁ h₂ hE₁₂ hE₂₁ hne hB
  obtain ⟨Φ, hΦ₁, hΦ₂⟩ := nonempty_mulEquiv_m22Stab_of_amalgam hgen φ₁ φ₂ hB' hB'' ht₁ ht₁'
    ht₂ ht₂' hs₁ hs₂ h₃
  refine ⟨Φ, fun x => ⟨fun hx => ?_, fun hx => ?_⟩, fun x => ⟨fun hx => ?_, fun hx => ?_⟩⟩
  · obtain ⟨p, hp⟩ := φ₁.surjective ⟨x, hx⟩
    rw [← show ((φ₁ p : ↥L₁) : L) = x from congrArg Subtype.val hp, hΦ₁]
    exact p.2
  · have e : Φ ((φ₁ ⟨_, hx⟩ : ↥L₁) : L) = Φ x := Subtype.ext (hΦ₁ ⟨_, hx⟩)
    rw [← Φ.injective e]
    exact (φ₁ _).2
  · obtain ⟨p, hp⟩ := φ₂.surjective ⟨x, hx⟩
    rw [← show ((φ₂ p : ↥L₂) : L) = x from congrArg Subtype.val hp, hΦ₂]
    exact p.2
  · have e : Φ ((φ₂ ⟨_, hx⟩ : ↥L₂) : L) = Φ x := Subtype.ext (hΦ₂ ⟨_, hx⟩)
    rw [← Φ.injective e]
    exact (φ₂ _).2

end CFSG.Quasithin.L34Amalgam
