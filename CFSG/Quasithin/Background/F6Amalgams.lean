module

public import CFSG.Quasithin.Background.F6GoldschmidtList
public import CFSG.Quasithin.Background.F6Basic
public import CFSG.Quasithin.Recognition.GoldschmidtTripleQuotient

public section

universe u

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique

namespace F6

theorem isGoldCase_quotient_pCore (hlist : GoldschmidtS3List.{u}) {D : Type u} [Group D]
    [Finite D] {G₁ G₂ : Subgroup D} (h : IsGoldschmidtTriple G₁ G₂) :
    IsGoldCase (G₁.map (QuotientGroup.mk' (Open.pCore 2 D)))
      (G₂.map (QuotientGroup.mk' (Open.pCore 2 D))) :=
  hlist _ _ _ h.quotient_pCore

variable {D : Type*} [Group D]

theorem charTwo_iff_centralizer_le {H : Subgroup D} :
    CharTwo H ↔ Subgroup.centralizer (Open.pCore 2 ↥H : Set ↥H) ≤ Open.pCore 2 ↥H := by
  constructor
  · intro hc x hx
    have hx' : (x : D) ∈ H ⊓ Subgroup.centralizer (pCoreOf 2 H : Set D) := by
      refine Subgroup.mem_inf.mpr ⟨x.2, ?_⟩
      rw [Subgroup.mem_centralizer_iff]
      rintro _ ⟨y, hy, rfl⟩
      exact congrArg Subtype.val ((Subgroup.mem_centralizer_iff.mp hx) y hy)
    obtain ⟨y, hy, hyx⟩ := hc hx'
    rwa [← Subtype.ext hyx]
  · rintro hc x ⟨hxH, hxc⟩
    have hx' : (⟨x, hxH⟩ : ↥H) ∈ Subgroup.centralizer (Open.pCore 2 ↥H : Set ↥H) := by
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      exact Subtype.ext ((Subgroup.mem_centralizer_iff.mp hxc) y ⟨y, hy, rfl⟩)
    exact ⟨_, hc hx', rfl⟩

theorem centralizer_pCore_le_of_mulEquiv {M M' : Type*} [Group M] [Group M'] (e : M ≃* M')
    (h : Subgroup.centralizer (Open.pCore 2 M : Set M) ≤ Open.pCore 2 M) :
    Subgroup.centralizer (Open.pCore 2 M' : Set M') ≤ Open.pCore 2 M' := by
  intro x hx
  have hP : (Open.pCore 2 M).map e.toMonoidHom = Open.pCore 2 M' := map_pCore_mulEquiv 2 e
  have hx' : e.symm x ∈ Subgroup.centralizer (Open.pCore 2 M : Set M) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have hy' : e y ∈ Open.pCore 2 M' := hP ▸ ⟨y, hy, rfl⟩
    have := (Subgroup.mem_centralizer_iff.mp hx) _ hy'
    apply e.injective
    simpa using this
  have := h hx'
  rw [← hP]
  exact ⟨_, this, by simp⟩

theorem charTwo_of_mulEquiv {E : Type*} [Group E] {H : Subgroup D} {K : Subgroup E}
    (e : ↥K ≃* ↥H) (hK : CharTwo K) : CharTwo H :=
  charTwo_iff_centralizer_le.mpr
    (centralizer_pCore_le_of_mulEquiv e (charTwo_iff_centralizer_le.mp hK))

theorem charTwo_of_mulEquiv_of_le {M : Type*} [Group M] [Finite M] {H : Subgroup D}
    (e : ↥H ≃* M) {V : Subgroup M} (hVn : V.Normal) (hV2 : ∀ v ∈ V, v ^ 2 = 1)
    (hcV : ∀ g : M, (∀ v ∈ V, g * v = v * g) → g ∈ V) : CharTwo H := by
  refine charTwo_iff_centralizer_le.mpr (centralizer_pCore_le_of_mulEquiv e.symm ?_)
  have hVle : V ≤ Open.pCore 2 M := le_pCore 2 hVn fun v => ⟨1, by
    apply Subtype.ext
    simpa using hV2 v v.2⟩
  intro g hg
  refine hVle (hcV g fun v hv => ?_)
  exact (Subgroup.mem_centralizer_iff.mp hg v (hVle hv)).symm

theorem not_charTwo_of_mem [Finite D] {H : Subgroup D} {x : D} (hx : x ∈ H)
    (hx3 : orderOf x = 3) (hconj : ∀ h ∈ H, h * x * h⁻¹ = x ∨ h * x * h⁻¹ = x⁻¹) :
    ¬ CharTwo H := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro hc
  have hnot : x ∉ pCoreOf 2 H := by
    intro hxQ
    obtain ⟨k, hk⟩ := (pCoreOf_isPGroup 2 H) ⟨x, hxQ⟩
    have hk' : x ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    have := orderOf_dvd_of_pow_eq_one hk'
    rw [hx3] at this
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).mp
      (Nat.prime_three.dvd_of_dvd_pow this)
    omega
  apply hnot
  refine hc (Subgroup.mem_inf.mpr ⟨hx, ?_⟩)
  rw [Subgroup.mem_centralizer_iff]
  intro q hq
  rcases hconj q (pCoreOf_le 2 H hq) with h1 | h1
  · calc q * x = q * x * q⁻¹ * q := by group
      _ = x * q := by rw [h1]
  ·
    exfalso
    apply hnot
    have hqn : q * (x * q⁻¹ * x⁻¹) ∈ pCoreOf 2 H := by
      refine (pCoreOf 2 H).mul_mem hq ?_
      have := (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 H hx) q⁻¹).mp
        ((pCoreOf 2 H).inv_mem hq)
      exact this
    have hx2 : x⁻¹ * x⁻¹ = x := by
      have h3 : x ^ 3 = 1 := by rw [← hx3]; exact pow_orderOf_eq_one x
      calc x⁻¹ * x⁻¹ = x⁻¹ * x⁻¹ * x ^ 3 := by rw [h3, mul_one]
        _ = x := by group
    have : q * (x * q⁻¹ * x⁻¹) = x := by
      calc q * (x * q⁻¹ * x⁻¹) = q * x * q⁻¹ * x⁻¹ := by group
        _ = x⁻¹ * x⁻¹ := by rw [h1]
        _ = x := hx2
    rwa [this] at hqn

theorem not_charTwo_of_mulEquiv [Finite D] {M : Type*} [Group M] {H : Subgroup D} (e : ↥H ≃* M)
    {c : M} (hc3 : orderOf c = 3) (hconj : ∀ m : M, m * c * m⁻¹ = c ∨ m * c * m⁻¹ = c⁻¹) :
    ¬ CharTwo H := by
  refine not_charTwo_of_mem (x := (e.symm c : D)) (e.symm c).2 ?_ ?_
  · rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq, hc3]
  · intro h hh
    rcases hconj (e ⟨h, hh⟩) with h1 | h1
    · left
      have := congrArg (fun m => ((e.symm m : ↥H) : D)) h1
      simpa using this
    · right
      have := congrArg (fun m => ((e.symm m : ↥H) : D)) h1
      simpa using this

theorem charTwo_of_mulEquiv_of_pred {M : Type*} [Group M] [Finite M] {H : Subgroup D}
    (e : ↥H ≃* M) (P : M → Prop) (h1 : P 1) (hmul : ∀ a b, P a → P b → P (a * b))
    (hinv : ∀ a, P a → P a⁻¹) (hn : ∀ g a, P a → P (g * a * g⁻¹)) (h2 : ∀ a, P a → a ^ 2 = 1)
    (hc : ∀ g, (∀ a, P a → g * a = a * g) → P g) : CharTwo H := by
  let V : Subgroup M :=
    { carrier := {a | P a}
      mul_mem' := fun ha hb => hmul _ _ ha hb
      one_mem' := h1
      inv_mem' := fun ha => hinv _ ha }
  exact charTwo_of_mulEquiv_of_le e (V := V) ⟨fun a ha g => hn g a ha⟩ (fun a ha => h2 a ha)
    (fun g hg => hc g fun a ha => hg a ha)

theorem finRotate_three_facts :
    orderOf (finRotate 3) = 3 ∧ ∀ m : Equiv.Perm (Fin 3),
      m * finRotate 3 * m⁻¹ = finRotate 3 ∨ m * finRotate 3 * m⁻¹ = (finRotate 3)⁻¹ :=
  ⟨orderOf_eq_prime (by decide) (by decide), by decide⟩

theorem dihedral6_facts :
    orderOf (DihedralGroup.r 2 : DihedralGroup 6) = 3 ∧ ∀ m : DihedralGroup 6,
      m * DihedralGroup.r 2 * m⁻¹ = DihedralGroup.r 2 ∨
        m * DihedralGroup.r 2 * m⁻¹ = (DihedralGroup.r 2)⁻¹ :=
  ⟨orderOf_eq_prime (by decide) (by decide), by decide⟩

theorem dihedral12_facts :
    orderOf (DihedralGroup.r 4 : DihedralGroup 12) = 3 ∧ ∀ m : DihedralGroup 12,
      m * DihedralGroup.r 4 * m⁻¹ = DihedralGroup.r 4 ∨
        m * DihedralGroup.r 4 * m⁻¹ = (DihedralGroup.r 4)⁻¹ :=
  ⟨orderOf_eq_prime (by decide) (by decide), by decide⟩

theorem s3_d8_facts :
    orderOf ((finRotate 3, 1) : Equiv.Perm (Fin 3) × DihedralGroup 4) = 3 ∧
      ∀ m : Equiv.Perm (Fin 3) × DihedralGroup 4,
        m * (finRotate 3, 1) * m⁻¹ = (finRotate 3, 1) ∨
          m * (finRotate 3, 1) * m⁻¹ = (finRotate 3, 1)⁻¹ :=
  ⟨orderOf_eq_prime (by decide) (by decide), by decide⟩

theorem z3_e4_facts :
    orderOf ((Multiplicative.ofAdd 1, 1) :
        Multiplicative (ZMod 3) × (Multiplicative (ZMod 2) × Multiplicative (ZMod 2))) = 3 ∧
      ∀ y : Multiplicative (ZMod 3) × (Multiplicative (ZMod 2) × Multiplicative (ZMod 2)),
        y ^ 3 = 1 → y = 1 ∨ y = (Multiplicative.ofAdd 1, 1) ∨
          y = (Multiplicative.ofAdd 1, 1)⁻¹ :=
  ⟨orderOf_eq_prime (by decide) (by decide), by decide⟩

theorem not_charTwo_of_isExtensionOf_z3_e4 [Finite D] {H : Subgroup D}
    (hH : IsExtensionOf ↥H (Multiplicative (ZMod 2))
      (Multiplicative (ZMod 3) × (Multiplicative (ZMod 2) × Multiplicative (ZMod 2)))) :
    ¬ CharTwo H := by
  obtain ⟨φ, -, ⟨e⟩⟩ := hH
  obtain ⟨hc3, hcube⟩ := z3_e4_facts
  set c₀ : Multiplicative (ZMod 3) × (Multiplicative (ZMod 2) × Multiplicative (ZMod 2)) :=
    (Multiplicative.ofAdd 1, 1) with hc₀
  have hcK : orderOf (e.symm c₀) = 3 := by rw [MulEquiv.orderOf_eq, hc3]
  set c : ↥H := (e.symm c₀).val with hcdef
  have hc : orderOf c = 3 := by rw [hcdef, Subgroup.orderOf_coe, hcK]
  refine not_charTwo_of_mem (x := (c : D)) c.2 (by rw [Subgroup.orderOf_coe, hc]) fun h hh => ?_
  set g : ↥H := ⟨h, hh⟩ with hg
  have hker : g * c * g⁻¹ ∈ φ.ker :=
    (inferInstance : φ.ker.Normal).conj_mem c (e.symm c₀).2 g
  have hy : (⟨g * c * g⁻¹, hker⟩ : ↥φ.ker) ^ 3 = 1 := by
    apply Subtype.ext
    rw [SubgroupClass.coe_pow, conj_pow, ← hc, pow_orderOf_eq_one, mul_one, mul_inv_cancel]
    rfl
  have hy3 : e ⟨g * c * g⁻¹, hker⟩ ^ 3 = 1 := by rw [← map_pow, hy, map_one]
  have hD : ∀ z : ↥H, (z : D) = ((g * c * g⁻¹ : ↥H) : D) → (z : D) = h * (c : D) * h⁻¹ :=
    fun z hz => by rw [hz]; simp [hg]
  rcases hcube _ hy3 with h1 | h1 | h1
  · exfalso
    have h2 : (⟨g * c * g⁻¹, hker⟩ : ↥φ.ker) = 1 := e.injective (by rw [h1, map_one])
    have h3 : g * c * g⁻¹ = 1 := congrArg Subtype.val h2
    have h4 : c = 1 := by
      calc c = g⁻¹ * (g * c * g⁻¹) * g := by group
        _ = 1 := by rw [h3]; group
    rw [h4, orderOf_one] at hc
    omega
  · left
    have h2 : (⟨g * c * g⁻¹, hker⟩ : ↥φ.ker) = e.symm c₀ :=
      e.injective (by rw [h1, MulEquiv.apply_symm_apply])
    have h3 : g * c * g⁻¹ = c := congrArg Subtype.val h2
    have := congrArg Subtype.val h3
    simpa [hg] using this
  · right
    have h2 : (⟨g * c * g⁻¹, hker⟩ : ↥φ.ker) = (e.symm c₀)⁻¹ :=
      e.injective (by rw [h1, map_inv, MulEquiv.apply_symm_apply])
    have h3 : g * c * g⁻¹ = c⁻¹ := congrArg Subtype.val h2
    have := congrArg Subtype.val h3
    simpa [hg] using this

theorem not_charTwo_of_isGoldCase_i_v [Finite D] {H₁ H₂ : Subgroup D}
    (h : IsGoldCaseI H₁ H₂ ∨ IsGoldCaseII H₁ H₂ ∨ IsGoldCaseIII H₁ H₂ ∨ IsGoldCaseIV H₁ H₂ ∨
      IsGoldCaseV H₁ H₂) : ¬ CharTwo H₁ ∨ ¬ CharTwo H₂ := by
  rcases h with ⟨⟨e⟩, -, -⟩ | ⟨⟨e⟩, -, -⟩ | ⟨⟨e⟩, -, -⟩ | ⟨-, -, hext⟩ | ⟨-, -, ⟨e⟩⟩
  · exact Or.inl (not_charTwo_of_mulEquiv e finRotate_three_facts.1 finRotate_three_facts.2)
  · exact Or.inl (not_charTwo_of_mulEquiv e dihedral6_facts.1 dihedral6_facts.2)
  · exact Or.inl (not_charTwo_of_mulEquiv e dihedral12_facts.1 dihedral12_facts.2)
  · exact Or.inr (not_charTwo_of_isExtensionOf_z3_e4 hext)
  · exact Or.inr (not_charTwo_of_mulEquiv e s3_d8_facts.1 s3_d8_facts.2)

@[expose] def kleinFourPerm (g : Equiv.Perm (Fin 4)) : Prop :=
  g = 1 ∨ g = Equiv.swap 0 1 * Equiv.swap 2 3 ∨ g = Equiv.swap 0 2 * Equiv.swap 1 3 ∨
    g = Equiv.swap 0 3 * Equiv.swap 1 2

instance : DecidablePred kleinFourPerm := fun g => by unfold kleinFourPerm; infer_instance

theorem kleinFourPerm_mul : ∀ a b, kleinFourPerm a → kleinFourPerm b → kleinFourPerm (a * b) := by
  decide

theorem kleinFourPerm_inv : ∀ a, kleinFourPerm a → kleinFourPerm a⁻¹ := by decide

theorem kleinFourPerm_conj : ∀ g a, kleinFourPerm a → kleinFourPerm (g * a * g⁻¹) := by decide

theorem kleinFourPerm_sq : ∀ a, kleinFourPerm a → a ^ 2 = 1 := by decide

theorem kleinFourPerm_centralizer :
    ∀ g : Equiv.Perm (Fin 4), (∀ a, kleinFourPerm a → g * a = a * g) → kleinFourPerm g := by
  decide

theorem charTwo_of_mulEquiv_perm_four {H : Subgroup D} (e : ↥H ≃* Equiv.Perm (Fin 4)) :
    CharTwo H :=
  charTwo_of_mulEquiv_of_pred e kleinFourPerm (Or.inl rfl) kleinFourPerm_mul kleinFourPerm_inv
    kleinFourPerm_conj kleinFourPerm_sq kleinFourPerm_centralizer

theorem charTwo_of_mulEquiv_z2_perm_four {H : Subgroup D}
    (e : ↥H ≃* Multiplicative (ZMod 2) × Equiv.Perm (Fin 4)) : CharTwo H := by
  refine charTwo_of_mulEquiv_of_pred e (fun g => kleinFourPerm g.2) (Or.inl rfl)
    (fun a b ha hb => kleinFourPerm_mul _ _ ha hb) (fun a ha => kleinFourPerm_inv _ ha)
    (fun g a ha => kleinFourPerm_conj _ _ ha) (fun a ha => ?_) (fun g hg => ?_)
  · have h1 : a.1 ^ 2 = 1 := by
      have : ∀ x : Multiplicative (ZMod 2), x ^ 2 = 1 := by decide
      exact this a.1
    exact Prod.ext h1 (kleinFourPerm_sq _ ha)
  · refine kleinFourPerm_centralizer g.2 fun b hb => ?_
    have := congrArg Prod.snd (hg (1, b) hb)
    simpa using this

@[expose] def MaxTwoLocalsCharTwo (IsY : ∀ (W : Type) [Group W], Prop) : Prop :=
  ∀ (W : Type) [Group W] [Finite W], IsY W → ∀ K : Subgroup W, quasithinIsMaxTwoLocal K →
    (∃ S : Sylow 2 W, (S : Subgroup W) ≤ K) → CharTwo K

theorem charTwo_of_isYAmalgam {IsY : ∀ (W : Type) [Group W], Prop}
    (hY : MaxTwoLocalsCharTwo IsY) {H₁ H₂ : Subgroup D} (h : IsYAmalgam IsY H₁ H₂) :
    CharTwo H₁ ∧ CharTwo H₂ := by
  obtain ⟨W, _, _, K₁, K₂, hW, ⟨hm₁, hm₂, -, S, hS⟩, φ₁, φ₂, -⟩ := h
  exact ⟨charTwo_of_mulEquiv φ₁.symm (hY W hW K₁ hm₁ ⟨S, hS ▸ inf_le_left⟩),
    charTwo_of_mulEquiv φ₂.symm (hY W hW K₂ hm₂ ⟨S, hS ▸ inf_le_right⟩)⟩

theorem charTwo_of_isGoldCaseVI (hG22 : MaxTwoLocalsCharTwo IsG22)
    (hG22' : MaxTwoLocalsCharTwo IsG22Prime) (hM12 : MaxTwoLocalsCharTwo IsM12)
    (hAut : MaxTwoLocalsCharTwo IsAutM12) {H₁ H₂ : Subgroup D} (h : IsGoldCaseVI H₁ H₂) :
    CharTwo H₁ ∧ CharTwo H₂ := by
  rcases h with ⟨-, -, ⟨e₁⟩, ⟨e₂⟩⟩ | ⟨-, -, ⟨e₁⟩, ⟨e₂⟩⟩ | ⟨hY, -⟩ | ⟨hY, -⟩ | ⟨hY, -⟩ | ⟨hY, -⟩
  · exact ⟨charTwo_of_mulEquiv_perm_four e₁, charTwo_of_mulEquiv_perm_four e₂⟩
  · exact ⟨charTwo_of_mulEquiv_z2_perm_four e₁, charTwo_of_mulEquiv_z2_perm_four e₂⟩
  · exact charTwo_of_isYAmalgam hG22 hY
  · exact charTwo_of_isYAmalgam hG22' hY
  · exact charTwo_of_isYAmalgam hM12 hY
  · exact charTwo_of_isYAmalgam hAut hY

theorem isGoldCaseVI_of_charTwo [Finite D] {H₁ H₂ : Subgroup D} (h : IsGoldCase H₁ H₂)
    (h₁ : CharTwo H₁) (h₂ : CharTwo H₂) : IsGoldCaseVI H₁ H₂ ∨ IsGoldCaseVI H₂ H₁ := by
  rcases h with h | h
  · rcases h with h | h | h | h | h | h
    · rcases not_charTwo_of_isGoldCase_i_v (Or.inl h) with h' | h' <;> contradiction
    · rcases not_charTwo_of_isGoldCase_i_v (Or.inr (Or.inl h)) with h' | h' <;> contradiction
    · rcases not_charTwo_of_isGoldCase_i_v (Or.inr (Or.inr (Or.inl h))) with h' | h' <;>
        contradiction
    · rcases not_charTwo_of_isGoldCase_i_v (Or.inr (Or.inr (Or.inr (Or.inl h)))) with h' | h' <;>
        contradiction
    · rcases not_charTwo_of_isGoldCase_i_v (Or.inr (Or.inr (Or.inr (Or.inr h)))) with h' | h' <;>
        contradiction
    · exact Or.inl h
  · rcases h with h | h | h | h | h | h
    · rcases not_charTwo_of_isGoldCase_i_v (Or.inl h) with h' | h' <;> contradiction
    · rcases not_charTwo_of_isGoldCase_i_v (Or.inr (Or.inl h)) with h' | h' <;> contradiction
    · rcases not_charTwo_of_isGoldCase_i_v (Or.inr (Or.inr (Or.inl h))) with h' | h' <;>
        contradiction
    · rcases not_charTwo_of_isGoldCase_i_v (Or.inr (Or.inr (Or.inr (Or.inl h)))) with h' | h' <;>
        contradiction
    · rcases not_charTwo_of_isGoldCase_i_v (Or.inr (Or.inr (Or.inr (Or.inr h)))) with h' | h' <;>
        contradiction
    · exact Or.inr h

theorem mem_centerOf_of_mem_omegaOneCenterOf {T : Subgroup D} {x : D}
    (hx : x ∈ omegaOneCenterOf T) : x ∈ centerOf T ∧ x ^ 2 = 1 := by
  induction hx using Subgroup.closure_induction with
  | mem y hy => exact hy
  | one => exact ⟨(centerOf T).one_mem, one_pow 2⟩
  | mul y z _ _ hy hz =>
    refine ⟨(centerOf T).mul_mem hy.1 hz.1, ?_⟩
    have hc : Commute y z := (Subgroup.mem_centralizer_iff.mp hy.1.2 z hz.1.1).symm
    rw [hc.mul_pow, hy.2, hz.2, one_mul]
  | inv y _ hy => exact ⟨(centerOf T).inv_mem hy.1, by rw [inv_pow, hy.2, inv_one]⟩

@[expose] def AtMostOneInvolution (S : Subgroup D) : Prop :=
  ∀ x ∈ S, ∀ y ∈ S, x ^ 2 = 1 → y ^ 2 = 1 → x ≠ 1 → y ≠ 1 → x = y

theorem card_omegaOneCenterOf_le_two [Finite D] {T S : Subgroup D} (hTS : centerOf T ≤ S)
    (hS : AtMostOneInvolution S) : Nat.card ↥(omegaOneCenterOf T) ≤ 2 := by
  by_cases hex : ∃ z ∈ omegaOneCenterOf T, z ≠ 1
  · obtain ⟨z, hz, hz1⟩ := hex
    have hz' := mem_centerOf_of_mem_omegaOneCenterOf hz
    have hle : omegaOneCenterOf T ≤ Subgroup.zpowers z := by
      intro x hx
      have hx' := mem_centerOf_of_mem_omegaOneCenterOf hx
      by_cases hx1 : x = 1
      · rw [hx1]; exact (Subgroup.zpowers z).one_mem
      · rw [hS x (hTS hx'.1) z (hTS hz'.1) hx'.2 hz'.2 hx1 hz1]
        exact Subgroup.mem_zpowers z
    calc Nat.card ↥(omegaOneCenterOf T) ≤ Nat.card ↥(Subgroup.zpowers z) :=
          Subgroup.card_le_of_le hle
      _ = orderOf z := Nat.card_zpowers z
      _ ≤ 2 := Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one hz'.2)
  · have : omegaOneCenterOf T = ⊥ := (Subgroup.eq_bot_iff_forall _).mpr fun x hx => by
      by_contra hne
      exact hex ⟨x, hx, hne⟩
    rw [this, Subgroup.card_bot]
    norm_num

theorem centerOf_inf_le_centerOf_pCoreOf [Finite D] {H₁ H₂ : Subgroup D}
    (h : IsGoldschmidtTriple H₁ H₂) (hc : CharTwo H₁) :
    centerOf (H₁ ⊓ H₂) ≤ centerOf (pCoreOf 2 H₁) := by
  intro x hx
  have hR := pCoreOf_le_inf_left h
  have hxc : x ∈ Subgroup.centralizer (pCoreOf 2 H₁ : Set D) :=
    Subgroup.centralizer_le hR hx.2
  have hxR : x ∈ pCoreOf 2 H₁ := hc (Subgroup.mem_inf.mpr ⟨hx.1.1, hxc⟩)
  exact Subgroup.mem_inf.mpr ⟨hxR, hxc⟩

theorem normal_of_sup_eq_top {R : Type*} [Group R] {A B : Subgroup R} (hAB : A ⊔ B = ⊤)
    (hc : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) : B.Normal := by
  rw [← Subgroup.normalizer_eq_top_iff, ← top_le_iff, ← hAB]
  refine sup_le (fun a ha => ?_) Subgroup.le_normalizer
  rw [Subgroup.mem_normalizer_iff]
  intro b
  constructor
  · intro hb
    rw [hc a ha b hb, mul_inv_cancel_right]
    exact hb
  · intro hb
    have h1 := hc a ha _ hb
    have : b = a * b * a⁻¹ := by
      calc b = a⁻¹ * ((a * b * a⁻¹) * a) := by group
        _ = a⁻¹ * (a * (a * b * a⁻¹)) := by rw [h1]
        _ = a * b * a⁻¹ := by group
    rw [this]
    exact hb

theorem exists_mul_of_mem_center {R : Type*} [Group R] {A B : Subgroup R} (hAB : A ⊔ B = ⊤)
    (hc : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) {x : R} (hx : x ∈ Subgroup.center R) :
    ∃ a ∈ A, ∃ b ∈ B, x = a * b ∧ (∀ a' ∈ A, a * a' = a' * a) ∧ ∀ b' ∈ B, b * b' = b' * b := by
  have hBn : B.Normal := normal_of_sup_eq_top hAB hc
  have hx' : x ∈ ((A ⊔ B : Subgroup R) : Set R) := by rw [hAB]; exact Subgroup.mem_top x
  rw [Subgroup.mul_normal] at hx'
  obtain ⟨a, ha, b, hb, rfl⟩ := hx'
  refine ⟨a, ha, b, hb, rfl, fun a' ha' => ?_, fun b' hb' => ?_⟩
  · have h1 : Commute (a * b) a' := (Subgroup.mem_center_iff.mp hx a').symm
    have h2 : Commute b a' := (hc a' ha' b hb).symm
    have h3 : Commute (a * b * b⁻¹) a' := h1.mul_left h2.inv_left
    rw [mul_inv_cancel_right] at h3
    exact h3
  · have h1 : Commute (a * b) b' := (Subgroup.mem_center_iff.mp hx b').symm
    have h2 : Commute a b' := hc a ha b' hb'
    have h3 : Commute (a⁻¹ * (a * b)) b' := h2.inv_left.mul_left h1
    rw [inv_mul_cancel_left] at h3
    exact h3

theorem eq_of_card_eq_two {G : Type*} [Group G] {S : Subgroup G} (hS : Nat.card S = 2) {x y : G}
    (hx : x ∈ S) (hy : y ∈ S) (hx1 : x ≠ 1) (hy1 : y ≠ 1) : x = y := by
  obtain ⟨z, -, hz⟩ := (Nat.card_eq_two_iff' (1 : ↥S)).mp hS
  have h1 := hz ⟨x, hx⟩ (fun h => hx1 (congrArg Subtype.val h))
  have h2 := hz ⟨y, hy⟩ (fun h => hy1 (congrArg Subtype.val h))
  exact congrArg Subtype.val (h1.trans h2.symm)

theorem quaternion_center_facts :
    ∀ q : QuaternionGroup 2, (∀ r : QuaternionGroup 2, q * r = r * q) →
      q = 1 ∨ q = QuaternionGroup.a 2 := by
  decide

theorem zmod_four_involution : ∀ u v : Multiplicative (ZMod 4), u ^ 2 = 1 → v ^ 2 = 1 → u ≠ 1 →
    v ≠ 1 → u = v := by
  decide

theorem mem_of_center_quaternion {R : Type*} [Group R] {A B : Subgroup R}
    (e : ↥B ≃* QuaternionGroup 2) (hAB : Nat.card ↥(A ⊓ B) = 2)
    (hc : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) {b : R} (hb : b ∈ B)
    (hbc : ∀ b' ∈ B, b * b' = b' * b) : b ∈ A := by
  obtain ⟨w, hw1⟩ : ∃ w : ↥(A ⊓ B), w ≠ 1 := by
    obtain ⟨w, hw, -⟩ := (Nat.card_eq_two_iff' (1 : ↥(A ⊓ B))).mp hAB
    exact ⟨w, hw⟩
  have hwc : ∀ r : QuaternionGroup 2, e ⟨w, w.2.2⟩ * r = r * e ⟨w, w.2.2⟩ := by
    intro r
    obtain ⟨b', rfl⟩ := e.surjective r
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hc w w.2.1 b' b'.2)
  have hbc' : ∀ r : QuaternionGroup 2, e ⟨b, hb⟩ * r = r * e ⟨b, hb⟩ := by
    intro r
    obtain ⟨b', rfl⟩ := e.surjective r
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hbc b' b'.2)
  have hw : e ⟨w, w.2.2⟩ ≠ 1 := by
    intro h
    apply hw1
    have h1 := e.injective (h.trans (map_one e).symm)
    have h2 : (w : R) = 1 := by simpa using congrArg Subtype.val h1
    exact Subtype.ext h2
  rcases quaternion_center_facts _ hbc' with h1 | h1
  · have : (⟨b, hb⟩ : ↥B) = 1 := e.injective (by rw [h1, map_one])
    rw [show b = 1 from congrArg Subtype.val this]
    exact A.one_mem
  · rcases quaternion_center_facts _ hwc with h2 | h2
    · exact absurd h2 hw
    · have : (⟨b, hb⟩ : ↥B) = ⟨w, w.2.2⟩ := e.injective (h1.trans h2.symm)
      rw [show b = w from congrArg Subtype.val this]
      exact w.2.1

theorem exists_mul_of_commute_sup {R : Type*} [Group R] {A B : Subgroup R} [B.Normal]
    (hc : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) {x : R} (hxAB : x ∈ A ⊔ B)
    (hx : ∀ y ∈ A ⊔ B, x * y = y * x) :
    ∃ a ∈ A, ∃ b ∈ B, x = a * b ∧ (∀ a' ∈ A, a * a' = a' * a) ∧ ∀ b' ∈ B, b * b' = b' * b := by
  have hx' : x ∈ ((A ⊔ B : Subgroup R) : Set R) := hxAB
  rw [Subgroup.mul_normal] at hx'
  obtain ⟨a, ha, b, hb, rfl⟩ := hx'
  refine ⟨a, ha, b, hb, rfl, fun a' ha' => ?_, fun b' hb' => ?_⟩
  · have h1 : Commute (a * b) a' := hx a' (Subgroup.mem_sup_left ha')
    have h2 : Commute b a' := (hc a' ha' b hb).symm
    have h3 : Commute (a * b * b⁻¹) a' := h1.mul_left h2.inv_left
    rw [mul_inv_cancel_right] at h3
    exact h3
  · have h1 : Commute (a * b) b' := hx b' (Subgroup.mem_sup_right hb')
    have h2 : Commute a b' := hc a ha b' hb'
    have h3 : Commute (a⁻¹ * (a * b)) b' := h2.inv_left.mul_left h1
    rw [inv_mul_cancel_left] at h3
    exact h3

theorem center_le_of_isCentralProduct₂ {R : Type*} [Group R] {A B : Subgroup R}
    (hAB : A ⊔ B = ⊤) (hc : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) (e : ↥B ≃* QuaternionGroup 2)
    (h2 : Nat.card ↥(A ⊓ B) = 2) : Subgroup.center R ≤ A := by
  intro x hx
  have hBn : B.Normal := normal_of_sup_eq_top hAB hc
  obtain ⟨a, ha, b, hb, rfl, -, hbc⟩ := exists_mul_of_commute_sup hc (hAB ▸ Subgroup.mem_top x)
    (fun y _ => (Subgroup.mem_center_iff.mp hx y).symm)
  exact A.mul_mem ha (mem_of_center_quaternion e h2 hc hb hbc)

theorem center_le_of_isCentralProduct₃ {R : Type*} [Group R] {A B C : Subgroup R}
    (hABC : A ⊔ B ⊔ C = ⊤) (hab : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a)
    (hac : ∀ a ∈ A, ∀ c ∈ C, a * c = c * a) (hbc : ∀ b ∈ B, ∀ c ∈ C, b * c = c * b)
    (eB : ↥B ≃* QuaternionGroup 2) (eC : ↥C ≃* QuaternionGroup 2) (hAC : A ⊓ C = A ⊓ B)
    (h2 : Nat.card ↥(A ⊓ B) = 2) : Subgroup.center R ≤ A := by
  intro x hx
  have hABc : ∀ u ∈ A ⊔ B, ∀ c ∈ C, u * c = c * u := by
    intro u hu c hc
    have : A ⊔ B ≤ Subgroup.centralizer (C : Set R) := sup_le
      (fun a ha => Subgroup.mem_centralizer_iff.mpr fun c hc => (hac a ha c hc).symm)
      (fun b hb => Subgroup.mem_centralizer_iff.mpr fun c hc => (hbc b hb c hc).symm)
    exact (Subgroup.mem_centralizer_iff.mp (this hu) c hc).symm
  have hCn : C.Normal := normal_of_sup_eq_top hABC hABc
  obtain ⟨u, hu, c, hc, rfl, huc, hcc⟩ := exists_mul_of_commute_sup hABc
    (hABC ▸ Subgroup.mem_top x) (fun y _ => (Subgroup.mem_center_iff.mp hx y).symm)
  have hcA : c ∈ A := mem_of_center_quaternion eC (by rw [hAC]; exact h2) hac hc hcc
  have hACb : ∀ v ∈ A ⊔ C, ∀ b ∈ B, v * b = b * v := by
    intro v hv b hb
    have : A ⊔ C ≤ Subgroup.centralizer (B : Set R) := sup_le
      (fun a ha => Subgroup.mem_centralizer_iff.mpr fun b hb => (hab a ha b hb).symm)
      (fun c hc => Subgroup.mem_centralizer_iff.mpr fun b hb => hbc b hb c hc)
    exact (Subgroup.mem_centralizer_iff.mp (this hv) b hb).symm
  have hBn : B.Normal := normal_of_sup_eq_top (A := A ⊔ C)
    (by rw [← hABC, sup_assoc, sup_comm C B, ← sup_assoc]) hACb
  obtain ⟨a, ha, b, hb, rfl, -, hbb⟩ := exists_mul_of_commute_sup hab hu huc
  have hbA : b ∈ A := mem_of_center_quaternion eB h2 hab hb hbb
  exact A.mul_mem (A.mul_mem ha hbA) hcA

theorem mem_center_of_mem_centerOf {R : Subgroup D} {x : D} (hx : x ∈ centerOf R) :
    (⟨x, hx.1⟩ : ↥R) ∈ Subgroup.center ↥R :=
  Subgroup.mem_center_iff.mpr fun g =>
    Subtype.ext ((Subgroup.mem_centralizer_iff.mp hx.2) g g.2)

theorem atMostOneInvolution_of_center_le_zmod_four {R : Subgroup D} {A : Subgroup ↥R}
    (hA : Subgroup.center ↥R ≤ A) (e : ↥A ≃* Multiplicative (ZMod 4)) :
    AtMostOneInvolution (centerOf R) := by
  intro x hx y hy hx2 hy2 hx1 hy1
  have hxA := hA (mem_center_of_mem_centerOf hx)
  have hyA := hA (mem_center_of_mem_centerOf hy)
  have hne : ∀ {z : D} (hz : z ∈ R) (hzA : (⟨z, hz⟩ : ↥R) ∈ A), z ≠ 1 →
      e ⟨⟨z, hz⟩, hzA⟩ ≠ 1 := by
    intro z hz hzA hz1 h
    apply hz1
    have := e.injective (h.trans (map_one e).symm)
    simpa using congrArg (fun w : ↥A => ((w : ↥R) : D)) this
  have hsq : ∀ {z : D} (hz : z ∈ R) (hzA : (⟨z, hz⟩ : ↥R) ∈ A), z ^ 2 = 1 →
      e ⟨⟨z, hz⟩, hzA⟩ ^ 2 = 1 := by
    intro z hz hzA hz2
    rw [← map_pow]
    have : (⟨⟨z, hz⟩, hzA⟩ : ↥A) ^ 2 = 1 := Subtype.ext (Subtype.ext (by simpa using hz2))
    rw [this, map_one]
  have := e.injective (zmod_four_involution _ _ (hsq hx.1 hxA hx2) (hsq hy.1 hyA hy2)
    (hne hx.1 hxA hx1) (hne hy.1 hyA hy1))
  simpa using congrArg (fun w : ↥A => ((w : ↥R) : D)) this

theorem atMostOneInvolution_of_isSpecial {R : Subgroup D} (hR : IsSpecialTwoOnePlusFour ↥R) :
    AtMostOneInvolution (centerOf R) := by
  intro x hx y hy _ _ hx1 hy1
  have := eq_of_card_eq_two hR.2.1 (mem_center_of_mem_centerOf hx) (mem_center_of_mem_centerOf hy)
    (fun h => hx1 (congrArg Subtype.val h)) (fun h => hy1 (congrArg Subtype.val h))
  exact congrArg Subtype.val this

theorem atMostOneInvolution_of_z4_q8 {R : Subgroup D}
    (hR : IsCentralProduct₂ ↥R (Multiplicative (ZMod 4)) (QuaternionGroup 2)) :
    AtMostOneInvolution (centerOf R) := by
  obtain ⟨A, B, hAB, hc, ⟨eA⟩, ⟨eB⟩, h2⟩ := hR
  exact atMostOneInvolution_of_center_le_zmod_four (center_le_of_isCentralProduct₂ hAB hc eB h2) eA

theorem atMostOneInvolution_of_q8_q8 {R : Subgroup D}
    (hR : IsCentralProduct₂ ↥R (QuaternionGroup 2) (QuaternionGroup 2)) :
    AtMostOneInvolution (centerOf R) := by
  obtain ⟨A, B, hAB, hc, ⟨eA⟩, ⟨eB⟩, h2⟩ := hR
  have hA := center_le_of_isCentralProduct₂ hAB hc eB h2
  have hB := center_le_of_isCentralProduct₂ (A := B) (B := A) (by rw [sup_comm]; exact hAB)
    (fun b hb a ha => (hc a ha b hb).symm) eA (by rw [inf_comm]; exact h2)
  intro x hx y hy _ _ hx1 hy1
  have hx' := mem_center_of_mem_centerOf hx
  have hy' := mem_center_of_mem_centerOf hy
  have := eq_of_card_eq_two h2 ⟨hA hx', hB hx'⟩ ⟨hA hy', hB hy'⟩
    (fun h => hx1 (congrArg Subtype.val h)) (fun h => hy1 (congrArg Subtype.val h))
  exact congrArg Subtype.val this

theorem atMostOneInvolution_of_z4_q8_q8 {R : Subgroup D}
    (hR : IsCentralProduct₃ ↥R (Multiplicative (ZMod 4)) (QuaternionGroup 2)
      (QuaternionGroup 2)) : AtMostOneInvolution (centerOf R) := by
  obtain ⟨A, B, C, hABC, hab, hac, hbc, ⟨eA⟩, ⟨eB⟩, ⟨eC⟩, hAC, -, h2⟩ := hR
  exact atMostOneInvolution_of_center_le_zmod_four
    (center_le_of_isCentralProduct₃ hABC hab hac hbc eB eC hAC h2) eA

theorem perm_four_centralizer_pair : ∀ a b : Equiv.Perm (Fin 4),
    (a ≠ 1 ∧ b ≠ 1 ∧ a ≠ b ∧ a ^ 2 = 1 ∧ b ^ 2 = 1 ∧ a * b = b * a) →
      ∀ g : Equiv.Perm (Fin 4), (g * a = a * g ∧ g * b = b * g) →
        g = 1 ∨ g = a ∨ g = b ∨ g = a * b := by
  decide

theorem isGoldCaseSp42_of_card_omegaOneCenter [Finite D] {H₁ H₂ : Subgroup D}
    (hG : IsGoldschmidtTriple H₁ H₂) (h : IsGoldCaseVI H₁ H₂) (h₁ : CharTwo H₁)
    (hm : Nat.card ↥(omegaOneCenterOf (H₁ ⊓ H₂)) = 4) : IsGoldCaseSp42 H₁ H₂ := by
  have hZ := centerOf_inf_le_centerOf_pCoreOf hG h₁
  rcases h with ⟨-, -, ⟨e⟩, -⟩ | hS | ⟨-, -, -, -, hR, -⟩ | ⟨-, -, -, -, hR, -⟩ |
    ⟨-, -, -, -, hR, -⟩ | ⟨-, -, -, -, hR, -⟩
  ·
    exfalso
    set Ω := omegaOneCenterOf (H₁ ⊓ H₂)
    obtain ⟨a, ha, ha1⟩ : ∃ a ∈ Ω, a ≠ 1 := by
      by_contra hne
      push Not at hne
      have : Ω = ⊥ := (Subgroup.eq_bot_iff_forall _).mpr hne
      rw [this, Subgroup.card_bot] at hm
      omega
    obtain ⟨b, hb, hb1, hba⟩ : ∃ b ∈ Ω, b ≠ 1 ∧ b ≠ a := by
      by_contra hne
      push Not at hne
      have hsub : (Ω : Set D) ⊆ {1, a} := by
        intro x hx
        by_cases hx1 : x = 1
        · exact Or.inl hx1
        · exact Or.inr (hne x hx hx1)
      have := Set.ncard_le_ncard hsub (Set.toFinite _)
      rw [← Nat.card_coe_set_eq, SetLike.coe_sort_coe] at this
      have h2 : Set.ncard ({1, a} : Set D) ≤ 2 :=
        (Set.ncard_insert_le _ _).trans (by rw [Set.ncard_singleton])
      omega
    have ha' := mem_centerOf_of_mem_omegaOneCenterOf ha
    have hb' := mem_centerOf_of_mem_omegaOneCenterOf hb
    have haH : a ∈ H₁ := ha'.1.1.1
    have hbH : b ∈ H₁ := hb'.1.1.1
    have hcomm : a * b = b * a := (Subgroup.mem_centralizer_iff.mp ha'.1.2 b hb'.1.1).symm
    have hT : ∀ t ∈ H₁ ⊓ H₂, t = 1 ∨ t = a ∨ t = b ∨ t = a * b := by
      intro t ht
      have key := perm_four_centralizer_pair (e ⟨a, haH⟩) (e ⟨b, hbH⟩) ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
        (e ⟨t, ht.1⟩) ⟨?_, ?_⟩
      · rcases key with h1 | h1 | h1 | h1
        · left
          have := e.injective (h1.trans (map_one e).symm)
          simpa using congrArg Subtype.val this
        · right; left
          simpa using congrArg Subtype.val (e.injective h1)
        · right; right; left
          simpa using congrArg Subtype.val (e.injective h1)
        · right; right; right
          have := e.injective (h1.trans (map_mul e _ _).symm)
          simpa using congrArg Subtype.val this
      · intro h1
        exact ha1 (by simpa using congrArg Subtype.val (e.injective (h1.trans (map_one e).symm)))
      · intro h1
        exact hb1 (by simpa using congrArg Subtype.val (e.injective (h1.trans (map_one e).symm)))
      · intro h1
        exact hba (by simpa using congrArg Subtype.val (e.injective h1).symm)
      · rw [← map_pow]
        have : (⟨a, haH⟩ : ↥H₁) ^ 2 = 1 := Subtype.ext (by simpa using ha'.2)
        rw [this, map_one]
      · rw [← map_pow]
        have : (⟨b, hbH⟩ : ↥H₁) ^ 2 = 1 := Subtype.ext (by simpa using hb'.2)
        rw [this, map_one]
      · rw [← map_mul, ← map_mul]
        exact congrArg e (Subtype.ext hcomm)
      · rw [← map_mul, ← map_mul]
        exact congrArg e (Subtype.ext ((Subgroup.mem_centralizer_iff.mp ha'.1.2 t ht)))
      · rw [← map_mul, ← map_mul]
        exact congrArg e (Subtype.ext ((Subgroup.mem_centralizer_iff.mp hb'.1.2 t ht)))
    have hsub : ((H₁ ⊓ H₂ : Subgroup D) : Set D) ⊆ {1, a, b, a * b} := fun t ht => by
      rcases hT t ht with h1 | h1 | h1 | h1 <;> simp [h1]
    have h1 := Set.ncard_le_ncard hsub (Set.toFinite _)
    rw [← Nat.card_coe_set_eq, SetLike.coe_sort_coe] at h1
    have h2 : Set.ncard ({1, a, b, a * b} : Set D) ≤ 4 := by
      refine (Set.ncard_insert_le _ _).trans ?_
      refine (Nat.succ_le_succ (Set.ncard_insert_le _ _)).trans ?_
      refine (Nat.succ_le_succ (Nat.succ_le_succ (Set.ncard_insert_le _ _))).trans ?_
      rw [Set.ncard_singleton]
    have h3 : Nat.card ↥H₁ = 24 := by
      rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, Fintype.card_perm,
        Fintype.card_fin]
      rfl
    have h4 := card_left hG
    omega
  · exact hS
  all_goals exfalso
  · have := card_omegaOneCenterOf_le_two hZ (atMostOneInvolution_of_isSpecial hR)
    omega
  · have := card_omegaOneCenterOf_le_two hZ (atMostOneInvolution_of_z4_q8 hR)
    omega
  · have := card_omegaOneCenterOf_le_two hZ (atMostOneInvolution_of_q8_q8 hR)
    omega
  · have := card_omegaOneCenterOf_le_two hZ (atMostOneInvolution_of_z4_q8_q8 hR)
    omega

theorem card_centerOf (X : Subgroup D) :
    Nat.card ↥(centerOf X) = Nat.card ↥(Subgroup.center ↥X) := by
  have : (Subgroup.center ↥X).map X.subtype = centerOf X := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      refine Subgroup.mem_inf.mpr ⟨y.2, Subgroup.mem_centralizer_iff.mpr fun g hg => ?_⟩
      exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hy ⟨g, hg⟩)
    · intro hx
      exact ⟨⟨x, hx.1⟩, mem_center_of_mem_centerOf hx, rfl⟩
  rw [← this]
  exact Nat.card_congr ((Subgroup.center ↥X).equivMapOfInjective _ X.subtype_injective).symm

theorem card_centerOf_of_mulEquiv {M : Type*} [Group M] {X : Subgroup D} (e : ↥X ≃* M) :
    Nat.card ↥(centerOf X) = Nat.card ↥(Subgroup.center M) := by
  rw [card_centerOf]
  exact Nat.card_congr (Subgroup.centerCongr e).toEquiv

theorem not_centerOf_le_of_card_lt [Finite D] {T H : Subgroup D}
    (h : Nat.card ↥(centerOf H) < Nat.card ↥(centerOf T)) : ¬ centerOf T ≤ centerOf H :=
  fun hle => absurd (Subgroup.card_le_of_le hle) (not_le.mpr h)

section Accessors

variable {H₁ H₂ : Subgroup D}

theorem IsGoldCaseI.card_inf (h : IsGoldCaseI H₁ H₂) : Nat.card ↥(H₁ ⊓ H₂) = 2 := by
  obtain ⟨-, ⟨e⟩, -⟩ := h
  rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card]; rfl

theorem IsGoldCaseII.card_inf (h : IsGoldCaseII H₁ H₂) : Nat.card ↥(H₁ ⊓ H₂) = 4 := by
  obtain ⟨-, ⟨e⟩, -⟩ := h
  rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card]; rfl

theorem IsGoldCaseIII.card_inf (h : IsGoldCaseIII H₁ H₂) : Nat.card ↥(H₁ ⊓ H₂) = 8 := by
  obtain ⟨-, ⟨e⟩, -⟩ := h
  rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card]; rfl

theorem IsGoldCaseIV.card_inf (h : IsGoldCaseIV H₁ H₂) : Nat.card ↥(H₁ ⊓ H₂) = 8 := by
  obtain ⟨-, ⟨e⟩, -⟩ := h
  rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card]; rfl

theorem IsGoldCaseV.card_inf (h : IsGoldCaseV H₁ H₂) : Nat.card ↥(H₁ ⊓ H₂) = 16 := by
  obtain ⟨-, ⟨e⟩, -⟩ := h
  rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card]; rfl

theorem IsGoldCaseI.card_centerOf_inf (h : IsGoldCaseI H₁ H₂) :
    Nat.card ↥(centerOf (H₁ ⊓ H₂)) = 2 := by
  obtain ⟨-, ⟨e⟩, -⟩ := h
  rw [card_centerOf_of_mulEquiv e, Nat.card_eq_fintype_card]; decide

theorem IsGoldCaseII.card_centerOf_inf (h : IsGoldCaseII H₁ H₂) :
    Nat.card ↥(centerOf (H₁ ⊓ H₂)) = 4 := by
  obtain ⟨-, ⟨e⟩, -⟩ := h
  rw [card_centerOf_of_mulEquiv e, Nat.card_eq_fintype_card]; decide

theorem IsGoldCaseIII.card_centerOf_inf (h : IsGoldCaseIII H₁ H₂) :
    Nat.card ↥(centerOf (H₁ ⊓ H₂)) = 2 := by
  obtain ⟨-, ⟨e⟩, -⟩ := h
  rw [card_centerOf_of_mulEquiv e, Nat.card_eq_fintype_card]; decide

theorem IsGoldCaseIV.card_centerOf_inf (h : IsGoldCaseIV H₁ H₂) :
    Nat.card ↥(centerOf (H₁ ⊓ H₂)) = 2 := by
  obtain ⟨-, ⟨e⟩, -⟩ := h
  rw [card_centerOf_of_mulEquiv e, Nat.card_eq_fintype_card]; decide

theorem IsGoldCaseV.card_centerOf_inf (h : IsGoldCaseV H₁ H₂) :
    Nat.card ↥(centerOf (H₁ ⊓ H₂)) = 4 := by
  obtain ⟨-, ⟨e⟩, -⟩ := h
  rw [card_centerOf_of_mulEquiv e, Nat.card_eq_fintype_card]; decide

theorem IsGoldCaseI.not_centerOf_le [Finite D] (h : IsGoldCaseI H₁ H₂) :
    ¬ centerOf (H₁ ⊓ H₂) ≤ centerOf H₁ ∧ ¬ centerOf (H₁ ⊓ H₂) ≤ centerOf H₂ := by
  have hT := h.card_centerOf_inf
  obtain ⟨⟨e₁⟩, -, ⟨e₂⟩⟩ := h
  have h₁ : Nat.card ↥(centerOf H₁) = 1 := by
    rw [card_centerOf_of_mulEquiv e₁, Nat.card_eq_fintype_card]; decide
  have h₂ : Nat.card ↥(centerOf H₂) = 1 := by
    rw [card_centerOf_of_mulEquiv e₂, Nat.card_eq_fintype_card]; decide
  exact ⟨not_centerOf_le_of_card_lt (by omega), not_centerOf_le_of_card_lt (by omega)⟩

theorem IsGoldCaseII.not_centerOf_le [Finite D] (h : IsGoldCaseII H₁ H₂) :
    ¬ centerOf (H₁ ⊓ H₂) ≤ centerOf H₁ ∧ ¬ centerOf (H₁ ⊓ H₂) ≤ centerOf H₂ := by
  have hT := h.card_centerOf_inf
  obtain ⟨⟨e₁⟩, -, ⟨e₂⟩⟩ := h
  have h₁ : Nat.card ↥(centerOf H₁) = 2 := by
    rw [card_centerOf_of_mulEquiv e₁, Nat.card_eq_fintype_card]; decide
  have h₂ : Nat.card ↥(centerOf H₂) = 2 := by
    rw [card_centerOf_of_mulEquiv e₂, Nat.card_eq_fintype_card]; decide
  exact ⟨not_centerOf_le_of_card_lt (by omega), not_centerOf_le_of_card_lt (by omega)⟩

theorem IsGoldCaseIII.not_centerOf_le_right [Finite D] (h : IsGoldCaseIII H₁ H₂) :
    ¬ centerOf (H₁ ⊓ H₂) ≤ centerOf H₂ := by
  have hT := h.card_centerOf_inf
  obtain ⟨-, -, ⟨e₂⟩⟩ := h
  have h₂ : Nat.card ↥(centerOf H₂) = 1 := by
    rw [card_centerOf_of_mulEquiv e₂, Nat.card_eq_fintype_card]; decide
  exact not_centerOf_le_of_card_lt (by omega)

theorem IsGoldCaseIV.not_centerOf_le_left [Finite D] (h : IsGoldCaseIV H₁ H₂) :
    ¬ centerOf (H₁ ⊓ H₂) ≤ centerOf H₁ := by
  have hT := h.card_centerOf_inf
  obtain ⟨⟨e₁⟩, -, -⟩ := h
  have h₁ : Nat.card ↥(centerOf H₁) = 1 := by
    rw [card_centerOf_of_mulEquiv e₁, Nat.card_eq_fintype_card]; decide
  exact not_centerOf_le_of_card_lt (by omega)

theorem IsGoldCaseV.not_centerOf_le [Finite D] (h : IsGoldCaseV H₁ H₂) :
    ¬ centerOf (H₁ ⊓ H₂) ≤ centerOf H₁ ∧ ¬ centerOf (H₁ ⊓ H₂) ≤ centerOf H₂ := by
  have hT := h.card_centerOf_inf
  obtain ⟨⟨e₁⟩, -, ⟨e₂⟩⟩ := h
  have h₁ : Nat.card ↥(centerOf H₁) = 2 := by
    rw [card_centerOf_of_mulEquiv e₁, Nat.card_eq_fintype_card]; decide
  have h₂ : Nat.card ↥(centerOf H₂) = 2 := by
    rw [card_centerOf_of_mulEquiv e₂, Nat.card_eq_fintype_card]; decide
  exact ⟨not_centerOf_le_of_card_lt (by omega), not_centerOf_le_of_card_lt (by omega)⟩

variable [Finite D]

theorem IsGoldCaseL32.card_inf (hG : IsGoldschmidtTriple H₁ H₂) (h : IsGoldCaseL32 H₁ H₂) :
    Nat.card ↥(H₁ ⊓ H₂) = 8 := by
  obtain ⟨-, -, ⟨e⟩, -⟩ := h
  have h1 := card_left hG
  rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card] at h1
  change 24 = _ at h1
  omega

theorem IsGoldCaseSp42.card_inf (hG : IsGoldschmidtTriple H₁ H₂) (h : IsGoldCaseSp42 H₁ H₂) :
    Nat.card ↥(H₁ ⊓ H₂) = 16 := by
  obtain ⟨-, -, ⟨e⟩, -⟩ := h
  have h1 := card_left hG
  rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card] at h1
  change 48 = _ at h1
  omega

theorem IsGoldCaseG22.card_inf (hG : IsGoldschmidtTriple H₁ H₂) (h : IsGoldCaseG22 H₁ H₂) :
    Nat.card ↥(H₁ ⊓ H₂) = 2 ^ 6 := by
  have h1 := card_right hG
  have h2 := card_left_eq_six_mul hG.symm
  rw [h.2.2.2.2.2] at h2
  omega

theorem IsGoldCaseG22Prime.card_inf (hG : IsGoldschmidtTriple H₁ H₂)
    (h : IsGoldCaseG22Prime H₁ H₂) : Nat.card ↥(H₁ ⊓ H₂) = 2 ^ 5 := by
  obtain ⟨-, -, -, -, -, ⟨e⟩⟩ := h
  have h1 := card_right hG
  have h2 := card_left_eq_six_mul hG.symm
  have h3 : Nat.card (Multiplicative (ZMod 4) × Multiplicative (ZMod 4)) = 16 := by
    rw [Nat.card_eq_fintype_card]; rfl
  rw [Nat.card_congr e.toEquiv, h3] at h2
  omega

theorem IsGoldCaseM12.card_inf (hG : IsGoldschmidtTriple H₁ H₂) (h : IsGoldCaseM12 H₁ H₂) :
    Nat.card ↥(H₁ ⊓ H₂) = 2 ^ 6 := by
  have h1 := card_right hG
  have h2 := card_left_eq_six_mul hG.symm
  rw [h.2.2.2.2.2] at h2
  omega

theorem IsGoldCaseAutM12.card_inf (hG : IsGoldschmidtTriple H₁ H₂)
    (h : IsGoldCaseAutM12 H₁ H₂) : Nat.card ↥(H₁ ⊓ H₂) = 2 ^ 7 := by
  have h1 := card_right hG
  have h2 := card_left_eq_six_mul hG.symm
  rw [h.2.2.2.2.2] at h2
  omega

theorem IsGoldCaseL32.not_centerOf_le (hG : IsGoldschmidtTriple H₁ H₂)
    (h : IsGoldCaseL32 H₁ H₂) :
    ¬ centerOf (H₁ ⊓ H₂) ≤ centerOf H₁ ∧ ¬ centerOf (H₁ ⊓ H₂) ≤ centerOf H₂ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hT : 1 < Nat.card ↥(centerOf (H₁ ⊓ H₂)) := by
    rw [card_centerOf]
    have hTn : Nontrivial ↥(H₁ ⊓ H₂) := by
      rw [← Finite.one_lt_card_iff_nontrivial, h.card_inf hG]
      norm_num
    have := hG.isPGroup_inf.center_nontrivial
    exact Finite.one_lt_card_iff_nontrivial.mpr this
  obtain ⟨-, -, ⟨e₁⟩, ⟨e₂⟩⟩ := h
  have h₁ : Nat.card ↥(centerOf H₁) = 1 := by
    rw [card_centerOf_of_mulEquiv e₁, Nat.card_eq_fintype_card]; decide
  have h₂ : Nat.card ↥(centerOf H₂) = 1 := by
    rw [card_centerOf_of_mulEquiv e₂, Nat.card_eq_fintype_card]; decide
  exact ⟨not_centerOf_le_of_card_lt (by omega), not_centerOf_le_of_card_lt (by omega)⟩

theorem card_omegaOneCenterOf_le_two_of_isGoldCase (hG : IsGoldschmidtTriple H₁ H₂)
    (h₁ : CharTwo H₁)
    (h : IsGoldCaseG22 H₁ H₂ ∨ IsGoldCaseG22Prime H₁ H₂ ∨ IsGoldCaseM12 H₁ H₂ ∨
      IsGoldCaseAutM12 H₁ H₂) : Nat.card ↥(omegaOneCenterOf (H₁ ⊓ H₂)) ≤ 2 := by
  have hZ := centerOf_inf_le_centerOf_pCoreOf hG h₁
  rcases h with ⟨-, -, -, -, hR, -⟩ | ⟨-, -, -, -, hR, -⟩ | ⟨-, -, -, -, hR, -⟩ |
    ⟨-, -, -, -, hR, -⟩
  · exact card_omegaOneCenterOf_le_two hZ (atMostOneInvolution_of_isSpecial hR)
  · exact card_omegaOneCenterOf_le_two hZ (atMostOneInvolution_of_z4_q8 hR)
  · exact card_omegaOneCenterOf_le_two hZ (atMostOneInvolution_of_q8_q8 hR)
  · exact card_omegaOneCenterOf_le_two hZ (atMostOneInvolution_of_z4_q8_q8 hR)

end Accessors

end F6

end CFSG.Quasithin
