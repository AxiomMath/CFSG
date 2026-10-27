module

public import CFSG.GroupTheory.LocalCores.Layer
public import CFSG.RankThree.GF2n.Stroth80.Sec4Alg
public import CFSG.Walter.AStar.Subnormal

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75
open scoped commutatorElement

@[expose] def CompSimple (Γ : Type) [Group Γ] : Prop :=
  ∀ C : Subgroup Γ, IsComponent C → Subgroup.center ↥C = ⊥

section Basic

variable {Γ : Type} [Group Γ]

theorem isComponent_conjSubgroup (g : Γ) {Y : Subgroup Γ} (hY : IsComponent Y) :
    IsComponent (conjSubgroup g Y) :=
  CFSG.LocalCores.isComponent_map_mulEquiv (MulAut.conj g) hY

theorem isSimpleGroup_of_center_eq_bot {C : Subgroup Γ} (hC : IsComponent C)
    (h : Subgroup.center ↥C = ⊥) : IsSimpleGroup ↥C := by
  obtain ⟨-, hs, -⟩ := hC.1
  have e : (↥C ⧸ Subgroup.center ↥C) ≃* ↥C :=
    (QuotientGroup.quotientMulEquivOfEq h).trans QuotientGroup.quotientBot
  exact (MulEquiv.isSimpleGroup_congr e).mp hs

theorem exists_noncomm_of_isComponent {C : Subgroup Γ} (hC : IsComponent C) :
    ∃ a b : ↥C, a * b ≠ b * a := by
  obtain ⟨-, -, a, b, hab⟩ := hC.1
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
  obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b
  refine ⟨a, b, fun h => hab ?_⟩
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, h]

theorem ne_bot_of_isComponent {Γ : Type} [Group Γ] {C : Subgroup Γ} (hC : IsComponent C) :
    C ≠ ⊥ := by
  intro h
  obtain ⟨a, b, hab⟩ := exists_noncomm_of_isComponent hC
  apply hab
  have ha : (a : Γ) = 1 := Subgroup.mem_bot.mp (h ▸ a.2)
  apply Subtype.ext
  show (a : Γ) * b = b * a
  rw [ha, one_mul, mul_one]

variable [Finite Γ]

theorem comm_of_ne_component {C D : Subgroup Γ} (hC : IsComponent C) (hD : IsComponent D)
    (hne : C ≠ D) : ∀ x ∈ C, ∀ y ∈ D, x * y = y * x := by
  have h1 : ⁅C, D⁆ = ⊥ := (CFSG.LocalCores.distinct_components_commute hC hD).resolve_left hne
  intro x hx y hy
  have h2 : ⁅x, y⁆ ∈ (⊥ : Subgroup Γ) := h1 ▸ Subgroup.commutator_mem_commutator hx hy
  rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at h2
  exact h2

theorem CompSimple.inf_eq_bot {Γ : Type} [Group Γ] [Finite Γ] (h : CompSimple Γ) {C D : Subgroup Γ}
    (hC : IsComponent C) (hD : IsComponent D) (hne : C ≠ D) : C ⊓ D = ⊥ := by
  rw [eq_bot_iff]
  rintro x ⟨hxC, hxD⟩
  have hz : (⟨x, hxC⟩ : ↥C) ∈ Subgroup.center ↥C := by
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (comm_of_ne_component hC hD hne g g.2 x hxD)
  rw [h C hC, Subgroup.mem_bot] at hz
  exact Subgroup.mem_bot.mpr (congrArg Subtype.val hz)

theorem CompSimple.le_of_inf_ne_bot (h : CompSimple Γ) {C N : Subgroup Γ} (hC : IsComponent C)
    (hN : ∀ c ∈ C, ∀ n ∈ N, c * n * c⁻¹ ∈ N) (h0 : N ⊓ C ≠ ⊥) : C ≤ N := by
  haveI := isSimpleGroup_of_center_eq_bot hC (h C hC)
  have hnorm : ((N ⊓ C).subgroupOf C).Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    exact ⟨hN g g.2 n hn.1, C.mul_mem (C.mul_mem g.2 hn.2) (C.inv_mem g.2)⟩
  rcases hnorm.eq_bot_or_eq_top with hb | ht
  · exfalso
    apply h0
    rw [eq_bot_iff]
    intro x hx
    have hx' : (⟨x, hx.2⟩ : ↥C) ∈ (N ⊓ C).subgroupOf C := hx
    rw [hb, Subgroup.mem_bot] at hx'
    exact Subgroup.mem_bot.mpr (congrArg Subtype.val hx')
  · intro x hx
    have : (⟨x, hx⟩ : ↥C) ∈ (N ⊓ C).subgroupOf C := by rw [ht]; exact Subgroup.mem_top _
    exact (Subgroup.mem_subgroupOf.mp this).1


theorem CompSimple.eq_one_of_commutes (h : CompSimple Γ) {C : Subgroup Γ} (hC : IsComponent C)
    {a : Γ} (ha : a ∈ C) (hcomm : ∀ y ∈ C, y * a = a * y) : a = 1 := by
  have hz : (⟨a, ha⟩ : ↥C) ∈ Subgroup.center ↥C := by
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (hcomm g g.2)
  rw [h C hC, Subgroup.mem_bot] at hz
  exact congrArg Subtype.val hz

theorem CompSimple.le_of_mul_mem_of_comm (h : CompSimple Γ) {C N : Subgroup Γ}
    (hC : IsComponent C) (hN : ∀ c ∈ C, ∀ n ∈ N, c * n * c⁻¹ ∈ N) {a b : Γ} (ha : a ∈ C)
    (hb : ∀ c ∈ C, c * b = b * c) (hab : a * b ∈ N) (ha1 : a ≠ 1) : C ≤ N := by
  apply h.le_of_inf_ne_bot hC hN
  intro h0
  have hcomm : ∀ c ∈ C, c * a * c⁻¹ * a⁻¹ = 1 := by
    intro c hc
    have hx : c * a * c⁻¹ * a⁻¹ ∈ N ⊓ C := by
      refine ⟨?_, C.mul_mem (C.mul_mem (C.mul_mem hc ha) (C.inv_mem hc)) (C.inv_mem ha)⟩
      have h1 := N.mul_mem (hN c hc _ hab) (N.inv_mem hab)
      have hcb : c * b = b * c := hb c hc
      have e : c * (a * b) * c⁻¹ * (a * b)⁻¹ = c * a * c⁻¹ * a⁻¹ := by
        have hbc : b * c⁻¹ = c⁻¹ * b := by
          calc b * c⁻¹ = c⁻¹ * (c * b) * c⁻¹ := by group
            _ = c⁻¹ * (b * c) * c⁻¹ := by rw [hcb]
            _ = c⁻¹ * b := by group
        calc c * (a * b) * c⁻¹ * (a * b)⁻¹ = c * a * (b * c⁻¹) * b⁻¹ * a⁻¹ := by group
          _ = c * a * (c⁻¹ * b) * b⁻¹ * a⁻¹ := by rw [hbc]
          _ = c * a * c⁻¹ * a⁻¹ := by group
      rwa [e] at h1
    rw [h0, Subgroup.mem_bot] at hx
    exact hx
  exact ha1 (h.eq_one_of_commutes hC ha fun y hy => by
    have h1 := hcomm y hy
    calc y * a = (y * a * y⁻¹ * a⁻¹) * (a * y) := by group
      _ = a * y := by rw [h1, one_mul])

theorem CompSimple.le_of_mul_mem (h : CompSimple Γ) {C D N : Subgroup Γ} (hC : IsComponent C)
    (hD : IsComponent D) (hne : C ≠ D) (hN : ∀ c ∈ C, ∀ n ∈ N, c * n * c⁻¹ ∈ N) {a b : Γ}
    (ha : a ∈ C) (hb : b ∈ D) (hab : a * b ∈ N) (ha1 : a ≠ 1) : C ≤ N :=
  h.le_of_mul_mem_of_comm hC hN ha (fun c hc => comm_of_ne_component hC hD hne c hc b hb) hab ha1

theorem exists_mul_of_mem_sup_of_commute {C D : Subgroup Γ}
    (hcomm : ∀ x ∈ C, ∀ y ∈ D, x * y = y * x) {x : Γ} (hx : x ∈ C ⊔ D) :
    ∃ a ∈ C, ∃ b ∈ D, x = a * b := by
  let S : Subgroup Γ :=
    { carrier := {x | ∃ a ∈ C, ∃ b ∈ D, x = a * b}
      one_mem' := ⟨1, C.one_mem, 1, D.one_mem, (one_mul 1).symm⟩
      mul_mem' := by
        rintro _ _ ⟨a, ha, b, hb, rfl⟩ ⟨a', ha', b', hb', rfl⟩
        refine ⟨a * a', C.mul_mem ha ha', b * b', D.mul_mem hb hb', ?_⟩
        have : b * a' = a' * b := (hcomm a' ha' b hb).symm
        calc a * b * (a' * b') = a * (b * a') * b' := by group
          _ = a * (a' * b) * b' := by rw [this]
          _ = a * a' * (b * b') := by group
      inv_mem' := by
        rintro _ ⟨a, ha, b, hb, rfl⟩
        refine ⟨a⁻¹, C.inv_mem ha, b⁻¹, D.inv_mem hb, ?_⟩
        have : b * a = a * b := (hcomm a ha b hb).symm
        calc (a * b)⁻¹ = (b * a)⁻¹ := by rw [this]
          _ = a⁻¹ * b⁻¹ := by group }
  have hle : C ⊔ D ≤ S := sup_le (fun a ha => ⟨a, ha, 1, D.one_mem, (mul_one a).symm⟩)
    (fun b hb => ⟨1, C.one_mem, b, hb, (one_mul b).symm⟩)
  exact hle hx


theorem CompSimple.sup_inf_sup_eq_bot (h : CompSimple Γ) {C₁ C₂ C₃ C₄ : Subgroup Γ}
    (h₁ : IsComponent C₁) (h₂ : IsComponent C₂) (h₃ : IsComponent C₃) (h₄ : IsComponent C₄)
    (h12 : C₁ ≠ C₂) (h13 : C₁ ≠ C₃) (h14 : C₁ ≠ C₄) (h23 : C₂ ≠ C₃) (h24 : C₂ ≠ C₄)
    (h34 : C₃ ≠ C₄) : (C₁ ⊔ C₂) ⊓ (C₃ ⊔ C₄) = ⊥ := by
  rw [eq_bot_iff]
  rintro x ⟨hx12, hx34⟩
  obtain ⟨a, ha, b, hb, rfl⟩ := exists_mul_of_mem_sup_of_commute
    (comm_of_ne_component h₁ h₂ h12) hx12
  obtain ⟨a', ha', b', hb', hab⟩ := exists_mul_of_mem_sup_of_commute
    (comm_of_ne_component h₃ h₄ h34) hx34
  have ha1 : a = 1 := by
    refine h.eq_one_of_commutes h₁ ha fun y hy => ?_
    have e : a = a' * b' * b⁻¹ := by rw [← hab]; group
    have c3 := comm_of_ne_component h₁ h₃ h13 y hy a' ha'
    have c4 := comm_of_ne_component h₁ h₄ h14 y hy b' hb'
    have c2 := comm_of_ne_component h₁ h₂ h12 y hy b⁻¹ (C₂.inv_mem hb)
    rw [e]
    calc y * (a' * b' * b⁻¹) = (y * a') * b' * b⁻¹ := by group
      _ = (a' * y) * b' * b⁻¹ := by rw [c3]
      _ = a' * (y * b') * b⁻¹ := by group
      _ = a' * (b' * y) * b⁻¹ := by rw [c4]
      _ = a' * b' * (y * b⁻¹) := by group
      _ = a' * b' * (b⁻¹ * y) := by rw [c2]
      _ = a' * b' * b⁻¹ * y := by group
  have hb1 : b = 1 := by
    refine h.eq_one_of_commutes h₂ hb fun y hy => ?_
    have e : b = a⁻¹ * (a' * b') := by rw [← hab]; group
    have c1 := comm_of_ne_component h₁ h₂ h12 a⁻¹ (C₁.inv_mem ha) y hy
    have c3 := comm_of_ne_component h₂ h₃ h23 y hy a' ha'
    have c4 := comm_of_ne_component h₂ h₄ h24 y hy b' hb'
    rw [e]
    calc y * (a⁻¹ * (a' * b')) = (y * a⁻¹) * (a' * b') := by group
      _ = (a⁻¹ * y) * (a' * b') := by rw [← c1]
      _ = a⁻¹ * ((y * a') * b') := by group
      _ = a⁻¹ * ((a' * y) * b') := by rw [c3]
      _ = a⁻¹ * (a' * (y * b')) := by group
      _ = a⁻¹ * (a' * (b' * y)) := by rw [c4]
      _ = a⁻¹ * (a' * b') * y := by group
  rw [ha1, hb1]
  simp


theorem normalClosure_subgroupOf_eq_top_of_forall {X S : Subgroup Γ} (hSX : S ≤ X)
    (h : ∀ N : Subgroup Γ, (∀ c ∈ X, ∀ n ∈ N, c * n * c⁻¹ ∈ N) → S ≤ N → X ≤ N) :
    Subgroup.normalClosure ((S.subgroupOf X : Subgroup ↥X) : Set ↥X) = ⊤ := by
  set NC := Subgroup.normalClosure ((S.subgroupOf X : Subgroup ↥X) : Set ↥X) with hNC
  have hnorm : NC.Normal := Subgroup.normalClosure_normal
  have hX : X ≤ NC.map X.subtype := by
    refine h (NC.map X.subtype) ?_ ?_
    · rintro c hc _ ⟨m, hm, rfl⟩
      exact ⟨⟨c, hc⟩ * m * ⟨c, hc⟩⁻¹, hnorm.conj_mem m hm ⟨c, hc⟩, by simp⟩
    · intro x hx
      exact ⟨⟨x, hSX hx⟩, Subgroup.subset_normalClosure (show (⟨x, hSX hx⟩ : ↥X) ∈
        (S.subgroupOf X : Set ↥X) from hx), rfl⟩
  rw [eq_top_iff]
  intro x _
  obtain ⟨m, hm, hmx⟩ := hX x.2
  have : m = x := Subtype.ext hmx
  rwa [this] at hm


theorem sup_le_normalizer_of_commute {C D : Subgroup Γ}
    (hcomm : ∀ x ∈ C, ∀ y ∈ D, x * y = y * x) :
    C ⊔ D ≤ Subgroup.normalizer (C : Set Γ) := by
  refine sup_le Subgroup.le_normalizer fun d hd => Subgroup.mem_normalizer_fintype fun y hy => ?_
  have h : d * y * d⁻¹ = y := by
    rw [mul_inv_eq_iff_eq_mul]
    exact (hcomm y hy d hd).symm
  rw [h]
  exact hy


theorem le_of_inf_ne_bot_of_simple {X N : Subgroup Γ} [IsSimpleGroup ↥X]
    (hN : ∀ c ∈ X, ∀ n ∈ N, c * n * c⁻¹ ∈ N) (h0 : N ⊓ X ≠ ⊥) : X ≤ N := by
  have hnorm : ((N ⊓ X).subgroupOf X).Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    exact ⟨hN g g.2 n hn.1, X.mul_mem (X.mul_mem g.2 hn.2) (X.inv_mem g.2)⟩
  rcases hnorm.eq_bot_or_eq_top with hb | ht
  · exfalso
    apply h0
    rw [eq_bot_iff]
    intro x hx
    have hx' : (⟨x, hx.2⟩ : ↥X) ∈ (N ⊓ X).subgroupOf X := hx
    rw [hb, Subgroup.mem_bot] at hx'
    exact Subgroup.mem_bot.mpr (congrArg Subtype.val hx')
  · intro x hx
    have : (⟨x, hx⟩ : ↥X) ∈ (N ⊓ X).subgroupOf X := by rw [ht]; exact Subgroup.mem_top _
    exact (Subgroup.mem_subgroupOf.mp this).1

end Basic

section Sylow

theorem exists_conj_mem_sylow_of_isSubnormal {Γ : Type} [Group Γ] [Finite Γ] (S : Sylow 2 Γ)
    {Y : Subgroup Γ} (hY : Y.IsSubnormal) {y : Γ} (hy : y ∈ Y) (hy2 : ∃ k : ℕ, y ^ 2 ^ k = 1) :
    ∃ g ∈ Y, g⁻¹ * y * g ∈ (S : Subgroup Γ) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P, hP⟩ := CFSG.Walter.exists_sylow_map_eq_inf_of_isSubnormal S hY
  obtain ⟨k, hk⟩ := hy2
  obtain ⟨z, hz⟩ : ∃ z : Y, (z : Γ) = y := ⟨⟨y, hy⟩, rfl⟩
  have hzk : z ^ 2 ^ k = 1 := Subtype.ext (by simp [hz, hk])
  have hzp : IsPGroup 2 (Subgroup.zpowers z) :=
    IsPGroup.of_card_dvd_pow (n := k) (by
      rw [Nat.card_zpowers]
      exact orderOf_dvd_of_pow_eq_one hzk)
  obtain ⟨Q, hQ⟩ := hzp.exists_le_sylow
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq Y P Q
  subst hc
  have hzQ : z ∈ ((c • P : Sylow 2 Y) : Subgroup Y) := hQ (Subgroup.mem_zpowers z)
  rw [Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hzQ
  have hmem : c⁻¹ * z * c ∈ (P : Subgroup Y) := by
    simpa [MulAut.smul_def] using hzQ
  have h1 : Y.subtype (c⁻¹ * z * c) ∈ (P : Subgroup Y).map Y.subtype :=
    Subgroup.mem_map_of_mem Y.subtype hmem
  rw [hP] at h1
  refine ⟨(c : Γ), c.2, ?_⟩
  have e : Y.subtype (c⁻¹ * z * c) = (c : Γ)⁻¹ * y * (c : Γ) := by
    simp [hz]
  rw [← e]
  exact (Subgroup.mem_inf.mp h1).1

end Sylow

section LemmaA

variable {Γ : Type} [Group Γ] [Finite Γ]

theorem component_le_of_not_centralizes {M₀ : Subgroup Γ} (hM₀ : M₀.Normal)
    (hno : ∀ X : Subgroup Γ, CFSG.IsQuasisimple ↥X → ¬ ∀ x ∈ X, ∀ m ∈ M₀, x * m = m * x)
    {C : Subgroup Γ} (hC : IsComponent C) : C ≤ M₀ := by
  rcases CFSG.LocalCores.component_normal_subgroup hC hM₀ with h | h
  · exact h
  · exfalso
    refine hno C hC.1 fun x hx m hm => ?_
    have h2 : ⁅x, m⁆ ∈ (⊥ : Subgroup Γ) := h ▸ Subgroup.commutator_mem_commutator hx hm
    rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at h2
    exact h2

theorem layer_le_of_not_centralizes {M₀ : Subgroup Γ} (hM₀ : M₀.Normal)
    (hno : ∀ X : Subgroup Γ, CFSG.IsQuasisimple ↥X → ¬ ∀ x ∈ X, ∀ m ∈ M₀, x * m = m * x) :
    layer Γ ≤ M₀ :=
  sSup_le fun _ hC => component_le_of_not_centralizes hM₀ hno hC

theorem compSimple_of_odd (hΓ : CFSG.pCore 2 Γ = ⊥) {Λ M₀ : Subgroup Γ} (hM₀ : M₀.Normal)
    (hΛ : Λ ≤ M₀)
    (hno : ∀ X : Subgroup Γ, CFSG.IsQuasisimple ↥X → ¬ ∀ x ∈ X, ∀ m ∈ M₀, x * m = m * x)
    (hodd : ∀ A : Subgroup Γ, A ≤ M₀ → Λ ≤ Subgroup.normalizer (A : Set Γ) →
      Odd (Nat.card A) → A = ⊥) : CompSimple Γ := by
  have hlay := CFSG.LocalCores.layer_characteristic (G := Γ)
  have hA : ((Subgroup.center (layer Γ)).map (layer Γ).subtype).Normal :=
    ConjAct.normal_of_characteristic_of_normal
  haveI := hA
  haveI : Group.IsNilpotent ((Subgroup.center (layer Γ)).map (layer Γ).subtype) :=
    (Group.isNilpotent_congr ((Subgroup.center (layer Γ)).equivMapOfInjective
      (layer Γ).subtype (layer Γ).subtype_injective)).mp inferInstance
  have hodd' : Odd (Nat.card ((Subgroup.center (layer Γ)).map (layer Γ).subtype)) :=
    odd_card_of_normal_nilpotent hΓ _
  have hA0 : (Subgroup.center (layer Γ)).map (layer Γ).subtype = ⊥ :=
    hodd _ ((Subgroup.map_subtype_le _).trans (layer_le_of_not_centralizes hM₀ hno))
      (fun x _ => by rw [Subgroup.normalizer_eq_top_iff.mpr hA]; exact Subgroup.mem_top x) hodd'
  intro C hC
  have h1 := (CFSG.LocalCores.layer_center (G := Γ)).2 C hC
  rw [hA0, inf_bot_eq] at h1
  rw [eq_bot_iff]
  intro z hz
  have hz' : (z : Γ) ∈ (Subgroup.center ↥C).map C.subtype := ⟨z, hz, rfl⟩
  rw [← h1] at hz'
  exact Subgroup.mem_bot.mpr (Subtype.ext (Subgroup.mem_bot.mp hz'))


theorem CompSimple.center_layer_eq_bot (h : CompSimple Γ) :
    (Subgroup.center (layer Γ)).map (layer Γ).subtype = ⊥ := by
  rw [(CFSG.LocalCores.layer_center (G := Γ)).1]
  refine iSup_eq_bot.mpr fun K => ?_
  rw [h K.1 K.2]
  exact Subgroup.map_bot _

theorem CompSimple.eq_one_of_comm_components (h : CompSimple Γ) {x : Γ} (hx : x ∈ layer Γ)
    (hcomm : ∀ C : Subgroup Γ, IsComponent C → ∀ c ∈ C, c * x = x * c) : x = 1 := by
  have hle : layer Γ ≤ Subgroup.centralizer ({x} : Set Γ) := by
    refine sSup_le fun C hC c hc => ?_
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact hcomm C hC c hc
  have hz : (⟨x, hx⟩ : ↥(layer Γ)) ∈ Subgroup.center ↥(layer Γ) := by
    rw [Subgroup.mem_center_iff]
    intro g
    have := Subgroup.mem_centralizer_singleton_iff.mp (hle g.2)
    exact Subtype.ext this
  have h1 : x ∈ (Subgroup.center (layer Γ)).map (layer Γ).subtype := ⟨_, hz, rfl⟩
  rw [h.center_layer_eq_bot, Subgroup.mem_bot] at h1
  exact h1

end LemmaA

end CFSG.RankThree.GF2n.Stroth80
