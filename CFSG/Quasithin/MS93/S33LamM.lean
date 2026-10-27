module

public import CFSG.Quasithin.MS93.S33LamOm
public import CFSG.Quasithin.MS93.S33LamQ
public import CFSG.Quasithin.MS93.S33SpDich
public import CFSG.Quasithin.MS93.M15Lift

public section

namespace CFSG.Quasithin.MS93.S33

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open scoped commutatorElement Matrix IsMulCommutative

variable {G : Type} [Group G]

section Coord

variable {F : Type} [Field F] {A V Z : Subgroup G} {α : ↥A →* MSP.Sp4 F}

@[expose] def natCoordOf (β : ↥V →* Multiplicative (Fin 1 → MSP.V4 F))
    (hβ : Function.Surjective β) (hβker : β.ker = Z.subgroupOf V)
    (hAβ : ∀ a : ↥A, IsCoordAct β a (MSP.mat (α a)).mulVec) : MSP.NatCoord A V Z α where
  toVec :=
    { toFun := fun u => Multiplicative.ofAdd (Multiplicative.toAdd (β u) 0)
      map_one' := by simp
      map_mul' := fun u v => by simp }
  surj := fun w => by
    obtain ⟨u, hu⟩ := hβ (Multiplicative.ofAdd fun _ => Multiplicative.toAdd w)
    exact ⟨u, by simp [hu]⟩
  ker_eq := by
    rw [← hβker]
    ext u
    simp only [MonoidHom.mem_ker, MonoidHom.coe_mk, OneHom.coe_mk]
    constructor
    · intro h1
      apply Multiplicative.toAdd.injective
      funext i
      have hi : i = 0 := Subsingleton.elim _ _
      subst hi
      have := congrArg Multiplicative.toAdd h1
      simpa using this
    · intro h1
      rw [h1]
      rfl
  equiv := fun a u v huv => by
    simpa using hAβ a u v huv

theorem isSumOfNaturalModulesVia_of_coord (hAV : A ≤ Subgroup.normalizer (V : Set G))
    (hZV : Z ≤ V) (β : ↥V →* Multiplicative (Fin 1 → MSP.V4 F)) (hβ : Function.Surjective β)
    (hβker : β.ker = Z.subgroupOf V) (hAβ : ∀ a : ↥A, IsCoordAct β a (MSP.mat (α a)).mulVec) :
    IsSumOfNaturalModulesVia A V Z α false 1 := by
  refine ⟨hAV, hZV, β, hβ, hβker, fun a u v huv i => ?_⟩
  have hi : i = 0 := Subsingleton.elim _ _
  subst hi
  simpa [moduleAct] using hAβ a u v huv

end Coord

section Lam

variable [Finite G] {M T L : Subgroup G} {F : Type} [Field F] [Fintype F] {A : Subgroup G}
  {α : ↥A →* ↥(StatedSp 2 F)} {β : ↥(Uq M T L) →* Multiplicative (Fin 1 → MSP.V4 F)}

omit [Fintype F] in
theorem closure_comm_map_eq (h : PUHyp M T L) (hAM : A ≤ M) {E : Subgroup G} (hEA : E ≤ A) :
    (Subgroup.closure {x : ↥(Uq M T L) | ∃ b ∈ E.subgroupOf A, ∃ v : ↥(Uq M T L),
      (x : G) = (b : G) * v * (b : G)⁻¹ * (v : G)⁻¹}).map (Uq M T L).subtype =
      ⁅Uq M T L, E⁆ := by
  rw [MonoidHom.map_closure, Subgroup.commutator_comm, Subgroup.commutator_def]
  congr 1
  ext g
  constructor
  · rintro ⟨x, ⟨b, hb, v, hx⟩, rfl⟩
    refine ⟨b, Subgroup.mem_subgroupOf.1 hb, v, v.2, ?_⟩
    rw [commutatorElement_def]
    exact hx.symm
  · rintro ⟨e, he, v, hv, rfl⟩
    have hEV : (⟨e, hEA he⟩ : ↥A) ∈ E.subgroupOf A := Subgroup.mem_subgroupOf.2 he
    have hc : ⁅e, v⁆ ∈ Uq M T L := by
      rw [commutatorElement_def]
      exact mul_mem ((Subgroup.mem_normalizer_iff.1
        (le_normalizer_Uq h.le_normalizer (hAM (hEA he))) v).1 hv) (inv_mem hv)
    exact ⟨⟨⁅e, v⁆, hc⟩, ⟨⟨e, hEA he⟩, hEV, ⟨v, hv⟩, commutatorElement_def _ _⟩, rfl⟩

variable (h : PUHyp M T L) (hAM : A ≤ M) (hβ : Function.Surjective β)
  (hβker : β.ker = (Uq M T L ⊓ Zq M L).subgroupOf (Uq M T L))
  (hAβ : ∀ a : ↥A, IsCoordAct β a (MSP.mat (α a)).mulVec)
include h hAM hβ hβker hAβ

omit [Fintype F] in
theorem mem_commSp_iff_crd {E : Subgroup G} (hEA : E ≤ A) (w : MSP.V4 F) :
    w ∈ MSP.commSp ((E.subgroupOf A).map α) ↔
      ∃ u : ↥(Uq M T L), (u : G) ∈ ⁅Uq M T L, E⁆ ∧ Multiplicative.toAdd (β u) 0 = w := by
  have hAV : A ≤ Subgroup.normalizer (Uq M T L : Set G) :=
    hAM.trans (le_normalizer_Uq h.le_normalizer)
  rw [(natCoordOf β hβ hβker hAβ).mem_commSp_iff hAV (E.subgroupOf A) w,
    ← closure_comm_map_eq h hAM hEA]
  refine exists_congr fun u => and_congr ?_ Iff.rfl
  exact (Subgroup.mem_map_iff_mem (Uq M T L).subtype_injective).symm

omit [Fintype F] in
theorem commSp_le_fixSp_of_quadratic {E : Subgroup G} (hEA : E ≤ A)
    (hEab : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x) (hUE : ⁅Uq M T L, E⁆ ≤ E) :
    MSP.commSp ((E.subgroupOf A).map α) ≤ MSP.fixSp ((E.subgroupOf A).map α) := by
  intro w hw
  obtain ⟨u, hu, rfl⟩ := (mem_commSp_iff_crd h hAM hβ hβker hAβ hEA w).1 hw
  rw [MSP.mem_fixSp]
  rintro _ ⟨e, he, rfl⟩
  have heE : (e : G) ∈ E := Subgroup.mem_subgroupOf.1 he
  have hc : (u : G) = e * u * (e : G)⁻¹ := by
    rw [hEab _ heE _ (hUE hu), mul_inv_cancel_right]
  exact (hAβ e u u hc).symm

omit [Fintype F] in
theorem mem_fixer_of_centralizer {E : Subgroup G} (hEA : E ≤ A) {y : ↥A}
    (hy : (y : G) ∈ Subgroup.centralizer ((⁅Uq M T L, E⁆ : Subgroup G) : Set G)) :
    α y ∈ MSP.fixer (MSP.commSp ((E.subgroupOf A).map α)) := by
  intro w hw
  obtain ⟨u, hu, rfl⟩ := (mem_commSp_iff_crd h hAM hβ hβker hAβ hEA w).1 hw
  have hc : (u : G) = y * u * (y : G)⁻¹ := by
    rw [← Subgroup.mem_centralizer_iff.mp hy u hu, mul_inv_cancel_right]
  exact (hAβ y u u hc).symm

omit [Fintype F] in
theorem commutator_le_sup_of_line {E : Subgroup G} (hEA : E ≤ A)
    (hl : MSP.IsLine (MSP.commSp ((E.subgroupOf A).map α))) {Y : Subgroup G} (hYA : Y ≤ A)
    (hYR : Y ≤ Subgroup.centralizer ((⁅Uq M T L, E⁆ : Subgroup G) : Set G)) :
    ⁅Uq M T L, Y⁆ ≤ ⁅Uq M T L, E⁆ ⊔ (Uq M T L ⊓ Zq M L) := by
  rw [Subgroup.commutator_le]
  intro u hu y hy
  have hyV : y * u * y⁻¹ ∈ Uq M T L :=
    (Subgroup.mem_normalizer_iff.1 (le_normalizer_Uq h.le_normalizer (hAM (hYA hy))) u).1 hu
  set c := natCoordOf β hβ hβker hAβ with hc
  have hfix := mem_fixer_of_centralizer h hAM hβ hβker hAβ hEA (y := ⟨y, hYA hy⟩) (hYR hy)
  have hmem : c.vec ⟨y * u * y⁻¹ * u⁻¹, mul_mem hyV (inv_mem hu)⟩ ∈
      MSP.commSp ((E.subgroupOf A).map α) := by
    rw [c.vec_commutator ⟨y, hYA hy⟩ ⟨u, hu⟩ hyV, ← hl.perp_eq]
    exact MSP.sub_mem_perp_of_mem_fixer hfix _
  obtain ⟨r, hr, hrv⟩ := (mem_commSp_iff_crd h hAM hβ hβker hAβ hEA _).1 hmem
  have hz : c.vec (⟨y * u * y⁻¹ * u⁻¹, mul_mem hyV (inv_mem hu)⟩ * r⁻¹) = 0 := by
    rw [c.vec_mul, c.vec_inv, ← hrv]
    exact add_neg_cancel (Multiplicative.toAdd (β r) 0)
  rw [c.vec_eq_zero_iff] at hz
  have e : ⁅u, y⁆ = ((y * u * y⁻¹ * u⁻¹) * (r : G)⁻¹ * r)⁻¹ := by
    rw [inv_mul_cancel_right, commutatorElement_def]
    group
  rw [e]
  refine inv_mem (Subgroup.mul_mem _ (Subgroup.mem_sup_right ?_) (Subgroup.mem_sup_left hr))
  exact hz

omit [Fintype F] in
theorem centralizer_of_eq_one {a : ↥A} (ha : α a = 1) :
    (a : G) ∈ Subgroup.centralizer (Uq M T L : Set G) :=
  centralizer_of_actTriv h ((image_eq_one_iff h hAM (natCoordOf β hβ hβker hAβ) a).1 ha)

theorem le_orthSp_of_not_le [CharP F 2] {k : ℕ} (hk : 1 ≤ k) (hcard : Fintype.card F = 2 ^ k)
    (hLA : L ≤ A) (hα : Function.Surjective α)
    (hCfix : ∀ a ∈ A, ∀ z ∈ Uq M T L ⊓ Zq M L, a * z * a⁻¹ = z) {E : Subgroup G}
    (hnle : ¬ Uq M T L ⊓ Zq M L ≤ ⁅Uq M T L, E⁆) :
    ∃ Q : MSP.V4 F → F, MSP.IsQuadOf Q ∧ (E.subgroupOf A).map α ≤ MSP.orthSp Q := by
  have := Sp4L.isMulCommutative_uq h
  have hAV : A ≤ Subgroup.normalizer (Uq M T L : Set G) :=
    hAM.trans (le_normalizer_Uq h.le_normalizer)
  obtain ⟨π, hπs, hπa⟩ := exists_pi_of_ker hAV hα fun a ha =>
    centralizer_of_eq_one h hAM hβ hβker hAβ ha
  have hnat := isSumOfNaturalModulesVia_of_coord hAV inf_le_left β hβ hβker hAβ
  have hreal := realizesVia_nat_of hAV hα hnat ((hAM.trans (le_normalizer_Uq_inf_Zq h)))
    hπs hπa
  have hZ : (Zq M L).subgroupOf (Uq M T L) ≤ fixV (autOn A (Uq M T L)) := by
    intro z hz x hx
    obtain ⟨g, hgA, rfl⟩ := Setup.mem_autOn_iff.1 hx
    apply Subtype.ext
    rw [InternalSec.coe_conjAct_apply]
    exact hCfix _ hgA _ ⟨z.2, Subgroup.mem_subgroupOf.1 hz⟩
  have hUA : ⁅Uq M T L, A⁆ = Uq M T L :=
    le_antisymm (commutator_le_left_of_le_normalizer hAV)
      (h.commutator_uq.symm.le.trans (Subgroup.commutator_mono le_rfl hLA))
  have hcomm : commV (autOn A (Uq M T L)) = ⊤ := InternalSec.commV_autOn_eq_top hAV hUA
  have hW : ∀ w : ↥(Uq M T L), w ^ 2 = 1 := fun w =>
    Subtype.ext (by simpa using Sp4L.uq_sq h w.2)
  have hFn : Nat.card F = 2 ^ k := by rw [Nat.card_eq_fintype_card, hcard]
  obtain ⟨ψ, hψs, hψe, hψZ⟩ := exists_omega5_quotient hFn hk hW hZ hcomm hreal
  have hZD : ¬ (Zq M L).subgroupOf (Uq M T L) ≤ (⁅Uq M T L, E⁆).subgroupOf (Uq M T L) := by
    intro hle
    apply hnle
    rintro z ⟨hzU, hzZ⟩
    exact Subgroup.mem_subgroupOf.1 (hle (show (⟨z, hzU⟩ : ↥(Uq M T L)) ∈ _ from hzZ))
  obtain ⟨Q, hQ, hQg⟩ := le_orthSp_of_omega5 hW hψs hψe hψZ hZD
  refine ⟨Q, hQ, ?_⟩
  rintro _ ⟨e, he, rfl⟩
  refine hQg _ fun w => ?_
  rw [Subgroup.mem_subgroupOf, Subgroup.coe_mul, hπa, InternalSec.coe_conjAct_apply,
    Subgroup.coe_inv, Subgroup.commutator_comm]
  exact Subgroup.commutator_mem_commutator (Subgroup.mem_subgroupOf.1 he) w.2

theorem lam_core {k : ℕ} (hk : 1 ≤ k) (hcard : Fintype.card F = 2 ^ k) (hLA : L ≤ A)
    (hα : Function.Surjective α)
    (hCfix : ∀ a ∈ A, ∀ z ∈ Uq M T L ⊓ Zq M L, a * z * a⁻¹ = z) {E : Subgroup G} (hEA : E ≤ A)
    (hEab : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x) (hE2 : ∀ x ∈ E, x ^ 2 = 1)
    (hUE : ⁅Uq M T L, E⁆ ≤ E) (hΓq : Fintype.card F ^ 2 ≤ Nat.card ((E.subgroupOf A).map α))
    (hfix : Module.finrank F (MSP.fixSp ((E.subgroupOf A).map α)) ≤ 2) {Y : Subgroup G}
    (hYA : Y ≤ A) (hYR : Y ≤ Subgroup.centralizer ((⁅Uq M T L, E⁆ : Subgroup G) : Set G))
    (hYn : ¬ ⁅Uq M T L, Y⁆ ≤ ⁅Uq M T L, E⁆) :
    Nat.card F = 2 ∧ ∃ p p' : Submodule F (MSP.V4 F), MSP.IsPoint p ∧ MSP.IsPoint p' ∧
      p' ≤ MSP.perp p ∧ (E.subgroupOf A).map α = MSP.xPoint p ⊔ MSP.xPoint p' := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP F 2 := charP_of_card_eq_prime_pow hcard
  set Γ := (E.subgroupOf A).map α with hΓ
  have hΓ2 : IsPGroup 2 Γ := by
    rintro ⟨_, e, he, rfl⟩
    exact ⟨1, Subtype.ext (by rw [pow_one, Subgroup.coe_pow, ← map_pow,
      show e ^ 2 = 1 from Subtype.ext (by simpa using hE2 _ (Subgroup.mem_subgroupOf.1 he)),
      map_one, Subgroup.coe_one])⟩
  have hq := commSp_le_fixSp_of_quadratic h hAM hβ hβker hAβ hEA hEab hUE
  obtain ⟨hl, -, hcf⟩ := line_of_quadratic hΓ2 hq hfix
  have hl' : MSP.IsLine (MSP.commSp Γ) := hcf ▸ hl
  have hsup := commutator_le_sup_of_line h hAM hβ hβker hAβ hEA hl' hYA hYR
  have hnle : ¬ Uq M T L ⊓ Zq M L ≤ ⁅Uq M T L, E⁆ := fun hle =>
    hYn (hsup.trans (sup_le le_rfl hle))
  obtain ⟨Q, hQ, hΓQ⟩ := le_orthSp_of_not_le h hAM hβ hβker hAβ hk hcard hLA hα hCfix hnle
  have hFn : Nat.card F = Fintype.card F := Nat.card_eq_fintype_card
  have hfix2 : Module.finrank F (MSP.fixSp Γ) = 2 := hl.1
  have hcfix : Nat.card (MSP.fixSp Γ) = Fintype.card F ^ 2 := by
    rw [MSP.card_fixSp, hfix2, hFn]
  have h1 : Nat.card (MSP.V4 F) ≤ Nat.card (MSP.fixSp Γ) * Nat.card Γ := by
    rw [MSP.card_V4, hcfix, hFn]
    calc Fintype.card F ^ 4 = Fintype.card F ^ 2 * Fintype.card F ^ 2 := by ring
      _ ≤ _ := Nat.mul_le_mul_left _ hΓq
  have h2 : Nat.card (MSP.V4 F) ≤ Nat.card (MSP.fixSp Γ) * Nat.card F ^ 2 := by
    rw [MSP.card_V4, hcfix, hFn]
    ring_nf
    exact le_rfl
  rcases MSP.eq_bot_or_of_le_orthSp hQ hΓQ hΓ2 h1 h2 with hbot | hpts
  · exfalso
    have hbot' : Γ = ⊥ := hbot
    rw [hbot', Subgroup.card_bot] at hΓq
    have : 1 < Fintype.card F := Fintype.one_lt_card
    nlinarith
  · exact hpts

omit [Fintype F] in
theorem not_map_le {E : Subgroup G} {Y : Subgroup G} (hYA : Y ≤ A)
    (hYn : ¬ ⁅Uq M T L, Y⁆ ≤ ⁅Uq M T L, E⁆) :
    ¬ (Y.subgroupOf A).map α ≤ (E.subgroupOf A).map α := by
  intro hle
  apply hYn
  rw [Subgroup.commutator_le]
  intro u hu y hy
  obtain ⟨e, he, hey⟩ := hle ⟨⟨y, hYA hy⟩, Subgroup.mem_subgroupOf.2 hy, rfl⟩
  have hk : α (e⁻¹ * ⟨y, hYA hy⟩) = 1 := by rw [map_mul, map_inv, hey, inv_mul_cancel]
  have hc := centralizer_of_eq_one h hAM hβ hβker hAβ hk
  have hcu := Subgroup.mem_centralizer_iff.mp hc u hu
  simp only [Subgroup.coe_mul, Subgroup.coe_inv] at hcu
  set k := (e : G)⁻¹ * y with hkdef
  have hku : k * u⁻¹ = u⁻¹ * k := by
    calc k * u⁻¹ = u⁻¹ * (u * k) * u⁻¹ := by group
      _ = u⁻¹ * (k * u) * u⁻¹ := by rw [hcu]
      _ = u⁻¹ * k := by group
  have hy' : y = (e : G) * k := by rw [hkdef]; group
  have e1 : ⁅u, y⁆ = ⁅u, (e : G)⁆ := by
    rw [commutatorElement_def, commutatorElement_def, hy']
    calc u * ((e : G) * k) * u⁻¹ * ((e : G) * k)⁻¹ =
        u * (e : G) * (k * u⁻¹) * k⁻¹ * (e : G)⁻¹ := by group
      _ = u * (e : G) * (u⁻¹ * k) * k⁻¹ * (e : G)⁻¹ := by rw [hku]
      _ = u * (e : G) * u⁻¹ * (e : G)⁻¹ := by group
  rw [e1]
  exact Subgroup.commutator_mem_commutator hu (Subgroup.mem_subgroupOf.1 he)

omit [Fintype F] hβ hβker hAβ in
theorem lam_alt {α₂ : ↥A →* ↥(StatedSp 2 (ZMod 2))}
    {β₂ : ↥(Uq M T L) →* Multiplicative (Fin 1 → MSP.V4 (ZMod 2))} (hβ₂ : Function.Surjective β₂)
    (hβ₂ker : β₂.ker = (Uq M T L ⊓ Zq M L).subgroupOf (Uq M T L))
    (hAβ₂ : ∀ a : ↥A, IsCoordAct β₂ a (MSP.mat (α₂ a)).mulVec)
    (hcomm : ∀ a : ↥A, α₂ a ∈ commutator (MSP.Sp4 (ZMod 2))) {E : Subgroup G} (hEA : E ≤ A)
    (hEab : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x) (hE2 : ∀ x ∈ E, x ^ 2 = 1)
    (hUE : ⁅Uq M T L, E⁆ ≤ E) (hΓq : 4 ≤ Nat.card ((E.subgroupOf A).map α₂))
    (hfix : Module.finrank (ZMod 2) (MSP.fixSp ((E.subgroupOf A).map α₂)) ≤ 2) {Y : Subgroup G}
    (hYA : Y ≤ A) (hYR : Y ≤ Subgroup.centralizer ((⁅Uq M T L, E⁆ : Subgroup G) : Set G))
    (hYn : ¬ ⁅Uq M T L, Y⁆ ≤ ⁅Uq M T L, E⁆) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite (MSP.Sp4 (ZMod 2)) := Subtype.finite
  set Γ := (E.subgroupOf A).map α₂ with hΓ
  set Yb := (Y.subgroupOf A).map α₂ with hYb
  have hΓ2 : IsPGroup 2 Γ := by
    rintro ⟨_, e, he, rfl⟩
    exact ⟨1, Subtype.ext (by rw [pow_one, Subgroup.coe_pow, ← map_pow,
      show e ^ 2 = 1 from Subtype.ext (by simpa using hE2 _ (Subgroup.mem_subgroupOf.1 he)),
      map_one, Subgroup.coe_one])⟩
  have hq := commSp_le_fixSp_of_quadratic h hAM hβ₂ hβ₂ker hAβ₂ hEA hEab hUE
  obtain ⟨hl, hΓl, hcf⟩ := line_of_quadratic hΓ2 hq hfix
  have hYbl : Yb ≤ MSP.qLine (MSP.fixSp Γ) := by
    rintro _ ⟨y, hy, rfl⟩
    have := mem_fixer_of_centralizer h hAM hβ₂ hβ₂ker hAβ₂ hEA (y := y)
      (hYR (Subgroup.mem_subgroupOf.1 hy))
    rwa [hcf] at this
  have hsub : Γ ⊔ Yb ≤ MSP.qLine (MSP.fixSp Γ) ⊓ commutator (MSP.Sp4 (ZMod 2)) := by
    refine sup_le (le_inf hΓl ?_) (le_inf hYbl ?_)
    · rintro _ ⟨e, -, rfl⟩
      exact hcomm e
    · rintro _ ⟨y, -, rfl⟩
      exact hcomm y
  have h4 := (Subgroup.card_le_of_le hsub).trans (card_qLine_inf_commutator_le hl)
  have hne : Γ ≠ Γ ⊔ Yb := fun heq =>
    not_map_le h hAM hβ₂ hβ₂ker hAβ₂ hYA hYn (by show Yb ≤ Γ; rw [heq]; exact le_sup_right)
  have hd : Nat.card Γ ∣ Nat.card ↥(Γ ⊔ Yb) := Subgroup.card_dvd_of_le le_sup_left
  have hcne : Nat.card Γ ≠ Nat.card ↥(Γ ⊔ Yb) := fun hc =>
    hne (Subgroup.eq_of_le_of_card_ge le_sup_left hc.ge)
  obtain ⟨c, hc⟩ := hd
  have hc1 : c ≠ 1 := fun h1 => hcne (by rw [hc, h1, mul_one])
  have hc0 : c ≠ 0 := fun h0 => by
    rw [h0, mul_zero] at hc
    exact absurd hc (Nat.card_pos (α := ↥(Γ ⊔ Yb))).ne'
  have : 2 ≤ c := by omega
  have : 8 ≤ Nat.card ↥(Γ ⊔ Yb) := by rw [hc]; nlinarith
  omega

end Lam

end CFSG.Quasithin.MS93.S33
