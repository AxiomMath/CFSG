module

public import CFSG.Quasithin.Recognition.St84.Gen.NatSecDefs
public import CFSG.CGT.Timmesfeld75.L2Basic
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionSquareFieldUnipotent
public import CFSG.ClassicalGroups.PCoreSection
public import CFSG.Quasithin.Background.F1Hyp

public section

namespace CFSG.Quasithin.F112R.St84

open Matrix CFSG.Open CFSG.Quasithin CFSG.Quasithin.F1 CFSG.QuasithinUnique
open CFSG.ClassicalGroups.PCoreSection CFSG.LieType.BorelTits CFSG.CGT.Timmesfeld75
open CFSG.ProperTwoGeneratedCore.LocalCriterionSquareField
open scoped MatrixGroups

section SL2

variable {F : Type} [Field F]

theorem mem_utri_iff_eq_unitri {g : SL(2, F)} :
    g ∈ utri F ↔ ∃ t : F, (g : Matrix (Fin 2) (Fin 2) F) = !![1, t; 0, 1] := by
  constructor
  · intro hg
    obtain ⟨h10, h00⟩ := mem_utri_entries.mp hg
    have hd := sl2_det g
    rw [h00, h10] at hd
    have h11 : g 1 1 = 1 := by linear_combination hd
    refine ⟨g 0 1, ?_⟩
    ext i j
    fin_cases i <;> fin_cases j <;> simp [h00, h10, h11]
  · rintro ⟨t, ht⟩
    refine mem_utri_entries.mpr ⟨?_, ?_⟩
    · change (g : Matrix (Fin 2) (Fin 2) F) 1 0 = 0
      rw [ht]
      simp
    · change (g : Matrix (Fin 2) (Fin 2) F) 0 0 = 1
      rw [ht]
      simp

theorem eq_utriElt_of_eq_unitri {g : SL(2, F)} {t : F}
    (h : (g : Matrix (Fin 2) (Fin 2) F) = !![1, t; 0, 1]) : g = utriElt t := by
  refine sl2_ext ?_ ?_ ?_ ?_
  · rw [utriElt_apply_00]
    change (g : Matrix (Fin 2) (Fin 2) F) 0 0 = 1
    rw [h]
    simp
  · rw [utriElt_apply_01]
    change (g : Matrix (Fin 2) (Fin 2) F) 0 1 = t
    rw [h]
    simp
  · rw [utriElt_apply_10]
    change (g : Matrix (Fin 2) (Fin 2) F) 1 0 = 0
    rw [h]
    simp
  · rw [utriElt_apply_11]
    change (g : Matrix (Fin 2) (Fin 2) F) 1 1 = 1
    rw [h]
    simp

theorem borel_commutator_mem_utri {g h : SL(2, F)} (hg : g ∈ borel F) (hh : h ∈ borel F) :
    g * h * g⁻¹ * h⁻¹ ∈ utri F := by
  have hg' : g 1 0 = 0 := mem_borel_iff.mp hg
  have hh' : h 1 0 = 0 := mem_borel_iff.mp hh
  have dg := sl2_det g
  have dh := sl2_det h
  rw [hg'] at dg
  rw [hh'] at dh
  refine mem_utri_entries.mpr ⟨?_, ?_⟩
  · exact mem_borel_iff.mp (mul_mem (mul_mem (mul_mem hg hh) (inv_mem hg)) (inv_mem hh))
  · sl2_simp
    rw [hg', hh']
    linear_combination (h 0 0 * h 1 1) * dg + dh

end SL2

section Coord

variable {G : Type*} [Group G] {L S : Subgroup G} {F : Type} [Field F]

theorem alpha_mem_borel_of_conj_mem (α : ↥L →* SL(2, F)) (hα : Function.Surjective α)
    (hmem : ∀ x : ↥L, (x : G) ∈ S ↔ α x ∈ utri F) {d : ↥L}
    (hd : ∀ s ∈ S, (d : G) * s * (d : G)⁻¹ ∈ S) : α d ∈ borel F := by
  obtain ⟨s₁, hs₁⟩ := hα (utriElt 1)
  have hs₁S : (s₁ : G) ∈ S := (hmem s₁).mpr (by rw [hs₁]; exact utriElt_mem_utri 1)
  have hU : α (d * s₁ * d⁻¹) ∈ utri F := (hmem _).mp (hd _ hs₁S)
  rw [map_mul, map_mul, map_inv, hs₁] at hU
  have h10 := (mem_utri_entries.mp hU).1
  rw [conj_utriElt_apply_10, mul_one] at h10
  have h2 : (α d) 1 0 ^ 2 = 0 := by linear_combination (-1 : F) * h10
  exact mem_borel_iff.mpr ((pow_eq_zero_iff two_ne_zero).mp h2)

theorem conj_mem_of_alpha_mem_borel (hSL : S ≤ L) (α : ↥L →* SL(2, F))
    (hmem : ∀ x : ↥L, (x : G) ∈ S ↔ α x ∈ utri F) {x : ↥L} (hx : α x ∈ borel F) {s : G}
    (hs : s ∈ S) : (x : G) * s * (x : G)⁻¹ ∈ S :=
  (hmem (x * ⟨s, hSL hs⟩ * x⁻¹)).mpr (by
    rw [map_mul, map_mul, map_inv]
    exact conj_mem_utri_of_mem_borel hx ((hmem ⟨s, hSL hs⟩).mp hs))

theorem mem_normalizer_iff_alpha_mem_borel (hSL : S ≤ L) (α : ↥L →* SL(2, F))
    (hα : Function.Surjective α) (hmem : ∀ x : ↥L, (x : G) ∈ S ↔ α x ∈ utri F) (x : ↥L) :
    (x : G) ∈ Subgroup.normalizer (S : Set G) ↔ α x ∈ borel F := by
  constructor
  · intro hx
    exact alpha_mem_borel_of_conj_mem α hα hmem fun s hs =>
      (Subgroup.mem_normalizer_iff.mp hx s).mp hs
  · intro hx
    rw [Subgroup.mem_normalizer_iff]
    intro s
    refine ⟨fun hs => conj_mem_of_alpha_mem_borel hSL α hmem hx hs, fun hs => ?_⟩
    have hx' : α x⁻¹ ∈ borel F := by
      rw [map_inv]
      exact inv_mem hx
    have h := conj_mem_of_alpha_mem_borel hSL α hmem hx' hs
    have e : ((x⁻¹ : ↥L) : G) * ((x : G) * s * (x : G)⁻¹) * ((x⁻¹ : ↥L) : G)⁻¹ = s := by
      rw [Subgroup.coe_inv]
      group
    rwa [e] at h

theorem commutator_mem_of_alpha_mem_borel (α : ↥L →* SL(2, F))
    (hmem : ∀ x : ↥L, (x : G) ∈ S ↔ α x ∈ utri F) {x y : ↥L} (hx : α x ∈ borel F)
    (hy : α y ∈ borel F) : (x : G) * y * (x : G)⁻¹ * (y : G)⁻¹ ∈ S :=
  (hmem (x * y * x⁻¹ * y⁻¹)).mpr (by
    rw [map_mul, map_mul, map_mul, map_inv, map_inv]
    exact borel_commutator_mem_utri hx hy)

theorem card_eq_card_mul_card_of_alpha {Q W : Subgroup G} (α : ↥L →* SL(2, F))
    (hα : Function.Surjective α) (hker : ∀ x : ↥L, α x = 1 ↔ (x : G) ∈ Q) (hWL : W ≤ L)
    (hQW : Q ≤ W) (R : Subgroup SL(2, F)) (hW : ∀ x : ↥L, (x : G) ∈ W ↔ α x ∈ R) :
    Nat.card W = Nat.card Q * Nat.card R := by
  let ψ : ↥W →* SL(2, F) := α.comp (Subgroup.inclusion hWL)
  have hk : ψ.ker = Q.subgroupOf W := by
    ext w
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    exact hker (Subgroup.inclusion hWL w)
  have hr : ψ.range = R := by
    ext g
    constructor
    · rintro ⟨w, rfl⟩
      exact (hW (Subgroup.inclusion hWL w)).mp w.2
    · intro hg
      obtain ⟨x, rfl⟩ := hα g
      exact ⟨⟨x, (hW x).mpr hg⟩, rfl⟩
  rw [← Subgroup.card_ker_mul_card_range ψ, hk, hr,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQW).toEquiv]

end Coord

section Groups

variable {G : Type*} [Group G] {S : Subgroup G}

theorem borelOf_eq_inf_of_le {L : Subgroup G} (h : S ≤ L) :
    borelOf L S = L ⊓ Subgroup.normalizer (S : Set G) := by
  rw [borelOf, inf_eq_left.mpr h]

theorem mem_normalizer_of_mem_borelOf {L : Subgroup G} (h : S ≤ L) {b : G}
    (hb : b ∈ borelOf L S) : b ∈ Subgroup.normalizer (S : Set G) := by
  rw [borelOf_eq_inf_of_le h] at hb
  exact hb.2

theorem mem_borelOf_iff_alpha_mem_borel {L : Subgroup G} (hSL : S ≤ L) {F : Type}
    [Field F] (α : ↥L →* SL(2, F)) (hα : Function.Surjective α)
    (hmem : ∀ x : ↥L, (x : G) ∈ S ↔ α x ∈ utri F) (x : ↥L) :
    (x : G) ∈ borelOf L S ↔ α x ∈ borel F := by
  rw [borelOf_eq_inf_of_le hSL, Subgroup.mem_inf,
    ← mem_normalizer_iff_alpha_mem_borel hSL α hα hmem x]
  exact and_iff_right x.2

theorem commute_mk_iff_commutator_mem {B : Subgroup G} [(S.subgroupOf B).Normal]
    (x y : ↥B) :
    Commute (x : ↥B ⧸ S.subgroupOf B) (y : ↥B ⧸ S.subgroupOf B) ↔
      (x : G) * y * (x : G)⁻¹ * (y : G)⁻¹ ∈ S := by
  have e : (x : G) * y * (x : G)⁻¹ * (y : G)⁻¹ = ((x * y * x⁻¹ * y⁻¹ : ↥B) : G) := rfl
  rw [e, ← Subgroup.mem_subgroupOf, ← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul,
    QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv, QuotientGroup.mk_inv]
  constructor
  · intro h
    rw [h.eq]
    group
  · intro h
    exact mul_inv_eq_iff_eq_mul.mp (mul_inv_eq_one.mp h)

def trivOTwoQuot (L : Subgroup G) : Subgroup G where
  carrier := {g | g ∈ Subgroup.normalizer (L : Set G) ∧
    ∀ x ∈ L, g * x * g⁻¹ * x⁻¹ ∈ pCoreOf 2 L}
  one_mem' := ⟨Subgroup.one_mem _, fun x _ => by simp⟩
  mul_mem' := by
    rintro a b ⟨haN, ha⟩ ⟨hbN, hb⟩
    refine ⟨Subgroup.mul_mem _ haN hbN, fun x hx => ?_⟩
    have h1 := (Subgroup.mem_normalizer_iff.mp
      (normalizer_le_normalizer_pCoreOf 2 L haN) _).mp (hb x hx)
    have e : a * b * x * (a * b)⁻¹ * x⁻¹ =
        a * (b * x * b⁻¹ * x⁻¹) * a⁻¹ * (a * x * a⁻¹ * x⁻¹) := by group
    rw [e]
    exact Subgroup.mul_mem _ h1 (ha x hx)
  inv_mem' := by
    rintro a ⟨haN, ha⟩
    refine ⟨Subgroup.inv_mem _ haN, fun x hx => ?_⟩
    have h1 := (Subgroup.mem_normalizer_iff.mp
      (normalizer_le_normalizer_pCoreOf 2 L (Subgroup.inv_mem _ haN)) _).mp
      (Subgroup.inv_mem _ (ha x hx))
    have e : a⁻¹ * x * a⁻¹⁻¹ * x⁻¹ = a⁻¹ * (a * x * a⁻¹ * x⁻¹)⁻¹ * a⁻¹⁻¹ := by group
    rw [e]
    exact h1

theorem mem_trivOTwoQuot {L : Subgroup G} {g : G} :
    g ∈ trivOTwoQuot L ↔ g ∈ Subgroup.normalizer (L : Set G) ∧
      ∀ x ∈ L, g * x * g⁻¹ * x⁻¹ ∈ pCoreOf 2 L :=
  Iff.rfl

theorem pCoreOf_le_trivOTwoQuot (L : Subgroup G) : pCoreOf 2 L ≤ trivOTwoQuot L := by
  intro a ha
  refine mem_trivOTwoQuot.mpr ⟨Subgroup.le_normalizer
    (CFSG.LieType.BorelTits.pCoreOf_le 2 L ha), fun x hx => ?_⟩
  have h := conj_mem_pCoreOf hx (inv_mem ha)
  have e : a * x * a⁻¹ * x⁻¹ = a * (x * a⁻¹ * x⁻¹) := by group
  rw [e]
  exact mul_mem ha h

end Groups

theorem exists_sup_eq_of_coprime {G : Type*} [Group G] [Finite G] {N X : Subgroup G}
    (hNX : N ≤ X)
    (hXN : X ≤ Subgroup.normalizer (N : Set G)) (k : ℕ) (hcard : Nat.card X = Nat.card N * k)
    (hcop : Nat.Coprime (Nat.card N) k) :
    ∃ H : Subgroup G, H ≤ X ∧ N ⊔ H = X ∧ Nat.card H = k := by
  haveI : (N.subgroupOf X).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hXN
  have hNc : Nat.card (N.subgroupOf X) = Nat.card N :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNX).toEquiv
  have hidx : (N.subgroupOf X).index = k := by
    have h := Subgroup.card_mul_index (N.subgroupOf X)
    rw [hNc, hcard] at h
    exact Nat.eq_of_mul_eq_mul_left Nat.card_pos h
  obtain ⟨H', hH'⟩ := Subgroup.exists_right_complement'_of_coprime (N := N.subgroupOf X)
    (by rw [hNc, hidx]; exact hcop)
  refine ⟨H'.map X.subtype, Subgroup.map_subtype_le H', ?_, ?_⟩
  · have h := congrArg (Subgroup.map X.subtype) hH'.sup_eq_top
    rwa [Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le hNX, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype] at h
  · rw [Subgroup.card_map_of_injective X.subtype_injective, ← hidx]
    exact hH'.symm.index_eq_card.symm

theorem mem_range_upperUnipotent_iff {F : Type} [Field F] {g : SL(2, F)} :
    g ∈ (upperUnipotent (F := F)).range ↔
      ∃ t : F, (g : Matrix (Fin 2) (Fin 2) F) = !![1, t; 0, 1] := by
  rw [← sl2_fixes_first_iff (F := F) g]
  constructor
  · intro h
    have h0 := congrFun h 0
    rw [Matrix.SpecialLinearGroup.smul_def, Matrix.smul_eq_mulVec] at h0
    have h00 : (g : Matrix (Fin 2) (Fin 2) F) 0 0 = 1 := by simpa using h0
    have h1 := congrFun h 1
    rw [Matrix.SpecialLinearGroup.smul_def, Matrix.smul_eq_mulVec] at h1
    have h10 : (g : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 := by simpa using h1
    have h11 : (g : Matrix (Fin 2) (Fin 2) F) 1 1 = 1 := by
      have hdet : (g : Matrix (Fin 2) (Fin 2) F).det = 1 := g.2
      rw [Matrix.det_fin_two, h00, h10] at hdet
      simpa using hdet
    refine ⟨(g : Matrix (Fin 2) (Fin 2) F) 0 1, ?_⟩
    ext i j
    fin_cases i <;> fin_cases j <;> simp [h00, h10, h11]
  · rintro ⟨t, ht⟩
    rw [Matrix.SpecialLinearGroup.smul_def, Matrix.smul_eq_mulVec, ht]
    funext i
    fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]

theorem range_upperUnipotent_eq_utri (F : Type) [Field F] :
    (upperUnipotent (F := F)).range = utri F := by
  ext g
  rw [mem_range_upperUnipotent_iff, mem_utri_iff_eq_unitri]

theorem exists_conj_mem_iff {G : Type*} [Group G] {L S : Subgroup G} {F : Type} [Field F]
    [Finite F] [CharP F 2] (hS : IsSylowTwoOf S L) (α : ↥L →* SL(2, F))
    (hα : Function.Surjective α) (hker : α.ker = CFSG.pCore 2 ↥L) :
    ∃ X : SL(2, F), ∀ x : ↥L, (x : G) ∈ S ↔ X * α x * X⁻¹ ∈ utri F := by
  classical
  have hS2 : IsPGroup 2 (S.subgroupOf L) :=
    hS.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hS.1).symm
  have hp : IsPGroup 2 α.ker := hker ▸ CFSG.pCore_isPGroup (p := 2) (G := ↥L)
  obtain ⟨x, hx⟩ := pgroup_sl2_conjugate_unipotent ((S.subgroupOf L).map α) (hS2.map α)
  rw [range_upperUnipotent_eq_utri] at hx
  let X : SL(2, F) := x⁻¹
  let α' : ↥L →* SL(2, F) := (MulAut.conj X).toMonoidHom.comp α
  have hα' : ∀ y, α' y = X * α y * X⁻¹ := fun y => rfl
  have hker' : α'.ker = α.ker := by
    ext y
    simp only [MonoidHom.mem_ker, hα']
    constructor
    · intro h
      calc α y = X⁻¹ * (X * α y * X⁻¹) * X := by group
        _ = 1 := by rw [h]; group
    · intro h
      rw [h]
      group
  have hle : (S.subgroupOf L).map α' ≤ utri F := by
    have hmap : (S.subgroupOf L).map α' =
        ((S.subgroupOf L).map α).map (MulAut.conj X).toMonoidHom := by
      rw [Subgroup.map_map]
    rw [hmap]
    simpa [X] using hx
  let P : Sylow 2 ↥L := hS2.toSylow hS.2.2
  have hU2 : IsPGroup 2 (utri F) := isPGroup_utri
  have hPle : (P : Subgroup ↥L) ≤ (utri F).comap α' := fun y hy =>
    hle (Subgroup.mem_map_of_mem α' hy)
  have hH : (utri F).comap α' = S.subgroupOf L :=
    P.is_maximal' (hU2.comap_of_ker_isPGroup α' (hker' ▸ hp)) hPle
  refine ⟨X, fun y => ?_⟩
  rw [← hα', ← Subgroup.mem_comap, hH, Subgroup.mem_subgroupOf]

theorem mem_pCoreOf_of_mem_trivOTwoQuot {G : Type*} [Group G] {L : Subgroup G} {F : Type}
    [Field F] [Finite F] [CharP F 2] (α : ↥L →* SL(2, F)) (hα : Function.Surjective α)
    (hker : ∀ x : ↥L, α x = 1 ↔ (x : G) ∈ pCoreOf 2 L) {x : G}
    (hx : x ∈ trivOTwoQuot L) (hxL : x ∈ L) : x ∈ pCoreOf 2 L := by
  classical
  have hc : α ⟨x, hxL⟩ ∈ Subgroup.center SL(2, F) := by
    rw [Subgroup.mem_center_iff]
    intro g
    obtain ⟨y, rfl⟩ := hα g
    have h1 : α (⟨x, hxL⟩ * y * ⟨x, hxL⟩⁻¹ * y⁻¹) = 1 :=
      (hker _).mpr ((mem_trivOTwoQuot.mp hx).2 y y.2)
    rw [map_mul, map_mul, map_mul, map_inv, map_inv] at h1
    exact (mul_inv_eq_iff_eq_mul.mp (mul_inv_eq_one.mp h1)).symm
  rw [center_sl2_eq_bot, Subgroup.mem_bot] at hc
  exact (hker _).mp hc

theorem isNatSecOf_comp_conj {G : Type*} [Group G] {L E N : Subgroup G} {F : Type} [Field F]
    {α : ↥L →* SL(2, F)} (h : IsNatSecOf L E N α) (g : SL(2, F)) :
    IsNatSecOf L E N ((MulAut.conj g).toMonoidHom.comp α) := by
  classical
  obtain ⟨β, hβsurj, hβker, hβeq⟩ := h
  set M : Matrix (Fin 2) (Fin 2) F := (g : Matrix (Fin 2) (Fin 2) F) with hMdef
  set Mi : Matrix (Fin 2) (Fin 2) F := ((g⁻¹ : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) with hMidef
  have hMiM : Mi * M = 1 := by
    rw [hMidef, hMdef, ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel,
      Matrix.SpecialLinearGroup.coe_one]
  have hMMi : M * Mi = 1 := by
    rw [hMidef, hMdef, ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel,
      Matrix.SpecialLinearGroup.coe_one]
  set σ : (Fin 2 → F) →+ (Fin 2 → F) :=
    { toFun := fun v => M *ᵥ v
      map_zero' := by simp
      map_add' := fun a b => by simp [Matrix.mulVec_add] } with hσdef
  have hσ : ∀ v : Fin 2 → F, σ v = M *ᵥ v := fun _ => rfl
  have hσinj : Function.Injective σ := by
    intro a b hab
    have h1 := congrArg (fun v => Mi *ᵥ v) hab
    rw [hσ, hσ, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hMiM, Matrix.one_mulVec,
      Matrix.one_mulVec] at h1
    exact h1
  let β' : ↥E →* Multiplicative (Fin 2 → F) := (AddMonoidHom.toMultiplicative σ).comp β
  have hβ'app : ∀ u : ↥E, Multiplicative.toAdd (β' u) = σ (Multiplicative.toAdd (β u)) :=
    fun _ => rfl
  have hzero : σ 0 = 0 := map_zero σ
  have htoAdd : ∀ v : Fin 2 → F, Multiplicative.toAdd (Multiplicative.ofAdd v) = v := fun _ => rfl
  have hofAdd : ∀ v : Multiplicative (Fin 2 → F),
      Multiplicative.ofAdd (Multiplicative.toAdd v) = v := fun _ => rfl
  refine ⟨β', ?_, ?_, ?_⟩
  · intro w
    obtain ⟨u, hu⟩ :=
      hβsurj (Multiplicative.ofAdd (Mi *ᵥ Multiplicative.toAdd w))
    refine ⟨u, ?_⟩
    show Multiplicative.ofAdd (σ (Multiplicative.toAdd (β u))) = w
    rw [hu, htoAdd, hσ, Matrix.mulVec_mulVec, hMMi, Matrix.one_mulVec]
    exact hofAdd w
  · have htoAddOne : Multiplicative.toAdd (1 : Multiplicative (Fin 2 → F)) = 0 := rfl
    have hkey : ∀ u : ↥E, β' u = 1 ↔ β u = 1 := by
      intro u
      constructor
      · intro hh
        have h1 : Multiplicative.toAdd (β' u) = 0 := by rw [hh, htoAddOne]
        rw [hβ'app u] at h1
        have h2 : Multiplicative.toAdd (β u) = 0 := hσinj (by rw [h1, hzero])
        rw [← hofAdd (β u), h2]
        rfl
      · intro hh
        show Multiplicative.ofAdd (σ (Multiplicative.toAdd (β u))) = 1
        rw [hh, htoAddOne, hzero]
        rfl
    ext u
    rw [MonoidHom.mem_ker, hkey u, ← hβker, MonoidHom.mem_ker]
  · intro l u v hv
    have h1 : Multiplicative.toAdd (β v) =
        (α l : Matrix (Fin 2) (Fin 2) F) *ᵥ Multiplicative.toAdd (β u) := hβeq l u v hv
    have hbuf : Multiplicative.toAdd (β u) = Mi *ᵥ Multiplicative.toAdd (β' u) := by
      rw [hβ'app u, hσ, Matrix.mulVec_mulVec, hMiM, Matrix.one_mulVec]
    have hcoe : ((((MulAut.conj g).toMonoidHom.comp α) l : SL(2, F)) :
        Matrix (Fin 2) (Fin 2) F) = M * (α l : Matrix (Fin 2) (Fin 2) F) * Mi := by
      rw [hMdef, hMidef]
      rfl
    rw [hβ'app v, h1, hbuf, hσ, hcoe, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]

section Diag

variable {F : Type} [Field F]

private theorem diagBorel_ne_zero (g : ↥(borel F)) : (g : SL(2, F)) 0 0 ≠ 0 := by
  have hg : (g : SL(2, F)) 1 0 = 0 := mem_borel_iff.mp g.2
  intro h0
  have hd := sl2_det (g : SL(2, F))
  rw [h0, hg, mul_zero, sub_zero, zero_mul] at hd
  exact zero_ne_one hd

private def diagBorel : ↥(borel F) →* Fˣ where
  toFun g := Units.mk0 ((g : SL(2, F)) 0 0) (diagBorel_ne_zero g)
  map_one' := by
    apply Units.ext
    rw [Units.val_mk0, Units.val_one]
    exact one_apply_00
  map_mul' := fun a b => by
    apply Units.ext
    rw [Units.val_mul, Units.val_mk0, Units.val_mk0, Units.val_mk0]
    have hb : (b : SL(2, F)) 1 0 = 0 := mem_borel_iff.mp b.2
    rw [show ((a * b : ↥(borel F)) : SL(2, F)) = (a : SL(2, F)) * b from rfl, mul_apply_00,
      hb, mul_zero, add_zero]

private theorem diagBorel_apply (g : ↥(borel F)) :
    ((diagBorel (F := F) g : Fˣ) : F) = (g : SL(2, F)) 0 0 := by
  show ((Units.mk0 ((g : SL(2, F)) 0 0) (diagBorel_ne_zero g) : Fˣ) : F) = _
  rw [Units.val_mk0]

private theorem diagBorel_ker : (diagBorel (F := F)).ker = (utri F).subgroupOf (borel F) := by
  ext g
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, mem_utri_entries]
  constructor
  · intro h
    have h00 : (g : SL(2, F)) 0 0 = 1 := by
      have hh := congrArg Units.val h
      rwa [diagBorel_apply, Units.val_one] at hh
    exact ⟨mem_borel_iff.mp g.2, h00⟩
  · rintro ⟨-, h00⟩
    apply Units.ext
    rw [diagBorel_apply, h00, Units.val_one]

end Diag

private theorem odd_two_pow_sub_one_of_ne_zero {k : ℕ} (hk : k ≠ 0) : Odd (2 ^ k - 1) :=
  Nat.Even.sub_odd Nat.one_le_two_pow ((show Even 2 by norm_num).pow_of_ne_zero hk) odd_one

private theorem odd_card_of_eq_sub_one {F : Type} [Field F] [Finite F] [CharP F 2]
    {T : Subgroup SL(2, F)} (hcard : Nat.card T = Nat.card F - 1) : Odd (Nat.card T) := by
  haveI : Fintype F := Fintype.ofFinite F
  obtain ⟨n, -, hq⟩ := FiniteField.card F 2
  have hFcard : Nat.card F = 2 ^ (n : ℕ) := by
    rw [Nat.card_eq_fintype_card]
    exact hq
  rw [hcard, hFcard]
  exact odd_two_pow_sub_one_of_ne_zero n.pos.ne'

private theorem inf_utri_eq_bot_of_odd {F : Type} [Field F] [Finite F] [CharP F 2]
    {T : Subgroup SL(2, F)}
    (hoddT : Odd (Nat.card T)) : utri F ⊓ T = ⊥ := by
  have hodd : Odd (Nat.card ↥(utri F ⊓ T)) :=
    hoddT.of_dvd_nat (Subgroup.card_dvd_of_le inf_le_right)
  have hp : IsPGroup 2 ↥(utri F ⊓ T) := isPGroup_utri.to_le inf_le_left
  obtain ⟨k, hk⟩ := hp.exists_card_eq
  have hk0 : k = 0 := by
    rcases Nat.eq_zero_or_pos k with h | h
    · exact h
    · exfalso
      have hd : 2 ∣ 2 ^ k := dvd_pow_self 2 h.ne'
      exact (Nat.not_even_iff_odd.mpr (hk ▸ hodd)) (even_iff_two_dvd.mpr hd)
  exact Subgroup.eq_bot_of_card_eq _ (by rw [hk, hk0, pow_zero])

private theorem exists_diag_bij {F : Type} [Field F] [Finite F] [CharP F 2]
    {T : Subgroup SL(2, F)} (hT : T ≤ borel F) (hcard : Nat.card T = Nat.card F - 1) :
    ∃ π : ↥T →* Fˣ, Function.Bijective π ∧
      ∀ t : ↥T, ((π t : Fˣ) : F) = (t : SL(2, F)) 0 0 := by
  haveI : Fintype F := Fintype.ofFinite F
  haveI hTfin : Fintype ↥T := Fintype.ofFinite _
  haveI hUfin : Fintype Fˣ := Fintype.ofFinite _
  have hdisj : utri F ⊓ T = ⊥ := inf_utri_eq_bot_of_odd (odd_card_of_eq_sub_one hcard)
  let π : ↥T →* Fˣ := (diagBorel (F := F)).comp (Subgroup.inclusion hT)
  have hπval : ∀ t : ↥T, ((π t : Fˣ) : F) = (t : SL(2, F)) 0 0 := fun t => by
    rw [MonoidHom.comp_apply, diagBorel_apply]
    rfl
  have hπinj : Function.Injective π := by
    intro x y hxy
    have h1 : π (x * y⁻¹) = 1 := by
      rw [map_mul, map_inv, hxy, mul_inv_cancel]
    have h2 : Subgroup.inclusion hT (x * y⁻¹) ∈ (diagBorel (F := F)).ker := h1
    rw [diagBorel_ker] at h2
    have h3 : ((x * y⁻¹ : ↥T) : SL(2, F)) ∈ utri F := Subgroup.mem_subgroupOf.mp h2
    have h4 : ((x * y⁻¹ : ↥T) : SL(2, F)) ∈ (⊥ : Subgroup SL(2, F)) := by
      rw [← hdisj]
      exact ⟨h3, (x * y⁻¹).2⟩
    rw [Subgroup.mem_bot] at h4
    have h5 : x * y⁻¹ = 1 := Subtype.ext h4
    rwa [mul_inv_eq_one] at h5
  have hπcard : Fintype.card ↥T = Fintype.card Fˣ := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hcard, Nat.card_units]
  exact ⟨π, Fintype.bijective_iff_injective_and_card π |>.mpr ⟨hπinj, hπcard⟩, hπval⟩

private theorem exists_zpowers_eq_top_of_bij {F : Type} [Field F] {T : Subgroup SL(2, F)}
    {π : ↥T →* Fˣ} (hbij : Function.Bijective π) {a : Fˣ}
    (ha : ∀ x : Fˣ, x ∈ Subgroup.zpowers a) :
    ∃ g : ↥T, π g = a ∧ Subgroup.zpowers g = ⊤ := by
  obtain ⟨g, hg⟩ := hbij.2 a
  have ha_top : Subgroup.zpowers a = ⊤ := (Subgroup.eq_top_iff' (Subgroup.zpowers a)).mpr ha
  refine ⟨g, hg, ?_⟩
  rw [eq_top_iff]
  intro x _
  have hx : π x ∈ Subgroup.zpowers a := by rw [ha_top]; exact Subgroup.mem_top _
  rw [Subgroup.mem_zpowers_iff] at hx
  obtain ⟨m, hm⟩ := hx
  have h1 : π x = π (g ^ m) := by rw [map_zpow, hg, hm]
  have h2 : x = g ^ m := hbij.1 h1
  rw [h2]
  exact Subgroup.zpow_mem (Subgroup.zpowers g) (Subgroup.mem_zpowers g) m

private theorem eq_zpowers_of_zpowers_subtype_eq_top {F : Type} [Field F]
    {T : Subgroup SL(2, F)} {g : ↥T} (h : Subgroup.zpowers g = ⊤) :
    T = Subgroup.zpowers ((g : SL(2, F))) := by
  have h1 : (⊤ : Subgroup ↥T).map T.subtype = Subgroup.zpowers ((g : SL(2, F))) := by
    rw [← h, MonoidHom.map_zpowers]
    rfl
  rwa [Subgroup.map_top, Subgroup.range_subtype] at h1

private theorem exists_utriElt_conj_eq_torusElt {F : Type} [Field F] [CharP F 2]
    {g : SL(2, F)} (hg : g ∈ borel F) {a : Fˣ} (ha1 : a ≠ 1) (h00 : g 0 0 = (a : F)) :
    ∃ u ∈ utri F, u * g * u⁻¹ = torusElt a := by
  have hg10 : g 1 0 = 0 := mem_borel_iff.mp hg
  set af : F := (a : F) with haf
  have hg00 : g 0 0 = af := h00
  have hg11 : g 1 1 = af⁻¹ := by
    have hd := sl2_det g
    rw [hg10, mul_zero, sub_zero, hg00] at hd
    exact eq_inv_of_mul_eq_one_right hd
  have haf0 : af ≠ 0 := Units.ne_zero a
  have hainv : af + af⁻¹ ≠ 0 := by
    intro h0
    apply ha1
    apply Units.ext
    rw [Units.val_one]
    have h1 : af = af⁻¹ := by
      rw [add_eq_zero_iff_eq_neg] at h0
      rwa [CharTwo.neg_eq] at h0
    have h2 : af * af = 1 := by
      have h := mul_inv_cancel₀ haf0
      rwa [← h1] at h
    have h4 : af ^ 2 = 1 := by rw [pow_two]; exact h2
    exact CharTwo.sq_injective (h4.trans (one_pow 2).symm)
  set b : F := g 0 1 with hbdef
  have hs' : (b / (af + af⁻¹)) * af + (b / (af + af⁻¹)) * af⁻¹ = b := by
    rw [← mul_add, div_mul_cancel₀ b hainv]
  have hinv : ((a⁻¹ : Fˣ) : F) = af⁻¹ := by
    rw [Units.val_inv_eq_inv_val, haf]
  have hkey : utriElt (b / (af + af⁻¹)) * g * (utriElt (b / (af + af⁻¹)))⁻¹ =
      torusElt a := by
    rw [utriElt_inv, CharTwo.neg_eq]
    apply sl2_ext
    · sl2_simp
      rw [hg10, hg00]
      simp only [mul_one, one_mul, mul_zero, add_zero]
      exact haf
    · sl2_simp
      rw [hg10, hg11, hg00, hbdef]
      simp only [mul_one, one_mul, mul_zero, zero_mul, add_zero, zero_add]
      rw [show af * (b / (af + af⁻¹)) + (b + (b / (af + af⁻¹)) * af⁻¹) =
        (af * (b / (af + af⁻¹)) + (b / (af + af⁻¹)) * af⁻¹) + b by ring]
      rw [show af * (b / (af + af⁻¹)) = (b / (af + af⁻¹)) * af from mul_comm _ _, hs',
        CharTwo.add_self_eq_zero]
    · sl2_simp
      rw [hg10]
      ring
    · sl2_simp
      rw [hg11, hinv, hg10]
      ring
  exact ⟨utriElt (b / (af + af⁻¹)), utriElt_mem_utri _, hkey⟩

theorem exists_utri_conj_eq_torus {F : Type} [Field F] [Finite F] [CharP F 2]
    {T : Subgroup SL(2, F)} (hT : T ≤ borel F) (hcard : Nat.card T = Nat.card F - 1) :
    ∃ u ∈ utri F, T.map (MulAut.conj u).toMonoidHom = torus F := by
  classical
  obtain ⟨π, hbij, hπval⟩ := exists_diag_bij hT hcard
  obtain ⟨a, ha⟩ := IsCyclic.exists_generator (α := Fˣ)
  obtain ⟨g, hg, hgen⟩ := exists_zpowers_eq_top_of_bij hbij ha
  have hgval : (g : SL(2, F)) 0 0 = (a : F) := by rw [← hπval g, hg]
  have hTgen : T = Subgroup.zpowers ((g : SL(2, F))) := eq_zpowers_of_zpowers_subtype_eq_top hgen
  by_cases ha1 : a = 1
  · have hg1 : (g : SL(2, F)) = 1 := by
      have h1 : g = 1 := hbij.1 (by rw [hg, ha1, map_one])
      rw [h1]
      rfl
    have hTbot : T = ⊥ := by rw [hTgen, hg1, Subgroup.zpowers_one_eq_bot]
    have htor : torus F = ⊥ := by
      refine Subgroup.eq_bot_of_card_eq _ ?_
      rw [card_torus, ← hcard, hTbot, Subgroup.card_bot]
    exact ⟨1, by simpa using utriElt_mem_utri (0 : F), by rw [hTbot, htor, Subgroup.map_bot]⟩
  · obtain ⟨u, hu, hkey⟩ := exists_utriElt_conj_eq_torusElt (hT g.2) ha1 hgval
    have hconjapp : (MulEquiv.toMonoidHom (MulAut.conj u)) (g : SL(2, F)) = torusElt a := by
      rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      exact hkey
    refine ⟨u, hu, ?_⟩
    rw [hTgen, MonoidHom.map_zpowers, hconjapp]
    refine le_antisymm (Subgroup.zpowers_le.mpr (torusElt_mem_torus a)) ?_
    intro x hx
    obtain ⟨c, rfl⟩ := mem_torus_iff.mp hx
    have hc : c ∈ Subgroup.zpowers a := by
      rw [(Subgroup.eq_top_iff' (Subgroup.zpowers a)).mpr ha]
      exact Subgroup.mem_top c
    rw [Subgroup.mem_zpowers_iff] at hc ⊢
    obtain ⟨m, rfl⟩ := hc
    exact ⟨m, (map_zpow (CFSG.Glauberman.Dickson.splitTorusSLHom F) a m).symm⟩

end CFSG.Quasithin.F112R.St84

end
