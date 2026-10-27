module

public import CFSG.Timmesfeld.RankTwo.ModelD43Weyl
public import CFSG.Timmesfeld.RankTwo.ModelG2
public import Certificates.Certificate45
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate49
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate53
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate59
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate68
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate72
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate115
public import Certificates.Certificate116
public import Certificates.Certificate117
public import Certificates.Certificate123

public section

namespace CFSG.Timmesfeld.RankTwo

open CFSG.Timmesfeld.GradedPresentation CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Adjoint
open CFSG.LieType.Steinberg.TwistedD4 CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open scoped commutatorElement

variable {K : Type} [Field K] (σ : K →+* K)

local notation "𝕩" => xPar (rootOperatorFamily d4)

set_option quotPrecheck false in
local notation "Φ" => RootSystem.ofCartan (twistedDatum σ).isFiniteType (twistedDatum σ).divisible

set_option quotPrecheck false in
local notation "𝕏" => (twistedDatum σ).rootGroup

@[expose] noncomputable def d43XE : ∀ i : Fin 6, d43Par σ i → adjointGroup d4 K
  | 0, c => d43XSh σ (hexRoot 0) c
  | 1, c => d43XLg σ (hexRoot 1) c
  | 2, c => d43XSh σ (hexRoot 2) c
  | 3, c => d43XLg σ (hexRoot 3) c
  | 4, c => d43XSh σ (hexRoot 4) c
  | 5, c => d43XLg σ (hexRoot 5) c

theorem d43Lift_hexRoot (i : Fin 6) :
    d43Lift (hexRoot i) = d4Root (![0, 19, 15, 22, 5, 2] i) := by
  rw [hexRoot_eq_g2, d43Lift_root (by fin_cases i <;> decide)]
  fin_cases i <;> rfl

theorem d43XE_zero (c : K) : d43XE σ 0 c = xOrbit σ (d4Root 0) c :=
  congrArg (fun γ => xOrbit σ γ c) (d43Lift_hexRoot 0)

theorem d43XE_one (c : fixedField σ) : d43XE σ 1 c = 𝕩 (d4Root 19) (c : K) :=
  congrArg (fun γ => 𝕩 γ (c : K)) (d43Lift_hexRoot 1)

theorem d43XE_two (c : K) : d43XE σ 2 c = xOrbit σ (d4Root 15) c :=
  congrArg (fun γ => xOrbit σ γ c) (d43Lift_hexRoot 2)

theorem d43XE_three (c : fixedField σ) : d43XE σ 3 c = 𝕩 (d4Root 22) (c : K) :=
  congrArg (fun γ => 𝕩 γ (c : K)) (d43Lift_hexRoot 3)

theorem d43XE_four (c : K) : d43XE σ 4 c = xOrbit σ (d4Root 5) c :=
  congrArg (fun γ => xOrbit σ γ c) (d43Lift_hexRoot 4)

theorem d43XE_five (c : fixedField σ) : d43XE σ 5 c = 𝕩 (d4Root 2) (c : K) :=
  congrArg (fun γ => 𝕩 γ (c : K)) (d43Lift_hexRoot 5)

theorem short_hexRoot_zero : ¬d43Long (hexRoot 0) := by
  change ¬(3 : ℤ) ∣ 1
  decide

theorem long_hexRoot_one : d43Long (hexRoot 1) := by
  change (3 : ℤ) ∣ 3
  decide

theorem short_hexRoot_two : ¬d43Long (hexRoot 2) := by
  change ¬(3 : ℤ) ∣ 2
  decide

theorem long_hexRoot_three : d43Long (hexRoot 3) := by
  change (3 : ℤ) ∣ 3
  decide

theorem short_hexRoot_four : ¬d43Long (hexRoot 4) := by
  change ¬(3 : ℤ) ∣ 1
  decide

theorem long_hexRoot_five : d43Long (hexRoot 5) := by
  change (3 : ℤ) ∣ 0
  decide

variable {σ}

theorem d43XE_rels [CharP K 2] (hσ : ∀ c, σ (σ (σ c)) = c) :
    ∀ r ∈ rels (d43Cm hσ), FreeGroup.lift (fun g : Σ i, d43Par σ i => d43XE σ g.1 g.2) r = 1 := by
  refine rels_d43Cm_of hσ ?_ (fun s t => ?_) (fun s t => ?_) (fun s t => ?_) (fun s t => ?_)
    (fun s t => ?_) (fun s t => ?_) (fun s t => ?_) (fun s t => ?_) (fun s t => ?_)
    (fun s t => ?_) (fun s t => ?_) (fun s t => ?_) (fun s t => ?_) (fun s t => ?_)
    (fun s t => ?_)
  · refine d43_add_of (φ := fun g : Σ i, d43Par σ i => d43XE σ g.1 g.2) (fun c d => ?_)
      (fun c d => ?_) (fun c d => ?_) (fun c d => ?_) (fun c d => ?_) (fun c d => ?_)
    · exact d43XSh_add (isRoot_hexRoot 0) short_hexRoot_zero c d
    · exact d43XLg_add _ c d
    · exact d43XSh_add (isRoot_hexRoot 2) short_hexRoot_two c d
    · exact d43XLg_add _ c d
    · exact d43XSh_add (isRoot_hexRoot 4) short_hexRoot_four c d
    · exact d43XLg_add _ c d
  · change ⁅d43XE σ 0 s, d43XE σ 2 t⁆ = d43XE σ 1 (d43Tr hσ (s * t))
    rw [d43XE_zero, d43XE_two, d43XE_one]
    exact d43_comm02 hσ s t
  · change ⁅d43XE σ 2 s, d43XE σ 4 t⁆ = d43XE σ 3 (d43Tr hσ (s * t))
    rw [d43XE_two, d43XE_four, d43XE_three]
    exact d43_comm24 hσ s t
  · change ⁅d43XE σ 1 s, d43XE σ 5 t⁆ = d43XE σ 3 (s * t : fixedField σ)
    rw [d43XE_one, d43XE_five, d43XE_three]
    exact d43_comm15 s t
  · change ⁅d43XE σ 0 s, d43XE σ 4 t⁆ = d43XE σ 1 (d43Tr hσ (d43Sharp σ s * t)) *
      d43XE σ 2 (d43Cross σ s t : K) * d43XE σ 3 (d43Tr hσ (s * d43Sharp σ t))
    rw [d43XE_zero, d43XE_four, d43XE_one, d43XE_two, d43XE_three]
    exact d43_comm04 hσ s t
  · change ⁅d43XE σ 0 s, d43XE σ 5 t⁆ = d43XE σ 1 (t * d43Norm hσ s : fixedField σ) *
      d43XE σ 2 ((t : K) * d43Sharp σ s : K) * d43XE σ 3 (t ^ 2 * d43Norm hσ s : fixedField σ) *
        d43XE σ 4 ((t : K) * s : K)
    rw [d43XE_zero, d43XE_five, d43XE_one, d43XE_two, d43XE_three, d43XE_four,
      d43_comm05 hσ s (t : K) t.2]
    rfl
  · change Commute (d43XE σ 0 s) (d43XE σ 1 t)
    rw [d43XE_zero, d43XE_one]
    exact d43_commute01 s (t : K)
  · change Commute (d43XE σ 0 s) (d43XE σ 3 t)
    rw [d43XE_zero, d43XE_three]
    exact d43_commute03 s (t : K)
  · change Commute (d43XE σ 1 s) (d43XE σ 2 t)
    rw [d43XE_one, d43XE_two]
    exact d43_commute12 (s : K) t
  · change Commute (d43XE σ 1 s) (d43XE σ 3 t)
    rw [d43XE_one, d43XE_three]
    exact d43_commute13 (s : K) (t : K)
  · change Commute (d43XE σ 1 s) (d43XE σ 4 t)
    rw [d43XE_one, d43XE_four]
    exact d43_commute14 (s : K) t
  · change Commute (d43XE σ 2 s) (d43XE σ 3 t)
    rw [d43XE_two, d43XE_three]
    exact d43_commute23 s (t : K)
  · change Commute (d43XE σ 2 s) (d43XE σ 5 t)
    rw [d43XE_two, d43XE_five]
    exact d43_commute25 s (t : K)
  · change Commute (d43XE σ 3 s) (d43XE σ 4 t)
    rw [d43XE_three, d43XE_four]
    exact d43_commute34 (s : K) t
  · change Commute (d43XE σ 3 s) (d43XE σ 5 t)
    rw [d43XE_three, d43XE_five]
    exact d43_commute35 (s : K) (t : K)
  · change Commute (d43XE σ 4 s) (d43XE σ 5 t)
    rw [d43XE_four, d43XE_five]
    exact d43_commute45 s (t : K)

variable (hσ : ∀ c, σ (σ (σ c)) = c)

include hσ in
theorem d43XE_mem (i : Fin 6) (c : d43Par σ i) :
    d43XE σ i c ∈ twistedRootSubgroupD4 σ (hexRoot i) :=
  match i, c with
  | 0, c => d43XSh_mem hσ (isRoot_hexRoot 0) short_hexRoot_zero c
  | 1, c => d43XLg_mem hσ (isRoot_hexRoot 1) long_hexRoot_one c
  | 2, c => d43XSh_mem hσ (isRoot_hexRoot 2) short_hexRoot_two c
  | 3, c => d43XLg_mem hσ (isRoot_hexRoot 3) long_hexRoot_three c
  | 4, c => d43XSh_mem hσ (isRoot_hexRoot 4) short_hexRoot_four c
  | 5, c => d43XLg_mem hσ (isRoot_hexRoot 5) long_hexRoot_five c

@[expose] noncomputable def d43X (i : Fin 6) (c : d43Par σ i) : twistedGroup σ :=
  ⟨d43XE σ i c, twistedRootSubgroupD4_le_twistedGroup σ (isRoot_hexRoot i) (d43XE_mem hσ i c)⟩

theorem d43X_mem (i : Fin 6) (c : d43Par σ i) : d43X hσ i c ∈ twistedRootGroup σ (hexRoot i) :=
  (mem_twistedRootGroup σ).2 (d43XE_mem hσ i c)

theorem d43XE_injective (i : Fin 6) : Function.Injective (d43XE σ i) :=
  match i with
  | 0 => fun _ _ h => d43XSh_injective (σ := σ) (isRoot_hexRoot 0) short_hexRoot_zero h
  | 1 => fun _ _ h => d43XLg_injective (σ := σ) (isRoot_hexRoot 1) h
  | 2 => fun _ _ h => d43XSh_injective (σ := σ) (isRoot_hexRoot 2) short_hexRoot_two h
  | 3 => fun _ _ h => d43XLg_injective (σ := σ) (isRoot_hexRoot 3) h
  | 4 => fun _ _ h => d43XSh_injective (σ := σ) (isRoot_hexRoot 4) short_hexRoot_four h
  | 5 => fun _ _ h => d43XLg_injective (σ := σ) (isRoot_hexRoot 5) h

theorem d43X_rels [CharP K 2] :
    ∀ r ∈ rels (d43Cm hσ), FreeGroup.lift (fun g : Σ i, d43Par σ i => d43X hσ g.1 g.2) r = 1 := by
  intro r hr
  have h := d43XE_rels hσ r hr
  have e : (twistedGroup σ).subtype.comp
      (FreeGroup.lift fun g : Σ i, d43Par σ i => d43X hσ g.1 g.2) =
        FreeGroup.lift fun g : Σ i, d43Par σ i => d43XE σ g.1 g.2 :=
    FreeGroup.ext_hom _ _ fun g => rfl
  apply Subtype.val_injective
  change ((twistedGroup σ).subtype.comp (FreeGroup.lift _)) r = 1
  rw [e, h]

theorem d43X_prod_injective :
    Function.Injective fun c : (∀ i, d43Par σ i) =>
      ([0, 5, 4, 2, 1, 3].map fun i => d43X hσ i (c i)).prod := by
  refine injective_prod_of_prodInjectiveFor (X := twistedRootGroup σ) hexRoot hexRoot_injective
    (fun i c => d43X hσ i c) (d43X_mem hσ) (fun i c d h => d43XE_injective i
      (congrArg Subtype.val h)) _ (by decide) ?_
  refine prodInjective_twisted σ 1 (([0, 5, 4, 2, 1, 3] : List (Fin 6)).map hexRoot) (by decide)
    (fun β hβ => ?_) (by decide)
  obtain ⟨i, -, rfl⟩ := List.mem_map.1 hβ
  exact ⟨isRoot_hexRoot i, by fin_cases i <;> decide⟩

open Classical in
@[expose] noncomputable def d43PhiOf {G : Type*} [Group G]
    (ψS : (Fin (Tag.rank .G2) → ℤ) → K → G) (ψL : (Fin (Tag.rank .G2) → ℤ) → fixedField σ → G) :
    ∀ γ, 𝕏 γ → G :=
  fun γ y => if h : IsRoot .G2 γ then
      if hl : d43Long γ then
        ψL γ ((mem_iff_d43XLg hσ h hl _).1 ((mem_twistedRootGroup σ).1 y.2)).choose
      else ψS γ ((mem_iff_d43XSh hσ h hl _).1 ((mem_twistedRootGroup σ).1 y.2)).choose
    else 1

variable {G : Type*} [Group G] (ψS : (Fin (Tag.rank .G2) → ℤ) → K → G)
  (ψL : (Fin (Tag.rank .G2) → ℤ) → fixedField σ → G)

theorem d43PhiOf_short {γ : Fin (Tag.rank .G2) → ℤ} (hγ : IsRoot .G2 γ) (hs : ¬d43Long γ)
    (c : K) (y : 𝕏 γ) (hy : ((y : twistedGroup σ) : adjointGroup d4 K) = d43XSh σ γ c) :
    d43PhiOf hσ ψS ψL γ y = ψS γ c := by
  classical
  unfold d43PhiOf
  rw [dite_eq_left hγ, dite_eq_right hs]
  exact congrArg (ψS γ) (d43XSh_injective hγ hs
    (((mem_iff_d43XSh hσ hγ hs _).1 ((mem_twistedRootGroup σ).1 y.2)).choose_spec.trans hy))

theorem d43PhiOf_long {γ : Fin (Tag.rank .G2) → ℤ} (hγ : IsRoot .G2 γ) (hl : d43Long γ)
    (c : fixedField σ) (y : 𝕏 γ)
    (hy : ((y : twistedGroup σ) : adjointGroup d4 K) = d43XLg σ γ c) :
    d43PhiOf hσ ψS ψL γ y = ψL γ c := by
  classical
  unfold d43PhiOf
  rw [dite_eq_left hγ, dite_eq_left hl]
  exact congrArg (ψL γ) (d43XLg_injective hγ
    (((mem_iff_d43XLg hσ hγ hl _).1 ((mem_twistedRootGroup σ).1 y.2)).choose_spec.trans hy))

@[expose] noncomputable def d43PsiPos : (Σ i, d43Par σ i) → G
  | ⟨0, c⟩ => ψS (hexRoot 0) c
  | ⟨1, c⟩ => ψL (hexRoot 1) c
  | ⟨2, c⟩ => ψS (hexRoot 2) c
  | ⟨3, c⟩ => ψL (hexRoot 3) c
  | ⟨4, c⟩ => ψS (hexRoot 4) c
  | ⟨5, c⟩ => ψL (hexRoot 5) c

variable (σ) in
theorem mem_d43_roots {γ : Fin (Tag.rank .G2) → ℤ} : γ ∈ (Φ).roots ↔ IsRoot .G2 γ := by
  change γ ∈ (twistedDatum σ).roots ↔ _
  rw [twistedDatum_roots]
  rfl

theorem d43_extendsToHom_pos [CharP K 2] [Finite K]
    (hψ : ∀ w ∈ rels (d43Cm hσ), FreeGroup.lift (d43PsiPos ψS ψL) w = 1) :
    ExtendsToHom 𝕏 (Φ).pos (d43PhiOf hσ ψS ψL) := by
  have hfin : ∀ i, Fintype (d43Par σ i) := fun i =>
    match i with
    | 0 => (Fintype.ofFinite K : Fintype K)
    | 1 => (Fintype.ofFinite (fixedField σ) : Fintype (fixedField σ))
    | 2 => (Fintype.ofFinite K : Fintype K)
    | 3 => (Fintype.ofFinite (fixedField σ) : Fintype (fixedField σ))
    | 4 => (Fintype.ofFinite K : Fintype K)
    | 5 => (Fintype.ofFinite (fixedField σ) : Fintype (fixedField σ))
  refine extendsToHom_of_rels (F := d43Par σ) (d43Cm_mem_above hσ) hexRoot
    (fun i c => d43X hσ i c) (d43X_mem hσ) (d43X_rels hσ) _ (d43X_prod_injective hσ)
    (fun γ hγ => exists_hexRoot_eq ((mem_d43_roots σ).1 hγ.1) hγ.2) (fun i y hy => ?_) _ hψ
    (fun i c => ?_)
  · obtain ⟨y, hyΓ⟩ := y
    have hy' := (mem_twistedRootGroup σ).1 hy
    fin_cases i
    · obtain ⟨c, hc⟩ := (mem_iff_d43XSh hσ (isRoot_hexRoot 0) short_hexRoot_zero _).1 hy'
      exact ⟨c, Subtype.ext hc⟩
    · obtain ⟨c, hc⟩ := (mem_iff_d43XLg hσ (isRoot_hexRoot 1) long_hexRoot_one _).1 hy'
      exact ⟨c, Subtype.ext hc⟩
    · obtain ⟨c, hc⟩ := (mem_iff_d43XSh hσ (isRoot_hexRoot 2) short_hexRoot_two _).1 hy'
      exact ⟨c, Subtype.ext hc⟩
    · obtain ⟨c, hc⟩ := (mem_iff_d43XLg hσ (isRoot_hexRoot 3) long_hexRoot_three _).1 hy'
      exact ⟨c, Subtype.ext hc⟩
    · obtain ⟨c, hc⟩ := (mem_iff_d43XSh hσ (isRoot_hexRoot 4) short_hexRoot_four _).1 hy'
      exact ⟨c, Subtype.ext hc⟩
    · obtain ⟨c, hc⟩ := (mem_iff_d43XLg hσ (isRoot_hexRoot 5) long_hexRoot_five _).1 hy'
      exact ⟨c, Subtype.ext hc⟩
  · match i, c with
    | 0, c => exact d43PhiOf_short hσ ψS ψL (isRoot_hexRoot 0) short_hexRoot_zero c _ rfl
    | 1, c => exact d43PhiOf_long hσ ψS ψL (isRoot_hexRoot 1) long_hexRoot_one c _ rfl
    | 2, c => exact d43PhiOf_short hσ ψS ψL (isRoot_hexRoot 2) short_hexRoot_two c _ rfl
    | 3, c => exact d43PhiOf_long hσ ψS ψL (isRoot_hexRoot 3) long_hexRoot_three c _ rfl
    | 4, c => exact d43PhiOf_short hσ ψS ψL (isRoot_hexRoot 4) short_hexRoot_four c _ rfl
    | 5, c => exact d43PhiOf_long hσ ψS ψL (isRoot_hexRoot 5) long_hexRoot_five c _ rfl

variable (σ) in
theorem d43_conj_mem_refl :
    ∀ i, ∀ γ ∈ (Φ).roots, ∀ x ∈ 𝕏 γ, nHat σ i * x * (nHat σ i)⁻¹ ∈ 𝕏 ((Φ).refl i γ) := by
  intro i γ hγ x hx
  exact nHat_conj_mem σ i ((mem_d43_roots σ).1 hγ) hx

theorem d43_conj_map_refl [CharP K 2] (ñ : Fin (Tag.rank .G2) → G)
    (hWS : ∀ i γ, IsRoot .G2 γ → ¬d43Long γ → ∀ c, ñ i * ψS γ c * (ñ i)⁻¹ = ψS ((Φ).refl i γ) c)
    (hWL : ∀ i γ, IsRoot .G2 γ → d43Long γ → ∀ c,
      ñ i * ψL γ c * (ñ i)⁻¹ = ψL ((Φ).refl i γ) c) :
    ∀ i, ∀ γ ∈ (Φ).roots, ∀ (x : 𝕏 γ) (y : 𝕏 ((Φ).refl i γ)),
      (y : twistedGroup σ) = nHat σ i * x * (nHat σ i)⁻¹ →
      ñ i * d43PhiOf hσ ψS ψL γ x * (ñ i)⁻¹ = d43PhiOf hσ ψS ψL ((Φ).refl i γ) y := by
  intro i γ hγ x y hy
  have hγ' := (mem_d43_roots σ).1 hγ
  have hs := (mem_d43_roots σ).1 ((Φ).refl_mem i γ hγ)
  have hy' : ((y : twistedGroup σ) : adjointGroup d4 K) =
      nHatE K i * ((x : twistedGroup σ) : adjointGroup d4 K) * (nHatE K i)⁻¹ := by
    rw [hy]
    rfl
  have hx := (mem_twistedRootGroup σ).1 x.2
  by_cases hl : d43Long γ
  · obtain ⟨c, hc⟩ := (mem_iff_d43XLg hσ hγ' hl _).1 hx
    have hl' : d43Long ((Φ).refl i γ) := (d43Long_reflect i hγ').2 hl
    have hyc : ((y : twistedGroup σ) : adjointGroup d4 K) = d43XLg σ ((Φ).refl i γ) c :=
      hy'.trans (by rw [← hc]; exact nHatE_conj_d43XLg i hγ' c)
    rw [d43PhiOf_long hσ ψS ψL hγ' hl c x hc.symm, d43PhiOf_long hσ ψS ψL hs hl' c y hyc]
    exact hWL i γ hγ' hl c
  · obtain ⟨c, hc⟩ := (mem_iff_d43XSh hσ hγ' hl _).1 hx
    have hl' : ¬d43Long ((Φ).refl i γ) := fun h => hl ((d43Long_reflect i hγ').1 h)
    have hyc : ((y : twistedGroup σ) : adjointGroup d4 K) = d43XSh σ ((Φ).refl i γ) c :=
      hy'.trans (by rw [← hc]; exact nHatE_conj_d43XSh i hγ' c)
    rw [d43PhiOf_short hσ ψS ψL hγ' hl c x hc.symm, d43PhiOf_short hσ ψS ψL hs hl' c y hyc]
    exact hWS i γ hγ' hl c

theorem d43_coneCompatible_of [CharP K 2] [Finite K]
    (hψ : ∀ w ∈ rels (d43Cm hσ), FreeGroup.lift (d43PsiPos ψS ψL) w = 1)
    (ñ : Fin (Tag.rank .G2) → G)
    (hWS : ∀ i γ, IsRoot .G2 γ → ¬d43Long γ → ∀ c, ñ i * ψS γ c * (ñ i)⁻¹ = ψS ((Φ).refl i γ) c)
    (hWL : ∀ i γ, IsRoot .G2 γ → d43Long γ → ∀ c,
      ñ i * ψL γ c * (ñ i)⁻¹ = ψL ((Φ).refl i γ) c)
    (hrank : ∀ i, ExtendsToHom 𝕏 {Pi.single i 1, -Pi.single i 1} (d43PhiOf hσ ψS ψL)) :
    ConeCompatible Φ 𝕏 (d43PhiOf hσ ψS ψL) :=
  coneCompatible_of_pos (nHat σ) (d43_conj_mem_refl σ) ñ
    (d43_conj_map_refl hσ ψS ψL ñ hWS hWL) (d43_extendsToHom_pos hσ ψS ψL hψ) hrank

end CFSG.Timmesfeld.RankTwo
