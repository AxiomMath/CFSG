module

public import CFSG.Quasithin.H13.NQBlockOriginalRadical
public import CFSG.Quasithin.H13.NQSetupOddCore
public import CFSG.Quasithin.H13.NQSetupPlaneAction
public import CFSG.Quasithin.SteinbergBMTIPairCommutation
public import CFSG.Quasithin.Background.A4Defs

public section

namespace CFSG.Quasithin.H13.NQBlock

open Subgroup CFSG.Open
open scoped commutatorElement

section General

variable {G : Type*} [Group G]

theorem normalizer_le_normalizer_weakClosure [Finite G] (U Y : Subgroup G) :
    normalizer (Y : Set G) ≤
      normalizer ((sSup {X : Subgroup G | (∃ h : G, CFSG.conjugate U h = X) ∧ X ≤ Y} :
        Subgroup G) : Set G) := by
  intro g hg
  refine A4.mem_normalizer_of_conj_mem fun k hk => ?_
  have hle : sSup {X : Subgroup G | (∃ h : G, CFSG.conjugate U h = X) ∧ X ≤ Y} ≤
      (sSup {X : Subgroup G | (∃ h : G, CFSG.conjugate U h = X) ∧ X ≤ Y}).comap
        (MulAut.conj g).toMonoidHom := by
    refine sSup_le fun X ⟨⟨h, hX⟩, hXY⟩ x hx => ?_
    rw [mem_comap]
    have hmem : CFSG.conjugate U (h * g⁻¹) ∈
        {X : Subgroup G | (∃ h : G, CFSG.conjugate U h = X) ∧ X ≤ Y} := by
      refine ⟨⟨h * g⁻¹, rfl⟩, fun y hy => ?_⟩
      rw [BlueprintB2.mem_conjugate_iff] at hy
      have h1 : g⁻¹ * y * g ∈ X := by
        rw [← hX, BlueprintB2.mem_conjugate_iff]
        rwa [show h * (g⁻¹ * y * g) * h⁻¹ = h * g⁻¹ * y * (h * g⁻¹)⁻¹ by group]
      have h2 := (mem_normalizer_iff.mp hg (g⁻¹ * y * g)).mp (hXY h1)
      rwa [show g * (g⁻¹ * y * g) * g⁻¹ = y by group] at h2
    have hx' : g * x * g⁻¹ ∈ CFSG.conjugate U (h * g⁻¹) := by
      rw [BlueprintB2.mem_conjugate_iff]
      rw [← hX, BlueprintB2.mem_conjugate_iff] at hx
      rwa [show h * g⁻¹ * (g * x * g⁻¹) * (h * g⁻¹)⁻¹ = h * x * h⁻¹ by group]
    exact le_sSup hmem hx'
  exact hle hk

theorem conjugate_le_centralizer_of_TI [Finite G] {U T : Subgroup G}
    (hUe : CFSG.IsElementaryAbelian 2 U) (hU1 : U ≠ ⊥)
    (hTI : ∀ x : G, U ⊓ CFSG.conjugate U x = ⊥ ∨ CFSG.conjugate U x = U) (hT2 : IsPGroup 2 T)
    (hUT : U ≤ T) (hTU : T ≤ normalizer (U : Set G)) {g : G} (hg : CFSG.conjugate U g ≤ T) :
    CFSG.conjugate U g ≤ centralizer (U : Set G) := by
  have hUc := (SteinbergBM.elementaryAbelian_two_facts hUe).1
  by_cases hgU : CFSG.conjugate U g = U
  · rw [hgU]
    intro x hx
    rw [mem_centralizer_iff]
    intro y hy
    exact hUc y hy x hx
  · have hne : CFSG.conjugate U g ≠ ⊥ := fun h0 =>
      hU1 ((map_eq_bot_iff_of_injective _ (MulAut.conj g⁻¹).injective).mp h0)
    have h1 := (SteinbergBM.nq_elementary_TI_pair_commutation hUe hTI hgU).2
      (hT2.to_le (sup_le hUT hg)) (by rwa [inf_eq_left.mpr (hg.trans hTU)])
    rw [commutator_comm] at h1
    exact commutator_eq_bot_iff_le_centralizer.mp h1

theorem commutator_mem_centralizer_of_stability {U V X : Subgroup G}
    (hU : ∀ x ∈ U, ∀ y ∈ U, x * y = y * x) (hXU : X ≤ centralizer (U : Set G))
    (hX : ∀ x ∈ X, ∀ v ∈ V, v⁻¹ * (x * v * x⁻¹) ∈ U) {a b : G} (ha : a ∈ X) (hb : b ∈ X) :
    a * b * a⁻¹ * b⁻¹ ∈ centralizer (V : Set G) := by
  rw [mem_centralizer_iff]
  intro v hv
  have key : ∀ x ∈ X, ∀ y ∈ X, x * y * v * (x * y)⁻¹ =
      v * (v⁻¹ * (x * v * x⁻¹)) * (v⁻¹ * (y * v * y⁻¹)) := by
    intro x hx y hy
    have hc : x * (v⁻¹ * (y * v * y⁻¹)) = (v⁻¹ * (y * v * y⁻¹)) * x :=
      (mem_centralizer_iff.mp (hXU hx) _ (hX y hy v hv)).symm
    calc x * y * v * (x * y)⁻¹ = (x * v * x⁻¹) * (x * (v⁻¹ * (y * v * y⁻¹)) * x⁻¹) := by group
      _ = (x * v * x⁻¹) * (v⁻¹ * (y * v * y⁻¹)) := by rw [hc]; group
      _ = v * (v⁻¹ * (x * v * x⁻¹)) * (v⁻¹ * (y * v * y⁻¹)) := by group
  have E : a⁻¹ * b⁻¹ * v * (a⁻¹ * b⁻¹)⁻¹ = b⁻¹ * a⁻¹ * v * (b⁻¹ * a⁻¹)⁻¹ := by
    rw [key _ (inv_mem ha) _ (inv_mem hb), key _ (inv_mem hb) _ (inv_mem ha)]
    have hc := hU _ (hX _ (inv_mem ha) v hv) _ (hX _ (inv_mem hb) v hv)
    rw [mul_assoc v, mul_assoc v, hc]
  calc v * (a * b * a⁻¹ * b⁻¹) = a * b * (b⁻¹ * a⁻¹ * v * (b⁻¹ * a⁻¹)⁻¹) * (a⁻¹ * b⁻¹) := by
        group
    _ = a * b * (a⁻¹ * b⁻¹ * v * (a⁻¹ * b⁻¹)⁻¹) * (a⁻¹ * b⁻¹) := by rw [← E]
    _ = a * b * a⁻¹ * b⁻¹ * v := by group

theorem supplement_frattini_of_le_normalizer [Finite G] {L N R L₁ : Subgroup G} (T : Sylow 2 G)
    (hTN : (T : Subgroup G) ≤ normalizer (N : Set G)) (hL₁N : L₁ ≤ normalizer (N : Set G))
    (hRT : R ≤ T) (hTNR : (T : Subgroup G) ⊓ N ≤ R)
    (hRc : ∀ r ∈ R, ∀ l ∈ L, l * r * l⁻¹ * r⁻¹ ∈ N)
    (hL₁L : L₁ ≤ L) (hTL₁ : (T : Subgroup G) ≤ normalizer (L₁ : Set G)) :
    L₁ = (L₁ ⊓ N) ⊔ (L₁ ⊓ normalizer (R : Set G)) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hRL₁ : R ≤ normalizer (L₁ : Set G) := hRT.trans hTL₁
  have hRR : R ≤ normalizer (R : Set G) := le_normalizer
  have hL₁L₁ : L₁ ≤ normalizer (L₁ : Set G) := le_normalizer
  have hTN₁ : (T : Subgroup G) ≤ normalizer ((L₁ ⊓ N : Subgroup G) : Set G) := fun t ht =>
    mem_normalizer_inf (hTL₁ ht) (hTN ht)
  have hRN₁ : R ≤ normalizer ((L₁ ⊓ N : Subgroup G) : Set G) := hRT.trans hTN₁
  have hS1 : CFSG.ABGLocalTools.IsSylowOf 2 (T : Subgroup G) ((L₁ ⊓ N) ⊔ T) :=
    (isSylowOf_top T).of_le le_sup_right le_top
  have hS2 := hS1.inf_of_le_normalizer le_sup_left (sup_le le_normalizer hTN₁)
  have hTR : (T : Subgroup G) ⊓ (L₁ ⊓ N) = R ⊓ (L₁ ⊓ N) :=
    le_antisymm (le_inf ((inf_le_inf_left _ inf_le_right).trans hTNR) inf_le_right)
      (inf_le_inf_right _ hRT)
  rw [hTR] at hS2
  have hS3 := isSylowOf_sup_of_inf hRN₁ (T.isPGroup'.to_le hRT) hS2
  have hconj : ∀ l ∈ L₁, ∀ y ∈ (L₁ ⊓ N) ⊔ R, l * y * l⁻¹ ∈ (L₁ ⊓ N) ⊔ R := by
    intro l hl y hy
    have hy' : y ∈ (((L₁ ⊓ N) ⊔ R : Subgroup G) : Set G) := hy
    rw [coe_mul_of_right_le_normalizer_left _ _ hRN₁, Set.mem_mul] at hy'
    obtain ⟨n, hn, r, hr, rfl⟩ := hy'
    have hn' : l * n * l⁻¹ ∈ L₁ ⊓ N :=
      (mem_normalizer_iff.mp (mem_normalizer_inf (hL₁L₁ hl) (hL₁N hl)) n).mp hn
    have hc : l * r * l⁻¹ * r⁻¹ ∈ L₁ ⊓ N := by
      refine mem_inf.mpr ⟨?_, hRc r hr l (hL₁L hl)⟩
      have h1 : r * l⁻¹ * r⁻¹ ∈ L₁ :=
        (mem_normalizer_iff.mp (hRL₁ hr) l⁻¹).mp (inv_mem hl)
      rw [show l * r * l⁻¹ * r⁻¹ = l * (r * l⁻¹ * r⁻¹) by group]
      exact mul_mem hl h1
    rw [show l * (n * r) * l⁻¹ = (l * n * l⁻¹) * (l * r * l⁻¹ * r⁻¹) * r by group]
    exact mul_mem (mul_mem (mem_sup_left hn') (mem_sup_left hc)) (mem_sup_right hr)
  have hconjR : ∀ r ∈ R, ∀ y ∈ (L₁ ⊓ N) ⊔ R, r * y * r⁻¹ ∈ (L₁ ⊓ N) ⊔ R := by
    intro r hr y hy
    have hy' : y ∈ (((L₁ ⊓ N) ⊔ R : Subgroup G) : Set G) := hy
    rw [coe_mul_of_right_le_normalizer_left _ _ hRN₁, Set.mem_mul] at hy'
    obtain ⟨n, hn, r', hr', rfl⟩ := hy'
    have hn' : r * n * r⁻¹ ∈ L₁ ⊓ N := (mem_normalizer_iff.mp (hRN₁ hr) n).mp hn
    rw [show r * (n * r') * r⁻¹ = (r * n * r⁻¹) * (r * r' * r⁻¹) by group]
    exact mul_mem (mem_sup_left hn') (mem_sup_right (mul_mem (mul_mem hr hr') (inv_mem hr)))
  have hXY : L₁ ⊔ R ≤ normalizer (((L₁ ⊓ N) ⊔ R : Subgroup G) : Set G) := by
    refine sup_le (fun l hl => mem_normalizer_of_conj_mem (hconj l hl) ?_)
      (fun r hr => mem_normalizer_of_conj_mem (hconjR r hr) ?_)
    · intro y hy
      simpa using hconj l⁻¹ (inv_mem hl) y hy
    · intro y hy
      simpa using hconjR r⁻¹ (inv_mem hr) y hy
  have hYX : (L₁ ⊓ N) ⊔ R ≤ L₁ ⊔ R := sup_le_sup_right inf_le_left R
  have hFr := frattini_le_sup hYX hXY hS3
  refine le_antisymm (fun l hl => ?_) (sup_le inf_le_left inf_le_left)
  have hl' : l ∈ ((((L₁ ⊓ N) ⊔ R) ⊔ ((L₁ ⊔ R) ⊓ normalizer (R : Set G)) : Subgroup G) :
      Set G) := hFr (mem_sup_left hl)
  rw [coe_mul_of_right_le_normalizer_left _ _ (inf_le_left.trans hXY), Set.mem_mul] at hl'
  obtain ⟨y, hy, a, ha, rfl⟩ := hl'
  have hy' : y ∈ (((L₁ ⊓ N) ⊔ R : Subgroup G) : Set G) := hy
  rw [coe_mul_of_right_le_normalizer_left _ _ hRN₁, Set.mem_mul] at hy'
  obtain ⟨n, hn, r, hr, rfl⟩ := hy'
  obtain ⟨haX, haN⟩ := mem_inf.mp ha
  have haX' : a ∈ ((L₁ ⊔ R : Subgroup G) : Set G) := haX
  rw [coe_mul_of_right_le_normalizer_left _ _ hRL₁, Set.mem_mul] at haX'
  obtain ⟨l', hl', r', hr', rfl⟩ := haX'
  have hl'N : l' ∈ normalizer (R : Set G) := by
    have := mul_mem haN (inv_mem (hRR hr'))
    rwa [mul_inv_cancel_right] at this
  set a₁ := r * l' * r⁻¹ with ha₁
  have ha₁L : a₁ ∈ L₁ := (mem_normalizer_iff.mp (hRL₁ hr) l').mp hl'
  have ha₁N : a₁ ∈ normalizer (R : Set G) :=
    mul_mem (mul_mem (hRR hr) hl'N) (inv_mem (hRR hr))
  have hr'' : r * r' ∈ L₁ := by
    have e : r * r' = a₁⁻¹ * n⁻¹ * (n * r * (l' * r')) := by rw [ha₁]; group
    rw [e]
    exact mul_mem (mul_mem (inv_mem ha₁L) (inv_mem (mem_inf.mp hn).1)) hl
  have hA : a₁ * (r * r') ∈ L₁ ⊓ normalizer (R : Set G) :=
    mem_inf.mpr ⟨mul_mem ha₁L hr'', mul_mem ha₁N (hRR (mul_mem hr hr'))⟩
  rw [show n * r * (l' * r') = n * (a₁ * (r * r')) by rw [ha₁]; group]
  exact mul_mem (mem_sup_left hn) (mem_sup_right hA)

theorem residual_of_radical_supplement [Finite G] {L A : Subgroup G}
    (hsimple : IsSimpleGroup (L ⧸ CFSG.solvableRadical L))
    (hnab : ∃ a b : L ⧸ CFSG.solvableRadical L, a * b ≠ b * a) (hAL : A ≤ L)
    (hLNA : L = (CFSG.solvableRadical L).map L.subtype ⊔ A) :
    CFSG.IsCComponent (CFSG.perfectResidual A) ∧
      L = (CFSG.solvableRadical L).map L.subtype ⊔ (CFSG.perfectResidual A).map A.subtype := by
  classical
  have hchar := (CFSG.QuasithinUnique.Setup.Offender.solvableRadical_characterization L).1
  set N := (CFSG.solvableRadical L).map L.subtype with hN
  have hNmem : ∀ y : L, (y : G) ∈ N ↔ y ∈ CFSG.solvableRadical L := fun y =>
    mem_map_iff_mem L.subtype_injective
  have hNL : N ≤ L := map_subtype_le _
  have hLN : L ≤ normalizer (N : Set G) :=
    le_normalizer.trans (LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic _)
  have hAN : A ≤ normalizer (N : Set G) := hAL.trans hLN
  set D := N.subgroupOf A with hD
  have hDn : D.Normal := ⟨fun x hx a => by
    rw [hD, mem_subgroupOf] at hx ⊢
    simp only [coe_mul, coe_inv]
    exact (mem_normalizer_iff.mp (hAN a.2) x).mp hx⟩
  have hNsolv : Group.IsSolvable N := by
    have : Group.IsSolvable (CFSG.solvableRadical L) :=
      CFSG.ABGLocalTools.solvableRadical_isSolvable
    exact Group.isSolvable_of_surjective
      (f := ((CFSG.solvableRadical L).equivMapOfInjective L.subtype
        L.subtype_injective).toMonoidHom) (MulEquiv.surjective _)
  have hDsolv : Group.IsSolvable D := by
    let f : D →* N :=
      { toFun := fun x => ⟨((x : A) : G), x.2⟩
        map_one' := rfl
        map_mul' := fun _ _ => rfl }
    refine Group.isSolvable_of_isSolvable_injective (f := f) fun x y h => ?_
    have h' := congrArg Subtype.val h
    exact Subtype.ext (Subtype.ext h')
  let φ : A →* L ⧸ CFSG.solvableRadical L := (QuotientGroup.mk' _).comp (inclusion hAL)
  have hφs : Function.Surjective φ := by
    intro q
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective _ q
    have hy : (y : G) ∈ ((N ⊔ A : Subgroup G) : Set G) := by
      rw [← hLNA]
      exact y.2
    rw [coe_mul_of_right_le_normalizer_left N A hAN, Set.mem_mul] at hy
    obtain ⟨n, hn, a, ha, hna⟩ := hy
    refine ⟨⟨a, ha⟩, ?_⟩
    change QuotientGroup.mk' _ (inclusion hAL ⟨a, ha⟩) = QuotientGroup.mk' _ y
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq, ← hNmem]
    have e : (((inclusion hAL ⟨a, ha⟩)⁻¹ * y : L) : G) = a⁻¹ * n * a := by
      simp only [coe_mul, coe_inv, coe_inclusion]
      rw [← hna]
      group
    rw [e]
    have h1 := (mem_normalizer_iff.mp (hAN (inv_mem ha)) n).mp hn
    rwa [inv_inv] at h1
  have hφker : φ.ker = D := by
    ext a
    rw [MonoidHom.mem_ker, hD, mem_subgroupOf]
    change QuotientGroup.mk' _ (inclusion hAL a) = 1 ↔ _
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, ← hNmem]
    rfl
  have eAD : (A ⧸ D) ≃* (L ⧸ CFSG.solvableRadical L) :=
    (QuotientGroup.quotientMulEquivOfEq hφker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective φ hφs)
  have hADs : IsSimpleGroup (A ⧸ D) := MulEquiv.isSimpleGroup eAD
  have hTopC : CFSG.IsCComponent (⊤ : Subgroup (A ⧸ D)) := by
    obtain ⟨a, b, hab⟩ := hnab
    refine isCComponent_top_of_isSimpleGroup ⟨eAD.symm a, eAD.symm b, fun h => hab ?_⟩
    have h1 := congrArg eAD h
    simpa using h1
  obtain ⟨-, hbij⟩ := Ccomponent_solvable_quotient_bijection D hDsolv
  obtain ⟨hK'C, hK'map⟩ := hbij ⊤ hTopC
  rw [comap_top, perfectResidual_top_map_subtype] at hK'C hK'map
  refine ⟨hK'C, le_antisymm (fun l hl => ?_) (sup_le hNL ((map_subtype_le _).trans hAL))⟩
  have hl' : l ∈ ((N ⊔ A : Subgroup G) : Set G) := by
    rw [← hLNA]
    exact hl
  rw [coe_mul_of_right_le_normalizer_left N A hAN, Set.mem_mul] at hl'
  obtain ⟨n, hn, a, ha, rfl⟩ := hl'
  have h1 : QuotientGroup.mk' D ⟨a, ha⟩ ∈ (CFSG.perfectResidual A).map (QuotientGroup.mk' D) := by
    rw [hK'map]
    exact mem_top _
  obtain ⟨k, hk, hka⟩ := h1
  have h2 := QuotientGroup.eq.mp hka
  rw [hD, mem_subgroupOf] at h2
  have e : n * a = n * (k : G) * ((k : G)⁻¹ * a) := by group
  rw [e]
  refine mul_mem (mul_mem (mem_sup_left hn) (mem_sup_right ⟨k, hk, rfl⟩)) (mem_sup_left ?_)
  simpa using h2

end General

variable {G : Type} [Group G] [Finite G]

theorem inf_centralizer_qtnqU {T L M : Subgroup G} (h : QTNQ T L M) :
    L ⊓ centralizer (qtnqU L M : Set G) = (CFSG.solvableRadical L).map L.subtype := by
  classical
  obtain ⟨-, -, -, -, ⟨-, hUM, hUn, hUe⟩, -⟩ :=
    NQTerm.nonquasisimple_normalizer_internal_module_properties h
  have hUc := (SteinbergBM.elementaryAbelian_two_facts hUe).1
  have hUV := NQSetup.qtnqU_le_qtnqVc h
  have hchar := (CFSG.QuasithinUnique.Setup.Offender.solvableRadical_characterization L).1
  have hLU : L ≤ normalizer (qtnqU L M : Set G) :=
    h.l_le.trans ((normal_subgroupOf_iff_le_normalizer hUM).mp hUn)
  have hDcent : (CFSG.solvableRadical L).map L.subtype ≤ L ⊓ centralizer (qtnqU L M : Set G) := by
    rw [← h.centralizer_eq_radical]
    exact inf_le_inf_left _ (centralizer_le hUV)
  refine le_antisymm ?_ hDcent
  set D := (CFSG.solvableRadical L).map L.subtype with hD
  set A₀ := L ⊓ centralizer (qtnqU L M : Set G) with hA₀
  have hA₀L : A₀ ≤ L := inf_le_left
  have hX : ∀ x ∈ A₀, ∀ v ∈ qtnqVc M, v⁻¹ * (x * v * x⁻¹) ∈ qtnqU L M := by
    intro x hx v hv
    have h1 := commutator_mem_commutator (inv_mem hv) (mem_inf.mp hx).1
    rw [commutatorElement_def, inv_inv] at h1
    rwa [show v⁻¹ * (x * v * x⁻¹) = v⁻¹ * x * v * x⁻¹ by group]
  have hcomm : ∀ a ∈ A₀, ∀ b ∈ A₀, a * b * a⁻¹ * b⁻¹ ∈ D := by
    intro a ha b hb
    rw [hD, ← h.centralizer_eq_radical]
    have haL := (mem_inf.mp ha).1
    have hbL := (mem_inf.mp hb).1
    exact mem_inf.mpr ⟨mul_mem (mul_mem (mul_mem haL hbL) (inv_mem haL)) (inv_mem hbL),
      commutator_mem_centralizer_of_stability hUc inf_le_right hX ha hb⟩
  have hLD : L ≤ normalizer (D : Set G) :=
    le_normalizer.trans (LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic _)
  have hDn : (D.subgroupOf A₀).Normal := ⟨fun x hx a => by
    rw [mem_subgroupOf] at hx ⊢
    simp only [coe_mul, coe_inv]
    exact (mem_normalizer_iff.mp (hLD (hA₀L a.2)) x).mp hx⟩
  have hDs : Group.IsSolvable D := by
    have : Group.IsSolvable (CFSG.solvableRadical L) :=
      CFSG.ABGLocalTools.solvableRadical_isSolvable
    exact Group.isSolvable_of_surjective
      (f := ((CFSG.solvableRadical L).equivMapOfInjective L.subtype
        L.subtype_injective).toMonoidHom) (MulEquiv.surjective _)
  have hquot : ∀ x y : A₀ ⧸ D.subgroupOf A₀, x * y = y * x := by
    intro x y
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective x
    obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective y
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq, mem_subgroupOf]
    have e : (((a * b)⁻¹ * (b * a) : A₀) : G) =
        (b : G)⁻¹ * (a : G)⁻¹ * (b : G)⁻¹⁻¹ * (a : G)⁻¹⁻¹ := by
      simp only [coe_mul, coe_inv]
      group
    rw [e]
    exact hcomm _ (inv_mem b.2) _ (inv_mem a.2)
  have : Group.IsSolvable (A₀ ⧸ D.subgroupOf A₀) := Group.isSolvable_of_comm hquot
  have hA₀s : Group.IsSolvable A₀ :=
    Group.isSolvable_of_ker_le_range (inclusion hDcent) (QuotientGroup.mk' (D.subgroupOf A₀))
      fun x hx => by
        rw [QuotientGroup.ker_mk', mem_subgroupOf] at hx
        exact ⟨⟨x, hx⟩, rfl⟩
  have hA₀n : (A₀.subgroupOf L).Normal := by
    refine (normal_subgroupOf_iff_le_normalizer hA₀L).mpr fun l hl => ?_
    refine mem_normalizer_inf (le_normalizer hl) ?_
    rw [mem_normalizer_iff]
    intro x
    have hlU := hLU hl
    have hlU' := hLU (inv_mem hl)
    constructor
    · intro hx
      rw [mem_centralizer_iff] at hx ⊢
      intro u hu
      have hu' : l⁻¹ * u * l⁻¹⁻¹ ∈ qtnqU L M := (mem_normalizer_iff.mp hlU' u).mp hu
      rw [inv_inv] at hu'
      have h1 := hx _ hu'
      calc u * (l * x * l⁻¹) = l * (l⁻¹ * u * l * x) * l⁻¹ := by group
        _ = l * (x * (l⁻¹ * u * l)) * l⁻¹ := by rw [h1]
        _ = l * x * l⁻¹ * u := by group
    · intro hx
      rw [mem_centralizer_iff] at hx ⊢
      intro u hu
      have hu' : l * u * l⁻¹ ∈ qtnqU L M := (mem_normalizer_iff.mp hlU u).mp hu
      have h1 := hx _ hu'
      calc u * x = l⁻¹ * ((l * u * l⁻¹) * (l * x * l⁻¹)) * l := by group
        _ = l⁻¹ * ((l * x * l⁻¹) * (l * u * l⁻¹)) * l := by rw [h1]
        _ = x * u := by group
  rw [hD, ← solvRad_eq_map_solvableRadical]
  exact le_solvRad hA₀L hA₀n hA₀s

theorem nq_TI_weak_closure_local_normalizer_witness {T L M : Subgroup G} (h : QTNQ T L M)
    (hTI : ∀ g : G, qtnqU L M ⊓ CFSG.conjugate (qtnqU L M) g = ⊥ ∨
      CFSG.conjugate (qtnqU L M) g = qtnqU L M)
    {W R A K : Subgroup G}
    (hW : W = sSup {X : Subgroup G | (∃ g : G, CFSG.conjugate (qtnqU L M) g = X) ∧ X ≤ T})
    (hR : R = T ⊓ centralizer (qtnqU L M : Set G)) (hA : A = L ⊓ normalizer (W : Set G))
    (hK : K = (CFSG.perfectResidual A).map A.subtype) :
    qtnqU L M ≠ ⊥ ∧ qtnqU L M ≤ W ∧ W ≤ R ∧
      W = sSup {X : Subgroup G | (∃ g : G, CFSG.conjugate (qtnqU L M) g = X) ∧ X ≤ R} ∧
      ⁅W, qtnqU L M⁆ = ⊥ ∧
      L ⊓ centralizer (qtnqU L M : Set G) = (CFSG.solvableRadical L).map L.subtype ∧
      L = (CFSG.solvableRadical L).map L.subtype ⊔ (L ⊓ normalizer (R : Set G)) ∧
      L = (CFSG.solvableRadical L).map L.subtype ⊔ A ∧
      L = (CFSG.solvableRadical L).map L.subtype ⊔ K ∧
      T ≤ normalizer (K : Set G) ∧ quasithinIsLocal T K ∧ K ⊔ T ≤ normalizer (W : Set G) ∧
      (quasithinIsMaxTwoLocal M ∧ K ⊔ T ≤ M ∧
          (∀ M' : Subgroup G, quasithinIsMaxTwoLocal M' → K ⊔ T ≤ M' → M' = M) →
        normalizer (W : Set G) ≤ M) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, -, -, -, ⟨hU1, hUM, hUn, hUe⟩, -⟩ :=
    NQTerm.nonquasisimple_normalizer_internal_module_properties h
  have hchar := (CFSG.QuasithinUnique.Setup.Offender.solvableRadical_characterization L).1
  have hUT : qtnqU L M ≤ T := NQSetup.qtnqU_le_t h
  have hT2 : IsPGroup 2 T := h.sylow.1
  have hMU : M ≤ normalizer (qtnqU L M : Set G) := (normal_subgroupOf_iff_le_normalizer hUM).mp hUn
  have hTU : T ≤ normalizer (qtnqU L M : Set G) := h.t_le.trans hMU
  have hLU : L ≤ normalizer (qtnqU L M : Set G) := h.l_le.trans hMU
  have hTL : T ≤ normalizer (L : Set G) := h.eq_normalizer ▸ h.t_le
  have hCL := inf_centralizer_qtnqU h
  have hconjC : ∀ X ∈ {X : Subgroup G | (∃ g : G, CFSG.conjugate (qtnqU L M) g = X) ∧ X ≤ T},
      X ≤ R := by
    rintro X ⟨⟨g, rfl⟩, hXT⟩
    rw [hR]
    exact le_inf hXT (conjugate_le_centralizer_of_TI hUe hU1 hTI hT2 hUT hTU hXT)
  have hWR : W ≤ R := hW ▸ sSup_le hconjC
  have hRT : R ≤ T := hR ▸ inf_le_left
  have hRC : R ≤ centralizer (qtnqU L M : Set G) := hR ▸ inf_le_right
  have hUW : qtnqU L M ≤ W := by
    rw [hW]
    refine le_sSup ⟨⟨1, ?_⟩, hUT⟩
    ext x
    rw [BlueprintB2.mem_conjugate_iff, one_mul, inv_one, mul_one]
  have hWWR : W = sSup {X : Subgroup G | (∃ g : G, CFSG.conjugate (qtnqU L M) g = X) ∧ X ≤ R} := by
    rw [hW]
    congr 1
    ext X
    exact and_congr_right fun hX =>
      ⟨fun hXT => hconjC X ⟨hX, hXT⟩, fun hXR => hXR.trans hRT⟩
  have hWU : ⁅W, qtnqU L M⁆ = ⊥ := commutator_eq_bot_iff_le_centralizer.mpr (hWR.trans hRC)
  have hDL : (CFSG.solvableRadical L).map L.subtype ≤ L := map_subtype_le _
  have hLD : L ≤ normalizer ((CFSG.solvableRadical L).map L.subtype : Set G) :=
    le_normalizer.trans (LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic _)
  let T' : Sylow 2 G := h.sylow.1.toSylow h.sylow.2
  have hT' : (T' : Subgroup G) = T := IsPGroup.toSylow_coe _ _
  have hRc : ∀ r ∈ R, ∀ l ∈ L, l * r * l⁻¹ * r⁻¹ ∈ (CFSG.solvableRadical L).map L.subtype := by
    intro r hr l hl
    rw [← hCL]
    have hrL : r * l⁻¹ * r⁻¹ ∈ L := (mem_normalizer_iff.mp (hTL (hRT hr)) l⁻¹).mp (inv_mem hl)
    refine mem_inf.mpr ⟨?_, ?_⟩
    · rw [show l * r * l⁻¹ * r⁻¹ = l * (r * l⁻¹ * r⁻¹) by group]
      exact mul_mem hl hrL
    · rw [mem_centralizer_iff]
      intro u hu
      have hu' : l⁻¹ * u * l⁻¹⁻¹ ∈ qtnqU L M :=
        (mem_normalizer_iff.mp (hLU (inv_mem hl)) u).mp hu
      rw [inv_inv] at hu'
      have h1 := mem_centralizer_iff.mp (hRC hr) _ hu'
      have h2 := mem_centralizer_iff.mp (hRC hr) _ hu
      calc u * (l * r * l⁻¹ * r⁻¹) = l * ((l⁻¹ * u * l) * r) * l⁻¹ * r⁻¹ := by group
        _ = l * (r * (l⁻¹ * u * l)) * l⁻¹ * r⁻¹ := by rw [h1]
        _ = l * r * l⁻¹ * (u * r⁻¹) := by group
        _ = l * r * l⁻¹ * (r⁻¹ * u) := by
          rw [show u * r⁻¹ = r⁻¹ * (r * u) * r⁻¹ by group, ← h2]
          group
        _ = l * r * l⁻¹ * r⁻¹ * u := by group
  have hTNR : (T' : Subgroup G) ⊓ (CFSG.solvableRadical L).map L.subtype ≤ R := by
    rw [hT', hR]
    refine inf_le_inf_left _ ?_
    rw [← hCL]
    exact inf_le_right
  have hFr := supplement_frattini_of_le_normalizer T' (hT' ▸ hTL.trans
    (LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic _)) hLD (hT' ▸ hRT) hTNR
    hRc le_rfl (hT' ▸ hTL)
  rw [inf_eq_right.mpr hDL] at hFr
  have hRW : normalizer (R : Set G) ≤ normalizer (W : Set G) := by
    rw [hWWR]
    exact normalizer_le_normalizer_weakClosure _ R
  have hAL : A ≤ L := hA ▸ inf_le_left
  have hLDA : L = (CFSG.solvableRadical L).map L.subtype ⊔ A := by
    refine le_antisymm ?_ (sup_le hDL hAL)
    conv_lhs => rw [hFr]
    rw [hA]
    exact sup_le_sup_left (inf_le_inf_left _ hRW) _
  have hLc : L ∈ cComp (L ⊔ T) := h.maximal_local.1.2.1
  have hLtop : CFSG.IsCComponent (⊤ : Subgroup L) := by
    have h1 := subgroupOf_mem_cComp (cComp_mem_of_le hLc le_rfl le_sup_left)
    rw [subgroupOf_self] at h1
    exact mem_cComp_top_iff_isCComponent.mp h1
  obtain ⟨hsimple, hnab⟩ := simple_radical_quotient_of_isCComponent_top hLtop
  obtain ⟨hK'C, hLDK⟩ := residual_of_radical_supplement hsimple hnab hAL hLDA
  rw [← hK] at hLDK
  have hKA : K ∈ cComp A := by
    rw [hK]
    exact map_subtype_mem_cComp (mem_cComp_top_iff_isCComponent.mpr hK'C)
  have hKAle : K ≤ A := le_of_mem_cComp hKA
  have hTW : T ≤ normalizer (W : Set G) := by
    rw [hW]
    exact le_normalizer.trans (normalizer_le_normalizer_weakClosure _ T)
  have hNN : normalizer (W : Set G) ≤
      normalizer ((normalizer (W : Set G) : Subgroup G) : Set G) := le_normalizer
  have hTA : T ≤ normalizer (A : Set G) := fun t ht => by
    rw [hA]
    exact mem_normalizer_inf (hTL ht) (hNN (hTW ht))
  have hTK : T ≤ normalizer (K : Set G) := by
    have hKc : K = perfectCore A := by
      rw [hK, perfectCore_eq_map_perfectResidual]
    rw [hKc]
    exact hTA.trans (normalizer_le_normalizer_perfectCore A)
  have hKK : K ∈ cComp K := by
    rw [cComp_self_eq_singleton hKA]
    rfl
  have hKTn : K ⊔ T ≤ normalizer (K : Set G) := sup_le le_normalizer hTK
  have hKc : K ∈ cComp (K ⊔ T) := cComp_mem_of_subnormal
    (A3.subnormal_of_normal le_sup_left ((normal_subgroupOf_iff_le_normalizer le_sup_left).mpr
      hKTn)) hKK
  have hAW : A ≤ normalizer (W : Set G) := hA ▸ inf_le_right
  have hKTW : K ⊔ T ≤ normalizer (W : Set G) := sup_le (hKAle.trans hAW) hTW
  have hWne : W ≠ ⊥ := fun h0 => hU1 (le_bot_iff.mp (h0 ▸ hUW))
  have hW2 : IsPGroup 2 W := hT2.to_le (hWR.trans hRT)
  have hWKT : W ≤ K ⊔ T := (hWR.trans hRT).trans le_sup_right
  have hloc : quasithinIsLocal T K := by
    refine ⟨hT2, hKc, fun h2 => h.sylow.2 (h2.trans (relIndex_dvd_index_of_le le_sup_right)),
      fun h0 => hWne (le_bot_iff.mp ?_)⟩
    rw [← h0]
    exact le_pCoreOf_of_subgroupOf_normal hWKT
      ((normal_subgroupOf_iff_le_normalizer hWKT).mpr hKTW) hW2
  refine ⟨hU1, hUW, hWR, hWWR, hWU, hCL, hFr, hLDA, hLDK, hTK, hloc, hKTW, ?_⟩
  rintro ⟨-, -, huniq⟩
  obtain ⟨M', hM', hle⟩ := exists_maxTwoLocal_ge_of_isTwoLocal ⟨W, hWne, hW2, rfl⟩
  rw [← huniq M' hM' (hKTW.trans hle)]
  exact hle

end CFSG.Quasithin.H13.NQBlock
