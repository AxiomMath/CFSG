module

public import CFSG.RankThree.PartTwo.Sec3.Sims321Module
public import CFSG.RankThree.PartTwo.Sec3.Sims321Singer
public import CFSG.RankThree.PartTwo.Sec3.Sims321Transv
public import CFSG.RankThree.PartTwo.Sec3.Sims321Action
public import CFSG.RankThree.PartTwo.Sec3.Sims321Group
public import CFSG.Timmesfeld.Orders.Bang
public import CFSG.RankThree.PartOne.KC.LinearSubfieldPointwise

public section

namespace CFSG.RankThree.PartTwo.Sec3.Sims321

open scoped MatrixGroups
open Matrix CFSG.RankThree.FFModules CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.ComponentClassification CFSG CFSG.RankThree.PartTwo

@[expose] noncomputable def theta (n : ℕ) :
    SL(3, GaloisField 2 n) →* MulAut (projectiveSL 3 (GaloisField 2 n)) :=
  MulAut.conj.comp (proj 3 (GaloisField 2 n))

theorem conj_injective_projectiveSL (n : ℕ) :
    Function.Injective (MulAut.conj : projectiveSL 3 (GaloisField 2 n) →* _) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro p hp
  rw [MonoidHom.mem_ker] at hp
  have hc : p ∈ Subgroup.center (projectiveSL 3 (GaloisField 2 n)) := by
    rw [Subgroup.mem_center_iff]
    intro z
    have h1 := congrArg (fun α : MulAut (projectiveSL 3 (GaloisField 2 n)) => α z) hp
    simp only [MulAut.conj_apply, MulAut.one_apply] at h1
    calc z * p = (p * z * p⁻¹) * p := by rw [h1]
      _ = p * z := by group
  rwa [center_projectiveSL_eq_bot] at hc

theorem theta_injective {n : ℕ} (hn : Odd n) : Function.Injective (theta n) :=
  (conj_injective_projectiveSL n).comp (proj_injective_of_odd hn)

theorem omegaZOf_facts {G : Type*} [Group G] (Q : Subgroup G) :
    (∀ x ∈ omegaZOf Q, ∀ y ∈ omegaZOf Q, x * y = y * x) ∧ (∀ x ∈ omegaZOf Q, x * x = 1) ∧
      omegaZOf Q ≤ Q ∧ ∀ x ∈ omegaZOf Q, ∀ q ∈ Q, q * x = x * q := by
  have key : ∀ x ∈ omegaZOf Q, x ∈ Q ∧ x * x = 1 ∧ ∀ q ∈ Q, q * x = x * q := by
    rintro _ ⟨w, ⟨⟨c, hc, hcw⟩, hw2⟩, rfl⟩
    refine ⟨w.2, ?_, fun q hq => ?_⟩
    · have := congrArg Subtype.val hw2
      rwa [Subgroup.coe_pow, pow_two] at this
    · have h1 := Subgroup.mem_center_iff.mp hc ⟨⟨q, hq⟩, Subgroup.mem_top _⟩
      have h2 := congrArg (fun z : (⊤ : Subgroup Q) => ((z : Q) : G)) h1
      simp only [Subgroup.coe_mul] at h2
      rw [← hcw]
      exact h2
  refine ⟨fun x hx y hy => ?_, fun x hx => (key x hx).2.1, fun x hx => (key x hx).1,
    fun x hx => (key x hx).2.2⟩
  exact ((key y hy).2.2 x (key x hx).1)

theorem mem_omegaOneCenter_top {S : Type*} [Group S] (z : S) :
    z ∈ CFSG.omegaOneCenter (⊤ : Subgroup S) ↔ z ∈ Subgroup.center S ∧ z ^ 2 = 1 := by
  constructor
  · rintro ⟨⟨w, hw, rfl⟩, hz⟩
    refine ⟨Subgroup.mem_center_iff.mpr fun y => ?_, hz⟩
    exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hw ⟨y, Subgroup.mem_top y⟩)
  · rintro ⟨hz, hz2⟩
    refine ⟨⟨⟨z, Subgroup.mem_top z⟩, Subgroup.mem_center_iff.mpr fun y => Subtype.ext ?_, rfl⟩,
      hz2⟩
    exact Subgroup.mem_center_iff.mp hz y

instance omegaOneCenter_top_characteristic' {S : Type*} [Group S] :
    (CFSG.omegaOneCenter (⊤ : Subgroup S)).Characteristic := by
  rw [Subgroup.characteristic_iff_map_le]
  rintro φ _ ⟨z, hz, rfl⟩
  rw [SetLike.mem_coe, mem_omegaOneCenter_top] at hz
  rw [mem_omegaOneCenter_top]
  refine ⟨Subgroup.mem_center_iff.mpr fun y => ?_, by
    change φ z ^ 2 = 1
    rw [← map_pow, hz.2, map_one]⟩
  obtain ⟨y, rfl⟩ := φ.surjective y
  change φ y * φ z = φ z * φ y
  rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hz.1 y]

theorem le_normalizer_omegaZOf {G : Type*} [Group G] (X : Subgroup G) :
    X ≤ Subgroup.normalizer (omegaZOf (CFSG.Open.pCoreOf 2 X) : Set G) :=
  (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 X).trans
    (CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic _)

theorem pCoreOf_le_of_sylow {G : Type*} [Group G] [Finite G] {T X : Subgroup G}
    (hT : CFSG.ABGLocalTools.IsSylowOf 2 T X) : CFSG.Open.pCoreOf 2 X ≤ T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S, rfl⟩ := hT
  have : (CFSG.pCore 2 X).Normal := CFSG.pCore_normal
  exact Subgroup.map_mono (CFSG.pCore_isPGroup.le_sylow_of_normal S)

theorem mulAut_mul_conj_mul_inv {P : Type*} [Group P] (α : MulAut P) (z : P) :
    α * MulAut.conj z * α⁻¹ = MulAut.conj (α z) := by
  ext p
  simp only [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv, MulAut.apply_inv_self]

theorem orderOf_two_eq_of_ppd {n r : ℕ} (hr : r.Prime) (hr3 : r ∣ 2 ^ (3 * n) - 1)
    (hrk : ∀ k : ℕ, 0 < k → k < 3 * n → ¬ r ∣ 2 ^ k - 1) (hn : 0 < n) :
    orderOf (2 : ZMod r) = 3 * n := by
  have : Fact r.Prime := ⟨hr⟩
  have hpow : ∀ k, (2 : ZMod r) ^ k = 1 ↔ r ∣ 2 ^ k - 1 := by
    intro k
    have h1 : 1 ≤ 2 ^ k := Nat.one_le_two_pow
    rw [← ZMod.natCast_eq_zero_iff, Nat.cast_sub h1, Nat.cast_pow, Nat.cast_ofNat,
      Nat.cast_one, sub_eq_zero]
  rw [orderOf_eq_iff (by omega)]
  refine ⟨(hpow _).mpr hr3, fun m hm hm0 h => hrk m hm0 hm ((hpow m).mp h)⟩

section Main

variable {G : Type} [Group G] [Finite G] {X L T : Subgroup G} {n : ℕ}

@[expose] noncomputable def rhoX (hLN : X ≤ Subgroup.normalizer (L : Set G))
    (φ : L ⧸ CFSG.pCore 2 L ≃* CFSG.Assembly.RankThreeEven.projSL 3 (GaloisField 2 n)) :
    X →* MulAut (projectiveSL 3 (GaloisField 2 n)) :=
  (rho φ).comp (Subgroup.inclusion hLN)

variable (hLN : X ≤ Subgroup.normalizer (L : Set G))
  (φ : L ⧸ CFSG.pCore 2 L ≃* CFSG.Assembly.RankThreeEven.projSL 3 (GaloisField 2 n))

include φ in
theorem isSimpleGroup_quot : IsSimpleGroup (L ⧸ CFSG.pCore 2 L) := by
  have : IsSimpleGroup (projectiveSL 3 (GaloisField 2 n)) :=
    CFSG.RankThree.PartOne.KCLinearSubfield.isSimpleGroup_projectiveSL (n := 3) le_rfl
  exact (φ.trans (CFSG.RankThree.PartTwo.KFacts.L34.projSLEquivProjectiveSL 3 _)).isSimpleGroup

include φ in
theorem center_quot_eq_bot : Subgroup.center (L ⧸ CFSG.pCore 2 L) = ⊥ := by
  set e := φ.trans (CFSG.RankThree.PartTwo.KFacts.L34.projSLEquivProjectiveSL 3 (GaloisField 2 n))
  rw [eq_bot_iff]
  intro z hz
  have hez : e z ∈ Subgroup.center (projectiveSL 3 (GaloisField 2 n)) := by
    rw [Subgroup.mem_center_iff]
    intro w
    obtain ⟨w', rfl⟩ := e.surjective w
    rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hz w']
  rw [center_projectiveSL_eq_bot, Subgroup.mem_bot] at hez
  rw [Subgroup.mem_bot]
  exact e.injective (hez.trans (map_one e).symm)

theorem rhoX_eq_conj (x : X) (l : L) (h : (x : G) = l) :
    rhoX hLN φ x = MulAut.conj (psi φ l) :=
  rho_eq_conj φ ⟨x, hLN x.2⟩ l h

include hLN in
theorem rhoX_eq_one_of_mem (hL : L ∈ oTwoComponentsIn X) (x : X)
    (hx : (x : G) ∈ CFSG.Open.pCoreOf 2 X) : rhoX hLN φ x = 1 := by
  have hLX : L ≤ X := le_of_mem_oTwoComponentsIn hL
  refine (rho_eq_one_iff φ ⟨x, hLN x.2⟩).mpr fun l hl => ?_
  rw [← pCoreOf_inf_eq hL hLN]
  refine ⟨?_, ?_⟩
  · have h1 : (x : G) * l * (x : G)⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp (hLN x.2) l).mp hl
    exact L.mul_mem h1 (L.inv_mem hl)
  · have hQ := CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 X (hLX hl)
    have h2 : l * (x : G)⁻¹ * l⁻¹ ∈ CFSG.Open.pCoreOf 2 X :=
      (Subgroup.mem_normalizer_iff.mp hQ _).mp (Subgroup.inv_mem _ hx)
    have : (x : G) * l * (x : G)⁻¹ * l⁻¹ = (x : G) * (l * (x : G)⁻¹ * l⁻¹) := by group
    rw [this]
    exact Subgroup.mul_mem _ hx h2

theorem mem_of_rhoX_eq_one (hL : L ∈ oTwoComponentsIn X)
    (hT : CFSG.ABGLocalTools.IsSylowOf 2 T X) (hLT : L ⊔ T = X) (x : X)
    (hx : rhoX hLN φ x = 1) : (x : G) ∈ CFSG.Open.pCoreOf 2 X :=
  mem_pCoreOf_of_centralizes_quotient hL hLN hT hLT (center_quot_eq_bot φ) x.2
    ((rho_eq_one_iff φ ⟨x, hLN x.2⟩).mp hx)

theorem conj_eq_of_rhoX_eq (hL : L ∈ oTwoComponentsIn X)
    (hT : CFSG.ABGLocalTools.IsSylowOf 2 T X) (hLT : L ⊔ T = X) {x x' : X}
    (h : rhoX hLN φ x = rhoX hLN φ x') :
    ∀ v ∈ omegaZOf (CFSG.Open.pCoreOf 2 X), (x : G) * v * (x : G)⁻¹ = x' * v * (x' : G)⁻¹ := by
  intro v hv
  have h1 : rhoX hLN φ (x'⁻¹ * x) = 1 := by rw [map_mul, map_inv, h, inv_mul_cancel]
  have hq := mem_of_rhoX_eq_one hLN φ hL hT hLT _ h1
  obtain ⟨-, -, -, hQV⟩ := omegaZOf_facts (CFSG.Open.pCoreOf 2 X)
  have h2 := hQV v hv _ hq
  simp only [Subgroup.coe_mul, Subgroup.coe_inv] at h2
  calc (x : G) * v * (x : G)⁻¹ = (x' : G) * (((x' : G)⁻¹ * x) * v) * (x : G)⁻¹ := by group
    _ = (x' : G) * (v * ((x' : G)⁻¹ * x)) * (x : G)⁻¹ := by rw [h2]
    _ = x' * v * (x' : G)⁻¹ := by group

@[expose] noncomputable def imgSL (H : Subgroup G) : Subgroup SL(3, GaloisField 2 n) :=
  ((H.subgroupOf X).map (rhoX hLN φ)).comap (theta n)

theorem mem_imgSL {H : Subgroup G} {g : SL(3, GaloisField 2 n)} :
    g ∈ imgSL hLN φ H ↔ ∃ a : X, (a : G) ∈ H ∧ rhoX hLN φ a = theta n g := by
  simp only [imgSL, Subgroup.mem_comap, Subgroup.mem_map, Subgroup.mem_subgroupOf]

theorem exists_theta_eq (hL : L ∈ oTwoComponentsIn X) (x : X)
    (hx : (x : G) ∈ L ⊔ CFSG.Open.pCoreOf 2 X) : ∃ g, rhoX hLN φ x = theta n g := by
  have hLX : L ≤ X := le_of_mem_oTwoComponentsIn hL
  have hQX : CFSG.Open.pCoreOf 2 X ≤ X := CFSG.LieType.BorelTits.pCoreOf_le 2 X
  have hmem : (x : G) ∈ ((CFSG.Open.pCoreOf 2 X ⊔ L : Subgroup G) : Set G) := by
    rw [sup_comm]; exact hx
  rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ (hQX.trans hLN)] at hmem
  obtain ⟨q, hq, l, hl, hql⟩ := hmem
  obtain ⟨g, hg⟩ := proj_surjective 3 (GaloisField 2 n) (psi φ ⟨l, hl⟩)
  refine ⟨g, ?_⟩
  have hx' : x = (⟨q, hQX hq⟩ : X) * ⟨l, hLX hl⟩ := Subtype.ext hql.symm
  rw [hx', map_mul, rhoX_eq_one_of_mem hLN φ hL _ hq, one_mul,
    rhoX_eq_conj hLN φ _ ⟨l, hl⟩ rfl, theta, MonoidHom.comp_apply, hg]

theorem card_imgSL (hL : L ∈ oTwoComponentsIn X) (hT : CFSG.ABGLocalTools.IsSylowOf 2 T X)
    (hLT : L ⊔ T = X) (hn : Odd n) {H : Subgroup G} (hHX : H ≤ X)
    (hHLQ : H ≤ L ⊔ CFSG.Open.pCoreOf 2 X) :
    Nat.card (imgSL hLN φ H) = (H ⊓ CFSG.Open.pCoreOf 2 X).relIndex H := by
  set K := (H.subgroupOf X).map (rhoX hLN φ) with hK
  have hKθ : K ≤ (theta n).range := by
    rintro _ ⟨a, ha, rfl⟩
    obtain ⟨g, hg⟩ := exists_theta_eq hLN φ hL a (hHLQ (Subgroup.mem_subgroupOf.mp ha))
    exact ⟨g, hg.symm⟩
  have h1 : Nat.card (imgSL hLN φ H) = Nat.card K := by
    have e := (imgSL hLN φ H).equivMapOfInjective (theta n) (theta_injective hn)
    rw [Nat.card_congr e.toEquiv, imgSL, Subgroup.map_comap_eq, inf_of_le_right hKθ]
  have hker : (rhoX hLN φ).ker = (CFSG.Open.pCoreOf 2 X).subgroupOf X := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    exact ⟨mem_of_rhoX_eq_one hLN φ hL hT hLT x, rhoX_eq_one_of_mem hLN φ hL x⟩
  rw [h1, hK, ← Subgroup.relIndex_ker, hker, Subgroup.relIndex_subgroupOf hHX,
    Subgroup.inf_relIndex_left]

theorem imgSL_elem (hn : Odd n) {H : Subgroup G} (hH : IsElemTwo H) :
    (∀ g ∈ imgSL hLN φ H, g * g = 1) ∧
      ∀ g ∈ imgSL hLN φ H, ∀ g' ∈ imgSL hLN φ H, g * g' = g' * g := by
  refine ⟨fun g hg => ?_, fun g hg g' hg' => ?_⟩
  · obtain ⟨a, haH, ha⟩ := (mem_imgSL hLN φ).mp hg
    apply theta_injective hn
    have haa : a * a = 1 := Subtype.ext (hH.2 a haH)
    rw [map_mul, ← ha, ← map_mul, haa, map_one, map_one]
  · obtain ⟨a, haH, ha⟩ := (mem_imgSL hLN φ).mp hg
    obtain ⟨a', ha'H, ha'⟩ := (mem_imgSL hLN φ).mp hg'
    apply theta_injective hn
    have hc : a * a' = a' * a := Subtype.ext (hH.1 a haH a' ha'H)
    rw [map_mul, map_mul, ← ha, ← ha', ← map_mul, ← map_mul, hc]

theorem rhoX_not_inner (hL : L ∈ oTwoComponentsIn X) (hT : CFSG.ABGLocalTools.IsSylowOf 2 T X)
    (hLT : L ⊔ T = X) (x : X) (hx : (x : G) ∉ L ⊔ CFSG.Open.pCoreOf 2 X) (l : L) :
    rhoX hLN φ x ≠ MulAut.conj (psi φ l) := by
  intro h
  have hLX : L ≤ X := le_of_mem_oTwoComponentsIn hL
  set lX : X := ⟨l, hLX l.2⟩
  have h1 : rhoX hLN φ (x * lX⁻¹) = 1 := by
    rw [map_mul, map_inv, h, rhoX_eq_conj hLN φ lX l rfl, mul_inv_cancel]
  have hq := mem_of_rhoX_eq_one hLN φ hL hT hLT _ h1
  apply hx
  have : (x : G) = ((x : G) * (l : G)⁻¹) * l := by group
  rw [this]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_right hq) (Subgroup.mem_sup_left l.2)

theorem rhoX_outer (hL : L ∈ oTwoComponentsIn X) (hT : CFSG.ABGLocalTools.IsSylowOf 2 T X)
    (hLT : L ⊔ T = X) (hn : Odd n) (x : X) (hxT : (x : G) ∈ T)
    (hx : (x : G) ∉ L ⊔ CFSG.Open.pCoreOf 2 X) :
    ∃ A₀ : GL (Fin 3) (GaloisField 2 n),
      rhoX hLN φ x = conjAut 3 (GaloisField 2 n) A₀ * dualAut 3 (GaloisField 2 n) := by
  obtain ⟨a, ha⟩ := hT.isPGroup ⟨x, hxT⟩
  have hxa : x ^ 2 ^ a = 1 := by
    apply Subtype.ext
    have := congrArg Subtype.val ha
    simpa using this
  refine rho_eq_conjAut_mul_dualAut φ hn ⟨x, hLN x.2⟩ ⟨a, ?_⟩
    (fun l => rhoX_not_inner hLN φ hL hT hLT x hx l)
  change (rhoX hLN φ x) ^ 2 ^ a = 1
  rw [← map_pow, hxa, map_one]

theorem le_of_isSylowOf' {T X : Subgroup G} (hT : CFSG.ABGLocalTools.IsSylowOf 2 T X) : T ≤ X := by
  obtain ⟨S, rfl⟩ := hT
  exact Subgroup.map_subtype_le _

include hLN φ in
theorem relIndex_inf_sup_le_two (hL : L ∈ oTwoComponentsIn X)
    (hT : CFSG.ABGLocalTools.IsSylowOf 2 T X) (hLT : L ⊔ T = X) (hn : Odd n) {A : Subgroup G}
    (hA : A ∈ famG T 0) {t : G} (htA : t ∈ A) (htLQ : t ∉ L ⊔ CFSG.Open.pCoreOf 2 X) :
    (A ⊓ (L ⊔ CFSG.Open.pCoreOf 2 X)).relIndex A ≤ 2 := by
  classical
  obtain ⟨hAT, hA2, -⟩ := mem_famG.mp hA
  have hLX : L ≤ X := le_of_mem_oTwoComponentsIn hL
  have hAX : A ≤ X := hAT.trans (le_of_isSylowOf' hT)
  have key : ∀ a ∈ A, a ∉ L ⊔ CFSG.Open.pCoreOf 2 X → a * t⁻¹ ∈ L ⊔ CFSG.Open.pCoreOf 2 X := by
    intro a haA haLQ
    obtain ⟨B₁, hB₁⟩ := rhoX_outer hLN φ hL hT hLT hn ⟨a, hAX haA⟩ (hAT haA) haLQ
    obtain ⟨B₀, hB₀⟩ := rhoX_outer hLN φ hL hT hLT hn ⟨t, hAX htA⟩ (hAT htA) htLQ
    obtain ⟨l, hl⟩ := exists_conj_eq_conjAut φ hn (B₁ * B₀⁻¹)
    have h1 : rhoX hLN φ ((⟨a, hAX haA⟩ * (⟨t, hAX htA⟩ : X)⁻¹) * (⟨l, hLX l.2⟩ : X)⁻¹) = 1 := by
      rw [map_mul, map_mul, map_inv, map_inv, hB₁, hB₀, rhoX_eq_conj hLN φ _ l rfl, hl, map_mul,
        map_inv]
      group
    have hq := mem_of_rhoX_eq_one hLN φ hL hT hLT _ h1
    simp only [Subgroup.coe_mul, Subgroup.coe_inv] at hq
    have : a * t⁻¹ = (a * t⁻¹ * (l : G)⁻¹) * l := by group
    rw [this]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_right hq) (Subgroup.mem_sup_left l.2)
  set H := A ⊓ (L ⊔ CFSG.Open.pCoreOf 2 X) with hH
  rw [Subgroup.relIndex, Subgroup.index]
  have hsurj : Function.Surjective (fun b : Bool =>
      if b then ((⟨t, htA⟩ : A) : A ⧸ H.subgroupOf A) else ((1 : A) : A ⧸ H.subgroupOf A)) := by
    intro q
    induction q using QuotientGroup.induction_on with
    | H a =>
      by_cases ha : (a : G) ∈ L ⊔ CFSG.Open.pCoreOf 2 X
      · refine ⟨false, ?_⟩
        simp only [Bool.false_eq_true, if_false]
        rw [QuotientGroup.eq, inv_one, one_mul, Subgroup.mem_subgroupOf]
        exact ⟨a.2, ha⟩
      · refine ⟨true, ?_⟩
        simp only [if_true]
        rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
        have hk := key a a.2 ha
        have hc : t⁻¹ * a = a * t⁻¹ := by
          have := hA2.1 a a.2 t htA
          calc t⁻¹ * a = t⁻¹ * (a * t) * t⁻¹ := by group
            _ = t⁻¹ * (t * a) * t⁻¹ := by rw [this]
            _ = a * t⁻¹ := by group
        simp only [Subgroup.coe_mul, Subgroup.coe_inv]
        rw [hc]
        exact ⟨A.mul_mem a.2 (A.inv_mem htA), hk⟩
  calc Nat.card (A ⧸ H.subgroupOf A) ≤ Nat.card Bool := Nat.card_le_card_of_surjective _ hsurj
    _ = 2 := by simp

include hLN φ in
theorem card_imgSL_lt (hL : L ∈ oTwoComponentsIn X) (hT : CFSG.ABGLocalTools.IsSylowOf 2 T X)
    (hLT : L ⊔ T = X) (hn : Odd n) [Fintype (GaloisField 2 n)] {A : Subgroup G}
    (hA : A ∈ famG T 0) {t : G} (htA : t ∈ A) (htX : t ∈ X) {B : GL (Fin 3) (GaloisField 2 n)}
    (htB : rhoX hLN φ ⟨t, htX⟩ = conjAut 3 _ B * dualAut 3 _) :
    Nat.card (imgSL hLN φ (A ⊓ (L ⊔ CFSG.Open.pCoreOf 2 X))) <
      Fintype.card (GaloisField 2 n) ^ 2 := by
  classical
  obtain ⟨hAT, hA2, -⟩ := mem_famG.mp hA
  set H := A ⊓ (L ⊔ CFSG.Open.pCoreOf 2 X) with hH
  have hH2 : IsElemTwo H :=
    ⟨fun a ha b hb => hA2.1 a ha.1 b hb.1, fun a ha => hA2.2 a ha.1⟩
  obtain ⟨hE2, hEc⟩ := imgSL_elem hLN φ hn hH2
  have hle := card_le_sq_of_elementary hE2 hEc
  refine lt_of_le_of_ne hle fun hcard => ?_
  obtain ⟨S, hSd, hES⟩ := eq_transvectionGroup_of_card hE2 hEc hcard
  have hfix : ∀ g ∈ transvectionGroup S,
      CatalogueBHigherLinearAction.slConjugation 3 _ B (CatalogueBGraphForm.slGraphAut 3 _ g) =
        g := by
    intro g hg
    rw [← hES] at hg
    obtain ⟨a, haH, ha⟩ := (mem_imgSL hLN φ).mp hg
    apply theta_injective hn
    have hta : (⟨t, htX⟩ : X) * a * (⟨t, htX⟩ : X)⁻¹ = a := by
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      rw [hA2.1 t htA a haH.1]
      group
    calc theta n (CatalogueBHigherLinearAction.slConjugation 3 _ B
          (CatalogueBGraphForm.slGraphAut 3 _ g))
        = MulAut.conj ((conjAut 3 (GaloisField 2 n) B * dualAut 3 (GaloisField 2 n))
            (proj 3 (GaloisField 2 n) g)) := by
          rw [conjAut_mul_dualAut_proj]; rfl
      _ = rhoX hLN φ ⟨t, htX⟩ * theta n g * (rhoX hLN φ ⟨t, htX⟩)⁻¹ := by
          rw [htB, theta, MonoidHom.comp_apply, mulAut_mul_conj_mul_inv]
      _ = theta n g := by rw [← ha, ← map_inv, ← map_mul, ← map_mul, hta]
  set S'' := (FFModules.dotOrth S).map (Matrix.mulVecLin (B : Matrix (Fin 3) (Fin 3) _))
  have hdim : Module.finrank (GaloisField 2 n) S'' + Module.finrank (GaloisField 2 n) S = 3 := by
    rw [CFSG.RankThree.PartTwo.Sec20.Res7.finrank_map_gl, FFModules.finrank_dotOrth]
  have hS''d : Module.finrank (GaloisField 2 n) S'' = 1 ∨
      Module.finrank (GaloisField 2 n) S'' = 2 := by omega
  have hle' : transvectionGroup S ≤ transvectionGroup S'' := fun g hg => by
    have := graph_mem_transvectionGroup hg B
    rwa [hfix g hg] at this
  have heq : transvectionGroup S = transvectionGroup S'' :=
    Subgroup.eq_of_le_of_card_ge hle' (by
      rw [← hES, hcard]; exact card_transvectionGroup_le hS''d)
  have hS0 : S ≠ ⊥ := fun h => by
    rw [h, finrank_bot] at hSd; omega
  have hS''0 : S'' ≠ ⊥ := fun h => by
    rw [h, finrank_bot] at hS''d; omega
  have : S = S'' := by
    rw [← natFix_transvectionGroup hS0, heq, natFix_transvectionGroup hS''0]
  rw [← this] at hdim
  omega

theorem relIndex_ne_zero_of_finite {G : Type*} [Group G] [Finite G] (H K : Subgroup G) :
    H.relIndex K ≠ 0 :=
  Subgroup.index_ne_zero_of_finite

theorem card_galoisField (hn : n ≠ 0) [Fintype (GaloisField 2 n)] :
    Fintype.card (GaloisField 2 n) = 2 ^ n := by
  rw [Fintype.card_eq_nat_card]
  exact GaloisField.card 2 n hn

theorem two_mul_le_of_lt_of_elem {E : Subgroup SL(3, GaloisField 2 n)}
    (hE2 : ∀ g ∈ E, g * g = 1) {k : ℕ} (hk : Nat.card E < 2 ^ k) : 2 * Nat.card E ≤ 2 ^ k := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp : IsPGroup 2 E := fun g => ⟨1, by
    rw [pow_one, pow_two]; exact Subtype.ext (hE2 g g.2)⟩
  obtain ⟨m, hm⟩ := hp.exists_card_eq
  rw [hm] at hk ⊢
  have : m < k := (Nat.pow_lt_pow_iff_right (by norm_num)).mp hk
  calc 2 * 2 ^ m = 2 ^ (m + 1) := by ring
    _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) this

include hLN φ in
theorem relIndex_le_of_outer (hL : L ∈ oTwoComponentsIn X)
    (hT : CFSG.ABGLocalTools.IsSylowOf 2 T X) (hLT : L ⊔ T = X) (hn : Odd n) {A : Subgroup G}
    (hA : A ∈ famG T 0) {t : G} (htA : t ∈ A) (htLQ : t ∉ L ⊔ CFSG.Open.pCoreOf 2 X)
    (htX : t ∈ X) {B : GL (Fin 3) (GaloisField 2 n)}
    (htB : rhoX hLN φ ⟨t, htX⟩ = conjAut 3 _ B * dualAut 3 _) :
    (A ⊓ CFSG.Open.pCoreOf 2 X).relIndex A ≤ 2 ^ (2 * n) := by
  classical
  letI : Fintype (GaloisField 2 n) := Fintype.ofFinite _
  have hn0 : n ≠ 0 := by obtain ⟨k, rfl⟩ := hn; omega
  obtain ⟨hAT, hA2, -⟩ := mem_famG.mp hA
  set H := A ⊓ (L ⊔ CFSG.Open.pCoreOf 2 X) with hH
  have hHA : H ≤ A := inf_le_left
  have hAQH : A ⊓ CFSG.Open.pCoreOf 2 X ≤ H := inf_le_inf_left _ le_sup_right
  have hHX : H ≤ X := hHA.trans (hAT.trans (le_of_isSylowOf' hT))
  have hcardE := card_imgSL hLN φ hL hT hLT hn hHX inf_le_right
  have hHQ : H ⊓ CFSG.Open.pCoreOf 2 X = A ⊓ CFSG.Open.pCoreOf 2 X := by
    rw [hH, inf_assoc,
      inf_eq_right.mpr (le_sup_right : CFSG.Open.pCoreOf 2 X ≤ L ⊔ CFSG.Open.pCoreOf 2 X)]
  rw [hHQ] at hcardE
  have hlt := card_imgSL_lt hLN φ hL hT hLT hn hA htA htX htB
  rw [card_galoisField hn0, ← pow_mul, mul_comm n 2] at hlt
  have hH2 : IsElemTwo H :=
    ⟨fun a ha b hb => hA2.1 a ha.1 b hb.1, fun a ha => hA2.2 a ha.1⟩
  have h2E := two_mul_le_of_lt_of_elem (imgSL_elem hLN φ hn hH2).1 hlt
  have h2 := relIndex_inf_sup_le_two hLN φ hL hT hLT hn hA htA htLQ
  calc (A ⊓ CFSG.Open.pCoreOf 2 X).relIndex A
      = (A ⊓ CFSG.Open.pCoreOf 2 X).relIndex H * H.relIndex A :=
        (Subgroup.relIndex_mul_relIndex _ _ _ hAQH hHA).symm
    _ ≤ (A ⊓ CFSG.Open.pCoreOf 2 X).relIndex H * 2 := Nat.mul_le_mul_left _ h2
    _ = 2 * Nat.card (imgSL hLN φ H) := by rw [hcardE, mul_comm]
    _ ≤ 2 ^ (2 * n) := h2E

theorem exists_ppd (hn : Odd n) : ∃ r : ℕ, r.Prime ∧ r ≠ 2 ∧ r ∣ 2 ^ (3 * n) - 1 ∧
    (∀ k : ℕ, 0 < k → k < 3 * n → ¬ r ∣ 2 ^ k - 1) ∧ orderOf (2 : ZMod r) = 3 * n := by
  have hn0 : 0 < n := by obtain ⟨k, rfl⟩ := hn; omega
  obtain ⟨r, hr, hr3, hrk⟩ := CFSG.Timmesfeld.exists_primitive_prime_dvd_two_pow_sub_one (3 * n)
    (by omega) (by obtain ⟨k, rfl⟩ := hn; omega)
  refine ⟨r, hr, ?_, hr3, hrk, orderOf_two_eq_of_ppd hr hr3 hrk hn0⟩
  rintro rfl
  have h1 : 1 ≤ 2 ^ (3 * n) := Nat.one_le_two_pow
  have h2 : 2 ∣ 2 ^ (3 * n) := dvd_pow_self 2 (by omega)
  omega

include hLN φ in
theorem caseOuter (hL : L ∈ oTwoComponentsIn X)
    (hT : CFSG.ABGLocalTools.IsSylowOf 2 T X) (hLT : L ⊔ T = X) (hn : Odd n)
    (hV : ⁅omegaZOf (CFSG.Open.pCoreOf 2 X), L⁆ ≠ ⊥) {A : Subgroup G} (hA : A ∈ famG T 0)
    (hAQ : ¬ A ≤ L ⊔ CFSG.Open.pCoreOf 2 X) : False := by
  classical
  letI : Fintype (GaloisField 2 n) := Fintype.ofFinite _
  have hn0 : n ≠ 0 := by obtain ⟨k, rfl⟩ := hn; omega
  obtain ⟨hAT, hA2, -⟩ := mem_famG.mp hA
  have hLX : L ≤ X := le_of_mem_oTwoComponentsIn hL
  have hTX : T ≤ X := le_of_isSylowOf' hT
  have hAX : A ≤ X := hAT.trans hTX
  obtain ⟨hVc, hV2, hVQ, hQV⟩ := omegaZOf_facts (CFSG.Open.pCoreOf 2 X)
  have hXV := le_normalizer_omegaZOf X
  have hVT := hVQ.trans (pCoreOf_le_of_sylow hT)
  have hoff := relIndex_le_of_famG hVT hVc hV2 (hTX.trans hXV) hA
  have hoff' : (A ⊓ Subgroup.centralizer (omegaZOf (CFSG.Open.pCoreOf 2 X) : Set G)).relIndex A ≤
      (A ⊓ CFSG.Open.pCoreOf 2 X).relIndex A :=
    Subgroup.relIndex_le_of_le_left (inf_le_inf_left _ fun q hq =>
      Subgroup.mem_centralizer_iff.mpr fun v hv => (hQV v hv q hq).symm)
      (relIndex_ne_zero_of_finite _ _)
  obtain ⟨t, htA, htLQ⟩ := Set.not_subset.mp hAQ
  have htX : t ∈ X := hAX htA
  have ht2 : t * t = 1 := hA2.2 t htA
  obtain ⟨A₀, hA₀⟩ := rhoX_outer hLN φ hL hT hLT hn ⟨t, htX⟩ (hAT htA) htLQ
  have hsq : (conjAut 3 (GaloisField 2 n) A₀ * dualAut 3 (GaloisField 2 n)) ^ 2 = 1 := by
    rw [← hA₀, ← map_pow, pow_two]
    have : (⟨t, htX⟩ : X) * ⟨t, htX⟩ = 1 := Subtype.ext ht2
    rw [this, map_one]
  obtain ⟨B, hBs, hBeq⟩ := exists_symm_of_sq_eq_one hn A₀ hsq
  have htB : rhoX hLN φ ⟨t, htX⟩ = conjAut 3 _ B * dualAut 3 _ := hA₀.trans hBeq
  obtain ⟨r, hr, hr2, hr3, hrk, hk⟩ := exists_ppd hn
  obtain ⟨g, hgr, hginv⟩ := exists_inverted_of_symm (card_galoisField hn0)
    (Nat.pos_of_ne_zero hn0) hr hr3 hrk B hBs
  have hpr : (proj 3 (GaloisField 2 n) g) ^ r = 1 := by
    rw [← map_pow, ← hgr, pow_orderOf_eq_one, map_one]
  obtain ⟨y, hyg, hyr⟩ := exists_lift φ hr hr2 _ hpr
  set yX : X := ⟨y, hLX y.2⟩ with hyX
  have hconj : rhoX hLN φ (⟨t, htX⟩ * yX * (⟨t, htX⟩ : X)⁻¹) = rhoX hLN φ yX⁻¹ := by
    rw [map_mul, map_mul, map_inv, map_inv, rhoX_eq_conj hLN φ yX y rfl,
      mulAut_mul_conj_mul_inv, hyg, htB, conjAut_mul_dualAut_proj, hginv, map_inv, map_inv]
  have hsy : ∀ v ∈ omegaZOf (CFSG.Open.pCoreOf 2 X),
      (t * y * t⁻¹) * v * (t * y * t⁻¹)⁻¹ = (y : G)⁻¹ * v * y := by
    intro v hv
    have := conj_eq_of_rhoX_eq hLN φ hL hT hLT hconj v hv
    simpa using this
  have hy1 : ∃ v ∈ omegaZOf (CFSG.Open.pCoreOf 2 X), (y : G) * v * (y : G)⁻¹ ≠ v := by
    by_contra hcon
    push Not at hcon
    have hyQ := mem_pCoreOf_of_centralizes_omegaZOf hL hLN hT hLT (isSimpleGroup_quot φ) hV
      (hLX y.2) hcon
    have h1 : psi φ y = 1 :=
      (psi_eq_one_iff φ y).mpr (by rw [← pCoreOf_inf_eq hL hLN]; exact ⟨y.2, hyQ⟩)
    rw [hyg] at h1
    have hg1 : g = 1 := proj_injective_of_odd hn (by rw [h1, map_one])
    rw [hg1, orderOf_one] at hgr
    exact hr.one_lt.ne hgr
  have hyr' : ∀ v ∈ omegaZOf (CFSG.Open.pCoreOf 2 X), (y : G) ^ r * v * ((y : G) ^ r)⁻¹ = v := by
    intro v _
    have : (y : G) ^ r = 1 := by rw [← Subgroup.coe_pow, hyr, Subgroup.coe_one]
    rw [this, one_mul, inv_one, mul_one]
  have hs2 : ∀ v ∈ omegaZOf (CFSG.Open.pCoreOf 2 X), t ^ 2 * v * (t ^ 2)⁻¹ = v := by
    intro v _
    rw [pow_two, ht2, one_mul, inv_one, mul_one]
  have hko : Odd (3 * n) := Nat.odd_mul.mpr ⟨by decide, hn⟩
  obtain ⟨-, hbound⟩ := two_pow_le_relIndex_centralizer hVc hV2 (hXV (hLX y.2)) (hXV htX) hr hr2
    hk hko hyr' hs2 hsy hy1
  have hle1 : (omegaZOf (CFSG.Open.pCoreOf 2 X) ⊓ Subgroup.centralizer ({t} : Set G)).relIndex
        (omegaZOf (CFSG.Open.pCoreOf 2 X)) ≤
      (omegaZOf (CFSG.Open.pCoreOf 2 X) ⊓ Subgroup.centralizer (A : Set G)).relIndex
        (omegaZOf (CFSG.Open.pCoreOf 2 X)) :=
    Subgroup.relIndex_le_of_le_left (inf_le_inf_left _ (Subgroup.centralizer_le
      (Set.singleton_subset_iff.mpr htA))) (relIndex_ne_zero_of_finite _ _)
  have hub := relIndex_le_of_outer hLN φ hL hT hLT hn hA htA htLQ htX htB
  have hfin : 2 ^ (3 * n) ≤ 2 ^ (2 * n) := hbound.trans (hle1.trans (hoff.trans (hoff'.trans hub)))
  have := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp hfin
  omega

theorem transpose_inv_eq_of_symm {F : Type*} [Field F] {y : SL(3, F)}
    (hy : (y : Matrix (Fin 3) (Fin 3) F)ᵀ = y) : (y⁻¹).transpose = y⁻¹ := by
  apply Subtype.ext
  change ((y⁻¹ : SL(3, F)) : Matrix (Fin 3) (Fin 3) F)ᵀ = ((y⁻¹ : SL(3, F)) : Matrix _ _ F)
  rw [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_transpose, hy]

include hLN φ in
theorem lower_of_symm (hL : L ∈ oTwoComponentsIn X) (hT : CFSG.ABGLocalTools.IsSylowOf 2 T X)
    (hLT : L ⊔ T = X) (hn : Odd n) (hV : ⁅omegaZOf (CFSG.Open.pCoreOf 2 X), L⁆ ≠ ⊥)
    (hLQ : L ⊔ CFSG.Open.pCoreOf 2 X ≠ X) {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2)
    (hk : orderOf (2 : ZMod r) = 3 * n) {y₀ : SL(3, GaloisField 2 n)} (hy₀1 : y₀ ≠ 1)
    (hy₀s : (y₀ : Matrix (Fin 3) (Fin 3) (GaloisField 2 n))ᵀ = y₀) {y : L} (hyr : y ^ r = 1)
    (hyg : psi φ y = proj 3 _ y₀) :
    2 ^ (2 * (3 * n)) ≤ (omegaZOf (CFSG.Open.pCoreOf 2 X) ⊓
      Subgroup.centralizer ({(y : G)} : Set G)).relIndex (omegaZOf (CFSG.Open.pCoreOf 2 X)) := by
  classical
  have hLX : L ≤ X := le_of_mem_oTwoComponentsIn hL
  have hTX : T ≤ X := le_of_isSylowOf' hT
  obtain ⟨hVc, hV2, -, -⟩ := omegaZOf_facts (CFSG.Open.pCoreOf 2 X)
  have hXV := le_normalizer_omegaZOf X
  obtain ⟨x, hxT, hxLQ⟩ : ∃ x ∈ T, x ∉ L ⊔ CFSG.Open.pCoreOf 2 X := by
    by_contra hcon
    push Not at hcon
    apply hLQ
    refine le_antisymm (sup_le hLX (CFSG.LieType.BorelTits.pCoreOf_le 2 X)) ?_
    calc X = L ⊔ T := hLT.symm
      _ ≤ L ⊔ CFSG.Open.pCoreOf 2 X := sup_le le_sup_left fun z hz => hcon z hz
  obtain ⟨A₀, hA₀⟩ := rhoX_outer hLN φ hL hT hLT hn ⟨x, hTX hxT⟩ hxT hxLQ
  obtain ⟨l₀, hl₀⟩ := exists_conj_eq_conjAut φ hn A₀⁻¹
  set s : X := ⟨l₀, hLX l₀.2⟩ * ⟨x, hTX hxT⟩ with hsdef
  have hδ : rhoX hLN φ s = dualAut 3 (GaloisField 2 n) := by
    rw [hsdef, map_mul, rhoX_eq_conj hLN φ _ l₀ rfl, hl₀, hA₀, ← mul_assoc, ← map_mul,
      inv_mul_cancel, map_one, one_mul]
  have hδδ : dualAut 3 (GaloisField 2 n) * dualAut 3 (GaloisField 2 n) = 1 :=
    (standard_automorphism_transport (K := GaloisField 2 n) (n := 3)).2.2.2.1
  set yX : X := ⟨y, hLX y.2⟩ with hyX
  have hs2 : ∀ v ∈ omegaZOf (CFSG.Open.pCoreOf 2 X), (s : G) ^ 2 * v * ((s : G) ^ 2)⁻¹ = v := by
    intro v hv
    have h1 : rhoX hLN φ (s * s) = rhoX hLN φ 1 := by rw [map_mul, hδ, hδδ, map_one]
    have := conj_eq_of_rhoX_eq hLN φ hL hT hLT h1 v hv
    simpa [pow_two] using this
  have hconj : rhoX hLN φ (s * yX * s⁻¹) = rhoX hLN φ yX⁻¹ := by
    rw [map_mul, map_mul, map_inv, map_inv, rhoX_eq_conj hLN φ yX y rfl,
      mulAut_mul_conj_mul_inv, hyg, hδ, dualAut_proj, transpose_inv_eq_of_symm hy₀s, map_inv,
      map_inv]
  have hsy : ∀ v ∈ omegaZOf (CFSG.Open.pCoreOf 2 X),
      ((s : G) * y * (s : G)⁻¹) * v * ((s : G) * y * (s : G)⁻¹)⁻¹ = (y : G)⁻¹ * v * y := by
    intro v hv
    have := conj_eq_of_rhoX_eq hLN φ hL hT hLT hconj v hv
    simpa using this
  have hy1 : ∃ v ∈ omegaZOf (CFSG.Open.pCoreOf 2 X), (y : G) * v * (y : G)⁻¹ ≠ v := by
    by_contra hcon
    push Not at hcon
    have hyQ := mem_pCoreOf_of_centralizes_omegaZOf hL hLN hT hLT (isSimpleGroup_quot φ) hV
      (hLX y.2) hcon
    have h1 : psi φ y = 1 :=
      (psi_eq_one_iff φ y).mpr (by rw [← pCoreOf_inf_eq hL hLN]; exact ⟨y.2, hyQ⟩)
    rw [hyg] at h1
    exact hy₀1 (proj_injective_of_odd hn (by rw [h1, map_one]))
  have hyr' : ∀ v ∈ omegaZOf (CFSG.Open.pCoreOf 2 X), (y : G) ^ r * v * ((y : G) ^ r)⁻¹ = v := by
    intro v _
    have : (y : G) ^ r = 1 := by rw [← Subgroup.coe_pow, hyr, Subgroup.coe_one]
    rw [this, one_mul, inv_one, mul_one]
  have hko : Odd (3 * n) := Nat.odd_mul.mpr ⟨by decide, hn⟩
  exact (two_pow_le_relIndex_centralizer hVc hV2 (hXV (hLX y.2)) (hXV s.2) hr hr2 hk hko hyr'
    hs2 hsy hy1).1

include hLN φ in
theorem relIndex_le_cube (hL : L ∈ oTwoComponentsIn X) (hT : CFSG.ABGLocalTools.IsSylowOf 2 T X)
    (hLT : L ⊔ T = X) {A : Subgroup G} {τ : SL(3, GaloisField 2 n)} (hτ : τ ∈ imgSL hLN φ A)
    (h₁ h₂ h₃ : SL(3, GaloisField 2 n)) {y : L}
    (hyg : psi φ y = proj 3 _ ((h₁ * τ * h₁⁻¹) * (h₂ * τ * h₂⁻¹) * (h₃ * τ * h₃⁻¹))) :
    (omegaZOf (CFSG.Open.pCoreOf 2 X) ⊓ Subgroup.centralizer ({(y : G)} : Set G)).relIndex
        (omegaZOf (CFSG.Open.pCoreOf 2 X)) ≤
      ((omegaZOf (CFSG.Open.pCoreOf 2 X) ⊓ Subgroup.centralizer (A : Set G)).relIndex
        (omegaZOf (CFSG.Open.pCoreOf 2 X))) ^ 3 := by
  classical
  set V := omegaZOf (CFSG.Open.pCoreOf 2 X) with hVdef
  have hLX : L ≤ X := le_of_mem_oTwoComponentsIn hL
  have hXV := le_normalizer_omegaZOf X
  obtain ⟨a, haA, ha⟩ := (mem_imgSL hLN φ).mp hτ
  have hlift : ∀ h : SL(3, GaloisField 2 n), ∃ l : L, psi φ l = proj 3 _ h :=
    fun h => psi_surjective φ (proj 3 _ h)
  obtain ⟨l₁, hl₁⟩ := hlift h₁
  obtain ⟨l₂, hl₂⟩ := hlift h₂
  obtain ⟨l₃, hl₃⟩ := hlift h₃
  set lX : L → X := fun l => ⟨l, hLX l.2⟩ with hlX
  have hconjρ : ∀ (l : L) (h : SL(3, GaloisField 2 n)), psi φ l = proj 3 _ h →
      rhoX hLN φ (lX l * a * (lX l)⁻¹) = theta n (h * τ * h⁻¹) := by
    intro l h hl
    rw [map_mul, map_mul, map_inv, rhoX_eq_conj hLN φ (lX l) l rfl, ha, hl, map_mul, map_mul,
      map_inv]
    rfl
  set z : X := (lX l₁ * a * (lX l₁)⁻¹) * (lX l₂ * a * (lX l₂)⁻¹) * (lX l₃ * a * (lX l₃)⁻¹)
    with hz
  have hρz : rhoX hLN φ z = rhoX hLN φ (lX y) := by
    rw [hz, map_mul, map_mul, hconjρ l₁ h₁ hl₁, hconjρ l₂ h₂ hl₂, hconjρ l₃ h₃ hl₃,
      rhoX_eq_conj hLN φ (lX y) y rfl, hyg, ← map_mul, ← map_mul]
    rfl
  have hyz := conj_eq_of_rhoX_eq hLN φ hL hT hLT hρz
  set H : L → Subgroup G :=
    fun l => (Subgroup.zpowers (a : G)).map (MulAut.conj (l : G)).toMonoidHom with hH
  have hHmem : ∀ l : L, ((lX l * a * (lX l)⁻¹ : X) : G) ∈ H l := by
    intro l
    refine ⟨a, Subgroup.mem_zpowers _, ?_⟩
    simp [lX, MulAut.conj_apply]
  have hcent : V ⊓ Subgroup.centralizer ((H l₁ ⊔ H l₂ ⊔ H l₃ : Subgroup G) : Set G) ≤
      V ⊓ Subgroup.centralizer ({(y : G)} : Set G) := by
    rintro v ⟨hv, hvc⟩
    refine ⟨hv, Subgroup.mem_centralizer_iff.mpr ?_⟩
    rintro _ rfl
    have hcomm : ∀ w ∈ H l₁ ⊔ H l₂ ⊔ H l₃, w * v = v * w := fun w hw =>
      Subgroup.mem_centralizer_iff.mp hvc w hw
    have hzv : (z : G) * v = v * z := by
      have c1 : Commute ((lX l₁ * a * (lX l₁)⁻¹ : X) : G) v :=
        hcomm _ (Subgroup.mem_sup_left (Subgroup.mem_sup_left (hHmem l₁)))
      have c2 : Commute ((lX l₂ * a * (lX l₂)⁻¹ : X) : G) v :=
        hcomm _ (Subgroup.mem_sup_left (Subgroup.mem_sup_right (hHmem l₂)))
      have c3 : Commute ((lX l₃ * a * (lX l₃)⁻¹ : X) : G) v :=
        hcomm _ (Subgroup.mem_sup_right (hHmem l₃))
      have c := (c1.mul_left c2).mul_left c3
      rw [hz, Subgroup.coe_mul, Subgroup.coe_mul]
      exact c
    have := hyz v hv
    simp only [lX] at this
    calc (y : G) * v = (y : G) * v * (y : G)⁻¹ * y := by group
      _ = (z : G) * v * (z : G)⁻¹ * y := by rw [this]
      _ = v * y := by rw [hzv]; group
  have hconjeq : ∀ l : L, (V ⊓ Subgroup.centralizer (H l : Set G)).relIndex V =
      (V ⊓ Subgroup.centralizer ((Subgroup.zpowers (a : G) : Subgroup G) : Set G)).relIndex V :=
    fun l => relIndex_centralizer_conj (hXV (hLX l.2)) _
  have hzA : (V ⊓ Subgroup.centralizer ((Subgroup.zpowers (a : G) : Subgroup G) : Set G)).relIndex V
      ≤ (V ⊓ Subgroup.centralizer (A : Set G)).relIndex V :=
    Subgroup.relIndex_le_of_le_left (inf_le_inf_left _ (Subgroup.centralizer_le
      (Subgroup.zpowers_le.mpr haA))) (relIndex_ne_zero_of_finite _ _)
  calc (V ⊓ Subgroup.centralizer ({(y : G)} : Set G)).relIndex V
      ≤ (V ⊓ Subgroup.centralizer ((H l₁ ⊔ H l₂ ⊔ H l₃ : Subgroup G) : Set G)).relIndex V :=
        Subgroup.relIndex_le_of_le_left hcent (relIndex_ne_zero_of_finite _ _)
    _ ≤ (V ⊓ Subgroup.centralizer ((H l₁ ⊔ H l₂ : Subgroup G) : Set G)).relIndex V *
          (V ⊓ Subgroup.centralizer (H l₃ : Set G)).relIndex V :=
        relIndex_centralizer_sup_le V _ _
    _ ≤ (V ⊓ Subgroup.centralizer (H l₁ : Set G)).relIndex V *
          (V ⊓ Subgroup.centralizer (H l₂ : Set G)).relIndex V *
          (V ⊓ Subgroup.centralizer (H l₃ : Set G)).relIndex V :=
        Nat.mul_le_mul_right _ (relIndex_centralizer_sup_le V _ _)
    _ ≤ (V ⊓ Subgroup.centralizer (A : Set G)).relIndex V ^ 3 := by
        rw [hconjeq l₁, hconjeq l₂, hconjeq l₃, pow_three, ← mul_assoc]
        exact Nat.mul_le_mul (Nat.mul_le_mul hzA hzA) hzA

include hLN φ in
theorem map_imgSL_le {A : Subgroup G} (g₁ : X) (h : SL(3, GaloisField 2 n))
    (A₀ : GL (Fin 3) (GaloisField 2 n))
    (hg₁ : rhoX hLN φ g₁ = MulAut.conj (proj 3 _ h) *
      (conjAut 3 (GaloisField 2 n) A₀ * dualAut 3 (GaloisField 2 n))) :
    (imgSL hLN φ A).map ((MulAut.conj h).toMonoidHom.comp
        ((CatalogueBHigherLinearAction.slConjugation 3 _ A₀).toMonoidHom.comp
          (CatalogueBGraphForm.slGraphAut 3 _).toMonoidHom)) ≤
      imgSL hLN φ (A.map (MulAut.conj (g₁ : G)).toMonoidHom) := by
  rintro _ ⟨g, hg, rfl⟩
  obtain ⟨a, haA, ha⟩ := (mem_imgSL hLN φ).mp hg
  refine (mem_imgSL hLN φ).mpr ⟨g₁ * a * g₁⁻¹, ⟨a, haA, by simp [MulAut.conj_apply]⟩, ?_⟩
  rw [map_mul, map_mul, map_inv, ha, theta, MonoidHom.comp_apply, mulAut_mul_conj_mul_inv, hg₁]
  have hcd : (conjAut 3 (GaloisField 2 n) A₀ * dualAut 3 (GaloisField 2 n))
      (proj 3 (GaloisField 2 n) g) = proj 3 (GaloisField 2 n)
        (CatalogueBHigherLinearAction.slConjugation 3 _ A₀
          (CatalogueBGraphForm.slGraphAut 3 _ g)) :=
    conjAut_mul_dualAut_proj A₀ g
  rw [MulAut.mul_apply, hcd, MulAut.conj_apply, ← map_inv, ← map_mul, ← map_mul]
  rfl

theorem finrank_map_sl {F : Type*} [Field F] (h : SL(3, F)) (W : Submodule F (Fin 3 → F)) :
    Module.finrank F (W.map (Matrix.mulVecLin (h : Matrix (Fin 3) (Fin 3) F))) =
      Module.finrank F W :=
  CFSG.RankThree.PartTwo.Sec20.Res7.finrank_map_gl (Matrix.SpecialLinearGroup.toGL h) W

theorem imgSL_mono {H₁ H₂ : Subgroup G} (h : H₁ ≤ H₂) : imgSL hLN φ H₁ ≤ imgSL hLN φ H₂ :=
  Subgroup.comap_mono (Subgroup.map_mono fun _ hx => h hx)

include hLN φ in
theorem caseInner (hL : L ∈ oTwoComponentsIn X)
    (hT : CFSG.ABGLocalTools.IsSylowOf 2 T X) (hLT : L ⊔ T = X) (hn : Odd n)
    (hV : ⁅omegaZOf (CFSG.Open.pCoreOf 2 X), L⁆ ≠ ⊥)
    (hLQ : L ⊔ CFSG.Open.pCoreOf 2 X ≠ X) {A : Subgroup G} (hA : A ∈ famG T 0)
    (hAQ : ¬ A ≤ CFSG.Open.pCoreOf 2 X) (hALQ : A ≤ L ⊔ CFSG.Open.pCoreOf 2 X) : False := by
  classical
  letI : Fintype (GaloisField 2 n) := Fintype.ofFinite _
  have hn0 : n ≠ 0 := by obtain ⟨k, rfl⟩ := hn; omega
  obtain ⟨hAT, hA2, -⟩ := mem_famG.mp hA
  have hLX : L ≤ X := le_of_mem_oTwoComponentsIn hL
  have hTX : T ≤ X := le_of_isSylowOf' hT
  have hAX : A ≤ X := hAT.trans hTX
  obtain ⟨hVc, hV2, hVQ, hQV⟩ := omegaZOf_facts (CFSG.Open.pCoreOf 2 X)
  have hXV := le_normalizer_omegaZOf X
  have hVT := hVQ.trans (pCoreOf_le_of_sylow hT)
  set V := omegaZOf (CFSG.Open.pCoreOf 2 X) with hVdef
  have hoff := relIndex_le_of_famG hVT hVc hV2 (hTX.trans hXV) hA
  have hoff' : (A ⊓ Subgroup.centralizer (V : Set G)).relIndex A ≤
      (A ⊓ CFSG.Open.pCoreOf 2 X).relIndex A :=
    Subgroup.relIndex_le_of_le_left (inf_le_inf_left _ fun q hq =>
      Subgroup.mem_centralizer_iff.mpr fun v hv => (hQV v hv q hq).symm)
      (relIndex_ne_zero_of_finite _ _)
  have hcardE : Nat.card (imgSL hLN φ A) = (A ⊓ CFSG.Open.pCoreOf 2 X).relIndex A :=
    card_imgSL hLN φ hL hT hLT hn hAX hALQ
  obtain ⟨hE2, hEc⟩ := imgSL_elem hLN φ hn hA2
  have hEle := card_le_sq_of_elementary hE2 hEc
  have hNE : (V ⊓ Subgroup.centralizer (A : Set G)).relIndex V ≤ Nat.card (imgSL hLN φ A) := by
    rw [hcardE]; exact hoff.trans hoff'
  obtain ⟨τ, hτE, hτ1⟩ : ∃ τ ∈ imgSL hLN φ A, τ ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have hbot : imgSL hLN φ A = ⊥ := eq_bot_iff.mpr fun g hg => (Subgroup.mem_bot).mpr (hcon g hg)
    rw [hbot, Subgroup.card_bot, eq_comm, Subgroup.relIndex_eq_one] at hcardE
    exact hAQ (hcardE.trans inf_le_right)
  have hτ2 : τ * τ = 1 := hE2 τ hτE
  obtain ⟨r, hr, hr2, hr3, hrk, hk⟩ := exists_ppd hn
  obtain ⟨y₀, τ₁, τ₂, τ₃, hy₀r, hy₀s, hy₀, h1a, h1b, h2a, h2b, h3a, h3b⟩ :=
    exists_symm_orderOf_prod_three (card_galoisField hn0) (Nat.pos_of_ne_zero hn0) hr hr3 hrk
  obtain ⟨k₁, hk₁⟩ := exists_conj_eq_of_involution τ τ₁ hτ2 hτ1 h1a h1b
  obtain ⟨k₂, hk₂⟩ := exists_conj_eq_of_involution τ τ₂ hτ2 hτ1 h2a h2b
  obtain ⟨k₃, hk₃⟩ := exists_conj_eq_of_involution τ τ₃ hτ2 hτ1 h3a h3b
  have hpr : (proj 3 (GaloisField 2 n) y₀) ^ r = 1 := by
    rw [← map_pow, ← hy₀r, pow_orderOf_eq_one, map_one]
  obtain ⟨y, hyg, hyr⟩ := exists_lift φ hr hr2 _ hpr
  have hy₀1 : y₀ ≠ 1 := by
    intro h; rw [h, orderOf_one] at hy₀r; exact hr.one_lt.ne hy₀r
  have hlow := lower_of_symm hLN φ hL hT hLT hn hV hLQ hr hr2 hk hy₀1 hy₀s hyr hyg
  have hyg' : psi φ y = proj 3 _ ((k₁ * τ * k₁⁻¹) * (k₂ * τ * k₂⁻¹) * (k₃ * τ * k₃⁻¹)) := by
    rw [hyg, hy₀, hk₁, hk₂, hk₃]
  have hcube := relIndex_le_cube hLN φ hL hT hLT hτE k₁ k₂ k₃ hyg'
  have hEq : Nat.card (imgSL hLN φ A) = Fintype.card (GaloisField 2 n) ^ 2 := by
    refine le_antisymm hEle ?_
    by_contra hlt
    push Not at hlt
    have h1 : Nat.card (imgSL hLN φ A) ^ 3 < (Fintype.card (GaloisField 2 n) ^ 2) ^ 3 :=
      Nat.pow_lt_pow_left hlt (by norm_num)
    rw [card_galoisField hn0, ← pow_mul, ← pow_mul] at h1
    have h2 := hlow.trans (hcube.trans (Nat.pow_le_pow_left hNE 3))
    have h3 : 2 * (3 * n) = n * (2 * 3) := by ring
    rw [h3] at h2
    exact absurd (h2.trans_lt h1) (lt_irrefl _)
  obtain ⟨S, hSd, hES⟩ := eq_transvectionGroup_of_card hE2 hEc hEq
  obtain ⟨x, hxT, hxLQ⟩ : ∃ x ∈ T, x ∉ L ⊔ CFSG.Open.pCoreOf 2 X := by
    by_contra hcon
    push Not at hcon
    apply hLQ
    refine le_antisymm (sup_le hLX (CFSG.LieType.BorelTits.pCoreOf_le 2 X)) ?_
    calc X = L ⊔ T := hLT.symm
      _ ≤ L ⊔ CFSG.Open.pCoreOf 2 X := sup_le le_sup_left fun z hz => hcon z hz
  obtain ⟨A₀, hA₀⟩ := rhoX_outer hLN φ hL hT hLT hn ⟨x, hTX hxT⟩ hxT hxLQ
  set S'' := (FFModules.dotOrth S).map (Matrix.mulVecLin (A₀ : Matrix (Fin 3) (Fin 3) _))
    with hS''
  have hdim : Module.finrank (GaloisField 2 n) S'' + Module.finrank (GaloisField 2 n) S = 3 := by
    rw [hS'', CFSG.RankThree.PartTwo.Sec20.Res7.finrank_map_gl, FFModules.finrank_dotOrth]
  obtain ⟨h, hgen, hhd⟩ : ∃ h : SL(3, GaloisField 2 n),
      transvectionGroup S ⊔
        transvectionGroup (S''.map (Matrix.mulVecLin (h : Matrix (Fin 3) (Fin 3) _))) = ⊤ ∧
      (Module.finrank (GaloisField 2 n)
          (S''.map (Matrix.mulVecLin (h : Matrix (Fin 3) (Fin 3) (GaloisField 2 n)))) = 1 ∨
        Module.finrank (GaloisField 2 n)
          (S''.map (Matrix.mulVecLin (h : Matrix (Fin 3) (Fin 3) (GaloisField 2 n)))) = 2) := by
    rcases hSd with hS1 | hS2
    · have hS''2 : Module.finrank (GaloisField 2 n) S'' = 2 := by omega
      obtain ⟨h, hh⟩ := exists_not_le_map_of_line hS1 hS''2
      refine ⟨h, transvectionGroup_sup_eq_top hS1 (by rw [finrank_map_sl]; exact hS''2) hh,
        Or.inr (by rw [finrank_map_sl]; exact hS''2)⟩
    · have hS''1 : Module.finrank (GaloisField 2 n) S'' = 1 := by omega
      obtain ⟨h, hh⟩ := exists_not_le_map_of_plane hS2 hS''1
      refine ⟨h, ?_, Or.inl (by rw [finrank_map_sl]; exact hS''1)⟩
      rw [sup_comm]
      exact transvectionGroup_sup_eq_top (by rw [finrank_map_sl]; exact hS''1) hS2 hh
  obtain ⟨lh, hlh⟩ := psi_surjective φ (proj 3 _ h)
  set g₁ : X := ⟨lh, hLX lh.2⟩ * ⟨x, hTX hxT⟩ with hg₁def
  have hg₁ : rhoX hLN φ g₁ = MulAut.conj (proj 3 _ h) *
      (conjAut 3 (GaloisField 2 n) A₀ * dualAut 3 (GaloisField 2 n)) := by
    rw [hg₁def, map_mul, rhoX_eq_conj hLN φ _ lh rfl, hlh, hA₀]
  set γ : SL(3, GaloisField 2 n) →* SL(3, GaloisField 2 n) :=
    (MulAut.conj h).toMonoidHom.comp
      ((CatalogueBHigherLinearAction.slConjugation 3 _ A₀).toMonoidHom.comp
        (CatalogueBGraphForm.slGraphAut 3 _).toMonoidHom) with hγ
  have hγinj : Function.Injective γ := by
    intro a b hab
    simpa [hγ] using hab
  have hγle : (imgSL hLN φ A).map γ ≤
      transvectionGroup (S''.map (Matrix.mulVecLin (h : Matrix (Fin 3) (Fin 3) _))) := by
    rintro _ ⟨g, hg, rfl⟩
    rw [hES] at hg
    have := conj_mem_transvectionGroup (graph_mem_transvectionGroup hg A₀) h
    simpa [hγ, MulAut.conj_apply] using this
  have hγeq : (imgSL hLN φ A).map γ =
      transvectionGroup (S''.map (Matrix.mulVecLin (h : Matrix (Fin 3) (Fin 3) _))) :=
    Subgroup.eq_of_le_of_card_ge hγle (by
      rw [Subgroup.card_map_of_injective hγinj, hEq]
      exact card_transvectionGroup_le hhd)
  have hT'' : transvectionGroup (S''.map (Matrix.mulVecLin (h : Matrix (Fin 3) (Fin 3) _))) ≤
      imgSL hLN φ (A.map (MulAut.conj (g₁ : G)).toMonoidHom) :=
    hγeq ▸ map_imgSL_le hLN φ g₁ h A₀ hg₁
  have hy₀mem : y₀ ∈ imgSL hLN φ (A ⊔ A.map (MulAut.conj (g₁ : G)).toMonoidHom) := by
    have htop : (⊤ : Subgroup SL(3, GaloisField 2 n)) ≤
        imgSL hLN φ (A ⊔ A.map (MulAut.conj (g₁ : G)).toMonoidHom) := by
      rw [← hgen]
      exact sup_le (hES ▸ imgSL_mono hLN φ le_sup_left) (hT''.trans (imgSL_mono hLN φ le_sup_right))
    exact htop (Subgroup.mem_top _)
  obtain ⟨w, hwAA, hw⟩ := (mem_imgSL hLN φ).mp hy₀mem
  have hwy : rhoX hLN φ w = rhoX hLN φ ⟨y, hLX y.2⟩ := by
    rw [hw, rhoX_eq_conj hLN φ _ y rfl, hyg]
    rfl
  have hwyv := conj_eq_of_rhoX_eq hLN φ hL hT hLT hwy
  have hcent : V ⊓ Subgroup.centralizer
        ((A ⊔ A.map (MulAut.conj (g₁ : G)).toMonoidHom : Subgroup G) : Set G) ≤
      V ⊓ Subgroup.centralizer ({(y : G)} : Set G) := by
    rintro v ⟨hv, hvc⟩
    refine ⟨hv, Subgroup.mem_centralizer_iff.mpr ?_⟩
    rintro _ rfl
    have hwv : (w : G) * v = v * w := Subgroup.mem_centralizer_iff.mp hvc _ hwAA
    have := hwyv v hv
    calc (y : G) * v = (y : G) * v * (y : G)⁻¹ * y := by group
      _ = (w : G) * v * (w : G)⁻¹ * y := by rw [this]
      _ = v * y := by rw [hwv]; group
  have hup := (Subgroup.relIndex_le_of_le_left hcent (relIndex_ne_zero_of_finite _ _)).trans
    (relIndex_centralizer_sup_le V A (A.map (MulAut.conj (g₁ : G)).toMonoidHom))
  rw [relIndex_centralizer_conj (hXV g₁.2) A] at hup
  have hfin := hlow.trans (hup.trans (Nat.mul_le_mul (hNE.trans hEq.le) (hNE.trans hEq.le)))
  rw [card_galoisField hn0, ← pow_mul, ← pow_add] at hfin
  have := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp hfin
  omega

end Main

theorem item321Split_holds : Item321Split := by
  intro G _ _ X L T n _ hL hLN hT hLT hn ⟨φ⟩
  by_contra hcon
  simp only [not_or] at hcon
  obtain ⟨⟨hJ, hV⟩, hLQ⟩ := hcon
  apply hJ
  have hJT : thompsonOf T = jG T 0 := map_higherElemThompson T 0
  rw [hJT]
  refine le_normalizer_jG_of_le hT ?_
  refine sSup_le fun A hA => ?_
  by_contra hAQ
  by_cases hALQ : A ≤ L ⊔ CFSG.Open.pCoreOf 2 X
  · exact caseInner hLN φ hL hT hLT hn hV hLQ hA hAQ hALQ
  · exact caseOuter hLN φ hL hT hLT hn hV hA hALQ

end CFSG.RankThree.PartTwo.Sec3.Sims321
