module

public import CFSG.Blueprint.Catalog
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherPrimeFormRealization
import CFSG.Adapters.LieModelL3U3Sylow
import CFSG.Adapters.LieModelSimple
import CFSG.GH74.GLS.Stage2.Signalizer.Odd87FU3Card
import CFSG.GH74.KGroups.L3EpsAutDiag
import CFSG.HardMathSupport.Solomon.Coordinator.L3BTorusPSU
import CFSG.RankThree.PartTwo.Sec4.Ronan148VLinTorus
public import CFSG.GH74.KGroups.L3EpsTest

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open Subgroup

theorem omega_inf_central_of_normalizer_pow {A : Type*} [Group A] [Finite A] {r : ℕ}
    [Fact r.Prime] (I : Subgroup A) [I.Normal] (S₀ : Subgroup A) (hS₀I : S₀ ≤ I)
    (hS₀ : Nat.card S₀ = r ^ (Nat.card I).factorization r) (N : ℕ) (hN : Nat.Coprime r N)
    (hact : ∀ b : A, (∀ s ∈ S₀, b * s * b⁻¹ ∈ S₀) → ∀ t ∈ S₀, t ^ r = 1 →
      b ^ N * t = t * b ^ N)
    (R : Subgroup A) (hR : IsPGroup r R)
    (hsyl : Nat.card (R ⊓ I : Subgroup A) = r ^ (Nat.card I).factorization r) :
    ∀ a ∈ R ⊓ I, a ^ r = 1 → ∀ b ∈ R, a * b = b * a := by
  have hcI : ∀ H : Subgroup A, H ≤ I → Nat.card H = r ^ (Nat.card I).factorization r →
      Nat.card (H.subgroupOf I) = r ^ (Nat.card I).factorization r := by
    intro H hH hc
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hH).toEquiv, hc]
  let P₀ : Sylow r I := Sylow.ofCard (S₀.subgroupOf I) (by rw [hcI S₀ hS₀I hS₀])
  let P₁ : Sylow r I := Sylow.ofCard ((R ⊓ I).subgroupOf I)
    (by rw [hcI _ inf_le_right hsyl])
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq I P₀ P₁
  have hmem : ∀ x : A, x ∈ R ⊓ I → (g : A)⁻¹ * x * g ∈ S₀ := by
    intro x hx
    have hxI : x ∈ I := (Subgroup.mem_inf.mp hx).2
    have h1 : (⟨x, hxI⟩ : I) ∈ (P₁ : Subgroup I) := by
      show (⟨x, hxI⟩ : I) ∈ (R ⊓ I).subgroupOf I
      exact Subgroup.mem_subgroupOf.mpr hx
    rw [← hg, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem,
      MulAut.smul_def, MulAut.conj_inv_apply] at h1
    have h2 : g⁻¹ * ⟨x, hxI⟩ * g ∈ S₀.subgroupOf I := h1
    exact Subgroup.mem_subgroupOf.mp h2
  have hmem' : ∀ y : A, y ∈ S₀ → (g : A) * y * (g : A)⁻¹ ∈ R ⊓ I := by
    intro y hy
    have hyI : y ∈ I := hS₀I hy
    have h1 : (⟨y, hyI⟩ : I) ∈ (P₀ : Subgroup I) := by
      show (⟨y, hyI⟩ : I) ∈ S₀.subgroupOf I
      exact Subgroup.mem_subgroupOf.mpr hy
    have h2 : (g * ⟨y, hyI⟩ * g⁻¹ : I) ∈ (P₁ : Subgroup I) := by
      rw [← hg, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem,
        MulAut.smul_def, MulAut.conj_inv_apply]
      have : g⁻¹ * (g * ⟨y, hyI⟩ * g⁻¹) * g = (⟨y, hyI⟩ : I) := by group
      rw [this]
      exact h1
    have h3 : (g * ⟨y, hyI⟩ * g⁻¹ : I) ∈ (R ⊓ I).subgroupOf I := h2
    have h4 := Subgroup.mem_subgroupOf.mp h3
    simpa using h4
  intro a ha har b hb
  set g' : A := (g : A) with hg'
  have hnorm : ∀ s ∈ S₀, (g'⁻¹ * b * g') * s * (g'⁻¹ * b * g')⁻¹ ∈ S₀ := by
    intro s hs
    have h1 : g' * s * g'⁻¹ ∈ R ⊓ I := hmem' s hs
    have h2 : b * (g' * s * g'⁻¹) * b⁻¹ ∈ R ⊓ I := by
      refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
      · exact R.mul_mem (R.mul_mem hb (Subgroup.mem_inf.mp h1).1) (R.inv_mem hb)
      · exact Subgroup.Normal.conj_mem inferInstance _ (Subgroup.mem_inf.mp h1).2 b
    have h3 := hmem _ h2
    have : (g'⁻¹ * b * g') * s * (g'⁻¹ * b * g')⁻¹ =
        g'⁻¹ * (b * (g' * s * g'⁻¹) * b⁻¹) * g' := by group
    rw [this]
    exact h3
  have ha0 : g'⁻¹ * a * g' ∈ S₀ := hmem a ha
  have har0 : (g'⁻¹ * a * g') ^ r = 1 := by
    have h := conj_pow (a := g'⁻¹) (b := a) (i := r)
    rw [inv_inv] at h
    rw [h, har]
    group
  have hc := hact _ hnorm _ ha0 har0
  set b' := g'⁻¹ * b * g' with hb'
  obtain ⟨k, hk⟩ := hR ⟨b, hb⟩
  have hbk : b' ^ r ^ k = 1 := by
    have hk' : b ^ r ^ k = 1 := by simpa using congrArg Subtype.val hk
    have h := conj_pow (a := g'⁻¹) (b := b) (i := r ^ k)
    rw [inv_inv] at h
    rw [hb', h, hk']
    group
  have hcop : Nat.Coprime N (orderOf b') :=
    Nat.Coprime.coprime_dvd_right (orderOf_dvd_of_pow_eq_one hbk)
      (Nat.Coprime.pow_right k hN.symm)
  obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime hcop
  have hc' : Commute b' (g'⁻¹ * a * g') := by
    rw [← hm]
    exact (Commute.pow_left hc m)
  have := congrArg (fun x => g' * x * g'⁻¹) hc'.eq
  simp only [hb', mul_assoc, mul_inv_cancel_left, mul_inv_cancel, mul_one] at this
  have this' : b * a = a * b := by simpa [← mul_assoc] using this
  exact this'.symm

theorem conj_mul_conj_inv {X : Type*} [Group X] (b : MulAut X) (s : X) :
    b * MulAut.conj s * b⁻¹ = MulAut.conj (b s) := by
  ext x
  simp [MulAut.conj_apply]

theorem omega_inner_central_of_normalizer_pow {X : Type*} [Group X] [Finite X]
    (hcen : Subgroup.center X = ⊥) {r : ℕ} [Fact r.Prime] (S₀ : Subgroup X)
    (hS₀ : Nat.card S₀ = r ^ (Nat.card X).factorization r) (N : ℕ) (hN : Nat.Coprime r N)
    (hact : ∀ b : MulAut X, (∀ s ∈ S₀, b s ∈ S₀) → ∀ t ∈ S₀, t ^ r = 1 → (b ^ N) t = t)
    (R : Subgroup (MulAut X)) (hR : IsPGroup r R)
    (hsyl : Nat.card (R ⊓ CFSG.ComponentClassification.OuterAutomorphisms.inner X : Subgroup _) =
      r ^ (Nat.card X).factorization r) :
    ∀ a ∈ R ⊓ CFSG.ComponentClassification.OuterAutomorphisms.inner X, a ^ r = 1 →
      ∀ b ∈ R, a * b = b * a := by
  classical
  set I := CFSG.ComponentClassification.OuterAutomorphisms.inner X with hI
  have hinj : Function.Injective (MulAut.conj : X →* MulAut X) := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have : x ∈ Subgroup.center X := by
      rw [Subgroup.mem_center_iff]
      intro y
      have := congrArg (fun φ : MulAut X => φ y) hx
      simp only [MulAut.conj_apply, MulAut.one_apply] at this
      calc y * x = (x * y * x⁻¹) * x := by rw [this]
        _ = x * y := by group
    rw [hcen] at this
    exact (Subgroup.mem_bot.mp this)
  have hcardI : Nat.card I = Nat.card X := by
    rw [hI, CFSG.ComponentClassification.OuterAutomorphisms.inner]
    exact Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv.symm
  have : I.Normal := CFSG.ComponentClassification.OuterAutomorphisms.inner_normal X
  have hle : S₀.map (MulAut.conj : X →* MulAut X) ≤ I := by
    rw [hI, CFSG.ComponentClassification.OuterAutomorphisms.inner]
    exact Subgroup.map_le_range _ _
  have hcard' : Nat.card (S₀.map (MulAut.conj : X →* MulAut X)) =
      r ^ (Nat.card I).factorization r := by
    rw [Subgroup.card_map_of_injective hinj, hS₀, hcardI]
  have hsyl' : Nat.card (R ⊓ I : Subgroup _) = r ^ (Nat.card I).factorization r := by
    rw [hcardI]; exact hsyl
  refine omega_inf_central_of_normalizer_pow I _ hle hcard' N hN ?_ R hR hsyl'
  intro b hb t ht htr
  obtain ⟨t₀, ht₀, rfl⟩ := Subgroup.mem_map.mp ht
  have ht₀r : t₀ ^ r = 1 := by
    apply hinj
    rw [map_pow, htr, map_one]
  have hbS : ∀ s ∈ S₀, b s ∈ S₀ := by
    intro s hs
    have h1 := hb _ (Subgroup.mem_map_of_mem _ hs)
    rw [conj_mul_conj_inv] at h1
    obtain ⟨s', hs', hs'e⟩ := Subgroup.mem_map.mp h1
    rw [← hinj hs'e]
    exact hs'
  have hfix := hact b hbS t₀ ht₀ ht₀r
  have h2 : b ^ N * MulAut.conj t₀ * (b ^ N)⁻¹ = MulAut.conj t₀ := by
    rw [conj_mul_conj_inv, hfix]
  calc b ^ N * MulAut.conj t₀ = (b ^ N * MulAut.conj t₀ * (b ^ N)⁻¹) * b ^ N := by group
    _ = MulAut.conj t₀ * b ^ N := by rw [h2]

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag

open CFSG.RankThree.PartTwo.Sec4.Ronan148V

open Matrix

private noncomputable def omcpl_prodHom (F : Type) [Field F] (m : ℕ) :
    (Fin 3 → rootsOfUnity m F) →* Fˣ where
  toFun d := ∏ i, (d i : Fˣ)
  map_one' := by simp
  map_mul' d e := by
    simp only [Pi.mul_apply, Subgroup.coe_mul]
    exact Finset.prod_mul_distrib

private noncomputable def omcpl_diagFun (F : Type) [Field F] (m : ℕ)
    (d : (omcpl_prodHom F m).ker) : torusSL (F := F) m :=
  ⟨CFSG.GH74.KGroups.L3Eps.diagSL ((d.1 0 : Fˣ) : F) ((d.1 1 : Fˣ) : F)
      ((d.1 2 : Fˣ) : F) (by
        have h1 : (d.1 0 : Fˣ) * (d.1 1 : Fˣ) * (d.1 2 : Fˣ) = 1 := by
          have h := MonoidHom.mem_ker.mp d.2
          rw [show (omcpl_prodHom F m) d.1 = ∏ i, (d.1 i : Fˣ) from rfl,
            Fin.prod_univ_three] at h
          exact h
        calc ((d.1 0 : Fˣ) : F) * ((d.1 1 : Fˣ) : F) * ((d.1 2 : Fˣ) : F)
            = (((d.1 0 : Fˣ) * (d.1 1 : Fˣ) * (d.1 2 : Fˣ) : Fˣ) : F) := by
              simp only [Units.val_mul]
          _ = 1 := by rw [h1, Units.val_one]),
    mem_torusSL.mpr ⟨d.1 0, d.1 1, d.1 2, (d.1 0).2, (d.1 1).2, (d.1 2).2,
      CFSG.GH74.KGroups.L3Eps.coe_diagSL _ _ _ _⟩⟩

private theorem omcpl_diagFun_bijective (F : Type) [Field F] (m : ℕ) :
    Function.Bijective (omcpl_diagFun F m) := by
  constructor
  · intro d e hde
    apply Subtype.ext
    funext i
    apply Subtype.ext
    apply Units.ext
    have hmat : diagonal ![((d.1 0 : Fˣ) : F), ((d.1 1 : Fˣ) : F), ((d.1 2 : Fˣ) : F)] =
        diagonal ![((e.1 0 : Fˣ) : F), ((e.1 1 : Fˣ) : F), ((e.1 2 : Fˣ) : F)] := by
      have hm := congrArg (fun g : torusSL (F := F) m =>
        ((g.1 : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)) hde
      simpa only [omcpl_diagFun, CFSG.GH74.KGroups.L3Eps.coe_diagSL] using hm
    have h := congrFun (congrFun hmat i) i
    fin_cases i <;> simpa using h
  · intro g
    obtain ⟨a, b, e, ha, hb, he, hg⟩ := mem_torusSL.mp g.2
    have hdet : (diagonal ![(a : F), (b : F), (e : F)]).det = 1 := by
      rw [← hg]; exact g.1.2
    rw [det_diagonal, Fin.prod_univ_three] at hdet
    have h1 : a * b * e = 1 := by
      apply Units.ext
      simpa only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        Matrix.head_cons, Matrix.tail_cons, Units.val_mul, Units.val_one] using hdet
    have hd_mem : (omcpl_prodHom F m) ![⟨a, (mem_rootsOfUnity m a).mpr ha⟩,
        ⟨b, (mem_rootsOfUnity m b).mpr hb⟩, ⟨e, (mem_rootsOfUnity m e).mpr he⟩] = 1 := by
      show (∏ i, ((![⟨a, (mem_rootsOfUnity m a).mpr ha⟩,
        ⟨b, (mem_rootsOfUnity m b).mpr hb⟩, ⟨e, (mem_rootsOfUnity m e).mpr he⟩] :
          Fin 3 → rootsOfUnity m F) i : Fˣ)) = 1
      rw [Fin.prod_univ_three]
      simpa only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        Matrix.head_cons, Matrix.tail_cons, Subtype.coe_mk] using h1
    set d : (omcpl_prodHom F m).ker :=
      ⟨![⟨a, (mem_rootsOfUnity m a).mpr ha⟩, ⟨b, (mem_rootsOfUnity m b).mpr hb⟩,
        ⟨e, (mem_rootsOfUnity m e).mpr he⟩], hd_mem⟩ with hd
    have hfield : (a : F) * (b : F) * (e : F) = 1 := by
      calc (a : F) * (b : F) * (e : F) = ((a * b * e : Fˣ) : F) := by
            simp only [Units.val_mul]
        _ = 1 := by rw [h1, Units.val_one]
    refine ⟨d, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    change (CFSG.GH74.KGroups.L3Eps.diagSL (a : F) (b : F) (e : F) hfield :
      Matrix (Fin 3) (Fin 3) F) = ((g.1 : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)
    rw [CFSG.GH74.KGroups.L3Eps.coe_diagSL]
    exact hg.symm

private theorem omcpl_card_torusSL {F : Type} [Field F] [Finite F] (m : ℕ) :
    Nat.card (torusSL (F := F) m) = (Nat.card (rootsOfUnity m F)) ^ 2 := by
  let μ := rootsOfUnity m F
  have hbij : Nat.card ((omcpl_prodHom F m).ker) = Nat.card (torusSL (F := F) m) :=
    Nat.card_congr (Equiv.ofBijective (omcpl_diagFun F m) (omcpl_diagFun_bijective F m))
  have hcard := Subgroup.card_ker_mul_card_range (omcpl_prodHom F m)
  have hrange : (omcpl_prodHom F m).range = μ := by
    ext x
    constructor
    · rintro ⟨d, rfl⟩
      exact μ.prod_mem (fun i _ => (d i).2)
    · intro hx
      refine ⟨![⟨x, hx⟩, 1, 1], ?_⟩
      show (∏ i, ((![⟨x, hx⟩, 1, 1] : Fin 3 → μ) i : Fˣ)) = x
      rw [Fin.prod_univ_three]
      simp
  have hdom : Nat.card (Fin 3 → μ) = Nat.card μ ^ 3 := by
    rw [Nat.card_fun]; simp
  rw [hbij, hrange, hdom, pow_succ] at hcard
  exact Nat.mul_right_cancel (Nat.card_pos (α := μ)) hcard

private theorem omcpl_torusSL_inf_scalars {F : Type} [Field F] {m : ℕ} (hm : Nat.Coprime m 3) :
    torusSL (F := F) m ⊓ scalars 3 F = ⊥ := by
  rw [eq_bot_iff]
  intro g hg
  rw [Subgroup.mem_bot]
  obtain ⟨hgt, hgs⟩ := Subgroup.mem_inf.mp hg
  obtain ⟨a, b, e, ha, hb, he, hgmat⟩ := mem_torusSL.mp hgt
  obtain ⟨c, hc3, hgc⟩ := mem_scalars.mp hgs
  have hdiag : diagonal ![(a : F), (b : F), (e : F)] = scalar (Fin 3) (c : F) := by
    rw [← hgmat, hgc]
  have hac : a = c := by
    apply Units.ext
    have := congrFun (congrFun hdiag 0) 0
    simpa [Matrix.scalar_apply] using this
  have hcm : c ^ m = 1 := by rw [← hac]; exact ha
  have hc1 : c = 1 := by
    have hgcd : c ^ Nat.gcd m 3 = 1 := pow_gcd_eq_one.mpr ⟨hcm, hc3⟩
    rw [hm.gcd_eq_one, pow_one] at hgcd
    exact hgcd
  apply Subtype.ext
  rw [hgc, hc1]
  simp [Matrix.scalar_apply, Matrix.diagonal_one]

private theorem omcpl_proj_injOn_torusSL {F : Type} [Field F] {m : ℕ} (hm : Nat.Coprime m 3)
    {A B : SpecialLinearGroup (Fin 3) F} (hA : A ∈ torusSL (F := F) m)
    (hB : B ∈ torusSL (F := F) m) (h : proj 3 F A = proj 3 F B) : A = B := by
  have hm2 : A⁻¹ * B ∈ torusSL (F := F) m ⊓ scalars 3 F :=
    ⟨(torusSL (F := F) m).mul_mem ((torusSL (F := F) m).inv_mem hA) hB,
      proj_eq_proj_iff.mp h⟩
  rw [omcpl_torusSL_inf_scalars hm] at hm2
  rwa [Subgroup.mem_bot, inv_mul_eq_one] at hm2

private noncomputable def omcpl_diagTorusEquiv {F : Type} [Field F] {m : ℕ}
    (hm : Nat.Coprime m 3) : torusSL (F := F) m ≃* diagTorus (F := F) m :=
  MulEquiv.ofBijective ((proj 3 F).subgroupMap (torusSL (F := F) m))
    ⟨fun a b hab => Subtype.ext (omcpl_proj_injOn_torusSL hm a.2 b.2 (congrArg Subtype.val hab)),
      (proj 3 F).subgroupMap_surjective _⟩

private theorem omcpl_card_rootsOfUnity {F : Type} [Field F] [Finite F] (m : ℕ) :
    Nat.card (rootsOfUnity m F) = Nat.gcd m (Nat.card F - 1) := by
  rw [rootsOfUnity_eq_ker, IsCyclic.card_powMonoidHom_ker, Nat.card_units, Nat.gcd_comm]

private theorem omcpl_card_specialLinear_center {F : Type} [Field F] [Finite F] (n : ℕ)
    (hn : 0 < n) :
    Nat.card (Subgroup.center (SpecialLinearGroup (Fin n) F)) = Nat.gcd n (Nat.card F - 1) := by
  rw [Nat.card_congr (Matrix.SpecialLinearGroup.center_equiv_rootsOfUnity' (R := F)
    (⟨0, hn⟩ : Fin n)).toEquiv]
  simpa using omcpl_card_rootsOfUnity (F := F) n

private theorem omcpl_card_diagTorus {F : Type} [Field F] [Finite F] {m : ℕ}
    (hm3 : Nat.Coprime m 3) (hmdvd : m ∣ Nat.card F - 1) :
    Nat.card (diagTorus (F := F) m) = m ^ 2 := by
  rw [← Nat.card_congr (omcpl_diagTorusEquiv hm3).toEquiv,
    omcpl_card_torusSL (F := F) m,
    omcpl_card_rootsOfUnity (F := F) m,
    Nat.gcd_eq_left hmdvd]

private theorem omcpl_factorization_projectiveSL {F : Type} [Field F] [Finite F] {r : ℕ}
    [Fact r.Prime] (hr5 : 5 ≤ r) (hrdvd : r ∣ Nat.card F - 1) :
    (Nat.card (projectiveSL 3 F)).factorization r =
      2 * (Nat.card F - 1).factorization r := by
  set q := Nat.card F with hq
  have hr : r.Prime := Fact.out
  have hq2 : 2 ≤ q := by
    have := Finite.one_lt_card (α := F)
    omega
  have hrq : ¬ r ∣ q := by
    intro h
    have h1 : r ∣ q - (q - 1) := Nat.dvd_sub h hrdvd
    have h2 : q - (q - 1) = 1 := by omega
    rw [h2] at h1
    exact hr.not_dvd_one h1
  have hrq1 : ¬ r ∣ q + 1 := by
    intro h
    have h1 : r ∣ q + 1 - (q - 1) := Nat.dvd_sub h hrdvd
    have h2 : q + 1 - (q - 1) = 2 := by omega
    rw [h2] at h1
    exact absurd ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).1 h1) (by omega)
  have hrq2 : ¬ r ∣ q ^ 2 + q + 1 := by
    intro h
    have hmul : r ∣ (q - 1) * (q + 2) := Dvd.dvd.mul_right hrdvd (q + 2)
    have h1 : r ∣ q ^ 2 + q + 1 - (q - 1) * (q + 2) :=
      Nat.dvd_sub h hmul
    have h2 : q ^ 2 + q + 1 - (q - 1) * (q + 2) = 3 := by
      have h3 : q ^ 2 + q + 1 = (q - 1) * (q + 2) + 3 := by
        rw [Nat.sub_mul, one_mul]
        have h : q * (q + 2) = q ^ 2 + 2 * q := by ring
        rw [h]; omega
      omega
    rw [h2] at h1
    exact absurd ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_three).1 h1) (by omega)
  have hZ : Nat.card (scalars 3 F) = Nat.gcd 3 (q - 1) := by
    rw [CFSG.LocalAnalysis.ComponentInitial.LinearFlag.scalars_eq_center]
    exact omcpl_card_specialLinear_center (F := F) 3 (by norm_num)
  have hrZ : ¬ r ∣ Nat.card (scalars 3 F) := by
    rw [hZ]
    intro h
    have : r ∣ 3 := h.trans (Nat.gcd_dvd_left 3 (q - 1))
    exact absurd ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_three).1 this) (by omega)
  have hPZ : Nat.card (projectiveSL 3 F) * Nat.card (scalars 3 F) =
      Nat.card (SpecialLinearGroup (Fin 3) F) := by
    rw [CFSG.LocalAnalysis.ComponentInitial.LinearFlag.card_projectiveSL]
    exact Nat.div_mul_cancel (Subgroup.card_subgroup_dvd_card (scalars 3 F))
  have hSL : Nat.card (SpecialLinearGroup (Fin 3) F) =
      q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 - 1)) := by
    have h := CFSG.LocalAnalysis.ComponentInitial.LinearFlag.card_SL_eq (K := F) (n := 3)
      (by norm_num)
    rw [show 3 * (3 - 1) / 2 = 3 from rfl,
      show Finset.Icc 2 3 = ({2, 3} : Finset ℕ) by decide,
      Finset.prod_pair (by norm_num)] at h
    exact h
  have hq2m1 : q ^ 2 - 1 ≠ 0 := Nat.sub_ne_zero_of_lt (one_lt_pow' (show 1 < q by omega) (by norm_num : (2:ℕ) ≠ 0))
  have hq3m1 : q ^ 3 - 1 ≠ 0 := Nat.sub_ne_zero_of_lt (one_lt_pow' (show 1 < q by omega) (by norm_num : (3:ℕ) ≠ 0))
  have hfac2 : (q ^ 2 - 1).factorization r = (q - 1).factorization r := by
    have h : q ^ 2 - 1 = (q - 1) * (q + 1) := by
      rw [Nat.sub_mul, one_mul]
      have h : q * (q + 1) = q ^ 2 + q := by ring
      rw [h]; omega
    rw [h, Nat.factorization_mul (by omega) (by omega), Finsupp.add_apply,
      Nat.factorization_eq_zero_of_not_dvd hrq1, add_zero]
  have hfac3 : (q ^ 3 - 1).factorization r = (q - 1).factorization r := by
    have h : q ^ 3 - 1 = (q - 1) * (q ^ 2 + q + 1) := by
      rw [Nat.sub_mul, one_mul]
      have h : q * (q ^ 2 + q + 1) = q ^ 3 + q ^ 2 + q := by ring
      rw [h]; omega
    rw [h, Nat.factorization_mul (by omega) (by nlinarith [hq2]), Finsupp.add_apply,
      Nat.factorization_eq_zero_of_not_dvd hrq2, add_zero]
  have hfacq : (q ^ 3).factorization r = 0 :=
    Nat.factorization_eq_zero_of_not_dvd fun h => hrq (hr.dvd_of_dvd_pow h)
  have hSfac : (Nat.card (SpecialLinearGroup (Fin 3) F)).factorization r =
      2 * (q - 1).factorization r := by
    rw [hSL, Nat.factorization_mul (pow_ne_zero 3 (by omega)) (mul_ne_zero hq2m1 hq3m1),
      Nat.factorization_mul hq2m1 hq3m1]
    simp only [Finsupp.add_apply]
    rw [hfacq, hfac2, hfac3]
    ring
  have hPf : (Nat.card (projectiveSL 3 F)).factorization r =
      (Nat.card (SpecialLinearGroup (Fin 3) F)).factorization r := by
    have h := congrArg (fun n => n.factorization r) hPZ
    rw [Nat.factorization_mul (Nat.card_pos.ne') (Nat.card_pos.ne'),
      Finsupp.add_apply, Nat.factorization_eq_zero_of_not_dvd hrZ, add_zero] at h
    exact h
  rw [hPf, hSfac]


private def omcpl_permPow {M : Type*} [Monoid M] (w : Equiv.Perm (Fin 3)) (u : ℕ) (v : Fin 3 → M) :
    Fin 3 → M :=
  fun i => v (w i) ^ u

private theorem omcpl_permPow_iterate {M : Type*} [CommMonoid M] (w : Equiv.Perm (Fin 3)) (u k : ℕ)
    (v : Fin 3 → M) : (omcpl_permPow w u)^[k] v = fun i => v ((w ^ k) i) ^ (u ^ k) := by
  induction k generalizing v with
  | zero => funext i; simp
  | succ k ih =>
    rw [Function.iterate_succ_apply, ih]
    funext i
    simp only [omcpl_permPow, pow_succ', Equiv.Perm.mul_apply, pow_mul]

private theorem omcpl_card_perm_fin_three : Fintype.card (Equiv.Perm (Fin 3)) = 6 := by
  rw [Fintype.card_perm, Fintype.card_fin]; rfl

private theorem omcpl_permPow_iterate_eq_self {M : Type*} [CommMonoid M] {r : ℕ} (hr : r.Prime)
    (w : Equiv.Perm (Fin 3)) {u : ℕ} (hu : Nat.Coprime u r) {v : Fin 3 → M}
    (hv : ∀ i, v i ^ r = 1) : (omcpl_permPow w u)^[6 * (r - 1)] v = v := by
  rw [omcpl_permPow_iterate]
  funext i
  have hw : w ^ (6 * (r - 1)) = 1 := by
    rw [pow_mul, ← omcpl_card_perm_fin_three, pow_card_eq_one, one_pow]
  have hmod : u ^ (6 * (r - 1)) % r = 1 % r := by
    have h1 : u ^ Nat.totient r ≡ 1 [MOD r] := Nat.ModEq.pow_totient hu
    rw [Nat.totient_prime hr] at h1
    have h2 := h1.pow 6
    rw [one_pow, ← pow_mul, mul_comm] at h2
    exact h2
  rw [hw, Equiv.Perm.one_apply, pow_eq_pow_mod _ (hv i), hmod,
    Nat.mod_eq_of_lt hr.one_lt, pow_one]

private theorem omcpl_exists_pow_of_ringEquiv {K : Type*} [Field K] (σ : K ≃+* K) {r : ℕ}
    (hr : r.Prime) :
    ∃ u : ℕ, Nat.Coprime u r ∧ ∀ x : Kˣ, x ^ r = 1 → σ (x : K) = (x : K) ^ u := by
  have : NeZero r := ⟨hr.ne_zero⟩
  obtain ⟨m, hm⟩ := rootsOfUnity.integer_power_of_ringEquiv' (n := r) σ
  set u₀ : ℕ := (m % (r : ℤ)).toNat with hu₀
  have hpow : ∀ x : Kˣ, x ^ r = 1 → σ (x : K) = (x : K) ^ u₀ := by
    intro x hx
    have hmem : x ∈ rootsOfUnity r K := (mem_rootsOfUnity r x).mpr hx
    have h1 := hm x hmem
    have hx' : x ^ m = x ^ u₀ := by
      have hr0 : (0 : ℤ) ≤ m % (r : ℤ) := Int.emod_nonneg _ (by exact_mod_cast hr.ne_zero)
      have hxr : x ^ (r : ℤ) = 1 := by rw [zpow_natCast, hx]
      rw [zpow_eq_zpow_emod m hxr, ← zpow_natCast, hu₀, Int.toNat_of_nonneg hr0]
    rw [h1, hx', Units.val_pow_eq_pow_val]
  by_cases hdvd : r ∣ u₀
  · refine ⟨1, Nat.coprime_one_left r, fun x hx => ?_⟩
    have hx1 : (x : K) = 1 := by
      have h := hpow x hx
      obtain ⟨k, hk⟩ := hdvd
      rw [hk, pow_mul, ← Units.val_pow_eq_pow_val, hx, Units.val_one, one_pow] at h
      exact σ.injective (h.trans σ.map_one.symm)
    rw [hx1, map_one, one_pow]
  · exact ⟨u₀, (Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd hr).mpr hdvd)), hpow⟩

private theorem omcpl_entryMap_eq_pow {K : Type} [Field K] {r : ℕ} (hr : r.Prime)
    (σ : K ≃+* K) (ε : ℕ) (hε : ε ≤ 1) :
    ∃ u : ℕ, Nat.Coprime u r ∧ ∀ x : Kˣ, x ^ r = 1 →
      CFSG.GH74.KGroups.L3Eps.entryMap (F := K) σ ε (x : K) = (x : K) ^ u := by
  obtain ⟨u₀, hu₀, hpow⟩ := omcpl_exists_pow_of_ringEquiv σ hr
  rcases (by omega : ε = 0 ∨ ε = 1) with rfl | rfl
  · exact ⟨u₀, hu₀, fun x hx => hpow x hx⟩
  · refine ⟨u₀ * (r - 1), ?_, fun x hx => ?_⟩
    · have hru : ¬ r ∣ u₀ := (hr.coprime_iff_not_dvd).mp (Nat.coprime_comm.mp hu₀)
      rw [Nat.coprime_comm, hr.coprime_iff_not_dvd]
      intro h
      rcases hr.dvd_mul.mp h with h' | h'
      · exact hru h'
      · exact Nat.not_dvd_of_pos_of_lt (Nat.sub_pos_of_lt hr.one_lt) (Nat.sub_one_lt hr.ne_zero) h'
    · show (if (1 : ℕ) = 0 then σ (x : K) else (σ (x : K))⁻¹) = (x : K) ^ (u₀ * (r - 1))
      rw [if_neg (by norm_num), hpow x hx]
      have hxr : (x : K) ^ r = 1 := by rw [← Units.val_pow_eq_pow_val, hx, Units.val_one]
      have hmul : (x : K) ^ (u₀ * (r - 1)) * (x : K) ^ u₀ = 1 := by
        rw [← pow_add]
        have : u₀ * (r - 1) + u₀ = u₀ * r := by
          calc u₀ * (r - 1) + u₀ = u₀ * (r - 1) + u₀ * 1 := by rw [Nat.mul_one]
            _ = u₀ * ((r - 1) + 1) := (Nat.mul_add u₀ (r - 1) 1).symm
            _ = u₀ * r := by rw [Nat.sub_add_cancel hr.one_le]
        rw [this, mul_comm u₀ r, pow_mul, hxr, one_pow]
      exact inv_eq_of_mul_eq_one_left hmul


private structure omcpl_Vec (K : Type) [Field K] (r : ℕ) where
  v : Fin 3 → Kˣ
  root : ∀ i, v i ^ r = 1
  prod : ∏ i, v i = 1

private noncomputable def omcpl_diagSLVec {K : Type} [Field K] {r : ℕ} (V : omcpl_Vec K r) :
    SpecialLinearGroup (Fin 3) K :=
  CFSG.GH74.KGroups.L3Eps.diagSL (V.v 0 : K) (V.v 1 : K) (V.v 2 : K) (by
    rw [← Units.val_mul, ← Units.val_mul, ← Fin.prod_univ_three, V.prod, Units.val_one])

private theorem omcpl_vec_cons_apply {K : Type} [Field K] (v : Fin 3 → Kˣ) (i : Fin 3) :
    (![(v 0 : K), (v 1 : K), (v 2 : K)] : Fin 3 → K) i = (v i : K) := by
  fin_cases i <;> rfl

private noncomputable def omcpl_permPowVec {K : Type} [Field K] {r : ℕ} (w : Equiv.Perm (Fin 3))
    (u : ℕ) (V : omcpl_Vec K r) : omcpl_Vec K r where
  v := omcpl_permPow w u V.v
  root := by
    intro i
    rw [omcpl_permPow, ← pow_mul, mul_comm u r, pow_mul, V.root (w i), one_pow]
  prod := by
    show (∏ i, V.v (w i) ^ u) = 1
    rw [Finset.prod_pow, Equiv.prod_comp w V.v, V.prod, one_pow]

private theorem omcpl_Vec_ext {K : Type} [Field K] {r : ℕ} {V W : omcpl_Vec K r}
    (h : V.v = W.v) : V = W := by
  cases V with
  | mk v r p =>
    cases W with
    | mk v' r' p' =>
      simp only at h
      subst h
      rfl

private theorem omcpl_permPowVec_iterate_v {K : Type} [Field K] {r : ℕ}
    (w : Equiv.Perm (Fin 3)) (u n : ℕ) (V : omcpl_Vec K r) :
    ((omcpl_permPowVec w u)^[n] V).v = (omcpl_permPow w u)^[n] V.v := by
  induction n generalizing V with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply, ih]
    rfl


private theorem omcpl_vec_injective {F : Type} [Field F] {a b c : F}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    Function.Injective (![a, b, c] : Fin 3 → F) := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all

private theorem omcpl_action {K : Type} [Field K] [Finite K] {r : ℕ} [Fact r.Prime] (hr5 : 5 ≤ r)
    (hrdvd : r ∣ Nat.card K - 1) (b : MulAut (projectiveSL 3 K))
    (hnorm : ∀ s ∈ diagTorus (F := K) (r ^ (Nat.card K - 1).factorization r),
      b s ∈ diagTorus (F := K) (r ^ (Nat.card K - 1).factorization r)) :
    ∃ (w : Equiv.Perm (Fin 3)) (u : ℕ), Nat.Coprime u r ∧
      ∀ V : omcpl_Vec K r,
        b (proj 3 K (omcpl_diagSLVec V)) =
          proj 3 K (omcpl_diagSLVec (omcpl_permPowVec w u V)) := by
  have hr : r.Prime := Fact.out
  have hrdvd' : r ∣ Nat.card Kˣ := by rwa [Nat.card_units]
  obtain ⟨ζ, hζ⟩ := exists_prime_orderOf_dvd_card' (G := Kˣ) r hrdvd'
  have hζr : ζ ^ r = 1 := by rw [← hζ]; exact pow_orderOf_eq_one ζ
  have ha1 : 1 ≤ (Nat.card K - 1).factorization r :=
    (hr.dvd_iff_one_le_factorization (Nat.sub_ne_zero_of_lt (Finite.one_lt_card (α := K)))).mp hrdvd
  have hζa : ζ ^ (r ^ (Nat.card K - 1).factorization r) = 1 :=
    orderOf_dvd_iff_pow_eq_one.mp (by rw [hζ]; exact dvd_pow_self r (by omega))
  have hζia : (ζ⁻¹) ^ (r ^ (Nat.card K - 1).factorization r) = 1 := by
    rw [inv_pow, hζa, inv_one]
  have hζne1 : ζ ≠ 1 := by
    intro h
    have := hζ
    rw [h, orderOf_one] at this
    exact hr.ne_one this.symm
  have hζneinv : ζ ≠ ζ⁻¹ := by
    intro h
    have h2 : ζ ^ 2 = 1 := by
      have hh : ζ * ζ = 1 := by
        have := congrArg (fun x => ζ * x) h
        rwa [mul_inv_cancel] at this
      simpa [pow_two] using hh
    have hdvd : r ∣ 2 := by
      rw [← hζ]
      exact orderOf_dvd_iff_pow_eq_one.mpr h2
    exact absurd hdvd (Nat.not_dvd_of_pos_of_lt (by norm_num) (by omega))
  have hζinvne1 : ζ⁻¹ ≠ 1 := fun h => hζne1 (inv_eq_one.mp h)
  have ht : (ζ : K) * ((ζ⁻¹ : Kˣ) : K) * 1 = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one, mul_one]
  have h1K : (ζ : K) ≠ 1 := fun h => hζne1 (Units.ext h)
  have h2K : ((ζ⁻¹ : Kˣ) : K) ≠ 1 := fun h => hζinvne1 (Units.ext h)
  have h3K : (ζ : K) ≠ ((ζ⁻¹ : Kˣ) : K) := fun h => hζneinv (Units.ext h)
  have hinj : Function.Injective (![(ζ : K), ((ζ⁻¹ : Kˣ) : K), (1 : K)] : Fin 3 → K) :=
    omcpl_vec_injective h3K h1K h2K
  have hmem : CFSG.GH74.KGroups.L3Eps.diagSL (ζ : K) ((ζ⁻¹ : Kˣ) : K) (1 : K) ht ∈
      torusSL (F := K) (r ^ (Nat.card K - 1).factorization r) :=
    mem_torusSL.mpr ⟨ζ, ζ⁻¹, 1, hζa, hζia, one_pow _,
      CFSG.GH74.KGroups.L3Eps.coe_diagSL _ _ _ _⟩
  have hmemdiag : proj 3 K (CFSG.GH74.KGroups.L3Eps.diagSL (ζ : K) ((ζ⁻¹ : Kˣ) : K)
      (1 : K) ht) ∈ diagTorus (F := K) (r ^ (Nat.card K - 1).factorization r) :=
    ⟨_, hmem, rfl⟩
  obtain ⟨g, hg, hgproj⟩ := Subgroup.mem_map.mp (hnorm _ hmemdiag)
  obtain ⟨aa, bb, ee, haa, hbb, hee, hgmat⟩ := mem_torusSL.mp hg
  have habc : (aa : K) * (bb : K) * (ee : K) = 1 := by
    have hdet : (diagonal ![(aa : K), (bb : K), (ee : K)]).det = 1 := by
      rw [← hgmat]; exact g.2
    rw [det_diagonal, Fin.prod_univ_three] at hdet
    exact hdet
  have hα : ∃ (x y z : K) (hxyz : x * y * z = 1),
      b (proj 3 K (CFSG.GH74.KGroups.L3Eps.diagSL (ζ : K) ((ζ⁻¹ : Kˣ) : K) (1 : K) ht)) =
        proj 3 K (CFSG.GH74.KGroups.L3Eps.diagSL x y z hxyz) := by
    refine ⟨(aa : K), (bb : K), (ee : K), habc, ?_⟩
    rw [← hgproj]
    exact congrArg (proj 3 K) (Subtype.ext (hgmat.trans
      (CFSG.GH74.KGroups.L3Eps.coe_diagSL _ _ _ _).symm))
  obtain ⟨σ, ε, π, hε, hact⟩ :=
    CFSG.GH74.KGroups.L3Eps.aut_diag_action b (ζ : K) ((ζ⁻¹ : Kˣ) : K) (1 : K) ht hinj hα
  obtain ⟨u, hu, hexp⟩ := omcpl_entryMap_eq_pow hr σ ε hε
  refine ⟨π, u, hu, fun V => ?_⟩
  have hprod : (V.v 0 : K) * (V.v 1 : K) * (V.v 2 : K) = 1 := by
    rw [← Units.val_mul, ← Units.val_mul, ← Fin.prod_univ_three, V.prod, Units.val_one]
  obtain ⟨h', hV⟩ := hact (V.v 0 : K) (V.v 1 : K) (V.v 2 : K) hprod
  have hstart : b (proj 3 K (omcpl_diagSLVec V)) = b (proj 3 K
      (CFSG.GH74.KGroups.L3Eps.diagSL (V.v 0 : K) (V.v 1 : K) (V.v 2 : K) hprod)) := by
    apply congrArg b
    apply congrArg (proj 3 K)
    apply Subtype.ext
    simp only [omcpl_diagSLVec, CFSG.GH74.KGroups.L3Eps.coe_diagSL]
  rw [hstart, hV]
  refine congrArg (proj 3 K) (CFSG.GH74.KGroups.L3Eps.diagSL_congr ?_ ?_ ?_)
  · rw [omcpl_vec_cons_apply, hexp (V.v (π 0)) (V.root (π 0))]
    show (V.v (π 0) : K) ^ u = ((V.v (π 0) ^ u : Kˣ) : K)
    rw [Units.val_pow_eq_pow_val]
  · rw [omcpl_vec_cons_apply, hexp (V.v (π 1)) (V.root (π 1))]
    show (V.v (π 1) : K) ^ u = ((V.v (π 1) ^ u : Kˣ) : K)
    rw [Units.val_pow_eq_pow_val]
  · rw [omcpl_vec_cons_apply, hexp (V.v (π 2)) (V.root (π 2))]
    show (V.v (π 2) : K) ^ u = ((V.v (π 2) ^ u : Kˣ) : K)
    rw [Units.val_pow_eq_pow_val]


private theorem omcpl_action_iterate {K : Type} [Field K] [Finite K] {r : ℕ} [Fact r.Prime]
    {b : MulAut (projectiveSL 3 K)}
    {w : Equiv.Perm (Fin 3)} {u : ℕ}
    (hP : ∀ V : omcpl_Vec K r, b (proj 3 K (omcpl_diagSLVec V)) =
      proj 3 K (omcpl_diagSLVec (omcpl_permPowVec w u V))) :
    ∀ (n : ℕ) (V : omcpl_Vec K r),
      (b ^ n) (proj 3 K (omcpl_diagSLVec V)) =
        proj 3 K (omcpl_diagSLVec ((omcpl_permPowVec w u)^[n] V)) := by
  intro n
  induction n with
  | zero => intro V; rfl
  | succ n ih =>
    intro V
    rw [pow_succ', Function.iterate_succ_apply']
    change b ((b ^ n) (proj 3 K (omcpl_diagSLVec V))) =
      proj 3 K (omcpl_diagSLVec (omcpl_permPowVec w u ((omcpl_permPowVec w u)^[n] V)))
    rw [ih V, hP]

private theorem omcpl_coprime_pow_three {r a : ℕ} (hr : r.Prime) (hr5 : 5 ≤ r) :
    Nat.Coprime (r ^ a) 3 := by
  have h3r : ¬ 3 ∣ r := by
    intro h
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hr).1 h
    omega
  exact Nat.coprime_comm.mpr ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr
    (fun h => h3r (Nat.prime_three.dvd_of_dvd_pow h)))

private theorem omcpl_mem_diagTorus_of_pow {K : Type} [Field K] [Finite K] {r : ℕ} [Fact r.Prime]
    (hr5 : 5 ≤ r) {t : projectiveSL 3 K}
    (ht : t ∈ diagTorus (F := K) (r ^ (Nat.card K - 1).factorization r)) (htr : t ^ r = 1) :
    t ∈ diagTorus (F := K) r := by
  have hr : r.Prime := Fact.out
  have hm3 := omcpl_coprime_pow_three (a := (Nat.card K - 1).factorization r) hr hr5
  obtain ⟨g, hg, rfl⟩ := Subgroup.mem_map.mp ht
  obtain ⟨aa, bb, ee, haa, hbb, hee, hgmat⟩ := mem_torusSL.mp hg
  have hscal : g ^ r ∈ scalars 3 K := by
    rw [← proj_eq_one_iff, map_pow, htr]
  have hmem : g ^ r ∈ torusSL (F := K) (r ^ (Nat.card K - 1).factorization r) ⊓ scalars 3 K :=
    ⟨(torusSL (F := K) (r ^ (Nat.card K - 1).factorization r)).pow_mem hg r, hscal⟩
  rw [omcpl_torusSL_inf_scalars hm3, Subgroup.mem_bot] at hmem
  have hpowmat : ((g ^ r : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      diagonal ![(aa : K) ^ r, (bb : K) ^ r, (ee : K) ^ r] := by
    rw [Matrix.SpecialLinearGroup.coe_pow, hgmat, diagonal_pow]
    congr 1
    funext i
    fin_cases i <;> rfl
  have hroot : ∀ i, (![aa, bb, ee] : Fin 3 → Kˣ) i ^ r = 1 := by
    intro i
    apply Units.ext
    have h1 : ((g ^ r : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = 1 := by
      rw [hmem]
      rfl
    have h2 := congrFun (congrFun (hpowmat.symm.trans h1) i) i
    fin_cases i <;> simpa [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons] using h2
  exact ⟨g, mem_torusSL.mpr ⟨aa, bb, ee, hroot 0, hroot 1, hroot 2, hgmat⟩, rfl⟩


open CFSG.LocalAnalysis.ComponentInitial in
theorem psl3_torus_leaf {K : Type} [Field K] [Finite K] {r : ℕ} [Fact r.Prime] (hr5 : 5 ≤ r)
    (hrq : r ∣ Nat.card K - 1) :
    ∃ S₀ : Subgroup (LinearFlag.projectiveSL 3 K),
      Nat.card S₀ = r ^ (Nat.card (LinearFlag.projectiveSL 3 K)).factorization r ∧
      ∀ b : MulAut (LinearFlag.projectiveSL 3 K), (∀ s ∈ S₀, b s ∈ S₀) →
        ∀ t ∈ S₀, t ^ r = 1 → (b ^ (6 * (r - 1))) t = t := by

  have hr : r.Prime := Fact.out
  refine ⟨diagTorus (F := K) (r ^ (Nat.card K - 1).factorization r), ?_, ?_⟩
  · have hmdvd : r ^ (Nat.card K - 1).factorization r ∣ Nat.card K - 1 :=
      (hr.pow_dvd_iff_le_factorization
        (Nat.sub_ne_zero_of_lt (Finite.one_lt_card (α := K)))).mpr le_rfl
    rw [omcpl_card_diagTorus (F := K) (omcpl_coprime_pow_three hr hr5) hmdvd,
      omcpl_factorization_projectiveSL (F := K) hr5 hrq, ← pow_mul,
      mul_comm ((Nat.card K - 1).factorization r) 2]
  · intro b hnorm t ht htr
    obtain ⟨g, hg, rfl⟩ := Subgroup.mem_map.mp (omcpl_mem_diagTorus_of_pow hr5 ht htr)
    obtain ⟨aa, bb, ee, haa, hbb, hee, hgmat⟩ := mem_torusSL.mp hg
    have hroot : ∀ i, (![aa, bb, ee] : Fin 3 → Kˣ) i ^ r = 1 := by
      intro i; fin_cases i <;> simp [haa, hbb, hee]
    have hprod : ∏ i, (![aa, bb, ee] : Fin 3 → Kˣ) i = 1 := by
      rw [Fin.prod_univ_three]
      apply Units.ext
      have hdet : (diagonal ![(aa : K), (bb : K), (ee : K)]).det = 1 := by
        rw [← hgmat]; exact g.2
      rw [det_diagonal, Fin.prod_univ_three] at hdet
      simpa only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        Matrix.head_cons, Matrix.tail_cons, Units.val_mul, Units.val_one] using hdet
    let V : omcpl_Vec K r := ⟨![aa, bb, ee], hroot, hprod⟩
    have hgV : proj 3 K g = proj 3 K (omcpl_diagSLVec V) := by
      apply congrArg (proj 3 K)
      apply Subtype.ext
      simp only [omcpl_diagSLVec, CFSG.GH74.KGroups.L3Eps.coe_diagSL]
      exact hgmat
    obtain ⟨w, u, hu, hP⟩ := omcpl_action hr5 hrq b hnorm
    have hiter := omcpl_action_iterate hP (6 * (r - 1)) V
    have hfix : ((omcpl_permPowVec w u)^[6 * (r - 1)] V) = V := by
      apply omcpl_Vec_ext
      rw [omcpl_permPowVec_iterate_v,
        omcpl_permPow_iterate_eq_self hr w hu (fun i => V.root i)]
    rw [hgV, hiter, hfix]

section

open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.HardMathSupport.Solomon.Coordinator
  CFSG.ClassicalGroups.UnitaryFlag

private theorem omcpu_isPrimeFormGram_one {K : Type} [Field K] :
    IsPrimeFormGram (1 : GL (Fin 3) K) where
  symm := by simp
  prime := by
    intro i j
    by_cases h : i = j
    · subst h; simp
    · simp [h]

private noncomputable def omcpu_prodHom {K : Type} [Field K] :
    (Fin 3 → Kˣ) →* Kˣ where
  toFun d := ∏ i, d i
  map_one' := by simp
  map_mul' d e := by
    simp only [Pi.mul_apply]
    rw [Finset.prod_mul_distrib]

private noncomputable def omcpu_E {K : Type} [Field K] (T : Subgroup Kˣ) :
    Subgroup (Fin 3 → Kˣ) :=
  (Subgroup.pi Set.univ (fun _ : Fin 3 => T)) ⊓ (omcpu_prodHom (K := K)).ker

private theorem omcpu_mem_E {K : Type} [Field K] {T : Subgroup Kˣ} {d : Fin 3 → Kˣ} :
    d ∈ omcpu_E T ↔ (∀ i, d i ∈ T) ∧ ∏ i, d i = 1 := by
  rw [omcpu_E, Subgroup.mem_inf, MonoidHom.mem_ker, Subgroup.mem_pi]
  simp [omcpu_prodHom]

private theorem omcpu_card_E {K : Type} [Field K] (T : Subgroup Kˣ) :
    Nat.card (omcpu_E T) = Nat.card T ^ 2 := by
  have hbij : Function.Bijective
      (fun d : omcpu_E T =>
        ((⟨d.1 0, (omcpu_mem_E.mp d.2).1 0⟩ : T),
          (⟨d.1 1, (omcpu_mem_E.mp d.2).1 1⟩ : T))) := by
    constructor
    · intro d e h
      apply Subtype.ext
      funext i
      have h0 : d.1 0 = e.1 0 := congrArg (Subtype.val) (congrArg Prod.fst h)
      have h1 : d.1 1 = e.1 1 := congrArg (Subtype.val) (congrArg Prod.snd h)
      have hd := (omcpu_mem_E.mp d.2).2
      have he := (omcpu_mem_E.mp e.2).2
      rw [Fin.prod_univ_three] at hd he
      have hd2 : (d.1 0 * d.1 1)⁻¹ = d.1 2 := by
        rw [inv_eq_iff_mul_eq_one]; exact hd
      have he2 : (e.1 0 * e.1 1)⁻¹ = e.1 2 := by
        rw [inv_eq_iff_mul_eq_one]; exact he
      fin_cases i
      · exact h0
      · exact h1
      · show d.1 2 = e.1 2
        rw [← hd2, ← he2, h0, h1]
    · rintro ⟨a, b⟩
      refine ⟨⟨![a.1, b.1, (a.1 * b.1)⁻¹], ?_⟩, ?_⟩
      · rw [omcpu_mem_E]
        refine ⟨fun i => ?_, ?_⟩
        · fin_cases i
          · exact a.2
          · exact b.2
          · exact T.inv_mem (T.mul_mem a.2 b.2)
        · rw [Fin.prod_univ_three]
          simp
      · simp
  rw [Nat.card_congr (Equiv.ofBijective _ hbij), Nat.card_prod, pow_two]

private abbrev omcpu_G (K : Type) [Field K] : Matrix (Fin 3) (Fin 3) K :=
  (1 : Matrix (Fin 3) (Fin 3) K)

private abbrev omcpu_Z {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K) :
    Subgroup (gramSU h (omcpu_G K)) :=
  normOneScalars h (gramSU h (omcpu_G K)) 3

private theorem omcpu_norm_eq_one_of_mem_rootsOfUnity {p f : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData p f K) {m : ℕ} (hm : m ∣ p ^ f + 1) {c : Kˣ}
    (hc : c ∈ rootsOfUnity m K) : h.norm (c : K) = 1 := by
  have hcm : c ^ m = 1 := (mem_rootsOfUnity m c).mp hc
  have hpow : (c : K) ^ (p ^ f + 1) = 1 := by
    rw [← Nat.mul_div_cancel' hm, pow_mul, ← Units.val_pow_eq_pow_val, hcm, Units.val_one,
      one_pow]
  rw [UnitaryFieldData.norm, h.bar_apply, ← pow_succ', hpow]

private theorem omcpu_diagHom_mem_gramSU {p f : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData p f K) {m : ℕ} (hm : m ∣ p ^ f + 1) {d : Fin 3 → Kˣ}
    (hd : d ∈ omcpu_E (rootsOfUnity m K)) :
    diagHom 3 K d ∈ gramSU h (omcpu_G K) := by
  obtain ⟨hdT, hdprod⟩ := omcpu_mem_E.mp hd
  rw [mem_gramSU]
  constructor
  · simp only [omcpu_G]
    rw [coe_diagHom, Matrix.diagonal_map (map_zero h.bar), Matrix.diagonal_transpose,
      Matrix.mul_one, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i
    simpa [UnitaryFieldData.norm, mul_comm] using
      omcpu_norm_eq_one_of_mem_rootsOfUnity h hm (hdT i)
  · rw [coe_diagHom, Matrix.det_diagonal]
    have h' : ((∏ i, d i : Kˣ) : K) = 1 := by rw [hdprod, Units.val_one]
    simpa [map_prod] using h'

private noncomputable def omcpu_EtoSU {p f : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData p f K) {m : ℕ} (hm : m ∣ p ^ f + 1) :
    omcpu_E (rootsOfUnity m K) →* gramSU h (omcpu_G K) where
  toFun d := ⟨diagHom 3 K d.1, omcpu_diagHom_mem_gramSU h hm d.2⟩
  map_one' := Subtype.ext (map_one (diagHom 3 K))
  map_mul' d e := Subtype.ext (map_mul (diagHom 3 K) d.1 e.1)

private noncomputable def omcpu_S₀ {p f : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData p f K) {m : ℕ} (hm : m ∣ p ^ f + 1) :
    Subgroup (primeFormP h (omcpu_G K)) :=
  ((QuotientGroup.mk' (omcpu_Z h)).comp (omcpu_EtoSU h hm)).range

private theorem omcpu_S₀_injective {p f : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData p f K) {m : ℕ} (hm : m ∣ p ^ f + 1) (hm3 : Nat.Coprime m 3) :
    Function.Injective
      ((QuotientGroup.mk' (omcpu_Z h)).comp (omcpu_EtoSU h hm)) := by
  intro d e hde
  have hmem : (omcpu_EtoSU h hm d)⁻¹ * (omcpu_EtoSU h hm e) ∈ omcpu_Z h := by
    rw [MonoidHom.comp_apply, QuotientGroup.mk'_apply] at hde
    exact QuotientGroup.eq.mp hde
  obtain ⟨c, -, hc3, hcmat⟩ := mem_normOneScalars.mp hmem
  have hL : ((omcpu_EtoSU h hm d)⁻¹ * (omcpu_EtoSU h hm e) : GL (Fin 3) K) =
      diagHom 3 K (d.1⁻¹ * e.1) := by
    have h1 : (omcpu_EtoSU h hm d)⁻¹ * (omcpu_EtoSU h hm e) =
        omcpu_EtoSU h hm (d⁻¹ * e) := by
      rw [← map_inv, ← map_mul]
    change (↑(((omcpu_EtoSU h hm d)⁻¹ * (omcpu_EtoSU h hm e) : gramSU h (omcpu_G K)) :
      GL (Fin 3) K)) = _
    rw [h1]
    rfl
  have hdiag : Matrix.diagonal (fun i => ((d.1⁻¹ * e.1) i : K)) =
      Matrix.diagonal (fun _ => (c : K)) := by
    have h2 : (diagHom 3 K (d.1⁻¹ * e.1) : GL (Fin 3) K) =
        GeneralLinearGroup.scalar (Fin 3) c := hL ▸ hcmat
    have h2m := congrArg (fun g : GL (Fin 3) K => (g : Matrix (Fin 3) (Fin 3) K)) h2
    rw [coe_diagHom, GeneralLinearGroup.coe_scalar] at h2m
    exact h2m
  have hpoint : ∀ i, (((d.1⁻¹ * e.1) i : Kˣ) : K) = (c : K) := by
    intro i
    have := congrFun (congrFun hdiag i) i
    simpa using this
  have hcT : c ∈ rootsOfUnity m K := by
    have hmemT : (d.1⁻¹ * e.1) 0 ∈ rootsOfUnity m K :=
      (omcpu_mem_E.mp (mul_mem (inv_mem d.2) e.2)).1 0
    rw [show c = (d.1⁻¹ * e.1) 0 from (Units.ext (hpoint 0)).symm]
    exact hmemT
  have hcm : c ^ m = 1 := (mem_rootsOfUnity m c).mp hcT
  have hc1 : c = 1 := by
    have h1 : orderOf c ∣ m := orderOf_dvd_of_pow_eq_one hcm
    have h2 : orderOf c ∣ 3 := orderOf_dvd_of_pow_eq_one hc3
    have h3 : orderOf c ∣ 1 := by
      have hg := Nat.dvd_gcd h1 h2
      rwa [hm3.gcd_eq_one] at hg
    exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp h3)
  have hfun : d.1⁻¹ * e.1 = 1 := by
    funext i
    have hh := Units.ext (hpoint i)
    rw [hc1] at hh
    simpa using hh
  have heq : e.1 = d.1 := by
    calc e.1 = d.1 * (d.1⁻¹ * e.1) := by group
      _ = d.1 * 1 := by rw [hfun]
      _ = d.1 := by group
  exact Subtype.ext heq.symm

private theorem omcpu_card_S₀ {p f : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData p f K) {m : ℕ} (hm : m ∣ p ^ f + 1) (hm3 : Nat.Coprime m 3) :
    Nat.card (omcpu_S₀ h hm) = Nat.card (rootsOfUnity m K) ^ 2 := by
  have hinj := omcpu_S₀_injective h hm hm3
  have h1 : Nat.card (omcpu_S₀ h hm) =
      Nat.card (omcpu_E (rootsOfUnity m K)) :=
    (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm
  rw [h1, omcpu_card_E]

private theorem omcpu_not_dvd_sub_one {q r : ℕ} (hr : r.Prime) (hr5 : 5 ≤ r)
    (hq2 : 2 ≤ q) (hdvd : r ∣ q + 1) : ¬ r ∣ q - 1 := by
  intro h
  have h2 : r ∣ (q + 1) - (q - 1) := Nat.dvd_sub hdvd h
  have h3 : (q + 1) - (q - 1) = 2 := by omega
  rw [h3] at h2
  have hr2 : r = 2 := (Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).mp h2
  omega

private theorem omcpu_not_dvd_self {q r : ℕ} (hr : r.Prime) (hdvd : r ∣ q + 1) :
    ¬ r ∣ q := by
  intro h
  have h2 : r ∣ (q + 1) - q := Nat.dvd_sub hdvd h
  have h3 : (q + 1) - q = 1 := by omega
  rw [h3] at h2
  exact hr.not_dvd_one h2

private theorem omcpu_sq_sub_add {q : ℕ} (hq2 : 2 ≤ q) :
    q ^ 2 - q + 1 = (q + 1) * (q - 2) + 3 := by
  have h1 : q ≤ q ^ 2 := by nlinarith
  apply Nat.cast_injective (R := ℤ)
  push_cast [Nat.cast_sub h1, Nat.cast_sub hq2]
  ring

private theorem omcpu_cube_add_one {q : ℕ} (hq2 : 2 ≤ q) :
    q ^ 3 + 1 = (q + 1) * (q ^ 2 - q + 1) := by
  have h1 : q ≤ q ^ 2 := by nlinarith
  apply Nat.cast_injective (R := ℤ)
  push_cast [Nat.cast_sub h1]
  ring

private theorem omcpu_not_dvd_sq_sub_add_one {q r : ℕ} (hr : r.Prime) (hr5 : 5 ≤ r)
    (hq2 : 2 ≤ q) (hdvd : r ∣ q + 1) : ¬ r ∣ q ^ 2 - q + 1 := by
  intro h
  have h1 : r ∣ (q + 1) * (q - 2) := Dvd.dvd.mul_right hdvd _
  have h2 : r ∣ (q ^ 2 - q + 1) - (q + 1) * (q - 2) := Nat.dvd_sub h h1
  have h3 : (q ^ 2 - q + 1) - (q + 1) * (q - 2) = 3 := by
    have := omcpu_sq_sub_add hq2
    omega
  rw [h3] at h2
  have : r = 3 := (Nat.prime_dvd_prime_iff_eq hr Nat.prime_three).mp h2
  omega

private theorem omcpu_factorization_numerator {q r : ℕ} (hr : r.Prime) (hr5 : 5 ≤ r)
    (hq2 : 2 ≤ q) (hdvd : r ∣ q + 1) :
    (q ^ 3 * (q ^ 2 - 1) * (q ^ 3 + 1)).factorization r = 2 * (q + 1).factorization r := by
  have hq3 : q ^ 3 ≠ 0 := by positivity
  have hq3p1 : q ^ 3 + 1 ≠ 0 := by positivity
  have hq2m1 : q ^ 2 - 1 ≠ 0 := by
    have : 1 < q ^ 2 := by nlinarith
    omega
  have hq1m : q - 1 ≠ 0 := by omega
  have hq1p : q + 1 ≠ 0 := by positivity
  have hq2m1' : q ^ 2 - q + 1 ≠ 0 := by omega
  have hsq : q ^ 2 - 1 = (q - 1) * (q + 1) := by
    rw [mul_comm (q - 1) (q + 1), ← Nat.sq_sub_sq q 1, one_pow]
  have hqfac : q.factorization r = 0 :=
    Nat.factorization_eq_zero_of_not_dvd (omcpu_not_dvd_self hr hdvd)
  have hq3fac : (q ^ 3).factorization r = 0 := by
    rw [Nat.factorization_pow]; simp [hqfac]
  have hm1fac : (q - 1).factorization r = 0 :=
    Nat.factorization_eq_zero_of_not_dvd (omcpu_not_dvd_sub_one hr hr5 hq2 hdvd)
  have hsqm1fac : (q ^ 2 - 1).factorization r = (q + 1).factorization r := by
    rw [hsq, Nat.factorization_mul hq1m hq1p, Finsupp.add_apply, hm1fac, zero_add]
  have hcu2fac : (q ^ 2 - q + 1).factorization r = 0 :=
    Nat.factorization_eq_zero_of_not_dvd (omcpu_not_dvd_sq_sub_add_one hr hr5 hq2 hdvd)
  have hcufac : (q ^ 3 + 1).factorization r = (q + 1).factorization r := by
    rw [omcpu_cube_add_one hq2, Nat.factorization_mul hq1p hq2m1', Finsupp.add_apply,
      hcu2fac, add_zero]
  rw [Nat.factorization_mul (mul_ne_zero hq3 hq2m1) hq3p1, Finsupp.add_apply,
    Nat.factorization_mul hq3 hq2m1, Finsupp.add_apply, hq3fac, hsqm1fac, hcufac]
  ring

private theorem omcpu_factorization_psu {p f : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData p f K) {r : ℕ} (hr : r.Prime) (hr5 : 5 ≤ r)
    (hrq : r ∣ p ^ f + 1) :
    (Nat.card (unitaryPSU h 3)).factorization r = 2 * (p ^ f + 1).factorization r := by
  have := h.finite
  have hq2 : 2 ≤ p ^ f := by
    have hpos : 0 < p ^ f + 1 := by positivity
    have := Nat.le_of_dvd hpos hrq
    omega
  have hUS := CFSG.GH74.GLS.Stage2.Signalizer.Odd87.card_unitarySU_three h
  have hZ := card_unitaryScalars h (n := 3) (by norm_num)
  have hquot := Subgroup.card_eq_card_quotient_mul_card_subgroup (unitaryScalars h 3)
  have hmain : Nat.card (unitaryPSU h 3) * Nat.gcd 3 (p ^ f + 1) =
      (p ^ f) ^ 3 * ((p ^ f) ^ 2 - 1) * ((p ^ f) ^ 3 + 1) := by
    rw [← hZ, ← hUS]
    exact hquot.symm
  have hfac := omcpu_factorization_numerator (q := p ^ f) hr hr5 hq2 hrq
  have hgcd0 : (Nat.gcd 3 (p ^ f + 1)).factorization r = 0 := by
    apply Nat.factorization_eq_zero_of_not_dvd
    intro hd
    have h3 : r ∣ 3 := hd.trans (Nat.gcd_dvd_left 3 (p ^ f + 1))
    have : r = 3 := (Nat.prime_dvd_prime_iff_eq hr Nat.prime_three).mp h3
    omega
  have hne : Nat.card (unitaryPSU h 3) ≠ 0 := by
    have : Nonempty (unitaryPSU h 3) := ⟨1⟩
    exact Nat.card_pos.ne'
  have hgne : Nat.gcd 3 (p ^ f + 1) ≠ 0 := (Nat.gcd_pos_of_pos_left _ (by norm_num)).ne'
  calc (Nat.card (unitaryPSU h 3)).factorization r
      = (Nat.card (unitaryPSU h 3) * Nat.gcd 3 (p ^ f + 1)).factorization r := by
        rw [Nat.factorization_mul hne hgne, Finsupp.add_apply, hgcd0, add_zero]
    _ = ((p ^ f) ^ 3 * ((p ^ f) ^ 2 - 1) * ((p ^ f) ^ 3 + 1)).factorization r := by
        rw [hmain]
    _ = 2 * (p ^ f + 1).factorization r := hfac

private theorem omcpu_factorization_P {p f : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData p f K) {r : ℕ} (hr : r.Prime) (hr5 : 5 ≤ r)
    (hrq : r ∣ p ^ f + 1) :
    (Nat.card (primeFormP h (omcpu_G K))).factorization r =
      2 * (p ^ f + 1).factorization r := by
  have hcard : Nat.card (primeFormP h (omcpu_G K)) = Nat.card (unitaryPSU h 3) := by
    obtain ⟨e⟩ := nonempty_primeFormP_mulEquiv (h := h) (C := (1 : GL (Fin 3) K))
      omcpu_isPrimeFormGram_one
    exact Nat.card_congr e.toEquiv
  rw [hcard]
  exact omcpu_factorization_psu h hr hr5 hrq

private theorem omcpu_hra {p f r : ℕ} (hr : r.Prime) (_hrq : r ∣ p ^ f + 1) :
    r ^ (p ^ f + 1).factorization r ∣ p ^ f + 1 :=
  (hr.pow_dvd_iff_le_factorization (by positivity)).mpr le_rfl

private theorem omcpu_card_S₀_eq {p f : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData p f K) {r : ℕ} (hr : r.Prime) (hr5 : 5 ≤ r)
    (hrq : r ∣ p ^ f + 1) :
    Nat.card (omcpu_S₀ h (omcpu_hra hr hrq)) =
      r ^ (Nat.card (primeFormP h (omcpu_G K))).factorization r := by
  have := h.finite
  have hr3 : ¬ r ∣ 3 := by
    intro h
    have : r = 3 := (Nat.prime_dvd_prime_iff_eq hr Nat.prime_three).mp h
    omega
  have hm3 : Nat.Coprime (r ^ (p ^ f + 1).factorization r) 3 :=
    Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd hr).mpr hr3)
  rw [omcpu_card_S₀ h (omcpu_hra hr hrq) hm3, omcpu_factorization_P h hr hr5 hrq]
  have hpow : p ^ (2 * f) = (p ^ f) ^ 2 :=
    (congrArg (fun e => p ^ e) (Nat.mul_comm 2 f)).trans (pow_mul p f 2)
  have hKq : Nat.card K - 1 = (p ^ f) ^ 2 - 1 := by
    rw [h.card, hpow]
  have hdvd2 : r ^ (p ^ f + 1).factorization r ∣ (p ^ f) ^ 2 - 1 := by
    have h1 : (p ^ f + 1) ∣ (p ^ f) ^ 2 - 1 :=
      ⟨p ^ f - 1, by
        rw [← Nat.sq_sub_sq (p ^ f) 1, one_pow]⟩
    exact (omcpu_hra hr hrq).trans h1
  have hT : Nat.card (rootsOfUnity (r ^ (p ^ f + 1).factorization r) K) =
      r ^ (p ^ f + 1).factorization r := by
    rw [omcpl_card_rootsOfUnity, hKq]
    exact Nat.gcd_eq_left hdvd2
  rw [hT]
  rw [(pow_mul r ((p ^ f + 1).factorization r) 2).symm.trans
    (congrArg (fun e => r ^ e) (Nat.mul_comm ((p ^ f + 1).factorization r) 2))]

private noncomputable def omcpu_step {p f : ℕ} {K : Type} [Field K]
    (_h : UnitaryFieldData p f K) {m : ℕ} (_hm : m ∣ p ^ f + 1)
    (w : Equiv.Perm (Fin 3)) (u : ℕ) :
    omcpu_E (rootsOfUnity m K) → omcpu_E (rootsOfUnity m K) :=
  fun x => ⟨omcpl_permPow w u x.1, by
    obtain ⟨hxT, hxp⟩ := omcpu_mem_E.mp x.2
    rw [omcpu_mem_E]
    refine ⟨fun i => ?_, ?_⟩
    · change x.1 (w i) ^ u ∈ rootsOfUnity m K
      rw [mem_rootsOfUnity, ← pow_mul, Nat.mul_comm, pow_mul,
        (mem_rootsOfUnity m (x.1 (w i))).mp (hxT (w i)), one_pow]
    · change ∏ i, x.1 (w i) ^ u = 1
      rw [Finset.prod_pow, Equiv.prod_comp, hxp, one_pow]
    ⟩

private theorem omcpu_A_monomial {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K)
    {m r : ℕ} (hr : r.Prime) (hr5 : 5 ≤ r) (hm : m ∣ p ^ f + 1) (hmr : r ∣ m)
    (hrq : r ∣ p ^ f + 1)
    (hC : IsPrimeFormGram (1 : GL (Fin 3) K))
    (A : primeFormUnitary h (omcpu_G K)) (φ : K ≃+* K)
    (hA : ∀ s ∈ omcpu_S₀ h hm,
      (primeFormConjHom h (omcpu_G K) A * primeFormFieldHom h hC φ) s ∈ omcpu_S₀ h hm) :
    ∃ ρ : Equiv.Perm (Fin 3), ∀ i j, (A : GL (Fin 3) K) i j ≠ 0 → i = ρ j := by
  have : Finite K := h.finite
  have : Fact r.Prime := ⟨hr⟩
  have hKunits : r ∣ Nat.card Kˣ := by
    have hpow : p ^ (2 * f) = (p ^ f) ^ 2 :=
      (congrArg (fun e => p ^ e) (Nat.mul_comm 2 f)).trans (pow_mul p f 2)
    have hc : Nat.card K - 1 = (p ^ f) ^ 2 - 1 := by rw [h.card, hpow]
    rw [Nat.card_units, hc,
      show (p ^ f) ^ 2 - 1 = (p ^ f - 1) * (p ^ f + 1) by
        rw [mul_comm, ← Nat.sq_sub_sq (p ^ f) 1, one_pow]]
    exact hrq.trans ⟨p ^ f - 1, by ring⟩
  obtain ⟨ζ, hζ⟩ := exists_prime_orderOf_dvd_card' (G := Kˣ) r hKunits
  have hζpow : ζ ^ r = 1 := (orderOf_dvd_iff_pow_eq_one).mp (by rw [hζ])
  have hζ1 : ζ ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hζ
    have := hr.two_le
    omega
  have hζm : ζ ^ m = 1 := by
    obtain ⟨k, hk⟩ := hmr
    rw [hk, pow_mul, hζpow, one_pow]
  obtain ⟨u, hu_cop, hpow⟩ := omcpl_exists_pow_of_ringEquiv φ hr
  have hu : ∀ x : Kˣ, x ^ r = 1 → Units.map (φ : K →* K) x = x ^ u :=
    fun x hx => Units.ext (hpow x hx)
  let d₁ : Fin 3 → Kˣ := ![ζ, ζ⁻¹, 1]
  have hd₁T : ∀ i, d₁ i ∈ rootsOfUnity m K := by
    intro i
    rw [mem_rootsOfUnity]
    fin_cases i
    · show ζ ^ m = 1
      exact hζm
    · show (ζ⁻¹) ^ m = 1
      rw [inv_pow, hζm, inv_one]
    · show (1 : Kˣ) ^ m = 1
      rw [one_pow]
  have hd₁p : ∏ i, d₁ i = 1 := by
    rw [Fin.prod_univ_three]
    simp [d₁]
  have hd₁r : ∀ i, d₁ i ^ r = 1 := by
    intro i
    fin_cases i
    · show ζ ^ r = 1
      exact hζpow
    · show (ζ⁻¹) ^ r = 1
      rw [inv_pow, hζpow, inv_one]
    · show (1 : Kˣ) ^ r = 1
      rw [one_pow]
  let x₁ : omcpu_E (rootsOfUnity m K) := ⟨d₁, omcpu_mem_E.mpr ⟨hd₁T, hd₁p⟩⟩
  have hfieldd : (glAut φ (diagHom 3 K d₁) : GL (Fin 3) K) = diagHom 3 K (fun i => d₁ i ^ u) := by
    rw [glAut_diagHom]
    congr 1
    funext i
    exact hu (d₁ i) (hd₁r i)
  let X : gramSU h (omcpu_G K) :=
    ⟨(A : GL (Fin 3) K) * glAut φ (diagHom 3 K d₁) * (A : GL (Fin 3) K)⁻¹,
      conj_mem_gramSU h _ A.2 (primeFormFieldSU h hC φ (omcpu_EtoSU h hm x₁)).2⟩
  have ht₁ : ((omcpu_EtoSU h hm x₁ : gramSU h (omcpu_G K)) : primeFormP h (omcpu_G K)) ∈
      omcpu_S₀ h hm := ⟨x₁, rfl⟩
  have hmem₁ : (primeFormConjHom h (omcpu_G K) A * primeFormFieldHom h hC φ)
      ((omcpu_EtoSU h hm x₁ : gramSU h (omcpu_G K)) : primeFormP h (omcpu_G K)) ∈
      omcpu_S₀ h hm := hA _ ht₁
  obtain ⟨y, hy⟩ := hmem₁
  have hBt : (primeFormConjHom h (omcpu_G K) A * primeFormFieldHom h hC φ)
      ((omcpu_EtoSU h hm x₁ : gramSU h (omcpu_G K)) : primeFormP h (omcpu_G K)) =
      (X : primeFormP h (omcpu_G K)) := by
    change primeFormConjHom h (omcpu_G K) A
      (primeFormFieldAut h hC φ
        ((omcpu_EtoSU h hm x₁ : gramSU h (omcpu_G K)) : primeFormP h (omcpu_G K))) =
      (X : primeFormP h (omcpu_G K))
    rw [primeFormFieldAut_mk, primeFormConjHom_mk]
    exact congrArg (QuotientGroup.mk' (omcpu_Z h)) (Subtype.ext rfl)
  rw [hBt] at hy
  have hmem : ((omcpu_EtoSU h hm y : gramSU h (omcpu_G K))⁻¹ * X) ∈ omcpu_Z h :=
    QuotientGroup.eq.mp hy
  obtain ⟨c, hcnorm, hc3, hcmat⟩ := mem_normOneScalars.mp hmem
  have hcgl : (X : GL (Fin 3) K) =
      (omcpu_EtoSU h hm y : GL (Fin 3) K) * GeneralLinearGroup.scalar (Fin 3) c := by
    calc (X : GL (Fin 3) K) =
        (omcpu_EtoSU h hm y : GL (Fin 3) K) *
          (((omcpu_EtoSU h hm y : gramSU h (omcpu_G K))⁻¹ * X : gramSU h (omcpu_G K)) :
            GL (Fin 3) K) := by
          rw [Subgroup.coe_mul, Subgroup.coe_inv]
          group
      _ = (omcpu_EtoSU h hm y : GL (Fin 3) K) * GeneralLinearGroup.scalar (Fin 3) c := by
          rw [hcmat]
  have hscal : ((GeneralLinearGroup.scalar (Fin 3) c : GL (Fin 3) K) :
      Matrix (Fin 3) (Fin 3) K) = Matrix.diagonal (fun _ => (c : K)) := by
    rw [GeneralLinearGroup.coe_scalar]
    rfl
  have hYmat : ((omcpu_EtoSU h hm y : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      Matrix.diagonal (fun i => (y.1 i : K)) := by
    rw [show (omcpu_EtoSU h hm y : GL (Fin 3) K) = diagHom 3 K y.1 from rfl, coe_diagHom]
  have hXmat : ((X : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      ((A : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
        Matrix.diagonal (fun i => ((d₁ i ^ u : Kˣ) : K)) *
        ((A : GL (Fin 3) K)⁻¹ : Matrix (Fin 3) (Fin 3) K) := by
    change (((A : GL (Fin 3) K) * glAut φ (diagHom 3 K d₁) * (A : GL (Fin 3) K)⁻¹ :
      GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = _
    rw [Units.val_mul, Units.val_mul, hfieldd, coe_diagHom]
    rw [Matrix.coe_units_inv]
  have hmat : ((X : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      Matrix.diagonal (fun i => (y.1 i : K) * (c : K)) := by
    have hco : ((X : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
        ((omcpu_EtoSU h hm y : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
          ((GeneralLinearGroup.scalar (Fin 3) c : GL (Fin 3) K) :
            Matrix (Fin 3) (Fin 3) K) := by
      have := congrArg (fun g : GL (Fin 3) K => (g : Matrix (Fin 3) (Fin 3) K)) hcgl
      simpa [Units.val_mul] using this
    rw [hYmat, hscal, Matrix.diagonal_mul_diagonal] at hco
    exact hco
  have heq : ((A : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
      Matrix.diagonal (fun i => ((d₁ i ^ u : Kˣ) : K)) =
      Matrix.diagonal (fun i => (y.1 i : K) * (c : K)) *
        ((A : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
    have h1 : ((A : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
        Matrix.diagonal (fun i => ((d₁ i ^ u : Kˣ) : K)) *
        ((A : GL (Fin 3) K)⁻¹ : Matrix (Fin 3) (Fin 3) K) =
        Matrix.diagonal (fun i => (y.1 i : K) * (c : K)) := by
      rw [← hXmat, hmat]
    have hinv : ((A : GL (Fin 3) K)⁻¹ : Matrix (Fin 3) (Fin 3) K) *
        ((A : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = 1 := by
      simp
    have h2 := congrArg (fun M : Matrix (Fin 3) (Fin 3) K =>
      M * ((A : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) h1
    rw [Matrix.mul_assoc, hinv, Matrix.mul_one] at h2
    exact h2
  have hζu1 : ζ ^ u ≠ 1 := by
    intro h1
    have hru : r ∣ u := by rw [← hζ]; exact orderOf_dvd_of_pow_eq_one h1
    have hru1 : r ∣ 1 := by
      have hd := Nat.dvd_gcd hru (dvd_refl r)
      rwa [hu_cop.gcd_eq_one] at hd
    have : r = 1 := Nat.dvd_one.mp hru1
    omega
  have hζu2 : ζ ^ u ≠ (ζ ^ u)⁻¹ := by
    intro h2
    have h2' : (ζ ^ u) ^ 2 = 1 := by
      rw [pow_two]
      nth_rewrite 1 [h2]
      rw [inv_mul_cancel]
    have hru : r ∣ 2 := by
      have hru2 : r ∣ u * 2 := by
        rw [← hζ]
        refine orderOf_dvd_of_pow_eq_one ?_
        rw [pow_mul, h2']
      exact hu_cop.symm.dvd_of_dvd_mul_left hru2
    have : r = 2 := (Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).mp hru
    omega
  have hf : Function.Injective (fun i : Fin 3 => ((d₁ i ^ u : Kˣ) : K)) := by
    have hfun : (fun i : Fin 3 => ((d₁ i ^ u : Kˣ) : K)) =
        (fun i : Fin 3 => ((![ζ ^ u, (ζ ^ u)⁻¹, 1] : Fin 3 → Kˣ) i : K)) := by
      funext i
      fin_cases i <;> simp [d₁, inv_pow]
    rw [hfun]
    intro i j hij
    fin_cases i <;> fin_cases j <;>
      simp only [Fin.reduceFinMk, Matrix.cons_val_zero, Matrix.cons_val_one] at hij ⊢
    all_goals
      first
      | rfl
      | exact absurd (Units.ext hij) hζu2
      | exact absurd (Units.ext hij) hζu1
      | exact absurd (Units.ext hij.symm) hζu2
      | exact absurd (Units.ext hij.symm) hζu1
      | exact absurd (inv_eq_one.mp (Units.ext hij)) hζu1
      | exact absurd (inv_eq_one.mp (Units.ext hij.symm)) hζu1
  obtain ⟨ρ, hρ⟩ := GH74.KGroups.L3Eps.exists_perm_of_conj_diag (A : GL (Fin 3) K)
    (fun i => ((d₁ i ^ u : Kˣ) : K)) (fun i => (y.1 i : K) * (c : K)) hf heq
  exact ⟨ρ, hρ⟩

private theorem omcpu_B_step {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K)
    {m : ℕ} (hm : m ∣ p ^ f + 1) (hC : IsPrimeFormGram (1 : GL (Fin 3) K))
    (A : primeFormUnitary h (omcpu_G K)) (φ : K ≃+* K)
    {r u : ℕ} (hu : ∀ x : Kˣ, x ^ r = 1 → Units.map (φ : K →* K) x = x ^ u)
    {ρ : Equiv.Perm (Fin 3)}
    (hρ : ∀ i j, (A : GL (Fin 3) K) i j ≠ 0 → i = ρ j) :
    ∀ x : omcpu_E (rootsOfUnity m K), (∀ i, x.1 i ^ r = 1) →
      (primeFormConjHom h (omcpu_G K) A * primeFormFieldHom h hC φ)
        ((omcpu_EtoSU h hm x : gramSU h (omcpu_G K)) : primeFormP h (omcpu_G K)) =
      ((omcpu_EtoSU h hm (omcpu_step h hm ρ.symm u x) : gramSU h (omcpu_G K)) :
        primeFormP h (omcpu_G K)) := by
  intro x hxr
  set d : Fin 3 → Kˣ := x.1 with hd
  have hdT : ∀ i, d i ∈ rootsOfUnity m K := (omcpu_mem_E.mp x.2).1
  have hdp : ∏ i, d i = 1 := (omcpu_mem_E.mp x.2).2
  have hfield : ((primeFormFieldSU h hC φ (omcpu_EtoSU h hm x) : gramSU h (omcpu_G K)) :
      GL (Fin 3) K) = diagHom 3 K (fun i => d i ^ u) := by
    rw [show (primeFormFieldSU h hC φ (omcpu_EtoSU h hm x) : GL (Fin 3) K) =
      glAut φ (diagHom 3 K d) from rfl, glAut_diagHom]
    congr 1
    funext i
    exact hu (d i) (hxr i)
  have hfield_mem := (primeFormFieldSU h hC φ (omcpu_EtoSU h hm x)).2
  let X : gramSU h (omcpu_G K) :=
    ⟨(A : GL (Fin 3) K) * diagHom 3 K (fun i => d i ^ u) * (A : GL (Fin 3) K)⁻¹,
      conj_mem_gramSU h _ A.2 (by rw [← hfield]; exact hfield_mem)⟩
  have hL : (primeFormConjHom h (omcpu_G K) A * primeFormFieldHom h hC φ)
      ((omcpu_EtoSU h hm x : gramSU h (omcpu_G K)) : primeFormP h (omcpu_G K)) =
      (X : primeFormP h (omcpu_G K)) := by
    change primeFormConjHom h (omcpu_G K) A
      (primeFormFieldAut h hC φ
        ((omcpu_EtoSU h hm x : gramSU h (omcpu_G K)) : primeFormP h (omcpu_G K))) =
      (X : primeFormP h (omcpu_G K))
    rw [primeFormFieldAut_mk, primeFormConjHom_mk]
    congr 1
    apply Subtype.ext
    rw [Subgroup.coe_mk, hfield]
  have hmono : X = omcpu_EtoSU h hm (omcpu_step h hm ρ.symm u x) := by
    apply Subtype.ext
    apply Units.ext
    calc (((A : GL (Fin 3) K) * diagHom 3 K (fun i => d i ^ u) * (A : GL (Fin 3) K)⁻¹ :
          GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)
        = ((A : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
            Matrix.diagonal (fun i => ((d i ^ u : Kˣ) : K)) *
            ((A⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
          rw [Units.val_mul, Units.val_mul, coe_diagHom]
      _ = Matrix.diagonal (fun i => ((d (ρ.symm i) ^ u : Kˣ) : K)) :=
          GH74.KGroups.L3Eps.conj_diag_of_perm (A : GL (Fin 3) K) ρ hρ
            (fun i => ((d i ^ u : Kˣ) : K))
      _ = (((omcpu_EtoSU h hm (omcpu_step h hm ρ.symm u x) : gramSU h (omcpu_G K)) :
            GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
          show Matrix.diagonal (fun i => ((d (ρ.symm i) ^ u : Kˣ) : K)) =
            ((diagHom 3 K (omcpl_permPow ρ.symm u d) : GL (Fin 3) K) :
              Matrix (Fin 3) (Fin 3) K)
          rw [coe_diagHom]
          rfl
  rw [hL, hmono]

private theorem omcpu_lift_pow_r {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K)
    {m r : ℕ} (hm : m ∣ p ^ f + 1) (hm3 : Nat.Coprime m 3)
    {x : omcpu_E (rootsOfUnity m K)}
    (htr : (((QuotientGroup.mk' (omcpu_Z h)).comp (omcpu_EtoSU h hm)) x) ^ r = 1) :
    ∀ i, x.1 i ^ r = 1 := by
  have hg : (omcpu_EtoSU h hm x) ^ r ∈ omcpu_Z h := by
    have h1 : (QuotientGroup.mk' (omcpu_Z h)) ((omcpu_EtoSU h hm x) ^ r) = 1 := by
      rw [map_pow]
      exact htr
    rw [QuotientGroup.mk'_apply] at h1
    rwa [QuotientGroup.eq_one_iff] at h1
  obtain ⟨c, hcnorm, hc3, hcmat⟩ := mem_normOneScalars.mp hg
  have hd : (diagHom 3 K (fun i => x.1 i ^ r) : GL (Fin 3) K) =
      GeneralLinearGroup.scalar (Fin 3) c := by
    have h1 : (((omcpu_EtoSU h hm x : gramSU h (omcpu_G K)) : GL (Fin 3) K) ^ r) =
        GeneralLinearGroup.scalar (Fin 3) c := by
      rw [← Subgroup.coe_pow]
      exact hcmat
    rw [show ((omcpu_EtoSU h hm x : gramSU h (omcpu_G K)) : GL (Fin 3) K) =
      diagHom 3 K x.1 from rfl, ← map_pow] at h1
    exact h1
  have hmat : Matrix.diagonal (fun i => ((x.1 i ^ r : Kˣ) : K)) =
      Matrix.diagonal (fun _ => (c : K)) := by
    have := congrArg (fun g : GL (Fin 3) K => (g : Matrix (Fin 3) (Fin 3) K)) hd
    simpa [coe_diagHom, GeneralLinearGroup.coe_scalar] using this
  have hpoint : ∀ i, x.1 i ^ r = c := by
    intro i
    apply Units.ext
    have := congrFun (congrFun hmat i) i
    simpa using this
  have hcT : c ∈ rootsOfUnity m K := by
    have hT : x.1 0 ^ r ∈ rootsOfUnity m K :=
      Subgroup.pow_mem (rootsOfUnity m K) ((omcpu_mem_E.mp x.2).1 0) r
    rw [← hpoint 0]
    exact hT
  have hcm : c ^ m = 1 := (mem_rootsOfUnity m c).mp hcT
  have hc1 : c = 1 := by
    have h1 : orderOf c ∣ m := orderOf_dvd_of_pow_eq_one hcm
    have h2 : orderOf c ∣ 3 := orderOf_dvd_of_pow_eq_one hc3
    have h3 : orderOf c ∣ 1 := by
      have hg' := Nat.dvd_gcd h1 h2
      rwa [hm3.gcd_eq_one] at hg'
    exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp h3)
  intro i
  rw [hpoint i, hc1]

private theorem omcpu_permPow_pow_r {M : Type*} [CommMonoid M] {r : ℕ}
    (w : Equiv.Perm (Fin 3)) (u : ℕ) {v : Fin 3 → M} (hv : ∀ i, v i ^ r = 1) (i : Fin 3) :
    (omcpl_permPow w u v) i ^ r = 1 := by
  rw [show omcpl_permPow w u v i = v (w i) ^ u from rfl, ← pow_mul, mul_comm, pow_mul,
    hv, one_pow]

private theorem omcpu_psu3 {p f : ℕ} {K : Type} [Field K] [Finite K] (h : UnitaryFieldData p f K)
    {r : ℕ} [Fact r.Prime] (hr5 : 5 ≤ r) (hrq : r ∣ p ^ f + 1) :
    ∃ S₀ : Subgroup (primeFormP h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)),
      Nat.card S₀ = r ^ (Nat.card (primeFormP h ((1 : GL (Fin 3) K) :
        Matrix (Fin 3) (Fin 3) K))).factorization r ∧
      ∀ b : MulAut (primeFormP h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)),
        (∀ s ∈ S₀, b s ∈ S₀) → ∀ t ∈ S₀, t ^ r = 1 → (b ^ (6 * (r - 1))) t = t := by
  classical
  have hr : r.Prime := Fact.out
  let hC : IsPrimeFormGram (1 : GL (Fin 3) K) := omcpu_isPrimeFormGram_one
  have hm : r ^ (p ^ f + 1).factorization r ∣ p ^ f + 1 := omcpu_hra hr hrq
  have hm3 : Nat.Coprime (r ^ (p ^ f + 1).factorization r) 3 := by
    have hr3 : ¬ r ∣ 3 := by
      intro hd
      have : r = 3 := (Nat.prime_dvd_prime_iff_eq hr Nat.prime_three).mp hd
      omega
    exact Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd hr).mpr hr3)
  refine ⟨omcpu_S₀ h hm, omcpu_card_S₀_eq h hr hr5 hrq, ?_⟩
  intro b hb t ht htr
  have hn3 : 3 ≤ (3 : ℕ) := le_rfl
  have hq : ¬((3 : ℕ) = 3 ∧ p ^ f = 2) := by
    rintro ⟨-, h2⟩
    have h3 : r ∣ 3 := by
      rw [h2] at hrq
      simpa using hrq
    have : r = 3 := (Nat.prime_dvd_prime_iff_eq hr Nat.prime_three).mp h3
    omega
  obtain ⟨⟨A, φ⟩, hb_eq⟩ := primeFormPsi_surjective h hC hn3 hq b
  have hb' : b = primeFormConjHom h (omcpu_G K) A * primeFormFieldHom h hC φ := by
    rw [← hb_eq, primeFormPsi_apply]
    rfl
  obtain ⟨u, hu_cop, hpow⟩ := omcpl_exists_pow_of_ringEquiv φ hr
  have hu : ∀ x : Kˣ, x ^ r = 1 → Units.map (φ : K →* K) x = x ^ u :=
    fun x hx => Units.ext (hpow x hx)
  have hfm : r ∣ r ^ (p ^ f + 1).factorization r := by
    have ha1 : 1 ≤ (p ^ f + 1).factorization r :=
      (hr.dvd_iff_one_le_factorization (by positivity)).mp hrq
    exact dvd_pow_self r (by omega)
  have hA : ∀ s ∈ omcpu_S₀ h hm,
      (primeFormConjHom h (omcpu_G K) A * primeFormFieldHom h hC φ) s ∈ omcpu_S₀ h hm := by
    intro s hs
    rw [← hb']
    exact hb s hs
  obtain ⟨ρ, hρ⟩ := omcpu_A_monomial h hr hr5 hm hfm hrq hC A φ hA
  obtain ⟨x, rfl⟩ := ht
  have hxr : ∀ i, x.1 i ^ r = 1 := omcpu_lift_pow_r h hm hm3 htr
  have hpow_r : ∀ k i, (((omcpu_step h hm ρ.symm u)^[k] x).1 i) ^ r = 1 := by
    intro k
    induction k with
    | zero => exact hxr
    | succ k ih =>
      intro i
      rw [Function.iterate_succ_apply']
      exact omcpu_permPow_pow_r ρ.symm u ih i
  have hiter : ∀ k, ((primeFormConjHom h (omcpu_G K) A * primeFormFieldHom h hC φ)^[k])
      (((QuotientGroup.mk' (omcpu_Z h)).comp (omcpu_EtoSU h hm)) x) =
      ((QuotientGroup.mk' (omcpu_Z h)).comp (omcpu_EtoSU h hm))
        ((omcpu_step h hm ρ.symm u)^[k] x) := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih =>
      rw [Function.iterate_succ_apply', ih, Function.iterate_succ_apply']
      simpa only [MonoidHom.comp_apply, QuotientGroup.mk'_apply] using
        omcpu_B_step h hm hC A φ hu hρ ((omcpu_step h hm ρ.symm u)^[k] x) (hpow_r k)
  have hstep_fun : ∀ k, (((omcpu_step h hm ρ.symm u)^[k] x).1) =
      (omcpl_permPow ρ.symm u)^[k] x.1 := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
      show omcpl_permPow ρ.symm u (((omcpu_step h hm ρ.symm u)^[k] x).1) =
        omcpl_permPow ρ.symm u ((omcpl_permPow ρ.symm u)^[k] x.1)
      rw [ih]
  have hN : ((omcpu_step h hm ρ.symm u)^[6 * (r - 1)] x) = x := by
    apply Subtype.ext
    rw [hstep_fun]
    exact omcpl_permPow_iterate_eq_self hr ρ.symm hu_cop hxr
  have hBiter : ∀ k, ((primeFormConjHom h (omcpu_G K) A * primeFormFieldHom h hC φ) ^ k)
      (((QuotientGroup.mk' (omcpu_Z h)).comp (omcpu_EtoSU h hm)) x) =
      ((primeFormConjHom h (omcpu_G K) A * primeFormFieldHom h hC φ)^[k])
      (((QuotientGroup.mk' (omcpu_Z h)).comp (omcpu_EtoSU h hm)) x) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ', MulAut.mul_apply, ih, Function.iterate_succ_apply']
  rw [hb', hBiter (6 * (r - 1)), hiter (6 * (r - 1)), hN]

end

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher in
theorem psu3_torus_leaf {p f : ℕ} {K : Type} [Field K] [Finite K] (h : UnitaryFieldData p f K)
    {r : ℕ} [Fact r.Prime] (hr5 : 5 ≤ r) (hrq : r ∣ p ^ f + 1) :
    ∃ S₀ : Subgroup (primeFormP h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)),
      Nat.card S₀ = r ^ (Nat.card (primeFormP h ((1 : GL (Fin 3) K) :
        Matrix (Fin 3) (Fin 3) K))).factorization r ∧
      ∀ b : MulAut (primeFormP h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)),
        (∀ s ∈ S₀, b s ∈ S₀) → ∀ t ∈ S₀, t ^ r = 1 → (b ^ (6 * (r - 1))) t = t := by
  exact omcpu_psu3 h hr5 hrq

private theorem omcoma_center_eq_bot_of_simple {X : Type*} [Group X] [IsSimpleGroup X]
    {p k : ℕ} (hp : p.Prime) (hk : 1 ≤ k) (hfac : (Nat.card X).factorization p = 3 * k) :
    Subgroup.center X = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center X) with h | h
  · exact h
  · exfalso
    have : IsMulCommutative X := IsMulCommutative.of_comm (fun a b => by
      have ha : a ∈ Subgroup.center X := by rw [h]; exact Subgroup.mem_top a
      exact (Subgroup.mem_center_iff.mp ha b).symm)
    have hpcard : (Nat.card X).Prime := Group.is_simple_iff_prime_card.mp inferInstance
    have hpos : (Nat.card X).factorization p ≠ 0 := by rw [hfac]; omega
    have hdvd : p ∣ Nat.card X := Nat.dvd_of_factorization_pos hpos
    have hpeq : p = Nat.card X := by
      rcases (Nat.dvd_prime hpcard).mp hdvd with h1 | h1
      · exact absurd h1 hp.ne_one
      · exact h1
    have h1 : (Nat.card X).factorization p = 1 := by
      rw [← hpeq]; exact hp.factorization_self
    omega

private theorem omcoma_coprime_six_mul_pred {r : ℕ} (hr : r.Prime) (h5 : 5 ≤ r) :
    Nat.Coprime r (6 * (r - 1)) := by
  have h6 : Nat.Coprime r 6 := by
    rw [hr.coprime_iff_not_dvd]
    intro h
    have h23 : (6 : ℕ) = 2 * 3 := by norm_num
    rw [h23] at h
    rcases hr.dvd_mul.mp h with h' | h'
    · exact absurd ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).1 h') (by omega)
    · exact absurd ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_three).1 h') (by omega)
  have hrr1 : Nat.Coprime r (r - 1) := by
    rw [hr.coprime_iff_not_dvd]
    exact Nat.not_dvd_of_pos_of_lt (Nat.sub_pos_of_lt hr.one_lt) (Nat.sub_one_lt hr.ne_zero)
  exact h6.mul_right hrr1

private theorem omcoma_transport_leaf {X Y : Type*} [Group X] [Group Y]
    (e : X ≃* Y) {r N : ℕ} (S : Subgroup Y)
    (hS : Nat.card S = r ^ (Nat.card Y).factorization r)
    (hleaf : ∀ b : MulAut Y, (∀ s ∈ S, b s ∈ S) → ∀ t ∈ S, t ^ r = 1 → (b ^ N) t = t) :
    ∃ S' : Subgroup X, Nat.card S' = r ^ (Nat.card X).factorization r ∧
      ∀ b : MulAut X, (∀ s ∈ S', b s ∈ S') → ∀ t ∈ S', t ^ r = 1 → (b ^ N) t = t := by
  refine ⟨S.map e.symm.toMonoidHom, ?_, ?_⟩
  · rw [Subgroup.card_map_of_injective e.symm.injective, hS, ← Nat.card_congr e.toEquiv]
  · intro b hnorm t ht htr
    have hmemS : ∀ x : X, x ∈ S.map e.symm.toMonoidHom → e x ∈ S := by
      intro x hx
      obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hx
      rw [← hyx]
      change e (e.symm y) ∈ S
      rw [e.apply_symm_apply]
      exact hy
    let b' : MulAut Y := MulAut.congr e b
    have hnorm' : ∀ s ∈ S, b' s ∈ S := by
      intro s hs
      change e (b (e.symm s)) ∈ S
      exact hmemS _ (hnorm _ (Subgroup.mem_map_of_mem e.symm.toMonoidHom hs))
    have hfix := hleaf b' hnorm' (e t) (hmemS t ht) (by rw [← map_pow, htr, map_one])
    have hpow : b' ^ N = MulAut.congr e (b ^ N) := by
      change (MulAut.congr e b) ^ N = (MulAut.congr e) (b ^ N)
      rw [map_pow]
    have hthis : e ((b ^ N) t) = e t := by
      have h2 : (MulAut.congr e (b ^ N)) (e t) = e t := by rw [← hpow]; exact hfix
      simpa using h2
    exact e.injective hthis

open CFSG.ComponentClassification.OuterAutomorphisms (inner)

theorem omega_inner_central_psl_three_two_pow {X : Type} [Group X] [Finite X] {n r : ℕ}
    (hX : CFSG.Blueprint.LieModel X .PSL 3 2 n) (hr : r.Prime) (h5 : 5 ≤ r)
    (hdvd : r ∣ 2 ^ n - 1) (R : Subgroup (MulAut X)) (hR : IsPGroup r ↥R)
    (hsyl : Nat.card ↥(R ⊓ inner X) = r ^ (Nat.card X).factorization r) :
    ∀ a ∈ R ⊓ inner X, a ^ r = 1 → ∀ b ∈ R, a * b = b * a := by
  classical
  have : Fact r.Prime := ⟨hr⟩
  obtain ⟨⟨hp, hf, -⟩, K, hfield, hfinite, hK, ⟨e⟩⟩ :=
    hX.statedClassicalModel_of_ne_zero (by norm_num)
  let : Field K := hfield
  let : Finite K := hfinite
  have : IsSimpleGroup X :=
    CFSG.Blueprint.LieModel.isSimpleGroup_of_mem_classicalTags (by decide) hX
  have hcen : Subgroup.center X = ⊥ :=
    omcoma_center_eq_bot_of_simple (p := 2) Nat.prime_two hf
      (CFSG.Blueprint.LieModel.factorization_card_psl3 hX)
  have hrq : r ∣ Nat.card K - 1 := by rw [hK]; exact hdvd
  have e' : X ≃* LinearFlag.projectiveSL 3 K :=
    (e.trans (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 3 K).symm).trans
      (CFSG.LocalAnalysis.ComponentInitial.LinearCover.projectiveSpecialLinearEquivProjectiveSL 3 K)
  obtain ⟨S₀, hS₀card, hS₀leaf⟩ := psl3_torus_leaf (K := K) h5 hrq
  obtain ⟨S₀', hS₀'card, hS₀'act⟩ := omcoma_transport_leaf e' S₀ hS₀card hS₀leaf
  exact omega_inner_central_of_normalizer_pow hcen S₀' hS₀'card (6 * (r - 1))
    (omcoma_coprime_six_mul_pred hr h5) hS₀'act R hR hsyl

theorem omega_inner_central_psu_three_two_pow {X : Type} [Group X] [Finite X] {n r : ℕ}
    (hX : CFSG.Blueprint.LieModel X .PSU 3 2 n) (hr : r.Prime) (h5 : 5 ≤ r)
    (hdvd : r ∣ 2 ^ n + 1) (R : Subgroup (MulAut X)) (hR : IsPGroup r ↥R)
    (hsyl : Nat.card ↥(R ⊓ inner X) = r ^ (Nat.card X).factorization r) :
    ∀ a ∈ R ⊓ inner X, a ^ r = 1 → ∀ b ∈ R, a * b = b * a := by
  classical
  have : Fact r.Prime := ⟨hr⟩
  obtain ⟨⟨hp, hf, -, hne⟩, K, hfield, hfinite, hK, ⟨e⟩⟩ :=
    hX.statedClassicalModel_of_ne_zero (by norm_num)
  let : Field K := hfield
  let : Finite K := hfinite
  have : IsSimpleGroup X :=
    CFSG.Blueprint.LieModel.isSimpleGroup_of_mem_classicalTags (by decide) hX
  have hcen : Subgroup.center X = ⊥ :=
    omcoma_center_eq_bot_of_simple (p := 2) Nat.prime_two hf
      (CFSG.Blueprint.LieModel.factorization_card_psu3 hX)
  have hU : UnitaryFieldData 2 n K :=
    ⟨Nat.prime_two, hf, by rw [hK, ← pow_mul, mul_comm]⟩
  have e' : X ≃* CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.primeFormP hU
      ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) :=
    (e.trans (CFSG.ClassicalGroups.UnitaryFlag.unitaryPSUEquiv hU (n := 3)
      (by norm_num)).symm).trans (Classical.choice
        (CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.nonempty_primeFormP_mulEquiv hU
          (CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.isPrimeFormGram_one
            (n := 3) (K := K)))).symm
  obtain ⟨S₀, hS₀card, hS₀leaf⟩ := psu3_torus_leaf hU h5 hdvd
  obtain ⟨S₀', hS₀'card, hS₀'act⟩ := omcoma_transport_leaf e' S₀ hS₀card hS₀leaf
  exact omega_inner_central_of_normalizer_pow hcen S₀' hS₀'card (6 * (r - 1))
    (omcoma_coprime_six_mul_pred hr h5) hS₀'act R hR hsyl

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
