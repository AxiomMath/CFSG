module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_3.ExcDim
public import CFSG.Quasithin.MS93.S32U
public import CFSG.Quasithin.Background.SmithB42L2L32
public import CFSG.LocalAnalysis.ComponentInitial.DiagonalSemilinear
public import CFSG.LocalAnalysis.UniquenessCase.UC22K147L2Fac
public import CFSG.Quasithin.Background.SmithB45L2Class

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_3

open CFSG.Quasithin CFSG.Open Subgroup
open CFSG.QuasithinUnique.Setup.SL2Modules CFSG.QuasithinUnique.Setup.Layer
open scoped MatrixGroups

private theorem exists_conjEndRing {k : Type} [Field k] {G : Type} [Group G]
    {W : Type} [AddCommGroup W] [Module k W] (ρ : Representation k G W)
    (u : (Module.End k W)ˣ)
    (hnorm : u ∈ Subgroup.normalizer (ρ.toHomUnits.range : Set (Module.End k W)ˣ))
    (δ : EndRing ρ) :
    ∃ y : EndRing ρ, epsHom ρ y = u.val * epsHom ρ δ * (u⁻¹).val := by
  have hz : ∀ (g : G) (v : W),
      (u.val * epsHom ρ δ * (u⁻¹).val) ((ρ g) v) =
        (ρ g) ((u.val * epsHom ρ δ * (u⁻¹).val) v) := by
    intro g v
    have hg : u⁻¹ * ρ.toHomUnits g * u ∈ ρ.toHomUnits.range :=
      (Subgroup.mem_normalizer_iff''.mp hnorm (ρ.toHomUnits g)).mp ⟨g, rfl⟩
    obtain ⟨g', hg'⟩ := hg
    have hρU_val : ∀ x : G, (ρ.toHomUnits x).val = ρ x := fun x =>
      MonoidHom.coe_toHomUnits ρ x
    have e1' : u⁻¹ * ρ.toHomUnits g = ρ.toHomUnits g' * u⁻¹ := by
      rw [show u⁻¹ * ρ.toHomUnits g = (u⁻¹ * ρ.toHomUnits g * u) * u⁻¹ by group,
        ← hg']
    have e2' : u * ρ.toHomUnits g' = ρ.toHomUnits g * u := by
      rw [hg']
      group
    have h1 : (u⁻¹).val ((ρ g) v) = (ρ.toHomUnits g').val ((u⁻¹).val v) := by
      have h := congrArg (fun x : (Module.End k W)ˣ => x.val v) e1'
      simp only [Units.val_mul, Module.End.mul_apply] at h
      rw [hρU_val g] at h
      exact h
    have h2 : epsHom ρ δ ((ρ.toHomUnits g').val ((u⁻¹).val v)) =
        (ρ.toHomUnits g').val (epsHom ρ δ ((u⁻¹).val v)) := by
      rw [hρU_val g']
      exact epsHom_commutes ρ δ g' ((u⁻¹).val v)
    have h3 : u.val ((ρ.toHomUnits g').val (epsHom ρ δ ((u⁻¹).val v))) =
        (ρ g) (u.val (epsHom ρ δ ((u⁻¹).val v))) := by
      have h := congrArg (fun x : (Module.End k W)ˣ =>
        x.val (epsHom ρ δ ((u⁻¹).val v))) e2'
      simp only [Units.val_mul, Module.End.mul_apply] at h
      rw [hρU_val g', hρU_val g] at h
      exact h
    simp only [Module.End.mul_apply]
    rw [h1, h2, h3]
  obtain ⟨y, hy⟩ := (mem_endRing_iff ρ (u.val * epsHom ρ δ * (u⁻¹).val)).mpr hz
  exact ⟨y, LinearMap.ext fun w => congrFun hy w⟩

private theorem ringEquiv_eq_of_card_four {D : Type} [Field D] [Finite D]
    (h4 : Nat.card D = 4) {τ σ : D ≃+* D} (hτ : τ ≠ 1) (hσ : σ ≠ 1) : τ = σ :=
  ((Nat.card_eq_two_iff' (1 : D ≃+* D)).mp
    (CFSG.LocalAnalysis.ComponentInitial.card_ringAut_and_isCyclic (n := 2) Nat.prime_two D
      (by rw [h4]; norm_num)).1).unique hτ hσ

private theorem unitsPsi_mem_normalizer {F : Type} [Field F] [Fintype F] [CharP F 2]
    {I : Type} [CommGroup I] [Finite I] {W : Type} [AddCommGroup W] [Module (ZMod 2) W]
    [Finite W] (θ : I ≃* Multiplicative W) {X L : Subgroup (MulAut I)} (hLX : L ≤ X)
    (hLn : (L.subgroupOf X).Normal) (φ : ↥L ≃* SL(2, F)) {a : MulAut I} (haX : a ∈ X) :
    B42L2.unitsPsi θ a ∈ Subgroup.normalizer
      ((B45L2.repOf θ φ).toHomUnits.range : Set (Module.End (ZMod 2) W)ˣ) := by
  have hunit : (CFSG.QuasithinUnique.Setup.Lift.unitsEquiv (ZMod 2) W) (B42L2.unitsPsi θ a) =
      binPsi θ a := by
    simp [B42L2.unitsPsi]
  have hnormL : a ∈ Subgroup.normalizer (L : Set (MulAut I)) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hLX).1 hLn haX
  have hbinNorm : binPsi θ a ∈ Subgroup.normalizer
      ((L.map (binPsi θ).toMonoidHom : Subgroup (W ≃ₗ[ZMod 2] W)) :
        Set (W ≃ₗ[ZMod 2] W)) := by
    rw [← Subgroup.map_equiv_normalizer_eq L (binPsi θ)]
    exact Subgroup.mem_map_of_mem _ hnormL
  have hu : B42L2.unitsPsi θ a ∈ CFSG.QuasithinUnique.Setup.Lift.toUnits
      (Subgroup.normalizer (L.map (binPsi θ).toMonoidHom : Set (W ≃ₗ[ZMod 2] W))) := by
    rw [CFSG.QuasithinUnique.Setup.Lift.mem_toUnits, hunit]
    exact hbinNorm
  rw [B45L2.repOf_range]
  exact CFSG.QuasithinUnique.Setup.Lift.toUnits_normalizer le_rfl hu

private theorem unitsPsi_mem_range_iff {F : Type} [Field F] {I : Type} [CommGroup I]
    {W : Type} [AddCommGroup W] [Module (ZMod 2) W] (θ : I ≃* Multiplicative W)
    {L : Subgroup (MulAut I)} (φ : ↥L ≃* SL(2, F)) {a : MulAut I} :
    B42L2.unitsPsi θ a ∈ (B45L2.repOf θ φ).toHomUnits.range ↔ a ∈ L := by
  have hunit : (CFSG.QuasithinUnique.Setup.Lift.unitsEquiv (ZMod 2) W) (B42L2.unitsPsi θ a) =
      binPsi θ a := by
    simp [B42L2.unitsPsi]
  rw [B45L2.repOf_range]
  constructor
  · intro h
    have h' : binPsi θ a ∈ L.map (binPsi θ).toMonoidHom := by
      rw [← hunit]
      exact (CFSG.QuasithinUnique.Setup.Lift.mem_toUnits).mp h
    obtain ⟨l, hl, hle⟩ := Subgroup.mem_map.mp h'
    exact (binPsi θ).injective hle ▸ hl
  · intro h
    refine (CFSG.QuasithinUnique.Setup.Lift.mem_toUnits).mpr ?_
    rw [hunit]
    exact Subgroup.mem_map_of_mem _ h

private theorem exists_not_commute_of_mem_normalizer {F : Type} [Field F] [Fintype F] [CharP F 2]
    (hF : Fintype.card F = 2 ^ 6) {I : Type} [CommGroup I] [Finite I]
    {W : Type} [AddCommGroup W] [Module (ZMod 2) W] [Finite W]
    (θ : I ≃* Multiplicative W) {X L : Subgroup (MulAut I)} (hLX : L ≤ X)
    (hLn : (L.subgroupOf X).Normal) (φ : ↥L ≃* SL(2, F))
    [Fact (B45L2.repOf θ φ).IsIrreducible]
    (hD : SixtyFourDescent (B45L2.repOf θ φ)) {a : MulAut I} (haX : a ∈ X)
    (ha2 : a * a = 1) (haL : a ∉ L) :
    ∃ δ : EndRing (B45L2.repOf θ φ),
      (B42L2.unitsPsi θ a).val * epsHom (B45L2.repOf θ φ) δ ≠
        epsHom (B45L2.repOf θ φ) δ * (B42L2.unitsPsi θ a).val := by
  classical
  let ρ : Representation (ZMod 2) SL(2, F) W := B45L2.repOf θ φ
  haveI : Fact ρ.IsIrreducible := by
    dsimp [ρ]
    infer_instance
  have hD' : SixtyFourDescent ρ := hD
  have hρinj : Function.Injective ρ := B45L2.repOf_injective θ φ
  have hρUinj : Function.Injective ρ.toHomUnits := fun g h e =>
    hρinj (by simpa using congrArg Units.val e)
  have hWnt : Nontrivial W := (isIrreducible_iff ρ).mp Fact.out |>.1
  let u : (Module.End (ZMod 2) W)ˣ := B42L2.unitsPsi θ a
  have hu2 : u * u = 1 := by
    dsimp [u]
    rw [← map_mul, ha2, map_one]
  have huNorm : u ∈ Subgroup.normalizer (ρ.toHomUnits.range :
      Set (Module.End (ZMod 2) W)ˣ) := by
    dsimp [u, ρ]
    exact unitsPsi_mem_normalizer θ hLX hLn φ haX
  have huNotL : u ∉ ρ.toHomUnits.range := by
    change B42L2.unitsPsi θ a ∉ (B45L2.repOf θ φ).toHomUnits.range
    rw [unitsPsi_mem_range_iff]
    exact haL
  haveI : CFSG.IsElementaryAbelian 2 (Subgroup.zpowers u) :=
    CFSG.IsElementaryAbelian.zpowers_of_pow_eq_one (p := 2) hu2
  have hcard : Nat.card F = 2 ^ 6 := by
    rw [Nat.card_eq_fintype_card]
    exact hF
  obtain ⟨s, hs1, hns, -, -, a', ha'A, ha'L, x, hxconj⟩ :=
    outer_data (n := 6) (by omega) hcard ρ Fact.out hρUinj (Subgroup.zpowers u)
      (Subgroup.zpowers_le.mpr huNorm) (fun h => huNotL (h (Subgroup.mem_zpowers u)))
  have hs3 : s = 3 := by omega
  have ha'2 : a' * a' = 1 := by
    rcases CFSG.LocalAnalysis.UniquenessCase.UC22.K147L2Fac.eq_one_or_eq_of_mem_zpowers
      hu2 ha'A with h | h
    · exfalso
      exact ha'L (h ▸ Subgroup.one_mem _)
    · rw [h]
      exact hu2
  have ha'u : a' = u := by
    rcases CFSG.LocalAnalysis.UniquenessCase.UC22.K147L2Fac.eq_one_or_eq_of_mem_zpowers
      hu2 ha'A with h | h
    · exfalso
      exact ha'L (h ▸ Subgroup.one_mem _)
    · exact h
  by_contra hcon
  push Not at hcon
  let a'' : (Module.End (ZMod 2) W)ˣ := (ρ.toHomUnits x)⁻¹ * a' * ρ.toHomUnits x
  have ha''2 : a'' * a'' = 1 := by
    dsimp [a'']
    calc ((ρ.toHomUnits x)⁻¹ * a' * ρ.toHomUnits x) *
          ((ρ.toHomUnits x)⁻¹ * a' * ρ.toHomUnits x)
        = (ρ.toHomUnits x)⁻¹ * (a' * a') * ρ.toHomUnits x := by group
      _ = 1 := by rw [ha'2]; group
  have hcomm'' : ∀ δ : EndRing ρ, a''.val * epsHom ρ δ = epsHom ρ δ * a''.val := by
    intro δ
    have h1 : ∀ g : SL(2, F), Commute (ρ.toHomUnits g).val (epsHom ρ δ) := by
      intro g
      apply LinearMap.ext
      intro v
      exact (epsHom_commutes ρ δ g v).symm
    have h3 : Commute ((ρ.toHomUnits x)⁻¹).val (epsHom ρ δ) := by
      rw [← map_inv ρ.toHomUnits x]
      exact h1 x⁻¹
    have h2 : Commute a'.val (epsHom ρ δ) := by
      rw [ha'u]
      exact hcon δ
    have h4 := (h3.mul_left h2).mul_left (h1 x)
    show ((ρ.toHomUnits x)⁻¹ * a' * ρ.toHomUnits x).val * _ =
      _ * ((ρ.toHomUnits x)⁻¹ * a' * ρ.toHomUnits x).val
    rw [Units.val_mul, Units.val_mul]
    exact h4
  let aD : Module.End (EndRing ρ) W := linD ρ a''.val hcomm''
  have haD2 : aD * aD = 1 := by
    apply LinearMap.ext
    intro w
    have h := congrArg (fun z : (Module.End (ZMod 2) W)ˣ => z.val w) ha''2
    simp only [Units.val_mul, Module.End.mul_apply, Units.val_one,
      Module.End.one_apply] at h
    exact h
  have hconjD : ∀ g : SL(2, F), aD * repD ρ g = repD ρ (fieldAut F s g) * aD := by
    intro g
    apply LinearMap.ext
    intro w
    have h := hxconj g
    have h' : a'' * ρ.toHomUnits g = ρ.toHomUnits (fieldAut F s g) * a'' := by
      calc a'' * ρ.toHomUnits g = (a'' * ρ.toHomUnits g * a''⁻¹) * a'' := by group
        _ = ρ.toHomUnits (fieldAut F s g) * a'' := by rw [h]
    have h2 := congrArg (fun z : (Module.End (ZMod 2) W)ˣ => z.val w) h'
    simp only [Units.val_mul, Module.End.mul_apply] at h2
    exact h2
  obtain ⟨hDcard, hDdata⟩ := hD'
  haveI : Finite (EndRing ρ) := finite_endRing ρ
  haveI : Module.Finite (EndRing ρ) W := Module.Finite.of_finite
  let b : Module.Basis (Fin (Module.finrank (EndRing ρ) W)) (EndRing ρ) W :=
    Module.finBasis (EndRing ρ) W
  obtain ⟨E, hE, hEfin, hEchar, ιF, ιD, J, hJ, hΦ⟩ := hDdata b
  letI : Field E := hE
  letI : Finite E := hEfin
  letI : CharP E 2 := hEchar
  letI : Algebra F E := ιF.toAlgebra
  obtain ⟨Φ⟩ := hΦ
  have hF2 : Fintype.card F = 2 ^ (2 * 3) := by
    rw [hF]
  have hJ2 : ∀ i ∈ J, i < 2 * 3 := by
    rcases hJ with hJ | hJ <;> rw [hJ] <;> decide
  have hconjD3 : ∀ g : SL(2, F), aD * repD ρ g = repD ρ (fieldAut F 3 g) * aD := by
    intro g
    rw [← hs3]
    exact hconjD g
  have hcount := outer_involution_count (ρ := ρ) (s := 3) (b := b) (E := E)
    (ιD := ιD) (J := J) (Φ := Φ) (by norm_num) hF2 hJ2 aD haD2 hconjD3
  obtain ⟨hJs, -⟩ := hcount
  have hnot1 : ({0, 2, 4} : Finset ℕ).image (shiftExp 3) ≠ ({0, 2, 4} : Finset ℕ) := by
    decide
  have hnot2 : ({1, 3, 5} : Finset ℕ).image (shiftExp 3) ≠ ({1, 3, 5} : Finset ℕ) := by
    decide
  rcases hJ with hJ | hJ
  · rw [hJ] at hJs
    exact hnot1 hJs
  · rw [hJ] at hJs
    exact hnot2 hJs

private theorem mul_mem_of_mem_not_mem {F : Type} [Field F] [Fintype F] [CharP F 2]
    (hF : Fintype.card F = 2 ^ 6) {I : Type} [CommGroup I] [Finite I]
    {W : Type} [AddCommGroup W] [Module (ZMod 2) W] [Finite W]
    (θ : I ≃* Multiplicative W) {X L : Subgroup (MulAut I)} (hLX : L ≤ X)
    (hLn : (L.subgroupOf X).Normal) (φ : ↥L ≃* SL(2, F))
    [Fact (B45L2.repOf θ φ).IsIrreducible]
    (hD : SixtyFourDescent (B45L2.repOf θ φ)) {A : Subgroup (MulAut I)} (hAX : A ≤ X)
    (hAea : IsElemAbelian2 A) {a c : MulAut I} (haA : a ∈ A) (hcA : c ∈ A)
    (haL : a ∉ L) (hcL : c ∉ L) : a * c ∈ L := by
  classical
  by_contra hacL
  let ρ : Representation (ZMod 2) SL(2, F) W := B45L2.repOf θ φ
  haveI : Fact ρ.IsIrreducible := by
    dsimp [ρ]
    infer_instance
  have hD' : SixtyFourDescent ρ := hD
  have hWnt : Nontrivial W := (isIrreducible_iff ρ).mp Fact.out |>.1
  haveI : Finite (EndRing ρ) := finite_endRing ρ
  have ha2 : a * a = 1 := hAea.2 a haA
  have hc2 : c * c = 1 := hAea.2 c hcA
  have hca : c * a = a * c := (hAea.1 a haA c hcA).symm
  have hacA : a * c ∈ A := A.mul_mem haA hcA
  have hac2 : a * c * (a * c) = 1 := by
    calc a * c * (a * c) = a * (c * a) * c := by group
      _ = a * (a * c) * c := by rw [hca]
      _ = a * a * (c * c) := by group
      _ = 1 := by rw [ha2, hc2, mul_one]
  obtain ⟨δa, hδa⟩ := exists_not_commute_of_mem_normalizer hF θ hLX hLn φ hD (hAX haA) ha2 haL
  obtain ⟨δc, hδc⟩ := exists_not_commute_of_mem_normalizer hF θ hLX hLn φ hD (hAX hcA) hc2 hcL
  have huNormA : B42L2.unitsPsi θ a ∈ Subgroup.normalizer (ρ.toHomUnits.range :
      Set (Module.End (ZMod 2) W)ˣ) := by
    dsimp [ρ]
    exact unitsPsi_mem_normalizer θ hLX hLn φ (hAX haA)
  have huNormC : B42L2.unitsPsi θ c ∈ Subgroup.normalizer (ρ.toHomUnits.range :
      Set (Module.End (ZMod 2) W)ˣ) := by
    dsimp [ρ]
    exact unitsPsi_mem_normalizer θ hLX hLn φ (hAX hcA)
  obtain ⟨τa, hτa⟩ := exists_conjAut (ε := epsHom ρ) (B42L2.unitsPsi θ a)
    (fun δ => exists_conjEndRing ρ (B42L2.unitsPsi θ a) huNormA δ)
  obtain ⟨τc, hτc⟩ := exists_conjAut (ε := epsHom ρ) (B42L2.unitsPsi θ c)
    (fun δ => exists_conjEndRing ρ (B42L2.unitsPsi θ c) huNormC δ)
  have hτa_ne : τa ≠ 1 := by
    intro h
    have e : (B42L2.unitsPsi θ a).val * epsHom ρ δa *
        ((B42L2.unitsPsi θ a)⁻¹).val = epsHom ρ δa := by
      simpa [h] using (hτa δa).symm
    have hinv : ((B42L2.unitsPsi θ a)⁻¹).val * (B42L2.unitsPsi θ a).val = 1 := by
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    have e2 : (B42L2.unitsPsi θ a).val * epsHom ρ δa = epsHom ρ δa * (B42L2.unitsPsi θ a).val := by
      calc (B42L2.unitsPsi θ a).val * epsHom ρ δa
          = (B42L2.unitsPsi θ a).val * epsHom ρ δa *
              (((B42L2.unitsPsi θ a)⁻¹).val * (B42L2.unitsPsi θ a).val) := by rw [hinv, mul_one]
        _ = ((B42L2.unitsPsi θ a).val * epsHom ρ δa * ((B42L2.unitsPsi θ a)⁻¹).val) *
              (B42L2.unitsPsi θ a).val := by simp only [mul_assoc]
        _ = epsHom ρ δa * (B42L2.unitsPsi θ a).val := by rw [e]
    exact hδa e2
  have hτc_ne : τc ≠ 1 := by
    intro h
    have e : (B42L2.unitsPsi θ c).val * epsHom ρ δc *
        ((B42L2.unitsPsi θ c)⁻¹).val = epsHom ρ δc := by
      simpa [h] using (hτc δc).symm
    have hinv : ((B42L2.unitsPsi θ c)⁻¹).val * (B42L2.unitsPsi θ c).val = 1 := by
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    have e2 : (B42L2.unitsPsi θ c).val * epsHom ρ δc = epsHom ρ δc * (B42L2.unitsPsi θ c).val := by
      calc (B42L2.unitsPsi θ c).val * epsHom ρ δc
          = (B42L2.unitsPsi θ c).val * epsHom ρ δc *
              (((B42L2.unitsPsi θ c)⁻¹).val * (B42L2.unitsPsi θ c).val) := by rw [hinv, mul_one]
        _ = ((B42L2.unitsPsi θ c).val * epsHom ρ δc * ((B42L2.unitsPsi θ c)⁻¹).val) *
              (B42L2.unitsPsi θ c).val := by simp only [mul_assoc]
        _ = epsHom ρ δc * (B42L2.unitsPsi θ c).val := by rw [e]
    exact hδc e2
  obtain ⟨δac, hδac⟩ :=
    exists_not_commute_of_mem_normalizer hF θ hLX hLn φ hD (hAX hacA) hac2 hacL
  have huNormAC : B42L2.unitsPsi θ (a * c) ∈ Subgroup.normalizer (ρ.toHomUnits.range :
      Set (Module.End (ZMod 2) W)ˣ) := by
    dsimp [ρ]
    exact unitsPsi_mem_normalizer θ hLX hLn φ (hAX hacA)
  obtain ⟨τac, hτac⟩ := exists_conjAut (ε := epsHom ρ) (B42L2.unitsPsi θ (a * c))
    (fun δ => exists_conjEndRing ρ (B42L2.unitsPsi θ (a * c)) huNormAC δ)
  have hτac_apply : ∀ δ, τac δ = τa (τc δ) := by
    intro δ
    apply epsHom_injective ρ
    calc epsHom ρ (τac δ)
        = (B42L2.unitsPsi θ (a * c)).val * epsHom ρ δ * ((B42L2.unitsPsi θ (a * c))⁻¹).val :=
          hτac δ
      _ = (B42L2.unitsPsi θ a).val * ((B42L2.unitsPsi θ c).val * epsHom ρ δ *
            ((B42L2.unitsPsi θ c)⁻¹).val) * ((B42L2.unitsPsi θ a)⁻¹).val := by
          rw [show B42L2.unitsPsi θ (a * c) = B42L2.unitsPsi θ a * B42L2.unitsPsi θ c
            from map_mul _ _ _]
          have hinv : ((B42L2.unitsPsi θ a * B42L2.unitsPsi θ c)⁻¹).val =
              ((B42L2.unitsPsi θ c)⁻¹).val * ((B42L2.unitsPsi θ a)⁻¹).val := by
            rw [mul_inv_rev, Units.val_mul]
          rw [hinv, Units.val_mul]
          simp only [mul_assoc]
      _ = (B42L2.unitsPsi θ a).val * epsHom ρ (τc δ) * ((B42L2.unitsPsi θ a)⁻¹).val := by
          rw [← hτc δ]
      _ = epsHom ρ (τa (τc δ)) := (hτa (τc δ)).symm
  have hτc_data : InvData (epsHom ρ) (B42L2.unitsPsi θ c) τc :=
    ⟨by rw [← map_mul, hc2, map_one], hτc⟩
  have hτac_id : τac = 1 := by
    have hτeq : τa = τc := ringEquiv_eq_of_card_four hD'.1 hτa_ne hτc_ne
    apply RingEquiv.ext
    intro δ
    rw [hτac_apply δ, hτeq]
    simpa using hτc_data.tau_tau δ
  have e : (B42L2.unitsPsi θ (a * c)).val * epsHom ρ δac * ((B42L2.unitsPsi θ (a * c))⁻¹).val =
      epsHom ρ δac := by
    simpa [hτac_id] using (hτac δac).symm
  have hinv : ((B42L2.unitsPsi θ (a * c))⁻¹).val * (B42L2.unitsPsi θ (a * c)).val = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have e2 : (B42L2.unitsPsi θ (a * c)).val * epsHom ρ δac =
      epsHom ρ δac * (B42L2.unitsPsi θ (a * c)).val := by
    calc (B42L2.unitsPsi θ (a * c)).val * epsHom ρ δac
        = (B42L2.unitsPsi θ (a * c)).val * epsHom ρ δac *
            (((B42L2.unitsPsi θ (a * c))⁻¹).val * (B42L2.unitsPsi θ (a * c)).val) := by
          rw [hinv, mul_one]
      _ = ((B42L2.unitsPsi θ (a * c)).val * epsHom ρ δac * ((B42L2.unitsPsi θ (a * c))⁻¹).val) *
            (B42L2.unitsPsi θ (a * c)).val := by simp only [mul_assoc]
      _ = epsHom ρ δac * (B42L2.unitsPsi θ (a * c)).val := by rw [e]
  exact hδac e2

private theorem fixV_inf_ne_fixV {F : Type} [Field F] [Fintype F] [CharP F 2]
    (hF : Fintype.card F = 2 ^ 6) {I : Type} [CommGroup I] [Finite I]
    (hI : ∀ w : I, w ^ 2 = 1) {W : Type} [AddCommGroup W] [Module (ZMod 2) W] [Finite W]
    (θ : I ≃* Multiplicative W) {X L : Subgroup (MulAut I)} (hLX : L ≤ X)
    (hLn : (L.subgroupOf X).Normal) (φ : ↥L ≃* SL(2, F))
    [Fact (B45L2.repOf θ φ).IsIrreducible]
    (hD : SixtyFourDescent (B45L2.repOf θ φ)) {A : Subgroup (MulAut I)} (hAX : A ≤ X)
    (hAea : IsElemAbelian2 A) (hAL : ¬ A ≤ L) :
    fixV (A ⊓ L) ≠ fixV A := by
  classical
  let ρ : Representation (ZMod 2) SL(2, F) W := B45L2.repOf θ φ
  haveI : Fact ρ.IsIrreducible := by
    dsimp [ρ]
    infer_instance
  have hD' : SixtyFourDescent ρ := hD
  have hWnt : Nontrivial W := (isIrreducible_iff ρ).mp Fact.out |>.1
  haveI : Finite (EndRing ρ) := finite_endRing ρ
  have hInt : Nontrivial I := by
    obtain ⟨w0, hw0⟩ := exists_ne (0 : W)
    refine ⟨⟨θ.symm (Multiplicative.ofAdd w0), 1, ?_⟩⟩
    intro h
    apply hw0
    have h' := congrArg θ h
    simpa using h'
  have hB2 : IsPGroup 2 ↥(A ⊓ L) := by
    intro b
    refine ⟨1, ?_⟩
    apply Subtype.ext
    have hb2 : (b : MulAut I) ^ 2 = 1 := hAea.2 b.1 b.2.1
    simpa using hb2
  have hfixB : fixV (A ⊓ L) ≠ ⊥ :=
    CFSG.Quasithin.MS93.S32.fixV_ne_bot_of_isPGroup hI hB2
  obtain ⟨v, hvB, hvne⟩ : ∃ v : I, v ∈ fixV (A ⊓ L) ∧ v ≠ 1 := by
    have hnt : Nontrivial ↥(fixV (A ⊓ L)) :=
      (Subgroup.nontrivial_iff_ne_bot _).mpr hfixB
    obtain ⟨z, hz⟩ := exists_ne (1 : ↥(fixV (A ⊓ L)))
    exact ⟨z.1, z.2, fun h => hz (Subtype.ext h)⟩
  let w : W := Multiplicative.toAdd (θ v)
  have hwne : w ≠ 0 := by
    intro h
    apply hvne
    apply θ.injective
    exact Multiplicative.toAdd.injective (by simpa [w] using h)
  have hfixD : ∀ δ : EndRing ρ, ∀ b ∈ A ⊓ L,
      binPsi θ b (epsHom ρ δ w) = epsHom ρ δ w := by
    intro δ b hb
    have hbv : b v = v := hvB b hb
    have hbw : binPsi θ b w = w := by
      simp [w, binPsi_apply, hbv]
    calc binPsi θ b (epsHom ρ δ w)
        = (B45L2.repOf θ φ (φ ⟨b, hb.2⟩)) (epsHom ρ δ w) := by
          rw [B45L2.repOf_theta]
      _ = epsHom ρ δ ((B45L2.repOf θ φ (φ ⟨b, hb.2⟩)) w) :=
          (epsHom_commutes ρ δ (φ ⟨b, hb.2⟩) w).symm
      _ = epsHom ρ δ (binPsi θ b w) := by rw [B45L2.repOf_theta]
      _ = epsHom ρ δ w := by rw [hbw]
  obtain ⟨a, haA, haL⟩ := Set.not_subset.mp hAL
  have haX : a ∈ X := hAX haA
  have ha2 : a * a = 1 := by
    have h := hAea.2 a haA
    simpa [pow_two] using h
  obtain ⟨δ, hδ⟩ := exists_not_commute_of_mem_normalizer hF θ hLX hLn φ hD haX ha2 haL
  have huNorm : B42L2.unitsPsi θ a ∈ Subgroup.normalizer (ρ.toHomUnits.range :
      Set (Module.End (ZMod 2) W)ˣ) := by
    dsimp [ρ]
    exact unitsPsi_mem_normalizer θ hLX hLn φ haX
  obtain ⟨δ', hδ'⟩ := exists_conjEndRing ρ (B42L2.unitsPsi θ a) huNorm δ
  have hδ'ne : δ' ≠ δ := by
    intro h
    apply hδ
    have e : (B42L2.unitsPsi θ a).val * epsHom ρ δ * ((B42L2.unitsPsi θ a)⁻¹).val = epsHom ρ δ := by
      rw [← hδ', h]
    have hinv : ((B42L2.unitsPsi θ a)⁻¹).val * (B42L2.unitsPsi θ a).val = 1 := by
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    have e2 : (B42L2.unitsPsi θ a).val * epsHom ρ δ = epsHom ρ δ * (B42L2.unitsPsi θ a).val := by
      calc (B42L2.unitsPsi θ a).val * epsHom ρ δ
          = (B42L2.unitsPsi θ a).val * epsHom ρ δ *
              (((B42L2.unitsPsi θ a)⁻¹).val * (B42L2.unitsPsi θ a).val) := by rw [hinv, mul_one]
        _ = ((B42L2.unitsPsi θ a).val * epsHom ρ δ * ((B42L2.unitsPsi θ a)⁻¹).val) *
              (B42L2.unitsPsi θ a).val := by simp only [mul_assoc]
        _ = epsHom ρ δ * (B42L2.unitsPsi θ a).val := by rw [e]
    exact e2
  intro hfix
  have hav : a v = v := by
    have hvA : v ∈ fixV A := by
      rw [← hfix]
      exact hvB
    exact hvA a haA
  have haw : binPsi θ a w = w := by
    simp [w, binPsi_apply, hav]
  have hu2 : B42L2.unitsPsi θ a * B42L2.unitsPsi θ a = 1 := by
    rw [← map_mul, ha2, map_one]
  have huinv : (B42L2.unitsPsi θ a)⁻¹ = B42L2.unitsPsi θ a := inv_eq_of_mul_eq_one_right hu2
  have hau : (B42L2.unitsPsi θ a).val w = w := by
    rw [B42L2.unitsPsi_apply, haw]
  have hau' : ((B42L2.unitsPsi θ a)⁻¹).val w = w := by
    rw [huinv, hau]
  have hv'B : θ.symm (Multiplicative.ofAdd (epsHom ρ δ w)) ∈ fixV (A ⊓ L) := by
    intro b hb
    apply θ.injective
    apply Multiplicative.toAdd.injective
    have h := hfixD δ b hb
    simpa [binPsi_apply] using h
  have hav' : a (θ.symm (Multiplicative.ofAdd (epsHom ρ δ w))) =
      θ.symm (Multiplicative.ofAdd (epsHom ρ δ w)) := by
    have hv'A : θ.symm (Multiplicative.ofAdd (epsHom ρ δ w)) ∈ fixV A := by
      rw [← hfix]
      exact hv'B
    exact hv'A a haA
  have haδw : binPsi θ a (epsHom ρ δ w) = epsHom ρ δ w := by
    have h := congrArg (fun z => Multiplicative.toAdd (θ z)) hav'
    simpa [binPsi_apply] using h
  have hauδ : (B42L2.unitsPsi θ a).val (epsHom ρ δ w) = epsHom ρ δ w := by
    rw [B42L2.unitsPsi_apply]
    exact haδw
  have hδ'w : epsHom ρ δ' w = epsHom ρ δ w := by
    rw [hδ']
    simp only [Module.End.mul_apply]
    rw [hau', hauδ]
  have hzero : epsHom ρ (δ' - δ) w = 0 := by
    rw [map_sub, LinearMap.sub_apply, hδ'w, sub_self]
  have hne : δ' - δ ≠ 0 := sub_ne_zero.mpr hδ'ne
  have hinv : epsHom ρ ((δ' - δ)⁻¹) (epsHom ρ (δ' - δ) w) = w := by
    rw [epsHom_apply, epsHom_apply, ← Module.End.mul_apply, inv_mul_cancel₀ hne,
      Module.End.one_apply]
  rw [hzero, map_zero] at hinv
  exact hwne hinv.symm

theorem not_mem_aSet_two_of_not_le {F : Type} [Field F] [Fintype F] [CharP F 2]
    (hF : Fintype.card F = 2 ^ 6) {I : Type} [CommGroup I] [Finite I] (hI : ∀ w : I, w ^ 2 = 1)
    {W : Type} [AddCommGroup W] [Module (ZMod 2) W] [Finite W] (θ : I ≃* Multiplicative W)
    {X L : Subgroup (MulAut I)} (hLX : L ≤ X) (hLn : (L.subgroupOf X).Normal)
    (φ : ↥L ≃* SL(2, F)) [Fact (B45L2.repOf θ φ).IsIrreducible]
    (hD : SixtyFourDescent (B45L2.repOf θ φ)) (A : Subgroup (MulAut I)) (hAL : ¬ A ≤ L) :
    A ∉ E3.aSet 2 X := by
  classical
  intro hAin
  rw [E3.aSet] at hAin
  obtain ⟨hAX, -, hAea, huniv⟩ := hAin
  obtain ⟨a, haA, haL⟩ := Set.not_subset.mp hAL
  have hBle : A ⊓ L ≤ A := inf_le_left
  have hrel : (A ⊓ L).relIndex A = 2 := by
    refine Subgroup.relIndex_eq_two_iff_exists_notMem_and.mpr ⟨a, haA, ?_, ?_⟩
    · intro h
      exact haL h.2
    · intro b hb
      by_cases hbL : b ∈ L
      · exact Or.inr ⟨hb, hbL⟩
      · refine Or.inl ⟨A.mul_mem hb haA, ?_⟩
        exact mul_mem_of_mem_not_mem hF θ hLX hLn φ hD hAX hAea hb haA hbL haL
  have hm : E3.mQuot A (A ⊓ L) < 2 := by
    rw [E3.mQuot, hrel]
    norm_num
  have hfixeq := huniv (A ⊓ L) hBle hm
  exact fixV_inf_ne_fixV hF hI θ hLX hLn φ hD hAX hAea hAL hfixeq

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_3
