module

public import CFSG.LocalAnalysis.StandardType.GGStdPosLocalDefs
public import CFSG.LocalAnalysis.StandardType.GGPsiDiagInner
import TauCeti.GroupTheory.Coxeter.Geometric
import Mathlib.RingTheory.RootsOfUnity.Basic
import Mathlib.Tactic.Group

public section

namespace CFSG.StandardType

open CFSG.LieType.Universal CFSG.LieType.RootSystem CFSG.LieType.Steinberg
  CFSG.LieType.CurtisTits

private theorem ggStdPosRefl_exists_char {K : Type*} [Group K] {D : UniversalRootDatum K}
    {F : Type*} [Field F] [CharP F 2] {x : (Fin D.rank → ℤ) → F → K}
    {C : (Fin D.rank → ℤ) → (Fin D.rank → ℤ) → ℕ × ℕ → ℤ}
    {O : CommOrder (CFSG.LieType.Steinberg.RootSystem.ofCartan D.isFiniteType D.divisible)}
    (hE : ChevalleyExtras D F x C O)
    (hlin : ∀ h ∈ ggTorus D, ∀ i : Fin D.rank, ∃ χ : F, ∀ c : F,
      h * x (Pi.single i 1) c * h⁻¹ = x (Pi.single i 1) (χ * c))
    {G : Type*} [Group G] (ψ : K →* G) (hker : ψ.ker ≤ Subgroup.center K) {Bs : Subgroup G}
    (hBs : GGKGPosStdPos D ψ Bs) (i : Fin D.rank) :
    ∃ χ : ↥Bs →* F, ∀ (b : ↥Bs) (c : F),
      (b : G) * ψ (x (Pi.single i 1) c) * (b : G)⁻¹ = ψ (x (Pi.single i 1) (χ b * c)) := by
  have hα := single_mem_roots (D := D) i
  have hpos := hE.param _ hα
  obtain ⟨φ, hφinj, hφu, -⟩ := hE.rankOne i
  have hΦ := PsiDiag.injective_comp_of_ker_le_center φ hφinj ψ hker
  have hxinj : ∀ a a' : F, ψ (x (Pi.single i 1) a) = ψ (x (Pi.single i 1) a') → a = a' := by
    intro a a' h
    have h1 := hΦ (show (ψ.comp φ) (sl2Upper a) = (ψ.comp φ) (sl2Upper a') by
      rw [MonoidHom.comp_apply, MonoidHom.comp_apply, hφu, hφu]
      exact h)
    simpa [PsiDiag.coe_sl2Upper] using congrArg (fun M : Matrix.SpecialLinearGroup (Fin 2) F =>
      (M : Matrix (Fin 2) (Fin 2) F) 0 1) h1
  have hex : ∀ b : ↥Bs, ∃ a : F, ∀ c : F,
      (b : G) * ψ (x (Pi.single i 1) c) * (b : G)⁻¹ = ψ (x (Pi.single i 1) (a * c)) := by
    intro b
    obtain ⟨h, hh, hz⟩ := hBs b b.2 _ hα
    obtain ⟨a, ha⟩ := hlin h hh i
    exact ⟨a, fun c => by rw [hz _ ((hpos.1 _).mpr ⟨c, rfl⟩), ha]⟩
  choose a ha using hex
  have huniq : ∀ (b : ↥Bs) (a' : F), (∀ c : F, (b : G) * ψ (x (Pi.single i 1) c) * (b : G)⁻¹ =
      ψ (x (Pi.single i 1) (a' * c))) → a b = a' := fun b a' h' => by
    simpa using hxinj _ _ ((ha b 1).symm.trans (h' 1))
  have h1 : a 1 = 1 := huniq 1 1 fun c => by simp
  have hmul : ∀ b b' : ↥Bs, a (b * b') = a b * a b' := fun b b' => huniq _ _ fun c => by
    calc ((b * b' : ↥Bs) : G) * ψ (x (Pi.single i 1) c) * ((b * b' : ↥Bs) : G)⁻¹ =
        (b : G) * ((b' : G) * ψ (x (Pi.single i 1) c) * (b' : G)⁻¹) * (b : G)⁻¹ := by
          rw [Subgroup.coe_mul]
          group
      _ = ψ (x (Pi.single i 1) (a b * a b' * c)) := by rw [ha, ha, mul_assoc]
  exact ⟨{ toFun := a, map_one' := h1, map_mul' := hmul }, ha⟩

private theorem ggStdPosRefl_commute_of_char_eq_one {K : Type*} [Group K] {D : UniversalRootDatum K}
    {F : Type*} [Field F] [CharP F 2] {x : (Fin D.rank → ℤ) → F → K}
    {C : (Fin D.rank → ℤ) → (Fin D.rank → ℤ) → ℕ × ℕ → ℤ}
    {O : CommOrder (CFSG.LieType.Steinberg.RootSystem.ofCartan D.isFiniteType D.divisible)}
    (hE : ChevalleyExtras D F x C O) {G : Type*} [Group G] (ψ : K →* G)
    (hker : ψ.ker ≤ Subgroup.center K) {Bs : Subgroup G} (hBs : GGKGPosStdPos D ψ Bs)
    {ν : GGWeyl D →* K} (hν : GGWeylLift D ν) (i : Fin D.rank) {b : G} (hb : b ∈ Bs)
    (h1 : ∀ c : F, b * ψ (x (Pi.single i 1) c) * b⁻¹ = ψ (x (Pi.single i 1) c)) :
    b * ψ (ν ((coxeterMatrix D.isFiniteType).toCoxeterSystem.simple i)) =
      ψ (ν ((coxeterMatrix D.isFiniteType).toCoxeterSystem.simple i)) * b := by
  obtain ⟨φ, hφinj, hφu, hφl⟩ := hE.rankOne i
  have hΦ := PsiDiag.injective_comp_of_ker_le_center φ hφinj ψ hker
  have hpos := hE.param _ (single_mem_roots (D := D) i)
  have hneg := hE.param _ (neg_single_mem_roots (D := D) i)
  obtain ⟨hm, hhm, hmz⟩ := hBs b hb _ (neg_single_mem_roots i)
  have hN : hm ∈ Subgroup.normalizer (D.rootGroup (-Pi.single i 1) : Set K) :=
    Subgroup.mem_iInf.mp (Subgroup.mem_iInf.mp hhm _) (neg_single_mem_roots i)
  have hmem : ∀ c, ∃ c', x (-Pi.single i 1) c' = hm * x (-Pi.single i 1) c * hm⁻¹ := fun c =>
    (hneg.1 _).mp ((Subgroup.mem_normalizer_iff.mp hN _).mp ((hneg.1 _).mpr ⟨c, rfl⟩))
  choose φ' hφ' using hmem
  have hu : ∀ c, b⁻¹⁻¹ * (ψ.comp φ) (sl2Upper c) * b⁻¹ = (ψ.comp φ) (sl2Upper c) := fun c => by
    rw [inv_inv, MonoidHom.comp_apply, hφu, h1]
  have hl : ∀ c, b⁻¹⁻¹ * (ψ.comp φ) (sl2Lower c) * b⁻¹ = (ψ.comp φ) (sl2Lower (φ' c)) :=
    fun c => by
      rw [inv_inv, MonoidHom.comp_apply, MonoidHom.comp_apply, hφl, hφl,
        hmz _ ((hneg.1 _).mpr ⟨c, rfl⟩), hφ']
  have hfix := PsiDiag.eq_of_conj_sl2 (ψ.comp φ) hΦ hu hl
  have hL : rankOne D.rootGroup i ≤ (Subgroup.centralizer ({b⁻¹} : Set G)).comap ψ := by
    refine sup_le (fun z hz => ?_) fun z hz => ?_
    · obtain ⟨c, rfl⟩ := (hpos.1 z).mp hz
      rw [PsiDiag.mem_fix_iff, inv_inv, h1]
    · obtain ⟨c, rfl⟩ := (hneg.1 z).mp hz
      rw [PsiDiag.mem_fix_iff, inv_inv, hmz _ ((hneg.1 _).mpr ⟨c, rfl⟩), ← hφ', hfix]
  have h2 := (PsiDiag.mem_fix_iff ψ).mp (hL (hν.simple_mem i))
  rw [inv_inv] at h2
  exact mul_inv_eq_iff_eq_mul.mp h2

private theorem ggStdPosRefl_card_fix_mul_eq {G : Type} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    {Bs : Subgroup G} (hpow : ∀ b ∈ Bs, b ^ p = 1) {F : Type*} [Field F] (χ : ↥Bs →* F)
    {φ : MulAut ↥Bs} (hfix : ∀ b : ↥Bs, χ b = 1 → φ b = b) (hne : φ ≠ 1) :
    Nat.card {b : ↥Bs // φ b = b} * p = Nat.card ↥Bs := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : NeZero p := ⟨hp.ne_zero⟩
  have hpow' : ∀ b : ↥Bs, b ^ p = 1 := fun b => Subtype.ext (by simpa using hpow b b.2)
  let f : ↥Bs →* Fˣ := χ.toHomUnits
  let Fx : Subgroup ↥Bs := MonoidHom.eqLocus φ.toMonoidHom (MonoidHom.id ↥Bs)
  have hcard : Nat.card {b : ↥Bs // φ b = b} = Nat.card Fx := rfl
  have h1 : f.ker.index ≤ p := by
    have hle : f.range ≤ rootsOfUnity p F := by
      rintro _ ⟨b, rfl⟩
      rw [mem_rootsOfUnity, ← map_pow, hpow' b, map_one]
    rw [Subgroup.index_ker]
    exact (Subgroup.card_le_of_le hle).trans (card_rootsOfUnity _ _)
  have h2 : f.ker ≤ Fx := fun b hb => hfix b (by
    simpa [f] using congrArg Units.val (MonoidHom.mem_ker.mp hb))
  have h3 : p ≤ Fx.index := by
    obtain ⟨k, hk⟩ := IsPGroup.index (fun b => ⟨1, by rw [pow_one, hpow' b]⟩ : IsPGroup p ↥Bs) Fx
    have hk0 : k ≠ 0 := by
      rintro rfl
      have htop : Fx = ⊤ := Subgroup.index_eq_one.mp (by rw [hk, pow_zero])
      refine hne (MulEquiv.ext fun b => ?_)
      have hb : b ∈ Fx := by
        rw [htop]
        exact Subgroup.mem_top b
      exact hb
    rw [hk]
    exact Nat.le_self_pow hk0 p
  rw [hcard]
  refine le_antisymm ((Subgroup.card_mul_index Fx) ▸ Nat.mul_le_mul_left _ h3) ?_
  calc Nat.card ↥Bs = Nat.card f.ker * f.ker.index := (Subgroup.card_mul_index f.ker).symm
    _ ≤ Nat.card Fx * p := Nat.mul_le_mul (Subgroup.card_le_of_le h2) h1

theorem ggStdPos_isReflection {K : Type*} [Group K] {D : UniversalRootDatum K} {F : Type*}
    [Field F] [CharP F 2] {x : (Fin D.rank → ℤ) → F → K}
    {C : (Fin D.rank → ℤ) → (Fin D.rank → ℤ) → ℕ × ℕ → ℤ}
    {O : CommOrder (CFSG.LieType.Steinberg.RootSystem.ofCartan D.isFiniteType D.divisible)}
    (hE : ChevalleyExtras D F x C O)
    (hlin : ∀ h ∈ ggTorus D, ∀ i : Fin D.rank, ∃ χ : F, ∀ c : F,
      h * x (Pi.single i 1) c * h⁻¹ = x (Pi.single i 1) (χ * c))
    {G : Type} [Group G] [Finite G] (ψ : K →* G) (hker : ψ.ker ≤ Subgroup.center K) {p : ℕ}
    (hp : p.Prime) {Bs X : Subgroup G} (hBs : GGKGPosStdPos D ψ Bs) (hpow : ∀ b ∈ Bs, b ^ p = 1)
    {ν : GGWeyl D →* K} (hν : GGWeylLift D ν) (ε : GGWeyl D ≃* ↥(ggAutomizer X Bs))
    (hε : ∀ (w : GGWeyl D) (b : ↥Bs), ((ε w : MulAut ↥Bs) b : G) = ψ (ν w) * b * (ψ (ν w))⁻¹)
    (i : Fin D.rank) :
    GGIsReflection p
      ((ε ((coxeterMatrix D.isFiniteType).simple i) : ↥(ggAutomizer X Bs)) : MulAut ↥Bs) := by
  have hsimp : (coxeterMatrix D.isFiniteType).toCoxeterSystem.simple i =
      (coxeterMatrix D.isFiniteType).simple i := by
    rw [CoxeterMatrix.toCoxeterSystem_simple]
  obtain ⟨χ, hχ⟩ := ggStdPosRefl_exists_char hE hlin ψ hker hBs i
  refine ⟨?_, ggStdPosRefl_card_fix_mul_eq hp hpow χ (fun b hb1 => ?_) fun h1 => ?_⟩
  · have hs2 : (coxeterMatrix D.isFiniteType).simple i ^ 2 = 1 := by
      rw [← hsimp]
      exact (coxeterMatrix D.isFiniteType).toCoxeterSystem.simple_sq i
    rw [← Subgroup.coe_pow, ← map_pow, hs2, map_one, Subgroup.coe_one]
  · have hc := ggStdPosRefl_commute_of_char_eq_one hE ψ hker hBs hν i b.2 fun c => by
      rw [hχ, hb1, one_mul]
    rw [hsimp] at hc
    apply Subtype.ext
    rw [hε, ← hc, mul_inv_cancel_right]
  · apply (coxeterMatrix D.isFiniteType).toCoxeterSystem.simple_ne_one i
    rw [hsimp, ← ε.map_eq_one_iff]
    exact Subtype.ext h1

end CFSG.StandardType

end
