module

public import CFSG.LocalAnalysis.StandardType.GGStdPosLocalDefs
public import CFSG.LocalAnalysis.StandardType.GGPsiDiagInnerMinusRank
import Mathlib.RingTheory.RootsOfUnity.Basic
import Mathlib.Tactic.Group

public section

namespace CFSG.StandardType

open CFSG.LieType.Universal CFSG.LieType.RootSystem CFSG.LieType.Steinberg
  CFSG.LieType.CurtisTits

theorem ggStdPos_exists_simpleRootChar {K : Type*} [Group K] {D : UniversalRootDatum K}
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

theorem ggStdPos_mem_centralizer_of_fix_posSimple {K : Type*} [Group K]
    {D : UniversalRootDatum K} {nn : Fin D.rank → K} {H : Fin D.rank → Subgroup K}
    (hct : IsCTGroupDatum (coxeterMatrix D.isFiniteType).toCoxeterSystem
      (weylAction D.isFiniteType) D.roots D.rootGroup nn H)
    (hdiv : D.divisible = ∅) {F : Type*} [Field F] [CharP F 2] {x : (Fin D.rank → ℤ) → F → K}
    {C : (Fin D.rank → ℤ) → (Fin D.rank → ℤ) → ℕ × ℕ → ℤ}
    {O : CommOrder (CFSG.LieType.Steinberg.RootSystem.ofCartan D.isFiniteType D.divisible)}
    (hE : ChevalleyExtras D F x C O) {G : Type*} [Group G] (ψ : K →* G)
    (hker : ψ.ker ≤ Subgroup.center K) {Bs : Subgroup G} (hBs : GGKGPosStdPos D ψ Bs) {b : G}
    (hb : b ∈ Bs)
    (h1 : ∀ (i : Fin D.rank) (c : F),
      b * ψ (x (Pi.single i 1) c) * b⁻¹ = ψ (x (Pi.single i 1) c)) :
    b ∈ Subgroup.centralizer (ψ.range : Set G) := by
  have hb' : b⁻¹ ∈ Subgroup.centralizer (ψ.range : Set G) := by
    refine PsiDiag.mem_centralizer_of_fix_simple hct hdiv ψ (fun i z hz => ?_) fun i z hz => ?_
    · obtain ⟨c, rfl⟩ := ((hE.param _ (single_mem_roots i)).1 z).mp hz
      rw [inv_inv]
      exact h1 i c
    · have hneg := hE.param _ (neg_single_mem_roots (D := D) i)
      obtain ⟨c, rfl⟩ := (hneg.1 z).mp hz
      obtain ⟨φ, hφinj, hφu, hφl⟩ := hE.rankOne i
      have hΦ := PsiDiag.injective_comp_of_ker_le_center φ hφinj ψ hker
      obtain ⟨hm, hhm, hmz⟩ := hBs b hb _ (neg_single_mem_roots i)
      have hN : hm ∈ Subgroup.normalizer (D.rootGroup (-Pi.single i 1) : Set K) :=
        Subgroup.mem_iInf.mp (Subgroup.mem_iInf.mp hhm _) (neg_single_mem_roots i)
      have hmem : ∀ c, ∃ c', x (-Pi.single i 1) c' = hm * x (-Pi.single i 1) c * hm⁻¹ :=
        fun c => (hneg.1 _).mp ((Subgroup.mem_normalizer_iff.mp hN _).mp ((hneg.1 _).mpr ⟨c, rfl⟩))
      choose φ' hφ' using hmem
      have hu : ∀ c, b⁻¹⁻¹ * (ψ.comp φ) (sl2Upper c) * b⁻¹ = (ψ.comp φ) (sl2Upper c) :=
        fun c => by rw [inv_inv, MonoidHom.comp_apply, hφu, h1]
      have hl : ∀ c, b⁻¹⁻¹ * (ψ.comp φ) (sl2Lower c) * b⁻¹ = (ψ.comp φ) (sl2Lower (φ' c)) :=
        fun c => by
          rw [inv_inv, MonoidHom.comp_apply, MonoidHom.comp_apply, hφl, hφl,
            hmz _ ((hneg.1 _).mpr ⟨c, rfl⟩), hφ']
      rw [inv_inv, hmz _ ((hneg.1 _).mpr ⟨c, rfl⟩), ← hφ',
        PsiDiag.eq_of_conj_sl2 (ψ.comp φ) hΦ hu hl c]
  simpa using inv_mem hb'

theorem ggStdPos_card_le_pow_rank_mul {K : Type*} [Group K] {D : UniversalRootDatum K}
    {nn : Fin D.rank → K} {H : Fin D.rank → Subgroup K}
    (hct : IsCTGroupDatum (coxeterMatrix D.isFiniteType).toCoxeterSystem
      (weylAction D.isFiniteType) D.roots D.rootGroup nn H)
    (hdiv : D.divisible = ∅) {F : Type*} [Field F] [CharP F 2] {x : (Fin D.rank → ℤ) → F → K}
    {C : (Fin D.rank → ℤ) → (Fin D.rank → ℤ) → ℕ × ℕ → ℤ}
    {O : CommOrder (CFSG.LieType.Steinberg.RootSystem.ofCartan D.isFiniteType D.divisible)}
    (hE : ChevalleyExtras D F x C O)
    (hlin : ∀ h ∈ ggTorus D, ∀ i : Fin D.rank, ∃ χ : F, ∀ c : F,
      h * x (Pi.single i 1) c * h⁻¹ = x (Pi.single i 1) (χ * c))
    {G : Type*} [Group G] [Finite G] (ψ : K →* G) (hker : ψ.ker ≤ Subgroup.center K) {p : ℕ}
    (hp : p ≠ 0) {Bs : Subgroup G} (hBs : GGKGPosStdPos D ψ Bs) (hpow : ∀ b ∈ Bs, b ^ p = 1) :
    Nat.card ↥Bs ≤ p ^ D.rank * Nat.card ↥(Bs ⊓ Subgroup.centralizer (ψ.range : Set G)) := by
  haveI : NeZero p := ⟨hp⟩
  choose χ hχ using fun i => ggStdPos_exists_simpleRootChar hE hlin ψ hker hBs i
  have hpow' : ∀ b : ↥Bs, b ^ p = 1 := fun b => Subtype.ext (by simpa using hpow b b.2)
  have hroot : ∀ (i : Fin D.rank) (b : ↥Bs), (χ i).toHomUnits b ∈ rootsOfUnity p F :=
    fun i b => by rw [mem_rootsOfUnity, ← map_pow, hpow' b, map_one]
  let θ : ↥Bs →* (Fin D.rank → ↥(rootsOfUnity p F)) :=
    MonoidHom.pi fun i => (χ i).toHomUnits.codRestrict (rootsOfUnity p F) (hroot i)
  have hkerθ : θ.ker.map Bs.subtype ≤ Bs ⊓ Subgroup.centralizer (ψ.range : Set G) := by
    rintro _ ⟨b, hb, rfl⟩
    refine ⟨b.2, ggStdPos_mem_centralizer_of_fix_posSimple hct hdiv hE ψ hker hBs b.2
      fun i c => ?_⟩
    have h1 : χ i b = 1 := by
      simpa [θ] using congrArg (fun v => ((v i : Fˣ) : F)) (MonoidHom.mem_ker.mp hb)
    show (b : G) * ψ (x (Pi.single i 1) c) * (b : G)⁻¹ = ψ (x (Pi.single i 1) c)
    rw [hχ, h1, one_mul]
  have hrange : Nat.card θ.range ≤ p ^ D.rank := by
    calc Nat.card θ.range ≤ Nat.card (Fin D.rank → ↥(rootsOfUnity p F)) :=
          Subgroup.card_le_card_group _
      _ = Nat.card ↥(rootsOfUnity p F) ^ D.rank := by
          rw [Nat.card_fun, Nat.card_eq_fintype_card (α := Fin D.rank), Fintype.card_fin]
      _ ≤ p ^ D.rank := Nat.pow_le_pow_left (card_rootsOfUnity _ _) _
  calc Nat.card ↥Bs = Nat.card θ.ker * Nat.card θ.range :=
        (Subgroup.card_ker_mul_card_range θ).symm
    _ ≤ Nat.card ↥(Bs ⊓ Subgroup.centralizer (ψ.range : Set G)) * p ^ D.rank := by
        refine Nat.mul_le_mul ?_ hrange
        rw [← Subgroup.card_map_of_injective Bs.subtype_injective]
        exact Subgroup.card_le_of_le hkerθ
    _ = _ := mul_comm _ _

end CFSG.StandardType

end
