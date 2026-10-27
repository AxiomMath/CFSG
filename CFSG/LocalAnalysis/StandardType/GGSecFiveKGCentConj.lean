module

public import CFSG.LocalAnalysis.StandardType.GGStdPosLocalDefs
public import CFSG.LieType.CurtisTits.Reduction
public import CFSG.LieType.Steinberg.PartB
import CFSG.LocalAnalysis.StandardType.GGStdPosCardScalar
import CFSG.LocalAnalysis.StandardType.GGStdPosTorusFix
import CFSG.LocalAnalysis.StandardType.GGPresentation
import CFSG.LieType.Steinberg.BruhatWeyl
import CFSG.LieType.RootSystem.Parabolic
import Mathlib.RingTheory.RootsOfUnity.Basic
import Mathlib.Tactic.Group

public section

namespace CFSG.StandardType

open CFSG.LieType.Universal CFSG.LieType.RootSystem CFSG.LieType.Steinberg

private theorem exists_eq_weylAction {K : Type*} [Group K] {D : UniversalRootDatum K}
    (hdiv : D.divisible = ∅) {β : Fin D.rank → ℤ} (hβ : β ∈ D.roots) :
    ∃ (w : (coxeterMatrix D.isFiniteType).Group) (i : Fin D.rank),
      β = weylAction D.isFiniteType w (Pi.single i 1) := by
  rcases (show β ∈ roots D.isFiniteType ∅ from hdiv ▸ hβ) with ⟨w, i, rfl⟩ | ⟨w, i, hi, -⟩
  · exact ⟨w, i, rfl⟩
  · simp at hi

private theorem ker_comp_conj {K : Type*} [Group K] {G : Type*} [Group G] {ψ : K →* G}
    (hker : ψ.ker ≤ Subgroup.center K) (m : K) :
    (ψ.comp (MulAut.conj m).toMonoidHom).ker ≤ Subgroup.center K := by
  intro z hz
  have hc := hker (show ψ (m * z * m⁻¹) = 1 from hz)
  have := Subgroup.Normal.conj_mem inferInstance _ hc m⁻¹
  simpa [mul_assoc] using this

private theorem stdPos_comp_conj {K : Type*} [Group K] {D : UniversalRootDatum K} {m : K}
    {w : (coxeterMatrix D.isFiniteType).Group} (hm : ActsAs D m w) {G : Type*} [Group G]
    {ψ : K →* G} {Bs : Subgroup G} (hBs : GGKGPosStdPos D ψ Bs) :
    GGKGPosStdPos D (ψ.comp (MulAut.conj m).toMonoidHom) Bs := by
  intro b hb γ hγ
  obtain ⟨h, hh, hz⟩ := hBs b hb _ (CFSG.LieType.RootSystem.weylAction_mem_roots _ w hγ)
  refine ⟨m⁻¹ * h * m, ?_, fun z hz' => ?_⟩
  · simpa using ggStdPos_conj_mem_ggTorus_of_actsAs hh hm.inv
  · have e := hz _ (hm.conj_mem hγ hz')
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [e]
    congr 1
    group

private theorem fix_neg_single {K : Type*} [Group K] {D : UniversalRootDatum K} {F : Type*}
    [Field F] [CharP F 2] {x : (Fin D.rank → ℤ) → F → K}
    {C : (Fin D.rank → ℤ) → (Fin D.rank → ℤ) → ℕ × ℕ → ℤ}
    {O : CommOrder (CFSG.LieType.Steinberg.RootSystem.ofCartan D.isFiniteType D.divisible)}
    (hE : ChevalleyExtras D F x C O) {G : Type*} [Group G] (ψ : K →* G)
    (hker : ψ.ker ≤ Subgroup.center K) {Bs : Subgroup G} (hBs : GGKGPosStdPos D ψ Bs) {b : G}
    (hb : b ∈ Bs) (i : Fin D.rank)
    (h1 : ∀ c : F, b * ψ (x (Pi.single i 1) c) * b⁻¹ = ψ (x (Pi.single i 1) c)) :
    ∀ z ∈ D.rootGroup (-Pi.single i 1), b * ψ z * b⁻¹ = ψ z := by
  intro z hz
  have hneg := hE.param _ (neg_single_mem_roots (D := D) i)
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
  rw [hmz _ ((hneg.1 _).mpr ⟨c, rfl⟩), ← hφ', PsiDiag.eq_of_conj_sl2 (ψ.comp φ) hΦ hu hl c]

theorem ggKGCent_fix_neg {K : Type*} [Group K] {D : UniversalRootDatum K}
    {nn : Fin D.rank → K} {H : Fin D.rank → Subgroup K}
    (hct : CFSG.LieType.CurtisTits.IsCTGroupDatum (coxeterMatrix D.isFiniteType).toCoxeterSystem
      (weylAction D.isFiniteType) D.roots D.rootGroup nn H)
    (hdiv : D.divisible = ∅) {F : Type*} [Field F] [CharP F 2] {x : (Fin D.rank → ℤ) → F → K}
    {C : (Fin D.rank → ℤ) → (Fin D.rank → ℤ) → ℕ × ℕ → ℤ}
    {O : CommOrder (CFSG.LieType.Steinberg.RootSystem.ofCartan D.isFiniteType D.divisible)}
    (hE : ChevalleyExtras D F x C O) {G : Type*} [Group G] (ψ : K →* G)
    (hker : ψ.ker ≤ Subgroup.center K) {Bs : Subgroup G} (hBs : GGKGPosStdPos D ψ Bs)
    {β : Fin D.rank → ℤ} (hβ : β ∈ D.roots) {b : G} (hb : b ∈ Bs)
    (h1 : ∀ z ∈ D.rootGroup β, b * ψ z * b⁻¹ = ψ z) :
    ∀ z ∈ D.rootGroup (-β), b * ψ z * b⁻¹ = ψ z := by
  obtain ⟨w, i, rfl⟩ := exists_eq_weylAction hdiv hβ
  have hm := actsAs_nrep hct w
  have hα := single_mem_roots (D := D) i
  have h2 := fix_neg_single hE _ (ker_comp_conj hker (nrep hct w)) (stdPos_comp_conj hm hBs) hb i
    fun c => h1 _ (hm.conj_mem hα (((hE.param _ hα).1 _).mpr ⟨c, rfl⟩))
  intro z hz
  have hz' := hm.inv_conj_mem (OfCartan.neg_mem_roots D.isFiniteType hβ) hz
  rw [map_neg, weylAction_inv_apply_apply] at hz'
  have e := h2 _ hz'
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at e
  have ez : nrep hct w * ((nrep hct w)⁻¹ * z * nrep hct w) * (nrep hct w)⁻¹ = z := by group
  rwa [ez] at e

theorem ggKGCent_card_le_mul {K : Type*} [Group K] {D : UniversalRootDatum K}
    {nn : Fin D.rank → K} {H : Fin D.rank → Subgroup K}
    (hct : CFSG.LieType.CurtisTits.IsCTGroupDatum (coxeterMatrix D.isFiniteType).toCoxeterSystem
      (weylAction D.isFiniteType) D.roots D.rootGroup nn H)
    (hdiv : D.divisible = ∅) {F : Type*} [Field F] [CharP F 2] {x : (Fin D.rank → ℤ) → F → K}
    {C : (Fin D.rank → ℤ) → (Fin D.rank → ℤ) → ℕ × ℕ → ℤ}
    {O : CommOrder (CFSG.LieType.Steinberg.RootSystem.ofCartan D.isFiniteType D.divisible)}
    (hE : ChevalleyExtras D F x C O)
    (hlin : ∀ h ∈ ggTorus D, ∀ i : Fin D.rank, ∃ χ : F, ∀ c : F,
      h * x (Pi.single i 1) c * h⁻¹ = x (Pi.single i 1) (χ * c))
    {G : Type*} [Group G] [Finite G] (ψ : K →* G) (hker : ψ.ker ≤ Subgroup.center K) {p : ℕ}
    (hp : p ≠ 0) {Bs : Subgroup G} (hBs : GGKGPosStdPos D ψ Bs) (hpow : ∀ b ∈ Bs, b ^ p = 1)
    {β : Fin D.rank → ℤ} (hβ : β ∈ D.roots) :
    Nat.card ↥Bs ≤
      p * Nat.card ↥(Bs ⊓ Subgroup.centralizer ((D.rootGroup β).map ψ : Set G)) := by
  have : NeZero p := ⟨hp⟩
  obtain ⟨w, i, rfl⟩ := exists_eq_weylAction hdiv hβ
  have hm := actsAs_nrep hct w
  have hα := single_mem_roots (D := D) i
  obtain ⟨χ, hχ⟩ := ggStdPos_exists_simpleRootChar hE hlin _ (ker_comp_conj hker (nrep hct w))
    (stdPos_comp_conj hm hBs) i
  have hpow' : ∀ b : ↥Bs, b ^ p = 1 := fun b => Subtype.ext (by simpa using hpow b b.2)
  have hroot : ∀ b : ↥Bs, χ.toHomUnits b ∈ rootsOfUnity p F :=
    fun b => by rw [mem_rootsOfUnity, ← map_pow, hpow' b, map_one]
  let θ : ↥Bs →* ↥(rootsOfUnity p F) := χ.toHomUnits.codRestrict (rootsOfUnity p F) hroot
  have hkerθ : θ.ker.map Bs.subtype ≤ Bs ⊓ Subgroup.centralizer
      ((D.rootGroup (weylAction D.isFiniteType w (Pi.single i 1))).map ψ : Set G) := by
    intro g hg
    obtain ⟨b, hb, rfl⟩ := Subgroup.mem_map.mp hg
    refine Subgroup.mem_inf.mpr ⟨b.2, ?_⟩
    have h1 : χ b = 1 := by
      simpa [θ] using congrArg (fun v : ↥(rootsOfUnity p F) => ((v : Fˣ) : F))
        (MonoidHom.mem_ker.mp hb)
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨z, hz, rfl⟩
    have hz0 := hm.inv_conj_mem (CFSG.LieType.RootSystem.weylAction_mem_roots _ w hα) hz
    rw [weylAction_inv_apply_apply] at hz0
    obtain ⟨c, hc⟩ := ((hE.param _ hα).1 _).mp hz0
    have e := hχ b c
    rw [h1, one_mul, hc] at e
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at e
    have ez : nrep hct w * ((nrep hct w)⁻¹ * z * nrep hct w) * (nrep hct w)⁻¹ = z := by group
    rw [ez] at e
    calc ψ z * (b : G) = (b : G) * ψ z * (b : G)⁻¹ * b := by rw [e]
      _ = b * ψ z := by group
  have hrange : Nat.card θ.range ≤ p :=
    (Subgroup.card_le_card_group _).trans (card_rootsOfUnity _ _)
  calc Nat.card ↥Bs = Nat.card θ.ker * Nat.card θ.range :=
        (Subgroup.card_ker_mul_card_range θ).symm
    _ ≤ Nat.card ↥(Bs ⊓ Subgroup.centralizer
          ((D.rootGroup (weylAction D.isFiniteType w (Pi.single i 1))).map ψ : Set G)) * p := by
        refine Nat.mul_le_mul ?_ hrange
        rw [← Subgroup.card_map_of_injective Bs.subtype_injective]
        exact Subgroup.card_le_of_le hkerθ
    _ = _ := mul_comm _ _

theorem ggKGCent_exists_not_commute {K : Type*} [Group K] {D : UniversalRootDatum K}
    {nn : Fin D.rank → K} {H : Fin D.rank → Subgroup K}
    (hct : CFSG.LieType.CurtisTits.IsCTGroupDatum (coxeterMatrix D.isFiniteType).toCoxeterSystem
      (weylAction D.isFiniteType) D.roots D.rootGroup nn H)
    (hdiv : D.divisible = ∅) {F : Type*} [Field F] [CharP F 2] {x : (Fin D.rank → ℤ) → F → K}
    {C : (Fin D.rank → ℤ) → (Fin D.rank → ℤ) → ℕ × ℕ → ℤ}
    {O : CommOrder (CFSG.LieType.Steinberg.RootSystem.ofCartan D.isFiniteType D.divisible)}
    (hE : ChevalleyExtras D F x C O) {G : Type*} [Group G] (ψ : K →* G)
    (hker : ψ.ker ≤ Subgroup.center K) {β : Fin D.rank → ℤ} (hβ : β ∈ D.roots) :
    ∃ a ∈ D.rootGroup β, ∃ a' ∈ D.rootGroup (-β), ψ a * ψ a' ≠ ψ a' * ψ a := by
  obtain ⟨w, i, rfl⟩ := exists_eq_weylAction hdiv hβ
  have hm := actsAs_nrep hct w
  obtain ⟨φ, hφinj, hφu, hφl⟩ := hE.rankOne i
  have hΦ := PsiDiag.injective_comp_of_ker_le_center φ hφinj _ (ker_comp_conj hker (nrep hct w))
  have hα := single_mem_roots (D := D) i
  have hα' := neg_single_mem_roots (D := D) i
  have hl := hm.conj_mem hα' (((hE.param _ hα').1 _).mpr ⟨1, rfl⟩)
  rw [map_neg] at hl
  refine ⟨_, hm.conj_mem hα (((hE.param _ hα).1 _).mpr ⟨1, rfl⟩), _, hl, fun h => ?_⟩
  have hne : (sl2Upper (1 : F) * sl2Lower 1 : Matrix.SpecialLinearGroup (Fin 2) F) ≠
      sl2Lower 1 * sl2Upper 1 := by
    intro h'
    have h00 := congrArg (fun M : Matrix.SpecialLinearGroup (Fin 2) F =>
      (M : Matrix (Fin 2) (Fin 2) F) 0 0) h'
    simp [Matrix.SpecialLinearGroup.coe_mul, PsiDiag.coe_sl2Upper, PsiDiag.coe_sl2Lower,
      Matrix.mul_apply, Fin.sum_univ_two] at h00
  apply hne
  apply hΦ
  rw [map_mul, map_mul]
  simp only [MonoidHom.comp_apply, hφu, hφl, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  exact h

end CFSG.StandardType

end
